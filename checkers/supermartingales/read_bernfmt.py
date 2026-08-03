"""bernfmt READER, python side  — the inverse seam of
`emit_bernfmt.py`, so the reference checker (`bl_checker.py`) can consume
certificate BYTES — in particular the meta-schema rows-projection output —
rather than only producer-side in-memory models.

Scope: exactly the producer subset (the emit module's docstring list) —
node tags Ax(0), Cut(2), AndI(3), AndE(4), OrE-ctx(6), EqElim(7),
ConvIntro(8), ConvElim(9), BernCone(11), Farkas(14), Promise(25),
Syzygy(26); term tags 0x01–0x06 (0x06 = neg — the
ge-flip syzygy conclusion reading) + 0x07 (idx, G1) + 0x08/0x09 (einsum /
coefficient-tensor poly — terms-v1, memo §8 ruling); formulas
atom/inRegion/and/or/tt/ff/sph; app-free hypernets (n_apps == 0).
Anything outside the subset is a LOUD `ReadError`, never a skip — this
reader is a checking instrument, not a general parser (the general
parser is the Rust bernfmt tooling, whose normative byte-level spec
lives with it outside this repository). (Wire-read
acceptance matters: reference ACCEPTs that run only on in-memory proofs
are exactly the seam where an emitter/wire canonical-form divergence can
hide; the companion experiments repository's acceptance batteries feed
real wire bytes back through this reader.)

Wire-shape inversions, each the mirror of an emit-side translation:

  * sph (0x26) reads back as `FTrue()` — the producer's SP_H terminus IS
    FTrue in the python model (`sp_H` of an app-free hypernet), so the
    reconstructed root pre matches `check_certificate`'s synthesized
    `FAnd(vc_hyp, sp_H(h))` exactly.
  * Farkas leaf → proof-premised model: the wire's farkasEntries
    combination term is unzipped into (lambda, entry) pairs; each entry
    must be a literal `(e <= 0)` conjunct of the node's own pre (the leaf
    discipline), and its premise proof is reconstructed as the canonical
    PAx + PAndE extraction chain to that conjunct. A missing conjunct is
    a ReadError — by construction this reader cannot manufacture a
    premise the pre does not contain.
  * Syzygy entries align 1:1 with components (emit order); an equality
    component post read back from polarity: entry == (l - r) carries
    lambda = +w, entry == (r - l) carries lambda = -w (the wire's
    nonneg-weights-on-either-polarity realization of free sign).
  * wire NAMES do not ride the wire (BINARY carries dtype/shape only);
    wires are named "w{id}". Checker verdicts are name-invariant.

Verification posture: this reader is untrusted tooling in exactly the
same sense as the projection it audits — a misparse yields a certificate
that FAILS checking (sequent identity is enforced at every node), never
a false ACCEPT. Its artifact pair is the Rust reader (outside this
repository), and the acceptance batteries in the companion experiments
repository feed both readers mutants.
"""

from __future__ import annotations

import os
import struct
import sys
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from sympy import Rational

from bl_cert import (
    FAnd, FAtom, FFalse, FInRegion, FOr, FTrue, Formula, HOLE, Hypernet,
    Judgment, PAndE, PAndI, PAx, PBernCone, PConvElim, PConvIntro, PCut,
    PEqElim, PFarkas, POrECtx, PPromise, PSyzygy, Proof, Simplex, TAdd,
    TConst, TEinsum, TIdx, TMul, TNeg, TPoly, TSub, TVar, Term, Wire,
    tpoly_wf_errors,
    BlockLattice, FamBlock, FamJudgment, PProductLattice,
    ENC_FUNCS, EncJudgment, PEnclosure,
)

MAGIC = bytes([0x42, 0x45, 0x52, 0x4E, 0x4C, 0x47, 0x43, 0x01])
HOLE_ID = 0xFFFF_FFFF
NO_PAYLOAD = 0xFFFF_FFFF_FFFF_FFFF
BOWTIE_INV = {0: "<", 1: "<=", 2: "=", 3: ">=", 4: ">"}
KIND_DTYPE = {0: "B", 2: "Q"}  # producer subset: Bool, Rat


class ReadError(Exception):
    pass


def _need(cond, msg):
    if not cond:
        raise ReadError(msg)


class _Buf:
    def __init__(self, data: bytes, base: int = 0):
        self.data = data
        self.pos = base

    def u8(self):
        v = self.data[self.pos]
        self.pos += 1
        return v

    def u16(self):
        (v,) = struct.unpack_from("<H", self.data, self.pos)
        self.pos += 2
        return v

    def u32(self):
        (v,) = struct.unpack_from("<I", self.data, self.pos)
        self.pos += 4
        return v

    def u64(self):
        (v,) = struct.unpack_from("<Q", self.data, self.pos)
        self.pos += 8
        return v

    def raw(self, n):
        b = self.data[self.pos:self.pos + n]
        _need(len(b) == n, "truncated read")
        self.pos += n
        return b

    def rat(self):
        nlen, dlen = self.u32(), self.u32()
        _need(1 <= nlen and 1 <= dlen, "empty rational limb")
        num = int.from_bytes(self.raw(nlen), "little", signed=True)
        den = int.from_bytes(self.raw(dlen), "little", signed=False)
        _need(den >= 1, "rational denominator must be >= 1")
        f = Fraction(num, den)
        _need(f.numerator == num and f.denominator == den,
              f"non-canonical rational {num}/{den} on the wire")
        return Rational(num, den)


def _bitset_indices(raw: bytes, n: int):
    out = []
    for i in range(n):
        if raw[i // 8] >> (i % 8) & 1:
            out.append(i)
    for i in range(n, len(raw) * 8):
        _need(not raw[i // 8] >> (i % 8) & 1, "bitset tail bits must be 0")
    return out


class _Pool:
    """Offset-addressed structure pool with memoized decoding. Records
    every parsed record's [start, end) for the record-boundary rule
    (BINARY.md §6.1, terms-v1)."""

    def __init__(self, buf: bytes, complexes, wires=None):
        self.buf = buf
        self.complexes = complexes  # list[tuple[vertex tuple, ...]]
        self.wires = wires  # [(name, dtype, shape)] — family-v1 F-A6
        self._terms, self._formulas = {}, {}
        self._simplices, self._extsets, self._judgments = {}, {}, {}
        self.intervals = []

    def check_partition(self):
        """§6.1 record-boundary rule: intervals tile [0, len(buf))."""
        cursor = 0
        for start, end in sorted(self.intervals):
            _need(start == cursor,
                  f"pool not partitioned: record at {start}, expected "
                  f"{cursor} (interior ref or unreachable slack)")
            cursor = end
        _need(cursor == len(self.buf),
              f"pool not partitioned: records end at {cursor}, pool is "
              f"{len(self.buf)} bytes")

    def term(self, off: int) -> Term:
        if off in self._terms:
            return self._terms[off]
        b = _Buf(self.buf, off)
        tag = b.u8()
        if tag == 0x01:
            wid = b.u32()
            t = TVar(HOLE if wid == HOLE_ID else f"w{wid}")
        elif tag == 0x02:
            t = TConst(b.rat())
        elif tag in (0x03, 0x04, 0x05):
            l, r = b.u32(), b.u32()
            cls = {0x03: TAdd, 0x04: TMul, 0x05: TSub}[tag]
            t = cls(self.term(l), self.term(r))
        elif tag == 0x06:
            # unary negation (Lean Term.neg — the ge-flip syzygy
            # conclusion reading)
            child = b.u32()
            _need(child < off, "neg child must point backward")
            t = TNeg(self.term(child))
        elif tag == 0x07:
            child, i = b.u32(), b.u32()
            t = TIdx(self.term(child), i)
        elif tag == 0x08:
            # terms-v1 einsum (BINARY.md §6.1): structural parse checks
            # mirror the Rust reader; type consistency is checker
            # territory.
            n_inputs = b.u32()
            _need(n_inputs >= 1, "einsum requires n_inputs >= 1")
            n_indices = b.u32()
            extents = tuple(b.u64() for _ in range(n_indices))
            inputs = []
            for _ in range(n_inputs):
                child = b.u32()
                _need(child < off, "einsum child must point backward")
                rank = b.u32()
                bindings = tuple(b.u32() for _ in range(rank))
                _need(all(x < n_indices for x in bindings),
                      "einsum input binding out of range")
                inputs.append((self.term(child), bindings))
            out_rank = b.u32()
            out_bindings = tuple(b.u32() for _ in range(out_rank))
            _need(all(x < n_indices for x in out_bindings),
                  "einsum out binding out of range")
            _need(len(set(out_bindings)) == len(out_bindings),
                  "einsum out bindings must be pairwise distinct")
            used = set()
            for _, bnd in inputs:
                used.update(bnd)
            _need(used == set(range(n_indices)),
                  "einsum: every index id must occur among input bindings "
                  "(no phantom / output-only ids)")
            t = TEinsum(extents, tuple(inputs), out_bindings)
        elif tag == 0x09:
            # terms-v1 poly (BINARY.md §6.1): every canonicity rule is a
            # parse-time reject; framing against the complex pool via the
            # resolved simplex.
            basis_code = b.u8()
            _need(basis_code in (0, 1),
                  f"poly basis {basis_code} outside terms-v1 "
                  "(2 = Chebyshev RESERVED)")
            basis = "monomial" if basis_code == 0 else "bernstein"
            _need(b.u8() == 0 and b.u8() == 0, "poly pad must be 0")
            dom_ref = b.u32()
            degree = b.u32()
            n_vars = b.u32()
            _need(n_vars >= 1, "poly n_vars must be >= 1")
            support = []
            for _ in range(n_vars):
                wid = b.u32()
                _need(wid != HOLE_ID, "poly support wire: hole forbidden")
                comp = b.u32()
                pair = (f"w{wid}", None if comp == HOLE_ID else comp)
                _need(pair not in support,
                      "poly support entries must be pairwise distinct")
                _need(not any(w2 == pair[0] and
                              ((c2 is None) != (pair[1] is None))
                              for w2, c2 in support),
                      "poly support alias: scalar-use and component forms "
                      "of one wire in one frame")
                support.append(pair)
            if basis == "monomial":
                _need(dom_ref == HOLE_ID,
                      "monomial basis must have absent domain")
                domain = None
                index_len = n_vars
            else:
                _need(dom_ref != HOLE_ID,
                      "bernstein basis requires a domain simplex")
                _need(dom_ref < off, "poly domain must point backward")
                domain = self.simplex(dom_ref)
                _need(len(domain.vertices) == n_vars + 1,
                      "poly domain vertex count != n_vars + 1")
                _need(all(len(v) == n_vars for v in domain.vertices),
                      "poly domain ambient dim != n_vars")
                index_len = n_vars + 1
            n_entries = b.u32()
            entries = []
            prev = None
            max_total = 0
            for _ in range(n_entries):
                alpha = tuple(b.u16() for _ in range(index_len))
                coeff = b.rat()
                _need(coeff != 0, "poly zero coefficient")
                _need(prev is None or prev < alpha,
                      "poly entries must be strictly ascending lex")
                total = sum(alpha)
                if basis == "bernstein":
                    _need(total == degree,
                          f"bernstein index sums to {total} != degree "
                          f"{degree}")
                max_total = max(max_total, total)
                prev = alpha
                entries.append((alpha, coeff))
            if basis == "monomial":
                _need(max_total == degree,
                      f"monomial degree cross-check: max total {max_total} "
                      f"!= stored degree {degree}")
            t = TPoly(basis, domain, degree, tuple(support), tuple(entries))
            _need(not tpoly_wf_errors(t),
                  f"poly record WF: {tpoly_wf_errors(t)}")
        else:
            raise ReadError(f"term tag 0x{tag:02x} at pool+{off} outside "
                            "the producer subset")
        self.intervals.append((off, b.pos))
        self._terms[off] = t
        return t

    def simplex(self, off: int) -> Simplex:
        if off in self._simplices:
            return self._simplices[off]
        b = _Buf(self.buf, off)
        _need(b.u8() == 0x10, f"expected simplex record at pool+{off}")
        cidx = b.u32()
        _need(cidx < len(self.complexes), "simplex complex index range")
        verts = self.complexes[cidx]
        mask = _bitset_indices(b.raw((len(verts) + 7) // 8), len(verts))
        s = Simplex(tuple(verts[i] for i in mask))
        self.intervals.append((off, b.pos))
        self._simplices[off] = s
        return s

    def extset(self, off: int):
        """Returns (simplex, S) — the python model stores S beside the
        simplex rather than as a separate object."""
        if off in self._extsets:
            return self._extsets[off]
        b = _Buf(self.buf, off)
        _need(b.u8() == 0x11, f"expected extset record at pool+{off}")
        soff = b.u32()
        s = self.simplex(soff)
        nverts = len(s.vertices)
        bits = _bitset_indices(b.raw((nverts + 7) // 8), nverts)
        pair = (s, frozenset(bits))
        self.intervals.append((off, b.pos))
        self._extsets[off] = pair
        return pair

    def formula(self, off: int) -> Formula:
        if off in self._formulas:
            return self._formulas[off]
        b = _Buf(self.buf, off)
        tag = b.u8()
        if tag == 0x20:
            bt = b.u8()
            _need(bt in BOWTIE_INV, f"bowtie code {bt} outside subset")
            l, r = b.u32(), b.u32()
            f = FAtom(BOWTIE_INV[bt], self.term(l), self.term(r))
        elif tag == 0x21:
            toff, soff, eoff = b.u32(), b.u32(), b.u32()
            s, S = self.extset(eoff)
            _need(self.simplex(soff) == s,
                  "inRegion simplex != extset simplex")
            f = FInRegion(self.term(toff), s, S)
        elif tag in (0x22, 0x23):
            l, r = b.u32(), b.u32()
            cls = FAnd if tag == 0x22 else FOr
            f = cls(self.formula(l), self.formula(r))
        elif tag in (0x24, 0x26):
            # 0x26 is the zero-payload sph marker; the producer's SP_H
            # terminus is FTrue in the python model (module docstring).
            f = FTrue()
        elif tag == 0x25:
            f = FFalse()
        else:
            raise ReadError(f"formula tag 0x{tag:02x} at pool+{off} "
                            "outside the producer subset")
        self.intervals.append((off, b.pos))
        self._formulas[off] = f
        return f

    def judgment(self, off: int) -> Judgment:
        if off in self._judgments:
            return self._judgments[off]
        b = _Buf(self.buf, off)
        _need(b.u8() == 0x30, f"expected judgment record at pool+{off}")
        pre, post = b.u32(), b.u32()
        j = Judgment(self.formula(pre), self.formula(post))
        self.intervals.append((off, b.pos))
        self._judgments[off] = j
        return j

    # ---- family-v1 (BINARY.md SS6.1 0x40 / 0x31) ----------------------

    def blocklattice(self, off: int):
        # Parse a 0x40 record -> (axes, blocks_raw) with every SS6.1
        # parse rule enforced; facet-proof OFFSETS returned unresolved
        # (nodes are the caller region). Memoized.
        if not hasattr(self, "_blocklattices"):
            self._blocklattices = {}
        if off in self._blocklattices:
            return self._blocklattices[off]
        b = _Buf(self.buf, off)
        _need(b.u8() == 0x40, f"expected blocklattice record at pool+{off}")
        amb = b.u8()
        _need(1 <= amb <= 2,
              f"blocklattice amb_dim {amb} outside the family-v1 gate")
        _need(b.u8() == 0 and b.u8() == 0, "blocklattice pad must be 0")
        axes = []
        wires_seen = set()
        for i in range(amb):
            wid = b.u32()
            _need(wid != HOLE_ID, "blocklattice axis wire: hole forbidden")
            _need(wid not in wires_seen, "duplicate blocklattice axis wire")
            wires_seen.add(wid)
            # F-A6 (review round 2): byte-level axis-wire predicate.
            _need(self.wires is not None and wid < len(self.wires),
                  "blocklattice axis wire out of range")
            _, dt, shape = self.wires[wid]
            _need(dt == "Q" and tuple(shape) == (1,),
                  "blocklattice axis wire must be the scalar exact-Q "
                  "convention <[1], Q> (F-A6)")
            dref = b.u32()
            _need(dref < off, "blocklattice drift must point backward")
            drift = self.term(dref)
            # F-A5 (review round 2): drift-term fragment gate — pinning is
            # defined only on the scalar polynomial tree.
            def frag_ok(t):
                if isinstance(t, TVar):
                    return t.wire != HOLE
                if isinstance(t, TConst):
                    return True
                if isinstance(t, (TAdd, TMul, TSub)):
                    return frag_ok(t.l) and frag_ok(t.r)
                return False
            _need(frag_ok(drift),
                  "blocklattice drift outside the scalar tree fragment "
                  "(const/var/add/mul/sub only — F-A5)")
            ng = b.u32()
            _need(ng >= 2, "blocklattice axis needs >= 2 gridlines")
            glines = tuple(b.rat() for _ in range(ng))
            _need(all(glines[k] < glines[k + 1] for k in range(ng - 1)),
                  "blocklattice gridlines must be strictly increasing")
            axes.append((f"w{wid}", drift, glines))
        n_cells = 1
        for (_, _, g) in axes:
            n_cells *= len(g) - 1
        n_blocks = b.u32()
        _need(n_blocks >= 1, "blocklattice n_blocks must be >= 1")
        blocks_raw = []
        seen = set()
        probe = BlockLattice(axes=tuple(axes), blocks=())
        for _ in range(n_blocks):
            cells = frozenset(
                _bitset_indices(b.raw((n_cells + 7) // 8), n_cells))
            _need(cells and cells < frozenset(range(n_cells)),
                  "blocklattice block must be a nonempty PROPER cell "
                  "subset")
            _need(cells not in seen, "duplicate blocklattice block")
            seen.add(cells)
            n_slots = b.u32()
            want = len(probe.boundary_facets(cells))
            _need(n_slots == want,
                  f"blocklattice facet-slot count {n_slots} != recomputed "
                  f"boundary count {want}")
            offs = tuple(b.u64() for _ in range(n_slots))
            blocks_raw.append((cells, offs))
        _need(b.u32() == HOLE_ID,
              "blocklattice ext_ref must be the absent sentinel "
              "(Morse+ reservation)")
        out = (tuple(axes), tuple(blocks_raw))
        self.intervals.append((off, b.pos))
        self._blocklattices[off] = out
        return out

    def fam_judgment(self, off: int) -> int:
        # Parse a 0x31 record -> the blocklattice poolref it carries.
        if not hasattr(self, "_famjudgments"):
            self._famjudgments = {}
        if off in self._famjudgments:
            return self._famjudgments[off]
        b = _Buf(self.buf, off)
        _need(b.u8() == 0x31, f"expected famJudgment record at pool+{off}")
        bl = b.u32()
        self.blocklattice(bl)  # type + rules check
        self.intervals.append((off, b.pos))
        self._famjudgments[off] = bl
        return bl

    def enc_judgment(self, off: int) -> EncJudgment:
        # Parse a 0x32 record (enclosure-v1, BINARY.md SS6.1): u8 0x32 ·
        # u8 func_tag · u8[3] pad=0 · u32 n · Q r · Q R.  Coefficients
        # are never on the wire (recompute pattern).
        if not hasattr(self, "_encjudgments"):
            self._encjudgments = {}
        if off in self._encjudgments:
            return self._encjudgments[off]
        b = _Buf(self.buf, off)
        _need(b.u8() == 0x32, f"expected encJudgment record at pool+{off}")
        ft = b.u8()
        _need(ft in (0, 1, 2), f"unknown enclosure func_tag {ft}")
        _need(b.u8() == 0 and b.u8() == 0 and b.u8() == 0,
              "encJudgment pad must be 0")
        n = b.u32()
        r = b.rat()
        R = b.rat()
        out = EncJudgment(func=ENC_FUNCS[ft], n=n, r=r, R=R)
        self.intervals.append((off, b.pos))
        self._encjudgments[off] = out
        return out


# ---------------------------------------------------------------------------
# combination-term unzipping + extraction-chain reconstruction
# ---------------------------------------------------------------------------

def unzip_combination(cc: Term):
    """Inverse of emit's `_combination_term` AST shape:
    TAdd(TMul(TConst(w1), e1), TAdd(..., TConst(0))) -> [(w1, e1), ...]."""
    entries = []
    t = cc
    while isinstance(t, TAdd):
        head = t.l
        _need(isinstance(head, TMul) and isinstance(head.l, TConst),
              "combination entry is not TMul(TConst(w), e)")
        entries.append((head.l.value, head.r))
        t = t.r
    _need(isinstance(t, TConst) and t.value == 0,
          "combination terminator is not TConst(0)")
    return entries


def _conjunct_paths(f: Formula, path=()):
    """Every (path, conjunct) of the AND-tree, root first (conj_get order:
    'l'/'r' steps into FAnd)."""
    yield path, f
    if isinstance(f, FAnd):
        yield from _conjunct_paths(f.l, path + ("l",))
        yield from _conjunct_paths(f.r, path + ("r",))


def extraction_chain(pre: Formula, target: Formula) -> Proof:
    """The canonical PAx + PAndE chain deriving `pre |- target` for a
    conjunct of pre — the reconstruction of the premise proof the wire's
    leaf-form Farkas dropped at emission."""
    for path, sub in _conjunct_paths(pre):
        if sub == target:
            proof = PAx(Judgment(pre, pre))
            walked = pre
            for step in path:
                walked = walked.l if step == "l" else walked.r
                proof = PAndE(Judgment(pre, walked), premise=proof,
                              which=step)
            return proof
    raise ReadError(f"Farkas entry is not a pre-conjunct (leaf "
                    f"discipline): {target}")


# ---------------------------------------------------------------------------
# the reader
# ---------------------------------------------------------------------------

class ReadResult:
    def __init__(self, hypernet, vc_hyp, vc_post, root, stats):
        self.hypernet = hypernet
        self.vc_hyp = vc_hyp
        self.vc_post = vc_post
        self.root = root
        self.stats = stats


def read_certificate(data: bytes) -> ReadResult:
    _need(len(data) >= 128, "shorter than the 128-byte header")
    h = _Buf(data)
    _need(h.raw(8) == MAGIC, "bad magic")
    _need(h.u32() == 1, "version != 1")
    h.u32()  # flags
    symtab_off, symtab_len = h.u64(), h.u64()
    payload_off, payload_len = h.u64(), h.u64()
    diagram_off, diagram_len = h.u64(), h.u64()
    proof_off, proof_len = h.u64(), h.u64()
    n_wires, n_apps = h.u32(), h.u32()
    n_proof_nodes, n_complexes = h.u32(), h.u32()
    root_off = h.u64()
    theta_ref = h.u32()
    _need(n_apps == 0,
          "reader subset: app-free hypernets only (producer certificates)")
    _need(payload_len == 0, "reader subset: no bulk payload section")

    # ---- symbol table ----
    st = _Buf(data, symtab_off)
    wires = []
    for i in range(n_wires):
        kind, sign, ext, pad = st.u8(), st.u8(), st.u8(), st.u8()
        _need(pad == 0, "symtab pad byte must be 0")
        _need(kind in KIND_DTYPE, f"wire {i} dtype kind {kind} outside "
              "the checker's Q/B subset")
        rank = st.u32()
        shape_aux = st.u64()
        pl_off, pl_len = st.u64(), st.u64()
        _need(pl_off == NO_PAYLOAD and pl_len == 0,
              "reader subset: payload-free wires only")
        aux = _Buf(data, symtab_off + shape_aux)
        shape = tuple(aux.u64() for _ in range(rank))
        wires.append((f"w{i}", KIND_DTYPE[kind], shape))
    _need(st.pos <= symtab_off + symtab_len, "symbol table overrun")

    # ---- diagram section: complexes as vertex tuples ----
    d = _Buf(data, diagram_off)
    n_cplx_inline = d.u32()
    _need(n_cplx_inline == n_complexes,
          "diagram complex count != header n_complexes")
    complexes = []
    for _ in range(n_complexes):
        nv, ad = d.u32(), d.u32()
        verts = tuple(tuple(d.rat() for _ in range(ad)) for _ in range(nv))
        n_masks = d.u32()
        for _ in range(n_masks):
            _bitset_indices(d.raw((nv + 7) // 8), nv)
        _need(d.u32() == 0, "reader subset: n_cells == 0")
        complexes.append(verts)
    _need(d.u32() == 0, "diagram n_apps must be 0 in the subset")
    _need(d.pos - diagram_off <= diagram_len, "diagram section overrun")

    # ---- proof section ----
    p = _Buf(data, proof_off)
    pool_len = p.u64()
    pool_bytes = p.raw(pool_len)
    pool = _Pool(pool_bytes, complexes, wires)
    nodes_base = 8 + pool_len  # node offsets are proof-section-relative

    node_cache = {}
    node_intervals = []

    def node(off: int) -> Proof:
        if off in node_cache:
            return node_cache[off]
        _need(off >= nodes_base, f"node offset {off} points into the pool")
        b = _Buf(data, proof_off + off)
        tag, variant = b.u8(), b.u8()
        _need(b.u16() == 0, "node reserved u16 must be 0")
        if tag == 27:
            # family-v1: concludes is a famJudgment record (0x31), and
            # every payload rule of SS6.2 tag 27 is a parse rule here;
            # [F2]-[F5] live in the checker.
            _need(variant == 0, "productLattice variant")
            fj_ref = b.u32()
            fj_bl = pool.fam_judgment(fj_ref)
            lb, rb, cb = b.u32(), b.u32(), b.u32()
            _need(cb == fj_bl,
                  "tag-27 concludes famJudgment must carry composite_bl")
            flows = b.u8()
            _need(flows in (0, 1), "flows_only must be 0 or 1")
            _need(b.u8() == 0 and b.u8() == 0 and b.u8() == 0,
                  "productLattice pad must be 0")
            _need(b.u32() == HOLE_ID,
                  "productLattice ext_ref must be the absent sentinel")

            def resolve_lattice(bl_ref):
                axes, blocks_raw = pool.blocklattice(bl_ref)
                fam_blocks = []
                for cells, offs in blocks_raw:
                    proofs = []
                    for o in offs:
                        _need(nodes_base <= o < off,
                              "facet off64 must name an earlier node "
                              "(cross-region rule)")
                        proofs.append(node(o))
                    fam_blocks.append(FamBlock(cells, tuple(proofs)))
                return BlockLattice(axes=axes, blocks=tuple(fam_blocks))

            left = resolve_lattice(lb)
            right = resolve_lattice(rb)
            comp = resolve_lattice(cb)
            out = PProductLattice(concludes=FamJudgment(comp), left=left,
                                  right=right, composite=comp,
                                  flows_only=bool(flows))
            node_intervals.append((off, b.pos - proof_off))
            node_cache[off] = out
            return out
        if tag == 28:
            # enclosure-v1 (BINARY.md SS6.2 tag 28): a LEAF whose 0x32
            # conclusion carries the whole witness; encCheck lives in
            # the checker, parse rules here.
            _need(variant == 0, "enclosure variant must be 0")
            ej = pool.enc_judgment(b.u32())
            out = PEnclosure(concludes=ej)
            node_intervals.append((off, b.pos - proof_off))
            node_cache[off] = out
            return out
        concludes = pool.judgment(b.u32())
        if tag == 0:
            _need(variant == 0, "Ax variant")
            out = PAx(concludes)
        elif tag == 2:
            cf = pool.formula(b.u32())
            l, r = b.u64(), b.u64()
            out = PCut(concludes, cutFormula=cf, left=node(l), right=node(r))
        elif tag == 3:
            l, r = b.u64(), b.u64()
            out = PAndI(concludes, l=node(l), r=node(r))
        elif tag == 4:
            prem = node(b.u64())
            other = pool.formula(b.u32())
            which = "l" if variant == 0 else "r"
            pj = prem.concludes.post
            _need(isinstance(pj, FAnd), "AndE premise post is not FAnd")
            _need(other == (pj.r if which == "l" else pj.l),
                  "AndE stored `other` != the non-selected conjunct")
            out = PAndE(concludes, premise=prem, which=which)
        elif tag == 6:
            l, r = b.u64(), b.u64()
            plen = b.u32()
            steps = b.raw(plen)
            _need(all(s in (0, 1) for s in steps), "OrE path step byte")
            path = tuple("l" if s == 0 else "r" for s in steps)
            out = POrECtx(concludes, path=path, left=node(l), right=node(r))
        elif tag == 7:
            e, body = b.u64(), b.u64()
            wid = b.u32()
            t, u, bf = b.u32(), b.u32(), b.u32()
            out = PEqElim(concludes, eq=node(e), body=node(body),
                          wire=(HOLE if wid == HOLE_ID else f"w{wid}"),
                          termT=pool.term(t), termU=pool.term(u),
                          bodyForm=pool.formula(bf))
        elif tag in (8, 9):
            # ConvIntro(8)/ConvElim(9): premise off64, then term/simplex/
            # extset poolrefs (BINARY.md tag table; layout mirrored from
            # the Rust reader + the HOL fused parser).
            prem = node(b.u64())
            t = pool.term(b.u32())
            s = pool.simplex(b.u32())
            es, S = pool.extset(b.u32())
            _need(es == s, "ConvIntro/ConvElim extset simplex != simplex")
            cls = PConvIntro if tag == 8 else PConvElim
            out = cls(concludes, premise=prem, term=t, simplex=s, S=S)
        elif tag == 11:
            reg = node(b.u64())
            tx = pool.term(b.u32())
            s = pool.simplex(b.u32())
            es, S = pool.extset(b.u32())
            _need(es == s, "BernCone extset simplex != simplex")
            degree = b.u32()
            poly = pool.term(b.u32())
            pred = pool.formula(b.u32())
            out = PBernCone(concludes, regionProof=reg, termX=tx, simplex=s,
                            S=S, degree=degree, polynomial=poly,
                            predicate=pred, stored_grid=())
        elif tag == 14:
            cc = pool.term(b.u32())
            concl = pool.term(b.u32())
            b.u64()  # den_bound_log2 (Q7 metadata; no checker weight)
            entries = unzip_combination(cc)
            premises = tuple(
                extraction_chain(concludes.pre,
                                 FAtom("<=", e, TConst(Rational(0))))
                for _, e in entries)
            out = PFarkas(concludes, premises=premises,
                          lambdas=tuple(w for w, _ in entries),
                          conclusion=concl)
        elif tag == 25:
            _need(variant == 0, "Promise variant")
            sup_off, con_off = b.u64(), b.u64()
            contract = pool.formula(b.u32())
            plen = b.u32()
            steps = b.raw(plen)
            _need(all(s in (0, 1) for s in steps), "Promise path step byte")
            path = tuple("l" if s == 0 else "r" for s in steps)
            n_if = b.u32()
            iface = tuple(f"w{b.u32()}" for _ in range(n_if))
            out = PPromise(concludes, supplier=node(sup_off),
                           consumer=node(con_off), contract=contract,
                           path=path, iface=iface)
        elif tag == 26:
            n = b.u32()
            comp_offs = [b.u64() for _ in range(n)]
            cc = pool.term(b.u32())
            concl = pool.term(b.u32())
            b.u64()  # den_bound_log2
            th_ref = b.u32()
            theta = None if th_ref == HOLE_ID else pool.term(th_ref)
            if theta is not None:
                _need(isinstance(theta, TConst), "syzygy theta poolref "
                      "must be a term-const record")
                theta = theta.value
            comps = tuple(node(o) for o in comp_offs)
            entries = unzip_combination(cc)
            _need(len(entries) == len(comps),
                  "syzygy combination arity != component count")
            lambdas = []
            for (w, e), comp in zip(entries, comps):
                post = comp.concludes.post
                _need(isinstance(post, FAtom), "syzygy component post shape")
                if post.op == "=":
                    if e == TSub(post.l, post.r):
                        lambdas.append(w)
                    elif e == TSub(post.r, post.l):
                        lambdas.append(-w)
                    else:
                        raise ReadError("syzygy eq-entry matches neither "
                                        "polarity of the component post")
                else:
                    _need(e == post.l, "syzygy entry != component post LHS")
                    lambdas.append(w)
            out = PSyzygy(concludes, components=comps,
                          lambdas=tuple(lambdas), conclusion=concl,
                          theta=theta)
        elif tag == 27:
            # family-v1 productLattice (BINARY.md SS6.2). concludes is a
            # famJudgment (0x31); the generic path above already parsed
            # it as a 0x30 — undone here by tag dispatch, so tag 27 is
            # handled BEFORE the generic concludes read (see wrapper).
            raise ReadError("tag-27 dispatch must not reach the generic "
                            "concludes path (reader bug)")
        else:
            raise ReadError(f"proof tag {tag} outside the producer subset")
        node_intervals.append((off, b.pos - proof_off))
        node_cache[off] = out
        return out

    root = node(root_off)
    for o, nd in node_cache.items():
        _need(not isinstance(nd, PEnclosure) or o == root_off,
              "tag-28 (enclosure) nodes are only legal at root "
              "(BINARY.md SS6.3 enclosure-root profile)")
    # record-boundary rule, both regions (BINARY.md §6.1)
    pool.check_partition()
    cursor = nodes_base
    for start, end in sorted(node_intervals):
        _need(start == cursor,
              f"node region not partitioned: node at {start}, expected "
              f"{cursor}")
        cursor = end
    _need(cursor == proof_len,
          f"node region not partitioned: nodes end at {cursor}, section "
          f"is {proof_len} bytes")
    _need(len(node_cache) == n_proof_nodes,
          f"reachable node count {len(node_cache)} != header "
          f"n_proof_nodes {n_proof_nodes}")

    # header theta_ref cross-check (BINARY §2: min over present per-node
    # thetas, or absent)
    thetas = [n_.theta for n_ in node_cache.values()
              if isinstance(n_, PSyzygy) and n_.theta is not None]
    if theta_ref == HOLE_ID:
        _need(not thetas, "theta_ref absent but per-node thetas present")
        theta_val = None
    else:
        t = pool.term(theta_ref)
        _need(isinstance(t, TConst), "theta_ref must point at a term-const")
        _need(thetas and t.value == min(thetas),
              "theta_ref != min over present per-node thetas")
        theta_val = t.value

    # ---- the checker's calling convention ----
    hypernet = Hypernet(
        wires=tuple(Wire(nm, dt) for nm, dt, _ in wires),
        prims=(),
        inputs=tuple(nm for nm, _, _ in wires),
        outputs=(),
    )
    if isinstance(root, (PProductLattice, PEnclosure)):
        # SS6.3 judgement-kind roots (family certificate / enclosure
        # witness artefact): no Phi/sph decomposition applies.
        vc_hyp, vc_post = None, None
    else:
        pre = root.concludes.pre
        _need(isinstance(pre, FAnd) and pre.r == FTrue(),
              "root pre is not FAnd(vc_hyp, sp_H-terminus)")
        vc_hyp, vc_post = pre.l, root.concludes.post

    stats = {
        "bytes": len(data),
        "n_wires": n_wires,
        "n_proof_nodes": n_proof_nodes,
        "n_complexes": n_complexes,
        "pool_bytes": pool_len,
        "theta_ref": theta_val,
        "wire_shapes": [shape for _, _, shape in wires],
    }
    return ReadResult(hypernet, vc_hyp, vc_post, root, stats)


def read_certificate_file(path: str) -> ReadResult:
    with open(path, "rb") as fh:
        return read_certificate(fh.read())
