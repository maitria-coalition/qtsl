"""dump_model.py — canonical model dump of a bernfmt certificate, via
`read_bernfmt.py` (the wire-side reference reader).

The differential partner of `read_rows.ts`: both emit the same
`rows-model-dump v1` text for one certificate read from their respective
stored forms (bernfmt bytes here; object-row listings there), so
byte-diffing the two dumps is a model-identity test of the whole
read path. Interning is by VALUE in first-visit canonical DFS order —
identical traversal is specified by the dump grammar itself, so equal
models yield byte-equal dumps regardless of sharing topology.

Usage: python3 dump_model.py cert.bernfmt
Exit 0 = dump on stdout; exit 3 = one `REFUSED <reason>` line (ReadError);
anything else is a crash and a bug.
"""

from __future__ import annotations

import sys

from read_bernfmt import ReadError, read_certificate_file
from bl_cert import (
    FAnd, FAtom, FFalse, FInRegion, FOr, FTrue, HOLE, PAndE, PAndI, PAx,
    PBernCone, PConvElim, PConvIntro, PCut, PEnclosure, PEqElim, PFarkas,
    POrECtx, PProductLattice, PPromise, PSyzygy, TAdd, TConst, TEinsum,
    TIdx, TMul, TNeg, TPoly, TSub, TVar,
)


def rat(r):
    return f"{r.p}/{r.q}"


class Dumper:
    def __init__(self):
        self.defs = []
        self.ids = {}

    def _def(self, body: str) -> int:
        if body in self.ids:
            return self.ids[body]
        i = len(self.defs)
        self.defs.append(body)
        self.ids[body] = i
        return i

    def term(self, t) -> int:
        if isinstance(t, TVar):
            return self._def("hole" if t.wire is HOLE else f"var {t.wire}")
        if isinstance(t, TConst):
            return self._def(f"const {rat(t.value)}")
        if isinstance(t, (TAdd, TMul, TSub)):
            k = {TAdd: "add", TMul: "mul", TSub: "sub"}[type(t)]
            return self._def(f"{k} D{self.term(t.l)} D{self.term(t.r)}")
        if isinstance(t, TNeg):
            return self._def(f"neg D{self.term(t.t)}")
        if isinstance(t, TIdx):
            return self._def(f"idx D{self.term(t.t)} {t.i}")
        if isinstance(t, (TEinsum, TPoly)):
            raise ReadError(f"{type(t).__name__} outside the rows reader subset")
        raise AssertionError(f"unknown term {t!r}")

    def simplex(self, s) -> int:
        coords = ";".join(
            "(" + ",".join(rat(c) for c in v) + ")" for v in s.vertices
        )
        return self._def(f"splx {len(s.vertices)} [{coords}]")

    def formula(self, f) -> int:
        if isinstance(f, FTrue):
            return self._def("tt")
        if isinstance(f, FFalse):
            return self._def("ff")
        if isinstance(f, FAtom):
            return self._def(f"atom {f.op} D{self.term(f.l)} D{self.term(f.r)}")
        if isinstance(f, FInRegion):
            S = ",".join(str(x) for x in sorted(f.S))
            return self._def(f"inreg D{self.term(f.term)} D{self.simplex(f.simplex)} {{{S}}}")
        if isinstance(f, (FAnd, FOr)):
            k = "and" if isinstance(f, FAnd) else "or"
            return self._def(f"{k} D{self.formula(f.l)} D{self.formula(f.r)}")
        raise AssertionError(f"unknown formula {f!r}")

    def judgment(self, j) -> int:
        return self._def(f"judg D{self.formula(j.pre)} D{self.formula(j.post)}")

    def lattice(self, bl) -> int:
        axes = ";".join(
            f"({w} D{self.term(drift)} [{','.join(rat(g) for g in grid)}])"
            for (w, drift, grid) in bl.axes
        )
        blocks = ";".join(
            "({%s} [%s])"
            % (
                ",".join(str(c) for c in sorted(b.cells)),
                ",".join(f"D{self.proof(p)}" for p in b.facet_proofs),
            )
            for b in bl.blocks
        )
        return self._def(f"blat [{axes}] [{blocks}]")

    def proof(self, p) -> int:
        def path(x):
            return "".join(x) if x else "."

        if isinstance(p, PAx):
            return self._def(f"ax D{self.judgment(p.concludes)}")
        if isinstance(p, PCut):
            return self._def(
                f"cut D{self.judgment(p.concludes)} D{self.formula(p.cutFormula)}"
                f" D{self.proof(p.left)} D{self.proof(p.right)}"
            )
        if isinstance(p, PAndI):
            return self._def(
                f"andi D{self.judgment(p.concludes)} D{self.proof(p.l)} D{self.proof(p.r)}"
            )
        if isinstance(p, PAndE):
            return self._def(
                f"ande D{self.judgment(p.concludes)} D{self.proof(p.premise)} {p.which}"
            )
        if isinstance(p, POrECtx):
            return self._def(
                f"orectx D{self.judgment(p.concludes)} {path(p.path)}"
                f" D{self.proof(p.left)} D{self.proof(p.right)}"
            )
        if isinstance(p, PEqElim):
            wire = "hole" if p.wire is HOLE else p.wire
            return self._def(
                f"eqelim D{self.judgment(p.concludes)} D{self.proof(p.eq)}"
                f" D{self.proof(p.body)} {wire} D{self.term(p.termT)}"
                f" D{self.term(p.termU)} D{self.formula(p.bodyForm)}"
            )
        if isinstance(p, (PConvIntro, PConvElim)):
            k = "convintro" if isinstance(p, PConvIntro) else "convelim"
            S = ",".join(str(x) for x in sorted(p.S))
            return self._def(
                f"{k} D{self.judgment(p.concludes)} D{self.proof(p.premise)}"
                f" D{self.term(p.term)} D{self.simplex(p.simplex)} {{{S}}}"
            )
        if isinstance(p, PBernCone):
            S = ",".join(str(x) for x in sorted(p.S))
            return self._def(
                f"berncone D{self.judgment(p.concludes)} D{self.proof(p.regionProof)}"
                f" D{self.term(p.termX)} D{self.simplex(p.simplex)} {{{S}}}"
                f" {p.degree} D{self.term(p.polynomial)} D{self.formula(p.predicate)}"
            )
        if isinstance(p, PFarkas):
            # entries: each premise concludes `pre |- (e <= 0)`; the dump
            # carries e (the premises themselves are the canonical
            # extraction chains, derived data on both sides).
            entries = [prem.concludes.post.l for prem in p.premises]
            return self._def(
                f"farkas D{self.judgment(p.concludes)}"
                f" [{','.join(rat(w) for w in p.lambdas)}]"
                f" [{','.join(f'D{self.term(e)}' for e in entries)}]"
                f" D{self.term(p.conclusion)}"
            )
        if isinstance(p, PPromise):
            return self._def(
                f"promise D{self.judgment(p.concludes)} D{self.proof(p.supplier)}"
                f" D{self.proof(p.consumer)} D{self.formula(p.contract)}"
                f" {path(p.path)} [{','.join(p.iface)}]"
            )
        if isinstance(p, PSyzygy):
            theta = rat(p.theta) if p.theta is not None else "-"
            return self._def(
                f"syzygy D{self.judgment(p.concludes)}"
                f" [{','.join(f'D{self.proof(c)}' for c in p.components)}]"
                f" [{','.join(rat(w) for w in p.lambdas)}]"
                f" D{self.term(p.conclusion)} {theta}"
            )
        if isinstance(p, PProductLattice):
            return self._def(
                f"pprod D{self.lattice(p.composite)} D{self.lattice(p.left)}"
                f" D{self.lattice(p.right)} {1 if p.flows_only else 0}"
            )
        if isinstance(p, PEnclosure):
            e = p.concludes
            return self._def(f"penc {e.func} {e.n} {rat(e.r)} {rat(e.R)}")
        raise AssertionError(f"unknown proof node {p!r}")

    def render(self, res) -> str:
        lines = ["FORMAT rows-model-dump v1"]
        for w, shape in zip(res.hypernet.wires, res.stats["wire_shapes"]):
            lines.append(f"W {w.name} {w.dtype} [{','.join(str(s) for s in shape)}]")
        root_id = self.proof(res.root)
        vc_h = "-" if res.vc_hyp is None else f"D{self.formula(res.vc_hyp)}"
        vc_p = "-" if res.vc_post is None else f"D{self.formula(res.vc_post)}"
        for i, d in enumerate(self.defs):
            lines.append(f"D{i} {d}")
        lines.append(f"VC_HYP {vc_h}")
        lines.append(f"VC_POST {vc_p}")
        lines.append(f"ROOT D{root_id}")
        theta = res.stats["theta_ref"]
        lines.append(
            "COUNTS wires=%d complexes=%d proof_nodes=%d theta=%s"
            % (
                res.stats["n_wires"],
                res.stats["n_complexes"],
                res.stats["n_proof_nodes"],
                rat(theta) if theta is not None else "-",
            )
        )
        return "\n".join(lines) + "\n"


def dump_one(path: str) -> tuple[str, int]:
    """(text, exit_code) for one certificate — dump, or one REFUSED line."""
    try:
        res = read_certificate_file(path)
        return Dumper().render(res), 0
    except ReadError as e:
        return f"REFUSED {e}\n", 3


def main():
    sys.setrecursionlimit(1_000_000)
    if len(sys.argv) == 3 and sys.argv[1] == "--batch":
        # batch: each line of the pairs file is `<input>\t<output>`;
        # per-file refusals land in the output file; always exit 0.
        import os

        for line in open(sys.argv[2]):
            line = line.rstrip("\n")
            if not line:
                continue
            inp, out = line.split("\t")
            os.makedirs(os.path.dirname(out), exist_ok=True)
            try:
                text, _ = dump_one(inp)
            except Exception as e:  # crash = a bug, but keep the batch going
                text = f"CRASH {type(e).__name__}: {e}\n"
            with open(out, "w") as fh:
                fh.write(text)
        return
    if len(sys.argv) != 2:
        print("usage: dump_model.py cert.bernfmt | --batch pairs.tsv", file=sys.stderr)
        sys.exit(2)
    text, code = dump_one(sys.argv[1])
    sys.stdout.write(text)
    sys.exit(code)


if __name__ == "__main__":
    main()
