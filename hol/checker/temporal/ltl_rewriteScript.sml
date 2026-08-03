(*
  Temporal rewrite rules over omega-words: LTL formulas over an atom
  alphabet, positional satisfaction over omega-words, each rewrite rule
  proved a denotation equality (satisfaction at every position of every
  trace), the congruence closure (a rule applied at any position),
  chain soundness via reflexive-transitive closure, and the consumption
  bridge from a demonic ranking conclusion to GF-satisfaction. Mirrors
  the Lean development's TemporalRewrite module statement for
  statement.
*)
open HolKernel Parse boolLib bossLib;
open arithmeticTheory relationTheory;

val _ = new_theory "ltl_rewrite";

Datatype:
  form = Atom 'a
       | Neg form
       | Conj form form
       | Disj form form
       | Impl form form
       | Next form
       | Fut form
       | Glob form
       | Until form form
       | FutLe num form
       | GlobLe num form
       | UntilLe num form form
End

Definition sat_def:
  (sat V i (Atom a) <=> V i a) /\
  (sat V i (Neg f) <=> ~sat V i f) /\
  (sat V i (Conj f g) <=> sat V i f /\ sat V i g) /\
  (sat V i (Disj f g) <=> sat V i f \/ sat V i g) /\
  (sat V i (Impl f g) <=> (sat V i f ==> sat V i g)) /\
  (sat V i (Next f) <=> sat V (i + 1) f) /\
  (sat V i (Fut f) <=> ?j. i <= j /\ sat V j f) /\
  (sat V i (Glob f) <=> !j. i <= j ==> sat V j f) /\
  (sat V i (Until s t) <=>
     ?j. i <= j /\ sat V j t /\ !k. i <= k /\ k < j ==> sat V k s) /\
  (sat V i (FutLe n f) <=> ?j. i <= j /\ j <= i + n /\ sat V j f) /\
  (sat V i (GlobLe n f) <=> !j. i <= j /\ j <= i + n ==> sat V j f) /\
  (sat V i (UntilLe n s t) <=>
     ?j. i <= j /\ j <= i + n /\ sat V j t /\
         !k. i <= k /\ k < j ==> sat V k s)
End

Theorem sat_imp_elim:
  !V i f g. sat V i (Impl f g) <=> sat V i (Disj (Neg f) g)
Proof
  rw[sat_def] >> metis_tac[]
QED

Theorem sat_or_and_r:
  !V i f g h.
    sat V i (Disj f (Conj g h)) <=> sat V i (Conj (Disj f g) (Disj f h))
Proof
  rw[sat_def] >> metis_tac[]
QED

Theorem sat_neg_neg:
  !V i f. sat V i (Neg (Neg f)) <=> sat V i f
Proof
  rw[sat_def]
QED

Theorem sat_neg_and:
  !V i f g. sat V i (Neg (Conj f g)) <=> sat V i (Disj (Neg f) (Neg g))
Proof
  rw[sat_def] >> metis_tac[]
QED

Theorem sat_neg_or:
  !V i f g. sat V i (Neg (Disj f g)) <=> sat V i (Conj (Neg f) (Neg g))
Proof
  rw[sat_def] >> metis_tac[]
QED

Theorem sat_neg_F:
  !V i f. sat V i (Neg (Fut f)) <=> sat V i (Glob (Neg f))
Proof
  rw[sat_def] >> metis_tac[]
QED

Theorem sat_neg_G:
  !V i f. sat V i (Neg (Glob f)) <=> sat V i (Fut (Neg f))
Proof
  rw[sat_def] >> metis_tac[]
QED

Theorem sat_neg_X:
  !V i f. sat V i (Neg (Next f)) <=> sat V i (Next (Neg f))
Proof
  rw[sat_def]
QED

Theorem sat_gf_or_fusion:
  !V i f g.
    sat V i (Disj (Glob (Fut f)) (Glob (Fut g))) <=>
    sat V i (Glob (Fut (Disj f g)))
Proof
  rw[sat_def] >> eq_tac
  >- (rw[] >> metis_tac[])
  >- (rw[] >> metis_tac[LESS_EQ_ADD, ADD_COMM, LESS_EQ_TRANS])
QED

(*
  The fusion family (polarity absorption): over omega-words the
  exists-over-time positions (Fut, the target of Until, the inner Fut of
  GF) absorb Disj and the forall-over-time positions (Glob, the safety of
  Until, the inner Glob of FG) absorb Conj — each a denotation equality.
  sat_gf_or_fusion above is the ninth landed rule; these are its five
  family members. Statement for statement with the Lean development.
*)

Theorem sat_f_or_fusion:
  !V i f g.
    sat V i (Disj (Fut f) (Fut g)) <=> sat V i (Fut (Disj f g))
Proof
  rw[sat_def] >> metis_tac[]
QED

Theorem sat_g_and_fusion:
  !V i f g.
    sat V i (Conj (Glob f) (Glob g)) <=> sat V i (Glob (Conj f g))
Proof
  rw[sat_def] >> metis_tac[]
QED

Theorem sat_fg_and_fusion:
  !V i f g.
    sat V i (Conj (Fut (Glob f)) (Fut (Glob g))) <=>
    sat V i (Fut (Glob (Conj f g)))
Proof
  rw[sat_def] >> eq_tac >> rw[] >>
  metis_tac[LESS_EQ_ADD, ADD_COMM, LESS_EQ_TRANS]
QED

Theorem sat_until_target_or_fusion:
  !V i s t1 t2.
    sat V i (Disj (Until s t1) (Until s t2)) <=>
    sat V i (Until s (Disj t1 t2))
Proof
  rw[sat_def] >> metis_tac[]
QED

Theorem sat_until_safe_and_fusion:
  !V i s1 s2 t.
    sat V i (Conj (Until s1 t) (Until s2 t)) <=>
    sat V i (Until (Conj s1 s2) t)
Proof
  rw[sat_def] >> eq_tac >> rw[]
  >- (Cases_on ‘j <= j'’
      >- (qexists_tac ‘j’ >> rw[] >>
          metis_tac[LESS_LESS_EQ_TRANS])
      >- (qexists_tac ‘j'’ >> rw[] >>
          ‘j' <= j’ by decide_tac >>
          metis_tac[LESS_LESS_EQ_TRANS]))
  >> metis_tac[]
QED

(*
  The bounded-horizon siblings: the same absorption equalities for the
  bounded operators (relative window j <= i + n), the horizon riding the
  witness arithmetic unchanged. FG has no bounded row: its settling time
  is unbounded by construction.
*)

Theorem sat_f_le_or_fusion:
  !V i n f g.
    sat V i (Disj (FutLe n f) (FutLe n g)) <=> sat V i (FutLe n (Disj f g))
Proof
  rw[sat_def] >> metis_tac[]
QED

Theorem sat_g_le_and_fusion:
  !V i n f g.
    sat V i (Conj (GlobLe n f) (GlobLe n g)) <=> sat V i (GlobLe n (Conj f g))
Proof
  rw[sat_def] >> metis_tac[]
QED

Theorem sat_until_le_target_or_fusion:
  !V i n s t1 t2.
    sat V i (Disj (UntilLe n s t1) (UntilLe n s t2)) <=>
    sat V i (UntilLe n s (Disj t1 t2))
Proof
  rw[sat_def] >> metis_tac[]
QED

Theorem sat_until_le_safe_and_fusion:
  !V i n s1 s2 t.
    sat V i (Conj (UntilLe n s1 t) (UntilLe n s2 t)) <=>
    sat V i (UntilLe n (Conj s1 s2) t)
Proof
  rw[sat_def] >> eq_tac >> rw[]
  >- (Cases_on ‘j <= j'’
      >- (qexists_tac ‘j’ >> rw[] >>
          metis_tac[LESS_LESS_EQ_TRANS])
      >- (qexists_tac ‘j'’ >> rw[] >>
          ‘j' <= j’ by decide_tac >>
          metis_tac[LESS_LESS_EQ_TRANS]))
  >> metis_tac[]
QED

(*
  The residue fence: the four tempting fusions outside the absorption
  polarity are refuted by explicit omega-word counterexamples, pinning
  the absorption law's boundary exactly. These double as the mutant
  battery for the fusion family. Parity helpers first.
*)

Triviality mod_two_cases:
  !k. k MOD 2 = 0 \/ k MOD 2 = 1
Proof
  strip_tac >> ‘k MOD 2 < 2’ by simp[MOD_LESS] >> decide_tac
QED

Triviality exists_even_ge:
  !j. ?k. j <= k /\ k MOD 2 = 0
Proof
  strip_tac >> qexists_tac ‘2 * j’ >>
  simp[MOD_2, EVEN_DOUBLE] >> decide_tac
QED

Triviality exists_odd_ge:
  !j. ?k. j <= k /\ k MOD 2 = 1
Proof
  strip_tac >> qexists_tac ‘2 * j + 1’ >>
  simp[MOD_2, EVEN_ADD, EVEN_DOUBLE] >> decide_tac
QED

Triviality one_mod_two:
  1 MOD 2 = 1
Proof
  simp[]
QED

Triviality zero_mod_two:
  0 MOD 2 = 0
Proof
  simp[]
QED

Theorem no_f_and_fusion:
  ?V. sat V 0 (Conj (Fut (Atom 0)) (Fut (Atom 1))) /\
      ~sat V 0 (Fut (Conj (Atom 0) (Atom 1)))
Proof
  qexists_tac ‘\j n. j = n’ >> simp[sat_def]
QED

Theorem no_g_or_fusion:
  ?V. sat V 0 (Glob (Disj (Atom 0) (Atom 1))) /\
      ~sat V 0 (Disj (Glob (Atom 0)) (Glob (Atom 1)))
Proof
  qexists_tac ‘\j n. j MOD 2 = n’ >> conj_tac
  >- (rw[sat_def] >> metis_tac[mod_two_cases])
  >- (rw[sat_def] >>
      metis_tac[one_mod_two, zero_mod_two, ZERO_LESS_EQ,
                DECIDE “(0:num) <> 1”])
QED

Theorem no_gf_and_fusion:
  ?V. sat V 0 (Conj (Glob (Fut (Atom 0))) (Glob (Fut (Atom 1)))) /\
      ~sat V 0 (Glob (Fut (Conj (Atom 0) (Atom 1))))
Proof
  qexists_tac ‘\j n. j MOD 2 = n’ >> conj_tac
  >- (rw[sat_def] >> metis_tac[exists_even_ge, exists_odd_ge])
  >- (rw[sat_def] >>
      metis_tac[ZERO_LESS_EQ, DECIDE “(0:num) <> 1”])
QED

Theorem no_fg_or_fusion:
  ?V. sat V 0 (Fut (Glob (Disj (Atom 0) (Atom 1)))) /\
      ~sat V 0 (Disj (Fut (Glob (Atom 0))) (Fut (Glob (Atom 1))))
Proof
  qexists_tac ‘\j n. j MOD 2 = n’ >> conj_tac
  >- (rw[sat_def] >> metis_tac[mod_two_cases, ZERO_LESS_EQ])
  >- (rw[sat_def] >>
      metis_tac[exists_even_ge, exists_odd_ge,
                DECIDE “(0:num) <> 1”])
QED

Inductive rewrites:
  (!f g. rewrites (Impl f g) (Disj (Neg f) g)) /\
  (!f g h. rewrites (Disj f (Conj g h)) (Conj (Disj f g) (Disj f h))) /\
  (!f. rewrites (Neg (Neg f)) f) /\
  (!f g. rewrites (Neg (Conj f g)) (Disj (Neg f) (Neg g))) /\
  (!f g. rewrites (Neg (Disj f g)) (Conj (Neg f) (Neg g))) /\
  (!f. rewrites (Neg (Fut f)) (Glob (Neg f))) /\
  (!f. rewrites (Neg (Glob f)) (Fut (Neg f))) /\
  (!f. rewrites (Neg (Next f)) (Next (Neg f))) /\
  (!f g. rewrites (Disj (Glob (Fut f)) (Glob (Fut g)))
                  (Glob (Fut (Disj f g)))) /\
  (!f g. rewrites (Disj (Fut f) (Fut g)) (Fut (Disj f g))) /\
  (!f g. rewrites (Conj (Glob f) (Glob g)) (Glob (Conj f g))) /\
  (!f g. rewrites (Conj (Fut (Glob f)) (Fut (Glob g)))
                  (Fut (Glob (Conj f g)))) /\
  (!s t1 t2. rewrites (Disj (Until s t1) (Until s t2))
                      (Until s (Disj t1 t2))) /\
  (!s1 s2 t. rewrites (Conj (Until s1 t) (Until s2 t))
                      (Until (Conj s1 s2) t)) /\
  (!n f g. rewrites (Disj (FutLe n f) (FutLe n g)) (FutLe n (Disj f g))) /\
  (!n f g. rewrites (Conj (GlobLe n f) (GlobLe n g))
                    (GlobLe n (Conj f g))) /\
  (!n s t1 t2. rewrites (Disj (UntilLe n s t1) (UntilLe n s t2))
                        (UntilLe n s (Disj t1 t2))) /\
  (!n s1 s2 t. rewrites (Conj (UntilLe n s1 t) (UntilLe n s2 t))
                        (UntilLe n (Conj s1 s2) t))
End

Theorem rewrites_sound:
  !f g. rewrites f g ==> !V i. (sat V i f <=> sat V i g)
Proof
  Induct_on ‘rewrites’ >> rw[] >>
  metis_tac[sat_imp_elim, sat_or_and_r, sat_neg_neg, sat_neg_and,
            sat_neg_or, sat_neg_F, sat_neg_G, sat_neg_X,
            sat_gf_or_fusion, sat_f_or_fusion, sat_g_and_fusion,
            sat_fg_and_fusion, sat_until_target_or_fusion,
            sat_until_safe_and_fusion, sat_f_le_or_fusion,
            sat_g_le_and_fusion, sat_until_le_target_or_fusion,
            sat_until_le_safe_and_fusion]
QED

Inductive rewrites_at:
  (!f g. rewrites f g ==> rewrites_at f g) /\
  (!f g. rewrites_at f g ==> rewrites_at (Neg f) (Neg g)) /\
  (!f g h. rewrites_at f g ==> rewrites_at (Conj f h) (Conj g h)) /\
  (!f g h. rewrites_at f g ==> rewrites_at (Conj h f) (Conj h g)) /\
  (!f g h. rewrites_at f g ==> rewrites_at (Disj f h) (Disj g h)) /\
  (!f g h. rewrites_at f g ==> rewrites_at (Disj h f) (Disj h g)) /\
  (!f g h. rewrites_at f g ==> rewrites_at (Impl f h) (Impl g h)) /\
  (!f g h. rewrites_at f g ==> rewrites_at (Impl h f) (Impl h g)) /\
  (!f g. rewrites_at f g ==> rewrites_at (Next f) (Next g)) /\
  (!f g. rewrites_at f g ==> rewrites_at (Fut f) (Fut g)) /\
  (!f g. rewrites_at f g ==> rewrites_at (Glob f) (Glob g)) /\
  (!f g h. rewrites_at f g ==> rewrites_at (Until f h) (Until g h)) /\
  (!f g h. rewrites_at f g ==> rewrites_at (Until h f) (Until h g)) /\
  (!n f g. rewrites_at f g ==> rewrites_at (FutLe n f) (FutLe n g)) /\
  (!n f g. rewrites_at f g ==> rewrites_at (GlobLe n f) (GlobLe n g)) /\
  (!n f g h. rewrites_at f g ==>
             rewrites_at (UntilLe n f h) (UntilLe n g h)) /\
  (!n f g h. rewrites_at f g ==>
             rewrites_at (UntilLe n h f) (UntilLe n h g))
End

Theorem rewrites_at_sound:
  !f g. rewrites_at f g ==> !V i. (sat V i f <=> sat V i g)
Proof
  Induct_on ‘rewrites_at’ >> rw[sat_def] >>
  metis_tac[rewrites_sound]
QED

Theorem chain_sound:
  !f g. RTC rewrites_at f g ==> !V i. (sat V i f <=> sat V i g)
Proof
  ho_match_mp_tac RTC_INDUCT >> rw[] >>
  metis_tac[rewrites_at_sound]
QED

Theorem sat_GF_of_frequently:
  !V P c.
    (!n. P n ==> sat V n c) /\ (!N. ?n. N <= n /\ P n) ==>
    sat V 0 (Glob (Fut c))
Proof
  rw[sat_def] >> metis_tac[]
QED

Theorem sat_conj_pairs:
  !V i f g. sat V i (Conj f g) <=> sat V i f /\ sat V i g
Proof
  rw[sat_def]
QED

val _ = export_theory ();
