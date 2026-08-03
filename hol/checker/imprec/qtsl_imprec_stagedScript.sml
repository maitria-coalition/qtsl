(*
  Staged goals for the imprecise-certificate soundness core: each
  goal is a boolean Definition, so the build type-checks the exact
  statement against the distribution's measure/martingale vocabulary
  without introducing axioms. Deliberately a separate theory: the core
  depends only on realTheory/real_sigmaTheory, while this file opens
  the larger src/probability surface.
*)
open HolKernel Parse boolLib bossLib;
open arithmeticTheory pred_setTheory listTheory;
open realTheory realLib real_sigmaTheory;
open extrealTheory sigma_algebraTheory measureTheory martingaleTheory;
open qtsl_imprecTheory;

val _ = new_theory "qtsl_imprec_staged";

Definition ville_goal_def:
  ville_goal (t : 'a itself) <=>
  !m a (u : num -> 'a -> extreal) (r : real).
    super_martingale m a u /\
    (!n x. x IN m_space m ==> 0 <= u n x) /\
    0 < r ==>
    measure m {x | x IN m_space m /\ ?n. Normal r <= u n x}
      <= integral m (u 0) / Normal r
End

Definition path_weight_def:
  (path_weight sg (h:'st list) [] = (1:real)) /\
  (path_weight sg h [x] = 1) /\
  (path_weight sg h (x::y::p) = sg (x::h) x y * path_weight sg (x::h) (y::p))
End

Definition paths_def:
  paths n (x0:'st) = {p | LENGTH p = SUC n /\ HD p = x0}
End

Definition hits_def:
  hits bad = {p : 'st list | EXISTS (\x. x IN bad) p}
End

Definition path_bridge_goal_def:
  path_bridge_goal (t : 'st itself) <=>
  !(cs : ('st -> 'st -> real) set) sg bad n (x0:'st).
    FINITE (UNIV:'st set) /\
    (!k. k IN cs ==> subkernel k /\ (!x. SIGMA (k x) UNIV = 1)) /\
    scheduler cs sg ==>
    ?m. measure_space m /\
        m_space m = paths n x0 /\
        measurable_sets m = POW (paths n x0) /\
        (!p. p IN paths n x0 ==>
             measure m {p} = Normal (path_weight sg [] p)) /\
        measure m (hits bad INTER paths n x0)
          = Normal (hitP sg bad n [] x0)
End

val _ = export_theory ();
