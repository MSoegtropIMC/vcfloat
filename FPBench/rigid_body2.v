Require Import vcfloat.VCFloat.
Require Import Interval.Tactic.
Import Binary List ListNotations.
Set Bullet Behavior "Strict Subproofs".
Section WITHNANS.
Context {NANS:Nans}.
Open Scope R_scope.

<<<<<<< HEAD:FPBench/rigid_body.v
Definition rigidbody1_bmap_list := [Build_varinfo Tdouble 1%positive (-15) (15);Build_varinfo Tdouble 2%positive (-15) (15);Build_varinfo Tdouble 3%positive (-15) (15)].

Definition rigidbody1_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list rigidbody1_bmap_list) in exact z).

Definition rigidbody1 (x1 : ftype Tdouble) (x2 : ftype Tdouble) (x3 : ftype Tdouble) := 
  cast Tdouble (((((-(x1 * x2)%F64) - (((2)%F64 * x2)%F64 * x3)%F64)%F64 - x1)%F64 - x3)%F64).

Definition rigidbody1_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive;3%positive]) rigidbody1 in exact e').


Derive rigidbody1_b 
SuchThat (forall vmap, prove_roundoff_bound rigidbody1_bmap vmap rigidbody1_expr rigidbody1_b)
As rigidbody1_bound.
Proof.
idtac "Starting rigidbody1".
time "rigidbody1" (
try (subst rigidbody1_b; intro; prove_roundoff_bound);
try (prove_rndval; interval);
try (prove_roundoff_bound2; prune_terms (cutoff 30); do_interval)).
Qed.

Lemma check_rigidbody1_bound: ltac:(CheckBound rigidbody1_b 3.1e-13%F64).
Proof. reflexivity. Qed.

=======
>>>>>>> b35234fce9cbf03ede4c0bfc4b61d33d055eb550:FPBench/rigid_body2.v
Definition rigidbody2_bmap_list := [Build_varinfo Tdouble 1%positive (-15) (15);Build_varinfo Tdouble 2%positive (-15) (15);Build_varinfo Tdouble 3%positive (-15) (15)].

Definition rigidbody2_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list rigidbody2_bmap_list) in exact z).

Definition rigidbody2 (x1 : ftype Tdouble) (x2 : ftype Tdouble) (x3 : ftype Tdouble) := 
  cast Tdouble (((((((((2)%F64 * x1)%F64 * x2)%F64 * x3)%F64 + (((3)%F64 * x3)%F64 * x3)%F64)%F64 - (((x2 * x1)%F64 * x2)%F64 * x3)%F64)%F64 + (((3)%F64 * x3)%F64 * x3)%F64)%F64 - x2)%F64).

Definition rigidbody2_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive;3%positive]) rigidbody2 in exact e').

Derive rigidbody2_b 
SuchThat (forall vmap, prove_roundoff_bound rigidbody2_bmap vmap rigidbody2_expr rigidbody2_b)
As rigidbody2_bound.
Proof.
idtac "Starting rigidbody2".
time "rigidbody2" (
try (subst rigidbody2_b; intro; prove_roundoff_bound);
try (prove_rndval; interval);
try (prove_roundoff_bound2; prune_terms (cutoff 30); do_interval)).
Qed.

Lemma check_rigidbody2_bound: ltac:(CheckBound rigidbody2_b 3.9e-11%F64).
Proof. reflexivity. Qed.

End WITHNANS.
Close Scope R_scope.