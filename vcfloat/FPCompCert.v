(** VCFloat: A Unified Coq Framework for Verifying C Programs with
 Floating-Point Computations. Application to SAR Backprojection.
 
 Version 1.0 (2015-12-04)
 
 Copyright (C) 2015 Reservoir Labs Inc.
 All rights reserved.
 
 This file, which is part of VCFloat, is free software. You can
 redistribute it and/or modify it under the terms of the GNU General
 Public License as published by the Free Software Foundation, either
 version 3 of the License (GNU GPL v3), or (at your option) any later
 version. A verbatim copy of the GNU GPL v3 is included in gpl-3.0.txt.
 
 This file is distributed in the hope that it will be useful, but
 WITHOUT ANY WARRANTY; without even the implied warranty of
 MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See LICENSE for
 more details about the use and redistribution of this file and the
 whole VCFloat library.
 
 This work is sponsored in part by DARPA MTO as part of the Power
 Efficiency Revolution for Embedded Computing Technologies (PERFECT)
 program (issued by DARPA/CMO under Contract No: HR0011-12-C-0123). The
 views and conclusions contained in this work are those of the authors
 and should not be interpreted as representing the official policies,
 either expressly or implied, of the DARPA or the
 U.S. Government. Distribution Statement "A" (Approved for Public
 Release, Distribution Unlimited.)
 
 
 If you are using or modifying VCFloat in your work, please consider
 citing the following paper:
 
 Tahina Ramananandro, Paul Mountcastle, Benoit Meister and Richard
 Lethin.
 A Unified Coq Framework for Verifying C Programs with Floating-Point
 Computations.
 In CPP (5th ACM/SIGPLAN conference on Certified Programs and Proofs)
 2016.
 
 
 VCFloat requires third-party libraries listed in ACKS along with their
 copyright information.
 
 VCFloat depends on third-party libraries listed in ACKS along with
 their copyright and licensing information.
*)
(**
Author: Tahina Ramananandro <ramananandro@reservoir.com>

VCFloat: automatic translation of a CompCert Clight floating-point
expression into a real-number expression with all rounding error terms
and their correctness proofs.
**)

Require Import Lia.
From vcfloat Require Export FPCore. (* FPLang Rounding FPLangOpt.*)
Require compcert.common.AST compcert.common.Values.
Require Import compcert.lib.Floats.
Import Binary BinPos.

Global Instance ident_vartype: VarType AST.ident :=
  {
    var_eqb_eq := Pos.eqb_eq
  }.

Inductive val_inject: Values.val -> forall ty, ftype ty -> Prop :=
| val_inject_single (f: ftype Tsingle):
    val_inject (Values.Vsingle f) Tsingle f
| val_inject_double f:
    val_inject (Values.Vfloat f) Tdouble f
.

Lemma val_inject_single_inv (f1: float32) (f2: ftype Tsingle):
  val_inject (Values.Vsingle f1) Tsingle f2 ->
  f1 = f2.
Proof.
  inversion 1; subst.
  revert H2.
  apply Eqdep_dec.inj_pair2_eq_dec; auto.
  apply type_eq_dec.
Qed.

Lemma val_inject_double_inv f1 f2:
  val_inject (Values.Vfloat f1) Tdouble f2 ->
  f1 = f2.
Proof.
  inversion 1; subst.
  revert H2.
  apply Eqdep_dec.inj_pair2_eq_dec; auto.
  apply type_eq_dec.
Qed.

Definition val_injectb v ty (f: ftype ty): bool :=
  match v with
    | Values.Vsingle f' =>
      type_eqb Tsingle ty && binary_float_eqb f' f
    | Values.Vfloat f' =>
      type_eqb Tdouble ty && binary_float_eqb f' f
    | _ => false
  end.

Lemma val_injectb_inject v ty f:
  val_injectb v ty f = true <-> val_inject v ty f.
Proof.
  unfold val_injectb.
  destruct v;
  (try (split; (try congruence); inversion 1; fail));
  rewrite Bool.andb_true_iff.
  {
    destruct (type_eqb Tdouble ty) eqn:EQ.
    {
      rewrite type_eqb_eq in EQ.
      subst.
      rewrite binary_float_eqb_eq.
      split.
      {
        destruct 1; subst.
        constructor.
      }
      intros; eauto using val_inject_double_inv.
    }
    split; try intuition congruence.
    inversion 1; subst.
    apply type_eqb_eq in H3.
    congruence.
  }
  destruct (type_eqb Tsingle ty) eqn:EQ.
  {
    rewrite type_eqb_eq in EQ.
    subst.
    rewrite binary_float_eqb_eq.
    split.
    {
      destruct 1; subst.
      constructor.
    }
    intros; eauto using val_inject_single_inv.
  }
  split; try intuition congruence.
  inversion 1; subst.
  apply type_eqb_eq in H3.
  congruence.  
Qed.

Lemma conv_nan_ex:
  { conv_nan: forall ty1 ty2,
                binary_float (fprec ty1) (femax ty1) -> (* guaranteed to be a nan, if this is not a nan then any result will do *)
                nan_payload (fprec ty2) (femax ty2)
  |
  conv_nan Tsingle Tdouble = Floats.Float.of_single_nan
  /\
  conv_nan Tdouble Tsingle = Floats.Float.to_single_nan
  }.
Proof.
  eapply exist.
  Unshelve.
  {
    shelve.
  }
  intros ty1 ty2.
  destruct (type_eq_dec ty1 Tsingle).
  {
    subst.
    destruct (type_eq_dec ty2 Tdouble).
    {
      subst.
      exact Floats.Float.of_single_nan.
    }
    auto using any_nan.
  }
  destruct (type_eq_dec ty1 Tdouble).
  {
    subst.
    destruct (type_eq_dec ty2 Tsingle).
    {
      subst.
      exact Floats.Float.to_single_nan.
    }
    intros.
    auto using any_nan.
  }
  intros.
  auto using any_nan.
  Unshelve.
  split; reflexivity.
Defined.

Definition conv_nan := let (c, _) := conv_nan_ex in c.

Lemma single_double_ex (U: _ -> Type):
  (forall ty, U ty) ->
  forall s: U Tsingle,
  forall d: U Tdouble,
    {
      f: forall ty, U ty |
      f Tsingle = s /\
      f Tdouble = d
    }.
Proof.
  intro ref.
  intros.
  esplit.
  Unshelve.
  shelve.
  intro ty.
  destruct (type_eq_dec ty Tsingle).
  {
    subst.
    exact s.
  }
  destruct (type_eq_dec ty Tdouble).
  {
    subst.
    exact d.
  }
  apply ref.
  Unshelve.
  split; reflexivity.
Defined.

Definition single_double (U: _ -> Type)
           (f_: forall ty, U ty)
           (s: U Tsingle)
           (d: U Tdouble)
:
  forall ty, U ty :=
  let (f, _) := single_double_ex U f_ s d in f.

Definition binop_nan :  forall ty, binary_float (fprec ty) (femax ty) ->
       binary_float (fprec ty) (femax ty) ->
       nan_payload (fprec ty) (femax ty) :=
  single_double
    (fun ty =>
       binary_float (fprec ty) (femax ty) ->
       binary_float (fprec ty) (femax ty) ->
       nan_payload (fprec ty) (femax ty)) 
     (fun ty  _ _ => any_nan ty)
     Floats.Float32.binop_nan
     Floats.Float.binop_nan.

Definition abs_nan :=
  single_double
    (fun ty =>
       binary_float (fprec ty) (femax ty) ->
       nan_payload (fprec ty) (femax ty)) 
     (fun ty  _ => any_nan ty)
     Floats.Float32.abs_nan
     Floats.Float.abs_nan.

Definition opp_nan :=
  single_double
    (fun ty =>
       binary_float (fprec ty) (femax ty) ->
       nan_payload (fprec ty) (femax ty)) 
     (fun ty  _ => any_nan ty)
     Floats.Float32.neg_nan
     Floats.Float.neg_nan.

#[export] Instance nans: Nans :=
  {
    conv_nan := conv_nan;
    plus_nan := binop_nan;
    mult_nan := binop_nan;
    div_nan := binop_nan;
    abs_nan := abs_nan;
    opp_nan := opp_nan;
    sqrt_nan := (fun ty _ => any_nan ty)
  }.

Lemma val_inject_eq_rect_r v ty1 e:
  val_inject v ty1 e ->
  forall ty2 (EQ: ty2 = ty1),
    val_inject v ty2 (eq_rect_r _ e EQ).
Proof.
  intros.
  subst.
  assumption.
Qed.
      
Lemma val_inject_single_inv_r v f:
  val_inject v Tsingle f ->
  v = Values.Vsingle f.
Proof.
  inversion 1; subst.
  apply val_inject_single_inv in H.
  congruence.
Qed.

Lemma val_inject_double_inv_r v f:
  val_inject v Tdouble f ->
  v = Values.Vfloat f.
Proof.
  inversion 1; subst.
  apply val_inject_double_inv in H.
  congruence.
Qed.

(** Why do we need this rewrite hint database?
   You might think that all of this could be accomplished with "change"
   instead of "rewrite".  But if you do that, then Qed takes forever. *)
Lemma Float32_add_rewrite: Float32.add = BPLUS Tsingle.  
Proof. reflexivity. Qed.
#[export] Hint Rewrite Float32_add_rewrite : float_elim.
Lemma Float32_sub_rewrite: Float32.sub = BMINUS Tsingle.  
Proof. reflexivity. Qed.
#[export] Hint Rewrite Float32_sub_rewrite : float_elim.
Lemma Float32_mul_rewrite: Float32.mul = BMULT Tsingle.  
Proof. reflexivity. Qed.
#[export] Hint Rewrite Float32_mul_rewrite : float_elim.
Lemma Float32_div_rewrite: Float32.div = BDIV Tsingle.  
Proof. reflexivity. Qed.
#[export] Hint Rewrite Float32_div_rewrite : float_elim.
Lemma Float32_neg_rewrite: Float32.neg = BOPP Tsingle.  
Proof. reflexivity. Qed.
#[export] Hint Rewrite Float32_neg_rewrite : float_elim.
Lemma Float32_abs_rewrite: Float32.abs = BABS Tsingle.  
Proof. reflexivity. Qed.
#[export] Hint Rewrite Float32_abs_rewrite : float_elim.

Lemma Float_add_rewrite: Float.add = BPLUS Tdouble.  
Proof. reflexivity. Qed.
#[export] Hint Rewrite Float_add_rewrite : float_elim.
Lemma Float_sub_rewrite: Float.sub = BMINUS Tdouble.  
Proof. reflexivity. Qed.
#[export] Hint Rewrite Float_sub_rewrite : float_elim.
Lemma Float_mul_rewrite: Float.mul = BMULT Tdouble.  
Proof. reflexivity. Qed.
#[export] Hint Rewrite Float_mul_rewrite : float_elim.
Lemma Float_div_rewrite: Float.div = BDIV Tdouble.  
Proof. reflexivity. Qed.
#[export] Hint Rewrite Float_div_rewrite : float_elim.
Lemma Float_neg_rewrite: Float.neg = BOPP Tdouble.  
Proof. reflexivity. Qed.
#[export] Hint Rewrite Float_neg_rewrite : float_elim.
Lemma Float_abs_rewrite: Float.abs = BABS Tdouble.  
Proof. reflexivity. Qed.
#[export] Hint Rewrite Float_abs_rewrite : float_elim.

Import Float_notations.

Lemma B754_finite_ext:
  forall prec emax s m e p1 p2,
    Binary.B754_finite prec emax s m e p1 = Binary.B754_finite prec emax s m e p2.
Proof.
intros.
f_equal.
apply Classical_Prop.proof_irrelevance.
Qed.

Import Integers.

Ltac canonicalize_float_constant x :=
match x with
| Float32.of_bits (Int.repr ?a) =>
  const_Z a;
  let x' := constr:(Bits.b32_of_bits a) in
  let y := eval compute in x' in
 match y with
   | Binary.B754_finite _ _ ?s ?m ?e _ =>
     let z := constr:(b32_B754_finite s m e (@eq_refl bool true))
      in change x with x'; 
        replace x' with z by (apply B754_finite_ext; reflexivity)
   | Binary.B754_zero _ _ ?s => 
       let z := constr:(b32_B754_zero s) in
       change x with z        
  end
| Float.of_bits (Int64.repr ?a) =>
  const_Z a;
  let x' := constr:(Bits.b64_of_bits a) in
  let y := eval compute in x' in
 match y with
   | Binary.B754_finite _ _ ?s ?m ?e _ =>
     let z := constr:(b64_B754_finite s m e (@eq_refl bool true))
      in change x with x'; 
        replace x' with z by (apply B754_finite_ext; reflexivity)
   | Binary.B754_zero _ _ ?s => 
       let z := constr:(b64_B754_zero s) in
       change x with z        
  end
end.

Ltac canonicalize_float_constants := 
  repeat
    match goal with
    | |- context [Binary.B754_finite 24 128 ?s ?m ?e ?p] =>
         let x := constr:(Binary.B754_finite 24 128 s m e p) in
         let e' := eval compute in e in
         let z := constr:(b32_B754_finite s m e' (@eq_refl bool true)) in
         replace x with z by (apply B754_finite_ext; reflexivity)
    | |- context [Binary.B754_finite 53 1024 ?s ?m ?e ?p] =>
         let x := constr:(Binary.B754_finite 53 1024 s m e p) in
         let e' := eval compute in e in
         let z := constr:(b64_B754_finite s m e' (@eq_refl bool true)) in
         replace x with z by (apply B754_finite_ext; reflexivity)
    | |- context [Float32.of_bits (Int.repr ?a)] =>
     canonicalize_float_constant constr:(Float32.of_bits (Int.repr a))
    | |- context [Float.of_bits (Int64.repr ?a)] =>
     canonicalize_float_constant constr:(Float.of_bits (Int64.repr a))
    end.

