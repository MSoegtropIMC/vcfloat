(** * Define Elpi based tactics which do restricted computations *)

Require Import elpi.elpi.

(** ** Elpi database with common definitions for restricted computation functions *)

Elpi Db restricted_computation.db lp:{{

  %%% CBV under applications of term F (usually a definition or constructor) using reduction flags RF
  %%% cbv-under-application-of function reduction-flags input-term output-term
  
  pred cbv-under-application-of i:term, i:coq.redflags, i:term, o:term.
    % forall X : T, B -> recurse
    cbv-under-application-of F RF (prod X T BI) (prod X T BO) :- pi x\ decl x X T => cbv-under-application-of F RF (BI x) (BO x).
    % let X : T := C in B -> recurse 
    cbv-under-application-of F RF (let X T V BI) (let X T V BO) :- pi x\ decl x X T => cbv-under-application-of F RF (BI x) (BO x).
    % application of F -> computate
    % Note: there is also a "coq.reduction.vm.norm" and "coq.reduction.native.norm"
    cbv-under-application-of F RF ((app [ F | _ ]) as TI) TO :- !, @redflags! RF => coq.reduction.cbv.norm TI TO.
    % application of any other function -> recurse
    cbv-under-application-of F RF (app LI) (app LO) :- std.map LI (cbv-under-application-of F RF) LO.
    % Everything else -> just copy
    % ATTENTION: cbv-under-application-of DOES NOT look into matches are function bodies, just forall, let and applications - this is easy to extend.
    cbv-under-application-of _ _ T T.

}}.

(** ** Elpi tactics *)

(** Tactic for cbv reduction of the goal, but only under applications of head term "F" - typical a definition or constructor
    Usage: cbv_uao <head symbol>
*)
(* Start a new tactic named "full_compute_under_application_of" *)
Elpi Tactic full_compute_under_application_of.
(* Include the common database defined above *)
Elpi Accumulate Db restricted_computation.db.
(* Add the tactic main predicate "solve" *)
Elpi Accumulate lp:{{
  solve (goal _ _ GoalType _ [trm HeadTerm] as Goal) GoalReduced :-
    cbv-under-application-of HeadTerm coq.redflags.all GoalType GoalTypeReduced,
    refine {{ _ : lp:{{GoalTypeReduced}} }} Goal GoalReduced
    % Note: I am not sure if this leaves a vm_cast - watch our for Qed time issues
  .
}}.
(* Check if all predicates have the correct types.
   Note: VSCode warnings are not written to a window but shown when hovering over the command. *)
Elpi Typecheck.

(** ** Examples *)

Require Import ZArith.
Goal ((3*4)+(5*6*7) = 222)%Z.
elpi full_compute_under_application_of (Z.mul).
(* ATTENTION: the () around Z.mul are important - otherwise elpi parses the argument as string! *)
Abort.
