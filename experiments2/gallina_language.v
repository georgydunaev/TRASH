
Section exper1.
Check (0 <: nat).

Context (a:nat).
Check (a :> ).

Fail Definition g y := fun x:nat => (y <: nat).
Definition g:=(0 <: nat).
Print g.
Compute g.
End exper1.
Print Grammar constr.
Print Grammar operconstr.
Module ModParam.
Parameter (A:Prop).
End ModParam.

Section exper2.
Hypothesis (A:Prop).
(* Set is predicative sort.  CIC *)
(* BUT IT MAY BE AN IMPREDICATIVE! (with special parameter) *)
(*Hypothesis (A:Prop).*)
Check 0.
Local Definition SDF : Prop := (A->A).
Reserved Notation "( a '???' b )" .
Notation "( a '???' b )" := (a=b)  (at level 0, no associativity) : my_scope.
Delimit Scope my_scope with my_dlmtr.
Check ( 0 ??? 1 ) %my_dlmtr.
Undelimit Scope my_scope.

Open Scope my_scope.
Print Visibility.
Theorem Q (a:SDF):Type.
Proof.
unfold SDF in a.
Abort.
Locate sumbool.
Close Scope my_scope.
Local Open Scope my_scope.
Local Close Scope my_scope.
Global Open Scope my_scope.
Global Close Scope my_scope.

Parameter U:Set.
Notation "(- a -)" := (a)  (at level 0, no associativity, only parsing) : my_scope2.

Bind Scope my_scope2 with U.
Definition def2 (a b:U) : U := (- a -).
End exper2.
Fail Check A.
Section TreeForest.
Local Axiom (A B:Set).
Theorem lll (a:A): True.
assert (a' := a).
Abort.
Inductive tree : Set := node : A -> forest -> tree
with forest : Set :=
    leaf : B -> forest
  | cons : tree -> forest -> forest.
End TreeForest.
Fail Fail Fail Fail Check A.
(** Todo: **)
Fixpoint thm (A:nat):bool.
exact (thm A).
Fail Qed.
Abort.

Let SDF2 : Prop := (A->A).

Context (A:Prop).
Context (B:Set).
Definition Def1 

Check (Prop).
(* Prop : Type@{Set+1} *)
Check (Set).
(* Set : Type@{Set+1} *)
Check "Top".

(* Set : Type@{Top.5} *)

(* {Top.5} |= Set < Top.5  *)

Check (Prop:>Type@{Set+1}).


Check LEFTA.