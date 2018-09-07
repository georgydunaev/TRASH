(* PUBLIC DOMAIN *)
Require Export Coq.Vectors.Vector.
Require Export Coq.Lists.List.
Require Import Bool.Bool.
Require Import Logic.FunctionalExtensionality.
Require Import Coq.Program.Wf.
Require Import Lia.
Add LoadPath "/home/user/0data/COQ/SHEN/".
Require Export ListForallT.

Definition SetVars  := nat.
Definition FuncSymb := nat.
Definition PredSymb := nat.
Record FSV := {
 fs : FuncSymb;
 fsv : nat;
}.
Record PSV := MPSV{
 ps : PredSymb;
 psv : nat;
}.

Section All.
  Variable T : Type.
  Variable P : T -> Prop.

  Fixpoint All (ls : list T) : Prop :=
    match ls with
      | nil => True
      | cons h t => P h /\ All t
    end.
End All.

Unset Elimination Schemes.
Inductive preTerms : Type :=
| FVC :> SetVars -> preTerms
| FSC (f:FSV) : list preTerms -> preTerms.
Set Elimination Schemes.

Section preTerms_ind'.
  Variable P : preTerms -> Prop.
  

Section preTerms_ind'.
  Variable P : preTerms -> Prop.
  Variable Q : FSV -> list preTerms -> Prop.
  Hypothesis preTerms_case1 : forall (sv : SetVars), P (FVC sv).

  Hypothesis preTerms_case2 : forall (f : FSV) (ls : list preTerms),
    ((Q f ls)/\(All preTerms P ls)) -> P (FSC f ls).

  Fixpoint preTerms_ind (tr : preTerms) : P tr.
  Proof.
  destruct tr.
  exact (preTerms_case1 _).
  apply preTerms_case2.
  revert l; fix G 1; intro l.
  split.

  destruct l;simpl;trivial.
  split.
  apply preTerms_ind.
  apply G.
  Defined.
End preTerms_ind'.
