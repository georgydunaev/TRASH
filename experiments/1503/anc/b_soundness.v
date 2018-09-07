(**)

Require Export Utf8_core.
Add LoadPath "/home/user/0data/diploma/experiments/1503/anc".
Require Export Bool.
Require Export a_base.
Export ListNotations.
Set Implicit Arguments.

Module Type sound_mod (X: base_mod).
Import X.


(** * Definitions 

definition of Propositional Formulas*)
Inductive PropF : Set :=
 | Var : PropVars -> PropF
 | Bot : PropF
 | Conj : PropF -> PropF -> PropF
 | Disj : PropF -> PropF -> PropF
 | Impl : PropF -> PropF -> PropF
.

Notation "# P" := (Var P) (at level 1) : My_scope.
Notation "A \u2228 B" := (Disj A B) (at level 15, right associativity) : My_scope.
Notation "A \u2227 B" := (Conj A B) (at level 15, right associativity) : My_scope.
Notation "A \u2192 B" := (Impl A B) (at level 16, right associativity) : My_scope.
Notation "\u22a5" := Bot (at level 0)  : My_scope.
Definition Neg A := A \u2192 \u22a5.
Notation "\u00ac A" := (Neg A) (at level 5) : My_scope.
Definition Top := \u00ac\u22a5.
Notation "\u22a4" := Top (at level 0) : My_scope.
Definition BiImpl A B := (A\u2192B)\u2227(B\u2192A).
Notation "A \u2194 B" := (BiImpl A B) (at level 17, right associativity) : My_scope.

(** Validness *)

(** Valuations are maps PropVars -> bool sending \u22a5 to false*)
Fixpoint TrueQ v A : bool := match A with
 | # P   => v P
 | \u22a5     => false
 | B \u2228 C => (TrueQ v B) || (TrueQ v C)
 | B \u2227 C => (TrueQ v B) && (TrueQ v C)
 | B \u2192 C => (negb (TrueQ v B)) || (TrueQ v C)
end.
(*G= G*)
Definition Satisfies v G := forall A, In A G -> Is_true (TrueQ v A).
Definition Models G A := forall v,Satisfies v G->Is_true (TrueQ v A).
Notation "G \u22a8 A" := (Models G A) (at level 80).
Definition Valid A := [] \u22a8 A.

(** Provability *)

Reserved Notation "G \u22a2 A" (at level 80).
Inductive Nc : list PropF-> PropF->Prop :=
| Nax   : forall G A  ,    In A G                           -> G \u22a2 A
| ImpI  : forall G A B,  A::G \u22a2 B                           -> G \u22a2 A \u2192 B
| ImpE  : forall G A B,     G \u22a2 A \u2192 B -> G \u22a2 A              -> G \u22a2 B
| BotC  : forall G A  , \u00acA::G \u22a2 \u22a5                              -> G \u22a2 A
| AndI  : forall G A B,     G \u22a2 A     -> G \u22a2 B              -> G \u22a2 A\u2227B
| AndE1 : forall G A B,     G \u22a2 A\u2227B                        -> G \u22a2 A
| AndE2 : forall G A B,     G \u22a2 A\u2227B                        -> G \u22a2 B
| OrI1  : forall G A B,     G \u22a2 A                           -> G \u22a2 A\u2228B
| OrI2  : forall G A B,     G \u22a2 B                           -> G \u22a2 A\u2228B
| OrE   : forall G A B C,   G \u22a2 A\u2228B -> A::G \u22a2 C -> B::G \u22a2 C -> G \u22a2 C
where "G \u22a2 A" := (Nc G A) : My_scope.

Definition Provable A := [] \u22a2 A.

(**The Theorems we are going to prove*)
Definition Prop_Soundness := forall A,Provable A->Valid A.
Definition Prop_Completeness := forall A,Valid A->Provable A.

(** * Theorems *)

Ltac mp := eapply ImpE.
Ltac AddnilL := match goal with 
| |- _ ?G _ => change G with ([]++G)
end.
Ltac in_solve := intros;repeat 
 (eassumption
||match goal with 
   | H:In _ (_::_) |- _ => destruct H;[subst;try discriminate|]
   | H:In _ (_++_) |- _ => apply in_app_iff in H as [];subst
   | |- In _ (_++_) => apply in_app_iff;(left;in_solve;fail)||(right;in_solve;fail) 
  end
||(constructor;reflexivity)
||constructor 2).
Ltac is_ass := econstructor;in_solve.

Ltac case_bool v A := let HA := fresh "H" in
(case_eq (TrueQ v A);intro HA;try rewrite HA in *;simpl in *;try trivial;try contradiction).

Local Ltac prove_satisfaction :=
intros ? K;destruct K;[subst;simpl;
match goal with
| [ H : TrueQ _ _ = _  |-  _ ] => rewrite H
end;exact I|auto].

Open Scope My_scope.

(*Check My_scope.Varseq_dec.
Check M.Varseq_dec.
Check base_mod.Varseq_dec.
Import base_mod.*)


Lemma PropFeq_dec : forall (x y : PropF), {x = y}+{x <> y}.
induction x;destruct y;try (right;discriminate);
 try (destruct (IHx1 y1);[destruct (IHx2 y2);[left;f_equal;assumption|]|];
  right;injection;intros;contradiction).
 destruct (Varseq_dec p p0).
   left;f_equal;assumption.
   right;injection;intro;contradiction.
 left;reflexivity.
Qed.

Lemma Excluded_Middle : forall G A, G \u22a2 A\u2228\u00acA.
intros;apply BotC;mp;[is_ass|apply OrI2;apply ImpI;mp;[is_ass|apply OrI1;is_ass]].
Qed.

Lemma weakening2 : forall G A, G \u22a2 A -> forall D, (forall B, In B G -> In B D) -> D \u22a2 A.
induction 1;[constructor|constructor 2|econstructor 3|constructor 4|constructor 5|econstructor 6
|econstructor 7|constructor 8|constructor 9|econstructor 10];try eauto;
[apply IHNc..|apply IHNc2|try apply IHNc3];intros;in_solve;eauto.
Qed.

Lemma weakening : forall G D A, G \u22a2 A -> G++D \u22a2 A.
intros;eapply weakening2;[eassumption|in_solve].
Qed.

Lemma deduction : forall G A B, G \u22a2 A \u2192 B -> A::G \u22a2 B.
intros;eapply ImpE with A;[eapply weakening2;[eassumption|in_solve]|is_ass].
Qed.

Lemma prov_impl : forall A B, Provable (A \u2192 B)->forall G, G \u22a2 A -> G \u22a2 B.
intros. mp. 
  AddnilL;apply weakening. apply H.
  assumption. 
Qed.

(* This tactic applies prov_impl in IH (apply prov_impl in IH doesn't work, because I want to keep the G quantified)*)
Ltac prov_impl_in IH := let H := fresh "K" in
try (remember (prov_impl IH) as H eqn:HeqH;clear IH HeqH).

(** Soundness *)

Theorem Soundness_general : forall A G, G \u22a2 A -> G \u22a8 A.
intros A G H0 v;induction H0;simpl;intros;auto;
 try simpl in IHNc;try simpl in IHNc1;try simpl in IHNc2;
  case_bool v A;try (case_bool v B;fail);
   try (apply IHNc||apply IHNc2;prove_satisfaction);
    case_bool v B;apply IHNc3;prove_satisfaction.
Qed.

Theorem Soundness : Prop_Soundness.
intros ? ? ? ?;eapply Soundness_general;eassumption.
Qed.

End sound_mod.
