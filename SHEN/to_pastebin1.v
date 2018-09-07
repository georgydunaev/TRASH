Require Import Coq.Lists.List.
Import ListNotations.

Definition SetVars  := nat.

Definition FuncSymb := nat.

Record FSV := {
 fs : FuncSymb;
 fsv : nat;
}.

Inductive preTerms := 
|Vari : SetVars -> preTerms
|Node : FSV -> list preTerms -> preTerms.

Fixpoint isNTerm (n:nat) (x : preTerms) {struct n}: Prop
:=match n with
  | 0 => True
  | S n => 
   match x with 
   | Vari v => True
   | Node f lp => (and ((length lp)=(fsv f)) (Forall (isNTerm n) lp))
   end
  end.

Notation isTerm := (fun x =>  (forall (n:nat), isNTerm n x)).
Record Terms := {
 Terms_x : preTerms;
 Terms_H : isTerm Terms_x;
}.

(* Good *)
Theorem VariIsTerm s y: isNTerm y (Vari s).
Proof.
destruct y.
exact I.
simpl in * |- *.
exact I.
Show Proof.
Defined.

Fixpoint ArgIsTerm (f:FSV) (ls:_) A:
(isTerm (Node f ls)) -> (In A ls) -> (isTerm A).
Proof.
intros H H0.
destruct A. 
- apply VariIsTerm. 
- intro n.
  pose (Q:= H (S n)).
  destruct H.
pose (GQ := Forall_forall (isNTerm n) ls).
destruct GQ.
apply H1.
assumption.
assumption.
Defined.

(* This function doesn't work properly. *)
Definition prototype (te:Terms) : list Terms.
Proof.
destruct (Terms_x te) eqn:a1.
exact [].
destruct l eqn:a2.
exact [].
refine [_].                              (** Here must be refine (_ :: _) ! **)
unshelve simple eapply Build_Terms.
exact p.
eapply (ArgIsTerm f (p::l0) p).
rewrite <- a1.
exact (Terms_H te).
constructor.
reflexivity.
Defined.