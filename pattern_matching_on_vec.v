Require Import Coq.Vectors.Vector.
Import VectorNotations.
Notation "'vector'" := Vector.t.

Definition openVector_when_S
  (A: Type) (n: nat) : vector A n -> Prop :=
  match n return vector A n -> Prop with
    | O => fun _ => True
    | S n => fun v => exists a, exists v0, v = cons A  a _ v0
  end.

Lemma openVector: 
  forall A n (v: vector A (S n)), exists a, exists v0, v = cons A a _ v0.
Proof.
intros A n v. change (openVector_when_S _ _ v). case v; clear v n.
  simpl. exact I. 
  intros a n v. simpl. exists a; exists v; reflexivity.
Qed.


Definition is_nil_when_0 (A: Type) (n: nat) : vector A n -> Prop :=
  match n return vector A n -> Prop with
    | O => fun v => v = nil _
    | S n => fun _ => True
  end.

Lemma is_nil: forall A (v: vector A 0), v = nil _.
Proof.
intros A v. change (is_nil_when_0 _ _ v). case v; clear v; simpl.
  reflexivity. 
  intros n a v; exact I.
Qed.