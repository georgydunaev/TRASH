(*Check dec_nat.*)
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Import ListNotations.


Require Import List.
Import ListNotations.

Section nod.
Context {A:Type}.
Context (decA: forall x y : A, {x = y} + {x <> y}).

Fixpoint nodup (l : list A) : list A :=
  match l with
    | [] => []
    | x::xs => if in_dec decA x xs then nodup xs else x::(nodup xs)
  end.
End nod.

Check Bool.bool_dec.
Definition count_uniques (l : list nat) : nat :=
  length (nodup eq_nat_dec l).

Eval compute in count_uniques [1; 2; 2; 4; 1].

Fixpoint A2 l :fold_left orb l true = true.
Proof.
destruct l; simpl.
reflexivity.
apply A2.
Defined.

Theorem A1 (x y:bool): (orb x y = false)->(x=false)/\(y=false).
Proof. intro H. destruct x, y; firstorder || inversion H. Defined.

Fixpoint A0 b l : fold_left orb (b :: l) false = orb b (fold_left orb l false) .
Proof.
destruct l.
simpl. firstorder.
simpl.
destruct b.
simpl.
apply A2.
simpl.
reflexivity.
Defined.

Fixpoint all_then_some (l:list bool) {struct l}:
(List.fold_left orb l false) = false ->
(forall (p:nat), (List.nth p l false) = false).
Proof.
intros.
destruct l. simpl. destruct p; trivial.
simpl.
rewrite A0 in H.
pose (Q:=A1 _ _ H).
destruct Q.
destruct p. trivial.
apply all_then_some.
trivial.
Defined.
(*
compute.

destruct b0;simpl.
simpl.
unfold fold_left.
destruct b.

Admitted.

assert (A0 :
unfold fold_left in H.
2 : {