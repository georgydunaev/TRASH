Definition pred' (x : nat) :=
  match x with
    | O => O
    | S n' => let y := n' in y
  end.

Theorem reduce_me : pred' 1 = 0.
Proof.
cbv delta. (* lazy delta. *)
cbv beta.
cbv iota.
cbv beta.
cbv zeta.
reflexivity.
Qed.

Definition id (n : nat) := n.

Eval compute in fun x => id x.

Fixpoint id' (n : nat) := n.

Eval compute in fun x => id' x.