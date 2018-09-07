 Require Import ZArith.
  Open Scope Z_scope.

  Inductive even: Z -> Prop :=
    | even_base: even 0
    | even_succ: forall n, odd (n - 1) -> even n

  with odd: Z -> Prop :=
    | odd_succ: forall n, even (n - 1) -> odd n.

(*(Yes, it's a silly example, but it fits in this e-mail.)
Just after defining the predicates, ask "Scheme" to generate its
induction principles:*)

Scheme even_ind_2 := Minimality for even Sort Prop
  with odd_ind_2  := Minimality for odd Sort Prop.

Check even_ind_2.
Check even_ind.
(*
even_ind_2
     : forall (P P0 : forall _ : Z, Prop) (_ : P Z0)
         (_ : forall (n : Z) (_ : odd (Z.sub n (Zpos xH)))
                (_ : P0 (Z.sub n (Zpos xH))), P n)
         (_ : forall (n : Z) (_ : even (Z.sub n (Zpos xH)))
                (_ : P (Z.sub n (Zpos xH))), P0 n) (z : Z) 
         (_ : even z), P z

even_ind
     : forall (P : forall _ : Z, Prop) (_ : P Z0)
         (_ : forall (n : Z) (_ : odd (Z.sub n (Zpos xH))), P n) 
         (z : Z) (_ : even z), P z
*)

Lemma even_pos:
  forall (n:Z), even n -> n >= 0.
Proof.
  apply (even_ind_2 (fun n => n >= 0) (fun n => n >= 1)).
  omega.
  intros. omega.
  intros. omega.
Qed.