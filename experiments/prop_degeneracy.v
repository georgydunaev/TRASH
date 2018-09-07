Axiom em : forall P : Prop, (P) \/ (~P).
Axiom proof_irrelevance : forall (P : Prop) (q p : P), p = q.
Theorem iff_eq : forall P Q : Prop, (P -> Q) -> (Q -> P) -> P = Q.
intros.
destruct (em P).

(* See classicalfacts.v *)

auto.
red.
elimtype P.
elim H.