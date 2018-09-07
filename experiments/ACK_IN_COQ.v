Require Export Setoid.

(* Skolemized version of IZF *)

Module Type IZF_sig.

Check (bool*Prop)%type.



Parameter
 (class : Type)
 (M : class -> Prop) (* is_set *)
 (eq_class : class -> class -> Prop)
 (in_class : class -> class -> Prop).
 Notation "x \in y" := (in_class x y) (at level 60).
 Notation "x == y" := (eq_class x y) (at level 70).



Inductive L1 :=
.

(*
Context (M:Prop).
Check False->False.
Check M->False.
*)

Inductive frm:Prop :=
|atom:Prop->frm
|cand:frm->frm->frm.

Definition tra (f:frm) :=
match f with
| atom

Parameter
 (eq_class_ax : forall a b, a == b <-> (forall x, x \in a <-> x \in b)).
Parameter
 (cc_ax : forall (F: class -> frm), 
(forall y, F y -> M y)
-> (exists x, forall y, y \in x <-> F y)).
