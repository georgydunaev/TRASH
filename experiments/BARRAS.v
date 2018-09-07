Add LoadPath "/home/user/Downloads/archives/sets-in-coq".
Require Export ZFdef.
Require Export ZF.
(*
Module M.
End M.

Module qq:IZF_sig := M.*)

(*Module Skolem (Z : IZF_Ex_sig) <: IZF_sig. *)

Require Ens ZFskol.
Module IZF : IZF_sig := ZFskol.Skolem Ens.IZF.
Import IZF.


Check set.
Check pair.
Definition orpair (a b:set) := pair (pair a a) (pair a b).
Locate "==".
Theorem w (a1 a2 b1 b2 :set)(e : (orpair a1 b1) == (orpair a2 b2)) : a1 == a2.
Locate "/\".
Print and.
Check (eq_set_ax a1 a2).
unfold orpair in e.
intros.

(*elim (pair_ax a1 a1 a1); auto.*)
(* refine (@pair_ext _ _ _ _ _ _).
apply pair_ext _ _ _). *)

destruct (eq_set_ax a1 a2) as [y u].
apply u.
clear y u.

intro w.

destruct (eq_set_ax (orpair a1 b1) (orpair a2 b2)) as [J0 J1].
pose (e1:=J0 e).
clear J1.

Theorem w (a1 a2 b1 b2 :set)(e : (orpair a1 b1) == (orpair a2 b2)) : a1 == a2.
unfold orpair in e.
compute in e.
Locate "==".
Check (@pair_inv _ _ _ _).

unfold "==" % IZF in e.

Check (@pair_inv _ _ _ _ e).




destruct (eq_set_ax a1 a2) as [y u].
intros.

pose (ggg:=(eq_set_ax (orpair a1 b1) (orpair a2 b2))).
destruct ggg as [J0 J1].
pose (i:=J0 e).
split.
intro.

apply
destruct (eq_set_ax (orpair a1 b1) (orpair a2 b2)).
split.

destruct (eq_set_ax a1 a2) as [y u].

set (q:= @eq_set_ax _ _ y e).
unfold "==".
red.

Print repl.
Check (repl).

Import ZFdef.IZF_sig.

Open Scope IZF_sig.
Check eq_set.
Check IZF_sig.eq_set.
Check pair.


Require Export CatsInZFC.tactics.

"exists2"