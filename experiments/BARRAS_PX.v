Add LoadPath "/home/user/Downloads/archives/sets-in-coq".
Require Export ZF.
Import IZF.

(*Theorem thm: not (exists x:set, ((power x) == x) ).*)
Theorem thm: not (exists x:set, ((power x) \incl x) ).
Proof.
intro H.
destruct H as [x A].
unfold "\incl" in A.
assert (H1 : not(x\in x)).
+ intro w.
  assert (G : x \in (singl x) ).
  * apply singl_intro.
  * destruct (regularity_ax _ _ G) as [z J C].
    apply C.
    exists x.
    trivial.
    rewrite -> (singl_elim _ _ J).
    trivial.
+ apply H1.
  apply (A x).
  apply power_intro.
  trivial.
Defined.

(* END OF PROOFS *)
(*
(*
Check (@eq_elim).
Check symmetry H.
Check (@eq_elim _ _ _ H).
pose (A := fun r => @eq_elim r _ _ H).
(*pose (B := fun r => @eq_elim r _ _ (symmetry H)).*)*)


Check regularity_ax (singl x) x.

destruct (regularity_ax x (x) w) as [z J C].
apply C.
exists x.
trivial.

pose (M1:=B x w).
pose (M2:=B z J).
rewrite <- H in M1.

%change x with (power x) in M1.
pose (M1:=B x w).

pose (eq_intro)


Theorem thm: not (exists x:set, ((power x) \incl x) ).
Proof.
intro H.
destruct H.
Print power.
unfold "\incl" in H.
assert (H1 : not(x\in x)).
Focus 2.
+ apply H1.
  apply (H x).
  apply power_intro.
  trivial.
+ intro w.
  pose(u:= minus2 x (singl x)).
  (*pose(u:= subset x (fun y => y \in singl x)).*)
  destruct (regularity_ax x x w).

  (*destruct (regularity_ax x x w).*)
  apply H1.
  exists u.
  admit.

  trivial.
  trivial.
  constructor.

Check (H x).
*)