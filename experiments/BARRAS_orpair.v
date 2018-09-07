Add LoadPath "/home/user/Downloads/archives/sets-in-coq".
Require Export ZF.
Import IZF.

Definition orpair (a b:set) := pair (pair a a) (pair a b).
Theorem w1 (a1 a2 b1 b2 :set)(e : (orpair a1 b1) == (orpair a2 b2)) : a1 == a2.
Proof.
destruct (@pair_inv _ _ _ _ e) as [[A1 A2] | [B1 B2]]; clear e.
(*destruct A as [A1 A2].*)
+ destruct (@pair_inv _ _ _ _ A1) as [AX | AY].
  firstorder.
  firstorder.
+ destruct (@pair_inv _ _ _ _ B1) as [BX | BY].
  firstorder.
  firstorder.
Defined.

Theorem sy (a1 a2 :set) (e : a2 == a1) : a1 == a2.
symmetry.
trivial.
Show Proof.
Defined.
Print "==".
Search eq_set.
Locate eq_set_equiv.
Search Symmetric.
Check @symmetry.
Locate symmetry.

Theorem w2 (a1 a2 b1 b2 :set)(e : (orpair a1 b1) == (orpair a2 b2)) : b1 == b2.
Proof.
destruct (@pair_inv _ _ _ _ e) as [[A1 A2] | [B1 B2]].
+ destruct (@pair_inv _ _ _ _ A2) as [AX | AY].
  firstorder.
  pose (q:= @w1 _ _ _ _ e).
  destruct AY as [H0 H1].
  rewrite <- H0.
  rewrite -> H1.
  symmetry in q.
  trivial.
+ destruct (@pair_inv _ _ _ _ B1) as [[B1X1 B1X2] | [B1Y1 B1Y2]].
  destruct (@pair_inv _ _ _ _ B2) as [[B2X1 B2X2] | [B2Y1 B2Y2]].
  rewrite <- B1X2.
  rewrite -> B2X2.
  symmetry.
  assumption.
  rewrite <- B1X2.
  rewrite -> B2Y2.
  symmetry.
  assumption.
  destruct (@pair_inv _ _ _ _ B2) as [[B2X1 B2X2] | [B2Y1 B2Y2]].
  rewrite <- B1Y1.
  rewrite -> B2X2.
  symmetry.
  assumption.
  rewrite <- B1Y1.
  rewrite -> B2Y2.
  symmetry.
  assumption.
Defined.


auto.

  rewrite -> H1.

  firstorder.

  destruct B2X as [H0 H1].
  firstorder.
Show Proof.
Defined.


Locate "==".
