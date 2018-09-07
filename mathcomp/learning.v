Add LoadPath "/home/user/Downloads/archives/math-comp-mathcomp-1.7.0/".
(*Add mathcomp "/home/user/Downloads/archives/math-comp-mathcomp-1.7.0/mathcomp".*)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq.
From mathcomp Require Import ssrnat.

Lemma is_true_locked_true : locked true. 
Proof. 
Print locked.
Print master_key.
by unlock. 
Show Proof.
Compute ((fun evar_0_ : (fun u : unit => is_true ((let 'tt := u in id) true)) tt =>
  match
    master_key as u
    return ((fun u0 : unit => is_true ((let 'tt := u0 in id) true)) u)
  with
  | tt => evar_0_
  end) is_true_true).
Qed.

Print erefl.
Print Logic.eq_refl.
(*Set Implicit Arguments.*)
Section Hilb.
Variables A B C:Prop.
Lemma HilbS : (A->B->C)->(A->B)->A->C.
Proof.
move=> aibic.
move=> aib a.
move: aibic.
Show Proof.
apply.
Show Proof.
 by [].
Show Proof.
by apply: aib.
Show Proof.
Defined.
Eval compute in (fun (aibic : A -> B -> C) (aib : A -> B) (a : A) =>
 (fun top_assumption_ : A -> B -> C =>
  (fun evar_0_ : A => [eta top_assumption_ evar_0_]) a (aib a)) aibic).


End Hilb.