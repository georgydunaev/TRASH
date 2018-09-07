(* -nois for clean state *)
Inductive nat :=
| O : nat
| S : forall _ : nat, nat
.
Print Libraries.
Fail Check 2. (* No interpretation for numeral 2. *)

Goal 2+(1+1)=4.
auto.


Require Import ZArith.
Require Ring.

Local Open Scope Z_scope.

Lemma toto1 : 1 + 1 = 2.
ring.
Defined.

Lemma toto2 : 2 + 2 = 4.
ring.
Qed.

Lemma toto3 : 2 + 1 = 3.
ring.
Qed.

Hint Resolve  toto2 toto3 : mybase.
Goal 2+(1+1)=4.
auto with mybase.
Show Proof.
No more subgoals.

Unnamed_thm < Qed.
Unnamed_thm is defined