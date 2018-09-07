(* http://gallium.inria.fr/~scherer/gagallium/coq-eval/index.html *)

Definition nat_eq (x y: nat) : {x=y} + {x<>y}.
Proof.
decide equality.
Qed.
Compute (nat_eq 2 2).

Definition nat_eq2 (x y: nat) : {x=y} + {x<>y}.
Proof.
decide equality.
Defined.
Compute (nat_eq2 2 2).

(*vm_compute
native_compute *)

Require Import Coq.Program.Tactics.
Require Import Coq.ZArith.ZArith.
(*Require Export Coq.ZArith.Zcompare.
Require Export Coq.ZArith.Znat.*)

Require Import Coq.QArith.QArith.
Definition a := Z.of_nat 2 # Pos.of_nat 3.
Check Z.le.

Open Scope Z_scope. (* good *)
Definition t := { n : Z | n > 1 }.

Program Definition two : t := 2.
Next Obligation.
omega.
Show Proof.
Qed.

Program Definition succ (n: t) : t := n + 1.
Next Obligation. destruct n; simpl; omega. Qed.

(*!*)
Goal (1 # 1 <> 2 # 2).
congruence.
Show Proof.
Qed.

