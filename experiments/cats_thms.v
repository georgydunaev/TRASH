Add LoadPath "/home/user/Downloads/archives/cats-in-zfc-2945072aa6c9c328a019d3128c0a725dabca434c".
Require Export CatsInZFC.tactics.

Theorem w1 (x : E):nonempty x -> exists y : E, inc y x.
Proof.
intros.
elim H.
intros.
exists y.
trivial.
Defined.

Definition w2 (x : E): (exists y : E, inc y x) -> nonempty x.
Proof.
intros H.
elim H.
Print nonempty.
intro y.
constructor 1 with (y:=y).
assumption.
Defined.

Definition w3 (x : E):nonempty x <-> exists y : E, inc y x.
Proof.
split.
exact (w1 x).
exact (w2 x).
Defined.

Definition v0 (a b:E): (forall x:E, (inc x a) <-> (inc x b)) <-> (a=b).
Proof.
split.
* intros.
  apply extensionality.
   all: (*par: *)
   intro x;
   elim (H x);
   intros H0 H1;
   assumption.
* intros.
  replace a with b.
  firstorder.
Defined.
(* CTRL+SHFT+L    "<->"  *)
(* A: iff is transparent.  What is not transparent? *)


auto.
  info_auto.

  rewrite a.
  change b with a. 
(*in |- *.*)
  split.

intro E.
replace x0 with y .


Inductive mybool:=| a:True->mybool |b:mybool.
Theorem g: mybool.
constructor.
Defined.

(*intros q w.*)

intros.


apply (@nonempty_intro _ _ H0).

Check (@nonempty_intro _ _ H0).

Focus 2.
constructor.
unfold nonempty.
red.
Defined.
(*
elimtype (nonempty x).
cofix x.
fix Q 0.
*)

Proof.
Defined.

Proof.
Defined.
