Definition injective := 
fun {rT aT : Type} (f : aT -> rT) => forall x1 x2 : aT, f x1 = f x2 -> x1 = x2.
Definition nat_of_bool := fun b : bool => if b then 1 else 0.
Lemma nat_of_bool_inj : injective nat_of_bool.
Proof. 
unfold injective.
intros. 
unfold nat_of_bool in * |-.
destruct x1,x2; (trivial || inversion H).
(*trivial.
inversion H.
inversion H.
trivial.*)
Defined.

CoInductive bigbody (R I : Type) : Type :=
    BigBody : I -> (R -> R -> R) -> bool -> R -> bigbody R I.

Definition applybig {R I} (body : bigbody R I) (x:R) :  R
:= (match body with
| BigBody _ _ _ op true v => op v x
| BigBody _ _ _ op false _ => x
end).


Definition funcomp :=fun {A B C : Type} (u : unit) (f : B -> A) (g : C -> B) (x : C) =>
let 'tt := u in f (g x).
Definition foldr :=fun {T R : Type} (f : T -> R -> R) (z0 : R) =>
fix foldr (s : list T) : R :=
  match s with
  | nil => z0
  | cons x s' => f x (foldr s')
  end.

Definition reducebig R I idx r (body : I -> bigbody R I) :=
  foldr (funcomp tt applybig body) idx r.

Section bigop_sec.
Hypothesis bigop : forall {R} {I}, R -> list I -> (I -> bigbody R I) -> R.

Check bigop _ _ 0.
(*Definition index_enum (T : finType) := Finite.enum T.*)

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(*Lemma nat_of_bool_inj : injective nat_of_bool.
Proof. by case=> [] []. Qed.*)

Lemma all_false n (r : n.-tuple bool) :
  \max_(i in 'I_n) tnth r i <= 0 ->
  forall i, tnth r i = false.
Proof.
by move/bigmax_leqP => H i; apply/nat_of_bool_inj/eqP; rewrite -leqn0 H.
Show Proof.
Qed.

(**"\max_"
bigmax_leqP : forall (I : finType) (P : pred I) (m : nat) (F : I -> nat),
       reflect (forall i : I, P i -> F i <= m) (\max_(i | P i) F i <= m)
eqP : reflect (?x = ?y) (?x == ?y)
leqn0 : forall n : nat, (n <= 0) = (n == 0)

"\max_ ( i | P ) F" := BigOp.bigop O (index_enum _)
                         (fun i => BigBody i maxn P F) : nat_scope
**)
Lemma all_false_tran (n:nat) (r:list bool) :

->
True.


Locate "\o".
Print funcomp.
Print foldr.

Locate ".-tuple".
Print tuple_of.
Locate "\max_".
(*"\max_ ( i 'in' A ) F" := BigOp.bigop O (index_enum _)
                            (fun i => BigBody i maxn (in_mem i (mem A)) F)
: nat_scope *)

Check BigBody.
(* BigBody : forall R I : Type, I -> (R -> R -> R) -> bool -> R -> bigbody R I *)
Print BigBody.
Locate "'I_".
(* "''I_' n" := ordinal n (default interpretation) *)
Print tnth.
(* tnth = 
fun (n : nat) (T : Type) (t : n.-tuple T) (i : 'I_n) =>
nth (tnth_default t i) t i
     : forall (n : nat) (T : Type), n.-tuple T -> 'I_n -> T *)
