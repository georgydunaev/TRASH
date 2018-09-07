(*https://stackoverflow.com/questions/46838928/nested-recursion-and-program-fixpoint-or-function*)
Require Import Coq.Lists.List.
Import ListNotations.
Definition SetVars  := nat.
Definition FuncSymb := nat.
Definition PredSymb := nat.
Record FSV := {
 fs : FuncSymb;
 fsv : nat;
}.
Record PSV := MPSV{
 ps : PredSymb;
 psv : nat;
}.

Section tree.
(*Context {A:Type}.*)
Unset Elimination Schemes.
Inductive preTerms := 
|Vari : SetVars -> preTerms
|Node : FSV -> list preTerms -> preTerms.
Set Elimination Schemes.

Inductive isTerm1 : preTerms -> Prop := 
|c1 : forall (v : SetVars), isTerm1 (Vari v)
|c2 : forall (f:FSV)(lt:list preTerms),
 ((fsv f) = (length lt))->
(* (fold_right (fun t => and (isTerm t)) True lt)->*)
  isTerm1 (Node f lt).

Inductive isTerm2 : preTerms -> Prop := 
|c3 : forall (v : SetVars), isTerm2 (Vari v)
|c4 : forall (f:FSV)(lt:list preTerms),
(fold_right (fun t => and (isTerm1 t)) True lt)->
  isTerm2 (Node f lt).

(*
Inductive isTerm : forall (n:nat), preTerms -> Prop := 
|a1 : forall (n:nat) (v : SetVars), isTerm n (Vari v)
|a2 : forall (n:nat) (f:FSV) (lt:list preTerms),
 ((fsv f) = (length lt))->
  (fold_right (fun t => and (isTerm n t)) True lt)->
  isTerm (S n) (Node f lt).*)
Check True.
(*Inductive isTerm (n:nat): preTerms -> Prop := 
|a1 : forall (v : SetVars), isTerm n (Vari v)
|a2 : forall (f:FSV) (lt:list preTerms),
 ((fsv f) = (length lt))->
  (fold_right (fun t => and (isTerm n t)) True lt)->
  isTerm (S n) (Node f lt).*)
Check True.
Fixpoint isTerm' (n:nat) (x : preTerms) {struct n}: Prop
:=match n with
  | 0 => True
  | S n => 
   match x with 
   | Vari v => True
   | Node f lp => (and ((length lp)=(fsv f)) (Forall (isTerm' n) lp))
   end
  end.

Definition isTerm (x : preTerms) := forall (n:nat), isTerm' n x.


FSV -> list preTerms -> preTerms.


Section tree_ind.
Context  (P : preTerms -> Prop).
Context  (Q : FSV -> list preTerms -> Prop).
Context  (IH1 : forall s, P (Vari s)).
Context  (IH2 : forall (n : FSV) (ts : list preTerms),
          (fold_right (fun t => and (P t)) True ts) ->
          (Q n ts) ->
          P (Node n ts)).
Fixpoint tree_ind
  (t : preTerms) : P t (*. destruct t.*)
 :=
  match t with
  | Vari v => IH1 v
  | Node n ts =>
    let fix loop ts :=
      match ts return fold_right (fun t' => and (P t')) True ts with
      | [] => I
      | t' :: ts' => conj (tree_ind t') (loop ts')
      end in
    IH2 n ts (loop ts)
  end.
End tree_ind.

(*Fixpoint map_preTerms (f : FSV -> FSV) (t : preTerms ) : preTerms :=
  match t with
  | Node x ts => Node (f x) (map (fun t => preTerms f t) ts)
  end.*)
End tree.
Compute map_tree S (Node 0 ((Node 1 nil) :: (Node 2 nil) :: nil)).
Compute map_tree S (Node 1 [Node 2 []; Node 3 []]).
(*Print tree.*)

(* PUBLIC DOMAIN *)
Require Export Coq.Vectors.Vector.
Require Export Coq.Lists.List.
Require Import Bool.Bool.
Require Import Logic.FunctionalExtensionality.
Require Import Coq.Program.Wf.
Require Import Lia.
Add LoadPath "/home/user/0data/COQ/SHEN/".
Require Export ListForallT.

Definition preTerms := @tree (sum SetVars FSV).

