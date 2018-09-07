(*https://stackoverflow.com/questions/46838928/nested-recursion-and-program-fixpoint-or-function*)
Require Import Coq.Lists.List.
Import ListNotations.

Section tree.
Context {A:Type}.
Unset Elimination Schemes.
Inductive tree := Node : A -> list tree -> tree.
Set Elimination Schemes.
Section tree_ind.
Context  (P : tree -> Prop).
Context  (IH : forall (n : A) (ts : list tree),
          fold_right (fun t => and (P t)) True ts ->
          P (Node n ts)).
Fixpoint tree_ind
  (t : tree) : P t :=
  match t with
  | Node n ts =>
    let fix loop ts :=
      match ts return fold_right (fun t' => and (P t')) True ts with
      | [] => I
      | t' :: ts' => conj (tree_ind t') (loop ts')
      end in
    IH n ts (loop ts)
  end.
End tree_ind.
Fixpoint map_tree (f : A -> A) (t : tree ) : tree :=
  match t with
  | Node x ts => Node (f x) (map (fun t => map_tree f t) ts)
  end.
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
Inductive preTerms :=
|
| tree preTerms -> preTerms

Definition preTerms := @tree (sum SetVars FSV).

