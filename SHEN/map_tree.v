(*https://stackoverflow.com/questions/46838928/nested-recursion-and-program-fixpoint-or-function*)
Require Import Coq.Lists.List.
Import ListNotations.

Unset Elimination Schemes.
Inductive tree := Node : nat -> list tree -> tree.
Set Elimination Schemes.

Fixpoint tree_ind
  (P : tree -> Prop)
  (IH : forall (n : nat) (ts : list tree),
          fold_right (fun t => and (P t)) True ts ->
          P (Node n ts))
  (t : tree) : P t :=
  match t with
  | Node n ts =>
    let fix loop ts :=
      match ts return fold_right (fun t' => and (P t')) True ts with
      | [] => I
      | t' :: ts' => conj (tree_ind P IH t') (loop ts')
      end in
    IH n ts (loop ts)
  end.

Fixpoint map_tree (f : nat -> nat) (t : tree) : tree :=
  match t with
  | Node x ts => Node (f x) (map (fun t => map_tree f t) ts)
  end.