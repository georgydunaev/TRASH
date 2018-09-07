(*https://stackoverflow.com/questions/46838928/nested-recursion-and-program-fixpoint-or-function*)
Require Import Coq.Lists.List.
Import ListNotations.

Unset Elimination Schemes.
Inductive tree (A:Type) := Node : A -> list (tree A) -> (tree A).
Set Elimination Schemes.

Fixpoint tree_ind
  (A:Type)
  (P : tree A -> Prop)
  (IH : forall (n : A) (ts : list (tree A)),
          fold_right (fun t => and (P t)) True ts ->
          P (Node A n ts))
  (t : (tree A)) : P t :=
  match t with
  | Node _ n ts =>
    let fix loop ts :=
      match ts return fold_right (fun t' => and (P t')) True ts with
      | [] => I
      | t' :: ts' => conj (tree_ind A P IH t') (loop ts')
      end in
    IH n ts (loop ts)
  end.

Fixpoint map_tree (f : nat -> nat) (t : tree) : tree :=
  match t with
  | Node x ts => Node (f x) (map (fun t => map_tree f t) ts)
  end.