Inductive nat_tree : Set :=
| NNode' : nat -> list nat_tree -> nat_tree.
Section All.
  Variable T : Set.
  Variable P : T -> Prop.

  Fixpoint All (ls : list T) : Prop :=
    match ls with
      | nil => True
      | cons h t => P h /\ All t
    end.
End All.

Section nat_tree_ind'.
  Variable P : nat_tree -> Prop.

  Hypothesis NNode'_case : forall (n : nat) (ls : list nat_tree),
    All nat_tree P ls -> P (NNode' n ls).

  Fixpoint nat_tree_ind' (tr : nat_tree) : P tr :=
    match tr with
      | NNode' n ls => NNode'_case n ls
        ((fix list_nat_tree_ind (ls : list nat_tree) : All nat_tree P ls :=
          match ls with
            | nil => I
            | cons tr' rest => conj (nat_tree_ind' tr') (list_nat_tree_ind rest)
          end) ls)
    end.
End nat_tree_ind'.

Section map.
  Variables T T' : Set.
  Variable F : T -> T'.

  Fixpoint map (ls : list T) : list T' :=
    match ls with
      | nil => nil
      | cons h t => cons (F h) (map t)
    end.
End map.

Fixpoint sum (ls : list nat) : nat :=
  match ls with
    | nil => O
    | cons h t => plus h (sum t)
  end.

(*Now we can define a size function over our trees.*)

Fixpoint ntsize (tr : nat_tree) : nat :=
  match tr with
    | NNode' _ trs => S (sum (map _ _ ntsize trs))
  end.

(* Notice that Coq was smart enough to expand the definition of map
 to verify that we are using proper nested recursion, even through 
a use of a higher-order function.*)

Fixpoint ntsplice (tr1 tr2 : nat_tree) : nat_tree :=
  match tr1 with
    | NNode' n nil => NNode' n (cons tr2 nil)
    | NNode' n (cons tr trs) => NNode' n (cons (ntsplice tr tr2) trs)
  end.

(*We have defined another arbitrary notion of tree splicing,
 similar to before, and we can prove an analogous theorem about
 its relationship with tree size. We start with a useful lemma about addition.*)


Add LoadPath "/home/user/Downloads/cpdt/".
Require Import Cpdt.CpdtTactics. (*!!! HOW TO src*)
(**)
Lemma plus_S : forall n1 n2 : nat,
  plus n1 (S n2) = S (plus n1 n2).
  induction n1; crush.
Qed.

(*Now we begin the proof of the theorem, adding the lemma plus_S as a hint.*)

Theorem ntsize_ntsplice : forall tr1 tr2 : nat_tree, ntsize (ntsplice tr1 tr2)
  = plus (ntsize tr2) (ntsize tr1).
  Hint Rewrite plus_S.
(*
We know that the standard induction principle is insufficient for the task, so we need to provide a using clause for the induction tactic to specify our alternate principle.
*)
  induction tr1 using nat_tree_ind'; crush.
(*
One subgoal remains:
  n : nat
  ls : list nat_tree
  H : All
        (fun tr1 : nat_tree =>
         forall tr2 : nat_tree,
         ntsize (ntsplice tr1 tr2) = plus (ntsize tr2) (ntsize tr1)) ls
  tr2 : nat_tree
  ============================
   ntsize
     match ls with
     | Nil => NNode' n (Cons tr2 Nil)
     | Cons tr trs => NNode' n (Cons (ntsplice tr tr2) trs)
     end = S (plus (ntsize tr2) (sum (map ntsize ls)))
 
After a few moments of squinting at this goal, it becomes apparent that we need to do a case analysis on the structure of ls. The rest is routine.
*)
  destruct ls; crush.
(*
We can go further in automating the proof by exploiting the hint mechanism.
*)
  Restart.

  Hint Extern 1 (ntsize (match ?LS with nil => _ | cons _ _ => _ end) = _) =>
    destruct LS; crush.
  induction tr1 using nat_tree_ind'; crush.
Defined.
Qed.
