(* The theorem is still not proven... *)
Require Vector.
Require List.




Fixpoint all_then_some (A:Type) (l:list bool) {struct l}:
(forall (b:bool), (List.fold_left orb l b)  = b) <->
(forall (p:nat), (List.nth p l false) = false).
Proof.
destruct l.
simpl.
split. intros _ p.
destruct p; trivial.
intros _; reflexivity.

split.
* intros.
simpl.
destruct p.
destruct b.
pose (J:= proj1 (all_then_some A (cons true l)) H 0).
simpl in J.
exact J.
reflexivity.
 admit.
* admit.
Abort.



(*Check proj1 (all_then_some A (cons true l)) H.
destruct b.
simpl in * |- *.
destruct p.*)
Theorem lm000 (p : Fin.t 0): False.
Proof. exact (Fin.case0 (fun _ => False) p ). Defined.

(*
Definition rectS (P: forall {n}, t (S n) -> Type)
  (P1: forall n, @P n F1) (PS : forall {n} (p: t (S n)), P p -> P (FS p)):
  forall {n} (p: t (S n)), P p.
*)

Lemma all_then_some (A:Type): forall (n:nat)(p:Fin.t (S n)) (v:Vector.t bool (S n))
(H : Vector.fold_left orb false v = false),
 (Vector.nth v p) = false.
Proof.
(*destruct n.
intro p; apply Fin.case0; exact p.*)
fix i 1.
Check Fin.rectS (fun n p => forall (v : Vector.t bool (S n)), (Vector.nth v p = false)).
intros n p v K.
unshelve eapply (Fin.rectS (fun n p => forall (v : Vector.t bool (S n)), (Vector.nth v p = false))).
+ intros. simpl.
destruct v.
unfold Vector.nth.
simpl.

Check Fin.rectS.
unshelve eapply Fin.rectS.
4 : exact p.
intros.
apply i; exact K.
trivial.
Defined.
Check Fin.rectS.

induction p with Fin.rectS  .
intros p v H.
Print Fin.t.
eqn: j
destruct p.
inversion p.

destruct p, v eqn: w.
simpl in * |- *.

induction v.
inversion p.


destruct h.
admit.
simpl in H.
unfold Vector.nth.

(*pose (G:= IHv (@Fin.F1 n) H).
simpl.
destruct p.*)
Abort.


rewrite -> l01 in H.
