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
Inductive preTerms := 
|Vari : SetVars -> preTerms
|Node : FSV -> list preTerms -> preTerms.
Fixpoint isNTerm (n:nat) (x : preTerms) {struct n}: Prop
:=match n with
  | 0 => True
  | S n => 
   match x with 
   | Vari v => True
   | Node f lp => (and ((length lp)=(fsv f)) (Forall (isNTerm n) lp))
   end
  end.
Notation isTerm := (fun x =>  (forall (n:nat), isNTerm n x)).
Record Terms := {
 Terms_x : preTerms;
 Terms_H : isTerm Terms_x;
}.
Check Build_Terms.

(* Good *)
Theorem VariIsTerm s y: isNTerm y (Vari s).
Proof.
destruct y.
exact I.
simpl in * |- *.
exact I.
Show Proof.
Defined.

Definition make_visible {X} (f : X) := f.

Notation "` f" := (make_visible f) (at level 5, format "` f").

Tactic Notation "unfold" "notation" constr(f) :=
  change f with (`f).
Tactic Notation "fold" "notation" constr(f) :=
  unfold make_visible.
(*
Fixpoint ListInst A P (t:A) ls : 
(Forall P ls)->(In t ls)->(P t).
intros z w.
unfold In in w.
destruct ls.
destruct w.
destruct w.
rewrite <- H.
eapply Forall_inv.
exact z.
eapply ListInst.
2 : { exact H. }*)



(* \u0422\u0435\u043f\u0435\u0440\u044c \u043d\u0430\u0434\u043e \u043f\u043e\u043a\u0430\u0437\u0430\u0442\u044c, \u0447\u0442\u043e \u0435\u0441\u043b\u0438 \u043d\u0435\u043a\u043e\u0442\u043e\u0440\u044b\u0439 \u043f\u0440\u0435\u0442\u0435\u0440\u043c \u044f\u0432\u043b\u044f\u0435\u0442\u0441\u044f \u0442\u0435\u0440\u043c\u043e\u043c, \u0442\u043e
\u0438 \u0435\u0433\u043e \u0430\u0440\u0433\u0443\u043c\u0435\u043d\u0442\u044b-\u043f\u0440\u0435\u0442\u0435\u0440\u043c\u044b \u0442\u043e\u0436\u0435 \u044f\u0432\u043b\u044f\u044e\u0442\u0441\u044f \u0442\u0435\u0440\u043c\u0430\u043c\u0438. 
\u041f\u0443\u0441\u0442\u044c A - \u043f\u0440\u0435\u0442\u0435\u0440\u043c, \u0442\u043e\u0433\u0434\u0430 (isTerm f ls)/\(In A ls) -> (isTerm A).
*)
Fixpoint ArgIsTerm (f:FSV) (ls:_) A:
(isTerm (Node f ls)) -> (In A ls) -> (isTerm A).
intros H H0.
Proof.
destruct A. (* \u041a\u0430\u043a\u043e\u0433\u043e \u0432\u0438\u0434\u0430 \u0442\u0435\u0440\u043c? *)
- apply VariIsTerm. (* \u041e\u043a!*)
- intro n.
  pose (Q:= H (S n)).
  destruct H.
Check Forall_forall.
pose (GQ := Forall_forall (isNTerm n) ls).
destruct GQ.
apply H1.
assumption.
assumption.
Defined.

Definition lemma00 T (ls:list T):
match ls with
| [] => True
| A::ls0 => In A ls
end.
Proof.
induction ls eqn:g.
exact I.
constructor.
reflexivity.
Defined.

Definition lemma01 (ls:list preTerms):
match ls with
| [] => True
| A::ls0 => In A ls
end.
Proof.
exact (lemma00 preTerms ls).
Defined.

Definition lemma02 (te:Terms) (*(ls:list Terms)*):
match Terms_x te with
| Vari v => True
| Node f ls =>
  match ls with
  | [] => True
  | A::ls0 => In A ls
  end
end.
Proof.
destruct (Terms_x te).
exact I.
exact (lemma01 l).
Defined.


Definition prototype (te:Terms) : list Terms.
Proof.
destruct (Terms_x te) eqn:a1.
exact [].
destruct l eqn:a2.
exact [].
refine [_]. (* here must be refine (_ :: _). *)
unshelve simple eapply Build_Terms.
exact p. (*Terms_x te).*)
eapply (ArgIsTerm f (p::l0) p).
rewrite <- a1.
exact (Terms_H te).
constructor.
reflexivity.
Defined.

Theorem reduce fs0 fsv0 p l0 
(H: isTerm (Node {| fs := fs0; fsv := S fsv0 |} (p :: l0))) :
isTerm (Node {| fs := fs0; fsv := fsv0 |} (l0)).
Proof.
admit.
Admitted.

Fixpoint newmea (te:preTerms) : nat.
Proof.
destruct te.
exact 1.
exact (@List.fold_left _ _ (fun a => fun b => Nat.add a (newmea b)) l 1).
Defined.

Require Import Coq.Program.Wf.

Program Fixpoint lemma03 (te:Terms) {measure (newmea (Terms_x te))}
: list Terms :=
 let p := Terms_x te in
 let a1 : Terms_x te = p := eq_refl in
 match p as p0 return (Terms_x te = p0 -> list Terms) with
 | Vari s => fun _ : Terms_x te = Vari s => []
 | Node f l =>
     fun a2 : Terms_x te = Node f l =>
     let l0 := l in
     let a3 : l = l0 := eq_refl in
     match
       l0 as l1 return (l = l1 -> Terms_x te = Node f l1 -> list Terms)
     with
     | [] => fun (_ : l = []) (_ : Terms_x te = Node f []) => []
     | p0 :: l1 =>
         fun (_ : l = p0 :: l1) (a5 : Terms_x te = Node f (p0 :: l1)) =>
         {|
         Terms_x := p0;
         Terms_H := ArgIsTerm f (p0 :: l1) p0
                      (eq_ind (Terms_x te) isTerm 
                         (Terms_H te) (Node f (p0 :: l1)) a5)
                      (or_introl eq_refl) |}
         :: match
              f as f0 return (Terms_x te = Node f0 (p0 :: l1) -> list Terms)
            with
            | {| fs := fs0; fsv := fsv0 |} =>
                fun
                  a6 : Terms_x te =
                       Node {| fs := fs0; fsv := fsv0 |} (p0 :: l1) =>
                match
                  fsv0 as n
                  return
                    (Terms_x te = Node {| fs := fs0; fsv := n |} (p0 :: l1) ->
                     list Terms)
                with
                | 0 =>
                    fun
                      _ : Terms_x te =
                          Node {| fs := fs0; fsv := 0 |} (p0 :: l1) => []
                | S fsv1 =>
                    fun
                      a7 : Terms_x te =
                           Node {| fs := fs0; fsv := S fsv1 |} (p0 :: l1) =>
                    lemma03
                      (let HYP :
                         isTerm (Node {| fs := fs0; fsv := fsv1 |} l1) :=
                         reduce fs0 fsv1 p0 l1
                           (let w : isTerm (Terms_x te) := Terms_H te in
                            let w0 :
                              forall n : nat,
                              isNTerm n
                                (Node {| fs := fs0; fsv := S fsv1 |}
                                   (p0 :: l1)) :=
                              eq_ind (Terms_x te) isTerm w
                                (Node {| fs := fs0; fsv := S fsv1 |}
                                   (p0 :: l1)) a7 in
                            w0) in
                       {|
                       Terms_x := Node {| fs := fs0; fsv := fsv1 |} l1;
                       Terms_H := HYP |})
                end a6
            end a5
     end a3 a2
 end a1
.
Next Obligation.
admit.
Admitted.

Next Obligation.
admit.
Admitted.

(* These theorems are nasty. *)

Fixpoint lemma03 (te:Terms) : list Terms.
Proof.
destruct (Terms_x te) eqn:a1.
exact [].
destruct l eqn:a2.
exact [].
refine (_ :: _).
unshelve simple eapply Build_Terms.
exact p. (*Terms_x te).*)
eapply (ArgIsTerm f (p::l0) p).
rewrite <- a1.
exact (Terms_H te).
constructor.
reflexivity.
destruct f.
destruct fsv0.
exact [].
(*Here the problem.*)
refine (lemma03 _ ).
assert (HYP : isTerm (Node {| fs := fs0; fsv := fsv0 |} (l0)) ).

unshelve eapply reduce.
exact p.
pose (w:=Terms_H te).
rewrite -> a1 in w.
exact w.
unshelve eapply Build_Terms.
exact (Node {| fs := fs0; fsv := fsv0 |} l0).
exact HYP.
Defined. (* Now go to NewTerms2 *)

refine (@Build_Terms (Node {| fs := fs0; fsv := fsv0 |} (l0)) _).
intro n.
simple refine (@ArgIsTerm _ _ _ _ _ _).

Check Terms_H te n.
refine ()
Defined.

exact  ArgIsTerm f (p::l0) p:
(isTerm (Node f ls)) -> (In A ls) -> (isTerm A).
Defined.
exact I.
re

refine (
match (Terms_x te) with
| Vari v => I
| Node f ls =>
  match ls with
  | [] => I
  | A::ls0 => _
  end
end).

destruct ()

Fixpoint Another (f:FSV) (ls:_) : (isTerm (Node f ls)) -> (In A ls).

(* \u0422\u0435\u043f\u0435\u0440\u044c \u043f\u0440\u0435\u043e\u0431\u0440\u0430\u0437\u043e\u0432\u0430\u043d\u0438\u044f \u0441\u043f\u0438\u0441\u043a\u0430 \u043f\u0440\u0435\u0442\u0435\u0440\u043c\u043e\u0432. *)
Check True.
Notation W := ArgIsTerm.
Definition W' f ls A x y := W f ls A y x.

Fixpoint preobr (f : FSV) (ls : list preTerms) 
(H:forall n : nat, isNTerm n (Node f ls))
{struct ls}: list Terms.
destruct f.
destruct fsv0.
exact [].
destruct ls as [|p ls0].
exact [].
simpl in H.
assert (G: forall n : nat, isNTerm n (Node {| fs := fs0; fsv := fsv0 |} ls0)).
2 : { exact (preobr {| fs := fs0; fsv := fsv0 |} ls0 G). }
simpl in * |- *.

intro y.
induction y; simpl.
exact I.
pose (NQ:= H y ).
(*pose (NQ:= H (S fsv0)).*)
simpl in * |- *.
(*destruct NQ.*)
split.
auto.

Check Forall_inv.


arith.
exact H0.
destruct (H y).
split.
admit.
Admitted.

refine (
match ls with
| [] => []
| a::q => preobr f q _
end ).
destruct n; simpl.
exact I. (* Interesting *)

Definition preobr : forall (f : FSV) (ls : list preTerms) (A : preTerms),
       In A ls ->
       (forall n : nat, isNTerm n (Node f ls)) -> forall n : nat, isNTerm n A.

Fixpoint Com :
Check True.
(*
assert (Y:isTerm (Node f ls)).
unfold notation isTerm.
change isTerm with (fun x =>  (forall (n:nat), isNTerm n x)) in * |- *.
unfold notation isTerm.
intro y.
destruct y.
simpl in * |- *.
Section heredity.
(* 1 Context (t:Terms). *)
(* 2 Context (f:FSV) (l :list preTerms).
Context (H: isTerm (Node f l)). *)
(* 3 *)
Context (f:FSV) (a:preTerms) (l0 :list preTerms).
Context (H: isTerm (Node f (a::l0))).
Theorem thm : isTerm a.
unfold isTerm.
fix K 1.
intro n.
pose (G := H n).
*)
Check True.

Fixpoint Make_TermsList f (l:list preTerms)(H:isTerm (Node f l)) {struct l}: list Terms.


Fixpoint Make_TermsList (t:Terms) : list Terms.
elim t;intros.
destruct Terms_x0 eqn: g.
(*destruct Terms_x0.*)
(*elim Terms_x0;intros.*)
exact [].
change Terms_x0 with (Node f l) in Terms_H0.
(*rewrite <- g in Terms_H0.*)
pose (fu:= (fun A => W _ _ A Terms_H0)).


unshelve eapply (List.map  _ l).
intros p.
simple refine ((Build_Terms _ _)).
exact p.
intro c.
Check W f (p::l) p.
(*
simple eapply (W f (l) ).
assumption.
simple eapply (W f (p::l) p ).
simpl.

intro NN.

Print Node.
constructor.
simpl.

 BAD *)


destruct l.
exact [].
simple refine ((Build_Terms _ _) :: _ ).
exact p.
intro c.
simple eapply (W f (p::l) p Terms_H0).

firstorder. (*GOOD*)

Show Proof.

eapply Make_TermsList.

eapply fu.

unfold isTerm in * |- *.
revert l Terms_H0; fix W 1; intros l Terms_H0.
elim l.
exact [].
intros.
refine ((Build_Terms a _)  :: (W l0 _)).
intro m.
induction m.
simpl in * |- *.
trivial.
 (Terms_H0 m).

2 : {

destruct (Terms_H0 2).
simpl in * |- *.
Fixpoint isParamT (xi : SetVars) (t : Terms) {struct t} : bool :=
   match t.(Terms_x) with
   | Vari s => PeanoNat.Nat.eqb s xi
   | Node f t0 => List.fold_left orb (List.map (isParamT xi) t0) false
   end.

