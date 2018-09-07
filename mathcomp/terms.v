(*Add LoadPath "/home/user/Downloads/archives/math-comp-mathcomp-1.7.0/".*)
(*Add mathcomp "/home/user/Downloads/archives/math-comp-mathcomp-1.7.0/mathcomp".*)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq.
From mathcomp Require Import ssrnat.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition SetVars  := nat.

Definition FuncSymb := nat.

Record FSV := {
 fs : FuncSymb;
 fsv : nat;
}.

Unset Elimination Schemes.
Inductive preterm :=
| Vari :> SetVars -> preterm
| Node : FSV -> list preterm -> preterm.
Set Elimination Schemes.


Section Ind.

Variable T : preterm -> Type.
Variable HVari : forall sv, T (Vari sv).
Variable HNode : forall fv ts, 
foldr (fun t acc => T t * acc)%type unit ts -> T (Node fv ts).

Fixpoint preterm_rect (t : preterm) : T t :=
  match t with
  | Vari sv => HVari sv
  | Node fv ts =>
    let fix loop ts : foldr (fun t acc => T t * acc)%type unit ts :=
        match ts with
        | [::] => tt
        | t :: ts => (preterm_rect t, loop ts)
        end in
    HNode fv (loop ts)
  end.

End Ind.

Definition preterm_ind := preterm_rect.

Require Import Arith Omega.
From Equations Require Import Equations.
(*Derive Signature Subterm for preterm.*)


Fixpoint is_term (t : preterm) :=
  match t with
  | Vari _ => true
  | Node fv ts => (fsv fv == length ts) && all is_term ts
  end.

Theorem thm0 fv (t:preterm) ts (H : is_term (Node fv (cons t ts))) : is_term t.
simpl in * |- *.
revert H.
move/andP.
intro H;destruct H;revert H0.
move/andP.
firstorder.
Abort.
Theorem thm0 fv(t:preterm)ts:forall (H : is_term (Node fv (cons t ts))), is_term t.
Proof.
by move/and3P => [X1 X2 X3].
(* destruct Q as [X1 X2 X3]; exact X2.*)
Defined.

Record term := Term { tval :> preterm; irt : is_term tval }.

Section let_will_not_survive.
Let fu u  := let: ( m, n ) := u in m + n .
End let_will_not_survive.
Fail Check fu.

Canonical term_subType := [subType for tval].
(*
Print  term_subType.
Print  subType. *)
Definition term_args t : list term :=
  match  t with
  | Vari _     => [::]
  | Node fv ts => pmap insub ts
  end.

Fixpoint substT (t:preterm) (xi: SetVars) (u:preterm): preterm.
Proof.
destruct u.
2 : { refine (Node f _).
exact (map (substT t xi) l). }
destruct (PeanoNat.Nat.eqb s xi).
exact t.
exact s.
Show Proof.
Abort.

(*Definition substT :=
(fix substT (t : preterm) (xi : SetVars) (u : preterm) {struct u} : preterm :=
   match u with
   | Vari s => let b := (s =? xi) in if b then t else Vari s
   | Node f l => Node f [seq substT t xi i | i <- l]
   end).*)
Definition substT :=
(fix substT (t : preterm) (xi : SetVars) (u : preterm) {struct u} : preterm :=
   match u return preterm with
   | Vari s =>
       let b : bool := Nat.eqb s xi in
       match b return preterm with
       | true => t
       | false => Vari s
       end
   | Node f l => Node f (@map preterm preterm (substT t xi) l : list preterm)
   end).

Check 0.

(*Inductive isTerm : preterm -> Prop :=
| c1 (q:preterm) (H:is_term q) : isTerm q.
Check isTerm_ind.*)

(* not finished
Fixpoint substIsTerm (t:term) (xi: SetVars) (u:term): is_term (substT t xi u).
destruct u as [tval0 i0].
simpl.

revert t xi tval0 i0. fix Hyp 3. intros.
Show Proof.
destruct tval0 as [ s | f l ].
simpl.
destruct (PeanoNat.Nat.eqb s xi) .
exact (irt t).
exact (i0).
simpl.
apply/andP.
split.
Locate " <- ]".
Locate length.
pose (q:= List.map_length).
rewrite -> q.
simpl in i0.
destruct (@andP (fsv f == length l) (all is_term l)) as [B1|B2].
firstorder.
exfalso.
exact (not_false_is_true i0).
Locate all.
simpl in i0.
destruct (@andP (fsv f == length l) (all is_term l)) as [B1|B2].
2 : { exfalso; exact (not_false_is_true i0). }
destruct B1. (* *)
Check all.
Locate conj.
pose (P1 := (fun a b => proj1 (List.forallb_forall a b)) _ _ H0).
apply (fun a b => proj2 (List.forallb_forall a b)).
intros.
simpl in *|-*.

Check (fun x1 x2 x3 x4 x5 => proj1 (@List.in_map_iff x1 x2 x3 x4 x5)).
Check (Hyp t xi x). 
Check List.in_map_iff.
(* usilit hyp ili rewrite H1
y := x
f := substT t xi
l := L
*)
Check (substT t xi).
pose lm1 := (@List.in_map_iff _ _ (substT t xi) l x).
pose lm2 := (proj1 lm1 H1).
destruct lm2 as [x0 [J0 J1]].
rewrite <- J0.
apply Hyp.
apply P1.
exact J1.
Defined.
Abort.*)

Check 0.

Section heredity.
Hypotheses (t : term) (xi : SetVars).
Fixpoint Hyp (tval0 : preterm) :
      is_term tval0 -> is_term (substT t xi tval0).
(*apply/implyP.
move/implyP.*)
intro H.
induction tval0 eqn:w.
simpl.
destruct (sv =? xi ).
simpl.
exact (irt t).
exact H.
simpl in * |- *.
apply/andP.
split.
revert H. move/andP. intro H. destruct H.
pose (q:= List.map_length).
rewrite -> q.
firstorder.
revert H. move/andP. intro H. destruct H.
rewrite <- all_map; fold is_term.
simpl in * |- *.
Abort.

Compute subn_rec 0 2.
Lemma l1: 4<=23.
Proof. by [].
Compute 4<=23.
Show Proof.
Abort.
(*intro a.
case a.*)
End heredity.

(* big proof *)
Fixpoint substIsTerm (t:term) (xi: SetVars) (u:term): 
is_term (substT t xi u).
destruct u as [tval0 i0].
simpl.
revert t xi tval0 i0. fix Hyp 3. intros.
Show Proof.
destruct tval0 as [ s | f l ].
simpl.
destruct (PeanoNat.Nat.eqb s xi) .
exact (irt t).
exact (i0).
simpl.
destruct l.
simpl in * |- *.
exact i0.
simpl in * |- *.
apply/andP.
split.
pose (q:= List.map_length).
rewrite -> q.
simpl in i0.
destruct (@andP (fsv f == (length l).+1) (all is_term l)) 
 as [B1|B2].
firstorder.

(* i0 must be destructed *)
(*destruct (@andP (fsv f == length l) (all is_term l)) as [B1|B2].*)

(* NOT BAD
exfalso.
exact (not_false_is_true i0).
Locate all.
simpl in i0.
destruct (@andP (fsv f == length l) (all is_term l)) as [B1|B2].
2 : { exfalso; exact (not_false_is_true i0). }
destruct B1. (* *)
Check all.
Locate conj.
pose (P1 := (fun a b => proj1 (List.forallb_forall a b)) _ _ H0).
apply (fun a b => proj2 (List.forallb_forall a b)).
intros.
simpl in *|-*.

Check (fun x1 x2 x3 x4 x5 => proj1 (@List.in_map_iff x1 x2 x3 x4 x5)).
Check (Hyp t xi x). 
Check List.in_map_iff.
(* usilit hyp ili rewrite H1
y := x
f := substT t xi
l := L
*)
Check (substT t xi).
pose lm1 := (@List.in_map_iff _ _ (substT t xi) l x).
pose lm2 := (proj1 lm1 H1).
destruct lm2 as [x0 [J0 J1]].
rewrite <- J0.
apply Hyp.
apply P1.
exact J1.*)
Abort.





eapply Hyp.
pose (P2 := ).

Check (@all_map _ _ (Hyp t xi)).
Check @preim.
Print pred.
Print simpl_pred.
Print simpl_fun.


Print Bool.reflect.
try bool_congr.
pose (w:= andP).

(* length o map = length *)

compute.

compute.
Locate is_true.
Locate andP.
Compute ( fun (b1 b2:bool) => reflect (b1 /\ b2) (b1 && b2) ).
Print is_true.
(*simple refine (( fun (b1 b2:bool) => reflect (b1 /\ b2) (b1 && b2) ) 
(fsv f == length [seq substT t xi i | i <- l]) 
(all is_term [seq substT t xi i | i <- l])).*)
Print andP.
apply/andP.
split.
unfold is_term in i0.
Check andP.

Theorem qua: forall (a b:bool), (a && b) -> (a /\ b).
move=> a b c.
case a .
case b.
split; trivial.
apply/andP.
auto.
inversion c.
destruct i0.

simpl.
Print andE.

case.

eapply reflect.
simple refine ( _ , _ ).

eapply substIsTerm.
Defined.


Fixpoint substT2 (t:term) (xi: SetVars) (u:term): term.
destruct u as [tval0 i0].
simple refine (@Term _ _).
exact (substT t xi tval0).
unfold is_term.
destruct t as [tval1 i1].
simpl.
destruct tval1 as [ s | f l ].
2 : {
compute.

simpl.



induction substT2.

exact (substT t xi u).

Locate "==".
Locate "[ :: ]".
Locate eq_op.

Theorem th0 : is_true (1 + 1 == 2).
compute.
reflexivity.
Show Proof.
Defined.
Print th0.
Compute is_true (1 + 1 == 2).
(*Compute 1 + 1 == 2.
simpl*)
Theorem th : (1+1 = 2).
simple refine ((1+1 =P 2) _ ).
compute.
reflexivity.
Defined.
Check ((1+1 =P 2) th0 ).

Check let x:= (compute (1+1 =P 2))  in x.
Check ((compute in (1+1 =P 2)) (erefl 2)  ).

Locate "^~".

Print pmap.
Definition fu (x:nat) :=
match x with
| 2 => None
| x => Some x
end.

Compute (pmap fu (4::3::2::1::0::[::])).

Check Some 3 :: None :: Some 1 :: [::].
Locate pmap.

Print Option.apply.
Print oapp.
Print seq.