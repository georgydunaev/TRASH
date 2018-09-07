(* PUBLIC DOMAIN *)
Require Export Coq.Vectors.Vector.
Require Export Coq.Lists.List.
Require Import Bool.Bool.
Require Import Logic.FunctionalExtensionality.
Require Import Coq.Program.Wf.
Require Import Lia.

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

Section All.
  Variable T : Type.
  Variable P : T -> Prop.

  Fixpoint All (ls : list T) : Prop :=
    match ls with
      | nil => True
      | cons h t => P h /\ All t
    end.
End All.

Section AllT.
  Variable T : Type.
  Variable P : T -> Type.

  Fixpoint AllT (ls : list T) : Type :=
    match ls with
      | nil => True
      | cons h t => (P h) * (AllT t)
    end.
End AllT.


Inductive preTerms : Type :=
| FVC :> SetVars -> preTerms
| FSC (f:FSV) : list preTerms -> preTerms.

Section preTerms_ind'.
  Variable P : preTerms -> Prop.

  Hypothesis preTerms_case1 : forall (sv : SetVars), P (FVC sv).

  Hypothesis preTerms_case2 : forall (n : FSV) (ls : list preTerms),
    All preTerms P ls -> P (FSC n ls).

  Fixpoint preTerms_ind' (tr : preTerms) : P tr.
  Proof.
  destruct tr.
  exact (preTerms_case1 _).
  apply preTerms_case2.
  revert l; fix G 1; intro l.
  destruct l;simpl;trivial.
  split.
  apply preTerms_ind'.
  apply G.
Show Proof.
  Defined.

(** fix preTerms_ind' (tr : preTerms) : P tr :=
   match tr as p return (P p) with
   | FVC s => preTerms_case1 s
   | FSC f l =>
       preTerms_case2 f l
         ((fix G (l0 : list preTerms) : All preTerms P l0 :=
             match l0 as l1 return (All preTerms P l1) with
             | Datatypes.nil => I
             | p :: l1 => conj (preTerms_ind' p) (G l1)
             end) l)
   end **)
End preTerms_ind'.

Section preTerms_rect'.
  Variable P : preTerms -> Type.

  Hypothesis preTerms_case1 : forall (sv : SetVars), P (FVC sv).

  Hypothesis preTerms_case2 : forall (n : FSV) (ls : list preTerms),
    AllT preTerms P ls -> P (FSC n ls).

  Fixpoint preTerms_rect' (tr : preTerms) : P tr.
  Proof.
  destruct tr.
  exact (preTerms_case1 _).
  apply preTerms_case2.
  revert l; fix G 1; intro l.
  destruct l;simpl;trivial.
  split.
  apply preTerms_rect'.
  apply G.
Show Proof.
  Defined.

(** fix preTerms_ind' (tr : preTerms) : P tr :=
   match tr as p return (P p) with
   | FVC s => preTerms_case1 s
   | FSC f l =>
       preTerms_case2 f l
         ((fix G (l0 : list preTerms) : All preTerms P l0 :=
             match l0 as l1 return (All preTerms P l1) with
             | Datatypes.nil => I
             | p :: l1 => conj (preTerms_ind' p) (G l1)
             end) l)
   end **)
End preTerms_rect'.


(*Definitio isTerm (t : preTerms) : Prop.*)

Fixpoint isTerm (t : preTerms) : Prop.
revert t; apply preTerms_rect'; intros.
exact True.
exact ((length ls)=(fsv n)).
Defined.

Eval compute in isTerm (FSC (Build_FSV 0 3) ((FVC 0)::(FVC 0)::(FVC 0)::nil)).

(*elim t using preTerms_ind'.
induction t using preTerms_ind'.*)

Inductive nat_tree : Set :=
| NNode' : nat -> list nat_tree -> nat_tree.



Check Forall.

Fixpoint mh (t : preTerms) : nat :=
  match t with
  | FVC _ => 0
  | FSC f l => S (fold_right (fun t acc => Nat.max acc (mh t)) 0 l)
  end.

Program Fixpoint isTerm isTerm (t : preTerms) {measure (mh t)}: Prop :=
   match t with
   | FVC _ => True
   | FSC f l => (length l = fsv f) /\ (@Forall preTerms (fun q=>isTerm q) l )
(*@All _ _ isTerm l*)
   end.

(isTerm a) /\ (chkd fu l)

Inductive isTerm : preTerms -> Prop :=
| c (pt : preTerms) 
(H: match pt with 
| FVC sv => True
| FSC f lpt => (Forall isTerm lpt) 
end) : isTerm pt.

Inductive Terms : Type :=
| nas (pt : preTerms) (H:isTerm pt): Terms
with isTerm :=
| c (pt : preTerms) () : isTerm pt

Fixpoint isTerm :=
(fix isTerm (t : preTerms) : Prop :=
   match t with
   | FVC _ => True
   | FSC f l => length l = fsv f /\ 
((fix chkd (fu : preTerms -> Prop )(l : list preTerms) : Prop :=
   match l with
   | nil => True
   | a::l => (isTerm a) /\ (chkd fu l)
   end) isTerm l)
   end).

Fixpoint isTerm (t:preTerms) : Prop.
destruct t.
exact True.
refine (((length l)=(fsv f))/\ _).
exact (List.Forall isTerm l).
Show Proof.
Defined.
destruct l.
exact True.
exact (List.Forall isTerm l).
Defined.
Show Proof.

Unset Elimination Schemes.
Set Elimination Schemes.

Definition Terms_rect (T : Terms -> Type)
                      (H_FVC : forall sv, T (FVC sv))
                      (H_FSC : forall f v, (forall n, T (Vector.nth v n)) -> T (FSC f v)) :=
  fix loopt (t : Terms) : T t :=
    match t with
    | FVC sv  => H_FVC sv
    | FSC f v =>
      let fix loopv s (v : Vector.t Terms s) : forall n, T (Vector.nth v n) :=
        match v with
        | @Vector.nil _ => Fin.case0 _
        | @Vector.cons _ t _ v => fun n => Fin.caseS' n (fun n => T (Vector.nth (Vector.cons _ t _ v) n))
                                                      (loopt t)
                                                      (loopv _ v)
        end in
      H_FSC f v (loopv _ v)
    end.

Definition Terms_ind := Terms_rect.

Fixpoint height (t : Terms) : nat :=
  match t with
  | FVC _ => 0
  | FSC f v => S (Vector.fold_right (fun t acc => Nat.max acc (height t)) v 0)
  end.

(* BEGIN *)
Definition substT :=
(fix substT (t : Terms) (xi : SetVars) (u : Terms) {struct u} : Terms :=
   match u with
   | FVC s => let b := PeanoNat.Nat.eqb s xi in if b then t else FVC s
   | FSC f t0 => FSC f (Vector.map (substT t xi) t0)
   end).

Fixpoint isParamT (xi : SetVars) (t : Terms) {struct t} : bool :=
   match t with
   | FVC s => PeanoNat.Nat.eqb s xi
   | FSC f t0 => Vector.fold_left orb false (Vector.map (isParamT xi) t0)
   end.

Section cor.
Context (X:Type).
Context (fsI:forall(q:FSV),(Vector.t X (fsv q))->X).
Context (prI:forall(q:PSV),(Vector.t X (psv q))->Prop).

Definition teI :=
 (fix teI (val : SetVars -> X) (t : Terms) {struct t} : X :=
   match t with
   | FVC s => val s
   | FSC f t0 => fsI f (Vector.map (teI val) t0)
   end).

(** (\pi + (\xi \mapsto ?) ) **)
Definition cng (val:SetVars -> X) (xi:SetVars) (m:X) (r:SetVars) :=
   match Nat.eqb r xi with
   | true => m
   | false => (val r)
   end.


Section Lem1.
Context (t : Terms).

Definition P(xi : SetVars) (pi : SetVars->X) (u :Terms)
:=(teI pi (substT t xi u))=(teI (cng pi xi (teI pi t)) u).

Definition ap {A B}{a0 a1:A} (f:A->B) (h:a0=a1):((f a0)=(f a1))
:= match h in (_ = y) return (f a0 = f y) with
   | eq_refl => eq_refl
   end.


Fixpoint vec_comp_as (A B C : Type) (f : B -> C) (g : A -> B) 
             (n : nat) (t0 : Vector.t A n) {struct t0} :
   Vector.map f (Vector.map g t0) = Vector.map (fun x : A => f (g x)) t0 :=
   match
     t0 as t in (Vector.t _ n0)
     return
       (Vector.map f (Vector.map g t) = Vector.map (fun x : A => f (g x)) t)
   with
   | Vector.nil _ => eq_refl
   | Vector.cons _ h n0 t1 =>
       eq_ind_r
         (fun t : Vector.t C n0 =>
          Vector.cons C (f (g h)) n0 t =
          Vector.cons C (f (g h)) n0 (Vector.map (fun x : A => f (g x)) t1))
         eq_refl (vec_comp_as A B C f g n0 t1)
   end.

(*
Program Fixpoint lem1 (u : Terms) (xi : SetVars) (pi : SetVars -> X) 
{measure (height u)} :
   teI pi (substT t xi u) = teI (cng pi xi (teI pi t)) u :=
   match
     u as t0 return (teI pi (substT t xi t0) = teI (cng pi xi (teI pi t)) t0)
   with
   | FVC s =>
       let b := Nat.eqb s xi in
       if b as b0
        return
          (teI pi (if b0 then t else s) = (if b0 then teI pi t else pi s))
       then eq_refl
       else eq_refl
   | FSC f t0 =>
       match
         f as f0
         return
           (forall t1 : Vector.t Terms (fsv f0),
            fsI f0 (Vector.map (teI pi) (Vector.map (substT t xi) t1)) =
            fsI f0 (Vector.map (teI (cng pi xi (teI pi t))) t1))
       with
       | {| fs := fs0; fsv := fsv0 |} =>
           fun t1 : Vector.t Terms (fsv {| fs := fs0; fsv := fsv0 |}) =>
           ap (fsI {| fs := fs0; fsv := fsv0 |})
             (let g :
                Vector.map (teI pi) (Vector.map (substT t xi) t1) =
                Vector.map (fun x : Terms => teI pi (substT t xi x)) t1 :=
                vec_comp_as Terms Terms X (teI pi) (substT t xi) fsv0 t1 in
              eq_ind_r
                (fun t2 : Vector.t X fsv0 =>
                 t2 = Vector.map (teI (cng pi xi (teI pi t))) t1)
                (let Y := fun wm : Terms -> X => Vector.map wm t1 in
                 let a1 := fun x : Terms => teI pi (substT t xi x) in
                 let a2 := teI (cng pi xi (teI pi t)) in
                 let Y1 := Y a1 in
                 let Y2 := Y a2 in
                 ap Y
                   (functional_extensionality
                      (fun x : Terms => teI pi (substT t xi x))
                      (teI (cng pi xi (teI pi t)))
                      (fun x : Terms => lem1 x xi pi))) g)
       end t0
   end.
Next Obligation.*)


Definition lem1 : forall(u :Terms)(xi : SetVars)(pi : SetVars->X), P xi pi u.
Proof. unfold P.
fix lem1 1.
intros.
destruct u as [s|f] .
+ simpl.
  unfold cng.
  destruct (Nat.eqb s xi).
  * reflexivity.
  * simpl.
    reflexivity.
+
  simpl.
  destruct f.
  simpl in * |- *.
  apply ap.

  simpl in t0.
revert fsv0 t0.
fix FFF 1.
intros fsv0 t0.
destruct t0 ; simpl in * |- *; trivial.

Lemma equal_a : forall (A B : Type) (f : A -> B) (a0 a1:A),
  (a0 = a1) -> f a0 = f a1.
Proof.
intros A B f a0 a1 r.
destruct r.
reflexivity.
Defined.

Check (FFF n).
rewrite <- FFF.
Check (functional_extensionality _ _ (FFF fs0)).

Check f_equal.
Check (f_equal (fun g=> Vector.cons X g n
  (Vector.map (teI pi) (Vector.map (substT t xi) t0)))).
apply (f_equal (fun g=> Vector.cons X g n
  (Vector.map (teI pi) (Vector.map (substT t xi) t0)))).
rewrite lem1.
reflexivity.
Defined.


Check functional_extensionality.
rewrite lem1.
apply f_equal.
reflexivity.
Defined.
rewrite -> FFF.

rewrite <- (functional_extensionality _ _ (FFF n)).
rewrite <- (functional_extensionality _ _ (FFF n)).
apply f_equal.

rewrite  FFF.

rewrite <- (functional_extensionality _ _ (FFF n)).
simpl.
Check (@f_equal _ _ _ _ _ _).
apply f_equal.

simpl.

apply functional_extensionality.

  apply ap.

  apply equal_a.

simpl.
  apply ap.

Check (FFF _ (Vector.map (teI pi) (Vector.map (substT t xi) t0)) ).
apply FFF.




  pose (g:= (@vec_comp_as _ _ _ (teI pi) (substT t xi) _ t0)).
  rewrite -> g.
(*Check (@vec_comp_as _ _ _ (teI ) (cng pi xi (teI pi t)) _ ).
  pose (g:= (@vec_comp_as _ _ _ (teI pi) (substT t xi) _ t0)).
  rewrite -> g.*)

pose (Y:=fun wm => @Vector.map Terms X wm fsv0 t0).
pose (a1:=(fun x : Terms => teI pi (substT t xi x))).
pose (a2:=(teI (cng pi xi (teI pi t)))).
pose (Y1:= Y a1).
pose (Y2:= Y a2).
unfold Y in Y1.
unfold Y in Y2.
fold Y1 Y2 in |- *.
apply (@ap _ _ a1 a2 Y).
unfold a1, a2 in |- *.
apply functional_extensionality.
    intro x.

refine (lem1 x xi pi ).
Show Proof.

Admitted.




