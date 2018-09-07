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
End AllT. (* TODO Lists.Forall !!! *)

Unset Elimination Schemes.
Inductive preTerms : Type :=
| FVC :> SetVars -> preTerms
| FSC (f:FSV) : list preTerms -> preTerms.
Set Elimination Schemes.

Section preTerms_ind'.
  Variable P : preTerms -> Prop.

  Hypothesis preTerms_case1 : forall (sv : SetVars), P (FVC sv).

  Hypothesis preTerms_case2 : forall (n : FSV) (ls : list preTerms),
    All preTerms P ls -> P (FSC n ls).

  Fixpoint preTerms_ind (tr : preTerms) : P tr.
  Proof.
  destruct tr.
  exact (preTerms_case1 _).
  apply preTerms_case2.
  revert l; fix G 1; intro l.
  destruct l;simpl;trivial.
  split.
  apply preTerms_ind.
  apply G.
  Defined.
End preTerms_ind'.
(*Print preTerms_ind.
Print preTerms_ind'.*)

Section preTerms_rect'.
  Variable P : preTerms -> Type.

  Hypothesis preTerms_case1 : forall (sv : SetVars), P (FVC sv).

  Hypothesis preTerms_case2 : forall (n : FSV) (ls : list preTerms),
    (@ForallT preTerms P ls) -> P (FSC n ls). 
(*AllT preTerms P ls -> P (FSC n ls).  ForallT!!! *)

  Fixpoint preTerms_rect (tr : preTerms) : P tr.
  Proof.
  destruct tr.
   exact (preTerms_case1 s).
   apply preTerms_case2.
   revert l; fix G 1; intro l.
   destruct l.
    constructor 1.
(* simpl. trivial.
Show Proof.*)
  simpl.
    constructor 2.
apply preTerms_rect.
  (* split.
  apply preTerms_rect.*)
  apply G.
  (*Show Proof.*)
  Defined.
End preTerms_rect'.

Fixpoint height (t : preTerms) : nat :=
  match t with
  | FVC _ => 0
  | FSC f l => S (List.fold_right (fun t acc => Nat.max acc (height t)) 0 l)
  end.

(*Fixpoint isTerm (x : preTerms) : Prop
:= match x with 
   | FVC v => True
   | FSC f lp => (and ((length lp)=(fsv f)) (Forall isTerm lp))
   end.*)
Check True.
(*Program Fixpoint isTerm (x : preTerms) {measure (height x)}: Prop
:= match x with 
   | FVC v => True
   | FSC f lp => (prod ((length lp)=(fsv f)) (Forall isTerm lp))
   end.*)
Check preTerms_rect.
(*Program Fixpoint isTermT (x : preTerms) {measure (height x)}: Type
:= match x with 
   | FVC v => True
   | FSC f lp => (prod ((length lp)=(fsv f)) (ForallT _ isTermT lp))
   end.
The term "isTermT" has type
 "forall x0 : preTerms, height x0 < height x -> Type"
while it is expected to have type "preTerms -> Type"*)
Check True.
Require Import FunInd.
(*
Function isTermT (x : preTerms) {struct x}: Type
:= match x with 
   | FVC v => True
   | FSC f lp => (prod ((length lp)=(fsv f)) (ForallT _ isTermT lp))
   end.
*)
Check True.
Program Fixpoint isTermT (x : preTerms) {measure (height x)}: Type
:= match x with 
   | FVC v => True
   | FSC f lp => True
   end.


 (prod ((length lp)=(fsv f)) (ForallT _ (isTermT x0 H) lp))
Program Fixpoint isTermT (x : preTerms) {measure (height x)}: Type
:= match x with 
   | FVC v => True
   | FSC f lp => (prod ((length lp)=(fsv f)) (ForallT _ (isTermT x0 H) lp))
   end.

Proof.


Fixpoint isTermT (t : preTerms) : Type.
Proof.
induction t. (*revert t; apply preTerms_rect; intros. destruct goves trivial *)
exact True.
refine (sum ((length ls)=(fsv n)) _).
Show Proof.
revert X. fix H 1. intro X.
destruct X.
exact True. (*((fsv n)=0).*)
refine (sum ((length l)=(fsv n)) _).

2 : {
Check 
exact X.
destruct ls.
exact (ForallT X ls).
Show Proof.
Defined.

Fixpoint isTerm (t : preTerms) : Prop.
Proof.
induction t. (*revert t; apply preTerms_rect; intros. destruct goves trivial *)
exact True.
refine (((length ls)=(fsv n))/\ _).
exact X.
destruct ls.
exact (Forall X ls).
Show Proof.
Defined.

Eval compute in isTerm (FSC (Build_FSV 0 3) ((FVC 0)::(FVC 0)::(FVC 0)::nil)).

Fixpoint mh (t : preTerms) : nat :=
  match t with
  | FVC _ => 0
  | FSC f l => S (fold_right (fun t acc => Nat.max acc (mh t)) 0 l)
  end.

Record Terms := 
{
 Terms_t : preTerms;
 Terms_p : isTerm Terms_t;
}.



(*
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
Definition Terms_ind := Terms_rect. *)
Check 0.
Fixpoint height (t : preTerms) : nat :=
  match t with
  | FVC _ => 0
  | FSC f l => S (List.fold_right (fun t acc => Nat.max acc (height t)) 0 l)
  end.

(* BEGIN *)
Definition substT :=
(fix substT (t : preTerms) (xi : SetVars) (u : preTerms) {struct u} : preTerms :=
   match u with
   | FVC s => let b := PeanoNat.Nat.eqb s xi in if b then t else FVC s
   | FSC f t0 => FSC f (List.map (substT t xi) t0)
   end).

Fixpoint isParamT (xi : SetVars) (t : preTerms) {struct t} : bool :=
   match t with
   | FVC s => PeanoNat.Nat.eqb s xi
   | FSC f t0 => List.fold_left orb (List.map (isParamT xi) t0) false
   end.

Section cor.
Context (X:Type).
Context (fsI:forall(q:FSV),(Vector.t X (fsv q))->X).
Context (prI:forall(q:PSV),(Vector.t X (psv q))->Prop).

Fixpoint teI (val : SetVars -> X) (t : Terms) {struct t} : X.
induction t.
induction Terms_t0.
exact (val sv).
Check n.(fsv). (*Set Printing Projections.*)
simpl in * |- *.
unshelve eapply fsI. 
exact n.
rewrite <- Terms_p0.
eapply Vector.map.
exact (teI val).

Check Vector.of_list.

(* Eval simpl in preTerms_ind isTerm. Nothing interesting. *)

Theorem HAF (q:FSV) (ls: list preTerms) (H: isTerm (FSC q ls))
(t:preTerms) (W: InT _ t ls) : isTerm t.
simpl in * |- *.
Theorem Q (h:Terms)(e :match (Terms_t h) with
|FVC _ => True
|FSC q ls => True
end): isTerm e.  (* HERE THE END *)
preTerms
preTerms_rect


Print ForallT_rect.
unshelve eapply Vector.of_list.

destruct ls; simpl; trivial.


unshelve eapply 
(*Unshelve.
2 : { exact n. } *)

Check (fsI n (List.map (teI val) ls)).

exact (fsI (f (List.map (teI val) ls)).

Definition teI :=
 (fix teI (val : SetVars -> X) (t : Terms) {struct t} : X :=
   match (Terms_t t) with
   | FVC s => val s
   | FSC f t0 => fsI f (List.map (teI val) t0)
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




