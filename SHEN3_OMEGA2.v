(* PUBLIC DOMAIN *)
(* Author: Georgy Dunaev, georgedunaev@gmail.com *)
Require Export Coq.Vectors.Vector.
Require Export Coq.Lists.List.
Require Import Bool.Bool.
Require Import Logic.FunctionalExtensionality.
Require Import Coq.Program.Wf.
Require Import Lia.
Add LoadPath "/home/user/0my/COQ".
Require Export UNIV_INST.

Require Import Logic.ClassicalFacts.
Axiom EquivThenEqual: prop_extensionality.

Inductive myeq (A : Type) (x : A) : A -> Type :=
| myeq_refl : myeq A x x.


Fixpoint myvec_comp_as {A B C} (f:B->C) (g:A->B) (n:nat) (t0: Vector.t A n) :
myeq _ (Vector.map f (Vector.map g t0))
(Vector.map (fun x=>(f(g x))) t0).
Proof.
destruct t0.
simpl.
reflexivity.
simpl.
rewrite -> myvec_comp_as.
reflexivity.
Defined.

Fixpoint vec_comp_as {A B C} (f:B->C) (g:A->B) (n:nat) (t0: Vector.t A n) :
Vector.map f (Vector.map g t0) =
Vector.map (fun x=>(f(g x))) t0.
Proof.
destruct t0.
simpl.
reflexivity.
simpl.
rewrite -> vec_comp_as.
reflexivity.
Defined.


Module VS.
Section sec0.
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
Check MPSV 0 0.
Notation A1Type:=Set.
Unset Elimination Schemes.
Inductive Terms : A1Type :=
| FVC :> SetVars -> Terms
| FSC (f:FSV) : (Vector.t Terms (fsv f)) -> Terms.
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

Definition Terms_ind (T : Terms -> Prop)
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


(*Formulas*)
(*Unset Elimination Schemes.*)
Inductive Fo :=
|Atom (p:PSV) : (Vector.t Terms (psv p)) ->  Fo
|Bot :Fo
|Conj:Fo->Fo->Fo
|Disj:Fo->Fo->Fo
|Impl:Fo->Fo->Fo
|Fora(x:SetVars)(f:Fo): Fo
|Exis(x:SetVars)(f:Fo): Fo
.
(*Set Elimination Schemes.
Section Fo_rect_section.
Definition Fo_rect (T : Fo -> Type)
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
End Fo_rect_section.*)


(* Substitution *)

Fixpoint substT (t:Terms) (xi: SetVars) (u:Terms): Terms. 
Proof.
destruct u.
2 : { refine (FSC _ _). 
Check @Vector.map.
Check @Vector.map _ _ (substT t xi) _ t0.
exact ( @Vector.map _ _ (substT t xi) _ t0 ). }

{
(*Check my.beq_natP s xi.*)
destruct (PeanoNat.Nat.eqb s xi).
Print bool.
exact t.
exact s. }
(*Show Proof.*)
Defined.


Fixpoint isParamT (xi : SetVars) (t : Terms) {struct t} : bool :=
   match t with
   | FVC s => PeanoNat.Nat.eqb s xi
   | FSC f t0 => Vector.fold_left orb false (Vector.map (isParamT xi) t0)
   end.

Fixpoint isParamF (xi:SetVars) (f:Fo): bool.
Proof.
(*elim f; intros. *)
destruct f.
Show Proof.
Search "Exists".
exact (Vector.fold_left orb false (Vector.map (isParamT xi) t)).
exact false.
Show Proof.
exact (orb (isParamF xi f1) (isParamF xi f2)).
exact (orb (isParamF xi f1) (isParamF xi f2)).
exact (orb (isParamF xi f1) (isParamF xi f2)).
Show Proof.
exact (match (PeanoNat.Nat.eqb x xi) with
       | true => false
       | false => (isParamF xi f)
       end).
exact (match (PeanoNat.Nat.eqb x xi) with
       | true => false
       | false => (isParamF xi f)
       end).
Show Proof.
Defined.

Fixpoint substF (t:Terms) (xi: SetVars) (u : Fo): option Fo. 
Proof.
pose(g := substT t xi).
pose(f := substF t xi).
destruct u.
refine (Some (Atom p _)).
exact (Vector.map g t0).
exact (Some Bot).
 exact (
 match (f u1),(f u2) with
 | Some f0,Some f1 => (Some (Conj f0 f1))
 | _,_ => None
 end).
 exact (
 match (f u1),(f u2) with
 | Some f0,Some f1 => (Some (Disj f0 f1))
 | _,_ => None
 end).
 exact (
 match (f u1),(f u2) with
 | Some f0,Some f1 => (Some (Impl f0 f1))
 | _,_ => None
 end).
(*destruct (isParamF xi (Fora x0 u)).*)
refine (match (isParamF xi (Fora x u)) with 
| true => match (isParamT x t) with 
          | false => match substF t xi u with
                    | Some q => Some (Fora x q)
                    | None => None
                    end
          | true => None
          end
| false => Some (Fora x u) end).
refine (match (isParamF xi (Exis x u)) with 
| true => match (isParamT x t) with 
          | false => match substF t xi u with
                    | Some q => Some (Exis x q)
                    | None => None
                    end
          | true => None
          end
| false => Some (Exis x u) end).
Defined.


Definition Top:Fo := Impl Bot Bot.

Notation " x --> y ":=(Impl x y) (at level 80).
(*
Notation " u '[' t >> xi ] ":=(substT t xi u ) (at level 10).
Set Warnings "-notation-overridden".
Notation " ph [ t | xi ] ":=(substF t xi ph ) (at level 10).
(*Set Warnings "default".*)
Check fun (t:Terms) (x:SetVars) => ( t [ t >> x ]).
Check fun (t:Terms) (x:SetVars) (ph:Fo) => ( ph [ t | x ] ).
*)

Open Scope list_scope.
Print List.In.
Locate "+".
Print sum.
Definition InL { A : Type } :=
fix InL (a : A) (l : list A) {struct l} : Type :=
  match l with
  | Datatypes.nil => False
  | b :: m => (sum (b = a) (InL a m))
  end.

Inductive PR (axi:list Fo) : Fo -> Type :=
| hyp (A : Fo): (InL A axi)-> @PR axi A
| a1 (A B: Fo) : @PR axi (Impl A (Impl B A))
| a2 (A B C: Fo) : @PR axi ((A-->(B-->C))-->((A-->B)-->(A-->C)))
| a12 (ph: Fo) (t:Terms) (xi:SetVars)
: @PR axi (match (substF t xi ph) with 
      | Some q => (Impl (Fora xi ph) q)
      | None => Top
      end)
| b1 (ps ph: Fo) (xi:SetVars) (H:isParamF xi ps = false):
@PR axi (Impl (Fora xi (Impl ps ph)) (Impl ps (Fora xi ph)) )
| MP (A B: Fo) : (@PR axi A)->(@PR axi (Impl A B))->(@PR axi B)
| GEN (A : Fo) (xi:SetVars): (@PR axi A)->(@PR axi (Fora xi A))
.

Check @PR.
Definition AtoA (A:Fo) : PR (List.nil) (A-->A).
Proof.
apply (MP nil (A-->(A-->A)) _).
apply a1.
apply (MP nil (A-->((A-->A)-->A)) _).
apply a1.
apply a2.
Defined.

Definition B1 (ps ph:Fo) (xi:SetVars) (H:isParamF xi ps = false): 
 PR nil (ps --> ph) -> PR nil (ps --> Fora xi ph).
Proof.
intro q.
apply (MP nil (Fora xi (ps --> ph))).
+ apply GEN.
  exact q.
+ apply (b1 _).
  exact H.
Defined.

Definition gen (A:Fo) (xi:SetVars) (*Generalization from Bernay's rule*)
: PR nil (A) -> PR nil (Fora xi A).
Proof.
intro q.
apply (MP nil Top).
unfold Top.
exact (AtoA Bot).
apply (MP nil (Fora xi (Top --> A))).
* apply GEN.
  apply (MP nil A).
  + exact q.
  + apply a1.
* apply b1.
  trivial.
Defined.

Definition neg (f:Fo):= (Impl f Bot).

Definition a1i (A B : Fo)(l : list Fo):(PR l B)->(PR l (Impl A B)).
Proof.
intros x.
apply (MP l B).
exact x.
apply a1.
Defined.

Fixpoint weak (A F:Fo) (l :list Fo) (x: (PR l F)) : (PR (A::l) F).
Proof.
destruct x.
apply hyp.
apply inr. (*or_intror *)
exact i.
apply a1.
apply a2.
apply a12.
apply b1.
assumption.
apply (@MP _ A0).
apply weak.
exact x1.
apply weak.
exact x2.
apply GEN. (* Order is not important! *)
apply weak. (* Order is not important! *)
exact x.
Defined.

Fixpoint weaken (F:Fo) (li l :list Fo) (x: (PR l F)) {struct li}: (PR (li ++ l) F).
Proof.
destruct li.
simpl.
exact x.
simpl.
simple refine (@weak f F (li ++ l) _).
apply weaken.
exact x.
Defined.

(*Export List Notations.*)
Fixpoint notGenWith (xi:SetVars)(l:list Fo)(B:Fo)(m:(PR l B)){struct m}:bool.
Proof.
destruct m. 
exact true.
exact true.
exact true.
exact true.
exact true.
exact (andb (notGenWith xi l _ m1) (notGenWith xi l _ m2)).
exact (andb (negb (PeanoNat.Nat.eqb xi xi0)) (notGenWith xi l _ m) ).
Defined.
Check isParamF.
(*Check fun A B=> forall xi:SetVars, (true = isParamF xi A)->(notGenWith xi m).*)
Fixpoint HA xi : true = PeanoNat.Nat.eqb (xi) (xi).
Proof.
destruct xi.
reflexivity.
simpl.
exact (HA xi).
Defined.

Fixpoint ZX (xi:SetVars) :true = negb (PeanoNat.Nat.eqb xi xi) -> False.
Proof.
intro q.
destruct xi.
compute in q.
inversion q.
rewrite <- HA in q.
inversion q.
Defined.


Theorem lm (a b :bool)(G:true = (a && b) ): true = a.
Proof.
destruct a.
trivial.
inversion G.
Defined.

Theorem lm2 (a b :bool)(G:true = (a && b) ): true = b.
Proof.
destruct a.
trivial.
inversion G.
Defined.

Theorem N (rr:bool): (true=rr \/ rr=false).
Proof.
destruct rr; firstorder.
Defined.

Fixpoint Ded (A B:Fo)(il:list Fo)(m:(PR (cons A il) B)) 
(H:forall xi:SetVars, (true = isParamF xi A)->(true=notGenWith xi _ _ m))
{struct m}:(PR il (A-->B)).
Proof.
destruct m. (*as [i|i|i|i|i|i|i].*)
+ unfold In in i.
  simpl in i .
  destruct i .
  * rewrite <- e.
    pose (J:=weaken _ il nil (AtoA A )).
    rewrite app_nil_r in J.
    exact J.
(*exact (weaken _ il nil (AtoA A )).
apply weak.
exact (AtoA A ).
exfalso.*)
  * simpl in H.
    apply a1i.
    exact (hyp il _ i).
+ apply a1i.
  apply a1.
+ apply a1i.
  apply a2.
+ apply a1i.
  apply a12.
+ apply a1i.
  apply b1.
  trivial.
+ apply (MP _ (A-->A0)).
- simple refine (@Ded _ _ _ _ _).
  exact m1.
  intros xi H0.
  pose (W:=H xi H0).
  simpl in W.
  pose (J:=notGenWith xi (A :: il) A0 m1).
  try reflexivity.
  fold J.
  fold J in W.
  apply (lm _ _ W).
-
apply (MP _ (A-->(A0-->B))).
simple refine (@Ded _ _ _ _ _).
  exact m2.
  intros xi H0.
  pose (W:=H xi H0).
  simpl in W.
  apply (lm2 _ _ W).
(*Last part about GEN*)
apply a2.
+
apply (MP _ (Fora xi (A-->A0))).
apply GEN.
simple refine (@Ded _ _ _ _ _).
  exact m.
  intros xi0 H0.
  pose (W:=H xi0 H0).
  simpl in W.
* exact (lm2 _ _ W).
* simpl.
apply b1.
pose (r := isParamF xi A).
pose (U := H xi).
fold r in U |- *.
simpl in U.

destruct (N r).
pose (C:= lm _ _(U H0)).
exfalso.
exact (ZX _ C).
exact H0.
Show Proof.
Defined.

(*Fixpoint Ded (A B:Fo)(m:(PR (cons A nil) B)) *)

Definition lm3 (a b :bool)(A: true = a)(B: true = b):true = (a && b) 
:=
 (if a as a0 return (true = a0 -> true = a0 && b)
  then
   fun _ : true = true =>
   (if b as b0 return (true = b0 -> true = true && b0)
    then fun _ : true = true => eq_refl
    else fun B0 : true = false => B0) B
  else
   fun A0 : true = false =>
   (if b as b0 return (true = b0 -> true = false && b0)
    then fun _ : true = true => A0
    else fun _ : true = false => A0) B) A.
(*destruct a,b.
reflexivity.
simpl.
exact B.
simpl.
exact A.
simpl.
exact A.
Show Proof.
Defined.*)


Fixpoint forClosed (A B:Fo)(m:(PR (cons A nil) B)):
(forall xi:SetVars, (false = isParamF xi A))
->
(forall xi:SetVars, (true = isParamF xi A)->(true=notGenWith xi _ _ m)).
Proof.
intros H xi Q.
destruct m; simpl; try reflexivity.
+ apply lm3.
  simple refine (@forClosed _ _ _ _ _ _); assumption.
  simple refine (@forClosed _ _ _ _ _ _); assumption.
+ apply lm3.
  2 : simple refine (@forClosed _ _ _ _ _ _); assumption.
  pose (U:=H xi).
  rewrite <- Q in U.
  exfalso.
  inversion U.
Show Proof.
Defined.

Fixpoint SimplDed (A B:Fo) (il: list Fo)(m:(PR (cons A il) B))
(NP:forall xi:SetVars, (false = isParamF xi A)) 
{struct m}:(PR il (A-->B)).
Proof.
simple refine (Ded _ _ _ _ _).
exact m.
intros xi H.
rewrite <- NP in H.
inversion H.
Defined.
End sec0.

Module ModProp.
Definition Omega := Prop.
Definition OFalse := False.
Definition OAnd := and.
Definition OOr := or.
Definition OImp := (fun x y:Omega => x->y).
End ModProp.

Module ModBool.
Definition Omega := bool.
Definition OFalse := false.
Definition OAnd := andb.
Definition OOr := orb.
Definition OImp := implb.
End ModBool.

(* Here we choose an interpretation. *)
(*Export ModBool.*)
Export ModProp. (* + classical axioms *)

(** Correctness theorem **)
(** for two-valued logic **)
Section cor.
 (* Truth values*)
Context (X:Type).
(*Context (val:SetVars->X).*)
Context (fsI:forall(q:FSV),(Vector.t X (fsv q))->X).
Context (prI:forall(q:PSV),(Vector.t X (psv q))->Omega).
(*Context (prI:forall(q:PSV),(Vector.t X (psv q))->Prop).*)

Fixpoint teI (val:SetVars->X) (t:Terms): X.
Proof.
destruct t.
exact (val s).
refine (fsI f _).
simple refine (@Vector.map _ _ _ _ _).
2 : apply teI.
exact val.
exact t.
Show Proof.
Defined.
(*
Fixpoint foI (val:SetVars->X) (f:Fo): Omega.
Proof.
destruct f.
+ refine (prI p _).
  apply (Vector.map  (teI val)).
  exact t.
+ exact false.
+ exact ( andb (foI val f1) (foI val f2)).
+ exact (  orb (foI val f1) (foI val f2)).
+ exact (implb (foI val f1) (foI val f2)).
+  (*Infinite conjunction!!!*)
 Show Proof.
*)

(** (\pi + (\xi \mapsto ?) ) **)
Definition cng (val:SetVars -> X) (xi:SetVars) (m:X) :=
(fun r:SetVars =>
match Nat.eqb r xi with
| true => m
| false => (val r)
end).

(*Inductive foI (val:SetVars->X) (f:Fo): Prop
:=
   | cAtom p t0 => ?Goal0@{t:=t0}
.
   | cBot => ?Goal
   | cConj f1 f2 => ?Goal1
   | cDisj f1 f2 => ?Goal2
   | cImpl f1 f2 => ?Goal3
   | cFora x f0 => ?Goal4@{f:=f0}
   | cExis x f0 => ?Goal5@{f:=f0}
.*)

Fixpoint foI (val:SetVars->X) (f:Fo): Omega.
Proof.
destruct f.
Show Proof.
+ refine (prI p _).
  apply (@Vector.map Terms X (teI val)).
  exact t.
+ exact OFalse.
+ exact ( OAnd (foI val f1) (foI val f2)).
+ exact (  OOr (foI val f1) (foI val f2)).
+ exact ( OImp (foI val f1) (foI val f2)).
Show Proof.
+ exact (forall m:X, foI (cng val x m) f).
(*forall m:X, foI (fun r:SetVars =>
match Nat.eqb r x with
| true => m
| false => (val r)
end
) f*)
+ exact (exists m:X, foI (fun r:SetVars =>
match Nat.eqb r x with
| true => m
| false => (val r)
end
) f
).
Defined.

Definition ap {A B}{a0 a1:A} (f:A->B) (h:a0=a1):((f a0)=(f a1))
:= match h in (_ = y) return (f a0 = f y) with
   | eq_refl => eq_refl
   end.


Section Lem1.
(*Context (t : Terms).*)

(* page 136 of the book *)
Definition lem1 (t : Terms) : forall (u :Terms) (xi : SetVars) (pi : SetVars->X) ,
(teI pi (substT t xi u))=(teI (cng pi xi (teI pi t)) u).
Proof.
fix lem1 1.
intros.
induction u as [s|f].
(*destruct u as [s|f] .*)
+ simpl.
  unfold cng.
  destruct (Nat.eqb s xi) eqn:ek. (* fsI as [H1|H2].*)
  * reflexivity.
  * simpl.
    reflexivity.
Show Proof.
+
  simpl. (* fsI teI *)
  destruct f.
  simpl.
  apply ap.
 simpl in * |- *.
apply (*Check *)
(proj1 (
eq_nth_iff X fsv0 
(Vector.map (teI pi) (Vector.map (substT t xi) v))
(Vector.map (teI (cng pi xi (teI pi t))) v)
)).
intros.
(*rewrite H0.*)
 simpl in * |- *.
(* now I need to show that .nth and .map commute *)
Check nth_map (teI pi) (Vector.map (substT t xi) v) p1 p2 H0.
rewrite -> (nth_map (teI pi) (Vector.map (substT t xi) v) p1 p2 H0).
Check nth_map (teI (cng pi xi (teI pi t))) v.
rewrite -> (nth_map (teI (cng pi xi (teI pi t))) v p2 p2 ).
Check nth_map (substT t xi) v p2 p2 eq_refl.
rewrite -> (nth_map (substT t xi) v p2 p2 eq_refl).
exact (H p2).
reflexivity.
Defined.

(*Theorem additi pi xi n (v:Vector.t _ n) :
Vector.map (teI pi) (Vector.map (substT t xi) v) =
Vector.map (teI (cng pi xi (teI pi t))) v.
apply (*Check *)
(proj1 (
eq_nth_iff X fsv0 
(Vector.map (teI pi) (Vector.map (substT t xi) v))
(Vector.map (teI (cng pi xi (teI pi t))) v)
)).
intros.
(*rewrite H0.*)
 simpl in * |- *.
(* now I need to show that .nth and .map commute *)
Check nth_map (teI pi) (Vector.map (substT t xi) v) p1 p2 H0.
rewrite -> (nth_map (teI pi) (Vector.map (substT t xi) v) p1 p2 H0).
Check nth_map (teI (cng pi xi (teI pi t))) v.
rewrite -> (nth_map (teI (cng pi xi (teI pi t))) v p2 p2 ).
Check nth_map (substT t xi) v p2 p2 eq_refl.
rewrite -> (nth_map (substT t xi) v p2 p2 eq_refl).
exact (H p2).
reflexivity.*)

End Lem1.

Theorem SomeInj {foo} :forall (a b : foo), Some a = Some b -> a = b.
Proof.
  intros a b H.
  inversion H.
  reflexivity.
Defined.

Theorem eq_equ (A B:Prop) : A=B -> (A <-> B).
Proof.
intro p. 
destruct p.
firstorder.
Defined. (* rewrite p. firstorder. *)

Theorem conj_eq (A0 B0 A1 B1:Prop)(pA:A0=A1)(pB:B0=B1): (A0 /\ B0) = (A1 /\ B1).
Proof. destruct pA, pB; reflexivity. Defined.
Theorem disj_eq (A0 B0 A1 B1:Prop)(pA:A0=A1)(pB:B0=B1): (A0 \/ B0) = (A1 \/ B1).
Proof. destruct pA, pB; reflexivity. Defined.
Theorem impl_eq (A0 B0 A1 B1:Prop)(pA:A0=A1)(pB:B0=B1): (A0 -> B0) = (A1 -> B1).
Proof. destruct pA, pB; reflexivity. Defined.
Lemma dbl_cng pi xi m1 m2: forall q,(cng (cng pi xi m1) xi m2) q = (cng pi xi m2) q.
Proof. intro q. unfold cng. destruct (Nat.eqb q xi); reflexivity. Defined.


Theorem l01 h n v :
Vector.fold_left orb false (Vector.cons bool h n v) = Vector.fold_left orb (orb false h) v.
Proof.
simpl. reflexivity.
Defined.
(*Fixpoint {struct v}*)
(*fold_left orb true v*)
(*Lemma l00 h n v :  Vector.fold_left orb false (Vector.cons bool h n v) = false
-> (h=false).
intros.
destruct h eqn:y.
simpl in * |- *.
simpl.
auto. *)

(** NOW SEE seq_of_bool.v **)
Check all_then_someV.
(*Lemma all_then_some (A:Type)(n:nat)(p:Fin.t (n)) (v:Vector.t bool (n))
(H : Vector.fold_left orb false v = false)
 : (Vector.nth v p) = false.
Proof.
induction v.
inversion p.
rewrite -> l01 in H.
destruct h.
admit.
simpl in H.
(*pose (G:= IHv (@Fin.F1 n) H).
simpl.
destruct p.*)
Abort.*)

Lemma all_then_someP (A:Type)(n:nat)(p:Fin.t (n)) (v:Vector.t A (n)) (P:A->bool)
(H : Vector.fold_left orb false (Vector.map P v) = false)
 : (P (Vector.nth v p)) = false.
Proof.
Check nth_map P v p p eq_refl.
rewrite <- (nth_map P v p p eq_refl).
apply all_then_someV. trivial.
Defined.

(* Not a parameter then not changed afted substitution (for Terms) *)
Lemma NPthenNCAST (u:Terms)(xi:SetVars)(t:Terms) (H:(isParamT xi u=false))
: (substT t xi u) = u.
Proof. induction u.
+ simpl in * |- *.
  rewrite H. reflexivity.
+ simpl in * |- *.
  apply ap.
apply eq_nth_iff.
intros p1 p2 ppe.
Check nth_map _ _ _ p2 ppe.
rewrite (nth_map _ _ _ p2 ppe).
apply H0.
simpl.
apply all_then_someP.
trivial.
Defined.

Lemma NPthenNCAST_vec:forall p xi t ts (H:(isParamF xi (Atom p ts)=false)), 
  (Vector.map (substT t xi) ts) = ts.
Proof.
  intros p xi t1 ts H.
  apply eq_nth_iff.
  intros p1 p2 H0.
  Check nth_map (substT t1 xi) ts p1 p2 H0.
  rewrite -> (nth_map (substT t1 xi) ts p1 p2 H0).
  apply NPthenNCAST.
  apply all_then_someP.
  simpl in H.
  exact H.
Defined.


(* Not a parameter then not changed afted substitution (for Formulas) *)
Fixpoint NPthenNCASF (mu:Fo) : forall (xi:SetVars)(t:Terms) (H:(isParamF xi mu=false))
   , substF t xi mu = Some mu .
Proof. (*induction mu eqn:u0.*)
destruct mu eqn:u0.
Check t.
* intros xi t0 H.
  simpl.
  rewrite -> NPthenNCAST_vec; (trivial || assumption).
* intros xi t H.
  simpl; trivial.
* intros xi t H.
  simpl.
  simpl in H.
  (*pose (Q:=A1 _ _ H).*)
  destruct (A1 _ _ H) as [H0 H1].
  rewrite -> NPthenNCASF .
  rewrite -> NPthenNCASF .
  (*rewrite -> IHf1 with xi t.
  rewrite -> IHf2 with xi t.*)
  trivial.
  trivial.
  trivial.
* simpl.
  intros xi t H.
  destruct (A1 _ _ H) as [H0 H1].
  rewrite -> NPthenNCASF .
  rewrite -> NPthenNCASF .
  (*rewrite -> IHmu1 with xi t.
  rewrite -> IHmu2 with xi t.*)
  trivial.
  trivial.
  trivial.
* simpl.
  intros xi t H.
  destruct (A1 _ _ H) as [H0 H1].
  rewrite -> NPthenNCASF .
  rewrite -> NPthenNCASF .
  trivial.
  trivial.
  trivial.
* simpl.
  intros xi t H.
  destruct (PeanoNat.Nat.eqb x xi) eqn:u2.
  trivial.
  destruct (isParamF xi f) eqn:u1.
  inversion H.
  trivial.
* simpl.
  intros xi t H.
  destruct (PeanoNat.Nat.eqb x xi) eqn:u2.
  trivial.
  destruct (isParamF xi f) eqn:u1.
  inversion H.
  trivial.
Defined.

(* p.137 *)
Section Lem2.
Definition lem2 : forall (t : Terms) (fi : Fo) (xi : SetVars) (pi : SetVars->X),
option_map (foI pi ) (substF t xi fi) = Some (foI (cng pi xi (teI pi t)) fi).
Proof.
fix lem2 1. intros.
destruct (substF t xi fi).
2 : { simpl.
Abort.

Definition lem2 : forall (t : Terms) (fi : Fo) (xi : SetVars) (pi : SetVars->X),
match (substF t xi fi) with 
| Some r => (foI pi r)=(foI (cng pi xi (teI pi t)) fi)
| None => True
end.
Proof. fix lem2 1. intros. destruct (substF t xi fi). 2 : exact I.
destruct f eqn:u0.
simpl in * |- *.
Fail  apply 
    (proj1 (
      eq_nth_iff X (psv p) 
      (Vector.map (teI pi) (Vector.map (substT t xi) t0))
      (Vector.map (teI (cng pi xi (teI pi t))) t0)
    )).
Abort.
Lemma mqd x t pi m (H:isParamT x t = false): (teI (cng pi x m) t) = (teI pi t).
Proof.
induction t.
 simpl.
simpl in H.
unfold cng.
rewrite -> H.
reflexivity.
 simpl.
simpl in H.
apply ap.
apply eq_nth_iff.
intros.
Check nth_map (teI (cng pi x m)) v p1 p1 eq_refl.
rewrite -> (nth_map (teI (cng pi x m)) v p1 p1 eq_refl).
rewrite -> (nth_map (teI pi) v p2 p2 eq_refl).
rewrite <- H1.
apply H0.
exact (all_then_someP _ _ p1 _ (isParamT x) H).
Defined.

Lemma IOF xi : PeanoNat.Nat.eqb xi xi = true.
induction xi.
simpl. trivial.
simpl. exact IHxi.
Defined.

Lemma cng_commT  x xi m0 m1 pi t :
PeanoNat.Nat.eqb x xi = false -> 
teI (cng (cng pi x m0) xi m1) t = teI (cng (cng pi xi m1) x m0) t.
Proof. intro i.
revert pi.
induction t; intro pi.
simpl.
unfold cng.
(*destruct (Nat.eqb x xi) eqn:j.
inversion i. NO*)
Check not_iff_compat (PeanoNat.Nat.eqb_eq x xi).
pose (n3:= proj1 (not_iff_compat (PeanoNat.Nat.eqb_eq x xi)) ).
Check proj2 (not_true_iff_false (PeanoNat.Nat.eqb x xi)).
pose (n4:= n3 (proj2 (not_true_iff_false (PeanoNat.Nat.eqb x xi)) i)).
Require Import Arith.Peano_dec.
Check eq_nat_dec.
destruct (PeanoNat.Nat.eq_dec sv xi).
rewrite -> e.
rewrite -> IOF.
destruct (PeanoNat.Nat.eq_dec x xi).
destruct (n4 e0).
pose (hi := (not_eq_sym n)).

Check not_true_iff_false .
pose (ih:= not_true_is_false _ (proj2 (not_iff_compat (PeanoNat.Nat.eqb_eq xi x)) hi)).
rewrite ih.
reflexivity.
pose (ih:= not_true_is_false _ (proj2 (not_iff_compat (PeanoNat.Nat.eqb_eq sv xi)) n)).
rewrite -> ih.
reflexivity.
simpl.
apply ap.
apply eq_nth_iff.
intros p1 p2 HU.

Check nth_map (teI (cng (cng pi x m0) xi m1)) v p1 p2 HU.
rewrite -> (nth_map (teI (cng (cng pi x m0) xi m1)) v p1 p2 HU).
Check nth_map.
rewrite -> (nth_map (teI (cng (cng pi xi m1) x m0)) v p2 p2 eq_refl).
apply H.
Defined.

Lemma cng_commF  xe xi m0 m1 pi fi :
PeanoNat.Nat.eqb xe xi = false -> 
foI (cng (cng pi xe m0) xi m1) fi = foI (cng (cng pi xi m1) xe m0) fi.
Proof. intro i. revert pi m0 m1 xe xi i.
induction fi; intros pi m0 m1 xe xi i.
+ simpl.
  apply ap.
  apply eq_nth_iff.
  intros p1 p2 HU.
  rewrite -> (nth_map (teI (cng (cng pi xe m0) xi m1)) t p1 p2 HU).
  rewrite -> (nth_map (teI (cng (cng pi xi m1) xe m0)) t p2 p2 eq_refl).
  apply cng_commT.
  exact i.
+ simpl. reflexivity.
+ simpl. rewrite -> IHfi1.  rewrite -> IHfi2. reflexivity. exact i. exact i.
+ simpl. rewrite -> IHfi1.  rewrite -> IHfi2. reflexivity.  exact i. exact i.
+ simpl. rewrite -> IHfi1.  rewrite -> IHfi2. reflexivity. exact i. exact i.
+ simpl. apply EquivThenEqual. split. intros.

 Check IHfi (cng pi xi m1) m0 m xe xi i.
 (*
 rewrite 
 rewrite <- IHfi.  rewrite -> IHfi2. reflexivity.
 reflexivity.
 *)
 
Abort. (* TODO replace cng_commEXT with cng_commF and cng_commT *)

Lemma cng_commEXT  x xi m0 m1 pi :
PeanoNat.Nat.eqb x xi = false -> 
(cng (cng pi x m0) xi m1) = (cng (cng pi xi m1) x m0). 
Proof. intro i.
apply functional_extensionality.
intro b.
unfold cng.
destruct (Nat.eqb b xi) eqn:e1, (Nat.eqb b x) eqn:e2.
rewrite -> (proj1 (PeanoNat.Nat.eqb_eq b x) e2) in e1.
rewrite e1 in i.
inversion i.
reflexivity.
reflexivity.
reflexivity.
Defined.



Context (t : Terms).
Definition lem2 : forall (fi : Fo) (xi : SetVars) (pi : SetVars->X)
(r:Fo) (H:(substF t xi fi) = Some r), (*(SH:sig (fun(r:Fo)=>(substF t xi fi) = Some r)),*)
(foI pi r)=(foI (cng pi xi (teI pi t)) fi).
Proof.
fix lem2 1.
intros fi xi pi.
(*destruct (substF t xi fi) eqn: j.*)
(**)
induction fi.
+  simpl in *|-*; intros r H.
  pose (Q:=SomeInj _ _ H).
  rewrite <- Q.
  simpl.
  (*apply eq_equ.*)
  apply ap.
  apply 
    (proj1 (
      eq_nth_iff X (psv p) 
      (Vector.map (teI pi) (Vector.map (substT t xi) t0))
      (Vector.map (teI (cng pi xi (teI pi t))) t0)
    )).
  rename t0 into v.
  intros p1 p2 H0.
  rewrite -> (nth_map (teI pi) (Vector.map (substT t xi) v) p1 p2 H0).
  rewrite -> (nth_map (teI (cng pi xi (teI pi t))) v p2 p2 ).
  rewrite -> (nth_map (substT t xi) v p2 p2 eq_refl).
  apply lem1. reflexivity.
+  simpl in *|-*; intros r H.
   inversion H. trivial.
+  simpl in *|-*; intros r H.
  destruct (substF t xi fi1) as [f1|].
  destruct (substF t xi fi2) as [f2|].
  pose (Q:=SomeInj _ _ H).
  rewrite <- Q.
  apply conj_eq ;   fold foI.
  simpl in * |- *.
  * apply (IHfi1 f1 eq_refl).
  * apply (IHfi2 f2 eq_refl).
  * inversion H.
  * inversion H.
+ simpl in *|-*; intros r H.
  destruct (substF t xi fi1) as [f1|].
  destruct (substF t xi fi2) as [f2|].
  pose (Q:=SomeInj _ _ H).
  rewrite <- Q.
  simpl in * |- *.
  apply disj_eq ;   fold foI.
  * apply (IHfi1 f1 eq_refl).
  * apply (IHfi2 f2 eq_refl).
  * inversion H.
  * inversion H.
+ simpl in *|-*; intros r H.
  destruct (substF t xi fi1) as [f1|].
  destruct (substF t xi fi2) as [f2|].
  pose (Q:=SomeInj _ _ H).
  rewrite <- Q.
  simpl in * |- *.
  apply impl_eq ;   fold foI.
  * apply (IHfi1 f1 eq_refl).
  * apply (IHfi2 f2 eq_refl).
  * inversion H.
  * inversion H.
+ intros r H.
  (*simpl in * |- *.
  destruct (PeanoNat.Nat.eqb x xi) eqn:j0.
  * destruct (isParamF xi (Fora x fi) ) eqn:tuc.
    - 
  simpl.*)
 destruct (isParamF xi (Fora x fi) ) eqn:tuc.
2 : { 
Check NPthenNCASF.
rewrite NPthenNCASF in H.
 pose (Q:=SomeInj _ _ H).
rewrite <- Q.
apply lem2.
pose (J:=(PeanoNat.Nat.eqb x xi)).
simpl.
simpl in tuc.
destruct (PeanoNat.Nat.eqb x xi) (*as [J0|J1]*).
reflexivity.
destruct (isParamF xi fi).
inversion tuc.
reflexivity.
assumption.
}
simpl in tuc.
simpl in H.
destruct (PeanoNat.Nat.eqb x xi) eqn:k1.
inversion tuc.
rewrite tuc in H.
destruct (isParamT x t) eqn:k2.
inversion H.
destruct (substF t xi fi) eqn:k3.
2 : inversion H.
pose(Q:=SomeInj _ _ H).
rewrite <- Q.
simpl in *|-*.
assert (AS0 : exists ro:Fo, (substF t xi fi) = Some ro).
 exists f.
 exact k3. clear AS0.
apply EquivThenEqual.
split.
intros.
pose (K:=H0 m).
rewrite -> lem2 with (fi:=fi) (xi:=xi) in K .
2 : exact k3.
rewrite -> mqd in K.
2 : exact k2. (* x and xi are different so they are interchangeable *)
simpl.
rewrite cng_commEXT in K.
exact K.
exact k1.

intros.
pose (K:=H0 m).
rewrite cng_commEXT in K.

rewrite <- mqd with (x:=x) (t:=t)(m:=m) in K.

Check lem2 fi xi (cng pi x m) f k3.
rewrite <- lem2 with (fi:=fi) (xi:=xi) (r:=f) in K .
exact K.
exact k3.
exact k2.
Check reflect.

destruct (PeanoNat.Nat.eq_dec x xi) eqn:w.
rewrite e in k1.
Check not_iff_compat.
Check PeanoNat.Nat.eqb_eq x xi.
Check not_iff_compat (PeanoNat.Nat.eqb_eq x xi).
rewrite -> (IOF xi) in k1.
inversion k1.
pose (n2:= not_eq_sym n).
Check not_iff_compat (PeanoNat.Nat.eqb_eq x xi).
pose (n3:= proj2 (not_iff_compat (PeanoNat.Nat.eqb_eq xi x)) n2).
apply not_true_is_false.
exact n3.
(* FORALL case is proved but with funext! *)
+ intros r H.
  (*simpl in * |- *.
  destruct (PeanoNat.Nat.eqb x xi) eqn:j0.
  * destruct (isParamF xi (Fora x fi) ) eqn:tuc.
    - 
  simpl.*)
 destruct (isParamF xi (Fora x fi) ) eqn:tuc.
2 : { 
Check NPthenNCASF.
rewrite NPthenNCASF in H.
 pose (Q:=SomeInj _ _ H).
rewrite <- Q.
apply lem2.
pose (J:=(PeanoNat.Nat.eqb x xi)).
simpl.
simpl in tuc.
destruct (PeanoNat.Nat.eqb x xi) (*as [J0|J1]*).
reflexivity.
destruct (isParamF xi fi).
inversion tuc.
reflexivity.
assumption.
}
simpl in tuc.
simpl in H.
destruct (PeanoNat.Nat.eqb x xi) eqn:k1.
inversion tuc.
rewrite tuc in H.
destruct (isParamT x t) eqn:k2.
inversion H.
destruct (substF t xi fi) eqn:k3.
2 : inversion H.
pose(Q:=SomeInj _ _ H).
rewrite <- Q.
simpl in *|-*.
assert (AS0 : exists ro:Fo, (substF t xi fi) = Some ro).
 exists f.
 exact k3. clear AS0.
apply EquivThenEqual.
split.
intros.
destruct H0 as [m K].
(*pose (K:=H0 m).*)
rewrite -> lem2 with (fi:=fi) (xi:=xi) in K .
2 : exact k3.
(* TODO: adapt this part from FORALL case to EXISTS case.
rewrite -> mqd in K.
2 : exact k2. (* x and xi are different so they are interchangeable *)
simpl.
rewrite cng_commEXT in K.
exact K.
exact k1.

intros.
pose (K:=H0 m).
rewrite cng_commEXT in K.

rewrite <- mqd with (x:=x) (t:=t)(m:=m) in K.

Check lem2 fi xi (cng pi x m) f k3.
rewrite <- lem2 with (fi:=fi) (xi:=xi) (r:=f) in K .
exact K.
exact k3.
exact k2.
Check reflect.

destruct (PeanoNat.Nat.eq_dec x xi) eqn:w.
rewrite e in k1.
Check not_iff_compat.
Check PeanoNat.Nat.eqb_eq x xi.
Check not_iff_compat (PeanoNat.Nat.eqb_eq x xi).
rewrite -> (IOF xi) in k1.
inversion k1.
pose (n2:= not_eq_sym n).
Check not_iff_compat (PeanoNat.Nat.eqb_eq x xi).
pose (n3:= proj2 (not_iff_compat (PeanoNat.Nat.eqb_eq xi x)) n2).
apply not_true_is_false.
exact n3.
(* EXISTS case is proved but with funext! *)
Defined.*)
Admitted.

auto with arith.
compute in k1.
Check PeanoNat.Nat.compare_eq_iff.
Print Eq.
simpl in k1.
inversion k1.
simpl in H2.
inversion H2.
destruct (PeanoNat.Nat.eqb xi x) eqn: s.

assert (ASSE: reflect (x=xi) (PeanoNat.Nat.eqb x xi)).
admit.
destruct ASSE eqn:j.
inversion k1.
Check reflect_iff _ _ ASSE.
admit.
(*rewrite e in .
Check iff_reflect.
Check eqb_eq _ _ k1.
exact k1.*)

+ admit.
Admitted.

simpl in K.
rewrite -> lem2 with (fi:=fi) (xi:=xi) in K .
2 : exact k3.
rewrite -> mqd in K.
2 : exact k2. (* x and xi are different so they are interchangeable *)
simpl.
rewrite cng_commEXT in K.
exact K.
exact k1.

(**** HERE IS THE DEVELOPMENT ****)


simpl.
Check functional_extensionality.

exact K.
Abort.
End Lem2. (*temporary*)


Check equal_f.


(* rewrite IHfi in H0. ne pomozhet *)
assert (AS1 : 
simpl in *|-*.
(*
Abort.
End Lem2. (*temporary*)
Fixpoint lmi t xi x psi r : substF t xi (Fora x psi) = Some r -> 
        exists ro:Fo, (substF t xi psi) = Some ro.
Proof.
intros H.
simpl in H.
destruct (PeanoNat.Nat.eqb x xi) eqn:k1.
destruct r eqn:ln.
inversion H.
inversion H.
inversion H.
inversion H.
inversion H.
exists psi.
reflexivity.

simpl in *|-*.
simpl .

(SomeInj _ _ H).
simpl in *|-*.

(*unfold substF in H.*)
(*cbv delta in H.*)
simpl in H.
destruct (substF t xi (Fora x psi)) eqn:k2.


pose(Y:=(substF t xi (Fora x psi))).
destruct (substF t xi (psi)) eqn:k0.
exists f0.
reflexivity.
simpl in k2, Y.
destruct (PeanoNat.Nat.eqb x xi) eqn:k1.
induction r.
inversion H.
inversion H.
inversion H.
inversion H.
inversion H.

*)

fold substF in H.
induction (substF t xi (psi)) eqn:e1.
exists a; reflexivity.
induction (substF t xi (Fora x psi)) eqn:e1.


simpl in *|-*.
destruct (PeanoNat.Nat.eqb x xi) eqn:k1.
inversion tuc.
destruct (isParamF xi fi) eqn:k2.
destruct (isParamT x t) eqn:k3.
inversion H.
destruct (substF t xi fi) eqn:k4.
simpl in *|-*.
pose(Q:=SomeInj _ _ H).
rewrite <- Q.
simpl in *|-*.
(*p.137.*)
assert (AS0 : exists ro:Fo, (substF t xi f) = Some ro).
 
apply EquivThenEqual.
split.
intros.
assert (U : forall m :X, (foI (cng pi x m) f) = (foI (cng (cng pi xi (teI pi t)) x m) fi)).
intro m.

admit.
rewrite U.
apply ap.


ENDENDENDENDENDENDENDENDENDENDENDENDENDENDENDENDENDENDENDENDENDEND

apply IHfi.
symmetry.
simpl.
rewrite <- IHfi.

HJJHJHJH

simpl.
destruct (PeanoNat.Nat.eqb x xi) eqn:xxi.
admit.
admit.
admit.
  simpl in *|-*.
 
  pose (Q:=SomeInj _ _ H).
  pose (E:=proj1 (@PeanoNat.Nat.eqb_eq x xi) xxi).
  rewrite -> E.
  rewrite <- Q.
  simpl in * |- *.
Check fun m=>(cng (cng pi xi (teI pi t)) xi m).
Check fun m1 m2 =>(functional_extensionality _ _ (dbl_cng pi xi m1 m2)).
(*rewrite -> (fun m=> (dbl_cng  pi xi (teI pi t) m)) .*)
 (*to be continued... *)
  *
(*rewrite -> IHfi.*)
(*destruct fi; simpl.*)
  admit.
  * destruct (isParamF xi fi) eqn: yu.
    destruct (isParamT x t) eqn: os.
simpl.
Abort.
(*
Vector.map (teI pi) (Vector.map (substT t xi) v) =
Vector.map (teI (cng pi xi (teI pi t))) v
*)
End Lem2.

(* lem2  is not proven yet! *) 


Fixpoint correct (f:Fo) (l:list Fo) (val:SetVars->X) (m:PR l f) 
(lfi : forall h:Fo, (InL h l)->(foI val h)) {struct m}: foI val f.
Proof.
destruct m (* eqn: meq *).
+ exact (lfi A i).
+ simpl.
  intros a b.
  exact a.
+ simpl.
  intros a b c.
  exact (a c (b c)).
+ destruct (substF t xi ph) eqn: j.
  2 : {simpl. trivial. }
  apply (correct _ l).
  2 : {assumption. }
  simpl.
pose (Z:=(@Ded (Fora xi ph) f l )).
simple refine (Z _ _ ).
(*
  pose (W:= lfi f).
  destruct (Nat.eqb r xi).
  simpl in H.
  exact H.
  unfold foI. 
  simpl.
*)
Abort.

End cor.
(* Definition ACK : list Fo := . *)

End VS.

(*Theorem AA (a:nat):nat.
elim a;
[> revert a | idtac 1].
elim a;
[> idtac 1 | idtac 1].
destruct a.
(*Unfocus.*)
[> idtac 1 | idtac 1].*)



