(* PUBLIC DOMAIN *)
Require Export Coq.Vectors.Vector.
Require Export Coq.Lists.List.
Require Import Bool.Bool.
Require Import Logic.FunctionalExtensionality.
Require Import Coq.Program.Wf.

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
Inductive Terms : A1Type :=
| FVC :> SetVars -> Terms
| FSC (f:FSV) : (Vector.t Terms (fsv f)) -> Terms.
(*Formulas*)
Inductive Fo :=
|Atom (p:PSV) : (Vector.t Terms (psv p)) ->  Fo
|Bot :Fo
|Conj:Fo->Fo->Fo
|Disj:Fo->Fo->Fo
|Impl:Fo->Fo->Fo
|Fora(x:SetVars)(f:Fo): Fo
|Exis(x:SetVars)(f:Fo): Fo
.
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
          | true => match substF t xi u with
                    | Some q => Some (Fora x q)
                    | None => None
                    end
          | false => None
          end
| false => Some u end).
refine (match (isParamF xi (Fora x u)) with 
| true => match (isParamT x t) with 
          | true => match substF t xi u with
                    | Some q => Some (Exis x q)
                    | None => None
                    end
          | false => None
          end
| false => Some u end).
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

(** Correctness theorem **)
(** for two-valued logic **)
Section cor.
Definition Omega := bool. (* Truth values*)
Context (X:Type).
(*Context (val:SetVars->X).*)
Context (fsI:forall(q:FSV),(Vector.t X (fsv q))->X).
(*Context (prI:forall(q:PSV),(Vector.t X (psv q))->Omega).*)
Context (prI:forall(q:PSV),(Vector.t X (psv q))->Prop).

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

Fixpoint foI (val:SetVars->X) (f:Fo): Prop.
Proof.
destruct f.
+ refine (prI p _).
  apply (@Vector.map Terms X (teI val)).
  exact t.
+ exact False.
+ exact ( and (foI val f1) (foI val f2)).
+ exact (  or (foI val f1) (foI val f2)).
+ exact ( (foI val f1) -> (foI val f2)).
+ exact (forall m:X, foI (cng val x m) f).
+ exact (exists m:X, foI (cng val x m) f).
Defined.

Definition ap {A B}{a0 a1:A} (f:A->B) (h:a0=a1):((f a0)=(f a1))
:= match h in (_ = y) return (f a0 = f y) with
   | eq_refl => eq_refl
   end.

Definition myap {A B}{a0 a1:A} (f:A->B) (h:myeq _ a0 a1):(myeq _ (f a0) (f a1)).
Proof.
destruct h.
constructor.
Show Proof.
Defined.



Lemma equal_a : forall (A B : Type) (f : A -> B) (a0 a1:A),
  (a0 = a1) -> f a0 = f a1.
Proof.
intros A B f a0 a1 r.
destruct r.
reflexivity.
Defined.

(* Measure for terms: the sum of all functional symbols and variables. *)
Definition meas:=
(fix meas (u : Terms) : nat :=
   match u with
   | FVC _ => 1
   | FSC f t0 =>
       @Vector.fold_left nat nat Nat.add 1 (fsv f)
         (@Vector.map Terms nat meas (fsv f) t0) + (fsv f)
   end).
Check Build_FSV 0 1.
Compute (meas (FSC (Build_FSV 0 1) (Vector.cons _ (FVC 0) 0 (Vector.nil _)))).

(*Program *)
Fixpoint qlem1 (t : Terms) (xi : SetVars) (pi : SetVars->X) (u :Terms)
:= match u with 
   | FVC v => FVC (v+1)
   | FSC f H => FSC f (Vector.map (qlem1 t xi pi) H)
   end.


(*(v:SetVars)(f:FSV)(H:t Terms (fsv f))*)
(* lem1  (is not proven yet) *) 
(*
Fixpoint lem1 (t : Terms) (xi : SetVars) (pi : SetVars->X) (u :Terms)
{struct u}
:
(teI pi (substT t xi u))=(teI (cng pi xi (teI pi t)) u).
Proof.
apply Terms_ind.
Check Terms_ind. *)    
Check True.

Theorem myfe :forall (A B : Type) (f g : A -> B), 
(forall x : A, myeq _ (f x) (g x)) -> myeq _ f g.
Proof.
intros.
assert( KK : (forall x : A, f x = g x)).
intro x.
destruct (H x).
reflexivity.

pose(v:=(@functional_extensionality _ _ f g KK)).
destruct (@functional_extensionality _ _ f g KK).
reflexivity.
Defined.


Section Lem1.
Context (t : Terms).

Definition P(xi : SetVars) (pi : SetVars->X) (u :Terms)
:=(teI pi (substT t xi u))=(teI (cng pi xi (teI pi t)) u).

(** 
Local Open Scope vector.**)
Inductive InV {A} (a:A): forall {n}, Vector.t A n -> Type :=
 |In_cons_hd {m} (v: Vector.t A m): InV a (@Vector.cons A a m v)
 |In_cons_tl {m} x (v: Vector.t A m): InV a v -> InV a (@Vector.cons A x m v).

Definition foma := @Vector.fold_left.
(* \u0418\u0437\u043c\u0435\u0440\u0435\u043d\u0438\u0435 - \u043a\u043e\u0434\u0438\u0440\u043e\u0432\u0430\u043d\u0438\u0435 \u0442\u0435\u0440\u043c\u043e\u0432 \u0430\u0440\u0438\u0444\u043c\u0435\u0442\u0438\u0447\u0435\u0441\u043a\u043e\u0435 x,y,z |-> c(x,y,z)*)
(* \u041d\u0430\u0434\u043e \u043f\u0440\u0438\u0434\u0443\u043c\u0430\u0442\u044c wf-\u043e\u0442\u043d\u043e\u0448\u0435\u043d\u0438\u0435 \u043d\u0430 \u0442\u0435\u0440\u043c\u0430\u0445 *)
(* x is less than y if ... *)
Definition rela : forall (x y:Terms), Prop.
Proof.
fix rela 2.
intros x y.
destruct y.
+ exact False.
+ refine (or _ _).
  exact (Vector.In x t0).
  simple refine (@Vector.fold_left Terms Prop _ False (fsv f) t0).
  intros Q e.
  exact (or Q (rela x e)).
Defined.

Definition snglV {A} (a:A) := Vector.cons A a 0 (Vector.nil A).

Definition wfr : @well_founded Terms rela.
Proof.
clear.
unfold well_founded.
assert (H : forall (n:Terms) (a:Terms), (rela a n) -> Acc rela a).
{ fix iHn 1.
  destruct n.
  + simpl. intros a b; destruct b.
  + simpl. intros a Q. destruct Q as [L|R].
    * apply Acc_intro. intros b Hb.
      apply Acc_intro. intros c Hc.
apply (iHn a).


Fixpoint fpt (f : FSV)
(t0 : Vector.t Terms (fsv f))
(b c : Terms)
(Hc : rela c b)
(H : @Vector.In Terms b (fsv f) t0) {struct t0}:
@Vector.fold_left Terms Prop (fun (Q : Prop) (e : Terms) => Q \/ rela c e)
  False (fsv f) t0.
destruct t0 as [|t2].
simpl in * |- *.
inversion H.
simpl in * |- *.
pose (td:= fpt f t0).

+ destruct t0.
simpl in * |- *.
inversion H.
simpl in * |- *.

unfold rela.

unfold rela in Hb. simpl in Hb.


apply (iHn a). exact Hb.
    * apply Acc_intro. intros m Hm. apply (iHn a). exact Hm. 
}
intros a.
simple refine (H _ _ _).
exact (FSC (Build_FSV 0 1) (snglV a)).
simpl.
apply or_introl.
constructor.
Defined.
simpl.
Terms
FSV




constructor.
fix H0 1.
intros z p.
clear.


destruct R.




unfold rela at 1. 
      apply iHn.

simpl.

unfold rela.

exact (H z p).
Defined.
Export VectorNotations.
*)


(*
Program Fixpoint lem1  (xi : SetVars) (pi : SetVars -> X) (u : Terms) 
{wf rela u} :
   teI pi (substT t xi u) = teI (cng pi xi (teI pi t)) u :=
   match
     u as t00 return (teI pi (substT t xi t00) = teI (cng pi xi (teI pi t)) t00)
   with
   | FVC s =>
       let b := Nat.eqb s xi in
       if b as b0
        return
          (teI pi (if b0 then t else s) = (if b0 then teI pi t else pi s))
       then @eq_refl X (teI pi t)
       else @eq_refl X (pi s)
   | FSC f t0 =>
       match
         f as f0
         return
           (forall t1 : Vector.t Terms (fsv f0),
            fsI f0
              (@Vector.map Terms X (teI pi) (fsv f0)
                 (@Vector.map Terms Terms (substT t xi) (fsv f0) t1)) =
            fsI f0
              (@Vector.map Terms X (teI (cng pi xi (teI pi t))) (fsv f0) t1))
       with
       | {| fs := fs0; fsv := fsv0 |} =>
           fun t1 : Vector.t Terms (fsv {| fs := fs0; fsv := fsv0 |}) =>
           @ap (Vector.t X fsv0) X
             (@Vector.map Terms X (teI pi) fsv0
                (@Vector.map Terms Terms (substT t xi) fsv0 t1))
             (@Vector.map Terms X (teI (cng pi xi (teI pi t))) fsv0 t1)
             (fsI {| fs := fs0; fsv := fsv0 |})
             (let g :
                @Vector.map Terms X (teI pi) fsv0
                  (@Vector.map Terms Terms (substT t xi) fsv0 t1) =
                @Vector.map Terms X (fun x : Terms => teI pi (substT t xi x))
                  fsv0 t1 :=
                @vec_comp_as Terms Terms X (teI pi) (substT t xi) fsv0 t1 in
              @eq_ind_r (Vector.t X fsv0)
                (@Vector.map Terms X
                   (fun x : Terms => teI pi (substT t xi x)) fsv0 t1)
                (fun t2 : Vector.t X fsv0 =>
                 t2 =
                 @Vector.map Terms X (teI (cng pi xi (teI pi t))) fsv0 t1)
                (let Y :=
                   fun wm : Terms -> X => @Vector.map Terms X wm fsv0 t1 in
                 let a1 := fun x : Terms => teI pi (substT t xi x) in
                 let a2 := teI (cng pi xi (teI pi t)) in
                 let Y1 := Y a1 in
                 let Y2 := Y a2 in
                 @ap (Terms -> X) (Vector.t X fsv0) a1 a2 Y
                   (@functional_extensionality Terms X
                      (fun x : Terms => teI pi (substT t xi x))
                      (teI (cng pi xi (teI pi t)))
                      (fun x : Terms => lem1 xi pi x)))
                (@Vector.map Terms X (teI pi) fsv0
                   (@Vector.map Terms Terms (substT t xi) fsv0 t1)) g)
       end t0
   end
.
Next Obligation.
unfold meas.
simpl. *)




(*Fixpoint InV (A:Type) (n:nat)(v : Vector.t A n) {struct v}: Type. :=
fix InL (a : A) (l : list A) {struct l} : Type :=
  match l with
  | Datatypes.nil => False
  | b :: m => (sum (b = a) (InL a m))
  end.*)

Check @well_founded Terms rela. 

Definition mea:=
(fix mea (u : Terms) : nat :=
   match u with
   | FVC _ => 1
   | FSC f t0 =>
       @Vector.fold_left nat nat Nat.add 1 (fsv f)
         (@Vector.map Terms nat mea (fsv f) t0)
   end).

Definition ll1 : forall (xi : SetVars) (pi : SetVars->X) (u :Terms),
(forall t:Terms, (mea t < mea u)-> (P xi pi u))->(P xi pi u).


Definition lem1 : forall (u :Terms) (xi : SetVars) (pi : SetVars->X) ,
(teI pi (substT t xi u))=(teI (cng pi xi (teI pi t)) u).
Proof.
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
  simpl.
  apply ap.

(*Theorem AA (a:nat):nat.
elim a;
[> revert a | idtac 1].
elim a;
[> idtac 1 | idtac 1].
destruct a.
(*Unfocus.*)
[> idtac 1 | idtac 1].*)

  simpl in t0.


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

End Lem1.


(* lem1  (is not proven yet) *) 


Fixpoint correct (f:Fo) (l:list Fo) (val:SetVars->X) (m:PR l f) 
(lfi : forall h:Fo, (InL h l)->(foI val h)) {struct m}: foI val f.
Proof.
destruct m.
+ exact (lfi A i).
+ simpl.
  intros a b.
  exact a.
+ simpl.
  intros a b c.
  exact (a c (b c)).
+ destruct (substF t xi ph).
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
Admitted.

End cor.
(* Definition ACK : list Fo := . *)

End VS.


