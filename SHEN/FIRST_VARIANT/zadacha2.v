(* PUBLIC DOMAIN *)
Require Export Coq.Vectors.Vector.
Require Export Coq.Lists.List.
Require Import Bool.Bool.
Require Import Logic.FunctionalExtensionality.
Require Import Coq.Program.Wf.
Require Import Logic.Classical_Prop.
Check classic.

Axiom iff_eq : forall P Q : Prop, (P -> Q) -> (Q -> P) -> P = Q.
Theorem Q (A:Prop) (H:~A): False = (False \/ A).
Proof.
apply iff_eq.
+ intro q ; apply or_introl ; exact q.
+ intro q ; destruct q. assumption. exact (H H0).
Defined.

Theorem Te0 (A:Prop) (H:~A): A = False.
Proof.
apply iff_eq.
+ intro q; exact (H q).
+ intro q; exfalso; exact q.
Defined.

Theorem Te1 (A:Prop) (H:A): A = True.
Proof.
apply iff_eq.
+ constructor.
+ intro q ; assumption.
Defined.

(* AIM 
1) PROVE transitivity
   1.1) DEFINE relation as Type.
*)

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
Inductive Terms : Type :=
| FVC :> SetVars -> Terms
| FSC (f:FSV) : (Vector.t Terms (fsv f)) -> Terms.

Definition rela : forall (x y:Terms), Prop.
Proof.
fix rela 2.
intros x y.
destruct y as [s|f t].
+ exact False.
+ refine (or _ _).
  exact (Vector.In x t).
  simple refine (@Vector.fold_left Terms Prop _ False (fsv f) t).
  intros Q e.
  exact (or Q (rela x e)).
Defined.

(*Definition rela : forall (x y:Terms), Type.
Proof.
fix rela 2.
intros x y.
destruct y as [s|f t].
+ exact False.
+ refine (or _ _).
  exact (Vector.In x t).
  simple refine (@Vector.fold_left Terms Type _ False (fsv f) t).
  intros Q e.
  exact (or Q (rela x e)).
Defined.*)


Definition snglV {A} (a:A) := Vector.cons A a 0 (Vector.nil A).

Fixpoint Tra (a b c:Terms) (Hc : rela c b) (Hb : rela b a) {struct a}: rela c a.
destruct a.
+ simpl in * |- *.
  exact Hb.
+ simpl in * |- *.
  destruct Hb.
  - apply or_intror.
    revert f t H .
    fix RECU 1.
    intros f t H.
    destruct t.
    * simpl in * |- *.
      inversion H.
    * simpl in * |- *.
destruct (classic (rela c h)).
pose (V := Te1 _ H0).
rewrite -> V.
assert (AM: (False \/ True) = True).
 apply iff_eq.
  trivial.
  intros. apply or_intror. trivial.
rewrite -> AM.

Fixpoint LQ (n:nat) (c:Terms) (t : Vector.t Terms n) :
(@Vector.fold_left Terms Prop (fun (Q0 : Prop) (e : Terms) => Q0 \/ rela c e)
  True n t) = True.
Proof.
destruct t.
simpl in * |- *.
+ trivial.
+ simpl in * |- *.
assert (AMT: (True \/ rela c h) = True).
 apply iff_eq.
  trivial.
  firstorder.
rewrite -> AMT.
apply LQ.
Defined.
rewrite -> LQ.
trivial.
rewrite -> (Te0 _ H0).
rewrite <- Q.

apply ( RECU (Build_FSV (fs f) n) t).
simpl. 
admit. (*GOOD!*)
intro q; exact q.
- admit.
Admitted.

(*apply RECU.
firstorder.
destruct (classic (rela c h)).
simpl in * |- *.
Print Vector.In.
      elim H.
destruct (classic (h=b)).
++ destruct H0.
      destruct Hc.

      destruct H.

      elim H.
      intros.
Print Vector.In.


      destruct H.
Check ( RECU f ).
Check (Build_FSV (fs f) m).
Check ( RECU (Build_FSV (fs f) m) v ).
pose (Arg := RECU (Build_FSV (fs f) m) v ).
simpl in Arg.
pose (Arg0 := RECU (Build_FSV (fs f) n) t ).
simpl in Arg.
(*\u0425\u043e\u0447\u0435\u0442\u0441\u044f \u043d\u0430\u043f\u0438\u0441\u0430\u0442\u044c "apply Arg0.", \u043d\u043e \u043d\u0435 \u043f\u043e\u043b\u0443\u0447\u0438\u0442\u0441\u044f:
\u0434\u043e\u043a\u0430\u0436\u0435\u043c \u043b\u0435\u043c\u043c\u0443 \u043f\u0440\u043e \u0444\u043e\u043b\u0434 \u0438 \u0438\u043c\u043f\u043b\u0438\u043a\u0430\u0446\u0438\u044e.*)

(*excluded_middle!*)
destruct (classic (rela c h)). (*Will be replaced later.*)
simpl in * |- *.
Focus 2.
simpl in * |- *.

rewrite <- Q.
apply Arg0.
2 : { exact H. }
simpl in * |- *. (*HERE I DECIDED TO REPLACE PROPS WITH ALGORITHMS 
(COMPUTABLE BOOLEAN FUNCTIONS). FIN. NO, I CHANGED MY MIND.*)
admit.
*)

(*Theorem 
@Vector.fold_left Terms Prop (fun (Q : Prop) (e : Terms) => Q \/ rela c e)
  (False \/ rela c h) n t
->
@Vector.fold_left Terms Prop (fun (Q : Prop) (e : Terms) => Q \/ rela c e)
  (False \/ rela c h) n t
*)

(*
simple refine (iff_eq _ _ _ _).
simple refine  ( RECU (Build_FSV (fs f) m) v _).
Print fsv.
simpl in * |- *.
unfold Vector.In in H. (* Here I start thinking about Type *)

      destruct H.
simpl in * |- *.
Check ( RECU f ). 

elim f; intros.
Check ( RECU f t). 

assert (OU := False -> (False \/ rela c h) ).

assumption.
exact H.
      destruct H.
Focus 2.
    destruct H. fold_left
simpl in * |- *.
     constructor 2.
      assumption.


simpl in * |- *.
    destruct H.
    * apply or_introl.
      constructor 1.


  - apply Tra with b.
    trivial.
    simpl in * |- *.
    destruct H.
    * apply or_introl.
      constructor 1.
    * apply or_introl.
      constructor 2.
      assumption.

  - apply Tra with b.
    trivial.
    simpl in * |- *.
    apply or_intror.
    assumption.
Defined.
    destruct H.
    * apply or_introl.
      constructor 1.
    * apply or_introl.
      constructor 2.
      assumption.
@Vector.In
contructor.
unfold Vector.In.
simpl.
    * apply or_intror.
      simpl in * |- *.
      apply or_intror.
  simpl in * |- *.
Admitted.*)

Check True.
Definition wfr : @well_founded Terms rela.
Proof.
clear.
unfold well_founded.
assert (H : forall (n:Terms) (a:Terms), (rela a n) -> Acc rela a).
{ fix iHn 1.
  destruct n.
  + simpl. intros a b. exfalso. exact b.
  + simpl. intros a Q. destruct Q as [L|R].
    * destruct L.
      (*pose (G:= iHn m).*)
      - apply Acc_intro. intros q Hq.
        apply Acc_intro. intros w Hw.
      (*apply Acc_intro. intros q Hq.*)
        apply (iHn a). apply Tra with q; assumption.
      -
    * apply Acc_intro. intros m Hm.
      apply Acc_intro. intros q Hq.
      apply (iHn a). apply Tra with m; assumption.

(*      simpl in * |- *. 
 exact Hm.

 admit.  (*apply Acc_intro. intros m Hm. apply (iHn a). exact Hm. *)
    * admit.  (* like in /Arith/Wf_nat.v *)*)
}
intros a.
simple refine (H _ _ _).
exact (FSC (Build_FSV 0 1) (snglV a)).
simpl.
apply or_introl.
constructor.
Defined.
