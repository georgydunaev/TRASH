Require Export Coq.Vectors.Vector.
Require Export Coq.Lists.List.
Require Import Bool.Bool.
Require Import Logic.FunctionalExtensionality.
Require Import Coq.Program.Wf.

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

Unset Elimination Schemes.
Inductive Terms : Type :=
| FVC :> SetVars -> Terms
| FSC (f:FSV) : (Vector.t Terms (fsv f)) -> Terms.
Set Elimination Schemes.
(*
Print Terms_rect.
: forall P : Terms -> Type,
       (forall s : SetVars, P s) ->
       (forall (f0 : FSV) (t : t Terms (fsv f0)), P (FSC f0 t)) ->
       forall t : Terms, P t
Definition Terms_rect (T : Terms -> Type)
                      (H_FVC : forall sv, T (FVC sv))
                      (H_FSC : forall f v, (forall n, T (Vector.nth v n)) -> T (FSC f v)).
*)

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

Require Import Lia.

Definition wfr : @well_founded Terms rela.
Proof.
apply (Wf_nat.well_founded_lt_compat _ height).
intros t1 t2. induction t2 as [sv2|f2 v2 IH]; simpl; try easy.
intros [t_v|t_sub]; apply Lt.le_lt_n_Sm.
{ clear IH. induction t_v; simpl; lia. }
revert v2 IH t_sub; generalize (fsv f2); clear f2.
intros k v2 IH t_sub.
enough (H : exists n, rela t1 (Vector.nth v2 n)).
{ destruct H as [n H]. apply IH in H. clear IH t_sub.
  transitivity (height (Vector.nth v2 n)); try lia; clear H.
  induction v2 as [|t2 m v2 IHv2].
  - inversion n.
  - apply (Fin.caseS' n); clear n; simpl; try lia.
    intros n. specialize (IHv2 n). lia. }
clear IH.
assert (H : Vector.fold_right (fun t Q => Q \/ rela t1 t) v2 False).
{ revert t_sub; generalize False.
  induction v2 as [|t2 n v2]; simpl in *; trivial.
  intros P H; specialize (IHv2 _ H); clear H.
  induction v2 as [|t2' n v2 IHv2']; simpl in *; tauto. }
clear t_sub.
induction v2 as [|t2 k v2 IH]; simpl in *; try easy.
destruct H as [H|H].
- apply IH in H.
  destruct H as [n Hn].
  now exists (Fin.FS n).
- now exists Fin.F1.
Defined.
Qed.
