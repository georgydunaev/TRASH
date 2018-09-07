Require Export Coq.Lists.List.

Section ExistsT_ForallT.
  Variable A:Type.

  Section One_predicateT.

    Variable P:A->Type.

    Inductive ForallT : list A -> Type :=
      | Forall_nil : ForallT nil
      | Forall_cons : forall x l, P x -> ForallT l -> ForallT (x::l).

    Hint Constructors ForallT.
Print List.In.
Definition  InT (A : Type) :=
fix InT (a : A) (l : list A) {struct l} : Type :=
  match l with
  | nil => False
  | b :: m => (sum (b = a <: Type) (InT a m))
  end.

    Lemma Forall_forallT (l:list A):
      (ForallT l -> (forall x, InT A x l -> P x)) *
      ((forall x, InT A x l -> P x) -> ForallT l) .
    Proof.
      split.
      - induction 1.
        + firstorder.
        + firstorder. subst. auto.
      - induction l; firstorder.
        constructor 2.
        eapply X.
         simpl.
         eapply inl.
         trivial.
        eapply IHl.
         intros b q.
         eapply X.
         simpl.
         eapply inr.
         assumption.
    Defined.

    Lemma Forall_inv : forall (a:A) l, ForallT (a :: l) -> P a.
    Proof.
      intros. inversion X. trivial.
    Defined.

Export ListNotations.

    Lemma Forall_rect : forall (Q : list A -> Type),
      Q [] -> (forall b l, P b -> Q (b :: l)) -> forall l, ForallT l -> Q l.
    Proof.
      intros Q H H'; induction l; intro; [|eapply H', Forall_inv]; eassumption.
    Defined.


    Lemma Forall_dec :
      (forall x:A, (P x) + (P x -> False)) ->
      forall l:list A, (ForallT l) + (ForallT l-> False).
    Proof.
      intro Pdec. induction l as [|a l' Hrec].
      - left. apply Forall_nil.
      - destruct Hrec as [Hl'|Hl'].
        + destruct (Pdec a) as [Ha|Ha].
          * left. now apply Forall_cons.
          * right. abstract now inversion 1.
        + right. abstract now inversion 1.
    Defined.

  End One_predicateT.

  (*Lemma Forall_Exists_neg (P:A->Prop)(l:list A) :
   Forall (fun x => ~ P x) l <-> ~(Exists P l).
  Proof.
   rewrite Forall_forall, Exists_exists. firstorder.
  Qed.

  Lemma Exists_Forall_neg (P:A->Prop)(l:list A) :
    (forall x, P x \/ ~P x) ->
    Exists (fun x => ~ P x) l <-> ~(Forall P l).
  Proof.
   intro Dec.
   split.
   - rewrite Forall_forall, Exists_exists; firstorder.
   - intros NF.
     induction l as [|a l IH].
     + destruct NF. constructor.
     + destruct (Dec a) as [Ha|Ha].
       * apply Exists_cons_tl, IH. contradict NF. now constructor.
       * now apply Exists_cons_hd.
  Qed.

  Lemma neg_Forall_Exists_neg (P:A->Prop) (l:list A) :
    (forall x:A, {P x} + { ~ P x }) ->
    ~ Forall P l ->
    Exists (fun x => ~ P x) l.
  Proof.
    intro Dec.
    apply Exists_Forall_neg; intros.
    destruct (Dec x); auto.
  Qed.

  Lemma Forall_Exists_dec (P:A->Prop) :
    (forall x:A, {P x} + { ~ P x }) ->
    forall l:list A,
    {Forall P l} + {Exists (fun x => ~ P x) l}.
  Proof.
    intros Pdec l.
    destruct (Forall_dec P Pdec l); [left|right]; trivial.
    now apply neg_Forall_Exists_neg.
  Defined.

  Lemma Forall_impl : forall (P Q : A -> Prop), (forall a, P a -> Q a) ->
    forall l, Forall P l -> Forall Q l.
  Proof.
    intros P Q H l. rewrite !Forall_forall. firstorder.
  Qed. *)
End ExistsT_ForallT.
