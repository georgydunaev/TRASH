(** * Primitives constructions of W_types *)
(** ** Definition of W_trees for the recursivity *)
Inductive W_tree
         (constructeur : Type)
         (parametre: constructeur -> Type)
         : Type :=
W_acc: forall (cons: constructeur)
              (pars: parametre cons -> W_tree constructeur parametre),
              W_tree constructeur parametre.

(** ** Definition of empty type to have leaves in W_trees *)
Inductive Empty: Type :=.
(** ** Definition of the binary sum to have a type with at least two constructors *)
Inductive BinarySum (A: Type) (B: Type): Type :=
| Left: A -> BinarySum A B
| Right: B -> BinarySum A B.
(** ** Definition of the dependant sum for existentials *)
Inductive DependantSum (A: Type) (f: A -> Type): Type :=
| Exist: forall a, f a -> DependantSum A f.
(** ** Definition of the dependant products for universals *)
Inductive DependantProduct (A: Type) (f: A -> Type) :=
| Forall: (forall a, f a) -> DependantProduct A f.
(** * Given a type, we have a predicate to tell if it is a W_type one *)
Inductive WTYPE: Type -> Prop :=
| WW_tree: forall C P, WTYPE C -> (forall c, WTYPE (P c)) -> WTYPE (W_tree C P)
| WEmpty: WTYPE Empty
| WBSum: forall A B, WTYPE A -> WTYPE B -> WTYPE (BinarySum A B)
| WDSum: forall A f, WTYPE A -> (forall a, WTYPE (f a)) ->
         WTYPE (DependantSum A f)
| WProduct: forall A f, WTYPE A -> (forall a, WTYPE (f a)) ->
            WTYPE (DependantProduct A f).
(** * Now, we require extensionality to build w_types such as natural numbers *)
Axiom ext: forall A B (f g: A -> B),
 (forall a, f a = g a) -> g = f.
Ltac cext H := case (ext _ _ _ _ H).
(** * A cast from empty type to any other *)
Definition Leaf (T: Type) (a: Empty): T := match a with end.
Lemma Leaf_elim: forall (A: Type) (f g: Empty -> A), g = f.
Proof.
 intros A f g.
 apply ext; intros [].
Qed.
(** Now, w_types are fully defined.
 Next section presents some examples. *)
(** * Some well known types seen as w_types *)
(** ** Unit type *)
Definition Unit := DependantProduct Empty (fun _ => Empty).
Lemma WUnit: WTYPE Unit.
Proof.
exact (WProduct Empty (fun _ : Empty => Empty) WEmpty (Leaf (WTYPE Empty))).
(*Check WProduct.
exact ( WProduct _ _ WEmpty (Leaf (WTYPE Empty))).*)
Show Proof.
Defined.
Definition single: Unit := Forall _ _ (Leaf Empty).
Lemma all_unit_is_single: forall u, single = u.
Proof.
 intros u; destruct u.
 case (Leaf_elim _ e (Leaf Empty)).
 split.
Qed.
(** ** Booleans type *)
Definition Bool := BinarySum Unit Unit.
Lemma WBool: WTYPE Bool.
Proof.
exact (WBSum _ _ WUnit WUnit).
Defined.
Definition top: Bool := Left _ _ single.
Definition bottom: Bool := Right _ _ single.
Definition Ift (A B: Type) (t: Bool): Type :=
if t then A else B.
Definition If (A B: Type) (P: Type -> Type) (Pt: P A) (Pb: P B)
              (t: Bool): P (Ift A B t) :=
if t as t0 return P (Ift A B t0)
   then Pt
   else Pb.
(** ** Naturals type *)
Definition Nat := W_tree Bool (Ift Empty Unit).
Lemma WNat: WTYPE Nat.
Proof WW_tree _ _ WBool (If _ _ _ WEmpty WUnit).
Definition O: Nat := W_acc _ _ top (Leaf _).
Definition S (n: Nat) : Nat := W_acc _ _ bottom (fun _ => n).
Lemma Nat_ind: forall (P : Nat -> Prop), P O -> (forall n, P n -> P (S n)) ->
forall n, P n.
 induction n.
 destruct cons; simpl in *.
  case (Leaf_elim _ pars (Leaf Nat)).
  case (all_unit_is_single u).
  assumption.
 unfold S in H0.
 case (all_unit_is_single u).
 assert (K := H0 _ (H1 single)); clear H0; simpl in K.
 assert ((fun _ : Unit => pars single) = pars).
  apply ext; intro a; case (all_unit_is_single a); split.
 case H0; assumption.
Qed.
(** ** And eventually parametric lists type *)
Definition List (A : Type) := W_tree (BinarySum Unit A)
                (fun b => if b then Empty else Unit).
Lemma WList: forall A, WTYPE A -> WTYPE (List A).
Proof.
 intros A WA; apply WW_tree.
  apply WBSum.
   exact WUnit.
  exact WA.
 intros []. (*intro.*)
  exact WEmpty.
 exact WUnit.
Qed.
Definition Nil A : List A := W_acc _ _ (Left _ _ single) (Leaf _).
Definition Cons A (a: A) (l: List A): List A :=
 W_acc _ _ (Right _ _ a) (fun _ => l).

(* preTerms are W-type? *)



