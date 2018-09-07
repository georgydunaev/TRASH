(*From LEM1 section*)

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
