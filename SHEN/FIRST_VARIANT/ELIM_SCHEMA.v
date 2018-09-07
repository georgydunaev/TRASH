(*Inductive mFalse :=.
Check mFalse_rect.*)
Unset Elimination Schemes.
Inductive mFalse :=.

Definition mFalse_rect : forall (P : mFalse -> Type) (m : mFalse), P m.
intros P m.
destruct m.
Show Proof.

Inductive mTrue 
Unset Elimination Schemes.
