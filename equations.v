Require Import Arith Omega.
From Equations Require Import Equations.

Definition SetVars  := nat.

Definition FuncSymb := nat.

Record FSV := {
 fs : FuncSymb;
 fsv : nat;
}.

Equations neg (b : bool) : bool :=
neg true := false ;
neg false := true.
Print All.

Equations mid (n : nat) : nat :=
  mid n by rec n lt :=
  mid 0 := 0;
  mid (S (S n')) := S (mid n');
  mid (S n') := S (mid n').
Next Obligation.
Defined.
Compute (mid 2).



Print Vector.t.

Fail
Equations is_te (u:preterm) : Prop :=
  (*substT2 u by rec u lt :=*)
  is_te (Vari q) := True;
  is_te (Node fv (nil)) := (fsv fv = 0);
  is_te (Node fv (cons l ts)) := (fsv fv = length ts) /\ (is_te (Node fv ts)).

Module AAA.
Local
Equations is_te (u:preterm) : Prop :=
  (*is_te u by rec u lt :=*)
  is_te (Vari q) := True;
  is_te (Node fv lts) <= (fsv fv == length lts) (* fv lts *) => {
   is_te (Node fv nil) true := True;
   is_te (Node fv (cons l ts)) true := (*is_te (Node fv ts) /\*) (is_te l);
   is_te (Node fv lts) false := False
  }
.
End AAA.
Check AAA.is_te.
Fail Check is_te.
Equations is_te (u:preterm) : Prop :=
  (*is_te u by rec u lt :=*)
  is_te (Vari q) := True;
  is_te (Node fv lts) <= (fsv fv == length lts) => {
   is_te (Node fv nil) true := True;
   is_te (Node fv (cons l ts)) true with is_te := {
    is_te := True
    (*checkpls (cons l ts) := (is_te l) (* /\ che *)*)
   }
  }
.
   is_te (Node fv lts) false := False


  is_te (Node fv (nil)) := (fsv fv = 0);
  is_te (Node fv (cons l ts)) := (fsv fv = length ts) .

Next Obligation.
Defined.



(*Section substsec.
Hypotheses (t:preterm) (xi: SetVars).
End substsec.*)


Equations mid (n : nat) : nat :=
  mid n by rec n lt :=
  mid 0 := 0;
  mid (S (S n')) := S (mid n');
  mid (S n') := S (mid n').
Next Obligation.
Defined.

Section substsec.
Hypotheses (t:preterm) (xi: SetVars).
Equations substIsTerm (u:term): 
is_term (substT u) :=
substIsTerm u by rec u MyWF :=
.
End substsec.

  mid n by rec n lt :=
  mid 0 := 0;
  mid (S (S n')) := S (mid n');
  mid (S n') := S (mid n').
Next Obligation.
Defined.



Unset Elimination Schemes.
Inductive preterm :=
| Vari :> SetVars -> preterm
| Node : FSV -> list preterm -> preterm.
Set Elimination Schemes.
