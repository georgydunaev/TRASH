Add LoadPath "/home/user/Downloads/archives/math-comp-mathcomp-1.7.0/".
(*From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.*)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq.
From mathcomp Require Import ssrnat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition SetVars  := nat.

Definition FuncSymb := nat.

Record FSV := {
 fs : FuncSymb;
 fsv : nat;
}.

Unset Elimination Schemes.
Inductive preterm :=
| Vari : SetVars -> preterm
| Node : FSV -> list preterm -> preterm.
Set Elimination Schemes.


Section Ind.

Variable T : preterm -> Type.
Variable HVari : forall sv, T (Vari sv).
Variable HNode : forall fv ts, foldr (fun t acc => T t * acc)%type unit ts -> T (Node fv ts).

Fixpoint preterm_rect (t : preterm) : T t :=
  match t with
  | Vari sv => HVari sv
  | Node fv ts =>
    let fix loop ts : foldr (fun t acc => T t * acc)%type unit ts :=
        match ts with
        | [::] => tt
        | t :: ts => (preterm_rect t, loop ts)
        end in
    HNode fv (loop ts)
  end.

End Ind.

Definition preterm_ind := preterm_rect.

Fixpoint is_term (t : preterm) :=
  match t with
  | Vari _ => true
  | Node fv ts => (fsv fv == length ts) && all is_term ts
  end.

Record term := Term { tval : preterm; _ : is_term tval }.

Canonical term_subType := [subType for tval].

Definition term_args t : list term :=
  match tval t with
  | Vari _     => [::]
  | Node fv ts => pmap insub ts
  end.
