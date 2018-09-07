
Reserved Notation " 'cc1' "  (at level 70, no associativity).

Inductive IT :=
| c1 : IT.

Require Import Utf8.
(*Require Unicode.Utf8.
Require  Unicode.Utf8_core.*)
(*
Notation "\u2200 x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' \u2200 x .. y ']' , P") : type_scope.*)
Theorem ef : \u2200x:False,False.
intro.
exact x.
Defined.

Theorem ef : \forall x:False,False.  (*uim*)

Inductive IT :=
| c1 : IT
| c2 (x:IT) (H:
 match x as x return Prop with 
 | c1 => True
 | c2 y => False
 end): IT
.

c2 c1 tt.
fun x:False => c2 (c2 c1 tt) x

Print IT_ind.


Inductive IT :=
| c1 : IT
| c2 : IT.
Print IT_ind.

fun (P : IT -> Prop) (f : P c1) (f0 : P c2) (i : IT) =>
match i as i0 return (P i0) with
| c1 => f
| c2 => f0
end
     : forall P : IT -> Prop, P c1 -> P c2 -> forall i : IT, P i


Inductive IT :=
| c1 : IT
| c2 : IT
| c3 (x:IT) (H:
 match x with 
 | c1 => True
 | _ => False
 end): IT
.

Inductive IT :=
| c1 : IT
| c2 : IT->IT
| c3 (x:IT) (H:match x with | _ => True end): IT
.

Check c3.

Inductive IT :=
| c1 : IT
| c2 : IT->IT
| c3 (x:IT) (H:match x with | _ => True end): IT
.

Print IT_ind.
