Require Export Coq.Vectors.Vector.
Require Import Coq.Vectors.Fin.
(* Coding of the element of particular ordinal with two natural numbers.
(n+1) - total, m - number.  $m \in (n+1)$ *)
Fixpoint code (n m:nat): t (S n).
Proof.
destruct n.
+ exact (F1).
+ destruct m.
  - exact (F1).
  - refine (FS _).
    exact (code n m).
Defined.

Section sec0.
Parameter SetFVars : Set.
Parameter SetBVars : Set.
Parameter Constants : Set.
Parameter FuncSymb : Set.
Parameter PredSymb : Set.
Parameter valfs : FuncSymb -> nat.
Parameter valpr : PredSymb -> nat.

(*
Hypothesis PVarseq_dec:forall x y:PropVars,{x=y}+{not(x=y)}.
Hypothesis FVarseq_dec:forall x y:SetFVars,{x=y}+{not(x=y)}.
Hypothesis BVarseq_dec:forall x y:SetBVars,{x=y}+{not(x=y)}.
*)

Inductive Term:Set:=
| CC  :> Constants -> Term
| FVC :> SetFVars  -> Term
| FSC (f:FuncSymb) :  (t (valfs f)-> Term) -> Term.

Check prod.

Inductive it:Set:=
|co1 :it
|co2 :it.

Fixpoint ni0 (x:SetFVars) (a:it) : Prop.
destruct a.
exact False.
exact True.
Defined.
Print ni0.

(*Incorrect Formulas*)
Inductive Fo:(list SetBVars) -> Set:=
(*|Atom (p:PredSymb): (t (valpr p)-> Term) ->  Fo
|Bot :Fo
|Conj:Fo->Fo->Fo
|Disj:Fo->Fo->Fo
|Impl:Fo->Fo->Fo
|Fora(a:SetFVars)(x:SetBVars)(f:Fo): Fo
|Exis(a:SetFVars)(x:SetBVars)(f:Fo): Fo*)
.

Context (M:Prop).
Check False->False.
Check M->False.

Inductive frm:Prop :=
|atom:Prop->frm
|cand:frm->frm->frm.
Definition det (p:Prop): Prop.
Print and.




