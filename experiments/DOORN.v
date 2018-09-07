Require Export Coq.Vectors.Vector.
Require Import Coq.Vectors.Fin.
(* Coding of the element of particular ordinal with two natural numbers.
(n+1) - total, m - number.  $m \in (n+1)$ *)
Print t.
Compute t 0.
Fixpoint code (n m:nat): t (S n).
Proof.
destruct n.
+ exact (F1).
+ destruct m.
  - exact (F1).
  - refine (FS _).
    exact (code n m).
Defined.
(* The same, last elements:
Compute code 2 3.
Compute code 2 2.*)

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

(* OK
Reserved Notation " x 'NotIn' a "  (at level 70, a at level 9, no associativity).
Inductive qw : Type 
:= | tqt (x:Prop)(a:Prop): x NotIn a -> qw
where " x 'NotIn' a " := (x=a).
*)

Reserved Notation " x 'NotIn' a "  (at level 70, a at level 9, no associativity).
(*Inductive qw : Type 
:= | tqt (x:Prop)(a:Prop): x NotIn a -> qw
where " x 'NotIn' a " := (x=a).
NotIn (x:SetFVars)(A:PropF) := True.*)

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
Inductive Fo:Set:=
|Atom (p:PredSymb): (t (valpr p)-> Term) -> Fo
|Bot :Fo
|Conj:Fo->Fo->Fo
|Disj:Fo->Fo->Fo
|Impl:Fo->Fo->Fo
|Fora(a:SetFVars)(x:SetBVars)(f:Fo): Fo (*x NotIn a  ->*)
|Exis(a:SetFVars)(x:SetBVars)(f:Fo): Fo.
Definition con :=
fix con (x : SetBVars) (a:Fo) {struct a}:Prop:=
  match a with
  | Atom p H => False
  | Bot => False
  | Conj u v =>  (con x u)\/(con x v)
  | Disj u v =>  (con x u)\/(con x v)
  | Impl u v =>  (con x u)\/(con x v)
  | Fora _ q v =>  (x=q)\/(con x v)
  | Exis _ q v =>  (x=q)\/(con x v)
  end.

Definition ni :=
fix ni (x : SetBVars) (a:Fo) {struct a}:Prop:=
  match a with
  | Atom p H => True
  | Bot => True
  | Conj u v =>  (ni x u)/\(ni x v)
  | Disj u v =>  (ni x u)/\(ni x v)
  | Impl u v =>  (ni x u)/\(ni x v)
  | Fora _ q v => not(x=q)/\(ni x v)
  | Exis _ q v => not(x=q)/\(ni x v)
  end.


Definition cor :=
fix cor (a:Fo) {struct a}:Prop:=
  match a with
  | Atom p H   => True
  | Bot        => True
  | Conj u v   => (cor u)/\(cor v)
  | Disj u v   => (cor u)/\(cor v)
  | Impl u v   => (cor u)/\(cor v)
  | Fora _ q v => (ni q v)/\(cor v)
  | Exis _ q v => (ni q v)/\(cor v)
  end.

Inductive Fmls :=
| cr (f:Fo) (H:cor f): Fmls.

Section sec1.
Context (a:SetFVars).
Context (x y:SetBVars).
Context (A:PredSymb).
Context (h1: (valpr A = 0)).
Notation "x '@' y " := (@cons _ x _ y) (at level 80, right associativity).

Check Vector.t.
Check 1 @ 0 @ nil _. (*vector of numerals, just an example of notation*)
Theorem hj :Fin.t 0 -> Term.
Proof.
intro f.
inversion f.
Show Proof.
Defined.
Theorem hj2: Fin.t (valpr A) -> Term.
Proof.
rewrite -> h1 .
exact hj.
Defined.

Definition example:= Fora a x (Fora a y (Atom A hj2)).
Compute example.

Definition ex0 := Fora a x
         (Fora a y
            (Atom A
               match
                 match h1 in (_ = x) return (x = valpr A) with
                 | eq_refl => eq_refl
                 end in (_ = x) return (t x -> Term)
               with
               | eq_refl =>
                   fun x : t 0 =>
                   match x in (t x0) return (x0 = 0 -> Term) with
                   | @F1 n =>
                       fun x0 : S n = 0 =>
                       match
                         match
                           x0 in (_ = x1)
                           return
                             match x1 with
                             | 0 => False
                             | S _ => True
                             end
                         with
                         | eq_refl => I
                         end return Term
                       with
                       end
                   | @FS n x0 =>
                       fun x1 : S n = 0 =>
                       match
                         match
                           x1 in (_ = x2)
                           return
                             match x2 with
                             | 0 => False
                             | S _ => True
                             end
                         with
                         | eq_refl => I
                         end return (t n -> Term)
                       with
                       end x0
                   end eq_refl
               end))
     : Fo.

Fixpoint cor (f:Fo):Prop.


Inductive cfo:=
|c1: ->cfo
Check (sig fun x=>ni).
Definition Fmls := sig 

where " x 'NotIn' a " :=
(let fix ni  (x : SetFVars) (a:PropF) {struct a}:Prop:=
  match a with
  | _ =>  False
  end in (ni x a)).

((fix ni0 (x : SetFVars) (a : it) {struct a} : Prop :=
  match a with
  | co1 => False
  | co2 => True
  end) x co1).

((fix ni (x:SetFVars) (a:PropF) {struct a}:Type:=
  match a with
  | _ =>  False
  end :Type ) x a).


 := (prod (x=x) (a=a)).

where NotIn (x:SetFVars)(A:PropF) := True.


where Definition NotIn (x:SetFVars)(A:PropF) := True.

with NotIn (x:SetFVars)(A:PropF) :=
| yyyy : forall (x:SetFVars)(A:PropF), NotIn .

(*with Sub:PropF->Term->SetFVars->PropF:=
| q.*)

(*|Forall:SetFVars->PropF->PropF
|Subst:PropF->Term->SetFVars->PropF*m
with q :=
|true
with w :=
|tqrue
.

Check Vector.t.

Section sec1.
Context (x y:SetVars).
Context (A:PropVars).

Check (Impl (Forall x A) (Subst A y x)). 

Definition Normalize : PropF -> PropF.
intro p.
destruct p.


Check Forall x (Impl A). 

Fixpoint substi (v:SetVars) (x:PropF) :PropF.
destruct x.
destruct (SVarseq_dec v p).

(*
Fixpoint eqvi (a b: PropF): Set. (* Prop.*)
destruct a, b.
exact (p=p0). (* Varseq_dec p p0 *).
*)


Notation "# P" := (Var P) (at level 1) : My_scope.
Notation "A \u2228 B" := (Disj A B) (at level 15, right associativity):My_scope.
Notation "A \u2227 B" := (Conj A B) (at level 15, right associativity):My_scope.
Notation "A * B":= (Impl A B)
(
at         level
16,
right         associativity
)
:
My
scope
