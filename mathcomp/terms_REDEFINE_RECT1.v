(*Add LoadPath "/home/user/Downloads/archives/math-comp-mathcomp-1.7.0/".*)
(*Add mathcomp "/home/user/Downloads/archives/math-comp-mathcomp-1.7.0/mathcomp".*)
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
| Vari :> SetVars -> preterm
| Node : FSV -> list preterm -> preterm.
Set Elimination Schemes.

Section Ind.

Variable T : preterm -> Type.
Variable HVari : forall sv, T (Vari sv).
Variable HNode : forall fv ts, 
foldr (fun t acc => T t * acc)%type unit ts -> T (Node fv ts).

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

Require Import Arith Omega.
From Equations Require Import Equations.
(*Derive Signature Subterm for preterm.*)


Fixpoint is_term (t : preterm) : bool :=
  match t with
  | Vari _ => true
  | Node fv ts => (fsv fv == length ts) && all is_term ts
  end.

Theorem thm0 fv (t:preterm) ts (H : is_term (Node fv (cons t ts))) : is_term t.
Proof. simpl in * |- *.
revert H.
move/andP.
intro H;destruct H;revert H0.
move/andP.
firstorder.
Abort.
Theorem thm0 fv(t:preterm)ts:forall (H : is_term (Node fv (cons t ts))), is_term t.
Proof.
by move/and3P => [X1 X2 X3].
(* destruct Q as [X1 X2 X3]; exact X2.*)
Defined.

Record term := Term { tval : preterm; irt : is_term tval }.

Section let_will_not_survive.
Let fu u  := let: ( m, n ) := u in m + n .
End let_will_not_survive.
Fail Check fu.

Canonical term_subType := [subType for tval].
(*
Print  term_subType.
Print  subType. *)
Definition term_args (t:preterm) : list term :=
  match  t with
  | Vari _     => [::]
  | Node fv ts => pmap insub ts
  end.

Section other.
Fixpoint minilemma (ts:list preterm) (H:all is_term ts) {struct ts}: list term.
Proof.
destruct ts.
exact []%list.
simpl in H.
revert H. move/andP => [H1 H2]. 
refine ( _ :: _)%list.
exact (@Term p H1).
exact (minilemma ts H2).
Defined.

Definition just_args (t:term) : list preterm.
Proof.
destruct t as [[A1|A2] B].
exact [::].
exact l.
Defined.

Definition allisterm (t:term) : all is_term (just_args t).
Proof.
destruct t.
destruct tval0; simpl in * |- *. exact irt0.
revert irt0; by move/andP => [H1 H2].
Defined.

Definition my_term_args (t:term) : list term.
Proof.
unshelve simple eapply minilemma.
exact (just_args t).
exact (allisterm t).
Defined.

Print FSV.
Print preterm.
Theorem lmma a b l p (J:is_term p)
(H:(is_term (Node (Build_FSV a b) l))) :
(is_term (Node (Build_FSV a (S b)) (p::l)%list)).
Proof.
simpl in * |- *.
revert H; move/andP => [H1 H2].
apply/and3P;split;trivial.
Defined.

Theorem amml a b l p (J:is_term p)
(H: is_term (Node (Build_FSV a (S b)) (p::l)%list)):
((is_term (Node (Build_FSV a b) l))).
Proof.
simpl in * |- *.
revert H; move/and3P => [H1 H2 H3].
apply/andP;split;trivial.
Defined.

Theorem lmma2 a b l p (J:is_term p)
(H:(is_term (Node (Build_FSV a b) l))) : { nfs | (is_term (Node nfs (p::l)%list)) }.
Proof.
unshelve eapply exist.
exact {| fs := a; fsv := S b |}.
simpl.
revert H; move/andP => [H1 H2].
apply/and3P;split;trivial.
Defined.

Print Assumptions lmma2.
(*Reset lmma2. !!
Fail Check lmma2. *)

Theorem and_elim a b : (a && b) -> a /\ b.
Proof.
intro H.  destruct (@andP a b). exact a0. inversion H.
Defined.

Lemma eq_bool_prop (D:eqType) (x y:D) : x==y -> x=y.
Proof. (by move/eqP). Defined.

Definition tta0 fv ts (Q:is_term (Node fv ts)) : 
my_term_args (@Term (Node fv ts) Q)=@minilemma _ (allisterm (@Term (Node fv ts) Q)). 
Proof. trivial. Defined.


Check just_args.
Fixpoint tta1 fv (ts:seq preterm) (Q:is_term (Node fv ts)) : 
(just_args (@Term (Node fv ts) Q)) = ts.
Proof. destruct ts; simpl in * |- *; trivial. Defined.

Lemma UTQ C (a b:C) l1 l2 (H:a=b) (J:l1=l2) : a::l1 = b::l2.
Proof.
rewrite H.
rewrite J.
reflexivity.
Defined.

Lemma match_cons (A B:Prop) (a:A) (b:B)(C:Type) p (l:seq C) : (match conj a b with |conj H1 H2 => p::l end ) =
(match conj a b with |conj H1 H2 => p end)::(match conj a b with |conj H1 H2 => l end)
.
simpl.
destruct (conj a b);trivial.
Defined.


Fixpoint tta fv ts (Q:is_term (Node fv ts)) : 
(map tval (my_term_args (@Term (Node fv ts) Q)))=ts.
(*Fixpoint tta fv ts (Q:is_term (Node fv ts)) : 
let M := @Term (Node fv ts) Q in
(map tval (my_term_args M))=ts.*)
Proof.
unfold my_term_args.
unfold minilemma.
pose ( rew := @tta1 fv ts Q).
set (BBJ := (just_args {| tval := Node fv ts; irt := Q |})).
fold BBJ in rew.
change BBJ with ts.
destruct ts; simpl in * |- *; trivial.
Check elimTF andP match elimTF andP Q with
                            | conj _ H2 => H2
                            end .
pose (R := elimTF andP match elimTF andP Q with
                            | conj _ H2 => H2
                            end).
change (elimTF andP match elimTF andP Q with
                            | conj _ H2 => H2
                            end)  with R.
simpl in R.
destruct R eqn:w.

Check match_cons.
(**
pose (M:=@map_cons _ _ tval 
(match elimTF andP match elimTF andP Q with
                            | conj _ H2 => H2
                            end with
          | conj H1 H2 =>
              {| tval := p; irt := H1 |} end)).
pose (S:= M 
( match elimTF andP match elimTF andP Q with
                            | conj _ H2 => H2
                            end with
          | conj H1 H2 =>
(fix
                  minilemma (ts0 : seq preterm) (H : all is_term ts0) {struct
                            ts0} : seq term :=
                    match ts0 as l return (all is_term l -> seq term) with
                    | []%list => fun _ : true => []%list
                    | p0 :: ts1 =>
                        fun H0 : is_term p0 && all is_term ts1 =>
                        match elimTF andP H0 with
                        | conj H3 H4 =>
                            {| tval := p0; irt := H3 |} :: minilemma ts1 H4
                        end
                    end H) ts H2
   end)
).
simpl in S.
rewrite S. **)
Check @match_cons.
assert (BW:

[seq tval i
   | i <- match elimTF andP match elimTF andP Q with
                            | conj _ H2 => H2
                            end with
          | conj H1 H2 =>
              {| tval := p; irt := H1 |}
          end
          :: 
          match elimTF andP match elimTF andP Q with
                            | conj _ H2 => H2
                            end with
          | conj H1 H2 =>  (fix
                  minilemma (ts0 : seq preterm) (H : all is_term ts0) {struct
                            ts0} : seq term :=
                    match ts0 as l return (all is_term l -> seq term) with
                    | []%list => fun _ : true => []%list
                    | p0 :: ts1 =>
                        fun H0 : is_term p0 && all is_term ts1 =>
                        match elimTF andP H0 with
                        | conj H3 H4 =>
                            {| tval := p0; irt := H3 |} :: minilemma ts1 H4
                        end
                    end H) ts H2
          end] = p :: ts
).
2 :  admit.
rewrite map_cons.
simpl.

apply UTQ.
destruct (elimTF andP match elimTF andP Q with
                    | conj _ H2 => H2
                    end).
simpl.
reflexivity.
fold my_term_args.
admit.
Admitted.


apply tta.
Check @match_cons _ _ i i0.

rewrite -> w.
(* change (match elimTF andP match elimTF andP Q with
                            | conj _ H2 => H2
                            end with
          | conj H1 H2 =>
              {| tval := p; irt := H1 |}
              :: (fix
                  minilemma (ts0 : seq preterm) (H : all is_term ts0) {struct
                            ts0} : seq term :=
                    match ts0 as l return (all is_term l -> seq term) with
                    | []%list => fun _ : true => []%list
                    | p0 :: ts1 =>
                        fun H0 : is_term p0 && all is_term ts1 =>
                        match elimTF andP H0 with
                        | conj H3 H4 =>
                            {| tval := p0; irt := H3 |} :: minilemma ts1 H4
                        end
                    end H) ts H2
          end)
with
(match R with
          | conj H1 H2 =>
              {| tval := p; irt := H1 |}
              :: (fix
                  minilemma (ts0 : seq preterm) (H : all is_term ts0) {struct
                            ts0} : seq term :=
                    match ts0 as l return (all is_term l -> seq term) with
                    | []%list => fun _ : true => []%list
                    | p0 :: ts1 =>
                        fun H0 : is_term p0 && all is_term ts1 =>
                        match elimTF andP H0 with
                        | conj H3 H4 =>
                            {| tval := p0; irt := H3 |} :: minilemma ts1 H4
                        end
                    end H) ts H2
          end).*)
(****************************************)
change BBJ with ts.
fold R.
 as [H1 H2].
simpl.
compute.
rewrite map_cons.
simpl.
fold minilemma.
unfold minilemma.

compute.
simpl.
rewrite <- rew .
simpl.
rewrite -> BBJ in rew.

replace -> (just_args {| tval := Node fv ts; irt := Q |}) in BBJ.

set (f j => expr'). replace expr with f i.

(@tta1 fv ts Q).

destruct fv.
destruct ts; simpl in * |- *.
trivial.
destruct (and_elim Q) as [A1 A2].
Check (eq_bool_prop A1).
revert Q.
rewrite -> (eq_bool_prop A1).
intro Q.

Print my_term_args.
Abort. (* tta *)

Definition perevod (ts : seq preterm) (R : all is_term ts) : seq term 
:= @minilemma ts R.

rewrite map_cons.
compute.
simpl.
Print eq_op.
Abort.
Check reflect.
Check andP.

elim Q.
Check proj2 (pair_andP (fsv0 == (length ts).+1) ((is_term p)&&(all is_term ts))).
pose (Y:=proj2 (pair_andP (fsv0 == (length ts).+1) ((is_term p)&&(all is_term ts))) ).
destruct (@and3P (fsv0 == (length ts).+1) (is_term p) (all is_term ts)).

revert Q. 
move/and3P.
unfold my_term_args.
unfold allisterm.
(*move/and3P. => [H1 H2 H3].
rewrite map_cons.
simpl.
unfold minilemma.*)
Abort. tta

(***********************************************************************************)
End other.

Fixpoint substT (t:preterm) (xi: SetVars) (u:preterm): preterm.
Proof.
destruct u.
2 : { refine (Node f _).
exact (map (substT t xi) l). }
destruct (PeanoNat.Nat.eqb s xi).
exact t.
exact s.
Show Proof.
Abort.


Definition substT :=
(fix substT (t : preterm) (xi : SetVars) (u : preterm) {struct u} : preterm :=
   match u return preterm with
   | Vari s =>
       let b : bool := Nat.eqb s xi in
       match b return preterm with
       | true => t
       | false => Vari s
       end
   | Node f l => Node f (@map preterm preterm (substT t xi) l : list preterm)
   end).

Check 0.


(* not finished
Fixpoint substIsTerm (t:term) (xi: SetVars) (u:term): is_term (substT t xi u).
destruct u as [tval0 i0].
simpl.

revert t xi tval0 i0. fix Hyp 3. intros.
Show Proof.
destruct tval0 as [ s | f l ].
simpl.
destruct (PeanoNat.Nat.eqb s xi) .
exact (irt t).
exact (i0).
simpl.
apply/andP.
split.
Locate " <- ]".
Locate length.
pose (q:= List.map_length).
rewrite -> q.
simpl in i0.
destruct (@andP (fsv f == length l) (all is_term l)) as [B1|B2].
firstorder.
exfalso.
exact (not_false_is_true i0).
Locate all.
simpl in i0.
destruct (@andP (fsv f == length l) (all is_term l)) as [B1|B2].
2 : { exfalso; exact (not_false_is_true i0). }
destruct B1. (* *)
Check all.
Locate conj.
pose (P1 := (fun a b => proj1 (List.forallb_forall a b)) _ _ H0).
apply (fun a b => proj2 (List.forallb_forall a b)).
intros.
simpl in *|-*.

Check (fun x1 x2 x3 x4 x5 => proj1 (@List.in_map_iff x1 x2 x3 x4 x5)).
Check (Hyp t xi x). 
Check List.in_map_iff.
(* usilit hyp ili rewrite H1
y := x
f := substT t xi
l := L
*)
Check (substT t xi).
pose lm1 := (@List.in_map_iff _ _ (substT t xi) l x).
pose lm2 := (proj1 lm1 H1).
destruct lm2 as [x0 [J0 J1]].
rewrite <- J0.
apply Hyp.
apply P1.
exact J1.
Defined.
Abort.*)

Check 0.

Section heredity.
Hypotheses (t : term) (xi : SetVars).
Fixpoint Hyp (tval0 : preterm) :
      is_term tval0 -> is_term (substT t xi tval0).
(*apply/implyP.
move/implyP.*)
intro H.
induction tval0 eqn:w.
simpl.
destruct (sv =? xi ).
simpl.
exact (irt t).
exact H.
simpl in * |- *.
apply/andP.
split.
revert H. move/andP. intro H. destruct H.
pose (q:= List.map_length).
rewrite -> q.
firstorder.
revert H. move/andP. intro H. destruct H.
rewrite <- all_map; fold is_term.
simpl in * |- *.
Abort.

End heredity.

(* big proof *)
Fixpoint substIsTerm (t:term) (xi: SetVars) (u:term): 
is_term (substT t xi u).
destruct u as [tval0 i0].
simpl.
revert t xi tval0 i0. fix Hyp 3. intros.
Show Proof.
destruct tval0 as [ s | f l ].
simpl.
destruct (PeanoNat.Nat.eqb s xi) .
exact (irt t).
exact (i0).
simpl.
destruct l.
simpl in * |- *.
exact i0.
simpl in * |- *.
apply/andP.
split.
pose (q:= List.map_length).
rewrite -> q.
simpl in i0.
destruct (@andP (fsv f == (length l).+1) (all is_term l)) 
 as [B1|B2].
firstorder.

(* i0 must be destructed *)
(*destruct (@andP (fsv f == length l) (all is_term l)) as [B1|B2].*)

(* NOT BAD
exfalso.
exact (not_false_is_true i0).
Locate all.
simpl in i0.
destruct (@andP (fsv f == length l) (all is_term l)) as [B1|B2].
2 : { exfalso; exact (not_false_is_true i0). }
destruct B1. (* *)
Check all.
Locate conj.
pose (P1 := (fun a b => proj1 (List.forallb_forall a b)) _ _ H0).
apply (fun a b => proj2 (List.forallb_forall a b)).
intros.
simpl in *|-*.

Check (fun x1 x2 x3 x4 x5 => proj1 (@List.in_map_iff x1 x2 x3 x4 x5)).
Check (Hyp t xi x). 
Check List.in_map_iff.
(* usilit hyp ili rewrite H1
y := x
f := substT t xi
l := L
*)
Check (substT t xi).
pose lm1 := (@List.in_map_iff _ _ (substT t xi) l x).
pose lm2 := (proj1 lm1 H1).
destruct lm2 as [x0 [J0 J1]].
rewrite <- J0.
apply Hyp.
apply P1.
exact J1.*)
Abort.





