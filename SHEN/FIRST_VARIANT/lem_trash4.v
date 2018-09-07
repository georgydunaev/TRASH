(*Fixpoint*)
Definition lem1 : forall
(t : Terms) (xi : SetVars) (pi : SetVars->X) (u :Terms),
(*{struct u}*)
(teI pi (substT t xi u))=(teI (cng pi xi (teI pi t)) u).
Proof.
fix lem1 4.
(*destruct (meas u).*)
(*revert t xi pi u.*)
Show Proof.

destruct u as [s|f] .
+ simpl.
  unfold cng.
  destruct (Nat.eqb s xi).
  * reflexivity.
  * simpl.
    reflexivity.
+
  simpl.
(**revert dependent f.
 fix flem1 1.
 intros f t0. **)
  destruct f.
  simpl.
  apply ap.
  simpl in t0.

  (*pose (g:= (@vec_comp_as _ _ _ (teI pi) (substT t xi) _ t0)).
  rewrite -> g.*)
(*unfold cng. teI *)
  pose (g:= (@vec_comp_as _ _ _ (teI pi) (substT t xi) _ t0)).
  rewrite -> g.

pose (Y:=fun wm => @Vector.map Terms X wm fsv0 t0).
pose (a1:=(fun x : Terms => teI pi (substT t xi x))).
pose (a2:=(teI (cng pi xi (teI pi t)))).
pose (Y1:= Y a1). (* (fun x : Terms => teI pi (substT t xi x)) ). *)
pose (Y2:= Y a2). (* (teI (cng pi xi (teI pi t)))).*)
(*pose (YY1:=Y1).
pose (YY2:=Y2).
assert(r1:Y1=YY1). reflexivity.
assert(r2:Y2=YY2). reflexivity.*)
unfold Y in Y1.
unfold Y in Y2.
fold Y1 Y2 in |- *.
Check (@ap).
Check (@ap _ _ a1 a2 Y).
apply (@ap _ _ a1 a2 Y). (**! **)
unfold a1, a2 in |- *.
apply functional_extensionality.
    intro x.

(* dich 
destruct x as [sx|fx] .
 simpl.
  unfold cng.
  destruct (Nat.eqb sx xi).
  * reflexivity.
  * simpl.
    reflexivity.
*
refine (flem1 fx t1  ).
Defined. *)

refine (lem1 t xi pi x ).
Show Proof.
Admitted.




(*Context (x:X).
Print Terms.
Compute (lem1 (FVC 0) 0 (fun _ => x) ).*)
