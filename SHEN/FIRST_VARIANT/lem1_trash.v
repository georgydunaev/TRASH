
Fixpoint lem1 (t : Terms) (xi : SetVars) (pi : SetVars->X) {struct t}:
(fun x : Terms => teI pi (substT t xi x)) = teI (cng pi xi (teI pi t)).
Proof.
apply functional_extensionality.
intro u.
destruct u as [s|f] .
+ simpl.
  unfold cng.
  destruct (Nat.eqb s xi).
  * reflexivity.
  * simpl.
    reflexivity.
+ simpl.
  destruct f.
  simpl.
  apply ap.
  simpl in t0.
  pose (g:= (@vec_comp_as _ _ _ (teI pi) (substT t xi) _ t0)).
  rewrite -> g.

pose (Y:=fun wm => @Vector.map Terms X wm fsv0 t0).
pose (a1:=(fun x : Terms => teI pi (substT t xi x))).
pose (a2:=(teI (cng pi xi (teI pi t)))).
pose (Y1:= Y a1). (* (fun x : Terms => teI pi (substT t xi x)) ). *)
pose (Y2:= Y a2). (* (teI (cng pi xi (teI pi t)))).*)
unfold Y in Y1.
unfold Y in Y2.
fold Y1 Y2 in |- *.
Check (@ap).
Check (@ap _ _ a1 a2 Y).
apply (@ap _ _ a1 a2 Y). (**! **)
unfold a1, a2 in |- *.

exact (lem1 t xi pi).
Defined.