Section Lem1.
Context (t : Terms).
Definition lem1 : forall (u :Terms) (xi : SetVars) (pi : SetVars->X) ,
(teI pi (substT t xi u))=(teI (cng pi xi (teI pi t)) u).
Proof.
fix lem1 1.
intros.
destruct u as [s|f] .
+ simpl.
  unfold cng.
  destruct (Nat.eqb s xi).
  * reflexivity.
  * simpl.
    reflexivity.
+
  simpl.
  destruct f.
  simpl.
  apply ap.
  simpl in t0.

  pose (g:= (@vec_comp_as _ _ _ (teI pi) (substT t xi) _ t0)).
  rewrite -> g.

pose (Y:=fun wm => @Vector.map Terms X wm fsv0 t0).
pose (a1:=(fun x : Terms => teI pi (substT t xi x))).
pose (a2:=(teI (cng pi xi (teI pi t)))).
pose (Y1:= Y a1).
pose (Y2:= Y a2).
unfold Y in Y1.
unfold Y in Y2.
fold Y1 Y2 in |- *.
apply (@ap _ _ a1 a2 Y).
unfold a1, a2 in |- *.
apply functional_extensionality.
    intro x.

refine (lem1 x xi pi ).
Show Proof.
Admitted.