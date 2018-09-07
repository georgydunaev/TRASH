Fixpoint lem1 (t : Terms) (xi : SetVars) (pi : SetVars->X) (u :Terms)
{struct u}
:
myeq _ (teI pi (substT t xi u)) (teI (cng pi xi (teI pi t)) u).
Proof.
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
  apply myap.
  simpl in t0.
  (*pose (g:= (@vec_comp_as _ _ _ (teI pi) (substT t xi) _ t0)).
  rewrite -> g.*)
unfold cng. 
  pose (g:= (@vec_comp_as _ _ _ (teI pi) (substT t xi) _ t0)).
  rewrite -> g.

(*
Check ap.
assert H.
destruct t0.
simpl.
reflexivity.
simpl.
rewrite <- lem1.
apply ap.
simpl.

pose (u1:= (fun x : Terms => teI pi (substT t xi x))).
pose (u2:=(teI (cng pi xi (teI pi t)))).
fold u1 u2 in |- *.
pose (Y:=fun wm => @Vector.map Terms X wm n t0).
apply (@ap _ _ u1 u2 Y).
unfold u1, u2 in |- *.
apply functional_extensionality.
    intro x.

    apply lem1.
Defined.
@Vector.map Terms X u1 n t0 =
@Vector.map Terms X u2 n t0
*)

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
apply (@myap _ _ a1 a2 Y). (**! **)
unfold a1, a2 in |- *.
(*refine (fun x => lem1 t xi pi x ).*)
(*
pose(v:=(@functional_extensionality)).
destruct H.
*)

apply @myfe.

(*apply @functional_extensionality.*)
    intro x.
refine (lem1 t xi pi x ).
Defined.
Show Proof.
Admitted.  *)
