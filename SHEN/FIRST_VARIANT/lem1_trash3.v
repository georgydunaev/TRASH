Program Fixpoint lem1 (t : Terms) (xi : SetVars) (pi : SetVars -> X) (u : Terms) 
{measure (meas u)} :
   teI pi (substT t xi u) = teI (cng pi xi (teI pi t)) u :=
   match
     u as t00 return (teI pi (substT t xi t00) = teI (cng pi xi (teI pi t)) t00)
   with
   | FVC s =>
       let b := Nat.eqb s xi in
       if b as b0
        return
          (teI pi (if b0 then t else s) = (if b0 then teI pi t else pi s))
       then @eq_refl X (teI pi t)
       else @eq_refl X (pi s)
   | FSC f t0 =>
       match
         f as f0
         return
           (forall t1 : Vector.t Terms (fsv f0),
            fsI f0
              (@Vector.map Terms X (teI pi) (fsv f0)
                 (@Vector.map Terms Terms (substT t xi) (fsv f0) t1)) =
            fsI f0
              (@Vector.map Terms X (teI (cng pi xi (teI pi t))) (fsv f0) t1))
       with
       | {| fs := fs0; fsv := fsv0 |} =>
           fun t1 : Vector.t Terms (fsv {| fs := fs0; fsv := fsv0 |}) =>
           @ap (Vector.t X fsv0) X
             (@Vector.map Terms X (teI pi) fsv0
                (@Vector.map Terms Terms (substT t xi) fsv0 t1))
             (@Vector.map Terms X (teI (cng pi xi (teI pi t))) fsv0 t1)
             (fsI {| fs := fs0; fsv := fsv0 |})
             (let g :
                @Vector.map Terms X (teI pi) fsv0
                  (@Vector.map Terms Terms (substT t xi) fsv0 t1) =
                @Vector.map Terms X (fun x : Terms => teI pi (substT t xi x))
                  fsv0 t1 :=
                @vec_comp_as Terms Terms X (teI pi) (substT t xi) fsv0 t1 in
              @eq_ind_r (Vector.t X fsv0)
                (@Vector.map Terms X
                   (fun x : Terms => teI pi (substT t xi x)) fsv0 t1)
                (fun t2 : Vector.t X fsv0 =>
                 t2 =
                 @Vector.map Terms X (teI (cng pi xi (teI pi t))) fsv0 t1)
                (let Y :=
                   fun wm : Terms -> X => @Vector.map Terms X wm fsv0 t1 in
                 let a1 := fun x : Terms => teI pi (substT t xi x) in
                 let a2 := teI (cng pi xi (teI pi t)) in
                 let Y1 := Y a1 in
                 let Y2 := Y a2 in
                 @ap (Terms -> X) (Vector.t X fsv0) a1 a2 Y
                   (@functional_extensionality Terms X
                      (fun x : Terms => teI pi (substT t xi x))
                      (teI (cng pi xi (teI pi t)))
                      (fun x : Terms => lem1 t xi pi x)))
                (@Vector.map Terms X (teI pi) fsv0
                   (@Vector.map Terms Terms (substT t xi) fsv0 t1)) g)
       end t0
   end
.
Check 0=1.
Locate "=".
Print eq.


Print eq_rect.
(*myeq_rect = 
fun (A : Type) (x : A) (P : forall a : A, myeq A x a -> Type)
  (f : P x (myeq_refl A x)) (y : A) (m : myeq A x y) =>
match m as m0 in (myeq _ _ y0) return (P y0 m0) with
| myeq_refl _ _ => f
end
     : forall (A : Type) (x : A) (P : forall a : A, myeq A x a -> Type),
       P x (myeq_refl A x) -> forall (y : A) (m : myeq A x y), P y m*)
Next Obligation.