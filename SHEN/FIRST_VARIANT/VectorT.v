
Inductive InV {A} (a:A): forall {n}, Vector.t A n -> Type :=
 |In_cons_hd {m} (v: Vector.t A m): InV a (@Vector.cons A a m v)
 |In_cons_tl {m} x (v: Vector.t A m): InV a v -> InV a (@Vector.cons A x m v).
