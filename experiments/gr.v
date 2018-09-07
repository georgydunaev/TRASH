Check (fix A (x:nat) : nat := x).
Check (fun (x:nat) => x : nat).
Check (fix A (x:nat) := x).
Check (fix A (x:nat) := x : nat).
Check (fix F (x:nat) := x):nat->nat.


Fixpoint nat_rect' (P : nat -> Type) 
  (HO : P O)
  (HS : forall n, P n -> P (S n)) (n : nat) :=
  match n return P n with
    | O => HO
    | S n' => HS n' (nat_rect' P HO HS n')
  end.
