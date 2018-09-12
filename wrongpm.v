Require Import Coq.Unicode.Utf8.

 Infix "≡" := (x=y) (at level 70, no associativity).
(*
Theorem thn (A : Type)
  (i : nat)
  (index_f : nat → nat)
  (n : nat)
  (ip : n < i)
  (partial_index_f : nat → option nat)
  (L : (partial_index_f (index_f n)) = Some n)
  (V : ∀ i0 : nat, i0 < i → option A)
  (l : ∀ z : nat, partial_index_f (index_f n) = Some z → z < i)
  :
   V n ip
   ≡ match
       partial_index_f (index_f n) as fn
       return (partial_index_f (index_f n) = fn → option A)
     with
     | Some z => λ p : partial_index_f (index_f n) = Some z, V z (l z p)
     | None => λ _ : partial_index_f (index_f n) = None, None
     end eq_refl.
*)