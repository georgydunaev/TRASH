

Inductive even: Set :=
  | c0 : even
  | c1 (s:even) (H:if s is c0 then False else True): even
.


Inductive even: Set :=
  | c0 : even
  | c1 : even
with odd: Prop :=
  | c2 (x:even) (H:
match x with
| c0 => True
| c1 => True
end
): odd.



Inductive even: nat -> Prop :=
  | even_base: even 0
  | even_succ: forall n, odd n -> even (S n)
with odd: nat -> Prop :=
  | odd_succ: forall n, even n -> odd (S n).

