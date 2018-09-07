Set Implicit Arguments.
Section List.
Variables X Y : Type.
Variable f : X -> Y -> Y.
Inductive list0 := nil0 : list0 | cons0 : X -> list0 -> list0.
Fixpoint fold (y : Y) (xs : list0) : Y := match xs with
| nil0 => y
| cons0 x xr => fold (f x y) xr
 end.
End List.
Inductive tree := T : list0 tree -> tree.
Fixpoint size (t : tree) : nat := match t with
| T ts => S (fold (fun t a => size t + a) 0 ts)
end.
Check nil0.
Fixpoint size2 (t : tree) : nat := match t with (*1*)
 | T ts =>
   S (let fix fold y xs {struct xs} :=
      match xs with
      | nil0 _ => y
      | cons0 x xr => fold (size x + y) xr
      end
    in fold 0 ts)
end. 



Fixpoint size (t : tree) : nat := match t with (*1*)
 | T ts =>
   S (let fix fold y xs {struct xs} :=
      match xs with
      | nil => y
      | cons x xr => fold (size x + y) xr
      end
    in fold 0 ts)
end. 