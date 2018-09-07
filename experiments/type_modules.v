
Module M.
(*    Interactive Module M started*)
Definition T := nat.
(*    T is defined*)
Definition x := 0.
(*    x is defined *)
Definition y : bool.
exact true.
Defined.
End M.


Module Type SIG.
Parameter T : Set.
Parameter x : T.
End SIG.
Module N : SIG := M.
 (* with Definition T := nat := M. *)
Print N.T.
Print N.x.