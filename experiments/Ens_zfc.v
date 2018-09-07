Polymorphic Inductive Ens: Type := 
sup : forall A:Type, (A->Ens)->Ens.

About sup.
Check Top.sup.
(*Check Type@{Top.2}.*)

(*
Check Type@{max(Prop, Top.2+1)}.
*)
Check sup Ens (fun x => x).