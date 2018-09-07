Module M.
 Module N.
  CoInductive pair1_type (a b: Type) :=
  | Pair1: a -> b -> pair1_type a b.
  Definition fst1 (a b: Type) (p: pair1_type a b) := let (x, _) := p in x.
  Definition snd1 (a b: Type) (p: pair1_type a b) := let (_, x) := p in x.
 End N.
 Module O.
  Inductive pair2_type (a b: Type) :=
  | Pair2: a -> b -> pair2_type a b.
  Definition fst2 (a b: Type) (p: pair2_type a b) := let (x, _) := p in x.
  Definition snd2 (a b: Type) (p: pair2_type a b) := let (_, x) := p in x.
 End O.
End M.
Extraction Language Scheme.
Recursive Extraction M.

Extraction Language Haskell.
Recursive Extraction M.

Search (fun x=> _).

(*Extraction Language OCaml.
Recursive Extraction M.
*)


From Coq Require Extraction.
Require Extraction.
