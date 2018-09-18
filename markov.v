
(*
\forall x (P(x)\lor\negP(x))-> (\neg\neg\exists x P(x) -> \exists x P(x))
*)
Lemma markov (P:nat->nat) :
forall (x:nat), ( (P x)=0 \/ not (P x = 0) )-> 
(not(not (exists x, (P x =0))) -> (exists x, (P x =0))).
Proof.
intros x.
induction x eqn:j.
intros.
destruct H.
exists 0.
exact H.

exists x.
Abort.


Lemma markov (P:nat->Prop) :
forall (x:nat), ( (P x) \/ not (P x) )-> 
(not(not (exists x, (P x))) -> (exists x, (P x))).
Proof.
intros x.
induction x eqn:j.
intros.
destruct H.
exists 0.
exact H.
Abort.