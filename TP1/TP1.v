(* Question 1 *)
Lemma l0 : forall A B C : Prop,
  ((A -> B) /\ (B -> C)) -> (A -> C).
Proof.
intros.
destruct H.
apply H1.
apply H.
apply H0.
Qed.

Lemma l1 : forall A B: Prop,
(A \/ B) -> (B \/ A).
Proof.
intros.
destruct H.
right.
assumption.
left.
assumption.
Qed.

Lemma l2 : forall A B C: Prop,
((A /\ B) -> C) -> A -> B -> C.
Proof.
intros.
apply H.
split; assumption.
Qed.

Lemma l3 : forall A B C: Prop,
(A -> B -> C) -> (A /\ B) -> C.
Proof.
intros.
apply H.
destruct H0.
assumption.
destruct H0.
assumption.
Qed.

Lemma l4 : forall A B C: Prop,
(A /\ (B \/ C)) -> ((A /\ B) \/ (A /\ C)).
Proof.
intros.
destruct H.
destruct H0.
left.
split; assumption.
right.
split; assumption.
Qed.

Lemma l5 : forall A B C: Prop,
((A /\ B) \/ (A /\ C)) -> (A /\ (B \/ C)).
Proof.
intros.
destruct H.
destruct H.
split.
assumption.
left.
assumption.
destruct H.
split.
assumption.
right.
assumption.
Qed.

(* Question 2 *)
Print l1.

(* Question 3 *)
Axiom tiers_exclu : forall A:Prop,
A \/ ~A.

Lemma contraposee : forall A B: Prop,
(A -> B) <-> (~B -> ~A).
Proof.
intros.
split.
intros.
intro.
apply H0.
apply H.
assumption.
intros.
assert(Htx := tiers_exclu B).
destruct Htx.
assumption.
destruct H.
assumption.
assumption.
Qed.

Lemma double_negation : forall A: Prop,
~(~A) <-> A.
Proof.
intros.
split.
intros.
assert(Htx := tiers_exclu A).
destruct Htx.
assumption.
elim H.
assumption.
intros.
intro.
apply H0.
assumption.
Qed.

Lemma loi_de_Pierce : forall A B: Prop,
((A -> B) -> A) -> A.
Proof.
intros.
elim (tiers_exclu A).
intro.
assumption.
intro.
apply H.
intro.
absurd A.
assumption.
assumption.
Qed.

(* Question 4 *)
Lemma q4 : forall (A : Set) (B : A -> A -> Prop),
(exists y : A, (forall x : A, B x y)) -> (forall x : A, exists y : A, B x y).
Proof.
intros.
destruct H.
exists x0.
apply H.
Qed.