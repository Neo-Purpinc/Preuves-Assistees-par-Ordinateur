(********** EXERCICE 1 **********)
Require Import ZArith.
Open Scope Z_scope.

(* Question 1 *)
Inductive gauss : Set :=
(* | Gauss (a : Z) (b : Z). *)
| Gauss: Z -> Z -> gauss.

Definition g0 := Gauss 0 0.
Definition g1 := Gauss 1 0.
Definition gi := Gauss 0 1.

(* Question 2 *)
Fixpoint conjug_gauss (g : gauss) :=
match g with
| Gauss a b => Gauss a (-b)
end.

Fixpoint add_gauss (x y : gauss) :=
match (x,y) with
| (Gauss a b, Gauss c d) => Gauss (a+c) (b+d)
end.

Fixpoint mult_gauss (x y : gauss) :=
match (x,y) with
| (Gauss a b, Gauss c d) => Gauss (a*c) (b*d)
end.

Definition sub_gauss (x y : gauss) :=
add_gauss x (conjug_gauss y).

(* Question 3 *)
Lemma q3 : forall a : gauss,
add_gauss g0 a = a.
Proof.
intros.
destruct a.
simpl.
reflexivity.
Qed.

(* Question 4 *)
Lemma gauss_plus_comm : forall a b : gauss,
add_gauss a b = add_gauss b a.
Proof.
intros.
destruct a,b.
simpl.
rewrite Zplus_comm.
rewrite (Zplus_comm z0 z2).
reflexivity.
Qed.

Lemma gauss_plus_assoc : forall a b c : gauss,
add_gauss (add_gauss a b) c = add_gauss a (add_gauss b c).
Proof.
intros.
destruct a,b,c.
simpl.
rewrite Zplus_assoc.
rewrite (Zplus_assoc z0 z2 z4).
reflexivity.
Qed.

Lemma gauss_mult_comm : forall a b : gauss,
mult_gauss a b = mult_gauss b a.
Proof.
intros.
destruct a,b.
simpl.
rewrite Zmult_comm.
rewrite (Zmult_comm z0 z2).
reflexivity.
Qed.
Close Scope Z_scope.
(********** EXERCICE 2 **********)
(* Question 1 *)
Inductive jour : Set :=
| Lundi : jour
| Mardi : jour
| Mercredi : jour
| Jeudi : jour
| Vendredi : jour
| Samedi : jour
| Dimanche : jour.

(* Question 2 *)
Definition jour_suivant (j:jour) : jour :=
match j with
| Lundi => Mardi
| Mardi => Mercredi
| Mercredi => Jeudi
| Jeudi => Vendredi
| Vendredi => Samedi
| Samedi => Dimanche
| Dimanche => Lundi
end.

Definition jour_precedent (j:jour) : jour :=
match j with
| Lundi => Dimanche
| Mardi => Lundi
| Mercredi => Mardi
| Jeudi => Mercredi
| Vendredi => Jeudi
| Samedi => Vendredi
| Dimanche => Samedi
end.

(* Question 3 *)
Lemma j_suivant : forall j : jour,
jour_suivant (jour_precedent j) = j.
Proof.
intros.
elim j; simpl; reflexivity.
Qed.

Lemma j_precedent : forall j : jour,
jour_precedent (jour_suivant j) = j.
Proof.
intros.
elim j; simpl; reflexivity.
Qed.

(* Question 4 *)
Fixpoint iter_jour (n:nat) (f:jour -> jour) (j:jour) :=
match n with
| 0 => j
| S m => f (iter_jour m f j)
end.

Lemma iter_jour_j_suivant : forall j : jour,
iter_jour 7 jour_suivant j = j.
Proof.
intros.
elim j; simpl; reflexivity.
Qed.

(* Question 5 *)
Lemma iter_jour_j_precedent : forall j : jour,
iter_jour 7 jour_precedent j = j.
Proof.
intros.
elim j; simpl; reflexivity.
Qed.

(* Question 6 *)
Lemma q6 : forall (n m: nat) (f: jour->jour),
forall j : jour, iter_jour(n+m) f j = iter_jour n f (iter_jour m f j).
Proof.
intros.
induction n.
simpl.
reflexivity.
simpl.
rewrite IHn.
reflexivity.
Qed.

(* Question 7 *)
Require Import Arith.

Lemma iter_jour_j_modulo : forall (n:nat) (j:jour),
iter_jour (7*n) jour_suivant j = j.
Proof.
intros.
induction n.
simpl.
reflexivity.
rewrite mult_comm.
rewrite mult_succ_l.
rewrite q6.
rewrite mult_comm.
rewrite iter_jour_j_suivant.
assumption.
Qed.