(********** Exercice 1 **********)
(* Question 1 *)
Fixpoint myplus (a b:nat) :=
match b with
| 0 => a
| S n => S (myplus a n)
end.

(* Question 2 *)
Require Import Arith.
Lemma myplus_assoc : forall a b c : nat,
myplus (myplus a b) c = myplus a (myplus b c).
Proof.
intros.
induction c.
simpl.
reflexivity.
simpl.
rewrite IHc.
reflexivity.
Qed.

(* Question 3 *)
Lemma myplus_Sn_m : forall n m : nat,
myplus (S n) m = S (myplus n m).
Proof.
intros.
induction m.
simpl.
reflexivity.
simpl.
rewrite <- IHm.
reflexivity.
Qed.

Lemma myplus_0_m : forall m : nat,
myplus 0 m = m.
Proof.
intros.
induction m.
simpl.
reflexivity.
simpl.
rewrite IHm.
reflexivity.
Qed.

(* Question 4 *)
Lemma myplus_comm : forall a b :nat,
myplus a b = myplus b a.
Proof.
intros.
induction a.
simpl.
rewrite myplus_0_m.
reflexivity.
simpl.
rewrite myplus_Sn_m.
rewrite IHa.
reflexivity.
Qed.

(* Question 5 *)
Fixpoint sommation (f:nat->nat) (n:nat) :=
match n with
| 0 => f n
| S m => f (S m) + sommation f m
end.

Eval compute in sommation (fun x => x) 100.

(* Question 6 *)
Require Export ArithRing.
Lemma sommation_f_Sn : forall (f: nat->nat) (n:nat),
sommation f (S n) = f (S n) + sommation f n.
Proof.
intros.
simpl.
reflexivity.
Qed.

Lemma q6 : forall n : nat,
2 * sommation (plus 0) n = n*(n+1).
Proof.
intros.
induction n.
simpl.
reflexivity.
rewrite plus_Sn_m.
rewrite sommation_f_Sn.
rewrite plus_O_n.
rewrite Nat.mul_add_distr_l.
rewrite IHn.
ring.
Qed.

(********** Exercice 2 **********)
(* Question 7 *)
(* 
  m correspond, à .
  i et j correspondent respectivement au nombre de pièces 5 et 3 euros.
*)
(* Question 8&9 *)
(*
  Avec le principe d'induction suivant, on pourra aisément démontrer le théorème.
  forall P : nat->Prop,
  P 0 -> P 1 -> P 2 -> (forall n : nat, P n -> P(n+3)) -> forall n : nat, P n.
*)
Lemma induc_by_3 : forall P : nat->Prop,
P 0 -> P 1 -> P 2 -> (forall n : nat, P n -> P(S (S (S n)))) -> forall n : nat, P n.
Proof.
intros.
assert (Hx : P n /\ P (S n) /\ P (S (S n))).
induction n.
split.
assumption.
split;assumption.
split.
destruct IHn.
destruct H4.
assumption.
split.
destruct IHn.
destruct H4.
assumption.
apply H2.
destruct IHn.
assumption.
destruct Hx.
assumption.
Qed.

Lemma pieces : forall m : nat, exists i : nat, exists j : nat,
8+m=5*i+3*j.
Proof.
intros.
induction m.
exists 1.
exists 1.
reflexivity.
destruct IHm as [x [y H]].
rewrite <- plus_n_Sm, H.
destruct x.
(* x=0 *)
  (* y=0 *)
  destruct y.
  discriminate.
    (* y => Sy *)
    destruct y.
    discriminate.
    destruct y.  
    discriminate.
    exists 2,y.
    ring.
(* x>0 *)
exists x, (y+2).
ring.
Qed.
	
Lemma pieces_avec_mon_lemmme : forall m : nat, exists i : nat, exists j : nat,
8+m=5*i+3*j.
Proof.
Qed.

