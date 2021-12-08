(****************************)
(****** ARBRES BINAIRES *****)
(****************************)
(* Question 1 *)
Inductive btree : Type :=
| Leaf
| Node : btree -> nat -> btree -> btree.

(* Question 2 *)
Fixpoint mirror (t:btree) :=
match t with
| Leaf => Leaf
| Node l e r => Node (mirror r) e (mirror l)
end.

(* Question 3 *)
Lemma mirror_idempotente : forall (t:btree),
mirror (mirror t) = t.
Proof.
intros.
induction t.
simpl.
reflexivity.
simpl.
rewrite IHt1.
rewrite IHt2.
reflexivity.
Qed.

(* Question 4 *)
Fixpoint tmap (f:nat->nat) (t:btree) :=
match t with
| Leaf => Leaf
| Node l e r => Node (tmap f l) (f e) (tmap f r)
end.

(* Question 5 *)
Lemma q5 : forall (f g:nat->nat) (t:btree),
tmap f (tmap g t) = tmap (fun x => f (g x)) t.
Proof.
intros.
induction t.
simpl.
reflexivity.
simpl.
rewrite IHt1.
rewrite IHt2.
reflexivity.
Qed.

(* Question 6 *)
Require Import List.
Fixpoint btree_to_list (t:btree) : list nat :=
match t with
| Leaf => nil
| Node l e r => (btree_to_list l)++(e::nil)++(btree_to_list r)
end.

(* Question 7 *)
Lemma q7 : forall (f:nat->nat) (t:btree),
map f (btree_to_list t) = btree_to_list (tmap f t) .
Proof.
intros.
induction t.
simpl.
reflexivity.
simpl.
rewrite map_app.
rewrite <- IHt2.
simpl.
rewrite <- IHt1.
reflexivity.
Qed.

(* Question 8 *)
Fixpoint nb_labels (t:btree) :=
match t with
| Leaf => 0
| Node l e r => S(nb_labels l + nb_labels r)
end.

(* Question 9 *)
Require Import Max.
Fixpoint height (t:btree) :=
match t with
| Leaf => 0
| Node l e r => S(max (height l) (height r))
end.

(* Question 10 *)
Require Import Arith.
Lemma q10 : forall (t:btree),
height t <= nb_labels t.
Proof.
intros.
induction t.
simpl.
reflexivity.
simpl.
assert (Hx := max_dec (height t1) (height t2)).
case_eq Hx; intros.
rewrite e.
apply le_n_S.
rewrite IHt1.
apply le_plus_trans.
reflexivity.
rewrite e.
apply le_n_S.
rewrite IHt2.
rewrite <- plus_comm.
apply le_plus_trans.
reflexivity.
Qed.

(* Question 11 *)
Fixpoint btree_in (x:nat) (t:btree) : Prop :=
match t with
| Leaf => False
| Node l e r => (btree_in x l) \/ e=x \/ (btree_in x r)
end.

Lemma q11 : forall (x:nat) (t:btree),
btree_in x t -> In x (btree_to_list t).
Proof.
intros.
induction t.
simpl.
auto.
simpl.
apply in_or_app.
destruct H as [Ha | Hb].
left.
apply IHt1.
assumption.
simpl.
destruct Hb.
right.
left.
assumption.
right.
right.
apply IHt2.
assumption.
Qed.

(* Question 12 *)
Lemma btree_in_mirror_1 : forall (x:nat) (t:btree),
btree_in x t -> btree_in x (mirror t).
Proof.
intros.
induction t.
simpl.
auto.
simpl.
simpl in H.
destruct H as [H1 | [H2 | H3]].
right. right.
apply (IHt1 H1).
right. left.
assumption.
left.
apply (IHt2 H3).
Qed.

Lemma btree_in_mirror_2 : forall (x:nat) (t:btree),
btree_in x (mirror t) -> btree_in x t.
Proof.
intros.
apply btree_in_mirror_1 in H.
rewrite mirror_idempotente in H.
assumption.
Qed.

(* Question 13 *)
Inductive btree_lt : btree -> nat -> Prop :=
| btree_lt_leaf : forall n,
                  btree_lt Leaf n 
| btree_lt_node : forall n l x r,
                  btree_lt l n -> 
                  x < n ->
                  btree_lt r n ->
                  btree_lt (Node l x r) n.

Inductive btree_gt : btree -> nat -> Prop :=
| btree_gt_leaf : forall n,
                  btree_gt Leaf n 
| btree_gt_node : forall n l x r,
                  btree_gt l n -> 
                  x > n ->
                  btree_gt r n ->
                  btree_gt (Node l x r) n.

(* Question 14 *)
Lemma btree_in_lt: forall (t:btree) (x n:nat), 
btree_in x t -> btree_lt t n -> x < n.
Proof.


Qed.

Lemma btree_in_gt: forall (t:btree) (x n:nat),
btree_in x t -> btree_gt t n -> n < x.
Proof.
Qed.

(* Question 15 *)
Inductive bst : btree -> Prop :=
| bst_leaf : bst Leaf
| bst_node : forall c x l r,
            btree_lt x l ->
            btree_gt x r ->
            bst l ->
            bst r ->
            bst (Node c l x r).

(* Question 16 *)


(* Question 17 *)
Lemma bst_btree_in: forall (x:nat) (t:btree),
bst_in x t -> btree_in x t.
Proof.
Qed.
Lemma btree_bst_in: forall (x:nat) (t:btree),
bst t -> btree_in x t -> bst_in x t.
Proof.
Qed.
(* Question 18 *)
Fixpoint 
(* Question 19 *)
Lemma btree_lt_insert: forall (t:btree) (n x:nat),
bst t -> btree_lt t n -> x < n -> btree_lt (bst_insert t x) n.
Proof.
Qed.
Lemma btree_gt_insert: forall (t:btree) (n x:nat),
bst t -> btree_gt t n -> n < x -> btree_gt (bst_insert t x) n.
Proof.
Qed.
Lemma bst_insert_bst: forall (t:btree) (n:nat),
bst t -> bst (bst_insert t n).
Proof.
Qed.

(* Question 20 *)
Lemma bst_to_list_sorted : forall (t:btree),
bst t -> sorted (btree_to_list t).
Proof.
Qed.