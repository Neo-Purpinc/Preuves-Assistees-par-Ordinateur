(****************************)
(********** LISTES **********)
(****************************)
Require Import Arith.
Require Import Basics.
Open Scope list_scope.
(********** Map **********)
(* Question 1 *)
Fixpoint length {A} (l : list A) : nat :=
  match l with
  | nil => 0
  | _::m => S (length m)
  end.

(* Question 2 *)
Fixpoint map {A B} (f:A->B) (l:list A) : list B :=
  match l with
  | nil => nil
  | h :: t => (f h) :: (map f t)
  end.
  
Eval compute in length (3::4::5::nil).
Eval compute in length (map (fun x => x*x) (3::4::5::nil)).
Eval compute in map (fun x => x*x) (3::4::5::nil).
(* Question 3 *)
Lemma length_original_map : forall (A B : Set) (f : A->B) (l : list A) ,
 length l = length (map f l).
  Proof.
  intros.
  induction l.
  simpl.
  reflexivity.
  simpl.
  rewrite IHl.
  reflexivity.
  Qed.
  
(* Question 4 *)
Definition compose {A B C} (f : B -> C) (g : A -> B) :=
fun x : A => f (g x).

(* Question 5 *)
Lemma assoc_compose : forall (A B C D : Set) (f:C->D) (g:B->C) (h:A->B),
 compose f (compose g h) = compose (compose f g) h.
  Proof.
  intros.
  unfold compose.
  reflexivity.
  Qed.
  
(* Question 6 *)
Lemma q6 : forall (A B C : Set) (f:B->C) (g:A->B) (l: list A),
map (compose f g) l = map f (map g l).
  Proof.
  intros.
  induction l.
  simpl.
  reflexivity.
  simpl.
  rewrite IHl.
  unfold compose.
  reflexivity.
  Qed.

(********** Paramètres implicites **********)
(* Question 7 *)
Set Implicit Arguments.

(********** Append et reverse **********)
(* Question 8 *)
Fixpoint append {A} (l m : list A) : list A :=
  match l with
  | nil => m
  | a::b => a :: (append b m)
  end.

(* Question 9 *)
Lemma q9 : forall (A B:Set) (f:A->B) (l1 l2 : list A),
 map f (append l1 l2) = append (map f l1) (map f l2).
  Proof.
  intros.
  induction l1.
  simpl.
  reflexivity.
  simpl.
  rewrite IHl1.
  reflexivity.
  Qed.
  
(* Question 10 *)
Fixpoint reverse {A} (l:list A) : list A :=
  match l with
  | nil => nil
  | a::b => append (reverse b) (a :: nil)
  end.
  
(* Question 11 *)
Lemma reverse_map : forall (A B: Set) (f:A->B) (l:list A),
 map f (reverse l) = reverse (map f l).
  Proof.
  intros.
  induction l.
  simpl.
  reflexivity.
  simpl.
  rewrite q9.
  rewrite IHl.
  simpl.
  reflexivity.
  Qed.

(* Question 12 *)
Lemma append_l_nil : forall (A:Set) (l:list A),
append l nil = l.
  Proof.
  intros.
  induction l.
  simpl.
  reflexivity.
  simpl.
  rewrite IHl.
  reflexivity.
  Qed.
  
Lemma append_assoc : forall (A:Set) (l1 l2 l3:list A),
append (append l1 l2) l3 = append l1 (append l2 l3).
  Proof.
  intros.
  induction l1.
  simpl.
  reflexivity.
  simpl.
  rewrite IHl1.
  reflexivity.
  Qed.

Lemma reverse_append : forall (A:Set) (l1 l2 : list A),
reverse (append l1 l2) = append (reverse l2) (reverse l1).
  Proof.
  intros.
  induction l1.
  simpl.
  induction l2.
  simpl.
  reflexivity.
  simpl.
  rewrite append_l_nil.
  reflexivity.
  simpl.
  rewrite IHl1.
  rewrite append_assoc.
  reflexivity.
  Qed.
  
(* Question 13 *)
Lemma reverse_reverse : forall (A:Set) (l:list A),
reverse (reverse l) = l.
  Proof.
  intros.
  induction l.
  simpl.
  reflexivity.
  simpl.
  rewrite reverse_append.
  rewrite IHl. 
  simpl.
  reflexivity.
  Qed.

(* Question 14 *)
(* Question 15 *)
Fixpoint foldr {A B} (f:A->B->B) (z:B) (l:list A) :=
  match l with
  | nil => z
  | a::b => f a (foldr f z b)
  end.

(* Question 16 *)
Lemma foldr_append : forall (A B : Set) (f: A->B->B) (z:B) (l1 l2: list A),
foldr f z (append l1 l2) = foldr f (foldr f z l2) l1.
  Proof.
  intros.
  induction l1.
  simpl.
  reflexivity.
  simpl.
  rewrite IHl1.
  reflexivity.
  Qed.
  
(* Question 17 *)
Lemma foldr_map : forall (A B: Set) (f: A->B->B) (l: list A),
foldr (fun h q => (f h)::q) nil l = map f l.
  Proof.
  intros.
  induction l.
  simpl.
  reflexivity.
  simpl.
  rewrite IHl.
  reflexivity.
  Qed.

(* Question 18 *)
Lemma foldr_length : forall (A:Set) (l: list A),
foldr (fun x y => S y) 0 l = length l.
  Proof.
  intros.
  induction l.
  simpl.
  reflexivity.
  simpl.
  rewrite IHl.
  reflexivity.
  Qed.

(* Question 19 *)
Lemma foldr_identity : forall (A:Set) (l: list A),
foldr (fun x y => x::y) nil l = l.
  Proof.
  intros.
  induction l.
  simpl.
  reflexivity.
  simpl.
  rewrite IHl.
  reflexivity.
  Qed.

(* Question 20 *)
Lemma foldr_reverse : forall (A :Set) (l:list A),
foldr (fun x y => match y with
                  | nil => x::y
                  | _ => append y (x::nil)
                  end) nil l = reverse l.
  Proof.
  intros.
  induction l.
  simpl.
  reflexivity.
  simpl.
  rewrite IHl.
  destruct reverse.
  simpl.
  reflexivity.
  reflexivity.
  Qed.
  
(* Question 21 *)
Fixpoint foldl {A B} (f:B->A->B) (z:B) (l:list A) :=
  match l with
  | nil => z
  | a::b => foldl f (f z a) b
  end.

(* Question 22 *)
Lemma foldr_foldl : forall (A B: Set) (f:A->B->B) (z:B) (l:list A),
foldr f z (reverse l) = foldl (flip f) z l.
  Proof.
  intros.
  generalize z.
  clear z.
  induction l.
  simpl.
  reflexivity.
  intros z.
  simpl.
  rewrite foldr_append.
  simpl.
  assert (H1 : flip f z a = f a z).  reflexivity.
  rewrite H1.
  rewrite IHl.
  reflexivity.
  Qed.

(* Question 23 *)
Fixpoint zip {A B} (l1 : list A) (l2 : list B) :=
  match l1, l2 with
  | a::b,c::d => (a,c)::(zip b d)
  | _,_ => nil
  end.

(* Question 24 *)
Lemma length_zip_reflexivity : forall (A:Set) (l1 l2:list A),
length (zip l1 l2) = length (zip l2 l1).
  Proof.
  intros.
  generalize l2.
  clear l2.
  induction l1.
  induction l2.
  simpl.
  reflexivity.
  simpl.
  reflexivity.
  simpl.
  destruct l2.
  simpl.
  reflexivity.
  simpl.
  rewrite IHl1.
  reflexivity.
  Qed.
  
Check zip.

(* Question 25 *)
Lemma length_zip_l1_l2 : forall (A : Set) (l1 l2: list A), 
(length (zip l1 l2) = length l1) \/ (length (zip l1 l2) = length l2).
  Proof.
  intros.
  generalize l2.
  clear l2.
  induction l1.
  simpl.
  auto.
  simpl.
  destruct l2.
  auto.
  simpl.
  destruct (IHl1 l2).
  auto.
  auto.
  Qed.

(* Question 26 *)
Definition prodf {A B} (f g: A->B) :=
fun x => ((f (fst x)),(g (snd x))).

Lemma zip_map : forall (A B: Set) (l1 l2: list A) (f1 f2:A->B),
zip (map f1 l1) (map f2 l2) = map (prodf f1 f2) (zip l1 l2).
  Proof.
  intros.
  generalize l2.
  clear l2.
  induction l1.
  simpl.
  reflexivity.
  simpl.
  destruct l2.
  simpl.
  reflexivity.
  simpl.
  destruct (IHl1 l2).
  unfold prodf.
  simpl.
  reflexivity.
  Qed.

(* Question 27 *)
Fixpoint unzip {A B}(l:list (A*B)) : list A * list B :=
match l with
| nil => (nil,nil)
| (a,b)::c => let (ta,tb) := unzip c in (a::ta,b::tb)
end.

Eval compute in unzip ((5, 2) :: (3, 4) ::(44,6)::(9,7)::nil).
Eval compute in unzip nil.
(* Question 28 *)
Lemma length_fst_unzip : forall (A:Set) (l:list (A*A)),
length  (fst (unzip l)) = length l.
  Proof.
  intros.
  induction l.
  simpl.
  reflexivity.
  simpl.
  destruct a.
  case_eq (unzip l).
  intros.
  simpl.
  rewrite H in IHl.
  simpl in IHl.
  rewrite IHl.
  reflexivity.
  Qed.

(* Question 29 *)
Lemma zip_unzip : forall (A B:Set) (l:list(A*B)),
let (l1,l2) := unzip l in zip l1 l2 = l.
Proof.
  intros.
  induction l.
  simpl.
  reflexivity.
  simpl.
  destruct a.
case_eq (unzip l).
intros.
simpl.
rewrite H in IHl.
rewrite IHl.
reflexivity.
Qed.
