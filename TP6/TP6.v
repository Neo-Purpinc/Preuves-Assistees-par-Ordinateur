(****************************)
(************ TP6 ***********)
(****************************)
Require Import ZArith.
Open Scope Z_scope.
(********** Exercice 1 **********)
(* Question 1 *)
Inductive expr : Set :=
| Plus : expr -> expr -> expr
| Minus : expr -> expr -> expr
| Mult : expr -> expr -> expr
| Oper : Z -> expr.

(* Question 2 *)
Definition exemple_1 := Mult (Plus (Oper 2) (Oper 5)) (Oper 3).
Definition exemple_2 := Minus (Plus (Minus (Oper 2) (Oper 1)) (Mult (Oper 7) (Oper 6))) (Oper 2).

(* Question 3 *)
Fixpoint eval_expr (e:expr) : Z :=
match e with
| Plus a b => (eval_expr a) + (eval_expr b)
| Minus c d => (eval_expr c) - (eval_expr d)
| Mult e f => (eval_expr e) * (eval_expr f)
| Oper o => o
end.

Eval compute in eval_expr (Mult (Plus (Oper 2) (Oper 5)) (Oper 3)).
Eval compute in eval_expr (exemple_2).

(********** Exercice 2 **********)
(* Question 4 *)
Inductive element : Set :=
| Plus_symb : element
| Minus_symb : element
| Mult_symb : element
| Operande : Z -> element.

Definition liste_postfixe := list element.
(* Question 5 *)
Open Scope list_scope.

Definition exemple_3 := (Operande 2)::(Operande 5)::Plus_symb::(Operande 3)::Mult_symb::nil.
Definition exemple_4 := (Operande 2)::(Operande 1)::Minus_symb::(Operande 7)::(Operande 6)::Mult_symb::Plus_symb::(Operande 2)::Minus_symb::nil.

(* Question 6 *)
Definition pile := list Z.
Definition pile_nouv : pile := nil.

Definition empiler (l:pile) (e:Z) := e::l.

Definition depiler (l:pile) :=
match l with
| nil => nil
| a::b => b
end.

Definition sommet (l:pile) :=
match l with
| nil => (-1)
| a::b => a
end.

Fixpoint eval_postfixe2 (l:liste_postfixe) (p:pile) :=
match l with
| nil => p
| a::b => let s1 := sommet p in
          let p1 := depiler p in
          let s2 := sommet p1 in
          let p2 := depiler p1 in 
          eval_postfixe2 b (
            match a with
            | Plus_symb => empiler p2 (s1 + s2)
            | Minus_symb => empiler p2 (s2 - s1)
            | Mult_symb => empiler p2 (s1 * s2)
            | Operande o => empiler p o
            end
          )
end.

Definition eval_postfixe (l:liste_postfixe) := eval_postfixe2 l pile_nouv.

(* Question 8 *)
Eval compute in eval_postfixe exemple_3.
Eval compute in eval_postfixe exemple_4.

(********** Exercice 3 **********)
(* Question 9 *)
Fixpoint translate (e:expr) :=
match e with
| Plus a b => (translate a)++(translate b)++(Plus_symb::nil)
| Minus c d => (translate c)++(translate d)++(Minus_symb::nil)
| Mult e f => (translate e)++(translate f)++(Mult_symb::nil)
| Oper o => (Operande o)::nil
end.

Eval compute in translate exemple_1.
Eval compute in translate exemple_2.

(* Question 10 *)
Inductive well_formed : liste_postfixe -> Prop :=
| w_seul : forall (z:Z), well_formed ((Operande z)::nil)
| w_plus : forall (l1 l2:liste_postfixe), 
          well_formed l1 ->
          well_formed l2 ->
          well_formed (l1++l2++(Plus_symb::nil)) 
| w_moins : forall (l1 l2:liste_postfixe), 
          well_formed l1 ->
          well_formed l2 ->
          well_formed (l1++l2++(Minus_symb::nil))
| w_fois : forall (l1 l2:liste_postfixe), 
          well_formed l1 ->
          well_formed l2 ->
          well_formed (l1++l2++(Mult_symb::nil)).

(* Question 11 *)
Lemma wf_ok : forall (e:expr),
well_formed (translate e).
Proof.
intros.
induction e.
simpl.
apply w_plus;
assumption.
apply w_moins;
assumption.
apply w_fois;
assumption.
apply w_seul.
Qed.

(* Question 12 *)
Lemma append_eval : forall (e f:liste_postfixe), forall (p:pile),
eval_postfixe2 (e ++ f) p = eval_postfixe2 f (eval_postfixe2 e p).
Proof.
induction e.
simpl.
reflexivity.
intros.
simpl.
apply IHe.
Qed.

Lemma depiler_eval : forall (f:liste_postfixe),
well_formed f -> forall p:pile, p=depiler(eval_postfixe2 f p).
Proof.
intros.
simpl.

Qed.

(* Question 13 *)
Lemma lemma_plus : forall (e f:liste_postfixe), forall (p:pile),
well_formed e ->
well_formed f ->
sommet (eval_postfixe2 e p) + sommet (eval_postfixe2 f (eval_postfixe2 e p))=
sommet (eval_postfixe2 (e ++ (f ++ ((Plus_symb)::nil))) p).
Proof.
Qed.

(* Question 14 *)
Lemma lemma_minus : forall (e f:liste_postfixe), forall (p:pile),
well_formed e ->
well_formed f ->
sommet (eval_postfixe2 e p) + sommet (eval_postfixe2 f (eval_postfixe2 e p))=
sommet (eval_postfixe2 (e ++ (f ++ ((Minus_symb)::nil))) p).
Proof.
Qed.

Lemma lemma_mult: forall (e f:liste_postfixe), forall (p:pile),
well_formed e ->
well_formed f ->
sommet (eval_postfixe2 e p) + sommet (eval_postfixe2 f (eval_postfixe2 e p))=
sommet (eval_postfixe2 (e ++ (f ++ ((Mult_symb)::nil))) p).
Proof.
Qed.

(* Question 15 *)
Lemma interp_ok : forall e:expr,
eval_expr e = (eval_postfixe (translate e)).
Proof.
Qed.

Lemma interp_ok' : forall e:expr, forall p:pile,
eval_expr e = sommet (eval_postfixe2 (translate e) p).
Proof.
Qed.

























