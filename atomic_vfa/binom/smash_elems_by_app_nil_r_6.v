Load LFindLoad.
From lfind Require Import LFind.
Unset Printing Notations.
Set Printing Implicit.

From QuickChick Require Import QuickChick.
Require Import Arith.
Require Import Lia.

Inductive listnat : Type :=
| nil : listnat
| cons : nat -> listnat -> listnat.

Derive Show for listnat. 
Derive Arbitrary for listnat.  
Instance Dec_Eq_listnat : Dec_Eq listnat. 
Proof. dec_eq. Qed.

Fixpoint append (n : listnat) (m : listnat) :=
  match n with 
  | nil => m
  | cons h t => cons h (append t m)
  end.

Lemma app_nil_r : forall l, append l nil = l. Proof. Admitted.

Inductive Permutation : listnat -> listnat -> Prop :=
  | perm_nil : Permutation nil nil
  | perm_skip : forall (x : nat) (l l' : listnat),
                Permutation l l' ->
                Permutation (cons x l) (cons x l')
  | perm_swap : forall (x y : nat) (l : listnat),
                Permutation (cons y (cons x l)) (cons x (cons y l))
  | perm_trans : forall l l' l'' : listnat,
                 Permutation l l' ->
                 Permutation l' l'' ->
                 Permutation l l''.

(* Proof of decidability for permutation *)

Lemma Permutation_refl : forall l, Permutation l l. Proof. Admitted.

Lemma Permutation_trans : forall l l' l'', Permutation l l' -> Permutation l' l'' -> Permutation l l''.
Proof. Admitted.

Lemma Permutation_app : forall l l' m m', Permutation l l' -> Permutation m m' -> Permutation (append l m) (append l' m').
Proof. Admitted.

Lemma Permutation_app_comm : forall l l', Permutation (append l l') (append l' l). Proof. Admitted.

Inductive tree : Type :=
|  Node: nat -> tree -> tree -> tree
|  Leaf : tree.

Derive Show for tree. 
Derive Arbitrary for tree.  
Instance Dec_Eq_tree : Dec_Eq tree. 
Proof. dec_eq. Qed.

Inductive tree_elems: tree -> listnat -> Prop :=
| tree_elems_leaf: tree_elems Leaf nil
| tree_elems_node:  forall bl br v tl tr b,
           tree_elems tl bl ->
           tree_elems tr br ->
           Permutation b (cons v (append bl br)) ->
           tree_elems (Node v tl tr) b.

Fixpoint pow2heapp (n: nat) (m: nat) (t: tree) :=
 match n, m, t with
    0, m, Leaf       => True
  | 0, m, Node _ _ _  => False
  | S _, m,Leaf    => False
  | S n', m, Node k l r  =>
       m >= k /\ pow2heapp n' k l /\ pow2heapp n' m r
 end.

Definition pow2heap (n: nat) (t: tree) :=
  match t with
    Node m t1 Leaf => pow2heapp n m t1
  | _ => False
  end.

Definition gtb (n m : nat) := m <? n.
Hint Unfold gtb : core.
Infix ">?" := gtb (at level 70) : nat_scope.

Definition smash (t u:  tree) : tree :=
  match t , u with
  |  Node x t1 Leaf, Node y u1 Leaf =>
                   if  (x >? y) then Node x (Node y u1 t1) Leaf
                                else Node y (Node x t1 u1) Leaf
  | _ , _ => Leaf  (* arbitrary bogus tree *)
  end.

(* ################################################################# *)
(** * Proof of Algorithm Correctness *)

Theorem smash_elems: forall n t u bt bu, pow2heap n t -> pow2heap n u -> tree_elems t bt -> 
  tree_elems u bu -> tree_elems (smash t u) (append bt bu).
Proof.
  intros. unfold pow2heap in H. unfold pow2heap in H0. destruct t.
  - destruct u.
  -- destruct t2. 
  --- contradict H.
  --- destruct u2.
  + contradict H0.
  + simpl. destruct (n0 >? n1).
  ++ inversion H1. inversion H2. apply (tree_elems_node (cons n1 (append bl0 bl)) nil).
  +++ eapply tree_elems_node. apply H13. apply H6. apply Permutation_refl.
  +++ apply tree_elems_leaf.
  +++ simpl. inversion H15. rewrite <- H18 in H16. inversion H8. rewrite <- H19 in H9. 
  (* HELPER LEMMA $ smash_elems_by_app_nil_r_1 $ *)
  rewrite app_nil_r. 
  (* HELPER LEMMA $ smash_elems_by_app_nil_r_2 $ *)
  rewrite app_nil_r in H9.
  (* HELPER LEMMA $ smash_elems_by_app_nil_r_3 $ *)
  rewrite app_nil_r in H16.
  (* HELPER LEMMA $ smash_elems_by_Permutation_trans_1 $ *)
  apply (@Permutation_trans _ (append (cons n0 bl) (cons n1 bl0)) _).
  * (* HELPER LEMMA $ smash_elems_by_Permutation_app_1 $ *)
  apply Permutation_app. assumption. assumption.
  * simpl. apply perm_skip. 
  (* HELPER LEMMA $ smash_elems_by_Permutation_app_comm_1 $ *)
  apply Permutation_app_comm.
  ++ inversion H1. inversion H2. apply (tree_elems_node (cons n0 (append bl bl0)) nil).
  +++ eapply tree_elems_node. apply H6. apply H13. apply Permutation_refl.
  +++ apply tree_elems_leaf.
  +++ simpl. inversion H15. rewrite <- H18 in H16. inversion H8. rewrite <- H19 in H9. 
  (* HELPER LEMMA $ smash_elems_by_app_nil_r_4 $ *)
  rewrite app_nil_r. 
  (* HELPER LEMMA $ smash_elems_by_app_nil_r_5 $ *)
  rewrite app_nil_r in H9.
  (* HELPER LEMMA $ smash_elems_by_app_nil_r_6 $ *)
  Admitted.

  (* rewrite app_nil_r in H16. 
  apply (@Permutation_trans _ (append (cons n0 bl) (cons n1 bl0)) _).
  apply Permutation_app. assumption. assumption.
  apply (@Permutation_trans _ (append (cons n1 bl0) (cons n0 bl)) _). 
  apply Permutation_app_comm. simpl. apply perm_skip. 
  apply Permutation_app_comm.
  -- contradict H0.
  - contradict H.
Qed.
  *)