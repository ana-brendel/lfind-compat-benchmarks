Load LFindLoad.
From lfind Require Import LFind.
Unset Printing Notations.
Set Printing Implicit.

From QuickChick Require Import QuickChick.
Require Import Arith.
From Coq Require Export Bool.Bool.

Lemma eqb_reflect : forall x y, reflect (x = y) (x =? y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply Nat.eqb_eq.
Qed.

Lemma ltb_reflect : forall x y, reflect (x < y) (x <? y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply Nat.ltb_lt.
Qed.

Lemma leb_reflect : forall x y, reflect (x <= y) (x <=? y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply Nat.leb_le.
Qed.

Hint Resolve ltb_reflect leb_reflect eqb_reflect : bdestruct.

Ltac bdestruct X :=
  let H := fresh in let e := fresh "e" in
   evar (e: Prop);
   assert (H: reflect e X); subst e;
    [eauto with bdestruct
    | destruct H as [H|H];
       [ | try first [apply not_lt in H | apply not_le in H]]].

Inductive listnat : Type :=
| nil : listnat
| cons : nat -> listnat -> listnat.

Fixpoint append (n : listnat) (m : listnat) :=
  match n with 
  | nil => m
  | cons h t => cons h (append t m)
  end.

Derive Show for listnat. 
Derive Arbitrary for listnat.  
Instance Dec_Eq_listnat : Dec_Eq listnat. 
Proof. dec_eq. Qed.

Fixpoint insert (i : nat) (l : listnat) :=
  match l with
  | nil => cons i nil
  | cons h t => if i <=? h then (cons i (cons h t)) else (cons h (insert i t))
  end.

Fixpoint sort (l : listnat) : listnat :=
  match l with
  | nil => nil
  | cons h t => insert h (sort t)
  end.

Definition bag := listnat.

(* Derive Show for bag. 
Derive Arbitrary for bag.  
Instance Dec_Eq_bag : Dec_Eq bag. 
Proof. dec_eq. Qed. *)

Fixpoint count (v:nat) (s:bag) : nat :=
  match s with
  | nil => 0
  | cons h t =>
      (if (h =? v) then 1 else 0) + count v t
  end.

Definition bag_eqv (b1 b2: bag) : Prop := forall n, count n b1 = count n b2. 

Lemma bag_eqv_refl : forall b, bag_eqv b b.
Proof. unfold bag_eqv. intros. reflexivity. Qed.

Lemma bag_eqv_sym: forall b1 b2, bag_eqv b1 b2 -> bag_eqv b2 b1. 
Proof. unfold bag_eqv. intros. symmetry. apply H. Qed.

Lemma bag_eqv_trans: forall b1 b2 b3, bag_eqv b1 b2 -> bag_eqv b2 b3 -> bag_eqv b1 b3.
Proof. unfold bag_eqv. intros. rewrite H. apply H0. Qed.

Lemma bag_eqv_cons : forall x b1 b2, bag_eqv b1 b2 -> bag_eqv (cons x b1) (cons x b2).
Proof. unfold bag_eqv. intros. simpl. rewrite H. reflexivity. Qed.

Lemma insert_bag: forall x l, bag_eqv (cons x l) (insert x l).
Proof. Admitted.

Theorem sort_bag: forall l, bag_eqv l (sort l).
  unfold bag_eqv. intros. induction l.
  simpl. reflexivity.
  simpl. 
  (* HELPER LEMMA $ sort_bag_by_insert_bag $ *)
  rewrite <- insert_bag. simpl. rewrite IHl. reflexivity.
Qed.

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

Lemma Permutation_middle : forall l1 l2 a, Permutation (cons a (append l1 l2)) (append l1 (cons a l2)). 
Proof. Admitted.

Lemma Permutation_middle_fixed : forall al n n0 x x0, Permutation (cons n al) (cons n (append (cons n0 x) x0)) -> Permutation (cons n al) (append (cons n0 x) (cons n x0)).
Proof. Admitted.

Lemma perm_bag: forall al bl : listnat, Permutation al bl -> bag_eqv al bl. 
Proof. Admitted.

Lemma bag_nil_inv : forall b, bag_eqv nil b -> b = nil. 
Proof. Admitted.

Lemma bag_cons_inv : forall l x n, S n = count x l -> exists l1 l2, l = append l1 (cons x l2) /\ count x (append l1 l2) = n.
Proof. Admitted.

Lemma count_insert_other : forall l1 l2 x y, y <> x -> count y (append l1 (cons x l2)) = count y (append l1 l2).
Proof. Admitted.

Lemma bag_eqv_uncons : forall b l1 l2, bag_eqv (cons b l1) (cons b l2) -> bag_eqv l1 l2.
Proof. Admitted.

Lemma app_comm_cons : forall (x y : listnat) (a : nat), cons a (append x y) = append (cons a x) y.
Proof. Admitted.

Lemma bag_perm: forall al bl, bag_eqv al bl -> Permutation al bl.
Proof.
  induction al.
  - intros. apply bag_nil_inv in H. rewrite H. constructor.
  - intros. destruct bl. unfold bag_eqv in H. 
  assert (count n (cons n al) = count n nil). apply H. simpl in H0. bdestruct (n =? n).
  simpl in H0. inversion H0. contradiction H1. reflexivity.
  bdestruct (n =? n0). rewrite H0. constructor. apply IHal. rewrite <- H0 in H. 
  (* HELPER LEMMA $ bag_perm_by_bag_eqv_uncons $ *)
  apply (bag_eqv_uncons n). assumption.
  unfold bag_eqv in H. assert (count n (cons n al) = count n (cons n0 bl)). apply H. simpl in H1. 
  bdestruct (n =? n). bdestruct (n0 =? n).
  rewrite H3 in H0. contradiction H0. simpl in H1.
  (* HELPER LEMMA $ bag_perm_by_bag_cons_inv $ *)
  apply bag_cons_inv in H1. inversion H1. inversion H4. inversion H5.
  assert (Permutation al (cons n0 (append x x0))). apply IHal. unfold bag_eqv. intros.
  bdestruct (n1 =? n). rewrite H8. simpl. bdestruct (n0 =? n). rewrite H9 in H3. contradiction H3.
  simpl. rewrite H7. reflexivity. rewrite H6 in H. 
  assert (count n0 (cons n al) = count n0 (append (cons n0 x) (cons n x0))). apply H. 
  (* HELPER LEMMA $ bag_perm_by_app_comm_cons_1 $ *)
  rewrite app_comm_cons.
  (* HELPER LEMMA $ bag_perm_by_count_insert_other $ *)
  rewrite <- (count_insert_other (cons n0 x) x0 n n1). rewrite <- H.
  simpl. bdestruct (n =? n1). rewrite H10 in H8. contradiction H8. reflexivity. reflexivity.  
  assumption. apply (perm_skip n) in H8. 
  (* HELPER LEMMA $ bag_perm_by_app_comm_cons_2 $ *)
  rewrite app_comm_cons in H8. 
  (* HELPER LEMMA $ bag_perm_by_Permutation_middle $ *)
  Admitted.
  (* apply Permutation_middle_fixed in H8. simpl in H8. rewrite <- H6 in H8. assumption.
  contradiction H2. reflexivity.
Qed. *)
 