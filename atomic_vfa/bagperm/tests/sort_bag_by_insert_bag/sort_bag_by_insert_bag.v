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
Proof.
  unfold bag_eqv. intros. induction l.
  simpl. reflexivity.
  simpl. 
  (* HELPER LEMMA $ sort_bag_by_insert_bag $ *)
  Admitted.
  (* rewrite <- insert_bag. simpl. rewrite IHl. reflexivity.
Qed. *)