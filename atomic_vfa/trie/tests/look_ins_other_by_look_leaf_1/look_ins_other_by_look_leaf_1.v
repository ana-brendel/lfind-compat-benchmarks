Load LFindLoad.
From lfind Require Import LFind.
Unset Printing Notations.
Set Printing Implicit.

From QuickChick Require Import QuickChick.
Require Import Arith.
Require Import Lia.

Inductive positive : Set :=
  | xI : positive -> positive
  | xO : positive -> positive
  | xH : positive.

Derive Show for positive. 
Derive Arbitrary for positive.  
Instance Dec_Eq_positive : Dec_Eq positive. 
Proof. dec_eq. Qed.

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

Notation "p ~ 1" := (xI p)
  (at level 7, left associativity, format "p '~' '1'").
 Notation "p ~ 0" := (xO p)
  (at level 7, left associativity, format "p '~' '0'").

Fixpoint positive2nat (p: positive) : nat :=
  match p with
  | xI q => 1 + 2 * positive2nat q
  | xO q => 0 + 2 * positive2nat q
  | xH => 1
 end.

Fixpoint succ x :=
match x with
  | p~1 => (succ p)~0
  | p~0 => p~1
  | xH => xH~0
end.

Fixpoint of_succ_nat (n:nat) : positive :=
  match n with
    | O => xH
    | S x => succ (of_succ_nat x)
  end.

Fixpoint nat2positive (n:nat) : positive :=
match n with
   | O => xH
   | S O => xH
   | S x => succ (nat2positive x)
end.
 
Fixpoint print_in_binary (p: positive) : listnat :=
  match p with
  | xI q => append (print_in_binary q) (cons 1 nil)
  | xO q => append (print_in_binary q) (cons 0 nil)
  | xH => cons 1 nil
 end.

Fixpoint addc (carry: bool) (x y: positive) {struct x} : positive :=
  match carry, x, y with
    | false, p~1, q~1 => (addc true p q)~0
    | false, p~1, q~0 => (addc false p q)~1
    | false, p~1, xH => (succ p)~0
    | false, p~0, q~1 => (addc false p q)~1
    | false, p~0, q~0 => (addc false p q)~0
    | false, p~0, xH => p~1
    | false, xH, q~1 => (succ q)~0
    | false, xH, q~0 => q~1
    | false, xH, xH => xH~0
    | true, p~1, q~1 => (addc true p q)~1
    | true, p~1, q~0 => (addc true p q)~0
    | true, p~1, xH => (succ p)~1
    | true, p~0, q~1 => (addc true p q)~0
    | true, p~0, q~0 => (addc false p q)~1
    | true, p~0, xH => (succ p)~0
    | true, xH, q~1 => (succ q)~1
    | true, xH, q~0 => (succ q)~0
    | true, xH, xH => xH~1
  end.

Definition add (x y: positive) : positive := addc false x y.

Inductive comparison : Set := Eq : comparison | Lt : comparison | Gt : comparison.

Fixpoint compare x y {struct x}:=
  match x, y with
    | p~1, q~1 => compare p q
    | p~1, q~0 => match compare p q with Lt => Lt | _ => Gt end
    | p~1, xH => Gt
    | p~0, q~1 => match compare p q with Gt => Gt | _ => Lt end
    | p~0, q~0 => compare p q
    | p~0, xH => Gt
    | xH, q~1 => Lt
    | xH, q~0 => Lt
    | xH, xH => Eq
  end.

Inductive LFType : Type := One | Two | Three | Four | Five | Six.

Inductive trie :=
  | Leaf : trie
  | Node : trie -> LFType -> trie -> trie.

Definition trie_table : Type := (LFType * trie)%type.

Definition empty (default: LFType) : trie_table := (default, Leaf).

Fixpoint look (default: LFType) (i: positive) (m: trie): LFType :=
    match m with
    | Leaf => default
    | Node l x r =>
        match i with
        | xH => x
        | xO i' => look default i' l
        | xI i' => look default i' r
        end
    end.

Definition lookup (i: positive) (t: trie_table) : LFType := look (fst t) i (snd t).

Fixpoint ins default (i: positive) (a: LFType) (m: trie): trie :=
    match m with
    | Leaf =>
        match i with
        | xH => Node Leaf a Leaf
        | xO i' => Node (ins default i' a Leaf) default Leaf
        | xI i' => Node Leaf default (ins default i' a Leaf)
        end
    | Node l o r =>
        match i with
        | xH => Node l a r
        | xO i' => Node (ins default i' a l) o r
        | xI i' => Node l o (ins default i' a r)
        end
    end.

Definition insert (i: positive) (a: LFType) (t: trie_table) : trie_table := (fst t, ins (fst t) i a (snd t)).

(* ################################################################# *)

Lemma succ_correct: forall p, positive2nat (succ p) = S (positive2nat p).
Proof. Admitted.

Lemma addc_correct: forall (c: bool) (p q: positive), positive2nat (addc c p q) = (if c then 1 else 0) + positive2nat p + positive2nat q.
Proof.
  intros c p. generalize dependent c. induction p. intros. simpl. destruct c. destruct q.
  simpl. specialize (IHp true q). simpl in IHp. lia.
  simpl. specialize (IHp true q). simpl in IHp. lia.
  simpl. 
  (* HELPER LEMMA $ addc_correct_by_succ_correct_1 $ *)
  rewrite succ_correct. lia.
  destruct q. simpl. specialize (IHp true q). simpl in IHp. lia.
  simpl. specialize (IHp false q). simpl in IHp. lia.
  simpl. 
  (* HELPER LEMMA $ addc_correct_by_succ_correct_2 $ *)
  rewrite succ_correct. lia.
  intros. simpl. destruct c. destruct q.
  simpl. specialize (IHp true q). simpl in IHp. lia.
  simpl. specialize (IHp false q). simpl in IHp. lia.
  simpl. 
  (* HELPER LEMMA $ addc_correct_by_succ_correct_3 $ *)
  rewrite succ_correct. lia.
  destruct q. simpl. specialize (IHp false q). simpl in IHp. lia.
  simpl. specialize (IHp false q). simpl in IHp. lia.
  simpl. lia.
  intros. simpl. destruct c. destruct q.
  simpl.  
  (* HELPER LEMMA $ addc_correct_by_succ_correct_4 $ *)
  rewrite succ_correct. lia.
  simpl. 
  (* HELPER LEMMA $ addc_correct_by_succ_correct_5 $ *)
  rewrite succ_correct. lia.
  simpl. reflexivity.
  destruct q. simpl. 
  (* HELPER LEMMA $ addc_correct_by_succ_correct_6 $ *)
  rewrite succ_correct. lia.
  simpl. lia. simpl. reflexivity.
Qed.
  

Theorem add_correct: forall (p q: positive), positive2nat (add p q) = positive2nat p + positive2nat q.
Proof. 
  intros. unfold add. 
  (* HELPER LEMMA $ add_correct_by_positive2nat_pos_1 $ *)
  apply addc_correct. 
Qed.

Lemma positive2nat_pos: forall p, positive2nat p > 0.
Proof. intros. induction p; simpl; lia. Qed.

Theorem compare_correct:
 forall x y,
  match compare x y with
  | Lt => positive2nat x < positive2nat y
  | Eq => positive2nat x = positive2nat y
  | Gt => positive2nat x > positive2nat y
 end.
Proof.
  induction x; destruct y; simpl.
  specialize (IHx y). destruct (compare x y); lia.
  specialize (IHx y). destruct (compare x y); lia.
  assert (positive2nat x > 0). 
  (* HELPER LEMMA $ compare_correct_by_positive2nat_pos_1 $ *)
  apply positive2nat_pos. lia.
  specialize (IHx y). destruct (compare x y); lia.
  specialize (IHx y). destruct (compare x y); lia.
  assert (positive2nat x > 0). 
  (* HELPER LEMMA $ compare_correct_by_positive2nat_pos_2 $ *)
  apply positive2nat_pos. lia.
  assert (positive2nat y > 0). 
  (* HELPER LEMMA $ compare_correct_by_positive2nat_pos_3 $ *)
  apply positive2nat_pos. lia.
  assert (positive2nat y > 0). 
  (* HELPER LEMMA $ compare_correct_by_positive2nat_pos_4 $ *)
  apply positive2nat_pos. lia.
  reflexivity.
Qed.

(* ================================================================= *)
(** ** Lemmas About the Relation Between [lookup] and [insert] *)

Lemma look_leaf: forall a j, look a j Leaf = a.
Proof. intros. destruct j; reflexivity. Qed.

Lemma look_ins_same: forall a k v t, look a k (ins a k v t) = v.
Proof.
  induction k. intros. simpl. destruct t. apply (IHk v Leaf). apply (IHk v t2).
  intros. simpl. destruct t. apply (IHk v Leaf). apply (IHk v t1).
  intros. simpl. destruct t. reflexivity. reflexivity.
Qed.


Lemma look_ins_other: forall a j k v t, j <> k -> look a j (ins a k v t) = look a j t.
Proof.
  induction j; destruct k; intros; simpl; auto.
  - destruct t. rewrite (IHj k v Leaf). 
  (* HELPER LEMMA $ look_ins_other_by_look_leaf_1 $ *)
  Admitted.
(*
  apply look_leaf. unfold not. intros. rewrite H0 in H. contradiction. 
    rewrite (IHj k v t2). reflexivity. unfold not. intros. rewrite H0 in H. contradiction. 
  - destruct t. 
  (* HELPER LEMMA $ look_ins_other_by_look_leaf_2 $ *)
  apply look_leaf. reflexivity.
  - destruct t. 
  (* HELPER LEMMA $ look_ins_other_by_look_leaf_3 $ *)
  apply look_leaf. reflexivity.
  - destruct t. 
  (* HELPER LEMMA $ look_ins_other_by_look_leaf_4 $ *)
  apply look_leaf. reflexivity.
  - destruct t. rewrite (IHj k v Leaf). 
  (* HELPER LEMMA $ look_ins_other_by_look_leaf_5 $ *)
  apply look_leaf. unfold not. intros. rewrite H0 in H. contradiction. 
    rewrite (IHj k v t1). reflexivity. unfold not. intros. rewrite H0 in H. contradiction. 
  - destruct t. 
  (* HELPER LEMMA $ look_ins_other_by_look_leaf_6 $ *)
  apply look_leaf. reflexivity.
  - destruct t. reflexivity. reflexivity.
  - destruct t. reflexivity. reflexivity.
  - destruct t. contradict H. reflexivity. contradict H. reflexivity.
Qed. 
*)