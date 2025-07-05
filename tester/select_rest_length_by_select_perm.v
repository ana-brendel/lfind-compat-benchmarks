(** * Selection:  Selection Sort *)
(* Some proofs from: https://github.com/kolya-vasiliev/verified-functional-algorithms-2019/blob/master/Selection.v *)

(* Load LFindLoad.
From lfind Require Import LFind.
Unset Printing Notations.
Set Printing Implicit. *)

(* Require Import vfa_selection_benchmarks.Definitions.
From vfa_selection_benchmarks Require Import Decide. *)

(* These specify the libraries of functions that should be considered during synthesis that 
    are not defined within the above libraries. *)
(* Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.  *)

Inductive listnat : Type :=
    | nil : listnat
    | cons : nat -> listnat -> listnat.

Fixpoint leb n m : bool :=
  match n, m with
    | 0, _ => true
    | _, 0 => false
    | S n', S m' => leb n' m'
  end.

Fixpoint select (x: nat) (l: listnat) : nat * listnat :=
  match l with
  | nil => (x, nil)
  | cons h t =>
    if leb x h
    then let (j, l') := select x t
         in (j, cons h l')
    else let (j, l') := select h t
         in (j, cons x l')
  end.

Inductive Permutation : listnat -> listnat -> Prop :=
| perm_nil: Permutation nil nil
| perm_skip x l l' : Permutation l l' -> Permutation (cons x l) (cons x l')
| perm_swap x y l : Permutation (cons y (cons x l)) (cons x (cons y l))
| perm_trans l l' l'' :
    Permutation l l' -> Permutation l' l'' -> Permutation l l''.

(* ################################################################# *)

(* Lemma select_perm: forall x l y r, select x l = (y, r) -> Permutation (cons x l) (cons y r).
Proof. 
    intros x l; revert x.
    induction l.
    - simpl. intros. inversion H.  auto.
    - simpl. intros. bdestruct (x <=? a).
    -- destruct (select x l) eqn:Q. inversion H.
    apply perm_trans with (a :: y :: l0).
    apply perm_trans with (a :: x :: l).
    apply perm_swap.
    apply perm_skip. apply IHl. rewrite <- H2. assumption.
    apply perm_swap.
    -- specialize (IHl a). destruct (select a l) eqn:Q. 
    inversion H.
    apply perm_trans with (x :: y :: l0).
    apply perm_skip. apply IHl. rewrite H2. reflexivity.
    apply perm_swap.
Qed. *)

Lemma select_rest_length : forall x l y r, select x l = (y, r) -> length l = length r.
Proof.
    intros. 
        lfind. Admitted.

    (* apply select_perm in H.
    apply Permutation_length in H. 
    auto.
Qed. *)
