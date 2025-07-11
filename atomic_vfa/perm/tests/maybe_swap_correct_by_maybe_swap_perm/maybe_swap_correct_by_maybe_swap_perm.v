Load LFindLoad.
From lfind Require Import LFind.
Unset Printing Notations.
Set Printing Implicit.

From QuickChick Require Import QuickChick.
Require Import Arith.

Inductive listnat : Type :=
| nil : listnat
| cons : nat -> listnat -> listnat.

Derive Show for listnat. 
Derive Arbitrary for listnat.  
Instance Dec_Eq_listnat : Dec_Eq listnat. 
Proof. dec_eq. Qed.

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

Definition maybe_swap (al: listnat) : listnat :=
  match al with
  | cons a (cons b ar) => if b <? a then cons b (cons a ar) else cons a (cons b ar)
  | _ => al
  end.

Definition first_le_second (al: listnat) : Prop :=
  match al with
  | cons a (cons b _) => a <= b
  | _ => True
  end.

Theorem maybe_swap_perm: forall al, Permutation al (maybe_swap al).
Proof. Admitted.

Theorem maybe_swap_correct: forall al, Permutation al (maybe_swap al) /\ first_le_second (maybe_swap al).
Proof.
  intros. split.
  - (* HELPER LEMMA $ maybe_swap_correct_by_maybe_swap_perm $ *)
  Admitted.
  (*
    apply maybe_swap_perm.
    - unfold maybe_swap.
      destruct al as [ | a [ | b al]]; simpl; auto.
      bdestruct (a >? b); simpl; lia.
  Qed.
  *)