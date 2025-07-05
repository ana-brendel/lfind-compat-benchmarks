Load LFindLoad.
From lfind Require Import LFind.
Unset Printing Notations.
Set Printing Implicit.

Fixpoint geb n m : bool :=
  match n, m with
    | 0, _ => false
    | _, 0 => true
    | S n', S m' => geb n' m'
  end.

Inductive listnat : Type :=
    | nil : listnat
    | cons : nat -> listnat -> listnat.

Fixpoint select (i: nat) (l: listnat) : nat * listnat :=
match l with
|  nil => (i, nil)
|  cons h t => if geb i h
               then let (j, l') := select i t in (j, cons h l')
               else let (j,l') := select h t in (j, cons i l')
end. 

Inductive Permutation : listnat -> listnat -> Prop :=
| perm_nil: Permutation nil nil
| perm_skip x l l' : Permutation l l' -> Permutation (cons x l) (cons x l')
| perm_swap x y l : Permutation (cons y (cons x l)) (cons x (cons y l))
| perm_trans l l' l'' :
    Permutation l l' -> Permutation l' l'' -> Permutation l l''.

Inductive Forall (P : nat -> Prop) : listnat -> Prop :=
 | Forall_nil : Forall P nil
 | Forall_cons : forall x l, P x -> Forall P l -> Forall P (cons x l).

Fixpoint length (l:listnat) : nat :=
    match l with
      | nil => 0
      | cons _ m => S (length m)
    end.

Definition delete_max (p: listnat) :=
  match p with
  | cons i p' => Some (select i p')
  | nil => None
  end.

Lemma select_perm: forall i l j r, select i l = (j, r) -> Permutation (cons i l) (cons j r).
Proof. Admitted.

Lemma forall_permutation: forall P (l l' : listnat), Permutation l l' -> Forall P l -> Forall P l'.
Proof. Admitted.

Lemma symmetry_permutation: forall (l l' : listnat), Permutation l l' <-> Permutation l' l.
Proof. Admitted.

Definition priq (p: listnat) := True.

Definition Abs (p : listnat) (kl : listnat) := Permutation p kl.

Lemma delete_max_Some_relate: forall (p q: listnat) k (pl ql: listnat), priq p ->
  Abs p pl -> delete_max p = Some (k,q) -> Abs q ql -> Permutation pl (cons k ql) /\ Forall (ge k) ql.
Proof.
  induction p. intros. discriminate. 
  intros. simpl in H1. inversion H1. split.
  (* HELPER LEMMA $ delete_max_Some_relate_by_Permutation_trans_1 $ *)
  apply perm_trans with (l' := cons n p).
  apply symmetry_permutation. assumption. 
  (* HELPER LEMMA $ delete_max_Some_relate_by_Permutation_trans_2 $ *)
  apply perm_trans with (l' := cons k q).
  (* HELPER LEMMA $ delete_max_Some_relate_by_select_perm $ *)
  apply select_perm. assumption. 
  apply perm_skip. assumption.
  (* HELPER LEMMA $ delete_max_Some_relate_by_forall_permutation $ *)
  apply forall_permutation with (l := q). assumption.
  (* HELPER LEMMA $ delete_max_Some_relate_by_select_biggest $ *)
  Admitted.
(*
  apply (select_biggest a p). assumption.
Qed.
*)