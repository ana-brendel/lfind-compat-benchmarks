Load LFindLoad.
From lfind Require Import LFind.
Unset Printing Notations.
Set Printing Implicit.

From QuickChick Require Import QuickChick.
Require Import Arith.

Inductive value := 
| Positive : nat -> value
| Negative : nat -> value.

Inductive color := Red | Black.

Inductive tree : Type :=
| E : tree
| T : color -> tree -> nat -> value -> tree -> tree.

Definition empty_tree : tree := E.

Fixpoint lookup (default : value) (x: nat) (t : tree) : value :=
    match t with
    | E => default
    | T _ tl k v tr => if x <? k then lookup default x tl
                    else if k <? x then lookup default x tr
                            else v
    end.

Definition make_black (t : tree) : tree :=
    match t with
    | E => E
    | T _ a x vx b => T Black a x vx b
    end.

Definition balance (rb : color) (t1 : tree) (k : nat) (vk : value) (t2 : tree) : tree :=
    match rb with
    | Red => T Red t1 k vk t2
    | _ => match t1 with
        | T Red (T Red a x vx b) y vy c =>
            T Red (T Black a x vx b) y vy (T Black c k vk t2)
        | T Red a x vx (T Red b y vy c) =>
            T Red (T Black a x vx b) y vy (T Black c k vk t2)
        | _ => match t2 with
                | T Red (T Red b y vy c) z vz d =>
            T Red (T Black t1 k vk b) y vy (T Black c z vz d)
                | T Red b y vy (T Red c z vz d)  =>
            T Red (T Black t1 k vk b) y vy (T Black c z vz d)
                | _ => T Black t1 k vk t2
                end
        end
    end.

Fixpoint ins (x : nat) (vx : value) (t : tree) : tree :=
    match t with
    | E => T Red E x vx E
    | T c a y vy b => if x <? y then balance c (ins x vx a) y vy b
                    else if y <? x then balance c a y vy (ins x vx b)
                            else T c a x vx b
    end.

Definition insert (x : nat) (vx : value) (t : tree) := make_black (ins x vx t).

Fixpoint ForallT (P : nat -> value -> Prop) (t : tree) {struct t} : Prop :=
  match t with
  | E => True
  | T _ l k v r => P k v /\ ForallT P l /\ ForallT P r
  end.

(* Proof of decidability for ForallT *)

Inductive BST : tree -> Prop :=
| BST_E : BST E
| BST_T : forall (c : color) (l : tree) (k : nat) (v : value) (r : tree),
    ForallT (fun k' _ => k' < k) l ->
    ForallT (fun k' _ => k' > k) r ->
    BST l ->
    BST r ->
    BST (T c l k v r).

(* Proof of decidability for BST *)

Lemma lookup_make_black : forall (default : value) (t : tree) (k : nat), lookup default k (make_black t) = lookup default k t.
Proof. intros. destruct t; simpl; auto. Qed.

Theorem lookup_insert_eq : forall (default : value) (t : tree) (k : nat) (v : value), BST t -> lookup default k (insert k v t) = v.
Proof. Admitted.

Theorem lookup_insert_neq : forall (default : value) (t : tree) (k k' : nat) (v : value), BST t -> k <> k' -> lookup default k' (insert k v t) = lookup default k' t.
Proof.
    intros. unfold insert. 
    (* HELPER LEMMA $ lookup_insert_neq_by_lookup_make_black $ *)
    Admitted.
    (*
        rewrite lookup_make_black. 
        (* HELPER LEMMA $ lookup_insert_neq_by_lookup_ins_eq $ *)
        apply lookup_ins_neq. assumption. assumption.
    Qed.
    *)