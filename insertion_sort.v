Require Import List.
Require Import ZArith.
Import ListNotations.
Open Scope Z_scope.



Inductive sorted : list Z -> Prop :=
  | sorted0 : sorted nil
  | sorted1 : forall z:Z, sorted (z :: nil)
  | sorted2 :
      forall (z1 z2:Z) (l:list Z),
        z1 <= z2 ->
        sorted (z2 :: l) -> sorted (z1 :: z2 :: l).

Hint Resolve sorted0 sorted1 sorted2 : sort.


Fixpoint nb_occ (z:Z) (l:list Z) {struct l} : nat :=
  match l with
  | nil => 0%nat
  | (z' :: l') =>
      match Z_eq_dec z z' with
      | left _ => S (nb_occ z l')
      | right _ => nb_occ z l'
      end
  end.

Definition equiv (l l':list Z) := 
    forall z:Z, nb_occ z l = nb_occ z l'.

Lemma equiv_refl : forall l:list Z, equiv l l.
Proof.
 unfold equiv. trivial.
Qed.

Lemma equiv_sym : forall l l':list Z, equiv l l' -> equiv l' l.
Proof.
  unfold equiv. 
  intros l l' H. symmetry. apply H.
Qed.

Lemma equiv_trans :
 forall l l' l'':list Z, equiv l l' -> 
                         equiv l' l'' -> 
                         equiv l l''.
Proof.
 intros l l' l'' H H0 z.
 eapply trans_eq; eauto.
Qed.

Lemma equiv_cons :
 forall (z:Z) (l l':list Z), equiv l l' -> 
                             equiv (z :: l) (z :: l').
Proof.
 intros z l l' H z'. 
 simpl; case (Z_eq_dec z' z); auto. 
Qed.

Lemma equiv_perm :
 forall (a b:Z) (l l':list Z),
   equiv l l' -> 
   equiv (a :: b :: l) (b :: a :: l').
Proof.
 intros a b l l' H z; simpl.
 case (Z_eq_dec z a); case (Z_eq_dec z b); 
  simpl; case (H z); auto.
Qed.

Hint Resolve equiv_cons equiv_refl equiv_perm : sort.







Fixpoint aux (z:Z) (l:list Z) : list Z :=
  match l with
  | nil => z :: nil
  | cons a l' =>
      match Z_le_gt_dec z a with
      | left _ =>  z :: a :: l'
      | right _ => a :: (aux z l')
      end
  end.
   

Lemma aux_equiv : forall (l:list Z) (x:Z), 
                  equiv (x :: l) (aux x l).
Proof.
 induction l as [|a l0 H] ; auto with sort.
 intros x. simpl. case (Z_le_gt_dec x a).
   intros. auto with sort.
 intro; apply equiv_trans with (a :: x :: l0);
   auto with sort.
Qed.

Lemma aux_sorted :
 forall (l:list Z) (x:Z), sorted l -> sorted (aux x l).
Proof.
 intros l x H; elim H; simpl; auto with sort.
 intro z; case (Z_le_gt_dec x z); simpl; 
   auto with sort zarith.
 intros z1 z2; case (Z_le_gt_dec x z2); simpl; intros;
  case (Z_le_gt_dec x z1); simpl; auto with sort zarith.
Qed.

Check fold_right.
(* fold_right : forall A B : Type, (B -> A -> A) -> A -> list B -> A *)

Definition insertion_sort (l : list Z) := fold_right (aux) ([]) (l).

Eval compute in (insertion_sort [1;3;5;6;1;2;0;-1;1]).


Inductive Sorting_correct (algo : list Z -> list Z) :=
| info:
   (forall l:list Z, equiv l (algo l) /\ sorted (algo l)) -> Sorting_correct algo.

Lemma insert_perm : forall h t, equiv (aux h t) (h :: t).
Proof.
  intros. induction t as [|h' t']; auto with sort.
  simpl. destruct (Z_le_gt_dec h h'); auto with sort.
  apply equiv_trans with (h' :: h :: t'); auto with sort. 
Qed.

Theorem insertion_sort_correct : Sorting_correct insertion_sort.
Proof.
  constructor. 
  intros. split.
  induction l as [| a l IHl]. 
  simpl. auto with sort. simpl.
  assert (equiv (a :: l) (a :: insertion_sort l)); auto with sort.
  apply equiv_trans with (l':=(a :: insertion_sort l)). apply H. 
  apply equiv_sym.
  apply insert_perm with (t:=(insertion_sort l)).
  induction l. simpl;auto with sort. 
  simpl. 
  apply aux_sorted. apply IHl. 
Qed. 


Definition Z_sort :
  forall l:list Z, {l' : list Z | equiv l l' /\ sorted l'}.
 induction l as [| a l IHl]. 
 exists (nil (A:=Z)); split; auto with sort.
 case IHl; intros l' [H0 H1].
 exists (aux a l'). split.
 apply equiv_trans with (a :: l'). auto with sort.
 apply aux_equiv.
 apply aux_sorted; auto.
Defined.




Extraction "insert-sort" aux sort.





