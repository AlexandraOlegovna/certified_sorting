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
  | nil => O
  | (z' :: l') =>
      match Z_eq_dec z z' with
      | left _ => S(nb_occ z l')
      | right _ => nb_occ z l'
      end
  end.

Print nb_occ.

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







Fixpoint bubble (z:Z) (l:list Z) : list Z :=
  match l with
  | nil => z :: nil
  | cons a l' =>
      match Z_le_gt_dec z a with
      | left _ =>  z :: (bubble a l')
      | right _ => a :: (bubble z l')
      end
  end.
   

Eval compute in bubble 5 [7;0;1;2;3;6].

Lemma bubble_equiv : forall (l:list Z) (x:Z), 
                  equiv (x :: l) (bubble x l).
Proof.
 induction l as [|a l0 H] ; auto with sort.
 intros x. simpl. case (Z_le_gt_dec x a).
   intros. auto with sort.
 intro; apply equiv_trans with (a :: x :: l0);
   auto with sort.
Qed.

(*Lemma help: forall (l:list Z) (x:Z) (z:Z), sorted (x::z::l) -> sorted (x::l).
Proof. 
intros. 
induction l. auto with sort. inversion H. inversion H4. apply sorted2.
rewrite H2. rewrite H7. auto with sort zarith. auto with sort zarith.
Qed.*)

Lemma my1: forall (l:list Z) (x:Z) (z:Z), sorted (x::l) -> (z<=x)-> sorted (z::l).
Proof.
  intros. induction l. auto with sort. apply sorted2. rewrite H0. 
  inversion H. apply H3. inversion H. apply H5.
Qed.

Lemma my2: forall (l:list Z) (x:Z), sorted (x::l) -> sorted l.
Proof.
  intros. induction l. auto with sort. inversion H. apply H4.
Qed.

Fixpoint max (a b: Z) : Z :=
match Z_le_gt_dec a b with
      | left _ =>  a
      | right _ => b
end.

Fixpoint maximum (e:Z) (l:list Z) {struct l} : Z :=
  match l with 
    | nil => e
    | x :: xs => max x (maximum e xs)
  end.

Fixpoint last_elem (e:Z) (l:list Z) {struct l} : Z := 
  match l with 
  | [] => e
  | [x] => x
  |x::xs => last_elem e xs
end.  

Lemma my3 : forall (l:list Z) (a b:Z), sorted (a::b::l) -> sorted (a::l).
Proof.
  intros. induction l. auto with sort. inversion H.
  apply my1 with (a0::l) b a in H4.
 apply H4. apply H2.
Qed.

Fixpoint is_minumum (z:Z) (l:list Z) {struct l} : bool :=
  match l with 
    | nil => true
    | a :: l' => 
      match Z_le_gt_dec z a with
      | left _ =>  is_minumum a l'
      | right _ => false
      end
  end.

Eval compute in is_minumum 1 [1;2;3;4].


Lemma my4: forall (l:list Z) (z:Z), sorted (z::l) -> is_minumum z l = true.
Proof. 
induction l. simpl. auto.
intros. simpl. case(Z_le_gt_dec z a). intro. 
apply my2 in H. apply IHl in H. auto with sort. intro.
inversion H. contradiction.
Qed.

Lemma my5: forall (l:list Z) (z:Z), sorted l -> is_minumum z l = true -> sorted (z::l).
Proof. 
induction l. simpl. intros. auto with sort.
intros. inversion H0. case (Z_le_gt_dec z a) in H2. 
auto with sort. inversion H2.
Qed.

Lemma my6: forall (l : list Z) (x a: Z), sorted (a::l) -> x<=a -> sorted (x::a::l).
Proof.
  auto with sort.
Qed.

Lemma bubble_sorted :
 forall (l:list Z) (x:Z), sorted l -> sorted (bubble x l).
Proof.
induction l. simpl; auto with sort.
intros. simpl. case (Z_le_gt_dec x a). intro.
assert (H1 := H).
apply my2 in H. apply IHl with a in H. apply my6 with l x a in H1.
apply my4 in H1. apply my5. apply H. 

Lemma min_eq: forall (l l':list Z) (z:Z), equiv l l' -> is_minumum z l = true -> is_minumum z l' = true.
Proof.
  induction l.
Lemma equiv_nil: forall (l : list Z) (a:Z), equiv [] (a::l) -> equiv [] l.
  unfold equiv. simpl. intros l a H z. 

Lemma nb_occ_nil: forall (l : list Z) (a : Z),  nb_occ a l = 0%nat -> l = [].
Proof.
  induction l. simpl. auto. simpl. intro a0. case (Z.eq_dec a0 a). intros.
  set (x:=nb_occ a0 l) in H. symmetry in H. apply O_S in H. contradiction. revert a0. intros. 
  apply IHl with a0 in H.












Lemma my7: forall (l : list Z) (a:Z), equiv [] (a::l) -> equiv [] l.
Proof.
  unfold equiv. intros. simpl. simpl in H. case (Z.eq_dec z a) in H. apply H with z.

Lemma my7: forall (l l':list Z) (z:Z), equiv l l' -> is_minumum z l = true -> is_minumum z l' = true.
Proof.
  induction l.
  induction l'. intros. auto with sort. intros. simpl. case (Z_le_gt_dec z a). intros.
  apply IHl' with a in H0. apply H0. unfold equiv in H. simpl in H. case (Z.eq_dec z a) in H.





induction l.
simpl. intros. case (Z_le_gt_dec x a) ; intro; simpl; auto with sort zarith. 

intros.
simpl. case (Z_le_gt_dec x a). intros. 
induction l.
simpl. case (Z_le_gt_dec x) ; intro; simpl; auto with sort zarith. 
case (Z_le_gt_dec x a). intros.  simpl. case (Z_le_gt_dec a a0). intros.



elim l.
intros.
simpl. auto with sort. simpl. 
case (Z_le_gt_dec x a). intro; simpl; auto with sort zarith. intro. 
simpl. auto with sort zarith.
intros. apply my3 in H0. apply H with x in H0.
simpl. simpl in H0. case (Z_le_gt_dec x a). case (Z_le_gt_dec x a) in H0.
intros. case (Z_le_gt_dec a a0). intros. 


elim H.
apply my2 in H. apply IHl in H. 
simpl; auto with sort. simpl.
intro z. case (Z_le_gt_dec x z). simpl; auto with sort zarith. 
simpl. auto with sort zarith. 

intros z1 z2 l2 H1. case (Z_le_gt_dec x z2). case (Z_le_gt_dec x z1).
intros. simpl. case (Z_le_gt_dec x z1).  case (Z_le_gt_dec z1 z2). intros. 
apply sorted2. auto with sort.
apply my1 with l3 z2 z1 in H1. apply my2 in H. apply IHl in H1.


intro. apply sorted2. auto with arith.
induction x. inversion g.
Check Z_le_lt_eq_dec.
intro. 

case (Z_le_gt_dec x a). simpl; 
   auto with sort zarith.
 intros z1 z2. case (Z_le_gt_dec z1 z2). case (Z_le_gt_dec x z1). 
 case (Z_le_gt_dec x z2). intros. apply sorted2. auto with sort zarith. 
  



 intros a b. case (Z_le_gt_dec x b). simpl. intros.
  case (Z_le_gt_dec x a). case (Z_le_gt_dec a b).
auto with sort.  intros.  case (Z_le_gt_dec z1 z2). auto with sort zarith.
Qed.

Lemma my6: forall (l:list Z), equiv l l' -> l=[].
Proof.

unfold equiv. simpl. Check trans_eq. eauto. unfold nb_occ. eauto. simpl. 

Lemma my6: forall (l l':list Z) (z:Z), equiv l l' -> is_minumum z l = true -> is_minumum z l' = true.
Proof.
induction l.
induction l'.
auto with sort zarith. intros. apply IHl' with z in H0. simpl in H.

  intros. simpl in H0. inversion H. assert (l' = nil). apply equiv_sym in H. auto with sort zarith.



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





