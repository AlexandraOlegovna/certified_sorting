Require Import List.
Require Import ZArith.
Import ListNotations.
Require Import Bool.
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
      | left _ =>  is_minumum z l'
      | right _ => false
      end
  end.

Eval compute in is_minumum 5 [8;7;6;9].


Lemma my4: forall (l:list Z) (z:Z), sorted (z::l) -> is_minumum z l = true.
Proof. 
induction l. simpl. auto.
intros. simpl. case(Z_le_gt_dec z a). intro. 
apply my3 in H. apply IHl in H. auto with sort. intro.
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

Lemma my7: forall (x: Z), x = x.
Proof.
  intros. auto.
Qed.

Lemma nb_occ_nil: forall  (l : list Z), (forall (a : Z),  nb_occ a l = 0%nat) -> l = [].
Proof.
  induction l. simpl. auto.  
  intro. assert (H0:=H a). simpl in H0. case (Z.eq_dec a a) in H0.
  symmetry in H0. Check O_S. apply O_S in H0. contradiction. assert (HH:= my7 a). contradiction.
Qed.



Lemma equiv_nil: forall (l : list Z), equiv l [] -> l = [].
  induction l. auto. intro.
  unfold equiv. apply nb_occ_nil in H. apply H. 
Qed.

Lemma equiv_0: forall (l l' :list Z) (z: Z), equiv (z::l) (z::l') -> equiv l l'.
Proof.
  unfold equiv. intros l l' z H z0.
  assert (H1:= H z0). simpl in H1. case (Z.eq_dec z0 z) in H1. apply eq_add_S in H1. auto. auto.
Qed.

Lemma equiv_1: forall (l l' :list Z) (z: Z), equiv l l' -> equiv (z::l) (z::l').
Proof.
  unfold equiv. intros l l' z H z0.
  assert (H1:= H z0). simpl. case (Z.eq_dec z0 z). intros. apply eq_S.  auto. auto.
Qed.

Lemma my8: forall (l: list Z) (z a: Z), is_minumum z l = true -> z <=a -> is_minumum z (a::l) = true.
Proof.
  intros. simpl. case (Z_le_gt_dec z a). intros. auto. intros. contradiction.
Qed.


Lemma my10: forall (l:list Z) (a:Z), equiv (a::l) [a] -> (a::l) = [a].
Proof.
  induction l. intros. auto. 
  intros. assert (H1:=IHl a0). 
  unfold equiv in H. assert (H2:= H a). simpl in H2. case (Z.eq_dec a a0) in H2. case (Z.eq_dec a a) in H2. symmetry in H2.
  apply eq_add_S in H2. apply O_S in H2. contradiction. assert (HH:= my7 a). contradiction. 
  case (Z.eq_dec a a) in H2. symmetry in H2. apply O_S in H2. contradiction. assert (HH:= my7 a). contradiction. 
Qed.

Lemma my11: forall  (a b:Z) (l:list Z), equiv (a::l) [b] -> ((a = b) /\ ((a::l) = [a])).
Proof.
  intros a b. case (Z.eq_dec a b). intros. split. auto. apply my10. symmetry in e. rewrite e in H. auto.
  intros. unfold equiv in H. assert (H1:= H a).
  simpl in H1. case (Z.eq_dec a a) in H1. case (Z.eq_dec a b) in H1. contradiction. 
    symmetry in H1. apply O_S in H1. contradiction. assert (HH:= my7 a). contradiction.
Qed.


Definition minimum (m:Z) (l:list Z) := 
    forall z:Z, (nb_occ z l > 0)%nat -> m <= z.


Lemma my77: forall (x: nat), (x > x)%nat -> False.
Proof.
  intros. assert (H1:=eq_refl x). inversion H. intuition. intuition. 
Qed.

Lemma my777: forall (x: Z), (x > x) -> False.
Proof.
  intros. assert (H1:=eq_refl x). inversion H. intuition.
Qed.

Lemma my12: forall (l:list Z) (m:Z), sorted (m::l) -> minimum m l.
Proof.
  induction l. intros. unfold minimum. intros. simpl in H0. assert(H2:=my77 0). apply H2 in H0. contradiction.
  intros. assert (H0:= IHl m). assert(H4:=H). apply my3 in H. apply H0 in H. case (Z_le_gt_dec m a).
  intros. unfold minimum. intros. unfold minimum in H. assert (H2:=H z). simpl in H1. case (Z.eq_dec z a) in H1.
  symmetry in e. rewrite e in l0. auto. apply H2. apply H1.
  intros. inversion H4. contradiction.
Qed.

Lemma my13: forall (x:nat), (S x > 0)%nat.
Proof.
  intros. induction x. auto. auto.
Qed.

Lemma my14: forall (l:list Z) (m:Z), sorted l -> minimum m l -> sorted (m::l).
Proof.
  induction l. auto with sort.
  intros. case (Z_le_gt_dec m a). intros. apply my6 with l m a in H. apply H. auto. 
  intros. assert(H4:=H0). unfold minimum in H0. assert(H1:=H0 a). simpl in H1. case (Z.eq_dec a a) in H1.
  assert (H2:=my13 (nb_occ a l)). apply H1 in H2. contradiction. assert (H2:= my7 a). contradiction.
Qed.

Lemma min_eq: forall (l l':list Z) (m:Z), equiv l l' -> minimum m l -> minimum m l'.
Proof.
  intros. unfold minimum. intros. unfold minimum in H0. apply H0. unfold equiv in H. assert (H2:=H z).
  rewrite H2. apply H1.
Qed.

Lemma my15: forall (l:list Z) (a x:Z), minimum a l -> a <= x -> minimum a (x::l).
Proof.
  unfold minimum. intros. simpl in H1. case (Z.eq_dec z x) in H1. symmetry in e. rewrite e in H0. apply H0.
  assert (H2:=H z). apply H2 in H1. apply H1.
Qed.

Lemma my16: forall (a x: Z), x > a -> a <= x.
Proof.
  intros. intuition.
Qed.

Lemma bubble_sorted :
 forall (l:list Z) (x:Z), sorted l -> sorted (bubble x l).
Proof.
induction l. simpl; auto with sort.
intros. simpl. assert (H1 := H). case (Z_le_gt_dec x a). intro.
apply my2 in H. apply IHl with a in H. apply my6 with l x a in H1.
apply my12 in H1. apply my14. apply H. Check bubble_equiv. assert (H2:= bubble_equiv l a). 
apply min_eq with (a :: l) . apply H2. apply H1. apply l0.
intros. apply my2 in H. apply IHl with x in H. apply my14. apply H. 
assert (H2:=bubble_equiv l x). apply min_eq with (x::l). apply H2. apply my15. apply my12 in H1.
apply H1. apply my16. apply g.
Qed.


Definition Z_sort :
  forall l:list Z, {l' : list Z | equiv l l' /\ sorted l'}.
 induction l as [| a l IHl]. 
 exists (nil (A:=Z)); split; auto with sort.
 case IHl; intros l' [H0 H1].
 exists (bubble a l'). split.
 apply equiv_trans with (a :: l'). auto with sort.
 apply bubble_equiv.
 apply bubble_sorted; auto.
Defined.




Extraction "insert-sort" aux sort.





