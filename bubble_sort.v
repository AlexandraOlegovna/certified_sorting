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


Lemma sorted_subs: forall (l:list Z) (x:Z) (z:Z), sorted (x::l) -> (z<=x)-> sorted (z::l).
Proof.
  intros. induction l. auto with sort. apply sorted2. rewrite H0. 
  inversion H. apply H3. inversion H. apply H5.
Qed.

Lemma sorted_elim_fst: forall (l:list Z) (a:Z), sorted (a::l) -> sorted l.
Proof.
  intros. induction l. auto with sort. inversion H. apply H4.
Qed.

Lemma sorted_elim_snd : forall (l:list Z) (a b:Z), sorted (a::b::l) -> sorted (a::l).
Proof.
  intros. induction l. auto with sort. inversion H.
  apply sorted_subs with (a0::l) b a in H4. apply H4. apply H2.
Qed.

Lemma sorted_add: forall (l : list Z) (x a: Z), sorted (a::l) -> x<=a -> sorted (x::a::l).
Proof.
  auto with sort.
Qed.

(*Lemma my7: forall (x: Z), x = x.
Proof.
  intros. auto.
Qed.*)

Lemma nb_occ_nil: forall  (l : list Z), (forall (a : Z),  nb_occ a l = 0%nat) -> l = [].
Proof.
  induction l. simpl. auto.  
  intro. assert (H0:=H a). simpl in H0. case (Z.eq_dec a a) in H0.
  symmetry in H0. Check O_S. apply O_S in H0. contradiction. intuition. (*assert (HH:= eq_refl a). contradiction. *)
Qed.

Lemma equiv_nil: forall (l : list Z), equiv l [] -> l = [].
  induction l. auto. intro.
  unfold equiv. apply nb_occ_nil in H. apply H. 
Qed.

Lemma equiv_elim: forall (l l' :list Z) (z: Z), equiv (z::l) (z::l') -> equiv l l'.
Proof.
  unfold equiv. intros l l' z H z0.
  assert (H1:= H z0). simpl in H1. case (Z.eq_dec z0 z) in H1. apply eq_add_S in H1. auto. auto.
Qed.

Lemma equiv_add: forall (l l' :list Z) (z: Z), equiv l l' -> equiv (z::l) (z::l').
Proof.
  unfold equiv. intros l l' z H z0.
  assert (H1:= H z0). simpl. case (Z.eq_dec z0 z). intros. apply eq_S. auto. auto.
Qed.


Lemma equiv_cons1: forall (l:list Z) (a:Z), equiv (a::l) [a] -> (a::l) = [a].
Proof.
  induction l. intros. auto. 
  intros. assert (H1:=IHl a0). 
  unfold equiv in H. assert (H2:= H a). simpl in H2. case (Z.eq_dec a a0) in H2. case (Z.eq_dec a a) in H2. symmetry in H2.
  
  apply eq_add_S in H2. apply O_S in H2. contradiction.
  intuition. (*assert (HH:= eq_refl a). (**???*) contradiction. *)
  case (Z.eq_dec a a) in H2. symmetry in H2. apply O_S in H2. contradiction. intuition. (* assert (HH:= eq_refl a). (**???**) contradiction. *)
Qed.

Lemma equiv_cons2: forall  (a b:Z) (l:list Z), equiv (a::l) [b] -> ((a = b) /\ ((a::l) = [a])).
Proof.
  intros a b. case (Z.eq_dec a b). intros. split. auto. apply equiv_cons1. symmetry in e. rewrite e in H. auto.
  intros. unfold equiv in H. assert (H1:= H a).
  simpl in H1. case (Z.eq_dec a a) in H1. case (Z.eq_dec a b) in H1. contradiction. 
    symmetry in H1. apply O_S in H1. contradiction. intuition. (*assert (HH:= eq_refl a). contradiction.*)
Qed.

Definition minimum (m:Z) (l:list Z) := 
    forall z:Z, (nb_occ z l > 0)%nat -> m <= z.

Eval compute in minimum 5 [1;2;3].

(*Lemma help1: forall (x: nat), (x > x)%nat -> False.
Proof.
  intros. assert (H1:=eq_refl x). inversion H. intuition. intuition. 
Qed.*)

Lemma sorted_min: forall (l:list Z) (m:Z), sorted (m::l) -> minimum m l.
Proof.
  induction l. intros. unfold minimum. intros. simpl in H0. intuition. (*assert(H2:=help1 0). apply H2 in H0. contradiction.*)
  intros. assert (H0:= IHl m). assert(H4:=H). apply sorted_elim_snd in H. apply H0 in H. case (Z_le_gt_dec m a).
  intros. unfold minimum. intros. unfold minimum in H. assert (H2:=H z). simpl in H1. case (Z.eq_dec z a) in H1.
  symmetry in e. rewrite e in l0. auto. apply H2. apply H1.
  intros. inversion H4. contradiction.
Qed.

(*Lemma help2: forall (x:nat), (S x > 0)%nat.
Proof.
  intros. induction x. auto. auto.
Qed.*)

Lemma min_sorted: forall (l:list Z) (m:Z), sorted l -> minimum m l -> sorted (m::l).
Proof.
  induction l. auto with sort.
  intros. case (Z_le_gt_dec m a). intros. apply sorted_add with l m a in H. apply H. auto. 
  intros. assert(H4:=H0). unfold minimum in H0. assert(H1:=H0 a). simpl in H1. case (Z.eq_dec a a) in H1. 
  intuition. intuition.
  (*assert (H2:=help2 (nb_occ a l)). apply H1 in H2. contradiction. assert (H2:= eq_refl a). contradiction.*)
Qed.

Lemma min_eq: forall (l l':list Z) (m:Z), equiv l l' -> minimum m l -> minimum m l'.
Proof.
  intros. unfold minimum. intros. unfold minimum in H0. apply H0. unfold equiv in H. assert (H2:=H z).
  rewrite H2. apply H1.
Qed.

Lemma minimum_cons: forall (l:list Z) (a x:Z), minimum a l -> a <= x -> minimum a (x::l).
Proof.
  unfold minimum. intros. simpl in H1. case (Z.eq_dec z x) in H1. symmetry in e. rewrite e in H0. apply H0.
  assert (H2:=H z). apply H2 in H1. apply H1.
Qed.

(*Lemma help3: forall (a x: Z), x > a -> a <= x.
Proof.
  intros. intuition.
Qed.*)

Lemma bubble_sorted :
 forall (l:list Z) (x:Z), sorted l -> sorted (bubble x l).
Proof.
induction l. simpl; auto with sort.
intros. simpl. assert (H1 := H). case (Z_le_gt_dec x a). intro.
apply sorted_elim_fst in H. apply IHl with a in H. apply sorted_add with l x a in H1.
apply sorted_min in H1. apply min_sorted. apply H. Check bubble_equiv. assert (H2:= bubble_equiv l a). 
apply min_eq with (a :: l) . apply H2. apply H1. apply l0.
intros. apply sorted_elim_fst in H. apply IHl with x in H. apply min_sorted. apply H. 
assert (H2:=bubble_equiv l x). apply min_eq with (x::l). apply H2. apply minimum_cons. apply sorted_min in H1.
apply H1. intuition. (*apply my16. apply g.*)
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



Extraction Language Haskell.
Extraction "/Users/User/Documents/IndependentWork/InsertionSort/certified_sorting/bubble_sort.hs" bubble Z_sort.





