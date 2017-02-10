Require Import List.
Require Import ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint find_min (l : list Z) (min : Z) : Z :=
  match l with
  | [] => min
  | h :: t => match Z_le_gt_dec h min with 
    | left _ => find_min t h
    | right _ => find_min t min
  end
  end.

Fixpoint remove (x : Z) (l : list Z) : list Z :=
    match l with
      | [] => []
      | y::tl => match (Z_eq_dec x y) with 
        |left _ => tl 
        |right _ => y::(remove x tl)
      end
    end.

Fixpoint selection_sort_support (l : list Z) (step: nat) : list Z :=
  match step with 
    | 0%nat => l
    | S step' => 
    match l with
        | [] => []
        | h:: t => let min := find_min l h 
          in min :: selection_sort_support (remove min (h :: t)) step'
    end
end.

Definition selection_sort (l : list Z) := selection_sort_support l (length l).

Eval compute in (remove 1 [1;2;3;4;1]). 
Eval compute in (selection_sort [10;5;0;0;45;1;5;3;4;2;1]). 





(* *)
Lemma select_perm : forall h t, equiv (selection_sort(h::t)) ((h:: selection_sort t)).
Proof.
  intros. induction t as [|h' t']. unfold  auto with sort.
  simpl. destruct (Z_le_gt_dec h h'); auto with sort.
  apply equiv_trans with (h' :: h :: t'); auto with sort. 
Qed.

Theorem selection_sort_correct : Sorting_correct selection_sort.
Proof.

  constructor. 
  intros. split.
  induction l. auto with sort. 
  assert (equiv (a :: l) (a :: selection_sort l)); auto with sort.
  apply equiv_trans with (l':=(a :: selection_sort l)). apply H. 
  apply equiv_sym. unfold selection_sort.
  unfold selection_sort. 







generalize dependent l.
  induction len as [|len']. intros. destruct l. auto with sort. 
   inversion Heqlen.
  unfold selection_sort in *. simpl. destruct (find_min_idx_aux l n 0 1) as [|n'] eqn: ret; auto.


  unfold selection_sort. 
 assert (equiv (a :: l) (a :: insertion_sort l)); auto with sort.
 apply equiv_trans with (l':=(a :: insertion_sort l)). apply H. 
 apply equiv_sym.
 apply insert_perm with (t:=(insertion_sort l)).
 induction l. simpl;auto with sort. 
  simpl. 
 apply aux_sorted. apply IHl. 
Qed. 





Definition sort :
  forall l:list Z, {l' : list Z | equiv l l' /\ sorted l'}.
 induction l as [| a l IHl]. 
 exists (nil (A:=Z)); split; auto with sort.
 case IHl; intros l' [H0 H1].
 exists (aux a l'). split.
 apply equiv_trans with (a :: l'). auto with sort.
 apply aux_equiv.
 apply aux_sorted; auto.
Defined.

Require Import PermutSetoid.

Lemma equiv_equiv: forall (l l':list Z) (x:Z), 
                  Permutation l l' -> Permutation (x:: l) (aux x l').
Proof. 
  intros.
  induction l'. rewrite permut_nil in H.



Theorem support: forall (l:list Z) (a:Z),
   Permutation (a :: l) (fold_right aux [] (a :: l)).
Proof. 
  intros. simpl. 






Lemma support: forall (l :list Z),
                  equiv l [] -> l = [].
Proof. 
  intro l; destruct l as [ | e l ]; trivial.
  assert().
  induction l.
  reflexivity. intros. contradiction. intros. 


Lemma equiv_equiv: forall (l l':list Z) (x:Z), 
                  equiv l l' -> equiv (x:: l) (aux x l').
Proof. 
  intros.
  induction l'. simpl. 


Lemma equiv_fold: forall (l:list Z) (x:Z), 
                  equiv l (fold_right aux [] l).
Proof.
intros.
  induction l. 
  auto with sort. 
 case (Z_le_gt_dec x a).
   simpl. intros.  apply equiv_cons with . auto with sort.
 intro; apply equiv_trans with (a :: x :: l0); 
   auto with sort.
  



      
apply equiv_trans with (fold_right aux [] (a :: l)). 



 apply equiv_trans with (a :: l'); auto with sort.
 apply aux_equiv.
 apply aux_sorted; auto.
Qed.
