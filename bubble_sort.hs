module Bubble_sort where

import qualified Prelude

__ :: any
__ = Prelude.error "Logical or arity value used"

data List a =
   Nil
 | Cons a (List a)

list_rect :: a2 -> (a1 -> (List a1) -> a2 -> a2) -> (List a1) -> a2
list_rect f f0 l =
  case l of {
   Nil -> f;
   Cons y l0 -> f0 y l0 (list_rect f f0 l0)}

list_rec :: a2 -> (a1 -> (List a1) -> a2 -> a2) -> (List a1) -> a2
list_rec =
  list_rect

data Comparison =
   Eq
 | Lt
 | Gt

compOpp :: Comparison -> Comparison
compOpp r =
  case r of {
   Eq -> Eq;
   Lt -> Gt;
   Gt -> Lt}

type Sig a =
  a
  -- singleton inductive, whose constructor was exist
  
data Sumbool =
   Left
 | Right

sumbool_rect :: (() -> a1) -> (() -> a1) -> Sumbool -> a1
sumbool_rect f f0 s =
  case s of {
   Left -> f __;
   Right -> f0 __}

sumbool_rec :: (() -> a1) -> (() -> a1) -> Sumbool -> a1
sumbool_rec =
  sumbool_rect

data Positive =
   XI Positive
 | XO Positive
 | XH

data Z =
   Z0
 | Zpos Positive
 | Zneg Positive

compare_cont :: Comparison -> Positive -> Positive -> Comparison
compare_cont r x y =
  case x of {
   XI p ->
    case y of {
     XI q -> compare_cont r p q;
     XO q -> compare_cont Gt p q;
     XH -> Gt};
   XO p ->
    case y of {
     XI q -> compare_cont Lt p q;
     XO q -> compare_cont r p q;
     XH -> Gt};
   XH ->
    case y of {
     XH -> r;
     _ -> Lt}}

compare :: Positive -> Positive -> Comparison
compare =
  compare_cont Eq

compare0 :: Z -> Z -> Comparison
compare0 x y =
  case x of {
   Z0 ->
    case y of {
     Z0 -> Eq;
     Zpos _ -> Lt;
     Zneg _ -> Gt};
   Zpos x' ->
    case y of {
     Zpos y' -> compare x' y';
     _ -> Gt};
   Zneg x' ->
    case y of {
     Zneg y' -> compOpp (compare x' y');
     _ -> Lt}}

z_le_dec :: Z -> Z -> Sumbool
z_le_dec x y =
  case compare0 x y of {
   Gt -> Right;
   _ -> Left}

z_le_gt_dec :: Z -> Z -> Sumbool
z_le_gt_dec x y =
  sumbool_rec (\_ -> Left) (\_ -> Right) (z_le_dec x y)

bubble :: Z -> (List Z) -> List Z
bubble z l =
  case l of {
   Nil -> Cons z Nil;
   Cons a l' ->
    case z_le_gt_dec z a of {
     Left -> Cons z (bubble a l');
     Right -> Cons a (bubble z l')}}

z_sort :: (List Z) -> (List Z)
z_sort l =
  list_rec Nil (\a _ iHl -> bubble a iHl) l

