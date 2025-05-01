import Katydid.Std.Linter.DetectClassical
import Katydid.Std.Ordering
import Katydid.Std.Lists

structure NonEmptyList (α: Type) where
  head : α
  tail : List α

namespace NonEmptyList

def compare [o: Ord α] (xs ys: NonEmptyList α): Ordering :=
  match xs with
  | NonEmptyList.mk x' xs' =>
  match ys with
  | NonEmptyList.mk y' ys' =>
    Ordering.lex (Ord.compare x' y') (Ord.compare xs' ys')

instance [Ord α] : Ord (NonEmptyList α) where
  compare := compare

def cons (x: α) (xs: NonEmptyList α): NonEmptyList α :=
  NonEmptyList.mk x (xs.head :: xs.tail)

def toList (xs: NonEmptyList α): List α :=
  match xs with
  | NonEmptyList.mk head tail =>
    head :: tail

instance [Ord α] : LE (NonEmptyList α) where
  le (x: NonEmptyList α) (y: NonEmptyList α) :=
    LE.le x.toList y.toList

def merge' [Ord α] (xs: NonEmptyList α) (ys: NonEmptyList α): List α :=
  List.merge (xs.toList) (ys.toList) (fun x y => (Ord.compare x y).isLE)

def merge [Ord α] (xs: NonEmptyList α) (ys: NonEmptyList α): NonEmptyList α :=
  match xs with
  | NonEmptyList.mk x1 xs1 =>
  match ys with
  | NonEmptyList.mk y1 ys1 =>
  match Ord.compare x1 y1 with
  | Ordering.eq =>
    NonEmptyList.mk x1 (Lists.merge xs1 ys1)
  | Ordering.lt =>
    NonEmptyList.mk x1 (Lists.merge xs1 (y1::ys1))
  | Ordering.gt =>
    NonEmptyList.mk y1 (Lists.merge (x1::xs1) ys1)

def eraseReps' [BEq α] (x: α) (xs: List α): List α :=
  match xs with
  | [] => []
  | (x1::xs') =>
    if x1 == x
    then eraseReps' x xs'
    else x1 :: eraseReps' x1 xs'

def eraseReps [BEq α] (xs: NonEmptyList α): NonEmptyList α :=
  match xs with
  | NonEmptyList.mk x xs =>
    NonEmptyList.mk x (eraseReps' x xs)

def mergeReps [BEq α] [Ord α] (xs ys : NonEmptyList α): NonEmptyList α :=
  eraseReps (merge xs ys)
