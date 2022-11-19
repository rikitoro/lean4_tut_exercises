section
namespace Hidden1
open Nat

def mul (m n : Nat) : Nat :=
  match n with
  | 0      => 0
  | succ n => m + mul m n

#eval mul 3 0
#eval mul 3 2

def pred (n : Nat) : Nat :=
  match n with
  | 0       => 0
  | succ n  => n

#eval pred 0
#eval pred 1
#eval pred 3

def trunc_sub (m n : Nat) : Nat :=
  match n with
  | 0       => m
  | succ n' => trunc_sub (pred m) n'

#eval trunc_sub 10 3
#eval trunc_sub 3 4
#eval trunc_sub 0 2


def exp (m n : Nat) : Nat :=
  match n with
  | 0       => 1
  | succ n' => mul m (exp m n')

#eval exp 2 0
#eval exp 2 3
#eval exp 3 2
#eval exp 0 0

end Hidden1
end

section
namespace Hidden2
inductive List (α : Type u) where
  | nil   : List α
  | cons  : α → List α → List α
  deriving Repr
namespace List

def append (as bs : List α)  : List α :=
  match as with
  | nil       => bs
  | cons a as => cons a (append as bs)

def length (as : List α) : Nat :=
  match as with
  | nil       => 0
  | cons _ as => 1 + length as

#eval length $ cons 3 $ cons 1 $ cons 4 $ cons 1 nil

def reverse (as : List α) : List α :=
  match as with
  | nil       => as
  | cons a as => append (reverse as) (cons a nil)

#eval reverse $ cons 3 $ cons 1 $ cons 4 $ cons 1 nil


example (s t : List α) : 
  length (append s l) = length s + length l := by
  sorry
  

end List
end Hidden2
end