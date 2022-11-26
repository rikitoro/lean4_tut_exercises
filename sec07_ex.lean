
section
namespace Hidden

inductive List (α : Type u) where
| nil   : List α
| cons  : α → List α → List α

namespace List

def append (as bs : List α) : List α :=
  match as with 
  | nil       => bs
  | cons a as => cons a (append as bs)

theorem nil_append (as : List α) : append nil as = as := 
  rfl

theorem cons_append (a : α) (as bs : List α)
  : append (cons a as) bs = cons a (append as bs) := by
  rfl

theorem append_nil (as : List α) : append as nil = as :=
  List.recOn (motive := fun as => append as nil = as)
    as
    (show append nil nil = nil from rfl)
    (fun (a : α) (as : List α) (ih : append as nil = as) =>
      show append (cons a as) nil = cons a as from
      calc
        append (cons a as) nil = cons a (append as nil) := by rw [cons_append]
        _ = cons a as := by rw [ih]
    )

theorem append_assoc (as bs cs : List α)
  : append (append as bs) cs = append as (append bs cs) :=
  List.recOn
  ( 
    motive := fun as =>
      append (append as bs) cs  = append as (append bs cs)
  )
  as 
  (
    show append (append nil bs) cs = append nil (append bs cs) from rfl
  )
  (
    fun (a : α) (as : List α)
      (ih : append (append as bs) cs = append as (append bs cs)) =>
      show append (append (cons a as) bs) cs = append (cons a as) (append bs cs) from
      calc
        append (append (cons a as) bs) cs 
          = append (cons a (append as bs)) cs := by rw [cons_append]
        _ = cons a (append (append as bs) cs) := by rw [cons_append]
        _ = cons a (append as (append bs cs)) := by rw [ih]
        _ = append (cons a as) (append bs cs) := by rw [←cons_append]
  )

end List
end Hidden
end

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
open List

def length : List α → Nat
  | nil     => 0
  | _ :: as => 1 + length as

def reverse : List α → List α
  | nil     => nil
  | a :: as => reverse as ++ a :: nil

#eval length $ (nil : List Nat)
#eval length $ 1 :: 2 :: 3 :: nil

#eval reverse $ (nil : List Nat)
#eval reverse $ 3 :: 1 :: 4 :: 1 :: nil


theorem length_append (s t : List α) 
  : length (s ++ t) = length s + length t :=
  List.recOn
  (
    motive := fun s => 
      length (s ++ t) = length s + length t
  )
  s
  (
    show length (nil ++ t) = length nil + length t from
    calc 
      length (nil ++ t) = length t := by rw [List.nil_append]
      _ = 0 + length t := by rw [Nat.zero_add]
      _ = length nil + length t := by rfl
  )
  (
    fun (x : α) (s : List α)
      (ih : length (s ++ t) = length s + length t) =>
      show length (x :: s ++ t) = length (x :: s) + length t from
      calc
        length (x :: s ++ t) = length (x :: (s ++ t)) := by rw [cons_append]
        _ = 1 + length (s ++ t) := by rfl
        _ = 1 + (length s + length t) := by rw [ih]
        _ = (1 + length s) + length t := by rw [Nat.add_assoc]
        _ = length (x :: s) + length t := by rfl
  )
  
example (t : List α)
  : length (reverse t) = length t :=
  List.recOn
  (
    motive := fun t => length (reverse t) = length t
  )
  t
  (
    show length (reverse nil) = length nil from rfl
  )
  (
    fun (x : α)(t : List α)
      (ih : length (reverse t) = length t) => 
      show length (reverse (x :: t)) = length (x :: t) from
      calc
        length (reverse (x :: t)) 
          = length (reverse t ++ x :: nil) := by rfl
        _ = length (reverse t) + length (x :: nil) := by rw [length_append]
        _ = length t + length (x :: nil) := by rw [ih]
        _ = length t + 1 := by rfl
        _ = 1 + length t := by rw [Nat.add_comm]
        _ = length (x :: t) := by rfl
  )
  
theorem reverse_append (s t : List)
  : reverse (s ++ t) = reverse t ++ reverse s := by
  induction s with
  | nil => 
  | cons x s ih => 


/-
example (t : List α)
  : reverse (reverse t) = t := by
  induction t with
  | nil =>
    rfl
  | cons x t ih =>
    rw [reverse]
    rw [ih]
-/

end Hidden2 
end