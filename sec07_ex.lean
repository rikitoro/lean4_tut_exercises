
section Other_Recursive_Data_Types
namespace Hidden

inductive List (α : Type u) where
  | nil   : List α
  | cons  : α → List α → List α

namespace List

def append (as bs : List α) : List α :=
  match as with 
  | nil       => bs
  | cons a as => cons a (append as bs)

theorem nil_append (as : List α) : append nil as = as := by
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

-- tactics version
theorem append_nil' (as : List α) : append as nil = as := by
  induction as with
    | nil => 
      rfl
    | cons a as' ih => 
      calc
        append (cons a as') nil = cons a (append as' nil) := by rfl
        _ = cons a as' := by rw [ih]


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

-- tactics version
theorem append_assoc' (as bs cs : List α)
  : append (append as bs) cs = append as (append bs cs) := by
  induction as with
  | nil => 
    calc
      append (append nil bs) cs = append nil (append bs cs) := by rfl
  | cons a as' ih =>
    -- show append (append (cons a as') bs) cs = append (cons a as') (append bs cs) from
    calc 
      append (append (cons a as') bs) cs = append (cons a (append as' bs)) cs := by rfl
      _ = cons a (append (append as' bs) cs) := by rfl
      _ = cons a (append as' (append bs cs)) := by rw [ih]
      _ = append (cons a as') (append bs cs) := by rfl

end List
end Hidden
end Other_Recursive_Data_Types

/- ------------------------------------- -/

section Inductive_Families
namespace Hidden'

inductive Eq {α : Sort u} (a : α) : α → Prop where
  | refl : Eq a a 

theorem subst {α : Type u} {a b : α} {p : α → Prop} (h₁ : Eq a b) (h₂ : p a) 
  : p b := by
  induction h₁ with
    | refl =>
      exact h₂

theorem symm {α : Type u} {a b : α} (h : Eq a b) 
  : Eq b a := by 
  induction h with
    | refl => exact Eq.refl

theorem trans {α : Type u} {a b c : α} (h₁ : Eq a b) (h₂ : Eq b c)
  : Eq a c := by
  induction h₁ with
    | refl => assumption

theorem congr {α β : Type u} {a b : α} (f : α → β) (h : Eq a b)
  : Eq (f a) (f b) := by
  induction h with
    | refl => exact Eq.refl

end Hidden'
end Inductive_Families

/- ------------------------------------- -/

section ex1
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
end ex1 

/- ------------------------------------- -/

section ex2
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

-- tactics version 
theorem length_append' (s t : List α)
  : length (s ++ t) = length s + length t := by
  induction s with
  | nil => 
    calc
      length (nil ++ t) = length t := by rw [List.nil_append]
      _ = 0 + length t := by rw [Nat.zero_add]
      _ = length nil + length t := by rfl
  | cons head tail ih =>
    calc
      length (head :: tail ++ t) = length (head :: (tail ++ t)) := by rfl
      _ = 1 + length (tail ++ t) := by rfl
      _ = 1 + (length tail + length t) := by rw [ih]
      _ = 1 + length tail + length t := by simp [Nat.add_assoc]
      _ = length (head :: tail) + length t := by rfl
  
example (t : List α)
  : length (reverse t) = length t :=
  List.recOn
  (
    motive := fun t => length (reverse t) = length t
  )
  t
  (
    show length (reverse nil) = length nil from by rfl
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
  
theorem reverse_nil : reverse (nil : List α) = nil := rfl

theorem reverse_append (s t : List α)
  : reverse (s ++ t) = reverse t ++ reverse s := 
  List.recOn
  (
    motive := fun s => reverse (s ++ t) = reverse t ++ reverse s
  )
  s
  (
    show reverse (nil ++ t) = reverse t ++ reverse nil from
    calc
      reverse (nil ++ t) = reverse t := by rw [nil_append]
      _ = reverse t ++ nil := by rw [append_nil]
      _ = reverse t ++ reverse nil := rfl
  )
  (
    fun (x : α) (s : List α)
      (ih : reverse (s ++ t) = reverse t ++ reverse s) => 
      show reverse (x :: s ++ t) = reverse t ++ reverse (x :: s) from
      calc
        reverse (x :: s ++ t) 
          = reverse (x :: (s ++ t)) := by rw [cons_append]
        _ = reverse (s ++ t) ++ x :: nil := by rfl
        _ = reverse t ++ reverse s ++ x :: nil := by rw [ih]
        _ = reverse t ++ (reverse s ++ x :: nil) := by rw [append_assoc]
        _ = reverse t ++ (reverse (x :: s)) := by rfl
  )


example (t : List α)
  : reverse (reverse t) = t :=
  List.recOn
  (
    motive := fun t => reverse (reverse t) = t
  )
  t
  (
    show reverse (reverse nil) = nil from by rfl
  )
  (
    fun (x : α) (t : List α) 
      (ih : reverse (reverse t) = t) => 
      show reverse (reverse (x :: t)) = x :: t from 
      calc 
        reverse (reverse (x :: t)) = reverse (reverse t ++ x :: nil) := by rfl
        _ = reverse (x :: nil) ++ reverse (reverse t) := by rw [reverse_append]
        _ = reverse (x :: nil) ++ t := by rw [ih]
        _ = reverse nil ++ x :: nil ++ t := by rfl
        _ = nil ++ x :: nil ++ t := by rfl
        _ = x :: nil ++ t := by rw [nil_append]
        _ = x :: (nil ++ t) := by rfl
        _ = x :: t := by rw [nil_append] 
  )


end Hidden2 
end ex2