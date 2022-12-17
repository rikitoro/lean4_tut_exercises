/- Induction and Recursion -/ 

section ex1
namespace Hidden
open Nat

def add : Nat → Nat → Nat
  | n, zero   => n
  | n, succ m => succ $ add n m

#print add

def mul : Nat → Nat → Nat
  | _, zero   => zero
  | n, succ m => add (mul n m) n

def pow : Nat → Nat → Nat
  | _, zero   => succ zero
  | n, succ m => mul (pow n m) n


end Hidden
end ex1


section ex5
inductive Expr where
  | const   : Nat → Expr
  | var     : Nat → Expr
  | plus    : Expr → Expr → Expr
  | times   : Expr → Expr → Expr
  deriving Repr 

open Expr

def sampleExpr :=
  plus (times (var 0) (const 7)) (times (const 2) (var 1))

def eval (v : Nat → Nat) : Expr → Nat
  | const n     => n
  | var n       => v n
  | plus e₁ e₂  => eval v e₁ + eval v e₂
  | times e₁ e₂ => eval v e₁ * eval v e₂

def sampleVal : Nat → Nat
  | 0 => 5
  | 1 => 6
  | _ => 0

#eval eval sampleVal sampleExpr

def simpConst : Expr → Expr
  | plus (const n₁) (const n₂)    => const $ n₁ + n₂
  | times (const n₁) (const n₂)   => const $ n₁ * n₂
  | e                             => e

def fuse : Expr → Expr
  | plus e₁ e₂  => simpConst $ plus (fuse e₁) (fuse e₂)
  | times e₁ e₂ => simpConst $ times (fuse e₁) (fuse e₂)
  | e           => simpConst e

#eval fuse $ const 2
#eval fuse $ plus (const 2) (const 3)
#eval fuse $ plus (var 1) (const 2)
#eval fuse $ plus (times (const 2) (const 3)) (var 0)


theorem simpConst_eq (v : Nat → Nat)
        : ∀ e : Expr, eval v (simpConst e) = eval v e := by
  intro e
  cases e with 
  | plus e₁ e₂  => 
    cases e₁ with
    | const n =>
      cases e₂ <;> rfl
    | _       => rfl
  | times e₁ e₂ => 
    cases e₁ with
    | const n => 
      cases e₂ <;> rfl
    | _       => rfl
  | _     => rfl

theorem fuse_eq (v : Nat → Nat)
        : ∀ e : Expr, eval v (fuse e) = eval v e := by 
  sorry


end ex5