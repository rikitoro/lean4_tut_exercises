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

end ex5