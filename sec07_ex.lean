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
  match m with
  | 0       => 0
  | succ m' => 
    match n with
    | 0       => m
    | succ n' => trunc_sub m' n'

#eval trunc_sub 10 3
#eval trunc_sub 3 4


end Hidden1

end