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