section
  variable (p q r : Prop)

  -- commutativity of ∧ and ∨
  example : p ∧ q ↔ q ∧ p := by 
    apply Iff.intro
    . intro h
      apply And.intro
      . exact h.right
      . exact h.left
    . intro h 
      apply And.intro 
      . exact h.right
      . exact h.left

  example : p ∨ q ↔ q ∨ p := by
    apply Iff.intro
    . intro hpq
      apply Or.elim hpq
      . intro hp
        apply Or.inr
        exact hp
      . intro hq 
        apply Or.inl
        exact hq
    . intro hqp 
      cases hqp with
      | inl hq => 
        apply Or.inr
        exact hq
      | inr hp =>
        apply Or.inl
        exact hp

  -- associativity of ∧ and ∨
  example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by 
    apply Iff.intro 
    . intro hpqr
      apply And.intro
      . exact hpqr.left.left
      . apply And.intro
        . exact hpqr.left.right
        . exact hpqr.right
    . intro hpqr
      apply And.intro
      . apply And.intro
        . exact hpqr.left
        . exact hpqr.right.left
      . exact hpqr.right.right

  example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by
    apply Iff.intro 
    . intro hpqr
      cases hpqr with
      | inl hpq => 
          cases hpq with
          | inl hp => 
              exact Or.inl hp
          | inr hq => 
              exact Or.inr $ Or.inl hq
      | inr hr => 
          exact Or.inr $ Or.inr hr
    . intro hpqr
      cases hpqr with
      | inl hp => 
          exact Or.inl $ Or.inl hp
      | inr hqr => 
          cases hqr with
          | inl hq => 
              exact Or.inl $ Or.inr hq
          | inr hr =>
              exact Or.inr hr

  -- distributivity
  example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := sorry
  example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := sorry

  -- other properties
  example : (p → (q → r)) ↔ (p ∧ q → r) := sorry
  example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry
  example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry
  example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry
  example : ¬(p ∧ ¬p) := sorry
  example : p ∧ ¬q → ¬(p → q) := sorry
  example : ¬p → (p → q) := sorry
  example : (¬p ∨ q) → (p → q) := sorry
  example : p ∨ False ↔ p := sorry
  example : p ∧ False ↔ False := sorry
  example : (p → q) → (¬q → ¬p) := sorry
end