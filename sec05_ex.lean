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
  example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
    apply Iff.intro
    . intro h   
      have hp := h.left
      have hqr := h.right
      cases hqr with
      | inl hq => 
        have hpq := And.intro hp hq
        exact Or.inl hpq
      | inr hr =>
        have hpr := And.intro hp hr 
        exact Or.inr hpr
    . intro h
      apply And.intro 
      . cases h with
        | inl hpq => 
          exact hpq.left
        | inr hpr => 
          exact hpr.left
      . cases h with
        | inl hpq =>
          have hq := hpq.right
          exact Or.inl hq
        | inr hpr =>
          have hr := hpr.right
          exact Or.inr hr

  example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
    apply Iff.intro
    . intro h
      apply And.intro
      . cases h with
        | inl hp =>
          exact Or.inl hp
        | inr hqr =>
          have hq := hqr.left 
          exact Or.inr hq
      . cases h with
        | inl hp => 
          exact Or.inl hp
        | inr hqr => 
          have hr := hqr.right
          exact Or.inr hr
    . intro h 
      have hpq := h.left
      have hpr := h.right
      cases hpq with
      | inl hp => 
        exact Or.inl hp
      | inr hq => 
        cases hpr with
        | inl hp => 
          apply Or.inl
          exact hp
        | inr hr => 
          have hqr := And.intro hq hr
          apply Or.inr
          exact hqr

  -- other properties
  example : (p → (q → r)) ↔ (p ∧ q → r) := by
    apply Iff.intro
    . intros hpqr hpq
      have hp := hpq.left
      have hq := hpq.right
      have hqr := hpqr hp
      have hr := hqr hq
      exact hr
    . intros hpqr hp hq
      have hpq := And.intro hp hq
      have hr := hpqr hpq
      exact hr

  example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := by
    apply Iff.intro
    case mp => 
      intro hpqr
      apply And.intro
      case left => 
        intro hp
        have hpq := Or.intro_left q hp 
        have hr := hpqr hpq
        assumption
      case right => 
        intro hq
        have hpq := Or.intro_right p hq
        have hr := hpqr hpq
        assumption
    case mpr => 
      intros hprqr hpq
      have hpr := hprqr.left 
      have hqr := hprqr.right
      cases hpq with
      | inl hp => 
        have hr := hpr hp
        assumption
      | inr hq => 
        have hr := hqr hq
        assumption 

  example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
    apply Iff.intro
    . intro hnpq
      apply And.intro
      . intro hp 
        have hpq := Or.intro_left q hp
        exact absurd hpq hnpq
      . intro hq 
        have hpq := Or.intro_right p hq 
        exact absurd hpq hnpq
    . intro hnpnq hpq
      cases hpq with
      | inl hp =>
        exact hnpnq.left hp 
      | inr hq =>
        exact hnpnq.right hq


  example : ¬p ∨ ¬q → ¬(p ∧ q) := by
    intro hnpnq hpq
    cases hnpnq with
    | inl hnp =>
      exact hnp hpq.left
    | inr hnq =>
      exact hnq hpq.right

  example : ¬(p ∧ ¬p) := by
    intro hpnp
    have hnp := hpnp.right 
    have hp := hpnp.left 
    exact hnp hp

  example : p ∧ ¬q → ¬(p → q) := by
    intro hpnq hpq
    have hp := hpnq.left
    have hnq := hpnq.right
    have hq := hpq hp 
    exact hnq hq

  example : ¬p → (p → q) := by
    intro hnp hp 
    exact absurd hp hnp

  example : (¬p ∨ q) → (p → q) := by
    intro hnpq hp 
    cases hnpq with
    | inl hnp => 
      exact absurd hp hnp
    | inr hq => 
      exact hq

  example : p ∨ False ↔ p := by
    apply Iff.intro
    . intro hpf
      cases hpf with
      | inl hp =>
        exact hp
      | inr hf =>
        exact False.elim hf
    . intro hp
      apply Or.inl
      exact hp

  example : p ∧ False ↔ False := by
    apply Iff.intro
    . intro hpf
      exact hpf.right
    . intro hf
      apply And.intro
      . exact False.elim hf
      . exact hf 

  example : (p → q) → (¬q → ¬p) := by
    intro hpq hnq hp 
    have hq := hpq hp 
    exact hnq hq
    
end