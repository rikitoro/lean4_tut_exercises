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


section
  open Classical

  variable (p q r : Prop)

  example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := by
    intro hpqr
    apply Or.elim (em q)
    . intro hq
      apply Or.inl
      intro 
      exact hq
    . intro hnq
      apply Or.inr
      intro hp 
      have hqr := hpqr hp
      cases hqr with
      | inl hq => contradiction
      | inr hr => assumption

  example : ¬(p ∧ q) → ¬p ∨ ¬q := by
    intro hnpq 
    apply Or.elim (em p)
    . intro hp
      apply Or.inr
      intro hq
      have hpq := And.intro hp hq
      contradiction      
    . intro hnp
      apply Or.inl
      assumption

  example : ¬(p → q) → p ∧ ¬q := by
    intro hnpq
    apply Or.elim (em p) 
    . intro hp 
      apply Or.elim (em q)
      . intro hq
        apply And.intro
        . assumption
        . have hpq : p → q := fun _ => hq
          contradiction
      . intro hnq
        apply And.intro  <;> assumption
    . intro hnp
      apply Or.elim (em q)
      . intro hq 
        have hpq : p → q := fun _ => hq 
        contradiction
      . intro 
        have hpq : p → q := fun hp => absurd hp hnp
        contradiction
  

  example : (p → q) → (¬p ∨ q) := by
    intro hpq
    cases (em p) with
    | inl hp =>
      have hq := hpq hp 
      apply Or.inr
      assumption
    | inr hq => 
      apply Or.inl 
      assumption

  example : (¬q → ¬p) → (p → q) := by
    intro hnqnp hp 
    cases (em q) with
    | inl hq => 
      assumption
    | inr hnq =>
      have hnp := hnqnp hnq
      contradiction
       
  example : p ∨ ¬p := by
    cases (em p) with
    | inl hp => 
      apply Or.inl
      assumption
    | inr hp =>
      apply Or.inr
      assumption

  example : (((p → q) → p) → p) := by
    intro hpqp
    cases (em p) with
    | inl hp  => 
      assumption
    | inr hnp => 
      have hpq : p → q := fun hp : p => absurd hp hnp
      have hp : p := hpqp hpq
      assumption


end


section
  variable (α : Type) (p q : α → Prop)

  example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := by
    apply Iff.intro 
    . intros hAxpxqx
      apply And.intro
      . intro x
        have hpxqx := hAxpxqx x
        exact hpxqx.left
      . intro x
        have hpxqx := hAxpxqx x
        exact hpxqx.right
    . intro h 
      have hAxpx := h.left 
      have hAxqx := h.right 
      intro x
      have px := hAxpx x 
      have qx := hAxqx x 
      apply And.intro
      . exact px
      . exact qx

  example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := by
    intros hAxpxqx hAxpx x
    have hpx := hAxpx x
    have hpxqx := hAxpxqx x 
    have hqx := hpxqx hpx
    exact hqx

  example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := by
    intros hAxpxAxqx x
    cases hAxpxAxqx with
    | inl hAxpx => 
      have hpx := hAxpx x
      apply Or.inl
      assumption
    | inr hAxqx => 
      have hqx := hAxqx x
      apply Or.inr
      assumption

end

section
  open Classical

  variable (α : Type) (p q : α → Prop)
  variable (r : Prop)

  example : α → ((∀ _ : α, r) ↔ r) := by 
    intro hα
    apply Iff.intro
    . intro hαr
      exact hαr hα
    . intro hr
      intro
      assumption
end

section
  variable (men : Type) (barber : men)
  variable (shaves : men → men → Prop)

  example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False := by 
    have h1 := h barber
    have h2 := fun hbb => h1.mp hbb hbb
    have h3 := h1.mpr h2
    contradiction

end


section
example (p q r : Prop) (hp :  p) 
  : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
  sorry

end