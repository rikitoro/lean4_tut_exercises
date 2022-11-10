section
  variable (p q r : Prop)

  example : p ∧ q ↔ q ∧ p := 
    Iff.intro
    (fun h => ⟨h.right, h.left⟩)
    (fun h => ⟨h.right, h.left⟩)

  example : p ∨ q ↔ q ∨ p :=
    Iff.intro
    (
      fun h =>
        Or.elim h 
        (
          fun hp => Or.inr hp
        )
        (
          fun hq => Or.inl hq
        )
    )
    (
      fun h =>
        Or.elim h
        (
          fun hq => Or.inr hq
        )
        (
          fun hp => Or.inl hp
        )
    )

  example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
    Iff.intro
    (
      fun h =>
        ⟨h.left.left, ⟨h.left.right, h.right⟩⟩
    )
    (
      fun h =>
        ⟨⟨h.left, h.right.left⟩, h.right.right⟩
    )

  example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
    Iff.intro 
    (
      fun h =>
        Or.elim h 
        (
          fun hpq => 
            Or.elim hpq
            (
              fun hp => Or.inl hp
            )
            (
              fun hq => Or.inr $ Or.inl hq
            )
        )
        (
          fun hr =>
            Or.inr $ Or.inr hr
        )
    )
    ( 
      fun h =>
        Or.elim h
        (
          fun hp =>
            Or.inl $ Or.inl hp
        )
        (
          fun hqr =>
            Or.elim hqr
            (
              fun hq => Or.inl $ Or.inr hq
            )
            (
              fun hr => Or.inr hr 
            )
        )
    )

  example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
    Iff.intro
    (
      fun h =>
        have hp := h.left
        Or.elim h.right 
        (
          fun hq => 
            Or.inl $ And.intro hp hq 
        )
        (
          fun hr => 
            Or.inr $ And.intro hp hr  
        )
    )
    (
      fun h =>
        Or.elim h
        (
          fun hpq => 
            And.intro hpq.left $ Or.inl hpq.right 
        )
        (
          fun hpr =>
            have hp := hpr.left
            have hr := hpr.right
            have hqr := Or.inr hr 
            And.intro hp hqr
        )
    )

  example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
    Iff.intro 
    (
      fun h =>
        Or.elim h
        (
          fun hp => 
            ⟨Or.inl hp, Or.inl hp⟩
        )
        (
          fun hqr =>
            ⟨Or.inr hqr.left, Or.inr hqr.right⟩
        )
    )
    (
      fun h =>
        have hpq := h.left
        have hpr := h.right
        Or.elim hpq
        (
          fun hp =>
            Or.inl hp
        )
        (
          fun hq =>
            Or.elim hpr 
            (
              fun hp =>
                Or.inl hp
            )
            (
              fun hr =>
                Or.inr ⟨hq, hr⟩
            )
        )
    )

  example : (p → (q → r)) ↔ (p ∧ q → r) :=
    Iff.intro 
    (
      fun hpqr =>
        fun hpq =>
          have hp := hpq.left
          have hq := hpq.right
          hpqr hp hq
    )
    (
      fun h =>
        fun hp =>
          fun hq =>
            have hpq := ⟨hp, hq⟩
            h hpq
    )

  example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := 
    Iff.intro
    (
      fun h =>
        And.intro
        (
          fun hp : p =>
            have hpq := Or.inl hp
            have hr := h hpq 
            hr
        )
        (
          fun hq : q =>
            have hpq := Or.inr hq 
            have hr := h hpq
            hr
        )
    )
    (
      fun h =>
        fun hpq : p ∨ q =>
          Or.elim hpq
          (
            fun hp => 
              h.left hp
          )
          (
            fun hq =>  
              h.right hq
          )
    )

  example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
    Iff.intro 
    (
      fun hnpq : ¬(p ∨ q) =>
        And.intro 
        (
          fun hp : p =>
            have hpq : p ∨ q := Or.inl hp 
            hnpq hpq
        )
        (
          fun hq : q =>
            have hpq : p ∨ q := Or.inr hq 
            hnpq hpq
        )
    )
    (
      fun hnpnq : ¬p ∧ ¬q =>
        fun hpq : p ∨ q =>
          Or.elim hpq 
          (
            fun hp =>
              have hnp := hnpnq.left
              hnp hp
          )
          (
            fun hq =>
              hnpnq.right hq
          )

    )

  example : ¬p ∨ ¬q → ¬(p ∧ q) :=
    fun hnpnq : ¬p ∨ ¬q =>
      fun hpq : p ∧ q =>
        Or.elim hnpnq 
        (
          fun hnp : ¬p =>
            hnp hpq.left
        )
        (
          fun hnq : ¬q =>
            hnq hpq.right
        )

  example : ¬(p ∧ ¬p) :=
    fun hpnp : p ∧ ¬p =>
      hpnp.right hpnp.left

  example : p ∧ ¬q → ¬(p → q) :=
    fun h =>
      fun hpq =>
        have hq := hpq h.left
        h.right hq

  example : ¬p → (p → q) :=
    fun hnp =>
      fun hp =>
        absurd hp hnp 

  example : (¬p ∨ q) → (p → q) :=
    fun hnpq =>
      fun hp =>
        Or.elim hnpq 
        (
          fun hnp =>
            absurd hp hnp 
        )
        (
          fun hq =>
            hq
        )

  example : p ∨ False ↔ p :=
    Iff.intro
    (
      fun h =>
        Or.elim h
        (
          fun hp => hp
        )
        (
          fun fls => False.elim fls 
        )
    )
    (
      fun h =>
        Or.inl h
    )

  example : p ∧ False ↔ False :=
    Iff.intro 
    (
      fun h => h.right 
    )
    (
      fun fls =>
        have hp := False.elim fls
        And.intro hp fls
    )

  example : (p → q) → (¬q → ¬p) := 
    fun hpq =>
      fun hnq =>
        fun hp =>
          hnq $ hpq hp 
end

section
  open Classical

  variable (p q r : Prop)

  example : (p → q ∨ r) → ((p → q) ∨ (p → r)) :=
    fun hpqr : (p → q ∨ r) =>
      Or.elim (em q)
      (
        fun hq =>
          Or.inl $ fun _ => hq
      )
      (
        fun hnq =>
          Or.inr <| 
            fun hp => 
              have hqr := hpqr hp
              Or.elim hqr
              (
                fun hq => absurd hq hnq 
              )
              (
                fun hr => hr
              )
      )

  example : ¬(p ∧ q) → ¬p ∨ ¬q :=
    fun hnpq =>
      Or.elim (em p) 
      (
        fun hp =>
          Or.elim (em q)
          (
            fun hq =>
              absurd ⟨hp, hq⟩ hnpq
          )
          (
            fun hnq => Or.inr hnq
          )
      )
      (
        fun hnp =>
          Or.inl hnp
      )

  example : ¬(p → q) → p ∧ ¬q := 
    fun hnpq : ¬(p → q) =>
      Or.elim (em p)
      (
        fun hp => 
          Or.elim (em q)
          (
            fun hq => 
              have hpq := fun _ => hq 
              absurd hpq hnpq
          )
          (
            fun hnq => 
              And.intro hp hnq 
          )
      )
      (
        fun hnp => 
          Or.elim (em q)
          (
            fun hq =>
              have hpq := fun _ => hq
              absurd hpq hnpq 
          )
          (
            fun _ => 
              have hpq := fun hp => absurd hp hnp
              absurd hpq hnpq
          )
      ) 


  example : (p → q) → (¬p ∨ q) := 
    fun hpq =>
      Or.elim (em p) 
      (
        fun hp =>
          have hq := hpq hp 
          Or.inr hq 
      )
      (
        fun hnp =>
          Or.inl hnp
      )

  example : (¬q → ¬p) → (p → q) := 
    fun hnqnp =>
      Or.elim (em q) 
      (
        fun hq =>
          have hpq := fun _ => hq 
          hpq
      )
      (
        fun hnq => 
          have hnp := hnqnp hnq 
          fun hp =>
            absurd hp hnp
      )

  example : (p ∨ ¬p) :=
    em p
  
  example : ((p → q) → p) → p := 
    fun hpqp =>
      Or.elim (em p) 
      (
        fun hp : p => hp
      )
      (
        fun hnp : ¬p => 
          have hpq := 
            fun hp => absurd hp hnp
          have hp := hpqp hpq
          absurd hp hnp
      )
    
end

section
  variable (p : Prop)

  example : ¬(p ↔ ¬p) := 
    fun h : p ↔ ¬p =>
      have hnp : ¬p := 
        fun hp : p =>
          have hnp' := h.mp hp
          absurd hp hnp'
      have hp : p := h.mpr hnp
      absurd hp hnp

end

