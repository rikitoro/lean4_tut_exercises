section
  variable (α : Type) (p q : α → Prop)

  example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
    Iff.intro
    (
      fun h : ∀ x, p x ∧ q x =>
        have hl := fun x => (h x).left
        have hr := fun x => (h x).right 
        And.intro hl hr
    )
    (
      fun h : (∀ x, p x) ∧ (∀ x, q x) =>
        fun x =>
          have hpx := h.left x
          have hqx := h.right x
          And.intro hpx hqx
    )

  example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
    fun hpq : ∀ x, p x → q x =>
      fun hp : ∀ x, p x =>
        fun x => 
          have hpx := hp x
          have hpxqx := hpq x 
          hpxqx hpx

  example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := 
    fun h : (∀ x, p x) ∨ (∀ x, q x) =>
      Or.elim h
      (
        fun hp =>
          fun x => Or.inl <| hp x
      )
      (
        fun hq =>
          fun x => Or.inr <| hq x 
      )

end

section
  open Classical

  variable (α : Type) (p q : α → Prop)
  variable (r : Prop)

  example : α → ((∀ _ : α, r) ↔ r) :=
    fun a : α =>
      Iff.intro
      ( 
        fun h : ∀ _ : α, r =>
          h a
      )
      (
        fun hr : r =>
          fun _ : α => hr
      )

  example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := 
    Iff.intro
    (
      fun h =>
        Or.elim (em r)
        (
          fun hr =>
            Or.inr hr
        )
        (
          fun hnr =>
            have hp := 
              fun x =>
                have pxr := h x
                Or.elim pxr
                (
                  fun hpx =>
                    hpx
                )
                (
                  fun hr =>
                    absurd hr hnr
                )
            Or.inl hp                
        )

    )
    (
      fun h =>
        Or.elim h
        (
          fun hp =>
            fun x =>
              Or.inl <| hp x
        )
        (
          fun hr =>
            fun _ => 
              Or.inr <| hr
        )
    )

  example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := 
    Iff.intro
    (
      fun h : ∀ x, r → p x =>
        fun hr : r =>
          fun x =>
            h x hr
    )
    (
      fun h : r → ∀ x, p x =>
        fun x =>
          fun r =>
            h r x
    )

end


section
  variable (men : Type) (barber : men)
  variable (shaves : men → men → Prop)

  example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
    have hbarber := h barber
    have hnsbb := 
      fun hsbb => hbarber.mp hsbb hsbb
    have hsbb := hbarber.mpr hnsbb
    hnsbb hsbb
end


section
  open Classical

  variable (α : Type) (p q : α → Prop)
  variable (r : Prop)

  example : (∃ _ : α, r) → r := 
    fun h =>
      match h with
      | ⟨_, hr⟩ => hr 

  example (a : α) : r → (∃ _ : α, r) := 
    fun hr => ⟨a, hr⟩

  example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := 
    Iff.intro
    (
      fun h =>
        match h with
        | ⟨w, hpxr⟩ => ⟨⟨w, hpxr.left⟩, hpxr.right⟩
    )
    (
      fun h =>
        match h.left with
        | ⟨w, hpx⟩ => ⟨w, ⟨hpx, h.right⟩⟩
    )

  example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := 
    Iff.intro
    (
      fun h =>
        match h with
        | ⟨w, hpwqw⟩ => 
            Or.elim hpwqw
            (
              fun hpw =>
                Or.inl ⟨w, hpw⟩
            )
            (
              fun hqw =>
                Or.inr ⟨w, hqw⟩
            )
    )
    (
      fun h =>
        Or.elim h
        (
          fun hp : ∃ x, p x =>
            match hp with
            | ⟨w, hpw⟩ => ⟨w, Or.inl hpw⟩
        )
        (
          fun hq : ∃ x, q x => 
            match hq with
            | ⟨w, hqw⟩ => ⟨w, Or.inr hqw⟩
        )

    )

  example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := 
    Iff.intro
    (
      fun h : ∀ x, p x =>
        fun hnp : ∃ x, ¬ p x =>
          match hnp with
          | ⟨w, hnpw⟩ => 
              let hpw := h w
              absurd hpw hnpw
    )
    (
      fun h : ¬ (∃ x, ¬ p x) =>
        fun x =>
          Or.elim (em $ p x)
          (
            fun hpx : p x =>
              hpx
          )
          (
            fun hnpx : ¬ p x =>
              have hnp := ⟨x, hnpx⟩
              absurd hnp h
          )
    )

  example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := sorry

  example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := sorry
  
  example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := sorry

  example : (∀ x, p x → r) ↔ (∃ x, p x) → r := sorry
  
  example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := sorry
  
  example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := sorry

end