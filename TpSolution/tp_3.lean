section Exercises
  variable (p q r: Prop)

  example : p ∧ q ↔ q ∧ p :=
    Iff.intro
      (fun h: p ∧ q => show q ∧ p from And.intro h.right h.left)
      (fun h: q ∧ p => show p ∧ q from ⟨h.right, h.left⟩)

  example : p ∨ q ↔ q ∨ p :=
    Iff.intro
      (fun h : p ∨ q => h.elim (λ hp: p => Or.inr hp) (λ hq: q => Or.inl hq))
      (fun h : q ∨ p => h.elim (λ hq: q => Or.inr hq) (λ hp: p => Or.inl hp))

  example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := sorry

  example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := sorry
  example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := sorry

  example : (p → (q → r)) ↔ (p ∧ q → r) :=
    Iff.intro
      (fun h: p → (q → r) => fun h_pq: p ∧ q => show r from (h h_pq.left) h_pq.right)
      (fun h: p ∧ q → r => fun h_p: p => (fun h_q : q => h ⟨h_p, h_q⟩ ))

  example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
    Iff.intro
      (fun h: (p ∨ q) → r =>
        have h₁ : p → r := fun h_a: p => h (Or.inl h_a)
        have h₂ : q → r := fun h_b: q => h (Or.inr h_b)
        ⟨h₁, h₂⟩
      )
      (
        fun h: (p → r) ∧ (q → r) =>
        fun h₁ : p ∨ q =>
        h₁.elim
          (fun hp: p => h.left hp)
          (fun hq: q => h.right hq)
      )

  example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
    Iff.intro
    (fun h: ¬(p ∨ q) => ⟨
        (fun hp: p => show False from h (Or.inl hp)),
        (fun hq: q => show False from h (Or.inr hq))
    ⟩ )
    (fun h: ¬p ∧ ¬q =>
      fun h₁: p ∨ q =>
      h₁.elim
      (fun hp: p => h.left hp)
      (fun hq: q => h.right hq)
    )

  example : ¬p ∨ ¬q → ¬(p ∧ q) :=
    fun h : ¬p ∨ ¬q =>
    fun h₁ : p ∧ q =>
    h.elim
      (fun h_np: ¬p => show False from h_np h₁.left)
      (fun h_nq: ¬q => show False from h_nq h₁.right)

  example : ¬(p ∧ ¬p) :=
    fun h: (p ∧ ¬p) => h.right h.left

  example : p ∧ ¬q → ¬(p → q) :=
    fun h: p ∧ ¬q =>
    fun h₁: p → q =>
    show False from h.right (h₁ h.left)

  example : ¬p → (p → q) :=
    fun h_np: ¬p =>
    fun h_p: p =>
    absurd h_p h_np

  example : (¬p ∨ q) → (p → q) :=
    fun h: ¬p ∨ q =>
    fun h₁ : p =>
    h.elim
      (fun h₂: ¬p => absurd h₁ h₂)
      (fun h₂: q => h₂)


  example : p ∨ False ↔ p :=
    Iff.intro
    (fun h: p ∨ False => h.elim (id) (fun h: False => h.elim))
    (Or.inl)

  example : p ∧ False ↔ False :=
    Iff.intro
    (fun h: p ∧ False =>h.right)
    (fun h: False => h.elim)

  example : (p → q) → (¬q → ¬p) :=
    fun h₁: p → q =>
    fun h₂: ¬q =>
    fun h₃: p => show False from h₂ (h₁ h₃)

end Exercises


-- open Classical
-- theorem dne: ¬¬p → p :=
--   fun h => (
--     (em p).elim
--       (fun hp: p => hp)
--       (fun np: ¬p => absurd np h)
--   )



section Exercises_Classical
open Classical

variable (p q r : Prop)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) :=
  (em p).elim
    (fun hp: p => fun (h: p → q ∨ r) => (h hp).elim
      (fun hq: q => Or.inl (fun _: p => hq))
      (fun hr: r => Or.inr (fun _: p => hr))
    )
    (fun np: ¬p => fun (_ : p → q ∨ r) => Or.inl (fun hp: p => (np hp).elim))


example : ¬(p ∧ q) → ¬p ∨ ¬q :=
  byCases
    (
      fun h_p: p =>
      byCases
        (fun h_q: q => fun h: ¬(p ∧ q) => (h ⟨h_p, h_q⟩).elim)
        (fun h_nq: ¬q => fun h: ¬(p ∧ q) => Or.inr h_nq)
    )
    (
      fun h_np: ¬p => fun h: ¬(p ∧ q) => Or.inl h_np
    )

example : ¬(p → q) → p ∧ ¬q :=
  byCases
    (fun h_p: p =>
      byCases
        (fun h_q: q => fun h: ¬(p → q) => (h fun hp: p => h_q).elim)
        (fun h_nq: ¬q => fun h : ¬(p → q) => ⟨h_p, h_nq⟩)
    )
    (fun h_np: ¬p =>
      fun h: ¬(p → q) =>
      (h (fun hp: p => (h_np hp).elim)).elim
    )


example : (p → q) → (¬p ∨ q) :=
  fun h: p → q =>
  byCases
    (fun h₁: p => Or.inr (h h₁))
    (fun h₁: ¬p => Or.inl h₁)

example : (¬q → ¬p) → (p → q) :=
  fun h: ¬q → ¬p =>
  byCases
    (fun h_q: q => fun h_p: p => h_q)
    (fun h_nq: ¬q => fun h_p: p => (h h_nq h_p).elim)

example : p ∨ ¬p :=
  em p

example : (((p → q) → p) → p) :=
  (em p).elim
    (fun hp: p => fun hpqp: ((p → q) → p) => hp)
    (fun np: ¬p => fun hpqp: ((p → q) → p) =>
      hpqp (fun hpq: p => absurd hpq np)
    )

-- last without classical
example : ¬(p ↔ ¬p) :=
  fun h: p ↔ ¬p =>
    have h₁ : p → ¬p := h.mp
    have h₂ : ¬p → p := h.mpr
    have h₃: ¬p := fun h₄: p => show False from (h₁ h₄) h₄
    show False from h₃ (h₂ h₃)




end Exercises_Classical
