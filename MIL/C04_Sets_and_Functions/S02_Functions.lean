import MIL.Common
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic

section

variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

open Function
open Set

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  ext
  rfl

example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y; constructor
  · rintro ⟨x, xs | xt, rfl⟩
    · left
      use x, xs
    right
    use x, xt
  rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
  · use x, Or.inl xs
  use x, Or.inr xt

example : s ⊆ f ⁻¹' (f '' s) := by
  intro x xs
  show f x ∈ f '' s
  use x, xs

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  constructor
  . intro h x xs
    exact h (mem_image_of_mem f xs)
  . rintro h y
    rintro ⟨x, xs, rfl⟩
    exact h xs

example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  sorry

example : f '' (f ⁻¹' u) ⊆ u := by
  sorry

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  sorry

example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  sorry

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  sorry

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  sorry

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  sorry

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  sorry

example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  sorry

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
  sorry

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  sorry

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  sorry

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  sorry

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  sorry

variable {I : Type*} (A : I → Set α) (B : I → Set β)

example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  ext y
  simp
  constructor
  . rintro ⟨x, ⟨i, xi⟩, fxy⟩
    use i
    use x
  . rintro ⟨i, x, xi, fxy⟩
    use x
    exact ⟨⟨i, xi⟩, fxy⟩

example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  simp
  rintro i x yAi
  simp
  have : x ∈ A i := by
    simp at yAi
    exact yAi i
  use x

example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
  intro y h
  simp
  simp at h
  have : ∃ x ∈ A i, f x = y := h i
  rcases this with ⟨x, xAi, fxy⟩
  use x
  constructor
  . intro i'
    rcases h i' with ⟨x', x'Ai', fxy'⟩
    have : f x = f x' := by
      rw [fxy, fxy']
    have : x = x' := injf this
    rwa [this]
  . assumption

example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  ext x
  simp

example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
  ext x
  simp

example : InjOn f s ↔ ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂ :=
  Iff.refl _

end

section

open Set Real

example : InjOn log { x | x > 0 } := by
  intro x xpos y ypos
  intro e
  -- log x = log y
  calc
    x = exp (log x) := by rw [exp_log xpos]
    _ = exp (log y) := by rw [e]
    _ = y := by rw [exp_log ypos]


example : range exp = { y | y > 0 } := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    apply exp_pos
  intro ypos
  use log y
  rw [exp_log ypos]

example : InjOn sqrt { x | x ≥ 0 } := by
  intro x xge0
  simp at xge0
  intro y yge0
  simp at yge0
  intro e
  calc
    x = sqrt (x ^ 2) := by rw [sqrt_sq xge0]
    _ = sqrt (x * x)  := by
      rw [pow_two]
    _ = (sqrt x) * (sqrt x) := by
      rw [sqrt_mul]
      assumption
    _ = (sqrt y) * (sqrt y) := by rw [e]
    _ = sqrt (y * y) := by
      rw [sqrt_mul]
      assumption
    _ = sqrt (y ^ 2) := by
      rw [pow_two]
    _ = y := by
      congr
      apply sqrt_sq
      assumption

example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  intro x xge0 y yge0
  simp at xge0 yge0
  simp
  intro e
  calc
    x = sqrt (x ^ 2) := by rw [sqrt_sq xge0]
    _ = sqrt (y ^ 2) := by rw [e]
    _ = y := by rw [sqrt_sq yge0]

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  ext x
  constructor
  . rintro ⟨y, yge0, e⟩
    rw [← e]
    apply sqrt_nonneg
  . intro xge0
    use x ^ 2
    constructor
    . simp
      apply pow_two_nonneg
    . apply (sqrt_sq xge0)

example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  ext x
  constructor
  . simp
    intro y
    intro e
    rw [← e]
    apply pow_two_nonneg
  . simp
    intro xge0
    use sqrt x
    exact sq_sqrt xge0
end

section
variable {α β : Type*} [Inhabited α]

#check (default : α)

variable (P : α → Prop) (h : ∃ x, P x)

#check Classical.choose h

example : P (Classical.choose h) :=
  Classical.choose_spec h

noncomputable section

open Classical

def inverse (f : α → β) : β → α := fun y : β ↦
  if h : ∃ x, f x = y then Classical.choose h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
  rw [inverse, dif_pos h]
  exact Classical.choose_spec h

variable (f : α → β)

open Function

example : Injective f ↔ LeftInverse (inverse f) f := by
  constructor
  . intro injf
    -- LeftInverse (inverse f) f := ∀ x, (inverse f) (f x) = x : Prop
    intro x
    apply injf -- injf := f x = f x' -> x = x' : Prop
    apply inverse_spec
    use x
  . intro h
    intro x x' xeqx'
    calc
      x = inverse f (f x) := (h x).symm
      _ = inverse f (f x') := by rw [xeqx']
      _ = x' := h x'

example : Surjective f ↔ RightInverse (inverse f) f := by
  constructor
  . intro surjf y
    apply inverse_spec
    apply surjf
  . intro rinvf y
    use (inverse f y)
    apply rinvf

end

section
variable {α : Type*}
open Function

-- Cantor's diagonalization
theorem Cantor : ∀ f : α → Set α, ¬Surjective f := by
  intro f surjf -- suppose f is a function that surjects onto Set α
  let S := { i | i ∉ f i }
  rcases surjf S with ⟨j, h⟩
  -- Since (surjf : f is surjective), there exists (j : α) such that (h : f j = S)
  -- Think of (j : α) as the Gödel number of the set S
  have h₁ : j ∉ f j := by
    intro h'
    have : j ∉ f j := by rwa [h] at h'
    contradiction
  have h₂ : j ∈ S := by
    simp [S]
    exact h₁
  have h₃ : j ∉ S := by
    simp
    rw [h]
    exact h₁
  contradiction

end
