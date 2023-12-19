import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import MIL.Common

open Set
open Function

noncomputable section
open Classical


variable {α β : Type*} [Nonempty β]

section
variable (f : α → β) (g : β → α)

-- sbuAux₀ = g(β)ᶜ
-- sbuAux₁ = g(f(sbuAux₀))
-- ...
def sbAux : ℕ → Set α
  | 0 => (univ : Set α) \ g '' (univ : Set β)
  | n + 1 => g '' (f '' sbAux n)

def sbSet :=
  ⋃ n, sbAux f g n

-- (sbFun f g) will be shown as bijective
def sbFun (x : α) : β :=
  if x ∈ sbSet f g then f x else invFun g x
  -- notice that we are using excluded middle
  -- by assuming x is in XOR not in sbSet f g

-- g⁻¹ is the right inverse of g on (∪ₙ Aₙ)ᶜ
-- If x ∉ ∪ₙ Aₙ, then x = g(g⁻¹(x))
theorem sb_right_inv {x : α} (hx : x ∉ sbSet f g) : g (invFun g x) = x := by
  apply invFun_eq
  -- x ∈ g(β)
  have : x ∈ g '' univ := by
    -- Suppose not, then x ∈ A₀
    contrapose! hx
    rw [sbSet, mem_iUnion]
    use 0
    rw [sbAux, mem_diff]
    exact ⟨ by simp, hx ⟩
  rcases this with ⟨y, _, _⟩
  use y

-- (sbFun f g) is injective
theorem sb_injective (hf : Injective f) (hg : Injective g) : Injective (sbFun f g) := by
  set A := sbSet f g with A_def
  set h := sbFun f g with h_def
  intro x₁ x₂
  intro (hxeq : h x₁ = h x₂)
  show x₁ = x₂
  simp only [h_def, sbFun, ← A_def] at hxeq
  -- We have three cases
  -- x₁ ∈ A: This case we prove in detail.
  -- x₂ ∈ A: This case is dealt by wlog, since it's symmetric to the previous case.
  -- x₁ ∉ A ∧ x₂ ∉ A: This is trivial.
  by_cases xA : x₁ ∈ A ∨ x₂ ∈ A
  · wlog x₁A : x₁ ∈ A generalizing x₁ x₂ hxeq xA
    · symm
      apply this hxeq.symm xA.symm (xA.resolve_left x₁A)
    have x₂A : x₂ ∈ A := by
      -- To show x₂ ∈ A, assume otherwise, then prove it anyway.
      apply not_imp_self.mp
      intro (x₂nA : x₂ ∉ A)
      rw [if_pos x₁A, if_neg x₂nA] at hxeq
      rw [A_def, sbSet, mem_iUnion] at x₁A
      have x₂eq : g (f x₁) = x₂ := by
        calc
          g (f x₁) = g (invFun g x₂) := by rw [hxeq]
          _ = x₂ := by rw [sb_right_inv f g x₂nA]
      rcases x₁A with ⟨n, hn⟩
      rw [A_def, sbSet, mem_iUnion]
      use n + 1
      simp [sbAux]
      exact ⟨x₁, hn, x₂eq⟩
    have : f x₁ = f x₂ := by
      rw [if_pos x₁A, if_pos x₂A] at hxeq
      exact hxeq
    exact hf this
  push_neg at xA
  rw [if_neg xA.1, if_neg xA.2] at hxeq -- extract the case
  calc
    x₁ = g (invFun g x₁) := by rw [sb_right_inv f g xA.1]
    _ = g (invFun g x₂) := by rw [hxeq]
    _ = x₂ := by rw [sb_right_inv f g xA.2]

-- (sbFun f g) is surjective
theorem sb_surjective (hf : Injective f) (hg : Injective g) : Surjective (sbFun f g) := by
  set A := sbSet f g with A_def
  set h := sbFun f g with h_def
  intro y
  by_cases gyA : g y ∈ A
  · rw [A_def, sbSet, mem_iUnion] at gyA
    rcases gyA with ⟨n, hn⟩
    rcases n with _ | n
    · simp [sbAux] at hn
    simp [sbAux] at hn
    rcases hn with ⟨x, xmem, hx⟩
    use x
    have : x ∈ A := by
      rw [A_def, sbSet, mem_iUnion]
      exact ⟨n, xmem⟩
    simp only [h_def, sbFun, if_pos this]
    exact hg hx
  -- If g y ∉ A, then y = h (g y)
  -- by route of g y = g (h (g y))
  use g y
  rw [h_def, sbFun, if_neg gyA]
  apply hg
  apply sb_right_inv
  exact gyA
end

-- Combining the two theorems, we have that (sbFun f g) is bijective
theorem schroeder_bernstein {f : α → β} {g : β → α} (hf : Injective f) (hg : Injective g) :
    ∃ h : α → β, Bijective h :=
  ⟨sbFun f g, sb_injective f g hf hg, sb_surjective f g hf hg⟩

-- Auxiliary information
section
variable (g : β → α) (x : α)

#check (invFun g : α → β)
#check (leftInverse_invFun : Injective g → LeftInverse (invFun g) g)
#check (leftInverse_invFun : Injective g → ∀ y, invFun g (g y) = y)
#check (invFun_eq : (∃ y, g y = x) → g (invFun g x) = x)

end
