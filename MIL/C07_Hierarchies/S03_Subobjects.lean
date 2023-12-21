import MIL.Common
import Mathlib.GroupTheory.QuotientGroup

set_option autoImplicit true

/-
In most of modern abstract algebra, objects are interpreted as set-like things with extra structure.
So, subobjects of algebraic objects are interpreted as subsets.
Sets are interpreted as predicate functions.
We can implement subobjects by first coercing down to predicate, then manipulate the predicates.
but instead we implement it as subsets, to not break the abstraction.

If M is a type that has an implementation of the Monoid class
then Submonoid₁ M is the type of submonoids of M.

WARNING. There is a strong asymmetry between M and Submonoid₁ M.
M is a type that represents a monoid.
Submonoid₁ M is a type whose INSTANCES represent submonoids of the monoid.

If you have studied abstract algebra from the category theoretic point of view
you would find this obvious, as monoids (the intuitive sense)
are *points* in the category Monoid,
but submonoids (the intuitive sense) are not points in the category Submonoid.
In fact, there is no such category. Submonoids (the intuitive sense) are
*monomorphic arrows* in the category Monoid.

If you have studied abstract algebra in the typical way, you would be surprised,
because typically subobjects are represented by subsets of the underlying set, and
in set theory, everything is a set, even subsets of a set! There is no sense in which
the subsets of a set depend on that set. Suppose A is a subset of B. Now you have forgotten B.
How can you recover B from A? You can't.
But in category theory, suppose f is a subobject of B -- that is, f is a monomorphic arrow
pointing at B. Now you have forgotten B. How can you recover B from the subobject?
Easy, B is the target of f.

Now, Lean is based on a type theory that is much closer to category theory than set theory,
so we have to implement set theory on top of a type-theoretic foundation, in a style that is
very close to category-theoretic set theory (ECTS). This is what we are doing here.

There is no Set, but only Set α for each type α.
There is no instance of Set, but only instances of Set α for each type α.
An instance of Set α is by definition a function of type α → Prop.
There are no subset-objects. Instead, being a subset is a property you can prove for two objects.

To be more precise, we could have implemented subsets like this:

class Set ...
structure Subset (S : Type) [Set S] ...

But we don't do that, because we want to emulate naive set theory as closely as possible. So

def Set (α : Type u) := α → Prop
def subset (S T : Type) [Set S] [Set T] := ∀ x : α, S x → T x

Something else that can be confusing is that Set α should actually be pictured as
the type of *subsets* of α, not the type of *elements* of α. Here, α plays the role of
a set-theoretic *universe*, which is not the type-theoretic sense of "universe".
-/

@[ext]
structure Submonoid₁ (M : Type) [Monoid M] where
  /-- The carrier of a submonoid. -/
  carrier : Set M
  /-- The product of two elements of a submonoid belongs to the submonoid. -/
  mul_mem {a b} : a ∈ carrier → b ∈ carrier → a * b ∈ carrier
  /-- The unit element belongs to the submonoid. -/
  one_mem : 1 ∈ carrier

/-
Submonoid₁ is a type constructor: given a type M that implements the Monoid class,
Submonoid₁ M is the type for submonoids of M.

Furthermore, instances of Submonoid₁ M are *also* types! In Lean, subobjects are really
subtypes.

Basically, in Lean, EVERYTHING is a type.
-/

#check Submonoid₁

/-- Submonoids in `M` can be seen as sets in `M`. -/
instance [Monoid M] : SetLike (Submonoid₁ M) M where
  coe := Submonoid₁.carrier
  coe_injective' := Submonoid₁.ext

example [Monoid M] (N : Submonoid₁ M) : 1 ∈ N := N.one_mem

example [Monoid M] (N : Submonoid₁ M) (α : Type u) (f : M → α) : Set α :=
  f '' N

-- type coercion
example [Monoid M] (N : Submonoid₁ M) (x : N) : (x : M) ∈ N := x.property

-- For each type M that implements the Monoid class
-- and each instance (N : Submonoid₁ M),
instance SubMonoid₁Monoid [Monoid M] (N : Submonoid₁ M) : Monoid N where
  mul := fun x y ↦ ⟨x*y, N.mul_mem x.property y.property⟩
  mul_assoc := fun x y z ↦ SetCoe.ext (mul_assoc (x : M) y z)
  one := ⟨1, N.one_mem⟩
  one_mul := fun x ↦ SetCoe.ext (one_mul (x : M))
  mul_one := fun x ↦ SetCoe.ext (mul_one (x : M))


example [Monoid M] (N : Submonoid₁ M) : Monoid N where
  mul := fun ⟨x, hx⟩ ⟨y, hy⟩ ↦ ⟨x*y, N.mul_mem hx hy⟩
  mul_assoc := fun ⟨x, _⟩ ⟨y, _⟩ ⟨z, _⟩ ↦ SetCoe.ext (mul_assoc x y z)
  one := ⟨1, N.one_mem⟩
  one_mul := fun ⟨x, _⟩ ↦ SetCoe.ext (one_mul x)
  mul_one := fun ⟨x, _⟩ ↦ SetCoe.ext (mul_one x)


class SubmonoidClass₁ (S : Type) (M : Type) [Monoid M] [SetLike S M] : Prop where
  mul_mem : ∀ (s : S) {a b : M}, a ∈ s → b ∈ s → a * b ∈ s
  one_mem : ∀ s : S, 1 ∈ s

instance [Monoid M] : SubmonoidClass₁ (Submonoid₁ M) M where
  mul_mem := Submonoid₁.mul_mem
  one_mem := Submonoid₁.one_mem

@[ext]
structure Subgroup₁ (G : Type) [Group G] where
  carrier : Set G
  mul_mem {a b} : a ∈ carrier → b ∈ carrier → a * b ∈ carrier
  one_mem : 1 ∈ carrier
  inv_mem {a} : a ∈ carrier → a⁻¹ ∈ carrier

instance [Group G] : SetLike (Subgroup₁ G) G where
  coe := Subgroup₁.carrier
  coe_injective' := Subgroup₁.ext

example [Group G] (G : Subgroup₁ G) : 1 ∈ G := G.one_mem

example [Group G] (H : Subgroup₁ G) (α : Type u) (f : G → α) : Set α := f '' H

class SubgroupClass₁ (S : Type) (M : Type) [Monoid M] [SetLike S M]
  extends SubmonoidClass₁ S M : Prop

instance [Group G] : SubgroupClass₁ (Subgroup₁ G) G where
  mul_mem := Subgroup₁.mul_mem
  one_mem := Subgroup₁.one_mem

instance Subgroup₁Group [Group G] (H : Subgroup₁ G) : Group H where
  mul := fun x y ↦ ⟨x*y, H.mul_mem x.property y.property⟩
  mul_assoc := fun x y z ↦ SetCoe.ext (mul_assoc (x : G) y z)
  one := ⟨1, H.one_mem⟩
  one_mul := fun x ↦ SetCoe.ext (one_mul (x : G))
  mul_one := fun x ↦ SetCoe.ext (mul_one (x : G))
  inv := fun x ↦ ⟨x⁻¹, H.inv_mem x.property⟩
  mul_left_inv := fun x ↦ SetCoe.ext (mul_left_inv (x : G))

instance [Monoid M] : SubmonoidClass₁ (Submonoid₁ M) M where
  mul_mem := Submonoid₁.mul_mem
  one_mem := Submonoid₁.one_mem

--

instance [Monoid M] : Inf (Submonoid₁ M) :=
  ⟨fun S₁ S₂ ↦
    { carrier := S₁ ∩ S₂
      one_mem := ⟨S₁.one_mem, S₂.one_mem⟩
      mul_mem := fun ⟨hx, hx'⟩ ⟨hy, hy'⟩ ↦ ⟨S₁.mul_mem hx hy, S₂.mul_mem hx' hy'⟩ }⟩


example [Monoid M] (N P : Submonoid₁ M) : Submonoid₁ M := N ⊓ P


def Submonoid.Setoid [CommMonoid M] (N : Submonoid M) : Setoid M  where
  r := fun x y ↦ ∃ w ∈ N, ∃ z ∈ N, x*w = y*z
  iseqv := {
    refl := fun x ↦ ⟨1, N.one_mem, 1, N.one_mem, rfl⟩
    symm := fun ⟨w, hw, z, hz, h⟩ ↦ ⟨z, hz, w, hw, h.symm⟩
    trans := by
      intro x y z h h'
      rcases h with ⟨w, hw, z', hz', h⟩
      rcases h' with ⟨w', hw', z'', hz'', h'⟩
      use w'*w
      constructor
      . exact N.mul_mem hw' hw
      use z''*z'
      constructor
      . exact N.mul_mem hz'' hz'
      -- z (z'' z') = (y w') z' = (w' y) z' = w' (x w) = x (w' w)
      have :   z * (z'' * z') = x * (w' * w) := by
        calc
          z * (z'' * z') = y * w' * z' := by
            rw [mul_comm z'' z']
            rw [h']
            rw [mul_assoc, mul_comm z'' z']
          _ = w' * y * z' := by simp [mul_comm]
          _ = w' * x * w := by
            rw [mul_assoc w' y z']
            rw [← h]
            simp [mul_assoc]
          _ = x * (w' * w) := by
            rw [mul_assoc w' x w]
            group
            rw [mul_comm w' x]
      exact this.symm

  }

instance [CommMonoid M] : HasQuotient M (Submonoid M) where
  quotient' := fun N ↦ Quotient N.Setoid

def QuotientMonoid.mk [CommMonoid M] (N : Submonoid M) : M → M ⧸ N := Quotient.mk N.Setoid

-- x ∼ y ∧ z ∼ w → x*z ∼ y*w
instance [CommMonoid M] (N : Submonoid M) : Monoid (M ⧸ N) where
  mul := Quotient.map₂' (· * ·) (by
      intro x y setoidrxy z w setoidrzw
      rcases setoidrxy with ⟨x', hx', y', hy', h⟩
      rcases setoidrzw with ⟨z', hz', w', hw', h'⟩
      dsimp
      use x'*z'
      constructor
      . exact N.mul_mem hx' hz'
      use y'*w'
      constructor
      . exact N.mul_mem hy' hw'
      group
      calc
        x * z * x' * z' = x * x' * z * z' := by
          rw [mul_assoc x z x', mul_comm z x', ← mul_assoc x x' z]
        _ = (x * x') * (z * z') := by
          simp [mul_assoc]
        _ = (y * y') * (z * z') := by rw [h, h']
        _ = (y * y') * (w * w') := by rw [← h', ← h]
        _ = y * w * y' * w' := by
          group
          rw [mul_assoc y w y', mul_comm w y', ← mul_assoc y y' w]
        )
  mul_assoc := by
      rintro ⟨a⟩ ⟨b⟩ ⟨c⟩
      apply Quotient.sound
      simp [mul_assoc]
      apply @Setoid.refl M N.Setoid

  one := QuotientMonoid.mk N 1
  one_mul := by
      rintro ⟨a⟩
      apply Quotient.sound
      simp
      apply @Setoid.refl M N.Setoid
  mul_one := by
      rintro ⟨a⟩
      apply Quotient.sound
      simp
      apply @Setoid.refl M N.Setoid
