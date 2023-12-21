import MIL.Common
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Real.Basic

set_option autoImplicit true


class One₁ (α : Type) where
  /-- The element one -/
  one : α

@[inherit_doc]
notation "𝟙" => One₁.one

#check One₁.one -- One₁.one {α : Type} [self : One₁ α] : α

example (α : Type) [One₁ α] : α := One₁.one

example (α : Type) [One₁ α] := (One₁.one : α)

instance : One₁ Bool where
  one := true
instance : One₁ Nat where
  one := 1

#eval (𝟙 : ℕ)
#eval (𝟙 : Bool)

@[class] structure One₂ (α : Type) where
  /-- The element one -/
  one : α

#check One₂.one
example {α : Type} [One₁ α] : α := 𝟙

example {α : Type} [One₁ α] : (𝟙 : α) = 𝟙 := rfl

-- magma
class Dia₁ (α : Type) where
  dia : α → α → α

infixl:70 " ⋄ "   => Dia₁.dia

-- associative magma
class Semigroup₁ (α : Type) where
  toDia₁ : Dia₁ α
  /-- Diamond is associative -/
  dia_assoc : ∀ a b c : α, a ⋄ b ⋄ c = a ⋄ (b ⋄ c)

attribute [instance] Semigroup₁.toDia₁

example {α : Type} [Semigroup₁ α] (a b : α) : α := a ⋄ b

class Semigroup₂ (α : Type) extends Dia₁ α where
  dia_assoc : ∀ a b c : α, a ⋄ b ⋄ c = a ⋄ (b ⋄ c)

-- unital magma
class UnitalMagma₁ (α : Type) [One₁ α] extends Dia₁ α where
  one_dia : ∀ a : α, 𝟙 ⋄ a = a
  dia_one : ∀ a : α, a ⋄ 𝟙 = a

-- commutative magma
class CommMagma₁ (α : Type) extends Dia₁ α where
  dia_comm : ∀ a b : α, a ⋄ b = b ⋄ a

example {α : Type} [Semigroup₂ α] (a b : α) : α := a ⋄ b

class DiaOneClass₁ (α : Type) extends One₁ α, Dia₁ α where
  /-- One is a left neutral element for diamond. -/
  one_dia : ∀ a : α, 𝟙 ⋄ a = a
  /-- One is a right neutral element for diamond -/
  dia_one : ∀ a : α, a ⋄ 𝟙 = a

class Rack (α : Type) extends Dia₁ α where
  right_distributive : ∀ a b c : α, a ⋄ (b ⋄ c) = (a ⋄ b) ⋄ (a ⋄ c)
  right_surjection : ∀ a b : α, ∃ c : α, a ⋄ c = b

class Kei (α : Type) extends Rack α where
  involution : ∀ a b : α, a ⋄ b ⋄ b = a

class Quandle (α : Type) extends Rack α where
  idempotence : ∀ a : α, a ⋄ a = a

-- Every group gives rise to a quandle
instance (G : Type) [Group G] : Quandle G where
  dia := fun a b ↦ a * b * a⁻¹
  right_distributive := fun a b c ↦ by group
  right_surjection := fun a b ↦ ⟨a⁻¹ * b * a, by group⟩
  idempotence := fun a ↦ by group

inductive Viergruppe
  | e : Viergruppe
  | a : Viergruppe
  | b : Viergruppe
  | c : Viergruppe
deriving Repr

def viergruppeMul : Viergruppe → Viergruppe → Viergruppe
  | Viergruppe.e, x => x
  | x, Viergruppe.e => x
  | Viergruppe.a, Viergruppe.a => Viergruppe.e
  | Viergruppe.b, Viergruppe.b => Viergruppe.e
  | Viergruppe.c, Viergruppe.c => Viergruppe.e
  | Viergruppe.a, Viergruppe.b => Viergruppe.c
  | Viergruppe.b, Viergruppe.a => Viergruppe.c
  | Viergruppe.a, Viergruppe.c => Viergruppe.b
  | Viergruppe.c, Viergruppe.a => Viergruppe.b
  | Viergruppe.b, Viergruppe.c => Viergruppe.a
  | Viergruppe.c, Viergruppe.b => Viergruppe.a

instance : Group Viergruppe where
  mul := viergruppeMul
  mul_assoc := by
    intro a b c
    cases a <;> cases b <;> cases c <;> rfl
  one := Viergruppe.e
  one_mul := by
    intro a
    cases a <;> rfl
  mul_one := by
    intro a
    cases a <;> rfl
  inv := λ x => x
  mul_left_inv := by
    intro a
    cases a <;> rfl

-- For example, the Viergruppe group gives rise to the Viergruppe quandle
#eval Viergruppe.b ⋄ Viergruppe.a

set_option trace.Meta.synthInstance true in
example {α : Type} [DiaOneClass₁ α] (a b : α) : Prop := a ⋄ b = 𝟙


class Monoid₁ (α : Type) extends Semigroup₁ α, DiaOneClass₁ α

#check Monoid₁.toSemigroup₁
#check Monoid₁.toDiaOneClass₁

-- Lean compiler automatically resolves the two paths to Dia₁ into the same thing.
example {α : Type} [Monoid₁ α] :
  (Monoid₁.toSemigroup₁.toDia₁.dia : α → α → α) = Monoid₁.toDiaOneClass₁.toDia₁.dia := rfl

class Monoid₂ (α : Type) where
  toSemigroup₁ : Semigroup₁ α
  toDiaOneClass₁ : DiaOneClass₁ α

/- Monoid₂.mk {α : Type} (toSemigroup₁ : Semigroup₁ α) (toDiaOneClass₁ : DiaOneClass₁ α) : Monoid₂ α -/
#check Monoid₂.mk

/- Monoid₁.mk {α : Type} [toSemigroup₁ : Semigroup₁ α] [toOne₁ : One₁ α] (one_dia : ∀ (a : α), 𝟙 ⋄ a = a) (dia_one : ∀ (a : α), a ⋄ 𝟙 = a) : Monoid₁ α -/
#check Monoid₁.mk



class Inv₁ (α : Type) where
  /-- The inversion function -/
  inv : α → α

@[inherit_doc]
postfix:max "⁻¹" => Inv₁.inv

class Group₁ (G : Type) extends Monoid₁ G, Inv G where
  inv_dia : ∀ a : G, a⁻¹ ⋄ a = 𝟙


lemma left_inv_eq_right_inv₁ {M : Type} [Monoid₁ M] {a b c : M} (hba : b ⋄ a = 𝟙) (hac : a ⋄ c = 𝟙) : b = c := by
  rw [← DiaOneClass₁.one_dia c, ← hba, Semigroup₁.dia_assoc, hac, DiaOneClass₁.dia_one b]


export DiaOneClass₁ (one_dia dia_one)
export Semigroup₁ (dia_assoc)
export Group₁ (inv_dia)


example {M : Type} [Monoid₁ M] {a b c : M} (hba : b ⋄ a = 𝟙) (hac : a ⋄ c = 𝟙) : b = c := by
  rw [← one_dia c, ← hba, dia_assoc, hac, dia_one b]


lemma inv_eq_of_dia [Group₁ G] {a b : G} (h : a ⋄ b = 𝟙) : a⁻¹ = b := by
  calc
    a⁻¹ = a⁻¹ ⋄ 𝟙 := by rw [dia_one]
    _ = a⁻¹ ⋄ (a ⋄ b) := by rw [h]
    _ = (a⁻¹ ⋄ a) ⋄ b := by rw [dia_assoc]
    _ = 𝟙 ⋄ b := by rw [inv_dia]
    _ = b := by rw [one_dia]

lemma double_inv [Group₁ G] (a : G) : (a⁻¹)⁻¹ = a := by
  apply inv_eq_of_dia; rw [inv_dia]

lemma dia_inv [Group₁ G] (a : G) : a ⋄ a⁻¹ = 𝟙 := by
  calc
    a ⋄ a⁻¹ = (a⁻¹)⁻¹ ⋄ a⁻¹ := by rw [double_inv]
    _ = 𝟙 := by rw [inv_dia]


class AddSemigroup₃ (α : Type) extends Add α where
/-- Addition is associative -/
  add_assoc₃ : ∀ a b c : α, a + b + c = a + (b + c)

@[to_additive AddSemigroup₃]
class Semigroup₃ (α : Type) extends Mul α where
/-- Multiplication is associative -/
  mul_assoc₃ : ∀ a b c : α, a * b * c = a * (b * c)

class AddMonoid₃ (α : Type) extends AddSemigroup₃ α, AddZeroClass α

@[to_additive AddMonoid₃]
class Monoid₃ (α : Type) extends Semigroup₃ α, MulOneClass α

attribute [to_additive existing] Monoid₃.toMulOneClass

export Semigroup₃ (mul_assoc₃)
export AddSemigroup₃ (add_assoc₃)

whatsnew in
@[to_additive]
lemma left_inv_eq_right_inv' {M : Type} [Monoid₃ M] {a b c : M} (hba : b * a = 1) (hac : a * c = 1) : b = c := by
  rw [← one_mul c, ← hba, mul_assoc₃, hac, mul_one b]

#check left_neg_eq_right_neg'

class AddCommSemigroup₃ (α : Type) extends AddSemigroup₃ α where
  add_comm : ∀ a b : α, a + b = b + a

@[to_additive AddCommSemigroup₃]
class CommSemigroup₃ (α : Type) extends Semigroup₃ α where
  mul_comm : ∀ a b : α, a * b = b * a

class AddCommMonoid₃ (α : Type) extends AddMonoid₃ α, AddCommSemigroup₃ α

@[to_additive AddCommMonoid₃]
class CommMonoid₃ (α : Type) extends Monoid₃ α, CommSemigroup₃ α

class AddGroup₃ (G : Type) extends AddMonoid₃ G, Neg G where
  neg_add : ∀ a : G, -a + a = 0

@[to_additive AddGroup₃]
class Group₃ (G : Type) extends Monoid₃ G, Inv G where
  inv_mul : ∀ a : G, a⁻¹ * a = 1


attribute [simp] Group₃.inv_mul AddGroup₃.neg_add



@[to_additive]
lemma inv_eq_of_mul [Group₃ G] {a b : G} (h : a * b = 1) : a⁻¹ = b :=
  sorry


@[to_additive (attr := simp)]
lemma Group₃.mul_inv {G : Type} [Group₃ G] {a : G} : a * a⁻¹ = 1 := by
  sorry

@[to_additive]
lemma mul_left_cancel₃ {G : Type} [Group₃ G] {a b c : G} (h : a * b = a * c) : b = c := by
  sorry

@[to_additive]
lemma mul_right_cancel₃ {G : Type} [Group₃ G] {a b c : G} (h : b*a = c*a) : b = c := by
  sorry

class AddCommGroup₃ (G : Type) extends AddGroup₃ G, AddCommMonoid₃ G

@[to_additive AddCommGroup₃]
class CommGroup₃ (G : Type) extends Group₃ G, CommMonoid₃ G



class Ring₃ (R : Type) extends AddGroup₃ R, Monoid₃ R, MulZeroClass R where
  /-- Multiplication is left distributive over addition -/
  left_distrib : ∀ a b c : R, a * (b + c) = a * b + a * c
  /-- Multiplication is right distributive over addition -/
  right_distrib : ∀ a b c : R, (a + b) * c = a * c + b * c

-- a + a + b + b = 2 * a + 2 * b = 2 * (a + b) = a + b + a + b
-- then cancel on both sides to get (a + b = b + a)
instance {R : Type} [Ring₃ R] : AddCommGroup₃ R :=
{ Ring₃.toAddGroup₃ with
  add_comm := by
    intro a b
    have h : a + a + b + b = (a + b) + (a + b) := by
      calc
        a + a + b + b = (a + a) + (b + b) := by rw [add_assoc₃, add_assoc₃]
        _ = (1 * a + 1 * a) + (1 * b + 1 * b) := by simp
        _ = (1 + 1) * a + (1 * b + 1 * b) := by
          rw [← Ring₃.right_distrib 1 1 a]
        _ = (1 + 1) * a + (1 + 1) * b := by
          rw [← Ring₃.right_distrib 1 1 b]
        _ = (1 + 1) * (a + b) := by rw [Ring₃.left_distrib]
        _ = (1 * (a + b) + 1 * (a + b)) := by
          rw [Ring₃.right_distrib 1 1 (a + b)]
        _ = (a + b) + (a + b):= by simp
    calc
      a + b = 0 + (a + b) + 0 := by simp
      _ = (-a + a) + (a + b) + (b + -b) := by simp
      _ = (-a) + (a + a + b + b) + (-b) := by
        repeat rw [add_assoc₃]
      _ = (-a) + ((a + b)+ (a + b)) + (-b) := by
        rw [h]
      _ = b + a := by
        simp [add_assoc₃]
        rw [← (add_assoc₃ (-a) a (b + a))]
        simp
}

instance : Ring₃ ℤ where
  add := (· + ·)
  add_assoc₃ := add_assoc
  zero := 0
  zero_add := by simp
  add_zero := by simp
  neg := (- ·)
  neg_add := by simp
  mul := (· * ·)
  mul_assoc₃ := mul_assoc
  one := 1
  one_mul := by simp
  mul_one := by simp
  zero_mul := by simp
  mul_zero := by simp
  left_distrib := Int.mul_add
  right_distrib := Int.add_mul

class LE₁ (α : Type) where
  /-- The Less-or-Equal relation. -/
  le : α → α → Prop

@[inherit_doc] infix:50 " ≤₁ " => LE₁.le

class Preorder₁ (α : Type)

class PartialOrder₁ (α : Type)

class OrderedCommMonoid₁ (α : Type)

instance : OrderedCommMonoid₁ ℕ where

class SMul₃ (α : Type) (β : Type) where
  /-- Scalar multiplication -/
  smul : α → β → β

infixr:73 " • " => SMul₃.smul


class Module₁ (R : Type) [Ring₃ R] (M : Type) [AddCommGroup₃ M] extends SMul₃ R M where
  zero_smul : ∀ m : M, (0 : R) • m = 0
  one_smul : ∀ m : M, (1 : R) • m = m
  mul_smul : ∀ (a b : R) (m : M), (a * b) • m = a • b • m
  add_smul : ∀ (a b : R) (m : M), (a + b) • m = a • m + b • m
  smul_add : ∀ (a : R) (m n : M), a • (m + n) = a • m + a • n

instance selfModule (R : Type) [Ring₃ R] : Module₁ R R where
  smul := fun r s ↦ r*s
  zero_smul := zero_mul
  one_smul := one_mul
  mul_smul := mul_assoc₃
  add_smul := Ring₃.right_distrib
  smul_add := Ring₃.left_distrib

def nsmul₁ [Zero M] [Add M] : ℕ → M → M
  | 0, _ => 0
  | n + 1, a => a + nsmul₁ n a

def zsmul₁ {M : Type*} [Zero M] [Add M] [Neg M] : ℤ → M → M
  | Int.ofNat n, a => nsmul₁ n a
  | Int.negSucc n, a => -nsmul₁ n.succ a

instance abGrpModule (A : Type) [AddCommGroup₃ A] : Module₁ ℤ A where
  smul := zsmul₁
  zero_smul := sorry
  one_smul := sorry
  mul_smul := sorry
  add_smul := sorry
  smul_add := sorry

#synth Module₁ ℤ ℤ -- abGrpModule ℤ


class AddMonoid₄ (M : Type) extends AddSemigroup₃ M, AddZeroClass M where
  /-- Multiplication by a natural number. -/
  nsmul : ℕ → M → M := nsmul₁
  /-- Multiplication by `(0 : ℕ)` gives `0`. -/
  nsmul_zero : ∀ x, nsmul 0 x = 0 := by intros; rfl
  /-- Multiplication by `(n + 1 : ℕ)` behaves as expected. -/
  nsmul_succ : ∀ (n : ℕ) (x), nsmul (n + 1) x = x + nsmul n x := by intros; rfl

instance mySMul {M : Type} [AddMonoid₄ M] : SMul ℕ M := ⟨AddMonoid₄.nsmul⟩

instance (M N : Type) [AddMonoid₄ M] [AddMonoid₄ N] : AddMonoid₄ (M × N) where
  add := fun p q ↦ (p.1 + q.1, p.2 + q.2)
  add_assoc₃ := fun a b c ↦ by ext <;> apply add_assoc₃
  zero := (0, 0)
  zero_add := fun a ↦ by ext <;> apply zero_add
  add_zero := fun a ↦ by ext <;> apply add_zero

instance : AddMonoid₄ ℤ where
  add := (· + ·)
  add_assoc₃ := Int.add_assoc
  zero := 0
  zero_add := Int.zero_add
  add_zero := Int.add_zero
  nsmul := fun n m ↦ (n : ℤ) * m
  nsmul_zero := Int.zero_mul
  nsmul_succ := fun n m ↦ show (n + 1 : ℤ) * m = m + n * m
    by rw [Int.add_mul, Int.add_comm, Int.one_mul]

example (n : ℕ) (m : ℤ) : SMul.smul (self := mySMul) n m = n * m := rfl
