import Mathlib

-- bundled from ReciprocityTheory.ThetaSummability.RealCoinvariants.GlRelZero
section
noncomputable section

open Finset

namespace ReciprocityTheory.ThetaSummability.Real

section Defs

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

def GlRel {n : ℕ} (E : Fin n → Fin n → Module.End ℂ M) : Prop :=
  ∀ a b c d : Fin n, E a b * E c d - E c d * E a b =
    (if b = c then E a d else 0) - (if d = a then E c b else 0)

def FamComm {n N : ℕ} (E : Fin n → Fin n → Module.End ℂ M) (E' : Fin N → Fin N → Module.End ℂ M) :
    Prop :=
  ∀ a b k l, E a b * E' k l = E' k l * E a b

structure IsCCR {X : Type*} [DecidableEq X] (α β : X → Module.End ℂ M) : Prop where
  β_α : ∀ x y, β x * α y - α y * β x = if x = y then 1 else 0
  α_α : ∀ x y, α x * α y = α y * α x
  β_β : ∀ x y, β x * β y = β y * β x

variable {n N : ℕ}

def oscL (α β : Fin n × Fin N → Module.End ℂ M) (c : ℂ) (a b : Fin n) : Module.End ℂ M :=
  (∑ k, α (a, k) * β (b, k)) + if a = b then c • (1 : Module.End ℂ M) else 0

def oscR (α β : Fin n × Fin N → Module.End ℂ M) (c : ℂ) (k l : Fin N) : Module.End ℂ M :=
  (∑ a, α (a, k) * β (a, l)) + if k = l then c • (1 : Module.End ℂ M) else 0

def signTwist {m : ℕ} (s : Fin m → ℂ) (E : Fin m → Fin m → Module.End ℂ M) (a b : Fin m) :
    Module.End ℂ M :=
  (s a * s b) • E a b

end Defs

def sgn {m : ℕ} (ε : Fin m → Bool) (a : Fin m) : ℂ := if ε a then 1 else -1

end ReciprocityTheory.ThetaSummability.Real
end
end

-- bundled from ReciprocityTheory.ThetaSummability.RealCoinvariants.Numbers
section
noncomputable section

namespace ReciprocityTheory.ThetaSummability.Real

structure RealData where
  a : ℕ
  a' : ℕ
  p : ℕ
  q : ℕ
  κ : ℕ

structure RealData.Hyp (D : RealData) : Prop where
  a_gt : D.a' < D.a
  a'_pos : 1 ≤ D.a'
  even_im_hermitian_sub : (D.a - D.a') % 2 = 0
  h1a : 2 * D.p + 1 ≤ D.a
  h1b : 2 * D.q + 1 ≤ D.a'
  h2 : D.a + D.a' < D.κ
  h3 : D.κ % 2 = 0
  h5 : 2 * (D.p + D.q) < D.a'
  h4 : 2 * D.p + D.a' < D.a

namespace RealData

variable (D : RealData)

def d : ℕ := D.a + D.a'
def y : ℕ := D.p + D.q
def R : ℕ := D.d - D.y
def S : ℕ := D.y
def P : ℕ := D.a - D.p
def Q : ℕ := D.p
def P' : ℕ := D.q
def Q' : ℕ := D.a' - D.q
def e : ℝ := ((D.a : ℝ) - D.a') / 2
def c₁ : ℝ := ((D.R : ℝ) - D.S) / 2
def c₂ : ℝ := ((D.P : ℝ) - D.Q) / 2
def c₂' : ℝ := ((D.P' : ℝ) - D.Q') / 2
def x₁ : ℝ := (D.κ : ℝ) / 2 - D.c₁ + D.c₂
def x₂ : ℝ := D.c₂
def y₁ : ℝ := (D.κ : ℝ) / 2 + D.c₁ - D.c₂
def y₂ : ℝ := -D.c₂

def ω : ℝ := D.x₁ - D.y₂

def ω' : ℝ := D.y₁ - D.x₂

end RealData

def exampleData : RealData := ⟨9, 5, 1, 1, 16⟩

theorem exampleData_hyp : exampleData.Hyp := by
  constructor <;> norm_num [exampleData]

end ReciprocityTheory.ThetaSummability.Real
end
end

