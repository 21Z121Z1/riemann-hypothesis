import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTorsionFormWithPoint
section
set_option autoImplicit false

noncomputable section

open Matrix MeasureTheory Set Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff ComplexConjugate

namespace GlobalTheory.TorsionForm

def str {m g : ℕ} (K : Ext (m + g) →L[ℂ] Ext (m + g)) : Ext m := fun S =>
  ∑ I : Finset (Fin g), (-1) ^ I.card * K (Pi.single (join ∅ I) 1) (join S I)

def baseMul {n : ℕ} (k : Matrix (Fin n) (Fin n) ℂ) (w : Ext (n + n)) : Ext (n + n) :=
  ∑ i, ∑ l, k i l • wedge (i.castAdd n) (wedge (l.natAdd n) w)

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g n : ℕ}
  (τ : E → Matrix (Fin g) (Fin g) ℂ) (M : Submodule ℤ (Fl g)) (j : Fl g → Pt E g → ℂ)
  (h : Pt E g → ℝ) (β : Fin n → E)

def IsHeatTraceWith (b : E) (k : Matrix (Fin n) (Fin n) ℂ) (F : ℝ → Ext (n + n)) : Prop :=
  ∃ D : Set (Fl g), IsAddFundamentalDomain M D volume ∧ ∀ u > 0, ∃ K,
    IsHeatKernel τ M j h β b u D K ∧
      F u = phi (∫ x in D, (strN (K 1 (per (τ b) x) (per (τ b) x)) +
        ((u : ℂ)⁻¹) • baseMul k (str (K 1 (per (τ b) x) (per (τ b) x)))))

def IsTorsionFormWith (b : E) (k : Matrix (Fin n) (Fin n) ℂ) (T : Ext (n + n)) : Prop :=
  ∃ F, IsHeatTraceWith τ M j h β b k F ∧ ∀ S, IsMellinDeriv (fun u => F u S) (T S)

def IsClosedHerm (B : Set E) (k : E → E →ₗ[ℂ] E →ₗ⋆[ℂ] ℂ) : Prop :=
  (∀ v w, ContDiffOn ℝ ∞ (fun b => k b v w) B) ∧ ∀ b ∈ B, (∀ v w, k b w v = conj (k b v w)) ∧
    ∀ u v w, d10 (fun x => k x v w) b u = d10 (fun x => k x u w) b v

theorem isTorsionFormWith_zero (b : E) (T : Ext (n + n)) :
    IsTorsionFormWith τ M j h β b 0 T ↔ IsTorsionForm τ M j h β b T := by
  simp [IsTorsionFormWith, IsTorsionForm, IsHeatTraceWith, IsHeatTrace, baseMul]

example (k : ℂ) : baseMul (n := 1) (of fun _ _ => k) (Pi.single ∅ 1) Finset.univ = k := by
  have e₁ : (Finset.univ : Finset (Fin 2)).erase 0 = {1} := by decide
  have e₄ : (({1} : Finset (Fin 2)).filter (· = 0)).card = 0 := by decide
  have e₅ : Fin.castAdd 1 (0 : Fin 1) = (0 : Fin 2) := rfl
  have e₆ : Fin.natAdd 1 (0 : Fin 1) = (1 : Fin 2) := rfl
  simp [baseMul, wedge, sgn, e₁, e₄, e₅, e₆]

end GlobalTheory.TorsionForm
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PDivisibleGroupsOverOC
section
noncomputable section

open CategoryTheory Ideal
open scoped TensorProduct

namespace GlobalTheory.Published

open GlobalTheory.PDivGroup

def hodgeTateSubspace {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Algebra ℤ_[p] O] (C : Type) [Field C]
    [Algebra O C] (G : PDivGroup p O) : Submodule C (C ⊗[O] (O ⊗[ℤ_[p]] G.Tate)) :=
  LinearMap.ker (G.hodgeTateLinear.baseChange C)

def PDivisibleGroupsOverOC : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O →
    ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O] [Algebra ℤ_[p] O],
      (∀ (G H : PDivGroup p O) (f : G.Tate →ₗ[ℤ_[p]] H.Tate),
        (∀ x ∈ hodgeTateSubspace C G, (f.baseChange O).baseChange C x ∈ hodgeTateSubspace C H) →
          ∃! φ : G ⟶ H, tateMap G H O φ = f) ∧
      ∀ (h : ℕ) (W : Submodule C (C ⊗[O] (O ⊗[ℤ_[p]] (Fin h → ℤ_[p])))),
        ∃ (G : PDivGroup p O) (e : G.Tate ≃ₗ[ℤ_[p]] (Fin h → ℤ_[p])),
          ∀ x, x ∈ hodgeTateSubspace C G ↔ (e.toLinearMap.baseChange O).baseChange C x ∈ W

end GlobalTheory.Published
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
section
noncomputable section

open CategoryTheory Ideal
open scoped TensorProduct

namespace GlobalTheory.Published

open GlobalTheory.PDivGroup

def ScholzeWeinsteinB : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O →
    ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O] [Algebra ℤ_[p] O],
      (∀ (G H : PDivGroup p O) (f : G.Tate →ₗ[ℤ_[p]] H.Tate),
        (∀ x, G.hodgeTateLinear x = 0 → H.hodgeTateLinear (f.baseChange O x) = 0) →
          ∃! φ : G ⟶ H, tateMap G H O φ = f) ∧
      ∀ (h : ℕ) (W : Submodule O (O ⊗[ℤ_[p]] (Fin h → ℤ_[p]))),
        (∀ (c : O) (x : O ⊗[ℤ_[p]] (Fin h → ℤ_[p])), c ≠ 0 → c • x ∈ W → x ∈ W) →
          ∃ (G : PDivGroup p O) (e : G.Tate ≃ₗ[ℤ_[p]] (Fin h → ℤ_[p])),
            ∀ x, G.hodgeTateLinear x = 0 ↔ e.toLinearMap.baseChange O x ∈ W

end GlobalTheory.Published
end
end

