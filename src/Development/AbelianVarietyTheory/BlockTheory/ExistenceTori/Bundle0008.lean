import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0007
import Formalism.LocalToGlobal.ProjectiveLattices.IsCombAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0040
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0002

-- bundled from Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.CuspMultiplicationClosed
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.GoodUniformizationCusps

open NumberField Formalism.L2.Pj Formalism.L2.PjFree ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

def IsGoodUnif (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) : Prop :=
  ∀ σ : c.F →+* ℂ, GoodEmb c σ → IsUnf (U σ)

def Cusp (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (_hn : Even n) :
    Submodule c.F (Rul Xo c) where
  carrier := {f | f ∈ sec Xo c a n ∧
    ∀ σ : c.F →+* ℂ, GoodEmb c σ → ∀ k : (U σ).Comp, rdU (U σ) f k ∈ ((U σ).X k).SS (laU (U σ) a n k)}
  zero_mem' := ⟨Submodule.zero_mem _, fun σ _ k => by
    rw [map_zero]
    exact (siegelSpaceAlgebra_holds r ((U σ).X k) (laU (U σ) a n k) (laU (U σ) a n k) 0).1.1⟩
  add_mem' := fun {f g} hf hg => ⟨Submodule.add_mem _ hf.1 hg.1, fun σ hσ k => by
    rw [map_add]
    exact (siegelSpaceAlgebra_holds r ((U σ).X k) (laU (U σ) a n k) (laU (U σ) a n k) 0).1.2.1 _ (hf.2 σ hσ k) _ (hg.2 σ hσ k)⟩
  smul_mem' := fun b f hf => ⟨Submodule.smul_mem _ b hf.1, fun σ hσ k => by
    rw [map_smulₛₗ]
    exact (siegelSpaceAlgebra_holds r ((U σ).X k) (laU (U σ) a n k) (laU (U σ) a n k) 0).1.2.2 _ _ (hf.2 σ hσ k)⟩

theorem mem_cusp (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (hn : Even n)
    (f : Rul Xo c) : f ∈ Cusp U a n hn ↔ f ∈ sec Xo c a n ∧
      ∀ σ : c.F →+* ℂ, GoodEmb c σ → IsHolCusp (U σ).X (laU (U σ) a n) (rdU (U σ) f) := Iff.rfl

theorem cusp_le_sec (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (hn : Even n) :
    Cusp U a n hn ≤ sec Xo c a n := fun _ hf => hf.1

variable (Xo c) in

def formMul (a a' : (E →+* ℂ) × ℕ → ℕ) (n n' : ℕ) (f : sec Xo c a n) (g : sec Xo c a' n') :
    sec Xo c (a + a') (n + n') :=
  ⟨(f : Rul Xo c) * (g : Rul Xo c), sec_mul Xo c a a' n n' f.2 g.2⟩

def CuspMulClosed (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) : Prop :=
  ∀ (a a' : (E →+* ℂ) × ℕ → ℕ) (n n' : ℕ) (h : Dom a n) (h' : Dom a' n'),
    ∀ f ∈ Cusp U a n h.2, ∀ g ∈ Cusp U a' n' h'.2, f * g ∈ Cusp U (a + a') (n + n') (h.2.add h'.2)

def CuspFinite (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (hn : Even n), FiniteDimensional c.F (Cusp U a n hn)

variable (Xo c r) in

def CuspMulClaim : Prop :=
  ∀ U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r, IsGoodUnif U → CuspMulClosed U

variable (Xo c r) in

def CuspFiniteClaim : Prop :=
  ∀ U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r, IsGoodUnif U → CuspFinite U

theorem laU_add {σ : c.F →+* ℂ} (V : Unf Xo c σ r) (a a' : (E →+* ℂ) × ℕ → ℕ) {n n' : ℕ} (hn : Even n)
    (hn' : Even n') (k : V.Comp) : laU V (a + a') (n + n') k = laU V a n k + laU V a' n' k := by
  obtain ⟨m, rfl⟩ := hn
  obtain ⟨m', rfl⟩ := hn'
  funext τ j
  have e : (m + m + (m' + m')) / 2 = (m + m) / 2 + (m' + m') / 2 := by omega
  simp only [laU, Pi.add_apply, e]
  split_ifs <;> push_cast <;> ring

theorem rdU_mul {σ : c.F →+* ℂ} (V : Unf Xo c σ r) (f g : Rul Xo c) (k : V.Comp) :
    rdU V (f * g) k = rdU V f k * rdU V g k := by
  funext x
  simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, Pi.mul_apply]
  split_ifs with h
  · exact evalAt_mul (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f g (V.un k ⟨x, h⟩)
  · simp

theorem cuspMulClosed (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) : CuspMulClosed U := by
  intro a a' n n' h h' f hf g hg
  refine ⟨sec_mul Xo c a a' n n' hf.1 hg.1, fun σ hσ k => ?_⟩
  rw [laU_add (U σ) a a' h.2 h'.2, rdU_mul]
  exact (siegelSpaceAlgebra_holds r ((U σ).X k) _ _ 0).2.1 _ (hf.2 σ hσ k) _ (hg.2 σ hσ k).1

def cuspMul (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) {a a' : (E →+* ℂ) × ℕ → ℕ} {n n' : ℕ} (h : Dom a n)
    (h' : Dom a' n') (f : Cusp U a n h.2) (g : Cusp U a' n' h'.2) : Cusp U (a + a') (n + n') (h.2.add h'.2) :=
  ⟨(f : Rul Xo c) * (g : Rul Xo c), cuspMulClosed U a a' n n' h h' f.1 f.2 g.1 g.2⟩

end GlobalTheory.IndefiniteRowSideFullHecke.GoodUniformizationCusps
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.CuspSectionNorms
section
namespace GlobalTheory.IndefiniteRowSideFullHecke.CuspSectionNorms

open NumberField ReciprocityTheory.ChartRestriction.G.FD
open scoped ENNReal

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {ι : Type}

abbrev Fn (X : ι → Data E r) : Type := ∀ c : ι, Frame (X c).Ψ r → ℂ

abbrev FamWt (X : ι → Data E r) : Type := ∀ c : ι, Wt (X c).Ψ r

def constWt {X : ι → Data E r} {Ψ : Finset (E →+* ℂ)} (hΨ : ∀ c, (X c).Ψ = Ψ) (la : Wt Ψ r) :
    FamWt X :=
  fun c τ i => la ⟨τ.1, hΨ c ▸ τ.2⟩ i

abbrev FramePt (X : ι → Data E r) : Type := Σ c : ι, (X c).dom

def ptNorm {X : ι → Data E r} (la : FamWt X) (F : Fn X) (p : FramePt X) : ℝ :=
  (X p.1).pnorm (la p.1) (F p.1) p.2.1

def IsCuspSec {X : ι → Data E r} (la : FamWt X) (F : Fn X) : Prop :=
  (∀ c, F c ∈ (X c).SS (la c)) ∧ ∃ C : ℝ, ∀ p : FramePt X, ptNorm la F p ≤ C

def ZeroOff {X : ι → Data E r} (F : Fn X) : Prop :=
  ∀ c, ∀ x, x ∉ (X c).dom → F c x = 0

theorem ptNorm_add_le {X : ι → Data E r} (la : FamWt X) (F G : Fn X) (p : FramePt X) :
    ptNorm la (F + G) p ≤ ptNorm la F p + ptNorm la G p := by
  unfold ptNorm Data.pnorm
  rw [← add_mul]
  exact mul_le_mul_of_nonneg_right (norm_add_le _ _)
    (Finset.prod_nonneg fun _ _ => Finset.prod_nonneg fun _ _ =>
      Real.rpow_nonneg (norm_nonneg _) _)

theorem ptNorm_smul {X : ι → Data E r} (la : FamWt X) (a : ℂ) (F : Fn X) (p : FramePt X) :
    ptNorm la (a • F) p = ‖a‖ * ptNorm la F p := by
  unfold ptNorm Data.pnorm
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_assoc]

def cuspSpace {X : ι → Data E r} (la : FamWt X) : Submodule ℂ (Fn X) where
  carrier := {F | IsCuspSec la F ∧ ZeroOff F}
  zero_mem' := by
    refine ⟨⟨fun c => (siegelSpaceAlgebra_holds r (X c) (la c) (la c) 0).1.1, 0, fun p => ?_⟩, fun _ _ _ => rfl⟩
    simp [ptNorm, Data.pnorm]
  add_mem' := by
    rintro F G ⟨⟨hF, C, hC⟩, hF0⟩ ⟨⟨hG, D, hD⟩, hG0⟩
    refine ⟨⟨fun c => (siegelSpaceAlgebra_holds r (X c) (la c) (la c) 0).1.2.1 _ (hF c) _ (hG c), C + D,
      fun p => (ptNorm_add_le la F G p).trans (add_le_add (hC p) (hD p))⟩, fun c x hx => ?_⟩
    simp [hF0 c x hx, hG0 c x hx]
  smul_mem' := by
    rintro a F ⟨⟨hF, C, hC⟩, hF0⟩
    refine ⟨⟨fun c => (siegelSpaceAlgebra_holds r (X c) (la c) (la c) 0).1.2.2 a _ (hF c), ‖a‖ * C,
      fun p => ?_⟩, fun c x hx => ?_⟩
    · rw [ptNorm_smul]
      exact mul_le_mul_of_nonneg_left (hC p) (norm_nonneg a)
    · simp [hF0 c x hx]

def supE {X : ι → Data E r} (la : FamWt X) (F : Fn X) : ℝ≥0∞ :=
  ⨆ p : FramePt X, ENNReal.ofReal (ptNorm la F p)

def supN {X : ι → Data E r} (la : FamWt X) (F : cuspSpace la) : ℝ :=
  (supE la (F : Fn X)).toReal

theorem isCuspSec_iff_of_finite [Finite ι] {X : ι → Data E r} (la : FamWt X) (F : Fn X) :
    IsCuspSec la F ↔ ∀ c, F c ∈ (X c).SS (la c) := by
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  choose C hC using fun c => (h c).1.2
  obtain ⟨M, hM⟩ := (Set.finite_range C).bddAbove
  exact ⟨M, fun p => (hC p.1 p.2.1 p.2.2).trans (hM ⟨p.1, rfl⟩)⟩

end

end GlobalTheory.IndefiniteRowSideFullHecke.CuspSectionNorms
end

