import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0019
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLitG
import Formalism.SharpRestriction.CuspSpanNormBounds.ExpansionFromLemmaB
import Formalism.SharpRestriction.CuspSpanNormBounds.TheoremBConstants
import Formalism.SharpRestriction.CuspSpanNormBounds.DiagonalEntryIdentity
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSB
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0010
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0013

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.GramProductLeHeightBound
section
noncomputable section

open scoped Classical

namespace Formalism.MainNotions.GramProductBounds

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.BridgeLemma₂

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem one_le_prod_max {ι : Type} (s : Finset ι) (f : ι → ℝ) : 1 ≤ ∏ l ∈ s, max 1 (f l) := by
  calc (1 : ℝ) = ∏ _l ∈ s, (1 : ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one) (fun _ _ => le_max_left _ _)

theorem le_prod_max {ι : Type} [DecidableEq ι] {s : Finset ι} {a : ι} (ha : a ∈ s) (f : ι → ℝ) :
    max 1 (f a) ≤ ∏ l ∈ s, max 1 (f l) := by
  rw [← Finset.mul_prod_erase s _ ha]
  exact le_mul_of_one_le_right (le_trans zero_le_one (le_max_left _ _)) (one_le_prod_max _ _)

section Bound

variable (D : D7) (u u' : D.what₂.Word)

theorem absDl_nonneg (Z : GramM D) (l : ℕ) (τ : D.what₂.Tau) : 0 ≤ Cnt.absDl D Z l τ := by
  unfold Cnt.absDl absReal
  refine mul_nonneg (norm_nonneg _) (Real.rpow_nonneg ?_ _)
  unfold Formalism.BasicNotions.Host.rdE
  exact Real.rpow_nonneg (abs_nonneg _) _

theorem one_le_sizeZ (b C : ℝ) (Z : GramM D) : 1 ≤ Cnt.sizeZ D b C Z := by
  unfold Cnt.sizeZ
  calc (1 : ℝ) = ∏ _τ : D.what₂.Tau, (1 : ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one) (fun _ _ => one_le_prod_max _ _)

end Bound

section Fam

def LatticeIdentitySignsGeneric : Prop :=
  ∀ (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A : ℝ),
  Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A →
  ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u →
  ∀ Λ : LatV D, IsRowLat D F0 Λ →
  ∀ F' : FlagU D u', IsTermF D Λ (lf D F0) F' → IsGeneric Λ (gS D) (lf D F0) F' →
    G0 Λ (gS D) (lf D F0) F' = localGramProduct D u u' (ZhatL (lf D F0) F') ∧
    (∀ τ, 0 ≤ Cnt.Gz D (Tu D u) (Tu D u') (ZhatL (lf D F0) F') τ) ∧ 1 ≤ G0 Λ (gS D) (lf D F0) F'

end Fam

end Formalism.MainNotions.GramProductBounds

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.HCFiniteKMultiplicityGapped
section
noncomputable section

namespace Formalism.MainNotions.BridgeDS3

open Formalism.MainNotions Formalism.MainNotions.S

theorem discrete_series_exists_gapped [Fact Formalism.MainNotions.DiscreteSeriesWeylDimension.DiscreteSeriesExistsG] : DiscreteSeriesWeylDimension.DiscreteSeriesExistsG := Fact.out

variable [Fact Formalism.MainNotions.DiscreteSeriesWeylDimension.DiscreteSeriesExistsG] in

theorem discrete_series_exists_fallback : DiscreteSeriesWeylDimension.DiscreteSeriesExistsFallback :=
  DiscreteSeriesWeylDimension.exists_fallback_of_exists_gapped discrete_series_exists_gapped

theorem lowest_K_type_mult_one_gapped [Fact Formalism.MainNotions.DiscreteSeriesWeylDimension.LowKMultOneG] : DiscreteSeriesWeylDimension.LowKMultOneG := Fact.out

theorem discrete_series_unique_gapped [Fact Formalism.MainNotions.BridgeLemma₂.deg_DSUniqG] : BridgeLemma₂.deg_DSUniqG := Fact.out

theorem discrete_series_unique_bessel [Fact Formalism.MainNotions.LeviCoordinates.DiscreteSeriesUniqueBesselGapped] : LeviCoordinates.DiscreteSeriesUniqueBesselGapped := Fact.out

theorem HC_finite_K_multiplicity_gapped [Fact Formalism.MainNotions.BridgeCPX.HCMultDSG] : BridgeCPX.HCMultDSG := Fact.out

end Formalism.MainNotions.BridgeDS3

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.KFinOfLowUnitH
section
noncomputable section

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ENNReal

namespace Formalism.MainNotions.KFiniteLowUnitary

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates Formalism.MainNotions.TheoremBConstants Formalism.MainNotions.DiscreteSeriesInnerProducts Formalism.MainNotions.CayleySignature Formalism.MainNotions.S.UnitaryLevelOperators

section Low

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem conj_mem_Kset' {ε : Fin (2 * r + k + 1) → Bool} {P : Mat k r} (hP : IsCayleyU k r ε P) {g : Mat k r}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (hgu : g ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ) :
    P * g * P⁻¹ ∈ Formalism.REAL.Kset ε := by
  have hPu := hP.2
  have hPs : star P * P = 1 := Matrix.mem_unitaryGroup_iff'.1 hPu
  have hPs' : P * star P = 1 := Matrix.mem_unitaryGroup_iff.1 hPu
  have hinv : P⁻¹ = star P := Matrix.inv_eq_left_inv hPs
  have hgs : g * star g = 1 := Matrix.mem_unitaryGroup_iff.1 hgu
  have hcay : star P * Formalism.REAL.Jm ε * P = Formalism.QuantumDeterminants.Hpk k r := by
    rw [Matrix.star_eq_conjTranspose]; exact hP.1.2
  have hg' : star g * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := by
    rw [Matrix.star_eq_conjTranspose]; exact hg

  have hcomm : Formalism.QuantumDeterminants.Hpk k r * g = g * Formalism.QuantumDeterminants.Hpk k r := by
    calc Formalism.QuantumDeterminants.Hpk k r * g = (g * star g) * Formalism.QuantumDeterminants.Hpk k r * g := by rw [hgs, Matrix.one_mul]
      _ = g * (star g * Formalism.QuantumDeterminants.Hpk k r * g) := by simp only [Matrix.mul_assoc]
      _ = g * Formalism.QuantumDeterminants.Hpk k r := by rw [hg']

  have hJ : Formalism.REAL.Jm ε = P * Formalism.QuantumDeterminants.Hpk k r * star P := by
    rw [← hcay]
    calc Formalism.REAL.Jm ε = (P * star P) * Formalism.REAL.Jm ε * (P * star P) := by
          rw [hPs', Matrix.one_mul, Matrix.mul_one]
      _ = P * (star P * Formalism.REAL.Jm ε * P) * star P := by simp only [Matrix.mul_assoc]
  refine ⟨?_, ?_⟩
  · rw [hinv]
    exact Submonoid.mul_mem _ (Submonoid.mul_mem _ hPu hgu) (Matrix.mem_unitaryGroup_iff.2 (by rw [star_star]; exact hPs))
  · rw [hinv, hJ]
    calc P * g * star P * (P * Formalism.QuantumDeterminants.Hpk k r * star P)
        = P * g * (star P * P) * Formalism.QuantumDeterminants.Hpk k r * star P := by simp only [Matrix.mul_assoc]
      _ = P * (g * Formalism.QuantumDeterminants.Hpk k r) * star P := by rw [hPs, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = P * (Formalism.QuantumDeterminants.Hpk k r * g) * star P := by rw [hcomm]
      _ = P * Formalism.QuantumDeterminants.Hpk k r * (star P * P) * g * star P := by
          rw [hPs, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = P * Formalism.QuantumDeterminants.Hpk k r * star P * (P * g * star P) := by simp only [Matrix.mul_assoc]

theorem kFin_of_lowUnitH' {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {σ : Mat k r → (H →L[ℂ] H)} {w : H} (hw : IsLowUnitH k r ε lam σ w) : IsKFinHpk (k := k) (r := r) σ w := by
  obtain ⟨P, hP, -, hmem⟩ := hw
  have hPd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP.1.1
  have key : ∀ g : Mat k r, P⁻¹ * (P * g * P⁻¹) * P = g := fun g => by
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul P hPd, Matrix.mul_one]
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul P hPd, Matrix.one_mul]
  set ρ : Mat k r → (H →L[ℂ] H) := fun g => σ (P⁻¹ * g * P) with hρ
  set Sset := {S : Submodule ℂ H | IsKTypeOf ε ρ (Formalism.QuantumDeterminants.lowK ε lam) S} with hSset
  have hmem' : w ∈ ⨆ S : Sset, (S : Submodule ℂ H) := by
    rw [← sSup_eq_iSup']; exact hmem
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.1 hmem'
  have : ∀ S : Sset, FiniteDimensional ℂ (S : Submodule ℂ H) := fun S => S.2.1
  refine ⟨s.sup fun S : Sset => (S : Submodule ℂ H), ?_, ?_, ?_⟩
  · infer_instance
  · rw [Finset.sup_eq_iSup]; exact hs
  · intro g hg x hx
    have hK : ∀ S : Sset, ∀ y ∈ (S : Submodule ℂ H), σ g y ∈ (S : Submodule ℂ H) := by
      intro S y hy
      have h1 := S.2.2.1 (P * g * P⁻¹) (conj_mem_Kset' hP hg.1 hg.2) y hy
      simpa only [hρ, key] using h1
    clear hs
    induction s using Finset.induction_on generalizing x with
    | empty =>
      simp only [Finset.sup_empty, Submodule.mem_bot] at hx ⊢
      rw [hx, map_zero]
    | insert S t hS ih =>
      rw [Finset.sup_insert] at hx ⊢
      obtain ⟨y, hy, y', hy', rfl⟩ := Submodule.mem_sup.1 hx
      rw [map_add]
      exact Submodule.add_mem_sup (hK S y hy) (ih y' hy')

end Low

end Formalism.MainNotions.KFiniteLowUnitary

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.NearParameterGap
section
noncomputable section

namespace Formalism.MainNotions.NearParameterGap

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.OnePlaceEstimates

def Cg0 : ℝ := 1000

theorem sizes (Cg m N P s : ℝ) (hCg : 1000 ≤ Cg) (hm2 : 2 ≤ m) (hmN : m ≤ N) (hPN : N ^ 3 ≤ P) (hs : 1 ≤ s) :
    120 * N ^ 3 ≤ Cg * (m ^ 4 * s) * P / 4 ∧ 125 * m ^ 2 * N ^ 3 ≤ Cg * m ^ 4 * P / 32 := by
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hN3 : (0 : ℝ) ≤ N ^ 3 := by positivity
  have hm2' : (4 : ℝ) ≤ m ^ 2 := by nlinarith
  have hm4e : m ^ 4 = m ^ 2 * m ^ 2 := by ring
  have hm4 : (16 : ℝ) ≤ m ^ 4 := by rw [hm4e]; nlinarith
  have hm4' : 4 * m ^ 2 ≤ m ^ 4 := by rw [hm4e]; nlinarith
  have hCg0 : (0 : ℝ) ≤ Cg := by linarith
  constructor
  · have a : (16 : ℝ) ≤ m ^ 4 * s := le_trans hm4 (le_mul_of_one_le_right (by positivity) hs)
    have b : (16000 : ℝ) ≤ Cg * (m ^ 4 * s) := by nlinarith
    have c : 16000 * N ^ 3 ≤ Cg * (m ^ 4 * s) * P :=
      le_trans (mul_le_mul_of_nonneg_right b hN3) (mul_le_mul_of_nonneg_left hPN (by positivity))
    linarith
  · have b : 4000 * m ^ 2 ≤ Cg * m ^ 4 := by nlinarith
    have c : 4000 * m ^ 2 * N ^ 3 ≤ Cg * m ^ 4 * P :=
      le_trans (mul_le_mul_of_nonneg_right b hN3) (mul_le_mul_of_nonneg_left hPN (by positivity))
    linarith

theorem consts (k r : ℕ) (hk : 1 ≤ k) :
    Formalism.FourierDecayAlt.ThreeDimData.Mexp r ≤ (2 * (r : ℝ) + 2) ^ 2 / 2 ∧ 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.Mexp r ∧
    Formalism.FourierDecayAlt.ThreeDimData.AS k r ≤ 2 * (2 * (r : ℝ) + k + 1) ^ 3 ∧ 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.AS k r ∧
    Formalism.FourierDecayAlt.ThreeDimData.AG k r ≤ 4 * (2 * (r : ℝ) + k + 1) ^ 3 ∧ 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.AG k r := by
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  set N : ℝ := 2 * (r : ℝ) + k + 1 with hN
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hN2 : N ^ 2 ≤ N ^ 3 := by nlinarith
  have hdN : Formalism.FourierDecayAlt.ThreeDimData.dN k r ≤ 2 * N ^ 2 := by unfold Formalism.FourierDecayAlt.ThreeDimData.dN; rw [hN]; nlinarith
  have hdN0 : 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.dN k r := by unfold Formalism.FourierDecayAlt.ThreeDimData.dN; nlinarith
  have hnk : ((2 * r + k : ℕ) : ℝ) ≤ N := by rw [hN]; push_cast; linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold Formalism.FourierDecayAlt.ThreeDimData.Mexp; nlinarith
  · unfold Formalism.FourierDecayAlt.ThreeDimData.Mexp; positivity
  · unfold Formalism.FourierDecayAlt.ThreeDimData.AS
    have : ((2 * r + k : ℕ) : ℝ) * Formalism.FourierDecayAlt.ThreeDimData.dN k r ≤ N * (2 * N ^ 2) :=
      mul_le_mul hnk hdN hdN0 (by linarith)
    nlinarith
  · unfold Formalism.FourierDecayAlt.ThreeDimData.AS; positivity
  · unfold Formalism.FourierDecayAlt.ThreeDimData.AG
    have e1 : ((k : ℝ) + r) ≤ N := by rw [hN]; linarith
    have e2 : ((r : ℝ) + 1) ≤ N := by rw [hN]; linarith
    have e3 : ((k : ℝ) + r) * ((r : ℝ) + 1) ≤ N * N := mul_le_mul e1 e2 (by linarith) (by linarith)
    nlinarith
  · unfold Formalism.FourierDecayAlt.ThreeDimData.AG; positivity

end Formalism.MainNotions.NearParameterGap
end
end

