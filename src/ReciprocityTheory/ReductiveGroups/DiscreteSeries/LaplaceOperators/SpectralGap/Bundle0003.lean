import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.NonvanishingHypotheses
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0374
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.ContinuousBlkWConj
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.Bundle0002
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSchur

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.CayleyIndep
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS
open Matrix

theorem cayleyIndep : CayleyIndepStatement := by
  intro k r ε lam H _ _ _ σ P₀ P h0 h1 hDS
  set σ₁ : Mat k r → (H →L[ℂ] H) := fun g => σ (P₀⁻¹ * g * P₀) with hσ₁
  have e0 : star P₀ * P₀ = 1 := Matrix.mem_unitaryGroup_iff'.mp h0.2
  have e0' : P₀ * star P₀ = 1 := Matrix.mem_unitaryGroup_iff.mp h0.2
  have e1 : star P * P = 1 := Matrix.mem_unitaryGroup_iff'.mp h1.2
  have e1' : P * star P = 1 := Matrix.mem_unitaryGroup_iff.mp h1.2
  have hinv0 : P₀⁻¹ = star P₀ := Matrix.inv_eq_left_inv e0
  have hinv1 : P⁻¹ = star P := Matrix.inv_eq_left_inv e1
  have hH0 := h0.1.2
  have hH1 := h1.1.2
  have hJ : star P₀ * Formalism.REAL.Jm ε * P₀ = star P * Formalism.REAL.Jm ε * P := by
    rw [Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose, hH0, hH1]
  have hbK : P₀ * star P ∈ Formalism.REAL.Kset ε := by
    refine ⟨Submonoid.mul_mem _ h0.2 (Matrix.mem_unitaryGroup_iff.mpr (by rw [star_star]; exact e1)), ?_⟩
    calc P₀ * star P * Formalism.REAL.Jm ε = P₀ * (star P * Formalism.REAL.Jm ε * P) * star P := by
          rw [Matrix.mul_assoc P₀ _ (star P), Matrix.mul_assoc (star P * _) P (star P), e1', Matrix.mul_one,
            Matrix.mul_assoc]
      _ = P₀ * (star P₀ * Formalism.REAL.Jm ε * P₀) * star P := by rw [hJ]
      _ = Formalism.REAL.Jm ε * (P₀ * star P) := by
          simp only [← Matrix.mul_assoc]
          rw [e0', Matrix.one_mul]
  have haK : P * star P₀ ∈ Formalism.REAL.Kset ε := by
    refine ⟨Submonoid.mul_mem _ h1.2 (Matrix.mem_unitaryGroup_iff.mpr (by rw [star_star]; exact e0)), ?_⟩
    calc P * star P₀ * Formalism.REAL.Jm ε = P * (star P₀ * Formalism.REAL.Jm ε * P₀) * star P₀ := by
          rw [Matrix.mul_assoc P _ (star P₀), Matrix.mul_assoc (star P₀ * _) P₀ (star P₀), e0', Matrix.mul_one,
            Matrix.mul_assoc]
      _ = P * (star P * Formalism.REAL.Jm ε * P) * star P₀ := by rw [hJ]
      _ = Formalism.REAL.Jm ε * (P * star P₀) := by
          simp only [← Matrix.mul_assoc]
          rw [e1', Matrix.one_mul]
  have hbU := ReciprocityTheory.ChartRestriction.DS.Lap.CayleyIndepA.kset_uj hbK
  have haU := ReciprocityTheory.ChartRestriction.DS.Lap.CayleyIndepA.kset_uj haK
  have hab : P * star P₀ * (P₀ * star P) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (star P₀), e0, Matrix.one_mul, e1']
  have hba : P₀ * star P * (P * star P₀) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (star P), e1, Matrix.one_mul, e0']
  have hfun : (fun g => σ (P⁻¹ * g * P)) = fun g => σ₁ (P₀ * star P * g * (P * star P₀)) := by
    funext g
    rw [hσ₁]
    congr 1
    rw [hinv0, hinv1]
    simp only [← Matrix.mul_assoc]
    rw [e0, Matrix.one_mul]
    simp only [Matrix.mul_assoc]
    rw [e0, Matrix.mul_one]
  obtain ⟨hc, hnt, hU, hI, hS, ⟨S0, hS0⟩, hmin⟩ := hDS
  rw [hfun]
  refine ⟨⟨hc, hnt, ?_, ?_, ?_, ⟨S0, ?_⟩, fun μ S hS' => hmin μ S ?_⟩, ?_⟩
  · apply ReciprocityTheory.ChartRestriction.DS.Lap.CayleyIndepA.urep_conj
    all_goals first | assumption | exact hU
  · apply ReciprocityTheory.ChartRestriction.DS.Lap.CayleyIndepA.irred_conj (hirr := hI)
    all_goals first | assumption | exact hU
  · apply ReciprocityTheory.ChartRestriction.DS.Lap.CayleyIndepA.sqint_conj (hsq := hS)
    all_goals first | assumption | exact hU
  · rw [ReciprocityTheory.ChartRestriction.DS.Lap.CayleyIndepA.ktype_iff]
    · exact hS0
    all_goals first | assumption | exact hU
  · rw [ReciprocityTheory.ChartRestriction.DS.Lap.CayleyIndepA.ktype_iff] at hS'
    · exact hS'
    all_goals first | assumption | exact hU
  · unfold Formalism.MainNotions.S.lowKSub
    refine congrArg sSup (Set.ext fun S => ?_)
    simp only [Set.mem_setOf_eq]
    rw [ReciprocityTheory.ChartRestriction.DS.Lap.CayleyIndepA.ktype_iff]
    all_goals first | assumption | exact hU

end ReciprocityTheory.ChartRestriction.DS.Lap
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.ContinuousLmulM
section
noncomputable section

open MeasureTheory Matrix

namespace ReciprocityTheory.ChartRestriction.DS.Lap

theorem continuous_lmulM' {k r : ℕ} (s : Mat k r) : Continuous (Formalism.QuantumDeterminants.lmulM (k := k) (r := r) s) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [Formalism.QuantumDeterminants.lmulM, Matrix.mul_apply, Matrix.of_apply]
  exact continuous_finsetSum _ fun l _ => continuous_const.mul ((continuous_apply j).comp (continuous_apply l))

def ptsOf {k r : ℕ} (U : Set (Mat k r)) : Set (Formalism.QuantumDeterminants.Mt k r) := {x | Matrix.of x ∈ U}

def ptsGroup {k r : ℕ} {U : Set (Mat k r)} (hU : Formalism.FourierDecayAlt.B2.IsClosedSubgroup U) : Group (ptsOf U) where
  mul a b := ⟨(Matrix.of a.1 * Matrix.of b.1 : Mat k r), hU.mul_mem (Matrix.of a.1) a.2 (Matrix.of b.1) b.2⟩
  one := ⟨(1 : Mat k r), hU.one_mem⟩
  inv a := ⟨((Matrix.of a.1)⁻¹ : Mat k r), hU.inv_mem (Matrix.of a.1) a.2⟩
  mul_assoc a b c := Subtype.ext (Matrix.mul_assoc (Matrix.of a.1) (Matrix.of b.1) (Matrix.of c.1))
  one_mul a := Subtype.ext (Matrix.one_mul (Matrix.of a.1))
  mul_one a := Subtype.ext (Matrix.mul_one (Matrix.of a.1))
  inv_mul_cancel a := Subtype.ext (Matrix.nonsing_inv_mul (Matrix.of a.1) (hU.unit (Matrix.of a.1) a.2))

end ReciprocityTheory.ChartRestriction.DS.Lap
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.SchurB
section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace ReciprocityTheory.ChartRestriction.DS.Lap

namespace SchurBAux

open Formalism.QuantumDeterminants

theorem conj_cancel {k r : ℕ} {P : Mat k r} (hd : IsUnit P.det) (g : Mat k r) :
    P⁻¹ * (P * g * P⁻¹) * P = g := by
  simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hd, Matrix.nonsing_inv_mul _ hd,
    Matrix.mul_one]

theorem conj_cancel' {k r : ℕ} {P : Mat k r} (hd : IsUnit P.det) (g : Mat k r) :
    P * (P⁻¹ * g * P) * P⁻¹ = g := by
  simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hd, Matrix.mul_nonsing_inv _ hd,
    Matrix.mul_one]

theorem conj_mul {k r : ℕ} {P : Mat k r} (hd : IsUnit P.det) (a b : Mat k r) :
    P * (a * b) * P⁻¹ = (P * a * P⁻¹) * (P * b * P⁻¹) := by
  simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hd]

theorem conj_inUJ {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {P : Mat k r} (hP : Formalism.MainNotions.S.IsCayley k r ε P)
    {a : Mat k r} (ha : a ∈ UH (Hpk k r)) : Formalism.REAL.inUJ ε (P * a * P⁻¹) := by
  obtain ⟨hPu, hPe⟩ := hP
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hPu
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have hq1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hd
  have hq2 : (P⁻¹)ᴴ * Pᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hq1, Matrix.conjTranspose_one]
  show (P * a * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * a * P⁻¹) = Formalism.REAL.Jm ε
  calc (P * a * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * a * P⁻¹)
      = (P⁻¹)ᴴ * (aᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * a) * P⁻¹ := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (P⁻¹)ᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * P⁻¹ := by rw [hPe, ha']
    _ = ((P⁻¹)ᴴ * Pᴴ) * Formalism.REAL.Jm ε * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [hq1, hq2, Matrix.one_mul, Matrix.mul_one]

theorem cont_conj {k r : ℕ} (A B : Mat k r) :
    Continuous (fun x : Mt k r => ((A * Matrix.of x * B : Mat k r) : Mt k r)) := by
  exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

theorem measEmb {k r : ℕ} (ε : Fin (2 * r + k + 1) → Bool) {P : Mat k r} (hd : IsUnit P.det) :
    MeasurableEmbedding (α := Formalism.REAL.UJ ε) (β := Mt k r) (fun g => ((P⁻¹ * Formalism.MainNotions.S.umat g * P : Mat k r) : Mt k r)) := by
  let e : Mt k r ≃ₜ Mt k r :=
    { toFun := fun x => ((P⁻¹ * Matrix.of x * P : Mat k r) : Mt k r)
      invFun := fun x => ((P * Matrix.of x * P⁻¹ : Mat k r) : Mt k r)
      left_inv := fun x => conj_cancel' hd (Matrix.of x)
      right_inv := fun x => conj_cancel hd (Matrix.of x)
      continuous_toFun := cont_conj _ _
      continuous_invFun := cont_conj _ _ }
  have h1 : Topology.IsClosedEmbedding (fun g : Formalism.REAL.UJ ε => (Formalism.MainNotions.S.umat g : Mt k r)) :=
    (Formalism.REAL.isClosedEmbeddingMatrix _ ε).1
  exact (e.isClosedEmbedding.comp h1).measurableEmbedding

end SchurBAux

open Formalism.QuantumDeterminants SchurBAux

theorem schurB : SchurBStatement := by
  intro k r ε lam H _ _ _ σ μG hDSH hH
  obtain ⟨P, ⟨hCay, _⟩, hDS⟩ := hDSH
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hCay.1
  obtain ⟨σ', hσ'⟩ : ∃ σ' : Mat k r → (H →L[ℂ] H), σ' = fun g => σ (P⁻¹ * g * P) := ⟨_, rfl⟩
  rw [← hσ'] at hDS
  have hrep : ∀ g, σ g = σ' (P * g * P⁻¹) := by
    intro g; rw [hσ']; exact (congrArg σ (conj_cancel hd g)).symm
  have uj : ∀ a ∈ UH (Hpk k r), P * a * P⁻¹ ∈ Formalism.MainNotions.S.UJset ε := fun a ha => conj_inUJ hCay ha
  obtain ⟨⟨h1, hmul⟩, hiso, hcont⟩ := hDS.2.2.1
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · rw [hrep, Matrix.mul_one, Matrix.mul_nonsing_inv _ hd]; exact h1
  · intro a ha b hb
    rw [hrep (a * b), hrep a, hrep b, conj_mul hd]
    exact hmul _ (uj a ha) _ (uj b hb)
  · intro g hg v
    rw [hrep]; exact hiso _ (uj g hg) v
  · intro v
    have hc : Continuous (fun g : Mat k r => P * g * P⁻¹) :=
      (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    refine ((hcont v).comp hc.continuousOn (fun g hg => uj g hg)).congr ?_
    intro g _
    show σ g v = σ' (P * g * P⁻¹) v
    rw [← hrep]
  · obtain ⟨d, hd0, hF⟩ := Formalism.MainNotions.BridgeCSchur.fdeg_of_DS lam σ' hDS
    have hmap := haarMap k r ε P hCay
    obtain ⟨c, hc, hμ⟩ := haarUniq2 k r _ _ μG (closedSubgroups k r 0).1 hmap hH
    have hemb := measEmb ε hd
    refine ⟨d / (c : ℝ), div_pos hd0 (by exact_mod_cast hc), fun v w v' w' => ?_⟩
    subst hσ'
    have hint := (hF v w v' w').1
    have hval := (hF v w v' w').2
    rw [hμ]
    refine ⟨((hemb.integrable_map_iff (g := fun x : Mt k r => ⟪w, σ (Matrix.of x) v⟫_ℂ * star ⟪w', σ (Matrix.of x) v'⟫_ℂ)).mpr hint).smul_measure_nnreal, ?_⟩
    calc _ = c • (⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ)) := by
          rw [integral_smul_nnreal_measure, hemb.integral_map]; exact congrArg (c • ·) hval
      _ = _ := by
          rw [NNReal.smul_def, Complex.real_smul]; push_cast; rw [div_div_eq_mul_div]; ring

end ReciprocityTheory.ChartRestriction.DS.Lap
end
end

