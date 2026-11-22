import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0077
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0090
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0119
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0094
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0088
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0104
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0035
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0120
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0059
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0041
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0023
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0002
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.MuPotentialSmoothOffBoundary
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Statements.MetricStatements.ExistsFlagModelBaseMetric
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0125
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0108
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0025
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0014
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0004
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0038
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0037
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0014
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedDensityNonnegOffNullSet
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0008
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PeriodDecompositionNearBoundary
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0084
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0018
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsAntisym
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0056
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0028
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0041
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0036
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0038
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0035
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0045
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0049
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0050
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0021
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0034
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0014
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0025
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0029
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0013
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0121
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0096

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticNinth
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph

namespace GlobalTheory.CompanionTheory.Ar.PB.CovGraph

section Pair

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {K' : Type} [Fintype K']
  {ι' : K' → Type} [∀ k, Fintype (ι' k)] {Ω : Type} [Field Ω]

theorem mConeMap_pair_inl (a : (Σ k, ι k) → Ω) (b : (Σ k, ι' k) → Ω) (g : MRing ι) :
    mConeMap (pairV a b) (rename inlV g) = rename Sum.inl (mConeMap a g) := by
  induction g using MvPolynomial.induction_on with
  | C c => simp [mConeMap]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p n hp =>
    simp only [map_mul, hp, rename_X]
    congr 1
    simp [mConeMap, inlV, pairV]

theorem mConeMap_pair_inr (a : (Σ k, ι k) → Ω) (b : (Σ k, ι' k) → Ω) (g : MRing ι') :
    mConeMap (pairV a b) (rename inrV g) = rename Sum.inr (mConeMap b g) := by
  induction g using MvPolynomial.induction_on with
  | C c => simp [mConeMap]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p n hp =>
    simp only [map_mul, hp, rename_X]
    congr 1
    simp [mConeMap, inrV, pairV]

theorem imageZ_inl (a : (Σ k, ι k) → Ω) (b : (Σ k, ι' k) → Ω) :
    imageZ inlV (mCoordIdeal (pairV a b)) = mCoordIdeal a := by
  ext f
  show mConeMap (pairV a b) (rename inlV f) = 0 ↔ mConeMap a f = 0
  rw [mConeMap_pair_inl]
  exact (rename_injective _ Sum.inl_injective).eq_iff' (map_zero _)

theorem imageZ_inr (a : (Σ k, ι k) → Ω) (b : (Σ k, ι' k) → Ω) :
    imageZ inrV (mCoordIdeal (pairV a b)) = mCoordIdeal b := by
  ext f
  show mConeMap (pairV a b) (rename inrV f) = 0 ↔ mConeMap b f = 0
  rw [mConeMap_pair_inr]
  exact (rename_injective _ Sum.inr_injective).eq_iff' (map_zero _)

end Pair

theorem pts : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M), ∀ z ∈ mcPts (mCoordIdeal y'), ∀ w ∈ mcPts (mCoordIdeal y), CovMap.IsImg Cv z w →
    pairV w z ∈ mcPts (mCoordIdeal (pairV (transPt Cv) y')) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M K' _ ι' _ Φ' _ y' M' Cv z hz w hw himg
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.flag_model_base_projection_points K' ι' Φ' y' Ψ N j M'
  obtain ⟨-, g2, -⟩ := GlobalTheory.T.flag_model_base_projection_points K ι Φ y Ψ N j M
  obtain ⟨F', hF', hG'⟩ := h2 _ (h1 z hz)
  have hch : ∀ k : NonPluckerBlocks M'.blk, basePart M'.blk z ⟨k, F'.c k⟩ ≠ 0 := fun k h0 => hG'.1 k (by
    show mConeMap _ (X _) = 0
    simp [mConeMap, h0])
  obtain ⟨c₁, hc₁, hcb⟩ : ∃ c₁ : K' → ℂ, (∀ k, c₁ k ≠ 0) ∧
      ∀ k : NonPluckerBlocks M'.blk, c₁ k.1 * basePart M'.blk z ⟨k, F'.c k⟩ = 1 := by
    refine ⟨fun k => if hk : ∀ p, M'.blk p ≠ some k then (basePart M'.blk z ⟨⟨k, hk⟩, F'.c ⟨k, hk⟩⟩)⁻¹ else 1,
      fun k => ?_, fun k => ?_⟩
    · by_cases hk : ∀ p, M'.blk p ≠ some k
      · simp only [dif_pos hk]
        exact inv_ne_zero (hch ⟨k, hk⟩)
      · simp only [dif_neg hk]
        exact one_ne_zero
    · simp only [dif_pos k.2]
      exact inv_mul_cancel₀ (hch k)
  let z₁ : (Σ k, ι' k) → ℂ := fun q => c₁ q.1 * z q
  have hz₁ : z₁ ∈ mcPts (mCoordIdeal y') :=
    mcPts_smul (CoordinateConeArithVar.isMultiHomogIdeal y') c₁ hc₁ hz
  have hb₁ : basePart M'.blk z₁ = fun q => (fun k : NonPluckerBlocks M'.blk => c₁ k.1) q.1 * basePart M'.blk z q := rfl
  have hI : mCoordIdeal (basePart M'.blk z₁) = mCoordIdeal (basePart M'.blk z) := by
    rw [hb₁]
    exact StepW.TorusAct.mCoordIdeal_torus (ι := baseIdx ι' M'.blk) (fun k : NonPluckerBlocks M'.blk => c₁ k.1)
      (fun k => hc₁ k.1) (basePart M'.blk z)
  have hG₁ : M'.GoodAt F' (mCoordIdeal (basePart M'.blk z₁)) := by rw [hI]; exact hG'
  have hnorm : ∀ k, basePart M'.blk z₁ ⟨k, F'.c k⟩ = 1 := hcb
  obtain ⟨h, hh⟩ := (h3 F' hF' z₁ (h1 z₁ hz₁) hG₁ hnorm).1 hz₁
  have hv := GlobalTheory.T.flag_cover_base_point_maps_to_points K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv _ (h1 z₁ hz₁)
  obtain ⟨F, hF, hG⟩ := g2 _ hv
  obtain ⟨z₀, ho, hb, hfl⟩ := himg z₁ ⟨c₁, hc₁, rfl⟩ F' F hF' hF hG₁ hG h hh
  obtain ⟨cw, hcw, hzw⟩ := ho
  have hz0 : ∀ k, ∃ i, z₀ ⟨k, i⟩ ≠ 0 := fun k => by
    obtain ⟨i, hi⟩ := hw.1 k
    exact ⟨i, by rw [hzw]; exact mul_ne_zero (hcw k) hi⟩
  have hblk : ∀ kk : K ⊕ K', ∃ (e : Φ') (s : Sum.elim ι ι' kk → Φ') (t : ℂ), e ≠ 0 ∧ t ≠ 0 ∧ ∀ i,
      pairV (transPt Cv) y' ⟨kk, i⟩ = e * s i ∧ IsValueAt y' (s i) z₁ (t * pairV z₀ z₁ ⟨kk, i⟩) := by
    rintro (k | k)
    · by_cases hk : ∀ p, M.blk p ≠ some k
      · exact GlobalTheory.T.flag_cover_base_block_value K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv z₁ z₀ ⟨k, hk⟩ hz₁ hb
      · obtain ⟨p, hp⟩ : ∃ p, M.blk p = some k := by simpa using hk
        exact GlobalTheory.T.flag_cover_frames_lift_point K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv z₁ z₀ F' F h p k hz₁ hF' hF hG₁ hG hh hfl hb hp
    · obtain ⟨c, hc⟩ := hz₁.1 k
      obtain ⟨hy0, hval⟩ := GlobalTheory.T.coordinate_ratio_value_at_point K' ι' Φ' y' z₁ k c hz₁ hc
      exact ⟨y' ⟨k, c⟩, fun i => y' ⟨k, i⟩ / y' ⟨k, c⟩, (z₁ ⟨k, c⟩)⁻¹, hy0, inv_ne_zero hc,
        fun i => ⟨(mul_div_cancel₀ _ hy0).symm, hval i⟩⟩
  choose e s t he ht hs using hblk
  have hnz : ∀ kk : K ⊕ K', ∃ i : Sum.elim ι ι' kk, pairV z₀ z₁ ⟨kk, i⟩ ≠ 0 := by
    rintro (k | k)
    · exact hz0 k
    · exact hz₁.1 k
  have hpt := GlobalTheory.T.scaled_coordinates_value_at_point (K ⊕ K') (Sum.elim ι ι') K' ι' Φ' (pairV (transPt Cv) y') y' z₁ (pairV z₀ z₁) e
    (fun q => s q.1 q.2) t hz₁ hnz he ht (fun q => (hs q.1 q.2).1) (fun q => (hs q.1 q.2).2)
  have hsm := mcPts_smul (CoordinateConeArithVar.isMultiHomogIdeal (pairV (transPt Cv) y'))
    (Sum.elim (fun k => (cw k)⁻¹) fun k => (c₁ k)⁻¹)
    (by
      rintro (k | k)
      · exact inv_ne_zero (hcw k)
      · exact inv_ne_zero (hc₁ k)) hpt
  convert hsm using 1
  funext ⟨kk, i⟩
  rcases kk with k | k
  · show w ⟨k, i⟩ = (cw k)⁻¹ * z₀ ⟨k, i⟩
    rw [hzw]
    exact (inv_mul_cancel_left₀ (hcw k) _).symm
  · show z ⟨k, i⟩ = (c₁ k)⁻¹ * (c₁ k * z ⟨k, i⟩)
    exact (inv_mul_cancel_left₀ (hc₁ k) _).symm

theorem graph_exists : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 2) → IsArithVar (mCoordIdeal y') (d + 2) → ∃ Pt : Ideal (MRing (Sum.elim ι ι')), IsArithVar Pt (d + 2) ∧ imageZ inlV Pt = mCoordIdeal y ∧ imageZ inrV Pt = mCoordIdeal y' ∧ ∀ z ∈ mcPts (mCoordIdeal y'), ∀ w ∈ mcPts (mCoordIdeal y), CovMap.IsImg Cv z w → ∃ zt ∈ mcPts Pt, (∀ p, zt (inlV p) = w p) ∧ ∀ q, zt (inrV q) = z q := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M K' _ ι' _ Φ' _ y' M' Cv d hy hy'
  haveI : CharZero Φ' := charZero_of_injective_algebraMap (algebraMap M'.Ω Φ').injective
  have hid := GlobalTheory.T.flag_cover_transfer_ideal_eq K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv
  obtain ⟨c', hc'⟩ := GroundTheory.Heights₂.Heights.HilbertSamuel.CoordArithOfFnField.nonzero_of_relevant y' hy'.2.1.2.2
  obtain ⟨c, hc⟩ := GroundTheory.Heights₂.Heights.HilbertSamuel.CoordArithOfFnField.nonzero_of_relevant (transPt Cv)
    (by rw [hid]; exact hy.2.1.2.2)
  have hnz : ∀ kk : K ⊕ K', ∃ i : Sum.elim ι ι' kk, pairV (transPt Cv) y' ⟨kk, i⟩ ≠ 0 := by
    rintro (k | k)
    · exact ⟨c k, hc k⟩
    · exact ⟨c' k, hc' k⟩
  obtain ⟨k₀⟩ := hy'.1
  refine ⟨mCoordIdeal (pairV (transPt Cv) y'), ?_, ?_, imageZ_inr _ _, fun z hz w hw himg =>
    ⟨pairV w z, pts K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv z hz w hw himg, fun _ => rfl, fun _ => rfl⟩⟩
  · exact GroundTheory.Heights₂.Heights.HilbertSamuel.CoordArithOfFnField.proof K' ι' (K ⊕ K') (Sum.elim ι ι') Φ' y'
      (pairV (transPt Cv) y') (d + 2) ⟨Sum.inr k₀⟩ hnz
      (GlobalTheory.T.flag_cover_block_field_eq K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv (fun k => ⟨c' k, hc' k⟩)) hy'
  · rw [imageZ_inl, hid]

end GlobalTheory.CompanionTheory.Ar.PB.CovGraph
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagGapPullbackFirstStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_gap_pullback_first : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (e : ℕ) (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e) (pr : R.X → BM.Rb.X), IsStepHyp M BM p κ v R pr → ∀ (x y' : R.X) (z : (Σ k, ι k) → ℂ), y' ∈ R.U x → pr y' ∉ bdry BM.s → z ∈ mcPts (mCoordIdeal y) → z ∘ v = R.lift x y' → stepPh M BM p v R pr y' = stepGap M BM p z := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.StepW.Wgt.main | exact GlobalTheory.CompanionTheory.Ar.PB.StepW.Wgt.main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.StepW.Wgt.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagGapPullbackSecondStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_gap_pullback_second : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (e : ℕ) (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e) (pr : R.X → BM.Rb.X), IsStepHyp M BM p κ v R pr → ∀ x x', pr x = pr x' → (∀ k (m : ιk k), M.blk p = some (κ k) → ∃ a : ℂ, ∀ m' : ιk k, R.lift x x ⟨k, m'⟩ = a * R.lift x' x' ⟨k, m'⟩) → stepPh M BM p v R pr x = stepPh M BM p v R pr x' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.StepW.WeightProp.main | exact GlobalTheory.CompanionTheory.Ar.PB.StepW.WeightProp.main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.StepW.WeightProp.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HilbertSamuelG3OfMoriwakiStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbert_samuel_G3_of_moriwaki : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiHSStatement → ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiBigStatement → GroundTheory.Heights₂.Heights.HilbertSamuel.G3.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.selfIntersection_le_of_boundedInjection | exact GlobalTheory.CompanionTheory.Ar.Giv.selfIntersection_le_of_boundedInjection | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.selfIntersection_le_of_boundedInjection <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgePotentialSmoothOffBoundary
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.hodge_potential_smooth_off_boundary : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (Hd : HodgeData D), (∀ a, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => phMu Hd ((D.chart a).γ t)) (offBd D a)) ∧ ∀ a, ∀ t₀ : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ, ‖t₀‖ ≤ 1 / 2 → ∃ ε > (0 : ℝ), ∃ C > (0 : ℝ), ∀ t ∈ offBd D a, ‖t - t₀‖ < ε → -(C * Real.log ((D.chart a).logR t)) ≤ phMu Hd ((D.chart a).γ t) ∧ phMu Hd ((D.chart a).γ t) ≤ C ∧ ‖fderiv ℝ (fun s => phMu Hd ((D.chart a).γ s)) t‖ ≤ C * (D.chart a).logR t ^ C * Real.exp ((D.chart a).logR t / 2) := by
  first | exact @LevelTowerAlt.mu_potential_smooth_off_boundary | exact LevelTowerAlt.mu_potential_smooth_off_boundary
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.IsArithVarOfSncModelStatement
section
open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isArithVar_of_snc_model : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (x : (Σ k, J k) → Ω) (n : ℕ) (bd : Ideal (MRing J)), 1 ≤ n → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, x ⟨k, c' k⟩) → Cmp.IsSncModel x n bd → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal x) (n + 1) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.isArithVar_of_snc_model | exact GlobalTheory.CompanionTheory.Relay.isArithVar_of_snc_model | (intros; apply GlobalTheory.CompanionTheory.Relay.isArithVar_of_snc_model <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LocDensDivJacN
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.Giv.Push

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem locDens_div_jacN (A : FinHolAtlas e X) (Φ : Fin e → LocPot X) (q : X → Fin e → ℂ) (S : Set X)
    (hq : ∀ x ∉ S, ∀ j, x ∈ (A.chart j).source →
      AnalyticAt ℂ (q ∘ (A.chart j).symm) (A.chart j x) ∧
        LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) (A.chart j x) :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0)
    (hsm : ∀ x ∉ S, ∀ i k, x ∈ (A.chart k).source →
      ContDiffAt ℝ 2 ((Φ i).φ x ∘ (A.chart k).symm) (A.chart k x))
    (j : Fin A.n) {x : X} (hx : x ∈ (A.chart j).source) (hxS : x ∉ S) :
    locDens A Φ j (A.chart j x) / jacN (q ∘ (A.chart j).symm) (A.chart j x) = pushDens A Φ q x := by
  set c := chartIdx A x
  have hc : x ∈ (A.chart c).source := Classical.choose_spec (A.cover x)
  set u := A.chart j x
  have hsu : (A.chart j).symm u = x := (A.chart j).left_inv hx
  set T := A.chart c ∘ (A.chart j).symm with hTdef
  have hT : AnalyticAt ℂ T u :=
    A.holo j c u ⟨(A.chart j).map_source hx, by rw [Set.mem_preimage, hsu]; exact hc⟩
  have hTu : T u = A.chart c x := by simp only [hTdef, Function.comp_apply, hsu]
  have hQc := (hq x hxS c hc).1
  have hQj := (hq x hxS j hx).2
  have heq : q ∘ (A.chart j).symm =ᶠ[𝓝 u] (q ∘ (A.chart c).symm) ∘ T := by
    filter_upwards [((A.chart j).isOpen_inter_preimage_symm (A.chart c).open_source).mem_nhds
      (⟨(A.chart j).map_source hx, by rw [Set.mem_preimage, hsu]; exact hc⟩ :
        u ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart c).source)] with v hv
    simp only [hTdef, Function.comp_apply, (A.chart c).left_inv hv.2]
  have hder : fderiv ℂ (q ∘ (A.chart j).symm) u =
      (fderiv ℂ (q ∘ (A.chart c).symm) (A.chart c x)).comp (fderiv ℂ T u) := by
    rw [heq.fderiv_eq, fderiv_comp u (by rw [hTu]; exact hQc.differentiableAt) hT.differentiableAt,
      hTu]
  have hdet : LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) u : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) =
      LinearMap.det (fderiv ℂ (q ∘ (A.chart c).symm) (A.chart c x) :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) *
      LinearMap.det (fderiv ℂ T u : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) := by
    rw [hder]
    exact LinearMap.det_comp _ _
  have hloc : locDens A Φ j u = locDens A Φ c (A.chart c x) *
      ‖LinearMap.det (fderiv ℂ T u : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))‖ ^ 2 := by
    have := GlobalTheory.CompanionTheory.Ar.Giv.MeasOff.locDens_chart_of_contDiffAt A Φ j c
      ((A.chart j).map_source hx) (by rw [hsu]; exact hc)
      (fun i => by rw [hsu]; exact hsm x hxS i c hc)
    rw [hsu, ReciprocityTheory.AnForm.A.det_jacC, Complex.normSq_eq_norm_sq] at this
    exact this
  have hne := hQj
  rw [hdet] at hne
  have hc1 : ‖LinearMap.det (fderiv ℂ (q ∘ (A.chart c).symm) (A.chart c x) :
      (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))‖ ≠ 0 := norm_ne_zero_iff.mpr (left_ne_zero_of_mul hne)
  have hc2 : ‖LinearMap.det (fderiv ℂ T u : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (right_ne_zero_of_mul hne)
  unfold jacN pushDens
  rw [hloc, hdet, norm_mul, mul_pow, show chartIdx A x = c from rfl]
  field_simp

theorem sum_fibSum_ae (A : FinHolAtlas e X) (q : X → Fin e → ℂ) (S : Set X)
    (hN : ∀ j, volume ((q ∘ (A.chart j).symm) '' (goodT A q j ∩ (A.chart j).symm ⁻¹' S)) = 0)
    (hq : ∀ x ∉ S, ∀ j, x ∈ (A.chart j).source →
      AnalyticAt ℂ (q ∘ (A.chart j).symm) (A.chart j x) ∧
        LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) (A.chart j x) :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0)
    (hfin : ∀ y, (q ⁻¹' {y} \ S).Finite) (Pt : ChartPartition A)
    (h : Fin A.n → (Fin e → ℂ) → ℝ) (T : X → ℝ)
    (hterm : ∀ j x, x ∈ (A.chart j).source → x ∉ S →
      h j (A.chart j x) / jacN (q ∘ (A.chart j).symm) (A.chart j x) = Pt.χ j x * T x) :
    ∀ᵐ y, ∑ j, fibSum (goodT A q j) (q ∘ (A.chart j).symm) (h j) y = ∑ᶠ x ∈ q ⁻¹' {y} \ S, T x := by
  classical
  have hNall : ∀ᵐ y, ∀ j, y ∉ (q ∘ (A.chart j).symm) '' (goodT A q j ∩ (A.chart j).symm ⁻¹' S) :=
    ae_all_iff.mpr fun j => measure_eq_zero_iff_ae_notMem.mp (hN j)
  filter_upwards [hNall] with y hy
  have hterm' : ∀ j, fibSum (goodT A q j) (q ∘ (A.chart j).symm) (h j) y =
      ∑ᶠ x ∈ q ⁻¹' {y} \ S, Pt.χ j x * T x := by
    intro j
    unfold fibSum
    rw [goodT_fibre_eq A q S hq j (hy j),
      finsum_mem_image ((A.chart j).injOn.mono Set.inter_subset_left)]
    refine (finsum_mem_congr (g := fun x => Pt.χ j x * T x) rfl
      fun x hx => hterm j x hx.1 hx.2.2).trans ?_
    refine finsum_mem_inter_support_eq' _ _ _ fun x hx => ?_
    have hχ : Pt.χ j x ≠ 0 := left_ne_zero_of_mul hx
    have hxs : x ∈ (A.chart j).source := Pt.tsupport_subset j (subset_tsupport _ hχ)
    exact ⟨fun h => h.2, fun h => ⟨hxs, h⟩⟩
  simp_rw [hterm']
  rw [finsum_mem_eq_finite_toFinset_sum _ (hfin y)]
  simp_rw [finsum_mem_eq_finite_toFinset_sum _ (hfin y)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_mul, Pt.sum_eq_one x, one_mul]

end GlobalTheory.CompanionTheory.Ar.Giv.Push
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalOrbitChartStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_orbit_chart_statement_holds : GroundTheory.Heights₂.Heights.LowerBoundFree.LocalOrbitChart.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.localOrbitChart | exact GlobalTheory.CompanionTheory.Ar.Giv.localOrbitChart | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.localOrbitChart <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.PeriodDecompositionNearBoundaryStatement
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_decomposition_near_boundary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (L : ActPeriods E n a g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (m : ℕ) (b : Ψ → Fin m → (Fin n → ℂ) → Fin g → ℂ), IsCMFam σ → IsEigFrames (Metric.ball 0 1) L.B σ b → ∃ (W : Submodule (𝓞 E) Λ) (I : Submodule (𝓞 E) Λ) (per : W →+ (Fin g → ℂ)) (s : W → (Fin n → ℂ) → Fin g → ℂ) (Hb : Matrix (Fin g) (Fin g) ℂ), (∀ x, x ∈ I ↔ x ∈ W ∧ ∀ y ∈ W, L.toLogPeriods.E x y = 0) ∧ IsSaturated I ∧ Function.Injective per ∧ (∀ x : W, ContinuousAt (s x) 0 ∧ s x 0 = per x ∧ ∀ w ∈ logCover L.a_le, s x (expCover a w) = L.P w x) ∧ (∀ (ws : ℕ → Fin n → ℂ) (x : ℕ → Λ) (p : Fin g → ℂ), (∀ k, ws k ∈ logCover L.a_le) → Tendsto (fun k => expCover a (ws k)) atTop (𝓝 0) → Tendsto (fun k => L.P (ws k) (x k)) atTop (𝓝 p) → ∃ x₀ : W, p = per x₀) ∧ Submodule.span ℂ (Set.range per) = ⊤ ∧ Hb.IsHermitian ∧ (∀ x x' : W, (per x ⬝ᵥ Hb *ᵥ star (per x')).im = L.toLogPeriods.E x x') ∧ (∀ x : W, (x : Λ) ∈ I → Hb *ᵥ star (per x) = 0) ∧ ∀ ν : ℝ, PhiNormSq (L.B 0) (fun x y => y ⬝ᵥ Hb *ᵥ star x) (AddSubgroup.closure {p | ∃ x : W, (x : Λ) ∈ I ∧ p = per x}) 1 σ (fun τ i => b τ i 0) ν → 0 < ν ∧ ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ w (hw : w ∈ logCover L.a_le), ‖expCover a w‖ < δ → |(L.riem w hw).logDet (fun τ i => b τ i (expCover a w)) - Real.log ((L.riem w hw).nz σ I) - Real.log ν| < ε := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.limit_at_centre | exact GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.limit_at_centre | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.limit_at_centre <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.PieceDegreeOfIntersectionAndResolution
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField

namespace GlobalTheory.CompanionTheory.Ar.Giv

noncomputable section

def fsOfDegree {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (A : HermLine ι) : HermLine ι :=
  HermLine.ofMetrics (fun k => fsMetric (ι k)) A.a

theorem fsOfDegree_a {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (A : HermLine ι) :
    (fsOfDegree A).a = A.a := rfl

theorem isSmoothHerm_fsOfDegree {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (A : HermLine ι) :
    IsSmoothHerm (fsOfDegree A) :=
  GroundTheory.Heights₂.Heights.Inter.isSmoothHerm_ofMetrics_fs A.a

theorem isConjInvariantH_fsOfDegree {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (A : HermLine ι) :
    IsConjInvariantH (fsOfDegree A) := by
  intro z
  simp only [fsOfDegree, HermLine.ofMetrics]
  exact Finset.prod_congr rfl fun k _ => by
    rw [GroundTheory.Heights₂.Heights.FubiniStudyConjugationInvariant.fsMetric_conj (fun i => z ⟨k, i⟩)]

theorem pieceDegree : ArithIntersectionSystemStatement → ResExistsStatement → PtsIntegrableStatement →
    GroundTheory.Heights₂.Heights.HilbertSamuel.PieceDegree.Statement := by
  intro hAr hRes hPts K _ ι _ Ω _ F _ _ _ y D L sg sg' har hbir hsm hone
  have hsm₀ : ∀ j, IsSmoothHerm (fsOfDegree (L j)) := fun j => isSmoothHerm_fsOfDegree _
  have hcj₀ : ∀ j, IsConjInvariantH (fsOfDegree (L j)) := fun j => isConjInvariantH_fsOfDegree _
  have hind : ∀ s : F →+* ℂ,
      ptsIntegral (mCoordIdeal y) (pot L) ({z | LiesOver y s z}.indicator fun _ => (1 : ℝ)) =
        ptsIntegral (mCoordIdeal y) (pot fun j => fsOfDegree (L j))
          ({z | LiesOver y s z}.indicator fun _ => (1 : ℝ)) := fun s =>
    GlobalTheory.T.points_integral_independent_of_metric hAr hPts K ι Ω F y D L (fun j => fsOfDegree (L j)) s har hsm hsm₀
      (fun j => (fsOfDegree_a (L j)).symm) hone
  rw [hind sg, hind sg']
  exact GlobalTheory.T.unit_log_orthogonal_weight_constant F
    (fun s => ptsIntegral (mCoordIdeal y) (pot fun j => fsOfDegree (L j))
      ({z | LiesOver y s z}.indicator fun _ => (1 : ℝ)))
    (fun s => GlobalTheory.T.points_integral_unique_embedding hRes K ι Ω F y D _ s har hsm₀ hcj₀ hone)
    (fun θ => GlobalTheory.T.sum_over_embeddings_unit_invariance hAr hPts K ι Ω F y D _ θ har hbir hsm₀ hone) sg sg'

end

end GlobalTheory.CompanionTheory.Ar.Giv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ProjectionFormulaOfArithSystem
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace GlobalTheory.CompanionTheory.Ar.Giv.ProjF

open GroundTheory.Heights₂.Heights

theorem pfIntZero : Inter.PFIntZero.Statement :=
  Inter.PFIntZero.proof (Inter.pointFormRank_holds.proof Inter.RatioAlgDep.proof)

theorem pfVert : Inter.PFVert.Statement :=
  Inter.PFVert.proof (by intros; exact geoNumStatement _) (by intros; exact Targets.ExistsUnique.full _ _)
    Targets.contractMixedField

theorem contractMixed : ContractMixedStatement :=
  Targets.ContractMixed.of_found imageArith Targets.Contract.pulledBackForms_topDensity_vanish
    (Inter.ProjectivePointVertical.proof (by intros; exact geoNumStatement _) (by intros; exact Targets.ExistsUnique.full _ _)
      (by intros; exact Targets.ProjContract.full _ _ _ _ _))
    pfIntZero pfVert

theorem pfStep : Inter.PFStep.Statement :=
  Inter.PFStep.proof (Inter.PFSecRed.proof (by intros; exact Targets.Multilin.full _ _) GlobalTheory.CompanionTheory.Ar.Giv.fibreDim) pfVert pfIntZero
    Inter.PFHoriz.proof (Inter.PFFibreSum.proof GlobalTheory.CompanionTheory.Ar.Giv.fibreDim Inter.PFFibreBij.proof Inter.PFFibreMult.proof)
    imageArith contractMixed

theorem projFormula : ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → PFStatement := fun h =>
  Inter.PushforwardProjLineFlag.proof (GlobalTheory.T.generic_degree_of_arith_system h) pfStep

end GlobalTheory.CompanionTheory.Ar.Giv.ProjF
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SncChartParametersAtConePointStatement
section
open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.snc_chart_parameters_at_cone_point : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (e : ℕ) (J : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing ι)), ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (ReciprocityTheory.ChartRestriction.G.Geo.mCoordIdeal y) (e + 1) → IsSncModel y e J → ∀ (p : (k : K) → ι k) (z : (Σ k, ι k) → ℂ), z ∈ conePts (ReciprocityTheory.ChartRestriction.G.Geo.pC (ReciprocityTheory.ChartRestriction.G.Geo.mCoordIdeal y)) → (∀ k, z ⟨k, p k⟩ ≠ 0) → ∃ (r : Fin e → MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ) (Jf : Finset (Fin e)), ((∀ h ∈ (SncRes.ideal (ReciprocityTheory.ChartRestriction.G.Geo.pC (ReciprocityTheory.ChartRestriction.G.Geo.mCoordIdeal y)) p), eval (renPt (affCoord p z)) h = 0) ∧ IsRegularLocalRing (locRing (SncRes.ideal (ReciprocityTheory.ChartRestriction.G.Geo.pC (ReciprocityTheory.ChartRestriction.G.Geo.mCoordIdeal y)) p) (renPt (affCoord p z))) ∧ ringKrullDim (locRing (SncRes.ideal (ReciprocityTheory.ChartRestriction.G.Geo.pC (ReciprocityTheory.ChartRestriction.G.Geo.mCoordIdeal y)) p) (renPt (affCoord p z))) = e ∧ Ideal.span (Set.range fun l => algebraMap _ (locRing (SncRes.ideal (ReciprocityTheory.ChartRestriction.G.Geo.pC (ReciprocityTheory.ChartRestriction.G.Geo.mCoordIdeal y)) p) (renPt (affCoord p z))) (r l)) = Ideal.map (algebraMap _ (locRing (SncRes.ideal (ReciprocityTheory.ChartRestriction.G.Geo.pC (ReciprocityTheory.ChartRestriction.G.Geo.mCoordIdeal y)) p) (renPt (affCoord p z)))) (ptIdeal (renPt (affCoord p z))) ∧ (∀ 𝔮 : Ideal (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ), 𝔮.IsPrime → (SncRes.ideal (ReciprocityTheory.ChartRestriction.G.Geo.pC (ReciprocityTheory.ChartRestriction.G.Geo.mCoordIdeal y)) p) ≤ 𝔮 → 𝔮 ≤ ptIdeal (renPt (affCoord p z)) → ((SncRes.ideal (ReciprocityTheory.ChartRestriction.G.Geo.pC (ReciprocityTheory.ChartRestriction.G.Geo.mCoordIdeal y) ⊔ (ReciprocityTheory.ChartRestriction.G.Geo.pC J)) p) ≤ 𝔮 ↔ ∃ i ∈ Jf, r i ∈ 𝔮))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par.exists_params | exact GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par.exists_params | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par.exists_params <;> assumption)
end

