import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
import Formalism.LocalToGlobal.GlobalTheory.GL5.Statement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0176
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0247
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0001
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0002
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0248
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HighestWeightEventuallyZero
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.FirstSlotSliceSlotMixedCasimirZero
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0004
import Formalism.RealPlaceAnalysis.FinalF
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0222
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0251
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0118
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0126
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0249
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MomAllP
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0250

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaussianPushforwardDensity
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.GaussMean.ProdDensity

open GlobalTheory.GaussMean.Density Filter Topology

theorem integral_lt_eq {n : ℕ} (ε : Fin n → Bool) {a : ℝ} (ha : a ≠ 0) :
    ∫ y in {y : Fin n → ℂ | qEps ε y < a}, gauss y = cdf ε a := by
  apply le_antisymm
  · exact setIntegral_mono_set (integrable_gauss n).integrableOn
      (Filter.Eventually.of_forall fun y => (gauss_pos y).le)
      (HasSubset.Subset.eventuallyLE fun y (hy : qEps ε y < a) => hy.le)
  · have hc : Tendsto (cdf ε) (𝓝[<] a) (𝓝 (cdf ε a)) :=
      (differentiableAt_cdf ε ha).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    refine le_of_tendsto hc ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : t < a)
    exact setIntegral_mono_set (integrable_gauss n).integrableOn
      (Filter.Eventually.of_forall fun y => (gauss_pos y).le)
      (HasSubset.Subset.eventuallyLE fun y (hy : qEps ε y ≤ t) => lt_of_le_of_lt hy ht)

theorem integral_Icc_eq {n : ℕ} (ε : Fin n → Bool) {a c : ℝ} (ha : a ≠ 0) (hac : a ≤ c) :
    ∫ y in qEps ε ⁻¹' Set.Icc a c, gauss y = cdf ε c - cdf ε a := by
  have hm : MeasurableSet {y : Fin n → ℂ | qEps ε y < a} :=
    measurableSet_lt (continuous_qEps ε).measurable measurable_const
  have h := integral_diff hm ((integrable_gauss n).integrableOn (s := {y | qEps ε y ≤ c}))
    (fun y (hy : qEps ε y < a) => show qEps ε y ≤ c by linarith)
  rw [integral_lt_eq ε ha] at h
  rw [cdf, ← h]
  congr 2
  ext y
  simp [and_comm]

theorem integral_box {ι : Type} [Fintype ι] {n : ℕ} (ε : ι → Fin n → Bool) (a c : ι → ℝ) (ha : ∀ v, a v ≠ 0)
    (hac : a ≤ c) :
    ∫ y in (fun (y : ι → Fin n → ℂ) (v : ι) => qEps (ε v) (y v)) ⁻¹' Set.Icc a c, ∏ v, gauss (y v) =
      ∏ v, (cdf (ε v) (c v) - cdf (ε v) (a v)) := by
  have hm : MeasurableSet ((fun (y : ι → Fin n → ℂ) (v : ι) => qEps (ε v) (y v)) ⁻¹' Set.Icc a c) :=
    measurableSet_Icc.preimage
      (continuous_pi fun v => (continuous_qEps (ε v)).comp (continuous_apply v)).measurable
  rw [← integral_indicator hm, ← Finset.prod_congr rfl fun v _ => integral_Icc_eq (ε v) (ha v) (hac v),
    ← Finset.prod_congr rfl fun v _ => integral_indicator
      (measurableSet_Icc.preimage (continuous_qEps (ε v)).measurable),
    ← integral_fintype_prod_volume_eq_prod]
  congr 1
  funext y
  by_cases hy : y ∈ (fun (y : ι → Fin n → ℂ) (v : ι) => qEps (ε v) (y v)) ⁻¹' Set.Icc a c
  · rw [Set.indicator_of_mem hy]
    exact Finset.prod_congr rfl fun v _ => (Set.indicator_of_mem (s := qEps (ε v) ⁻¹' Set.Icc (a v) (c v))
      ⟨hy.1 v, hy.2 v⟩ _).symm
  · rw [Set.indicator_of_notMem hy]
    obtain ⟨v, hv⟩ : ∃ v, y v ∉ qEps (ε v) ⁻¹' Set.Icc (a v) (c v) := by
      by_contra! h
      exact hy ⟨fun v => (h v).1, fun v => (h v).2⟩
    exact (Finset.prod_eq_zero (Finset.mem_univ v) (Set.indicator_of_notMem hv _)).symm

theorem tendsto_mean_cube {ι : Type} [Fintype ι] {G : (ι → ℝ) → ℂ} (hG : Continuous G) (b : ι → ℝ) :
    Tendsto (fun r : ℝ => (r ^ Fintype.card ι)⁻¹ • ∫ x in Set.Icc b (fun v => b v + r), G x) (𝓝[>] 0)
      (𝓝 (G b)) := by
  rw [Metric.tendsto_nhds]
  intro e he
  obtain ⟨d, hd, hδ⟩ := Metric.continuousAt_iff.1 (hG.continuousAt (x := b)) (e / 2) (half_pos he)
  filter_upwards [Ioo_mem_nhdsGT hd] with r hr
  have hr0 := hr.1
  have hk : 0 < r ^ Fintype.card ι := pow_pos hr0 _
  have hvol : volume.real (Set.Icc b (fun v => b v + r)) = r ^ Fintype.card ι := by
    rw [Measure.real, Real.volume_Icc_pi_toReal (fun v => by simp [hr0.le])]
    simp
  have hfin : volume (Set.Icc b (fun v => b v + r)) < ⊤ := isCompact_Icc.measure_lt_top
  have h1 : ∫ x in Set.Icc b (fun v => b v + r), (G x - G b) =
      (∫ x in Set.Icc b (fun v => b v + r), G x) - (r ^ Fintype.card ι) • G b := by
    rw [integral_sub hG.continuousOn.integrableOn_Icc continuousOn_const.integrableOn_Icc,
      setIntegral_const, hvol]
  have h2 : ‖∫ x in Set.Icc b (fun v => b v + r), (G x - G b)‖ ≤ e / 2 * r ^ Fintype.card ι := by
    rw [← hvol]
    refine norm_setIntegral_le_of_norm_le_const hfin fun x hx => ?_
    rw [← dist_eq_norm]
    refine (hδ (lt_of_le_of_lt ?_ hr.2)).le
    rw [dist_pi_le_iff hr0.le]
    intro v
    have h3 := hx.1 v
    have h4 := hx.2 v
    rw [Real.dist_eq, abs_le]
    constructor <;> linarith
  have h3 : (r ^ Fintype.card ι)⁻¹ • (∫ x in Set.Icc b (fun v => b v + r), G x) - G b =
      (r ^ Fintype.card ι)⁻¹ • ∫ x in Set.Icc b (fun v => b v + r), (G x - G b) := by
    rw [h1, smul_sub, smul_smul, inv_mul_cancel₀ hk.ne', one_smul]
  rw [dist_eq_norm, h3, norm_smul, Real.norm_of_nonneg (inv_pos.2 hk).le, inv_mul_lt_iff₀ hk]
  nlinarith

theorem density_eq_prod (ι : Type) [Fintype ι] (n : ℕ) (ε : ι → Fin n → Bool) (G : (ι → ℝ) → ℂ)
    (hG : Continuous G)
    (h : ∀ S : Set (ι → ℝ), IsCompact S →
      ∫ y in (fun (y : ι → Fin n → ℂ) (v : ι) => qEps (ε v) (y v)) ⁻¹' S, ((∏ v, gauss (y v) : ℝ) : ℂ) =
        ∫ b in S, G b)
    (b : ι → ℝ) (hb : ∀ v, b v ≠ 0) : G b = ((∏ v, gaussDens (ε v) (b v) : ℝ) : ℂ) := by
  have h1 : Tendsto (fun r : ℝ => ∏ v, r⁻¹ • (cdf (ε v) (b v + r) - cdf (ε v) (b v))) (𝓝[>] 0)
      (𝓝 (∏ v, gaussDens (ε v) (b v))) :=
    tendsto_finset_prod _ fun v _ =>
      (differentiableAt_cdf (ε v) (hb v)).hasDerivAt.tendsto_slope_zero_right
  have h2 := (Complex.continuous_ofReal.tendsto _).comp h1
  refine tendsto_nhds_unique (tendsto_mean_cube hG b) (h2.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  rw [← h _ isCompact_Icc, integral_complex_ofReal, integral_box ε b _ hb (fun v => by simp [hr.le])]
  simp [Finset.prod_mul_distrib]

end GlobalTheory.GaussMean.ProdDensity
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetAmplitudeBoundLocalStatement
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianDoubleCoset_amplitude_bound_local : ∀ (C : ℝ), 39 ≤ C → ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), 4 * r + 7 ≤ k → Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → LocNG.NGAt k P C := by
  first | exact @GlobalTheory.HL.AbstractBound.ngAt | exact GlobalTheory.HL.AbstractBound.ngAt | (intros; apply GlobalTheory.HL.AbstractBound.ngAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFrameWitnessIntegralChangeStatement
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_frame_witness_integral_change : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ), ∀ (k : ℕ) (P : FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (theta M) → ∀ (d : Datum P) (t : Term V M r), IsTermOver P d t → ∀ (A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (g g' : Fin (r + 1) → V), Uni A → Uni A' → (∀ a b, A a b ∈ M.L.O ∧ A' a b ∈ M.L.O ∧ A a b - A' a b ∈ Submodule.span M.L.O {algebraMap F E (theta M)}) → Chg t.f A g → Chg t.f' A' g' → IsTermOver P d ⟨t.abelian₂, g, g', t.T, t.T'⟩ := by
  first | exact @GlobalTheory.LocOver.WitChange.witness_change | exact GlobalTheory.LocOver.WitChange.witness_change | (intros; apply GlobalTheory.LocOver.WitChange.witness_change <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianOrbitUniqueLatticeIntegralFramesStatement
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_orbit_unique_lattice_integral_frames : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), 4 * r + 7 ≤ k → Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → P.PrimeTo → ∀ (A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) E), (∀ a b, b < a → A a b = 0 ∧ A' a b = 0) → (∀ a, A a a = 1 ∧ A' a a = 1) → (∀ a b, A a b ∈ M.L.O ∧ A' a b ∈ M.L.O) → ∀ (f f' : Fin (r + 1) → V), (∀ j, f j = ∑ i, A i j • P.A.f i) → (∀ j, f' j = ∑ i, A' i j • P.B.f i) → ∀ d0 : LocNG.Datum P, (∃ t, LocNG.IsTermOver P d0 t) → ∀ d : LocNG.Datum P, (LocNG.Datum.Rel d0 d → ∃! Λ : Submodule M.L.O V, LocNG.IsTermOver P d (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r) ∧ ¬ LocNG.BBne (H := H) (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r)) ∧ ((∃ t, LocNG.IsTermOver P d t) → LocNG.Datum.Rel d0 d) := by
  first | exact @GlobalTheory.HL.GoodFrames.main | exact GlobalTheory.HL.GoodFrames.main | (intros; apply GlobalTheory.HL.GoodFrames.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HighestWeightEventuallyZeroStatement
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.highest_weight_eventually_zero : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ V) (lam : Fin n → ℝ) (u : V), IsURepOn (UJset ε) σ → IsDer ε σ V E → KHighest ε E (LamOf ε lam) u → FiniteDimensional ℂ (kSpan ε E u) → ∀ G ∈ Vminus ε E (LamOf ε lam) u, ∀ y : H, ∀ᶠ g : UJ ε in nhds 1, ∑ a, ∑ b, Eab ε a b (fun z => ∫ k : KG ε, Phi lam (((toMK k)⁻¹ * z * toMK k).map star) * (⟪y, σ (toMK k) (u : H)⟫_ℂ * ⟪σ (toMK k) (u : H), (at1 G a b : V)⟫_ℂ) ∂(muK ε)) (umat g) = 0 := by
  first | exact @GlobalTheory.Jet.SchmidIntegral.eab_integral_eq_zero | exact GlobalTheory.Jet.SchmidIntegral.eab_integral_eq_zero | (intros; apply GlobalTheory.Jet.SchmidIntegral.eab_integral_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InnerBesselFunctionalEqIntegralSubgroup
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf

theorem afun_inner_eq_integral : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)), Std σ w a μG d → Side z π μS → ∀ u ∈ DD σ w, ∀ u₁ ∈ DD σ w, ∀ v ∈ DD σ w, ∀ ξ : Wp, ∀ x : Mt k r, Matrix.of x ∈ GG k r → ⟪Afun (psiGen k r z c) π μS σ u₁ v ξ (Matrix.of x), Afun (psiGen k r z c) π μS σ u v ξ (Matrix.of x)⟫_ℂ = ∫ s, coef σ u v (Matrix.of (lmulM (Matrix.of s) x)) * ⟪Afun (psiGen k r z c) π μS σ u₁ v ξ (Matrix.of (lmulM (Matrix.of s) x)), ξ⟫_ℂ ∂μS := by
  intro k r H _ _ _ Wp _ _ _ _ σ w a μG d z c π μS hStd hSide u hu u₁ hu₁ v hv ξ x hx
  have hσ : IsURepOn (GG k r) σ := hStd.2.1
  have hDec : Decay σ (DD σ w) a := hStd.2.2.2.2.2.2.2.1
  have hzb : inWb k r z := hSide.1
  have hTz : 0 < Tz k r z := hSide.2.1
  have hπ : IsURepOn (UWset k r z) π := hSide.2.2.1
  have hμS : IsHaarOn (Sset k r z) μS := hSide.2.2.2.1
  have hstab := (GlobalTheory.T.smooth_vectors_dense_invariant k r σ w hσ).1
  have hSsub : Sset k r z ⊆ GG k r := (GlobalTheory.T.bessel_subgroups_closed_unitaryW_compact k r z hzb hTz).2.2.2.1.1
  have hD1 := GlobalTheory.T.besselForm_converges_equivariant_hermitian k r σ w a μG d z c π μS hStd hSide (DD σ w) hstab hDec
  have hxu : σ (Matrix.of x) u ∈ DD σ w := hstab _ hx u hu
  have hxu₁ : σ (Matrix.of x) u₁ ∈ DD σ w := hstab _ hx u₁ hu₁
  obtain ⟨hint, -, -, -⟩ := hD1 _ hxu v hv
  obtain ⟨-, heq₁, -, -⟩ := hD1 _ hxu₁ v hv
  have hPi := GlobalTheory.T.besselSubgroupRepTwisted_isUnitaryRep k r z c π hzb hTz hπ
  have hae : ∀ᵐ s ∂μS, Matrix.of s ∈ Sset k r z := by rw [ae_iff]; exact hμS.2.2.1
  show ⟪Afun (psiGen k r z c) π μS σ u₁ v ξ (Matrix.of x),
      be (psiGen k r z c) π μS σ (σ (Matrix.of x) u) v ξ⟫_ℂ = _
  rw [be, ContinuousLinearMap.integral_apply hint, ← integral_inner (hint.apply_continuousLinearMap ξ)]
  refine integral_congr_ae ?_
  filter_upwards [hae] with s hs
  have hsG : Matrix.of s ∈ GG k r := hSsub hs
  have hmul : σ (Matrix.of s * Matrix.of x) = (σ (Matrix.of s)).comp (σ (Matrix.of x)) :=
    hσ.1.2 _ hsG _ hx
  have hcoef : coef σ (σ (Matrix.of x) u) v (Matrix.of s) =
      coef σ u v (Matrix.of (lmulM (Matrix.of s) x)) := by
    show ⟪v, σ (Matrix.of s) (σ (Matrix.of x) u)⟫_ℂ = ⟪v, σ (Matrix.of s * Matrix.of x) u⟫_ℂ
    rw [hmul]; rfl
  have hadj := ((hPi.2.2.1) _ hs).2
  rw [ContinuousLinearMap.smul_apply, inner_smul_right, hcoef]
  congr 1
  rw [← hadj, ContinuousLinearMap.adjoint_inner_right]
  congr 1
  show PiS (psiGen k r z c) π (Matrix.of s) (be (psiGen k r z c) π μS σ (σ (Matrix.of x) u₁) v ξ) =
    be (psiGen k r z c) π μS σ (σ (Matrix.of s * Matrix.of x) u₁) v ξ
  rw [hmul, ContinuousLinearMap.comp_apply, (heq₁ _ hs).1]
  rfl

end GlobalTheory.SgInf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrableMatrixCoefficientQuotientMeasureStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_matrixCoefficient_quotientMeasure : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)), Std σ w a μG d → Side z π μS → ∀ ν : Measure (Mt k r), IsQuotMeas μG μS ν → ∀ u ∈ DD σ w, ∀ v ∈ DD σ w, ∀ ξ : Wp, Integrable (fun x : Mt k r => Afun (psiGen k r z c) π μS σ u v ξ (Matrix.of x)) ν := by
  first | exact @GlobalTheory.SgInf.integrable_Afun_quotMeas | exact GlobalTheory.SgInf.integrable_Afun_quotMeas | (intros; apply GlobalTheory.SgInf.integrable_Afun_quotMeas <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFdegFdegOfOfIsDS
section
open MeasureTheory Formalism.MainNotions.S

namespace GlobalTheory.LowestVectorDegree

theorem fdegOf_eq {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {d : ℝ} (h : IsFdeg (Formalism.REAL.muG ε) σ d) {w : H} (hw : w ≠ 0) :
    fdegOf (Formalism.REAL.muG ε) σ w = d := by
  obtain ⟨hd, h⟩ := h
  have hwpos : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hw
  have hsq : ∀ z : ℂ, z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    intro z
    rw [RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have h1 := (h w w w w).2
  simp only [hsq] at h1
  rw [integral_complex_ofReal, inner_self_eq_norm_sq_to_K] at h1
  have h2 : ((∫ g, ‖coefOn σ w w g‖ ^ 2 ∂(Formalism.REAL.muG ε) : ℝ) : ℂ) = ((‖w‖ ^ 4 / d : ℝ) : ℂ) := by
    rw [h1]
    push_cast
    rw [← pow_add]
    rfl
  have h3 : ∫ g, ‖coefOn σ w w g‖ ^ 2 ∂(Formalism.REAL.muG ε) = ‖w‖ ^ 4 / d := by exact_mod_cast h2
  unfold fdegOf
  rw [h3]
  have h4 : ‖w‖ ^ 4 ≠ 0 := by positivity
  field_simp

theorem isFdeg_fdegOf_of_isDS {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsDS ε lam σ) {w : H}
    (hw : ‖w‖ = 1) : IsFdeg (Formalism.REAL.muG ε) σ (fdegOf (Formalism.REAL.muG ε) σ w) := by
  have hw0 : w ≠ 0 := by
    rintro rfl
    simp at hw
  obtain ⟨d, hd⟩ := GlobalTheory.Mem.Vol.exists_isFdeg_smul_of_isDS n ε lam H σ hσ 1 one_pos
  have hd' : IsFdeg (Formalism.REAL.muG ε) σ d := by simpa using hd
  rw [fdegOf_eq hd' hw0]
  exact hd'

end GlobalTheory.LowestVectorDegree
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LastMajorantLengthSqGeAndPosStatement
section
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.last_majorant_length_sq_ge_and_pos : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), inWb k r z → 0 < Tz k r z → ∀ g ∈ GG k r, Tz k r z ≤ lenA k r z g (Fin.last r) ^ 2 ∧ ∀ a, 0 < lenA k r z g a ∧ lenA k r z g a = lA k r z g a := by
  first | exact @GlobalTheory.LastLen.last_len | exact GlobalTheory.LastLen.last_len | (intros; apply GlobalTheory.LastLen.last_len <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeSeenInDefiniteSpaceDetRankIndexStatement
section
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeSeenInDefiniteSpace_det_rank_index : ∀ (D : D7) (T : D.host.E) (F : Fg D T) (H : Submodule D.host.E (hS D).V), WHyp D F (Wsp D) → H ≤ orth (hS D) (Xplus F) → H ⊓ Xsp F = ⊥ → ∀ N N' : LatV D, N ≤ toO (hS D) H → N' ≤ toO (hS D) H → detW D (seen D F N) = latDet (hS D) N ∧ rkW D (seen D F N) = finrank D.host.E (spanE (hS D) N) ∧ idxW D (seen D F N) (seen D F N') = idx (hS D) N N' := by
  first | exact @GlobalTheory.LoopC.SeenIso.main | exact GlobalTheory.LoopC.SeenIso.main | (intros; apply GlobalTheory.LoopC.SeenIso.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LineLatticeClassMeanSumNonzeroUnfoldStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineLatticeClassMean_sum_nonzero_unfold : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ j : ℕ, 2 ≤ j → ∀ (w : ℝ → ENNReal) (Φ : VecInf E j → ENNReal), Measurable w → Measurable Φ → latMean E j (fun L => w (covAt E j L) * ∑' x : {x : VecInf E j // x ∈ L ∧ x ≠ 0}, Φ x.1) = glVol E (j - 1) * ENNReal.ofReal (Formalism.HermitianLatticesTheory.vInv E ^ (Formalism.HermitianLatticesTheory.fDeg E * (2 * j - 1)) * zetaE E j) * (∫⁻ x, Φ x) * ∫⁻ t in Set.Ioi (0 : ℝ), w t / ENNReal.ofReal (t ^ 2) := by
  first | exact @GlobalTheory.FlagBase.SiegelUnfold.latMean_sum_ne_zero | exact GlobalTheory.FlagBase.SiegelUnfold.latMean_sum_ne_zero | (intros; apply GlobalTheory.FlagBase.SiegelUnfold.latMean_sum_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralProdPowLeOfMomentsMassLeOneStatement
section
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_prod_pow_le_of_moments_mass_le_one : ∀ (Ω : Type) [MeasurableSpace Ω] (ν : Measure Ω) (r q : ℕ) (ρ : Fin r → Ω → ℝ) (Ph : Ω → ℝ) (Rr : ℝ) (s : Finset (Fin r)), (∀ a, AEMeasurable (ρ a) ν) → (∀ a, ∀ᵐ x ∂ν, 0 ≤ ρ a x) → AEMeasurable Ph ν → (∀ x, 0 ≤ Ph x) → ∫⁻ x, ENNReal.ofReal (Ph x) ∂ν ≤ 1 → 1 ≤ Rr → (∀ a, ∫⁻ x, ENNReal.ofReal (ρ a x ^ (2 * (r * q)) * Ph x) ∂ν ≤ ENNReal.ofReal (Rr ^ (2 * (r * q)))) → ∫⁻ x, ENNReal.ofReal ((∏ a ∈ s, ρ a x) ^ (2 * q) * Ph x) ∂ν ≤ ENNReal.ofReal (Rr ^ (2 * (r * q))) := by
  first | exact @GlobalTheory.lintegral_prod_pow_le_of_moments | exact GlobalTheory.lintegral_prod_pow_le_of_moments | (intros; apply GlobalTheory.lintegral_prod_pow_le_of_moments <;> assumption)
end

