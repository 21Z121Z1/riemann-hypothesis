import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0841
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0834
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0801
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0113
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0788
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0539
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0620
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0084
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0076
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0015
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0054
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0025
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0028
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0044
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0024
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0026
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0032
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0751
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0815
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0795
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0824
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0836
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0429
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0042
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0483
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0471
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0498
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0477
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0460
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0814
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0470
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0481
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0463
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0821
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0831
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SphericalBoundOfHeights
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KvFintype
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0003
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0773
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0774
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0785
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0776
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0775
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0833
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0508
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0842
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1870
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0771

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScalarExtensionFibreMeasureStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scalar_extension_fibre_measure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (t : F), t ≠ 0 → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b) (hT' : ∀ a b, σ (blockOne (algebraMap F E t) T b a) = blockOne (algebraMap F E t) T a b), ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R), lam.IsAddHaarMeasure → ∀ m m₁ m', IsGramFibFree R σ (blockOne (algebraMap F E t) J) (n + 1) (coordW R b lam (n + 1) (M + 1)) (coordHerm R σ b lam (n + 1)) m → IsGramFib R σ (blockOne (algebraMap F E t) J) 1 (coordW R b lam 1 (M + 1)) (coordHerm R σ b lam 1) m₁ → IsGramFibFree R σ J n (coordW R b lam n M) (coordHerm R σ b lam n) m' → ∀ c : ℝ≥0, (coordK R b lam).map (fun y => inclR R (algebraMap F E t) * y) = c • coordK R b lam → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → ∃ Ψ : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable Ψ ∧ (∀ h : HA R σ (blockOne (algebraMap F E t) J), Ψ (actW R σ _ h (fun _ => Fin.cons 1 (fun _ => 0))) = ∫⁻ X, φ (actW R σ _ h (consTup X)) ∂(m' (hermOf R σ T hT))) ∧ ∫⁻ X, φ X ∂(m (hermOf R σ _ hT')) = (c : ℝ≥0∞) ^ n * ∫⁻ y, Ψ y ∂(m₁ (hermScal R σ (algebraMap F R t))) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.FreeStage.fibre_block_stages_free | exact GlobalTheory.CompanionTheory.WeilSiegel.FreeStage.fibre_block_stages_free | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.FreeStage.fibre_block_stages_free <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilFreeZeroRankOneOfThreeLe
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.OneZero

theorem one_vector_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (h₀ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b), (framesE σ J (0 : Matrix (Fin 1) (Fin 1) E)).Nonempty → SWFree σ J (0 : Matrix (Fin 1) (Fin 1) E) h₀ := by
  intro F E _ _ _ _ _ σ hcm M J hJ hM h₀ hne d b li lam hli hlam μ 𝓕 hμ h𝓕 mi m hmi hm
  classical
  obtain ⟨t0, t1, t2⟩ := GlobalTheory.T.theta_measure_locally_finite_invariant F E σ hcm M J hJ hM μ 𝓕 hμ h𝓕
  set I := thetaMeas σ J μ 𝓕 (framesE σ J (0 : Matrix (Fin 1) (Fin 1) E)) with hI
  set m0 : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin 1 → Fin M → Fv F v ⊗[F] E) :=
    fun v => m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) with hm0
  set mi0 := mi (hermOf (Ainf F) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) with hmi0
  obtain ⟨sfi, sfv, hnz⟩ := GlobalTheory.T.global_volume_rank_one_product F E σ hcm M J hJ hM h₀ d b li lam hli hlam mi hmi m hm
  obtain ⟨nzi, nzv⟩ := hnz hne
  obtain ⟨hfin, hsum⟩ := GlobalTheory.T.finite_volume_rank_one_product F E σ hcm M J hJ hM h₀ d b lam hlam m hm
  choose cS hcS using GlobalTheory.T.global_volume_rank_one_isotropic F E σ hcm M J hJ hM h₀ d b li lam hli hlam mi hmi m hm I t0 t1 t2
  obtain ⟨A, hAm, hA0, hAt⟩ := @GlobalTheory.CompanionTheory.SW.Fact.exists_test_set _ _ mi0 sfi nzi
  choose B hBm hB0 hBt using fun v => @GlobalTheory.CompanionTheory.SW.Fact.exists_test_set _ _ (m0 v) (sfv v) (nzv v)
  have hLv : ∀ v, IsLocR (Fv F v) := GlobalTheory.T.completion_is_local_ring F
  have hstep : ∀ S : Finset (HeightOneSpectrum (𝓞 F)), ∅ ⊆ S → ∀ v, v ∉ S →
      (cS S : ℝ) = cS (insert v S) * (m0 v (latV b v)).toReal := by
    intro S _ v hv
    have hlatm : MeasurableSet (latV b v : Set (Fin 1 → Fin M → Fv F v ⊗[F] E)) := by
      haveI := GlobalTheory.CompanionTheory.SW.Fact.borel_tup σ hcm (Fv F v) (hLv v) 1 M
      exact ((GlobalTheory.T.adelic_tuple_projections F E σ hcm d b 1 M).2.2.2.1 v).2.measurableSet
    let φ0 : ∀ w : HeightOneSpectrum (𝓞 F), (Fin 1 → Fin M → Fv F w ⊗[F] E) → ℝ≥0∞ :=
      fun w => (B w).indicator 1
    let φ1 := Function.update φ0 v ((latV b v).indicator 1)
    have hφ0 : ∀ w, Measurable (φ0 w) := fun w => measurable_one.indicator (hBm w)
    have hφ1 : ∀ w, Measurable (φ1 w) := by
      intro w
      by_cases hw : w = v
      · subst hw
        simpa [φ1] using measurable_one.indicator hlatm
      · simpa [φ1, Function.update_of_ne hw] using hφ0 w
    have hAφ : Measurable (A.indicator (1 : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞)) := measurable_one.indicator hAm
    have e1 : ∫⁻ X, pureL b S (A.indicator 1) φ0 X ∂I = (cS S : ℝ≥0∞) * ((∫⁻ X, A.indicator (1 : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞) X ∂mi0) * ∏ w ∈ S, ∫⁻ X, φ0 w X ∂(m0 w)) :=
      hcS S _ φ0 hAφ hφ0
    have e2 : ∫⁻ X, pureL b (insert v S) (A.indicator 1) φ1 X ∂I = (cS (insert v S) : ℝ≥0∞) * ((∫⁻ X, A.indicator (1 : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞) X ∂mi0) * ∏ w ∈ insert v S, ∫⁻ X, φ1 w X ∂(m0 w)) :=
      hcS (insert v S) _ φ1 hAφ hφ1
    have e3 : ∫⁻ X, pureL b (insert v S) (A.indicator 1) φ1 X ∂I =
        ∫⁻ X, pureL b S (A.indicator 1) φ0 X ∂I :=
      lintegral_congr fun X => GlobalTheory.CompanionTheory.SW.Fact.pureL_insert b S v hv _ φ0 X
    rw [e3, e1, Finset.prod_insert hv] at e2
    have hp : ∏ w ∈ S, ∫⁻ X, φ1 w X ∂(m0 w) = ∏ w ∈ S, ∫⁻ X, φ0 w X ∂(m0 w) :=
      Finset.prod_congr rfl fun w hw => by
        have hne : w ≠ v := fun h => hv (h ▸ hw)
        simp only [φ1, Function.update_of_ne hne]
    have hL : ∫⁻ X, φ1 v X ∂(m0 v) = m0 v (latV b v) := by
      simp only [φ1, Function.update_self]
      exact lintegral_indicator_one hlatm
    have hB : ∀ w, ∫⁻ X, φ0 w X ∂(m0 w) = m0 w (B w) := fun w => lintegral_indicator_one (hBm w)
    have hA : ∫⁻ X, A.indicator (1 : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞) X ∂mi0 = mi0 A :=
      lintegral_indicator_one hAm
    rw [hp, hL, hA] at e2
    simp only [hB] at e2
    set Q := ∏ w ∈ S, m0 w (B w) with hQ
    set a := mi0 A with ha
    set L := m0 v (latV b v) with hLdef
    have hQ0 : Q ≠ 0 := Finset.prod_ne_zero_iff.mpr fun w _ => hB0 w
    have hQt : Q ≠ ⊤ := ENNReal.prod_ne_top fun w _ => hBt w
    have hP0 : a * Q ≠ 0 := mul_ne_zero hA0 hQ0
    have hPt : a * Q ≠ ⊤ := ENNReal.mul_ne_top hAt hQt
    have e4 : (cS S : ℝ≥0∞) * (a * Q) = ((cS (insert v S) : ℝ≥0∞) * L) * (a * Q) := by
      rw [e2]; ring
    have e5 := (ENNReal.mul_left_inj hP0 hPt).mp e4
    have e6 := congrArg ENNReal.toReal e5
    simpa [ENNReal.toReal_mul] using e6
  obtain ⟨c, S₀, -, hS₀⟩ := GlobalTheory.T.infinite_product_renormalization _ (fun v => (m0 v (latV b v)).toReal) cS ∅
    (fun _ => ENNReal.toReal_nonneg) hsum hstep
  have hc : IsEulerProd b I c mi0 m0 := by
    refine ⟨hfin, hsum, S₀, fun S hS φinf φ hφi hφ => ?_⟩
    refine (hcS S φinf φ hφi hφ).trans ?_
    have hcS' : (cS S : ℝ≥0∞) = (c : ℝ≥0∞) *
        ENNReal.ofReal (∏' v : {v // v ∉ S}, (m0 v.1 (latV b v.1)).toReal) := by
      rw [← ENNReal.ofReal_coe_nnreal (p := cS S), (hS₀ S hS).2, ENNReal.ofReal_mul (NNReal.coe_nonneg _),
        ENNReal.ofReal_coe_nnreal]
    rw [hcS']
    ring
  suffices h : c = 1 from h ▸ hc
  obtain ⟨φ, C, φc, φp, φf, hb⟩ := GlobalTheory.T.global_volume_rank_one_normalised F E σ hcm M J hJ hM h₀ d b li lam hli hlam μ 𝓕 hμ h𝓕 mi hmi m hm
  obtain ⟨hdf, κ, hκ, hg⟩ := GlobalTheory.T.finite_volume_rank_one_euler F E σ hcm M J hJ hM h₀ d b lam hlam m hm nzv
  have : BorelSpace (Fin 1 → Fin M → Ainf F ⊗[F] E) := by
    have : BorelSpace (Ainf F ⊗[F] E) := ⟨rfl⟩
    obtain ⟨_, _, _, _, -⟩ := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hcm.1
    exact (GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (Ainf F)).2.2.2.2.2.2.2.1 1 M
  have hφm : Measurable fun X => ENNReal.ofReal (φ X) := φc.measurable.ennreal_ofReal
  set w := ∫⁻ X, ENNReal.ofReal (φ X) ∂mi0 with hw
  have hw0 : 0 < w.toReal := ENNReal.toReal_pos (fun h => nzi (by
    rw [hw, lintegral_eq_zero_iff hφm] at h
    exact ae_eq_bot.1 (Filter.eventually_false_iff_eq_bot.1 (h.mono fun X hX =>
      (ENNReal.ofReal_pos.2 (φp X)).ne' hX)))) φf.ne
  have key : ∀ k : ℕ, ∃ a : ℕ, k < a ∧ |(c : ℝ) - 1| * (w.toReal * κ) * (a : ℝ) ≤ |C| := fun k => by
    obtain ⟨a, ha, h1⟩ := hg k
    have ha0 : 0 < a := lt_of_le_of_lt k.zero_le ha
    have haE : (a : E) ≠ 0 := by exact_mod_cast ha0.ne'
    obtain ⟨I', e1, e2⟩ := hb a ha0
    have hA : ∀ v, MeasurableSet {X : Fin 1 → Fin M → Fv F v ⊗[F] E | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v} := fun v => by
      have hR := GlobalTheory.T.completion_is_local_ring F v
      obtain ⟨_, _, _, _, -⟩ := hR
      have : BorelSpace (Fv F v) := ⟨rfl⟩
      obtain ⟨_, _, _, _, -, -, -, hB, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (Fv F v)
      have := hB 1 M
      have hu : IsUnit (a : Fv F v ⊗[F] E) := by simpa using (Ne.isUnit haE).map (inclR (F := F) (Fv F v))
      have hK : IsCompact {X : Fin 1 → Fin M → Fv F v ⊗[F] E | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v} :=
        (Homeomorph.smul hu.unit).isCompact_preimage.2 ((GlobalTheory.T.adelic_tuple_projections F E σ hcm d b 1 M).2.2.2.1 v).1
      exact hK.measurableSet
    obtain ⟨-, e3⟩ := GlobalTheory.T.euler_product_measure_integral F E σ hcm d b 1 M _ c _ _ hc _ _ hφm (fun v => hA v) (fun v => hdf a ha0 v)
      (((GlobalTheory.T.lattice_stable_almost_everywhere F E σ hcm d b 1 M).1 (Matrix.of fun _ _ => (a : E)) ((Matrix.det_unique _).trans_ne haE)).mono fun v hv => Set.ext fun X => by
        refine Iff.trans (Iff.of_eq (congrArg (· ∈ latV b v) (funext fun p => funext fun i => ?_))) (hv X)
        rw [Subsingleton.elim p 0]
        simp [rmul, mul_comm])
    generalize (∏' v, (m0 v {X : Fin 1 → Fin M → Fv F v ⊗[F] E |
      (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v}).toReal) = P at h1 e2 e3
    have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha0
    have hP : 0 ≤ P := le_trans (by positivity) h1
    have e4 := congrArg ENNReal.toReal (e1.symm.trans e3)
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hP, ENNReal.coe_toReal, ENNReal.coe_toReal] at e4
    rw [e4, show (c : ℝ) * w.toReal * P - w.toReal * P = (c - 1) * (w.toReal * P) by ring, abs_mul,
      abs_of_nonneg (mul_nonneg hw0.le hP)] at e2
    have hD : 0 < Module.finrank ℚ F := Module.finrank_pos
    have h2 : (a : ℝ) * (a : ℝ) ^ (Module.finrank ℚ F * M) ≤ (a : ℝ) ^ (Module.finrank ℚ F * (2 * M - 2)) := by
      rw [← pow_succ']
      refine pow_le_pow_right₀ haR ?_
      obtain ⟨M', rfl⟩ := Nat.exists_eq_add_of_le' hM
      rw [show 2 * (M' + 3) - 2 = M' + 3 + (M' + 1) by omega, mul_add _ (M' + 3)]
      exact Nat.add_le_add_left (Nat.mul_pos hD (Nat.succ_pos _)) _
    refine ⟨a, ha, le_of_mul_le_mul_right ?_ (show (0 : ℝ) < (a : ℝ) ^ (Module.finrank ℚ F * M) by positivity)⟩
    calc _ = |(c : ℝ) - 1| * (w.toReal * (κ * ((a : ℝ) * (a : ℝ) ^ (Module.finrank ℚ F * M)))) := by ring
      _ ≤ |(c : ℝ) - 1| * (w.toReal * P) := by
          gcongr
          exact (mul_le_mul_of_nonneg_left h2 hκ.le).trans h1
      _ ≤ _ := e2.trans (by gcongr; exact le_abs_self C)
  by_contra hne'
  have hp : 0 < |(c : ℝ) - 1| * (w.toReal * κ) :=
    mul_pos (abs_pos.2 (sub_ne_zero.2 (by exact_mod_cast hne'))) (mul_pos hw0 hκ)
  obtain ⟨k, hk⟩ := exists_nat_gt (|C| / (|(c : ℝ) - 1| * (w.toReal * κ)))
  obtain ⟨a, ha, h⟩ := key k
  rw [div_lt_iff₀' hp] at hk
  have : (k : ℝ) < a := by exact_mod_cast ha
  nlinarith

end GlobalTheory.CompanionTheory.SW.OneZero
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothTensorFixedParabolicNearOneStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_tensor_fixed_parabolic_near_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W), IsSmooth τ → IsSmooth σ → ∀ z : V ⊗[ℂ] W, ∃ U ∈ nhds (1 : Mir k (i + t)), ∀ h : HPG k i t, (h : Mir k (i + t)) ∈ U → hRep τ σ h z = z := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.Stab.hRep_fix | exact GlobalTheory.CompanionTheory.BZPsiPG.Stab.hRep_fix | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.Stab.hRep_fix <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SphericalBoundOfHeightsStatement
section
open PositivityTheory.Rg.Rsw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spherical_bound_of_heights : HtExist → SphBound := by
  first | exact @GlobalTheory.CompanionTheory.SphPole.sphBound_of_htExist | exact GlobalTheory.CompanionTheory.SphPole.sphBound_of_htExist | (intros; apply GlobalTheory.CompanionTheory.SphPole.sphBound_of_htExist <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitPlaceRankCutOfAlternative
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Jp

theorem hU_thU (D : D7) (n : ℕ) (v : Pl D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)
    (g : GLoc D.sp.cm.sig (Jst D n) v) :
    hU D n v τ (thU D n v τ g) = GlobalTheory.LocIntw.hgtUp _ D.sp.cm.sig (Jst D n) (absEv D.host.F D.host.E v)
      (GlobalTheory.LocIntw.KUpFin D.sp.cm.sig (Jst D n) v) g := by
  unfold hU
  rw [Function.leftInverse_invFun (GlobalTheory.T.bijective_local_unitary_to_GL D n v τ).1 g]

theorem hU_isHgt (D : D7) (n : ℕ) (v : Pl D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) :
    IsHgt (O := Ov D v) (nvL D v) (hU D n v τ) := by
  intro a d b κ
  obtain ⟨y, hy⟩ := (GlobalTheory.T.bijective_local_unitary_to_GL D n v τ).2 (pM a d b)
  obtain ⟨k, hk⟩ := (GlobalTheory.T.bijective_local_unitary_to_GL D n v τ).2 (inL κ)
  have hkK : k ∈ GlobalTheory.LocIntw.KUpFin D.sp.cm.sig (Jst D n) v := (GlobalTheory.T.mem_maximal_compact_iff_integral_image D n v τ k).2 ⟨κ, hk.symm⟩
  obtain ⟨hyP, hab⟩ := GlobalTheory.T.modulus_upper_parabolic_local D n v τ y a d b hy
  rw [← hy, ← hk, ← map_mul, hU_thU]
  exact (GlobalTheory.LocIntw.hgtUp_mul (GlobalTheory.LocIntw.isIwasawaUp_fin D n v) ⟨y, hyP⟩ hkK).trans hab

theorem rank_beta0 {k : Type} [Field k] {n r t : ℕ} (h : r + t = n) :
    (Matrix.diagonal fun i : Fin n => if i.1 < r then (1 : k) else 0).rank = r := by
  classical
  rw [Matrix.rank_diagonal]
  have hr : r ≤ n := by omega
  simp only [ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not]
  exact Fintype.card_fin_lt_of_le hr

theorem psiV_lift (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (v : Pl D) (w : (Lv D v)ˣ) (ψ₀ : AddChar (kv D v) ℂ)
    (h : ∀ c : Ov D v, psiV D.host.F ψ v (((w⁻¹ : (Lv D v)ˣ) : Lv D v) * algebraMap (Ov D v) (Lv D v) c) =
      ψ₀ (IsLocalRing.residue (Ov D v) c))
    (ℓ : kv D v → Ov D v) (hℓ : ∀ a, IsLocalRing.residue (Ov D v) (ℓ a) = a) {n : ℕ}
    (Y : Matrix (Fin n) (Fin n) (kv D v)) (T₀ : Matrix (Fin n) (Fin n) (Ov D v)) :
    psiV D.host.F ψ v (Matrix.trace ((((w⁻¹ : (Lv D v)ˣ) : Lv D v) • liftM (L := Lv D v) ℓ Y) * T₀.map (algebraMap (Ov D v) (Lv D v)))) =
      ψ₀ (Matrix.trace (Y * T₀.map (IsLocalRing.residue (Ov D v)))) := by
  have key : Matrix.trace ((((w⁻¹ : (Lv D v)ˣ) : Lv D v) • liftM (L := Lv D v) ℓ Y) * T₀.map (algebraMap (Ov D v) (Lv D v)))
      = ((w⁻¹ : (Lv D v)ˣ) : Lv D v) * algebraMap (Ov D v) (Lv D v) (Matrix.trace (Y.map ℓ * T₀)) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
      GlobalTheory.CompanionTheory.Jp.liftM, Matrix.map_apply, map_sum, map_mul, Finset.mul_sum, mul_assoc]
  have key2 : Matrix.trace (Y * T₀.map (IsLocalRing.residue (Ov D v))) =
      IsLocalRing.residue (Ov D v) (Matrix.trace (Y.map ℓ * T₀)) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, map_sum, map_mul, hℓ]
  rw [key, h, key2]

theorem split_place_rank_cut_of_local_computation : JpCondition → SplitPlaceRankCutEigenvalue := by
  intro hA D n r t hrt hr ψ hψ nb hnb v hgood τ
  classical
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Ov D v)
  have hϖ0 : algebraMap (Ov D v) (Lv D v) ϖ ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective (Ov D v) (Lv D v))]
    exact hϖ.ne_zero
  obtain ⟨w, hw⟩ : ∃ w : (Lv D v)ˣ, (w : Lv D v) = algebraMap (Ov D v) (Lv D v) ϖ := ⟨Units.mk0 _ hϖ0, rfl⟩
  obtain ⟨ψ₀, hψ₀, hψ₀c⟩ := GlobalTheory.T.exists_residue_character_of_conductor D ψ v hgood ϖ hϖ w hw
  have hok := GlobalTheory.T.normalized_valuation_uniformizer D v ϖ hϖ w hw
  choose ℓ hℓ using fun a : kv D v => IsLocalRing.residue_surjective (R := Ov D v) a
  have hβ : (Matrix.diagonal fun i : Fin n => if i.1 < r then (1 : kv D v) else 0).rank = r := rank_beta0 hrt
  obtain ⟨ρ, hρ, hρs, hρm⟩ := GlobalTheory.T.surjective_reduction_maximal_compact D n v τ
  obtain ⟨c, hcd, hct, hcint⟩ := hA (Ov D v) (Lv D v) n r t hrt hr ψ₀ hψ₀ _ hβ
  choose f hinf hoff hfX _ using fun Y : Matrix (Fin n) (Fin n) (kv D v) =>
    GlobalTheory.T.exists_global_hermitian_local_approximation D n v τ (((w⁻¹ : (Lv D v)ˣ) : Lv D v) • liftM (L := Lv D v) ℓ Y)
  have hfinj : Function.Injective f := by
    intro Y Y' hYY
    have h1 : ((w⁻¹ : (Lv D v)ˣ) : Lv D v) • liftM (L := Lv D v) ℓ Y =
        ((w⁻¹ : (Lv D v)ˣ) : Lv D v) • liftM (L := Lv D v) ℓ Y' := by
      rw [← hfX Y, ← hfX Y', hYY]
    funext i j
    have h2 := congrFun (congrFun h1 i) j
    simp only [Matrix.smul_apply, smul_eq_mul, GlobalTheory.CompanionTheory.Jp.liftM, Matrix.map_apply] at h2
    have h3 := IsFractionRing.injective (Ov D v) (Lv D v) (mul_left_cancel₀ (Units.ne_zero _) h2)
    rw [← hℓ (Y i j), ← hℓ (Y' i j), h3]
  have hsinf : ∀ x ∈ Finset.univ.image f, ∀ (w' : NumberField.InfinitePlace D.host.F) (i j : Fin n),
      (GlobalTheory.AdelicU.compInf D.host.F D.host.E w') (x.1 i j) = 0 := by
    intro x hx
    obtain ⟨Y, -, rfl⟩ := Finset.mem_image.1 hx
    exact hinf Y
  have hsoff : ∀ x ∈ Finset.univ.image f, ∀ (v' : Pl D), v' ≠ v → ∀ (i j : Fin n),
      (PositivityTheory.Rg.Rsw.L.cv D v') (x.1 i j) = 0 := by
    intro x hx
    obtain ⟨Y, -, rfl⟩ := Finset.mem_image.1 hx
    exact hoff Y
  refine ⟨⟨Finset.univ.image f, fun x => coY ψ₀ (Matrix.diagonal fun i : Fin n => if i.1 < r then (1 : kv D v) else 0)
    (Function.invFun f x), hsinf, hsoff⟩, c, ?_, hcd, hct, ?_⟩
  · intro β' hβ' hint
    have hTint : ∀ i j, (β'.1.map τ) i j ∈ HeightOneSpectrum.adicCompletionIntegers D.host.F v := by
      apply GlobalTheory.T.integral_of_character_trivial_on_lattice D ψ v hgood n
      intro X hX
      obtain ⟨x, hinf', hoff', htx, hint'⟩ := GlobalTheory.T.exists_global_hermitian_local_approximation D n v τ X
      rw [← htx, ← GlobalTheory.T.character_pairing_local_hermitian D n v τ ψ x hinf' hoff' β']
      apply hint
      unfold PositivityTheory.Rg.Rsw.L.IntAt
      exact ⟨hinf', hoff', hint' hX⟩
    let T₀ : Matrix (Fin n) (Fin n) (Ov D v) := fun i j => ⟨(β'.1.map τ) i j, hTint i j⟩
    have hT : (β'.1.map τ : Matrix (Fin n) (Fin n) (Lv D v)) = T₀.map (algebraMap (Ov D v) (Lv D v)) := rfl
    have hne : T₀.map (IsLocalRing.residue (Ov D v)) ≠
        Matrix.diagonal fun i : Fin n => if i.1 < r then (1 : kv D v) else 0 := by
      intro heq
      have h1 := GlobalTheory.T.rank_residue_le_rank_generic (Ov D v) (Lv D v) n T₀
      have h2 := GlobalTheory.Core.Rk.rank_map_field (τ : D.host.E →+* Fv D.host.F v) β'.1
      rw [heq, hβ] at h1
      have h3 : (T₀.map (algebraMap (Ov D v) (Lv D v))).rank = (β'.1.map τ).rank := by rw [← hT]
      exact absurd (h1.trans (h3.trans h2).le) (not_le.2 hβ')
    have hpch : ∀ Y, PositivityTheory.Rg.Rsw.L.pch ψ (f Y).1 (GlobalTheory.MixModel.rat β'.1) =
        ψ₀ (Matrix.trace (Y * T₀.map (IsLocalRing.residue (Ov D v)))) := by
      intro Y
      rw [GlobalTheory.T.character_pairing_local_hermitian D n v τ ψ (f Y) (hinf Y) (hoff Y) β', hfX Y, hT]
      exact psiV_lift D ψ v w ψ₀ hψ₀c ℓ hℓ Y T₀
    show ∑ x ∈ Finset.univ.image f, coY ψ₀ (Matrix.diagonal fun i : Fin n => if i.1 < r then (1 : kv D v) else 0)
      (Function.invFun f x) * PositivityTheory.Rg.Rsw.L.pch ψ x.1 (GlobalTheory.MixModel.rat β'.1) = 0
    rw [Finset.sum_image (fun Y _ Y' _ h => hfinj h)]
    calc _ = ∑ Y, coY ψ₀ (Matrix.diagonal fun i : Fin n => if i.1 < r then (1 : kv D v) else 0) Y *
          ψ₀ (Matrix.trace (Y * T₀.map (IsLocalRing.residue (Ov D v)))) := by
            refine Finset.sum_congr rfl fun Y _ => ?_
            rw [Function.leftInverse_invFun hfinj Y, hpch Y]
      _ = 0 := GlobalTheory.T.sum_character_orthogonality_matrices (kv D v) n ψ₀ hψ₀ _ _ hne
  · intro νv hH hP z
    have e1 : ∀ g, GlobalTheory.CompanionTheory.Jp.sphV D n v z g =
        GlobalTheory.Doubling.npow (hU D n v τ (thU D n v τ g)) (z + (n : ℂ) / 2) := by
      intro g
      rw [hU_thU]
      rfl
    rw [← hcint ϖ hϖ w hw ℓ hℓ (nvL D v) hok (hU D n v τ) (hU_isHgt D n v τ) _ νv ρ hρs (hρm ϖ hϖ) z]
    dsimp only
    congr 1
    funext k
    rw [Finset.sum_image (fun Y _ Y' _ h => hfinj h)]
    refine Finset.sum_congr rfl fun Y _ => ?_
    rw [Function.leftInverse_invFun hfinj Y, e1, map_mul, map_mul, hρ k, GlobalTheory.T.local_image_of_unipotent_element D n nb hnb v τ (f Y), hfX Y]
    rfl

end GlobalTheory.CompanionTheory.Jp

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StandardLatticeMeasureEqOneStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standard_lattice_measure_eq_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), (∀ v, IsStdV v (lam v)) → ∀ v, coordW (Fv F v) b (lam v) 1 1 (latV b v) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.CoordLat.coordW_latV_one | exact GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.CoordLat.coordW_latV_one | (intros; apply GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.CoordLat.coordW_latV_one <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TamagawaFourierIntegrableStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tamagawa_fourier_integrable : ∀ (F : Type) [Field F] [NumberField F], NumberField.IsTotallyReal F → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ (κ : Type) [Fintype κ] [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)] (μ : Measure (κ → AF F)), GlobalTheory.SWLit.IsTamagawa F κ μ → ∀ (Y : Type) [MeasurableSpace Y] (ν : Measure Y) [SFinite ν] (φ : Y → ℂ) (g : Y → κ → AF F), Integrable φ ν → Measurable g → Integrable (fun v : κ → AF F => ∫ y, φ y * ψ (v ⬝ᵥ g y) ∂ν) μ → ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, (∀ y, Φ (g y) = 0) → ∫ z, (∫ v, (∫ y, φ y * ψ (v ⬝ᵥ g y) ∂ν) * ψ (-(v ⬝ᵥ z)) ∂μ) * Φ z ∂μ = 0 := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.pair_vanish | exact GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.pair_vanish | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.pair_vanish <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaFourierJacobiLatticeSwapStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_fourier_jacobi_lattice_swap : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ b₀ : HermE D ρ, b₀.1.det ≠ 0 → ThTwist → ∀ (χ' : (AE D)ˣ →* Circle), IsHeckeChar D χ' → ∀ θ : InfFam D, IsInfFam θ → ∀ Ω, IsTh ψ χ' θ b₀ m.μ Ω → ∀ (χ : (AE D)ˣ →* Circle) (s : ℂ) (f : G D n → ℂ), IsLaw χ s f → ∀ (g γ : _), γ ∈ GF D p → ∀ (T : Mx D ρ p × Mx D ρ p → Mx D ρ p × Mx D ρ p), (∀ y x : Mx D ρ p, ∃ z' : hermA D ρ, M.emb γ * (M.nzx 0 x * M.sh y) = M.nzx z' (T (y, x)).2 * M.sh (T (y, x)).1 * M.emb γ) → ∀ v : Mx D ρ p × Mx D ρ p, (∀ η : Matrix (Fin ρ) (Fin p) D.host.E, ‖Wz M m ψ b₀ f (M.sh (GlobalTheory.CompanionTheory.FJE.rt η) * M.emb γ * (M.nzx 0 v.2 * (M.sh v.1 * g)))‖ = ‖Wz M m ψ b₀ f (M.sh (GlobalTheory.CompanionTheory.FJE.rt η + (T v).1) * M.emb γ * g)‖) ∧ (∑' η : Matrix (Fin ρ) (Fin p) D.host.E, Wz M m ψ b₀ f (M.sh (GlobalTheory.CompanionTheory.FJE.rt η) * M.emb γ * (M.nzx 0 v.2 * (M.sh v.1 * g)))) * conj (th ψ b₀ (Ω 1) 0 v.2 v.1) = GlobalTheory.CompanionTheory.FJE.Ap ψ b₀ (fun y => Wz M m ψ b₀ f (M.sh y * M.emb γ * g)) (Ω γ) (T v) := by
  first | exact @GlobalTheory.CompanionTheory.FJE.term_after | exact GlobalTheory.CompanionTheory.FJE.term_after | (intros; apply GlobalTheory.CompanionTheory.FJE.term_after <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaSeriesInvariantRationalUnitsStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_series_invariant_rational_units : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (φ : (Fin 1 → Fin 1 → Ainf F ⊗[F] E) → ℝ) (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E)) (q : Eˣ) (y : (AF F ⊗[F] E)ˣ), Th φ A (ofE q * y) = Th φ A y := by
  first | exact @GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.Th_ofE_mul | exact GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.Th_ofE_mul | (intros; apply GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.Th_ofE_mul <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaTestFunctionRayAsymptoticStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_test_function_ray_asymptotic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (J : Matrix (Fin 1) (Fin 1) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (θ : ℝ →+* Ainf F) (r : ℝ → (AF F)ˣ), IsRay θ r → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (φ : (Fin 1 → Fin 1 → Ainf F ⊗[F] E) → ℝ) (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E)), IsTest σ J b S φ A → ∀ K : Set (AF F ⊗[F] E)ˣ, IsCompact K → ∃ (N : ℕ) (ρ : ℝ), 0 < N ∧ ∀ k ∈ K, ∀ (X : Fin 1 → Fin 1 → E) (ε : ℝ), 0 < ε → Psi φ A (fun a i => ((k * ofF (r ε) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * inclR (AF F) (X a i)) ≠ 0 → (∀ (p : Fin 1 × Fin 1 × Fin d) (v : HeightOneSpectrum (𝓞 F)), algebraMap F (Fv F v) ((N : F) * b.repr (X p.1 p.2.1) p.2.2) ∈ v.adicCompletionIntegers F) ∧ ∀ (p : Fin 1 × Fin 1 × Fin d) (w : InfinitePlace F), ‖(θ ε * algebraMap F (Ainf F) ((N : F) * b.repr (X p.1 p.2.1) p.2.2)) w‖ ≤ ρ := by
  first | exact @GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.Box.unit_box | exact GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.Box.unit_box | (intros; apply GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.Box.unit_box <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryScalarHasNormOneStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_scalar_has_norm_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (J : Matrix (Fin 1) (Fin 1) E), IsHermND σ J → ∀ h : HA (AF F) σ J, IsNm σ (ue (AF F) σ J h) 1 := by
  first | exact @GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.isNm_ue_one | exact GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.isNm_ue_one | (intros; apply GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.isNm_ue_one <;> assumption)
end

