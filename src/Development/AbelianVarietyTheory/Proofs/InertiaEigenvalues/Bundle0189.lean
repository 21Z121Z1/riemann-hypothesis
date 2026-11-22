import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0143
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyMeasAndReps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0170
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0172
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0178
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0180
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0156
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0174
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0168
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0166
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0161
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0100
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0111
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0119
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0160
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0149
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0059
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0060
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0112
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0098
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0103
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0065
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0087
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0139
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0145
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0173
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0144
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TruncatedWhittakerJHypEqOrbitalIntegral
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory

theorem scale_integral : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ (f : A.K → ℂ) (t : A.K), IsUnit t → ∫ b, f (t * b) ∂μK = ((A.absK t : ℂ))⁻¹ * ∫ s, f s ∂μK := by
  intro F E _ _ _ _ _ A μK hH f t ht
  have := Unram.lcF (F := F) (E := E); have := Unram.ultraF (F := F) (E := E)
  obtain ⟨_, _, _, _, -⟩ := GlobalTheory.JR.EtMeas.top_facts F A.K
  have hme : MeasurableEmbedding (fun b : A.K => ht.unit • b) := (Homeomorph.smul ht.unit).measurableEmbedding
  have hmap : Measure.map (fun b : A.K => ht.unit • b) μK =
      ((distribHaarChar A.K ht.unit : ENNReal))⁻¹ • μK := by
    ext S hS
    rw [hme.map_apply, Measure.smul_apply, smul_eq_mul]
    have h1 := distribHaarChar_mul μK ht.unit⁻¹ S
    rw [Set.preimage_smul, ← h1, map_inv, ENNReal.coe_inv (distribHaarChar_pos).ne']
  have hint : ∫ b, f (t * b) ∂μK = ∫ b, f b ∂(Measure.map (fun b : A.K => ht.unit • b) μK) := by
    rw [hme.integral_map]; rfl
  rw [hint, hmap, integral_smul_measure]
  simp [Et.absK, ht, Complex.real_smul]

theorem jHyp_wn : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ (φ' : A.K × A.K → ℂ) (z : A.K), A.jHyp μK ψ φ' (wS A.K * nS z) = ∫ t, (∫ b, φ' (b, t) * A.psiK ψ (t * z * b) ∂μK) * A.etaK t ∂μK := by
  intro F E _ _ _ _ _ A ψ μK hH φ' z
  have := Unram.lcF (F := F) (E := E); have := Unram.ultraF (F := F) (E := E)
  obtain ⟨_, _, _, _, -⟩ := GlobalTheory.JR.EtMeas.top_facts F A.K
  have : μK.IsNegInvariant := Measure.IsAddHaarMeasure.isNegInvariant_of_regular μK
  have h10 : ((wS A.K * nS z : SpecialLinearGroup (Fin 2) A.K) : Matrix (Fin 2) (Fin 2) A.K) 1 0 = -1 := by
    show (!![0, 1; -1, 0] * !![1, z; 0, 1] : Matrix (Fin 2) (Fin 2) A.K) 1 0 = -1
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have h11 : ((wS A.K * nS z : SpecialLinearGroup (Fin 2) A.K) : Matrix (Fin 2) (Fin 2) A.K) 1 1 = -z := by
    show (!![0, 1; -1, 0] * !![1, z; 0, 1] : Matrix (Fin 2) (Fin 2) A.K) 1 1 = -z
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have heta : ∀ t : A.K, A.etaK (-t) = A.etaK t := by
    intro t
    unfold Et.etaK
    have hg : ∀ x y : F, ‖x‖ = ‖y‖ → eta x = eta y := by
      intro x y h; unfold eta; rw [h]
    apply hg
    show ‖Algebra.norm F (-t)‖ = ‖Algebra.norm F t‖
    rw [show -t = algebraMap F A.K (-1) * t by simp, map_mul, Algebra.norm_algebraMap, norm_mul, norm_pow,
      norm_neg, norm_one, one_pow, one_mul]
  unfold Et.jHyp
  simp only [h10, h11]
  refine (integral_neg_eq_self _ μK).symm.trans ?_
  congr 1
  funext t
  simp only [mul_neg, mul_one, neg_neg, neg_mul, heta]
  rfl

theorem whittaker_jHyp_eq_orbK : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), SelfDual μK (A.kerK ψ) → ∀ φ', IsTest φ' → ∀ a : A.K, IsUnit a → ∀ᶠ c in 𝓝[≠] (0 : F), A.abelian₂ μK ψ a (A.jHyp μK ψ φ') c = A.orbK μK φ' a := by
  intro F E _ _ _ _ _ A ψ hψ μK hμ φ' hφ a ha
  have hH : μK.IsAddHaarMeasure := hμ.1
  have hnull : μK {t : A.K | ¬ IsUnit t} = 0 := (GlobalTheory.T.etaleHermitianPair_structure_facts F E A).2.2.2.2.2.2.2.2.1 μK hH
  have hae : ∀ᵐ t ∂μK, IsUnit t := ae_iff.2 (by simpa using hnull)
  have hV : {v : A.K | ∀ t : A.K, IsUnit t → φ' ((a + v) * Ring.inverse t, t) = φ' (a * Ring.inverse t, t)}
      ∈ 𝓝 (0 : A.K) := by
    have h2 := GlobalTheory.T.eventually_testFunction_mul_inverse_unit_eq F E A φ' hφ a ha
    have hc : Tendsto (fun v : A.K => a + v) (𝓝 0) (𝓝 a) := by
      have := (continuous_add_left a).tendsto (0 : A.K)
      rwa [add_zero] at this
    exact hc h2
  filter_upwards [GlobalTheory.T.eventually_dual_scaled_OK_subset_nhds F E A ψ hψ _ hV, self_mem_nhdsWithin] with c hc hc0
  have hc0' : c ≠ 0 := hc0
  set M := {z : A.K | c • z ∈ A.OK} with hM
  set N := {y : A.K | ∀ x : A.K, c • x ∈ A.OK → A.psiK ψ (x * y) = 1} with hN
  obtain ⟨hNm, hvol⟩ := GlobalTheory.T.volume_scaledIntegers_mul_volume_dual_eq_one F E A ψ hψ μK hμ c hc0'
  have hLam : A.abelian₂ μK ψ a (A.jHyp μK ψ φ') c = (((μK M).toReal : ℝ) : ℂ) *
      ∫ t, (∫ b, φ' (b, t) * N.indicator (fun _ => (1 : ℂ)) (t * b - a) ∂μK) * A.etaK t ∂μK := by
    rw [← GlobalTheory.T.truncatedWhittakerIntegral_eq_volume_mul_integral_perp F E A ψ hψ μK hH φ' hφ a c hc0']
    unfold Et.abelian₂
    simp only [jHyp_wn F E A ψ μK hH φ']
  have hin : ∀ t : A.K, IsUnit t → (∫ b, φ' (b, t) * N.indicator (fun _ => (1 : ℂ)) (t * b - a) ∂μK) =
      ((A.absK t : ℂ))⁻¹ * (φ' (a * Ring.inverse t, t) * (((μK N).toReal : ℝ) : ℂ)) := by
    intro t ht
    have h4 := scale_integral F E A μK hH (fun s => φ' (Ring.inverse t * s, t) * N.indicator (fun _ => (1 : ℂ)) (s - a)) t ht
    simp only [Ring.inverse_mul_cancel_left t _ ht] at h4
    rw [h4]
    congr 1
    have h5 : (fun s => φ' (Ring.inverse t * s, t) * N.indicator (fun _ => (1 : ℂ)) (s - a)) =
        fun s => φ' (a * Ring.inverse t, t) * N.indicator (fun _ => (1 : ℂ)) (s - a) := by
      funext s
      by_cases hs : s - a ∈ N
      · have := hc hs t ht
        simp only [add_sub_cancel] at this
        rw [mul_comm (Ring.inverse t) s, this]
      · simp [Set.indicator_of_notMem hs]
    rw [h5, integral_const_mul]
    congr 1
    have h6 : ∫ s, N.indicator (fun _ => (1 : ℂ)) (s - a) ∂μK = ∫ s, N.indicator (fun _ => (1 : ℂ)) s ∂μK :=
      integral_sub_right_eq_self (fun s => N.indicator (fun _ => (1 : ℂ)) s) a
    rw [h6, integral_indicator_const _ hNm]
    rw [Complex.real_smul, mul_one]
    rfl
  have horb : A.orbK μK φ' a = ∫ t, φ' (a * Ring.inverse t, t) * A.etaK t * ((A.absK t : ℂ))⁻¹ ∂μK := by
    unfold Et.orbK
    rw [Measure.restrict_eq_self_of_ae_mem (s := {t : A.K | IsUnit t}) hae]
  rw [hLam, horb]
  have h7 : ∫ t, (∫ b, φ' (b, t) * N.indicator (fun _ => (1 : ℂ)) (t * b - a) ∂μK) * A.etaK t ∂μK =
      (((μK N).toReal : ℝ) : ℂ) * ∫ t, φ' (a * Ring.inverse t, t) * A.etaK t * ((A.absK t : ℂ))⁻¹ ∂μK := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hae] with t ht
    rw [hin t ht]
    ring
  rw [h7, ← mul_assoc, hvol, one_mul]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TruncatedWhittakerWeilRepEventually
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.WhitX

theorem u_formula (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.K) (ω : A.K → ℂ) (μ : Measure A.L) (γ : ℂ)
    (W : SpecialLinearGroup (Fin 2) A.K → (A.L → ℂ) → A.L → ℂ) (hW : A.IsWeil ψ x ω μ γ W)
    (φ : A.L → ℂ) (hφ : IsTest φ) (z : A.K) :
    W (wS A.K * nS z) φ 0 = γ * ∫ y, φ y * A.psiK ψ (z * x * A.NL y) ∂μ := by
  obtain ⟨hrep, hform⟩ := hW
  rw [hrep.2.2.1 _ _ _ hφ, (hform _ (hrep.1 _ _ hφ)).2.2 0]
  congr 1
  unfold fourB
  congr 1
  funext y
  rw [(hform φ hφ).1 z y]
  simp [Et.kerL, Et.psiK, mul_comm]

theorem M_sub (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
    [Unram F E] (A : Et F E) (c : F) (hc : c ≠ 0) :
    ∃ M : AddSubgroup A.K, (M : Set A.K) = {z : A.K | c • z ∈ A.OK} ∧ IsOpen (M : Set A.K) ∧ IsCompact (M : Set A.K) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hOo, hOc, R, hR⟩ := GlobalTheory.T.etaleHermitianPair_structure_facts F E A
  haveI : ContinuousSMul F A.K := IsModuleTopology.toContinuousSMul F A.K
  refine ⟨(R.toAddSubgroup).comap (DistribMulAction.toAddMonoidHom A.K c), ?_, ?_, ?_⟩
  · ext z; simp [← hR]
  · have : ((R.toAddSubgroup).comap (DistribMulAction.toAddMonoidHom A.K c) : Set A.K) = (fun z => c • z) ⁻¹' A.OK := by
      ext z; simp [← hR]
    rw [this]; exact hOo.preimage (continuous_const_smul c)
  · have : ((R.toAddSubgroup).comap (DistribMulAction.toAddMonoidHom A.K c) : Set A.K) = (fun z => c⁻¹ • z) '' A.OK := by
      ext z; simp only [AddSubgroup.coe_comap, Set.mem_preimage, Set.mem_image, DistribMulAction.toAddMonoidHom_apply]
      constructor
      · intro h; exact ⟨c • z, by simpa [← hR] using h, by simp [smul_smul, inv_mul_cancel₀ hc]⟩
      · rintro ⟨w, hw, rfl⟩; simpa [smul_smul, mul_inv_cancel₀ hc, ← hR] using hw
    rw [this]; exact hOc.image (continuous_const_smul c⁻¹)

theorem lam_weil_eventually : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (m : A.Meas ψ) (x : A.Kˣ) (γ : ℂ) W, A.IsWeil ψ x A.etaK (m.μL x) γ W → ∀ φ, IsTest φ → ∀ a : A.K, IsUnit a → (∀ y : A.L, IsUnit y → a = x * A.NL y → ∀ᶠ c in 𝓝[≠] (0 : F), A.abelian₂ m.μK ψ a (fun g => W g φ 0) c = γ * A.orbL m.ν φ y) ∧ ((¬ ∃ y : A.L, IsUnit y ∧ a = x * A.NL y) → ∀ᶠ c in 𝓝[≠] (0 : F), A.abelian₂ m.μK ψ a (fun g => W g φ 0) c = 0) := by
  intro F E _ _ _ _ _ A ψ hψ m x γ W hW φ hφ a ha
  haveI := m.sdK.1
  haveI := (m.sdL x).1
  obtain ⟨-, -, hnd, -, -, -, -, -, -, hOo, -, R, hR⟩ := GlobalTheory.T.etaleHermitianPair_structure_facts F E A
  have key : ∀ c : F, c ≠ 0 → A.abelian₂ m.μK ψ a (fun g => W g φ 0) c =
      γ * ((m.μK {z | c • z ∈ A.OK}).toReal : ℂ) *
        ∫ y, φ y * Set.indicator {b : A.K | ∀ z : A.K, c • z ∈ A.OK → A.psiK ψ (z * b) = 1} (fun _ => (1 : ℂ))
          ((x : A.K) * A.NL y - a) ∂(m.μL x) := by
    intro c hc
    unfold Et.abelian₂
    simp_rw [u_formula F E A ψ x A.etaK (m.μL x) γ W hW φ hφ, mul_assoc γ]
    rw [integral_const_mul, GlobalTheory.T.setIntegral_integral_psiK_swap F E A ψ hψ m.μK inferInstance (m.μL x) inferInstance φ hφ x a c hc]
    simp_rw [GlobalTheory.T.integral_psiK_over_scaled_integers_eq_volume_indicator F E A ψ hψ m.μK inferInstance c hc]
    congr 1
    rw [← integral_const_mul]
    congr 1; funext y
    simp only [Set.indicator]
    split_ifs <;> ring
  obtain ⟨U1, hU1, hinv⟩ := GlobalTheory.T.exists_nhds_one_etaleAlgebra_mul_invariant F E A φ hφ
  have hOK1 : A.OK ∈ 𝓝 (1 : A.K) := hOo.mem_nhds (by rw [← hR]; exact R.one_mem)
  have hsq := GlobalTheory.T.finiteEtale_exists_sq_root_near_one F E A (U1 ∩ A.OK) (inter_mem hU1 hOK1)
  have hcont : Tendsto (fun b : A.K => 1 + Ring.inverse a * b) (𝓝 0) (𝓝 1) := by
    have : Continuous (fun b : A.K => 1 + Ring.inverse a * b) := by fun_prop
    simpa using this.tendsto 0
  have hU : {b : A.K | ∃ s ∈ U1 ∩ A.OK, ∃ s' ∈ U1 ∩ A.OK, s * s' = 1 ∧ s ^ 2 = 1 + Ring.inverse a * b} ∈ 𝓝 (0 : A.K) :=
    hcont hsq
  have hev := GlobalTheory.T.scaledIntegersK_annihilator_small_near_zero F E A ψ hψ _ hU
  have hne : ∀ᶠ c in 𝓝[≠] (0 : F), c ≠ 0 := self_mem_nhdsWithin
  constructor
  · intro y hy hay
    filter_upwards [hev, hne] with c hc hc0
    rw [key c hc0]
    obtain ⟨D, hDset, hDo, hDc⟩ := GlobalTheory.T.exists_openCompact_annihilator_scaled_integersK F E A ψ hψ c hc0
    obtain ⟨M, hMset, hMo, hMc⟩ := M_sub F E A c hc0
    have hMD : m.μK M * m.μK D = 1 := by
      have h := ((GlobalTheory.T.selfDual_iff_lattice_volume_and_plancherel_alt F E ψ hψ A.K (Algebra.traceForm F A.K) (Algebra.traceForm_isSymm F) hnd m.μK
        inferInstance).1 M hMo hMc).1
      have hk : A.kerK ψ = fun x y => ψ (Algebra.traceForm F A.K x y) := by
        funext x y; simp [Et.kerK, Et.psiK, Algebra.traceForm_apply]
      have hsd : SelfDual m.μK (fun x y => ψ (Algebra.traceForm F A.K x y)) := hk ▸ m.sdK
      have hDeq : (D : Set A.K) = {y | ∀ x ∈ M, ψ (Algebra.traceForm F A.K x y) = 1} := by
        rw [hDset]; ext b; simp [← SetLike.mem_coe, hMset, Et.psiK, Algebra.traceForm_apply]
      rw [hDeq]; exact h.1 hsd
    rw [← hDset, ← hMset]
    subst hay
    rw [GlobalTheory.T.truncatedIntegral_eq_vol_mul_orbitalIntegral F E A (GlobalTheory.T.finiteEtaleHermitianPair_norm_properties F E A) (GlobalTheory.T.absK_multiplicative_unitOne_haarScaling F E A) ψ hψ m x y hy D hDo hDc φ hφ ?_]
    · have : (m.μK M).toReal * (m.μK D).toReal = 1 := by rw [← ENNReal.toReal_mul, hMD]; simp
      have : ((m.μK M).toReal : ℂ) * ((m.μK D).toReal : ℂ) = 1 := by exact_mod_cast this
      linear_combination (γ * A.orbL m.ν φ y) * this
    · intro b hb
      have hb' := hc b (by rw [← SetLike.mem_coe, hDset] at hb; exact hb)
      obtain ⟨s, ⟨hsU, hsO⟩, s', ⟨hsU', hsO'⟩, hss, hs2⟩ := hb'
      exact ⟨s, s', hsO, hsO', hss, hs2, hinv s hsU s' hsU' hss⟩
  · intro hno
    filter_upwards [hev, hne] with c hc hc0
    rw [key c hc0]
    have hz := GlobalTheory.T.truncated_set_empty_outside_norm_coset F E A (GlobalTheory.T.finiteEtaleHermitianPair_norm_properties F E A) x a {b : A.K | ∀ z : A.K, c • z ∈ A.OK → A.psiK ψ (z * b) = 1}
      (fun b hb => by
        obtain ⟨s, -, s', -, hss, hs2⟩ := hc b hb
        exact ⟨s, s', hss, hs2⟩) ha hno
    have : (fun y => φ y * Set.indicator {b : A.K | ∀ z : A.K, c • z ∈ A.OK → A.psiK ψ (z * b) = 1}
        (fun _ => (1 : ℂ)) ((x : A.K) * A.NL y - a)) = fun _ => 0 := by
      funext y; rw [Set.indicator_of_notMem (hz y)]; simp
    rw [this]; simp

end GlobalTheory.JR.WhitX
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryOrbitalIntegralLiftLastBasisReduce
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.Step.OrbULift
theorem actU_uEmb_liftH : ∀ {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] {r : ℕ} (s : Matrix.unitaryGroup (Fin r) E) (X : Hn r F E) (ν : E) (l : F), actU (GlobalTheory.JR.Step.uEmb r E s) (GlobalTheory.JR.Step.liftH X ν l) = GlobalTheory.JR.Step.liftH (actU s X) ν l := GlobalTheory.T.unitaryActHermitianBlock_diagOne_liftLastBasis
theorem unitU_liftH : ∀ {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] {r : ℕ} (X : Hn r F E) (ν : E) (l : F), ‖ν‖ ≤ 1 → unitU (r + 1) F E (GlobalTheory.JR.Step.liftH X ν l) = (if ‖l‖ ≤ 1 then 1 else 0) * unitU r F E X := GlobalTheory.T.unitIndicatorHermitianBlock_liftLastBasis_of_norm_le_one
theorem support_sub : ∀ {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] {r : ℕ} (X : Hn r F E) (ν : E) (l : F), ‖ν‖ = 1 → ∀ g : Matrix.unitaryGroup (Fin (r + 1)) E, unitU (r + 1) F E (actU g (GlobalTheory.JR.Step.liftH X ν l)) ≠ 0 → ∃ k ∈ uO (r + 1) E, ∃ s, g = k * GlobalTheory.JR.Step.uEmb r E s := GlobalTheory.T.unitaryAct_liftHermitianBlock_mem_integralUnitary_mul_embedding
theorem support_bounded : ∀ {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] {n : ℕ} (Y : Hn n F E), Delta (inv Y.toGl) ≠ 0 → ∃ K : Set (Matrix.unitaryGroup (Fin n) E), IsCompact K ∧ ∀ g, unitU n F E (actU g Y) ≠ 0 → g ∈ K := GlobalTheory.T.exists_compact_unitaries_integral_orbit_of_hankelDet_ne_zero
theorem uEmb_isClosedEmbedding : ∀ (r : ℕ) (E : Type) [NormedField E] [StarRing E] [ContinuousStar E], Topology.IsClosedEmbedding (GlobalTheory.JR.Step.uEmb r E) := GlobalTheory.T.isClosedEmbedding_diagOneUnitaryGroupEmbedding

section Reformulated
variable {E : Type} [NormedField E]

theorem entries_mul_le {n : ℕ} [IsUltrametricDist E] {P Q : Matrix (Fin n) (Fin n) E}
    (hP : ∀ i j, ‖P i j‖ ≤ 1) (hQ : ∀ i j, ‖Q i j‖ ≤ 1) : ∀ i j, ‖(P * Q) i j‖ ≤ 1 := by
  intro i j
  rw [Matrix.mul_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hP i k) (norm_nonneg _) (hQ k j)

theorem entries_mulVec_le {n : ℕ} [IsUltrametricDist E] {P : Matrix (Fin n) (Fin n) E} {v : Fin n → E}
    (hP : ∀ i j, ‖P i j‖ ≤ 1) (hv : ∀ i, ‖v i‖ ≤ 1) : ∀ i, ‖(P *ᵥ v) i‖ ≤ 1 := by
  intro i
  simp only [Matrix.mulVec, dotProduct]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hP i k) (norm_nonneg _) (hv k)

variable [StarRing E]

theorem entries_star_le {n : ℕ} [NormedStarGroup E] {P : Matrix (Fin n) (Fin n) E}
    (hP : ∀ i j, ‖P i j‖ ≤ 1) : ∀ i j, ‖(star P) i j‖ ≤ 1 := by
  intro i j
  rw [Matrix.star_apply, norm_star]
  exact hP j i

theorem uO_mul {n : ℕ} [IsUltrametricDist E]
    {a b : Matrix.unitaryGroup (Fin n) E} (ha : a ∈ uO n E) (hb : b ∈ uO n E) : a * b ∈ uO n E :=
  entries_mul_le (P := a.1) (Q := b.1) ha hb

theorem uO_one {n : ℕ} : (1 : Matrix.unitaryGroup (Fin n) E) ∈ uO n E := by
  intro i j
  show ‖(1 : Matrix (Fin n) (Fin n) E) i j‖ ≤ 1
  rw [Matrix.one_apply]
  split_ifs <;> simp

theorem uO_inv {n : ℕ} [NormedStarGroup E]
    {a : Matrix.unitaryGroup (Fin n) E} (ha : a ∈ uO n E) : a⁻¹ ∈ uO n E :=
  entries_star_le (P := a.1) ha

theorem uO_isOpen {n : ℕ} [IsUltrametricDist E] : IsOpen (uO n E) := by
  have e : uO n E = ⋂ i, ⋂ j, (fun g : Matrix.unitaryGroup (Fin n) E => g.1 i j) ⁻¹' Metric.closedBall 0 1 := by
    ext g; simp [uO]
  rw [e]
  have hc : ∀ i j, Continuous (fun g : Matrix.unitaryGroup (Fin n) E => g.1 i j) := fun i j =>
    (continuous_subtype_val (p := fun M => M ∈ Matrix.unitaryGroup (Fin n) E)).matrix_elem i j
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    (IsUltrametricDist.isOpen_closedBall (0 : E) one_ne_zero).preimage (hc i j)

theorem isClosed_unitaryGroup' {n : ℕ} [ContinuousStar E] :
    IsClosed (Matrix.unitaryGroup (Fin n) E : Set (Matrix (Fin n) (Fin n) E)) := by
  have e : (Matrix.unitaryGroup (Fin n) E : Set (Matrix (Fin n) (Fin n) E)) = {M | star M * M = 1} := by
    ext M; exact Matrix.mem_unitaryGroup_iff'
  rw [e]
  exact isClosed_eq (continuous_star.matrix_mul continuous_id) continuous_const

theorem uO_isCompact {n : ℕ} [ProperSpace E] [ContinuousStar E] : IsCompact (uO n E) := by
  let B : Set (Matrix (Fin n) (Fin n) E) :=
    Set.univ.pi fun _ => Set.univ.pi fun _ => Metric.closedBall (0 : E) 1
  have hB : IsCompact B := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  have e : uO n E = Subtype.val ⁻¹' B := by
    ext g
    show (∀ i j, ‖g.1 i j‖ ≤ 1) ↔
      (∀ i ∈ (Set.univ : Set (Fin n)), ∀ j ∈ (Set.univ : Set (Fin n)), g.1 i j ∈ Metric.closedBall (0 : E) 1)
    simp
  rw [e]
  exact (isClosed_unitaryGroup' (n := n)).isClosedEmbedding_subtypeVal.isCompact_preimage hB

theorem preimage_uO (r : ℕ) : uEmb r E ⁻¹' uO (r + 1) E = uO r E := by
  ext s
  simp only [Set.mem_preimage, uO, Set.mem_setOf_eq]
  constructor
  · intro h i j
    have := h (Fin.castSucc i) (Fin.castSucc j)
    simpa [uEmb, embHom, Matrix.reindex_apply] using this
  · intro h i j
    show ‖(embHom r E s.1) i j‖ ≤ 1
    simp only [embHom, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.reindex_apply, Matrix.submatrix_apply]
    generalize finSumFinEquiv.symm i = a
    generalize finSumFinEquiv.symm j = b
    rcases a with a | a <;> rcases b with b | b
    · simpa using h a b
    · simp
    · simp
    · rw [Matrix.fromBlocks_apply₂₂, Matrix.one_apply]; split_ifs <;> simp

theorem actU_mul {F : Type} [CommRing F] [Algebra F E] {n : ℕ} (k g : Matrix.unitaryGroup (Fin n) E)
    (Y : Hn n F E) : actU (k * g) Y = actU k (actU g Y) := by
  unfold actU
  refine Prod.ext (Subtype.ext ?_) (Prod.ext ?_ rfl)
  · show (k.1 * g.1) * Y.1.1 * star (k.1 * g.1) = k.1 * (g.1 * Y.1.1 * star g.1) * star k.1
    rw [star_mul]; simp only [Matrix.mul_assoc]
  · show (k.1 * g.1) *ᵥ Y.2.1 = k.1 *ᵥ (g.1 *ᵥ Y.2.1)
    rw [Matrix.mulVec_mulVec]

theorem actU_one {F : Type} [CommRing F] [Algebra F E] {n : ℕ} (Y : Hn n F E) :
    actU (1 : Matrix.unitaryGroup (Fin n) E) Y = Y := by
  unfold actU
  refine Prod.ext (Subtype.ext ?_) (Prod.ext ?_ rfl)
  · show (1 : Matrix (Fin n) (Fin n) E) * Y.1.1 * star (1 : Matrix (Fin n) (Fin n) E) = Y.1.1
    simp
  · show (1 : Matrix (Fin n) (Fin n) E) *ᵥ Y.2.1 = Y.2.1
    simp

theorem integral_actU {F : Type} [NormedField F] [Algebra F E] [IsUltrametricDist E] [NormedStarGroup E] {n : ℕ}
    (k : Matrix.unitaryGroup (Fin n) E) (hk : k ∈ uO n E) (Y : Hn n F E)
    (hY : Y ∈ {X : Hn n F E | (∀ i j, ‖X.1.1 i j‖ ≤ 1) ∧ (∀ i, ‖X.2.1 i‖ ≤ 1) ∧ ‖X.2.2‖ ≤ 1}) :
    actU k Y ∈ {X : Hn n F E | (∀ i j, ‖X.1.1 i j‖ ≤ 1) ∧ (∀ i, ‖X.2.1 i‖ ≤ 1) ∧ ‖X.2.2‖ ≤ 1} := by
  obtain ⟨h1, h2, h3⟩ := hY
  refine ⟨?_, ?_, h3⟩
  · exact entries_mul_le (entries_mul_le hk h1) (entries_star_le hk)
  · exact entries_mulVec_le hk h2

end Reformulated

theorem unitU_actU_mul {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
    [IsUltrametricDist E] [NormedStarGroup E] {n : ℕ} (k g : Matrix.unitaryGroup (Fin n) E) (hk : k ∈ uO n E)
    (Y : Hn n F E) : unitU n F E (actU (k * g) Y) = unitU n F E (actU g Y) := by
  rw [actU_mul]
  have hiff : ∀ Z : Hn n F E, actU k Z ∈ {X : Hn n F E | (∀ i j, ‖X.1.1 i j‖ ≤ 1) ∧ (∀ i, ‖X.2.1 i‖ ≤ 1) ∧ ‖X.2.2‖ ≤ 1} ↔
      Z ∈ {X : Hn n F E | (∀ i j, ‖X.1.1 i j‖ ≤ 1) ∧ (∀ i, ‖X.2.1 i‖ ≤ 1) ∧ ‖X.2.2‖ ≤ 1} := fun Z =>
    ⟨fun h => by
      have := integral_actU k⁻¹ (uO_inv hk) _ h
      rwa [← actU_mul, inv_mul_cancel, actU_one] at this, fun h => integral_actU k hk Z h⟩
  unfold unitU
  by_cases h : actU g Y ∈ {X : Hn n F E | (∀ i j, ‖X.1.1 i j‖ ≤ 1) ∧ (∀ i, ‖X.2.1 i‖ ≤ 1) ∧ ‖X.2.2‖ ≤ 1}
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem ((hiff _).2 h)]; rfl
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h ((hiff _).1 h'))]

theorem compact_support {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] {r : ℕ} (X : Hn r F E) (ν : E) (l : F)
    (hΔ : Delta (inv (liftH X ν l).toGl) ≠ 0) :
    HasCompactSupport (fun s => unitU (r + 1) F E (actU (uEmb r E s) (liftH X ν l))) := by
  haveI : NormedStarGroup E := ⟨fun x => (Unram.norm_star (F := F) x).le⟩
  obtain ⟨K, hK, hsub⟩ := support_bounded (liftH X ν l) hΔ
  refine HasCompactSupport.intro ((uEmb_isClosedEmbedding r E).isCompact_preimage hK) ?_
  intro s hs
  by_contra h
  exact hs (hsub _ h)

theorem orbU_liftH (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas (r + 1) F E) (M' : Meas r F E) (X : Hn r F E) (ν : E) (l : F) (hν : ‖ν‖ = 1) (hΔ : Delta (inv (GlobalTheory.JR.Step.liftH X ν l).toGl) ≠ 0) :
  orbU M (unitU (r + 1) F E) (GlobalTheory.JR.Step.liftH X ν l) = (if ‖l‖ ≤ 1 then 1 else 0) * orbU M' (unitU r F E) X := by
  haveI : IsUltrametricDist E := Unram.ultraE (F := F)
  haveI : NormedStarGroup E := ⟨fun x => (Unram.norm_star (F := F) x).le⟩
  haveI : LocallyCompactSpace E := Unram.lcE (F := F)
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  haveI : SecondCountableTopology (Matrix (Fin (r+1)) (Fin (r+1)) E) :=
    inferInstanceAs (SecondCountableTopology (Fin (r+1) → Fin (r+1) → E))
  haveI : SecondCountableTopology (Matrix.unitaryGroup (Fin (r+1)) E) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : LocallyCompactSpace (Matrix.unitaryGroup (Fin (r+1)) E) := by
    exact IsCompact.locallyCompactSpace_of_mem_nhds_of_group (uO_isCompact (n := r + 1))
      (uO_isOpen.mem_nhds uO_one)
  let R₀ : Subgroup (Matrix.unitaryGroup (Fin (r+1)) E) :=
    { carrier := uO (r+1) E, mul_mem' := uO_mul, one_mem' := uO_one, inv_mem' := uO_inv }
  unfold orbU
  letI := M.mU; haveI := M.bU; letI := M'.mU; haveI := M'.bU
  haveI := M.haarU; haveI := M'.haarU
  haveI := (GlobalTheory.T.unitaryGroup_positiveCharacter_trivial_and_unimodular F E (r+1)).2 M
  haveI := (GlobalTheory.T.unitaryGroup_positiveCharacter_trivial_and_unimodular F E r).2 M'
  rw [GlobalTheory.CosetIntegral.integral_eq_of_coset_support _ _ (uEmb r E) (uEmb_isClosedEmbedding r E) M.μU M'.μU R₀
    uO_isOpen uO_isCompact M.volU (by
      show M'.μU (uEmb r E ⁻¹' uO (r + 1) E) = 1
      rw [preimage_uO]; exact M'.volU)
    _ (fun k hk g => unitU_actU_mul k g hk _) (support_sub X ν l hν) (compact_support X ν l hΔ)]
  simp_rw [actU_uEmb_liftH, unitU_liftH _ ν l hν.le]
  rw [integral_const_mul]
end GlobalTheory.JR.Step.OrbULift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedBaseChangeLatticeCountEq
section
noncomputable section

namespace GlobalTheory.UnitLemma.Unr

open GlobalTheory.UnitLemma Polynomial

theorem N_overExt : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ (B : InvAlg K) (ψ : K'.E →+* B.A) (hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e) (hσ : ∀ e, B.σ (ψ e) = ψ (K'.c e)), (∀ y : K'.O, ψ (algebraMap K'.O K'.E y) ∈ Algebra.adjoin K.O ({B.g} : Set B.A)) → ∀ x : B.A, (overExt φ B ψ hψ hσ).N x = B.N x := by
  intro K K' d φ hU B ψ hψ hσ hO x
  refine (@GlobalTheory.T.weightedOrbitSum_congr_coefficientRing K.O K'.O B.A _ _ B.cA B.aO (overExt φ B ψ hψ hσ).aO B.T (B.X x) ((overExt φ B ψ hψ hσ).X x) ?_ ?_ ?_)
  · intro L hL
    let S : Subalgebra K.O B.A :=
      { carrier := {a | ∀ z ∈ L, a * z ∈ L}
        mul_mem' := fun {a b} ha hb z hz => by rw [mul_assoc]; exact ha _ (hb z hz)
        add_mem' := fun {a b} ha hb z hz => by rw [add_mul]; exact L.add_mem (ha z hz) (hb z hz)
        algebraMap_mem' := fun c z hz => by rw [← Algebra.smul_def]; exact L.smul_mem c hz }
    have hS : Algebra.adjoin K.O ({B.g} : Set B.A) ≤ S := by
      rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff]
      exact fun z hz => hL.2.1 z hz
    let L' : Submodule K'.O (overExt φ B ψ hψ hσ).A :=
      { carrier := (L : Set B.A)
        add_mem' := fun ha hb => L.add_mem ha hb
        zero_mem' := L.zero_mem
        smul_mem' := fun c z hz => hS (hO c) z hz }
    refine ⟨L', ⟨(GlobalTheory.T.isFullLatticeOver_unramifiedExt_iff K K' d φ hU B ψ hψ hσ L' L rfl).2 hL.1, fun y hy => hL.2.1 y hy, fun y => ?_⟩, rfl⟩
    exact (hL.2.2 y).trans (GlobalTheory.T.hermitianDual_invAlgBaseChangeUnramified_iff K K' d φ hU B ψ hψ hσ L' x y).symm
  · intro L' hL'
    let M : Submodule K.O B.A :=
      { carrier := (L' : Set B.A)
        add_mem' := fun ha hb => L'.add_mem ha hb
        zero_mem' := L'.zero_mem
        smul_mem' := fun c z hz => by
          obtain ⟨b, hb⟩ := exists_int_image hU c
          have h : c • z = ψ (algebraMap K'.O K'.E b) * z := by
            rw [Algebra.smul_def, hb, hψ, ← IsScalarTower.algebraMap_apply]
          rw [h]; exact L'.smul_mem b hz }
    refine ⟨M, ⟨(GlobalTheory.T.isFullLatticeOver_unramifiedExt_iff K K' d φ hU B ψ hψ hσ L' M rfl).1 hL'.1, fun y hy => hL'.2.1 y hy, fun y => ?_⟩, rfl⟩
    exact (hL'.2.2 y).trans (GlobalTheory.T.hermitianDual_invAlgBaseChangeUnramified_iff K K' d φ hU B ψ hψ hσ L' x y)
  · ext t
    simp only [Subgroup.mem_inf]
    refine and_congr_left' ?_
    change (IsIntegral K.O (t : B.A) ∧ IsIntegral K.O ((t⁻¹ : B.Aˣ) : B.A)) ↔
      (@IsIntegral K'.O (overExt φ B ψ hψ hσ).A _ _ _ (t : B.A) ∧ @IsIntegral K'.O (overExt φ B ψ hψ hσ).A _ _ _ ((t⁻¹ : B.Aˣ) : B.A))
    rw [GlobalTheory.T.isIntegral_unramifiedExt_iff_isIntegral_base K K' d φ hU B ψ hψ hσ, GlobalTheory.T.isIntegral_unramifiedExt_iff_isIntegral_base K K' d φ hU B ψ hψ hσ]

end GlobalTheory.UnitLemma.Unr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.XPowSmulMemPrimePowAddFiltrationPhiModuleStatement
section
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.X_pow_smul_mem_prime_pow_add_filtration_phiModule : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] (P : PhiMod O K l e a ι), ∀ (j : ℕ), j ≤ l → ∀ w ∈ P.MM, ∃ s ∈ P.MM, ∃ f ∈ P.FilMM j, (X : K⟦X⟧) ^ (e * l) • w = (l : K) ^ (l - j) • s + f := by
  first | exact @GlobalTheory.BK.X_pow_smul_mem_l_pow_MM_add_FilMM | exact GlobalTheory.BK.X_pow_smul_mem_l_pow_MM_add_FilMM | (intros; apply GlobalTheory.BK.X_pow_smul_mem_l_pow_MM_add_FilMM <;> assumption)
end

