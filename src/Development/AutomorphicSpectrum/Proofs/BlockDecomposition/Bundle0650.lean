import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0632
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FintypeResidue
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0601
import GroundTheory.AutomorphicForms.MacdonaldWhittaker
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.GlobalDifferentialForms.PullHEq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.HdgAffIso
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GrCechFin
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreClassOfCechSpectralSequence
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinBasicFirst
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0618
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinBasicThird
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0619
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0534
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0591
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0604

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentiableBoundaryZetaTerm
section
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate SchwartzMap Classical
open Ad3 Ad3.R

namespace GlobalTheory.CompanionTheory.RSZeta

theorem Bd_differentiable : ∀ (μ : Measure G2) (𝓕 : Set G2) (mK : Measure KA) (𝓓 : Set Jd) (H : G2 → ℂ) (c : HeckeCharacter ℚ),
    Set0 μ 𝓕 mK 𝓓 → Aut H → Differentiable ℂ (GlobalTheory.CompanionTheory.RSZeta.Bd μ 𝓕 H c) := by
  intro μ 𝓕 mK 𝓓 H c h0 hH s₀
  obtain ⟨C, hC⟩ := hH.bdd
  have hband : MeasurableSet band :=
    (measurable_Dt measurableSet_Ici).inter (measurable_Dt measurableSet_Iio)
  have hS : MeasurableSet (𝓕 ∩ band) := h0.meas.inter hband
  haveI : IsFiniteMeasure (μ.restrict (𝓕 ∩ band)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact h0.vol⟩
  set R : ℝ := |s₀.re| + 1 with hR
  have hR0 : 0 ≤ R := by positivity
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 1)

  have hpow : ∀ g ∈ 𝓕 ∩ band, ∀ s ∈ Metric.ball s₀ 1, ‖((Dt g : ℝ) : ℂ) ^ s‖ ≤ (2 : ℝ) ^ R := by
    intro g hg s hs
    obtain ⟨h1, h2⟩ := hg.2
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (Dt_pos g)]
    have hre : s.re ≤ R := by
      have h3 : |(s - s₀).re| ≤ ‖s - s₀‖ := Complex.abs_re_le_norm _
      have h4 : ‖s - s₀‖ < 1 := by simpa [dist_eq_norm] using hs
      have h5 := abs_le.1 h3
      have h6 := le_abs_self s₀.re
      simp only [Complex.sub_re] at h5
      rw [hR]; linarith [h5.2]
    calc Dt g ^ s.re ≤ Dt g ^ R := Real.rpow_le_rpow_of_exponent_le h1 hre
      _ ≤ (2 : ℝ) ^ R := Real.rpow_le_rpow (Dt_pos g).le h2.le hR0
  have hlog : ∀ g ∈ 𝓕 ∩ band, ‖Complex.log ((Dt g : ℝ) : ℂ)‖ ≤ 1 := by
    intro g hg
    obtain ⟨h1, h2⟩ := hg.2
    rw [← Complex.ofReal_log (Dt_pos g).le, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg h1)]
    linarith [Real.log_le_sub_one_of_pos (Dt_pos g)]
  have hF' : ∀ s : ℂ, Measurable fun g =>
      H g * cdet c g * (((Dt g : ℝ) : ℂ) ^ s * Complex.log ((Dt g : ℝ) : ℂ)) := by
    intro s
    have hl : Measurable fun g => Complex.log ((Dt g : ℝ) : ℂ) :=
      Complex.measurable_log.comp (Complex.measurable_ofReal.comp measurable_Dt)
    exact (hH.cont.measurable.mul (measurable_cdet c)).mul
      (((Complex.measurable_ofReal.comp measurable_Dt).pow_const s).mul hl)
  have hbd : ∀ g ∈ 𝓕 ∩ band, ∀ s ∈ Metric.ball s₀ 1, ‖H g * cdet c g * ((((Dt g : ℝ) : ℂ) ^ s) * Complex.log ((Dt g : ℝ) : ℂ))‖ ≤ C * (2 : ℝ) ^ R := by
    intro g hg s hs
    rw [norm_mul, norm_mul, norm_mul, norm_cdet, mul_one]
    have h1 := hpow g hg s hs
    have h2 := hlog g hg
    have h3 := hC g
    calc ‖H g‖ * (‖((Dt g : ℝ) : ℂ) ^ s‖ * ‖Complex.log ((Dt g : ℝ) : ℂ)‖)
        ≤ C * ((2 : ℝ) ^ R * 1) := by gcongr
      _ = C * (2 : ℝ) ^ R := by ring
  have hint : Integrable (fun g => H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ s₀) (μ.restrict (𝓕 ∩ band)) := by
    refine (integrable_const (C * (2 : ℝ) ^ R)).mono' (measurable_w hH c s₀).aestronglyMeasurable ?_
    refine (ae_restrict_iff' hS).2 (Eventually.of_forall fun g hg => ?_)
    rw [norm_mul, norm_mul, norm_cdet, mul_one]
    have h1 := hpow g hg s₀ (Metric.mem_ball_self one_pos)
    have h3 := hC g
    gcongr
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ.restrict (𝓕 ∩ band))
    (F := fun s g => H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ s)
    (F' := fun s g => H g * cdet c g * (((Dt g : ℝ) : ℂ) ^ s * Complex.log ((Dt g : ℝ) : ℂ)))
    (x₀ := s₀) (s := Metric.ball s₀ 1) (bound := fun _ => C * (2 : ℝ) ^ R)
    (Metric.ball_mem_nhds s₀ one_pos)
    (Eventually.of_forall fun s => (measurable_w hH c s).aestronglyMeasurable)
    hint (hF' s₀).aestronglyMeasurable
    ((ae_restrict_iff' hS).2 (Eventually.of_forall fun g hg s hs => hbd g hg s hs))
    (integrable_const _)
    (Eventually.of_forall fun g s _ => by
      have := ((hasDerivAt_id s).const_cpow (c := ((Dt g : ℝ) : ℂ)) (Or.inl (Dt_ne g))).const_mul (H g * cdet c g)
      simpa using this)
  exact key.2.differentiableAt

end GlobalTheory.CompanionTheory.RSZeta
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentiablePartialZetaIntegral
section
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate SchwartzMap Classical
open Ad3 Ad3.R

namespace GlobalTheory.CompanionTheory.RSZeta

theorem differentiable_integral_cpow_of_one_le {X : Type*} [MeasurableSpace X] (ν : Measure X) (D : X → ℝ)
    (w : X → ℂ) (hD : Measurable D) (hw : Measurable w) (h1 : ∀ᵐ x ∂ν, 1 ≤ D x)
    (hfin : ∀ σ : ℝ, 1 < σ → ∫⁻ x, ‖w x‖ₑ * ENNReal.ofReal (D x ^ σ) ∂ν < ∞) :
    Differentiable ℂ (fun s : ℂ => ∫ x, w x * ((D x : ℝ) : ℂ) ^ s ∂ν) := by
  intro s₀
  set σ : ℝ := max 2 (|s₀.re| + 3) with hσ
  have hσ2 : 2 ≤ σ := le_max_left _ _
  have hσ3 : |s₀.re| + 3 ≤ σ := le_max_right _ _
  have hmD : Measurable fun x => ((D x : ℝ) : ℂ) := Complex.measurable_ofReal.comp hD
  have hmb : Measurable fun x => ‖w x‖ * D x ^ σ := hw.norm.mul (hD.pow_const σ)
  have hbound : Integrable (fun x => ‖w x‖ * D x ^ σ) ν := by
    refine ⟨hmb.aestronglyMeasurable, ?_⟩
    refine lt_of_le_of_lt (le_of_eq ?_) (hfin σ (by linarith))
    refine lintegral_congr_ae ?_
    filter_upwards [h1] with x hx
    have hp : 0 ≤ D x ^ σ := Real.rpow_nonneg (by linarith) σ
    rw [enorm_mul, Real.enorm_of_nonneg hp, enorm_norm]
  have hre : ∀ s ∈ Metric.ball s₀ 1, s.re + 1 ≤ σ := by
    intro s hs
    have h : ‖s - s₀‖ < 1 := by simpa [dist_eq_norm] using hs
    have h2 : |(s - s₀).re| ≤ ‖s - s₀‖ := Complex.abs_re_le_norm _
    have h3 := le_abs_self (s - s₀).re
    have h4 := le_abs_self s₀.re
    simp only [Complex.sub_re] at h2 h3
    linarith
  have hnorm : ∀ x, 1 ≤ D x → ∀ s : ℂ, ‖((D x : ℝ) : ℂ) ^ s‖ = D x ^ s.re := fun x hx s =>
    Complex.norm_cpow_eq_rpow_re_of_pos (by linarith) s
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν) (x₀ := s₀)
    (F := fun s x => w x * ((D x : ℝ) : ℂ) ^ s)
    (F' := fun s x => w x * (((D x : ℝ) : ℂ) ^ s * Complex.log ((D x : ℝ) : ℂ)))
    (bound := fun x => ‖w x‖ * D x ^ σ) (Metric.ball_mem_nhds s₀ one_pos)
    (Eventually.of_forall fun s => (hw.mul (hmD.pow_const s)).aestronglyMeasurable)
    ?_ ((hw.mul ((hmD.pow_const s₀).mul (Complex.measurable_log.comp hmD))).aestronglyMeasurable)
    ?_ hbound ?_
  · exact key.2.differentiableAt
  · refine hbound.mono' (hw.mul (hmD.pow_const s₀)).aestronglyMeasurable ?_
    filter_upwards [h1] with x hx
    rw [norm_mul, hnorm x hx]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    refine Real.rpow_le_rpow_of_exponent_le hx ?_
    have := le_abs_self s₀.re
    linarith
  · filter_upwards [h1] with x hx s hs
    rw [norm_mul, norm_mul, hnorm x hx, ← Complex.ofReal_log (by linarith), Complex.norm_real,
      Real.norm_of_nonneg (Real.log_nonneg hx)]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have hpos : 0 < D x := by linarith
    have hlog : Real.log (D x) ≤ D x := (Real.log_le_sub_one_of_pos hpos).trans (by linarith)
    calc D x ^ s.re * Real.log (D x) ≤ D x ^ s.re * D x :=
          mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg hpos.le _)
      _ = D x ^ (s.re + 1) := by rw [Real.rpow_add_one hpos.ne']
      _ ≤ D x ^ σ := Real.rpow_le_rpow_of_exponent_le hx (hre s hs)
  · filter_upwards [h1] with x hx s _
    have h0 : ((D x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (by linarith)
    have := ((hasDerivAt_id s).const_cpow (c := ((D x : ℝ) : ℂ)) (Or.inl h0)).const_mul (w x)
    simpa using this

theorem differentiable_Zp (μ : Measure G2) (𝓕 : Set G2) (mK : Measure KA) (𝓓 : Set Jd) (H : G2 → ℂ)
    (Φ : (Fin 2 → 𝔸[ℚ]) → ℂ) (c : HeckeCharacter ℚ) (h3 : Ad3.R.G3) (h0 : Set0 μ 𝓕 mK 𝓓) (hH : Aut H)
    (hΦ : Φ ∈ Adele2.schwartzBruhat2 ℚ) : Differentiable ℂ (GlobalTheory.CompanionTheory.RSZeta.Zp μ 𝓕 H c Φ) := by
  have hth : Measurable (th Φ) := (h3 μ 𝓕 mK 𝓓 h0 H hH Φ hΦ 2 one_lt_two).1
  have hmA : MeasurableSet (𝓕 ∩ {g | 1 ≤ Dt g}) :=
    h0.meas.inter (measurableSet_le measurable_const measurable_Dt)
  have hw : Measurable fun g => H g * cdet c g * th Φ g :=
    (hH.cont.measurable.mul (measurable_cdet c)).mul hth
  have main := differentiable_integral_cpow_of_one_le (μ.restrict (𝓕 ∩ {g | 1 ≤ Dt g})) Dt
    (fun g => H g * cdet c g * th Φ g) measurable_Dt hw
    ((ae_restrict_mem hmA).mono fun g hg => hg.2) ?_
  · have e : GlobalTheory.CompanionTheory.RSZeta.Zp μ 𝓕 H c Φ =
        fun s : ℂ => ∫ g, (H g * cdet c g * th Φ g) * ((Dt g : ℝ) : ℂ) ^ s ∂(μ.restrict (𝓕 ∩ {g | 1 ≤ Dt g})) := by
      funext s
      simp only [Zp]
      refine integral_congr_ae (Eventually.of_forall fun g => ?_)
      simp only
      ring
    rw [e]
    exact main
  · intro σ hσ
    refine lt_of_le_of_lt ?_ (h3 μ 𝓕 mK 𝓓 h0 H hH Φ hΦ σ hσ).2.2
    refine le_trans ?_ (lintegral_mono_set (Set.inter_subset_left (t := {g | 1 ≤ Dt g})))
    refine lintegral_mono fun g => ?_
    have hc : ‖cdet c g‖ₑ = 1 := by
      rw [← ofReal_norm, norm_cdet]; simp
    rw [enorm_mul, enorm_mul, hc, mul_one]
    calc ‖H g‖ₑ * ‖th Φ g‖ₑ * ENNReal.ofReal (Dt g ^ σ)
        = (‖H g‖ₑ * ENNReal.ofReal (Dt g ^ σ)) * ‖th Φ g‖ₑ := by ring
      _ ≤ _ := by gcongr; exact enorm_tsum_le_tsum_enorm

end GlobalTheory.CompanionTheory.RSZeta
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DigitCharacterSumValues
section
noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.LFUDom

section CharSum

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

def negCharC (ψ : AddChar F Circle) : AddChar F ℂ where
  toFun x := ((ψ (-x) : Circle) : ℂ)
  map_zero_eq_one' := by simp
  map_add_eq_mul' x y := by
    rw [neg_add, AddChar.map_add_eq_mul]
    simp

theorem negCharC_apply (ψ : AddChar F Circle) (x : F) :
    negCharC ψ x = ((ψ (-x) : Circle) : ℂ) := rfl

theorem std_trivial_of_mem {ψ : AddChar F Circle} (hψ : Ad3.IsStd ψ) {x : F} (hx : x ∈ 𝒪[F]) :
    ψ x = 1 := by
  obtain ⟨hc, h1, h0⟩ := hψ
  refine isTrivialOn_addCharConductor hc h1 x ?_
  rw [h0]
  exact mem_valBall_zero_iff.2 hx

theorem std_exists_ne_one {ψ : AddChar F Circle} (hψ : Ad3.IsStd ψ) :
    ∃ x : F, (GLnLocal.uniformizer F : F) * x ∈ 𝒪[F] ∧ ψ x ≠ 1 := by
  obtain ⟨hc, h1, h0⟩ := hψ
  have hnot := not_isTrivialOn_addCharConductor_sub_one hc h1
  rw [h0] at hnot
  simp only [IsTrivialOn, not_forall] at hnot
  obtain ⟨x, hx, hne⟩ := hnot
  refine ⟨x, ?_, hne⟩
  have hϖ : (GLnLocal.uniformizer F : F) ≠ 0 := Cartan.uniformizer_ne_zero F
  have hp : (GLnLocal.uniformizer F : F) ∈ valBall F 1 := by
    rw [mem_valBall_iff_le_ord hϖ, ord_uniformizer (irreducible_uniformizer F)]
  have h := mul_mem_valBall hp hx
  rw [show (1 : ℤ) + (0 - 1) = 0 by norm_num] at h
  exact mem_valBall_zero_iff.1 h

theorem sum_negCharC_residue_eq_zero {ψ : AddChar F Circle} (hψ : Ad3.IsStd ψ) :
    ∑ x : 𝓀[F], negCharC ψ ((residueLift F x : F) * (GLnLocal.uniformizer F : F)⁻¹) = 0 := by
  have h0 : ∀ x ∈ 𝒪[F], negCharC ψ x = 1 := fun x hx => by
    rw [negCharC_apply, std_trivial_of_mem hψ (neg_mem hx)]
    simp
  have h1 : ∃ x : F, (GLnLocal.uniformizer F : F) * x ∈ 𝒪[F] ∧ negCharC ψ x ≠ 1 := by
    obtain ⟨x, hx, hne⟩ := std_exists_ne_one hψ
    refine ⟨-x, by rw [mul_neg]; exact neg_mem hx, ?_⟩
    rw [negCharC_apply, neg_neg]
    intro h
    exact hne (Circle.ext (by simpa using h))
  have h := AddChar.sum_eq_zero_of_ne_one
    (GroundTheory.Automorphic.Spherical.residueChar_ne_one (negCharC ψ) h0 h1)
  rw [← h]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [mul_comm]
  rfl

theorem digitSum_mul_zpow (j : ℕ) (c : Fin j → 𝓀[F]) (m : ℤ) :
    digitSum F j c * (GLnLocal.uniformizer F : F) ^ m =
      ∑ t : Fin j, (residueLift F (c t) : F) * (GLnLocal.uniformizer F : F) ^ (((t : ℕ) : ℤ) + m) := by
  have hϖ : (GLnLocal.uniformizer F : F) ≠ 0 := Cartan.uniformizer_ne_zero F
  rw [digitSum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [zpow_add₀ hϖ, zpow_natCast, mul_assoc]

end CharSum

theorem charsum : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle), Ad3.IsStd ψ → ∀ (j : ℕ) (m : ℤ),
  (0 ≤ m → ∑ c : Fin j → 𝓀[F], ((ψ (-(digitSum F j c) * (GLnLocal.uniformizer F : F) ^ m) : Circle) : ℂ) = (qF F : ℂ) ^ j) ∧
  (m < 0 → -m ≤ j → ∑ c : Fin j → 𝓀[F], ((ψ (-(digitSum F j c) * (GLnLocal.uniformizer F : F) ^ m) : Circle) : ℂ) = 0) := by
  intro F _ _ _ _ _ _ ψ hψ j m
  constructor
  · intro hm
    lift m to ℕ using hm
    have hterm : ∀ c : Fin j → 𝓀[F],
        ((ψ (-(digitSum F j c) * (GLnLocal.uniformizer F : F) ^ (m : ℤ)) : Circle) : ℂ) = 1 := by
      intro c
      rw [std_trivial_of_mem hψ, Circle.coe_one]
      rw [zpow_natCast]
      exact mul_mem (neg_mem (digitSum_mem j c)) (pow_mem (GLnLocal.uniformizer F).2 m)
    rw [Finset.sum_congr rfl fun c _ => hterm c]
    simp [qF, Nat.card_eq_fintype_card]
  · intro hm hj
    obtain ⟨n, hn⟩ : ∃ n : ℕ, m = -((n : ℤ) + 1) := ⟨(-m - 1).toNat, by omega⟩
    have hnj : n < j := by omega
    set G : Fin j → 𝓀[F] → ℂ := fun t x => negCharC ψ
      ((residueLift F x : F) * (GLnLocal.uniformizer F : F) ^ (((t : ℕ) : ℤ) + m)) with hG
    have key := Finset.prod_univ_sum (fun _ : Fin j => (Finset.univ : Finset 𝓀[F])) G
    rw [Fintype.piFinset_univ] at key
    have hterm : ∀ c : Fin j → 𝓀[F],
        ((ψ (-(digitSum F j c) * (GLnLocal.uniformizer F : F) ^ m) : Circle) : ℂ) =
          ∏ t, G t (c t) := by
      intro c
      rw [neg_mul, ← negCharC_apply, digitSum_mul_zpow, addChar_sum_eq_prod]
    rw [Finset.sum_congr rfl fun c _ => hterm c, ← key]
    refine Finset.prod_eq_zero (Finset.mem_univ (⟨n, hnj⟩ : Fin j)) ?_
    have hexp : (((⟨n, hnj⟩ : Fin j) : ℕ) : ℤ) + m = -1 := by
      simp only [hn]
      ring
    simp only [hG, hexp, _root_.zpow_neg_one]
    exact sum_negCharC_residue_eq_zero hψ

end GlobalTheory.CompanionTheory.LFUDom
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleComplexClassZeroOfLeadZero
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w

namespace GlobalTheory.CompanionTheory.RowInj

theorem clsZ_mem_of_leadE {R : Type} [CommRing R] (K : DCx.{w} R) (n a q : ℕ) (haq : a + q = n)
    (z : Zf K n a) (hz : leadE K a q z = 0) : clsZ K n a z ∈ Ff K n (a + 1) := by
  have hT : (Subtype.val (Subtype.val (Subtype.val z)) : (p q : ℕ) → K.X p q) ∈ K.T n :=
    Subtype.prop (Subtype.val (Subtype.val z))
  have h0 : ∀ p r, p < a → (Subtype.val (Subtype.val (Subtype.val z)) : (p q : ℕ) → K.X p q) p r = 0 :=
    fun p r hp => z.2 p r hp
  have hdv : K.dv a q ((Subtype.val (Subtype.val (Subtype.val z)) : (p q : ℕ) → K.X p q) a q) = 0 :=
    dv_lead K _ (D_zero K (Subtype.val z)) a q h0
  have hB : leadC K a q z ∈ (colH K q).B a := by
    have hz' := hz
    rw [leadE_eq] at hz'
    unfold CrystallineSemistableComparison.Cx.cls at hz'
    rw [Submodule.Quotient.mk_eq_zero] at hz'
    exact hz'
  have hL := leadC_eq K a q z hdv
  obtain ⟨v₁, W₁, hW₁, hD, hv⟩ : ∃ (v₁ : K.X a q) (W₁ : (p q : ℕ) → K.X p q),
      (∀ p r, p + r + 1 ≠ n → W₁ p r = 0) ∧ K.D W₁ = K.sgl a q v₁ ∧
      (Subtype.val (Subtype.val (Subtype.val z)) : (p q : ℕ) → K.X p q) a q - v₁ ∈ (K.col a).B q := by
    cases a with
    | zero =>
      refine ⟨0, 0, fun _ _ _ => rfl, by simp, ?_⟩
      have hb : leadC K 0 q z ∈ (⊥ : Submodule R ((colH K q).X 0)) := hB
      rw [Submodule.mem_bot, hL] at hb
      unfold CrystallineSemistableComparison.Cx.cls at hb
      rw [Submodule.Quotient.mk_eq_zero] at hb
      simpa using hb
    | succ a' =>
      have hb : leadC K (a' + 1) q z ∈ LinearMap.range ((colH K q).d a') := hB
      obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hb
      obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective
        (Submodule.comap ((K.col a').Z q).subtype ((K.col a').B q)) y
      have hw : K.dv a' q (w : K.X a' q) = 0 := w.2
      refine ⟨K.dh a' q w, K.sgl a' q w, ?_, ?_, ?_⟩
      · intro p r hpr
        apply K.sgl_ne
        by_cases hp : p = a'
        · right
          intro hr
          apply hpr
          omega
        · left
          exact hp
      · rw [DCx.D_sgl, hw, map_zero, smul_zero, add_zero]
      · rw [hL] at hy
        unfold CrystallineSemistableComparison.Cx.cls at hy
        change (colMap K a').mapH q (Submodule.Quotient.mk w) = _ at hy
        unfold CrystallineSemistableComparison.Cx.Hom.mapH at hy
        rw [Submodule.mapQ_apply, Submodule.Quotient.eq] at hy
        have h2 := Submodule.neg_mem _ hy
        rw [neg_sub] at h2
        exact h2
  obtain ⟨W, hW, hW'⟩ := lower_vert K _ hT haq h0 v₁ W₁ hW₁ hD hv
  exact lower K z W hW hW'

theorem leadE_eq_zero_of_subsingleton {R : Type} [CommRing R] (K : DCx.{w} R) (n a q : ℕ)
    (hs : Subsingleton ((K.col a).H q)) (z : Zf K n a) : leadE K a q z = 0 := by
  have h0 : leadC K a q z = 0 := Subsingleton.elim _ _
  rw [leadE_eq]
  unfold CrystallineSemistableComparison.Cx.cls
  rw [Submodule.Quotient.mk_eq_zero]
  show leadC K a q z ∈ (colH K q).B a
  rw [h0]
  exact Submodule.zero_mem _

theorem Ff_eq_zero {R : Type} [CommRing R] (K : DCx.{w} R) (a j : ℕ)
    (hK : ∀ p q, q < a → Subsingleton ((K.col p).H q)) :
    ∀ k b, j < b → b + k = a + j + 1 → ∀ x ∈ Ff K (a + j) b, x = 0 := by
  intro k
  induction k with
  | zero =>
    intro b _ hbk x hx
    have hb' : b = a + j + 1 := by omega
    subst hb'
    have hs := Ff_top_subsingleton K (a + j)
    have hxx := Subsingleton.elim (⟨x, hx⟩ : ↥(Ff K (a + j) (a + j + 1))) 0
    simpa using congrArg Subtype.val hxx
  | succ k ih =>
    intro b hb hbk x hx
    have hx' : x ∈ LinearMap.range (clsZ K (a + j) b) := hx
    obtain ⟨z, rfl⟩ := LinearMap.mem_range.mp hx'
    have hq : b + (a + j - b) = a + j := by omega
    have hz : leadE K b (a + j - b) z = 0 :=
      leadE_eq_zero_of_subsingleton K (a + j) b (a + j - b) (hK b _ (by omega)) z
    exact ih (b + 1) (by omega) (by omega) _ (clsZ_mem_of_leadE K (a + j) b (a + j - b) hq z hz)

theorem clsZ_eq_zero_of_leadE : ∀ {R : Type} [CommRing R] (K : DCx.{w} R) (a j : ℕ), (∀ p q, q < a → Subsingleton ((K.col p).H q)) →
    ∀ z : Zf K (a + j) j, leadE K j a z = 0 → clsZ K (a + j) j z = 0 := by
  intro R _ K a j hK z hz
  exact Ff_eq_zero K a j hK a (j + 1) (by omega) (by omega) _
    (clsZ_mem_of_leadE K (a + j) j a (by omega) z hz)

end GlobalTheory.CompanionTheory.RowInj
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleComplexMapLeadCompat
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w

noncomputable section

namespace GlobalTheory.CompanionTheory.CechSerre

theorem leadE_map : ∀ {R : Type} [CommRing R] (K L : DCx.{1} R) (φ : DCx.Hom K L (RingHom.id R)) (a j : ℕ) (z : Zf K (a + j) j),
    ∃ z' : Zf L (a + j) j, clsZ L (a + j) j z' = φ.tot.mapH (a + j) (clsZ K (a + j) j z) ∧
      ∃ (y : (L.col j).H a) (hy : (colH L a).d j y = 0) (y₀ : (K.col j).H a) (hy₀ : (colH K a).d j y₀ = 0),
        leadE K j a z = (colH K a).cls y₀ hy₀ ∧ leadE L j a z' = (colH L a).cls y hy ∧ y = (φ.col j).mapH a y₀ := by
  intro R _ K L φ a j z
  have hc : L.tot.d (a + j) (φ.tot.f (a + j) z.1.1) = 0 := by
    rw [φ.tot.comm, show K.tot.d (a + j) z.1.1 = 0 from z.1.2, map_zero]
  have hvan : ∀ p q, p < j → (φ.tot.f (a + j) z.1.1).1 p q = 0 := by
    intro p q hp
    change φ.f p q (z.1.1.1 p q) = 0
    rw [z.2 p q hp, map_zero]
  let z' : Zf L (a + j) j := ⟨⟨φ.tot.f (a + j) z.1.1, hc⟩, hvan⟩
  have hv : (K.col j).d a (z.1.1.1 j a) = 0 := dv_lead K z.1.1.1 (D_zero K z.1) j a z.2
  have hv' : (L.col j).d a ((φ.col j).f a (z.1.1.1 j a)) = 0 := by
    rw [(φ.col j).comm, hv, map_zero]
  have hy : leadC L j a z' = (φ.col j).mapH a (leadC K j a z) := by
    rw [leadC_eq K j a z hv, P.mapH_cls _ a _ hv hv']
    rfl
  refine ⟨z', ?_, leadC L j a z', leadC_mem L j a z', leadC K j a z, leadC_mem K j a z,
    leadE_eq K j a z, leadE_eq L j a z', hy⟩
  exact (P.mapH_cls φ.tot (a + j) z.1.1 z.1.2 hc).symm

end GlobalTheory.CompanionTheory.CechSerre
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinBasicFirstStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_basic_first : Ad3.R.B0 → Ad3.R.E1 := by
  first | exact @GlobalTheory.CompanionTheory.RSEuler.eulerProduct_integral | exact GlobalTheory.CompanionTheory.RSEuler.eulerProduct_integral | (intros; apply GlobalTheory.CompanionTheory.RSEuler.eulerProduct_integral <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinBasicSecondStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_basic_second : Ad3.R.B0 → Ad3.R.E2 := by
  first | exact @GlobalTheory.CompanionTheory.RankinEuler.e2 | exact GlobalTheory.CompanionTheory.RankinEuler.e2 | (intros; apply GlobalTheory.CompanionTheory.RankinEuler.e2 <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinBasicThirdStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_basic_third : Ad3.R.B0 → Ad3.R.E3 := by
  first | exact @GlobalTheory.CompanionTheory.RSCompact.integral_prod_finAt | exact GlobalTheory.CompanionTheory.RSCompact.integral_prod_finAt | (intros; apply GlobalTheory.CompanionTheory.RSCompact.integral_prod_finAt <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinCoefficientBlockUnfoldingStatement
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisUnfold
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_coefficient_block_unfolding : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (V : HSp D) (r s : ℕ)
    (μr : Measure (Mx D V.rank r)) (𝓕r : Set (Mx D V.rank r)) (μs : Measure (Mx D V.rank s)) (𝓕s : Set (Mx D V.rank s)),
    IsCovolOne (ratMx D V.rank r) μr 𝓕r → IsCovolOne (ratMx D V.rank s) μs 𝓕s →
    ∀ (b : Matrix (Fin r) (Fin r) D.host.E) (a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E), IsUnit a.det →
    ∀ Φ : Mx D V.rank (r + s) → ℂ, Continuous Φ →
    ∀ B : ℝ≥0, (∀ w, ∑' ξ : Matrix (Fin V.rank) (Fin (r + s)) D.host.E, ‖Φ (rat ξ + w)‖ₑ ≤ B) →
      ∫ z in 𝓕r ×ˢ 𝓕s, ∑' pq : Matrix (Fin V.rank) (Fin r) D.host.E × Matrix (Fin V.rank) (Fin s) D.host.E,
          cellTerm ψ V b a Φ pq.1 pq.2 z.1 z.2 ∂(μr.prod μs) =
        ∫ t, ψ (halfTr (Matrix.trace (HMul.hMul (rat b) (inner V t t) : Mx D r r))) *
          Φ (HMul.hMul (colJoin (-t) (0 : Mx D V.rank s)) (rat a)) ∂μr := by
  first | exact @GlobalTheory.CompanionTheory.EisUnfold.integral_cells_eq | exact GlobalTheory.CompanionTheory.EisUnfold.integral_cells_eq | (intros; apply GlobalTheory.CompanionTheory.EisUnfold.integral_cells_eq <;> assumption)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinEulerProductStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_euler_product : Ad3.R.B0 → Ad3.R.M0 → Ad3.R.F3 → Ad3.R.E0 := by
  first | exact @GlobalTheory.CompanionTheory.RankinWhittaker.whittaker_factorisation | exact GlobalTheory.CompanionTheory.RankinWhittaker.whittaker_factorisation | (intros; apply GlobalTheory.CompanionTheory.RankinWhittaker.whittaker_factorisation <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EpsteinSeriesAbsoluteConvergenceStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.epstein_series_absolute_convergence : Ad3.R.G3a := by
  first | exact @GlobalTheory.CompanionTheory.EpsteinTensorBound.g3a | exact GlobalTheory.CompanionTheory.EpsteinTensorBound.g3a | (intros; apply GlobalTheory.CompanionTheory.EpsteinTensorBound.g3a <;> assumption)
end

