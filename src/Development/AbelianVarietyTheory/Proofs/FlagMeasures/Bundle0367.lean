import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0222
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0324
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0356
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0019
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0207
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0195
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensInfTR
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0350
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0315
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0227
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0111
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0132
import Formalism.FormalDegreeBessel.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0124
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0149
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0359
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsBesPosOfBesselTied
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0219
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0351

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SiegelOneVectorMeasurableOfCompactSupport
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice GlobalTheory.GaugeEx
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.OneVecMeas

theorem sw1b2_of_cc : GlobalTheory.GaussMean.OneVectorCc → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → SW1b2 F E σ M J := by
  intro hOV F E _ _ _ _ _ σ hCM M J hJ hM β hβ d b Φ Φi Φf Φv hΦi hpure hreal hΦ
  have hOV' := hOV F E σ hCM M J hJ
  have H0 := hOV'.2 hM β hβ d b (fun _ => 0) (fun _ => 0) Φf Φv continuous_const HasCompactSupport.zero
    (fun N e _ _ => contDiff_const) hpure (fun X => by simp)
  refine ⟨H0.1, fun ψ hψ => ?_⟩
  have H1 := H0.2 ψ hψ
  refine ⟨H1.1, fun μ hμ => ⟨(H1.2 μ hμ).1, fun 𝓕 h𝓕 => ?_⟩⟩
  have H2 := (H1.2 μ hμ).2 𝓕 h𝓕
  have hfin : μ 𝓕 < ⊤ := (hOV'.1.2 μ hμ).2 𝓕 h𝓕
  refine ⟨H2.1, H2.2.1, H2.2.2.1, H2.2.2.2.1, ?_⟩
  intro μi νi μv νv hμi hνi hμv hνv
  have hCc := fun (Φ' : (Fin 1 → Fin M → AF F ⊗[F] E) → ℂ) (Φi' : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℂ) h1 h2 h3 h5 =>
    ((((hOV'.2 hM β hβ d b Φ' Φi' Φf Φv h1 h2 h3 hpure h5).2 ψ hψ).2 μ hμ).2 𝓕 h𝓕).2.2.2.2 μi νi μv νv hμi hνi hμv hνv
  refine ⟨?_, ?_, ?_⟩
  · exact GlobalTheory.T.exists_fibreFamily_hermitianLength_infiniteAdeles F E σ hCM M J μi νi (by omega) hJ hμi.1 hνi.1
  · exact ⟨fun v => Classical.choose (GlobalTheory.T.exists_fibreMeasures_localHermitianForm F E σ hCM M J hJ (by omega) v (μv v) (νv v) (hμv v).1 (hνv v).1),
      fun v => Classical.choose_spec (GlobalTheory.T.exists_fibreMeasures_localHermitianForm F E σ hCM M J hJ (by omega) v (μv v) (νv v) (hμv v).1 (hνv v).1)⟩
  intro fi fv hfi hfv

  have : IsTotallyReal F := hCM.1
  have : Countable E := (Module.finBasis ℚ E).equivFun.toEquiv.injective.countable
  set βi : Ainf F := algebraMap F (Ainf F) β with hβi
  have hβiB : βi ∈ {c : Ainf F | ∀ w, c w ≠ 0} :=
    (FibExist.isUnit_ainf_iff βi).1 ((Ne.isUnit hβ).map (algebraMap F (Ainf F)))
  have hβv : ∀ v, algebraMap F (Fv F v) β ≠ 0 := fun v => (map_ne_zero _).2 hβ
  have hBi : {c : Ainf F | IsUnit c} = {c : Ainf F | ∀ w, c w ≠ 0} :=
    Set.ext fun c => FibExist.isUnit_ainf_iff c
  have hBio : IsOpen {c : Ainf F | ∀ w, c w ≠ 0} := by
    have : {c : Ainf F | ∀ w, c w ≠ 0} = ⋂ w, {c : Ainf F | c w ≠ 0} := by ext; simp
    rw [this]
    exact isOpen_iInter_of_finite fun w => isOpen_ne.preimage (continuous_apply w)
  have hΦvR : ∀ v, Φv v = fun X => (((Φv v X).re : ℝ) : ℂ) := fun v => funext fun X =>
    Complex.ext (by simp) (by simp [(hreal v X).2])
  have hΦfR : ∀ Y, Φf Y = (((Φf Y).re : ℝ) : ℂ) ∧ 0 ≤ (Φf Y).re := by
    intro Y
    have e1 : Φf Y = ((∏ᶠ v, (Φv v (projV v Y)).re : ℝ) : ℂ) := by
      have h1 := Complex.ofRealHom.toMonoidHom.map_finprod_of_injective Complex.ofReal_injective
        (fun v => (Φv v (projV v Y)).re)
      rw [hpure.2.2 Y]
      exact (finprod_congr fun v => congrFun (hΦvR v) _).trans h1.symm
    rw [e1]
    exact ⟨by simp, by simpa using finprod_nonneg fun v => (hreal v _).1⟩

  have hdensV : ∀ (Fl : ∀ v, Fv F v → ℂ),
      (∀ v, IsContDensityOn (μv v) (fun X => qR (Fv F v) σ J (X 0)) id (νv v) {c | c ≠ 0} (Φv v) (Fl v)) →
      ∀ v, Fl v (algebraMap F (Fv F v) β) =
          ((∫ X, (Φv v X).re ∂(fv v (algebraMap F (Fv F v) β)) : ℝ) : ℂ) ∧
        ∫⁻ X, ENNReal.ofReal (Φv v X).re ∂(fv v (algebraMap F (Fv F v) β)) =
          ENNReal.ofReal (Fl v (algebraMap F (Fv F v) β)).re := by
    intro Fl hFl v
    have := (hνv v).1
    have h' : IsContDensityOn (μv v) (fun X => qR (Fv F v) σ J (X 0)) id (νv v) {c | c ≠ 0}
        (fun X => (((Φv v X).re : ℝ) : ℂ)) (Fl v) := by
      rw [← hΦvR v]; exact hFl v
    exact GlobalTheory.T.contDensity_eq_fibre_integral _ _ (μv v) _ (νv v) _ (fv v) (fun X => (Φv v X).re) (Fl v)
      (FibExist.continuous_qR (Fv F v) σ J) isOpen_ne (hfv v)
      (Complex.continuous_re.comp (hpure.1 v).1.continuous) ((hpure.1 v).2.comp_left Complex.zero_re)
      (fun X => (hreal v X).1) h' _ (hβv v)

  obtain ⟨Fi0, Fl0, -, hFl0, hmul0, -⟩ := hCc (fun _ => 0) (fun _ => 0) continuous_const HasCompactSupport.zero
    (fun N e _ _ => contDiff_const) (fun X => by simp)
  have hFlR : ∀ (Fl : ∀ v, Fv F v → ℂ),
      (∀ v, IsContDensityOn (μv v) (fun X => qR (Fv F v) σ J (X 0)) id (νv v) {c | c ≠ 0} (Φv v) (Fl v)) →
      Multipliable (fun v => Fl v (algebraMap F (Fv F v) β)) →
      Multipliable (fun v => ∫⁻ X, ENNReal.ofReal (Φv v X).re ∂(fv v (algebraMap F (Fv F v) β))) ∧
      ∏' v, ∫⁻ X, ENNReal.ofReal (Φv v X).re ∂(fv v (algebraMap F (Fv F v) β)) =
        ENNReal.ofReal (∏' v, Fl v (algebraMap F (Fv F v) β)).re := by
    intro Fl hFl hm
    have e : (fun v => ∫⁻ X, ENNReal.ofReal (Φv v X).re ∂(fv v (algebraMap F (Fv F v) β))) =
        fun v => ENNReal.ofReal (Fl v (algebraMap F (Fv F v) β)).re := funext fun v => (hdensV Fl hFl v).2
    rw [e]
    exact GlobalTheory.T.multipliable_ofReal_re_of_nonneg_real _ _ hm fun v => by
      rw [(hdensV Fl hFl v).1]
      exact ⟨by simp, by simpa using integral_nonneg fun X => (hreal v X).1⟩
  refine ⟨(hFlR Fl0 hFl0 hmul0).1, ?_⟩
  set C := ∏' v, ∫⁻ X, ENNReal.ofReal (Φv v X).re ∂(fv v (algebraMap F (Fv F v) β)) with hC
  have hCtop : C < ⊤ := by rw [(hFlR Fl0 hFl0 hmul0).2]; exact ENNReal.ofReal_lt_top

  obtain ⟨k, eK, hK⟩ := PI.VolStabS.exists_coord_tens F E
  obtain ⟨k1, e1, h1⟩ := PI.VolStabS.exists_coord_pi eK hK (Fin M)
  obtain ⟨N, eV, hV⟩ := PI.VolStabS.exists_coord_pi e1 h1 (Fin 1)
  let eA : (Fin 1 → Fin M → Ainf F ⊗[F] E) ≃+ (Fin N → ℝ) := { eV.toEquiv with map_add' := hV }
  have hsmooth : ∀ φ : (Fin N → ℝ) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ →
      ∀ (N' : ℕ) (e' : (Fin 1 → Fin M → Ainf F ⊗[F] E) ≃+ (Fin N' → ℝ)), Continuous e' → Continuous e'.symm →
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ((fun X => ((φ (eV X) : ℝ) : ℂ)) ∘ e'.symm) := by
    intro φ hφ N' e' _ he'
    let L := ((eA : (Fin 1 → Fin M → Ainf F ⊗[F] E) →+ (Fin N → ℝ)).comp
      (e'.symm : (Fin N' → ℝ) →+ (Fin 1 → Fin M → Ainf F ⊗[F] E))).toRealLinearMap
      (eV.continuous.comp he')
    have : ((fun X => ((φ (eV X) : ℝ) : ℂ)) ∘ e'.symm) = Complex.ofRealCLM ∘ φ ∘ L := rfl
    rw [this]
    exact Complex.ofRealCLM.contDiff.comp (hφ.comp L.contDiff)

  let act : (Fin 1 → Fin M → E) → HA (AF F) σ J → (Fin 1 → Fin M → AF F ⊗[F] E) :=
    fun x h => h⁻¹ • ratTup (F := F) (AF F) x
  have hact : ∀ x, Continuous (act x) := fun x => continuous_inv.smul continuous_const
  have hpF : Continuous (projFin (F := F) (E := E) (M := M) (n := 1)) :=
    continuous_pi fun a => continuous_pi fun i =>
      (GlobalTheory.GaugeGlue.continuous_map b (sndA F) GlobalTheory.GaugeGlue.continuous_sndA).comp
        ((continuous_apply i).comp (continuous_apply a))
  have hpI : Continuous (projInf (F := F) (E := E) (M := M) (n := 1)) := GlobalTheory.GaugeGlue.continuous_projInf b
  have hΦfc := GlobalTheory.T.pureFiniteAdelicTestFunction_continuous_compact F E d M 1 b Φf Φv hpure
  let T : Set (Fin 1 → Fin M → E) := {x | hE σ J (x 0) (x 0) = algebraMap F E β}
  have hS : {x : Fin 1 → Fin M → E | x 0 ≠ 0 ∧ hE σ J (x 0) (x 0) = algebraMap F E β} = T := by
    ext x
    refine ⟨fun h => h.2, fun h => ⟨fun h0 => ?_, h⟩⟩
    have : hE σ J (x 0) (x 0) = 0 := by rw [h0]; simp [hE, Formalism.UG.hform]
    exact (map_ne_zero (algebraMap F E)).2 hβ (h.symm.trans this)
  let a : T → HA (AF F) σ J → (Fin N → ℝ) := fun x h => eV (projInf (act x h))
  let w : T → HA (AF F) σ J → ℝ≥0∞ := fun x h => ENNReal.ofReal (Φf (projFin (act x h))).re
  have ha : ∀ x, Continuous (a x) := fun x => eV.continuous.comp (hpI.comp (hact x))
  have hwr : ∀ x, Continuous fun h => (Φf (projFin (act x h))).re :=
    fun x => Complex.continuous_re.comp (hΦfc.1.comp (hpF.comp (hact x)))
  have hw : ∀ x, Continuous (w x) := fun x => ENNReal.continuous_ofReal.comp (hwr x)
  let m₁ : Measure (Fin N → ℝ) := (μ 𝓕)⁻¹ • Measure.sum fun x : T => ((μ.restrict 𝓕).withDensity (w x)).map (a x)
  have hm₁ : ∀ g : (Fin N → ℝ) → ℝ≥0∞, Measurable g →
      ∫⁻ y, g y ∂m₁ = (μ 𝓕)⁻¹ * ∫⁻ h in 𝓕, ∑' x : T, g (a x h) * w x h ∂μ := by
    intro g hg
    have hts := lintegral_tsum (μ := μ.restrict 𝓕) (f := fun (x : T) h => g (a x h) * w x h)
      fun x => ((hg.comp (ha x).measurable).mul (hw x).measurable).aemeasurable
    beta_reduce at hts
    rw [lintegral_smul_measure, lintegral_sum_measure, smul_eq_mul, hts]
    congr 1
    refine tsum_congr fun x => ?_
    rw [lintegral_map hg (ha x).measurable]
    have hwd := lintegral_withDensity_eq_lintegral_mul (μ.restrict 𝓕) (hw x).measurable (hg.comp (ha x).measurable)
    simp only [Function.comp_def] at hwd
    rw [hwd]
    refine lintegral_congr fun h => ?_
    simp only [Pi.mul_apply]
    ring
  let m₂ : Measure (Fin N → ℝ) := C • (fi βi).map eV
  have hm₂ : ∀ g : (Fin N → ℝ) → ℝ≥0∞, Measurable g →
      ∫⁻ y, g y ∂m₂ = C * ∫⁻ X, g (eV X) ∂(fi βi) := by
    intro g hg
    rw [lintegral_smul_measure, lintegral_map hg eV.continuous.measurable, smul_eq_mul]

  have hfoc : IsFiniteMeasureOnCompacts m₂ := by
    refine ⟨fun K hK => ?_⟩
    obtain ⟨f, hf1, -, hfcs, -⟩ := exists_continuous_one_zero_of_isCompact hK isClosed_empty (Set.disjoint_empty K)
    have hint := (hfi.2.2 (fun X => f (eV X)) (f.continuous.comp eV.continuous) (hfcs.comp_homeomorph eV)
      (Set.subset_univ _)).1 βi hβiB
    have hle : (fi βi) (eV ⁻¹' K) ≤ ∫⁻ X, ‖f (eV X)‖ₑ ∂(fi βi) := by
      rw [← lintegral_indicator_one (hK.isClosed.measurableSet.preimage eV.continuous.measurable)]
      refine lintegral_mono fun X => ?_
      by_cases hX : X ∈ eV ⁻¹' K
      · rw [Set.indicator_of_mem hX, Pi.one_apply, hf1 hX, Pi.one_apply]; simp
      · rw [Set.indicator_of_notMem hX]; exact bot_le
    show (C • (fi βi).map eV) K < ⊤
    rw [Measure.smul_apply, Measure.map_apply eV.continuous.measurable hK.isClosed.measurableSet, smul_eq_mul]
    exact ENNReal.mul_lt_top hCtop (hle.trans_lt hint.2)

  have htest : ∀ φ : (Fin N → ℝ) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
      (∀ y, 0 ≤ φ y) → ∫⁻ y, ENNReal.ofReal (φ y) ∂m₁ = ∫⁻ y, ENNReal.ofReal (φ y) ∂m₂ := by
    intro φ hφ hφcs hφ0
    have hφc : Continuous φ := hφ.continuous
    let Φi' : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℂ := fun X => ((φ (eV X) : ℝ) : ℂ)
    let Φ' : (Fin 1 → Fin M → AF F ⊗[F] E) → ℂ := fun X => Φi' (projInf X) * Φf (projFin X)
    have hΦi'c : Continuous Φi' := Complex.continuous_ofReal.comp (hφc.comp eV.continuous)
    have hΦi'cs : HasCompactSupport Φi' := (hφcs.comp_homeomorph eV).comp_left Complex.ofReal_zero
    have hΦ'c := GlobalTheory.T.continuous_hasCompactSupport_infFin_product_testFunction F E M 1 Φ' Φi' Φf hΦi'c hΦi'cs hΦfc.1 hΦfc.2 (fun X => rfl)
    obtain ⟨Fi', Fl', hdi, hdv, hmul', hmean'⟩ := hCc Φ' Φi' hΦi'c hΦi'cs (hsmooth φ hφ) (fun X => rfl)
    rw [hBi] at hdi
    have := hνi.1
    have hFi := GlobalTheory.T.contDensity_eq_fibre_integral _ _ μi _ νi _ fi (fun X => φ (eV X)) Fi' (FibExist.continuous_qR (Ainf F) σ J)
      hBio hfi (hφc.comp eV.continuous) (hφcs.comp_homeomorph eV) (fun X => hφ0 _) hdi βi hβiB
    have hP := hFlR Fl' hdv hmul'
    let f : T → HA (AF F) σ J → ℝ := fun x h => φ (a x h) * (Φf (projFin (act x h))).re
    have hf0 : ∀ x h, 0 ≤ f x h := fun x h => mul_nonneg (hφ0 _) (hΦfR _).2
    have hfm : ∀ x, Measurable (f x) := fun x => ((hφc.comp (ha x)).mul (hwr x)).measurable
    have hΦ'f : ∀ (x : T) h, Φ' (act x h) = ((f x h : ℝ) : ℂ) := by
      intro x h
      show ((φ (eV (projInf (act x h))) : ℝ) : ℂ) * Φf (projFin (act x h)) =
        ((φ (eV (projInf (act x h))) * (Φf (projFin (act x h))).re : ℝ) : ℂ)
      conv_lhs => rw [(hΦfR (projFin (act x h))).1]
      push_cast; ring
    have hint := GlobalTheory.T.lintegral_hermitian_orbit_sum_fixed_length_lt_top F E σ hCM M J hJ β hβ Φ' hΦ'c.1 hΦ'c.2 μ 𝓕 hμ h𝓕
    have hint' : ∫⁻ h in 𝓕, ∑' x : T, ‖((f x h : ℝ) : ℂ)‖ₑ ∂μ < ⊤ := by
      refine lt_of_eq_of_lt ?_ hint
      refine lintegral_congr fun h => tsum_congr fun x => ?_
      rw [← hΦ'f]
    have hL := GlobalTheory.T.meanL_tsum_ofReal_eq_ofReal_re_meanC (HA (AF F) σ J) μ 𝓕 T f hfm hf0 hfin hint'
    rw [hm₁ (fun y => ENNReal.ofReal (φ y)) (ENNReal.measurable_ofReal.comp hφc.measurable),
      hm₂ (fun y => ENNReal.ofReal (φ y)) (ENNReal.measurable_ofReal.comp hφc.measurable)]
    have e1 : (μ 𝓕)⁻¹ * ∫⁻ h in 𝓕, ∑' x : T, ENNReal.ofReal (φ (a x h)) * w x h ∂μ =
        meanL μ 𝓕 (fun h => ∑' x : T, ENNReal.ofReal (f x h)) := by
      unfold meanL; congr 1; refine lintegral_congr fun h => tsum_congr fun x => ?_
      simp only [f, w]; rw [ENNReal.ofReal_mul (hφ0 _)]
    rw [e1, hL]
    have e2 : meanC μ 𝓕 (fun h => ∑' x : T, ((f x h : ℝ) : ℂ)) =
        Fi' βi * ∏' v, Fl' v (algebraMap F (Fv F v) β) := by
      rw [← hmean']; unfold thSum; congr 1; funext h; exact tsum_congr fun x => (hΦ'f x h).symm
    rw [e2, hP.2, hFi.2, hFi.1]
    have hr : 0 ≤ ∫ X, φ (eV X) ∂(fi βi) := integral_nonneg fun X => hφ0 _
    simp only [Complex.re_ofReal_mul, Complex.ofReal_re]
    rw [ENNReal.ofReal_mul hr, mul_comm]
  have := hfoc
  have hm : m₁ = m₂ := GlobalTheory.T.measure_eq_of_lintegral_smooth_eq' N m₁ m₂ htest
  rw [hS]
  calc meanL μ 𝓕 (fun h => ∑' x : T, Φ (h⁻¹ • ratTup (F := F) (AF F) (x : Fin 1 → Fin M → E)))
      = ∫⁻ y, Φi (eV.symm y) ∂m₁ := by
        rw [hm₁ (fun y => Φi (eV.symm y)) (hΦi.comp eV.symm.continuous.measurable)]
        unfold meanL; congr 1; refine lintegral_congr fun h => tsum_congr fun x => ?_
        simp only [a, w, act, hΦ, Homeomorph.symm_apply_apply]
    _ = ∫⁻ y, Φi (eV.symm y) ∂m₂ := by rw [hm]
    _ = (∫⁻ X, Φi X ∂(fi βi)) * C := by
        rw [hm₂ (fun y => Φi (eV.symm y)) (hΦi.comp eV.symm.continuous.measurable), mul_comm]
        simp only [Homeomorph.symm_apply_apply]

end GlobalTheory.OneVecMeas
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SobolevInequalityAtIdentityBesselModelUnitaryGro
section
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace ContDiff ENNReal

namespace GlobalTheory.SobAtOne

theorem ofReal_list_sum {α : Type*} (S : List α) (g : α → ℝ) (hg : ∀ a, 0 ≤ g a) :
    ENNReal.ofReal (S.map g).sum = (S.map fun a => ENNReal.ofReal (g a)).sum := by
  induction S with
  | nil => simp
  | cons a S ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ENNReal.ofReal_add (hg a) (List.sum_nonneg fun x hx => by
      obtain ⟨b, -, rfl⟩ := List.mem_map.1 hx; exact hg b), ih]

theorem sobolev_at_one_G : ∀ (k r : ℕ) (μG : Measure (Mt k r)), IsHaarOn (GG k r) μG → ∃ (C : ℝ)
    (Ws : List (List (Mat k r))) (K₀ : Set (Mt k r)), IsCompact K₀ ∧ (∀ ws ∈ Ws, ∀ X ∈ ws, InLieHpk k r X) ∧
    ∀ (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (f : Mat k r → B),
      SmoothOnH (Hpk k r) f → ‖f 1‖ ^ 2 ≤ C * (Ws.map fun ws =>
        ∫ x in K₀, ‖rdWord ws f (Matrix.of x)‖ ^ 2 ∂μG).sum := by
  intro k r μG hμ
  obtain ⟨-, -, -, ε, -, P, hPd, hPJ⟩ := hpkFacts k r
  have hPu : IsUnit P := (Matrix.isUnit_iff_isUnit_det P).2 hPd
  have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hPd
  have hPP' : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hPd
  obtain ⟨S, C, Q, hQ, hS, hC, hsob⟩ := GlobalTheory.T.sobolev_valueAtOne_fixedCompact_diagSignUnitary (2 * r + k + 1) ε
  obtain ⟨c, hc, hB⟩ := GlobalTheory.T.besselUnitary_haar_transport_diagonal k r μG ε P hμ hPd hPJ
  let cj : Mat k r → Mat k r := fun Y => P⁻¹ * Y * P
  have hcjc : Continuous cj := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  let ψ : Formalism.REAL.UJ ε → Mt k r := fun y => Matrix.of.symm (cj (umat y))
  have hψc : Continuous ψ := hcjc.comp (Units.continuous_val.comp continuous_subtype_val)
  have hmemG : ∀ g : Mat k r, Formalism.REAL.inUJ ε g → cj g ∈ GG k r := by
    intro g hg
    show cj g ∈ UH (Hpk k r)
    rw [uHConj _ ε (Hpk k r) P hPd hPJ]
    have e : P * cj g * P⁻¹ = g := by
      simp only [cj, ← Matrix.mul_assoc, hPP, Matrix.one_mul]
      rw [Matrix.mul_assoc, hPP, Matrix.mul_one]
    rw [e]; exact hg
  have hlie : ∀ X, Formalism.REAL.inG ε X → InLieHpk k r (cj X) := by
    intro X hX
    have hX' : Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0 := hX
    have e1 : (P⁻¹)ᴴ * Pᴴ = 1 := by rw [← conjTranspose_mul, hPP, conjTranspose_one]
    show (P⁻¹ * X * P)ᴴ * Hpk k r + Hpk k r * (P⁻¹ * X * P) = 0
    rw [← hPJ]
    calc (P⁻¹ * X * P)ᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) + Pᴴ * Formalism.REAL.Jm ε * P * (P⁻¹ * X * P)
        = Pᴴ * (Xᴴ * ((P⁻¹)ᴴ * Pᴴ) * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * (P * P⁻¹) * X) * P := by
          simp only [conjTranspose_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      _ = 0 := by rw [e1, hPP, Matrix.mul_one, Matrix.mul_one, hX', Matrix.mul_zero, Matrix.zero_mul]
  have hwm : ∀ l : List (Mat k r), (∀ Y ∈ l, Formalism.REAL.inG ε Y) → ∀ Y ∈ l.map cj, InLieHpk k r Y := by
    intro l hl Y hY
    obtain ⟨Z, hZ, rfl⟩ := List.mem_map.1 hY
    exact hlie Z (hl Z hZ)
  have hK₀ : IsCompact (ψ '' Q) := hQ.image hψc
  have hK₀G : ∀ x ∈ ψ '' Q, Matrix.of x ∈ GG k r := by
    rintro _ ⟨y, -, rfl⟩
    simpa [ψ] using hmemG _ y.2
  have hfin : IsFiniteMeasureOnCompacts μG := by
    obtain ⟨hG, -⟩ := closedSub_groups k r (bvec (wI k r (Fin.last k))) (fun i hi => by
      simp only [bvec, wI]
      rw [Pi.single_apply, if_neg]
      intro h; rw [h] at hi; simp at hi) (by
      have h : herm (Hpk k r) (bvec (wI k r (Fin.last k))) (bvec (wI k r (Fin.last k))) =
          Hpk k r (wI k r (Fin.last k)) (wI k r (Fin.last k)) := by
        simp [herm, bvec, Matrix.mulVec, dotProduct, Pi.single_apply]
      rw [Tz, h]
      simp [Hpk, wI])
    exact ⟨fun K hK => (haarOn_locFinite_openPos k r (GG k r) μG hG hμ).1 K hK⟩
  refine ⟨C * c.toReal, S.map (List.map cj), ψ '' Q, hK₀, ?_, ?_⟩
  · intro ws hws X hX
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hws
    exact hwm l (hS l hl) X hX
  intro B _ _ _ f hf
  have hword : ∀ l : List (Mat k r), (∀ Y ∈ l, InLieHpk k r Y) → SmoothOnH (Hpk k r) (rdWord l f) := by
    intro l
    induction l with
    | nil => intro _; exact hf
    | cons X l ih =>
      intro hl
      exact (GlobalTheory.T.rightDerivative_smooth_on_indefinite_unitary_group _ (Hpk k r) X B (rdWord l f) (hl X List.mem_cons_self)
        (ih fun Y hY => hl Y (List.mem_cons_of_mem _ hY))).2.1
  have hcont : ∀ l : List (Mat k r), (∀ Y ∈ l, Formalism.REAL.inG ε Y) →
      ContinuousOn (rdWord (l.map cj) f) (GG k r) := fun l hl =>
    (GlobalTheory.T.rightDerivative_smooth_on_indefinite_unitary_group _ (Hpk k r) 0 B _ (by simp) (hword _ (hwm l hl))).1
  have hof : Continuous (fun x : Mt k r => (Matrix.of x : Mat k r)) := continuous_id
  have hI : ∀ l : List (Mat k r), (∀ Y ∈ l, Formalism.REAL.inG ε Y) →
      ContinuousOn (fun x : Mt k r => ‖rdWord (l.map cj) f (Matrix.of x)‖ ^ 2) (ψ '' Q) := fun l hl =>
    (((hcont l hl).comp hof.continuousOn fun x hx => hK₀G x hx).norm).pow 2
  have hnn : 0 ≤ C * c.toReal * ((S.map (List.map cj)).map fun ws =>
      ∫ x in ψ '' Q, ‖rdWord ws f (Matrix.of x)‖ ^ 2 ∂μG).sum :=
    mul_nonneg (mul_nonneg hC ENNReal.toReal_nonneg) (List.sum_nonneg fun x hx => by
      obtain ⟨b, -, rfl⟩ := List.mem_map.1 hx; exact integral_nonneg fun _ => by positivity)
  by_cases h0 : f 1 = 0
  · rw [h0, norm_zero]; simpa using hnn
  haveI : Nontrivial B := ⟨⟨f 1, 0, h0⟩⟩
  obtain ⟨ℓ, hℓ1, hℓ⟩ := exists_dual_vector' ℂ (f 1)
  let F : List (Mat k r) → Mat k r → ℂ := fun l g => ℓ (rdWord (l.map cj) f (cj g))
  have hFc : ∀ l : List (Mat k r), (∀ Y ∈ l, Formalism.REAL.inG ε Y) → ContinuousOn (F l) (UJset ε) := fun l hl =>
    ℓ.continuous.comp_continuousOn ((hcont l hl).comp hcjc.continuousOn fun g hg => hmemG g hg)
  have hFd : ∀ l : List (Mat k r), (∀ Y ∈ l, Formalism.REAL.inG ε Y) → ∀ X, Formalism.REAL.inG ε X →
      ∀ g ∈ UJset ε, HasDerivAt (fun t : ℝ => F l (g * NormedSpace.exp ((t : ℂ) • X))) (F (X :: l) g) 0 := by
    intro l hl X hX g hg
    have hA := (GlobalTheory.T.rightDerivative_smooth_on_indefinite_unitary_group _ (Hpk k r) (cj X) B (rdWord (l.map cj) f) (hlie X hX) (hword _ (hwm l hl))).2.2
      (cj g) (hmemG g hg)
    have h2 := (ℓ.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hA
    have e : ∀ t : ℝ, cj (g * NormedSpace.exp ((t : ℂ) • X)) = cj g * NormedSpace.exp ((t : ℂ) • cj X) := by
      intro t
      have e2 : (t : ℂ) • cj X = P⁻¹ * ((t : ℂ) • X) * P := by
        simp only [cj, Matrix.mul_smul, Matrix.smul_mul]
      rw [e2, Matrix.exp_conj' P _ hPu]
      simp only [cj, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc P P⁻¹, hPP, Matrix.one_mul]
    have e3 : (fun t : ℝ => F l (g * NormedSpace.exp ((t : ℂ) • X))) = (ℓ.restrictScalars ℝ) ∘
        (fun t : ℝ => rdWord (l.map cj) f (cj g * NormedSpace.exp ((t : ℂ) • cj X))) := by
      funext t; simp only [F, Function.comp_apply, e]; rfl
    rw [e3]; exact h2
  have key := hsob F hFc hFd
  have hF1 : ‖F [] 1‖ = ‖f 1‖ := by
    have : cj 1 = 1 := by simp [cj, hPP']
    simp only [F, List.map_nil, this]
    show ‖ℓ (f 1)‖ = ‖f 1‖
    rw [hℓ]; simp
  rw [hF1] at key
  have hstep : ∀ l ∈ S, ∫⁻ y in Q, ENNReal.ofReal (‖F l (umat y)‖ ^ 2) ∂(Formalism.REAL.muG ε) ≤
      c * ENNReal.ofReal (∫ x in ψ '' Q, ‖rdWord (l.map cj) f (Matrix.of x)‖ ^ 2 ∂μG) := by
    intro l hlS
    have hl := hS l hlS
    classical
    set φ : Mt k r → ℝ≥0∞ := (ψ '' Q).indicator
      (fun x => ENNReal.ofReal (‖rdWord (l.map cj) f (Matrix.of x)‖ ^ 2)) with hφ
    have hφm : Measurable φ := by
      have := ContinuousOn.measurable_piecewise (f := fun x : Mt k r =>
        ENNReal.ofReal (‖rdWord (l.map cj) f (Matrix.of x)‖ ^ 2)) (g := 0)
        (ENNReal.continuous_ofReal.comp_continuousOn (hI l hl)) continuousOn_const hK₀.isClosed.measurableSet
      rwa [Set.piecewise_eq_indicator] at this
    have hint : IntegrableOn (fun x : Mt k r => ‖rdWord (l.map cj) f (Matrix.of x)‖ ^ 2) (ψ '' Q) μG :=
      (hI l hl).integrableOn_compact hK₀
    rw [ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun _ => by positivity),
      ← lintegral_indicator hK₀.isClosed.measurableSet, ← hφ, ← hB φ hφm]
    refine le_trans ?_ (setLIntegral_le_lintegral Q _)
    refine setLIntegral_mono (hφm.comp hψc.measurable) fun y hy => ?_
    have hψy : ψ y ∈ ψ '' Q := ⟨y, hy, rfl⟩
    have hφy : φ (ψ y) = ENNReal.ofReal (‖rdWord (l.map cj) f (Matrix.of (ψ y))‖ ^ 2) := by
      rw [hφ]; exact Set.indicator_of_mem hψy _
    show _ ≤ φ (ψ y)
    rw [hφy]
    refine ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) ?_ 2)
    have : (Matrix.of (ψ y) : Mat k r) = cj (umat y) := by simp [ψ]
    rw [this]
    refine (ℓ.le_opNorm _).trans ?_
    rw [hℓ1, one_mul]
  have hsum := List.sum_le_sum hstep
  rw [List.sum_map_mul_left, ← ofReal_list_sum S _ (fun l => integral_nonneg fun _ => by positivity)] at hsum
  have htot : ENNReal.ofReal (‖f 1‖ ^ 2) ≤ ENNReal.ofReal C * (c * ENNReal.ofReal
      ((S.map fun l => ∫ x in ψ '' Q, ‖rdWord (l.map cj) f (Matrix.of x)‖ ^ 2 ∂μG).sum)) := key.trans (by gcongr)
  conv_rhs at htot => rw [← ENNReal.ofReal_toReal hc]
  rw [← ENNReal.ofReal_mul ENNReal.toReal_nonneg, ← ENNReal.ofReal_mul hC, ← mul_assoc] at htot
  rw [List.map_map] at hnn ⊢
  exact (ENNReal.ofReal_le_ofReal_iff hnn).1 htot

end GlobalTheory.SobAtOne

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ThetaKernelInvariance
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Per MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.IndefiniteRowSideFullHecke.BesselData (hA vecA actV)
open scoped TensorProduct

namespace GlobalTheory.Per.ThetaAut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem actHom_tPt {L A : HSp D} (hr : L.rank ≤ A.rank) (c : D.host.E) (γ : GA D A) (a : Fin A.rank → AE D) :
    actHom L A 1 γ (tPt L A c a) = tPt L A c ((Formalism.L2.Theta.mt A γ).mulVec a) := by
  have h1 : cM (1 : Matrix (Fin L.rank) (Fin L.rank) (AE D)) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  unfold actHom
  rw [if_pos hr, BesselCompare.mt_one, h1, Matrix.one_mul]
  ext i k
  simp only [Matrix.mul_apply, Matrix.transpose_apply, tPt, Matrix.of_apply, Matrix.mulVec, dotProduct, Finset.mul_sum,
    ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem heis_at_zero (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (u : WA V W) (f : WA V W → ℂ) :
    Heisenberg₂ ψ V W u f 0 = f u := by
  simp only [Heisenberg₂, symplH_zero_left, AddChar.map_zero_eq_one, one_mul, zero_add]

variable {X : ThetaX D} {T : ThetaTied D X}

theorem exists_heis (Wl : WeilTied D X T) {V W : HSp D} (hne : V.rank ≠ W.rank) (u : WA V W) (Φ : X.Sch V W) :
    ∃ Φ', Wl.evS V W Φ' = Heisenberg₂ Wl.ψ V W u (Wl.evS V W Φ) := by
  have h1 : Wl.evS V W Φ ∈ {f | IsThetaFun Wl.ψ V W f} := by
    rw [← Wl.evS_range V W hne]; exact ⟨Φ, rfl⟩
  have h2 : Heisenberg₂ Wl.ψ V W u (Wl.evS V W Φ) ∈ Set.range (Wl.evS V W) := by
    rw [Wl.evS_range V W hne]; exact GlobalTheory.Mem.ThetaClosed.isThetaFun_heis Wl.ψ_std h1 u
  exact h2

theorem isThetaFun_jacOp (Wl : WeilTied D X T) {L A : HSp D} (hne : L.rank ≠ A.rank) (c : D.host.E)
    (a : Fin A.rank → AE D) (t : AE D) (Φ : X.Sch L A) :
    IsThetaFun Wl.ψ L A (jacOp Wl.ψ L A c a t (Wl.evS L A Φ)) := by
  obtain ⟨Φ', h⟩ := exists_heis Wl hne (tPt L A c a) Φ
  have h2 : jacOp Wl.ψ L A c a t (Wl.evS L A Φ) ∈ Set.range (Wl.evS L A) :=
    ⟨Wl.ψ (cenCo L c t) • Φ', by rw [map_smul, h]; rfl⟩
  rw [Wl.evS_range L A hne] at h2
  exact h2

theorem theta_aut : ∀ (D : D7) (X : ThetaX D) (T : ThetaTied D X) (Wl : WeilTied D X T) (L A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : FJDat L A B ι), 1 < A.rank → ∀ (Φ : X.Sch L A) (g : GA D A), ∀ n ∈ d.N, (∀ γ ∈ d.N, γ ∈ GQ B → d.theta Wl.ψ (omZ Wl L A Φ) (γ * n) g = d.theta Wl.ψ (omZ Wl L A Φ) n g) ∧ ∀ γ ∈ GQ A, ∀ δ, EmbRel B A ι δ γ → d.theta Wl.ψ (omZ Wl L A Φ) (δ * n * δ⁻¹) (γ * g) = d.theta Wl.ψ (omZ Wl L A Φ) n g := by
  intro D X T Wl L A B ι d hA1 Φ g n hn
  have hL : L.rank = 1 := d.line.rank_one
  have hlt : L.rank < A.rank := hL ▸ hA1
  obtain ⟨hrat, -, -, hconj⟩ := GlobalTheory.T.theta_unipotent_conjugation D L A B ι d
  refine ⟨fun γ hγ hq => ?_, fun γ hγ δ hδ => ?_⟩
  · obtain ⟨ha, ht, -⟩ := GlobalTheory.T.theta_unipotent_action_cocycle D L A B ι d γ hγ n hn
    have h1 := ((hrat Wl.ψ Wl.ψ_std.1).1 γ hq).2 _
      (isThetaFun_jacOp Wl hlt.ne d.c (d.aCo n) (d.tCo n) (Wl.om L A X.etaT⁻¹ (X.etaT ^ A.rank) (1, g) Φ))
    unfold FJDat.theta FJDat.jac at *
    rw [ha, ht, ← jacOp_mul Wl.ψ hlt.le]
    exact h1
  · obtain ⟨-, ha, ht, -⟩ := hconj δ γ hδ n hn
    rw [d.theta_eq, d.theta_eq, ha, ht, ← actHom_tPt hlt.le]
    congr 1
    obtain ⟨Φ', h⟩ := exists_heis Wl hlt.ne (tPt L A d.c (d.aCo n)) (Wl.om L A X.etaT⁻¹ (X.etaT ^ A.rank) (1, g) Φ)
    have h1 := Wl.om_heis L A _ _ hlt.ne (resEta_line T hL) (resEta_pow T _) 1 γ _ _ _ h
    have h2 := Wl.om_aut L A _ _ hlt.ne (resEta_line T hL) (resEta_pow T _) 1 (one_mem _) γ hγ Φ'
    rw [h1, h, heis_at_zero, heis_at_zero, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul] at h2
    exact h2

end GlobalTheory.Per.ThetaAut
end

