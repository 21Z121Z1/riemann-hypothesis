import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1796
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1859
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1738
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1831
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFourierTransformSurjectiveIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1760
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1849
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1833
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureUAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1830
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1845
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1850
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairTestVectorExpansion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenCompactLevelOfStandardCongruenceLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1851
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarAdelicIntegralFormula
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeylFour
open scoped GlobalTheory.VacAny
noncomputable section

namespace GlobalTheory.WeylMeas

open scoped ENNReal

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem exists_meas : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → (∀ᶠ v in cofinite, PsiUnr ψ v) →
    (∀ v : Pl F, ∃ x, psiLoc ψ v x ≠ 1) → ∀ (κ : Type) [Fintype κ],
    ∃ μ : Measure (κ → AF F), μ.IsAddRightInvariant ∧
      ∀ (g : (κ → mixedEmbedding.mixedSpace F) → ℂ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ), Continuous g →
        Integrable g (measI F κ) → (∀ v, φ v ∈ SB (κ → Fv F v)) → (∀ᶠ v in cofinite, φ v = GlobalTheory.SympChange.indO v) →
        Integrable (fun x => g (fun i => evI F (x i)) * ∏ᶠ v, φ v (fun i => evFin F v (x i))) μ ∧
        ∫ x, g (fun i => evI F (x i)) * ∏ᶠ v, φ v (fun i => evFin F v (x i)) ∂μ =
          (∫ z, g z ∂(measI F κ)) * ∏ᶠ v, ∫ z, φ v z ∂(Measure.pi fun _ : κ => measV ψ v) := by
  intro F _ _ ψ hψ hunr hne κ _
  classical
  haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  haveI hB : ∀ v : Pl F, BorelSpace (Fv F v) := fun v => ⟨rfl⟩
  haveI hSC : ∀ v : Pl F, SecondCountableTopology (Fv F v) := fun v => GlobalTheory.SplitWeil.secondCountable _
  haveI hH : ∀ v : Pl F, (measV ψ v).IsAddHaarMeasure := fun v => (isSelfDualFor_measV ψ hψ.1 v (hne v)).1
  haveI : (measI F κ).IsAddHaarMeasure := measI_isAddHaar F κ
  have hOint : ∀ v : Pl F, (v.adicCompletionIntegers F : Set (Fv F v)) =
      ((ValuativeRel.valuation (Fv F v)).integer : Set (Fv F v)) := fun v => by
    ext x; exact (GlobalTheory.WeylFour.IndOSelf.mem_int_iff x).symm
  have hOc : ∀ v : Pl F, IsCompact (v.adicCompletionIntegers F : Set (Fv F v)) := fun v =>
    (hOint v) ▸ GlobalTheory.SplitWeil.isCompact_int _
  have hOo : ∀ v : Pl F, IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) := fun v =>
    (hOint v) ▸ GlobalTheory.SplitWeil.isOpen_int _
  have hOpi : ∀ v : Pl F, {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} =
      Set.univ.pi fun _ => (v.adicCompletionIntegers F : Set (Fv F v)) := fun v => by
    ext x; simp
  have hOm : ∀ v : Pl F, MeasurableSet {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} := fun v => by
    rw [hOpi v]; exact MeasurableSet.univ_pi fun _ => (hOo v).measurableSet
  set c : Pl F → ℝ≥0∞ := fun v =>
    (Measure.pi fun _ : κ => measV ψ v) {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} with hcdef
  have hcpi : ∀ v, c v = ∏ _i : κ, measV ψ v (v.adicCompletionIntegers F : Set (Fv F v)) := fun v => by
    simp only [c]; rw [hOpi v, Measure.pi_pi]
  have hc0 : ∀ v, c v ≠ 0 := fun v => by
    rw [hcpi v]
    exact Finset.prod_ne_zero_iff.2 fun _ _ =>
      ((hOo v).measure_pos (measV ψ v) ⟨0, (v.adicCompletionIntegers F).zero_mem⟩).ne'
  have hct : ∀ v, c v ≠ ⊤ := fun v => by
    rw [hcpi v]
    exact ENNReal.prod_ne_top fun _ _ => (hOc v).measure_lt_top.ne
  have hc1 : ∀ v, PsiUnr ψ v → c v = 1 := fun v hv => by
    have h1 := (GlobalTheory.WeylFour.IndOSelf.isUnitVol_measV ψ v hv).2
    rw [← hOint v] at h1
    rw [hcpi v, h1, Finset.prod_const_one]
  set μv : ∀ v : Pl F, Measure (κ → Fv F v) := fun v => (c v)⁻¹ • Measure.pi fun _ : κ => measV ψ v with hμvdef
  haveI hμvH : ∀ v, (μv v).IsAddHaarMeasure := fun v =>
    Measure.IsAddHaarMeasure.smul _ (ENNReal.inv_ne_zero.2 (hct v)) (ENNReal.inv_ne_top.2 (hc0 v))
  have hμv1 : ∀ v, μv v {x | ∀ i, x i ∈ v.adicCompletionIntegers F} = 1 := fun v => by
    simp only [μv]
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.inv_mul_cancel (hc0 v) (hct v)
  have hpi : ∀ v, (Measure.pi fun _ : κ => measV ψ v) = c v • μv v := fun v => by
    simp only [μv, smul_smul, ENNReal.mul_inv_cancel (hc0 v) (hct v), one_smul]
  obtain ⟨c₀, hc₀, hform⟩ := GlobalTheory.AdelicHaarPure.integral_pure_haar F κ (Measure.addHaar : Measure (κ → AF F))
    (measI F κ) μv hμv1

  have hind1 : ∀ v, ∫ x, GlobalTheory.RatWeilOp.ind κ v x ∂(μv v) = 1 := fun v => by
    have := integral_indicator_const (μ := μv v) (1 : ℂ) (hOm v)
    simpa [GlobalTheory.RatWeilOp.ind, Measure.real, Pi.one_def, hμv1 v] using this

  let b : ContDiffBump (0 : κ → mixedEmbedding.mixedSpace F) := ⟨1, 2, one_pos, one_lt_two⟩
  have hbcs : HasCompactSupport (fun z => b z) := b.hasCompactSupport
  have hf₀c : Continuous (fun z => ((b z : ℝ) : ℂ)) := Complex.continuous_ofReal.comp b.continuous
  have hf₀cs : HasCompactSupport (fun z => ((b z : ℝ) : ℂ)) := hbcs.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  have hf₀i : Integrable (fun z => ((b z : ℝ) : ℂ)) (measI F κ) := hf₀c.integrable_of_hasCompactSupport hf₀cs
  have hBpos : 0 < ∫ z, b z ∂(measI F κ) :=
    b.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := measI F κ) (x := 0) hbcs (fun z => b.nonneg)
      (by rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)]; exact one_ne_zero)
  have hfam0 : GlobalTheory.RatWeilOp.IsFam (fun v : Pl F => GlobalTheory.RatWeilOp.ind κ v) :=
    ⟨fun v => GlobalTheory.WeylFour.IndOSelf.indO_mem_SB v κ, Filter.Eventually.of_forall fun v => rfl⟩
  obtain ⟨-, h0⟩ := hform (fun z => ((b z : ℝ) : ℂ)) _ hf₀c hf₀i hfam0
  rw [finprod_congr hind1, finprod_one, mul_one, integral_complex_ofReal] at h0
  set H : (κ → AF F) → ℂ := fun x => ((b (fun i => evI F (x i)) : ℝ) : ℂ) *
    ∏ᶠ v, GlobalTheory.RatWeilOp.ind κ v (fun i => evFin F v (x i)) with hHdef
  have key : ∀ z w : ℂ, (z.im = 0 ∧ 0 ≤ z.re) → (w.im = 0 ∧ 0 ≤ w.re) → ((z * w).im = 0 ∧ 0 ≤ (z * w).re) := by
    rintro z w ⟨h1, h2⟩ ⟨h3, h4⟩
    refine ⟨by rw [Complex.mul_im, h1, h3]; simp, by rw [Complex.mul_re, h1, h3]; simpa using mul_nonneg h2 h4⟩
  have hP : ∀ x, (H x).im = 0 ∧ 0 ≤ (H x).re := by
    intro x
    refine key _ _ ⟨by simp, by simpa using b.nonneg⟩ ?_
    refine finprod_induction (fun z : ℂ => z.im = 0 ∧ 0 ≤ z.re) ⟨by simp, by simp⟩ key (fun v => ?_)
    by_cases h : (fun i => evFin F v (x i)) ∈ {y : κ → Fv F v | ∀ i, y i ∈ v.adicCompletionIntegers F}
    · simp [GlobalTheory.RatWeilOp.ind, Set.indicator_of_mem h]
    · simp [GlobalTheory.RatWeilOp.ind, Set.indicator_of_notMem h]
  have hHr : H = fun x => (((H x).re : ℝ) : ℂ) := funext fun x => Complex.ext (by simp) (by simp [(hP x).1])
  have hL : ∫ x, H x ∂(Measure.addHaar : Measure (κ → AF F)) =
      ((∫ x, (H x).re ∂(Measure.addHaar : Measure (κ → AF F)) : ℝ) : ℂ) := by
    conv_lhs => rw [hHr]
    exact integral_complex_ofReal
  have hLnn : 0 ≤ ∫ x, (H x).re ∂(Measure.addHaar : Measure (κ → AF F)) := integral_nonneg fun x => (hP x).2
  set L := ∫ x, (H x).re ∂(Measure.addHaar : Measure (κ → AF F)) with hLdef
  set B := ∫ z, b z ∂(measI F κ) with hBdef
  have hc₀eq : c₀ = ((L / B : ℝ) : ℂ) := by
    have hB0 : (B : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hBpos.ne'
    rw [Complex.ofReal_div, eq_div_iff hB0, ← hL, ← h0]
  set t := L / B with htdef
  have ht0 : t ≠ 0 := fun h => hc₀ (by rw [hc₀eq, h, Complex.ofReal_zero])
  have htpos : 0 < t := lt_of_le_of_ne (div_nonneg hLnn hBpos.le) (Ne.symm ht0)

  obtain ⟨T, hT⟩ : ∃ T : Finset (Pl F), ∀ v ∉ T, PsiUnr ψ v :=
    ⟨(Filter.eventually_cofinite.1 hunr).toFinset, fun v hv => by simpa using hv⟩
  set Cr : ℝ := ∏ v ∈ T, (c v).toReal with hCrdef
  have hCr : 0 ≤ Cr := Finset.prod_nonneg fun v _ => ENNReal.toReal_nonneg
  refine ⟨ENNReal.ofReal (Cr / t) • Measure.addHaar, inferInstance, fun g φ hgc hgi hSB hev => ?_⟩
  have hfam : GlobalTheory.RatWeilOp.IsFam φ := ⟨hSB, hev⟩
  obtain ⟨hI, hE⟩ := hform g φ hgc hgi hfam
  refine ⟨hI.smul_measure ENNReal.ofReal_ne_top, ?_⟩
  have hloc : ∀ v, ∫ z, φ v z ∂(Measure.pi fun _ : κ => measV ψ v) = ((c v).toReal : ℂ) * ∫ z, φ v z ∂(μv v) :=
    fun v => by rw [hpi v, integral_smul_measure, Complex.real_smul]
  have hsub : Function.mulSupport (fun v => ((c v).toReal : ℂ)) ⊆ (T : Set (Pl F)) := fun v hv => by
    by_contra h
    exact hv (by show ((c v).toReal : ℂ) = 1; rw [hc1 v (hT v h)]; simp)
  have hs2 : (Function.mulSupport fun v => ∫ z, φ v z ∂(μv v)).Finite :=
    (Filter.eventually_cofinite.1 hev).subset fun v hv h => hv (by
      show ∫ z, φ v z ∂(μv v) = 1
      rw [h]; exact hind1 v)
  have hCprod : ∏ᶠ v, ((c v).toReal : ℂ) = (Cr : ℂ) := by
    rw [finprod_eq_prod_of_mulSupport_subset _ hsub, hCrdef, Complex.ofReal_prod]
  rw [integral_smul_measure, hE, ENNReal.toReal_ofReal (div_nonneg hCr htpos.le), hc₀eq, finprod_congr hloc,
    finprod_mul_distrib (T.finite_toSet.subset hsub) hs2, hCprod, Complex.real_smul]
  have ht0' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht0
  rw [Complex.ofReal_div]
  field_simp

end GlobalTheory.WeylMeas

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelCurvePhaseEqOfCloseStatement
section
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_level_curvePhase_eq_of_close : ∀ {D : D7} (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ →
  ∀ {a d : ℕ} (x : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y : Formalism.MainNotions.StandardLatticesGL3.GA D d) (z : Matrix (Fin d) (Fin a) D.host.E),
  ∃ n : ℕ, 0 < n ∧ ∀ z', Formalism.MainNotions.StandardLatticesGL3.CloseTo D cc n (x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) (y : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) z z' →
    Formalism.MainNotions.StandardLatticesGL3.wdPh D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z') = Formalism.MainNotions.StandardLatticesGL3.wdPh D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) := by
  first | exact @GlobalTheory.PhaseMove.phase_eq | exact GlobalTheory.PhaseMove.phase_eq | (intros; apply GlobalTheory.PhaseMove.phase_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocChrOfResEtaPow
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HoweLocal
open scoped TensorProduct Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.HoweLocal

theorem locChr_exists (hC : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl F), Continuous (GlobalTheory.HoweLocal.liftU (F := F) (E := E) v)) (hN : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl F) (z : (Fv F v ⊗[F] E)ˣ), Units.map (Algebra.norm (AF F) : AE F E →* AF F) (GlobalTheory.HoweLocal.liftU v z) = GlobalTheory.HoweLocal.liftUF v (Units.map (Algebra.norm (Fv F v) : Fv F v ⊗[F] E →* Fv F v) z)) (hQ : GlobalTheory.Published.QuadraticClassFieldTheory → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], Module.finrank F E = 2 → ∀ (v : Pl F) (a : (Fv F v)ˣ) (t : Fˣ) (z : (AE F E)ˣ), GlobalTheory.HoweLocal.liftUF v a = Units.map (algebraMap F (AF F)).toMonoidHom t * Units.map (Algebra.norm (AF F) : AE F E →* AF F) z → a ∈ (Units.map (Algebra.norm (Fv F v) : Fv F v ⊗[F] E →* Fv F v)).range) : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (m : ℕ) (χ : Chr F E), IsHecke F E χ →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m →
      ∀ v : Pl F, IsEmpty (E →ₐ[F] Fv F v) →
        ∃ χv : (Fv F v ⊗[F] E)ˣ →* Circle, Continuous χv ∧ ResEtaPow (R := Fv F v) ⊥ χv m ∧ GlobalTheory.HoweLocal.IsLocChr χ v χv := by
  intro hP F E _ _ _ _ _ σ hcm m χ hχ hres v _
  refine ⟨locChr χ v, hχ.1.comp (hC F E v), ?_, ?_⟩
  · intro a
    change ((χ (liftU v (Units.map (algebraMap (Fv F v) (Fv F v ⊗[F] E) : Fv F v →* Fv F v ⊗[F] E) a)) : Circle) : ℂ) = _
    rw [liftU_algebraMap]
    have h := hres (liftUF v a)
    simp only [RingHom.toMonoidHom_eq_coe] at h ⊢
    rw [h]
    congr 1
    apply propext
    rw [bot_sup_eq]
    constructor
    · intro hm
      obtain ⟨y, hy, n, hn, hyn⟩ := Subgroup.mem_sup.1 hm
      obtain ⟨t, rfl⟩ := hy
      obtain ⟨z, rfl⟩ := hn
      exact hQ hP.quadraticClassFieldTheory F E hcm.2.2.1 v a t z hyn.symm
    · rintro ⟨z, rfl⟩
      exact Subgroup.mem_sup_right ⟨liftU v z, hN F E v z⟩
  · intro a ha
    change χ (liftU v _) = χ a
    rw [liftU_compFin_of_at v a ha]

theorem exists_locChr_of_resEtaPow : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (m : ℕ) (χ : Chr F E), IsHecke F E χ →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m →
      ∀ v : Pl F, IsEmpty (E →ₐ[F] Fv F v) →
        ∃ χv : (Fv F v ⊗[F] E)ˣ →* Circle, Continuous χv ∧ ResEtaPow (R := Fv F v) ⊥ χv m ∧ GlobalTheory.HoweLocal.IsLocChr χ v χv :=
  locChr_exists GlobalTheory.HoweLocal.continuous_liftU GlobalTheory.HoweLocal.NormLift.norm_liftU GlobalTheory.HoweLocal.mem_localNorms_of_liftUF_eq

end GlobalTheory.HoweLocal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalDictionaryInertPlaceStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_dictionary_inertPlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n r s : ℕ) (X : Spc F E n), B.IsGood σ → X.IsHerm σ B r s →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∃ (O : Type) (_ : CommRing O) (c : O →+* O) (ι : O →ₙ+* AE F E) (P Q : Matrix (Fin n) (Fin n) (AE F E))
      (JL : Matrix (Fin n) (Fin n) O),
      IsLocalRing O ∧ (∀ x, c (c x) = x) ∧ IsUnit (2 : O) ∧ (∃ x : O, IsUnit (c x - x)) ∧
      Function.Injective ι ∧ At (evFin F v) (ι 1) ∧ (∀ y : AE F E, At (evFin F v) y → ι 1 * y = y) ∧
      (∀ x, cA σ (ι x) = ι (c x)) ∧
      P * Q = ι 1 • (1 : Matrix (Fin n) (Fin n) (AE F E)) ∧ Q * P = ι 1 • (1 : Matrix (Fin n) (Fin n) (AE F E)) ∧
      ι 1 • P = P ∧ ι 1 • Q = Q ∧
      (∀ i j, c (JL j i) = JL i j) ∧ IsUnit JL.det ∧ Pᵀ * incM F X.J * P.map (cA σ) = JL.map ι ∧
      ∀ z : Fin n → AE F E, z ∈ GlobalTheory.InertSph.latAt X v ↔ ∃ a : Fin n → O, z = P *ᵥ fun i => ι (a i) := by
  first | exact @GlobalTheory.InertLocDict.exists_local_dictionary | exact GlobalTheory.InertLocDict.exists_local_dictionary | (intros; apply GlobalTheory.InertLocDict.exists_local_dictionary <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalSchroedingerFamilyAtPlaceStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_schroedinger_family_at_place : ∀ (F : Type) [Field F] [NumberField F] (v : Pl F) (ψ : AddChar (AF F) ℂ), IsStd ψ → PsiUnr ψ v →
    ∀ {Wm : Type} [AddCommGroup Wm] [Module (AF F) Wm] {Bf : Wm → Wm → AF F} {κ : Type} [Fintype κ] (co : Darboux Bf κ)
      (Y : Type) [AddCommGroup Y] (Xm : Y →+ Wm) (χ : Y → Y → ℂ),
      (∀ z : Wm, At (evFin F v) z ↔ ∃ y, Xm y = z) → (∀ x y, ψ (⅟(2 : AF F) * Bf (Xm x) (Xm y)) = χ x y) →
      ∃ ρ : Y → Module.End ℂ (SB (κ → Fv F v)), ρ 0 = 1 ∧ (∀ x y, ρ x * ρ y = χ x y • ρ (x + y)) ∧
        (∀ x (φ : SB (κ → Fv F v)), Acts (evFin F v) (co.rho ψ (Xm x)) (φ : (κ → Fv F v) → ℂ)
          ((ρ x φ : SB (κ → Fv F v)) : (κ → Fv F v) → ℂ)) ∧
        ∀ s : SB (κ → Fv F v), s ≠ 0 → Submodule.span ℂ (Set.range fun x => ρ x s) = ⊤ := by
  first | exact @GlobalTheory.SchrLocModel.exists_locRho | exact GlobalTheory.SchrLocModel.exists_locRho | (intros; apply GlobalTheory.SchrLocModel.exists_locRho <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormScaleCurveIdealStatement
section
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normScale_curveIdeal : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)), Formalism.MainNotions.TaylorLogMetric.IsCurveIdeal D cc → ∃ r : D.host.E, IsScale D cc r := by
  first | exact @GlobalTheory.NormRatio.exists_scale | exact GlobalTheory.NormRatio.exists_scale | (intros; apply GlobalTheory.NormRatio.exists_scale <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNsmulSymplecticPairingCharacterTrivial
section
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped TensorProduct Topology

namespace GlobalTheory.FinCharInt

theorem tensInt_le {F E R : Type} [Field F] [CommRing E] [Algebra F E] [CommRing R] [Algebra F R]
    (S₁ : Subring E) (S₂ : Subring R) (K : AddSubgroup (E ⊗[F] R))
    (hK : ∀ b ∈ S₁, ∀ α ∈ S₂, b ⊗ₜ[F] α ∈ K) {x : E ⊗[F] R} (hx : x ∈ Formalism.UG.tensInt R S₁ S₂) : x ∈ K := by
  let C : AddSubgroup (E ⊗[F] R) := AddSubgroup.closure {z | ∃ b ∈ S₁, ∃ α ∈ S₂, z = b ⊗ₜ[F] α}
  have hC : C ≤ K := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨b, hb, α, hα, rfl⟩
    exact hK b hb α hα
  have hmul : ∀ x ∈ C, ∀ y ∈ C, x * y ∈ C := by
    intro x hx y hy
    induction hx, hy using AddSubgroup.closure_induction₂ with
    | mem x y hx hy =>
      obtain ⟨b, hb, α, hα, rfl⟩ := hx
      obtain ⟨c, hc, β, hβ, rfl⟩ := hy
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      exact AddSubgroup.subset_closure ⟨_, S₁.mul_mem hb hc, _, S₂.mul_mem hα hβ, rfl⟩
    | zero_left x _ => rw [zero_mul]; exact C.zero_mem
    | zero_right x _ => rw [mul_zero]; exact C.zero_mem
    | add_left x y z _ _ _ h1 h2 => rw [add_mul]; exact C.add_mem h1 h2
    | add_right x y z _ _ _ h1 h2 => rw [mul_add]; exact C.add_mem h1 h2
    | neg_left x y _ _ h => rw [neg_mul]; exact C.neg_mem h
    | neg_right x y _ _ h => rw [mul_neg]; exact C.neg_mem h
  refine hC ?_
  unfold Formalism.UG.tensInt at hx
  induction hx using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · exact AddSubgroup.subset_closure ⟨_, c.2, _, S₂.one_mem, rfl⟩
    · exact AddSubgroup.subset_closure ⟨_, S₁.one_mem, _, c.2, rfl⟩
  | zero => exact C.zero_mem
  | one => exact AddSubgroup.subset_closure ⟨_, S₁.one_mem, _, S₂.one_mem, Algebra.TensorProduct.one_def⟩
  | add x y _ _ ihx ihy => exact C.add_mem ihx ihy
  | neg x _ ihx => exact C.neg_mem ihx
  | mul x y _ _ ihx ihy => exact hmul _ ihx _ ihy

theorem exists_nsmul_kill {F : Type} [Field F] [NumberField F] {ψ : AddChar (AF F) ℂ} (hc : Continuous ψ)
    (hn : ∀ x, ‖ψ x‖ = 1) {ι : Type} [Finite ι] (c : ι → AF F) :
    ∃ N : ℕ, 0 < N ∧ ∀ i, ∀ α ∈ Formalism.UG.intAd F, ψ (N • (pairA F 0 α * c i)) = 1 := by
  have hU : (⋂ i, {α : Af F | ψ (pairA F 0 (α * (c i).2)) = 1}) ∈ 𝓝 (0 : Af F) := by
    refine Filter.iInter_mem.2 fun i => ?_
    have h1 : Continuous fun α : Af F => α * (c i).2 := continuous_id.mul continuous_const
    exact h1.continuousAt.preimage_mem_nhds (x := 0) (t := {a | ψ (pairA F 0 a) = 1})
      (by rw [zero_mul]; exact GlobalTheory.FinTranslate.ker_mem_nhds hc hn)
  obtain ⟨N, hN, h⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F _ hU
  refine ⟨N, hN, fun i α hα => ?_⟩
  have h1 : ψ (pairA F 0 ((N • α) * (c i).2)) = 1 := Set.mem_iInter.1 (h α hα) i
  have e : N • (pairA F 0 α * c i) = pairA F 0 ((N • α) * (c i).2) :=
    Prod.ext (show N • ((0 : Ainf F) * (c i).1) = 0 by rw [zero_mul, smul_zero])
      (show N • (α * (c i).2) = (N • α) * (c i).2 from (smul_mul_assoc N α _).symm)
  rw [e, h1]

def kerSub {A : Type} [AddCommGroup A] (ψ : AddChar A ℂ) : AddSubgroup A where
  carrier := {a | ψ a = 1}
  zero_mem' := ψ.map_zero_eq_one
  add_mem' {a b} ha hb := by
    have ha' : ψ a = 1 := ha
    have hb' : ψ b = 1 := hb
    show ψ (a + b) = 1
    rw [AddChar.map_add_eq_mul, ha', hb', one_mul]
  neg_mem' {a} ha := by
    have ha' : ψ a = 1 := ha
    show ψ (-a) = 1
    have := AddChar.map_add_eq_mul ψ a (-a)
    rw [add_neg_cancel, ψ.map_zero_eq_one, ha', one_mul] at this
    exact this.symm

variable {D : D7}

noncomputable def finIncl (D : D7) : Af D.host.F ⊗[D.host.F] D.host.E →ₗ[D.host.F] AE D :=
  TensorProduct.map (LinearMap.inr D.host.F (Ainf D.host.F) (Af D.host.F)) LinearMap.id

theorem finIncl_finPart {a : AE D} (h : infPart D a = 0) : finIncl D (finPart D a) = a := by
  have key : ∀ a : AE D, (1 - GlobalTheory.FinTranslate.eInf D) • a = finIncl D (finPart D a) := by
    intro a
    induction a using TensorProduct.induction_on with
    | zero => simp only [smul_zero, map_zero]
    | add a b ha hb => rw [smul_add, ha, hb, RingHom.map_add, map_add]
    | tmul a x =>
      rw [TensorProduct.smul_tmul']
      have : (1 - GlobalTheory.FinTranslate.eInf D) • a =
          LinearMap.inr D.host.F (Ainf D.host.F) (Af D.host.F) (sndA D.host.F a) :=
        Prod.ext (show (1 - 1) * a.1 = 0 by rw [sub_self, zero_mul]) (show (1 - 0) * a.2 = a.2 by rw [sub_zero, one_mul])
      rw [this]
      rfl
  rw [← key, sub_smul, one_smul, GlobalTheory.FinTranslate.smul_eq_zero_of_inf h, sub_zero]

theorem exists_nsmul_kill_forms {ψ : AddChar (AF D.host.F) ℂ} (hc : Continuous ψ) (hn : ∀ x, ‖ψ x‖ = 1)
    {ι : Type} [Finite ι] (lam : ι → (AE D →ₗ[AF D.host.F] AF D.host.F)) :
    ∃ N : ℕ, 0 < N ∧ ∀ i, ∀ a : AE D, infPart D a = 0 → GlobalTheory.BotClassDict.finQ D a ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D →
      ψ (N • lam i a) = 1 := by
  let w := RingOfIntegers.basis D.host.E
  obtain ⟨N, hN, h⟩ := exists_nsmul_kill hc hn
    (fun p : ι × Module.Free.ChooseBasisIndex ℤ (𝓞 D.host.E) =>
      lam p.1 ((1 : AF D.host.F) ⊗ₜ[D.host.F] (algebraMap (𝓞 D.host.E) D.host.E (w p.2))))
  refine ⟨N, hN, fun i a ha hint => ?_⟩
  let g : D.host.E ⊗[D.host.F] Af D.host.F →+ AF D.host.F :=
    N • ((lam i).toAddMonoidHom.comp ((finIncl D).toAddMonoidHom.comp
      (TensorProduct.comm D.host.F D.host.E (Af D.host.F)).toLinearMap.toAddMonoidHom))
  have hg : ∀ y, g (Lev.swapAE D y) = N • lam i (finIncl D y) := by
    intro y
    have : TensorProduct.comm D.host.F D.host.E (Af D.host.F) (Lev.swapAE D y) = y :=
      (TensorProduct.comm D.host.F (Af D.host.F) D.host.E).symm_apply_apply y
    show N • lam i (finIncl D (TensorProduct.comm D.host.F D.host.E (Af D.host.F) (Lev.swapAE D y))) = _
    rw [this]
  have h1 : Lev.swapAE D (finPart D a) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    have := (GlobalTheory.BotClassDict.toAfE_int_iff _).2 hint
    rwa [GlobalTheory.BotClassDict.toAfE_finQ] at this
  have h2 : Lev.swapAE D (finPart D a) ∈ (kerSub ψ).comap g := by
    refine tensInt_le _ _ _ ?_ h1
    rintro _ ⟨b, rfl⟩ α hα
    let φ : 𝓞 D.host.E →+ D.host.E ⊗[D.host.F] Af D.host.F :=
      ((TensorProduct.mk D.host.F D.host.E (Af D.host.F)).flip α).toAddMonoidHom.comp
        (algebraMap (𝓞 D.host.E) D.host.E).toAddMonoidHom
    have hb : b ∈ (((kerSub ψ).comap g).comap φ).toIntSubmodule := by
      have hsp : b ∈ Submodule.span ℤ (Set.range w) := by rw [w.span_eq]; trivial
      refine Submodule.span_le.2 ?_ hsp
      rintro _ ⟨k, rfl⟩
      have h3 := h (i, k) α hα
      rw [← smul_eq_mul, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one] at h3
      exact h3
    exact hb
  have h3 : ψ (g (Lev.swapAE D (finPart D a))) = 1 := h2
  rwa [hg, finIncl_finPart ha] at h3

noncomputable def symplR (S T : HSp D) (x : WO S T) : WO S T →ₗ[AF D.host.F] AF D.host.F where
  toFun := symplOH S T x
  map_add' := GlobalTheory.FinTranslate.symplOH_add_right S T x
  map_smul' c y := GlobalTheory.FinTranslate.symplOH_smul_right S T c x y

theorem char_sympl_nsmul_int : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), Continuous ψ → (∀ x, ‖ψ x‖ = 1) →
    ∀ (S T : HSp D) (A0 : WO S T), ∃ N : ℕ, 0 < N ∧ ∀ v : WO S T, (∀ i j, infPart D (v i j) = 0) →
      (∀ i j, GlobalTheory.BotClassDict.finQ D (v i j) ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D) → ψ (symplOH S T A0 (N • v)) = 1 := by
  intro D ψ hc hn S T A0
  obtain ⟨N, hN, h⟩ := exists_nsmul_kill_forms hc hn
    (fun p : Fin T.rank × Fin S.rank => (symplR S T A0).comp (Matrix.singleLinearMap (AF D.host.F) p.1 p.2))
  refine ⟨N, hN, fun v hv hint => ?_⟩
  show symplR S T A0 (N • v) ∈ kerSub ψ
  rw [map_nsmul, Matrix.matrix_eq_sum_single v, map_sum, Finset.smul_sum]
  refine sum_mem fun i _ => ?_
  rw [map_sum, Finset.smul_sum]
  exact sum_mem fun j _ => h (i, j) (v i j) (hv i j) (hint i j)

end GlobalTheory.FinCharInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenCompactLevelOfStandardCongruenceLevelStatement
section
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_openCompactLevel_of_standardCongruenceLevel : ∀ {D : D7} (V : HSp D) (n : ℕ) (ι : Formalism.MainNotions.StandardLatticesGL3.GA D n →* GA D V) (J : Subgroup (Formalism.MainNotions.StandardLatticesGL3.GA D n)), V.gram = 1 →
  (∀ x, IsFinPt V (ι x) x) → Function.Injective ι → ι.range = GfC V → J ≤ intG D n → IsCongLevel J →
  ∃ K : Subgroup (GL (Fin V.rank) (Lev.EAf D)), IsOpenCompactLevel V K ∧ ∀ x, Lev.finE V (ι x) ∈ K ↔ x ∈ J := by
  first | exact @GlobalTheory.CongLevelStd.exists_level | exact GlobalTheory.CongLevelStd.exists_level | (intros; apply GlobalTheory.CongLevelStd.exists_level <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrthonormalBasisSplitSupportedAdelicPointStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orthonormalBasis_splitSupported_adelicPoint : ∀ (D : D7) (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), V.SigOK →
    (∀ τ, V.sig τ = (V.rank, 0)) → IsSelfDualC V Λ → ∀ S : Finset ℕ, (∀ q ∈ S, q.Prime) →
    ∃ (fr : GL (Fin V.rank) D.host.E) (u : GfC V),
      Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr.1 * V.gram * fr.1 = 1 ∧
      (∃ (P : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e P ∧ SuppAt e V u.1 ∧ ∀ w ∈ P, Off S w) ∧
      ∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr) ↔
        (Formalism.IndefR.Lev.finE V u.1).1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
  first | exact @GlobalTheory.FunObj.StdVertex.exists_std_vertex | exact GlobalTheory.FunObj.StdVertex.exists_std_vertex | (intros; apply GlobalTheory.FunObj.StdVertex.exists_std_vertex <;> assumption)
end

