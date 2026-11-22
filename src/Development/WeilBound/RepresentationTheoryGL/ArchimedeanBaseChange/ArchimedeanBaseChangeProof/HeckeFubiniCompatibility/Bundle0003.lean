import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.Bundle0001
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PSplit
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0073

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PCompat
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Measure Topology
open GlobalTheory.CuspRep PositivityTheory.Rg.BcB.E
open PositivityTheory.RgTw (G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

namespace PositivityTheory.Rg.BcB.CG

section Gen

theorem hasCompactSupport_slice {A B : Type} [TopologicalSpace A] [TopologicalSpace B] [T2Space B] {F : A × B → ℂ}
    (hF : HasCompactSupport F) (a : A) : HasCompactSupport (fun b => F (a, b)) :=
  HasCompactSupport.intro (hF.isCompact.image continuous_snd) fun b hb =>
    image_eq_zero_of_notMem_tsupport fun h => hb ⟨(a, b), h, rfl⟩

theorem integral_tensor {X Y Z : Type} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z] (mX : Measure X) (mY : Measure Y) (mZ : Measure Z) [SigmaFinite mX] [SigmaFinite mY]
    [SigmaFinite mZ] (p : X → ℂ) (q : Y → ℂ) (r : Z → ℂ) :
    ∫ z, p z.1 * q z.2.1 * r z.2.2 ∂(mX.prod (mY.prod mZ)) = (∫ x, p x ∂mX) * (∫ y, q y ∂mY) * ∫ w, r w ∂mZ := by
  calc ∫ z, p z.1 * q z.2.1 * r z.2.2 ∂(mX.prod (mY.prod mZ))
      = ∫ z, p z.1 * (fun w : Y × Z => q w.1 * r w.2) z.2 ∂(mX.prod (mY.prod mZ)) := by simp only [mul_assoc]
    _ = (∫ x, p x ∂mX) * ∫ w, q w.1 * r w.2 ∂(mY.prod mZ) :=
      integral_prod_mul (L := ℂ) (μ := mX) (ν := mY.prod mZ) p (fun w : Y × Z => q w.1 * r w.2)
    _ = _ := by rw [integral_prod_mul (L := ℂ) (μ := mY) (ν := mZ) q r, mul_assoc]

end Gen

section Abstract

variable {X : Type} [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
variable {Y : Type} [Group Y] [TopologicalSpace Y] [IsTopologicalGroup Y] [LocallyCompactSpace Y]
  [SecondCountableTopology Y] [T2Space Y] [MeasurableSpace Y] [BorelSpace Y]
variable {Z : Type} [Group Z] [TopologicalSpace Z] [IsTopologicalGroup Z] [LocallyCompactSpace Z]
  [SecondCountableTopology Z] [T2Space Z] [MeasurableSpace Z] [BorelSpace Z]
variable {K : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [MeasurableSpace K] [BorelSpace K]

omit [SecondCountableTopology X] in
theorem exists_bump (μ : Measure X) [IsHaarMeasure μ] :
    ∃ f : X → ℂ, Continuous f ∧ HasCompactSupport f ∧ ∫ x, f x ∂μ ≠ 0 := by
  obtain ⟨f, hf1, -, hfc, hf01⟩ := exists_continuous_one_zero_of_isCompact (isCompact_singleton (x := (1 : X)))
    isClosed_empty (Set.disjoint_empty _)
  refine ⟨fun x => ((f x : ℝ) : ℂ), Complex.continuous_ofReal.comp f.continuous, hfc.comp_left Complex.ofReal_zero, ?_⟩
  show ∫ x, ((f x : ℝ) : ℂ) ∂μ ≠ 0
  rw [show ∫ x, ((f x : ℝ) : ℂ) ∂μ = ((∫ x, f x ∂μ : ℝ) : ℂ) from integral_ofReal, Complex.ofReal_ne_zero]
  exact (f.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hfc (fun x => (hf01 x).1) (x := 1)
    (by simp [hf1 (Set.mem_singleton (1 : X))])).ne'

theorem exists_split (e : X × (Y × Z) ≃ₜ* K) (μ : Measure K) [IsHaarMeasure μ] (mX : Measure X) [IsHaarMeasure mX]
    (mY : Measure Y) [IsHaarMeasure mY] (mZ : Measure Z) [IsHaarMeasure mZ] :
    ∃ c : NNReal, 0 < c ∧ ∀ f : K → ℂ, ∫ g, f g ∂μ = c • ∫ z, f (e z) ∂(mX.prod (mY.prod mZ)) := by
  haveI : IsHaarMeasure (μ.map e.symm) := ContinuousMulEquiv.isHaarMeasure_map μ e.symm
  obtain ⟨c, hc0, h⟩ : ∃ c : NNReal, 0 < c ∧ μ.map e.symm = c • mX.prod (mY.prod mZ) :=
    ⟨_, haarScalarFactor_pos_of_isHaarMeasure _ _, isMulLeftInvariant_eq_smul _ _⟩
  refine ⟨c, hc0, fun f => ?_⟩
  have he : ∫ z, f (e z) ∂(μ.map e.symm) = ∫ g, f g ∂μ := by
    have := integral_map_equiv (μ := μ) (e.toHomeomorph.toMeasurableEquiv.symm) (fun z => f (e z))
    refine this.trans ?_
    congr 1
    funext x
    exact congrArg f (e.apply_symm_apply x)
  rw [← he, h, integral_smul_nnreal_measure]

theorem integral_iter (mX : Measure X) [IsHaarMeasure mX] (mY : Measure Y) [IsHaarMeasure mY] (mZ : Measure Z)
    [IsHaarMeasure mZ] (f : X × (Y × Z) → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) :
    ∫ z, f z ∂(mX.prod (mY.prod mZ)) = ∫ x, ∫ y, ∫ w, f (x, (y, w)) ∂mZ ∂mY ∂mX := by
  rw [integral_prod _ (hf.integrable_of_hasCompactSupport hfc)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact integral_prod _ ((hf.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
    (hasCompactSupport_slice hfc x))

end Abstract

section Inst

theorem lc_G (n : ℕ) : LocallyCompactSpace (G n) := Units.isClosedEmbedding_embedProduct.locallyCompactSpace

theorem sc_G (n : ℕ) : SecondCountableTopology (G n) :=
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  Units.isEmbedding_embedProduct.secondCountableTopology

variable (E : Type) [Field E] [NumberField E]

theorem lc_GLf (n : ℕ) : LocallyCompactSpace (GL (Fin n) (Af E)) :=
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele E
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField E
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (Af E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → Af E))
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (Af E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  Units.isClosedEmbedding_embedProduct.locallyCompactSpace

theorem sc_GLf (n : ℕ) : SecondCountableTopology (GL (Fin n) (Af E)) :=
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele E
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (Af E)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → Af E))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (Af E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  Units.isEmbedding_embedProduct.secondCountableTopology

theorem t2_GL_finite_adeles (n : ℕ) : T2Space (GL (Fin n) (Af E)) :=
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField E
  Units.isEmbedding_embedProduct.t2Space

end Inst

attribute [local instance] lc_G sc_G lc_GLf sc_GLf t2_GL_finite_adeles

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem borelSpaceH : BorelSpace (H E a b) := ⟨rfl⟩

attribute [local instance] borelSpaceH

theorem haar_of_dom (D : Dom E a b) : IsHaarMeasure D.μ :=
  haveI := D.haar.2.2.2
  { toIsFiniteMeasureOnCompacts := isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure
    toIsMulLeftInvariant := D.haar.1
    toIsOpenPosMeasure := D.haar.2.2.1 }

def tensH (fa : InfinitePlace E → G a → ℂ) (fb : InfinitePlace E → G b → ℂ) (ψ : Hf E a b → ℂ) (g : H E a b) : ℂ :=
  (∏ v, fa v (gInf v g.1)) * (∏ v, fb v (gInf v g.2)) * ψ (hFin g)

theorem tensH_splitH (fa : InfinitePlace E → G a → ℂ) (fb : InfinitePlace E → G b → ℂ) (ψ : Hf E a b → ℂ)
    (z : (InfinitePlace E → G a) × ((InfinitePlace E → G b) × Hf E a b)) :
    tensH fa fb ψ (splitH a b z) = (∏ v, fa v (z.1 v)) * (∏ v, fb v (z.2.1 v)) * ψ z.2.2 := by
  simp only [tensH, gInf_splitH₁, gInf_splitH₂, hFin_splitH]

theorem integral_tensH_splitH [MeasurableSpace (G a)] [MeasurableSpace (G b)] [MeasurableSpace (Hf E a b)]
    (μa : Measure (G a)) [SigmaFinite μa] (μb : Measure (G b)) [SigmaFinite μb] (ν : Measure (Hf E a b)) [SigmaFinite ν]
    (fa : InfinitePlace E → G a → ℂ) (fb : InfinitePlace E → G b → ℂ) (ψ : Hf E a b → ℂ) :
    ∫ z, tensH fa fb ψ (splitH a b z) ∂((Measure.pi fun _ : InfinitePlace E => μa).prod
      ((Measure.pi fun _ : InfinitePlace E => μb).prod ν)) =
      (∏ v, ∫ y, fa v y ∂μa) * (∏ v, ∫ y, fb v y ∂μb) * ∫ h, ψ h ∂ν := by
  simp_rw [tensH_splitH]
  rw [integral_tensor _ _ _ (fun y : InfinitePlace E → G a => ∏ v, fa v (y v))
    (fun y : InfinitePlace E → G b => ∏ v, fb v (y v)) ψ]
  beta_reduce
  rw [integral_fintype_prod_eq_prod, integral_fintype_prod_eq_prod]

theorem compatFub : CompatFub := by
  intro E _ _ _ a b D _ _ _ _ _ _ μa _ μb _ ν _ hC F hF hFc
  haveI := haar_of_dom D
  have : IsHaarMeasure (Measure.pi fun _ : InfinitePlace E => μa) := pi.isHaarMeasure _
  have : IsHaarMeasure (Measure.pi fun _ : InfinitePlace E => μb) := pi.isHaarMeasure _
  obtain ⟨c, hc0, hc⟩ := exists_split (splitH a b) D.μ (Measure.pi fun _ : InfinitePlace E => μa)
    (Measure.pi fun _ : InfinitePlace E => μb) ν
  obtain ⟨fa, hfa, hfac, hfa0⟩ := exists_bump μa
  obtain ⟨fb, hfb, hfbc, hfb0⟩ := exists_bump μb
  obtain ⟨ψ, hψ, hψc, hψ0⟩ := exists_bump ν
  have h1 := hC (fun _ => fa) (fun _ => fb) ψ (fun _ => ⟨hfa, hfac⟩) (fun _ => ⟨hfb, hfbc⟩) hψ hψc
  change ∫ g, tensH (fun _ => fa) (fun _ => fb) ψ g ∂D.μ = _ at h1
  rw [hc, integral_tensH_splitH] at h1
  have hc1 : c = 1 := by
    have hne : (∏ _v : InfinitePlace E, ∫ y, fa y ∂μa) * (∏ _v : InfinitePlace E, ∫ y, fb y ∂μb) * ∫ h, ψ h ∂ν ≠ 0 := by
      simp [hfa0, hfb0, hψ0]
    rw [NNReal.smul_def, Complex.real_smul] at h1
    have h2 : ((c : ℝ) : ℂ) = 1 := mul_right_cancel₀ hne (by rw [one_mul]; exact h1)
    exact_mod_cast h2
  rw [hc F, hc1, one_smul]
  exact integral_iter _ _ _ (fun z => F (splitH a b z)) (hF.comp (splitH a b).continuous)
    (hFc.comp_homeomorph (splitH a b).toHomeomorph)

theorem compatEx : CompatEx := by
  intro E _ _ _ a b D _ _ _ _ _ _ μa _ μb _
  haveI := haar_of_dom D
  haveI : D.μ.IsMulRightInvariant := D.haar.2.1
  have : IsHaarMeasure (Measure.pi fun _ : InfinitePlace E => μa) := pi.isHaarMeasure _
  have : IsHaarMeasure (Measure.pi fun _ : InfinitePlace E => μb) := pi.isHaarMeasure _
  set ν₀ : Measure (Hf E a b) := Measure.haar
  obtain ⟨c, hc0, hc⟩ := exists_split (splitH a b) D.μ (Measure.pi fun _ : InfinitePlace E => μa)
    (Measure.pi fun _ : InfinitePlace E => μb) ν₀
  obtain ⟨fa, hfa, hfac, hfa0⟩ := exists_bump μa
  obtain ⟨fb, hfb, hfbc, hfb0⟩ := exists_bump μb
  have hR : ∀ h : Hf E a b, ν₀.map (· * h) = ν₀ := by
    intro h
    obtain ⟨k, hk⟩ : ∃ k : NNReal, ν₀.map (· * h) = k • ν₀ := ⟨_, isMulLeftInvariant_eq_smul _ _⟩
    obtain ⟨ψ, hψ, hψc, hψ0⟩ := exists_bump ν₀
    have h1 := integral_mul_right_eq_self (μ := D.μ) (tensH (fun _ => fa) (fun _ => fb) ψ) (splitH a b (1, (1, h)))
    rw [hc, hc] at h1
    have e1 : ∀ z : (InfinitePlace E → G a) × ((InfinitePlace E → G b) × Hf E a b),
        tensH (fun _ => fa) (fun _ => fb) ψ (splitH a b z * splitH a b (1, (1, h))) =
          (∏ v, fa (z.1 v)) * (∏ v, fb (z.2.1 v)) * ψ (z.2.2 * h) := by
      intro z
      rw [← map_mul, tensH_splitH]
      simp
    simp_rw [e1] at h1
    rw [integral_tensor _ _ _ (fun y : InfinitePlace E → G a => ∏ v, fa (y v))
      (fun y : InfinitePlace E → G b => ∏ v, fb (y v)) (fun w : Hf E a b => ψ (w * h)),
      integral_tensH_splitH] at h1
    beta_reduce at h1
    rw [integral_fintype_prod_eq_prod, integral_fintype_prod_eq_prod] at h1
    have e2 : ∫ w, ψ (w * h) ∂ν₀ = k • ∫ w, ψ w ∂ν₀ := by
      rw [← integral_smul_nnreal_measure, ← hk, integral_map (measurable_mul_const h).aemeasurable
        hψ.aestronglyMeasurable]
    rw [e2] at h1
    have hne : (∏ _v : InfinitePlace E, ∫ y, fa y ∂μa) * (∏ _v : InfinitePlace E, ∫ y, fb y ∂μb) * ∫ w, ψ w ∂ν₀ ≠ 0 := by
      simp [hfa0, hfb0, hψ0]
    simp only [NNReal.smul_def, Complex.real_smul] at h1
    have hc' : ((c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc0.ne'
    have h2 : ((k : ℝ) : ℂ) * (((c : ℝ) : ℂ) * ((∏ _v : InfinitePlace E, ∫ y, fa y ∂μa) *
        (∏ _v : InfinitePlace E, ∫ y, fb y ∂μb) * ∫ w, ψ w ∂ν₀)) = 1 * (((c : ℝ) : ℂ) *
        ((∏ _v : InfinitePlace E, ∫ y, fa y ∂μa) * (∏ _v : InfinitePlace E, ∫ y, fb y ∂μb) * ∫ w, ψ w ∂ν₀)) := by
      linear_combination h1
    have h3 : ((k : ℝ) : ℂ) = 1 := mul_right_cancel₀ (mul_ne_zero hc' hne) h2
    have hk1 : k = 1 := by exact_mod_cast h3
    rw [hk, hk1, one_smul]
  haveI : ν₀.IsMulRightInvariant := ⟨hR⟩
  refine ⟨c • ν₀, IsHaarMeasure.nnreal_smul _ hc0.ne', ⟨fun h => by rw [Measure.map_smul, hR]⟩, ?_⟩
  intro fa' fb' ψ' hfa' hfb' hψ' hψc'
  change ∫ g, tensH fa' fb' ψ' g ∂D.μ = _
  rw [hc, integral_tensH_splitH, integral_smul_nnreal_measure]
  simp only [NNReal.smul_def, Complex.real_smul]
  ring

end PositivityTheory.Rg.BcB.CG

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PReproA
section
noncomputable section

open MeasureTheory NumberField GlobalTheory.CuspRep

namespace PositivityTheory.Rg.BcB.CG.ReproA

section Fin

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

theorem hasCompactSupport_prod {ι : Type} [Fintype ι] (a : ι → G → ℂ) (ha' : ∀ i, HasCompactSupport (a i))
    (f : (ι → G) → ℂ) : HasCompactSupport fun y : ι → G => (∏ i, a i (y i)) * f y := by
  refine HasCompactSupport.intro (isCompact_univ_pi fun i => ha' i) fun y hy => ?_
  simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hy
  obtain ⟨i, hi⟩ := hy
  rw [Finset.prod_eq_zero (Finset.mem_univ i) (image_eq_zero_of_notMem_tsupport (f := a i) hi), zero_mul]

theorem continuous_prod_mul {ι : Type} [Fintype ι] (a : ι → G → ℂ) (ha : ∀ i, Continuous (a i))
    (f : (ι → G) → ℂ) (hf : Continuous f) : Continuous fun y : ι → G => (∏ i, a i (y i)) * f y :=
  (continuous_finsetProd _ fun i _ => (ha i).comp (continuous_apply i)).mul hf

theorem cons_one_mul (n : ℕ) (z : Fin n → G) (j : Fin n) (t : G) :
    (Fin.cons 1 (z * Pi.mulSingle j t) : Fin (n + 1) → G) = Fin.cons 1 z * Pi.mulSingle j.succ t := by
  funext k
  refine Fin.cases ?_ (fun k => ?_) k
  · simp [Fin.succ_ne_zero]
  · simp only [Fin.cons_succ, Pi.mul_apply, Pi.mulSingle_apply, Fin.succ_inj]

theorem cons_mul_single (n : ℕ) (z : Fin n → G) (t : G) :
    (Fin.cons 1 z : Fin (n + 1) → G) * Pi.mulSingle 0 t = Fin.cons t z := by
  funext k
  refine Fin.cases ?_ (fun k => ?_) k
  · simp
  · simp [Fin.succ_ne_zero]

variable (μ : Measure G) [μ.IsHaarMeasure]

theorem integral_fin_repro : ∀ (n : ℕ) (a : Fin n → G → ℂ), (∀ i, Continuous (a i)) → (∀ i, HasCompactSupport (a i)) →
    ∀ (f : (Fin n → G) → ℂ), Continuous f → ∀ (s : Fin n → ℂ),
    (∀ i y, ∫ t, a i t * f (y * Pi.mulSingle i t) ∂μ = s i * f y) →
    ∫ y, (∏ i, a i (y i)) * f y ∂(Measure.pi fun _ => μ) = (∏ i, s i) * f 1
  | 0, a, _, _, f, _, s, _ => by
    rw [Measure.pi_of_empty (fun _ : Fin 0 => μ) 1, integral_dirac]
    simp
  | n + 1, a, ha, ha', f, hf, s, h => by
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => G) 0 with he
    have hmp : MeasurePreserving e (Measure.pi fun _ => μ) (μ.prod (Measure.pi fun _ : Fin n => μ)) :=
      measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0
    set F : (Fin (n + 1) → G) → ℂ := fun y => (∏ i, a i (y i)) * f y with hF
    have hFi : Integrable F (Measure.pi fun _ => μ) :=
      (continuous_prod_mul a ha f hf).integrable_of_hasCompactSupport (hasCompactSupport_prod a ha' f)
    have e1 : ∫ y, F y ∂(Measure.pi fun _ => μ) = ∫ p, F (e.symm p) ∂(μ.prod (Measure.pi fun _ : Fin n => μ)) := by
      rw [← hmp.integral_comp' (fun p => F (e.symm p))]
      simp
    have hsymm : ∀ p : G × (Fin n → G), e.symm p = Fin.cons p.1 p.2 := by
      intro p
      rw [he, MeasurableEquiv.piFinSuccAbove_symm_apply]
      exact Fin.insertNth_zero' _ _
    have hGi : Integrable (fun p => F (e.symm p)) (μ.prod (Measure.pi fun _ : Fin n => μ)) := by
      have := (hmp.symm e).integrable_comp_emb e.symm.measurableEmbedding (g := F)
      exact this.2 hFi
    change ∫ y, F y ∂(Measure.pi fun _ => μ) = _
    rw [e1, integral_prod_symm _ hGi]
    have e2 : ∀ z : Fin n → G, ∫ t, F (e.symm (t, z)) ∂μ =
        (∏ j, a j.succ (z j)) * (s 0 * f (Fin.cons 1 z)) := by
      intro z
      rw [← h 0 (Fin.cons 1 z), ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      simp only [hsymm, hF, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, cons_mul_single]
      ring
    simp_rw [e2]
    set a' : Fin n → G → ℂ := fun j => a j.succ
    set f' : (Fin n → G) → ℂ := fun z => f (Fin.cons 1 z)
    have hf' : Continuous f' := hf.comp (continuous_const.finCons continuous_id)
    have h' : ∀ j z, ∫ t, a' j t * f' (z * Pi.mulSingle j t) ∂μ = s j.succ * f' z := by
      intro j z
      simp only [a', f', cons_one_mul]
      exact h j.succ (Fin.cons 1 z)
    have ih := integral_fin_repro n a' (fun j => ha j.succ) (fun j => ha' j.succ) f' hf' (fun j => s j.succ) h'
    have e3 : ∀ z : Fin n → G, (∏ j, a j.succ (z j)) * (s 0 * f (Fin.cons 1 z)) =
        s 0 * ((∏ j, a' j (z j)) * f' z) := fun z => by simp only [a', f']; ring
    simp_rw [e3]
    rw [integral_const_mul, ih, Fin.prod_univ_succ]
    have e4 : f' 1 = f 1 := by
      simp only [f']
      congr 1
      funext k
      refine Fin.cases ?_ (fun k => ?_) k <;> simp
    rw [e4]
    ring

end Fin

theorem integral_pi_repro {ι : Type} [Fintype ι] [DecidableEq ι] {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G]
    [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (a : ι → G → ℂ) (ha : ∀ i, Continuous (a i))
    (ha' : ∀ i, HasCompactSupport (a i)) (f : (ι → G) → ℂ) (hf : Continuous f) (s : ι → ℂ)
    (h : ∀ i y, ∫ t, a i t * f (y * Pi.mulSingle i t) ∂μ = s i * f y) :
    ∫ y, (∏ i, a i (y i)) * f y ∂(Measure.pi fun _ => μ) = (∏ i, s i) * f 1 := by
  set e := Fintype.equivFin ι
  set Φ := MeasurableEquiv.arrowCongr' e.symm (MeasurableEquiv.refl G) with hΦ
  have hmp : MeasurePreserving Φ (Measure.pi fun _ : Fin (Fintype.card ι) => μ) (Measure.pi fun _ : ι => μ) :=
    measurePreserving_arrowCongr' _ _ e.symm (MeasurableEquiv.refl G) fun _ => MeasurePreserving.id μ
  have hΦa : ∀ z : Fin (Fintype.card ι) → G, Φ z = fun i => z (e i) := by
    intro z; funext i; rfl
  rw [← hmp.integral_comp' (fun y => (∏ i, a i (y i)) * f y)]
  simp_rw [hΦa]
  set a' : Fin (Fintype.card ι) → G → ℂ := fun k => a (e.symm k)
  set f' : (Fin (Fintype.card ι) → G) → ℂ := fun z => f fun i => z (e i)
  have e1 : ∀ z : Fin (Fintype.card ι) → G, (∏ i, a i (z (e i))) * f (fun i => z (e i)) =
      (∏ k, a' k (z k)) * f' z := by
    intro z
    simp only [a', f']
    congr 1
    exact Fintype.prod_equiv e _ _ fun i => by simp
  simp_rw [e1]
  have hf' : Continuous f' := hf.comp (continuous_pi fun i => continuous_apply (e i))
  have hmul : ∀ (z : Fin (Fintype.card ι) → G) (k : Fin (Fintype.card ι)) (t : G),
      (fun i => (z * Pi.mulSingle k t : Fin (Fintype.card ι) → G) (e i)) =
        (fun i => z (e i)) * Pi.mulSingle (e.symm k) t := by
    intro z k t
    funext i
    simp only [Pi.mul_apply, Pi.mulSingle_apply]
    by_cases hi : i = e.symm k
    · subst hi; simp
    · have : e i ≠ k := fun h' => hi (by rw [← h']; simp)
      simp [hi, this]
  have h' : ∀ k z, ∫ t, a' k t * f' (z * Pi.mulSingle k t) ∂μ = s (e.symm k) * f' z := by
    intro k z
    simp only [a', f', hmul]
    exact h (e.symm k) _
  rw [integral_fin_repro μ _ a' (fun k => ha _) (fun k => ha' _) f' hf' _ h']
  have e2 : f' 1 = f 1 := rfl
  rw [e2]
  congr 1
  exact Fintype.prod_equiv e.symm _ _ fun k => rfl

theorem pi_isHaar {ι : Type} [Fintype ι] {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G]
    [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] : (Measure.pi fun _ : ι => μ).IsHaarMeasure := by
  infer_instance

theorem haar_restrict_eq {X A : Type} [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [MeasurableSpace X]
    [BorelSpace X] [Group A] [TopologicalSpace A] [IsTopologicalGroup A] [LocallyCompactSpace A]
    [SecondCountableTopology A] [T2Space A] [MeasurableSpace A] [BorelSpace A]
    (ν : Measure X) [ν.IsHaarMeasure] (lam0 : Measure A) [lam0.IsHaarMeasure] (P : X →* A) (hP : Continuous P)
    (σ : A →* X) (hσ : ∀ a, P (σ a) = a) (U0 : Subgroup X) (hU0 : IsOpen (U0 : Set X)) (hσU : ∀ a, σ a ∈ U0)
    (hprop : ∀ C : Set A, IsCompact C → ∃ D : Set X, IsCompact D ∧ (U0 : Set X) ∩ P ⁻¹' C ⊆ D) :
    ∃ c : ℝ, 0 < c ∧ ∀ F : A → ℂ, Continuous F → HasCompactSupport F →
      ∫ x, (U0 : Set X).indicator (fun x => F (P x)) x ∂ν = c * ∫ a, F a ∂lam0 := by
  have hPm : Measurable P := hP.measurable
  have hU0m : MeasurableSet (U0 : Set X) := hU0.measurableSet
  set lam : Measure A := Measure.map P (ν.restrict U0) with hlam
  have hinv : lam.IsMulLeftInvariant := by
    refine ⟨fun a => ?_⟩
    have hf : Measurable fun x : X => σ a * x := measurable_const_mul (σ a)
    have hpre : (fun x : X => σ a * x) ⁻¹' (U0 : Set X) = U0 := by
      ext x
      simp only [Set.mem_preimage, SetLike.mem_coe]
      exact ⟨fun h => by simpa using U0.mul_mem (U0.inv_mem (hσU a)) h, fun h => U0.mul_mem (hσU a) h⟩
    have e1 : Measure.map (fun x : X => σ a * x) (ν.restrict U0) = ν.restrict U0 := by
      conv_lhs => rw [← hpre]
      rw [← Measure.restrict_map hf hU0m, map_mul_left_eq_self]
    rw [hlam, Measure.map_map (measurable_const_mul a) hPm]
    have e2 : (fun x : A => a * x) ∘ P = P ∘ fun x : X => σ a * x := by
      funext x; simp [hσ]
    rw [e2, ← Measure.map_map hPm hf, e1]
  have hfin : IsFiniteMeasureOnCompacts lam := by
    refine ⟨fun C hC => ?_⟩
    obtain ⟨D, hD, hsub⟩ := hprop C hC
    rw [hlam, Measure.map_apply hPm hC.isClosed.measurableSet, Measure.restrict_apply (hPm hC.isClosed.measurableSet)]
    refine lt_of_le_of_lt (measure_mono ?_) hD.measure_lt_top
    intro x hx
    exact hsub ⟨hx.2, hx.1⟩
  have heq := Measure.isMulLeftInvariant_eq_smul lam lam0
  set c' := Measure.haarScalarFactor lam lam0 with hc'
  have hpos : c' ≠ 0 := by
    intro h0
    have h1 : lam Set.univ = 0 := by rw [heq, h0]; simp
    rw [hlam, Measure.map_apply hPm MeasurableSet.univ, Set.preimage_univ, Measure.restrict_apply MeasurableSet.univ,
      Set.univ_inter] at h1
    exact (hU0.measure_ne_zero ν ⟨1, U0.one_mem⟩) h1
  refine ⟨(c' : ℝ), lt_of_le_of_ne c'.2 (fun h => hpos (NNReal.coe_eq_zero.1 h.symm)), fun F hF _ => ?_⟩
  rw [integral_indicator hU0m, ← integral_map hPm.aemeasurable hF.aestronglyMeasurable, ← hlam]
  conv_lhs => rw [heq]
  rw [integral_smul_nnreal_measure]
  simp [NNReal.smul_def]

theorem exists_compact_open_le (E : Type) [Field E] [NumberField E] (N : ℕ) (K : Subgroup (GL (Fin N) (Af E)))
    (hK : IsOpen (K : Set (GL (Fin N) (Af E)))) :
    ∃ K0 : Subgroup (GL (Fin N) (Af E)), K0 ≤ K ∧ IsOpen (K0 : Set (GL (Fin N) (Af E))) ∧
      IsCompact (K0 : Set (GL (Fin N) (Af E))) := by
  obtain ⟨U, hUo, hUc⟩ := GlobalTheory.GLIntegral.exists_isOpen_isCompact E N
  refine ⟨K ⊓ U, inf_le_left, ?_, ?_⟩
  · exact hK.inter hUo
  · exact hUc.inter_left (K.isClosed_of_isOpen hK)

end PositivityTheory.Rg.BcB.CG.ReproA
end
end

