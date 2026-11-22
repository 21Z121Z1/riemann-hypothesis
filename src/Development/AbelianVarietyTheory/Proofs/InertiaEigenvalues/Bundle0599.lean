import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0086
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0188
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0198
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0592
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0590
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0580
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTameFieldGoodLatticePotentiallyCrystalline
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0589
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleUnitsHaarMeasureDivAbsIsHaarMeasure
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open scoped NNReal ENNReal Pointwise

noncomputable section

namespace GlobalTheory.JR.UnitsHaar

theorem secondCountable_base (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] : SecondCountableTopology F := by
  haveI : LocallyCompactSpace F := @Unram.lcF F E _ _ _ _ ‹_›
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F (E := F)
  infer_instance

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  [Unram F E] (A : Et F E)

theorem top_K : T2Space A.K ∧ SecondCountableTopology A.K := by
  haveI := secondCountable_base F E
  let e := (Module.finBasis F A.K).equivFun
  have h1 : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have h2 : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  let h : A.K ≃ₜ (Fin _ → F) := ⟨e.toEquiv, h1, h2⟩
  exact ⟨h.isEmbedding.t2Space, h.isEmbedding.isInducing.secondCountableTopology⟩

omit [Unram F E] in
theorem openUnits : IsOpenUnits A.K :=
  GlobalTheory.GaugeEx.isOpenUnits_of_basis (Module.finBasis F A.K)

omit [Unram F E] in
theorem absK_eq (t : A.K) : A.absK t = (GlobalTheory.GaugeEx.modu A.K t : ℝ) := by
  unfold Et.absK GlobalTheory.GaugeEx.modu; split_ifs <;> simp

omit [Unram F E] in
theorem borel_units : BorelSpace A.Kˣ := by
  have hemb := (openUnits A).isOpenEmbedding_unitsVal
  refine ⟨?_⟩
  rw [hemb.isEmbedding.isInducing.eq_induced, borel_comap, ← BorelSpace.measurable_eq]
  rfl

omit [Unram F E] in
theorem modu_mul_left (c : A.Kˣ) (t : A.K) :
    GlobalTheory.GaugeEx.modu A.K ((c : A.K) * t) = GlobalTheory.GaugeEx.modu A.K c * GlobalTheory.GaugeEx.modu A.K t := by
  classical
  by_cases ht : IsUnit t
  · obtain ⟨u, rfl⟩ := ht
    rw [← Units.val_mul, GlobalTheory.GaugeEx.modu_units, GlobalTheory.GaugeEx.modu_units, GlobalTheory.GaugeEx.modu_units, map_mul]
  · have hct : ¬ IsUnit ((c : A.K) * t) := fun h => ht (IsUnit.mul_iff.1 h).2
    simp [GlobalTheory.GaugeEx.modu, ht, hct]

omit [Unram F E] in
theorem modu_units_inv (u : A.Kˣ) :
    (GlobalTheory.GaugeEx.modu A.K u)⁻¹ = distribHaarChar A.K u⁻¹ := by
  rw [GlobalTheory.GaugeEx.modu_units, map_inv]

def dens (t : A.K) : ℝ≥0 := (GlobalTheory.GaugeEx.modu A.K t)⁻¹

omit [Unram F E] in
theorem unitsMeas_eq (μK : Measure A.K) :
    LinDesc.unitsMeas A μK = (μK.withDensity fun t => (dens A t : ℝ≥0∞)).comap Units.val := by
  have : ∀ t, ENNReal.ofReal (A.absK t)⁻¹ = (dens A t : ℝ≥0∞) := fun t => by
    rw [absK_eq, dens, ← NNReal.coe_inv, ENNReal.ofReal_coe_nnreal]
  unfold LinDesc.unitsMeas
  simp only [this]

theorem finiteRing_sq_sub_mul_sq_eq_of_card (μK : Measure A.K) (hμ : μK.IsAddHaarMeasure) :
    BorelSpace A.Kˣ ∧ (LinDesc.unitsMeas A μK).IsHaarMeasure ∧ ∀ h : A.K → ℂ,
      ∫ s, h (s : A.K) ∂(LinDesc.unitsMeas A μK) = ∫ t in {t : A.K | IsUnit t}, h t * ((A.absK t : ℂ))⁻¹ ∂μK := by
  classical
  obtain ⟨hT2, hSC⟩ := top_K A
  have hOU := openUnits A
  haveI hB := borel_units A
  have hemb := hOU.isOpenEmbedding_unitsVal
  have hme : MeasurableEmbedding (Units.val : A.Kˣ → A.K) := hemb.measurableEmbedding
  have hU : IsOpen {t : A.K | IsUnit t} := hemb.isOpen_range
  have hmod : Measurable (GlobalTheory.GaugeEx.modu A.K) := by
    have hc := (GlobalTheory.GaugeEx.modu_basic A.K).2.2.2 hOU
    have := hc.measurable_piecewise (g := fun _ => 0) continuousOn_const hU.measurableSet
    convert this using 1
    funext u
    by_cases hu : IsUnit u
    · simp [Set.piecewise, hu]
    · simp [Set.piecewise, GlobalTheory.GaugeEx.modu, hu]
  have hdm : Measurable (dens A) := hmod.inv
  set ν := μK.withDensity fun t => (dens A t : ℝ≥0∞) with hν
  rw [unitsMeas_eq]
  refine ⟨hB, ?_, ?_⟩
  swap
  · intro h
    have hr : Set.range (Units.val : A.Kˣ → A.K) = {t : A.K | IsUnit t} := Set.ext fun _ => Iff.rfl
    rw [← hme.integral_map, hme.map_comap, hr, restrict_withDensity hU.measurableSet,
      integral_withDensity_eq_integral_smul hdm]
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    simp only
    rw [NNReal.smul_def, Complex.real_smul, absK_eq, dens, NNReal.coe_inv, Complex.ofReal_inv, mul_comm]
  haveI := hμ
  have hc0 : ∀ c : A.Kˣ, 0 < GlobalTheory.GaugeEx.modu A.K c := fun c => ((GlobalTheory.GaugeEx.modu_basic A.K).1 c c.isUnit).1
  have hscale : ∀ (c : A.Kˣ) (G : A.K → ℝ≥0∞),
      ∫⁻ t, G t ∂μK = (GlobalTheory.GaugeEx.modu A.K c : ℝ≥0∞) * ∫⁻ t, G ((c : A.K) * t) ∂μK := by
    intro c G
    have e := ((GlobalTheory.GaugeEx.modu_basic A.K).1 c c.isUnit).2 μK hμ
    have hm : MeasurableEmbedding (fun z : A.K => (c : A.K) * z) := (Homeomorph.smul c).measurableEmbedding
    conv_lhs => rw [e]
    rw [lintegral_smul_measure, hm.lintegral_map]
    rfl
  have hinv : ∀ (c : A.Kˣ) (T : Set A.K), MeasurableSet T → ν ((fun t => (c : A.K) * t) ⁻¹' T) = ν T := by
    intro c T hT
    have hT' : MeasurableSet ((fun t => (c : A.K) * t) ⁻¹' T) := (measurable_const_mul _) hT
    rw [hν, withDensity_apply _ hT, withDensity_apply _ hT', ← lintegral_indicator hT, ← lintegral_indicator hT']
    conv_rhs => rw [hscale c]
    rw [← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
    refine lintegral_congr fun t => ?_
    by_cases ht : (c : A.K) * t ∈ T
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem (show t ∈ (fun t => (c : A.K) * t) ⁻¹' T from ht)]
      rw [← ENNReal.coe_mul, ENNReal.coe_inj, dens, dens, modu_mul_left, mul_inv, ← mul_assoc,
        mul_inv_cancel₀ (hc0 c).ne', one_mul]
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem (show t ∉ (fun t => (c : A.K) * t) ⁻¹' T from ht),
        mul_zero]
  have hL : (ν.comap Units.val).IsMulLeftInvariant := by
    refine ⟨fun c => ?_⟩
    ext S hS
    rw [Measure.map_apply (measurable_const_mul c) hS, hme.comap_apply, hme.comap_apply]
    have hset : Units.val '' ((fun x => c * x) ⁻¹' S) = (fun t : A.K => (c : A.K) * t) ⁻¹' (Units.val '' S) := by
      ext t; constructor
      · rintro ⟨u, hu, rfl⟩; exact ⟨c * u, hu, Units.val_mul c u⟩
      · rintro ⟨s, hs, hst⟩
        refine ⟨c⁻¹ * s, by simpa [Set.mem_preimage] using hs, ?_⟩
        rw [Units.val_mul, hst, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
    rw [hset, hinv c _ (hme.measurableSet_image.2 hS)]
  have hF : IsFiniteMeasureOnCompacts (ν.comap Units.val) := by
    refine ⟨fun C hC => ?_⟩
    rw [hme.comap_apply]
    have hcont : Continuous fun u : A.Kˣ => distribHaarChar A.K u⁻¹ :=
      (GlobalTheory.GaugeEx.continuous_distribHaarChar_units A.K).comp continuous_inv
    obtain ⟨M, hM⟩ := (hC.image hcont).bddAbove
    have hC' : IsCompact (Units.val '' C) := hC.image Units.continuous_val
    calc ν (Units.val '' C) = ∫⁻ t in Units.val '' C, (dens A t : ℝ≥0∞) ∂μK :=
          withDensity_apply _ hC'.measurableSet
      _ ≤ ∫⁻ t in Units.val '' C, (M : ℝ≥0∞) ∂μK := by
          refine setLIntegral_mono measurable_const fun t ht => ?_
          obtain ⟨u, hu, rfl⟩ := ht
          rw [ENNReal.coe_le_coe, dens, modu_units_inv]
          exact hM ⟨u, hu, rfl⟩
      _ = M * μK (Units.val '' C) := setLIntegral_const _ _
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.coe_lt_top hC'.measure_lt_top
  have hP : (ν.comap Units.val).IsOpenPosMeasure := by
    refine ⟨fun U hUo hne => ?_⟩
    rw [hme.comap_apply]
    have hVo : IsOpen (Units.val '' U) := hemb.isOpenMap U hUo
    intro h0
    rw [hν, withDensity_apply _ hVo.measurableSet, lintegral_eq_zero_iff hdm.coe_nnreal_ennreal] at h0
    have h1 : ∀ᵐ t ∂(μK.restrict (Units.val '' U)), False := by
      filter_upwards [h0, ae_restrict_mem hVo.measurableSet] with t ht hV
      obtain ⟨u, -, rfl⟩ := hV
      have : (dens A u : ℝ≥0∞) ≠ 0 := by
        rw [ENNReal.coe_ne_zero, dens, modu_units_inv]; exact distribHaarChar_pos.ne'
      exact this (by simpa using ht)
    have h2 : μK.restrict (Units.val '' U) = 0 := ae_eq_bot.1 (eventually_false_iff_eq_bot.1 h1)
    rw [Measure.restrict_eq_zero] at h2
    exact (hVo.measure_pos μK (hne.image _)).ne' h2
  exact { toIsFiniteMeasureOnCompacts := hF, toIsMulLeftInvariant := hL, toIsOpenPosMeasure := hP }

end GlobalTheory.JR.UnitsHaar

namespace GlobalTheory.JR.LinDesc

theorem unitsMeas_isHaar : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (μK : Measure A.K), μK.IsAddHaarMeasure → BorelSpace A.Kˣ ∧ (LinDesc.unitsMeas A μK).IsHaarMeasure ∧ ∀ h : A.K → ℂ, ∫ s, h (s : A.K) ∂(LinDesc.unitsMeas A μK) = ∫ t in {t : A.K | IsUnit t}, h t * ((A.absK t : ℂ))⁻¹ ∂μK :=
  fun _ _ _ _ _ _ _ A μK hμ => GlobalTheory.JR.UnitsHaar.finiteRing_sq_sub_mul_sq_eq_of_card A μK hμ

end GlobalTheory.JR.LinDesc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDescentSolutionLiftModPrismIdeal
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem pow_smul_top_eq {A : Type} [CommRing A] (I : Ideal A) (n : ℕ) :
    (I ^ n • (⊤ : Submodule A A)) = I ^ n := by
  rw [Ideal.smul_eq_mul, Ideal.mul_top]

theorem mulVec_mem_of_mem {B : Type} [CommRing B] {d : ℕ} (E : Matrix (Fin d) (Fin d) B) (J : Ideal B)
    (v : Fin d → B) (hv : ∀ j, v j ∈ J) (i : Fin d) : E.mulVec v i ∈ J := by
  simp only [Matrix.mulVec, dotProduct]
  exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hv j)

theorem lift_solution_of_step {A B : Type} [CommRing A] [CommRing B] (I : Ideal A) (J : Ideal B)
    (hA : IsPrecomplete I A) (hB : IsHausdorff J B) {d : ℕ} (p q : A →+* B)
    (hp : ∀ m : ℕ, I ^ m ≤ (J ^ m).comap p) (hq : ∀ m : ℕ, I ^ m ≤ (J ^ m).comap q)
    (E : Matrix (Fin d) (Fin d) B)
    (step : ∀ (m : ℕ) (z : Fin d → A), (∀ i, p (z i) - E.mulVec (fun j => q (z j)) i ∈ J ^ m) →
      ∃ z' : Fin d → A, (∀ i, z' i - z i ∈ I ^ m) ∧
        ∀ i, p (z' i) - E.mulVec (fun j => q (z' j)) i ∈ J ^ (m + 1))
    (z : Fin d → A) (hz : ∀ i, p (z i) - E.mulVec (fun j => q (z j)) i ∈ J ^ 1) :
    ∃ z' : Fin d → A, (∀ i, z' i - z i ∈ I ^ 1) ∧
      (fun i => p (z' i)) = E.mulVec (fun j => q (z' j)) := by

  let res : (Fin d → A) → Fin d → B := fun w i => p (w i) - E.mulVec (fun j => q (w j)) i
  have hres_sub : ∀ (w w' : Fin d → A) (i : Fin d),
      res w i - res w' i = p (w i - w' i) - E.mulVec (fun j => q (w j - w' j)) i := by
    intro w w' i
    have : (fun j => q (w j - w' j)) = (fun j => q (w j)) - (fun j => q (w' j)) := by
      funext j; simp
    show p (w i) - E.mulVec (fun j => q (w j)) i - (p (w' i) - E.mulVec (fun j => q (w' j)) i) = _
    rw [this, Matrix.mulVec_sub, Pi.sub_apply, map_sub]
    ring

  have hseq : ∃ g : ℕ → (Fin d → A), g 0 = z ∧ (∀ k i, res (g k) i ∈ J ^ (k + 1)) ∧
      ∀ k i, g (k + 1) i - g k i ∈ I ^ (k + 1) := by
    let G : (k : ℕ) → {w : Fin d → A // ∀ i, res w i ∈ J ^ (k + 1)} := fun k =>
      Nat.rec (motive := fun k => {w : Fin d → A // ∀ i, res w i ∈ J ^ (k + 1)}) ⟨z, hz⟩
        (fun k w => ⟨Classical.choose (step (k + 1) w.1 w.2),
          (Classical.choose_spec (step (k + 1) w.1 w.2)).2⟩) k
    refine ⟨fun k => (G k).1, rfl, fun k => (G k).2, fun k i => ?_⟩
    exact (Classical.choose_spec (step (k + 1) (G k).1 (G k).2)).1 i
  let g := Classical.choose hseq
  have hg0 : g 0 = z := (Classical.choose_spec hseq).1
  have hgres : ∀ k i, res (g k) i ∈ J ^ (k + 1) := (Classical.choose_spec hseq).2.1
  have hgd : ∀ k i, g (k + 1) i - g k i ∈ I ^ (k + 1) := (Classical.choose_spec hseq).2.2

  have hcau : ∀ i {m n : ℕ}, m ≤ n → g n i - g m i ∈ I ^ m := by
    intro i m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have h1 : g (n + 1) i - g n i ∈ I ^ m :=
        Ideal.pow_le_pow_right (by omega) (hgd n i)
      have := Ideal.add_mem _ h1 ih
      simpa using this

  have hlim : ∀ i, ∃ L : A, ∀ n, g n i - L ∈ I ^ n := by
    intro i
    have h := @IsPrecomplete.prec' A _ I A _ _ hA (fun k => g k i) (fun {m n} hmn => by
      rw [SModEq.sub_mem, pow_smul_top_eq]
      have := hcau i hmn
      rw [← neg_mem_iff, neg_sub] at this
      exact this)
    refine ⟨Classical.choose h, fun n => ?_⟩
    have := Classical.choose_spec h n
    rw [SModEq.sub_mem, pow_smul_top_eq] at this
    exact this
  let z' : Fin d → A := fun i => Classical.choose (hlim i)
  have hz' : ∀ i n, g n i - z' i ∈ I ^ n := fun i => Classical.choose_spec (hlim i)
  refine ⟨z', fun i => ?_, ?_⟩
  · have h1 : g 1 i - z' i ∈ I ^ 1 := hz' i 1
    have h2 : g 1 i - g 0 i ∈ I ^ 1 := hgd 0 i
    rw [hg0] at h2
    have := Ideal.sub_mem _ h2 h1
    simpa using this
  · funext i
    rw [← sub_eq_zero]
    refine hB.haus' _ fun k => ?_
    rw [SModEq.sub_mem, sub_zero, pow_smul_top_eq]
    have hd : res (g k) i - res z' i ∈ J ^ k := by
      rw [hres_sub]
      refine Ideal.sub_mem _ (hp k (hz' i k)) ?_
      exact mulVec_mem_of_mem E _ _ (fun j => hq k (hz' j k)) i
    have hr : res (g k) i ∈ J ^ k := Ideal.pow_le_pow_right (by omega) (hgres k i)
    have := Ideal.sub_mem _ hr hd
    simpa [res] using this

theorem lift_solution (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d)
    (B C D : Obj l ↥(OL K)) (h : Hom B C) (f : Hom bk.prism C) (p q : Hom C D) (hh : Cover h)
    (hpo : IsPO h h p q) (z : Fin d → C.A)
    (hz : ∀ i, p.f (z i) - (S.ε (p.comp f) (q.comp f)).mulVec (fun j => q.f (z j)) i ∈ adI D ^ 1) :
    ∃ z' : Fin d → C.A, (∀ i, z' i - z i ∈ adI C ^ 1) ∧
      (fun i => p.f (z' i)) = (S.ε (p.comp f) (q.comp f)).mulVec (fun j => q.f (z' j)) :=
  lift_solution_of_step (adI C) (adI D) C.complete.toIsPrecomplete D.complete.toIsHausdorff p.f q.f
    (adI_pow_le p) (adI_pow_le q) _ (GlobalTheory.T.lift_stratifiedSolution_succ_of_cover l K bk d S B C D h f p q hh hpo) z hz

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEtaleOEBasisOfIsogenousLattice
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.EtBasis

variable {l : ℕ} [Fact l.Prime]

theorem algebraMap_ne_zero (x : ℤ_[l]) (hx : x ≠ 0) : algebraMap ℤ_[l] (WCb l) x ≠ 0 := by
  rw [PadicInt.unitCoeff_spec hx, map_mul, map_pow, map_natCast]
  exact mul_ne_zero ((PadicInt.unitCoeff hx).isUnit.map _).ne_zero
    (pow_ne_zero _ (WittVector.irreducible l).ne_zero)

theorem algebraMap_mem_OE {K : FinExt l} (bk : BK K) (x : ℤ_[l]) : algebraMap ℤ_[l] (WCb l) x ∈ bk.OE := by
  intro n
  obtain ⟨y, hy⟩ := (Ideal.mem_span_singleton'.1 (PadicInt.appr_spec n x))
  refine ⟨0, (PadicInt.appr x n : bk.S), algebraMap ℤ_[l] (WCb l) y, ?_⟩
  have : x = (PadicInt.appr x n : ℤ_[l]) + (l : ℤ_[l]) ^ n * y := by rw [mul_comm, hy]; ring
  have h2 := congrArg (algebraMap ℤ_[l] (WCb l)) this
  rw [map_add, map_mul, map_pow, map_natCast, map_natCast] at h2
  rw [pow_zero, one_mul, h2, map_natCast]

theorem evW_mem_OE {K : FinExt l} (bk : BK K) (s : bk.S) : bk.evW s ∈ bk.OE := fun _ => ⟨0, s, 0, by simp⟩

theorem not_l_dvd_E {K : FinExt l} (bk : BK K) : ¬ (l : bk.S) ∣ bk.E := by
  rintro ⟨t, ht⟩
  have h := congrArg (coeff bk.Ep.natDegree) ht
  rw [← map_natCast (C (R := Wq l bk.a)) l, coeff_C_mul, Polynomial.coeff_coe, bk.monic.coeff_natDegree] at h
  have h2 := congrArg (WittVector.constantCoeff (p := l) (R := Fq l bk.a)) h
  rw [map_mul, map_natCast, map_one, CharP.cast_eq_zero, zero_mul] at h2
  exact one_ne_zero h2

theorem adj_comm {d : ℕ} (f A B : Matrix (Fin d) (Fin d) ℤ_[l]) (hf : f.det ≠ 0) (h : f * B = A * f) :
    f.adjugate * A = B * f.adjugate := by
  have h1 : f.det • (f.adjugate * A) = f.det • (B * f.adjugate) := by
    calc f.det • (f.adjugate * A) = f.adjugate * A * (f * f.adjugate) := by
          rw [Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one]
      _ = f.adjugate * (f * B) * f.adjugate := by rw [h]; simp only [Matrix.mul_assoc]
      _ = f.det • (B * f.adjugate) := by
          rw [← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul]
  exact smul_right_injective _ hf h1

end GlobalTheory.EtBasis

namespace GlobalTheory.EtBasis

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (N d : ℕ)
    (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (ρ'' : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l]))
    (F : Pre bk N d ρ) (f : Matrix (Fin d) (Fin d) (ℤ_[l])), f.det ≠ 0 → (∀ g, IsUnit (ρ'' g)) →
    (∀ g, f * ρ'' g = ρ g * f) → ∃ T'' P : Matrix (Fin d) (Fin d) (WCb l), IsUnit T'' ∧ (∀ i j, P i j ∈ bk.OE) ∧
      zW f * T'' = F.T * P := by
  intro l _ K bk τ _ N d ρ ρ'' F f hf hρ'' hfρ
  obtain ⟨hsat1, -, hinvS, -, -, hgalOE, hfrobOE⟩ := GlobalTheory.T.integral_elements_unit_factorization l K bk
  have hl0 : (l : WCb l) ≠ 0 := (WittVector.irreducible l).ne_zero
  have hzW : ∀ M : Matrix (Fin d) (Fin d) ℤ_[l], zW M = (algebraMap ℤ_[l] (WCb l)).mapMatrix M := fun _ => rfl
  have hzWmul : ∀ M M' : Matrix (Fin d) (Fin d) ℤ_[l], zW (M * M') = zW M * zW M' := fun M M' => by
    rw [hzW, hzW, hzW, map_mul]
  have hfadj : zW f * zW f.adjugate = algebraMap ℤ_[l] (WCb l) f.det • (1 : Matrix (Fin d) (Fin d) (WCb l)) := by
    rw [← hzWmul, Matrix.mul_adjugate]
    ext i j
    by_cases h : i = j <;> simp [zW, h, Matrix.one_apply]
  have hTdet : F.T.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 F.unit).ne_zero
  have hdf : algebraMap ℤ_[l] (WCb l) f.det ≠ 0 := algebraMap_ne_zero _ hf
  set Y1 := zW f.adjugate * F.T with hY1
  have hY1det : Y1.det ≠ 0 := by
    rw [hY1, Matrix.det_mul, hzW, ← RingHom.map_det, Matrix.det_adjugate, map_pow]
    exact mul_ne_zero (pow_ne_zero _ hdf) hTdet
  obtain ⟨m, P₀, Y', hP₀, hP₀det, hY', hlat, hsat⟩ := GlobalTheory.SatLattice.exists_lattice_basis l K bk d Y1 hY1det
  have hlm : (l : WCb l) ^ m ≠ 0 := pow_ne_zero _ hl0
  have hcancel : ∀ M M' : Matrix (Fin d) (Fin d) (WCb l), (l : WCb l) ^ m • M = (l : WCb l) ^ m • M' → M = M' :=
    fun M M' h => Matrix.ext fun i j => mul_left_cancel₀ hlm (congrFun (congrFun h i) j)

  have hY'det : Y'.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hY'
    rw [Matrix.det_smul, h0, mul_zero, Matrix.det_mul] at this
    exact mul_ne_zero hY1det hP₀det this.symm

  obtain ⟨e, he, hEe⟩ := hinvS bk.E (not_l_dvd_E bk)
  have hφ : ∃ A'' : Matrix (Fin d) (Fin d) (WCb l), (∀ i j, A'' i j ∈ bk.OE) ∧ Y'.map (frobW l) = Y' * A'' := by
    set B := e ^ N • F.A.map bk.evW with hB
    have hB_OE : ∀ i j, B i j ∈ bk.OE := fun i j => by
      simp only [hB, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
      exact bk.OE.mul_mem (bk.OE.pow_mem he N) (evW_mem_OE bk _)
    have hTφ : F.T.map (frobW l) = F.T * B := by
      have h := congrArg (fun M => e ^ N • M) F.φ
      have h1 : e ^ N * bk.evW bk.E ^ N = 1 := by rw [← mul_pow, mul_comm, hEe, one_pow]
      simp only [smul_smul, h1, one_smul] at h
      rw [h, hB, Matrix.mul_smul]
    have hfrobzW : ∀ M : Matrix (Fin d) (Fin d) ℤ_[l], (zW M).map (frobW l) = zW M := fun M => by
      exact Matrix.ext fun i j => (frobW l).commutes _
    have hmapmul : ∀ M M' : Matrix (Fin d) (Fin d) (WCb l),
        (M * M').map (frobW l) = M.map (frobW l) * M'.map (frobW l) :=
      fun M M' => Matrix.map_mul (f := (frobW l).toRingHom)
    have hY1φ : Y1.map (frobW l) = Y1 * B := by
      rw [hY1, hmapmul, hfrobzW, hTφ, Matrix.mul_assoc]
    set V := B * P₀.map (frobW l) with hV
    have hV_OE : ∀ i j, V i j ∈ bk.OE := fun i j => by
      simp only [hV, Matrix.mul_apply]
      exact bk.OE.sum_mem fun k _ => bk.OE.mul_mem (hB_OE i k) (hfrobOE _ (hP₀ k j))
    have hmain : (l : WCb l) ^ m • Y'.map (frobW l) = Y1 * V := by
      have h : ((l : WCb l) ^ m • Y').map (frobW l) = (Y1 * P₀).map (frobW l) := by rw [hY']
      rw [hmapmul, hY1φ] at h
      rw [hV, ← Matrix.mul_assoc, ← h]
      ext i j
      simp [map_mul, map_pow, map_natCast]
    have hcol : ∀ j, ∃ w : Fin d → WCb l, (∀ i, w i ∈ bk.OE) ∧ (fun i => V i j) = P₀ *ᵥ w := by
      intro j
      obtain ⟨w, hw, hvw⟩ := hlat (fun i => V i j) (fun i => hV_OE i j) m (fun i => by
        have : (Y1 *ᵥ fun i => V i j) i = (Y1 * V) i j := by
          simp [Matrix.mulVec, Matrix.mul_apply, dotProduct]
        rw [this, ← hmain, Matrix.smul_apply, smul_eq_mul]
        exact Dvd.intro _ rfl)
      exact ⟨w, hw, funext fun i => mul_left_cancel₀ hlm (congrFun hvw i)⟩
    choose w hw hvw using hcol
    refine ⟨Matrix.of fun i j => w j i, fun i j => hw j i, ?_⟩
    have hVP : V = P₀ * Matrix.of fun i j => w j i := by
      ext i j
      have := congrFun (hvw j) i
      simp only [Matrix.mulVec, dotProduct] at this
      simp [Matrix.mul_apply, this]
    apply hcancel
    rw [hmain, hVP, ← Matrix.mul_assoc, ← hY', Matrix.smul_mul]

  have hg : ∀ g : ↥(GK K), bk.FixFlat g → ∃ R : Matrix (Fin d) (Fin d) (WCb l), IsUnit R ∧
      R * Y'.map (galW l (g : GQ l)) = Y' := by
    intro g hfix
    refine ⟨zW (ρ'' g), by rw [hzW]; exact (hρ'' g).map _, ?_⟩
    have hgmul : ∀ M M' : Matrix (Fin d) (Fin d) (WCb l), (M * M').map (galW l (g : GQ l)) =
        M.map (galW l (g : GQ l)) * M'.map (galW l (g : GQ l)) :=
      fun M M' => Matrix.map_mul (f := (galW l (g : GQ l)).toRingEquiv.toRingHom)
    have hgzW : ∀ M : Matrix (Fin d) (Fin d) ℤ_[l], (zW M).map (galW l (g : GQ l)) = zW M := fun M => by
      exact Matrix.ext fun i j => (galW l (g : GQ l)).commutes _
    have hgP : P₀.map (galW l (g : GQ l)) = P₀ := by
      exact Matrix.ext fun i j => hgalOE g hfix _ (hP₀ i j)
    have hcomm : zW (ρ'' g) * zW f.adjugate = zW f.adjugate * zW (ρ g) := by
      rw [← hzWmul, ← hzWmul, adj_comm f (ρ g) (ρ'' g) hf (hfρ g)]
    have h : ((l : WCb l) ^ m • Y').map (galW l (g : GQ l)) = (Y1 * P₀).map (galW l (g : GQ l)) := by rw [hY']
    rw [hgmul, hY1, hgmul, hgzW, hgP] at h
    have hs : ((l : WCb l) ^ m • Y').map (galW l (g : GQ l)) = (l : WCb l) ^ m • Y'.map (galW l (g : GQ l)) := by
      ext i j; simp
    apply hcancel
    rw [← Matrix.mul_smul, ← hs, h, hY', hY1]
    calc zW (ρ'' g) * (zW f.adjugate * F.T.map (galW l (g : GQ l)) * P₀)
        = zW (ρ'' g) * zW f.adjugate * F.T.map (galW l (g : GQ l)) * P₀ := by simp only [Matrix.mul_assoc]
      _ = zW f.adjugate * (zW (ρ g) * F.T.map (galW l (g : GQ l))) * P₀ := by
          rw [hcomm]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [F.fix g hfix]
  obtain ⟨A'', hA'', hφ'⟩ := hφ
  have hunit : IsUnit Y' := GlobalTheory.SatInvUnit.isUnit_of_saturated l K bk d Y' A'' hY'det hA'' hφ' hg hsat
  set Ti := F.T⁻¹ with hTi'
  have hTi : Ti * F.T = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 F.unit)
  have hTTi : F.T * Ti = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 F.unit)
  refine ⟨Y', Ti * zW f * Y', hunit, fun i j => ?_, ?_⟩
  · have hP : (l : WCb l) ^ m • (Ti * zW f * Y') = algebraMap ℤ_[l] (WCb l) f.det • P₀ := by
      rw [← Matrix.mul_smul, hY', hY1]
      calc Ti * zW f * (zW f.adjugate * F.T * P₀) = Ti * (zW f * zW f.adjugate) * F.T * P₀ := by
            simp only [Matrix.mul_assoc]
        _ = _ := by
            rw [hfadj, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.smul_mul, hTi, Matrix.one_mul]
    have := congrFun (congrFun hP i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at this
    refine GlobalTheory.SatLattice.sat_pow bk.OE hl0 hsat1 m _ ?_
    rw [this]
    exact bk.OE.mul_mem (algebraMap_mem_OE bk _) (hP₀ i j)
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hTTi, Matrix.one_mul]

end GlobalTheory.EtBasis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralWittLatticeBasisStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integralWittLattice_basis : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (Y1 : Matrix (Fin d) (Fin d) (WCb l)), Y1.det ≠ 0 → ∃ (m : ℕ) (P Y' : Matrix (Fin d) (Fin d) (WCb l)), (∀ i j, P i j ∈ bk.OE) ∧ P.det ≠ 0 ∧ (l : WCb l) ^ m • Y' = Y1 * P ∧ (∀ v : Fin d → WCb l, (∀ i, v i ∈ bk.OE) → ∀ n : ℕ, (∀ i, (l : WCb l) ^ n ∣ (Y1 *ᵥ v) i) → ∃ w : Fin d → WCb l, (∀ i, w i ∈ bk.OE) ∧ (l : WCb l) ^ m • v = (l : WCb l) ^ n • (P *ᵥ w)) ∧ ∀ w : Fin d → WCb l, (∀ i, w i ∈ bk.OE) → (∀ i, (l : WCb l) ∣ (Y' *ᵥ w) i) → ∀ i, (l : WCb l) ∣ w i := by
  first | exact @GlobalTheory.SatLattice.exists_lattice_basis | exact GlobalTheory.SatLattice.exists_lattice_basis | (intros; apply GlobalTheory.SatLattice.exists_lattice_basis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPhiContractionDiscStepStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_phiContraction_disc_step : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A] (s : bk.S →+* A) (ι : Type), TopBasis s bk.J ι → ∀ (φ : A →+* A), φ (s X) = s X ^ l → ∀ (Φ : Disc l (s X) bk.ρ₀ →+* Disc l (s X) bk.ρ₀), IsDiscMap φ Φ → ∀ (κ : Type) (c : κ → κ → A), (∀ i (n : ℕ), {j | c i j ∉ (bk.J ^ n).map s}.Finite) → ∀ (h : ℕ) (V : κ → Disc l (s X) bk.ρ₀), (∀ j, HasSum (fun i => Φ (V i) * toDisc l (s X) bk.ρ₀ (c i j)) (toDisc l (s X) bk.ρ₀ (s bk.E) ^ h * V j)) → ∀ (ρ ρ' : ℝ≥0), bk.ρ₀ ≤ ρ → ρ < 1 → ρ' ^ l = ρ → ∀ (R : Disc l (s X) ρ →+* Disc l (s X) bk.ρ₀) (R' : Disc l (s X) ρ' →+* Disc l (s X) bk.ρ₀), IsDiscMap (RingHom.id A) R → IsDiscMap (RingHom.id A) R' → ∀ (U : κ → Disc l (s X) ρ) (C : ℝ), 0 ≤ C → Filter.Tendsto U Filter.cofinite (nhds 0) → (∀ j, R (U j) = V j) → (∀ j, ‖U j‖ ≤ C) → ∃ U' : κ → Disc l (s X) ρ', Filter.Tendsto U' Filter.cofinite (nhds 0) ∧ (∀ j, R' (U' j) = V j) ∧ ∀ j, (ρ' : ℝ) ^ (bk.Ep.natDegree * h) * ‖U' j‖ ≤ C := by
  first | exact @GlobalTheory.BSP.exists_discStep | exact GlobalTheory.BSP.exists_discStep | (intros; apply GlobalTheory.BSP.exists_discStep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTameFieldGoodLatticePotentiallyCrystallineStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tameField_goodLattice_potentiallyCrystalline : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → a = (l - 1).factorial → ∀ (K' : FinExt l) (h : (Formalism.MainNotions.ElementDenominator.qlExt l).1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : Gl l) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)).actB g (algebraMap ↥(K0 K') Pl.R.B c) = algebraMap ↥(K0 K') Pl.R.B c') (Sig : Finset ((pc Pl h hN hF hS).Iner →* (↥LL.1)ˣ)) (Fr : Gl l) (N : ℕ), (pc Pl h hN hF hS).IsFrob Fr → FrobStable (pc Pl h hN hF hS).Iner Fr Sig → 1 ∈ Sig → Sig.card ≤ N → N < l → (∀ χ ∈ Sig, ∀ g : (pc Pl h hN hF hS).Iner, (g : Gl l) ∈ (pc Pl h hN hF hS).H → χ g = 1) → (∀ χ ∈ Sig, Nat.Coprime (orderOf χ) l) → ∃ Sig' : Finset (ZMod e), (∀ c ∈ Sig', (l : ZMod e) * c ∈ Sig') ∧ (0 : ZMod e) ∈ Sig' ∧ Sig'.card ≤ N ∧ maxPeriod l Sig' = Formalism.MainNotions.ElementDenominator.rPrime (pc Pl h hN hF hS).Iner Fr Sig ∧ ∀ T : QLat LL, (pc Pl h hN hF hS).IsPotCrys T.ρ → (pc Pl h hN hF hS).InertiaThrough T.ρ Sig → IsCrys (Pl.PD (ϖ.field a)) (resF T (ϖ.field a)).ρ ∧ TameType a ϖ Pl T Sig' := by
  first | exact @GlobalTheory.GoodLatt.main | exact GlobalTheory.GoodLatt.main | (intros; apply GlobalTheory.GoodLatt.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWachFunctorComparisonOfBhattScholzeStatement
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_wachFunctor_comparison_of_bhattScholze : GlobalTheory.Published.BhattScholzeIntegral → ∀ D : D7, ∃ (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), Nonempty (CmpOf D.loc D.locA HW F) := by
  first | exact @GlobalTheory.HWL.exists_hw_fon_cmp_of_integral | exact GlobalTheory.HWL.exists_hw_fon_cmp_of_integral | (intros; apply GlobalTheory.HWL.exists_hw_fon_cmp_of_integral <;> assumption)
end

