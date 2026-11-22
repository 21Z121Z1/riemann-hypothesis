import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1904
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1809
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1802
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1873
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1914
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1876
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1902
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1897
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0005
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0318
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCosetOfIsTensor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoefficientBound
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0575
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0501
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0325
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateRowBoundOfDictionary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1864
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1903
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1679

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedIntegersStableSubgroupEqDoubleOrthogonal
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
open scoped GlobalTheory.VacAny

namespace GlobalTheory.LatticeDual

theorem exists_integral_form_separating {R K : Type} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] [Field K] [Algebra R K] [IsFractionRing R K] {κ : Type} [Fintype κ]
    (M : Submodule R (κ → K)) (hM : M.FG) (z : K) (hz : z ∉ (algebraMap R K).range)
    (t : κ → K) (ht : t ∉ M) :
    ∃ y : κ → K, (∀ s ∈ M, s ⬝ᵥ y ∈ (algebraMap R K).range) ∧ t ⬝ᵥ y ∉ (algebraMap R K).range := by
  classical
  haveI : Module.Finite R M := Module.Finite.iff_fg.mpr hM
  haveI : Module.Free R M := Module.free_of_finite_type_torsion_free'
  let b := Module.Free.chooseBasis R M
  let ι := Module.Free.ChooseBasisIndex R M
  let a : ι → (κ → K) := fun i => (b i : κ → K)
  have hliR : LinearIndependent R a := b.linearIndependent.map' M.subtype (Submodule.ker_subtype M)
  have hli : LinearIndependent K a := (LinearIndependent.iff_fractionRing R K).mp hliR
  let B := Module.Basis.sumExtend hli
  have hfin : Finite (ι ⊕ Module.Basis.sumExtendIndex hli) := Module.Finite.finite_basis B
  have : Finite (Module.Basis.sumExtendIndex hli) :=
    Finite.of_injective (Sum.inr : _ → ι ⊕ _) Sum.inr_injective
  have : Fintype (Module.Basis.sumExtendIndex hli) := Fintype.ofFinite _
  have hB : ∀ i, B (Sum.inl i) = a i := by
    intro i
    simp only [B, Module.Basis.sumExtend, Module.Basis.reindex_apply, Module.Basis.coe_extend,
      Equiv.symm_symm, Equiv.trans_apply, Equiv.sumCongr_apply]
    rfl

  have key : ∀ f : (κ → K) →ₗ[K] K, (∀ i, f (a i) ∈ (algebraMap R K).range) →
      ∀ s ∈ M, f s ∈ (algebraMap R K).range := by
    intro f hf s hs
    have hs' : s = ∑ i, b.repr ⟨s, hs⟩ i • a i := by
      have := congrArg Subtype.val (b.sum_repr ⟨s, hs⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at this
      exact this.symm
    rw [hs', map_sum]
    refine Subring.sum_mem _ fun i _ => ?_
    rw [f.map_smul_of_tower]
    obtain ⟨r, hr⟩ := hf i
    exact ⟨b.repr ⟨s, hs⟩ i * r, by rw [map_mul, hr, Algebra.smul_def]⟩

  have dot : ∀ f : (κ → K) →ₗ[K] K, ∃ y : κ → K, ∀ x, x ⬝ᵥ y = f x := by
    intro f
    refine ⟨fun k => f (fun j => if k = j then 1 else 0), fun x => ?_⟩
    rw [LinearMap.pi_apply_eq_sum_univ f x]
    simp [dotProduct, smul_eq_mul]
  suffices h : ∃ f : (κ → K) →ₗ[K] K, (∀ i, f (a i) ∈ (algebraMap R K).range) ∧
      f t ∉ (algebraMap R K).range by
    obtain ⟨f, hf, hft⟩ := h
    obtain ⟨y, hy⟩ := dot f
    exact ⟨y, fun s hs => (hy s).symm ▸ key f hf s hs, (hy t).symm ▸ hft⟩
  by_cases h1 : ∃ i, B.repr t (Sum.inl i) ∉ (algebraMap R K).range
  · obtain ⟨i, hi⟩ := h1
    refine ⟨B.coord (Sum.inl i), fun i' => ?_, by simpa using hi⟩
    rw [← hB, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs
    · exact ⟨1, map_one _⟩
    · exact ⟨0, map_zero _⟩
  by_cases h2 : ∃ j, B.repr t (Sum.inr j) ≠ 0
  · obtain ⟨j, hj⟩ := h2
    refine ⟨(z / B.repr t (Sum.inr j)) • B.coord (Sum.inr j), fun i => ?_, ?_⟩
    · rw [LinearMap.smul_apply, ← hB, Module.Basis.coord_apply, Module.Basis.repr_self,
        Finsupp.single_apply, if_neg Sum.inl_ne_inr, smul_zero]
      exact ⟨0, map_zero _⟩
    · rw [LinearMap.smul_apply, Module.Basis.coord_apply, smul_eq_mul, div_mul_cancel₀ _ hj]
      exact hz
  push_neg at h1 h2
  choose c hc using h1
  exfalso
  apply ht
  have htc : t = ∑ i, c i • a i := by
    conv_lhs => rw [← B.sum_repr t]
    rw [Fintype.sum_sum_type]
    simp [h2, hB, ← hc, algebraMap_smul]
  rw [htc]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (b i).2

end GlobalTheory.LatticeDual

namespace GlobalTheory.LatticeDual

theorem mem_of_mem_doubleOrth : ∀ (F : Type) [Field F] [NumberField F] (v : Pl F) (κ : Type) [Fintype κ] (ψ₀ : AddChar (Fv F v) ℂ),
    (∀ x : Fv F v, (∀ y ∈ HeightOneSpectrum.adicCompletionIntegers F v, ψ₀ (x * y) = 1) ↔ x ∈ HeightOneSpectrum.adicCompletionIntegers F v) →
    ∀ A : AddSubgroup (κ → Fv F v), (∀ c ∈ HeightOneSpectrum.adicCompletionIntegers F v, ∀ t ∈ A, c • t ∈ A) →
    (∃ c : Fv F v, c ≠ 0 ∧ ∀ t ∈ A, ∀ k, c * t k ∈ HeightOneSpectrum.adicCompletionIntegers F v) →
    ∀ t : κ → Fv F v, (∀ y : κ → Fv F v, (∀ s ∈ A, ψ₀ (s ⬝ᵥ y) = 1) → ψ₀ (t ⬝ᵥ y) = 1) → t ∈ A := by
  intro F _ _ v κ _ ψ₀ hψ A hA hbd t ht
  classical
  let O := HeightOneSpectrum.adicCompletionIntegers F v
  have hrange : ∀ x : Fv F v, x ∈ (algebraMap O (Fv F v)).range ↔ x ∈ O :=
    fun x => ⟨fun ⟨r, hr⟩ => hr ▸ r.2, fun h => ⟨⟨x, h⟩, rfl⟩⟩
  have hψO : ∀ x ∈ O, ψ₀ x = 1 := fun x hx => by
    simpa using (hψ 1).mpr (one_mem _) x hx

  let M : Submodule O (κ → Fv F v) :=
    { carrier := A
      add_mem' := fun h h' => A.add_mem h h'
      zero_mem' := A.zero_mem
      smul_mem' := fun c x hx => hA _ c.2 x hx }
  obtain ⟨c, hc0, hc⟩ := hbd

  let N : Submodule O (κ → Fv F v) :=
    Submodule.span O (Set.range fun k : κ => c⁻¹ • (Pi.single k 1 : κ → Fv F v))
  have hN : N.FG := Submodule.fg_span (Set.finite_range _)
  have hMN : M ≤ N := by
    intro s hs
    have hs' : s = ∑ k, (⟨c * s k, hc s hs k⟩ : O) • (c⁻¹ • (Pi.single k 1 : κ → Fv F v)) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
      show s j = c * s j * c⁻¹
      rw [mul_comm c, mul_inv_cancel_right₀ hc0]
    rw [hs']
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  have hMfg : M.FG := by
    haveI := isNoetherian_of_fg_of_noetherian N hN
    have h1 : (M.comap N.subtype).FG := IsNoetherian.noetherian _
    have h2 := h1.map N.subtype
    rwa [Submodule.map_comap_subtype, inf_eq_right.mpr hMN] at h2

  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hϖ0 : (ϖ : Fv F v) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have hz : (ϖ : Fv F v)⁻¹ ∉ (algebraMap O (Fv F v)).range := by
    rw [hrange]
    intro h
    apply hϖ.not_isUnit
    refine isUnit_iff_exists_inv.mpr ⟨⟨_, h⟩, Subtype.ext ?_⟩
    simp [hϖ0]
  by_contra htA
  obtain ⟨y', hyA, hyt⟩ := exists_integral_form_separating M hMfg _ hz t htA
  simp only [hrange] at hyA hyt
  obtain ⟨b, hb, hbψ⟩ : ∃ b ∈ O, ψ₀ ((t ⬝ᵥ y') * b) ≠ 1 := by
    by_contra h
    push_neg at h
    exact hyt ((hψ _).mp h)
  apply hbψ
  have := ht (b • y') (fun s hs => by
    rw [dotProduct_smul, smul_eq_mul, mul_comm]
    exact hψO _ (mul_mem (hyA s hs) hb))
  rwa [dotProduct_smul, smul_eq_mul, mul_comm] at this

end GlobalTheory.LatticeDual
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxProductDiagonalFunctionalNeZero
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LatVac
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open MeasureTheory

noncomputable section

namespace GlobalTheory.DiagTens

attribute [local instance] GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele
  GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField
  GlobalTheory.DiagForm.measAf GlobalTheory.DiagForm.borelAf

theorem finprod_indicator {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (y : κ → FiniteAdeleRing (𝓞 F) F) :
    (∏ᶠ w : Pl F, Set.indicator {x : κ → Fv F w | ∀ i, x i ∈ w.adicCompletionIntegers F} (1 : (κ → Fv F w) → ℂ)
      (fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w (y i))) =
    (Set.univ.pi fun _ : κ => {x : FiniteAdeleRing (𝓞 F) F | ∀ w : Pl F, x w ∈ w.adicCompletionIntegers F}).indicator
      (fun _ => (1 : ℂ)) y := by
  by_cases h : ∀ i (w : Pl F), y i w ∈ w.adicCompletionIntegers F
  · rw [Set.indicator_of_mem (show y ∈ (Set.univ.pi fun _ : κ => {x : FiniteAdeleRing (𝓞 F) F | ∀ w : Pl F, x w ∈ w.adicCompletionIntegers F}) from Set.mem_univ_pi.2 fun i => h i)]
    refine finprod_eq_one_of_forall_eq_one fun w => ?_
    rw [Set.indicator_of_mem (show (fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w (y i)) ∈
      {x : κ → Fv F w | ∀ i, x i ∈ w.adicCompletionIntegers F} from fun i => h i w)]
    rfl
  · rw [Set.indicator_of_notMem (show y ∉ (Set.univ.pi fun _ : κ => {x : FiniteAdeleRing (𝓞 F) F | ∀ w : Pl F, x w ∈ w.adicCompletionIntegers F}) from fun hy => h fun i => Set.mem_univ_pi.1 hy i)]
    push_neg at h
    obtain ⟨i₀, w₀, hw₀⟩ := h
    have hfin : (Function.mulSupport fun w : Pl F => Set.indicator
        {x : κ → Fv F w | ∀ i, x i ∈ w.adicCompletionIntegers F} (1 : (κ → Fv F w) → ℂ)
        (fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w (y i))).Finite := by
      have hx : ∀ᶠ w in Filter.cofinite, ∀ i, (y i) w ∈ w.adicCompletionIntegers F := by
        rw [Filter.eventually_all]
        intro i
        exact (y i).2
      refine Set.Finite.subset (Filter.eventually_cofinite.1 hx) ?_
      intro w hw hw'
      apply hw
      show Set.indicator _ _ _ = _
      rw [Set.indicator_of_mem (show (fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w (y i)) ∈
        {x : κ → Fv F w | ∀ i, x i ∈ w.adicCompletionIntegers F} from hw')]
      rfl
    refine finprod_eq_zero _ w₀ ?_ hfin
    exact Set.indicator_of_notMem (show (fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w₀ (y i)) ∉
      {x : κ → Fv F w₀ | ∀ i, x i ∈ w₀.adicCompletionIntegers F} from fun hy => hw₀ (hy i₀)) _

theorem lDiag_box_tens_ne : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (v : Pl F), ∃ φ₀ ∈ SB (κ → Fv F v), boxFun φ₀ φ₀ ∈ SB (κ ⊕ κ → Fv F v) ∧
    ∃ R R' : (κ → AF F) → ℂ, (∀ φ ∈ SB (κ → Fv F v), Rest (evFin F v) φ R ∧ Rest (evFin F v) φ R') ∧
      GlobalTheory.DiagForm.lDiag F κ (boxFun (tens (evFin F v) φ₀ R) (tens (evFin F v) φ₀ R')) ≠ 0 := by
  intro F _ _ κ _ v
  classical
  obtain ⟨hO, hK⟩ := PI.IntAdCpctOpenWork.main F
  set O := {x : FiniteAdeleRing (𝓞 F) F | ∀ w : HeightOneSpectrum (𝓞 F), x w ∈ w.adicCompletionIntegers F} with hOdef
  let b : ContDiffBump (0 : κ → mixedEmbedding.mixedSpace F) := ⟨1, 2, one_pos, one_lt_two⟩
  have hc : HasCompactSupport (fun x => ((b x : ℝ) : ℂ)) := b.hasCompactSupport.comp_left Complex.ofReal_zero
  have hd : ContDiff ℝ (⊤ : ℕ∞) (fun x => ((b x : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp b.contDiff
  let f : SInf F κ := hc.toSchwartzMap hd
  have hf : ∀ x, f x = ((b x : ℝ) : ℂ) := fun x => rfl
  let φs : ∀ w : Pl F, (κ → Fv F w) → ℂ := fun w => Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1
  have hstd : ∀ᶠ w in Filter.cofinite, φs w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 :=
    Filter.Eventually.of_forall fun _ => rfl
  obtain ⟨r, hr, hrt⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φs hstd
  have hRest : ∀ φ ∈ SB (κ → Fv F v), Rest (evFin F v) φ r := fun φ hφ => ⟨hr, by
    rw [hrt φ]
    refine GlobalTheory.TensUniq.pure_mem_schA f _ (fun w => ?_) (GlobalTheory.PureFactor.update_eventually φs v φ hstd)
    by_cases hw : w = v
    · subst hw; rw [Function.update_self]; exact hφ
    · rw [Function.update_of_ne hw]; exact GlobalTheory.StdVacuum.indicator_mem_SB w⟩
  have h0 : φs v ∈ SB (κ → Fv F v) := GlobalTheory.StdVacuum.indicator_mem_SB v
  refine ⟨φs v, h0, ?_, r, r, fun φ hφ => ⟨hRest φ hφ, hRest φ hφ⟩, ?_⟩
  · have e : boxFun (φs v) (φs v) = Set.indicator {x : κ ⊕ κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
      funext x
      simp only [boxFun, φs, Set.indicator_apply, Set.mem_setOf_eq, Function.comp_apply, Sum.forall, Pi.one_apply]
      split_ifs <;> simp_all
    rw [e]; exact GlobalTheory.StdVacuum.indicator_mem_SB v
  · set V : Set (GlobalTheory.DiagForm.Vf F κ) := Set.univ.pi fun _ => O with hVdef
    set g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ := V.indicator fun _ => (1 : ℂ) with hgdef
    have hΦ : tens (evFin F v) (φs v) r = pureA F f g := by
      rw [hrt, Function.update_eq_self]
      funext x
      show f _ * _ = f _ * _
      congr 1
      exact finprod_indicator _
    have hΦs : tens (evFin F v) (φs v) r ∈ schA F κ := (hRest _ h0).2
    have hbox := GlobalTheory.SchwartzBox.boxFun_mem_schA F κ κ _ hΦs _ hΦs
    have hint := GlobalTheory.DiagForm.integrable_resD hbox
    have hres : GlobalTheory.DiagForm.resD F κ (boxFun (tens (evFin F v) (φs v) r) (tens (evFin F v) (φs v) r)) =
        fun p => ((b (GlobalTheory.DiagForm.eI F κ p.1) * b (GlobalTheory.DiagForm.eI F κ p.1) : ℝ) : ℂ) * (g p.2 * g p.2) := by
      rw [hΦ]
      funext p
      show pureA F f g _ * pureA F f g _ = _
      have e1 : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((GlobalTheory.DiagForm.glue p) i).1) =
          GlobalTheory.DiagForm.eI F κ p.1 := by
        funext i; simp [GlobalTheory.DiagForm.glue]
      have e2 : (fun i => ((GlobalTheory.DiagForm.glue p) i).2) = p.2 := rfl
      simp only [pureA, Function.comp_def, Sum.elim_inl, Sum.elim_inr]
      rw [e1, e2, hf]
      push_cast
      ring
    rw [GlobalTheory.DiagForm.lDiag, LinearMap.comp_apply, GlobalTheory.DiagForm.Lext_apply _ hint, hres, GlobalTheory.DiagForm.mu,
      integral_prod_mul (fun u => ((b (GlobalTheory.DiagForm.eI F κ u) * b (GlobalTheory.DiagForm.eI F κ u) : ℝ) : ℂ))
        (fun y => g y * g y)]
    have h0O : (0 : FiniteAdeleRing (𝓞 F) F) ∈ O := fun w => (w.adicCompletionIntegers F).zero_mem
    have hVo : IsOpen V := isOpen_set_pi Set.finite_univ fun _ _ => hO
    have hVc : IsCompact V := isCompact_univ_pi fun _ => hK
    have hgg : (fun y => g y * g y) = V.indicator fun _ => (1 : ℂ) := by
      funext y
      simp only [hgdef, Set.indicator_apply]
      split_ifs <;> simp
    have hc2 : (∫ y, g y * g y ∂(Measure.addHaar : Measure (GlobalTheory.DiagForm.Vf F κ))) ≠ 0 := by
      rw [hgg, integral_indicator_const _ hVo.measurableSet]
      have hpos : 0 < (Measure.addHaar : Measure (GlobalTheory.DiagForm.Vf F κ)) V := hVo.measure_pos _ ⟨0, fun i _ => h0O⟩
      have hfin : (Measure.addHaar : Measure (GlobalTheory.DiagForm.Vf F κ)) V < ⊤ := hVc.measure_lt_top
      have : 0 < (Measure.addHaar : Measure (GlobalTheory.DiagForm.Vf F κ)).real V := ENNReal.toReal_pos hpos.ne' hfin.ne
      simpa using this.ne'
    have hc1 : (∫ u, ((b (GlobalTheory.DiagForm.eI F κ u) * b (GlobalTheory.DiagForm.eI F κ u) : ℝ) : ℂ)
        ∂(volume : Measure (GlobalTheory.DiagForm.Vi F κ))) ≠ 0 := by
      rw [integral_complex_ofReal]
      have hcs1 : HasCompactSupport fun u : GlobalTheory.DiagForm.Vi F κ => b (GlobalTheory.DiagForm.eI F κ u) :=
        b.hasCompactSupport.comp_homeomorph (GlobalTheory.DiagForm.eI F κ).toHomeomorph
      have hcs : HasCompactSupport fun u : GlobalTheory.DiagForm.Vi F κ =>
          b (GlobalTheory.DiagForm.eI F κ u) * b (GlobalTheory.DiagForm.eI F κ u) := hcs1.mul_right
      have hcont : Continuous fun u : GlobalTheory.DiagForm.Vi F κ =>
          b (GlobalTheory.DiagForm.eI F κ u) * b (GlobalTheory.DiagForm.eI F κ u) :=
        (b.continuous.comp (GlobalTheory.DiagForm.eI F κ).continuous).mul (b.continuous.comp (GlobalTheory.DiagForm.eI F κ).continuous)
      have hpos := hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero
        (μ := (volume : Measure (GlobalTheory.DiagForm.Vi F κ))) (x := 0) hcs (fun u => mul_nonneg b.nonneg b.nonneg) (by
          simp only [map_zero]
          rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)]
          norm_num)
      exact_mod_cast hpos.ne'
    exact mul_ne_zero hc1 hc2

end GlobalTheory.DiagTens
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterPartitionOfUnitySupportStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_partition_of_unity_support : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → ∀ (C K : Set (κ → Af F)), IsCompact C → IsOpen K → (0 : κ → Af F) ∈ K →
    ∀ y : κ → AF F, ∃ (s : Finset (κ → AF F)) (c : (κ → AF F) → ℂ), (∀ b ∈ s, ∀ i, (b i).1 = 0) ∧
      ∑ b ∈ s, c b * ψ (y ⬝ᵥ b) = 1 ∧
      ∀ x : κ → AF F, (fun i => (x i).2) ∈ C → (∀ k ∈ K, (fun i => (x i).2) ≠ (fun i => (y i).2) + k) →
        ∑ b ∈ s, c b * ψ (x ⬝ᵥ b) = 0 := by
  first | exact @GlobalTheory.FinCharCut.fin_char_cut | exact GlobalTheory.FinCharCut.fin_char_cut | (intros; apply GlobalTheory.FinCharCut.fin_char_cut <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffPlaceValuationResidueFieldCardEqZeroOfNotMe
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RowTest GlobalTheory.SumSize GlobalTheory.RowClaim
open Formalism.DivisionValues (vw lw)
open MeasureTheory ValuativeRel GlobalTheory.UnfoldLoss

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.UnfoldLoss.ResCardAway

theorem absNorm_eq_plc_pow {K : Type} [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K)) :
    ∃ n : ℕ, Ideal.absNorm P.asIdeal = ringChar (𝓞 K ⧸ P.asIdeal) ^ n := by
  classical
  haveI : P.asIdeal.IsMaximal := P.isMaximal
  letI : Field (𝓞 K ⧸ P.asIdeal) := Ideal.Quotient.field _
  haveI : Finite (𝓞 K ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
  letI : Fintype (𝓞 K ⧸ P.asIdeal) := Fintype.ofFinite _
  obtain ⟨n, -, hn⟩ := FiniteField.card (𝓞 K ⧸ P.asIdeal) (ringChar (𝓞 K ⧸ P.asIdeal))
  refine ⟨n, ?_⟩
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  exact hn

theorem vw_resCard_eq_zero : ∀ {D : D7} (P : Pl D.host.E) (w : PlL D),
    ((Formalism.EigenvalueLevelCeiling.plc P : ℕ) : 𝓞 D.what₂.LL) ∉ w.asIdeal →
    vw w ((resCard (Kw P) : ℕ) : D.what₂.LL) = 0 := by
  intro D P w h
  obtain ⟨n, hn⟩ := absNorm_eq_plc_pow P
  have hq : resCard (Kw P) = Formalism.EigenvalueLevelCeiling.plc P ^ n :=
    (ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.ResCardPlace.resCard_Kw P).trans hn
  have hnot : ((resCard (Kw P) : ℕ) : 𝓞 D.what₂.LL) ∉ w.asIdeal := by
    rw [hq, Nat.cast_pow]
    exact fun hm => h (w.isPrime.mem_of_pow_mem n hm)
  letI : StarRing D.what₂.LL := starRingOfComm
  have := Formalism.DivisionValues.ValuationZeroReduction.vw_eq_zero_of_not_mem w _ hnot
  simpa using this

end GlobalTheory.UnfoldLoss.ResCardAway
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffValuationLossLeAddCharNegUnfoldingPhase
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RowTest GlobalTheory.SumSize GlobalTheory.RowClaim
open Formalism.DivisionValues (vw lw)
open MeasureTheory ValuativeRel GlobalTheory.UnfoldLoss

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.UnfoldLoss

theorem isOfFinOrder_of_hasConductor {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {ψ : AddChar k Circle} {c : kˣ} (h : HasConductor ψ c) (a : k) : IsOfFinOrder (ψ a) := by
  have hn : ∀ n : ℕ, valuation k (n : k) ≤ 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.cast_succ]
      exact (valuation k).map_add_le ih (by simp)

  have hc : ∀ y : k, valuation k y ≤ valuation k (c : k) → ψ y = 1 := (h c).2 le_rfl
  have hc0 : valuation k (c : k) ≠ 0 := by simp
  set γ : (ValueGroupWithZero k)ˣ := Units.mk0 _ hc0 with hγ

  obtain ⟨t, -, ht⟩ := (IsNonarchimedeanLocalField.isCompact_closedBall k (valuation k a)).elim_nhds_subcover
    (fun x => {z | valuation k (z - x) < γ}) (fun x _ => by
      rw [IsValuativeTopology.mem_nhds_iff']
      exact ⟨γ, subset_rfl⟩)
  have hmem : ∀ n : ℕ, ∃ x : t, valuation k ((n : k) * a - x) < γ := by
    intro n
    have : (n : k) * a ∈ {x | valuation k x ≤ valuation k a} := by
      simp only [Set.mem_ofPred_eq, map_mul]
      calc valuation k (n : k) * valuation k a ≤ 1 * valuation k a := by gcongr; exact hn n
        _ = valuation k a := one_mul _
    obtain ⟨x, hx⟩ := Set.mem_iUnion₂.mp (ht this)
    exact ⟨⟨x, hx.1⟩, hx.2⟩
  choose f hf using hmem

  obtain ⟨n, m, hnm, hfnm⟩ := Finite.exists_ne_map_eq_of_infinite f
  have hdiff : valuation k ((n : k) * a - (m : k) * a) ≤ valuation k (c : k) := by
    have h1 := hf n
    have h2 := hf m
    rw [hfnm] at h1
    have : (n : k) * a - (m : k) * a = ((n : k) * a - (f m : k)) - ((m : k) * a - (f m : k)) := by ring
    rw [this]
    refine le_of_lt ?_
    calc valuation k (((n : k) * a - (f m : k)) - ((m : k) * a - (f m : k)))
        ≤ max (valuation k ((n : k) * a - (f m : k))) (valuation k ((m : k) * a - (f m : k))) :=
          (valuation k).map_sub _ _
      _ < γ := max_lt h1 h2
  have hpow : ψ a ^ n = ψ a ^ m := by
    have := hc _ hdiff
    rw [AddChar.map_sub_eq_div, div_eq_one, ← nsmul_eq_mul, ← nsmul_eq_mul,
      AddChar.map_nsmul_eq_pow, AddChar.map_nsmul_eq_pow] at this
    exact this
  rw [isOfFinOrder_iff_pow_eq_one]
  rcases Nat.lt_or_gt_of_ne hnm with hlt | hlt
  · refine ⟨m - n, Nat.sub_pos_of_lt hlt, ?_⟩
    rw [pow_sub _ hlt.le, ← hpow, mul_inv_cancel]
  · refine ⟨n - m, Nat.sub_pos_of_lt hlt, ?_⟩
    rw [pow_sub _ hlt.le, hpow, mul_inv_cancel]

theorem lossLe_psi_neg_phase : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A) (CF b : ℝ),
    HidaSetting large₂ R F → ch.Is → ch.AtScale CF b → ch.FieldOK → ∀ (t : T) (Φ : ch.G.Datum), ∀ β ∈ ch.S.supp t Φ, ∀ (P : locPl ch.G t), ∀ X Y (e : Vars (locGrid ch.G t P)),
    (ch.S.term t Φ β P).datum X Y ≠ 0 →
    moved (locGrid ch.G t P) (keepAt ch.G P) ((repsAt ch.G t P).elt (β P)) (Tflip ch.W ch.S.B t Φ P) (fill one_le_sLen X Y e) ≠ 0 →
    ∀ w : PlL D, LossLe w ((psiAt ch.W P.1 (-phase X e) : Circle) : ℂ) 0 := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch large₂ F CF b hS hIs _ hF t Φ β hβ P X Y e hd hm w

  obtain ⟨y, hy⟩ := hF.phases t Φ β hβ P X Y e hd hm

  have hcond : HasConductor (psiAt ch.W P.1) 1 :=
    GlobalTheory.FunObj.Good.hasConductor_psiAt ch.W
      (GlobalTheory.FunObj.Good.badInt_notMem hS.core.lev (GlobalTheory.FlipIntegrand.pde_ne_q_of_setting hS) (hIs.guard t) P.2)
  obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp (isOfFinOrder_of_hasConductor hcond (-phase X e))
  have hneg : ((psiAt ch.W P.1 (-phase X e) : Circle) : ℂ) = D.what₂.embLL y⁻¹ := by
    rw [AddChar.map_neg_eq_inv, Circle.coe_inv, map_inv₀, hy]
  refine ⟨y⁻¹, hneg.symm, Or.inr ?_⟩
  have hroot : y⁻¹ ^ n = 1 := by
    apply D.what₂.embLL.injective
    rw [map_pow, ← hneg, ← Circle.coe_pow, hpow, Circle.coe_one, map_one]
  have h0 : (n : ℤ) * Formalism.DivisionValues.vw w y⁻¹ = 0 := by
    unfold Formalism.DivisionValues.vw
    rw [← FractionalIdeal.count_pow, FractionalIdeal.spanSingleton_pow, hroot,
      FractionalIdeal.spanSingleton_one, FractionalIdeal.count_one]
  have hv : Formalism.DivisionValues.vw w y⁻¹ = 0 := (mul_eq_zero.mp h0).resolve_left (by exact_mod_cast hn.ne')
  simp [hv]

end GlobalTheory.UnfoldLoss
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateRowBoundOfDictionaryStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_row_bound_of_dictionary : GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → DictK → DepthK → ∀ C1 : ℝ, 0 < C1 → BigC fun _ ch C b => ConjRowAt ch C b C1 := by
  first | exact @GlobalTheory.KerConjRow.conjRowK | exact GlobalTheory.KerConjRow.conjRowK | (intros; apply GlobalTheory.KerConjRow.conjRowK <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVectorBlockLevelUnimodularEigenStatement
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cosetVector_blockLevel_unimodular_eigen : ∀ (D : D7) (δ t0 : ℂ) (hc : Crv D ⊤ δ) (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0) (a d : ℕ) (hd : Even d) (e0 : VC D a d → ℂ) (hv : oddE0 D ⊤ δ t0 a d e0) (W : WeilO D ⊤ δ a d e0) (hep : W.ep = 1) (hep' : W.ep' = 1) (𝔪 : Ideal (𝓞 D.host.E)) (hm : 𝔪 ≠ ⊥) (hcop : 𝔪 ⊔ D.host.conj • 𝔪 = ⊤) (hcond : ∀ u : (AE D)ˣ, IntU D u → (u : AE D) - 1 ∈ hatId D (𝔪 * D.host.conj • 𝔪) → W.chV'.f u = 1) (o : ℕ) (ho : o + a = d), ∀ j ∈ GlobalTheory.BotPairSmall.blockJ D 𝔪 o d, ∃ k ∈ intG D a, ∃ c : ℂ, ‖c‖ = 1 ∧ W.Om 1 j (GlobalTheory.BotPairSmall.cvec D δ (D.host.conj • 𝔪) o a d e0) = c • W.Om k 1 (GlobalTheory.BotPairSmall.cvec D δ (D.host.conj • 𝔪) o a d e0) := by
  first | exact @GlobalTheory.BotPairSmall.cvec_eig | exact GlobalTheory.BotPairSmall.cvec_eig | (intros; apply GlobalTheory.BotPairSmall.cvec_eig <;> assumption)
end

