import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0322
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ArchimedeanCompact.OneTmulMemCenter
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.Bundle0004
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.Bundle0005
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualInfinitesimalCharacterRegular
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Bundle0003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0125

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CvCount
section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

open scoped ENNReal in
private theorem sq_on_le {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) [μ.IsMulLeftInvariant]
    {S : Set G} (hS : MeasurableSet S) (N : ℕ) (hN : ∀ x : G, {γ : Γ | (γ : G) * x ∈ S}.encard ≤ N)
    (F : GlobalTheory.AutomorphicL2Unitary.L2 Γ μ) :
    eLpNorm (GlobalTheory.AutomorphicL2Unitary.lift Γ F) 2 (μ.restrict S) ≤ N * eLpNorm F 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) := by
  have hmeasF : AEStronglyMeasurable (GlobalTheory.AutomorphicL2Unitary.lift Γ (F : GlobalTheory.AutomorphicL2Unitary.Quot Γ → ℂ)) μ :=
    GlobalTheory.AutomorphicL2Unitary.aestronglyMeasurable_quotMeasure_iff_lift.mp (Lp.aestronglyMeasurable F)
  have key : ∫⁻ x, ‖GlobalTheory.AutomorphicL2Unitary.lift Γ (F : GlobalTheory.AutomorphicL2Unitary.Quot Γ → ℂ) x‖ₑ ^ (2 : ℝ) ∂(μ.restrict S) ≤
      (N : ℝ≥0∞) * ∫⁻ q, ‖(F : GlobalTheory.AutomorphicL2Unitary.Quot Γ → ℂ) q‖ₑ ^ (2 : ℝ) ∂(GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) := by
    rw [← lintegral_indicator hS, GlobalTheory.AutomorphicL2Unitary.lintegral_eq_lintegral_tsum (Γ := Γ) ((hmeasF.enorm.pow_const _).indicator hS),
      ← lintegral_const_mul' _ _ (ENNReal.natCast_ne_top N)]
    refine lintegral_mono (fun q => ?_)
    have hq : ∀ γ : Γ, S.indicator (fun x => ‖GlobalTheory.AutomorphicL2Unitary.lift Γ (F : GlobalTheory.AutomorphicL2Unitary.Quot Γ → ℂ) x‖ₑ ^ (2 : ℝ))
        ((γ : G) * Quotient.out q) = {γ : Γ | (γ : G) * Quotient.out q ∈ S}.indicator
          (fun _ => ‖(F : GlobalTheory.AutomorphicL2Unitary.Quot Γ → ℂ) q‖ₑ ^ (2 : ℝ)) γ := by
      intro γ
      have hl : GlobalTheory.AutomorphicL2Unitary.lift Γ (F : GlobalTheory.AutomorphicL2Unitary.Quot Γ → ℂ) ((γ : G) * Quotient.out q) =
          (F : GlobalTheory.AutomorphicL2Unitary.Quot Γ → ℂ) q := by
        rw [GlobalTheory.AutomorphicL2Unitary.lift, GlobalTheory.AutomorphicL2Unitary.mk_mul]
        exact congrArg _ (Quotient.out_eq q)
      by_cases h : (γ : G) * Quotient.out q ∈ S
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show γ ∈ {γ : Γ | (γ : G) * Quotient.out q ∈ S} from h), hl]
      · rw [Set.indicator_of_notMem h,
          Set.indicator_of_notMem (show γ ∉ {γ : Γ | (γ : G) * Quotient.out q ∈ S} from h)]
    rw [tsum_congr hq, ← tsum_subtype, ENNReal.tsum_set_const]
    gcongr
    have h1 := ENat.toENNReal_le.mpr (hN (Quotient.out q))
    simpa using h1
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat]
  have hN2 : (N : ℝ≥0∞) ^ (1 / 2 : ℝ) ≤ N := by
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · subst h0
      simp
    · calc (N : ℝ≥0∞) ^ (1 / 2 : ℝ) ≤ (N : ℝ≥0∞) ^ (1 : ℝ) :=
            ENNReal.rpow_le_rpow_of_exponent_le (by exact_mod_cast h0) (by norm_num)
        _ = N := ENNReal.rpow_one _
  calc (∫⁻ x, ‖GlobalTheory.AutomorphicL2Unitary.lift Γ (F : GlobalTheory.AutomorphicL2Unitary.Quot Γ → ℂ) x‖ₑ ^ (2 : ℝ) ∂(μ.restrict S)) ^ (1 / 2 : ℝ)
      ≤ ((N : ℝ≥0∞) * ∫⁻ q, ‖(F : GlobalTheory.AutomorphicL2Unitary.Quot Γ → ℂ) q‖ₑ ^ (2 : ℝ) ∂(GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ)) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow key (by norm_num)
    _ = (N : ℝ≥0∞) ^ (1 / 2 : ℝ) *
        (∫⁻ q, ‖(F : GlobalTheory.AutomorphicL2Unitary.Quot Γ → ℂ) q‖ₑ ^ (2 : ℝ) ∂(GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ)) ^ (1 / 2 : ℝ) :=
        ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
    _ ≤ _ := by gcongr

theorem UpperTheory.V.Cj.H.cvCount :
    UpperTheory.V.Cj.H.CvCount := by
  intro G _ _ _ _ _ _ _ _ Γ _ μ _ _ ψ hψ hψc
  obtain ⟨C0, hC0⟩ := hψ.bounded_above_of_compact_support hψc
  have hC : ∀ z, ‖ψ z‖ ≤ max C0 0 := fun z => (hC0 z).trans (le_max_left _ _)
  have hC' : 0 ≤ max C0 0 := le_max_right _ _
  have hMfin : μ (tsupport ψ)⁻¹ ≠ ⊤ := (hψc.isCompact.inv).measure_lt_top.ne
  refine ⟨max C0 0 * (μ (tsupport ψ)⁻¹).toReal ^ (1 / 2 : ℝ), by positivity, ?_⟩
  intro x N hN F
  have hS : MeasurableSet {y : G | ψ (y⁻¹ * x) ≠ 0} :=
    (isOpen_ne_fun (hψ.comp (continuous_inv.mul continuous_const)) continuous_const).measurableSet
  have hSK : μ {y : G | ψ (y⁻¹ * x) ≠ 0} ≤ μ (tsupport ψ)⁻¹ := by
    calc μ {y : G | ψ (y⁻¹ * x) ≠ 0} ≤ μ ((fun y => x⁻¹ * y) ⁻¹' (tsupport ψ)⁻¹) := by
          refine measure_mono (fun y hy => ?_)
          show (x⁻¹ * y)⁻¹ ∈ tsupport ψ
          rw [_root_.mul_inv_rev, inv_inv]
          exact subset_tsupport _ hy
      _ = μ (tsupport ψ)⁻¹ := measure_preimage_mul μ x⁻¹ _
  have hF := sq_on_le Γ μ hS N hN F
  have hmeas : AEStronglyMeasurable (GlobalTheory.AutomorphicL2Unitary.lift Γ (F : GlobalTheory.AutomorphicL2Unitary.Quot Γ → ℂ)) μ :=
    GlobalTheory.AutomorphicL2Unitary.aestronglyMeasurable_quotMeasure_iff_lift.mp (Lp.aestronglyMeasurable F)
  have hH := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2) (by norm_num)
    (hmeas.restrict (s := {y : G | ψ (y⁻¹ * x) ≠ 0}))
  rw [show (1 / (1 : ENNReal).toReal - 1 / (2 : ENNReal).toReal) = (1 / 2 : ℝ) by norm_num,
    Measure.restrict_apply_univ] at hH
  have hE : ‖cv ψ F x‖ₑ ≤ (N * eLpNorm F 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) * μ (tsupport ψ)⁻¹ ^ (1 / 2 : ℝ)) *
      ENNReal.ofReal (max C0 0) := by
    calc ‖cv ψ F x‖ₑ ≤ ∫⁻ y, ‖GlobalTheory.AutomorphicL2Unitary.lift Γ (F : GlobalTheory.AutomorphicL2Unitary.Quot Γ → ℂ) y * ψ (y⁻¹ * x)‖ₑ ∂μ :=
          enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ y, {y : G | ψ (y⁻¹ * x) ≠ 0}.indicator
            (fun y => ‖GlobalTheory.AutomorphicL2Unitary.lift Γ (F : GlobalTheory.AutomorphicL2Unitary.Quot Γ → ℂ) y‖ₑ) y * ENNReal.ofReal (max C0 0) ∂μ := by
          refine lintegral_mono (fun y => ?_)
          by_cases hy : y ∈ {y : G | ψ (y⁻¹ * x) ≠ 0}
          · rw [Set.indicator_of_mem hy, enorm_mul]
            gcongr
            rw [← ofReal_norm]
            exact ENNReal.ofReal_le_ofReal (hC _)
          · have h0 : ψ (y⁻¹ * x) = 0 := not_not.mp hy
            rw [h0, mul_zero, enorm_zero]
            exact bot_le
      _ = (∫⁻ y in {y : G | ψ (y⁻¹ * x) ≠ 0}, ‖GlobalTheory.AutomorphicL2Unitary.lift Γ (F : GlobalTheory.AutomorphicL2Unitary.Quot Γ → ℂ) y‖ₑ ∂μ) *
            ENNReal.ofReal (max C0 0) := by
          rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, lintegral_indicator hS]
      _ = eLpNorm (GlobalTheory.AutomorphicL2Unitary.lift Γ (F : GlobalTheory.AutomorphicL2Unitary.Quot Γ → ℂ)) 1 (μ.restrict {y : G | ψ (y⁻¹ * x) ≠ 0}) *
            ENNReal.ofReal (max C0 0) := by
          rw [eLpNorm_one_eq_lintegral_enorm]
      _ ≤ _ := by
          gcongr
          calc _ ≤ _ := hH
            _ ≤ _ := by gcongr
  have hRfin : (N * eLpNorm F 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) * μ (tsupport ψ)⁻¹ ^ (1 / 2 : ℝ)) *
      ENNReal.ofReal (max C0 0) ≠ ⊤ := by
    have h1 : eLpNorm F 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) ≠ ⊤ := Lp.eLpNorm_ne_top F
    have h2 : μ (tsupport ψ)⁻¹ ^ (1 / 2 : ℝ) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hMfin
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top N) h1) h2)
      ENNReal.ofReal_ne_top
  calc ‖cv ψ F x‖ = ‖cv ψ F x‖ₑ.toReal := (toReal_enorm _).symm
    _ ≤ _ := ENNReal.toReal_mono hRfin hE
    _ = max C0 0 * (μ (tsupport ψ)⁻¹).toReal ^ (1 / 2 : ℝ) * N * ‖F‖ := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hC',
        ENNReal.toReal_rpow, ENNReal.toReal_natCast, Lp.norm_def]
      ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.LevLin
section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private def levFnSub {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}
    (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a) : Submodule ℂ (Sm E a) where
  carrier := {φ | IsLevelFn U Ξ φ}
  zero_mem' := ⟨fun _ _ => rfl, fun u _ => map_zero _, fun m _ => by simp⟩
  add_mem' := fun {φ ψ} h h' => ⟨fun γ g => congrArg₂ (· + ·) (h.1 γ g) (h'.1 γ g),
    fun u hu => by rw [map_add, h.2.1 u hu, h'.2.1 u hu],
    fun m hm => by rw [map_add, h.2.2 m hm, h'.2.2 m hm, smul_add]⟩
  smul_mem' := fun c φ h => ⟨fun γ g => congrArg (c • ·) (h.1 γ g),
    fun u hu => by rw [map_smul, h.2.1 u hu],
    fun m hm => by rw [map_smul, h.2.2 m hm, smul_comm]⟩

private theorem cmp_rTensor {W : Type} [AddCommGroup W] [Module ℂ W] {d : ℕ} (T : Module.End ℂ W) (i : Fin d)
    (m : W ⊗[ℂ] (Fin d → ℂ)) : cmp i (T.rTensor (Fin d → ℂ) m) = T (cmp i m) := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul φ v => simp only [LinearMap.rTensor_tmul, cmp_tmul, map_smul]

theorem UpperTheory.V.Cj.H.levLin :
    UpperTheory.V.Cj.H.LevLin := by
  intro E _ _ _ a U Ξ q
  have ap : ∀ (α β : Co Ξ q) (s t : ℂ) X, (s • α + t • β) X = s • α X + t • β X := fun _ _ _ _ _ => rfl
  refine ⟨fun α β s t hα hβ => ⟨fun k X => ?_, fun X i hi => ?_, fun X => ?_⟩, fun α β s t => ?_,
    fun α hα X i => ?_, fun T α X i => ?_⟩
  · rw [ap, ap, hα.equiv k X, hβ.equiv k X, map_add, map_smul, map_smul]
  · rw [ap, hα.basic X i hi, hβ.basic X i hi, smul_zero, smul_zero, add_zero]
  · rw [ap]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (hα.val X)) (Submodule.smul_mem _ _ (hβ.val X))
  · refine AlternatingMap.ext fun X => ?_
    have e : (s • dCo (smLie Ξ) α + t • dCo (smLie Ξ) β) X = s • dCo (smLie Ξ) α X + t • dCo (smLie Ξ) β X := rfl
    rw [e, dCo_apply, dCo_apply, dCo_apply]
    simp only [ap, map_add, map_smul, smul_add, Finset.sum_add_distrib, Finset.smul_sum]
    congr 1 <;> exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
  · exact mem_tens.1 (span_le_tens (N := levFnSub U Ξ) (fun φ h => h) (hα.val X)) i
  · rw [app_apply, cmp_rTensor]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.LocInt
section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

open scoped Pointwise in
theorem UpperTheory.V.Cj.H.locInt :
    UpperTheory.V.Cj.H.LocInt := by
  intro G _ _ _ _ _ _ _ _ Γ _ μ _ _
  refine ⟨fun F => ?_, fun C hC => ?_⟩
  · rw [MeasureTheory.locallyIntegrable_iff]
    intro K hK
    exact (GlobalTheory.AutomorphicL2Local.memLp_restrict_compact G Γ μ F K hK).2
  · have hfin := GlobalTheory.AutomorphicL2Unitary.finite_mem_compact (Γ := Γ) (hC.mul hC.inv)
    refine ⟨hfin.toFinset.card, fun g => ?_⟩
    by_cases hne : {γ : Γ | ↑γ * g ∈ C}.Nonempty
    · obtain ⟨γ0, hγ0⟩ := hne
      calc {γ : Γ | ↑γ * g ∈ C}.encard ≤ {δ : Γ | ↑δ ∈ C * C⁻¹}.encard := by
            apply Set.encard_le_encard_of_injOn (f := fun γ => γ * γ0⁻¹)
            · intro γ hγ
              refine ⟨↑γ * g, hγ, (↑γ0 * g)⁻¹, Set.inv_mem_inv.2 hγ0, ?_⟩
              simp [mul_assoc]
            · intro a _ b _ h
              simpa using h
        _ = hfin.toFinset.card := hfin.encard_eq_coe_toFinset_card
    · rw [Set.not_nonempty_iff_eq_empty.1 hne]
      simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.LocLimMul
section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

section

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

private noncomputable def cj (χ : HChar E) (T : Module.End ℂ (Sm E a)) : Module.End ℂ (Sm E a) :=
  (mulChi a χ).symm.toLinearMap ∘ₗ T ∘ₗ (mulChi a χ).toLinearMap

private theorem mul_cj (χ : HChar E) (T : Module.End ℂ (Sm E a)) (φ : Sm E a) :
    mulChi a χ (cj χ T φ) = T (mulChi a χ φ) := (mulChi a χ).apply_symm_apply _

private theorem isOp_cj {r : ℝ} {χ : HChar E} (hχ : IsTw (a := a) r χ) {N : Submodule ℂ (Sm E a)}
    {T : Module.End ℂ (Sm E a)} (hT : IsOp N T) : IsOp (N.comap (mulChi a χ).toLinearMap) (cj χ T) where
  maps φ hφ := by
    change mulChi a χ (cj χ T φ) ∈ N
    rw [mul_cj]
    exact hT.maps _ hφ
  lie X φ hφ := by
    apply (mulChi a χ).injective
    have h1 := hT.lie X _ hφ
    have h2 := hχ.2 X (cj χ T φ)
    change lie E a X (T (mulChi a χ φ)) = T (lie E a X (mulChi a χ φ)) at h1
    rw [mul_cj, h1, hχ.2, map_add, map_add, map_add, map_smul, map_smul, map_smul, mul_cj] at h2
    rw [mul_cj]
    exact (add_right_cancel h2).symm
  rt g φ hφ := by
    apply (mulChi a χ).injective
    have h1 := hT.rt g _ hφ
    have h2 := rt_mulChi χ g (cj χ T φ)
    change rt E a g (T (mulChi a χ φ)) = T (rt E a g (mulChi a χ φ)) at h1
    rw [mul_cj, h1, rt_mulChi, map_smul, map_smul, map_smul] at h2
    rw [mul_cj]
    exact (smul_right_injective _ (chiDet a χ g).ne_zero h2).symm

private theorem shift_mul {r : ℝ} {χ : HChar E} (hχ : IsTw (a := a) r χ) (X : Lie E a) (φ : Sm E a) :
    shift (lie E a) 0 X (mulChi a χ φ) = mulChi a χ (shift (lie E a) r X φ) := by
  rw [shift_apply, shift_apply, zero_mul, zero_smul, add_zero, hχ.2, LinearMap.add_apply, LinearMap.smul_apply,
    Module.End.one_apply, Complex.coe_smul]

private theorem casA_mul {r : ℝ} {χ : HChar E} (hχ : IsTw (a := a) r χ) (c : ℝ) {n : ℕ} (e : Fin n → Herm E a)
    (φ : Sm E a) : casA 0 c e (mulChi a χ φ) = mulChi a χ (casA r c e φ) := by
  simp only [casA, cas, LinearMap.sub_apply, LinearMap.sum_apply, Module.End.mul_apply, LinearMap.smul_apply,
    Module.End.one_apply, map_sub, map_sum, map_smul, shift_mul hχ]

private theorem locLim_mul (χ : HChar E) {f : ℕ → Sm E a} {φ : Sm E a}
    (h : LocLim (fun k => mulChi a χ (f k)) (mulChi a χ φ)) : LocLim f φ := by
  intro C hC
  have hc : Continuous fun g : GA E a => (((chiDet a χ g)⁻¹ : ℂˣ) : ℂ) :=
    Units.continuous_val.comp (χ.2.1.comp Matrix.GeneralLinearGroup.continuous_det).inv
  obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn hc.continuousOn
  have h1 := h C hC
  rw [Metric.tendstoUniformlyOn_iff] at h1 ⊢
  intro ε hε
  have hp : 0 < |B| + 1 := by positivity
  filter_upwards [h1 (ε / (|B| + 1)) (by positivity)] with k hk g hg
  have h2 := hk g hg
  rw [dist_eq_norm, mulChi_apply, mulChi_apply, ← sub_mul, lt_div_iff₀ hp] at h2
  have e : φ.1 g - (f k).1 g = (φ.1 g - (f k).1 g) * (chiDet a χ g : ℂˣ) * (((chiDet a χ g)⁻¹ : ℂˣ) : ℂ) :=
    (Units.mul_inv_cancel_right _ _).symm
  rw [dist_eq_norm, e, norm_mul]
  refine lt_of_le_of_lt (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)) h2
  exact (hB g hg).trans ((le_abs_self B).trans (le_add_of_nonneg_right zero_le_one))

end

theorem UpperTheory.V.Cj.H.twRes :
    UpperTheory.V.Cj.H.TwRes := by
  intro E _ _ _ a r χ hχ N n e c P Q S h
  refine ⟨cj χ P, fun k => cj χ (Q k), fun k => cj χ (S k), isOp_cj hχ h.opP, fun k => isOp_cj hχ (h.opQ k),
    fun k => isOp_cj hχ (h.opS k), fun k φ hφ => ?_, fun φ hφ => ?_, fun φ hφ => ?_⟩
  · apply (mulChi a χ).injective
    rw [map_sub, ← casA_mul hχ, mul_cj, mul_cj]
    exact h.res k _ hφ
  · apply (mulChi a χ).injective
    rw [map_zero, ← casA_mul hχ, mul_cj]
    exact h.ker _ hφ
  · apply locLim_mul χ
    simp only [mul_cj]
    exact h.lim _ hφ
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.ROpApply
section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private theorem mapQ {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (f : A →ₐ[ℂ] B) {n : ℕ}
    (X : Fin n → Fin n → A) (u : ℂ) : f (Formalism.REAL.qdet X u) = Formalism.REAL.qdet (fun i j => f (X i j)) u := by
  simp only [Formalism.REAL.qdet, Formalism.REAL.qminor, Formalism.REAL.Tm, map_sum, map_mul, map_intCast, map_list_prod, List.map_ofFn,
    Function.comp_def, map_add, apply_ite f, AlgHom.commutes, map_zero]

private noncomputable def rAlg (V : Type) [AddCommGroup V] [Module ℂ V] (d : ℕ) :
    Matrix (Fin d) (Fin d) ℂ →ₐ[ℂ] Module.End ℂ (V ⊗[ℂ] (Fin d → ℂ)) :=
  (Module.End.lTensorAlgHom ℂ (Fin d → ℂ) V).comp
    (Matrix.toLinAlgEquiv' : Matrix (Fin d) (Fin d) ℂ ≃ₐ[ℂ] Module.End ℂ (Fin d → ℂ)).toAlgHom

private noncomputable def rOp (V : Type) [AddCommGroup V] [Module ℂ V] (d : ℕ) :
    Matrix (Fin d) (Fin d) ℂ →ₐ[ℂ] (Module.End ℂ (V ⊗[ℂ] (Fin d → ℂ)))ᵐᵒᵖ where
  toFun N := MulOpposite.op (rAlg V d Nᵀ)
  map_one' := by simp
  map_mul' x y := by simp [Matrix.transpose_mul]
  map_zero' := by simp
  map_add' x y := by simp [Matrix.transpose_add]
  commutes' c := by simp [Algebra.algebraMap_eq_smul_one]

private theorem rOp_apply (V : Type) [AddCommGroup V] [Module ℂ V] (d : ℕ) (N : Matrix (Fin d) (Fin d) ℂ) :
    rOp V d N = MulOpposite.op (rAlg V d Nᵀ) := rfl

private theorem qdet_stab {M : Type} [AddCommGroup M] [Module ℂ M] (N : Submodule ℂ M) {n : ℕ}
    (X : Fin n → Fin n → Module.End ℂ M) (h : ∀ i j, ∀ m ∈ N, X i j m ∈ N) (u : ℂ) :
    ∀ m ∈ N, Formalism.REAL.qdet X u m ∈ N := by
  let S : Subalgebra ℂ (Module.End ℂ M) :=
    { carrier := {z | ∀ m ∈ N, z m ∈ N}
      mul_mem' := fun hx hy m hm => hx _ (hy m hm)
      add_mem' := fun hx hy m hm => N.add_mem (hx m hm) (hy m hm)
      algebraMap_mem' := fun c m hm => N.smul_mem c hm }
  let Z : Fin n → Fin n → S := fun i j => ⟨X i j, h i j⟩
  have e : ((Formalism.REAL.qdet Z u : S) : Module.End ℂ M) = Formalism.REAL.qdet X u := mapQ S.val Z u
  rw [← e]
  exact (Formalism.REAL.qdet Z u).2

theorem UpperTheory.V.Cj.H.capSm :
    UpperTheory.V.Cj.H.CapSm := by
  intro E _ _ _ a Ξ τ u
  have hE : ∀ i j : Fin a, Eop (a := a) τ i j = eL (N := Module.End ℂ (Sm E a)) (lie E a) τ i j := fun _ _ => rfl
  have hc : cap (a := a) τ u = Formalism.REAL.qdet (Eop (a := a) τ) (u + ((a : ℂ) - 1) / 2) := rfl
  refine ⟨?_, fun m hm => ?_, fun X => ?_, fun N hN => ?_⟩
  · let f : Module.End ℂ (Sm E a) →ₐ[ℂ] Module.End ℂ (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)) :=
      Module.End.rTensorAlgHom ℂ (Sm E a) (Fin Ξ.d → ℂ)
    have hf : ∀ X, smA Ξ X = f (lie E a X) := fun _ => rfl
    have e : eL (smA Ξ) τ = fun i j => f (Eop (a := a) τ i j) := by
      funext i j
      simp only [hE, eL, hf, map_smul, map_sub]
    rw [e, ← mapQ, ← hc]
    rfl
  · have hd := (dualIff E a Ξ τ m).1 hm
    have hB : ∀ X, smB Ξ X = rAlg (Sm E a) Ξ.d (Ξ.dmat X) := fun X => smB_apply Ξ X
    have h := (mapQ (rOp (Sm E a) Ξ.d) (GlobalTheory.WignerGL.dualE Ξ τ) (u + ((a : ℂ) - 1) / 2)).symm.trans
      (congrArg (rOp (Sm E a) Ξ.d) (hd.2 u))
    rw [map_smul, map_one] at h
    have e : ∀ i j, rOp (Sm E a) Ξ.d (GlobalTheory.WignerGL.dualE Ξ τ i j) = -MulOpposite.op (eL (smB Ξ) τ i j) := fun i j => by
      rw [dualE_eq, map_neg, rOp_apply, Matrix.transpose_transpose]
      simp only [eL, hB, map_smul, map_sub]
    simp only [e] at h
    rw [h, MulOpposite.unop_smul, MulOpposite.unop_one]
  · rw [← UpperTheory.V.Cm.uC_capC, ← UpperTheory.V.Cm.uC_ιC]
    exact Commute.map (Subalgebra.mem_center_iff.1 (UpperTheory.V.Cm.capC_mem_center τ u) _) (UpperTheory.V.Cm.uC E a)
  · rw [hc]
    refine qdet_stab N _ (fun i j φ hφ => ?_) _
    rw [hE]
    exact N.smul_mem _ (N.sub_mem (hN _ φ hφ) (N.smul_mem _ (hN _ φ hφ)))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.SmSepDer
section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private theorem sm_sepDer (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (Ξ : AlgRep E a) :
    SepDer (smK Ξ) (smLie Ξ) := by
  intro k Z h0 hk m' hm
  have h1 : ∃ j, Bor.cmp j m' ≠ 0 := by
    by_contra h
    push Not at h
    apply hm
    rw [← sum_cmp m']
    simp [h]
  obtain ⟨j, hj⟩ := h1
  have h2 : (Bor.cmp j m').1 ≠ 0 := fun h => hj (Subtype.ext h)
  obtain ⟨g, hg⟩ := Function.ne_iff.1 h2
  let l : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun m => (Bor.cmp j m).1 g
      map_add' := fun x y => by rw [map_add]; rfl
      map_smul' := fun c x => by rw [map_smul]; rfl }
  have hl : ∀ (φ : Sm E a) (v : Fin Ξ.d → ℂ), l (φ ⊗ₜ v) = φ.1 g * v j := fun φ v => by
    change (Bor.cmp j (φ ⊗ₜ v)).1 g = _
    rw [cmp_tmul, mul_comm]
    rfl
  have hc0 : (fun t => Unitary.toUnits (k t)) 0 = 1 := by simp only [h0, map_one]
  refine ⟨l, hg, fun m => ?_⟩
  induction m using TensorProduct.induction_on with
  | zero => simpa only [map_zero] using hasDerivAt_const (0 : ℝ) (0 : ℂ)
  | add x y hx hy => simpa only [map_add] using hx.fun_add hy
  | tmul φ v =>
    have h3 := GlobalTheory.CuspRep.hasDerivAt_curve φ g (fun t => Unitary.toUnits (k t)) (toL Z) hc0 hk
    have h4 := HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
      (Ξ.hasDerivAt_curve (fun t => Unitary.toUnits (k t)) (toL Z) hc0 hk j i).mul_const (v i)
    have h5 := h3.fun_mul h4
    simp only [h0, map_one, mul_one] at h5
    have h7 : smLie Ξ (toL Z) (φ ⊗ₜ v) = lie E a (toL Z) φ ⊗ₜ v + φ ⊗ₜ (Ξ.dmat (toL Z) *ᵥ v) := rfl
    simp only [smK, h7, TensorProduct.map_tmul, map_add, hl, Matrix.toLin'_apply]
    have h6 : ∑ i, (1 : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) j i * v i = v j := congrFun (Matrix.one_mulVec v) j
    rw [h6] at h5
    exact h5

theorem UpperTheory.V.Cj.H.smAB :
    UpperTheory.V.Cj.H.SmAB := by
  intro E _ _ _ a Ξ
  refine ⟨fun X Y => ?_, fun X Y => ?_, fun X Y => ?_, fun k X => ?_, fun k X => ?_,
    infAbs E a _ _ _ (sm_sepDer E a Ξ)⟩
  · simp only [smA_apply]
    rw [← LinearMap.rTensor_mul, ← LinearMap.rTensor_mul, ← LinearMap.rTensor_sub]
    congr 1
    exact (lie_comm (toL X) (toL Y)).trans (map_sub (lie E a) (toL (X * Y)) (toL (Y * X))).symm
  · simp only [smB_apply]
    rw [← GlobalTheory.AlgInfChar.dmat_bracket, map_sub, LinearMap.lTensor_sub, Matrix.toLin'_mul, Matrix.toLin'_mul,
      LinearMap.lTensor_comp, LinearMap.lTensor_comp]
    rfl
  · rw [smA_apply, smB_apply]
    exact TensorProduct.ext' fun _ _ => rfl
  · refine TensorProduct.ext' fun φ v => ?_
    have h1 : act (.cpt k) (lie E a (toL X) φ) = lie E a (toL (k.1 * X * star k.1)) (act (.cpt k) φ) :=
      LinearMap.congr_fun (GlobalTheory.CapAdInv.rt_lie (Unitary.toUnits k) X) φ
    simp only [Module.End.mul_apply, smK, smA_apply, LinearMap.rTensor_tmul, TensorProduct.map_tmul, h1]
  · refine TensorProduct.ext' fun φ v => ?_
    have h2 : Ξ.mat (Unitary.toUnits k) * Ξ.dmat (toL X) =
        Ξ.dmat (toL (k.1 * X * star k.1)) * Ξ.mat (Unitary.toUnits k) :=
      Ξ.mat_mul_dmat (Unitary.toUnits k) X
    simp only [Module.End.mul_apply, smK, smB_apply, LinearMap.lTensor_tmul, TensorProduct.map_tmul,
      Matrix.toLin'_apply, Matrix.mulVec_mulVec, h2]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.TestOps
section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

section
variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

private def stab (ψ : Sm E a) : Subgroup (GL (Fin a) (GlobalTheory.CuspRep.Af E)) where
  carrier := {k | rt E a (finGL E a k) ψ = ψ}
  one_mem' := by simp
  mul_mem' := fun {x y} hx hy => by
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    rw [map_mul, map_mul, Module.End.mul_apply, hy, hx]
  inv_mem' := fun {x} hx => by
    simp only [Set.mem_setOf_eq] at hx ⊢
    conv_lhs => rw [← hx]
    rw [← Module.End.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one, Module.End.one_apply]

private theorem lev_lie (X : Lie E a) (ψ : Sm E a) (h : HasLev ψ) : HasLev (lie E a X ψ) := by
  have hle : stab ψ ≤ stab (lie E a X ψ) := fun k hk =>
    (LinearMap.congr_fun (lie_rt_fin X k) ψ).symm.trans (congrArg (lie E a X) hk)
  exact Subgroup.isOpen_mono hle h

private theorem lev_rt (g : GA E a) (ψ : Sm E a) (h : HasLev ψ) : HasLev (rt E a g ψ) := by
  obtain ⟨y, l, rfl⟩ : ∃ y l, infGL E a y * finGL E a l = g := ⟨_, _, infGL_mul_finGL g⟩
  have hc : Continuous fun k : GL (Fin a) (GlobalTheory.CuspRep.Af E) => l⁻¹ * k * l := by fun_prop
  have ho : IsOpen ((fun k : GL (Fin a) (GlobalTheory.CuspRep.Af E) => l⁻¹ * k * l) ⁻¹' (stab ψ : Set _)) :=
    IsOpen.preimage hc h
  refine Subgroup.isOpen_of_mem_nhds (stab (rt E a (infGL E a y * finGL E a l) ψ)) (g := 1)
    (mem_of_superset (ho.mem_nhds ?_) fun k hk => ?_)
  · simpa using (stab ψ).one_mem
  · have hk' : rt E a (finGL E a (l⁻¹ * k * l)) ψ = ψ := hk
    change rt E a (finGL E a k) (rt E a (infGL E a y * finGL E a l) ψ) = rt E a (infGL E a y * finGL E a l) ψ
    have e : finGL E a k * (infGL E a y * finGL E a l) = infGL E a y * finGL E a l * finGL E a (l⁻¹ * k * l) := by
      rw [← mul_assoc, ← infGL_comm, mul_assoc, mul_assoc (infGL E a y), ← map_mul, ← map_mul]
      congr 2
      group
    rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply, hk']

private theorem supp_lie (X : Lie E a) (ψ : Sm E a) (h : HasCompactSupport ψ.1) :
    HasCompactSupport (lie E a X ψ).1 := by
  obtain ⟨c, c0, -, ccont, cder, -⟩ := UpperTheory.V.Lit.Bor.oneParam E a X
  refine HasCompactSupport.intro h fun g hg => ?_
  have hd := GlobalTheory.CuspRep.hasDerivAt_curve ψ g c X c0 cder
  have hc : Continuous fun t : ℝ => g * infGL E a (c t) := continuous_const.mul ccont
  have ht : Tendsto (fun t : ℝ => g * infGL E a (c t)) (𝓝 0) (𝓝 g) := by
    simpa [c0] using hc.tendsto 0
  have hz : (fun t : ℝ => ψ.1 (g * infGL E a (c t))) =ᶠ[𝓝 0] fun _ => (0 : ℂ) :=
    ht.eventually (notMem_tsupport_iff_eventuallyEq.1 hg)
  exact hd.unique ((hasDerivAt_const (0 : ℝ) (0 : ℂ)).congr_of_eventuallyEq hz)

private theorem supp_rt (g : GA E a) (ψ : Sm E a) (h : HasCompactSupport ψ.1) :
    HasCompactSupport (rt E a g ψ).1 :=
  h.comp_homeomorph (Homeomorph.mulRight g)

end

theorem UpperTheory.V.Cj.H.testOps :
    UpperTheory.V.Cj.H.TestOps := by
  intro E _ _ _ a ψ
  exact ⟨fun h => ⟨ContAut.continuous_of_isOpen_stab E a ψ h, fun X => lev_lie X ψ h, fun g => lev_rt g ψ h⟩,
    fun h => ⟨fun X => ⟨supp_lie X ψ h.1, lev_lie X ψ h.2⟩, fun g => ⟨supp_rt g ψ h.1, lev_rt g ψ h.2⟩⟩⟩
end

