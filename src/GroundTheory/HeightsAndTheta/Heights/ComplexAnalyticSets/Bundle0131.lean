import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveNormalisationLength
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0019
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0128
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0074
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0125
import GroundTheory.HeightsAndTheta.Heights.Intersections.PTorusInvLevi
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0127
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0130
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0075
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0121
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0093
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0077
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0122
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0126
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0129

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.CurveNormalisationFiniteLemmas
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets FieldNumbers

noncomputable section

theorem exists_finset_span_integral_of_div (hN : NoetherIntegralClosureFinite.Statement.{0}) {n : ℕ} {O Ω : Type}
    [CommRing O] [Field Ω] [Algebra O Ω] (φ : MvPolynomial (Fin n) ℂ →+* O)
    (hφ : ∀ o : O, ∃ f s, IsUnit (φ s) ∧ o * φ s = φ f)
    (hΩ : ∀ x : Ω, ∃ a b : O, x = algebraMap O Ω a / algebraMap O Ω b) :
    ∃ t : Finset Ω, ∀ x : Ω, IsIntegral O x → x ∈ Submodule.span O (t : Set Ω) := by
  let ψ : MvPolynomial (Fin n) ℂ →+* Ω := (algebraMap O Ω).comp φ
  let _ : Algebra ℂ Ω := (ψ.comp C).toAlgebra
  let S : Set Ω := Set.range fun i ↦ ψ (X i)
  have hpoly : ∀ f, ψ f ∈ Algebra.adjoin ℂ S := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C c => exact Subalgebra.algebraMap_mem _ c
    | add f g hf hg => rw [map_add]; exact add_mem hf hg
    | mul_X f i hf => rw [map_mul]; exact mul_mem hf (Algebra.subset_adjoin ⟨i, rfl⟩)
  let A : Subalgebra ℂ Ω :=
    { toSubsemiring := (algebraMap O Ω).rangeS, algebraMap_mem' := fun c ↦ ⟨φ (C c), rfl⟩ }
  have hRA : Algebra.adjoin ℂ S ≤ A := Algebra.adjoin_le (by rintro _ ⟨i, rfl⟩; exact ⟨φ (X i), rfl⟩)
  have hloc : ∀ a ∈ A, ∃ r ∈ Algebra.adjoin ℂ S, ∃ d ∈ Algebra.adjoin ℂ S, d ≠ 0 ∧ d⁻¹ ∈ A ∧ a = r * d⁻¹ := by
    rintro _ ⟨o, rfl⟩
    obtain ⟨f, s, hs, ho⟩ := hφ o
    refine ⟨ψ f, hpoly f, ψ s, hpoly s, (hs.map (algebraMap O Ω)).ne_zero, ⟨↑hs.unit⁻¹, ?_⟩, ?_⟩
    · change algebraMap O Ω ↑hs.unit⁻¹ = (algebraMap O Ω (φ s))⁻¹
      rw [map_units_inv, IsUnit.unit_spec]
    · refine (eq_mul_inv_iff_mul_eq₀ (hs.map (algebraMap O Ω)).ne_zero).2 ?_
      change algebraMap O Ω o * algebraMap O Ω (φ s) = algebraMap O Ω (φ f)
      rw [← map_mul, ho]
  have hE : ∀ x : Ω, x ∈ IntermediateField.adjoin ℂ S := by
    have hA : ∀ a ∈ A, a ∈ IntermediateField.adjoin ℂ S := by
      intro a ha
      obtain ⟨r, hr, d, hd, -, -, rfl⟩ := hloc a ha
      exact mul_mem (IntermediateField.algebra_adjoin_le_adjoin ℂ S hr)
        (inv_mem (IntermediateField.algebra_adjoin_le_adjoin ℂ S hd))
    intro x
    obtain ⟨a, b, rfl⟩ := hΩ x
    exact div_mem (hA _ ⟨a, rfl⟩) (hA _ ⟨b, rfl⟩)
  have hfin : FiniteDimensional (IntermediateField.adjoin ℂ S)
      (IntermediateField.extendScalars (le_refl (IntermediateField.adjoin ℂ S))) := by
    rw [IntermediateField.extendScalars_self]; infer_instance
  obtain ⟨t, -, ht⟩ := exists_finset_integral_span hN (Set.finite_range _) A _ hRA hloc le_rfl hfin
  let _ : Algebra O A := ((algebraMap O Ω).codRestrict A fun o ↦ (⟨o, rfl⟩ : algebraMap O Ω o ∈ (algebraMap O Ω).rangeS)).toAlgebra
  have : IsScalarTower O A Ω := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hsur : Function.Surjective (algebraMap O A) := by rintro ⟨_, o, rfl⟩; exact ⟨o, rfl⟩
  refine ⟨t, fun x hx ↦ ?_⟩
  rw [← Submodule.restrictScalars_span O A hsur]
  exact ht x (hE x) hx.tower_top

theorem exists_algHom_span_of_mem_minimalPrimes (hN : NoetherIntegralClosureFinite.Statement.{0}) {n : ℕ}
    {O : Type} [CommRing O] (φ : MvPolynomial (Fin n) ℂ →+* O)
    (hφ : ∀ o : O, ∃ f s, IsUnit (φ s) ∧ o * φ s = φ f) {p : Ideal O} (hp : p ∈ minimalPrimes O) :
    ∃ g : FractionRing O →ₐ[O] FractionRing (O ⧸ p), ∃ t : Finset (FractionRing (O ⧸ p)),
      ∀ x : FractionRing O, IsIntegral O x → g x ∈ Submodule.span O (t : Set (FractionRing (O ⧸ p))) := by
  have := Ideal.IsMinimalPrime.isPrime hp
  have hu : ∀ y : nonZeroDivisors O, IsUnit (Algebra.ofId O (FractionRing (O ⧸ p)) y) := by
    intro y
    refine IsUnit.mk0 _ fun h ↦ notMem_nonZeroDivisors_of_mem_mem_minimalPrimes ?_ hp y.2
    have h' : algebraMap (O ⧸ p) (FractionRing (O ⧸ p)) (Ideal.Quotient.mk p y) =
        algebraMap (O ⧸ p) (FractionRing (O ⧸ p)) 0 := by rw [map_zero]; exact h
    exact Ideal.Quotient.eq_zero_iff_mem.1 (IsFractionRing.injective _ _ h')
  obtain ⟨t, ht⟩ := exists_finset_span_integral_of_div hN φ hφ (Ω := FractionRing (O ⧸ p)) fun x ↦ by
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := O ⧸ p) x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    exact ⟨a, b, rfl⟩
  exact ⟨IsLocalization.liftAlgHom (M := nonZeroDivisors O) hu, t, fun x hx ↦ ht _ (hx.map _)⟩

theorem finite_integralClosure_of_isReduced (hN : NoetherIntegralClosureFinite.Statement.{0}) {n : ℕ} {O : Type}
    [CommRing O] [IsReduced O] [IsNoetherianRing O] (φ : MvPolynomial (Fin n) ℂ →+* O)
    (hφ : ∀ o : O, ∃ f s, IsUnit (φ s) ∧ o * φ s = φ f) :
    Module.Finite O (integralClosure O (FractionRing O)) := by
  have := (minimalPrimes.finite_of_isNoetherianRing O).to_subtype
  choose g t ht using fun p : minimalPrimes O ↦ exists_algHom_span_of_mem_minimalPrimes hN φ hφ p.2
  let F : integralClosure O (FractionRing O) →ₗ[O]
      ((p : minimalPrimes O) → Submodule.span O (t p : Set (FractionRing (O ⧸ (p : Ideal O))))) :=
    LinearMap.pi fun p ↦ LinearMap.codRestrict _
      ((g p).toLinearMap ∘ₗ (integralClosure O (FractionRing O)).val.toLinearMap) fun x ↦ ht p x x.2
  refine Module.Finite.of_injective F ((injective_iff_map_eq_zero F).2 fun x hx ↦ ?_)
  have h0 : ∀ p : minimalPrimes O, g p x = 0 := fun p ↦ congrArg Subtype.val (congr_fun hx p)
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors O) (x : FractionRing O)
  have ha : a ∈ sInf (minimalPrimes O) := by
    refine Ideal.mem_sInf.2 fun p hp ↦ ?_
    have := Ideal.IsMinimalPrime.isPrime hp
    have e : algebraMap (O ⧸ p) (FractionRing (O ⧸ p)) (Ideal.Quotient.mk p a) =
        algebraMap (O ⧸ p) (FractionRing (O ⧸ p)) 0 := by
      rw [map_zero]
      change algebraMap O (FractionRing (O ⧸ p)) a = 0
      rw [← (g ⟨p, hp⟩).commutes, ← hab, map_mul, h0, zero_mul]
    exact Ideal.Quotient.eq_zero_iff_mem.1 (IsFractionRing.injective _ _ e)
  rw [Ideal.sInf_minimalPrimes, Ideal.mem_radical_iff] at ha
  obtain ⟨k, hk⟩ := ha
  have ha0 : a = 0 := IsNilpotent.eq_zero ⟨k, by simpa using hk⟩
  rw [ha0, map_zero, (IsLocalization.map_units (FractionRing O) b).mul_left_eq_zero] at hab
  exact Subtype.ext hab

theorem isReduced_curveLocalRing {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ)
    (h : IsRadicalAt I q) : IsReduced (curveLocalRing I q) := by
  refine (Ideal.isRadical_iff_quotient_reduced _).1 ?_
  rw [Ideal.IsRadical, ← IsLocalization.map_radical (RingHom.ker (eval q)).primeCompl]
  refine Ideal.map_le_iff_le_comap.2 fun f hf ↦ ?_
  obtain ⟨s, hs, hsf⟩ := h f hf
  have hu : IsUnit (algebraMap _ (Localization.AtPrime (RingHom.ker (eval q))) s) :=
    IsLocalization.map_units _ (⟨s, fun h' ↦ hs (RingHom.mem_ker.1 h')⟩ : (RingHom.ker (eval q)).primeCompl)
  exact (Ideal.unit_mul_mem_iff_mem _ hu).1 (by rw [← map_mul]; exact Ideal.mem_map_of_mem _ hsf)

theorem curveLocalRing_eq_div {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ)
    (o : curveLocalRing I q) : ∃ f s, IsUnit (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) s) ∧
      o * algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) s =
        algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f := by
  obtain ⟨z, rfl⟩ : ∃ z, Ideal.Quotient.mk
      (I.map (algebraMap _ (Localization.AtPrime (RingHom.ker (eval q))))) z = o :=
    Ideal.Quotient.mk_surjective o
  obtain ⟨⟨f, s⟩, rfl⟩ := IsLocalization.mk'_surjective (RingHom.ker (eval q)).primeCompl z
  refine ⟨f, s, isUnit_algebraMap_curveLocalRing I q s fun h ↦ s.2 (RingHom.mem_ker.2 h), ?_⟩
  have e := congrArg (Ideal.Quotient.mk (I.map (algebraMap _ (Localization.AtPrime (RingHom.ker (eval q))))))
    (IsLocalization.mk'_spec (Localization.AtPrime (RingHom.ker (eval q))) f s)
  rw [map_mul] at e
  exact e

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPolynomialChartInjective
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Topology

noncomputable section

theorem PolynomialChartInjective.full : PolynomialChartInjective.Statement := by
  classical
  intro σ _ k t f w hk hlin
  set g : Fin (k + 1) → MvPolynomial σ ℂ := Fin.cons t f with hg
  set F : (σ → ℂ) → Fin (k + 1) → ℂ := fun z j ↦ eval z (g j) with hF
  set L : (σ → ℂ) →L[ℂ] (Fin (k + 1) → ℂ) :=
    ContinuousLinearMap.pi fun j ↦ fderiv ℂ (fun z : σ → ℂ ↦ eval z (g j)) w with hL
  have hFL : HasStrictFDerivAt F L w := hasStrictFDerivAt_pi.2 fun j ↦
    (AnalyticOnNhd.eval_mvPolynomial (𝕜 := ℂ) (g j) w trivial).hasStrictFDerivAt
  set r : Fin (k + 1) → σ → ℂ :=
    Fin.cons (fun i ↦ eval w (pderiv i t)) (fun j i ↦ eval w (pderiv i (f j))) with hr
  have hrow : ∀ j i, fderiv ℂ (fun z : σ → ℂ ↦ eval z (g j)) w (Pi.single i 1) = r j i := by
    intro j i
    rw [NormalCurveRegularPoint.fderiv_eval_single]
    refine Fin.cases ?_ (fun j ↦ ?_) j <;> simp [g, r]
  have hspan : Submodule.span ℂ (Set.range r) = ⊤ :=
    hlin.span_eq_top_of_card_eq_finrank' (by simp [Module.finrank_fintype_fun_eq_card, hk])
  have hinj : Function.Injective L := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    let ψ : (σ → ℂ) →ₗ[ℂ] ℂ :=
      { toFun := fun u ↦ ∑ i, u i * v i
        map_add' := fun a b ↦ by simp [add_mul, Finset.sum_add_distrib]
        map_smul' := fun c a ↦ by simp [Finset.mul_sum, mul_assoc] }
    have hker : Submodule.span ℂ (Set.range r) ≤ LinearMap.ker ψ := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      have h0 := congrFun hv j
      simp only [hL, ContinuousLinearMap.pi_apply, Pi.zero_apply] at h0
      rw [pi_eq_sum_univ' v, map_sum] at h0
      simp only [map_smul, smul_eq_mul, hrow] at h0
      simpa [ψ, mul_comm] using h0
    rw [hspan] at hker
    funext i
    have := hker (Submodule.mem_top (x := Pi.single i 1))
    simpa [ψ, Pi.single_apply] using this
  let e : (σ → ℂ) ≃L[ℂ] (Fin (k + 1) → ℂ) :=
    (LinearMap.linearEquivOfInjective L.toLinearMap hinj
      (by simp [Module.finrank_fintype_fun_eq_card, hk])).toContinuousLinearEquiv
  have hFe : HasStrictFDerivAt F (e : (σ → ℂ) →L[ℂ] (Fin (k + 1) → ℂ)) w := by
    convert hFL using 1
    ext v : 1
    rfl
  refine ⟨_, hFe.eventually_left_inverse, fun x hx y hy hxy ↦ ?_⟩
  have hFxy : F x = F y := by
    funext j
    refine Fin.cases ?_ (fun j ↦ ?_) j
    · simpa [F, g] using hxy
    · simp only [F, g, Fin.cons_succ, hx.2 j, hy.2 j]
  rw [← hx.1, ← hy.1, hFxy]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRegLogDensNonneg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix ComplexSets
open GroundTheory.Heights₂.Heights.LowerBoundFree.FubiniLevi
open scoped ComplexOrder

noncomputable section

namespace RegularizedLogDensityNonneg

theorem hessC_logDistSq_comp_posSemidef {n e : ℕ} (x : Fin n → ℂ) (s : (Fin e → ℂ) → Fin n → ℂ)
    (y : Fin e → ℂ) (han : AnalyticAt ℂ s y) (hne : s y ≠ x) :
    (ReciprocityTheory.AnForm.hessC (logDistSq x ∘ s) y).PosSemidef := by
  let τ : (Fin e → ℂ) → Fin n → ℂ := fun w => s w - x
  have hτ : AnalyticAt ℂ τ y := han.sub analyticAt_const
  have hS : sqSum (τ y) ≠ 0 := by
    intro h0
    apply hne
    have hj : ∀ j ∈ Finset.univ, ‖(s y - x) j‖ ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg _).1 h0
    funext j
    have := hj j (Finset.mem_univ j)
    simpa [sub_eq_zero] using this
  have hφ : ContDiffAt ℝ 2 phi (τ y) := contDiffAt_phi hS
  have hfun : logDistSq x ∘ s = fun w => 2 * (phi ∘ τ) w := by
    funext w
    simp only [Function.comp_apply, logDistSq, phi, τ, euclPot, sqSum]
    ring
  have hP : (ReciprocityTheory.AnForm.hessC (phi ∘ τ) y).PosSemidef := by
    refine ReciprocityTheory.AnForm.M.hessC_posSemidef _ _ (hφ.comp _ hτ.restrictScalars.contDiffAt) fun v => ?_
    rw [ReciprocityTheory.AnForm.levi_comp v hτ hφ]
    exact GroundTheory.Heights₂.Heights.Inter.TorusInvariantLevi.leviForm_phi_nonneg hS _
  rw [hfun, ReciprocityTheory.AnForm.M.hessC_const_mul']
  exact hP.smul (by norm_num)

end RegularizedLogDensityNonneg

theorem RegLogDensNonneg.proof : RegLogDensNonneg.Statement := by
  intro n d J A u ε x z s hε hzx hs
  have han : AnalyticAt ℂ s (A *ᵥ z) := FormIntegralPositivity.analyticAt_sheet hs
  have hsz : s (A *ᵥ z) = z := by
    obtain ⟨U, -, -, -, h, -⟩ := hs
    exact h
  refine ReciprocityTheory.AnForm.A.maDens_nonneg_of_posSemidef _ _ fun k => ?_
  refine Fin.cases ?_ (fun j => ?_) k
  · simp only [Matrix.cons_val_zero]
    set y := A *ᵥ z
    have hh : AnalyticAt ℂ (fun w => linEval u (s w)) y := by
      unfold linEval
      exact Finset.analyticAt_fun_sum _ fun j _ => analyticAt_const.mul ((analyticAt_pi_iff.1 han) j)
    let τ : (Fin (d + 1) → ℂ) → (Fin 2 → ℂ) := fun w => ![linEval u (s w), ((√ε : ℝ) : ℂ)]
    have hτ : AnalyticAt ℂ τ y := by
      refine analyticAt_pi_iff.2 fun i => ?_
      fin_cases i
      · simpa [τ] using hh
      · simpa [τ] using (analyticAt_const : AnalyticAt ℂ (fun _ : Fin (d + 1) → ℂ => ((√ε : ℝ) : ℂ)) y)
    have hS : sqSum (τ y) ≠ 0 := by
      have : sqSum (τ y) = ‖linEval u (s y)‖ ^ 2 + ε := by
        simp only [τ, sqSum, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
          Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hε.le]
      rw [this]
      positivity
    have hφ : ContDiffAt ℝ 2 phi (τ y) := contDiffAt_phi hS
    have hfun : logReg u ε ∘ s = phi ∘ τ := by
      funext w
      exact RegularizedDensityNonneg.half_log_eq_phi _ hε.le
    rw [hfun]
    refine ReciprocityTheory.AnForm.M.hessC_posSemidef _ _ (hφ.comp _ hτ.restrictScalars.contDiffAt) fun v => ?_
    rw [ReciprocityTheory.AnForm.levi_comp v hτ hφ]
    exact GroundTheory.Heights₂.Heights.Inter.TorusInvariantLevi.leviForm_phi_nonneg hS _
  · simp only [Matrix.cons_val_succ]
    exact RegularizedLogDensityNonneg.hessC_logDistSq_comp_posSemidef x s _ han (hsz.symm ▸ hzx)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceCutBoundary
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

theorem SliceCutBoundary.proof (hB : SliceBoundaryBound.Statement) (hD : SliceCutDecay.Statement) :
    SliceCutBoundary.Statement := by
  intro n e h W g ℓ A F G hW hg hℓ hA hF0 hG0 hF hG
  obtain ⟨C, hC0, hC⟩ := hB n e h W g ℓ A F G hW hg hℓ hA hF0 hG0 hF hG
  obtain ⟨D, hDk⟩ := hD n e h W g ℓ A hW hg hℓ hA
  have h1 : Tendsto (fun k : ℕ => D / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hlim : Tendsto (fun k : ℕ => C * (D / ((k : ℝ) + 1) + Real.sqrt (D / ((k : ℝ) + 1)))) atTop
      (𝓝 0) := by
    simpa using (h1.add h1.sqrt).const_mul C
  refine squeeze_zero_norm (fun k => ?_) hlim
  rw [Real.norm_eq_abs]
  refine (hC _ (SliceCut.contDiff h k) (SliceCut.hasCompactSupport h k)).trans ?_
  obtain ⟨hm, he⟩ := hDk k
  gcongr

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceLogIntegrable
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets Filter

noncomputable section

namespace SliceLogIntegrableProof

variable {n : ℕ}

theorem linEval_eq_one {J : Ideal (MvPolynomial (Fin n) ℂ)} {ℓ x : Fin n → ℂ}
    (hx : x ∈ zeroSet (J ⊔ Ideal.span {linForm ℓ - 1})) : linEval ℓ x = 1 := by
  have h1 := hx _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self (linForm ℓ - 1)))
  rw [map_sub, map_one, sub_eq_zero] at h1
  rw [← h1]
  simp [linForm, linEval]

theorem abs_le (h : HermNorm n) {J : Ideal (MvPolynomial (Fin n) ℂ)} {u ℓ x : Fin n → ℂ}
    (hx : x ∈ zeroSet (J ⊔ Ideal.span {linForm ℓ - 1})) :
    |Real.log (h.dualNorm x) - Real.log ‖linEval u x‖| ≤ |fsLog h u x| + |fsLog h ℓ x| := by
  have hℓ := linEval_eq_one hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp [linEval] at hℓ
  have hd := (h.dualNorm_pos hx0).ne'
  have hfℓ : fsLog h ℓ x = -Real.log (h.dualNorm x) := by
    show Real.log (‖linEval ℓ x‖ / h.dualNorm x) = _
    rw [hℓ, norm_one, one_div, Real.log_inv]
  by_cases hu : linEval u x = 0
  · rw [hu, norm_zero, Real.log_zero, sub_zero, hfℓ, abs_neg]
    exact le_add_of_nonneg_left (abs_nonneg _)
  · have hfu : fsLog h u x = Real.log ‖linEval u x‖ - Real.log (h.dualNorm x) := by
      show Real.log (‖linEval u x‖ / h.dualNorm x) = _
      rw [Real.log_div (norm_ne_zero_iff.mpr hu) hd]
    rw [hfu, abs_sub_comm]
    exact le_add_of_nonneg_right (abs_nonneg _)

end SliceLogIntegrableProof

open SliceLogIntegrableProof in

theorem SliceLogIntegrable.proof (hG : SliceFsLogIntegrable.Statement) : SliceLogIntegrable.Statement := by
  classical
  intro n e h J F u ℓ A hJ hF hu hℓ hA
  obtain ⟨hprime, hdim, -⟩ := SliceIdeal.proof n (e + 1) J F ℓ hJ hF hℓ
  have hsm : SmoothNear (zeroSet (J ⊔ Ideal.span {linForm ℓ - 1})) fun x => Real.log (h.dualNorm x) := by
    refine ⟨{x | x ≠ 0}, isOpen_ne, fun x hx hx0 => ?_, h.contDiffOn_log_dualNorm⟩
    have h1 := linEval_eq_one hx
    rw [hx0] at h1
    simp [linEval] at h1
  have hcu : Continuous fun x : Fin n → ℂ => linEval u x := by
    unfold linEval
    fun_prop
  have hcd : Continuous h.dualNorm := by
    unfold HermNorm.dualNorm
    fun_prop
  have hmeas : Measurable fun x : Fin n → ℂ => Real.log (h.dualNorm x) - Real.log ‖linEval u x‖ :=
    (Real.measurable_log.comp hcd.measurable).sub
      (Real.measurable_log.comp (continuous_norm.comp hcu).measurable)
  have hm := (SheetSumMeasurable.proof n (e + 1) _ A _ _ hprime hdim hA hmeas fun _ => hsm).2
  refine ((hG n e h J F u ℓ A hJ hF hu hℓ hA).add (hG n e h J F ℓ ℓ A hJ hF hℓ hℓ hA)).mono'
    hm.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  have hfin := IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hA y
  simp only [Pi.add_apply, chartAbsDens, sheetSum]
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin,
    finsum_mem_eq_finite_toFinset_sum _ hfin, ← Finset.sum_add_distrib, Real.norm_eq_abs,
    abs_of_nonneg (Finset.sum_nonneg fun x _ => by split_ifs <;> positivity)]
  refine Finset.sum_le_sum fun x hx => ?_
  rw [Set.Finite.mem_toFinset] at hx
  split_ifs
  · rw [abs_mul, abs_mul, abs_mul, ← add_mul]
    exact mul_le_mul_of_nonneg_right (abs_le h hx.1) (abs_nonneg _)
  · simp

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceMassFiniteDirect
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix Metric Set ComplexSets

noncomputable section

theorem SliceMassFinite.proof' (hL : ConeSheetGramLintegral.Statement) (hMF : MassFinite.Statement)
    (hD : ConeDimOfChowForm.Statement) : SliceMassFinite.Statement := by
  intro n d h I ℓ A hI hℓ hdim hA
  cases d with
  | zero =>
    have hconst : chartAbsDens I A (fun _ => 1) (fun _ x => Real.log (h.dualNorm x)) =
        fun _ => chartAbsDens I A (fun _ => 1) (fun _ x => Real.log (h.dualNorm x)) 0 :=
      funext fun y => congrArg _ (Subsingleton.elim y 0)
    rw [hconst]
    have : IsFiniteMeasure (volume : Measure (Fin 0 → ℂ)) := by
      rw [MeasureTheory.volume_pi, Measure.pi_of_empty (x := 0)]
      infer_instance
    exact integrable_const _
  | succ e =>
    obtain ⟨W, F, hW, hFW, hℓW, hWI⟩ := SliceMassFinite.exists_projClosure I ℓ hI hℓ hdim
    subst hWI
    have hdimW : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = ((e + 1 + 1 : ℕ) : WithBot ℕ∞) :=
      hD ℂ n (e + 2) W F hW hFW
    have hpm : Continuous fun z : EuclideanSpace ℂ (Fin n) => h.pointOf z := by
      unfold HermNorm.pointOf
      exact continuous_const.matrix_mulVec (PiLp.continuous_ofLp 2 _)
    have hFm : Measurable fun z : EuclideanSpace ℂ (Fin n) => ENNReal.ofReal
        ((ball (0 : EuclideanSpace ℂ (Fin n)) 1).indicator
          (fun z => |(fun _ => (1 : ℝ)) (h.pointOf z)|) z) :=
      ENNReal.measurable_ofReal.comp (measurable_const.indicator measurableSet_ball)
    have k1 := (hL n (e + 1) h W ℓ A _ hW hdimW hℓW hA hFm).2
    rw [lintegral_congr fun y => sheetSum_lintegral_eq h W ℓ A (fun _ => (1 : ℝ))
      (fun _ _ _ => rfl) y, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at k1

    have hball : ∫⁻ z in {z : EuclideanSpace ℂ (Fin n) | ∀ q ∈ W, eval (h.pointOf z) q = 0},
        ENNReal.ofReal ((ball (0 : EuclideanSpace ℂ (Fin n)) 1).indicator
          (fun z => |(fun _ => (1 : ℝ)) (h.pointOf z)|) z)
          ∂(Measure.hausdorffMeasure ((2 * (e + 1 + 1) : ℕ) : ℝ)) < ⊤ := by
      have hfun : (fun z : EuclideanSpace ℂ (Fin n) => ENNReal.ofReal
          ((ball (0 : EuclideanSpace ℂ (Fin n)) 1).indicator
            (fun z => |(fun _ => (1 : ℝ)) (h.pointOf z)|) z)) =
          (ball (0 : EuclideanSpace ℂ (Fin n)) 1).indicator 1 := by
        funext z
        by_cases hz : z ∈ ball (0 : EuclideanSpace ℂ (Fin n)) 1
        · simp [indicator_of_mem hz]
        · simp [indicator_of_notMem hz]
      rw [hfun, lintegral_indicator_one measurableSet_ball, Measure.restrict_apply measurableSet_ball]
      have hset : ball (0 : EuclideanSpace ℂ (Fin n)) 1 ∩
          {z : EuclideanSpace ℂ (Fin n) | ∀ q ∈ W, eval (h.pointOf z) q = 0} =
          {z : EuclideanSpace ℂ (Fin n) | ‖z‖ < 1 ∧ ∀ q ∈ W, eval (h.pointOf z) q = 0} := by
        ext z
        simp
      rw [hset]
      exact coneBall_hausdorff_lt_top hMF (e := e + 1) h W hW.isPrime hdimW
    have hc0 : ENNReal.ofReal (Real.pi ^ (e + 1 + 1) / ((e + 1 + 1).factorial : ℝ)) ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
    obtain ⟨hM0, -⟩ := coordBall_mass (n := n) (m := e + 1 + 1) (le_of_ringKrullDim_quotient W hdimW)
    have hfin : ∫⁻ y, ENNReal.ofReal (chartAbsDens (W ⊔ Ideal.span {linForm ℓ - 1}) A (fun _ => 1)
        (fun _ x => Real.log (h.dualNorm x)) y) < ⊤ := by
      rw [lt_top_iff_ne_top]
      intro htop
      rw [htop, ENNReal.mul_top hc0, ENNReal.mul_top hM0.ne'] at k1
      exact (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hball).ne k1

    have hmeas : Measurable (chartAbsDens (W ⊔ Ideal.span {linForm ℓ - 1}) A (fun _ => 1)
        (fun _ x => Real.log (h.dualNorm x))) :=
      SheetSumMeasurable.measurable_sheetSum hA (fun a b => |a * b|)
        (continuous_abs.comp (continuous_fst.mul continuous_snd)).measurable measurable_const _
    have hnn : ∀ y, 0 ≤ chartAbsDens (W ⊔ Ideal.span {linForm ℓ - 1}) A (fun _ => 1)
        (fun _ x => Real.log (h.dualNorm x)) y :=
      fun y => finsum_nonneg fun x => finsum_nonneg fun _ => by split_ifs <;> positivity
    exact ⟨hmeas.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hnn)).2 hfin⟩

end

end GroundTheory.Heights₂.Heights
end

