import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ZerosDisc
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LFunctionConjEqZero
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0035
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ZeroFreePrincipal
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0036
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0031
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FinprodLocalDifferentIdealNormEqDiscr
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ThetaConstantWeber
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0001
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0014
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0022
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.IsSemiChar
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormRayClassFamilyFOneGeOfRealCharacter
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LamIdealOfNotPrimePow
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RayClassIdealCountEqNcardShiftedBinaryForm
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0013

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExceptionalDirichletZeroUniqueZeroFreeRegion
section
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical

namespace GlobalTheory.ExceptionalPair

theorem one_le_log {M : ℕ} (hM : 3 ≤ M) : 1 ≤ Real.log M := by
  have hM' : (3 : ℝ) ≤ M := by exact_mod_cast hM
  rw [Real.le_log_iff_exp_le (by linarith)]
  linarith [Real.exp_one_lt_d9]

theorem log_mul_le {M : ℕ} (hM : 3 ≤ M) {a : ℝ} (ha : 0 < a) (ha3 : a ≤ 3) :
    Real.log (a * M) ≤ 2 * Real.log M := by
  have hM' : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  rw [Real.log_mul ha.ne' hM0.ne']
  have := Real.log_le_log ha (show a ≤ (M : ℝ) by linarith)
  linarith

theorem le_log_mul {M : ℕ} (hM : 3 ≤ M) {a : ℝ} (ha : 1 ≤ a) :
    Real.log M ≤ Real.log (a * M) := by
  have hM' : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  exact Real.log_le_log hM0 (le_mul_of_one_le_left hM0.le ha)

theorem div_log_le {M : ℕ} (hM : 3 ≤ M) {c₁ c : ℝ} (h0 : 0 ≤ c) (h : c₁ ≤ c / 2) :
    c₁ / Real.log M ≤ c / Real.log (2 * M) := by
  have hl := log_mul_le hM (a := 2) (by norm_num) (by norm_num)
  have hpos : 0 < Real.log M := lt_of_lt_of_le one_pos (one_le_log hM)
  have hpos2 : 0 < Real.log (2 * M) := by
    linarith [le_log_mul hM (a := 2) (by norm_num)]
  rw [div_le_div_iff₀ hpos hpos2]
  nlinarith [mul_nonneg (sub_nonneg.2 h) hpos2.le, mul_nonneg h0 (sub_nonneg.2 hl)]

private theorem exists_ne_zero_smul_mem_of_mem_span' {a b x y : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hx : 0 < x) (hxy : x ≤ y) :
    a / y ≤ b / x := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  rw [div_le_div_iff₀ hy hx]
  nlinarith [mul_le_mul_of_nonneg_right hab hx.le, mul_le_mul_of_nonneg_left hxy (ha.trans hab)]

theorem main : ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ c₀ → ∃ c : ℝ, 0 < c ∧ ∀ (M : ℕ) [NeZero M], 3 ≤ M → (∀ (χ χ' : DirichletCharacter ℂ M) (β β' : ℝ), IsExc c₁ χ β → IsExc c₁ χ' β' → χ = χ' ∧ β = β') ∧ (∀ (χ : DirichletCharacter ℂ M) (β : ℝ), IsExc c₁ χ β → χ ≠ 1 ∧ 7 / 8 ≤ β ∧ LFunction χ β = 0 ∧ ord χ β = 1 ∧ c / ((M : ℝ) ^ 2 * Real.log M) ≤ 1 - β) ∧ ∀ (χ : DirichletCharacter ℂ M) (ρ : ℂ), ρ.re < 1 → LFunction χ ρ = 0 → (ρ.im = 0 ∧ IsExc c₁ χ ρ.re) ∨ ρ.re ≤ 1 - c / Real.log (M * (|ρ.im| + 2)) := by
  obtain ⟨cu, hcu, hU⟩ := GlobalTheory.RealZeroNearOne.main
  obtain ⟨cp, hcp, hP⟩ := GlobalTheory.ZeroFreePrincipal.zero_free
  obtain ⟨cz, hcz, hZ⟩ := GlobalTheory.ZeroFreeComplex.zero_free_region
  obtain ⟨cs, hcs, hS⟩ := GlobalTheory.T.exists_dirichletLFunction_zero_gap_near_one
  refine ⟨min (1 / 8) (min (cu / 2) (cp / 2)),
    lt_min (by norm_num) (lt_min (by linarith) (by linarith)), fun c₁ hc₁ hc₁0 => ?_⟩
  have hc18 : c₁ ≤ 1 / 8 := hc₁0.trans (min_le_left _ _)
  have hcu2 : c₁ ≤ cu / 2 := hc₁0.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hcp2 : c₁ ≤ cp / 2 := hc₁0.trans ((min_le_right _ _).trans (min_le_right _ _))
  set c := min c₁ (min cz (min cp (cs / 2))) with hcdef
  have hcpos : 0 < c := lt_min hc₁ (lt_min hcz (lt_min hcp (by linarith)))
  have hcc₁ : c ≤ c₁ := min_le_left _ _
  have hccz : c ≤ cz := (min_le_right _ _).trans (min_le_left _ _)
  have hccp : c ≤ cp := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hccs : c ≤ cs / 2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨c, hcpos, fun M _ hM => ?_⟩
  have hM' : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hlog1 : 1 ≤ Real.log M := one_le_log hM
  have hlogpos : 0 < Real.log M := lt_of_lt_of_le one_pos hlog1
  have hsmall : c₁ / Real.log M ≤ 1 / 8 := (div_le_self hc₁.le hlog1).trans hc18
  have hlogT : ∀ t : ℝ, 0 < Real.log (M * (|t| + 2)) := fun t =>
    Real.log_pos (by nlinarith [abs_nonneg t])
  have hexc : ∀ (χ : DirichletCharacter ℂ M) (β : ℝ), IsExc c₁ χ β →
      χ ≠ 1 ∧ 7 / 8 ≤ β ∧ LFunction χ β = 0 ∧ 1 - cu / Real.log (2 * M) ≤ β := by
    intro χ β h
    obtain ⟨_, hlt, hlt1, hL⟩ := h
    have hβ : 7 / 8 ≤ β := by linarith
    have hne : (β : ℂ) ≠ 1 := fun h => by
      have := congrArg Complex.re h
      simp at this
      linarith
    have hLχ : LFunction χ β = 0 :=
      (GlobalTheory.T.dirichletL_zeros_eq_primitiveCharacter_zeros M χ β (by simp; linarith) (Or.inr hne)).1.mpr hL
    refine ⟨fun hχ => ?_, hβ, hLχ, by linarith [div_log_le hM hcu.le hcu2]⟩
    rw [hχ] at hLχ
    have h1 := hP M (β : ℂ) hne hLχ
    have e : (M : ℝ) * 2 = 2 * M := mul_comm _ _
    rw [Complex.ofReal_re, Complex.ofReal_im, abs_zero, zero_add, e] at h1
    linarith [div_log_le hM hcp.le hcp2]
  refine ⟨fun χ χ' β β' h h' => ?_, fun χ β h => ?_, fun χ ρ hre hL => ?_⟩
  · obtain ⟨n1, -, L1, b1⟩ := hexc χ β h
    obtain ⟨n2, -, L2, b2⟩ := hexc χ' β' h'
    obtain ⟨s1, -⟩ := h
    obtain ⟨s2, -⟩ := h'
    obtain ⟨e1, e2, -⟩ := hU M χ χ' β β' n1 n2 s1 s2 b1 b2 L1 L2
    exact ⟨e1, e2⟩
  · obtain ⟨n1, h78, L1, b1⟩ := hexc χ β h
    obtain ⟨s1, -⟩ := h
    refine ⟨n1, h78, L1, ?_, ?_⟩
    · have hd := (hU M χ χ β β n1 n1 s1 s1 b1 b1 L1 L1).2.2
      have h1 := (GlobalTheory.RealZeroNearOne.analyticAt_L n1 (β : ℂ)).analyticOrderAt_eq_one_of_zero_deriv_ne_zero
        L1 hd
      rw [GlobalTheory.Lin.ord, analyticOrderNatAt, h1]
      rfl
    · have h1 := hS M χ β (Or.inl n1) L1 (by simp)
      rw [Complex.ofReal_re] at h1
      have hl3 := log_mul_le hM (a := 3) (by norm_num) le_rfl
      have hl3pos : 0 < Real.log (3 * M) := Real.log_pos (by linarith)
      have hD : 0 < (M : ℝ) ^ 2 * Real.log M := by positivity
      have hE : 0 < (M : ℝ) ^ 2 * Real.log (3 * M) := by positivity
      calc c / ((M : ℝ) ^ 2 * Real.log M) ≤ (cs / 2) / ((M : ℝ) ^ 2 * Real.log M) :=
            exists_ne_zero_smul_mem_of_mem_span' hcpos.le hccs hD le_rfl
        _ = cs / (2 * ((M : ℝ) ^ 2 * Real.log M)) := div_div cs 2 _
        _ ≤ cs / ((M : ℝ) ^ 2 * Real.log (3 * M)) :=
            exists_ne_zero_smul_mem_of_mem_span' hcs.le le_rfl hE (by nlinarith [sq_nonneg (M : ℝ)])
        _ ≤ 1 - β := h1
  · by_cases hreal : χ ^ 2 = 1 ∧ ρ.im = 0
    · obtain ⟨hsq, him⟩ := hreal
      have hρ : ρ = (ρ.re : ℂ) := Complex.ext (by simp) (by simp [him])
      by_cases hbig : 1 - c₁ / Real.log M < ρ.re
      · left
        refine ⟨him, ?_⟩
        have hpos : 0 < ρ.re := by linarith
        have hne : ρ ≠ 1 := fun h => by
          rw [h] at hre
          simp at hre
        have hL' := (GlobalTheory.T.dirichletL_zeros_eq_primitiveCharacter_zeros M χ ρ hpos (Or.inr hne)).1.mp hL
        unfold IsExc
        refine ⟨hsq, hbig, hre, ?_⟩
        rw [← hρ]
        exact hL'
      · right
        replace hbig := not_lt.mp hbig
        rw [him, abs_zero, zero_add]
        have h2 : Real.log M ≤ Real.log (M * 2) := by
          rw [mul_comm]
          exact le_log_mul hM (by norm_num)
        have := exists_ne_zero_smul_mem_of_mem_span' hcpos.le hcc₁ hlogpos h2
        linarith
    · right
      have hne' : χ ^ 2 = 1 → ρ.im ≠ 0 := fun h h' => hreal ⟨h, h'⟩
      by_cases hχ : χ = 1
      · have him : ρ.im ≠ 0 := hne' (by rw [hχ]; exact one_pow 2)
        have hne : ρ ≠ 1 := fun h => him (by rw [h]; simp)
        rw [hχ] at hL
        have h1 := hP M ρ hne hL
        have := exists_ne_zero_smul_mem_of_mem_span' hcpos.le hccp (hlogT ρ.im) le_rfl
        linarith
      · have hor : χ ^ 2 ≠ 1 ∨ ρ.im ≠ 0 := by
          by_cases h : χ ^ 2 = 1
          · exact Or.inr (hne' h)
          · exact Or.inl h
        have h1 := hZ M χ ρ hχ hL hor
        have := exists_ne_zero_smul_mem_of_mem_span' hcpos.le hccz (hlogT ρ.im) le_rfl
        linarith

end GlobalTheory.ExceptionalPair
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FinprodLocalDifferentIdealNormEqDiscrStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finprod_localDifferentIdealNorm_eq_discr : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (σ : E →ₐ[F] E), IsCMExt F E σ → (∀ x : E, star x = σ x) → Formalism.HermitianLatticesTheory.IsCMUnram E → (Function.mulSupport (normDifferentV F)).Finite ∧ ((∏ᶠ v, normDifferentV F v : ℕ) : ℝ) = absDiscr F ∧ absDiscr F = (2 * Formalism.HermitianLatticesTheory.vInv E) ^ Formalism.HermitianLatticesTheory.fDeg E := by
  first | exact @GlobalTheory.LocalDifferentProduct.prod_normDifferentV | exact GlobalTheory.LocalDifferentProduct.prod_normDifferentV | (intros; apply GlobalTheory.LocalDifferentProduct.prod_normDifferentV <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.JacobiTripleProductTwoVariableTheta
section
open Complex
open UpperHalfPlane hiding I
open scoped Real

noncomputable section

namespace GlobalTheory.JacobiTriple

theorem tripleProduct : GlobalTheory.ThetaWeberRoad.TripleProduct := by
  intro τ z
  set s := cexp (π * I * (τ : ℂ)) with hs
  set x := cexp (2 * π * I * z) with hx
  have hτ : 0 < (τ : ℂ).im := τ.2
  have hs1 : ‖s‖ < 1 := norm_exp_pi_I_lt_one (τ : ℂ) hτ
  have hs0 : s ≠ 0 := exp_ne_zero _
  have hx0 : x ≠ 0 := exp_ne_zero _
  have ht1 : ‖s ^ 2‖ < 1 := by
    rw [norm_pow]; nlinarith [norm_nonneg s]
  obtain ⟨hP, hP0, -⟩ := qPoch_tendsto (s ^ 2) ht1
  have hT := GlobalTheory.T.jacobi_triple_product_limit (τ : ℂ) z hτ
  rw [(multipliable_tpFactor τ z).hasProd_iff_tendsto_nat]
  have key : ∀ n : ℕ, ∏ k ∈ Finset.range n, GlobalTheory.ThetaWeberRoad.tpFactor τ z k =
      qPoch (s ^ 2) n * ∑ j ∈ Finset.Icc (-(n : ℤ)) n,
        finCoeff (cexp (π * I * (τ : ℂ)) ^ 2) n j * jacobiTheta₂_term j z τ := by
    intro n
    rw [Finset.prod_congr rfl (fun k _ => tpFactor_eq τ z k), Finset.prod_mul_distrib]
    have hf := GlobalTheory.T.jacobiTriple_finite_product s x hs0 hs1 hx0 n
    simp only [hs, hx] at hf
    simp only [hf, jacobiTheta₂_term_eq_zpow]
    rfl
  simp_rw [key]
  have := hP.mul hT
  rwa [mul_left_comm, mul_inv_cancel₀ hP0, mul_one] at this

end GlobalTheory.JacobiTriple
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatticeJetsAreBoundedMomentsOfTensorFourthPowerStatement
section
open GlobalTheory.MomN Formalism.L2.Th1.H
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeJetsAreBoundedMoments_of_tensorFourthPower : ∀ (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (n : Type) [Fintype n] (ω : ℂ_[q]) (Λ : AddSubgroup (n → ℂ)) (G : (n → ℂ) → ℂ), ContDiff ℂ ⊤ G → LatInt ι ω (pow4 Λ) (tens4 G) → LatInt ι ω Λ G := by
  first | exact @GlobalTheory.MomRoot.jets_root | exact GlobalTheory.MomRoot.jets_root | (intros; apply GlobalTheory.MomRoot.jets_root <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormRayClassFamilyFOneGeOfRealCharacterStatement
section
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_rayClassFamily_F_one_ge_of_real_character : ∃ A c : ℝ, 0 < A ∧ 0 < c ∧ ∀ (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ), χ * χ = 1 → c / 𝓕.B ^ A ≤ ‖𝓕.F χ 1‖ := by
  first | exact @GlobalTheory.Hk.RealChar.norm_F_one_ge | exact GlobalTheory.Hk.RealChar.norm_F_one_ge | (intros; apply GlobalTheory.Hk.RealChar.norm_F_one_ge <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RayClassIdealCountEqNcardShiftedBinaryFormStatement
section
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rayClassIdealCount_eq_ncard_shiftedBinaryForm : ∀ (K : Type) [Field K] [NumberField K] (d M : ℕ) (x : K), d.Prime → d % 4 = 3 → 100 ≤ d → x ^ 2 = -(d : K) → Module.finrank ℚ K = 2 → 3 ≤ M → ∀ D : RayData K M, ∀ g : D.G, ∃ α γ l θ₁ θ₂ : ℝ, 1 ≤ α ∧ 1 ≤ γ ∧ α * γ = d * (M : ℝ) ^ 4 / 4 ∧ (∀ v : ℤ × ℤ, ∃ n : ℕ, 1 ≤ n ∧ qForm α γ l θ₁ θ₂ v = n) ∧ ∀ n : ℕ, aRay D g n = (({v : ℤ × ℤ | qForm α γ l θ₁ θ₂ v = n}.ncard : ℕ) : ℝ) := by
  first | exact @GlobalTheory.Hk.RayForm.aRay_eq_ncard_qForm | exact GlobalTheory.Hk.RayForm.aRay_eq_ncard_qForm | (intros; apply GlobalTheory.Hk.RayForm.aRay_eq_ncard_qForm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RayClassLFunctionLogDerivLocalFormula
section
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical

namespace GlobalTheory.HkLocal

theorem analyticOrderNatAt_comp_affine (g : ℂ → ℂ) (c ρ w : ℂ) (hρ : ρ ≠ 0) :
    analyticOrderNatAt (fun z => g (c + ρ * z)) w = analyticOrderNatAt g (c + ρ * w) := by
  unfold analyticOrderNatAt
  congr 1
  have hd : HasDerivAt (fun z : ℂ => c + ρ * z) ρ w := by
    simpa using ((hasDerivAt_id w).const_mul ρ).const_add c
  have h := analyticOrderAt_comp_of_deriv_ne_zero (f := g) (g := fun z : ℂ => c + ρ * z) (z₀ := w)
    (by fun_prop) (by rw [hd.deriv]; exact hρ)
  exact h

theorem logDeriv_local : ∃ C : ℝ, 0 < C ∧ ∀ (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (t : ℝ), {w : ℂ | ‖w - (5 / 4 + t * I)‖ ≤ 3 / 5 ∧ 𝓕.F χ w = 0}.Finite ∧ (∑ᶠ w ∈ {w : ℂ | ‖w - (5 / 4 + t * I)‖ ≤ 3 / 5 ∧ 𝓕.F χ w = 0}, (analyticOrderNatAt (𝓕.F χ) w : ℝ)) ≤ C * 𝓕.ell t ∧ ∀ s : ℂ, ‖s - (5 / 4 + t * I)‖ ≤ 1 / 2 → 𝓕.F χ s ≠ 0 → ‖deriv (𝓕.F χ) s / 𝓕.F χ s - ∑ᶠ w ∈ {w : ℂ | ‖w - (5 / 4 + t * I)‖ ≤ 3 / 5 ∧ 𝓕.F χ w = 0}, (analyticOrderNatAt (𝓕.F χ) w : ℂ) / (s - w)‖ ≤ C * 𝓕.ell t := by
  obtain ⟨C, hC, H⟩ := GlobalTheory.LogDerivZeros.main (5/7) (6/7) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨12 * C, by positivity, ?_⟩
  intro 𝓕 χ t
  obtain ⟨han, hLS, hgr, -⟩ := GlobalTheory.T.rayClassLFunctionFamily_continuation_growth 𝓕 χ
  set c : ℂ := 5 / 4 + t * I with hc
  have hcre : c.re = 5 / 4 := by simp [hc]
  have hcn : ‖c‖ ≤ 5 / 4 + |t| := by
    refine (norm_add_le _ _).trans ?_
    simp
  have hB : 4 ≤ 𝓕.B := 𝓕.B_ge
  have ht : 0 ≤ |t| := abs_nonneg t
  set ρ : ℂ := 7 / 10 with hρ
  have hρ0 : ρ ≠ 0 := by rw [hρ]; norm_num
  have hρn : ‖ρ‖ = 7 / 10 := by simp [hρ]
  have hre : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, 11 / 20 ≤ (c + ρ * z).re ∧ ‖ρ * z‖ ≤ 7 / 10 := by
    intro z hz
    have hz1 : ‖z‖ ≤ 1 := by simpa using hz
    have h1 : ‖ρ * z‖ ≤ 7 / 10 := by rw [norm_mul, hρn]; linarith
    have := (abs_le.1 ((Complex.abs_re_le_norm _).trans h1)).1
    refine ⟨?_, h1⟩
    rw [add_re, hcre]; linarith
  have hf : AnalyticOnNhd ℂ (fun z => 𝓕.F χ (c + ρ * z)) (Metric.closedBall 0 1) := by
    intro z hz
    have h1 : AnalyticAt ℂ (𝓕.F χ) (c + ρ * z) :=
      han _ (show 1 / 2 < (c + ρ * z).re by linarith [(hre z hz).1])
    exact AnalyticAt.comp (g := 𝓕.F χ) (f := fun z => c + ρ * z) h1 (by fun_prop)
  have hlow : 1 / 100 ≤ ‖𝓕.F χ (c + ρ * 0)‖ := by
    have h1 : 1 < c.re := by rw [hcre]; norm_num
    have h2 := (GlobalTheory.T.rayClassFamily_logDeriv_re_gt_one 𝓕 χ c h1).2.1
    rw [hcre] at h2
    rw [mul_zero, add_zero, (hLS c h1).2, norm_mul]
    have h3 : 1 / 4 ≤ ‖(if χ = 1 then c - 1 else 1 : ℂ)‖ := by
      split_ifs
      · have := (le_abs_self _).trans (Complex.abs_re_le_norm (c - 1))
        rw [sub_re, hcre, one_re] at this
        linarith
      · norm_num
    have h4 : 1 / 25 ≤ ‖LSeries (𝓕.aChi χ) c‖ := le_trans (by norm_num) h2
    calc (1 / 100 : ℝ) = (1 / 4) * (1 / 25) := by norm_num
      _ ≤ _ := by gcongr
  have hf0 : 𝓕.F χ (c + ρ * 0) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hlow
    linarith
  have hM : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      ‖𝓕.F χ (c + ρ * z)‖ ≤ 300 * 𝓕.B * (|t| + 3) ^ 2 := by
    intro z hz
    obtain ⟨h1, h2⟩ := hre z hz
    have hn : ‖c + ρ * z‖ + 1 ≤ |t| + 3 := by
      have := norm_add_le c (ρ * z)
      linarith
    refine (hgr _ h1).trans ?_
    gcongr
  obtain ⟨⟨hfin, hcnt⟩, hb⟩ := H _ _ hf hf0 hM
  have hset : {w : ℂ | ‖w - c‖ ≤ 3 / 5 ∧ 𝓕.F χ w = 0} =
      (fun z => c + ρ * z) '' {w : ℂ | ‖w‖ ≤ 6 / 7 ∧ 𝓕.F χ (c + ρ * w) = 0} := by
    ext w
    constructor
    · rintro ⟨h1, h2⟩
      have e : c + ρ * ((w - c) / ρ) = w := by field_simp; ring
      refine ⟨(w - c) / ρ, ⟨?_, by rw [e]; exact h2⟩, e⟩
      rw [norm_div, hρn, div_le_iff₀ (by norm_num)]
      linarith
    · rintro ⟨z, ⟨h1, h2⟩, rfl⟩
      refine ⟨?_, h2⟩
      simp only [add_sub_cancel_left, norm_mul, hρn]
      linarith
  have hinj : Set.InjOn (fun z => c + ρ * z) {w : ℂ | ‖w‖ ≤ 6 / 7 ∧ 𝓕.F χ (c + ρ * w) = 0} :=
    fun a _ b _ h => mul_left_cancel₀ hρ0 (add_left_cancel h)
  have hlog : 1 + Real.log (300 * 𝓕.B * (|t| + 3) ^ 2 / ‖𝓕.F χ (c + ρ * 0)‖) ≤ 8 * 𝓕.ell t ∧
      0 ≤ 𝓕.ell t := by
    unfold LFam.ell
    set X : ℝ := 𝓕.B * (|t| + 2) with hX
    have hX8 : 8 ≤ X := by rw [hX]; nlinarith
    have hl1 : 1 ≤ Real.log X := by
      rw [Real.le_log_iff_exp_le (show 0 < X by linarith)]
      linarith [Real.exp_one_lt_d9]
    have hp : 0 < ‖𝓕.F χ (c + ρ * 0)‖ := norm_pos_iff.2 hf0
    have h8 : 300 * 𝓕.B * (|t| + 3) ^ 2 / ‖𝓕.F χ (c + ρ * 0)‖ ≤ X ^ 7 := by
      rw [div_le_iff₀ hp]
      have hX0 : 0 ≤ X := by linarith
      have h5 : (8 : ℝ) ^ 5 ≤ X ^ 5 := by gcongr
      have h6 : 4 * (𝓕.B * (|t| + 2) ^ 2) ≤ X ^ 2 := by
        rw [hX, mul_pow, pow_two 𝓕.B, mul_assoc]
        gcongr
      have h7 : (|t| + 3) ^ 2 ≤ (9 / 4) * (|t| + 2) ^ 2 := by nlinarith
      have h9 : 𝓕.B * (|t| + 3) ^ 2 ≤ 𝓕.B * ((9 / 4) * (|t| + 2) ^ 2) := by gcongr
      have h10 : 0 ≤ X ^ 2 := by positivity
      calc 300 * 𝓕.B * (|t| + 3) ^ 2 ≤ 8 ^ 5 * X ^ 2 * (1 / 100) := by nlinarith
        _ ≤ X ^ 5 * X ^ 2 * ‖𝓕.F χ (c + ρ * 0)‖ := by gcongr
        _ = _ := by ring
    have h9 := Real.log_le_log (by positivity) h8
    rw [Real.log_pow] at h9
    push_cast at h9
    constructor <;> linarith
  obtain ⟨hlog, hell⟩ := hlog
  have hCl : C * (1 + Real.log (300 * 𝓕.B * (|t| + 3) ^ 2 / ‖𝓕.F χ (c + ρ * 0)‖)) ≤
      C * (8 * 𝓕.ell t) := by gcongr
  have hCe : 0 ≤ C * 𝓕.ell t := by positivity
  rw [hset]
  refine ⟨hfin.image _, ?_, ?_⟩
  · rw [finsum_mem_image hinj]
    simp only [analyticOrderNatAt_comp_affine _ _ _ _ hρ0] at hcnt
    refine hcnt.trans (hCl.trans ?_)
    linarith
  · intro s hs hLs
    have e : c + ρ * ((s - c) / ρ) = s := by field_simp; ring
    have hz : ‖(s - c) / ρ‖ ≤ 5 / 7 := by
      rw [norm_div, hρn, div_le_iff₀ (by norm_num)]
      linarith
    have hb' := hb ((s - c) / ρ) hz (by simpa only [e] using hLs)
    have hsre : 1 / 2 < s.re := by
      have := (hre ((s - c) / ρ) (by simpa only [mem_closedBall_zero_iff] using hz.trans (by norm_num))).1
      rw [e] at this
      linarith
    have hder : deriv (fun z => 𝓕.F χ (c + ρ * z)) ((s - c) / ρ) = ρ * deriv (𝓕.F χ) s := by
      have hd : HasDerivAt (fun z : ℂ => c + ρ * z) ρ ((s - c) / ρ) := by
        simpa using ((hasDerivAt_id ((s - c) / ρ)).const_mul ρ).const_add c
      have h1 : HasDerivAt (𝓕.F χ) (deriv (𝓕.F χ) s) (c + ρ * ((s - c) / ρ)) := by
        rw [e]; exact (han s hsre).differentiableAt.hasDerivAt
      have := (HasDerivAt.comp ((s - c) / ρ) h1 hd).deriv
      rw [mul_comm] at this
      exact this
    rw [finsum_mem_image hinj]
    simp only [analyticOrderNatAt_comp_affine _ _ _ _ hρ0, hder, e] at hb'
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin] at hb' ⊢
    have e2 : ∀ w : ℂ, (analyticOrderNatAt (𝓕.F χ) (c + ρ * w) : ℂ) / ((s - c) / ρ - w) =
        ρ * ((analyticOrderNatAt (𝓕.F χ) (c + ρ * w) : ℂ) / (s - (c + ρ * w))) := by
      intro w
      have : s - (c + ρ * w) = ρ * ((s - c) / ρ - w) := by field_simp; ring
      rw [this, ← mul_div_assoc, mul_div_mul_left _ _ hρ0]
    simp only [e2] at hb'
    rw [← Finset.mul_sum, mul_div_assoc, ← mul_sub, norm_mul, hρn] at hb'
    have := hb'.trans hCl
    linarith

end GlobalTheory.HkLocal
end

