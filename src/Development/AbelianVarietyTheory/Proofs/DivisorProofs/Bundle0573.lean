import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0555
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0526
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0559
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0542
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FinalD

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TprodLocalVolumeFactorLeZeta
section
open NumberField IsDedekindDomain GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory.EulerLocVol

theorem locFactor_eq_of_isPrime (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (hr : 1 ≤ r)
    (hw : (v.asIdeal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E))).IsPrime) :
    locFactor E r v = ∏ i ∈ Finset.Icc 2 r, (1 - (-1) ^ i * ((Ideal.absNorm v.asIdeal : ℝ) ^ i)⁻¹) := by
  classical
  unfold locFactor resOrder
  rw [if_pos hw]
  set w := v.asIdeal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) with hwdef
  set c := IsCMField.ringOfIntegersComplexConj E with hcdef
  have hcc : ∀ x, c (c x) = x := fun x => by
    ext; simp [hcdef]
  have hfix : ∀ a, c (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) a) = algebraMap _ _ a :=
    fun a => (IsCMField.ringOfIntegersComplexConj_eq_self_iff E _).2 ⟨a, rfl⟩
  have hle : w ≤ w.comap (c : 𝓞 E →+* 𝓞 E) := by
    rw [hwdef, Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Ideal.mem_comap]
    change c _ ∈ _
    rw [hfix]
    exact Ideal.mem_map_of_mem _ ha
  have hw0 : w ≠ ⊥ := by
    rw [hwdef, Ne, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)]
    exact v.ne_bot
  haveI hmax : w.IsMaximal := hw.isMaximal hw0
  letI : Field (𝓞 E ⧸ w) := Ideal.Quotient.field w
  haveI : Finite (𝓞 E ⧸ w) := Ideal.finiteQuotientOfFreeOfNeBot w hw0
  let σ : (𝓞 E ⧸ w) →+* (𝓞 E ⧸ w) := Ideal.quotientMap w (c : 𝓞 E →+* 𝓞 E) hle
  have hσ : ∀ x, σ (Ideal.Quotient.mk w x) = Ideal.Quotient.mk w (c x) := fun x => rfl
  letI : StarRing (𝓞 E ⧸ w) :=
    { star := σ
      star_involutive := fun x => by
        obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
        change σ (σ _) = _
        rw [hσ, hσ, hcc]
      star_mul := fun x y => by
        change σ (x * y) = σ y * σ x
        rw [map_mul, mul_comm]
      star_add := fun x y => map_add σ x y }
  have hstar : ∀ x, star (Ideal.Quotient.mk w x) = Ideal.Quotient.mk w (c x) := hσ
  rw [ncard_image_lifts_eq_card_specialUnitaryGroup w c hstar r]
  set q := Ideal.absNorm v.asIdeal with hq
  have hK : Nat.card (𝓞 E ⧸ w) = q ^ 2 := by
    have h := Ideal.absNorm_algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) v.asIdeal
    rw [← IsFractionRing.finrank_eq (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E) (𝓞 E) E,
      Algebra.IsQuadraticExtension.finrank_eq_two, Ideal.absNorm_apply (Ideal.map _ _),
      Submodule.cardQuot_apply] at h
    exact h
  have hq2 : 2 ≤ q := GlobalTheory.FiniteOrders.two_le_of_card_eq_sq hK
  have hs : ∃ a : 𝓞 E ⧸ w, star a ≠ a := by
    let f : (𝓞 (maximalRealSubfield E) ⧸ v.asIdeal) →+* (𝓞 E ⧸ w) :=
      Ideal.quotientMap w (algebraMap _ _) Ideal.le_comap_map
    have hf : ∀ a, f (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk w (algebraMap _ _ a) :=
      fun a => rfl
    refine exists_star_ne_of_not_surjective f (fun x => ?_) (fun x => ?_) (fun hsurj => ?_)
    · obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨a, ha⟩ := (IsCMField.ringOfIntegersComplexConj_eq_self_iff E (y + c y)).1
        (by change c _ = _; rw [map_add, hcc, add_comm])
      exact ⟨Ideal.Quotient.mk _ a, by rw [hf, ha, hstar, map_add]⟩
    · obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨a, ha⟩ := (IsCMField.ringOfIntegersComplexConj_eq_self_iff E (y * c y)).1
        (by change c _ = _; rw [map_mul, hcc, mul_comm])
      exact ⟨Ideal.Quotient.mk _ a, by rw [hf, ha, hstar, map_mul]⟩
    · haveI : Finite (𝓞 (maximalRealSubfield E) ⧸ v.asIdeal) :=
        Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
      have h1 := Nat.card_le_card_of_surjective f hsurj
      have h2 : Nat.card (𝓞 (maximalRealSubfield E) ⧸ v.asIdeal) = q := by
        rw [hq, Ideal.absNorm_apply, Submodule.cardQuot_apply]
      rw [hK, h2] at h1
      nlinarith
  have h := GlobalTheory.FiniteOrders.card_specialUnitaryGroup hK hs (Fin r) (Fintype.card_fin r) hr
  have h' := congrArg (Rat.cast : ℚ → ℝ) h
  push_cast at h'
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  rw [h', mul_div_cancel_left₀ _ (pow_ne_zero _ hq0.ne')]

theorem locFactor_nonneg_and_mul_le_one (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (hr : 1 ≤ r) :
    0 ≤ locFactor E r v ∧
      locFactor E r v * ∏ i ∈ Finset.Icc 2 r, (1 - ((Ideal.absNorm v.asIdeal : ℝ) ^ i)⁻¹) ≤ 1 := by
  set q : ℝ := (Ideal.absNorm v.asIdeal : ℝ) with hqdef
  have hq1 : (1 : ℝ) ≤ q := by
    have : Ideal.absNorm v.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
    rw [hqdef]
    exact_mod_cast Nat.one_le_iff_ne_zero.2 this
  have ht : ∀ i : ℕ, 0 ≤ (q ^ i)⁻¹ ∧ (q ^ i)⁻¹ ≤ 1 := fun i =>
    ⟨by positivity, inv_le_one_of_one_le₀ (one_le_pow₀ hq1)⟩
  have hg0 : 0 ≤ ∏ i ∈ Finset.Icc 2 r, (1 - (q ^ i)⁻¹) :=
    Finset.prod_nonneg fun i _ => sub_nonneg.2 (ht i).2
  have hg1 : ∏ i ∈ Finset.Icc 2 r, (1 - (q ^ i)⁻¹) ≤ 1 :=
    Finset.prod_le_one (fun i _ => sub_nonneg.2 (ht i).2) fun i _ => sub_le_self _ (ht i).1
  by_cases hp : (v.asIdeal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E))).IsPrime
  · rw [locFactor_eq_of_isPrime E r v hr hp, ← hqdef, ← Finset.prod_mul_distrib]
    have hf0 : ∀ i : ℕ, 0 ≤ 1 - (-1) ^ i * (q ^ i)⁻¹ := by
      intro i
      obtain ⟨h0, h1⟩ := ht i
      rcases neg_one_pow_eq_or ℝ i with h | h <;> rw [h] <;> linarith
    refine ⟨Finset.prod_nonneg fun i _ => hf0 i, ?_⟩
    refine Finset.prod_le_one (fun i _ => mul_nonneg (hf0 i) (sub_nonneg.2 (ht i).2)) fun i _ => ?_
    obtain ⟨h0, h1⟩ := ht i
    rcases neg_one_pow_eq_or ℝ i with h | h <;> rw [h] <;> nlinarith
  · have heq : locFactor E r v = ∏ i ∈ Finset.Icc 2 r, (1 - (q ^ i)⁻¹) := by
      let _ : Field (𝓞 (maximalRealSubfield E) ⧸ v.asIdeal) := Ideal.Quotient.field _
      have hc : Nat.card (𝓞 (maximalRealSubfield E) ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal := by
        rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
      have h := GlobalTheory.FiniteOrders.card_specialLinearGroup hc (Fin r) (Fintype.card_fin r) hr
      have hq : (0 : ℝ) < q := by linarith
      unfold locFactor resOrder
      rw [if_neg hp]
      have h' : (Nat.card (Matrix.SpecialLinearGroup (Fin r) (𝓞 (maximalRealSubfield E) ⧸ v.asIdeal)) : ℝ) =
          q ^ (r ^ 2 - 1) * ∏ i ∈ Finset.Icc 2 r, (1 - (q ^ i)⁻¹) := by
        have := congrArg (fun x : ℚ => (x : ℝ)) h
        push_cast at this
        exact this
      rw [h', ← hqdef, mul_div_cancel_left₀ _ (pow_ne_zero _ hq.ne')]
    rw [heq]
    exact ⟨hg0, mul_le_one₀ hg1 hg0 hg1⟩

theorem tprod_locFactor_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ), 2 ≤ r →
    Multipliable (GlobalTheory.SUVol.locFactor E r) →
      ∏' v, GlobalTheory.SUVol.locFactor E r v ≤
        (∏ i ∈ Finset.Icc 2 r, ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i) ^ ReciprocityTheory.ChartRestriction.G.FD.fdeg E := by
  intro E _ _ _ r hr hm
  let g : ℝ → ℝ := fun x => ∏ i ∈ Finset.Icc 2 r, (1 - (x ^ i)⁻¹)
  set Z : ℝ := ∏ i ∈ Finset.Icc 2 r, ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i with hZdef
  have hzeta : ∀ i ∈ Finset.Icc 2 r, 1 ≤ ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i := by
    intro i hi
    have hi2 : 2 ≤ i := (Finset.mem_Icc.1 hi).1
    have hs : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ i) := by
      have := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (by omega : 1 < i))
      simpa using this
    have := hs.le_tsum 0 (fun j _ => by positivity)
    simpa using this
  have hZ : 0 < Z := Finset.prod_pos fun i hi => lt_of_lt_of_le one_pos (hzeta i hi)
  have hf : fdeg E = Module.finrank ℚ (maximalRealSubfield E) := by
    have h2 : Module.finrank (maximalRealSubfield E) E = 2 :=
      Algebra.IsQuadraticExtension.finrank_eq_two _ _
    unfold fdeg
    rw [← Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E, h2]
    omega
  have g_nonneg : ∀ x : ℝ, 1 ≤ x → 0 ≤ g x := fun x hx =>
    Finset.prod_nonneg fun i _ => sub_nonneg.2 (inv_le_one_of_one_le₀ (one_le_pow₀ hx))
  have g_le_one : ∀ x : ℝ, 1 ≤ x → g x ≤ 1 := fun x hx =>
    Finset.prod_le_one (fun i _ => sub_nonneg.2 (inv_le_one_of_one_le₀ (one_le_pow₀ hx)))
      fun i _ => sub_le_self _ (by positivity)
  have g_mono : ∀ x y : ℝ, 1 ≤ x → x ≤ y → g x ≤ g y := fun x y hx hxy =>
    Finset.prod_le_prod (fun i _ => sub_nonneg.2 (inv_le_one_of_one_le₀ (one_le_pow₀ hx)))
      fun i _ => sub_le_sub_left (inv_anti₀ (by positivity) (pow_le_pow_left₀ (by linarith) hxy i)) _
  have hloc : ∀ v, 0 ≤ locFactor E r v ∧ locFactor E r v * g (Ideal.absNorm v.asIdeal) ≤ 1 :=
    fun v => locFactor_nonneg_and_mul_le_one E r v (by omega)
  let pv : HeightOneSpectrum (𝓞 (maximalRealSubfield E)) → ℕ := ReciprocityTheory.Neutral.Bridge.ratPrimeBelow
  have hN : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)),
      (pv v).Prime ∧ pv v ≤ Ideal.absNorm v.asIdeal := by
    intro v
    have hp := ReciprocityTheory.Neutral.Bridge.ratPrimeBelow_prime v
    obtain ⟨f, hfv⟩ := ReciprocityTheory.Neutral.Bridge.absNorm_eq_ratPrimeBelow_pow v
    have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
    have hf0 : f ≠ 0 := by rintro rfl; rw [pow_zero] at hfv; exact h1 hfv
    refine ⟨hp, ?_⟩
    rw [hfv]
    exact Nat.le_self_pow hf0 _
  have key : ∀ s : Finset (HeightOneSpectrum (𝓞 (maximalRealSubfield E))),
      ∏ v ∈ s, locFactor E r v ≤ Z ^ fdeg E := by
    intro s
    set T := s.image pv
    have hp1 : ∀ p ∈ T, (1 : ℝ) ≤ p := by
      intro p hp
      obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hp
      exact_mod_cast (hN v).1.one_lt.le
    have s1 : ∏ v ∈ s, g (pv v) ≤ ∏ v ∈ s, g (Ideal.absNorm v.asIdeal) := by
      refine Finset.prod_le_prod (fun v _ => g_nonneg _ (by exact_mod_cast (hN v).1.one_lt.le))
        fun v _ => g_mono _ _ (by exact_mod_cast (hN v).1.one_lt.le) (by exact_mod_cast (hN v).2)
    have s2 : ∏ v ∈ s, g (pv v) = ∏ p ∈ T, g p ^ (s.filter fun v => pv v = p).card := by
      rw [Finset.prod_comp (fun p : ℕ => g p) pv]
    have s3 : ∏ p ∈ T, g p ^ fdeg E ≤ ∏ p ∈ T, g p ^ (s.filter fun v => pv v = p).card := by
      refine Finset.prod_le_prod (fun p hp => pow_nonneg (g_nonneg _ (hp1 p hp)) _) fun p hp => ?_
      refine pow_le_pow_of_le_one (g_nonneg _ (hp1 p hp)) (g_le_one _ (hp1 p hp)) ?_
      rw [hf]
      obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hp
      exact ReciprocityTheory.Neutral.Bridge.card_fiber_ratPrimeBelow_le id Function.injective_id s (pv v) (hN v).1
    have s4 : Z⁻¹ ≤ ∏ p ∈ T, g p := by
      rw [Finset.prod_comm, hZdef, ← Finset.prod_inv_distrib]
      refine Finset.prod_le_prod (fun i _ => by positivity) fun i hi => ?_
      refine GlobalTheory.EulerLocVol.inv_zeta_le_prod_primes i (Finset.mem_Icc.1 hi).1 T fun p hp => ?_
      obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hp
      exact (hN v).1
    have hlow : (Z ^ fdeg E)⁻¹ ≤ ∏ v ∈ s, g (Ideal.absNorm v.asIdeal) :=
      calc (Z ^ fdeg E)⁻¹ = (Z⁻¹) ^ fdeg E := (inv_pow Z _).symm
        _ ≤ (∏ p ∈ T, g p) ^ fdeg E := pow_le_pow_left₀ (by positivity) s4 _
        _ = ∏ p ∈ T, g p ^ fdeg E := (Finset.prod_pow _ _ _).symm
        _ ≤ _ := s3
        _ = _ := s2.symm
        _ ≤ _ := s1
    have hL0 : 0 ≤ ∏ v ∈ s, locFactor E r v := Finset.prod_nonneg fun v _ => (hloc v).1
    have hprod : (∏ v ∈ s, locFactor E r v) * ∏ v ∈ s, g (Ideal.absNorm v.asIdeal) ≤ 1 := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_le_one (fun v _ => mul_nonneg (hloc v).1 (g_nonneg _ ?_)) fun v _ => (hloc v).2
      have : Ideal.absNorm v.asIdeal ≠ 0 := by
        rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
      exact_mod_cast Nat.one_le_iff_ne_zero.2 this
    have hZf : 0 < Z ^ fdeg E := pow_pos hZ _
    have h3 : (∏ v ∈ s, locFactor E r v) * (Z ^ fdeg E)⁻¹ ≤ 1 :=
      (mul_le_mul_of_nonneg_left hlow hL0).trans hprod
    rwa [← div_eq_mul_inv, div_le_one hZf] at h3
  exact le_of_tendsto hm.hasProd (Filter.Eventually.of_forall key)

end GlobalTheory.EulerLocVol
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UpperTriangularSignFormDiagonalUnimodularStatement
section
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.TorusFrame
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.upperTriangular_signForm_diagonal_unimodular : ∀ (r : ℕ) (b : Matrix (Fin r) (Fin r) ℂ) (s : Fin r → ℝ), (∀ a, s a = 1 ∨ s a = -1) → IsUnit b.det → (∀ a c : Fin r, c < a → b a c = 0) → bᵀ * diagonal (fun a => (s a : ℂ)) * b.map (starRingEnd ℂ) = diagonal (fun a => (s a : ℂ)) → (∀ a c : Fin r, a ≠ c → b a c = 0) ∧ ∀ a, ‖b a a‖ = 1 := by
  first | exact @GlobalTheory.upperTriangular_signForm_diagonal | exact GlobalTheory.upperTriangular_signForm_diagonal | (intros; apply GlobalTheory.upperTriangular_signForm_diagonal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylTensorCoefSpaceEndomorphismPreservesTorusWei
section
set_option autoImplicit false
noncomputable section
open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV
open scoped Matrix

namespace GlobalTheory.CoefTorusWeight

theorem coeff_aeval_scale {K σ : Type} [Field K] [Fintype σ] (c : σ → K) (F : MvPolynomial σ K)
    (m : σ →₀ ℕ) :
    coeff m (aeval (fun v => (C (c v) * X v : MvPolynomial σ K)) F) = (∏ v, c v ^ m v) * coeff m F := by
  classical
  induction F using MvPolynomial.induction_on' with
  | monomial u a =>
    have h : aeval (fun v => (C (c v) * X v : MvPolynomial σ K)) (monomial u a)
        = monomial u ((∏ v, c v ^ u v) * a) := by
      rw [aeval_monomial, Finsupp.prod_fintype _ _ (by simp), monomial_eq,
        Finsupp.prod_fintype _ _ (by simp)]
      simp only [mul_pow, Finset.prod_mul_distrib, ← C_pow, ← map_prod, algebraMap_eq, C_mul]
      ring
    rw [h, coeff_monomial, coeff_monomial]
    split_ifs with hu
    · rw [hu]
    · simp
  | add p q hp hq => rw [map_add, coeff_add, coeff_add, hp, hq, mul_add]

theorem coeff_actP_diag {K ι : Type} [Field K] [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)
    (t : ι → Fin n → Kˣ) (F : Pol K ι n) (m : (ι × Fin n × Fin n) →₀ ℕ) :
    coeff m (actP lam (fun τ => diagGL K n (t τ)) F)
      = detTwK lam (fun τ => diagGL K n (t τ)) *
        ((∏ v : ι × Fin n × Fin n, (t v.1 v.2.1 : K) ^ m v) * coeff m F) := by
  classical
  have h : trAct (fun τ => diagGL K n (t τ))
      = aeval (fun v : ι × Fin n × Fin n => (C (t v.1 v.2.1 : K) * X v : Pol K ι n)) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp only [trAct, Formalism.GradedWeylDivisibility.blockAct, aeval_X, diagGL, Matrix.diagonal_transpose]
    rw [Finset.sum_eq_single v.2.1]
    · simp
    · intro b _ hb
      simp [Matrix.diagonal_apply_ne _ (Ne.symm hb)]
    · simp
  rw [actP, LinearMap.smul_apply, AlgHom.toLinearMap_apply, coeff_smul, smul_eq_mul, h,
    coeff_aeval_scale]

theorem detTwK_ne_zero {K ι : Type} [Field K] [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)
    (h : ι → GL (Fin n) K) : detTwK lam h ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _ _ => Units.ne_zero _

theorem weight_preserved (K : Type) [Field K] [CharZero K] {ι : Type} [Fintype ι] {n : ℕ}
    (lam : ι → DomWeight n) (g : Module.End K (VV K lam))
    (hg : ∀ (h : ι → GL (Fin n) K) v, g (rhoK lam h v) = rhoK lam h (g v)) (v : VV K lam)
    (hv : ∀ m ∈ (v : Pol K ι n).support, ∀ τ a, ∑ s : Fin n, m (τ, a, s) = (lam τ).natW a) :
    ∀ m ∈ ((g v : VV K lam) : Pol K ι n).support, ∀ τ a,
      ∑ s : Fin n, m (τ, a, s) = (lam τ).natW a := by
  classical
  intro m hm τ0 a0
  let u : Kˣ := Units.mk0 (2 : K) two_ne_zero
  let t : ι → Fin n → Kˣ := fun τ a => if τ = τ0 ∧ a = a0 then u else 1
  have hprod : ∀ m : (ι × Fin n × Fin n) →₀ ℕ,
      (∏ v : ι × Fin n × Fin n, (t v.1 v.2.1 : K) ^ m v) = 2 ^ (∑ s : Fin n, m (τ0, a0, s)) := by
    intro m
    rw [Fintype.prod_prod_type, Finset.prod_eq_single τ0, Fintype.prod_prod_type,
      Finset.prod_eq_single a0, ← Finset.prod_pow_eq_pow_sum]
    · simp [t, u]
    · intro b _ hb
      simp [t, hb]
    · simp
    · intro b _ hb
      simp [t, hb]
    · simp
  set h : ι → GL (Fin n) K := fun τ => diagGL K n (t τ) with hh
  have hco : ∀ (w : VV K lam) (m : (ι × Fin n × Fin n) →₀ ℕ),
      coeff m ((rhoK lam h w : VV K lam) : Pol K ι n)
        = detTwK lam h * (2 ^ (∑ s : Fin n, m (τ0, a0, s)) * coeff m (w : Pol K ι n)) := by
    intro w m
    rw [← hprod]
    exact coeff_actP_diag lam t w m
  have h1 : rhoK lam h v = (detTwK lam h * 2 ^ (lam τ0).natW a0) • v := by
    apply Subtype.ext
    ext m'
    rw [hco, Submodule.coe_smul, coeff_smul, smul_eq_mul, mul_assoc]
    by_cases hm' : m' ∈ (v : Pol K ι n).support
    · rw [hv m' hm']
    · rw [notMem_support_iff.mp hm']
      simp
  have h2 := hg h v
  rw [h1, map_smul] at h2
  have h3 := congrArg (fun w : VV K lam => coeff m (w : Pol K ι n)) h2
  simp only [hco, Submodule.coe_smul, coeff_smul, smul_eq_mul, mul_assoc] at h3
  have h4 := mul_right_cancel₀ (mem_support_iff.mp hm) (mul_left_cancel₀ (detTwK_ne_zero lam h) h3)
  have h5 : (2 : ℕ) ^ (lam τ0).natW a0 = 2 ^ (∑ s : Fin n, m (τ0, a0, s)) := by
    exact_mod_cast h4
  exact (Nat.pow_right_injective le_rfl h5).symm

end GlobalTheory.CoefTorusWeight
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylTensorCoefSpaceLeSpanPureTensors
section
set_option autoImplicit false
noncomputable section
open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV
open scoped Matrix

namespace GlobalTheory

theorem multilinear_mem_span_of_mem_span {K ι M N : Type} [Field K] [Fintype ι]
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (m : MultilinearMap K (fun _ : ι => M) N) (S : ι → Set M) (f : ι → M)
    (hf : ∀ τ, f τ ∈ Submodule.span K (S τ)) :
    m f ∈ Submodule.span K {P | ∃ g : ι → M, (∀ τ, g τ ∈ S τ) ∧ P = m g} := by
  classical
  have key : ∀ (s : Finset ι) (f : ι → M), (∀ τ, f τ ∈ Submodule.span K (S τ)) →
      (∀ τ, τ ∉ s → f τ ∈ S τ) →
      m f ∈ Submodule.span K {P | ∃ g : ι → M, (∀ τ, g τ ∈ S τ) ∧ P = m g} := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro f _ h
      exact Submodule.subset_span ⟨f, fun τ => h τ (Finset.notMem_empty τ), rfl⟩
    | insert a s ha ih =>
      intro f h1 h2
      have hle : Submodule.span K (S a) ≤
          (Submodule.span K {P | ∃ g : ι → M, (∀ τ, g τ ∈ S τ) ∧ P = m g}).comap
            (m.toLinearMap f a) := by
        rw [Submodule.span_le]
        intro x hx
        rw [SetLike.mem_coe, Submodule.mem_comap, MultilinearMap.toLinearMap_apply]
        apply ih
        · intro τ
          by_cases hτ : τ = a
          · subst hτ
            rw [Function.update_self]
            exact Submodule.subset_span hx
          · rw [Function.update_of_ne hτ]
            exact h1 τ
        · intro τ hτs
          by_cases hτ : τ = a
          · subst hτ
            rw [Function.update_self]
            exact hx
          · rw [Function.update_of_ne hτ]
            exact h2 τ (by simp [hτ, hτs])
      have h := hle (h1 a)
      rw [Submodule.mem_comap, MultilinearMap.toLinearMap_apply, Function.update_eq_self] at h
      exact h
  exact key Finset.univ f hf (fun τ h => absurd (Finset.mem_univ τ) h)

theorem coefSpace_le_span_pure_tensors (K : Type) [Field K] {ι : Type} [Fintype ι] {n : ℕ}
    (lam : ι → DomWeight n) (S : ι → Set (MvPolynomial (Fin n × Fin n) K))
    (hS : ∀ τ, nablaSq K n (lam τ) ≤ Submodule.span K (S τ)) :
    VV K lam ≤ Submodule.span K
      {P | ∃ f : ι → MvPolynomial (Fin n × Fin n) K, (∀ τ, f τ ∈ S τ) ∧ P = ten f} := by
  classical
  let m : MultilinearMap K (fun _ : ι => MvPolynomial (Fin n × Fin n) K)
      (MvPolynomial (ι × Fin n × Fin n) K) :=
    (MultilinearMap.mkPiAlgebra K ι (MvPolynomial (ι × Fin n × Fin n) K)).compLinearMap
      (fun τ => (Formalism.GradedWeylDivisibility.blockEmb K τ).toLinearMap)
  have hm : ∀ f, m f = ten f := fun f => rfl
  unfold VV Formalism.GradedWeylDivisibility.tensorLat
  rw [Submodule.span_le]
  rintro P ⟨F, hF, rfl⟩
  exact multilinear_mem_span_of_mem_span m S F (fun τ => hS τ (hF τ))

end GlobalTheory
end
end

