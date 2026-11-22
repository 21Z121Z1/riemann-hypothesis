import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0245
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0250
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0254
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0006
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0131
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0119
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0176
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0112
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0256
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0163
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0133
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTraceCompatibleTorusEmbeddingStandardTorus
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0255
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0240
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExpMvNegLogMvMul
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

namespace GlobalTheory.ExpLogMv

open PowerSeries

theorem coeff_subst_range {K σ : Type*} [CommRing K] {G : MvPowerSeries σ K}
    (hG : MvPowerSeries.constantCoeff G = 0) (f : PowerSeries K) (α : σ →₀ ℕ) :
    MvPowerSeries.coeff α (f.subst G) =
      ∑ n ∈ Finset.range ((α.sum fun _ k => k) + 1),
        coeff n f * MvPowerSeries.coeff α (G ^ n) := by
  rw [coeff_subst (HasSubst.of_constantCoeff_zero hG),
    finsum_eq_sum_of_support_subset (s := Finset.range ((α.sum fun _ k => k) + 1))]
  · rfl
  · intro k hk
    by_contra h
    apply hk
    have hlt : (α.sum fun _ k => k) < k := by simpa using h
    have h0 : MvPowerSeries.coeff α (G ^ k) = 0 := by
      apply MvPowerSeries.coeff_of_lt_order
      refine lt_of_lt_of_le ?_ (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero k hG)
      exact_mod_cast hlt
    simp [h0]

variable {p : ℕ} [Fact p.Prime] {σ : Type*}

theorem expMv_eq_subst {G : MvPowerSeries σ ℂ_[p]} (hG : MvPowerSeries.constantCoeff G = 0) :
    expMv G = (exp ℂ_[p]).subst G := by
  ext α
  rw [coeff_subst_range hG]
  show expMv G α = _
  rw [expMv]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [div_eq_inv_mul]

theorem logMv_eq_subst {F : MvPowerSeries σ ℂ_[p]} (hF : MvPowerSeries.constantCoeff F = 1) :
    GL3Theta.logMv F = (log ℂ_[p]).subst (F - 1) := by
  have h1 : MvPowerSeries.constantCoeff (F - 1) = 0 := by simp [hF]
  ext α
  rw [coeff_subst_range h1]
  show GL3Theta.logMv F α = _
  rw [GL3Theta.logMv]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [coeff_log]
  split_ifs
  · simp
  · simp
    ring

theorem exp_neg_log_one_var (K : Type*) [Field K] [CharZero K] :
    (exp K).subst (-log K) * (1 + X : PowerSeries K) = 1 := by
  have h0 : constantCoeff (-log K) = 0 := by simp
  have hs := HasSubst.of_constantCoeff_zero' h0
  have e : (1 + X) * d⁄dX K (log K) = 1 := by
    rw [deriv_log]
    ext n
    cases n with
    | zero => simp [add_mul]
    | succ n => simp [add_mul, coeff_succ_X_mul, coeff_one, pow_succ]
  refine derivative.ext ?_ ?_
  · rw [Derivation.leibniz, derivative_subst hs, derivative_exp, map_neg, derivative_one, map_add,
      derivative_one, derivative_X]
    simp only [smul_eq_mul]
    linear_combination (-(exp K).subst (-log K)) * e
  · have : constantCoeff ((exp K).subst (-log K) : PowerSeries K) = 1 := by
      rw [← coeff_zero_eq_constantCoeff_apply, coeff_subst' hs, finsum_eq_single _ 0]
      · simp
      · intro k hk
        simp [hk]
    simp [this]

theorem expMv_neg_logMv_mul : ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (F : MvPowerSeries σ ℂ_[p]), MvPowerSeries.constantCoeff F = 1 → MvPowerSeries.constantCoeff (GL3Theta.logMv F) = 0 ∧ expMv (-GL3Theta.logMv F) * F = 1 := by
  intro p _ σ F hF
  have h1 : MvPowerSeries.constantCoeff (F - 1) = 0 := by simp [hF]
  have hs := HasSubst.of_constantCoeff_zero h1
  have h0 : MvPowerSeries.constantCoeff (GL3Theta.logMv F) = 0 := by
    rw [logMv_eq_subst hF]
    exact constantCoeff_subst_eq_zero h1 _ constantCoeff_log
  refine ⟨h0, ?_⟩
  have hl : HasSubst (-log ℂ_[p]) := HasSubst.of_constantCoeff_zero' (by simp)
  have e := congrArg (substAlgHom (R := ℂ_[p]) hs) (exp_neg_log_one_var ℂ_[p])
  have en : subst (F - 1) (-log ℂ_[p]) = -GL3Theta.logMv F := by
    rw [logMv_eq_subst hF, ← coe_substAlgHom hs, map_neg]
  rw [map_mul, map_add, map_one, substAlgHom_X, coe_substAlgHom, subst_comp_subst_apply hl hs,
    en, add_sub_cancel] at e
  rw [expMv_eq_subst (by rw [map_neg, h0, neg_zero])]
  exact e

end GlobalTheory.ExpLogMv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinsumNormNeg
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

namespace GlobalTheory.NormGauss

theorem exists_norm_eq {k : Type} [Field k] [Finite k] (s : k →+* k) (hs : ∀ a, s (s a) = a)
    (hne : ∃ a, s a ≠ a) (u : k) (hu : s u = u) : ∃ t, t * s t = u := by
  classical
  let F : Subfield k := RingHom.eqLocusField s (RingHom.id k)
  let σ : k ≃ₐ[F] k :=
    { toFun := s, invFun := s, left_inv := hs, right_inv := hs,
      map_mul' := map_mul s, map_add' := map_add s, commutes' := fun r => r.2 }
  have hσ_apply : ∀ x, σ x = s x := fun _ => rfl
  have hσ1 : σ ≠ 1 := by
    obtain ⟨a, ha⟩ := hne
    intro h
    apply ha
    have := AlgEquiv.ext_iff.1 h a
    rwa [hσ_apply, AlgEquiv.one_apply] at this
  have hσ2 : σ ^ 2 = 1 := by
    ext a
    rw [pow_two, AlgEquiv.mul_apply, hσ_apply, hσ_apply, hs, AlgEquiv.one_apply]
  have hfix : IntermediateField.fixedField (Subgroup.zpowers σ) = ⊥ := by
    ext x
    rw [IntermediateField.mem_fixedField_iff, IntermediateField.mem_bot]
    constructor
    · intro h
      exact ⟨⟨x, h σ (Subgroup.mem_zpowers σ)⟩, rfl⟩
    · rintro ⟨r, rfl⟩ τ _
      exact τ.commutes r
  have htop : Subgroup.zpowers σ = ⊤ := by
    rw [← IntermediateField.fixingSubgroup_fixedField (Subgroup.zpowers σ), hfix]
    ext τ
    simp only [Subgroup.mem_top, iff_true]
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    obtain ⟨r, rfl⟩ := IntermediateField.mem_bot.1 hx
    exact τ.commutes r
  have hcard : Fintype.card (k ≃ₐ[F] k) = 2 := by
    rw [← Nat.card_eq_fintype_card, ← Subgroup.card_top, ← htop, Nat.card_zpowers,
      orderOf_eq_prime hσ2 hσ1]
  have huniv : (Finset.univ : Finset (k ≃ₐ[F] k)) = {1, σ} := by
    symm
    apply Finset.eq_univ_of_card
    rw [Finset.card_pair hσ1.symm, hcard]
  have hnorm : ∀ t : k, algebraMap F k (Algebra.norm F t) = t * s t := by
    intro t
    rw [Algebra.norm_eq_prod_automorphisms, huniv, Finset.prod_pair hσ1.symm]
    rfl
  obtain ⟨t, ht⟩ := FiniteField.norm_surjective F k (⟨u, hu⟩ : F)
  refine ⟨t, ?_⟩
  rw [← hnorm, ht]
  rfl

theorem sum_norm_neg {k : Type} [Field k] [Fintype k] (s : k →+* k) (hs : ∀ a, s (s a) = a)
    (hne : ∃ a, s a ≠ a) (ψ : AddChar k ℂ) (hψ : ∃ a, ψ (a + s a) ≠ 1) :
    ∃ m : ℝ, 0 < m ∧ ∑ t : k, ψ (t * s t) = -(m : ℂ) := by
  classical
  let F : Subfield k := RingHom.eqLocusField s (RingHom.id k)
  have hs0 : ∀ x : k, s x = 0 → x = 0 := by
    intro x h
    have := congrArg s h
    rwa [hs, map_zero] at this
  have hNF : ∀ t : k, t * s t ∈ F := fun t => by
    show s (t * s t) = t * s t
    rw [map_mul, hs, mul_comm]
  let N : k → F := fun t => ⟨t * s t, hNF t⟩
  have hN : ∀ t, ((N t : F) : k) = t * s t := fun _ => rfl
  let φ : AddChar F ℂ := ψ.compAddMonoidHom F.subtype.toAddMonoidHom
  have hφ_apply : ∀ u : F, φ u = ψ (u : k) := fun _ => rfl
  have hφ : φ ≠ 1 := by
    obtain ⟨a, ha⟩ := hψ
    intro h
    have hmem : a + s a ∈ F := by
      show s (a + s a) = a + s a
      rw [map_add, hs, add_comm]
    apply ha
    have := congrArg (fun χ : AddChar F ℂ => χ ⟨a + s a, hmem⟩) h
    simpa only [hφ_apply, AddChar.one_apply] using this
  have hsumφ : ∑ u : F, ψ (u : k) = 0 := by
    simpa only [hφ_apply] using AddChar.sum_eq_zero_of_ne_one hφ
  obtain ⟨c, hc⟩ : ∃ c : ℕ, c = (Finset.univ.filter (fun t : k => t * s t = 1)).card := ⟨_, rfl⟩
  have hfib : ∀ u : F,
      (Finset.univ.filter (fun t : k => N t = u)).card = if u = 0 then 1 else c := by
    intro u
    split_ifs with hu
    · subst hu
      rw [Finset.card_eq_one]
      refine ⟨0, ?_⟩
      ext t
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro h
        have h' : t * s t = 0 := congrArg Subtype.val h
        rcases mul_eq_zero.1 h' with h0 | h0
        · exact h0
        · exact hs0 t h0
      · rintro rfl
        apply Subtype.ext
        rw [hN, zero_mul]
        rfl
    · obtain ⟨t0, ht0⟩ := exists_norm_eq s hs hne (u : k) u.2
      have hu0 : (u : k) ≠ 0 := fun h => hu (Subtype.ext h)
      have ht0ne : t0 ≠ 0 := by
        rintro rfl
        apply hu0
        rw [← ht0, zero_mul]
      rw [hc]
      apply Finset.card_nbij' (fun t => t * t0⁻¹) (fun t => t * t0)
      · intro t ht
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ht ⊢
        have h' : t * s t = u := congrArg Subtype.val ht
        have e : t * t0⁻¹ * s (t * t0⁻¹) = (t * s t) * (t0 * s t0)⁻¹ := by
          rw [map_mul, map_inv₀, mul_inv]
          ring
        rw [e, h', ht0, mul_inv_cancel₀ hu0]
      · intro t ht
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ht ⊢
        apply Subtype.ext
        rw [hN]
        have e : t * t0 * s (t * t0) = (t * s t) * (t0 * s t0) := by
          rw [map_mul]
          ring
        rw [e, ht, ht0, one_mul]
      · intro t _
        exact inv_mul_cancel_right₀ ht0ne t
      · intro t _
        exact mul_inv_cancel_right₀ ht0ne t
  have hsplit : ∑ t : k, ψ (t * s t) =
      ∑ u : F, ((Finset.univ.filter (fun t : k => N t = u)).card : ℂ) * ψ (u : k) := by
    rw [← Finset.sum_fiberwise Finset.univ N (fun t => ψ (t * s t))]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [Finset.sum_congr rfl (g := fun _ => ψ (u : k)), Finset.sum_const, nsmul_eq_mul]
    intro t ht
    have := (Finset.mem_filter.1 ht).2
    rw [← this]
  have hψ0 : ψ ((0 : F) : k) = 1 := by
    rw [ZeroMemClass.coe_zero, AddChar.map_zero_eq_one]
  have key : ∀ u : F, (((if u = 0 then 1 else c : ℕ)) : ℂ) * ψ (u : k) =
      (c : ℂ) * ψ (u : k) + (if u = 0 then (1 - (c : ℂ)) else 0) := by
    intro u
    split_ifs with h
    · subst h
      rw [hψ0]
      push_cast
      ring
    · ring
  have hval : ∑ u : F, (((if u = 0 then 1 else c : ℕ)) : ℂ) * ψ (u : k) = 1 - c := by
    rw [Finset.sum_congr rfl (fun u _ => key u), Finset.sum_add_distrib, ← Finset.mul_sum, hsumφ,
      mul_zero, zero_add]
    simp
  have hc2 : 2 ≤ c := by
    obtain ⟨a, ha⟩ := hne
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact ha (map_zero s)
    have hsa0 : s a ≠ 0 := fun h => ha0 (hs0 a h)
    have hne1 : a * (s a)⁻¹ ≠ 1 := by
      intro h
      apply ha
      rw [mul_inv_eq_one₀ hsa0] at h
      exact h.symm
    rw [hc]
    calc 2 = ({1, a * (s a)⁻¹} : Finset k).card := (Finset.card_pair hne1.symm).symm
      _ ≤ _ := by
        apply Finset.card_le_card
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rcases hx with rfl | rfl
        · rw [map_one, one_mul]
        · rw [map_mul, map_inv₀, hs]
          field_simp
  refine ⟨(c : ℝ) - 1, ?_, ?_⟩
  · have : (2 : ℝ) ≤ c := by exact_mod_cast hc2
    linarith
  · rw [hsplit]
    simp_rw [hfib]
    rw [hval]
    push_cast
    ring

theorem finsum_norm_neg : ∀ (R : Type) [CommRing R] (σ : R →+* R) (P : Ideal R) [P.IsMaximal] [Finite (R ⧸ P)], (∀ a, σ (σ a) = a) → (∀ a ∈ P, σ a ∈ P) → (∃ a, a - σ a ∉ P) → ∀ χ : R → ℂ, (∀ a b, χ (a + b) = χ a * χ b) → (∀ a ∈ P, χ a = 1) → (∃ a, χ (a + σ a) ≠ 1) → ∃ m : ℝ, 0 < m ∧ ∑ᶠ q : R ⧸ P, χ (Quotient.out q * σ (Quotient.out q)) = -(m : ℂ) := by
  intro R _ σ P _ _ hσ hP hne χ hχ hχP hχa
  classical
  let _ : Field (R ⧸ P) := Ideal.Quotient.field P
  let _ : Fintype (R ⧸ P) := Fintype.ofFinite _
  have hle : P ≤ P.comap σ := fun a ha => hP a ha
  let s : R ⧸ P →+* R ⧸ P := Ideal.quotientMap P σ hle
  have hs_mk : ∀ a : R, s (Ideal.Quotient.mk P a) = Ideal.Quotient.mk P (σ a) :=
    fun a => Ideal.quotientMap_mk
  have hs : ∀ x, s (s x) = x := by
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [hs_mk, hs_mk, hσ]
  have hsne : ∃ x, s x ≠ x := by
    obtain ⟨a, ha⟩ := hne
    refine ⟨Ideal.Quotient.mk P a, ?_⟩
    rw [hs_mk]
    intro h
    apply ha
    have h' := P.neg_mem (Ideal.Quotient.eq.1 h)
    rwa [neg_sub] at h'
  have hχ_congr : ∀ x y : R, x - y ∈ P → χ x = χ y := by
    intro x y h
    have e : x = y + (x - y) := by ring
    conv_lhs => rw [e]
    rw [hχ, hχP _ h, mul_one]
  let ψ : AddChar (R ⧸ P) ℂ :=
    { toFun := fun q => χ (Quotient.out q)
      map_zero_eq_one' := by
        apply hχP
        rw [← Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.mk_out]
      map_add_eq_mul' := by
        intro q₁ q₂
        rw [← hχ]
        apply hχ_congr
        rw [← Ideal.Quotient.eq, map_add, Ideal.Quotient.mk_out, Ideal.Quotient.mk_out,
          Ideal.Quotient.mk_out] }
  have hψ_mk : ∀ a, ψ (Ideal.Quotient.mk P a) = χ a := fun a =>
    hχ_congr _ _ (by rw [← Ideal.Quotient.eq, Ideal.Quotient.mk_out])
  have hψne : ∃ x, ψ (x + s x) ≠ 1 := by
    obtain ⟨a, ha⟩ := hχa
    exact ⟨Ideal.Quotient.mk P a, by rw [hs_mk, ← map_add, hψ_mk]; exact ha⟩
  obtain ⟨m, hm, hsum⟩ := sum_norm_neg s hs hsne ψ hψne
  refine ⟨m, hm, ?_⟩
  rw [finsum_eq_sum_of_fintype, ← hsum]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  conv_rhs => rw [← Ideal.Quotient.mk_out q]
  rw [hs_mk, ← map_mul, hψ_mk]

end GlobalTheory.NormGauss
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisSlTwoActionModularFunctionRingOfCongr
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem gal_sl_io_of_cong :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (a : GlobalTheory.FN.ring ε.range) (N w : ℕ), 0 < N → Lv ε.range N w a → ∀ (s : Ω ≃ₐ[ℚ] Ω) (d : ℤ), s (eOm ε (1 / N)) = eOm ε (1 / N) ^ d → ∀ γ γ' : SL(2, ℤ), Cong N d γ γ' → T.gal s (T.sl (ofSL γ) (T.io a)) = T.sl (ofSL γ') (T.gal s (T.io a)) := by
  intro Ω _ _ _ ε T a N w hN hLv s d hs γ γ' hC
  haveI : NeZero N := ⟨hN.ne'⟩
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_complex_ringEquiv_extending_subfield_aut Ω ε s.toRingEquiv
  have hg' : ∀ x, g (ε x) = ε (s x) := hg
  obtain ⟨u, hu, hZ⟩ := (GlobalTheory.T.galois_exponent_rootOfUnity_expTwoPiI Ω ε s N hN).2 d hs
  have hE : ∀ x ∈ ε.range, g x ∈ ε.range := by
    rintro _ ⟨y, rfl⟩
    exact ⟨s y, (hg' y).symm⟩
  obtain ⟨f', hf'L, hf'C⟩ := GlobalTheory.T.levelN_function_galois_conj_qExpansion g ε.range N u w (a : ℍ → ℂ) hE (hZ g hg') hLv
  let a' : GlobalTheory.FN.ring ε.range := ⟨f', mem_ring_of_inR ⟨N, w, hN, hf'L⟩⟩
  obtain ⟨hext, hcmp, hexpinj, -⟩ := GlobalTheory.T.fractionField_ext_closure_injective Ω ε T
  obtain ⟨-, -, hSL, -⟩ := GlobalTheory.T.cmp_mul_ofSL_and_up_cmp_eq_up_mob

  have key : ∀ γ γ' : SL(2, ℤ), dg u * redGL N γ' = redGL N γ * dg u →
      T.gal s (T.sl (ofSL γ) (T.io a)) = T.sl (ofSL γ') (T.io a') := by
    intro γ γ' hM
    obtain ⟨b, hb, hbio⟩ := hcmp (ofSL γ) a
    obtain ⟨b', hb', hb'io⟩ := hcmp (ofSL γ') a'
    rw [hbio, hb'io]
    apply hexpinj
    ext r
    rw [T.gal_exp]
    have hb1 : (b : ℍ → ℂ) = fun τ => (a : ℍ → ℂ) (γ • τ) := by rw [hb, hSL]
    have hb2 : (b' : ℍ → ℂ) = fun τ => f' (γ' • τ) := by rw [hb', hSL]
    refine Eq.symm ?_
    refine GlobalTheory.T.cuspExpansion_coeff_conj_of_qExpansion_conj Ω ε s.toRingEquiv.toRingHom g N w b b' _ _ hg' hN ?_ ?_ (T.exp_io b) (T.exp_io b') r
    · rw [hb1]; exact hLv.2 γ
    · rw [hb1, hb2]; exact hf'C γ γ' hM
  have h1 : T.gal s (T.io a) = T.io a' := by
    have hM1 : dg u * redGL N 1 = redGL N 1 * dg u := by simp [redGL]
    have := key 1 1 hM1
    obtain ⟨c, hc, hcio⟩ := hcmp (ofSL 1) a
    obtain ⟨c', hc', hc'io⟩ := hcmp (ofSL 1) a'
    have e1 : c = a := Subtype.ext (by rw [hc, hSL]; funext τ; simp)
    have e2 : c' = a' := Subtype.ext (by rw [hc', hSL]; funext τ; simp [a'])
    rw [hcio, hc'io, e1, e2] at this
    exact this
  rw [h1]
  exact key γ γ' ((GlobalTheory.T.slTwoDiagConjCongruence_iff_diagOneUnit_matrix_eq N d u hu γ γ').mp hC)

end GlobalTheory.FN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSumTaylorCoordinateSpaceEntire
section
namespace GlobalTheory.EntireTaylor

theorem summable_of_entire {σ : Type*} [Fintype σ] [DecidableEq σ] {f : (σ → ℂ) → ℂ}
    (hf : Differentiable ℂ f) (c : (σ →₀ ℕ) → ℂ)
    (hc : ∀ α, (∏ j, ((α j).factorial : ℂ)) * c α = pderivIter α f 0) (w : σ → ℂ) :
    Summable fun α : σ →₀ ℕ => c α * ∏ j, w j ^ α j := by
  obtain ⟨R, hRdef⟩ : ∃ R : σ → ℝ, R = fun j => 2 * ‖w j‖ + 1 := ⟨_, rfl⟩
  have hR : ∀ j, 0 < R j := fun j => by rw [hRdef]; positivity
  obtain ⟨M, hM⟩ : ∃ M, ∀ z ∈ Set.univ.pi (fun j => Metric.closedBall (0 : ℂ) (R j)), ‖f z‖ ≤ M :=
    (isCompact_univ_pi fun j => isCompact_closedBall (0 : ℂ) (R j)).exists_bound_of_continuousOn
      hf.continuous.continuousOn
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _)
    (hM 0 (Set.mem_univ_pi.mpr fun j => Metric.mem_closedBall.mpr (by simpa using (hR j).le)))
  have hw : ∀ j, ‖w j‖ / R j ≤ 1 / 2 := fun j => by
    rw [div_le_iff₀ (hR j), hRdef]
    linarith [norm_nonneg (w j)]
  have key : ∀ α : σ →₀ ℕ, ‖c α * ∏ j, w j ^ α j‖ ≤ M * ∏ j, (1 / 2 : ℝ) ^ α j := by
    intro α
    have hP : (∏ j, ((α j).factorial : ℂ)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun j _ => by exact_mod_cast Nat.factorial_ne_zero _
    have hcα : c α = pderivIter α f 0 / ∏ j, ((α j).factorial : ℂ) := by
      rw [← hc α, mul_div_cancel_left₀ _ hP]
    have hnormP : ‖∏ j, ((α j).factorial : ℂ)‖ = ∏ j, ((α j).factorial : ℝ) := by
      rw [norm_prod]
      simp
    have hPpos : 0 < ∏ j, ((α j).factorial : ℝ) :=
      Finset.prod_pos fun j _ => by exact_mod_cast Nat.factorial_pos _
    have hC : ‖pderivIter α f 0‖ ≤ (∏ k, ((α k).factorial : ℝ)) * M / ∏ k, R k ^ α k :=
      GlobalTheory.norm_pderivIter_le_of_differentiable α (fun k => (hR k).le) (fun k _ => hR k) hf
        fun z hz => hM z (Set.mem_univ_pi.mpr fun j => Metric.mem_closedBall.mpr (by
          have h := hz j
          simp only [Pi.zero_apply, sub_zero] at h
          rw [dist_zero_right]
          exact h.le))
    have h1 : ‖c α‖ ≤ M / ∏ j, R j ^ α j := by
      rw [hcα, norm_div, hnormP, div_le_iff₀ hPpos]
      calc ‖pderivIter α f 0‖ ≤ (∏ k, ((α k).factorial : ℝ)) * M / ∏ k, R k ^ α k := hC
        _ = (M / ∏ j, R j ^ α j) * ∏ j, ((α j).factorial : ℝ) := by ring
    calc ‖c α * ∏ j, w j ^ α j‖ = ‖c α‖ * ∏ j, ‖w j‖ ^ α j := by
          rw [norm_mul, norm_prod]
          simp [norm_pow]
      _ ≤ (M / ∏ j, R j ^ α j) * ∏ j, ‖w j‖ ^ α j :=
          mul_le_mul_of_nonneg_right h1 (Finset.prod_nonneg fun j _ => by positivity)
      _ = M * ∏ j, (‖w j‖ / R j) ^ α j := by
          simp only [div_pow, Finset.prod_div_distrib]
          ring
      _ ≤ M * ∏ j, (1 / 2 : ℝ) ^ α j :=
          mul_le_mul_of_nonneg_left
            (Finset.prod_le_prod (fun j _ => by have := (hR j).le; positivity)
              fun j _ => pow_le_pow_left₀ (by have := (hR j).le; positivity) (hw j) _) hM0
  exact Summable.of_norm_bounded
    ((GlobalTheory.ProdThetaConj.summable_prod_half_pow (σ := σ)).mul_left M) key

end GlobalTheory.EntireTaylor

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators

theorem GlobalTheory.EntireTaylor.hasSum_taylor_mono : ∀ (D : D7) (N N' : ℕ) (F : VC D N N' → ℂ), Differentiable ℂ F → ∀ z : VC D N N', HasSum (fun α : Mono D N N' => Formalism.MainNotions.TaylorLogMetric.taylor D F α * mono D α z) (F z) := by
  intro D N N' F hF z
  have hcd : Differentiable ℂ (fun w => F (GlobalTheory.GaussCauchy.curry D N N' w)) := fun w =>
    (hF _).comp w (LinearMap.toContinuousLinearMap (GlobalTheory.GaussCauchy.curry D N N')).differentiableAt
  have hS := GlobalTheory.EntireTaylor.summable_of_entire hcd (fun α => Formalism.MainNotions.TaylorLogMetric.taylor D F α)
    (fun α => by
      rw [← GlobalTheory.GaussCauchy.factorial_mul_taylor D N N' F hF α, Finsupp.prod_fintype]
      intro i
      simp)
    (fun k => z k.1 k.2.1 k.2.2)
  have hmono : ∀ α : Mono D N N', mono D α z = ∏ k, z k.1 k.2.1 k.2.2 ^ α k := fun α => by
    show (α.prod fun k n => z k.1 k.2.1 k.2.2 ^ n) = _
    rw [Finsupp.prod_fintype]
    intro i
    simp
  have hS' : Summable fun α : Mono D N N' => Formalism.MainNotions.TaylorLogMetric.taylor D F α * mono D α z := by
    simpa only [hmono] using hS
  rw [← GlobalTheory.ProdThetaConj.tsum_taylor_mono D hF z]
  exact hS'.hasSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralCexpGaussianPlaneStatement
section
open Complex MeasureTheory GlobalTheory.UnitaryTheta
open scoped BigOperators ComplexConjugate Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_cexp_complex_gaussian_linear : ∀ l u v : ℂ, 0 < l.re → Integrable (fun z : ℂ => cexp (-(π : ℂ) * l * (z * conj z) + π * (u * conj z) + π * (z * conj v))) ∧ ∫ z : ℂ, cexp (-(π : ℂ) * l * (z * conj z) + π * (u * conj z) + π * (z * conj v)) = l⁻¹ * cexp (π * (u * conj v) / l) := by
  first | exact @GlobalTheory.UnitaryTheta.integral_cexp_gaussian_plane | exact GlobalTheory.UnitaryTheta.integral_cexp_gaussian_plane | (intros; apply GlobalTheory.UnitaryTheta.integral_cexp_gaussian_plane <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralUnfoldFundamentalDomainStatement
section
open Complex MeasureTheory GlobalTheory.UnitaryTheta
open scoped BigOperators ComplexConjugate Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.setIntegral_tsum_translate_eq_integral : ∀ (V : Type) [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] (μ : Measure V) [μ.IsAddLeftInvariant] (Λ : AddSubgroup V) [Countable Λ] (Fd : Set V), IsAddFundamentalDomain Λ Fd μ → ∀ g : V → ℂ, Integrable g μ → IntegrableOn (fun z => ∑' y : Λ, g (z + y)) Fd μ ∧ ∫ z in Fd, ∑' y : Λ, g (z + y) ∂μ = ∫ z, g z ∂μ := by
  first | exact @GlobalTheory.integral_unfold_fundamentalDomain | exact GlobalTheory.integral_unfold_fundamentalDomain | (intros; apply GlobalTheory.integral_unfold_fundamentalDomain <;> assumption)
end

