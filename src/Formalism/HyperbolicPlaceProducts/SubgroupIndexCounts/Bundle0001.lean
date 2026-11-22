import Formalism.HyperbolicPlaceProducts.Bundle0001

-- bundled from Formalism.HyperbolicPlaceProducts.SubgroupIndexCounts.ArithmeticLatticeHypothesis
section
namespace Formalism.SLP.GlobalBoundRefinements.P
open Formalism.SLP.GlobalBoundRefinements

theorem matrix_entries_integral (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.conjTranspose * J * M = J) :
    ‖M 0 0‖ ^ 2 - ‖M 1 0‖ ^ 2 = 1 ∧ ‖M 0 1‖ ^ 2 - ‖M 1 1‖ ^ 2 = -1 ∧
      ‖M 0 0‖ * ‖M 0 1‖ = ‖M 1 0‖ * ‖M 1 1‖ := by
  have e00 := congrFun (congrFun hM 0) 0
  have e11 := congrFun (congrFun hM 1) 1
  have e01 := congrFun (congrFun hM 0) 1
  simp [J, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply] at e00 e11 e01
  rw [Complex.conj_mul', Complex.conj_mul'] at e00 e11
  refine ⟨?_, ?_, ?_⟩
  · exact_mod_cast e00
  · exact_mod_cast e11
  · have h : (starRingEnd ℂ) (M 0 0) * M 0 1 = (starRingEnd ℂ) (M 1 0) * M 1 1 := by
      linear_combination e01
    have := congrArg norm h
    simpa [norm_mul] using this

theorem unipotent_upper_entries : EntriesOfSignaturePreserving := by
  intro M hM
  obtain ⟨h1, h2, h3⟩ := matrix_entries_integral M hM
  have hsq : ‖M 0 0‖ ^ 2 * ‖M 0 1‖ ^ 2 = ‖M 1 0‖ ^ 2 * ‖M 1 1‖ ^ 2 := by
    rw [← mul_pow, ← mul_pow, h3]
  have hbc : ‖M 0 1‖ ^ 2 = ‖M 1 0‖ ^ 2 := by nlinarith
  have had : ‖M 0 0‖ ^ 2 = ‖M 1 1‖ ^ 2 := by linarith
  have hbc' : ‖M 0 1‖ = ‖M 1 0‖ := (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hbc
  have had' : ‖M 0 0‖ = ‖M 1 1‖ := (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 had
  refine ⟨had', hbc', h1, ?_⟩
  intro sh ch hsh hch hchsh hc
  have hsh0 : sh ≠ 0 := hsh.ne'
  have key : ‖M 0 0‖ ^ 2 = (ch / sh) ^ 2 := by
    have : ‖M 0 0‖ ^ 2 = 1 + (1 / sh) ^ 2 := by rw [← hc]; linarith
    rw [this, div_pow, div_pow, hchsh]
    field_simp
  exact (pow_left_inj₀ (norm_nonneg _) (div_nonneg hch hsh.le) two_ne_zero).1 key

theorem arithmetic_lattice_hypothesis : AlHyp := by
  intro M sh ch u u' hM hsh hch hchsh hc hu
  obtain ⟨_, hbc, _, hA⟩ := unipotent_upper_entries M hM
  have ha := hA sh ch hsh hch hchsh hc
  have hb : ‖M 0 1‖ = 1 / sh := hbc.trans hc
  calc ‖M 0 0 * u + M 0 1 * u'‖ ≤ ‖M 0 0 * u‖ + ‖M 0 1 * u'‖ := norm_add_le _ _
    _ = ch / sh * ‖u‖ + 1 / sh * ‖u‖ := by rw [norm_mul, norm_mul, ha, hb, hu]
    _ = ‖u‖ * (1 + ch) / sh := by ring

end Formalism.SLP.GlobalBoundRefinements.P
end

-- bundled from Formalism.HyperbolicPlaceProducts.SubgroupIndexCounts.CardEqCardRangeNsmulMulCardKer
section
open Module

namespace Formalism.SLP.P

theorem card_eq_card_range_nsmul_mul_card_ker : Formalism.SLP.TorsionIndexEq := by
  intro A _ _ g
  set f : A →+ A := nsmulAddMonoidHom g
  rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.ker,
    Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv]

theorem card_range_nsmul_mul_card_le : Formalism.SLP.TorsionIndex := by
  intro A _ _ g K hK
  have hle : K ≤ (nsmulAddMonoidHom g : A →+ A).ker := fun x hx => by
    simpa using hK x hx
  rw [card_eq_card_range_nsmul_mul_card_ker A g]
  exact Nat.mul_le_mul_left _ (AddSubgroup.card_le_of_le hle)

end Formalism.SLP.P
end

-- bundled from Formalism.HyperbolicPlaceProducts.SubgroupIndexCounts.DedekindLFunctions
section
open Module

noncomputable section

namespace Formalism.SLP.P

private theorem exists_span_singleton_eq_of_le_span_singleton {R M : Type} [CommRing R] [IsDedekindDomain R]
    [AddCommGroup M] [Module R M] [Finite M] (v : M) (N : Submodule R M)
    (hN : N ≤ R ∙ v) : ∃ t : M, (R ∙ t) = N := by
  let f : R →ₗ[R] M := LinearMap.toSpanSingleton R M v
  let I : Ideal R := N.comap f
  let J : Ideal R := LinearMap.ker f
  have hJI : J ≤ I := fun r hr => by
    show f r ∈ N
    rw [LinearMap.mem_ker.1 hr]
    exact N.zero_mem
  have key : ∃ x, J ⊔ Ideal.span {x} = I := by
    by_cases hJ : J = ⊥
    ·
      have hinj : Function.Injective f := LinearMap.ker_eq_bot.1 hJ
      haveI : Finite R := Finite.of_injective f hinj
      have hF : IsField R := Finite.isField_of_domain R
      by_cases hI : I = ⊥
      · exact ⟨0, by rw [hJ, hI]; simp⟩
      · obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
        obtain ⟨b, hb⟩ := hF.mul_inv_cancel ha0
        have hIt : I = ⊤ := (Ideal.eq_top_iff_one I).2 (by rw [← hb]; exact I.mul_mem_right b ha)
        exact ⟨1, by rw [hIt, Ideal.span_singleton_one, sup_top_eq]⟩
    · exact IsDedekindDomain.exists_sup_span_eq hJI hJ
  obtain ⟨x, hx⟩ := key
  refine ⟨x • v, le_antisymm ?_ ?_⟩
  · rw [Submodule.span_singleton_le_iff_mem]
    have hxI : x ∈ I := hx ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self x)
    have hfx : f x ∈ N := hxI
    simpa [f] using hfx
  · intro n hn
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 (hN hn)
    have hr : r ∈ I := by
      show f r ∈ N
      simpa [f] using hn
    rw [← hx, Submodule.mem_sup] at hr
    obtain ⟨j, hj, y, hy, rfl⟩ := hr
    obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.1 hy
    have hjv : j • v = 0 := by simpa [f] using LinearMap.mem_ker.1 hj
    rw [Submodule.mem_span_singleton]
    exact ⟨s, by rw [add_smul, hjv, zero_add, mul_smul]⟩

theorem exists_family_span_eq_of_le {R M : Type} [CommRing R] [IsDedekindDomain R]
    [AddCommGroup M] [Module R M] [Finite M] :
    ∀ (e : ℕ) (v : Fin e → M) (N : Submodule R M), N ≤ Submodule.span R (Set.range v) →
      ∃ t : Fin e → M, Submodule.span R (Set.range t) = N := by
  intro e
  induction e with
  | zero =>
    intro v N hN
    refine ⟨v, ?_⟩
    rw [Set.range_eq_empty v, Submodule.span_empty] at hN ⊢
    exact (le_bot_iff.1 hN).symm
  | succ e ih =>
    intro v N hN
    set S' : Submodule R M := Submodule.span R (Set.range (Fin.tail v)) with hS'
    have hv : Submodule.span R (Set.range v) = (R ∙ v 0) ⊔ S' := by
      conv_lhs => rw [← Fin.cons_self_tail v]
      rw [Fin.range_cons, Submodule.span_insert]
    haveI : Finite (M ⧸ S') := Finite.of_surjective _ (Submodule.mkQ_surjective S')

    have hπ : N.map S'.mkQ ≤ R ∙ S'.mkQ (v 0) := by
      rw [Submodule.map_le_iff_le_comap]
      intro n hn
      have h := hN hn
      rw [hv, Submodule.mem_sup] at h
      obtain ⟨a, ha, b, hb, rfl⟩ := h
      obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 ha
      rw [Submodule.mem_comap, map_add, map_smul]
      have hb0 : S'.mkQ b = 0 := (Submodule.Quotient.mk_eq_zero S').2 hb
      rw [hb0, add_zero]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    obtain ⟨t', ht'⟩ := exists_span_singleton_eq_of_le_span_singleton (S'.mkQ (v 0)) (N.map S'.mkQ) hπ
    have ht'm : t' ∈ N.map S'.mkQ := ht' ▸ Submodule.mem_span_singleton_self t'
    obtain ⟨n0, hn0, hn0t⟩ := ht'm
    obtain ⟨u, hu⟩ := ih (Fin.tail v) (N ⊓ S') inf_le_right
    refine ⟨Fin.cons n0 u, ?_⟩
    rw [Fin.range_cons, Submodule.span_insert, hu]
    apply le_antisymm
    · exact sup_le ((Submodule.span_singleton_le_iff_mem _ _).2 hn0) inf_le_left
    · intro n hn
      have hπn : S'.mkQ n ∈ R ∙ S'.mkQ n0 := by
        rw [hn0t, ht']
        exact Submodule.mem_map_of_mem hn
      obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 hπn
      have hd : n - r • n0 ∈ S' := by
        have h0 : S'.mkQ (n - r • n0) = 0 := by rw [map_sub, map_smul, hr, sub_self]
        exact (Submodule.Quotient.mk_eq_zero S').1 h0
      rw [Submodule.mem_sup]
      exact ⟨r • n0, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), n - r • n0,
        ⟨N.sub_mem hn (N.smul_mem _ hn0), hd⟩, by abel⟩

theorem card_submodules_le_of_dedekind : Formalism.SLP.SubmoduleCountDed := by
  intro R M _ _ _ _ _ e v hv
  have hsurj : Function.Surjective
      (fun t : Fin e → M => Submodule.span R (Set.range t)) := by
    intro N
    exact exists_family_span_eq_of_le e v N (by rw [hv]; exact le_top)
  calc Nat.card (Submodule R M) ≤ Nat.card (Fin e → M) :=
        Nat.card_le_card_of_surjective _ hsurj
    _ = Nat.card M ^ e := by
        rw [Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end Formalism.SLP.P

end
end

-- bundled from Formalism.HyperbolicPlaceProducts.SubgroupIndexCounts.DetIndexProductHyperbolicInequality
section
open Module

noncomputable section

namespace Formalism.SLP.GlobalBoundRefinements.P

open Formalism.SLP.GlobalBoundRefinements

theorem polarization_of_orthogonal_splittings : Formalism.SLP.GlobalBoundRefinements.Polarise := by
  intro V _ _ h hsym y A y' A' hw hyA hyA'
  have hAy : h A y = 0 := by rw [hsym y A, hyA, map_zero]
  have hAy' : h A' y' = 0 := by rw [hsym y' A', hyA', map_zero]
  have e1 : h (y - A) (y - A) = h y y + h A A := by
    simp only [map_sub, LinearMap.sub_apply, hyA, hAy]
    ring
  have e2 : h (y' + A') (y' + A') = h y' y' + h A' A' := by
    simp only [map_add, LinearMap.add_apply, hyA', hAy']
    ring
  rw [← e1, ← e2, hw]

theorem card_linearEquiv_le : Formalism.SLP.GlobalBoundRefinements.AutCount := by
  intro R M _ _ _ _ e v hv
  have hinj : Function.Injective (fun f : M ≃ₗ[R] M => fun i => f (v i)) := by
    intro f g hfg
    apply LinearEquiv.toLinearMap_injective
    exact LinearMap.ext_on_range hv (fun i => congrFun hfg i)
  calc Nat.card (M ≃ₗ[R] M) ≤ Nat.card (Fin e → M) := Nat.card_le_card_of_injective _ hinj
    _ = Nat.card M ^ e := by rw [Nat.card_fun, Nat.card_fin]

set_option maxHeartbeats 800000 in
theorem coefficients_of_form_preserving : Formalism.SLP.GlobalBoundRefinements.FormCoeff := by
  intro a b c d T T' hT hT' hform
  have h10 := hform 1 0
  have h01 := hform 0 1
  simp only [mul_one, mul_zero, add_zero, zero_add, norm_one, norm_zero, one_pow] at h10 h01
  norm_num at h10 h01
  have e1 : ‖a‖ ^ 2 - 1 = T' * ‖c‖ ^ 2 / T := by
    field_simp
    linarith
  have e2 : ‖d‖ ^ 2 - 1 = T * ‖b‖ ^ 2 / T' := by
    field_simp
    linarith
  refine ⟨e1, e2, fun ha => ?_⟩
  have hc2 : ‖c‖ ^ 2 = 0 := by
    rw [ha] at h10
    nlinarith [sq_nonneg ‖c‖]
  have hc : c = 0 := by simpa using hc2
  have haa : a * (starRingEnd ℂ a) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, ha]
    norm_num
  have hx := hform (starRingEnd ℂ a * b) 1
  have h2b : a * (starRingEnd ℂ a * b) + b * 1 = 2 * b := by
    rw [← mul_assoc, haa]
    ring
  rw [h2b, hc] at hx
  simp only [zero_mul, zero_add, mul_one, norm_mul, Complex.norm_conj, ha, one_mul, norm_one,
    one_pow] at hx
  norm_num at hx
  have hb2 : ‖b‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖b‖]
  have hb : b = 0 := by simpa using hb2
  refine ⟨hc, hb, ?_⟩
  rw [hb, norm_zero] at e2
  have hd2 : ‖d‖ ^ 2 = 1 := by linarith [e2, show T * (0:ℝ) ^ 2 / T' = 0 by simp]
  nlinarith [norm_nonneg d]

theorem prod_places_hyperbolic_inequality : Formalism.SLP.GlobalBoundRefinements.ProdPlacesHyperbolicInequality := by
  intro ι _ T al n ch sh Nr hT hal hsh hch hbd hNr h1
  have hsq : ∀ v, T v * al v ^ 2 ≤ (n v * (1 + ch v) / sh v) ^ 2 := by
    intro v
    have h0 : 0 ≤ Real.sqrt (T v) * al v := mul_nonneg (Real.sqrt_nonneg _) (hal v)
    have h2 := pow_le_pow_left₀ h0 (hbd v) 2
    rwa [mul_pow, Real.sq_sqrt (hT v).le] at h2
  have hprod : (∏ v, T v) * ∏ v, al v ^ 2 ≤ (∏ v, n v ^ 2) * ∏ v, ((1 + ch v) / sh v) ^ 2 := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod
    · intro v _
      exact mul_nonneg (hT v).le (sq_nonneg _)
    · intro v _
      calc T v * al v ^ 2 ≤ (n v * (1 + ch v) / sh v) ^ 2 := hsq v
        _ = n v ^ 2 * ((1 + ch v) / sh v) ^ 2 := by ring
  have hTpos : 0 ≤ ∏ v, T v := Finset.prod_nonneg fun v _ => (hT v).le
  calc (∏ v, T v) / Nr ≤ (∏ v, T v) * ∏ v, al v ^ 2 := by
        rw [div_le_iff₀ hNr]
        calc (∏ v, T v) = (∏ v, T v) * 1 := (mul_one _).symm
          _ ≤ (∏ v, T v) * ((∏ v, al v ^ 2) * Nr) := mul_le_mul_of_nonneg_left h1 hTpos
          _ = (∏ v, T v) * (∏ v, al v ^ 2) * Nr := by ring
    _ ≤ _ := hprod

theorem det_index_product_hyperbolic_inequality : Formalism.SLP.GlobalBoundRefinements.DetIndexProductHyperbolicInequality := by
  intro detM dLa₁ dLa₂ dPs₁ dPs₂ P₁ P₂ dQ₁ dQ₂ i₁ i₂ G0₁ G0₂ g NT K₁ K₂ Nr₁ Nr₂ e f
    hP₁ hP₂ hQ₁ hQ₂ hg hi₁ hi₂ hL₁ hL₂ hNT hK₁ hK₂ hN₁ hN₂ hD₁ hD₂ hPs₁ hPs₂ hG₁ hG₂ hB₁ hB₂ hgQ
  subst hPs₁ hPs₂
  have hG₁0 : 0 ≤ G0₁ / Nr₁ := le_trans (by positivity) hG₁
  have hG₂0 : 0 ≤ G0₂ / Nr₂ := le_trans (by positivity) hG₂
  have hG₁' : 0 ≤ G0₁ := by
    have h := mul_nonneg hG₁0 hN₁.le
    rwa [div_mul_cancel₀ _ hN₁.ne'] at h
  have hG₂' : 0 ≤ G0₂ := by
    have h := mul_nonneg hG₂0 hN₂.le
    rwa [div_mul_cancel₀ _ hN₂.ne'] at h
  have hD0 : 0 ≤ detM := by
    rw [hD₁]
    positivity
  have hDD : detM * detM = dLa₁ * dLa₂ / ((P₁ * P₂) * (dQ₁ * dQ₂)) := by
    calc detM * detM = (dLa₁ / (P₁ * dQ₁)) * (dLa₂ / (P₂ * dQ₂)) := by rw [← hD₁, ← hD₂]
      _ = dLa₁ * dLa₂ / ((P₁ * P₂) * (dQ₁ * dQ₂)) := by
        rw [div_mul_div_comm]
        congr 1
        ring
  have hX2 : (detM * i₁ * i₂) ^ 2 = (dLa₁ * i₁ ^ 2) * (dLa₂ * i₂ ^ 2) / ((P₁ * P₂) * (dQ₁ * dQ₂)) := by
    calc (detM * i₁ * i₂) ^ 2 = (detM * detM) * i₁ ^ 2 * i₂ ^ 2 := by ring
      _ = _ := by
        rw [hDD]
        field_simp
  have hnum : (dLa₁ * i₁ ^ 2) * (dLa₂ * i₂ ^ 2) ≤ (G0₁ / Nr₁) * (G0₂ / Nr₂) :=
    mul_le_mul hG₁ hG₂ (by positivity) hG₁0
  have hgQ' : g ^ (2 * f * e) / 4 ^ (e * f) ≤ dQ₁ * dQ₂ := by
    rw [div_le_iff₀ (by positivity)]
    linarith [hgQ, show (4:ℝ) ^ (e * f) * dQ₁ * dQ₂ = dQ₁ * dQ₂ * 4 ^ (e * f) by ring]
  have hden : (NT / (Nr₂ * K₂ ^ 2)) * (NT / (Nr₁ * K₁ ^ 2)) * (g ^ (2 * f * e) / 4 ^ (e * f)) ≤
      (P₁ * P₂) * (dQ₁ * dQ₂) :=
    mul_le_mul (mul_le_mul hB₁ hB₂ (by positivity) hP₁.le) hgQ' (by positivity) (by positivity)
  have hX2le : (detM * i₁ * i₂) ^ 2 ≤ (G0₁ / Nr₁) * (G0₂ / Nr₂) /
      ((NT / (Nr₂ * K₂ ^ 2)) * (NT / (Nr₁ * K₁ ^ 2)) * (g ^ (2 * f * e) / 4 ^ (e * f))) := by
    rw [hX2]
    exact div_le_div₀ (mul_nonneg hG₁0 hG₂0) hnum (by positivity) hden
  have hpw : ((2 / g) ^ (e * f)) ^ 2 = 4 ^ (e * f) / g ^ (2 * f * e) := by
    rw [← pow_mul, div_pow, show (4:ℝ) = 2 ^ 2 by norm_num, ← pow_mul,
      show e * f * 2 = 2 * (e * f) by ring, show 2 * f * e = 2 * (e * f) by ring]
  have hY2 : ((2 / g) ^ (e * f) * Real.sqrt (G0₁ * G0₂) * K₁ * K₂ / NT) ^ 2 =
      (G0₁ / Nr₁) * (G0₂ / Nr₂) /
        ((NT / (Nr₂ * K₂ ^ 2)) * (NT / (Nr₁ * K₁ ^ 2)) * (g ^ (2 * f * e) / 4 ^ (e * f))) := by
    rw [div_pow, mul_pow, mul_pow, mul_pow, hpw, Real.sq_sqrt (mul_nonneg hG₁' hG₂')]
    field_simp
  have hY0 : 0 ≤ (2 / g) ^ (e * f) * Real.sqrt (G0₁ * G0₂) * K₁ * K₂ / NT := by positivity
  rw [← hY2] at hX2le
  exact (pow_le_pow_iff_left₀ (by positivity) hY0 two_ne_zero).mp hX2le

end Formalism.SLP.GlobalBoundRefinements.P
end
end

-- bundled from Formalism.HyperbolicPlaceProducts.SubgroupIndexCounts.OmegaPow
section
namespace Formalism.SLP.P

theorem two_pow_length_primeFactorsList_le (j : ℕ) (hj : 1 ≤ j) :
    2 ^ (Nat.primeFactorsList j).length ≤ j := by
  have hprod := Nat.prod_primeFactorsList (show j ≠ 0 by omega)
  calc 2 ^ (Nat.primeFactorsList j).length ≤ (Nat.primeFactorsList j).prod :=
        List.pow_card_le_prod _ _ (fun p hp => (Nat.prime_of_mem_primeFactorsList hp).two_le)
    _ = j := hprod

theorem pow_primeFactors_length_le : Formalism.SLP.OmegaPow := by
  intro n j hn hj
  set k := (Nat.primeFactorsList j).length
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hk : (2 : ℝ) ^ k ≤ j := by exact_mod_cast two_pow_length_primeFactorsList_le j hj

  have hklog : (k : ℝ) ≤ Real.logb 2 j := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) hj0]
    simpa [Real.rpow_natCast] using hk
  have hlogn : 0 ≤ Real.logb 2 n := Real.logb_nonneg (by norm_num) (by exact_mod_cast hn)

  have e1 : (n : ℝ) ^ k = (2 : ℝ) ^ ((k : ℝ) * Real.logb 2 n) := by
    rw [mul_comm, Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hn0,
      Real.rpow_natCast]
  have e2 : (j : ℝ) ^ Real.logb 2 n = (2 : ℝ) ^ (Real.logb 2 j * Real.logb 2 n) := by
    rw [Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hj0]
  rw [e1, e2]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (mul_le_mul_of_nonneg_right hklog hlogn)

end Formalism.SLP.P
end

-- bundled from Formalism.HyperbolicPlaceProducts.SubgroupIndexCounts.ProdInfinitePlaceLeOfIntegral
section
open NumberField

namespace Formalism.SLP.GlobalBoundRefinements.P

theorem eq_one_of_sub_one_mem_prime : Formalism.SLP.GlobalBoundRefinements.RootUnityTriv := by
  intro E _ _ α P hP hw h1 hm

  obtain ⟨n, hn, hpow⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one E ℂ
    (NumberField.RingOfIntegers.isIntegral_coe α) (fun φ => by
      have := hw (NumberField.InfinitePlace.mk φ)
      rwa [NumberField.InfinitePlace.apply] at this)
  have hpowO : α ^ n = 1 := NumberField.RingOfIntegers.ext (by simpa using hpow)
  have hu : Units.ofPowEqOne α n hpowO hn.ne' ∈ NumberField.Units.torsion E := by
    rw [NumberField.Units.mem_torsion]
    intro w
    simpa using hw w
  have hm1 : α ^ Nat.card (NumberField.Units.torsion E) = 1 := by
    have := congrArg (fun g : NumberField.Units.torsion E => (((g : (RingOfIntegers E)ˣ)) : RingOfIntegers E))
      (pow_card_eq_one' (x := (⟨_, hu⟩ : NumberField.Units.torsion E)))
    simp only [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, Units.val_ofPowEqOne,
      OneMemClass.coe_one, Units.val_one] at this
    exact this
  by_contra hne
  apply hm

  have hsum : ∑ i ∈ Finset.range (Nat.card (NumberField.Units.torsion E)), α ^ i = 0 := by
    have h := geom_sum_mul α (Nat.card (NumberField.Units.torsion E))
    rw [hm1, sub_self] at h
    exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr hne)
  have hdiff : ∑ i ∈ Finset.range (Nat.card (NumberField.Units.torsion E)), (α ^ i - 1) ∈ P := by
    refine Ideal.sum_mem _ (fun i _ => ?_)
    obtain ⟨c, hc⟩ : α - 1 ∣ α ^ i - 1 := by simpa using sub_dvd_pow_sub_pow α 1 i
    rw [hc]
    exact P.mul_mem_right c h1
  rw [Finset.sum_sub_distrib, hsum, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
    zero_sub, neg_mem_iff] at hdiff
  exact hdiff

theorem prod_infinitePlace_le_of_integral : Formalism.SLP.GlobalBoundRefinements.ThmBNorm := by
  intro F _ _ s q x hs hq hβ hw
  obtain ⟨β, hβ⟩ := hβ
  have hβ0 : β ≠ 0 := by
    intro h0
    have : s / q = 0 := by rw [← hβ, h0]; simp
    exact div_ne_zero hs hq this

  have hN : (1 : ℝ) ≤ ∏ w : NumberField.InfinitePlace F, w (s / q) ^ w.mult := by
    rw [NumberField.InfinitePlace.prod_eq_abs_norm, ← hβ, ← Algebra.coe_norm_int]
    have hne : Algebra.norm ℤ β ≠ 0 := Algebra.norm_ne_zero_iff.mpr hβ0
    have : (1 : ℤ) ≤ |Algebra.norm ℤ β| := Int.one_le_abs hne
    exact_mod_cast this
  have hdiv : ∏ w : NumberField.InfinitePlace F, w (s / q) ^ w.mult =
      (∏ w : NumberField.InfinitePlace F, w s ^ w.mult) / ∏ w : NumberField.InfinitePlace F, w q ^ w.mult := by
    rw [← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl (fun w _ => ?_)
    rw [map_div₀, div_pow]
  have hqpos : 0 < ∏ w : NumberField.InfinitePlace F, w q ^ w.mult :=
    Finset.prod_pos (fun w _ => pow_pos (NumberField.InfinitePlace.pos_iff.mpr hq) _)
  have hsle : ∏ w : NumberField.InfinitePlace F, w s ^ w.mult ≤ ∏ w, (x w ^ 2) ^ w.mult :=
    Finset.prod_le_prod (fun w _ => pow_nonneg (NumberField.InfinitePlace.pos_iff.mpr hs).le _)
      (fun w _ => pow_le_pow_left₀ (NumberField.InfinitePlace.pos_iff.mpr hs).le (hw w) _)
  rw [hdiv, le_div_iff₀ hqpos, one_mul] at hN
  linarith

end Formalism.SLP.GlobalBoundRefinements.P
end

