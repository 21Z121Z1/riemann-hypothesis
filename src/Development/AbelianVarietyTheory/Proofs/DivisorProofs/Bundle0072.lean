import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerUnitRadicandQuotientRootIsReduced
section
open IsLocalRing Polynomial

namespace GlobalTheory

theorem kummerUnit_quotRoot_isReduced : ∀ (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (ϖ : A) (u : Aˣ) (m k : ℕ), Irreducible ϖ → IsUnit (m : A) → 0 < k → IsReduced (AdjoinRoot (Polynomial.X ^ k - Polynomial.C (AdjoinRoot.of (Polynomial.X ^ m - Polynomial.C (u : A) : Polynomial A) ϖ * AdjoinRoot.root (Polynomial.X ^ m - Polynomial.C (u : A) : Polynomial A)) : Polynomial (AdjoinRoot (Polynomial.X ^ m - Polynomial.C (u : A) : Polynomial A))) ⧸ Ideal.span {AdjoinRoot.root (Polynomial.X ^ k - Polynomial.C (AdjoinRoot.of (Polynomial.X ^ m - Polynomial.C (u : A) : Polynomial A) ϖ * AdjoinRoot.root (Polynomial.X ^ m - Polynomial.C (u : A) : Polynomial A)) : Polynomial (AdjoinRoot (Polynomial.X ^ m - Polynomial.C (u : A) : Polynomial A)))}) := by
  intro A _ _ _ ϖ u m k hϖ hm hk
  set f : A[X] := X ^ m - C (u : A) with hf
  set c : AdjoinRoot f := AdjoinRoot.of f ϖ * AdjoinRoot.root f with hc
  set g : (AdjoinRoot f)[X] := X ^ k - C c with hg
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hm
  have hy : IsUnit (AdjoinRoot.root f) := by
    have h0 := AdjoinRoot.eval₂_root f
    have h1 : AdjoinRoot.root f ^ m = AdjoinRoot.of f (u : A) := by
      rw [hf] at h0
      simp only [eval₂_sub, eval₂_X_pow, eval₂_C] at h0
      exact sub_eq_zero.mp h0
    have h2 : IsUnit (AdjoinRoot.root f ^ m) := by
      rw [h1]; exact (u.isUnit.map _)
    exact (isUnit_pow_iff hm0).mp h2
  have hspan : Ideal.span {c} = (Ideal.span {ϖ}).map (AdjoinRoot.of f) := by
    rw [Ideal.map_span, Set.image_singleton, hc]
    exact Ideal.span_singleton_mul_right_unit hy _
  haveI : (Ideal.span {ϖ}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hϖ
  letI : Field (A ⧸ Ideal.span {ϖ}) := Ideal.Quotient.field _
  have hredK : IsReduced ((A ⧸ Ideal.span {ϖ})[X] ⧸ Ideal.span {f.map (Ideal.Quotient.mk (Ideal.span {ϖ}))}) := by
    rw [← Ideal.isRadical_iff_quotient_reduced, ← isRadical_iff_span_singleton]
    apply Squarefree.isRadical
    apply Polynomial.Separable.squarefree
    have hmap : f.map (Ideal.Quotient.mk (Ideal.span {ϖ})) =
        X ^ m - C ((Units.map (Ideal.Quotient.mk (Ideal.span {ϖ})).toMonoidHom u : (A ⧸ Ideal.span {ϖ})ˣ) : A ⧸ Ideal.span {ϖ}) := by
      simp [hf, Polynomial.map_sub]
    rw [hmap]
    apply separable_X_pow_sub_C_unit
    simpa using hm.map (Ideal.Quotient.mk (Ideal.span {ϖ}))
  have hred1 : IsReduced (AdjoinRoot f ⧸ Ideal.span {c}) := by
    have e := (Ideal.quotEquivOfEq hspan).trans (AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot (Ideal.span {ϖ}) f)
    exact isReduced_of_injective e.toRingHom e.injective
  have hgroot : AdjoinRoot.of g c = AdjoinRoot.root g ^ k := by
    have h0 := AdjoinRoot.eval₂_root g
    rw [hg] at h0
    simp only [eval₂_sub, eval₂_X_pow, eval₂_C] at h0
    exact (sub_eq_zero.mp h0).symm
  let φ0 : AdjoinRoot g →+* AdjoinRoot f ⧸ Ideal.span {c} :=
    AdjoinRoot.lift (Ideal.Quotient.mk (Ideal.span {c})) 0 (by
      rw [hg]
      simp only [eval₂_sub, eval₂_X_pow, eval₂_C, zero_pow hk.ne', zero_sub, neg_eq_zero]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self c))
  let φ : AdjoinRoot g ⧸ Ideal.span {AdjoinRoot.root g} →+* AdjoinRoot f ⧸ Ideal.span {c} :=
    Ideal.Quotient.lift _ φ0 (by
      intro a ha
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      simp [φ0])
  let ψ : AdjoinRoot f ⧸ Ideal.span {c} →+* AdjoinRoot g ⧸ Ideal.span {AdjoinRoot.root g} :=
    Ideal.Quotient.lift _ ((Ideal.Quotient.mk _).comp (AdjoinRoot.of g)) (by
      intro a ha
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      rw [RingHom.comp_apply, map_mul, hgroot, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self _) k hk))
  have hcomp : ψ.comp φ = RingHom.id _ := by
    apply Ideal.Quotient.ringHom_ext
    apply AdjoinRoot.ringHom_ext
    · ext <;> simp [φ, φ0, ψ]
    · simp [φ, φ0, ψ]
  have hinj : Function.Injective φ := by
    intro x y hxy
    have := congrArg ψ hxy
    simpa [← RingHom.comp_apply, hcomp] using this
  exact isReduced_of_injective φ hinj

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LamLowNumericalEnd
section
namespace GlobalTheory

theorem lamLow_numerical_end : ∀ (f n r : ℕ) (L' dmax mass Lq lam : ℝ) (H dt dk dD : Fin f → ℝ), 8 ≤ n → 2 * r ≤ n → 1 ≤ r → 1 ≤ f → (5.5 : ℝ) ≤ L' → Real.log n ≤ L' → 0 ≤ dmax → Real.log (dmax + 2) ≤ 2 * L' → 1 / ((2 : ℝ) ^ n * (n.factorial : ℝ)) ≤ mass → 0 < Lq → |Real.log Lq| ≤ f * r / 4 → (∀ ρ, 0 < H ρ ∧ 1 ≤ dt ρ ∧ 1 ≤ dk ρ ∧ 0 < dD ρ ∧ Real.log (dD ρ) ≤ 2 + (r : ℝ) ^ 2 * Real.log (3 * (r : ℝ) ^ 2 * n * (dmax + 2))) → lam = mass * Lq * ∏ ρ, (H ρ * dt ρ * dk ρ / dD ρ) → ∑ ρ, Real.log (H ρ) - 2 * f * (n : ℝ) ^ 2 * L' ≤ Real.log lam := by
  intro f n r L' dmax mass Lq lam H dt dk dD hn hr hr1 hf hL' hlogn hdmax hlogd hmass hLq hlogLq hρ hlam
  have hn8 : (8 : ℝ) ≤ n := by exact_mod_cast hn
  have hr1' : (1 : ℝ) ≤ r := by exact_mod_cast hr1
  have hr2 : 2 * (r : ℝ) ≤ n := by exact_mod_cast hr
  have hf1 : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hnpos : (0 : ℝ) < n := by linarith
  have hrpos : (0 : ℝ) < r := by linarith
  have hmpos : 0 < mass := lt_of_lt_of_le (by positivity) hmass
  have hlogmass : -((n : ℝ) * Real.log 2 + (n : ℝ) * Real.log n) ≤ Real.log mass := by
    have h1 := Real.log_le_log (by positivity) hmass
    rw [one_div, Real.log_inv, Real.log_mul (by positivity) (by positivity), Real.log_pow] at h1
    have hfac : Real.log (n.factorial : ℝ) ≤ (n : ℝ) * Real.log n := by
      rw [← Real.log_pow]
      apply Real.log_le_log (by positivity)
      exact_mod_cast Nat.factorial_le_pow n
    linarith
  have hX : Real.log (3 * (r : ℝ) ^ 2 * n * (dmax + 2)) ≤ 5 * L' := by
    have hd : (0 : ℝ) < dmax + 2 := by linarith
    have h3 : 3 * (r : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by nlinarith
    have hle : 3 * (r : ℝ) ^ 2 * n * (dmax + 2) ≤ (n : ℝ) ^ 3 * (dmax + 2) := by
      calc 3 * (r : ℝ) ^ 2 * n * (dmax + 2) ≤ (n : ℝ) ^ 2 * n * (dmax + 2) := by gcongr
        _ = (n : ℝ) ^ 3 * (dmax + 2) := by ring
    have hpos : 0 < 3 * (r : ℝ) ^ 2 * n * (dmax + 2) :=
      mul_pos (mul_pos (mul_pos (by norm_num) (pow_pos hrpos 2)) hnpos) hd
    have h4 := Real.log_le_log hpos hle
    rw [Real.log_mul (pow_pos hnpos 3).ne' hd.ne', Real.log_pow] at h4
    push_cast at h4
    linarith
  have hsq : (r : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 / 4 := by nlinarith
  have hdD : (r : ℝ) ^ 2 * Real.log (3 * (r : ℝ) ^ 2 * n * (dmax + 2)) ≤ 5 / 4 * (n : ℝ) ^ 2 * L' := by
    calc (r : ℝ) ^ 2 * Real.log (3 * (r : ℝ) ^ 2 * n * (dmax + 2)) ≤ (r : ℝ) ^ 2 * (5 * L') :=
          mul_le_mul_of_nonneg_left hX (by positivity)
      _ ≤ (n : ℝ) ^ 2 / 4 * (5 * L') := mul_le_mul_of_nonneg_right hsq (by linarith)
      _ = 5 / 4 * (n : ℝ) ^ 2 * L' := by ring
  have hfac_pos : ∀ ρ, 0 < H ρ * dt ρ * dk ρ / dD ρ := fun ρ => by
    obtain ⟨h1, h2, h3, h4, -⟩ := hρ ρ
    have ht : 0 < dt ρ := by linarith
    have hk : 0 < dk ρ := by linarith
    exact div_pos (mul_pos (mul_pos h1 ht) hk) h4
  have hprodpos : 0 < ∏ ρ, (H ρ * dt ρ * dk ρ / dD ρ) := Finset.prod_pos (fun ρ _ => hfac_pos ρ)
  have e1 : Real.log lam = Real.log mass + Real.log Lq + ∑ ρ, Real.log (H ρ * dt ρ * dk ρ / dD ρ) := by
    rw [hlam, Real.log_mul (mul_pos hmpos hLq).ne' hprodpos.ne', Real.log_mul hmpos.ne' hLq.ne',
      Real.log_prod (fun ρ _ => (hfac_pos ρ).ne')]
  have e2 : ∀ ρ, Real.log (H ρ) - (2 + 5 / 4 * (n : ℝ) ^ 2 * L') ≤ Real.log (H ρ * dt ρ * dk ρ / dD ρ) := by
    intro ρ
    obtain ⟨h1, h2, h3, h4, h5⟩ := hρ ρ
    have ht : 0 < dt ρ := by linarith
    have hk : 0 < dk ρ := by linarith
    rw [Real.log_div (mul_pos (mul_pos h1 ht) hk).ne' h4.ne', Real.log_mul (mul_pos h1 ht).ne' hk.ne',
      Real.log_mul h1.ne' ht.ne']
    have := Real.log_nonneg h2
    have := Real.log_nonneg h3
    linarith
  have hsum : ∑ ρ, Real.log (H ρ) - (f : ℝ) * (2 + 5 / 4 * (n : ℝ) ^ 2 * L') ≤
      ∑ ρ, Real.log (H ρ * dt ρ * dk ρ / dD ρ) := by
    have := Finset.sum_le_sum (fun ρ (_ : ρ ∈ Finset.univ) => e2 ρ)
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    exact this
  have hLqlow : -((f : ℝ) * r / 4) ≤ Real.log Lq := by
    have := neg_abs_le (Real.log Lq)
    linarith
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hfL : 1 ≤ (f : ℝ) * L' := by nlinarith
  have hP1 : (n : ℝ) ≤ f * n * L' := by linarith [mul_le_mul_of_nonneg_left hfL hnpos.le]
  have hnL : 0 ≤ (n : ℝ) * L' := by positivity
  have hP2 : (n : ℝ) * L' ≤ f * n * L' := by linarith [mul_le_mul_of_nonneg_right hf1 hnL]
  have hP3 : (f : ℝ) * r / 4 ≤ f * n * L' := by
    have hrn : (r : ℝ) / 4 ≤ n * L' := by nlinarith
    linarith [mul_le_mul_of_nonneg_left hrn (by linarith : (0 : ℝ) ≤ f)]
  have hnL2 : (2 : ℝ) ≤ n * L' := by nlinarith [mul_le_mul hn8 hL' (by norm_num) hnpos.le]
  have hP4 : 2 * (f : ℝ) ≤ f * n * L' := by linarith [mul_le_mul_of_nonneg_left hnL2 (by linarith : (0 : ℝ) ≤ f)]
  have hbig : 8 * ((f : ℝ) * n * L') ≤ f * (n : ℝ) ^ 2 * L' := by
    have h0 : 0 ≤ (f : ℝ) * n * L' := by positivity
    linarith [mul_le_mul_of_nonneg_right hn8 h0]
  have hm1 := mul_le_mul_of_nonneg_left hlog2 hnpos.le
  have hm2 := mul_le_mul_of_nonneg_left hlogn hnpos.le
  rw [e1]
  linarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeFormIdealDualVectorIntegral
section
open NumberField
open scoped nonZeroDivisors

namespace GlobalTheory

theorem exists_fractionalIdeal_smul_mem_lattice_of_alternating
    {F V : Type} [Field F] [NumberField F] [AddCommGroup V] [Module F V]
    (hV : Module.finrank F V = 2) (B : LinearMap.BilinForm F V) (hB : ∀ z, B z z = 0)
    (L : Set V) (h0 : (0 : V) ∈ L) (hadd : ∀ x ∈ L, ∀ x' ∈ L, x + x' ∈ L)
    (hsmul : ∀ (a : 𝓞 F), ∀ x ∈ L, (a : F) • x ∈ L)
    (J : FractionalIdeal (𝓞 F)⁰ F) (hJ : J ≠ 0) (hBJ : ∀ z ∈ L, ∀ w ∈ L, B z w ∈ J)
    (hspan : ∀ t ∈ J, t ∈ Submodule.span (𝓞 F) {t | ∃ z ∈ L, ∃ w ∈ L, t = B z w})
    {v : V} (hv : v ≠ 0) :
    ∃ I : FractionalIdeal (𝓞 F)⁰ F, I ≠ 0 ∧ ∀ a : F, a ∈ I ↔ a • v ∈ L := by
  obtain ⟨x, hx, x', hx', hxx⟩ : ∃ x ∈ L, ∃ x' ∈ L, B x x' ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hJ
    rw [FractionalIdeal.eq_zero_iff]
    intro t ht
    have h1 := hspan t ht
    have h2 : Submodule.span (𝓞 F) {t | ∃ z ∈ L, ∃ w ∈ L, t = B z w} = ⊥ := by
      rw [Submodule.span_eq_bot]
      rintro _ ⟨z, hz, w, hw, rfl⟩
      exact hcon z hz w hw
    rw [h2] at h1
    exact (Submodule.mem_bot _).1 h1
  have hli : LinearIndependent F ![x, x'] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have e1 : B (s • x + t • x') x' = 0 := by rw [hst]; simp
    have e2 : B x (s • x + t • x') = 0 := by rw [hst]; simp
    simp [hB, hxx] at e1 e2
    exact ⟨e1, e2⟩
  have htop := hli.span_eq_top_of_card_eq_finrank (by simp [hV])
  have hvm : v ∈ Submodule.span F ({x, x'} : Set V) := by
    have : Set.range ![x, x'] = {x, x'} := by simp [Set.pair_comm]
    rw [← this, htop]; trivial
  obtain ⟨c, c', hc⟩ := Submodule.mem_span_pair.1 hvm
  obtain ⟨t, ht0, ht⟩ : ∃ t : F, t ≠ 0 ∧ ∀ a : F, a • v ∈ L → a * t ∈ J := by
    by_cases hc0 : c = 0
    · have hc' : c' ≠ 0 := by
        rintro rfl
        apply hv
        rw [← hc, hc0]; simp
      refine ⟨B x v, ?_, fun a ha => ?_⟩
      · rw [← hc]; simp [hB, hxx, hc']
      · simpa using hBJ x hx _ ha
    · refine ⟨B v x', ?_, fun a ha => ?_⟩
      · rw [← hc]; simp [hB, hxx, hc0]
      · simpa using hBJ _ ha x' hx'
  let M : Submodule (𝓞 F) F :=
    { carrier := {a | a • v ∈ L}
      add_mem' := fun {a b} ha hb => by
        show (a + b) • v ∈ L
        rw [add_smul]; exact hadd _ ha _ hb
      zero_mem' := by
        show (0 : F) • v ∈ L
        rw [zero_smul]; exact h0
      smul_mem' := fun r a ha => by
        show ((r : F) * a) • v ∈ L
        rw [mul_smul]; exact hsmul r _ ha }
  have hM : IsFractional (𝓞 F)⁰ M := by
    apply FractionalIdeal.isFractional_of_le
      (J := FractionalIdeal.spanSingleton (𝓞 F)⁰ t⁻¹ * J)
    intro a ha
    rw [FractionalIdeal.mem_coe, FractionalIdeal.mem_singleton_mul]
    exact ⟨a * t, ht a ha, by field_simp⟩
  refine ⟨⟨M, hM⟩, ?_, fun a => Iff.rfl⟩
  obtain ⟨d, n, hn⟩ := IsLocalization.exists_integer_multiple (𝓞 F)⁰ c
  obtain ⟨d', n', hn'⟩ := IsLocalization.exists_integer_multiple (𝓞 F)⁰ c'
  have hn1 : (n : F) = ((d : 𝓞 F) : F) * c := by
    simpa [Algebra.smul_def] using hn
  have hn2 : (n' : F) = ((d' : 𝓞 F) : F) * c' := by
    simpa [Algebra.smul_def] using hn'
  intro hz
  replace hz := FractionalIdeal.eq_zero_iff.1 hz
  have hmem : (((d : 𝓞 F) : F) * ((d' : 𝓞 F) : F)) • v ∈ L := by
    have e : (((d : 𝓞 F) : F) * ((d' : 𝓞 F) : F)) • v
        = ((d' : 𝓞 F) : F) • (n : F) • x + ((d : 𝓞 F) : F) • (n' : F) • x' := by
      rw [← hc, hn1, hn2]; module
    rw [e]
    exact hadd _ (hsmul _ _ (hsmul _ _ hx)) _ (hsmul _ _ (hsmul _ _ hx'))
  have h := hz _ hmem
  have hd : ((d : 𝓞 F) : F) ≠ 0 := by exact_mod_cast nonZeroDivisors.coe_ne_zero d
  have hd' : ((d' : 𝓞 F) : F) ≠ 0 := by exact_mod_cast nonZeroDivisors.coe_ne_zero d'
  exact mul_ne_zero hd hd' h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeFormIdealGeneratesDualVector
section
open NumberField
open scoped nonZeroDivisors

namespace GlobalTheory

theorem exists_coords_of_alt_ne_zero {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    (hV : Module.finrank F V = 2) (B : LinearMap.BilinForm F V) (hB : ∀ z, B z z = 0)
    {x x' : V} (h : B x x' ≠ 0) (v : V) : ∃ c c' : F, v = c • x + c' • x' := by
  have hanti : B x' x = - B x x' := by
    have h1 := hB (x + x')
    simp only [map_add, LinearMap.add_apply, hB] at h1
    linear_combination h1
  have hli : LinearIndependent F ![x, x'] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 := congrArg (fun u => B u x') hst
    have h2 := congrArg (fun u => B x u) hst
    simp [hB] at h1 h2
    exact ⟨h1.resolve_right h, h2.resolve_right h⟩
  have hsp : Submodule.span F (Set.range ![x, x']) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank (by simp [hV])
  have hv : v ∈ Submodule.span F (Set.range ![x, x']) := by rw [hsp]; trivial
  rw [Matrix.range_cons_cons_empty, Submodule.mem_span_pair] at hv
  obtain ⟨a, b, hab⟩ := hv
  exact ⟨a, b, hab.symm⟩

theorem exists_fractionalIdeal_pairing_values :
    ∀ {F V : Type} [Field F] [NumberField F] [AddCommGroup V] [Module F V],
    Module.finrank F V = 2 → ∀ (B : LinearMap.BilinForm F V), (∀ z, B z z = 0) →
    ∀ (L : Set V), (0 : V) ∈ L → (∀ x ∈ L, ∀ x' ∈ L, x + x' ∈ L) →
    (∀ (a : 𝓞 F), ∀ x ∈ L, (a : F) • x ∈ L) →
    ∀ (J : FractionalIdeal (𝓞 F)⁰ F), J ≠ 0 → (∀ z ∈ L, ∀ w ∈ L, B z w ∈ J) →
    (∀ t ∈ J, t ∈ Submodule.span (𝓞 F) {t | ∃ z ∈ L, ∃ w ∈ L, t = B z w}) →
    ∀ {v : V}, v ≠ 0 →
      ∃ K : FractionalIdeal (𝓞 F)⁰ F, K ≠ 0 ∧ ∀ t, t ∈ K ↔ ∃ z ∈ L, t = B z v := by
  intro F V _ _ _ _ hV B hB L h0 hadd hsmul J hJ hLJ hJL v hv
  obtain ⟨x, hx, x', hx', hxx⟩ : ∃ x ∈ L, ∃ x' ∈ L, B x x' ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hJ
    rw [FractionalIdeal.eq_zero_iff]
    intro t ht
    have h1 := hJL t ht
    have h2 : Submodule.span (𝓞 F) {t | ∃ z ∈ L, ∃ w ∈ L, t = B z w} ≤ ⊥ := by
      rw [Submodule.span_le]
      rintro s ⟨z, hz, w, hw, rfl⟩
      simpa using hcon z hz w hw
    simpa using h2 h1
  obtain ⟨c, c', rfl⟩ := exists_coords_of_alt_ne_zero hV B hB hxx v
  let M : Submodule (𝓞 F) F :=
    { carrier := {t | ∃ z ∈ L, t = B z (c • x + c' • x')}
      zero_mem' := ⟨0, h0, by simp⟩
      add_mem' := by
        rintro _ _ ⟨z, hz, rfl⟩ ⟨w, hw, rfl⟩
        exact ⟨z + w, hadd z hz w hw, by rw [map_add B, LinearMap.add_apply]⟩
      smul_mem' := by
        rintro a _ ⟨z, hz, rfl⟩
        refine ⟨(a : F) • z, hsmul a z hz, ?_⟩
        rw [map_smul B, LinearMap.smul_apply, Algebra.smul_def, smul_eq_mul] }
  have hM : M ≤ ((FractionalIdeal.spanSingleton (𝓞 F)⁰ c * J +
      FractionalIdeal.spanSingleton (𝓞 F)⁰ c' * J : FractionalIdeal (𝓞 F)⁰ F) :
      Submodule (𝓞 F) F) := by
    rintro _ ⟨z, hz, rfl⟩
    rw [FractionalIdeal.coe_add, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    refine Submodule.add_mem_sup ?_ ?_
    · exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ _)
        (hLJ z hz x hx)
    · exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ _)
        (hLJ z hz x' hx')
  refine ⟨⟨M, FractionalIdeal.isFractional_of_le hM⟩, ?_, fun t => Iff.rfl⟩
  intro hK0
  have hK := FractionalIdeal.eq_zero_iff.1 hK0
  have h1 := hK _ (show B x (c • x + c' • x') ∈ M from ⟨x, hx, rfl⟩)
  have h2 := hK _ (show B x' (c • x + c' • x') ∈ M from ⟨x', hx', rfl⟩)
  have hanti : B x' x = - B x x' := by
    have h1 := hB (x + x')
    simp only [map_add, LinearMap.add_apply, hB] at h1
    linear_combination h1
  simp [hB, hanti, hxx] at h1 h2
  apply hv
  simp [h1, h2]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeFormIdealPairOfVectors
section
open NumberField
open scoped nonZeroDivisors

namespace GlobalTheory

theorem exists_coords_of_alt_pair {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    (hV : Module.finrank F V = 2) (B : LinearMap.BilinForm F V) (hB : ∀ z, B z z = 0)
    {v w : V} (hv : v ≠ 0) (hw : B w v = 1) (u : V) : ∃ p q : F, p • v + q • w = u := by
  have hli : LinearIndependent F ![v, w] := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have h1 : B (s • v + t • w) v = 0 := by rw [h]; simp
    have ht : t = 0 := by simpa [hB, hw] using h1
    subst ht
    simp only [zero_smul, add_zero, smul_eq_zero] at h
    exact ⟨h.resolve_right hv, rfl⟩
  have hsp := hli.span_eq_top_of_card_eq_finrank (by simp [hV])
  have hr : Set.range ![v, w] = {v, w} := by
    simp [Matrix.range_cons, Matrix.range_empty, Set.pair_comm]
  rw [hr] at hsp
  have hu : u ∈ Submodule.span F ({v, w} : Set V) := by rw [hsp]; trivial
  exact Submodule.mem_span_pair.mp hu

theorem lattice_eq_ideal_sum_and_mul_eq :
    ∀ {F V : Type} [Field F] [NumberField F] [AddCommGroup V] [Module F V], Module.finrank F V = 2 → ∀ (B : LinearMap.BilinForm F V), (∀ z, B z z = 0) → ∀ (L : Set V), (0 : V) ∈ L → (∀ x ∈ L, ∀ x' ∈ L, x + x' ∈ L) → (∀ (a : 𝓞 F), ∀ x ∈ L, (a : F) • x ∈ L) →
    ∀ (J : FractionalIdeal (𝓞 F)⁰ F), (∀ z ∈ L, ∀ w ∈ L, B z w ∈ J) →
    (∀ t ∈ J, t ∈ Submodule.span (𝓞 F) {t | ∃ z ∈ L, ∃ w ∈ L, t = B z w}) →
    ∀ {v w : V}, v ≠ 0 → ∀ (I K : FractionalIdeal (𝓞 F)⁰ F), (∀ a : F, a ∈ I ↔ a • v ∈ L) →
    (∀ t, t ∈ K ↔ ∃ z ∈ L, t = B z v) → B w v = 1 → (∀ t ∈ K, t • w ∈ L) →
    (∀ x, x ∈ L ↔ ∃ a ∈ I, ∃ t ∈ K, x = a • v + t • w) ∧ I * K = J := by
  intro F V _ _ _ _ hV B hB L _ hadd hsmul J hJ hJs v w hv I K hI hK hw hwL
  have hvw : B v w = -1 := by
    have h := hB (v + w)
    simp only [map_add, LinearMap.add_apply, hB, hw] at h
    linear_combination h
  have hmem : ∀ x, x ∈ L ↔ ∃ a ∈ I, ∃ t ∈ K, x = a • v + t • w := by
    intro x
    constructor
    · intro hx
      obtain ⟨p, q, rfl⟩ := exists_coords_of_alt_pair hV B hB hv hw x
      have hq : q ∈ K := (hK q).2 ⟨_, hx, by simp [hB, hw]⟩
      refine ⟨p, (hI p).2 ?_, q, hq, rfl⟩
      have h1 := hadd _ hx _ (hsmul (-1) _ (hwL q hq))
      simpa using h1
    · rintro ⟨a, ha, t, ht, rfl⟩
      exact hadd _ ((hI a).1 ha) _ (hwL t ht)
  refine ⟨hmem, le_antisymm ?_ ?_⟩
  · rw [FractionalIdeal.mul_le]
    intro a ha t ht
    have h := hJ _ (hwL t ht) _ ((hI a).1 ha)
    simpa [hw, mul_comm] using h
  · intro t ht
    have h := hJs t ht
    have hle : Submodule.span (𝓞 F) {t | ∃ z ∈ L, ∃ w ∈ L, t = B z w}
        ≤ ((I * K : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F) := by
      rw [Submodule.span_le]
      rintro _ ⟨z, hz, z', hz', rfl⟩
      obtain ⟨a, ha, s, hs, rfl⟩ := (hmem z).1 hz
      obtain ⟨a', ha', s', hs', rfl⟩ := (hmem z').1 hz'
      have e : B (a • v + s • w) (a' • v + s' • w) = a' * s - a * s' := by
        simp [hB, hw, hvw]; ring
      rw [e]
      exact Submodule.sub_mem _ (FractionalIdeal.mul_mem_mul ha' hs)
        (FractionalIdeal.mul_mem_mul ha hs')
    exact hle h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeHomFiniteImageOfTrivialOnMultiples
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory

theorem lattice_hom_finite_image_of_trivial_on_multiples :
    ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (G : Type) [Group G] (e : (Fin g → ℂ) → G) (N : ℕ),
    DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → (∀ z w, e (z + w) = e z * e w) → 0 < N →
    (∀ l ∈ Λ, e ((N : ℂ) • l) = 1) → (e '' (Λ : Set (Fin g → ℂ))).Finite := by
  intro g Λ G _ e N hd hspan hadd hN hker
  haveI := hd
  haveI : IsZLattice ℝ Λ := ⟨hspan⟩
  let b := Module.Free.chooseBasis ℤ Λ
  let f : (Module.Free.ChooseBasisIndex ℤ Λ → Fin N) → G :=
    fun a => e (∑ i, ((a i : ℕ) : ℤ) • ((b i : Λ) : Fin g → ℂ))
  refine (Set.finite_range f).subset ?_
  rintro _ ⟨l, hl, rfl⟩
  set x : Λ := ⟨l, hl⟩ with hxdef
  let c : Module.Free.ChooseBasisIndex ℤ Λ → ℤ := fun i => b.repr x i
  let q : Λ := ∑ i, (c i / N) • b i
  have hc : ∀ i, 0 ≤ c i % (N : ℤ) := fun i => Int.emod_nonneg _ (by exact_mod_cast hN.ne')
  refine ⟨fun i => ⟨(c i % (N : ℤ)).toNat, ?_⟩, ?_⟩
  · have h1 := Int.emod_lt_of_pos (c i) (by exact_mod_cast hN : (0 : ℤ) < N)
    omega
  · have hl' : l = (N : ℂ) • ((q : Λ) : Fin g → ℂ) +
        ∑ i, (((c i % (N : ℤ)).toNat : ℕ) : ℤ) • ((b i : Λ) : Fin g → ℂ) := by
      have hx : l = ((∑ i, c i • b i : Λ) : Fin g → ℂ) := by
        rw [b.sum_repr x]
      rw [hx]
      simp only [q, Submodule.coe_sum, Submodule.coe_smul, Finset.smul_sum]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Int.toNat_of_nonneg (hc i)]
      have hN' : (N : ℂ) = ((N : ℤ) : ℂ) := by norm_cast
      rw [hN', Int.cast_smul_eq_zsmul, smul_smul, ← add_smul]
      have h2 := Int.mul_ediv_add_emod (c i) (N : ℤ)
      congr 1
      linarith
    refine Eq.trans ?_ (congrArg e hl').symm
    rw [hadd, hker _ q.2, one_mul]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeMultipleMemSublattice
section
open Module

namespace GlobalTheory

theorem sublattice_of_full_rank_quotient_torsion : ∀ (n : ℕ) (Λ Λ₂ M : Submodule ℤ (Fin n → ℂ)), DiscreteTopology Λ → DiscreteTopology Λ₂ → Submodule.span ℝ (Λ : Set (Fin n → ℂ)) = ⊤ → Submodule.span ℝ (Λ₂ : Set (Fin n → ℂ)) = ⊤ → M ≤ Λ → Module.rank ℤ Λ₂ ≤ Module.rank ℤ M → ∀ w ∈ Λ, ∃ k : ℤ, k ≠ 0 ∧ k • w ∈ M := by
  intro n Λ Λ₂ M hΛ hΛ₂ hsΛ hsΛ₂ hM hr w hw
  haveI : IsZLattice ℝ Λ := ⟨hsΛ⟩
  haveI : IsZLattice ℝ Λ₂ := ⟨hsΛ₂⟩
  haveI : Module.Finite ℤ Λ := ZLattice.module_finite ℝ Λ
  haveI : Module.Finite ℤ Λ₂ := ZLattice.module_finite ℝ Λ₂
  have e1 : finrank ℤ Λ = finrank ℝ (Fin n → ℂ) := ZLattice.rank ℝ Λ
  have e2 : finrank ℤ Λ₂ = finrank ℝ (Fin n → ℂ) := ZLattice.rank ℝ Λ₂
  set M' : Submodule ℤ Λ := M.comap Λ.subtype with hM'
  have hMM : Module.rank ℤ M' = Module.rank ℤ M := (Submodule.comapSubtypeEquivOfLe hM).rank_eq
  have hΛr : Module.rank ℤ Λ = (finrank ℤ Λ : Cardinal) := (Module.finrank_eq_rank ℤ Λ).symm
  have hΛ₂r : Module.rank ℤ Λ₂ = (finrank ℤ Λ₂ : Cardinal) := (Module.finrank_eq_rank ℤ Λ₂).symm
  have hle : Module.rank ℤ M' ≤ Module.rank ℤ Λ := Submodule.rank_le M'
  have hge : Module.rank ℤ Λ ≤ Module.rank ℤ M' := by
    rw [hMM, hΛr, e1, ← e2, ← hΛ₂r]; exact hr
  have heq : Module.rank ℤ M' = Module.rank ℤ Λ := le_antisymm hle hge
  have hsum := rank_quotient_add_rank_of_isDomain M'
  haveI : Module.Finite ℤ M' := Module.Finite.of_injective M'.subtype M'.injective_subtype
  rw [heq, hΛr, ← Module.finrank_eq_rank ℤ (Λ ⧸ M')] at hsum
  have h0 : finrank ℤ (Λ ⧸ M') = 0 := by
    have : ((finrank ℤ (Λ ⧸ M') + finrank ℤ Λ : ℕ) : Cardinal) = (finrank ℤ Λ : Cardinal) := by
      push_cast; exact hsum
    have := Nat.cast_injective this
    omega
  have htor : Module.IsTorsion ℤ (Λ ⧸ M') := Module.finrank_eq_zero_iff_isTorsion.1 h0
  obtain ⟨⟨k, hk⟩, hx⟩ := htor (x := Submodule.Quotient.mk (⟨w, hw⟩ : Λ))
  refine ⟨k, nonZeroDivisors.ne_zero hk, ?_⟩
  have : (k • (⟨w, hw⟩ : Λ)) ∈ M' := by
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]; exact hx
  simpa [hM'] using this

end GlobalTheory
end

