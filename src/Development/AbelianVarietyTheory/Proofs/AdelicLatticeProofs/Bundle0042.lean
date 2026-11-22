import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0039
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0002
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0027
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0019
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0028
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0025
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0026
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0040
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0021

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Hilbert90SUnitsKummerStatement
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbert90_sUnits_kummer' : ∀ (p : ℕ) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (ζ δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsKum p ζ δ θ σ → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (SE : Finset (HeightOneSpectrum (𝓞 E))), (∀ w : HeightOneSpectrum (𝓞 E), w ∈ SE ↔ w.under (𝓞 F) ∈ S) → AdmP p F S → (∀ v, v ∉ S → v.valuation F δ = 1) → ∀ u : Eˣ, u ∈ sUnits E SE → ∏ i ∈ Finset.range p, σ^[i] (u : E) = 1 → ∃ y : Eˣ, y ∈ sUnits E SE ∧ (u : E) = σ y / y := by
  first | exact @GlobalTheory.CNorm.hilbert90_sUnits_kummer | exact GlobalTheory.CNorm.hilbert90_sUnits_kummer | (intros; apply GlobalTheory.CNorm.hilbert90_sUnits_kummer <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IndexUnitsLocalSquaresFiniteRealPlacesLe
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

private theorem isSquare_real_iff_nonneg (r : ℝ) : IsSquare r ↔ 0 ≤ r :=
  ⟨fun h => h.nonneg, fun h => ⟨Real.sqrt r, (Real.mul_self_sqrt h).symm⟩⟩

theorem index_sqSub_real_dvd_two {F : Type} [Field F] (σ : F →+* ℝ) : (sqSub σ).index ∣ 2 := by
  by_cases h : ∀ x : Fˣ, x ∈ sqSub σ
  · rw [show sqSub σ = ⊤ from eq_top_iff.mpr fun x _ => h x, Subgroup.index_top]
    exact one_dvd 2
  · push_neg at h
    obtain ⟨a, ha⟩ := h
    have hne : ∀ x : Fˣ, σ (x : F) ≠ 0 := fun x => (x.isUnit.map σ).ne_zero
    have hmem : ∀ x : Fˣ, x ∈ sqSub σ ↔ 0 ≤ σ (x : F) := fun x =>
      (mem_sqSub σ x).trans (isSquare_real_iff_nonneg _)
    have ha' : σ (a : F) < 0 := not_le.mp fun h' => ha ((hmem a).mpr h')
    have h2 : (sqSub σ).index = 2 := by
      refine Subgroup.index_eq_two_iff.mpr ⟨a, fun b => ?_⟩
      rw [hmem, hmem, Units.val_mul, map_mul]
      rcases lt_or_gt_of_ne (hne b) with hb | hb
      · exact Or.inl ⟨mul_nonneg_of_nonpos_of_nonpos hb.le ha'.le, not_le.mpr hb⟩
      · exact Or.inr ⟨hb.le, not_le.mpr (mul_neg_of_pos_of_neg hb ha')⟩
    rw [h2]

theorem exists_valuation_two_eq_exp {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) : ∃ e : ℕ, v.valuation F 2 = WithZero.exp (-(e : ℤ)) := by
  have h2 : (2 : F) = algebraMap (𝓞 F) F 2 := (map_ofNat _ 2).symm
  have hle : v.valuation F 2 ≤ 1 := by
    rw [h2]
    exact v.valuation_le_one 2
  have hne : v.valuation F 2 ≠ 0 := (Valuation.ne_zero_iff _).mpr two_ne_zero
  have hk : WithZero.log (v.valuation F 2) ≤ 0 := by
    rw [← WithZero.exp_le_exp, WithZero.exp_log hne, WithZero.exp_zero]
    exact hle
  refine ⟨(-WithZero.log (v.valuation F 2)).toNat, ?_⟩
  rw [Int.toNat_of_nonneg (by omega), neg_neg, WithZero.exp_log hne]

private theorem index_biInf_ne_zero_and_le_prod {G ι : Type} [Group G] [DecidableEq ι] (S : Finset ι)
    (f : ι → Subgroup G) :
    (∀ i ∈ S, (f i).index ≠ 0) →
      (⨅ i ∈ S, f i).index ≠ 0 ∧ (⨅ i ∈ S, f i).index ≤ ∏ i ∈ S, (f i).index := by
  refine Finset.induction_on S ?_ ?_
  · intro _
    simp
  · intro a s ha ih hf
    rw [Finset.iInf_insert, Finset.prod_insert ha]
    obtain ⟨h0, hle⟩ := ih fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have ha0 := hf a (Finset.mem_insert_self a s)
    exact ⟨Subgroup.index_inf_ne_zero ha0 h0,
      Subgroup.index_inf_le.trans (Nat.mul_le_mul_left _ hle)⟩

theorem index_locSq_le : ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))), (locSq F S).index ≠ 0 ∧ (locSq F S).index ≤ 4 ^ (S.card + Fintype.card (InfinitePlace F)) := by
  intro F _ _ S
  classical
  choose e he using fun v : HeightOneSpectrum (𝓞 F) => exists_valuation_two_eq_exp v
  have hP := GlobalTheory.T.prod_absNorm_pow_valuation_two_le F S e (fun v _ => he v)
  have hN : ∀ v : HeightOneSpectrum (𝓞 F),
      (sqSub (algebraMap F (v.adicCompletion F))).index ≠ 0 ∧
        (sqSub (algebraMap F (v.adicCompletion F))).index ≤ 4 * Ideal.absNorm v.asIdeal ^ e v :=
    fun v => GlobalTheory.T.index_unitsSquareUnderRingHom_adicCompletion_le F v (e v) (he v)
  obtain ⟨hF0, hFle⟩ := index_biInf_ne_zero_and_le_prod S (fun v => sqSub (algebraMap F (v.adicCompletion F)))
    (fun v _ => (hN v).1)
  have hR2 : ∀ σ : F →+* ℝ, (sqSub σ).index ≤ 2 := fun σ =>
    Nat.le_of_dvd two_pos (index_sqSub_real_dvd_two σ)
  obtain ⟨hR0, hRle⟩ := index_biInf_ne_zero_and_le_prod (Finset.univ : Finset (F →+* ℝ)) (fun σ => sqSub σ)
    (fun σ _ => ne_zero_of_dvd_ne_zero two_ne_zero (index_sqSub_real_dvd_two σ))
  have hRu : (⨅ σ : F →+* ℝ, sqSub σ) = ⨅ σ ∈ (Finset.univ : Finset (F →+* ℝ)), sqSub σ := by
    simp
  have hloc : locSq F S = (⨅ v ∈ S, sqSub (algebraMap F (v.adicCompletion F))) ⊓
      ⨅ σ ∈ (Finset.univ : Finset (F →+* ℝ)), sqSub σ := by
    rw [← hRu]
    rfl
  rw [hloc]
  refine ⟨Subgroup.index_inf_ne_zero hF0 hR0, ?_⟩
  have hF : (⨅ v ∈ S, sqSub (algebraMap F (v.adicCompletion F))).index ≤
      4 ^ S.card * 2 ^ Module.finrank ℚ F := by
    refine hFle.trans ?_
    calc ∏ v ∈ S, (sqSub (algebraMap F (v.adicCompletion F))).index
        ≤ ∏ v ∈ S, (4 * Ideal.absNorm v.asIdeal ^ e v) :=
          Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun v _ => (hN v).2)
      _ = 4 ^ S.card * ∏ v ∈ S, Ideal.absNorm v.asIdeal ^ e v := by
          rw [Finset.prod_mul_distrib, Finset.prod_const]
      _ ≤ 4 ^ S.card * 2 ^ Module.finrank ℚ F := Nat.mul_le_mul_left _ hP
  have hR : (⨅ σ ∈ (Finset.univ : Finset (F →+* ℝ)), sqSub σ).index ≤
      2 ^ InfinitePlace.nrRealPlaces F := by
    refine hRle.trans ?_
    calc ∏ σ ∈ (Finset.univ : Finset (F →+* ℝ)), (sqSub σ).index
        ≤ ∏ _σ ∈ (Finset.univ : Finset (F →+* ℝ)), 2 :=
          Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun σ _ => hR2 σ)
      _ = 2 ^ InfinitePlace.nrRealPlaces F := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_eq_nat_card, GlobalTheory.T.card_ringHom_real_eq_nrRealPlaces' F]
  refine Subgroup.index_inf_le.trans ((Nat.mul_le_mul hF hR).trans (le_of_eq ?_))
  rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    ← InfinitePlace.card_add_two_mul_card_eq_rank, show (4 : ℕ) = 2 ^ 2 by norm_num]
  simp only [← pow_mul, ← pow_add]
  congr 1
  ring

end GlobalTheory.QNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemSpanRatPolysVanishingOfAutStable
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem evC_map_ringEquiv {ι : Type} (σ : ℂ ≃+* ℂ) (f : MvPolynomial (ι × ι) ℂ) (g : Matrix ι ι ℂ) :
    evC (MvPolynomial.map (σ : ℂ →+* ℂ) f) g = σ (evC f (g.map σ.symm)) := by
  unfold evC
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p n hp => simp only [map_mul, hp]; simp

theorem evC_map_rat {ι : Type} (f : MvPolynomial (ι × ι) ℚ) (g : Matrix ι ι ℂ) :
    evC (MvPolynomial.map (algebraMap ℚ ℂ) f) g = ev f g := by
  unfold evC ev
  rw [MvPolynomial.eval_map, MvPolynomial.aeval_def]

theorem mem_span_vanI_of_vanish : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), (∀ σ : ℂ ≃+* ℂ, ∀ g ∈ Γ, g.map σ ∈ Γ) → ∀ f : MvPolynomial (ι × ι) ℂ, (∀ g ∈ Γ, evC f g = 0) → f ∈ Submodule.span ℂ ((MvPolynomial.map (algebraMap ℚ ℂ)) '' vanI Γ) := by
  intro ι _ _ Γ hΓ f hf
  let W : Submodule ℂ (MvPolynomial (ι × ι) ℂ) :=
    { carrier := {f | ∀ g ∈ Γ, evC f g = 0}
      add_mem' := by
        intro a b ha hb g hg
        have h1 := ha g hg
        have h2 := hb g hg
        unfold evC at *
        rw [map_add, h1, h2, add_zero]
      zero_mem' := by
        intro g hg
        simp [evC]
      smul_mem' := by
        intro c a ha g hg
        have h1 := ha g hg
        unfold evC at *
        rw [MvPolynomial.smul_eval, h1, mul_zero] }
  have hrepr : ∀ (p : MvPolynomial (ι × ι) ℂ) k,
      (MvPolynomial.basisMonomials (ι × ι) ℂ).repr p k = MvPolynomial.coeff k p := fun p k => rfl
  have key := GlobalTheory.T.galoisStable_submodule_le_span_rational _ _ (MvPolynomial.basisMonomials (ι × ι) ℂ) W (by
    intro σ w hw
    refine ⟨MvPolynomial.map (σ : ℂ →+* ℂ) w, ?_, ?_⟩
    · intro g hg
      rw [evC_map_ringEquiv, hw _ (hΓ σ.symm g hg), map_zero]
    · intro k
      rw [hrepr, hrepr, MvPolynomial.coeff_map]
      rfl)
  refine Submodule.span_mono ?_ (key (show f ∈ W from hf))
  rintro w ⟨hw, hq⟩
  have hl : w ∈ Set.range (MvPolynomial.map (σ := ι × ι) (algebraMap ℚ ℂ)) := by
    rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
    intro c hc
    simp only [Finset.mem_coe, MvPolynomial.mem_coeffs_iff] at hc
    obtain ⟨k, -, rfl⟩ := hc
    obtain ⟨q, hq⟩ := hq k
    exact ⟨q, by rw [← hrepr, hq]; rfl⟩
  obtain ⟨w₀, rfl⟩ := hl
  refine ⟨w₀, ?_, rfl⟩
  intro g hg
  rw [← evC_map_rat]
  exact hw g hg

end GlobalTheory.ClassFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemSpanRationalKroneckerInvariants
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.RationalInvariants

def invSub {ι : Type} [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (n : ℕ) :
    Submodule ℂ ((Fin n → ι) → ℂ) where
  carrier := {μ | ∀ g ∈ Γ, μ ᵥ* tpow n g = μ}
  add_mem' := by
    intro a b ha hb g hg
    rw [Matrix.add_vecMul, ha g hg, hb g hg]
  zero_mem' := by
    intro g _
    exact Matrix.zero_vecMul _
  smul_mem' := by
    intro c a ha g hg
    rw [Matrix.smul_vecMul, ha g hg]

theorem mem_span_rational :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), (∀ σ : ℂ ≃+* ℂ, ∀ g ∈ Γ, g.map σ ∈ Γ) → ∀ (n : ℕ) (l : (Fin n → ι) → ℂ), (∀ g ∈ Γ, l ᵥ* tpow n g = l) → l ∈ Submodule.span ℂ {μ : (Fin n → ι) → ℂ | (∀ g ∈ Γ, μ ᵥ* tpow n g = μ) ∧ ∀ a, ∃ q : ℚ, μ a = q} := by
  intro ι _ _ Γ hΓ n l hl
  have h := GlobalTheory.T.galoisStable_submodule_le_span_rational _ _ (Pi.basisFun ℂ (Fin n → ι)) (invSub Γ n) (by
    intro σ w hw
    refine ⟨fun a => σ (w a), ?_, fun k => by simp⟩
    intro g hg
    funext b
    have h1 := congrArg σ (congrFun (hw _ (hΓ σ.symm g hg)) b)
    rw [← h1]
    simp [Matrix.vecMul, dotProduct, tpow, map_sum, map_prod])
  have h2 := h (show l ∈ invSub Γ n from hl)
  simp only [Pi.basisFun_repr] at h2
  exact h2

end GlobalTheory.ClassFin.RationalInvariants
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PIdxUnitsFiniteExtensionAdicCompletion
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem pIdx_range_of_injective (p : ℕ) {A B : Type} [CommGroup A] [CommGroup B] (j : A →* B)
    (hj : Function.Injective j) : pIdx p j.range = pIdx p (⊤ : Subgroup A) := by
  have h : pows p j.range = (pows p (⊤ : Subgroup A)).map j := by
    ext x
    simp only [pows, Subgroup.mem_map, MonoidHom.mem_range, powMonoidHom_apply, Subgroup.mem_top,
      true_and]
    constructor
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      exact ⟨_, ⟨a, rfl⟩, map_pow _ _ _⟩
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      exact ⟨_, ⟨a, rfl⟩, (map_pow _ _ _).symm⟩
  unfold pIdx
  rw [h, MonoidHom.range_eq_map, Subgroup.relIndex_map_map_of_injective _ _ hj]

theorem pTor_range_of_injective (p : ℕ) {A B : Type} [CommGroup A] [CommGroup B] (j : A →* B)
    (hj : Function.Injective j) : pTor p j.range = pTor p (⊤ : Subgroup A) := by
  unfold pTor
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun x => ⟨j x.1, ⟨x.1, rfl⟩, by rw [← map_pow, x.2.2, map_one]⟩) ⟨?_, ?_⟩)
  · intro x y h
    exact Subtype.ext (hj (congrArg Subtype.val h))
  · rintro ⟨_, ⟨a, rfl⟩, h⟩
    exact ⟨⟨a, trivial, hj (by rw [map_pow, h, map_one])⟩, rfl⟩

theorem pTor_pIdx_subgroup_int (p : ℕ) (hp : 0 < p) (H : Subgroup (Multiplicative ℤ))
    (hH : H ≠ ⊥) : pTor p H = 1 ∧ pIdx p H = p := by
  have htor : ∀ U : Subgroup (Multiplicative ℤ), pTor p U = 1 := by
    intro U
    unfold pTor
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun x y => Subtype.ext ?_⟩, ⟨⟨1, U.one_mem, one_pow _⟩⟩⟩
    rw [(pow_eq_one_iff_left hp.ne').1 x.2.2, (pow_eq_one_iff_left hp.ne').1 y.2.2]
  refine ⟨htor H, ?_⟩
  obtain ⟨d, hd⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top H).1 inferInstance
  have hd1 : d ≠ 1 := by
    rintro rfl
    exact hH (by rw [← hd, Subgroup.zpowers_one_eq_bot])
  have hr : H = (zpowersHom (Multiplicative ℤ) d).range := by
    rw [← hd]; rfl
  have hinj : Function.Injective (zpowersHom (Multiplicative ℤ) d) := by
    intro a b h
    simp only [zpowersHom_apply] at h
    have h2 := congrArg Multiplicative.toAdd h
    simp only [toAdd_zpow, smul_eq_mul] at h2
    have hd0 : d.toAdd ≠ 0 := fun h0 => hd1 (by simpa using h0)
    exact Multiplicative.toAdd.injective (mul_right_cancel₀ hd0 h2)
  rw [hr, pIdx_range_of_injective p _ hinj]
  have h := (pIdx_top_of_fg p (Multiplicative ℤ) hp).2
  have hf : Module.finrank ℤ (Additive (Multiplicative ℤ)) = 1 := by
    rw [(AddEquiv.additiveMultiplicative ℤ).toIntLinearEquiv.finrank_eq]
    exact Module.finrank_self ℤ
  rw [h, htor, hf, pow_one, mul_one]

theorem pIdx_of_ker_eq_range (p : ℕ) (hp : 0 < p) {A B : Type} [CommGroup A] [CommGroup B]
    (j : A →* B) (hj : Function.Injective j) (g : B →* Multiplicative ℤ) (hk : g.ker = j.range)
    (hg : g.range ≠ ⊥) (N : ℕ) (hN : N ≠ 0) (h1 : pTor p (⊤ : Subgroup A) ≠ 0)
    (h2 : pIdx p (⊤ : Subgroup A) = N * pTor p (⊤ : Subgroup A)) :
    pTor p (⊤ : Subgroup B) ≠ 0 ∧ pIdx p (⊤ : Subgroup B) = p * N * pTor p (⊤ : Subgroup B) := by
  obtain ⟨r1, r2⟩ := pTor_pIdx_subgroup_int p hp g.range hg
  have k1 : pTor p g.ker = pTor p (⊤ : Subgroup A) := by
    rw [hk, pTor_range_of_injective p j hj]
  have k2 : pIdx p g.ker = N * pTor p (⊤ : Subgroup A) := by
    rw [hk, pIdx_range_of_injective p j hj, h2]
  obtain ⟨-, a2, a3⟩ := pIdx_pTor_ker_range p B (Multiplicative ℤ) g
    (by rw [k2]; exact mul_ne_zero hN h1) (by rw [k1]; exact h1) (by rw [r2]; exact hp.ne')
    (by rw [r1]; exact one_ne_zero)
  refine ⟨a2, ?_⟩
  rw [k1, k2, r1, r2] at a3
  apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero h1)
  linarith

theorem pIdx_units_finite_extension_adicCompletion (p : ℕ) (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (e : ℕ) (L : Type) [Field L] [Algebra (v.adicCompletion F) L]
    [FiniteDimensional (v.adicCompletion F) L] (hp : 0 < p)
    (he : v.valuation F (p : F) = WithZero.exp (-(e : ℤ))) :
    pTor p (⊤ : Subgroup Lˣ) ≠ 0 ∧ pIdx p (⊤ : Subgroup Lˣ) =
      p * (Ideal.absNorm v.asIdeal ^ e) ^ Module.finrank (v.adicCompletion F) L *
        pTor p (⊤ : Subgroup Lˣ) := by
  letI : Algebra (v.adicCompletionIntegers F) L :=
    ((algebraMap (v.adicCompletion F) L).comp
      (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))).toAlgebra
  haveI : IsScalarTower (v.adicCompletionIntegers F) (v.adicCompletion F) L :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : CharZero (v.adicCompletion F) :=
    charZero_of_injective_algebraMap (algebraMap F (v.adicCompletion F)).injective
  haveI : CharZero L :=
    charZero_of_injective_algebraMap (algebraMap (v.adicCompletion F) L).injective
  have hinjRL : Function.Injective (algebraMap (v.adicCompletionIntegers F) L) :=
    (algebraMap (v.adicCompletion F) L).injective.comp Subtype.val_injective
  haveI : FaithfulSMul (v.adicCompletionIntegers F) L :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hinjRL
  let O : Type := integralClosure (v.adicCompletionIntegers F) L
  haveI : Module.Finite (v.adicCompletionIntegers F) O :=
    IsIntegralClosure.finite (v.adicCompletionIntegers F) (v.adicCompletion F) L O
  haveI : Module.Free (v.adicCompletionIntegers F) O :=
    IsIntegralClosure.module_free (v.adicCompletionIntegers F) (v.adicCompletion F) L O
  have hrank : Module.finrank (v.adicCompletionIntegers F) O =
      Module.finrank (v.adicCompletion F) L :=
    IsIntegralClosure.rank (v.adicCompletionIntegers F) (v.adicCompletion F) L O
  obtain ⟨⟨π₀, -, hπ₀⟩, hval, -⟩ := exists_uniformizer_and_residue_representatives F v
  obtain ⟨hc, hcard⟩ := isAdicComplete_and_card_quotient_adicCompletionIntegers F v
  have hlt : (WithZero.exp (-1) : ℤᵐ⁰) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  let π : v.adicCompletionIntegers F := ⟨algebraMap F (v.adicCompletion F) π₀, by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hπ₀]; exact hlt.le⟩
  have hπ : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1) := hπ₀
  have hπK : (π : v.adicCompletion F) ≠ 0 := by
    intro h
    rw [h, map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  have hπL : algebraMap (v.adicCompletion F) L π ≠ 0 := by
    simpa using hπK
  have hvp : Valued.v (((p : v.adicCompletionIntegers F)) : v.adicCompletion F) =
      WithZero.exp (-(e : ℤ)) := by
    rw [← he, ← hval]; simp
  have hq : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have hπO : algebraMap (v.adicCompletionIntegers F) O π ≠ 0 := by
    intro h
    exact hπL (congrArg Subtype.val h)
  have hcomp := isAdicComplete_span_algebraMap_of_free_finite (v.adicCompletionIntegers F) O π
    (hc π (by rw [hπ]; exact hlt))
  have hc1 : Nat.card (O ⧸ Ideal.span {(p : O)}) =
      (Ideal.absNorm v.asIdeal ^ e) ^ Module.finrank (v.adicCompletion F) L := by
    have := card_quot_span_algebraMap (v.adicCompletionIntegers F) O (p : _)
    rw [map_natCast, hcard _ e hvp, hrank] at this
    exact this
  have hc2 : Nat.card (O ⧸ Ideal.span
      {(p : O) * algebraMap (v.adicCompletionIntegers F) O π}) ≠ 0 := by
    have := card_quot_span_algebraMap (v.adicCompletionIntegers F) O ((p : _) * π)
    rw [map_mul, map_natCast, hcard _ (e + 1) (by
      rw [MulMemClass.coe_mul, map_mul, hvp, hπ, ← WithZero.exp_add]
      congr 1; push_cast; ring)] at this
    rw [this]
    exact pow_ne_zero _ (pow_ne_zero _ hq)
  obtain ⟨u1, u2⟩ := GlobalTheory.T.subgroupPowRelIndex_units_of_isAdicComplete p O _ hp hπO hcomp hc2
  rw [hc1] at u2
  have hN : ∀ x : Lˣ, Valued.v (Algebra.norm (v.adicCompletion F) (x : L)) ≠ 0 := by
    intro x
    rw [Ne, map_eq_zero, Algebra.norm_eq_zero_iff]
    exact x.ne_zero
  let g : Lˣ →* Multiplicative ℤ :=
    { toFun := fun x => Multiplicative.ofAdd
        (WithZero.log (Valued.v (Algebra.norm (v.adicCompletion F) (x : L))))
      map_one' := by simp
      map_mul' := fun x y => by
        rw [Units.val_mul, map_mul, map_mul, WithZero.log_mul (hN x) (hN y), ofAdd_add] }
  have hg : ∀ x : Lˣ, g x = 1 ↔ Valued.v (Algebra.norm (v.adicCompletion F) (x : L)) = 1 := by
    intro x
    change Multiplicative.ofAdd (WithZero.log _) = 1 ↔ _
    rw [ofAdd_eq_one]
    constructor
    · intro h
      rw [← WithZero.exp_log (hN x), h, WithZero.exp_zero]
    · intro h
      rw [h, WithZero.log_one]
  have hmul : ∀ x : Lˣ, Valued.v (Algebra.norm (v.adicCompletion F) (x : L)) *
      Valued.v (Algebra.norm (v.adicCompletion F) ((x⁻¹ : Lˣ) : L)) = 1 := by
    intro x
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  let j : Oˣ →* Lˣ := Units.map ((integralClosure (v.adicCompletionIntegers F) L).val : O →* L)
  refine pIdx_of_ker_eq_range p hp j (Units.map_injective Subtype.val_injective) g ?_ ?_ _
    (pow_ne_zero _ (pow_ne_zero _ hq)) u1 u2
  · ext x
    rw [MonoidHom.mem_ker, hg]
    constructor
    · intro h
      have h' := hmul x
      rw [h, one_mul] at h'
      have i1 := (isIntegral_iff_valued_norm_le_one F v L (x : L)).2 h.le
      have i2 := (isIntegral_iff_valued_norm_le_one F v L ((x⁻¹ : Lˣ) : L)).2 h'.le
      exact ⟨⟨⟨x, i1⟩, ⟨(x⁻¹ : Lˣ), i2⟩, Subtype.ext x.mul_inv, Subtype.ext x.inv_mul⟩,
        Units.ext rfl⟩
    · rintro ⟨u, rfl⟩
      have i1 := (isIntegral_iff_valued_norm_le_one F v L ((j u : Lˣ) : L)).1 (u : O).2
      have i2 := (isIntegral_iff_valued_norm_le_one F v L (((j u)⁻¹ : Lˣ) : L)).1
        ((u⁻¹ : Oˣ) : O).2
      exact eq_one_of_one_le_mul_left i1 i2 (hmul _).ge
  · intro h
    have h1 : g (Units.mk0 _ hπL) = 1 := by
      rw [← Subgroup.mem_bot, ← h]; exact ⟨_, rfl⟩
    rw [hg, Units.val_mk0, Algebra.norm_algebraMap, map_pow, hπ] at h1
    exact (pow_lt_one₀ zero_le' hlt Module.finrank_pos.ne').ne h1

end GlobalTheory.CNorm
end

