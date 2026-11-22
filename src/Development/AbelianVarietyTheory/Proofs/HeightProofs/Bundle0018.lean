import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0048
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0010
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0011

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsIdeleNotMulNorm
section
open NumberField IsDedekindDomain

namespace GlobalTheory.QNorm

theorem exists_adele_finite_component (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) :
    ∃ e : AdeleRing (𝓞 F) F →+* v.adicCompletion F, (∀ x, e x = x.2 v) ∧
      ∀ t : F, e (algebraMap F (AdeleRing (𝓞 F) F) t) = algebraMap F (v.adicCompletion F) t :=
  ⟨{ toFun := fun x => x.2 v
     map_one' := rfl
     map_mul' := fun _ _ => rfl
     map_zero' := rfl
     map_add' := fun _ _ => rfl }, fun _ => rfl, fun _ => rfl⟩

theorem exists_infiniteAdele_real_component (F : Type) [Field F] [NumberField F]
    (σ : F →+* ℝ) :
    ∃ e : InfiniteAdeleRing F →+* ℝ,
      ∀ t : F, e (algebraMap F (InfiniteAdeleRing F) t) = σ t := by
  have hφ : ComplexEmbedding.IsReal (Complex.ofRealHom.comp σ) := by
    rw [ComplexEmbedding.isReal_iff]
    ext x
    simp
  have hw : (InfinitePlace.mk (Complex.ofRealHom.comp σ)).IsReal := ⟨_, hφ, rfl⟩
  refine ⟨(InfinitePlace.Completion.extensionEmbeddingOfIsReal hw).comp
    (Pi.evalRingHom (fun v : InfinitePlace F => v.Completion) _), fun t => ?_⟩
  have he := InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hw
    ((WithAbs.equiv (InfinitePlace.mk (Complex.ofRealHom.comp σ)).1).symm t)
  refine he.trans ?_
  apply Complex.ofReal_injective
  rw [InfinitePlace.embedding_of_isReal_apply, InfinitePlace.embedding_mk_eq_of_isReal hφ]
  simp

open Classical in

noncomputable def adeleOn (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (z : F) : AdeleRing (𝓞 F) F :=
  (algebraMap F (InfiniteAdeleRing F) z,
    (⟨fun v => if v ∈ S then algebraMap F (v.adicCompletion F) z else 1, by
      filter_upwards [S.finite_toSet.compl_mem_cofinite] with v hv
      have hv' : v ∉ S := hv
      simp only [if_neg hv', SetLike.mem_coe]
      exact one_mem _⟩ : FiniteAdeleRing (𝓞 F) F))

theorem adeleOn_snd_of_mem (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (z : F) {v : HeightOneSpectrum (𝓞 F)} (hv : v ∈ S) :
    (adeleOn F S z).2 v = algebraMap F (v.adicCompletion F) z := if_pos hv

theorem adeleOn_snd_of_notMem (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (z : F) {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) :
    (adeleOn F S z).2 v = 1 := if_neg hv

theorem adeleOn_mul_inv (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) {z : F} (hz : z ≠ 0) :
    adeleOn F S z * adeleOn F S z⁻¹ = 1 := by
  refine Prod.ext ?_ (FiniteAdeleRing.ext F fun v => ?_)
  · change algebraMap F (InfiniteAdeleRing F) z * algebraMap F (InfiniteAdeleRing F) z⁻¹ = 1
    rw [← map_mul, mul_inv_cancel₀ hz, map_one]
  · change (adeleOn F S z).2 v * (adeleOn F S z⁻¹).2 v = 1
    by_cases hv : v ∈ S
    · rw [adeleOn_snd_of_mem F S _ hv, adeleOn_snd_of_mem F S _ hv, ← map_mul,
        mul_inv_cancel₀ hz, map_one]
    · rw [adeleOn_snd_of_notMem F S _ hv, adeleOn_snd_of_notMem F S _ hv, mul_one]

theorem div_mem_normSub {F L : Type} [Field F] [Field L] (φ : F →+* L) (δ : F) (z t : Fˣ)
    (a b : L) (h : φ (z : F) = φ (t : F) * (a ^ 2 - φ δ * b ^ 2)) : z / t ∈ normSub φ δ := by
  refine ⟨a, b, ?_⟩
  have ht : φ (t : F) ≠ 0 := by simp
  rw [Units.val_div_eq_div_val, map_div₀, h]
  field_simp

theorem exists_idele_not_mul_norm : ∀ (F : Type) [Field F] [NumberField F] (δ : F), ¬ IsSquare δ → ∃ a : (AdeleRing (𝓞 F) F)ˣ, ∀ (t : F) (x y : AdeleRing (𝓞 F) F), (a : AdeleRing (𝓞 F) F) ≠ algebraMap F (AdeleRing (𝓞 F) F) t * (x ^ 2 - algebraMap F (AdeleRing (𝓞 F) F) δ * y ^ 2) := by
  intro F _ _ δ hsq
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    exact hsq IsSquare.zero
  obtain ⟨S, hS, hδ, hadj⟩ := GlobalTheory.T.exists_admissible_localNorm_mem_sUnits_sup_globalNorm F (Units.mk0 δ hδ0) hsq
  have hne := sUnits_sup_locNorm_ne_top F (Units.mk0 δ hδ0) S hS hδ hsq
  simp only [Units.val_mk0] at hadj hne
  obtain ⟨z, hz⟩ : ∃ z : Fˣ, z ∉ sUnits F S ⊔ locNorm F δ S := by
    by_contra hcon
    push Not at hcon
    exact hne (Subgroup.eq_top_iff' _ |>.2 hcon)
  refine ⟨Units.mkOfMulEqOne _ _ (adeleOn_mul_inv F S z.ne_zero), fun t x y h => hz ?_⟩
  replace h : adeleOn F S z = algebraMap F (AdeleRing (𝓞 F) F) t *
      (x ^ 2 - algebraMap F (AdeleRing (𝓞 F) F) δ * y ^ 2) := h
  have ht : t ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_mul] at h
    have h1 : algebraMap F (InfiniteAdeleRing F) z = 0 := congrArg Prod.fst h
    exact z.ne_zero ((map_eq_zero _).1 h1)
  have hfin : ∀ v : HeightOneSpectrum (𝓞 F), ∃ a b : v.adicCompletion F,
      (adeleOn F S z).2 v = algebraMap F (v.adicCompletion F) t *
        (a ^ 2 - algebraMap F (v.adicCompletion F) δ * b ^ 2) := by
    intro v
    obtain ⟨e, he, he'⟩ := exists_adele_finite_component F v
    refine ⟨e x, e y, ?_⟩
    rw [← he, h, map_mul, map_sub, map_mul, map_pow, map_pow, he', he']
  have h1 : Units.mk0 t ht ∈ sUnits F S ⊔ locNorm F δ S := by
    refine sup_le_sup_left (normSub_id_le_locNorm F δ S) _ (hadj _ fun v hv => ?_)
    obtain ⟨a, b, hab⟩ := hfin v
    rw [adeleOn_snd_of_notMem F S _ hv] at hab
    have h2 := div_mem_normSub (algebraMap F (v.adicCompletion F)) δ 1 (Units.mk0 t ht) a b
      (by simpa using hab)
    rwa [one_div, inv_mem_iff] at h2
  have h2 : z / Units.mk0 t ht ∈ locNorm F δ S := by
    refine ⟨Subgroup.mem_iInf.2 fun v => Subgroup.mem_iInf.2 fun hv => ?_,
      Subgroup.mem_iInf.2 fun σ => ?_⟩
    · obtain ⟨a, b, hab⟩ := hfin v
      rw [adeleOn_snd_of_mem F S _ hv] at hab
      exact div_mem_normSub _ δ z (Units.mk0 t ht) a b hab
    · obtain ⟨e, he⟩ := exists_infiniteAdele_real_component F σ
      refine div_mem_normSub σ δ z (Units.mk0 t ht) (e x.1) (e y.1) ?_
      have h3 : algebraMap F (InfiniteAdeleRing F) z = algebraMap F (InfiniteAdeleRing F) t *
          (x.1 ^ 2 - algebraMap F (InfiniteAdeleRing F) δ * y.1 ^ 2) := congrArg Prod.fst h
      have h4 := congrArg e h3
      rwa [map_mul, map_sub, map_mul, map_pow, map_pow, he, he, he] at h4
  have h3 := mul_mem (Subgroup.mem_sup_right (S := sUnits F S) h2) h1
  rwa [div_mul_cancel] at h3

end GlobalTheory.QNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.UnitNormFormAtOddPlace
section
open NumberField IsDedekindDomain IsLocalRing Polynomial

namespace GlobalTheory.QNorm

theorem exists_eq_sq_sub_mul_sq_finite {k : Type} [Field k] [Finite k] (h2 : (2 : k) ≠ 0)
    {δ : k} (hδ : δ ≠ 0) (u : k) : ∃ a b : k, u = a ^ 2 - δ * b ^ 2 := by
  classical
  have := Fintype.ofFinite k
  have hc : ringChar k ≠ 2 := by
    intro h
    apply h2
    have := ringChar.Nat.cast_ringChar (R := k)
    rw [h] at this
    exact_mod_cast this
  have hodd := FiniteField.odd_card_of_char_ne_two hc
  have hf : (X ^ 2 : k[X]).degree = 2 := by simp
  have hg : (-(C δ) * X ^ 2 - C u : k[X]).degree = 2 := by
    have h1 : (-(C δ) * X ^ 2 : k[X]).degree = 2 := by simp [hδ]
    rw [degree_sub_eq_left_of_degree_lt (by rw [h1]; exact degree_C_le.trans_lt (by norm_num)), h1]
  obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic hf hg hodd
  refine ⟨a, b, ?_⟩
  simp at hab
  linear_combination -hab

theorem exists_integral_sq_sub_mul_sq_of_unit : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (δ u : v.adicCompletion F), Valued.v (2 : v.adicCompletion F) = 1 → Valued.v δ = 1 → Valued.v u = 1 → ∃ x ∈ v.adicCompletionIntegers F, ∃ y ∈ v.adicCompletionIntegers F, u = x ^ 2 - δ * y ^ 2 := by
  intro F _ _ v δ u h2 hδ hu
  set O := v.adicCompletionIntegers F with hO
  have hmem : ∀ x : v.adicCompletion F, x ∈ O ↔ Valued.v x ≤ 1 := by
    intro x; rw [hO]; exact HeightOneSpectrum.mem_adicCompletionIntegers ..
  have hval1 : ∀ z : O, IsUnit z → Valued.v (z : v.adicCompletion F) = 1 := by
    intro z hz
    obtain ⟨w, hw⟩ := hz.exists_right_inv
    have h1 : Valued.v (z : v.adicCompletion F) * Valued.v (w : v.adicCompletion F) = 1 := by
      rw [← map_mul, ← Subring.coe_mul, hw]
      simp
    have hz1 := (hmem _).1 z.2
    have hw1 := (hmem _).1 w.2
    refine le_antisymm hz1 ?_
    calc (1 : WithZero (Multiplicative ℤ)) = Valued.v (z : v.adicCompletion F) * Valued.v (w : v.adicCompletion F) := h1.symm
      _ ≤ Valued.v (z : v.adicCompletion F) * 1 := mul_le_mul_right hw1 _
      _ = _ := mul_one _
  have : Finite (IsLocalRing.ResidueField O) := SelfDualGenus.finite_residueField_adicCompletionIntegers v
  have hres_ne : ∀ z : O, Valued.v (z : v.adicCompletion F) = 1 → IsLocalRing.residue O z ≠ 0 := by
    intro z hz
    rw [IsLocalRing.residue_ne_zero_iff_isUnit]
    have hz0 : (z : v.adicCompletion F) ≠ 0 := by
      intro h; rw [h, map_zero] at hz; exact zero_ne_one hz
    refine IsUnit.of_mul_eq_one (a := z) ⟨(z : v.adicCompletion F)⁻¹, (hmem _).2 (by rw [map_inv₀, hz, inv_one])⟩ ?_
    exact Subtype.ext (by simp [hz0])
  let uO : O := ⟨u, (hmem _).2 hu.le⟩
  let δO : O := ⟨δ, (hmem _).2 hδ.le⟩
  have hc2 : ((2 : O) : v.adicCompletion F) = 2 := map_ofNat O.subtype 2
  have h2O : IsLocalRing.residue O (2 : O) ≠ 0 := hres_ne 2 (by rw [hc2]; exact h2)
  have hk2 : (2 : IsLocalRing.ResidueField O) ≠ 0 := by rwa [map_ofNat] at h2O
  obtain ⟨a, b, hab⟩ := exists_eq_sq_sub_mul_sq_finite hk2 (hres_ne δO hδ) (IsLocalRing.residue O uO)
  obtain ⟨a', rfl⟩ := IsLocalRing.residue_surjective a
  obtain ⟨b', rfl⟩ := IsLocalRing.residue_surjective b
  let N : O := a' ^ 2 - δO * b' ^ 2
  have hresN : IsLocalRing.residue O N = IsLocalRing.residue O uO := by
    simp only [N, map_sub, map_mul, map_pow]; exact hab.symm
  have hvN : Valued.v (N : v.adicCompletion F) = 1 :=
    hval1 N ((IsLocalRing.residue_ne_zero_iff_isUnit N).1 (hresN ▸ hres_ne uO hu))
  have hN0 : (N : v.adicCompletion F) ≠ 0 := by
    intro h; rw [h, map_zero] at hvN; exact zero_ne_one hvN
  have hz1 : Valued.v (u / (N : v.adicCompletion F)) = 1 := by rw [map_div₀, hu, hvN, div_one]
  let z : O := ⟨u / (N : v.adicCompletion F), (hmem _).2 hz1.le⟩
  have hzN : z * N = uO := Subtype.ext (by
    change u / (N : v.adicCompletion F) * (N : v.adicCompletion F) = u
    field_simp)
  have hresz : IsLocalRing.residue O z = 1 := by
    have h := congrArg (IsLocalRing.residue O) hzN
    rw [map_mul, hresN] at h
    have hne : IsLocalRing.residue O uO ≠ 0 := hres_ne uO hu
    calc IsLocalRing.residue O z = IsLocalRing.residue O z * IsLocalRing.residue O uO / IsLocalRing.residue O uO := by
          field_simp
      _ = 1 := by rw [h, div_self hne]
  obtain ⟨s, hs⟩ := isSquare_of_isSquare_residue_odd F v h2 z hz1 ⟨1, by rw [hresz, mul_one]⟩
  have hvs : Valued.v s ≤ 1 := by
    by_contra hc
    push Not at hc
    have : Valued.v s ≤ Valued.v s * Valued.v s := by
      calc Valued.v s = Valued.v s * 1 := (mul_one _).symm
        _ ≤ Valued.v s * Valued.v s := mul_le_mul_right hc.le _
    rw [← map_mul, ← hs, hz1] at this
    exact absurd (hc.trans_le this) (lt_irrefl _)
  have ha' := (hmem _).1 a'.2
  have hb' := (hmem _).1 b'.2
  refine ⟨s * a', (hmem _).2 ?_, s * b', (hmem _).2 ?_, ?_⟩
  · rw [map_mul]; exact mul_le_one' hvs ha'
  · rw [map_mul]; exact mul_le_one' hvs hb'
  · have hNK : (N : v.adicCompletion F) = (a' : v.adicCompletion F) ^ 2 - δ * (b' : v.adicCompletion F) ^ 2 := by
      simp [N, δO]
    have hzK : (z : v.adicCompletion F) = u / (N : v.adicCompletion F) := rfl
    calc u = (z : v.adicCompletion F) * (N : v.adicCompletion F) := by rw [hzK]; field_simp
      _ = _ := by rw [hs, hNK]; ring

end GlobalTheory.QNorm
end

