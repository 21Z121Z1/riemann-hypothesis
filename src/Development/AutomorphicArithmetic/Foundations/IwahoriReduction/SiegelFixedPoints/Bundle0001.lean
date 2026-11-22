import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.IsThBIff
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0021
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0279
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0102

-- bundled from Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.DlgalMapMul
section
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

private theorem hahnSeries_map_mul {Ω : Type} [Field Ω] [Algebra ℚ Ω] (s : Ω ≃ₐ[ℚ] Ω) (x y : HahnSeries ℚ Ω) :
    HahnSeries.map (x * y) (s : Ω →+* Ω) = HahnSeries.map x (s : Ω →+* Ω) * HahnSeries.map y (s : Ω →+* Ω) := by
  have e : ∀ z : HahnSeries ℚ Ω, HahnSeries.map z ((s : Ω →+* Ω) : Ω →ₙ+* Ω) = HahnSeries.map z (s : Ω →+* Ω) := by
    intro z
    ext r
    simp [HahnSeries.map_coeff]
    rfl
  rw [← e, ← e, ← e]
  exact HahnSeries.map_mul _

private theorem theta_hahnSeries_map_comm {Ω : Type} [Field Ω] [Algebra ℚ Ω] (s : Ω ≃ₐ[ℚ] Ω) (q : ℚ) (x : HahnSeries ℚ Ω) :
    theta q (HahnSeries.map x (s : Ω →+* Ω)) = HahnSeries.map (theta q x) (s : Ω →+* Ω) := by
  ext r
  show algebraMap ℚ Ω (q * r) * (HahnSeries.map x (s : Ω →+* Ω)).coeff r = (s : Ω →+* Ω) (algebraMap ℚ Ω (q * r) * x.coeff r)
  rw [HahnSeries.map_coeff, map_mul (s : Ω →+* Ω),
    show (s : Ω →+* Ω) (algebraMap ℚ Ω (q * r)) = algebraMap ℚ Ω (q * r) from s.commutes _]

private theorem hahnSeries_map_sub {Ω : Type} [Field Ω] [Algebra ℚ Ω] (s : Ω ≃ₐ[ℚ] Ω) (x y : HahnSeries ℚ Ω) :
    HahnSeries.map (x - y) (s : Ω →+* Ω) = HahnSeries.map x (s : Ω →+* Ω) - HahnSeries.map y (s : Ω →+* Ω) := by
  ext r
  simp [HahnSeries.map_coeff]

private theorem prim_hahnSeries_map_of_prim_comap {Ω : Type} [Field Ω] [Algebra ℚ Ω] (A A' : ValuationSubring Ω) (s : Ω ≃ₐ[ℚ] Ω)
    (hA : ∀ x, x ∈ A' ↔ s x ∈ A) (x : HahnSeries ℚ Ω) (hx : Prim A' x) :
    Prim A (HahnSeries.map x (s : Ω →+* Ω)) := by
  obtain ⟨h1, r, hr0, hr⟩ := hx
  refine ⟨fun t => ?_, r, ?_, ?_⟩
  · rw [HahnSeries.map_coeff]
    exact (hA _).1 (h1 t)
  · rw [HahnSeries.map_coeff]
    exact (map_ne_zero _).2 hr0
  · rw [HahnSeries.map_coeff, ← map_inv₀]
    exact (hA _).1 hr

set_option maxHeartbeats 800000 in
theorem UpperTheory.Kd.L.dlgal :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [CharZero Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (A A' : ValuationSubring Ω) (s : Ω ≃ₐ[ℚ] Ω), (∀ x, x ∈ A' ↔ s x ∈ A) → ∀ (n : ℕ) (a : ℚ) (f : X.K) (φ : HahnSeries ℚ Ω), IsDl X A' l n a f φ → IsDl X A l n a (X.gal s f) (HahnSeries.map φ (s : Ω →+* Ω)) := by
  intro Ω _ _ _ _ ε X l _ A A' s hA n q f φ h
  obtain ⟨hφ, a, b, κ, hκ, hfb, ha, hb, hc⟩ := h
  have hM : ∀ g : X.K, X.exp (X.gal s g) = HahnSeries.map (X.exp g) (s : Ω →+* Ω) := by
    intro g
    ext r
    rw [HahnSeries.map_coeff, X.gal_exp]
    rfl
  have hsm : ∀ (c : Ω) (y : HahnSeries ℚ Ω) (r : ℚ),
      (algebraMap Ω (HahnSeries ℚ Ω) c * y).coeff r = c * y.coeff r := by
    intro c y r
    rw [HahnSeries.algebraMap_apply']
    simp [HahnSeries.C_mul_eq_smul]
  have hsκ : s κ ≠ 0 := (map_ne_zero _).2 hκ
  have hc0 : algebraMap Ω X.K (s κ) ≠ 0 := (map_ne_zero _).2 hsκ
  have hexpa : X.exp ((algebraMap Ω X.K (s κ))⁻¹ * X.gal s (algebraMap Ω X.K κ * a)) =
      HahnSeries.map (X.exp a) (s : Ω →+* Ω) := by
    rw [← map_inv₀, map_mul, AlgHom.commutes, hM, map_mul, AlgHom.commutes]
    ext r
    rw [hsm, HahnSeries.map_coeff, HahnSeries.map_coeff, hsm, map_mul, ← mul_assoc,
      show (s κ)⁻¹ * (s : Ω →+* Ω) κ = 1 from inv_mul_cancel₀ hsκ, one_mul]
  refine ⟨fun r => ?_, (algebraMap Ω X.K (s κ))⁻¹ * X.gal s (algebraMap Ω X.K κ * a), X.gal s b, s κ, hsκ,
    ?_, ?_, ?_, fun r => ?_⟩
  · rw [HahnSeries.map_coeff]
    exact (hA _).1 (hφ r)
  · rw [← map_mul, hfb, ← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
  · rw [hexpa]
    exact prim_hahnSeries_map_of_prim_comap A A' s hA _ ha
  · rw [hM]
    exact prim_hahnSeries_map_of_prim_comap A A' s hA _ hb
  · rw [hexpa, hM, theta_hahnSeries_map_comm, theta_hahnSeries_map_comm, ← hahnSeries_map_mul, ← hahnSeries_map_mul, ← hahnSeries_map_mul, ← hahnSeries_map_mul, ← hahnSeries_map_sub,
      HahnSeries.map_coeff, HahnSeries.map_coeff]
    obtain ⟨z, hz, e⟩ := hc r
    refine ⟨s z, (hA z).1 hz, ?_⟩
    rw [← map_sub, e, map_mul]
    simp
end

-- bundled from Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.DvdOfModEq
section
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

namespace UpperTheory.Kd.L

section Series

variable {K : Type} [Field K] [CharZero K]

end Series

section Root

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [CharZero Ω]

end Root

end UpperTheory.Kd.L

private theorem eps_eOm_eq_cexp {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [CharZero Ω] (ε : Ω →+* ℂ) (x : ℚ) :
    ε (eOm ε x) = Complex.exp (2 * ↑Real.pi * Complex.I * ↑x) := by
  unfold eOm
  apply Function.invFun_eq
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : NeZero ((x.den : ℕ) : Ω) := ⟨by exact_mod_cast x.den_nz⟩
  haveI : NeZero x.den := ⟨x.den_nz⟩
  obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω x.den
  have h2 := hξ.map_of_injective ε.injective
  have h1 : Complex.exp (2 * ↑Real.pi * Complex.I * ↑x) ^ x.den = 1 := by
    rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
    refine ⟨x.num, ?_⟩
    have hx : (x : ℂ) * (x.den : ℂ) = (x.num : ℂ) := by exact_mod_cast Rat.mul_den_eq_num x
    linear_combination (2 * ↑Real.pi * Complex.I) * hx
  obtain ⟨i, -, hi⟩ := h2.eq_pow_of_pow_eq_one h1
  exact ⟨ξ ^ i, by rw [map_pow, hi]⟩

private theorem eOm_inv_mul_pow_eq_eOm_inv {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [CharZero Ω] (ε : Ω →+* ℂ) (D M : ℕ) (hD : 0 < D) :
    eOm ε (1 / ((D * M : ℕ) : ℚ)) ^ D = eOm ε (1 / (M : ℚ)) := by
  apply ε.injective
  rw [map_pow, eps_eOm_eq_cexp, eps_eOm_eq_cexp, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  have : (D:ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  by_cases hM : (M:ℂ) = 0
  · simp [hM]
  · field_simp

private theorem eisF_mul_scale_eq_ite_dvd {K : Type*} [Field K] (D M : ℕ) (ζ' ζ : K) (hζ : ζ' ^ D = ζ) (A a : ℤ) (hD : 0 < D) (hA : ¬ (M:ℤ) ∣ A) (n : ℕ) :
    eisF 1 (D * M) ζ' ((D:ℤ) * A) ((D:ℤ) * a) n = if D ∣ n then eisF 1 M ζ A a (n / D) else 0 := by
  have hD' : (D:ℤ) ≠ 0 := by exact_mod_cast hD.ne'
  have key : ∀ x : ℤ, x ≡ (D:ℤ) * A [ZMOD ((D * M : ℕ) : ℤ)] → (D:ℤ) ∣ x := by
    intro x hx
    have h := hx.symm.dvd
    push_cast at h
    have h2 : (D:ℤ) ∣ x - D * A := (Dvd.intro _ rfl).trans h
    have h3 : (D:ℤ) ∣ D * A := Dvd.intro _ rfl
    simpa using h2.add h3
  have cong : ∀ y : ℤ, (((D:ℤ) * y) ≡ (D:ℤ) * A [ZMOD ((D * M : ℕ) : ℤ)] ↔ y ≡ A [ZMOD M]) := by
    intro y
    push_cast
    exact ⟨Int.ModEq.mul_left_cancel' hD', fun h => Int.ModEq.mul_left' h⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [eisF, const0, if_true, dvd_zero, Nat.zero_div]
    have h1 : ¬ ((D * M : ℕ) : ℤ) ∣ (D:ℤ) * A := by
      push_cast
      rwa [mul_dvd_mul_iff_left hD']
    rw [if_neg h1, if_neg hA]
    unfold frc
    push_cast
    rw [Int.mul_emod_mul_of_pos _ _ (by exact_mod_cast hD)]
    push_cast
    have : (D:ℚ) ≠ 0 := by exact_mod_cast hD.ne'
    field_simp
  · simp only [eisF, coefPos, hn.ne', if_false, Nat.sub_self, pow_zero, one_mul]
    by_cases hDn : D ∣ n
    · rw [if_pos hDn]
      obtain ⟨k, rfl⟩ := hDn
      have hk : k ≠ 0 := by
        rintro rfl
        simp at hn
      rw [Nat.mul_div_cancel_left k hD, if_neg hk]
      have hsub : k.divisors ⊆ (D * k).divisors :=
        Nat.divisors_subset_of_dvd (Nat.mul_ne_zero hD.ne' hk) (dvd_mul_left k D)
      have hpow : ∀ t : ℤ, ζ' ^ ((D:ℤ) * t) = ζ ^ t := by
        intro t
        rw [zpow_mul, zpow_natCast, hζ]
      have hout : ∀ x : ℕ, x ∣ D * k → (D:ℤ) ∣ ((D * k / x : ℕ) : ℤ) → x ∣ k := by
        intro x hx hdx
        rw [Int.natCast_dvd_natCast] at hdx
        obtain ⟨e, he⟩ := hdx
        have h1 : D * k / x * x = D * k := Nat.div_mul_cancel hx
        rw [he, mul_assoc] at h1
        exact ⟨e, by rw [mul_comm x e]; exact (Nat.eq_of_mul_eq_mul_left hD h1).symm⟩
      rw [← Finset.sum_subset hsub]
      · apply Finset.sum_congr rfl
        intro x hx
        have hxk : x ∣ k := Nat.dvd_of_mem_divisors hx
        have e1 : ((D * k / x : ℕ) : ℤ) = (D:ℤ) * ((k / x : ℕ) : ℤ) := by
          rw [Nat.mul_div_assoc D hxk]
          push_cast
          ring
        simp only [e1, neg_mul_eq_mul_neg, cong, mul_assoc, hpow]
      · intro x hx hxn
        have hx' : x ∣ D * k := Nat.dvd_of_mem_divisors hx
        have hnot : ¬ x ∣ k := fun h => hxn (Nat.mem_divisors.mpr ⟨h, hk⟩)
        rw [if_neg, if_neg, sub_zero]
        · intro h
          exact hnot (hout x hx' (by simpa using key _ h))
        · intro h
          exact hnot (hout x hx' (key _ h))
    · rw [if_neg hDn]
      apply Finset.sum_eq_zero
      intro x hx
      have hx' : x ∣ n := Nat.dvd_of_mem_divisors hx
      have hout : (D:ℤ) ∣ ((n / x : ℕ) : ℤ) → False := by
        intro hdx
        rw [Int.natCast_dvd_natCast] at hdx
        exact hDn (hdx.trans (Nat.div_dvd_of_dvd hx'))
      rw [if_neg, if_neg, sub_zero]
      · intro h
        exact hout (by simpa using key _ h)
      · intro h
        exact hout (key _ h)

private theorem smF_mul_scale_eq_ite_dvd {K : Type*} [Field K] (c : ℤ) (D M : ℕ) (ζ' ζ : K) (hζ : ζ' ^ D = ζ) (A a : ℤ) (hD : 0 < D) (hA : ¬ (M:ℤ) ∣ A) (hcA : ¬ (M:ℤ) ∣ c * A) (n : ℕ) :
    smF c 1 (D * M) ζ' ((D:ℤ) * A) ((D:ℤ) * a) n = if D ∣ n then smF c 1 M ζ A a (n / D) else 0 := by
  unfold smF
  rw [mul_left_comm c (D:ℤ) A, mul_left_comm c (D:ℤ) a, eisF_mul_scale_eq_ite_dvd D M ζ' ζ hζ A a hD hA, eisF_mul_scale_eq_ite_dvd D M ζ' ζ hζ (c * A) (c * a) hD hcA]
  split_ifs <;> simp

private theorem cmul_dilate_eq_ite_dvd {K : Type*} [Field K] (D : ℕ) (hD : 0 < D) (f g f' g' : ℕ → K) (hf : ∀ n, f' n = if D ∣ n then f (n / D) else 0) (hg : ∀ n, g' n = if D ∣ n then g (n / D) else 0) (N : ℕ) :
    cmul f' g' N = if D ∣ N then cmul f g (N / D) else 0 := by
  unfold cmul
  by_cases hN : D ∣ N
  · rw [if_pos hN]
    obtain ⟨K0, rfl⟩ := hN
    rw [Nat.mul_div_cancel_left K0 hD]
    have hsub : (Finset.range (K0 + 1)).image (fun k => D * k) ⊆ Finset.range (D * K0 + 1) := by
      intro i hi
      simp only [Finset.mem_image, Finset.mem_range] at hi ⊢
      obtain ⟨k, hk, rfl⟩ := hi
      have := Nat.mul_le_mul_left D (Nat.lt_succ_iff.mp hk)
      omega
    rw [← Finset.sum_subset hsub, Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro k hk
      have e : D * K0 - D * k = D * (K0 - k) := (Nat.mul_sub D K0 k).symm
      rw [hf, hg, if_pos (dvd_mul_right D k), e, if_pos (dvd_mul_right _ _), Nat.mul_div_cancel_left _ hD, Nat.mul_div_cancel_left _ hD]
    · intro x _ y _ hxy
      exact Nat.eq_of_mul_eq_mul_left hD hxy
    · intro i hi hni
      rw [hf]
      split_ifs with hDi
      · exfalso
        obtain ⟨k, rfl⟩ := hDi
        apply hni
        simp only [Finset.mem_image, Finset.mem_range] at hi ⊢
        refine ⟨k, ?_, rfl⟩
        have h1 : D * k ≤ D * K0 := by omega
        have := Nat.le_of_mul_le_mul_left h1 hD
        omega
      · simp
  · rw [if_neg hN]
    apply Finset.sum_eq_zero
    intro i hi
    have hi' : i ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [hf, hg]
    split_ifs with h1 h2
    · exfalso
      apply hN
      have := Nat.dvd_add h1 h2
      rwa [Nat.add_sub_cancel' hi'] at this
    · simp
    · simp
    · simp

private theorem coefQ_eq_of_mul_eq_nat {Ω : Type} [Field Ω] (L : ℕ) (hL : 0 < L) (F : ℕ → Ω) (r : ℚ) (N : ℕ) (h : r * L = N) :
    coefQ L F r = F N := by
  unfold coefQ
  have hL' : (0:ℚ) < L := by exact_mod_cast hL
  have hr : 0 ≤ r := by
    have h0 : 0 ≤ r * L := by
      rw [h]
      exact Nat.cast_nonneg _
    exact (mul_nonneg_iff_of_pos_right hL').mp h0
  rw [if_pos ⟨hr, by rw [h]; simp⟩, h]
  simp

private theorem coefQ_eq_zero_of_not_nat {Ω : Type} [Field Ω] (L : ℕ) (F : ℕ → Ω) (r : ℚ) (h : ¬ ∃ N : ℕ, r * L = N) :
    coefQ L F r = 0 := by
  unfold coefQ
  rw [if_neg]
  rintro ⟨hr, hd⟩
  apply h
  have h1 : ((r * L).num : ℚ) = r * L := Rat.coe_int_num_of_den_eq_one hd
  have h2 : 0 ≤ (r * L).num := Rat.num_nonneg.mpr (mul_nonneg hr (Nat.cast_nonneg _))
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le h2
  refine ⟨m, ?_⟩
  rw [← h1, hm]
  simp

theorem UpperTheory.Kd.L.resc :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [CharZero Ω] (ε : Ω →+* ℂ) (D M c d L : ℕ) (A a B b : ℤ), 0 < D → 0 < M → 0 < L → ¬ (M : ℤ) ∣ A → ¬ (M : ℤ) ∣ c * A → ¬ (M : ℤ) ∣ B → ¬ (M : ℤ) ∣ d * B → ∀ r : ℚ, coefQ L (cmul (smF c 1 (D * M) (eOm ε (1 / ((D * M : ℕ) : ℚ))) (D * A) (D * a)) (smF d 1 (D * M) (eOm ε (1 / ((D * M : ℕ) : ℚ))) (D * B) (D * b))) r = coefQ L (cmul (smF c 1 M (eOm ε (1 / (M : ℚ))) A a) (smF d 1 M (eOm ε (1 / (M : ℚ))) B b)) (r / D) := by
  intro Ω _ _ _ _ ε D M c d L A a B b hD hM hL hA hcA hB hdB r
  have hζ := eOm_inv_mul_pow_eq_eOm_inv ε D M hD
  have h1 := smF_mul_scale_eq_ite_dvd (c:ℤ) D M _ _ hζ A a hD hA hcA
  have h2 := smF_mul_scale_eq_ite_dvd (d:ℤ) D M _ _ hζ B b hD hB hdB
  have hc := cmul_dilate_eq_ite_dvd D hD _ _ _ _ h1 h2
  by_cases h : ∃ N : ℕ, r * L = N
  · obtain ⟨N, hN⟩ := h
    rw [coefQ_eq_of_mul_eq_nat L hL _ r N hN, hc]
    by_cases hDN : D ∣ N
    · obtain ⟨K0, rfl⟩ := hDN
      rw [if_pos (dvd_mul_right _ _), Nat.mul_div_cancel_left _ hD]
      refine (coefQ_eq_of_mul_eq_nat L hL _ _ K0 ?_).symm
      have hD' : (D:ℚ) ≠ 0 := by exact_mod_cast hD.ne'
      rw [div_mul_eq_mul_div, hN]
      push_cast
      field_simp
    · rw [if_neg hDN, coefQ_eq_zero_of_not_nat]
      rintro ⟨m, hm⟩
      apply hDN
      refine ⟨m, ?_⟩
      have hD' : (D:ℚ) ≠ 0 := by exact_mod_cast hD.ne'
      have e : (N:ℚ) = D * m := by
        rw [← hN, ← hm]
        field_simp
      exact_mod_cast e
  · rw [coefQ_eq_zero_of_not_nat L _ r h, coefQ_eq_zero_of_not_nat]
    rintro ⟨m, hm⟩
    apply h
    refine ⟨D * m, ?_⟩
    have hD' : (D:ℚ) ≠ 0 := by exact_mod_cast hD.ne'
    push_cast
    rw [← hm]
    field_simp
end

-- bundled from Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.IsDlDivM
section
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

private theorem exists_pow_eq {Ω : Type} [Field Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω)
    (hl : ((l : ℕ) : Ω) ∈ A.nonunits) (M : ℕ) (hM : 0 < M) : ∃ k : ℕ, ∃ u ∈ A, (l : Ω) ^ k = (M : Ω) * u := by
  have hp : l.Prime := Fact.out
  obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hM.ne' l hp.ne_one
  have hc : IsCoprime (l : ℤ) (m : ℤ) := Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hm)
  have hc' : IsCoprime (l : A) (m : A) := by simpa using hc.map (Int.castRingHom A)
  have hlu : ¬ IsUnit (l : A) := by
    have h1 : ((l : A) : Ω) ∈ A.nonunits := by simpa using hl
    have := (ValuationSubring.coe_mem_nonunits_iff).1 h1
    exact (IsLocalRing.mem_maximalIdeal _).1 this
  have hmu : IsUnit (m : A) := by
    obtain ⟨a, b, e⟩ := hc'
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add (e ▸ isUnit_one) with h | h
    · exact absurd (isUnit_of_mul_isUnit_right h) hlu
    · exact isUnit_of_mul_isUnit_right h
  obtain ⟨u, hu⟩ := hmu.exists_right_inv
  refine ⟨k, (u : Ω), u.2, ?_⟩
  have e : (m : Ω) * (u : Ω) = 1 := by simpa using congrArg (fun x : A => (x : Ω)) hu
  push_cast
  rw [mul_assoc, e, mul_one]

private theorem isDl_divM {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [CharZero Ω] {ε : Ω →+* ℂ}
    (X : Tower Ω ε) (A : ValuationSubring Ω) (l n k M : ℕ) (hM : 0 < M) (u : Ω) (hu : u ∈ A)
    (hk : (l : Ω) ^ k = (M : Ω) * u) (F : X.K) (ψ : HahnSeries ℚ Ω) (hψ : ∀ r, ψ.coeff r ∈ A)
    (h : IsDl X A l (n + k) (M : ℚ) F (HahnSeries.C (M : Ω) * ψ)) : IsDl X A l n 1 F ψ := by
  obtain ⟨-, a, c, κ, hκ, he, ha, hc, hcg⟩ := h
  refine ⟨hψ, a, c, κ, hκ, he, ha, hc, fun r => ?_⟩
  obtain ⟨z, hz, e⟩ := hcg r
  refine ⟨u * z, mul_mem hu hz, ?_⟩
  have hm : algebraMap ℚ Ω (M : ℚ) = (M : Ω) := map_natCast _ _
  rw [NrmT.theta_eq_C_mul _ (X.exp a), NrmT.theta_eq_C_mul _ (X.exp c), hm] at e
  have hM0 : (M : Ω) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
  have e2 : HahnSeries.C (M : Ω) * ψ * X.exp a * X.exp c =
      HahnSeries.C (M : Ω) * (ψ * X.exp a * X.exp c) := by ring
  have e3 : HahnSeries.C (M : Ω) * theta 1 (X.exp a) * X.exp c -
      X.exp a * (HahnSeries.C (M : Ω) * theta 1 (X.exp c)) =
      HahnSeries.C (M : Ω) * (theta 1 (X.exp a) * X.exp c - X.exp a * theta 1 (X.exp c)) := by ring
  rw [e2, e3, HahnSeries.C_mul_eq_smul, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, HahnSeries.coeff_smul,
    smul_eq_mul, smul_eq_mul, ← mul_sub, pow_add, hk] at e
  apply mul_left_cancel₀ hM0
  rw [e]; ring

private theorem isDl_weak {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}
    (X : Tower Ω ε) (A : ValuationSubring Ω) (l n k : ℕ) (s : ℚ) (F : X.K) (φ : HahnSeries ℚ Ω)
    (h : IsDl X A l (n + k) s F φ) : IsDl X A l n s F φ := by
  obtain ⟨hφ, a, c, κ, hκ, he, ha, hc, hcg⟩ := h
  refine ⟨hφ, a, c, κ, hκ, he, ha, hc, fun r => ?_⟩
  obtain ⟨z, hz, e⟩ := hcg r
  exact ⟨(l : Ω) ^ k * z, mul_mem (pow_mem (natCast_mem A l) k) hz, by rw [e, pow_add]; ring⟩

theorem UpperTheory.Kd.L.nrm :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [CharZero Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), ((l : ℕ) : Ω) ∈ A.nonunits → ∀ (n M : ℕ), 0 < M → ∀ (w : X.K) (φ φ' : HahnSeries ℚ Ω), w ∈ KT X M → IsDl X A l n (M : ℚ) w φ → (∀ r : ℚ, φ.coeff r ≠ 0 → (r * M).den = 1) → (∀ r : ℚ, φ'.coeff r = if r.den = 1 then φ.coeff r else 0) → IsDl X A l n 1 (nrmT X M w) φ' := by
  intro Ω _ _ _ _ ε X l _ A hl n M hM w φ φ' hw hφ _ hφ'
  have hj := X.j_hol.imp fun _ h => And.symm h
  obtain ⟨k, u, huA, hk⟩ := exists_pow_eq l A hl M hM
  have hw0 : w ≠ 0 := by
    rintro rfl
    obtain ⟨-, a, c, κ, hκ, he, ha, -, -⟩ := hφ
    rw [zero_mul] at he
    have ha0 : a = 0 := by
      rcases mul_eq_zero.1 he.symm with h | h
      · exact absurd ((map_eq_zero_iff _ (algebraMap Ω X.K).injective).1 h) hκ
      · exact h
    obtain ⟨-, r, hr, -⟩ := ha
    exact hr (by rw [ha0, map_zero]; rfl)
  obtain ⟨φ2, h2, hs2⟩ := GlobalTheory.T.exists_logDerivQExpansion_modPrimePow_of_translationInvariant ε X hj l A hl (n + k) M w hM hw0 hw
  have hu := GlobalTheory.T.isLogDerivQExpansionModPrimePow_unique ε X hj l A hl n (M : ℚ) w φ φ2 hφ (isDl_weak X A l n k _ w φ2 h2)
  have hT : ∀ b ∈ Finset.range M,
      IsDl X A l (n + k) (M : ℚ) (X.sl (ofSL (ModularGroup.T ^ b)) w) (NrmT.trT ε b φ2) :=
    fun b _ => NrmT.isLogDerivQExpansionModPrimePow_slash_T_pow X A l (n + k) _ w φ2 b h2
  have hP := GlobalTheory.T.isLogDerivQExpansion_finset_prod_zpow ε X hj l A hl (n + k) (M : ℚ) ℕ (Finset.range M)
    (fun b => X.sl (ofSL (ModularGroup.T ^ b)) w) (fun b => NrmT.trT ε b φ2) (fun _ => 1) hT
  simp only [zpow_one, one_smul] at hP
  rw [NrmT.sum_trT M φ2 hs2 (NrmT.resZ φ2) (NrmT.resZ_coeff φ2)] at hP
  have hN := isDl_divM X A l n k M hM u huA hk _ (NrmT.resZ φ2) (fun r => by
    rw [NrmT.resZ_coeff]; split_ifs
    · exact h2.1 r
    · exact zero_mem A) hP
  refine NrmT.isDl_congr X A l n 1 _ (NrmT.resZ φ2) φ' hN (fun r => ?_) (fun r => ?_)
  · rw [hφ']; split_ifs
    · exact hφ.1 r
    · exact zero_mem A
  · rw [hφ', NrmT.resZ_coeff]; split_ifs
    · exact hu r
    · exact ⟨0, zero_mem A, by ring⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.Witalg
section
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

private theorem gal_mul' {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (s t : Ω ≃ₐ[ℚ] Ω) (f : X.K) :
    X.gal (s * t) f = X.gal s (X.gal t f) := by
  apply X.exp.toRingHom.injective
  show X.exp _ = X.exp _
  ext r
  simp [X.gal_exp]

private theorem kmap_comp' {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime]
    (φ ψ χ : X.K ≃+* X.K) (h : ∀ f, χ f = φ (ψ f)) (a : X.Khat l) : X.kmap l χ a = X.kmap l φ (X.kmap l ψ a) := by
  unfold Tower.kmap
  have e : (AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive (Units.map χ.toMonoidHom))) =
      (AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive (Units.map φ.toMonoidHom))) ∘ₗ
        (AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive (Units.map ψ.toMonoidHom))) := by
    ext u
    exact h _
  show AdicCompletion.map (idl l) _ a = AdicCompletion.map (idl l) _ (AdicCompletion.map (idl l) _ a)
  rw [AdicCompletion.map_comp_apply, ← LinearMap.baseChange_comp, e]

theorem UpperTheory.Kd.L.witalg :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [CharZero Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N n : ℕ), 1 ≤ N → (∀ (b b' : X.Fn l) (f f' : X.Kˣ), IsWit X N l n b f → IsWit X N l n b' f' → IsWit X N l n (b + b') (f * f')) ∧ IsWit X N l n 0 1 ∧ (∀ (s : Ω ≃ₐ[ℚ] Ω) (b : X.Fn l) (f : X.Kˣ), IsWit X N l n b f → IsWit X N l n (X.galB l s b) (Units.map (X.gal s).toMonoidHom f)) ∧ ∀ s t : Ω ≃ₐ[ℚ] Ω, ∀ b : X.Fn l, X.galB l (s * t) b = X.galB l s (X.galB l t b) := by
  intro Ω _ _ _ _ ε X l _ N n _
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hl : 0 < l := (Fact.out : l.Prime).pos
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro b b' f f' ⟨h1, h2, h3⟩ ⟨k1, k2, k3⟩
    refine ⟨fun γ hγ => ?_, ?_, fun δ a c => ?_⟩
    · rw [Units.val_mul, map_mul, h1 γ hγ, k1 γ hγ]
    · rw [Pi.add_apply, map_add, h2, k2]
      unfold Tower.cls
      rw [← Submodule.Quotient.mk_add, ← TensorProduct.tmul_add, ofMul_mul]
    · obtain ⟨g, hg, e⟩ := h3 δ a c
      obtain ⟨g', hg', e'⟩ := k3 δ a c
      refine ⟨g * g', fun γ hγ => by rw [map_mul, hg γ hγ, hg' γ hγ], ?_⟩
      rw [Units.val_mul, map_mul, mul_pow, ← e, ← e']
      ring
  · refine ⟨fun γ _ => by simp, ?_, fun δ _ _ => ⟨1, fun γ _ => by simp, by simp⟩⟩
    simp [Tower.cls]
  · rintro s b f ⟨hfI, hcls, hδ⟩
    have hf : ((Units.map (X.gal s).toMonoidHom f : X.Kˣ) : X.K) = X.gal s f := rfl
    refine ⟨?_, ?_, ?_⟩
    · rw [hf]; exact GlobalTheory.ThGal.inv_gal X s _ _ hfI
    · have hu : (![(![1, 0] : Fin 2 → ℤ_[l]) 0,
          (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) * (![1, 0] : Fin 2 → ℤ_[l]) 1] : Fin 2 → ℤ_[l]) = ![1, 0] := by
        funext i; fin_cases i <;> simp
      have hg : X.galB l s b ![1, 0] = X.kmap l (X.gal s) (b ![(![1, 0] : Fin 2 → ℤ_[l]) 0,
          (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) * (![1, 0] : Fin 2 → ℤ_[l]) 1]) := rfl
      rw [hu] at hg
      rw [AdicCompletion.eval_apply] at hcls
      rw [hg, AdicCompletion.eval_apply, Tower.kmap]
      erw [AdicCompletion.map_val_apply]
      rw [hcls]
      simp [Tower.cls, LinearMap.reduceModIdeal_apply]
    · intro δ hδ1 hδ2
      obtain ⟨δ', h1, h2, hrec⟩ := GlobalTheory.ThGal.exists_twist X s N l n hl f hfI δ hδ1 hδ2
      obtain ⟨g, hg, hfg⟩ := hδ δ' h1 h2
      refine ⟨X.gal s g, GlobalTheory.ThGal.inv_gal X s _ _ hg, ?_⟩
      rw [hf, ← hrec, ← map_mul, hfg, map_pow]
  · intro s t b
    funext u
    show X.kmap l (X.gal (s * t)) (b ![u 0, (cyclotomicCharacter Ω l (s * t).toRingEquiv : ℤ_[l]) * u 1]) =
      X.kmap l (X.gal s) (X.kmap l (X.gal t) (b ![u 0, (cyclotomicCharacter Ω l t.toRingEquiv : ℤ_[l]) *
        ((cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) * u 1)]))
    have hm : (s * t).toRingEquiv = s.toRingEquiv * t.toRingEquiv := rfl
    rw [kmap_comp' X l _ _ _ (gal_mul' X s t), hm, map_mul, Units.val_mul, mul_left_comm, mul_assoc]
end

