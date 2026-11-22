import Mathlib

-- bundled from ReciprocityTheory.Chebotarev.AbsProdSubProdLeSumAbsSub
section
open Finset

namespace ReciprocityTheory.Cheb

noncomputable def tent (t : ℝ) : ℝ := max 0 (1 - |t|)

theorem tent_nonneg (t : ℝ) : 0 ≤ tent t := le_max_left _ _

theorem tent_le_one (t : ℝ) : tent t ≤ 1 :=
  max_le zero_le_one (by linarith [abs_nonneg t])

theorem tent_of_abs_le {t : ℝ} (h : |t| ≤ 1) : tent t = 1 - |t| :=
  max_eq_right (by linarith)

theorem tent_of_one_le_abs {t : ℝ} (h : 1 ≤ |t|) : tent t = 0 :=
  max_eq_left (by linarith)

theorem abs_tent_sub_tent_le (s t : ℝ) : |tent s - tent t| ≤ |s - t| := by
  unfold tent
  calc |max 0 (1 - |s|) - max 0 (1 - |t|)| ≤ |(1 - |s|) - (1 - |t|)| := by
        rw [max_comm 0, max_comm 0]; exact abs_max_sub_max_le_abs _ _ _
    _ = |(|t| - |s|)| := by ring_nf
    _ ≤ |t - s| := abs_abs_sub_abs_le_abs_sub t s
    _ = |s - t| := abs_sub_comm t s

theorem abs_lt_one_of_tent_ne_zero {t : ℝ} (h : tent t ≠ 0) : |t| < 1 := by
  by_contra h'
  exact h (tent_of_one_le_abs (not_lt.mp h'))

theorem tent_add_int_eq_zero_of_notMem (t : ℝ) {n : ℤ} (hn : n ∉ ({-⌊t⌋, -⌊t⌋ - 1} : Finset ℤ)) :
    tent (t + n) = 0 := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
  apply tent_of_one_le_abs
  have h1 := Int.floor_le t
  have h2 := Int.lt_floor_add_one t
  rcases lt_or_gt_of_ne hn.1 with h | h
  · have : n ≤ -⌊t⌋ - 2 := by omega
    have : (n : ℝ) ≤ -⌊t⌋ - 2 := by exact_mod_cast this
    rw [abs_of_neg (by linarith)]; linarith
  · have : (n : ℝ) ≥ -⌊t⌋ + 1 := by exact_mod_cast (show n ≥ -⌊t⌋ + 1 by omega)
    rw [abs_of_nonneg (by linarith)]; linarith

theorem sum_tent_add_int_pair (t : ℝ) :
    ∑ n ∈ ({-⌊t⌋, -⌊t⌋ - 1} : Finset ℤ), tent (t + n) = 1 := by
  have hne : (-⌊t⌋ : ℤ) ≠ -⌊t⌋ - 1 := by omega
  rw [Finset.sum_pair hne]
  have h1 := Int.floor_le t
  have h2 := Int.lt_floor_add_one t
  push_cast
  rw [tent_of_abs_le, tent_of_abs_le]
  · rw [abs_of_nonneg (by linarith), abs_of_neg (by linarith)]; ring
  · rw [abs_le]; constructor <;> linarith
  · rw [abs_le]; constructor <;> linarith

section Product

theorem abs_prod_sub_prod_le_sum_abs_sub {κ : Type*} (s : Finset κ) (a b : κ → ℝ)
    (ha : ∀ i ∈ s, |a i| ≤ 1) (hb : ∀ i ∈ s, |b i| ≤ 1) :
    |∏ i ∈ s, a i - ∏ i ∈ s, b i| ≤ ∑ i ∈ s, |a i - b i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [prod_insert hj, prod_insert hj, sum_insert hj]
    have hP : |∏ i ∈ s, b i| ≤ 1 := by
      rw [Finset.abs_prod]
      exact prod_le_one (fun i _ => abs_nonneg _) (fun i hi => hb i (mem_insert_of_mem hi))
    have ih' := ih (fun i hi => ha i (mem_insert_of_mem hi)) (fun i hi => hb i (mem_insert_of_mem hi))
    have haj := ha j (mem_insert_self j s)
    have hsum : 0 ≤ ∑ i ∈ s, |a i - b i| := sum_nonneg fun i _ => abs_nonneg _
    calc |a j * ∏ i ∈ s, a i - b j * ∏ i ∈ s, b i|
        = |a j * (∏ i ∈ s, a i - ∏ i ∈ s, b i) + (a j - b j) * ∏ i ∈ s, b i| := by ring_nf
      _ ≤ |a j| * |∏ i ∈ s, a i - ∏ i ∈ s, b i| + |a j - b j| * |∏ i ∈ s, b i| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ 1 * ∑ i ∈ s, |a i - b i| + |a j - b j| * 1 :=
        add_le_add (mul_le_mul haj ih' (abs_nonneg _) zero_le_one)
          (mul_le_mul_of_nonneg_left hP (abs_nonneg _))
      _ = |a j - b j| + ∑ i ∈ s, |a i - b i| := by ring

variable {ι : Type*} [Fintype ι]

noncomputable def Tent (y : ι → ℝ) : ℝ := ∏ i, tent (y i)

theorem Tent_nonneg (y : ι → ℝ) : 0 ≤ Tent y := prod_nonneg fun _ _ => tent_nonneg _

theorem Tent_le_one (y : ι → ℝ) : Tent y ≤ 1 :=
  prod_le_one (fun _ _ => tent_nonneg _) (fun _ _ => tent_le_one _)

theorem abs_lt_one_of_Tent_ne_zero {y : ι → ℝ} (h : Tent y ≠ 0) (i : ι) : |y i| < 1 :=
  abs_lt_one_of_tent_ne_zero fun h' => h (prod_eq_zero (mem_univ i) h')

theorem abs_Tent_sub_Tent_le (y y' : ι → ℝ) : |Tent y - Tent y'| ≤ ∑ i, |y i - y' i| := by
  unfold Tent
  refine (abs_prod_sub_prod_le_sum_abs_sub univ _ _ (fun i _ => ?_) (fun i _ => ?_)).trans
    (sum_le_sum fun i _ => abs_tent_sub_tent_le (y i) (y' i))
  · rw [abs_of_nonneg (tent_nonneg _)]; exact tent_le_one _
  · rw [abs_of_nonneg (tent_nonneg _)]; exact tent_le_one _

theorem Tent_add_int_eq_zero_of_notMem [DecidableEq ι] (y : ι → ℝ) {n : ι → ℤ}
    (hn : n ∉ Fintype.piFinset fun i => ({-⌊y i⌋, -⌊y i⌋ - 1} : Finset ℤ)) :
    Tent (fun i => y i + n i) = 0 := by
  rw [Fintype.mem_piFinset] at hn
  push Not at hn
  obtain ⟨i, hi⟩ := hn
  exact prod_eq_zero (mem_univ i) (tent_add_int_eq_zero_of_notMem (y i) hi)

theorem sum_Tent_add_int_piFinset [DecidableEq ι] (y : ι → ℝ) :
    ∑ n ∈ Fintype.piFinset (fun i => ({-⌊y i⌋, -⌊y i⌋ - 1} : Finset ℤ)), Tent (fun i => y i + n i) = 1 := by
  classical
  show ∑ n ∈ Fintype.piFinset (fun i => ({-⌊y i⌋, -⌊y i⌋ - 1} : Finset ℤ)), ∏ i, tent (y i + n i) = 1
  rw [← Finset.prod_univ_sum (fun i => ({-⌊y i⌋, -⌊y i⌋ - 1} : Finset ℤ)) (fun i n => tent (y i + n))]
  exact prod_eq_one fun i _ => sum_tent_add_int_pair (y i)

theorem hasSum_Tent_add_int (y : ι → ℝ) : HasSum (fun n : ι → ℤ => Tent (fun i => y i + n i)) 1 := by
  classical
  have h : HasSum (fun n : ι → ℤ => Tent (fun i => y i + n i))
      (∑ n ∈ Fintype.piFinset (fun i => ({-⌊y i⌋, -⌊y i⌋ - 1} : Finset ℤ)), Tent (fun i => y i + n i)) :=
    hasSum_sum_of_ne_finset_zero fun n hn => Tent_add_int_eq_zero_of_notMem y hn
  rwa [sum_Tent_add_int_piFinset] at h

end Product

end ReciprocityTheory.Cheb
end

-- bundled from ReciprocityTheory.Chebotarev.CrossFix
section
open NumberField Polynomial

namespace ReciprocityTheory.Cheb

variable {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    [IsGalois ℚ K] [IsGalois ℚ M]

theorem eq_one_of_restrict_eq_one {l : ℕ} [Fact l.Prime] [IsCyclotomicExtension {l} K M]
    {ζ : M} (hζ : IsPrimitiveRoot ζ l) (h : Gal(M/ℚ)) (hK : AlgEquiv.restrictNormal h K = 1) (h1 : h ζ = ζ) : h = 1 := by
  have hl : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  have htop := IsCyclotomicExtension.adjoin_primitive_root_eq_top (A := K) hζ
  refine AlgEquiv.ext fun x => ?_
  rw [AlgEquiv.one_apply]
  have hx : x ∈ Algebra.adjoin K ({ζ} : Set M) := htop ▸ Algebra.mem_top
  induction hx using Algebra.adjoin_induction with
  | mem y hy => rw [Set.mem_singleton_iff.mp hy]; exact h1
  | algebraMap r =>
    have := AlgEquiv.restrictNormal_commutes h K r
    rw [hK, AlgEquiv.one_apply] at this
    exact this.symm
  | add y z _ _ hy hz => rw [map_add, hy, hz]
  | mul y z _ _ hy hz => rw [map_mul, hy, hz]

theorem pow_apply_zeta_of_apply_eq_pow {ζ : M} (g : Gal(M/ℚ)) (t : ℕ) (hg : g ζ = ζ ^ t) (m : ℕ) :
    (g ^ m) ζ = ζ ^ (t ^ m) := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, AlgEquiv.mul_apply, hg, map_pow, ih, ← pow_mul, ← pow_succ]

theorem zeta_pow_eq_pow_iff_natCast {l : ℕ} [NeZero l] {ζ : M} (hζ : IsPrimitiveRoot ζ l) (a b : ℕ) :
    ζ ^ a = ζ ^ b ↔ (a : ZMod l) = b := by
  have hfin : IsOfFinOrder ζ := isOfFinOrder_iff_pow_eq_one.2 ⟨l, NeZero.pos l, hζ.pow_eq_one⟩
  rw [ZMod.natCast_eq_natCast_iff, hζ.eq_orderOf]
  exact hfin.pow_eq_pow_iff_modEq

theorem pow_apply_zeta_eq_units_pow {l : ℕ} [NeZero l] {ζ : M} (hζ : IsPrimitiveRoot ζ l) (τ : (ZMod l)ˣ)
    (g : Gal(M/ℚ)) (hgζ : g ζ = ζ ^ (τ : ZMod l).val) (m : ℕ) :
    (g ^ m) ζ = ζ ^ (((τ ^ m : (ZMod l)ˣ) : ZMod l).val) := by
  rw [pow_apply_zeta_of_apply_eq_pow g _ hgζ m, zeta_pow_eq_pow_iff_natCast hζ]
  simp

theorem restrictNormal_pow_of_gal (g : Gal(M/ℚ)) (m : ℕ) :
    AlgEquiv.restrictNormal (g ^ m) K = (AlgEquiv.restrictNormal g K) ^ m :=
  map_pow (AlgEquiv.restrictNormalHom K) g m

theorem eq_of_apply_eq_pow {l : ℕ} [Fact l.Prime] [IsCyclotomicExtension {l} K M]
    {ζ : M} (hζ : IsPrimitiveRoot ζ l) (σ : Gal(K/ℚ)) (hσ : orderOf σ ∣ l - 1) (τ : (ZMod l)ˣ) (hτ : orderOf τ = l - 1)
    (g : Gal(M/ℚ)) (hg : AlgEquiv.restrictNormal g K = σ) (hgζ : g ζ = ζ ^ (τ : ZMod l).val)
    (φ : M ≃ₐ[IntermediateField.fixedField (Subgroup.zpowers g)] M) (n : ℕ) (hφ : φ ζ = ζ ^ n) (hn : (n : ZMod l) = τ) :
    φ.restrictScalars ℚ = g := by
  have hl : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  have hmem' : φ.restrictScalars ℚ ∈
      IntermediateField.fixingSubgroup (IntermediateField.fixedField (Subgroup.zpowers g)) := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact φ.commutes ⟨x, hx⟩
  have hmem : φ.restrictScalars ℚ ∈ Subgroup.zpowers g := by
    rwa [IntermediateField.fixingSubgroup_fixedField] at hmem'
  obtain ⟨k, hk : g ^ k = _⟩ := mem_powers_iff_mem_zpowers.mpr hmem
  have hpos := orderOf_pos g
  set m := k + orderOf g - 1 with hm
  have hkm : g ^ (m + 1) = g ^ k := by
    rw [show m + 1 = k + orderOf g by omega, pow_add, pow_orderOf_eq_one, mul_one]
  have hφ' : (g ^ (m + 1)) ζ = ζ ^ n := by rw [hkm, hk]; exact hφ
  rw [pow_apply_zeta_eq_units_pow hζ τ g hgζ, zeta_pow_eq_pow_iff_natCast hζ, ZMod.natCast_zmod_val, hn] at hφ'
  have hτm : τ ^ m = 1 := by
    have h2 : τ ^ (m + 1) = τ := Units.ext hφ'
    rw [pow_succ] at h2
    exact mul_eq_right.mp h2
  have hdiv : l - 1 ∣ m := hτ ▸ orderOf_dvd_of_pow_eq_one hτm
  have hσm : σ ^ m = 1 := orderOf_dvd_iff_pow_eq_one.mp (hσ.trans hdiv)
  have hgm : g ^ m = 1 := by
    refine eq_one_of_restrict_eq_one (K := K) hζ (g ^ m) ?_ ?_
    · rw [restrictNormal_pow_of_gal, hg, hσm]
    · rw [pow_apply_zeta_eq_units_pow hζ τ g hgζ, hτm, Units.val_one, ZMod.val_one_eq_one_mod,
        Nat.mod_eq_of_lt (Fact.out : l.Prime).one_lt, pow_one]
  rw [← hk, ← hkm, pow_succ, hgm, one_mul]

theorem irreducible_cyclotomic_fixedField {l : ℕ} [Fact l.Prime] [IsCyclotomicExtension {l} K M]
    {ζ : M} (hζ : IsPrimitiveRoot ζ l) (σ : Gal(K/ℚ)) (hσ : orderOf σ ∣ l - 1) (τ : (ZMod l)ˣ) (hτ : orderOf τ = l - 1)
    (g : Gal(M/ℚ)) (hg : AlgEquiv.restrictNormal g K = σ) (hgζ : g ζ = ζ ^ (τ : ZMod l).val) :
    Irreducible (cyclotomic l (IntermediateField.fixedField (Subgroup.zpowers g))) := by
  have hlp := (Fact.out : l.Prime)
  have hl : NeZero l := ⟨hlp.ne_zero⟩
  set E := IntermediateField.fixedField (Subgroup.zpowers g)
  have hint : IsIntegral E ζ := Algebra.IsIntegral.isIntegral ζ
  set p := minpoly E ζ with hp
  have hcard : Fintype.card (ZMod l)ˣ = l - 1 := by
    rw [ZMod.card_units_eq_totient, Nat.totient_prime hlp]

  have htop : Subgroup.zpowers τ = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, hτ, Nat.card_eq_fintype_card, hcard]

  have hroot : ∀ u : (ZMod l)ˣ, aeval (ζ ^ (u : ZMod l).val) p = 0 := by
    intro u
    have hu : u ∈ Subgroup.zpowers τ := htop ▸ Subgroup.mem_top u
    obtain ⟨k, hk : τ ^ k = u⟩ := mem_powers_iff_mem_zpowers.mpr hu
    have hgk : g ^ k ∈ IntermediateField.fixingSubgroup E := by
      rw [IntermediateField.fixingSubgroup_fixedField]
      exact Subgroup.npow_mem_zpowers g k
    set ψ := IntermediateField.fixingSubgroupEquiv E ⟨g ^ k, hgk⟩
    have hψ : ψ ζ = ζ ^ (u : ZMod l).val := by
      change (g ^ k) ζ = _
      rw [pow_apply_zeta_eq_units_pow hζ τ g hgζ, hk]
    rw [← hψ, Polynomial.aeval_algEquiv, AlgHom.comp_apply, hp, minpoly.aeval, map_zero]
  have hdvd : p ∣ cyclotomic l E := by
    apply minpoly.dvd
    rw [← Polynomial.eval_map_algebraMap, Polynomial.map_cyclotomic]
    exact (hζ.isRoot_cyclotomic (NeZero.pos l))
  have hp0 : p.map (algebraMap E M) ≠ 0 := Polynomial.map_ne_zero (minpoly.ne_zero hint)
  classical
  let Z : Finset M := Finset.univ.image (fun u : (ZMod l)ˣ => ζ ^ (u : ZMod l).val)
  have hZcard : Z.card = l - 1 := by
    rw [Finset.card_image_of_injective _ ?_, Finset.card_univ, hcard]
    intro u v huv
    have := hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) huv
    exact Units.ext (ZMod.val_injective l this)
  have hZ : Z.val ⊆ (p.map (algebraMap E M)).roots := by
    intro z hz
    obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp hz
    rw [Polynomial.mem_roots hp0, Polynomial.IsRoot, Polynomial.eval_map_algebraMap]
    exact hroot u
  have hdeg := Polynomial.card_le_degree_of_subset_roots hZ
  rw [hZcard, Polynomial.natDegree_map] at hdeg
  have heq : cyclotomic l E = p := by
    refine Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint)
      (Polynomial.cyclotomic.monic l E) hdvd ?_
    rw [Polynomial.natDegree_cyclotomic, Nat.totient_prime hlp]
    exact hdeg
  rw [heq]
  exact minpoly.irreducible hint

end ReciprocityTheory.Cheb
end

-- bundled from ReciprocityTheory.Chebotarev.CrossFrobE
section
open NumberField Polynomial

namespace ReciprocityTheory.Cheb

theorem exists_frob_above {M : Type} [Field M] [NumberField M] (E : IntermediateField ℚ M) [IsGalois E M]
    (l : ℕ) [Fact l.Prime] {ζ : M} (hζ : IsPrimitiveRoot ζ l) (q : Ideal (𝓞 E)) (hq : q.IsPrime)
    (hqp : (Ideal.absNorm q).Prime) (hql : Ideal.absNorm q ≠ l) :
    ∃ (P : Ideal (𝓞 M)) (_ : P.IsPrime) (φ : M ≃ₐ[E] M),
      P.LiesOver (Ideal.span {((Ideal.absNorm q : ℕ) : ℤ)}) ∧ φ ζ = ζ ^ Ideal.absNorm q ∧
      IsArithFrobAt ℤ (φ.restrictScalars ℚ) P := by
  set p := Ideal.absNorm q with hpdef
  have hq0 : q ≠ ⊥ := by
    intro h
    rw [h, Ideal.absNorm_bot] at hpdef
    exact Nat.not_prime_zero (hpdef ▸ hqp)
  have hqmax : q.IsMaximal := hq.isMaximal hq0
  obtain ⟨P, hPmax, hPq⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 M) q
  have hPunder : P.under (𝓞 E) = q := hPq.over.symm
  have hP0 : P ≠ ⊥ := by
    intro h
    apply hq0
    rw [← hPunder, h]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)
  have hPfin : Finite (𝓞 M ⧸ P) :=
    (Ideal.absNorm_ne_zero_iff P).mp (fun h => hP0 (Ideal.absNorm_eq_zero_iff.mp h))
  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant (𝓞 E) (M ≃ₐ[E] M) P

  have hqZ : q.under ℤ = Ideal.span {(p : ℤ)} := by
    have hpr : (Ideal.span {(p : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hqp).irreducible
    have hle : Ideal.span {(p : ℤ)} ≤ q.under ℤ := by
      rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.under_def, Ideal.mem_comap]
      have := Ideal.absNorm_mem q
      rw [← hpdef] at this
      simpa using this
    exact (hpr.eq_of_le (Ideal.IsPrime.under ℤ q).ne_top hle).symm
  have hPZ : P.under ℤ = Ideal.span {(p : ℤ)} := by
    rw [← Ideal.under_under (B := 𝓞 E), hPunder, hqZ]
  have hcardZ : Nat.card (ℤ ⧸ P.under ℤ) = p := by
    rw [hPZ, Nat.card_congr (Int.quotientSpanNatEquivZMod p).toEquiv, Nat.card_zmod]
  have hcardE : Nat.card (𝓞 E ⧸ P.under (𝓞 E)) = p := by
    rw [hPunder, hpdef, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hfrob : IsArithFrobAt ℤ (σ.restrictScalars ℚ) P := by
    intro x
    have := hσ x
    rw [hcardE] at this
    show (σ.restrictScalars ℚ) • x - x ^ Nat.card (ℤ ⧸ P.under ℤ) ∈ P
    rw [hcardZ]
    exact this
  refine ⟨P, hPmax.isPrime, σ, ⟨hPZ.symm⟩, ?_, hfrob⟩

  have hint : IsIntegral ℤ ζ := hζ.isIntegral (Nat.Prime.pos Fact.out)
  let z : 𝓞 M := ⟨ζ, hint⟩
  have hz : z ^ l = 1 := by
    apply RingOfIntegers.ext
    rw [RingOfIntegers.coe_eq_algebraMap, RingOfIntegers.coe_eq_algebraMap, map_one]
    exact (map_pow (algebraMap (𝓞 M) M) z l).trans hζ.pow_eq_one
  have hl : ((l : ℕ) : 𝓞 M) ∉ P := by
    intro h
    have h' : ((l : ℕ) : ℤ) ∈ P.under ℤ := by
      rw [Ideal.mem_comap]; simpa using h
    rw [hPZ, Ideal.mem_span_singleton] at h'
    have hdvd : p ∣ l := by exact_mod_cast h'
    exact hql ((Nat.prime_dvd_prime_iff_eq hqp Fact.out).mp hdvd)
  have key := AlgHom.IsArithFrobAt.apply_of_pow_eq_one hfrob hz hl
  rw [hcardZ] at key
  calc σ ζ = (((σ.restrictScalars ℚ) • z : 𝓞 M) : M) := rfl
    _ = ((z ^ p : 𝓞 M) : M) := congrArg (fun y : 𝓞 M => (y : M)) key
    _ = ζ ^ p := by
      rw [RingOfIntegers.coe_eq_algebraMap]
      exact (map_pow (algebraMap (𝓞 M) M) z p).trans rfl

end ReciprocityTheory.Cheb
end

-- bundled from ReciprocityTheory.Chebotarev.CrossGal
section
open NumberField Polynomial

namespace ReciprocityTheory.Cheb

theorem cxgal_exists_sf (K : Type) [Field K] [NumberField K] [IsGalois ℚ K] :
    ∃ p : ℚ[X], p ≠ 0 ∧ IsSplittingField ℚ K p := by
  obtain ⟨p, hp⟩ := Normal.exists_isSplittingField ℚ K
  by_cases h0 : p = 0
  · subst h0
    refine ⟨X, X_ne_zero, ?_⟩
    constructor
    · simp
    · have h := hp.adjoin_rootSet
      simp only [rootSet_zero, Algebra.adjoin_empty] at h
      rw [eq_top_iff, ← h]
      exact bot_le
  · exact ⟨p, h0, hp⟩

theorem isGalois_cyclotomicField (K : Type) [Field K] [NumberField K] [IsGalois ℚ K] (l : ℕ) [NeZero l] :
    IsGalois ℚ (CyclotomicField l K) := by
  obtain ⟨p, hp0, hp⟩ := cxgal_exists_sf K
  have : IsSplittingField K (CyclotomicField l K) ((X ^ l - 1 : ℚ[X]).map (algebraMap ℚ K)) := by
    simp only [Polynomial.map_sub, Polynomial.map_pow, map_X, Polynomial.map_one]
    exact IsCyclotomicExtension.isSplittingField_X_pow_sub_one l K (CyclotomicField l K)
  have := IsSplittingField.mul (K := K) (L := CyclotomicField l K) p (X ^ l - 1) hp0
    (X_pow_sub_C_ne_zero (NeZero.pos l) 1)
  have : Normal ℚ (CyclotomicField l K) := Normal.of_isSplittingField (p * (X ^ l - 1))
  exact IsGalois.mk

end ReciprocityTheory.Cheb
end

-- bundled from ReciprocityTheory.Chebotarev.CrossLift
section
open NumberField Polynomial

namespace ReciprocityTheory.Cheb

theorem exists_lift_pow {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    [IsGalois ℚ K] [IsGalois ℚ M] (l : ℕ) [Fact l.Prime] [IsCyclotomicExtension {l} K M]
    (hirr : Irreducible (cyclotomic l K)) {ζ : M} (hζ : IsPrimitiveRoot ζ l) (σ : Gal(K/ℚ)) (τ : (ZMod l)ˣ) :
    ∃ g : Gal(M/ℚ), AlgEquiv.restrictNormal g K = σ ∧ g ζ = ζ ^ (τ : ZMod l).val := by
  have hl : 0 < l := (Fact.out : l.Prime).pos
  have : NeZero l := ⟨hl.ne'⟩
  obtain ⟨g₀, hg₀⟩ := AlgEquiv.restrictNormalHom_surjective (F := ℚ) (K₁ := K) M σ
  have hg₀ζ : IsPrimitiveRoot (g₀ ζ) l := hζ.map_of_injective g₀.injective
  obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hg₀ζ.pow_eq_one
  have hcop : i.Coprime l := (hζ.pow_iff_coprime hl i).mp (hi ▸ hg₀ζ)
  set u : (ZMod l)ˣ := ZMod.unitOfCoprime i hcop with hu
  set t : (ZMod l)ˣ := τ * u⁻¹ with ht
  set h : M ≃ₐ[K] M := (IsCyclotomicExtension.autEquivPow M hirr).symm t with hh
  have hz := IsCyclotomicExtension.zeta_spec l K M
  have hhz : h (IsCyclotomicExtension.zeta l K M) = (IsCyclotomicExtension.zeta l K M) ^ (t : ZMod l).val := by
    have h1 := hz.autToPow_spec K h
    have h2 : hz.autToPow K h = t := by
      have := (IsCyclotomicExtension.autEquivPow M hirr).apply_symm_apply t
      exact this
    rw [← h1, h2]
  obtain ⟨a, -, ha⟩ := hz.eq_pow_of_pow_eq_one hζ.pow_eq_one
  have hhζ : h ζ = ζ ^ (t : ZMod l).val := by
    rw [← ha, map_pow, hhz, ← pow_mul, ← pow_mul, mul_comm]
  refine ⟨h.restrictScalars ℚ * g₀, ?_, ?_⟩
  · have h1 : AlgEquiv.restrictNormal (h.restrictScalars ℚ) K = 1 := by
      ext x
      have e := AlgEquiv.restrictNormal_commutes (h.restrictScalars ℚ : M ≃ₐ[ℚ] M) K x
      have e2 : (h.restrictScalars ℚ) (algebraMap K M x) = algebraMap K M x := h.commutes x
      rw [e2] at e
      exact (algebraMap K M).injective e
    have h2 : AlgEquiv.restrictNormal (h.restrictScalars ℚ * g₀) K =
        AlgEquiv.restrictNormal (h.restrictScalars ℚ) K * AlgEquiv.restrictNormal g₀ K :=
      map_mul (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := M) K) _ _
    rw [h2, h1, one_mul]
    exact hg₀
  · show h (g₀ ζ) = _
    rw [← hi, map_pow, hhζ, ← pow_mul]
    rw [← pow_mod_orderOf, ← hζ.eq_orderOf, ← pow_mod_orderOf ζ (τ : ZMod l).val, ← hζ.eq_orderOf]
    congr 1
    rw [← ZMod.natCast_eq_natCast_iff']
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    have : ((u : (ZMod l)ˣ) : ZMod l) = (i : ZMod l) := rfl
    rw [← this]
    rw [← Units.val_mul, ht, inv_mul_cancel_right]

end ReciprocityTheory.Cheb
end

-- bundled from ReciprocityTheory.Chebotarev.CrossRes
section
open NumberField Polynomial

namespace ReciprocityTheory.Cheb

theorem isArithFrobAt_restrictNormal {K M : Type} [Field K] [NumberField K] [IsGalois ℚ K] [Field M] [NumberField M]
    [Algebra K M] (g : Gal(M/ℚ)) (p : ℕ) (P : Ideal (𝓞 M)) (hP : P.IsPrime)
    (hPp : P.LiesOver (Ideal.span {(p : ℤ)})) (h : IsArithFrobAt ℤ g P) :
    (P.under (𝓞 K)).IsPrime ∧ (P.under (𝓞 K)).LiesOver (Ideal.span {(p : ℤ)}) ∧
      IsArithFrobAt ℤ (AlgEquiv.restrictNormal g K) (P.under (𝓞 K)) := by
  refine ⟨Ideal.IsPrime.under _ _, ⟨by rw [Ideal.under_under]; exact hPp.over⟩, ?_⟩
  intro y
  have hu : (P.under (𝓞 K)).under ℤ = P.under ℤ := Ideal.under_under P
  have hc : algebraMap (𝓞 K) (𝓞 M) ((AlgEquiv.restrictNormal g K) • y) =
      g • algebraMap (𝓞 K) (𝓞 M) y := by
    apply NumberField.RingOfIntegers.ext
    exact AlgEquiv.restrictNormal_commutes g K (y : K)
  show _ ∈ Ideal.comap _ P
  rw [Ideal.mem_comap]
  simp only [MulSemiringAction.toAlgHom_apply, hu, map_sub, map_pow, hc]
  simpa using h (algebraMap (𝓞 K) (𝓞 M) y)

end ReciprocityTheory.Cheb
end

-- bundled from ReciprocityTheory.Chebotarev.CycStatement
section
open NumberField

namespace ReciprocityTheory.Cheb

def Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsGalois ℚ K] (σ : Gal(K/ℚ)) (T : Finset ℕ),
    ∃ p : ℕ, p.Prime ∧ p ∉ T ∧ ∃ P : Ideal (𝓞 K), ∃ _ : P.IsPrime,
      P.LiesOver (Ideal.span {(p : ℤ)}) ∧ Algebra.IsUnramifiedAt ℤ P ∧ IsArithFrobAt ℤ σ P

def CycStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime], Irreducible (Polynomial.cyclotomic l E) →
    ∀ (a : (ZMod l)ˣ) (T : Finset ℕ), ∃ q : Ideal (𝓞 E), q.IsPrime ∧ (Ideal.absNorm q).Prime ∧ Ideal.absNorm q ∉ T ∧
      ((Ideal.absNorm q : ℕ) : ZMod l) = a

end ReciprocityTheory.Cheb
end

