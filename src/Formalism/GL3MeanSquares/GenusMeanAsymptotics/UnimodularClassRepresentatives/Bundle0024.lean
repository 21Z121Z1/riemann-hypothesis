import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0022

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.SupEqTopOfMemHcompl
section
open NumberField Module Matrix

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.OrthogonalBases

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem sup_eq_top_of_mem_hcompl (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {P : Ideal (𝓞 K)}
    (hP : P.IsMaximal) {u : 𝓞 K} (hu : u ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) P) :
    Ideal.span {u} ⊔ extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) = ⊤ := by
  by_contra hne
  obtain ⟨Q, hQ, hle⟩ := Ideal.exists_le_maximal _ hne
  have hu' := (Formalism.HermitianLattices.Ext.L3.WA.mem_hcompl_iff hP.isPrime u).1 hu
  have huQ : u ∈ Q := hle (Ideal.mem_sup_left (Ideal.mem_span_singleton_self u))
  have hext : extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) ≤ Q := le_trans le_sup_right hle
  have hpQ : P.comap (algebraMap (𝓞 F) (𝓞 K)) ≤ Q.comap (algebraMap (𝓞 F) (𝓞 K)) :=
    Ideal.map_le_iff_le_comap.1 hext
  have hmax : (P.comap (algebraMap (𝓞 F) (𝓞 K))).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P
  haveI := hQ.isPrime
  have heq : P.comap (algebraMap (𝓞 F) (𝓞 K)) = Q.comap (algebraMap (𝓞 F) (𝓞 K)) :=
    hmax.eq_of_le (inferInstance : (Q.comap (algebraMap (𝓞 F) (𝓞 K))).IsPrime).ne_top hpQ
  rcases (comap_eq_comap_iff hK hF hP hQ).1 heq with h | h
  · exact hu'.1 (h ▸ huQ)
  · exact hu'.2 (h ▸ huQ)

private theorem isUnitIn_mul' {S : Subring K} {a b : K} (ha : Formalism.HermitianLattices.Ext.L3.WA.IsUnitIn S a)
    (hb : Formalism.HermitianLattices.Ext.L3.WA.IsUnitIn S b) : Formalism.HermitianLattices.Ext.L3.WA.IsUnitIn S (a * b) :=
  ⟨mul_ne_zero ha.1 hb.1, S.mul_mem ha.2.1 hb.2.1, by rw [mul_inv]; exact S.mul_mem ha.2.2 hb.2.2⟩

theorem exists_orth_basis (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) (hv : vd h L 𝔭 = 0) :
    ∃ (b : Basis (Fin (finrank K V)) K V) (u : Fin (finrank K V) → 𝓞 K), (∀ i, b i ∈ L) ∧
      locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) = locF 𝔭 L ∧
      (∀ i j, algebraMap (𝓞 K) K (diagonal u i j) = h (b i) (b j)) ∧
      (∀ i, conjO K (u i) = u i) ∧ ∀ i, Ideal.span {u i} ⊔ extP K 𝔭 = ⊤ := by
  obtain ⟨P, hP, rfl⟩ := exists_maximal_over hK hF h𝔭
  have hU : Formalism.HermitianLatticesTheory.IsUnimodularAt h P L := (isUnimodularAt_iff_vd hK hF hs hd hL hLi hP).2 hv
  have hSD := Formalism.HermitianLattices.Ext.L3.WA.isSelfDualMod_loc hL hP.isPrime hU
  have hdd : ∀ x, h x x = 0 → x = 0 := by
    intro x hx
    by_contra hx0
    have := hd x hx0 (Classical.arbitrary (NumberField.InfinitePlace K)).embedding
    rw [hx, map_zero, Complex.zero_re] at this
    exact lt_irrefl 0 this
  obtain ⟨x, hxM, hxo, hxu⟩ := Formalism.HermitianLattices.Ext.L3.LocF.exists_orth_unit_frame
    (Formalism.HermitianLattices.Ext.L3.WA.isHermSemilocal_locRing hK hP)
    (Formalism.HermitianLattices.Ext.L3.LocF.locRing_local hP.isPrime) hs hdd hSD
  have hx' : ∀ i, ∃ s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) P, s • x i ∈ L := fun i => hxM i
  choose s hsP hsL using hx'
  set b0 : Fin (finrank K V) → V := fun i => algebraMap (𝓞 K) K (s i) • x i with hb0
  have hb0L : ∀ i, b0 i ∈ L := by
    intro i
    simp only [hb0, algebraMap_smul]
    exact hsL i
  have hbb : ∀ i j, h (b0 i) (b0 j) =
      star (algebraMap (𝓞 K) K (s i)) * algebraMap (𝓞 K) K (s j) * h (x i) (x j) := by
    intro i j
    simp only [hb0, LinearMap.map_smulₛₗ₂, map_smul, smul_eq_mul, starRingEnd_apply]
    ring
  have hunit : ∀ i, Formalism.HermitianLattices.Ext.L3.WA.IsUnitIn (Formalism.HermitianLattices.Ext.L3.WA.locRing P) (h (b0 i) (b0 i)) := by
    intro i
    have hσ := (Formalism.HermitianLattices.Ext.L3.LocF.isUnitIn_algebraMap_iff hP.isPrime (s i)).2 (hsP i)
    have hσs := (Formalism.HermitianLattices.Ext.L3.LocF.isUnitIn_algebraMap_iff hP.isPrime (conjO K (s i))).2
      (Formalism.HermitianLattices.Ext.L3.WA.conjO_mem_hcompl (hsP i))
    rw [hbb]
    exact isUnitIn_mul' (isUnitIn_mul' hσs hσ) (hxu i)
  have horth : ∀ i j, i ≠ j → h (b0 i) (b0 j) = 0 := by
    intro i j hij
    rw [hbb, hxo i j hij, mul_zero]
  have hint : ∀ i, h (b0 i) (b0 i) ∈ (1 : Submodule (𝓞 K) K) := fun i => hLi _ (hb0L i) _ (hb0L i)
  choose u hu using fun i => Submodule.mem_one.1 (hint i)
  have huP : ∀ i, u i ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) P := by
    intro i
    refine (Formalism.HermitianLattices.Ext.L3.LocF.isUnitIn_algebraMap_iff hP.isPrime (u i)).1 ?_
    rw [hu i]
    exact hunit i
  have hli : LinearIndependent K b0 := by
    rw [linearIndependent_iff']
    intro t g hg i hi
    have := congrArg (h (b0 i)) hg
    rw [map_sum, map_zero, Finset.sum_eq_single i] at this
    · rw [map_smul, smul_eq_mul] at this
      exact (mul_eq_zero.1 this).resolve_right (hunit i).1
    · intro j _ hji
      rw [map_smul, horth i j (Ne.symm hji), smul_zero]
    · intro hi'
      exact absurd hi hi'
  have htop : ⊤ ≤ Submodule.span K (Set.range b0) :=
    (Submodule.eq_top_of_finrank_eq (by rw [finrank_span_eq_card hli, Fintype.card_fin])).ge
  let b := Basis.mk hli htop
  have hb : ⇑b = b0 := Basis.coe_mk hli htop
  refine ⟨b, u, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [hb]
    exact hb0L i
  · rw [hb, locF_eq_loc hK hF hP, locF_eq_loc hK hF hP]
    apply le_antisymm
    · rintro y ⟨t, ht, hy⟩
      exact ⟨t, ht, (Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hb0L i)) hy⟩
    · rintro y ⟨t, ht, hy⟩
      have hz : t • y ∈ Formalism.HermitianLatticesTheory.loc (K := K) P (Submodule.span (𝓞 K) (Set.range b0)) := by
        rw [← b.sum_repr (t • y)]
        refine Submodule.sum_mem _ fun i _ => ?_
        refine ⟨u i, huP i, ?_⟩
        obtain ⟨a, ha⟩ := Submodule.mem_one.1 (hLi _ (hb0L i) _ hy)
        have hrep : h (b0 i) (t • y) = b.repr (t • y) i * h (b0 i) (b0 i) := by
          conv_lhs => rw [← b.sum_repr (t • y)]
          rw [map_sum, Finset.sum_eq_single i]
          · rw [map_smul, smul_eq_mul, hb]
          · intro j _ hji
            rw [map_smul, hb, horth i j (Ne.symm hji), smul_zero]
          · intro hi
            exact absurd (Finset.mem_univ i) hi
        have key : u i • (b.repr (t • y) i • b i) = a • b0 i := by
          rw [← algebraMap_smul K (u i), smul_smul, hu i, mul_comm, ← hrep, ← ha, algebraMap_smul, hb]
        rw [key]
        exact Submodule.smul_mem _ a (Submodule.subset_span ⟨i, rfl⟩)
      obtain ⟨t', ht', hy'⟩ := hz
      exact ⟨t' * t, mul_mem ht' ht, by rw [mul_smul]; exact hy'⟩
  · intro i j
    rw [hb, Matrix.diagonal_apply]
    split_ifs with hij
    · subst hij
      exact hu i
    · rw [map_zero, horth i j hij]
  · intro i
    apply IsFractionRing.injective (𝓞 K) K
    have h1 : algebraMap (𝓞 K) K (conjO K (u i)) = star (algebraMap (𝓞 K) K (u i)) := rfl
    rw [h1, hu i, ← starRingEnd_apply]
    exact hs.eq (b0 i) (b0 i)
  · intro i
    exact sup_eq_top_of_mem_hcompl hK hF hP (huP i)

end Formalism.HermitianLattices.Ext.L3.OrthogonalBases
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.TendstoSumPeriodic
section
open NumberField Module Filter Topology
open scoped Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.BoxSum

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem finite_quot {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) : Finite (𝓞 F ⧸ I) :=
  Ideal.finiteQuotientOfFreeOfNeBot I hI

theorem exists_crt {b 𝔞 : Ideal (𝓞 F)} (hco : b ⊔ 𝔞 = ⊤) (x₀ : 𝓞 F) (c : 𝓞 F ⧸ 𝔞) :
    ∃ x : 𝓞 F, x - x₀ ∈ b ∧ Ideal.Quotient.mk 𝔞 x = c := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective c
  have h1 : (1 : 𝓞 F) ∈ b ⊔ 𝔞 := by rw [hco]; exact Submodule.mem_top
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp h1
  refine ⟨x₀ * v + y * u, ?_, ?_⟩
  · have e : x₀ * v + y * u - x₀ = (y - x₀) * u := by linear_combination x₀ * huv
    rw [e]
    exact b.mul_mem_left _ hu
  · rw [Ideal.Quotient.eq]
    have e : x₀ * v + y * u - y = (x₀ - y) * v := by linear_combination y * huv
    rw [e]
    exact 𝔞.mul_mem_left _ hv

theorem sum_split (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (T : ℝ) {b 𝔞 : Ideal (𝓞 F)}
    [Fintype (𝓞 F ⧸ 𝔞)] (hco : b ⊔ 𝔞 = ⊤) (x₀ : 𝓞 F) (g : 𝓞 F → ℝ) (φ : 𝓞 F ⧸ 𝔞 → ℝ)
    (x : 𝓞 F ⧸ 𝔞 → 𝓞 F) (hx : ∀ c, x c - x₀ ∈ b ∧ Ideal.Quotient.mk 𝔞 (x c) = c) :
    ∑ᶠ n ∈ {n : 𝓞 F | n ∈ boxSet K F T ∧ n - x₀ ∈ b}, g n * φ (Ideal.Quotient.mk 𝔞 n) =
      ∑ c, φ c * ∑ᶠ n ∈ {n : 𝓞 F | n ∈ boxSet K F T ∧ n - x c ∈ b * 𝔞}, g n := by
  set S := {n : 𝓞 F | n ∈ boxSet K F T ∧ n - x₀ ∈ b} with hSdef
  have hS : S.Finite := finite_box_inter hK hF T {n | n - x₀ ∈ b}
  have hT : ∀ c, {n : 𝓞 F | n ∈ boxSet K F T ∧ n - x c ∈ b * 𝔞} = {n | n ∈ S ∧ Ideal.Quotient.mk 𝔞 n = c} := by
    intro c
    ext n
    simp only [Set.mem_setOf_eq, hSdef]
    rw [Ideal.mul_eq_inf_of_coprime hco, Ideal.mem_inf]
    constructor
    · rintro ⟨hn, h1, h2⟩
      refine ⟨⟨hn, ?_⟩, ?_⟩
      · have := b.add_mem h1 (hx c).1
        rwa [sub_add_sub_cancel] at this
      · rw [← (hx c).2]
        exact Ideal.Quotient.eq.mpr h2
    · rintro ⟨⟨hn, h1⟩, h2⟩
      refine ⟨hn, ?_, ?_⟩
      · have := b.sub_mem h1 (hx c).1
        rwa [sub_sub_sub_cancel_right] at this
      · rw [← (hx c).2] at h2
        exact Ideal.Quotient.eq.mp h2
  have hSc : ∀ c, ({n | n ∈ S ∧ Ideal.Quotient.mk 𝔞 n = c} : Set (𝓞 F)).Finite :=
    fun c => hS.subset fun n hn => hn.1
  rw [finsum_mem_eq_finite_toFinset_sum _ hS, ← Finset.sum_fiberwise hS.toFinset (Ideal.Quotient.mk 𝔞)]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [hT c, finsum_mem_eq_finite_toFinset_sum _ (hSc c), Finset.mul_sum]
  have e : (hSc c).toFinset = hS.toFinset.filter (fun n => Ideal.Quotient.mk 𝔞 n = c) := by
    ext n
    simp
  rw [e]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [(Finset.mem_filter.mp hn).2, mul_comm]

theorem tendsto_sum_periodic (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {m : ℕ} (hm : 1 ≤ m)
    (k : ℕ) (φ : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, (𝓞 F ⧸ 𝔭.1 ^ k) → ℝ)
    (S : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) :
    ∀ (b : Ideal (𝓞 F)), b ≠ ⊥ → (∀ 𝔭 ∈ S, b ⊔ 𝔭.1 = ⊤) → ∀ x₀ : 𝓞 F,
    Tendsto (fun j : ℕ => ((j : ℝ) ^ 2) ^ (-((Formalism.HermitianLatticesTheory.fDeg K * m : ℕ) : ℤ)) *
        ∑ᶠ n ∈ {n : 𝓞 F | n ∈ boxSet K F ((j : ℝ) ^ 2) ∧ n - x₀ ∈ b},
          (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1) *
            ∏ 𝔭 ∈ S, φ 𝔭 (Ideal.Quotient.mk (𝔭.1 ^ k) n))
      atTop (𝓝 ((m : ℝ) ^ (-(Formalism.HermitianLatticesTheory.fDeg K : ℤ)) /
        Real.sqrt ((2 * Formalism.HermitianLatticesTheory.vInv K) ^ Formalism.HermitianLatticesTheory.fDeg K) / (Ideal.absNorm b : ℝ) *
          ∏ 𝔭 ∈ S, ((Ideal.absNorm 𝔭.1 : ℝ) ^ (-(k : ℤ)) * ∑ᶠ c, φ 𝔭 c))) := by
  induction S using Finset.induction_on with
  | empty =>
    intro b hb _ x₀
    have := tendsto_sum_coset hK hF hm hb x₀
    simp only [Finset.prod_empty, mul_one]
    exact this
  | insert 𝔮 S' h𝔮S ih =>
    intro b hb hcop x₀
    have h𝔮0 : 𝔮.1 ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField 𝔮.2 (RingOfIntegers.not_isField F)
    have h𝔞0 : 𝔮.1 ^ k ≠ ⊥ := by
      have h0 : 𝔮.1 ≠ 0 := by simpa only [Ideal.zero_eq_bot] using h𝔮0
      simpa only [Ideal.zero_eq_bot] using pow_ne_zero k h0
    haveI : Fintype (𝓞 F ⧸ 𝔮.1 ^ k) := @Fintype.ofFinite _ (finite_quot h𝔞0)
    have hco : b ⊔ 𝔮.1 ^ k = ⊤ := by
      have h1 : IsCoprime b 𝔮.1 := Ideal.isCoprime_iff_sup_eq.mpr (hcop 𝔮 (Finset.mem_insert_self _ _))
      exact Ideal.isCoprime_iff_sup_eq.mp h1.pow_right
    choose x hx using fun c => exists_crt hco x₀ c
    have hb' : b * 𝔮.1 ^ k ≠ ⊥ := by
      have h0 : b ≠ 0 := by simpa only [Ideal.zero_eq_bot] using hb
      have h1 : 𝔮.1 ^ k ≠ 0 := by simpa only [Ideal.zero_eq_bot] using h𝔞0
      simpa only [Ideal.zero_eq_bot] using mul_ne_zero h0 h1
    have hcop' : ∀ 𝔭 ∈ S', b * 𝔮.1 ^ k ⊔ 𝔭.1 = ⊤ := by
      intro 𝔭 h𝔭
      have h1 : IsCoprime b 𝔭.1 := Ideal.isCoprime_iff_sup_eq.mpr (hcop 𝔭 (Finset.mem_insert_of_mem h𝔭))
      have hne : 𝔮.1 ≠ 𝔭.1 := fun e => h𝔮S ((Subtype.ext e : 𝔮 = 𝔭) ▸ h𝔭)
      have h2 : IsCoprime 𝔮.1 𝔭.1 := Ideal.isCoprime_iff_sup_eq.mpr (Ideal.IsMaximal.coprime_of_ne 𝔮.2 𝔭.2 hne)
      have h3 : IsCoprime (𝔮.1 ^ k) 𝔭.1 := h2.pow_left
      exact Ideal.isCoprime_iff_sup_eq.mp (h1.mul_left h3)
    have hlim := fun c => ih (b * 𝔮.1 ^ k) hb' hcop' (x c)

    have hsplit : ∀ j : ℕ, ∑ᶠ n ∈ {n : 𝓞 F | n ∈ boxSet K F ((j : ℝ) ^ 2) ∧ n - x₀ ∈ b},
        (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1) * ∏ 𝔭 ∈ insert 𝔮 S', φ 𝔭 (Ideal.Quotient.mk (𝔭.1 ^ k) n) =
        ∑ c, φ 𝔮 c * ∑ᶠ n ∈ {n : 𝓞 F | n ∈ boxSet K F ((j : ℝ) ^ 2) ∧ n - x c ∈ b * 𝔮.1 ^ k},
          (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1) * ∏ 𝔭 ∈ S', φ 𝔭 (Ideal.Quotient.mk (𝔭.1 ^ k) n) := by
      intro j
      rw [← sum_split hK hF _ hco x₀ (fun n => (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1) *
        ∏ 𝔭 ∈ S', φ 𝔭 (Ideal.Quotient.mk (𝔭.1 ^ k) n)) (φ 𝔮) x hx]
      refine finsum_mem_congr rfl fun n _ => ?_
      rw [Finset.prod_insert h𝔮S]
      ring
    have hT := tendsto_finset_sum (Finset.univ : Finset (𝓞 F ⧸ 𝔮.1 ^ k)) fun c _ => (hlim c).const_mul (φ 𝔮 c)
    convert hT using 1
    · funext j
      rw [hsplit j, Finset.mul_sum]
      exact Finset.sum_congr rfl fun c _ => by ring
    · congr 1
      rw [Finset.prod_insert h𝔮S, finsum_eq_sum_of_fintype]
      simp only [map_mul, map_pow, Nat.cast_mul, Nat.cast_pow, zpow_neg, zpow_natCast, Finset.mul_sum,
        Finset.sum_mul]
      refine Finset.sum_congr rfl fun c _ => ?_
      ring

end Formalism.HermitianLattices.Ext.L3.BoxSum
end
end

