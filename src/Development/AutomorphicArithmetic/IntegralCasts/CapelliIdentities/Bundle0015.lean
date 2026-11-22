import Mathlib

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ElementDenominator
section
theorem UpperTheory.Reformulated.B.ElementDenominator.eltDen.{u_1, u_2, u_3} :
    ∀ {K : Type u_1} [inst : Field K] {R : Type u_2} [inst_1 : CommRing R] [IsDomain R] [inst_3 : Algebra R K]
    [IsFractionRing R K] {V : Type u_3} [inst_5 : AddCommGroup V] [inst_6 : _root_.Module K V]
    [inst_7 : _root_.Module R V] [IsScalarTower R K V] (Y : Submodule R V) {y : V},
    y ∈ Submodule.span K (↑Y : Set V) → ∃ (s : R), s ≠ (0 : R) ∧ s • y ∈ Y := by
  intro K _ R _ _ _ _ V _ _ _ _ Y y hy
  induction hy using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hx⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact Y.zero_mem⟩
  | add x z _ _ hx hz =>
    obtain ⟨s, hs, hsx⟩ := hx
    obtain ⟨t, ht, htz⟩ := hz
    refine ⟨s * t, mul_ne_zero hs ht, ?_⟩
    rw [smul_add]
    refine Y.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact Y.smul_mem t hsx
    · rw [mul_smul]
      exact Y.smul_mem s htz
  | smul c x _ hx =>
    obtain ⟨s, hs, hsx⟩ := hx
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors R) c
    refine ⟨s * (b : R), mul_ne_zero hs (nonZeroDivisors.coe_ne_zero b), ?_⟩
    have h1 : (b : R) • (c • x) = a • x := by
      rw [← algebraMap_smul K (b : R) (c • x), smul_smul, mul_comm, hab, algebraMap_smul]
    rw [mul_smul, h1, smul_comm]
    exact Y.smul_mem a hsx
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ElementarySymmetricInverse
section
private theorem aux {ι : Type*} [DecidableEq ι] (t : Finset ι) (f : ι → ℂ)
    (hf : ∀ i ∈ t, f i ≠ 0) (j : ℕ) (hj : j ≤ t.card) :
    (t.val.map (fun i => (f i)⁻¹)).esymm j * (t.val.map f).prod
      = (t.val.map f).esymm (t.card - j) := by
  rw [Finset.esymm_map_val, Finset.esymm_map_val, Finset.sum_mul]
  refine Finset.sum_nbij' (fun u => t \ u) (fun u => t \ u) ?_ ?_ ?_ ?_ ?_
  · intro u hu
    rw [Finset.mem_powersetCard] at hu ⊢
    exact ⟨Finset.sdiff_subset, by rw [Finset.card_sdiff_of_subset hu.1, hu.2]⟩
  · intro u hu
    rw [Finset.mem_powersetCard] at hu ⊢
    exact ⟨Finset.sdiff_subset, by rw [Finset.card_sdiff_of_subset hu.1, hu.2]; omega⟩
  · intro u hu
    rw [Finset.mem_powersetCard] at hu
    exact Finset.sdiff_sdiff_eq_self hu.1
  · intro u hu
    rw [Finset.mem_powersetCard] at hu
    exact Finset.sdiff_sdiff_eq_self hu.1
  · intro u hu
    rw [Finset.mem_powersetCard] at hu
    have h1 : (t.val.map f).prod = (∏ i ∈ t \ u, f i) * ∏ i ∈ u, f i :=
      (Finset.prod_sdiff hu.1).symm
    have h2 : (∏ i ∈ u, f i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i hi => hf i (hu.1 hi)
    rw [h1, Finset.prod_inv_distrib]
    field_simp

theorem UpperTheory.Reformulated.B.EsymmMapInvMulProd.esymm_inv :
    ∀ (s : Multiset ℂ),
    (∀ x ∈ s, x ≠ (0 : ℂ)) →
      ∀ j ≤ s.card, (Multiset.map (fun (x : ℂ) ↦ x⁻¹) s).esymm j * s.prod = s.esymm (s.card - j) := by
  intro s hs j hj
  classical
  have e : (Finset.univ : Finset s.ToType).val.map (fun x : s.ToType => (x : ℂ)) = s :=
    Multiset.map_univ_coe s
  have c : (Finset.univ : Finset s.ToType).card = s.card := by
    rw [Finset.card_univ, Multiset.card_coe]
  have h := aux (Finset.univ : Finset s.ToType) (fun x : s.ToType => (x : ℂ))
    (fun i _ => hs _ (Multiset.coe_mem)) j (by rw [c]; exact hj)
  have e2 : (Finset.univ : Finset s.ToType).val.map (fun x : s.ToType => ((x : ℂ))⁻¹)
      = s.map (fun x : ℂ => x⁻¹) := by
    conv_rhs => rw [← e]
    rw [Multiset.map_map]
    rfl
  rw [e2, e, c] at h
  exact h
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EmbTwo
section
theorem UpperTheory.Reformulated.B.Qe21.emb_two :
    ∀ {K M : Type} [inst : Field K] [NumberField K]
    [inst_2 : Field M] [NumberField M] [inst_4 : Algebra K M] [IsGalois K M],
    Module.finrank K M = (2 : ℕ) →
      ∀ (σ : Gal(M/K)),
        σ ≠ (1 : Gal(M/K)) →
          ∀ (τ τ' : M →+* ℂ),
            τ ≠ τ' →
              τ.comp (Algebra.algebraMap K M) = τ'.comp (Algebra.algebraMap K M) →
                τ.comp σ.toRingEquiv.toRingHom = τ' := by
  intro K M _ _ _ _ _ _ h2 σ hσ τ τ' hne hc
  obtain ⟨ρ, hρ⟩ := NumberField.ComplexEmbedding.exists_comp_symm_eq_of_comp_eq τ τ' hc
  have hcard : Nat.card Gal(M/K) = 2 := by
    rw [IsGalois.card_aut_eq_finrank, h2]
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : Gal(M/K))).1 hcard
  have h1 : ρ.symm ≠ 1 := by
    intro h
    apply hne
    rw [← hρ, h]
    ext x
    rfl
  have h3 : σ = ρ.symm := (hy σ hσ).trans (hy _ h1).symm
  rw [← hρ, h3]
  ext x
  rfl
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EqOfNatCastMem
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.Yza3.Pl :
    Type :=
    IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)

noncomputable def UpperTheory.Reformulated.B.Yza3.normV.{u_1} :
    {F : Type u_1} → [inst : Field F] → IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) → ℕ :=
    fun {F : Type u_1} [Field F] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) ↦
      Nat.card (NumberField.RingOfIntegers F ⧸ v.asIdeal)

namespace UpperTheory.Reformulated.B.Yza3

open NumberField in
private lemma exists_prime_gen (v : Pl) :
    ∃ p : ℕ, p.Prime ∧ v.asIdeal = Ideal.span {(p : 𝓞 ℚ)} := by
  classical
  let e : 𝓞 ℚ ≃+* ℤ := Rat.ringOfIntegersEquiv
  have hprime : v.asIdeal.IsPrime := v.isPrime
  obtain ⟨g, hg⟩ : ∃ g : 𝓞 ℚ, v.asIdeal = Ideal.span {g} :=
    haveI : IsPrincipalIdealRing (𝓞 ℚ) :=
      IsPrincipalIdealRing.of_surjective e.symm.toRingHom e.symm.surjective
    (IsPrincipalIdealRing.principal v.asIdeal).principal
  have hg0 : g ≠ 0 := by
    rintro rfl
    exact v.ne_bot (by simpa using hg)
  have hgp : Prime g := by
    rw [← Ideal.span_singleton_prime hg0, ← hg]
    exact hprime
  have hep : Prime (e g) := (MulEquiv.prime_iff e.toMulEquiv).2 hgp
  refine ⟨(e g).natAbs, Int.prime_iff_natAbs_prime.1 hep, ?_⟩
  rw [hg]
  have hassoc : Associated (e g) (((e g).natAbs : ℕ) : ℤ) := (Int.associated_natAbs _)
  have : Associated g (((e g).natAbs : ℕ) : 𝓞 ℚ) := by
    have h2 := hassoc.map e.symm.toMonoidHom
    generalize (e g).natAbs = n at h2 ⊢
    have h3 : e.symm.toMonoidHom (e g) = g := e.symm_apply_apply g
    have h4 : e.symm.toMonoidHom ((n : ℕ) : ℤ) = (n : 𝓞 ℚ) := map_natCast e.symm n
    rwa [h3, h4] at h2
  exact Ideal.span_singleton_eq_span_singleton.2 this

open NumberField in
private lemma eq_of_natCast_mem {p : ℕ} (hp : p.Prime) (v v' : Pl)
    (h : (p : 𝓞 ℚ) ∈ v.asIdeal) (h' : (p : 𝓞 ℚ) ∈ v'.asIdeal) : v = v' := by
  have key : ∀ u : Pl, (p : 𝓞 ℚ) ∈ u.asIdeal → u.asIdeal = Ideal.span {(p : 𝓞 ℚ)} := by
    intro u hu
    obtain ⟨q, hq, huq⟩ := exists_prime_gen u
    rw [huq] at hu ⊢
    have hd : (q : 𝓞 ℚ) ∣ (p : 𝓞 ℚ) := Ideal.mem_span_singleton.1 hu
    have hd' : (q : ℤ) ∣ (p : ℤ) := by
      have := map_dvd (Rat.ringOfIntegersEquiv : 𝓞 ℚ ≃+* ℤ) hd
      simpa using this
    have : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).1 (Int.natCast_dvd_natCast.1 hd')
    rw [this]
  exact IsDedekindDomain.HeightOneSpectrum.ext ((key v h).trans (key v' h').symm)

open NumberField in
theorem htc_places :
    ∀ (w : UpperTheory.Reformulated.B.Yza3.Pl),
      UpperTheory.Reformulated.B.Yza3.normV w ≠ (0 : ℕ) ∧
        (∀ (v : UpperTheory.Reformulated.B.Yza3.Pl), v ≠ w → (↑(UpperTheory.Reformulated.B.Yza3.normV w) : NumberField.RingOfIntegers ℚ) ∉ v.asIdeal) ∧
          ∀ (p : ℕ),
            Nat.Prime p →
              ∀ (v v' : UpperTheory.Reformulated.B.Yza3.Pl),
                (↑p : NumberField.RingOfIntegers ℚ) ∈ v.asIdeal → (↑p : NumberField.RingOfIntegers ℚ) ∈ v'.asIdeal → v = v' := by
  intro w
  obtain ⟨p, hp, hw⟩ := exists_prime_gen w
  have hnorm : normV w = p := by
    have h1 : normV w = Ideal.absNorm w.asIdeal := by
      simp [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rw [h1, hw, Ideal.absNorm_span_singleton]
    have : ((p : 𝓞 ℚ)) = algebraMap ℤ (𝓞 ℚ) (p : ℤ) := by simp
    rw [this, Algebra.norm_algebraMap, RingOfIntegers.rank]
    simp
  refine ⟨by rw [hnorm]; exact hp.ne_zero, ?_, fun q hq v v' => eq_of_natCast_mem hq v v'⟩
  intro v hvw hmem
  rw [hnorm] at hmem
  refine hvw (eq_of_natCast_mem hp v w hmem ?_)
  rw [hw]
  exact Ideal.mem_span_singleton_self _

end UpperTheory.Reformulated.B.Yza3
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EqOneOfForallZpow
section
private theorem UpperTheory.Reformulated.B.Qk23.half_le_re {w : ℂ} (h : ‖w⁻¹ - 1‖ < 1) : (1 / 2 : ℝ) ≤ w.re := by
  have hw : w ≠ 0 := by
    rintro rfl
    simp at h
  have e : w⁻¹ - 1 = (1 - w) / w := by field_simp
  rw [e, norm_div, div_lt_one (norm_pos_iff.mpr hw)] at h
  have h2 : ‖1 - w‖ ^ 2 < ‖w‖ ^ 2 := by
    have := norm_nonneg (1 - w)
    nlinarith
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply] at h2
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im] at h2
  nlinarith

theorem UpperTheory.Reformulated.B.Qk23.eq_one_of_forall_zpow :
    ∀ {z : ℂ}, (∀ (k : ℤ), ‖z ^ k - (1 : ℂ)‖ < (1 : ℝ)) → z = (1 : ℂ) := by
  intro z h
  by_contra hz
  have hd : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
  have hre : ∀ k : ℕ, (1 / 2 : ℝ) ≤ (z ^ k).re := by
    intro k
    apply UpperTheory.Reformulated.B.Qk23.half_le_re
    have := h (-(k : ℤ))
    rwa [zpow_neg, zpow_natCast] at this
  obtain ⟨n, hn⟩ := exists_nat_gt (2 / ‖z - 1‖)
  rw [div_lt_iff₀ hd] at hn
  have h1 : (n : ℝ) * (1 / 2) ≤ ‖∑ k ∈ Finset.range n, z ^ k‖ := by
    refine le_trans ?_ (Complex.re_le_norm _)
    rw [Complex.re_sum]
    have := Finset.card_nsmul_le_sum (Finset.range n) (fun k => (z ^ k).re) (1 / 2 : ℝ)
      (fun k _ => hre k)
    rwa [Finset.card_range, nsmul_eq_mul] at this
  have h2 : ‖∑ k ∈ Finset.range n, z ^ k‖ * ‖z - 1‖ < 1 := by
    rw [← norm_mul, geom_sum_mul]
    have := h (n : ℤ)
    rwa [zpow_natCast] at this
  have h3 := mul_le_mul_of_nonneg_right h1 hd.le
  linarith
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EqOneOfNear
section
namespace UpperTheory.Reformulated.B.S7

theorem eq_one_of_near {l : ℕ} [Fact l.Prime] {u : PadicAlgCl l} {m : ℕ} (hm : ¬ l ∣ m) (hu : u ^ m = 1)
    (h : ‖u - 1‖ < 1) : u = 1 := by
  by_contra hne
  have hu1 : ‖u‖ ≤ 1 := by
    have := IsUltrametricDist.norm_add_le_max (u - 1) 1
    rw [sub_add_cancel, norm_one] at this
    exact this.trans (max_le h.le le_rfl)
  have hpow : ∀ i : ℕ, ‖u ^ i - 1‖ < 1 := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have e : u ^ (i + 1) - 1 = (u ^ i - 1) * u + (u - 1) := by ring
      rw [e]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ h)
      rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) hu1).trans_lt ih
  have hsum : ∀ n : ℕ, ‖(∑ i ∈ Finset.range n, u ^ i) - (n : PadicAlgCl l)‖ < 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have e : (∑ i ∈ Finset.range (n + 1), u ^ i) - ((n + 1 : ℕ) : PadicAlgCl l)
          = ((∑ i ∈ Finset.range n, u ^ i) - (n : PadicAlgCl l)) + (u ^ n - 1) := by
        rw [Finset.sum_range_succ]; push_cast; ring
      rw [e]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ih (hpow n))
  have h0 : (∑ i ∈ Finset.range m, u ^ i) = 0 := by
    have := geom_sum_mul u m
    rw [hu, sub_self] at this
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hne)
  have hlt := hsum m
  rw [h0, zero_sub, norm_neg] at hlt
  have e : (m : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (m : ℚ_[l]) := by simp
  rw [e, norm_algebraMap'] at hlt
  exact hm (Padic.norm_natCast_lt_one_iff.mp hlt)

end UpperTheory.Reformulated.B.S7
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EqOneOfPowNear
section
theorem UpperTheory.Reformulated.B.EqOneOfPowNear.eq_one_of_pow_near :
    ∀ (z : ℂ),
    (∀ (n : ℕ), ‖z ^ n - (1 : ℂ)‖ < (1 / 2 : ℝ)) → z = (1 : ℂ) := by
  intro z h
  have step : ∀ n : ℕ, (3 / 2 : ℝ) * ‖z ^ n - 1‖ ≤ ‖z ^ (n * 2) - 1‖ := by
    intro n
    have e : z ^ (n * 2) - 1 = (z ^ n + 1) * (z ^ n - 1) := by ring
    have h1 : ‖(2 : ℂ)‖ ≤ ‖z ^ n + 1‖ + ‖z ^ n - 1‖ := by
      have e2 : (2 : ℂ) = (z ^ n + 1) - (z ^ n - 1) := by ring
      calc ‖(2 : ℂ)‖ = ‖(z ^ n + 1) - (z ^ n - 1)‖ := congrArg _ e2
        _ ≤ _ := norm_sub_le _ _
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    have h3 := h n
    rw [e, norm_mul]
    exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
  have grow : ∀ k : ℕ, (3 / 2 : ℝ) ^ k * ‖z - 1‖ ≤ ‖z ^ (2 ^ k) - 1‖ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have s := step (2 ^ k)
      rw [pow_succ, pow_succ]
      linarith
  by_contra hz
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ((1 / 2 : ℝ) / ‖z - 1‖) (by norm_num : (1 : ℝ) < 3 / 2)
  rw [div_lt_iff₀ hpos] at hk
  have g := grow k
  have h4 := h (2 ^ k)
  linarith
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EqZeroOfAevalEqZero
section
noncomputable def UpperTheory.Reformulated.B.G8.kry :
    {R : Type} → [CommRing R] → {n : ℕ} → Matrix (Fin n) (Fin n) R → (Fin n → R) → Matrix (Fin n) (Fin n) R :=
    fun {R : Type} [CommRing R] {n : ℕ} (g : Matrix (Fin n) (Fin n) R) (v : Fin n → R) ↦
      (Matrix.of : (Fin n → Fin n → R) → Matrix (Fin n) (Fin n) R) fun (i j : Fin n) ↦ (g ^ (↑j : ℕ)).mulVec v i

open Polynomial in
private theorem UpperTheory.Reformulated.B.G8.eq_zero_of_aeval_eq_zero {K : Type} [Field K] {n : ℕ}
    (g : Matrix (Fin n) (Fin n) K) (hg : g.charpoly.Separable) (p : K[X])
    (hp : p.degree < n) (h0 : aeval g p = 0) : p = 0 := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using hp
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let L := AlgebraicClosure K
  let f : K →+* L := algebraMap K L
  let G : Matrix (Fin n) (Fin n) L := g.map f
  have hG : G.charpoly.Separable := by
    rw [Matrix.charpoly_map]
    exact hg.map
  have hG0 : aeval G (p.map f) = 0 := by
    have h1 := congrArg (AlgHom.mapMatrix (m := Fin n) (Algebra.ofId K L)) h0
    rw [map_zero, ← aeval_algHom_apply] at h1
    rw [aeval_map_algebraMap]
    exact h1
  have hcard : G.charpoly.roots.toFinset.card = n := by
    rw [Multiset.toFinset_card_of_nodup (nodup_roots hG), ← (IsAlgClosed.splits G.charpoly).natDegree_eq_card_roots,
      Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hz : p.map f = 0 := by
    refine eq_zero_of_degree_lt_of_eval_finset_eq_zero G.charpoly.roots.toFinset ?_ ?_
    · rw [hcard, degree_map]
      exact hp
    · intro x hx
      have hx' : x ∈ spectrum L G :=
        Matrix.mem_spectrum_of_isRoot_charpoly (isRoot_of_mem_roots (Multiset.mem_toFinset.mp hx))
      have h2 := spectrum.subset_polynomial_aeval G (p.map f) ⟨x, hx', rfl⟩
      rw [hG0, spectrum.zero_eq] at h2
      exact h2
  exact (Polynomial.map_eq_zero_iff f.injective).mp hz

open Polynomial in
private theorem UpperTheory.Reformulated.B.G8.exists_kry_field {K : Type} [Field K] {n : ℕ}
    (g : Matrix (Fin n) (Fin n) K) (hg : g.charpoly.Separable) :
    ∃ v : Fin n → K, (UpperTheory.Reformulated.B.G8.kry g v).det ≠ 0 := by
  classical
  obtain ⟨x, hx⟩ := Module.exists_ker_toSpanSingleton_eq_annihilator K[X]
    (Module.AEval K (Fin n → K) g)
  obtain ⟨v, rfl⟩ := (Module.AEval.of K (Fin n → K) g).surjective x
  refine ⟨v, fun hdet => ?_⟩
  obtain ⟨c, hc, hc0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  let p : K[X] := ∑ j : Fin n, C (c j) * X ^ (j : ℕ)
  have hdeg : p.degree < n := degree_sum_fin_lt c
  have hv : aeval g p • v = 0 := by
    rw [← hc0]
    ext i
    simp only [p, map_sum, map_mul, aeval_C, map_pow, aeval_X, Finset.sum_smul, Finset.sum_apply,
      ← Algebra.smul_def, smul_assoc, Pi.smul_apply, smul_eq_mul, Matrix.smul_eq_mulVec]
    simp only [UpperTheory.Reformulated.B.G8.kry, Matrix.mulVec, dotProduct, Matrix.of_apply]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hker : p ∈ Module.annihilator K[X] (Module.AEval K (Fin n → K) g) := by
    rw [← hx, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, ← Module.AEval.of_aeval_smul,
      hv, map_zero]
  have hp0 : aeval g p = 0 := by
    refine Matrix.ext_iff_mulVec.mpr fun w => ?_
    have h1 := Module.mem_annihilator.mp hker (Module.AEval.of K (Fin n → K) g w)
    rw [← Module.AEval.of_aeval_smul, map_eq_zero_iff _ (LinearEquiv.injective _)] at h1
    rw [Matrix.zero_mulVec]
    exact h1
  have hp : p = 0 := UpperTheory.Reformulated.B.G8.eq_zero_of_aeval_eq_zero g hg p hdeg hp0
  apply hc
  ext j
  have h1 := congrArg (fun q => q.coeff j) hp
  simpa [p, finsetSum_coeff, coeff_X_pow, Fin.val_inj] using h1

private theorem UpperTheory.Reformulated.B.G8.kry_map {R S : Type} [CommRing R] [CommRing S] {n : ℕ} (f : R →+* S)
    (g : Matrix (Fin n) (Fin n) R) (v : Fin n → R) :
    f (UpperTheory.Reformulated.B.G8.kry g v).det = (UpperTheory.Reformulated.B.G8.kry (g.map f) (f ∘ v)).det := by
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp only [UpperTheory.Reformulated.B.G8.kry, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
  rw [RingHom.map_mulVec, Matrix.map_pow]

theorem UpperTheory.Reformulated.B.G8.exists_kry :
    ∀ {R : Type} [inst : CommRing R] [Finite (MaximalSpectrum R)] {n : ℕ} (g : Matrix (Fin n) (Fin n) R),
      g.charpoly.Separable → ∃ (v : Fin n → R), IsUnit (UpperTheory.Reformulated.B.G8.kry g v).det := by
  intro R _ _ n g hg
  have h1 : ∀ m : MaximalSpectrum R, ∃ w : Fin n → R ⧸ m.asIdeal,
      (UpperTheory.Reformulated.B.G8.kry (g.map (Ideal.Quotient.mk m.asIdeal)) w).det ≠ 0 := by
    intro m
    haveI := m.isMaximal
    letI := Ideal.Quotient.field m.asIdeal
    refine UpperTheory.Reformulated.B.G8.exists_kry_field _ ?_
    rw [Matrix.charpoly_map]
    exact hg.map
  choose w hw using h1
  have hco : Pairwise (Function.onFun IsCoprime fun m : MaximalSpectrum R => m.asIdeal) := by
    intro a b hab
    exact Ideal.isCoprime_iff_sup_eq.mpr
      (a.isMaximal.coprime_of_ne b.isMaximal fun h => hab (MaximalSpectrum.ext h))
  choose v hv using fun i : Fin n => Ideal.pi_quotient_surjective hco fun m => w m i
  refine ⟨v, ?_⟩
  by_contra hu
  obtain ⟨M, hM, hmem⟩ := exists_max_ideal_of_mem_nonunits hu
  apply hw ⟨M, hM⟩
  have h2 : w ⟨M, hM⟩ = Ideal.Quotient.mk M ∘ v := funext fun i => (hv i ⟨M, hM⟩).symm
  rw [h2, ← UpperTheory.Reformulated.B.G8.kry_map]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EvDecomp
section
theorem UpperTheory.Reformulated.B.Qf39.ev_decomp :
    ∀ {O σ : Type} [inst : CommRing O] [inst_1 : Fintype σ]
    (f : MvPowerSeries σ O),
    ∃ (h : σ → MvPowerSeries σ O),
      f =
          (MvPowerSeries.C : O → MvPowerSeries σ O) ((MvPowerSeries.constantCoeff : MvPowerSeries σ O → O) f) +
            ∑ i : σ, MvPowerSeries.X i * h i ∧
        ∀ (i : σ),
          (MvPowerSeries.constantCoeff : MvPowerSeries σ O → O) (h i) =
            (MvPowerSeries.coeff fun₀ | i => (1 : ℕ) : MvPowerSeries σ O → O) f := by
  intro O σ _ _ f
  classical
  have key : ∀ m : σ →₀ ℕ, ∃ o : Option σ,
      (m ≠ 0 → ∃ j, o = some j) ∧ ∀ j, o = some j → m j ≠ 0 := by
    intro m
    by_cases hm : m = 0
    · exact ⟨none, fun h => (h hm).elim, fun j hj => by cases hj⟩
    · obtain ⟨j, hj⟩ := Finsupp.ne_iff.1 hm
      refine ⟨some j, fun _ => ⟨j, rfl⟩, fun k hk => ?_⟩
      cases hk
      simpa using hj
  choose c hc₁ hc₂ using key
  let h : σ → MvPowerSeries σ O := fun i m =>
    if c (m + Finsupp.single i 1) = some i then
      MvPowerSeries.coeff (m + Finsupp.single i 1) f else 0
  have hh : ∀ i m, MvPowerSeries.coeff m (h i) =
      if c (m + Finsupp.single i 1) = some i then
        MvPowerSeries.coeff (m + Finsupp.single i 1) f else 0 := fun _ _ => rfl
  have hX : ∀ i m, MvPowerSeries.coeff m (MvPowerSeries.X i * h i) =
      if c m = some i then MvPowerSeries.coeff m f else 0 := by
    intro i m
    rw [MvPowerSeries.X_def, MvPowerSeries.coeff_monomial_mul, one_mul]
    by_cases hle : Finsupp.single i 1 ≤ m
    · rw [if_pos hle, hh, tsub_add_cancel_of_le hle]
    · rw [if_neg hle, if_neg]
      intro hi
      exact hle (Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 (hc₂ m i hi)))
  refine ⟨h, ?_, fun i => ?_⟩
  · ext m
    rw [map_add, map_sum, MvPowerSeries.coeff_C]
    simp only [hX]
    by_cases hm : m = 0
    · subst hm
      have : ∀ i, ¬ c 0 = some i := fun i hi => hc₂ 0 i hi rfl
      simp [this]
    · obtain ⟨j, hj⟩ := hc₁ m hm
      simp [hm, hj]
  · have hne : (Finsupp.single i 1 : σ →₀ ℕ) ≠ 0 := by simp
    obtain ⟨j, hj⟩ := hc₁ _ hne
    have hji : j = i := by
      by_contra hji
      exact hc₂ _ j hj (Finsupp.single_eq_of_ne hji)
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hh, zero_add, if_pos (hji ▸ hj)]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EvalFg
section
theorem UpperTheory.Reformulated.B.Qn15.eval_fg :
    ∀ {R : Type} [inst : CommRing R] [inst_1 : Algebra R ℂ] {σ : Type} {M₀ : Submodule R ℂ},
    M₀.FG →
      ∀ (P : MvPolynomial σ ℂ),
        ∃ (M : Submodule R ℂ),
          M.FG ∧ ∀ (v : σ → ℂ), (∀ (i : σ), v i ∈ M₀) → (MvPolynomial.eval v : MvPolynomial σ ℂ → ℂ) P ∈ M := by
  intro R _ _ σ M₀ h₀ P
  induction P using MvPolynomial.induction_on with
  | C a =>
    refine ⟨Submodule.span R {a}, Submodule.fg_span_singleton a, fun v _ => ?_⟩
    rw [MvPolynomial.eval_C]
    exact Submodule.mem_span_singleton_self a
  | add p q hp hq =>
    obtain ⟨M, hM, hp⟩ := hp
    obtain ⟨N, hN, hq⟩ := hq
    refine ⟨M ⊔ N, hM.sup hN, fun v hv => ?_⟩
    rw [map_add]
    exact Submodule.add_mem_sup (hp v hv) (hq v hv)
  | mul_X p i hp =>
    obtain ⟨M, hM, hp⟩ := hp
    refine ⟨M * M₀, hM.mul h₀, fun v hv => ?_⟩
    rw [map_mul, MvPolynomial.eval_X]
    exact Submodule.mul_mem_mul (hp v hv) (hv i)
end

