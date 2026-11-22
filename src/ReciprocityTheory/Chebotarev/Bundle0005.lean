import ReciprocityTheory.Chebotarev.Bundle0003

-- bundled from ReciprocityTheory.Chebotarev.EulerFin
section
open NumberField Filter Topology

namespace ReciprocityTheory.Cheb

theorem euler_fin_pow {E : Type} [Field E] [NumberField E] (f : Ideal (𝓞 E) → ℂ) (hf1 : f 1 = 1)
    (hmul : ∀ a b : Ideal (𝓞 E), f (a * b) = f a * f b) (a : Ideal (𝓞 E)) (k : ℕ) :
    f (a ^ k) = f a ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, hf1]
  | succ k ih => rw [pow_succ, hmul, ih, pow_succ]

theorem euler_finite {E : Type} [Field E] [NumberField E] (f : Ideal (𝓞 E) → ℂ) (hf1 : f 1 = 1)
    (hmul : ∀ a b : Ideal (𝓞 E), f (a * b) = f a * f b)
    (hsum : Summable (fun a : NZIdeal E => ‖f a.1‖)) (hlt : ∀ q : Prm E, ‖f q.asIdeal‖ < 1)
    (S : Finset (Prm E)) :
    HasSum (Set.indicator {a : NZIdeal E | Smooth S a.1} (fun a => f a.1)) (∏ q ∈ S, (1 - f q.asIdeal)⁻¹) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty]
    have hT : (⊤ : Ideal (𝓞 E)) ≠ ⊥ := top_ne_bot
    have key : Set.indicator {a : NZIdeal E | Smooth ∅ a.1} (fun a => f a.1) =
        fun a => if a = ⟨⊤, hT⟩ then (1:ℂ) else 0 := by
      funext a
      by_cases h : a = ⟨⊤, hT⟩
      · subst h
        have hs : Smooth (∅ : Finset (Prm E)) (⊤ : Ideal (𝓞 E)) := (smooth_empty_iff hT).2 rfl
        rw [Set.indicator_of_mem (show (⟨⊤, hT⟩ : NZIdeal E) ∈ {a : NZIdeal E | Smooth ∅ a.1} from hs), if_pos rfl]
        show f ⊤ = 1
        rw [← Ideal.one_eq_top, hf1]
      · have hs : ¬ Smooth (∅ : Finset (Prm E)) a.1 := by
          intro hs
          exact h (Subtype.ext ((smooth_empty_iff a.2).1 hs))
        rw [Set.indicator_of_notMem (show a ∉ {a : NZIdeal E | Smooth ∅ a.1} from hs), if_neg h]
    rw [key]
    exact hasSum_ite_eq _ _
  | insert q S hq ih =>
    rw [Finset.prod_insert hq]
    rw [← hasSum_subtype_iff_indicator] at ih ⊢
    have hgeo : HasSum (fun k : ℕ => f q.asIdeal ^ k) (1 - f q.asIdeal)⁻¹ :=
      hasSum_geometric_of_norm_lt_one (hlt q)
    have hs1 : Summable (fun k : ℕ => ‖f q.asIdeal ^ k‖) := by
      simpa [norm_pow] using summable_geometric_of_lt_one (norm_nonneg _) (hlt q)
    have hs2 : Summable (fun b : {a : NZIdeal E | Smooth S a.1} => ‖f b.1.1‖) :=
      hsum.subtype _
    have hprod : HasSum (fun p : ℕ × {a : NZIdeal E | Smooth S a.1} => f q.asIdeal ^ p.1 * f p.2.1.1)
        ((1 - f q.asIdeal)⁻¹ * ∏ x ∈ S, (1 - f x.asIdeal)⁻¹) :=
      by
        have ih' : HasSum (fun b : {a : NZIdeal E | Smooth S a.1} => f b.1.1) (∏ x ∈ S, (1 - f x.asIdeal)⁻¹) := ih
        have h3 : Summable (fun p : ℕ × {a : NZIdeal E | Smooth S a.1} => f q.asIdeal ^ p.1 * f p.2.1.1) :=
          summable_mul_of_summable_norm (f := fun k : ℕ => f q.asIdeal ^ k)
            (g := fun b : {a : NZIdeal E | Smooth S a.1} => f b.1.1) hs1 hs2
        exact HasSum.mul (f := fun k : ℕ => f q.asIdeal ^ k)
            (g := fun b : {a : NZIdeal E | Smooth S a.1} => f b.1.1) hgeo ih' h3
    have hne : ∀ (k : ℕ) (b : {a : NZIdeal E | Smooth S a.1}), q.asIdeal ^ k * b.1.1 ≠ ⊥ := by
      intro k b
      exact mul_ne_zero (pow_ne_zero _ q.ne_bot) b.1.2
    let e : ℕ × {a : NZIdeal E | Smooth S a.1} → {a : NZIdeal E | Smooth (insert q S) a.1} :=
      fun p => ⟨⟨q.asIdeal ^ p.1 * p.2.1.1, hne p.1 p.2⟩, smooth_insert_mul q p.1 p.2.2⟩
    have hbij : Function.Bijective e := by
      constructor
      · rintro ⟨k, b⟩ ⟨k', b'⟩ h
        have h' : q.asIdeal ^ k * b.1.1 = q.asIdeal ^ k' * b'.1.1 :=
          congrArg (fun x : {a : NZIdeal E | Smooth (insert q S) a.1} => x.1.1) h
        obtain ⟨h1, h2⟩ := smooth_mul_inj hq b.2 b'.2 h'
        subst h1
        have hb : b = b' := Subtype.ext (Subtype.ext h2)
        rw [hb]
      · rintro ⟨⟨a, ha⟩, hs⟩
        obtain ⟨k, b, hb, hbs, rfl⟩ := smooth_insert_decomp q ha hs
        exact ⟨(k, ⟨⟨b, hb⟩, hbs⟩), rfl⟩
    refine (Equiv.ofBijective e hbij).hasSum_iff.mp ?_
    convert hprod using 1
    funext p
    simp only [Function.comp_apply, Equiv.ofBijective_apply, e]
    rw [hmul, euler_fin_pow f hf1 hmul]

end ReciprocityTheory.Cheb
end

-- bundled from ReciprocityTheory.Chebotarev.PrimeCont
section
open NumberField Filter Topology

namespace ReciprocityTheory.Cheb

theorem norm_chiNrm_cpow_le {E : Type} [Field E] [NumberField E] {l : ℕ} (χ : DirichletCharacter ℂ l)
    (q : Prm E) (s : ℝ) :
    ‖χ ((Nrm q : ℕ) : ZMod l) * ((Nrm q : ℕ) : ℂ) ^ (-(s : ℂ))‖ ≤ ((Nrm q : ℕ) : ℝ) ^ (-s) := by
  have hN : 0 < Nrm q := lt_of_lt_of_le (by norm_num) (two_le_Nrm q)
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos hN]
  have h1 := χ.norm_le_one ((Nrm q : ℕ) : ZMod l)
  have h2 : (0:ℝ) ≤ ((Nrm q : ℕ) : ℝ) ^ (-(s:ℂ)).re := Real.rpow_nonneg (by positivity) _
  simp only [Complex.neg_re, Complex.ofReal_re] at h2 ⊢
  nlinarith [norm_nonneg (χ ((Nrm q : ℕ) : ZMod l))]

theorem nrm_rpow_neg_le_half {E : Type} [Field E] [NumberField E] (q : Prm E) {s : ℝ} (hs : 1 ≤ s) :
    ((Nrm q : ℕ) : ℝ) ^ (-s) ≤ 1 / 2 := by
  have h2 : (2:ℝ) ≤ ((Nrm q : ℕ) : ℝ) := by exact_mod_cast two_le_Nrm q
  calc ((Nrm q : ℕ) : ℝ) ^ (-s) ≤ ((Nrm q : ℕ) : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    _ = (((Nrm q : ℕ) : ℝ))⁻¹ := Real.rpow_neg_one _
    _ ≤ 1 / 2 := by rw [one_div]; exact inv_anti₀ (by norm_num) h2

theorem smoothMap_seminorm_bound' : SmoothMapSeminormBound := by
  intro E _ _ l _ χ s0 hs0
  have hs0' : (1:ℝ) < s0 := hs0
  set a : ℝ := (1 + s0) / 2 with ha_def
  have ha1 : 1 < a := by rw [ha_def]; linarith
  have has0 : a < s0 := by rw [ha_def]; linarith
  have hcont : ContinuousOn (fun s : ℝ => abelian₂ E χ s) (Set.Ioi a) := by
    unfold abelian₂
    refine continuousOn_tsum (u := fun q : Prm E => (3 / 2) * ((Nrm q : ℕ) : ℝ) ^ (-a)) ?_
      ((summable_prm_rpow E ha1).mul_left _) ?_
    · intro q
      have hN : (Nrm q : ℕ) ≠ 0 := by have := two_le_Nrm q; omega
      have hc : Continuous (fun s : ℝ => χ ((Nrm q : ℕ) : ZMod l) * ((Nrm q : ℕ) : ℂ) ^ (-(s : ℂ))) :=
        continuous_const.mul (Continuous.const_cpow (Complex.continuous_ofReal.neg)
          (Or.inl (by exact_mod_cast hN)))
      refine ContinuousOn.neg (ContinuousOn.clog (continuous_const.sub hc).continuousOn ?_)
      intro s hs
      have hs' : a < s := hs
      have hz := (norm_chiNrm_cpow_le χ q s).trans (nrm_rpow_neg_le_half q (by linarith))
      rw [Complex.mem_slitPlane_iff]
      left
      have hre := Complex.abs_re_le_norm (χ ((Nrm q : ℕ) : ZMod l) * ((Nrm q : ℕ) : ℂ) ^ (-(s : ℂ)))
      rw [Complex.sub_re, Complex.one_re]
      have := (abs_le.mp (hre.trans hz)).2
      linarith
    · intro q s hs
      have hs' : a < s := hs
      have hz1 := norm_chiNrm_cpow_le χ q s
      have hz := hz1.trans (nrm_rpow_neg_le_half q (by linarith))
      rw [norm_neg, sub_eq_add_neg]
      have hz' : ‖-(χ ((Nrm q : ℕ) : ZMod l) * ((Nrm q : ℕ) : ℂ) ^ (-(s : ℂ)))‖ ≤ 1 / 2 := by
        rw [norm_neg]; exact hz
      refine (Complex.norm_log_one_add_half_le_self hz').trans ?_
      rw [norm_neg]
      have hmono : ((Nrm q : ℕ) : ℝ) ^ (-s) ≤ ((Nrm q : ℕ) : ℝ) ^ (-a) := by
        have h2 : (2:ℝ) ≤ ((Nrm q : ℕ) : ℝ) := by exact_mod_cast two_le_Nrm q
        exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      nlinarith
  exact (hcont.continuousAt (Ioi_mem_nhds has0)).continuousWithinAt

end ReciprocityTheory.Cheb
end

-- bundled from ReciprocityTheory.Chebotarev.PrimeSum
section
open NumberField Filter Topology

namespace ReciprocityTheory.Cheb

theorem norm_neg_log_one_sub_sub_le {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) : ‖-Complex.log (1 - z) - z‖ ≤ ‖z‖ ^ 2 := by
  have h1 : ‖-z‖ < 1 := by rw [norm_neg]; linarith
  have h := Complex.norm_log_one_add_sub_self_le h1
  rw [norm_neg] at h
  have e : -Complex.log (1 - z) - z = -(Complex.log (1 + -z) - -z) := by ring_nf
  rw [e, norm_neg]
  refine h.trans ?_
  have h0 : 0 ≤ ‖z‖ := norm_nonneg _
  have h2 : (1 - ‖z‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  calc ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 ≤ ‖z‖ ^ 2 * 2 / 2 := by gcongr
    _ = ‖z‖ ^ 2 := by ring

theorem psum_term_norm_le {E : Type} [Field E] [NumberField E] {l : ℕ} (χ : DirichletCharacter ℂ l) (s : ℝ)
    (q : Prm E) :
    ‖χ ((Nrm q : ℕ) : ZMod l) * ((Nrm q : ℕ) : ℂ) ^ (-(s : ℂ))‖ ≤ ((Nrm q : ℕ) : ℝ) ^ (-s) := by
  have hN : (0 : ℕ) < Nrm q := by have := two_le_Nrm q; omega
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos hN]
  simp only [Complex.neg_re, Complex.ofReal_re]
  have := DirichletCharacter.norm_le_one χ ((Nrm q : ℕ) : ZMod l)
  have hp : 0 ≤ ((Nrm q : ℕ) : ℝ) ^ (-s) := Real.rpow_nonneg (by positivity) _
  nlinarith

theorem Nrm_rpow_neg_le_inv {E : Type} [Field E] [NumberField E] {s : ℝ} (hs : 1 < s) (q : Prm E) :
    ((Nrm q : ℕ) : ℝ) ^ (-s) ≤ ((Nrm q : ℕ) : ℝ)⁻¹ := by
  have h2 : (2 : ℝ) ≤ ((Nrm q : ℕ) : ℝ) := by exact_mod_cast two_le_Nrm q
  rw [← Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)

theorem casimirPower_surjective_symmetric' : CasimirPowerSurjectiveSymmetric := by
  intro E _ _ l _ χ
  refine ⟨∑' q : Prm E, ((Nrm q : ℕ) : ℝ) ^ (-(2 : ℝ)), fun s hs => ?_⟩
  set z : Prm E → ℂ := fun q => χ ((Nrm q : ℕ) : ZMod l) * ((Nrm q : ℕ) : ℂ) ^ (-(s : ℂ)) with hzdef
  have hzb : ∀ q, ‖z q‖ ≤ ((Nrm q : ℕ) : ℝ) ^ (-s) := fun q => psum_term_norm_le χ s q
  have hzs : Summable z := Summable.of_norm_bounded (summable_prm_rpow E hs) hzb
  have hls : Summable (fun q => -Complex.log (1 - z q)) := hzs.clog_one_sub.neg
  have hsq : ∀ q, ‖-Complex.log (1 - z q) - z q‖ ≤ ((Nrm q : ℕ) : ℝ) ^ (-(2 : ℝ)) := by
    intro q
    have h2 : (2 : ℝ) ≤ ((Nrm q : ℕ) : ℝ) := by exact_mod_cast two_le_Nrm q
    have hz1 : ‖z q‖ ≤ ((Nrm q : ℕ) : ℝ)⁻¹ := (hzb q).trans (Nrm_rpow_neg_le_inv hs q)
    have hz2 : ‖z q‖ ≤ 1 / 2 := hz1.trans (by rw [one_div]; exact inv_anti₀ (by norm_num) h2)
    refine (norm_neg_log_one_sub_sub_le hz2).trans ?_
    rw [Real.rpow_neg (by linarith), Real.rpow_two, ← inv_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hz1 2
  have e : abelian₂ E χ s - Psum E χ s = ∑' q, (-Complex.log (1 - z q) - z q) := by
    unfold abelian₂ Psum
    exact (hls.tsum_sub hzs).symm
  rw [e]
  exact tsum_of_norm_bounded (summable_prm_rpow E (by norm_num : (1 : ℝ) < 2)).hasSum hsq

end ReciprocityTheory.Cheb
end

-- bundled from ReciprocityTheory.Chebotarev.SplitA
section
open NumberField Filter Topology

namespace ReciprocityTheory.Cheb

theorem liesOver_of_under_eq {E E' : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra E E']
    (P : Prm E') (q : Prm E) (hP : under P = q) : P.asIdeal.LiesOver q.asIdeal :=
  ⟨by rw [← hP, under_asIdeal]⟩

theorem prime_dvd_norm_sub_one_cyclotomic (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime]
    (P : Prm (CyclotomicField l E)) (hl : Nat.Coprime (Nrm P) l) : l ∣ Nrm P - 1 := by
  have hlp : l.Prime := Fact.out
  have : NeZero l := ⟨hlp.ne_zero⟩
  set M := CyclotomicField l E
  have hz := (IsCyclotomicExtension.zeta_spec l E M).toInteger_isPrimitiveRoot
  have h1 : Ideal.absNorm P.asIdeal ≠ 1 := Ideal.absNorm_eq_one_iff.not.mpr P.isPrime.ne_top
  have hq := hz.idealQuotient_mk (I := P.asIdeal) h1 hl
  have : P.asIdeal.IsMaximal := P.isMaximal
  let _ := Ideal.Quotient.field P.asIdeal
  have hu := hq.isUnit hlp.ne_zero
  have hu' : IsPrimitiveRoot hu.unit l := IsPrimitiveRoot.coe_units_iff.mp hq
  have hd : orderOf hu.unit ∣ Nat.card (𝓞 M ⧸ P.asIdeal)ˣ := orderOf_dvd_natCard _
  rw [← hu'.eq_orderOf, Nat.card_units] at hd
  simpa [Nrm, Ideal.absNorm_apply, Submodule.cardQuot_apply] using hd

theorem norm_coprime_of_not_dvd_under (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime] (q : Prm E)
    (P : Prm (CyclotomicField l E)) (hP : under P = q) (hl : ¬ l ∣ Nrm q) : Nat.Coprime (Nrm P) l := by
  have hlp : l.Prime := Fact.out
  have := liesOver_of_under_eq P q hP
  have hN : Nrm q ^ P.asIdeal.inertiaDeg (𝓞 E) = Nrm P :=
    Ideal.absNorm_pow_inertiaDeg q.asIdeal P.asIdeal
  have hcq : Nat.Coprime (Nrm q) l := (Nat.coprime_comm).mp ((Nat.Prime.coprime_iff_not_dvd hlp).mpr hl)
  exact hN ▸ Nat.Coprime.pow_left _ hcq

theorem natCast_mem_of_not_coprime (E : Type) [Field E] [NumberField E] (n : ℕ) (q : Prm E)
    (h : ¬ Nat.Coprime (Nrm q) n) : ((n : ℕ) : 𝓞 E) ∈ q.asIdeal := by
  have : q.asIdeal.IsMaximal := q.isMaximal
  let _ := Ideal.Quotient.field q.asIdeal
  let _ : Fintype (𝓞 E ⧸ q.asIdeal) := Fintype.ofFinite _
  have := ringChar.charP (𝓞 E ⧸ q.asIdeal)
  obtain ⟨k, hcp, hcard⟩ := FiniteField.card (𝓞 E ⧸ q.asIdeal) (ringChar (𝓞 E ⧸ q.asIdeal))
  have hN : Nrm q = ringChar (𝓞 E ⧸ q.asIdeal) ^ (k : ℕ) := by
    rw [← hcard, Nrm, Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, CharP.cast_eq_zero_iff (𝓞 E ⧸ q.asIdeal) (ringChar (𝓞 E ⧸ q.asIdeal))]
  by_contra hd
  exact h (hN ▸ Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hcp).mpr hd))

theorem inertia_trivial_cyclotomic_coprime (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime]
    [IsGalois E (CyclotomicField l E)]
    (P : Prm (CyclotomicField l E)) (hl : Nat.Coprime (Nrm P) l)
    (g : Gal(CyclotomicField l E/E)) (hg : g ∈ P.asIdeal.inertia Gal(CyclotomicField l E/E)) : g = 1 := by
  have hlp : l.Prime := Fact.out
  have : NeZero l := ⟨hlp.ne_zero⟩
  set M := CyclotomicField l E
  have hz0 := IsCyclotomicExtension.zeta_spec l E M
  have hz := hz0.toInteger_isPrimitiveRoot
  set ζ := hz0.toInteger
  have h1 : Ideal.absNorm P.asIdeal ≠ 1 := Ideal.absNorm_eq_one_iff.not.mpr P.isPrime.ne_top
  have hq := hz.idealQuotient_mk (I := P.asIdeal) h1 hl
  have hgl : (g • ζ) ^ l = 1 := by rw [← smul_pow', hz.pow_eq_one, smul_one]
  obtain ⟨i, hi, hiz⟩ := hz.eq_pow_of_pow_eq_one hgl
  have hmem : g • ζ - ζ ∈ P.asIdeal := hg ζ
  rw [← hiz, ← Ideal.Quotient.eq, map_pow] at hmem
  have hi1 : i = 1 := hq.pow_inj hi hlp.one_lt (by rw [hmem, pow_one])
  rw [hi1, pow_one] at hiz
  have hfix : g (IsCyclotomicExtension.zeta l E M) = IsCyclotomicExtension.zeta l E M := by
    have := congrArg (fun x : 𝓞 M => (x : M)) hiz
    exact this.symm
  have hext : (g : M →ₐ[E] M) = AlgHom.id E M := by
    refine AlgHom.ext_of_adjoin_eq_top (IsCyclotomicExtension.adjoin_primitive_root_eq_top hz0) ?_
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact hfix
  ext x
  exact DFunLike.congr_fun hext x

theorem splitA_fibre (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime]
    (hirr : Irreducible (Polynomial.cyclotomic l E)) (q : Prm E) :
    {P : Prm (CyclotomicField l E) | under P = q}.Finite ∧
      {P : Prm (CyclotomicField l E) | under P = q}.ncard ≤ l - 1 := by
  have hlp : l.Prime := Fact.out
  have : NeZero l := ⟨hlp.ne_zero⟩
  set M := CyclotomicField l E
  have : IsGalois E M := IsCyclotomicExtension.isGalois {l} E M
  have hfin : (q.asIdeal.primesOver (𝓞 M)).Finite := Algebra.QuasiFinite.finite_primesOver q.asIdeal
  have hinj : Function.Injective (fun P : Prm M => P.asIdeal) := fun a b h =>
    IsDedekindDomain.HeightOneSpectrum.ext h
  have hmaps : ∀ P ∈ {P : Prm M | under P = q}, P.asIdeal ∈ q.asIdeal.primesOver (𝓞 M) := by
    intro P hP
    have := liesOver_of_under_eq P q hP
    exact ⟨P.isPrime, this⟩
  refine ⟨hfin.preimage hinj.injOn |>.subset hmaps, ?_⟩
  have h1 := Set.ncard_le_ncard_of_injOn _ hmaps hinj.injOn hfin
  have h2 := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn q.asIdeal (𝓞 M) Gal(M/E)
  have h3 : Nat.card Gal(M/E) = l - 1 := by
    rw [IsGalois.card_aut_eq_finrank, IsCyclotomicExtension.finrank M hirr, Nat.totient_prime hlp]
  rw [h3] at h2
  have h4 : q.asIdeal.ramificationIdxIn (𝓞 M) * q.asIdeal.inertiaDegIn (𝓞 M) ≠ 0 := by
    intro h; rw [h, mul_zero] at h2; have := hlp.two_le; omega
  have h5 := Nat.le_mul_of_pos_right ((q.asIdeal.primesOver (𝓞 M)).ncard) (Nat.pos_of_ne_zero h4)
  exact h1.trans (h5.trans h2.le)

theorem splitA_norm (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime] (q : Prm E)
    (P : Prm (CyclotomicField l E)) (hP : under P = q) (hl : ¬ l ∣ Nrm q) :
    (Nrm P = Nrm q ∧ ((Nrm q : ℕ) : ZMod l) = 1) ∨ Nrm q ^ 2 ≤ Nrm P := by
  have hlp : l.Prime := Fact.out
  have := liesOver_of_under_eq P q hP
  have hN : Nrm q ^ P.asIdeal.inertiaDeg (𝓞 E) = Nrm P :=
    Ideal.absNorm_pow_inertiaDeg q.asIdeal P.asIdeal
  have hf := Ideal.inertiaDeg_pos P.asIdeal (𝓞 E)
  have hcq : Nat.Coprime (Nrm q) l := (Nat.coprime_comm).mp ((Nat.Prime.coprime_iff_not_dvd hlp).mpr hl)
  have hcP : Nat.Coprime (Nrm P) l := hN ▸ Nat.Coprime.pow_left _ hcq
  have hd := prime_dvd_norm_sub_one_cyclotomic E l P hcP
  have hq0 : Nrm q ≠ 0 := by
    intro h; exact hl (h ▸ dvd_zero l)
  rcases Nat.lt_or_ge (P.asIdeal.inertiaDeg (𝓞 E)) 2 with h2 | h2
  · have h1 : P.asIdeal.inertiaDeg (𝓞 E) = 1 := by omega
    rw [h1, pow_one] at hN
    refine Or.inl ⟨hN.symm, ?_⟩
    rw [← hN] at hd
    have h3 : ((Nrm q - 1 : ℕ) : ZMod l) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hd
    have h4 : Nrm q = (Nrm q - 1) + 1 := by omega
    rw [h4, Nat.cast_add, h3, Nat.cast_one, zero_add]
  · exact Or.inr (hN ▸ Nat.pow_le_pow_right (Nat.pos_of_ne_zero hq0) h2)

theorem splitA_finite_not_coprime (E : Type) [Field E] [NumberField E] (n : ℕ) (hn : n ≠ 0) :
    {q : Prm E | ¬ Nat.Coprime (Nrm q) n}.Finite := by
  have h0 : Ideal.span {((n : ℕ) : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn
  refine (Ideal.finite_factors h0).subset fun q hq => ?_
  exact (Ideal.dvd_span_singleton).mpr (natCast_mem_of_not_coprime E n q hq)

theorem splitA_unram (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime] (q : Prm E)
    (P : Prm (CyclotomicField l E)) (hP : under P = q) (hl : ¬ l ∣ Nrm q) :
    P.asIdeal.ramificationIdx (𝓞 E) = 1 := by
  have hlp : l.Prime := Fact.out
  have : NeZero l := ⟨hlp.ne_zero⟩
  have : IsGalois E (CyclotomicField l E) := IsCyclotomicExtension.isGalois {l} E (CyclotomicField l E)
  have := liesOver_of_under_eq P q hP
  have : q.asIdeal.IsMaximal := q.isMaximal
  have : Finite q.asIdeal.ResidueField :=
    Finite.of_surjective _ q.asIdeal.bijective_algebraMap_quotient_residueField.surjective
  have hcP := norm_coprime_of_not_dvd_under E l q P hP hl
  have hbot : P.asIdeal.inertia Gal(CyclotomicField l E/E) = ⊥ :=
    (Subgroup.eq_bot_iff_forall _).mpr fun g hg => inertia_trivial_cyclotomic_coprime E l P hcP g hg
  rw [← Ideal.ramificationIdxIn_eq_ramificationIdx q.asIdeal P.asIdeal Gal(CyclotomicField l E/E),
    ← Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(CyclotomicField l E/E)) q.asIdeal P.asIdeal,
    hbot, Subgroup.card_bot]

end ReciprocityTheory.Cheb
end

-- bundled from ReciprocityTheory.Chebotarev.SplitD
section
open NumberField Filter Topology

namespace ReciprocityTheory.Cheb

theorem splitD_natCast_not_mem (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime] (q : Prm E)
    (hl : ¬ l ∣ Nrm q) : (l : 𝓞 E) ∉ q.asIdeal := by
  intro h
  have hmax : q.asIdeal.IsMaximal := q.isMaximal
  let : Field (𝓞 E ⧸ q.asIdeal) := Ideal.Quotient.field _
  have hfin : Finite (𝓞 E ⧸ q.asIdeal) := by
    have := (Ideal.absNorm_ne_zero_iff q.asIdeal).1 (by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact q.ne_bot)
    exact this
  let := Fintype.ofFinite (𝓞 E ⧸ q.asIdeal)
  have h0 : ((l : 𝓞 E ⧸ q.asIdeal)) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk q.asIdeal), Ideal.Quotient.eq_zero_iff_mem]; exact h
  set p := ringChar (𝓞 E ⧸ q.asIdeal)
  have hpl : p ∣ l := (ringChar.spec _ l).1 h0
  have hp1 : p ≠ 1 := CharP.ringChar_ne_one
  have hpeq : p = l := ((Fact.out : l.Prime).eq_one_or_self_of_dvd p hpl).resolve_left hp1
  obtain ⟨n, -, hn⟩ := FiniteField.card (𝓞 E ⧸ q.asIdeal) p
  apply hl
  have : Nrm q = Fintype.card (𝓞 E ⧸ q.asIdeal) := by
    rw [Nrm, Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  rw [this, hn, hpeq]
  exact dvd_pow_self l n.ne_zero

theorem splitD_frob (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime] (q : Prm E)
    (P : Prm (CyclotomicField l E)) (hP : under P = q) (hl : ¬ l ∣ Nrm q) :
    ∃ σ : CyclotomicField l E ≃ₐ[E] CyclotomicField l E,
      σ (IsCyclotomicExtension.zeta l E (CyclotomicField l E)) =
        IsCyclotomicExtension.zeta l E (CyclotomicField l E) ^ Nrm q ∧
      ∀ x : 𝓞 (CyclotomicField l E), ∃ y : 𝓞 (CyclotomicField l E),
        (y : CyclotomicField l E) = σ (x : CyclotomicField l E) ∧ y - x ^ Nrm q ∈ P.asIdeal := by
  have : IsGalois E (CyclotomicField l E) := IsCyclotomicExtension.isGalois {l} E _
  have : Algebra.IsInvariant (𝓞 E) (𝓞 (CyclotomicField l E))
      (𝓞 (CyclotomicField l E) ≃ₐ[𝓞 E] 𝓞 (CyclotomicField l E)) :=
    Algebra.isInvariant_of_isGalois' (𝓞 E) E (CyclotomicField l E) (𝓞 (CyclotomicField l E))
  have : Finite (𝓞 (CyclotomicField l E) ≃ₐ[𝓞 E] 𝓞 (CyclotomicField l E)) :=
    Finite.of_equiv _ (galRestrict (𝓞 E) E (CyclotomicField l E) (𝓞 (CyclotomicField l E))).toEquiv
  have : P.asIdeal.IsPrime := P.isPrime
  have : Finite (𝓞 (CyclotomicField l E) ⧸ P.asIdeal) :=
    (Ideal.absNorm_ne_zero_iff P.asIdeal).1 (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact P.ne_bot)
  obtain ⟨τ, hτ⟩ := IsArithFrobAt.exists_of_isInvariant (𝓞 E)
    (𝓞 (CyclotomicField l E) ≃ₐ[𝓞 E] 𝓞 (CyclotomicField l E)) P.asIdeal
  have hcard : Nat.card (𝓞 E ⧸ P.asIdeal.under (𝓞 E)) = Nrm q := by
    rw [Nrm, ← hP, under_asIdeal, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hσ : ∀ x : 𝓞 (CyclotomicField l E),
      ((τ x : 𝓞 (CyclotomicField l E)) : CyclotomicField l E) =
        (galRestrict (𝓞 E) E (CyclotomicField l E) (𝓞 (CyclotomicField l E))).symm τ
          (x : CyclotomicField l E) := by
    intro x
    have := algebraMap_galRestrict_apply (𝓞 E)
      ((galRestrict (𝓞 E) E (CyclotomicField l E) (𝓞 (CyclotomicField l E))).symm τ) x
    simpa only [MulEquiv.apply_symm_apply] using this
  have hfr : ∀ x : 𝓞 (CyclotomicField l E), τ x - x ^ Nrm q ∈ P.asIdeal := by
    intro x
    have := hτ x
    rw [hcard] at this
    exact this
  refine ⟨(galRestrict (𝓞 E) E (CyclotomicField l E) (𝓞 (CyclotomicField l E))).symm τ, ?_,
    fun x => ⟨τ x, hσ x, hfr x⟩⟩
  have hz := IsCyclotomicExtension.zeta_spec l E (CyclotomicField l E)
  have hlP : ((l : ℕ) : 𝓞 (CyclotomicField l E)) ∉ P.asIdeal := by
    intro h
    apply splitD_natCast_not_mem E l q hl
    rw [← hP, under_asIdeal, Ideal.mem_comap, map_natCast]
    exact h
  have h1 := hτ.apply_of_pow_eq_one (ζ := hz.toInteger) (m := l) hz.toInteger_isPrimitiveRoot.pow_eq_one hlP
  rw [hcard] at h1
  have h2 : ((τ hz.toInteger : 𝓞 (CyclotomicField l E)) : CyclotomicField l E) =
      ((hz.toInteger ^ Nrm q : 𝓞 (CyclotomicField l E)) : CyclotomicField l E) := congrArg _ h1
  rw [hσ] at h2
  push_cast at h2
  exact h2

end ReciprocityTheory.Cheb
end

