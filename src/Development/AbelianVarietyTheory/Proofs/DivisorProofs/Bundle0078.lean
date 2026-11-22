import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCardEqFinsumLengthLocalizedMaximal
section
namespace GlobalTheory.CardLength

variable {R : Type} [CommRing R]

noncomputable def lenAt (w : Ideal R) [w.IsPrime] (Q : Type) [AddCommGroup Q] [Module R Q] : ℕ∞ :=
  Module.length (Localization.AtPrime w) (LocalizedModule w.primeCompl Q)

theorem lenAt_exact (w : Ideal R) [w.IsPrime] {N M P : Type} [AddCommGroup N] [Module R N]
    [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P] (f : N →ₗ[R] M) (g : M →ₗ[R] P)
    (hf : Function.Injective f) (hg : Function.Surjective g) (H : Function.Exact f g) :
    lenAt w M = lenAt w N + lenAt w P :=
  Module.length_eq_add_of_exact (LocalizedModule.map w.primeCompl f)
    (LocalizedModule.map w.primeCompl g) (LocalizedModule.map_injective _ f hf)
    (LocalizedModule.map_surjective _ g hg) (LocalizedModule.map_exact _ f g H)

theorem lenAt_congr (w : Ideal R) [w.IsPrime] {M N : Type} [AddCommGroup N] [Module R N]
    [AddCommGroup M] [Module R M] (e : M ≃ₗ[R] N) : lenAt w M = lenAt w N :=
  le_antisymm
    (Module.length_le_of_injective (LocalizedModule.map w.primeCompl e.toLinearMap)
      (LocalizedModule.map_injective _ _ e.injective))
    (Module.length_le_of_injective (LocalizedModule.map w.primeCompl e.symm.toLinearMap)
      (LocalizedModule.map_injective _ _ e.symm.injective))

theorem lenAt_subsingleton (w : Ideal R) [w.IsPrime] (Q : Type) [AddCommGroup Q] [Module R Q]
    [Subsingleton Q] : lenAt w Q = 0 :=
  Module.length_eq_zero_iff.2 (IsLocalizedModule.subsingleton_of_subsingleton w.primeCompl
    (LocalizedModule.mkLinearMap w.primeCompl Q))

theorem lenAt_quot_ne (w m : Ideal R) [hw : w.IsMaximal] [hm : m.IsMaximal] (h : w ≠ m) :
    lenAt w (R ⧸ m) = 0 := by
  refine Module.length_eq_zero_iff.2 ((IsLocalizedModule.subsingleton_iff w.primeCompl
    (LocalizedModule.mkLinearMap w.primeCompl (R ⧸ m))).2 ?_)
  have hnle : ¬ m ≤ w := fun hle => h (hm.eq_of_le hw.ne_top hle).symm
  obtain ⟨s, hsm, hsw⟩ := SetLike.not_le_iff_exists.1 hnle
  intro x
  refine ⟨s, hsw, ?_⟩
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  exact m.mul_mem_right _ hsm

theorem lenAt_quot_self (m : Ideal R) [hm : m.IsMaximal] : lenAt m (R ⧸ m) = 1 := by
  refine Module.length_eq_one_iff.2 (isSimpleModule_iff_toSpanSingleton_surjective.2 ⟨?_, ?_⟩)
  · rw [← not_subsingleton_iff_nontrivial, IsLocalizedModule.subsingleton_iff m.primeCompl
      (LocalizedModule.mkLinearMap m.primeCompl (R ⧸ m))]
    intro h
    obtain ⟨r, hr, hr0⟩ := h 1
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, mul_one,
      Ideal.Quotient.eq_zero_iff_mem] at hr0
    exact hr hr0
  · intro x hx y
    induction x using LocalizedModule.induction_on with
    | h a s =>
    induction y using LocalizedModule.induction_on with
    | h c t =>
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨r', rfl⟩ := Ideal.Quotient.mk_surjective c
    have hr : r ∈ m.primeCompl := by
      intro hrm
      apply hx
      rw [Ideal.Quotient.eq_zero_iff_mem.2 hrm, LocalizedModule.zero_mk]
    refine ⟨Localization.mk (r' * s) (⟨r, hr⟩ * t), ?_⟩
    rw [LinearMap.toSpanSingleton_apply, LocalizedModule.mk_smul_mk, LocalizedModule.mk_eq]
    refine ⟨1, ?_⟩
    simp only [Submonoid.smul_def, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
      Submonoid.coe_mul, Submonoid.coe_one]
    congr 1
    ring

theorem card_eq_prod_lenAt : ∀ (n : ℕ) (Q : Type) [AddCommGroup Q] [Module R Q] [Finite Q],
    Nat.card Q = n → ∃ k : MaximalSpectrum R →₀ ℕ,
      (∀ w : MaximalSpectrum R, lenAt w.asIdeal Q = (k w : ℕ∞)) ∧
      Nat.card Q = k.prod fun w j => Nat.card (R ⧸ w.asIdeal) ^ j := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro Q _ _ _ hn
  by_cases hQ : Subsingleton Q
  · refine ⟨0, fun w => ?_, ?_⟩
    · rw [lenAt_subsingleton]; simp
    · rw [Finsupp.prod_zero_index]; exact Nat.card_of_subsingleton 0
  · rw [not_subsingleton_iff_nontrivial] at hQ
    rcases eq_top_or_exists_le_coatom (⊥ : Submodule R Q) with h | ⟨Q1, hQ1, -⟩
    · exact absurd h bot_ne_top
    · have hsimple : IsSimpleModule R (Q ⧸ Q1) := isSimpleModule_iff_isCoatom.2 hQ1
      obtain ⟨m0, hm0, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.1 hsimple
      have hnt : Nontrivial (Q ⧸ Q1) := IsSimpleModule.nontrivial R _
      have hcard : Nat.card Q = Nat.card Q1 * Nat.card (Q ⧸ Q1) :=
        Submodule.card_eq_card_quotient_mul_card Q1
      have hfq : Finite (Q ⧸ Q1) := Finite.of_surjective _ Q1.mkQ_surjective
      have h1 : 1 < Nat.card (Q ⧸ Q1) := Finite.one_lt_card
      have h2 : 0 < Nat.card Q1 := Nat.card_pos
      have hlt : Nat.card Q1 < n := by
        rw [← hn, hcard]; nlinarith
      obtain ⟨k1, hk1, hk1c⟩ := ih _ hlt Q1 rfl
      refine ⟨k1 + Finsupp.single ⟨m0, hm0⟩ 1, fun w => ?_, ?_⟩
      · have := w.isMaximal
        rw [lenAt_exact w.asIdeal Q1.subtype Q1.mkQ Q1.injective_subtype Q1.mkQ_surjective
          (LinearMap.exact_subtype_mkQ Q1), hk1 w, lenAt_congr w.asIdeal e, Finsupp.add_apply,
          Finsupp.single_apply]
        by_cases hw : (⟨m0, hm0⟩ : MaximalSpectrum R) = w
        · subst hw
          rw [if_pos rfl, lenAt_quot_self]; simp
        · rw [if_neg hw, lenAt_quot_ne w.asIdeal m0
            (fun h => hw (MaximalSpectrum.ext h.symm))]; simp
      · have hz : ∀ w : MaximalSpectrum R, Nat.card (R ⧸ w.asIdeal) ^ 0 = 1 :=
          fun _ => pow_zero _
        have ha : ∀ (w : MaximalSpectrum R) (a c : ℕ), Nat.card (R ⧸ w.asIdeal) ^ (a + c) =
            Nat.card (R ⧸ w.asIdeal) ^ a * Nat.card (R ⧸ w.asIdeal) ^ c := fun _ _ _ => pow_add _ _ _
        rw [Finsupp.prod_add_index'
            (h := fun (w : MaximalSpectrum R) (j : ℕ) => Nat.card (R ⧸ w.asIdeal) ^ j) hz ha,
          Finsupp.prod_single_index
            (h := fun (w : MaximalSpectrum R) (j : ℕ) => Nat.card (R ⧸ w.asIdeal) ^ j) (hz _),
          pow_one, hcard, hk1c, Nat.card_congr e.toEquiv]

theorem log_card_eq_finsum_length : ∀ (B : Type) [CommRing B] (N : Type) [AddCommGroup N]
    [Module B N] [Finite N], Real.log (Nat.card N) = ∑ᶠ m : MaximalSpectrum B,
      ((Module.length (Localization.AtPrime m.asIdeal)
        (LocalizedModule m.asIdeal.primeCompl N)).toNat : ℝ) * Real.log (Nat.card (B ⧸ m.asIdeal)) := by
  intro B _ N _ _ _
  classical
  obtain ⟨k, hk, hc⟩ := card_eq_prod_lenAt (R := B) _ N rfl
  have hlen : ∀ m : MaximalSpectrum B, (Module.length (Localization.AtPrime m.asIdeal)
      (LocalizedModule m.asIdeal.primeCompl N)).toNat = k m := fun m => by
    have h := hk m
    unfold lenAt at h
    rw [h]; rfl
  simp_rw [hlen]
  rw [finsum_eq_sum_of_support_subset (s := k.support) _ ?_]
  · have h0 : (k.prod fun w j => Nat.card (B ⧸ w.asIdeal) ^ j) ≠ 0 := by
      rw [← hc]; exact Nat.card_pos.ne'
    rw [Finsupp.prod, Finset.prod_ne_zero_iff] at h0
    rw [hc, Finsupp.prod, Nat.cast_prod, Real.log_prod]
    · refine Finset.sum_congr rfl fun m _ => ?_
      rw [Nat.cast_pow, Real.log_pow]
    · intro m hm
      exact_mod_cast h0 m hm
  · intro m hm
    rw [Function.mem_support] at hm
    rw [Finset.mem_coe, Finsupp.mem_support_iff]
    intro h0; apply hm; simp [h0]

end GlobalTheory.CardLength
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCardQuotSpanEqFinsumLogNormEmbeddings
section
open scoped nonZeroDivisors

namespace GlobalTheory

namespace IndexNormEmb

theorem card_quot_span_eq (B : Type) [CommRing B] [IsDomain B] [Module.Free ℤ B] [Module.Finite ℤ B]
    (b : B) (hb : b ≠ 0) : Nat.card (B ⧸ Ideal.span {b}) = (Algebra.norm ℤ b).natAbs := by
  classical
  rw [Algebra.norm_apply]
  let bs := Module.Free.chooseBasis ℤ B
  have := Submodule.natAbs_det_equiv ((Ideal.span {b}).restrictScalars ℤ)
    (bs.equiv (Ideal.basisSpanSingleton bs hb) (Equiv.refl _))
  rw [show Nat.card (B ⧸ Ideal.span {b}) = Nat.card (B ⧸ (Ideal.span {b}).restrictScalars ℤ) from rfl,
    ← this]
  congr
  refine bs.ext fun i => ?_
  simp
  show ((bs.equiv (Ideal.basisSpanSingleton bs hb) (Equiv.refl _) (bs i) : Ideal.span {b}) : B) = b * bs i
  rw [Module.Basis.equiv_apply, Equiv.refl_apply, Ideal.basisSpanSingleton_apply]

theorem injective_of_ringHom (B : Type) [CommRing B] [IsDomain B] [Module.Finite ℤ B]
    (τ : B →+* ℂ) : Function.Injective τ := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have h : (RingHom.ker τ).comap (algebraMap ℤ B) = ⊥ := by
    ext n
    simp [RingHom.mem_ker, Ideal.mem_comap]
  have := Ideal.eq_bot_of_comap_eq_bot h
  have hx' : x ∈ RingHom.ker τ := hx
  rw [this] at hx'
  simpa using hx'

noncomputable def embEquiv (B : Type) [CommRing B] [IsDomain B] [CharZero B] [Module.Finite ℤ B] :
    (FractionRing B →ₐ[ℚ] ℂ) ≃ (B →+* ℂ) where
  toFun σ := (σ : FractionRing B →+* ℂ).comp (algebraMap B (FractionRing B))
  invFun τ := (IsFractionRing.lift (K := FractionRing B) (injective_of_ringHom B τ)).toRatAlgHom
  left_inv σ := by
    apply AlgHom.coe_ringHom_injective
    apply IsLocalization.ringHom_ext B⁰
    ext x
    simp
  right_inv τ := by
    ext x
    simp

theorem log_card_quot_span_eq_finsum_log_norm : ∀ (B : Type) [CommRing B] [IsDomain B] [CharZero B] [Module.Finite ℤ B] (b : B),
    b ≠ 0 → Finite (B ⧸ Ideal.span {b}) ∧
      Real.log (Nat.card (B ⧸ Ideal.span {b})) = ∑ᶠ τ : B →+* ℂ, Real.log ‖τ b‖ := by
  intro B _ _ _ _ b hb
  classical
  haveI : IsLocalization (Algebra.algebraMapSubmonoid B ℤ⁰) (FractionRing B) :=
    Algebra.IsAlgebraic.instIsLocalizationAlgebraMapSubmonoidNonZeroDivisors ℤ B (FractionRing B)
  haveI : IsScalarTower ℤ ℚ (FractionRing B) :=
    ⟨fun n q x => by rw [zsmul_eq_mul, zsmul_eq_mul, Algebra.smul_def, Algebra.smul_def, map_mul, map_intCast, mul_assoc]⟩
  haveI : @IsScalarTower ℤ ℚ (FractionRing B) Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_int _ _)
  haveI : FiniteDimensional ℚ (FractionRing B) := Module.Finite.of_isLocalization ℤ B ℤ⁰
  have hcard := card_quot_span_eq B b hb
  have hN0 : Algebra.norm ℤ b ≠ 0 := Algebra.norm_ne_zero_iff.mpr hb
  refine ⟨Nat.finite_of_card_ne_zero (by rw [hcard]; exact Int.natAbs_ne_zero.mpr hN0), ?_⟩
  have hN : algebraMap ℤ ℂ (Algebra.norm ℤ b) =
      ∏ σ : FractionRing B →ₐ[ℚ] ℂ, σ (algebraMap B (FractionRing B) b) := by
    rw [IsScalarTower.algebraMap_apply ℤ ℚ ℂ,
      ← Algebra.norm_localization ℤ (Sₘ := FractionRing B) ℤ⁰, Algebra.norm_eq_prod_embeddings]
  have hx : algebraMap B (FractionRing B) b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective B (FractionRing B))).mpr hb
  rw [← finsum_comp_equiv (embEquiv B), finsum_eq_sum_of_fintype]
  change _ = ∑ σ : FractionRing B →ₐ[ℚ] ℂ, Real.log ‖σ (algebraMap B (FractionRing B) b)‖
  rw [← Real.log_prod (fun σ _ => norm_ne_zero_iff.mpr ((map_ne_zero_iff _ σ.toRingHom.injective).mpr hx)),
    ← norm_prod, ← hN, hcard, Nat.cast_natAbs, eq_intCast, Complex.norm_intCast, Int.cast_abs]

end IndexNormEmb

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogConcaveMultiplicativeGrowthBound
section
open NumberField

namespace GlobalTheory

theorem nat_le_of_forall_pow_le_mul_pow (x y C : ℕ) (h : ∀ j, x ^ j ≤ C * y ^ j) : x ≤ y := by
  by_contra hlt
  push_neg at hlt
  rcases Nat.eq_zero_or_pos y with hy | hy
  · subst hy
    have := h 1
    simp at this
    omega
  · have hyR : (0:ℝ) < y := by exact_mod_cast hy
    have hq : (1:ℝ) < (x:ℝ) / y := by
      rw [one_lt_div hyR]; exact_mod_cast hlt
    obtain ⟨j, hj⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hq).eventually_gt_atTop (C:ℝ)).exists
    have h1 : ((x:ℝ))^j ≤ C * (y:ℝ)^j := by exact_mod_cast h j
    rw [div_pow, lt_div_iff₀ (pow_pos hyR j)] at hj
    linarith

theorem first_term_le_of_logConcave_blocks :
    ∀ (g : ℕ → ℕ) (e C B : ℕ), 1 ≤ e → g 0 = 1 → (∀ n, 0 < g n) →
    (∀ k, g (k + 2) * g k ≤ g (k + 1) ^ 2) → (∀ j, g (e * (j + 1)) = g (e * j) * g e) →
    (∀ n, g n ≤ C * B ^ n) → g 1 ≤ B := by
  intro g e C B he h0 hpos hlc hblk hgr
  set r : ℕ → ℝ := fun k => (g (k+1) : ℝ) / g k with hr
  have gpos : ∀ n, (0:ℝ) < g n := fun n => by exact_mod_cast hpos n
  have rpos : ∀ k, 0 < r k := fun k => div_pos (gpos _) (gpos _)
  have rstep : ∀ k, r (k+1) ≤ r k := by
    intro k
    simp only [hr]
    rw [div_le_div_iff₀ (gpos _) (gpos _)]
    have h1 : ((g (k+2) : ℝ)) * g k ≤ (g (k+1):ℝ)^2 := by exact_mod_cast hlc k
    have h2 : k + 1 + 1 = k + 2 := by ring
    rw [h2]; nlinarith [h1]
  have ranti : Antitone r := antitone_nat_of_succ_le rstep
  have gmul : ∀ a n, (g (a + n) : ℝ) = g a * ∏ i ∈ Finset.range n, r (a + i) := by
    intro a n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.prod_range_succ, ← mul_assoc, ← ih]
      simp only [hr]
      rw [← add_assoc]
      field_simp [(gpos (a+n)).ne']
  have g0 : (g 0 : ℝ) = 1 := by exact_mod_cast h0
  have ge : (g e : ℝ) = ∏ i ∈ Finset.range e, r i := by
    have := gmul 0 e; simpa [g0] using this
  have g2e : (g (e + e) : ℝ) = g e * g e := by
    have := hblk 1
    have h2 : e * (1+1) = e + e := by ring
    rw [h2, mul_one] at this
    exact_mod_cast this
  have hprodeq : ∏ i ∈ Finset.range e, r (e + i) = ∏ i ∈ Finset.range e, r i := by
    have := gmul e e
    rw [g2e] at this
    have hne : (g e : ℝ) ≠ 0 := (gpos e).ne'
    rw [← ge]
    exact (mul_left_cancel₀ hne this).symm
  have hre : r e = r 0 := by
    apply le_antisymm (ranti (Nat.zero_le e))
    by_contra hlt
    push_neg at hlt
    have : ∏ i ∈ Finset.range e, r (e + i) < ∏ i ∈ Finset.range e, r i := by
      apply Finset.prod_lt_prod
      · intro i _; exact rpos _
      · intro i _; exact ranti (by omega)
      · exact ⟨0, Finset.mem_range.2 (by omega), by simpa using hlt⟩
    rw [hprodeq] at this
    exact lt_irrefl _ this
  have hconst : ∀ i ∈ Finset.range e, r i = r 0 := by
    intro i hi
    have hi' := Finset.mem_range.1 hi
    apply le_antisymm (ranti (Nat.zero_le i))
    rw [← hre]; exact ranti (by omega)
  have r0 : r 0 = g 1 := by simp [hr, g0]
  have geR : (g e : ℝ) = (g 1 : ℝ) ^ e := by
    rw [ge, Finset.prod_congr rfl hconst, Finset.prod_const, Finset.card_range, r0]
  have geN : g e = g 1 ^ e := by exact_mod_cast geR
  have gej : ∀ j, g (e * j) = (g 1 ^ e) ^ j := by
    intro j
    induction j with
    | zero => simp [h0]
    | succ j ih => rw [hblk, ih, geN, pow_succ]
  have hpow : g 1 ^ e ≤ B ^ e := by
    apply nat_le_of_forall_pow_le_mul_pow _ _ C
    intro j
    rw [← gej, ← pow_mul]
    exact hgr _
  exact (pow_le_pow_iff_left₀ (Nat.zero_le _) (Nat.zero_le _) (by omega : e ≠ 0)).1 hpow

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogSizeBoundsClassNumberVolume
section
open Real

namespace GlobalTheory

theorem log_size_bounds_class_number_volume : ∀ f r L lrd lM lh w d D : ℝ, 1 ≤ f → 2 ≤ r → 1 ≤ L → log f + log r ≤ L → 0 ≤ lrd → lrd ≤ 2*L → 0 ≤ lM → lM ≤ 30*L → lh ≤ f*lrd + 2*f*log (1 + f*lrd) → 1 ≤ d → log d / 2 ≤ lrd → 0 < w → D = f*r*(r-1)/2 → lh ≤ 9*f*L ∧ lh + 2*f*lM ≤ 69*f*L ∧ log 2 + lh + 2*f*(r^2+1)*lM + f*(r^2-1)/2*lrd ≤ 80*f*r^2*L ∧ log 2 + lh + 2*f*(r^2+1)*lM + f*(r^2-1)/2*lrd + f*r^2/2*log r ≤ 81*f*r^2*L ∧ 2 + D*log (1600*r^2/π) + (2*f*r)^2*log (5*f*r*exp (3/2*lrd)*max 1 (exp lM*f*w*√d)) + (log 2 + lh + 2*f*(r^2+1)*lM + f*(r^2-1)/2*lrd) ≤ 242*(f*r*L)^2 + 4*f^2*r^2*log (max 1 w) ∧ (w ≤ 3*exp (2*L) → 2 + D*log (1600*r^2/π) + (2*f*r)^2*log (5*f*r*exp (3/2*lrd)*max 1 (exp lM*f*w*√d)) + (log 2 + lh + 2*f*(r^2+1)*lM + f*(r^2-1)/2*lrd) ≤ 250*f^2*r^2*L) := by
  intro f r L lrd lM lh w d D hf hr hL hfr hrd0 hrd hM0 hM hlh hd hdl hw hD
  have f0 : 0 < f := by linarith
  have r0 : 0 < r := by linarith
  have L0 : 0 < L := by linarith
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have lf0 : 0 ≤ log f := log_nonneg hf
  have lr2 : log 2 ≤ log r := log_le_log (by norm_num) hr
  have lLL : log L ≤ L - 1 := log_le_sub_one_of_pos L0
  have hfL : 1 ≤ f * L := by nlinarith
  have l4 : log 4 = 2 * log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, log_pow]; norm_num
  have l8 : log 8 = 3 * log 2 := by
    rw [show (8:ℝ) = 2^3 by norm_num, log_pow]; norm_num
  have l16 : log 16 = 4 * log 2 := by
    rw [show (16:ℝ) = 2^4 by norm_num, log_pow]; norm_num
  have l1024 : log 1024 = 10 * log 2 := by
    rw [show (1024:ℝ) = 2^10 by norm_num, log_pow]; norm_num
  have l5 : log 5 ≤ 3 * log 2 := l8 ▸ log_le_log (by norm_num) (by norm_num)
  have l15 : log 5 + log 3 ≤ 4 * log 2 := by
    rw [← log_mul (by norm_num) (by norm_num), ← l16]
    exact log_le_log (by norm_num) (by norm_num)
  have hfrd : f * lrd ≤ f * (2 * L) := mul_le_mul_of_nonneg_left hrd f0.le
  have hfrd0 : 0 ≤ f * lrd := by positivity
  have h1 : log (1 + f * lrd) ≤ 2 * L := by
    have : log (1 + f * lrd) ≤ log (4 * f * L) := log_le_log (by linarith) (by linarith)
    rw [log_mul (by positivity) L0.ne', log_mul (by norm_num) f0.ne'] at this
    linarith
  have c1 : lh ≤ 9 * f * L := by
    have := mul_le_mul_of_nonneg_left h1 f0.le
    linarith
  have hfM : f * lM ≤ f * (30 * L) := mul_le_mul_of_nonneg_left hM f0.le
  have r2 : 4 ≤ r ^ 2 := by nlinarith
  have c3 : log 2 + lh + 2*f*(r^2+1)*lM + f*(r^2-1)/2*lrd ≤ 80*f*r^2*L := by
    have a := mul_le_mul_of_nonneg_left hfM (show 0 ≤ r^2+1 by positivity)
    have b := mul_le_mul_of_nonneg_left hfrd (show 0 ≤ r^2-1 by linarith)
    have c := mul_le_mul_of_nonneg_left r2 (show 0 ≤ f * L by linarith)
    linarith
  have lrL : log r ≤ L := by linarith
  have hfr2 : 0 ≤ f * r ^ 2 := by positivity
  have c4 : f*r^2/2*log r ≤ f*r^2*L := by
    have := mul_le_mul_of_nonneg_left lrL hfr2
    have : 0 ≤ f * r^2 * L := by positivity
    linarith
  have pi3 := Real.pi_gt_three
  have h2 : log (1600*r^2/π) ≤ 10 * log 2 + 2 * L := by
    have : log (1600*r^2/π) ≤ log (1024 * r^2) := by
      apply log_le_log (by positivity)
      rw [div_le_iff₀ pi_pos]
      nlinarith
    rw [log_mul (by norm_num) (by positivity), log_pow, l1024] at this
    push_cast at this
    linarith
  have hD0 : 0 ≤ D := by
    rw [hD]; have : 0 ≤ r - 1 := by linarith
    positivity
  have hD1 : D ≤ f * r ^ 2 / 2 := by
    rw [hD]; have : 0 ≤ f * r := by positivity
    nlinarith
  have h3 : D * log (1600*r^2/π) ≤ f * r^2 / 2 * (9 * L) := by
    calc D * log (1600*r^2/π) ≤ D * (9 * L) := mul_le_mul_of_nonneg_left (by linarith) hD0
      _ ≤ _ := mul_le_mul_of_nonneg_right hD1 (by positivity)
  have m1 : (1:ℝ) ≤ max 1 w := le_max_left _ _
  have sd : 1 ≤ √d := Real.one_le_sqrt.mpr hd
  have eM : 1 ≤ exp lM := one_le_exp hM0
  have h4 : max 1 (exp lM*f*w*√d) ≤ exp lM*f*max 1 w*√d := by
    apply max_le
    · exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le eM hf) m1) sd
    · gcongr; exact le_max_right _ _
  have h5 : log (5*f*r*exp (3/2*lrd)*max 1 (exp lM*f*w*√d))
      ≤ log 5 - log 2 + 37 * L + log (max 1 w) := by
    have : log (5*f*r*exp (3/2*lrd)*max 1 (exp lM*f*w*√d))
        ≤ log (5*f*r*exp (3/2*lrd)*(exp lM*f*max 1 w*√d)) := by
      apply log_le_log (by positivity)
      gcongr
    have e : log (5*f*r*exp (3/2*lrd)*(exp lM*f*max 1 w*√d))
        = log 5 + log f + log r + 3/2*lrd + (lM + log f + log (max 1 w) + log d / 2) := by
      rw [log_mul (by positivity) (by positivity), log_mul (by positivity) (by positivity),
        log_mul (by positivity) (by positivity), log_mul (by positivity) (by positivity),
        log_mul (by positivity) (by positivity), log_mul (by positivity) (by positivity),
        log_mul (by positivity) (by positivity), log_exp, log_exp,
        log_sqrt (by linarith)]
    linarith
  have hX : 0 ≤ f^2 * r^2 := by positivity
  have hA : f * r^2 * L ≤ f^2 * r^2 * L := by
    have : 0 ≤ f * r^2 * L := by positivity
    have := mul_le_mul_of_nonneg_left hf this
    linarith
  have hB : 4 ≤ f * r^2 * L := by
    have := mul_le_mul_of_nonneg_left hfL (show 0 ≤ r^2 by positivity)
    linarith
  have hC : f^2 * r^2 * L ≤ (f*r*L)^2 := by
    have : 0 ≤ f^2 * r^2 * L := by positivity
    have := mul_le_mul_of_nonneg_left hL this
    linarith
  refine ⟨c1, by linarith, c3, by linarith, ?_, fun hw3 => ?_⟩
  · have h6 : log (5*f*r*exp (3/2*lrd)*max 1 (exp lM*f*w*√d)) ≤ 39 * L + log (max 1 w) := by
      linarith
    have := mul_le_mul_of_nonneg_left h6 hX
    generalize log (5*f*r*exp (3/2*lrd)*max 1 (exp lM*f*w*√d)) = Y at this ⊢
    linarith
  · have h7 : log (max 1 w) ≤ log 3 + 2 * L := by
      have e : 1 ≤ exp (2 * L) := one_le_exp (by linarith)
      have : log (max 1 w) ≤ log (3 * exp (2 * L)) :=
        log_le_log (by positivity) (max_le (by linarith) hw3)
      rwa [log_mul (by norm_num) (by positivity), log_exp] at this
    have h6 : log (5*f*r*exp (3/2*lrd)*max 1 (exp lM*f*w*√d)) ≤ 411/10 * L := by
      linarith
    have := mul_le_mul_of_nonneg_left h6 hX
    generalize log (5*f*r*exp (3/2*lrd)*max 1 (exp lM*f*w*√d)) = Y at this ⊢
    linarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowerBoundAlongResidues
section
open Filter Topology

namespace GlobalTheory

theorem lowerBound_along_residues : ∀ (d n : ℕ) (u : ℕ → ℝ) (γ : ℝ), 0 < n → (∀ r < n, ∀ ε : ℝ, 0 < ε → ∀ᶠ q : ℕ in atTop, (γ - ε) * (q : ℝ) ^ d ≤ u (n * q + r)) → ∀ ε : ℝ, 0 < ε → ∀ᶠ M : ℕ in atTop, (γ / (n : ℝ) ^ d - ε) * (M : ℝ) ^ d ≤ u M := by
  intro d n u γ hn h ε hε
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hnd : (0:ℝ) < (n:ℝ)^d := pow_pos hnR d
  set ε' := ε * (n:ℝ)^d / 2 with hε'
  have hε'pos : 0 < ε' := by positivity
  have h1 : ∀ᶠ q : ℕ in atTop, ∀ r ∈ Set.Iio n, (γ - ε') * (q:ℝ)^d ≤ u (n*q + r) :=
    (Filter.eventually_all_finite (Set.finite_Iio n)).2 (fun r hr => h r hr ε' hε'pos)
  have h2 : ∀ᶠ M : ℕ in atTop, ∀ r ∈ Set.Iio n, (γ - ε') * ((M / n : ℕ):ℝ)^d ≤ u (n*(M/n) + r) :=
    (Nat.tendsto_div_const_atTop hn.ne').eventually h1
  have hf : Tendsto (fun M : ℕ => ((M / n : ℕ):ℝ) / M) atTop (𝓝 (1 / n)) := by
    have hlow : Tendsto (fun M : ℕ => 1 / (n:ℝ) - 1 / (M:ℝ)) atTop (𝓝 (1 / n)) := by
      simpa using (tendsto_const_nhds (x := 1/(n:ℝ))).sub tendsto_one_div_atTop_nhds_zero_nat
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with M hM
      have hMR : (0:ℝ) < M := Nat.cast_pos.mpr hM
      have key : (n:ℝ) * ((M/n : ℕ):ℝ) + ((M % n : ℕ):ℝ) = M := by exact_mod_cast Nat.div_add_mod M n
      have hmod : ((M % n : ℕ):ℝ) < n := by exact_mod_cast Nat.mod_lt M hn
      have hq : (M:ℝ) - n ≤ n * ((M/n : ℕ):ℝ) := by linarith
      rw [div_sub_div _ _ hnR.ne' hMR.ne', div_le_div_iff₀ (by positivity) hMR]
      nlinarith [mul_le_mul_of_nonneg_right hq hMR.le]
    · filter_upwards [eventually_gt_atTop 0] with M hM
      have hMR : (0:ℝ) < M := Nat.cast_pos.mpr hM
      rw [div_le_div_iff₀ hMR hnR]
      have h0 : ((M / n : ℕ):ℝ) ≤ (M:ℝ) / n := Nat.cast_div_le
      rw [le_div_iff₀ hnR] at h0
      linarith
  have hg : Tendsto (fun M : ℕ => (γ - ε') * (((M / n : ℕ):ℝ) / M)^d) atTop (𝓝 ((γ - ε') * (1/(n:ℝ))^d)) :=
    (hf.pow d).const_mul _
  have hlim : (γ - ε') * (1/(n:ℝ))^d = γ / (n:ℝ)^d - ε/2 := by
    rw [one_div_pow, hε']; field_simp
  have h3 : ∀ᶠ M : ℕ in atTop, γ / (n:ℝ)^d - ε < (γ - ε') * (((M / n : ℕ):ℝ) / M)^d := by
    rw [hlim] at hg
    exact hg.eventually (lt_mem_nhds (by linarith))
  filter_upwards [h2, h3, eventually_gt_atTop 0] with M hM2 hM3 hM
  have hMR : (0:ℝ) < M := Nat.cast_pos.mpr hM
  have hMd : (0:ℝ) < (M:ℝ)^d := pow_pos hMR d
  have e1 := hM2 (M % n) (Nat.mod_lt M hn)
  rw [Nat.div_add_mod] at e1
  rw [div_pow, ← mul_div_assoc, lt_div_iff₀ hMd] at hM3
  linarith

end GlobalTheory
end

