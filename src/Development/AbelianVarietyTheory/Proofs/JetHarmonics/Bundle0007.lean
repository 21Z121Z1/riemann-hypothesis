import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.SplitUnramifiedPlaces
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsExtensionCharacter
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0003
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0005
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0004

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConvergentSubstOneVariableAndFormalAgreement
section
noncomputable section

namespace GlobalTheory.ConvSer.Bridge

def unitExp : ℕ ≃ (Unit →₀ ℕ) where
  toFun n := Finsupp.single () n
  invFun ν := ν ()
  left_inv n := by simp
  right_inv ν := by ext; simp

variable {K : Type} [NormedField K]

theorem powerSeriesConvergentSubstMv_eq_mv {τ : Type} (s : MvPowerSeries τ K) (f : PowerSeries K) :
    csub1 s f = csub (fun _ : Unit => s) f := by
  ext μ
  change ∑' n : ℕ, PowerSeries.coeff n f * MvPowerSeries.coeff μ (s ^ n) =
    ∑' ν : Unit →₀ ℕ, MvPowerSeries.coeff ν f * MvPowerSeries.coeff μ (∏ i : Unit, s ^ ν i)
  rw [← unitExp.tsum_eq]
  refine tsum_congr fun n => ?_
  simp [unitExp]

theorem powerSeriesEvalTsum_eq_mvPowerSeriesEvalTsum (f : PowerSeries K) (t : K) : ev1 f t = ev f (fun _ : Unit => t) := by
  unfold ev1 ev
  rw [← unitExp.tsum_eq]
  refine tsum_congr fun n => ?_
  simp [unitExp]

theorem powerSeriesHasSumAt_iff_mvPowerSeriesHasSumAt (f : PowerSeries K) (t a : K) : PowerSeriesHasSumAt f t a ↔ HS f (fun _ : Unit => t) a := by
  unfold PowerSeriesHasSumAt HS
  rw [← unitExp.hasSum_iff]
  have h : (fun ν : Unit →₀ ℕ => MvPowerSeries.coeff ν f * ∏ i : Unit, t ^ ν i) ∘ unitExp =
      fun n : ℕ => PowerSeries.coeff n f * t ^ n := by
    funext n
    simp [unitExp]
  rw [h]

theorem csub_C {σ τ : Type} [Fintype σ] (S : MvPowerSeries σ K) (x : σ → K) :
    csub (fun i => (MvPowerSeries.C (x i) : MvPowerSeries τ K)) S = MvPowerSeries.C (ev S x) := by
  have hC : ∀ ν : σ →₀ ℕ, (∏ i, (MvPowerSeries.C (x i) : MvPowerSeries τ K) ^ ν i) =
      MvPowerSeries.C (∏ i, x i ^ ν i) := fun ν => by simp [map_prod, map_pow]
  ext μ
  change ∑' ν : σ →₀ ℕ, MvPowerSeries.coeff ν S *
      MvPowerSeries.coeff μ (∏ i, (MvPowerSeries.C (x i) : MvPowerSeries τ K) ^ ν i) = _
  simp only [hC]
  by_cases h : μ = 0
  · subst h
    simp only [MvPowerSeries.coeff_zero_C]
    rfl
  · simp only [MvPowerSeries.coeff_C_of_ne_zero h, mul_zero, tsum_zero]

theorem shift1_eq_csub (F : MvPowerSeries (Fin 2) K) (y : K) :
    shift1 F y = csub (![PowerSeries.X, PowerSeries.C y] : Fin 2 → MvPowerSeries Unit K) F := by
  ext m
  have hc : ∀ p : PowerSeries K, MvPowerSeries.coeff (unitExp m) p = PowerSeries.coeff m p :=
    fun p => by simp [unitExp]
  change PowerSeries.coeff m (shift1 F y) = ∑' ν : Fin 2 →₀ ℕ, MvPowerSeries.coeff ν F *
    MvPowerSeries.coeff (unitExp m)
      (∏ i, (![PowerSeries.X, PowerSeries.C y] : Fin 2 → MvPowerSeries Unit K) i ^ ν i)
  have hterm : ∀ ν : Fin 2 →₀ ℕ, MvPowerSeries.coeff ν F * MvPowerSeries.coeff (unitExp m)
      (∏ i, (![PowerSeries.X, PowerSeries.C y] : Fin 2 → MvPowerSeries Unit K) i ^ ν i) =
      MvPowerSeries.coeff ν F * (if m = ν 0 then y ^ ν 1 else 0) := by
    intro ν
    rw [hc, Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← map_pow, mul_comm (PowerSeries.X ^ _), PowerSeries.coeff_C_mul_X_pow]
  simp only [hterm]
  rw [shift1, PowerSeries.coeff_mk]
  have hinj : Function.Injective
      (fun b : ℕ => Finsupp.single (0 : Fin 2) m + Finsupp.single 1 b) := by
    intro b b' h
    have h1 := congrArg (fun ν : Fin 2 →₀ ℕ => ν 1) h
    simpa using h1
  have hsupp : Function.support
      (fun ν : Fin 2 →₀ ℕ => MvPowerSeries.coeff ν F * (if m = ν 0 then y ^ ν 1 else 0)) ⊆
      Set.range (fun b : ℕ => Finsupp.single (0 : Fin 2) m + Finsupp.single 1 b) := by
    intro ν hν
    have h0 : m = ν 0 := by
      by_contra h
      exact hν (by simp [h])
    refine ⟨ν 1, ?_⟩
    ext i
    fin_cases i <;> simp [h0]
  refine Eq.trans ?_ (hinj.tsum_eq hsupp)
  refine tsum_congr fun b => ?_
  simp

theorem csub_eq_subst {σ τ : Type} [Fintype σ] (a : σ → MvPowerSeries τ K)
    (S : MvPowerSeries σ K) (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) :
    csub a S = MvPowerSeries.subst a S := by
  have hs : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  ext μ
  rw [MvPowerSeries.coeff_subst hs, ← tsum_eq_finsum (L := SummationFilter.unconditional (σ →₀ ℕ))
    (MvPowerSeries.coeff_subst_finite hs S μ)]
  change ∑' ν : σ →₀ ℕ, MvPowerSeries.coeff ν S * MvPowerSeries.coeff μ (∏ i, a i ^ ν i) = _
  refine tsum_congr fun ν => ?_
  rw [smul_eq_mul, Finsupp.prod_fintype _ _ (fun i => pow_zero _)]

theorem powerSeriesConvergentSubstMv_eq_subst {τ : Type} (a : MvPowerSeries τ K) (f : PowerSeries K)
    (ha : MvPowerSeries.constantCoeff a = 0) : csub1 a f = f.subst a := by
  rw [powerSeriesConvergentSubstMv_eq_mv, csub_eq_subst _ _ (fun _ => ha)]
  rfl

theorem csub_bridge : ∀ (K : Type) [NormedField K], (∀ (τ : Type) (s : MvPowerSeries τ K) (f : PowerSeries K), csub1 s f = csub (fun _ : Unit => s) f) ∧ (∀ (f : PowerSeries K) (t : K), ev1 f t = ev f (fun _ : Unit => t)) ∧ (∀ (f : PowerSeries K) (t a : K), PowerSeriesHasSumAt f t a ↔ HS f (fun _ : Unit => t) a) ∧ (∀ (σ τ : Type) [Fintype σ] (S : MvPowerSeries σ K) (x : σ → K), csub (fun i => (MvPowerSeries.C (x i) : MvPowerSeries τ K)) S = MvPowerSeries.C (ev S x)) ∧ (∀ (F : MvPowerSeries (Fin 2) K) (y : K), shift1 F y = csub (![PowerSeries.X, PowerSeries.C y] : Fin 2 → MvPowerSeries Unit K) F) ∧ (∀ (σ τ : Type) [Fintype σ] (a : σ → MvPowerSeries τ K) (S : MvPowerSeries σ K), (∀ i, MvPowerSeries.constantCoeff (a i) = 0) → csub a S = MvPowerSeries.subst a S) ∧ (∀ (τ : Type) (a : MvPowerSeries τ K) (f : PowerSeries K), MvPowerSeries.constantCoeff a = 0 → csub1 a f = f.subst a) := by
  intro K _
  exact ⟨fun _ s f => powerSeriesConvergentSubstMv_eq_mv s f, fun f t => powerSeriesEvalTsum_eq_mvPowerSeriesEvalTsum f t, fun f t a => powerSeriesHasSumAt_iff_mvPowerSeriesHasSumAt f t a,
    fun _ _ _ S x => csub_C S x, fun F y => shift1_eq_csub F y,
    fun _ _ _ a S ha => csub_eq_subst a S ha, fun _ a f ha => powerSeriesConvergentSubstMv_eq_subst a f ha⟩

end GlobalTheory.ConvSer.Bridge
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DifferentPowerUnramifiedIff
section
noncomputable section

open scoped TensorProduct

namespace GlobalTheory.Proof.different_power_unramified_iff

open GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces

private lemma eq_zero_of_natCast_mul_eq_zero_op (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R]
    [IsDomain R] [CharZero R] [Module.Finite ℤ R] (z : Op p R) (hz : (p : Op p R) * z = 0) :
    z = 0 := by
  have hp := (Fact.out : p.Prime)
  have : Module.Free ℤ R := Module.free_of_finite_type_torsion_free'
  have hsmul : (p : ℤ_[p]) • z = 0 := by
    rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
    exact hz
  rcases smul_eq_zero.mp hsmul with h | h
  · exact absurd h (Nat.cast_ne_zero.mpr hp.ne_zero)
  · exact h

theorem ow_p_torsionFree (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [IsDomain R] [CharZero R]
    [Module.Finite ℤ R] (w : Place p R) (x : w.Ow) (hx : (p : w.Ow) * x = 0) : x = 0 := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hy : (p : Op p R) * y ∈ Ideal.span {1 - w.e} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, map_natCast]
    exact hx
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hy
  have hey : w.e * y = 0 := by
    apply eq_zero_of_natCast_mul_eq_zero_op p R
    have hee : w.e * w.e = w.e := w.idem
    calc (p : Op p R) * (w.e * y) = w.e * ((p : Op p R) * y) := by ring
      _ = w.e * (a * (1 - w.e)) := by rw [ha]
      _ = a * (w.e - w.e * w.e) := by ring
      _ = 0 := by rw [hee, sub_self, mul_zero]
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
  exact ⟨y, by rw [mul_sub, mul_one, mul_comm y, hey, sub_zero]⟩

theorem map_eq_top_of_coprime {R S : Type} [CommRing R] [IsDedekindDomain R] [CommRing S]
    (f : R →+* S) (P : Ideal R) (hP : P.IsMaximal)
    (h : ∀ Q : Ideal R, Q.IsMaximal → Q ≠ P → Q.map f = ⊤) (Q : Ideal R) (hQ : Q ≠ ⊥)
    (hPQ : P ⊔ Q = ⊤) : Q.map f = ⊤ := by
  by_contra hne
  obtain ⟨M, hM, hQM⟩ := Ideal.exists_le_maximal _ hne
  have hQ' : Q ≤ M.comap f := Ideal.map_le_iff_le_comap.mp hQM
  have hprime : (M.comap f).IsPrime := Ideal.comap_isPrime f M
  have hbot : M.comap f ≠ ⊥ := fun h => hQ (eq_bot_iff.mpr (h ▸ hQ'))
  have hmax : (M.comap f).IsMaximal := hprime.isMaximal hbot
  by_cases hPeq : M.comap f = P
  · apply hP.ne_top
    rw [← hPQ]
    exact (sup_eq_left.mpr (hPeq ▸ hQ')).symm
  · apply hM.ne_top
    rw [eq_top_iff, ← h _ hmax hPeq]
    exact Ideal.map_comap_le

private lemma isIdempotentElem_Ow_eq_zero_or_one {p : ℕ} [Fact p.Prime] {OE : Type} [CommRing OE]
    (w : GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces.Place p OE) (g : w.Ow) (hg : IsIdempotentElem g) : g = 0 ∨ g = 1 := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective g
  have hee : w.e * w.e = w.e := w.idem
  have hyy : y * y - y ∈ Ideal.span {1 - w.e} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul]
    exact sub_eq_zero.mpr hg
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hyy
  have hey : w.e * (y * y) = w.e * y := by
    have : w.e * (y * y - y) = 0 := by
      rw [← ha]
      calc w.e * (a * (1 - w.e)) = a * (w.e - w.e * w.e) := by ring
        _ = 0 := by rw [hee, sub_self, mul_zero]
    rw [mul_sub] at this
    exact sub_eq_zero.mp this
  have hf : IsIdempotentElem (w.e * y) := by
    show w.e * y * (w.e * y) = w.e * y
    calc w.e * y * (w.e * y) = (w.e * w.e) * (y * y) := by ring
      _ = w.e * y := by rw [hee, hey]
  have hfe : w.e * y * w.e = w.e * y := by
    calc w.e * y * w.e = (w.e * w.e) * y := by ring
      _ = w.e * y := by rw [hee]
  have hmk : (Ideal.Quotient.mk (Ideal.span {1 - w.e}) y) =
      Ideal.Quotient.mk (Ideal.span {1 - w.e}) (w.e * y) := by
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton']
    exact ⟨y, by ring⟩
  rw [hmk]
  rcases w.primitive _ hf hfe with h | h
  · left
    rw [h, map_zero]
  · right
    rw [h, ← map_one (Ideal.Quotient.mk (Ideal.span {1 - w.e})), Ideal.Quotient.eq,
      Ideal.mem_span_singleton']
    exact ⟨-1, by ring⟩

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra in

theorem different_pow_and_unramified_iff (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R]
    [IsDedekindDomain R] [CharZero R] [Module.Finite ℤ R] (w : GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces.Place p R)
    (P : Ideal R) (hP : P.IsMaximal) (hpP : (p : R) ∈ P) (hm : (P.map w.toOw).IsMaximal)
    (hQ : ∀ Q : Ideal R, Q.IsMaximal → Q ≠ P → Q.map w.toOw = ⊤) :
    (∃ a b : ℕ, 0 < b ∧ (differentIdeal ℤ R).map w.toOw ^ b = Ideal.span {(p : w.Ow) ^ a}) ∧
      (w.IsUnramified ↔ (differentIdeal ℤ R).map w.toOw = ⊤) := by
  have hp := (Fact.out : p.Prime)
  have hDne : differentIdeal ℤ R ≠ ⊥ := differentIdeal_ne_bot
  have hPtop : P.map w.toOw ≠ ⊤ := hm.ne_top
  have hpR : (p : R) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hIne : Ideal.span {(p : R)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact hpR
  have hIP : Ideal.span {(p : R)} ≤ P := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hpP
  obtain ⟨J, hPJ, hIJ⟩ := Ideal.eq_prime_pow_mul_coprime hIne P
  set c := Multiset.count P (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(p : R)}))
    with hc
  have hJne : J ≠ ⊥ := by
    rintro rfl
    rw [Ideal.mul_bot] at hIJ
    exact hIne hIJ
  have hpOw : Ideal.span {(p : w.Ow)} = P.map w.toOw ^ c := by
    have hsp : Ideal.span {(p : w.Ow)} = (Ideal.span {(p : R)}).map w.toOw := by
      rw [Ideal.map_span, Set.image_singleton, map_natCast]
    rw [hsp, hIJ, Ideal.map_mul, Ideal.map_pow,
      map_eq_top_of_coprime w.toOw P hP hQ J hJne hPJ, Ideal.mul_top]
  have hcpos : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · exfalso
      rw [h0, pow_zero, Ideal.one_eq_top, Ideal.top_mul] at hIJ
      rw [hIJ] at hIP
      apply hP.ne_top
      rw [← hPJ]
      exact (sup_eq_left.mpr hIP).symm
    · exact h0
  obtain ⟨J', hPJ', hDJ'⟩ := Ideal.eq_prime_pow_mul_coprime hDne P
  set k := Multiset.count P (UniqueFactorizationMonoid.normalizedFactors (differentIdeal ℤ R))
    with hk
  have hJ'ne : J' ≠ ⊥ := by
    rintro rfl
    rw [Ideal.mul_bot] at hDJ'
    exact hDne hDJ'
  have hDmap : (differentIdeal ℤ R).map w.toOw = P.map w.toOw ^ k := by
    rw [hDJ', Ideal.map_mul, Ideal.map_pow,
      map_eq_top_of_coprime w.toOw P hP hQ J' hJ'ne hPJ', Ideal.mul_top]
  refine ⟨⟨k, c, hcpos, ?_⟩, ?_⟩
  · rw [hDmap, ← pow_mul, Nat.mul_comm k c, pow_mul, ← hpOw, Ideal.span_singleton_pow]
  have hUnr : w.IsUnramified ↔ c = 1 := by
    show (Ideal.span {(p : w.Ow)}).IsMaximal ↔ c = 1
    rw [hpOw]
    constructor
    · intro hmax
      by_contra hc1
      have hc2 : 2 ≤ c := by omega
      have heq : P.map w.toOw ^ c = P.map w.toOw :=
        hmax.eq_of_le hPtop (Ideal.pow_le_self hcpos.ne')
      have hidem : IsIdempotentElem (P.map w.toOw) := by
        show P.map w.toOw * P.map w.toOw = P.map w.toOw
        apply le_antisymm Ideal.mul_le_right
        calc P.map w.toOw = P.map w.toOw ^ c := heq.symm
          _ ≤ P.map w.toOw ^ 2 := Ideal.pow_le_pow_right hc2
          _ = P.map w.toOw * P.map w.toOw := sq _
      have hfg : (P.map w.toOw).FG := Ideal.FG.map (IsNoetherian.noetherian P) w.toOw
      obtain ⟨g, hg, hgspan⟩ := (Ideal.isIdempotentElem_iff_of_fg _ hfg).mp hidem
      have hpmem : (p : w.Ow) ∈ P.map w.toOw := by
        rw [← map_natCast w.toOw p]
        exact Ideal.mem_map_of_mem _ hpP
      rcases isIdempotentElem_Ow_eq_zero_or_one w g hg with rfl | rfl
      · rw [hgspan] at hpmem
        have hp0 : (p : w.Ow) = 0 := by simpa using hpmem
        have h10 : (1 : w.Ow) = 0 := ow_p_torsionFree p R w 1 (by rw [mul_one]; exact hp0)
        apply hPtop
        rw [Ideal.eq_top_iff_one, h10]
        exact zero_mem _
      · apply hPtop
        rw [hgspan]
        exact Ideal.span_singleton_one
    · intro h1
      rw [h1, pow_one]
      exact hm
  have hDtop : (differentIdeal ℤ R).map w.toOw = ⊤ ↔ ¬ P ∣ differentIdeal ℤ R := by
    constructor
    · intro h hdvd
      apply hPtop
      rw [eq_top_iff, ← h]
      exact Ideal.map_mono (Ideal.le_of_dvd hdvd)
    · intro h
      apply map_eq_top_of_coprime w.toOw P hP hQ _ hDne
      by_contra hne
      apply h
      rw [Ideal.dvd_iff_le, hP.eq_of_le hne le_sup_left]
      exact le_sup_right
  have hunder : P.under ℤ = Ideal.span {(p : ℤ)} := by
    have hpZ : (Ideal.span {(p : ℤ)}).IsMaximal := by
      have hpr : (Ideal.span {(p : ℤ)}).IsPrime :=
        (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr
          (Nat.prime_iff_prime_int.mp hp)
      exact hpr.isMaximal (by
        rw [Ne, Ideal.span_singleton_eq_bot]
        exact_mod_cast hp.ne_zero)
    symm
    apply hpZ.eq_of_le (Ideal.comap_ne_top _ hP.ne_top)
    rw [Ideal.span_le, Set.singleton_subset_iff]
    show algebraMap ℤ R (p : ℤ) ∈ P
    rw [map_natCast]
    exact hpP
  have : P.IsPrime := hP.isPrime
  have : P.LiesOver (Ideal.span {(p : ℤ)}) := ⟨hunder.symm⟩
  have hspZ : Ideal.span {(p : ℤ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  have hmapZ : (Ideal.span {(p : ℤ)}).map (algebraMap ℤ R) = Ideal.span {(p : R)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  have hram : (Ideal.span {(p : ℤ)}).ramificationIdx' P = c := by
    apply Ideal.ramificationIdx'_spec
    · rw [hmapZ, hIJ]
      exact le_trans (Ideal.mul_mono_right le_top) (le_of_eq (Ideal.mul_top _))
    · rw [hmapZ]
      intro hle
      have hdvd : P ^ c * P ∣ P ^ c * J := by
        rw [← pow_succ, ← hIJ, Ideal.dvd_iff_le]
        exact hle
      have hPc : P ^ c ≠ 0 := pow_ne_zero _ (by
        intro h0
        exact hP.ne_top (by
          rw [Ideal.zero_eq_bot] at h0
          rw [h0] at hIP
          exact absurd (le_bot_iff.mp hIP) hIne))
      have hPJdvd : P ∣ J := (mul_dvd_mul_iff_left hPc).mp hdvd
      apply hP.ne_top
      rw [← hPJ]
      exact (sup_eq_left.mpr (Ideal.le_of_dvd hPJdvd)).symm
  rw [hDtop, hUnr, not_dvd_differentIdeal_iff, Algebra.isUnramifiedAt_iff_of_isDedekindDomain,
    ← Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {(p : ℤ)}) P hspZ, hram]

end GlobalTheory.Proof.different_power_unramified_iff
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsGeneratingCharacters
section
namespace GlobalTheory.PrimaryCharacter

theorem exists_extend_of_injective {H M F : Type} [CommGroup H] [CommGroup M] [Field F] [IsAlgClosed F]
    (Φ : H →* M) (hΦ : Function.Injective Φ) (χ : H →* Fˣ) : ∃ κ : M →* Fˣ, ∀ x, κ (Φ x) = χ x := by
  first
  | exact @_root_.GlobalTheory.ExtensionCharacter.exists_extension_character
  | exact _root_.GlobalTheory.ExtensionCharacter.exists_extension_character
  | (apply _root_.GlobalTheory.ExtensionCharacter.exists_extension_character <;> assumption)
  | (intros; apply _root_.GlobalTheory.ExtensionCharacter.exists_extension_character <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ExtensionCharacter.exists_extension_character <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ExtensionCharacter.exists_extension_character ..)

theorem exists_factor_of_ker_le {H M F : Type} [CommGroup H] [CommGroup M] [Field F] [IsAlgClosed F]
    (Φ : H →* M) (χ : H →* Fˣ) (h : Φ.ker ≤ χ.ker) : ∃ κ : M →* Fˣ, ∀ x, κ (Φ x) = χ x := by
  obtain ⟨κ, hκ⟩ := exists_extend_of_injective (QuotientGroup.kerLift Φ)
    (QuotientGroup.kerLift_injective Φ) (QuotientGroup.lift Φ.ker χ h)
  exact ⟨κ, fun x => hκ (QuotientGroup.mk x)⟩

end GlobalTheory.PrimaryCharacter
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIntegralPolyOfCharacter
section
open GlobalTheory.ConvSer

namespace GlobalTheory.ConvSer

theorem exists_integral_poly_of_character (K : Type) [NormedField K] [IsUltrametricDist K]
    (G : Type) [AddCommGroup G] [Fintype G] (x χ : G → K) (hx : Function.Injective x)
    (hχ : ∀ i j, χ (i + j) = χ i * χ j)
    (hc : ∀ k : Fin (Fintype.card G), ∃ c : Fin (Fintype.card G) → Fin (Fintype.card G) → K,
      (∀ a b, ‖c a b‖ ≤ 1) ∧
        ∀ i j, x (i + j) ^ (k : ℕ) = ∑ a, ∑ b, c a b * x i ^ (a : ℕ) * x j ^ (b : ℕ)) :
    ∃ g : Polynomial K, (∀ k, ‖g.coeff k‖ ≤ 1) ∧ ∀ i, g.eval (x i) = χ i := by
  classical
  choose c hc1 hc2 using hc
  have van : ∀ v : Fin (Fintype.card G) → K, (∀ i, ∑ a, v a * x i ^ (a : ℕ) = 0) → v = 0 := by
    intro v hv
    exact Matrix.eq_zero_of_forall_index_sum_mul_pow_eq_zero
      (f := fun j => x ((Fintype.equivFin G).symm j))
      (hx.comp (Fintype.equivFin G).symm.injective) (fun j => hv _)
  set g : Polynomial K := Lagrange.interpolate Finset.univ x χ with hg
  have hinj : Set.InjOn x (Finset.univ : Finset G) := hx.injOn
  have hdeg : g.degree < (Fintype.card G : ℕ) := by
    exact Lagrange.degree_interpolate_lt (r := χ) hinj
  have hev : ∀ i, g.eval (x i) = χ i := fun i =>
    Lagrange.eval_interpolate_at_node χ hinj (Finset.mem_univ i)
  have hpos : 0 < Fintype.card G := Fintype.card_pos
  have hnat : g.natDegree < Fintype.card G := by
    by_cases h0 : g = 0
    · simpa [h0] using hpos
    · exact (Polynomial.natDegree_lt_iff_degree_lt h0).2 hdeg
  have hsum : ∀ i, χ i = ∑ a : Fin (Fintype.card G), g.coeff a * x i ^ (a : ℕ) := by
    intro i
    rw [← hev i, Polynomial.eval_eq_sum_range' hnat,
      Fin.sum_univ_eq_sum_range (fun a => g.coeff a * x i ^ a)]
  have key : ∀ a b : Fin (Fintype.card G),
      g.coeff a * g.coeff b = ∑ k : Fin (Fintype.card G), g.coeff k * c k a b := by
    have h1 : ∀ j, (fun a : Fin (Fintype.card G) => ∑ b : Fin (Fintype.card G),
        (g.coeff a * g.coeff b - ∑ k : Fin (Fintype.card G), g.coeff k * c k a b)
          * x j ^ (b : ℕ)) = 0 := by
      intro j
      apply van
      intro i
      have e1 : χ i * χ j = ∑ a : Fin (Fintype.card G), ∑ b : Fin (Fintype.card G),
          g.coeff a * g.coeff b * x j ^ (b : ℕ) * x i ^ (a : ℕ) := by
        rw [hsum i, hsum j, Finset.sum_mul_sum]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
      have e2 : χ (i + j) = ∑ a : Fin (Fintype.card G), ∑ b : Fin (Fintype.card G),
          (∑ k : Fin (Fintype.card G), g.coeff k * c k a b) * x j ^ (b : ℕ) * x i ^ (a : ℕ) := by
        rw [hsum (i + j)]
        simp_rw [hc2, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => by ring
      have e3 := hχ i j
      rw [e1, e2] at e3
      simp_rw [Finset.sum_mul, sub_mul, Finset.sum_sub_distrib]
      rw [sub_eq_zero]
      exact e3.symm
    intro a b
    have h2 := van _ (fun j => congrFun (h1 j) a)
    exact sub_eq_zero.1 (congrFun h2 b)
  haveI : Nonempty (Fin (Fintype.card G)) := ⟨⟨0, hpos⟩⟩
  obtain ⟨m, -, hm⟩ := Finset.exists_max_image Finset.univ
    (fun a : Fin (Fintype.card G) => ‖g.coeff a‖) Finset.univ_nonempty
  have hM : ‖g.coeff m‖ * ‖g.coeff m‖ ≤ ‖g.coeff m‖ := by
    rw [← norm_mul, key]
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _)
    intro k _
    rw [norm_mul]
    calc ‖g.coeff k‖ * ‖c k m m‖ ≤ ‖g.coeff k‖ * 1 :=
          mul_le_mul_of_nonneg_left (hc1 k m m) (norm_nonneg _)
      _ ≤ ‖g.coeff m‖ := by simpa using hm k (Finset.mem_univ k)
  have hM1 : ‖g.coeff m‖ ≤ 1 := by nlinarith [norm_nonneg (g.coeff m)]
  refine ⟨g, fun k => ?_, hev⟩
  by_cases hk : k < Fintype.card G
  · exact (hm ⟨k, hk⟩ (Finset.mem_univ _)).trans hM1
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
    simp

end GlobalTheory.ConvSer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FiniteAugmentedConnectedPartLocalisation
section
open Polynomial

namespace GlobalTheory

theorem finite_augmented_connected_part_localisation :
    ∀ (F : Type) [Field F] [IsAlgClosed F] (W : ValuationSubring F) (p : W), (∀ a : W, ¬ IsUnit a → ∃ n : ℕ, a ^ n ∈ Ideal.span {p}) → ∀ (A : Type) [CommRing A] [Algebra W A] [Module.Finite W A] (aug : A →ₐ[W] W), ∃ s : A, Function.Surjective (algebraMap A (Localization.Away s)) ∧ (∃ m : ℕ, ((RingHom.ker aug).map (algebraMap A (Localization.Away s))) ^ m ≤ Ideal.span {algebraMap W (Localization.Away s) p}) ∧ ∀ (R : Type) [CommRing R] [Algebra W R] (w : A →ₐ[W] R), (∀ t ∈ RingHom.ker aug, IsNilpotent (w t)) → IsUnit (w s) := by
  first
  | exact @_root_.GlobalTheory.MonicSeparableProduct.main
  | exact _root_.GlobalTheory.MonicSeparableProduct.main
  | (apply _root_.GlobalTheory.MonicSeparableProduct.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.MonicSeparableProduct.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.MonicSeparableProduct.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.MonicSeparableProduct.main ..)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ReInnerLeOnImageOfIntertwiningStatement
section
open Finset
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.re_inner_le_on_image_of_intertwining' : ∀ (T N : Type) [NormedAddCommGroup T] [InnerProductSpace ℂ T] [FiniteDimensional ℂ T] [NormedAddCommGroup N] [InnerProductSpace ℂ N] (Φ : T →ₗ[ℂ] N) (A : T →ₗ[ℂ] T) (B : N →ₗ[ℂ] N) (C : ℝ), A.IsSymmetric → B.IsSymmetric → (∀ x, Φ (A x) = B (Φ x)) → (∀ x, (⟪x, A x⟫_ℂ).re ≤ C * ‖x‖ ^ 2) → ∀ x, (⟪Φ x, B (Φ x)⟫_ℂ).re ≤ C * ‖Φ x‖ ^ 2 := by
  first | exact @GlobalTheory.re_inner_le_on_image_of_intertwining | exact GlobalTheory.re_inner_le_on_image_of_intertwining | (intros; apply GlobalTheory.re_inner_le_on_image_of_intertwining <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumNormAddSqLeOfBoundsStatement
section
open Finset
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_norm_add_sq_le_add_sq_mul : ∀ (V ι : Type) [NormedAddCommGroup V] [Fintype ι] (u v : ι → V) (c s N : ℝ), 0 ≤ c → 0 ≤ s → 0 ≤ N → ∑ i, ‖u i‖ ^ 2 ≤ c ^ 2 * N → ∑ i, ‖v i‖ ^ 2 ≤ s ^ 2 * N → ∑ i, ‖u i + v i‖ ^ 2 ≤ (c + s) ^ 2 * N := by
  first | exact @GlobalTheory.sum_norm_add_sq_le_of_bounds | exact GlobalTheory.sum_norm_add_sq_le_of_bounds | (intros; apply GlobalTheory.sum_norm_add_sq_le_of_bounds <;> assumption)
end

