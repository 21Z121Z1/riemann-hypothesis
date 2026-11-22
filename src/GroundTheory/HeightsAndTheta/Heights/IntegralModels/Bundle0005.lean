import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.FiniteIntegralClosureCharZero
import GroundTheory.ArithmeticGeometry.ToricVarieties.Bundle0001
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0060

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.PDominatingDVR
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

theorem isFractionRing_of_subalgebra {A K : Type*} [CommRing A] [IsDomain A] [Field K]
    [Algebra A K] [IsFractionRing A K] (B : Subalgebra A K) : IsFractionRing B K := by
  rw [IsFractionRing, isLocalization_iff]
  refine ⟨fun y => ?_, fun z => ?_, fun {u v} h => ⟨1, ?_⟩⟩
  · have hy : (y : B) ≠ 0 := nonZeroDivisors.coe_ne_zero y
    exact isUnit_iff_ne_zero.2 fun h => hy (Subtype.ext h)
  · obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj (nonZeroDivisors A) z
    have hs : algebraMap A B s ≠ 0 := fun h0 =>
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2 (congrArg Subtype.val h0)
    exact ⟨⟨algebraMap A B a, ⟨_, mem_nonZeroDivisors_of_ne_zero hs⟩⟩, h⟩
  · simpa using Subtype.ext h

set_option maxHeartbeats 400000 in

theorem DominatingDVR.proof (hKA : KrullAkizuki.Statement) (hBU : BlowUpChart.Statement) :
    DominatingDVR.Statement := by
  intro A _ _ _ _ hAf K _ _ _

  obtain ⟨n, x, hx⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian (IsLocalRing.maximalIdeal A))
  have hx' : Ideal.span (Set.range x) = IsLocalRing.maximalIdeal A := hx
  have hx0 : ∃ j, x j ≠ 0 := by
    by_contra h
    push Not at h
    apply hAf
    rw [IsLocalRing.isField_iff_maximalIdeal_eq, ← hx']
    exact Submodule.span_eq_bot.mpr (by rintro _ ⟨j, rfl⟩; exact h j)
  obtain ⟨i, hxi, hunit, -⟩ := hBU A K n x hx' hx0

  set B := blowUpChart K x i
  have : IsNoetherianRing B :=
    isNoetherianRing_of_fg (Subalgebra.fg_def.2 ⟨_, Set.finite_range _, rfl⟩)
  have : IsFractionRing B K := isFractionRing_of_subalgebra B

  set xi : B := algebraMap A B (x i)
  have hspan : Ideal.span {xi} ≠ ⊤ := fun h => hunit (Ideal.span_singleton_eq_top.mp h)
  obtain ⟨q, hq⟩ := Ideal.nonempty_minimalPrimes hspan
  have : q.IsPrime := hq.1.1
  have hxiq : xi ∈ q := hq.1.2 (Ideal.mem_span_singleton_self _)
  have hxi0 : xi ≠ 0 := fun h => hxi (IsFractionRing.injective A K (by
    simpa [xi] using congrArg Subtype.val h))
  have hq1 : q.height = 1 := le_antisymm
    (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ q hq)
    ((Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hxi0)).trans (Ideal.height_mono hq.1.2))
  have hmq : (IsLocalRing.maximalIdeal A).map (algebraMap A B) ≤ q := by
    rw [← hx', Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    have e : algebraMap A B (x j) =
        ⟨algebraMap A K (x j) / algebraMap A K (x i), Algebra.subset_adjoin ⟨j, rfl⟩⟩ * xi := by
      apply Subtype.ext
      have : algebraMap A K (x i) ≠ 0 := fun h => hxi (IsFractionRing.injective A K (by simpa using h))
      simp [xi, div_mul_cancel₀ _ this]
    exact e ▸ q.mul_mem_left _ hxiq

  set R := Localization.subalgebra.ofField K q.primeCompl q.primeCompl_le_nonZeroDivisors
  have : IsLocalization.AtPrime R q := (inferInstance : IsLocalization q.primeCompl R)
  have : IsLocalRing R := IsLocalization.AtPrime.isLocalRing R q
  have : IsNoetherianRing R := IsLocalization.isNoetherianRing q.primeCompl R inferInstance
  have hdimR : ringKrullDim R = 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height q R, hq1]
    rfl

  set C := integralClosure R K
  have : IsDedekindDomain C := hKA.2 R hdimR K
  have : IsFractionRing C K := isFractionRing_of_subalgebra C
  have hinj : Function.Injective (algebraMap R C) := fun a b h =>
    by
    have h' : ((algebraMap R C a : C) : K) = ((algebraMap R C b : C) : K) := congrArg _ h
    exact IsFractionRing.injective R K h'
  obtain ⟨P, hPmax, hPc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := C)
    (IsLocalRing.maximalIdeal R) (by rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]; exact bot_le)
  have : P.IsPrime := hPmax.isPrime
  have hPbot : P ≠ ⊥ := by
    rintro rfl
    have hF : IsField R := by
      rw [IsLocalRing.isField_iff_maximalIdeal_eq, ← hPc, Ideal.comap_bot_of_injective _ hinj]
    have h0 := ringKrullDim_eq_zero_of_isField hF
    rw [hdimR] at h0
    exact one_ne_zero h0

  set V := Localization.subalgebra.ofField K P.primeCompl P.primeCompl_le_nonZeroDivisors
  letI : CommRing V := Subalgebra.toCommRing (R := C) (A := K) V
  have : IsDomain V := Subalgebra.isDomain (R := C) (A := K) V
  have : IsLocalization.AtPrime V P := (inferInstance : IsLocalization P.primeCompl V)
  have hV : IsDiscreteValuationRing V :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain C hPbot V
  let φ : A →+* V :=
    (algebraMap C V).comp ((algebraMap R C).comp ((algebraMap B R).comp (algebraMap A B)))
  have hφ : ∀ a, (φ a : K) = algebraMap A K a := fun a => rfl
  refine ⟨Subalgebra.toSubring (R := C) V, hV, fun a => ?_, fun a => ?_⟩
  · show algebraMap A K a ∈ V
    exact hφ a ▸ (φ a).2
  show ¬ IsUnit (φ a) ↔ _
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  refine ⟨fun h ha => h (ha.map φ), fun ha hu => ?_⟩
  have hb : algebraMap A B a ∈ q := hmq (Ideal.mem_map_of_mem _ (by
    rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]))
  have hr : algebraMap B R (algebraMap A B a) ∈ IsLocalRing.maximalIdeal R :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff R q _).mpr hb
  rw [← hPc, Ideal.mem_comap] at hr
  exact (IsLocalization.AtPrime.isUnit_to_map_iff V P _).mp hu hr

end GroundTheory.Heights₂.Heights.Model
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.PFiniteIntegralClosure
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

theorem FiniteIntegralClosure.proof : FiniteIntegralClosure.Statement := by
  intro A _ _ _ K _ _ _ L _ _ _ _ _
  obtain ⟨p, hp⟩ := CharP.exists A
  rcases CharP.char_is_prime_or_zero A p with hp' | rfl
  · have : Fact p.Prime := ⟨hp'⟩
    exact finite_integralClosure_of_charP p A K L
  · have : CharZero A := CharP.charP_to_charZero A
    exact finite_integralClosure_of_charZero A K L

end GroundTheory.Heights₂.Heights.Model
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.PHeightOneIntersection
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

theorem HeightOneIntersection.proof : HeightOneIntersection.Statement := by
  intro A _ _ _ _ K _ _ _
  apply le_antisymm
  · intro x hx
    simp only [Submodule.mem_iInf]
    intro p _
    exact ⟨1, (Ideal.ne_top_iff_one _).mp p.isPrime.ne_top, by rwa [one_smul]⟩
  · intro x hx
    simp only [Submodule.mem_iInf] at hx
    change x ∈ (⊥ : Subalgebra A K)
    rw [Algebra.mem_bot]
    obtain ⟨y, hy⟩ := GroundTheory.Arith.Toric.mem_range_of_forall_height_one (A := A) (K := K) x
      (fun p hp h1 => by
        obtain ⟨s, hs, hsx⟩ := hx ⟨p, hp⟩ h1
        change s • x ∈ (⊥ : Subalgebra A K) at hsx
        obtain ⟨a, ha⟩ := Algebra.mem_bot.mp hsx
        refine ⟨a, s, hs, ?_⟩
        rw [Algebra.smul_def] at ha
        rw [ha, mul_comm])
    exact ⟨y, hy⟩

end GroundTheory.Heights₂.Heights.Model
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.PLatticesAgree
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

variable {A : Type} [CommRing A] [IsDomain A]
  {K : Type} [Field K] [Algebra A K] [IsFractionRing A K]
  {V : Type} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]

theorem exists_ne_zero_smul_mem_of_span_eq_top (M : Submodule A V)
    (hM : Submodule.span K (M : Set V) = ⊤) (v : V) : ∃ d : A, d ≠ 0 ∧ d • v ∈ M :=
  _root_.UpperTheory.Reformulated.B.SmulMemOfSpanEqTop.exists_ne_zero_smul_mem_of_span_eq_top M hM v

theorem mem_of_forall_mem_localizedIn (hHOI : HeightOneIntersection.Statement)
    [IsNoetherianRing A] [IsIntegrallyClosed A] (M : Submodule A V) [Module.Projective A M]
    (hM : Submodule.span K (M : Set V) = ⊤) (v : V)
    (hv : ∀ p : PrimeSpectrum A, p.asIdeal.height = 1 → v ∈ localizedIn p.asIdeal M) : v ∈ M := by
  obtain ⟨d, hd, hdv⟩ := exists_ne_zero_smul_mem_of_span_eq_top (K := K) M hM v
  obtain ⟨c, hc⟩ := Module.projective_def.mp (inferInstance : Module.Projective A M)
  set x : M := ⟨d • v, hdv⟩ with hx
  have hdK : algebraMap A K d ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr hd

  have hdiv : ∀ y : M, ∃ a : A, c x y = d * a := by
    intro y
    have hq : algebraMap A K (c x y) / algebraMap A K d ∈
        Subalgebra.toSubmodule (⊥ : Subalgebra A K) := by
      rw [hHOI A K]
      simp only [Submodule.mem_iInf]
      intro p hp
      obtain ⟨s, hs, hsv⟩ := hv p hp
      refine ⟨s, hs, ?_⟩
      set x' : M := ⟨s • v, hsv⟩
      have hxx : d • x' = s • x := by
        ext; simp only [x', hx, SetLike.val_smul, smul_smul, mul_comm]
      have hcc : d * c x' y = s * c x y := by
        have := congrArg (fun z => c z y) hxx
        simpa [map_smul] using this
      refine Algebra.mem_bot.mpr ⟨c x' y, ?_⟩
      rw [Algebra.smul_def, ← mul_div_assoc, ← map_mul, ← hcc, map_mul,
        mul_div_right_comm, div_self hdK, one_mul]
    obtain ⟨a, ha⟩ := Algebra.mem_bot.mp hq
    refine ⟨a, IsFractionRing.injective A K ?_⟩
    rw [map_mul, ha, mul_div_cancel₀ _ hdK]
  choose a ha using hdiv
  have hw : (∑ y ∈ (c x).support, a y • (y : V)) ∈ M :=
    M.sum_mem fun y _ => M.smul_mem (a y) y.2
  have hsum : d • v = d • ∑ y ∈ (c x).support, a y • (y : V) := by
    have h1 : ((Finsupp.linearCombination A id (c x) : M) : V) = d • v := by rw [hc x]
    rw [← h1, Finsupp.linearCombination_apply, Finsupp.sum, Submodule.coe_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Submodule.coe_smul, id, ha y, mul_smul]
  have hvw : v = ∑ y ∈ (c x).support, a y • (y : V) := by
    rw [← algebraMap_smul K d v, ← algebraMap_smul K d (∑ y ∈ (c x).support, a y • (y : V))]
      at hsum
    exact smul_right_injective V hdK hsum
  rw [hvw]
  exact hw

theorem LatticesAgree.proof (hHOI : HeightOneIntersection.Statement) : LatticesAgree.Statement := by
  intro A _ _ _ _ K _ _ _ V _ _ _ _ _ M N _ hMp _ hNp hM hN hMN
  have sub : ∀ (P Q : Submodule A V), Module.Projective A P →
      Submodule.span K (P : Set V) = ⊤ →
      (∀ p : PrimeSpectrum A, p.asIdeal.height = 1 →
        localizedIn p.asIdeal Q = localizedIn p.asIdeal P) → Q ≤ P := by
    intro P Q hP hPs hQP v hvQ
    exact mem_of_forall_mem_localizedIn (K := K) hHOI P hPs v fun p hp =>
      hQP p hp ▸ ⟨1, fun h => p.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by simpa using hvQ⟩
  exact le_antisymm (sub N M hNp hN fun p hp => hMN p hp)
    (sub M N hMp hM fun p hp => (hMN p hp).symm)

end GroundTheory.Heights₂.Heights.Model
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.PMertensUpper
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open Real

lemma div_le_padicValNat_factorial (N p : ℕ) (hp : p.Prime) :
    N / p ≤ padicValNat p N.factorial := by
  have := Fact.mk hp
  rcases lt_or_ge N p with h | h
  · rw [Nat.div_eq_of_lt h]; exact Nat.zero_le _
  · rw [padicValNat_factorial (b := Nat.log p N + 1) (Nat.lt_succ_self _)]
    have h1 : 1 ∈ Finset.Ico 1 (Nat.log p N + 1) := by
      have := Nat.log_pos hp.one_lt h
      simp only [Finset.mem_Ico]; omega
    have := Finset.single_le_sum (f := fun i => N / p ^ i) (fun _ _ => Nat.zero_le _) h1
    simpa using this

lemma prod_pow_div_dvd_factorial (N : ℕ) :
    (∏ p ∈ (Finset.Iic N).filter Nat.Prime, p ^ (N / p)) ∣ N.factorial := by
  have : ((∏ p ∈ (Finset.Iic N).filter Nat.Prime, p ^ (N / p) : ℕ) : ℤ) ∣ (N.factorial : ℤ) := by
    push_cast
    apply Finset.prod_dvd_of_coprime
    · intro p hp q hq hpq
      have hp' := (Finset.mem_filter.1 hp).2
      have hq' := (Finset.mem_filter.1 hq).2
      simp only [Function.onFun]
      exact_mod_cast Nat.isCoprime_iff_coprime.2 (Nat.coprime_pow_primes _ _ hp' hq' hpq)
    · intro p hp
      have hp' := (Finset.mem_filter.1 hp).2
      exact_mod_cast (pow_dvd_pow p (div_le_padicValNat_factorial N p hp')).trans
        pow_padicValNat_dvd
  exact_mod_cast this

theorem MertensUpper.proof : MertensUpper.Statement := by
  refine ⟨Real.log 4, fun B hB => ?_⟩
  set N := ⌊B⌋₊ with hN
  set P := (Finset.Iic N).filter Nat.Prime with hP
  have hN2 : 2 ≤ N := Nat.le_floor (by exact_mod_cast hB)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hNB : (N : ℝ) ≤ B := Nat.floor_le (by linarith)
  have hpos : ∀ p ∈ P, (1 : ℝ) ≤ p := fun p hp => by
    exact_mod_cast (Finset.mem_filter.1 hp).2.one_lt.le

  have hle : ∏ p ∈ P, p ^ (N / p) ≤ N ^ N :=
    (Nat.le_of_dvd (Nat.factorial_pos _) (prod_pow_div_dvd_factorial N)).trans
      (Nat.factorial_le_pow N)
  have hlog : ∑ p ∈ P, ((N / p : ℕ) : ℝ) * Real.log p ≤ N * Real.log N := by
    have hprod : (0 : ℝ) < ∏ p ∈ P, ((p : ℝ) ^ (N / p)) :=
      Finset.prod_pos fun p hp => pow_pos (by linarith [hpos p hp]) _
    have h := Real.log_le_log hprod
      (show ∏ p ∈ P, ((p : ℝ) ^ (N / p)) ≤ (N : ℝ) ^ N by exact_mod_cast hle)
    rw [Real.log_prod (fun p hp => (pow_pos (by linarith [hpos p hp]) _).ne'),
      Real.log_pow] at h
    simpa [Real.log_pow] using h

  have hfloor : ∀ p ∈ P, ((N : ℝ) / p - 1) * Real.log p ≤ ((N / p : ℕ) : ℝ) * Real.log p :=
    fun p hp => mul_le_mul_of_nonneg_right
      (by rw [← Nat.floor_div_eq_div (K := ℝ)]; exact (Nat.sub_one_lt_floor _).le)
      (Real.log_nonneg (hpos p hp))

  have htheta : ∑ p ∈ P, Real.log p ≤ Real.log 4 * N := by
    have h := Chebyshev.theta_le_log4_mul_x (x := (N : ℝ)) hNpos.le
    have hset : P = (Finset.Ioc 0 ⌊(N : ℝ)⌋₊).filter Nat.Prime := by
      rw [Nat.floor_natCast, hP]
      ext p
      simp only [Finset.mem_filter, Finset.mem_Iic, Finset.mem_Ioc]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨⟨h2.pos, h1⟩, h2⟩
      · rintro ⟨⟨-, h1⟩, h2⟩; exact ⟨h1, h2⟩
    rw [hset]; exact h
  have key : (N : ℝ) * ∑ p ∈ P, Real.log p / p - ∑ p ∈ P, Real.log p ≤ N * Real.log N := by
    calc (N : ℝ) * ∑ p ∈ P, Real.log p / p - ∑ p ∈ P, Real.log p
        = ∑ p ∈ P, ((N : ℝ) / p - 1) * Real.log p := by
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun p _ => ?_
          ring
      _ ≤ ∑ p ∈ P, ((N / p : ℕ) : ℝ) * Real.log p := Finset.sum_le_sum hfloor
      _ ≤ N * Real.log N := hlog
  have hS : ∑ p ∈ P, Real.log p / p ≤ Real.log N + Real.log 4 := by
    have : (N : ℝ) * ∑ p ∈ P, Real.log p / p ≤ N * (Real.log N + Real.log 4) := by
      rw [mul_add]; linarith
    exact le_of_mul_le_mul_left this hNpos
  have hlogNB : Real.log N ≤ Real.log B := Real.log_le_log hNpos hNB
  linarith

end GroundTheory.Heights₂.Heights.Model
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.PPrimeOpensCover
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open AlgebraicGeometry TopologicalSpace

namespace PrimeOpensCover

lemma not_mem_of_isCoprime {P : Ideal ℤ} (hP : P ≠ ⊤) {a b : ℤ} (h : IsCoprime a b)
    (ha : a ∈ P) : b ∉ P := by
  intro hb
  obtain ⟨u, v, huv⟩ := h
  exact hP ((Ideal.eq_top_iff_one P).mpr (huv ▸ P.add_mem (P.mul_mem_left u ha) (P.mul_mem_left v hb)))

lemma mem_of_dvd_mem {P : Ideal ℤ} {a b : ℤ} (h : a ∣ b) (ha : a ∈ P) : b ∈ P := by
  obtain ⟨c, rfl⟩ := h
  exact P.mul_mem_right c ha

lemma exists_mem_of_primeProd_mem {P : Ideal ℤ} [P.IsPrime] {S : Finset Nat.Primes}
    (h : primeProd S ∈ P) : ∃ r ∈ S, ((r : ℕ) : ℤ) ∈ P :=
  Ideal.IsPrime.prod_mem_iff.mp h

theorem proof : PrimeOpensCover.Statement := by
  intro X f S mp hcop hdvd
  refine ⟨?_, fun p hp q hq hpq => ?_⟩
  · refine top_le_iff.mp fun x _ => ?_
    let P : Ideal ℤ := (f.base x).asIdeal
    have : P.IsPrime := (f.base x).isPrime
    rw [Opens.mem_sup]
    by_cases hm : primeProd S ∈ P
    · obtain ⟨r, hr, hrP⟩ := exists_mem_of_primeProd_mem hm
      right
      rw [Opens.mem_iSup]
      refine ⟨r, ?_⟩
      rw [Opens.mem_iSup]
      refine ⟨hr, ?_⟩
      rw [mem_invOpen]
      exact not_mem_of_isCoprime (Ideal.IsPrime.ne_top ‹_›)
        ((Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp r.2)).mpr (hcop r hr)) hrP
    · left
      exact hm
  · have hm : ∀ x : X, x ∈ invOpen f (mp p) ⊓ invOpen f (mp q) → x ∈ invOpen f (primeProd S) := by
      intro x hx
      obtain ⟨hxp, hxq⟩ := hx
      replace hxp : mp p ∉ (f.base x).asIdeal := hxp
      replace hxq : mp q ∉ (f.base x).asIdeal := hxq
      rw [mem_invOpen]
      let P : Ideal ℤ := (f.base x).asIdeal
      have : P.IsPrime := (f.base x).isPrime
      intro hmem
      obtain ⟨r, hr, hrP⟩ := exists_mem_of_primeProd_mem (P := P) hmem
      by_cases hrp : r = p
      · subst hrp
        exact hxq (mem_of_dvd_mem (hdvd q hq r hr hpq) hrP)
      · exact hxp (mem_of_dvd_mem (hdvd p hp r hr hrp) hrP)
    refine ⟨fun x hx => hm x hx, fun x hx => ?_⟩
    have h1 := hm x hx
    obtain ⟨hxp, _⟩ := hx
    replace hxp : mp p ∉ (f.base x).asIdeal := hxp
    rw [mem_invOpen] at h1 ⊢
    have : (f.base x).asIdeal.IsPrime := (f.base x).isPrime
    intro hmul
    rcases Ideal.IsPrime.mem_or_mem ‹_› hmul with h | h
    · exact h1 h
    · exact hxp h

end PrimeOpensCover

end GroundTheory.Heights₂.Heights.Model
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.PSumCp
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

theorem primeWeight_nonneg {p : ℕ} (hp : p.Prime) : 0 ≤ primeWeight p := by
  unfold primeWeight
  split_ifs
  · norm_num
  · have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    exact div_nonneg zero_le_one (by linarith)

theorem primeWeight_le {p : ℕ} (hp : p.Prime) : primeWeight p ≤ 4 / p := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  unfold primeWeight
  split_ifs with h
  · subst h; norm_num
  · rw [div_le_div_iff₀ (by linarith) (by linarith)]
    linarith

theorem SumCp.proof (hM : MertensUpper.Statement) : SumCp.Statement := by
  obtain ⟨CM, hCM⟩ := hM
  intro d hd
  set T := d.natAbs.primeFactors with hT
  set K1 : ℝ := ∑ p ∈ T, primeWeight p * Real.log p
  set K2 : ℝ := ∑ p ∈ T, 2 * (padicValInt p d : ℝ) * Real.log p
  set A : ℝ := |4 * CM + K1 + K2|
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨4 + A / Real.log 2, fun B hB S hS => ?_⟩
  set P := (Finset.Iic ⌊B⌋₊).filter Nat.Prime
  have hlogB : Real.log 2 ≤ Real.log B := Real.log_le_log (by norm_num) hB
  have hlog : ∀ p : ℕ, p.Prime → 0 ≤ Real.log p := fun p hp =>
    Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  have hTprime : ∀ p ∈ T, p.Prime := fun p hp => (Nat.mem_primeFactors.mp hp).1
  have hPprime : ∀ p ∈ P, p.Prime := fun p hp => (Finset.mem_filter.mp hp).2
  have hSsub : S ⊆ P ∪ T := by
    intro p hp
    obtain ⟨hpp, hpB | hpd⟩ := hS p hp
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
        ⟨Finset.mem_Iic.mpr (Nat.le_floor hpB), hpp⟩)
    · exact Finset.mem_union_right _ (Nat.mem_primeFactors.mpr
        ⟨hpp, Int.natCast_dvd.mp hpd, Int.natAbs_ne_zero.mpr hd⟩)

  have hW : ∑ p ∈ S, primeWeight p * Real.log p ≤ 4 * (Real.log B + CM) + K1 := by
    have hnn : ∀ p ∈ P ∪ T, 0 ≤ primeWeight p * Real.log p := by
      intro p hp
      have hpp : p.Prime := (Finset.mem_union.mp hp).elim (hPprime p) (hTprime p)
      exact mul_nonneg (primeWeight_nonneg hpp) (hlog p hpp)
    calc ∑ p ∈ S, primeWeight p * Real.log p
        ≤ ∑ p ∈ P ∪ T, primeWeight p * Real.log p :=
          Finset.sum_le_sum_of_subset_of_nonneg hSsub (fun p hp _ => hnn p hp)
      _ ≤ ∑ p ∈ P, primeWeight p * Real.log p + K1 := by
          rw [← Finset.sum_union_inter]
          have : 0 ≤ ∑ p ∈ P ∩ T, primeWeight p * Real.log p :=
            Finset.sum_nonneg fun p hp => hnn p (Finset.mem_union_left _ (Finset.mem_inter.mp hp).1)
          linarith
      _ ≤ ∑ p ∈ P, 4 * (Real.log p / p) + K1 := by
          have hsum : ∑ p ∈ P, primeWeight p * Real.log p ≤ ∑ p ∈ P, 4 * (Real.log p / p) := by
            refine Finset.sum_le_sum fun p hp => ?_
            have hpp := hPprime p hp
            have hw := mul_le_mul_of_nonneg_right (primeWeight_le hpp) (hlog p hpp)
            calc primeWeight p * Real.log p ≤ 4 / p * Real.log p := hw
              _ = 4 * (Real.log p / p) := by ring
          linarith
      _ ≤ 4 * (Real.log B + CM) + K1 := by
          rw [← Finset.mul_sum]
          linarith [hCM B hB]

  have hV : ∑ p ∈ S, 2 * (padicValInt p d : ℝ) * Real.log p ≤ K2 := by
    rw [← Finset.sum_filter_of_ne (p := fun p => p ∈ T)]
    · apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp; exact (Finset.mem_filter.mp hp).2
      · intro p hp _
        exact mul_nonneg (by positivity) (hlog p (hTprime p hp))
    · intro p hp hne
      by_contra hpT
      apply hne
      have hpp := (hS p hp).1
      have hnd : ¬ (p : ℤ) ∣ d := fun hpd => hpT (Nat.mem_primeFactors.mpr
        ⟨hpp, Int.natCast_dvd.mp hpd, Int.natAbs_ne_zero.mpr hd⟩)
      rw [padicValInt.eq_zero_of_not_dvd hnd]
      simp
  have hsplit : ∑ p ∈ S, (primeWeight p + 2 * padicValInt p d) * Real.log p
      = ∑ p ∈ S, primeWeight p * Real.log p + ∑ p ∈ S, 2 * (padicValInt p d : ℝ) * Real.log p := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ => by ring
  have hA : 4 * CM + K1 + K2 ≤ A := le_abs_self _
  have hA0 : 0 ≤ A := abs_nonneg _
  have habs : A ≤ A / Real.log 2 * Real.log B := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
    exact mul_le_mul_of_nonneg_left hlogB hA0
  rw [hsplit]
  nlinarith [hW, hV, hA, habs]

end GroundTheory.Heights₂.Heights.Model
end

