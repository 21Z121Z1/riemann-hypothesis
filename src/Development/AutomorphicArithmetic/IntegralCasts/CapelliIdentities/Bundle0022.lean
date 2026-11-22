import Mathlib

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsUniqueNormed
section
noncomputable def UpperTheory.Reformulated.B.Yzb8.SelfDual :
    {V : Type} →
      [AddCommGroup V] → [TopologicalSpace V] → [inst : MeasurableSpace V] → MeasureTheory.Measure V → (V → V → ℂ) → Prop :=
    fun {V : Type} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] (μ : MeasureTheory.Measure V) (χ : V → V → ℂ) ↦
      μ.IsAddHaarMeasure ∧
        ∀ (Φ : V → ℂ),
          Continuous Φ →
            HasCompactSupport Φ →
              MeasureTheory.Integrable (fun (y : V) ↦ ∫ (x : V), Φ x * χ x y ∂μ) μ →
                ∀ (z : V), ∫ (y : V), (∫ (x : V), Φ x * χ x y ∂μ) * χ y z ∂μ = Φ (-z)

namespace UpperTheory.Reformulated.B.Yzb8

open MeasureTheory FourierTransform
open scoped NNReal ENNReal

section aux

variable {V E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

private noncomputable def ee (t : ℝ) : ℂ :=
  Complex.exp ((2 : ℂ) * (↑Real.pi : ℂ) * Complex.I * (↑t : ℂ))

private lemma integral_mul_ee (f : E → ℂ) (w : E) :
    ∫ u, f u * ee (inner ℝ u w) = 𝓕 f (-w) := by
  rw [Real.fourier_eq']
  refine integral_congr_ae (.of_forall fun u => ?_)
  simp only [ee, inner_neg_right, smul_eq_mul]
  rw [mul_comm]
  congr 2
  push_cast
  ring

private lemma integral_mul_ee' (f : E → ℂ) (w : E) :
    ∫ u, f u * ee (inner ℝ u w) = 𝓕⁻ f w := by
  rw [Real.fourierInv_eq']
  refine integral_congr_ae (.of_forall fun u => ?_)
  simp only [ee, smul_eq_mul]
  rw [mul_comm]
  congr 2
  push_cast
  ring

private lemma emb (T : V ≃L[ℝ] E) : MeasurableEmbedding (T.symm : E → V) :=
  T.symm.toHomeomorph.measurableEmbedding

private lemma inner_eq (T S : V ≃L[ℝ] E) (b : V → V → ℝ)
    (hb : ∀ x y, b x y = inner ℝ (T x) (S y)) (Φ : V → ℂ) (y : V) :
    ∫ x, Φ x * ee (b x y) ∂(Measure.map (T.symm : E → V) volume) =
      𝓕 (fun u => Φ (T.symm u)) (-(S y)) := by
  rw [(emb T).integral_map, ← integral_mul_ee]
  refine integral_congr_ae (.of_forall fun u => ?_)
  simp [hb]

private lemma outer_eq (T S : V ≃L[ℝ] E) (b : V → V → ℝ)
    (hb : ∀ x y, b x y = inner ℝ (T x) (S y)) (hs : ∀ x y, b x y = b y x)
    (H : E → ℂ) (z : V) :
    ∫ y, H (-(S y)) * ee (b y z) ∂(Measure.map (S.symm : E → V) volume) =
      𝓕⁻ H (-(T z)) := by
  rw [(emb S).integral_map, ← integral_mul_ee',
    ← integral_neg_eq_self (fun u => H u * ee (inner ℝ u (-(T z))))]
  refine integral_congr_ae (.of_forall fun u => ?_)
  simp [hs _ z, hb, real_inner_comm]

private lemma main (T S : V ≃L[ℝ] E) (b : V → V → ℝ)
    (hb : ∀ x y, b x y = inner ℝ (T x) (S y)) (hs : ∀ x y, b x y = b y x)
    (k a : ℝ≥0) (hk0 : k ≠ 0) (ha : a ≠ 0)
    (hk : Measure.map (S.symm : E → V) volume = k • Measure.map (T.symm : E → V) volume)
    (Φ : V → ℂ) (hc : Continuous Φ) (hcs : HasCompactSupport Φ) :
    (Integrable (fun y => ∫ x, Φ x * ee (b x y) ∂(a • Measure.map (T.symm : E → V) volume))
        (a • Measure.map (T.symm : E → V) volume) ↔
      Integrable (𝓕 (fun u => Φ (T.symm u))) volume) ∧
    (Integrable (𝓕 (fun u => Φ (T.symm u))) volume → ∀ z,
      ∫ y, (∫ x, Φ x * ee (b x y) ∂(a • Measure.map (T.symm : E → V) volume)) * ee (b y z)
        ∂(a • Measure.map (T.symm : E → V) volume) = ((a ^ 2 / k : ℝ≥0) : ℂ) * Φ (-z)) := by
  set G : E → ℂ := fun u => Φ (T.symm u) with hG
  have h1 : ∀ y, ∫ x, Φ x * ee (b x y) ∂(a • Measure.map (T.symm : E → V) volume) =
      (a : ℂ) * 𝓕 G (-(S y)) := by
    intro y
    rw [integral_smul_nnreal_measure, inner_eq T S b hb, NNReal.smul_def, Complex.real_smul]
  have hμ : a • Measure.map (T.symm : E → V) volume =
      (a / k) • Measure.map (S.symm : E → V) volume := by
    rw [hk, smul_smul, div_mul_cancel₀ _ hk0]
  have hak : ((a / k : ℝ≥0) : ℝ≥0∞) ≠ 0 := by
    simpa using div_ne_zero ha hk0
  simp only [h1]
  rw [hμ]
  refine ⟨?_, ?_⟩
  · have : Integrable (fun y => (a : ℂ) * 𝓕 G (-(S y))) ((a / k) • Measure.map (S.symm : E → V) volume) ↔
        Integrable (fun y => (a : ℂ) * 𝓕 G (-(S y))) (Measure.map (S.symm : E → V) volume) :=
      integrable_smul_measure hak ENNReal.coe_ne_top
    rw [this, (emb S).integrable_map_iff]
    have ha' : IsUnit (a : ℂ) := by simpa using ha
    have e1 : ((fun y => (a : ℂ) * 𝓕 G (-(S y))) ∘ (S.symm : E → V)) =
        fun w => (a : ℂ) * (fun w => 𝓕 G (-w)) w := by
      funext w; simp
    rw [e1, integrable_const_mul_iff ha']
    exact ⟨fun h => by simpa using h.comp_neg, fun h => h.comp_neg⟩
  · intro hint z
    have e2 : ∀ y, (a : ℂ) * 𝓕 G (-(S y)) * ee (b y z) = (a : ℂ) * (𝓕 G (-(S y)) * ee (b y z)) :=
      fun y => mul_assoc _ _ _
    simp only [e2]
    have hGc : Continuous G := hc.comp T.symm.continuous
    have hGs : HasCompactSupport G := hcs.comp_homeomorph T.symm.toHomeomorph
    have hinv : 𝓕⁻ (𝓕 G) = G :=
      hGc.fourierInv_fourier_eq (hGc.integrable_of_hasCompactSupport hGs) hint
    rw [integral_smul_nnreal_measure, integral_const_mul, outer_eq T S b hb hs,
      hinv, NNReal.smul_def, Complex.real_smul]
    have e3 : G (-(T z)) = Φ (-z) := by simp [hG]
    rw [e3]
    push_cast
    field_simp

private lemma exists_bump : ∃ G : E → ℂ, Continuous G ∧ HasCompactSupport G ∧ G 0 ≠ 0 ∧
    Integrable (𝓕 G) volume := by
  let f : ContDiffBump (0 : E) := default
  have hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => ((f x : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp f.contDiff
  have hcs : HasCompactSupport (fun x => ((f x : ℝ) : ℂ)) :=
    f.hasCompactSupport.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
  refine ⟨fun x => ((f x : ℝ) : ℂ), hd.continuous, hcs, ?_, ?_⟩
  · have h1 : f 0 = 1 := f.one_of_mem_closedBall (by simp [f.rIn_pos.le])
    simp [h1]
  · exact (𝓕 (hcs.toSchwartzMap hd)).integrable

end aux

end UpperTheory.Reformulated.B.Yzb8

open MeasureTheory FourierTransform UpperTheory.Reformulated.B.Yzb8
open scoped NNReal ENNReal
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExtendPt
section
theorem UpperTheory.Reformulated.B.Qi4.extendPt :
    ∀ (O Λ T K : Type) [inst : CommRing O] [inst_1 : CommRing Λ] [inst_2 : CommRing T]
    [inst_3 : Field K] [IsAlgClosed K] [inst_5 : Algebra O Λ] [inst_6 : Algebra O T] [inst_7 : Algebra Λ T]
    [IsScalarTower O Λ T] [inst_9 : Algebra O K] [Algebra.IsIntegral Λ T] (P : Ideal T) (y : Λ →ₐ[O] K),
    Ideal.comap (Algebra.algebraMap Λ T) P ≤ RingHom.ker y →
      ∃ (x : T →ₐ[O] K),
        P ≤ RingHom.ker x ∧ ∀ (a : Λ), (x : T → K) ((Algebra.algebraMap Λ T : Λ → T) a) = (y : Λ → K) a := by
  intro O Λ T K _ _ _ _ _ _ _ _ _ _ _ P y hP
  haveI hprime : (RingHom.ker y).IsPrime := RingHom.ker_isPrime y
  obtain ⟨Q, hPQ, hQ, hQc⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral (RingHom.ker y) P hP
  have hker : ∀ a ∈ Q.comap (algebraMap Λ T), (y : Λ →+* K) a = 0 := by
    intro a ha
    rw [hQc] at ha
    exact ha
  let ybar : (Λ ⧸ Q.comap (algebraMap Λ T)) →+* K := Ideal.Quotient.lift _ (y : Λ →+* K) hker
  have hinj : Function.Injective ybar := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [Ideal.Quotient.eq_zero_iff_mem, hQc]
    exact ha
  letI : Algebra (Λ ⧸ Q.comap (algebraMap Λ T)) K := ybar.toAlgebra
  haveI : FaithfulSMul (Λ ⧸ Q.comap (algebraMap Λ T)) K :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  haveI : FaithfulSMul (Λ ⧸ Q.comap (algebraMap Λ T)) (T ⧸ Q) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 Ideal.algebraMap_quotient_injective
  haveI : Module.IsTorsionFree (Λ ⧸ Q.comap (algebraMap Λ T)) (T ⧸ Q) :=
    FaithfulSMul.to_isTorsionFree _ _
  haveI : Module.IsTorsionFree (Λ ⧸ Q.comap (algebraMap Λ T)) K :=
    FaithfulSMul.to_isTorsionFree _ _
  haveI hint : Algebra.IsIntegral (Λ ⧸ Q.comap (algebraMap Λ T)) (T ⧸ Q) :=
    Algebra.IsIntegral.quotient
  haveI : Algebra.IsAlgebraic (Λ ⧸ Q.comap (algebraMap Λ T)) (T ⧸ Q) :=
    Algebra.IsIntegral.isAlgebraic
  let z : (T ⧸ Q) →ₐ[Λ ⧸ Q.comap (algebraMap Λ T)] K := IsAlgClosed.lift
  have hz : ∀ a : Λ, z (Ideal.Quotient.mk Q (algebraMap Λ T a)) = y a := fun a =>
    z.commutes (Ideal.Quotient.mk _ a)
  refine ⟨{ (z : (T ⧸ Q) →+* K).comp (Ideal.Quotient.mk Q) with commutes' := fun o => ?_ }, ?_, hz⟩
  · have h := hz (algebraMap O Λ o)
    rw [← IsScalarTower.algebraMap_apply, y.commutes] at h
    exact h
  · intro t ht
    have h0 : Ideal.Quotient.mk Q t = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (hPQ ht)
    show z (Ideal.Quotient.mk Q t) = 0
    rw [h0, map_zero]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FGe
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qk42.M4 :
    Type → Type :=
    fun (R : Type) ↦ Matrix (Fin (4 : ℕ)) (Fin (4 : ℕ)) R

noncomputable def UpperTheory.Reformulated.B.Qk42.FGe :
    {R : Type} → [CommRing R] → (Fin (4 : ℕ) → ℤ) → ℤ → UpperTheory.Reformulated.B.Qk42.M4 R → Prop :=
    fun {R : Type} [CommRing R] (m : Fin (4 : ℕ) → ℤ) (p : ℤ) (X : UpperTheory.Reformulated.B.Qk42.M4 R) ↦
      ∀ (i j : Fin (4 : ℕ)), m i - m j < p → X i j = (0 : R)

theorem UpperTheory.Reformulated.B.Qk42.mul :
    ∀ {R : Type} [inst : CommRing R] {m : Fin (4 : ℕ) → ℤ} {p q : ℤ} {A B : UpperTheory.Reformulated.B.Qk42.M4 R},
      UpperTheory.Reformulated.B.Qk42.FGe m p A → UpperTheory.Reformulated.B.Qk42.FGe m q B → UpperTheory.Reformulated.B.Qk42.FGe m (p + q) (A * B) := by
  intro R _ m p q A B hA hB i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : m i - m k < p
  · rw [hA i k hk, zero_mul]
  · rw [hB k j (by omega), mul_zero]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FInt
section
namespace YhaHelp
open MeasureTheory Set Real

private lemma F_int {c : ℝ} (hc : 0 < c) :
    Integrable ((Ici (0:ℝ)).indicator (fun x : ℝ => exp (-c * x))) := by
  rw [integrable_indicator_iff measurableSet_Ici]
  exact (exp_neg_integrableOn_Ioi (-1) hc).mono_set (fun x hx => by
    simp only [mem_Ici, mem_Ioi] at *; linarith)

end YhaHelp

theorem UpperTheory.Reformulated.B.Yha4.main :
    ∀ {c : ℝ}, (0 : ℝ) < c → MeasureTheory.Integrable (fun (x : ℝ) ↦ Real.exp (-c * |x|)) MeasureTheory.MeasureSpace.volume := by
  intro c hc
  have hF := YhaHelp.F_int hc
  have hG := hF.comp_neg
  refine (hF.add hG).mono' (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  simp only [Pi.add_apply, Set.indicator, Set.mem_Ici, Left.nonneg_neg_iff]
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h, if_pos h]
    split_ifs
    · linarith [Real.exp_pos (-c * -x)]
    · simp
  · rw [abs_of_neg h, if_neg (not_le.mpr h), if_pos h.le]
    simp
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FactorConjugationCancel
section
open MeasureTheory

private theorem UpperTheory.Reformulated.B.FactorConjugationCancel.smul_cancel {G : Type} [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [LocallyCompactSpace G] [MeasurableSpace G]
    [BorelSpace G] (ν : Measure G) [ν.IsAddHaarMeasure] {a b : NNReal}
    (h : a • ν = b • ν) : a = b := by
  obtain ⟨K, hK, hK0⟩ := exists_compact_mem_nhds (0 : G)
  have h0 : ν K ≠ 0 := (Measure.measure_pos_of_mem_nhds ν hK0).ne'
  have h1 : ν K ≠ ⊤ := hK.measure_lt_top.ne
  have h2 : (a : ENNReal) * ν K = (b : ENNReal) * ν K := by
    have := congrArg (fun μ : Measure G => μ K) h
    simpa using this
  exact_mod_cast (ENNReal.mul_left_inj h0 h1).1 h2

private theorem UpperTheory.Reformulated.B.FactorConjugationCancel.exists_factor {G : Type} [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (m : G ≃ₜ+ G) (ν : Measure G) [ν.IsAddHaarMeasure] :
    ∃ a : NNReal, Measure.map (⇑m : G → G) ν = a • ν := by
  haveI : (Measure.map (⇑m : G → G) ν).IsAddHaarMeasure := m.isAddHaarMeasure_map ν
  exact ⟨_, Measure.isAddLeftInvariant_eq_smul _ ν⟩

theorem UpperTheory.Reformulated.B.FactorConjugationCancel.map_eq_of_conj :
    ∀ {G : Type} [inst : AddCommGroup G] [inst_1 : TopologicalSpace G]
    [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [inst_5 : MeasurableSpace G]
    [BorelSpace G] (m s : G ≃ₜ+ G) (ν : MeasureTheory.Measure G) [ν.IsAddHaarMeasure] (c : NNReal),
    (∀ (x : G), (s : G → G) ((s : G → G) x) = x) →
      MeasureTheory.Measure.map (fun (x : G) ↦ (s : G → G) ((m : G → G) ((s : G → G) ((m : G → G) x)))) ν = (c * c) • ν →
        MeasureTheory.Measure.map (⇑m : G → G) ν = c • ν := by
  intro G _ _ _ _ _ _ _ m s ν _ c hs h
  obtain ⟨a, ha⟩ := UpperTheory.Reformulated.B.FactorConjugationCancel.exists_factor m ν
  obtain ⟨b, hb⟩ := UpperTheory.Reformulated.B.FactorConjugationCancel.exists_factor s ν
  have mm : Measurable (⇑m : G → G) := m.continuous.measurable
  have ms : Measurable (⇑s : G → G) := s.continuous.measurable
  have hm' : ∀ r : NNReal, Measure.map (⇑m : G → G) (r • ν) = (r * a) • ν := by
    intro r
    rw [Measure.map_smul, ha, smul_smul]
  have hs' : ∀ r : NNReal, Measure.map (⇑s : G → G) (r • ν) = (r * b) • ν := by
    intro r
    rw [Measure.map_smul, hb, smul_smul]
  have hbb : b * b = 1 := by
    apply UpperTheory.Reformulated.B.FactorConjugationCancel.smul_cancel ν
    rw [← hs', ← hb, Measure.map_map ms ms, one_smul]
    have : (⇑s ∘ ⇑s : G → G) = id := funext hs
    rw [this, Measure.map_id]
  have hcomp : (fun (x : G) ↦ (s : G → G) ((m : G → G) ((s : G → G) ((m : G → G) x))))
      = (⇑s : G → G) ∘ ((⇑m : G → G) ∘ ((⇑s : G → G) ∘ (⇑m : G → G))) := rfl
  rw [hcomp, ← Measure.map_map ms (mm.comp (ms.comp mm)), ← Measure.map_map mm (ms.comp mm),
    ← Measure.map_map ms mm, ha, hs', hm', hs'] at h
  have h2 := UpperTheory.Reformulated.B.FactorConjugationCancel.smul_cancel ν h
  have h3 : a * a = c * c := by
    rw [← h2]
    calc a * a = a * a * (b * b) := by rw [hbb, mul_one]
      _ = _ := by ring
  have h5 : (a : ℝ) * a = (c : ℝ) * c := by rw [← NNReal.coe_mul, ← NNReal.coe_mul, h3]
  have h4 : a = c := NNReal.eq ((mul_self_inj_of_nonneg a.coe_nonneg c.coe_nonneg).1 h5)
  rw [ha, h4]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FactorialTendstoZero
section
open Filter Topology NumberField IsDedekindDomain

private lemma UpperTheory.Reformulated.B.AdelicCharacterNormOne.factorial_tendsto_zero {K : Type*} [NormedField K]
    (h1 : ∀ n : ℕ, ‖(n : K)‖ ≤ 1) (N : ℕ) (hN : 0 < N) (hlt : ‖(N : K)‖ < 1) :
    Tendsto (fun n : ℕ => ((n.factorial : ℕ) : K)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun n => ha.trans_le (norm_nonneg _),
    fun a ha => ?_⟩
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one ha hlt
  filter_upwards [eventually_ge_atTop (N ^ k)] with n hn
  obtain ⟨m, hm⟩ := Nat.dvd_factorial (pow_pos hN k) hn
  rw [hm, Nat.cast_mul, Nat.cast_pow, norm_mul, norm_pow]
  exact (mul_le_of_le_one_right (by positivity) (h1 m)).trans_lt hk

private lemma UpperTheory.Reformulated.B.AdelicCharacterNormOne.local_tendsto {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) :
    Tendsto (fun n : ℕ => ((n.factorial : ℕ) : v.adicCompletion F)) atTop (𝓝 0) := by
  refine UpperTheory.Reformulated.B.AdelicCharacterNormOne.factorial_tendsto_zero (K := v.adicCompletion F) (fun n => ?_)
    (Ideal.absNorm v.asIdeal) (zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v)) ?_
  · have := FinitePlace.norm_le_one F v (n : 𝓞 F)
    rwa [map_natCast, map_natCast] at this
  · have := (FinitePlace.norm_lt_one_iff_mem F v _).2 (Ideal.absNorm_mem v.asIdeal)
    rwa [map_natCast, map_natCast] at this

private lemma UpperTheory.Reformulated.B.AdelicCharacterNormOne.finite_tendsto {F : Type} [Field F] [NumberField F] :
    Tendsto (fun n : ℕ => ((n.factorial : ℕ) : FiniteAdeleRing (𝓞 F) F)) atTop (𝓝 0) := by
  have h : Tendsto (fun (n : ℕ) (v : HeightOneSpectrum (𝓞 F)) =>
      ((n.factorial : ℕ) : v.adicCompletionIntegers F)) atTop (𝓝 0) := by
    rw [tendsto_pi_nhds]
    intro v
    rw [tendsto_subtype_rng]
    simpa using UpperTheory.Reformulated.B.AdelicCharacterNormOne.local_tendsto v
  have hc := (RestrictedProduct.isEmbedding_structureMap
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (𝓕 := cofinite)).continuous
  exact (hc.tendsto _).comp h

private lemma UpperTheory.Reformulated.B.AdelicCharacterNormOne.eq_one_of_tendsto {r : ℝ} (hr : 0 ≤ r)
    (h : Tendsto (fun n : ℕ => r ^ n.factorial) atTop (𝓝 1)) : r = 1 := by
  have hf : Tendsto Nat.factorial atTop atTop :=
    tendsto_atTop_mono Nat.self_le_factorial tendsto_id
  rcases lt_trichotomy r 1 with hlt | heq | hgt
  · exact absurd (tendsto_nhds_unique ((tendsto_pow_atTop_nhds_zero_of_lt_one hr hlt).comp hf) h)
      zero_ne_one
  · exact heq
  · exact absurd h (not_tendsto_nhds_of_tendsto_atTop
      ((tendsto_pow_atTop_atTop_of_one_lt hgt).comp hf) 1)

theorem UpperTheory.Reformulated.B.AdelicCharacterNormOne.norm_eq_one :
    ∀ {F : Type} [inst : Field F] [inst_1 : NumberField F]
    (ψ : AddChar (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) ℂ),
    Continuous (⇑ψ : NumberField.AdeleRing (NumberField.RingOfIntegers F) F → ℂ) →
      (∀ (a : F),
          (ψ : NumberField.AdeleRing (NumberField.RingOfIntegers F) F → ℂ)
              ((Algebra.algebraMap F (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) :
                  F → NumberField.AdeleRing (NumberField.RingOfIntegers F) F)
                a) =
            (1 : ℂ)) →
        ∀ (x : NumberField.AdeleRing (NumberField.RingOfIntegers F) F),
          ‖(ψ : NumberField.AdeleRing (NumberField.RingOfIntegers F) F → ℂ) x‖ = (1 : ℝ) := by
  intro F _ _ ψ hψ htriv
  let i : InfiniteAdeleRing F → AdeleRing (𝓞 F) F := fun x => (x, 0)
  let j : FiniteAdeleRing (𝓞 F) F → AdeleRing (𝓞 F) F := fun y => (0, y)
  have hi : Continuous i := continuous_id.prodMk continuous_const
  have hj : Continuous j := continuous_const.prodMk continuous_id
  have hsplit : ∀ x : AdeleRing (𝓞 F) F, x = i x.1 + j x.2 := fun x =>
    Prod.ext (add_zero x.1).symm (zero_add x.2).symm
  have hfin : ∀ y, ‖ψ (j y)‖ = 1 := by
    intro y
    apply UpperTheory.Reformulated.B.AdelicCharacterNormOne.eq_one_of_tendsto (norm_nonneg _)
    have h1 := (UpperTheory.Reformulated.B.AdelicCharacterNormOne.finite_tendsto (F := F)).mul_const y
    rw [zero_mul] at h1
    have h2 := (((hψ.comp hj).norm).tendsto 0).comp h1
    have h0 : j 0 = 0 := rfl
    have hs : ∀ n : ℕ, j ((n : FiniteAdeleRing (𝓞 F) F) * y) = n • j y := fun n =>
      Prod.ext (nsmul_zero n).symm (nsmul_eq_mul n y).symm
    simp only [Function.comp_def, h0, hs, AddChar.map_zero_eq_one, norm_one,
      AddChar.map_nsmul_eq_pow, norm_pow] at h2
    exact h2
  have hinf : ∀ x, ‖ψ (i x)‖ = 1 := by
    intro x
    refine (InfiniteAdeleRing.denseRange_algebraMap F).induction_on x
      (isClosed_eq (hψ.comp hi).norm continuous_const) fun a => ?_
    have h := congrArg norm (htriv a)
    rw [hsplit (algebraMap F _ a), AddChar.map_add_eq_mul, norm_mul, hfin, mul_one, norm_one] at h
    exact h
  intro x
  rw [hsplit x, AddChar.map_add_eq_mul, norm_mul, hfin, hinf, mul_one]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FactorizationBis
section
theorem UpperTheory.Reformulated.B.TriangularFactorizationNearIdentity.factor :
    ∀ {L : Type} [inst : NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ) (r : ℝ),
      (0 : ℝ) ≤ r →
        r < (1 : ℝ) →
          ∀ (A : Matrix (Fin n) (Fin n) L),
            (∀ (i j : Fin n), ‖(A - (1 : Matrix (Fin n) (Fin n) L)) i j‖ ≤ r) →
              ∃ (U : Matrix (Fin n) (Fin n) L) (W : Matrix (Fin n) (Fin n) L),
                (∀ (i j : Fin n), j < i → U i j = (0 : L)) ∧
                  (∀ (i j : Fin n), i < j → W i j = (0 : L)) ∧
                    (∀ (i j : Fin n), ‖(U - (1 : Matrix (Fin n) (Fin n) L)) i j‖ ≤ r) ∧
                      (∀ (i j : Fin n), ‖(W - (1 : Matrix (Fin n) (Fin n) L)) i j‖ ≤ r) ∧ A = U * W := by
  intro L _ _ n r h0 h1
  induction n with
  | zero =>
    intro A _
    exact ⟨1, 1, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
      Subsingleton.elim _ _⟩
  | succ n ih =>
    intro A hA
    have hlc : ∀ i : Fin n, Fin.last n ≠ i.castSucc := fun i => (Fin.castSucc_lt_last i).ne'
    have hcl : ∀ i : Fin n, i.castSucc ≠ Fin.last n := fun i => (Fin.castSucc_lt_last i).ne
    have hd1 : ‖A (Fin.last n) (Fin.last n) - 1‖ ≤ r := by
      simpa using hA (Fin.last n) (Fin.last n)
    have hd : ‖A (Fin.last n) (Fin.last n)‖ = 1 := by
      have hne : ‖A (Fin.last n) (Fin.last n) - 1‖ ≠ ‖(1 : L)‖ := by
        rw [norm_one]; exact (hd1.trans_lt h1).ne
      have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne
      rw [sub_add_cancel, norm_one] at this
      rw [this]
      exact max_eq_right (hd1.trans h1.le)
    have hd0 : A (Fin.last n) (Fin.last n) ≠ 0 := by
      intro h; rw [h, norm_zero] at hd; exact zero_ne_one hd
    have hb : ∀ i : Fin n, ‖A i.castSucc (Fin.last n)‖ ≤ r := fun i => by
      simpa [Matrix.one_apply_ne (hcl i)] using hA i.castSucc (Fin.last n)
    have hc : ∀ i : Fin n, ‖A (Fin.last n) i.castSucc‖ ≤ r := fun i => by
      simpa [Matrix.one_apply_ne (hlc i)] using hA (Fin.last n) i.castSucc
    have hu : ∀ i : Fin n, ‖A i.castSucc (Fin.last n) / A (Fin.last n) (Fin.last n)‖ ≤ r :=
      fun i => by rw [norm_div, hd, div_one]; exact hb i
    have hone : ∀ i j : Fin n, (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) L) i.castSucc j.castSucc
        = (1 : Matrix (Fin n) (Fin n) L) i j := fun i j => by
      simp [Matrix.one_apply]
    obtain ⟨U, W, hU, hW, hU1, hW1, hUW⟩ := ih
      (Matrix.of fun i j : Fin n => A i.castSucc j.castSucc -
        A i.castSucc (Fin.last n) / A (Fin.last n) (Fin.last n) * A (Fin.last n) j.castSucc)
      (fun i j => by
        have h2 := hA i.castSucc j.castSucc
        rw [Matrix.sub_apply, hone] at h2
        rw [Matrix.sub_apply, Matrix.of_apply, sub_right_comm, sub_eq_add_neg]
        refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h2 ?_)
        rw [norm_neg, norm_mul]
        calc _ ≤ r * 1 := mul_le_mul (hu i) ((hc j).trans h1.le) (norm_nonneg _) h0
          _ = r := mul_one r)
    refine ⟨Matrix.of fun i j => Fin.lastCases (motive := fun _ => L)
        (Fin.lastCases (motive := fun _ => L) 1 (fun _ => 0) j)
        (fun i' => Fin.lastCases (motive := fun _ => L)
          (A i'.castSucc (Fin.last n) / A (Fin.last n) (Fin.last n)) (fun j' => U i' j') j) i,
      Matrix.of fun i j => Fin.lastCases (motive := fun _ => L)
        (A (Fin.last n) j)
        (fun i' => Fin.lastCases (motive := fun _ => L) 0 (fun j' => W i' j') j) i,
      ?_, ?_, ?_, ?_, ?_⟩
    · intro i j hij
      induction i using Fin.lastCases <;> induction j using Fin.lastCases
      · exact absurd hij (lt_irrefl _)
      · simp
      · exact absurd hij (Fin.le_last _).not_gt
      · simpa using hU _ _ (by simpa using hij)
    · intro i j hij
      induction i using Fin.lastCases <;> induction j using Fin.lastCases
      · exact absurd hij (lt_irrefl _)
      · exact absurd hij (Fin.le_last _).not_gt
      · simp
      · simpa using hW _ _ (by simpa using hij)
    · intro i j
      induction i using Fin.lastCases <;> induction j using Fin.lastCases
      · simpa using h0
      · simpa [Matrix.one_apply_ne (hlc _)] using h0
      · simpa [Matrix.one_apply_ne (hcl _), hd] using hb _
      · rw [Matrix.sub_apply, hone]
        simpa using hU1 _ _
    · intro i j
      induction i using Fin.lastCases <;> induction j using Fin.lastCases
      · simpa using hd1
      · simpa [Matrix.one_apply_ne (hlc _)] using hc _
      · simpa [Matrix.one_apply_ne (hcl _)] using h0
      · rw [Matrix.sub_apply, hone]
        simpa using hW1 _ _
    · ext i j
      rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
      induction i using Fin.lastCases <;> induction j using Fin.lastCases
      · simp
      · simp
      · simp [hd0]
      · rename_i i j
        have := congrFun (congrFun hUW i) j
        rw [Matrix.of_apply, Matrix.mul_apply] at this
        simp only [Matrix.of_apply, Fin.lastCases_castSucc, Fin.lastCases_last]
        rw [← this, sub_add_cancel]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FrobeniusElementAlt
section
noncomputable def UpperTheory.Reformulated.B.FrobeniusElementAlt.frb :
    {l : ℕ} → [Fact (Nat.Prime l)] → {B : Type} → [inst : CommRing B] → (↑l : B) = (0 : B) → B →+* B :=
  fun {l} hl {B} _ h =>
    { toFun := fun x => x ^ l
      map_one' := one_pow l
      map_mul' := fun x y => mul_pow x y l
      map_zero' := zero_pow hl.out.ne_zero
      map_add' := fun x y => by
        rw [add_pow_prime_eq hl.out x y, h]
        simp }
end

