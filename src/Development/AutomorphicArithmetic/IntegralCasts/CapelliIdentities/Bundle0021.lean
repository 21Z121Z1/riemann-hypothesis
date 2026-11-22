import Mathlib

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsSemi
section
theorem UpperTheory.Reformulated.B.Ra9.exists_semi :
    ∀ {A K : Type} [inst : CommRing A]
    [inst_1 : Field K] (M : Type) [inst_2 : AddCommGroup M] [inst_3 : _root_.Module A M] [inst_4 : Algebra A K]
    [Module.Free A M] {C W : Type} [inst_6 : Field C] [inst_7 : AddCommGroup W] [inst_8 : _root_.Module C W] (ι : K ≃+* C)
    (sp : M →+ W),
    (∀ (a : A) (m : M), (sp : M → W) (a • m) = (ι : K → C) ((Algebra.algebraMap A K : A → K) a) • (sp : M → W) m) →
      (∀ (κ : Type) (b : Module.Basis κ A M), LinearIndependent C fun (i : κ) ↦ (sp : M → W) ((b : κ → M) i)) →
        ∃ (Ψ : TensorProduct A K M →+ W),
          (∀ (k : K) (m : M), (Ψ : TensorProduct A K M → W) (k ⊗ₜ[A] m) = (ι : K → C) k • (sp : M → W) m) ∧
            (∀ (k : K) (v : TensorProduct A K M),
                (Ψ : TensorProduct A K M → W) (k • v) = (ι : K → C) k • (Ψ : TensorProduct A K M → W) v) ∧
              Function.Injective (⇑Ψ : TensorProduct A K M → W) ∧
                ∀ (w : W),
                  w ∈ Submodule.span C (Set.range (⇑sp : M → W)) ↔
                    ∃ (v : TensorProduct A K M), (Ψ : TensorProduct A K M → W) v = w := by
  intro A K _ _ M _ _ _ _ C W _ _ _ ι sp hsp hli
  classical
  let f : K →+ M →+ W :=
    { toFun := fun k =>
        { toFun := fun m => ι k • sp m
          map_zero' := by simp
          map_add' := by intro x y; simp [smul_add] }
      map_zero' := by ext m; simp
      map_add' := by intro x y; ext m; simp [add_smul] }
  have hfa : ∀ (k : K) (m : M), f k m = ι k • sp m := fun _ _ => rfl
  have hf : ∀ (r : A) (k : K) (m : M), f (r • k) m = f k (r • m) := by
    intro r k m
    have h := hsp r m
    rw [hfa, hfa, h, Algebra.smul_def, map_mul, mul_smul, smul_comm]
  let Ψ : TensorProduct A K M →+ W := TensorProduct.liftAddHom f hf
  have hΨ : ∀ (k : K) (m : M), Ψ (k ⊗ₜ[A] m) = ι k • sp m := fun k m => by
    simp only [Ψ, TensorProduct.liftAddHom_tmul, hfa]
  have hsemi : ∀ (k : K) (v : TensorProduct A K M), Ψ (k • v) = ι k • Ψ v := by
    intro k v
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul x m => rw [TensorProduct.smul_tmul', hΨ, hΨ, smul_eq_mul, map_mul, mul_smul]
    | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]
  refine ⟨Ψ, hΨ, hsemi, ?_, ?_⟩
  · refine (injective_iff_map_eq_zero Ψ).2 ?_
    intro v hv
    let b := Module.Free.chooseBasis A M
    let bK := Algebra.TensorProduct.basis K b
    have hsum : Ψ v = Finsupp.linearCombination C (fun i => sp (b i))
        ((bK.repr v).mapRange ι (map_zero ι)) := by
      rw [Finsupp.linearCombination_apply, Finsupp.sum_mapRange_index (by simp)]
      conv_lhs => rw [← bK.linearCombination_repr v]
      rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, Finsupp.sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [hsemi, Algebra.TensorProduct.basis_apply, hΨ, map_one, one_smul]
    have hl := (linearIndependent_iff.1 (hli _ b)) _ (hsum.symm.trans hv)
    have hr : bK.repr v = 0 := by
      ext i
      have h := DFunLike.congr_fun hl i
      simpa using h
    simpa using hr
  · intro w
    constructor
    · intro hw
      induction hw using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨m, rfl⟩ := hx
        exact ⟨1 ⊗ₜ[A] m, by rw [hΨ, map_one, one_smul]⟩
      | zero => exact ⟨0, map_zero Ψ⟩
      | add x y _ _ hx hy =>
        obtain ⟨a, rfl⟩ := hx
        obtain ⟨c, rfl⟩ := hy
        exact ⟨a + c, map_add Ψ a c⟩
      | smul c x _ hx =>
        obtain ⟨v, rfl⟩ := hx
        exact ⟨ι.symm c • v, by rw [hsemi, RingEquiv.apply_symm_apply]⟩
    · rintro ⟨v, rfl⟩
      induction v using TensorProduct.induction_on with
      | zero => simp
      | tmul k m =>
        rw [hΨ]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)
      | add x y hx hy =>
        rw [map_add]
        exact Submodule.add_mem _ hx hy
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsSmoothExtensionNear
section
theorem UpperTheory.exists_smooth_extension_near :
    ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
      {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {m : ℕ∞} {U : Set E},
      IsOpen U → ∀ {F : E → V}, ContDiffOn ℝ (m : WithTop ℕ∞) F U → ∀ {x : E}, x ∈ U →
        ∃ G : E → V, ContDiff ℝ (m : WithTop ℕ∞) G ∧ G =ᶠ[nhds x] F := by
  intro E _ _ _ V _ _ m U hU F hF x hx
  obtain ⟨ε, hε, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds hx)
  let b : ContDiffBump x := ⟨ε / 2, ε, half_pos hε, half_lt_self hε⟩
  have hsub : tsupport (b : E → ℝ) ⊆ U := by
    rw [b.tsupport_eq]
    exact hball
  refine ⟨fun y => b y • F y, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ U
    · exact (b.contDiff (n := m)).contDiffAt.smul (hF.contDiffAt (hU.mem_nhds hy))
    · have h0 : (b : E → ℝ) =ᶠ[nhds y] 0 :=
        notMem_tsupport_iff_eventuallyEq.1 fun h => hy (hsub h)
      have h1 : (fun z => b z • F z) =ᶠ[nhds y] fun _ => (0 : V) := by
        filter_upwards [h0] with z hz
        simp [hz]
      exact contDiffAt_const.congr_of_eventuallyEq h1
  · filter_upwards [b.eventuallyEq_one] with z hz
    simp [hz]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsSmulMemTer
section
theorem UpperTheory.Reformulated.B.ExistsSmulMemTer.exists_smul_mem :
    ∀ {K : Type} [inst : Field K] [NumberField K] {V : Type} [inst_2 : AddCommGroup V]
    [inst_3 : _root_.Module K V] [inst_4 : _root_.Module (NumberField.RingOfIntegers K) V]
    [IsScalarTower (NumberField.RingOfIntegers K) K V] (M : Submodule (NumberField.RingOfIntegers K) V),
    ∀ x ∈ Submodule.span K (↑M : Set V),
      ∃ (a : NumberField.RingOfIntegers K), a ≠ (0 : NumberField.RingOfIntegers K) ∧ a • x ∈ M := by
  intro K _ _ V _ _ _ _ M x hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hy⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact M.zero_mem⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine M.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact M.smul_mem b hay
    · rw [mul_smul]
      exact M.smul_mem a hbz
  | smul c y _ hy =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨⟨p, q⟩, hpq⟩ :=
      IsLocalization.surj (nonZeroDivisors (NumberField.RingOfIntegers K)) c
    refine ⟨a * (q : NumberField.RingOfIntegers K),
      mul_ne_zero ha (nonZeroDivisors.coe_ne_zero q), ?_⟩
    have h1 : (q : NumberField.RingOfIntegers K) • c • y = p • y := by
      rw [← algebraMap_smul K (q : NumberField.RingOfIntegers K), ← mul_smul, mul_comm]
      simp only at hpq
      rw [hpq, algebraMap_smul]
    rw [mul_smul, h1, ← mul_smul, mul_comm, mul_smul]
    exact M.smul_mem p hay
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsSpanModSq
section
theorem UpperTheory.Reformulated.B.Ra7.exists_span_mod_sq :
    ∀ {O R K : Type} [inst : CommRing O]
    [inst_1 : CommRing R] [inst_2 : Algebra O R] [IsNoetherianRing R] [inst_4 : CommRing K] [inst_5 : Algebra O K]
    (y : R →ₐ[O] K),
    Module.Finite O ↥y.range →
      ∃ (s : Finset R), ∀ (a : R), ∃ b ∈ Submodule.span O (↑s : Set R), a - b ∈ RingHom.ker y ^ (2 : ℕ) := by
  intro O R K _ _ _ _ _ _ y hfin
  classical
  obtain ⟨t', ht'⟩ := hfin.fg_top
  have hsurj : Function.Surjective y.rangeRestrict := y.rangeRestrict_surjective
  obtain ⟨σ, hσ⟩ := hsurj.hasRightInverse
  obtain ⟨g, hg⟩ : (RingHom.ker y).FG := IsNoetherian.noetherian _
  let t : Finset R := t'.image σ
  have h1 : ∀ a : R, ∃ b ∈ Submodule.span O (↑t : Set R), a - b ∈ RingHom.ker y := by
    intro a
    have hm : Submodule.map y.rangeRestrict.toLinearMap (Submodule.span O (↑t : Set R)) = ⊤ := by
      rw [Submodule.map_span, eq_top_iff, ← ht']
      apply Submodule.span_mono
      intro z hz
      exact ⟨σ z, Finset.mem_coe.2 (Finset.mem_image_of_mem σ hz), hσ z⟩
    have hz : y.rangeRestrict a ∈
        Submodule.map y.rangeRestrict.toLinearMap (Submodule.span O (↑t : Set R)) := by
      rw [hm]; exact Submodule.mem_top
    obtain ⟨b, hb, hab⟩ := hz
    refine ⟨b, hb, ?_⟩
    have hab' : y b = y a := congrArg Subtype.val hab
    rw [RingHom.mem_ker, map_sub, hab', sub_self]
  let s : Finset R := t ∪ Finset.image₂ (· * ·) t g
  have h2 : ∀ x ∈ g, ∀ b ∈ Submodule.span O (↑t : Set R),
      b * x ∈ Submodule.span O (↑s : Set R) := by
    intro x hx b hb
    induction hb using Submodule.span_induction with
    | mem z hz =>
      exact Submodule.subset_span (Finset.mem_coe.2
        (Finset.mem_union_right _ (Finset.mem_image₂_of_mem hz hx)))
    | zero => rw [zero_mul]; exact zero_mem _
    | add u v _ _ hu hv => rw [add_mul]; exact add_mem hu hv
    | smul c u _ hu => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hu
  have h3 : ∀ x ∈ Ideal.span (↑g : Set R), ∀ r : R,
      ∃ b ∈ Submodule.span O (↑s : Set R), r * x - b ∈ RingHom.ker y ^ (2 : ℕ) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem z hz =>
      intro r
      obtain ⟨b, hb, hrb⟩ := h1 r
      refine ⟨b * z, h2 z hz b hb, ?_⟩
      have hzI : z ∈ RingHom.ker y := by
        rw [← hg]; exact Ideal.subset_span hz
      rw [← sub_mul, pow_two]
      exact Ideal.mul_mem_mul hrb hzI
    | zero => intro r; exact ⟨0, zero_mem _, by rw [mul_zero, sub_zero]; exact zero_mem _⟩
    | add u v _ _ hu hv =>
      intro r
      obtain ⟨b, hb, hb'⟩ := hu r
      obtain ⟨c, hc, hc'⟩ := hv r
      refine ⟨b + c, add_mem hb hc, ?_⟩
      have e : r * (u + v) - (b + c) = (r * u - b) + (r * v - c) := by ring
      rw [e]; exact add_mem hb' hc'
    | smul c u _ hu =>
      intro r
      rw [smul_eq_mul, ← mul_assoc]
      exact hu (r * c)
  refine ⟨s, fun a => ?_⟩
  obtain ⟨b, hb, hab⟩ := h1 a
  obtain ⟨c, hc, hc'⟩ := h3 (a - b) (by rw [hg]; exact hab) 1
  refine ⟨b + c, add_mem (Submodule.span_mono ?_ hb) hc, ?_⟩
  · exact Finset.coe_subset.2 Finset.subset_union_left
  · have e : a - (b + c) = 1 * (a - b) - c := by ring
    rw [e]; exact hc'
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsSum
section
theorem UpperTheory.Reformulated.B.Qg3.exists_sum.{u_1} :
    ∀ {G : Type u_1} [inst : Group G]
    [inst_1 : TopologicalSpace G] [IsTopologicalGroup G] [inst_3 : MeasurableSpace G] [BorelSpace G]
    (μ : MeasureTheory.Measure G) [MeasureTheory.IsFiniteMeasureOnCompacts μ] (K : Subgroup G),
    IsOpen (↑K : Set G) →
      IsCompact (↑K : Set G) →
        ∀ {S : Set G},
          IsCompact S →
            ∃ (T : Finset (G ⧸ K)) (r : G ⧸ K → G) (c : G ⧸ K → ℂ),
              ∀ (F : G → ℂ),
                (∀ (g k : G), k ∈ K → F (g * k) = F g) →
                  (∀ g ∉ S, F g = (0 : ℂ)) → ∫ (g : G), F g ∂μ = ∑ x ∈ T, c x * F (r x) := by
  intro G _ _ _ _ _ μ _ K hKo hKc S hS
  classical
  haveI : DiscreteTopology (G ⧸ K) := QuotientGroup.discreteTopology hKo
  have hcont : Continuous (QuotientGroup.mk : G → G ⧸ K) := QuotientGroup.continuous_mk
  have hfin : ((QuotientGroup.mk : G → G ⧸ K) '' S).Finite :=
    (hS.image hcont).finite_of_discrete
  let C : G ⧸ K → Set G := fun x => (QuotientGroup.mk : G → G ⧸ K) ⁻¹' {x}
  have hmem : ∀ (x : G ⧸ K) (g : G), g ∈ C x ↔ (x.out)⁻¹ * g ∈ K := by
    intro x g
    rw [← QuotientGroup.eq, QuotientGroup.out_eq']
    exact eq_comm
  have hmeas : ∀ x, MeasurableSet (C x) := fun x =>
    ((isOpen_discrete {x}).preimage hcont).measurableSet
  have hcomp : ∀ x, IsCompact (C x) := by
    intro x
    have h : C x = (fun k => x.out * k) '' (K : Set G) := by
      ext g
      rw [hmem]
      constructor
      · intro h
        exact ⟨_, h, by simp⟩
      · rintro ⟨k, hk, rfl⟩
        simpa using hk
    rw [h]
    exact hKc.image (continuous_const.mul continuous_id)
  refine ⟨hfin.toFinset, fun x => x.out, fun x => (μ.real (C x) : ℂ), ?_⟩
  intro F hF h0
  have hout : ∀ g : G, F (QuotientGroup.mk g : G ⧸ K).out = F g := by
    intro g
    have h := hF (QuotientGroup.mk g : G ⧸ K).out _ ((hmem _ g).1 rfl)
    rw [mul_inv_cancel_left] at h
    exact h.symm
  have hdec : ∀ g, F g = ∑ x ∈ hfin.toFinset, (C x).indicator (fun _ => F x.out) g := by
    intro g
    rw [Finset.sum_eq_single (QuotientGroup.mk g : G ⧸ K)]
    · rw [Set.indicator_of_mem (show g ∈ C (QuotientGroup.mk g) from rfl), hout]
    · intro x _ hx
      have hg : g ∉ C x := fun h => hx (Eq.symm h)
      rw [Set.indicator_of_notMem hg]
    · intro hg
      rw [Set.indicator_of_mem (show g ∈ C (QuotientGroup.mk g) from rfl), hout]
      exact h0 g fun hgS => hg (hfin.mem_toFinset.2 ⟨g, hgS, rfl⟩)
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hdec),
    MeasureTheory.integral_finset_sum]
  · refine Finset.sum_congr rfl fun x _ => ?_
    rw [MeasureTheory.integral_indicator_const _ (hmeas x), Complex.real_smul]
  · intro x _
    rw [MeasureTheory.integrable_indicator_iff (hmeas x)]
    exact MeasureTheory.integrableOn_const (hcomp x).measure_lt_top.ne
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsSumTmul
section
theorem UpperTheory.Reformulated.B.Qj2.exists_sum_tmul :
    ∀ {R O B σ : Type} [inst : CommRing R]
    [inst_1 : AddCommGroup O] [inst_2 : _root_.Module R O] [inst_3 : AddCommGroup B] [inst_4 : _root_.Module R B]
    [inst_5 : Fintype σ] (ω : Module.Basis σ R O) (x : TensorProduct R O B),
    ∃ (y : σ → B), x = ∑ s : σ, (ω : σ → O) s ⊗ₜ[R] y s := by
  intro R O B σ _ _ _ _ _ _ ω x
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul o b =>
    refine ⟨fun s => ω.repr o s • b, ?_⟩
    conv_lhs => rw [← ω.sum_repr o]
    rw [TensorProduct.sum_tmul]
    exact Finset.sum_congr rfl fun s _ => TensorProduct.smul_tmul _ _ _
  | add x₁ x₂ h₁ h₂ =>
    obtain ⟨y₁, rfl⟩ := h₁
    obtain ⟨y₂, rfl⟩ := h₂
    refine ⟨y₁ + y₂, ?_⟩
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun s _ => (TensorProduct.tmul_add _ _ _).symm
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsSupported
section
theorem UpperTheory.Reformulated.B.Qo8.exists_supported :
    ∀ {F : Type} [inst : Field F] [NumberField F]
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)),
    ∃ (π : NumberField.RingOfIntegers F),
      π ≠ (0 : NumberField.RingOfIntegers F) ∧
        π ∈ p.asIdeal ∧
          ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)), v ≠ p → π ∉ v.asIdeal := by
  intro F _ _ p
  have hp : p.asIdeal ∈ nonZeroDivisors (Ideal (NumberField.RingOfIntegers F)) :=
    mem_nonZeroDivisors_of_ne_zero p.ne_bot
  obtain ⟨n, hn, hpow⟩ :=
    (isOfFinOrder_of_finite (ClassGroup.mk0 ⟨p.asIdeal, hp⟩)).exists_pow_eq_one
  rw [← map_pow] at hpow
  have hprin : (p.asIdeal ^ n).IsPrincipal :=
    (ClassGroup.mk0_eq_one_iff (pow_mem hp n)).1 hpow
  obtain ⟨π, hπ⟩ := hprin
  have hπ' : p.asIdeal ^ n = Ideal.span {π} := hπ
  have hmem : π ∈ p.asIdeal ^ n := hπ' ▸ Ideal.mem_span_singleton_self π
  refine ⟨π, ?_, Ideal.pow_le_self hn.ne' hmem, ?_⟩
  · rintro rfl
    rw [Ideal.span_singleton_zero] at hπ'
    exact pow_ne_zero n p.ne_bot hπ'
  · intro v hv hπv
    have hle : p.asIdeal ^ n ≤ v.asIdeal := by
      rw [hπ', Ideal.span_le, Set.singleton_subset_iff]
      exact hπv
    have hle' : p.asIdeal ≤ v.asIdeal := v.isPrime.le_of_pow_le hle
    exact hv (IsDedekindDomain.HeightOneSpectrum.ext
      (p.isMaximal.eq_of_le v.isPrime.ne_top hle').symm)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsUniqueFixedPoint
section
open MvPowerSeries in
private theorem UpperTheory.Reformulated.B.Ydb5.le_order_iff {σ R : Type*} [CommRing R]
    (f g : MvPowerSeries σ R) (n : ℕ) :
    (n : ℕ∞) ≤ (f - g).order ↔ ∀ d : σ →₀ ℕ, d.degree < n → coeff d f = coeff d g := by
  constructor
  · intro h d hd
    have h0 : coeff d (f - g) = 0 :=
      coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hd) h)
    rwa [map_sub, sub_eq_zero] at h0
  · intro h
    refine nat_le_order fun d hd => ?_
    rw [map_sub, h d hd, sub_self]

theorem UpperTheory.Reformulated.B.Ydb5.existsUnique_fixedPoint.{u_1, u_2} :
    ∀ {σ : Type u_1} {R : Type u_2} [inst : CommRing R] (Φ : MvPowerSeries σ R → MvPowerSeries σ R),
      (∀ (f g : MvPowerSeries σ R) (n : ℕ), (↑n : ℕ∞) ≤ (f - g).order → (↑(n + (1 : ℕ)) : ℕ∞) ≤ (Φ f - Φ g).order) →
        ∃! f : MvPowerSeries σ R, Φ f = f := by
  intro σ R _ Φ h
  simp only [UpperTheory.Reformulated.B.Ydb5.le_order_iff] at h
  have step : ∀ (k : ℕ) (g : MvPowerSeries σ R) (d : σ →₀ ℕ), d.degree < k →
      MvPowerSeries.coeff d (Φ^[k] g) = MvPowerSeries.coeff d (Φ^[k] 0) := by
    intro k g
    induction k with
    | zero => intro d hd; exact absurd hd (Nat.not_lt_zero _)
    | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact h _ _ k ih
  let f : MvPowerSeries σ R := fun d => MvPowerSeries.coeff d (Φ^[d.degree + 1] 0)
  have hf : ∀ d : σ →₀ ℕ,
      MvPowerSeries.coeff d f = MvPowerSeries.coeff d (Φ^[d.degree + 1] 0) := fun _ => rfl
  have approx : ∀ (k : ℕ) (d : σ →₀ ℕ), d.degree < k →
      MvPowerSeries.coeff d f = MvPowerSeries.coeff d (Φ^[k] 0) := by
    intro k d hd
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hd)
    rw [hf, Function.iterate_add_apply Φ (Nat.succ _) m]
    exact (step _ _ d (Nat.lt_succ_self _)).symm
  refine ⟨f, ?_, ?_⟩
  · ext d
    rw [h f _ d.degree (approx _) d (Nat.lt_succ_self _), hf, Function.iterate_succ_apply']
  · intro g hg
    ext d
    rw [hf, ← step _ g d (Nat.lt_succ_self _), Function.iterate_fixed hg]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsValuationSubLeOne
section
theorem UpperTheory.Reformulated.B.ExistsValuationSubLeOne.exists_valuation_sub_le_one.{u_1, u_2} :
    ∀ {R : Type u_1} [inst : CommRing R] [inst_1 : IsDedekindDomain R] {K : Type u_2} [inst_2 : Field K]
    [inst_3 : Algebra R K] [inst_4 : IsFractionRing R K] (S : Finset (IsDedekindDomain.HeightOneSpectrum R))
    (x : IsDedekindDomain.HeightOneSpectrum R → K),
    ∃ (k : K),
      (∀ v ∈ S,
          (IsDedekindDomain.HeightOneSpectrum.valuation K v : K → WithZero (Multiplicative ℤ)) (k - x v) ≤
            (1 : WithZero (Multiplicative ℤ))) ∧
        ∀ v ∉ S,
          (IsDedekindDomain.HeightOneSpectrum.valuation K v : K → WithZero (Multiplicative ℤ)) k ≤
            (1 : WithZero (Multiplicative ℤ)) := by
  classical
  intro R _ _ K _ _ _ S x
  obtain ⟨⟨d, hdm⟩, hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors R) S x
  simp only at hd
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hdm
  have hdK : algebraMap R K d ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hdm
  have hr : ∀ v, ∃ r : R, v ∈ S → algebraMap R K r = algebraMap R K d * x v := by
    intro v
    by_cases hv : v ∈ S
    · obtain ⟨r, hr⟩ := hd v hv
      exact ⟨r, fun _ => by rw [hr, Algebra.smul_def]⟩
    · exact ⟨0, fun h => absurd h hv⟩
  choose r hr using hr
  have hI : Ideal.span {d} ≠ (0 : Ideal R) := by
    simpa using hd0
  let T : Finset (IsDedekindDomain.HeightOneSpectrum R) := S ∪ (Ideal.finite_factors hI).toFinset
  let e : IsDedekindDomain.HeightOneSpectrum R → ℕ := fun v =>
    (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {d} : Ideal R)).factors
  have he : ∀ v : IsDedekindDomain.HeightOneSpectrum R,
      v.intValuation d = WithZero.exp (-(e v : ℤ)) := fun v => v.intValuation_if_neg hd0
  have he0 : ∀ v, v ∉ T → e v = 0 := by
    intro v hv
    have hmem : d ∉ v.asIdeal := by
      intro h
      apply hv
      simp only [T, Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
      exact Or.inr (Ideal.dvd_span_singleton.2 h)
    have h1 := IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.2 hmem
    rw [he, ← WithZero.exp_zero, WithZero.exp_inj] at h1
    omega
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := T)
    (fun v : IsDedekindDomain.HeightOneSpectrum R => v.asIdeal) e
    (fun v _ => v.prime)
    (fun v _ w _ hvw h => hvw (IsDedekindDomain.HeightOneSpectrum.ext h))
    (fun v => if v.1 ∈ S then r v.1 else 0)
  have key : ∀ (v : IsDedekindDomain.HeightOneSpectrum R) (a : R), a ∈ v.asIdeal ^ e v →
      v.valuation K (algebraMap R K a / algebraMap R K d) ≤ 1 := by
    intro v a ha
    rw [map_div₀, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap, he]
    exact div_le_one_of_le₀ ((v.intValuation_le_pow_iff_mem a (e v)).2 ha) zero_le'
  refine ⟨algebraMap R K y / algebraMap R K d, fun v hv => ?_, fun v hv => ?_⟩
  · have hvT : v ∈ T := Finset.mem_union_left _ hv
    have h1 := hy v hvT
    simp only [hv, if_true] at h1
    have h2 := key v _ h1
    have h3 : algebraMap R K (y - r v) / algebraMap R K d =
        algebraMap R K y / algebraMap R K d - x v := by
      rw [map_sub, hr v hv]
      field_simp
    rwa [h3] at h2
  · apply key
    by_cases hvT : v ∈ T
    · have h1 := hy v hvT
      simpa [hv] using h1
    · simp [he0 v hvT]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExpSq
section
theorem UpperTheory.Reformulated.B.Qf11.expSq :
    ∀ {n : ℕ} (N : Matrix (Fin n) (Fin n) ℂ),
    N * N = (0 : Matrix (Fin n) (Fin n) ℂ) → NormedSpace.exp N = (1 : Matrix (Fin n) (Fin n) ℂ) + N := by
  intro n N h
  have hz : ∀ k : ℕ, k ∉ Finset.range 2 → ((k.factorial : ℂ)⁻¹) • N ^ k = 0 := by
    intro k hk
    have hk2 : 2 ≤ k := by
      rw [Finset.mem_range] at hk
      omega
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk2
    rw [pow_add, pow_two, h, zero_mul, smul_zero]
  rw [NormedSpace.exp_eq_tsum ℂ]
  beta_reduce
  rw [tsum_eq_sum hz]
  simp [Finset.sum_range_succ]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExtIntegral
section
theorem UpperTheory.Reformulated.B.Qe16.ext_integral :
    ∀ {B S K : Type} [inst : CommRing B] [inst_1 : CommRing S]
    [inst_2 : Field K] [IsAlgClosed K] [inst_4 : Algebra B S] [Algebra.IsIntegral B S],
    Function.Injective (⇑(Algebra.algebraMap B S) : B → S) →
      ∀ (φ : B →+* K), ∃ (Φ : S →+* K), ∀ (b : B), (Φ : S → K) ((Algebra.algebraMap B S : B → S) b) = (φ : B → K) b := by
  intro B S K _ _ _ _ _ _ hinj φ
  haveI hP : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  obtain ⟨Q, -, hQ, hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := S)
    (RingHom.ker φ) ⊥ (by
      rw [← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).1 hinj]
      exact bot_le)
  haveI : Q.LiesOver (RingHom.ker φ) := ⟨hQP.symm⟩
  letI : Algebra (B ⧸ RingHom.ker φ) K := (RingHom.kerLift φ).toAlgebra
  haveI : FaithfulSMul (B ⧸ RingHom.ker φ) K :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.kerLift_injective φ)
  haveI : Algebra.IsIntegral (B ⧸ RingHom.ker φ) (S ⧸ Q) :=
    Algebra.IsIntegral.tower_top (R := B)
  haveI : FaithfulSMul (B ⧸ RingHom.ker φ) (S ⧸ Q) := inferInstance
  haveI : Module.IsTorsionFree (B ⧸ RingHom.ker φ) (S ⧸ Q) :=
    Module.isTorsionFree_iff_faithfulSMul.2 inferInstance
  haveI : Module.IsTorsionFree (B ⧸ RingHom.ker φ) K :=
    Module.isTorsionFree_iff_faithfulSMul.2 inferInstance
  haveI : Nontrivial (B ⧸ RingHom.ker φ) := Ideal.Quotient.nontrivial_iff.2 hP.ne_top
  haveI : Algebra.IsAlgebraic (B ⧸ RingHom.ker φ) (S ⧸ Q) := Algebra.IsIntegral.isAlgebraic
  let f : (S ⧸ Q) →ₐ[B ⧸ RingHom.ker φ] K := IsAlgClosed.lift
  refine ⟨f.toRingHom.comp (Ideal.Quotient.mk Q), fun b => ?_⟩
  exact (f.commutes (Ideal.Quotient.mk _ b)).trans (RingHom.kerLift_mk φ b)
end

