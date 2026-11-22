import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ExistsPowSmulMemBall
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.RecNZFullFacts

-- bundled from Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.IsIntegralOfAll
section
set_option linter.style.haveILetI false

noncomputable section

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps.Hunt

section
variable (O A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing A] [Algebra O A]

def redAs (m : Ideal A) : ↥(As O A) →ₐ[O] ↥(As O (A ⧸ m)) :=
  ((Ideal.Quotient.mkₐ O m).comp (As O A).val).codRestrict (As O (A ⧸ m))
    fun a => (show IsIntegral O (a : A) from a.2).map (Ideal.Quotient.mkₐ O m)

theorem redAs_coe (m : Ideal A) (a : ↥(As O A)) : (redAs O A m a : A ⧸ m) = Ideal.Quotient.mk m a := rfl

end

theorem isIntegral_of_all (O A : Type) [CommRing O] [CommRing A] [Algebra O A] [IsArtinianRing A] [IsReduced A] (a : A)
    (h : ∀ m : MaximalSpectrum A, IsIntegral O (Ideal.Quotient.mk m.asIdeal a)) : IsIntegral O a := by
  classical
  haveI : Finite (MaximalSpectrum A) := by
    haveI := (IsArtinianRing.setOf_isMaximal_finite A).to_subtype
    exact Finite.of_injective
      (fun m : MaximalSpectrum A => (⟨m.asIdeal, m.isMaximal⟩ : {I : Ideal A | I.IsMaximal}))
      (fun x y hxy => MaximalSpectrum.ext (congrArg Subtype.val hxy))
  letI := Fintype.ofFinite (MaximalSpectrum A)
  choose p hp hpa using fun m : MaximalSpectrum A => h m
  have hmem : ∀ m : MaximalSpectrum A, Polynomial.aeval a (p m) ∈ m.asIdeal := by
    intro m
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have e : (Ideal.Quotient.mk m.asIdeal) (Polynomial.aeval a (p m)) =
        Polynomial.aeval (Ideal.Quotient.mk m.asIdeal a) (p m) := by
      rw [← Ideal.Quotient.mkₐ_eq_mk O, Polynomial.aeval_algHom_apply]
    rw [e, Polynomial.aeval_def]
    exact hpa m
  have hzero : ∀ x : A, (∀ m : MaximalSpectrum A, x ∈ m.asIdeal) → x = 0 := by
    intro x hx
    have hj : x ∈ Ideal.jacobson (⊥ : Ideal A) := by
      rw [Ideal.jacobson]
      refine Ideal.mem_sInf.mpr ?_
      rintro J ⟨-, hJ⟩
      exact hx ⟨J, hJ⟩
    obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := A)
    have hxn : x ^ n = 0 := by
      have := Ideal.pow_mem_pow hj n
      rw [hn] at this
      exact (Submodule.mem_bot _).mp this
    exact IsReduced.eq_zero x ⟨n, hxn⟩
  refine ⟨∏ m, p m, Polynomial.monic_prod_of_monic _ _ fun m _ => hp m, ?_⟩
  rw [← Polynomial.aeval_def, map_prod]
  apply hzero
  intro m
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ m)]
  exact Ideal.mul_mem_right _ _ (hmem m)

theorem integralClosure_dvr :
    ∀ (O K A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [CharZero K] [CommRing A] [Algebra K A] [Algebra O A] [IsScalarTower O K A]
    [FiniteDimensional K A] [IsReduced A],
    Module.Finite O ↥(As O A) ∧ ∀ ζ : Pts O A, IsDVRAt ζ := by
  intro O K A _ _ _ _ _ _ _ _ _ _ _ _ _
  classical
  haveI : IsArtinianRing A := IsArtinianRing.of_finite K A
  haveI := Fintype.ofFinite (MaximalSpectrum A)
  have hinj : ∀ a : A, (∀ m : MaximalSpectrum A, Ideal.Quotient.mk m.asIdeal a = 0) → a = 0 := fun a h => by
    apply (IsArtinianRing.equivPi A).injective
    rw [map_zero]
    funext m
    exact h m
  have hsurj : ∀ b : (m : MaximalSpectrum A) → A ⧸ m.asIdeal, ∃ a : A, ∀ m, Ideal.Quotient.mk m.asIdeal a = b m := fun b => by
    obtain ⟨a, ha⟩ := (IsArtinianRing.equivPi A).surjective b
    exact ⟨a, fun m => congrFun ha m⟩
  constructor
  · haveI : ∀ m : MaximalSpectrum A, Module.Finite O ↥(As O (A ⧸ m.asIdeal)) := fun m => by
      haveI := m.isMaximal
      letI := Ideal.Quotient.field m.asIdeal
      exact IsIntegralClosure.finite O K (A ⧸ m.asIdeal) _
    refine Module.Finite.of_injective (LinearMap.pi fun m : MaximalSpectrum A => (redAs O A m.asIdeal).toLinearMap) ?_
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    apply Subtype.ext
    exact hinj _ fun m => congrArg Subtype.val (congrFun ha m)
  · intro ζ
    choose e he using fun m : MaximalSpectrum A => hsurj (Pi.single m 1)
    have hei : ∀ m, IsIntegral O (e m) := fun m => isIntegral_of_all O A _ fun m' => by
      rw [he]
      by_cases h : m' = m
      · subst h; rw [Pi.single_eq_same]; exact isIntegral_one
      · rw [Pi.single_eq_of_ne h]; exact isIntegral_zero
    have hsum : ∑ m, (⟨e m, hei m⟩ : ↥(As O A)) = 1 := by
      apply Subtype.ext
      rw [← sub_eq_zero]
      apply hinj
      intro m'
      rw [map_sub]
      simp only [AddSubmonoidClass.coe_finsetSum, map_sum, he, OneMemClass.coe_one, map_one]
      rw [← Finset.sum_apply, Finset.univ_sum_single]
      simp
    obtain ⟨m, hm⟩ : ∃ m, (⟨e m, hei m⟩ : ↥(As O A)) ∉ ζ.asIdeal := by
      by_contra hc
      push Not at hc
      exact ζ.isMaximal.ne_top ((Ideal.eq_top_iff_one _).2 (hsum ▸ Ideal.sum_mem _ fun m _ => hc m))
    haveI := m.isMaximal
    letI := Ideal.Quotient.field m.asIdeal
    let f := redAs O A m.asIdeal
    have hf : Function.Surjective f := fun b => by
      obtain ⟨a, ha⟩ := hsurj (Pi.single m (b : A ⧸ m.asIdeal))
      refine ⟨⟨a, isIntegral_of_all O A _ fun m' => ?_⟩, Subtype.ext ?_⟩
      · rw [ha]
        by_cases h : m' = m
        · subst h; rw [Pi.single_eq_same]; exact b.2
        · rw [Pi.single_eq_of_ne h]; exact isIntegral_zero
      · show Ideal.Quotient.mk m.asIdeal a = _
        rw [ha, Pi.single_eq_same]
    have hker : ∀ x, f x = 0 → (⟨e m, hei m⟩ : ↥(As O A)) * x = 0 := fun x hx => by
      apply Subtype.ext
      apply hinj
      intro m'
      show Ideal.Quotient.mk m'.asIdeal (e m * x) = 0
      rw [map_mul, he]
      by_cases h : m' = m
      · subst h
        have : Ideal.Quotient.mk m'.asIdeal (x : A) = 0 := congrArg Subtype.val hx
        rw [this, mul_zero]
      · rw [Pi.single_eq_of_ne h, zero_mul]
    have hkl : RingHom.ker f.toRingHom ≤ ζ.asIdeal := fun x hx =>
      (ζ.isMaximal.isPrime.mem_or_mem (by rw [hker x hx]; exact zero_mem _)).resolve_left hm
    have hcm : (ζ.asIdeal.map f.toRingHom).comap f.toRingHom = ζ.asIdeal := by
      rw [Ideal.comap_map_of_surjective f.toRingHom hf]
      exact sup_eq_left.2 hkl
    have hmax : (ζ.asIdeal.map f.toRingHom).IsMaximal := by
      rcases Ideal.map_eq_top_or_isMaximal_of_surjective f.toRingHom hf ζ.isMaximal with h | h
      · rw [h, Ideal.comap_top] at hcm; exact absurd hcm.symm ζ.isMaximal.ne_top
      · exact h
    let ζ' : Pts O (A ⧸ m.asIdeal) := ⟨ζ.asIdeal.map f.toRingHom, hmax⟩
    have hmem : ∀ x, f x ∈ ζ'.asIdeal ↔ x ∈ ζ.asIdeal := fun x => by
      rw [← hcm]; exact Iff.rfl
    have hD : IsDVRAt ζ' := isDVRAt_of_field_ext K ζ'
    letI alg : Algebra ↥(As O A) (Loc ζ') := ((algebraMap _ (Loc ζ')).comp f.toRingHom).toAlgebra
    have halg : ∀ x, algebraMap ↥(As O A) (Loc ζ') x = algebraMap _ (Loc ζ') (f x) := fun _ => rfl
    haveI : IsLocalization.AtPrime (Loc ζ') ζ.asIdeal := by
      refine ⟨⟨fun s => ?_, fun z => ?_, fun {x y} h => ?_⟩⟩
      · rw [halg]
        exact IsLocalization.map_units (Loc ζ') (⟨f s, fun h => s.2 ((hmem _).1 h)⟩ : ζ'.asIdeal.primeCompl)
      · obtain ⟨⟨b, t⟩, hb⟩ := IsLocalization.surj ζ'.asIdeal.primeCompl z
        obtain ⟨a, rfl⟩ := hf b
        obtain ⟨s, hs⟩ := hf t
        refine ⟨⟨a, ⟨s, fun h => t.2 (hs ▸ (hmem _).2 h)⟩⟩, ?_⟩
        simp only [halg, hs]
        exact hb
      · rw [halg, halg] at h
        obtain ⟨t, ht⟩ := (IsLocalization.eq_iff_exists ζ'.asIdeal.primeCompl (Loc ζ')).1 h
        obtain ⟨s, hs⟩ := hf t
        have hs' : s ∉ ζ.asIdeal := fun h => t.2 (hs ▸ (hmem _).2 h)
        refine ⟨⟨⟨e m, hei m⟩ * s, fun h => (ζ.isMaximal.isPrime.mem_or_mem h).elim hm hs'⟩, ?_⟩
        have := hker (s * x - s * y) (by rw [map_sub, map_mul, map_mul, hs, ht, sub_self])
        show ⟨e m, hei m⟩ * s * x = ⟨e m, hei m⟩ * s * y
        rw [← sub_eq_zero, ← this]; ring
    let E := (IsLocalization.algEquiv ζ.asIdeal.primeCompl (Loc ζ') (Loc ζ)).toRingEquiv
    haveI := hD.isDomain
    haveI := hD.isDVR
    haveI hd : IsDomain (Loc ζ) := E.symm.toMulEquiv.isDomain _
    exact ⟨hd, IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing E⟩

end Formalism.MainNotions.Gaps.EtaleWeightGaps.Hunt
end
end

-- bundled from Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.RecNZFullLen
section
noncomputable section

namespace Formalism.MainNotions.Gaps.RN

open TensorProduct IsLocalRing IsDiscreteValuationRing

private theorem length_quot_span_singleton_dvr_lemma {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (ϖ : O) (hϖ : Irreducible ϖ) (n : ℕ) :
    Module.length O (O ⧸ Ideal.span {ϖ ^ n}) = n := by
  induction n with
  | zero =>
    rw [pow_zero, Nat.cast_zero, Module.length_eq_zero_iff, Ideal.Quotient.subsingleton_iff,
      Ideal.span_singleton_one]
  | succ n ih =>
    let f : (O ⧸ Ideal.span {ϖ}) →ₗ[O] (O ⧸ Ideal.span {ϖ ^ (n + 1)}) :=
      (Ideal.span {ϖ}).mapQ (Ideal.span {ϖ ^ (n + 1)}) (LinearMap.mulLeft O (ϖ ^ n)) (by
        intro x hx
        obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hx
        refine Submodule.mem_comap.mpr (Ideal.mem_span_singleton'.mpr ⟨a, ?_⟩)
        rw [LinearMap.mulLeft_apply]
        ring)
    let g : (O ⧸ Ideal.span {ϖ ^ (n + 1)}) →ₗ[O] (O ⧸ Ideal.span {ϖ ^ n}) :=
      (Ideal.span {ϖ ^ (n + 1)}).mapQ (Ideal.span {ϖ ^ n}) LinearMap.id (by
        intro x hx
        obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hx
        refine Submodule.mem_comap.mpr (Ideal.mem_span_singleton'.mpr ⟨a * ϖ, ?_⟩)
        rw [LinearMap.id_apply]
        ring)
    have hf : Function.Injective f := by
      rw [injective_iff_map_eq_zero]
      intro x hx
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      change Submodule.Quotient.mk (ϖ ^ n * x) = (0 : O ⧸ Ideal.span {ϖ ^ (n + 1)}) at hx
      rw [Submodule.Quotient.mk_eq_zero] at hx
      rw [Submodule.Quotient.mk_eq_zero]
      obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hx
      refine Ideal.mem_span_singleton'.mpr ⟨a, ?_⟩
      have hne : ϖ ^ n ≠ 0 := pow_ne_zero _ hϖ.ne_zero
      apply mul_left_cancel₀ hne
      rw [← ha]
      ring
    have hg : Function.Surjective g := by
      intro y
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      exact ⟨Submodule.Quotient.mk y, rfl⟩
    have hex : Function.Exact f g := by
      intro y
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      change Submodule.Quotient.mk y = (0 : O ⧸ Ideal.span {ϖ ^ n}) ↔ _
      rw [Submodule.Quotient.mk_eq_zero]
      constructor
      · intro hy
        obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hy
        refine ⟨Submodule.Quotient.mk a, ?_⟩
        change Submodule.Quotient.mk (ϖ ^ n * a) = (Submodule.Quotient.mk (a * ϖ ^ n) : O ⧸ Ideal.span {ϖ ^ (n + 1)})
        rw [mul_comm]
      · rintro ⟨x, hx⟩
        obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
        change Submodule.Quotient.mk (ϖ ^ n * x) = (Submodule.Quotient.mk y : O ⧸ Ideal.span {ϖ ^ (n + 1)}) at hx
        rw [Submodule.Quotient.eq] at hx
        obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hx
        refine Ideal.mem_span_singleton'.mpr ⟨x - b * ϖ, ?_⟩
        linear_combination -hb
    have hs : Module.length O (O ⧸ Ideal.span {ϖ}) = 1 := by
      have hm : IsLocalRing.maximalIdeal O = Ideal.span {ϖ} := by
        first
          | exact (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
          | exact hϖ.maximalIdeal_eq
      rw [Module.length_eq_one_iff, ← hm]
      first
        | exact isSimpleModule_iff_isCoatom.mpr (IsLocalRing.maximalIdeal.isMaximal O).out
        | exact isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp (IsLocalRing.maximalIdeal.isMaximal O))
        | infer_instance
    rw [Module.length_eq_add_of_exact f g hf hg hex, hs, ih]
    push_cast
    ring

theorem length_quot_span_singleton_dvr {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (t : O)
    (ht : t ≠ 0) : Module.length O (O ⧸ Ideal.span {t}) = addVal O t := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ht hϖ
  rw [IsDiscreteValuationRing.addVal_def _ u hϖ n rfl, Ideal.span_singleton_mul_left_unit u.isUnit]
  exact length_quot_span_singleton_dvr_lemma ϖ hϖ n

open Classical in

theorem length_pi_span_quot (A O : Type*) [CommRing A] [CommRing O] [Algebra A O] (ι : Type*) [Fintype ι]
    (N : Submodule A (ι → A)) :
    Module.length O ((ι → O) ⧸ Submodule.span O ((fun x : ι → A => algebraMap A O ∘ x) '' (N : Set (ι → A)))) =
      Module.length O (O ⊗[A] ((ι → A) ⧸ N)) := by
  set S := Submodule.span O ((fun x : ι → A => algebraMap A O ∘ x) '' (N : Set (ι → A))) with hS

  let Φ : (ι → O) →ₗ[O] O ⊗[A] ((ι → A) ⧸ N) :=
    { toFun := fun v => ∑ i, v i ⊗ₜ[A] (Submodule.Quotient.mk (Pi.single i 1) : (ι → A) ⧸ N)
      map_add' := fun v w => by
        simp only [Pi.add_apply, TensorProduct.add_tmul, Finset.sum_add_distrib]
      map_smul' := fun c v => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, TensorProduct.smul_tmul'] }
  have hmk : ∀ x : ι → A, (Submodule.Quotient.mk x : (ι → A) ⧸ N) =
      ∑ i, x i • (Submodule.Quotient.mk (Pi.single i 1) : (ι → A) ⧸ N) := by
    intro x
    have hx : x = ∑ i, x i • Pi.single i (1 : A) := by
      ext k
      simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hx]
    simp only [← Submodule.mkQ_apply, map_sum, map_smul]
  have hΦg : ∀ x : ι → A, Φ (algebraMap A O ∘ x) = (1 : O) ⊗ₜ[A] (Submodule.Quotient.mk x : (ι → A) ⧸ N) := by
    intro x
    change ∑ i, algebraMap A O (x i) ⊗ₜ[A] (Submodule.Quotient.mk (Pi.single i 1) : (ι → A) ⧸ N) = _
    rw [hmk x, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  have hker : S ≤ LinearMap.ker Φ := by
    rw [hS, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    have hx0 : (Submodule.Quotient.mk x : (ι → A) ⧸ N) = 0 := (Submodule.Quotient.mk_eq_zero N).mpr hx
    show Φ (algebraMap A O ∘ x) = 0
    rw [hΦg x, hx0, TensorProduct.tmul_zero]
  let Φbar : ((ι → O) ⧸ S) →ₗ[O] O ⊗[A] ((ι → A) ⧸ N) := S.liftQ Φ hker
  let ψ1 : (ι → A) →ₗ[A] (ι → O) ⧸ S :=
    (S.mkQ.restrictScalars A) ∘ₗ (LinearMap.compLeft (Algebra.linearMap A O) ι)
  have hN : N ≤ LinearMap.ker ψ1 := by
    intro x hx
    rw [LinearMap.mem_ker]
    show (Submodule.Quotient.mk (algebraMap A O ∘ x) : (ι → O) ⧸ S) = 0
    rw [Submodule.Quotient.mk_eq_zero, hS]
    exact Submodule.subset_span ⟨x, hx, rfl⟩
  let ψ0 : ((ι → A) ⧸ N) →ₗ[A] (ι → O) ⧸ S := N.liftQ ψ1 hN
  let Ψ : O ⊗[A] ((ι → A) ⧸ N) →ₗ[O] (ι → O) ⧸ S :=
    TensorProduct.AlgebraTensorModule.lift (LinearMap.toSpanSingleton O (((ι → A) ⧸ N) →ₗ[A] (ι → O) ⧸ S) ψ0)
  have h1 : Φbar ∘ₗ Ψ = LinearMap.id := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro c q
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective N q
    rw [LinearMap.comp_apply, LinearMap.id_apply, TensorProduct.AlgebraTensorModule.lift_tmul,
      LinearMap.toSpanSingleton_apply, LinearMap.smul_apply, Submodule.liftQ_apply, map_smul]
    change c • Φ (algebraMap A O ∘ x) = _
    rw [hΦg x, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hs : ∀ i : ι, algebraMap A O ∘ (Pi.single i (1 : A) : ι → A) = Pi.single i (1 : O) := by
    intro i
    ext k
    by_cases h : k = i <;> simp [Pi.single_apply, h]
  have h2 : Ψ ∘ₗ Φbar = LinearMap.id := by
    apply Submodule.linearMap_qext
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.comp_apply, LinearMap.id_apply, Submodule.mkQ_apply, Submodule.liftQ_apply]
    change Ψ (∑ i, v i ⊗ₜ[A] (Submodule.Quotient.mk (Pi.single i 1) : (ι → A) ⧸ N)) = _
    rw [map_sum]
    simp only [Ψ, TensorProduct.AlgebraTensorModule.lift_tmul, LinearMap.toSpanSingleton_apply,
      LinearMap.smul_apply, Submodule.liftQ_apply]
    change ∑ i, v i • (Submodule.Quotient.mk (algebraMap A O ∘ Pi.single i 1) : (ι → O) ⧸ S) = _
    have hv : v = ∑ i, v i • Pi.single i (1 : O) := by
      ext k
      simp [Finset.sum_apply, Pi.single_apply]
    conv_rhs => rw [hv]
    rw [← Submodule.mkQ_apply, map_sum]
    simp only [map_smul, Submodule.mkQ_apply, hs]
  exact LinearEquiv.length_eq (LinearEquiv.ofLinear Φbar Ψ h1 h2)

theorem lenBaseChangeDVR : LenBaseChangeDVR := by
  intro A O _ _ _ _ _ _ f hloc hinj ϖ hϖ ι _ N
  letI : Algebra A O := f.toAlgebra
  haveI : IsLocalHom (algebraMap A O) := hloc
  haveI : Module.IsTorsionFree A O := Module.IsTorsionFree.of_smul_eq_zero (fun a c h => by
    rw [Algebra.smul_def, mul_eq_zero] at h
    exact h.imp_left (fun h0 => hinj (h0.trans (map_zero f).symm)))
  haveI : Module.Flat A O := inferInstance
  have h0 : f ϖ ≠ 0 := fun h => hϖ.ne_zero (hinj (h.trans (map_zero f).symm))
  have h1 := length_pi_span_quot A O ι N
  have h2 : (IsLocalRing.maximalIdeal A).map (algebraMap A O) = Ideal.span {f ϖ} := by
    rw [hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
    rfl
  have h3 : ((addVal O (f ϖ)).toNat : ℕ∞) = addVal O (f ϖ) :=
    ENat.coe_toNat (fun h => h0 (addVal_eq_top_iff.1 h))
  rw [IsLocalRing.length_baseChange, h2, length_quot_span_singleton_dvr _ h0] at h1
  rw [h3, mul_comm]
  exact h1

end Formalism.MainNotions.Gaps.RN

end
end

