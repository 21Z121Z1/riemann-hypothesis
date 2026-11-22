import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
import GroundTheory.GlobalFields.ExistenceTheorem.PowerIndex
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0007
import CompanionTheory.AutomorphicTheory.HeckeStandardModules.ExistsCen
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.Bundle0003
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0029

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.CardSUnit
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem index_range_eq_card_ker {T : Type*} [CommGroup T] [Finite T] (f : T →* T) :
    f.range.index = Nat.card f.ker := by
  have h1 := Subgroup.card_mul_index f.range
  have h2 := Subgroup.card_mul_index f.ker
  have hk : f.ker.index = Nat.card f.range := by
    show Nat.card (T ⧸ f.ker) = _
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
  rw [hk] at h2
  have hpos : 0 < Nat.card f.range := Nat.card_pos
  have h3 : Nat.card f.range * f.range.index = Nat.card f.range * Nat.card f.ker := by
    rw [h1, ← h2, mul_comm]
  exact Nat.eq_of_mul_eq_mul_left hpos h3

private theorem mem_unit_of_pow_mem {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))} {p : ℕ}
    (hp : p ≠ 0) {b : Kˣ} (hb : b ^ p ∈ S.unit K) : b ∈ S.unit K := by
  intro v hv
  have h := hb v hv
  rw [Units.val_pow_eq_pow_val, map_pow] at h
  simpa [hp] using h

private theorem powK_subgroupOf {K : Type} [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K))) {p : ℕ}
    (hp : p ≠ 0) : (powK K p).subgroupOf (S.unit K) = (powMonoidHom p : S.unit K →* S.unit K).range := by
  ext x
  rw [Subgroup.mem_subgroupOf, powK.eq_1, MonoidHom.mem_range, MonoidHom.mem_range]
  constructor
  · rintro ⟨b, hb⟩
    rw [powMonoidHom_apply] at hb
    have hbS : b ∈ S.unit K := mem_unit_of_pow_mem hp (by rw [hb]; exact x.2)
    refine ⟨⟨b, hbS⟩, ?_⟩
    apply Subtype.ext
    simpa using hb
  · rintro ⟨c, hc⟩
    refine ⟨c.1, ?_⟩
    rw [← hc]
    simp

private theorem card_ker_eq {K : Type} [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K))) (n : ℕ) [NeZero n] :
    Nat.card (powMonoidHom n : CommGroup.torsion (S.unit K) →* CommGroup.torsion (S.unit K)).ker =
      Nat.card (rootsOfUnity n K) := by
  have hfin : ∀ ζ : rootsOfUnity n K, IsOfFinOrder (ζ : Kˣ) := fun ζ =>
    isOfFinOrder_iff_pow_eq_one.mpr ⟨n, NeZero.pos n, (mem_rootsOfUnity _ _).mp ζ.2⟩
  have hS : ∀ ζ : rootsOfUnity n K, (ζ : Kˣ) ∈ S.unit K := fun ζ v _ =>
    GroundTheory.Global.SUnit.valuation_eq_one_of_isOfFinOrder (hfin ζ) v
  refine Nat.card_congr
    { toFun := fun t => ⟨t.1.1.1, (mem_rootsOfUnity _ _).mpr (by
        have h := congrArg (fun y : CommGroup.torsion (S.unit K) => ((y : S.unit K) : Kˣ))
          (MonoidHom.mem_ker.mp t.2)
        simpa using h)⟩
      invFun := fun ζ => ⟨⟨⟨ζ.1, hS ζ⟩, (CommGroup.mem_torsion _).mpr
          (isOfFinOrder_iff_pow_eq_one.mpr ⟨n, NeZero.pos n, Subtype.ext (by
            simpa using (mem_rootsOfUnity _ _).mp ζ.2)⟩)⟩,
        MonoidHom.mem_ker.mpr (Subtype.ext (Subtype.ext (by
            simpa using (mem_rootsOfUnity _ _).mp ζ.2)))⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem UpperTheory.V.Kum.cardSUnit :
    ∀ (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K))) (n : ℕ) [NeZero n], S.Finite → Nat.card (S.unit K ⧸ (powK K n).subgroupOf (S.unit K)) = n ^ (InfinitePlace.nrRealPlaces K + InfinitePlace.nrComplexPlaces K - 1 + Nat.card S) * Nat.card (rootsOfUnity n K) := by
  intro K _ _ S n _ hS
  haveI : Finite S := hS
  rw [← Subgroup.index_eq_card, powK_subgroupOf S (NeZero.ne n),
    GroundTheory.Global.index_range_powMonoidHom_eq_pow_mul (NeZero.ne n), GroundTheory.Global.SUnit.finrank_quotient_torsion,
    index_range_eq_card_ker, card_ker_eq, Units.rank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ClMapBasic
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem clMapBasic_mem {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] (τ : K ≃+* K')
    (I : Ideal (𝓞 K)) (y : 𝓞 K') :
    y ∈ I.map (RingOfIntegers.mapRingEquiv τ) ↔ ∃ x ∈ I, RingOfIntegers.mapRingEquiv τ x = y :=
  Ideal.mem_map_iff_of_surjective _ (RingOfIntegers.mapRingEquiv τ).surjective

private theorem clMapBasic_lemma {K K' K'' : Type} [Field K] [NumberField K] [Field K'] [NumberField K']
    [Field K''] [NumberField K''] (τ : K ≃+* K') (τ' : K' ≃+* K'') (c : ClassGroup (𝓞 K)) :
    clMap (τ.trans τ') c = clMap τ' (clMap τ c) := by
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
  rw [class_map_mk0, class_map_mk0, class_map_mk0]
  congr 1
  apply Subtype.ext
  show Ideal.map _ _ = Ideal.map _ (Ideal.map _ _)
  ext y
  rw [clMapBasic_mem, clMapBasic_mem]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨RingOfIntegers.mapRingEquiv τ x, (clMapBasic_mem τ _ _).mpr ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨x, hx, rfl⟩ := (clMapBasic_mem τ _ _).mp hz
    exact ⟨x, hx, rfl⟩
private theorem clMap_refl_apply {K : Type} [Field K] [NumberField K] (c : ClassGroup (𝓞 K)) :
    clMap (RingEquiv.refl K) c = c := by
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
  rw [class_map_mk0]
  congr 1
  apply Subtype.ext
  show Ideal.map _ _ = _
  ext y
  rw [clMapBasic_mem]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hy
    exact ⟨y, hy, rfl⟩

theorem UpperTheory.V.Kum.clMapBasic :
    ∀ (K K' K'' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] [Field K''] [NumberField K''] (τ : K ≃+* K') (τ' : K' ≃+* K''),
    (∀ c, clMap (RingEquiv.refl K) c = c) ∧ (∀ c, clMap (τ.trans τ') c = clMap τ' (clMap τ c)) ∧ Function.Bijective (clMap τ) ∧
    ∀ (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 K')), (∀ x, x ∈ v.asIdeal ↔ RingOfIntegers.mapRingEquiv τ x ∈ w.asIdeal) → clMap τ (primeCl v) = primeCl w := by
  intro K K' K'' _ _ _ _ _ _ τ τ'
  refine ⟨clMap_refl_apply, clMapBasic_lemma τ τ', ?_, ?_⟩
  · have hl : ∀ c, clMap τ.symm (clMap τ c) = c := by
      intro c
      rw [← clMapBasic_lemma, RingEquiv.self_trans_symm, clMap_refl_apply]
    have hr : ∀ c, clMap τ (clMap τ.symm c) = c := by
      intro c
      rw [← clMapBasic_lemma, RingEquiv.symm_trans_self, clMap_refl_apply]
    exact ⟨Function.LeftInverse.injective hl, Function.RightInverse.surjective hr⟩
  · intro v w hvw
    unfold primeCl
    rw [class_map_mk0]
    congr 1
    apply Subtype.ext
    show Ideal.map _ _ = _
    ext y
    rw [clMapBasic_mem]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hvw x).mp hx
    · intro hy
      refine ⟨(RingOfIntegers.mapRingEquiv τ).symm y, ?_, ?_⟩
      · rw [hvw, RingEquiv.apply_symm_apply]
        exact hy
      · exact RingEquiv.apply_symm_apply _ y
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ClProd
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem mk_eq_finprod (K : Type) [Field K] [NumberField K]
    (I : (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ) :
    ClassGroup.mk K I = ∏ᶠ v : HeightOneSpectrum (𝓞 K), primeCl v ^ FractionalIdeal.count K v I.1 := by
  let P : HeightOneSpectrum (𝓞 K) → (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ := fun v =>
    FractionalIdeal.mk0 K ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩
  have hfin : (Function.mulSupport fun v => P v ^ FractionalIdeal.count K v I.1).Finite :=
    (Filter.eventually_cofinite.1 (FractionalIdeal.finite_factors I.1)).subset
      fun v hv h => hv (by simp only [h, zpow_zero])
  have hI : ∏ᶠ v, P v ^ FractionalIdeal.count K v I.1 = I := by
    apply Units.ext
    rw [← Units.coeHom_apply, map_finprod _ hfin]
    conv_rhs => rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K I.ne_zero]
    exact finprod_congr fun v => by simp [Units.val_zpow_eq_zpow_val, P]
  conv_lhs => rw [← hI]
  rw [map_finprod _ hfin]
  exact finprod_congr fun v => by rw [map_zpow, ClassGroup.mk_mk0]; rfl

private theorem count_eq_ordv (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (a : Kˣ) :
    FractionalIdeal.count K v (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (a : K)) = ordv v a := by
  have hI : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (a : K) =
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K))
        (algebraMap (𝓞 K) K (IsLocalization.sec (nonZeroDivisors (𝓞 K)) (a : K)).2)⁻¹ *
        ↑(Ideal.span {(IsLocalization.sec (nonZeroDivisors (𝓞 K)) (a : K)).1} : Ideal (𝓞 K)) := by
    rw [FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.spanSingleton_mul_spanSingleton,
      IsLocalization.sec_spec' (nonZeroDivisors (𝓞 K)) (a : K), inv_mul_cancel_left₀]
    simpa using nonZeroDivisors.coe_ne_zero _
  rw [FractionalIdeal.count_well_defined K v (FractionalIdeal.spanSingleton_ne_zero_iff.2 a.ne_zero) hI]
  change _ = -Multiplicative.toAdd (v.valuationOfNeZeroToFun a)
  simp only [HeightOneSpectrum.valuationOfNeZeroToFun, toAdd_ofAdd]
  ring

theorem UpperTheory.V.Kum.clProd :
    ∀ (K : Type) [Field K] [NumberField K], (∀ I : (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ, ClassGroup.mk K I = ∏ᶠ v : HeightOneSpectrum (𝓞 K), primeCl v ^ FractionalIdeal.count K v I.1) ∧
    (∀ (v : HeightOneSpectrum (𝓞 K)) (a : Kˣ), FractionalIdeal.count K v (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (a : K)) = ordv v a) ∧ (∀ a : Kˣ, {v : HeightOneSpectrum (𝓞 K) | ordv v a ≠ 0}.Finite) ∧ ∀ a : Kˣ, radCl 1 a = 1 := by
  intro K _ _
  refine ⟨mk_eq_finprod K, count_eq_ordv K, fun a => ?_, fun a => ?_⟩
  · simp only [← count_eq_ordv]
    exact Filter.eventually_cofinite.1 (FractionalIdeal.finite_factors _)
  · have h := mk_eq_finprod K (toPrincipalIdeal (𝓞 K) K a)
    rw [coe_toPrincipalIdeal] at h
    simp only [count_eq_ordv] at h
    simp only [radCl, Nat.cast_one, Int.ediv_one]
    rw [← h, ClassGroup.mk_eq_one_iff, coe_toPrincipalIdeal]
    exact (FractionalIdeal.isPrincipal_iff _).2 ⟨_, rfl⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ClSubUniv
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

theorem UpperTheory.V.Kum.clSubUniv :
    ∀ (K : Type) [Field K] [NumberField K], clSub (Set.univ : Set (HeightOneSpectrum (𝓞 K))) = ⊤ := by
  intro K _ _
  classical
  have key : ∀ I : Ideal (𝓞 K), ∀ hI : I ∈ nonZeroDivisors (Ideal (𝓞 K)),
      ClassGroup.mk0 ⟨I, hI⟩ ∈ clSub (Set.univ : Set (HeightOneSpectrum (𝓞 K))) := by
    intro I
    induction I using UniqueFactorizationMonoid.induction_on_prime with
    | h₁ =>
      intro hI
      exact absurd hI (zero_notMem_nonZeroDivisors)
    | h₂ u hu =>
      intro hI
      have hu' : u = ⊤ := Ideal.isUnit_iff.mp hu
      subst hu'
      have : (⟨⊤, hI⟩ : nonZeroDivisors (Ideal (𝓞 K))) = 1 := Subtype.ext Ideal.one_eq_top.symm
      rw [this, map_one]
      exact Subgroup.one_mem _
    | h₃ a p ha hp ih =>
      intro hI
      have ha' : a ∈ nonZeroDivisors (Ideal (𝓞 K)) := mem_nonZeroDivisors_of_ne_zero ha
      have hp0 : p ≠ 0 := hp.ne_zero
      have hp' : p ∈ nonZeroDivisors (Ideal (𝓞 K)) := mem_nonZeroDivisors_of_ne_zero hp0
      have hsplit : (⟨p * a, hI⟩ : nonZeroDivisors (Ideal (𝓞 K))) = ⟨p, hp'⟩ * ⟨a, ha'⟩ := rfl
      rw [hsplit, map_mul]
      refine Subgroup.mul_mem _ ?_ (ih ha')
      have hpr : p.IsPrime := (Ideal.prime_iff_isPrime hp0).mp hp
      let v : HeightOneSpectrum (𝓞 K) := ⟨p, hpr, hp0⟩
      have hv : primeCl v = ClassGroup.mk0 ⟨p, hp'⟩ := rfl
      rw [← hv]
      exact Subgroup.subset_closure ⟨v, Set.mem_univ _, rfl⟩
  rw [eq_top_iff]
  intro x _
  obtain ⟨⟨I, hI⟩, rfl⟩ := ClassGroup.mk0_surjective x
  exact key I hI
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.CobOfGen
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

theorem UpperTheory.V.Kum.cobOfGen :
    ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (χ : Γ →* ℤ_[l]ˣ) (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R Γ M) (γ : Γ),
    Continuous χ → ContAction ρ → (∀ g, χ g = 1 → ∀ m, ρ g m = m) → (∀ g, χ g ∈ (Subgroup.zpowers (χ γ)).topologicalClosure) → (Function.Surjective fun m => ρ γ m - m) →
    ∀ z ∈ Z1 ρ, (∀ g, χ g = 1 → z g = 0) → z ∈ B1 ρ :=
  _root_.UpperTheory.Reformulated.B.CoboundaryOfGenerator.cobOfGen
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.DvdOfIne
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem ram_one {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] [IsGalois K E]
    (v : HeightOneSpectrum (𝓞 K)) (P : Ideal (𝓞 E)) [P.IsPrime] [P.LiesOver v.asIdeal]
    (L : IntermediateField K E) (h : P.inertia (E ≃ₐ[K] E) ≤ L.fixingSubgroup) :
    (P.under (𝓞 L)).ramificationIdx (𝓞 K) = 1 := by
  have hb := v.ne_bot
  have hPb : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hb P
  have hqb : P.under (𝓞 L) ≠ ⊥ := Ideal.under_ne_bot _ hPb
  have : IsGaloisGroup L.fixingSubgroup L E :=
    .of_mulEquiv_algEquiv (IntermediateField.fixingSubgroupEquiv L) fun _ _ ↦ rfl
  have : IsGaloisGroup L.fixingSubgroup (𝓞 L) (𝓞 E) :=
    IsGaloisGroup.of_isFractionRing _ _ _ L E
  have := v.isMaximal
  have : (P.under (𝓞 L)).IsMaximal := Ideal.IsPrime.isMaximal inferInstance hqb
  have : Finite (𝓞 K ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ hb
  have : Finite (𝓞 L ⧸ P.under (𝓞 L)) := Ideal.finiteQuotientOfFreeOfNeBot _ hqb
  have h1 := Ideal.card_inertia_eq_ramificationIdxIn (G := E ≃ₐ[K] E) v.asIdeal P
  have h2 := Ideal.card_inertia_eq_ramificationIdxIn (G := L.fixingSubgroup) (P.under (𝓞 L)) P
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx _ P (E ≃ₐ[K] E)] at h1
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx _ P L.fixingSubgroup] at h2
  have h3 := Ideal.ramificationIdx_tower (R := 𝓞 K) (P.under (𝓞 L)) P
  have h4 : Nat.card (P.inertia L.fixingSubgroup) =
      Nat.card ↥(P.inertia (E ≃ₐ[K] E) ⊓ L.fixingSubgroup) := by
    rw [← AddSubgroup.inertia_map_subtype, Subgroup.card_subtype]
  rw [← h1, ← h2, h4] at h3
  have hpos : 0 < Nat.card ↥(P.inertia (E ≃ₐ[K] E) ⊓ L.fixingSubgroup) := Nat.card_pos
  rw [inf_eq_left.mpr h] at h3 hpos
  exact Nat.eq_of_mul_eq_mul_right hpos (h3.symm.trans (one_mul _).symm)

private theorem dvd_of_ram {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver v.asIdeal]
    (h : Q.ramificationIdx (𝓞 K) = 1) (n : ℕ) (b : L) (a : Kˣ) (hb : b ^ n = algebraMap K L a) :
    (n : ℤ) ∣ ordv v a := by
  let w : HeightOneSpectrum (𝓞 L) := ⟨Q, inferInstance, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩
  have : w.asIdeal.LiesOver v.asIdeal := (inferInstance : Q.LiesOver v.asIdeal)
  have h1 := HeightOneSpectrum.valuation_liesOver L v w (a : K)
  rw [show v.asIdeal.ramificationIdx' w.asIdeal = 1 from
    (Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal Q v.ne_bot).trans h, pow_one, ← hb, map_pow,
    ← HeightOneSpectrum.valuationOfNeZero_eq] at h1
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [pow_zero, ← WithZero.coe_one, WithZero.coe_inj] at h1
    simp [ordv, h1]
  · have h0 : w.valuation L b ≠ 0 := fun e => by
      rw [e, zero_pow hn.ne'] at h1
      exact WithZero.coe_ne_zero h1
    obtain ⟨m, hm⟩ := WithZero.ne_zero_iff_exists.1 h0
    rw [← hm, ← WithZero.coe_pow, WithZero.coe_inj] at h1
    rw [ordv, h1, toAdd_pow, dvd_neg, nsmul_eq_mul]
    exact dvd_mul_right _ _

private theorem dvd_fin {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] [IsGalois K E]
    (v : HeightOneSpectrum (𝓞 K)) (P : Ideal (𝓞 E)) [P.IsPrime] [P.LiesOver v.asIdeal] (n : ℕ) (b : E) (a : Kˣ)
    (hb : b ^ n = algebraMap K E a) (h : ∀ τ ∈ P.inertia (E ≃ₐ[K] E), τ b = b) : (n : ℤ) ∣ ordv v a := by
  let L : IntermediateField K E := IntermediateField.fixedField (P.inertia (E ≃ₐ[K] E))
  have hle : P.inertia (E ≃ₐ[K] E) ≤ L.fixingSubgroup := (IntermediateField.le_iff_le _ _).1 le_rfl
  have hbL : b ∈ L := (IntermediateField.mem_fixedField_iff _ _).2 h
  have : (P.under (𝓞 L)).LiesOver v.asIdeal := ⟨by rw [Ideal.under_under]; exact Ideal.LiesOver.over⟩
  exact dvd_of_ram v (P.under (𝓞 L)) (ram_one v P L hle) n ⟨b, hbL⟩ a (Subtype.ext hb)

theorem UpperTheory.V.Kum.dvdOfIne :
    ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (n : ℕ) (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (β : Ω) (a : Kˣ), IsPlaceOver A v → β ^ n = algebraMap K Ω a → (∀ g ∈ Ine (F := K) A, g β = β) → (n : ℤ) ∣ ordv v a := by
  intro K Ω _ _ _ _ _ n A v β a hA hβ hI
  have : IsGalois K Ω := IsAlgClosure.isGalois K Ω
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  let L : IntermediateField K Ω := (FiniteGaloisIntermediateField.adjoin K ({β} : Set Ω)).toIntermediateField
  have hβL : β ∈ L := FiniteGaloisIntermediateField.subset_adjoin K _ rfl
  have : NumberField L := NumberField.of_module_finite K _
  have hv : (CompanionTheory.PlaceDict.cen A).under (𝓞 K) = v.asIdeal := Ideal.ext fun x => hA x
  have : Algebra.IsIntegral (𝓞 K) (𝓞 Ω) := ⟨fun b => (RingOfIntegers.isIntegral b).tower_top⟩
  have hm : (CompanionTheory.PlaceDict.cen A).IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := 𝓞 K) _ (by
      have := v.isMaximal
      rwa [← hv] at this)
  let P : Ideal (𝓞 L) := (CompanionTheory.PlaceDict.cen A).under (𝓞 L)
  have : P.LiesOver v.asIdeal := ⟨by rw [← hv]; exact (Ideal.under_under _).symm⟩
  refine dvd_fin v P n ⟨β, hβL⟩ a (Subtype.ext hβ) fun τ hτ => ?_
  obtain ⟨φ, h1, h2⟩ := CompanionTheory.PlaceDict.lift L (CompanionTheory.PlaceDict.cen A) τ (RingHom.id _) fun x => by
    rw [RingHom.id_apply, Ideal.Quotient.eq, ← map_sub, ← Ideal.mem_comap]
    exact hτ x
  obtain ⟨h3, h4⟩ := CompanionTheory.PlaceDict.of_cong A φ one_ne_zero fun b => by
    rw [pow_one]
    exact Ideal.Quotient.eq.1 (h2 b)
  have h5 : φ ∈ Ine (F := K) A := ⟨h3, fun x hx => by
    simpa using (A.mem_nonunits_iff).1 (h4 x ((A.valuation_le_one_iff _).1 hx))⟩
  rw [← h1]
  exact Subtype.ext ((AlgEquiv.restrictNormal_commutes φ L ⟨β, hβL⟩).trans (hI φ h5))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ExistsGen
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

open KStar.TotallyRealRoots in
private theorem eg_pow_mem {l : ℕ} [Fact l.Prime] {a : ℕ} (ha : 1 ≤ a) {u : ℤ_[l]ˣ} (hu : u ∈ princ l a) :
    u ^ l ∈ princ l (a + 1) := by
  rw [mem_princ] at hu ⊢
  obtain ⟨c, hc⟩ := hu
  obtain ⟨f, hf⟩ := sq_dvd_add_pow_sub_sub ((l : ℤ_[l]) ^ a * c) 1 l
  have hw : (u : ℤ_[l]) = 1 + (l : ℤ_[l]) ^ a * c := by rw [← hc]; ring
  obtain ⟨m, rfl⟩ : ∃ m, a = m + 1 := ⟨a - 1, by omega⟩
  refine ⟨c + (l : ℤ_[l]) ^ m * c ^ 2 * f, ?_⟩
  rw [Units.val_pow_eq_pow_val, hw]
  simp only [one_pow, one_mul] at hf
  linear_combination hf

open KStar.TotallyRealRoots in
private theorem eg_exists_not_mem {l : ℕ} [Fact l.Prime] {u : ℤ_[l]ˣ} (hu : u ≠ 1) :
    ∃ a, u ∉ princ l a := by
  by_contra h
  push Not at h
  apply hu
  have hb : IsClosed ((⊥ : Subgroup ℤ_[l]ˣ) : Set ℤ_[l]ˣ) := by
    rw [Subgroup.coe_bot]
    exact isClosed_singleton
  have := mem_of_isClosed hb (x := u) fun b => ⟨1, Subgroup.one_mem _, by
    rw [map_one]; exact (MonoidHom.mem_ker.1 (h b)).symm⟩
  exact Subgroup.mem_bot.1 this

theorem UpperTheory.V.Kum.existsGen :
    ∀ (l : ℕ) [Fact l.Prime] (V : Subgroup ℤ_[l]ˣ), IsClosed (V : Set ℤ_[l]ˣ) → (l ≠ 2 ∨ V ≤ KStar.TotallyRealRoots.princ l 2) → ∃ γ ∈ V, V ≤ (Subgroup.zpowers γ).topologicalClosure := by
  classical
  intro l _ V _ hl
  have hp : l.Prime := Fact.out
  obtain ⟨⟨_, g, hg, rfl⟩, hgen⟩ := IsCyclic.exists_generator (α := V.map (KStar.TotallyRealRoots.red l))
  have key : ∀ γ ∈ V, KStar.TotallyRealRoots.red l γ = KStar.TotallyRealRoots.red l g →
      V ⊓ KStar.TotallyRealRoots.princ l 1 ≤ (Subgroup.zpowers γ).topologicalClosure →
      V ≤ (Subgroup.zpowers γ).topologicalClosure := by
    intro γ hγ e h v hv
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hgen ⟨_, Subgroup.mem_map_of_mem _ hv⟩)
    have hk' : KStar.TotallyRealRoots.red l g ^ k = KStar.TotallyRealRoots.red l v := congrArg Subtype.val hk
    have h1 : v * (γ ^ k)⁻¹ ∈ V ⊓ KStar.TotallyRealRoots.princ l 1 := by
      refine Subgroup.mem_inf.2 ⟨V.mul_mem hv (V.inv_mem (V.zpow_mem hγ k)), ?_⟩
      rw [KStar.TotallyRealRoots.princ_one_eq_ker, MonoidHom.mem_ker, map_mul, map_inv, map_zpow, e, hk',
        mul_inv_cancel]
    have h2 : γ ^ k ∈ (Subgroup.zpowers γ).topologicalClosure :=
      Subgroup.le_topologicalClosure _ (Subgroup.zpow_mem_zpowers γ k)
    simpa using Subgroup.mul_mem _ (h h1) h2
  by_cases hW : V ⊓ KStar.TotallyRealRoots.princ l 1 = ⊥
  · exact ⟨g, hg, key g hg rfl (by rw [hW]; exact bot_le)⟩
  have hex : ∃ b, ¬ V ⊓ KStar.TotallyRealRoots.princ l 1 ≤ KStar.TotallyRealRoots.princ l b := by
    obtain ⟨⟨w, hw⟩, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hW
    obtain ⟨b, hb⟩ := eg_exists_not_mem (u := w) (fun h => hw1 (Subtype.ext h))
    exact ⟨b, fun h => hb (h hw)⟩
  have hspec := Nat.find_spec hex
  have hmin : ∀ m, m < Nat.find hex → V ⊓ KStar.TotallyRealRoots.princ l 1 ≤ KStar.TotallyRealRoots.princ l m :=
    fun m hm => not_not.1 (Nat.find_min hex hm)
  have h1 : 1 < Nat.find hex := by
    by_contra h
    exact hspec (inf_le_right.trans (KStar.TotallyRealRoots.princ_anti (by omega)))
  have h2 : l = 2 → 2 < Nat.find hex := by
    intro h2
    by_contra h
    exact hspec (inf_le_left.trans ((hl.resolve_left (not_not.2 h2)).trans (KStar.TotallyRealRoots.princ_anti (by omega))))
  obtain ⟨a, ha⟩ : ∃ a, Nat.find hex = a + 1 := ⟨Nat.find hex - 1, by omega⟩
  rw [ha] at hspec hmin h1 h2
  have hle := hmin a (Nat.lt_succ_self a)
  obtain ⟨u, hu, hua⟩ := SetLike.not_le_iff_exists.1 hspec
  have fin : ∀ γ ∈ V, KStar.TotallyRealRoots.red l γ = KStar.TotallyRealRoots.red l g → γ ^ (l - 1) ∉ KStar.TotallyRealRoots.princ l (a + 1) →
      V ≤ (Subgroup.zpowers γ).topologicalClosure := by
    intro γ hγ e h
    refine key γ hγ e (hle.trans ?_)
    have hm : γ ^ (l - 1) ∈ KStar.TotallyRealRoots.princ l a := by
      refine hle (Subgroup.mem_inf.2 ⟨V.pow_mem hγ _, ?_⟩)
      rw [KStar.TotallyRealRoots.princ_one_eq_ker, MonoidHom.mem_ker, map_pow, ZMod.units_pow_card_sub_one_eq_one]
    refine KStar.TotallyRealRoots.princ_le_of_isClosed (u := γ ^ (l - 1)) (by omega) (fun h => by have := h2 h; omega)
      (Subgroup.isClosed_topologicalClosure _)
      (Subgroup.le_topologicalClosure _ (Subgroup.npow_mem_zpowers γ _)) ?_
    exact emultiplicity_eq_coe.2 ⟨KStar.TotallyRealRoots.mem_princ.1 hm, fun h' => h (KStar.TotallyRealRoots.mem_princ.2 h')⟩
  by_cases hga : g ^ (l - 1) ∈ KStar.TotallyRealRoots.princ l (a + 1)
  · refine ⟨g * u, V.mul_mem hg hu.1, fin _ (V.mul_mem hg hu.1) ?_ ?_⟩
    · have : u ∈ (KStar.TotallyRealRoots.red l).ker := by
        rw [← KStar.TotallyRealRoots.princ_one_eq_ker]
        exact (Subgroup.mem_inf.1 hu).2
      rw [map_mul, MonoidHom.mem_ker.1 this, mul_one]
    · intro h
      rw [mul_pow] at h
      have h3 := (mul_mem_cancel_left hga).1 h
      have h4 := eg_pow_mem (by omega) (hle hu)
      have h5 : u ^ l = u ^ (l - 1) * u := by
        rw [← pow_succ, Nat.sub_add_cancel hp.one_le]
      rw [h5] at h4
      exact hua ((mul_mem_cancel_left h3).1 h4)
  · exact ⟨g, hg, fin g hg rfl hga⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.FunRepMem
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

theorem UpperTheory.V.Kum.funRepMem :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (N : ℕ) (U : Subgroup (G F Ω)) [U.Normal] (R M : Type) [CommRing R] [AddCommGroup M] [Module R M], (∀ g, ∀ φ ∈ XDual N U R M, funRep R M U g φ ∈ XDual N U R M) ∧ (∀ g ∈ U, ∀ φ ∈ XDual N U R M, funRep R M U g φ = φ) ∧
    ∀ (ρ : Representation R (G F Ω) M) (φ : U → M), φ ∈ EqHom N U ρ ↔ φ ∈ XDual N U R M ∧ ∀ g u, ρ g (funRep R M U g φ u) = φ u := by
  intro F Ω _ _ _ _ _ N U _ R M _ _ _
  have hf : ∀ (g : G F Ω) (φ : U → M) (u : U), funRep R M U g φ u = φ (UpperTheory.V.Base.conjHom U g u) := fun _ _ _ => rfl
  have hc : ∀ (g : G F Ω) (u : U), (UpperTheory.V.Base.conjHom U g u).1 = g⁻¹ * u.1 * g := fun _ _ => rfl
  refine ⟨fun g φ hφ => ?_, fun g hg φ hφ => ?_, fun ρ φ => ?_⟩
  · have h : IsLift (RingEquiv.refl F) g.toRingEquiv := fun x => g.commutes x
    have e1 : ∀ x : G F Ω, conjGal h x = g⁻¹ * x * g := fun _ => rfl
    have hA : ∀ (A : ValuationSubring Ω) x, g.toRingEquiv x ∈ A ↔ x ∈ A.comap g.toRingEquiv.toRingHom :=
      fun _ _ => Iff.rfl
    obtain ⟨h1, h2, h3, h4⟩ := hφ
    refine ⟨h1.comp_continuous (continuous_conjHom U g), fun a b => ?_, fun A u hu => ?_, fun A hN u hu => ?_⟩
    · rw [hf, hf, hf, map_mul, h2]
    · rw [hf]
      refine h3 (A.comap g.toRingEquiv.toRingHom) _ ?_
      rw [hc, ← e1]
      exact conjGal_mem_Ine h (hA A) hu
    · rw [hf]
      refine h4 (A.comap g.toRingEquiv.toRingHom) ?_ _ ?_
      · rw [← val_lt_one (hA A), map_natCast]
        exact hN
      · rw [hc, ← e1]
        exact conjGal_mem_Dec h (hA A) hu
  · funext u
    have e : (⟨g, hg⟩ : U) * UpperTheory.V.Base.conjHom U g u = u * ⟨g, hg⟩ :=
      Subtype.ext (by simp [hc, mul_assoc])
    have e2 := congrArg φ e
    rw [hφ.2.1, hφ.2.1, add_comm] at e2
    rw [hf]
    exact add_right_cancel e2
  · unfold EqHom
    rw [Submodule.mem_inf, Submodule.mem_iInf]
    refine and_congr_right fun _ => forall_congr' fun g => ⟨fun h u => ?_, fun h u u' hu => ?_⟩
    · rw [hf]
      refine (h _ u fun x => ?_).symm
      show u.1 (g x) = g (g.symm (u.1 (g x)))
      rw [g.apply_symm_apply]
    · have e : UpperTheory.V.Base.conjHom U g u' = u := Subtype.ext (AlgEquiv.ext fun x => by
        show g.symm (u'.1 (g x)) = u.1 x
        exact g.symm_apply_eq.2 (hu x))
      rw [← h u', hf, e]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Imports
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

theorem UpperTheory.V.Kum.h90 :
    ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (f : G K Ω → Ω), IsLocallyConstant f → (∀ g, f g ≠ 0) → (∀ g h, f (g * h) = f g * g (f h)) → ∃ β : Ω, β ≠ 0 ∧ ∀ g : G K Ω, g β = f g * β :=
  _root_.UpperTheory.Reformulated.B.HilbertNinetyCapelliIdentities.h90
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.RadConj
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

theorem UpperTheory.V.Kum.radConj :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (U : Subgroup (G F Ω)) (n : ℕ) [NeZero n] (ζ β : Ω) (σ : Ω ≃+* Ω) (k : ZMod n) (φ φ' : U → ZMod n), ζ ^ n = 1 → σ ζ = ζ ^ k.val → IsRad ζ U φ β →
    (∀ u' : U, ∃ u : U, (∀ x, u'.1 (σ x) = σ (u.1 x)) ∧ φ' u' = k * φ u) → IsRad ζ U φ' (σ β) := by
  intro F Ω _ _ _ _ _ U n _ ζ β σ k φ φ' hζ hσ hβ h
  refine ⟨fun h0 => hβ.1 (σ.injective (by rw [h0, map_zero])), fun u' => ?_⟩
  obtain ⟨u, hu, hφ⟩ := h u'
  rw [hu β, hβ.2 u, map_mul, map_pow, hσ, hφ, ZMod.val_mul, ← pow_mul, ← pow_eq_pow_mod _ hζ]
end

