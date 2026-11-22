import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.OrdBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.Bundle0003
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.Bundle0003

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.AdmFin
section
open UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite TensorProduct

private theorem isMax_of_le {R : Type*} [CommRing R] (I : Ideal R) [IsArtinianRing (R ⧸ I)]
    (P : Ideal R) [hP : P.IsPrime] (h : I ≤ P) : P.IsMaximal := by
  have h1 : (P.map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  have h2 : (P.map (Ideal.Quotient.mk I)).IsMaximal := IsArtinianRing.isMaximal_of_isPrime _
  have h3 := Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    (K := P.map (Ideal.Quotient.mk I))
  rwa [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
    Ideal.mk_ker, sup_eq_left.2 h] at h3

private theorem art_pow {R : Type*} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    [IsArtinianRing (R ⧸ I)] (k : ℕ) : IsArtinianRing (R ⧸ I ^ k) := by
  rw [isArtinianRing_iff_krullDimLE_zero, Ring.krullDimLE_zero_iff]
  intro p hp
  have h0 : I ^ k ≤ p.comap (Ideal.Quotient.mk (I ^ k)) := by
    intro x hx
    simp [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
  have h1 : (p.comap (Ideal.Quotient.mk (I ^ k))).IsMaximal :=
    isMax_of_le I _ (Ideal.IsPrime.le_of_pow_le h0)
  have h2 := Ideal.map_comap_of_surjective (Ideal.Quotient.mk (I ^ k)) Ideal.Quotient.mk_surjective p
  rcases Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk (I ^ k))
    Ideal.Quotient.mk_surjective h1 with h | h
  · exact absurd (h2 ▸ h) hp.ne_top
  · exact h2 ▸ h

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.tateH1FinitenessAtPlacesOver :
    ∀ {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R] [IsArtinianRing (R ⧸ I)] [Module.Finite R M], OrdAdm M I := by
  intro R _ M _ _ _ I _ _ _
  refine ⟨UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.completeFin I, fun k => ?_⟩
  haveI := art_pow I k
  rw [isFiniteLength_iff_isNoetherian_isArtinian]
  refine ⟨inferInstance, ?_⟩
  haveI : Module.Finite (R ⧸ I ^ k) (M ⧸ (I ^ k • ⊤ : Submodule R M)) :=
    Module.Finite.of_restrictScalars_finite R _ _
  exact isArtinian_of_surjective_algebraMap (R := R ⧸ I ^ k) Ideal.Quotient.mk_surjective
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.EigOrdInt
section
open UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite TensorProduct

private theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.eigOrdInt_inv
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] {I : Ideal R}
    {U e : Module.End R M} (h : IsOrdProj I U e) : ∃ V : Module.End R M, V * U * e = e := by
  have hm : ∀ x ∈ LinearMap.range e, U x ∈ LinearMap.range e := fun x hx => h.bij.mapsTo hx
  have hb : Function.Bijective (U.restrict hm) := by
    constructor
    · intro x y hxy
      exact Subtype.ext (h.bij.injOn x.2 y.2 (congrArg Subtype.val hxy))
    · intro y
      obtain ⟨x, hx, hxy⟩ := h.bij.surjOn y.2
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  let E := LinearEquiv.ofBijective _ hb
  let V : Module.End R M := (LinearMap.range e).subtype ∘ₗ E.symm.toLinearMap ∘ₗ e.rangeRestrict
  have hc : ∀ x, U (e x) = e (U x) := fun x => LinearMap.congr_fun h.comm.eq x
  have hV : ∀ z, e z = z → V (U z) = z := by
    intro z hz
    have : e.rangeRestrict (U z) = E ⟨z, z, hz⟩ := Subtype.ext (by
      show e (U z) = U z
      rw [← hc, hz])
    simp only [V, LinearMap.comp_apply, this]
    simp
  refine ⟨V, LinearMap.ext fun x => ?_⟩
  exact hV (e x) (LinearMap.congr_fun h.idem.eq x)

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.eigOrdInt :
    ∀ {O K : Type*} [CommRing O] [Field K] [Algebra O K] [IsLocalRing O] [IsAlgClosed K] {M : Type*} [AddCommGroup M] [Module O M] [Module.Finite O M] {U e : Module.End O M}, IsOrdProj (IsLocalRing.maximalIdeal O) U e → LinearMap.range (e.baseChange K) = ⨆ μ ∈ {μ : K | μ ≠ 0 ∧ IsIntegral O μ ∧ IsIntegral O μ⁻¹}, Module.End.maxGenEigenspace (U.baseChange K) μ := by
  intro O K _ _ _ _ _ M _ _ _ U e h
  refine UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.eigSum (U.baseChange K) (e.baseChange K) _ ?_ ?_ ?_ ?_
  · show _ * _ = _
    rw [← LinearMap.baseChange_mul, h.idem.eq]
  · show _ * _ = _ * _
    rw [← LinearMap.baseChange_mul, ← LinearMap.baseChange_mul, h.comm.eq]
  · intro μ y hy he hU
    obtain ⟨V, hV⟩ := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.eigOrdInt_inv h
    exact UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.eigUnitInt U V e hV μ y hy he hU
  · rintro μ y hy he hU ⟨h0, -, hi⟩
    obtain ⟨n, hn⟩ := h.nil 1
    have hp : ∀ k : ℕ, (U ^ k).baseChange K y = μ ^ k • y := by
      intro k
      induction k with
      | zero => rw [pow_zero, pow_zero, LinearMap.baseChange_one, one_smul, Module.End.one_apply]
      | succ k ih =>
        rw [pow_succ, LinearMap.baseChange_mul, Module.End.mul_apply, hU, map_smul, ih, smul_smul,
          pow_succ']
    refine UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.eigNilInt (U ^ n * (1 - e)) ?_ (μ ^ n) y hy ?_ (pow_ne_zero n h0) ?_
    · rintro _ ⟨x, rfl⟩
      have := hn x
      rw [pow_one] at this
      exact this
    · rw [LinearMap.baseChange_mul, Module.End.mul_apply, LinearMap.baseChange_sub,
        LinearMap.baseChange_one, LinearMap.sub_apply, he, sub_zero, Module.End.one_apply, hp]
    · rw [← inv_pow]
      exact hi.pow n
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.HeckeRestr
section
open IsLocalRing UpperTheory.V.Hi

private theorem restr_pow {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] {Y : Submodule A M}
    {t : Module.End A Y} {φ : Module.End A M} (h : Restr t φ) (n : ℕ) : Restr (t ^ n) (φ ^ n) := by
  induction n with
  | zero => intro y; simp
  | succ n ih => intro y; rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, h]

private theorem mem_locPart_iff {A M ι : Type} [CommRing A] [IsLocalRing A] [AddCommGroup M] [Module A M]
    {Y : Submodule A M} {op : ι → Module.End A M} {a : ι → A} (u : ι → Module.End A Y)
    (hu : ∀ i, Restr (u i) (op i - algebraMap A _ (a i))) (y : Y) :
    (y : M) ∈ locPart Y op a ↔
      ∀ (i : ι) (k : ℕ), ∃ n : ℕ, (u i ^ n) y ∈ maximalIdeal A ^ k • (⊤ : Submodule A Y) := by
  have hmono : ∀ (i : ι) (k : ℕ), Monotone fun n : ℕ =>
      (maximalIdeal A ^ k • Y).comap ((op i - algebraMap A _ (a i)) ^ n) := by
    intro i k
    refine monotone_nat_of_le_succ fun n x hx => ?_
    rw [Submodule.mem_comap] at hx ⊢
    rw [pow_succ', Module.End.mul_apply]
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro r hr z hz
      rw [map_smul]
      refine Submodule.smul_mem_smul hr ?_
      rw [← hu i ⟨z, hz⟩]
      exact (u i ⟨z, hz⟩).2
    · intro b c hb hc
      rw [map_add]
      exact Submodule.add_mem _ hb hc
  unfold locPart
  rw [Submodule.mem_inf, and_iff_right y.2]
  simp only [Submodule.mem_iInf]
  refine forall_congr' fun i => forall_congr' fun k => ?_
  rw [Submodule.mem_iSup_of_directed _ (hmono i k).directed_le]
  refine exists_congr fun n => ?_
  rw [Submodule.mem_comap, Submodule.mem_smul_top_iff, restr_pow (hu i) n y]

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.heckeRestr :
    ∀ (A M ι : Type) [CommRing A] [IsCNL A] [AddCommGroup M] [Module A M] (Y : Submodule A M) [Module.Finite A Y] (op : ι → Module.End A M) (a : ι → A), CommOn Y op → ∀ (T T' : Type) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (j : T →ₐ[A] Module.End A Y) (j' : T' →ₐ[A] Module.End A (locPart Y op a)), Function.Injective j → j.range = heckeAlg Y op → Function.Injective j' → j'.range = heckeAlg (locPart Y op a) op → ∃ r : T →ₐ[A] T', Function.Surjective r ∧ (∀ (s : T) (y : locPart Y op a), (j' (r s) y : M) = j s ⟨y, y.2.1⟩) ∧ ∀ (R : Type) [CommRing R] [IsLocalRing R] (x : T →+* R), (∀ c ∈ maximalIdeal A, x (algebraMap A T c) ∈ maximalIdeal R) → (∀ i s, Restr (j s) (op i) → x s - x (algebraMap A T (a i)) ∈ maximalIdeal R) → locPart Y op a ≠ ⊥ ∧ ∃ x' : T' →+* R, x'.comp (r : T →+* T') = x := by
  intro A M ι _ _ _ _ Y _ op a hC T T' _ _ _ _ j j' hj hjr hj' hjr'
  have ht0 : ∀ i, ∃ s : T, Restr (j s) (op i) := by
    intro i
    have h : (op i).restrict (hC.1 i) ∈ j.range := by
      rw [hjr]
      exact Algebra.subset_adjoin ⟨i, fun _ => rfl⟩
    obtain ⟨s, hs⟩ := h
    refine ⟨s, fun y => ?_⟩
    have hs' : j s = (op i).restrict (hC.1 i) := hs
    rw [hs']
    rfl
  choose t ht using ht0
  have hset : ∀ (Z : Submodule A M) (ρ : T →ₐ[A] Module.End A Z), (∀ i, Restr (ρ (t i)) (op i)) →
      (Algebra.adjoin A (Set.range t)).map ρ = heckeAlg Z op := by
    intro Z ρ hρ
    rw [AlgHom.map_adjoin, heckeAlg]
    congr 1
    ext φ
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, hρ i⟩
    · rintro ⟨i, hi⟩
      exact ⟨t i, ⟨i, rfl⟩, LinearMap.ext fun y => Subtype.ext ((hρ i y).trans (hi y).symm)⟩
  have hgen : Algebra.adjoin A (Set.range t) = ⊤ := by
    refine eq_top_iff.2 fun s _ => ?_
    have h : j s ∈ (Algebra.adjoin A (Set.range t)).map j := by
      rw [hset Y j ht, ← hjr]
      exact ⟨s, rfl⟩
    obtain ⟨s', hs', h'⟩ := h
    rwa [← hj h']
  haveI : IsNoetherian A (Module.End A Y) := isNoetherian_linearMap A Y Y
  haveI : Module.Finite A T := Module.Finite.of_injective j.toLinearMap hj
  obtain ⟨e, he, hnil, h1e, -, -⟩ := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.locAbs A T ι t a hgen
  have hI : ∀ μ ∈ (maximalIdeal A).map (algebraMap A T), ∀ y,
      j μ y ∈ maximalIdeal A • (⊤ : Submodule A Y) := by
    intro μ hμ
    refine Submodule.span_induction (p := fun μ _ => ∀ y,
      j μ y ∈ maximalIdeal A • (⊤ : Submodule A Y)) ?_ ?_ ?_ ?_ hμ
    · rintro _ ⟨c, hc, rfl⟩ y
      rw [AlgHom.commutes, Module.algebraMap_end_apply]
      exact Submodule.smul_mem_smul hc Submodule.mem_top
    · intro y; simp
    · intro b c _ _ hb hc y
      rw [map_add, LinearMap.add_apply]
      exact Submodule.add_mem _ (hb y) (hc y)
    · intro b c _ hc y
      rw [smul_eq_mul, mul_comm, map_mul, Module.End.mul_apply]
      exact hc _
  have hL : ∀ y : Y, (y : M) ∈ locPart Y op a ↔ j e y = y := by
    intro y
    rw [mem_locPart_iff (fun i => j (t i - algebraMap A T (a i)))]
    · exact (UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.locChar A Y T ι (j : T →+* Module.End A Y) _ _ e hI he hnil h1e y).symm
    · intro i z
      rw [map_sub, AlgHom.commutes, LinearMap.sub_apply, LinearMap.sub_apply, Submodule.coe_sub, ht i z]
      rfl
  have hpres : ∀ (s : T) (y : locPart Y op a), (j s ⟨y, y.2.1⟩ : M) ∈ locPart Y op a := by
    intro s y
    rw [hL, ← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply,
      (hL ⟨y, y.2.1⟩).1 y.2]
  have he' : ∀ y : Y, (j e y : M) ∈ locPart Y op a := by
    intro y
    rw [hL, ← Module.End.mul_apply, ← map_mul, he.eq]
  let ρ0 : T → Module.End A (locPart Y op a) := fun s =>
    LinearMap.codRestrict _ (Y.subtype ∘ₗ j s ∘ₗ Submodule.inclusion inf_le_left) (hpres s)
  have hρ0 : ∀ s y, (ρ0 s y : M) = j s ⟨y, y.2.1⟩ := fun _ _ => rfl
  let ρ : T →ₐ[A] Module.End A (locPart Y op a) :=
    { toFun := ρ0
      map_one' := by ext y; rw [hρ0, map_one]; rfl
      map_mul' := fun s s' => by ext y; rw [hρ0, map_mul]; rfl
      map_zero' := by ext y; rw [hρ0, map_zero]; rfl
      map_add' := fun s s' => by ext y; rw [hρ0, map_add]; rfl
      commutes' := fun c => by ext y; rw [hρ0, AlgHom.commutes]; rfl }
  have hρ : ∀ s y, (ρ s y : M) = j s ⟨y, y.2.1⟩ := fun _ _ => rfl
  have hrange : ρ.range = j'.range := by
    rw [hjr', ← hset _ ρ (fun i y => by rw [hρ, ht i]), hgen, Algebra.map_top]
  let r : T →ₐ[A] T' := (AlgEquiv.ofInjective j' hj').symm.toAlgHom.comp
    (ρ.codRestrict j'.range fun s => hrange ▸ ⟨s, rfl⟩)
  have hr : ∀ s, j' (r s) = ρ s := fun s =>
    congrArg Subtype.val ((AlgEquiv.ofInjective j' hj').apply_symm_apply
      (ρ.codRestrict j'.range (fun s => hrange ▸ ⟨s, rfl⟩) s))
  have hsurj : Function.Surjective r := by
    intro s'
    have h : j' s' ∈ ρ.range := hrange ▸ ⟨s', rfl⟩
    obtain ⟨s, hs⟩ := h
    exact ⟨s, hj' ((hr s).trans hs)⟩
  refine ⟨r, hsurj, fun s y => by rw [hr, hρ], fun R _ _ x hx hxt => ?_⟩
  have hle : (maximalIdeal A).map (algebraMap A T) ⊔
      Ideal.span (Set.range fun i => t i - algebraMap A T (a i)) ≤ (maximalIdeal R).comap x := by
    refine sup_le (Ideal.map_le_iff_le_comap.2 fun c hc => hx c hc) (Ideal.span_le.2 ?_)
    rintro _ ⟨i, rfl⟩
    have := hxt i (t i) (ht i)
    rwa [← map_sub] at this
  have hxe : x e = 1 := by
    have h1 : 1 - x e ∈ maximalIdeal R := by
      have := hle h1e
      rwa [Ideal.mem_comap, map_sub, map_one] at this
    have h2 : IsUnit (x e) := by
      have := isUnit_one_sub_self_of_mem_nonunits _ h1
      rwa [sub_sub_cancel] at this
    exact h2.mul_left_cancel (by rw [← map_mul, he.eq, mul_one])
  refine ⟨fun hb => ?_, ?_⟩
  · have h0 : e = 0 := by
      refine hj ?_
      rw [map_zero]
      ext y
      have := he' y
      rw [hb] at this
      exact this
    rw [h0, map_zero] at hxe
    exact zero_ne_one hxe
  · have hker : RingHom.ker (r : T →+* T') ≤ RingHom.ker x := by
      intro s hs
      have hs0 : r s = 0 := hs
      have h0 : s * e = 0 := by
        refine hj ?_
        ext y
        have := hρ s ⟨_, he' y⟩
        rw [← hr, hs0, map_zero] at this
        rw [map_mul, map_zero]
        exact this.symm
      rw [RingHom.mem_ker, ← mul_one (x s), ← hxe, ← map_mul, h0, map_zero]
    exact ⟨(r : T →+* T').liftOfSurjective hsurj ⟨x, hker⟩,
      RingHom.liftOfRightInverse_comp _ _ _ _⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.OneVar
section
open IsLocalRing

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.oneVar :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [Field K] (ι : O →+* K), Function.Injective ι → ∀ (g : PowerSeries O) (Z : Set K), Z.Infinite → (∀ z ∈ Z, ∃ y : PowerSeries O →+* K, (∀ a, y (PowerSeries.C a) = ι a) ∧ y PowerSeries.X = z ∧ y g = 0) → g = 0 := by
  intro O K _ _ _ _ _ ι hι g Z hZ h
  by_contra hg
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨m, P, U, -, hP, -, hU, hfac⟩ := UpperTheory.V.abelian₂.weier O ϖ hϖ g hg
  have hmon : (P.map ι).Monic := hP.monic.map ι
  have hϖ0 : ι ϖ ≠ 0 := fun h0 => hϖ.ne_zero (hι (by rw [h0, map_zero]))
  refine hmon.ne_zero (Polynomial.eq_zero_of_infinite_isRoot _ (hZ.mono ?_))
  intro z hz
  obtain ⟨y, hyC, hyX, hy0⟩ := h z hz
  have hyP : y (P : PowerSeries O) = (P.map ι).eval z := by
    have e : y.comp Polynomial.coeToPowerSeries.ringHom = Polynomial.eval₂RingHom ι z := by
      apply Polynomial.ringHom_ext
      · intro a
        simp [hyC]
      · simp [hyX]
    have := RingHom.congr_fun e P
    simpa [Polynomial.eval_map] using this
  rw [hfac, map_mul, map_mul, map_pow, hyC, hyP] at hy0
  have hyU : y U ≠ 0 := (hU.map y).ne_zero
  show (P.map ι).IsRoot z
  rcases mul_eq_zero.1 hy0 with h1 | h1
  · rcases mul_eq_zero.1 h1 with h2 | h2
    · exact absurd h2 (pow_ne_zero m hϖ0)
    · exact h2
  · exact absurd h1 hyU
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.PointEig
section
open UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite TensorProduct

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.pointEig :
    ∀ {Λ T K M : Type*} [CommRing Λ] [CommRing T] [Algebra Λ T] [Field K] [Algebra Λ K] [AddCommGroup M] [Module Λ M] [Module T M] [IsScalarTower Λ T M] [Module.Finite Λ M] [FaithfulSMul T M] (x : T →ₐ[Λ] K), ∃ y : K ⊗[Λ] M, y ≠ 0 ∧ ∀ t : T, (Algebra.lsmul Λ Λ M t).baseChange K y = x t • y := by
  intro Λ T K M _ _ _ _ _ _ _ _ _ _ _ x
  letI : Algebra T K := x.toRingHom.toAlgebra
  haveI : IsScalarTower Λ T K := IsScalarTower.of_algebraMap_eq fun r => (x.commutes r).symm
  haveI : Module.Finite T M := Module.Finite.of_restrictScalars_finite Λ T M
  have hne : Nontrivial (K ⊗[T] M) := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.fibreNe
  let φ : K ⊗[Λ] M →ₗ[K] K ⊗[T] M := TensorProduct.AlgebraTensorModule.lift
    ((LinearMap.restrictScalarsₗ Λ T M (K ⊗[T] M) K).comp
      (TensorProduct.AlgebraTensorModule.mk T K K M))
  have hφt : ∀ (k : K) (m : M), φ (k ⊗ₜ[Λ] m) = k ⊗ₜ[T] m := by
    intro k m
    simp [φ]
  let A : T → Module.End K (K ⊗[Λ] M) := fun t => (Algebra.lsmul Λ Λ M t).baseChange K
  have hA : ∀ (t : T) (k : K) (m : M), A t (k ⊗ₜ[Λ] m) = k ⊗ₜ[Λ] (t • m) := by
    intro t k m
    simp [A]
  have hc : ∀ s t, Commute (A s) (A t) := by
    intro s t
    show A s * A t = A t * A s
    apply LinearMap.ext
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul k m =>
      rw [Module.End.mul_apply, Module.End.mul_apply, hA, hA, hA, hA, smul_comm]
    | add a b ha hb =>
      rw [Module.End.mul_apply, Module.End.mul_apply] at ha hb ⊢
      rw [map_add, map_add, ha, hb, map_add, map_add]
  have hφA : ∀ t y, φ (A t y) = x t • φ y := by
    intro t y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul k m =>
      rw [hA, hφt, hφt, ← TensorProduct.smul_tmul, TensorProduct.smul_tmul']
      congr 1
    | add a b ha hb =>
      rw [map_add, map_add, ha, hb, map_add, smul_add]
  have hφ0 : φ ≠ 0 := by
    intro h0
    have hall : ∀ p : K ⊗[T] M, p = 0 := by
      intro p
      induction p using TensorProduct.induction_on with
      | zero => rfl
      | tmul k m => rw [← hφt, h0, LinearMap.zero_apply]
      | add a b ha hb => rw [ha, hb, add_zero]
    obtain ⟨p, hp⟩ := exists_ne (0 : K ⊗[T] M)
    exact hp (hall p)
  exact UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.eigOfQuot A hc (fun t => x t) φ hφ0 hφA
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.QuotOfEig
section
open UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite TensorProduct

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.quotOfEig :
    ∀ {K Y ι : Type*} [Field K] [AddCommGroup Y] [Module K Y] [FiniteDimensional K Y] (A : ι → Module.End K Y), (∀ i j, Commute (A i) (A j)) → ∀ (x : ι → K) (y : Y), y ≠ 0 → (∀ i, A i y = x i • y) → ∃ φ : Module.Dual K Y, φ ≠ 0 ∧ ∀ i z, φ (A i z) = x i * φ z := by
  intro K Y ι _ _ _ _ A hA x y hy hAy
  have hc : ∀ i j, Commute (A i).dualMap (A j).dualMap := by
    intro i j
    show (A i).dualMap * (A j).dualMap = (A j).dualMap * (A i).dualMap
    refine LinearMap.ext fun ψ => LinearMap.ext fun z => ?_
    have h := LinearMap.congr_fun (hA j i).eq z
    simp only [Module.End.mul_apply] at h
    simp only [Module.End.mul_apply, LinearMap.dualMap_apply]
    rw [h]
  have hne : Module.Dual.eval K Y y ≠ 0 := by
    intro h0
    apply hy
    refine (Module.forall_dual_apply_eq_zero_iff K y).mp ?_
    intro ψ
    exact LinearMap.congr_fun h0 ψ
  obtain ⟨ψ, hψ, hψA⟩ := eigOfQuot (fun i => (A i).dualMap) hc x (Module.Dual.eval K Y y) hne (by
    intro i ψ
    simp [LinearMap.dualMap_apply, hAy])
  refine ⟨ψ, hψ, fun i z => ?_⟩
  have := LinearMap.congr_fun (hψA i) z
  simpa [LinearMap.dualMap_apply] using this
end

