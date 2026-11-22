import Mathlib

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsAverage
section
namespace UpperTheory.Reformulated.B.ExistsAverage

private theorem exists_op {K : Type*} {M : Type*} [Group K] [AddCommGroup M] [Module ℂ M]
    (ρ : K →* Module.End ℂ M) (H : Subgroup K) [H.Normal] [H.FiniteIndex] :
    ∃ A : M →ₗ[ℂ] M,
      (∀ m, (∀ h ∈ H, ρ h m = m) → ∀ k, ρ k (A m) = A m) ∧
      (∀ m, (∀ h ∈ H, ρ h m = m) → ∀ k, A (ρ k m) = A m) ∧
      (∀ m, (∀ k, ρ k m = m) → A m = m) ∧
      (∀ m, m - A m ∈ Submodule.span ℂ {x : M | ∃ k y, x = y - ρ k y}) := by
  classical
  haveI : Fintype (K ⧸ H) := Fintype.ofFinite _
  have hc : ((Fintype.card (K ⧸ H) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have key : ∀ m, (∀ h ∈ H, ρ h m = m) → ∀ g : K, ρ g m = ρ ((g : K ⧸ H).out) m := by
    intro m hm g
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H g
    rw [hh, map_mul, Module.End.mul_apply, hm h h.2]
  have hA : ∀ m, (((Fintype.card (K ⧸ H) : ℕ) : ℂ)⁻¹ • ∑ q : K ⧸ H, (ρ q.out : M →ₗ[ℂ] M)) m
      = ((Fintype.card (K ⧸ H) : ℕ) : ℂ)⁻¹ • ∑ q : K ⧸ H, ρ q.out m := by
    intro m
    rw [LinearMap.smul_apply, LinearMap.sum_apply]
  have hconst : ∀ m : M, ((Fintype.card (K ⧸ H) : ℕ) : ℂ)⁻¹ • ∑ _q : K ⧸ H, m = m := by
    intro m
    rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
      inv_mul_cancel₀ hc, one_smul]
  refine ⟨((Fintype.card (K ⧸ H) : ℕ) : ℂ)⁻¹ • ∑ q : K ⧸ H, (ρ q.out : M →ₗ[ℂ] M),
    ?_, ?_, ?_, ?_⟩
  · intro m hm k
    rw [hA, map_smul, map_sum]
    congr 1
    refine Fintype.sum_equiv (Equiv.mulLeft (k : K ⧸ H)) _ _ fun q => ?_
    rw [← Module.End.mul_apply, ← map_mul, key m hm]
    simp
  · intro m hm k
    rw [hA, hA]
    congr 1
    refine Fintype.sum_equiv (Equiv.mulRight (k : K ⧸ H)) _ _ fun q => ?_
    rw [← Module.End.mul_apply, ← map_mul, key m hm]
    simp
  · intro m hm
    rw [hA]
    simp only [hm]
    exact hconst m
  · intro m
    rw [hA]
    nth_rewrite 1 [← hconst m]
    rw [← smul_sub, ← Finset.sum_sub_distrib]
    exact Submodule.smul_mem _ _
      (Submodule.sum_mem _ fun q _ => Submodule.subset_span ⟨_, _, rfl⟩)

private theorem exists_sub {K : Type*} {M : Type*} [Group K] [AddCommGroup M] [Module ℂ M]
    [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
    (ρ : K →* Module.End ℂ M) (hs : ∀ m : M, IsOpen {k : K | ρ k m = m}) (m : M) :
    ∃ H : Subgroup K, H.Normal ∧ H.FiniteIndex ∧ ∀ h ∈ H, ρ h m = m := by
  let S : Subgroup K :=
    { carrier := {k : K | ρ k m = m}
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at *
        rw [map_mul, Module.End.mul_apply, hb, ha]
      one_mem' := by simp
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at *
        nth_rewrite 1 [← ha]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  haveI : Finite (K ⧸ S) := Subgroup.quotient_finite_of_isOpen S (hs m)
  haveI : S.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  exact ⟨S.normalCore, inferInstance, inferInstance, fun h hh => S.normalCore_le hh⟩

theorem exists_avg {K : Type*} {M : Type*} [Group K] [AddCommGroup M] [Module ℂ M]
    [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
    (ρ : K →* Module.End ℂ M) (hs : ∀ m : M, IsOpen {k : K | ρ k m = m}) :
    ∃ P : M →ₗ[ℂ] M, (∀ (m : M) (k : K), ρ k (P m) = P m) ∧
      (∀ m : M, (∀ k : K, ρ k m = m) → P m = m) ∧
      ∀ T : M →ₗ[ℂ] M, (∀ (k : K) (m : M), T (ρ k m) = ρ k (T m)) →
        ∀ m : M, T (P m) = P (T m) := by
  set N : Submodule ℂ M := Submodule.span ℂ {x : M | ∃ k y, x = y - ρ k y} with hN
  have hdis : ∀ x ∈ N, (∀ k, ρ k x = x) → x = 0 := by
    intro x hx hfix
    have : ∃ H : Subgroup K, H.Normal ∧ H.FiniteIndex ∧ ∀ A : M →ₗ[ℂ] M,
        (∀ m, (∀ h ∈ H, ρ h m = m) → ∀ k, A (ρ k m) = A m) → A x = 0 := by
      clear hfix
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨k, y, rfl⟩ := hx
        obtain ⟨H, h1, h2, h3⟩ := exists_sub ρ hs y
        exact ⟨H, h1, h2, fun A hA => by rw [map_sub, hA y h3, sub_self]⟩
      | zero => exact ⟨⊤, inferInstance, inferInstance, fun A _ => map_zero A⟩
      | add x y _ _ hx hy =>
        obtain ⟨H, h1, h2, h3⟩ := hx
        obtain ⟨H', h1', h2', h3'⟩ := hy
        refine ⟨H ⊓ H', inferInstance, inferInstance, fun A hA => ?_⟩
        rw [map_add, h3 A fun m hm => hA m fun h hh => hm h hh.1,
          h3' A fun m hm => hA m fun h hh => hm h hh.2, add_zero]
      | smul c x _ hx =>
        obtain ⟨H, h1, h2, h3⟩ := hx
        exact ⟨H, h1, h2, fun A hA => by rw [map_smul, h3 A hA, smul_zero]⟩
    obtain ⟨H, h1, h2, h3⟩ := this
    obtain ⟨A, -, a2, a3, -⟩ := exists_op ρ H
    rw [← a3 x hfix]
    exact h3 A a2
  have hex : ∀ m : M, ∃ p : M, (∀ k, ρ k p = p) ∧ m - p ∈ N := by
    intro m
    obtain ⟨H, h1, h2, h3⟩ := exists_sub ρ hs m
    obtain ⟨A, a1, -, -, a4⟩ := exists_op ρ H
    exact ⟨A m, a1 m h3, a4 m⟩
  choose f hf1 hf2 using hex
  have huniq : ∀ m p : M, (∀ k, ρ k p = p) → m - p ∈ N → f m = p := by
    intro m p hp hm
    rw [← sub_eq_zero]
    refine hdis _ ?_ fun k => by rw [map_sub, hf1, hp]
    have := N.sub_mem hm (hf2 m)
    rwa [sub_sub_sub_cancel_left] at this
  refine ⟨{ toFun := f, map_add' := ?_, map_smul' := ?_ }, hf1, ?_, ?_⟩
  · intro x y
    refine huniq _ _ (fun k => by rw [map_add, hf1, hf1]) ?_
    rw [add_sub_add_comm]
    exact N.add_mem (hf2 x) (hf2 y)
  · intro c x
    refine huniq _ _ (fun k => by rw [map_smul, hf1]) ?_
    rw [RingHom.id_apply, ← smul_sub]
    exact N.smul_mem c (hf2 x)
  · intro m hm
    exact huniq m m hm (by rw [sub_self]; exact N.zero_mem)
  · intro T hT m
    refine (huniq (T m) (T (f m)) (fun k => by rw [← hT, hf1]) ?_).symm
    rw [← map_sub]
    have hle : N ≤ N.comap T := by
      rw [hN, Submodule.span_le]
      rintro _ ⟨k, y, rfl⟩
      exact Submodule.subset_span ⟨k, T y, by rw [map_sub, hT]⟩
    exact hle (hf2 m)

end UpperTheory.Reformulated.B.ExistsAverage
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsBasisOfPid
section
theorem UpperTheory.Reformulated.B.Qi33.aux1.{u_1, u_2} :
    ∀ {R : Type u_2} [inst : CommRing R] {W : Type u_1} [inst_1 : AddCommGroup W] [inst_2 : _root_.Module R W]
      (S : Submonoid R) (L : Submodule R W) {x y : W},
      x ∈ {x : W | ∃ s ∈ S, s • x ∈ L} → y ∈ {x : W | ∃ s ∈ S, s • x ∈ L} → x + y ∈ {x : W | ∃ s ∈ S, s • x ∈ L} := by
  intro R _ W _ _ S L x y hx hy
  obtain ⟨s, hs, hx⟩ := hx
  obtain ⟨t, ht, hy⟩ := hy
  refine ⟨s * t, S.mul_mem hs ht, ?_⟩
  rw [smul_add]
  refine L.add_mem ?_ ?_
  · rw [mul_comm, mul_smul]
    exact L.smul_mem t hx
  · rw [mul_smul]
    exact L.smul_mem s hy

theorem UpperTheory.Reformulated.B.Qi33.aux2.{u_1, u_2} :
    ∀ {R : Type u_1} [inst : CommRing R] {W : Type u_2} [inst_1 : AddCommGroup W] [inst_2 : _root_.Module R W]
      (S : Submonoid R) (L : Submodule R W), ∃ s ∈ S, s • (0 : W) ∈ L := by
  intro R _ W _ _ S L
  exact ⟨1, S.one_mem, by simp⟩

theorem UpperTheory.Reformulated.B.Qi33.aux3.{u_1, u_2} :
    ∀ {R : Type u_2} [inst : CommRing R] {W : Type u_1} [inst_1 : AddCommGroup W] [inst_2 : _root_.Module R W]
      (S : Submonoid R) (L : Submodule R W) (r : R) {x : W},
      x ∈ {x : W | ∃ s ∈ S, s • x ∈ L} → r • x ∈ {x : W | ∃ s ∈ S, s • x ∈ L} := by
  intro R _ W _ _ S L r x hx
  obtain ⟨s, hs, hx⟩ := hx
  refine ⟨s, hs, ?_⟩
  rw [smul_comm]
  exact L.smul_mem r hx

noncomputable def UpperTheory.Reformulated.B.Qi33.locS.{u_1, u_4} :
    {R : Type u_1} →
      [inst : CommRing R] →
        {W : Type u_4} →
          [inst_1 : AddCommGroup W] → [inst_2 : _root_.Module R W] → Submonoid R → Submodule R W → Submodule R W :=
    fun {R : Type u_1} [inst : CommRing R] {W : Type u_4} [inst_1 : AddCommGroup W] [inst_2 : _root_.Module R W]
        (S : Submonoid R) (L : Submodule R W) ↦
      { carrier := {x : W | ∃ s ∈ S, s • x ∈ L}, add_mem' := @UpperTheory.Reformulated.B.Qi33.aux1 R inst W inst_1 inst_2 S L,
        zero_mem' := UpperTheory.Reformulated.B.Qi33.aux2 S L, smul_mem' := UpperTheory.Reformulated.B.Qi33.aux3 S L : Submodule R W }

noncomputable def UpperTheory.Reformulated.B.Qi33.localization₂.{u_1, u_4} :
    {R : Type u_1} →
      [inst : CommRing R] →
        {W : Type u_4} →
          [inst_1 : AddCommGroup W] →
            [inst_2 : _root_.Module R W] → (p : Ideal R) → [p.IsPrime] → Submodule R W → Submodule R W :=
    fun {R : Type u_1} [CommRing R] {W : Type u_4} [AddCommGroup W] [_root_.Module R W] (p : Ideal R) [p.IsPrime]
        (L : Submodule R W) ↦
      UpperTheory.Reformulated.B.Qi33.locS p.primeCompl L

private theorem UpperTheory.Reformulated.B.Qi33.mem_locS_iff {R : Type*} [CommRing R] {W : Type*} [AddCommGroup W]
    [Module R W] (S : Submonoid R) (R' : Type*) [CommRing R'] [Algebra R R'] [IsLocalization S R']
    [Module R' W] [IsScalarTower R R' W] (L : Submodule R W) (x : W) :
    x ∈ UpperTheory.Reformulated.B.Qi33.locS S L ↔ x ∈ Submodule.span R' (L : Set W) := by
  rw [IsLocalization.mem_span_iff S, Submodule.span_eq]
  constructor
  · rintro ⟨s, hs, hx⟩
    refine ⟨s • x, hx, ⟨s, hs⟩, ?_⟩
    rw [← algebraMap_smul R' s x, smul_smul]
    have h := IsLocalization.mk'_spec R' (1 : R) (⟨s, hs⟩ : S)
    simp only [map_one] at h
    rw [h, one_smul]
  · rintro ⟨y, hy, z, rfl⟩
    refine ⟨z, z.2, ?_⟩
    rw [← algebraMap_smul R' (z : R), smul_smul]
    have h := IsLocalization.mk'_spec' R' (1 : R) z
    simp only [map_one] at h
    rw [h, one_smul]
    exact hy

private theorem UpperTheory.Reformulated.B.Qi33.exists_basis_of_pid {D K Z : Type} [CommRing D] [IsDomain D]
    [IsPrincipalIdealRing D] [Field K] [Algebra D K] [IsFractionRing D K] [AddCommGroup Z]
    [Module K Z] [Module D Z] [IsScalarTower D K Z] (M : Submodule D Z) (hM : M.FG)
    (hs : Submodule.span K (M : Set Z) = ⊤) :
    ∃ b : Module.Basis (Fin (Module.finrank K Z)) K Z, Submodule.span D (Set.range b) = M := by
  haveI : Module.Finite D M := Module.Finite.iff_fg.mpr hM
  haveI : Module.IsTorsionFree D Z := Module.IsTorsionFree.trans_faithfulSMul D K Z
  haveI : Module.Free D M := inferInstance
  let c := Module.finBasis D M
  let v : Fin (Module.finrank D M) → Z := fun i => (c i : Z)
  have hli : LinearIndependent D v := c.linearIndependent.map' M.subtype M.ker_subtype
  have hliK : LinearIndependent K v := (LinearIndependent.iff_fractionRing D K).mp hli
  have hsp : Submodule.span D (Set.range v) = M := by
    have h1 : Set.range v = M.subtype '' Set.range c := by
      rw [← Set.range_comp]; rfl
    rw [h1, ← Submodule.map_span, c.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hspK : ⊤ ≤ Submodule.span K (Set.range v) := by
    rw [← Submodule.span_span_of_tower D K (Set.range v), hsp, hs]
  let b0 := Module.Basis.mk hliK hspK
  have hn : Module.finrank K Z = Module.finrank D M := by
    simpa using Module.finrank_eq_card_basis b0
  refine ⟨b0.reindex (finCongr hn.symm), ?_⟩
  rw [Module.Basis.range_reindex, Module.Basis.coe_mk, hsp]

theorem UpperTheory.Reformulated.B.Qi33.exists_loc_basis :
    ∀ {K : Type} [inst : Field K] [NumberField K] [StarRing K] {Z : Type} [inst_3 : AddCommGroup Z]
      [inst_4 : _root_.Module K Z] [inst_5 : _root_.Module (NumberField.RingOfIntegers K) Z]
      [IsScalarTower (NumberField.RingOfIntegers K) K Z] [FiniteDimensional K Z]
      (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
      (A : Submodule (NumberField.RingOfIntegers K) Z),
      A.FG →
        Submodule.span K (↑A : Set Z) = ⊤ →
          ∃ (b : Module.Basis (Fin (Module.finrank K Z)) K Z),
            UpperTheory.Reformulated.B.Qi33.localization₂ w.asIdeal A =
              UpperTheory.Reformulated.B.Qi33.localization₂ w.asIdeal
                (Submodule.span (NumberField.RingOfIntegers K) (Set.range (⇑b : Fin (Module.finrank K Z) → Z))) := by
  intro K _ _ _ Z _ _ _ _ _ w A hA hsp
  let D := Localization.subalgebra.ofField K w.asIdeal.primeCompl
    (Ideal.primeCompl_le_nonZeroDivisors w.asIdeal)
  haveI hloc : IsLocalization w.asIdeal.primeCompl D :=
    Localization.subalgebra.isLocalization_ofField K _ _
  haveI : IsFractionRing D K := Localization.subalgebra.isFractionRing_ofField K _ _
  haveI : IsDiscreteValuationRing D :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      (NumberField.RingOfIntegers K) w.ne_bot D
  haveI : IsScalarTower (NumberField.RingOfIntegers K) D Z :=
    IsScalarTower.of_algebraMap_smul fun r z => algebraMap_smul K r z
  have hfg : (Submodule.span D (A : Set Z)).FG := by
    obtain ⟨t, rfl⟩ := hA
    exact ⟨t, (Submodule.span_span_of_tower _ _ _).symm⟩
  obtain ⟨b, hb⟩ := UpperTheory.Reformulated.B.Qi33.exists_basis_of_pid (D := D) (K := K) _ hfg
    (by rw [Submodule.span_span_of_tower, hsp])
  refine ⟨b, ?_⟩
  ext x
  unfold UpperTheory.Reformulated.B.Qi33.localization₂
  rw [UpperTheory.Reformulated.B.Qi33.mem_locS_iff _ D, UpperTheory.Reformulated.B.Qi33.mem_locS_iff _ D,
    Submodule.span_span_of_tower, hb]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsCharNeOne
section
open MeasureTheory WeakDual

namespace UpperTheory.Reformulated.B.CharactersSeparatePoints

private theorem comm_case {C A : Type*} [CommGroup C] [TopologicalSpace C] [CommCStarAlgebra A]
    (U : C →* A) (hU : ∀ h, star (U h) = U h⁻¹) (T : A) (hT : Continuous fun h => U h * T)
    {g : C} (hg : U g * T ≠ T) : ∃ χ : C →ₜ* Circle, χ g ≠ 1 := by
  have h1 : gelfandTransform ℂ A (U g * T) ≠ gelfandTransform ℂ A T :=
    fun h => hg ((gelfandTransform_isometry A).injective h)
  obtain ⟨φ, hφ⟩ := DFunLike.ne_iff.1 h1
  change φ (U g * T) ≠ φ T at hφ
  have hT0 : φ T ≠ 0 := by
    intro h0
    apply hφ
    rw [map_mul, h0, mul_zero]
  have hn : ∀ h, ‖φ (U h)‖ = 1 := by
    intro h
    have : star (φ (U h)) * φ (U h) = 1 := by
      rw [← map_star, ← map_mul, hU, ← map_mul, inv_mul_cancel, map_one, map_one]
    have h2 := congrArg norm this
    rw [norm_mul, norm_star, norm_one] at h2
    nlinarith [norm_nonneg (φ (U h))]
  have hc : Continuous fun h => φ (U h) := by
    have : (fun h => φ (U h)) = fun h => φ (U h * T) / φ T := by
      funext h
      rw [map_mul, mul_div_cancel_right₀ _ hT0]
    rw [this]
    exact ((map_continuous φ).comp hT).div_const _
  refine ⟨{ toFun := fun h => ⟨φ (U h), mem_sphere_zero_iff_norm.2 (hn h)⟩
            map_one' := Circle.ext (by simp)
            map_mul' := fun a b => Circle.ext (by
              change φ (U (a * b)) = φ (U a) * φ (U b)
              rw [map_mul, map_mul])
            continuous_toFun := hc.subtype_mk _ }, ?_⟩
  intro h
  apply hφ
  have : φ (U g) = 1 := congrArg (fun z : Circle => (z : ℂ)) h
  rw [map_mul, this, one_mul]

private theorem alg_case {C A : Type*} [CommGroup C] [TopologicalSpace C] [CStarAlgebra A]
    (U : C →* A) (hU : ∀ h, star (U h) = U h⁻¹) (T : A)
    (hB : ∀ B : A, (∀ h, U h * B = B * U h) → B * T = T * B)
    (hT : Continuous fun h => U h * T)
    {g : C} (hg : U g * T ≠ T) : ∃ χ : C →ₜ* Circle, χ g ≠ 1 := by
  let S' : StarSubalgebra ℂ A := StarSubalgebra.centralizer ℂ (Set.range U)
  have mem' : ∀ B, B ∈ S' ↔ ∀ h, U h * B = B * U h := by
    intro B
    rw [StarSubalgebra.mem_centralizer_iff]
    constructor
    · intro H h
      exact (H _ ⟨h, rfl⟩).1
    · rintro H _ ⟨h, rfl⟩
      exact ⟨H h, by rw [hU]; exact H _⟩
  let S : StarSubalgebra ℂ A := StarSubalgebra.centralizer ℂ (S' : Set A)
  have mem : ∀ B, B ∈ S ↔ ∀ D ∈ S', D * B = B * D := by
    intro B
    rw [StarSubalgebra.mem_centralizer_iff]
    constructor
    · intro H D hD
      exact (H _ hD).1
    · intro H D hD
      exact ⟨H D hD, H _ (star_mem hD)⟩
  have hUS' : ∀ h, U h ∈ S' := fun h => (mem' _).2 fun k => by
    rw [← map_mul, ← map_mul, mul_comm]
  have hUS : ∀ h, U h ∈ S := fun h => (mem _).2 fun D hD => ((mem' D).1 hD h).symm
  have hTS : T ∈ S := (mem _).2 fun D hD => hB D ((mem' D).1 hD)
  have hSS : ∀ B ∈ S, B ∈ S' := fun B hB => (mem' _).2 fun h => (mem _).1 hB _ (hUS' h)
  have hcl : IsClosed (S : Set A) := by
    have : (S : Set A) = ⋂ D ∈ S', {B | D * B = B * D} := by
      ext B
      simp only [SetLike.mem_coe, mem, Set.mem_iInter, Set.mem_setOf_eq]
    rw [this]
    exact isClosed_biInter fun D _ => isClosed_eq (by fun_prop) (by fun_prop)
  let _ : CommCStarAlgebra S :=
    { (inferInstance : CStarAlgebra S) with
      mul_comm := fun a b => Subtype.ext ((mem _).1 b.2 _ (hSS _ a.2)) }
  refine comm_case (A := S) (U.codRestrict S hUS) (fun h => Subtype.ext (hU h)) ⟨T, hTS⟩
    (hT.subtype_mk _) (fun h => hg (congrArg Subtype.val h))

private theorem hilbert_case {C H : Type*} [CommGroup C] [TopologicalSpace C]
    [IsTopologicalGroup C] [CompactSpace C] [MeasurableSpace C] [BorelSpace C]
    (μ : Measure C) [μ.IsHaarMeasure]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (U : C →* (H →L[ℂ] H)) (hn : ∀ h v, ‖U h v‖ = ‖v‖) (hc : ∀ v, Continuous fun h => U h v)
    {g : C} {v : H} (hg : U g v ≠ v) : ∃ χ : C →ₜ* Circle, χ g ≠ 1 := by
  have happ : ∀ a b x, U a (U b x) = U (a * b) x := by
    intro a b x
    rw [map_mul]
    rfl
  have hstar : ∀ h, star (U h) = U h⁻¹ := by
    intro h
    rw [ContinuousLinearMap.star_eq_adjoint, eq_comm, ContinuousLinearMap.eq_adjoint_iff]
    intro x y
    have := (LinearIsometry.mk (U h).toLinearMap (hn h)).inner_map_map (U h⁻¹ x) y
    rw [← this]
    change inner ℂ (U h (U h⁻¹ x)) (U h y) = _
    rw [happ, mul_inv_cancel, map_one]
    rfl
  have hint : ∀ (f : C(C, ℂ)) (x : H), Integrable (fun h => f h • U h x) μ := fun f x =>
    (f.continuous.smul (hc x)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let T₀ : C(C, ℂ) →ₗ[ℂ] H →ₗ[ℂ] H := LinearMap.mk₂ ℂ (fun f x => ∫ h, f h • U h x ∂μ)
    (fun f f' x => by
      rw [← integral_add (hint f x) (hint f' x)]
      simp [add_smul])
    (fun c f x => by
      rw [← integral_smul]
      simp [mul_smul])
    (fun f x y => by
      rw [← integral_add (hint f x) (hint f y)]
      simp)
    (fun c f x => by
      rw [← integral_smul]
      simp [smul_comm c])
  let T : C(C, ℂ) →L[ℂ] H →L[ℂ] H := T₀.mkContinuous₂ (μ.real Set.univ) (fun f x => by
    have : ‖∫ h, f h • U h x ∂μ‖ ≤ (‖f‖ * ‖x‖) * μ.real Set.univ :=
      norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun h => by
        rw [norm_smul, hn]
        exact mul_le_mul_of_nonneg_right (f.norm_coe_le_norm h) (norm_nonneg _))
    calc ‖T₀ f x‖ ≤ _ := this
      _ = _ := by ring)
  have hT : ∀ f x, T f x = ∫ h, f h • U h x ∂μ := fun _ _ => rfl
  have hB : ∀ f, ∀ B : H →L[ℂ] H, (∀ h, U h * B = B * U h) → B * T f = T f * B := by
    intro f B hB
    ext x
    change B (T f x) = T f (B x)
    rw [hT, hT, ← B.integral_comp_comm (hint f x)]
    congr 1
    funext h
    rw [map_smul]
    congr 1
    exact (congrArg (fun L : H →L[ℂ] H => L x) (hB h)).symm
  let w : H := U g v - v
  have hw : w ≠ 0 := sub_ne_zero.2 hg
  let f : C(C, ℂ) := ⟨fun h => inner ℂ (U h w) w, (hc w).inner continuous_const⟩
  let F : C(C, C(C, ℂ)) :=
    (f.comp ⟨fun p : C × C => p.1⁻¹ * p.2, by fun_prop⟩).curry
  have hF : ∀ k, U k * T f = T (F k) := by
    intro k
    ext x
    change U k (T f x) = T (F k) x
    rw [hT, hT, ← (U k).integral_comp_comm (hint f x),
      ← integral_mul_left_eq_self (fun h => F k h • U h x) k]
    congr 1
    funext h
    rw [map_smul, happ]
    congr 1
    change f h = f (k⁻¹ * (k * h))
    rw [inv_mul_cancel_left]
  refine alg_case U hstar (T f) (hB f) ?_ ?_
  · simp_rw [hF]
    exact T.continuous.comp F.continuous
  · intro h0
    have h1 : T f w = 0 := by
      have h2 := hB f (U g) (fun h => by rw [← map_mul, ← map_mul, mul_comm])
      rw [h0] at h2
      have h3 : T f v = T f (U g v) := congrArg (fun L : H →L[ℂ] H => L v) h2
      rw [map_sub, ← h3, sub_self]
    have h2 : ∫ h, ((‖f h‖ ^ 2 : ℝ) : ℂ) ∂μ = 0 := by
      have := integral_inner (𝕜 := ℂ) (hint f w) w
      rw [← hT, h1, inner_zero_right] at this
      rw [← this]
      congr 1
      funext h
      rw [inner_smul_right, ← inner_conj_symm w (U h w)]
      change _ = f h * (starRingEnd ℂ) (f h)
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [integral_complex_ofReal, Complex.ofReal_eq_zero] at h2
    refine (Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := μ) (x := 1)
      (f := fun h => ‖f h‖ ^ 2) (by fun_prop) (HasCompactSupport.of_compactSpace _)
      (fun h => by positivity) ?_).ne' h2
    have : f 1 = inner ℂ w w := by
      change inner ℂ (U 1 w) w = _
      rw [map_one]
      rfl
    simp only [this]
    exact pow_ne_zero _ (norm_ne_zero_iff.2 (inner_self_ne_zero.2 hw))

end UpperTheory.Reformulated.B.CharactersSeparatePoints

theorem UpperTheory.Reformulated.B.CharactersSeparatePoints.exists_char_ne_one.{u_1} :
    ∀ {C : Type u_1} [inst : CommGroup C] [inst_1 : TopologicalSpace C] [IsTopologicalGroup C] [CompactSpace C] [T2Space C]
      {g : C}, g ≠ (1 : C) → ∃ (χ : C →ₜ* Circle), (χ : C → Circle) g ≠ (1 : Circle) := by
  intro C _ _ _ _ _ g hg
  borelize C
  let μ : Measure C := Measure.haar
  let m : C(C, C(C, C)) := ContinuousMap.curry ⟨fun p : C × C => p.1 * p.2, by fun_prop⟩
  have hm : ∀ h, MeasurePreserving (m h) μ μ := fun h => measurePreserving_mul_left μ h
  let V : C → (Lp ℂ 2 μ →ₗᵢ[ℂ] Lp ℂ 2 μ) := fun h => Lp.compMeasurePreservingₗᵢ ℂ (m h) (hm h)
  have hV : ∀ h x, V h x = Lp.compMeasurePreserving (m h) (hm h) x := fun _ _ => rfl
  let U : C →* (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) :=
    { toFun := fun h => (V h).toContinuousLinearMap
      map_one' := by
        refine ContinuousLinearMap.ext fun x => ?_
        change Lp.compMeasurePreserving (m 1) (hm 1) x = x
        convert Lp.compMeasurePreserving_id_apply x
        funext a
        exact one_mul a
      map_mul' := fun a b => by
        refine ContinuousLinearMap.ext fun x => ?_
        change Lp.compMeasurePreserving (m (a * b)) (hm _) x =
          Lp.compMeasurePreserving (m a) (hm a) (Lp.compMeasurePreserving (m b) (hm b) x)
        rw [← Lp.compMeasurePreserving_comp_apply]
        congr 2
        funext c
        exact (mul_left_comm b a c).trans (mul_assoc a b c).symm |>.symm }
  obtain ⟨F, hF0, hF1, -⟩ := exists_continuous_zero_one_of_isClosed
    (isClosed_singleton (x := g)) (isClosed_singleton (x := (1 : C)))
    (Set.disjoint_singleton.2 hg)
  let G : C(C, ℂ) := ⟨fun a => (F a : ℂ), by fun_prop⟩
  refine hilbert_case μ U (fun h x => (V h).norm_map x)
    (fun x => continuous_const.compMeasurePreservingLp m.continuous hm (by simp))
    (v := ContinuousMap.toLp 2 μ ℂ G) ?_
  intro h0
  have h0' : Lp.compMeasurePreserving (m g) (hm g) (ContinuousMap.toLp 2 μ ℂ G) =
      ContinuousMap.toLp 2 μ ℂ G := h0
  have h1 : ContinuousMap.toLp 2 μ ℂ (G.comp (m g)) = ContinuousMap.toLp 2 μ ℂ G := by
    refine Eq.trans (Lp.ext ?_) h0'
    have e1 := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) μ (G.comp (m g))
    have e2 := Lp.coeFn_compMeasurePreserving (ContinuousMap.toLp 2 μ ℂ G) (hm g)
    have e3 := (hm g).quasiMeasurePreserving.ae_eq_comp
      (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) μ G)
    exact e1.trans (e2.trans e3).symm
  have h2 : (F (g * 1) : ℂ) = F 1 :=
    congrArg (fun f : C(C, ℂ) => f 1) (ContinuousMap.toLp_injective μ h1)
  rw [mul_one, hF0 rfl, hF1 rfl] at h2
  simp at h2
end

