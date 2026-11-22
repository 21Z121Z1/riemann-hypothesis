import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0037
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsLatticeOfFibLocNeZeroGood

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MemSmulSpanIff
section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.D2

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

open LocalSpans in
theorem exists_smith {A₀ B₀ : Submodule (𝓞 K) V} (hA₀ : Submodule.IsLattice K A₀)
    (hB₀ : Submodule.IsLattice K B₀) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ (a b : Basis (Fin (finrank K V)) K V) (e : Fin (finrank K V) → 𝓞 K) (c : 𝓞 K),
      c ≠ 0 ∧ (∀ i, e i ≠ 0) ∧
      locF 𝔭 (Submodule.span (𝓞 K) (Set.range a)) = locF 𝔭 A₀ ∧
      locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) = locF 𝔭 B₀ ∧ ∀ i, c • b i = e i • a i := by
  have : 𝔭.IsPrime := h𝔭.isPrime
  have hp0 : 𝔭 ≠ ⊥ := fun h => RingOfIntegers.not_isField F (Ring.isField_iff_maximal_bot.2 (h ▸ h𝔭))
  have : IsDedekindDomain (RP K 𝔭) := IsLocalization.isDedekindDomain (𝓞 K) (sF_le 𝔭) _
  have : IsPrincipalIdealRing (RP K 𝔭) :=
    IsDedekindDomain.isPrincipalIdealRing_localization_over_prime (𝓞 K) 𝔭 hp0
  obtain ⟨a0, -, ha0⟩ := exists_basis_locF hA₀ h𝔭
  obtain ⟨b0, -, hb0⟩ := exists_basis_locF hB₀ h𝔭

  obtain ⟨⟨c, hc⟩, hcint⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 K))
    (fun p : Fin (finrank K V) × Fin (finrank K V) => a0.repr (b0 p.1) p.2)
  have hc0 : c ≠ 0 := nonZeroDivisors.ne_zero hc
  have hcK : algebraMap (𝓞 K) K c ≠ 0 := by
    simpa using hc0
  let MA : Submodule (RP K 𝔭) V := Submodule.span (RP K 𝔭) (Set.range a0)
  let MB : Submodule (RP K 𝔭) V := Submodule.span (RP K 𝔭) (Set.range b0)
  let μ : V →ₗ[RP K 𝔭] V := ((algebraMap (𝓞 K) K c) • (LinearMap.id : V →ₗ[K] V)).restrictScalars (RP K 𝔭)
  have hμ : ∀ x, μ x = algebraMap (𝓞 K) K c • x := fun x => rfl
  have hμi : Function.Injective μ := fun x y hxy => by
    rw [hμ, hμ] at hxy
    exact smul_right_injective V hcK hxy
  let N' : Submodule (RP K 𝔭) V := MB.map μ
  have hN' : N' ≤ MA := by
    show Submodule.map μ (Submodule.span _ _) ≤ MA
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    rw [hμ, ← a0.sum_repr (b0 i), Finset.smul_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    obtain ⟨z, hz⟩ := hcint (i, j)
    rw [smul_smul]
    have : algebraMap (𝓞 K) K c * a0.repr (b0 i) j = algebraMap (𝓞 K) K z := by
      rw [hz, Algebra.smul_def]
    rw [this, algebraMap_smul, ← algebraMap_smul (RP K 𝔭)]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hliA : LinearIndependent (RP K 𝔭) a0 := a0.linearIndependent.restrict_scalars' (RP K 𝔭)
  have hliB : LinearIndependent (RP K 𝔭) b0 := b0.linearIndependent.restrict_scalars' (RP K 𝔭)
  have hfA : finrank (RP K 𝔭) MA = finrank K V := by
    rw [finrank_span_eq_card hliA, Fintype.card_fin]
  have hfB : finrank (RP K 𝔭) MB = finrank K V := by
    rw [finrank_span_eq_card hliB, Fintype.card_fin]
  let N : Submodule (RP K 𝔭) MA := N'.comap MA.subtype
  have hfN : finrank (RP K 𝔭) N = finrank (RP K 𝔭) MA := by
    rw [hfA, ← hfB, (Submodule.comapSubtypeEquivOfLe hN').finrank_eq,
      (Submodule.equivMapOfInjective μ hμi MB).finrank_eq]
  obtain ⟨b', α, ab', hab⟩ := Submodule.exists_smith_normal_form_of_rank_eq (Basis.span hliA) hfN
  have hlatA : Submodule.IsLattice K MA :=
    { fg := Submodule.fg_span (Set.finite_range _)
      span_eq_top := by
        rw [eq_top_iff, ← a0.span_eq]
        exact Submodule.span_mono Submodule.subset_span }
  let a := b'.extendOfIsLattice K
  have ha : ∀ i, a i = (b' i : V) := fun i => Basis.extendOfIsLattice_apply K b' i
  have hα0 : ∀ i, α i ≠ 0 := fun i h0 => by
    have h1 := hab i
    rw [h0, zero_smul] at h1
    exact ab'.ne_zero i (Subtype.ext h1)
  have hα : ∀ i, ∃ (z : 𝓞 K) (t : 𝓞 F), t ∉ 𝔭 ∧ (α i : K) =
      algebraMap (𝓞 K) K z * (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t))⁻¹ := fun i => by
    obtain ⟨z, s, ⟨t, ht, rfl⟩, hz⟩ := (α i).2
    exact ⟨z, t, ht, hz⟩
  choose e t ht he using hα
  have ht0 : ∀ i, algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (t i)) ≠ 0 := by
    intro i h0
    have h1 := (FaithfulSMul.algebraMap_injective (𝓞 K) K) (h0.trans (map_zero _).symm)
    have h2 := (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K)) (h1.trans (map_zero _).symm)
    exact ht i (h2 ▸ 𝔭.zero_mem)
  have he0 : ∀ i, e i ≠ 0 := fun i h0 => hα0 i (Subtype.ext (by rw [he, h0]; simp))
  have heK : ∀ i, algebraMap (𝓞 K) K (e i) ≠ 0 := fun i => by
    simpa using he0 i
  let b := a.unitsSMul fun i => Units.mk0 (algebraMap (𝓞 K) K (e i) * (algebraMap (𝓞 K) K c)⁻¹)
    (mul_ne_zero (heK i) (inv_ne_zero hcK))
  have hb : ∀ i, b i = (algebraMap (𝓞 K) K (e i) * (algebraMap (𝓞 K) K c)⁻¹) • a i := fun i => by
    rw [Basis.unitsSMul_apply, Units.smul_def, Units.val_mk0]
  have hcb : ∀ i, algebraMap (𝓞 K) K c • b i = algebraMap (𝓞 K) K (e i) • a i := fun i => by
    rw [hb, smul_smul, mul_comm, mul_assoc, inv_mul_cancel₀ hcK, mul_one]
  have habV : ∀ i, (((ab' i : N) : MA) : V) = (α i : K) • a i := fun i => by
    rw [hab, ha]
    rfl
  have hτ : ∀ i, μ (b i) = algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (t i)) • (((ab' i : N) : MA) : V) :=
    fun i => by
      rw [hμ, hcb, habV, he, smul_smul, mul_comm, mul_assoc, inv_mul_cancel₀ (ht0 i), mul_one]
  have hsA : Submodule.span (RP K 𝔭) (Set.range a) = MA := by
    have h1 : Set.range a = MA.subtype '' Set.range b' := by
      rw [← Set.range_comp]
      exact congrArg _ (funext ha)
    rw [h1, ← Submodule.map_span, b'.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hsN : Submodule.span (RP K 𝔭) (Set.range fun i => (((ab' i : N) : MA) : V)) = N' := by
    have h1 : (Set.range fun i => (((ab' i : N) : MA) : V)) =
        MA.subtype '' (N.subtype '' Set.range ab') := by
      rw [← Set.range_comp, ← Set.range_comp]
      rfl
    rw [h1, ← Submodule.map_span, ← Submodule.map_span, ab'.span_eq, Submodule.map_top,
      Submodule.range_subtype, Submodule.map_comap_subtype, inf_eq_right.2 hN']
  have hsB : Submodule.span (RP K 𝔭) (Set.range b) = MB := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      obtain ⟨y, hy, hyx⟩ : (((ab' i : N) : MA) : V) ∈ N' := (ab' i).2
      have h1 : μ (b i) = μ (algebraMap (𝓞 F) (𝓞 K) (t i) • y) := by
        rw [hτ, ← hyx, hμ, hμ, ← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) (t i)), smul_comm]
      rw [hμi h1, ← algebraMap_smul (RP K 𝔭)]
      exact Submodule.smul_mem _ _ hy
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      have h1 : μ (b0 j) ∈ N' := ⟨b0 j, Submodule.subset_span ⟨j, rfl⟩, rfl⟩
      have h2 : N' ≤ (Submodule.span (RP K 𝔭) (Set.range b)).map μ := by
        rw [← hsN, Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        let u : RP K 𝔭 := ⟨(algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (t i)))⁻¹,
          ⟨1, _, ⟨t i, ht i, rfl⟩, by simp⟩⟩
        refine ⟨u • b i, Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩), ?_⟩
        rw [map_smul, hτ, Subalgebra.smul_def, smul_smul, inv_mul_cancel₀ (ht0 i), one_smul]
      obtain ⟨y, hy, hyx⟩ := h2 h1
      exact hμi hyx ▸ hy
  refine ⟨a, b, e, c, hc0, he0, ?_, ?_, fun i => ?_⟩
  · rw [← ha0]
    ext x
    rw [← mem_span_RP, ← mem_span_RP, Submodule.span_span_of_tower, Submodule.span_span_of_tower, hsA]
  · rw [← hb0]
    ext x
    rw [← mem_span_RP, ← mem_span_RP, Submodule.span_span_of_tower, Submodule.span_span_of_tower, hsB]
  · rw [← algebraMap_smul K, ← algebraMap_smul K (e i), hcb]

theorem basis_mem_locF {κ : Type} (a : Basis κ K V) (𝔭 : Ideal (𝓞 F)) (i : κ) :
    a i ∈ locF 𝔭 (Submodule.span (𝓞 K) (Set.range a)) :=
  LocF.le_locF 𝔭 _ (Submodule.subset_span ⟨i, rfl⟩)

theorem repr_mem_pK_zero {κ : Type} (a : Basis κ K V) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    {x : V} (hx : x ∈ locF 𝔭 (Submodule.span (𝓞 K) (Set.range a))) (i : κ) :
    a.repr x i ∈ pK K 𝔭 0 := by
  obtain ⟨t, ht, hx⟩ := (LocF.mem_locF_iff h𝔭.isPrime _ x).1 hx
  obtain ⟨z, hz⟩ := (a.mem_span_iff_repr_mem (𝓞 K) _).1 hx i
  refine (mem_pK h𝔭).2 ⟨t, ht, z, by simp, ?_⟩
  rw [hz, ← algebraMap_smul K, map_smul, Finsupp.smul_apply, smul_eq_mul]
  rfl

theorem mem_smul_span_iff {κ : Type} [Fintype κ] (a : Basis κ K V) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (k : ℕ) (x : V) :
    x ∈ extP K 𝔭 ^ k • locF 𝔭 (Submodule.span (𝓞 K) (Set.range a)) ↔
      ∀ i, a.repr x i ∈ pK K 𝔭 k := by
  constructor
  · intro hx i
    induction hx using Submodule.smul_induction_on' with
    | smul r hr n hn =>
      have h1 : algebraMap (𝓞 K) K r ∈ pK K 𝔭 k := LocF.le_locF 𝔭 _ ⟨r, hr, rfl⟩
      have h2 := mul_mem_pK h𝔭 h1 (repr_mem_pK_zero a h𝔭 hn i)
      rw [← algebraMap_smul K, map_smul, Finsupp.smul_apply, smul_eq_mul]
      simpa using h2
    | add x _ y _ hx hy =>
      rw [map_add, Finsupp.add_apply]
      exact (pK K 𝔭 k).add_mem hx hy
  · intro hx
    rw [← a.sum_repr x]
    refine Submodule.sum_mem _ fun i _ => ?_
    have h0 : a i ∈ extP K 𝔭 ^ 0 • locF 𝔭 (Submodule.span (𝓞 K) (Set.range a)) := by
      rw [pow_zero_smul]
      exact basis_mem_locF a 𝔭 i
    simpa using smul_mem_smul h𝔭 _ (hx i) h0

theorem mem_endL_iff {κ : Type} [Fintype κ] [DecidableEq κ] (a : Basis κ K V) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (k : ℕ) (D : V →ₗ[K] V) :
    D ∈ endL (locF 𝔭 (Submodule.span (𝓞 K) (Set.range a)))
        (extP K 𝔭 ^ k • locF 𝔭 (Submodule.span (𝓞 K) (Set.range a))) ↔
      ∀ i j, LinearMap.toMatrix a a D i j ∈ pK K 𝔭 k := by
  constructor
  · intro hD i j
    rw [LinearMap.toMatrix_apply]
    exact (mem_smul_span_iff a h𝔭 k _).1 (hD _ (basis_mem_locF a 𝔭 j)) i
  · intro hD x hx
    rw [← a.sum_repr x, map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [map_smul]
    have h1 : D (a j) ∈ extP K 𝔭 ^ k • locF 𝔭 (Submodule.span (𝓞 K) (Set.range a)) :=
      (mem_smul_span_iff a h𝔭 k _).2 fun i => by
        rw [← LinearMap.toMatrix_apply]
        exact hD i j
    simpa using smul_mem_smul h𝔭 _ (repr_mem_pK_zero a h𝔭 hx j) h1

theorem mem_sesqL_iff (hF : IsFixF K F) {κ : Type} [Fintype κ] (a : Basis κ K V)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) (s : V →ₗ⋆[K] V →ₗ[K] K) :
    s ∈ sesqL (locF 𝔭 (Submodule.span (𝓞 K) (Set.range a))) 𝔭 k ↔
      ∀ i j, s (a i) (a j) ∈ pK K 𝔭 k := by
  constructor
  · intro hs i j
    exact hs _ (basis_mem_locF a 𝔭 i) _ (basis_mem_locF a 𝔭 j)
  · intro hs x hx y hy
    rw [← a.sum_repr x, ← a.sum_repr y, map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [map_sum, LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
    have h1 := mul_mem_pK h𝔭 (repr_mem_pK_zero a h𝔭 hy j)
      (mul_mem_pK h𝔭 (star_mem_pK hF h𝔭 (repr_mem_pK_zero a h𝔭 hx i)) (hs i j))
    rw [zero_add, zero_add] at h1
    exact h1

end Formalism.HermitianLattices.Ext.L3.D2
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.SurjectiveOfNondegenerate
section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.D2.IA

theorem relIndex_eq_of_map {G M : Type*} [Group G] [AddCommGroup M] (H T : Subgroup G)
    (N' N : AddSubgroup M) (f : G → M) (hf : ∀ X ∈ T, f X ∈ N)
    (hc : ∀ X ∈ T, ∀ Y ∈ T, X⁻¹ * Y ∈ H ↔ f X - f Y ∈ N')
    (hsurj : ∀ Z ∈ N, ∃ X ∈ T, f X - Z ∈ N') : H.relIndex T = N'.relIndex N := by
  unfold Subgroup.relIndex AddSubgroup.relIndex Subgroup.index AddSubgroup.index
  let g : (T ⧸ H.subgroupOf T) → (N ⧸ N'.addSubgroupOf N) :=
    Quotient.lift (s := QuotientGroup.leftRel (H.subgroupOf T))
      (fun X : T => ((⟨f X, hf X X.2⟩ : N) : N ⧸ N'.addSubgroupOf N)) (by
        intro X Y hXY
        have hXY := QuotientGroup.leftRel_apply.1 hXY
        have h1 : f X - f Y ∈ N' := (hc X X.2 Y Y.2).1 (by simpa [Subgroup.mem_subgroupOf] using hXY)
        rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
        have := N'.neg_mem h1
        simpa [neg_add_eq_sub] using this)
  refine Nat.card_eq_of_bijective g ⟨?_, ?_⟩
  · intro a b
    induction a using QuotientGroup.induction_on with | _ X => ?_
    induction b using QuotientGroup.induction_on with | _ Y => ?_
    intro hab
    have h1 : ((⟨f X, hf X X.2⟩ : N) : N ⧸ N'.addSubgroupOf N) = ((⟨f Y, hf Y Y.2⟩ : N) : N ⧸ N'.addSubgroupOf N) := hab
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at h1
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have h2 : f X - f Y ∈ N' := by
      have := N'.neg_mem h1
      simpa [neg_add_eq_sub] using this
    simpa using (hc X X.2 Y Y.2).2 h2
  · intro b
    induction b using QuotientAddGroup.induction_on with | _ Z => ?_
    obtain ⟨X, hX, hXZ⟩ := hsurj Z Z.2
    refine ⟨((⟨X, hX⟩ : T) : T ⧸ H.subgroupOf T), ?_⟩
    show ((⟨f X, hf X hX⟩ : N) : N ⧸ N'.addSubgroupOf N) = (Z : N ⧸ N'.addSubgroupOf N)
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
    have := N'.neg_mem hXZ
    simpa [neg_add_eq_sub] using this

variable {K : Type} [Field K] [StarRing K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem surjective_of_nondegenerate {h : V →ₗ⋆[K] V →ₗ[K] K} (hn : h.Nondegenerate) :
    Function.Surjective h := by
  have hinj : Function.Injective h := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    exact hn.1 x (fun y => by rw [hx]; rfl)
  have hbij : Function.Bijective (h.rangeRestrict) :=
    ⟨fun a b hab => hinj (congrArg Subtype.val hab), h.surjective_rangeRestrict⟩
  let j : V ≃+ LinearMap.range h := AddEquiv.ofBijective (h.rangeRestrict).toAddMonoidHom hbij
  have hr : Module.rank K V = Module.rank K (LinearMap.range h) :=
    rank_eq_of_equiv_equiv (starRingEnd K) j star_involutive.bijective (fun r m => by
      apply Subtype.ext
      show h (r • m) = (starRingEnd K) r • h m
      rw [map_smulₛₗ])
  have hf : finrank K (LinearMap.range h) = finrank K (Dual K V) := by
    rw [Subspace.dual_finrank_eq]
    unfold finrank
    rw [hr]
  have htop := Submodule.eq_top_of_finrank_eq hf
  exact LinearMap.range_eq_top.1 htop

theorem exists_adj {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hn : h.Nondegenerate)
    (s : V →ₗ⋆[K] V →ₗ[K] K) : ∃ Y : V →ₗ[K] V, ∀ x y, h x (Y y) = s x y := by
  have hex : ∀ y, ∃ w, ∀ x, h x w = s x y := by
    intro y
    let l : V →ₗ[K] K :=
      { toFun := fun x => star (s x y)
        map_add' := fun a b => by simp
        map_smul' := fun a b => by simp [starRingEnd_apply] }
    obtain ⟨w, hw⟩ := surjective_of_nondegenerate hn l
    refine ⟨w, fun x => ?_⟩
    have h1 : h w x = star (s x y) := by rw [hw]; rfl
    have h2 := hs.eq w x
    rw [← h2, h1, starRingEnd_apply, star_star]
  choose Y hY using hex
  refine ⟨{ toFun := Y, map_add' := fun a b => ?_, map_smul' := fun a b => ?_ }, fun x y => hY y x⟩
  · rw [← sub_eq_zero]
    refine hn.2 _ (fun x => ?_)
    rw [map_sub, map_add, hY, hY, hY, map_add, sub_self]
  · rw [← sub_eq_zero]
    refine hn.2 _ (fun x => ?_)
    rw [RingHom.id_apply, map_sub, map_smul, hY, hY, map_smul, sub_self]

section Lat

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

def phi (h : V →ₗ⋆[K] V →ₗ[K] K) (X : V ≃ₗ[K] V) : V →ₗ⋆[K] V →ₗ[K] K :=
  (h.comp (X : V →ₗ[K] V)).compl₂ (X : V →ₗ[K] V) - h

theorem phi_apply (h : V →ₗ⋆[K] V →ₗ[K] K) (X : V ≃ₗ[K] V) (x y : V) :
    phi h X x y = h (X x) (X y) - h x y := rfl

theorem star_phi {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (X : V ≃ₗ[K] V) (x y : V) :
    star (phi h X x y) = phi h X y x := by
  have e : ∀ a b, star (h a b) = h b a := fun a b => hs.eq a b
  rw [phi_apply, phi_apply, star_sub, e, e]

theorem unif_ne_zero {𝔭 : Ideal (𝓞 F)} {π : 𝓞 F} (hπ' : π ∉ 𝔭 ^ 2) : algebraMap F K (π : F) ≠ 0 := by
  intro h0
  have h1 : (π : F) = 0 := (map_eq_zero (algebraMap F K)).1 h0
  have h2 : π = 0 := by exact_mod_cast h1
  exact hπ' (h2 ▸ zero_mem _)

theorem sesq_scale (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {A₀ B₀ : Submodule (𝓞 K) V} {r : ℕ}
    (hr : extP K 𝔭 ^ r • locF 𝔭 A₀ ≤ locF 𝔭 B₀) (s : V →ₗ⋆[K] V →ₗ[K] K) {n m : ℕ} (hnm : n + 2 * r ≤ m)
    (hs : ∀ x ∈ locF 𝔭 B₀, ∀ y ∈ locF 𝔭 B₀, s x y ∈ pK K 𝔭 m) :
    ∀ x ∈ locF 𝔭 A₀, ∀ y ∈ locF 𝔭 A₀, s x y ∈ pK K 𝔭 n := by
  obtain ⟨π, hπ, hπ'⟩ := exists_unif h𝔭
  have h0 : algebraMap F K (π : F) ≠ 0 := unif_ne_zero hπ'
  have hst : star (algebraMap F K (π : F)) = algebraMap F K (π : F) := (hF _).2 ⟨_, rfl⟩
  intro x hx y hy
  have hx' : algebraMap F K (π : F) ^ r • x ∈ locF 𝔭 B₀ :=
    hr ((mem_smul_iff_unif h𝔭 hπ hπ' A₀).2 ⟨x, hx, rfl⟩)
  have hy' : algebraMap F K (π : F) ^ r • y ∈ locF 𝔭 B₀ :=
    hr ((mem_smul_iff_unif h𝔭 hπ hπ' A₀).2 ⟨y, hy, rfl⟩)
  have h1 := pK_anti (K := K) 𝔭 hnm (hs _ hx' _ hy')
  rw [map_smul, map_smulₛₗ, LinearMap.smul_apply, starRingEnd_apply, star_pow, hst, smul_eq_mul, smul_eq_mul] at h1
  obtain ⟨b, hb, e⟩ := (mem_pK_iff_unif h𝔭 hπ hπ').1 h1
  refine (mem_pK_iff_unif h𝔭 hπ hπ').2 ⟨b, hb, ?_⟩
  apply mul_left_cancel₀ (pow_ne_zero (2 * r) h0)
  calc algebraMap F K (π : F) ^ (2 * r) * s x y
      = algebraMap F K (π : F) ^ r * (algebraMap F K (π : F) ^ r * s x y) := by ring
    _ = algebraMap F K (π : F) ^ (n + 2 * r) * b := e
    _ = _ := by ring

theorem end_scale {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {A₀ B₀ : Submodule (𝓞 K) V} {r r' : ℕ}
    (hr : extP K 𝔭 ^ r • locF 𝔭 A₀ ≤ locF 𝔭 B₀) (hr' : extP K 𝔭 ^ r' • locF 𝔭 B₀ ≤ locF 𝔭 A₀)
    (Y : V →ₗ[K] V) {n m : ℕ} (hnm : n + r + r' ≤ m)
    (hY : ∀ x ∈ locF 𝔭 A₀, Y x ∈ extP K 𝔭 ^ m • locF 𝔭 A₀) :
    ∀ x ∈ locF 𝔭 B₀, Y x ∈ extP K 𝔭 ^ n • locF 𝔭 B₀ := by
  obtain ⟨π, hπ, hπ'⟩ := exists_unif h𝔭
  have h0 : algebraMap F K (π : F) ≠ 0 := unif_ne_zero hπ'
  intro x hx
  have hx' : algebraMap F K (π : F) ^ r' • x ∈ locF 𝔭 A₀ :=
    hr' ((mem_smul_iff_unif h𝔭 hπ hπ' B₀).2 ⟨x, hx, rfl⟩)
  have h1 := smul_anti 𝔭 (locF 𝔭 A₀) hnm (hY _ hx')
  obtain ⟨a, ha, e⟩ := (mem_smul_iff_unif h𝔭 hπ hπ' A₀).1 h1
  have ha' : algebraMap F K (π : F) ^ r • a ∈ locF 𝔭 B₀ :=
    hr ((mem_smul_iff_unif h𝔭 hπ hπ' A₀).2 ⟨a, ha, rfl⟩)
  refine (mem_smul_iff_unif h𝔭 hπ hπ' B₀).2 ⟨_, ha', ?_⟩
  rw [map_smul] at e
  apply smul_right_injective V (pow_ne_zero r' h0)
  show algebraMap F K (π : F) ^ r' • Y x = algebraMap F K (π : F) ^ r' • _
  rw [e, smul_smul, smul_smul]
  congr 1
  ring

end Lat

end Formalism.HermitianLattices.Ext.L3.D2.IA
end
end

