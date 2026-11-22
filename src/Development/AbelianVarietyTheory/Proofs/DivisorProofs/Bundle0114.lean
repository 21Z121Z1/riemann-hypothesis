import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimAddOneLeOfSsubset
section
open TopologicalSpace

namespace GlobalTheory

theorem topologicalKrullDim_add_one_le_of_ssubset (T : Type) [TopologicalSpace T] (A B : Set T)
    (hA : IsClosed A) (hAi : IsIrreducible A) (hBi : IsIrreducible B) (hAB : A ⊂ B) :
    topologicalKrullDim A + 1 ≤ topologicalKrullDim B := by
  have hsub : A ⊆ B := hAB.subset
  have hemb : Topology.IsClosedEmbedding (Set.inclusion hsub) :=
    Topology.IsClosedEmbedding.inclusion hsub (hA.preimage continuous_subtype_val)
  haveI : IrreducibleSpace A := Subtype.irreducibleSpace hAi
  haveI : IrreducibleSpace B := Subtype.irreducibleSpace hBi
  let f : IrreducibleCloseds A → IrreducibleCloseds B := fun Z =>
    ⟨Set.inclusion hsub '' (Z : Set A),
      Z.isIrreducible.image _ hemb.continuous.continuousOn,
      hemb.isClosedMap _ Z.isClosed⟩
  let top : IrreducibleCloseds B := ⟨Set.univ, IrreducibleSpace.isIrreducible_univ B, isClosed_univ⟩
  have hf : StrictMono f := by
    intro Z W h
    have h' : (Z : Set A) ⊂ (W : Set A) := h
    show Set.inclusion hsub '' (Z : Set A) ⊂ Set.inclusion hsub '' (W : Set A)
    exact hemb.injective.injOn.image_ssubset_image_iff (Set.subset_univ _) (Set.subset_univ _) |>.mpr h'
  have htop : ∀ Z, f Z < top := by
    intro Z
    show Set.inclusion hsub '' (Z : Set A) ⊂ Set.univ
    obtain ⟨x, hxB, hxA⟩ := Set.exists_of_ssubset hAB
    refine Set.ssubset_univ_iff.mpr ?_
    intro h
    have : (⟨x, hxB⟩ : B) ∈ Set.inclusion hsub '' (Z : Set A) := h ▸ Set.mem_univ _
    obtain ⟨y, -, hy⟩ := this
    have : (y : T) = x := congrArg Subtype.val hy
    exact hxA (this ▸ y.2)
  haveI : Nonempty (IrreducibleCloseds A) :=
    ⟨⟨Set.univ, IrreducibleSpace.isIrreducible_univ A, isClosed_univ⟩⟩
  let g : WithTop (IrreducibleCloseds A) → IrreducibleCloseds B := WithTop.recTopCoe top f
  have hg : StrictMono g := by
    rw [WithTop.strictMono_iff]
    exact ⟨hf, htop⟩
  have := Order.krullDim_le_of_strictMono g hg
  rwa [Order.krullDim_WithTop] at this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimDropAndFiniteOfDimZero
section
open TopologicalSpace Order

namespace GlobalTheory.DimDrop

theorem length_le_topologicalKrullDim_of_last_subset {X : Type} [TopologicalSpace X] (Z : Set X)
    (q : LTSeries (IrreducibleCloseds X)) (h : (q.last : Set X) ⊆ Z) :
    (q.length : WithBot ℕ∞) ≤ topologicalKrullDim Z := by
  have hsub : ∀ i, (q i : Set X) ⊆ Z := fun i x hx => h (q.monotone (Fin.le_last i) hx)
  have irr : ∀ i, IsIrreducible (Subtype.val ⁻¹' (q i : Set X) : Set Z) := by
    intro i
    haveI : IrreducibleSpace (q i : Set X) := Subtype.irreducibleSpace (q i).isIrreducible
    have := (IrreducibleSpace.isIrreducible_univ (q i : Set X)).image (Set.inclusion (hsub i))
      (continuous_inclusion (hsub i)).continuousOn
    rw [Set.image_univ, Set.range_inclusion] at this
    exact this
  let f : Fin (q.length + 1) → IrreducibleCloseds Z := fun i =>
    ⟨Subtype.val ⁻¹' (q i : Set X), irr i, (q i).isClosed.preimage continuous_subtype_val⟩
  have hf : ∀ i j, f i = f j → q i = q j := by
    intro i j e
    have e' : (Subtype.val ⁻¹' (q i : Set X) : Set Z) = Subtype.val ⁻¹' (q j : Set X) :=
      congrArg SetLike.coe e
    have e'' := congrArg (Set.image (Subtype.val : Z → X)) e'
    rw [Subtype.image_preimage_coe, Subtype.image_preimage_coe,
      Set.inter_eq_right.2 (hsub i), Set.inter_eq_right.2 (hsub j)] at e''
    exact SetLike.coe_injective e''
  let p : LTSeries (IrreducibleCloseds Z) :=
    { length := q.length
      toFun := f
      step := fun i => by
        have hs : q i.castSucc < q i.succ := q.step i
        show f i.castSucc < f i.succ
        refine lt_of_le_of_ne ?_ fun e => hs.ne (hf _ _ e)
        intro x hx
        exact hs.le hx }
  exact LTSeries.length_le_krullDim p

theorem topologicalKrullDim_lt_of_isClosed (S : Type) [TopologicalSpace S] [NoetherianSpace S]
    (C : Set S) (d : ℕ) (hC : IsClosed C) (hS : topologicalKrullDim S ≤ d)
    (hZ : ∀ Z ∈ irreducibleComponents S, (d : WithBot ℕ∞) ≤ topologicalKrullDim Z → ¬ Z ⊆ C) :
    topologicalKrullDim C < d := by
  by_contra hlt
  rw [not_lt] at hlt
  obtain ⟨p, hp⟩ := le_krullDim_iff.1 hlt
  let q : LTSeries (IrreducibleCloseds S) :=
    p.map (IrreducibleCloseds.map Subtype.val continuous_subtype_val)
      (IrreducibleCloseds.map_strictMono_of_isInducing Topology.IsInducing.subtypeVal)
  have hql : q.length = d := hp
  have hWC : (q.last : Set S) ⊆ C := by
    show closure (Subtype.val '' (p.last : Set C)) ⊆ C
    refine closure_minimal ?_ hC
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  obtain ⟨Z, hZc, hWZ⟩ :=
    exists_mem_irreducibleComponents_subset_of_isIrreducible _ q.last.isIrreducible
  by_cases hEq : (q.last : Set S) = Z
  · refine hZ Z hZc ?_ (hEq ▸ hWC)
    have := length_le_topologicalKrullDim_of_last_subset Z q hEq.le
    rwa [hql] at this
  · let Zt : IrreducibleCloseds S := ⟨Z, hZc.1, isClosed_of_mem_irreducibleComponents Z hZc⟩
    have hlt' : q.last < Zt := lt_of_le_of_ne hWZ fun e => hEq (congrArg SetLike.coe e)
    have h1 := LTSeries.length_le_krullDim (q.snoc Zt hlt')
    have h2 : ((d + 1 : ℕ) : WithBot ℕ∞) ≤ (d : WithBot ℕ∞) := by
      have e : (q.snoc Zt hlt').length = d + 1 := by simp [hql]
      rw [e] at h1
      exact h1.trans hS
    norm_cast at h2
    omega

theorem finite_of_topologicalKrullDim_nonpos (S : Type) [TopologicalSpace S] [NoetherianSpace S]
    [T0Space S] (h : topologicalKrullDim S ≤ 0) : Finite S := by
  have hm := Order.krullDim_nonpos_iff_forall_isMax.1 h
  have hcomp : ∀ x : S, closure ({x} : Set S) ∈ irreducibleComponents S := by
    intro x
    refine ⟨isIrreducible_singleton.closure, fun T hT hle => ?_⟩
    have := hm ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩
      (b := ⟨closure T, hT.closure, isClosed_closure⟩) (fun y hy => subset_closure (hle hy))
    exact subset_closure.trans this
  haveI : Finite (irreducibleComponents S) :=
    NoetherianSpace.finite_irreducibleComponents.to_subtype
  exact Finite.of_injective (fun x => (⟨closure {x}, hcomp x⟩ : irreducibleComponents S))
    fun x y hxy => (inseparable_iff_closure_eq.2 (congrArg Subtype.val hxy)).eq

theorem dim_drop : ∀ (S : Type) [TopologicalSpace S] [NoetherianSpace S],
    (∀ (C : Set S) (d : ℕ), IsClosed C → topologicalKrullDim S ≤ d →
      (∀ Z ∈ irreducibleComponents S, (d : WithBot ℕ∞) ≤ topologicalKrullDim Z → ¬ Z ⊆ C) →
      topologicalKrullDim C < d) ∧
    (T0Space S → topologicalKrullDim S ≤ 0 → Finite S) := by
  intro S _ _
  exact ⟨fun C d hC hS hZ => topologicalKrullDim_lt_of_isClosed S C d hC hS hZ,
    fun _ h => finite_of_topologicalKrullDim_nonpos S h⟩

end GlobalTheory.DimDrop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionBasisRelationsDivisible
section
open NumberField

namespace GlobalTheory

theorem dvd_of_two_gens_of_card_torsion : ∀ (F : Type) [Field F] [NumberField F] (M : Type) [AddCommGroup M] [Module (𝓞 F) M] (N : ℕ), 1 ≤ N →
    Nat.card {x : M // N • x = 0} = N ^ (2 * Module.finrank ℚ F) →
    ∀ p : Fin 2 → M, (∀ i, N • p i = 0) →
    (∀ y : M, N • y = 0 → ∃ a b : 𝓞 F, y = a • p 0 + b • p 1) →
    ∀ a b : 𝓞 F, a • p 0 + b • p 1 = 0 → (N : 𝓞 F) ∣ a ∧ (N : 𝓞 F) ∣ b := by
  intro F _ _ M _ _ N hN hc p hp hgen a b hab
  classical
  set I : Ideal (𝓞 F) := Ideal.span {(N : 𝓞 F)} with hI
  have hNp : ∀ (c : 𝓞 F) i, ((N : 𝓞 F) * c) • p i = 0 := by
    intro c i
    rw [mul_comm, mul_smul, Nat.cast_smul_eq_nsmul, hp i, smul_zero]
  let ψ : 𝓞 F × 𝓞 F →+ M :=
    { toFun := fun x => x.1 • p 0 + x.2 • p 1
      map_zero' := by simp
      map_add' := by intro x y; simp [add_smul]; abel }
  let g : 𝓞 F × 𝓞 F →+ (𝓞 F ⧸ I) × (𝓞 F ⧸ I) :=
    { toFun := fun x => (Ideal.Quotient.mk I x.1, Ideal.Quotient.mk I x.2)
      map_zero' := by simp
      map_add' := by intro x y; simp }
  have hgker : ∀ x y : 𝓞 F, (x, y) ∈ g.ker ↔ (N : 𝓞 F) ∣ x ∧ (N : 𝓞 F) ∣ y := by
    intro x y
    simp only [AddMonoidHom.mem_ker, g, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Prod.mk_eq_zero,
      Ideal.Quotient.eq_zero_iff_mem, hI, Ideal.mem_span_singleton]
  have hle : g.ker ≤ ψ.ker := by
    rintro ⟨x, y⟩ hx
    rw [hgker] at hx
    obtain ⟨⟨c, rfl⟩, ⟨d, rfl⟩⟩ := hx
    simp [ψ, hNp]
  have hrange : (ψ.range : Set M) = {x : M | N • x = 0} := by
    ext y
    simp only [SetLike.mem_coe, AddMonoidHom.mem_range, Set.mem_setOf_eq]
    constructor
    · rintro ⟨⟨x1, x2⟩, rfl⟩
      simp only [ψ, AddMonoidHom.coe_mk, ZeroHom.coe_mk, smul_add]
      rw [smul_comm, hp 0, smul_zero, smul_comm, hp 1, smul_zero, add_zero]
    · intro hy
      obtain ⟨a, b, rfl⟩ := hgen y hy
      exact ⟨(a, b), rfl⟩
  have hindψ : ψ.ker.index = N ^ (2 * Module.finrank ℚ F) := by
    rw [AddSubgroup.index_ker, ← hc]
    exact Nat.card_congr (Equiv.setCongr hrange)
  have hcardR : Nat.card (𝓞 F ⧸ I) = N ^ Module.finrank ℚ F := by
    have h1 := Ideal.absNorm_span_singleton (S := 𝓞 F) (N : 𝓞 F)
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at h1
    rw [hI, h1, ← map_natCast (algebraMap ℤ (𝓞 F)) N, Algebra.norm_algebraMap,
      NumberField.RingOfIntegers.rank]
    simp
  have hindg : g.ker.index = N ^ (2 * Module.finrank ℚ F) := by
    have hs : Function.Surjective g := by
      rintro ⟨u, v⟩
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective u
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective v
      exact ⟨(x, y), rfl⟩
    rw [AddSubgroup.index_ker, AddMonoidHom.range_eq_top.mpr hs]
    rw [Nat.card_congr (AddSubgroup.topEquiv).toEquiv, Nat.card_prod, hcardR, ← pow_add, two_mul]
  have hrel := AddSubgroup.relIndex_mul_index hle
  rw [hindψ, hindg] at hrel
  have hpos : 0 < N ^ (2 * Module.finrank ℚ F) := pow_pos (by omega) _
  have h1 : g.ker.relIndex ψ.ker = 1 := by
    have := Nat.eq_of_mul_eq_mul_right hpos (hrel.trans (one_mul _).symm)
    exact this
  have hk := AddSubgroup.relIndex_eq_one.mp h1
  have hmem : ((a, b) : 𝓞 F × 𝓞 F) ∈ ψ.ker := hab
  have := hk hmem
  exact (hgker a b).mp this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionCountLogConcavePrimePowers
section
open NumberField

namespace GlobalTheory

def killedBy {R : Type} [CommRing R] (M : Type) [AddCommGroup M] [Module R M] (I : Ideal R) :
    AddSubgroup M where
  carrier := {x | ∀ a ∈ I, a • x = 0}
  zero_mem' := fun a _ => smul_zero a
  add_mem' := fun hx hy a ha => by rw [smul_add, hx a ha, hy a ha, add_zero]
  neg_mem' := fun hx a ha => by rw [smul_neg, hx a ha, neg_zero]

theorem killedBy_anti {R : Type} [CommRing R] (M : Type) [AddCommGroup M] [Module R M]
    {I J : Ideal R} (h : I ≤ J) : killedBy M J ≤ killedBy M I :=
  fun _ hx a ha => hx a (h ha)

theorem card_eq_card_ker_mul_card_range {G H : Type} [AddCommGroup G] [AddCommGroup H]
    (f : G →+ H) : Nat.card G = Nat.card f.ker * Nat.card f.range := by
  rw [← AddSubgroup.index_ker, AddSubgroup.card_mul_index]

theorem card_torsion_pow_log_concave : ∀ (F : Type) [Field F] [NumberField F] (M : Type)
    [AddCommGroup M] [Module (𝓞 F) M] (𝔭 : Ideal (𝓞 F)), 𝔭.IsMaximal → ∀ k : ℕ,
    Finite {x : M // ∀ a ∈ 𝔭 ^ (k + 2), a • x = 0} →
    Nat.card {x : M // ∀ a ∈ 𝔭 ^ (k + 2), a • x = 0} * Nat.card {x : M // ∀ a ∈ 𝔭 ^ k, a • x = 0} ≤
      Nat.card {x : M // ∀ a ∈ 𝔭 ^ (k + 1), a • x = 0} ^ 2 := by
  intro F _ _ M _ _ 𝔭 hmax k hfin
  have hp0 : 𝔭 ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hmax (RingOfIntegers.not_isField F)
  have hp2 : 𝔭 ^ 2 ≠ ⊥ := pow_ne_zero 2 hp0
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_sup_span_eq (Ideal.pow_le_self two_ne_zero : 𝔭 ^ 2 ≤ 𝔭) hp2
  have haP : a ∈ 𝔭 := ha ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self a)
  have key : 𝔭 ^ (k + 2) ⊔ 𝔭 ^ k * Ideal.span {a} = 𝔭 ^ (k + 1) := by
    have e : 𝔭 ^ (k + 1) = 𝔭 ^ k * (𝔭 ^ 2 ⊔ Ideal.span {a}) := by rw [ha, pow_succ]
    rw [e, Ideal.mul_sup, ← pow_add]
  set A := killedBy M (𝔭 ^ (k + 2)) with hA
  set B := killedBy M (𝔭 ^ (k + 1)) with hB
  set C := killedBy M (𝔭 ^ k) with hC
  have eA : Nat.card {x : M // ∀ a ∈ 𝔭 ^ (k + 2), a • x = 0} = Nat.card A := rfl
  have eB : Nat.card {x : M // ∀ a ∈ 𝔭 ^ (k + 1), a • x = 0} = Nat.card B := rfl
  have eC : Nat.card {x : M // ∀ a ∈ 𝔭 ^ k, a • x = 0} = Nat.card C := rfl
  rw [eA, eB, eC]
  have hBA : B ≤ A := killedBy_anti M (Ideal.pow_le_pow_right (by omega))
  have hCB : C ≤ B := killedBy_anti M (Ideal.pow_le_pow_right (by omega))
  haveI : Finite A := hfin
  haveI : Finite B := Finite.of_injective _ (AddSubgroup.inclusion_injective hBA)

  have hAB : ∀ x ∈ A, a • x ∈ B := by
    intro x hx b hb
    rw [← mul_smul]
    apply hx
    rw [pow_succ]
    exact Ideal.mul_mem_mul hb haP

  have hiff : ∀ x ∈ A, (a • x ∈ C ↔ x ∈ B) := by
    intro x hx
    constructor
    · intro hax
      have hle : 𝔭 ^ (k + 1) ≤ LinearMap.ker (LinearMap.toSpanSingleton (𝓞 F) M x) := by
        rw [← key]
        apply sup_le
        · intro b hb
          simpa using hx b hb
        · rw [Ideal.mul_le]
          intro r hr s hs
          obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hs
          simp only [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
          rw [← mul_assoc, mul_smul]
          exact hax _ (Ideal.mul_mem_right c _ hr)
      intro b hb
      simpa using hle hb
    · intro hxB b hb
      rw [← mul_smul]
      apply hxB
      rw [pow_succ]
      exact Ideal.mul_mem_mul hb haP
  let π : M →+ M ⧸ C := QuotientAddGroup.mk' C
  let g : A →+ M ⧸ C := (π.comp (DistribMulAction.toAddMonoidHom M a)).comp A.subtype
  let h : B →+ M ⧸ C := π.comp B.subtype
  have hg : Nat.card g.ker = Nat.card B := by
    have : g.ker = B.addSubgroupOf A := by
      ext x
      simp only [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf, g, π,
        AddMonoidHom.comp_apply, AddSubgroup.coe_subtype, DistribMulAction.toAddMonoidHom_apply,
        QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
      exact hiff x.1 x.2
    rw [this]
    exact Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe hBA).toEquiv
  have hh : Nat.card h.ker = Nat.card C := by
    have : h.ker = C.addSubgroupOf B := by
      ext x
      simp only [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf, h, π,
        AddMonoidHom.comp_apply, AddSubgroup.coe_subtype,
        QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
    rw [this]
    exact Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe hCB).toEquiv
  have hrange : g.range ≤ h.range := by
    rintro _ ⟨x, rfl⟩
    exact ⟨⟨a • (x : M), hAB x.1 x.2⟩, rfl⟩
  haveI : Finite h.range := Finite.of_surjective _ h.rangeRestrict_surjective
  have hcard : Nat.card g.range ≤ Nat.card h.range :=
    Nat.card_le_card_of_injective _ (AddSubgroup.inclusion_injective hrange)
  have e1 := card_eq_card_ker_mul_card_range g
  have e2 := card_eq_card_ker_mul_card_range h
  rw [hg] at e1
  rw [hh] at e2
  rw [e1, sq]
  nth_rewrite 3 [e2]
  calc Nat.card B * Nat.card g.range * Nat.card C
      ≤ Nat.card B * Nat.card h.range * Nat.card C := by gcongr
    _ = Nat.card B * (Nat.card C * Nat.card h.range) := by ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionCountMultiplicativePrimePowers
section
open NumberField

namespace GlobalTheory.PrimaryTorsionBlocks

variable {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]

def killedBy (I : Ideal R) : AddSubgroup M where
  carrier := {x | ∀ a ∈ I, a • x = 0}
  zero_mem' := fun a _ => smul_zero a
  add_mem' := fun {x y} hx hy a ha => by
    show a • (x + y) = 0
    rw [smul_add, hx a ha, hy a ha, add_zero]
  neg_mem' := fun {x} hx a ha => by
    show a • (-x) = 0
    rw [smul_neg, hx a ha, neg_zero]

def annOf (x : M) : Ideal R := LinearMap.ker (LinearMap.toSpanSingleton R M x)

lemma mem_annOf {x : M} {a : R} : a ∈ annOf x ↔ a • x = 0 := by
  simp [annOf]

lemma mem_killedBy_iff {I : Ideal R} {x : M} : x ∈ killedBy (M := M) I ↔ I ≤ annOf x :=
  ⟨fun h a ha => mem_annOf.2 (h a ha), fun h a ha => mem_annOf.1 (h ha)⟩

theorem card_killedBy_block (P J : Ideal R) (n : R) (e : ℕ)
    (hspan : Ideal.span {n} = P ^ e * J) (hcop : P ⊔ J = ⊤)
    (hlift : ∀ j : ℕ, ∀ y : M, n ^ j • y = 0 → ∃ z : M, n ^ (j + 1) • z = 0 ∧ n • z = y)
    (j : ℕ) :
    Nat.card (killedBy (M := M) (P ^ (e * (j + 1)))) =
      Nat.card (killedBy (M := M) (P ^ (e * j))) * Nat.card (killedBy (M := M) (P ^ e)) := by
  have hpow : ∀ k : ℕ, Ideal.span {n ^ k} = P ^ (e * k) * J ^ k := by
    intro k
    rw [← Ideal.span_singleton_pow, hspan, mul_pow, pow_mul]
  have hcop' : ∀ a b : ℕ, P ^ a ⊔ J ^ b = ⊤ := by
    intro a b
    exact Ideal.isCoprime_iff_sup_eq.1 ((Ideal.isCoprime_iff_sup_eq.2 hcop).pow)
  have hnmem : ∀ k : ℕ, n ^ k ∈ P ^ (e * k) := by
    intro k
    have : n ^ k ∈ Ideal.span {n ^ k} := Ideal.mem_span_singleton_self _
    rw [hpow k] at this
    exact (Ideal.mul_le_left : P ^ (e * k) * J ^ k ≤ P ^ (e * k)) this
  have hn : n ∈ P ^ e := by simpa using hnmem 1
  have hexp : e * (j + 1) = e * j + e := by ring
  have hle1 : P ^ (e * (j + 1)) ≤ P ^ (e * j) := Ideal.pow_le_pow_right (by rw [hexp]; omega)
  have hle2 : P ^ (e * (j + 1)) ≤ P ^ e := Ideal.pow_le_pow_right (by rw [hexp]; omega)

  let f : killedBy (M := M) (P ^ (e * (j + 1))) →+ killedBy (M := M) (P ^ (e * j)) :=
    AddMonoidHom.mk' (fun x => ⟨n • (x : M), fun a ha => by
      rw [smul_smul]
      apply x.2
      rw [hexp, pow_add]
      exact Ideal.mul_mem_mul ha hn⟩)
      (fun x y => by ext; simp [smul_add])
  have hsurj : Function.Surjective f := by
    rintro ⟨y, hy⟩
    have hy0 : n ^ j • y = 0 := hy _ (hnmem j)
    obtain ⟨z, hz, hzy⟩ := hlift j y hy0
    have h1 : (1 : R) ∈ P ^ (e * (j + 1)) ⊔ J ^ (j + 1) := by rw [hcop']; trivial
    obtain ⟨s, hs, t, ht, hst⟩ := Submodule.mem_sup.1 h1
    refine ⟨⟨t • z, fun a ha => ?_⟩, ?_⟩
    · rw [smul_smul]
      have hat : a * t ∈ Ideal.span {n ^ (j + 1)} := by
        rw [hpow]
        exact Ideal.mul_mem_mul ha ht
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hat
      rw [← hc, mul_smul, hz, smul_zero]
    · ext
      show n • t • z = y
      rw [smul_comm, hzy]
      have hsy : s • y = 0 := hy s (hle1 hs)
      calc t • y = s • y + t • y := by rw [hsy, zero_add]
        _ = (s + t) • y := (add_smul s t y).symm
        _ = y := by rw [hst, one_smul]
  have hsup : P ^ e ≤ P ^ (e * (j + 1)) ⊔ Ideal.span {n} := by
    have hc : P ^ (e * j) ⊔ J = ⊤ := by simpa using hcop' (e * j) 1
    have : P ^ e = P ^ e * (P ^ (e * j) ⊔ J) := by rw [hc, Ideal.mul_top]
    rw [this, Ideal.mul_sup, hspan, ← pow_add, hexp, add_comm (e * j) e]
  have hker : Nat.card f.ker = Nat.card (killedBy (M := M) (P ^ e)) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨(x.1 : M), ?_⟩
        invFun := fun x => ⟨⟨(x : M), fun a ha => x.2 a (hle2 ha)⟩, ?_⟩
        left_inv := fun x => rfl
        right_inv := fun x => rfl }
    · have hx1 := mem_killedBy_iff.1 x.1.2
      have hx2 : n • (x.1 : M) = 0 := by
        have := x.2
        rw [AddMonoidHom.mem_ker] at this
        exact congrArg Subtype.val this
      refine mem_killedBy_iff.2 (le_trans hsup (sup_le hx1 ?_))
      rw [Ideal.span_singleton_le_iff_mem]
      exact mem_annOf.2 hx2
    · rw [AddMonoidHom.mem_ker]
      ext
      exact x.2 n hn
  have hmul := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.ker
  rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective f hsurj).toEquiv, hker] at hmul
  exact hmul

end GlobalTheory.PrimaryTorsionBlocks

namespace GlobalTheory

open GlobalTheory.PrimaryTorsionBlocks in

theorem card_primaryTorsion_mul_blocks :
    ∀ (F : Type) [Field F] [NumberField F] (M : Type) [AddCommGroup M] [Module (𝓞 F) M] (N : ℕ), 1 ≤ N →
    (∀ j : ℕ, Finite {x : M // (N ^ j) • x = 0}) →
    (∀ j : ℕ, ∀ y : M, (N ^ j) • y = 0 → ∃ z : M, (N ^ (j + 1)) • z = 0 ∧ N • z = y) →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → (N : 𝓞 F) ∈ 𝔭 →
    ∃ e : ℕ, 1 ≤ e ∧ ∀ j : ℕ, Nat.card {x : M // ∀ a ∈ 𝔭 ^ (e * (j + 1)), a • x = 0} =
      Nat.card {x : M // ∀ a ∈ 𝔭 ^ (e * j), a • x = 0} * Nat.card {x : M // ∀ a ∈ 𝔭 ^ e, a • x = 0} := by
  classical
  intro F _ _ M _ _ N hN _ hlift 𝔭 h𝔭 hN𝔭
  have hne : (N : 𝓞 F) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hI : Ideal.span {(N : 𝓞 F)} ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  obtain ⟨Q, hPQ, hspan⟩ := Ideal.eq_prime_pow_mul_coprime hI 𝔭
  refine ⟨Multiset.count 𝔭 (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(N : 𝓞 F)})),
    ?_, fun j => ?_⟩
  · by_contra h0
    have h0' : Multiset.count 𝔭 (UniqueFactorizationMonoid.normalizedFactors
        (Ideal.span {(N : 𝓞 F)})) = 0 := by omega
    rw [h0', pow_zero, one_mul] at hspan
    have hQ : Q ≤ 𝔭 := by rw [← hspan, Ideal.span_singleton_le_iff_mem]; exact hN𝔭
    rw [sup_eq_left.2 hQ] at hPQ
    exact h𝔭.ne_top hPQ
  · have hlift' : ∀ j : ℕ, ∀ y : M, (N : 𝓞 F) ^ j • y = 0 →
        ∃ z : M, (N : 𝓞 F) ^ (j + 1) • z = 0 ∧ (N : 𝓞 F) • z = y := by
      intro j y hy
      rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul] at hy
      obtain ⟨z, h1, h2⟩ := hlift j y hy
      refine ⟨z, ?_, ?_⟩
      · rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]; exact h1
      · rw [Nat.cast_smul_eq_nsmul]; exact h2
    exact card_killedBy_block 𝔭 Q (N : 𝓞 F) _ hspan hPQ hlift' j

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFreeOver
section
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.GoodEtale

def Hart (A R M : Type) [CommRing A] [CommRing R] [Algebra A R] [AddCommGroup M] [Module R M] : Prop :=
  ∀ a : A, a ≠ 0 → ∀ m : M,
    (∀ p : Ideal A, p.IsPrime → p.height ≤ 1 →
      ∃ u : A, u ∉ p ∧ ∃ m' : M, algebraMap A R u • m = algebraMap A R a • m') →
    ∃ m' : M, m = algebraMap A R a • m'

def TorsionFreeOver (A R M : Type) [CommRing A] [CommRing R] [Algebra A R] [AddCommGroup M]
    [Module R M] : Prop :=
  ∀ a : A, a ≠ 0 → ∀ m : M, algebraMap A R a • m = 0 → m = 0

def EtaleLow (A R C : Type) [CommRing A] [CommRing R] [Algebra A R] [CommRing C] [Algebra R C] : Prop :=
  ∀ (P : Ideal R) [P.IsPrime], (P.comap (algebraMap A R)).height ≤ 1 →
    Algebra.Etale (Localization.AtPrime P) (Localization.AtPrime P ⊗[R] C)

end GlobalTheory.GoodEtale

example (k : Type) [Field k] : GlobalTheory.GoodEtale.Hart k k k := fun a ha m _ =>
  ⟨a⁻¹ * m, by simp [smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ ha]⟩

example (A : Type) [CommRing A] : GlobalTheory.GoodEtale.TorsionFreeOver A A Unit := fun _ _ _ _ => rfl
end
end

