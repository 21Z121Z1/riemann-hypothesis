import Mathlib
import GroundTheory.AutomorphicForms.Bundle0020
import GroundTheory.AutomorphicForms.FiniteLengthSubquotient

-- bundled from GroundTheory.AutomorphicForms.AnisotropicDivisionCompact
section
set_option maxSynthPendingDepth 1

open Module Matrix TensorProduct Topology NumberField IsDedekindDomain
open scoped NumberField.AdeleRing

set_option linter.unusedSectionVars false

namespace GroundTheory.Automorphic

noncomputable section

namespace Anisotropic

variable (K : Type*) [Field K] [NumberField K] (D : Type*) [DivisionRing D] [Algebra K D]

abbrev adeleTensorTopology : TopologicalSpace (𝔸[K] ⊗[K] D) :=
  moduleTopology 𝔸[K] (𝔸[K] ⊗[K] D)

attribute [local instance] adeleTensorTopology

theorem isModuleTopology_adeleTensor : IsModuleTopology 𝔸[K] (𝔸[K] ⊗[K] D) := ⟨rfl⟩

attribute [local instance] isModuleTopology_adeleTensor

theorem isTopologicalRing_adeleTensor [FiniteDimensional K D] :
    IsTopologicalRing (𝔸[K] ⊗[K] D) :=
  IsModuleTopology.isTopologicalRing 𝔸[K] _

attribute [local instance] isTopologicalRing_adeleTensor

def rationalUnits : Dˣ →* (𝔸[K] ⊗[K] D)ˣ :=
  Units.map (Algebra.TensorProduct.includeRight : D →ₐ[K] 𝔸[K] ⊗[K] D).toRingHom.toMonoidHom

def scalarUnits : (𝔸[K])ˣ →* (𝔸[K] ⊗[K] D)ˣ :=
  Units.map (algebraMap 𝔸[K] (𝔸[K] ⊗[K] D)).toMonoidHom

variable {K D}

theorem baseMap_ofId_eq_includeRight (ξ : K ⊗[K] D) :
    baseMap (Algebra.ofId K 𝔸[K]) ξ =
      Algebra.TensorProduct.includeRight (Algebra.TensorProduct.lid K D ξ) := by
  induction ξ using TensorProduct.induction_on with
  | zero => simp
  | tmul k e =>
    rw [baseMap, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lid_tmul,
      Algebra.TensorProduct.includeRight_apply, ← TensorProduct.smul_tmul, Algebra.ofId_apply,
      Algebra.algebraMap_eq_smul_one]
    rfl
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

theorem rationalUnits'_eq (ξ : (K ⊗[K] D)ˣ) :
    rationalUnits' ξ = rationalUnits K D
      (Units.map (Algebra.TensorProduct.lid K D : K ⊗[K] D →ₐ[K] D).toRingHom.toMonoidHom ξ) :=
  Units.ext (baseMap_ofId_eq_includeRight (ξ : K ⊗[K] D))

variable [FiniteDimensional K D] {d : ℕ} (b : Basis (Fin d) K D)

theorem continuous_coords_adele : Continuous (coords b 𝔸[K]) :=
  IsModuleTopology.continuous_of_linearMap (coords b 𝔸[K]).toLinearMap

theorem continuous_coords_adele_symm : Continuous (coords b 𝔸[K]).symm := by
  have h : ⇑(coords b 𝔸[K]).symm = fun y => ∑ k, y k • baseBasis b 𝔸[K] k := by
    funext y
    exact Module.Basis.equivFun_symm_apply _ y
  rw [h]
  exact continuous_finsetSum _ fun k _ => (continuous_apply k).smul continuous_const

def coordsHomeomorph : 𝔸[K] ⊗[K] D ≃ₜ (Fin d → 𝔸[K]) where
  toEquiv := (coords b 𝔸[K]).toEquiv
  continuous_toFun := continuous_coords_adele b
  continuous_invFun := continuous_coords_adele_symm b

variable (K D) in
theorem t2Space_adeleTensor : T2Space (𝔸[K] ⊗[K] D) :=
  (coordsHomeomorph (Module.finBasis K D)).isEmbedding.t2Space

attribute [local instance] t2Space_adeleTensor

theorem continuous_rmat_adele : Continuous (rmat b 𝔸[K]) :=
  continuous_pi fun _ => continuous_pi fun l => (continuous_apply l).comp
    ((continuous_coords_adele b).comp (continuous_const.mul continuous_id))

theorem continuous_rmatUnits : Continuous (rmatUnits b 𝔸[K]) :=
  Units.continuous_iff.2 ⟨(continuous_rmat_adele b).comp Units.continuous_val,
    (continuous_rmat_adele b).comp Units.continuous_coe_inv⟩

theorem isCompact_preimage_rmatUnits {C : Set (GL (Fin d) 𝔸[K])} (hC : IsCompact C) :
    IsCompact (rmatUnits b 𝔸[K] ⁻¹' C) := by
  let ψ : Matrix (Fin d) (Fin d) 𝔸[K] → 𝔸[K] ⊗[K] D := fun A =>
    (coords b 𝔸[K]).symm (coords b 𝔸[K] 1 ᵥ* A)
  have hψ : Continuous ψ :=
    (continuous_coords_adele_symm b).comp (continuous_const.matrix_vecMul continuous_id)
  have hψr : ∀ w : 𝔸[K] ⊗[K] D, ψ (rmat b 𝔸[K] w) = w := by
    intro w
    simp only [ψ]
    rw [← coords_mul, one_mul, LinearEquiv.symm_apply_apply]
  let Fp : GL (Fin d) 𝔸[K] → (𝔸[K] ⊗[K] D) × (𝔸[K] ⊗[K] D)ᵐᵒᵖ := fun g =>
    (ψ (g : Matrix (Fin d) (Fin d) 𝔸[K]), MulOpposite.op (ψ (↑g⁻¹ : Matrix (Fin d) (Fin d) 𝔸[K])))
  have hFp : Continuous Fp := (hψ.comp Units.continuous_val).prodMk
    (MulOpposite.continuous_op.comp (hψ.comp Units.continuous_coe_inv))
  have hsub : rmatUnits b 𝔸[K] ⁻¹' C ⊆ Units.embedProduct _ ⁻¹' (Fp '' C) := by
    intro w hw
    refine ⟨_, hw, ?_⟩
    simp only [Fp, Units.embedProduct_apply]
    exact Prod.ext (hψr (w : 𝔸[K] ⊗[K] D)) (congrArg MulOpposite.op (hψr (↑w⁻¹ : 𝔸[K] ⊗[K] D)))
  have hcl : IsClosed (rmatUnits b 𝔸[K] ⁻¹' C) := hC.isClosed.preimage (continuous_rmatUnits b)
  exact (Units.isClosedEmbedding_embedProduct.isCompact_preimage (hC.image hFp)).of_isClosed_subset
    hcl hsub

theorem exists_isCompact_normOneUnits :
    ∃ Ω : Set (𝔸[K] ⊗[K] D)ˣ, IsCompact Ω ∧ ∀ x ∈ normOneUnits b,
      ∃ δ : Dˣ, (rationalUnits K D δ)⁻¹ * x ∈ Ω := by
  obtain ⟨C, hC, h⟩ := exists_isCompact_rmatUnits b
  refine ⟨rmatUnits b 𝔸[K] ⁻¹' C, isCompact_preimage_rmatUnits b hC, fun x hx => ?_⟩
  obtain ⟨ξ, hξ⟩ := h x hx
  exact ⟨_, by rw [← rationalUnits'_eq]; exact hξ⟩

end Anisotropic

end

end GroundTheory.Automorphic
end

-- bundled from GroundTheory.AutomorphicForms.FiniteLengthJacquet
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Automorphic

open Function

namespace Parabolic

open Function Matrix Iwasawa

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

section Congr

variable {α α' : Type*} [LinearOrder α] [LinearOrder α'] {β : Fin n → α} {γ : Fin n → α'}

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem eq_iff_eq_of_lt_iff (h : ∀ i j, β i < β j ↔ γ i < γ j) (i j : Fin n) :
    β i = β j ↔ γ i = γ j := by
  constructor
  · intro e
    rcases lt_trichotomy (γ i) (γ j) with hl | he | hg
    · exact absurd ((h i j).2 hl) (by rw [e]; exact lt_irrefl _)
    · exact he
    · exact absurd ((h j i).2 hg) (by rw [e]; exact lt_irrefl _)
  · intro e
    rcases lt_trichotomy (β i) (β j) with hl | he | hg
    · exact absurd ((h i j).1 hl) (by rw [e]; exact lt_irrefl _)
    · exact he
    · exact absurd ((h j i).1 hg) (by rw [e]; exact lt_irrefl _)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in

theorem blockUpper_congr (h : ∀ i j, β i < β j ↔ γ i < γ j) :
    blockUpper F n β = blockUpper F n γ := by
  ext g
  simp only [mem_blockUpper, Matrix.BlockTriangular]
  exact forall_congr' fun i => forall_congr' fun j => imp_congr_left (h j i)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in

theorem unipotentRadical_congr (h : ∀ i j, β i < β j ↔ γ i < γ j) :
    unipotentRadical F n β = unipotentRadical F n γ := by
  ext g
  rw [mem_unipotentRadical, mem_unipotentRadical, blockUpper_congr h]
  exact and_congr_right fun _ => forall_congr' fun i => forall_congr' fun j =>
    imp_congr_left (eq_iff_eq_of_lt_iff h i j)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem blockRank_lt_iff {i j : Fin n} : blockRank β i < blockRank β j ↔ β i < β j := by
  refine ⟨fun h => ?_, blockRank_lt⟩
  by_contra h'
  rcases (not_lt.1 h').lt_or_eq with h'' | h''
  · exact absurd (blockRank_lt h'') (by omega)
  · exact absurd (blockRank_eq h''.symm) (by omega)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem blockRank_lt_card (β : Fin n → α) (i : Fin n) : blockRank β i < n := by
  have : (Finset.univ.filter fun j => β j < β i) ⊂ Finset.univ :=
    Finset.ssubset_iff_subset_ne.2 ⟨Finset.subset_univ _, fun h => by
      have := h ▸ Finset.mem_univ i
      simp at this⟩
  simpa [blockRank] using Finset.card_lt_card this

def rankFun (β : Fin n → α) : Fin n → Fin n := fun i => ⟨blockRank β i, blockRank_lt_card β i⟩

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem rankFun_lt_iff (β : Fin n → α) (i j : Fin n) :
    ((rankFun β i : Fin n) : ℕ) < (rankFun β j : ℕ) ↔ β i < β j :=
  blockRank_lt_iff

end Congr

section Jacquet

variable {V V' : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
  {X : Representation ℂ (GL (Fin n) F) V} {π : Representation ℂ (GL (Fin n) F) V'}

theorem jacquetMap_surjective (p : Representation.IntertwiningMap X π) (hp : Surjective p)
    (γ : Fin n → ℕ) : Surjective (jacquetMap F n γ p) := by
  intro y
  obtain ⟨v, rfl⟩ := Representation.Coinvariants.mk_surjective _ y
  obtain ⟨u, rfl⟩ := hp v
  exact ⟨Representation.Coinvariants.mk _ u, jacquetMap_mk _ _⟩

theorem jacquetMap_injective (hX : IsSmooth X) (hπ : IsSmooth π)
    (i : Representation.IntertwiningMap X π) (hi : Injective i) (γ : Fin n → ℕ) :
    Injective (jacquetMap F n γ i) := by
  have hex := exact_jacquetMap (β := γ) hX hπ (0 : Representation.IntertwiningMap X X) i
    (fun y => ⟨fun hy => ⟨0, by
      show (0 : V) = y
      exact (hi (hy.trans (map_zero i).symm)).symm⟩, by rintro ⟨z, rfl⟩; exact map_zero i⟩)
  refine (injective_iff_map_eq_zero _).2 fun y hy => ?_
  obtain ⟨z, hz⟩ := (hex y).1 hy
  obtain ⟨z, rfl⟩ := Representation.Coinvariants.mk_surjective _ z
  rw [jacquetMap_mk] at hz
  rw [← hz]
  exact map_zero (Representation.Coinvariants.mk _)

theorem _root_.GroundTheory.Automorphic.IsSubquotient.jacquetRep (hX : IsSmooth X) (h : IsSubquotient π X) (γ : Fin n → ℕ) :
    IsSubquotient (jacquetRep F n γ π) (jacquetRep F n γ X) := by
  obtain ⟨C, p, hp⟩ := h
  exact .of_injective_of_surjective (jacquetMap F n γ (subrepInclusion C))
    (jacquetMap_injective (isSmooth_subrep hX C) hX _ (fun a b h => Subtype.ext h) γ)
    (jacquetMap F n γ p) (jacquetMap_surjective p hp γ)

theorem surjective_frobeniusParabolic [Nontrivial V'] {δ : Fin n → ℕ} {U : Type*}
    [AddCommGroup U] [Module ℂ U] {τ : Representation ℂ (levi F n δ) U} [τ.IsIrreducible]
    (hπ : IsSmooth π) (Φ : Representation.IntertwiningMap π (parabolicInd F n δ τ))
    (hΦ : Injective Φ) : Surjective (frobeniusParabolic F n δ τ hπ Φ) := by
  rcases Representation.IsIrreducible.surjective_or_eq_zero
    (frobeniusParabolic F n δ τ hπ Φ) with h | h
  · exact h
  · exfalso
    have h0 : Φ = 0 := (frobeniusParabolic F n δ τ hπ).injective (h.trans (map_zero _).symm)
    obtain ⟨v, hv⟩ := exists_ne (0 : V')
    exact hv (hΦ (by rw [map_zero, h0]; rfl))

end Jacquet

end Parabolic

section Irreducible

variable {G : Type*} [Group G] {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
  [Module ℂ W] {ρ : Representation ℂ G V} {π : Representation ℂ G W}

theorem IsSubquotient.exists_bijective [π.IsIrreducible] [ρ.IsIrreducible]
    (h : IsSubquotient π ρ) : ∃ e : Representation.IntertwiningMap π ρ, Bijective e := by
  obtain ⟨C, p, hp⟩ := h
  obtain ⟨x, hx⟩ := exists_ne_zero_of_isIrreducible (ρ := π)
  have hC : C = ⊤ := (eq_bot_or_eq_top C).resolve_left fun hC => hx (by
    obtain ⟨c, rfl⟩ := hp x
    have hc : (c : V) ∈ (⊥ : Subrepresentation ρ).toSubmodule := by rw [← hC]; exact c.2
    rw [show c = 0 from Subtype.ext ((Submodule.mem_bot ℂ).1 hc), map_zero])
  have hCtop : ∀ v : V, v ∈ C.toSubmodule := fun v => by rw [hC]; trivial

  let K : Subrepresentation ρ := ⟨(LinearMap.ker p.toLinearMap).map C.toSubmodule.subtype, by
    rintro g _ ⟨c, hc, rfl⟩
    refine ⟨C.toRepresentation g c, ?_, rfl⟩
    have hc' : p c = 0 := hc
    show p (C.toRepresentation g c) = 0
    rw [Representation.IntertwiningMap.isIntertwining, hc', map_zero]⟩
  have hK : K = ⊥ := (eq_bot_or_eq_top K).resolve_right fun hK => hx (by
    obtain ⟨c, rfl⟩ := hp x
    have hc : (c : V) ∈ K.toSubmodule := by rw [hK]; trivial
    obtain ⟨c', hc', hcc'⟩ := hc
    rw [show c = c' from Subtype.ext hcc'.symm]
    exact hc')
  have hpinj : Injective p := (injective_iff_map_eq_zero _).2 fun c hc => Subtype.ext (by
    have hmem : (c : V) ∈ K.toSubmodule := ⟨c, hc, rfl⟩
    rw [hK] at hmem
    exact (Submodule.mem_bot ℂ).1 hmem)
  let e₀ : C.toSubmodule ≃ₗ[ℂ] W := LinearEquiv.ofBijective p.toLinearMap ⟨hpinj, hp⟩
  have he₀ : ∀ c, e₀ c = p c := fun c => rfl
  refine ⟨⟨C.toSubmodule.subtype ∘ₗ e₀.symm.toLinearMap, fun g => LinearMap.ext fun y => ?_⟩,
    ⟨?_, fun v => ⟨e₀ ⟨v, hCtop v⟩, by simp⟩⟩⟩
  · obtain ⟨c, rfl⟩ := e₀.surjective y
    have h1 : π g (e₀ c) = e₀ (C.toRepresentation g c) := by
      rw [he₀, he₀, Representation.IntertwiningMap.isIntertwining]
    simp only [LinearMap.coe_comp, comp_apply, LinearEquiv.coe_coe, h1,
      LinearEquiv.symm_apply_apply, Submodule.coe_subtype]
    rfl
  · intro a b hab
    exact e₀.symm.injective (Subtype.ext hab)

end Irreducible

end GroundTheory.Automorphic
end
end

