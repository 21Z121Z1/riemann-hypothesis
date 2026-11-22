import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0135
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0124
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHilbertSchemeRepresentableOfIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Bundle0001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0165
import Formalism.SatakeDualWeyl.Statement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0081
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0006
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0086
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0004

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteFlatRankClosedSubschemeOfQuotientBasis
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

namespace GlobalTheory.HilbAff

theorem good_xI : ∀ (A B C : Type) [CommRing A] [CommRing B] [Algebra A B] [CommRing C] [Algebra A C] (J : Ideal (C ⊗[A] B)) {r : ℕ} (v : Fin r → B), LinearIndependent C (fun k => Ideal.Quotient.mk J ((1 : C) ⊗ₜ[A] v k)) → Submodule.span C (Set.range (fun k => Ideal.Quotient.mk J ((1 : C) ⊗ₜ[A] v k))) = ⊤ → GlobalTheory.HilbAff.Good A B r (Spec.map (CommRingCat.ofHom (algebraMap A C))) (GlobalTheory.HilbAff.xI A B C J) := by
  intro A B C _ _ _ _ _ J r v hli hsp
  let bas : Module.Basis (Fin r) C ((C ⊗[A] B) ⧸ J) := Module.Basis.mk hli hsp.ge
  haveI : Module.Free C ((C ⊗[A] B) ⧸ J) := Module.Free.of_basis bas
  haveI : Module.Finite C ((C ⊗[A] B) ⧸ J) := Module.Finite.of_basis bas
  have hsurj : Function.Surjective ((Ideal.Quotient.mk J).comp
      (Algebra.TensorProduct.comm A B C).toRingHom) :=
    (Ideal.Quotient.mk_surjective).comp (Algebra.TensorProduct.comm A B C).surjective
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk J).comp
      (Algebra.TensorProduct.comm A B C).toRingHom))) :=
    IsClosedImmersion.spec_of_surjective _ hsurj
  have hsnd : (Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk J).comp
      (Algebra.TensorProduct.comm A B C).toRingHom)) ≫ (pullbackSpecIso A B C).inv) ≫
      pullback.snd _ _ = Spec.map (CommRingCat.ofHom (algebraMap C ((C ⊗[A] B) ⧸ J))) := by
    rw [Category.assoc, pullbackSpecIso_inv_snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
  refine good_ker A B r _ _ ?_ ?_ ?_
  · rw [hsnd]
    exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  · rw [hsnd]
    exact Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  · intro y
    rw [hsnd]
    refine (Scheme.Hom.finrank_SpecMap_algebraMap C ((C ⊗[A] B) ⧸ J) y).trans ?_
    haveI : Nontrivial C := by
      let p : PrimeSpectrum C := y
      refine ⟨⟨0, 1, fun h => p.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)⟩⟩
      rw [← h]; exact p.asIdeal.zero_mem
    rw [Module.rankAtStalk_eq_finrank_of_free, Module.finrank_eq_card_basis bas, Fintype.card_fin]
    rfl

end GlobalTheory.HilbAff
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHilbertSchemeRepresentableOfIsoStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GlobalTheory.HilbertSch
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isHilbertSchemeRepresentable_of_iso : ∀ {S Z S' Z' : Scheme.{0}} (z : Z ⟶ S) (z' : Z' ⟶ S') (eS : S' ≅ S) (eZ : Z' ≅ Z), eZ.hom ≫ z = z' ≫ eS.hom → ∀ r : ℕ, IsHilbRep z' r → IsHilbRep z r := by
  first | exact @GlobalTheory.HilbertSch.isHilbRep_transfer | exact GlobalTheory.HilbertSch.isHilbRep_transfer | (intros; apply GlobalTheory.HilbertSch.isHilbRep_transfer <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsInCharacterIsotypicPartTwistedInduction
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin.IndIso

theorem sum_dite_mem {G M : Type} [Group G] [Fintype G] [AddCommMonoid M] (H : Subgroup G)
    (f : H → M) : ∑ z : G, (if h : z ∈ H then f ⟨z, h⟩ else 0) = ∑ h : H, f h := by
  rw [← Fintype.sum_subtype_add_sum_subtype (fun z => z ∈ H)]
  have h2 : ∑ i : {x // ¬ x ∈ H}, (if h : (i : G) ∈ H then f ⟨i, h⟩ else 0) = 0 :=
    Finset.sum_eq_zero fun i _ => dif_neg i.2
  rw [h2, add_zero]
  exact Fintype.sum_congr _ _ fun i => dif_pos i.2

theorem star_ext_zero {G : Type} [Group G] (H : Subgroup G) (c : H → ℂ) (z : G) :
    star (ext0 H c z) = ext0 H (fun h => star (c h)) z := by
  unfold ext0; split_ifs <;> simp

theorem reidx {G M : Type} [Group G] [Fintype G] [AddCommMonoid M] [Module ℂ M] (H : Subgroup G)
    (a b : G) (c : H → ℂ) (T : G → M) :
    ∑ x : G, ext0 H c (a * x * b) • T x = ∑ h : H, c h • T (a⁻¹ * h * b⁻¹) := by
  rw [Fintype.sum_equiv ((Equiv.mulLeft a).trans (Equiv.mulRight b)) _
    (fun z => ext0 H c z • T (a⁻¹ * z * b⁻¹)) (fun x => by simp [mul_assoc])]
  rw [← sum_dite_mem H (fun h => c h • T (a⁻¹ * h * b⁻¹))]
  refine Fintype.sum_congr _ _ fun z => ?_
  unfold ext0; split_ifs <;> simp

end GlobalTheory.Shin.IndIso

namespace GlobalTheory.Shin.IndIso

theorem kills_ind : ∀ (G : Type) [Group G] [Finite G] (H : Subgroup G) (τ : G → G) (φ Y : H → ℂ), Kills φ Y →
    Kills (fun x => (Nat.card H : ℂ)⁻¹ * ∑ᶠ y : G, ext0 H φ (y⁻¹ * x * τ y)) (ind H Y) := by
  intro G _ _ H τ φ Y hK V _ _ _ ρ hρ
  letI : Fintype G := Fintype.ofFinite G
  have hHc : (Nat.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hGc : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'

  have hres : ∑ᶠ h : H, star (Y h) * LinearMap.trace ℂ V ((ρ.comp H.subtype) h) = 0 := by
    rw [finsum_eq_sum_of_fintype]
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
    simp only [ind, finsum_eq_sum_of_fintype, star_mul', star_inv₀, star_natCast, star_sum, star_ext_zero] at hρ
    simp only [mul_assoc, ← Finset.mul_sum] at hρ
    have hρ' := (mul_eq_zero.mp hρ).resolve_left (inv_ne_zero hHc)
    have trc : ∀ g x : G, LinearMap.trace ℂ V (ρ (g * (x * g⁻¹))) = LinearMap.trace ℂ V (ρ x) := by
      intro g x
      rw [map_mul ρ, map_mul ρ, LinearMap.trace_mul_comm, mul_assoc, ← map_mul ρ, ← map_mul ρ]
      simp
    simp only [Finset.sum_mul] at hρ'
    rw [Finset.sum_comm] at hρ'
    have key : ∀ g : G, ∑ x : G, ext0 H (fun h => star (Y h)) (g⁻¹ * (x * g)) * LinearMap.trace ℂ V (ρ x)
        = ∑ h : H, star (Y h) * LinearMap.trace ℂ V (ρ h) := by
      intro g
      have := reidx (M := ℂ) H g⁻¹ g (fun h => star (Y h)) (fun x => LinearMap.trace ℂ V (ρ x))
      simp only [smul_eq_mul, inv_inv, mul_assoc] at this
      rw [this]
      exact Fintype.sum_congr _ _ fun h => by rw [trc]
    simp only [key, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hρ'
    rw [← Nat.card_eq_fintype_card] at hρ'
    exact (mul_eq_zero.mp hρ').resolve_left hGc
  have hk := hK V (ρ.comp H.subtype) hres
  rw [finsum_eq_sum_of_fintype] at hk
  simp only [MonoidHom.comp_apply, Subgroup.coe_subtype] at hk

  rw [finsum_eq_sum_of_fintype]
  simp only [finsum_eq_sum_of_fintype, star_mul', star_inv₀, star_natCast, star_sum, star_ext_zero, mul_smul,
    Finset.sum_smul]
  rw [← Finset.smul_sum, Finset.sum_comm]
  have key2 : ∀ y : G, ∑ x : G, ext0 H (fun h => star (φ h)) (y⁻¹ * x * τ y) • ρ x = 0 := by
    intro y
    rw [reidx H y⁻¹ (τ y) (fun h => star (φ h)) (fun x => ρ x)]
    simp only [inv_inv, map_mul]
    have : ∑ h : H, star (φ h) • (ρ y * ρ h * ρ (τ y)⁻¹) = ρ y * (∑ h : H, star (φ h) • ρ h) * ρ (τ y)⁻¹ := by
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Fintype.sum_congr _ _ fun h => ?_
      rw [mul_smul_comm, smul_mul_assoc]
    rw [this, hk, mul_zero, zero_mul]
  simp only [key2, Finset.sum_const_zero, smul_zero]

end GlobalTheory.Shin.IndIso
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegerOfMaximalIdealPowSmulIsInteger
section
open IsLocalRing TensorProduct Pointwise

namespace GlobalTheory

theorem isInteger_of_maximalIdeal_smul_isInteger (S : Type) [CommRing S] [IsRegularLocalRing S]
    (hdim : 2 ≤ ringKrullDim S) (c : FractionRing S)
    (hc : ∀ a ∈ maximalIdeal S, IsLocalization.IsInteger S (a • c)) :
    IsLocalization.IsInteger S c := by
  obtain ⟨hD, hI⟩ := GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing S
  have hinj : Function.Injective (algebraMap S (FractionRing S)) := IsFractionRing.injective S (FractionRing S)
  by_cases hA : ∀ a ∈ maximalIdeal S, ∃ y ∈ maximalIdeal S, algebraMap S (FractionRing S) y = a • c
  ·
    let N : Submodule S (FractionRing S) := Submodule.map (Algebra.linearMap S (FractionRing S)) (maximalIdeal S)
    have hne : maximalIdeal S ≠ ⊥ := by
      intro h
      have hF : IsField S := (isField_iff_maximalIdeal_eq).2 h
      have := ringKrullDim_eq_zero_of_isField hF
      rw [this] at hdim
      exact absurd hdim (by decide)
    have hN : N ≠ ⊥ := by
      intro h
      apply hne
      rw [eq_bot_iff]
      intro x hx
      have : Algebra.linearMap S (FractionRing S) x ∈ N := Submodule.mem_map_of_mem hx
      rw [h, Submodule.mem_bot] at this
      rw [Submodule.mem_bot]
      exact hinj (by simpa using this)
    have hFG : N.FG := Submodule.FG.map _ (IsNoetherian.noetherian _)
    have hint : IsIntegral S c := by
      refine isIntegral_of_smul_mem_submodule N hN hFG c ?_
      intro n hn
      obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.1 hn
      obtain ⟨y, hy, hy'⟩ := hA a ha
      refine Submodule.mem_map.2 ⟨y, hy, ?_⟩
      simp only [Algebra.linearMap_apply, smul_eq_mul]
      rw [hy', Algebra.smul_def, mul_comm]
    exact (IsIntegrallyClosed.isIntegral_iff).1 hint
  · exfalso
    push_neg at hA
    obtain ⟨a, ha, hy⟩ := hA
    obtain ⟨y, hy'⟩ := hc a ha
    have hyu : y ∉ maximalIdeal S := fun h => hy y h hy'
    have hyunit : IsUnit y := by simpa [mem_maximalIdeal, mem_nonunits_iff] using hyu
    have hspan : maximalIdeal S = Ideal.span {a} := by
      apply le_antisymm
      · intro b hb
        obtain ⟨z, hz⟩ := hc b hb
        have key : b * y = a * z := by
          apply hinj
          rw [map_mul, map_mul, hy', hz, ← Algebra.smul_def, ← Algebra.smul_def, smul_comm]
        rw [Ideal.mem_span_singleton']
        obtain ⟨u, rfl⟩ := hyunit
        refine ⟨z * ↑u⁻¹, ?_⟩
        calc z * ↑u⁻¹ * a = (a * z) * ↑u⁻¹ := by ring
          _ = (b * ↑u) * ↑u⁻¹ := by rw [key]
          _ = b := by simp [mul_assoc]
      · rw [Ideal.span_le]
        simpa using ha
    have h1 : (maximalIdeal S).spanFinrank ≤ 1 := by
      rw [hspan]
      refine (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_singleton a)).trans ?_
      simp
    have h2 := ringKrullDim_le_spanFinrank_maximalIdeal S
    have h3 : ringKrullDim S ≤ 1 := h2.trans (by exact_mod_cast h1)
    have := hdim.trans h3
    exact absurd this (by decide)

theorem isInteger_of_maximalIdeal_pow_smul_isInteger :
    ∀ (S : Type) [CommRing S] [IsRegularLocalRing S], 2 ≤ ringKrullDim S →
      ∀ (k : ℕ) (c : FractionRing S), (∀ a ∈ maximalIdeal S ^ k,
        IsLocalization.IsInteger S (a • c)) → IsLocalization.IsInteger S c := by
  intro S _ _ hdim k
  induction k with
  | zero =>
    intro c hc
    simpa using hc 1 (by simp)
  | succ k ih =>
    intro c hc
    apply isInteger_of_maximalIdeal_smul_isInteger S hdim c
    intro a ha
    apply ih
    intro b hb
    rw [smul_smul]
    apply hc
    rw [pow_succ]
    exact Ideal.mul_mem_mul hb ha

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralMatrixOfMapsToFullRankLatticeStatement
section
open Polynomial Matrix GlobalTheory.LatOrb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_matrix_of_mapsTo_fullRankLattice : ∀ {O K : Type} [CommRing O] [Field K] [Algebra O K] (n : ℕ) (M : Submodule O (Fin n → K)),
    IsLatV O M → ∀ c : Matrix (Fin n) (Fin n) K, (∀ v ∈ M, c *ᵥ v ∈ M) → IsIntegral O c := by
  first | exact @GlobalTheory.LatOrb.isIntegral_of_mapsTo_lattice | exact GlobalTheory.LatOrb.isIntegral_of_mapsTo_lattice | (intros; apply GlobalTheory.LatOrb.isIntegral_of_mapsTo_lattice <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOfEsymmMemSubringStatement
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_of_esymm_mem_subring : ∀ (ι : Type) [Fintype ι] (R : Subring ℂ) (x : ι → ℂ), (∀ k : ℕ, (∑ t ∈ Finset.powersetCard k Finset.univ, ∏ i ∈ t, x i) ∈ R) → ∀ i, IsIntegral R (x i) := by
  first | exact @GlobalTheory.QFam.isIntegral_of_esymm_mem | exact GlobalTheory.QFam.isIntegral_of_esymm_mem | (intros; apply GlobalTheory.QFam.isIntegral_of_esymm_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoMorphismRestrictFiniteOfIsNormalDense
section
open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.FiniteBirationalNear

theorem isIso_morphismRestrict_of_isNormal : ∀ {S T : Scheme.{0}} [IsLocallyNoetherian T] (ν : S ⟶ T) [IsFinite ν] (U V : T.Opens), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (V : Scheme.{0}) → Dense (U : Set T) → Dense (ν ⁻¹' (U : Set T)) → IsIso (ν ∣_ U) → IsIso (ν ∣_ V) := by
  intro S T _ ν _ U V hS hV hU hνU hiso
  have : IsReduced S := by
    haveI : ∀ x : S, _root_.IsReduced (S.presheaf.stalk x) := fun x => by
      have := (hS x).1
      infer_instance
    exact isReduced_of_isReduced_stalk S
  have hloc : ∀ x : V, ∃ W : T.Opens, (x : T) ∈ W ∧ IsIso (ν ∣_ W) := by
    intro x
    have e := (V.stalkIso x).symm.commRingCatIsoToRingEquiv
    have h1 : IsDomain (T.presheaf.stalk (x : T)) := by
      have := (hV x).1
      exact e.toMulEquiv.isDomain _
    have h2 : IsIntegrallyClosed (T.presheaf.stalk (x : T)) := by
      have := (hV x).2
      exact IsIntegrallyClosed.of_equiv e.symm
    exact main S T ν U ‹_› ‹_› hiso hU hνU (x : T) h1 h2
  choose W hxW hW using hloc
  let W' : V → V.toScheme.Opens := fun x => V.ι ⁻¹ᵁ W x
  have hcov : iSup W' = ⊤ := by
    rw [eq_top_iff]
    intro y _
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨y, hxW y⟩
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme) W' hcov
    fun x => ?_
  have h1 : IsIso (ν ∣_ W x ∣_ ((W x).ι ⁻¹ᵁ V)) := inferInstance
  have h2 := ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictRestrict ν (W x) ((W x).ι ⁻¹ᵁ V))).1 h1
  have e : (W x).ι ''ᵁ ((W x).ι ⁻¹ᵁ V) = V.ι ''ᵁ W' x := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Opens.opensRange_ι, Scheme.Opens.opensRange_ι, inf_comm]
  exact ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictRestrict ν V (W' x))).2
    (((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff (morphismRestrictEq ν e)).1 h2)

end GlobalTheory.FiniteBirationalNear
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantAddChar
section
noncomputable section

open MeasureTheory Matrix ValuativeRel
open scoped NNReal Topology Pointwise

namespace GlobalTheory.WeilM

theorem eq_zero_of_mul_invariant {X : Type} [TopologicalSpace X] (l : (X → ℂ) →ₗ[ℂ] ℂ) (S : Set (X → ℂ))
    (hS : ∀ f ∈ S, IsLocallyConstant f) (hl : ∀ f ∈ S, ∀ φ ∈ SB X, l (f * φ) = l φ)
    {φ : X → ℂ} (hφ : φ ∈ SB X) (h : ∀ x, φ x ≠ 0 → ∃ f ∈ S, f x ≠ 1) : l φ = 0 := by
  have hind : ∀ U : Set X, IsClopen U → ∀ φ ∈ SB X, U.indicator φ ∈ SB X := by
    intro U hU φ hφ
    have : U.indicator φ = U.indicator 1 * φ := by
      funext x; by_cases hx : x ∈ U <;> simp [hx]
    rw [this]
    exact ⟨(LocallyConstant.indicator (1 : LocallyConstant X ℂ) hU).isLocallyConstant.mul hφ.1, hφ.2.mul_left⟩
  have hsupp : IsClopen (Function.support φ) := (hφ.1.isClopen_fiber 0).compl
  have hc : IsCompact (Function.support φ) := by
    have := hφ.2
    rwa [HasCompactSupport, tsupport, hsupp.isClosed.closure_eq] at this
  have key : ∃ U : Set X, IsClopen U ∧ Function.support φ ⊆ U ∧
      ∀ φ' ∈ SB X, Function.support φ' ⊆ U → l φ' = 0 := by
    refine hc.induction_on (p := fun s => ∃ U : Set X, IsClopen U ∧ s ⊆ U ∧
      ∀ φ' ∈ SB X, Function.support φ' ⊆ U → l φ' = 0) ?_ ?_ ?_ ?_
    · refine ⟨∅, isClopen_empty, le_rfl, fun φ' _ h0 => ?_⟩
      rw [Set.subset_empty_iff, Function.support_eq_empty_iff] at h0
      rw [h0, map_zero]
    · rintro s t hst ⟨U, hU, htU, h'⟩
      exact ⟨U, hU, hst.trans htU, h'⟩
    · rintro s t ⟨U, hU, hsU, h1⟩ ⟨V, hV, htV, h2⟩
      refine ⟨U ∪ V, hU.union hV, Set.union_subset_union hsU htV, fun φ' hφ' hs => ?_⟩
      rw [← Set.indicator_self_add_compl U φ', map_add, h1 _ (hind U hU _ hφ') Set.support_indicator_subset,
        h2 _ (hind _ hU.compl _ hφ'), add_zero]
      rw [Set.support_indicator]
      rintro x ⟨hx, hx'⟩
      exact (hs hx').resolve_left hx
    · intro x hx
      obtain ⟨f, hf, hfx⟩ := h x hx
      have hU := (hS f hf).isClopen_fiber (f x)
      refine ⟨_, mem_nhdsWithin_of_mem_nhds (hU.isOpen.mem_nhds rfl), _, hU, le_rfl, fun φ' hφ' hs => ?_⟩
      have h1 : f * φ' = f x • φ' := by
        funext y
        by_cases hy : φ' y = 0
        · simp [hy]
        · have : f y = f x := hs hy
          simp [this]
      have h2 := hl f hf φ' hφ'
      rw [h1, map_smul, smul_eq_mul] at h2
      have h3 : (f x - 1) * l φ' = 0 := by rw [sub_mul, h2, one_mul, sub_self]
      exact (mul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr hfx)
  obtain ⟨U, -, hU, h'⟩ := key
  exact h' φ hφ hU

theorem eq_one_of_forall_pow_near {z : ℂ} (h : ∀ n : ℕ, ‖z ^ n - 1‖ < 1 / 2) : z = 1 := by
  first
  | exact @_root_.GlobalTheory.PowerTwoNormLowerBound.main
  | exact _root_.GlobalTheory.PowerTwoNormLowerBound.main
  | (apply _root_.GlobalTheory.PowerTwoNormLowerBound.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.PowerTwoNormLowerBound.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PowerTwoNormLowerBound.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PowerTwoNormLowerBound.main ..)

theorem isLocallyConstant_addChar {V : Type} [AddCommGroup V] [TopologicalSpace V] [NonarchimedeanAddGroup V]
    (ψ : AddChar V ℂ) (hψ : Continuous ψ) : IsLocallyConstant ψ := by
  have h0 : {x | ‖ψ x - 1‖ < 1 / 2} ∈ 𝓝 (0 : V) :=
    (isOpen_lt (by fun_prop) continuous_const).mem_nhds (by simp)
  obtain ⟨K, hK⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ h0
  have h1 : ∀ x ∈ K, ψ x = 1 := fun x hx => eq_one_of_forall_pow_near fun n => by
    rw [← AddChar.map_nsmul_eq_pow]
    exact hK (nsmul_mem hx n)
  refine (IsLocallyConstant.iff_eventually_eq _).mpr fun x => ?_
  have : (fun z => -x + z) ⁻¹' (K : Set V) ∈ 𝓝 x :=
    (K.isOpen.preimage (by fun_prop)).mem_nhds (by simp)
  filter_upwards [this] with z hz
  have h2 : z = x + (-x + z) := by abel
  rw [h2, AddChar.map_add_eq_mul, h1 _ hz, mul_one]

variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem nonarch_field : NonarchimedeanAddGroup F where
  is_nonarchimedean U hU := by
    obtain ⟨s, hs⟩ := SplitWeil.exists_cball_subset hU
    exact ⟨⟨⟨⟨⟨SplitWeil.cball s, SplitWeil.add_mem_cball⟩, by simp [SplitWeil.cball]⟩, SplitWeil.neg_mem_cball⟩,
      SplitWeil.isOpen_cball s⟩, hs⟩

theorem nonarch_pi (κ : Type) [Fintype κ] : NonarchimedeanAddGroup (κ → F) where
  is_nonarchimedean U hU := by
    haveI := nonarch_field F
    rw [nhds_pi, Filter.mem_pi] at hU
    obtain ⟨I, -, t, ht, hs⟩ := hU
    choose K hK using fun i => NonarchimedeanAddGroup.is_nonarchimedean (G := F) (t i) (ht i)
    exact ⟨⟨AddSubgroup.pi Set.univ fun i => (K i : AddSubgroup F),
      isOpen_set_pi Set.finite_univ fun i _ => (K i).isOpen⟩, fun x hx => hs fun i _ => hK i (hx i trivial)⟩

section Cov

variable {F} [MeasurableSpace F] [BorelSpace F] (ν : Measure F) [ν.IsAddHaarMeasure]
  {κ : Type} [Fintype κ] [DecidableEq κ]

theorem smul_map_mulVec_pi (M : Matrix κ κ F) (u : Fˣ) (hu : (u : F) = M.det) :
    (distribHaarChar F u : ENNReal) • Measure.map M.mulVec (Measure.pi fun _ : κ => ν) = Measure.pi fun _ : κ => ν := by
  haveI := SplitWeil.secondCountable F
  haveI := SplitWeil.t2Space F
  have hm : ∀ A : Matrix κ κ F, Measurable A.mulVec := fun A =>
    (continuous_const.matrix_mulVec continuous_id).measurable
  have hM : M.det ≠ 0 := hu ▸ u.ne_zero
  revert u
  apply diagonal_transvection_induction_of_det_ne_zero _ M hM
  · intro D hD u hu
    refine (Measure.pi_eq fun s hs => ?_).symm
    rw [det_diagonal] at hD hu
    have A : ∀ i, D i ≠ 0 := fun i => Finset.prod_ne_zero_iff.1 hD i (Finset.mem_univ i)
    have hu' : u = ∏ i, Units.mk0 (D i) (A i) := Units.ext (by simp [hu])
    rw [Measure.smul_apply, Measure.map_apply (hm _) (MeasurableSet.univ_pi hs)]
    have : ((diagonal D).mulVec ⁻¹' Set.pi Set.univ fun i : κ => s i) =
        Set.pi Set.univ fun i : κ => (Units.mk0 (D i) (A i))⁻¹ • s i := by
      ext f
      simp only [Set.mem_preimage, Set.mem_univ_pi, mulVec_diagonal]
      exact forall_congr' fun i => (Set.mem_inv_smul_set_iff (a := Units.mk0 (D i) (A i))).symm
    rw [this, Measure.pi_pi, hu', map_prod, ENNReal.coe_finset_prod, smul_eq_mul, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [distribHaarChar_mul, smul_inv_smul]
  · intro t u hu
    have hu' : u = 1 := Units.ext (by simp [hu])
    rw [hu', map_one, ENNReal.coe_one, one_smul]
    refine (Measure.pi_eq fun s hs ↦ ?_).symm
    have h2s : MeasurableSet (Set.univ.pi s) := .pi Set.countable_univ fun i _ ↦ hs i
    simp_rw [← Measure.pi_pi, ← lintegral_indicator_one h2s]
    rw [lintegral_map (measurable_one.indicator h2s) (hm _)]
    refine lintegral_eq_of_lmarginal_eq {t.i} ((measurable_one.indicator h2s).comp (hm _))
      (measurable_one.indicator h2s) ?_
    simp_rw [lmarginal_singleton]
    ext x
    cases t with | mk t_i t_j t_hij t_c =>
    simp [transvection, add_mulVec, single_mulVec, t_hij.symm, ← Function.update_add,
      lintegral_add_right_eq_self fun xᵢ ↦ Set.indicator (Set.univ.pi s) 1 (Function.update x t_i xᵢ)]
  · intro A B hA hB IHA IHB u hu
    have hu' : u = Units.mk0 _ hA * Units.mk0 _ hB := Units.ext (by simp [hu])
    have e : (A * B).mulVec = A.mulVec ∘ B.mulVec := funext fun x => (mulVec_mulVec x A B).symm
    rw [hu', map_mul, ENNReal.coe_mul, mul_smul, e, ← Measure.map_map (hm _) (hm _), ← Measure.map_smul,
      IHB _ rfl, IHA _ rfl]

theorem integral_comp_mulVec (g : GL κ F) (f : (κ → F) → ℂ) :
    ((distribHaarChar F (Matrix.GeneralLinearGroup.det g) : ℝ) : ℂ) *
      ∫ x, f (g.val.mulVec x) ∂(Measure.pi fun _ : κ => ν) = ∫ x, f x ∂(Measure.pi fun _ : κ => ν) := by
  haveI := SplitWeil.secondCountable F
  have hm : ∀ A : Matrix κ κ F, Measurable A.mulVec := fun A =>
    (continuous_const.matrix_mulVec continuous_id).measurable
  let e : (κ → F) ≃ᵐ (κ → F) :=
    { toFun := g.val.mulVec, invFun := (g⁻¹).val.mulVec
      left_inv := fun x => by rw [mulVec_mulVec, Units.inv_mul, one_mulVec]
      right_inv := fun x => by rw [mulVec_mulVec, Units.mul_inv, one_mulVec]
      measurable_toFun := hm _, measurable_invFun := hm _ }
  conv_rhs => rw [← smul_map_mulVec_pi ν g.val (Matrix.GeneralLinearGroup.det g) rfl, integral_smul_measure]
  rw [show g.val.mulVec = e from rfl, integral_map_equiv]
  simp

end Cov

end GlobalTheory.WeilM

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNbhdAwayOfAddMulEqOneStatement
section
open GlobalTheory.AffineCurveNbhd
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isNbhd_away_of_add_algebraMap_mul_eq_one : ∀ (B A' : Type) [CommRing B] [CommRing A'] [Algebra B A'] (f : B) (h c : A'), IsNbhd B A' f → h + algebraMap B A' f * c = 1 → IsNbhd B (Localization.Away h) f := by
  first | (exact @GlobalTheory.AffineCurveNbhd.isNbhd_away_of_add_mul_eq_one) | (exact GlobalTheory.AffineCurveNbhd.isNbhd_away_of_add_mul_eq_one) | (intros; apply GlobalTheory.AffineCurveNbhd.isNbhd_away_of_add_mul_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNormalSchemePullbackSpMapOfAlgebra
section
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem GlobalTheory.isNormalScheme_pullback_spMap_of_algebra
    (halg : ∀ (F K A : Type) [Field F] [CharZero F] [Field K] [Algebra F K] [CommRing A]
      [Algebra F A], (∀ (P : Ideal A) [P.IsPrime], IsDomain (Localization.AtPrime P) ∧
        IsIntegrallyClosed (Localization.AtPrime P)) →
      ∀ (Q : Ideal (TensorProduct F A K)) [Q.IsPrime], IsDomain (Localization.AtPrime Q) ∧
        IsIntegrallyClosed (Localization.AtPrime Q))
    (F K : Type) [Field F] [CharZero F] [Field K] (c : F →+* K) (Y : Scheme.{0})
    (g : Y ⟶ Sp F) (hY : GlobalTheory.IsNormalScheme Y) : GlobalTheory.IsNormalScheme (pullback g (spMap c)) := by
  let 𝒰 := Y.affineOpenCover.openCover
  refine (GlobalTheory.IsNormalScheme.iff_of_openCover (Scheme.Pullback.openCoverOfLeft 𝒰 g (spMap c))).mpr ?_
  intro i
  change GlobalTheory.IsNormalScheme (pullback (𝒰.f i ≫ g) (spMap c))
  let R := Y.affineOpenCover.X i
  have hR : GlobalTheory.IsNormalScheme (Spec R) :=
    @GlobalTheory.IsNormalScheme.of_isOpenImmersion _ _ (𝒰.f i) (𝒰.map_prop i) hY
  let φ := Spec.preimage (𝒰.f i ≫ g)
  letI : Algebra F R := φ.hom.toAlgebra
  letI : Algebra F K := c.toAlgebra
  have e1 : 𝒰.f i ≫ g = Spec.map (CommRingCat.ofHom (algebraMap F R)) :=
    (Spec.map_preimage (𝒰.f i ≫ g)).symm
  have e2 : spMap c = Spec.map (CommRingCat.ofHom (algebraMap F K)) := rfl
  rw [e1, e2]
  refine (GlobalTheory.IsNormalScheme.iff_of_iso (pullbackSpecIso F R K)).mpr ?_
  refine (GlobalTheory.IsNormalScheme.spec_iff _).mpr ?_
  exact halg F K R ((GlobalTheory.IsNormalScheme.spec_iff R).mp hR)
end

