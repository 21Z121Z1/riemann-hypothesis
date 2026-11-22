import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0422
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAffineNeighbourhoodExists
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0176
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1581
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueEqAdicSumAtImageOfZeroPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1097

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeGenericNeZeroEquidimensional
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GenFinite

theorem finiteDimensional_of_trdeg_eq (F A B K L : Type) [Field F] [CommRing A] [IsDomain A]
    [CommRing B] [IsDomain B] [Field K] [Field L] [Algebra F A] [Algebra A B] [Algebra F B]
    [IsScalarTower F A B] [Algebra A K] [Algebra B L] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L] [IsFractionRing A K] [IsFractionRing B L]
    [Algebra.FiniteType A B] (n : ℕ) (hA : Algebra.trdeg F A = n) (hB : Algebra.trdeg F B = n) :
    FiniteDimensional K L := by
  letI : Algebra F K := ((algebraMap A K).comp (algebraMap F A)).toAlgebra
  letI : Algebra F L := ((algebraMap B L).comp (algebraMap F B)).toAlgebra
  haveI : IsScalarTower F A K := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower F B L := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower F K L := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    change algebraMap B L (algebraMap F B x) = algebraMap K L (algebraMap A K (algebraMap F A x))
    rw [← IsScalarTower.algebraMap_apply A K L, IsScalarTower.algebraMap_apply A B L,
      ← IsScalarTower.algebraMap_apply F A B]
  haveI : FaithfulSMul F A := (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap F A).injective
  haveI : FaithfulSMul F B := (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap F B).injective
  haveI : FaithfulSMul A K := (faithfulSMul_iff_algebraMap_injective _ _).mpr (IsFractionRing.injective A K)
  haveI : FaithfulSMul B L := (faithfulSMul_iff_algebraMap_injective _ _).mpr (IsFractionRing.injective B L)
  haveI : Algebra.IsAlgebraic A K := IsLocalization.isAlgebraic K (nonZeroDivisors A)
  haveI : Algebra.IsAlgebraic B L := IsLocalization.isAlgebraic L (nonZeroDivisors B)
  have hK : Algebra.trdeg F K = n := (trdeg_eq_of_isAlgebraic_top F A K).trans hA
  have hL : Algebra.trdeg F L = n := (trdeg_eq_of_isAlgebraic_top F B L).trans hB
  have h0 : Algebra.trdeg K L = 0 := by
    have e := trdeg_add_eq F K (A := L)
    rw [hK, hL] at e
    rcases (Cardinal.add_eq_left_iff).1 e with h | h
    · exact absurd (le_trans (le_max_left _ _) h) (not_le.2 (Cardinal.natCast_lt_aleph0))
    · exact h
  haveI : Algebra.IsAlgebraic K L := trdeg_eq_zero_iff.1 h0
  obtain ⟨s, hs⟩ := (inferInstance : Algebra.FiniteType A B).out
  let g : B →ₐ[A] L := IsScalarTower.toAlgHom A B L
  let T : IntermediateField K L := IntermediateField.adjoin K (g '' (s : Set B))
  have hfin : FiniteDimensional K T :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have hrange : ∀ b : B, algebraMap B L b ∈ T := by
    intro b
    have hb : b ∈ Algebra.adjoin A (s : Set B) := hs ▸ Algebra.mem_top
    have : g b ∈ (Algebra.adjoin A (s : Set B)).map g := Subalgebra.mem_map.2 ⟨b, hb, rfl⟩
    rw [AlgHom.map_adjoin] at this
    have hle : Algebra.adjoin A (g '' (s : Set B)) ≤ T.toSubalgebra.restrictScalars A :=
      Algebra.adjoin_le (IntermediateField.subset_adjoin K _)
    exact hle this
  have htop : T = ⊤ := by
    refine eq_top_iff.2 fun l _ => ?_
    obtain ⟨x, y, _, rfl⟩ := IsFractionRing.div_surjective (A := B) l
    exact T.div_mem (hrange x) (hrange y)
  rw [htop] at hfin
  exact LinearEquiv.finiteDimensional (IntermediateField.topEquiv (F := K) (E := L)).toLinearEquiv

end GlobalTheory.GenFinite

namespace GlobalTheory.GenFinite

theorem trdeg_affineOpen_eq (F : Type) [Field F] {Y : Scheme.{0}} [IsIntegral Y]
    (q : Y ⟶ Sp F) [LocallyOfFiniteType q] {U : Y.Opens} (hU : IsAffineOpen U)
    (hne : (U : Set Y).Nonempty) [Algebra F Γ(Y, U)] [Algebra.FiniteType F Γ(Y, U)] (n : ℕ)
    (hn : topologicalKrullDim Y = n) : Algebra.trdeg F Γ(Y, U) = n := by
  haveI : Nonempty U := ⟨⟨hne.some, hne.some_mem⟩⟩
  obtain ⟨d, h₁, h₂⟩ := exists_ringKrullDim_eq_and_trdeg_eq F Γ(Y, U)
  have e : topologicalKrullDim (U : Set Y) = d := by
    rw [← h₁, ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact topologicalKrullDim_eq_of_isEmbedding hU.fromSpec.isOpenEmbedding.isEmbedding
      hU.range_fromSpec
  rw [GlobalTheory.OpenDim.topologicalKrullDim_open F q U hne, hn] at e
  have hd : d = n := by exact_mod_cast e.symm
  rw [h₂, hd]

theorem residueDegree_genericPoint_ne_zero : ∀ (F : Type) [Field F] (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (p : W ⟶ Sp F) (f : M ⟶ W) (n : ℕ), LocallyOfFiniteType p → LocallyOfFiniteType f → Surjective f → topologicalKrullDim M = n → topologicalKrullDim W = n → f.residueDegree (genericPoint M) ≠ 0 := by
  intro F _ M W _ _ p f n hp hf hs hM hW
  have hη : f (genericPoint M) = genericPoint W := by
    have := (genericPoint_spec M).image f.continuous
    rw [Set.image_univ, f.surjective.range_eq, closure_univ] at this
    exact this.eq (genericPoint_spec W)
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ := W.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (genericPoint W)) isOpen_univ
  have hV : IsAffineOpen V := hV
  have hx : f (genericPoint M) ∈ V := hη ▸ hxV
  obtain ⟨_, ⟨U, hU, rfl⟩, hy, hUV⟩ := M.isBasis_affineOpens.exists_subset_of_mem_open
    (show genericPoint M ∈ f ⁻¹ᵁ V from hx) (f ⁻¹ᵁ V).isOpen
  have hU : IsAffineOpen U := hU
  haveI : Nonempty V := ⟨⟨_, hx⟩⟩
  haveI : Nonempty U := ⟨⟨_, hy⟩⟩
  have e : U ≤ f ⁻¹ᵁ V := hUV
  let φ := Spec.preimage (hV.fromSpec ≫ p)
  have hφ : Spec.map φ = hV.fromSpec ≫ p := Spec.map_preimage _
  letI : Algebra F Γ(W, V) := φ.hom.toAlgebra
  have hftA : Algebra.FiniteType F Γ(W, V) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := φ)).mp (hφ ▸ inferInstance)
  letI : Algebra Γ(W, V) Γ(M, U) := (f.appLE V U e).hom.toAlgebra
  have hftB : Algebra.FiniteType Γ(W, V) Γ(M, U) :=
    HasRingHomProperty.appLE @LocallyOfFiniteType f hf ⟨V, hV⟩ ⟨U, hU⟩ e
  letI : Algebra F Γ(M, U) := (φ ≫ f.appLE V U e).hom.toAlgebra
  haveI : IsScalarTower F Γ(W, V) Γ(M, U) := IsScalarTower.of_algebraMap_eq' rfl
  have hftC : Algebra.FiniteType F Γ(M, U) := Algebra.FiniteType.trans hftA hftB
  have hA : Algebra.trdeg F Γ(W, V) = n := trdeg_affineOpen_eq F p hV ⟨_, hx⟩ n hW
  have hB : Algebra.trdeg F Γ(M, U) = n := trdeg_affineOpen_eq F (f ≫ p) hU ⟨_, hy⟩ n hM
  letI := (W.evaluation V _ hx).hom.toAlgebra
  letI := (M.evaluation U _ hy).hom.toAlgebra
  letI := (f.residueFieldMap (genericPoint M)).hom.toAlgebra
  letI : Algebra Γ(W, V) (M.residueField (genericPoint M)) :=
    (f.appLE V U e ≫ M.evaluation U _ hy).hom.toAlgebra
  haveI : IsScalarTower Γ(W, V) Γ(M, U) (M.residueField (genericPoint M)) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have nat : f.appLE V U e ≫ M.evaluation U _ hy =
      W.evaluation V _ hx ≫ f.residueFieldMap (genericPoint M) := by
    rw [Scheme.evaluation_naturality f _ hx, Scheme.Hom.appLE, Category.assoc]
    congr 1
    simp only [Scheme.evaluation]
    rw [← Category.assoc, TopCat.Presheaf.germ_res]
  haveI : IsScalarTower Γ(W, V) (W.residueField (f (genericPoint M)))
      (M.residueField (genericPoint M)) :=
    IsScalarTower.of_algebraMap_eq' congr($(nat).hom)
  haveI := GenFiniteEtale.isFractionRing_eval W hV hη hx
  haveI := GenFiniteEtale.isFractionRing_eval M hU rfl hy
  have := finiteDimensional_of_trdeg_eq F Γ(W, V) Γ(M, U) (W.residueField (f (genericPoint M)))
    (M.residueField (genericPoint M)) n hA hB
  change Module.finrank (W.residueField (f (genericPoint M))) (M.residueField (genericPoint M)) ≠ 0
  exact Module.finrank_pos.ne'

end GlobalTheory.GenFinite
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueFieldInertiaFixedIsAlgClosed
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.InertiaRes

def toV (R K Ω : Type) [CommRing R] [Field K] [Algebra R K] [Field Ω] [Algebra K Ω]
    (V : ValuationSubring Ω) (hV : IsAbove R K V.toSubring) : R →+* V :=
  ((algebraMap K Ω).comp (algebraMap R K)).codRestrict V (fun r => by
    have : algebraMap R K r ∈ V.toSubring.comap (algebraMap K Ω) := hV ▸ ⟨r, rfl⟩
    exact this)

theorem coe_toV (R K Ω : Type) [CommRing R] [Field K] [Algebra R K] [Field Ω] [Algebra K Ω]
    (V : ValuationSubring Ω) (hV : IsAbove R K V.toSubring) (r : R) :
    ((toV R K Ω V hV r : V) : Ω) = algebraMap K Ω (algebraMap R K r) := rfl

theorem isLocalHom_toV (R K Ω : Type) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    [Field Ω] [Algebra K Ω] (V : ValuationSubring Ω) (hV : IsAbove R K V.toSubring) :
    IsLocalHom (toV R K Ω V hV) := by
  constructor
  intro r hr
  obtain ⟨u, hu⟩ := hr
  have hx : algebraMap K Ω (algebraMap R K r) * ((u⁻¹ : Vˣ) : V) = 1 := by
    rw [← coe_toV R K Ω V hV r, ← hu]
    exact congrArg Subtype.val u.mul_inv
  have hx0 : algebraMap R K r ≠ 0 := by
    intro h0; rw [h0, map_zero, zero_mul] at hx; exact zero_ne_one hx
  have hmem : (algebraMap R K r)⁻¹ ∈ V.toSubring.comap (algebraMap K Ω) := by
    change algebraMap K Ω _ ∈ V
    rw [map_inv₀, inv_eq_of_mul_eq_one_right hx]
    exact ((u⁻¹ : Vˣ) : V).2
  rw [hV] at hmem
  obtain ⟨s, hs⟩ := hmem
  have h1 : r * s = 1 := IsFractionRing.injective R K (by rw [map_mul, hs, map_one, mul_inv_cancel₀ hx0])
  exact ⟨⟨r, s, h1, by rw [mul_comm]; exact h1⟩, rfl⟩

def resMap (R K Ω : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    [Field Ω] [Algebra K Ω] (V : ValuationSubring Ω) (hV : IsAbove R K V.toSubring) :
    ResidueField R →+* ResidueField V :=
  haveI := isLocalHom_toV R K Ω V hV
  ResidueField.map (toV R K Ω V hV)

open Polynomial

theorem residue_algebraic (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω] (V : ValuationSubring Ω)
    (hV : IsAbove R K V.toSubring) (a : ResidueField V) :
    ∃ p : Polynomial (ResidueField R), p ≠ 0 ∧ p.eval₂ (resMap R K Ω V hV) a = 0 := by
  haveI : IsLocalHom (toV R K Ω V hV) := isLocalHom_toV R K Ω V hV
  letI := UniqueFactorizationMonoid.normalizationMonoid (α := R)
  letI := UniqueFactorizationMonoid.toNormalizedGCDMonoid R
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨w, rfl⟩ := residue_surjective a
  obtain ⟨p, hp0, hpw⟩ := Algebra.IsAlgebraic.isAlgebraic (R := K) ((w : V) : Ω)
  obtain ⟨b, hb⟩ := IsLocalization.integerNormalization_map_to_map (nonZeroDivisors R) p
  set q := IsLocalization.integerNormalization (nonZeroDivisors R) p
  have hφinj : Function.Injective (toV R K Ω V hV) := fun x y h =>
    IsFractionRing.injective R K ((algebraMap K Ω).injective (by
      have := congrArg Subtype.val h
      rwa [coe_toV, coe_toV] at this))
  have hq0 : q ≠ 0 := by
    intro hq; rw [hq, Polynomial.map_zero] at hb
    have hb0 : (algebraMap R K (b : R)) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
    rw [Algebra.smul_def, Polynomial.algebraMap_apply] at hb
    exact hp0 ((mul_eq_zero.1 hb.symm).resolve_left (by simpa using hb0))
  have hcomp : V.subtype.comp (toV R K Ω V hV) = (algebraMap K Ω).comp (algebraMap R K) :=
    RingHom.ext fun r => coe_toV R K Ω V hV r
  have hqw : Polynomial.eval₂ (toV R K Ω V hV) w q = 0 := by
    apply Subtype.ext
    change V.subtype _ = V.subtype 0
    rw [map_zero, Polynomial.hom_eval₂, hcomp, ← Polynomial.eval₂_map, hb, Algebra.smul_def,
      Polynomial.eval₂_mul]
    have : Polynomial.eval₂ (algebraMap K Ω) (V.subtype w) p = 0 := hpw
    rw [this, mul_zero]
  set pp := q.primPart
  have hpp : Polynomial.eval₂ (toV R K Ω V hV) w pp = 0 := by
    have hc : q.content ≠ 0 := (Polynomial.content_eq_zero_iff).not.2 hq0
    have := hqw
    rw [Polynomial.eq_C_content_mul_primPart q, Polynomial.eval₂_mul, Polynomial.eval₂_C] at this
    exact (mul_eq_zero.1 this).resolve_left (fun h0 => hc (hφinj (by rw [h0, map_zero])))
  refine ⟨pp.map (residue R), ?_, ?_⟩
  · intro h0
    have hmem : pp ∈ RingHom.ker (Polynomial.mapRingHom (residue R)) := by
      simpa [RingHom.mem_ker] using h0
    rw [Polynomial.ker_mapRingHom, ker_residue, hϖ.maximalIdeal_eq, Ideal.map_span,
      Set.image_singleton, Ideal.mem_span_singleton] at hmem
    exact hϖ.not_isUnit (Polynomial.isPrimitive_primPart q ϖ hmem)
  · rw [Polynomial.eval₂_map]
    change Polynomial.eval₂ ((ResidueField.map (toV R K Ω V hV)).comp (residue R)) _ _ = 0
    rw [ResidueField.map_comp_residue, ← Polynomial.hom_eval₂, hpp, map_zero]

theorem eq_of_residue_eq {A : Type} [CommRing A] [IsDomain A] [IsLocalRing A] (q : A[X])
    (hs : (q.map (residue A)).Separable) (b c : A) (hb : q.IsRoot b) (hc : q.IsRoot c)
    (h : residue A b = residue A c) : b = c := by
  by_contra hne
  obtain ⟨q1, rfl⟩ := Polynomial.dvd_iff_isRoot.2 hb
  have hc1 : q1.IsRoot c := by
    have := hc
    rw [IsRoot, eval_mul, eval_sub, eval_X, eval_C] at this
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 (Ne.symm hne))
  obtain ⟨q2, rfl⟩ := Polynomial.dvd_iff_isRoot.2 hc1
  rw [← _root_.mul_assoc, Polynomial.map_mul, Polynomial.map_mul] at hs
  have h2 := hs.of_mul_left
  simp only [Polynomial.map_sub, map_X, map_C, h] at h2
  exact not_isUnit_X_sub_C _ (isCoprime_self.1 h2.isCoprime)

theorem residueField_inertiaFixed_isAlgClosed : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring → IsAlgClosed (IsLocalRing.ResidueField (V.comap (algebraMap (IntermediateField.fixedField (inertia K V)) Ω))) := by
  intro R K Ω _ _ _ _ _ _ _ _ _ _ V hV
  haveI : IsSepClosed Ω := IsSepClosure.sep_closed K
  haveI : Algebra.IsSeparable K Ω := IsSepClosure.separable
  haveI : IsLocalHom (toV R K Ω V hV) := isLocalHom_toV R K Ω V hV
  letI : Algebra (ResidueField R) (ResidueField V) := (resMap R K Ω V hV).toAlgebra
  haveI : Algebra.IsAlgebraic (ResidueField R) (ResidueField V) := ⟨fun a => by
    obtain ⟨p, hp, h⟩ := residue_algebraic R K Ω V hV a
    exact ⟨p, hp, h⟩⟩
  haveI : PerfectField (ResidueField V) := Algebra.IsAlgebraic.perfectField (ResidueField R)

  have hred : ∀ s : Multiset V, ((s.map fun b => X - C b).prod).map (residue V) =
      ((s.map (residue V)).map fun a => X - C a).prod := by
    intro s
    rw [Polynomial.map_multiset_prod, Multiset.map_map, Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro b _
    simp

  haveI : IsSepClosed (ResidueField V) := IsSepClosed.of_exists_root _ fun p hm hirr hsep => by
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
      ((Polynomial.mem_lifts p).2 (Polynomial.map_surjective _ residue_surjective p)) hm
    obtain ⟨s, hs⟩ := GlobalTheory.T.monic_splits_valuationSubring_of_separable_reduction Ω V q hqm (by rw [hq]; exact hsep)
    rw [← hq, hs, hred] at hirr ⊢
    obtain ⟨b, hb⟩ : ∃ b, b ∈ s := by
      by_contra h0
      push_neg at h0
      rw [Multiset.eq_zero_of_forall_notMem h0] at hirr
      simp at hirr
    refine ⟨residue V b, ?_⟩
    have hr := Polynomial.roots_multiset_prod_X_sub_C (s.map (residue V))
    have hmem : residue V b ∈ ((s.map (residue V)).map fun a => X - C a).prod.roots := by
      rw [hr]; exact Multiset.mem_map_of_mem _ hb
    exact (Polynomial.mem_roots'.1 hmem).2
  haveI : IsAlgClosed (ResidueField V) := inferInstance

  set K' := IntermediateField.fixedField (inertia K V) with hK'
  set V' := V.comap (algebraMap K' Ω) with hV'
  let jV : V' →+* V := ((algebraMap K' Ω).comp V'.subtype).codRestrict V (fun x => x.2)
  haveI : IsLocalHom jV := by
    constructor
    intro x hx
    obtain ⟨u, hu⟩ := hx
    have hx1 : ((x : K') : Ω) * ((u⁻¹ : Vˣ) : V) = 1 := by
      have : ((jV x : V) : Ω) = ((x : K') : Ω) := rfl
      rw [← this, ← hu]
      exact congrArg Subtype.val u.mul_inv
    have hx0 : (x : K') ≠ 0 := by
      intro h0; rw [h0] at hx1; simp at hx1
    have hmem : (x : K')⁻¹ ∈ V' := by
      change ((((x : K')⁻¹ : K')) : Ω) ∈ V
      rw [IntermediateField.coe_inv, inv_eq_of_mul_eq_one_right hx1]
      exact ((u⁻¹ : Vˣ) : V).2
    refine isUnit_iff_exists_inv.2 ⟨⟨_, hmem⟩, ?_⟩
    apply Subtype.ext
    simp only [MulMemClass.coe_mul, OneMemClass.coe_one]
    exact mul_inv_cancel₀ hx0
  haveI : Algebra.IsSeparable (ResidueField R) (ResidueField V) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  have hsurj : Function.Surjective (ResidueField.map jV) := by
    intro a
    have hsep : (minpoly (ResidueField R) a).Separable := Algebra.IsSeparable.isSeparable _ a
    have hmon : (minpoly (ResidueField R) a).Monic := minpoly.monic (Algebra.IsIntegral.isIntegral a)
    obtain ⟨g, hg, -, hgm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
      ((Polynomial.mem_lifts _).2 (Polynomial.map_surjective _ residue_surjective _)) hmon
    set gV := g.map (toV R K Ω V hV) with hgV
    have hgV' : gV.map (residue V) = (minpoly (ResidueField R) a).map (resMap R K Ω V hV) := by
      rw [hgV, Polynomial.map_map, ← ResidueField.map_comp_residue, ← Polynomial.map_map, hg]
      rfl
    have hsepV : (gV.map (residue V)).Separable := by rw [hgV']; exact hsep.map
    obtain ⟨s, hs⟩ := GlobalTheory.T.monic_splits_valuationSubring_of_separable_reduction Ω V gV (hgm.map _) hsepV
    have hroot : a ∈ (gV.map (residue V)).roots := by
      rw [Polynomial.mem_roots ((hgm.map _).map _).ne_zero, hgV', IsRoot, Polynomial.eval_map]
      exact minpoly.aeval _ a
    rw [hs, hred, Polynomial.roots_multiset_prod_X_sub_C] at hroot
    obtain ⟨b, hbs, rfl⟩ := Multiset.mem_map.1 hroot
    have hbroot : gV.IsRoot b := by
      have : b ∈ gV.roots := by rw [hs, Polynomial.roots_multiset_prod_X_sub_C]; exact hbs
      exact (Polynomial.mem_roots'.1 this).2
    have hfix : ∀ σ ∈ inertia K V, σ (b : Ω) = b := by
      intro σ hσ
      obtain ⟨-, h2⟩ := (mem_inertia_iff V σ).1 hσ
      have hlt := h2 b b.2
      have hd : σ (b : Ω) - b ∈ V := (V.valuation_le_one_iff _).1 hlt.le
      have hmem : σ (b : Ω) ∈ V := by simpa using add_mem hd b.2
      set c : V := ⟨σ b, hmem⟩ with hc
      have hres : residue V c = residue V b := by
        rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
        exact hlt
      have hcroot : gV.IsRoot c := by
        have key : ∀ y : V, ((gV.eval y : V) : Ω) = g.eval₂ ((algebraMap K Ω).comp (algebraMap R K)) (y : Ω) := by
          intro y
          rw [hgV, Polynomial.eval_map]
          change V.subtype _ = _
          rw [Polynomial.hom_eval₂]
          rfl
        have hb0 := key b
        rw [hbroot.eq_zero] at hb0
        have hcomm : (σ : Ω →+* Ω).comp ((algebraMap K Ω).comp (algebraMap R K)) =
            (algebraMap K Ω).comp (algebraMap R K) := by
          ext r; simp
        apply Subtype.ext
        rw [key c, show ((c : V) : Ω) = (σ : Ω →+* Ω) b from rfl, ← hcomm, ← Polynomial.hom_eval₂, ← hb0]
        simp
      have := eq_of_residue_eq gV hsepV c b hcroot hbroot hres
      exact congrArg Subtype.val this
    have hbK : (b : Ω) ∈ K' := by
      rw [hK', IntermediateField.mem_fixedField_iff]
      exact hfix
    have hbV' : (⟨b, hbK⟩ : K') ∈ V' := b.2
    refine ⟨residue V' ⟨⟨b, hbK⟩, hbV'⟩, ?_⟩
    rw [ResidueField.map_residue]
    rfl
  let e := RingEquiv.ofBijective (ResidueField.map jV) ⟨(ResidueField.map jV).injective, hsurj⟩
  exact IsAlgClosed.of_ringEquiv _ _ e.symm

end GlobalTheory.InertiaRes
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResiduePerfectAndChar
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbVarRedRes

theorem residue_perfect_and_char :
  ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] [PerfectField (ResidueField R)] (L W : Type) [Field L] [Algebra K L] [FiniteDimensional K L] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Algebra W L] [IsFractionRing W L], IsAbove R K (algebraMap W L).range → PerfectField (ResidueField W) ∧ ∀ m : ℕ, (m : ResidueField R) ≠ 0 → (m : ResidueField W) ≠ 0 := by
  intro R K _ _ _ _ _ _ _ L W _ _ _ _ _ _ _ _ h
  have hWL : Function.Injective (algebraMap W L) := IsFractionRing.injective W L
  have hRK : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  set V : Subring L := (algebraMap W L).range with hV
  have memV : ∀ x : K, algebraMap K L x ∈ V ↔ x ∈ (algebraMap R K).range := by
    intro x
    rw [← Subring.mem_comap, show V.comap (algebraMap K L) = (algebraMap R K).range from h]
  let e : W ≃+* V := RingEquiv.ofBijective (algebraMap W L).rangeRestrict
    ⟨fun a b hab => hWL (by simpa using congrArg Subtype.val hab), (algebraMap W L).rangeRestrict_surjective⟩
  have he : ∀ v : V, algebraMap W L (e.symm v) = v := by
    intro v
    have := congrArg Subtype.val (e.apply_symm_apply v)
    exact this
  let ψ : R →+* V := ((algebraMap K L).comp (algebraMap R K)).codRestrict V
    (fun r => (memV _).2 ⟨r, rfl⟩)
  let φ : R →+* W := e.symm.toRingHom.comp ψ
  have hφ : ∀ r, algebraMap W L (φ r) = algebraMap K L (algebraMap R K r) := by
    intro r; exact he (ψ r)
  have hφinj : Function.Injective φ := by
    intro a b hab
    have := congrArg (algebraMap W L) hab
    rw [hφ, hφ] at this
    exact hRK ((algebraMap K L).injective this)
  haveI : IsLocalHom φ := by
    constructor
    intro r hr
    obtain ⟨u, hu⟩ := hr
    have hx : algebraMap W L (φ r) * algebraMap W L (u⁻¹ : Wˣ) = 1 := by
      rw [← map_mul, ← hu]; simp
    rw [hφ] at hx
    have hx0 : algebraMap R K r ≠ 0 := by
      intro h0; rw [h0] at hx; simp at hx
    have hinv : algebraMap K L (algebraMap R K r)⁻¹ = algebraMap W L (u⁻¹ : Wˣ) := by
      rw [map_inv₀]; exact (eq_inv_of_mul_eq_one_right hx).symm
    obtain ⟨s, hs⟩ := (memV _).1 (by rw [hinv]; exact RingHom.mem_range_self _ _)
    have h1 : r * s = 1 := hRK (by rw [map_mul, hs, map_one, mul_inv_cancel₀ hx0])
    exact ⟨⟨r, s, h1, by rw [mul_comm]; exact h1⟩, rfl⟩
  let f := ResidueField.map φ
  have hf : Function.Injective f := f.injective
  refine ⟨?_, fun m hm hW => hm (hf (by rw [map_natCast, map_zero]; exact hW))⟩
  letI : Algebra (ResidueField R) (ResidueField W) := f.toAlgebra
  letI := UniqueFactorizationMonoid.normalizationMonoid (α := R)
  letI := UniqueFactorizationMonoid.toNormalizedGCDMonoid R
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  haveI : Algebra.IsAlgebraic (ResidueField R) (ResidueField W) := by
    constructor
    intro y
    obtain ⟨w, rfl⟩ := residue_surjective y
    have hint : IsIntegral K (algebraMap W L w) := Algebra.IsIntegral.isIntegral _
    set p := minpoly K (algebraMap W L w)
    obtain ⟨b, hb⟩ := IsLocalization.integerNormalization_map_to_map (nonZeroDivisors R) p
    set q := IsLocalization.integerNormalization (nonZeroDivisors R) p
    have hp0 : p ≠ 0 := minpoly.ne_zero hint
    have hq0 : q ≠ 0 := by
      intro hq; rw [hq, Polynomial.map_zero] at hb
      have hb0 : (algebraMap R K (b : R)) ≠ 0 :=
        IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
      rw [Algebra.smul_def, Polynomial.algebraMap_apply] at hb
      exact hp0 ((mul_eq_zero.1 hb.symm).resolve_left (by simpa using hb0))
    have hqw : Polynomial.eval₂ φ w q = 0 := by
      apply hWL
      rw [map_zero, Polynomial.hom_eval₂]
      have : (algebraMap W L).comp φ = (algebraMap K L).comp (algebraMap R K) := RingHom.ext hφ
      rw [this, ← Polynomial.eval₂_map, hb]
      rw [Algebra.smul_def, Polynomial.eval₂_mul]
      have : Polynomial.eval₂ (algebraMap K L) (algebraMap W L w) p = 0 := minpoly.aeval K _
      rw [this, mul_zero]
    set pp := q.primPart
    have hpp : Polynomial.eval₂ φ w pp = 0 := by
      have hc : q.content ≠ 0 := (Polynomial.content_eq_zero_iff).not.2 hq0
      have := hqw
      rw [Polynomial.eq_C_content_mul_primPart q, Polynomial.eval₂_mul, Polynomial.eval₂_C] at this
      exact (mul_eq_zero.1 this).resolve_left (fun h0 => hc (hφinj (by rw [h0, map_zero])))
    refine ⟨pp.map (residue R), ?_, ?_⟩
    · intro h0
      have hmem : pp ∈ RingHom.ker (Polynomial.mapRingHom (residue R)) := by
        simpa [RingHom.mem_ker] using h0
      rw [Polynomial.ker_mapRingHom, ker_residue, hϖ.maximalIdeal_eq, Ideal.map_span,
        Set.image_singleton, Ideal.mem_span_singleton] at hmem
      exact hϖ.not_isUnit (Polynomial.isPrimitive_primPart q ϖ hmem)
    · rw [Polynomial.aeval_def, Polynomial.eval₂_map]
      change Polynomial.eval₂ (f.comp (residue R)) _ _ = 0
      rw [ResidueField.map_comp_residue, ← Polynomial.hom_eval₂, hpp, map_zero]
  exact Algebra.IsAlgebraic.perfectField (ResidueField R)

end GlobalTheory.AbVarRedRes
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowEigensystemCarriedByFiniteTypeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowEigensystem_carried_by_finite_type : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, GlobalTheory.Chain.LiftInteg D → A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → (∀ P, Good R.toRealDat A3.A.μ0 P → conjPl P = P → TwoSided R.toRealDat A3.A.μ0 P) → ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧ ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) → R.PGEquiv F → Nonempty A3.fam3.base3.Ix → (∀ c, R.EEc c ≠ ⊥ → ∃ p, R.Carries p c) := by
  first | exact @GlobalTheory.Div.carries_of_eEc_ne_bot | exact GlobalTheory.Div.carries_of_eEc_ne_bot | (intros; apply GlobalTheory.Div.carries_of_eEc_ne_bot <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueEqAdicSumAtImageOfZeroPairStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generic_frame_liesOver_of_y_eq_zero : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif I D A G) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ (k : ℕ), 1 ≤ k → ∀ (p : QkPt D.toPre F k) (x : TFK (R := R) F ⟶ A.A), p.y = 0 → QkToAkU U.toUnifPre F k p x → ∃ (w : Frm D.toPre F 1 p.g.b) (fr : FrAt x), w.IsGen ∧ fr.IsGen ∧ GlobalTheory.Poinc.Tors.LiesOver U.toUnifPre w₀ p.g w x fr := by
  first | exact @GlobalTheory.Poinc.Tors.ValPair.liesOver_of_qkToAkU | exact GlobalTheory.Poinc.Tors.ValPair.liesOver_of_qkToAkU | (intros; apply GlobalTheory.Poinc.Tors.ValPair.liesOver_of_qkToAkU <;> assumption)
end

