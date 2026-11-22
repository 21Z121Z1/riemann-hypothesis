import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0081
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1294
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2732
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHomBirationalModelsAmpleFrames
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0659
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaModelRelAmpleAndPrincipalAbelianLocus
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0107
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0027
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2351
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2480
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2711
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2754
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyUWit
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitIntCastStalkIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2714
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2621
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2676

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalizationRelativeDimZero
section
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Vert.Model

theorem eq_genericPoint_of_isFinite {X N : Scheme.{0}} [IsIntegral X] [IsIntegral N] (ν : N ⟶ X)
    [IsFinite ν] {n : N} (hn : ν n = genericPoint X) : n = genericPoint N := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hηU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (genericPoint X)) isOpen_univ
  have hU' : IsAffineOpen U := hU
  have hV : IsAffineOpen (ν ⁻¹ᵁ U) := hU'.preimage ν
  have hnV : n ∈ ν ⁻¹ᵁ U := show ν n ∈ U from hn ▸ hηU
  haveI : Nonempty U := ⟨⟨_, hηU⟩⟩
  haveI : Nonempty (ν ⁻¹ᵁ U) := ⟨⟨_, hnV⟩⟩
  let φ := ν.appLE U (ν ⁻¹ᵁ U) le_rfl
  have hfin : φ.hom.Finite := by
    have := Scheme.Hom.finite_app ν U hU'
    rwa [Scheme.Hom.app_eq_appLE] at this
  letI := φ.hom.toAlgebra
  haveI : Algebra.IsIntegral Γ(X, U) Γ(N, ν ⁻¹ᵁ U) :=
    ⟨fun b => hfin.to_isIntegral b⟩
  have hcomm := IsAffineOpen.SpecMap_appLE_fromSpec ν hU' hV le_rfl
  set p := hV.primeIdealOf ⟨n, hnV⟩
  have hp : hV.fromSpec p = n := hV.fromSpec_primeIdealOf ⟨n, hnV⟩
  have h1 : hU'.fromSpec (Spec.map φ p) = hU'.fromSpec ⟨⊥, inferInstance⟩ := by
    rw [map_bot_eq_genericPoint (A := Γ(X, U)) hU'.fromSpec, ← hn, ← hp]
    exact congr($hcomm p)
  have h2 := hU'.fromSpec.isOpenEmbedding.injective h1
  have h3 : p.asIdeal.comap (algebraMap Γ(X, U) Γ(N, ν ⁻¹ᵁ U)) = ⊥ :=
    congrArg PrimeSpectrum.asIdeal h2
  have h4 : p = ⟨⊥, inferInstance⟩ := PrimeSpectrum.ext (Ideal.eq_bot_of_comap_eq_bot h3)
  rw [← hp, h4]
  exact map_bot_eq_genericPoint (A := Γ(N, ν ⁻¹ᵁ U)) hV.fromSpec

theorem exists_normal_hom (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CharZero O] (Z : Model O) :
    ∃ (Z' : Model O) (n : Model.Hom Z' Z), GlobalTheory.IsNormalScheme Z'.X ∧ n.relDim = 0 := by
  set η := genericPoint Z.X
  let u : Spec (.of (Z.X.residueField η)) ⟶ Z.X := Spec.map (Z.X.residue η) ≫ Z.X.fromSpecStalk η
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (u ≫ Z.str)
  have hu : u (IsLocalRing.closedPoint (Z.X.residueField η)) = η :=
    Scheme.fromSpecResidueField_apply η _
  have hφinj : Function.Injective φ.hom := by
    have hη : (Z.str η).asIdeal = ⊥ := mem_gen_iff_eq_bot.1 Z.genericPoint_mem_gen
    have e : Spec.map φ (IsLocalRing.closedPoint (Z.X.residueField η)) = Z.str η := by
      rw [hφ]
      exact congrArg Z.str hu
    rw [RingHom.injective_iff_ker_eq_bot]
    have e' := congrArg PrimeSpectrum.asIdeal e
    rw [hη] at e'
    rw [← e']
    ext a
    change _ ↔ φ.hom a ∈ IsLocalRing.maximalIdeal _
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_ne_zero, not_not]
    rfl
  haveI : CharZero (Z.X.residueField η) := charZero_of_injective_ringHom hφinj
  haveI : CharZero (IsLocalRing.ResidueField (Z.X.presheaf.stalk η)) := charZero_of_injective_ringHom hφinj
  haveI : LocallyOfFiniteType Z.str := inferInstance
  have hfin : IsFinite u.fromNormalization :=
    GlobalTheory.isFinite_fromNormalization_SpecMap_fromSpecStalk (o := .of O) Z.str η (Z.X.residue η)
      (RingHom.FiniteType.of_surjective _ (Z.X.residue_surjective η)).essFiniteType
  let ν := u.fromNormalization
  haveI : Flat (u.fromNormalization ≫ Z.str) := by
    have : Flat (u.toNormalization ≫ u.fromNormalization ≫ Z.str) := by
      rw [← Category.assoc, Scheme.Hom.toNormalization_fromNormalization, ← hφ]
      exact Flat.SpecMap_iff.mpr (flat_of_dedekind_of_injective φ.hom hφinj)
    exact flat_normalization u _
  let Z' : Model O :=
    { X := u.normalization
      str := ν ≫ Z.str
      isIntegral := inferInstance
      isProjOver := isProjOver_comp_of_isFinite ν Z.isProjOver
      flat := ‹_› }
  have hrange : Set.range ν = Set.univ := by
    have hcl : IsClosed (Set.range ν) := ν.isClosedMap.isClosed_range
    have hmem : η ∈ Set.range ν :=
      ⟨u.toNormalization (IsLocalRing.closedPoint _), by
        change (u.toNormalization ≫ u.fromNormalization) _ = η
        rw [Scheme.Hom.toNormalization_fromNormalization]
        exact hu⟩
    refine Set.eq_univ_of_univ_subset ?_
    rw [← (genericPoint_spec Z.X).def]
    exact hcl.closure_subset_iff.2 (Set.singleton_subset_iff.2 hmem)
  haveI : Surjective ν := ⟨fun x => hrange.ge (Set.mem_univ x)⟩
  let n : Model.Hom Z' Z := ⟨ν, rfl⟩
  refine ⟨Z', n, GlobalTheory.IsNormalScheme.normalization_of_isIntegral u, ?_⟩
  have hdim := topologicalKrullDim_genFibre O Z Z' n
  haveI : Subsingleton n.genFibre := by
    constructor
    intro a b
    have key : ∀ c : n.genFibre, (ν.fiberι η) c = genericPoint Z'.X := fun c => by
      have hc : (ν.fiberι η) c ∈ ν ⁻¹' {η} := by
        rw [← Scheme.Hom.range_fiberι]; exact ⟨c, rfl⟩
      exact eq_genericPoint_of_isFinite ν hc
    exact (ν.fiberι η).isEmbedding.injective ((key a).trans (key b).symm)
  have h0 := topologicalKrullDim_zero_of_discreteTopology n.genFibre
  rw [hdim] at h0
  have h1 : n.relDim ≤ 0 := by exact_mod_cast h0
  omega

end GlobalTheory.Vert.Model

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNsmulEqZeroOfIsIntegral
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.HodgeMin

open GlobalTheory.CechPic

theorem exists_norm {K Ω : Type} [Field K] [Field Ω] (κ : K →+* Ω) {σ : Ω} (h0 : σ ≠ 0) (hσ : κ.IsIntegralElem σ) :
    ∃ (d : ℕ) (ν : K), 1 ≤ d ∧ ν ≠ 0 ∧ ∀ (R : Type) [CommRing R] (φ : R →+* K) (tr : K),
      ((κ.comp φ).IsIntegralElem (κ tr * σ) → φ.IsIntegralElem (tr ^ d * ν)) ∧
      ((κ.comp φ).IsIntegralElem (κ tr * σ)⁻¹ → φ.IsIntegralElem (tr ^ d * ν)⁻¹) := by
  letI := κ.toAlgebra
  let E := IntermediateField.adjoin K {σ}
  have : FiniteDimensional K E := IntermediateField.adjoin.finiteDimensional hσ
  let s : E := IntermediateField.AdjoinSimple.gen K σ
  have key : ∀ (R : Type) [CommRing R] (φ : R →+* K) (x : E), (κ.comp φ).IsIntegralElem (x : Ω) →
      φ.IsIntegralElem (Algebra.norm K x) := by
    intro R _ φ x ⟨P, hP, e⟩
    letI := φ.toAlgebra
    letI := ((algebraMap K E).comp φ).toAlgebra
    have : IsScalarTower R K E := .of_algebraMap_eq fun _ => rfl
    refine Algebra.isIntegral_norm (R := R) K ⟨P, hP, (algebraMap E Ω).injective ?_⟩
    rw [Polynomial.hom_eval₂, map_zero]
    exact e
  have hn : ∀ tr : K, Algebra.norm K (algebraMap K E tr * s) = tr ^ Module.finrank K E * Algebra.norm K s := fun tr => by
    rw [map_mul, Algebra.norm_algebraMap]
  refine ⟨Module.finrank K E, Algebra.norm K s, Module.finrank_pos, Algebra.norm_ne_zero_iff.2 fun h => h0 (congrArg Subtype.val h),
    fun R _ φ tr => ⟨fun h => hn tr ▸ key R φ _ h, fun h => ?_⟩⟩
  rw [← hn, ← Algebra.norm_inv]
  exact key R φ _ h

theorem exists_section {S : Scheme.{0}} [IsIntegral S] [GlobalTheory.IsNormalScheme S] (U : S.Opens) (hU : genericPoint S ∈ U)
    (x : S.functionField) (h : ∀ (V : S.Opens) (hV : genericPoint S ∈ V), IsAffineOpen V → V ≤ U →
      (S.presheaf.germ V _ hV).hom.IsIntegralElem x) : ∃ a : Γ(S, U), (S.presheaf.germ U _ hU).hom a = x := by
  have : Nonempty U := ⟨⟨_, hU⟩⟩
  refine GlobalTheory.IsNormalScheme.exists_germToFunctionField_eq_of_locally U x fun y hy => ?_
  obtain ⟨_, ⟨(V : S.Opens), hV, rfl⟩, hyV, hVU⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open hy U.isOpen
  have : Nonempty V := ⟨⟨y, hyV⟩⟩
  obtain ⟨s, hs⟩ := IsIntegrallyClosedIn.algebraMap_eq_of_integral (R := Γ(S, V)) (A := S.functionField) (x := x)
    (h V _ hV hVU)
  exact ⟨V, this, s, hyV, hVU, hs⟩

theorem exists_nsmul_eq_zero_of_isIntegral {S W : Scheme.{0}} (p : W ⟶ S) [IsIntegral S] [GlobalTheory.IsNormalScheme S]
    [UniversallyClosed p] [Surjective p] (c : Pic S) (h : pull p c = 0) : ∃ d : ℕ, 1 ≤ d ∧ d • c = 0 := by
  obtain ⟨L, hL, rfl⟩ := cls_surj c
  obtain ⟨t, ht⟩ := (cls_eq_zero_iff (pull_isLB hL p)).1 h
  let ξ := genericPoint S
  have hξ : ∀ (V : S.Opens) (y : S), y ∈ V → ξ ∈ V := fun V y hy =>
    ((genericPoint_spec S).specializes (Set.mem_univ y)).mem_open V.isOpen hy
  obtain ⟨w, hw⟩ := p.surjective ξ
  have hsp : p w ⤳ ξ := hw ▸ specializes_rfl
  have hw' : ∀ {V : S.Opens}, ξ ∈ V → p w ∈ V := fun h => hw ▸ h
  let ρ : W.presheaf.stalk w →+* W.residueField w := (W.residue w).hom
  let κ : S.functionField →+* W.residueField w := ρ.comp (S.presheaf.stalkSpecializes hsp ≫ p.stalkMap w).hom
  have hκ : ∀ (V : S.Opens) (hV : ξ ∈ V), κ.comp (S.presheaf.germ V ξ hV).hom =
      (ρ.comp (W.presheaf.germ (p ⁻¹ᵁ V) w (hw' hV)).hom).comp (p.app V).hom := fun V hV => by
    have e : S.presheaf.germ V ξ hV ≫ S.presheaf.stalkSpecializes hsp ≫ p.stalkMap w =
        p.app V ≫ W.presheaf.germ (p ⁻¹ᵁ V) w (hw' hV) := by
      rw [S.presheaf.germ_stalkSpecializes_assoc, Scheme.Hom.germ_stalkMap]
    exact congrArg (fun q => ρ.comp q.hom) e
  let σ : L.ι → W.residueField w := fun i => ρ (gm (𝟙 W) w _ (t.s fun _ => i)).val
  let tr : L.ι → L.ι → S.functionField := fun i j => (gm (𝟙 S) ξ _ (L.g i j)).val
  have hσ0 : ∀ i, σ i ≠ 0 := fun i => ((gm (𝟙 W) w _ (t.s fun _ => i)).isUnit.map ρ).ne_zero
  have hσ : ∀ i j, ξ ∈ L.U i → ξ ∈ L.U j → σ i = κ (tr i j) * σ j := fun i j hi hj => by
    have e := (isGen_iff_germ t).1 ht w (fun _ => i) (fun _ => j) (mem_pull.2 (hw' hi)) (mem_pull.2 (hw' hj))
    rw [gm_pull_g L p (𝟙 W) w _ _ (mem_pull.2 (hw' hi)) (mem_pull.2 (hw' hj)), Category.id_comp] at e
    refine (congrArg (fun u => ρ u.val) e).trans ((map_mul ρ _ _).trans (congrArg (· * σ j) ?_))
    have hij : ξ ∈ L.U i ⊓ L.U j := ⟨hi, hj⟩
    rw [gm_val p w _ (hw' hij)]
    refine (RingHom.congr_fun (hκ _ hij) _).symm.trans (congrArg κ ?_)
    exact (gm_val (𝟙 S) ξ _ hij _).symm
  have hint : ∀ i (V : S.Opens) (hV : ξ ∈ V), IsAffineOpen V → V ≤ L.U i → ∀ u : Γ(W, (L.pull p).U fun _ => i)ˣ,
      (κ.comp (S.presheaf.germ V ξ hV).hom).IsIntegralElem (ρ (gm (𝟙 W) w _ u).val) := fun i V hV ha hle u => by
    have l : p ⁻¹ᵁ V ≤ (L.pull p).U fun _ => i := fun x hx => mem_pull.2 (hle hx)
    rw [hκ, ← gm_res (𝟙 W) w l (hw' hV), gm_val (𝟙 W) w _ (hw' hV)]
    exact RingHom.IsIntegralElem.map (GenPush.isIntegral_app_of_universallyClosed p V ha (res l u).val)
      (ρ.comp (W.presheaf.germ (p ⁻¹ᵁ V) w (hw' hV)).hom)
  obtain ⟨i₀, hi₀⟩ := exists_chart hL ξ
  obtain ⟨d, ν, hd, hν, H⟩ := exists_norm κ (hσ0 i₀) (by
    obtain ⟨_, ⟨(V : S.Opens), hV, rfl⟩, hyV, hVU⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open hi₀ (L.U i₀).isOpen
    exact RingHom.IsIntegralElem.of_comp (hint i₀ V hyV hV hVU _))
  have ex : ∀ i, ∃ a : Γ(S, L.U i)ˣ, ξ ∈ L.U i → (gm (𝟙 S) ξ _ a).val = tr i i₀ ^ d * ν := fun i => by
    by_cases hi : ξ ∈ L.U i
    swap
    · exact ⟨1, fun h => (hi h).elim⟩
    obtain ⟨a, ha⟩ := exists_section (L.U i) hi (tr i i₀ ^ d * ν) fun V hV hV' hle =>
      (H _ _ _).1 (hσ i i₀ hi hi₀ ▸ hint i V hV hV' hle _)
    obtain ⟨b, hb⟩ := exists_section (L.U i) hi (tr i i₀ ^ d * ν)⁻¹ fun V hV hV' hle => (H _ _ _).2 (by
      have := hint i V hV hV' hle (t.s fun _ => i)⁻¹
      rwa [map_inv, map_units_inv ρ, show ρ _ = σ i from rfl, hσ i i₀ hi hi₀] at this)
    have hab : a * b = 1 := germ_injective_of_isIntegral S ξ hi (by
      refine (map_mul (S.presheaf.germ _ ξ hi).hom a b).trans ?_
      rw [ha, hb, map_one]
      exact mul_inv_cancel₀ (mul_ne_zero (pow_ne_zero _ (gm (𝟙 S) ξ _ (L.g i i₀)).ne_zero) hν))
    exact ⟨⟨a, b, hab, (mul_comm _ _).trans hab⟩, fun _ => (gm_val (𝟙 S) ξ _ hi _).trans ha⟩
  choose a ha using ex
  have hg : ∀ i j, res (inf_le_left : L.U i ⊓ L.U j ≤ L.U i) (a i) =
      L.g i j ^ d * res (inf_le_right : L.U i ⊓ L.U j ≤ L.U j) (a j) := fun i j => by
    by_cases hij : ξ ∈ L.U i ⊓ L.U j
    swap
    · exact unit_ext fun y hy => (hij (hξ _ y hy)).elim
    have e : gm (𝟙 S) ξ _ (res (inf_le_left : L.U i ⊓ L.U j ≤ L.U i) (a i)) =
        gm (𝟙 S) ξ _ (L.g i j ^ d * res (inf_le_right : L.U i ⊓ L.U j ≤ L.U j) (a j)) := by
      rw [map_mul, map_pow, gm_res _ ξ _ hij, gm_res _ ξ _ hij]
      apply Units.ext
      rw [Units.val_mul, Units.val_pow_eq_pow_val, ha i hij.1, ha j hij.2, ← _root_.mul_assoc, ← mul_pow]
      exact congrArg (fun u => u.val ^ d * ν) (gm_cocycle hL (𝟙 S) ξ hij.1 hij.2 hi₀).symm
    have e' := congrArg Units.val e
    rw [gm_val _ ξ _ hij, gm_val _ ξ _ hij] at e'
    exact Units.ext (germ_injective_of_isIntegral S ξ hij e')
  refine ⟨d, hd, ?_⟩
  rw [← cls_lbPow hL d (isLB_lbPow hL d), cls_eq_zero_iff]
  refine ⟨⟨fun J => res (LB.wchart_le L (fun _ : PUnit => 𝟙 S) J PUnit.unit) (a (J PUnit.unit))⟩,
    (isGen_iff_germ _).2 fun y J J' hJ hJ' => ?_⟩
  have m : y ∈ L.U (J PUnit.unit) ⊓ L.U (J' PUnit.unit) := ⟨Set.mem_iInter.1 hJ PUnit.unit, Set.mem_iInter.1 hJ' PUnit.unit⟩
  have e := congrArg (gm (𝟙 S) y _) (hg (J PUnit.unit) (J' PUnit.unit))
  rw [map_mul, map_pow, gm_res _ y _ m, gm_res _ y _ m] at e
  refine (gm_res (𝟙 S) y _ hJ _).trans (e.trans (congrArg₂ (· * ·) ?_ (gm_res (𝟙 S) y _ hJ' _).symm))
  refine Eq.trans ?_ (gm_linComb L (fun _ : PUnit => 𝟙 S) (fun _ => (d : ℤ)) (𝟙 S) y J J' hJ hJ').symm
  rw [Fintype.prod_unique, zpow_natCast, Category.id_comp]

theorem exists_nsmul_eq_zero {S W : Scheme.{0}} [AlgebraicGeometry.IsNoetherian S] (hS : Geo.Tor.IsNormalScheme S) (p : W ⟶ S)
    [UniversallyClosed p] [Surjective p] (c : Pic S) (h : pull p c = 0) : ∃ d : ℕ, 1 ≤ d ∧ d • c = 0 := by
  have := GlobalTheory.IsNormalScheme.of_pred hS
  have := Fintype.ofFinite (irreducibleComponents S)
  choose d hd H using fun C : irreducibleComponents S =>
    exists_nsmul_eq_zero_of_isIntegral (pullback.snd p (IsNormalScheme.component C).ι) (pull (IsNormalScheme.component C).ι c)
      (by rw [← pull_comp, ← pullback.condition, pull_comp, h, map_zero])
  refine ⟨∏ C, d C, Finset.prod_pos (s := Finset.univ) (f := d) fun C _ => hd C, ?_⟩
  obtain ⟨L, hL, e⟩ := cls_surj ((∏ C, d C) • c)
  rw [← e]
  refine (cls_eq_iff hL (LB.isLB_triv S)).2 (DisjointCoverLB.lbIso_of_disjoint_cover S _ IsNormalScheme.component
    (fun a b y ha hb => Subtype.ext (IsNormalScheme.eq_of_mem_irreducibleComponents a.2 b.2 ha hb))
    (fun y => ⟨⟨_, irreducibleComponent_mem_irreducibleComponents y⟩, mem_irreducibleComponent⟩) L _ hL (LB.isLB_triv S)
    fun C => (cls_eq_iff (pull_isLB hL _) (pull_isLB (LB.isLB_triv S) _)).1 ?_)
  obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem d (Finset.mem_univ C)
  rw [cls_pull hL, cls_pull (LB.isLB_triv S), e, map_nsmul, hk, mul_comm, mul_smul, H, smul_zero]
  exact (map_zero _).symm

theorem exists_common_cover {R : Type} [CommRing R] [IsDedekindDomain R] [CharZero R] {Z S S' U : Scheme.{0}} (z : Z ⟶ Sp R)
    (π : S ⟶ Z) (π' : S' ⟶ Z) [LocallyOfFiniteType (π ≫ z)] [QuasiSeparated π] [IsProper π'] [IsLocallyNoetherian S']
    (hS' : Geo.Tor.IsNormalScheme S') (a : U ⟶ S) (k : U ⟶ S') [IsOpenImmersion k] (w : a ≫ π = k ≫ π')
    (hd : Dense (a '' {x | ((a ≫ π ≫ z) x).asIdeal = ⊥}))
    {A : Over U} [GrpObj A] {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] (hG : IsSemiAbelian G) (hG' : IsSemiAbelian G')
    {φ : A.left ⟶ G.left} {ψ : A.left ⟶ G'.left} (hφ : IsGrpPullback A G a φ) (hψ : IsGrpPullback A G' k ψ) :
    ∃ (W : Scheme.{0}) (p : W ⟶ S) (p' : W ⟶ S') (H : Over W) (_ : GrpObj H) (α : H.left ⟶ G.left) (β : H.left ⟶ G'.left),
      IsProper p ∧ Surjective p ∧ p ≫ π = p' ≫ π' ∧ IsGrpPullback H G p α ∧ IsGrpPullback H G' p' β := by
  let K := FractionRing R
  let b : Sp K ⟶ Sp R := spMap (algebraMap R K)
  have : IsPreimmersion b := IsPreimmersion.of_isLocalization (R := CommRingCat.of R) (S := K) (nonZeroDivisors R)
  have : Flat b := Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 (IsLocalization.flat K (nonZeroDivisors R)))
  let T := pullback (a ≫ π ≫ z) b
  let t : T ⟶ U := pullback.fst _ _
  have := GlobalTheory.IsNormalScheme.of_pred hS'
  have : QuasiCompact k := inferInstance
  have := isIso_stalkMap_of_flat_of_surjectiveOnStalks (t ≫ k)
  have : GlobalTheory.IsNormalScheme T := GlobalTheory.IsNormalScheme.of_isIso_stalkMap (t ≫ k)
  have : IsLocallyNoetherian T := AmpUniq.isLocallyNoetherian_of_isPreimmersion (t ≫ k)
  let f : T ⟶ pullback π π' := pullback.lift (t ≫ a) (t ≫ k) (by simp [w])
  have hf₁ : f ≫ pullback.fst π π' = t ≫ a := pullback.lift_fst _ _ _
  have hf₂ : f ≫ pullback.snd π π' = t ≫ k := pullback.lift_snd _ _ _
  have : IsPreimmersion (f ≫ pullback.snd π π') := hf₂ ▸ inferInstance
  have : IsPreimmersion f := AmpUniq.isPreimmersion_of_comp f (pullback.snd π π')
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian (π ≫ z)
  have : IsLocallyNoetherian (pullback π π') := LocallyOfFiniteType.isLocallyNoetherian (pullback.fst π π')
  have : QuasiCompact (f ≫ pullback.snd π π') := hf₂ ▸ inferInstance
  have : QuasiCompact f := .of_comp f (pullback.snd π π')
  have : Flat (f ≫ pullback.fst π π' ≫ π ≫ z) := by
    rw [reassoc_of% hf₁, pullback.condition]; infer_instance
  have : IsFinite f.fromNormalization := AmpUniq.isFinite_fromNormalization_graph f (pullback.fst π π' ≫ π ≫ z)
  let u := f.toNormalization
  let p := f.fromNormalization ≫ pullback.fst π π'
  let p' := f.fromNormalization ≫ pullback.snd π π'
  have hu₁ : u ≫ p = t ≫ a := by simp [u, p, hf₁]
  have hu₂ : u ≫ p' = t ≫ k := by simp [u, p', hf₂]
  have : IsPreimmersion (u ≫ p') := hu₂ ▸ inferInstance
  have : IsPreimmersion u := AmpUniq.isPreimmersion_of_comp u p'
  have : Flat u := AmpUniq.flat_of_isPreimmersion u
  have hN := GlobalTheory.IsNormalScheme.pred f.normalization
  have : IsLocallyNoetherian f.normalization := LocallyOfFiniteType.isLocallyNoetherian p
  have : IsDominant (u ≫ p) := by
    rw [hu₁]
    refine ⟨hd.mono ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    have : x ∈ Set.range t := by
      rw [Scheme.Pullback.range_fst]
      refine ⟨closedPoint K, PrimeSpectrum.ext ?_⟩
      refine Eq.trans ?_ hx.symm
      change Ideal.comap (algebraMap R K) (maximalIdeal K) = ⊥
      rw [maximalIdeal_eq_bot, Ideal.comap_bot_of_injective _ (IsFractionRing.injective R K)]
    obtain ⟨y, rfl⟩ := this
    exact ⟨y, by simp⟩
  have : IsDominant p := .of_comp u p
  have lift : ∀ {Y : Scheme.{0}} {B : Over Y} [GrpObj B] (q : f.normalization ⟶ Y) {c : U ⟶ Y} {χ : A.left ⟶ B.left},
      IsGrpPullback A B c χ → u ≫ q = t ≫ c →
      ∃ χ', IsGrpPullback ((Over.pullback t).obj A) ((Over.pullback q).obj B) u χ' := by
    intro Y B _ q c χ h e
    have h' := ((isGrpPullback_pullback A t).comp h).congr e.symm rfl
    exact ⟨pullback.lift _ _ (h'.1.w.trans (Category.assoc _ _ _).symm), (isGrpPullback_pullback B q).cancel
      (h'.congr rfl (pullback.lift_fst _ _ _).symm) (pullback.lift_snd _ _ _)⟩
  obtain ⟨_, a₁⟩ := lift p hφ hu₁
  obtain ⟨_, a₂⟩ := lift p' hψ hu₂
  obtain ⟨e, _⟩ := HodgeGenDesc.exists_iso_of_extensions u hN (IsSemiAbelian.pullback p G hG)
    (IsSemiAbelian.pullback p' G' hG') a₁ a₂
  exact ⟨f.normalization, p, p', (Over.pullback p).obj G, inferInstance, _, _, inferInstance,
    surjective_of_isDominant_of_isClosed_range p p.isClosedMap.isClosed_range, by simp [p, p', pullback.condition],
    isGrpPullback_pullback G p,
    ((isGrpPullback_of_iso e).comp (isGrpPullback_pullback G' p')).congr (Category.id_comp _) rfl⟩

end GlobalTheory.HodgeMin

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPicPatch
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.PinchLift

theorem exists_pic_patch : ∀ (X X' Z Z' : Scheme.{0}) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z), IsPullback i' p' p i → IsAffineHom p → IsClosedImmersion i → GlobalTheory.PinchLift.Glues p i i' p' → ∀ (a : Pic X') (b : Pic Z), GlobalTheory.CechPic.pull i' a = GlobalTheory.CechPic.pull p' b → ∃ e : Pic X, GlobalTheory.CechPic.pull p e = a ∧ GlobalTheory.CechPic.pull i e = b := by
  have hA1 := GlobalTheory.T.exists_lineBundle_generator_off_closed_subscheme
  have hA2 := GlobalTheory.T.exists_matching_lineBundle_generators_near_pinching_point
  have hB := GlobalTheory.T.pinchingSquare_glue_lineBundle_of_local_generators
  intro X X' Z Z' p i i' p' hsq hp hi hgl a b hab
  obtain ⟨L', hL', rfl⟩ := cls_surj a
  obtain ⟨LZ, hLZ, rfl⟩ := cls_surj b
  rw [← cls_pull hL' i' (pull_isLB hL' i'), ← cls_pull hLZ p' (pull_isLB hLZ p')] at hab
  obtain ⟨w, hw⟩ := (cls_eq_iff _ _).1 hab
  refine hB X X' Z Z' p i i' p' hsq hgl L' LZ hL' hLZ w hw fun x => ?_
  by_cases hx : ∃ z, i z = x
  · obtain ⟨z, rfl⟩ := hx
    exact hA2 X X' Z Z' p i i' p' hsq hp hi hgl L' LZ hL' hLZ w hw z
  · push_neg at hx
    obtain ⟨W, s', hxW, hbot, hs'⟩ := hA1 X X' Z Z' p i i' p' hsq hp hi hgl L' hL' x hx
    have hno : ∀ y : Z, y ∉ i ⁻¹ᵁ W := fun y hy => by rw [hbot] at hy; exact hy
    refine ⟨W, s', fun _ => 1, hxW, hs', fun k l y _ _ hy => (hno y hy).elim,
      fun z j k _ _ hz _ => (hno _ hz).elim⟩

end GlobalTheory.PinchLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolAVCommonPullback
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc

theorem exists_polAV_common_pullback : ∀ (Ω : Type) [Field Ω] (T T' : Scheme.{0}) (Q : PolAV T) (P' : PolAV T') (f : Sp Ω ⟶ T) (f' : Sp Ω ⟶ T') (G' : Over (Sp Ω)) [GrpObj G'] (a₁ : G'.left ⟶ Q.A.left) (a₂ : G'.left ⟶ P'.A.left), IsGrpPullback G' Q.A f a₁ → IsGrpPullback G' P'.A f' a₂ → LBIso (Q.L.pull a₁) (P'.L.pull a₂) → ∃ (P₀ : PolAV (Sp Ω)) (a : P₀.A.left ⟶ Q.A.left) (a' : P₀.A.left ⟶ P'.A.left) (e : G'.left ⟶ P₀.A.left), IsIso e ∧ e ≫ a = a₁ ∧ e ≫ a' = a₂ ∧ IsGrpPullback P₀.A Q.A f a ∧ IsGrpPullback P₀.A P'.A f' a' ∧ LBIso P₀.L (Q.L.pull a) ∧ LBIso P₀.L (P'.L.pull a') := by
  intro Ω _ T T' Q P' f f' G' _ a₁ a₂ h₁ h₂ hL
  obtain ⟨P₀, φ, hφ, hL₀⟩ := exists_pol_baseChange Q f
  obtain ⟨e, he, hea⟩ := grpPullback_iso h₁ hφ
  haveI := he
  have hinv : IsMonHom e.symm.hom := inferInstanceAs (IsMonHom e.inv)
  have hφ' : φ = e.inv.left ≫ a₁ := by
    rw [← hea, ← Category.assoc, ← Over.comp_left, e.inv_hom_id, Over.id_left, Category.id_comp]
  have hiso : IsIso e.hom.left := ⟨⟨e.inv.left, by rw [← Over.comp_left, e.hom_inv_id, Over.id_left],
    by rw [← Over.comp_left, e.inv_hom_id, Over.id_left]⟩⟩
  refine ⟨P₀, φ, e.inv.left ≫ a₂, e.hom.left, hiso, hea, ?_, hφ, ?_, hL₀, ?_⟩
  · rw [← Category.assoc, ← Over.comp_left, e.hom_inv_id, Over.id_left, Category.id_comp]
  · exact ((isGrpPullback_of_iso e.symm).comp h₂).congr (Category.id_comp _) rfl
  · exact LBIso.trans P₀.isLB (pull_isLB Q.isLB _) (pull_isLB P'.isLB _) hL₀
      (GenSpread.lbIso_pull_comp e.inv.left hφ' rfl hL)

end GlobalTheory.UPoinc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolAVRingOnNear
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UPoinc

theorem USetup.exists_polAV_ringOn_near : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X : USetup C) (w₀ : X.M.Z), X.π w₀ ∈ Set.range C.i → ∀ (U₀ : X.M.Z.Opens) (u₀ : Sp (ratHull (X.M.ringOn U₀)) ⟶ Xo.XF cf), IsAffineOpen U₀ → w₀ ∈ U₀ → spMap (ratHull (X.M.ringOn U₀)).val.toRingHom ≫ u₀ = X.uΩ → ∃ (U₁ : X.M.Z.Opens) (h : X.M.ringOn U₀ ≤ X.M.ringOn U₁) (P₁ : PolAV (Sp (X.M.ringOn U₁))), U₁ ≤ U₀ ∧ IsAffineOpen U₁ ∧ w₀ ∈ U₁ ∧ UOver Xo cf P₁ (toRat (X.M.ringOn U₁)) (spMap (Subalgebra.inclusion (ratHull_mono h)).toRingHom ≫ u₀) :=
  fun E _ _ _ H Dw _ l Xo cf C X w₀ hw U₀ u₀ hU hwU _ =>
    LocSpread.exists_uOver_ringOn E H Dw l Xo cf C X U₀ u₀ w₀ hU hwU hw

end GlobalTheory.UPoinc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarisedAbelianSemiAbelianSiegelPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_polarisedAbelian_semiAbelian_siegelPoint : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V],
    GlobalTheory.Mum.Base V → IsDiscreteValuationRing V → ∀ y : Sp (FractionRing V) ⟶ F.X,
      ∃ (V₁ : Type) (_ : CommRing V₁) (_ : IsDomain V₁) (_ : IsLocalRing V₁) (f : V →+* V₁)
        (fK : FractionRing V →+* FractionRing V₁), GlobalTheory.LN.CDvr V₁ ∧ Function.Injective f ∧ IsLocalHom f ∧ f.Finite ∧
        (∀ a, fK (algebraMap V _ a) = algebraMap V₁ _ (f a)) ∧
        ∃ (A : PolAV (Sp (FractionRing V₁))) (α : A.A.left ⟶ F.univ.A.left) (α₂ : (G2 A.A).left ⟶ (G2 F.univ.A).left),
          IsGrpPullback A.A F.univ.A (spMap fK ≫ y) α ∧ IsSquare α α₂ ∧ LBIso (abelian₂ A.A A.L) (F.univ.P.pull α₂) ∧
          ∃ (G : Over (Sp V₁)) (_ : GrpObj G) (_ : IsCommMonObj G) (gen : (Over.pullback (jK V₁)).obj G ≅ A.A),
            IsSemiAbelian G ∧ IsMonHom gen.hom := by
  first | exact @GlobalTheory.CExtGen.exists_polAV_semiAbelian | exact GlobalTheory.CExtGen.exists_polAV_semiAbelian | (intros; apply GlobalTheory.CExtGen.exists_polAV_semiAbelian <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPosNonzeroPairSectionOfAmpleStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pos_nonzero_pairSection_of_ample : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.A.B → ∀ (a : ℤ), ∃ (c : ℕ) (h : X.functionField), 0 < c ∧ h ≠ 0 ∧ h ∈ P.H a c := by
  first | exact @GlobalTheory.HSNef.exists_pos_nonzero_mem_H | exact GlobalTheory.HSNef.exists_pos_nonzero_mem_H | (intros; apply GlobalTheory.HSNef.exists_pos_nonzero_mem_H <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullDegIdentitySelfAdmissibleStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pullDeg_identity_self_admissible : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I),
    ∃ h : IsPullDeg (RingHom.id R) D.toPre D.toPre, (∀ x, h.xe x = x) ∧
      h.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R)) = 𝟙 _ := by
  first | exact @GlobalTheory.DegPullId.exists_isPullDeg_id_self | exact GlobalTheory.DegPullId.exists_isPullDeg_id_self | (intros; apply GlobalTheory.DegPullId.exists_isPullDeg_id_self <;> assumption)
end

