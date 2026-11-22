import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1031
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNonzeroLocusFormMap
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BijectiveAlgebraMapIntegralClosureOfBirational
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0054
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0027
import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.Bundle0001
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0281
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0288
import Formalism.LocalToGlobal.IndefiniteReal.HeckeNonvanishing.Imports
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0017
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0022
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0283
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0292
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
import Formalism.LocalToGlobal.HermitianForms.Bundle0006
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0222
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.LatticeIdealNonzero
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0013
import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
import Formalism.LocalRingCardinality.Bundle0004
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0036
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0041
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0293
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VecMulVecComm

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingKrullDimLeOfIsAlgebraic
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.ModelDom

theorem ringKrullDim_le_of_isAlgebraic (A B : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [CommRing B]
    [IsDomain B] [Algebra A B] [FaithfulSMul A B] [Algebra.FiniteType A B] [Algebra.IsAlgebraic A B] :
    ringKrullDim B ≤ ringKrullDim A := by
  classical
  have step : ∀ (R S : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [CommRing S] [IsDomain S] (f : R →+* S),
      Function.Injective f → ∀ x : S, Function.Surjective (Polynomial.eval₂RingHom f x) →
      (∃ g : Polynomial R, g ≠ 0 ∧ Polynomial.eval₂ f x g = 0) → ringKrullDim S ≤ ringKrullDim R := by
    intro R S _ _ _ _ _ f hf x hgen halg
    rw [ringKrullDim_le_iff_height_le]
    intro q hq
    have h := ReciprocityTheory.CA.height_le_height_comap_of_eval₂_surjective f hf x hgen halg q
    have h2 : ((q.comap f).height : WithBot ℕ∞) ≤ ringKrullDim R :=
      Ideal.height_le_ringKrullDim_of_ne_top (Ideal.IsPrime.ne_top inferInstance)
    exact (WithBot.coe_le_coe.2 h).trans h2
  have key : ∀ s : Finset B, ringKrullDim (Algebra.adjoin A (s : Set B)) ≤ ringKrullDim A := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      refine step A _ (algebraMap A _) (FaithfulSMul.algebraMap_injective _ _) 0 ?_
        ⟨Polynomial.X, Polynomial.X_ne_zero, by simp⟩
      rintro ⟨y, hy⟩
      rw [Finset.coe_empty, Algebra.adjoin_empty, Algebra.mem_bot] at hy
      obtain ⟨a, rfl⟩ := hy
      exact ⟨Polynomial.C a, Subtype.ext (by simp)⟩
    | insert x s _ ih =>
      have hle : Algebra.adjoin A (s : Set B) ≤ Algebra.adjoin A ((insert x s : Finset B) : Set B) :=
        Algebra.adjoin_mono (by simp)
      have : Algebra.FiniteType A (Algebra.adjoin A (s : Set B)) :=
        Algebra.FiniteType.adjoin_of_finite s.finite_toSet
      have : IsNoetherianRing (Algebra.adjoin A (s : Set B)) := Algebra.FiniteType.isNoetherianRing A _
      have hx : x ∈ Algebra.adjoin A ((insert x s : Finset B) : Set B) := Algebra.subset_adjoin (by simp)
      refine le_trans (step _ _ (Subalgebra.inclusion hle).toRingHom (Subalgebra.inclusion_injective hle) ⟨x, hx⟩
        ?_ ?_) ih
      · rintro ⟨y, hy⟩
        induction hy using Algebra.adjoin_induction with
        | mem y hy =>
          rw [Finset.coe_insert] at hy
          rcases hy with rfl | hy
          · exact ⟨Polynomial.X, by simp⟩
          · exact ⟨Polynomial.C ⟨y, Algebra.subset_adjoin hy⟩, Subtype.ext (by simp)⟩
        | algebraMap a => exact ⟨Polynomial.C (algebraMap A _ a), Subtype.ext (by simp)⟩
        | add y z _ _ hy hz =>
          obtain ⟨p, hp⟩ := hy
          obtain ⟨q, hq⟩ := hz
          exact ⟨p + q, by rw [map_add, hp, hq]; rfl⟩
        | mul y z _ _ hy hz =>
          obtain ⟨p, hp⟩ := hy
          obtain ⟨q, hq⟩ := hz
          exact ⟨p * q, by rw [map_mul, hp, hq]; rfl⟩
      · obtain ⟨g, hg, h0⟩ := Algebra.IsAlgebraic.isAlgebraic (R := A) x
        refine ⟨g.map (algebraMap A _), (Polynomial.map_ne_zero_iff (FaithfulSMul.algebraMap_injective _ _)).2 hg, ?_⟩
        apply Subtype.ext
        rw [Polynomial.eval₂_map]
        have := Polynomial.hom_eval₂ g
          ((Subalgebra.inclusion hle).toRingHom.comp (algebraMap A (Algebra.adjoin A (s : Set B))))
          (Algebra.adjoin A ((insert x s : Finset B) : Set B)).val.toRingHom ⟨x, hx⟩
        exact this.trans h0
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := A) (A := B)
  have := key s
  rw [hs] at this
  exact (ringKrullDim_eq_of_ringEquiv Subalgebra.topEquiv.toRingEquiv).ge.trans this

theorem dim_le_of_birational {N M : Scheme.{0}} [IsIntegral N] [IsIntegral M] [IsLocallyNoetherian M] (π : N ⟶ M)
    [LocallyOfFiniteType π] [IsDominant π] [IsIso (π.stalkMap (genericPoint N))] :
    topologicalKrullDim N ≤ topologicalKrullDim M := by
  have hd : ∀ {Z : Scheme.{0}} (U : Z.Opens), IsAffineOpen U →
      topologicalKrullDim (U : Set Z) = ringKrullDim Γ(Z, U) := fun {Z} U hU => by
    rw [topologicalKrullDim_eq_of_isEmbedding hU.fromSpec.isOpenEmbedding.isEmbedding hU.range_fromSpec]
    exact PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := Γ(Z, U))
  refine topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_
  obtain ⟨U, hU, hxU, -⟩ := Opens.isBasis_iff_nbhd.1 M.isBasis_affineOpens (Opens.mem_top (π x))
  obtain ⟨V, hV, hxV, hVU⟩ := Opens.isBasis_iff_nbhd.1 N.isBasis_affineOpens (show x ∈ π ⁻¹ᵁ U from hxU)
  refine ⟨V, V.isOpen, hxV, ?_⟩
  refine le_trans ?_ (topologicalKrullDim_subspace_le M (U : Set M))
  rw [hd U hU, hd V hV]
  have : Nonempty U := ⟨⟨_, hxU⟩⟩
  have : Nonempty V := ⟨⟨_, hxV⟩⟩
  have : IsNoetherianRing Γ(M, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  letI := (π.appLE U V hVU).hom.toAlgebra
  have : Algebra.FiniteType Γ(M, U) Γ(N, V) := π.finiteType_appLE hU hV hVU
  have hη := apply_genericPoint_of_isDominant π
  have hηV : genericPoint N ∈ V :=
    ((genericPoint_spec N).mem_open_set_iff V.isOpen).mpr ⟨x, trivial, hxV⟩
  have hyU : π (genericPoint N) ∈ U := hVU hηV
  letI := M.presheaf.algebra_section_stalk (U := U) ⟨_, hyU⟩
  have hfr := isFractionRing_stalk_of_eq_genericPoint hU _ hyU hη
  have hgerm (a : Γ(M, U)) : π.stalkMap (genericPoint N) (M.presheaf.germ U _ hyU a) =
      N.presheaf.germ V (genericPoint N) hηV (π.appLE U V hVU a) := by
    rw [π.germ_stalkMap_apply U _ hyU a, Scheme.Hom.appLE, CommRingCat.comp_apply,
      TopCat.Presheaf.germ_res_apply]
  have hbij : Function.Bijective (π.stalkMap (genericPoint N)) := ConcreteCategory.bijective_of_isIso _
  have hinj : Function.Injective (algebraMap Γ(M, U) Γ(N, V)) := fun a a' h => by
    have h' : π.appLE U V hVU a = π.appLE U V hVU a' := h
    apply germ_injective_of_isIntegral M _ hyU
    apply hbij.1
    rw [hgerm, hgerm, h']
  have : FaithfulSMul Γ(M, U) Γ(N, V) := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  let φ : Γ(N, V) ⟶ M.presheaf.stalk (π (genericPoint N)) :=
    N.presheaf.germ V (genericPoint N) hηV ≫ inv (π.stalkMap (genericPoint N))
  have hφ (c : Γ(N, V)) : π.stalkMap (genericPoint N) (φ c) = N.presheaf.germ V (genericPoint N) hηV c := by
    rw [← CommRingCat.comp_apply, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  let ψ : Γ(N, V) →ₐ[Γ(M, U)] M.presheaf.stalk (π (genericPoint N)) :=
    { φ.hom with
      commutes' := fun a ↦ hbij.1 ((hφ _).trans (hgerm a).symm) }
  have hψ : Function.Injective ψ := fun a b h => by
    apply germ_injective_of_isIntegral N _ hηV
    rw [← hφ, ← hφ]
    exact congrArg _ h
  have : Algebra.IsAlgebraic Γ(M, U) (M.presheaf.stalk (π (genericPoint N))) :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors Γ(M, U))
  have : Algebra.IsAlgebraic Γ(M, U) Γ(N, V) := Algebra.IsAlgebraic.of_injective ψ hψ
  exact ringKrullDim_le_of_isAlgebraic _ _

theorem exists_isIso_restrict {Y N M : Scheme.{0}} [IsIntegral Y] [IsIntegral N] [IsIntegral M] (jN : Y ⟶ N)
    [IsDominant jN] (π : N ⟶ M) [IsSeparated π] [LocallyOfFiniteType π] (j : Y ⟶ M) [Flat j] [SurjectiveOnStalks j]
    (h : jN ≫ π = j) : ∃ U : M.Opens, (U : Set M).Nonempty ∧ IsIso (π ∣_ U) := by
  have := isIso_stalkMap_of_flat_of_surjectiveOnStalks j (genericPoint Y)
  let φ : Spec (M.presheaf.stalk (j (genericPoint Y))) ⟶ N :=
    Spec.map (inv (j.stalkMap (genericPoint Y))) ≫ Y.fromSpecStalk (genericPoint Y) ≫ jN
  have hφ : φ ≫ π = M.fromSpecStalk (j (genericPoint Y)) ≫ 𝟙 M := by
    simp only [φ, Category.assoc, h, Category.comp_id]
    rw [← Scheme.SpecMap_stalkMap_fromSpecStalk, ← Category.assoc, ← Spec.map_comp, IsIso.hom_inv_id, Spec.map_id,
      Category.id_comp]
  obtain ⟨U, hU, g, hg₁, hg₂⟩ := spread_out_of_isGermInjective' (𝟙 M) π φ hφ
  rw [Category.comp_id] at hg₂
  have : IsDominant (Y.fromSpecStalk (genericPoint Y)) :=
    ⟨((dense_iff_closure_eq.2 (genericPoint_spec Y)).mono
      (Set.singleton_subset_iff.2 ⟨_, Scheme.fromSpecStalk_closedPoint⟩))⟩
  have : IsDominant φ := inferInstance
  have : IsDominant g := by
    rw [hg₁] at this
    exact IsDominant.of_comp (U.fromSpecStalkOfMem _ hU) g
  exact ⟨U, ⟨_, hU⟩, GlobalTheory.ZH.isIso_morphismRestrict_of_local_dominant_sections π U fun y hy =>
    ⟨U, U.ι, inferInstance, g, ⟨⟨y, hy⟩, rfl⟩, by simp, ‹_›, hg₂⟩⟩

theorem exists_normal_dominating (F : Type) [Field F] [NumberField F] (Y : Var F) (M M' : TrueGeo.Model Y) :
    ∃ (N : TrueGeo.Model Y) (π : N.X ⟶ M.X) (π' : N.X ⟶ M'.X), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme N.X ∧
      π ≫ M.p = N.p ∧ π' ≫ M'.p = N.p ∧ N.j ≫ π = M.j ∧ N.j ≫ π' = M'.j ∧
      (∃ U : M.X.Opens, (U : Set M.X).Nonempty ∧ IsIso (π ∣_ U)) ∧
      ∃ U : M'.X.Opens, (U : Set M'.X).Nonempty ∧ IsIso (π' ∣_ U) := by
  have H₀ := M.pb
  have := M.ar.isIntegral
  have := M'.ar.isIntegral
  have := M.ar.isLocallyNoetherian
  have : IsProper M.p := CommonModel.isProper_of_isProjOver M.ar.isProjOver
  have : IsProper M'.p := CommonModel.isProper_of_isProjOver M'.ar.isProjOver
  let r := pullback.fst M.p M'.p
  let h : Y.X ⟶ pullback M.p M'.p := pullback.lift M.j M'.j (M.pb.w.trans M'.pb.w.symm)
  have hr : h ≫ r = M.j := pullback.lift_fst _ _ _
  have hr' : h ≫ pullback.snd M.p M'.p = M'.j := pullback.lift_snd _ _ _
  have hW : IsProjOver (r ≫ M.p) := GlobalTheory.ProjSpace.isProjOver_pullback M.ar.isProjOver M'.ar.isProjOver
  have w : h ≫ r ≫ M.p = Y.str ≫ spMap (algebraMap (𝓞 F) F) := by rw [← Category.assoc, hr, H₀.w]
  have hb := IsPullback.of_hasPullback (r ≫ M.p) (spMap (algebraMap (𝓞 F) F))
  let f' : Y.X ⟶ pullback (r ≫ M.p) (spMap (algebraMap (𝓞 F) F)) := pullback.lift h Y.str w
  let ρ : pullback (r ≫ M.p) (spMap (algebraMap (𝓞 F) F)) ⟶ Y.X :=
    H₀.lift (pullback.fst _ _ ≫ r) (pullback.snd _ _) (by rw [Category.assoc]; exact hb.w)
  have hρ : ρ ≫ Y.str = pullback.snd _ _ := H₀.lift_snd _ _ _
  have hfρ : f' ≫ ρ = 𝟙 Y.X := by
    apply H₀.hom_ext
    · rw [Category.assoc, H₀.lift_fst, pullback.lift_fst_assoc, hr, Category.id_comp]
    · rw [Category.assoc, hρ, pullback.lift_snd, Category.id_comp]
  have : IsSeparated (ρ ≫ Y.str) := by rw [hρ]; infer_instance
  have : IsSeparated ρ := IsSeparated.of_comp ρ Y.str
  have : IsClosedImmersion (f' ≫ ρ) := by rw [hfρ]; infer_instance
  have : IsClosedImmersion f' := IsClosedImmersion.of_comp f' ρ
  have hh : h = f' ≫ 𝟙 _ ≫ pullback.fst _ _ := by rw [Category.id_comp, pullback.lift_fst]
  have : IsAffineHom (pullback.fst (r ≫ M.p) (spMap (algebraMap (𝓞 F) F))) :=
    MorphismProperty.of_isPullback hb.flip (isAffineHom_of_isAffine _)
  have : IsAffineHom h := by rw [hh]; infer_instance
  have hpb := GlobalTheory.isPullback_toNormalization_of_isLocalization (nonZeroDivisors (𝓞 F)) hb f' (𝟙 _) h hh
  rw [Category.id_comp] at hpb
  have hfin : IsFinite h.fromNormalization :=
    GlobalTheory.isFinite_fromNormalization_of_over_fractionRing (o := .of (𝓞 F)) h (r ≫ M.p) F Y.str w
  have : GlobalTheory.IsNormalScheme Y.X := Y.isNormalScheme
  have : GlobalTheory.IsNormalScheme h.normalization := GlobalTheory.IsNormalScheme.normalization_of_isIntegral h
  have hint : IsIntegral h.normalization := inferInstance
  have : Flat (spMap (algebraMap (𝓞 F) F)) := flat_specMap_localization (nonZeroDivisors (𝓞 F)) F
  have : IsPreimmersion (spMap (algebraMap (𝓞 F) F)) :=
    IsPreimmersion.of_isLocalization (R := 𝓞 F) (S := F) (nonZeroDivisors (𝓞 F))
  have : Flat M.j := MorphismProperty.of_isPullback M.pb.flip ‹_›
  have : Flat M'.j := MorphismProperty.of_isPullback M'.pb.flip ‹_›
  have : IsPreimmersion M.j := MorphismProperty.of_isPullback M.pb.flip ‹_›
  have : IsPreimmersion M'.j := MorphismProperty.of_isPullback M'.pb.flip ‹_›
  have e₁ : h.toNormalization ≫ h.fromNormalization ≫ r = M.j := by
    rw [← Category.assoc, Scheme.Hom.toNormalization_fromNormalization, hr]
  have e₂ : h.toNormalization ≫ h.fromNormalization ≫ pullback.snd M.p M'.p = M'.j := by
    rw [← Category.assoc, Scheme.Hom.toNormalization_fromNormalization, hr']
  have hU := exists_isIso_restrict h.toNormalization (h.fromNormalization ≫ r) M.j e₁
  have hU' := exists_isIso_restrict h.toNormalization (h.fromNormalization ≫ pullback.snd M.p M'.p) M'.j e₂
  have hdim : topologicalKrullDim h.normalization = (Y.dim + 1 : ℕ) := by
    obtain ⟨U, hne, _⟩ := hU
    obtain ⟨_, _⟩ := birational_of_isIso_morphismRestrict (h.fromNormalization ≫ r) U hne.to_subtype
    have := surjective_of_isDominant_of_isClosed_range (h.fromNormalization ≫ r)
      (h.fromNormalization ≫ r).isClosedMap.isClosed_range
    rw [← M.ar.dim_eq]
    exact (dim_le_of_birational (h.fromNormalization ≫ r)).antisymm
      (PosBaseChange.dim_le_of_isClosedMap (h.fromNormalization ≫ r).isClosedMap
        (h.fromNormalization ≫ r).surjective)
  have hfl : Flat (h.fromNormalization ≫ r ≫ M.p) := GlobalTheory.flat_fromNormalization_comp h F (r ≫ M.p) Y.str w
  have hfZ : Flat (spMap (Int.castRingHom (𝓞 F))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat ℤ (𝓞 F))
  have hpb' := hpb.paste_vert hb
  rw [pullback.lift_snd] at hpb'
  refine ⟨⟨h.normalization, h.fromNormalization ≫ r ≫ M.p,
    ⟨M.ar.isDomain, M.ar.finite, hint, GlobalTheory.isProjOver_comp_of_finite _ _ _ _ _ hfin hW, inferInstance, hdim⟩,
    h.toNormalization, hpb'⟩, h.fromNormalization ≫ r, h.fromNormalization ≫ pullback.snd M.p M'.p,
    GlobalTheory.IsNormalScheme.pred _, Category.assoc _ _ _, ?_, e₁, e₂, hU, hU'⟩
  change (h.fromNormalization ≫ pullback.snd M.p M'.p) ≫ M'.p = h.fromNormalization ≫ r ≫ M.p
  rw [Category.assoc, ← pullback.condition]

end GlobalTheory.ModelDom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ScalarsZeroPartConventionFixedPlace
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section
namespace GlobalTheory.Mem.R3

section Gen

theorem majAt_eq_zero_of_self {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K) {x : V}
    (h : Formalism.HermitianLatticesTheory.majAt b X v x x = 0) (y : V) : Formalism.HermitianLatticesTheory.majAt b X v x y = 0 := by
  unfold Formalism.HermitianLatticesTheory.majAt at h ⊢
  have hz : ∀ i, Formalism.HermitianLatticesTheory.fcoord b X v x i = 0 := by
    have h1 : ∀ i, star (Formalism.HermitianLatticesTheory.fcoord b X v x i) * Formalism.HermitianLatticesTheory.fcoord b X v x i =
        ((Complex.normSq (Formalism.HermitianLatticesTheory.fcoord b X v x i) : ℝ) : ℂ) := fun i => by
      rw [mul_comm]; exact Complex.mul_conj _
    simp only [h1] at h
    have h2 : ∑ i, Complex.normSq (Formalism.HermitianLatticesTheory.fcoord b X v x i) = 0 := by exact_mod_cast h
    intro i
    have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => Complex.normSq_nonneg _).1 h2 i (Finset.mem_univ _)
    exact Complex.normSq_eq_zero.1 this
  simp [hz]

theorem partPr_of_bot {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} (Df : DefSide Bs) (t : Bs.Tup) (p : Bs.Ix)
    (h : Df.Qp t p = ⊥) : partPr Df t p = 0 := by
  unfold partPr
  split_ifs with hc
  · have hz : ∀ z ∈ Df.Qp t p, z = 0 := fun z hz => by
      rw [h] at hz
      exact (Submodule.mem_bot K).1 hz
    ext i j
    rw [LinearMap.toMatrix'_apply, LinearMap.comp_apply, Submodule.subtype_apply, hz _ (Submodule.coe_mem _)]
    rfl
  · rfl

theorem rowXE_congr {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} (Df : DefSide Bs)
    (Y : Matrix (Fin (Df.dQ Bs.μ0)) (Fin (Df.dQ Bs.μ0)) ℂ) (κ : InfinitePlace K → ℝ) (lam lam' : Bs.J → Bs.Ix → InfinitePlace K → ℝ)
    (h : ∀ p, partPr Df Bs.μ0 p ≠ 0 → ∀ j v, lam j p v = lam' j p v) : rowXE Df Y κ lam = rowXE Df Y κ lam' := by
  have hw : weightMet (partPr Df Bs.μ0) (fun p v => κ v * ∏ j, lam j p v) (Df.XQ Bs.μ0) =
      weightMet (partPr Df Bs.μ0) (fun p v => κ v * ∏ j, lam' j p v) (Df.XQ Bs.μ0) := by
    funext v
    unfold weightMet
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases hp : partPr Df Bs.μ0 p = 0
    · rw [hp]
      simp [restrMetC]
    · simp only [h p hp]
  unfold rowXE rowFrame weightFrame
  rw [hw]

end Gen

section GenCx2
variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs} {fc : DefSub A → DefFace Bs}

theorem cx_XE_scal (Y : CxData A) (cr : Crd A fc) (lam : type_of% Y.lam) (b : Bool)
    (h : ∀ p, partPr (lv (fc Y.zs) b) Bs.μ0 p ≠ 0 → ∀ j v, lam j Bs.μ0 p v = Y.lam j Bs.μ0 p v) :
    ((reScal Y Y.κ lam).data cr b).XE = (Y.data cr b).XE :=
  rowXE_congr _ _ _ _ _ h

theorem cx_galD_scal (Y : CxData A) (cr : Crd A fc) (κ : InfinitePlace K → ℝ) (lam : type_of% Y.lam)
    (hlam : ∀ j p v, v ≠ Bs.v0 → (∃ x, Y.tC cr false j Bs.μ0 (cpt Bs.v0.embedding x) ∈ Y.Wp j p ∧
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) ((lv (fc Y.zs) false).XT j Bs.μ0) v x x ≠ 0) → lam j Bs.μ0 p v = Y.lam j Bs.μ0 p v)
    (h : Y.GalD cr false) : (reScal Y κ lam).GalD cr false := by
  intro j v hv p x hx y
  have h0 := h j v hv p x hx y
  refine h0.trans ?_
  show _ = ((lam j Bs.μ0 p v : ℝ) : ℂ) * Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) ((lv (fc Y.zs) false).XT j Bs.μ0) v x y
  by_cases hp : ∃ x, Y.tC cr false j Bs.μ0 (cpt Bs.v0.embedding x) ∈ Y.Wp j p ∧
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) ((lv (fc Y.zs) false).XT j Bs.μ0) v x x ≠ 0
  · rw [hlam j p v hv hp]
  · have hxx : Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) ((lv (fc Y.zs) false).XT j Bs.μ0) v x x = 0 := by
      by_contra hne
      exact hp ⟨x, hx, hne⟩
    rw [majAt_eq_zero_of_self _ _ v hxx y, mul_zero, mul_zero]

end GenCx2

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

open Classical in

def zeroLam (R : RealDat3 D A3 Ks) (F : Face3 D A3) (c : Fin D.R.m → ℝ) : type_of% R.lam3 :=
  fun i t p v => if (v = A3.A.v0 ∧ R.Wp3 i p = ⊥) ∨ (v ≠ A3.A.v0 ∧ ¬ R.PartAt F i p v) then Real.exp (c i) else R.lam3 i t p v

theorem zeroLam_of_ne (R : RealDat3 D A3 Ks) (F : Face3 D A3) (c : Fin D.R.m → ℝ) {i t p v}
    (h1 : R.Wp3 i p ≠ ⊥) (h2 : v ≠ A3.A.v0 → R.PartAt F i p v) : zeroLam R F c i t p v = R.lam3 i t p v := by
  unfold zeroLam
  rw [if_neg]
  rintro (⟨_, h⟩ | ⟨hv, h⟩)
  · exact h1 h
  · exact h (h2 hv)

theorem scalarsZeroPartConvention_fixedPlace (R : RealDat3 D A3 Ks) (F : Face3 D A3) (c : Fin D.R.m → ℝ) {i t p}
    (h1 : R.Wp3 i p ≠ ⊥) : zeroLam R F c i t p A3.A.v0 = R.lam3 i t p A3.A.v0 :=
  zeroLam_of_ne R F c h1 fun h => absurd rfl h

theorem zeroLam_off (R : RealDat3 D A3 Ks) (F : Face3 D A3) (c : Fin D.R.m → ℝ) {i t p v}
    (hv : v ≠ A3.A.v0) (h2 : R.PartAt F i p v) : zeroLam R F c i t p v = R.lam3 i t p v := by
  unfold zeroLam
  rw [if_neg]
  rintro (⟨h, _⟩ | ⟨_, h⟩)
  · exact hv h
  · exact h h2

theorem zeroLam_of_zero (R : RealDat3 D A3 Ks) (F : Face3 D A3) (c : Fin D.R.m → ℝ) {i t p v}
    (h : (v = A3.A.v0 ∧ R.Wp3 i p = ⊥) ∨ (v ≠ A3.A.v0 ∧ ¬ R.PartAt F i p v)) : zeroLam R F c i t p v = Real.exp (c i) := by
  unfold zeroLam
  rw [if_pos h]

theorem zeroLam_pos (R : RealDat3 D A3 Ks) (F : Face3 D A3) (c : Fin D.R.m → ℝ) (h : ∀ i t p v, 0 < R.lam3 i t p v) (i t p v) :
    0 < zeroLam R F c i t p v := by
  unfold zeroLam
  split_ifs
  · exact Real.exp_pos _
  · exact h i t p v

set_option maxHeartbeats 4000000 in

theorem qp_bot (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hC : R.WeakCharacterisation F) (hP : PrimRows3 R F) (hOk : A3.fam3.Ok3 1)
    (hsep : A3.fam3.TypesSep3) {p : A3.fam3.base3.Ix} (hp : R.EEp3 p = ⊥) (b : Bool) :
    (lv (F.fc (R.toCx3 F).zs) b).Qp A3.fam3.base3.μ0 p = ⊥ := by
  have kR := RealDat3.kFormR_of (F := F) hC.base.models
  have hst := (subspaces_stable_in_block (complex_data_conditions_base_level_of_primitive_links hOk hsep hC hP)).1
  have hH := hP.hecke.1.choose_spec
  have key : ∀ ℓ y, y ∈ (A3.fam3.RI A3.fam3.F.μ0).part3 ℓ ((R.toCx3 F).Z A3.fam3.F.μ0) p.1 → y = 0 := by
    intro ℓ y hy
    have h1 := (part_iff_rows3 kR hst hOk hH p ℓ y).1 hy
    have h2 : (R.toCx3 F).Θ A3.fam3.F.μ0 ((R.toCx3 F).jR A3.fam3.F.μ0
        ((A3.fam3.F.R A3.fam3.F.μ0).toF ℓ ((R.toCx3 F).Z A3.fam3.F.μ0) y)) = 0 := by
      have h3 : Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H) ((R.toCx3 F).Θ A3.fam3.F.μ0 ((R.toCx3 F).jR A3.fam3.F.μ0
          ((A3.fam3.F.R A3.fam3.F.μ0).toF ℓ ((R.toCx3 F).Z A3.fam3.F.μ0) y))) ∈ R.EEp3 p := h1
      rw [hp] at h3
      have h5 := (Submodule.mem_bot ℂ).1 h3
      exact h5
    have h4 := CxData.theta_jR_inj (R.toCx3 F) kR _ _ (coordinates_mem_subspace ℓ _ y) h2
    exact BlockDat.toF_injective _ ℓ _ (h4.trans (map_zero _).symm)
  rw [eq_bot_iff]
  intro y hy
  rw [Submodule.mem_bot]
  cases b
  · exact key _ y hy
  · exact key _ y hy

end GlobalTheory.Mem.R3

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanBasisImageAdicCompletionEqTop
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem span_basis_image_adicCompletion_eq_top
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L))
    (f : v.adicCompletion K →+* v'.adicCompletion L) (hfc : Continuous f)
    (hf : ∀ x : K, f (algebraMap K _ x) = algebraMap L _ (algebraMap K L x)) :
    letI := f.toAlgebra; ∀ (n : ℕ) (b : Module.Basis (Fin n) K L),
      Submodule.span (v.adicCompletion K)
        (Set.range fun i => algebraMap L (v'.adicCompletion L) (b i)) = ⊤ := by
  letI := f.toAlgebra
  intro n b
  letI : NontriviallyNormedField (v.adicCompletion K) := Valued.toNontriviallyNormedField _ _
  set S := Submodule.span (v.adicCompletion K)
    (Set.range fun i => algebraMap L (v'.adicCompletion L) (b i)) with hS
  haveI : ContinuousSMul (v.adicCompletion K) (v'.adicCompletion L) := by
    constructor
    have : (fun p : v.adicCompletion K × v'.adicCompletion L => p.1 • p.2)
        = fun p => f p.1 * p.2 := by
      funext p; exact Algebra.smul_def _ _
    rw [this]
    exact (hfc.comp continuous_fst).mul continuous_snd
  haveI : FiniteDimensional (v.adicCompletion K) S :=
    FiniteDimensional.span_of_finite _ (Set.finite_range _)
  have hclosed : IsClosed (S : Set (v'.adicCompletion L)) := S.closed_of_finiteDimensional
  have hmem : ∀ z : L, algebraMap L (v'.adicCompletion L) z ∈ S := by
    intro z
    rw [← b.sum_repr z, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    have : algebraMap L (v'.adicCompletion L) (b.repr z i • b i)
        = (algebraMap K (v.adicCompletion K) (b.repr z i)) •
            algebraMap L (v'.adicCompletion L) (b i) := by
      rw [Algebra.smul_def, Algebra.smul_def, map_mul, RingHom.algebraMap_toAlgebra, hf]
    rw [this]
    exact S.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)
  have hdense := HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 L) L v'
  have hsub : Set.range (algebraMap L (v'.adicCompletion L)) ⊆ (S : Set _) := by
    rintro _ ⟨z, rfl⟩; exact hmem z
  have huniv : (S : Set (v'.adicCompletion L)) = Set.univ := by
    have := closure_minimal hsub hclosed
    rw [hdense.closure_range] at this
    exact Set.univ_subset_iff.mp this
  exact eq_top_iff.mpr fun x _ => by
    have : x ∈ (S : Set (v'.adicCompletion L)) := huniv ▸ Set.mem_univ x
    exact this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepZeroHermitianLevelUniformiserKillsValuesStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stepZeroHermitianLevel_uniformiser_kills_values_alt : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch : ℕ → Type} {chOf : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch i} (F : FormsTiedSym (I.rec7 l Z) u Ch chOf), I.StdF l Z u F → ∀ (L : ColLevel (I.rec7 l Z).R (I.rec7 l Z).host.F (I.rec7 l Z).host.E (I.rec7 l Z).sp (I.rec7 l Z).host.g ((I.rec7 l Z).mem u).C ((I.rec7 l Z).mem u).A ((I.rec7 l Z).clsLat u)), SameCar (rank_eq_first_level (I.rec7 l Z).R) L.Lb (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.Lb L.Uloc (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.Uloc L.U (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.U (fun c => (L.y c).1) (fun c => ((F.cls 0 (Nat.zero_le _) (Or.inl rfl)).y c).1) (fun c s => (L.stabI c s).1) (fun c s => ((F.cls 0 (Nat.zero_le _) (Or.inl rfl)).stabI c s).1) → ∃ L' : ColLevel (I.rec7 l Z).R (I.rec7 l Z).host.F (I.rec7 l Z).host.E (I.rec7 l Z).sp (I.rec7 l Z).host.g ((I.rec7 l Z).mem u).C ((I.rec7 l Z).mem u).A ((I.rec7 l Z).clsLat u), L'.Lb = L.Lb ∧ L'.Uloc = L.Uloc ∧ L'.U = L.U ∧ L'.y = L.y ∧ L'.stabI = L.stabI ∧ L'.splitG = L.splitG ∧ L'.frG = L.frG ∧ ∀ (w : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (h : ((((I.rec7 l Z).mem u).A.T : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ w.asIdeal) (a : intV (I.rec7 l Z).host.E w), (a : TensorProduct (I.rec7 l Z).host.F (I.rec7 l Z).host.E (w.adicCompletion (I.rec7 l Z).host.F)) = inclE (F := (I.rec7 l Z).host.F) (w.adicCompletion (I.rec7 l Z).host.F) ((F.atT.piU : 𝓞 (I.rec7 l Z).host.E) : (I.rec7 l Z).host.E) → ∀ m : L'.fM w h, a • m = 0 := by
  first | exact @GlobalTheory.Mem.Col2.LevTwist.stepZeroHermitianLevel_uniformiser_kills_values | exact GlobalTheory.Mem.Col2.LevTwist.stepZeroHermitianLevel_uniformiser_kills_values | (intros; apply GlobalTheory.Mem.Col2.LevTwist.stepZeroHermitianLevel_uniformiser_kills_values <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StrongApproximationUpperUnitriangularFiniteAdeleStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory Topology
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.strongApproximation_upperUnitriangular_finiteAdeles : PIW.ClassFinD.UnipApprox := by
  first | exact @GlobalTheory.UnipApproxGL.unipApprox | exact GlobalTheory.UnipApproxGL.unipApprox | (intros; apply GlobalTheory.UnipApproxGL.unipApprox <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaComparisonDataIndependentOfAlgebraicFormsStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_comparison_data_independent_of_algebraic_forms : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (nW : Fin D.R.m → ℕ) (FW : ∀ i, Arith.FormsL D.what₂.LL T.Q.c.F (Fin (nW i) → D.what₂.LL) (fun σ => (R.HW i σ).H) G) (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), ∃ O' : OMDat T.toCore (updFW R nW FW) i Tp tup, O'.c' = O.c' ∧ O'.lev = O.lev ∧ (O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) T.σ₀) → O'.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) T.σ₀)) ∧ ∀ (cc : (T.U ((i : ℕ) + 1) T.σ₀).Comp → ℂ) (ph : ℂ), O.OneMapOf (κ i) (v₀ i (sg0 D A)) cc ph → O'.OneMapOf (κ i) (v₀ i (sg0 D A)) cc ph := by
  first | exact @GlobalTheory.RealGeo.omDat_updFW | exact GlobalTheory.RealGeo.omDat_updFW | (intros; apply GlobalTheory.RealGeo.omDat_updFW <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopDegreeFormCoeffEqTensorSquareTopCoefficientStatement
section
open MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topDegreeFormCoeff_eq_tensorSquareTopCoefficient : ∀ (n : ℕ) (P : MvPolynomial (Fin n × Fin n) ℂ), GlobalTheory.GoodMetric.topCoeff P = GlobalTheory.GrassModel.topBig n (GlobalTheory.GrassModel.toEven n P : GlobalTheory.GrassModel.Big n) := by
  first | exact @GlobalTheory.GrassModel.TopRead.topCoeff_eq_topBig | exact GlobalTheory.GrassModel.TopRead.topCoeff_eq_topBig | (intros; apply GlobalTheory.GrassModel.TopRead.topCoeff_eq_topBig <;> assumption)
end

