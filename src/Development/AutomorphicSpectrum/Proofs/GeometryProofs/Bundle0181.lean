import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.IsQProjOverOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0027
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0175
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.FramedPointSpecialization
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0018
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0109
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0101
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PlaceEqOneOfNotMem
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0034
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0179
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0042
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0030
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0031
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0177
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0009
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0176
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0106
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0005
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0075
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0125
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0038
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0009
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsResolutionGenericFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.GenRes

theorem genericFibre_closed {O K : Type} [CommRing O] [Field K] (β : O →+* K)
    (hinj : Function.Injective β) (hfr : ∀ x : K, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a)
    (P : Scheme.{0}) (s : P ⟶ Sp O) (hs : IsProjOver s) (hn : IsNormalScheme P) :
    IsReduced (pullback s (spMap β)) ∧ IsLocallyNoetherian (pullback s (spMap β)) ∧
      ∃ (M : ℕ) (i : pullback s (spMap β) ⟶ PSpace K M), IsClosedImmersion i ∧
        i ≫ PSpace.str K M = pullback.snd s (spMap β) := by
  letI : Algebra O K := β.toAlgebra
  haveI : IsDomain O := hinj.isDomain β
  haveI : IsFractionRing O K :=
    { map_units := fun y => by
        have hy : β y.1 ≠ 0 := fun h => nonZeroDivisors.ne_zero y.2 (hinj (by rw [h, map_zero]))
        exact (IsUnit.mk0 _ hy)
      surj := fun z => by
        obtain ⟨a, b, hb, h⟩ := hfr z
        have hb0 : b ≠ 0 := fun h0 => hb (by rw [h0, map_zero])
        exact ⟨⟨a, ⟨b, mem_nonZeroDivisors_of_ne_zero hb0⟩⟩, h⟩
      exists_of_eq := fun {x y} h => ⟨1, by rw [hinj h]⟩ }
  have hp : IsProjOver (pullback.snd s (spMap β)) := GlobalTheory.ProjSpace.isProjOver_pullback_snd _ hs
  have hb : IsPreimmersion (spMap β) :=
    IsPreimmersion.of_isLocalization (R := CommRingCat.of O) (S := K) (nonZeroDivisors O)
  have hbf : Flat (spMap β) := by
    rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat K (nonZeroDivisors O))
  have h1 : IsPreimmersion (pullback.fst s (spMap β)) :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) (IsPullback.of_hasPullback _ _).flip hb
  have hiso := GlobalTheory.isIso_stalkMap_of_flat_of_surjectiveOnStalks (pullback.fst s (spMap β))
  have := GlobalTheory.SchemeWords.isProper_of_isProjOver hp
  refine ⟨?_, LocallyOfFiniteType.isLocallyNoetherian (pullback.snd s (spMap β)), hp⟩
  have : ∀ x, _root_.IsReduced ((pullback s (spMap β)).presheaf.stalk x) := fun x => by
    have := hiso x
    have i := (asIso ((pullback.fst s (spMap β)).stalkMap x)).commRingCatIsoToRingEquiv
    obtain ⟨_, _⟩ := hn (pullback.fst s (spMap β) x)
    exact isReduced_of_injective i.symm i.symm.injective
  exact isReduced_of_isReduced_stalk _

theorem isProper_of_closed {K : Type} [Field K] {M r : ℕ} {X X' : Scheme.{0}} (i : X ⟶ PSpace K M)
    [IsClosedImmersion i] (j : X' ⟶ pullback (PSpace.str K M) (PSpace.str K r)) [IsClosedImmersion j]
    (f : X' ⟶ X) (h : f ≫ i = j ≫ pullback.fst _ _) : IsProper f ∧ IsProper (f ≫ i ≫ PSpace.str K M) := by
  have := isProper_str K M
  have := isProper_str K r
  have hfst : IsProper (pullback.fst (PSpace.str K M) (PSpace.str K r)) :=
    MorphismProperty.of_isPullback (P := @IsProper) (IsPullback.of_hasPullback _ _).flip inferInstance
  have hfi : IsProper (f ≫ i) := by rw [h]; infer_instance
  have hf : IsProper f := IsProper.of_comp f i
  refine ⟨hf, ?_⟩
  rw [← Category.assoc]
  infer_instance

end GlobalTheory.CompanionTheory.Ar.Flat.GenRes

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_resolution_genericFibre : Geo.ResK.ResKStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), (Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → IsLocallyNoetherian (pullback Y.s (spMap β)) ∧ ∃ (X' : Scheme.{0}) (f : X' ⟶ pullback Y.s (spMap β)) (d : ℕ) (W' : X'.Opens) (jW : W'.toScheme ⟶ Xo.XF c), IsIso jW ∧ jW ≫ Y.jQ = W'.ι ≫ f ∧ IsProper f ∧ IsProper (f ≫ pullback.snd Y.s (spMap β)) ∧ SmoothOfRelativeDimension d (f ≫ pullback.snd Y.s (spMap β)) ∧ Geo.ResK.HasSncCoords (f ≫ pullback.snd Y.s (spMap β)) d (W' : Set X')ᶜ := by
  rintro hRes E _ _ _ H D l Xo c O _ β Y ⟨hinj, -, hfr⟩
  obtain ⟨hred, hln, M, i, hi, his⟩ := GenRes.genericFibre_closed β hinj hfr Y.X Y.s Y.proj Y.normal
  refine ⟨hln, ?_⟩
  have := Y.jQ_open
  let U : (pullback Y.s (spMap β)).Opens := Y.jQ.opensRange
  have hd : Dense (U : Set (pullback Y.s (spMap β) : Scheme.{0})) := by
    have : (U : Set (pullback Y.s (spMap β) : Scheme.{0})) = Set.range Y.jQ := Scheme.Hom.coe_opensRange _
    rw [this]; exact Y.jQ_dense
  have hιe : Y.jQ.isoOpensRange.inv ≫ Y.jQ = U.ι := by
    rw [Iso.inv_comp_eq, Scheme.Hom.isoOpensRange_hom_ι]
  have hXF : SmoothOfRelativeDimension D.dim
      (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) := by
    have := Xo.smooth
    have := smoothOfRelativeDimension_isStableUnderBaseChange D.dim
    exact MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension D.dim)
      (IsPullback.of_hasPullback _ _) Xo.smooth
  have hU : SmoothOfRelativeDimension D.dim (U.ι ≫ pullback.snd Y.s (spMap β)) := by
    rw [← hιe, Category.assoc, Y.jQ_over]
    have := smoothOfRelativeDimension_isStableUnderBaseChange D.dim
    exact MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension D.dim)
      (IsPullback.of_horiz_isIso ⟨by simp⟩ :
        IsPullback Y.jQ.isoOpensRange.inv (Y.jQ.isoOpensRange.inv ≫ pullback.snd _ _) (pullback.snd _ _) (𝟙 _)) hXF
  have hin : Geo.ResK.IsResInput M i U D.dim := ⟨hi, hred, hd, by rw [his]; exact hU⟩
  haveI : CharZero c.F := inferInstance
  obtain ⟨r, X', j, f, hj, hfj, hsm, hiso, hdense, hsnc⟩ := hRes c.F M D.dim _ i U hin
  obtain ⟨hp1, hp2⟩ := GenRes.isProper_of_closed i j f hfj
  rw [his] at hp2 hsm hsnc
  refine ⟨X', f, D.dim, f ⁻¹ᵁ U, (f ∣_ U) ≫ Y.jQ.isoOpensRange.inv, inferInstance, ?_, hp1, hp2, hsm, hsnc⟩
  rw [Category.assoc, hιe, morphismRestrict_ι]

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameAtComponentPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_at_component_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (σ : c.F →+* ℂ) (b₁ : Fin D.p → Z.V) (b₂ : Fin D.q → Z.V) (p₀ : Cpt (Z.ξ₀ ≫ Y.j)), (Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → τ (H.rt : E) = H.rt0 → LinearIndependent Z.Ω b₁ → Submodule.span Z.Ω (Set.range b₁) = eigSp Z.ρ (Z.inc.comp (tauIn c τ)) → LinearIndependent Z.Ω b₂ → Submodule.span Z.Ω (Set.range b₂) = eigSp Z.ρ (Z.inc.comp (tauIn c (ComplexEmbedding.conjugate τ))) → p₀ ∈ Z.genFib → ∃ (A : Y.X.Opens) (hA : IsAffineOpen A) (EB : Type) (_ : AddCommGroup EB) (_ : Module Γ(Y.X, A) EB) (MB : LieModel Y.t.G hA.fromSpec EB) (e₁ : Fin D.p → EB) (e₂ : Fin D.q → EB) (v₁ : Fin D.p → Z.V) (v₂ : Fin D.q → Z.V), p₀.1 ∈ A ∧ (∀ q : Cpt (Z.ξ₀ ≫ Y.j), q.1 ∈ A → (Z.eig τ).IsFrameAt v₁ q ∧ (Z.eig (ComplexEmbedding.conjugate τ)).IsFrameAt v₂ q) ∧ (∀ (f : Γ(Y.X, A) →+* ℂ) (y : Sp ℂ ⟶ Y.X) (v : Fin D.p → (epsAt y ⟶ Y.t.G)) (w : Fin D.q → (epsAt y ⟶ Y.t.G)), y = spMap f ≫ hA.fromSpec → y ≫ Y.s = spMap (σ.comp β) → (∀ i, (v i).left = spMap (dualMap f) ≫ (MB.pt (e₁ i)).left) → (∀ j, (w j).left = spMap (dualMap f) ≫ (MB.pt (e₂ j)).left) → IsEigFrame Y.t.act y (σ.comp (tauIn c τ)) v ∧ IsEigFrame Y.t.act y (σ.comp (tauIn c (ComplexEmbedding.conjugate τ))) w) ∧ (∀ (f : Γ(Y.X, A) →+* ℂ) (y : Sp ℂ ⟶ Y.X) (v : Fin D.p → (epsAt y ⟶ Y.t.G)) (w : Fin D.q → (epsAt y ⟶ Y.t.G)), y = spMap f ≫ hA.fromSpec → genPt (Z.ξ₀ ≫ Y.j) ⤳ centre y → (∀ i, (v i).left = spMap (dualMap f) ≫ (MB.pt (e₁ i)).left) → (∀ j, (w j).left = spMap (dualMap f) ≫ (MB.pt (e₂ j)).left) → (∀ i, Z.M.ValAt y (v₁ i) (v i)) ∧ ∀ j, Z.M.ValAt y (v₂ j) (w j)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.LocalFrames.exists_affine_eigenframes | exact GlobalTheory.CompanionTheory.Ar.Flat.LocalFrames.exists_affine_eigenframes | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.LocalFrames.exists_affine_eigenframes <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FramedPointDescends
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

theorem GlobalTheory.CompanionTheory.Ar.Flat.exists_framed_residue : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (F : Type) [Field F] (β : c.F →+* F) (y : Sp F ⟶ Xo.XF c) (v : Vecs y D.p) (w : Vecs y D.q), IsFramed U τ β y v w → ∃ (k : Type) (_ : Field k) (β₀ : c.F →+* k) (y₀ : Sp k ⟶ Xo.XF c) (v₀ : Vecs y₀ D.p) (w₀ : Vecs y₀ D.q) (f : k →+* F) (j : k →+* ℂ), IsFramed U τ β₀ y₀ v₀ w₀ ∧ f.comp β₀ = β ∧ j.comp β₀ = algebraMap c.F ℂ ∧ y = spMap f ≫ y₀ ∧ ∀ (F' : Type) [Field F'] (f' : k →+* F'), ∃ (v' : Vecs (spMap f' ≫ y₀) D.p) (w' : Vecs (spMap f' ≫ y₀) D.q), IsFramed U τ (f'.comp β₀) (spMap f' ≫ y₀) v' w' ∧ (∀ a, (v' a).left = spMap (dualMap f') ≫ (v₀ a).left) ∧ ∀ b, (w' b).left = spMap (dualMap f') ≫ (w₀ b).left :=
  PositivityTheory.Xgn.framed_point_specialization
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericFibreProjectiveEmbedding
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

namespace GlobalTheory.CompanionTheory.Ar.SncBase

theorem genericFibre_reduced_noetherian_closed : ∀ (F : Type) [Field F] [NumberField F] (P : Scheme.{0}) (s : P ⟶ Sp (𝓞 F)), IsProjOver s → Tor.IsNormalScheme P → IsReduced (pullback s (spMap (algebraMap (𝓞 F) F))) ∧ IsLocallyNoetherian (pullback s (spMap (algebraMap (𝓞 F) F))) ∧ ∃ (M : ℕ) (i : pullback s (spMap (algebraMap (𝓞 F) F)) ⟶ PSpace F M), IsClosedImmersion i ∧ i ≫ PSpace.str F M = pullback.snd _ _ := by
  intro F _ _ P s hs hn
  have hp : IsProjOver (pullback.snd s (spMap (algebraMap (𝓞 F) F))) :=
    GlobalTheory.ProjSpace.isProjOver_pullback_snd _ hs
  have hb : IsPreimmersion (spMap (algebraMap (𝓞 F) F)) :=
    IsPreimmersion.of_isLocalization (R := CommRingCat.of (𝓞 F)) (S := F) (nonZeroDivisors (𝓞 F))
  have hbf : Flat (spMap (algebraMap (𝓞 F) F)) := by
    rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat F (nonZeroDivisors (𝓞 F)))
  have h1 : IsPreimmersion (pullback.fst s (spMap (algebraMap (𝓞 F) F))) :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) (IsPullback.of_hasPullback _ _).flip hb
  have hiso := GlobalTheory.isIso_stalkMap_of_flat_of_surjectiveOnStalks (pullback.fst s (spMap (algebraMap (𝓞 F) F)))
  have := GlobalTheory.SchemeWords.isProper_of_isProjOver hp
  refine ⟨?_, LocallyOfFiniteType.isLocallyNoetherian (pullback.snd s (spMap (algebraMap (𝓞 F) F))), hp⟩
  have : ∀ x, _root_.IsReduced ((pullback s (spMap (algebraMap (𝓞 F) F))).presheaf.stalk x) := fun x => by
    have := hiso x
    have i := (asIso ((pullback.fst s (spMap (algebraMap (𝓞 F) F))).stalkMap x)).commRingCatIsoToRingEquiv
    obtain ⟨_, _⟩ := hn (pullback.fst s (spMap (algebraMap (𝓞 F) F)) x)
    exact isReduced_of_injective i.symm i.symm.injective
  exact isReduced_of_isReduced_stalk _

end GlobalTheory.CompanionTheory.Ar.SncBase
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GluedLatticeFromLocalMatrices
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.PtHt
open GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame

namespace GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame

variable {L : Type} [Field L] [NumberField L]

theorem gIdx_eq_locAt {W : Type} [AddCommGroup W] [Module (𝓞 L) W] (v : FinitePlace L) (A B : Submodule (𝓞 L) W)
    (h1 : A.toAddSubgroup.relIndex B.toAddSubgroup ≠ 0) (h2 : B.toAddSubgroup.relIndex A.toAddSubgroup ≠ 0)
    (h : ∀ w : FinitePlace L, w ≠ v → locAt w A = locAt w B) :
    gIdx A.toAddSubgroup B.toAddSubgroup = gIdx (locAt v A).toAddSubgroup (locAt v B).toAddSubgroup := by
  have eA : ∀ X Y : Submodule (𝓞 L) W, (X ⊓ Y).toAddSubgroup.relIndex X.toAddSubgroup =
      Y.toAddSubgroup.relIndex X.toAddSubgroup := fun X Y => by
    have : (X ⊓ Y).toAddSubgroup = Y.toAddSubgroup ⊓ X.toAddSubgroup := by
      ext x; simp [and_comm]
    rw [this, AddSubgroup.inf_relIndex_right]
  have hA : ∀ w : FinitePlace L, w ≠ v → locAt w A = locAt w (A ⊓ B) := fun w hw => by
    rw [locAt_inf, ← h w hw, inf_idem]
  have hB : ∀ w : FinitePlace L, w ≠ v → locAt w B = locAt w (B ⊓ A) := fun w hw => by
    rw [locAt_inf, h w hw, inf_idem]
  have n1 := GlobalTheory.T.local_index_at_single_place L W v A (A ⊓ B) inf_le_left (by rwa [eA]) hA
  have n2 := GlobalTheory.T.local_index_at_single_place L W v B (B ⊓ A) inf_le_left (by rwa [eA]) hB
  rw [eA, locAt_inf, eA] at n1
  rw [eA, locAt_inf, eA] at n2
  rw [gIdx, gIdx, n1, n2]

variable {n : ℕ}

theorem gIdx_glued (S : Finset (FinitePlace L)) : ∀ T : FinitePlace L → Matrix (Fin n) (Fin n) L,
    (∀ v, (T v).det ≠ 0) → (∀ v, v ∉ S → UnitAt v (T v)) →
    gIdx (glued T).toAddSubgroup (frame (1 : Matrix (Fin n) (Fin n) L)).toAddSubgroup =
      ∑ v ∈ S, Real.log (v (T v).det) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro T _ hS
    have : glued T = frame 1 := by
      rw [glued, ← iInf_locAt_frame_one]
      exact iInf_congr fun v => (hS v (by simp)).locAt_frame
    rw [this, gIdx_self, Finset.sum_empty]
  | insert v S hv ih =>
    intro T hd hS
    set T' := Function.update T v 1 with hT'
    have hTv : T' v = 1 := by simp [hT']
    have hTw : ∀ w, w ≠ v → T' w = T w := fun w hw => by simp [hT', hw]
    have hd' : ∀ w, (T' w).det ≠ 0 := fun w => by
      by_cases hw : w = v
      · subst hw; rw [hTv]; simp
      · rw [hTw w hw]; exact hd w
    have hS' : ∀ w, w ∉ S → UnitAt w (T' w) := fun w hw => by
      by_cases hwv : w = v
      · subst hwv; rw [hTv]; exact unitAt_one _
      · rw [hTw w hwv]; exact hS w (by simp [hwv, hw])
    have f1 : {w : FinitePlace L | ¬ UnitAt w (T w)}.Finite :=
      (Finset.finite_toSet (insert v S)).subset fun w hw => by
        by_contra h
        exact hw (hS w h)
    have f2 : {w : FinitePlace L | ¬ UnitAt w (T' w)}.Finite :=
      S.finite_toSet.subset fun w hw => by
        by_contra h
        exact hw (hS' w h)
    obtain ⟨a1, a2⟩ := GlobalTheory.T.glued_lattice_finite_index L n T hd f1
    obtain ⟨b1, b2⟩ := GlobalTheory.T.glued_lattice_finite_index L n T' hd' f2
    have c1 := AddSubgroup.relIndex_ne_zero_trans a1 b2
    have c2 := AddSubgroup.relIndex_ne_zero_trans b1 a2
    have loc : ∀ w : FinitePlace L, w ≠ v → locAt w (glued T) = locAt w (glued T') := fun w hw => by
      rw [GlobalTheory.T.glued_lattice_localization L n T hd f1, GlobalTheory.T.glued_lattice_localization L n T' hd' f2, hTw w hw]
    rw [gIdx_add c1 c2 b1 b2, gIdx_eq_locAt v _ _ c1 c2 loc, GlobalTheory.T.glued_lattice_localization L n T hd f1, GlobalTheory.T.glued_lattice_localization L n T' hd' f2,
      hTv, GlobalTheory.T.local_index_frame_log_det L n v (T v) (hd v), ih T' hd' hS', Finset.sum_insert hv]
    refine congrArg _ (Finset.sum_congr rfl fun w hw => ?_)
    rw [hTw w fun e => hv (e ▸ hw)]

end GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame

namespace GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame

theorem logIdx_localFrames : ∀ (L : Type) [Field L] [NumberField L] (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (n : ℕ) (g : Fin n → V) (F : Submodule (𝓞 L) V) (T : FinitePlace L → Matrix (Fin n) (Fin n) L) (C : Matrix (Fin n) (Fin n) L), LinearIndependent L g → (∀ v, (T v).det ≠ 0) → C.det ≠ 0 → {v : FinitePlace L | ¬ ((∀ i j, v (T v i j) ≤ 1) ∧ v (T v).det = 1)}.Finite → (∀ x, x ∈ F ↔ x ∈ Submodule.span L (Set.range g) ∧ ∀ v : FinitePlace L, ∃ t : 𝓞 L, t ∉ v.maximalIdeal.asIdeal ∧ t • x ∈ Submodule.span (𝓞 L) (Set.range fun k => ∑ j, T v j k • g j)) → logIdx F (fun k => ∑ j, C j k • g j) = (∑ᶠ v : FinitePlace L, Real.log (v (T v).det)) + ∑ σ : L →+* ℂ, Real.log ‖σ C.det‖ := by
  intro L _ _ V _ _ _ _ n g F T C hg hd hC hfin hF
  classical

  let Φ : (Fin n → L) →ₗ[𝓞 L] V := (Fintype.linearCombination L g).restrictScalars (𝓞 L)
  have hΦ : Function.Injective Φ := hg.fintypeLinearCombination_injective
  have hΦa : ∀ c, Φ c = ∑ i, c i • g i := fun c => by
    simp [Φ, Fintype.linearCombination_apply]
  have hfr : ∀ A : Matrix (Fin n) (Fin n) L, (frame A).map Φ =
      Submodule.span (𝓞 L) (Set.range fun k => ∑ j, A j k • g j) := fun A => by
    rw [frame, Submodule.map_span, ← Set.range_comp]
    congr 2
  have hFg : F = (glued T).map Φ := by
    ext x
    rw [hF x, Submodule.mem_map]
    constructor
    · rintro ⟨hx, hl⟩
      have hr : x ∈ Set.range (Fintype.linearCombination L g) := by
        rw [← Fintype.range_linearCombination] at hx
        exact hx
      obtain ⟨c, rfl⟩ := hr
      refine ⟨c, ?_, rfl⟩
      rw [glued, Submodule.mem_iInf]
      intro v
      obtain ⟨t, ht, h⟩ := hl v
      rw [← hfr, Submodule.mem_map] at h
      obtain ⟨y, hy, e⟩ := h
      refine mem_locAt.2 ⟨t, ht, ?_⟩
      have : t • c = y := hΦ (by rw [map_smul, e]; rfl)
      rwa [this]
    · rintro ⟨c, hc, rfl⟩
      refine ⟨?_, fun v => ?_⟩
      · rw [← Fintype.range_linearCombination]
        exact ⟨c, rfl⟩
      · obtain ⟨t, ht, h⟩ := mem_locAt.1 ((Submodule.mem_iInf _).1 hc v)
        refine ⟨t, ht, ?_⟩
        rw [← hfr, ← map_smul]
        exact Submodule.mem_map_of_mem h
  have hidx : logIdx F (fun k => ∑ j, C j k • g j) = gIdx (glued T).toAddSubgroup (frame C).toAddSubgroup := by
    have e : logIdx F (fun k => ∑ j, C j k • g j) = gIdx F.toAddSubgroup ((frame C).map Φ).toAddSubgroup := by
      rw [hfr]; rfl
    rw [e, hFg, Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup]
    exact gIdx_map _ hΦ _ _
  obtain ⟨g1, g2, g3⟩ := GlobalTheory.T.global_index_frame_log_norm L n C hC
  have hfin' : {v : FinitePlace L | ¬ UnitAt v (T v)}.Finite := hfin
  obtain ⟨a1, a2⟩ := GlobalTheory.T.glued_lattice_finite_index L n T hd hfin'
  rw [hidx, gIdx_add a1 a2 g1 g2, g3, gIdx_glued hfin'.toFinset T hd fun v hv => by
    by_contra h
    exact hv (hfin'.mem_toFinset.2 h)]
  congr 1
  rw [finsum_eq_sum_of_support_subset]
  intro v hv
  rw [Set.Finite.coe_toFinset]
  intro h
  exact hv (show Real.log (v (T v).det) = 0 by rw [h.2, Real.log_one])

end GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompComparisonLeftStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_comp_comparison_left : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S₀ S : Finset ℕ) (Ω₁ Ω : Type) [Field Ω₁] [Field Ω] (K₁ : Type) [Fintype K₁] (J₁ : K₁ → Type) [∀ k, Fintype (J₁ k)] (y₁ : (Σ k, J₁ k) → Ω₁) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (A : HodgeCpt Y S₀ y₁) (B : HodgeCpt Y S y) (i : Ω₁ →+* Ω) (h : B.X ⟶ A.X), GlobalTheory.CompanionTheory.Ar.Dominates B.ξ A.ξ h i → B.f = h ≫ A.f → ∃ jA : A.Li →+ B.Li, IsExtOver i jA ∧ (∀ e, (B.M.pt (jA e)).left ≫ B.m.φ = spMap (dualMap i) ≫ (A.M.pt e).left ≫ A.m.φ) ∧ (∀ a e, jA (A.ρ a e) = B.ρ a (jA e)) ∧ B.M.lat = A.M.lat.pull B.ξ h jA := by
  first | exact @GlobalTheory.CompanionTheory.Ar.CoverLie.main | exact GlobalTheory.CompanionTheory.Ar.CoverLie.main | (intros; apply GlobalTheory.CompanionTheory.Ar.CoverLie.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeComponentFiniteChartsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.QuotUnif Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_component_finite_charts : Geo.ResK.ResKStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y), ∃ (n nc : ℕ) (w : Fin nc → (Fin n → ℂ) → (Σ k, J k) → ℂ) (a : Fin nc → ℕ), (∀ i, a i ≤ n) ∧ (∀ i, AnalyticOnNhd ℂ (w i) (ball 0 1)) ∧ (∀ i, ∀ t ∈ ball (0 : Fin n → ℂ) 1, w i t ∈ mcPts (mCoordIdeal y)) ∧ (∀ i, ∀ t ∈ ball (0 : Fin n → ℂ) 1, (∀ j : Fin n, (j : ℕ) < a i → t j ≠ 0) → ∀ z : Sp ℂ ⟶ 𝔐.X, CoordsAt 𝔐.ξ y z (w i t) → 𝔐.Interior z) ∧ ∀ x ∈ mcPts (mCoordIdeal y), ∃ (i : Fin nc) (t : Fin n → ℂ) (b : K → ℂ), ‖t‖ ≤ 1 / 2 ∧ (∀ k, b k ≠ 0) ∧ x = GroundTheory.Heights₂.Heights.LowerBoundFree.torusSmul b (w i t) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.QuotUnif.Charts.exists_halfPolydisc_cover | exact GlobalTheory.CompanionTheory.Ar.QuotUnif.Charts.exists_halfPolydisc_cover | (intros; apply GlobalTheory.CompanionTheory.Ar.QuotUnif.Charts.exists_halfPolydisc_cover <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeComponentMatchesModelComponentStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_component_matches_model_component : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) [NumberField c.F] (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (U : Set (Xo.XF c)) (Z : CptOver Y U) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y), genPt 𝔐.ξ₀ = genPt (Z.ξ₀ ≫ Y.j) → ∃ (i : Z.Ω →+* Ω) (j : Z.V →+ 𝔐.Li), CptIn.IsTie Z 𝔐 i j := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.CptIn.exists_isTie | exact GlobalTheory.CompanionTheory.Ar.Flat.CptIn.exists_isTie | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.CptIn.exists_isTie <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeFormOfIsHodgeGram
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fl

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

theorem hodgeForm_of_isHodgeGram (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left) (x : Sp ℂ ⟶ S) (n : ℕ)
    (v : Fin n → (epsAt x ⟶ G)) (Γ : Matrix (Fin n) (Fin n) ℂ) (hL : L.IsLB) (hv : ∀ i, IsTanAt G x (v i))
    (h : Fl.IsHodgeGram G L x v Γ) (i j : Fin n) : HodgeForm G L x (v i) (v j) (Γ i j) := by
  obtain ⟨Q, ψ, v', u, Hm, χ, W, hp, hiso, hAH, hvW, hΓ⟩ := h
  have hM := pull_isLB hL ψ
  obtain ⟨w, hw⟩ := LBIso.symm hiso
  exact ⟨hL, hv i, hv j, Q.A, inferInstance, ψ, Q.g, GlobalTheory.TorsionTauCompare.transport Q.isLB hM hw u, Hm, χ, v' i, v' j,
    W i, W j, hp, GlobalTheory.TorsionTauCompare.isAH_transport Q.isLB hM hw u hAH, (hvW i).1, (hvW j).1, (hvW i).2, (hvW j).2,
    hΓ i j⟩

end GlobalTheory.CompanionTheory.Ar.Fl
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeGramComplexConjugate
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.GramConj

open GlobalTheory.ArchMetricCompare (cj cjPt cjUnif cj_isAH cj_val isIso_of_cj carry carry_isAH)

attribute [local instance] Over.cartesianMonoidalCategory

theorem dualConj_dualConj :
    spMap (dualMap (starRingEnd ℂ)) ≫ spMap (dualMap (starRingEnd ℂ)) = 𝟙 (Sp (DualNumber ℂ)) := by
  have h : (dualMap (starRingEnd ℂ)).comp (dualMap (starRingEnd ℂ)) = RingHom.id (DualNumber ℂ) := by
    ext c <;> simp [dualMap]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, h]
  exact Spec.map_id _

theorem fderiv_conj {g : ℕ} (F : (Fin g → ℂ) → ℂ) (w : Fin g → ℂ) :
    fderiv ℂ (star ∘ F ∘ star) 0 (star w) = star (fderiv ℂ F 0 w) := by
  by_cases h : DifferentiableAt ℂ F 0
  · have d := h.hasFDerivAt.star_star
    rw [star_zero] at d
    rw [d.fderiv]
    simp
  · have h' : ¬ DifferentiableAt ℂ (star ∘ F ∘ star) 0 := fun h' => h (by
      have := h'.star_star
      have e : star ∘ (star ∘ F ∘ star) ∘ star = F := by
        ext z
        simp
      rw [star_zero, e] at this
      exact this)
    rw [fderiv_zero_of_not_differentiableAt h, fderiv_zero_of_not_differentiableAt h']
    simp

variable {A A' : Over (Sp ℂ)} [GrpObj A] [GrpObj A'] {ψ : A'.left ⟶ A.left} {M : LB A.left} {M' : LB A'.left} {g : ℕ}

theorem isDiff_conj (h : IsGrpPullback A' A cj ψ) (u : HolUnif A M g) (u' : HolUnif A' M' g)
    (hex : ∀ z, u'.ex z = cjPt h (u.ex (star z))) {t : epsR ℂ ⟶ A} {t' : epsR ℂ ⟶ A'}
    (e : t'.left ≫ ψ = spMap (dualMap (starRingEnd ℂ)) ≫ t.left) {w : Fin g → ℂ} (hd : u.IsDiff w t) :
    u'.IsDiff (star w) t' := by
  haveI := isIso_of_cj h
  intro U hU f
  have e2 : t'.left = spMap (dualMap (starRingEnd ℂ)) ≫ (show Sp (DualNumber ℂ) ⟶ _ from t.left) ≫ inv ψ := by
    rw [← Category.assoc]
    exact (IsIso.eq_comp_inv ψ).2 e
  have e4 : (show Sp (DualNumber ℂ) ⟶ _ from t.left) ≫ inv ψ = spMap (dualMap (starRingEnd ℂ)) ≫ t'.left := by
    rw [e2, ← Category.assoc, dualConj_dualConj, Category.id_comp]
  have h2 : ⊤ ≤ t.left ⁻¹ᵁ (inv ψ ⁻¹ᵁ U) := fun p _ => by
    have q : ((show Sp (DualNumber ℂ) ⟶ _ from t.left) ≫ inv ψ) p ∈ U := by
      rw [e4]
      exact hU (show spMap (dualMap (starRingEnd ℂ)) p ∈ (⊤ : (Sp (DualNumber ℂ)).Opens) from trivial)
    exact q
  have e1 : (fun z => valAt' (u'.ex z).left U f) =
      star ∘ (fun z => valAt' (u.ex z).left (inv ψ ⁻¹ᵁ U) (((inv ψ).app U).hom f)) ∘ star :=
    funext fun z => by
      simp only [hex]
      exact cj_val h _ U f
  rw [e1, fderiv_conj]
  have k : ∀ (y : Sp (DualNumber ℂ) ⟶ A'.left) (hy : ⊤ ≤ y ⁻¹ᵁ U),
      y = spMap (dualMap (starRingEnd ℂ)) ≫ (show Sp (DualNumber ℂ) ⟶ _ from t.left) ≫ inv ψ →
      TangentOrigin.evalPt y U hy f = dualMap (starRingEnd ℂ)
        (TangentOrigin.evalPt (R := DualNumber ℂ) t.left _ h2 (((inv ψ).app U).hom f)) := by
    rintro _ hy rfl
    rw [TangentOrigin.evalPt_spMap_comp _ _ U h2]
    congr 1
  refine (congrArg TrivSqZeroExt.snd (k _ hU e2)).trans ?_
  have e3 := hd _ h2 (((inv ψ).app U).hom f)
  simp only [dualMap, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl,
    TrivSqZeroExt.snd_inr, zero_add]
  exact congrArg (starRingEnd ℂ) e3

theorem exists_conjUnif (h : IsGrpPullback A' A cj ψ) (hM : M.IsLB) (u : HolUnif A M g)
    {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ} (hA : u.IsAH Hm χ) :
    ∃ (u' : HolUnif A' (M.pull ψ) g) (χ' : u'.Λ → ℂ), u'.IsAH (Hm.map star) χ' ∧
      ∀ z, u'.ex z = cjPt h (u.ex (star z)) := by
  have hM1 : (M.pull (𝟙 A.left)).IsLB := pull_isLB hM _
  obtain ⟨w, hw⟩ : LBIso M (M.pull (𝟙 A.left)) :=
    LBIso.chartPull (chartPullId M) (chartPullPull M (𝟙 _) (𝟙 _) rfl) (PolBaseChange.lbIso_refl hM)
  have key : ∀ f, f = ψ ≫ 𝟙 A.left → ∃ (u' : HolUnif A' (M.pull f) g) (χ' : u'.Λ → ℂ),
      u'.IsAH (Hm.map star) χ' ∧ ∀ z, u'.ex z = cjPt h (u.ex (star z)) := by
    rintro _ rfl
    exact ⟨cjUnif h (carry u hM hM1 hw), _, cj_isAH h _ (carry_isAH hM hM1 hw hA), fun _ => rfl⟩
  exact key _ (Category.comp_id _).symm

theorem isHodgeGram_conj : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left) (x x' : Spec (CommRingCat.of ℂ) ⟶ S) (n : ℕ) (v : Fin n → (epsAt x ⟶ G)) (v' : Fin n → (epsAt x' ⟶ G)) (Γ : Matrix (Fin n) (Fin n) ℂ), x' = spMap (starRingEnd ℂ) ≫ x → (∀ i, (v' i).left = spMap (dualMap (starRingEnd ℂ)) ≫ (v i).left) → Fl.IsHodgeGram G L x v Γ → Fl.IsHodgeGram G L x' v' (Γ.map (starRingEnd ℂ)) := by
  rintro S G _ L x x' n v v' Γ rfl hv' ⟨Q, ψ, vo, u, Hm, χ, W, hP, hLB, hAH, hvo, hΓ⟩
  have hc := isGrpPullback_pullback Q.A cj
  haveI := (Out.TLinPf.isAb_pullback cj Q.A Q.isAb).comm
  obtain ⟨u', χ', hAH', hex⟩ := exists_conjUnif hc Q.isLB u hAH
  have sq : ∀ i, (spMap (dualMap (starRingEnd ℂ)) ≫ (vo i).left) ≫ Q.A.hom = (epsR ℂ).hom ≫ cj := fun i => by
    rw [Category.assoc, Over.w]
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  let t : ∀ i, epsR ℂ ⟶ (Over.pullback cj).obj Q.A := fun i => Over.homMk (hc.1.lift _ _ (sq i)) (hc.1.lift_snd _ _ _)
  have et : ∀ i, (t i).left ≫ pullback.fst Q.A.hom cj = spMap (dualMap (starRingEnd ℂ)) ≫ (vo i).left :=
    fun i => hc.1.lift_fst _ _ _
  refine ⟨GlobalTheory.TorsionTauCompare.polOfPullback Q _ hc, pullback.fst Q.A.hom cj ≫ ψ, t, u', Hm.map star, χ',
    fun i => star (W i), hc.comp hP, ?_, hAH', fun i => ⟨?_, isDiff_conj hc u u' hex (et i) (hvo i).2⟩, fun i j => ?_⟩
  · exact LBIso.symm (Cusp.FibreMove.lbIso_pull (LBIso.symm hLB) _)
  · exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ ψ) (et i))).trans
      (((Category.assoc _ _ _).trans (congrArg _ (hvo i).1)).trans (hv' i).symm)
  · rw [Matrix.map_apply, hΓ, map_mul, Complex.conj_ofReal]
    congr 1
    refine Eq.trans ?_ (GlobalTheory.ArchMetricCompare.star_form Hm (star (W i)) (star (W j)))
    rw [star_star (W i), star_star (W j)]
    rfl

end GlobalTheory.CompanionTheory.Ar.GramConj
end
end

