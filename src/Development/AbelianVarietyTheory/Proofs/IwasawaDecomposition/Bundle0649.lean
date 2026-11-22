import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0594
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalEquationComplexPoints
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0631
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineOpenChartCompStructureEqSpMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0626
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0629
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0617
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0632
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0619
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.UnifMetricScalar
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0009
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0020
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HasSumPolyDerivMulProdAddMatrix
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0015
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0638
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0607
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0036
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1565
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0014
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0622
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModuliModelUltrametricPoints
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0119
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0234
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.IsPrecompleteOfBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0633
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GrassmannCellCoordinatesExist
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0610

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalFlagCoordinates
section
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open scoped ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.FlagFrames

attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_frames_nhds : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (F : Type) [Field F] [NumberField F] (e : F ≃+* c.F) (Y : FlagCpt Z e) (σ : F →+* ℂ) (y : Y.Y.X), ∃ (U : Y.Y.X.Opens) (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Y.Y.Fnˣ) (V : (gen Z).affineOpens) (φ : c.F →+* Γ(gen Z, V.1)) (Fr : EigFrame Z φ (LogKS.chart V ≫ genι Z)) (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Γ(Y.Y.X, U)), y ∈ U ∧ LogKS.chart V ≫ genStr Z = spMap φ ∧ (∀ p : Y.Y.pts σ, p ∈ ptsIn Y.Y.str σ U → Y.down p ∈ ptsIn (genStr Z) (embOf e σ) V.1) ∧ (∀ y' ∈ U, ∀ τ i, (Y.gr τ i).IsEqn y' (t τ i)) ∧ ∀ (p : Y.Y.pts σ) (hp : p ∈ ptsIn Y.Y.str σ U), ∃ (hv : Y.down p ∈ ptsIn (genStr Z) (embOf e σ) V.1) (g f : Y.FrameAt p), Y.Adapted p t g 1 ∧ Fr.IsMap (evHom hv) f ∧ ∀ τ, f.co g τ = (A τ).map (evHom hp) := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ _ e Y σ y
  obtain ⟨V₀, hV₀, φ₀, Fr₀, hy₀, hs₀, -⟩ := EigSpread.exists_stable_eigFrame E H Dw l Xo c O β Z (Y.π y)
  obtain ⟨U, hU, hy, φ, fr, t, hle, hs, hT, ht⟩ := Spread.exists_frame_nhds E H Dw l Xo c O β Z F e Y y (Y.π ⁻¹ᵁ V₀) hy₀
  let ρ : Γ(gen Z, V₀) →+* Γ(Y.Y.X, U) := (Y.π.appLE V₀ U hle).hom
  have hρ : spMap ρ ≫ (show Sp Γ(gen Z, V₀) ⟶ gen Z from hV₀.fromSpec) =
      (show Sp Γ(Y.Y.X, U) ⟶ Y.Y.X from hU.fromSpec) ≫ Y.π := IsAffineOpen.SpecMap_appLE_fromSpec Y.π hV₀ hU hle

  have hφ : φ = ρ.comp φ₀ := EigLoc.spMap_inj (by
    rw [← hs, ← hρ, Category.assoc, hs₀]
    exact spMap_comp_spMap φ₀ ρ)
  have hxρ : ((show Sp Γ(Y.Y.X, U) ⟶ Y.Y.X from hU.fromSpec) ≫ Y.π) ≫ genι Z =
      spMap ρ ≫ (show Sp Γ(gen Z, V₀) ⟶ gen Z from hV₀.fromSpec) ≫ genι Z := by
    rw [← Category.assoc, hρ]
  obtain ⟨Fr', hFr'⟩ := Fr₀.exists_isMap ρ hφ hxρ
  have hdown : ∀ p : Y.Y.pts σ, p ∈ ptsIn Y.Y.str σ U → Y.down p ∈ ptsIn (genStr Z) (embOf e σ) V₀ := fun p hp =>
    CxPts.mem_ptsIn.2 (hle (CxPts.mem_ptsIn.1 hp))
  refine ⟨U, t, ⟨V₀, hV₀⟩, φ₀, Fr₀, fun τ => Fr'.co fr τ, hy, hs₀, hdown, ht, fun p hp => ⟨hdown p hp, ?_⟩⟩
  have hv := hdown p hp
  have hpU : spMap (evHom hp) ≫ (show Sp Γ(Y.Y.X, U) ⟶ Y.Y.X from hU.fromSpec) = p.1 :=
    Points.specMap_valMap_fromSpec hU p.1 hp
  have hpV : spMap (evHom hv) ≫ (show Sp Γ(gen Z, V₀) ⟶ gen Z from hV₀.fromSpec) = (Y.down p).1 :=
    Points.specMap_valMap_fromSpec hV₀ (Y.down p).1 hv
  have hov : (Y.down p).1 ≫ genStr Z = spMap (embOf e σ) := (Y.down p).2
  have hxg : (Y.down p).1 ≫ genι Z = spMap (evHom hp) ≫ ((show Sp Γ(Y.Y.X, U) ⟶ Y.Y.X from hU.fromSpec) ≫ Y.π) ≫ genι Z := by
    rw [← Category.assoc, ← Category.assoc, hpU]; rfl
  have hxf : (Y.down p).1 ≫ genι Z = spMap (evHom hv) ≫ (show Sp Γ(gen Z, V₀) ⟶ gen Z from hV₀.fromSpec) ≫ genι Z := by
    rw [← Category.assoc, hpV]
  have hφg : embOf e σ = (evHom hp).comp φ := EigLoc.spMap_inj (hov.symm.trans (by
    rw [← spMap_comp_spMap φ (evHom hp), ← hs, ← Category.assoc, ← Category.assoc, hpU]; rfl))
  have hφf : embOf e σ = (evHom hv).comp φ₀ := EigLoc.spMap_inj (hov.symm.trans (by
    rw [← spMap_comp_spMap φ₀ (evHom hv), ← hs₀, ← Category.assoc, hpV]))
  have hev : (evHom hp).comp ρ = evHom hv := EigLoc.spMap_inj ((cancel_mono
    (show Sp Γ(gen Z, V₀) ⟶ gen Z from hV₀.fromSpec)).1 (by
      rw [hpV, ← spMap_comp_spMap ρ (evHom hp), Category.assoc, hρ, ← Category.assoc, hpU]; rfl))
  obtain ⟨g, hg⟩ := fr.exists_isMap (evHom hp) hφg hxg
  obtain ⟨f, hf⟩ := Fr₀.exists_isMap (evHom hv) hφf hxf
  have hf' : Fr'.IsMap (evHom hp) f := fun τ i => by
    rw [hf τ i, hFr' τ i, GradedPieces.dual_comp, hev]
  refine ⟨g, f, ?_, hf, fun τ => EigFrame.IsMap.co τ hf' hg hxg⟩
  have hb : Var.base p ∈ U := CxPts.mem_ptsIn.1 hp
  let gm : Γ(Y.Y.X, U) →+* Y.Y.X.presheaf.stalk (Var.base p) := (Y.Y.X.presheaf.germ U (Var.base p) hb).hom
  have hxs : stalkPt Y.Y (Var.base p) ≫ Y.π ≫ genι Z =
      spMap gm ≫ ((show Sp Γ(Y.Y.X, U) ⟶ Y.Y.X from hU.fromSpec) ≫ Y.π) ≫ genι Z := by
    have h0 : stalkPt Y.Y (Var.base p) = spMap gm ≫ (show Sp Γ(Y.Y.X, U) ⟶ Y.Y.X from hU.fromSpec) :=
      (Spread.spMap_germ hU hb).symm
    rw [h0]; simp only [Category.assoc]
  obtain ⟨frs, hfrs⟩ := fr.exists_isMap gm rfl hxs
  have hgm : (Var.evStalk p).comp gm = evHom hp :=
    (congrArg CommRingCat.Hom.hom (HolFrames.valR_eq_germ p.1 U hp)).symm
  have hgs : frs.IsMap (Var.evStalk p) g := fun τ i => by
    rw [hg τ i, hfrs τ i, GradedPieces.dual_comp, hgm]
  have hxp : (Y.down p).1 ≫ genι Z = spMap (Var.evStalk p) ≫ stalkPt Y.Y (Var.base p) ≫ Y.π ≫ genι Z := by
    rw [← Category.assoc, Y.spMap_evStalk p]; rfl
  have hκ : (algebraMap (Y.Y.X.presheaf.stalk (Var.base p)) Y.Y.X.functionField).comp gm = fnOf U (gen_mem hy) :=
    RingHom.ext fun a => algebraMap_germ _ a
  have ha : frs.Tri (algebraMap _ Y.Y.X.functionField) Y.f0 t := by
    refine ⟨by rw [hT.1, hxs, ← hκ, ← spMap_comp_spMap gm, Category.assoc], by rw [hT.2.1, ← hκ]; rfl, fun τ i => ?_⟩
    have h3 := hT.2.2 τ i
    rw [← hκ] at h3
    simpa only [hfrs τ, GradedPieces.dual_comp] using h3
  have hφs : embOf e σ = (Var.evStalk p).comp (gm.comp φ) := by
    rw [hφg, ← hgm]; rfl
  exact (FlagCpt.adapted_of_tri (Y.spMap_evStalk p).symm ha (hgs.tri hφs hxp)).1

end GlobalTheory.ShFam.FlagFrames
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelOfAtlasStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_model_of_atlas : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p) (i : Idx H p) (X : Scheme.{0}) (π : X ⟶ (Y i).X) (ty : (E →+* ℂ) → Finset ℕ) (A : Atlas (Y i) π ty), i₀.l.Dvd i.l → i₀.c.F ≤ i.c.F → Geo (Y i) π → ∃ (Z' : Mdl Y i₀) (e : Z'.X ≅ X), Z'.i = i ∧ Z'.ty = ty ∧ (∀ (Z₁ : Mdl Y i₀) (g : Z₁.X ⟶ X), MapsTo Z₁ A g → MapsTo Z₁ (atlasOf Z') (g ≫ e.inv)) ∧ (∀ (X₂ : Scheme.{0}) (π₂ : X₂ ⟶ (Y i).X) (ty₂ : (E →+* ℂ) → Finset ℕ) (A₂ : Atlas (Y i) π₂ ty₂) (f : X ⟶ X₂), f ≫ π₂ = π → (∀ (K : Type) [Field K] (w : Sp K ⟶ X) (u : Vecs Dw (Y i).t K), A.FlagAt w u → A₂.FlagAt (w ≫ f) u) → MapsTo Z' A₂ (e.hom ≫ f)) ∧ ∀ σ k, IntStep A σ k → IntStep (atlasOf Z') σ k := by
  first | exact @GlobalTheory.DRFlag.exists_mdl_of_atlas | exact GlobalTheory.DRFlag.exists_mdl_of_atlas | (intros; apply GlobalTheory.DRFlag.exists_mdl_of_atlas <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPluckerFlagEmbeddingOfProjectiveBase
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.FlagEmb

theorem span_plk_uvec_eq_top {X : Scheme.{0}} {T : Type} {m : T → ℕ} {M : ℕ} {U : X.affineOpens}
    {c D : Let m → Fin (M + 1) → Γ(X, U.1)} (h : LeftInv D c) (w : Pm m) (en : En m) :
    Ideal.span (Set.range (plk (uvec c w) en.2.1)) = ⊤ :=
  (Ideal.eq_top_iff_one _).2 (Ideal.mem_span_range_iff_exists_fun.2 ⟨_,
    (GlobalTheory.T.cauchyBinet_plucker_and_cellCoordinates.2 T m (CR m U) M _ _ w MvPolynomial.X
      (h.map (MvPolynomial.C : Γ(X, U.1) →+* CR m U))).1 en.1 en.2.1 en.2.2⟩)

theorem exists_isPlk : ∀ (O K : Type) [CommRing O] [Field K] (β : O →+* K) (X : Scheme.{0}) (s : X ⟶ Sp O)
    (T : Type) [Finite T] (m : T → ℕ) (M : ℕ) (B : Type) (V : B → X.affineOpens) (α : ∀ b, K →+* Γ(X, (V b).1))
    (c D : ∀ b, Let m → Fin (M + 1) → Γ(X, (V b).1)), IsProjOver s → IsCover β s V α c D →
    ∃ (P : Scheme.{0}) (p0 : P ⟶ X) (p : ∀ en : En m, P ⟶ PSpace O (plN M en.1))
      (h : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ P)), IsPlk β s V α c p0 p h := by
  intro O K _ _ β X s T _ m M B V α c D hs hC
  obtain ⟨P, p0, p, hP, hp, univ⟩ := GlobalTheory.T.exists_isProjOver_finite_fibreProduct O (En m) X s (fun en => PSpace O (plN M en.1))
    (fun en => PSpace.str O _) hs fun en => ⟨_, 𝟙 _, inferInstance, Category.id_comp _⟩
  have hb : ∀ b, cbase m (V b) ≫ s =
      spMap ((MvPolynomial.C : _ →+* CR m (V b)).comp ((α b).comp β)) := fun b => by
    rw [cbase, Category.assoc, hC.ovr b, ← Spec.map_comp]
    rfl
  choose h hh using fun (b : B) (w : Pm m) => (univ _ (cbase m (V b))
    (fun en => pt ((MvPolynomial.C : _ →+* CR m (V b)).comp ((α b).comp β)) (plk (uvec (c b) w) en.2.1)
      (span_plk_uvec_eq_top (hC.inv b) w en))
    fun en => (pt_str _ _ _).trans (hb b).symm).exists
  refine ⟨P, p0, p, h, ⟨fun b w => (hh b w).1, fun b w en => ⟨_, (hh b w).2 en⟩⟩, hP, hp, fun Z a a' h0 h1 => ?_⟩
  exact (univ Z (a ≫ p0) (fun en => a ≫ p en) fun en => by
    rw [Category.assoc, hp, Category.assoc]).unique ⟨rfl, fun _ => rfl⟩ ⟨h0.symm, fun en => (h1 en).symm⟩

end GlobalTheory.FlagEmb
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPointOfIntegralPoint
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.HTLine
open Formalism.MainNotions.DIV.Cons (intO SCF)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.Pj.PointsOfFlagModel GlobalTheory.ShFam.Pad.Pull

namespace GlobalTheory.ModelPt

theorem exists_ptC : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Z : Mdl Y i₀) (C : SCF p) (z : Sp ↥(intO ↥C.S) ⟶ Z.X), Set.range (spMap (intO ↥C.S).subtype ≫ z) ⊆ Z.opn → ∃ P : PointsOfFlagModel.PtC (Y Z.i) C, z ≫ Z.π = P.yt := by
  intro E _ _ _ H Dw Xo p W Y i₀ _ _ Z C z hz
  set w : Sp ↥C.S ⟶ Z.X := spMap (intO ↥C.S).subtype ≫ z with hw
  obtain ⟨pt⟩ : Nonempty (Sp ↥C.S) := inferInstance
  have hpt : w pt ∈ Z.opn := hz ⟨pt, rfl⟩
  rw [← Z.cover] at hpt
  obtain ⟨a, ha⟩ := Set.mem_iUnion.1 hpt
  have hsub : Subsingleton (Sp ↥C.S) := inferInstance
  obtain ⟨φ, hφ⟩ := exists_fromSpec (Z.U a).2 w (fun q _ => by
    rw [Subsingleton.elim q pt]; exact ha)
  have hcomp : ∀ {A B D : Type} [CommRing A] [CommRing B] [CommRing D] (f : A →+* B) (g : B →+* D),
      spMap (g.comp f) = spMap g ≫ spMap f := fun f g => by
    rw [← Spec.map_comp]; rfl
  let fK : Z.i.c.F →+* ↥C.S := φ.comp (Z.alg a)
  let alg : ↥(Z.i.c.V W) →+* ↥(intO ↥C.S) := (Spec.preimage (z ≫ Z.π ≫ (Y Z.i).s)).hom
  have halg : spMap alg = z ≫ Z.π ≫ (Y Z.i).s := Spec.map_preimage _
  have hs := affineOpenChart_comp_structure_eq_spMap Z hφ
  have compat : (intO ↥C.S).subtype.comp alg = fK.comp (Z.i.c.V W).subtype := by
    refine congrArg CommRingCat.Hom.hom (Spec.map_injective (a₁ := CommRingCat.ofHom _) (a₂ := CommRingCat.ofHom _) ?_)
    change spMap _ = spMap _
    rw [hcomp, hcomp, halg, ← hs, hw, Category.assoc]
  have := (Y Z.i).jQ_open
  let q : Sp ↥C.S ⟶ pullback (Y Z.i).s (spMap (Z.i.c.V W).subtype) :=
    pullback.lift (w ≫ Z.π) (spMap fK) ((Category.assoc _ _ _).trans hs)
  have hq : q ≫ pullback.fst _ _ = w ≫ Z.π := pullback.lift_fst _ _ _
  have hq2 : q ≫ pullback.snd _ _ = spMap fK := pullback.lift_snd _ _ _
  have : IsPreimmersion (spMap (Z.i.c.V W).subtype) :=
    IsPreimmersion.of_isLocalization (R := Z.i.c.V W) (S := Z.i.c.F) (nonZeroDivisors _)
  have hr : Set.range q ⊆ Set.range (Y Z.i).jQ := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, hy⟩ := range_opn Z hφ ⟨x, rfl⟩
    refine ⟨y, (pullback.fst (Y Z.i).s (spMap (Z.i.c.V W).subtype)).isEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hq, Scheme.Hom.comp_apply w]
    exact hy
  let y := IsOpenImmersion.lift _ q hr
  have hy : y ≫ (Y Z.i).jQ = q := IsOpenImmersion.lift_fac _ _ _
  refine ⟨⟨alg, fK, compat, y, ?_, z ≫ Z.π, ?_, ?_⟩, rfl⟩
  · rw [← (Y Z.i).jQ_over, ← Category.assoc, hy, hq2]
  · rw [halg, Category.assoc]
  · rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model.j, reassoc_of% hy, hq]
    rfl

end GlobalTheory.ModelPt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRealBilinFormEqSumAdditiveImageIntFormsStatement
section
open GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_realBilinForm_eq_sum_additive_image_intForms : ∀ {L : Type} [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L] (B : L →ₗ[ℤ] L →ₗ[ℤ] ℝ), ∃ (n : ℕ) (w : Fin n → ℝ) (Q : Fin n → LinearMap.BilinForm ℤ L), B = ∑ j, w j • toReal (Q j) ∧ ∀ j, ∃ g : ℝ →+ ℝ, ∀ y z, (Q j y z : ℝ) = g (B y z) := by
  first | exact @GlobalTheory.PolFan.exists_sum_toReal_additive_images | exact GlobalTheory.PolFan.exists_sum_toReal_additive_images | (intros; apply GlobalTheory.PolFan.exists_sum_toReal_additive_images <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRescaleUniformisationRigidificationStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rescale_uniformisation_rigidification : ∀ (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (g : ℕ) (u : HolUnif A L g) (rig : LB.Gen (L.pull (eSec A))), L.IsLB → rig.IsGen → ∃ (u' : HolUnif A L g) (lam : ℂ), lam ≠ 0 ∧ u'.ex = u.ex ∧ u'.Λ = u.Λ ∧ u'.IsRig rig ∧ ∀ i z, u'.fr i z = lam * u.fr i z := by
  first | exact @GlobalTheory.RigRescale.exists_rescale_rig | exact GlobalTheory.RigRescale.exists_rescale_rig | (intros; apply GlobalTheory.RigRescale.exists_rescale_rig <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsScfEmbeddingDvdStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.HTLine
open Formalism.MainNotions.DIV.Cons (intO SCF)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_spherically_complete_embedding' : ∀ (p : ℕ) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], p.Prime → (p : V) ∈ IsLocalRing.maximalIdeal V → Cardinal.mk V ≤ Cardinal.continuum → ∃ (C : SCF p) (φ : V →+* ↥(intO ↥C.S)), Function.Injective φ ∧ ∀ a b : V, ‖((φ a : ↥(intO ↥C.S)) : ↥C.S)‖ ≤ ‖((φ b : ↥(intO ↥C.S)) : ↥C.S)‖ → b ∣ a := by
  first | exact @GlobalTheory.ShFam.Pad.Pull.exists_scf_embedding_dvd | exact GlobalTheory.ShFam.Pad.Pull.exists_scf_embedding_dvd | (intros; apply GlobalTheory.ShFam.Pad.Pull.exists_scf_embedding_dvd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitCoefOpen
section
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

noncomputable section

namespace GlobalTheory.KeyOpen

theorem glue_units {Z : Scheme.{0}} [IsReduced Z] (V : Z.Opens) (P : Z.Opens → Prop)
    (hP : ∀ p ∈ V, ∃ W : Z.Opens, IsAffineOpen W ∧ W ≤ V ∧ P W ∧ p ∈ W)
    (R : ∀ (L : Type) [Field L], (Sp L ⟶ Z) → L → Prop)
    (uniq : ∀ (L : Type) [Field L] (z : Sp L ⟶ Z), ⊤ ≤ z ⁻¹ᵁ V → ∀ x y, R L z x → R L z y → x = y)
    (loc : ∀ W : Z.Opens, IsAffineOpen W → W ≤ V → P W → ∃ a : Γ(Z, W)ˣ,
      ∀ (L : Type) [Field L] (z : Sp L ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ W), R L z (ev z W hz a.val)) :
    ∃ a : Γ(Z, V)ˣ, ∀ (L : Type) [Field L] (z : Sp L ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ V), R L z (ev z V hz a.val) := by
  let I := {W : Z.Opens // IsAffineOpen W ∧ W ≤ V ∧ P W}
  choose a ha using fun i : I => loc i.1 i.2.1 i.2.2.1 i.2.2.2
  have hc : ∀ p ∈ V, ∃ i : I, p ∈ i.1 := fun p hp => by
    obtain ⟨W, hW, hWV, hPW, hpW⟩ := hP p hp
    exact ⟨⟨W, hW, hWV, hPW⟩, hpW⟩
  have hcov : V ≤ iSup fun i : I => i.1 := fun p hp => TopologicalSpace.Opens.mem_iSup.2 (hc p hp)
  have key : ∀ (i j : I) (L : Type) [Field L] (z : Sp L ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ (i.1 ⊓ j.1)),
      ev z _ hz (resG Z inf_le_left (a i).val) = ev z _ hz (resG Z inf_le_right (a j).val) := by
    intro i j L _ z hz
    have hi := GlobalTheory.FlagMod.le_preimage_mono inf_le_left hz
    have hj := GlobalTheory.FlagMod.le_preimage_mono inf_le_right hz
    rw [GlobalTheory.FlagMod.ev_res z _ hz hi, GlobalTheory.FlagMod.ev_res z _ hz hj]
    exact uniq L z (GlobalTheory.FlagMod.le_preimage_mono i.2.2.1 hi) _ _ (ha i L z hi) (ha j L z hj)
  obtain ⟨s, hs, -⟩ := Z.sheaf.existsUnique_gluing' (fun i : I => i.1) V (fun i => homOfLE i.2.2.1)
    hcov (fun i => (a i).val) (fun i j =>
      GlobalTheory.FlagMod.ext_ev_field (a := resG Z inf_le_left (a i).val) (b := resG Z inf_le_right (a j).val)
        fun L _ z hz => key i j L z hz)
  obtain ⟨t, ht, -⟩ := Z.sheaf.existsUnique_gluing' (fun i : I => i.1) V (fun i => homOfLE i.2.2.1)
    hcov (fun i => (a i)⁻¹.val) (fun i j =>
      GlobalTheory.FlagMod.ext_ev_field (a := resG Z inf_le_left (a i)⁻¹.val) (b := resG Z inf_le_right (a j)⁻¹.val)
        fun L _ z hz => by
          have e := key i j L z hz
          have e₁ := map_units_inv (((ev z _ hz).comp (resG Z inf_le_left)) : Γ(Z, i.1) →+* L) (a i)
          have e₂ := map_units_inv (((ev z _ hz).comp (resG Z inf_le_right)) : Γ(Z, j.1) →+* L) (a j)
          simp only [RingHom.coe_comp, Function.comp_apply] at e₁ e₂
          rw [e₁, e₂, e])
  obtain ⟨s, t, hs, ht⟩ : ∃ s t : Γ(Z, V), (∀ i : I, resG Z i.2.2.1 s = (a i).val) ∧
      ∀ i : I, resG Z i.2.2.1 t = (a i)⁻¹.val := ⟨s, t, hs, ht⟩
  have hval : ∀ (L : Type) [Field L] (z : Sp L ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ V), ∃ i : I, ∃ hi : ⊤ ≤ z ⁻¹ᵁ i.1,
      ev z V hz s = ev z i.1 hi (a i).val ∧ ev z V hz t = ev z i.1 hi (a i)⁻¹.val := by
    intro L _ z hz
    obtain ⟨i, hi⟩ := hc (z (IsLocalRing.closedPoint L)) (hz (Set.mem_univ _))
    have hi' : ⊤ ≤ z ⁻¹ᵁ i.1 := ((IsLocalRing.closed_point_mem_iff (U := z ⁻¹ᵁ i.1)).1 hi).ge
    exact ⟨i, hi', (GlobalTheory.FlagMod.ev_res z i.2.2.1 hi' hz s).symm.trans (congrArg _ (hs i)),
      (GlobalTheory.FlagMod.ev_res z i.2.2.1 hi' hz t).symm.trans (congrArg _ (ht i))⟩
  have hst : s * t = 1 := GlobalTheory.FlagMod.ext_ev_field fun L _ z hz => by
    obtain ⟨i, hi, e₁, e₂⟩ := hval L z hz
    rw [map_mul, map_one, e₁, e₂, ← map_mul, Units.mul_inv, map_one]
  refine ⟨⟨s, t, hst, by rw [mul_comm, hst]⟩, fun L _ z hz => ?_⟩
  obtain ⟨i, hi, e₁, -⟩ := hval L z hz
  show R L z (ev z V hz s)
  rw [e₁]
  exact ha i L z hi

end GlobalTheory.KeyOpen

namespace GlobalTheory.KeyOpen

end GlobalTheory.KeyOpen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedUniformisationPolarisedTriple
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace Polynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.ResLift

open ReciprocityTheory.ChartRestriction.G.Semi.Nb

theorem irreducible_adjoinRoot {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (f : V[X])
    (hf : f.Monic) (hg : Irreducible (f.map (residue V))) [IsDomain (AdjoinRoot f)] [IsLocalRing (AdjoinRoot f)]
    [IsDiscreteValuationRing (AdjoinRoot f)] {ϖ : V} (hϖ : Irreducible ϖ) :
    Irreducible (algebraMap V (AdjoinRoot f) ϖ) := by
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer, maxEq f hf hg, hϖ.maximalIdeal_eq, Ideal.map_span,
    Set.image_singleton]

theorem exists_lift (n : ℕ) : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [IsAdicComplete (maximalIdeal V) V]
    (k'' : Type) [Field k''] [Algebra (ResidueField V) k'']
    [FiniteDimensional (ResidueField V) k''], Module.finrank (ResidueField V) k'' = n →
    ∃ (V'' : Type) (_ : CommRing V'') (_ : IsDomain V'') (_ : IsDiscreteValuationRing V'')
      (_ : IsAdicComplete (maximalIdeal V'') V'') (_ : Algebra V V''),
      Module.Finite V V'' ∧ Function.Injective (algebraMap V V'') ∧
      (∀ ϖ : V, Irreducible ϖ → Irreducible (algebraMap V V'' ϖ)) ∧
      ∃ (_ : IsLocalHom (algebraMap V V'')) (e : k'' ≃+* ResidueField V''),
        e.toRingHom.comp (algebraMap (ResidueField V) k'') =
          ResidueField.map (algebraMap V V'') := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V' _ _ _ _ k'' _ _ _ hn
  by_cases hs : Function.Surjective (algebraMap (ResidueField V') k'')
  · have hb : Function.Bijective (algebraMap (ResidueField V') k'') :=
      ⟨(algebraMap (ResidueField V') k'').injective, hs⟩
    refine ⟨V', inferInstance, inferInstance, inferInstance, inferInstance, Algebra.id V',
      Module.Finite.self V', Function.injective_id, fun ϖ h => h, ?_, (RingEquiv.ofBijective _ hb).symm, ?_⟩
    · change IsLocalHom (RingHom.id V'); infer_instance
    · ext x
      change _ = ResidueField.map (RingHom.id V') x
      rw [ResidueField.map_id]
      exact (RingEquiv.ofBijective _ hb).symm_apply_apply x
  · obtain ⟨α, hα⟩ : ∃ α : k'', α ∉ Set.range (algebraMap (ResidueField V') k'') := by
      by_contra h
      push_neg at h
      exact hs h
    have hint : IsIntegral (ResidueField V') α := .of_finite (ResidueField V') α
    have hmon := minpoly.monic hint
    have hirr := minpoly.irreducible hint
    obtain ⟨f, hfg, hdeg, hf⟩ := exists_monic_lift (minpoly (ResidueField V') α) hmon
    have hg : Irreducible (f.map (residue V')) := hfg ▸ hirr
    have := isDomain f hf hg
    have := isLocal f hf hg
    have := dvr f hf hg
    have := complete f hf hg
    have := locHom f hf hg
    have := finite f hf
    have haev : Polynomial.aeval α (f.map (residue V')) = 0 := by
      rw [hfg]; exact minpoly.aeval _ α
    let ψ : AdjoinRoot (f.map (residue V')) →ₐ[ResidueField V'] k'' :=
      AdjoinRoot.liftAlgHom _ (Algebra.ofId _ _) α (by rwa [Polynomial.aeval_def] at haev)
    letI : Algebra (ResidueField (AdjoinRoot f)) k'' :=
      (ψ.toRingHom.comp (resEquiv f hf hg).toRingHom).toAlgebra
    have : Fact (Irreducible (f.map (residue V'))) := ⟨hg⟩
    letI : Algebra (AdjoinRoot (f.map (residue V'))) k'' := ψ.toRingHom.toAlgebra
    have : IsScalarTower (ResidueField V') (AdjoinRoot (f.map (residue V'))) k'' :=
      IsScalarTower.of_algebraMap_eq fun x => (ψ.commutes x).symm
    have hL : Module.finrank (ResidueField V') (AdjoinRoot (f.map (residue V'))) =
        (minpoly (ResidueField V') α).natDegree := by
      rw [(AdjoinRoot.powerBasis hg.ne_zero).finrank, AdjoinRoot.powerBasis_dim, hfg]
    have hd1 : (minpoly (ResidueField V') α).natDegree ≠ 1 := fun h =>
      hα (minpoly.natDegree_eq_one_iff.1 h)
    have hd0 : 0 < (minpoly (ResidueField V') α).natDegree := minpoly.natDegree_pos hint
    have : FiniteDimensional (AdjoinRoot (f.map (residue V'))) k'' :=
      Module.Finite.of_restrictScalars_finite (ResidueField V') _ k''
    have hmul := Module.finrank_mul_finrank (ResidueField V') (AdjoinRoot (f.map (residue V'))) k''
    have hAL : Module.finrank (ResidueField (AdjoinRoot f)) k'' =
        Module.finrank (AdjoinRoot (f.map (residue V'))) k'' :=
      Algebra.finrank_eq_of_equiv_equiv (resEquiv f hf hg) (RingEquiv.refl k'') rfl
    have hpos : 0 < Module.finrank (AdjoinRoot (f.map (residue V'))) k'' := Module.finrank_pos
    have : FiniteDimensional (ResidueField (AdjoinRoot f)) k'' :=
      Module.finite_of_finrank_pos (hAL ▸ hpos)
    have hlt : Module.finrank (ResidueField (AdjoinRoot f)) k'' < n := by
      rw [hAL, ← hn, ← hmul, hL]
      calc Module.finrank (AdjoinRoot (f.map (residue V'))) k''
          < 2 * Module.finrank (AdjoinRoot (f.map (residue V'))) k'' := by omega
        _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
    obtain ⟨V'', i1, i2, i3, i4, i5, hfin, hinj, hirr'', hloc, e2, he2⟩ :=
      ih _ hlt (AdjoinRoot f) k'' rfl
    letI : Algebra V' V'' := ((algebraMap (AdjoinRoot f) V'').comp (algebraMap V' (AdjoinRoot f))).toAlgebra
    have : IsScalarTower V' (AdjoinRoot f) V'' := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have hlc : IsLocalHom (algebraMap V' V'') := by
      change IsLocalHom ((algebraMap (AdjoinRoot f) V'').comp (algebraMap V' (AdjoinRoot f)))
      infer_instance
    refine ⟨V'', i1, i2, i3, i4, inferInstance, Module.Finite.trans (AdjoinRoot f) V'',
      hinj.comp (inj f hf hg), fun ϖ hϖ => hirr'' _ (irreducible_adjoinRoot f hf hg hϖ), hlc, e2, ?_⟩
    have h1 : (algebraMap (ResidueField (AdjoinRoot f)) k'').comp
        (ResidueField.map (algebraMap V' (AdjoinRoot f))) = algebraMap (ResidueField V') k'' := by
      change ψ.toRingHom.comp ((resEquiv f hf hg).toRingHom.comp
        (ResidueField.map (algebraMap V' (AdjoinRoot f)))) = _
      rw [resEquiv_comp f hf hg, ← AdjoinRoot.algebraMap_eq]
      exact ψ.comp_algebraMap
    change e2.toRingHom.comp (algebraMap (ResidueField V') k'') =
      ResidueField.map ((algebraMap (AdjoinRoot f) V'').comp (algebraMap V' (AdjoinRoot f)))
    rw [ResidueField.map_comp, ← h1, ← RingHom.comp_assoc, he2]

end GlobalTheory.ResLift

namespace GlobalTheory.TorRef

theorem exists_unif_unram : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsLocalRing V], CDvr V → ∀ ϖ : V, Irreducible ϖ → ∀ (t : SAB H (Sp V)), PolAt t (jK V) →
    ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (f : V →+* V'),
      CDvr V' ∧ Function.Injective f ∧ IsLocalHom f ∧ Irreducible (f ϖ) ∧
      ∃ (t' : SAB H (Sp V')) (_ : SABMap t' t (spMap f)), Nonempty (PELUnif (maximalIdeal V') t') := by
  intro E _ _ _ H V _ _ _ hV ϖ hϖ t hp
  obtain ⟨hd, hc, hz⟩ := (cDvr_iff V).1 hV
  let Ω := AlgebraicClosure (ResidueField V)
  obtain ⟨s, hs, h⟩ := GlobalTheory.Ex.UnifModel.exists_finite_split (algebraMap (ResidueField V) Ω) t.G t.semi
  have := hs.to_subtype
  let k'' := IntermediateField.adjoin (ResidueField V) s
  have : FiniteDimensional (ResidueField V) k'' :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  obtain ⟨W, _, _, _, hcW, _, -, hinj, hirr, hloc, e, he⟩ :=
    GlobalTheory.ResLift.exists_lift _ V k'' rfl
  have : IsLocalRing W := inferInstance
  have hzW : CharZero W := charZero_of_injective_algebraMap hinj
  let β : ResidueField W →+* Ω := k''.val.toRingHom.comp e.symm.toRingHom
  have hβ : β.comp (ResidueField.map (algebraMap V W)) = algebraMap (ResidueField V) Ω := by
    rw [← he]
    ext x
    simp [β]
  have hsp := h W (algebraMap V W) β hβ fun x hx =>
    ⟨e ⟨x, IntermediateField.subset_adjoin _ _ hx⟩, by simp [β]⟩
  obtain ⟨PP', cub, sym, adj, prim, m, -⟩ := sabPull CubePf.cubePull (spMap (algebraMap V W)) t
  have j : Function.Injective ((algebraMap W (FractionRing W)).comp (algebraMap V W)) :=
    (IsFractionRing.injective W _).comp hinj
  let g : FractionRing V →+* FractionRing W := IsFractionRing.lift j
  have hp' := GlobalTheory.DatUniq.polAt_pull m hp (jK W) (spMap g)
    ((GlobalTheory.Ex.UnifModel.spMap_comp (IsFractionRing.lift_algebraMap j)).trans
      (GlobalTheory.Ex.UnifModel.spMap_comp fun _ => rfl).symm)
  have hW : CDvr W := (cDvr_iff W).2 ⟨inferInstance, hcW, hzW⟩
  obtain ⟨P, -⟩ := GlobalTheory.LN.uDvrSt_holds E H W hW _ hp' hsp
  exact ⟨W, inferInstance, inferInstance, inferInstance, algebraMap V W, hW, hinj, hloc, hirr ϖ hϖ, _, m, ⟨P⟩⟩

end GlobalTheory.TorRef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExpModelFiberEqOneIffMemPeriodLatticeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.expModelFiber_eq_one_iff_mem_periodLattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (σ₀ : KA l →+* ℂ) (Fu : FamilyUnif Xo σ₀ ty) (y : Sp ℂ ⟶ Xo.XF c) (i : Fin Fu.n) (P : (Fu.Di i).La →+ (Fin g → ℂ)) (p : Sp ℂ ⟶ Z.X) (hu : Fu.u i P = y ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) (hp : y ≫ Z.jQ ≫ pullback.fst Z.s (spMap β) = p), IsPeriod (Fu.Di i) ty P → ∀ z, pushEx Z Fu y i P p hu hp z = 1 ↔ z ∈ P.range := by
  first | exact @GlobalTheory.ShFam.Hor.LogCh.pushEx_eq_one_iff | exact GlobalTheory.ShFam.Hor.LogCh.pushEx_eq_one_iff | (intros; apply GlobalTheory.ShFam.Hor.LogCh.pushEx_eq_one_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FramesAgreeOnLieEmbeddingChartStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frames_agree_on_lie_embedding_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (X : Scheme.{0}) (t : SAB H X) (L : FinLB X) (aff : ∀ i, IsAffineOpen (L.U i)) (M : ℕ) (crd : Crd t L M), IsLieEmb t L aff crd → ∀ (i : Fin L.n) (R : Type) [CommRing R] (φ : Γ(X, L.U i) →+* R) (x : Sp R ⟶ X) (f f' : c.F →+* R) (u u' : Vecs Dw t R), spMap φ ≫ (aff i).fromSpec = x → IsFrame t f x u → IsFrame t f' x u' → (SameFlag (fun τ => Finset.range (Dw.mult τ + 1)) t x u u' ↔ ∃ d, Tri (fun z : Let Dw.mult => crd i R φ (u z.1 z.2)) (fun z => crd i R φ (u' z.1 z.2)) d) ∧ (∀ τ, LinearIndependent R fun j => crd i R φ (u τ j)) ∧ (f = f' → InBlock (fun z : Let Dw.mult => crd i R φ (u z.1 z.2)) (fun z => crd i R φ (u' z.1 z.2))) := by
  first | exact @GlobalTheory.FlagEmb.sameFlag_iff_tri_crd | exact GlobalTheory.FlagEmb.sameFlag_iff_tri_crd | (intros; apply GlobalTheory.FlagEmb.sameFlag_iff_tri_crd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GrassmannCellCoordinatesExistStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.grassmann_cell_coordinates_exist : ∀ (K : Type) [Field K] (m a k b N : ℕ) (hk : k ≤ m) (D c : Fin m → Fin (N + 1) → K) (u : Fin k → Fin (N + 1) → K), a ≤ k → k ≤ b → LeftInv D c → LinearIndependent K u → initSpan K c a ≤ Submodule.span K (Set.range u) → Submodule.span K (Set.range u) ≤ initSpan K c b → (∃ w : GPm m a b, ∑ q, gell a b hk D w q * plk u id q ≠ 0) ∧ ∀ w : GPm m a b, ∑ q, gell a b hk D w q * plk u id q ≠ 0 → ∃ x : GVar m a k b → K, Submodule.span K (Set.range u) = initSpan K (gvec c w x) k := by
  first | exact @GlobalTheory.GrCl.Normal.main | exact GlobalTheory.GrCl.Normal.main | (intros; apply GlobalTheory.GrCl.Normal.main <;> assumption)
end

