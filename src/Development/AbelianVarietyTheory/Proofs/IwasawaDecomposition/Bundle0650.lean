import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0606
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramSmoothOfHolomorphicFrames
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0633
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0636
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0567
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GenericLieMultiplicitiesUniformisedGroup
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0034
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0630
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0632
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

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExpCoordinatesTangentFieldHolomorphicPeriodMap
section
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open GlobalTheory.ArcQ
open scoped ContDiff

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.ModelExpCoord

open GlobalTheory.ShFam.Hor.LogCh
open ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows (isDerivAt0_unique)

theorem coord_holomorphic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (i : Fin Fu.n) (n : ℕ) (B : Set (Fin n → ℂ)) (P : (Fin n → ℂ) → ((Fu.Di i).La →+ (Fin g → ℂ))) (p : (Fin n → ℂ) → (Sp ℂ ⟶ Xo.XF c)) (hu : ∀ b, Fu.u i (P b) = p b ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) (V : (gen Z).affineOpens) (v : Sp (DualNumber Γ(gen Z, V.1)) ⟶ Z.t.G.left), IsOpen B → (∀ b, IsPeriod (Fu.Di i) ty (P b)) → (∀ a, DifferentiableOn ℂ (fun b => P b a) B) → (∀ b, p b ≫ pullback.snd _ _ = spMap σ) → IsTanAtG Z.t (LogKS.chart V ≫ genι Z) v → ∃ W : (Fin n → ℂ) → (Fin g → ℂ), DifferentiableOn ℂ W {b ∈ B | ⊤ ≤ (p b ≫ Z.jQ) ⁻¹ᵁ V.1} ∧ ∀ b ∈ B, ∀ (y : CxPts (genStr Z) σ) (hy : y ∈ ptsIn (genStr Z) σ V.1), y.1 = p b ≫ Z.jQ → IsDerivAt0 (fun z => GlobalTheory.ShFam.Hor.LogCh.liftEx Z Fu (p b) i (P b) (hu b) z ≫ Z.m.φ) (W b) (spMap (Formalism.L2.Pj.dualMap (evHom hy)) ≫ v) := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ g ty Fu i n B P p hu V v hB hP hPd hs hv
  classical
  have h1 := Fu.hol i n B P hB ⟨fun b _ => hP b, hPd⟩
  have hp : IsHolTo B p := TrueCx.TorHolo.isHolTo_of_fst _ _ hB (spMap σ) hs
    (LocLift.isHolTo_congr h1.1 fun b _ => (hu b).symm)
  have h2 := TrueCx.TorFrHolo.isHolTo_lift Z.m0.toSABMap.cart.1 hB (fun b z => (Fu.ex i (P b) z).left) p h1.2 hp
    (fun b z => by rw [Over.w (Fu.ex i (P b) z), ← hu b]; rfl)
  have hFt : IsHolTo (B ×ˢ Set.univ) (fun bz : (Fin n → ℂ) × (Fin g → ℂ) =>
      liftEx Z Fu (p bz.1) i (P bz.1) (hu bz.1) bz.2 ≫ Z.m.φ) :=
    ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_comp h2 Z.m.φ
  have hY : IsHolTo B fun b => p b ≫ Z.jQ := ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_comp hp Z.jQ
  set B' := {b ∈ B | ⊤ ≤ (p b ≫ Z.jQ) ⁻¹ᵁ V.1} with hB'def
  have hB' : IsOpen B' := (hY V.1 0).1
  let yb : (Fin n → ℂ) → CxPts (genStr Z) σ := fun b =>
    ⟨p b ≫ Z.jQ, by rw [Category.assoc, Z.jQ_over]; exact hs b⟩
  have hm : ∀ b, ⊤ ≤ (p b ≫ Z.jQ) ⁻¹ᵁ V.1 → yb b ∈ ptsIn (genStr Z) σ V.1 := fun b h => h
  have hExp : ∀ b, IsExpAt Z.t (p b ≫ Z.jQ ≫ genι Z)
      (pushEx Z Fu (p b) i (P b) (p b ≫ Z.jQ ≫ genι Z) (hu b) rfl) := fun b =>
    isExpAt_pushEx E H Dw l Xo c O β Z g ty _ Fu (p b) i (P b) (p b ≫ Z.jQ ≫ genι Z) (hu b) rfl (hP b)
  have hTan : ∀ b (h : ⊤ ≤ (p b ≫ Z.jQ) ⁻¹ᵁ V.1),
      IsTanAtG Z.t (p b ≫ Z.jQ ≫ genι Z) (spMap (Formalism.L2.Pj.dualMap (evHom (hm b h))) ≫ v) := fun b h =>
    isTan_map (evHom (hm b h)) (by rw [← Category.assoc, spMap_evHom]; rfl) hv
  have hW0 : ∀ b (h : ⊤ ≤ (p b ≫ Z.jQ) ⁻¹ᵁ V.1), ∃! w, IsDerivAt0
      (fun z => liftEx Z Fu (p b) i (P b) (hu b) z ≫ Z.m.φ) w
      (spMap (Formalism.L2.Pj.dualMap (evHom (hm b h))) ≫ v) := fun b h =>
    (hExp b).2.2 _ (hTan b h)
  let W : (Fin n → ℂ) → Fin g → ℂ := fun b =>
    if h : ⊤ ≤ (p b ≫ Z.jQ) ⁻¹ᵁ V.1 then (hW0 b h).exists.choose else 0
  have hWd : ∀ b (h : ⊤ ≤ (p b ≫ Z.jQ) ⁻¹ᵁ V.1), IsDerivAt0
      (fun z => liftEx Z Fu (p b) i (P b) (hu b) z ≫ Z.m.φ) (W b)
      (spMap (Formalism.L2.Pj.dualMap (evHom (hm b h))) ≫ v) := fun b h => by
    have e : W b = (hW0 b h).exists.choose := dif_pos h
    rw [e]
    exact (hW0 b h).exists.choose_spec
  have : IsOpenImmersion (LogKS.chart V) := IsAffineOpen.isOpenImmersion_fromSpec V.2
  have hdiff : ∀ b₀ ∈ B', DifferentiableAt ℂ W b₀ := fun b₀ hb₀ => by
    have h₀ : ⊤ ≤ (p b₀ ≫ Z.jQ) ⁻¹ᵁ V.1 := hb₀.2
    let ev : (Fin n → ℂ) → (Γ(gen Z, V.1) →+* ℂ) := fun b =>
      if h : ⊤ ≤ (p b ≫ Z.jQ) ⁻¹ᵁ V.1 then evHom (hm b h) else evHom (hm b₀ h₀)
    have hevb : ∀ b (h : ⊤ ≤ (p b ≫ Z.jQ) ⁻¹ᵁ V.1), ev b = evHom (hm b h) := fun b h => dif_pos h
    have hev : ∀ cc, DifferentiableAt ℂ (fun b => ev b cc) b₀ :=
      HolLieFrame.differentiableAt_ev (B := B') (LocLift.isHolTo_mono hY hB' fun b hb => hb.1) (LogKS.chart V) ev
        (fun b hb => by rw [hevb b hb.2]; exact (spMap_evHom (hm b hb.2)).symm) hb₀
    have hder : ∀ b ∈ B', IsDerivAt0 (fun z => liftEx Z Fu (p b) i (P b) (hu b) z ≫ Z.m.φ) (W b)
        (spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR (ev b)) ≫ v) := fun b hb => by
      rw [hevb b hb.2]
      exact hWd b hb.2
    refine HolLieFrame.differentiableAt_of_forms W b₀ fun w hw => ?_
    have hw' : ∀ (O : Z.t.G.left.Opens) (f : Γ(Z.t.G.left, O)),
        ⊤ ≤ (liftEx Z Fu (p b₀) i (P b₀) (hu b₀) 0 ≫ Z.m.φ) ⁻¹ᵁ O →
        fderiv ℂ (fun z => valAt' (liftEx Z Fu (p b₀) i (P b₀) (hu b₀) z ≫ Z.m.φ) O f) 0 w = 0 := by
      intro O f hO
      refine hw (fun b => fderiv ℂ (fun z => valAt' (liftEx Z Fu (p b) i (P b) (hu b) z ≫ Z.m.φ) O f) 0)
        (HolLieFrame.differentiableAt_fderiv
          (e := fun b z => liftEx Z Fu (p b) i (P b) (hu b) z ≫ Z.m.φ) hFt hb₀.1 O f hO) ?_
      obtain ⟨Fn, hF, hF'⟩ := HolLieFrame.exists_hol_snd v ev b₀ hev O f
        ((TangentOrigin.top_le_preimage_iff _ O).2 (by rw [(hder b₀ hb₀).1]; exact hO))
      refine hF.congr_of_eventuallyEq ?_
      filter_upwards [hF', hB'.mem_nhds hb₀] with b ⟨h, e'⟩ hb
      exact ((hder b hb).2 O h f).symm.trans e'
    have d₁ := LocalLift.isDerivAt0_const (fun z => liftEx Z Fu (p b₀) i (P b₀) (hu b₀) z ≫ Z.m.φ) w hw'
    have d₀ := LocalLift.isDerivAt0_const (fun z => liftEx Z Fu (p b₀) i (P b₀) (hu b₀) z ≫ Z.m.φ) 0
      fun _ _ _ => map_zero _
    obtain ⟨u, ⟨hut, hud⟩, -⟩ := (hExp b₀).2.1 0
    have hu0 := isDerivAt0_unique hud d₀
    obtain ⟨w', -, hw''⟩ := (hExp b₀).2.2 u hut
    have a1 : w = w' := hw'' w (by rw [hu0]; exact d₁)
    have a0 : (0 : Fin g → ℂ) = w' := hw'' 0 hud
    exact a1.trans a0.symm
  refine ⟨W, fun b hb => (hdiff b hb).differentiableWithinAt, fun b _ y hy hyb => ?_⟩
  have hyb' : y = yb b := Subtype.ext hyb
  subst hyb'
  exact hWd b hy

end GlobalTheory.ModelExpCoord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagCellPointEqOfTriangularFrames
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.FlagEmb

theorem spMap_comp_spMap_same {R S U : Type} [CommRing R] [CommRing S] [CommRing U] (f : R →+* S) (g : S →+* U) :
    spMap g ≫ spMap f = spMap (g.comp f) :=
  (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)).symm

theorem cell_pt_eq_of_tri (O K : Type) [CommRing O] [Field K] (β : O →+* K) (X : Scheme.{0}) (s : X ⟶ Sp O) (T : Type)
    [Finite T] (m : T → ℕ) (M : ℕ) (B : Type) (V : B → X.affineOpens) (α : ∀ b, K →+* Γ(X, (V b).1))
    (c D : ∀ b, Let m → Fin (M + 1) → Γ(X, (V b).1)) (P : Scheme.{0}) (p0 : P ⟶ X)
    (p : ∀ en : En m, P ⟶ PSpace O (plN M en.1)) (h : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ P))
    (hc : IsCover β s V α c D) (hp : IsPlk β s V α c p0 p h) (k : Type) [Field k] (b b' : B) (w w' : Pm m)
    (ψ : CR m (V b) →+* k) (ψ' : CR m (V b') →+* k) (d : Let m → k)
    (hb : spMap ψ ≫ cbase m (V b) = spMap ψ' ≫ cbase m (V b')) (hd : ∀ z, d z ≠ 0)
    (ht : Tri (fun z => ψ ∘ uvec (c b) w z) (fun z => ψ' ∘ uvec (c b') w' z) d) :
    spMap ψ ≫ h b w = spMap ψ' ≫ h b' w' := by
  have hO : ψ.comp ((MvPolynomial.C : _ →+* CR m (V b)).comp ((α b).comp β)) =
      ψ'.comp ((MvPolynomial.C : _ →+* CR m (V b')).comp ((α b').comp β)) := by
    have e := congrArg (· ≫ s) hb
    simp only [cbase, Category.assoc, hc.ovr, spMap_comp_spMap_same] at e
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  refine hp.ext _ _ _ ?_ fun en => ?_
  · rw [Category.assoc, Category.assoc, hp.base, hp.base, hb]
  · obtain ⟨hu, e⟩ := hp.plk b w en
    obtain ⟨hu', e'⟩ := hp.plk b' w' en
    rw [Category.assoc, Category.assoc, e, e', spMap_pt, spMap_pt]
    have hu2 := span_range_comp_eq_top _ hu' ψ'
    have key : ∀ (f g : O →+* k) (v v' : Fin (plN M en.1 + 1) → k) hv hv', f = g → (∃ u : kˣ, v' = u • v) →
        pt f v hv = pt g v' hv' := by
      rintro f g v v' hv hv' rfl hh
      exact (pt_eq_pt_iff f hv hv').2 hh
    refine key _ _ _ _ _ _ hO ⟨Units.mk0 (∏ l, d (en.2.1 l)) (Finset.prod_ne_zero_iff.2 fun l _ => hd _), ?_⟩
    rw [map_plk, map_plk, GlobalTheory.T.pluckerVector_blockTriangular_frame_change T m k M _ _ d en.1 en.2.1 ht en.2.2]
    rfl

end GlobalTheory.FlagEmb
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormallyUnramifiedEtaleCompletion
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.CharRank

open MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.Serre GlobalTheory.EigenSplit Matrix GlobalTheory.LieUnif
open ReciprocityTheory.ChartRestriction.G.Chart (prodPts)
open scoped CategoryTheory.Obj

theorem trace_of_unif_loc {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    {D : DegData R (maximalIdeal R)} {P : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    (U : UnifPre (maximalIdeal R) D P G) {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X] {oD : D.OAct O}
    {oP : P.OAct O} {aG : OAct O G} (hl : U.OLinear O oD oP aG.toRingAct) [IsCommMonObj D.toPre.P.A]
    [Smooth D.toPre.P.A.hom] {g h r : ℕ} {v : Fin g → (epsR R ⟶ G)} (hv : IsLieBasis v)
    {ρ : O →+* Module.End R (Fin g → R)} (hρ : ∀ a c, prodPts (ρ a c) v = prodPts c v ≫ aG.act a)
    {w : Fin h → (epsR R ⟶ D.toPre.P.A)} (hw : IsLieBasis w)
    {ρB : O →+* Module.End R (Fin h → R)}
    (hρB : ∀ a c, prodPts (ρB a c) w = prodPts c w ≫ (ofRingAct oD.onB.toRingAct).act a)
    (b : Module.Basis (Fin r) ℤ D.toPre.X) (a : O) :
    LinearMap.trace R _ (ρ a) = LinearMap.trace R _ (ρB a) + (latTrace b a : R) := by
  have key : ∀ e : ℕ, LinearMap.trace R _ (ρ a) - (LinearMap.trace R _ (ρB a) + (latTrace b a : R)) ∈
      maximalIdeal R ^ (e + 1) := fun e => by
    let f := Ideal.Quotient.mk (maximalIdeal R ^ (e + 1))
    have : IsLocalRing (R ⧸ maximalIdeal R ^ (e + 1)) := by
      have : Nontrivial (R ⧸ maximalIdeal R ^ (e + 1)) := Ideal.Quotient.nontrivial_iff.2 fun h =>
        (maximalIdeal.isMaximal R).ne_top (top_le_iff.1 (h.symm.le.trans (Ideal.pow_le_self (Nat.succ_ne_zero e))))
      exact IsLocalRing.of_surjective' f Ideal.Quotient.mk_surjective
    have := U.smooth
    obtain ⟨v', ρ', hv', hρ', hM⟩ := ToricRank.exists_action_pullback hv hρ f
    obtain ⟨w', ρB', hw', hρB', hMB⟩ := ToricRank.exists_action_pullback hw hρB f
    let gc := U.gt e
    have := gc.q_hom
    have := gc.i_hom
    have := gc.q_flat
    have := gc.q_surj
    have := gc.q_affine
    have := (H1.torus_dim (Sp (R ⧸ maximalIdeal R ^ (e + 1))) D.toPre.X).smooth
    have : Smooth gc.q.left := by
      refine MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth)
        (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
        ((H1.torsor_pullback gc.i gc.q gc.isKernel).map (Over.forget _)).flip
        ⟨⟨‹_›, ‹_›⟩, inferInstanceAs (QuasiCompact gc.q.left)⟩ ?_
      exact smooth_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _) this
    let aK := @Diag.diagAct (Sp (R ⧸ maximalIdeal R ^ (e + 1))) O _ D.toPre.X _ (Module.compHom _ (starRingEnd O))
    let MK : O → Matrix (Fin r) (Fin r) (R ⧸ maximalIdeal R ^ (e + 1)) := fun x =>
      (LinearMap.toMatrix b b (DistribSMul.toAddMonoidHom D.toPre.X (star x)).toIntLinearMap).map (Int.castRingHom _)
    have hvK := Diag.isLieBasis_dualBasis (R := R ⧸ maximalIdeal R ^ (e + 1)) b
    have hMK : ∀ x i, IsLieComb (MK x i) (fun i => Diag.lieVec (Diag.dualBasis _ b i))
        (Diag.lieVec (Diag.dualBasis _ b i) ≫ aK.act x) := fun x i =>
      Diag.isLieComb_comp_diagMap b b (DistribSMul.toAddMonoidHom D.toPre.X (star x)) i
    have hi : IsLinearHom aK (aG.pullback (thick R _ e) G) gc.i := ⟨inferInstance, fun x => by
      obtain ⟨t, ht, hi⟩ := hl.i_lin e x
      obtain rfl := ConstBasis.eq_diagMap (DistribSMul.toAddMonoidHom D.toPre.X (star x)) ht
      exact hi.symm⟩
    have h := trace_level (K := splitTorus (Sp (R ⧸ maximalIdeal R ^ (e + 1))) D.toPre.X) (aK := aK)
      (aG := aG.pullback (thick R _ e) G) (aB := (ofRingAct oD.onB.toRingAct).pullback (thick R _ e) _)
      (i := gc.i) (q := gc.q) hi ⟨inferInstance, hl.q_lin e⟩ gc.isKernel hvK hv' hw' a
      (MK a) ((LinearMap.toMatrix' (ρ a))ᵀ.map f) ((LinearMap.toMatrix' (ρB a))ᵀ.map f)
      (fun c => (ConstBasis.prodPts_act hvK hMK a c).symm) (fun c => by rw [← hM, hρ']) (fun c => by rw [← hMB, hρB'])
    rw [← Ideal.Quotient.eq, map_add, map_intCast, trace_map_eq, trace_map_eq, h]
    refine (add_comm _ _).trans (congrArg _ ?_)
    simp [MK, latTrace, Matrix.trace]
  rw [← sub_eq_zero, ← Ideal.mem_bot, ← Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal R).ne_top,
    Ideal.mem_iInf]
  intro n
  exact Ideal.pow_le_pow_right (Nat.le_succ n) (key n)

theorem lieMult_unif_loc {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R]
    [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [CharZero R] (t : SAB H (Sp R))
    (P : PELUnif (maximalIdeal R) t) (F : Type) [Field F] [IsAlgClosed F] (f : R →+* F) (hf : Function.Injective f)
    (τ : 𝓞 E →+* F) (N : ℕ) (hN : LieMult t.act (spMap f) τ N) :
    letI := H.starRing; ∃ n, LieMult (ofRingAct P.oD.onB.toRingAct) (spMap f) τ n ∧
      n + Module.finrank (𝓞 E) P.D.toPre.X = N := by
  classical
  letI := H.starRing
  haveI : CharZero F := ⟨fun a b h => Nat.cast_injective (R := R) (hf (by simpa using h))⟩
  have := P.U.smooth
  have : Smooth P.D.toPre.P.A.hom := P.D.toPre.P.smoothDim.smooth
  obtain ⟨g, v, hv⟩ := Chart.exists_isLieBasis t.G P.U.smooth
  obtain ⟨ρ, hρ⟩ := LieEigen.exists_action hv t.act
  obtain ⟨h, w, hw⟩ := Chart.exists_isLieBasis P.D.toPre.P.A this
  obtain ⟨ρB, hρB⟩ := LieEigen.exists_action hw (ofRingAct P.oD.onB.toRingAct)
  let b := Module.finBasis ℤ P.D.toPre.X
  have htr := trace_of_unif_loc P.U.toUnifPre P.lin hv hρ hw hρB b
  obtain ⟨v', ρ', hv', hρ', hM⟩ := ToricRank.exists_action_pullback hv hρ f
  obtain ⟨w', ρB', hw', hρB', hMB⟩ := ToricRank.exists_action_pullback hw hρB f
  let aG := t.act.pullback (spMap f) t.G
  let aB := (ofRingAct P.oD.onB.toRingAct).pullback (spMap f) P.D.toPre.P.A
  haveI := Module.Finite.of_basis (Lie.basis aG hv')
  haveI := Module.Finite.of_basis (Lie.basis aB hw')
  have tG : ∀ a, LinearMap.trace F (Lie aG) (Module.toModuleEnd F (Lie aG) a) = f (LinearMap.trace R _ (ρ a)) :=
    fun a => by rw [trace_map_eq]; exact trace_lie hv' aG a _ (fun c => by rw [← hM, hρ'])
  have tB : ∀ a, LinearMap.trace F (Lie aB) (Module.toModuleEnd F (Lie aB) a) = f (LinearMap.trace R _ (ρB a)) :=
    fun a => by rw [trace_map_eq]; exact trace_lie hw' aB a _ (fun c => by rw [← hMB, hρB'])
  let σ : (E →+* F) → 𝓞 E →+* F := fun i => i.comp (algebraMap (𝓞 E) E)
  have hinj : Function.Injective σ := fun i j hij =>
    IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) hij
  have hσ : IsSplitting σ := by
    simpa using isSplitting_of_isDomain hinj (NumberField.Embeddings.card E F) (RingHom.id F)
      (isUnit_discr_of_charZero F)
  obtain ⟨j, rfl⟩ : ∃ j, σ j = τ :=
    ⟨IsFractionRing.lift (injective_of_charZero τ), RingHom.ext fun x => IsFractionRing.lift_algebraMap (injective_of_charZero τ) x⟩
  have : Module.Finite (𝓞 E) P.D.toPre.X := .of_restrictScalars_finite ℤ _ _
  have he : ∀ {X : Over (Sp F)} [GrpObj X] [IsCommMonObj X] (a : OAct (𝓞 E) X),
      Lie.eig a (σ j) = eigenSub (Module.toModuleEnd F (Lie a)) (σ j) := fun a =>
    Submodule.ext fun v => by rw [mem_eigenSub]; rfl
  have hm := mult_eq hinj (fun i => Module.finrank F (eigenSub (Module.toModuleEnd F (Lie aG)) (σ i)))
    (fun i => Module.finrank F (eigenSub (Module.toModuleEnd F (Lie aB)) (σ i)))
    (Module.finrank (𝓞 E) P.D.toPre.X) (fun a => by
      have hT := trace_eq_sum hσ (torusRep (𝓞 E) P.D.toPre.X F) a
      simp only [fun i => finrank_eigenSub_torusRep (X := P.D.toPre.X) (σ i) (injective_of_charZero _)] at hT
      rw [← trace_eq_sum hσ, ← trace_eq_sum hσ, ← hT, tG, tB, htr, trace_torusRep b, map_add, map_intCast]) j
  rw [Lie.lieMult_iff_finrank (isLinearPullback_pullback _ (spMap f)), he] at hN
  refine ⟨_, ?_, hm.symm.trans hN.2⟩
  rw [Lie.lieMult_iff_finrank (isLinearPullback_pullback _ (spMap f)), he]
  exact ⟨inferInstance, rfl⟩

theorem bar_rt_neg {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) : H.bar H.rt = -H.rt := by
  have h1 : (H.bar H.rt) ^ 2 = H.rt ^ 2 := by rw [← map_pow, H.rt_sq]; simp
  refine (sq_eq_sq_iff_eq_or_eq_neg.mp h1).resolve_left fun h => ?_
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have h2 : starRingEnd ℂ (φ (H.rt : E)) = φ (H.rt : E) := by
    rw [← IsCMField.complexEmbedding_complexConj, ← H.bar_eq, h]
  obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.1 h2
  have h3 : φ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
    have := congrArg (φ.comp (algebraMap (𝓞 E) E)) H.rt_sq
    rw [map_pow, map_neg, map_natCast] at this
    exact this
  rw [hr] at h3
  have h4 : r ^ 2 = -(H.d : ℝ) := by exact_mod_cast h3
  have h5 : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  nlinarith [sq_nonneg r]

theorem exists_chars {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K]
    [IsAlgClosed K] [CharZero K] (δ : K) (hδ : δ ^ 2 = -(H.d : K)) :
    ∃ τ₁ τ₂ : 𝓞 E →+* K, τ₁ H.rt = δ ∧ τ₂ H.rt ≠ δ := by
  let e₀ : E →ₐ[ℚ] K := IsAlgClosed.lift
  let τ₀ : 𝓞 E →+* K := e₀.toRingHom.comp (algebraMap (𝓞 E) E)
  let τ' : 𝓞 E →+* K := τ₀.comp (H.bar : 𝓞 E →+* 𝓞 E)
  have h' : τ' H.rt = -τ₀ H.rt := by
    change τ₀ (H.bar H.rt) = _
    rw [bar_rt_neg, map_neg]
  have h0 : (τ₀ H.rt) ^ 2 = δ ^ 2 := by rw [← map_pow, H.rt_sq, map_neg, map_natCast, hδ]
  have hne : δ ≠ -δ := fun h => by
    have h2 : δ = 0 := by
      have : (2 : K) * δ = 0 := by linear_combination h
      exact (mul_eq_zero.1 this).resolve_left two_ne_zero
    rw [h2] at hδ
    have : (H.d : K) = 0 := by linear_combination hδ
    exact H.d_prime.ne_zero (by exact_mod_cast this)
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h0 with h | h
  · exact ⟨τ₀, τ', h, by rw [h', h]; exact fun e => hne e.symm⟩
  · exact ⟨τ', τ₀, by rw [h', h, neg_neg], by rw [h]; exact fun e => hne e.symm⟩

theorem finrank_le_min : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Z : GMod Xo c) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (ξ : Sp R ⟶ Z.X) (t : SAB H (Sp R)), SABMap t Z.t ξ → ∀ P : PELUnif (maximalIdeal R) t, IsCN R → IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → ((residue R).comp (Scheme.stalkClosedPointTo ξ).hom).FormallyUnramified → P.TorsionIso → Module.finrank (𝓞 E) P.D.toPre.X ≤ min D.p D.q := by
  intro E _ _ _ H D l Xo c Z R _ _ _ ξ t m P hCN hEt _ _
  obtain ⟨hNoeth, -, -, hChar⟩ := hCN
  haveI := hNoeth
  haveI := hChar
  haveI := c.fin
  haveI : NumberField c.F := {}
  obtain ⟨y, hy⟩ := DomFine.exists_generic_point (𝓞 c.F) c.F Z.X (Xo.XF c) Z.s Z.jQ Z.flat Z.proj Z.jQ_open
    Z.jQ_dense ξ hEt.1
  let K := AlgebraicClosure (FractionRing R)
  let f : R →+* K := (algebraMap (FractionRing R) K).comp (algebraMap R (FractionRing R))
  have hf : Function.Injective f :=
    (algebraMap (FractionRing R) K).injective.comp (IsFractionRing.injective R (FractionRing R))
  haveI : CharZero K := ⟨fun a b h => Nat.cast_injective (R := R) (hf (by simpa using h))⟩
  let x' : Sp K ⟶ Xo.XF c := spMap (algebraMap (FractionRing R) K) ≫ y
  have hx : x' ≫ Z.jQ ≫ pullback.fst _ _ = spMap f ≫ ξ := by
    rw [← DomFine.spMap_comp', Category.assoc, hy]
    rfl
  obtain ⟨β₀, hβ₀⟩ := Spec.map_surjective
    (x' ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Xo.s)
  have hβ : x' ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Xo.s = spMap β₀.hom :=
    hβ₀.symm
  have hdet := (Z.oF.geom K x' β₀.hom hβ).1
  have hr : (β₀.hom (baseKA l).ρ) ^ 2 = -(H.d : K) := by
    rw [← map_pow, (baseKA l).ρ_sq, map_neg, map_natCast]
  have bound : ∀ (τ : 𝓞 E →+* K) (N : ℕ), LieMult Z.oF.t.act x' τ N →
      Module.finrank (𝓞 E) P.D.toPre.X ≤ N := by
    intro τ N hN
    have h₅ := (GlobalTheory.lieMult_iff_of_isGrpPullback Z.m.cart Z.oF.t.act Z.t.act Z.m.act x' τ N).1 hN
    rw [hx] at h₅
    have h₆ := (GlobalTheory.lieMult_iff_of_isGrpPullback m.cart t.act Z.t.act m.act (spMap f) τ N).2 h₅
    obtain ⟨n, -, hn⟩ := lieMult_unif_loc H R t P K f hf τ N h₆
    omega
  obtain ⟨τ₁, τ₂, h₁, h₂⟩ := exists_chars H K _ hr
  exact le_min (bound τ₁ _ ((hdet τ₁).1 h₁)) (bound τ₂ _ ((hdet τ₂).2 h₂))

end GlobalTheory.CharRank
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeneratorExtendsPower
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.TraitGen

variable {X Y : Scheme.{0}}

theorem powPull_le (L : LB X) (m : ℕ) (χ : Y ⟶ X) (j : ((lbPow L m).pull χ).ι) :
    ((lbPow L m).pull χ).U j ≤ (L.pull χ).U (fun _ => j PUnit.unit PUnit.unit) := fun _ hy =>
  Set.mem_iInter.2 fun _ => Set.mem_iInter.1 (Set.mem_iInter.1 hy PUnit.unit) PUnit.unit

def powPull (L : LB X) (m : ℕ) (χ : Y ⟶ X) (e : LB.Gen (L.pull χ)) : LB.Gen ((lbPow L m).pull χ) where
  s j := res (powPull_le L m χ j) (e.s (fun _ => j PUnit.unit PUnit.unit)) ^ m

theorem gm_powPull {Z : Scheme.{0}} (L : LB X) (m : ℕ) (χ : Y ⟶ X) (e : LB.Gen (L.pull χ)) (r : Z ⟶ Y) (z : Z)
    (j : ((lbPow L m).pull χ).ι) (h : r z ∈ ((lbPow L m).pull χ).U j) :
    gm r z _ ((powPull L m χ e).s j) = gm r z _ (e.s (fun _ => j PUnit.unit PUnit.unit)) ^ m :=
  (map_pow _ _ _).trans (congrArg (· ^ m) (gm_res r z _ h _))

theorem gm_powPull_g {Z : Scheme.{0}} (L : LB X) (m : ℕ) (χ : Y ⟶ X) (r : Z ⟶ Y) (z : Z)
    (j j' : ((lbPow L m).pull χ).ι) (hj : r z ∈ ((lbPow L m).pull χ).U j)
    (hj' : r z ∈ ((lbPow L m).pull χ).U j') :
    gm r z _ (((lbPow L m).pull χ).g j j') =
      trF (L := L) (fun _ : PUnit => χ) (fun _ => 1) r z (fun _ => j PUnit.unit PUnit.unit)
        (fun _ => j' PUnit.unit PUnit.unit) ^ m := by
  refine (gm_pull_g (lbPow L m) χ r z j j' hj hj').trans ?_
  refine (gm_linComb L (fun _ : PUnit => 𝟙 X) (fun _ => (m : ℤ)) (r ≫ χ) z (j PUnit.unit) (j' PUnit.unit)
    (Set.mem_iInter.1 hj PUnit.unit) (Set.mem_iInter.1 hj' PUnit.unit)).trans ?_
  simp only [trF, Fintype.prod_unique, Category.comp_id, zpow_natCast, zpow_one]

theorem powPull_isGen (L : LB X) (m : ℕ) (χ : Y ⟶ X) (e : LB.Gen (L.pull χ)) (he : e.IsGen) :
    (powPull L m χ e).IsGen := by
  intro j j'
  refine unit_ext fun y hy => ?_
  have hj := powPull_le L m χ j hy.1
  have hj' := powPull_le L m χ j' hy.2
  have ht := gen_trans (L := L) (φ := fun _ : PUnit => χ) (ε := fun _ => 1) (t := e) he (𝟙 Y) y hj hj'
  refine (gm_res _ y _ hy _).trans ?_
  refine (gm_powPull L m χ e (𝟙 Y) y j hy.1).trans ?_
  refine Eq.trans ?_ (map_mul _ _ _).symm
  rw [gm_powPull_g L m χ (𝟙 Y) y j j' hy.1 hy.2, gm_res _ y _ hy, gm_powPull L m χ e (𝟙 Y) y j' hy.2, ← mul_pow]
  exact congrArg (· ^ m) ht

theorem val_powPull {Z : Scheme.{0}} (L : LB X) (m : ℕ) (χ : Y ⟶ X) (e : LB.Gen (L.pull χ)) (r : Z ⟶ Y) (z : Z)
    (J : (Z ⟶ X) → (lbPow L m).ι) (hJ : Good (lbPow L m) z J) :
    val (L := lbPow L m) (φ := fun _ : PUnit => χ) (ε := fun _ => 1) (powPull L m χ e) r z J =
      val (L := L) (φ := fun _ : PUnit => χ) (ε := fun _ => 1) e r z (fun ψ => J ψ PUnit.unit) ^ m :=
  gm_powPull L m χ e r z _ (hJ.mem (fun _ : PUnit => χ) r)

theorem extAt_lbPow (X : Scheme.{0}) (L : LB X) (R : Type) [CommRing R] [IsDomain R] (x : Sp (FractionRing R) ⟶ X)
    (e : LB.Gen (L.pull x)) (m : ℕ) (he : e.IsGen) (hx : GlobalTheory.TraitGen.ExtAt L x e) :
    ∃ e' : LB.Gen ((lbPow L m).pull x), e'.IsGen ∧ GlobalTheory.TraitGen.ExtAt (lbPow L m) x e' := by
  refine ⟨powPull L m x e, powPull_isGen L m x e he, ?_⟩
  intro V _ _ _ hV ψ gam hg χ hχ
  obtain ⟨e₁, h₁, hv⟩ := hx V hV ψ gam hg χ hχ
  refine ⟨powPull L m χ e₁, powPull_isGen L m χ e₁ h₁, fun z J hJ => ?_⟩
  rw [val_powPull L m x e _ z J hJ, val_powPull L m χ e₁ _ z J hJ]
  exact congrArg (· ^ m) (hv z (fun ψ => J ψ PUnit.unit) fun ψ => Set.mem_iInter.1 (hJ ψ) PUnit.unit)

end GlobalTheory.TraitGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeneratorExtendsTensor
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.TraitGen

variable {X Y Z : Scheme.{0}}

theorem tensGen_le₁ (A B : LB X) (f : Y ⟶ X) (j : PUnit → A.ι × B.ι) :
    ((GlobalTheory.CechPic.tens A B).pull f).U j ≤ (A.pull f).U (fun _ => (j PUnit.unit).1) :=
  fun _ hy => mem_pull.2 (mem_pull.1 hy).1

theorem tensGen_le₂ (A B : LB X) (f : Y ⟶ X) (j : PUnit → A.ι × B.ι) :
    ((GlobalTheory.CechPic.tens A B).pull f).U j ≤ (B.pull f).U (fun _ => (j PUnit.unit).2) :=
  fun _ hy => mem_pull.2 (mem_pull.1 hy).2

def tensGen (A B : LB X) (f : Y ⟶ X) (a : LB.Gen (A.pull f)) (b : LB.Gen (B.pull f)) :
    LB.Gen ((GlobalTheory.CechPic.tens A B).pull f) where
  s j := res (tensGen_le₁ A B f j) (a.s _) * res (tensGen_le₂ A B f j) (b.s _)

theorem gm_tensGen (A B : LB X) (f : Y ⟶ X) (a : LB.Gen (A.pull f)) (b : LB.Gen (B.pull f)) (r : Z ⟶ Y) (z : Z)
    (j : PUnit → A.ι × B.ι) (hj : r z ∈ ((GlobalTheory.CechPic.tens A B).pull f).U j) :
    gm r z _ ((tensGen A B f a b).s j) =
      gm r z ((A.pull f).U (fun _ => (j PUnit.unit).1)) (a.s _) *
      gm r z ((B.pull f).U (fun _ => (j PUnit.unit).2)) (b.s _) :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z _ hj _) (gm_res r z _ hj _))

theorem tensGen_isGen (A B : LB X) (f : Y ⟶ X) (a : LB.Gen (A.pull f)) (b : LB.Gen (B.pull f))
    (ha : a.IsGen) (hb : b.IsGen) : (tensGen A B f a b).IsGen := by
  refine (GlobalTheory.CechPic.isGen_iff_germ _).2 fun y i j hi hj => ?_
  have hi' := mem_pull.1 hi
  have hj' := mem_pull.1 hj
  have ai : y ∈ (A.pull f).U (fun _ => (i PUnit.unit).1) := mem_pull.2 hi'.1
  have aj : y ∈ (A.pull f).U (fun _ => (j PUnit.unit).1) := mem_pull.2 hj'.1
  have bi : y ∈ (B.pull f).U (fun _ => (i PUnit.unit).2) := mem_pull.2 hi'.2
  have bj : y ∈ (B.pull f).U (fun _ => (j PUnit.unit).2) := mem_pull.2 hj'.2
  rw [gm_tensGen A B f a b (𝟙 Y) y i hi, gm_tensGen A B f a b (𝟙 Y) y j hj,
    gm_pull_g (GlobalTheory.CechPic.tens A B) f (𝟙 Y) y i j hi hj, GlobalTheory.CechPic.gm_tens A B (𝟙 Y ≫ f) y _ _ hi' hj',
    (GlobalTheory.CechPic.isGen_iff_germ a).1 ha y _ _ ai aj,
    (GlobalTheory.CechPic.isGen_iff_germ b).1 hb y _ _ bi bj,
    gm_pull_g A f (𝟙 Y) y _ _ ai aj, gm_pull_g B f (𝟙 Y) y _ _ bi bj]
  exact mul_mul_mul_comm _ _ _ _

theorem val_tensGen (A B : LB X) (f : Y ⟶ X) (a : LB.Gen (A.pull f)) (b : LB.Gen (B.pull f)) (r : Z ⟶ Y) (z : Z)
    (J : (Z ⟶ X) → A.ι × B.ι) (hJ : Good (GlobalTheory.CechPic.tens A B) z J) :
    val (L := GlobalTheory.CechPic.tens A B) (φ := fun _ : PUnit => f) (ε := fun _ => 1) (tensGen A B f a b) r z J =
      val (L := A) (φ := fun _ : PUnit => f) (ε := fun _ => 1) a r z (fun ψ => (J ψ).1) *
      val (L := B) (φ := fun _ : PUnit => f) (ε := fun _ => 1) b r z (fun ψ => (J ψ).2) :=
  gm_tensGen A B f a b r z _ (hJ.mem _ r)

theorem exists_tens_extAt : ∀ (X : Scheme.{0}) (A B : LB X) (R : Type) [CommRing R] [IsDomain R] (x : Sp (FractionRing R) ⟶ X)
    (eA : LB.Gen (A.pull x)) (eB : LB.Gen (B.pull x)), eA.IsGen → eB.IsGen →
    GlobalTheory.TraitGen.ExtAt A x eA → GlobalTheory.TraitGen.ExtAt B x eB →
    ∃ e : LB.Gen ((GlobalTheory.CechPic.tens A B).pull x), e.IsGen ∧ GlobalTheory.TraitGen.ExtAt (GlobalTheory.CechPic.tens A B) x e := by
  intro X A B R _ _ x eA eB hA hB hxA hxB
  refine ⟨tensGen A B x eA eB, tensGen_isGen A B x eA eB hA hB, ?_⟩
  intro V _ _ _ hV ψ gam hg χ hχ
  obtain ⟨a', ha', hva⟩ := hxA V hV ψ gam hg χ hχ
  obtain ⟨b', hb', hvb⟩ := hxB V hV ψ gam hg χ hχ
  refine ⟨tensGen A B χ a' b', tensGen_isGen A B χ a' b' ha' hb', fun z J hJ => ?_⟩
  have hJA : Good A z (fun ψ => (J ψ).1) := fun ψ => (hJ ψ).1
  have hJB : Good B z (fun ψ => (J ψ).2) := fun ψ => (hJ ψ).2
  rw [val_tensGen A B x eA eB _ z J hJ, val_tensGen A B χ a' b' _ z J hJ, hva z _ hJA, hvb z _ hJB]

end GlobalTheory.TraitGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GenericFibreGroupFactorsUniversalCartesianStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericFibre_group_factors_universal_cartesian : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (yF : Sp ℂ ⟶ Xo.XF c) (x : KeyIn ℂ) (φ : x.P.A.left ⟶ Y.t.G.left), IsGrpPullback x.P.A Y.t.G (yF ≫ Y.j) φ → LBIso x.P.L (Y.t.PP.L.pull φ) → ∃ φ' : x.P.A.left ⟶ Y.oF.t.G.left, φ' ≫ Y.m.φ = φ ∧ φ' ≫ Y.oF.t.G.hom = x.P.A.hom ≫ yF ∧ IsGrpPullback x.P.A Xo.univ.t.G (yF ≫ pullback.fst _ _) (φ' ≫ Y.m0.toSABMap.φ) ∧ LBIso x.P.L (Xo.univ.t.PP.L.pull (φ' ≫ Y.m0.toSABMap.φ)) := by
  first | exact @GlobalTheory.GenericFibrePoint.fibre_map_univ | exact GlobalTheory.GenericFibrePoint.fibre_map_univ | (intros; apply GlobalTheory.GenericFibrePoint.fibre_map_univ <;> assumption)
end

