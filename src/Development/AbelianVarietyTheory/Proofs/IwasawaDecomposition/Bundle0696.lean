import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0046
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0567
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.CancelSecAct
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.TorusInj
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0023
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0043
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0042
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1122
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RamifiedRationalPrimesOfTupleBaseTupleEqEmpty
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToIntBijective
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0018
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0394
import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle0008
import Formalism.LocalToGlobal.LatticeGeometry.Inhabited
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0485

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorusCoordSecondPresentationWeightEq
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.WtSecond

lemma left_eq {S : Scheme.{0}} {A B C : Over S} {f : A ⟶ B} {g : B ⟶ C} {h : A ⟶ C} (H : f ≫ g = h) :
    f.left ≫ g.left = h.left :=
  (Over.comp_left _ _ _ f g).symm.trans (congrArg (fun k => k.left) H)

lemma appLE_congr {A B : Scheme.{0}} {f g : A ⟶ B} (h : f = g) {U : B.Opens} {W : A.Opens}
    (e : W ≤ f ⁻¹ᵁ U) (e' : W ≤ g ⁻¹ᵁ U) : f.appLE U W e = g.appLE U W e' := by
  subst h; rfl

section Core

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D D' : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

def chg (θ : WeightPf.Te D' I e ≅ WeightPf.Te D I e) :
    WeightPf.Te D I e ⊗ thickObj R I e G ⟶ WeightPf.Te D' I e ⊗ thickObj R I e G :=
  lift (fst (WeightPf.Te D I e) (thickObj R I e G) ≫ θ.inv) (snd (WeightPf.Te D I e) (thickObj R I e G))

lemma chg_fst (θ : WeightPf.Te D' I e ≅ WeightPf.Te D I e) :
    chg (G := G) θ ≫ fst (WeightPf.Te D' I e) (thickObj R I e G) =
      fst (WeightPf.Te D I e) (thickObj R I e G) ≫ θ.inv :=
  lift_fst _ _

lemma chg_snd (θ : WeightPf.Te D' I e ≅ WeightPf.Te D I e) :
    chg (G := G) θ ≫ snd (WeightPf.Te D' I e) (thickObj R I e G) = snd (WeightPf.Te D I e) (thickObj R I e G) :=
  lift_snd _ _

lemma chg_chg (θ : WeightPf.Te D' I e ≅ WeightPf.Te D I e) :
    chg (G := G) θ ≫ chg (G := G) θ.symm = 𝟙 _ := by
  refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
  · rw [Category.assoc, chg_fst, ← Category.assoc, chg_fst, Category.assoc, Iso.symm_inv, Iso.inv_hom_id,
      Category.comp_id, Category.id_comp]
  · rw [Category.assoc, chg_snd, chg_snd, Category.id_comp]

lemma chg_act (g : GtCoord I D e G) (g' : GtCoord I D' e G) (θ : WeightPf.Te D' I e ≅ WeightPf.Te D I e)
    (hi : θ.hom ≫ g.i = g'.i) : chg θ ≫ WeightPf.act g' = WeightPf.act g := by
  have hgi : θ.inv ≫ g'.i = g.i := (Iso.inv_comp_eq θ).2 hi.symm
  have h1 : chg θ ≫ lift (fst (WeightPf.Te D' I e) (thickObj R I e G) ≫ g'.i) (snd _ _) =
      lift (fst (WeightPf.Te D I e) (thickObj R I e G) ≫ g.i) (snd _ _) := by
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
    · rw [Category.assoc, lift_fst, lift_fst, ← Category.assoc, chg_fst, Category.assoc, hgi]
    · rw [Category.assoc, lift_snd, lift_snd, chg_snd]
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ μ[thickObj R I e G]) h1)

end Core

section Weight

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D D' : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

lemma chg_weight (g : GtCoord I D e G) (g' : GtCoord I D' e G) (θ : WeightPf.Te D' I e ≅ WeightPf.Te D I e)
    (hi : θ.hom ≫ g.i = g'.i) (x₀ : D'.X → D.X)
    (hx : ∀ x, θ.hom.left.appTop.hom (charUnit (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.X (x₀ x)).val =
      (charUnit (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D'.X x).val)
    (α' : D'.X) (jt : Fin 4 → D'.P.L.ι) (hjt : LB.Coh D'.P.L (D'.Oφ g'.pG α') jt)
    (W' : (WeightPf.Te D I e ⊗ thickObj R I e G).left.Opens) (hs : W' ≤ (snd (WeightPf.Te D I e) (thickObj R I e G)).left ⁻¹ᵁ LB.wchart D'.P.L (D'.Oφ g'.pG α') jt)
    (ha : W' ≤ (WeightPf.act g).left ⁻¹ᵁ LB.wchart D'.P.L (D'.Oφ g'.pG α') jt) :
    ((WeightPf.act g).left.appLE _ W' ha).hom ((g'.t α').s jt).val =
      ((WeightPf.Te D I e ⊗ thickObj R I e G).left.presheaf.map (homOfLE le_top).op).hom (TorusInj.chiP D.X (thickObj R I e G) (x₀ α')) *
      ((snd (WeightPf.Te D I e) (thickObj R I e G)).left.appLE _ W' hs).hom ((g'.t α').s jt).val := by
  have hΨs : chg (G := G) θ.symm ≫ (snd (WeightPf.Te D I e) (thickObj R I e G)) = (snd (WeightPf.Te D' I e) (thickObj R I e G)) := chg_snd θ.symm
  have hact' : chg (G := G) θ.symm ≫ WeightPf.act g = WeightPf.act g' :=
    chg_act g' g θ.symm (by rw [Iso.symm_hom, ← hi, Iso.inv_hom_id_assoc])
  have hs'' : (chg (G := G) θ.symm).left ⁻¹ᵁ W' ≤ (snd (WeightPf.Te D' I e) (thickObj R I e G)).left ⁻¹ᵁ LB.wchart D'.P.L (D'.Oφ g'.pG α') jt := by
    have h1 : (snd (WeightPf.Te D' I e) (thickObj R I e G)).left = (chg (G := G) θ.symm).left ≫ (snd (WeightPf.Te D I e) (thickObj R I e G)).left :=
      (left_eq hΨs).symm
    rw [h1, Scheme.Hom.comp_preimage]
    exact fun y hy => hs hy
  have ha'' : (chg (G := G) θ.symm).left ⁻¹ᵁ W' ≤ (WeightPf.act g').left ⁻¹ᵁ LB.wchart D'.P.L (D'.Oφ g'.pG α') jt := by
    have h1 : (WeightPf.act g').left = (chg (G := G) θ.symm).left ≫ (WeightPf.act g).left :=
      (left_eq hact').symm
    rw [h1, Scheme.Hom.comp_preimage]
    exact fun y hy => ha hy
  have hΦW : W' ≤ (chg (G := G) θ).left ⁻¹ᵁ ((chg (G := G) θ.symm).left ⁻¹ᵁ W') := by
    have h2 : (chg (G := G) θ).left ≫ (chg (G := G) θ.symm).left = 𝟙 _ :=
      (left_eq (chg_chg θ)).trans (Over.id_left _)
    rw [← Scheme.Hom.comp_preimage, h2]
    exact fun y hy => hy
  have key := WeightPf.t_act g' α' jt hjt _ hs'' ha''
  have k2 := congrArg ((chg (G := G) θ).left.appLE _ W' hΦW).hom key
  have e0 : (chg (G := G) θ).left ≫ (WeightPf.act g').left = (WeightPf.act g).left :=
    left_eq (chg_act g g' θ hi)
  have e1 : (chg (G := G) θ).left ≫ (snd (WeightPf.Te D' I e) (thickObj R I e G)).left = (snd (WeightPf.Te D I e) (thickObj R I e G)).left :=
    left_eq (chg_snd θ)
  have L : ∀ x, ((chg (G := G) θ).left.appLE _ W' hΦW).hom (((WeightPf.act g').left.appLE _ _ ha'').hom x) =
      ((WeightPf.act g).left.appLE _ W' ha).hom x := by
    intro x
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
    exact congrArg (fun φ => φ.hom x) (appLE_congr e0 _ ha)
  have S : ∀ x, ((chg (G := G) θ).left.appLE _ W' hΦW).hom (((snd (WeightPf.Te D' I e) (thickObj R I e G)).left.appLE _ _ hs'').hom x) =
      ((snd (WeightPf.Te D I e) (thickObj R I e G)).left.appLE _ W' hs).hom x := by
    intro x
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
    exact congrArg (fun φ => φ.hom x) (appLE_congr e1 _ hs)
  have hres : ∀ x, ((chg (G := G) θ).left.appLE _ W' hΦW).hom (((WeightPf.Te D' I e ⊗ thickObj R I e G).left.presheaf.map (homOfLE le_top).op).hom x) =
      ((WeightPf.Te D I e ⊗ thickObj R I e G).left.presheaf.map (homOfLE le_top).op).hom ((chg (G := G) θ).left.appTop.hom x) := by
    intro x
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE, Scheme.Hom.appTop,
      Scheme.Hom.app_eq_appLE]
    first | erw [Scheme.Hom.appLE_map] | rfl
  have hchi : (chg (G := G) θ).left.appTop.hom (TorusInj.chiP D'.X (thickObj R I e G) α') =
      TorusInj.chiP D.X (thickObj R I e G) (x₀ α') := by
    unfold TorusInj.chiP
    rw [← SplitTorusHom.appTop_comp, chg_fst, SplitTorusHom.appTop_comp, ← hx α',
      ← SplitTorusHom.appTop_comp θ.inv θ.hom, Iso.inv_hom_id, SplitTorusHom.appTop_id]
  rw [map_mul] at k2
  exact (L _).symm.trans (k2.trans (congrArg₂ (· * ·) ((hres _).trans (congrArg _ hchi)) (S _)))

end Weight

theorem wt_second : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G) (e : ℕ) (xe : D'.toPre.X ≃+ D.toPre.X), GlobalTheory.CharAgree.Match (U.gt e) (U'.gt e) xe → ∀ (α' : D'.toPre.X) (jt : Fin 4 → D'.toPre.P.L.ι), LB.Coh D'.toPre.P.L (D'.toPre.Oφ (U'.gt e).pG α') jt → ∀ (W' : (WeightPf.Te D.toPre (maximalIdeal R) e ⊗ thickObj R (maximalIdeal R) e G).left.Opens) (hs : W' ≤ (snd (WeightPf.Te D.toPre (maximalIdeal R) e) (thickObj R (maximalIdeal R) e G)).left ⁻¹ᵁ LB.wchart D'.toPre.P.L (D'.toPre.Oφ (U'.gt e).pG α') jt) (ha : W' ≤ (WeightPf.act (U.gt e)).left ⁻¹ᵁ LB.wchart D'.toPre.P.L (D'.toPre.Oφ (U'.gt e).pG α') jt), ((WeightPf.act (U.gt e)).left.appLE _ W' ha).hom (((U'.gt e).t α').s jt).val = ((WeightPf.Te D.toPre (maximalIdeal R) e ⊗ thickObj R (maximalIdeal R) e G).left.presheaf.map (homOfLE le_top).op).hom (TorusInj.chiP D.toPre.X (thickObj R (maximalIdeal R) e G) (xe α')) * ((snd (WeightPf.Te D.toPre (maximalIdeal R) e) (thickObj R (maximalIdeal R) e G)).left.appLE _ W' hs).hom (((U'.gt e).t α').s jt).val := by
  intro R _ _ _ hCN G _ _ hG D D' A A' U U' e xe hM α' jt hjt W' hs ha
  have hR := admissibleBase_of_completeNormalLocalCharZero hCN
  obtain ⟨hN, -, -, -⟩ := hR
  have hI : maximalIdeal R ≠ ⊤ := (maximalIdeal.isMaximal R).ne_top
  obtain ⟨θ, hθ, hi⟩ := CharAgree.exists_torus_iso hI (U.gt e) (U'.gt e)
  have := CharAgree.connected_thick hI e
  obtain ⟨x₀, hx⟩ := exists_addEquiv_of_splitTorus_iso _ D.toPre.X D'.toPre.X θ hθ

  have hM₀ : CharAgree.Match (U.gt e) (U'.gt e) x₀ := by
    intro Z r z J J' hJ hJ' _ h' x
    let FinalForm : Over (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1)))) :=
      Over.mk (r ≫ (thickObj R (maximalIdeal R) e G).hom)
    let a : FinalForm ⟶ thickObj R (maximalIdeal R) e G := Over.homMk r rfl
    let τ := (U'.gt e).isKernel.lift a (toUnit _) ((CharAgree.comp_q_eq_one_iff (U'.gt e) a).2 h')
    have hτ : τ ≫ (U'.gt e).i = a := (U'.gt e).isKernel.lift_fst _ _ _
    have hτ' : (τ ≫ θ.hom) ≫ (U.gt e).i = a := by rw [Category.assoc, hi, hτ]
    have k := (TorusCoord.val_torus_point_and_translate R (maximalIdeal R) D.toPre e G (U.gt e) FinalForm
      (τ ≫ θ.hom) 1 z J hJ (x₀ x)).1
    have k' := (TorusCoord.val_torus_point_and_translate R (maximalIdeal R) D'.toPre e G (U'.gt e) FinalForm
      τ 1 z J' hJ' x).1
    rw [hτ'] at k
    rw [hτ] at k'
    refine k.trans (Eq.trans (Units.ext ?_) k'.symm)
    rw [gm_val _ _ ⊤ trivial, gm_val _ _ ⊤ trivial]
    refine congrArg (FinalForm.left.presheaf.germ ⊤ z trivial).hom ?_
    exact (SplitTorusHom.appTop_comp τ θ.hom _).trans (congrArg τ.left.appTop.hom (hx x))
  have hxe : (xe : D'.toPre.X → D.toPre.X) = x₀ := CharAgree.match_unique hI _ _ hM hM₀
  rw [congrFun hxe α']
  exact chg_weight (U.gt e) (U'.gt e) θ hi x₀ hx α' jt hjt W' hs ha

end GlobalTheory.WtSecond
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupPinsOfMuIsW
section
noncomputable section

namespace GlobalTheory.Mem.Top.DivRec

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links GlobalTheory.Mem.R3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3}
  {cG : G0 R.Pg D.R.r ≃* G0g D.nd} {X0 : BaseLevelRowSide D} {Y : Read (A3 := A3) R.toRealDat F.lv2 X0}

theorem nonempty_ix (hH : Holds R F) : Nonempty A3.fam3.base3.Ix :=
  GlobalTheory.Div.nonempty_ix_of_pos A3 F.P0 F.ψ0 (R.toCx3 F).zs hH.ok hH.prim.block (hH.prim.pos false)

open Classical in

def labOf (Z : ReadL R F X0 Y) (hH : Holds R F) (σ : D.what₂.FT) : A3.fam3.base3.Ix :=
  if h : ∃ c, Bl.OverIx Z σ c then h.choose else (nonempty_ix hH).some

theorem overIx_labOf (Z : ReadL R F X0 Y) (hH : Holds R F) (σ : D.what₂.FT) (h : ∃ c, Bl.OverIx Z σ c) :
    Bl.OverIx Z σ (labOf Z hH σ) := by
  rw [labOf, dif_pos h]
  exact h.choose_spec

open Classical in

def logLamOf (Z : ReadL R F X0 Y) (hH : Holds R F) (j : ℕ) (σ : D.what₂.FT) (e : D.what₂.LL →+* ℂ) : ℝ :=
  if e = D.what₂.embLL then Real.log (D.what₂.lamP D.what₂.mu0 j σ)
  else if h : j - 1 < D.R.m then
    if D.what₂.isot j σ = ⊥ then 0 else Real.log ((s0Of R F).lam ⟨j - 1, h⟩ A3.A.μ0 (labOf Z hH σ) (InfinitePlace.mk e))
  else 0

theorem lamAre_of_eq (Z : ReadL R F X0 Y) (hH : Holds R F) (Xd : DivX D) (hX : Xd.logLam = logLamOf Z hH) : Bl.LamAre Z Xd := by
  refine ⟨labOf Z hH, overIx_labOf Z hH, fun i σ e he => ?_⟩
  have h : (i : ℕ) + 1 - 1 < D.R.m := i.2
  rw [hX, logLamOf, if_neg he, dif_pos h]
  exact ⟨fun h0 => if_neg h0, fun h0 => if_pos h0⟩

def x0 (Z : ReadL R F X0 Y) (hP : Pins R F cG) (hH : Holds R F) : DivX D where
  geo := Formalism.BasicNotions.Examples₂.geoExample _
  Lev := Empty
  levPr := fun κ => κ.elim
  shv := fun _ κ => κ.elim
  shv_N := fun _ κ => κ.elim
  shv_lev := fun _ κ => κ.elim
  PlP := fun p _ => Formalism.L2.Geo.PlL D p
  plpFin := fun p _ => Formalism.L2.Geo.finPl D p
  plpNe := fun p _ => Formalism.L2.Geo.plL_ne D p
  wtP := fun p _ => Formalism.L2.Geo.wtL D p
  divisorWeight_nonneg := fun p _ => Formalism.L2.Geo.wtL_nonneg D p
  divisorWeight_sum := fun p _ => Formalism.L2.Geo.wtL_sum D p
  plP := fun p _ => Formalism.BasicNotions.Examples₂.PlOver.plLEquiv D p
  divisorWeight_def := fun p _ la => Formalism.BasicNotions.Examples₂.PlOver.wtLog_eq D p la
  jC := fun p _ _ => (Formalism.BasicNotions.Examples₂.teich_Om_equiv p).some.toRingHom.comp (algebraMap (DV.KW p) (Formalism.BasicNotions.Examples₂.TeichOm p))
  Mp := fun _ κ => κ.elim
  md := fun _ κ => κ.elim
  vdd := fun _ _ => 0
  vdd_unram := fun _ _ _ => rfl
  phiFr_unram := fun _ κ => κ.elim
  vdd_nonneg := fun _ _ => le_rfl
  CurveM := fun _ κ => κ.elim
  degM := fun _ κ => κ.elim
  htMdl := fun _ κ => κ.elim
  htCurve := fun _ κ => κ.elim
  htCurve_deg := fun _ κ => κ.elim
  MjH := mjH Z
  MjH_good := mjH_good Z hH
  jM := jM Z
  jM_basis := jM_basis Z hH
  jM_lat := jM_lat Z hP hH
  MjLat_sub := mjLat_sub Z hP hH
  jM_metric := jM_metric Z hH
  Qp := fun _ => ∅
  degreeZero_partial_set_empty := rfl
  Qp_muAt := fun _ => Finset.notMem_empty _
  Qp_g := fun _ _ _ => Finset.notMem_empty _
  QPl := fun _ => Empty
  qv := fun _ v => v.elim
  qv_gt := fun _ v => v.elim
  qv_char := fun _ _ v => v.elim
  nu := fun _ v => v.elim
  nu_ne := fun _ v => v.elim
  nu_abs := fun _ v => v.elim
  ZQ := fun _ v => v.elim
  quotientLocalValueFirst := fun _ v => v.elim
  typeDim := fun _ v => v.elim
  Comp := fun _ => Empty
  degHH := fun _ c => c.elim
  Yv := fun _ c => c.elim
  Ybd := fun _ c => c.elim
  Lw := fun _ c => c.elim
  iMj := fun _ c => c.elim
  iMj_mem := fun _ c => c.elim
  logLam := logLamOf Z hH
  logLam_base := fun _ _ => if_pos rfl
  kapR := fun _ => kapSharp D
  kapR_pos := fun _ => RowSide.kapOf_pos _ _
  kapR_conj := fun _ => rfl
  Surf := Empty
  surfCh2 := fun _ => 0
  surfDegOm := fun _ => 0
  SurfFp := Empty
  surfFpCh2 := fun _ => 0

end GlobalTheory.Mem.Top.DivRec

end

noncomputable section

namespace GlobalTheory.Mem.Top.DivRec

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl
  NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem tupPins_of_muIsW (X : Stages) (f : Fr X.B.toPre) (T : TwDat X.B) (Wt : Set X.B.places.Pl)
    (xi : X.C.Tup → HChar X.B.host.E) (h : V4.MuIsW X f T Wt xi) {C : CharFrame X.toD7} {nch : NChoice X.toD7}
    (tp : TupTied X.toD7 C nch) (hxi : tp.xi = xi) : GlobalTheory.Mem.HD.TupPins tp := by
  refine ⟨fun μ v hv => ?_, fun w v hv => ?_⟩
  · rw [hxi] at hv
    obtain ⟨h1, h2, h3, h4⟩ :=
      (GlobalTheory.Mem.HD.TupPin.isTwist_types X.B f T (xi μ) (h.range ▸ Set.mem_range_self μ)).2.2.2 v hv
    exact ⟨h1, h2, h3, fun k hk => h4
      ⟨k, Examples₂.PlacesToy.prime_mem_unique v (X.B.host.g_prime k) h2 hk (Ideal.absNorm_mem _)⟩⟩
  · rw [hxi]
    show (xi (X.W.muAt w)).UnrAt v
    by_cases hw : w ∈ Wt
    · rw [h.on w hw, h.tw w]
      exact GlobalTheory.Mem.HD.TupPin.xiTw_unr X.B f T w v hv
    · rw [h.off w hw, h.mu0]
      exact fun x _ => HChar.loc_one _ _

open Formalism.L2.Rows Formalism.L2.Geo GlobalTheory.GeoGraft GlobalTheory.GeoModel in

theorem geoOver_stages (X : Stages) (X₀ : DivX X.toD7) : GeoOver (fun _ => True) X₀ := by
  let D := X.toD7
  let eO : 𝓞 X.B.Ks ≃+* D.what₂.O := RingEquiv.refl _
  let kL : X.B.Ks →+* D.what₂.LL := X.B.Ks.val.toRingHom
  have hk : ∀ x : 𝓞 X.B.Ks, kL (x : X.B.Ks) = D.what₂.OtoLL (eO x) := fun _ => rfl
  let jc : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ) :=
    fun p _ la => Classical.choose (GlobalTheory.WittFracPlace.exists_jcPin D p la)
  have hjc : ComplexEmbeddingsCompatible jc := GlobalTheory.ShFam.PinPlace.pinned_tiedFor D jc
    (fun p _ la => Classical.choose_spec (GlobalTheory.WittFracPlace.exists_jcPin D p la))
  refine ⟨divXFl D jc X₀, fun _ _ => True, ⟨divXFl D jc X₀, (divXFl D jc X₀).iMj, (divXFl D jc X₀).iMj_mem, rfl⟩,
    ⟨famFlJ D jc X.B.Ks eO kL hk, fun p _ => Equiv.refl _, fun _ _ _ => Equiv.refl _, tiedX_fl D jc X₀, hjc,
      fun _ _ _ _ _ => trivial, isoInv_famFlJ D jc X.B.Ks eO kL hk, levInTie_famFlJ D jc X.B.Ks eO kL hk⟩, trivial⟩

variable {B : Base} {f : Fr B.toPre} {T : TwDat B}

theorem qpIs_qpSet (w : ColW B f T) (pin : ColPin w) (Z : w.Lt) {nch : NChoice (w.D Z)}
    (tp : TupTied (w.D Z) (TC.cf w.I w.l Z) nch) (hxi : tp.xi = w.I.xi) (hp : GlobalTheory.Mem.HD.TupPins tp) :
    TC.QpIs w.I (GlobalTheory.Mem.HD.ReQ.qpSet tp) := GlobalTheory.Mem.Top.Bl.QpIsOf.qpIs_qpSet w pin Z tp hxi hp

theorem mjAre_x0 {K : Ctx} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl} {p0 : BaseLevelRowSide (w.D Z)} (t : RowsT K w Z Wt p0) :
    MjAre t.r.Z (x0 t.r.Z t.r.z.pins t.r.intersectionNumber_baseChange) :=
  GlobalTheory.Mem.R3.exists_mjHTie t.r.Z _ rfl HEq.rfl

theorem exists_divT {𝒮 : Slots} {K : Ctx} (w : ColW B f T) (pin : ColPin w) (Z : w.Lt) (l : Lv4 𝒮 K w Z) :
    ∃ Y : DivX (w.D Z), Nonempty (DivT l.n Y) ∧ MjAre l.what₂.r.Z Y ∧ (∀ σ, Y.kapR σ = kapSharp (w.D Z)) ∧
      LamAre l.what₂.r.Z Y := by
  have hp : GlobalTheory.Mem.HD.TupPins l.n.tp := tupPins_of_muIsW (w.st Z) f T l.Wt w.I.xi l.what₂.mu l.n.tp l.n.xi
  let X₁ := x0 l.what₂.r.Z l.what₂.r.z.pins l.what₂.r.intersectionNumber_baseChange
  let X₂ := GlobalTheory.Mem.HD.ReQ.reQ l.n.tp hp w.I.sel pin.above X₁
  obtain ⟨X, inK, ⟨Xg, iM, hiM, rfl⟩, hG, -⟩ := geoOver_stages (w.st Z) X₂
  let c := GlobalTheory.Mem.HD.ReQ.reducedDivisorCharacter l.n.tp hp w.I.sel pin.above X₁
  obtain ⟨h1, h2⟩ := GlobalTheory.Mem.HD.ReQ.reLoc l.n.tp hp w.I.sel pin.above X₁
  let chr : DivisorCharacterCompatibility (w.D Z) (TC.cf w.I w.l Z) _ l.n.tp (GlobalTheory.GeoGraft.graft Xg X₂ iM hiM) := ⟨c.Qp_iff, c.eQPl, c.qv_eq⟩
  refine ⟨GlobalTheory.GeoGraft.graft Xg X₂ iM hiM,
    ⟨{ Qp := qpIs_qpSet w pin Z l.n.tp l.n.xi hp, chr := chr, loc := ⟨h1, ?_⟩, inK := inK, geo := hG }⟩,
    GlobalTheory.Mem.R3.exists_mjHTie l.what₂.r.Z _ rfl HEq.rfl, fun _ => rfl,
    lamAre_of_eq l.what₂.r.Z l.what₂.r.intersectionNumber_baseChange _ rfl⟩
  exact ⟨h2.qv_eq, h2.deg1, h2.ram, h2.off_g, h2.nu_eq, h2.typeDim_eq, h2.ZQ_eq, h2.quotientLocalValueFirst_eq⟩

theorem lamAre_x0 {K : Ctx} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl} {p0 : BaseLevelRowSide (w.D Z)} (t : RowsT K w Z Wt p0) :
    LamAre t.r.Z (x0 t.r.Z t.r.z.pins t.r.intersectionNumber_baseChange) :=
  lamAre_of_eq t.r.Z t.r.intersectionNumber_baseChange _ rfl

theorem lamAre_heq {K : Ctx} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl} {p0 p0' : BaseLevelRowSide (w.D Z)} {t : RowsT K w Z Wt p0}
    {t' : RowsT K w Z Wt p0'} (e : p0 = p0') (h : HEq t t') {X : DivX (w.D Z)} (hX : LamAre t'.r.Z X) : LamAre t.r.Z X := by
  subst e
  obtain rfl := eq_of_heq h
  exact hX

theorem divEx_prov (𝒮 : Slots) (hOx : 𝒮.Ox = OX anyGeometry) : DivEx 𝒮 :=
  StepW.of_all fun _ _ _ _ w _ _ hpin Z l =>
    let ⟨Y, h1, h2, h3, h4⟩ := exists_divT w hpin.some Z l
    ⟨Y, h1, h2, h3, fun O t hX hp ht => by
      rw [hOx]
      exact ⟨⟨trivial, lamAre_heq hp ht (hX ▸ h4)⟩⟩⟩

theorem divEx_of_ox : GlobalTheory.NT.RayField → GlobalTheory.Published.PrincipalIdealSt → GlobalTheory.Published.CMCurveGoodOutsidePrimeSt → ∀ 𝒮 : Slots,
    𝒮.Ox = OX anyGeometry → DivEx 𝒮 :=
  fun _ _ _ 𝒮 hOx => divEx_prov 𝒮 hOx

end GlobalTheory.Mem.Top.DivRec

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightTwoFactorSqValuesCorrespond
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PsiCompare

open ReciprocityTheory.ChartRestriction.G.DVR

theorem prod_famB_wtTwo {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {T : Over (Spec (CommRingCat.of R))}
    (y : T ⟶ D.P.A) (α : D.X) {U : Type} [CommGroup U] (h : (T.left ⟶ D.P.A.left) → U) :
    ∏ i, h (y.left ≫ D.famφB α i) ^ DegPre.famε 2 i =
      h y.left * h (y * cP D T α).left * (h (cP D T α).left)⁻¹ * h (1 : T ⟶ D.P.A).left := by
  have a₀ : y.left ≫ D.famφB α 0 = y.left := Category.comp_id _
  have a₁ : y.left ≫ D.famφB α 1 = (y * cP D T α).left := congrArg (fun z => z.left)
    ((MonObj.comp_mul y (𝟙 _) (cP D _ α)).trans (congrArg₂ (· * ·) (Category.comp_id _) (comp_cP D _ α)))
  have a₂ : y.left ≫ D.famφB α 2 = (cP D T α).left := congrArg (fun z => z.left) (comp_cP D y α)
  have a₃ : y.left ≫ D.famφB α 3 = (1 : T ⟶ D.P.A).left :=
    congrArg (fun z : _ ⟶ D.P.A => z.left) (MonObj.comp_one (M := D.P.A) y)
  rw [Fin.prod_univ_four, a₀, a₁, a₂, a₃]
  show _ ^ (((2 : ℕ) : ℤ) - 1) * _ ^ (1 : ℤ) * _ ^ (-1 : ℤ) * _ ^ (1 : ℤ) = _
  norm_num

theorem sq_unit_cancel {A : Type} [CommRing A] [IsDomain A] {s s' F₁ F₁' : A}
    {θ θ' V V' ωx ωam ωm2 ω1 ωa ωm : Aˣ} (hs : s ≠ 0)
    (h₁ : F₁ = s * (θ * V).val) (h₂ : F₁' = s' * (θ' * V').val)
    (h₃ : F₁ ^ 2 = (ωx * ωam * ωm2⁻¹ * ω1).val * F₁' ^ 2)
    (h₄ : s ^ 2 = (ωa * ωa * ω1⁻¹ * ω1).val * s' ^ 2)
    (h₅ : θ ^ 2 = ωam * ωm2⁻¹ * ωa⁻¹ * ωa⁻¹ * ωm * ωm * ωx * ω1⁻¹ * θ' ^ 2) :
    V' ^ 2 = (ωm * ω1⁻¹) ^ 2 * V ^ 2 := by
  have hs' : s' ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero, MulZeroClass.mul_zero] at h₄
    exact hs (pow_eq_zero_iff two_ne_zero |>.1 h₄)
  have E : ωa * ωa * ω1⁻¹ * ω1 * (θ * V) ^ 2 = ωx * ωam * ωm2⁻¹ * ω1 * (θ' * V') ^ 2 :=
    Units.ext (mul_left_cancel₀ (pow_ne_zero 2 hs') (by
      rw [h₁, h₂] at h₃
      simp only [Units.val_mul, Units.val_pow_eq_pow_val] at h₃ h₄ ⊢
      linear_combination h₃ - ((θ : A) * V) ^ 2 * h₄))
  apply Additive.ofMul.injective
  have E' := congrArg Additive.ofMul E
  have h₅' := congrArg Additive.ofMul h₅
  simp only [ofMul_mul, ofMul_inv, ofMul_pow] at E' h₅' ⊢
  linear_combination (norm := abel) h₅' - E'

end GlobalTheory.PsiCompare

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.PsiCompare in

theorem GlobalTheory.PsiCompare.famMult_sq_corr : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], ∀ (D D' : DegData R (maximalIdeal R)), ∀ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)), IsMonHom Φ.hom → ∀ xe : D'.toPre.X ≃+ D.toPre.X, (∀ x : D'.toPre.X, D'.toPre.c (2 • x) ≫ Φ.hom = D.toPre.c (xe (2 • x))) → ∀ (f : ∀ α : D.toPre.X, D.toPre.SecB 2 α) (f' : ∀ α : D'.toPre.X, D'.toPre.SecB 2 α), (∀ (mu α : D.toPre.X) (T : Over (Sp R)) (κ : T ⟶ TF (R := R) (FractionRing R)) (y : T ⟶ D.toPre.P.A) (z : T.left) (J : (T.left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → sval (f (α + 2 • mu)) y.left z J = sval (f α) (y * ReciprocityTheory.ChartRestriction.G.DVR.cP D.toPre T mu).left z J * (ReciprocityTheory.ChartRestriction.G.DVR.uVal D.toPre (FractionRing R) 2 α (ReciprocityTheory.ChartRestriction.G.DVR.cP D.toPre _ mu) (CartesianMonoidalCategory.lift κ y) z J * val (DegPre.famMult D.toPre (FractionRing R) 2 mu α) κ.left z J).val) → (∀ (mu α : D'.toPre.X) (T : Over (Sp R)) (κ : T ⟶ TF (R := R) (FractionRing R)) (y : T ⟶ D'.toPre.P.A) (z : T.left) (J : (T.left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Geo.Tor.Good D'.toPre.P.L z J → sval (f' (α + 2 • mu)) y.left z J = sval (f' α) (y * ReciprocityTheory.ChartRestriction.G.DVR.cP D'.toPre T mu).left z J * (ReciprocityTheory.ChartRestriction.G.DVR.uVal D'.toPre (FractionRing R) 2 α (ReciprocityTheory.ChartRestriction.G.DVR.cP D'.toPre _ mu) (CartesianMonoidalCategory.lift κ y) z J * val (DegPre.famMult D'.toPre (FractionRing R) 2 mu α) κ.left z J).val) → (∀ (β : D'.toPre.X) (Z : Scheme.{0}) (ρ : Z ⟶ D'.toPre.P.A.left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D'.toPre.P.L z J' → sval (f (xe (2 • β))) (ρ ≫ Φ.hom.left) z J ^ 2 = (∏ κ, ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (ρ ≫ D'.toPre.famφB (2 • β) κ) ^ DegPre.famε 2 κ).val * sval (f' (2 • β)) ρ z J' ^ 2) → (∀ (T : Over (Sp R)) (z : T.left) (J : (T.left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (T.left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D'.toPre.P.L z J' → ∀ (Ω : (T ⟶ D'.toPre.P.A) → (T.left.presheaf.stalk z)ˣ), Ω = (fun x => ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) x.left) → ∀ (a b c : T ⟶ D'.toPre.P.A), cubV D.toPre.cub z J (a ≫ Φ.hom) (b ≫ Φ.hom) (c ≫ Φ.hom) ^ 2 = Ω (a * b * c) * (Ω (a * b))⁻¹ * (Ω (a * c))⁻¹ * (Ω (b * c))⁻¹ * Ω a * Ω b * Ω c * (Ω 1)⁻¹ * cubV D'.toPre.cub z J' a b c ^ 2) → ∀ (y : D'.toPre.X) (z : (DegPre.BF D.toPre (FractionRing R)).left) (J : ((DegPre.BF D.toPre (FractionRing R)).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : ((DegPre.BF D.toPre (FractionRing R)).left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D'.toPre.P.L z J' → IsDomain ((DegPre.BF D.toPre (FractionRing R)).left.presheaf.stalk z) → sval (f 0) (DegPre.prB D.toPre (FractionRing R)).left z J ≠ 0 → val (DegPre.famMult D'.toPre (FractionRing R) 2 (2 • y) 0) (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left z J' ^ 2 = (ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (ReciprocityTheory.ChartRestriction.G.DVR.cP D'.toPre (DegPre.BF D.toPre (FractionRing R)) (2 • y)).left * (ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (1 : (DegPre.BF D.toPre (FractionRing R)) ⟶ D'.toPre.P.A).left)⁻¹) ^ 2 * val (DegPre.famMult D.toPre (FractionRing R) 2 (xe (2 • y)) 0) (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left z J ^ 2 := by
  intro R _ _ _ D D' Φ w hΦ xe hc f f' hf hf' hcorr hcub y z J J' hJ hJ' hdom h0
  haveI := hΦ
  haveI := hdom
  set κ : DegPre.BF D.toPre (FractionRing R) ⟶ TF (R := R) (FractionRing R) := fst (TF (R := R) (FractionRing R)) D.toPre.P.A with hκ
  set pB : DegPre.BF D.toPre (FractionRing R) ⟶ D.toPre.P.A := DegPre.prB D.toPre (FractionRing R) with hpB
  set m' : DegPre.BF D.toPre (FractionRing R) ⟶ D'.toPre.P.A := cP D'.toPre (DegPre.BF D.toPre (FractionRing R)) (2 • y) with hm'
  set a : DegPre.BF D.toPre (FractionRing R) ⟶ D'.toPre.P.A := pB ≫ Φ.inv with ha
  set x' : DegPre.BF D.toPre (FractionRing R) ⟶ D'.toPre.P.A := a * m'⁻¹ with hx'
  let T := DegPre.BF D.toPre (FractionRing R)
  have hxm : x' * m' = a := inv_mul_cancel_right _ _
  have hmΦ : m' ≫ Φ.hom = cP D.toPre T (xe (2 • y)) := cP_comp Φ.hom (hc y) T
  have haΦ : a ≫ Φ.hom = pB := by rw [ha, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hx'Φ : (x' ≫ Φ.hom) * cP D.toPre T (xe (2 • y)) = pB := by
    rw [← hmΦ, ← MonObj.mul_comp, hxm, haΦ]

  have e₁ := hf (xe (2 • y)) 0 T κ (x' ≫ Φ.hom) z J hJ
  have u₁ : uVal D.toPre (FractionRing R) 2 0 (cP D.toPre _ (xe (2 • y))) (lift κ (x' ≫ Φ.hom)) z J =
      cubV D.toPre.cub z J (cP D.toPre T (xe (2 • y))) (cP D.toPre T (xe (2 • y))) (x' ≫ Φ.hom) := by
    have C := isCub_cubV D.toPre.cub hJ
    have ρ₂ : lift κ (x' ≫ Φ.hom) ≫ DegPre.prB D.toPre (FractionRing R) = x' ≫ Φ.hom := lift_snd _ _
    rw [uVal, cPoint_zero, cubN, ρ₂, comp_cP, comp_cP]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, pow_zero, pow_one, _root_.one_mul,
      _root_.mul_one, C.face, inv_one]
    rfl
  rw [u₁, hx'Φ, zero_add] at e₁

  have e₂ := hf' (2 • y) 0 T κ x' z J' hJ'
  have u₂ : uVal D'.toPre (FractionRing R) 2 0 (cP D'.toPre _ (2 • y)) (lift κ x') z J' =
      cubV D'.toPre.cub z J' m' m' x' := by
    have C := isCub_cubV D'.toPre.cub hJ'
    have ρ₂ : lift κ x' ≫ DegPre.prB D'.toPre (FractionRing R) = x' := lift_snd _ _
    rw [uVal, cPoint_zero, cubN, ρ₂, comp_cP, comp_cP]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, pow_zero, pow_one, _root_.one_mul,
      _root_.mul_one, C.face, inv_one]
    rfl
  rw [u₂, hxm, zero_add] at e₂

  have e₃ := hcorr (2 • y) T.left x'.left z J J' hJ hJ'
  have p₄ : x' * m' ^ 2 = a * m' := by rw [pow_two, ← _root_.mul_assoc, hxm]
  rw [prod_famB_wtTwo, cPoint_nsmul, ← hm', p₄, map_nsmul] at e₃

  have e₄ := hcorr 0 T.left a.left z J J' hJ hJ'
  rw [prod_famB_wtTwo, smul_zero, map_zero, cPoint_zero, _root_.mul_one,
    show a.left ≫ Φ.hom.left = pB.left from congrArg (fun q => q.left) haΦ] at e₄

  have e₅ := hcub T z J J' hJ hJ' _ rfl m' m' x'
  have p₁ : m' * m' * x' = a * m' := by rw [mul_comm (m' * m') x', ← _root_.mul_assoc, hxm]
  have p₃ : m' * x' = a := by rw [mul_comm, hxm]
  rw [hmΦ, p₁, p₃, ← sq] at e₅
  exact sq_unit_cancel h0 e₁ e₂ e₃ e₄ e₅
end
end

