import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpObjPullG
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2220
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2291
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0654
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenframeBaseChangeLocalRings
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegers
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalBoundaryMetricData
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2278
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2248
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianHaarIndependentOfOrthonormalFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1951
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0065
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0126
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.MuCardLeTwo

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelStabilizerAction
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EqvInterior

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H}

section Moves

variable (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M) (Xo : Moduli Dw l)

def nu (g : LevelAut Dw l) : SABMap Xo.univ.t Xo.univ.t (GlobalTheory.CompLevelStab.mv hpq hA Xo g) :=
  (GlobalTheory.CompLevelStab.mv_spec hpq hA Xo g).choose

theorem nu_spec (g : LevelAut Dw l) :
    IsLevMove (GlobalTheory.CompLevelStab.mv hpq hA Xo g) (nu hpq hA Xo g) (liftLa g) LinearMap.id :=
  (GlobalTheory.CompLevelStab.mv_spec hpq hA Xo g).choose_spec.2

theorem nu_mul (c : Coeff l) (g h : LevelAut Dw l) : (nu hpq hA Xo (g * h)).φ = (nu hpq hA Xo g).φ ≫ (nu hpq hA Xo h).φ := by
  obtain ⟨μ, hμ, -⟩ := (GlobalTheory.T.framedPointMove_calculus E H Dw l Xo c).2.1 _ _ (nu hpq hA Xo g) (nu hpq hA Xo h)
  have hg := nu_spec hpq hA Xo g
  have hh := nu_spec hpq hA Xo h
  have hc : IsLevMove (GlobalTheory.CompLevelStab.mv hpq hA Xo g ≫ GlobalTheory.CompLevelStab.mv hpq hA Xo h) μ (liftLa (g * h))
      LinearMap.id := by
    refine ⟨?_, fun a => ?_, fun a => ?_⟩
    · rw [Category.assoc, hh.1, hg.1]
    · rw [GlobalTheory.LevelActionLaws.eta_congr Xo (GlobalTheory.LevelActionLaws.liftLa_mul_sub g h a), hμ, ← Category.assoc, hg.2.1,
        Category.assoc, hh.2.1, Category.assoc]
    · have e : (LinearMap.id : Dw.La →ₗ[𝓞 E] Dw.La) a =
          (LinearMap.id : Dw.La →ₗ[𝓞 E] Dw.La) ((LinearMap.id : Dw.La →ₗ[𝓞 E] Dw.La) a) := rfl
      rw [e, hμ, ← Category.assoc, hg.2.2, Category.assoc, hh.2.2, Category.assoc]
  have := (GlobalTheory.CompLevelStab.mv_spec hpq hA Xo g).choose_spec.1
  have := (GlobalTheory.CompLevelStab.mv_spec hpq hA Xo h).choose_spec.1
  rw [← hμ]
  exact (GlobalTheory.LevelActionLaws.move_unique hpq hA Xo c (g * h) (GlobalTheory.CompLevelStab.mv_spec hpq hA Xo (g * h)).choose_spec.1
    inferInstance (nu_spec hpq hA Xo (g * h)) hc).2

end Moves

section Lift

variable {hpq : 1 ≤ Dw.p + Dw.q} {hA : l.A.Coprime l.M} {Xo : Moduli Dw l} {c : Coeff l}
variable (TF : TorFlag Xo c) (Z : Comp Xo c)

theorem j₀_ι' : j₀ TF.Y Z ≫ (barComp TF.Y Z).ι = i₀ TF.Y Z ≫ (TF.Y.jQ ≫ pullback.fst _ _) := j₀_ι TF.Y Z

def toF : (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)).left ⟶ TF.Y.oF.t.G.left :=
  TF.Y.m.cart.1.lift (pullback.fst TF.Y.t.G.hom (j₀ TF.Y Z ≫ (barComp TF.Y Z).ι))
    (pullback.snd TF.Y.t.G.hom (j₀ TF.Y Z ≫ (barComp TF.Y Z).ι) ≫ i₀ TF.Y Z) (by
      rw [pullback.condition, Category.assoc]; exact congrArg (_ ≫ ·) (j₀_ι' TF Z))

theorem toF_m : toF TF Z ≫ TF.Y.m.φ = pullback.fst TF.Y.t.G.hom (j₀ TF.Y Z ≫ (barComp TF.Y Z).ι) :=
  TF.Y.m.cart.1.lift_fst _ _ _

theorem toF_hom : toF TF Z ≫ TF.Y.oF.t.G.hom =
    pullback.snd TF.Y.t.G.hom (j₀ TF.Y Z ≫ (barComp TF.Y Z).ι) ≫ i₀ TF.Y Z :=
  TF.Y.m.cart.1.lift_snd _ _ _

theorem toF_cart : IsGrpPullback (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)) TF.Y.oF.t.G (i₀ TF.Y Z) (toF TF Z) :=
  IsGrpPullback.cancel TF.Y.m.cart
    ((GlobalTheory.EqvAct.isGrpPullback_pullψ TF Z (j₀ TF.Y Z)).congr (j₀_ι' TF Z) (toF_m TF Z).symm) (toF_hom TF Z)

def toU : (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)).left ⟶ Xo.univ.t.G.left := toF TF Z ≫ TF.Y.m0.toSABMap.φ

theorem toU_cart : IsGrpPullback (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)) Xo.univ.t.G (i₀ TF.Y Z ≫ pullback.fst _ _)
    (toU TF Z) :=
  (toF_cart TF Z).comp TF.Y.m0.cart

theorem hom_ext' {T : Scheme.{0}} {u u' : T ⟶ (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)).left}
    (h₁ : u ≫ pullback.snd TF.Y.t.G.hom (j₀ TF.Y Z ≫ (barComp TF.Y Z).ι) =
      u' ≫ pullback.snd TF.Y.t.G.hom (j₀ TF.Y Z ≫ (barComp TF.Y Z).ι))
    (h₂ : u ≫ toU TF Z = u' ≫ toU TF Z) : u = u' :=
  (toU_cart TF Z).1.hom_ext h₂ h₁

end Lift

section Move

variable (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M) {Xo : Moduli Dw l} {c : Coeff l}
variable (TF : TorFlag Xo c) (Z : Comp Xo c)

theorem nF_w (g : LevelAut Dw l) (r : V₀ TF.Y Z ⟶ V₀ TF.Y Z)
    (hr : r ≫ i₀ TF.Y Z = i₀ TF.Y Z ≫ GlobalTheory.CompLevelStab.mvF hpq hA Xo c g) :
    (toU TF Z ≫ (nu hpq hA Xo g).φ) ≫ Xo.univ.t.G.hom =
      (pullback.snd TF.Y.t.G.hom (j₀ TF.Y Z ≫ (barComp TF.Y Z).ι) ≫ r ≫ i₀ TF.Y Z) ≫ pullback.fst _ _ := by
  rw [Category.assoc, (nu hpq hA Xo g).cart.1.w, ← Category.assoc, (toU_cart TF Z).1.w, hr,
    Category.assoc, Category.assoc, Category.assoc, Category.assoc, GlobalTheory.CompLevelStab.mvF_fst]
  rfl

def nF (g : LevelAut Dw l) (r : V₀ TF.Y Z ⟶ V₀ TF.Y Z)
    (hr : r ≫ i₀ TF.Y Z = i₀ TF.Y Z ≫ GlobalTheory.CompLevelStab.mvF hpq hA Xo c g) :
    (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)).left ⟶ (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)).left :=
  pullback.lift
    (TF.Y.m0.cart.1.lift (toU TF Z ≫ (nu hpq hA Xo g).φ)
      (pullback.snd TF.Y.t.G.hom (j₀ TF.Y Z ≫ (barComp TF.Y Z).ι) ≫ r ≫ i₀ TF.Y Z) (nF_w hpq hA TF Z g r hr) ≫ TF.Y.m.φ)
    (pullback.snd TF.Y.t.G.hom (j₀ TF.Y Z ≫ (barComp TF.Y Z).ι) ≫ r) (by
      rw [Category.assoc, TF.Y.m.cart.1.w, ← Category.assoc, TF.Y.m0.cart.1.lift_snd]
      simp only [Category.assoc]
      exact congrArg (fun x => _ ≫ r ≫ x) (j₀_ι' TF Z).symm)

variable (g : LevelAut Dw l) (r : V₀ TF.Y Z ⟶ V₀ TF.Y Z)
  (hr : r ≫ i₀ TF.Y Z = i₀ TF.Y Z ≫ GlobalTheory.CompLevelStab.mvF hpq hA Xo c g)

theorem nF_snd : nF hpq hA TF Z g r hr ≫ pullback.snd TF.Y.t.G.hom (j₀ TF.Y Z ≫ (barComp TF.Y Z).ι) =
    pullback.snd TF.Y.t.G.hom (j₀ TF.Y Z ≫ (barComp TF.Y Z).ι) ≫ r :=
  pullback.lift_snd _ _ _

theorem nF_toF : nF hpq hA TF Z g r hr ≫ toF TF Z = TF.Y.m0.cart.1.lift (toU TF Z ≫ (nu hpq hA Xo g).φ)
      (pullback.snd TF.Y.t.G.hom (j₀ TF.Y Z ≫ (barComp TF.Y Z).ι) ≫ r ≫ i₀ TF.Y Z) (nF_w hpq hA TF Z g r hr) := by
  apply TF.Y.m.cart.1.hom_ext
  · rw [Category.assoc, toF_m]
    exact pullback.lift_fst _ _ _
  · rw [Category.assoc, toF_hom, ← Category.assoc, nF_snd, Category.assoc, TF.Y.m0.cart.1.lift_snd]

theorem nF_toU : nF hpq hA TF Z g r hr ≫ toU TF Z = toU TF Z ≫ (nu hpq hA Xo g).φ := by
  rw [toU, ← Category.assoc, nF_toF]
  exact TF.Y.m0.cart.1.lift_fst _ _ _

theorem nF_cart : IsGrpPullback (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)) (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)) r
    (nF hpq hA TF Z g r hr) := by
  refine IsGrpPullback.cancel (toU_cart TF Z) (((toU_cart TF Z).comp (nu hpq hA Xo g).cart).congr ?_ ?_) ?_
  · rw [Category.assoc, ← GlobalTheory.CompLevelStab.mvF_fst, ← Category.assoc, ← hr, Category.assoc]
  · exact (nF_toU hpq hA TF Z g r hr).symm
  · exact nF_snd hpq hA TF Z g r hr

end Move

section Laws

variable (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M) {Xo : Moduli Dw l} {c : Coeff l}
variable (TF : TorFlag Xo c) (Z : Comp Xo c)

theorem act_toF (a : 𝓞 E) : ((GlobalTheory.EqvAct.pullAct TF Z (j₀ TF.Y Z)).act a).left ≫ toF TF Z =
    toF TF Z ≫ (TF.Y.oF.t.act.act a).left := by
  apply TF.Y.m.cart.1.hom_ext
  · rw [Category.assoc, toF_m, Category.assoc, TF.Y.m.act a, ← Category.assoc, toF_m]
    exact GlobalTheory.EqvAct.pullAct_pullψ TF Z (j₀ TF.Y Z) a
  · rw [Category.assoc, toF_hom, Category.assoc, Over.w (TF.Y.oF.t.act.act a), toF_hom, ← Category.assoc]
    exact congrArg (· ≫ i₀ TF.Y Z) (Over.w ((GlobalTheory.EqvAct.pullAct TF Z (j₀ TF.Y Z)).act a))

theorem act_toU (a : 𝓞 E) : ((GlobalTheory.EqvAct.pullAct TF Z (j₀ TF.Y Z)).act a).left ≫ toU TF Z =
    toU TF Z ≫ (Xo.univ.t.act.act a).left := by
  rw [toU, ← Category.assoc, act_toF, Category.assoc, TF.Y.m0.toSABMap.act a, Category.assoc]

variable (g : LevelAut Dw l) (r : V₀ TF.Y Z ⟶ V₀ TF.Y Z)
  (hr : r ≫ i₀ TF.Y Z = i₀ TF.Y Z ≫ GlobalTheory.CompLevelStab.mvF hpq hA Xo c g)

theorem act_nF (a : 𝓞 E) : ((GlobalTheory.EqvAct.pullAct TF Z (j₀ TF.Y Z)).act a).left ≫ nF hpq hA TF Z g r hr =
    nF hpq hA TF Z g r hr ≫ ((GlobalTheory.EqvAct.pullAct TF Z (j₀ TF.Y Z)).act a).left := by
  apply hom_ext' TF Z
  · rw [Category.assoc, nF_snd, Category.assoc]
    have e := Over.w ((GlobalTheory.EqvAct.pullAct TF Z (j₀ TF.Y Z)).act a)
    erw [e, ← Category.assoc, e]
    exact (nF_snd hpq hA TF Z g r hr).symm
  · have e1 : ((GlobalTheory.EqvAct.pullAct TF Z (j₀ TF.Y Z)).act a).left ≫ nF hpq hA TF Z g r hr ≫ toU TF Z =
        toU TF Z ≫ (Xo.univ.t.act.act a).left ≫ (nu hpq hA Xo g).φ := by
      rw [nF_toU, ← Category.assoc, act_toU, Category.assoc]
    have e2 : (nF hpq hA TF Z g r hr ≫ ((GlobalTheory.EqvAct.pullAct TF Z (j₀ TF.Y Z)).act a).left) ≫ toU TF Z =
        toU TF Z ≫ (nu hpq hA Xo g).φ ≫ (Xo.univ.t.act.act a).left := by
      rw [Category.assoc, act_toU, ← Category.assoc, nF_toU, Category.assoc]
    rw [Category.assoc, e1, e2, (nu hpq hA Xo g).act a]

theorem sec_toU (b : Dw.La) (w : V₀ TF.Y Z ⟶ (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)).left)
    (hw : w ≫ (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)).hom = 𝟙 _)
    (hb : w ≫ GlobalTheory.EqvAct.pullψ TF Z (j₀ TF.Y Z) = i₀ TF.Y Z ≫ (TF.Y.oF.eta b).left ≫ TF.Y.m.φ) :
    w ≫ toU TF Z = i₀ TF.Y Z ≫ pullback.fst _ _ ≫ (Xo.univ.eta b).left := by
  have hF : w ≫ toF TF Z = i₀ TF.Y Z ≫ (TF.Y.oF.eta b).left := by
    apply TF.Y.m.cart.1.hom_ext
    · rw [Category.assoc, toF_m, Category.assoc]
      exact hb
    · rw [Category.assoc, toF_hom, ← Category.assoc]
      erw [hw]
      rw [Category.id_comp, Category.assoc, Over.w (TF.Y.oF.eta b)]
      exact (Category.comp_id _).symm
  rw [toU, ← Category.assoc, hF, Category.assoc, TF.Y.m0.eta b]

end Laws

theorem eqvAct_interior : Hypotheses2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M) (Γ : Type) [Group Γ] (ι : Γ →* LevelAut Dw l) (ρ : Γ →* Aut (V₀ TF.Y Z)), (∀ γ : Γ, (ρ γ).hom ≫ i₀ TF.Y Z = i₀ TF.Y Z ≫ GlobalTheory.CompLevelStab.mvF hpq hA Xo c (ι γ)⁻¹) → ∃ n : Γ → ((GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)).left ⟶ (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)).left), GlobalTheory.EqvAct.IsEqvAct ρ (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)) (GlobalTheory.EqvAct.pullAct TF Z (j₀ TF.Y Z)) n ∧ GlobalTheory.EqvAct.MovesEta TF Z ι ρ (𝟙 (V₀ TF.Y Z)) (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)) (GlobalTheory.EqvAct.pullψ TF Z (j₀ TF.Y Z)) n := by
  intro _ E _ _ _ H Dw l Xo c TF Z hpq hA Γ _ ι ρ hρ
  refine ⟨fun γ => nF hpq hA TF Z (ι γ)⁻¹ (ρ γ).hom (hρ γ),
    ⟨fun γ => nF_cart hpq hA TF Z _ _ (hρ γ), fun γ a => act_nF hpq hA TF Z _ _ (hρ γ) a, fun γ₁ γ₂ => ?_⟩,
    fun γ a b hab w w' hw hw' hb ha => ?_⟩
  · apply hom_ext' TF Z
    · rw [nF_snd, Category.assoc, nF_snd, ← Category.assoc, nF_snd, Category.assoc, map_mul, Aut.Aut_mul_def]
      rfl
    · rw [nF_toU, Category.assoc, nF_toU, ← Category.assoc, nF_toU, Category.assoc, ← nu_mul hpq hA Xo c, map_mul,
        mul_inv_rev]
  · apply hom_ext' TF Z
    · rw [Category.assoc, nF_snd, ← Category.assoc, Category.assoc (ρ γ).hom]
      erw [hw, hw']
      rw [Category.id_comp, Category.comp_id]
    · have hq : b - liftLa (ι γ)⁻¹ a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) := by
        rw [← Submodule.Quotient.eq]
        exact hab.trans (liftLa_spec (ι γ)⁻¹ a).symm
      have L : (w ≫ nF hpq hA TF Z (ι γ)⁻¹ (ρ γ).hom (hρ γ)) ≫ toU TF Z =
          i₀ TF.Y Z ≫ pullback.fst _ _ ≫ (Xo.univ.eta b).left ≫ (nu hpq hA Xo (ι γ)⁻¹).φ := by
        rw [Category.assoc, nF_toU, ← Category.assoc, sec_toU TF Z b w hw hb, Category.assoc, Category.assoc]
      have R : ((ρ γ).hom ≫ w') ≫ toU TF Z = (ρ γ).hom ≫ i₀ TF.Y Z ≫ pullback.fst _ _ ≫ (Xo.univ.eta a).left := by
        rw [Category.assoc, sec_toU TF Z a w' hw' ha]
      rw [L, R, GlobalTheory.LevelActionLaws.eta_congr Xo hq, (nu_spec hpq hA Xo (ι γ)⁻¹).2.1 a,
        ← Category.assoc (pullback.fst _ _), ← GlobalTheory.CompLevelStab.mvF_fst]
      simp only [← Category.assoc]
      rw [← hρ γ]

end GlobalTheory.EqvInterior
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieDeterminantLineRatioFunction
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam
  GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine

namespace GlobalTheory.DetRatio

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {l : Level H}
  {S X : Scheme.{0}} {c : Coeff l} {t : SAB H S} {π : X ⟶ S} {s : X ⟶ Sp c.F} {V : Set X} {τ : E →+* ℂ}
  {p q : ℕ} {R R' : Type} [CommRing R] [CommRing R'] {σ σ' : Rule t π p q}

theorem sec_pull (hσ : IsSection t π s V (HermitianCompactForm.chi c τ) σ) (g : R →+* R') {j : c.F →+* R} {j' : c.F →+* R'}
    {x : Sp R ⟶ X} {v w} {x' : Sp R' ⟶ X} {v' w'}
    (h : IsFrame t π s V (HermitianCompactForm.chi c τ) j x v w) (h' : IsFrame t π s V (HermitianCompactForm.chi c τ) j' x' v' w')
    (hx : x' = spMap g ≫ x) (a : ∀ i, (v' i).left = spMap (Chart.dualMapR g) ≫ (v i).left)
    (b : ∀ i, (w' i).left = spMap (Chart.dualMapR g) ≫ (w i).left) : σ R' x' v' w' = g (σ R x v w) :=
  hσ.1 R R' g (Chart.dualMapR g) j _ x x' v w v' w'
    (fun a => by ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl])
    (by ext <;> simp [Chart.dualMapR]) h h' hx a b

theorem ratio_frame (hσ : IsSection t π s V (HermitianCompactForm.chi c τ) σ) (hn : NowhereZero t π s V (HermitianCompactForm.chi c τ) σ)
    (hσ' : IsSection t π s V (HermitianCompactForm.chi c τ) σ') {j : c.F →+* R} {x : Sp R ⟶ X} {v w v' w'}
    (h : IsFrame t π s V (HermitianCompactForm.chi c τ) j x v w) (h' : IsFrame t π s V (HermitianCompactForm.chi c τ) j x v' w') {a : R}
    (e : σ' R x v w = a * σ R x v w) : σ' R x v' w' = a * σ R x v' w' := by
  have h₁ : IsFrame t π s V (HermitianCompactForm.chi c τ) j x v' w := ⟨h.1, h.2.1, h'.2.2.1, h.2.2.2⟩
  choose M hM using fun i => (h.2.2.1.2 _ (h'.2.2.1.1 i)).exists
  choose N hN using fun i => (h.2.2.2.2 _ (h'.2.2.2.1 i)).exists
  have ow : ∀ i, IsCombAt (x ≫ π) ((1 : Matrix (Fin q) (Fin q) R) i) w (w i) :=
    fun i => DetExtendZero.comb_one (fun k => (h.2.2.2.1 k).1) i
  have ov : ∀ i, IsCombAt (x ≫ π) ((1 : Matrix (Fin p) (Fin p) R) i) v' (v' i) :=
    fun i => DetExtendZero.comb_one (fun k => (h'.2.2.1.1 k).1) i
  have e1 := hσ.2 R j x v w v' w (Matrix.of M) 1 h h₁ hM ow
  have e1' := hσ'.2 R j x v w v' w (Matrix.of M) 1 h h₁ hM ow
  have e2 := hσ.2 R j x v' w v' w' 1 (Matrix.of N) h₁ h' ov hN
  have e2' := hσ'.2 R j x v' w v' w' 1 (Matrix.of N) h₁ h' ov hN
  rw [Matrix.det_one, _root_.one_mul] at e1 e1' e2 e2'
  have hu : IsUnit (Matrix.of M).det := isUnit_of_mul_isUnit_left (e1 ▸ hn R j x v w h)
  have e3 : σ' R x v' w = a * σ R x v' w := by
    refine hu.mul_left_cancel ?_
    rw [← e1', e, e1]; ring
  rw [← e2', ← e2, e3]; ring

theorem ratio_pull (hσ : IsSection t π s V (HermitianCompactForm.chi c τ) σ) (hn : NowhereZero t π s V (HermitianCompactForm.chi c τ) σ)
    (hσ' : IsSection t π s V (HermitianCompactForm.chi c τ) σ') (g : R →+* R') {j : c.F →+* R} {j' : c.F →+* R'}
    {x : Sp R ⟶ X} {v w} {x' : Sp R' ⟶ X} {v' w'}
    (h : IsFrame t π s V (HermitianCompactForm.chi c τ) j x v w) (h' : IsFrame t π s V (HermitianCompactForm.chi c τ) j' x' v' w')
    (hx : x' = spMap g ≫ x) {a : R} (e : σ' R x v w = a * σ R x v w) :
    σ' R' x' v' w' = g a * σ R' x' v' w' := by
  obtain ⟨v₁, w₁, h₁, a₁, b₁⟩ := exists_pull g h hx
  obtain rfl := (exists_chg g h h' hx).1
  refine ratio_frame hσ hn hσ' h₁ h' ?_
  rw [sec_pull hσ g h h₁ hx a₁ b₁, sec_pull hσ' g h h₁ hx a₁ b₁, e, map_mul]

theorem exists_ratio_affine (hσ : IsSection t π s V (HermitianCompactForm.chi c τ) σ)
    (hn : NowhereZero t π s V (HermitianCompactForm.chi c τ) σ) (hσ' : IsSection t π s V (HermitianCompactForm.chi c τ) σ')
    {W : X.Opens} (hW : IsAffineOpen W) {j₀ : c.F →+* Γ(X, W)} {v₀ w₀}
    (h₀ : IsFrame t π s V (HermitianCompactForm.chi c τ) (p := p) (q := q) j₀ (show Sp Γ(X, W) ⟶ X from hW.fromSpec) v₀ w₀) :
    ∃ f : Γ(X, W), ∀ (R : Type) [CommRing R] (j : c.F →+* R) (x : Sp R ⟶ X) v w, ⊤ ≤ x ⁻¹ᵁ W →
      IsFrame t π s V (HermitianCompactForm.chi c τ) j x v w → σ' R x v w = valR x W f * σ R x v w := by
  obtain ⟨u, hu⟩ := hn _ j₀ _ v₀ w₀ h₀
  refine ⟨σ' _ _ v₀ w₀ * u.inv, fun R _ j x v w hx h => ?_⟩
  rw [Points.valR_eq x W hx]
  refine ratio_pull hσ hn hσ' (Points.valMap x W hx).hom h₀ h (Points.specMap_valMap_fromSpec hW x hx).symm ?_
  rw [← hu, _root_.mul_assoc, u.inv_val, _root_.mul_one]

theorem valR_fromSpec {A : X.Opens} (hA : IsAffineOpen A) (f : Γ(X, A)) :
    valR (show Sp Γ(X, A) ⟶ X from hA.fromSpec) A f = f := by
  have hx : ⊤ ≤ (show Sp Γ(X, A) ⟶ X from hA.fromSpec) ⁻¹ᵁ A := hA.fromSpec_preimage_self.ge
  rw [Points.valR_eq _ A hx]
  have : Points.valMap (show Sp Γ(X, A) ⟶ X from hA.fromSpec) A hx = 𝟙 _ := by
    apply Spec.map_injective
    rw [← cancel_mono hA.fromSpec, Points.specMap_valMap_fromSpec]
    exact ((congrArg (· ≫ hA.fromSpec) (Spec.map_id _)).trans (Category.id_comp _)).symm
  rw [this]
  rfl

end GlobalTheory.DetRatio

open GlobalTheory.DetRatio in

theorem GlobalTheory.detLine_exists_ratio (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (l : Level H) (c : Coeff l) (S X : Scheme.{0}) (t : SAB H S) (π : X ⟶ S) (s : X ⟶ Sp c.F) (τ : E →+* ℂ)
    (p q : ℕ) (V : X.Opens) (σ σ' : Rule t π p q) (hc : FrameCover t π s V (HermitianCompactForm.chi c τ) p q)
    (hσ : IsSection t π s V (HermitianCompactForm.chi c τ) σ) (hn : NowhereZero t π s V (HermitianCompactForm.chi c τ) σ)
    (hσ' : IsSection t π s V (HermitianCompactForm.chi c τ) σ') :
    ∃ f : Γ(X, V), ∀ (R : Type) [CommRing R] (j : c.F →+* R) (x : Sp R ⟶ X) v w,
      IsFrame t π s V (HermitianCompactForm.chi c τ) j x v w → σ' R x v w = valR x V f * σ R x v w := by
  choose W hW j₀ v₀ w₀ hz h₀ using fun z : V => hc z z.2
  choose f hf using fun z : V => exists_ratio_affine hσ hn hσ' (hW z) (h₀ z)
  have hle : ∀ z, W z ≤ V := fun z y hy => (h₀ z).2.1 (by
    change y ∈ Set.range (hW z).fromSpec
    rw [(hW z).range_fromSpec]; exact hy)
  have hcov : V ≤ iSup W := fun y hy => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨y, hy⟩, hz _⟩
  have hcomp : TopCat.Presheaf.IsCompatible X.presheaf W f := by
    intro a b
    refine X.sheaf.eq_of_locally_eq' (fun A : {A : X.affineOpens // A.1 ≤ W a ⊓ W b} => A.1.1) (W a ⊓ W b)
      (fun A => homOfLE A.2) (fun y hy => ?_) _ _ fun A => ?_
    · obtain ⟨_, ⟨A, hA, rfl⟩, hy', hA'⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hy (W a ⊓ W b).2
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨A, hA⟩, hA'⟩, hy'⟩
    · obtain ⟨⟨A, hA⟩, hAle⟩ := A
      replace hA : IsAffineOpen A := hA
      have hx : ⊤ ≤ (show Sp Γ(X, A) ⟶ X from hA.fromSpec) ⁻¹ᵁ A := hA.fromSpec_preimage_self.ge
      have hxa := Points.le_preimage_mono _ (hAle.trans inf_le_left) hx
      have hxb := Points.le_preimage_mono _ (hAle.trans inf_le_right) hx
      have hxab := Points.le_preimage_mono _ hAle hx
      obtain ⟨v, w, h, -, -⟩ := exists_pull (Points.valMap _ (W a) hxa).hom (h₀ a)
        (Points.specMap_valMap_fromSpec (hW a) _ hxa).symm
      have e := (hn _ _ _ v w h).mul_right_cancel ((hf a _ _ _ v w hxa h).symm.trans (hf b _ _ _ v w hxb h))
      refine (valR_fromSpec hA _).symm.trans (Eq.trans ?_ (valR_fromSpec hA _))
      refine (Points.valR_res _ hAle hx _).trans (Eq.trans ?_ (Points.valR_res _ hAle hx _).symm)
      exact (Points.valR_res _ inf_le_left hxab _).trans (e.trans (Points.valR_res _ inf_le_right hxab _).symm)
  obtain ⟨F, hF, -⟩ := X.sheaf.existsUnique_gluing' W V (fun z => homOfLE (hle z)) hcov f hcomp
  refine ⟨F, fun R _ j x v w h => ?_⟩
  have hxV : ⊤ ≤ x ⁻¹ᵁ V := fun y _ => h.2.1 ⟨y, rfl⟩
  rw [← sub_eq_zero]
  refine eq_zero_of_localization _ fun J hJ => ?_
  let g := algebraMap R (Localization.AtPrime J)
  obtain ⟨v₁, w₁, h₁, a₁, b₁⟩ := exists_pull g h rfl
  let z : V := ⟨(spMap g ≫ x) (IsLocalRing.closedPoint (Localization.AtPrime J)), h₁.2.1 ⟨_, rfl⟩⟩
  have hxW : ⊤ ≤ (spMap g ≫ x) ⁻¹ᵁ W z := (Points.le_preimage_iff _ _).2 (hz z)
  have e := hf z _ _ _ v₁ w₁ hxW h₁
  rw [sec_pull hσ g h h₁ rfl a₁ b₁, sec_pull hσ' g h h₁ rfl a₁ b₁, ← hF z] at e
  have e' := (Points.valR_res _ (hle z) hxW F).trans (Points.valR_spMap_comp g x V hxV F)
  change g _ = 0
  rw [map_sub, map_mul, ← e', sub_eq_zero]
  exact e
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieEigenspaceFrameFlagCoverChartDomain
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open scoped LaurentSeries

noncomputable section

namespace GlobalTheory.ChartEigFrame

open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv actR)
open GlobalTheory.FlagMod GlobalTheory.Reg
open MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}

theorem tanPull_injective_of_chart {V K : Type} [CommRing V] [CommRing K] (ρ : V →+* K) (hρ : Function.Injective ρ)
    (M : MChart Y) {x : Sp V ⟶ Y.X} {x' : Sp K ⟶ Y.X} (e : spMap ρ ≫ x = x') (h : ⊤ ≤ x ⁻¹ᵁ M.U)
    (h' : ⊤ ≤ x' ⁻¹ᵁ M.U) : Function.Injective (tanPull (G := Y.t.G) ρ e) := by
  intro u u' huu
  obtain ⟨cv, rfl⟩ := (vec M x h).surjective u
  obtain ⟨cv', rfl⟩ := (vec M x h).surjective u'
  rw [tanPull_vec M ρ e h h', tanPull_vec M ρ e h h'] at huu
  have := (vec M x' h').injective huu
  congr 1
  funext j
  exact hρ (congrFun this j)

theorem exists_eigFrame_of_top {X : FlagCover Y} {V K : Type} [CommRing V] [CommRing K] [Algebra c.F K]
    (ρ : V →+* K) (hρ : Function.Injective ρ) (φ : c.F →+* V) (hφ : ρ.comp φ = algebraMap c.F K)
    (q : Sp V ⟶ X.YY) (k : X.F.J) (hz : ⊤ ≤ q ⁻¹ᵁ X.F.U k) (hz' : ⊤ ≤ (spMap ρ ≫ q) ⁻¹ᵁ X.F.U k)
    (htop : ∀ σ, initSpan K (X.F.vecAt k (spMap ρ ≫ q) hz' rfl σ) (Dw.mult σ) = eigLie c ((spMap ρ ≫ q) ≫ X.π) σ) :
    ∃ f : GlobalTheory.ShFam.EigFrame Y φ (q ≫ X.π), ∀ τ i, f.v τ i = (tv (X.F.vecAt k q hz rfl τ i)).left := by
  have hx : ⊤ ≤ (q ≫ X.π) ⁻¹ᵁ (X.F.M k).toMChart.U := X.F.inM hz rfl
  have hx' : ⊤ ≤ ((spMap ρ ≫ q) ≫ X.π) ⁻¹ᵁ (X.F.M k).toMChart.U := X.F.inM hz' rfl
  have e : spMap ρ ≫ (q ≫ X.π) = (spMap ρ ≫ q) ≫ X.π := (Category.assoc _ _ _).symm
  have hinj := tanPull_injective_of_chart ρ hρ (X.F.M k).toMChart e hx hx'
  have hpull : ∀ τ i, tanPull ρ e (X.F.vecAt k q hz rfl τ i) = X.F.vecAt k (spMap ρ ≫ q) hz' rfl τ i :=
    fun τ i => X.F.tanPull_vecAt k ρ q hz hz' rfl rfl e τ i
  have hmem : ∀ τ i, X.F.vecAt k (spMap ρ ≫ q) hz' rfl τ i ∈ eigLie c ((spMap ρ ≫ q) ≫ X.π) τ := fun τ i => by
    rw [← htop τ]
    exact Submodule.subset_span ⟨i, i.2, rfl⟩
  have hsmul : ∀ (τ : E →+* ℂ) (a : 𝓞 E) (w : TanM (q ≫ X.π) Y.t.G),
      tanPull ρ e (φ (embK c τ a) • w) = algebraMap c.F K (embK c τ a) • tanPull ρ e w := fun τ a w => by
    rw [map_smulₛₗ, ← hφ]
    rfl
  refine ⟨GlobalTheory.ShFam.EigFrame.ofVec (fun τ i => X.F.vecAt k q hz rfl τ i) (fun τ i a => ?_) (fun τ w hw => ?_),
    fun τ i => rfl⟩
  · apply hinj
    rw [tanPull_actR, hsmul, hpull]
    exact hmem τ i a
  · have hw' : tanPull ρ e w ∈ eigLie c ((spMap ρ ≫ q) ≫ X.π) τ := fun a => by
      rw [← tanPull_actR, hw a, hsmul]
    rw [← htop τ] at hw'
    obtain ⟨a, -, ha⟩ := mem_initSpan.1 hw'
    obtain ⟨W, hW⟩ := X.F.uAt_split k q hz τ
    obtain ⟨cv, rfl⟩ := (vec (X.F.M k).toMChart (q ≫ X.π) hx).surjective w
    rw [X.F.sum_vecAt, tanPull_vec (X.F.M k).toMChart ρ e hx hx'] at ha
    have hc := (vec (X.F.M k).toMChart _ hx').injective ha
    rw [X.F.uAt_spMap k ρ q hz hz'] at hc
    have hWρ : W.map ρ * (X.F.uAt k q hz τ).map ρ = 1 := by
      rw [← Matrix.map_mul, hW, Matrix.map_one _ (map_zero _) (map_one _)]
    have ha2 : (W.map ρ).mulVec (fun j => ρ (cv j)) = a := by
      rw [← hc, Matrix.mulVec_mulVec, hWρ, Matrix.one_mulVec]
    refine ⟨W.mulVec cv, ?_, fun b hb => ?_⟩
    · show _ = ∑ i, _ • X.F.vecAt k q hz rfl τ i
      rw [X.F.sum_vecAt]
      congr 1
      funext j
      apply hρ
      rw [RingHom.map_mulVec]
      have : (ρ ∘ W.mulVec cv) = a := by
        rw [← ha2]
        funext i
        exact RingHom.map_mulVec ρ W cv i
      rw [this, hc]
    · have hb' : vec (X.F.M k).toMChart (q ≫ X.π) hx cv =
          vec (X.F.M k).toMChart (q ≫ X.π) hx ((X.F.uAt k q hz τ).mulVec b) := by
        rw [← X.F.sum_vecAt]
        exact hb
      have := (vec (X.F.M k).toMChart _ hx).injective hb'
      rw [this, Matrix.mulVec_mulVec, hW, Matrix.one_mulVec]

theorem exists_eigFrame_vecAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (X : FlagCover Y) (V K : Type) [CommRing V] [IsDomain V] [Field K] [Algebra V K] [IsFractionRing V K] [Algebra c.F K] (φ : c.F →+* V), (algebraMap V K).comp φ = algebraMap c.F K → ∀ (q : Sp V ⟶ X.YY) (k : X.F.J) (hz : ⊤ ≤ q ⁻¹ᵁ X.F.U k) (yF : Sp K ⟶ Xo.XF c), yF ≫ pullback.snd _ _ = spMap (algebraMap c.F K) → (spMap (algebraMap V K) ≫ q) ≫ X.π = yF ≫ Y.j → ∃ f : GlobalTheory.ShFam.EigFrame Y φ (q ≫ X.π), ∀ τ i, f.v τ i = (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv (X.F.vecAt k q hz rfl τ i)).left := by
  intro E _ _ _ H Dw l Xo c O _ β Y X V K _ _ _ _ _ _ φ hφ q k hz yF hyF hpt
  have hz' : ⊤ ≤ (spMap (algebraMap V K) ≫ q) ⁻¹ᵁ X.F.U k := le_preimage_comp _ hz
  have key : ∀ (x'' : Sp K ⟶ Y.X) (hx : (spMap (algebraMap V K) ≫ q) ≫ X.π = x''),
      (∀ σ, initSpan K (X.F.vecAt k _ hz' hx σ) (Dw.mult σ) = eigLie c x'' σ) →
      ∀ σ, initSpan K (X.F.vecAt k _ hz' rfl σ) (Dw.mult σ) = eigLie c ((spMap (algebraMap V K) ≫ q) ≫ X.π) σ := by
    rintro x'' rfl h
    exact h
  exact exists_eigFrame_of_top (algebraMap V K) (IsFractionRing.injective V K) φ hφ q k hz hz'
    (key _ hpt fun σ => X.top K yF hyF _ hpt k hz' σ)

end GlobalTheory.ChartEigFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPackingSetMeasureGeCovolumeStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_packingSet_measure_ge_covolume : ∀ (H : Type) [Group H] [MeasurableSpace H] [MeasurableMul H] (ν : Measure H) (Γ : Subgroup H), Countable Γ → ∃ F : Set H, MeasurableSet F ∧ covolume Γ H ν ≤ ν F ∧ ∀ γ ∈ Γ, ∀ y ∈ F, γ * y ∈ F → γ = 1 := by
  first | exact @GlobalTheory.packing_set_covolume_le | exact GlobalTheory.packing_set_covolume_le | (intros; apply GlobalTheory.packing_set_covolume_le <;> assumption)
end

