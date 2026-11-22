import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0096
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0103
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AmpleHeightBounds
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0004
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0002
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0003
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle0014
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0089
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DedekindConstantsDegreeTwo
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0016
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TranslDiffEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GenFibreExists
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NumberField
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.MetricsProjectionFormulaNef
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0002
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EtaleLocalizationAtPrimeTensorOfLowHeight
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0004
import Development.AutomorphicSpectrum.Statements.GeometryStatements.KeyBadSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0105
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbBound
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.QuotUnif

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def AbBound {X : Scheme.{0}} (t : SAB H X) {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {Li : Type} [AddCommGroup Li] [Module Ω Li]
    {M : LieModel t.G ξ Li} {K : Type} {J : K → Type} {y : (Σ k, J k) → Ω} (h : LieMetric M y) (C : ℝ)
    (z : Sp ℂ ⟶ X) : Prop :=
  ∀ P : AbPart t z, IsPrincipal P.tB ∧ ∀ (v : epsAt (𝟙 (Sp ℂ)) ⟶ P.tK.G) (v₀ : epsAt z ⟶ t.G) (c : ℂ),
    IsTanAt _ _ v → v.left ≫ P.m.φ = v₀.left →
    HodgeIP P.tB.G P.tB.PP.L (𝟙 _) (v ≫ P.τ.q ≫ P.e.hom) (v ≫ P.τ.q ≫ P.e.hom) c → c.re ≤ C * (h.ip z v₀ v₀).re

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)}
  {S : Finset ℕ} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω}

def GoodPt (𝔐 : HodgeCpt Y S y) (z : Sp ℂ ⟶ 𝔐.X) : Prop :=
  ∃ τ : c.F →+* ℂ, z ≫ 𝔐.f ≫ Y.s = spMap (τ.comp (algebraMap (𝓞 c.F) c.F)) ∧
    (τ.comp (IntermediateField.inclusion c.le).toRingHom) (baseKA l).ρ = H.rt0

end GlobalTheory.CompanionTheory.Ar.QuotUnif
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianPartMapsCompatibleLeft
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.TanCompare

theorem grp_mul {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {T : Scheme.{0}} (a : T ⟶ S') (b : T ⟶ S) (hb : b = a ≫ f)
    (x y : Over.mk a ⟶ G') (x₀ y₀ : Over.mk b ⟶ G) (hx : x₀.left = x.left ≫ φ) (hy : y₀.left = y.left ≫ φ) :
    (x₀ * y₀).left = (x * y).left ≫ φ := by
  subst hb
  exact h.2 (Over.mk a) x y x₀ y₀ hx hy

theorem exists_lift {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} {f : S' ⟶ S} {φ : G'.left ⟶ G.left}
    (h : IsPullback φ G'.hom G.hom f) {T : Scheme.{0}} (a : T ⟶ S') (w : T ⟶ G.left) (hw : w ≫ G.hom = a ≫ f) :
    ∃ v : Over.mk a ⟶ G', v.left ≫ φ = w :=
  ⟨Over.homMk (h.lift w a hw) (by simp), by simp⟩

theorem lift_unique {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} {f : S' ⟶ S} {φ : G'.left ⟶ G.left}
    (h : IsPullback φ G'.hom G.hom f) {T : Scheme.{0}} {a : T ⟶ S'} (v v' : Over.mk a ⟶ G')
    (e : v.left ≫ φ = v'.left ≫ φ) : v = v' :=
  Over.OverMorphism.ext (h.hom_ext e (by rw [Over.w, Over.w]))

theorem spMap_dual_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (dualMap (g.comp f)) = spMap (dualMap g) ≫ spMap (dualMap f) := by
  rw [← spMap_comp]
  congr 1
  refine RingHom.ext fun a => ?_
  refine TrivSqZeroExt.ext ?_ ?_ <;> simp [LieTangent.dualMap_fst, LieTangent.dualMap_snd]

def scale {S : Scheme.{0}} {Y : Over S} (a : Sp ℂ ⟶ S) (c : ℂ) (v : epsAt a ⟶ Y) : epsAt a ⟶ Y :=
  Over.homMk (spMap (epsMul c) ≫ v.left) (by
    have h := Over.w v
    simp only [Over.mk_left, Over.mk_hom, Category.assoc] at h ⊢
    rw [h, ← Category.assoc, LieTangent.spec_eps_alg])

@[simp] theorem scale_left {S : Scheme.{0}} {Y : Over S} (a : Sp ℂ ⟶ S) (c : ℂ) (v : epsAt a ⟶ Y) :
    (scale a c v).left = spMap (epsMul c) ≫ v.left := rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem abPart_mul {S : Scheme.{0}} {t : SAB H S} {K : Type} [Field K] {z : Sp K ⟶ S} (P : AbPart t z) {T : Over (Sp K)}
    (x y : T ⟶ P.tK.G) :
    (x * y) ≫ P.τ.q ≫ P.e.hom = (x ≫ P.τ.q ≫ P.e.hom) * (y ≫ P.τ.q ≫ P.e.hom) := by
  letI := P.τ.grpB
  haveI := P.τ.q_hom
  haveI : IsMonHom P.e.hom := P.e_hom
  rw [← Category.assoc, mul_comp, mul_comp, Category.assoc, Category.assoc]

end GlobalTheory.CompanionTheory.Ar.TanCompare

namespace GlobalTheory.CompanionTheory.Ar.TanCompare

theorem tan_compare : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (L₁ L : Type) [Field L₁] [Field L] [NumberField L] (e₂ : L₁ →+* L) (z₁ : Sp L₁ ⟶ X) (z : Sp (𝓞 L) ⟶ X) (hz : spMap (algebraMap (𝓞 L) L) ≫ z = spMap e₂ ≫ z₁) (P₁ : AbPart t z₁) (P₂ : AbPart t (spMap e₂ ≫ z₁)) (mK2 : SABMap P₂.tK P₁.tK (spMap e₂)) (mB2 : SABMap P₂.tB P₁.tB (spMap e₂)) (c1 : mK2.φ ≫ P₁.m.φ = P₂.m.φ) (c2 : mK2.φ ≫ (P₁.τ.q ≫ P₁.e.hom).left = (P₂.τ.q ≫ P₂.e.hom).left ≫ mB2.φ) (t' : SAB H (Sp (𝓞 L))) (tK : SAB H (Sp L)) (m' : SABMap tK t' (spMap (algebraMap (𝓞 L) L))) (mP : SABMap tK P₁.tB (spMap e₂)) (w : P₂.tB.G.left ⟶ tK.G.left) (hw : w ≫ mP.φ = mB2.φ) (hw' : w ≫ tK.G.hom = P₂.tB.G.hom) (V₁ V₂ : Type) [AddCommGroup V₁] [Module (𝓞 L) V₁] [AddCommGroup V₂] [Module (𝓞 L) V₂] (MB : LieModel t.G z V₁) (MB' : LieModel t'.G (𝟙 _) V₂) (f : V₁ →ₗ[𝓞 L] V₂) (hf : ∀ (e : V₁) (v : epsAt (𝟙 (Sp L)) ⟶ P₂.tK.G), MB.Lifts (algebraMap (𝓞 L) L) P₂.m.φ e v → MB'.Lifts (algebraMap (𝓞 L) L) (P₂.e.hom.left ≫ w ≫ m'.φ) (f e) (v ≫ P₂.τ.q)) (σ : L →+* ℂ) (Pσ : AbPart t (spMap (σ.comp e₂) ≫ z₁)) (mKσ : SABMap Pσ.tK P₁.tK (spMap (σ.comp e₂))) (mBσ : SABMap Pσ.tB P₁.tB (spMap (σ.comp e₂))) (d1 : mKσ.φ ≫ P₁.m.φ = Pσ.m.φ) (d2 : mKσ.φ ≫ (P₁.τ.q ≫ P₁.e.hom).left = (Pσ.τ.q ≫ Pσ.e.hom).left ≫ mBσ.φ) (Mσ : LieModel t.G (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z) (GroundTheory.Heights₂.Heights.Fibre σ V₁)) (hMσ : ∀ e : V₁, MB.Lifts (σ.comp (algebraMap (𝓞 L) L)) (𝟙 t.G.left) e (Mσ.pt ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] e))) (Mσ' : LieModel t'.G (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ 𝟙 _) (GroundTheory.Heights₂.Heights.Fibre σ V₂)) (hMσ' : ∀ e : V₂, MB'.Lifts (σ.comp (algebraMap (𝓞 L) L)) (𝟙 t'.G.left) e (Mσ'.pt ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] e))) (x : GroundTheory.Heights₂.Heights.Fibre σ V₁) (v : epsAt (𝟙 (Sp ℂ)) ⟶ Pσ.tK.G) (u : epsAt (spMap σ) ⟶ tK.G), v.left ≫ Pσ.m.φ = (Mσ.pt x).left → u.left ≫ m'.φ = (Mσ'.pt (f.lTensor (GroundTheory.Heights₂.Heights.ComplexAt σ) x)).left → u.left ≫ mP.φ = (v ≫ Pσ.τ.q ≫ Pσ.e.hom).left ≫ mBσ.φ := by
  intro E _ _ _ H X t L₁ L _ _ _ e₂ z₁ z hz P₁ P₂ mK2 mB2 c1 c2 t' tK m' mP w hw hw' V₁ V₂ _ _ _ _ MB MB' f hf σ Pσ mKσ mBσ
    d1 d2 Mσ hMσ Mσ' hMσ' x v u hv hu
  have hbase : spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z = spMap (σ.comp e₂) ≫ z₁ := by
    rw [spMap_comp (algebraMap (𝓞 L) L) σ, spMap_comp e₂ σ, Category.assoc, Category.assoc, hz]
  have hb1 : spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z =
      (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ 𝟙 _) ≫ spMap (σ.comp e₂) ≫ z₁ := by
    rw [hbase, Category.comp_id]
  have hb2 : spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ 𝟙 _ =
      (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap σ) ≫ spMap (algebraMap (𝓞 L) L) := by
    rw [spMap_comp (algebraMap (𝓞 L) L) σ, Category.comp_id, Category.assoc]
  have hb3 : (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ 𝟙 _) ≫ spMap (σ.comp e₂) =
      (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap σ) ≫ spMap e₂ := by
    rw [spMap_comp e₂ σ, Category.comp_id, Category.assoc]
  have base : ∀ e : V₁, ∃ (v : epsAt (𝟙 (Sp ℂ)) ⟶ Pσ.tK.G) (u : epsAt (spMap σ) ⟶ tK.G),
      v.left ≫ Pσ.m.φ = (Mσ.pt ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] e)).left ∧
      u.left ≫ m'.φ = (Mσ'.pt ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] f e)).left ∧
      u.left ≫ mP.φ = (v ≫ Pσ.τ.q ≫ Pσ.e.hom).left ≫ mBσ.φ := by
    intro e
    obtain ⟨vL, hvL⟩ := exists_lift P₂.m.cart.1 (spMap (algebraMap L (DualNumber L)) ≫ 𝟙 _)
      (spMap (dualMap (algebraMap (𝓞 L) L)) ≫ (MB.pt e).left) (by
        have hMe : (MB.pt e).left ≫ t.G.hom = spMap (algebraMap (𝓞 L) (DualNumber (𝓞 L))) ≫ z := Over.w (MB.pt e)
        rw [Category.assoc, hMe, ← Category.assoc, LieTangent.spec_dual_alg, Category.assoc, hz, Category.comp_id])
    have hfe : (vL ≫ P₂.τ.q).left ≫ P₂.e.hom.left ≫ w ≫ m'.φ =
        spMap (dualMap (algebraMap (𝓞 L) L)) ≫ (MB'.pt (f e)).left := hf e vL hvL
    obtain ⟨v, hv⟩ := exists_lift Pσ.m.cart.1 (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ 𝟙 _)
      (Mσ.pt ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] e)).left
      ((Over.w (Mσ.pt ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] e))).trans hb1)
    obtain ⟨u, hu⟩ := exists_lift m'.cart.1 (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap σ)
      (Mσ'.pt ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] f e)).left
      ((Over.w (Mσ'.pt ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] f e))).trans hb2)
    refine ⟨v, u, hv, hu, ?_⟩
    have hde : spMap (dualMap (σ.comp (algebraMap (𝓞 L) L))) =
        spMap (dualMap σ) ≫ spMap (dualMap (algebraMap (𝓞 L) L)) := spMap_dual_comp _ _
    have hd : spMap (dualMap σ) ≫ spMap (algebraMap L (DualNumber L)) =
        spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap σ := LieTangent.spec_dual_alg σ
    have h1 : (Mσ.pt ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] e)).left =
        spMap (dualMap (σ.comp (algebraMap (𝓞 L) L))) ≫ (MB.pt e).left :=
      (Category.comp_id _).symm.trans (hMσ e)
    have h1' : (Mσ'.pt ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] f e)).left =
        spMap (dualMap (σ.comp (algebraMap (𝓞 L) L))) ≫ (MB'.pt (f e)).left :=
      (Category.comp_id _).symm.trans (hMσ' (f e))
    have hvd : v.left ≫ Pσ.m.φ = spMap (dualMap σ) ≫ vL.left ≫ P₂.m.φ := by
      rw [hv, h1, hde, Category.assoc, hvL]
    have wv : v.left ≫ Pσ.tK.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ 𝟙 _ := Over.w v
    have wvL : vL.left ≫ P₂.tK.G.hom = spMap (algebraMap L (DualNumber L)) ≫ 𝟙 _ := Over.w vL
    have star : v.left ≫ mKσ.φ = spMap (dualMap σ) ≫ vL.left ≫ mK2.φ := by
      refine P₁.m.cart.1.hom_ext ?_ ?_
      · rw [Category.assoc, d1, hvd, Category.assoc, Category.assoc, c1]
      · rw [Category.assoc, mKσ.cart.1.w, ← Category.assoc, wv, hb3]
        simp only [Category.assoc]
        rw [mK2.cart.1.w, ← Category.assoc vL.left, wvL, Category.comp_id]
        have hd2 : spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap σ ≫ spMap e₂ =
            spMap (dualMap σ) ≫ spMap (algebraMap L (DualNumber L)) ≫ spMap e₂ := by
          rw [← Category.assoc, ← hd, Category.assoc]
        exact hd2
    have wu : u.left ≫ tK.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap σ := Over.w u
    have wq : (vL ≫ P₂.τ.q).left ≫ P₂.τ.B.hom = spMap (algebraMap L (DualNumber L)) ≫ 𝟙 _ := Over.w (vL ≫ P₂.τ.q)
    have we : P₂.e.hom.left ≫ P₂.tB.G.hom = P₂.τ.B.hom := Over.w P₂.e.hom
    have hu2 : u.left = spMap (dualMap σ) ≫ (vL ≫ P₂.τ.q).left ≫ P₂.e.hom.left ≫ w := by
      refine m'.cart.1.hom_ext ?_ ?_
      · rw [hu, h1', hde]
        simp only [Category.assoc]
        rw [hfe]
      · rw [wu]
        simp only [Category.assoc]
        rw [hw', we, wq, Category.comp_id, hd]
    have e1 : (vL ≫ P₂.τ.q).left ≫ P₂.e.hom.left ≫ mB2.φ = vL.left ≫ (P₂.τ.q ≫ P₂.e.hom).left ≫ mB2.φ := by
      simp only [Over.comp_left, Category.assoc]
    have e2 : (v ≫ Pσ.τ.q ≫ Pσ.e.hom).left ≫ mBσ.φ = v.left ≫ (Pσ.τ.q ≫ Pσ.e.hom).left ≫ mBσ.φ := by
      rw [Over.comp_left, Category.assoc]
    rw [hu2, e2, ← d2, ← Category.assoc v.left, star]
    simp only [Category.assoc]
    rw [hw, e1, ← c2]
  have tm : ∀ (c : GroundTheory.Heights₂.Heights.ComplexAt σ) (e : V₁), ∃ (v : epsAt (𝟙 (Sp ℂ)) ⟶ Pσ.tK.G) (u : epsAt (spMap σ) ⟶ tK.G),
      v.left ≫ Pσ.m.φ = (Mσ.pt (c ⊗ₜ[𝓞 L] e)).left ∧
      u.left ≫ m'.φ = (Mσ'.pt (f.lTensor (GroundTheory.Heights₂.Heights.ComplexAt σ) (c ⊗ₜ[𝓞 L] e))).left ∧
      u.left ≫ mP.φ = (v ≫ Pσ.τ.q ≫ Pσ.e.hom).left ≫ mBσ.φ := by
    intro c e
    obtain ⟨v, u, h, k, l⟩ := base e
    let c' : ℂ := c
    have hs : c' • (1 : GroundTheory.Heights₂.Heights.ComplexAt σ) = c := by
      rw [GroundTheory.Heights₂.Heights.ComplexAt.complex_smul_def, _root_.mul_one]
      rfl
    have hc : ∀ (W : Type) [AddCommGroup W] [Module (𝓞 L) W] (a : W),
        c ⊗ₜ[𝓞 L] a = c' • ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] a) := by
      intro W _ _ a
      rw [TensorProduct.smul_tmul', hs]
    refine ⟨scale _ c' v, scale _ c' u, ?_, ?_, ?_⟩
    · rw [hc, Mσ.smul, scale_left, Category.assoc, h]
    · rw [LinearMap.lTensor_tmul, hc, Mσ'.smul, scale_left, Category.assoc, k]
    · rw [scale_left, Category.assoc, l]
      simp only [Over.comp_left, scale_left, Category.assoc]
  have hx0 : ∀ u : epsAt (spMap σ) ⟶ tK.G, (u.left ≫ mP.φ) ≫ P₁.tB.G.hom =
      (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap σ) ≫ spMap e₂ := by
    intro u
    have wu : u.left ≫ tK.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap σ := Over.w u
    rw [Category.assoc, mP.cart.1.w, ← Category.assoc, wu]
  have key : ∀ x : GroundTheory.Heights₂.Heights.Fibre σ V₁, ∃ (v : epsAt (𝟙 (Sp ℂ)) ⟶ Pσ.tK.G) (u : epsAt (spMap σ) ⟶ tK.G),
      v.left ≫ Pσ.m.φ = (Mσ.pt x).left ∧
      u.left ≫ m'.φ = (Mσ'.pt (f.lTensor (GroundTheory.Heights₂.Heights.ComplexAt σ) x)).left ∧
      u.left ≫ mP.φ = (v ≫ Pσ.τ.q ≫ Pσ.e.hom).left ≫ mBσ.φ := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero =>
      have h0 := tm 0 0
      rwa [TensorProduct.zero_tmul] at h0
    | tmul c e => exact tm c e
    | add x y hx hy =>
      obtain ⟨v₁, u₁, h₁, k₁, l₁⟩ := hx
      obtain ⟨v₂, u₂, h₂, k₂, l₂⟩ := hy
      refine ⟨v₁ * v₂, u₁ * u₂, ?_, ?_, ?_⟩
      · rw [Mσ.add]
        exact (grp_mul Pσ.m.cart _ _ hb1 v₁ v₂ (Mσ.pt x) (Mσ.pt y) h₁.symm h₂.symm).symm
      · rw [map_add, Mσ'.add]
        exact (grp_mul m'.cart _ _ hb2 u₁ u₂ _ _ k₁.symm k₂.symm).symm
      · rw [abPart_mul]
        let x₀ : Over.mk ((spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap σ) ≫ spMap e₂) ⟶ P₁.tB.G :=
          Over.homMk (u₁.left ≫ mP.φ) (hx0 u₁)
        let y₀ : Over.mk ((spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap σ) ≫ spMap e₂) ⟶ P₁.tB.G :=
          Over.homMk (u₂.left ≫ mP.φ) (hx0 u₂)
        rw [← grp_mul mP.cart _ _ rfl u₁ u₂ x₀ y₀ rfl rfl]
        exact grp_mul mBσ.cart _ _ hb3.symm _ _ x₀ y₀ l₁ l₂
  obtain ⟨v₀, u₀, h₀, k₀, l₀⟩ := key x
  have hv' : v = v₀ := lift_unique Pσ.m.cart.1 _ _ (hv.trans h₀.symm)
  have hu' : u = u₀ := lift_unique m'.cart.1 _ _ (hu.trans k₀.symm)
  rw [hv', hu']
  exact l₀

end GlobalTheory.CompanionTheory.Ar.TanCompare
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianQuotientLineBundleGauge
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.AdTr

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar.Flat.FrGauge
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X)
  {k : Type} [Field k] (x : Sp k ⟶ X)

abbrev sqU : Over.mk ((GF t x ⊗ GF t x).hom ≫ x) ⟶ t.G ⊗ t.G :=
  lift (sqPr t x (fst _ _)) (sqPr t x (snd _ _))

theorem sqPt_left_fst (a : t.G ⊗ t.G ⟶ t.G) :
    (sqPt t x a).left ≫ pullback.fst t.G.hom x = sqMap t x ≫ a.left :=
  pullback.lift_fst _ _ _

theorem fib_ext {T : Over (Sp k)} {a b : T ⟶ GF t x}
    (h : a.left ≫ pullback.fst t.G.hom x = b.left ≫ pullback.fst t.G.hom x) : a = b := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext h
  exact (Over.w a).trans (Over.w b).symm

theorem sqPt_psum {n : ℕ} (xs : Fin n → (t.G ⊗ t.G ⟶ t.G)) (I : Finset (Fin n)) :
    sqPt t x (psum t.G xs I) = psum (GF t x) (fun i => sqPt t x (xs i)) I := by
  apply fib_ext
  rw [sqPt_left_fst]
  refine Eq.symm (psum_push (isGrpPullback_pullback t.G x) _ xs (sqU t x) (fun i => ?_) I)
  apply Over.OverMorphism.ext
  exact sqPt_left_fst t x (xs i)

theorem sqPt_fst : sqPt t x (fst t.G t.G) = fst (GF t x) (GF t x) := by
  apply fib_ext
  rw [sqPt_left_fst]
  show (sqU t x ≫ fst t.G t.G).left = _
  rw [lift_fst]
  rfl

theorem sqPt_snd : sqPt t x (snd t.G t.G) = snd (GF t x) (GF t x) := by
  apply fib_ext
  rw [sqPt_left_fst]
  show (sqU t x ≫ snd t.G t.G).left = _
  rw [lift_snd]
  rfl

theorem sqPt_comp (b : t.G ⊗ t.G ⟶ t.G) (c : t.G ⟶ t.G) :
    sqPt t x (b ≫ c) = sqPt t x b ≫ (Over.pullback x).map c := by
  apply fib_ext
  rw [sqPt_left_fst, Over.comp_left, Over.comp_left, Category.assoc]
  have A : ((Over.pullback x).map c).left ≫ pullback.fst t.G.hom x = pullback.fst t.G.hom x ≫ c.left :=
    pullback.lift_fst _ _ _
  rw [A, ← Category.assoc (Over.Hom.left (sqPt t x b)), sqPt_left_fst]
  simp only [Category.assoc]

theorem psum_comp_hom {S : Scheme.{0}} {A B : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
    (q : A ⟶ B) [IsMonHom q] {T : Over S} {n : ℕ} (ys : Fin n → (T ⟶ A)) (I : Finset (Fin n)) :
    psum A ys I ≫ q = psum B (fun i => ys i ≫ q) I :=
  psum_hom (MonoidHom.mk' (· ≫ q) fun a b => MonObj.mul_comp a b q) ys I

theorem comp_psum {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B]
    {T T' : Over S} (U : T' ⟶ T) {n : ℕ} (ys : Fin n → (T ⟶ B)) (I : Finset (Fin n)) :
    U ≫ psum B ys I = psum B (fun i => U ≫ ys i) I :=
  psum_hom (preHom U) ys I

section Quot

variable {t x} (Q : AbQuot t x)

abbrev qL : GF t x ⊗ GF t x ⟶ Q.tB.G ⊗ Q.tB.G :=
  lift (fst (GF t x) (GF t x) ≫ Q.q) (snd (GF t x) (GF t x) ≫ Q.q)

theorem sqPt_psum_q {n : ℕ} (xs : Fin n → (t.G ⊗ t.G ⟶ t.G)) (ys : Fin n → (Q.tB.G ⊗ Q.tB.G ⟶ Q.tB.G))
    (h : ∀ i, sqPt t x (xs i) ≫ Q.q = qL Q ≫ ys i) (I : Finset (Fin n)) :
    (sqPt t x (psum t.G xs I)).left ≫ Q.q.left = qq Q ≫ (psum Q.tB.G ys I).left := by
  haveI := Q.q_hom
  have e : sqPt t x (psum t.G xs I) ≫ Q.q = qL Q ≫ psum Q.tB.G ys I := by
    rw [sqPt_psum, psum_comp_hom, comp_psum]
    exact congrArg (fun z => psum Q.tB.G z I) (funext h)
  exact congrArg (fun z => z.left) e

theorem sqPt_fst_q : sqPt t x (fst t.G t.G) ≫ Q.q = qL Q ≫ fst Q.tB.G Q.tB.G := by
  rw [sqPt_fst, lift_fst]

theorem sqPt_snd_q : sqPt t x (snd t.G t.G) ≫ Q.q = qL Q ≫ snd Q.tB.G Q.tB.G := by
  rw [sqPt_snd, lift_snd]

theorem sqPt_act_q {b : t.G ⊗ t.G ⟶ t.G} {b' : Q.tB.G ⊗ Q.tB.G ⟶ Q.tB.G}
    (h : sqPt t x b ≫ Q.q = qL Q ≫ b') (a : 𝓞 E) :
    sqPt t x (b ≫ t.act.act a) ≫ Q.q = qL Q ≫ b' ≫ Q.tB.act.act a := by
  rw [sqPt_comp, Category.assoc, Q.act_q, ← Category.assoc, h, Category.assoc]

end Quot

theorem adF_fst (a : 𝓞 E) (i : ULift (Finset (Fin 2)) ⊕ ULift (Finset (Fin 2))) :
    adF t x a i ≫ pullback.fst t.G.hom x = sqMap t x ≫ Sum.elim (cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)])
      (cφG t ![fst t.G t.G ≫ t.act.act a, snd t.G t.G]) i := by
  rcases i with I | I
  · exact sqPt_left_fst t x _
  · exact sqPt_left_fst t x _

theorem adF_q {t : SAB H X} {x : Sp k ⟶ X} (Q : AbQuot t x) (a : 𝓞 E) (i : ULift (Finset (Fin 2)) ⊕ ULift (Finset (Fin 2))) :
    adF t x a i ≫ Q.q.left = qq Q ≫ Sum.elim (cφG Q.tB ![fst Q.tB.G Q.tB.G, snd Q.tB.G Q.tB.G ≫ Q.tB.act.act (H.bar a)])
      (cφG Q.tB ![fst Q.tB.G Q.tB.G ≫ Q.tB.act.act a, snd Q.tB.G Q.tB.G]) i := by
  rcases i with I | I
  · refine sqPt_psum_q Q _ _ (fun i => ?_) I.down
    fin_cases i
    · exact sqPt_fst_q Q
    · exact sqPt_act_q Q (sqPt_snd_q Q) _
  · refine sqPt_psum_q Q _ _ (fun i => ?_) I.down
    fin_cases i
    · exact sqPt_act_q Q (sqPt_fst_q Q) _
    · exact sqPt_snd_q Q

theorem adjunction_ratio : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X) (Q : AbQuot t x) (d d' : ℕ) (g : GermAt t x d) (gB : GermAt Q.tB (𝟙 (Sp k)) d'), ∀ (w : LB.Iso (t.PP.L.pull (pullback.fst t.G.hom x)) (Q.tB.PP.L.pull Q.q.left)), w.IsGen → ∀ (a : 𝓞 E) (wL : AdTy t a) (wB : AdTy Q.tB a), wL.IsGen → wB.IsGen → ∃ u : Γ((GF t x ⊗ GF t x).left, ⊤)ˣ, Tr w (adF t x a) (fun i => sqMap t x ≫ Sum.elim (cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)]) (cφG t ![fst t.G t.G ≫ t.act.act a, snd t.G t.G]) i) (fun i => qq Q ≫ Sum.elim (cφG Q.tB ![fst Q.tB.G Q.tB.G, snd Q.tB.G Q.tB.G ≫ Q.tB.act.act (H.bar a)]) (cφG Q.tB ![fst Q.tB.G Q.tB.G ≫ Q.tB.act.act a, snd Q.tB.G Q.tB.G]) i) (Sum.elim (cε 2) fun I => -cε 2 I) (LB.pullGen t.PP.L _ _ wL (sqMap t x)) (LB.pullGen Q.tB.PP.L _ _ wB (qq Q)) u := by
  intro E _ _ _ H _ _ X t k _ _ p _ _ x Q d d' g gB w hw a wL wB hL hB
  exact GlobalTheory.T.generator_ratio_unit_exists t.G.left Q.tB.G.left (GF t x).left t.PP.L Q.tB.PP.L (pullback.fst t.G.hom x) Q.q.left
    t.PP.isLB Q.tB.PP.isLB w hw _ _ (adF t x a) _ _ _ _ _ (adF_fst t x a) (adF_q Q a)
    (LB.isGen_pullGen _ _ _ _ hL _) (LB.isGen_pullGen _ _ _ _ hB _)

end GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.AdTr
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AmpleHeightBoundsStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ample_height_bounds : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (d : ℕ), IsArithVar (mCoordIdeal y) d → Birational y → ∀ A : HermLine ι, IsSmoothHerm A → AmpleQ y A.a → (∃ C : ℝ, ∀ (L : Type) [Field L] [NumberField L], ∀ w ∈ ptsOver L (mCoordIdeal y), -C ≤ lineHt A L w) ∧ ∀ B : HermLine ι, IsSmoothHerm B → ∃ n C : ℝ, 0 ≤ n ∧ ∀ (L : Type) [Field L] [NumberField L], ∀ w ∈ ptsOver L (mCoordIdeal y), |lineHt B L w| ≤ n * lineHt A L w + C := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Ht.AmpleBd.height_bound | exact GlobalTheory.CompanionTheory.Ar.Ht.AmpleBd.height_bound | (intros; apply GlobalTheory.CompanionTheory.Ar.Ht.AmpleBd.height_bound <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarCommonCover
section
open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.JoinModel

theorem exists_normal_common_model : ∀ (K₁ : Type) [Fintype K₁] (ι₁ : K₁ → Type) [∀ k, Fintype (ι₁ k)] (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)] (Ω₁ Ω₂ Ω : Type) [Field Ω₁] [Field Ω₂] [Field Ω] [CharZero Ω] (i₁ : Ω₁ →+* Ω) (i₂ : Ω₂ →+* Ω) (y₁ : (Σ k, ι₁ k) → Ω₁) (y₂ : (Σ k, ι₂ k) → Ω₂) (d : ℕ) (X₁ X₂ : Scheme.{0}) (ξ₁ : Spec (CommRingCat.of Ω₁) ⟶ X₁) (ξ₂ : Spec (CommRingCat.of Ω₂) ⟶ X₂), IsArithVar (mCoordIdeal y₁) d → IsArithVar (mCoordIdeal y₂) d → Birational y₁ → Birational y₂ → FiniteDimensional i₁.fieldRange Ω → FiniteDimensional i₂.fieldRange Ω → (∀ q : X₁, genPt ξ₁ ⤳ q) → (∀ q : X₂, genPt ξ₂ ⤳ q) → CoordTie ℤ ξ₁ (fun c' : (k : K₁) → ι₁ k => ∏ k, y₁ ⟨k, c' k⟩) → CoordTie ℤ ξ₂ (fun c' : (k : K₂) → ι₂ k => ∏ k, y₂ ⟨k, c' k⟩) → ∃ (K : Type) (_ : Fintype K) (ι : K → Type) (_ : ∀ k, Fintype (ι k)) (κ₁ : K₁ → K) (v₁ : (Σ k, ι₁ k) → Σ k, ι k) (κ₂ : K₂ → K) (v₂ : (Σ k, ι₂ k) → Σ k, ι k) (y : (Σ k, ι k) → Ω) (Z : Scheme.{0}) (ξ : Spec (CommRingCat.of Ω) ⟶ Z) (h₁ : Z ⟶ X₁) (h₂ : Z ⟶ X₂), IsBlockMap κ₁ v₁ ∧ IsBlockMap κ₂ v₂ ∧ y ∘ v₁ = (fun p => i₁ (y₁ p)) ∧ y ∘ v₂ = (fun p => i₂ (y₂ p)) ∧ IsArithVar (mCoordIdeal y) d ∧ Birational y ∧ (∀ q : Z, genPt ξ ⤳ q) ∧ CoordTie ℤ ξ (fun c' : (k : K) → ι k => ∏ k, y ⟨k, c' k⟩) ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z ∧ GlobalTheory.CompanionTheory.Ar.Dominates ξ ξ₁ h₁ i₁ ∧ GlobalTheory.CompanionTheory.Ar.Dominates ξ ξ₂ h₂ i₂ ∧ IntermediateField.relfinrank (blockFnField (y ∘ v₁)) (blockFnField y) = Module.finrank i₁.fieldRange Ω ∧ IntermediateField.relfinrank (blockFnField (y ∘ v₂)) (blockFnField y) = Module.finrank i₂.fieldRange Ω :=
  @PositivityTheory.UnitarySelfGeneration.j_normal_of GlobalTheory.T.finite_extension_coords_compare

end GlobalTheory.CompanionTheory.Ar.JoinModel
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DedekindConstantsDegreeTwoStatement
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dedekind_constants_degree_two : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∀ d : ℕ, IsArithVar (mCoordIdeal y) (d + 1) → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsDedekindDomain A] [Module.Finite ℤ A], Function.Injective (algebraMap A Ω) → HasConstants ℤ A y → ∀ (p : ℕ), p.Prime → ∀ (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω] (ϖ : O), Irreducible ϖ → ∀ (E : Type) [AddCommGroup E] [Module Ω E] (r : ℕ) (w : Module.Basis (Fin r) Ω E) (L L' : Lat ξ E) (Q : LocPair J ℤ (Fin r)), IsLatFlagPair y (overPrime ξ p) L L' w Q → (∀ q : Cpt ξ, q ∈ overPrime ξ p → ¬ InFibre ξ p q → L q = L' q) → ∃ (B B' : ChartBundle O (segreVec y) r E) (v v' : Module.Basis (Fin r) Ω E), (∀ c, segreVec y c ≠ 0 → ∀ z, (z ∈ B.lat c ↔ ∀ q : Cpt ξ, InChart ξ (segreVec y) c q → (∀ o : O, algebraMap O Ω o ∈ regAt ξ q) → z ∈ L q) ∧ (z ∈ B'.lat c ↔ ∀ q : Cpt ξ, InChart ξ (segreVec y) c q → (∀ o : O, algebraMap O Ω o ∈ regAt ξ q) → z ∈ L' q)) ∧ IsModelOver (pointIdeal O y) d ∧ SameGenericFibre ϖ B B' ∧ IsFlagPair ϖ y B B' v v' Q.x Q.x' (Q.map (Int.castRingHom O)).f (Q.map (Int.castRingHom O)).g := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.LatFlag.flag_pair_of_lat | exact GlobalTheory.CompanionTheory.Ar.Num.LatFlag.flag_pair_of_lat | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.LatFlag.flag_pair_of_lat <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DeltaExpansionRestrictionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.delta_expansion_restriction : ∀ (X0 : Scheme.{0}) (G : Over X0) [GrpObj G] (k : Type) [Field k] (x : Sp k ⟶ X0) (p : ℕ) (hp : 1 ≤ p) (B : Type) [CommRing B] [Algebra k B] (z : overAt x B ⟶ G) (W : (pullback G.hom x).Opens) (hW : ⊤ ≤ xkZ G x z ⁻¹ᵁ W) (c : Fin (p + 1) → Γ(pullback G.hom x, W)) (f : Γ(Ym G x p, prZ G x p ⁻¹ᵁ W)) (v : B), f = ∑ i, ((prZ G x p).app W).hom (c i) * dltOn G x p _ ^ (i : ℕ) → ∀ hr : ⊤ ≤ rQ G x p z ⁻¹ᵁ (prZ G x p ⁻¹ᵁ W), ((rQ G x p z).appLE _ ⊤ hr).hom f = toΓ _ (1 + dQ B p ^ p * algebraMap B _ v) → ((xkZ G x z).appLE W ⊤ hW).hom (c (Fin.last p)) = toΓ B v := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Coc.coef_pull | exact GlobalTheory.CompanionTheory.Ar.Coc.coef_pull | (intros; apply GlobalTheory.CompanionTheory.Ar.Coc.coef_pull <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueRationalStatement
section
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo

namespace GlobalTheory.CompanionTheory.Ar.Link

theorem existsUnique_rat (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] :
    ReciprocityTheory.ChartRestriction.G.AI.I1.ExistsUniqueStatement ℚ ι :=
  (GlobalTheory.CompanionTheory.Ar.PB.Known.fieldNumbers ℚ K ι).1

end GlobalTheory.CompanionTheory.Ar.Link
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatHermRootLineDegreeStatement
section
open MvPolynomial NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_herm_root_line_degree : GlobalTheory.CompanionTheory.Ar.PB.Inputs → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M : GlobalTheory.CompanionTheory.Ar.Top.RootModel Ψ N) (S : GlobalTheory.CompanionTheory.Ar.PB.AnSys (GlobalTheory.CompanionTheory.Ar.Top.dimFl Ψ N) (Option (Ψ × Fin N))) (Re : GlobalTheory.CompanionTheory.Ar.PB.Realis S M.P) (τ : Ψ) (i₀ : Fin N) (F : Type) [Field F] [NumberField F] (φ : F →+* M.Ω) (A : HermLine M.ι) (Sf : FlatHerm M.y φ A), OverInt M.y φ → IsSmoothHerm A → (i₀ : ℕ) + 1 = N → 0 < S.t₀ → A.a = ∑ i, M.xdeg (τ, i) → (∀ (σ : Ψ) (i : Fin N), M.xdeg (σ, i) + (Re.ref (some (σ, i))).a = if h : 0 < (i : ℕ) then (Re.ref (some (σ, ⟨i - 1, by omega⟩))).a else 0) → (∀ t, 0 < t → t ≤ S.t₀ → ∀ (σ : Ψ) (i : Fin N), ∀ z ∈ mcPts M.P, (M.x t (σ, i)).h z * (Re.line (some (σ, i)) t).h z = if h : 0 < (i : ℕ) then (Re.line (some (σ, ⟨i - 1, by omega⟩)) t).h z else 1) → (∀ x, Re.π x ∈ S.open' → -Real.log (A.h (Re.R.lift x x)) = Real.log ((Re.ref (some (τ, i₀))).h (Re.R.lift x x)) + S.ph (some (τ, i₀)) (Re.π x)) → ∃ R : RootFlat M τ, R.ht = Sf.ht := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.exists_rootFlat_of_realis | exact GlobalTheory.CompanionTheory.Ar.Flat.exists_rootFlat_of_realis | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.exists_rootFlat_of_realis <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FractionFieldCoordsGeneratedStatement
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fraction_field_coords_generated : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (κ : Type) (x : κ → Ω),
    CoordTie ℤ ξ x → ∀ c : κ, x c ≠ 0 → ∀ a : Ω, ∃ s ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c),
      ∃ t ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c), t ≠ 0 ∧ a = s / t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ChartFrac.exists_eq_div_chart | exact GlobalTheory.CompanionTheory.Ar.ChartFrac.exists_eq_div_chart | (intros; apply GlobalTheory.CompanionTheory.Ar.ChartFrac.exists_eq_div_chart <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FundamentalDomainRiemannFormStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fundamental_domain_riemann_form : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) → (∀ l ∈ Λ, ∀ l' ∈ Λ, ∃ k : ℤ, (l ⬝ᵥ Hm.mulVec (star l')).im = k) → (∀ w : Fin g → ℂ, (∀ l ∈ Λ, ∃ k : ℤ, (w ⬝ᵥ Hm.mulVec (star l)).im = k) → w ∈ Λ) → ∀ Fd : Set (Fin g → ℂ), IsAddFundamentalDomain Λ Fd volume → (volume Fd).toReal * ‖Hm.det‖ = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.SelfDualCovol.volume_mul_norm_det_eq_one | exact GlobalTheory.CompanionTheory.Ar.Sl.SelfDualCovol.volume_mul_norm_det_eq_one | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.SelfDualCovol.volume_mul_norm_det_eq_one <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericOfSmoothSurjectiveStatement
section
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
open Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_of_smooth_surjective : ∀ (K : Type) [Field K] (X₀ X' : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X₀) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (π : X' ⟶ X₀) (s' : X' ⟶ Spec (CommRingCat.of K)), Smooth s' → ξ' ≫ π = ξ → IsCptGen ξ → Function.Surjective (π.stalkMap (genPt ξ')).hom → IsCptGen ξ' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.CptLift.isCptGen_of_smooth_of_surjective | exact GlobalTheory.CompanionTheory.Ar.CptLift.isCptGen_of_smooth_of_surjective | (intros; apply GlobalTheory.CompanionTheory.Ar.CptLift.isCptGen_of_smooth_of_surjective <;> assumption)
end

