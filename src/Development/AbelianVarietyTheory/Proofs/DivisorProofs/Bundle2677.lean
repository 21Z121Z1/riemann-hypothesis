import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2554
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0078
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0024
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2557
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2464
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAbelianSchemeThick
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2558
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0031
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1481
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2248
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0065
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2540
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2351
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2559
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2290
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupEndomorphismUniqueOfThickeningAc
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
namespace GlobalTheory.Mum

theorem actsAs_unique : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (b : D.toPre.P.A ⟶ D.toPre.P.A) (h : D.toPre.X → D.toPre.X) (g g' : G ⟶ G), IsMonHom g → IsMonHom g' → ActsAs U.toUnifPre b h g → ActsAs U.toUnifPre b h g' → g = g' := by
  intro R _ _ _ hR D A G _ _ hG U b h g g' hg hg' H H'
  have : IsNoetherianRing R := hR.1.1
  have : Smooth G.hom := hG.smooth
  have : GeometricallyConnected G.hom := hG.geomConnected
  have : IsSeparated G.hom := hG.separated
  refine GlobalTheory.AbelianPartIso.hom_eq_of_map_eq (IsLocalRing.maximalIdeal_le_jacobson _) G g g' fun e => ?_
  obtain ⟨q1, t, ht, i1⟩ := H e
  obtain ⟨q2, t', ht', i2⟩ := H' e
  have htt : t = t' := GlobalTheory.LinearUnifCheck.torusEndOf_unique ht ht'
  have := (U.gt e).i_hom
  exact GlobalTheory.LinearUnifIso.hom_ext_torus (U.gt e) (U.gt e) GlobalTheory.globalFns_holds _ _
    (q1.trans q2.symm) (i1.trans (htt ▸ i2.symm))

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedModelBaseChangeCompleteDvrExtensionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisedModel_baseChange_complete_dvr_extension : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsDiscreteValuationRing V₂] [Algebra (FractionRing V₂) (PadicAlgCl p)], IsAdicComplete (IsLocalRing.maximalIdeal V₂) V₂ → (∀ x : FractionRing V₂, ‖algebraMap (FractionRing V₂) (PadicAlgCl p) x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V₂ (FractionRing V₂))) → ∀ σ : FractionRing u.V →+* FractionRing V₂, (algebraMap (FractionRing V₂) (PadicAlgCl p)).comp σ = algebraMap (FractionRing u.V) (PadicAlgCl p) →
  ∃ (u' : ρ.UTest p y₀) (τ : FractionRing V₂ →+* FractionRing u'.V) (e : u'.D.toPre.X ≃+ u.D.toPre.X) (T : (TFK (R := u'.V) (PadicAlgCl p) ⟶ u'.A.A) ≃ (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)),
    (algebraMap (FractionRing u'.V) (PadicAlgCl p)).comp τ = algebraMap (FractionRing V₂) (PadicAlgCl p) ∧
    (∀ χ r, u.PsiNorm (e χ) r → u'.PsiNorm χ r) ∧
    (∀ x, (T x).left ≫ u.φ = x.left ≫ u'.φ) ∧
    (∀ (m : ℕ) (pk' : QkPt u'.D.toPre (PadicAlgCl p) m) x', 1 ≤ m → QkToAkU u'.U.toUnifPre (PadicAlgCl p) m pk' x' → ∃ pk : QkPt u.D.toPre (PadicAlgCl p) m, pk.y = e pk'.y ∧ QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk (T x')) ∧
    (∀ (m : ℕ) (pk : QkPt u.D.toPre (PadicAlgCl p) m) x, 1 ≤ m → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x → ∃ pk' : QkPt u'.D.toPre (PadicAlgCl p) m, e pk'.y = pk.y ∧ QkToAkU u'.U.toUnifPre (PadicAlgCl p) m pk' (T.symm x)) := by
  first | exact @GlobalTheory.Poinc.UTestBaseChange.baseChange | exact GlobalTheory.Poinc.UTestBaseChange.baseChange | (intros; apply GlobalTheory.Poinc.UTestBaseChange.baseChange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedPointOverLabelPowRNEqOneStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformised_point_over_label_pow_rN_eq_one : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (b : S.Gam) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), x.left ≫ u.φ = spMap y₀ ≫ (ρ.pt b).left → x ^ (S.r * S.N) = 1 := by
  first | exact @GlobalTheory.LabelTorsion.pow_eq_one_of_over_label | exact GlobalTheory.LabelTorsion.pow_eq_one_of_over_label | (intros; apply GlobalTheory.LabelTorsion.pow_eq_one_of_over_label <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedSemiAbelianSplitModMaximalIdeal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.SplitRed

theorem splitOver_of_unif : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))), Unif (maximalIdeal V₁) D₀ A₀ G₀ → IsSemiAbelian G₀ → GlobalTheory.LN.SplitOver G₀ (maximalIdeal V₁) := by
  intro V₁ _ _ _ _ D₀ G₀ _ _ A₀ U _
  obtain ⟨E, -, -, -, -, hE⟩ := GlobalTheory.gtCoord_isGt V₁ (IsLocalRing.maximalIdeal V₁) D₀.toPre 0 G₀ ⟨U.gt 0⟩
  have key : ∀ J : Ideal V₁, J = IsLocalRing.maximalIdeal V₁ →
      ∀ S : SplitExt (Spec (CommRingCat.of (V₁ ⧸ J))),
        S.IsGt ((Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).obj G₀) →
        GlobalTheory.LN.SplitOver G₀ (IsLocalRing.maximalIdeal V₁) := by
    rintro J rfl S hS
    exact ⟨S, hS⟩
  exact key _ (pow_one _) E hE

end GlobalTheory.SplitRed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformiserZpowMulUnitExponentUniqueStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformiser_zpow_mul_unit_exponent_unique : ∀ {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}, Irreducible ϖ → ∀ (a b : ℤ) (w w' : Vˣ), algebraMap V (FractionRing V) ϖ ^ a * algebraMap V (FractionRing V) (w : V) = algebraMap V (FractionRing V) ϖ ^ b * algebraMap V (FractionRing V) (w' : V) → a = b := by
  first | exact @GlobalTheory.exponent_uniformiser_unique | exact GlobalTheory.exponent_uniformiser_unique | (intros; apply GlobalTheory.exponent_uniformiser_unique <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitCocycleLiftObstructionPullbackNaturalityStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitCocycleLiftObstruction_pullback_naturality : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (C' : Type) [Category.{0} C'] (F' : C' ⥤ CommAlgCat.{0} R₀) (L' : Pre I π F') (n : CoefMap (RingHom.id R₀) F F') (l : ∀ T : C', L.B (n.G.obj T) →ₐ[R] L'.B T) (u : ∀ (T T' : C) (_ : T ⟶ T'), (F.obj T')ˣ) (u' : ∀ (T T' : C') (_ : T ⟶ T'), (F'.obj T')ˣ) (c : GlobalTheory.CatCoh.H2 (ext R₁ F)), L.IsLift L' n l → L.IsNat L' n l → (∀ T T' a, (u' T T' a : F'.obj T') = n.α T' (u _ _ (n.G.map a) : F.obj (n.G.obj T'))) → IsObU L α u c → IsObU L' α u' ((extMap R₁ n).pull2 c) := by
  first | exact @GlobalTheory.LBObs.isObU_pull | exact GlobalTheory.LBObs.isObU_pull | (intros; apply GlobalTheory.LBObs.isObU_pull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitCocycleLiftObstructionUniqueStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitCocycleLiftObstruction_unique : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (u : ∀ (T T' : C) (_ : T ⟶ T'), (F.obj T')ˣ) (c c' : GlobalTheory.CatCoh.H2 (ext R₁ F)), IsObU L α u c → IsObU L α u c' → c = c' := by
  first | exact @GlobalTheory.LBObs.isObU_unique | exact GlobalTheory.LBObs.isObU_unique | (intros; apply GlobalTheory.LBObs.isObU_unique <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitCocycleLiftOfObstructionEqZeroStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitCocycle_lift_of_obstruction_eq_zero : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (u : ∀ (T T' : C) (_ : T ⟶ T'), (F.obj T')ˣ), IsObU L α u 0 → ∃ v : ∀ (T T' : C) (_ : T ⟶ T'), (L.B T')ˣ, (∀ T T' a, L.p T' (v T T' a : L.B T') = (u T T' a : F.obj T')) ∧ ∀ (T T' T'' : C) (a : T ⟶ T') (b : T' ⟶ T''), (v T T'' (a ≫ b) : L.B T'') = L.ρ b (v T T' a : L.B T') * (v T' T'' b : L.B T'') := by
  first | exact @GlobalTheory.LBLift.lift_of_isObU_zero | exact GlobalTheory.LBLift.lift_of_isObU_zero | (intros; apply GlobalTheory.LBLift.lift_of_isObU_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFrameModelVacuumStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_weil_action_pure_tensor_le_majorant : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ (q : ℕ) (x y : Fin q → Fin n → E), IsFrameU σ X.J x y →
    ∀ (M₁ : Model σ X W) (blk : Fin q → Finset (Fin n × Fin d)) (e : Fn F n d →ₗ[ℂ] Fn F n d),
    M₁.IsGood B.ψ → IsFrameCo σ X.J W.J x y M₁.co blk → IsEv B M M₁ 1 1 ∅ e →
    ∀ Cc : Set (UA σ X.J), IsCompact Cc → ∀ c : ℝ, 0 < c → ∀ φ ∈ SB (Fin n × Fin d → Af F),
    ∃ A : ℕ, ∀ N : ℕ, ∃ (C : ℝ) (k : ℕ), ∀ (f : SInf F (Fin n × Fin d)) (t : Fin q → ℝ) (a κ : UA σ X.J) (h : UA σ W.J),
      (∀ i, c ≤ t i) → IsTorusU x y t a → κ ∈ Cc → ∃ m : ℕ, 1 ≤ m ∧ (m : ℝ) ≤ C * (ht h : ℝ) ^ k ∧
        ∀ ξ : Fin n × Fin d → F, ‖e (om (a * κ, h) (pureA F f φ)) (fun j => algebraMap F (AF F) (ξ j))‖ ≤
          C * semK (Fin n × Fin d) k f * (ht h : ℝ) ^ k * majI blk A N m t ξ := by
  first | exact @GlobalTheory.ThKTorus.frameMajorant | exact GlobalTheory.ThKTorus.frameMajorant | (intros; apply GlobalTheory.ThKTorus.frameMajorant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryGroupMeasureDecomposition
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovTop.VolUp.MassUp

theorem inv_facts {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {κ : Type} {p q : κ → ℕ}
    {Ψ : Finset (E →+* ℂ)} {G : Matrix (Fin r) (Fin r) E} {x : Frame Ψ r} {σ : κ ≃ Ψ}
    {A : ∀ ρ, Matrix (Fin (p ρ) ⊕ Fin (q ρ)) (Fin r) ℂ} {e : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ) ≃ Fin r}
    (hI : IsIdent p q Ψ G x σ A e) (ρ : κ) :
    (permM (e ρ))ᵀ * A ρ * mat x (σ ρ) = 1 ∧ mat x (σ ρ) * ((permM (e ρ))ᵀ * A ρ) = 1 ∧
    A ρ * (mat x (σ ρ) * (permM (e ρ))ᵀ) = 1 ∧ mat x (σ ρ) * (permM (e ρ))ᵀ * A ρ = 1 := by
  have h0 := (hI ρ).2
  have h1 : (permM (e ρ))ᵀ * A ρ * mat x (σ ρ) = 1 := by rw [Matrix.mul_assoc, h0, transpose_mul_permM]
  have h2 : mat x (σ ρ) * ((permM (e ρ))ᵀ * A ρ) = 1 := mul_eq_one_comm.1 h1
  refine ⟨h1, h2, ?_, by rw [Matrix.mul_assoc, h2]⟩
  rw [← Matrix.mul_assoc, h0, permM_mul_transpose]

theorem det_ne {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {κ : Type} {p q : κ → ℕ}
    {Ψ : Finset (E →+* ℂ)} {G : Matrix (Fin r) (Fin r) E} {x : Frame Ψ r} {σ : κ ≃ Ψ}
    {A : ∀ ρ, Matrix (Fin (p ρ) ⊕ Fin (q ρ)) (Fin r) ℂ} {e : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ) ≃ Fin r}
    (hI : IsIdent p q Ψ G x σ A e) (ρ : κ) : G.det ≠ 0 := by
  obtain ⟨-, -, h3, h4⟩ := inv_facts hI ρ
  set B := mat x (σ ρ) * (permM (e ρ))ᵀ
  have hJ := GlobalTheory.UpqTopology.jpq_sq (P := p ρ) (Q := q ρ)
  have key : (-(G.map (σ ρ).1)ᵀ) * (B * Formalism.UG.Jpq (p ρ) (q ρ) * Bᴴ) = 1 := by
    rw [← (hI ρ).1]
    calc (A ρ)ᴴ * Formalism.UG.Jpq (p ρ) (q ρ) * A ρ * (B * Formalism.UG.Jpq (p ρ) (q ρ) * Bᴴ)
        = (A ρ)ᴴ * (Formalism.UG.Jpq (p ρ) (q ρ) * ((A ρ * B) * (Formalism.UG.Jpq (p ρ) (q ρ) * Bᴴ))) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [h3, Matrix.one_mul, ← Matrix.mul_assoc (Formalism.UG.Jpq (p ρ) (q ρ)), hJ, Matrix.one_mul,
            ← Matrix.conjTranspose_mul, h4, Matrix.conjTranspose_one]
  have hd := Matrix.det_ne_zero_of_right_inverse key
  rw [Matrix.det_neg, Matrix.det_transpose] at hd
  have hd' : (G.map (σ ρ).1).det ≠ 0 := fun h => hd (by rw [h, mul_zero])
  intro h0
  apply hd'
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]

theorem perm_conj {ι : Type} [Fintype ι] [DecidableEq ι] {r : ℕ} (e : ι ≃ Fin r) (M : Matrix ι ι ℂ) (a b : Fin r) :
    ((permM e)ᵀ * M * permM e) a b = M (e.symm a) (e.symm b) := by
  simp [Matrix.mul_apply, permM, Equiv.apply_eq_iff_eq_symm_apply]

theorem preimage_frBall : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (κ : Type) (p q : κ → ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (σ : κ ≃ Ψ) (A : ∀ ρ, Matrix (Fin (p ρ) ⊕ Fin (q ρ)) (Fin r) ℂ) (e : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ) ≃ Fin r) (a₀ : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ)) (π : (∀ ρ, UpqT (p ρ) (q ρ)) → realSU Ψ G), IsIdent p q Ψ G x σ A e → IsProj p q Ψ G σ A a₀ π → ∀ ε : ℝ, π ⁻¹' frBall Ψ G x ε = Set.univ.pi (fun ρ => {u : UpqT (p ρ) (q ρ) | ∀ a b, ‖(sMat (a₀ ρ) u - 1) a b‖ < ε}) := by
  intro E _ _ _ r κ p q Ψ G x σ A e a₀ π hI hP ε
  ext b
  simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_setOf_eq, frBall]
  have key : ∀ ρ, (mat x (σ ρ))⁻¹ * (((π b).1 (σ ρ) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * mat x (σ ρ) - 1
      = (permM (e ρ))ᵀ * (sMat (a₀ ρ) (b ρ) - 1) * permM (e ρ) := by
    intro ρ
    obtain ⟨h1, -, -, -⟩ := inv_facts hI ρ
    have hinv : (mat x (σ ρ))⁻¹ = (permM (e ρ))ᵀ * A ρ := Matrix.inv_eq_left_inv h1
    rw [hinv, Matrix.mul_assoc (permM (e ρ))ᵀ (A ρ), hP b ρ]
    simp only [Matrix.mul_assoc, (hI ρ).2, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul,
      transpose_mul_permM]
  constructor
  · intro h ρ i j
    have := h (σ ρ) (e ρ i) (e ρ j)
    rwa [key ρ, perm_conj, Equiv.symm_apply_apply, Equiv.symm_apply_apply] at this
  · intro h τ i j
    obtain ⟨ρ, rfl⟩ := σ.surjective τ
    rw [key ρ, perm_conj]
    exact h ρ _ _
theorem exists_lift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (κ : Type) (p q : κ → ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (σ : κ ≃ Ψ) (A : ∀ ρ, Matrix (Fin (p ρ) ⊕ Fin (q ρ)) (Fin r) ℂ) (e : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ) ≃ Fin r), IsIdent p q Ψ G x σ A e → ∀ s : realSU Ψ G, ∃ b₀ : ∀ ρ, UpqT (p ρ) (q ρ), ∀ ρ, UpqT.mat (b₀ ρ) * A ρ = A ρ * ((s.1 (σ ρ) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) := by
  intro E _ _ _ r κ p q Ψ G x σ A e hI s
  have key : ∀ ρ, ∃ b : UpqT (p ρ) (q ρ), UpqT.mat b =
      A ρ * ((s.1 (σ ρ) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * (mat x (σ ρ) * (permM (e ρ))ᵀ) := by
    intro ρ
    rw [← Set.mem_range, GlobalTheory.UpqTopology.range_mat]
    show _ = _
    set Sm := ((s.1 (σ ρ) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)
    set Bm := mat x (σ ρ) * (permM (e ρ))ᵀ
    have hmem := ((GlobalTheory.SUVol.DensOne.mem_realSU_iff Ψ G s.1).1 s.2 (σ ρ)).1
    have h2 : Smᴴ * (G.map (σ ρ).1)ᵀ * Sm = (G.map (σ ρ).1)ᵀ := by
      have := congrArg Matrix.transpose hmem
      rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose] at this
      rw [Matrix.mul_assoc]
      exact this
    calc (A ρ * Sm * Bm)ᴴ * Formalism.UG.Jpq (p ρ) (q ρ) * (A ρ * Sm * Bm)
        = Bmᴴ * (Smᴴ * ((A ρ)ᴴ * Formalism.UG.Jpq (p ρ) (q ρ) * A ρ) * Sm) * Bm := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Bmᴴ * ((A ρ)ᴴ * Formalism.UG.Jpq (p ρ) (q ρ) * A ρ) * Bm := by
          rw [(hI ρ).1, Matrix.mul_neg, Matrix.neg_mul, h2]
      _ = (A ρ * Bm)ᴴ * Formalism.UG.Jpq (p ρ) (q ρ) * (A ρ * Bm) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Formalism.UG.Jpq (p ρ) (q ρ) := by
          rw [(inv_facts hI ρ).2.2.1, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  choose b hb using key
  refine ⟨b, fun ρ => ?_⟩
  rw [hb ρ, Matrix.mul_assoc (A ρ * _), (inv_facts hI ρ).2.2.2, Matrix.mul_one]
theorem constant_bound : ∀ (f r : ℕ) (ε : ℝ), 1 ≤ f → 1 ≤ r → 0 < ε → ((200 * (r : ℝ)) ^ (r ^ 2) * ε ^ (r ^ 2 - 1)) ^ f ≤ (1000 * (f : ℝ) * (r : ℝ) ^ 3) ^ (f * r ^ 2) * ((ε / (2 * ((f : ℝ) * (r : ℝ) ^ 2))) ^ (f * (r ^ 2 - 1)) / 2) := by
  intro f r ε hf hr hε
  have hf' : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hN : 1 ≤ f * r ^ 2 := by have := Nat.one_le_pow 2 r hr; nlinarith
  have hnN : f * (r ^ 2 - 1) ≤ f * r ^ 2 := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  have hL : ((200 * (r : ℝ)) ^ (r ^ 2) * ε ^ (r ^ 2 - 1)) ^ f =
      (200 * (r : ℝ)) ^ (f * r ^ 2) * ε ^ (f * (r ^ 2 - 1)) := by
    rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm (r ^ 2) f, mul_comm (r ^ 2 - 1) f]
  rw [hL, div_pow]
  generalize hN' : f * r ^ 2 = N at hN hnN
  generalize hn' : f * (r ^ 2 - 1) = n at hnN
  have hr2 : (1 : ℝ) ≤ (r : ℝ) ^ 2 := one_le_pow₀ hr'
  have ha1 : (1 : ℝ) ≤ 2 * ((f : ℝ) * (r : ℝ) ^ 2) := by nlinarith
  generalize ha : 2 * ((f : ℝ) * (r : ℝ) ^ 2) = a at ha1
  have ha0 : 0 < a := by linarith
  have e1 : 1000 * (f : ℝ) * (r : ℝ) ^ 3 = (5 / 2) * (200 * (r : ℝ) * a) := by rw [← ha]; ring
  have han : a ^ n ≤ a ^ N := pow_le_pow_right₀ ha1 hnN
  have hq : 0 ≤ 200 * (r : ℝ) * a := mul_nonneg (by positivity) ha0.le
  have h52 : (2 : ℝ) ≤ (5 / 2) ^ N := by
    calc (2 : ℝ) ≤ 5 / 2 := by norm_num
      _ = (5 / 2) ^ 1 := (pow_one _).symm
      _ ≤ (5 / 2) ^ N := pow_le_pow_right₀ (by norm_num) hN
  have key : (200 * (r : ℝ)) ^ N * a ^ N * 2 ≤ (1000 * (f : ℝ) * (r : ℝ) ^ 3) ^ N := by
    rw [e1, mul_pow (5 / 2 : ℝ), ← mul_pow (200 * (r : ℝ)) a N]
    have hp : 0 ≤ (200 * (r : ℝ) * a) ^ N := pow_nonneg hq _
    nlinarith
  have hεn : 0 < ε ^ n := pow_pos hε _
  have han0 : 0 < a ^ n := pow_pos ha0 _
  have hw : 0 ≤ ε ^ n / a ^ n / 2 := by positivity
  calc (200 * (r : ℝ)) ^ N * ε ^ n = ((200 * (r : ℝ)) ^ N * a ^ n * 2) * (ε ^ n / a ^ n / 2) := by
        field_simp
    _ ≤ ((200 * (r : ℝ)) ^ N * a ^ N * 2) * (ε ^ n / a ^ n / 2) := by
        gcongr
    _ ≤ _ := mul_le_mul_of_nonneg_right key hw

theorem massUp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (κ : Type) [Fintype κ] (p q : κ → ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (σ : κ ≃ Ψ) (A : ∀ ρ, Matrix (Fin (p ρ) ⊕ Fin (q ρ)) (Fin r) ℂ) (e : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ) ≃ Fin r) (a₀ : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ)) (π : (∀ ρ, UpqT (p ρ) (q ρ)) → realSU Ψ G) (m : ∀ ρ, Measure (UpqT (p ρ) (q ρ))), 1 ≤ r → 1 ≤ Ψ.card → IsIdent p q Ψ G x σ A e → Continuous π → IsProj p q Ψ G σ A a₀ π → (∀ (s : realSU Ψ G) (b₀ : ∀ ρ, UpqT (p ρ) (q ρ)), (∀ ρ, UpqT.mat (b₀ ρ) * A ρ = A ρ * ((s.1 (σ ρ) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) → ∀ b, π (b₀ * b) = s * π b) → (∀ ρ, IsMinf (m ρ)) → ∀ S : Set (realSU Ψ G), MeasurableSet S → Measure.pi m (π ⁻¹' S) ≤ ENNReal.ofReal ((1000 * (Ψ.card : ℝ) * (r : ℝ) ^ 3) ^ (Ψ.card * r ^ 2)) * riemHaar Ψ G x S := by
  intro E _ _ _ r κ _ p q Ψ G x σ A e a₀ π m hr hΨ hI hπc hP hT hm S hS
  classical
  haveI : ∀ ρ, IsTopologicalGroup (UpqT (p ρ) (q ρ)) := fun ρ => (GlobalTheory.UpqTopology.upq_lcsc _ _).1
  haveI : ∀ ρ, LocallyCompactSpace (UpqT (p ρ) (q ρ)) := fun ρ => (GlobalTheory.UpqTopology.upq_lcsc _ _).2.2.1
  haveI : ∀ ρ, SecondCountableTopology (UpqT (p ρ) (q ρ)) := fun ρ => (GlobalTheory.UpqTopology.upq_lcsc _ _).2.2.2.1
  haveI : ∀ ρ, BorelSpace (UpqT (p ρ) (q ρ)) := fun ρ => (GlobalTheory.UpqTopology.upq_lcsc _ _).2.2.2.2.1
  haveI : ∀ ρ, (m ρ).IsHaarMeasure := fun ρ => (hm ρ).1

  have hcard : Fintype.card κ = Ψ.card := by
    rw [Fintype.card_congr σ]; simp
  have hne : Nonempty κ := by
    rw [← Fintype.card_pos_iff, hcard]; omega
  obtain ⟨ρ₀⟩ := hne
  have hG : G.det ≠ 0 := det_ne hI ρ₀
  have hx : ∀ τ, (mat x τ).det ≠ 0 := by
    intro τ
    obtain ⟨ρ, rfl⟩ := σ.surjective τ
    exact Matrix.det_ne_zero_of_right_inverse (inv_facts hI ρ).2.1
  have hpq : ∀ ρ, p ρ + q ρ = r := by
    intro ρ; simpa using Fintype.card_congr (e ρ)
  have hπm : Measurable π := hπc.measurable
  set μ := Measure.pi m with hμ
  set ν := μ.map π with hν

  haveI hinv : ν.IsMulLeftInvariant := by
    constructor
    intro s
    obtain ⟨b₀, hb₀⟩ := exists_lift E r κ p q Ψ G x σ A e hI s
    rw [hν, Measure.map_map (measurable_const_mul s) hπm]
    have h : (fun y => s * y) ∘ π = π ∘ (fun b => b₀ * b) := funext fun b => (hT s b₀ hb₀ b).symm
    rw [h, ← Measure.map_map hπm (measurable_const_mul b₀), map_mul_left_eq_self]

  have hopen : ∀ ε, IsOpen (frBall Ψ G x ε) := by
    intro ε
    have hc : ∀ τ a b, Continuous fun s : realSU Ψ G =>
        ‖((mat x τ)⁻¹ * ((s.1 τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * mat x τ - 1) a b‖ := by
      intro τ a b
      have h1 : Continuous fun s : realSU Ψ G => ((s.1 τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) :=
        Units.continuous_val.comp ((continuous_apply τ).comp continuous_subtype_val)
      exact ((((continuous_const.matrix_mul h1).matrix_mul continuous_const).sub continuous_const).matrix_elem a b).norm
    have : frBall Ψ G x ε = ⋂ τ, ⋂ a, ⋂ b, {s : realSU Ψ G |
        ‖((mat x τ)⁻¹ * ((s.1 τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * mat x τ - 1) a b‖ < ε} := by
      ext s; simp [frBall]
    rw [this]
    exact isOpen_iInter_of_finite fun τ => isOpen_iInter_of_finite fun a =>
      isOpen_iInter_of_finite fun b => isOpen_lt (hc τ a b) continuous_const
  have h1mem : ∀ ε, 0 < ε → (1 : realSU Ψ G) ∈ frBall Ψ G x ε := by
    intro ε hε τ a b
    have : (mat x τ)⁻¹ * ((((1 : realSU Ψ G).1 τ : GL (Fin r) ℂ)) : Matrix (Fin r) (Fin r) ℂ) * mat x τ = 1 := by
      simp [Matrix.nonsing_inv_mul _ (hx τ).isUnit]
    rw [this, sub_self]; simpa using hε
  have hplace := fun ρ => GlobalTheory.T.measure_detOneFactor_nearIdentity_le (p ρ) (q ρ) (a₀ ρ) (m ρ) (hm ρ)
  choose εp hεp hbp using hplace
  obtain ⟨εl, hεl, hbl⟩ := GlobalTheory.T.riemannianHaar_frameBall_lower_bound E r Ψ G x hr hG hx
  set δ := Finset.univ.inf' ⟨ρ₀, Finset.mem_univ _⟩ εp with hδdef
  have hδ : 0 < δ := (Finset.lt_inf'_iff _).2 fun ρ _ => hεp ρ
  set ε := min δ εl / 2 with hεdef
  have hεm : ε < min δ εl := half_lt_self (lt_min hδ hεl)
  have hε : 0 < ε := half_pos (lt_min hδ hεl)
  have hεδ : ∀ ρ, ε < εp ρ := fun ρ =>
    lt_of_lt_of_le (lt_of_lt_of_le hεm (min_le_left _ _)) (Finset.inf'_le _ (Finset.mem_univ ρ))
  have hεl' : ε < εl := lt_of_lt_of_le hεm (min_le_right _ _)
  set U := ((200 * (r : ℝ)) ^ (r ^ 2) * ε ^ (r ^ 2 - 1)) ^ Ψ.card with hU
  have hνB : ν (frBall Ψ G x ε) ≤ ENNReal.ofReal U := by
    rw [hν, Measure.map_apply hπm (hopen ε).measurableSet,
      preimage_frBall E r κ p q Ψ G x σ A e a₀ π hI hP ε, hμ, Measure.pi_pi]
    calc _ ≤ ∏ _ρ : κ, ENNReal.ofReal ((200 * (r : ℝ)) ^ (r ^ 2) * ε ^ (r ^ 2 - 1)) :=
          Finset.prod_le_prod' fun ρ _ => by
            have := hbp ρ ε hε (hεδ ρ)
            rw [hpq ρ] at this
            exact this
      _ = ENNReal.ofReal U := by
          rw [Finset.prod_const, Finset.card_univ, hcard, ← ENNReal.ofReal_pow (by positivity)]
  have hfinB : ν (frBall Ψ G x ε) < ∞ := lt_of_le_of_lt hνB ENNReal.ofReal_lt_top
  haveI : IsLocallyFiniteMeasure ν := ⟨fun g => ⟨(fun h => g⁻¹ * h) ⁻¹' frBall Ψ G x ε,
    (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds (by
      show frBall Ψ G x ε ∈ nhds (g⁻¹ * g)
      rw [inv_mul_cancel]; exact (hopen ε).mem_nhds (h1mem ε hε)),
    by rw [measure_preimage_mul]; exact hfinB⟩⟩
  haveI hH : (riemHaar Ψ G x).IsHaarMeasure :=
    (GlobalTheory.SUVol.DensOne.tangentHaar_riemLie (Ψ := Ψ) (G := G) (hG := hG) (x := x) (hx := hx)).1
  have hc := Measure.isMulLeftInvariant_eq_smul ν (riemHaar Ψ G x)
  set c := ν.haarScalarFactor (riemHaar Ψ G x) with hcdef
  have hL := hbl ε hε hεl'
  have hf : (0 : ℝ) < Ψ.card := by exact_mod_cast hΨ
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  set L := (ε / (2 * ((Ψ.card : ℝ) * (r : ℝ) ^ 2))) ^ (Ψ.card * (r ^ 2 - 1)) / 2 with hLdef
  have hLpos : 0 < L := div_pos (pow_pos (div_pos hε (mul_pos two_pos (mul_pos hf (pow_pos hr' 2)))) _) two_pos
  have hcL : (c : ℝ) * L ≤ U := by
    have h1 : (c : ℝ≥0∞) * ENNReal.ofReal L ≤ ENNReal.ofReal U := by
      calc (c : ℝ≥0∞) * ENNReal.ofReal L ≤ c * riemHaar Ψ G x (frBall Ψ G x ε) := mul_le_mul_of_nonneg_left hL (zero_le)
        _ = ν (frBall Ψ G x ε) := by
          conv_rhs => rw [hc]
          rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
        _ ≤ _ := hνB
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg _)] at h1
    exact (ENNReal.ofReal_le_ofReal_iff (pow_nonneg (mul_nonneg (by positivity) (pow_nonneg hε.le _)) _)).1 h1
  have hUC := constant_bound Ψ.card r ε hΨ hr hε
  have hcC : (c : ℝ) ≤ (1000 * (Ψ.card : ℝ) * (r : ℝ) ^ 3) ^ (Ψ.card * r ^ 2) :=
    le_of_mul_le_mul_right (hcL.trans hUC) hLpos
  rw [← Measure.map_apply hπm hS, ← hν, hc, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  have hcC' : (c : ℝ≥0∞) ≤ ENNReal.ofReal ((1000 * (Ψ.card : ℝ) * (r : ℝ) ^ 3) ^ (Ψ.card * r ^ 2)) := by
    rw [← ENNReal.ofReal_coe_nnreal]; exact ENNReal.ofReal_le_ofReal hcC
  exact mul_le_mul_of_nonneg_right hcC' (zero_le)

end GlobalTheory.CovTop.VolUp.MassUp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VectorBundleLocallyFree
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB

namespace GlobalTheory.VB

theorem exists_open_isVB_free_finite (B : Scheme.{0}) (ι : Type) [Finite ι] (E : ι → B.Modules) (r : ι → ℕ) :
    (∀ a, GlobalTheory.VB.IsVB (E a) (r a)) → ∀ b : B, ∃ U : B.Opens, b ∈ U ∧ ∀ a,
      Nonempty ((Scheme.Modules.pullback U.ι).obj (E a) ≅
        SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin (r a))) := by
  intro hE b
  have := Fintype.ofFinite ι
  choose V e hb he using fun a => hE a b
  refine ⟨Finset.univ.inf V, ?_, fun a => ?_⟩
  · rw [← SetLike.mem_coe, TopologicalSpace.Opens.coe_finset_inf]
    simpa using hb
  · have hle : Finset.univ.inf V ≤ V a := Finset.inf_le (Finset.mem_univ a)
    set U := Finset.univ.inf V
    have hU : U.ι ''ᵁ ⊤ ≤ V a := (U.ι_image_le ⊤).trans hle
    exact ⟨((Scheme.Modules.restrictFunctorIsoPullback U.ι).app (E a)).symm ≪≫
      ((GlobalTheory.VB.isFrame_freeFrame U.toScheme (Fin (r a))).iso
        ((GlobalTheory.VB.isFrame_restrict_iff U.ι _).2 ((he a).res hU))).symm⟩

end GlobalTheory.VB
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VerticalTangentFrameJacobianDetOneStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vertical_tangentFrame_jacobian_det_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J) (L N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W)) (h : IsCell TF Z U e v W k L N) (K : Type) [Field K] [Algebra c.F K] (z : Sp K ⟶ Y₀ TF.X Z) (hz : ⊤ ≤ z ⁻¹ᵁ W) (P₀ P : FrPt Xo c K) (hU : ⊤ ≤ (frX P₀ ≫ TF.Y.j) ⁻¹ᵁ U.1), z ≫ inc₀ TF.X Z = TF.X.ptY P → GlobalTheory.Frames.FrChg (fun σ => (N σ).map (ev z W hz)) 1 P₀ P → IsBaseFrame TF U e v P₀ hU → ∀ (w : VIx Dw → FrPt Xo c (DualNumber K)) (zw : VIx Dw → (Sp (DualNumber K) ⟶ Y₀ TF.X Z)) (hzw : ∀ b, ⊤ ≤ zw b ⁻¹ᵁ W), (∀ b, IsVert P (Pi.single b.toF (1 : K)) (w b)) → (∀ b, zw b ≫ inc₀ TF.X Z = TF.X.ptY (w b)) → (Matrix.of fun a b : VIx Dw => (ev (zw b) W (hzw b) (cellCoord N a)).snd).det = 1 ∧ ∀ b r, (ev (zw b) W (hzw b) (((toBase TF Z).appLE U.1 W h.2.1).hom r)).snd = 0 := by
  first | exact @GlobalTheory.LogPole.vert_jac_det_one | exact GlobalTheory.LogPole.vert_jac_det_one | (intros; apply GlobalTheory.LogPole.vert_jac_det_one <;> assumption)
end

