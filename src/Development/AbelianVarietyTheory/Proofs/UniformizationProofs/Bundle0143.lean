import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0056
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditionalStatement
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.FiniteDimensionalBase
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsFgForallOverLbIso
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0048
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0126
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsNsmulAndNeg
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0134
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0053
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0124
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InvariantFunctionsDescend
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CorrOfGenericOfIsSeparated
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationAdjointEndomorphismsCommute
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformizationEndomorphismCalculus
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RosatiAdjointAbelianPartAndClassifyingMapLinear
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0028
import Development.AbelianVarietyTheory.BlockTheory.UniformisationCharts.ConstantUnitPairing
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0021
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0004

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHoldStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.all_uniformization_laws_hold : LL := by
  first | exact @GlobalTheory.firstFiveLaws | exact GlobalTheory.firstFiveLaws | (intros; apply GlobalTheory.firstFiveLaws <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ArcClauseClosed
section
namespace GlobalTheory

theorem arcClause_closed : ReciprocityTheory.ChartRestriction.G.Geo.Tor.ToroidalArchimedeanCondition :=
  GlobalTheory.T.holomorphic_degenerationArc_of_uniformisation GlobalTheory.T.abelianScheme_laws_unconditional.1 GlobalTheory.T.abelianScheme_laws_unconditional.2 GlobalTheory.T.thetaUniformisation_complexAbelianVariety

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CmPointClosed
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PureType
open scoped CategoryTheory.Obj

namespace GlobalTheory

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj in
private theorem weil_pairing_properties : _root_.ReciprocityTheory.ChartRestriction.G.Out.WeilSt :=
  (_root_.GlobalTheory.AbLaw.FromCube.all_of_cubeGen
    (fun S P M a ↦ _root_.GlobalTheory.AbLaw.CubeAssembly.cube_gen S P M a)).2.2.2.2.1

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj in

theorem _root_.GlobalTheory.cmPoint_closed : _root_.GlobalTheory.CMPoint :=
  _root_.GlobalTheory.cmPoint _root_.GlobalTheory.thetaUnifAV_all weil_pairing_properties

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCmEllipticCurveWithPeriod
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane

namespace GlobalTheory

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj UpperHalfPlane in

theorem _root_.GlobalTheory.cmCurve_closed : _root_.GlobalTheory.CMCurve :=
  _root_.GlobalTheory.cmCurve_of_uniformisation _root_.GlobalTheory.thetaUnifAV_all
    _root_.GlobalTheory.polBaseChange_holds _root_.GlobalTheory.homExtension_semiAbelian_dvr_unconditional

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsRingActionDegenerationLinearUniformisation
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section

namespace GlobalTheory.RingActData

variable {R : Type} [CommRing R] [IsDomain R]

theorem corr_of_val_field (F : Type) [Field F] [Algebra (FractionRing R) F] {X : Scheme.{0}} {L : LB X} (hL : L.IsLB)
    {K K' : Type} [Fintype K] [Fintype K'] {φ : K → ((TK R).left ⟶ X)} {ε : K → ℤ} {φ' : K' → ((TK R).left ⟶ X)}
    {ε' : K' → ℤ} {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε')}
    (h : ∀ (y : (TF (R := R) F).left) J, Good L y J →
      val t (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) y J = val t' (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) y J) :
    LB.Gen.Corr L φ ε φ' ε' t t' := by
  have hf : Flat (jFK (R := R) F) := Flat.SpecMap_iff.2 (by
    show (algebraMap (FractionRing R) F).Flat
    exact RingHom.flat_algebraMap_iff.2 inferInstance)
  have hs : Surjective (jFK (R := R) F) := ⟨fun x => ⟨(⊥ : PrimeSpectrum F),
    Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) _ _⟩⟩
  have he : Epi (jFK (R := R) F) := Flat.epi_of_flat_of_surjective _
  refine GlobalTheory.corr_of_corr_pullGen L φ ε φ' ε' t t' (jFK (R := R) F) (fun U => GlobalTheory.FunDescent.app_injective _ U)
    (fun a b e => (cancel_epi _).1 e) (corr_of_val hL fun y J hJ => ?_)
  exact (val_pull hJ _ _ _).trans ((h y J hJ).trans (val_pull hJ _ _ _).symm)

theorem prod_O (D : DegPre R) {T : Over (Spec (CommRingCat.of R))} (b : T ⟶ D.P.A) (χ : D.X) {U : Type} [CommGroup U]
    (h : (T.left ⟶ D.P.A.left) → U) :
    ∏ i, h (D.Oφ b χ i) ^ Oε i =
      h (cP D _ χ * b).left * (h (cP D _ χ).left)⁻¹ * (h b.left)⁻¹ * h (1 : T ⟶ D.P.A).left := by
  rw [Fin.prod_univ_four, mul_comm (cP D _ χ) b]
  show h (b * cP D _ χ).left ^ (1 : ℤ) * h (cP D _ χ).left ^ (-1 : ℤ) * h b.left ^ (-1 : ℤ) *
    h (1 : T ⟶ D.P.A).left ^ (1 : ℤ) = _
  simp only [zpow_neg, zpow_one]

theorem prod_Oinv (D : DegPre R) {T : Over (Spec (CommRingCat.of R))} (b : T ⟶ D.P.A) (χ : D.X) {U : Type} [CommGroup U]
    (h : (T.left ⟶ D.P.A.left) → U) :
    ∏ i, h (D.Oφ b χ i) ^ Oinvε i =
      (h (cP D _ χ * b).left)⁻¹ * h (cP D _ χ).left * h b.left * (h (1 : T ⟶ D.P.A).left)⁻¹ := by
  rw [Fin.prod_univ_four, mul_comm (cP D _ χ) b]
  show h (b * cP D _ χ).left ^ (-1 : ℤ) * h (cP D _ χ).left ^ (1 : ℤ) * h b.left ^ (1 : ℤ) *
    h (1 : T ⟶ D.P.A).left ^ (-1 : ℤ) = _
  simp only [zpow_neg, zpow_one]

theorem val_eq_rosati (hG : GlobalFnsSt) (D : DegPre R) (f g : D.P.A ⟶ D.P.A) [IsMonHom f] [IsMonHom g]
    (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A f g) rosatiε)) (hu : u.IsGen)
    (u₀ : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (zero2 D.P.A)) (LB.oneGen D.P.L))
    (χ χ' : D.X) (hc : D.c χ' = D.c χ ≫ f)
    (v : LB.Gen (LB.LinComb D.P.L (Sum.elim (D.Oφ (𝟙 _) χ') (D.Oφ g χ)) (Sum.elim Oε Oinvε))) (hv : Normd v)
    {T : Over (Spec (CommRingCat.of R))} (x : T ⟶ D.P.A) (z : T.left) (J) (hJ : Good D.P.L z J) :
    val v x.left z J = val₂ u z J (cP D T χ) x := by
  have cf : ∀ T, cP D T χ' = cP D T χ ≫ f := fun T => by rw [cP, hc, ← Category.assoc]; rfl
  have vp : ∀ {T : Over (Spec (CommRingCat.of R))} (x : T ⟶ D.P.A) (z : T.left) (J), Good D.P.L z J →
      val (LB.pullGen D.P.L _ _ u (lift (cP D _ χ) (𝟙 D.P.A)).left) x.left z J = val₂ u z J (cP D T χ) x :=
    fun x z J hJ => by
      rw [val_pull hJ, ← Over.comp_left, comp_lift, comp_cP, Category.comp_id]; rfl
  refine Eq.trans (gen_unique' D.P.isLB (fun U _ h => ?_) D.P.A.hom (eSec D.P.A) (Over.w η[D.P.A]) (hG _ _ D.P.isAb).2
    hv.1 (pullGen_isGen _ _ _ _ hu _) (fun y I hI => ?_) _ x.left z J hJ) (vp x z J hJ)
  · refine (prod_ros f g (cP D _ χ) (𝟙 D.P.A) h).trans (Eq.trans ?_
      (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ (prod_O D (𝟙 _) χ' h) (prod_Oinv D g χ h)).symm)
    rw [cf, Category.id_comp]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · have a₁ := val_corr hI hv.2 (𝟙 _)
    rw [val_pull hI, Category.id_comp, val_one] at a₁
    have C : IsCub (cubV D.cub (T := 𝟙_ _) y I) := isCub_cubV D.cub hI
    have e := (ros_add D.cub hG D.P.isAb _ _ u hu u₀ (T := 𝟙_ _) hI 1 1 (cP D _ χ)).2
    rw [_root_.mul_one, MonObj.one_comp, C.face₃, C.face₃, _root_.mul_one, _root_.one_mul] at e
    have e₁ : (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A) = η[D.P.A] := by simp [Hom.one_def]
    have e₂ := mul_eq_left.1 e.symm
    rw [e₁] at e₂
    exact a₁.trans (e₂.symm.trans (vp η[D.P.A] y I hI).symm)

variable {I : Ideal R} {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

theorem tauBal_of_act (hG : GlobalFnsSt) {U : UnifPre I D A G} (E E' : EndU U) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (hc : ∀ χ, D.toPre.c (E.h χ) = D.toPre.c χ ≫ E'.aB)
    (hex : ∀ g : GtPtF D.toPre F, ∃ g', E.Act g g')
    (hb : ∀ y (g g' : GtPtF D.toPre F), GtPtF.IsIota y g → E.Act g g' → GtPtF.IsIota (E'.h y) g') :
    D.toPre.TauBal E'.aB E.aB E.h E'.h := by
  intro u hu u₀ χ y
  have := E.homB
  have := E'.homB
  refine corr_of_val_field F D.toPre.P.isLB fun z J hJ => ?_
  obtain ⟨g, hg⟩ := GlobalTheory.TorusExt.exists_iota (F := F) D.tau_bimult y
  obtain ⟨g', hg'⟩ := hex g
  obtain ⟨ιb, ιv⟩ := (isIota_iff _ _).1 hg
  obtain ⟨-, ιv'⟩ := (isIota_iff _ _).1 (hb y g g' hg hg')
  have e := hg'.2 χ z J hJ
  rw [ιv' χ z J hJ, ιv _ z J hJ, val_eq_rosati hG D.toPre E'.aB E.aB u hu u₀ χ _ (hc χ) (E.u χ) (E.u_norm χ) g.b z J hJ,
    ιb] at e
  let κ : TF (R := R) F ⟶ TK R := Over.homMk (𝟙 _ ≫ jFK (R := R) F) (by
    rw [Category.id_comp]; rfl)
  have e' : val (LB.pullGen D.toPre.P.L _ _ u (D.toPre.pt2 χ y)) κ.left z J =
      val₂ u z J (cP D.toPre _ χ) (cP D.toPre _ y) := by
    rw [val_pull hJ, val₂, ← comp_cP D.toPre κ, ← comp_cP D.toPre κ y, ← comp_lift]; rfl
  refine (val_mul hJ _ _ _).trans ?_
  exact (congrArg₂ (· * ·) (tau_symm (𝟙 (TF (R := R) F)) hJ _ _) e').trans
    (e.symm.trans (tau_symm (𝟙 (TF (R := R) F)) hJ _ _))

theorem exists_oAct : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => ∀ (O : Type) [CommRing O] [StarRing O] (ιA : A.OAct O) (ιG : RingAct G O), (∀ a, (Over.pullback (jK R)).map (ιG.act a) ≫ U.gen.hom = U.gen.hom ≫ ιA.act a) → (∀ a, LBIso (cubeLB G ![fst G G ≫ ιG.act a, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ ιG.act (star a)] U.LG.L)) → ∃ (_ : Module O D.toPre.X) (ιD : D.toPre.OAct O), U.toUnifPre.OLinear O ιD ιA ιG := by
  intro hL h₁ h₂ h₃ h₄ R _ _ _ I hI D A G _ _ hS U O _ _ ιA ιG hext hros
  choose E EG EA using fun a => GlobalTheory.T.exists_endomorphism_action_uniformization_data hL R I hI D A G hS U (ιG.act a) (ιA.act a) (ιG.hom a) (ιA.hom a) (hext a)
  have hcalc := GlobalTheory.T.uniformizationEndomorphism_calculus hL R I hI D A G hS U (AlgebraicClosure (FractionRing R))
  have hadj : ∀ a, LBIso (cubeLB G ![fst G G ≫ (E a).aG, snd G G] U.LG.L)
      (cubeLB G ![fst G G, snd G G ≫ (E (star a)).aG] U.LG.L) := fun a => by
    rw [EG, EG]; exact hros a
  have ros := fun a => GlobalTheory.T.rosatiAdjoint_abelianPart_and_classifying_map_linear hL R I hI D A G hS U _ _ (hadj a)
  have bal := fun a => (GlobalTheory.T.uniformisation_adjoint_endomorphisms_commute hL h₁ h₂ h₃ h₄ R I hI D A G hS U (AlgebraicClosure (FractionRing R)) _ _ (hadj a)).1
  obtain ⟨E₁, g₁, -, b₁, x₁, -⟩ := (GlobalTheory.IntEnd.exists_nsmul_and_neg hL R I hI D A G hS U).1 1
  have one := (hcalc (E 1) E₁ E₁).2.2.2.1 (by rw [EG, ιG.map_one, g₁, pow_one])
  have add := fun a b => (hcalc (E a) (E b) (E (a + b))).2.2.2.2.1 (by rw [EG, EG, EG, ιG.map_add]; rfl)
  have mul := fun a b => (hcalc (E b) (E a) (E (a * b))).2.2.2.2.2 (by rw [EG, EG, EG, ιG.map_mul])
  let M : Module O D.toPre.X :=
    { smul := fun a y => (E (star a)).h y
      one_smul := fun y => by
        show (E (star 1)).h y = y
        rw [star_one, one.2.1, x₁, one_nsmul]
      mul_smul := fun a b y => by
        show (E (star (a * b))).h y = (E (star a)).h ((E (star b)).h y)
        rw [star_mul, (mul _ _).2.1]; rfl
      smul_zero := fun a => map_zero (E (star a)).h
      smul_add := fun a => map_add (E (star a)).h
      add_smul := fun a b y => by
        show (E (star (a + b))).h y = (E (star a)).h y + (E (star b)).h y
        rw [star_add, (add _ _).2.1]; rfl
      zero_smul := fun y => by
        show (E (star 0)).h y = 0
        have := DFunLike.congr_fun (add 0 0).2.1 y
        rw [add_zero, AddMonoidHom.add_apply] at this
        rw [star_zero]
        exact left_eq_add.1 this }
  have sm : ∀ a, (fun y : D.toPre.X => star a • y) = (E a).h := fun a => funext fun y => by
    show (E (star (star a))).h y = _
    rw [star_star]
  refine ⟨M,
    { onB :=
        { act := fun a => (E a).aB
          hom := fun a => (E a).homB
          map_one := by rw [one.1, b₁, pow_one]
          map_mul := fun a b => (mul a b).1
          map_add := fun a b => (add a b).1
          rosati := fun a => (ros a).2.1 }
      c_lin := fun a y => (ros a).2.2.2 y
      tau_bal := fun a => ?_ }, hext, fun e a => ?_, fun e a => ?_⟩
  · have hb := bal (star a)
    rw [star_star] at hb
    rw [sm]
    exact tauBal_of_act hL.1.globalFns (E (star a)) (E a) _ (ros a).2.2.2
      (fun g => ((hcalc (E (star a)) E₁ E₁).1 g).exists) hb
  · rw [← EG]; exact (E a).q_lin e
  · rw [← EG, sm]; exact (E a).i_lin e

end GlobalTheory.RingActData
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FunctorialOfUnif
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.UT

set_option maxHeartbeats 1000000 in

theorem functorial_of_unif :
    AllU fun {_} _ _ {_} {_} {_} {_} _ _ U => Cl.Functorial U := by
  have hL := GlobalTheory.firstFiveLaws
  obtain ⟨-, h1, h2, h3, h4⟩ := GlobalTheory.twistBaseChange_and_valuation_statements
  have hex := @GlobalTheory.EndData.exists_endU hL
  have hros := @GlobalTheory.UT.rosatiAdj_and_c_linear_of_endU hL
  have hcalc := @GlobalTheory.EndCalc.end_calculus hL
  have hbal := @GlobalTheory.Balanced.main hL h1 h2 h3 h4
  intro R _ _ _ I hB D A G _ _ hG U
  refine ⟨hex R I hB D A G hG U, fun E E' hE => ⟨hros R I hB D A G hG U E E' hE, fun F _ _ _ => ?_⟩⟩
  exact ⟨(hcalc R I hB D A G hG U F E E E).1, hbal R I hB D A G hG U F E E' hE⟩

end GlobalTheory.UT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GaloisHolds
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.UT.Cl

theorem galois_holds : AllU fun {_} _ _ {_} {_} {_} {_} _ _ U => Cl.Galois U := by
  intro R _ _ _ I hI D A G _ _ hG U F _ _ _ F' _ _ _ σ k hk p
  refine ⟨qkExtExists R D.toPre F F' σ.toRingHom σ.commutes k p, fun x => ?_, fun p' x x' hp hx =>
    TorsionExt.qkToAkU_iff_of_qkExt firstFiveLaws R I hI D A G hG U F F' σ k hk p p' x x' hp hx⟩
  letI : Algebra F F' := σ.toRingHom.toAlgebra
  haveI : IsScalarTower (FractionRing R) F F' := IsScalarTower.of_algebraMap_eq fun c => (σ.commutes c).symm
  exact ⟨TorsionExt.fieldMap F F' ≫ x, rfl⟩

end GlobalTheory.UT.Cl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LinearUniformisationTorsionMapIsLinear
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
namespace GlobalTheory.UT.OLinTors

theorem main : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (ιD : D.toPre.OAct O) (ιA : A.OAct O) (ιG : RingAct G O), U.toUnifPre.OLinear O ιD ιA ιG → (∀ a, LBIso (cubeLB G ![fst G G ≫ ιG.act a, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ ιG.act (star a)] U.LG.L)) → ∀ (k : ℕ), 1 ≤ k → ∀ f, Tors U.toUnifPre F k f → ∀ a p p', QkAct ιD a p p' → f p' = f p ≫ ιA.act a := by
  intro hL h₁ h₂ h₃ h₄ R _ _ _ I hI D A G _ _ hG U F _ _ _ O _ _ _ ιD ιA ιG hlin hcube k hk f hf a p p' hp
  obtain ⟨E, eG, eA, -, -, eact⟩ := GlobalTheory.UT.OLinEnd.main hL R I hI D A G hG U O ιD ιA ιG hlin a
  obtain ⟨E', eG', -, -, eh', -⟩ := GlobalTheory.UT.OLinEnd.main hL R I hI D A G hG U O ιD ιA ιG hlin (star a)
  obtain ⟨q, hy, hg, hq⟩ := hp
  have hb := (GlobalTheory.T.uniformisation_adjoint_endomorphisms_commute hL h₁ h₂ h₃ h₄ R I hI D A G hG U F E E' (by rw [eG, eG']; exact hcube a)).2 k hk p q (f p)
    (by rw [eh', star_star]; exact hy) ((eact F _ _).2 hg) ((hf.1 p _).2 rfl)
  have e := (hf.1 q _).1 hb
  rw [eA] at e
  rw [e]
  first | exact (hf.2.2.1 _ _).2 hq | exact ((hf.2.2.1 _ _).2 hq).symm
end GlobalTheory.UT.OLinTors
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SecondIffFirstAndRest
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section

namespace GlobalTheory.PairingCompare

open GlobalTheory.IndefiniteRowSideFullHecke.ConstantUnitPairing GlobalTheory.TorsionExt GlobalTheory.FieldBaseChange

def First : Prop :=
  LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (k : ℕ), 1 ≤ k → ∀ (p p' : QkPt D.toPre F k) x x', QkToAkU U.toUnifPre F k p x → QkToAkU U.toUnifPre F k p' x' → ∀ ζ : Fˣ, WeilQkIs D.toPre F k p p' ζ ↔ WeilIs A.A A.L k x x' (unitOn ζ)

section Clause

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  [IsCommMonObj G]

def ClauseFirst (U : Unif I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] : Prop :=
  ∀ (k : ℕ), 1 ≤ k → ∀ (p p' : QkPt D.toPre F k) x x', QkToAkU U.toUnifPre F k p x →
    QkToAkU U.toUnifPre F k p' x' → ∀ ζ : Fˣ, WeilQkIs D.toPre F k p p' ζ ↔ WeilIs A.A A.L k x x' (unitOn ζ)

def ClauseSecond (U : Unif I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] : Prop :=
  ∀ (k : ℕ), 1 ≤ k → ∀ (p p' : QkPt D.toPre F k) (x x' : TFK (R := R) F ⟶ A.A),
    QkToAkU U.toUnifPre F k p x → QkToAkU U.toUnifPre F k p' x' →
    ∀ ζ : Fˣ, WeilQkIs D.toPre F k p p' (ζ : F) ↔ WeilIs A.A A.L (k : ℤ) x x' (constUnit R F ζ)

theorem weilQkIs_iff_operators (hG : GlobalFnsSt) {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ}
    {p p' : QkPt D.toPre F k} {w : Frm D.toPre F k p.g.b} {w' : Frm D.toPre F k p'.g.b}
    (hw : w.IsGen) (hw' : w'.IsGen) {Φ Φ' : Fam D.toPre F k →ₗ[F] Fam D.toPre F k}
    (hΦ : ∀ s t, PhiRel D.toPre F k p w s t ↔ t = Φ s) (hΦ' : ∀ s t, PhiRel D.toPre F k p' w' s t ↔ t = Φ' s)
    (ζ : F) : WeilQkIs D.toPre F k p p' ζ ↔ ∀ s, Φ (Φ' s) = ζ • Φ' (Φ s) := by
  have r : ∀ s, PhiRel D.toPre F k p w s (Φ s) := fun s => (hΦ _ _).2 rfl
  have r' : ∀ s, PhiRel D.toPre F k p' w' s (Φ' s) := fun s => (hΦ' _ _).2 rfl
  constructor
  · intro h s
    exact (isSmul_iff _ _ _).1 (h w w' hw hw' s _ _ _ _ (r' s) (r _) (r s) (r' _))
  · intro H v v' hv hv' s s₁ s₂ s₃ s₄ h₁ h₂ h₃ h₄
    obtain ⟨c, -, hc⟩ := TorsionImage.exists_smul_of_phiVal p w v hw hv
    obtain ⟨c', -, hc'⟩ := TorsionImage.exists_smul_of_phiVal p' w' v' hw' hv'
    have q : ∀ s t, PhiRel D.toPre F k p v s t → t = c • Φ s := fun s t h =>
      hc s _ t ((phiRel_iff hG p w hw _ _).1 (r s)) ((phiRel_iff hG p v hv _ _).1 h)
    have q' : ∀ s t, PhiRel D.toPre F k p' v' s t → t = c' • Φ' s := fun s t h =>
      hc' s _ t ((phiRel_iff hG p' w' hw' _ _).1 (r' s)) ((phiRel_iff hG p' v' hv' _ _).1 h)
    rw [isSmul_iff, q _ _ h₂, q' _ _ h₁, q' _ _ h₄, q _ _ h₃, map_smul, map_smul, H s,
      smul_comm c' ζ, smul_comm c ζ, smul_comm c c']

theorem injective_of_isExtension {K F V W : Type} [Field K] [Field F] [Algebra K F] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module F W] {a : V →ₛₗ[algebraMap K F] W} (h : IsExtension a) : Function.Injective a := by
  obtain ⟨ℓ, hℓ⟩ := (Algebra.linearMap K F).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 (algebraMap K F).injective)
  have h1 : ℓ 1 = 1 := by simpa using LinearMap.congr_fun hℓ 1
  obtain ⟨Λ, hΛ⟩ := h.coord ℓ
  have h2 : ∀ v, Λ (a v) = v := fun v => by
    have := hΛ 1 v
    rwa [one_smul, h1, one_smul] at this
  exact Function.LeftInverse.injective h2

variable {E F : Type} [Field F] [Algebra (FractionRing R) F] [Field E] [Algebra (FractionRing R) E] [Algebra E F]
  [IsScalarTower (FractionRing R) E F]

theorem weilQkIs_iff_of_algebra (hG : GlobalFnsSt) {k : ℕ} (hk : 1 ≤ k) {p p' : QkPt D.toPre E k}
    {q q' : QkPt D.toPre F k} (h : QkExt (algebraMap E F) p q) (h' : QkExt (algebraMap E F) p' q') (ζ : E) :
    WeilQkIs D.toPre E k p p' ζ ↔ WeilQkIs D.toPre F k q q' (algebraMap E F ζ) := by
  obtain ⟨w, hw⟩ : ∃ w : Frm D.toPre E k p.g.b, w.IsGen := exists_gen_of_local D.toPre.P.L D.toPre.P.isLB _ _
  obtain ⟨w', hw'⟩ : ∃ w : Frm D.toPre E k p'.g.b, w.IsGen := exists_gen_of_local D.toPre.P.L D.toPre.P.isLB _ _
  obtain ⟨v, hv, hwv⟩ := exists_phiVal_pull hG h hw
  obtain ⟨v', hv', hwv'⟩ := exists_phiVal_pull hG h' hw'
  obtain ⟨Φ, hΦ⟩ := phiFun_of_globalFns hG R I D E k hk p w hw
  obtain ⟨Φ', hΦ'⟩ := phiFun_of_globalFns hG R I D E k hk p' w' hw'
  obtain ⟨Ψ, hΨ⟩ := phiFun_of_globalFns hG R I D F k hk q v hv
  obtain ⟨Ψ', hΨ'⟩ := phiFun_of_globalFns hG R I D F k hk q' v' hv'
  have c : ∀ s, Ψ (famPull D.toPre E F hG k s) = famPull D.toPre E F hG k (Φ s) := fun s =>
    phi_unique q v ((phiRel_iff hG q v hv _ _).1 ((hΨ _ _).2 rfl))
      (hwv _ _ ((phiRel_iff hG p w hw s _).1 ((hΦ s _).2 rfl)))
  have c' : ∀ s, Ψ' (famPull D.toPre E F hG k s) = famPull D.toPre E F hG k (Φ' s) := fun s =>
    phi_unique q' v' ((phiRel_iff hG q' v' hv' _ _).1 ((hΨ' _ _).2 rfl))
      (hwv' _ _ ((phiRel_iff hG p' w' hw' s _).1 ((hΦ' s _).2 rfl)))
  have hx := isExtension_famPull D.toPre E F hG hk
  rw [weilQkIs_iff_operators hG hw hw' hΦ hΦ', weilQkIs_iff_operators hG hv hv' hΨ hΨ']
  constructor
  · intro H s
    have e : Ψ ∘ₗ Ψ' = algebraMap E F ζ • (Ψ' ∘ₗ Ψ) := LinearMap.ext_on hx.span (by
      rintro _ ⟨t, rfl⟩
      rw [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.comp_apply, c', c, c, c', H, map_smulₛₗ])
    exact LinearMap.congr_fun e s
  · intro H s
    refine injective_of_isExtension hx ?_
    rw [map_smulₛₗ, ← c, ← c', ← c', ← c, H]

end Clause

def SecondOn (P : ∀ (R : Type) [CommRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G], Prop) : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I →
    ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R))))
      (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], P R G → ∀ (U : Unif I D A G)
      (F : Type) [Field F] [Algebra (FractionRing R) F], ClauseSecond U F

end GlobalTheory.PairingCompare
end
end

