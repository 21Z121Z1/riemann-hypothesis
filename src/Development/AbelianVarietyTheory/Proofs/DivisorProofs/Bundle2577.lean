import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2548
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomLiftsSqZeroClassifiedByDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2480
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2369
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2413
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2452
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2511
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenseSectionsOfAlgebraicAffineNbhd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2462
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import Development.AutomorphicArithmetic.CMTraceForms.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2410
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2463
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivativeCechCocycleInvariantVectorFieldIsCobou
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualMapCompDualMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2505
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZbLeftWhiskerRight
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0078
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0393
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationRescaleTauBimultExists
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.RescaleBimult

variable {R : Type} [CommRing R] [IsDomain R]

theorem pt_add (D : DegPre R) (a b : D.X) :
    toUnit (TK R) ≫ D.c (a + b) = (toUnit (TK R) ≫ D.c a) * (toUnit (TK R) ≫ D.c b) := by
  rw [D.c_add]; exact MonObj.comp_mul _ _ _

theorem gm_unitOn_inj {u v : (FractionRing R)ˣ} (z : (TK R).left)
    (h : gm (𝟙 (TK R).left) z ⊤ (unitOn u) = gm (𝟙 (TK R).left) z ⊤ (unitOn v)) : u = v := by
  have hs : Subsingleton (TK R).left := (inferInstance : Subsingleton (PrimeSpectrum (FractionRing R)))
  have e : unitOn u = unitOn v := unit_ext fun x _ => by rw [Subsingleton.elim x z]; exact h
  exact Units.map_injective (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv).1 e

theorem val_tau (D : DegPre R) (a b : D.X) {z : (TK R).left} {J} (hJ : Good D.P.L z J) :
    val (D.tau a b) (𝟙 _) z J = val (D.psi (a + b)) (𝟙 _) z J * (val (D.psi a) (𝟙 _) z J)⁻¹ *
      (val (D.psi b) (𝟙 _) z J)⁻¹ * (val D.rigK (𝟙 _) z J)⁻¹ :=
  (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))

theorem val_cub3 (D : DegPre R) (a a' b : D.X) {z : (TK R).left} {J} (hJ : Good D.P.L z J) :
    val (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 a a' b)) (𝟙 _) z J =
      cubV D.cub z J (toUnit (TK R) ≫ D.c a) (toUnit (TK R) ≫ D.c a') (toUnit (TK R) ≫ D.c b) := by
  refine (val_cub D.cub (𝟙 (TK R)) hJ _ _ _).trans ?_
  rw [Category.id_comp, Category.id_comp, Category.id_comp]

theorem exists_defect (D : DegPre R) (a a' b : D.X) : ∃ k : (FractionRing R)ˣ, ∀ (z : (TK R).left) J, Good D.P.L z J →
    val (D.psi (a + a' + b)) (𝟙 _) z J * val (D.psi a) (𝟙 _) z J * val (D.psi a') (𝟙 _) z J * val (D.psi b) (𝟙 _) z J *
      val D.rigK (𝟙 _) z J *
      cubV D.cub z J (toUnit (TK R) ≫ D.c a) (toUnit (TK R) ≫ D.c a') (toUnit (TK R) ≫ D.c b) =
      gm (𝟙 (TK R).left) z ⊤ (unitOn k) *
        (val (D.psi (a + a')) (𝟙 _) z J * val (D.psi (a + b)) (𝟙 _) z J * val (D.psi (a' + b)) (𝟙 _) z J) := by
  let t := LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _
    (LB.mulGen D.P.L _ _ _ _ (D.psi (a + a' + b)) (D.psi a)) (D.psi a')) (D.psi b)) D.rigK)
    (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 a a' b))
  have ht : t.IsGen := DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (D.psi_gen _) (D.psi_gen _)) (D.psi_gen _))
    (D.psi_gen _)) (DVR.pullGen_isGen _ _ _ _ D.rig_gen _)) (DVR.pullGen_isGen _ _ _ _ D.cub.isGen _)
  let t' := LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (D.psi (a + a')) (D.psi (a + b))) (D.psi (a' + b))
  have ht' : t'.IsGen := DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (D.psi_gen _) (D.psi_gen _))
    (D.psi_gen _)
  obtain ⟨c, hc, H⟩ := DVR.TWM.exists_ratio (F := FractionRing R) D.P.isLB t ht t' ht' (fun U _ h => by
    refine ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) rfl
      (prod_cub (toUnit (TK R) ≫ D.c a) (toUnit (TK R) ≫ D.c a') (toUnit (TK R) ≫ D.c b) h))).trans ?_
    rw [← pt_add, ← pt_add, ← pt_add, ← pt_add]
    simp only [Fintype.prod_sum_type, Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr, zpow_neg, zpow_one]
    have e : (toUnit (TK R)).left ≫ eSec D.P.A = (1 : TK R ⟶ D.P.A).left := rfl
    erw [e]
    simp only [ptK]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel)
  refine ⟨Units.mk0 c hc, fun z J hJ => ?_⟩
  have e := H _ (𝟙 _) z J hJ
  have e₁ : val t (𝟙 _) z J = val (D.psi (a + a' + b)) (𝟙 _) z J * val (D.psi a) (𝟙 _) z J *
      val (D.psi a') (𝟙 _) z J * val (D.psi b) (𝟙 _) z J * val D.rigK (𝟙 _) z J *
      cubV D.cub z J (toUnit (TK R) ≫ D.c a) (toUnit (TK R) ≫ D.c a') (toUnit (TK R) ≫ D.c b) :=
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
      (val_mul hJ _ _ _) rfl)) rfl)) rfl)) (val_cub3 D a a' b hJ))
  have e₂ : val t' (𝟙 _) z J = val (D.psi (a + a')) (𝟙 _) z J * val (D.psi (a + b)) (𝟙 _) z J *
      val (D.psi (a' + b)) (𝟙 _) z J :=
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_mul hJ _ _ _) rfl)
  rw [← e₁, ← e₂]
  refine Units.ext (e.trans ?_)
  rw [Units.val_mul, ← gs_unit _ z ⊤ trivial]
  rfl

theorem exists_rescale_tauBimult : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R),
    ∃ g : D.X → (FractionRing R)ˣ, (GlobalTheory.PolDeg.rescale D g).TauBimult := by
  intro R _ _ D
  choose F hF using exists_defect D
  let z₀ : (TK R).left := (⊥ : PrimeSpectrum (FractionRing R))
  obtain ⟨J₀, hJ₀⟩ := GlobalTheory.UU.exists_good_pt D.P.isLB z₀
  have C := isCub_cubV D.cub hJ₀
  have um : ∀ u v : (FractionRing R)ˣ, unitOn (u * v) = unitOn u * unitOn v :=
    fun u v => map_mul _ _ _
  have ui : ∀ u : (FractionRing R)ˣ, unitOn u⁻¹ = (unitOn u)⁻¹ := fun u => map_inv _ _
  have E := fun {z : (TK R).left} {p q : ((TK R).left.presheaf.stalk z)ˣ} (e : p = q) => congrArg Additive.ofMul e
  obtain ⟨g, hg⟩ := GlobalTheory.symm_cubical_cocycle_isThirdDifference D.X (FractionRing R)ˣ F
    (fun a b c => gm_unitOn_inj z₀ (by
      have h₁ := E (hF a b c z₀ J₀ hJ₀)
      have h₂ := E (hF b a c z₀ J₀ hJ₀)
      rw [add_comm b a, C.s01] at h₂
      apply Additive.ofMul.injective
      simp only [ofMul_mul] at h₁ h₂
      linear_combination (norm := abel) h₂ - h₁))
    (fun a b c => gm_unitOn_inj z₀ (by
      have h₁ := E (hF a b c z₀ J₀ hJ₀)
      have h₂ := E (hF a c b z₀ J₀ hJ₀)
      rw [add_comm c b, add_right_comm a c b, C.s12] at h₂
      apply Additive.ofMul.injective
      simp only [ofMul_mul] at h₁ h₂
      linear_combination (norm := abel) h₂ - h₁))
    (fun x x' x'' y => gm_unitOn_inj z₀ (by
      have h₁ := E (hF (x + x') x'' y z₀ J₀ hJ₀)
      have h₂ := E (hF x x' y z₀ J₀ hJ₀)
      have h₃ := E (hF x (x' + x'') y z₀ J₀ hJ₀)
      have h₄ := E (hF x' x'' y z₀ J₀ hJ₀)
      have h₅ := E (C.coc (toUnit (TK R) ≫ D.c x) (toUnit (TK R) ≫ D.c x') (toUnit (TK R) ≫ D.c x'')
        (toUnit (TK R) ≫ D.c y))
      rw [← pt_add, ← pt_add] at h₅
      rw [← add_assoc x x' x''] at h₃
      rw [um, um, map_mul, map_mul]
      apply Additive.ofMul.injective
      simp only [ofMul_mul] at h₁ h₂ h₃ h₄ h₅ ⊢
      linear_combination (norm := abel) h₃ + h₄ - h₁ - h₂ + h₅))
  refine ⟨fun x => (g x)⁻¹, fun (a a' b : D.X) => corr_of_val D.P.isLB fun z J hJ => ?_⟩
  have hp : ∀ x : D.X, val ((GlobalTheory.PolDeg.rescale D fun x => (g x)⁻¹).psi x) (𝟙 _) z J =
      (gm (𝟙 (TK R).left) z ⊤ (unitOn (g x)))⁻¹ * val (D.psi x) (𝟙 _) z J := fun x =>
    (GlobalTheory.UU.val_scaleGen _ _ _ hJ).trans (by rw [ui, map_inv]; rfl)
  have ht : ∀ x y : D.X, val ((GlobalTheory.PolDeg.rescale D fun x => (g x)⁻¹).tau x y) (𝟙 _) z J =
      (gm (𝟙 (TK R).left) z ⊤ (unitOn (g (x + y))))⁻¹ * val (D.psi (x + y)) (𝟙 _) z J *
      ((gm (𝟙 (TK R).left) z ⊤ (unitOn (g x)))⁻¹ * val (D.psi x) (𝟙 _) z J)⁻¹ *
      ((gm (𝟙 (TK R).left) z ⊤ (unitOn (g y)))⁻¹ * val (D.psi y) (𝟙 _) z J)⁻¹ *
      (val D.rigK (𝟙 _) z J)⁻¹ := fun x y =>
    (val_tau (GlobalTheory.PolDeg.rescale D fun x => (g x)⁻¹) x y hJ).trans (congrArg₂ (· * ·) (congrArg₂ (· * ·)
      (congrArg₂ (· * ·) (hp (x + y)) (congrArg (·⁻¹) (hp x))) (congrArg (·⁻¹) (hp y))) rfl)
  refine ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (ht (a + a') b) (val_cub3 D a a' b hJ))).trans
    (Eq.trans ?_ ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (ht a b) (ht a' b))).symm)
  have h₁ := E (hF a a' b z J hJ)
  have h₂ := congrArg (fun u => gm (𝟙 (TK R).left) z ⊤ (unitOn u)) (hg a a' b)
  simp only [um, map_mul] at h₂
  have h₃ := E h₂
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv] at h₁ h₃ ⊢
  linear_combination (norm := abel) h₁ + h₃

end GlobalTheory.RescaleBimult
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeTwoObstructionClassNatural
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Obs

theorem extHom_coefHom_restrict {R₀ : Type} [CommRing R₀] (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁]
    {C₂ C' : Type} [Category.{0} C₂] [Category.{0} C'] (F₂ : C₂ ⥤ CommAlgCat.{0} R₀) (G : C' ⥤ C₂) (T : C')
    (y : R₁ ⊗[R₀] F₂.obj ((CoefMap.restrict F₂ G).G.obj T)) :
    extHom R₁ (coefHom (CoefMap.restrict F₂ G) T) y = y := by
  change Algebra.TensorProduct.map (AlgHom.id R₁ R₁) (AlgHom.id R₀ _) y = y
  rw [Algebra.TensorProduct.map_id]; rfl

theorem isOb2_natural : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (C₂ : Type) [Category.{0} C₂] (F₂ : C₂ ⥤ CommAlgCat.{0} R₀) (C' : Type) [Category.{0} C'] (G : C' ⥤ C₂) (n : CoefMap (RingHom.id R₀) F (G ⋙ F₂)) (L : Pre I π F) (L₂ : Pre I π F₂) (w : Glob1 F) (w₂ : Glob1 F₂) (c : GlobalTheory.CatCoh.H2 (ext R₁ F)) (c₂ : GlobalTheory.CatCoh.H2 (ext R₁ F₂)), (∀ T, q1 n T (w.1 _) = w₂.1 (G.obj T)) → L.IsOb2 α w c → L₂.IsOb2 α w₂ c₂ → (extMap R₁ n).pull2 c = (extMap R₁ (CoefMap.restrict F₂ G)).pull2 c₂ := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α C _ F C₂ _ F₂ C' _ G n L L₂ w w₂ c c₂ hw h1 h2
  obtain ⟨θ, σ, z, hθ, hσ, rfl, hz⟩ := h1
  obtain ⟨θ₂, σ₂, z₂, hθ₂, hσ₂, rfl, hz₂⟩ := h2
  have hl0 : ∀ T : C', ∃ l : L.B (n.G.obj T) →ₐ[R] L₂.B (G.obj T),
      ∀ b, L₂.p (G.obj T) (l b) = coefHom n T (L.p _ b) := by
    intro T
    haveI := L.smooth (n.G.obj T)
    exact homLift R R₀ I hI π hπ hk _ _ (L.p _) (L.semi _) (L.surj _) (L.ker _) _ _ (L₂.p (G.obj T))
      (L₂.semi _) (L₂.surj _) (L₂.ker _) (coefHom n T)
  choose l hl using hl0
  have hd : ∀ (T T' : C') (a : T ⟶ T') (b : L.B (n.G.obj T)),
      ((L₂.ρ (G.map a)).comp (l T)) b - ((l T').comp (L.ρ (n.G.map a))) b ∈
        I.map (algebraMap R (L₂.B (G.obj T'))) := by
    intro T T' a b
    refine (L₂.ker _ _).1 ?_
    rw [map_sub, sub_eq_zero]
    simp only [AlgHom.comp_apply]
    rw [L₂.nat, hl, hl, L.nat]
    exact (n.naturality a (L.p _ b)).symm
  choose κ hκ using fun (T T' : C') (a : T ⟶ T') ↦ ((theta_classify R R₀ (L.B (n.G.obj T)) (F.obj (n.G.obj T))
    (L₂.B (G.obj T')) I hI π hπ (L.p _) (L.semi _) (L.surj _) (L.ker _)
    ((L₂.ρ (G.map a)).comp (l T))).1 _ (hd T T' a)).exists
  have key : ∀ (T T' T'' : C') (a : T ⟶ T') (b : T' ⟶ T'') (ω : Ω[F.obj (n.G.obj T)⁄R₀]),
      θ₂ _ _ _ (G.map a) (G.map b) (q1 n T ω) + κ T T'' (a ≫ b) ω =
        L₂.ρ (G.map b) (κ T T' a ω) + κ T' T'' b (p1 F (n.G.map a) ω) +
          l T'' (θ _ _ _ (n.G.map a) (n.G.map b) ω) := by
    intro T T' T'' a b ω
    have e1 := (GlobalTheory.T.isDifferenceDerivationOfLifts_comp R R₀ I hI π hπ hk _ _ (L₂.p (G.obj T)) (L₂.semi _) (L₂.surj _) (L₂.ker _) _ _
      (L.p (n.G.obj T)) (L.semi _) (L.surj _) (L.ker _) (L₂.B (G.obj T'')) (L₂.B (G.obj T'')) _ _ _ (hθ₂ _ _ _ (G.map a) (G.map b))).2
      (l T) (coefHom n T) (hl T)
    have e2 := hκ T T'' (a ≫ b)
    rw [Functor.map_comp, Functor.map_comp] at e2
    have s1 := (isTheta_add R R₀ I hI π hπ hk _ _ (L.p (n.G.obj T)) (L.semi _) (L.surj _) (L.ker _) _ _ _ _ _ _
      e1).2.1 e2
    have f1 := (GlobalTheory.T.isDifferenceDerivationOfLifts_comp R R₀ I hI π hπ hk _ _ (L.p (n.G.obj T)) (L.semi _) (L.surj _) (L.ker _) _ _
      (L.p (n.G.obj T)) (L.semi _) (L.surj _) (L.ker _) (L₂.B (G.obj T')) (L₂.B (G.obj T'')) _ _ _ (hκ T T' a)).1 (L₂.ρ (G.map b))
    have f2 := (GlobalTheory.T.isDifferenceDerivationOfLifts_comp R R₀ I hI π hπ hk _ _ (L.p (n.G.obj T')) (L.semi _) (L.surj _) (L.ker _) _ _
      (L.p (n.G.obj T)) (L.semi _) (L.surj _) (L.ker _) (L₂.B (G.obj T'')) (L₂.B (G.obj T'')) _ _ _ (hκ T' T'' b)).2
      (L.ρ (n.G.map a)) (mp F (n.G.map a)) (L.nat (n.G.map a))
    have f3 := (GlobalTheory.T.isDifferenceDerivationOfLifts_comp R R₀ I hI π hπ hk _ _ (L.p (n.G.obj T)) (L.semi _) (L.surj _) (L.ker _) _ _
      (L.p (n.G.obj T)) (L.semi _) (L.surj _) (L.ker _) (L.B (n.G.obj T'')) (L₂.B (G.obj T'')) _ _ _ (hθ _ _ _ (n.G.map a) (n.G.map b))).1 (l T'')
    have s2 := (isTheta_add R R₀ I hI π hπ hk _ _ (L.p (n.G.obj T)) (L.semi _) (L.surj _) (L.ker _) _ _ _ _ _ _
      ((isTheta_add R R₀ I hI π hπ hk _ _ (L.p (n.G.obj T)) (L.semi _) (L.surj _) (L.ker _) _ _ _ _ _ _
        f1).2.1 f2)).2.1 f3
    have e := congrArg (fun t : Ω[F.obj (n.G.obj T)⁄R₀] →+ L₂.B (G.obj T'') ↦ t ω)
      ((isTheta_add R R₀ I hI π hπ hk _ _ (L.p (n.G.obj T)) (L.semi _) (L.surj _) (L.ker _) _ _ _ (l T'' |>.comp (L.ρ (n.G.map (a ≫ b)))) _ _
        s1).2.2.1 s2)
    exact e
  choose g hgK hg using fun (T T' : C') (a : T ⟶ T') ↦ (sig_basic R R₀ I hI π hπ hk R₁ α _ _
    (L₂.p (G.obj T')) (L₂.semi _) (L₂.surj _) (L₂.ker _) (σ₂ _) (hσ₂ _)).2.2.2 (κ T T' a (w.1 _))
    ((hκ T T' a).mem _)
  have kadd : ∀ {X : C₂} (y y' : R₁ ⊗[R₀] F₂.obj X), α.KerQ y → α.KerQ y' → α.KerQ (y + y') :=
    fun y y' h h' ↦ by unfold Aug.KerQ at *; rw [map_add, h, h', add_zero]
  have kneg : ∀ {X : C₂} (y : R₁ ⊗[R₀] F₂.obj X), α.KerQ y → α.KerQ (-y) :=
    fun y h ↦ by unfold Aug.KerQ at *; rw [map_neg, h, neg_zero]
  have ksub : ∀ {X : C₂} (y y' : R₁ ⊗[R₀] F₂.obj X), α.KerQ y → α.KerQ y' → α.KerQ (y - y') :=
    fun y y' h h' ↦ by rw [sub_eq_add_neg]; exact kadd _ _ h (kneg _ h')
  rw [CoefMap.pullCohomologyTwo_class, CoefMap.pullCohomologyTwo_class, H2.mk_eq_mk]
  refine ⟨fun T T' a ↦ -g T T' a, ?_⟩
  funext T T' T'' a b
  haveI := L₂.smooth (G.obj T'')
  have nb := sig_natural R R₀ I hI π hπ hk R₁ α _ _ (L₂.p (G.obj T')) (L₂.semi _) (L₂.surj _) (L₂.ker _) _ _
    (L₂.p (G.obj T'')) (L₂.semi _) (L₂.surj _) (L₂.ker _) (L₂.ρ (G.map b)) (mp F₂ (G.map b)) (L₂.nat (G.map b))
    (σ₂ _) (σ₂ _) (hσ₂ _) (hσ₂ _)
  have nl := sig_natural R R₀ I hI π hπ hk R₁ α _ _ (L.p (n.G.obj T'')) (L.semi _) (L.surj _) (L.ker _) _ _
    (L₂.p (G.obj T'')) (L₂.semi _) (L₂.surj _) (L₂.ker _) (l T'') (coefHom n T'') (hl T'')
    (σ _) (σ₂ _) (hσ _) (hσ₂ _)
  change extHom R₁ (mp F₂ (G.map b)) (-g T T' a) - -g T T'' (a ≫ b) + -g T' T'' b =
    extHom R₁ (coefHom n T'') (z.1 _ _ _ (n.G.map a) (n.G.map b)) -
      extHom R₁ (coefHom (CoefMap.restrict F₂ G) T'') (z₂.1 _ _ _ (G.map a) (G.map b))
  rw [extHom_coefHom_restrict, ← sub_eq_zero]
  refine GlobalTheory.T.augmentation_sigma_map_injective_of_flat R R₀ I hI π hπ hk R₁ α _ _ (L₂.p (G.obj T'')) (L₂.semi _) (L₂.surj _) (L₂.ker _)
    (σ₂ _) (hσ₂ _) _ ?_ ?_
  · refine ksub _ _ (kadd _ _ (ksub _ _ ?_ (kneg _ (hgK _ _ _))) (kneg _ (hgK _ _ _)))
      (ksub _ _ (nl.2 _ (hz _ _ _ _ _).1) (hz₂ _ _ _ _ _).1)
    rw [map_neg]; exact kneg _ (nb.2 _ (hgK _ _ _))
  · change σ₂ (G.obj T'') ((_ : R₁ ⊗[R₀] F₂.obj (G.obj T'')) -
      (_ - z₂.1 (G.obj T) (G.obj T') (G.obj T'') (G.map a) (G.map b))) = 0
    simp only [map_sub, map_add, map_neg]
    rw [← nb.1, ← nl.1, hg, hg, hg, (hz _ _ _ _ _).2, (hz₂ _ _ _ _ _).2, ← hw, w.2 (n.G.map a)]
    linear_combination key T T' T'' a b (w.1 _)

end GlobalTheory.Obs
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenseSectionsOfAlgebraicAffineNbhdStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.denseSections_of_algebraic_affineNbhd : (∀ (R : Type) [CommRing R] [IsLocalRing R], IsAdicComplete (maximalIdeal R) R → ∀ (A : Type) [CommRing A] [Algebra R A] [Algebra.Smooth R A] (ε : A →ₐ[R] R) (Ω : Type) [Field Ω] [Algebra R Ω], RingHom.ker (algebraMap R Ω) ≠ maximalIdeal R → IrreducibleSpace (PrimeSpectrum (TensorProduct R Ω A)) → ∀ f : TensorProduct R Ω A, ¬ IsNilpotent f → ∃ a : A →ₐ[R] R, GlobalTheory.DenseSec.pt ((Algebra.ofId R Ω).comp a) f ≠ 0) → ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R], IsAdicComplete (maximalIdeal R) R → ∀ (U : Over (Sp R)), Smooth U.hom → ∀ (e : Sp R ⟶ U.left), e ≫ U.hom = 𝟙 _ → ∀ (Ω : Type) [Field Ω] (x : Sp Ω ⟶ Sp R), closedPoint R ∉ Set.range x → IrreducibleSpace (pullback U.hom x : Scheme.{0}) → ∀ O : (pullback U.hom x).Opens, (O : Set (pullback U.hom x : Scheme.{0})).Nonempty → ∃ (a : Sp R ⟶ U.left) (aΩ : Sp Ω ⟶ pullback U.hom x), a ≫ U.hom = 𝟙 _ ∧ aΩ ≫ pullback.fst _ _ = x ≫ a ∧ aΩ ≫ pullback.snd _ _ = 𝟙 _ ∧ Set.range aΩ ⊆ O := by
  first | exact @GlobalTheory.DenseAff.denseSections_of_algebraic | exact GlobalTheory.DenseAff.denseSections_of_algebraic | (intros; apply GlobalTheory.DenseAff.denseSections_of_algebraic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DepthOscillationLeBoundEveryPrimeStatement
section
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.depthOscillation_le_bound_every_prime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (F k m M : ℕ) (Mb Sm : ℝ) (cx : Lt1 Dw → ℕ), Shape Dw F k m → ExpBd Dw k cx Mb Sm M → ∀ (vd : ℕ → ℝ) (S R : Finset ℕ), (∀ q, 0 ≤ vd q) → (∀ (q : ℕ) [Fact q.Prime], q ∈ S → UpperTheory.Depth.SplitPlaces q H F (vd q)) → 2 ∈ S → H.d ∈ R → (∀ q : ℕ, q.Prime → q ∉ S → q ∉ R → ¬ (q : ℤ) ∣ discr E) → ∀ (p : ℕ) [Fact p.Prime], OscLe Xo c p cx (eOf F (Dw.p + Dw.q) k m Mb Sm vd M S R p) := by
  first | exact @GlobalTheory.RefSum.oscLe_eOf | exact GlobalTheory.RefSum.oscLe_eOf | (intros; apply GlobalTheory.RefSum.oscLe_eOf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationContractionLieDerivativeDeRhamRulesStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivationContraction_lieDerivative_deRham_rules : (∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (v : Derivation R B B), (∀ b, ctr v (algebraMap B (DR R B) b) = 0) ∧ (∀ ω, ctr v (ι1 ω) = algebraMap B (DR R B) (v.liftKaehlerDifferential ω)) ∧ (∀ x y, ctr v (x * y) = ctr v x * y + sgn x * ctr v y) ∧ (∀ x, ctr v (ctr v x) = 0) ∧ (∀ x, ctr v (sgn x) = -sgn (ctr v x)) ∧ ∀ (j : ℕ), ∀ x ∈ ⋀[B]^(j + 1) Ω[B⁄R], ctr v x ∈ ⋀[B]^j Ω[B⁄R]) ∧ ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (v : Derivation R B B), (∀ x y, lie v (x * y) = lie v x * y + x * lie v y) ∧ (∀ b, lie v (algebraMap B (DR R B) b) = algebraMap B (DR R B) (v b)) ∧ (∀ b, lie v (ι1 (D R B b)) = ι1 (D R B (v b))) ∧ (∀ x, lie v (dDR R B x) = dDR R B (lie v x)) ∧ (∀ x, lie v (ctr v x) = ctr v (lie v x)) ∧ ∀ (j : ℕ), ∀ x ∈ ⋀[B]^j Ω[B⁄R], lie v x ∈ ⋀[B]^j Ω[B⁄R] := by
  first | exact @GlobalTheory.PDForm.ctr_lie_rules | exact GlobalTheory.PDForm.ctr_lie_rules | (intros; apply GlobalTheory.PDForm.ctr_lie_rules <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationTaylorPowerSeriesDerivationEqPderivStatement
section
open IsLocalRing GlobalTheory.FormalOrigin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivationTaylorPowerSeries_derivation_eq_pderiv : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra ℚ B] (n : ℕ) (ev : A →+* B) (ds : Fin n → Derivation ℤ A A), (∀ a b f, ds a (ds b f) = ds b (ds a f)) → ∀ a f, taylor ev (fun i => ⇑(ds i)) (ds a f) = MvPowerSeries.pderiv B a (taylor ev (fun i => ⇑(ds i)) f) := by
  first | exact @GlobalTheory.FormalOrigin.TaylorDeriv.taylor_deriv_eq_pderiv | exact GlobalTheory.FormalOrigin.TaylorDeriv.taylor_deriv_eq_pderiv | (intros; apply GlobalTheory.FormalOrigin.TaylorDeriv.taylor_deriv_eq_pderiv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationTaylorPowerSeriesOfDerivationsKillStatement
section
open IsLocalRing GlobalTheory.FormalOrigin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivationTaylorPowerSeries_of_derivations_kill : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra ℚ B] (n : ℕ) (ev : A →+* B) (ds : Fin n → Derivation ℤ A A) (c : A), (∀ i, ds i c = 0) → taylor ev (fun i => ⇑(ds i)) c = MvPowerSeries.C (ev c) := by
  first | exact @GlobalTheory.FormalOrigin.taylor_const | exact GlobalTheory.FormalOrigin.taylor_const | (intros; apply GlobalTheory.FormalOrigin.taylor_const <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivativeCechCocycleInvariantVectorFieldIsCobouStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivative_cechCocycle_invariantVectorField_isCoboundary : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (J : Type) (V : J → A.left.Opens), ⨆ a, V a = ⊤ → ∀ φ : ∀ a b, Γ(A.left, V a ⊓ V b), (∀ (a b c : J) (P : GPt A), P.In (V a) → P.In (V b) → P.In (V c) → valR P.x _ (φ a b) + valR P.x _ (φ b c) = valR P.x _ (φ a c)) → ∀ v : epsR K ⟶ A, IsTangent v → ∃ ψ : J → PtFn (A.hom ≫ 𝟙 (Sp K)), (∀ a, IsNat (V a) (ψ a)) ∧ ∀ (a b : J) (P : GPt A), P.In (V a) → P.In (V b) → (valR (P.trx v) _ (φ a b)).snd = ψ a P - ψ b P := by
  first | exact @GlobalTheory.CechInv.deriv_cocycle_isCoboundary | exact GlobalTheory.CechInv.deriv_cocycle_isCoboundary | (intros; apply GlobalTheory.CechInv.deriv_cocycle_isCoboundary <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescentCocycleDefectIsTripleCocycle
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot
open GlobalTheory.LBDescent GlobalTheory.DescNorm

namespace GlobalTheory.PolRoot

private theorem gm_charPullTop {X T : Scheme.{0}} (r : T ⟶ X) (t : T) (a : Γ(X, ⊤)ˣ) :
    gm (𝟙 T) t ⊤ (GlobalTheory.CharKer.pullTop r a) = gm r t ⊤ a :=
  (gm_pull (𝟙 T) r t ⊤ trivial a).trans (by rw [Category.id_comp])

theorem defect_tri {X Y T : Scheme.{0}} {f : X ⟶ Y} {M : LB X} {φ : ∀ i j, Γ(pullback f f, chart f M i j)ˣ}
    {D : Γ(Triple f, ⊤)ˣ} (h : Defect f M φ D) (a b c : T ⟶ X) (h₁ : a ≫ f = b ≫ f) (h₂ : b ≫ f = c ≫ f)
    (t : T) (i j k : M.ι) (hi : a t ∈ M.U i) (hj : b t ∈ M.U j) (hk : c t ∈ M.U k) :
    gm (tri f a b c h₁ h₂) t ⊤ D * gm (pullback.lift a c (h₁.trans h₂)) t _ (φ i k) =
      gm (pullback.lift a b h₁) t _ (φ i j) * gm (pullback.lift b c h₂) t _ (φ j k) := by
  have e₁ : tri f a b c h₁ h₂ ≫ pullback.fst (pullback.snd f f) (pullback.fst f f) = pullback.lift a b h₁ :=
    pullback.lift_fst _ _ _
  have e₂ : tri f a b c h₁ h₂ ≫ pullback.snd (pullback.snd f f) (pullback.fst f f) = pullback.lift b c h₂ :=
    pullback.lift_snd _ _ _
  have e₃ : tri f a b c h₁ h₂ ≫ pr13 f = pullback.lift a c (h₁.trans h₂) := by
    apply pullback.hom_ext
    · rw [pr13, Category.assoc, pullback.lift_fst, reassoc_of% e₁, pullback.lift_fst]
      try rw [pullback.lift_fst]
    · rw [pr13, Category.assoc, pullback.lift_snd, reassoc_of% e₂, pullback.lift_snd]
      try rw [pullback.lift_snd]
  have := h T (tri f a b c h₁ h₂) t i j k
    (by rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, reassoc_of% e₁, pullback.lift_fst]; exact hi)
    (by rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, reassoc_of% e₁, pullback.lift_snd]; exact hj)
    (by rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, reassoc_of% e₂, pullback.lift_snd]; exact hk)
  rwa [e₁, e₂, e₃] at this

theorem triCocycle_of_defect : ∀ (X Y : Scheme.{0}) (f : X ⟶ Y) (M : LB X), M.IsLB → ∀ (φ : ∀ i j, Γ(pullback f f, chart f M i j)ˣ) (D : Γ(Triple f, ⊤)ˣ), Defect f M φ D → TriCocycle f D := by
  intro X Y f M hM φ D h T a b c d h₁ h₂ h₃
  refine unit_ext fun t _ => ?_
  obtain ⟨i, hi⟩ := exists_chart hM (a t)
  obtain ⟨j, hj⟩ := exists_chart hM (b t)
  obtain ⟨k, hk⟩ := exists_chart hM (c t)
  obtain ⟨l, hl⟩ := exists_chart hM (d t)
  have e₁ := defect_tri h a b c h₁ h₂ t i j k hi hj hk
  have e₂ := defect_tri h a c d (h₁.trans h₂) h₃ t i k l hi hk hl
  have e₃ := defect_tri h b c d h₂ h₃ t j k l hj hk hl
  have e₄ := defect_tri h a b d h₁ (h₂.trans h₃) t i j l hi hj hl
  rw [map_mul, map_mul, gm_charPullTop, gm_charPullTop, gm_charPullTop, gm_charPullTop]
  apply mul_right_cancel (b := gm (pullback.lift a d ((h₁.trans h₂).trans h₃)) t _ (φ i l))
  rw [_root_.mul_assoc, _root_.mul_assoc, e₂, e₄, ← _root_.mul_assoc, e₁, _root_.mul_left_comm, e₃, _root_.mul_assoc]

end GlobalTheory.PolRoot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescentCocycleDefectNormalisedEqOneStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open GlobalTheory.LBDescent GlobalTheory.DescNorm
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.descentCocycleDefect_normalised_eq_one : ∀ (K : Type) [Field K] (A A' B : Over (Sp K)) [GrpObj A] [GrpObj B] (q : A ⟶ A') (P : LB (A ⊗ B).left) (τ : LB.Gen (ev P (𝟙 A) (1 : A ⟶ B))), P.IsLB → ∀ (φ : ∀ i j, Γ(pullback (q ▷ B).left (q ▷ B).left, chart (q ▷ B).left P i j)ˣ) (D : Γ(Triple (q ▷ B).left, ⊤)ˣ), NormAlong q P τ φ → Defect (q ▷ B).left P φ D → ∀ w : Triple (q ▷ B).left, gm (rhoW q) w ⊤ D = 1 := by
  first | exact @GlobalTheory.DescNorm.defect_normalised | exact GlobalTheory.DescNorm.defect_normalised | (intros; apply GlobalTheory.DescNorm.defect_normalised <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantNonzeroDifferentialsStatement
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
  IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (IsDefSum polydisc defCoord cWt)

attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.determinant_nonzero_differentials : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (X : Obj F 𝔠 (Sp ℂ)) (L : LB X.A.left)
    (u : HolUnif X.A L (Module.finrank ℚ F)) (δ : X.DetGen) (v : Fin (Module.finrank ℚ F) → X.Lie)
    (W : Matrix (Fin (Module.finrank ℚ F)) (Fin (Module.finrank ℚ F)) ℂ),
    (∀ j, u.IsDiff (W j) (v j).hom) → W.det ≠ 0 → δ.1 v ≠ 0 := by
  first | exact @GlobalTheory.LatJet.detGen_apply_ne_zero_of_isDiff | exact GlobalTheory.LatJet.detGen_apply_ne_zero_of_isDiff | (intros; apply GlobalTheory.LatJet.detGen_apply_ne_zero_of_isDiff <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagSumPullTwo
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem diagSum_pullTwo : ∀ (R : Type) [CommRing R] (D D' : Type) [CommRing D] [Bialgebra R D]
    [Coalgebra.IsCocomm R D] [CommRing D'] [Bialgebra R D'] [Coalgebra.IsCocomm R D'] (f : D →ₐc[R] D')
    (m : ℕ) (c : D ⊗[R] D), f (diagSum R D m c) = diagSum R D' m (pullbackTwo f c) := by
  intro R _ D D' _ _ _ _ _ _ f m c
  induction c using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    simp only [diagSum_tmul, pullbackTwo, TensorProduct.map_tmul, map_sum, map_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mulBy]
    rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

end GlobalTheory.PtExt
end

