import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2765
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2670
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0587
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2416
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2766
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0060
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.GeneratorValues
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPsiCoordOfIsPsiCoord
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0691
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0714
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2776
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHtFunGenericIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2767
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvTranspose
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2672
import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2736
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2768

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPullbackChainCompatStatement
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_pullback_chain_compat : ∀ (R₀ R : Subring ℂ) (ic : R₀ →+* R), (∀ x, ((ic x : R) : ℂ) = x) →
  ∀ (G₀ : Over (Sp R₀)) [GrpObj G₀] (G : Over (Sp R)) [GrpObj G] (A : Over (Sp ℂ)) [GrpObj A]
    (g : G.left ⟶ G₀.left) (p : A.left ⟶ G.left), IsGrpPullback G G₀ (spMap ic) g → IsGrpPullback A G (spMap R.subtype) p →
    ∀ (v₀ : epsR R₀ ⟶ G₀) (v' : epsR ℂ ⟶ A), IsTangent v₀ →
      v'.left ≫ p ≫ g = spMap (Chart.dualMapR R₀.subtype) ≫ v₀.left →
      ∃ v : epsR R ⟶ G, IsTangent v ∧ v'.left ≫ p = spMap (Chart.dualMapR R.subtype) ≫ v.left := by
  first | exact @GlobalTheory.TangentBaseChange.exists_tangent_baseChange | exact GlobalTheory.TangentBaseChange.exists_tangent_baseChange | (intros; apply GlobalTheory.TangentBaseChange.exists_tangent_baseChange <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPullbackPrimitiveCrystallineClassEpsPartIStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangentPullback_primitiveCrystallineClass_epsPart_isCob : ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (f : Z1 (O (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _))), CatCoh.H1.mk _ f ∈ primDR (A ⊗ B) → ∀ v : epsR R ⟶ B, Cohom (whole A) (sndPull (fv f) v) (Fn1.zero A) := by
  first | exact @GlobalTheory.PtExt.cohom_sndPull_zero | exact GlobalTheory.PtExt.cohom_sndPull_zero | (intros; apply GlobalTheory.PtExt.cohom_sndPull_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentVectorSectionValueEqExpansionSumStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.tangentVector_section_value_eq_expansion_sum : AllVC fun {V} _ _ _ {D} {A} {G} _ _ U {C} _ _ {N} ν => ∀ (w₀ : GlobalTheory.UT.W0 U.toUnifPre) (ρ : LB.Gen (A.L.pull (eSec A.A))), GlobalTheory.UT.NormW U.toUnifPre w₀ ρ → ∀ (y : epsR V ⟶ G) (gm₀ : GtPt D.toPre (epsR V)) (gm : GtPt D.toPre (TE V C)) (yA : Sp (DualNumber C) ⟶ (TFK (R := V) C ⊗ A.A).left), IsTangent y → TanRel U.toUnifPre y gm₀ → GtPt.IsPull (spMap (dualMap (toF V C))) gm₀ gm → VecAt U.toUnifPre C y yA → ∀ (k : ℕ) (i₀ : A.L.ι), ⊤ ≤ (jFK (R := V) C ≫ eSec A.A) ⁻¹ᵁ A.L.U i₀ → ∃ c : C, ∀ (t : GlobalTheory.UT.SecA A C k) (s : Fam D.toPre C k), U.ExpandsF C k w₀ t s → (Summable fun α => (jc ν s gm α).fst / ν.rg ^ k) ∧ (Summable fun α => (jc ν s gm α).snd / ν.rg ^ k) ∧ valR yA ((LPow A.A A.L (k : ℤ) (TFK (R := V) C)).U fun _ => i₀) (t.f fun _ => i₀) = TrivSqZeroExt.inl (valR (jFK (R := V) C) ((A.L.pull (eSec A.A)).U fun _ => i₀) (ρ.s fun _ => i₀).val ^ k) * (TrivSqZeroExt.inl (∑' α, (jc ν s gm α).fst / ν.rg ^ k) + TrivSqZeroExt.inr ((∑' α, (jc ν s gm α).snd / ν.rg ^ k) + c * ∑' α, (jc ν s gm α).fst / ν.rg ^ k)) := by
  first | exact @GlobalTheory.MBLow.TanExp.value_at_tangent | exact GlobalTheory.MBLow.TanExp.value_at_tangent | (intros; apply GlobalTheory.MBLow.TanExp.value_at_tangent <;> assumption) | exact @GlobalTheory.MBLow.TanExp.ds_sum | exact GlobalTheory.MBLow.TanExp.ds_sum | (intros; apply GlobalTheory.MBLow.TanExp.ds_sum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TauCoordinateEqUnitMulPsiQuotientStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tauCoordinate_eq_unit_mul_psi_quotient : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (a b : D.X)
    (x x₁ x₂ x₃ : (FractionRing R)ˣ), IsTauCoord D a b x → IsPsiCoord D (a + b) x₁ → IsPsiCoord D a x₂ →
      IsPsiCoord D b x₃ → ∃ u : Rˣ, (x : FractionRing R) =
        algebraMap R (FractionRing R) u * x₁ * (x₂ : FractionRing R)⁻¹ * (x₃ : FractionRing R)⁻¹ := by
  first | exact @GlobalTheory.TauCoordQuot.main | exact GlobalTheory.TauCoordQuot.main | (intros; apply GlobalTheory.TauCoordQuot.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TauDiagEqUnitMulPsiSq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.E8Ring
open GlobalTheory.Mum.UnitValuedLeadingSection

noncomputable section

namespace GlobalTheory.Mum.UnitValuedLeadingSection

theorem left_comp_hom_unit {R : Type} [CommRing R] {B : Over (Spec (CommRingCat.of R))}
    (s : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ B) : s.left ≫ B.hom = 𝟙 _ :=
  Over.w s

theorem toUnit_TK_left (R : Type) [CommRing R] [IsDomain R] : (toUnit (TK R)).left = jK R :=
  Over.w (toUnit (TK R))

theorem tau_diag_eq_unit_mul_psi_sq (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R)
    (hT : D.TauBimult) (hE : D.PsiEven) (z : (TK R).left) (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι)
    (hJ : TopGood D.P z J) (y : D.X) :
    ∃ u : Rˣ, val (D.tau y y) (𝟙 _) z J = uK R z u * val (D.psi y) (𝟙 _) z J ^ 2 := by
  have hG := hJ.1
  set P : D.X → ((TK R).left.presheaf.stalk z)ˣ := fun χ => val (D.psi χ) (𝟙 _) z J with hPdef
  have hP : ∀ χ, val (D.psi χ) (𝟙 _) z J = P χ := fun _ => rfl
  set rg := val D.rigK (𝟙 _) z J with hrgdef

  have h1 : ∀ a b, val (D.tau a b) (𝟙 _) z J = P (a + b) * (P a)⁻¹ * (P b)⁻¹ * rg⁻¹ := by
    intro a b
    unfold DegPre.tau
    rw [val_mul hG, val_mul hG, val_mul hG, val_inv, val_inv, val_inv]

  obtain ⟨r, hr⟩ : ∃ u : Rˣ, rg = uK R z u := by
    rw [hrgdef]
    unfold DegPre.rigK
    rw [val_pull hG, Category.id_comp, toUnit_TK_left]
    have e : jK R = jK R ≫ (𝟙 (Spec (CommRingCat.of R)) : Spec (CommRingCat.of R) ⟶ (𝟙_ (Over (Spec (CommRingCat.of R)))).left) :=
      (Category.comp_id _).symm
    rw [e]
    exact val_section_unit D.P z J hJ D.rig _ (fun _ => by
      rw [Category.id_comp]; exact left_comp_hom_unit (η[D.P.A]))

  set C : D.X → D.X → D.X → ((TK R).left.presheaf.stalk z)ˣ :=
    fun a a' b => val D.cub.t (D.pt3 a a' b) z J with hCdef
  have h2 : ∀ a a' b, val (D.tau (a + a') b) (𝟙 _) z J * C a a' b =
      val (D.tau a b) (𝟙 _) z J * val (D.tau a' b) (𝟙 _) z J := by
    intro a a' b
    have := (val_mul hG _ _ _).symm.trans ((val_corr hG (hT a a' b) (𝟙 _)).trans (val_mul hG _ _ _))
    have hp : val (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 a a' b)) (𝟙 _) z J = C a a' b :=
      (val_pull hG D.cub.t (D.pt3 a a' b) (𝟙 _)).trans (by rw [Category.id_comp])
    exact (congrArg (fun x => val (D.tau (a + a') b) (𝟙 _) z J * x) hp).symm.trans this
  have hC : ∀ a a' b, ∃ u : Rˣ, C a a' b = uK R z u := by
    intro a a' b
    have e : D.pt3 a a' b = jK R ≫ (lift (D.c a) (lift (D.c a') (D.c b))).left := by
      unfold DegPre.pt3
      rw [← comp_lift, ← comp_lift, Over.comp_left, toUnit_TK_left]
    show ∃ u : Rˣ, val D.cub.t (D.pt3 a a' b) z J = uK R z u
    rw [e]
    exact val_section_unit D.P z J hJ D.cub.t _ (fun k => by
      rw [← Over.comp_left]; exact left_comp_hom_unit _)

  set S : D.X → ((TK R).left.presheaf.stalk z)ˣ :=
    fun χ => val D.sym (D.xK χ) z J with hSdef
  have h3 : ∀ χ, P (-χ) * S χ = P χ := by
    intro χ
    have := (val_mul hG _ _ _).symm.trans (val_corr hG (hE χ) (𝟙 _))
    rw [val_pull hG, Category.id_comp] at this
    exact this
  have hS : ∀ χ, ∃ u : Rˣ, S χ = uK R z u := by
    intro χ
    have e : D.xK χ = jK R ≫ (D.c χ).left := by
      show (toUnit (TK R) ≫ D.c χ).left = _
      rw [Over.comp_left, toUnit_TK_left]
    show ∃ u : Rˣ, val D.sym (D.xK χ) z J = uK R z u
    rw [e]
    refine val_section_unit D.P z J hJ D.sym _ (fun k => ?_)
    fin_cases k
    · show ((D.c χ).left ≫ (ι[D.P.A]).left) ≫ D.P.A.hom = 𝟙 _
      rw [← Over.comp_left]; exact left_comp_hom_unit _
    · show ((D.c χ).left ≫ 𝟙 D.P.A.left) ≫ D.P.A.hom = 𝟙 _
      rw [Category.comp_id]; exact left_comp_hom_unit _

  obtain ⟨c0, hc0⟩ := hC 0 0 0
  obtain ⟨c1, hc1⟩ := hC y (-y) y
  obtain ⟨s, hs⟩ := hS y
  have e0 := h2 0 0 0
  simp only [h1, add_zero] at e0

  have hP0 : P 0 = (C 0 0 0 * rg)⁻¹ := by
    have : C 0 0 0 = P 0 * (P 0)⁻¹ * (P 0)⁻¹ * rg⁻¹ := mul_left_cancel e0
    rw [this]; group
  have e1 := h2 y (-y) y
  simp only [h1, add_neg_cancel, zero_add, neg_add_cancel] at e1
  have hPm : P (-y) = P y * (S y)⁻¹ := by rw [← h3 y]; group
  rw [hPm, hP0] at e1
  refine ⟨(c0 * r) ^ 2 * c1 * s⁻¹, ?_⟩
  rw [h1, map_mul, map_mul, map_inv, map_pow, map_mul, ← hc0, ← hc1, ← hs, ← hr, hP y]

  rw [eq_mul_inv_of_mul_eq e1.symm]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_pow]
  abel

end GlobalTheory.Mum.UnitValuedLeadingSection
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalBasePeriodsFactorMulGeneratorStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tautologicalBase_periods_factor_mul_generator : ∀ {o W V : Type} [CommRing o] [CommRing W] [IsLocalRing W] [CommRing V] [IsDomain V] (T : GlobalTheory.PolDeg.TautBase o W) (iw : W →+* V) {I : Type} [Fintype I] (s : I → V) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (Q : Data V) (e : Q.X ≃+ (Fin T.r → ℤ)), DataFrom T iw s ε n Q e → ∀ a b : Q.X, ∃ k : (FractionRing V)ˣ, (k : FractionRing V) = ∏ i, algebraMap V (FractionRing V) (s i) ^ ((n : ℤ) * ε i (e a) (e b)) ∧ Q.TauCoord a b k := by
  first | exact @GlobalTheory.TautTau.tauCoord_of_dataFrom | exact GlobalTheory.TautTau.tauCoord_of_dataFrom | (intros; apply GlobalTheory.TautTau.tauCoord_of_dataFrom <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoUniformlyOfFamAt
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField Filter Topology TopologicalSpace Set
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ArInt GlobalTheory.VB GlobalTheory.CxPts GlobalTheory.Points
open scoped ContDiff

namespace GlobalTheory.MetFam

section Fam

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}
  {F G : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

def FamAt (t : ℝ → ℝ) (u : ℝ → CxPts p σ → F) (u₀ : CxPts p σ → F) (y : CxPts p σ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (f : CxPts p σ → ι → ℂ) (Φ : ℝ × (ι → ℂ) → F) (O : Set (ℝ × (ι → ℂ))),
    VInfAt f y ∧ IsOpen O ∧ (0, f y) ∈ O ∧ ContDiffOn ℝ ∞ Φ O ∧ (u₀ =ᶠ[𝓝 y] fun z => Φ (0, f z)) ∧
      ∀ᶠ x : ℝ × CxPts p σ in atTop ×ˢ 𝓝 y, u x.1 x.2 = Φ (t x.1, f x.2)

variable {t : ℝ → ℝ} {u u' : ℝ → CxPts p σ → F} {u₀ u₀' : CxPts p σ → F} {y : CxPts p σ}

theorem FamAt.congr (h : FamAt t u u₀ y) (e : ∀ᶠ x : ℝ × CxPts p σ in atTop ×ˢ 𝓝 y, u' x.1 x.2 = u x.1 x.2)
    (e₀ : u₀' =ᶠ[𝓝 y] u₀) : FamAt t u' u₀' y :=
  have ⟨ι, i, f, Φ, O, h₁, h₂, h₃, h₄, h₅, h₆⟩ := h
  ⟨ι, i, f, Φ, O, h₁, h₂, h₃, h₄, e₀.trans h₅, (e.and h₆).mono fun _ hx => hx.1.trans hx.2⟩

theorem famAt_param (t : ℝ → ℝ) (y : CxPts p σ) : FamAt t (fun R _ => t R) (fun _ => (0 : ℝ)) y :=
  ⟨Empty, inferInstance, fun _ => 0, Prod.fst, univ, vInfAt_const _ _, isOpen_univ, trivial, contDiff_fst.contDiffOn,
    EventuallyEq.rfl, .of_forall fun _ => rfl⟩

theorem famAt_const (h : VInfAt u₀ y) (t : ℝ → ℝ) : FamAt t (fun _ => u₀) u₀ y := by
  obtain ⟨W, ι, _, g, Φ, O, h₁, h₂, h₃, h₄, h₅⟩ := h
  exact ⟨ι, inferInstance, fun z a => ev p σ W (g a) z, fun x => Φ x.2, Prod.snd ⁻¹' O,
    vInfAt_pi fun a => vInfAt_ev _ h₁, h₂.preimage continuous_snd, h₃,
    h₄.comp contDiff_snd.contDiffOn fun _ hx => hx, h₅, tendsto_snd.eventually h₅⟩

theorem FamAt.comp (h : FamAt t u u₀ y) {Ψ : F → G} {T : Set F} (hT : IsOpen T) (hy : u₀ y ∈ T)
    (hΨ : ContDiffOn ℝ ∞ Ψ T) : FamAt t (fun R z => Ψ (u R z)) (fun z => Ψ (u₀ z)) y := by
  obtain ⟨ι, _, f, Φ, O, h₁, h₂, h₃, h₄, h₅, h₆⟩ := h
  exact ⟨ι, inferInstance, f, Ψ ∘ Φ, O ∩ Φ ⁻¹' T, h₁, h₄.continuousOn.isOpen_inter_preimage h₂ hT,
    ⟨h₃, mem_preimage.2 (h₅.self_of_nhds ▸ hy :)⟩, hΨ.comp (h₄.mono inter_subset_left) fun _ hv => hv.2,
    h₅.fun_comp Ψ, h₆.mono fun _ hx => congrArg Ψ hx⟩

theorem FamAt.comp_contDiff (h : FamAt t u u₀ y) {Ψ : F → G} (hΨ : ContDiff ℝ ∞ Ψ) :
    FamAt t (fun R z => Ψ (u R z)) (fun z => Ψ (u₀ z)) y := h.comp isOpen_univ trivial hΨ.contDiffOn

theorem FamAt.prodMk {v : ℝ → CxPts p σ → G} {v₀ : CxPts p σ → G} (h : FamAt t u u₀ y) (h' : FamAt t v v₀ y) :
    FamAt t (fun R z => (u R z, v R z)) (fun z => (u₀ z, v₀ z)) y := by
  obtain ⟨ι, _, f, Φ, O, h₁, h₂, h₃, h₄, h₅, h₆⟩ := h
  obtain ⟨ι', _, f', Φ', O', h₁', h₂', h₃', h₄', h₅', h₆'⟩ := h'
  have cl : ContDiff ℝ ∞ fun (x : ℝ × (ι ⊕ ι' → ℂ)) => (x.1, fun a => x.2 (.inl a)) :=
    contDiff_fst.prodMk (contDiff_pi.2 fun a => (contDiff_apply ℝ ℂ _).comp contDiff_snd)
  have cr : ContDiff ℝ ∞ fun (x : ℝ × (ι ⊕ ι' → ℂ)) => (x.1, fun a => x.2 (.inr a)) :=
    contDiff_fst.prodMk (contDiff_pi.2 fun a => (contDiff_apply ℝ ℂ _).comp contDiff_snd)
  refine ⟨ι ⊕ ι', inferInstance, fun z => Sum.elim (f z) (f' z),
    fun x => (Φ (x.1, fun a => x.2 (.inl a)), Φ' (x.1, fun a => x.2 (.inr a))),
    (fun x => (x.1, fun a => x.2 (.inl a))) ⁻¹' O ∩ (fun x => (x.1, fun a => x.2 (.inr a))) ⁻¹' O',
    vInfAt_pi fun a => ?_, (h₂.preimage cl.continuous).inter (h₂'.preimage cr.continuous), ⟨h₃, h₃'⟩,
    (h₄.comp cl.contDiffOn fun _ hv => hv.1).prodMk (h₄'.comp cr.contDiffOn fun _ hv => hv.2), ?_, ?_⟩
  · rcases a with a | a
    exacts [h₁.comp_contDiff (contDiff_apply ℝ ℂ a), h₁'.comp_contDiff (contDiff_apply ℝ ℂ a)]
  · filter_upwards [h₅, h₅'] with z e e' using Prod.ext e e'
  · filter_upwards [h₆, h₆'] with z e e' using Prod.ext e e'

theorem famAt_pi {ι : Type} [Fintype ι] {w : ℝ → CxPts p σ → ι → F} {w₀ : CxPts p σ → ι → F}
    (h : ∀ a, FamAt t (fun R z => w R z a) (fun z => w₀ z a) y) : FamAt t w w₀ y := by
  classical
  have key (s : Finset ι) : FamAt t (fun R z => ∑ a ∈ s, Pi.single a (w R z a) : ℝ → CxPts p σ → ι → F)
      (fun z => ∑ a ∈ s, Pi.single a (w₀ z a)) y := by
    induction s using Finset.induction_on with
    | empty => simpa using famAt_const (vInfAt_const (0 : ι → F) y) t
    | insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact ((h a).prodMk ih).comp_contDiff (Ψ := fun x => Pi.single a x.1 + x.2)
        (((ContinuousLinearMap.single ℝ (fun _ : ι => F) a).contDiff.comp contDiff_fst).add contDiff_snd)
  simpa only [Finset.univ_sum_single] using key Finset.univ

theorem FamAt.pull {q : Y ⟶ Sp k} (π : Y ⟶ X) (hπ : π ≫ p = q) {z : CxPts q σ}
    (h : FamAt t u u₀ (PtsOver.map π hπ _ z)) :
    FamAt t (fun R w => u R (PtsOver.map π hπ _ w)) (fun w => u₀ (PtsOver.map π hπ _ w)) z := by
  obtain ⟨ι, _, f, Φ, O, h₁, h₂, h₃, h₄, h₅, h₆⟩ := h
  have hc := (PtsOver.continuous_map π hπ (spMap σ)).continuousAt (x := z)
  exact ⟨ι, inferInstance, fun w => f (PtsOver.map π hπ _ w), Φ, O, h₁.pull π hπ, h₂, h₃, h₄, hc.eventually h₅,
    (tendsto_id.prodMap hc).eventually h₆⟩

theorem tendstoUniformly_of_famAt [CompactSpace (CxPts p σ)] (ht : Tendsto t atTop (𝓝 0)) (h : ∀ y, FamAt t u u₀ y) :
    TendstoUniformly u u₀ atTop := by
  rw [← tendstoLocallyUniformly_iff_tendstoUniformly_of_compactSpace, tendstoLocallyUniformly_iff_forall_tendsto]
  intro y
  obtain ⟨ι, _, f, Φ, O, h₁, h₂, h₃, h₄, h₅, h₆⟩ := h y
  have hΦ := h₄.continuousOn.continuousAt (h₂.mem_nhds h₃)
  have hf : Tendsto (fun x : ℝ × CxPts p σ => f x.2) (atTop ×ˢ 𝓝 y) (𝓝 (f y)) := h₁.continuousAt.tendsto.comp tendsto_snd
  have a₁ := hΦ.tendsto.comp ((tendsto_const_nhds (x := (0 : ℝ))).prodMk_nhds hf)
  have a₂ := hΦ.tendsto.comp ((ht.comp tendsto_fst).prodMk_nhds hf)
  refine ((a₁.prodMk_nhds a₂).mono_right (nhds_le_uniformity _)).congr' ?_
  filter_upwards [tendsto_snd.eventually h₅, h₆] with x e e'
  exact Prod.ext e.symm e'.symm

def VFam {E : X.Modules} {r : ℕ} (t : ℝ → ℝ) (h : ℝ → VMetric p E r) (h₀ : VMetric p E r) : Prop :=
  ∀ (σ : k →+* ℂ) (y : CxPts p σ), ∃ c : Chart E r, y ∈ ptsIn p σ c.U ∧
    ∀ a b, FamAt t (fun R z => ((h R).met σ).G c z a b) (fun z => (h₀.met σ).G c z a b) y

theorem VFam.pull {E : X.Modules} {r : ℕ} {h : ℝ → VMetric p E r} {h₀ : VMetric p E r} (H : VFam t h h₀)
    {q : Y ⟶ Sp k} (π : Y ⟶ X) (hπ : π ≫ p = q) : VFam t (fun R => (h R).pull π hπ) (h₀.pull π hπ) := fun σ z => by
  obtain ⟨c, hc, hf⟩ := H σ (PtsOver.map π hπ _ z)
  have hn : ∀ᶠ w in 𝓝 z, PtsOver.map π hπ _ w ∈ ptsIn p σ c.U :=
    (PtsOver.continuous_map π hπ (spMap σ)).continuousAt.eventually ((isOpen_ptsIn _).mem_nhds hc)
  refine ⟨c.pull h₀.isVB π, hc, fun a b => ((hf a b).pull π hπ).congr
    ((tendsto_snd.eventually hn).mono fun x hx => ?_) (hn.mono fun w hw => ?_)⟩
  · exact congrFun (congrFun (((h x.1).met σ).pull_G π hπ c hx) a) b
  · exact congrFun (congrFun ((h₀.met σ).pull_G π hπ c hw) a) b

def LFam (t : ℝ → ℝ) (L : ℝ → HermLB p) (L₀ : HermLB p) : Prop :=
  ∃ (u : ℝ → ∀ σ : k →+* ℂ, CxPts p σ → ℝ) (hu : ∀ R σ y, CInfAt (u R σ) y)
    (hc : ∀ R σ σ', (Weight.ofFun (u R σ)).IsConj (Weight.ofFun (u R σ'))),
    (∀ R, (L₀.raise (u R) (hu R) (hc R)).Isometric (L R)) ∧ ∀ σ y, FamAt t (fun R => u R σ) (fun _ => 0) y

end Fam

open GlobalTheory.ShFam GlobalTheory.Toroidal
open GlobalTheory.LieVB (omega unitSec dUnit)
open GlobalTheory.QCoh (pullbackSections)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l}
    {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz] {β : Oz →+* c.F}
    {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β}

def IsDualEigOn (G : ∀ σ', EigMet Z σ') {T : Scheme.{0}} (j : T ⟶ Z.X) {q : T ⟶ Sp Oz} {g : ℕ}
    (h : VMetric q ((Scheme.Modules.pullback j).obj (omega Z.t.G)) g) : Prop :=
  ∀ (σ' : c.F →+* ℂ) (yc : CxPts (genStr Z) σ') (y : CxPts q (σ'.comp β)), y.1 ≫ j = yc.1 ≫ genι Z →
    ∀ (u : EigFrame Z σ' (yc.1 ≫ genι Z)) (U : Z.X.Opens) (W : Z.t.G.left.Opens) (hU : U ≤ unitSec Z.t.G ⁻¹ᵁ W)
      (f f' : Γ(Z.t.G.left, W)), y ∈ ptsIn q (σ'.comp β) (j ⁻¹ᵁ U) →
      (h.met (σ'.comp β)).form (pullbackSections j _ (le_refl (j ⁻¹ᵁ U)) (dUnit Z.t.G hU f))
          (pullbackSections j _ (le_refl (j ⁻¹ᵁ U)) (dUnit Z.t.G hU f')) y =
        ∑ τ : E →+* ℂ, HermFrame.form ((G σ').gram yc u τ)⁻¹ (fun i => (valR (u.v τ i) W f).snd)
          fun i => (valR (u.v τ i) W f').snd

theorem isDualEigOn_pull {G : ∀ σ', EigMet Z σ'} {g : ℕ} {h : VMetric Z.s (omega Z.t.G) g}
    (hd : VdmRec.IsDualEig G h) {T : Scheme.{0}} (j : T ⟶ Z.X) {q : T ⟶ Sp Oz} (w : j ≫ Z.s = q) :
    IsDualEigOn G j (h.pull j w) :=
  fun σ' yc y e u U W hU f f' hy =>
    ((h.met _).form_pull j w _ _ le_rfl hy).trans (hd σ' yc (PtsOver.map j w _ y) e u U W hU f f' hy)

end GlobalTheory.MetFam

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorActionCompatibleWithDegenerationStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_action_compatible_with_degeneration : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D D' W) (s : SymUnit r), letI := T.mod s; ∀ (a : TensO s) (y : D'.X), D'.c (a • y) = D'.c y ≫ T.act (TensO.mat s a) := by
  first | exact @GlobalTheory.Mum.Tens.c_smul | exact GlobalTheory.Mum.Tens.c_smul | (intros; apply GlobalTheory.Mum.Tens.c_smul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataCubicalStructureValuesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorData_cubicalStructure_values : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N) (ν' : NumOf D'.toPre F N'), ∀ x y u, (N'.θ x y u : F) * wv T ν ν' (x * y * u) * wv T ν ν' x * wv T ν ν' y * wv T ν ν' u =
    ((∏ i, ∏ j, (N.θ (cmp T ν ν' x i * cmp T ν ν' x j) (cmp T ν ν' y i * cmp T ν ν' y j) (cmp T ν ν' u i * cmp T ν ν' u j) /
        (N.θ (cmp T ν ν' x i) (cmp T ν ν' y i) (cmp T ν ν' u i) * N.θ (cmp T ν ν' x j) (cmp T ν ν' y j) (cmp T ν ν' u j))) ^ W i j : Fˣ) : F) *
      wv T ν ν' (x * y) * wv T ν ν' (x * u) * wv T ν ν' (y * u) * wv T ν ν' 1 := by
  first | exact @GlobalTheory.Mum.TensCube.theta_tens | exact GlobalTheory.Mum.TensCube.theta_tens | (intros; apply GlobalTheory.Mum.TensCube.theta_tens <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataPsiValuesThroughBundleIsoStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorData_psi_values_through_bundleIso : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N) (ν' : NumOf D'.toPre F N'), ∀ χ', (N'.ψ χ' : F) * wv T ν ν' 1 = wv T ν ν' (N'.c χ') * ((∏ i, ∏ j, N.τ (chi T ν ν' χ' i) (chi T ν ν' χ' j) ^ W i j : Fˣ) : F) := by
  first | exact @GlobalTheory.Mum.TensTor.tensFacts_psi | exact GlobalTheory.Mum.TensTor.tensFacts_psi | (intros; apply GlobalTheory.Mum.TensTor.tensFacts_psi <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDegenerationDataTauBimultiplicative
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.TensPolBimult

theorem base_of_isCN {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (h : IsCN R) : Base R :=
  ⟨⟨h.1, inferInstance, h.2.1, h.2.2.1⟩, h.2.2.2⟩

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (Q : Data R) (D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (pr : Fin r → (D'.P.A ⟶ Q.B)), (∀ i, IsMonHom (pr i)) → IsLimit (Fan.mk D'.P.A pr) → ∀ (xe : D'.X ≃+ (Fin r → Q.X)), (∀ z i, D'.c z ≫ pr i = Q.c (xe z i)) → ∀ (w : LB.Iso D'.P.L (LB.LinComb Q.M.L (tensφ pr) (tensε W))), w.IsGen → (∀ y z J J', Good Q.M.L z J → Good D'.P.L z J' → val (D'.psi y) (𝟙 _) z J' = gm (D'.xK y) z _ (w.s (fun k => J (D'.xK y ≫ tensφ pr k), J' (D'.xK y))) * ∏ i, ∏ j, val (Q.tau (xe y i) (xe y j)) (𝟙 _) z J ^ W i j) → (∀ (z : (TK R).left) (J : ((TK R).left ⟶ D'.P.A.left) → D'.P.L.ι), Good D'.P.L z J → val (D'.psi 0) (𝟙 _) z J * val D'.rigK (𝟙 _) z J = 1) → D'.TauBimult := by
  intro R _ _ _ hR Q D' r W pr hpr hlim xe hc w hw hpsi hn
  exact GlobalTheory.PolTensBimult.main R (base_of_isCN hR) Q D' W pr xe ⟨hpr, ⟨hlim⟩, hc, w, hw, hpsi⟩ hn

end GlobalTheory.TensPolBimult
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorTorsionPairingEqProdFactorPairingsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorTorsionPairing_eq_prod_factor_pairings : ∀ (F : Type) [Field F] (N N' : NumD F) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (φ : N'.A → Fin r → N.A) (e : N'.X → Fin r → N.X) (wv : N'.A → F), TensFacts W φ e wv → ∀ (k : ℕ), 1 ≤ k → ∀ (q' p' : N'.QT k) (qs ps : Fin r → N.QT k), QRelV W φ e wv q' qs → QRelV W φ e wv p' ps → N'.wp q' p' = ∏ i, ∏ j, N.wp (qs i) (ps j) ^ (W + W.transpose) i j := by
  first | exact @GlobalTheory.Mum.TensTor.PairVal.wp_eq_prod | exact GlobalTheory.Mum.TensTor.PairVal.wp_eq_prod | (intros; apply GlobalTheory.Mum.TensTor.PairVal.wp_eq_prod <;> assumption)
end

