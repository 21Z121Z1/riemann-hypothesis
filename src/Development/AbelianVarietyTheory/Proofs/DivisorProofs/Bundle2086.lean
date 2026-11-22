import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0322
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0260
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2081
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1466
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2068
import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2069
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.GreenSeriesSt
import Formalism.LocalToGlobal.GlobalTheory.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.LiftFrameEmbeddingBase
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0533
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardIndependentBoundedSectionsShiftedWeightLe
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0408
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0455
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2079
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0328
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2070
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0069
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsThetaSumSiegelSetLeTorusPower
section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TorusBound

theorem absTheta_le_torus : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (n : ℕ) (r : ℕ) (X Y : Matrix (Fin V.rank) (Fin r) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ c : ℝ, 0 < c → ∀ Q : Set (GA D V), IsCompact Q → ∀ Φ : schwartzA θ V.rank n, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ GlobalTheory.SiegelSet.cone r c, ∀ a : GA D V, GlobalTheory.SiegelSet.IsTorusElt D.sp.cm.sig V.gram X Y t a → ∀ y ∈ Q, GlobalTheory.SiegelFormula.absTheta V Φ.1 (a * y) ≤ ENNReal.ofReal (C * ∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n))) := by
  intro D θ hθ V n r X Y hXY c hc Q hQ Φ
  have hSB := GlobalTheory.T.isSchwartzBruhatAdelicMatrix_of_mem_adelicSchwartz D θ hθ V.rank n Φ.1 Φ.2
  obtain ⟨-, K, hK, hmaj⟩ := GlobalTheory.T.schwartzBruhatAdelicMatrix_continuous_le_majorant D θ hθ V.rank n Φ.1 hSB
  obtain ⟨K', hK', hmul⟩ := GlobalTheory.T.adelicMatrixSchwartzMajorant_inv_mul_le D θ hθ V n Q hQ K hK
  obtain ⟨N, C₁, hC₁, hframe⟩ := GlobalTheory.T.siegelTorus_tsum_majorant_translatedRationalPoints_le D θ hθ V n r X Y hXY c hc K' hK'
  obtain ⟨C₀, hC₀⟩ := hmaj N
  obtain ⟨C₂, hC₂, hmul'⟩ := hmul N
  set A : ℝ := max C₀ 0 * C₂ with hA
  have hA0 : 0 ≤ A := mul_nonneg (le_max_right _ _) hC₂
  refine ⟨A * C₁, mul_nonneg hA0 hC₁, ?_⟩
  intro t ht a ha y hy
  have hpt : ∀ ξ : Matrix (Fin V.rank) (Fin n) D.host.E,
      GlobalTheory.SiegelFormula.invPt V (a * y) ξ
        = (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) (GlobalTheory.SiegelFormula.invPt V a ξ) : Mx D V.rank n) := by
    intro ξ
    have h2 : Formalism.L2.Theta.mt V (a * y)⁻¹ = Formalism.L2.Theta.mt V y⁻¹ * Formalism.L2.Theta.mt V a⁻¹ := by
      rw [mul_inv_rev]; rfl
    simp only [GlobalTheory.SiegelFormula.invPt, h2, Matrix.mul_assoc]
  have hterm : ∀ ξ : Matrix (Fin V.rank) (Fin n) D.host.E,
      ‖Φ.1 (GlobalTheory.SiegelFormula.invPt V (a * y) ξ)‖ₑ
        ≤ ENNReal.ofReal A * ENNReal.ofReal (GlobalTheory.Unf.maj θ K' N (GlobalTheory.SiegelFormula.invPt V a ξ)) := by
    intro ξ
    rw [← ENNReal.ofReal_mul hA0, ← ofReal_norm_eq_enorm]
    apply ENNReal.ofReal_le_ofReal
    rw [hpt ξ]
    set x := GlobalTheory.SiegelFormula.invPt V a ξ
    have h1 := hC₀ (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n)
    have h2 := hmul' y hy x
    have hm0 := GlobalTheory.Unf.maj_nonneg θ K N (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n)
    calc ‖Φ.1 (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n)‖
        ≤ C₀ * GlobalTheory.Unf.maj θ K N (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) := h1
      _ ≤ max C₀ 0 * GlobalTheory.Unf.maj θ K N (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hm0
      _ ≤ max C₀ 0 * (C₂ * GlobalTheory.Unf.maj θ K' N x) :=
          mul_le_mul_of_nonneg_left h2 (le_max_right _ _)
      _ = A * GlobalTheory.Unf.maj θ K' N x := by rw [hA, mul_assoc]
  calc GlobalTheory.SiegelFormula.absTheta V Φ.1 (a * y)
      = ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, ‖Φ.1 (GlobalTheory.SiegelFormula.invPt V (a * y) ξ)‖ₑ := rfl
    _ ≤ ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E,
          ENNReal.ofReal A * ENNReal.ofReal (GlobalTheory.Unf.maj θ K' N (GlobalTheory.SiegelFormula.invPt V a ξ)) :=
        ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal A * ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E,
          ENNReal.ofReal (GlobalTheory.Unf.maj θ K' N (GlobalTheory.SiegelFormula.invPt V a ξ)) := ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal A * ENNReal.ofReal (C₁ * ∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n))) :=
        by gcongr; exact hframe t ht a ha
    _ = ENNReal.ofReal (A * C₁ * ∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n))) := by
        rw [← ENNReal.ofReal_mul hA0]; congr 1; ring

end GlobalTheory.TorusBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedExistenceStatement
section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adapted_existence : AdaptEx := by
  first | exact @GlobalTheory.BigOn.Exp.adaptEx | exact GlobalTheory.BigOn.Exp.adaptEx | (intros; apply GlobalTheory.BigOn.Exp.adaptEx <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BadShareSizeBoundsAlongFamilyStatement
section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.ShareOn Formalism.MainNotions.ArithmeticCylinders
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.badShareSize_bounds_along_family : Closed FamHyp fun Fm _ => ∃ x0 : ℝ, ∀ (x : ℝ), Fm.x1 < x → x0 ≤ x → ∀ (ι : Fm.Ix x), 100 ≤ (Fm.D x ι).R.r ∧ TieAdmG (Fm.D x ι) ∧ Real.exp (-((Fm.L x ι).sc.x ^ ((Fm.L x ι).sc.ez / 7))) ≤ 1 / 4 ∧ ∀ k : Fin 2, 2 ^ 12 ≤ (Fm.D x ι).host.g k ∧ 4 * (3 * ((Fm.D x ι).R.f : ℝ) / ((Fm.D x ι).host.g k : ℝ) + 23 * ((Fm.D x ι).R.f : ℝ) * Real.log ((Fm.D x ι).host.g k : ℝ) / Real.sqrt ((Fm.D x ι).host.g k : ℝ) + 2 * ((Fm.D x ι).R.f : ℝ) * ((Fm.D x ι).R.m : ℝ) * (1 / (4 * ((min (Fm.D x ι).host.q (Fm.D x ι).host.d : ℕ) : ℝ)) + (1 + Real.log ((Fm.D x ι).R.r : ℝ)) / (((Fm.D x ι).host.g k : ℝ) - 1)) + ((Fm.D x ι).R.r : ℝ) / 2 * (7 / 8 : ℝ) ^ (Fm.D x ι).R.f + Real.exp (-((Fm.D x ι).R.f : ℝ) / (5 * Real.log ((Fm.D x ι).R.r : ℝ)))) ≤ Real.exp (-((Fm.L x ι).sc.x ^ ((Fm.L x ι).sc.ez / 7))) := by
  first | exact @GlobalTheory.BadNumOnto.badShare_numbers_onto | exact GlobalTheory.BadNumOnto.badShare_numbers_onto | (intros; apply GlobalTheory.BadNumOnto.badShare_numbers_onto <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChange
section
set_option autoImplicit false

noncomputable section

open MvPolynomial
open Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD GlobalTheory.ExpFrame

namespace GlobalTheory.HighWt

variable (O : Type) [CommRing O] (N : ℕ) {ι : Type} [DecidableEq ι] (lam : ι → ℕ → ℕ)

def JointWt (Gm : Type) [AddCommGroup Gm] [Module (alg O N lam) Gm] (w : ι → Fin N → ℕ) : Prop :=
  ∃ z : Gm, z ≠ 0 ∧ ∀ τ (a : alg O N lam), IsProj O N lam τ (w τ) a → a • z = z

def pot {ι : Type} [Fintype ι] (w : ι → Fin N → ℕ) : ℕ := ∑ τ, ∑ a : Fin N, (N - (a : ℕ)) * w τ a

def extW {ι : Type} (w : ι → Fin N → ℕ) : ι → ℕ → ℕ := fun τ a => if h : a < N then w τ ⟨a, h⟩ else 0

def genSub (f : MvPolynomial (Fin N × Fin N) O) : MvPolynomial (Fin N × Fin N) (MvPolynomial (Fin N × Fin N) O) :=
  aeval (fun v : Fin N × Fin N => ∑ b : Fin N, X (v.1, b) * C (X (b, v.2))) f

def IsCoef (τ : ι) (m : Fin N × Fin N →₀ ℕ) (a : Module.End O (NablaT O N lam)) : Prop :=
  ∀ (x : ∀ τ, dualWeyl O N N (res N (lam τ))) (y : dualWeyl O N N (res N (lam τ))),
    (y : MvPolynomial (Fin N × Fin N) O) = (genSub O N (x τ : MvPolynomial (Fin N × Fin N) O)).coeff m →
    a (PiTensorProduct.tprod O x) = PiTensorProduct.tprod O (Function.update x τ y)

def CoefIn : Prop := ∀ (τ : ι) (m : Fin N × Fin N →₀ ℕ), ∃ a : alg O N lam, IsCoef O N lam τ m a

def BaseChange : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (N : ℕ) (ν : Fin N → ℕ), Antitone ν →
    (∀ f ∈ dualWeyl (O ⧸ Ideal.span {ϖ}) N N ν, ∃ g ∈ dualWeyl O N N ν, MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {ϖ})) g = f) ∧
    (∀ g ∈ dualWeyl O N N ν, MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {ϖ})) g = 0 → ∃ h ∈ dualWeyl O N N ν, g = ϖ • h)

theorem res_extW {ι : Type} (w : ι → Fin N → ℕ) (τ : ι) : res N (extW N w τ) = w τ := by
  funext a
  simp [res, extW, a.isLt]

end GlobalTheory.HighWt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomConstantOfBottomPairStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bottom_constant_of_bottom_pair : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
      NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW) (B B' WW₁ : HSp D)
      (Y : Tri T B B' WW₁) (c : T → ℂ), IsBottomTri W i j X → IsBottomTri W i j Y → Y.IsConst W.ψ W.θ c →
      ∃ u : T → D.what₂.LLˣ, X.IsConst W.ψ W.θ fun t => D.what₂.embLL (u t) * c t := by
  first | exact @GlobalTheory.BotTransfer.bottom_const_transfer | exact GlobalTheory.BotTransfer.bottom_const_transfer | (intros; apply GlobalTheory.BotTransfer.bottom_const_transfer <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalExistenceStatement
section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.canonical_existence : CanEx := by
  first | exact @GlobalTheory.BigOn.Exp.canEx_holds | exact GlobalTheory.BigOn.Exp.canEx_holds | (intros; apply GlobalTheory.BigOn.Exp.canEx_holds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalProjectionStatement
section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.canonical_projection : CanProj := by
  first | exact @GlobalTheory.BigOn.Exp.canProj | exact GlobalTheory.BigOn.Exp.canProj | (intros; apply GlobalTheory.BigOn.Exp.canProj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardIndependentBoundedSectionsShiftedWeightLeStatement
section
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_independent_boundedSections_shiftedWeight_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (m : ℕ) (f : Fin m → Frame X.Ψ r → ℂ), (∀ q, X.IsBddSec (Xa.Fp + (Xa.T + (nd X + 4)) • Xa.L) (f q)) → (∀ u : Fin m → ℂ, (∀ x ∈ X.dom, ∑ q, u q * f q x = 0) → u = 0) → m ≤ Fl.δ * (Xa.T + 3 * nd X + 10).choose (nd X) := by
  first | exact @GlobalTheory.UpperShift.upper_shift | exact GlobalTheory.UpperShift.upper_shift | (intros; apply GlobalTheory.UpperShift.upper_shift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartCharacterIsLogarithm
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CharLogOfChar

section Series

open MvPowerSeries ReciprocityTheory.PGsh GlobalTheory.FGDepth GlobalTheory.FormalCalc

variable {C : Type} [Field C]

theorem cc_pderiv {σ : Type} (i : σ) (f : MvPowerSeries σ C) :
    constantCoeff (pderiv C i f) = coeff (Finsupp.single i 1) f := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv]
  simp

theorem subst_zero_fun {σ τ : Type} [Finite σ] (f : MvPowerSeries σ C) :
    subst (fun _ : σ => (0 : MvPowerSeries τ C)) f = MvPowerSeries.C (constantCoeff f) := by
  classical
  have hs : HasSubst (fun _ : σ => (0 : MvPowerSeries τ C)) :=
    hasSubst_of_constantCoeff_zero fun _ => map_zero _
  ext e
  rw [coeff_subst hs, finsum_eq_single _ 0]
  · simp [coeff_C, coeff_one]
  · intro D hD
    obtain ⟨s, hs'⟩ := Finsupp.support_nonempty_iff.mpr hD
    rw [Finsupp.prod, Finset.prod_eq_zero hs' (zero_pow (Finsupp.mem_support_iff.mp hs'))]
    simp

theorem coeff_single_subst {σ τ : Type} [Fintype σ] {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) (f : MvPowerSeries σ C) (i : τ) :
    coeff (Finsupp.single i 1) (subst a f) =
      ∑ s, coeff (Finsupp.single s 1) f * coeff (Finsupp.single i 1) (a s) := by
  have hs : HasSubst a := hasSubst_of_constantCoeff_zero ha
  rw [← cc_pderiv, pderiv_subst hs, map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [map_mul, constantCoeff_subst_of_zero hs ha, cc_pderiv, cc_pderiv]
  rfl

variable {d : ℕ}

theorem pderiv_of_mul (g : MvPowerSeries (Fin d) C)
    (h : subst (fun a : Fin d => (X (Sum.inl a) + X (Sum.inr a) : MvPowerSeries (Fin d ⊕ Fin d) C)) g =
      subst (fun a : Fin d => (X (Sum.inl a) : MvPowerSeries (Fin d ⊕ Fin d) C)) g *
        subst (fun a : Fin d => (X (Sum.inr a) : MvPowerSeries (Fin d ⊕ Fin d) C)) g) (i : Fin d) :
    pderiv C i g = coeff (Finsupp.single i 1) g • g := by
  classical
  have hS : HasSubst (fun a : Fin d => (X (Sum.inl a) + X (Sum.inr a) : MvPowerSeries (Fin d ⊕ Fin d) C)) :=
    hasSubst_of_constantCoeff_zero fun _ => by simp
  have hL : HasSubst (fun a : Fin d => (X (Sum.inl a) : MvPowerSeries (Fin d ⊕ Fin d) C)) :=
    hasSubst_of_constantCoeff_zero fun _ => by simp
  have hR : HasSubst (fun a : Fin d => (X (Sum.inr a) : MvPowerSeries (Fin d ⊕ Fin d) C)) :=
    hasSubst_of_constantCoeff_zero fun _ => by simp
  let Z : Fin d ⊕ Fin d → MvPowerSeries (Fin d) C := Sum.elim X fun _ => 0
  have hZ : HasSubst Z := hasSubst_of_constantCoeff_zero fun s => by cases s <;> simp [Z]
  have hd := congrArg (fun f => subst Z (pderiv C (Sum.inr i) f)) h
  simp only [Derivation.leibniz, pderiv_subst hS, pderiv_subst hL, pderiv_subst hR, map_add, pderiv_X,
    Pi.single_apply, reduceCtorEq, if_false, Sum.inr.injEq, zero_add, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const_zero, smul_zero, add_zero,
    smul_eq_mul] at hd
  rw [subst_mul hZ, subst_comp_subst_apply hS hZ, subst_comp_subst_apply hL hZ,
    subst_comp_subst_apply hR hZ] at hd
  simp only [subst_add hZ, subst_X hZ, Z, Sum.elim_inl, Sum.elim_inr, add_zero] at hd
  rw [subst_zero_fun, cc_pderiv] at hd
  have e : (fun s : Fin d => (X s : MvPowerSeries (Fin d) C)) = X := rfl
  rw [e, subst_self] at hd
  rw [show pderiv C i g = id (pderiv C i g) from rfl, hd, id, mul_comm, smul_eq_C_mul]

variable [CharZero C]

open Formalism.L2.Th1.C in

theorem coeff_of_pderiv (g : MvPowerSeries (Fin d) C) (c : Fin d → C) (h0 : constantCoeff g = 1)
    (h : ∀ i, pderiv C i g = c i • g) (α : Fin d →₀ ℕ) :
    coeff α g = α.prod fun e n => c e ^ n / (n.factorial : C) := by
  classical
  rw [← CharBound.coeff_mvExp_lin]
  set L : MvPowerSeries (Fin d) C := ∑ s, c s • (X s : MvPowerSeries (Fin d) C) with hLdef
  have hL : constantCoeff L = 0 := by simp [hLdef]
  have hnL : constantCoeff (-L) = 0 := by rw [map_neg, hL, neg_zero]
  have hpL : ∀ i, pderiv C i L = c i • (1 : MvPowerSeries (Fin d) C) := fun i => by
    simp [hLdef, pderiv_X, Pi.single_apply]
  have key : g * mvExp (-L) = 1 := by
    refine pderiv.ext (fun i => ?_) ?_
    · rw [Derivation.leibniz, pderiv_mvExp hnL, map_neg, hpL, h, pderiv_one]
      simp only [smul_eq_mul, Algebra.smul_def]
      ring
    · rw [map_mul, h0, constantCoeff_mvExp hnL, map_one, mul_one]
  have hE : mvExp L = g := by
    calc mvExp L = (g * mvExp (-L)) * mvExp L := by rw [key, one_mul]
      _ = g := by rw [mul_assoc, mvExp_neg hL, mul_one]
  rw [hE]

variable {v : AddValuation C (WithTop ℝ)}

theorem coeff_single_expOf (G : LogFGL v d) (a i : Fin d) :
    coeff (Finsupp.single i 1) (expOf G a) = if a = i then 1 else 0 := by
  classical
  have h := congrArg (coeff (Finsupp.single i 1)) ((expOf_twoSided_unique C v d G).2.1 a)
  rw [coeff_single_subst G.lg_const] at h
  simp only [G.lg_lin, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  rw [h, ← cc_pderiv, pderiv_X, Pi.single_apply]
  split_ifs <;> simp

theorem mul_of_char (G : LogFGL v d) (χ : MvPowerSeries (Fin d) C)
    (h : subst G.F χ = subst (fun a : Fin d => (X (Sum.inl a) : MvPowerSeries (Fin d ⊕ Fin d) C)) χ *
        subst (fun a : Fin d => (X (Sum.inr a) : MvPowerSeries (Fin d ⊕ Fin d) C)) χ) :
    subst (fun a : Fin d => (X (Sum.inl a) + X (Sum.inr a) : MvPowerSeries (Fin d ⊕ Fin d) C))
        (subst (expOf G) χ) =
      subst (fun a : Fin d => (X (Sum.inl a) : MvPowerSeries (Fin d ⊕ Fin d) C)) (subst (expOf G) χ) *
        subst (fun a : Fin d => (X (Sum.inr a) : MvPowerSeries (Fin d ⊕ Fin d) C)) (subst (expOf G) χ) := by
  obtain ⟨⟨hE0, hE1⟩, hE2, -⟩ := expOf_twoSided_unique C v d G
  have hE : HasSubst (expOf G) := hasSubst_of_constantCoeff_zero hE0
  have hS : HasSubst (fun a : Fin d => (X (Sum.inl a) + X (Sum.inr a) : MvPowerSeries (Fin d ⊕ Fin d) C)) :=
    hasSubst_of_constantCoeff_zero fun _ => by simp
  have hL : HasSubst (fun a : Fin d => (X (Sum.inl a) : MvPowerSeries (Fin d ⊕ Fin d) C)) :=
    hasSubst_of_constantCoeff_zero fun _ => by simp
  have hR : HasSubst (fun a : Fin d => (X (Sum.inr a) : MvPowerSeries (Fin d ⊕ Fin d) C)) :=
    hasSubst_of_constantCoeff_zero fun _ => by simp
  have hF : HasSubst G.F := hasSubst_of_constantCoeff_zero G.F_const
  have hlg : HasSubst G.lg := hasSubst_of_constantCoeff_zero G.lg_const
  let P : Fin d ⊕ Fin d → MvPowerSeries (Fin d ⊕ Fin d) C :=
    Sum.elim (fun b => subst (fun a : Fin d => (X (Sum.inl a) : MvPowerSeries (Fin d ⊕ Fin d) C)) (expOf G b))
      (fun b => subst (fun a : Fin d => (X (Sum.inr a) : MvPowerSeries (Fin d ⊕ Fin d) C)) (expOf G b))
  have hP0 : ∀ s, constantCoeff (P s) = 0 := fun s => by
    cases s with
    | inl b => exact constantCoeff_subst_eq_zero hL (fun _ => by simp) (hE0 b)
    | inr b => exact constantCoeff_subst_eq_zero hR (fun _ => by simp) (hE0 b)
  have hP : HasSubst P := hasSubst_of_constantCoeff_zero hP0
  have eL : ∀ f : MvPowerSeries (Fin d) C,
      subst P (subst (fun a : Fin d => (X (Sum.inl a) : MvPowerSeries (Fin d ⊕ Fin d) C)) f) =
        subst (fun a : Fin d => (X (Sum.inl a) : MvPowerSeries (Fin d ⊕ Fin d) C)) (subst (expOf G) f) := by
    intro f
    rw [subst_comp_subst_apply hL hP, subst_comp_subst_apply hE hL]
    simp only [subst_X hP, P, Sum.elim_inl]
  have eR : ∀ f : MvPowerSeries (Fin d) C,
      subst P (subst (fun a : Fin d => (X (Sum.inr a) : MvPowerSeries (Fin d ⊕ Fin d) C)) f) =
        subst (fun a : Fin d => (X (Sum.inr a) : MvPowerSeries (Fin d ⊕ Fin d) C)) (subst (expOf G) f) := by
    intro f
    rw [subst_comp_subst_apply hR hP, subst_comp_subst_apply hE hR]
    simp only [subst_X hP, P, Sum.elim_inr]
  have hQ : HasSubst (fun a => (subst P (G.F a) : MvPowerSeries (Fin d ⊕ Fin d) C)) :=
    hasSubst_of_constantCoeff_zero fun a => constantCoeff_subst_eq_zero hP hP0 (G.F_const a)
  have e1 : (fun a : Fin d => (X (Sum.inl a) + X (Sum.inr a) : MvPowerSeries (Fin d ⊕ Fin d) C)) =
      fun a => subst (fun b => (subst P (G.F b) : MvPowerSeries (Fin d ⊕ Fin d) C)) (G.lg a) := by
    funext a
    rw [← subst_comp_subst_apply hF hP, G.lg_F, subst_add hP, eL, eR, hE1, subst_X hL, subst_X hR]
  have e2 : (fun b => (subst (fun a : Fin d => (X (Sum.inl a) + X (Sum.inr a) :
      MvPowerSeries (Fin d ⊕ Fin d) C)) (expOf G b) : MvPowerSeries (Fin d ⊕ Fin d) C)) =
      fun b => subst P (G.F b) := by
    funext b
    rw [e1, ← subst_comp_subst_apply hlg hQ, hE2, subst_X hQ]
  rw [subst_comp_subst_apply hE hS, e2, ← subst_comp_subst_apply hF hP, h, subst_mul hP, eL, eR]

theorem isCharLog_of_char (G : LogFGL v d) (χ : MvPowerSeries (Fin d) C) (hi : MvIsInt v χ)
    (h0 : constantCoeff χ = 1)
    (h : subst G.F χ = subst (fun a : Fin d => (X (Sum.inl a) : MvPowerSeries (Fin d ⊕ Fin d) C)) χ *
        subst (fun a : Fin d => (X (Sum.inr a) : MvPowerSeries (Fin d ⊕ Fin d) C)) χ) :
    IsCharLog G fun j => coeff (Finsupp.single j 1) χ := by
  classical
  have hE0 := (expOf_twoSided_unique C v d G).1.1
  have hE : HasSubst (expOf G) := hasSubst_of_constantCoeff_zero hE0
  refine ⟨χ, hi, coeff_of_pderiv _ _ ?_ fun i => ?_⟩
  · rw [constantCoeff_subst_of_zero hE hE0, h0, map_one]
  · rw [pderiv_of_mul _ (mul_of_char G χ h), coeff_single_subst hE0]
    simp [coeff_single_expOf]

end Series

open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)

theorem isCharLog_dl : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p), ∀ χ : PS X.O 1 (chD Ch.ch), ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.IsCh (fun i => MvPowerSeries.map X.ι (Ch.FT i)) χ → IsCharLog (fgl Ch X) (fun j => algebraMap X.O X.C (ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.dl χ j)) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro p _ T io y Ch X χ hχ
  obtain ⟨h0, hm⟩ := hχ
  set φ := algebraMap X.O X.C with hφ
  have hj : φ.comp X.ι = jX X := RingHom.ext fun r => (X.comp r).symm
  have hFe : ∀ i, MvPowerSeries.map φ (MvPowerSeries.map X.ι (Ch.FT i)) = (lawX Ch X).F i := fun i => by
    rw [lawX_F, ← hj, MvPowerSeries.map_comp]; rfl
  have hinj : Function.Injective φ := X.ints.hom_inj
  have hF0 : ∀ i, MvPowerSeries.constantCoeff (MvPowerSeries.map X.ι (Ch.FT i)) = 0 := fun i => hinj (by
    have h := (lawX Ch X).const i
    rw [← hFe, MvPowerSeries.constantCoeff_map] at h
    rw [h, map_zero])
  have hadd : addOf (fun i => MvPowerSeries.map X.ι (Ch.FT i)) (pt X.O (n := 2) _ 0) (pt X.O (n := 2) _ 1) =
      fun i => MvPowerSeries.map X.ι (Ch.FT i) := by
    funext i
    have e : (fun q : Fin 2 × Fin (chD Ch.ch) =>
        (![pt X.O (n := 2) _ 0, pt X.O _ 1] : Fin 2 → Pt X.O 2 _) q.1 q.2) = MvPowerSeries.X := by
      funext q
      obtain ⟨j, i⟩ := q
      fin_cases j <;> rfl
    unfold addOf ev
    rw [e, MvPowerSeries.subst_self]
    rfl
  have hmap : ∀ a : Pt X.O 2 (chD Ch.ch), (∀ i, MvPowerSeries.constantCoeff (a i) = 0) →
      MvPowerSeries.map φ (ev ![a] χ) = ev ![fun i => MvPowerSeries.map φ (a i)] (MvPowerSeries.map φ χ) := by
    intro a ha
    unfold ev
    rw [MvPowerSeries.map_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => by
      obtain ⟨j, i⟩ := q
      fin_cases j; exact ha i)]
    congr 1
    funext q
    obtain ⟨j, i⟩ := q
    fin_cases j; rfl
  have hp : ∀ (k : Type) [CommRing k] (j : Fin 2) i,
      MvPowerSeries.constantCoeff (pt k (n := 2) (chD Ch.ch) j i) = 0 := fun k _ j i => by simp [pt]
  have hpm : ∀ j : Fin 2, (fun i => MvPowerSeries.map φ (pt X.O (n := 2) (chD Ch.ch) j i)) = pt X.C _ j :=
    fun j => funext fun i => by simp [pt]
  have hm' := congrArg (MvPowerSeries.map φ) hm
  rw [hadd, map_mul, hmap _ hF0, hmap _ (hp _ 0), hmap _ (hp _ 1), hpm, hpm, funext hFe] at hm'
  have key := isCharLog_of_char (fgl Ch X)
    (MvPowerSeries.subst (GlobalTheory.LawLog.oneVar X.C _) (MvPowerSeries.map φ χ)) ?_ ?_ ?_
  · simp only [GlobalTheory.LawLog.coeff_single_oneVar, MvPowerSeries.coeff_map] at key
    exact key
  · refine CharBound.mvIsInt_subst' GlobalTheory.LawLog.hs_oneVar (fun q => CharBound.mvIsInt_X' _) fun α => ?_
    rw [MvPowerSeries.coeff_map, isIntV_iff]
    exact X.ints.map_le_one _
  · rw [GlobalTheory.FormalCalc.constantCoeff_subst_of_zero GlobalTheory.LawLog.hs_oneVar GlobalTheory.LawLog.cc_oneVar]
    simp [h0]
  · have e0 : (fun b => (MvPowerSeries.X (Sum.inl b) : MvPowerSeries (Fin (chD Ch.ch) ⊕ Fin (chD Ch.ch)) X.C)) =
        fun i => MvPowerSeries.subst (GlobalTheory.LawLog.twoVars X.C _) (pt X.C (n := 2) _ 0 i) := by
      funext i; rw [pt, MvPowerSeries.subst_X GlobalTheory.LawLog.hs_twoVars]; simp [GlobalTheory.LawLog.twoVars]
    have e1 : (fun b => (MvPowerSeries.X (Sum.inr b) : MvPowerSeries (Fin (chD Ch.ch) ⊕ Fin (chD Ch.ch)) X.C)) =
        fun i => MvPowerSeries.subst (GlobalTheory.LawLog.twoVars X.C _) (pt X.C (n := 2) _ 1 i) := by
      funext i; rw [pt, MvPowerSeries.subst_X GlobalTheory.LawLog.hs_twoVars]; simp [GlobalTheory.LawLog.twoVars]
    have eF : (fgl Ch X).F = fun i => MvPowerSeries.subst (GlobalTheory.LawLog.twoVars X.C _) ((lawX Ch X).F i) := rfl
    rw [e0, e1, eF, GlobalTheory.LawLog.subst_oneVar _ GlobalTheory.LawLog.cc_twoVars _ (lawX Ch X).const,
      GlobalTheory.LawLog.subst_oneVar _ GlobalTheory.LawLog.cc_twoVars _ (hp _ 0),
      GlobalTheory.LawLog.subst_oneVar _ GlobalTheory.LawLog.cc_twoVars _ (hp _ 1), ← MvPowerSeries.subst_mul GlobalTheory.LawLog.hs_twoVars, hm']

end GlobalTheory.CharLogOfChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefLatticeIndepCoefMapProof
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.OnTies
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.CoefIndepProof

theorem coefIndep : GlobalTheory.BaseCmp.CoefIndep := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i c0L hc h w hw
  obtain ⟨gramR', c0R', c0L', hT', P, hP, rfl⟩ := hw
  obtain ⟨gramR, c0R, hT⟩ := hc
  obtain ⟨c, ⟨γ, k, e⟩, -⟩ := (R.B.L i A.μ0).pres.reps (fin (Vc D i) h)
  have hst : Formalism.UG.bc (swapAE D) ((k : Bridge.Gf (Vc D i)) : GL (Fin (Vc D i).rank) _) ∈ St (R.βV i) :=
    Formalism.L2.DIV.parLev_St k.2.1
  obtain ⟨γE, hγ, hl⟩ := GlobalTheory.HLatMove.hLat_rat_mul_stab (Vc D i) (R.βV i) (R.ΛV i) (hR.lev.βV i) γ
  rw [e, hl _ _ hst, Formalism.L2.Col.nabAtr_gmap, MulEquiv.apply_symm_apply] at hP ⊢
  obtain ⟨P', hP', rfl⟩ := hP
  obtain ⟨e', -, h2', -, h4', -⟩ := hT'.coefL i A.μ0
  obtain ⟨e1, -, h2, -, h4, -⟩ := hT.coefL i A.μ0
  rw [← h4' c] at hP'
  obtain ⟨y, hy, rfl⟩ := hP'
  refine ⟨rhoVr (labLL D) (lamV D i) γE (e1 y), ⟨e1 y, ?_, rfl⟩, ?_⟩
  · rw [← h4 c]; exact ⟨y, hy, rfl⟩
  · have a1 := (hT'.mapL i).1 γ γE hγ (e' y)
    have a2 := (hT.mapL i).1 γ γE hγ (e1 y)
    change c0L' i (rhoVr (labLL D) (lamV D i) γE (e' y)) = c0L i (rhoVr (labLL D) (lamV D i) γE (e1 y))
    rw [a1, ← h2', h2]
    exact a2.symm

end GlobalTheory.CoefIndepProof
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineLatticeLinkOfBlockDataStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystallineLatticeLink_of_blockData : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ¬ (l : ℤ) ∣ NumberField.discr E → ∀ (ι : Type) (inc : ι → (E →+* PadicAlgCl l)), IsHalf inc → ∃ (fr : ℕ → ι → ι) (cjj : ℕ → ι → Bool), ∀ (P : Par) (W : Wts ι), P.Hyp → W.Ok P → (∀ τ a, a < P.Nr → 0 ≤ W.U P τ a ∧ W.U P τ a ≤ (h0 P : ℤ)) → ∀ mu : ι → ℕ → ℕ, Linked l P.Nr W.lam mu → BlockFor Ω inc P W mu → ∀ τ, LatticeLink P (reFr W fr cjj) l τ (res P.Nr (mu τ)) := by
  first | exact @GlobalTheory.ExpLink.latticeLink_of_blockFor | exact GlobalTheory.ExpLink.latticeLink_of_blockFor | (intros; apply GlobalTheory.ExpLink.latticeLink_of_blockFor <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventualPointsOfRowTiesStatement
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Fc GlobalTheory.Fc.Ind GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventual_points_of_row_ties : ∀ (prem : ∀ {eps : ℝ}, FamP eps → Prop) (G : PtP) (T : ℝ → ℝ → PtP), (Closed FamHyp fun Fm CH => prem Fm → ∃ C0 : ℝ, 0 ≤ C0 ∧ EvPt Fm fun x hx i p => G _ (objAt Fm x hx i) _ p → ∀ C, C0 ≤ C → T C CH _ (objAt Fm x hx i) _ p) → ∀ (𝒜 : FamClass) (σ : RawSel Part 𝒜), (∀ (eps : ℝ) (Fm : FamP eps), 𝒜 Fm → GlobalTheory.EX.DQ.Duty7 Fm) → EvW PRows 𝒜 σ → EvW (onPt G) 𝒜 σ → EvWC prem (fun C CH => onPt (T C CH)) 𝒜 σ := by
  first | exact @GlobalTheory.Fc.Ind.evWC_onPt_of_guarded | exact GlobalTheory.Fc.Ind.evWC_onPt_of_guarded | (intros; apply GlobalTheory.Fc.Ind.evWC_onPt_of_guarded <;> assumption)
end

