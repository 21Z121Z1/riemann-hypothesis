import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0320
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharacteristicFunctionIntegralApply
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoOneOfSummable
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftGoodProjectorIntertwinesMatchedHecke
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0311
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceDoubleCosetOperatorsCommuteSpherical
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0374
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0122
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0102
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0316
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0019
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0104
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0008
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Formalism.SharpRestriction.Bundle0001
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0246
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0321
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.Bundle0010
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0150
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0484
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0167
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0149
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0158
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0065
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.Bundle0003
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0089
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0095
import Formalism.LocalToGlobal.Divisibility.DivisibilityProofs.NumbersP
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0025
import Formalism.LocalToGlobal.Columns.XtPhiTopGCongr
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TwistEmptyOfChartsEx
import Formalism.LocalToGlobal.GlobalTheory.GL6.Bundle0007
import Formalism.LocalToGlobal.LatticeGeometry.GeometryDefinitions.PNeatB
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0187
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsSpan
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0314
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0318
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0136
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0134
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0124
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0040
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0057
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0215
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0317
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0191
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0244
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0243
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0254
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0227
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0212

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ModerateGrowthDefiniteThetaIntegralVectorFormStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct ComplexOrder
open MeasureTheory Formalism.IndefR.Datum Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.moderateGrowth_definiteThetaIntegral_vectorForm : ∀ {D : D7} (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ℂ) (V W : Formalism.BasicNotions.TH.HSp D)
    (χS χT : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)),
    IsWeilDatumO ψ V W χS χT om → (∀ τ, (gramAt D V τ).PosDef) →
    ∀ (ν : Measure (GA D V)) (𝓕 : Set (GA D V)), ν.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 ν →
    ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [FiniteDimensional ℂ X] (L : X →ₗ[ℂ] (WO V W → ℂ)),
    (∀ x, IsThetaFunO ψ V W (L x)) → ∀ u : GA D V → X, Continuous u → (∀ γ ∈ GQ V, ∀ h, u (γ * h) = u h) →
    GlobalTheory.Grow.ModGrowth W (fun g => ∫ h in 𝓕, thetaKO om h g (L (u h)) ∂ν) := by
  first | exact @GlobalTheory.ThetaLiftGrowth.modGrowth_thetaIntegral | exact GlobalTheory.ThetaLiftGrowth.modGrowth_thetaIntegral | (intros; apply GlobalTheory.ThetaLiftGrowth.modGrowth_thetaIntegral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MultiplicitySpaceAllLevelsValuesSmoothCuspidalStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct ComplexOrder
open Formalism.IndefR Formalism.IndefR.Mult Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplicitySpaceAllLevels_values_smooth_cuspidal : ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {V : Formalism.BasicNotions.TH.HSp D}
    {S : D.what₂.Tau → Formalism.BasicNotions.TH.SPar} {n : ℕ} (P : principalLevelFrame.RowPsi V n) (M : DSModel V S),
    ∀ T ∈ principalLevelFrame.Minf θ P M, ∀ v : M.Vec, IsAutFunSm θ V (T v) ∧ IsCuspFun V (T v) := by
  first | exact @GlobalTheory.MinfCusp.minf_val_autCusp | exact GlobalTheory.MinfCusp.minf_val_autCusp | (intros; apply GlobalTheory.MinfCusp.minf_val_autCusp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormaliserGLintEqScalarMulGLintStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normaliser_GLint_conj_eq_two_sided_GLint_mul : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n : ℕ)
    (N : GL (Fin n) (v.adicCompletion F)),
    (∀ g ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v), ∀ z : Fin n → v.adicCompletion F, (∀ i, z i ∈ Formalism.UG.Ov F v) →
      ∃ z' : Fin n → v.adicCompletion F, (∀ i, z' i ∈ Formalism.UG.Ov F v) ∧
        (g : Matrix (Fin n) (Fin n) (v.adicCompletion F)).mulVec
            ((N : Matrix (Fin n) (Fin n) (v.adicCompletion F)).mulVec z) =
          (N : Matrix (Fin n) (Fin n) (v.adicCompletion F)).mulVec z') →
    ∀ X : Matrix (Fin n) (Fin n) (v.adicCompletion F), ∃ k₁ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v),
      ∃ k₂ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v),
        ((N⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * X *
            (N : Matrix (Fin n) (Fin n) (v.adicCompletion F)) =
          (k₁ : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * X * (k₂ : Matrix (Fin n) (Fin n) (v.adicCompletion F)) := by
  first | exact @GlobalTheory.NormaliserGLint.conj_eq_glint_mul_mul | exact GlobalTheory.NormaliserGLint.conj_eq_glint_mul_mul | (intros; apply GlobalTheory.NormaliserGLint.conj_eq_glint_mul_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PeriodRelationsTrueColumnsAtTuple
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.AtG

open Formalism.L2.Col GlobalTheory.ColPeriodCompare
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound GlobalTheory.Mem GlobalTheory.Mem.Col2
namespace GlobalTheory.TiesTrue

def baseCast {D : D7} {cc cc' : Ideal (𝓞 D.host.K)} (e : cc = cc') {δ : ℂ} (Bs : Formalism.L2.Ker.Base D cc δ) :
    Formalism.L2.Ker.Base D cc' δ := e ▸ Bs

theorem ambOf_baseCast {D : D7} {X : Fields} (s : Seam D X) {cc cc' : Ideal (𝓞 D.host.K)} (e : cc = cc') {δ : ℂ}
    (Bs : Formalism.L2.Ker.Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) :
    ambOf s (baseCast e Bs) χ cD = ambOf s Bs χ cD := by
  subst e; rfl

def exOf {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : GlobalTheory.Mem.Col2.TC B X} {l : I.Laws}
    {Z : GlobalTheory.Mem.Col2.TC.Later B (I.cols l)} (EX : ErrX (I.rec7 l Z)) (h1 : EX.piG = X.piG) (h2 : EX.piT = X.piT) :
    ErrX (I.rec7 l Z) :=
  ⟨X.piG, h1 ▸ EX.piG_K, h1 ▸ EX.piG_norm, X.piT, h2 ▸ EX.piT_K, h2 ▸ EX.piT_norm, h2 ▸ EX.piT_cong, EX.vPl, EX.vPl_inj,
    EX.norm_mem_place_ideal⟩

theorem exOf_eq {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : GlobalTheory.Mem.Col2.TC B X} {l : I.Laws}
    {Z : GlobalTheory.Mem.Col2.TC.Later B (I.cols l)} (EX : ErrX (I.rec7 l Z)) (h1 : EX.piG = X.piG) (h2 : EX.piT = X.piT) :
    exOf EX h1 h2 = EX := by
  obtain ⟨piG, _, _, piT, _, _, _, _, _, _⟩ := EX
  obtain rfl : piG = X.piG := h1
  obtain rfl : piT = X.piT := h2
  rfl

theorem badS_subset {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : GlobalTheory.Mem.Col2.TC B X} (h : I.Ok) (l : I.Laws)
    (Z : GlobalTheory.Mem.Col2.TC.Later B (I.cols l)) : badS (I.rec7 l Z) ⊆ I.S := by
  rintro p (hp | ⟨u, rfl⟩ | hp)
  · rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact h.two_q_d_mem.1
    · exact h.two_q_d_mem.2.1
    · exact h.two_q_d_mem.2.2
    · exact h.g_mem 0
    · exact h.g_mem 1
  · exact h.T_mem u
  · exact h.small_mem (Finset.mem_coe.1 hp)

theorem mem_tupGrp_of_subset {F E L : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [Field L]
    {S S' : Set ℕ} (hS : S' ⊆ S) {x : Chr F E L} (hx : x ∈ tupGrp F E L S) : x ∈ tupGrp F E L S' := by
  obtain ⟨h1, h4⟩ := Subgroup.mem_inf.1 hx
  refine Subgroup.mem_inf.2 ⟨h1, Subgroup.mem_iInf.2 fun v => Subgroup.mem_iInf.2 fun hv => ?_⟩
  exact Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 h4 v) fun hg => hv ⟨hg.1, hg.2.1, fun hm => hg.2.2 (hS hm)⟩

section Gen

variable {D : D7} {EX : ErrX D} (Ch : Chars (recFields D) (recPrimes EX) D.R.m)
  (sel : HeightOneSpectrum (𝓞 D.host.F) → HeightOneSpectrum (𝓞 D.host.E))

def TwistTieS {S : Set ℕ} (Dx : DivX D) (μ : D.what₂.Tup) (ξ : Tup (recFields D).F (recFields D).E (recFields D).K S) : Prop :=
  ((Dx.Qp μ : Set ℕ) = QprimeN (ξ : Chr (recFields D).F (recFields D).E (recFields D).K)) ∧
    (μ = D.what₂.mu0 → (ξ : Chr (recFields D).F (recFields D).E (recFields D).K) = 1)

def FieldTieS (A : Amb (recFields D)) {S : Set ℕ} (ξ : Tup (recFields D).F (recFields D).E (recFields D).K S)
    (cst : LocCst (recFields D) (rowSG (recPrimes EX) sel ξ)) (u : D.what₂.Word) : Prop :=
  ∀ i < D.R.m, JetsRatDeg A (D.R.N i) (D.R.N (i + 1)) (Sall (Pr := recPrimes EX) sel ξ u)
    (cAof sel ξ cst * cBof sel ξ cst u) (fun τ => ∑ a, ((recWts EX).nuW u (i + 1) τ).w a)

def RowTieS (μ : D.what₂.Tup) {S : Set ℕ} (ξ : Tup (recFields D).F (recFields D).E (recFields D).K S)
    (jA : MtildeV (recWts EX) Ch sel ξ (rPsymF Ch) →ₛₗ[D.what₂.embLL] D.what₂.Amb μ) : Prop :=
  (∀ s : Finset (MtildeV (recWts EX) Ch sel ξ (rPsymF Ch)),
      LinearIndependent D.what₂.LL (fun x : s => (x : MtildeV (recWts EX) Ch sel ξ (rPsymF Ch))) →
      LinearIndependent ℂ (fun x : s => jA x)) ∧
    Submodule.span ℂ (Set.range jA) = ⊤ ∧
    (∀ v ∈ (D.what₂.Mtilde μ).gen, v ∈ Set.range jA) ∧
    ∀ x, x ∈ MtildeL (recWts EX) Ch sel ξ (rPsymF Ch) ↔ ∃ c : D.what₂.Amb μ → 𝓞 D.what₂.LL,
      jA x = ∑ v ∈ (D.what₂.Mtilde μ).gen, D.what₂.embLL ((c v : 𝓞 D.what₂.LL) : D.what₂.LL) • v

def PerTieS (u : D.what₂.Word) (μ : D.what₂.Tup) {S : Set ℕ} (ξ : Tup (recFields D).F (recFields D).E (recFields D).K S)
    (hP : (mtildeGSD (recWts EX) Ch sel ξ (rPsymF Ch)).Ok)
    (col : MfV (recWts EX) Ch u →ₗ[D.what₂.LL] (evGSD (recWts EX) Ch sel ξ (rPsymF Ch) u).EqFun)
    (eM : (D.div.Nu u).V ≃ₗ[D.what₂.LL] MramV (recWts EX) Ch u)
    (jA : MtildeV (recWts EX) Ch sel ξ (rPsymF Ch) →ₛₗ[D.what₂.embLL] D.what₂.Amb μ) : Prop :=
  ∀ φ x, D.what₂.perCol u μ (D.jN u φ) (jA x) =
    D.what₂.embLL (PtilE (recWts EX) Ch sel ξ (rPsymF Ch) hP u (col (eM φ : MfV (recWts EX) Ch u)) x)

def ChainTieS (Dx : DivX D) (mu0 : Fin D.R.m → Formalism.L2.Host.HChar D.host.E) (A : Amb (recFields D))
    (u : D.what₂.Word) (μ : D.what₂.Tup) {S : Set ℕ} (ξ : Tup (recFields D).F (recFields D).E (recFields D).K S) : Prop :=
  ∃ (cst : LocCst (recFields D) (rowSG (recPrimes EX) sel ξ))
    (I : ChIdx (recFields D) (recPrimes EX) D.R (QE sel (ξ : Chr (recFields D).F (recFields D).E (recFields D).K)))
    (hI : I.Ok Ch sel ξ cst (recGlob D mu0) (D.R.m - 2))
    (b : I.β (D.R.m - 2 + 1)) (hY : YbHyp (R := D.R) sel ξ cst I u (D.R.m - 2) b)
    (hK : KerEquivC (recWts EX) Ch sel ξ cst I A u (D.R.m - 2) b hY (rPsymF Ch))
    (hF : ∀ j, (chF (recWts EX) sel ξ I u j).Ok)
    (hP : (mtildeGSD (recWts EX) Ch sel ξ (rPsymF Ch)).Ok)
    (eM : (D.div.Nu u).V ≃ₗ[D.what₂.LL] MramV (recWts EX) Ch u)
    (jA : MtildeV (recWts EX) Ch sel ξ (rPsymF Ch) →ₛₗ[D.what₂.embLL] D.what₂.Amb μ),
    cst.sharp = true ∧ TwistTieS Dx μ ξ ∧ FieldTieS sel A ξ cst u ∧ ColTie Ch u eM ∧ RowTieS Ch sel μ ξ jA ∧
      PerTieS Ch sel u μ ξ hP (colMu (recWts EX) Ch sel ξ cst I A u (D.R.m - 2) b hY (rPsymF Ch) hK hF hI) eM jA

theorem chainPeriodRelation_read_for_character_avoiding_primes (Dx : DivX D) (mu0 : Fin D.R.m → Formalism.L2.Host.HChar D.host.E) (A : Amb (recFields D))
    (u : D.what₂.Word) (μ : D.what₂.Tup) {S : Set ℕ} (χ : Chr (recFields D).F (recFields D).E (recFields D).K)
    (h : IsTwist (recFields D).F (recFields D).E (recFields D).K S χ)
    (h' : IsTwist (recFields D).F (recFields D).E (recFields D).K (badS D) χ)
    (H : ChainTieS Ch sel Dx mu0 A u μ (@Subtype.mk _ (IsTwist _ _ _ S) χ h)) : ChainTie Ch sel Dx mu0 A u μ := by
  obtain ⟨cst, I, hI, b, hY, hK, hF, hP, eM, jA, h1, h2, h3, h4, h5, h6⟩ := H
  exact ⟨@Subtype.mk _ (IsTwist _ _ _ (badS D)) χ h', cst, I, { hI with }, b, ⟨hY.fin⟩, hK, hF, hP, eM, jA, h1,
    ⟨h2.1, fun e => Subtype.ext (h2.2 e)⟩, h3, h4, h5, h6⟩

theorem chainTie_of (Dx : DivX D) (mu0 : Fin D.R.m → Formalism.L2.Host.HChar D.host.E) (A : Amb (recFields D))
    (u : D.what₂.Word) (μ : D.what₂.Tup) {S : Set ℕ} (ξ : Tup (recFields D).F (recFields D).E (recFields D).K S)
    (hξ : (ξ : Chr (recFields D).F (recFields D).E (recFields D).K) ∈
      tupGrp (recFields D).F (recFields D).E (recFields D).K (badS D))
    (H : ChainTieS Ch sel Dx mu0 A u μ ξ) : ChainTie Ch sel Dx mu0 A u μ := by
  obtain ⟨χ, h⟩ := ξ
  exact chainPeriodRelation_read_for_character_avoiding_primes Ch sel Dx mu0 A u μ χ h hξ H

end Gen

theorem colTie_of_addEquiv {D : D7} {EX : ErrX D} (Ch : Chars (recFields D) (recPrimes EX) D.R.m) (u : D.what₂.Word)
    (eM : (D.div.Nu u).V ≃+ MramV (recWts EX) Ch u) (hs : ∀ (r : D.what₂.LL) x, eM (r • x) = r • eM x)
    (h : ∀ x, x ∈ DV.MramL D u ↔ eM x ∈ MramL (recWts EX) Ch u) : ColTie Ch u (eM.toLinearEquiv hs) := h

theorem span_range_comp_eq_top {K V W U : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup U] [Module ℂ U] {σ : K →+* ℂ} (f : V →ₛₗ[σ] W) (e : W ≃ₗ[ℂ] U)
    (h : Submodule.span ℂ (Set.range f) = ⊤) : Submodule.span ℂ (Set.range (e.toLinearMap.comp f)) = ⊤ := by
  rw [LinearMap.coe_comp, Set.range_comp, Submodule.span_image, h, Submodule.map_top, LinearEquiv.range]

theorem perCol_eq {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} (I : GlobalTheory.Mem.Col2.TC B X) (h : I.Ok) (l : I.Laws)
    (Z : GlobalTheory.Mem.Col2.TC.Later B (I.cols l)) (u : B.Word) (a : (I.rec7 l Z).what₂.Tup)
    (eM : ((I.rec7 l Z).div.Nu u).V ≃+ MramV (Pr := B.primes X) B.wts I.Ch u)
    (heM3 : ∀ x, (I.rec7 l Z).nuIn u x = KerRat.colForm I l h u I.mu0 (eM x).1)
    (heM4 : ∀ a φ, (I.fm l u a).emb 0 (KerRat.colForm I l h u a φ) =
      (I.cols l).e0Tw u a ((I.fm l u I.mu0).emb 0 (KerRat.colForm I l h u I.mu0 φ)))
    (e : (I.per l u a).Mt ≃ₗ[ℂ] (I.rec7 l Z).what₂.Amb a)
    (he1 : a = (I.rec7 l Z).what₂.mu0 → HEq e ((I.rec7 l Z).eMt u))
    (he2 : a ≠ (I.rec7 l Z).what₂.mu0 → e = (I.rec7 l Z).eMtTw u a) (φ : ((I.rec7 l Z).div.Nu u).V)
    (z : MtildeV (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) I.Ps) :
    (I.rec7 l Z).what₂.perCol u a ((I.rec7 l Z).jN u φ) (e (KerRat.rowForm I l h u a z)) =
      (I.per l u a).PtilCol ((I.fm l u a).emb 0 (KerRat.colForm I l h u a (eM φ).1)) (KerRat.rowForm I l h u a z) := by
  have hj := (I.rec7 l Z).nuIn_jN u φ
  rw [heM3 φ] at hj
  by_cases ha : a = (I.rec7 l Z).what₂.mu0
  · subst ha
    have e1 : e = (I.rec7 l Z).eMt u := eq_of_heq (he1 rfl)
    rw [(I.rec7 l Z).perCol_base_eq_PtilCol u, hj, e1]
    erw [LinearEquiv.symm_apply_apply]
    rfl
  · rw [(I.rec7 l Z).perCol_tie u a ha, hj, he2 ha]
    erw [LinearEquiv.symm_apply_apply]
    exact congrArg (fun w => (I.per l u a).PtilCol w (KerRat.rowForm I l h u a z)) (heM4 a (eM φ).1).symm

set_option maxHeartbeats 40000000 in

theorem tiesAt_true : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} (I : GlobalTheory.Mem.Col2.TC B X) (h : I.Ok) (l : I.Laws) (Z : GlobalTheory.Mem.Col2.TC.Later B (I.cols l)) (l0 : I.Law0 l), GlobalTheory.Mem.Col2.ColIn.JetsIn I → ∀ (EX : ErrX (I.rec7 l Z)) (Dx : DivX (I.rec7 l Z)) (a : I.ι), EX.piG = X.piG → EX.piT = X.piT → I.QpIs Dx.Qp → RowPin I h l Z a → TiesAt (I.rec7 l Z) EX Dx a := by
  intro B X I h l Z l0 hJ EX Dx a h1 h2 hQ hR
  change (I.rec7 l Z).what₂.Tup at a
  rw [← exOf_eq EX h1 h2]
  have hA : ambOf (recSeam (I.rec7 l Z)) (baseCast B.ccK_top.symm (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G)) I.chi I.J.cD = I.A :=
    (ambOf_baseCast _ _ _ _ _).trans (AmbIn.amb_eq_ambOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G I.J I.chi).symm
  have hX := base_fields_primes_ok B X
  have hcc : TaylorLogMetric.IsCurveIdeal (I.rec7 l Z) ⊤ := ⟨top_ne_bot, by simp⟩
  have hδ := (I.J.ok_iff B (I.cols l) Z.W Z.V Z.S Z.N Z.G).1 h.amb_ok
  have hχ : TaylorLogMetric.IsChi (I.rec7 l Z) I.chi := GlobalTheory.Mem.ChiIdeal.isChi_chiId _ _ I.C.isChi
  have hFL : KerRat.FamilyLaws I l Z := ⟨GlobalTheory.Mem.NatEqui.eqP _ _ _ (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G) I.chi hcc hδ.1 hχ,
    (GlobalTheory.NatFamily.family _ _ _ (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G) I.chi hcc hδ.1 hχ).1⟩
  have hFam := KerRat.kernels_rational I l Z h hJ (Or.inr (hFL))
  refine ⟨I.Ch, I.C.mu0, I.C.eta, I.sel, I.J.δ, baseCast B.ccK_top.symm (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G), I.chi, I.J.cD, ?_, ?_, ?_, fun u => ?_⟩
  · obtain ⟨c1, c2, c3, c4, -, -, c7, -⟩ := GlobalTheory.Core.Ht2.host_fields_primes_ties I h hX.1 l Z
    exact ⟨c1, c2, c3, c4, c7⟩
  · exact ⟨h.ch_ok, h.ch_tied, h.weil, h.sel_ok⟩
  · exact ⟨by rw [show (I.rec7 l Z).host.ccK = ⊤ from B.ccK_top]; exact hδ.1, hχ, hδ.2⟩
  · have hC : ∀ A : Amb B.fields, A = I.A → ChainTie (D := I.rec7 l Z) (EX := exOf EX h1 h2) I.Ch I.sel Dx I.C.mu0 A u a := by
      rintro A rfl
      obtain ⟨hne, hb⟩ := (hFam.1 u a).period
      obtain ⟨hY, hK, hF, hM, hper⟩ := hb hne.some
      obtain ⟨eM, heM1, heM2, heM3, heM4⟩ := GlobalTheory.T.ramifiedColumns_trueColumns_eq_concrete I h l Z l0 u
      obtain ⟨e, he1, he2, he3, he4⟩ := hR u
      let rE := GlobalTheory.PeriodOnStep.rowEmb (Pr := B.primes X) (I := I.chIn u a) B.wts I.Ch I.sel (I.tup a) I.Ps (I.perIn u a).b0
        (I.perIn u a).til (I.perIn u a).ext (I.perIn u a).tz (I.perIn u a).H (KerRat.tilOk I h u a).2.2 B.embLL
      have hrf : ⇑rE = KerRat.rowForm I l h u a := rfl
      refine chainTie_of (D := I.rec7 l Z) (EX := exOf EX h1 h2) I.Ch I.sel Dx I.C.mu0 I.A u a (I.tup a) (mem_tupGrp_of_subset (badS_subset h l Z) (I.tup a).2) ?_
      refine ⟨I.cst a, I.idx a, h.idx_ok a, hne.some, hY, hK, hF, hM, (show ((I.rec7 l Z).div.Nu u).V ≃+ MramV (recWts (exOf EX h1 h2)) I.Ch u from eM).toLinearEquiv heM1, LinearMap.comp (σ₁₃ := B.embLL) e.toLinearMap rE, h.sharp a, ?_, ?_, ?_, ?_, ?_⟩
      · refine ⟨?_, fun e0 => by rw [e0]; exact congrArg Subtype.val I.trueColumn_tuple_trivial_eq_one⟩
        have hfin : (Qprime (I.tup a : Chr B.fields.F B.fields.E B.fields.K)).Finite :=
          GlobalTheory.OpenChrRam.qprime_finite _ _ _ _ (I.tup a).2.1.1.1.1.2
        ext p
        rw [Finset.mem_coe, hQ a p]
        constructor
        · rintro ⟨hp, P, hP, hpP⟩
          obtain ⟨v, hv, rfl, -⟩ := I.exists_of_mem_Q hP
          refine ⟨v, hv, ?_⟩
          have := (GlobalTheory.Mem.ReadTwist.plc_under_eq_iff (F := B.host.F) (I.sel v) hp).2 hpP
          rwa [GlobalTheory.Mem.LevTwist.under_sel h v] at this
        · rintro ⟨v, hv, rfl⟩
          have hmem : I.sel v ∈ I.Q a := by
            classical
            unfold ColIn.Q QE
            rw [dif_pos hfin]
            convert Finset.mem_image_of_mem I.sel (hfin.mem_toFinset.2 hv)
          have hu := (GlobalTheory.Mem.ReadTwist.plc_under_eq_iff (F := B.host.F) (I.sel v) (Formalism.L2.DIV.plc_prime' v)).1
          rw [GlobalTheory.Mem.LevTwist.under_sel h v] at hu
          exact ⟨Formalism.L2.DIV.plc_prime' v, I.sel v, hmem, hu rfl⟩
      · exact fun i hi => hJ a u i hi
      · exact colTie_of_addEquiv (EX := exOf EX h1 h2) I.Ch u eM heM1 heM2
      · obtain ⟨r1, r2⟩ := GlobalTheory.T.rowForms_coefficientField_form_complexPeriodRows I h l u a
        refine ⟨fun s hs => (r1 s hs).map' e.toLinearMap e.ker, span_range_comp_eq_top rE e r2, fun v hv => ?_, he4⟩
        obtain ⟨z, hz⟩ := he3 v hv
        exact ⟨z, hz⟩
      · intro φ x
        exact (perCol_eq I h l Z u a eM heM3 heM4 e he1 he2 φ x).trans (hper (eM φ).1 x)
    exact hC _ hA

end GlobalTheory.TiesTrue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PulledLatticeVectorMemDualBaseLatticeCompletionStatement
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col GlobalTheory.TwU Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pulledLatticeVector_mem_dualBaseLatticeCompletion : ∀ {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (sp : Spaces R F E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E), IsUnit J.det → ∀ (c : GL (Fin N) E) (a : 𝓞 E)
    (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)), x ∈ UPts sp.cm.sig J (FiniteAdeleRing (𝓞 F) F) →
    ∀ (Lb : Submodule (𝓞 E) (Fin N → E)), Module.Finite (𝓞 E) Lb → Submodule.span E (Lb : Set (Fin N → E)) = ⊤ →
    (∀ y ∈ Lb, y ∈ dualSet (sp.cm.sig : E →+* E) J Lb) → ∀ (v : HeightOneSpectrum (𝓞 F)) (y : Fin N → E),
    y ∈ latCo sp J c a x Lb →
    (fun l => prV (E := E) v (pullV (F := F) (ratA F c * x) y l)) ∈
      latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) J Lb)) := by
  first | exact @GlobalTheory.MemDual.mem_latS_dual_of_latCo | exact GlobalTheory.MemDual.mem_latS_dual_of_latCo | (intros; apply GlobalTheory.MemDual.mem_latS_dual_of_latCo <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RationalUnitaryOrthonormalCoordsIsColumnIsometry
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV

noncomputable section

namespace GlobalTheory.TwRat

theorem ratUnitCol : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ i (hi : i ≤ D.R.m) (γ : GL (Fin (D.R.N i)) D.host.E), γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi) →
      ∃ g : UF t.X.E (D.R.N i), seamGL t.seam g.1 = A.crd i hi * γ * (A.crd i hi)⁻¹) := by
  intro D _ _ _ _ _ _ _ _ t u μ St A dtU a hP _ i hi γ hγ
  exact GlobalTheory.T.exists_unitaryAut_columnField_of_standard_unitary_matrix t.seam t.seam_ok (A.crd i hi * γ * (A.crd i hi)⁻¹)
    (GlobalTheory.unitary_conj_orthonormal D _ _ _ (hP.crd_orth i hi) hγ)

end GlobalTheory.TwRat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowsAOfJumpCountStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rows_a_of_jump_count : GlobalTheory.NRows.Hypotheses₂ → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), JumpsCard D.nd D.naut → GlobalTheory.NRows.RowsA D := by
  first | exact @GlobalTheory.RowsAClose.main | exact GlobalTheory.RowsAClose.main | (intros; apply GlobalTheory.RowsAClose.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowsBAndLocalLifts
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RowsBClosing

theorem main : GlobalTheory.NRows.Hypotheses₂ → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), Join P →
    GlobalTheory.NRows.RowsA D → Formalism.MainNotions.SumRepresentations.adm1 D → (∀ i : D.nd.Loc, GlobalTheory.RowCopy.LamPos D (D.nd.mu i) (D.nd.j i)) →
    GlobalTheory.NRows.RowsB D ∧ ∀ i, PairLift D.nd D.naut i ∧ SplitBC D.nd D.naut i ∧ RepOfLoc D.nd D.naut i := by
  intro hPr hL D P J hA h1 hpos
  have hRM : ∀ i : D.nd.Loc, Nonempty (RowMod D P.rep (D.nd.j i)) := fun i => ⟨J.rowM i⟩
  obtain ⟨S, hT, hLaws, -⟩ := GlobalTheory.T.exists_true_reading_with_laws hPr.fin hL D P hRM
  have hU : RowUnit S := GlobalTheory.RowUnitProof.rowUnit_of_isTrue hL D P hRM S hT
  have hPR : PairRead S := GlobalTheory.T.pair_reading_of_join hPr.bz hL D P J S hT hU
  have hpair : ∀ i, PairLift D.nd D.naut i :=
    GlobalTheory.SplitPairLift.main hPr.bz hPr.bern hPr.howe _ _ _ D.nd D.naut P.T S hLaws hU hPR
  have hIf := GlobalTheory.AdmIface.main D
  have hcheb : ChebSplit D.nd := (hIf.2.1 hA.a5).1
  have hsplit : ∀ i, SplitBC D.nd D.naut i := fun i =>
    GlobalTheory.RowTie.splitBC_of_galIso _ _ _ D.nd D.naut i (GlobalTheory.BCGal.main D hA.tie0 hA.a2 hA.temp i) hcheb hA.an2
  have hrep : ∀ i, RepOfLoc D.nd D.naut i := GlobalTheory.T.local_rep_of_reading_laws hL D P S hT hLaws
  have hbc : ∀ i, BCEx D.nd D.naut i := hIf.1 h1
  have horth : ∀ i, GlobalTheory.ThetaExh.TypeOrth D.nd D.naut i := fun i => GlobalTheory.T.type_orthogonality_of_form hL D P i (J.form i)
  refine ⟨⟨?_, GlobalTheory.RowTie.split_theta_correspondence_of_local_pairings D hpair, GlobalTheory.T.adm4_of_rows_a hPr hL D P hRM hA,
    GlobalTheory.Proof.ThetaOneGenusOne.thetaOne_of_ties D hpos hpair horth hbc hsplit hrep⟩, fun i => ⟨hpair i, hsplit i, hrep i⟩⟩
  exact GlobalTheory.RowSizeClosing.rowSize_of_unitarySphericalComponent D
    (GlobalTheory.SplitRead.unitarySphericalComponent_of_reading hPr.bz _ _ _ D.nd D.naut P.T S hLaws hU)

end GlobalTheory.RowsBClosing
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceIdempotentComponentOneDeterminesPartStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlaceIdempotent_component_one_determines_part : ∀ (D : D7) (sp : SplitPlace D.host.E) (hF : D.host.F = maximalRealSubfield D.host.E)
    (p : GlobalTheory.LocMod.Place D (sp.w.adicCompletion D.host.E))
    (c : sp.v.adicCompletion (maximalRealSubfield D.host.E) ≃+* sp.w.adicCompletion D.host.E),
    (∀ a : Formalism.L2.Theta.AE D, p.π a = c (sp.proj (GlobalTheory.NJoin.tensCast hF (Formalism.L2.Theta.finPart D a)))) →
    sp.proj (GlobalTheory.NJoin.tensCast hF (Formalism.L2.Theta.finPart D p.e)) = 1 ∧
      ∀ x y, sp.proj (GlobalTheory.NJoin.tensCast hF x) = sp.proj (GlobalTheory.NJoin.tensCast hF y) →
        Formalism.L2.Theta.finPart D p.e * x = Formalism.L2.Theta.finPart D p.e * y := by
  first | exact @GlobalTheory.PlaceSupp.comp_idem | exact GlobalTheory.PlaceSupp.comp_idem | (intros; apply GlobalTheory.PlaceSupp.comp_idem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardFrameConjGLintLeSelfDualLatticeStabilizeStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardFrame_conj_GLint_le_selfDualLattice_stabilizer : ∀ {D : D7} (hF : D.host.F = maximalRealSubfield D.host.E) {V : TH.HSp D}
    (Ps : Formalism.IndefR.principalLevelFrame.RowPsi V V.rank) (sp : SplitPlace D.host.E)
    (β β' : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)),
    β * β' = 1 → β' * β = 1 →
    (∀ κ, Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram (Ps.ψ κ) =
      β * ((κ.1 : Matrix (Fin V.rank) (Fin V.rank) (ReciprocityTheory.Aut.AL D.host.E)).map (GlobalTheory.NJoin.tensCast hF).symm) * β') →
    (∀ κ, κ ∈ ReciprocityTheory.Aut.Umax D.host.E V.rank ↔ Ps.ψ κ ∈ Formalism.L2.Theta.KsphC V ∅) →
    ∀ (ε : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)
      (sec : sp.v.adicCompletion (maximalRealSubfield D.host.E) → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)
      (B : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)),
    (∀ t, sp.proj (GlobalTheory.NJoin.tensCast hF (sec t)) = t) →
    (∀ t ∈ sp.v.adicCompletionIntegers (maximalRealSubfield D.host.E), sec t ∈ Formalism.L2.Theta.intAE D) →
    (∀ x ∈ Formalism.L2.Theta.intAE D,
      sp.proj (GlobalTheory.NJoin.tensCast hF x) ∈ sp.v.adicCompletionIntegers (maximalRealSubfield D.host.E)) →
    sp.proj (GlobalTheory.NJoin.tensCast hF ε) = 1 →
    (∀ z, Formalism.IndefR.Mult.IntVec z → (fun a => ε * B.mulVec z a) ∈ Formalism.L2.NTheta.LamHat V) →
    (∀ y ∈ Formalism.L2.NTheta.LamHat V, ∃ z, Formalism.IndefR.Mult.IntVec z ∧ (fun a => ε * y a) = fun a => ε * B.mulVec z a) →
    ∀ g ∈ Formalism.UG.GLint (Fin V.rank) (Formalism.UG.Ov (maximalRealSubfield D.host.E) sp.v),
    ∀ z : Fin V.rank → sp.v.adicCompletion (maximalRealSubfield D.host.E),
      (∀ i, z i ∈ Formalism.UG.Ov (maximalRealSubfield D.host.E) sp.v) →
      ∃ z' : Fin V.rank → sp.v.adicCompletion (maximalRealSubfield D.host.E),
        (∀ i, z' i ∈ Formalism.UG.Ov (maximalRealSubfield D.host.E) sp.v) ∧
        (g : Matrix (Fin V.rank) (Fin V.rank) _).mulVec
            ((β'.map (fun x => sp.proj (GlobalTheory.NJoin.tensCast hF x)) *
              B.map (fun x => sp.proj (GlobalTheory.NJoin.tensCast hF x))).mulVec z) =
          (β'.map (fun x => sp.proj (GlobalTheory.NJoin.tensCast hF x)) *
              B.map (fun x => sp.proj (GlobalTheory.NJoin.tensCast hF x))).mulVec z' := by
  first | exact @GlobalTheory.SplitFrameLattice.glint_mul_frame_basis | exact GlobalTheory.SplitFrameLattice.glint_mul_frame_basis | (intros; apply GlobalTheory.SplitFrameLattice.glint_mul_frame_basis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardFrameMemHyperspecialIffMaxCompactTrivOutStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardFrame_mem_hyperspecial_iff_maxCompact_trivOutside : ∀ {D : D7} (hF : D.host.F = maximalRealSubfield D.host.E) {V : TH.HSp D} {n : ℕ} (Ps : Formalism.IndefR.principalLevelFrame.RowPsi V n), GlobalTheory.NJoin.StdFrame hF Ps → ∀ (sp : SplitPlace D.host.E) (κ : Formalism.AUTREP.GAf D.host.E n), Ps.ψ κ ∈ GlobalTheory.Hk3.hyp V sp.w ↔ κ ∈ Umax D.host.E n ∧ TrivOutside {sp.v} κ := by
  first | exact @GlobalTheory.FrameHyp.mem_hyp_iff | exact GlobalTheory.FrameHyp.mem_hyp_iff | (intros; apply GlobalTheory.FrameHyp.mem_hyp_iff <;> assumption)
end

