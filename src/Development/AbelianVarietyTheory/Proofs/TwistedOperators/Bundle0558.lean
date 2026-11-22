import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0533
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0469
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0356
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0541
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0521
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0071
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0943
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0540
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0547
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0162
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1729
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0542
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0393
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0114
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0143
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0113
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0240
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0020
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0238
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqEqToL2
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0421
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0141
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0056
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.FirstCoordinateAdmissible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousReprSymm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0126
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0205
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0241
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0499
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0525
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0428
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0007
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0217
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspAlongOfPairLifts
import Development.AbelianVarietyTheory.Proofs.HeightProofs.TypeAtOfDiscreteSeries
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0523
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0404
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0304
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisOSumSmul
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.MovedAlg

variable {D : D7}

def IsAlgComb (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (f₀ F : WO S T → ℂ) : Prop :=
  ∃ (n : ℕ) (c : Fin n → ℂ) (w : Fin n → WO S T), (∀ p, IsAlgebraic ℚ (c p)) ∧ (∀ p, (w p).map (infPart D) = 0) ∧
    F = ∑ p, c p • heisO ψ S T (w p) f₀

theorem isAlg_mul {a b : ℂ} (ha : IsAlgebraic ℚ a) (hb : IsAlgebraic ℚ b) : IsAlgebraic ℚ (a * b) := by
  rw [← mem_algebraicClosure_iff] at ha hb ⊢
  exact mul_mem ha hb

section Comb

variable {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {f₀ : WO S T → ℂ}

theorem IsAlgComb.zero : IsAlgComb ψ S T f₀ 0 :=
  ⟨0, Fin.elim0, Fin.elim0, fun p => p.elim0, fun p => p.elim0, by simp⟩

theorem IsAlgComb.smul {a : ℂ} (ha : IsAlgebraic ℚ a) {F : WO S T → ℂ} (h : IsAlgComb ψ S T f₀ F) :
    IsAlgComb ψ S T f₀ (a • F) := by
  obtain ⟨n, c, w, hc, hw, rfl⟩ := h
  refine ⟨n, fun p => a * c p, w, fun p => isAlg_mul ha (hc p), hw, ?_⟩
  rw [Finset.smul_sum]
  simp only [smul_smul]

theorem IsAlgComb.add {F F' : WO S T → ℂ} (hF : IsAlgComb ψ S T f₀ F) (hF' : IsAlgComb ψ S T f₀ F') :
    IsAlgComb ψ S T f₀ (F + F') := by
  obtain ⟨n, c, w, hc, hw, rfl⟩ := hF
  obtain ⟨m, c', w', hc', hw', rfl⟩ := hF'
  refine ⟨n + m, Fin.append c c', Fin.append w w', fun p => ?_, fun p => ?_, ?_⟩
  · refine Fin.addCases (fun q => ?_) (fun q => ?_) p
    · simpa using hc q
    · simpa using hc' q
  · refine Fin.addCases (fun q => ?_) (fun q => ?_) p
    · simpa using hw q
    · simpa using hw' q
  · rw [Fin.sum_univ_add]
    simp

theorem IsAlgComb.finsum : ∀ {n : ℕ} (c : Fin n → ℂ) (F : Fin n → WO S T → ℂ), (∀ p, IsAlgebraic ℚ (c p)) →
    (∀ p, IsAlgComb ψ S T f₀ (F p)) → IsAlgComb ψ S T f₀ (∑ p, c p • F p)
  | 0, _, _, _, _ => by simpa using (IsAlgComb.zero : IsAlgComb ψ S T f₀ 0)
  | n + 1, c, F, hc, hF => by
    rw [Fin.sum_univ_succ]
    exact (IsAlgComb.smul (hc 0) (hF 0)).add (IsAlgComb.finsum _ _ (fun p => hc _) fun p => hF _)

theorem heisO_sum_smul (u : WO S T) {n : ℕ} (c : Fin n → ℂ) (F : Fin n → WO S T → ℂ) :
    heisO ψ S T u (∑ p, c p • F p) = ∑ p, c p • heisO ψ S T u (F p) := by
  funext z
  simp only [heisO, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ => by ring

theorem IsAlgComb.Heisenberg₂
    (hψ : ∀ u v : WO S T, u.map (infPart D) = 0 → v.map (infPart D) = 0 → IsAlgebraic ℚ (ψ (symplOH S T u v)))
    {u : WO S T} (hu : u.map (infPart D) = 0) {F : WO S T → ℂ} (hF : IsAlgComb ψ S T f₀ F) :
    IsAlgComb ψ S T f₀ (heisO ψ S T u F) := by
  obtain ⟨n, c, w, hc, hw, rfl⟩ := hF
  refine ⟨n, fun p => c p * ψ (symplOH S T u (w p)), fun p => u + w p,
    fun p => isAlg_mul (hc p) (hψ _ _ hu (hw p)), fun p => ?_, ?_⟩
  · rw [Matrix.map_add _ (map_add (infPart D)), hu, hw p, add_zero]
  · rw [heisO_sum_smul]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [GlobalTheory.LinkCompare.heisO_heisO, smul_smul]

end Comb

theorem om_algComb {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW} (hX : IsBottomTri W i j X)
    (hψ : ∀ u v : WO (GlobalTheory.Grid.neg A) WW, u.map (infPart D) = 0 → v.map (infPart D) = 0 →
      IsAlgebraic ℚ (W.ψ (symplOH (GlobalTheory.Grid.neg A) WW u v)))
    (t : T) (x : GA D A) (h : GA D WW)
    (h0 : IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac (X.ω t (x, h) X.vac)) {F : WO (GlobalTheory.Grid.neg A) WW → ℂ}
    (hF : IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac F) : IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac (X.ω t (x, h) F) := by
  obtain ⟨n, c, w, hc, hw, rfl⟩ := hF
  have hv : IsThetaFunO W.ψ (GlobalTheory.Grid.neg A) WW X.vac := hX.is.isVac.2.theta
  have e : ∀ p, X.ω t (x, h) (heisO W.ψ (GlobalTheory.Grid.neg A) WW (w p) X.vac) =
      heisO W.ψ (GlobalTheory.Grid.neg A) WW (actO (GlobalTheory.Grid.neg A) WW ((GlobalTheory.Grid.ofSgn true A).symm x) h (w p))
        (X.ω t (x, h) X.vac) := fun p =>
    (hX.is.weil t).om_heis ((GlobalTheory.Grid.ofSgn true A).symm x) h (w p) X.vac hv
  rw [map_sum]
  simp only [map_smul, e]
  exact IsAlgComb.finsum _ _ hc fun p => IsAlgComb.Heisenberg₂ hψ (GlobalTheory.FinApprox.actO_fin _ _ (hw p)) h0

end GlobalTheory.MovedAlg

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergRootSmulFiniteRationalLatticeDecompStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenberg_root_smul_finiteRational_latticeDecomp : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsStdChar D ψ (-1) → IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ f : WO S T → ℂ, IsLatVac (heisO ψ S T) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) f → ∀ n : ℕ, 0 < n → ∀ w : WO S T, n • w ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) → ∃ (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (ζ : ℂ), (∃ m : ℕ, 0 < m ∧ ζ ^ m = 1) ∧ GlobalTheory.VacUnique.finRat S T (n • M) ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) ∧ heisO ψ S T w f = ζ • heisO ψ S T (GlobalTheory.VacUnique.finRat S T M) f := by
  first | exact @GlobalTheory.MultLatDecomp.heisO_eq_root_smul_finRat | exact GlobalTheory.MultLatDecomp.heisO_eq_root_smul_finRat | (intros; apply GlobalTheory.MultLatDecomp.heisO_eq_root_smul_finRat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergTranslateFiniteRationalRealGaussianStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergTranslate_finiteRational_realGaussian : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1 → IsStdChar D ψ (-1) → IsInfFam θ → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → ∀ Φ : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank → ℂ, (∀ w : WO S T, w.map (finPart D) = 0 → f w = GlobalTheory.FockPos.gaussO θ frS frT w * Φ (GlobalTheory.FockPos.zCo θ frS frT w)) → ∀ (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (X : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank), X = (fun τ a b => -(((GlobalTheory.FockPos.frAt frT τ)⁻¹ * Matrix.of (GlobalTheory.VacUnique.infRat S T M τ) * GlobalTheory.FockPos.frAt frS τ) a b)) → ∀ w : WO S T, w.map (finPart D) = 0 → heisO ψ S T (GlobalTheory.VacUnique.finRat S T M) f w = GlobalTheory.FockPos.gaussO θ frS frT w * (Φ (GlobalTheory.FockPos.zCo θ frS frT w + X) * Complex.exp (-(Real.pi : ℂ) * (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, GlobalTheory.FockPos.zCo θ frS frT w τ a b * starRingEnd ℂ (X τ a b)) - (Real.pi : ℂ) * (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, X τ a b * starRingEnd ℂ (X τ a b)) / 2)) := by
  first | exact @GlobalTheory.MovedTrans.heisO_finRat_real | exact GlobalTheory.MovedTrans.heisO_finRat_real | (intros; apply GlobalTheory.MovedTrans.heisO_finRat_real <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HorizontalThetaLevelSecond
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ThetaLiftSmoothAut

theorem isAutFunSm_th : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i ≤ D.R.m → j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.V i j).V (G.V i (j + 1)).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i (j + 1)) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.th t i j).ω h g Φ * φ g) (G.meas t i (j + 1)).fd (G.meas t i (j + 1)).ν) → IsAutFunSm R.θ (G.V i j).V (fun h => ∫ g in (G.meas t i (j + 1)).fd, thetaKO (G.th t i j).ω h g Φ * φ g ∂(G.meas t i (j + 1)).ν) := by
  intro _hL hP D _hS G₀ _ _ Pl0 T A Ks _ _ _ R G hRB hG t i j hi hj Φ hΦ φ hφ _hI
  have hM := GlobalTheory.PairLift.haar_vert hRB hG t hi (Nat.succ_le_of_lt hj)
  have hw : IsWeilDatumO R.ψ (G.V i j).V (G.V i (j + 1)).V _ _ (G.th t i j).ω := (hG.arrows.th t i j hi hj).weil
  exact isAutFunSm_thetaLift hP.cuspRapidDecay hRB.inf hw hΦ hM.1 hM.2 hφ.1 hφ.2.1

end GlobalTheory.ThetaLiftSmoothAut

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentCutMemLatticeStabilizerOfProductLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open Matrix

namespace GlobalTheory.CutProdLev

theorem cutGL_mem_St_of_mem_prodLev : ∀ {D : D7} {n : ℕ} (β : GL (Fin n) (Lev.EAf D)) (P : Finset (Pl D.host.E))
    {n' : P → ℕ} (h : ∀ w, n' w = n) (K : ∀ w : P, Subgroup (GL (Fin (n' w)) (Kw w.1))) (x : GL (Fin n) (Lev.EAf D)),
    x ∈ prodLev β P h K → ∀ (b : Lev.EAf D) (hb : b * b = b),
    (∀ w : Pl D.host.E, (∃ PP ∈ P, w.under (𝓞 D.host.F) = PP.under (𝓞 D.host.F)) → GlobalTheory.StdFrames.cpt (D := D) w b = 0) →
    GlobalTheory.UnitaryIdemCut.cutGL b hb x ∈ St β := by
  intro D n β P n' h K x hx b hb hb0
  apply StabilizerBasis.GlobalTheory.CompanionTheory.StabBasis.mem_St_of_inBasis_mem_KO
  intro w

  have hc : GlobalTheory.StdFrames.cpt (D := D) w b * GlobalTheory.StdFrames.cpt (D := D) w b = GlobalTheory.StdFrames.cpt (D := D) w b :=
    (map_mul (GlobalTheory.StdFrames.cpt (D := D) w) b b).symm.trans (congrArg _ hb)
  have h01 : GlobalTheory.StdFrames.cpt (D := D) w b = 0 ∨ GlobalTheory.StdFrames.cpt (D := D) w b = 1 := by
    have h' : GlobalTheory.StdFrames.cpt (D := D) w b * (GlobalTheory.StdFrames.cpt (D := D) w b - 1) = 0 := by
      rw [mul_sub, hc, mul_one, sub_self]
    rcases mul_eq_zero.mp h' with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (sub_eq_zero.mp h1)

  have hconj : (MulAut.conj β⁻¹).toMonoidHom (GlobalTheory.UnitaryIdemCut.cutGL b hb x) =
      GlobalTheory.UnitaryIdemCut.cutGL b hb ((MulAut.conj β⁻¹).toMonoidHom x) :=
    (GlobalTheory.UnitaryIdemCut.cutGL_conj b hb β⁻¹ x).symm
  have hloc : ∀ y : GL (Fin n) (Lev.EAf D), GlobalTheory.StdFrames.loc w (GlobalTheory.UnitaryIdemCut.cutGL b hb y) =
      GlobalTheory.UnitaryIdemCut.cutGL _ hc (GlobalTheory.StdFrames.loc w y) := fun y =>
    GlobalTheory.UnitaryIdemCut.bc_cutGL (GlobalTheory.StdFrames.cpt w) b hb _ hc rfl y
  rcases h01 with h0 | h1
  ·
    have e1 : ∀ g : GL (Fin n) (IsDedekindDomain.HeightOneSpectrum.adicCompletion D.host.E w), GlobalTheory.UnitaryIdemCut.cutGL _ hc g = 1 := fun g => Units.ext (by
      rw [GlobalTheory.UnitaryIdemCut.cutGL_val, h0]
      simp)
    have e : GlobalTheory.FunObj.inBasis rfl β w (GlobalTheory.UnitaryIdemCut.cutGL b hb x) = 1 := by
      simp only [GlobalTheory.FunObj.inBasis, MonoidHom.comp_apply]
      rw [hconj, hloc, e1, map_one]
    rw [e]
    exact one_mem _
  ·

    unfold GlobalTheory.FunObj.prodLev at hx
    have hx2 := (Subgroup.mem_inf.mp hx).2
    rw [Subgroup.mem_iInf] at hx2
    have hx3 := hx2 w
    rw [Subgroup.mem_iInf] at hx3
    have hxw := Subgroup.mem_comap.mp (hx3 fun PP hPP e => by
      have h2 := hb0 w ⟨PP, hPP, e⟩
      rw [h1] at h2
      exact one_ne_zero h2)
    have e1 : ∀ g : GL (Fin n) (IsDedekindDomain.HeightOneSpectrum.adicCompletion D.host.E w), GlobalTheory.UnitaryIdemCut.cutGL _ hc g = g := fun g => Units.ext (by
      rw [GlobalTheory.UnitaryIdemCut.cutGL_val, h1]
      simp)
    have e : GlobalTheory.FunObj.inBasis rfl β w (GlobalTheory.UnitaryIdemCut.cutGL b hb x) = GlobalTheory.FunObj.inBasis rfl β w x := by
      simp only [GlobalTheory.FunObj.inBasis, MonoidHom.comp_apply]
      rw [hconj, hloc, e1]
    rw [e]
    exact hxw

end GlobalTheory.CutProdLev
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegerOutsidePrimePowDvdMaximalIdealPowStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integer_outside_prime_pow_dvd_maximal_ideal_pow : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (p : GlobalTheory.FinPl.SplitPt D k) (w : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt p.e w → ∀ (d : ℕ) (m : 𝓞 D.host.E),
  m ∉ w.asIdeal ^ (d + 1) → ∀ z ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ d, ∃ c ∈ 𝒪[k], (z : k) = c * p.pr (incA D ((m : 𝓞 D.host.E) : D.host.E)) := by
  first | exact @GlobalTheory.SplitPtLev.dvd_of_mem_maxIdeal_pow | exact GlobalTheory.SplitPtLev.dvd_of_mem_maxIdeal_pow | (intros; apply GlobalTheory.SplitPtLev.dvd_of_mem_maxIdeal_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCompactUnitaryRealPointsOfGramEqOne
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

namespace GlobalTheory.GramOneCompact

theorem isCompact_GinfC_of_gram_eq_one : ∀ (D : D7) (V : HSp D), V.gram = 1 → IsCompact (GinfC V : Set (GA D V)) := by
  intro D V hg
  have hL : (GlobalTheory.SW.stdL D.host.E V.rank).FG ∧ Submodule.span D.host.E
      (GlobalTheory.SW.stdL D.host.E V.rank : Set (Fin V.rank → D.host.E)) = ⊤ := by
    refine ⟨Submodule.fg_span (Set.finite_range _), ?_⟩
    rw [eq_top_iff, ← (Pi.basisFun D.host.E (Fin V.rank)).span_eq]
    apply Submodule.span_mono
    rintro _ ⟨a, rfl⟩
    apply Submodule.subset_span
    exact ⟨a, by simp⟩
  obtain ⟨C, hC, hCm⟩ := GlobalTheory.Ker.CongTop.exists_compact V _ hL.1 hL.2
  refine hC.of_isClosed_subset (GlobalTheory.Ker.CongTop.isClosed_GinfC V) fun k hk => hCm k ?_ (Or.inr hg)
  have hk1 : finHom V k = 1 := hk
  have h1 : GlobalTheory.Ker.fmt V k = GlobalTheory.Ker.fmt V 1 := by
    rw [GlobalTheory.Ker.CongTop.fmt_eq, GlobalTheory.Ker.CongTop.fmt_eq, hk1, map_one]
  rw [h1]
  exact (GlobalTheory.Ker.CongTop.congSub V (GlobalTheory.SW.stdL D.host.E V.rank) 1).one_mem.1

end GlobalTheory.GramOneCompact
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCompactUnitriangularOfRationalMulMemCompactStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompact_unitriangular_of_rational_mul_mem_compact : ∀ (D : D7) (n ρ : ℕ) (x₀ : Matrix (Fin n) (Fin ρ) D.host.E), LinearIndependent D.host.E x₀.transpose → ∀ K : Set (Mx D n ρ), IsCompact K → IsCompact {u : UX D ρ | rat x₀ ⬝ u.1.1 ∈ K} := by
  first | exact @GlobalTheory.AscFin.isCompact_setOf_rat_mul_mem | exact GlobalTheory.AscFin.isCompact_setOf_rat_mul_mem | (intros; apply GlobalTheory.AscFin.isCompact_setOf_rat_mul_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsContRepLeftRep
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta MeasureTheory Matrix

noncomputable section

namespace GlobalTheory.LeftRegularRepresentation

def leftRep {K : Type} [Group K] (F : Submodule ℂ (K → ℂ)) (hF : ∀ φ ∈ F, ∀ a : K, (fun k => φ (a * k)) ∈ F) :
    Representation ℂ K F where
  toFun a :=
    { toFun := fun φ => ⟨fun k => φ.1 (a⁻¹ * k), hF _ φ.2 _⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by
    ext φ k
    simp
  map_mul' a b := by
    ext φ k
    simp [mul_assoc]

theorem dual_mem_span {K : Type} (F : Submodule ℂ (K → ℂ)) [FiniteDimensional ℂ F] (ℓ : Module.Dual ℂ F) :
    ℓ ∈ Submodule.span ℂ (Set.range fun y : K => (LinearMap.proj y).comp F.subtype) := by
  have h : (Submodule.span ℂ (Set.range fun y : K =>
      ((LinearMap.proj y).comp F.subtype : Module.Dual ℂ F))) = ⊤ := by
    refine Submodule.span_eq_top_of_ne_zero fun z hz => ?_
    by_contra hc
    push Not at hc
    exact hz (Subtype.ext (funext fun y => hc _ ⟨y, rfl⟩))
  rw [h]
  trivial

theorem isContRep_leftRep {K : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    (F : Submodule ℂ (K → ℂ)) [FiniteDimensional ℂ F] (hF : ∀ φ ∈ F, ∀ a : K, (fun k => φ (a * k)) ∈ F)
    (hc : ∀ φ ∈ F, Continuous φ) : GlobalTheory.Published.AutFin.IsContRep (leftRep F hF) := by
  intro ℓ w
  induction dual_mem_span F ℓ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, rfl⟩ := hx
    exact (hc _ w.2).comp (continuous_inv.mul continuous_const)
  | zero => exact continuous_const
  | add x y _ _ hx hy => exact hx.add hy
  | smul a x _ hx => exact hx.const_smul a

theorem conv_mem {K : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsHaarMeasure]
    (F : Submodule ℂ (K → ℂ)) (hF : ∀ φ ∈ F, ∀ a : K, (fun k => φ (a * k)) ∈ F)
    (hc : ∀ φ ∈ F, Continuous φ) {e : K → ℂ} (he : e ∈ F) {f : K → ℂ} (hf : Continuous f) :
    (fun a => ∫ k, e k * f (a * k) ∂μ) ∈ GlobalTheory.Published.AutFin.coeffSpan (leftRep F hF) := by
  have hi : ∀ φ : F, Integrable (fun k => φ.1 k * f k) μ := fun φ =>
    ((hc _ φ.2).mul hf).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let ℓ : Module.Dual ℂ F :=
    { toFun := fun φ => ∫ k, φ.1 k * f k ∂μ
      map_add' := fun a b => by
        rw [← integral_add (hi a) (hi b)]
        simp only [Submodule.coe_add, Pi.add_apply, add_mul]
      map_smul' := fun c a => by
        simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]
        exact integral_const_mul _ _ }
  refine Submodule.subset_span ⟨ℓ, ⟨e, he⟩, funext fun a => ?_⟩
  change _ = ∫ k, e (a⁻¹ * k) * f k ∂μ
  rw [← integral_mul_left_eq_self (fun k => e (a⁻¹ * k) * f k) a]
  simp only [inv_mul_cancel_left]

theorem kFinAt_avg : ∀ (D : Formalism.BasicNotions.D7) (θ : Formalism.IndefR.Datum.InfFam D), Formalism.L2.Theta.IsInfFam θ → ∀ (N : GlobalTheory.Grid.Node D) (ψ : Formalism.L2.Theta.GA D (GlobalTheory.Grid.Node.V N) → ℂ), Formalism.L2.Theta.IsAutFunSm θ (GlobalTheory.Grid.Node.V N) ψ → ∀ (τ : Formalism.BasicNotions.Rows.Data.Tau (Formalism.BasicNotions.D7.what₂ D)) (e : ↥(Formalism.REAL.KG (Formalism.IndefR.Mult.DSModel.ε (GlobalTheory.Grid.Node.M N) τ)) → ℂ), GlobalTheory.TypeSum.KFinFun (Formalism.IndefR.Mult.DSModel.ε (GlobalTheory.Grid.Node.M N) τ) e → GlobalTheory.CuspKFin.KFinAt θ N τ (GlobalTheory.SeriesToClosure.avg θ (GlobalTheory.Grid.Node.V N) τ (Formalism.IndefR.Mult.DSModel.ε (GlobalTheory.Grid.Node.M N) τ) (Formalism.IndefR.Mult.DSModel.fr (GlobalTheory.Grid.Node.M N) τ) e ψ) := by
  intro D θ hθ N ψ hψ τ e he
  obtain ⟨F, hfd, heF, hc, hF⟩ := he
  haveI : IsTopologicalGroup (GA D N.V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have hP := N.M.fr_unit τ
  have hJ := N.M.fr_gram τ
  have hmem := GlobalTheory.Published.AutFin.conj_mem_UH hP hJ
  have hd : IsUnit (N.M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 hP
  have hK : Continuous fun k : Formalism.REAL.KG (N.M.ε τ) => Formalism.REAL.toMK k :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hk : Continuous (GlobalTheory.Published.AutFin.kAt θ N.V τ (N.M.ε τ) (N.M.fr τ)) :=
    (GlobalTheory.PointAtPlaceHom.continuousOn_atTau hθ N.V τ).comp_continuous
      ((continuous_const.matrix_mul hK).matrix_mul continuous_const) hmem
  have hmul : ∀ a b, GlobalTheory.Published.AutFin.kAt θ N.V τ (N.M.ε τ) (N.M.fr τ) (a * b) =
      GlobalTheory.Published.AutFin.kAt θ N.V τ (N.M.ε τ) (N.M.fr τ) a * GlobalTheory.Published.AutFin.kAt θ N.V τ (N.M.ε τ) (N.M.fr τ) b := by
    intro a b
    unfold GlobalTheory.Published.AutFin.kAt
    rw [← GlobalTheory.PointAtPlaceHom.atTau_mul hθ N.V τ (hmem a) (hmem b)]
    congr 1
    have e1 : Formalism.REAL.toMK (a * b) = Formalism.REAL.toMK a * Formalism.REAL.toMK b := rfl
    rw [e1]
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hd]
  refine ⟨F, inferInstance, inferInstance, hfd, leftRep F fun φ h a => (hF φ h a).1,
    isContRep_leftRep F _ hc, fun x => ?_⟩
  have h := conv_mem (Formalism.REAL.muK (N.M.ε τ)) F (fun φ h a => (hF φ h a).1) hc heF
    (f := fun k => ψ (x * GlobalTheory.Published.AutFin.kAt θ N.V τ (N.M.ε τ) (N.M.fr τ) k))
    (hψ.cont.comp (continuous_const.mul hk))
  simp only [hmul, ← mul_assoc] at h
  exact h

end GlobalTheory.LeftRegularRepresentation

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsOpenCongruenceEmbeddingStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_congruence_embedding : ∀ (D : D7) (Y V : HSp D) (d : HermitianOrthogonalExtensionData Y V 1 1) (Λ : Lat Y) (𝔪 : Ideal (𝓞 D.host.E)), IsSelfDualC Y Λ → 𝔪 ≠ ⊥ → IsOpen {g : GA D V | Lev.finE V g ∈ congLev D.sp.cm V.gram (d.lat Λ fun _ => 1) 𝔪} := by
  first | exact @GlobalTheory.UnitaryEmbeddingOpenLevel.levOpen | exact GlobalTheory.UnitaryEmbeddingOpenLevel.levOpen | (intros; apply GlobalTheory.UnitaryEmbeddingOpenLevel.levOpen <;> assumption)
end

