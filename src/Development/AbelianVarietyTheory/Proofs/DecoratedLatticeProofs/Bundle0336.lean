import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0327
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0010
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CollSBound
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0054
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DegenerateConstant
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0328
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0322
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0019
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0205
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0330
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegrableMajorantCoordinateCosetMeasure
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0160
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0052
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFrameRescaleConjReductionsDiagonal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0457
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0450
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0020
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PiEqOfFinPart
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumAtPlaceEqLatticeIntertwinerMulDetChar
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0175
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0329
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0005
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DstarIdxPf
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0302
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0311
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DegenerateCollisionRowBoundAtParametersStatement
section
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degenerateCollision_rowBound_at_sizeData : ∀ CT cH cV Ca C2 Ch c C : ℝ, 1 ≤ c → CT ≤ c → |cH| + 2 ≤ c → |cV| + 2 ≤ c → 0 ≤ Ch → c ≤ C → 4 + (c ^ 2 + 2 * max (Ch - c) 0) * (6 * c + 2) ≤ C → 2 * C2 ≤ C → |Ca| ≤ C → ∀ (D : D7) (large₂ : SizeData₂ D) (u : D.what₂.Word) (T : TermTie D) (Z : LoopTie D large₂ T u u 1) (C' Cl Cg cb Cu cT C0 : ℝ), 3 * |C2| ≤ C' → Cnt.Hyp D large₂ u u C' Cl Cg cb Cu cT CT C0 1 → UnitaryVolumeMass.MeanFlagPairCount D large₂ u u C' Cl Cg cb Cu cT CT C0 1 3 c → UnitaryVolumeMass.stHH D large₂ u u C' Cl Cg cb Cu cT CT C0 1 cH → UnitaryVolumeMass.stVol D large₂ T u u 1 Z C' Cl Cg cb Cu cT CT C0 1 cV → AmpAt D large₂ C' Cl Cg cb Cu cT CT C0 (9 * c + 3) Ca C2 Ch 1 → SmallAt D large₂ C' Cl Cg cb Cu cT CT C0 1 → BridgeLemma.TermPtsTie T Z → @BridgeLemma.LatticeDeterminantFactorization D T u u → BridgeLemma₂.wordPairEntriesInLattice T u u → BridgeLemma.RowsDeg T Z C := by
  first | exact @GlobalTheory.Core.Deg.rowsDeg_at_record | exact GlobalTheory.Core.Deg.rowsDeg_at_record | (intros; apply GlobalTheory.Core.Deg.rowsDeg_at_record <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleLiftReductionToFockVectorsUniformStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubleLift_reduction_to_fockVectors_uniform : ∀ D : D7, BiAct D → CenFock D → LiftSum D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (A S A' : HSp D) (x : DefSp A) (y : DefSp S) (z : DefSp A'), x.Is → y.Is → z.Is → ∀ (k₀ : KerDat A S) (k₀' : KerDat S A'), k₀.Is ψ θ x y → k₀'.Is ψ θ y z → ∀ (χ : GA D A → ℂ) (C : WO A S → WO S A' → ℂ), IsBiVac ψ A S A' x.L y.L z.L C → IsBiSmooth C → ∃ (n : ℕ) (P : Fin n → PolF D S.rank A.rank) (P' : Fin n → PolF D A'.rank S.rank), ∀ (k : KerDat A S) (k' : KerDat S A'), k.Is ψ θ x y → k'.Is ψ θ y z → k.vac = k₀.vac → k'.vac = k₀'.vac → (∀ a ∈ GinfC A, ∀ b ∈ GinfC S, ∀ f, IsThetaFunO ψ A S f → k.om (a, b) f = k₀.om (a, b) f) → (∀ a ∈ GinfC S, ∀ b ∈ GinfC A', ∀ f, IsThetaFunO ψ S A' f → k'.om (a, b) f = k₀'.om (a, b) f) → ∀ φ, IsContAut A φ → HasCen A χ φ → biLift k.om k'.om x.vol y.vol φ (biComb ψ A S A' k.c k'.c C) = ∑ i, k'.lift ψ θ y z (P' i) (k.lift ψ θ x y (P i) φ) := by
  first | exact @GlobalTheory.SeeSaw.fockRed_uniform | exact GlobalTheory.SeeSaw.fockRed_uniform | (intros; apply GlobalTheory.SeeSaw.fockRed_uniform <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledCompactSubgroupConjHermitianSpaceStatement
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledCompactSubgroup_conj_hermitianSpace : ∀ (D : D7) (A : HSp D) (L L' : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (k : GA D A), k ∈ GfC A →
    (∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (z : Fin A.rank → TensorProduct D.host.F (Fv D.host.F v) D.host.E),
      z ∈ latLoc D.host.F L v ↔
        (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig A.gram (proj D.sp.cm.sig A.gram v k)).val *ᵥ z ∈ latLoc D.host.F L' v) →
    ∀ (a : GL (Fin A.rank) (AE D)) (x : GA D (dblSp A)), x ∈ KAd D.sp.cm.sig (dblSp A).gram L' a ↔
      (io A (k, k))⁻¹ * x * io A (k, k) ∈ KAd D.sp.cm.sig (dblSp A).gram L a := by
  first | exact @GlobalTheory.LatMove.mem_KAd_io_conj | exact GlobalTheory.LatMove.mem_KAd_io_conj | (intros; apply GlobalTheory.LatMove.mem_KAd_io_conj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledPairSchrodingerFunctionContinuousIntegrab
section
open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW

namespace GlobalTheory.Core.Rk.SchInt

theorem mixS_continuous_integrable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S S₀ T : HSp D} {ρ : ℕ}
    (d : HypDec S S₀ ρ) (v : GlobalTheory.Unf.VolM D T.rank ρ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (w : WO S₀ T) :
    Continuous (fun x => d.mixS T ψ v.μ v.𝓕 f x w) ∧ Integrable (fun x => d.mixS T ψ v.μ v.𝓕 f x w) v.μ := by
  have hc : Continuous (fun x => d.mixS T ψ v.μ v.𝓕 f x w) :=
    (GlobalTheory.HeisMixSource.heis_mixS D ψ hψ S S₀ T ρ d v f hf).2.2.2.1.comp
      (f := fun x : Mx D T.rank ρ => (x, w)) (continuous_id.prodMk continuous_const)
  refine ⟨hc, ?_⟩
  obtain ⟨θ, hθ⟩ := GlobalTheory.DualPairCompare.exists_infFam D
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := lattice_Mx D T.rank ρ
  haveI : BorelSpace (Mx D T.rank ρ) := ⟨rfl⟩
  haveI := v.covol.1
  obtain ⟨N, hN⟩ := GlobalTheory.Unf.MajInt.maj_integrable D θ hθ T.rank ρ (fun _ _ => True) 0 v.μ inferInstance
    (Filter.Eventually.of_forall fun x i j h => (h trivial).elim)
    (fun t _ => by
      have e : (fun x : Mx D T.rank ρ => x + t) = fun x => t + x := funext fun x => add_comm x t
      rw [e]; exact map_add_left_eq_self v.μ t)
  obtain ⟨U, hU, hfU⟩ := hf.level
  have hfL : f ∈ GlobalTheory.Size.thetaLevel ψ S T U := ⟨hf, hfU⟩
  obtain ⟨K, hK, hKN⟩ := GlobalTheory.Unf.mixS_le_maj D ψ hψ θ hθ S S₀ T ρ d v U hU
  obtain ⟨C, hC⟩ := hKN N
  have hfin := (GlobalTheory.T.heisenberg_sup_sobolev_seminorm_theta_laws D ψ hψ θ hθ S T).1 N f hf
  refine ⟨hc.aestronglyMeasurable, ?_⟩
  have hI := (hN K hK).2
  refine lt_of_le_of_lt (lintegral_mono fun x => (hC f hfL x w).trans
    (mul_le_mul_right (Real.ofReal_le_enorm _) _)) ?_
  rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.coe_ne_top hfin)]
  exact ENNReal.mul_lt_top (ENNReal.mul_ne_top ENNReal.coe_ne_top hfin).lt_top hI

theorem sch_continuous_integrable : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A B : HSp D)
    (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ f, IsThetaFunO ψ (dblSp A) B f →
    Continuous (sch ψ A B ν 𝓨 f) ∧ Integrable (sch ψ A B ν 𝓨 f) ν :=
  fun _ _ hψ A _ ν 𝓨 hν _ hf => mixS_continuous_integrable hψ (dblDec A) ⟨ν, 𝓨, hν⟩ hf 0

end GlobalTheory.Core.Rk.SchInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsDiagonalFrameChangeUnweightingSymEdges
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV Formalism.L2.SG.InstExistsPf GlobalTheory.FlagBasis
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DiagFrameWeights

theorem isUnit_res {E : Type} [Field E] [NumberField E] (PP : Formalism.L2.DIV.Pl E) (x : Formalism.L2.DIV.kP PP) (hx : x ≠ 0) :
    IsUnit x := by
  haveI : PP.asIdeal.IsMaximal := PP.isMaximal
  letI : Field (Formalism.L2.DIV.kP PP) := Ideal.Quotient.field PP.asIdeal
  exact isUnit_iff_ne_zero.mpr hx

set_option maxHeartbeats 1000000 in

theorem exists_diag_frame : ∀ {D : D7} {n : ℕ} (ρ k : ℕ) (Pg : Finset (Pl D.host.E)) (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (β₀ : GL (Fin n) (Formalism.IndefR.Lev.EAf D)), Formalism.L2.DIV.IsFrame β₀ Λ → ∀ a : ∀ PP : Pl D.host.E, Fin n → Fin n → kP PP, (∀ PP ∈ Pg, ∀ i j, Formalism.L2.DIV.symEdge ρ k i j → a PP i j ≠ 0) → ∃ β₃ : GL (Fin n) (Formalism.IndefR.Lev.EAf D), Formalism.L2.DIV.IsFrame β₃ Λ ∧ Formalism.L2.DIV.St β₃ = Formalism.L2.DIV.St β₀ ∧ ∀ PP ∈ Pg, ∀ y ∈ Formalism.L2.DIV.St β₀, (Formalism.L2.DIV.redFn β₃ PP y ∈ Formalism.L2.DIV.unipSym (kP PP) n ρ k ↔ Formalism.L2.DIV.redFn β₀ PP y ∈ Formalism.L2.DIV.unipSym (kP PP) n ρ k) ∧ (∑ i, ∑ j, if Formalism.L2.DIV.symEdge ρ k i j then a PP i j * ((Formalism.L2.DIV.redFn β₀ PP y : GL (Fin n) (kP PP)) : Matrix (Fin n) (Fin n) (kP PP)) i j else 0) = Formalism.L2.DIV.edgeSum (Formalism.L2.DIV.symEdge ρ k) (Formalism.L2.DIV.redFn β₃ PP y) := by
  intro D n ρ k Pg Λ β₀ hβ a ha
  classical
  let w : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Fin n → Fin n → (Formalism.L2.DIV.kP PP)ˣ := fun PP i j =>
    if h : PP ∈ Pg ∧ Formalism.L2.DIV.symEdge ρ k i j then (isUnit_res PP (a PP i j) (ha PP h.1 i j h.2)).unit else 1
  let d : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Fin n → (Formalism.L2.DIV.kP PP)ˣ := fun PP =>
    GlobalTheory.SeeConjScale.forestLift (Formalism.L2.DIV.symEdge ρ k) (GlobalTheory.SeeConjScale.symEdge_lt ρ k) (w PP)
  have hd : ∀ PP ∈ Pg, ∀ i j, Formalism.L2.DIV.symEdge ρ k i j → (((d PP i)⁻¹ : (Formalism.L2.DIV.kP PP)ˣ) : Formalism.L2.DIV.kP PP) * (d PP j : Formalism.L2.DIV.kP PP) = a PP i j := by
    intro PP hPP i j h
    have e := congrArg Units.val (GlobalTheory.SeeConjScale.forestLift_edge (Formalism.L2.DIV.symEdge ρ k) (GlobalTheory.SeeConjScale.symEdge_lt ρ k)
      (GlobalTheory.SeeConjScale.symEdge_uniq ρ k) (w PP) h)
    rw [Units.val_mul] at e
    rw [e]
    simp only [w, dif_pos (And.intro hPP h), IsUnit.unit_spec]
  choose u hu using fun j : Fin n => GlobalTheory.FrameRescale.exists_unit_res (D := D) Pg (fun PP => d PP j)
  have hSt : ∀ M, M ∈ Formalism.L2.DIV.St (β₀ * Formalism.L2.DIV.intGL D.host.F D.host.E n (GlobalTheory.SeeConjRead.diagGL u)) ↔ M ∈ Formalism.L2.DIV.St β₀ := by
    intro M
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨GlobalTheory.SeeConjRead.diagGL u * y * (GlobalTheory.SeeConjRead.diagGL u)⁻¹, (GlobalTheory.FrameRescale.frGL_mul β₀ (GlobalTheory.SeeConjRead.diagGL u) y).symm⟩
    · rintro ⟨y, rfl⟩
      refine ⟨(GlobalTheory.SeeConjRead.diagGL u)⁻¹ * y * GlobalTheory.SeeConjRead.diagGL u, ?_⟩
      rw [GlobalTheory.FrameRescale.frGL_mul]
      congr 1
      group
  have hred : ∀ PP ∈ Pg, ∀ M ∈ Formalism.L2.DIV.St β₀,
      Formalism.L2.DIV.redFn (β₀ * Formalism.L2.DIV.intGL D.host.F D.host.E n (GlobalTheory.SeeConjRead.diagGL u)) PP M =
        (GlobalTheory.SeeConjRead.diagGL (d PP))⁻¹ * Formalism.L2.DIV.redFn β₀ PP M * GlobalTheory.SeeConjRead.diagGL (d PP) := by
    intro PP hPP M hM
    obtain ⟨y, rfl⟩ := hM
    have e1 : Formalism.L2.DIV.frGL β₀ y =
        Formalism.L2.DIV.frGL (β₀ * Formalism.L2.DIV.intGL D.host.F D.host.E n (GlobalTheory.SeeConjRead.diagGL u)) ((GlobalTheory.SeeConjRead.diagGL u)⁻¹ * y * GlobalTheory.SeeConjRead.diagGL u) := by
      rw [GlobalTheory.FrameRescale.frGL_mul]
      congr 1
      group
    have hb : Formalism.UG.bc (Formalism.L2.DIV.resS D.host.F PP) (GlobalTheory.SeeConjRead.diagGL u) = GlobalTheory.SeeConjRead.diagGL (d PP) := by
      apply Units.ext
      ext i j
      show Formalism.L2.DIV.resS D.host.F PP (((GlobalTheory.SeeConjRead.diagGL u : GL (Fin n) (Formalism.L2.Herm.intAf D.host.F D.host.E)) : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf D.host.F D.host.E)) i j) =
        ((GlobalTheory.SeeConjRead.diagGL (d PP) : GL (Fin n) (Formalism.L2.DIV.kP PP)) : Matrix (Fin n) (Fin n) (Formalism.L2.DIV.kP PP)) i j
      rw [GlobalTheory.SeeConjRead.diagGL_val, GlobalTheory.SeeConjRead.diagGL_val, Matrix.diagonal_apply, Matrix.diagonal_apply]
      split_ifs with h
      · subst h
        exact hu i PP hPP
      · exact map_zero _
    have e3 := Formalism.L2.DIV.redFn_frGL (β₀ * Formalism.L2.DIV.intGL D.host.F D.host.E n (GlobalTheory.SeeConjRead.diagGL u)) PP ((GlobalTheory.SeeConjRead.diagGL u)⁻¹ * y * GlobalTheory.SeeConjRead.diagGL u)
    have e4 := Formalism.L2.DIV.redFn_frGL β₀ PP y
    rw [← e1] at e3
    rw [e3, e4, GlobalTheory.FrameRescale.bc_conj, hb]
  refine ⟨β₀ * Formalism.L2.DIV.intGL D.host.F D.host.E n (GlobalTheory.SeeConjRead.diagGL u), ?_, ?_, ?_⟩
  · intro x
    rw [hβ x]
    have hinv : ((β₀ * Formalism.L2.DIV.intGL D.host.F D.host.E n (GlobalTheory.SeeConjRead.diagGL u))⁻¹).val = Matrix.diagonal (fun i => ((((u i)⁻¹ : (Formalism.L2.Herm.intAf D.host.F D.host.E)ˣ) : (Formalism.L2.Herm.intAf D.host.F D.host.E)) : Formalism.IndefR.Lev.EAf D)) *
          (β₀⁻¹).val := by
      rw [_root_.mul_inv_rev, Units.val_mul, ← map_inv, GlobalTheory.SeeConjRead.diagGL_inv, GlobalTheory.FrameRescale.intGL_diagGL_val]
    rw [hinv]
    refine forall_congr' fun i => ?_
    rw [← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal]
    have hm : ((u i : (Formalism.L2.Herm.intAf D.host.F D.host.E)) : Formalism.IndefR.Lev.EAf D) * ((((u i)⁻¹ : (Formalism.L2.Herm.intAf D.host.F D.host.E)ˣ) : (Formalism.L2.Herm.intAf D.host.F D.host.E)) : Formalism.IndefR.Lev.EAf D) = 1 := congrArg Subtype.val (u i).mul_inv
    constructor
    · intro h
      exact Subring.mul_mem _ ((u i)⁻¹ : (Formalism.L2.Herm.intAf D.host.F D.host.E)ˣ).val.2 h
    · intro h
      have h2 := Subring.mul_mem _ (u i).val.2 h
      rwa [← mul_assoc, hm, one_mul] at h2
  · ext M
    exact hSt M
  · intro PP hPP y hy
    rw [hred PP hPP y hy]
    refine ⟨(GlobalTheory.SeeConjRead.unipSym_conj_iff ρ k (d PP) _).symm, ?_⟩
    unfold Formalism.L2.DIV.edgeSum
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs with h
    · rw [GlobalTheory.SeeConjRead.diagGL_conj_apply, ← hd PP hPP i j h]
      ring
    · rfl

end GlobalTheory.DiagFrameWeights
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralFramePointOfInertHalfLatticePoint
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.InertFrameLoc

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.InertFrameLoc

theorem cA_algebraMap_place (D : D7) (ε : AF D.host.F) :
    cA D (algebraMap (AF D.host.F) (AE D) ε) = algebraMap (AF D.host.F) (AE D) ε := by
  rw [Algebra.TensorProduct.algebraMap_apply]
  show sigR _ _ _ = _
  simp [sigR]

theorem placeIdem_mul {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε)
    (a : AE D) : algebraMap (AF D.host.F) (AE D) ε * a = GlobalTheory.EmbChart.tensAt D.host.E v (compFin D.host.F D.host.E v a) := by
  obtain ⟨α, rfl, h1, h0⟩ := hε
  have hα : α = singleFin v 1 := FiniteAdeleRing.ext _ fun u => by
    change evalV D.host.F u α = evalV D.host.F u (singleFin v 1)
    by_cases e : u = v
    · subst e; rw [evalV_singleFin_self, h1]
    · rw [evalV_singleFin_ne e, h0 u e]
  have h2 : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) = GlobalTheory.EmbChart.tensAt D.host.E v 1 := by
    rw [Algebra.TensorProduct.algebraMap_apply, hα, Algebra.TensorProduct.one_def, GlobalTheory.EmbChart.tensAt_tmul]
    rfl
  rw [h2, GlobalTheory.EmbChart.tensAt_mul_right, one_mul]

end GlobalTheory.InertFrameLoc

namespace GlobalTheory.InertFrameLoc

variable {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {w : HeightOneSpectrum (𝓞 D.host.E)}

theorem pair_mem_intL (S : HSp D) {s : Fin S.rank → D.host.E} (hs : s ∈ L0c D S)
    {z : Fin S.rank → w.adicCompletion D.host.E} (hz : z ∈ latAt w (frameLat S)) :
    ∑ m, algebraMap D.host.E (w.adicCompletion D.host.E) (∑ k, star (s k) * S.gram k m) * z m ∈
      Formalism.UG.intL (w.adicCompletion D.host.E) := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    simp only [← map_mul, ← map_sum]
    have hX : ∑ k, s k • S.frame k ∈ S.L0 := hs
    have hY : ∑ m, y m • S.frame m ∈ S.L0 := (mem_frameLat S y).1 hy
    have hd : ∑ m, y m • S.frame m ∈ Formalism.HermitianLatticesTheory.dual S.hT S.L0 := by rw [S.baseLattice_isUnimodular]; exact hY
    have h1 := Submodule.mem_iInf _ |>.1 (Submodule.mem_iInf _ |>.1 hd (∑ k, s k • S.frame k)) hX
    rw [Submodule.mem_comap] at h1
    obtain ⟨o, ho⟩ := Submodule.mem_one.1 h1
    have e : ∑ m, (∑ k, star (s k) * S.gram k m) * y m = algebraMap (𝓞 D.host.E) D.host.E o := by
      rw [ho]
      simp only [LinearMap.restrictScalars_apply, map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply,
        LinearMap.smul_apply, smul_eq_mul, Formalism.BasicNotions.HSpace.gram, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun k _ => ?_
      simp only [starRingEnd_apply, RingHom.id_apply]
      ring
    rw [e]
    rw [GlobalTheory.InertLoc.mem_intL, GlobalTheory.Idele.valued_algebraMap]
    exact HeightOneSpectrum.valuation_le_one w o
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    exact add_mem hx hy
  | smul c x _ hx =>
    have e : ∑ m, algebraMap D.host.E (w.adicCompletion D.host.E) (∑ k, star (s k) * S.gram k m) * (c • x) m =
        (c : w.adicCompletion D.host.E) * ∑ m, algebraMap D.host.E (w.adicCompletion D.host.E) (∑ k, star (s k) * S.gram k m) * x m := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Pi.smul_apply]
      show _ * ((c : w.adicCompletion D.host.E) * x m) = _
      ring
    rw [e]
    exact mul_mem (show Valued.v (c : w.adicCompletion D.host.E) ≤ 1 from c.2) hx

end GlobalTheory.InertFrameLoc

namespace GlobalTheory.InertFrameLoc

variable {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {w : HeightOneSpectrum (𝓞 D.host.E)}

def piW (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) : AE D →+* w.adicCompletion D.host.E :=
  (GlobalTheory.LFun.InertChart.complEquiv hw h).toRingHom.comp (compFin D.host.F D.host.E v)

theorem secW_piW (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) (a : AE D) :
    secW hw h (piW hw h a) = GlobalTheory.EmbChart.tensAt D.host.E v (compFin D.host.F D.host.E v a) := by
  show GlobalTheory.EmbChart.tensAt D.host.E v ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm
    (GlobalTheory.LFun.InertChart.complEquiv hw h (compFin D.host.F D.host.E v a))) = _
  rw [RingEquiv.symm_apply_apply]

theorem piW_tmul (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) (α : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)
    (m : D.host.E) : piW hw h (pairA D.host.F 0 α ⊗ₜ[D.host.F] m) =
      complMap h (evalV D.host.F v α) * algebraMap D.host.E (w.adicCompletion D.host.E) m := rfl

end GlobalTheory.InertFrameLoc

namespace GlobalTheory.InertFrameLoc

variable {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {w : HeightOneSpectrum (𝓞 D.host.E)}

theorem latO_frame_int (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) {S T : HSp D}
    {k : w.adicCompletion D.host.E} {aS : GL (Fin S.rank) (w.adicCompletion D.host.E)}
    {aT : GL (Fin T.rank) (w.adicCompletion D.host.E)} (hk : GlobalTheory.InertLoc.IsGen D w k)
    (haS : IsFrameAt w (frameLat S) aS) (haT : IsFrameAt w (frameLat T) aT) {u : WO S T}
    (hu : u ∈ latO S T (L0c D S) (L0c D T) (fun _ => True)) (i : Fin T.rank) (j : Fin S.rank) :
    (k⁻¹ • ((aT⁻¹).1 * u.map (piW hw h) * aS.1)) i j ∈ Formalism.UG.intL (w.adicCompletion D.host.E) := by
  induction hu using AddSubgroup.closure_induction generalizing i j with
  | mem x hx =>
    obtain ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩ := hx
    let c0 := complMap h (evalV D.host.F v α)
    let t' : Fin T.rank → w.adicCompletion D.host.E := fun l => algebraMap D.host.E _ (t l)
    let r : Fin S.rank → w.adicCompletion D.host.E :=
      fun m => algebraMap D.host.E _ (∑ l, star (s l) * S.gram l m)
    have e1 : Matrix.map (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t i * ∑ l, star (s l) * S.gram l j) :
        WO S T) (piW hw h) = (c0 * algebraMap D.host.E _ a) • vecMulVec t' r := by
      ext i j
      rw [Matrix.map_apply, Matrix.of_apply, piW_tmul, Matrix.smul_apply, smul_eq_mul, vecMulVec_apply,
        map_mul, map_mul]
      simp only [mul_assoc]
      rfl
    rw [e1, Matrix.mul_smul, Matrix.smul_mul, mul_vecMulVec, vecMulVec_mul, smul_smul, Matrix.smul_apply,
      vecMulVec_apply, smul_eq_mul]
    have h1 : c0 ∈ Formalism.UG.intL (w.adicCompletion D.host.E) := complMap_mem h (hα v)
    have h2 : k⁻¹ * algebraMap D.host.E _ a ∈ Formalism.UG.intL (w.adicCompletion D.host.E) := hk.2.2 a ha
    have h3 : ((aT⁻¹).1 *ᵥ t') i ∈ Formalism.UG.intL (w.adicCompletion D.host.E) := by
      refine (haT ((aT⁻¹).1 *ᵥ t')).2 ?_ i
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
      exact Submodule.subset_span ⟨t, (mem_frameLat T t).2 ht, rfl⟩
    have h4 : (r ᵥ* aS.1) j ∈ Formalism.UG.intL (w.adicCompletion D.host.E) := by
      have hcol : (fun m => aS.1 m j) ∈ latAt w (frameLat S) := by
        have := (haS (Pi.single j 1)).1 fun l => by
          by_cases e : l = j
          · subst e; simp
          · simp [e]
        rwa [Matrix.mulVec_single_one] at this
      show ∑ m, r m * aS.1 m j ∈ _
      exact pair_mem_intL S hs hcol
    have e2 : k⁻¹ * (c0 * algebraMap D.host.E (w.adicCompletion D.host.E) a) * (((aT⁻¹).1 *ᵥ t') i * (r ᵥ* aS.1) j) =
        c0 * (k⁻¹ * algebraMap D.host.E _ a) * (((aT⁻¹).1 *ᵥ t') i * (r ᵥ* aS.1) j) := by ring
    rw [e2]
    exact mul_mem (mul_mem h1 h2) (mul_mem h3 h4)
  | zero =>
    rw [Matrix.map_zero _ (map_zero _), Matrix.mul_zero, Matrix.zero_mul, smul_zero]
    exact zero_mem _
  | add x y _ _ hx hy =>
    rw [Matrix.map_add _ (map_add _), Matrix.mul_add, Matrix.add_mul, smul_add, Matrix.add_apply]
    exact add_mem (hx i j) (hy i j)
  | neg x _ hx =>
    rw [Matrix.map_neg _ (map_neg _), Matrix.mul_neg, Matrix.neg_mul, smul_neg, Matrix.neg_apply]
    exact neg_mem (hx i j)

end GlobalTheory.InertFrameLoc

namespace GlobalTheory.InertFrameLoc

theorem exists_uPt_of_half : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) (S T : HSp D) (k : w.adicCompletion D.host.E) (aS : GL (Fin S.rank) (w.adicCompletion D.host.E)) (aT : GL (Fin T.rank) (w.adicCompletion D.host.E)), GlobalTheory.InertLoc.IsGen D w k → IsFrameAt w (frameLat S) aS → IsFrameAt w (frameLat T) aT → ∀ e e', IsPrimeIdem w e e' → ∀ u ∈ latO S T (L0c D S) (L0c D T) (fun _ => True), IsHalf e u ∨ IsHalf (cA D e) u → ∃ x : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E), (∀ i j, x i j ∈ Formalism.UG.intL (w.adicCompletion D.host.E)) ∧ uPt hw h k aS aT x = u := by
  intro D v w hw h S T k aS aT hk haS haT e e' he u hu hhalf
  obtain ⟨ε, hε, -, -, hee⟩ := GlobalTheory.VacFixInert.inert_data (GlobalTheory.WeilAtPlace.conjPl_eq_of_inert hw h)
  obtain ⟨rfl, -⟩ := hee e e' he
  rw [h] at hε
  have hh : IsHalf (algebraMap (AF D.host.F) (AE D) ε) u := by
    rcases hhalf with h1 | h1
    · exact h1
    · rwa [cA_algebraMap_place] at h1
  have hent : ∀ i j, secW hw h (piW hw h (u i j)) = u i j := fun i j => by
    rw [secW_piW, ← placeIdem_mul hε, hh i j]
  refine ⟨k⁻¹ • ((aT⁻¹).1 * u.map (piW hw h) * aS.1), fun i j => latO_frame_int hw h hk haS haT hu i j, ?_⟩
  have e1 : k • ((aT.1 * (k⁻¹ • ((aT⁻¹).1 * u.map (piW hw h) * aS.1))) * (aS⁻¹).1) = u.map (piW hw h) := by
    rw [Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_inv_cancel₀ hk.1, one_smul, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  ext i j
  rw [uPt, e1, Matrix.map_apply, Matrix.map_apply, hent]

end GlobalTheory.InertFrameLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnitaryFiniteAdelicMapSelfDualCompletionsStatement
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_finiteAdelic_map_selfDual_completions : ∀ (D : D7) (A : HSp D) (L L' : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)),
    IsSelfDualC A L → IsSelfDualC A L' →
    ∃ b ∈ HR (Af D.host.F) D.sp.cm.sig A.gram, ∀ w : Fin A.rank → TensorProduct D.host.F (Af D.host.F) D.host.E,
      w ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L : Set (Fin A.rank → D.host.E)) ↔
        b.val *ᵥ w ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L' : Set (Fin A.rank → D.host.E)) := by
  first | exact @GlobalTheory.Core.Rk.OrthIsom.exists_unitary_latHat | exact GlobalTheory.Core.Rk.OrthIsom.exists_unitary_latHat | (intros; apply GlobalTheory.Core.Rk.OrthIsom.exists_unitary_latHat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HaarMeasureDisintegrationBesselGroup
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Mi.Disint

theorem disint : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A), ∃ c : ℝ, 0 < c ∧ ∀ G : X.B.I.GA → ENNReal, Measurable G → (∀ x, G x ≠ 0 → ∃ s ∈ SfinU X u, ∃ k ∈ X.K2, x.2 = s * X.xu u * k) → ∫⁻ x, G x ∂(X.B.I.muA X.B.μf) = ENNReal.ofReal c * ∫⁻ y, ∫⁻ s, ∫⁻ k in X.K2, G (iotaX X h s.1 * (y, X.xu u) * (1, k)) ∂X.B.μf ∂B.lev.μR ∂(X.nuQ u) := by
  intro D X h u ψ A B
  obtain ⟨μSf, hHaar, hσ, c₁, hc₁, hfin⟩ := GlobalTheory.T.haar_finite_adele_disintegration_stabilizer_compact D X u
  obtain ⟨c₃, hc₃, hR⟩ := GlobalTheory.T.lintegral_besselGroup_haar_eq_const_mul_prod D X h u ψ A B μSf hHaar hσ (GlobalTheory.T.real_stabilizer_product_measure_isHaarOnSet D X u)
  refine ⟨c₁ / c₃, div_pos hc₁ hc₃, ?_⟩
  intro G hGm hsupp
  haveI : SecondCountableTopology X.B.I.Gf := Formalism.L2.SG.Pf.gf_secondCountable X.B.I
  haveI := hσ
  set μS := ((X.muN u).prod (X.muH u)).map (fun p : X.B.I.Ginf × X.B.I.Ginf => p.1 * p.2) with hμS

  set g : X.B.I.Ginf → ENNReal := fun x => ∫⁻ t, ∫⁻ k in X.K2, G (x, t.1 * X.xu u * k) ∂X.B.μf ∂μSf with hgdef
  have hg : Measurable g := by
    have hΨ : Measurable (fun p : (X.B.I.Ginf × Formalism.L2.SG.Pf.SfinSub X.B.I X.eR (X.zR u)) × X.B.I.Gf =>
        G (p.1.1, p.1.2.1 * X.xu u * p.2)) :=
      hGm.comp (measurable_fst.fst.prodMk
        (((measurable_subtype_coe.comp measurable_fst.snd).mul_const _).mul measurable_snd))
    exact (hΨ.lintegral_prod_right' (ν := X.B.μf.restrict X.K2)).lintegral_prod_right' (ν := μSf)
  have hL : ∫⁻ x, G x ∂(X.B.I.muA X.B.μf) = ENNReal.ofReal c₁ * ∫⁻ y, ∫⁻ a, g (a * y) ∂μS ∂(X.nuQ u) := by
    have e0 : X.B.I.muA X.B.μf = (Formalism.L2.SG.ProjRows.muInf X.B.I).prod X.B.μf := rfl
    rw [e0, lintegral_prod _ hGm.aemeasurable]
    have e1 : ∀ x, ∫⁻ z, G (x, z) ∂X.B.μf = ENNReal.ofReal c₁ * g x := fun x =>
      hfin (fun z => G (x, z)) (hGm.comp measurable_prodMk_left) (fun z hz => hsupp (x, z) hz)
    simp_rw [e1]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, X.nuQ_weil u g hg]
  have hRy : ∀ y : X.B.I.Ginf, ∫⁻ s, ∫⁻ k in X.K2, G (iotaX X h s.1 * (y, X.xu u) * (1, k)) ∂X.B.μf ∂B.lev.μR =
      ENNReal.ofReal c₃ * ∫⁻ a, g (a * y) ∂μS := by
    intro y
    set Φ : X.B.I.GA → ENNReal := fun p => ∫⁻ k in X.K2, G (p.1 * y, p.2 * X.xu u * k) ∂X.B.μf with hΦ
    have hΦm : Measurable Φ := by
      have : Measurable (fun q : X.B.I.GA × X.B.I.Gf => G (q.1.1 * y, q.1.2 * X.xu u * q.2)) :=
        hGm.comp ((measurable_fst.fst.mul_const y).prodMk ((measurable_fst.snd.mul_const _).mul measurable_snd))
      exact this.lintegral_prod_right' (ν := X.B.μf.restrict X.K2)
    have e : ∀ s : besGrp B.d B.o, ∫⁻ k in X.K2, G (iotaX X h s.1 * (y, X.xu u) * (1, k)) ∂X.B.μf = Φ (iotaX X h s.1) := by
      intro s
      refine lintegral_congr fun k => ?_
      congr 1
      ext <;> simp
    simp_rw [e]
    rw [hR Φ hΦm]
  calc ∫⁻ x, G x ∂(X.B.I.muA X.B.μf) = ENNReal.ofReal c₁ * ∫⁻ y, ∫⁻ a, g (a * y) ∂μS ∂(X.nuQ u) := hL
    _ = ENNReal.ofReal (c₁ / c₃) * (ENNReal.ofReal c₃ * ∫⁻ y, ∫⁻ a, g (a * y) ∂μS ∂(X.nuQ u)) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (div_pos hc₁ hc₃).le, div_mul_cancel₀ _ hc₃.ne']
    _ = _ := by
        congr 1
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        exact (lintegral_congr fun y => hRy y).symm

end GlobalTheory.Core.Mi.Disint
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsJointlySmoothBiThetaWeilRepFirstVariableStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isJointlySmoothBiTheta_weilRep_first_variable : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (χA χS : (AE D)ˣ →* Circle) (oma : Om A S), IsWeilDatumO ψ A S χA χS oma → ∀ C, IsBiTheta ψ A S A' C → ∀ p, IsBiTheta ψ A S A' fun u v => oma p (fun u' => C u' v) u := by
  first | exact @GlobalTheory.BiTransfer.isBiTheta_act_left | exact GlobalTheory.BiTransfer.isBiTheta_act_left | (intros; apply GlobalTheory.BiTransfer.isBiTheta_act_left <;> assumption)
end

