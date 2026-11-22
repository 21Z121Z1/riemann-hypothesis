import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1518
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1462
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1473
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1478
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasurePreservingConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1532
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1524
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1505
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0036
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1526
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1530
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0175
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1520
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1416
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1496
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1506
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0026
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfM
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0038
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0769
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0028
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0026
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1497

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartFirstColumnsEqGraphTimesTopBlock
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.ChartGraph

namespace GlobalTheory.ChartGraph

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem chartMatrixTopBlock_det_eq_one (X : Data E r) (z : V (nd X)) (τ : X.Ψ) : (chartMatrixTopBlock X z τ).det = 1 := by
  rw [Matrix.det_of_lowerTriangular (chartMatrixTopBlock X z τ) (by
    intro i j hij
    have hij' : i < j := hij
    show nmat X z τ (Fin.castLE X.p0_le i) (Fin.castLE X.p0_le j) = 0
    have h1 : ¬ (Fin.castLE X.p0_le j < Fin.castLE X.p0_le i) := by
      rw [Fin.lt_iff_val_lt_val]; simp only [Fin.coe_castLE]; exact not_lt.mpr (le_of_lt hij')
    have h2 : Fin.castLE X.p0_le i ≠ Fin.castLE X.p0_le j := by
      intro h; apply ne_of_lt hij'; exact Fin.castLE_injective _ h
    simp only [nmat, dif_neg h1, if_neg h2])]
  apply Finset.prod_eq_one
  intro i _
  show nmat X z τ (Fin.castLE X.p0_le i) (Fin.castLE X.p0_le i) = 1
  simp [nmat]

theorem entry_eq (X : Data E r) (z : V (nd X)) (τ : X.Ψ) (m : Fin r) (a : Fin X.p0) :
    nmat X z τ m (Fin.castLE X.p0_le a) =
      ∑ c : Fin X.p0, X.lowBlock (graphCoord X z) τ m (Fin.castLE X.p0_le c) * chartMatrixTopBlock X z τ c a := by
  by_cases hm : (m : ℕ) < X.p0
  · have hrow : ∀ c : Fin X.p0, X.lowBlock (graphCoord X z) τ m (Fin.castLE X.p0_le c) =
        if (⟨m, hm⟩ : Fin X.p0) = c then 1 else 0 := by
      intro c
      simp only [Data.lowBlock, Matrix.of_apply]
      rw [dif_neg (by omega)]
      simp only [add_zero]
      congr 1
      apply propext
      constructor
      · intro h
        have hv : (m : ℕ) = (c : ℕ) := by simpa using congrArg (fun t : Fin r => (t : ℕ)) h
        exact Fin.ext hv
      · intro h; ext; rw [← h]; rfl
    simp only [hrow, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rfl
  · have hm' : X.p0 ≤ (m : ℕ) := not_lt.mp hm
    have hrow : ∀ c : Fin X.p0, X.lowBlock (graphCoord X z) τ m (Fin.castLE X.p0_le c) =
        graphCoord X z τ ⟨(m : ℕ) - X.p0, by have := m.isLt; omega⟩ c := by
      intro c
      simp only [Data.lowBlock, Matrix.of_apply]
      have hne : m ≠ Fin.castLE X.p0_le c := by
        intro h; have := congrArg Fin.val h; simp at this; have := c.isLt; omega
      rw [if_neg hne, dif_pos ⟨hm', c.isLt⟩, zero_add]
      rfl
    simp only [hrow]
    have hdet : IsUnit (chartMatrixTopBlock X z τ).det := by rw [chartMatrixTopBlock_det_eq_one]; exact isUnit_one
    have key : chartBottomLeftBlock X z τ * (chartMatrixTopBlock X z τ)⁻¹ * chartMatrixTopBlock X z τ = chartBottomLeftBlock X z τ := by
      rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.mul_one]
    have := congrFun (congrFun key ⟨(m : ℕ) - X.p0, by have := m.isLt; omega⟩) a
    rw [Matrix.mul_apply] at this
    have h2 : chartBottomLeftBlock X z τ ⟨(m : ℕ) - X.p0, by have := m.isLt; omega⟩ a = nmat X z τ m (Fin.castLE X.p0_le a) := by
      show nmat X z τ ⟨X.p0 + ((m : ℕ) - X.p0), _⟩ (Fin.castLE X.p0_le a) = _
      congr 1
      ext; simp only; omega
    exact (this.trans h2).symm

theorem cols_graph : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r)
    (z : V (nd X)) (τ : X.Ψ), (chartMatrixTopBlock X z τ).det = 1 ∧ ∀ a : Fin X.p0,
    col (mat (cpt X x z) τ) (Fin.castLE X.p0_le a) =
      ∑ c : Fin X.p0, chartMatrixTopBlock X z τ c a • col (mat (X.xZ x (graphCoord X z)) τ) (Fin.castLE X.p0_le c) := by
  intro E _ _ _ r X x z τ
  refine ⟨chartMatrixTopBlock_det_eq_one X z τ, fun a => ?_⟩
  funext k
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  show (mat x τ * mat (nmat X z) τ) k (Fin.castLE X.p0_le a) =
    ∑ c : Fin X.p0, chartMatrixTopBlock X z τ c a * (mat x τ * X.lowBlock (graphCoord X z) τ) k (Fin.castLE X.p0_le c)
  simp only [Matrix.mul_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  show mat x τ k m * nmat X z τ m (Fin.castLE X.p0_le a) = _
  rw [entry_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

end GlobalTheory.ChartGraph
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermAlongSubset
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability

noncomputable section
namespace GlobalTheory.ConstTrans
open GlobalTheory.StdPar GlobalTheory.Cusp

theorem unip_eq_unipFlag : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
      ∀ (S : Finset (Fin r)) (m : Fin r), m ∈ S → (∀ k ∈ S, k ≤ m) →
        GlobalTheory.StdPar.unip σ J X S = GlobalTheory.UAut.unipFlag σ J (GlobalTheory.StdPar.initCols X m) (fun i => (S.filter fun k => k.val < i.val).card) := fun F E _ _ _ _ _ σ h n J hJ r X Y hW S m hm hm' => le_antisymm (GlobalTheory.T.standardParabolicUnipotent_le_flagUnipotentRadical F E σ h n J hJ r X Y hW S m hm hm') (GlobalTheory.T.flagUnipotentRadical_le_standardParabolicUnipotent F E σ h n J hJ r X Y hW S m hm hm')
theorem unip_mono : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
      ∀ (S T : Finset (Fin r)), T ⊆ S → GlobalTheory.StdPar.unip σ J X T ≤ GlobalTheory.StdPar.unip σ J X S := GlobalTheory.T.standardParabolicUnipotent_mono
theorem unip_le_parFlag : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
      ∀ (S T : Finset (Fin r)) (m : Fin r), T ⊆ S → m ∈ T → (∀ k ∈ T, k ≤ m) →
        GlobalTheory.StdPar.unip σ J X S ≤ GlobalTheory.UAut.parFlag σ J (GlobalTheory.StdPar.initCols X m) (fun i => (T.filter fun k => k.val < i.val).card) := GlobalTheory.T.standardParabolicUnipotent_le_isotropicFlagStabiliser

theorem isConstAlong_zero_of_subset : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
      ∀ φ : GAd σ J → ℂ, Continuous φ → (∀ γ ∈ ratPts σ J, ∀ g, φ (γ * g) = φ g) → ∀ S T : Finset (Fin r), T ⊆ S →
        GlobalTheory.StdPar.IsConstAlong σ J X T φ 0 → GlobalTheory.StdPar.IsConstAlong σ J X S φ 0 := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW φ hφc hφ S T hTS hT
  by_cases hT0 : T = ∅
  · subst hT0
    have e := isConstAlong_empty hT
    rw [← e]
    exact isConstAlong_const σ J X S 0
  obtain ⟨mT, hmT, hmT'⟩ : ∃ m ∈ T, ∀ k ∈ T, k ≤ m := ⟨T.max' (Finset.nonempty_iff_ne_empty.2 hT0),
    T.max'_mem _, fun k hk => T.le_max' k hk⟩
  obtain ⟨mS, hmS, hmS'⟩ : ∃ m ∈ S, ∀ k ∈ S, k ≤ m := ⟨S.max' ⟨mT, hTS hmT⟩, S.max'_mem _, fun k hk => S.le_max' k hk⟩
  have hσ := sigma_sigma h
  have eS := unip_eq_unipFlag F E σ h n J hJ r X Y hW S mS hmS hmS'
  have eT := unip_eq_unipFlag F E σ h n J hJ r X Y hW T mT hmT hmT'
  have hCS : IsIsoCols σ J (initCols X mS) := isIsoCols_of_isWittFrame hW hσ hJ mS.2
  have hCT : IsIsoCols σ J (initCols X mT) := isIsoCols_of_isWittFrame hW hσ hJ mT.2
  haveI : LocallyCompactSpace (unip σ J X S) := (isClosed_unip S h hJ hW).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : LocallyCompactSpace (unip σ J X T) := (isClosed_unip T h hJ hW).isClosedEmbedding_subtypeVal.locallyCompactSpace
  have hcS : Cocompact (ratPts σ J) (unip σ J X S) := eS ▸ cocompact_unipFlag hJ hσ hCS _
  have hcT : Cocompact (ratPts σ J) (unip σ J X T) := eT ▸ cocompact_unipFlag hJ hσ hCT _
  have hφ' : GlobalTheory.AutomorphicL2Unitary.LeftInv (ratPts σ J) φ := hφ
  have hnorm : ∀ p ∈ unip σ J X S, ∀ u ∈ unip σ J X T, p * u * p⁻¹ ∈ unip σ J X T := fun p hp u hu => by
    rw [eT] at hu ⊢
    exact conj_mem_unipFlag hJ hσ hCT _ (unip_le_parFlag F E σ h n J hJ r X Y hW S T mT hTS hmT hmT' hp) hu
  have h0 : (0 : GAd σ J → ℂ) = constTermOn (ratPts σ J) (unip σ J X T) φ :=
    (isConstTermOn_iff hcT fun γ hγ => hφ γ hγ.1).1 hT
  refine (isConstTermOn_iff hcS fun γ hγ => hφ γ hγ.1).2 (funext fun x => ?_)
  rw [Stages.constTermOn_stages (GAd σ J) (ratPts σ J) (unip σ J X S) (unip σ J X T)
    (unip_mono F E σ h n J hJ r X Y hW S T hTS) hnorm hcS hcT φ hφ' hφc x, ← h0]
  simp [constTermOn]

end GlobalTheory.ConstTrans
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousLeviProjTwo
section
noncomputable section

namespace GlobalTheory.LocRankBig

open GlobalTheory.SmGL GlobalTheory.SplitWeil

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem totallyDisconnected : TotallyDisconnectedSpace k := by
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  haveI : NonarchimedeanAddGroup k := ⟨fun V hV => by
    obtain ⟨s, hs⟩ := GlobalTheory.SplitWeil.exists_cball_subset hV
    exact ⟨⟨⟨⟨⟨GlobalTheory.SplitWeil.cball s, GlobalTheory.SplitWeil.add_mem_cball⟩, by simp [GlobalTheory.SplitWeil.cball]⟩,
      GlobalTheory.SplitWeil.neg_mem_cball⟩, GlobalTheory.SplitWeil.isOpen_cball s⟩, hs⟩⟩
  infer_instance

theorem nonarchimedeanGroup_GL (n : ℕ) : NonarchimedeanGroup (GL (Fin n) k) := by
  haveI := totallyDisconnected (k := k)
  haveI : TotallyDisconnectedSpace (Matrix (Fin n) (Fin n) k) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin n → Fin n → k))
  haveI : TotallyDisconnectedSpace (GL (Fin n) k) :=
    ⟨isTotallyDisconnected_of_image (f := fun g : GL (Fin n) k => g.val) Units.continuous_val.continuousOn
      Units.val_injective (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩
  haveI : CompactSpace (KO k (Fin n)) := isCompact_iff_compactSpace.1 GlobalTheory.SplitFlip.isCompact_KO
  haveI : NonarchimedeanGroup (KO k (Fin n)) := ⟨fun U hU => by
    obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one (isOpen_interior (s := U))
      (mem_interior_iff_mem_nhds.2 hU)
    exact ⟨N.toOpenSubgroup, hN.trans interior_subset⟩⟩
  exact NonarchimedeanGroup.nonarchimedean_of_emb (KO k (Fin n)).subtype
    GlobalTheory.SplitFlip.isOpen_KO.isOpenEmbedding_subtypeVal

@[reducible] def act (k : Type) [Field k] (n x x' : ℕ) :
    MulAction (GL (Fin n) k × parab k (GlobalTheory.ThK.MidJac.e2 x x')) (Matrix (Fin n) (Fin (x + x')) k) where
  smul γ X := (γ.1 : Matrix (Fin n) (Fin n) k) * X *
    Matrix.transpose ((γ.2 : GL (Fin (x + x')) k) : Matrix (Fin (x + x')) (Fin (x + x')) k)
  one_smul X := by
    show ((1 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * X *
      Matrix.transpose ((1 : GL (Fin (x + x')) k) : Matrix (Fin (x + x')) (Fin (x + x')) k) = X
    simp
  mul_smul γ δ X := by
    show ((γ.1 * δ.1 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * X *
      Matrix.transpose ((γ.2.1 * δ.2.1 : GL (Fin (x + x')) k) : Matrix (Fin (x + x')) (Fin (x + x')) k) =
      (γ.1 : Matrix (Fin n) (Fin n) k) * ((δ.1 : Matrix (Fin n) (Fin n) k) * X *
        Matrix.transpose ((δ.2 : GL (Fin (x + x')) k) : Matrix (Fin (x + x')) (Fin (x + x')) k)) *
        Matrix.transpose ((γ.2 : GL (Fin (x + x')) k) : Matrix (Fin (x + x')) (Fin (x + x')) k)
    simp [Matrix.transpose_mul, Matrix.mul_assoc]

def chi (n x x' : ℕ) (α β : kˣ →* ℂˣ) : GL (Fin n) k × parab k (GlobalTheory.ThK.MidJac.e2 x x') →* ℂˣ :=
  ((deltaHalf k _ * GlobalTheory.ThK.DetProd.twoDet x x' α β).comp
      ((leviProj k (GlobalTheory.ThK.MidJac.e2 x x')).comp (MonoidHom.snd _ _))) *
    ((detChar _ (β * absPow k ((-(n : ℝ) / 2 : ℝ) : ℂ)))⁻¹.comp
      ((parab k (GlobalTheory.ThK.MidJac.e2 x x')).subtype.comp (MonoidHom.snd _ _))) *
    ((detChar _ (β * α⁻¹ * absPow k ((-((x + x' : ℕ) : ℝ) / 2 : ℝ) : ℂ)))⁻¹.comp (MonoidHom.fst _ _))

end Local

end GlobalTheory.LocRankBig
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOnDiagValExtTrace
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

noncomputable section

open Set Filter Topology Matrix MeasureTheory
open scoped ContDiff ENNReal ComplexOrder

namespace GlobalTheory

namespace HermFrame

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]

theorem continuousOn_diagVal_extTrace {K : E → Matrix (m ⊕ l) (m ⊕ l) ℂ} {W : Set E}
    (hW : IsOpen W) (hK : ∀ v ∈ W, MContDiffAt ∞ K v) (hp : ∀ v ∈ W, (K v).PosDef) (ξ : E) :
    ContinuousOn (fun v => diagVal (extTrace K v) ξ) W := by
  intro v hv
  refine ContinuousAt.continuousWithinAt ?_
  have he : (fun w => diagVal (extTrace K w) ξ) =ᶠ[𝓝 v]
      fun w => (-Complex.I * (kappa * (secondForm K w ξ * secondFormAdj K w ξ).trace)).re := by
    filter_upwards [hW.mem_nhds hv] with w hw
    rw [diagVal, extTrace_eq ((hK w hw).of_le (by norm_cast))
      (eventually_of_mem (hW.mem_nhds hw) hp)]
  refine ContinuousAt.congr ?_ he.symm
  have hu : IsUnit (K v).det := (hp v hv).det_pos.ne'.isUnit
  have hsu : IsUnit (subGram (K v)).det := (posDef_subGram (hp v hv)).det_pos.ne'.isUnit
  have h0 : MContDiffAt 0 K v := (hK v hv).of_le (by simp)
  have hc : MContDiffAt 0 (fun w => conn K w ξ) v := (hK v hv).conn hu (by simp) ξ
  have hs : MContDiffAt 0 (fun w => secondForm K w ξ) v := fun a b => by
    simp only [secondForm_eq]; exact hc (Sum.inr a) (Sum.inl b)
  have ha : MContDiffAt 0 (fun w => secondFormAdj K w ξ) v :=
    ((h0.subGram.transpose.inv (by rwa [det_transpose])).mul hs.conjTranspose).mul
      (h0.quotGram hsu).transpose
  have hM := hs.mul ha
  have ht : ContinuousAt (fun w => (secondForm K w ξ * secondFormAdj K w ξ).trace) v := by
    simp only [Matrix.trace, Matrix.diag]
    exact (ContDiffAt.sum fun i _ => hM i i).continuousAt
  exact Complex.continuous_re.continuousAt.comp (f := fun w =>
    -Complex.I * (kappa * (secondForm K w ξ * secondFormAdj K w ξ).trace))
    (continuousAt_const.mul (continuousAt_const.mul ht))

end HermFrame

namespace Met

open HermFrame

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}
  {S : ShortComplex X.Modules} {r s : ℕ} {h : Met p σ S.X₂ (r + s)}

theorem bcMeas_finiteAtFilter_nhds [SecondCountableTopology (CxPts p σ)] [T2Space (CxPts p σ)]
    (hS : S.ShortExact) (h₁ : IsVB S.X₁ r) (h₃ : IsVB S.X₃ s) (H : h.IsCInf)
    (c : AlgChart p σ 1) {y : CxPts p σ} (hy : y ∈ c.e.source) :
    (h.bcMeas hS h₁ h₃).FiniteAtFilter (𝓝 y) := by
  obtain ⟨a, ha⟩ := exists_adapted hS h₁ h₃ y
  set W := c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ a.U with hWdef
  have hWo : IsOpen W := ChartGlue.isOpen_over c.e (isOpen_ptsIn a.U)
  have hyW : c.e y ∈ W := ChartGlue.mem_over c.e hy ha
  obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.1 hWo _ hyW
  set B := Metric.closedBall (c.e y) (ε / 2) with hBdef
  have hBW : B ⊆ W := (Metric.closedBall_subset_ball (by linarith)).trans hεW
  have hBt : B ⊆ c.e.target := hBW.trans inter_subset_left
  set K : ReciprocityTheory.L2DbarEstimates.V 1 → Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ :=
    fun v => h.gram a.frame (c.e.symm v) with hKdef
  have hK : ∀ v ∈ W, MContDiffAt ∞ K v := fun v hv => by
    have hz := c.e.map_target hv.1
    have := (H.gram a.frame hv.2).mContDiffAt c hz
    rwa [c.e.right_inv hv.1] at this
  have hp : ∀ v ∈ W, (K v).PosDef := fun v hv => h.posDef_gram_frame hS a hv.2
  have hg := continuousOn_diagVal_extTrace hWo hK hp (EuclideanSpace.single 0 1)
  set T := c.e.symm '' B with hTdef
  have hTc : IsCompact T :=
    (isCompact_closedBall _ _).image_of_continuousOn (c.e.continuousOn_symm.mono hBt)
  have hTs : T ⊆ c.e.source := by
    rintro _ ⟨v, hv, rfl⟩; exact c.e.map_target (hBt hv)
  have hTB : c.e '' T = B := by
    rw [hTdef, Set.image_image]
    exact (Set.image_congr fun v hv => c.e.right_inv (hBt hv)).trans (Set.image_id' B)
  refine ⟨T, ?_, ?_⟩
  · refine mem_of_superset ((c.e.isOpen_inter_preimage Metric.isOpen_ball).mem_nhds
      ⟨hy, Metric.mem_ball_self (half_pos hε)⟩) fun z hz => ⟨c.e z, ?_, c.e.left_inv hz.1⟩
    exact Metric.ball_subset_closedBall hz.2
  · rw [bcMeas_apply hS h₁ h₃ c H hTc.isClosed.measurableSet hTs, hTB]
    have e : ∀ v ∈ B, ENNReal.ofReal (h.bcDens hS h₁ h₃ c (c.e.symm v)) =
        ENNReal.ofReal (2 * diagVal (extTrace K v) (EuclideanSpace.single 0 1)) := fun v hv => by
      rw [bcDens_eq hS h₁ h₃ a c H (c.e.map_target (hBt hv)) (hBW hv).2, bcForm,
        c.e.right_inv (hBt hv)]
    rw [setLIntegral_congr_fun Metric.isClosed_closedBall.measurableSet e]
    exact Integrable.lintegral_lt_top (((continuousOn_const.mul (hg.mono hBW))).integrableOn_compact
      (isCompact_closedBall _ _))

end Met

theorem VMetric.bcFinite_of_curve : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k),
    IsProjOver p → GenSmooth p 1 → ∀ (S : ShortComplex X.Modules) (r s : ℕ)
    (h : VMetric p S.X₂ (r + s)) (hS : S.ShortExact) (h₁ : IsVB S.X₁ r) (h₃ : IsVB S.X₃ s),
    h.IsCInf → h.BcFinite hS h₁ h₃ := by
  intro k _ X p hp hg S r s h hS h₁ h₃ H σ
  have := CxPts.compactSpace σ hp
  have := CxPts.secondCountableTopology_of_isProjOver σ hp
  have := CxPts.t2Space_cxPts_of_isProjOver σ hp
  obtain ⟨R⟩ := hg σ
  refine (isCompact_univ.measure_lt_top_of_nhdsWithin fun y _ => ?_).ne
  obtain ⟨i, hi⟩ := R.cover y
  exact (Met.bcMeas_finiteAtFilter_nhds hS h₁ h₃ (H σ) (R.chart i) hi).filter_mono
    nhdsWithin_le_nhds

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormEqZeroOfWhittakerVanishingStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_form_eq_zero_of_whittaker_vanishing : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (φ : Sm E a), IsCuspForm φ → (∀ g, GlobalTheory.JSW.whit φ.1 g = 0) → φ = 0 := by
  first | exact @GlobalTheory.JSW.eq_zero_of_whit_eq_zero | exact GlobalTheory.JSW.eq_zero_of_whit_eq_zero | (intros; apply GlobalTheory.JSW.eq_zero_of_whit_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormGLSiegelConeDecayOneStep
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GlobalTheory

theorem cuspForm_decay_step : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (ψ : Sm E a), IsCuspForm ψ → ∀ t : ℝ, 0 < t → ∀ i j : Fin a, (j : ℕ) = i + 1 → ∀ (Ω : Set (GL (Fin a) (Cinf E))), IsCompact Ω → ∃ (Ω' : Set (GL (Fin a) (Cinf E))) (B : Finset (Lie E a)) (C : ℝ), IsCompact Ω' ∧ 0 ≤ C ∧ ∀ (r : Fin a → ℝ) (d : GL (Fin a) (Cinf E)), (∀ i, 0 < r i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ)) → ∀ M : ℝ, 0 ≤ M → (∀ Y ∈ B, ∀ c' ∈ Ω', ‖lieD Y ψ.1 (infGL E a (d * c'))‖ ≤ M) → ∀ c ∈ Ω, ‖ψ.1 (infGL E a (d * c))‖ ≤ C * (r j / r i) * M := by
  intro E _ _ _ a ψ hψ t ht i j hij Ω hΩ
  have hL : {k | finRep E a k ψ = ψ} ∈ nhds (1 : GL (Fin a) (Af E)) :=
    hψ.1.level.mem_nhds (by simp)
  obtain ⟨R, hR0, hcov⟩ := GlobalTheory.T.unipotentRadical_adelic_eq_rat_mul_boundedReal_mul_level E a (j : ℕ) _ hL
  obtain ⟨Ω', B, C, hΩ', hC, hvar⟩ := GlobalTheory.T.siegelCone_smooth_variation_along_bounded_unipotent E a t ht i j hij Ω hΩ R hR0
  refine ⟨Ω', B, C, hΩ', hC, fun r d hr hrt hd M hM hY c hc => ?_⟩
  refine GlobalTheory.T.cuspForm_norm_le_of_unipotent_variation E a ψ hψ (j : ℕ) (by omega) j.2 (infGL E a (d * c)) (C * (r j / r i) * M) fun x => ?_
  obtain ⟨ξ, z, k, hk, hz, hx⟩ := hcov x
  have hk' : finRep E a k ψ = ψ := hk
  have e : ψ.1 (unip x * infGL E a (d * c)) = ψ.1 (infGL E a (unip z * (d * c))) := by
    rw [hx, mul_assoc, mul_assoc, ← infGL_comm, ← mul_assoc (infGL E a (unip z)), ← map_mul, hψ.1.left]
    have := congrArg (fun φ : Sm E a => φ.1 (infGL E a (unip z * (d * c)))) hk'
    exact this
  rw [e]
  exact hvar ψ r d hr hrt hd M hM hY c hc z hz

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarDerivCutoffNormSqBoundAnnulus
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory
open Complex ComplexConjugate

theorem wdb_normSq_div {n : ℕ} (ρ : ℝ) (j : Fin n) (z : V n) :
    wdb n j (fun w : V n => (((‖w‖ ^ 2 / ρ ^ 2 : ℝ)) : ℂ)) z = z j / (ρ ^ 2 : ℝ) := by
  have h1 := ((hasStrictFDerivAt_norm_sq z).hasFDerivAt).const_smul ((ρ ^ 2)⁻¹ : ℝ)
  have e : (fun w : V n => ‖w‖ ^ 2 / ρ ^ 2) = fun w => ((ρ ^ 2)⁻¹ : ℝ) • ‖w‖ ^ 2 := by
    funext w; simp [smul_eq_mul, div_eq_inv_mul]
  have hv : HasFDerivAt (fun w : V n => ‖w‖ ^ 2 / ρ ^ 2) (((ρ ^ 2)⁻¹ : ℝ) • (2 • innerSL ℝ z)) z := by
    rw [e]; exact h1
  unfold wdb
  rw [fderiv_ofReal_apply hv.differentiableAt, fderiv_ofReal_apply hv.differentiableAt, hv.fderiv]
  simp only [bas, ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul]
  have hr : ∀ x y : V n, inner ℝ x y = re (inner ℂ x y) := by
    intro x y
    rw [PiLp.inner_apply, PiLp.inner_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [mul_comm]
  rw [hr, hr, inner_smul_right,
    EuclideanSpace.inner_single_right]
  rw [div_eq_mul_inv (z j), ← Complex.ofReal_inv]
  generalize (ρ ^ 2)⁻¹ = r
  apply Complex.ext <;> simp <;> ring

theorem wdb_cutoff_sq_le : ∀ (χ : ℝ → ℝ) (A : ℝ), ContDiff ℝ ∞ χ → (∀ t, 0 ≤ χ t ∧ χ t ≤ 1) → (∀ t, t ≤ 1 / 4 → χ t = 1) → (∀ t, 1 ≤ t → χ t = 0) → (∀ t, |deriv χ t| ≤ A) → ∀ (n : ℕ) (ρ : ℝ), 0 < ρ → ∀ (z : V n) (ξ : Fin n → ℂ), ‖∑ j, wdb n j (fun w => ((χ (‖w‖ ^ 2 / ρ ^ 2) : ℝ) : ℂ)) z * (starRingEnd ℂ) (ξ j)‖ ^ 2 ≤ if ρ / 2 ≤ ‖z‖ ∧ ‖z‖ < ρ then A ^ 2 / ρ ^ 2 * ∑ j, ‖ξ j‖ ^ 2 else 0 := by
  intro χ A hχ h01 h1 h0 hA n ρ hρ z ξ
  have hdχ : Differentiable ℝ χ := hχ.differentiable (by simp)
  have hv : DifferentiableAt ℝ (fun w : V n => ‖w‖ ^ 2 / ρ ^ 2) z :=
    by
    have := (differentiableAt_id (x := z)).norm_sq ℝ
    simpa [div_eq_mul_inv] using this.mul_const ((ρ ^ 2)⁻¹)
  set t := ‖z‖ ^ 2 / ρ ^ 2 with ht
  have hw : ∀ j, wdb n j (fun w => ((χ (‖w‖ ^ 2 / ρ ^ 2) : ℝ) : ℂ)) z =
      ((deriv χ t : ℝ) : ℂ) * (z j / ((ρ ^ 2 : ℝ) : ℂ)) := by
    intro j
    rw [wdb_ofReal_comp (k := χ) (v := fun w : V n => ‖w‖ ^ 2 / ρ ^ 2) (hdχ _) hv,
      wdb_normSq_div]
  simp_rw [hw]
  have hsum : ∑ j, ((deriv χ t : ℝ) : ℂ) * (z j / ((ρ ^ 2 : ℝ) : ℂ)) * (starRingEnd ℂ) (ξ j) =
      ((deriv χ t : ℝ) : ℂ) / ((ρ ^ 2 : ℝ) : ℂ) * ∑ j, z j * (starRingEnd ℂ) (ξ j) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hsum]
  split_ifs with hann
  · have hCS : ‖∑ j, z j * (starRingEnd ℂ) (ξ j)‖ ^ 2 ≤ ‖z‖ ^ 2 * ∑ j, ‖ξ j‖ ^ 2 := by
      calc ‖∑ j, z j * (starRingEnd ℂ) (ξ j)‖ ^ 2 ≤ (∑ j, ‖z j‖ * ‖ξ j‖) ^ 2 := by
            apply pow_le_pow_left₀ (norm_nonneg _)
            refine (norm_sum_le _ _).trans (le_of_eq ?_)
            exact Finset.sum_congr rfl fun j _ => by rw [norm_mul, Complex.norm_conj]
        _ ≤ (∑ j, ‖z j‖ ^ 2) * ∑ j, ‖ξ j‖ ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
        _ = ‖z‖ ^ 2 * ∑ j, ‖ξ j‖ ^ 2 := by rw [EuclideanSpace.norm_sq_eq]
    have hz : ‖z‖ ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hann.2.le 2
    have hS : ‖∑ j, z j * (starRingEnd ℂ) (ξ j)‖ ^ 2 ≤ ρ ^ 2 * ∑ j, ‖ξ j‖ ^ 2 :=
      hCS.trans (mul_le_mul_of_nonneg_right hz (Finset.sum_nonneg fun j _ => by positivity))
    have hd : |deriv χ t| ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hA t) 2
    have hρ2 : (0 : ℝ) < ρ ^ 2 := by positivity
    rw [norm_mul, norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos hρ2, mul_pow, div_pow]
    calc |deriv χ t| ^ 2 / (ρ ^ 2) ^ 2 * ‖∑ j, z j * (starRingEnd ℂ) (ξ j)‖ ^ 2
        ≤ A ^ 2 / (ρ ^ 2) ^ 2 * (ρ ^ 2 * ∑ j, ‖ξ j‖ ^ 2) := by gcongr
      _ = A ^ 2 / ρ ^ 2 * ∑ j, ‖ξ j‖ ^ 2 := by field_simp
  · have hd0 : deriv χ t = 0 := by
      rcases not_and_or.mp hann with h | h
      · push_neg at h
        have ht4 : t ≤ 1 / 4 := by
          rw [ht, div_le_iff₀ (by positivity)]; nlinarith [norm_nonneg z]
        apply IsLocalMax.deriv_eq_zero
        exact Filter.Eventually.of_forall fun s => by rw [h1 t ht4]; exact (h01 s).2
      · push_neg at h
        have ht1 : 1 ≤ t := by
          rw [ht, le_div_iff₀ (by positivity)]; nlinarith
        apply IsLocalMin.deriv_eq_zero
        exact Filter.Eventually.of_forall fun s => by rw [h0 t ht1]; exact (h01 s).1
    rw [hd0]; simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteSeriesModelTraceTermsStatement
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discrete_series_model_trace_terms : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.FlathFactorisation → GlobalTheory.Published.HarishChandraCharacters → GlobalTheory.IndefiniteRowSideFullHecke.PseudoCoefficientSeparation.PseudoCoeffSeparation → ∀ (D : D7) (V : HSp D) (lam : D.what₂.Tau → Fin V.rank → ℤ) (S : D.what₂.Tau → SPar) (M : DSModel V S) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ), IsTestData V lam M T U μa μf μ fa ff → ∀ ν, IsFinMeas V μf ν → ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : GA D V →* (H →L[ℂ] H)), IsIrrUnitary π → ∀ c : ℂ, HasTrace (repOp π μ (tensor D.sp.cm.sig V.gram fa ff)) c → c ≠ 0 → ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (σ : Representation ℂ (GfC V) W), σ.IsIrreducible ∧ IsAdmissible σ ∧ IsCopyFinDS σ M π ⊤ ∧ GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasTrace ν σ (finFn V ff) c := by
  first | exact @GlobalTheory.irrUnitary_trace_ne_zero_copyFinDS | exact GlobalTheory.irrUnitary_trace_ne_zero_copyFinDS | (intros; apply GlobalTheory.irrUnitary_trace_ne_zero_copyFinDS <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalArchimedeanSchwartzFockOperatorStatement
section
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_archimedeanSchwartzFockOperatorSpan : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (P : Submodule ℂ (SInf F κ)),
    FiniteDimensional ℂ P → FiniteDimensional ℂ (GlobalTheory.FockKFin.dStep P) := by
  first | exact @GlobalTheory.FockKFinStep.dStep_finiteDimensional | exact GlobalTheory.FockKFinStep.dStep_finiteDimensional | (intros; apply GlobalTheory.FockKFinStep.dStep_finiteDimensional <;> assumption)
end

