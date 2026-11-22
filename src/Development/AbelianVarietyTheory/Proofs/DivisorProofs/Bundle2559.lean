import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2290
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2376
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0173
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2375
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2404
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2370
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0228
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0647
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2447
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2209
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2213
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightDimensionLogBound
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightParamCoeffSumBound
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightParamCoeffSumLeAtIndex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0833
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2446
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2204
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2251
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0126
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2240
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2179

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VerticalTangentFrameJacobianDetOne
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

theorem GlobalTheory.LogPole.vert_jac_det_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J) (L N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W)) (h : IsCell TF Z U e v W k L N) (K : Type) [Field K] [Algebra c.F K] (z : Sp K ⟶ Y₀ TF.X Z) (hz : ⊤ ≤ z ⁻¹ᵁ W) (P₀ P : FrPt Xo c K) (hU : ⊤ ≤ (frX P₀ ≫ TF.Y.j) ⁻¹ᵁ U.1), z ≫ inc₀ TF.X Z = TF.X.ptY P → GlobalTheory.Frames.FrChg (fun σ => (N σ).map (ev z W hz)) 1 P₀ P → IsBaseFrame TF U e v P₀ hU → ∀ (w : VIx Dw → FrPt Xo c (DualNumber K)) (zw : VIx Dw → (Sp (DualNumber K) ⟶ Y₀ TF.X Z)) (hzw : ∀ b, ⊤ ≤ zw b ⁻¹ᵁ W), (∀ b, IsVert P (Pi.single b.toF (1 : K)) (w b)) → (∀ b, zw b ≫ inc₀ TF.X Z = TF.X.ptY (w b)) → (Matrix.of fun a b : VIx Dw => (ev (zw b) W (hzw b) (cellCoord N a)).snd).det = 1 ∧ ∀ b r, (ev (zw b) W (hzw b) (((toBase TF Z).appLE U.1 W h.2.1).hom r)).snd = 0 := by
  intro E _ _ _ H Dw l Xo c TF Z U n e v hv W k L N h K _ _ z hz P₀ P hU hzP hPG hB w zw hzw hw hzw'
  have key : ∀ b σ', (N σ').map (ev (zw b) W (hzw b)) = GlobalTheory.FlagTan.unip K (Pi.single b.toF (1 : K)) σ' *
      ((N σ').map (ev z W hz)).map (fun r => (TrivSqZeroExt.inl r : DualNumber K)) := by
    intro b σ'
    have hx : frX (w b) ≫ TF.Y.j = zw b ≫ toBase TF Z := by
      rw [toBase, ← Category.assoc, hzw' b]; exact (TF.X.lies_ptY (w b)).1.symm
    have hUx : ⊤ ≤ (zw b ≫ toBase TF Z) ⁻¹ᵁ U.1 := GlobalTheory.FlagMod.le_preimage_map (toBase TF Z) h.2.1 (hzw b)
    have hk : ⊤ ≤ (zw b ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U k := GlobalTheory.FlagMod.le_preimage_map (inc₀ TF.X Z) h.2.2.1 (hzw b)
    have hM : ⊤ ≤ (zw b ≫ toBase TF Z) ⁻¹ᵁ (TF.X.F.M k).U := TF.X.F.inM hk (Category.assoc _ _ _)
    obtain ⟨B, hBl, hBu, hBc⟩ := GlobalTheory.T.bigCell_framedPointVectors_lowerTriangular_eigenbasis E H Dw l Xo c TF Z U n e v hv W k L N h (DualNumber K) (w b) (zw b) (hzw b)
      _ hx hUx (hzw' b)
    have hF := GlobalTheory.T.framedPointVectors_verticalDeformation_eigenbasis E H Dw l Xo c TF U n e v hv K P₀ P hU _ hPG hB (Pi.single b.toF (1 : K)) (w b) _ hx hUx
      (TF.X.F.M k).toMChart hM (hw b)
    have eq : B σ' * (L σ').map (ev (zw b) W (hzw b)) * (N σ').map (ev (zw b) W (hzw b)) =
        GlobalTheory.FlagTan.unip K (Pi.single b.toF (1 : K)) σ' *
          ((N σ').map (ev z W hz)).map (fun r => (TrivSqZeroExt.inl r : DualNumber K)) := by
      refine Matrix.ext fun i j => ?_
      have := GlobalTheory.T.bigCell_eigenbasisCombination_coeff_unique E H Dw l Xo c TF Z U n e v hv W k L N h (DualNumber K) (zw b) (hzw b) _ rfl hUx σ' _ _ _
        (hBc σ' i) (hF σ' i)
      have := congrFun this j
      simpa [Matrix.map_mul, Matrix.mul_assoc] using this
    have hN : ∀ i j, j < i → (N σ').map (ev (zw b) W (hzw b)) i j = 0 := fun i j hij => by
      simp [h.2.2.2.2.2.1 σ' i j hij]
    have hN1 : ∀ i, (N σ').map (ev (zw b) W (hzw b)) i i = 1 := fun i => by simp [h.2.2.2.2.2.2.1 σ' i]
    have hL : ∀ i j, i < j → (L σ').map (ev (zw b) W (hzw b)) i j = 0 := fun i j hij => by
      simp [h.2.2.2.1 σ' i j hij]
    have hN0 : ∀ i j, j < i → ((N σ').map (ev z W hz)).map (fun r => (TrivSqZeroExt.inl r : DualNumber K)) i j = 0 :=
      fun i j hij => by simp [h.2.2.2.2.2.1 σ' i j hij]
    have hN01 : ∀ i, ((N σ').map (ev z W hz)).map (fun r => (TrivSqZeroExt.inl r : DualNumber K)) i i = 1 :=
      fun i => by simp [h.2.2.2.2.2.2.1 σ' i]
    have hbt : ∀ (p q : Fin (Dw.mult σ')), some ⟨σ', (p, q)⟩ = b.toF → p < q := by
      intro p q hpq
      obtain ⟨σb, ⟨⟨i, j⟩, hij⟩⟩ := b
      simp only [GlobalTheory.FlagTan.VIx.toF, Option.some.injEq, Sigma.mk.inj_iff] at hpq
      obtain ⟨rfl, hq⟩ := hpq
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.1 (eq_of_heq hq)
      exact hij
    have hU0 : ∀ i j, j < i → GlobalTheory.FlagTan.unip K (Pi.single b.toF (1 : K)) σ' i j = 0 := fun i j hij => by
      have h1 : (1 : Matrix (Fin (Dw.mult σ')) (Fin (Dw.mult σ')) K) i j = 0 := Matrix.one_apply_ne (ne_of_gt hij)
      have h2 : (Pi.single b.toF (1 : K) : GlobalTheory.FlagTan.FIx Dw → K) (some ⟨σ', (i, j)⟩) = 0 :=
        Pi.single_eq_of_ne (fun hh => absurd (hbt i j hh) (not_lt.2 hij.le)) _
      simp [GlobalTheory.FlagTan.unip, h1, h2]
    have hU1 : ∀ i, GlobalTheory.FlagTan.unip K (Pi.single b.toF (1 : K)) σ' i i = 1 := fun i => by
      have h2 : (Pi.single b.toF (1 : K) : GlobalTheory.FlagTan.FIx Dw → K) (some ⟨σ', (i, i)⟩) = 0 :=
        Pi.single_eq_of_ne (fun hh => absurd (hbt i i hh) (lt_irrefl _)) _
      simp [GlobalTheory.FlagTan.unip, h2]
    exact GlobalTheory.T.lu_decomposition_unitriangular_unique _ _ _ _ _ _ _ (hBl σ') hL hN hN1 hU0 hU1 hN0 hN01 eq
  refine ⟨?_, fun b r => GlobalTheory.T.derivative_basePullback_eq_zero_along_verticalDeformation E H Dw l Xo c TF Z U.1 W h.2.1 K P _ (w b) (zw b) (hzw b) (hw b) (hzw' b) r⟩
  have hM : ∀ σ i j, j < i → (N σ).map (ev z W hz) i j = 0 := fun σ i j hij => by simp [h.2.2.2.2.2.1 σ i j hij]
  have hM1 : ∀ σ i, (N σ).map (ev z W hz) i i = 1 := fun σ i => by simp [h.2.2.2.2.2.2.1 σ i]
  convert GlobalTheory.T.det_bigCellCoordinateJacobian_verticalChanges_eq_one E H Dw K (fun σ => (N σ).map (ev z W hz)) hM hM1 using 2
  refine Matrix.ext fun a b => ?_
  simp only [Matrix.of_apply, cellCoord]
  rw [← key b a.1]
  rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeierstrassModularTransformationLevel
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open GlobalTheory.WpFam

namespace GlobalTheory.WpFam

theorem wB_smul_transform : ∀ (N : ℕ) [NeZero N] (x : Fin 2 → ZMod N) (γ : SL(2, ℤ)) (τ : ℍ), wB N x (γ • τ) = (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) : ℂ) ^ 2 * wB N (vact N x γ) τ - ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) / (2 * Real.pi * Complex.I) := by
  intro N _ x γ τ
  have h := congrFun (EisensteinSeries.G2_slash_action γ) τ
  rw [ModularForm.SL_slash_apply, Pi.sub_apply, EisensteinSeries.D2] at h
  have hj : UpperHalfPlane.denom γ τ ≠ 0 := UpperHalfPlane.denom_ne_zero _ _
  have hd : UpperHalfPlane.denom γ τ = ((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ) := by
    simp [ModularGroup.denom_apply]
  have hG : EisensteinSeries.G2 (γ • τ) = UpperHalfPlane.denom γ τ ^ 2 * EisensteinSeries.G2 τ
      - 2 * Real.pi * Complex.I * ((γ 1 0 : ℤ) : ℂ) * UpperHalfPlane.denom γ τ := by
    rw [zpow_neg, zpow_ofNat] at h
    field_simp at h
    linear_combination h
  have hwp := ((GlobalTheory.QFam.isFam_iff_values _ _ _ _).1 (GlobalTheory.T.weierstrassP_torsion_isModularFamily N).1) x γ τ
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  rw [zpow_ofNat] at hwp
  rw [wB, wB, gN, gN, hwp, hG, hd]
  field_simp
  ring
end GlobalTheory.WpFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightAntitoneBoundaryStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_antitone_boundary : Size → Covers fun Fm x _ ι p i Y PP _ => 1 ≤ (dat p i).p ∧ ∀ la ∈ ({(⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁, (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).ub} : Set (AllWt.Weight (dat p i))), (∀ τ, Antitone (la τ)) ∧ ∀ τ (a b : Fin ((dat p i).p + (dat p i).q)), (a : ℕ) + 1 = (dat p i).p → (b : ℕ) = (dat p i).p → (GlobalTheory.RefSum.nCol (dat p i) : ℤ) + 1 ≤ la τ a - la τ b := by
  first | exact @GlobalTheory.LiftGaps.lift_gaps | exact GlobalTheory.LiftGaps.lift_gaps | (intros; apply GlobalTheory.LiftGaps.lift_gaps <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightDimensionLogBoundStatement
section
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_dimension_log_bound : Lifts fun Fm x _ ι p i _ C => (i : ℕ) + 1 = (Fm.D x ι).R.m → |(ofRecord (Fm.D x ι) (Fm.L x ι) p.Del p.h0).logOm| * (∑ τ : Psi p.T.Q.H, ∑ k, |(laOf (dat p i) (wtA (p.κ i)) (p.κ i).n τ k : ℝ) - (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n ((Fm.D x ι).R.k - 1) τ : ℝ)|) + (∑ τ : Psi p.T.Q.H, Real.log (GlobalTheory.DualWeyl.dim (part (dat p i) (wtA (p.κ i)) τ.1) : ℝ)) + ((p.κ i).n : ℝ) * (Fintype.card (Psi p.T.Q.H) : ℝ) * ((dat p i).p : ℝ) * |GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd (Fm.D x ι).host.E| ≤ C * unitE p := by
  first | exact @GlobalTheory.CovTop.DefSizes.sizes | exact GlobalTheory.CovTop.DefSizes.sizes | (intros; apply GlobalTheory.CovTop.DefSizes.sizes <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightParamCoeffSumBoundStatement
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_param_coeff_sum_bound : Size → Covers fun Fm x _ ι p i Y PP _ => ∀ la ∈ ({(⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁, (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₂} : Set (AllWt.Weight (dat p i))), ∑ τ, ∑ k, |(la τ k : ℝ)| ≤ zBase (Fm.L x ι) ^ 2 * (kap p i / lenT p i PP + 1) := by
  first | exact @GlobalTheory.CovTop.WtSz.wts_le | exact GlobalTheory.CovTop.WtSz.wts_le | (intros; apply GlobalTheory.CovTop.WtSz.wts_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightParamCoeffSumLeAtIndexStatement
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_param_coeff_sum_le_at_index : Size → Covers fun Fm x _ ι p i Y PP _ => ∀ j ≤ lenT p i PP, ∑ τ, ∑ k, |((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt j τ k : ℝ)| ≤ zBase (Fm.L x ι) ^ 2 * kap p i := by
  first | exact @GlobalTheory.CovTop.WtRun.wt_size | exact GlobalTheory.CovTop.WtRun.wt_size | (intros; apply GlobalTheory.CovTop.WtRun.wt_size <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightParameterStrictAntitone
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
namespace GlobalTheory.QuoWt

theorem dominance : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H) (P : WtPar Dw),
    0 ≤ P.c₀ → 2 * (Dw.p + Dw.q) + CompHt.dimFlag Dw ≤ P.T →
    (∀ (τ : Psi H) (a b : Fin (Dw.p + Dw.q)), (b : ℕ) = a + 1 →
      ((b : ℕ) ≠ Dw.p → ((P.T : ℤ) + CompHt.dimFlag Dw + 2) * ((P.T : ℤ) + CompHt.dimFlag Dw + 2 + 2 * ((Dw.p + Dw.q : ℕ) : ℤ)) ≤
        P.u τ a - P.u τ b + 2) ∧
      ((b : ℕ) = Dw.p → ((P.T : ℤ) + P.c₀) * ((P.T : ℤ) + CompHt.dimFlag Dw + 1) + P.c₀ + 2 * ((Dw.p + Dw.q : ℕ) : ℤ) - 2 ≤
        P.u τ a - P.u τ b)) →
    ∀ s : ℕ, s ≤ 3 → ∀ τ : Psi H, Antitone (P.uMinus τ + (s * P.c₀) • hodgeWt Dw τ) ∧
      Antitone (((P.T + CompHt.dimFlag Dw + (if s = 0 then 3 else 4) : ℕ) : ℤ) • P.u₁ τ - (P.uMinus τ + (s * P.c₀) • hodgeWt Dw τ)) := GlobalTheory.T.shifted_weights_dominant_of_gaps

theorem arith : ∀ (T D c0 h0 N f m k PP : ℝ), 4 * D + 4 ≤ T → 4 * T ^ 2 ≤ h0 → PP * T * N * f ^ 2 * m ^ 2 * k * D ≤ h0 →
    4 * (c0 + 2 * N + T + D + 1) ≤ h0 → 0 ≤ c0 → c0 ≤ 22 * f ^ 2 * N ^ 4 → D = f * (N * (N - 1) / 2) → 40 ≤ PP →
    N + 4 ≤ 2 * k → 2 ≤ m → 6 ≤ N → 8 ≤ f →
    (T + c0) * (T + D + 1) + c0 + 2 * N - 2 ≤ h0 ∧ 2 * N + D ≤ T := GlobalTheory.T.bar_gap_parameter_inequality

theorem isQuot_u₁ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)
    (P : WtPar Dw) (kc : ℕ) (hk : P.a + 1 = kc) : IsQuot Dw kc P.T P.c₀ P.u P.u₁ := by
  intro τ
  refine ⟨fun a (ha : (a : ℕ) + 1 = kc) => (P.anchored τ (by omega)).1, fun a b hb => ?_⟩
  have hb' : (a : ℕ) + 1 < Dw.p + Dw.q := hb ▸ b.2
  show P.u₁ τ a - P.u₁ τ b = (P.u τ a - P.u τ b + if (b : ℕ) = Dw.p then -P.c₀ - (2 * ((Dw.p + Dw.q : ℕ) : ℤ) - 2) else 2) /
    ((P.T : ℤ) + CompHt.dimFlag Dw + 1)
  rw [← CompHS.gap_eq (P.u₁ τ) hb, P.gap_u₁ τ hb', P.gap_uMinus_sub_kap τ hb', CompHS.gap_eq (P.u τ) hb, hb,
    WtPar.T₁, dimFlag_eq]

theorem quo_unique {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)
    (P : WtPar Dw) (kc : ℕ) (hk : P.a + 1 = kc) (hN : kc ≤ Dw.p + Dw.q) (u1 : AllWt.Weight Dw)
    (hq : IsQuot Dw kc P.T P.c₀ P.u u1) : u1 = P.u₁ :=
  GlobalTheory.MeanTop.Inhab.dividedWeight_unique _ u1 (by show 1 ≤ kc; omega) hN (isQuot_u₁ Dw P kc hk) hq

section Pt

open IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

theorem atPoint (PP A M : ℝ) (hi : (i : ℕ) + 1 < D.R.m) (hw : WtNum p i PP) (hh : HostNum D L PP A M) :
    1 ≤ (dat p i).p ∧ 1 ≤ (dat p i).q ∧ 2 < Module.finrank ℚ D.host.E / 2 ∧ (∀ u1, Quo p i PP u1 → u1 = (⟨uW p i, cZero D ((i : ℕ) + 1), D.R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁) ∧ (∀ τ, StrictAnti ((⟨uW p i, cZero D ((i : ℕ) + 1), D.R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ τ) ∧ StrictAnti (CompHt.uPrime (dat p i) (⟨uW p i, cZero D ((i : ℕ) + 1), D.R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ τ)) ∧ (∃ w : Psi p.T.Q.H → ℤ, (∀ τ, |w τ| ≤ 3 * (D.R.r : ℤ)) ∧ uM p i = (⟨uW p i, cZero D ((i : ℕ) + 1), D.R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt (lenT p i PP) + GlobalTheory.FlatLine.parWt (dat p i) w) ∧ ∀ s : ℕ, s ≤ 3 → ∀ τ, Antitone (uM p i τ + (s * cZero D ((i : ℕ) + 1)) • hodgeWt (dat p i) τ) ∧ Antitone (((lenT p i PP + CompHt.dimFlag (dat p i) + (if s = 0 then 3 else 4) : ℕ) : ℤ) • (⟨uW p i, cZero D ((i : ℕ) + 1), D.R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ τ - (uM p i τ + (s * cZero D ((i : ℕ) + 1)) • hodgeWt (dat p i) τ)) := by
  obtain ⟨⟨s1, s2, s3⟩, -, hdim, -, -, -, -, -, -, -, hyp⟩ := hw
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have ep : (dat p i).p = D.R.k + i := by rw [s1]; unfold Ranks.sigW; omega
  have eq : (dat p i).q = D.R.m - ((i : ℕ) + 1) := by rw [s2]; rfl
  have er : (dat p i).p + (dat p i).q = D.R.r := s3
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  set P : WtPar (dat p i) := ⟨uW p i, cZero D ((i : ℕ) + 1), D.R.k - 2, lenT p i PP⟩ with hP
  have hPa : P.a + 1 = D.R.k - 1 := by show D.R.k - 2 + 1 = D.R.k - 1; omega
  have hquo : Quo p i PP P.u₁ := GlobalTheory.QuoWt.isQuot_u₁ (dat p i) P (D.R.k - 1) hPa
  obtain ⟨h0, S, eta, -, -, -, hT2, hrow, hH⟩ := hyp hi
  have hW := hH P.u₁
  have hdiv := (quo_iff p i PP h0 S eta P.u₁).1 hquo
  have ha : D.R.k - 2 < (dat p i).p + (dat p i).q := by omega
  refine ⟨by omega, by omega, ?_, fun u1 hu => GlobalTheory.QuoWt.quo_unique (dat p i) P _ hPa (by omega) u1 hu, fun τ => ?_, ?_, ?_⟩
  · have := hh.deg
    have := hh.f8
    omega
  · obtain ⟨a1, a2, -⟩ := GlobalTheory.MeanTop.divided_strictAnti _ _ _ hW hdiv τ
    refine ⟨a1, ?_⟩
    convert a2 using 1
    funext j
    simp only [CompHt.uPrime, hodgeWt, CompHt.barWt, GlobalTheory.MeanTop.Wts.u', wtsAt, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    by_cases h : (j : ℕ) < (dat p i).p <;> simp [h] <;> ring
  · refine ⟨fun τ => -(FlagTan.kap (dat p i) τ ⟨D.R.k - 2, ha⟩), fun τ => ?_, ?_⟩
    · simp only [FlagTan.kap]
      rw [if_pos (by show D.R.k - 2 < (dat p i).p; omega), ep, eq, hr, abs_le]
      constructor <;> push_cast <;> omega
    · funext τ j
      have e := P.uMinus_eq τ (a := ⟨D.R.k - 2, ha⟩) rfl j
      have e1 : P.u τ ⟨D.R.k - 2, ha⟩ = 0 :=
        uWt_anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ ⟨D.R.k - 2, ha⟩ (by show D.R.k - 2 + 1 = D.R.k - 1; omega)
      have e0 : P.uMinus τ ⟨D.R.k - 2, ha⟩ = 0 := by
        simp only [WtPar.uMinus, Pi.sub_apply, Pi.smul_apply, hodgeWt, CompHt.barWt, smul_eq_mul, e1]
        rw [if_pos (by show D.R.k - 2 < (dat p i).p; omega)]
        ring
      show P.uMinus τ j = P.wt P.T τ j + GlobalTheory.FlatLine.parWt (dat p i) _ τ j
      rw [e, e0]
      simp [GlobalTheory.FlatLine.parWt, sub_eq_add_neg]
  · intro s hs τ
    have hc := cZero_spec D ((i : ℕ) + 1)
    have hf8 := hh.f8
    have hL := hh.big.2.1
    have hZ : (40 : ℝ) ≤ zBase L := by
      unfold zBase
      have a1 : (8 : ℝ) ≤ D.R.f := by exact_mod_cast hf8
      have a2 : (6 : ℝ) ≤ D.R.r := by exact_mod_cast (show 6 ≤ D.R.r by omega)
      have a3 : (48 : ℝ) ≤ D.R.f * D.R.r := by nlinarith
      have a4 : (10 : ℝ) ≤ L.sc.L := hL
      nlinarith
    have hPP : (40 : ℝ) ≤ PP := hZ.trans ((le_self_pow₀ (by linarith) (by norm_num)).trans hh.ppLow)
    have hD : ((CompHt.dimFlag (dat p i) : ℕ) : ℝ) = (D.R.f : ℝ) * ((D.R.r : ℝ) * ((D.R.r : ℝ) - 1) / 2) := by
      rw [hdim]; push_cast [Nat.cast_choose_two]; ring
    have hh1 : 4 * CompHt.dimFlag (dat p i) + 4 ≤ lenT p i PP := hW.h1
    have hh2 : 4 * (cZero D ((i : ℕ) + 1) + 2 * ((D.R.r : ℕ) : ℤ) + lenT p i PP + CompHt.dimFlag (dat p i) + 1) ≤ h0 := by
      have := hW.h2.1
      change 4 * (cZero D ((i : ℕ) + 1) + 2 * (((dat p i).p + (dat p i).q : ℕ) : ℤ) + (lenT p i PP : ℤ) +
        (CompHt.dimFlag (dat p i) : ℤ) + 1) ≤ h0 at this
      rw [er] at this; exact this
    obtain ⟨r1, r2⟩ := GlobalTheory.QuoWt.arith (lenT p i PP : ℝ) (CompHt.dimFlag (dat p i) : ℝ) (cZero D ((i : ℕ) + 1) : ℝ) (h0 : ℝ)
      (D.R.r : ℝ) (D.R.f : ℝ) (D.R.m : ℝ) (D.R.k : ℝ) PP (by exact_mod_cast hh1) (by exact_mod_cast hT2) hrow
      (by exact_mod_cast hh2) (by exact_mod_cast hc.2.1) (by exact_mod_cast hc.2.2) hD hPP
      (by exact_mod_cast (show D.R.r + 4 ≤ 2 * D.R.k by omega)) (by exact_mod_cast hm)
      (by exact_mod_cast (show 6 ≤ D.R.r by omega)) (by exact_mod_cast hf8)
    have hbar : ((P.T : ℤ) + P.c₀) * ((P.T : ℤ) + CompHt.dimFlag (dat p i) + 1) + P.c₀ +
        2 * (((dat p i).p + (dat p i).q : ℕ) : ℤ) - 2 ≤ h0 := by
      rw [er]; exact_mod_cast r1
    have hTD : 2 * ((dat p i).p + (dat p i).q) + CompHt.dimFlag (dat p i) ≤ P.T := by
      rw [er]; exact_mod_cast r2
    exact GlobalTheory.QuoWt.dominance (dat p i) P hW.weightConst_nonneg hTD
      (fun τ a b hab => ⟨fun hb => (hW.h4 τ a b hab).1 hb, fun hb => hbar.trans ((hW.h4 τ a b hab).2.2 hb)⟩) s hs τ

end Pt

theorem weights_at_point : Size → Lifts fun Fm x _ ι p i PP _ => (i : ℕ) + 1 < (Fm.D x ι).R.m → 1 ≤ (dat p i).p ∧ 1 ≤ (dat p i).q ∧ 2 < Module.finrank ℚ (Fm.D x ι).host.E / 2 ∧ (∀ u1, Quo p i PP u1 → u1 = (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁) ∧ (∀ τ, StrictAnti ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ τ) ∧ StrictAnti (CompHt.uPrime (dat p i) (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ τ)) ∧ (∃ w : Psi p.T.Q.H → ℤ, (∀ τ, |w τ| ≤ 3 * ((Fm.D x ι).R.r : ℤ)) ∧ uM p i = (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt (lenT p i PP) + GlobalTheory.FlatLine.parWt (dat p i) w) ∧ ∀ s : ℕ, s ≤ 3 → ∀ τ, Antitone (uM p i τ + (s * cZero (Fm.D x ι) ((i : ℕ) + 1)) • hodgeWt (dat p i) τ) ∧ Antitone (((lenT p i PP + CompHt.dimFlag (dat p i) + (if s = 0 then 3 else 4) : ℕ) : ℤ) • (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ τ - (uM p i τ + (s * cZero (Fm.D x ι) ((i : ℕ) + 1)) • hodgeWt (dat p i) τ)) := by
  intro _
  have hw : WtN := GlobalTheory.T.weight_bound_holds
  have hh : HostN 1 := GlobalTheory.CovTop.Sizes.hostN 1
  unfold WtN Lifts at hw
  unfold HostN Lifts at hh
  unfold Lifts
  refine Closed.imp (Closed.and hw hh) ?_
  intro eps Fm CH _ h
  obtain ⟨⟨C1, -, x1, h1⟩, ⟨C2, -, x2, h2⟩⟩ := h
  refine ⟨0, le_rfl, max x1 x2, fun x hx hle ι p hp i hi => ?_⟩
  exact atPoint p i _ _ _ hi (h1 x hx ((le_max_left _ _).trans hle) ι p hp i)
    (h2 x hx ((le_max_right _ _).trans hle) ι p hp i)

end GlobalTheory.QuoWt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WtChar
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.GSum

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
  {X₁ : Setup F W i} {ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}

open Classical in

def base (X₁ : Setup F W i) (z₁ : X₁.M.Z) : X₁.S.Gam :=
  if h : (X₁.S.supI X₁.M z₁).Nonempty then h.some else 0

def wtChar (D : Deep X₁ ε₁) (T : AddSubgroup D.X.S.Gam) (a : D.X.S.Gam) : T →+ ZMod D.X.S.N where
  toFun t := ZMod.castHom (dvd_mul_left D.X.S.N D.X.S.r) (ZMod D.X.S.N) (eStd D.X.S.g _ (t : D.X.S.Gam) (D.m • a))
  map_zero' := by simp [eStd]
  map_add' := by
    intro s t
    rw [← map_add]
    congr 1
    simp only [eStd, AddSubgroup.coe_add, Pi.add_apply, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring

open Classical in

def lift (D : Deep X₁ ε₁) (z₂ : D.X.M.Z) (κ : X₁.S.Gam) : D.X.S.Gam :=
  if h : ∃ h' ∈ D.X.S.HH D.X.M z₂, D.m • h' = D.lab κ then h.choose else 0

def part (D : Deep X₁ ε₁) (z₁ : X₁.M.Z) (z₂ : D.X.M.Z) (a : D.X.S.Gam) (κ : X₁.S.HH X₁.M z₁) : D.X.Ω₁ :=
  (∑ j, algebraMap D.X.o₁ D.X.Ω₁ (D.X.S.proj (D.X.S.TT D.X.M z₂) (wtChar D _ a) j D.X.ρ.i₀) *
      D.X.S.ev (lift D z₂ (κ : X₁.S.Gam)) j) / D.X.S.th (D.lab (base X₁ z₁))

end GlobalTheory.Poinc.GSum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZariskiDescentDvrTraceLocalisationStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
open Polynomial

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zariski_descent_dvr_trace_localisation : ∀ (K L : Type) [Field K] [Field L] (φ : K →+* L) (c : ℂ →+* K), (letI := φ.toAlgebra; FiniteDimensional K L) → ∀ (V : ValuationSubring L) [IsDiscreteValuationRing V] (hc : ∀ a, φ (c a) ∈ V) (t : Finset L), (∀ x ∈ t, x ∈ V ∧ ∃ p : K[X], p.Monic ∧ (∀ i, p.coeff i ∈ V.comap φ) ∧ p.eval₂ φ x = 0) → (∀ s ∈ V, ∃ b ∈ Subring.closure (Set.range (φ.comp c) ∪ ↑t), ∃ d ∈ Subring.closure (Set.range (φ.comp c) ∪ ↑t), d ≠ 0 ∧ d⁻¹ ∈ V ∧ s = b / d) → (c.codRestrict (V.comap φ) hc).EssFiniteType := by
  first | exact @GlobalTheory.zariski_descent_heart | exact GlobalTheory.zariski_descent_heart | (intros; apply GlobalTheory.zariski_descent_heart <;> assumption)
end

