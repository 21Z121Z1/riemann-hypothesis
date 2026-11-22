import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1359
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1758
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.AdelicConjTransposeBlockMatrixTwoByTwoFin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixTwoByTwoFinTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1780
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumUnderAdelicPairModulusOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpanRationalTranslatesVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1679
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1416
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1779
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1451
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1449
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1650
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1788
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1473
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1371
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0348
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0924
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0923
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1791

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetSumEqSumCellSum
section
noncomputable section

open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SiegelCells

variable {D : D7} {n : ℕ}

def lastDiag (R : Type) [Zero R] [One R] (n j : ℕ) : Matrix (Fin n) (Fin n) R :=
  Matrix.diagonal fun i => if n - j ≤ i.val then 1 else 0

def wMat (R : Type) [Ring R] (n j : ℕ) : Matrix (Fin (n + n)) (Fin (n + n)) R :=
  StdUnn.blk4 (1 - lastDiag R n j) (lastDiag R n j) (-lastDiag R n j) (1 - lastDiag R n j)

theorem lastDiag_mul_self (R : Type) [Ring R] (n j : ℕ) : lastDiag R n j * lastDiag R n j = lastDiag R n j := by
  simp only [lastDiag, Matrix.diagonal_mul_diagonal]
  congr 1; funext i; split_ifs <;> simp

theorem lastDiag_mul_one_sub (R : Type) [Ring R] (n j : ℕ) : lastDiag R n j * (1 - lastDiag R n j) = 0 := by
  rw [Matrix.mul_sub, Matrix.mul_one, lastDiag_mul_self, sub_self]

theorem one_sub_mul_lastDiag (R : Type) [Ring R] (n j : ℕ) : (1 - lastDiag R n j) * lastDiag R n j = 0 := by
  rw [Matrix.sub_mul, Matrix.one_mul, lastDiag_mul_self, sub_self]

theorem adj_lastDiag {j : ℕ} : adj (lastDiag (AE D) n j) = lastDiag (AE D) n j := by
  ext i k
  simp only [adj, lastDiag, Matrix.transpose_apply, Matrix.map_apply, Matrix.diagonal_apply]
  by_cases h : k = i
  · subst h; split_ifs <;> simp
  · simp [h, Ne.symm h]

theorem wMat_key {R : Type} [CommRing R] {n : ℕ} (L : Matrix (Fin n) (Fin n) R) (h : L * L = L) :
    StdUnn.blk4 (1 - L) (-L) L (1 - L) * StdUnn.blk4 0 1 (-1) 0 * StdUnn.blk4 (1 - L) L (-L) (1 - L) =
      StdUnn.blk4 0 1 (-1) 0 := by
  rw [StdUnn.Model.submatrix_fromBlocks_mul, StdUnn.Model.submatrix_fromBlocks_mul]
  have h1 : (1 - L) * (1 - L) = 1 - L := by rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, h, sub_self, sub_zero]
  have h2 : L * (1 - L) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, h, sub_self]
  have h3 : (1 - L) * L = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, h, sub_self]
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_neg, Matrix.neg_mul, neg_neg,
    add_zero, zero_add]
  congr 1
  · simp only [Matrix.add_mul, Matrix.neg_mul, Matrix.mul_neg, h2, h3, neg_zero, add_zero]
  · simp only [Matrix.add_mul, Matrix.neg_mul, Matrix.mul_neg, neg_neg, h, h1, h2, h3]; abel
  · rw [h1, h]; abel
  · rw [h2, h3]; simp

theorem exists_wPart (j : ℕ) : ∃ g : StdUnn.G D n, StdUnn.mat g = wMat (AE D) n j := by
  have e1 := lastDiag_mul_self (AE D) n j
  have e2 := lastDiag_mul_one_sub (AE D) n j
  have e3 := one_sub_mul_lastDiag (AE D) n j
  have e4 : (1 - lastDiag (AE D) n j) * (1 - lastDiag (AE D) n j) = 1 - lastDiag (AE D) n j := by
    rw [Matrix.sub_mul, Matrix.one_mul, e2, sub_zero]
  refine StdUnn.Model.exists_mat _ (StdUnn.blk4 (1 - lastDiag (AE D) n j) (-lastDiag (AE D) n j) (lastDiag (AE D) n j)
    (1 - lastDiag (AE D) n j)) ?_ ?_ ?_
  · simp only [wMat, StdUnn.Model.submatrix_fromBlocks_mul, e1, e2, e3, e4, Matrix.mul_neg, Matrix.neg_mul, neg_neg]
    rw [← StdUnn.Model.block_matrix_one]; congr 1 <;> abel
  · simp only [wMat, StdUnn.Model.submatrix_fromBlocks_mul, e1, e2, e3, e4, Matrix.mul_neg, Matrix.neg_mul, neg_neg]
    rw [← StdUnn.Model.block_matrix_one]; congr 1 <;> abel
  · have ha : adj (wMat (AE D) n j) = StdUnn.blk4 (1 - lastDiag (AE D) n j) (-lastDiag (AE D) n j) (lastDiag (AE D) n j)
        (1 - lastDiag (AE D) n j) := by
      rw [wMat, StdUnn.Model.adelicConjTranspose_blockMatrixTwoByTwoFin, adj_sub, adj_one, adj_neg, adj_lastDiag]
    rw [ha]
    exact wMat_key _ e1

variable (D n) in

def wPart (j : ℕ) : StdUnn.G D n := (exists_wPart (D := D) (n := n) j).choose

variable (D n) in

def hermJ (j : ℕ) : AddSubgroup (Mx D n n) where
  carrier := {b | adj b = b ∧ ∀ i k : Fin n, (i.val < n - j ∨ k.val < n - j) → b i k = 0}
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨by rw [adj_add, ha, hb], fun i k h => ?_⟩
    simp [ha' i k h, hb' i k h]
  zero_mem' := ⟨adj_zero, fun _ _ _ => rfl⟩
  neg_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨by rw [adj_neg, ha], fun i k h => ?_⟩
    simp [ha' i k h]

variable (D n) in

def ratHermJ (j : ℕ) : AddSubgroup (hermJ D n j) := (ratMx D n n).addSubgroupOf (hermJ D n j)

def nPart {j : ℕ} (b : hermJ D n j) : StdUnn.G D n := GlobalTheory.ResAniso.nElt ⟨b.1, b.2.1⟩

variable (D n) in

def firstSpan (j : ℕ) : Submodule D.host.E (Fin n → D.host.E) :=
  LinearMap.ker (LinearMap.funLeft D.host.E D.host.E (Subtype.val : {i : Fin n // n - j ≤ i.val} → Fin n))

variable (D n) in

def Qpar (j : ℕ) : Subgroup (GL (Fin n) D.host.E) := Formalism.UG.stabGL (firstSpan D n j)

def mRat (a : GL (Fin n) D.host.E) : StdUnn.G D n :=
  (StdUnn.Model.exists_levi (Matrix.GeneralLinearGroup.map (incA D) a)).choose

def intwJ (j : ℕ) (db : Measure (hermJ D n j)) (f : StdUnn.G D n → ℂ) (g : StdUnn.G D n) : ℂ :=
  ∫ b, f (wPart D n j * nPart b * g) ∂db

def eisJ (j : ℕ) (db : Measure (hermJ D n j)) (f : StdUnn.G D n → ℂ) (g : StdUnn.G D n) : ℂ :=
  cosetSum (Qpar D n j) ⊤ (fun a => intwJ j db f (mRat a * g)) 1

def lowerRank (γ : StdUnn.G D n) : ℕ :=
  if h : ∃ M : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E, rat M = StdUnn.mat γ then
    ((h.choose.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁).rank else 0

def cellSum (j : ℕ) (f : StdUnn.G D n → ℂ) (g : StdUnn.G D n) : ℂ :=
  ∑' q : Cosets (StdUnn.P D n) (StdUnn.GF D n),
    if lowerRank ((q.out : StdUnn.GF D n) : StdUnn.G D n) = j then term (StdUnn.P D n) (StdUnn.GF D n) f g q else 0

end GlobalTheory.SiegelCells

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVecMemThetaSpaceStatement
section
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField Polynomial
open scoped Pointwise nonZeroDivisors
open Formalism.L2.Host (HChar embTau)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cosetVec_mem_theta_space : ∀ {D : D7} {δ t0 : ℂ} {Q : ℕ} (P : Pair D ⊤ δ t0 Q) {𝔪 : Ideal (𝓞 D.host.E)}, 𝔪 ≠ ⊥ → ∀ o : ℕ, cosetVec P 𝔪 o ∈ TT D (tor0 D ⊤ δ) P.a P.d := by
  first | exact @GlobalTheory.FunObj.CosetTheta.cosetVec_mem_TT | exact GlobalTheory.FunObj.CosetTheta.cosetVec_mem_TT | (intros; apply GlobalTheory.FunObj.CosetTheta.cosetVec_mem_TT <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspRapidDecaySiegelGLOfFinite
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GlobalTheory

theorem cuspRapidDecaySiegelGL_of_finite (hfin : GlobalTheory.Published.AutomorphicFormsFiniteGL) :
    GlobalTheory.Published.CuspRapidDecaySiegelGL := by
  intro E _ _ _ a φ hφ ω hω hωB _ t ht lam
  obtain ⟨Ω, Kf, hΩ, hKf, hgeom⟩ := GlobalTheory.T.siegelSet_adelicGL_exists_compact_decomposition E a ω hω hωB t ht
  obtain ⟨S, hS⟩ := GlobalTheory.T.finite_translates_smoothFunction_of_compact E a φ hφ.1.level Kf hKf
  have hcore := fun f' : GL (Fin a) (Af E) =>
    GlobalTheory.T.cuspForm_rapidDecay_siegelCone_realPoints hfin E a (finRep E a f' φ) (GlobalTheory.T.isCuspForm_operator_act hfin E a (.fin f') φ hφ) Ω hΩ t ht lam
  choose C hC0 hC using hcore
  refine ⟨∑ f' ∈ S, C f', fun b hb r hr hchain hprod k hk => ?_⟩
  obtain ⟨d, hd, hdiag⟩ := GlobalTheory.T.exists_realDiagonal_infGL_eq_positiveIdeleDiagonal E a r hr
  rw [hdiag]
  obtain ⟨c, hc, f, hf, heq⟩ := hgeom r d hr hchain hd b hb k hk
  rw [heq]
  obtain ⟨f', hf', hff'⟩ := hS f hf
  have e : φ.1 (infGL E a (d * c) * finGL E a f) = (finRep E a f' φ).1 (infGL E a (d * c)) := by
    rw [← hff']; rfl
  rw [e]
  refine (hC f' r d hr hchain hd hprod c hc).trans ?_
  exact mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun i _ => hC0 i) hf')
    (Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hr i).le _)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalRepEndomorphismScalarSchurStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.ResW GlobalTheory.Published
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidalRep_endomorphism_scalar_schur : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (x : CuspSub E a) (f : x.V →ₗ[ℂ] x.V), (∀ o φ, f (x.op o φ) = x.op o (f φ)) → ∃ c : ℂ, ∀ φ, f φ = c • φ := by
  first | exact @GlobalTheory.CuspSchur.schur | exact GlobalTheory.CuspSchur.schur | (intros; apply GlobalTheory.CuspSchur.schur <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalTraceMultiplicityGiven
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

noncomputable section

namespace GlobalTheory.MultEqTrace

def conjEquiv {G H W : Type} [Group G] [Group H] [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ G W)
    (Φ Φ₀ : G ≃* H) (b : G) (hb : ∀ g, Φ g = Φ₀ (b * g * b⁻¹)) :
    Representation.Equiv (σ.comp Φ.symm.toMonoidHom : Representation ℂ H W)
      (σ.comp Φ₀.symm.toMonoidHom : Representation ℂ H W) :=
  Representation.Equiv.mk
    (LinearEquiv.ofLinear (σ b) (σ b⁻¹) (by rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl)
      (by rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]; rfl))
    fun h => by
      have e : Φ.symm h = b⁻¹ * Φ₀.symm h * b := by
        apply Φ.injective
        rw [Φ.apply_symm_apply, hb]
        simp [mul_assoc]
      ext x
      simp only [LinearMap.coe_comp, Function.comp_apply, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom,
        LinearEquiv.coe_coe, LinearEquiv.ofLinear_apply, e]
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      congr 2
      group

theorem multEq_of_trCusp : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.DixmierMalliavinFactorisation → GlobalTheory.Published.GreenCuspidal → TRCusp → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → GlobalTheory.CuspMult.MultEq R := by
  intro hRD hHC hDM hGC hTR D G _ _ Pl0 T A Ks _ _ _ R F hG
  intro i M₀ j Φ hΦ W _ _ σ hirr hadm hgood
  obtain ⟨Ty, hNF, hTV⟩ := GlobalTheory.T.exists_typeVector_of_good_level_representation hGC R F hG W σ hadm hgood
  obtain ⟨jl, Φ₀, b, hjl, hΦ₀, hb⟩ := GlobalTheory.T.exists_localIsometries_innerAut_adelicFrameIsometry R F hG i j Φ hΦ
  obtain ⟨hr, lam, hodd, hgap, hM₀, hMW⟩ := GlobalTheory.T.discrete_series_odd_rank_gap R F hG i M₀
  have hinf : IsInfFam R.θ := hG.core.models.inf
  let μ : Measure (GA D (Yc D 0)) := Measure.haar
  let μ' : Measure (GA D (Wc D i)) := Measure.haar
  haveI : μ.IsMulRightInvariant := GlobalTheory.T.isMulRightInvariant_haar_adelicUnitaryGroup_hermitianSpace D _ μ inferInstance
  haveI : μ'.IsMulRightInvariant := GlobalTheory.T.isMulRightInvariant_haar_adelicUnitaryGroup_hermitianSpace D _ μ' inferInstance
  have hadm' : IsAdmissible (σ.comp Φ.symm.toMulEquiv.toMonoidHom) :=
    GlobalTheory.CuspMult.isAdmissible_comp_equiv σ Φ.symm hadm
  rw [GlobalTheory.T.cuspidalMultiplicity_eq_discreteSeriesModel_maps hRD hHC hDM D R.θ hinf (Yc D 0) _ M₀ μ W σ hadm.1,
    GlobalTheory.T.cuspidalMultiplicity_eq_discreteSeriesModel_maps hRD hHC hDM D R.θ hinf (Wc D i) _ (R.MW i (sg0 D A)) μ' W _ hadm'.1,
    hTR D (Yc D 0) lam _ M₀ Ty hodd hgap hM₀ hNF (Wc D i) hr _ (R.MW i (sg0 D A)) hMW jl hjl Φ₀ hΦ₀ μ μ' W σ hirr hadm hTV]
  exact ((mDS_congr (GlobalTheory.MultEqTrace.conjEquiv σ Φ.toMulEquiv Φ₀.toMulEquiv b hb)).2).symm

end GlobalTheory.MultEqTrace
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxBasisAdaptedCoordinates
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.MixModel GlobalTheory.SWLit
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (UA incM ratU)
open GlobalTheory.WeilM (Darboux symp schA thetaSum UG)
open GlobalTheory.SiegelFormula (coord)
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SWLink

namespace GlobalTheory.SWLink.Darb

section General

variable {F E A ι : Type} [Field F] [Field E] [Algebra F E] [CommRing A] [Algebra F A] [FiniteDimensional F E]

theorem trace_one_tmul (z : E) :
    Algebra.trace A (A ⊗[F] E) (1 ⊗ₜ z) = algebraMap F A (Algebra.trace F E z) := by
  rw [Algebra.trace_apply, Algebra.trace_apply, ← LinearMap.trace_baseChange]
  congr 1
  ext y
  simp

theorem sum_repr_dual [Algebra.IsSeparable F E] [Fintype ι] [DecidableEq ι] (ε : Module.Basis ι F E) (a b : A ⊗[F] E) :
    ∑ k, (Algebra.TensorProduct.basis A ε).repr a k * (Algebra.TensorProduct.basis A ε.traceDual).repr b k =
      Algebra.trace A (A ⊗[F] E) (a * b) := by
  conv_rhs => rw [← (Algebra.TensorProduct.basis A ε).sum_repr a, ← (Algebra.TensorProduct.basis A ε.traceDual).sum_repr b,
    Finset.sum_mul_sum]
  simp only [map_sum, smul_mul_smul_comm, map_smul, Algebra.TensorProduct.basis_apply,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, trace_one_tmul, Module.Basis.trace_mul_traceDual, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i] <;> simp +contextual [eq_comm]

end General

variable {D : D7} {m n d : ℕ}

theorem cj_smul (a : AF D.host.F) (x : Mx D m n) : cj (a • x) = a • cj x := by
  rw [← map_cAl, ← map_cAl]
  funext i j
  exact map_smul (cAl D) a (x i j)

theorem cat_add {R : Type} [Add R] (p y p' y' : Matrix (Fin m) (Fin n) R) :
    cat (p + p') (y + y') = cat p y + cat p' y' := by
  funext i j
  obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective j <;>
    simp [cat, -finSumFinEquiv_apply_left, -finSumFinEquiv_apply_right]

theorem cat_smul {S R : Type} [SMul S R] (a : S) (p y : Matrix (Fin m) (Fin n) R) :
    cat (a • p) (a • y) = a • cat p y := by
  funext i j
  obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective j <;>
    simp [cat, -finSumFinEquiv_apply_left, -finSumFinEquiv_apply_right]

theorem cat_map {S R : Type} (f : R → S) (p y : Matrix (Fin m) (Fin n) R) :
    (cat p y).map f = cat (p.map f) (y.map f) := by
  funext i j
  obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective j <;>
    simp [cat, -finSumFinEquiv_apply_left, -finSumFinEquiv_apply_right]

def ptLin (T : GL (Fin (n + n)) D.host.E) (m : ℕ) : (Mx D m n × Mx D m n) →ₗ[AF D.host.F] Mx D m (n + n) where
  toFun p := pt T p.1 p.2
  map_add' p p' := by
    rw [Prod.fst_add, Prod.snd_add, pt, pt, pt, cj_add, cj_add, cat_add, Matrix.add_mul]
  map_smul' a p := by
    rw [Prod.smul_fst, Prod.smul_snd, pt, pt, cj_smul, cj_smul, cat_smul, Matrix.smul_mul, RingHom.id_apply]

def ptEquiv (T : GL (Fin (n + n)) D.host.E) (m : ℕ) : (Mx D m n × Mx D m n) ≃ₗ[AF D.host.F] Mx D m (n + n) :=
  LinearEquiv.ofBijective (ptLin T m)
    ⟨fun _ _ h => Prod.ext (pt_inj h).1 (pt_inj h).2, fun u => by
      obtain ⟨q, x, h⟩ := exists_pt T u
      exact ⟨(q, x), h.symm⟩⟩

theorem ptEquiv_symm (T : GL (Fin (n + n)) D.host.E) (q x : Mx D m n) : (ptEquiv T m).symm (pt T q x) = (q, x) :=
  (ptEquiv T m).symm_apply_eq.2 rfl

def gramEquiv (V : HSp D) (n : ℕ) : Mx D V.rank n ≃ₗ[AF D.host.F] Mx D V.rank n where
  toFun q := cj (-(gA V ⬝ q))
  map_add' q q' := by rw [Matrix.mul_add, neg_add, cj_add]
  map_smul' a q := by rw [Matrix.mul_smul, ← smul_neg, cj_smul, RingHom.id_apply]
  invFun y := -(giA V ⬝ cj y)
  left_inv q := by
    show -(giA V ⬝ cj (cj (-(gA V ⬝ q))) : Mx D V.rank n) = q
    rw [cj_cj, Matrix.mul_neg, neg_neg, giA_gA_cancel]
  right_inv y := by
    show cj (-(gA V ⬝ (-(giA V ⬝ cj y) : Mx D V.rank n))) = y
    rw [Matrix.mul_neg, neg_neg, gA_giA_cancel, cj_cj]

def coEquiv (V : HSp D) (T : GL (Fin (n + n)) D.host.E) (ε : Module.Basis (Fin d) D.host.F D.host.E) :
    Mx D V.rank (n + n) ≃ₗ[AF D.host.F]
      (Fin V.rank × Fin n × Fin d → AF D.host.F) × (Fin V.rank × Fin n × Fin d → AF D.host.F) :=
  (ptEquiv T V.rank).symm ≪≫ₗ LinearEquiv.prodComm _ _ _ ≪≫ₗ
    (coordL ε V.rank n).prodCongr (gramEquiv V n ≪≫ₗ coordL ε.traceDual V.rank n)

theorem coEquiv_pt (V : HSp D) (T : GL (Fin (n + n)) D.host.E) (ε : Module.Basis (Fin d) D.host.F D.host.E)
    (q x : Mx D V.rank n) : coEquiv V T ε (pt T q x) = (coord ε x, coord ε.traceDual (cj (-(gA V ⬝ q)))) := by
  rw [coEquiv, LinearEquiv.trans_apply, LinearEquiv.trans_apply, ptEquiv_symm]
  rfl

theorem coord_dot (ε : Module.Basis (Fin d) D.host.F D.host.E) (x y : Mx D m n) :
    coord ε x ⬝ᵥ coord ε.traceDual (cj y) = StdUnn.trA (Matrix.trace (adj x ⬝ y : Mx D n n)) := by
  have h : Matrix.trace (adj x ⬝ y : Mx D n n) = ∑ i, ∑ j, cA D (x i j) * y i j := by
    rw [Finset.sum_comm]; rfl
  rw [h, StdUnn.trA, map_sum, dotProduct, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine (sum_repr_dual ε (x i j) (cA D (y i j))).trans ?_
  refine Eq.trans ?_ (trA_cA _)
  rw [map_mul (cA D), cA_cA]

theorem coord_dot_gram (V : HSp D) (ε : Module.Basis (Fin d) D.host.F D.host.E) (x q : Mx D V.rank n) :
    coord ε x ⬝ᵥ coord ε.traceDual (cj (-(gA V ⬝ q))) = -StdUnn.trA (Matrix.trace (StdUnn.inner V x q)) := by
  rw [coord_dot, Matrix.mul_neg, Matrix.trace_neg, StdUnn.trA, map_neg]
  rfl

theorem coord_rat (ε : Module.Basis (Fin d) D.host.F D.host.E) (γ : Matrix (Fin m) (Fin n) D.host.E) :
    coord ε (rat γ : Mx D m n) = fun p => algebraMap D.host.F (AF D.host.F) (ε.repr (γ p.1 p.2.1) p.2.2) := by
  funext p
  show (Algebra.TensorProduct.basis (AF D.host.F) ε).repr (1 ⊗ₜ γ p.1 p.2.1) p.2.2 = _
  rw [Algebra.TensorProduct.basis_repr_tmul, one_smul, Finsupp.mapRange_apply]

theorem exists_pt_rat (T : GL (Fin (n + n)) D.host.E) (u : Matrix (Fin m) (Fin (n + n)) D.host.E) :
    ∃ q x : Matrix (Fin m) (Fin n) D.host.E, (rat u : Mx D m (n + n)) = pt T (rat q) (rat x) := by
  obtain ⟨p, y, h⟩ := exists_cat (u * (T⁻¹).1ᵀ)
  refine ⟨p.map D.sp.cm.sig, y.map D.sp.cm.sig, ?_⟩
  have h1 : u = cat p y * T.1ᵀ := by
    rw [← h, Matrix.mul_assoc, ← Matrix.transpose_mul, T.mul_inv, Matrix.transpose_one, Matrix.mul_one]
  rw [pt, ← cj_rat, ← cj_rat, cj_cj, cj_cj, h1, rat_mul, rat, cat_map]
  rfl

theorem coEquiv_form (V : HSp D) {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E} {T : GL (Fin (n + n)) D.host.E}
    (hG : T.1ᵀ * J₂ * T.1.map D.sp.cm.sig = GlobalTheory.StdUnn.Jst D n) (ε : Module.Basis (Fin d) D.host.F D.host.E)
    (w w' : Mx D V.rank (n + n)) :
    symp (R := AF D.host.F) (cAl D) (-1) (incM D.host.F (-V.gram)) (incM D.host.F J₂) w w' =
      (coEquiv V T ε w).1 ⬝ᵥ (coEquiv V T ε w').2 - (coEquiv V T ε w').1 ⬝ᵥ (coEquiv V T ε w).2 := by
  obtain ⟨q, x, rfl⟩ := exists_pt T w
  obtain ⟨q', x', rfl⟩ := exists_pt T w'
  rw [symp_pt V hG, coEquiv_pt, coEquiv_pt]
  dsimp only
  rw [coord_dot_gram, coord_dot_gram, trA_inner_comm V q x', neg_sub_neg]

def co (V : HSp D) {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E} {T : GL (Fin (n + n)) D.host.E}
    (hG : T.1ᵀ * J₂ * T.1.map D.sp.cm.sig = GlobalTheory.StdUnn.Jst D n) (ε : Module.Basis (Fin d) D.host.F D.host.E) :
    Dbx V J₂ d := ⟨coEquiv V T ε, coEquiv_form V hG ε⟩

theorem coEquiv_rat (V : HSp D) (T : GL (Fin (n + n)) D.host.E) (ε : Module.Basis (Fin d) D.host.F D.host.E)
    (u : Matrix (Fin V.rank) (Fin (n + n)) D.host.E) : ∃ y z : Fin V.rank × Fin n × Fin d → D.host.F,
    coEquiv V T ε (rat u) =
      (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i)) := by
  obtain ⟨q, x, h⟩ := exists_pt_rat T u
  have h1 : coEquiv V T ε (rat u) =
      (coord ε (rat x), coord ε.traceDual (rat ((-(V.gram * q)).map D.sp.cm.sig))) := by
    rw [h, coEquiv_pt, gA, ← rat_mul, ← rat_neg, cj_rat]
  rw [coord_rat, coord_rat] at h1
  exact ⟨_, _, h1⟩

theorem exists_adapted (D : D7) (n : ℕ) (V : HSp D) (J : Matrix (Fin n) (Fin n) D.host.E)
    (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E) (T : GL (Fin (n + n)) D.host.E)
    (hT : IsWittBasis D.sp.cm.sig J 1 T) (hG : T.1ᵀ * J₂ * T.1.map D.sp.cm.sig = GlobalTheory.StdUnn.Jst D n)
    (d : ℕ) (ε : Module.Basis (Fin d) D.host.F D.host.E) :
    ∃ co : Dbx V J₂ d, IsAdapted D.sp.cm.sig co ∧ IsCoord V T ε co := by
  refine ⟨co V hG ε, ⟨coEquiv_rat V T ε, fun u hu => ?_, fun u hu => ?_⟩, fun q x => ?_⟩
  · obtain ⟨q, x, rfl⟩ := exists_pt T u
    obtain rfl := (pt_diag_iff hT q x).1 hu
    exact (congrArg Prod.fst (coEquiv_pt V T ε q 0)).trans (coord_zero ε)
  · obtain ⟨q, x, rfl⟩ := exists_pt T u
    obtain rfl := (pt_anti_iff hT q x).1 hu
    refine (congrArg Prod.snd (coEquiv_pt V T ε 0 x)).trans ?_
    rw [Matrix.mul_zero, neg_zero, cj_zero]
    exact coord_zero _
  · refine ⟨congrArg Prod.fst (coEquiv_pt V T ε q x), fun x' => ?_⟩
    exact (congrArg (fun p => coord ε x' ⬝ᵥ Prod.snd p) (coEquiv_pt V T ε q x)).trans (coord_dot_gram V ε x' q)

end GlobalTheory.SWLink.Darb

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteKernelNodeRankLeTotalRank
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount

namespace GlobalTheory.DefRank

theorem rank_le_bigN : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (X : Node),
    DefNode D.R.m X → (G.V X).rank ≤ bigN D := by
  intro D T L sc G X hX
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hm := D.R.two_le_m
  rcases X with ⟨_ | i, j⟩ | i | j
  · obtain rfl := hX.2
    have e : G.V (.grid 0 D.R.m) = D.sp.X' := congrArg LSp.sp (colY_m L)
    rw [e, D.sp.X'_rank]
    show D.R.r + D.R.m * D.R.t ≤ D.R.k + D.R.m * (D.R.t + sLen D + 1)
    have e : D.R.m * (D.R.t + sLen D + 1) = D.R.m * D.R.t + D.R.m * sLen D + D.R.m := by ring
    omega
  · obtain ⟨hi, rfl⟩ := hX
    rw [(G.isV (X := .grid (i + 1) D.R.m) ⟨hi, le_rfl⟩ (by simp)).rank]
    show D.R.r + D.R.m * D.R.t + (i + 1) * sLen D ≤ D.R.k + D.R.m * (D.R.t + sLen D + 1)
    have := Nat.mul_le_mul_right (sLen D) hi
    have e : D.R.m * (D.R.t + sLen D + 1) = D.R.m * D.R.t + D.R.m * sLen D + D.R.m := by ring
    omega
  · exact hX.elim
  · rw [(G.isV (X := .top j) hX (by simp)).rank]
    show nRk D + D.R.m * (sLen D - 1) + j * (D.R.t + 1) ≤ D.R.k + D.R.m * (D.R.t + sLen D + 1)
    have h1 := Nat.mul_le_mul_right (D.R.t + 1) (show j ≤ D.R.m from hX)
    have hs : sLen D - 1 + 1 = sLen D := by unfold sLen; omega
    have hn : nRk D = D.R.r + 1 := rfl
    have e : D.R.m * (D.R.t + sLen D + 1) = D.R.m * (sLen D - 1) + D.R.m * (D.R.t + 1) + D.R.m := by
      conv_lhs => rw [← hs]
      ring
    have h2 : j * (D.R.t + 1) ≤ D.R.m * (D.R.t + 1) := h1
    omega

end GlobalTheory.DefRank
end

