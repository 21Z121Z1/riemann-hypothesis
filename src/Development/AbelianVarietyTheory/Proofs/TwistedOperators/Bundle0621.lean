import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0032
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0010
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0450
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0456
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0559
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0461
import Formalism.LocalToGlobal.Divisibility.TiedLemmas
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0601
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0599
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0579
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0588
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0372
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0418
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0603
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0589
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0602
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0558
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0078
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SqrtDivMulEqSqrtMul
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAnti
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1928
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInterOfSubfield
import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1773
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1406
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1904
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1439
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagOneNegOneConjAntidiagonalStabilizerMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagonalFixingDoublingMatrix
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0444

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ResidueConjugatePlaceCharacterArgumentSignedSum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

noncomputable section

namespace GlobalTheory.SeeConjChar.AtConj

theorem resT_of_mem {D : D7} (PP : Pl D.host.E) {x : EAf D} (hx : x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    resT PP x = Formalism.L2.DIV.resS D.host.F PP ⟨x, hx⟩ := by
  unfold resT; rw [dif_pos hx]

theorem resT_zero {D : D7} (PP : Pl D.host.E) : resT PP (0 : EAf D) = 0 := by
  rw [resT_of_mem PP (zero_mem _)]
  exact map_zero (Formalism.L2.DIV.resS D.host.F PP)

theorem resT_add {D : D7} (PP : Pl D.host.E) {x y : EAf D} (hx : x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (hy : y ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) : resT PP (x + y) = resT PP x + resT PP y := by
  rw [resT_of_mem PP hx, resT_of_mem PP hy, resT_of_mem PP (add_mem hx hy), ← map_add]
  rfl

theorem resT_sum {D : D7} (PP : Pl D.host.E) {ι : Type} [Fintype ι] (f : ι → EAf D)
    (hf : ∀ i, f i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) : resT PP (∑ i, f i) = ∑ i, resT PP (f i) := by
  have hs : (∑ i, f i) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := sum_mem fun i _ => hf i
  rw [resT_of_mem PP hs]
  have e : (⟨∑ i, f i, hs⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = ∑ i, (⟨f i, hf i⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) := by
    apply Subtype.ext
    simp
  rw [e, map_sum]
  exact Finset.sum_congr rfl fun i _ => (resT_of_mem PP (hf i)).symm

theorem flagV_f {M : Type} [Zero M] {ρ k n : ℕ} (e f : Fin ρ → M) (b : Fin k → M) (z : M) (i : Fin n)
    (h1 : ρ + k < i.1) (h2 : i.1 < 2 * ρ + k + 1) :
    GlobalTheory.SeeConjRead.flagV ρ k n e f b z i = f ⟨2 * ρ + k - i.1, by omega⟩ := by
  unfold GlobalTheory.SeeConjRead.flagV
  rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_pos h2]

theorem symmetricFlagBasisVectors_apply_middle {M : Type} [Zero M] {ρ k n : ℕ} (e f : Fin ρ → M) (b : Fin k → M) (z : M) (i : Fin n)
    (h1 : i.1 = ρ + k) : GlobalTheory.SeeConjRead.flagV ρ k n e f b z i = z := by
  unfold GlobalTheory.SeeConjRead.flagV
  rw [dif_neg (by omega), dif_neg (by omega), dif_pos h1]

theorem flagV_b {M : Type} [Zero M] {ρ k n : ℕ} (e f : Fin ρ → M) (b : Fin k → M) (z : M) (i : Fin n)
    (h1 : ρ ≤ i.1) (h2 : i.1 < ρ + k) : GlobalTheory.SeeConjRead.flagV ρ k n e f b z i = b ⟨i.1 - ρ, by omega⟩ := by
  unfold GlobalTheory.SeeConjRead.flagV
  rw [dif_neg (by omega), dif_pos h2]

end GlobalTheory.SeeConjChar.AtConj

open GlobalTheory.SeeConjChar GlobalTheory.SeeConjChar.AtConj

theorem GlobalTheory.SeeConjChar.resT_cP_argT : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → ∀ β : GL (Fin (Yc D 0).rank) (EAf D), IsFrame β (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → (∀ PP ∈ R.Pg, RedIs β PP (flagAt X h PP)) → ∀ PP ∈ R.Pg, ∀ κ : GA D (Yc D 0), finE (Yc D 0) κ ∈ St β → ((iotaX X h).toMulEquiv κ).2 ∈ X.K2 → GlobalTheory.SeeConjChar.resT (GlobalTheory.IdemSupport.cP PP) (GlobalTheory.SeeConjChar.argT X h (finE (Yc D 0) κ)) = GlobalTheory.SeeConjChar.conjRes PP (∑ i, ∑ j, if symEdge D.R.rS D.R.k i j then ((GlobalTheory.SeeConjChar.wB D.R.rS D.R.k (GlobalTheory.SeeConjChar.sideAt X h PP) i j : ℤ) : kP PP) * ((upperLeftBlock (r_le_Y (D := D) 0) (redFn β PP (finE (Yc D 0) κ)) : GL (Fin D.R.r) (kP PP)).val i j) else 0) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F X h hL hGrp β hβ hred PP hP κ hS hK2
  classical
  have hn : (Yc D 0).rank = 2 * D.R.rS + D.R.k + 1 := by
    have e := X.n_eq
    rw [h] at e
    have e2 := Formalism.L2.DIV.ranks_r_sym D
    change (Formalism.L2.SG.InstExistsPf.instOf D).n = _
    omega
  have hrn : D.R.r = (Yc D 0).rank := by
    have e := X.n_eq
    rw [h] at e
    change D.R.r = (Formalism.L2.SG.InstExistsPf.instOf D).n
    omega
  have hK : ((iotaX X h).toMulEquiv κ).2 ∈ X.B.I.Kset := (Formalism.L2.SG.Closed.level_subgroup_properties X).2.1 _ hK2
  have hU : upperLeftBlock (r_le_Y (D := D) 0) (redFn β PP (finE (Yc D 0) κ)) ∈ unip (kP PP) D.R.r :=
    unipCol_le _ _ _ (((GlobalTheory.T.mem_K2_iff_upperLeftBlock_reductions R F X h hL hGrp β hβ hred κ hK hS).1 hK2) PP hP)
  have hMinv : (finE (Yc D 0) κ)⁻¹ ∈ St β := inv_mem hS
  have hredinv : redFn β PP (finE (Yc D 0) κ)⁻¹ = (redFn β PP (finE (Yc D 0) κ))⁻¹ := extendOne_inv _ hS
  have hC : ∀ a j, hT X h (flagAt X h PP j) (Matrix.mulVec (finE (Yc D 0) κ).val (pairAt X h PP a)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧
      resT (GlobalTheory.IdemSupport.cP PP) (hT X h (flagAt X h PP j) (Matrix.mulVec (finE (Yc D 0) κ).val (pairAt X h PP a))) =
        conjRes PP ((sgnD D.R.rS D.R.k a : kP PP) * ((redFn β PP (finE (Yc D 0) κ))⁻¹).val a j) := by
    intro a j
    have c1 := GlobalTheory.T.residue_conjugatePlace_hermitianForm_adjoint X h PP κ (flagAt X h PP j) (pairAt X h PP a)
    have c2 := GlobalTheory.T.residue_otherInstanceForm_frameStabilizer_mulVec X h β PP (flagAt X h PP) (hred PP hP) _ hMinv (pairAt X h PP a) (GlobalTheory.T.otherInstanceForm_flagPairing_integral_on_frameLattice X h β hβ PP a) j
    refine ⟨c1.1.2 c2.1, ?_⟩
    rw [c1.2, c2.2, hredinv]
    congr 1
    simp only [GlobalTheory.T.residue_otherInstanceForm_flagPairing_eq_signedDelta R X h hL PP hP a, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

  let fF : Fin D.R.rS → Fin (Yc D 0).rank := fun a => ⟨2 * D.R.rS + D.R.k - a.1, by have := a.2; omega⟩
  let fN : Fin D.R.rS → Fin (Yc D 0).rank := fun a =>
    ⟨if a.1 + 1 < D.R.rS then 2 * D.R.rS + D.R.k - (a.1 + 1) else D.R.rS + D.R.k, by have := a.2; split_ifs <;> omega⟩
  let gB : Fin D.R.k → Fin (Yc D 0).rank := fun i => ⟨D.R.rS + D.R.k - 1 - i.1, by have := i.2; omega⟩
  have hF : ∀ a, f0T X h a = flagAt X h PP (fF a) := by
    intro a
    have ha := a.2
    have e : (fF a).1 = 2 * D.R.rS + D.R.k - a.1 := rfl
    have h1 : D.R.rS + D.R.k < (fF a).1 := by omega
    have h2 : (fF a).1 < 2 * D.R.rS + D.R.k + 1 := by omega
    unfold flagAt
    split_ifs <;> rw [flagV_f _ _ _ _ _ h1 h2] <;> congr 1 <;> ext <;> simp only [e] <;> omega
  have hNx : ∀ a, Formalism.L2.SG.HidaSetting.nxt (e0T X h) (z0T X h) a = pairAt X h PP (fN a) := by
    intro a
    have ha := a.2
    have e : (fN a).1 = if a.1 + 1 < D.R.rS then 2 * D.R.rS + D.R.k - (a.1 + 1) else D.R.rS + D.R.k := rfl
    unfold Formalism.L2.SG.HidaSetting.nxt
    by_cases hlt : a.1 + 1 < D.R.rS
    · rw [dif_pos hlt]
      rw [if_pos hlt] at e
      have h1 : D.R.rS + D.R.k < (fN a).1 := by omega
      have h2 : (fN a).1 < 2 * D.R.rS + D.R.k + 1 := by omega
      unfold pairAt
      split_ifs <;> rw [flagV_f _ _ _ _ _ h1 h2] <;> congr 1 <;> ext <;> simp only [e] <;> omega
    · rw [dif_neg hlt]
      rw [if_neg hlt] at e
      unfold pairAt
      split_ifs <;> rw [symmetricFlagBasisVectors_apply_middle _ _ _ _ _ e]
  have hBd : GlobalTheory.SeeConjChar.sideAt X h PP ≠ true → ∀ i, bwdT X h i = flagAt X h PP (gB i) := by
    intro hs i
    have hi := i.2
    have e : (gB i).1 = D.R.rS + D.R.k - 1 - i.1 := rfl
    have hs' : ¬ GlobalTheory.StdFrames.cpt PP (ewT X h) = 1 := by simpa [GlobalTheory.SeeConjChar.sideAt] using hs
    unfold flagAt
    rw [if_neg hs', flagV_b _ _ _ _ _ (by omega) (by omega)]
    congr 1; ext; simp only [e, Fin.val_rev]; omega
  have hBw : GlobalTheory.SeeConjChar.sideAt X h PP ≠ true → ∀ i : Fin D.R.k, bwT X h i = pairAt X h PP (gB i) := by
    intro hs i
    have hi := i.2
    have e : (gB i).1 = D.R.rS + D.R.k - 1 - i.1 := rfl
    have hs' : ¬ GlobalTheory.StdFrames.cpt PP (ewT X h) = 1 := by simpa [GlobalTheory.SeeConjChar.sideAt] using hs
    unfold pairAt
    rw [if_neg hs', flagV_b _ _ _ _ _ (by omega) (by omega)]
    congr 1; ext; simp only [e, Fin.val_rev]; omega

  have hfterm : ∀ a, hT X h (f0T X h a) (Matrix.mulVec (finE (Yc D 0) κ).val (Formalism.L2.SG.HidaSetting.nxt (e0T X h) (z0T X h) a)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧
      resT (GlobalTheory.IdemSupport.cP PP) (hT X h (f0T X h a) (Matrix.mulVec (finE (Yc D 0) κ).val (Formalism.L2.SG.HidaSetting.nxt (e0T X h) (z0T X h) a))) =
        conjRes PP ((sgnD D.R.rS D.R.k (fN a) : kP PP) * ((redFn β PP (finE (Yc D 0) κ))⁻¹).val (fN a) (fF a)) := by
    intro a
    rw [hF a, hNx a]
    exact hC _ _
  have hbterm : ∀ i : Fin D.R.k, (if hi : i.1 + 1 < D.R.k then hT X h (bwdT X h i) (Matrix.mulVec (finE (Yc D 0) κ).val (bwT X h ⟨i.1 + 1, hi⟩)) else 0) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧
      resT (GlobalTheory.IdemSupport.cP PP) (if hi : i.1 + 1 < D.R.k then hT X h (bwdT X h i) (Matrix.mulVec (finE (Yc D 0) κ).val (bwT X h ⟨i.1 + 1, hi⟩)) else 0) =
        conjRes PP (if hi : i.1 + 1 < D.R.k then (if GlobalTheory.SeeConjChar.sideAt X h PP then 0 else (sgnD D.R.rS D.R.k (gB ⟨i.1 + 1, hi⟩) : kP PP) * ((redFn β PP (finE (Yc D 0) κ))⁻¹).val (gB ⟨i.1 + 1, hi⟩) (gB i)) else 0) := by
    intro i
    by_cases hi : i.1 + 1 < D.R.k
    · rw [dif_pos hi, dif_pos hi]
      by_cases hs : GlobalTheory.SeeConjChar.sideAt X h PP = true
      · rw [if_pos hs]
        obtain ⟨h1, h2⟩ := GlobalTheory.T.residue_conjugatePlace_hermitian_dualBasis_stabiliser_eq_zero X h β hβ PP hs _ hS i ⟨i.1 + 1, hi⟩
        exact ⟨h1, by rw [h2, map_zero]⟩
      · rw [if_neg hs, hBd hs i, hBw hs ⟨i.1 + 1, hi⟩]
        exact hC _ _
    · rw [dif_neg hi, dif_neg hi]
      exact ⟨zero_mem _, by rw [map_zero, resT_zero]⟩
  unfold argT
  rw [resT_add _ (sum_mem fun a _ => (hfterm a).1) (sum_mem fun i _ => (hbterm i).1), resT_sum _ _ (fun a => (hfterm a).1),
    resT_sum _ _ (fun i => (hbterm i).1), Finset.sum_congr rfl fun a _ => (hfterm a).2,
    Finset.sum_congr rfl fun i _ => (hbterm i).2, ← map_sum, ← map_sum, ← map_add]
  congr 1
  exact GlobalTheory.T.conjugateResidue_flagTerms_reindex_symmetricEdge (r_le_Y (D := D) 0) D.R.rS D.R.k hn hrn _ hU (GlobalTheory.SeeConjChar.sideAt X h PP) fF fN gB (fun a => rfl) (fun a => rfl) (fun i => rfl)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilZetaFactor
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.TripleAssembly.PureImage

theorem det_ne_of_sig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hn, A, hA⟩ := h
  subst hn
  intro h0
  have h1 : Aᵀ * M * A.map star = (A.submatrix finSumFinEquiv id)ᵀ * M.submatrix finSumFinEquiv finSumFinEquiv *
      (A.map star).submatrix finSumFinEquiv id := by
    rw [Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]
  have h2 := congrArg Matrix.det hA
  rw [h1, Matrix.det_mul, Matrix.det_mul, Matrix.det_submatrix_equiv_self, h0, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_neg] at h2
  simp only [mul_zero, zero_mul, Matrix.det_one, one_mul, mul_one] at h2
  exact pow_ne_zero _ (neg_ne_zero.2 one_ne_zero) h2.symm

theorem det_ne_of_sig_map {E : Type} [Field E] {n r s : ℕ} {J : Matrix (Fin n) (Fin n) E} (τ : E →+* ℂ) (c : ℂ)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.HasSig (c • J.map τ) r s) : J.det ≠ 0 := by
  intro h0
  refine det_ne_of_sig h ?_
  have : (J.map τ).det = τ J.det := (RingHom.map_det τ J).symm
  rw [Matrix.det_smul, this, h0, map_zero, mul_zero]

theorem exists_factor_inj {U V P : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V] [AddCommGroup P]
    [Module ℂ P] (T : U →ₗ[ℂ] V) (S : Submodule ℂ U) (hT : ∀ x ∈ S, T x = 0 → x = 0) (p : U →ₗ[ℂ] P) :
    ∃ q : V →ₗ[ℂ] P, ∀ x ∈ S, q (T x) = p x := by
  obtain ⟨r, hr⟩ := (T.comp S.subtype).exists_leftInverse_of_injective (by
    rw [LinearMap.ker_eq_bot']
    exact fun x hx => Subtype.ext (hT x.1 x.2 hx))
  refine ⟨p.comp (S.subtype.comp r), fun x hx => ?_⟩
  have := LinearMap.congr_fun hr ⟨x, hx⟩
  change r (T x) = ⟨x, hx⟩ at this
  simp [this]

theorem mapA_thO_sum_pure : GlobalTheory.Published.HoweDualityReal → GlobalTheory.FunPr.Hypotheses₂ →
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
    ∀ (ωA : WRep W X) (ωB : WRep W₁ X), IsWeil ψ true W X β (β / α) ωA → IsWeil ψ false W₁ X α (α / β) ωB →
    ∀ (e : Fin (W.rank + W₁.rank) ≃ Fin X.rank) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
      (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank) (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
      (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
      (h : GlobalTheory.TripleRead.IsReading ψ A A₁ B α β e Bs Γ Xc),
      GlobalTheory.TripleRead.IsTransp ψ true Γ.M om ωA e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 h.JW) (GlobalTheory.TripleRead.toUX X e h.JX) →
      GlobalTheory.TripleRead.IsTransp ψ false Γ.M' om' ωB e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) h.JW₁) (GlobalTheory.TripleRead.toUX X e h.JX) →
      ∀ R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
      ∀ (m : ℕ) (f : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin W.rank × Fin (W.rank + W₁.rank)))
        (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl D.host.F, (Fin W.rank × Fin (W.rank + W₁.rank) → Fv D.host.F v) → ℂ),
        (∀ i, (∀ v, φ i v ∈ GlobalTheory.WeilM.SB _) ∧ ∀ᶠ v in Filter.cofinite, φ i v = Γ.M.vac v) →
        (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)) ∈ GlobalTheory.TripleAssembly.darbAlg Γ.M Bs.ψ Bs.emb →
        GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf (GlobalTheory.TripleRead.thO Γ.M ψ (sgn true W).gram e (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i))) =
          ∑ i, R.p (f i) ⊗ₜ[ℂ] GlobalTheory.SmallThetaModules.pureT (GlobalTheory.TripleAssembly.vacIm Γ Rf) (fun v => Rf.p v (φ i v)) := by
  intro hH hP D ψ θ hψ hθ W W₁ X A A₁ B α β hTr ωA ωB hA hB e Bs Γ Xc om om' h tA tB R Rf hm m f φ hφ hmem
  classical
  have hg := hm.triple.geo
  have hψ' : Bs.ψ = ψ := h.ψ
  have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ := hψ' ▸ hm.triple.base.std
  obtain ⟨w⟩ : Nonempty (InfinitePlace D.host.F) := inferInstance
  have dV : Γ.V.J.det ≠ 0 := det_ne_of_sig_map (Bs.emb w).1 1 (by rw [one_smul]; exact hg.hV.sig w)
  have dW : Γ.W.J.det ≠ 0 := det_ne_of_sig_map (Bs.emb w).1 Complex.I (hg.hW.sig w)
  have gA : (sgn true W).gram.det ≠ 0 := by
    have e1 : (sgn true W).gram = -W.gram := rfl
    rw [h.JW, one_smul] at dV
    rw [e1, Matrix.det_neg]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) dV
  obtain ⟨T, hT, hinj⟩ := GlobalTheory.T.thetaTransform_darbouxModel_linear_injective D Γ.M ψ (sgn true W).gram e (hψ' ▸ hg.hM) hstd dV dW gA
  have hS := GlobalTheory.T.darbouxModelAlgebraicVectors_le_adelicSchwartz _ _ _ Γ.M Bs.ψ Bs.emb hg.hM

  have Hq : ∃ q : (Matrix (Fin X.rank) (Fin W.rank) (AE D) → ℂ) →ₗ[ℂ] PiT R Γ Rf,
      ∀ Ψ ∈ darbAlg Γ.M Bs.ψ Bs.emb, q (GlobalTheory.TripleRead.thO Γ.M ψ (sgn true W).gram e Ψ) =
        liftPure Γ.M R.p Rf.p (vacIm Γ Rf) Ψ := by
    obtain ⟨q, hq⟩ := exists_factor_inj T _ (fun x hx => hinj x (hS hx)) (liftPure Γ.M R.p Rf.p (vacIm Γ Rf))
    exact ⟨q, fun Ψ hΨ => by rw [← hT Ψ (hS hΨ)]; exact hq Ψ hΨ⟩

  have HL := GlobalTheory.T.weil_model_projection_factorisation D.sp.cm.sig Γ.V Γ.W Γ.M Bs.ψ hg.hM _ R.p _ Rf.p (vacIm Γ Rf)
    (Filter.Eventually.of_forall fun _ => rfl)
  have hL : ∀ i, liftPure Γ.M R.p Rf.p (vacIm Γ Rf) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)) =
      R.p (f i) ⊗ₜ[ℂ] GlobalTheory.SmallThetaModules.pureT (vacIm Γ Rf) (fun v => Rf.p v (φ i v)) := by
    intro i
    unfold liftPure
    rw [dif_pos HL]
    exact HL.choose_spec (f i) (φ i) (hφ i).1 (hφ i).2
  unfold mapA thetaLift
  rw [dif_pos Hq, Hq.choose_spec _ hmem, map_sum]
  exact Finset.sum_congr rfl fun i _ => hL i

end GlobalTheory.TripleAssembly.PureImage
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilZetaUnramifiedStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seesaw_weil_zeta_unramified : GlobalTheory.Published.HoweDualityReal → GlobalTheory.FunPr.Hypotheses₂ →
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
    ∀ (ωA : WRep W X) (ωB : WRep W₁ X), IsWeil ψ true W X β (β / α) ωA → IsWeil ψ false W₁ X α (α / β) ωB →
    ∀ (e : Fin (W.rank + W₁.rank) ≃ Fin X.rank) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
      (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank) (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
      (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
      (h : GlobalTheory.TripleRead.IsReading ψ A A₁ B α β e Bs Γ Xc),
      GlobalTheory.TripleRead.IsTransp ψ true Γ.M om ωA e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 h.JW) (GlobalTheory.TripleRead.toUX X e h.JX) →
      GlobalTheory.TripleRead.IsTransp ψ false Γ.M' om' ωB e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) h.JW₁) (GlobalTheory.TripleRead.toUX X e h.JX) →
      ∀ R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
        ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin W.rank × Fin (W.rank + W₁.rank)))
          (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl D.host.F, (Fin W.rank × Fin (W.rank + W₁.rank) → Fv D.host.F v) → ℂ)
          (u : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE D.host.F D.host.E))
          (f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin W.rank × Fin (W.rank + W₁.rank))), f ∈ Γ.M.Pol Bs.ψ Bs.emb →
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) u →
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (Γ.M.heisLine Bs.ψ u) f f₁ →
          (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = Γ.M.vac v) →
          ∃ L : ℝ →+ WO (sgn true W) X, Continuous L ∧ (∀ t, (L t).map (finPart D) = 0) ∧
            GlobalTheory.TripleRead.thO Γ.M ψ (sgn true W).gram e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₁ φ) =
              fun x => deriv (fun t : ℝ => heisO ψ (sgn true W) X (L t) (GlobalTheory.TripleRead.thO Γ.M ψ (sgn true W).gram e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ)) x) 0 := by
  first | exact @GlobalTheory.ThetaDer.thO_pure_deriv_first | exact GlobalTheory.ThetaDer.thO_pure_deriv_first | (intros; apply GlobalTheory.ThetaDer.thO_pure_deriv_first <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitCharacterValueAlgebraic
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.SplitCharAlg

open Formalism.L2.Host
open scoped TensorProduct

theorem isAlgebraic_loc {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] {φ : I → E →+* ℂ} {n : I → ℤ}
    {χ : HChar E} (h : χ.HasInf φ n) (v : HeightOneSpectrum (𝓞 E)) (x : (v.adicCompletion E)ˣ) :
    IsAlgebraic ℚ ((χ.loc v x : ℂˣ) : ℂ) := by
  have h2 : (χ ^ 2).HasInf φ (fun i => 2 * n i) := by
    intro k
    have e1 : (((χ ^ 2).inf k : ℂˣ) : ℂ) = ((χ.inf k : ℂˣ) : ℂ) ^ 2 := rfl
    rw [e1, h k, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun i _ => ?_
    show _ = _ ^ (2 * n i)
    rw [mul_comm, zpow_mul]
    norm_cast
  obtain ⟨M, hM, hv⟩ := GlobalTheory.HeckeLocVals.locVals_of_even h2
  have hx := hv v x
  have e2 : (((χ ^ 2).loc v x : ℂˣ) : ℂ) = ((χ.loc v x : ℂˣ) : ℂ) ^ 2 := rfl
  rw [e2] at hx
  have hint : IsIntegral ℚ (((⟨_, hx⟩ : M) : ℂ)) := (IsIntegral.of_finite ℚ (⟨_, hx⟩ : M)).map M.val
  exact IsAlgebraic.of_pow two_pos hint.isAlgebraic

open GlobalTheory.AdelicU GlobalTheory.AdelicU.Supp GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels in

theorem exists_locIdele {D : D7} {e : AE D} (he : IsSplitIdem D e) (x : (AE D)ˣ) (hx : (x : AE D) = e * x + (1 - e)) :
    ∃ (w : HeightOneSpectrum (𝓞 D.host.E)) (y : (w.adicCompletion D.host.E)ˣ), x = GlobalTheory.LFun.locIdele D.host.F w y := by
  obtain ⟨v, τ, rfl⟩ := isSplitIdem_iff_exists.1 he
  have hA : At (evFin D.host.F v) (splitIdemAd (isCMExt_host D) τ) := by
    intro u hu
    rw [Algebra.smul_def, mul_comm]
    change singleTens D.host.E v _ * _ = 0
    rw [singleTens_mul]
    have : compFin D.host.F D.host.E v (algebraMap (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) u) = 0 := by
      change (evFin D.host.F v u) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
      rw [hu, TensorProduct.zero_tmul]
    rw [this, mul_zero, map_zero]
  have h1 : (x : AE D) - 1 = splitIdemAd (isCMExt_host D) τ * ((x : AE D) - 1) := by
    rw [mul_sub, mul_one]
    nth_rewrite 1 [hx]
    ring
  refine ⟨_, _, GlobalTheory.ChrLocal.eq_locIdele_splitPrime (isCMExt_host D) τ x ?_ ?_⟩
  · intro u hu
    rw [h1, ← smul_mul_assoc, hA u hu, zero_mul]
  · obtain ⟨-, e0⟩ := GlobalTheory.LatSplit.piW_splitIdemAd (isCMExt_host D) τ
    rw [hx, map_add, map_mul, map_sub, map_one, e0]
    ring

end GlobalTheory.SplitCharAlg

namespace GlobalTheory.SplitCharAlg

theorem beta_isAlgebraic : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X → ∀ e : AE D, IsSplitIdem D e → ∀ x : (AE D)ˣ, (x : AE D) = e * x + (1 - e) →
      IsAlgebraic ℚ (((G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2)) x : Circle) : ℂ) := by
  intro D T _ L μ₀ sc G W i j A A' WW X _ _ hL _ e he x hx
  obtain ⟨w, y, rfl⟩ := exists_locIdele he x hx
  have hi1 : 1 ≤ D.R.m - (i : ℕ) := by have := i.2; omega
  have hi2 : D.R.m - (i : ℕ) ≤ D.R.m := Nat.sub_le _ _
  have hchi : (((G.ch.chi (D.R.m - i)) (GlobalTheory.LFun.locIdele D.host.F w y) : Circle) : ℂ) =
      (((G.ch.chiH (D.R.m - i)).loc w y : ℂˣ) : ℂ) :=
    congrArg (fun f => ((f y : ℂˣ) : ℂ)) (GlobalTheory.LFun.locChar_eq_of_chrEq (G.ch.chi_eq _ hi1 hi2) w)
  have heta : ((L.eta (GlobalTheory.LFun.locIdele D.host.F w y) : Circle) : ℂ) = ((L.C.eta.loc w y : ℂˣ) : ℂ) :=
    congrArg (fun f => ((f y : ℂˣ) : ℂ)) (GlobalTheory.LFun.locChar_eq_of_chrEq hL.eta w)
  rw [MonoidHom.mul_apply, Circle.coe_mul, MonoidHom.pow_apply, Circle.coe_pow, hchi, heta]
  exact (isAlgebraic_loc (G.ch.inf _ hi1 hi2) w y).mul ((isAlgebraic_loc L.C.isEta.inf w y).pow _)

end GlobalTheory.SplitCharAlg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitDoublingTMatrixMulInverseEqOne
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

namespace GlobalTheory.SplitDblGen

theorem tMat_mul_tMat_eq_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d : ℕ) (c : AE F E) (K K' : Matrix (Fin d) (Fin d) (AE F E)),
    K * K' = 1 → (c * c) • (K - 1) = K - 1 →
    GlobalTheory.SplitDblGen.tMat c K * GlobalTheory.SplitDblGen.tMat c K' = 1 := by
  intro F E _ _ _ _ _ d c K K' hKK hc
  have h2 : (half : AE F E) * 2 = 1 := by
    unfold half
    rw [show (2 : AE F E) = algebraMap (AF F) (AE F E) 2 from (map_ofNat _ 2).symm, ← map_mul, invOf_mul_self, map_one]
  have hP : (c * c) • ((K - 1) * (K' - 1)) = (K - 1) * (K' - 1) := by rw [← smul_mul_assoc, hc]
  have hsum : (K - 1) + (K' - 1) + (K - 1) * (K' - 1) = 0 := by
    rw [sub_mul, mul_sub, mul_sub, hKK]; noncomm_ring
  have hff : ((half * (1 + c)) * (half * (1 + c))) • ((K - 1) * (K' - 1))
      = (half * (1 + c)) • ((K - 1) * (K' - 1)) := by
    rw [show (half * (1 + c)) * (half * (1 + c)) = half * half * (1 + 2 * c) + half * half * (c * c) by ring,
      add_smul, ← smul_smul (half * half) (c * c), hP, ← add_smul]
    congr 1
    linear_combination (half * (1 + c)) * h2
  unfold tMat
  generalize half * (1 + c) = f at hff ⊢
  have e : (1 + f • (K - 1)) * (1 + f • (K' - 1))
      = 1 + f • ((K - 1) + (K' - 1)) + (f * f) • ((K - 1) * (K' - 1)) := by
    rw [add_mul, one_mul, mul_add, mul_one, smul_mul_smul_comm, smul_add]; abel
  rw [e, hff, add_assoc, ← smul_add, hsum, smul_zero, add_zero]

end GlobalTheory.SplitDblGen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceLatticeStabilisersFixWeilVacuum
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceTensor

theorem splitVacuumFixed : ∀ D : D7, SplitVacuumFixed D := by
  intro D ψ S T χS χT om ΛS ΛT hW hS hT v hv uS uT f hf hvac k hk k' hk'
  obtain ⟨e, he, hb⟩ := hv
  have hε : IsPlaceIdem D v (pairA D.host.F 0 (singleV D.host.F v 1)) :=
    ⟨_, rfl, GlobalTheory.SplitIdem.evalV_singleV_same _ _ _, fun _ hw => GlobalTheory.SplitIdem.evalV_singleV_ne _ _ _ hw⟩
  have hb' : e + cA D e = algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (singleV D.host.F v 1)) := hb
  have he' := GlobalTheory.SplitScalar.isSplitIdem_conj he
  have s1 : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (singleV D.host.F v 1)) * e = e := by
    rw [← hb']; linear_combination he.1 + he.2.1
  have s2 : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (singleV D.host.F v 1)) * cA D e = cA D e := by
    rw [← hb']; linear_combination he'.1 + he.2.1
  have sk := suppPl_emb S v k
  have sk' := suppPl_emb T v k'
  have kS := emb_keeps_latHat S hS.1.fg v hk
  have kT := emb_keeps_latHat T hT.1.fg v hk'
  have key := GlobalTheory.VacStabFixed.om_split_halves hW hS hT he (fun i j => by rw [hb']; exact sk i j)
    (fun i j => by rw [hb']; exact sk' i j)
    (fun u hu => ⟨GlobalTheory.LocalLatStab.actO_mem S T _ _ _ _ _ (fun y hy => (kS y).1 hy) (fun y hy => (kT y).1 hy) u hu,
      GlobalTheory.LocalLatStab.actO_mem S T _ _ _ _ _ (GlobalTheory.LocalLatStab.inv_keeps S _ _ kS)
        (GlobalTheory.LocalLatStab.inv_keeps T _ _ kT) u hu⟩)
    (GlobalTheory.VecInv.isDetAt_detAt e he.1 S _) (GlobalTheory.VecInv.isDetAt_detAt e he.1 T _) hf
    (fun u hu hh => hvac.2 e he u (GlobalTheory.VacStabFixed.half_mem_place hε s1 hu hh) hh)
    (fun u hu hh => hvac.2 _ he' u (GlobalTheory.VacStabFixed.half_mem_place hε s2 hu hh) hh)
  rwa [splitFacO, GlobalTheory.VacStabFixed.unram_detAt hS.1 kS he.1 s1 uT, GlobalTheory.VacStabFixed.unram_detAt hT.1 kT he.1 s1 uS,
    inv_one, mul_one, Circle.coe_one, one_smul] at key

end GlobalTheory.PlaceTensor

end
end

