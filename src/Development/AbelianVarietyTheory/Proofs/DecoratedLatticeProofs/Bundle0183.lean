import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0173
import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ContinuesConst
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsLatticeFrameIsMajorantFrame
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0165
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0166
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0167
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0327
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0170
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0092
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsInnerProductSmoothVectorsTensor
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0171
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsGLSubmatrix
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSiegelLeviDetHomLeviMulUnipotent
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP
open GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw

namespace GlobalTheory.Core.Rk.SWLaw

theorem aP_levi_mul_nC : ∀ (D : D7) (A : HSp D) (p : siegel A) (a : GL (Fin A.rank) (AE D)) (c : skewA D A.rank), (p : GA D (dblSp A)) = (dblDec A).levi a * (dblDec A).nC c → aP A p = Matrix.GeneralLinearGroup.det a := by
  intro D A p a c hp
  have hM : Formalism.L2.Theta.mt (dblSp A) (p : GA D (dblSp A)) ⬝ (dblDec A).jX = (dblDec A).jX ⬝ a.1 := by
    rw [hp, GlobalTheory.MixModel.mt_mul, Matrix.mul_assoc, HypDec.nC_jX, HypDec.levi_jX]
  apply Units.ext
  rw [GlobalTheory.Doubling.val_aOf]
  show (GlobalTheory.Doubling.leviMat finSumFinEquiv (Formalism.L2.Theta.mt (dblSp A) (p : GA D (dblSp A)))).det = a.1.det
  set M := Formalism.L2.Theta.mt (dblSp A) (p : GA D (dblSp A)) with hMdef
  have key : GlobalTheory.Doubling.leviMat finSumFinEquiv M * rat A.gram⁻¹ = rat A.gram⁻¹ * a.1 := by
    ext i j
    have h := congrFun (congrFun hM (finSumFinEquiv (Sum.inl i))) j
    simp only [HypDec.jX, dblDec, rat, stackRows, Matrix.mul_apply, Matrix.map_apply, Matrix.submatrix_apply,
      Fin.sum_univ_add, finSumFinEquiv_apply_left, finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd,
      Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, id] at h
    simp only [GlobalTheory.Doubling.leviMat, rat, Matrix.mul_apply, Matrix.add_apply, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂,
      Matrix.of_apply, Matrix.submatrix_apply, Matrix.map_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
      add_mul, Finset.sum_add_distrib]
    exact h
  have hu : IsUnit (rat (D := D) A.gram⁻¹).det := by
    rw [rat, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (Matrix.isUnit_nonsing_inv_det _ (gram_det_ne A).isUnit).map _
  have hd := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_mul, mul_comm] at hd
  exact hu.mul_left_cancel hd

end GlobalTheory.Core.Rk.SWLaw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsAdaptedLatticeFrame
section
open scoped NNReal Matrix TensorProduct Topology
open Filter NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.EisCont GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Core.Rk.SWLaw (dblDec zeroSp)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HypAdapt

open Formalism.UG (cT bc cT_mul cT_one)
open Matrix

section Pure

variable {R : Type} [CommRing R] (s : R →+* R) {n r m : ℕ} (J : Matrix (Fin n) (Fin n) R)

theorem exists_frame_of_sign {κ : Type} [Fintype κ] [DecidableEq κ] (e : κ ≃ Fin n) (A : Matrix (Fin n) κ R) (ε : κ → Bool)
    {X Z : Matrix (Fin n) (Fin r) R} (M N : Matrix κ (Fin r) R)
    (hA : cT s A * J * A = diagonal fun i => if ε i then 1 else -1) (hM : A * M = X) (hN : A * N = Z)
    (h : (diagonal fun i => if ε i then (1 : R) else -1) * N = M) :
    ∃ (b : GL (Fin n) R) (δ : Fin n → Bool), (cT s b.1 * J * b.1 = diagonal fun i => if δ i then 1 else -1) ∧
      cT s (b⁻¹).1 * (b⁻¹).1 * X = J * Z := by
  set Δ : Matrix κ κ R := diagonal fun i => if ε i then (1 : R) else -1 with hΔ
  have h1 : Δ * Δ = 1 := by
    rw [hΔ, diagonal_mul_diagonal, ← diagonal_one]
    exact congrArg diagonal (funext fun i => by split_ifs <;> simp)
  have h2 : Δ * (cT s A * J) * A = 1 := by rw [Matrix.mul_assoc, hA, h1]
  have h3 : A * (Δ * (cT s A * J)) = 1 :=
    (Matrix.mul_eq_one_comm_of_card_eq _ _ _ (Fintype.card_congr e)).1 h2
  generalize Δ * (cT s A * J) = B at h2 h3
  have h4 : cT s B * cT s A = 1 := by rw [← cT_mul, h3, cT_one]
  refine ⟨⟨A.submatrix id e.symm, B.submatrix e.symm id, ?_, ?_⟩, fun i => ε (e.symm i), ?_, ?_⟩
  · rw [submatrix_mul_equiv, h3, submatrix_id_id]
  · exact (submatrix_mul _ _ _ id _ Function.bijective_id).symm.trans (by rw [h2, submatrix_one_equiv])
  · have := congrArg (fun y => y.submatrix e.symm e.symm) hA
    simp only [hΔ, submatrix_diagonal_equiv] at this
    exact this
  · change (cT s B).submatrix id e.symm * B.submatrix e.symm id * X = _
    rw [submatrix_mul_equiv, submatrix_id_id, ← hM, Matrix.mul_assoc, ← Matrix.mul_assoc B, h2, Matrix.one_mul, ← h, ← hA,
      ← hN, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc, h4, Matrix.one_mul]

theorem exists_frame_hyp (hn : m + 2 * r = n) {X Y : Matrix (Fin n) (Fin r) R} {I : Matrix (Fin n) (Fin m) R} (ε : Fin m → Bool)
    {t : R} (ht : t + t = 1) (hs : s t = t)
    (XX : cT s X * J * X = 0) (YY : cT s Y * J * Y = 0) (YX : cT s Y * J * X = 1) (XY : cT s X * J * Y = 1)
    (IX : cT s I * J * X = 0) (IY : cT s I * J * Y = 0) (XI : cT s X * J * I = 0) (YI : cT s Y * J * I = 0)
    (II : cT s I * J * I = diagonal fun i => if ε i then 1 else -1) :
    ∃ (b : GL (Fin n) R) (δ : Fin n → Bool), (cT s b.1 * J * b.1 = diagonal fun i => if δ i then 1 else -1) ∧
      cT s (b⁻¹).1 * (b⁻¹).1 * X = (J * Y : Matrix (Fin n) (Fin r) R) * diagonal fun _ : Fin r => t := by
  have hΔ : (diagonal fun i => if Sum.elim (Sum.elim (fun _ : Fin r => true) fun _ : Fin r => false) ε i then (1 : R) else -1) =
      fromBlocks (fromBlocks 1 0 0 (-1)) 0 0 (diagonal fun i => if ε i then 1 else -1) := by
    rw [← diagonal_one, diagonal_neg, fromBlocks_diagonal, fromBlocks_diagonal]
    exact congrArg diagonal (funext fun i => by rcases i with (i | i) | i <;> rfl)
  have hp : cT s (X + t • Y) = cT s X + t • cT s Y := by ext i j; simp [cT, hs]
  have hm : cT s (X - t • Y) = cT s X - t • cT s Y := by ext i j; simp [cT, hs]
  have hc : cT s (fromCols (fromCols (X + t • Y) (X - t • Y)) I) =
      fromRows (fromRows (cT s X + t • cT s Y) (cT s X - t • cT s Y)) (cT s I) := by
    rw [← hp, ← hm]; ext ((i | i) | i) j <;> rfl
  have h1 : (t • 1 + t • 1 : Matrix (Fin r) (Fin r) R) = 1 := by rw [← add_smul, ht, one_smul]
  rw [Matrix.mul_assoc J]
  refine exists_frame_of_sign s J (Fintype.equivFinOfCardEq (by simp [← hn]; ring))
    (fromCols (fromCols (X + t • Y) (X - t • Y)) I) (Sum.elim (Sum.elim (fun _ => true) fun _ => false) ε)
    (fromRows (fromRows (t • 1) (t • 1)) 0) (fromRows (fromRows (t • 1) (-(t • 1))) 0) ?_ ?_ ?_ ?_
  · rw [hΔ, hc, fromRows_mul _ _ J, fromRows_mul _ _ J, fromRows_mul_fromCols, fromRows_mul_fromCols, fromRows_mul, mul_fromCols]
    simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, XX, YY, YX, XY,
      IX, IY, XI, YI, II, smul_zero, add_zero, zero_add, sub_zero, zero_sub, fromRows_zero, fromCols_zero, h1, sub_self,
      neg_add_cancel, add_neg_cancel, ← neg_add', sub_neg_eq_add]
  · rw [fromCols_mul_fromRows, fromCols_mul_fromRows, ← Matrix.add_mul]
    simp [← add_smul, smul_add, ht]
  · rw [fromCols_mul_fromRows, fromCols_mul_fromRows, ← smul_eq_mul_diagonal]
    have h2 : t • Y = (t * t) • Y + (t * t) • Y := by rw [← add_smul, ← mul_add, ht, mul_one]
    simp only [Matrix.mul_neg, Matrix.mul_smul, Matrix.mul_one, Matrix.mul_zero, add_zero, smul_add, smul_sub, smul_smul]
    rw [h2]; abel
  · rw [hΔ, fromBlocks_mul_fromRows, fromBlocks_mul_fromRows]
    simp

theorem exists_frame_hyp' (hn : m + 2 * r = n) {X Y : Matrix (Fin n) (Fin r) R} {I : Matrix (Fin n) (Fin m) R}
    {G c : Matrix (Fin m) (Fin m) R} (ε : Fin m → Bool) {t : R} (ht : t + t = 1) (hs : s t = t)
    (XX : cT s X * J * X = 0) (YY : cT s Y * J * Y = 0) (YX : cT s Y * J * X = 1) (XY : cT s X * J * Y = 1)
    (IX : cT s I * J * X = 0) (IY : cT s I * J * Y = 0) (XI : cT s X * J * I = 0) (YI : cT s Y * J * I = 0)
    (II : cT s I * J * I = G) (hc : cT s c * G * c = diagonal fun i => if ε i then 1 else -1) :
    ∃ (b : GL (Fin n) R) (δ : Fin n → Bool), (cT s b.1 * J * b.1 = diagonal fun i => if δ i then 1 else -1) ∧
      cT s (b⁻¹).1 * (b⁻¹).1 * X = (J * Y : Matrix (Fin n) (Fin r) R) * diagonal fun _ : Fin r => t := by
  refine exists_frame_hyp s J hn (I := I * c) ε ht hs XX YY YX XY ?_ ?_ ?_ ?_ ?_
  · rw [cT_mul, Matrix.mul_assoc (cT s c), Matrix.mul_assoc (cT s c), IX, Matrix.mul_zero]
  · rw [cT_mul, Matrix.mul_assoc (cT s c), Matrix.mul_assoc (cT s c), IY, Matrix.mul_zero]
  · rw [← Matrix.mul_assoc, XI, Matrix.zero_mul]
  · rw [← Matrix.mul_assoc, YI, Matrix.zero_mul]
  · rw [← Matrix.mul_assoc, cT_mul, Matrix.mul_assoc (cT s c), Matrix.mul_assoc (cT s c), II, hc]

end Pure

section Lattice

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n r m : ℕ}
  (J : Matrix (Fin n) (Fin n) E)

def imLat (P : Matrix (Fin n) (Fin m) E) (L : Submodule (𝓞 E) (Fin m → E)) : Submodule (𝓞 E) (Fin n → E) :=
  L.map (P.mulVecLin.restrictScalars (𝓞 E))

omit [NumberField E] in
theorem mulVec_mem_span_imLat (P : Matrix (Fin n) (Fin m) E) {L : Submodule (𝓞 E) (Fin m → E)} (hL : Submodule.IsLattice E L)
    (u : Fin m → E) : P *ᵥ u ∈ Submodule.span E (imLat P L : Set (Fin n → E)) :=
  Submodule.apply_mem_span_image_of_mem_span P.mulVecLin (hL.span_eq_top ▸ Submodule.mem_top : u ∈ Submodule.span E (L : Set _))

omit [NumberField F] [NumberField E] in
theorem hE_eq (x y : Fin n → E) : hE σ J x y = (fun i => σ (x i)) ⬝ᵥ J *ᵥ y := by
  simp [hE, Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

omit [NumberField F] [NumberField E] in
theorem hE_mulVec {P : Matrix (Fin n) (Fin m) E} {G : Matrix (Fin m) (Fin m) E} {Q : Matrix (Fin m) (Fin n) E}
    (h : G * Q = cT (σ : E →+* E) P * J) (u : Fin m → E) (y : Fin n → E) : hE σ J (P *ᵥ u) y = hE σ G u (Q *ᵥ y) := by
  have e : (fun i => σ ((P *ᵥ u) i)) = (fun i => σ (u i)) ᵥ* cT (σ : E →+* E) P := by
    ext i; simp [cT, mulVec, vecMul, dotProduct, mul_comm]
  rw [hE_eq, hE_eq, mulVec_mulVec, h, e, ← dotProduct_mulVec, mulVec_mulVec]

omit [NumberField F] [NumberField E] in
theorem hE_add (x x' y : Fin n → E) : hE σ J (x + x') y = hE σ J x y + hE σ J x' y := by
  simp [hE, Formalism.UG.hform, add_mul, Finset.sum_add_distrib]

omit [NumberField E] in
theorem smul_col_mem {X : Matrix (Fin n) (Fin r) E} {u : Fin r → E} (hu : u ∈ stdLattice E r) (i : Fin r) :
    u i • Xᵀ i ∈ imLat X (stdLattice E r) := by
  refine ⟨Pi.single i (u i), fun j _ => ?_, ?_⟩
  · by_cases h : j = i
    · subst h; simpa using hu j trivial
    · simp [h]
  · ext j; simp [mul_comm]

theorem exists_lattice_hyp (hJ : J.det ≠ 0) {G : Matrix (Fin m) (Fin m) E} (hG : G.det ≠ 0)
    {L₀ : Submodule (𝓞 E) (Fin m → E)} (hL : Submodule.IsLattice E L₀) (hd : ∀ v, IsSelfDualAt σ G L₀ v)
    {X Y : Matrix (Fin n) (Fin r) E} {I : Matrix (Fin n) (Fin m) E} {Q : Matrix (Fin m) (Fin n) E}
    (XX : cT (σ : E →+* E) X * J * X = 0) (YY : cT (σ : E →+* E) Y * J * Y = 0) (YX : cT (σ : E →+* E) Y * J * X = 1)
    (XY : cT (σ : E →+* E) X * J * Y = 1) (XI : cT (σ : E →+* E) X * J * I = 0) (YI : cT (σ : E →+* E) Y * J * I = 0)
    (QX : Q * X = 0) (QY : Q * Y = 0) (QI : Q * I = 1) (hQ : G * Q = cT (σ : E →+* E) I * J)
    (h1 : X * (cT (σ : E →+* E) Y * J) + I * Q + Y * (cT (σ : E →+* E) X * J) = 1) :
    ∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (∀ v, IsSelfDualAt σ J L v) ∧
      ∀ z ∈ L, ∀ i, ((cT (σ : E →+* E) Y * J) *ᵥ z) i • Xᵀ i ∈ L ∧ ((cT (σ : E →+* E) X * J) *ᵥ z) i • Yᵀ i ∈ L := by
  set L := imLat X (stdLattice E r) ⊔ imLat I L₀ ⊔ imLat Y (stdLattice E r)
  have l1 : imLat X (stdLattice E r) ≤ L := le_sup_left.trans le_sup_left
  have l2 : imLat I L₀ ≤ L := le_sup_right.trans le_sup_left
  have l3 : imLat Y (stdLattice E r) ≤ L := le_sup_right
  have hz : ∀ z : Fin n → E, z = X *ᵥ ((cT (σ : E →+* E) Y * J) *ᵥ z) + I *ᵥ (Q *ᵥ z) +
      Y *ᵥ ((cT (σ : E →+* E) X * J) *ᵥ z) := fun z => by
    rw [mulVec_mulVec, mulVec_mulVec, mulVec_mulVec, ← add_mulVec, ← add_mulVec, h1, one_mulVec]
  have hm : ∀ z, z ∈ L ↔ (cT (σ : E →+* E) Y * J) *ᵥ z ∈ stdLattice E r ∧ Q *ᵥ z ∈ L₀ ∧
      (cT (σ : E →+* E) X * J) *ᵥ z ∈ stdLattice E r := fun z => by
    refine ⟨fun h => ?_, fun h => hz z ▸ add_mem (add_mem (l1 ⟨_, h.1, rfl⟩) (l2 ⟨_, h.2.1, rfl⟩)) (l3 ⟨_, h.2.2, rfl⟩)⟩
    obtain ⟨_, h', _, ⟨c, hc, rfl⟩, rfl⟩ := Submodule.mem_sup.1 h
    obtain ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩ := Submodule.mem_sup.1 h'
    simp only [LinearMap.restrictScalars_apply, mulVecLin_apply, mulVec_add, mulVec_mulVec, XX, YY, YX, XY, XI, YI, QX, QY, QI,
      zero_mulVec, one_mulVec, add_zero, zero_add]
    exact ⟨ha, hb, hc⟩
  have hs : Submodule.IsLattice E (stdLattice E r) := isLattice_stdLattice
  have hl : Submodule.IsLattice E L := ⟨((hs.fg.map _).sup (hL.fg.map _)).sup (hs.fg.map _), eq_top_iff.2 fun z _ =>
    hz z ▸ add_mem (add_mem (Submodule.span_mono l1 (mulVec_mem_span_imLat X hs _))
      (Submodule.span_mono l2 (mulVec_mem_span_imLat I hL _))) (Submodule.span_mono l3 (mulVec_mem_span_imLat Y hs _))⟩
  have d0 := (SelfDual.forall_isSelfDualAt_iff hG hL).1 hd
  have d1 := (SelfDual.forall_isSelfDualAt_iff (by simp) hs).1 (isSelfDualAt_stdLattice_one σ)
  have eX := hE_mulVec σ J (Matrix.one_mul (cT (σ : E →+* E) X * J))
  have eY := hE_mulVec σ J (Matrix.one_mul (cT (σ : E →+* E) Y * J))
  have eI := hE_mulVec σ J hQ
  refine ⟨L, hl, (SelfDual.forall_isSelfDualAt_iff hJ hl).2 fun y => ⟨fun hy x hx => ?_, fun h => (hm y).2
    ⟨(d1 _).2 fun u hu => eY u y ▸ h _ (l3 ⟨u, hu, rfl⟩), (d0 _).2 fun u hu => eI u y ▸ h _ (l2 ⟨u, hu, rfl⟩),
      (d1 _).2 fun u hu => eX u y ▸ h _ (l1 ⟨u, hu, rfl⟩)⟩⟩,
    fun z h i => ⟨l1 (smul_col_mem ((hm z).1 h).1 i), l3 (smul_col_mem ((hm z).1 h).2.2 i)⟩⟩
  rw [hm] at hx hy
  rw [hz x, hE_add, hE_add, eX, eI, eY]
  exact add_mem (add_mem ((d1 _).1 hy.2.2 _ hx.1) ((d0 _).1 hy.2.1 _ hx.2.1)) ((d1 _).1 hy.1 _ hx.2.2)

theorem exists_arch_frame_hyp (h : IsCMExt F E σ) (hn : m + 2 * r = n) {G : Matrix (Fin m) (Fin m) E} (hG : IsHermND σ G)
    {X Y : Matrix (Fin n) (Fin r) E} {I : Matrix (Fin n) (Fin m) E}
    (XX : cT (σ : E →+* E) X * J * X = 0) (YY : cT (σ : E →+* E) Y * J * Y = 0) (YX : cT (σ : E →+* E) Y * J * X = 1)
    (XY : cT (σ : E →+* E) X * J * Y = 1) (IX : cT (σ : E →+* E) I * J * X = 0) (IY : cT (σ : E →+* E) I * J * Y = 0)
    (XI : cT (σ : E →+* E) X * J * I = 0) (YI : cT (σ : E →+* E) Y * J * I = 0) (II : cT (σ : E →+* E) I * J * I = G)
    (w : InfinitePlace F) : ∃ (b : GL (Fin n) (w.Completion ⊗[F] E)) (δ : Fin n → Bool),
      (cT (sigR _ σ) b.1 * JR w.Completion J * b.1 = diagonal fun i => if δ i then 1 else -1) ∧
      cT (sigR _ σ) (b⁻¹).1 * (b⁻¹).1 * X.map (inclR (F := F) w.Completion) =
        (JR w.Completion J * Y.map (inclR (F := F) w.Completion) : Matrix (Fin n) (Fin r) (w.Completion ⊗[F] E)) *
          diagonal fun _ : Fin r => inclR (F := F) w.Completion (2⁻¹ : E) := by
  obtain ⟨c, ε, hc⟩ := Frames.exists_arch_frame h hG w
  have up : ∀ {k l : ℕ} {A : Matrix (Fin n) (Fin k) E} {B : Matrix (Fin n) (Fin l) E} {C : Matrix (Fin k) (Fin l) E},
      cT (σ : E →+* E) A * J * B = C →
      (cT (sigR _ σ) (A.map (inclR (F := F) w.Completion)) * JR w.Completion J :
        Matrix (Fin k) (Fin n) (w.Completion ⊗[F] E)) *
        B.map (inclR (F := F) w.Completion) = C.map (inclR (F := F) w.Completion) := fun h => by
    rw [← h, Matrix.map_mul, Matrix.map_mul]; rfl
  have z : ∀ {k l : ℕ}, (0 : Matrix (Fin k) (Fin l) E).map (inclR (F := F) w.Completion) = 0 :=
    Matrix.map_zero _ (map_zero _)
  have o : (1 : Matrix (Fin r) (Fin r) E).map (inclR (F := F) w.Completion) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  refine exists_frame_hyp' _ _ hn (I := I.map (inclR (F := F) w.Completion)) ε
    (by rw [← map_add, ← map_one (inclR (F := F) w.Completion)]; norm_num) ?_
    ((up XX).trans z) ((up YY).trans z) ((up YX).trans o) ((up XY).trans o) ((up IX).trans z) ((up IY).trans z)
    ((up XI).trans z) ((up YI).trans z) (up II) hc
  change inclR (F := F) w.Completion (σ (2⁻¹ : E)) = _
  rw [map_inv₀, map_ofNat]

end Lattice

end GlobalTheory.HypAdapt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsAdelicMajorantFrameForCartanInvolutionsStatement
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
theorem _root_.GlobalTheory.T.exists_adelicMajorantFrame_for_cartanInvolutions : ∀ (D : D7) (θ : InfFam D) (A : HSp D) (sA : RealMat A), IsInfFam θ → (∀ τ, IsCartanInv (gramAt D A τ) (sA τ)) → ∃ a : GL (Fin A.rank) (AE D), IsMaj A a ∧ ∀ τ, (compAt θ τ a.1)ᴴ * (gramAt D A τ * sA τ) * compAt θ τ a.1 = 1 := by
  first | exact @GlobalTheory.Core.Rk.MajFrame.exists_maj_cart | exact GlobalTheory.Core.Rk.MajFrame.exists_maj_cart | (intros; apply GlobalTheory.Core.Rk.MajFrame.exists_maj_cart <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCommonLevelCompactTranslatesThetaFunctionStatement
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
theorem _root_.GlobalTheory.T.exists_common_level_compact_translates_thetaFunction : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : WRep S T), IsWeilDatumO ψ S T χS χT om → ∀ K : Set (GA D S), IsCompact K → ∀ f, IsThetaFunO ψ S T f → ∃ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) ∧ ∀ k ∈ K, ∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ S T u (om (k, 1) f) = om (k, 1) f := by
  first | exact @GlobalTheory.Core.Rk.Level.exists_common_level | exact GlobalTheory.Core.Rk.Level.exists_common_level | (intros; apply GlobalTheory.Core.Rk.Level.exists_common_level <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsConjugateWeilDatumHermitianSpaceNegStatement
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
theorem _root_.GlobalTheory.T.exists_conjugate_weilDatum_hermitianSpaceNeg : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (om : WRep A B), IsWeilDatumO ψ A B χA χB om → (∀ f : WO A B → ℂ, IsThetaFunO ψ A B f → IsThetaFunO ψ (negSp A) B fun x => conj (f (-x))) ∧ ∃ om' : WRep (negSp A) B, IsWeilDatumO ψ (negSp A) B χA⁻¹ χB om' ∧ ∀ (g : GA D (negSp A)) (h : GA D B) (f : WO A B → ℂ), IsThetaFunO ψ A B f → om' (g, h) (fun x => conj (f (-x))) = fun x => (((χB (detA A (negEquiv A g)))⁻¹ : Circle) : ℂ) * conj (om (negEquiv A g, h) f (-x)) := by
  first | exact @GlobalTheory.NegWeil.exists_neg_datum | exact GlobalTheory.NegWeil.exists_neg_datum | (intros; apply GlobalTheory.NegWeil.exists_neg_datum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsDoubledUnitaryChartSplitPlace
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)

namespace GlobalTheory.LFun.DblSplit

section Pure

variable {A : Type} [CommRing A] {m ι : Type} [Fintype m] [Fintype ι] [DecidableEq m] [DecidableEq ι] (e : m ⊕ m ≃ ι)

theorem blkGL_mem_diag (a : GL m A) : blkGL e (a, a) ∈ Formalism.UG.stabGL (diagSub A e) :=
  mem_stabGL_diagSub.2 ((keepsDiag_blkMat _).2 rfl)

theorem keepsDiag_conj_iff (a : GL m A) (x : GL ι A) :
    KeepsDiag e ((blkGL e (a, a))⁻¹ * x * blkGL e (a, a)).1 ↔ KeepsDiag e x.1 := by
  rw [← mem_stabGL_diagSub, ← mem_stabGL_diagSub, Subgroup.mul_mem_cancel_right _ (blkGL_mem_diag e a),
    Subgroup.mul_mem_cancel_left _ (inv_mem (blkGL_mem_diag e a))]

theorem det_leviMat_conj (a : GL m A) {x : GL ι A} (hx : KeepsDiag e x.1) :
    (leviMat e ((blkGL e (a, a))⁻¹ * x * blkGL e (a, a)).1).det = (leviMat e x.1).det := by
  let p : Formalism.UG.stabGL (diagSub A e) := ⟨_, blkGL_mem_diag e a⟩
  let q : Formalism.UG.stabGL (diagSub A e) := ⟨x, mem_stabGL_diagSub.2 hx⟩
  change (leviGL e (p⁻¹ * q * p)).1.det = (leviGL e q).1.det
  rw [map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul, Matrix.det_units_conj']

theorem det_quotMat_conj (a : GL m A) {x : GL ι A} (hx : KeepsDiag e x.1) :
    (quotMat e ((blkGL e (a, a))⁻¹ * x * blkGL e (a, a)).1).det = (quotMat e x.1).det := by
  have h1 := ((keepsDiag_conj_iff e a x).2 hx).det_eq
  rw [det_leviMat_conj e a hx, Units.val_mul, Units.val_mul, Matrix.det_units_conj', hx.det_eq] at h1
  have hu : IsUnit (leviMat e x.1).det := by
    have := (Matrix.isUnit_iff_isUnit_det _).1 x.isUnit
    rw [hx.det_eq] at this
    exact isUnit_of_mul_isUnit_left this
  exact (hu.mul_left_cancel h1).symm

omit [Fintype m] [Fintype ι] [DecidableEq m] [DecidableEq ι] in
theorem quotMat_map {B : Type} [CommRing B] (f : A →+* B) (M : Matrix ι ι A) :
    quotMat e (M.map f) = (quotMat e M).map f := by
  ext i j; simp [quotMat, Matrix.toBlocks₁₁, Matrix.toBlocks₂₁]

end Pure

theorem ordL_eq_neg_log {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] (x : K) :
    ordL x = -WithZero.log (Valued.v x) := by
  unfold ordL
  split_ifs with h
  · simp [h]
  · conv_rhs => rw [← WithZero.coe_unzero h]
    rfl

theorem isHermND_dbl {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J) : IsHermND σ (dblGram finSumFinEquiv J) := by
  refine ⟨fun i j => ?_, ?_⟩
  · obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨b, rfl⟩ := finSumFinEquiv.surjective j
    simp only [dblGram, blkMat, Matrix.submatrix_apply, Equiv.symm_apply_apply]
    rcases a with a | a <;> rcases b with b | b <;> simp [hJ.1]
  · rw [dblGram, det_blkMat]
    exact mul_ne_zero hJ.2 (by rw [Matrix.det_neg]; exact mul_ne_zero (pow_ne_zero _ (by simp)) hJ.2)

theorem exists_dbl_chart : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (Q : Matrix (Fin (n + n)) (Fin (n + n)) E) (hQ : Q = dblGram finSumFinEquiv J) (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L], ∀ (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) (h : w.under (𝓞 F) = v), IsSplit (E := E) v → IsSelfDualAt σ J L v → ∀ e : GLoc σ J v ≃* GL (Fin n) (w.adicCompletion E), IsSplitChart σ J L h e → ∃ f : GLoc σ Q v ≃* GL (Fin (n + n)) (w.adicCompletion E), (∀ g, g ∈ KFin σ Q L v ↔ f g ∈ KGL w (n + n)) ∧ (∀ y y', f (ioH _ σ hQ (y, y')) = blkGL finSumFinEquiv (e y, e y')) ∧ (∀ g, g ∈ siegelH (Fv F v) σ Q ↔ KeepsDiag finSumFinEquiv (f g).1) ∧ ∀ p : siegelH (Fv F v) σ Q, toCompl h (aH _ σ Q p).1 = (leviMat finSumFinEquiv (f p).1).det ∧ ∀ (w' : HeightOneSpectrum (𝓞 E)) (h' : w'.under (𝓞 F) = v), w ≠ w' → ordL (toCompl h' (aH _ σ Q p).1) = -ordL (quotMat finSumFinEquiv (f p).1).det := by
  intro F E _ _ _ _ _ σ hc n J hJ Q hQ L _ v w h hv hL e he
  have hQ' : IsHermND σ Q := hQ ▸ isHermND_dbl σ hJ
  have hLL : Submodule.IsLattice E (sumLat finSumFinEquiv L L) := inferInstance
  obtain ⟨f₀, ⟨⟨b, hb, e0⟩, hK⟩, -⟩ := SplitChart.exists_isSplitChart hc hQ' hLL.fg hLL.span_eq_top h hv
    (isSelfDualAt_dbl hQ hL)
  obtain ⟨⟨a, ha, ea⟩, -⟩ := id he
  have hk := hb.inv_mul_mem (GlobalTheory.T.isLatticeFrameAtPlace_directSum_blockDiagonal E w n L a ha)
  have ef : ∀ g, f₀.trans (MulAut.conj (b⁻¹ * blkGL finSumFinEquiv (a, a))⁻¹) g =
      (blkGL finSumFinEquiv (a, a))⁻¹ * locMat σ Q h g * blkGL finSumFinEquiv (a, a) := fun g => by
    rw [MulEquiv.trans_apply, MulAut.conj_apply, e0]; group
  have hP : ∀ p : siegelH (Fv F v) σ Q, KeepsDiag finSumFinEquiv (locMat σ Q h p).1 := fun p =>
    (mem_siegelOf.1 p.2).map _ (toCompl h)
  refine ⟨f₀.trans (MulAut.conj (b⁻¹ * blkGL finSumFinEquiv (a, a))⁻¹), fun g => ?_, fun y y' => ?_, fun g => ?_,
    fun p => ⟨?_, fun w' h' hne => ?_⟩⟩
  · rw [MulEquiv.trans_apply, MulAut.conj_apply, inv_inv, Subgroup.mul_mem_cancel_right _ hk,
      Subgroup.mul_mem_cancel_left _ (inv_mem hk)]
    exact hK g
  · have h1 : locMat σ Q h (ioH _ σ hQ (y, y')) = blkGL finSumFinEquiv (locMat σ J h y, locMat σ J h y') :=
      bc_blkGL finSumFinEquiv (toCompl h) _ _
    rw [ef, h1, ← map_inv, ← map_mul, ← map_mul, ea, ea]
    rfl
  · rw [ef, keepsDiag_conj_iff]
    refine ⟨fun hg => hP ⟨g, hg⟩, fun hg => ?_⟩
    obtain ⟨τ, hτ⟩ := SplitChart.exists_splitPrime_eq hc hv h
    refine GlobalTheory.Core.Rk.IwSplit.mem_siegelH_of_split hc hQ hJ.2 τ (mem_stabGL_diagSub.2 ?_)
    rw [ConjPlace.locMat_eq hc h hτ] at hg
    have h2 := hg.map _ ((ConjPlace.complEquiv hc h hτ).symm : w.adicCompletion E →+* Fv F v)
    convert h2 using 1
    exact Matrix.ext fun i j => ((ConjPlace.complEquiv hc h hτ).symm_apply_apply _).symm
  · rw [ef, det_leviMat_conj _ a (hP p)]
    change toCompl h (leviMat finSumFinEquiv (matHom _ σ Q p).1).det =
      (leviMat finSumFinEquiv ((matHom _ σ Q p).1.map (toCompl h))).det
    rw [leviMat_map, RingHom.map_det, RingHom.mapMatrix_apply]
  · obtain ⟨c, hcv, -, hcc, -⟩ := ConjPlace.exists_conj_chart hc hJ hL hne h h' he
    rw [ef, det_quotMat_conj _ a (hP p)]
    have h1 : (quotMat finSumFinEquiv (locMat σ Q h p).1).det =
        toCompl h (quotMat finSumFinEquiv (matHom _ σ Q p).1).det := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, ← quotMat_map]
      rfl
    have h2 := congrArg (fun y => Valued.v (toCompl h' y)) (sigR_det_quot_mul_aH hQ hJ.2 p)
    simp only [map_mul, map_one, ← hcc, hcv] at h2
    rw [h1, ordL_eq_neg_log, ordL_eq_neg_log, eq_inv_of_mul_eq_one_right h2, WithZero.log_inv]

end GlobalTheory.LFun.DblSplit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsInnerProductSmoothVectorsTensorStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_inner_product_smooth_vectors_tensor : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S), ∃ ipD : SmT M →ₗ[ℂ] SmT M →ₗ⋆[ℂ] ℂ, (∀ v v' : M.Vec, ipD (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ v') = ∏ τ, ⟪(v' τ : M.H τ), (v τ : M.H τ)⟫_ℂ) ∧ (∀ w w', ipD w w' = conj (ipD w' w)) ∧ ∀ w, w ≠ 0 → 0 < (ipD w w).re := by
  first | exact @GlobalTheory.ChainOnto.exists_ipD_smT | exact GlobalTheory.ChainOnto.exists_ipD_smT | (intros; apply GlobalTheory.ChainOnto.exists_ipD_smT <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsOpenPrincipalCongruenceFinitelyManyPrimesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_principal_congruence_finitely_many_primes : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Z : Finset (Pl D.host.E)), ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧ ∀ k ∈ U, Lev.finE V k ∈ Formalism.L2.DIV.St β ∧ ∀ PP ∈ Z, Formalism.L2.DIV.redFn β PP (Lev.finE V k) = 1 := by
  first | exact @GlobalTheory.ChainOnto.LevelOpen.exists_open_princ | exact GlobalTheory.ChainOnto.LevelOpen.exists_open_princ | (intros; apply GlobalTheory.ChainOnto.LevelOpen.exists_open_princ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsOrthDec
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OrthSumExists

def orthDecHsum (D : D7) (A L : HSp D) : OrthDec (GlobalTheory.Doubling.hsum A L) A L where
  iA := (Matrix.fromRows (1 : Matrix (Fin A.rank) (Fin A.rank) D.host.E) (0 : Matrix (Fin L.rank) (Fin A.rank) D.host.E)).submatrix finSumFinEquiv.symm id
  iB := (Matrix.fromRows (0 : Matrix (Fin A.rank) (Fin L.rank) D.host.E) (1 : Matrix (Fin L.rank) (Fin L.rank) D.host.E)).submatrix finSumFinEquiv.symm id
  isoA := by
    rw [GlobalTheory.Doubling.gram_hsum, GlobalTheory.Doubling.blkMat, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.fromCols_mul_fromBlocks, Matrix.fromCols_mul_fromRows]
    simp only [Matrix.conjTranspose_one, Matrix.conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, Matrix.mul_one, add_zero, zero_add]
  isoB := by
    rw [GlobalTheory.Doubling.gram_hsum, GlobalTheory.Doubling.blkMat, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.fromCols_mul_fromBlocks, Matrix.fromCols_mul_fromRows]
    simp only [Matrix.conjTranspose_one, Matrix.conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, Matrix.mul_one, add_zero, zero_add]
  orth := by
    rw [GlobalTheory.Doubling.gram_hsum, GlobalTheory.Doubling.blkMat, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.fromCols_mul_fromBlocks, Matrix.fromCols_mul_fromRows]
    simp only [Matrix.conjTranspose_one, Matrix.conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, Matrix.mul_one, add_zero, zero_add]
  rank_add := rfl

theorem exists_orthDec (D : D7) (A L : HSp D) : Nonempty (Σ V₀ : HSp D, OrthDec V₀ A L) :=
  ⟨⟨GlobalTheory.Doubling.hsum A L, orthDecHsum D A L⟩⟩

end GlobalTheory.OrthSumExists
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRealDiscreteSeriesDataThetaPropertiesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_real_discreteSeries_data_theta_properties : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∃ X : ProvA, ChosenSeries X ∧ Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFirst X ∧ Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisSecond X ∧ Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisUpDownLine X ∧ Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFourth X ∧ Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFifth X := by
  first | exact @GlobalTheory.RealPlaceTheta.exists_record_theta_all | exact GlobalTheory.RealPlaceTheta.exists_record_theta_all | (intros; apply GlobalTheory.RealPlaceTheta.exists_record_theta_all <;> assumption)
end

