import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SquareIntegrableIffExtension
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0237
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesModelIsometryUnitHighestVectorIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0324
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0149
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0032
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0010
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0030
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0226
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0210
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0024
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0331
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0009
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0227
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0228
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0030
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0323
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0078

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetUnitScalarMul
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S
open GlobalTheory.DSSU (SUJ)
open GlobalTheory.SqIntSU (scalarMul unitScalar)

noncomputable section

namespace GlobalTheory.ExtChar

variable {n : ℕ} (ε : Fin n → Bool)

def detRoot (x : UJ ε) : Circle := Circle.exp (Complex.arg (umat x).det / n)

theorem detRoot_pow (hn : n ≠ 0) (x : UJ ε) : ((detRoot ε x : Circle) : ℂ) ^ n = (umat x).det := by
  have h1 := GlobalTheory.SqIntSU.norm_det_umat ε x
  rw [detRoot, Circle.coe_exp, ← Complex.exp_nat_mul]
  have e : (n : ℂ) * (((Complex.arg (umat x).det / n : ℝ)) * Complex.I) =
      (Complex.arg (umat x).det : ℂ) * Complex.I := by
    push_cast
    field_simp
  rw [e]
  conv_rhs => rw [← Complex.norm_mul_exp_arg_mul_I (umat x).det, h1]
  simp

theorem unitScalar_inv (z : Circle) : (unitScalar ε z)⁻¹ = unitScalar ε z⁻¹ := by
  rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← GlobalTheory.SqIntSU.unitScalar_mul, inv_mul_cancel, GlobalTheory.SqIntSU.unitScalar_one]

theorem det_unitScalar_mul (z : Circle) (x : UJ ε) :
    (umat (unitScalar ε z * x)).det = (z : ℂ) ^ n * (umat x).det := by
  show ((z : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) * umat x).det = _
  rw [Matrix.smul_mul, Matrix.one_mul, Matrix.det_smul, Fintype.card_fin]

variable [NeZero n]

def root (x : UJ ε) (j : ZMod n) : Circle := detRoot ε x * ZMod.toCircle j

theorem toCircle_pow (j : ZMod n) : ((ZMod.toCircle j : Circle) : ℂ) ^ n = 1 := by
  have h : (ZMod.toCircle j : Circle) ^ n = 1 := by
    rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, ZMod.natCast_self, zero_mul, AddChar.map_zero_eq_one]
  rw [← Circle.coe_pow, h, Circle.coe_one]

theorem root_pow (x : UJ ε) (j : ZMod n) : ((root ε x j : Circle) : ℂ) ^ n = (umat x).det := by
  rw [root, Circle.coe_mul, mul_pow, detRoot_pow ε (NeZero.ne n), toCircle_pow, mul_one]

def part (x : UJ ε) (j : ZMod n) : SUJ ε :=
  ⟨unitScalar ε (root ε x j)⁻¹ * x, by
    show (umat (unitScalar ε (root ε x j)⁻¹ * x)).det = 1
    rw [det_unitScalar_mul, Circle.coe_inv, inv_pow, root_pow, inv_mul_cancel₀]
    intro h0
    have := GlobalTheory.SqIntSU.norm_det_umat ε x
    rw [h0, norm_zero] at this
    exact zero_ne_one this⟩

def extChar (m : ℤ) (Θ' : SUJ ε → ℂ) (x : UJ ε) : ℂ :=
  (n : ℂ)⁻¹ * ∑ j : ZMod n, ((root ε x j : Circle) : ℂ) ^ m * Θ' (part ε x j)

def cen (j : ZMod n) : SUJ ε :=
  ⟨unitScalar ε (ZMod.toCircle j)⁻¹, by
    show (umat (unitScalar ε (ZMod.toCircle j)⁻¹)).det = 1
    have h := det_unitScalar_mul ε (ZMod.toCircle j)⁻¹ 1
    rw [mul_one] at h
    rw [h, Circle.coe_inv, inv_pow, toCircle_pow, inv_one, one_mul]
    exact Matrix.det_one⟩

theorem suMat_cen (j : ZMod n) :
    GlobalTheory.SUChar.suMat ε (cen ε j) = ((ZMod.toCircle j)⁻¹ : Circle) • (1 : Matrix (Fin n) (Fin n) ℂ) := rfl

def avgChar (m : ℤ) (Θ' : SUJ ε → ℂ) (g : SUJ ε) : ℂ :=
  (n : ℂ)⁻¹ * ∑ j : ZMod n, ((ZMod.toCircle j : Circle) : ℂ) ^ m * Θ' (cen ε j * g)

end GlobalTheory.ExtChar

namespace GlobalTheory.ExtChar

variable {n : ℕ} (ε : Fin n → Bool) [NeZero n]

theorem exists_toCircle_eq (w : Circle) (hw : w ^ n = 1) : ∃ i : ZMod n, ZMod.toCircle i = w := by
  have hu : (toUnits w : Circleˣ) ∈ rootsOfUnity n Circle := by
    rw [mem_rootsOfUnity, ← map_pow, hw, map_one]
  obtain ⟨i, hi⟩ := (bijective_rootsOfUnityAddChar n).2 ⟨_, hu⟩
  refine ⟨i, ?_⟩
  have h := congrArg (fun u : rootsOfUnity n Circle => ((u : Circleˣ) : Circle)) hi
  simpa using h

theorem root_scalarMul (z : Circle) (g : SUJ ε) :
    ∃ i : ZMod n, ∀ j, root ε (scalarMul ε (z, g)) j = z * ZMod.toCircle (i + j) := by
  have hdet : (umat (scalarMul ε (z, g))).det = (z : ℂ) ^ n := by
    rw [GlobalTheory.SqIntSU.scalarMul_apply, det_unitScalar_mul]
    have : (umat (g : UJ ε)).det = 1 := g.2
    rw [this, mul_one]
  have hd : detRoot ε (scalarMul ε (z, g)) ^ n = z ^ n :=
    Circle.ext (by rw [Circle.coe_pow, Circle.coe_pow, detRoot_pow ε (NeZero.ne n), hdet])
  have hw : (detRoot ε (scalarMul ε (z, g)) * z⁻¹) ^ n = 1 := by
    rw [mul_pow, hd, inv_pow, mul_inv_cancel]
  obtain ⟨i, hi⟩ := exists_toCircle_eq (n := n) _ hw
  refine ⟨i, fun j => ?_⟩
  rw [root, AddChar.map_add_eq_mul, hi, mul_comm (detRoot ε _) z⁻¹, mul_assoc, mul_inv_cancel_left]

theorem part_scalarMul (z : Circle) (g : SUJ ε) (i : ZMod n)
    (h : ∀ j, root ε (scalarMul ε (z, g)) j = z * ZMod.toCircle (i + j)) (j : ZMod n) :
    part ε (scalarMul ε (z, g)) j = cen ε (i + j) * g := by
  apply Subtype.ext
  show unitScalar ε (root ε (scalarMul ε (z, g)) j)⁻¹ * (unitScalar ε z * (g : UJ ε)) =
    unitScalar ε (ZMod.toCircle (i + j))⁻¹ * (g : UJ ε)
  have e : (z * ZMod.toCircle (i + j))⁻¹ * z = (ZMod.toCircle (i + j))⁻¹ := by
    rw [mul_inv, mul_comm z⁻¹, mul_assoc, inv_mul_cancel, mul_one]
  rw [h, ← mul_assoc, ← GlobalTheory.SqIntSU.unitScalar_mul, e]

theorem extChar_scalarMul (m : ℤ) (Θ' : SUJ ε → ℂ) (z : Circle) (g : SUJ ε) :
    extChar ε m Θ' (scalarMul ε (z, g)) = (z : ℂ) ^ m * avgChar ε m Θ' g := by
  obtain ⟨i, hi⟩ := root_scalarMul ε z g
  rw [extChar, avgChar]
  simp only [hi, part_scalarMul ε z g i hi, Circle.coe_mul, mul_zpow, Finset.mul_sum]
  exact Fintype.sum_equiv (Equiv.addLeft i) _ _ fun j => by simp only [Equiv.coe_addLeft]; ring

end GlobalTheory.ExtChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagonalUnitaryAntidiagonalFormExponentBalance
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem diag_unitary_exp_sym {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (c : L →+* L) (q : ℕ)
    (hU : IsUnramInv ϖ c q) (r : ℕ) (d : Fin r → ℤ) (t : GU c r)
    (ht : t.1.1 = Matrix.diagonal (fun i => ϖ ^ d i)) :
    ∑ i, max (-d i) 0 = ∑ i, max (d i) 0 := by
  obtain ⟨_, _, hcϖ, hv, _⟩ := hU
  have hmem := t.2
  change Formalism.UG.cT c (t.1.1) * Formalism.UG.antiJ L r * t.1.1 = Formalism.UG.antiJ L r at hmem
  rw [ht] at hmem
  have hcT : Formalism.UG.cT c (Matrix.diagonal (fun i => ϖ ^ d i)) = Matrix.diagonal (fun i => ϖ ^ d i) := by
    ext i j
    simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.diagonal_apply]
    by_cases h : i = j
    · subst h; simp [map_zpow₀, hcϖ]
    · simp [h, Ne.symm h]
  rw [hcT] at hmem
  have hϖ : ϖ ≠ 0 := by
    intro h0; rw [h0, map_zero] at hv; exact WithZero.zero_ne_coe hv
  have key : ∀ i : Fin r, d (Fin.rev i) = -d i := by
    intro i
    have e := congrArg (fun M => M i (Fin.rev i)) hmem
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal] at e
    have hJ : Formalism.UG.antiJ L r i (Fin.rev i) = 1 := by
      simp only [Formalism.UG.antiJ, Fin.val_rev]; rw [if_pos]; omega
    rw [hJ, mul_one] at e
    rw [← zpow_add₀ hϖ] at e
    have e2 := congrArg (fun x => Valued.v x) e
    simp only [map_zpow₀, map_one, hv] at e2
    rw [← WithZero.coe_zpow, ← ofAdd_zsmul] at e2
    have e3 : (d i + d (Fin.rev i)) • (-1 : ℤ) = 0 := by
      have := WithZero.coe_injective e2
      exact Multiplicative.ofAdd.injective (this.trans ofAdd_zero.symm)
    simp at e3
    omega
  calc ∑ i, max (-d i) 0 = ∑ i, max (d (Fin.rev i)) 0 := by simp [key]
    _ = ∑ i, max (d i) 0 := Equiv.sum_comp Fin.revPerm (fun i => max (d i) 0)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesModelIsometryUnitHighestVectorIffStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discreteSeriesModelIsometry_unit_highestVector_iff : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau) (p q : ℕ) (T : GrpData p q) (R : DSRep T) (lam : Ix p q → ℚ) (c : ℚ) (br cj : Bool) (e : Ix p q ≃ Fin V.rank) (m : ℤ) (U : M.H τ → R.U.H), IsParam lam → IsOrd (M.ε τ) (M.lam τ) lam c (sg br cj) e → (m : ℚ) = 2 * c → Comparison₂ R M τ br cj e m U → Module.finrank ℂ ↥(hwSub R.HK.act (blattner lam)) = 1 → ∀ x v, U x = R.ι v → (IsHighestUnit (M.ε τ) (M.lam τ) (M.σ τ) x ↔ UnitHW R (blattner lam) v) := by
  first | exact @GlobalTheory.ArchRec.HighTie.highestUnit_iff | exact GlobalTheory.ArchRec.HighTie.highestUnit_iff | (intros; apply GlobalTheory.ArchRec.HighTie.highestUnit_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfSEEofTT
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Cx Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Twist.SeeIsoRow

variable {D : D7} {S : D.what₂.Tau → SPar}

theorem sEEofTT_apply {M : DSModel (D.sp.Y 0) S} {μ : Measure (GA D (D.sp.Y 0))} {𝓕 : Set (GA D (D.sp.Y 0))}
    {E : Submodule ℂ (MMap M)} {St : Formalism.L2.SG.HidaSetting.HidaSetting D} {Gd : GoodOp St} {ι : GA D (D.sp.Y 0) ≃* St.B.I.GA}
    {t : GA D (D.sp.Y 0)} {c : ℝ} (hE : EvalTieT M μ 𝓕 E St Gd ι t c) (T : E) :
    sEEofTT M μ 𝓕 E St Gd ι t c T = conjHH St Gd (hE.choose_spec.2.choose T) := by
  unfold sEEofTT
  simp only [dif_pos hE]
  rfl

theorem norm_sq_sEEofTT {M : DSModel (D.sp.Y 0) S} {μ : Measure (GA D (D.sp.Y 0))} {𝓕 : Set (GA D (D.sp.Y 0))}
    {E : Submodule ℂ (MMap M)} {St : Formalism.L2.SG.HidaSetting.HidaSetting D} {Gd : GoodOp St} {ι : GA D (D.sp.Y 0) ≃* St.B.I.GA}
    {t : GA D (D.sp.Y 0)} {c : ℝ} (hE : EvalTieT M μ 𝓕 E St Gd ι t c) (T : E) :
    ‖sEEofTT M μ 𝓕 E St Gd ι t c T‖ ^ 2 = c * (ipM M μ 𝓕 (T : MMap M) (T : MMap M)).re := by
  have h := congrArg norm (sEEofTT_apply hE T)
  rw [LinearIsometry.norm_map] at h
  rw [h]
  exact (hE.choose_spec.2.choose_spec T).2

theorem eq_zero_of_sEEofTT {M : DSModel (D.sp.Y 0) S} {μ : Measure (GA D (D.sp.Y 0))} {𝓕 : Set (GA D (D.sp.Y 0))}
    {E : Submodule ℂ (MMap M)} {St : Formalism.L2.SG.HidaSetting.HidaSetting D} {Gd : GoodOp St} {ι : GA D (D.sp.Y 0) ≃* St.B.I.GA}
    {t : GA D (D.sp.Y 0)} {c : ℝ} (hE : EvalTieT M μ 𝓕 E St Gd ι t c) (T : E)
    (h : ‖sEEofTT M μ 𝓕 E St Gd ι t c T‖ = 0) : T = 0 := by
  have h1 := congrArg norm (sEEofTT_apply hE T)
  rw [LinearIsometry.norm_map] at h1
  have h2 : ‖hE.choose_spec.2.choose T‖ = 0 := h1.symm.trans h
  exact (LinearEquiv.map_eq_zero_iff _).1 (norm_eq_zero.1 h2)

theorem seeIso_row : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Gd : GoodOp X) (hK : X.LevelSubgroupCharacter) (Zs : DefSub A3.fam3.amb3) (Dc : DefCols (A3.side3 F.P1 F.ψ1 Zs)) (wdD : Dc.Mem → D.what₂.Word) (pw : ∀ x, PerW X hK (wdD x)) (bR : ∀ x, Fin (Dc.a x) → (D.mem (wdD x)).A.Mram) (sEE : (R.toCx3 F).EE →ₗ⋆[ℂ] (F.fc (R.toCx3 F).zs).Sp.HH) (sEEc : Tw (twAt D.what₂.embLL A3.A.v0) R.HE.H →ₗ⋆[ℂ] Tw (twAt D.what₂.embLL A3.A.v0) (HHX X)) (ι : GA D (Yc D 0) ≃* X.B.I.GA) (tS : GA D (Yc D 0)) (cS κS : ℝ) (uS : ℂ), R.toRealDat.IsModels → (R.toCx3 F).zs = Zs → F.Dc Zs = Dc → HEq (F.Sp Zs) (spOf (X := X) (twAt D.what₂.embLL A3.A.v0) Dc hK Gd wdD pw bR) → HEq sEE sEEc → EvalTieT (R.MY 0) R.ν0 R.fd0 (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) X Gd ι tS cS → ‖uS‖ = 1 → (∀ (x : Tw (twAt D.what₂.embLL A3.A.v0) R.HE.H) (hx : R.HE.e (Tw.out x) ∈ (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true))), sEEc x = Tw.mk (twAt D.what₂.embLL A3.A.v0) ((uS * (κS : ℂ)) • (sEEofTT (R.MY 0) R.ν0 R.fd0 (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) X Gd ι tS cS) ⟨R.HE.e (Tw.out x), hx⟩)) → (0 < κS ∧ ((∃ κ' : ℝ, 0 < κ' ∧ ∀ (x : Tw (twAt D.what₂.embLL A3.A.v0) R.HE.H) (hx : R.HE.e (Tw.out x) ∈ (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true))), ‖(κ' : ℂ) • (sEEofTT (R.MY 0) R.ν0 R.fd0 (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) X Gd ι tS cS) ⟨R.HE.e (Tw.out x), hx⟩‖ = ‖x‖) → ∀ (x : Tw (twAt D.what₂.embLL A3.A.v0) R.HE.H), R.HE.e (Tw.out x) ∈ (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) → RealDat.nP F.lv2 true * ‖sEEc x‖ ^ 2 = ‖x‖ ^ 2)) → (R.toCx3 F).SEEIso sEE := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F X Gd hK Zs Dc wdD pw bR sEE sEEc ι tS cS κS uS hM hzs hDc hSp hh hE _ hDef hK'
  subst hzs
  subst hDc
  have hSp' := eq_of_heq hSp
  have hHE := hM.HE
  have hle := (GlobalTheory.T.goodRows_level_sub_principalLevel_hilbertModel R.toRealDat hM).1 (R.toRealDat.levR F.lv2 true)
  have key : ∀ (x : Tw (twAt D.what₂.embLL A3.A.v0) R.HE.H)
      (hx : R.HE.e (Tw.out x) ∈ R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)),
      ‖sEEofTT (R.MY 0) R.ν0 R.fd0 (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) X Gd ι tS cS ⟨R.HE.e (Tw.out x), hx⟩‖ ^ 2 = cS * ‖x‖ ^ 2 := by
    intro x hx
    rw [norm_sq_sEEofTT hE]
    congr 1
    show (ipM (R.MY 0) R.ν0 R.fd0 (R.HE.e (Tw.out x)) (R.HE.e (Tw.out x))).re = ‖Tw.out x‖ ^ 2
    rw [← hHE.2.2]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) (Tw.out x)
  have hex : ∃ κ' : ℝ, 0 < κ' ∧ ∀ (x : Tw (twAt D.what₂.embLL A3.A.v0) R.HE.H)
      (hx : R.HE.e (Tw.out x) ∈ R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)),
      ‖(κ' : ℂ) • sEEofTT (R.MY 0) R.ν0 R.fd0 (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) X Gd ι tS cS ⟨R.HE.e (Tw.out x), hx⟩‖ = ‖x‖ := by
    by_cases hc : 0 < cS
    · have hsp : 0 < Real.sqrt cS := Real.sqrt_pos.2 hc
      refine ⟨(Real.sqrt cS)⁻¹, inv_pos.2 hsp, fun x hx => ?_⟩
      have h1 : ‖sEEofTT (R.MY 0) R.ν0 R.fd0 (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) X Gd ι tS cS ⟨R.HE.e (Tw.out x), hx⟩‖ = Real.sqrt cS * ‖x‖ := by
        rw [← pow_left_inj₀ (norm_nonneg _) (mul_nonneg hsp.le (norm_nonneg _)) two_ne_zero, key x hx, mul_pow,
          Real.sq_sqrt hc.le]
      rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_pos.2 hsp).le, h1, ← mul_assoc,
        inv_mul_cancel₀ hsp.ne', one_mul]
    · refine ⟨1, one_pos, fun x hx => ?_⟩
      have h2 : ‖sEEofTT (R.MY 0) R.ν0 R.fd0 (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) X Gd ι tS cS ⟨R.HE.e (Tw.out x), hx⟩‖ ^ 2 ≤ 0 := by
        rw [key x hx]
        exact mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hc) (sq_nonneg _)
      have h0 : ‖sEEofTT (R.MY 0) R.ν0 R.fd0 (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) X Gd ι tS cS ⟨R.HE.e (Tw.out x), hx⟩‖ = 0 :=
        pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm h2 (sq_nonneg _))
      have hT := eq_zero_of_sEEofTT hE _ h0
      have he0 : R.HE.e (Tw.out x) = 0 := congrArg Subtype.val hT
      have hx0 : Tw.out x = 0 := (map_eq_zero_iff _ hHE.1).1 he0
      rw [norm_smul, h0, mul_zero]
      show 0 = ‖Tw.out x‖
      rw [hx0, norm_zero]
  have hn := hK'.2 hex
  refine GlobalTheory.Mem.SJ.RowIso.clauses (twAt D.what₂.embLL A3.A.v0) (F.Dc (R.toCx3 F).zs) hK Gd wdD pw bR (F.Sp (R.toCx3 F).zs)
    hSp' ((R.toCx3 F).EEl true) ((R.toCx3 F).nP true) sEE sEEc hh (fun e he => hn e he) (fun e he => ?_) ?_
  · refine (congrArg (fun y : Tw (twAt D.what₂.embLL A3.A.v0) (HHX X) =>
      ((Tw.out y : HHX X) : L2X X) ∈ goodSub X Gd) (hDef e he)).mpr ?_
    show (((uS * (κS : ℂ)) • sEEofTT (R.MY 0) R.ν0 R.fd0 (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) X Gd ι tS cS ⟨R.HE.e (Tw.out e), he⟩ : HHX X) : L2X X) ∈ goodSub X Gd
    rw [Submodule.coe_smul]
    refine Submodule.smul_mem _ _ ?_
    unfold sEEofTT
    rw [dif_pos hE]
    exact (mem_EEC X Gd _).1 (hE.choose_spec.2.choose _).2
  · refine (GlobalTheory.Mem.SJ.RowIso.finrank_of_evalTieT hE).trans ?_
    refine Eq.symm ((GlobalTheory.Mem.SJ.RowIso.finrank_twSub (E := R.HE.H) (twAt D.what₂.embLL A3.A.v0)
      ((R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)).comap R.HE.e)).trans ?_)
    refine GlobalTheory.Mem.SJ.RowIso.finrank_comap_of_le_range _ hHE.1 _ ?_
    rw [hHE.2.1]
    exact hle

end GlobalTheory.Twist.SeeIsoRow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyLocalIntegersIffPowerBasisCoordsAllStatement
section
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_localIntegers_iff_powerBasisCoords_all : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (r : ℕ) (P : PPol σ r), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ∀ y : Fv F v ⊗[F] Fld P, y ∈ intLoc F (Fld P) v ↔ GlobalTheory.TrUnitLat.coordEquiv P (Fv F v) y ∈ latLoc F (stdLattice E r) v := by
  first | exact @GlobalTheory.TrUnitLat.eventually_mem_intLoc_iff_coordEquiv_mem_all | exact GlobalTheory.TrUnitLat.eventually_mem_intLoc_iff_coordEquiv_mem_all | (intros; apply GlobalTheory.TrUnitLat.eventually_mem_intLoc_iff_coordEquiv_mem_all <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExThOfChain
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ProjectedLift

theorem ex_Th_of_chain : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → R.grp_record → R.ex_Th := by
  intro D G _ _ Pl0 T A Ks _ _ _ R h0 hf hm hr t
  obtain ⟨Th, hTh⟩ := GlobalTheory.ProjectedLift.exists_chain_Th D G Pl0 T A Ks R h0 hf hm hr
  exact ⟨Th t, fun x => hTh t x⟩

end GlobalTheory.ProjectedLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCartanSystemStatement
section
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar IsSqIntIrr)
open GlobalTheory.Orb (ujMat ujRep CcMat IsBiFinite IsUnitEquiv IsCharFn IsRegSS cent HasOrbInt quotMeas)
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible)
open GlobalTheory.HCChar GlobalTheory.Published GlobalTheory.Published.Langlands
open scoped InnerProductSpace Topology ENNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cartan_system : ∀ (n : ℕ) (ε : Fin n → Bool), ∃ 𝒯 : Finset (Subgroup (UJ ε)), IsCartanSystem 𝒯 := by
  first | exact @GlobalTheory.CartanFinite.exists_isCartanSystem | exact GlobalTheory.CartanFinite.exists_isCartanSystem | (intros; apply GlobalTheory.CartanFinite.exists_isCartanSystem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCoverKFinitePairingOfRealIntertwinerStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt GlobalTheory.Chain.RealLine
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cover_kFinite_pairing_of_realIntertwiner : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (τ : D.what₂.Tau) (p q r s : ℕ) (T₁ : GrpData p q) (T₂ : GrpData r s) (R₁ : DSRep T₁) (R₂ : DSRep T₂) (e : Ix p q ≃ Fin V.rank) (e' : Ix r s ≃ Fin W.rank) (m m' : ℤ) (aS aT : ℚ) (U : M.H τ ≃ₗᵢ[ℂ] R₁.U.H) (U' : M'.H τ ≃ₗᵢ⋆[ℂ] R₂.U.H) (κ : LPol W.rank V.rank ≃ₗ[ℂ] Pol p q r s) (A : LPol W.rank V.rank →ₗ[ℂ] M'.sm τ →ₗ[ℂ] M.H τ), (m : ℚ) = 2 * aT → (m' : ℚ) = 2 * aS → GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.Matches R₁ M τ (GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.barMat e) m U → GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.Matches R₂ M' τ (GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.plainMat e') m' U' → IsPolyIso (M.ε τ) (M'.ε τ) e e' κ → LocW M M' τ aS aT A → ∃ B : Pol p q r s →ₗ[ℂ] R₂.HK.V →ₛₗ[starRingEnd ℂ] R₁.HK.V, CoverW R₁ R₂ B ∧ ∀ (P : LPol W.rank V.rank) (x : R₂.HK.V) (y : M'.sm τ), U' (y : M'.H τ) = R₂.ι x → R₁.ι (B (κ P) x) = U (A P y) := by
  first | exact @GlobalTheory.Chain.RealLine.CoverFromLocal.exists_coverW | exact GlobalTheory.Chain.RealLine.CoverFromLocal.exists_coverW | (intros; apply GlobalTheory.Chain.RealLine.CoverFromLocal.exists_coverW <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFockPolynomialIsoGradedIsometryStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fockPolynomialIso_graded_isometry : ∀ (p q r s a b : ℕ) (ε : Fin a → Bool) (ε' : Fin b → Bool) (e : Ix p q ≃ Fin a) (e' : Ix r s ≃ Fin b), SignCompat ε e → SignCompat ε' e' → ∃ κ : LPol b a ≃ₗ[ℂ] Pol p q r s, IsPolyIso ε ε' e e' κ ∧ Graded κ ∧ ∀ P Q, fockIp (κ P) (κ Q) = fockIp P Q := by
  first | exact @GlobalTheory.ArchRec.SignedRename.exists_isPolyIso_graded_isometry | exact GlobalTheory.ArchRec.SignedRename.exists_isPolyIso_graded_isometry | (intros; apply GlobalTheory.ArchRec.SignedRename.exists_isPolyIso_graded_isometry <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFockPolynomialOperatorHeisenbergDerivativeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fockPolynomial_operator_heisenberg_derivative : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (τ : D.what₂.Tau), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (sS frS : Mn S.rank) (εS : Fin S.rank → Bool) (sT frT : Mn T.rank) (εT : Fin T.rank → Bool), IsFrameOf (gramAt D S τ) sS εS frS → IsFrameOf (gramAt D T τ) sT εT frT → ∀ z : Matrix (Fin T.rank) (Fin S.rank) ℂ, ∃ L : Module.End ℂ (LPol T.rank S.rank), ∀ f, IsThetaFunO ψ S T f → IsFockVacAt (heisO ψ S T) θ τ (cplxO sS sT) f → ∀ P, dRho (heisO ψ S T) θ τ z (ptAt ψ θ S T τ sS sT frS⁻¹ frT⁻¹ f P) = ptAt ψ θ S T τ sS sT frS⁻¹ frT⁻¹ f (L P) := by
  first | exact @GlobalTheory.ArchRec.DerFock.exists_dRho_ptAt | exact GlobalTheory.ArchRec.DerFock.exists_dRho_ptAt | (intros; apply GlobalTheory.ArchRec.DerFock.exists_dRho_ptAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFrameReorderingLevelDataStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frame_reordering_levelData : ∀ {D : D7} {T : Type} (Lc : LevCh D T) (P P' : LevelP Lc.Pg D.R.r ℂ) (π : Equiv.Perm (Fin D.R.r)), (∀ g, g ∈ P.H ↔ reord π g ∈ P'.H) → (∀ g hg hg', P.chi ⟨g, hg⟩ = P'.chi ⟨reord π g, hg'⟩) → ∀ β₃ : GL (Fin (Yc D 0).rank) (EAf D), IsFrame β₃ (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → ∃ β₂ : GL (Fin (Yc D 0).rank) (EAf D), IsFrame β₂ (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) ∧ ∀ κ : GA D (Yc D 0), (κ ∈ levS (Yc D 0) β₂ (Lc.dat0 P) ↔ κ ∈ levS (Yc D 0) β₃ (Lc.dat0 P')) ∧ levChi (Yc D 0) β₂ (Lc.dat0 P) κ = levChi (Yc D 0) β₃ (Lc.dat0 P') κ := by
  first | exact @GlobalTheory.SeeConjReord.exists_frame_reord | exact GlobalTheory.SeeConjReord.exists_frame_reord | (intros; apply GlobalTheory.SeeConjReord.exists_frame_reord <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHoweDualityIntertwinerUnitaryPairLocal
section
open Formalism.MainNotions.S Matrix GlobalTheory.CompactHowe
open scoped TensorProduct InnerProductSpace

noncomputable section

namespace GlobalTheory.CompactHowe.Lift

open MvPolynomial

theorem map_star_subst2 {N n : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (B : Matrix (Fin n) (Fin n) ℂ)
    (P : MvPolynomial (Fin N × Fin n) ℂ) :
    MvPolynomial.map (starRingEnd ℂ) (subst2 A B P) =
      subst2 (A.map star) (B.map star) (MvPolynomial.map (starRingEnd ℂ) P) := by
  have key : (MvPolynomial.map (starRingEnd ℂ)).comp (subst2 A B).toRingHom =
      (subst2 (A.map star) (B.map star)).toRingHom.comp (MvPolynomial.map (starRingEnd ℂ)) := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun p => ?_)
    · simp
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_X, subst2_X,
        map_sum, map_mul, map_C, Matrix.map_apply]
      rfl
  exact congrArg (fun f => f P) key

theorem map_star_map_star_poly {N n : ℕ} (P : MvPolynomial (Fin N × Fin n) ℂ) :
    MvPolynomial.map (starRingEnd ℂ) (MvPolynomial.map (starRingEnd ℂ) P) = P := by
  rw [MvPolynomial.map_map]
  have : (starRingEnd ℂ).comp (starRingEnd ℂ) = RingHom.id ℂ := RingHom.ext fun z => by simp
  rw [this, MvPolynomial.map_id]

theorem map_star_smul {N n : ℕ} (c : ℂ) (P : MvPolynomial (Fin N × Fin n) ℂ) :
    MvPolynomial.map (starRingEnd ℂ) (c • P) = star c • MvPolynomial.map (starRingEnd ℂ) P := by
  rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul, map_C]
  rfl

end GlobalTheory.CompactHowe.Lift

namespace GlobalTheory.CompactHowe

open Contraction Lift

theorem exists_local_lift : ∀ (N n : ℕ) (hn : n ≤ N) (ν : Fin N → ℕ) (x₁ x₃ : ℤ) (Λ : Fin n → ℝ) (Λ' : Fin N → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [FiniteDimensional ℂ H'] (σ' : Matrix (Fin N) (Fin N) ℂ → (H' →L[ℂ] H')), Antitone ν → (∀ b : Fin N, n ≤ (b : ℕ) → ν b = 0) → (∀ a, Λ a = -(x₃ : ℝ) + ν (Fin.castLE hn a)) → (∀ b, Λ' b = (x₁ : ℝ) + ν b) → Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset (Formalism.MainNotions.S.allPos n)) σ → Formalism.MainNotions.S.IsKTypeOf (Formalism.MainNotions.S.allPos n) σ Λ ⊤ → Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset (Formalism.MainNotions.S.allPos N)) σ' → Formalism.MainNotions.S.IsKTypeOf (Formalism.MainNotions.S.allPos N) σ' Λ' ⊤ → ∃ I : MvPolynomial (Fin N × Fin n) ℂ →ₗ[ℂ] H →ₗ[ℂ] H', I ≠ 0 ∧ ∀ h ∈ Formalism.MainNotions.S.UJset (Formalism.MainNotions.S.allPos N), ∀ g ∈ Formalism.MainNotions.S.UJset (Formalism.MainNotions.S.allPos n), ∀ P v, I ((h.det ^ x₁ * g.det ^ x₃) • GlobalTheory.CompactHowe.subst2 h (g⁻¹)ᵀ P) (σ g v) = σ' h (I P v) := by
  intro N n hn ν x₁ x₃ Λ Λ' H _ _ _ σ H' _ _ _ σ' hν hν0 hΛ hΛ' hσ hK hσ' hK'
  obtain ⟨hτ, hτK⟩ := GlobalTheory.T.detTwistedConjugate_isKTypeOf_reversed n Λ 0 H σ hσ hK
  obtain ⟨hτ', hτK'⟩ := GlobalTheory.T.detTwistedConjugate_isKTypeOf_reversed N Λ' 0 H' σ' hσ' hK'
  obtain ⟨I₀, hI₀0, hI₀⟩ := GlobalTheory.T.exists_local_howe_contraction_compact_unitary N n hn ν x₁ x₃ (fun a => ((0 : ℤ) : ℝ) - Λ (Fin.rev a))
    (fun b => ((0 : ℤ) : ℝ) - Λ' (Fin.rev b)) H (fun g => g.det ^ (0 : ℤ) • σ (g.map star)) H'
    (fun g => g.det ^ (0 : ℤ) • σ' (g.map star)) hν hν0
    (fun a => by simp only [hΛ, Int.cast_zero]; ring) (fun b => by simp only [hΛ', Int.cast_zero]; ring)
    hτ hτK hτ' hτK'
  let cj : MvPolynomial (Fin N × Fin n) ℂ →+* MvPolynomial (Fin N × Fin n) ℂ :=
    MvPolynomial.map (starRingEnd ℂ)
  refine ⟨{ toFun := fun P => LinearMap.adjoint (I₀ (cj P)),
            map_add' := fun P Q => by simp only [map_add]
            map_smul' := fun c P => by
              simp only [cj, map_star_smul, map_smul, LinearEquiv.map_smulₛₗ, RingHom.id_apply]
              simp }, fun h0 => hI₀0 ?_, fun h hh g hg P v => ?_⟩
  · refine LinearMap.ext fun P => ?_
    have := congrArg (fun f => f (cj P)) h0
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.zero_apply, cj, map_star_map_star_poly] at this
    simpa using this
  · have hQ : cj ((h.det ^ x₁ * g.det ^ x₃) • subst2 h (g⁻¹)ᵀ P) =
        ((h.map star).det ^ x₁ * (g.map star).det ^ x₃) • subst2 (h.map star) ((g.map star)⁻¹)ᵀ (cj P) := by
      simp only [cj]
      rw [map_star_smul, map_star_subst2, Contraction.inv_transpose hg,
        Contraction.inv_transpose (map_star_mem hg)]
      simp only [Contraction.det_map_star, star_mul', star_zpow₀]
    have key := hI₀ (h.map star) (map_star_mem hh) (g.map star) (map_star_mem hg) (cj P)
    simp only [zpow_zero, one_smul, map_star_map_star] at key
    show LinearMap.adjoint (I₀ (cj _)) (σ g v) = σ' h (LinearMap.adjoint (I₀ (cj P)) v)
    rw [hQ]
    refine ext_inner_left ℂ fun w => ?_
    obtain ⟨u, rfl⟩ : ∃ u, σ' h u = w := by
      refine ⟨σ' hᴴ w, ?_⟩
      have := hσ'.1.2 h hh _ (conjTranspose_mem hh)
      rw [mul_eq_one_comm.1 ((mem_iff h).1 hh), hσ'.1.1] at this
      simpa using (congrArg (fun f => f w) this).symm
    have iso1 : ∀ a b : H, inner ℂ (σ g a) (σ g b) = inner ℂ a b := fun a b =>
      (LinearIsometry.mk (σ g : H →ₗ[ℂ] H) (hσ.2.1 g hg)).inner_map_map a b
    have iso2 : ∀ a b : H', inner ℂ (σ' h a) (σ' h b) = inner ℂ a b := fun a b =>
      (LinearIsometry.mk (σ' h : H' →ₗ[ℂ] H') (hσ'.2.1 h hh)).inner_map_map a b
    rw [LinearMap.adjoint_inner_right, key u, iso1, iso2, LinearMap.adjoint_inner_right]

end GlobalTheory.CompactHowe
end
end

