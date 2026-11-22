import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0317
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0271
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1559
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0072
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactSubgroupsActOnFockVectorsAllSignatures
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0032
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0010
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Formalism.LocalToGlobal.Columns.AdelicLemmas
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0813
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0442
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0029
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0082
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAnti
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0438
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0444
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0443
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0428

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousSmulMx
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AnnNbhdCpt

variable {D : D7}

theorem pairA_add_one : pairA D.host.F 0 1 + pairA D.host.F 1 0 = 1 :=
  GlobalTheory.AdelicCoord.af_ext (by rw [map_add, map_one, GlobalTheory.AdelicCoord.fstA_pairA, GlobalTheory.AdelicCoord.fstA_pairA, zero_add])
    (by rw [map_add, map_one, GlobalTheory.AdelicCoord.sndA_pairA, GlobalTheory.AdelicCoord.sndA_pairA, add_zero])

theorem pairA_mul_pairA : pairA D.host.F 1 0 * pairA D.host.F 0 1 = 0 :=
  GlobalTheory.AdelicCoord.af_ext (by rw [map_mul, map_zero, GlobalTheory.AdelicCoord.fstA_pairA, GlobalTheory.AdelicCoord.fstA_pairA, mul_zero])
    (by rw [map_mul, map_zero, GlobalTheory.AdelicCoord.sndA_pairA, GlobalTheory.AdelicCoord.sndA_pairA, zero_mul])

theorem smul_fin_add (z : AE D) : pairA D.host.F 0 1 • z + pairA D.host.F 1 0 • z = z := by
  rw [← add_smul, pairA_add_one, one_smul]

theorem smul_fin_of_inf (z : AE D) (h : infPart D z = 0) : pairA D.host.F 0 1 • z = z := by
  have h' := (GlobalTheory.AdelicCoord.infPart_eq_zero_iff D z).1 h
  have := smul_fin_add z
  rwa [h', add_zero] at this

theorem infPart_smul_fin (z : AE D) : infPart D (pairA D.host.F 0 1 • z) = 0 := by
  rw [GlobalTheory.AdelicCoord.infPart_eq_zero_iff, smul_smul, pairA_mul_pairA, zero_smul]

theorem mem_idAt_true (z : AE D) : z ∈ idAt D (fun _ => True) ↔ infPart D z = 0 := by
  unfold idAt
  rw [Ideal.mem_inf, Ideal.mem_iInf, RingHom.mem_ker]
  exact ⟨fun h => h.1, fun h => ⟨h, fun w => absurd trivial w.2⟩⟩

theorem mxAt_true_iff {m n : ℕ} (x : Mx D m n) : MxAt (fun _ => True) x ↔ pairA D.host.F 1 0 • x = 0 := by
  unfold MxAt
  rw [← Matrix.ext_iff]
  simp only [Matrix.smul_apply, Matrix.zero_apply, mem_idAt_true, GlobalTheory.AdelicCoord.infPart_eq_zero_iff]

theorem continuous_smul_mx {m n : ℕ} (c : AF D.host.F) : Continuous fun x : Mx D m n => c • x := by
  haveI := (Formalism.IndefR.Eqv.ae_facts D).1
  refine continuous_pi fun i => continuous_pi fun j => ?_
  show Continuous fun x : Mx D m n => c • x i j
  simp only [Algebra.smul_def]
  exact continuous_const.mul (continuous_id.matrix_elem i j)

def annSet (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (Γ : AddSubgroup (WO S T)) : Set (WO S T) :=
  {u' | MxAt (fun _ => True) u' ∧ ∀ u ∈ Γ, ψ (symplO S T u u') = 1}

set_option maxHeartbeats 1000000 in

theorem isCompact_annSet (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D)
    (Γ : AddSubgroup (WO S T)) (U : Set (WO S T)) (hU : IsOpen U) (h0 : (0 : WO S T) ∈ U)
    (hUΓ : ∀ a ∈ U, MxAt (fun _ => True) a → a ∈ Γ) : IsCompact (annSet ψ Γ) := by
  obtain ⟨h1, h2, -⟩ := Formalism.IndefR.Eqv.ae_facts D
  let e : AF D.host.F := pairA D.host.F 0 1
  let V : AddSubgroup (WO S T) :=
    { carrier := {u | e • u ∈ Γ}
      add_mem' := fun {a b} ha hb => by show e • (a + b) ∈ Γ; rw [smul_add]; exact add_mem ha hb
      zero_mem' := by show e • (0 : WO S T) ∈ Γ; rw [smul_zero]; exact zero_mem _
      neg_mem' := fun {a} ha => by show e • (-a) ∈ Γ; rw [smul_neg]; exact neg_mem ha }
  have hfinE : ∀ u : WO S T, MxAt (fun _ => True) (e • u) := fun u i j => by
    rw [mem_idAt_true, Matrix.smul_apply]; exact infPart_smul_fin _
  have hVo : IsOpen (V : Set (WO S T)) := by
    refine AddSubgroup.isOpen_of_mem_nhds V (g := 0) ?_
    refine Filter.mem_of_superset (((continuous_smul_mx e).isOpen_preimage U hU).mem_nhds (by
      show e • (0 : WO S T) ∈ U; rw [smul_zero]; exact h0)) fun u hu => hUΓ _ hu (hfinE u)
  obtain ⟨Q, hQc, hQ⟩ := GlobalTheory.AnnihMat.annihilator_inBox_full D ψ hψ S T V hVo
  have hfix : ∀ u : WO S T, MxAt (fun _ => True) u → e • u = u := fun u hu => by
    ext i j
    rw [Matrix.smul_apply]
    exact smul_fin_of_inf _ ((mem_idAt_true _).1 (hu i j))
  have hsub : annSet ψ Γ ⊆ (fun x : WO S T => e • x) '' Q := by
    rintro u' ⟨hfin, hann⟩
    obtain ⟨k, hk, hk0⟩ := hQ u' fun u hu hu0 => by
      have hu1 : MxAt (fun _ => True) u := fun i j => by
        rw [mem_idAt_true]; exact congrFun (congrFun hu0 i) j
      have : u ∈ Γ := by
        have h := hu
        change e • u ∈ Γ at h
        rwa [hfix u hu1] at h
      exact (psi_symplO_swap ψ _ _).2 (hann u this)
    refine ⟨k, hk, ?_⟩
    have hd : e • (u' - k) = 0 := by
      ext i j
      rw [Matrix.smul_apply, Matrix.zero_apply]
      exact (GlobalTheory.AdelicCoord.finPart_eq_zero_iff D _).1 (congrFun (congrFun hk0 i) j)
    rw [smul_sub, sub_eq_zero] at hd
    show e • k = u'
    rw [← hd, hfix u' hfin]
  have hcl : IsClosed (annSet ψ Γ) := by
    have e1 : annSet ψ Γ = {x : WO S T | pairA D.host.F 1 0 • x = 0} ∩
        ⋂ u ∈ Γ, {x : WO S T | ψ (symplO S T u x) = 1} := by
      ext x
      simp only [annSet, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, mxAt_true_iff]
    rw [e1]
    refine IsClosed.inter (isClosed_eq (continuous_smul_mx _) continuous_const)
      (isClosed_biInter fun u _ => isClosed_eq ?_ continuous_const)
    exact hψ.1.1.comp (GlobalTheory.SplitScalar.continuous_symplO S T continuous_const continuous_id)
  exact (hQc.image (continuous_smul_mx e)).of_isClosed_subset hcl hsub

end GlobalTheory.AnnNbhdCpt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetPositivePartKroneckerBlockUnitaryOrthonormal
section
open Formalism.IndefR.Datum Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting

namespace GlobalTheory.PlusDetONB

open GlobalTheory.CompactFockAction GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators

def sgnP {k : ℕ} (p : ℕ) : Fin k → Bool := fun a => decide (a.val < p)

theorem onb_facts {k : ℕ} {G s B : Matrix (Fin k) (Fin k) ℂ} {p : ℕ} (h : IsONBasis G s B p) :
    B * B⁻¹ = 1 ∧ B⁻¹ * B = 1 ∧ s = B * Formalism.REAL.Jm (sgnP p) * B⁻¹ := by
  obtain ⟨ε, hε, hG, hs⟩ := h
  have hd : Matrix.diagonal (fun a => (ε a : ℂ)) = Formalism.REAL.Jm (sgnP (k := k) p) := by
    unfold Formalism.REAL.Jm sgnP
    congr 1
    funext a
    rcases hε a with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp [h1, h2]
    · have : ¬ a.val < p := by omega
      simp [h1, this]
  have hsq : Matrix.diagonal (fun a => (ε a : ℂ)) * Matrix.diagonal (fun a => (ε a : ℂ)) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    rcases hε a with ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp [h1]
  have hdet : (Matrix.diagonal (fun a => (ε a : ℂ))).det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hsq
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  have hB : B.det ≠ 0 := by
    intro h0
    apply hdet
    rw [← hG, Matrix.det_mul, h0, mul_zero]
  have hU : IsUnit B.det := isUnit_iff_ne_zero.2 hB
  have h1 : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B hU
  have h2 : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B hU
  refine ⟨h1, h2, ?_⟩
  rw [← hd, ← hs, Matrix.mul_assoc, h1, Matrix.mul_one]

theorem isBlock_of_isKMat {k p : ℕ} {κ : Matrix (Fin k) (Fin k) ℂ} (h : IsKMat p κ) : IsBlock (sgnP p) κ := by
  intro i j hij
  apply h.2 i j
  intro hiff
  apply hij
  unfold sgnP
  exact decide_eq_decide.2 hiff

theorem card_sgnP {k p : ℕ} (hp : p ≤ k) (e : Bool) :
    (Finset.univ.filter fun i : Fin k => sgnP p i = e).card = if e then p else k - p := by
  have h1 : (Finset.univ.filter fun i : Fin k => i.val < p).card = p := by
    rw [Fin.card_filter_val_lt]; omega
  have h2 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin k)))
    (p := fun i : Fin k => i.val < p)
  rw [Finset.card_univ, Fintype.card_fin] at h2
  cases e
  · simp only [sgnP, decide_eq_false_iff_not, Bool.false_eq_true, if_false]
    omega
  · simp only [sgnP, decide_eq_true_eq, if_true]
    exact h1

theorem signBlockDeterminant_positive_eq {k p : ℕ} (κ : Matrix (Fin k) (Fin k) ℂ) : signBlockDeterminant (sgnP p) true κ = detPos p κ := by
  unfold signBlockDeterminant detPos
  rw [← Matrix.det_submatrix_equiv_self (Equiv.subtypeEquivRight (fun a : Fin k => (by simp [sgnP] : sgnP p a = true ↔ a.val < p)))]
  rfl

theorem signBlockDeterminant_negative_eq {k p : ℕ} (κ : Matrix (Fin k) (Fin k) ℂ) : signBlockDeterminant (sgnP p) false κ = detNeg p κ := by
  unfold signBlockDeterminant detNeg
  rw [← Matrix.det_submatrix_equiv_self (Equiv.subtypeEquivRight (fun a : Fin k => (by simp [sgnP] : sgnP p a = false ↔ ¬ a.val < p)))]
  rfl

theorem detPlus_onb : ∀ {n m : ℕ} (GS sS BS κS : Matrix (Fin n) (Fin n) ℂ) (GT sT BT κT : Matrix (Fin m) (Fin m) ℂ)
    (pS pT : ℕ), pS ≤ n → pT ≤ m → IsONBasis GS sS BS pS → IsONBasis GT sT BT pT → IsKMat pS κS → IsKMat pT κT →
    GlobalTheory.WeilParts.detPlus sS sT (BS * κS * BS⁻¹)⁻¹ (BT * κT * BT⁻¹) =
      detPos pT κT ^ pS * detNeg pT κT ^ (n - pS) * (detPos pS κS ^ pT)⁻¹ * (detNeg pS κS ^ (m - pT))⁻¹ := by
  intro n m GS sS BS κS GT sT BT κT pS pT hpS hpT hBS hBT hκS hκT
  obtain ⟨h1S, h2S, hsS⟩ := onb_facts hBS
  obtain ⟨h1T, h2T, hsT⟩ := onb_facts hBT
  have hu : κS * κSᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hκS.1
  have hinv : (BS * κS * BS⁻¹)⁻¹ = BS * κSᴴ * BS⁻¹ := by
    refine Matrix.inv_eq_right_inv ?_
    calc BS * κS * BS⁻¹ * (BS * κSᴴ * BS⁻¹) = BS * (κS * (BS⁻¹ * BS) * κSᴴ) * BS⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h2S, Matrix.mul_one, hu, Matrix.mul_one, h1S]
  rw [hinv, hsS, hsT, detPlus_conj h2S h2T]
  have bS := isBlock_of_isKMat hκS
  have bT := isBlock_of_isKMat hκT
  have bS' : IsBlock (sgnP pS) κSᴴ := fun i j e => by
    rw [Matrix.conjTranspose_apply, bS j i (Ne.symm e), star_zero]
  rw [detPlus_block bS' bT, prod_bool _ fun e => signBlockDeterminant (sgnP pS) e κSᴴ,
    prod_bool _ fun e => signBlockDeterminant (sgnP pT) e κT, card_sgnP hpT, card_sgnP hpT, card_sgnP hpS, card_sgnP hpS]
  have ih := fun e => signBlockDeterminant_mul_eq_one_of_mul_eq_one e bS hu
  rw [eq_inv_of_mul_eq_one_right (ih true), eq_inv_of_mul_eq_one_right (ih false)]
  simp only [if_true, Bool.false_eq_true, if_false, signBlockDeterminant_positive_eq, signBlockDeterminant_negative_eq, inv_pow]
  ring

end GlobalTheory.PlusDetONB
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagGLConjApply
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.SeeConjRead

open Classical

variable {D : D7}

def diagGL {κ : Type} [CommRing κ] {r : ℕ} (d : Fin r → κˣ) : GL (Fin r) κ :=
  Units.map (Matrix.diagonalRingHom (Fin r) κ).toMonoidHom (MulEquiv.piUnits.symm d)

theorem diagGL_val {κ : Type} [CommRing κ] {r : ℕ} (d : Fin r → κˣ) :
    ((diagGL d : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ) = Matrix.diagonal fun i => (d i : κ) := rfl

def flagV {M : Type} [Zero M] (ρ k n : ℕ) (e f : Fin ρ → M) (b : Fin k → M) (z : M) (i : Fin n) : M :=
  if h1 : i.1 < ρ then e ⟨i.1, h1⟩
  else if h2 : i.1 < ρ + k then b ⟨i.1 - ρ, by omega⟩
  else if h4 : i.1 = ρ + k then z
  else if h3 : i.1 < 2 * ρ + k + 1 then f ⟨2 * ρ + k - i.1, by omega⟩
  else 0

def e0T (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) :
    Fin D.R.rS → Fin (Yc D 0).rank → EAf D :=
  cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Fin D.R.rS → Formalism.L2.SG.HidaSetting.VA I) h) X.e0

def f0T (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) :
    Fin D.R.rS → Fin (Yc D 0).rank → EAf D :=
  cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Fin D.R.rS → Formalism.L2.SG.HidaSetting.VA I) h) X.f0

def z0T (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) :
    Fin (Yc D 0).rank → EAf D :=
  cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Formalism.L2.SG.HidaSetting.VA I) h) X.z0

def bwT (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) :
    Fin D.R.k → Fin (Yc D 0).rank → EAf D :=
  cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Fin D.R.k → Formalism.L2.SG.HidaSetting.VA I) h) X.bw

def bwdT (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) :
    Fin D.R.k → Fin (Yc D 0).rank → EAf D :=
  cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Fin D.R.k → Formalism.L2.SG.HidaSetting.VA I) h) X.bwd

def ewT (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) : EAf D :=
  cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F)) h) X.ew

def flagAt (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (PP : Pl D.host.E) :
    Fin (Yc D 0).rank → Fin (Yc D 0).rank → EAf D :=
  if GlobalTheory.StdFrames.cpt PP (ewT X h) = 1 then
    flagV D.R.rS D.R.k (Yc D 0).rank (e0T X h) (f0T X h) (bwT X h) (z0T X h)
  else flagV D.R.rS D.R.k (Yc D 0).rank (e0T X h) (f0T X h) (fun i => bwdT X h (Fin.rev i)) (z0T X h)

def RedIs {n : ℕ} (β : GL (Fin n) (EAf D)) (PP : Pl D.host.E) (w : Fin n → Fin n → EAf D) : Prop :=
  ∀ i j, ∃ hm : Matrix.mulVec (β⁻¹).val (w j) i ∈
      Formalism.L2.Herm.intAf D.host.F D.host.E,
    Formalism.L2.DIV.resS D.host.F PP ⟨_, hm⟩ = if i = j then 1 else 0

end GlobalTheory.SeeConjRead

namespace GlobalTheory.SeeConjRead

theorem diagGL_inv {κ : Type} [CommRing κ] {r : ℕ} (d : Fin r → κˣ) : (diagGL d)⁻¹ = diagGL (fun i => (d i)⁻¹) := by
  unfold diagGL
  rw [← map_inv, ← map_inv]
  rfl

theorem diagGL_conj_apply {κ : Type} [CommRing κ] {r : ℕ} (d : Fin r → κˣ) (u : GL (Fin r) κ) (i j : Fin r) :
    (((diagGL d)⁻¹ * u * diagGL d : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ) i j =
      (((d i)⁻¹ : κˣ) : κ) * (u : Matrix (Fin r) (Fin r) κ) i j * (d j : κ) := by
  rw [diagGL_inv, Units.val_mul, Units.val_mul, diagGL_val, diagGL_val, Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem unipSym_conj_of {κ : Type} [CommRing κ] {r : ℕ} (ρ k : ℕ) (d : Fin r → κˣ) {u : GL (Fin r) κ}
    (hu : u ∈ unipSym κ r ρ k) : (diagGL d)⁻¹ * u * diagGL d ∈ unipSym κ r ρ k := by
  obtain ⟨⟨h1, h2⟩, h3⟩ := hu
  refine ⟨⟨fun i j hij => ?_, fun i => ?_⟩, fun i j a b c => ?_⟩
  · show (((diagGL d)⁻¹ * u * diagGL d : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ) i j = 0
    rw [diagGL_conj_apply, h1 hij, mul_zero, zero_mul]
  · rw [diagGL_conj_apply, h2, mul_one, Units.inv_mul]
  · rw [diagGL_conj_apply, h3 i j a b c, mul_zero, zero_mul]

theorem unipSym_conj_iff {κ : Type} [CommRing κ] {r : ℕ} (ρ k : ℕ) (d : Fin r → κˣ) (u : GL (Fin r) κ) :
    u ∈ unipSym κ r ρ k ↔ (diagGL d)⁻¹ * u * diagGL d ∈ unipSym κ r ρ k := by
  refine ⟨unipSym_conj_of ρ k d, fun h => ?_⟩
  have h' := unipSym_conj_of ρ k (fun i => (d i)⁻¹) h
  rw [← diagGL_inv, inv_inv] at h'
  simpa [mul_assoc] using h'

end GlobalTheory.SeeConjRead
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCommonDenominatorSelfDualLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevelDenom

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem natCast_smul_mem_hatL_std (Λ : Submodule (𝓞 E) (Fin n → E)) (c : ℕ)
    (hc : ∀ y ∈ Λ, c • y ∈ Formalism.L2.Col.stdLat E n) (x : Fin n → E ⊗[F] Formalism.L2.Herm.Af F)
    (hx : x ∈ Formalism.L2.Herm.hatL (F := F) Λ) :
    (c : E ⊗[F] Formalism.L2.Herm.Af F) • x ∈ Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (Formalism.L2.Col.stdLat E n) := by
  unfold Formalism.L2.Herm.hatL Formalism.UG.latS at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, hl, rfl⟩ := hy
    apply Submodule.subset_span
    refine ⟨c • l, hc l hl, ?_⟩
    funext i
    simp [nsmul_eq_mul, map_mul, map_natCast]
  | zero => simp
  | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
  | smul a y _ hy =>
    rw [smul_comm]
    exact Submodule.smul_mem _ a hy

theorem exists_nsmul_le_std (Λ : Submodule (𝓞 E) (Fin n → E)) (hfg : Λ.FG) :
    ∃ c : ℕ, 0 < c ∧ ∀ y ∈ Λ, c • y ∈ Formalism.L2.Col.stdLat E n := by
  obtain ⟨S, hS⟩ := hfg
  obtain ⟨c, hc, h⟩ := GlobalTheory.LatSandwich.exists_nsmul_le S (Formalism.L2.Pj.stdLat E n)
    (fun x _ => GlobalTheory.LatSandwich.exists_nsmul_mem_stdLat x)
  exact ⟨c, hc, fun y hy => h y (by rw [hS]; exact hy)⟩

theorem exists_nsmul_single_mem (Λ : Submodule (𝓞 E) (Fin n → E)) (hsp : Submodule.span E (Λ : Set (Fin n → E)) = ⊤) :
    ∃ c : ℕ, 0 < c ∧ ∀ j, c • (Pi.single j (1 : E) : Fin n → E) ∈ Λ := by
  classical
  obtain ⟨c, hc, h⟩ := GlobalTheory.LatSandwich.exists_nsmul_le (Finset.univ.image fun j : Fin n => (Pi.single j (1 : E) : Fin n → E)) Λ
    (fun x _ => GlobalTheory.LatSandwich.exists_nsmul_mem_of_span Λ hsp x)
  exact ⟨c, hc, fun j => h _ (Submodule.subset_span (by simp))⟩

end GlobalTheory.LevelDenom

namespace GlobalTheory.LevelDenom

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}

theorem exists_denom_stab (hc : Formalism.BasicNotions.CMData F E) (J : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E))
    (hfg : Λ.FG) (hsp : Submodule.span E (Λ : Set (Fin n → E)) = ⊤) :
    ∃ b : ℕ, 0 < b ∧ ∀ k ∈ congLev hc J Λ ⊤, ∀ i j,
      (b : E ⊗[F] Formalism.L2.Herm.Af F) * k.1 i j ∈ Formalism.L2.Herm.intAf F E := by
  classical
  obtain ⟨a, ha, hae⟩ := exists_nsmul_single_mem Λ hsp
  obtain ⟨c, hc0, hce⟩ := exists_nsmul_le_std Λ hfg
  refine ⟨a * c, Nat.mul_pos ha hc0, fun k hk i j => ?_⟩
  have hs := hk.2.1
  have hzmem : (fun l => Formalism.UG.inclE (Formalism.L2.Herm.Af F) ((a • (Pi.single j (1 : E) : Fin n → E)) l)) ∈
      Formalism.L2.Herm.hatL (F := F) Λ := Submodule.subset_span ⟨_, hae j, rfl⟩
  have ez : (fun l => Formalism.UG.inclE (Formalism.L2.Herm.Af F) ((a • (Pi.single j (1 : E) : Fin n → E)) l)) =
      (a : E ⊗[F] Formalism.L2.Herm.Af F) • (Pi.single j 1 : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) := by
    funext l
    by_cases e : l = j
    · subst e; simp [nsmul_eq_mul]
    · simp [Pi.single_eq_of_ne e, nsmul_eq_mul]
  rw [ez] at hzmem
  have hkz := (hs _).1 hzmem
  have h2 := natCast_smul_mem_hatL_std Λ c hce _ hkz
  rw [Formalism.L2.Col.mem_latS_std] at h2
  have h3 := h2 i
  rw [Matrix.mulVec_smul] at h3
  convert h3 using 1
  simp [Matrix.mulVec_single_one, mul_comm, mul_left_comm, mul_assoc]

end GlobalTheory.LevelDenom

namespace GlobalTheory.LevelDenom

theorem exists_denom_congLev : ∀ (D : D7) (V : HSp D) (Λ : Lat V), IsSelfDualC V Λ → ∃ b : ℕ, 0 < b ∧ ∀ k ∈ congLev D.sp.cm V.gram Λ ⊤, ∀ i j, (b : Lev.EAf D) * k.1 i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  intro D V Λ hΛ
  haveI := hΛ.1
  exact exists_denom_stab D.sp.cm V.gram Λ (Submodule.IsLattice.fg (A := D.host.E))
    (Submodule.IsLattice.span_eq_top (A := D.host.E))

end GlobalTheory.LevelDenom
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCosetRepHeckeElementPrincipalLevelStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coset_rep_hecke_element_principal_level : ∀ (D : D7) {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks),
    R.toLevCh.Is A.μ0 → R.IsFam → ∀ (i : Fin D.R.m) (P : Formalism.L2.DIV.Pl D.host.E) (k : ℕ) (α : GA D (Wc D i))
    (Rc : Finset (GA D (Wc D i))) (e : AE D) (ϖ : 𝓞 D.host.E) (a₀ : GA D (Wc D i)),
    Bridge.SplitOff P (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) → IsHeckeAt (Wc D i) P k α →
    Bridge.IsDC (Lev.levG (Wc D i) (R.βW i) (R.datWp i R.triv)) α Rc →
    Formalism.L2.NTheta.IsIdemAt e P → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 →
    Formalism.L2.NTheta.IsHeckeElt (Wc D i) e (ϖ : D.host.E) k a₀ →
    ∃ a ∈ Rc, a⁻¹ * a₀ ∈ Lev.levG (Wc D i) (R.βW i) (R.datWp i R.triv) := by
  first | exact @GlobalTheory.HeckeDC.exists_rep | exact GlobalTheory.HeckeDC.exists_rep | (intros; apply GlobalTheory.HeckeDC.exists_rep <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLiftKer
section
set_option autoImplicit false

noncomputable section

open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.HeckeKerLat

theorem ex_nsmul {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (F : FamilyUnif Xo σ ty) (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P) (n : ℕ) (w : Fin g → ℂ) :
    F.ex i P (n • w) = F.ex i P w ^ n := by
  induction n with
  | zero =>
    rw [zero_smul, pow_zero]
    have := (F.ex_ker i P hP 0).2 (zero_mem _)
    exact this
  | succ n ih => rw [succ_nsmul, F.ex_add i P hP, ih, pow_succ]

theorem exists_lift_ker : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty) (i j : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (P' : (F.Di j).La →+ (Fin g → ℂ)) (p : ℕ) (C : Subgroup (Over.mk (F.u i P) ⟶ Xo.univ.t.G)) (ψ : pullback Xo.univ.t.G.hom (F.u i P) ⟶ pullback Xo.univ.t.G.hom (F.u j P')) (ψp : (Over.mk (F.u i P) ⟶ Xo.univ.t.G) →* (Over.mk (F.u j P') ⟶ Xo.univ.t.G)), IsPeriod (F.Di i) ty P → IsPeriod (F.Di j) ty P' → p.Prime → (∀ a ∈ C, a ^ p ^ 2 = 1) → Formalism.L2.Pj.IsHkIsog p (F.u i P) (F.u j P') C ψ ψp →
  ∃ (gam : (F.Di i).La →ₗ[𝓞 E] (F.Di j).La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)),
    (∀ a b, (F.Di j).EF (gam a) (gam b) = (p : ℤ) ^ 2 * (F.Di i).EF a b) ∧ (∀ a, P' (gam a) = h (P a)) ∧
    (∀ b, ∃ a, gam a = (p ^ 2) • b) ∧ (∀ z, F.ex j P' (h z) = ψp (F.ex i P z)) ∧
    (∀ a, F.ex i P (((p : ℂ) ^ 2)⁻¹ • P a) ∈ C ↔ ∃ b, gam a = (p ^ 2) • b) ∧
    ∀ c ∈ C, ∃ a, c = F.ex i P (((p : ℂ) ^ 2)⁻¹ • P a) := by
  intro E _ _ _ H Dw l Xo σ g ty F i j P P' p C ψ ψp hP hP' hp hC hI
  obtain ⟨gam, h, h1, h2, h3, h4⟩ := GlobalTheory.T.heckeIsogeny_lifts_to_lattice_map_scaling_forms E H Dw l Xo σ g ty F i j P P' p C ψ ψp hP hP' hp hC hI
  have hker : ψp.ker = C := hI.2.2.2.2.2.1
  have hp0 : ((p : ℂ) ^ 2) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hp.ne_zero)
  refine ⟨gam, h, h1, h2, h3, h4, fun a => ?_, fun c hc => ?_⟩
  · rw [← hker, MonoidHom.mem_ker, ← h4, map_smul, ← h2, F.ex_ker j P' hP']
    constructor
    · rintro ⟨b, hb⟩
      refine ⟨b, hP'.2.1 ?_⟩
      rw [map_nsmul, hb, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
      push_cast
      rw [mul_inv_cancel₀ hp0, one_smul]
    · rintro ⟨b, hb⟩
      refine ⟨b, ?_⟩
      rw [hb, map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
      push_cast
      rw [inv_mul_cancel₀ hp0, one_smul]
  · obtain ⟨w, rfl⟩ := F.ex_onto i P hP c
    have e1 : F.ex i P ((p ^ 2) • w) = 1 := by rw [ex_nsmul F i P hP, hC _ hc]
    obtain ⟨a, ha⟩ := (F.ex_ker i P hP _).1 e1
    refine ⟨a, congrArg _ ?_⟩
    rw [ha, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    push_cast
    rw [inv_mul_cancel₀ hp0, one_smul]

end GlobalTheory.HeckeKerLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRigidifiedThetaIsoBaseChangeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rigidified_theta_iso_base_change : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {T Ω : Type} [CommRing T] [CommRing Ω] (χ : T →+* Ω) {x x' : Sp T ⟶ Xo.X} {x₁ x₁' : Sp Ω ⟶ Xo.X} {Ψ : Gx x ⟶ Gx x'} {Ψ₁ : Gx x₁ ⟶ Gx x₁'} {pm : Gx x₁ ⟶ Gx x} {pm' : Gx x₁' ⟶ Gx x'} {k : ℤ} {β : LB.Gen (isoLB Xo.univ.t.G Xo.univ.t.PP Ψ k)}, IsCan χ pm → IsCan χ pm' → Ψ₁ ≫ pm' = pm ≫ Ψ → Ψ₁ ≫ (fst (Over.mk x₁') Xo.univ.t.G).left = (fst (Over.mk x₁) Xo.univ.t.G).left → IsRigIso Xo.univ.t.G Xo.univ.t.PP Ψ k β → ∃ β₁ : LB.Gen (isoLB Xo.univ.t.G Xo.univ.t.PP Ψ₁ k), IsRigIso Xo.univ.t.G Xo.univ.t.PP Ψ₁ k β₁ ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Gx x₁) (z : Z) (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι), Good Xo.univ.t.PP.L z J → val β₁ r z J = val β (r ≫ pm) z J := by
  first | exact @GlobalTheory.HeckeEx.exists_isRigIso_baseChange | exact GlobalTheory.HeckeEx.exists_isRigIso_baseChange | (intros; apply GlobalTheory.HeckeEx.exists_isRigIso_baseChange <;> assumption)
end

