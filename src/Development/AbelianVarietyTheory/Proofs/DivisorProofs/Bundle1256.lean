import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceFiniteAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0010
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1216
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1174
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0288
import Development.AbelianVarietyTheory.Definitions.Divisors.DiagValExtTraceNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1177
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1228
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1217
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.GenericOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0018
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0006
import CompanionTheory.AutomorphicTheory.PadicUnitaryWeights.DixmierMalliavin.DixmierMalliavinFactorisationHolds

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjSrcMemOrb
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EulerTw.Comm

open GlobalTheory.EulerTw

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem pLoc_idem (T : Finset (Pl E)) (w : Pl E) : pLoc E w (idem E T) = if w ∈ T then 1 else 0 := rfl

theorem prjG_val (T : Finset (Pl E)) (g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) :
    (prjG E n T g).val = idem E T • g.val + (1 - idem E T) • (1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) := rfl

theorem conjSrc_mem_orb (u v : Pl E) :
    conjSrc (IsCMField.complexConj E).toRingEquiv v ∈ orb E u ↔ v ∈ orb E u := by
  simp only [orb, cPl, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (h | h)
    · right; rw [← h, GlobalTheory.ThetaPull.conjSrc_conjSrc]
    · left; exact conjSrc_injective _ h
  · rintro (rfl | rfl)
    · right; rfl
    · left; exact GlobalTheory.ThetaPull.conjSrc_conjSrc _

theorem cFin_idem (u : Pl E) : GlobalTheory.ThetaPull.cFin E (idem E (orb E u)) = idem E (orb E u) :=
  FiniteAdeleRing.ext _ fun v => by
    show conjLoc _ v (pLoc E _ (idem E _)) = pLoc E v (idem E _)
    rw [pLoc_idem, pLoc_idem]
    by_cases h : v ∈ orb E u
    · rw [if_pos ((conjSrc_mem_orb u v).2 h), if_pos h, map_one]
    · rw [if_neg (mt (conjSrc_mem_orb u v).1 h), if_neg h, map_zero]

theorem thF_val (g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) :
    (thF E n g).val = (PhiU n _).val * (((g⁻¹).val.map (GlobalTheory.ThetaPull.cFin E))ᵀ) * ((PhiU n _)⁻¹).val := rfl

theorem thF_prjG (u : Pl E) (g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) :
    thF E n (prjG E n (orb E u) g) = prjG E n (orb E u) (thF E n g) := by
  apply Units.ext
  have he := cFin_idem (E := E) u
  rw [thF_val, prjG_val, thF_val, ← map_inv, prjG_val]
  have h1 : (idem E (orb E u) • (g⁻¹).val + (1 - idem E (orb E u)) • (1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E))).map
      (GlobalTheory.ThetaPull.cFin E) = idem E (orb E u) • (g⁻¹).val.map (GlobalTheory.ThetaPull.cFin E) + (1 - idem E (orb E u)) • 1 := by
    ext i j
    by_cases hij : i = j <;> simp [hij, Matrix.one_apply, he]
  have h2 : (PhiU n (FiniteAdeleRing (𝓞 E) E)).val * ((PhiU n (FiniteAdeleRing (𝓞 E) E))⁻¹).val = 1 := Units.mul_inv _
  rw [h1, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_smul, Matrix.transpose_one, Matrix.mul_add,
    Matrix.add_mul, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_one, h2]

theorem prjG_prjG (T : Finset (Pl E)) (g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) :
    prjG E n T (prjG E n T g) = prjG E n T g := by
  apply Units.ext
  have h1 : idem E T * (1 - idem E T) = 0 := by rw [mul_sub, mul_one, idem_mul_self, sub_self]
  rw [prjG_val, prjG_val, smul_add, smul_smul, smul_smul, idem_mul_self, h1, zero_smul, add_zero]

theorem thU_val (u : Pl E) (a : Gam E n u) : (thU E n u a).1 = thF E n a.1 := by
  obtain ⟨g, hg⟩ := a.2
  show prjG E n (orb E u) (thF E n a.1) = thF E n a.1
  rw [← hg, thF_prjG, prjG_prjG]

theorem thF_thF (g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) : thF E n (thF E n g) = g :=
  GlobalTheory.ThetaPull.thetaGL_thetaGL _ GlobalTheory.ThetaPull.cFin_cFin g

theorem thF_ratF (g : GL (Fin n) E) : ratF E n (thE E n g) = thF E n (ratF E n g) :=
  GlobalTheory.ThetaPull.map_thetaGL _ _ _ (fun x => (conjFin_algebraMap (IsCMField.complexConj E).toRingEquiv x).symm) g

end GlobalTheory.EulerTw.Comm

namespace GlobalTheory.EulerTw

end GlobalTheory.EulerTw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjUnitaryOfSameHermitianMultiplicationModelStatement
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conj_unitary_of_same_hermitianMultiplicationModel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E) (B : GlobalTheory.UnitLemma.InvAlg K) (u x : B.A) (n : ℕ) (γ γ' : GLw n w), IsModel w e B u x γ → IsModel w e B u x γ' → ∃ y ∈ UL n w, γ' = y⁻¹ * γ * y := by
  first | exact @GlobalTheory.KapLat.models_conj | exact GlobalTheory.KapLat.models_conj | (intros; apply GlobalTheory.KapLat.models_conj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjZpowersEntriesValuedBoundedOfCompactClosureStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conj_zpowers_entries_valued_bounded_of_compact_closure : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (t g : UL n w),
    IsCompact (closure (Subgroup.zpowers t : Set (UL n w))) →
    ∃ B : WithZero (Multiplicative ℤ), ∀ (k : ℤ) (i j : Fin n),
      Valued.v ((((g⁻¹ * t ^ k * g : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ B := by
  first | exact @GlobalTheory.BCT.powers_entries_bdd | exact GlobalTheory.BCT.powers_entries_bdd | (intros; apply GlobalTheory.BCT.powers_entries_bdd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectionBlocksHermitianFrame
section
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms

noncomputable section

namespace GlobalTheory.SubQuotConn

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V]
  [IsScalarTower ℝ ℂ V]
variable {m l : Type*} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]

section Leibniz

variable {p k : Type*} [Fintype k] {M : V → Matrix p k ℂ} {v : V → k → ℂ} {z : V}

omit [NormedSpace ℂ V] [IsScalarTower ℝ ℂ V] in

theorem diff_mulVec (hM : MContDiffAt 1 M z) (hv : ∀ a, DifferentiableAt ℝ (fun x => v x a) z)
    (a : p) : DifferentiableAt ℝ (fun x => (M x *ᵥ v x) a) z := by
  simp only [mulVec, dotProduct]
  exact DifferentiableAt.fun_sum fun b _ => (hM.diff a b).fun_mul (hv b)

theorem del_mulVec (hM : MContDiffAt 1 M z) (hv : ∀ a, DifferentiableAt ℝ (fun x => v x a) z)
    (ξ : V) (a : p) : del (fun x => (M x *ᵥ v x) a) z ξ =
      (M z *ᵥ (fun b => del (fun x => v x b) z ξ) + mdel M z ξ *ᵥ v z) a := by
  simp only [mulVec, dotProduct, Pi.add_apply]
  rw [del_sum fun b _ => (hM.diff a b).fun_mul (hv b), ContinuousLinearMap.sum_apply,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun b _ => by rw [del_mul (hM.diff a b) (hv b), mdel_apply]

theorem dbar_mulVec (hM : MContDiffAt 1 M z) (hv : ∀ a, DifferentiableAt ℝ (fun x => v x a) z)
    (η : V) (a : p) : dbar (fun x => (M x *ᵥ v x) a) z η =
      (M z *ᵥ (fun b => dbar (fun x => v x b) z η) + mdbar M z η *ᵥ v z) a := by
  simp only [mulVec, dotProduct, Pi.add_apply]
  rw [dbar_sum fun b _ => (hM.diff a b).fun_mul (hv b), ContinuousLinearMap.sum_apply,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun b _ => by rw [dbar_mul (hM.diff a b) (hv b), mdbar_apply]

end Leibniz

section Blocks

variable {H : Matrix (m ⊕ l) (m ⊕ l) ℂ}

theorem incl_transpose_mul_mul (M : Matrix (m ⊕ l) (m ⊕ l) ℂ) :
    (incl m l)ᵀ * M * incl m l = M.toBlocks₁₁ := by
  conv_lhs => rw [← fromBlocks_toBlocks M]
  simp [incl, transpose_fromRows, fromCols_mul_fromBlocks, fromCols_mul_fromRows]

theorem orthProj_transpose_mul (hs : IsUnit (subGram H).det) :
    (orthProj H)ᵀ * subGram H = H * incl m l := by
  conv_rhs => rw [← fromBlocks_toBlocks H]
  rw [orthProj, incl, transpose_fromCols, fromRows_mul, fromBlocks_mul_fromRows]
  congr 1
  · simp [subGram]
  · rw [orthCoeff, transpose_mul, transpose_transpose, transpose_nonsing_inv, transpose_transpose,
      subGram, Matrix.mul_assoc, nonsing_inv_mul H.toBlocks₁₁ hs]
    simp

theorem mul_orthLift_conj (hh : H.IsHermitian) (hs : IsUnit (subGram H).det) :
    H * (orthLift H)ᴴᵀ = fromRows 0 (quotGram H) := by
  have := congrArg conjTranspose (orthLift_transpose_mul hs)
  rw [conjTranspose_mul, hh.eq] at this
  rw [show (orthLift H)ᴴᵀ = (orthLift H)ᵀᴴ from rfl, this]
  ext (a | a) b <;> simp [(isHermitian_quotGram hh).apply]

end Blocks

section Frame

variable {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V}

theorem mdel_orthLift (ξ : V) :
    mdel (fun x => orthLift (H x)) z ξ = fromRows (-mdel (fun x => orthCoeff (H x)) z ξ) 0 := by
  ext (a | a) b <;> simp [orthLift, del_neg]

theorem mdbar_orthLift (η : V) :
    mdbar (fun x => orthLift (H x)) z η = fromRows (-mdbar (fun x => orthCoeff (H x)) z η) 0 := by
  ext (a | a) b <;> simp [orthLift, dbar_neg]

theorem quotMap_mul_mdel_orthLift (ξ : V) :
    quotMap m l * mdel (fun x => orthLift (H x)) z ξ = 0 := by
  rw [mdel_orthLift]; simp [quotMap, fromCols_mul_fromRows]

theorem quotMap_mul_mdbar_orthLift (η : V) :
    quotMap m l * mdbar (fun x => orthLift (H x)) z η = 0 := by
  rw [mdbar_orthLift]; simp [quotMap, fromCols_mul_fromRows]

variable (h : IsHermFrame U H) (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det) (hz : z ∈ U)
include h hs hz

theorem conn_gramS (ξ : V) : conn (gramS H) z ξ = orthProj (H z) * conn H z ξ * incl m l := by
  refine (eq_conn_of_compatible (H := gramS H) (hs z hz) ?_).symm
  have e : mdel (gramS H) z ξ = (mdel H z ξ).toBlocks₁₁ := rfl
  rw [e, ← conn_transpose_mul (h.isUnit z hz), ← incl_transpose_mul_mul, transpose_mul,
    transpose_mul]
  simp only [gramS, Matrix.mul_assoc]
  rw [orthProj_transpose_mul (hs z hz)]

theorem conn_gramQ (ξ : V) :
    conn (gramQ H) z ξ = quotMap m l * conn H z ξ * orthLift (H z) := by
  have hH1 := h.one hz
  have hsz := hs z hz
  have hL : MContDiffAt 1 (fun x => orthLift (H x)) z :=
    GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm.mContDiffAt_orthLift hH1 hsz
  refine (eq_conn_of_compatible (H := gramQ H)
    (isUnit_det_quotGram (h.isUnit z hz) hsz) ?_).symm
  have hev : gramQ H =ᶠ[𝓝 z] fun x => (orthLift (H x))ᵀ * H x * (orthLift (H x))ᴴᵀ := by
    filter_upwards [h.isOpen.mem_nhds hz] with x hx
    rw [orthLift_transpose_mul (hs x hx)]
    simp [gramQ, orthLift, fromCols_mul_fromRows, conjTranspose_fromRows_eq_fromCols_conjTranspose,
      transpose_fromCols]
  have hK : (quotMap m l)ᵀ * quotGram (H z) = fromRows 0 (quotGram (H z)) := by
    simp [quotMap, transpose_fromCols, fromRows_mul]
  rw [mdel_congr hev, mdel_mul (hL.transpose.mul hH1) hL.conjTranspose.transpose,
    mdel_mul hL.transpose hH1, mdel_transpose (fun x => (orthLift (H x))ᴴ), mdel_conjTranspose,
    mdel_transpose, orthLift_transpose_mul hsz, ← conn_transpose_mul (h.isUnit z hz),
    mdbar_orthLift, mdel_orthLift]
  simp only [Matrix.add_mul, Matrix.mul_assoc, mul_orthLift_conj (h.herm z hz) hsz, transpose_mul,
    gramQ, hK]
  simp [fromCols_mul_fromRows, conjTranspose_fromRows_eq_fromCols_conjTranspose, transpose_fromCols,
    transpose_fromRows]

theorem orthProj_mul_covDel_orthLift (ξ : V) :
    orthProj (H z) * (mdel (fun x => orthLift (H x)) z ξ + conn H z ξ * orthLift (H z)) = 0 := by
  have hH1 := h.one hz
  have hsz := hs z hz
  have hL : MContDiffAt 1 (fun x => orthLift (H x)) z :=
    GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm.mContDiffAt_orthLift hH1 hsz
  have hev : (fun x => (orthLift (H x))ᵀ * H x * incl m l) =ᶠ[𝓝 z] fun _ => 0 := by
    filter_upwards [h.isOpen.mem_nhds hz] with x hx
    rw [orthLift_transpose_mul (hs x hx)]
    simp [incl, fromCols_mul_fromRows]
  have h1 := mdel_congr hev ξ
  rw [mdel_const, mdel_mul (hL.transpose.mul hH1) (mContDiffAt_const _), mdel_const,
    Matrix.mul_zero, zero_add, mdel_mul hL.transpose hH1, mdel_transpose,
    ← conn_transpose_mul (h.isUnit z hz)] at h1
  set X := orthProj (H z) * (mdel (fun x => orthLift (H x)) z ξ + conn H z ξ * orthLift (H z))
  have h2 : Xᵀ * subGram (H z) = 0 := by
    rw [transpose_mul, Matrix.mul_assoc, orthProj_transpose_mul hsz, transpose_add, transpose_mul,
      ← h1]
    simp only [Matrix.add_mul, Matrix.mul_assoc]
    abel
  have h3 : Xᵀ = 0 := by
    rw [← Matrix.mul_nonsing_inv_cancel_right (subGram (H z)) Xᵀ hsz, h2, Matrix.zero_mul]
  rw [← transpose_transpose X, h3, transpose_zero]

end Frame

theorem connBlocks_secondForm {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m]
    [DecidableEq l] {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : IsHermFrame U H)
    (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det) (hz : z ∈ U) :
    ConnBlocks H z (fun η => -secondFormAdj H z η) (secondForm H z) := by
  have hH1 := h.one hz
  have hu := h.isUnit z hz
  have hsz := hs z hz
  have hL : MContDiffAt 1 (fun x => orthLift (H x)) z :=
    GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm.mContDiffAt_orthLift hH1 hsz
  have hI : MContDiffAt 1 (fun _ : V => incl m l) z := mContDiffAt_const _
  intro u q hu' hq'
  have e1 : ∀ ξ, covDel H (splitSec H u q) z ξ =
      incl m l *ᵥ (fun a => del (fun x => u x a) z ξ) +
        orthLift (H z) *ᵥ (fun a => del (fun x => q x a) z ξ) +
        mdel (fun x => orthLift (H x)) z ξ *ᵥ q z +
        conn H z ξ *ᵥ (incl m l *ᵥ u z + orthLift (H z) *ᵥ q z) := by
    intro ξ
    rw [covDel]
    congr 1
    funext a
    simp only [splitSec, Pi.add_apply]
    rw [del_add (diff_mulVec hI hu' a) (diff_mulVec hL hq' a), ContinuousLinearMap.add_apply,
      del_mulVec hI hu' ξ a, del_mulVec hL hq' ξ a]
    simp [add_assoc]
  have e2 : ∀ η, secDbar (splitSec H u q) z η =
      incl m l *ᵥ (fun a => dbar (fun x => u x a) z η) +
        orthLift (H z) *ᵥ (fun a => dbar (fun x => q x a) z η) +
        mdbar (fun x => orthLift (H x)) z η *ᵥ q z := by
    intro η
    funext a
    simp only [secDbar, splitSec, Pi.add_apply]
    rw [dbar_add (diff_mulVec hI hu' a) (diff_mulVec hL hq' a), ContinuousLinearMap.add_apply,
      dbar_mulVec hI hu' η a, dbar_mulVec hL hq' η a]
    simp [add_assoc]
  have kP := orthProj_mul_covDel_orthLift h hs hz
  refine ⟨fun ξ => ?_, fun ξ => ?_, fun η => ?_, fun η => ?_⟩
  · have k : orthProj (H z) * mdel (fun x => orthLift (H x)) z ξ =
        -(orthProj (H z) * conn H z ξ * orthLift (H z)) := by
      rw [Matrix.mul_assoc, eq_neg_iff_add_eq_zero, ← Matrix.mul_add, kP]
    rw [e1, covDel, conn_gramS h hs hz]
    simp only [mulVec_add, mulVec_mulVec, orthProj_mul_incl, orthProj_mul_orthLift, one_mulVec,
      zero_mulVec, k, neg_mulVec, ← Matrix.mul_assoc]
    abel
  · rw [e1, covDel, conn_gramQ h hs hz, secondForm, blockQS]
    simp only [mulVec_add, mulVec_mulVec, quotMap_mul_incl, quotMap_mul_orthLift,
      quotMap_mul_mdel_orthLift, one_mulVec, zero_mulVec, ← Matrix.mul_assoc]
    abel
  · beta_reduce
    rw [e2, ← extForm_eq_neg_secondFormAdj hH1 (h.eventually_herm hz) hu hsz, extForm]
    simp only [mulVec_add, mulVec_mulVec, orthProj_mul_incl, orthProj_mul_orthLift, one_mulVec,
      zero_mulVec, add_zero]
    rfl
  · rw [e2]
    simp only [mulVec_add, mulVec_mulVec, quotMap_mul_incl, quotMap_mul_orthLift,
      quotMap_mul_mdbar_orthLift, one_mulVec, zero_mulVec, zero_add, add_zero]
    rfl

example : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l] {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : IsHermFrame U H) (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det) (hz : z ∈ U), ConnBlocks H z (fun η => -secondFormAdj H z η) (secondForm H z) := @connBlocks_secondForm

end GlobalTheory.SubQuotConn
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOneAddLowRankEmbeddingQuaternionMatrixStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.QSA GlobalTheory.PlaneSU
open scoped TensorProduct Quaternion
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_oneAddLowRankEmbedding_quaternionMatrix : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (a b : F) (M : ℕ) (A : Matrix (Fin M) (Fin 2) (AF F ⊗[F] E)) (B : Matrix (Fin 2) (Fin M) (AF F ⊗[F] E)) (θ : AF F ⊗[F] E), Continuous fun x : DA F a b => emb A B (qm (algebraMap (AF F) (AF F ⊗[F] E)) θ x) := by
  first | exact @GlobalTheory.emb_qm_continuous | exact GlobalTheory.emb_qm_continuous | (intros; apply GlobalTheory.emb_qm_continuous <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CountKernelNonzero
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

namespace GlobalTheory

theorem count_kernel_nonzero : ∀ {κ κ' : Type} [Field κ] [Field κ'] [Algebra ℂ κ] [Algebra ℂ κ'] (k c M l : ℕ) (ρ : Fin c → (κ →ₐ[ℂ] κ'))
    (w : Fin l → κ), (∃ z : Fin k → κ, TrBasis (algebraMap ℂ κ) z) → c * (M + k - 1).choose k < l →
  ∃ b : Fin l → κ', b ≠ 0 ∧ ∀ i, ∑ j, w j ⊗ₜ[ℂ] b j ∈
    (RingHom.ker (Algebra.TensorProduct.productMap (ρ i) (AlgHom.id ℂ κ'))) ^ M := by
  intro κ κ' _ _ _ _ k c M l ρ w hz hlt
  letI : Algebra κ' (κ ⊗[ℂ] κ') := Algebra.TensorProduct.rightAlgebra
  set J : Fin c → Ideal (κ ⊗[ℂ] κ') := fun i =>
    (RingHom.ker (Algebra.TensorProduct.productMap (ρ i) (AlgHom.id ℂ κ'))) ^ M with hJ
  have hjet := fun i => GlobalTheory.T.finrank_graphJets_le_choose k M (ρ i) hz
  haveI : ∀ i, Module.Finite κ' ((κ ⊗[ℂ] κ') ⧸ J i) := fun i => (hjet i).2
  let g : (Fin l → κ') →ₗ[κ'] (κ ⊗[ℂ] κ') := Fintype.linearCombination κ' (fun j => w j ⊗ₜ[ℂ] (1 : κ'))
  have hg : ∀ b, g b = ∑ j, w j ⊗ₜ[ℂ] b j := by
    intro b
    simp only [g, Fintype.linearCombination_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def]
    show (1 ⊗ₜ[ℂ] b j) * (w j ⊗ₜ[ℂ] (1 : κ')) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  let f : (Fin l → κ') →ₗ[κ'] ((i : Fin c) → (κ ⊗[ℂ] κ') ⧸ J i) :=
    LinearMap.pi fun i => (Ideal.Quotient.mkₐ κ' (J i)).toLinearMap.comp g
  have hdim : Module.finrank κ' ((i : Fin c) → (κ ⊗[ℂ] κ') ⧸ J i) < Module.finrank κ' (Fin l → κ') := by
    rw [Module.finrank_pi_fintype, Module.finrank_fin_fun]
    calc ∑ i, Module.finrank κ' ((κ ⊗[ℂ] κ') ⧸ J i) ≤ ∑ _i : Fin c, (M + k - 1).choose k :=
          Finset.sum_le_sum fun i _ => (hjet i).1
      _ = c * (M + k - 1).choose k := by simp
      _ < l := hlt
  obtain ⟨b, hbker, hb0⟩ := (Submodule.ne_bot_iff _).1 (LinearMap.ker_ne_bot_of_finrank_lt (f := f) hdim)
  refine ⟨b, hb0, fun i => ?_⟩
  have := congr_fun (LinearMap.mem_ker.mp hbker) i
  simp only [f, LinearMap.pi_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply, Pi.zero_apply] at this
  rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, hg] at this
  exact this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurvatureQuotientSubBlock
section
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms

namespace GlobalTheory

theorem blockQS_curv_eq_neg_dbarHol_extFormAdj {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m]
    [DecidableEq l] {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : IsHermFrame U H)
    (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det) (hz : z ∈ U) (ξ η : V) :
    blockQS (curv H z ξ η) = -dbarHol (extFormAdj H) z ξ η := by
  have e1 : blockQS (curv H z ξ η) = -mdbar (fun x => secondForm H x ξ) z η := by
    rw [blockQS_eq, curv]
    ext a b
    simp [secondForm, blockQS_eq, Matrix.toBlocks₂₁]
  have he : (fun x => extFormAdj H x ξ) =ᶠ[𝓝 z] fun x => -secondForm H x ξ := by
    filter_upwards [h.isOpen.mem_nhds hz] with x hx
    exact extFormAdj_eq_neg_secondForm (h.one hx) (h.eventually_herm hx) (h.isUnit x hx)
      (hs x hx) ξ
  rw [e1, dbarHol, neg_neg, mdbar_congr he, mdbar_neg]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarExtensionFormZero
section
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms

noncomputable section
namespace GlobalTheory.DbarExt

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V]
  [IsScalarTower ℝ ℂ V]

theorem hasFDerivAt_fderiv_apply {f : V → ℂ} {z : V} (hf : ContDiffAt ℝ 2 f z) (u : V) :
    HasFDerivAt (fun x => fderiv ℝ f x u)
      ((ContinuousLinearMap.apply ℝ ℂ u).comp (fderiv ℝ (fderiv ℝ f) z)) z := by
  have hD : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  exact (ContinuousLinearMap.apply ℝ ℂ u).hasFDerivAt.comp z hD.hasFDerivAt

theorem dbar_dbar_comm {f : V → ℂ} {z : V} (hf : ContDiffAt ℝ 2 f z) (v w : V) :
    dbar (fun x => dbar f x w) z v = dbar (fun x => dbar f x v) z w := by
  have hs : IsSymmSndFDerivAt ℝ f z := hf.isSymmSndFDerivAt (by simp)
  have key : ∀ u : V, HasFDerivAt (fun x => dbar f x u)
      ((1 / 2 : ℂ) • ((ContinuousLinearMap.apply ℝ ℂ u).comp (fderiv ℝ (fderiv ℝ f) z) +
        I • (ContinuousLinearMap.apply ℝ ℂ (I • u)).comp (fderiv ℝ (fderiv ℝ f) z))) z := by
    intro u
    have := ((hasFDerivAt_fderiv_apply hf u).add
      ((hasFDerivAt_fderiv_apply hf (I • u)).const_smul I)).const_smul (1 / 2 : ℂ)
    exact this
  rw [dbar_eq_of_hasFDerivAt (key w), dbar_eq_of_hasFDerivAt (key v)]
  simp only [antilinPart_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.apply_apply]
  rw [hs v w, hs v (I • w), hs (I • v) w, hs (I • v) (I • w)]
  ring_nf

theorem dbarAnti_extForm_eq_zero {m l : Type} [Fintype m] [Fintype l] [DecidableEq m]
    [DecidableEq l] {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : IsHermFrame U H)
    (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det) (hz : z ∈ U) (η₁ η₂ : V) :
    dbarAnti (extForm H) z η₁ η₂ = 0 := by
  have hc : ∀ a b, ContDiffAt ℝ 2 (fun x => orthCoeff (H x) a b) z := by
    intro a b
    have h1 := (GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm.mContDiffAt_orthLift (h.mContDiffAt hz) (hs z hz)) (Sum.inl a) b
    have h2 : (fun x => orthCoeff (H x) a b) = fun x => -orthLift (H x) (Sum.inl a) b := by
      funext x; simp [orthLift]
    rw [h2]
    exact (h1.neg).of_le (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))
  simp only [dbarAnti, extForm_eq_neg_mdbar]
  ext a b
  simp only [Matrix.sub_apply, mdbar_apply, Matrix.neg_apply, Matrix.zero_apply, dbar_neg,
    ContinuousLinearMap.neg_apply]
  rw [dbar_dbar_comm (hc a b) η₁ η₂]
  simp

end GlobalTheory.DbarExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeEqChernFormIntegralOfComplexCaseStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degreeEqChernFormIntegral_of_complex_case : GlobalTheory.Published.ChernDegreeComplex → GlobalTheory.Published.ChernDegree := by
  first | exact @GlobalTheory.ChernDegreeBaseChange.chernDegree_of_complex | exact GlobalTheory.ChernDegreeBaseChange.chernDegree_of_complex | (intros; apply GlobalTheory.ChernDegreeBaseChange.chernDegree_of_complex <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetWirtingerAntiholomorphicDerivEqSumStatement
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_wirtingerAntiholomorphicDeriv_eq_sum : ∀ {n : ℕ} (f : Fin n → V n → ℂ) (j : Fin n) (v : V n), (∀ i, ContDiffAt ℝ 2 (f i) v) → (Matrix.of fun i b => dbar (f i) v (coordVec b)).det = ∑ w : Equiv.Perm (Fin n), ((Equiv.Perm.sign w : ℤ) : ℂ) * dbar (fun x => f j x * ∏ i ∈ Finset.univ.erase j, dbar (f i) x (coordVec (w i))) v (coordVec (w j)) := by
  first | exact @GlobalTheory.GoodTop.det_dbar_eq_sum_dbar | exact GlobalTheory.GoodTop.det_dbar_eq_sum_dbar | (intros; apply GlobalTheory.GoodTop.det_dbar_eq_sum_dbar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockConjUnipotentStatement
section
open ValuativeRel Matrix MeasureTheory
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.LocLanglands GlobalTheory.GamMul DiscreteGroups.sglob.LConv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diagonal_block_conj_unipotent : ∀ (R : Type) [CommRing R] (n o₁ o₂ p q : ℕ), (o₁ + p ≤ o₂ ∨ o₂ + q ≤ o₁) → o₁ + p ≤ n → o₂ + q ≤ n → (∀ (g : GL (Fin p) R) (X : Matrix (Fin p) (Fin q) R), dg n o₁ g * uni n o₁ o₂ X = uni n o₁ o₂ (g.val * X) * dg n o₁ g) ∧ (∀ (g : GL (Fin q) R) (X : Matrix (Fin p) (Fin q) R), uni n o₁ o₂ X * dg n o₂ g = dg n o₂ g * uni n o₁ o₂ (X * g.val)) ∧ (∀ (a : GL (Fin p) R) (b : GL (Fin q) R), dg n o₁ a * dg n o₂ b = dg n o₂ b * dg n o₁ a) := by
  first | exact @GlobalTheory.GamMul.dg_uni_comm | exact GlobalTheory.GamMul.dg_uni_comm | (intros; apply GlobalTheory.GamMul.dg_uni_comm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DixmierMalliavinFactorisationFromLibrary
section
namespace GlobalTheory

theorem dixmierMalliavinFactorisation_fromLibrary : GlobalTheory.Published.DixmierMalliavinFactorisation :=
  CompanionTheory.DM.dixmierMalliavinFactorisation_holds

end GlobalTheory
end

