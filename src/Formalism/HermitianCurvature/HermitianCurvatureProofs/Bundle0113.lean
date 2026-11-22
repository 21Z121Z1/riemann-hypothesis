import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0108
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormRankZeroApply
import Formalism.DoubleCosetMeasures.Statement
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0064
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0110
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0084
import Formalism.HermitianCurvature.HermitianCurvatureProofs.KloostermanDensityOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixOneZero
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BlockTwoDiagonalZeroSize
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedLocSec
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadicalReductionOperator

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ChainX1
section
open Matrix Finset

namespace Formalism.FourierDecayAlt.P.PBN

open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.SignAntidiagonal

theorem chainX1' {A M : Type} [Ring A] [Algebra ℂ A] [AddCommGroup M] [Module ℂ M] (k r : ℕ) (c : Fin r → ℂ)
    (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A) (La : A →ₗ[ℂ] M) (hG : GlRel E) (m : ℕ) (hm : m + 2 ≤ r)
    (u : ℂ)
    (hR0 : ∀ (x : A) (l : ℕ) (hl : l < m), La (x * E (eI k r ⟨l, by omega⟩) (eI k r ⟨m + 1, by omega⟩)) = 0)
    (hR1 : ∀ x : A, La (x * E (eI k r ⟨m, by omega⟩) (eI k r ⟨m + 1, by omega⟩)) = La x)
    (hL : ∀ (x : A) (q : ℕ) (hq : q ≤ m), La (E (eI k r ⟨m + 1, by omega⟩) (eI k r ⟨q, by omega⟩) * x) =
      (if q = m then c ⟨m + 1, by omega⟩ / c ⟨m, by omega⟩ else 0) • La x) :
    La (qminor E (xR k r (m + 2) hm) (xR k r (m + 2) hm) u) =
      La (qminor E (xR k r (m + 1) (by omega)) (xR k r (m + 1) (by omega)) u *
          Tm E (u - ((m + 1 : ℕ) : ℂ)) (eI k r ⟨m + 1, by omega⟩) (eI k r ⟨m + 1, by omega⟩)) -
        (c ⟨m + 1, by omega⟩ / c ⟨m, by omega⟩) • La (qminor E (xR k r m (by omega)) (xR k r m (by omega)) u) := by
  set a := xR k r (m + 2) hm with hadef
  have hav : ∀ l, (a l).val = l.val := by intro l; simp [a, xR, eI]
  have hcs : a ∘ Fin.castSucc = xR k r (m + 1) (by omega) := by
    funext l; ext; simp [a, xR, eI]
  have hexp := Formalism.FourierDecayAlt.P.expansion_last_column A _ (m + 1) E a a u
  rw [hexp, map_sum, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]

  have hzero : ∀ l : Fin m, La ((((-1 : ℤ) ^ (m + 1 + ((Fin.castSucc (Fin.castSucc l) : Fin (m + 2)) : ℕ)) : ℤ) : A) *
      (qminor E (a ∘ (Fin.castSucc (Fin.castSucc l)).succAbove) (a ∘ Fin.castSucc) u *
        Tm E (u - ((m + 1 : ℕ) : ℂ)) (a (Fin.castSucc (Fin.castSucc l))) (a (Fin.last (m + 1))))) = 0 := by
    intro l
    rw [la_intmul]
    have hne : a (Fin.castSucc (Fin.castSucc l)) ≠ a (Fin.last (m + 1)) := by
      intro h'; have := congrArg Fin.val h'; rw [hav, hav] at this; simp at this; omega
    rw [tm_offdiag _ _ hne]
    have ha1 : a (Fin.castSucc (Fin.castSucc l)) = eI k r ⟨l.val, by omega⟩ := by ext; rw [hav]; simp [eI]
    have ha2 : a (Fin.last (m + 1)) = eI k r ⟨m + 1, by omega⟩ := by ext; rw [hav]; simp [eI]
    rw [ha1, ha2, hR0 _ l.val l.isLt, smul_zero]
  rw [Finset.sum_eq_zero (fun l _ => hzero l), zero_add]

  have hlast : La ((((-1 : ℤ) ^ (m + 1 + ((Fin.last (m + 1) : Fin (m + 2)) : ℕ)) : ℤ) : A) *
      (qminor E (a ∘ (Fin.last (m + 1)).succAbove) (a ∘ Fin.castSucc) u *
        Tm E (u - ((m + 1 : ℕ) : ℂ)) (a (Fin.last (m + 1))) (a (Fin.last (m + 1))))) =
      La (qminor E (xR k r (m + 1) (by omega)) (xR k r (m + 1) (by omega)) u *
        Tm E (u - ((m + 1 : ℕ) : ℂ)) (eI k r ⟨m + 1, by omega⟩) (eI k r ⟨m + 1, by omega⟩)) := by
    rw [la_intmul, Fin.succAbove_last, hcs]
    have h1 : a (Fin.last (m + 1)) = eI k r ⟨m + 1, by omega⟩ := by ext; rw [hav]; simp [eI]
    rw [h1]
    have h2 : ((-1 : ℤ) ^ (m + 1 + ((Fin.last (m + 1) : Fin (m + 2)) : ℕ))) = 1 := by
      simp only [Fin.val_last]; rw [← two_mul, pow_mul]; norm_num
    rw [h2]; simp
  rw [hlast]

  set rowsP : Fin (m + 1) → Fin (2 * r + k + 1) := Fin.cons (eI k r ⟨m + 1, by omega⟩) (xR k r m (by omega)) with hrP
  have hrows : a ∘ (Fin.castSucc (Fin.last m) : Fin (m + 2)).succAbove = rowsP ∘ (finRotate (m + 1)) := by
    funext q
    ext
    simp only [Function.comp_apply]
    by_cases hq : q = Fin.last m
    · subst hq
      rw [finRotate_last]
      simp only [rowsP, Fin.cons_zero]
      rw [hav, succAbove_val]; simp [eI]
    · have hq' : q.val < m := by
        have := q.isLt; have : q.val ≠ m := fun h' => hq (Fin.ext (by simp [h'])); omega
      have hr1 : finRotate (m + 1) q = Fin.succ ⟨q.val, hq'⟩ := by
        ext; rw [coe_finRotate_of_ne_last hq]; simp
      rw [hr1]
      simp only [rowsP, Fin.cons_succ]
      rw [hav, succAbove_val]; simp [xR, eI]; omega
  have hQm : La (qminor E (a ∘ (Fin.castSucc (Fin.last m) : Fin (m + 2)).succAbove) (a ∘ Fin.castSucc) u) =
      (c ⟨m + 1, by omega⟩ / c ⟨m, by omega⟩) • La (qminor E (xR k r m (by omega)) (xR k r m (by omega)) u) := by
    rw [hrows, Formalism.REAL.quantumMinorRowSkew_holds A _ (m + 1) E rowsP _ (finRotate (m + 1)) u, la_intmul, sign_finRotate]
    rw [Formalism.FourierDecayAlt.P.expansion_first_line A _ m E hG rowsP _ u, map_sum]
    rw [Fin.sum_univ_castSucc, Finset.sum_eq_zero, zero_add]
    · rw [la_intmul]
      have hr0 : rowsP 0 = eI k r ⟨m + 1, by omega⟩ := by simp [rowsP]
      have hrs : rowsP ∘ Fin.succ = xR k r m (by omega) := by funext q; simp [rowsP]
      rw [hr0, hrs, Fin.succAbove_last, hcs]
      have hne : eI k r ⟨m + 1, by omega⟩ ≠ xR k r (m + 1) (by omega) (Fin.last m) := by
        intro h'; have := congrArg Fin.val h'; simp [eI, xR] at this
      rw [tm_offdiag _ _ hne]
      have hx : xR k r (m + 1) (by omega) (Fin.last m) = eI k r ⟨m, by omega⟩ := by ext; simp [xR, eI]
      rw [hx, hL _ m le_rfl, if_pos rfl]
      have hcs2 : xR k r (m + 1) (by omega) ∘ Fin.castSucc = xR k r m (by omega) := by funext q; ext; simp [xR, eI]
      rw [hcs2, smul_smul, smul_smul]
      congr 1
      simp only [Fin.val_last]
      push_cast
      rw [neg_one_sq', one_mul]
    · intro q _
      rw [la_intmul]
      have hr0 : rowsP 0 = eI k r ⟨m + 1, by omega⟩ := by simp [rowsP]
      rw [hr0, hcs]
      have hqv : (xR k r (m + 1) (by omega) (Fin.castSucc q)).val = q.val := by simp [xR, eI]
      have hne : eI k r ⟨m + 1, by omega⟩ ≠ xR k r (m + 1) (by omega) (Fin.castSucc q) := by
        intro h'; have := congrArg Fin.val h'; rw [hqv] at this; simp [eI] at this; omega
      rw [tm_offdiag _ _ hne]
      have hx : xR k r (m + 1) (by omega) (Fin.castSucc q) = eI k r ⟨q.val, by omega⟩ := by ext; simp [xR, eI]
      have hq := q.isLt
      rw [hx, hL _ q.val (by omega), if_neg (by omega), zero_smul, smul_zero]
  have hmT : La (qminor E (a ∘ (Fin.castSucc (Fin.last m) : Fin (m + 2)).succAbove) (a ∘ Fin.castSucc) u *
      Tm E (u - ((m + 1 : ℕ) : ℂ)) (a (Fin.castSucc (Fin.last m))) (a (Fin.last (m + 1)))) =
      La (qminor E (a ∘ (Fin.castSucc (Fin.last m) : Fin (m + 2)).succAbove) (a ∘ Fin.castSucc) u) := by
    have hne : a (Fin.castSucc (Fin.last m)) ≠ a (Fin.last (m + 1)) := by
      intro h'; have := congrArg Fin.val h'; rw [hav, hav] at this; simp at this
    rw [tm_offdiag _ _ hne]
    have ha1 : a (Fin.castSucc (Fin.last m)) = eI k r ⟨m, by omega⟩ := by ext; rw [hav]; simp [eI]
    have ha2 : a (Fin.last (m + 1)) = eI k r ⟨m + 1, by omega⟩ := by ext; rw [hav]; simp [eI]
    rw [ha1, ha2, hR1]
  rw [la_intmul, hmT, hQm]
  have h3 : ((((-1 : ℤ) ^ (m + 1 + ((Fin.castSucc (Fin.last m) : Fin (m + 2)) : ℕ))) : ℤ) : ℂ) = -1 := by
    simp only [Fin.val_castSucc, Fin.val_last]
    push_cast
    rw [show m + 1 + m = 2 * m + 1 by ring, pow_succ, pow_mul]; norm_num
  rw [h3, neg_one_smul]; abel

end Formalism.FourierDecayAlt.P.PBN
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXMkTopCut
section
noncomputable section

open Matrix MeasureTheory
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutEXMT

open Formalism.FourierDecayAlt

def MkTopCut : Prop :=
  ∀ r : ℕ, ∃ β : (Fin r → Fin r → ℂ) → ℝ,
    ContDiffOn ℝ ∞ β {Z | (Matrix.of Z).det ≠ 0} ∧
    (∀ Z : Fin r → Fin r → ℂ, (Matrix.of Z).det ≠ 0 →
      Integrable (fun v : G.UT r → ℂ => β (Matrix.of.symm (Matrix.of Z * G.upper v))) ∧
        ∫ v : G.UT r → ℂ, β (Matrix.of.symm (Matrix.of Z * G.upper v)) = 1) ∧
    ∀ (X : Type) [TopologicalSpace X] (K : Set ((Fin r → Fin r → ℂ) × X)), IsCompact K →
      (∀ q ∈ K, (Matrix.of q.1).det ≠ 0) →
      ∃ K' : Set ((Fin r → Fin r → ℂ) × X), IsCompact K' ∧
        (∀ q ∈ K', (Matrix.of q.1).det ≠ 0 ∧ ∃ q₀ ∈ K, q.2 = q₀.2) ∧
        ∀ q : (Fin r → Fin r → ℂ) × X, (Matrix.of q.1).det ≠ 0 → β q.1 ≠ 0 →
          (∃ u : Matrix (Fin r) (Fin r) ℂ, Formalism.DoubleCosetMeasures.IsUpUni u ∧ (Matrix.of.symm (Matrix.of q.1 * u), q.2) ∈ K) →
          q ∈ K'

end Formalism.FourierDecayAlt.P.CutEXMT
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCGenToQQ
section
noncomputable section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

section hs

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem hsv_add (A C : Wq →L[ℂ] Wp) : B.hsVec (A + C) = B.hsVec A + B.hsVec C := by
  unfold B.hsVec
  rw [← WithLp.toLp_add]
  rfl

theorem hsv_smul (c : ℂ) (A : Wq →L[ℂ] Wp) : B.hsVec (c • A) = c • B.hsVec A := by
  unfold B.hsVec
  rw [← WithLp.toLp_smul]
  rfl

end hs

section intw

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq}
  {e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)}

def Intw (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (A : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) (A' : MA.A P (MA.DQ P)) : Prop :=
  ∀ Φ, trR P Bs e (A.1 Φ) = MA.actA P A' (trR P Bs e Φ)

theorem rawR_add (Φ Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (ρ : M.Ty P) :
    rawR P Bs.μsec e ((Φ + Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ =
      rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ + rawR P Bs.μsec e (Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ := by
  funext q
  simp only [rawR, Submodule.coe_add, Pi.add_apply, hsv_add, inner_add_right, mul_add]

theorem rawR_smul (c : ℂ) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (ρ : M.Ty P) :
    rawR P Bs.μsec e ((c • Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ =
      c • rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ := by
  funext q
  simp only [rawR, Submodule.coe_smul, Pi.smul_apply, hsv_smul, inner_smul_right, smul_eq_mul]
  ring

theorem toSm_smul' {u : MA.Qp P.r P.TT → ℂ} (c : ℂ) (hu : u ∈ MA.smSub P.r P.TT) :
    MA.toSm P (c • u) = c • MA.toSm P u := by
  rw [toSm_of_mem P hu, toSm_of_mem P (Subalgebra.smul_mem _ hu c)]
  rfl

end intw

section clos

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq}
  {e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)}

theorem trR_add (hsm : ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') ρ,
      rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ ∈ MA.smSub P.r P.TT)
    (Φ Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : trR P Bs e (Φ + Ψ) = trR P Bs e Φ + trR P Bs e Ψ := by
  funext ρ
  simp only [trR, Pi.add_apply]
  rw [rawR_add, toSm_add P (hsm Φ ρ) (hsm Ψ ρ)]

theorem trR_smul (hsm : ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') ρ,
      rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ ∈ MA.smSub P.r P.TT)
    (c : ℂ) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : trR P Bs e (c • Φ) = c • trR P Bs e Φ := by
  funext ρ
  simp only [trR, Pi.smul_apply]
  rw [rawR_smul, toSm_smul' c (hsm Φ ρ)]

theorem actA_smulM (c : ℂ) (x : MA.A P (MA.DQ P)) (f : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (c • x) f = c • MA.actA P x f := by
  funext π
  show ∑ π', ((c • x) π π').1 (f π') = c • ∑ π', (x π π').1 (f π')
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun π' _ => ?_
  rw [Matrix.smul_apply, Algebra.smul_def]
  rfl

theorem actA_one (f : M.Ty P → MA.SmQ P.r P.TT) : MA.actA P 1 f = f := by
  funext π
  show ∑ π', ((1 : MA.A P (MA.DQ P)) π π').1 (f π') = f π
  rw [Fintype.sum_eq_single π (fun b hb => by rw [Matrix.one_apply_ne (Ne.symm hb)]; rfl), Matrix.one_apply_eq]
  rfl

theorem actA_alg (c : ℂ) (f : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (algebraMap ℂ (MA.A P (MA.DQ P)) c) f = c • f := by
  rw [Algebra.algebraMap_eq_smul_one, actA_smulM, actA_one]

variable (hsm : ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') ρ,
      rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ ∈ MA.smSub P.r P.TT)
include hsm

theorem intw_add {A B : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} {A' B' : MA.A P (MA.DQ P)}
    (hA : Intw P Bs e A A') (hB : Intw P Bs e B B') : Intw P Bs e (A + B) (A' + B') := by
  intro Φ
  show trR P Bs e (A.1 Φ + B.1 Φ) = _
  rw [trR_add hsm, hA, hB, actA_add]

theorem intw_mul {A B : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} {A' B' : MA.A P (MA.DQ P)}
    (hA : Intw P Bs e A A') (hB : Intw P Bs e B B') : Intw P Bs e (A * B) (A' * B') := by
  intro Φ
  show trR P Bs e (A.1 (B.1 Φ)) = _
  rw [hA, hB, actA_mul]

theorem intw_alg (c : ℂ) : Intw P Bs e (algebraMap ℂ _ c) (algebraMap ℂ (MA.A P (MA.DQ P)) c) := by
  intro Φ
  show trR P Bs e (c • Φ) = _
  rw [trR_smul hsm, actA_alg]

theorem intw_neg {A : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} {A' : MA.A P (MA.DQ P)}
    (hA : Intw P Bs e A A') : Intw P Bs e (-A) (-A') := by
  have h := intw_mul hsm (intw_alg hsm (-1)) hA
  intro Φ
  have e1 : (-A) = algebraMap ℂ _ (-1) * A := by simp
  have e2 : (-A') = algebraMap ℂ (MA.A P (MA.DQ P)) (-1) * A' := by simp
  rw [e1, e2]
  exact h Φ

theorem intw_sub {A B : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} {A' B' : MA.A P (MA.DQ P)}
    (hA : Intw P Bs e A A') (hB : Intw P Bs e B B') : Intw P Bs e (A - B) (A' - B') := by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  exact intw_add hsm hA (intw_neg hsm hB)

theorem intw_zero : Intw P Bs e 0 0 := by
  intro Φ
  show trR P Bs e 0 = MA.actA P 0 (trR P Bs e Φ)
  rw [actA_zero]
  have h := trR_smul hsm 0 Φ
  rw [zero_smul, zero_smul] at h
  exact h

theorem intw_sum {ι : Type} (s : Finset ι) {A : ι → Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')}
    {A' : ι → MA.A P (MA.DQ P)} (h : ∀ i ∈ s, Intw P Bs e (A i) (A' i)) :
    Intw P Bs e (∑ i ∈ s, A i) (∑ i ∈ s, A' i) := by
  first | exact UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum .. | (apply UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum <;> assumption) | (intros; apply UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum <;> assumption) | (apply @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum <;> assumption) | (apply @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp Wq ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› P Bs e hsm ι s A A' h | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp Wq ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› P Bs e hsm ι s A A' | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp Wq ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› P Bs e hsm ι s A | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp Wq ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› P Bs e hsm ι s | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp Wq ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› P Bs e hsm ι | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp Wq ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› P Bs e hsm | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp Wq ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› P Bs e | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp Wq ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› P Bs | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp Wq ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› P | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp Wq ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp Wq ‹_› ‹_› ‹_› ‹_› ‹_› | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp Wq ‹_› ‹_› ‹_› ‹_› | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp Wq ‹_› ‹_› ‹_› | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp Wq ‹_› ‹_› | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp Wq ‹_› | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp Wq | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp

end clos

theorem generator_to_quadratic_form : GenToQQ := by
  intro hRS hGT Wp Wq _ _ _ _ _ _ P Bs hPl hk hsec X
  obtain ⟨d, hL, hstar, hrel, hQQ⟩ := Formalism.FourierDecayAlt.P.normal_form_actual Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hPl X
  obtain ⟨e, he, hg⟩ := hGT Wp Wq P Bs hPl hk hsec X d hL hstar hrel hQQ
  have hsm : ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') ρ,
      rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ ∈ MA.smSub P.r P.TT :=
    fun Φ ρ => hRS Wp Wq P Bs hPl hk e he Φ ρ
  refine ⟨e, he, fun Φ Y a b => ?_⟩

  have hζ : Intw P Bs e d.L.ζ (MA.zA P (MA.DQ P)) := fun Φ => (hg Φ).1
  have hζi : Intw P Bs e d.L.ζi (MA.ziA P (MA.DQ P)) := fun Φ => (hg Φ).2.1
  have hζb : Intw P Bs e d.L.ζb (MA.zbA P (MA.DQ P)) := fun Φ => (hg Φ).2.2.1
  have hζbi : Intw P Bs e d.L.ζbi (MA.zbiA P (MA.DQ P)) := fun Φ => (hg Φ).2.2.2.1
  have hGG : Intw P Bs e d.L.GG (MA.ggA P (MA.DQ P)) := fun Φ => (hg Φ).2.2.2.2.1
  have hGGi : Intw P Bs e d.L.GGi (MA.ggiA P (MA.DQ P)) := fun Φ => (hg Φ).2.2.2.2.2.1
  have hnab : Intw P Bs e d.L.nab (MA.nabA P (MA.DQ P)) := fun Φ => (hg Φ).2.2.2.2.2.2.1
  have hnabs : Intw P Bs e d.L.nabs (MA.nabsA P (MA.DQ P)) := fun Φ => (hg Φ).2.2.2.2.2.2.2.1
  have hκ : ∀ f, Intw P Bs e (d.κ f) (MA.kap P (MA.DQ P) f) := fun f Φ => (hg Φ).2.2.2.2.2.2.2.2.1 f
  have hSS : ∀ l ∈ Finset.Icc 1 (P.k - 1), Intw P Bs e (d.SS l) (MA.SS P (MA.DQ P) l) :=
    fun l hl Φ => (hg Φ).2.2.2.2.2.2.2.2.2.1 l hl
  have hSSs : ∀ l ∈ Finset.Icc 1 (P.k - 1), Intw P Bs e (star (d.SS l)) (star (MA.SS P (MA.DQ P) l)) :=
    fun l hl Φ => (hg Φ).2.2.2.2.2.2.2.2.2.2 l hl

  have hx : Intw P Bs e (d.x Y) (MA.xA P (MA.DQ P) Y) := hκ _
  have hl0 : Intw P Bs e (d.L.l0 Y) (MA.l0A P (MA.DQ P) Y) := by
    show Intw P Bs e (-d.L.nab - algebraMap ℂ _ (Y + 1/2) * (d.L.ζb * d.L.GGi))
      (-MA.nabA P (MA.DQ P) - algebraMap ℂ (MA.A P (MA.DQ P)) (Y + 1 / 2) * (MA.zbA P (MA.DQ P) * MA.ggiA P (MA.DQ P)))
    exact intw_sub hsm (intw_neg hsm hnab) (intw_mul hsm (intw_alg hsm _) (intw_mul hsm hζb hGGi))
  have hm0 : Intw P Bs e (d.L.m0 Y) (MA.m0A P (MA.DQ P) Y) := by
    show Intw P Bs e (-d.L.nabs - algebraMap ℂ _ (Y - 1/2) * (d.L.ζ * d.L.GGi))
      (-MA.nabsA P (MA.DQ P) - algebraMap ℂ (MA.A P (MA.DQ P)) (Y - 1 / 2) * (MA.zA P (MA.DQ P) * MA.ggiA P (MA.DQ P)))
    exact intw_sub hsm (intw_neg hsm hnabs) (intw_mul hsm (intw_alg hsm _) (intw_mul hsm hζ hGGi))
  have hS21 : Intw P Bs e (d.weightedSumBis Y) (MA.weightedSumBis P (MA.DQ P) Y) :=
    intw_sum hsm _ fun l hl => intw_mul hsm (hSS l hl) (hκ _)
  have hS12 : Intw P Bs e (d.S12 Y) (MA.S12 P (MA.DQ P) Y) :=
    intw_sum hsm _ fun l hl => intw_mul hsm (hκ _) (hSSs l hl)
  have hS4 : Intw P Bs e (d.S4 Y) (MA.S4 P (MA.DQ P) Y) :=
    intw_sum hsm _ fun l hl => intw_sum hsm _ fun j hj =>
      intw_mul hsm (intw_mul hsm (hSSs l hl) (hSS j (Finset.mem_of_mem_erase hj))) (hκ _)

  have hent : ∀ a b : Fin 2, Intw P Bs e (d.QQ Y a b) (MA.QQr P (MA.DQ P) Y a b) := by
    intro a b
    fin_cases a <;> fin_cases b
    · show Intw P Bs e (d.L.GGi * (d.κ fun ρ => M.wC P ρ Y) + d.L.GG * d.x Y * d.L.m0 Y * d.L.l0 Y +
          d.L.GG * d.L.m0 Y * d.L.GGi * d.weightedSumBis Y + d.S12 Y * d.L.l0 Y + d.L.GGi * d.S4 Y) (MA.t11 P (MA.DQ P) Y)
      exact intw_add hsm (intw_add hsm (intw_add hsm (intw_add hsm (intw_mul hsm hGGi (hκ _))
        (intw_mul hsm (intw_mul hsm (intw_mul hsm hGG hx) hm0) hl0))
        (intw_mul hsm (intw_mul hsm (intw_mul hsm hGG hm0) hGGi) hS21))
        (intw_mul hsm hS12 hl0)) (intw_mul hsm hGGi hS4)
    · show Intw P Bs e (d.L.GG * d.x Y * d.L.m0 Y + d.S12 Y) (MA.t12 P (MA.DQ P) Y)
      exact intw_add hsm (intw_mul hsm (intw_mul hsm hGG hx) hm0) hS12
    · show Intw P Bs e (d.L.GG * d.x Y * d.L.l0 Y + d.weightedSumBis Y) (MA.t21 P (MA.DQ P) Y)
      exact intw_add hsm (intw_mul hsm (intw_mul hsm hGG hx) hl0) hS21
    · show Intw P Bs e (d.L.GG * d.x Y) (MA.t22 P (MA.DQ P) Y)
      exact intw_mul hsm hGG hx
  have ht : X.t Y a b = (X.QQ Y a b).1 := rfl
  rw [ht, hQQ Y]
  exact hent a b Φ

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCCurvPolyCut
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

def sumU (P : M.Par) : ℂ := ∑ i ∈ Finset.Icc 1 P.k, ((P.u i : ℂ) + (P.u' i : ℂ))

def GTCCurvScal : Prop :=
  ∀ (P : M.Par), 2 ≤ P.k → ∀ ρ : M.Ty P,
    (∃ c : ℕ → ℂ, ∀ u : ℂ, M.wC P ρ u = u ^ (P.k + 1) * (-(P.TT : ℂ)) +
        u ^ P.k * ((P.TT : ℂ) * ((absTy P ρ : ℂ) - 1 - sumU P)) + ∑ i ∈ Finset.range P.k, u ^ i * c i) ∧
    (∃ c : ℕ → ℂ, ∀ u : ℂ, M.xC P ρ u = u ^ (P.k - 1) + (absTy P ρ : ℂ) * u ^ (P.k - 2) +
        ∑ i ∈ Finset.range (P.k - 2), u ^ i * c i) ∧
    (∀ ex : Finset ℕ, (∃ l ∈ ex, l ∈ Finset.Icc 1 (P.k - 1)) →
      ∃ c : ℕ → ℂ, ∀ u : ℂ, M.xEx P ex ρ u = ∑ i ∈ Finset.range (P.k - 1), u ^ i * c i)

def GTCCurvPolyOfScal : Prop := GTCCurvScal → GTCCurvPoly

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCCurvRTT
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

open Formalism.FourierDecayAlt.P.MAx3.G

section PolyTools

variable {R : Type} [Ring R] [Algebra ℂ R]

theorem curv_polyIn_congr {f g : ℂ → R} {d : ℕ} (h : PolyIn f d) (e : ∀ s, g s = f s) : PolyIn g d := by
  obtain ⟨a, ha⟩ := h
  exact ⟨a, fun s => by rw [e, ha]⟩

theorem curv_polyIn_csmul {f : ℂ → R} {d : ℕ} (c : ℂ) (hf : PolyIn f d) : PolyIn (fun s => c • f s) d := by
  obtain ⟨a, ha⟩ := hf
  exact ⟨fun k => c • a k, fun s => by dsimp only; rw [ha, Finset.smul_sum]; simp only [smul_comm c]⟩

theorem curv_polyIn_sub {f g : ℂ → R} {d : ℕ} (hf : PolyIn f d) (hg : PolyIn g d) :
    PolyIn (fun s => f s - g s) d :=
  curv_polyIn_congr (polyIn_add hf (curv_polyIn_csmul (-1) hg)) fun s => by simp [sub_eq_add_neg]

theorem curv_polyIn_monomial (n : ℕ) (x : R) : PolyIn (fun s => s ^ n • x) n := by
  refine ⟨fun k => if k = n then x else 0, fun s => ?_⟩
  dsimp only
  rw [Finset.sum_eq_single n (fun b _ hb => by rw [if_neg hb, smul_zero])
    (fun h => absurd (Finset.mem_range.2 (Nat.lt_succ_self n)) h), if_pos rfl]

end PolyTools

theorem curv_top_zero {E : Type*} [AddCommGroup E] [Module ℂ E] (n : ℕ) (c : E) (a : ℕ → E)
    (h : ∀ u : ℂ, u ^ (n + 1) • c = ∑ i ∈ Finset.range (n + 1), u ^ i • a i) : c = 0 := by
  rw [← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro φ
  set p : Polynomial ℂ := Polynomial.C (φ c) * Polynomial.X ^ (n + 1) -
    ∑ i ∈ Finset.range (n + 1), Polynomial.C (φ (a i)) * Polynomial.X ^ i with hpdef
  have hp : p = 0 := by
    apply Polynomial.funext
    intro u
    have hu := congrArg φ (h u)
    simp only [map_smul, map_sum, smul_eq_mul] at hu
    simp only [hpdef, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_finsetSum, Polynomial.eval_zero]
    rw [mul_comm (φ c), hu, sub_eq_zero]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hc := congrArg (fun q => Polynomial.coeff q (n + 1)) hp
  simp only [hpdef, Polynomial.coeff_sub, Polynomial.coeff_C_mul_X_pow, Polynomial.finsetSum_coeff,
    Polynomial.coeff_zero] at hc
  rw [Finset.sum_eq_zero (fun i hi => by
    rw [if_neg (by have := Finset.mem_range.1 hi; omega)]), sub_zero] at hc
  exact hc

theorem curvature_radial_torus_holds : GTCCurvRTT := by
  intro A _ _ n f g Θ hn hrtt hF hg v
  set T := g v with hT
  set F : ℂ → A := fun u => f u - u ^ (n + 1) • (1 : A) - u ^ n • Θ with hFdef
  have hn' : n - 1 + 1 = n := Nat.sub_add_cancel hn
  have hG : PolyIn (fun u => F u * T - T * F u) (n - 1) :=
    curv_polyIn_sub (polyIn_mul_const hF T) (polyIn_const_mul T hF)
  have hSt : PolyIn (fun u => g u * f v - u ^ n • (T * Θ) - T * F u + v • (u ^ n • (Θ * T - T * Θ)) -
      u • (F u * T - T * F u) + v • (F u * T - T * F u)) n := by
    refine polyIn_add (curv_polyIn_sub (polyIn_add (curv_polyIn_sub (curv_polyIn_sub (polyIn_mul_const hg (f v))
      (curv_polyIn_monomial n (T * Θ))) (polyIn_mono (polyIn_const_mul T hF) (by omega)))
      (curv_polyIn_csmul v (curv_polyIn_monomial n (Θ * T - T * Θ)))) ?_) ?_
    · have := polyIn_smul_var hG
      rw [hn'] at this
      exact this
    · exact polyIn_mono (curv_polyIn_csmul v hG) (by omega)
  obtain ⟨s, hs⟩ := hSt
  have key : ∀ u : ℂ, u ^ (n + 1) • (Θ * T - T * Θ + T) = ∑ i ∈ Finset.range (n + 1), u ^ i • s i := by
    intro u
    rw [← hs u]
    have hfu : f u = F u + u ^ (n + 1) • (1 : A) + u ^ n • Θ := by simp only [hFdef]; abel
    have h := hrtt u v
    rw [← hT, hfu] at h
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one] at h
    linear_combination (norm := module) h
  have h0 := curv_top_zero n _ s key
  exact eq_neg_of_add_eq_zero_left h0

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.KloostermanDensity
section
namespace Formalism.FourierDecayAlt.P

theorem kloosterman_density : Formalism.FourierDecayAlt.KB.KloostDens :=
  PBJ.Asm.kloosterman_density_of_parts PBJ.fubini_head_last_part PBJ.freeze_last_entry PBJ.long_orbital_integral_multiple PBJ.block_orbital_integral_multiple

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedF
section
namespace Formalism.FourierDecayAlt.P

theorem representation_smooth : NFRadRedS.RepSmooth := representation_smooth_of_log local_logarithm_unitary

theorem radical_reduction_surjective : Formalism.FourierDecayAlt.NF.RadRedSurj :=
  radical_surjective_of_parts local_smooth_section representation_smooth

end Formalism.FourierDecayAlt.P
end

