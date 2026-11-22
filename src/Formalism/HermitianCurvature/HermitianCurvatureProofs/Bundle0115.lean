import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0109
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0055
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0108
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0098
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0094
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreKLIsoAlg
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0102
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0059
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0088
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ParametersUPrimeForULower
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DiagonalTransferAction
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0046
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0110

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRCoreCut
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP

noncomputable section

section defs

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def Rc (Z : Q.Mx k r) (f : Q.Mx k r → E) : Q.Mx k r → E :=
  fun g => RdV (hpart1 (Hpk k r) Z) f g + Complex.I • RdV (hpart2 (Hpk k r) Z) f g

def wordR (w : List (Q.Mx k r)) (f : Q.Mx k r → E) : Q.Mx k r → E :=
  w.foldr (fun Z h => Rc Z h) f

def dZV (f : ℂ → E) (ζ : ℂ) : E := (1 / 2 : ℂ) • (fderiv ℝ f ζ 1 - Complex.I • fderiv ℝ f ζ Complex.I)

def dZbV (f : ℂ → E) (ζ : ℂ) : E := (1 / 2 : ℂ) • (fderiv ℝ f ζ 1 + Complex.I • fderiv ℝ f ζ Complex.I)

end defs

def GLc (k r : ℕ) (Z : Q.Mx k r) : Prop :=
  Q.inLieLev k r (Fin.last r) (hpart1 (Hpk k r) Z) ∧ Q.inLieLev k r (Fin.last r) (hpart2 (Hpk k r) Z)

def GWc (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (Z : Q.Mx k r) : Prop :=
  P.QrD.InLieW k r z (hpart1 (Hpk k r) Z) ∧ P.QrD.InLieW k r z (hpart2 (Hpk k r) Z)

def Dp (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) : Set (Q.Mx k r) := {g | 0 < Q.GGl k r z z' g}

def mu0 (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (ζ : ℂ) : Q.Mx k r := NF.muZ k r (TheSec.theSection k r z z') ζ

def etaZ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (ζ : ℂ) : Q.Mx k r :=
  (mu0 k r z z' ζ)⁻¹ * Matrix.of fun i j => NF.dZ (fun w => mu0 k r z z' w i j) ζ

def etaZb (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (ζ : ℂ) : Q.Mx k r :=
  (mu0 k r z z' ζ)⁻¹ * Matrix.of fun i j => NF.dZb (fun w => mu0 k r z z' w i j) ζ

def RcLin : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (D : Set (Q.Mx k r)) (f : Q.Mx k r → E),
    IsOpen D → Q.SmoothLev k r (Fin.last r) D f → ∀ g ∈ Q.Glev k r (Fin.last r) ∩ D,
    ∀ (a : ℂ) (Z Z' : Q.Mx k r), GLc k r Z → GLc k r Z' → Rc (a • Z + Z') f g = a • Rc Z f g + Rc Z' f g

def RcSmooth : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (D : Set (Q.Mx k r)) (f f' : Q.Mx k r → E),
    IsOpen D → Q.SmoothLev k r (Fin.last r) D f → Q.SmoothLev k r (Fin.last r) D f' → ∀ Z : Q.Mx k r, GLc k r Z →
      Q.SmoothLev k r (Fin.last r) D (Rc Z f) ∧
      (∀ (a : ℂ), ∀ g ∈ Q.Glev k r (Fin.last r) ∩ D, Rc Z (fun x => a • f x + f' x) g = a • Rc Z f g + Rc Z f' g) ∧
      ∀ (E' : Type) [NormedAddCommGroup E'] [NormedSpace ℂ E'] (L : E →L[ℂ] E'), ∀ g ∈ Q.Glev k r (Fin.last r) ∩ D,
        Rc Z (fun x => L (f x)) g = L (Rc Z f g)

def RcComm : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (D : Set (Q.Mx k r)) (f : Q.Mx k r → E),
    IsOpen D → Q.SmoothLev k r (Fin.last r) D f → ∀ Z₁ Z₂ : Q.Mx k r, GLc k r Z₁ → GLc k r Z₂ →
    ∀ g ∈ Q.Glev k r (Fin.last r) ∩ D,
      Rc Z₁ (Rc Z₂ f) g - Rc Z₂ (Rc Z₁ f) g = Rc (Z₁ * Z₂ - Z₂ * Z₁) f g

def LeftCov : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (π : Q.Mx k r → (Wp →L[ℂ] Wp)), IsCRepOn (UWset k r z) π → ContinuousOn π (UWset k r z) → inWb k r z →
    ∀ (D : Set (Q.Mx k r)) (F : Q.Mx k r → (Wq →L[ℂ] Wp)), IsOpen D → (∀ h ∈ UWset k r z, ∀ g ∈ D, h * g ∈ D) →
    Q.SmoothLev k r (Fin.last r) D F →
    (∀ h ∈ UWset k r z, ∀ g ∈ Q.Glev k r (Fin.last r) ∩ D, F (h * g) = (π h).comp (F g)) →
    ∀ μ ∈ Q.Glev k r (Fin.last r) ∩ D, ∀ B : Q.Mx k r, GWc k r z B →
      GLc k r (μ⁻¹ * B * μ) ∧ Rc (μ⁻¹ * B * μ) F μ = (P.QrD.ecOp π B).comp (F μ)

def RightCov : Prop :=
  ∀ (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (π' : Q.Mx k r → (Wq →L[ℂ] Wq)), IsCRepOn (UWset k r z') π' → ContinuousOn π' (UWset k r z') → inWb k r z' →
    ∀ (D : Set (Q.Mx k r)) (F : Q.Mx k r → (Wq →L[ℂ] Wp)), IsOpen D → (∀ h ∈ UWset k r z', ∀ g ∈ D, g * h ∈ D) →
    Q.SmoothLev k r (Fin.last r) D F →
    (∀ h ∈ UWset k r z', ∀ g ∈ Q.Glev k r (Fin.last r) ∩ D, F (g * h) = (F g).comp (π' h)) →
    ∀ g ∈ Q.Glev k r (Fin.last r) ∩ D, ∀ A : Q.Mx k r, GWc k r z' A →
      GLc k r A ∧ Rc A F g = (F g).comp (P.QrD.ecOp π' A)

def SecDeriv : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' →
    ∀ ζ : ℂ, (Tz k r z * Tz k r z') < Complex.normSq ζ →
      GLc k r (etaZ k r z z' ζ) ∧ GLc k r (etaZb k r z z' ζ) ∧ (mu0 k r z z' ζ) ∈ Q.Glev k r (Fin.last r) ∩ Dp k r z z' ∧
      ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (F : Q.Mx k r → E),
        Q.SmoothLev k r (Fin.last r) (Dp k r z z') F →
        Rc (etaZ k r z z' ζ) F (mu0 k r z z' ζ) = dZV (fun w => F (mu0 k r z z' w)) ζ ∧
        Rc (etaZb k r z z' ζ) F (mu0 k r z z' ζ) = dZbV (fun w => F (mu0 k r z z' w)) ζ

def Decomp : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' →
    ∀ a b : Fin (k + 1), ∃ (n₁ n₂ : ℕ) (B₁ : Fin n₁ → Q.Mx k r) (b₁ : Fin n₁ → ℂ → ℂ) (B₂ : Fin n₂ → Q.Mx k r)
      (b₂ : Fin n₂ → ℂ → ℂ) (β₁ β₂ : ℂ → ℂ),
      (∀ t, GWc k r z' (B₁ t)) ∧ (∀ t, GWc k r z (B₂ t)) ∧ (∀ t, PS (Tz k r z * Tz k r z') (b₁ t)) ∧ (∀ t, PS (Tz k r z * Tz k r z') (b₂ t)) ∧
      PS (Tz k r z * Tz k r z') β₁ ∧ PS (Tz k r z * Tz k r z') β₂ ∧
      ∀ ζ : ℂ, (Tz k r z * Tz k r z') < Complex.normSq ζ →
        Matrix.single (wI k r a) (wI k r b) (1 : ℂ) =
          ∑ t, b₁ t ζ • B₁ t + (mu0 k r z z' ζ)⁻¹ * (∑ t, b₂ t ζ • B₂ t) * (mu0 k r z z' ζ) +
            β₁ ζ • etaZ k r z z' ζ + β₂ ζ • etaZb k r z z' ζ

def PSCalc : Prop :=
  ∀ (TT : ℝ), 0 < TT →
    (∀ c : ℂ, PS TT (fun _ => c)) ∧ PS TT id ∧ PS TT (fun ζ => conj ζ) ∧ PS TT (sig TT) ∧ PS TT (fun ζ => (gg TT ζ)⁻¹) ∧
    (∀ f g, PS TT f → PS TT g → PS TT (fun ζ => f ζ + g ζ) ∧ PS TT (fun ζ => f ζ * g ζ)) ∧
    (∀ f, PS TT f → PS TT (NF.dZ f) ∧ PS TT (NF.dZb f)) ∧
    ∀ (V V' : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup V'] [NormedSpace ℂ V'],
      (∀ f g : ℂ → V, PSV TT f → PSV TT g → PSV TT (fun ζ => f ζ + g ζ)) ∧
      (∀ (a : ℂ → ℂ) (f : ℂ → V), PS TT a → PSV TT f → PSV TT (fun ζ => a ζ • f ζ)) ∧
      (∀ (L : V →ₗ[ℂ] V') (f : ℂ → V), PSV TT f → PSV TT (fun ζ => L (f ζ))) ∧
      (∀ (f : ℂ → V), PSV TT f → PSV TT (dZV f) ∧ PSV TT (dZbV f)) ∧
      (∀ v : V, PSV TT (fun _ => v))

def LowerUnipotentMatrixWords : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' →
    ∀ Y : ℂ, ∃ (n : ℕ) (κ : Fin n → ℂ → ℂ) (w : Fin n → List (Q.Mx k r)),
      (∀ i, PS (Tz k r z * Tz k r z') (κ i)) ∧ (∀ i, ∀ Z ∈ w i, ∃ a b : Fin (k + 1), Z = Matrix.single (wI k r a) (wI k r b) 1) ∧
      ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (F : Q.Mx k r → E),
        Q.SmoothLev k r (Fin.last r) (Dp k r z z') F → ∀ ζ : ℂ, (Tz k r z * Tz k r z') < Complex.normSq ζ →
          Q.tL k r z z' (Fin.last r) Y 1 0 F (mu0 k r z z' ζ) = ∑ i, κ i ζ • wordR (w i) F (mu0 k r z z' ζ)

def WordPSV : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → Bs.μsec = TheSec.theSection P.k P.r Bs.z Bs.z' →
    ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (X₀ : Wq →L[ℂ] Wp),
      (∀ c ∈ OmX P.r, ∀ ζ ∈ Gauge.GC.Ann P,
        (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ) = X₀) →
      ∀ c ∈ OmX P.r, ∀ w : List (Q.Mx P.k P.r), (∀ Z ∈ w, GLc P.k P.r Z) →
        PSV P.TT (fun ζ => wordR w ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c) (NF.muZ P.k P.r Bs.μsec ζ))

def WordPSVOfCut : Prop :=
  RcLin → RcSmooth → RcComm → LeftCov → RightCov → SecDeriv → Decomp → PSCalc → WordPSV

def CorePolyOfCut : Prop := LowerUnipotentMatrixWords → WordPSV → PSCalc → CorePoly

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRPhaseExtract
section
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR

theorem evenPart_poly (c : ℂ) (p : MvPolynomial (Fin 3) ℂ) :
    ∃ q : Polynomial ℂ, ∀ t s : ℂ, t ^ 2 = s ^ 2 + c →
      MvPolynomial.eval ![t, t, s] p + MvPolynomial.eval ![-t, -t, s] p = q.eval s := by
  induction p using MvPolynomial.induction_on' with
  | monomial u a =>
    rcases Nat.even_or_odd' (u 0 + u 1) with ⟨j, hj | hj⟩
    · refine ⟨Polynomial.C (2 * a) * (Polynomial.X ^ 2 + Polynomial.C c) ^ j * Polynomial.X ^ (u 2), fun t s h => ?_⟩
      simp only [MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_three,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X]
      rw [← pow_add, ← pow_add, hj, pow_mul, pow_mul, neg_sq, h]
      ring
    · refine ⟨0, fun t s h => ?_⟩
      simp only [MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_three,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
        Polynomial.eval_zero]
      rw [← pow_add, ← pow_add, hj, Odd.neg_pow ⟨j, rfl⟩]
      ring
  | add p₁ p₂ h₁ h₂ =>
    obtain ⟨q₁, hq₁⟩ := h₁
    obtain ⟨q₂, hq₂⟩ := h₂
    refine ⟨q₁ + q₂, fun t s h => ?_⟩
    rw [map_add, map_add, Polynomial.eval_add, ← hq₁ t s h, ← hq₂ t s h]
    ring

theorem phase_extraction_holds : PhaseExtract := by
  intro TT f _ hPS hrot
  obtain ⟨m, p, hp⟩ := hPS
  obtain ⟨q, hq⟩ := evenPart_poly (TT : ℂ) p
  refine ⟨m, Polynomial.C (1 / 2) * q, fun ζ hζ => ?_⟩
  have hn : Complex.normSq ((‖ζ‖ : ℝ) : ℂ) = Complex.normSq ζ := by
    rw [Complex.normSq_ofReal, Complex.normSq_eq_norm_sq]; ring
  have hn' : Complex.normSq (-((‖ζ‖ : ℝ) : ℂ)) = Complex.normSq ζ := by
    rw [Complex.normSq_neg, hn]
  have h1 : f ζ = f ((‖ζ‖ : ℝ) : ℂ) := by
    have := hrot (Complex.arg ζ) ((‖ζ‖ : ℝ) : ℂ) (by rw [hn]; exact hζ)
    rw [← this]
    congr 1
    unfold rot
    rw [mul_comm, Complex.norm_mul_exp_arg_mul_I]
  have h2 : f ζ = f (-((‖ζ‖ : ℝ) : ℂ)) := by
    have := hrot Real.pi ((‖ζ‖ : ℝ) : ℂ) (by rw [hn]; exact hζ)
    rw [h1, ← this]
    congr 1
    unfold rot
    rw [Complex.exp_pi_mul_I]; ring
  have e1 := hp ((‖ζ‖ : ℝ) : ℂ) (by rw [hn]; exact hζ)
  have e2 := hp (-((‖ζ‖ : ℝ) : ℂ)) (by rw [hn']; exact hζ)
  have g1 : gg TT ((‖ζ‖ : ℝ) : ℂ) = gg TT ζ := by unfold gg; rw [hn]
  have g2 : gg TT (-((‖ζ‖ : ℝ) : ℂ)) = gg TT ζ := by unfold gg; rw [hn']
  have s1 : sig TT ((‖ζ‖ : ℝ) : ℂ) = sig TT ζ := by unfold sig; rw [hn]
  have s2 : sig TT (-((‖ζ‖ : ℝ) : ℂ)) = sig TT ζ := by unfold sig; rw [hn']
  rw [g1, s1, ← h1, Complex.conj_ofReal] at e1
  rw [g2, s2, ← h2, map_neg, Complex.conj_ofReal] at e2
  have hcurve : (((‖ζ‖ : ℝ) : ℂ)) ^ 2 = sig TT ζ ^ 2 + (TT : ℂ) := by
    unfold sig
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, Real.sq_sqrt (by linarith), ← Complex.ofReal_add,
      Complex.normSq_eq_norm_sq]
    congr 1; ring
  have := hq _ _ hcurve
  rw [← e1, ← e2] at this
  rw [Polynomial.eval_mul, Polynomial.eval_C, ← this]
  ring

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJATCDatumTransitFam
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC.DT

noncomputable section

variable {k r : ℕ}

def fam (k r : ℕ) (e : Fin (k + 1) → Fin (2 * r + k + 1) → ℂ) : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ :=
  fun i => if h : r ≤ i.val ∧ i.val ≤ r + k then e ⟨i.val - r, by omega⟩ else bvec i

def ONb (k r : ℕ) (e : Fin (k + 1) → Fin (2 * r + k + 1) → ℂ) : Prop :=
  (∀ a, inWb k r (e a)) ∧
    ∀ a b, herm (Hpk k r) (e a) (e b) = if a = b then (if a.val = k then -1 else 1) else 0

theorem hpk_out_in {i j : Fin (2 * r + k + 1)} (hi : i.val < r ∨ r + k < i.val) (hj : r ≤ j.val ∧ j.val ≤ r + k) :
    Hpk k r i j = 0 ∧ Hpk k r j i = 0 := by
  constructor <;> simp only [Hpk] <;> split_ifs <;> first | rfl | (exfalso; omega)

theorem herm_bvec_bvec (i j : Fin (2 * r + k + 1)) : herm (Hpk k r) (bvec i) (bvec j) = Hpk k r j i := by
  simp [herm, bvec, dotProduct, Matrix.mulVec, Pi.single_apply]

theorem herm_bvec_w {i : Fin (2 * r + k + 1)} (hi : i.val < r ∨ r + k < i.val) {w : Fin (2 * r + k + 1) → ℂ}
    (hw : inWb k r w) : herm (Hpk k r) (bvec i) w = 0 := by
  have hc : ∀ l, (Hpk k r *ᵥ bvec i) l = Hpk k r l i := fun l => by
    simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]
  simp only [herm, dotProduct, hc]
  apply Finset.sum_eq_zero
  intro l _
  by_cases hl : r ≤ l.val ∧ l.val ≤ r + k
  · rw [(hpk_out_in hi hl).2, mul_zero]
  · rw [Pi.star_apply, hw l (by omega), star_zero, zero_mul]

theorem herm_w_bvec {i : Fin (2 * r + k + 1)} (hi : i.val < r ∨ r + k < i.val) {w : Fin (2 * r + k + 1) → ℂ}
    (hw : inWb k r w) : herm (Hpk k r) w (bvec i) = 0 := by
  have hc : herm (Hpk k r) w (bvec i) = (Hpk k r *ᵥ w) i := by
    simp [herm, bvec, dotProduct, Pi.single_apply]
  rw [hc]
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_eq_zero
  intro l _
  by_cases hl : r ≤ l.val ∧ l.val ≤ r + k
  · rw [(hpk_out_in hi hl).1, zero_mul]
  · rw [hw l (by omega), mul_zero]

theorem fam_in {e : Fin (k + 1) → Fin (2 * r + k + 1) → ℂ} {i : Fin (2 * r + k + 1)} (h : r ≤ i.val ∧ i.val ≤ r + k) :
    fam k r e i = e ⟨i.val - r, by omega⟩ := by
  simp only [fam]
  rw [dif_pos h]

theorem fam_out {e : Fin (k + 1) → Fin (2 * r + k + 1) → ℂ} {i : Fin (2 * r + k + 1)} (h : i.val < r ∨ r + k < i.val) :
    fam k r e i = bvec i := by
  simp only [fam]
  rw [dif_neg]
  omega

theorem famGram {e : Fin (k + 1) → Fin (2 * r + k + 1) → ℂ} (he : ONb k r e) (i j : Fin (2 * r + k + 1)) :
    herm (Hpk k r) (fam k r e i) (fam k r e j) = Hpk k r j i := by
  by_cases hi : r ≤ i.val ∧ i.val ≤ r + k <;> by_cases hj : r ≤ j.val ∧ j.val ≤ r + k
  · rw [fam_in hi, fam_in hj, he.2]
    simp only [Hpk]
    split_ifs <;> (try simp only [Fin.ext_iff, Fin.val_mk] at *) <;> first | rfl | (exfalso; omega)
  · rw [fam_in hi, fam_out (i := j) (by omega), herm_w_bvec (i := j) (by omega) (he.1 _),
      (hpk_out_in (i := j) (j := i) (by omega) hi).1]
  · rw [fam_out (i := i) (by omega), fam_in hj, herm_bvec_w (i := i) (by omega) (he.1 _),
      (hpk_out_in (i := i) (j := j) (by omega) hj).2]
  · rw [fam_out (i := i) (by omega), fam_out (i := j) (by omega), herm_bvec_bvec]

theorem out_cases {i : Fin (2 * r + k + 1)} (hi : i.val < r ∨ r + k < i.val) :
    (∃ a : Fin r, i = eI k r a) ∨ (∃ a : Fin r, i = esI k r a) := by
  have := i.isLt
  rcases hi with hi | hi
  · left
    exact ⟨⟨i.val, hi⟩, Fin.ext rfl⟩
  · right
    refine ⟨⟨2 * r + k - i.val, by omega⟩, Fin.ext ?_⟩
    show i.val = 2 * r + k - (2 * r + k - i.val)
    omega

theorem glev_fix {g : Q.Mx k r} (hg : g ∈ Q.Glev k r (Fin.last r)) {i : Fin (2 * r + k + 1)}
    (hi : i.val < r ∨ r + k < i.val) : g *ᵥ bvec i = bvec i := by
  obtain ⟨_, h2⟩ := hg
  rcases out_cases hi with ⟨a, rfl⟩ | ⟨a, rfl⟩
  · exact (h2 a (by rw [Fin.val_last]; exact a.isLt)).1
  · exact (h2 a (by rw [Fin.val_last]; exact a.isLt)).2

theorem uw_glev {z : Fin (2 * r + k + 1) → ℂ} {g : Q.Mx k r} (hg : g ∈ UWset k r z) : g ∈ Q.Glev k r (Fin.last r) := by
  obtain ⟨h1, h2, -⟩ := hg
  exact ⟨h1, fun a _ => h2 a⟩

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC.DT
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJATCLineNonzero
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC

noncomputable section

theorem line_nonvanishing_holds : LineNonzero := by
  intro Wp Wq _ _ _ _ _ _ P Bs hpl hk Pr hPr π ζ hζ
  have hζT : P.TT < Complex.normSq ζ := hζ
  obtain ⟨hOK, hz, hz', hTz, hTz', -, -⟩ := id hpl
  have hζ' : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ := by
    rw [hTz, hTz']; exact hζT
  have hT := Bs.T_pos
  obtain ⟨hνfix, hνν, -, -⟩ := DU.base hz hz' Bs.T_pos Bs.T'_pos Bs.sec hζ'
  set ν := SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ with hνdef

  set μ := NF.muZ P.k P.r Bs.μsec ζ with hμ
  have hm := NFRadRedA.muZ_uwb Bs.sec hζ'
  have hG := NFRadRedA.uwb_glev hm
  have hy : inWb P.k P.r (μ *ᵥ Bs.z') := Qx8.inWb_mulVec hG hz'
  have hνW : inWb P.k P.r ν := by
    show inWb P.k P.r (SSn.unitH P.k P.r (SSn.prWv P.k P.r Bs.z (μ *ᵥ Bs.z')))
    unfold SSn.unitH
    exact Qx8.inWb_smul (DU.prWv_inWb hz hy) _
  have hνz : herm (Hpk P.k P.r) ν Bs.z = 0 := by
    rw [← hνfix]; exact DU.prWv_perp hT hνW
  obtain ⟨Fr, hFr⟩ := Topx1.typ_frame_exists P.k P.r (by omega) Bs.z ν hz hT hνW hνz hνν
  obtain ⟨hFr', hpass⟩ := PRho.GL.gauge_left_line_holds Wp Wq P Bs hpl hk ζ hζT Fr hFr
  have hq : ((fun _ => (1 : ℂ)), ζ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨fun _ => one_ne_zero, hζ'⟩
  obtain ⟨-, hg, hGG⟩ := Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' Bs.sec hq
  have hEx := Gauge.GC.lie_existence_of_iso_group Gauge.GC.KLIso.lie_algebra_isomorphism_holds Gauge.GC.lie_group_realization
  obtain ⟨E, hEfib, hEeig, hE0⟩ := hEx Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hpl hk _ hg hGG.ne' _ hFr' π
  have hEF : E ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ :=
    fun p hp => hEfib p.1 hp.1 p.2 hp.2.1 hp.2.2
  have hgl' := (Formalism.FourierDecayAlt.P.frame_general_linear Wq P.k P.r (P.k - 1) Bs.z' Bs.π'
    (fun a => μ⁻¹ *ᵥ Fr a) ⟨Bs.π'_rep, Bs.π'_cont⟩
    (Formalism.FourierDecayAlt.P.Qx8.frame_sub hFr' (by simp))).2
  have hπrep : Qr.IsRepW P.k P.r Bs.z Bs.π := ⟨Bs.π_rep, Bs.π_cont⟩
  refine ⟨E, hEF, ?_, hE0⟩
  have hpos : 0 < PRho.nrmW P.k P.r Bs.z ν := by
    unfold PRho.nrmW
    rw [hνfix, hνν]; simp
  have hrange := ((hPr.2.2 ν hpos).2.2.2 π)
  ext v
  rw [ContinuousLinearMap.comp_apply]
  refine (hrange (E v)).2 ?_
  intro Fr2 hFr2 w
  rw [hνfix] at hFr2
  rw [Topx1.typ_frame_change P.k P.r (by omega) Bs.z ν Bs.π Fr2 Fr hz hT hνW hνz hνν hπrep hFr2 hFr w (E v),
    hpass E hEF w v, hgl']
  have hw : w = (w - ((P.k : ℂ) - 2) / 2) + ((P.k : ℂ) - 2) / 2 := by ring
  conv_lhs => rw [hw]
  exact hEeig _ v

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.DwPt
section
open Matrix MeasureTheory Finset
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.DiagonalScalarMatrices

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

section

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]

private lemma scalar_pow_mul_diagonal {A S : Type} [Ring A] [Fintype S] [DecidableEq S] (a : A) (n : ℕ)
    (D : Ix S → A) :
    (Matrix.scalar (Ix S) a) ^ n * Matrix.diagonal D = Matrix.diagonal (fun e => a ^ n * D e) := by
  rw [← map_pow, Matrix.scalar_apply, Matrix.diagonal_mul_diagonal]

theorem dw_pt (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (hD : IsData P z z' π π' X μ L st l0) (ws : List (Letter ℂ S)) (hw : WordOK P z z' π π' st l0 ws)
    (Y₀ : ℝ) (e : Ix S) (p : Polynomial ℂ)
    (hp : ∀ ρ : M.Ty P, p.eval (M.xC P ρ (Y₀ : ℂ)) = Fr.cs (M.x0 P l0 ρ) (M.qC P) ws e)
    (y : Ix S → RadSp P.k P.r z z' π π') (c : Fin P.r → ℂ) (g : Mx P.k P.r) (hx : (c, g) ∈ DomR P.k P.r z z')
    (Bs : Fin (P.k - 1) → Fin (2 * P.r + P.k + 1) → ℂ) (hBs : IsFrameOf P.k P.r [g⁻¹ *ᵥ z, z'] Bs) (v : Wq) :
    (act ((Fr.ofWord L st ws).d L) y e : Fn P.k P.r (Wq →L[ℂ] Wp)) c g v =
      (((Complex.normSq (zetaL P.k P.r z z' (Fin.last P.r) g) * (GGl P.k P.r z z' g)⁻¹ : ℝ) : ℂ) ^ ws.length) •
        (y e : Fn P.k P.r (Wq →L[ℂ] Wp)) c g
          (Polynomial.aeval (qdet (Qr.EB π' Bs) ((Y₀ : ℂ) + ((P.k : ℂ) - 2) / 2)) p v) := by
  have hD' := hD
  obtain ⟨hPl, -, hAL, hQQ, hq, -, -, hLS⟩ := hD'
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hGG, hGGi, -⟩ := id hAL
  obtain ⟨κ, hκx, hκxi, -⟩ := Formalism.FourierDecayAlt.P5.xKappaOfNF Formalism.FourierDecayAlt.P.normal_form_actual
    Formalism.FourierDecayAlt.P5.kappaFibrePos Wp Wq P z z' π π' X μ L st l0 hD
  let st' : Fr.Start (Pr (RadSp P.k P.r z z' π π')) :=
    { st with xi := fun Y => κ fun ρ => (M.x0 P l0 ρ Y)⁻¹ }
  have hxiw : ∀ l ∈ ws, st'.xi (l.pt + 1) = st.xi (l.pt + 1) ∧ st'.xi (l.pt - 1) = st.xi (l.pt - 1) := by
    intro l hl
    obtain ⟨-, h1, h2, -⟩ := hw.1.2.2.1 l hl
    exact ⟨(hκxi _ h1).symm, (hκxi _ h2).symm⟩
  have hc : (Fr.ofWord L st ws).c =
      Matrix.diagonal fun e => κ fun ρ => Fr.cs (M.x0 P l0 ρ) (M.qC P) ws e := by
    rw [← Formalism.FourierDecayAlt.P5.WordTransvectionCongruences.ofWord_c_congr L st st' rfl rfl ws hxiw,
      (Formalism.FourierDecayAlt.P.c_diagonal _ S P.r L st' (M.Ty P) κ (M.x0 P l0) (fun Y => hκx Y) (fun Y => rfl) ws).2.2,
      ← hq]
  have hd : (Fr.ofWord L st ws).d L = Matrix.diagonal (fun e => (L.ζ * L.ζb * L.GGi) ^ ws.length *
      κ (fun ρ => Fr.cs (M.x0 P l0 ρ) (M.qC P) ws e)) := by
    rw [Fr.FrameData.d, Formalism.FourierDecayAlt.P5.WordTransvectionCongruences.ofWord_N, hc]
    exact scalar_pow_mul_diagonal _ _ _
  set K := κ (fun ρ => M.xC P ρ (Y₀ : ℂ)) with hKdef
  have hs : M.sgn P l0 ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  have hK : K.1 = X.fn 5 * X.t (Y₀ : ℂ) 1 1 := by
    have t := hLS.tau (Y₀ : ℂ)
    rw [hQQ, hκx, Formalism.FourierDecayAlt.P5.signed_coordinate_eq_sign_smul, map_smul] at t
    have t1 := congrArg (Formalism.FourierDecayAlt.P5.Kfp.fstAlg _) t
    rw [map_mul, map_smul, Matrix.smul_apply, map_smul] at t1
    change M.sgn P l0 • X.t (Y₀ : ℂ) 1 1 = L.GG.1 * (M.sgn P l0 • K.1) at t1
    rw [hGG, mul_smul_comm] at t1
    have h4 : X.fn 4 * K.1 = X.t (Y₀ : ℂ) 1 1 := (smul_right_injective _ hs t1).symm
    have h54 : X.fn 5 * X.fn 4 = 1 := by
      have := congrArg Prod.fst L.GGi_GG
      rw [hGGi, hGG] at this
      exact this
    rw [← h4, ← mul_assoc, h54, one_mul]
  have hκf : κ (fun ρ => Fr.cs (M.x0 P l0 ρ) (M.qC P) ws e) = Polynomial.aeval K p :=
    Formalism.FourierDecayAlt.P5.Kfp.kappa_aeval (NFData.mk L κ (fun _ => 0)) (Y₀ : ℂ) p _ hp
  have hκf1 : (κ (fun ρ => Fr.cs (M.x0 P l0 ρ) (M.qC P) ws e)).1 = Polynomial.aeval K.1 p := by
    rw [hκf]
    exact (Polynomial.aeval_algHom_apply (Formalism.FourierDecayAlt.P5.Kfp.fstAlg _) K p).symm
  have hT : ∀ (Ψ : RadSp P.k P.r z z' π π') (w : Wq),
      ((K.1 Ψ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) c g w =
        (Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g (qdet (Qr.EB π' Bs) ((Y₀ : ℂ) + ((P.k : ℂ) - 2) / 2) w) := by
    intro Ψ w
    rw [hK]
    exact Formalism.FourierDecayAlt.P5.Kfp.diagonal_transfer_action X hPl.2.1 hPl.2.2.1 hPl.2.2.2.2.2.2.2.1 hPl.2.2.2.2.2.2.2.2.1 hx Bs hBs _ Ψ w
  have hA := Formalism.FourierDecayAlt.P5.Kfp.aeval_act K.1 _ hT p
  have hpow := Formalism.FourierDecayAlt.P5.WordTransvectionCongruences.pow_apply X L hAL ws.length
    ((κ (fun ρ => Fr.cs (M.x0 P l0 ρ) (M.qC P) ws e)).1 (y e)) (c, g) hx
  have hmul : ∀ a b : Pr (RadSp P.k P.r z z' π π'), (a * b).1 = a.1 * b.1 := fun _ _ => rfl
  rw [hd, Formalism.FourierDecayAlt.P5.WordTransvectionCongruences.act_diagonal, hmul, Module.End.mul_apply, hpow,
    _root_.smul_apply, hκf1, hA]
  congr 1
  simp only [fnVal]
  congr 1
  rw [Complex.ofReal_mul, Complex.ofReal_inv, ← Complex.mul_conj]
  rfl

end

end Formalism.FourierDecayAlt.P.DiagonalScalarMatrices
end
end

