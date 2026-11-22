import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1388
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1369
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTwistedClassesCharpoly
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SelfReciprocalLocalField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInfiniteDecomp
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactOneParameterLinesOfLieLines
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineSignMulSelf
section
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

noncomputable section

namespace GlobalTheory.HoweD.CCRSig

variable {W : Type} [DecidableEq W] {P Q R S : W → ℕ}

def unitAtS (j : Σ w : W, Ix (P w) (Q w) × Ix (R w) (S w)) (z : ℂ) : ∀ w : W, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ :=
  Pi.single j.1 (Matrix.single j.2.1 j.2.2 z)

theorem sum_unitAtS [Fintype W] (j k : Σ w : W, Ix (P w) (Q w) × Ix (R w) (S w)) (z z' : ℂ) :
    (∑ w, ∑ a, ∑ b, lineSign a b * unitAtS j z w a b * star (unitAtS k z' w a b)) =
      if j = k then lineSign j.2.1 j.2.2 * z * star z' else 0 := by
  obtain ⟨w0, a0, b0⟩ := j
  obtain ⟨w1, a1, b1⟩ := k
  rw [Finset.sum_eq_single w0]
  · by_cases hw : w1 = w0
    · subst hw
      simp only [unitAtS, Pi.single_eq_same]
      rw [Finset.sum_eq_single a0, Finset.sum_eq_single b0]
      · by_cases ha : a0 = a1
        · subst ha
          by_cases hb : b0 = b1
          · subst hb; simp
          · have : (⟨w1, a0, b0⟩ : Σ w : W, Ix (P w) (Q w) × Ix (R w) (S w)) ≠ ⟨w1, a0, b1⟩ := by
              intro h; simp at h; exact hb h
            simp [this, hb, Ne.symm hb]
        · have : (⟨w1, a0, b0⟩ : Σ w : W, Ix (P w) (Q w) × Ix (R w) (S w)) ≠ ⟨w1, a1, b1⟩ := by
            intro h; simp at h; exact ha h.1
          simp [this, ha, Ne.symm ha]
      · intro b _ hb; simp [Ne.symm hb]
      · simp
      · intro a _ ha; simp [Ne.symm ha]
      · simp
    · have : (⟨w0, a0, b0⟩ : Σ w : W, Ix (P w) (Q w) × Ix (R w) (S w)) ≠ ⟨w1, a1, b1⟩ := by
        intro h; exact hw (congrArg Sigma.fst h).symm
      simp [unitAtS, hw, this]
  · intro w _ hw; simp [unitAtS, hw]
  · simp

theorem sum_unitAtS_eq [Fintype W] (c : ∀ w : W, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) :
    c = ∑ j : (Σ w : W, Ix (P w) (Q w) × Ix (R w) (S w)), unitAtS j (c j.1 j.2.1 j.2.2) := by
  funext w a b
  simp only [Finset.sum_apply, Matrix.sum_apply, Fintype.sum_sigma, unitAtS]
  rw [Finset.sum_eq_single w]
  · simp only [Pi.single_eq_same]
    rw [Fintype.sum_prod_type, Finset.sum_eq_single a, Finset.sum_eq_single b]
    · simp
    · intro b' _ hb; simp [Matrix.single_apply, hb]
    · simp
    · intro a' _ ha; simp [Matrix.single_apply, ha]
    · simp
  · intro w' _ hw; simp [Pi.single_eq_of_ne' hw]
  · simp

end GlobalTheory.HoweD.CCRSig

namespace GlobalTheory.HoweD.CCRSig

variable {V : Type} [AddCommGroup V] [Module ℂ V] {W : Type} [DecidableEq W] {P Q R S : W → ℕ}

theorem lineSign_cases {P Q R S : ℕ} (a : Ix P Q) (b : Ix R S) : (lineSign a b : ℂ) = 1 ∨ (lineSign a b : ℂ) = -1 := by
  rcases a with a | a <;> rcases b with b | b <;> simp [lineSign]

theorem lineSign_mul_self {P Q R S : ℕ} (a : Ix P Q) (b : Ix R S) : lineSign a b * lineSign a b = 1 := by
  rcases a with a | a <;> rcases b with b | b <;> simp [lineSign]

theorem comm_expand (A A' B B' : Module.End ℂ V) (c u v : ℂ) :
    -(c • (A + u • A')) * (c • (B - v • B')) - (c • (B - v • B')) * -(c • (A + u • A')) =
      -((c * c) • ((A * B - B * A) - v • (A * B' - B' * A) + u • (A' * B - B * A') - (u * v) • (A' * B' - B' * A'))) := by
  simp only [neg_mul, mul_neg, smul_mul_assoc, mul_smul_comm, mul_add, add_mul, mul_sub, sub_mul]
  module

theorem inv_sq : (2 * ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ))⁻¹ * (2 * ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ))⁻¹ =
    (8 * (Real.pi : ℂ))⁻¹ := by
  have h : ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) = 2 * (Real.pi : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    push_cast; ring
  rw [← mul_inv]
  congr 1
  linear_combination 4 * h

def ccrM (H : (∀ w : W, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) → Module.End ℂ V)
    (j : Σ w : W, Ix (P w) (Q w) × Ix (R w) (S w)) : Module.End ℂ V :=
  (2 * ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ))⁻¹ •
    (H (unitAtS j 1) - (lineSign j.2.1 j.2.2 * Complex.I) • H (unitAtS j Complex.I))

def ccrD (H : (∀ w : W, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) → Module.End ℂ V)
    (j : Σ w : W, Ix (P w) (Q w) × Ix (R w) (S w)) : Module.End ℂ V :=
  -((2 * ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ))⁻¹ •
    (H (unitAtS j 1) + (lineSign j.2.1 j.2.2 * Complex.I) • H (unitAtS j Complex.I)))

theorem ccrM_comm [Fintype W] (H : (∀ w : W, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) → Module.End ℂ V)
    (hc : ∀ c c', H c * H c' - H c' * H c =
      ((4 * Real.pi : ℂ) * Complex.I * ((∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im : ℂ)) • 1)
    (j k : Σ w : W, Ix (P w) (Q w) × Ix (R w) (S w)) : ccrM H j * ccrM H k = ccrM H k * ccrM H j := by
  have h11 := hc (unitAtS j 1) (unitAtS k 1)
  have h1i := hc (unitAtS j 1) (unitAtS k Complex.I)
  have hi1 := hc (unitAtS j Complex.I) (unitAtS k 1)
  have hii := hc (unitAtS j Complex.I) (unitAtS k Complex.I)
  rw [sum_unitAtS] at h11 h1i hi1 hii
  by_cases hjk : j = k
  · rw [hjk]
  · simp only [if_neg hjk, Complex.zero_im, Complex.ofReal_zero, mul_zero, zero_smul, sub_eq_zero] at h11 h1i hi1 hii
    unfold ccrM
    have c : Commute (H (unitAtS j 1) - (lineSign j.2.1 j.2.2 * Complex.I) • H (unitAtS j Complex.I))
        (H (unitAtS k 1) - (lineSign k.2.1 k.2.2 * Complex.I) • H (unitAtS k Complex.I)) :=
      Commute.sub_left (Commute.sub_right h11 (Commute.smul_right h1i _))
        (Commute.smul_left (Commute.sub_right hi1 (Commute.smul_right hii _)) _)
    exact ((c.smul_left _).smul_right _).eq

theorem ccrD_ccrM_comm [Fintype W] (H : (∀ w : W, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) → Module.End ℂ V)
    (hc : ∀ c c', H c * H c' - H c' * H c =
      ((4 * Real.pi : ℂ) * Complex.I * ((∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im : ℂ)) • 1)
    (j k : Σ w : W, Ix (P w) (Q w) × Ix (R w) (S w)) :
    ccrD H j * ccrM H k - ccrM H k * ccrD H j = if j = k then 1 else 0 := by
  unfold ccrD ccrM
  rw [comm_expand, hc, hc, hc, hc, sum_unitAtS, sum_unitAtS, sum_unitAtS, sum_unitAtS,
    inv_sq]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  by_cases h : j = k
  · subst h
    simp only [if_true, smul_smul, ← sub_smul, ← add_smul, ← neg_smul]
    conv_rhs => rw [← one_smul ℂ (1 : Module.End ℂ V)]
    congr 1
    rcases lineSign_cases j.2.1 j.2.2 with h | h
    · rw [h]; simp; field_simp; linear_combination (-8 : ℂ) * Complex.I_sq
    · rw [h]; simp; field_simp; linear_combination (-8 : ℂ) * Complex.I_sq
  · simp [h]

theorem unitAtS_re_im (j : Σ w : W, Ix (P w) (Q w) × Ix (R w) (S w)) (z : ℂ) :
    unitAtS j z = ((z.re : ℝ) : ℂ) • unitAtS j 1 + ((z.im : ℝ) : ℂ) • unitAtS j Complex.I := by
  funext w
  by_cases hw : w = j.1
  · subst hw
    simp only [unitAtS, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, Matrix.smul_single, ← Matrix.single_add, smul_eq_mul,
      mul_one, Complex.re_add_im]
  · simp [unitAtS, Pi.single_eq_of_ne hw]

theorem heis_expanccrD [Fintype W] (H : (∀ w : W, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) → Module.End ℂ V)
    (hadd : ∀ c c', H (c + c') = H c + H c') (hsmul : ∀ (r : ℝ) c, H ((r : ℂ) • c) = (r : ℂ) • H c)
    (c : ∀ w : W, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) :
    H c = ∑ j : (Σ w : W, Ix (P w) (Q w) × Ix (R w) (S w)),
      ((((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * GlobalTheory.CCRFock.coefM (c j.1 j.2.1 j.2.2) (lineSign j.2.1 j.2.2)) • ccrM H j +
        (((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * GlobalTheory.CCRFock.coefD (c j.1 j.2.1 j.2.2) (lineSign j.2.1 j.2.2)) • ccrD H j) := by
  have h0 : H 0 = 0 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact left_eq_add.mp this
  let H' : (∀ w : W, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) →+ Module.End ℂ V := ⟨⟨H, h0⟩, hadd⟩
  have hsum : H c = ∑ j : (Σ w : W, Ix (P w) (Q w) × Ix (R w) (S w)), H (unitAtS j (c j.1 j.2.1 j.2.2)) := by
    conv_lhs => rw [sum_unitAtS_eq c]
    exact map_sum H' _ _
  rw [hsum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [unitAtS_re_im, hadd, hsmul, hsmul]
  have hs : ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) ≠ 0 := by
    have : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
    exact_mod_cast this.ne'
  have he := lineSign_mul_self j.2.1 j.2.2
  unfold ccrM ccrD GlobalTheory.CCRFock.coefM GlobalTheory.CCRFock.coefD
  generalize ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) = s at hs ⊢
  generalize lineSign j.2.1 j.2.2 = e at he ⊢
  generalize H (unitAtS j 1) = A
  generalize H (unitAtS j Complex.I) = B
  generalize ((c j.1 j.2.1 j.2.2).re : ℂ) = x
  generalize ((c j.1 j.2.1 j.2.2).im : ℂ) = y
  have hI := Complex.I_mul_I
  match_scalars
  · field_simp
    ring
  · field_simp
    linear_combination (2 * y * e * e) * hI - 2 * y * he

end GlobalTheory.HoweD.CCRSig

namespace GlobalTheory.HoweD

open GlobalTheory.HoweD.CCRSig in

theorem ccr_fock_ops_sig : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] {W : Type} [Fintype W] [DecidableEq W] {P Q R S : W → ℕ} (H : (∀ w : W, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) → Module.End ℂ V), (∀ c c', H (c + c') = H c + H c') → (∀ (r : ℝ) c, H ((r : ℂ) • c) = (r : ℂ) • H c) → (∀ c c', H c * H c' - H c' * H c = ((4 * Real.pi : ℂ) * Complex.I * ((∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im : ℂ)) • 1) → ∃ m D : (Σ w : W, Ix (P w) (Q w) × Ix (R w) (S w)) → Module.End ℂ V, (∀ i j, m i * m j = m j * m i) ∧ (∀ i j, D i * m j - m j * D i = if i = j then 1 else 0) ∧ (∀ (j : Σ w : W, Ix (P w) (Q w) × Ix (R w) (S w)) (f₀ : V), H (Pi.single j.1 (Matrix.single j.2.1 j.2.2 1)) f₀ + (lineSign j.2.1 j.2.2 * Complex.I) • H (Pi.single j.1 (Matrix.single j.2.1 j.2.2 Complex.I)) f₀ = 0 → D j f₀ = 0) ∧ ∀ c, H c = ∑ j : (Σ w : W, Ix (P w) (Q w) × Ix (R w) (S w)), ((((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * GlobalTheory.CCRFock.coefM (c j.1 j.2.1 j.2.2) (lineSign j.2.1 j.2.2)) • m j + (((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * GlobalTheory.CCRFock.coefD (c j.1 j.2.1 j.2.2) (lineSign j.2.1 j.2.2)) • D j) := by
  intro V _ _ W _ _ P Q R S H hadd hsmul hc
  refine ⟨ccrM H, ccrD H, ccrM_comm H hc, ccrD_ccrM_comm H hc, fun j f₀ h => ?_, heis_expanccrD H hadd hsmul⟩
  have h' : H (unitAtS j 1) f₀ + (lineSign j.2.1 j.2.2 * Complex.I) • H (unitAtS j Complex.I) f₀ = 0 := h
  simp only [GlobalTheory.HoweD.CCRSig.ccrD, LinearMap.neg_apply, LinearMap.smul_apply, LinearMap.add_apply, h', smul_zero, neg_zero]

end GlobalTheory.HoweD
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalNormAtSplitPlace
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct ComplexOrder
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocalNormSplit

theorem exists_sq_of_split (E : Type) [Field E] [NumberField E] [IsCMField E]
    (θ : E) (hθ0 : θ ≠ 0) (hθ : IsCMField.complexConj E θ = -θ)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)))
    (hv : ∃ w w' : HeightOneSpectrum (𝓞 E), w ≠ w' ∧ w.under (𝓞 (maximalRealSubfield E)) = v ∧
      w'.under (𝓞 (maximalRealSubfield E)) = v)
    (d : maximalRealSubfield E) (hd : (d : E) = θ * θ) :
    ∃ s : v.adicCompletion (maximalRealSubfield E),
      s * s = algebraMap (maximalRealSubfield E) (v.adicCompletion (maximalRealSubfield E)) d := by
  classical
  by_contra hns
  push_neg at hns
  obtain ⟨w, w', hne, hw, hw'⟩ := hv
  obtain ⟨ψ, -, hb, -⟩ := GlobalTheory.TraceClasses.exists_finite_decomp (maximalRealSubfield E) E
  have hθF : ∀ a : maximalRealSubfield E, (a : E) ≠ θ := by
    intro a ha
    have h1 : IsCMField.complexConj E (a : E) = a := (IsCMField.complexConj_eq_self_iff E _).2 a.2
    rw [ha, hθ] at h1
    exact hθ0 (by linear_combination -h1 / 2)
  have hli : LinearIndependent (maximalRealSubfield E) ![(1 : E), θ] := by
    rw [LinearIndependent.pair_iff]
    intro p q hpq
    by_cases hq : q = 0
    · subst hq
      simpa using hpq
    · exfalso
      refine hθF (-p / q) ?_
      rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hpq
      have hq' : (q : E) ≠ 0 := by simpa using hq
      change ((-p / q : maximalRealSubfield E) : E) = θ
      push_cast
      field_simp
      rw [show algebraMap _ E p = p from rfl, show algebraMap _ E q = q from rfl] at hpq
      linear_combination -hpq
  let b := basisOfLinearIndependentOfCardEqFinrank hli
    (by rw [Fintype.card_fin, Algebra.IsQuadraticExtension.finrank_eq_two])
  set K := v.adicCompletion (maximalRealSubfield E)
  let bA := Algebra.TensorProduct.basis K b
  let t : K ⊗[maximalRealSubfield E] E := 1 ⊗ₜ θ
  have hb0 : bA 0 = 1 := by
    simp [bA, b, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.one_def]
  have hb1 : bA 1 = t := by
    simp [bA, b, Algebra.TensorProduct.basis_apply, t]
  have li : ∀ p q : K, algebraMap K _ p + algebraMap K _ q * t = 0 → p = 0 ∧ q = 0 := by
    intro p q h
    have := Fintype.linearIndependent_iff.1 bA.linearIndependent ![p, q] (by
      rw [Fin.sum_univ_two, hb0, hb1]
      simpa [Algebra.smul_def] using h)
    exact ⟨by simpa using this 0, by simpa using this 1⟩
  have sp : ∀ y, y = algebraMap K _ (bA.repr y 0) + algebraMap K _ (bA.repr y 1) * t := by
    intro y
    conv_lhs => rw [← bA.sum_repr y]
    rw [Fin.sum_univ_two, hb0, hb1, Algebra.smul_def, Algebra.smul_def, mul_one]
  have htt : t * t = algebraMap K _ (algebraMap (maximalRealSubfield E) K d) := by
    rw [← IsScalarTower.algebraMap_apply]
    change (1 : K) ⊗ₜ θ * (1 : K) ⊗ₜ θ = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← hd]
    exact (Algebra.TensorProduct.includeRight.commutes d)
  let W := {u : HeightOneSpectrum (𝓞 E) // u.under (𝓞 (maximalRealSubfield E)) = v}
  let w₀ : W := ⟨w, hw⟩
  let w₁ : W := ⟨w', hw'⟩
  have h01 : w₀ ≠ w₁ := fun h => hne (congrArg Subtype.val h)
  let e₀ : ∀ u : W, u.1.adicCompletion E := Pi.single (M := fun u : W => u.1.adicCompletion E) w₀ 1
  let e₁ : ∀ u : W, u.1.adicCompletion E := Pi.single (M := fun u : W => u.1.adicCompletion E) w₁ 1
  obtain ⟨u₀, hu₀⟩ := (hb v).2 e₀
  obtain ⟨u₁, hu₁⟩ := (hb v).2 e₁
  have hprod : u₀ * u₁ = 0 := by
    apply (hb v).1
    funext u
    simp only [map_mul, map_zero]
    rw [show ψ v u u₀ = e₀ u from congrFun hu₀ u, show ψ v u u₁ = e₁ u from congrFun hu₁ u]
    by_cases h : u = w₀
    · subst h
      simp [e₁, Pi.single_apply, h01]
    · simp [e₀, Pi.single_apply, h]
  have hn₀ : u₀ ≠ 0 := by
    rintro rfl
    have := congrFun hu₀ w₀
    simp [e₀] at this
  have hn₁ : u₁ ≠ 0 := by
    rintro rfl
    have := congrFun hu₁ w₁
    simp [e₁] at this
  obtain ⟨a, b', hu0⟩ : ∃ a b' : K, u₀ = algebraMap K _ a + algebraMap K _ b' * t := ⟨_, _, sp u₀⟩
  obtain ⟨c, e, hu1⟩ : ∃ c e : K, u₁ = algebraMap K _ c + algebraMap K _ e * t := ⟨_, _, sp u₁⟩
  set d' := algebraMap (maximalRealSubfield E) K d
  have ha : ¬ (a = 0 ∧ b' = 0) := by
    rintro ⟨h1, h2⟩
    apply hn₀
    rw [hu0, h1, h2]
    simp
  have hc : ¬ (c = 0 ∧ e = 0) := by
    rintro ⟨h1, h2⟩
    apply hn₁
    rw [hu1, h1, h2]
    simp
  have heq := li (a * c + d' * b' * e) (a * e + b' * c) (by
    rw [← hprod, hu0, hu1]
    simp only [map_add, map_mul]
    linear_combination (-(algebraMap K _ b' * algebraMap K _ e)) * htt)
  have hz : c * c - d' * e * e = 0 := by
    by_contra hz
    apply ha
    constructor
    · refine (mul_eq_zero.1 (?_ : a * (c * c - d' * e * e) = 0)).resolve_right hz
      linear_combination c * heq.1 - d' * e * heq.2
    · refine (mul_eq_zero.1 (?_ : b' * (c * c - d' * e * e) = 0)).resolve_right hz
      linear_combination -(e * heq.1) + c * heq.2
  by_cases he : e = 0
  · apply hc
    refine ⟨?_, he⟩
    rw [he] at hz
    simpa using hz
  · apply hns (c / e)
    field_simp
    linear_combination hz

theorem exists_norm_of_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Q : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.SelfRecip E r) (x : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q), GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.invol Q x = x → ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), (∃ w w' : Pl E, w ≠ w' ∧ w.under (𝓞 (maximalRealSubfield E)) = v ∧ w'.under (𝓞 (maximalRealSubfield E)) = v) → ∃ z : v.adicCompletion (maximalRealSubfield E) ⊗[maximalRealSubfield E] GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q, z * GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.involBase Q _ z = 1 ⊗ₜ x := by
  intro E _ _ _ r Q x hx v hv
  obtain ⟨θ, hθ0, hθ⟩ := GlobalTheory.Published.exists_cc_eq_neg E
  have hθ' : IsCMField.complexConj E θ = -θ := hθ
  have hdmem : θ * θ ∈ maximalRealSubfield E :=
    (IsCMField.complexConj_eq_self_iff E _).1 (by rw [map_mul, hθ']; ring)
  let K := v.adicCompletion (maximalRealSubfield E)
  obtain ⟨d, hd⟩ : ∃ d : maximalRealSubfield E, (d : E) = θ * θ := ⟨⟨_, hdmem⟩, rfl⟩
  obtain ⟨s, hs⟩ := exists_sq_of_split E θ hθ0 hθ' v hv d hd
  let B := K ⊗[maximalRealSubfield E] GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0, mul_zero, eq_comm] at hs
    have h1 := (_root_.map_eq_zero (algebraMap (maximalRealSubfield E) K)).1 hs
    rw [h1] at hd
    exact hθ0 (mul_self_eq_zero.1 (by simpa using hd.symm))
  let uT : B := 1 ⊗ₜ algebraMap E _ θ
  have hTT : uT * uT = algebraMap K B (s * s) := by
    rw [hs, ← IsScalarTower.algebraMap_apply]
    change (1 : K) ⊗ₜ algebraMap E _ θ * (1 : K) ⊗ₜ algebraMap E _ θ = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← map_mul, ← hd,
      show (d : E) = algebraMap (maximalRealSubfield E) E d from rfl,
      ← IsScalarTower.algebraMap_apply]
    exact (Algebra.TensorProduct.includeRight.commutes _)
  let uc : B := algebraMap K B s⁻¹ * uT
  have hc : uc * uc = 1 := by
    have : uc * uc = algebraMap K B (s⁻¹ * s⁻¹ * (s * s)) := by
      rw [map_mul, map_mul, ← hTT]; ring
    rw [this, show s⁻¹ * s⁻¹ * (s * s) = 1 by rw [← mul_inv, inv_mul_cancel₀ (mul_ne_zero hs0 hs0)], map_one]
  have hiT : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.involBase Q K uT = -uT := by
    change Algebra.TensorProduct.map _ _ ((1 : K) ⊗ₜ algebraMap E _ θ) = _
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.invol_algebraMap, hθ',
      map_neg, TensorProduct.tmul_neg]
  have hic : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.involBase Q K uc = -uc := by
    change GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.involBase Q K (algebraMap K B s⁻¹ * uT) = -(algebraMap K B s⁻¹ * uT)
    rw [map_mul, AlgHom.commutes, hiT, mul_neg]
  have hiX : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.involBase Q K (1 ⊗ₜ x) = 1 ⊗ₜ x := by
    change Algebra.TensorProduct.map _ _ ((1 : K) ⊗ₜ x) = _
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hx]
  have h2K : (2 : K) ≠ 0 := by
    rw [← map_ofNat (algebraMap (maximalRealSubfield E) K) 2]
    exact (_root_.map_ne_zero _).2 two_ne_zero
  let hf : B := algebraMap K B 2⁻¹
  have hh : hf * 2 = 1 := by
    rw [← map_ofNat (algebraMap K B) 2, ← map_mul, inv_mul_cancel₀ h2K, map_one]
  have hih : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.involBase Q K hf = hf := AlgHom.commutes _ _
  refine ⟨hf * (1 + uc) * (1 ⊗ₜ x) + hf * (1 - uc), ?_⟩
  rw [map_add, map_mul, map_mul, map_mul, map_add, map_sub, map_one, hic, hiX, hih]
  linear_combination (hf ^ 2 * (2 * (1 ⊗ₜ x : B) - (1 ⊗ₜ x : B) ^ 2 - 1)) * hc + ((2 * hf + 1) * (1 ⊗ₜ x : B)) * hh

end GlobalTheory.LocalNormSplit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTwistContinuousInvolutionIntegralProperties
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

namespace GlobalTheory.BCT.ThBasic

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem cj_mem_integers (hU : Unr E) (w : Pl E) (x : w.adicCompletion E) (hx : x ∈ Ov E w) : cj w x ∈ Ov E w := by
  have h := (GlobalTheory.T.placeConjugation_properties_cmField E hU w).2.2.1 x
  change Valued.v (cj w x) ≤ 1
  rw [h]; exact hx

theorem thL_thL (hU : Unr E) (n : ℕ) (w : Pl E) (g : GLw n w) : thL n w (thL n w g) = g := by
  unfold thL
  split_ifs
  · rfl
  · exact GlobalTheory.ThetaPull.thetaGL_thetaGL _ (GlobalTheory.T.placeConjugation_properties_cmField E hU w).2.1 g

theorem continuous_thL (hU : Unr E) (n : ℕ) (w : Pl E) : Continuous (thL n w) := by
  unfold thL
  split_ifs
  · exact continuous_id
  · exact GlobalTheory.ThetaPull.continuous_thetaGL _ (GlobalTheory.T.placeConjugation_properties_cmField E hU w).1

theorem thL_mem_KGL (hU : Unr E) (n : ℕ) (w : Pl E) (k : GLw n w) (hk : k ∈ GlobalTheory.LFun.KGL w n) :
    thL n w k ∈ GlobalTheory.LFun.KGL w n := by
  unfold thL
  split_ifs
  · exact hk
  · obtain ⟨k', rfl⟩ := hk
    let c' : Ov E w →+* Ov E w := (cj w).restrict (Ov E w) (Ov E w) (cj_mem_integers hU w)
    refine ⟨thetaGL n c' k', ?_⟩
    exact GlobalTheory.ThetaPull.map_thetaGL (Ov E w).subtype c' (cj w) (fun x => rfl) k'

theorem nrmL_twist (hU : Unr E) (n : ℕ) (w : Pl E) (g y : GLw n w) :
    nrmL n w (g⁻¹ * y * thL n w g) = g⁻¹ * nrmL n w y * g := by
  unfold nrmL
  have h2 := thL_thL hU n w g
  unfold thL at h2 ⊢
  split_ifs with hs
  · simp [hs] at *
  · simp only [hs, if_false] at h2 ⊢
    rw [map_mul, map_mul, map_inv, h2]
    group

theorem isClosed_UL (hU : Unr E) (n : ℕ) (w : Pl E) : IsClosed (UL n w : Set (GLw n w)) := by
  unfold UL
  split_ifs
  · exact isClosed_univ
  · have hc := (GlobalTheory.T.placeConjugation_properties_cmField E hU w).1
    have : Continuous fun g : GLw n w => cT (cj w) (g : Matrix (Fin n) (Fin n) _) * 1 * (g : Matrix (Fin n) (Fin n) _) := by
      refine Continuous.mul (Continuous.mul ?_ continuous_const) Units.continuous_val
      exact continuous_matrix fun i j => hc.comp (Units.continuous_val.matrix_elem _ _)
    exact isClosed_singleton.preimage this

theorem charpoly_nrmL (hU : Unr E) (n : ℕ) (w : Pl E) (δ : GL (Fin n) E) :
    (nrmL n w (locEl n w δ)).val.charpoly = atPl w (δ * thE E n δ).val.charpoly := by
  unfold nrmL locEl
  split_ifs with hs
  · exact (Matrix.charpoly_map _ _)
  · have hm : thetaGL n (cj w) (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) δ) =
        GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) (thE E n δ) :=
      (GlobalTheory.ThetaPull.map_thetaGL _ _ _ (fun x => ((GlobalTheory.T.placeConjugation_properties_cmField E hU w).2.2.2.1 hs).1 x |>.symm) δ).symm
    rw [hm, ← map_mul]
    exact (Matrix.charpoly_map _ _)

theorem cLoc_mem_UL (hU : Unr E) (n : ℕ) (w : Pl E) (x : UA E n) : cLoc w x ∈ UL n w := by
  unfold UL
  split_ifs with hs
  · exact Subgroup.mem_top _
  · have hp := ((GlobalTheory.T.placeConjugation_properties_cmField E hU w).2.2.2.1 hs).2.2.1
    have hx := x.2
    change cT (conjAd E) (x.1 : Matrix (Fin n) (Fin n) (Ad E)) * 1 * (x.1 : Matrix (Fin n) (Fin n) (Ad E)) = 1 at hx
    change cT (cj w) ((cLoc w x : GLw n w) : Matrix (Fin n) (Fin n) _) * 1 * ((cLoc w x : GLw n w) : Matrix (Fin n) (Fin n) _) = 1
    have := congrArg (((pLoc E w).comp (pFin E)).mapMatrix) hx
    rw [map_one, map_mul, map_mul, map_one] at this
    convert this using 3
    · refine Matrix.ext fun i j => ?_
      show cj w (pLoc E w (pFin E ((x.1 : Matrix (Fin n) (Fin n) (Ad E)) j i))) =
        pLoc E w (pFin E (conjAd E ((x.1 : Matrix (Fin n) (Fin n) (Ad E)) j i)))
      rw [← hp]
      rfl
    · rfl

theorem twist_basic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E), Continuous (thL n w) ∧ (∀ g, thL n w (thL n w g) = g) ∧ (∀ k ∈ GlobalTheory.LFun.KGL w n, thL n w k ∈ GlobalTheory.LFun.KGL w n) ∧ (∀ g y, nrmL n w (g⁻¹ * y * thL n w g) = g⁻¹ * nrmL n w y * g) ∧ IsOpen (GlobalTheory.LFun.KGL w n : Set (GLw n w)) ∧ IsCompact (GlobalTheory.LFun.KGL w n : Set (GLw n w)) ∧ IsOpen (KL n w : Set (UL n w)) ∧ IsCompact (KL n w : Set (UL n w)) ∧ (∀ δ : GL (Fin n) E, (nrmL n w (locEl n w δ)).val.charpoly = atPl w (δ * thE E n δ).val.charpoly) ∧ ∀ x ∈ locU n w, cLoc w x ∈ UL n w := by
  intro E _ _ _ hU n w
  have hK := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n
  refine ⟨continuous_thL hU n w, thL_thL hU n w, thL_mem_KGL hU n w, nrmL_twist hU n w, hK.1, hK.2, ?_, ?_,
    charpoly_nrmL hU n w, fun x _ => cLoc_mem_UL hU n w x⟩
  · rw [KL, Subgroup.coe_subgroupOf]
    exact hK.1.preimage continuous_subtype_val
  · rw [KL, Subgroup.coe_subgroupOf]
    exact (isClosed_UL hU n w).isClosedEmbedding_subtypeVal.isCompact_preimage hK.2

end GlobalTheory.BCT.ThBasic
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactOneParameterLinesOfLieLinesStatement
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maximalCompact_oneParameterLines_of_lieLines : GlobalTheory.RealLift.LineEx → GlobalTheory.RealLift.KLine := by
  first | exact @GlobalTheory.RealLift.kLine_of_lineEx | exact GlobalTheory.RealLift.kLine_of_lineEx | (intros; apply GlobalTheory.RealLift.kLine_of_lineEx <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSmallSectionBallOfMulPowSectionStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_smallSectionBall_of_mul_pow_section : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ s : X.functionField, s ∈ P.H 0 1 → s ≠ 0 → ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧ ∀ (N m : ℕ) (f : X.functionField), f ∈ P.H N 0 → f * s ^ m ∈ P.Bl N m 2 → f ∈ P.Bl N 0 (2 * Real.exp (δ * N + C * m)) := by
  first | exact @GlobalTheory.VolBr.MpDiv.mem_Bl_of_mul_pow | exact GlobalTheory.VolBr.MpDiv.mem_Bl_of_mul_pow | (intros; apply GlobalTheory.VolBr.MpDiv.mem_Bl_of_mul_pow <;> assumption)
end

