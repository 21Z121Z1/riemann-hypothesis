import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1042
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0032
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1141
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1118
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1094
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1137
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0876
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankWeightComponentEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1115
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1136
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAnti
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertPlaceHeckeDoubleCosetsInverseRepsLabel

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjDiagReNonneg
section
noncomputable section

open Matrix GlobalTheory.PsCo.Pc1
open scoped ComplexConjugate

namespace GlobalTheory.PsCo.Pc3

variable {n : ℕ}

def prP (ε : Fin n → Bool) : Mat n := diagonal fun i => if ε i then 1 else 0

def sgM (ε : Fin n → Bool) : Mat n := diagonal fun i => if ε i then 1 else -1

def bExt (ε : Fin n → Bool) (B : Mode ε → ℂ) (p : Fin n × Fin n) : ℂ :=
  if h : ε p.1 = true ∧ ε p.2 = false then B ⟨p, h⟩ else 0

theorem sum_mode (ε : Fin n → Bool) (g : Fin n × Fin n → ℂ) :
    ∑ x : Mode ε, g x.1 = ∑ i, ∑ j, if ε i = true ∧ ε j = false then g (i, j) else 0 := by
  rw [← Finset.sum_subtype (Finset.univ.filter fun p : Fin n × Fin n => ε p.1 = true ∧ ε p.2 = false)
    (by simp) g, Finset.sum_filter, ← Finset.univ_product_univ, Finset.sum_product]

theorem sum_mode_re (ε : Fin n → Bool) (g : Fin n × Fin n → ℝ) :
    ∑ x : Mode ε, g x.1 = ∑ i, ∑ j, if ε i = true ∧ ε j = false then g (i, j) else 0 := by
  rw [← Finset.sum_subtype (Finset.univ.filter fun p : Fin n × Fin n => ε p.1 = true ∧ ε p.2 = false)
    (by simp) g, Finset.sum_filter, ← Finset.univ_product_univ, Finset.sum_product]

theorem prP_mul_pB_apply (ε : Fin n → Bool) (B : Mode ε → ℂ) (i j : Fin n) :
    (prP ε * pB ε B) i j = if ε i = true ∧ ε j = false then bExt ε B (i, j) else 0 := by
  simp only [prP, diagonal_mul, pB, bExt]
  by_cases hi : ε i = true <;> by_cases hj : ε j = true <;> simp [hi, hj]

theorem trace_projection_mul_modeMatrix_mul (ε : Fin n → Bool) (B : Mode ε → ℂ) (M : Mat n) :
    trace (prP ε * pB ε B * M) = ∑ x : Mode ε, B x * M x.1.2 x.1.1 := by
  have : ∀ x : Mode ε, B x * M x.1.2 x.1.1 = (fun p : Fin n × Fin n => bExt ε B p * M p.2 p.1) x.1 := by
    intro x; simp [bExt, x.2]
  rw [Finset.sum_congr rfl fun x _ => this x, sum_mode ε (fun p : Fin n × Fin n => bExt ε B p * M p.2 p.1)]
  simp only [trace, diag]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_apply (M := prP ε * pB ε B)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [prP_mul_pB_apply]
  split_ifs <;> simp

theorem pB_apply_swap (ε : Fin n → Bool) (B : Mode ε → ℂ) (i j : Fin n) :
    pB ε B j i = star (pB ε B i j) := by
  simp only [pB]
  by_cases hi : ε i = true <;> by_cases hj : ε j = true <;> simp [hi, hj]

theorem pB_isHermitian (ε : Fin n → Bool) (B : Mode ε → ℂ) : (pB ε B).IsHermitian := by
  ext i j
  simp only [conjTranspose_apply]
  rw [pB_apply_swap ε B j i]

theorem trace_projection_mul_modeMatrix_mul_self (ε : Fin n → Bool) (B : Mode ε → ℂ) :
    trace (prP ε * pB ε B * pB ε B) = ((∑ x, ‖B x‖ ^ 2 : ℝ) : ℂ) := by
  rw [trace_projection_mul_modeMatrix_mul]
  push_cast
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [pB_apply_swap]
  have : pB ε B x.1.1 x.1.2 = B x := by simp [pB, x.2.1, x.2.2]
  rw [this, show star (B x) = conj (B x) from rfl, Complex.mul_conj']

theorem sgM_mul_sgM (ε : Fin n → Bool) : sgM ε * sgM ε = 1 := by
  rw [sgM, diagonal_mul_diagonal, ← diagonal_one]
  congr 1; funext i; split_ifs <;> simp

theorem sgM_pB_sgM (ε : Fin n → Bool) (B : Mode ε → ℂ) : sgM ε * pB ε B * sgM ε = -pB ε B := by
  ext i j
  simp only [sgM, diagonal_mul, mul_diagonal, Matrix.neg_apply]
  simp only [pB]
  by_cases hi : ε i = true <;> by_cases hj : ε j = true <;> simp [hi, hj]

theorem sgM_prP (ε : Fin n → Bool) : sgM ε * prP ε = prP ε * sgM ε := by
  simp only [sgM, prP, diagonal_mul_diagonal, mul_comm]

theorem exp_neg_pB (ε : Fin n → Bool) (B : Mode ε → ℂ) :
    NormedSpace.exp (-pB ε B) = sgM ε * NormedSpace.exp (pB ε B) * sgM ε := by
  have hu : IsUnit (sgM ε) := ⟨⟨sgM ε, sgM ε, sgM_mul_sgM ε, sgM_mul_sgM ε⟩, rfl⟩
  have hinv : (sgM ε)⁻¹ = sgM ε := inv_eq_left_inv (sgM_mul_sgM ε)
  calc NormedSpace.exp (-pB ε B) = NormedSpace.exp (sgM ε * pB ε B * (sgM ε)⁻¹) := by rw [hinv, sgM_pB_sgM]
    _ = sgM ε * NormedSpace.exp (pB ε B) * (sgM ε)⁻¹ := Matrix.exp_conj _ _ hu
    _ = _ := by rw [hinv]

theorem trace_neg_side (ε : Fin n → Bool) (B : Mode ε → ℂ) :
    trace (prP ε * pB ε B * NormedSpace.exp (-pB ε B)) = -trace (prP ε * pB ε B * NormedSpace.exp (pB ε B)) := by
  have hS := sgM_mul_sgM ε
  have hP : prP ε * sgM ε = sgM ε * prP ε := (sgM_prP ε).symm
  have h1 : prP ε * pB ε B * (sgM ε * NormedSpace.exp (pB ε B) * sgM ε) =
      (sgM ε * (prP ε * (sgM ε * pB ε B * sgM ε) * NormedSpace.exp (pB ε B))) * sgM ε := by
    calc prP ε * pB ε B * (sgM ε * NormedSpace.exp (pB ε B) * sgM ε)
        = prP ε * (sgM ε * sgM ε) * pB ε B * (sgM ε * NormedSpace.exp (pB ε B) * sgM ε) := by rw [hS, mul_one]
      _ = (prP ε * sgM ε) * (sgM ε * pB ε B * sgM ε) * NormedSpace.exp (pB ε B) * sgM ε := by
        simp only [mul_assoc]
      _ = _ := by rw [hP]; simp only [mul_assoc]
  rw [exp_neg_pB, h1, trace_mul_comm, ← mul_assoc, hS, one_mul, sgM_pB_sgM]
  simp [trace_neg]

theorem trace_conj_diag (U : Mat n) (hU : star U * U = 1) (A : Mat n) (v : Fin n → ℂ) :
    trace (A * (U * diagonal v * star U)) = ∑ i, (star U * A * U) i i * v i := by
  have : A * (U * diagonal v * star U) = (A * U * diagonal v) * star U := by simp only [mul_assoc]
  rw [this, trace_mul_comm, ← mul_assoc, ← mul_assoc]
  simp only [trace, diag, mul_diagonal]

theorem conjDiag_re_nonneg (U : Matrix (Fin n) (Fin n) ℂ) (ε : Fin n → Bool) (i : Fin n) :
    ∃ c : ℝ, 0 ≤ c ∧ (star U * prP ε * U) i i = c := by
  refine ⟨∑ k, (if ε k then 1 else 0) * ‖U k i‖ ^ 2, Finset.sum_nonneg fun k _ => by positivity, ?_⟩
  rw [Matrix.mul_apply, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [prP, Matrix.mul_diagonal, Matrix.star_apply, show star (U k i) = conj (U k i) from rfl]
  split_ifs
  · rw [mul_one, mul_comm, Complex.mul_conj']; push_cast; ring
  · simp

theorem re_term (c l : ℝ) (hc : 0 ≤ c) :
    2 * (((c : ℂ) * ((l : ℂ) * (l : ℂ))).re) ≤
      ((c : ℂ) * ((l : ℂ) * Complex.exp l)).re - ((c : ℂ) * ((l : ℂ) * Complex.exp (-l))).re := by
  have h1 : ((c : ℂ) * ((l : ℂ) * (l : ℂ))).re = c * (l * l) := by norm_cast
  have h2 : ((c : ℂ) * ((l : ℂ) * Complex.exp l)).re = c * (l * Real.exp l) := by
    rw [← Complex.ofReal_exp]; norm_cast
  have h3 : ((c : ℂ) * ((l : ℂ) * Complex.exp (-l))).re = c * (l * Real.exp (-l)) := by
    rw [← Complex.ofReal_neg, ← Complex.ofReal_exp]; norm_cast
  rw [h1, h2, h3]
  have hs : l * l ≤ l * Real.sinh l := by
    rcases le_total 0 l with h | h
    · exact mul_le_mul_of_nonneg_left (Real.self_le_sinh_iff.2 h) h
    · have : Real.sinh l ≤ l := by
        have := Real.self_le_sinh_iff.2 (neg_nonneg.2 h); rw [Real.sinh_neg] at this; linarith
      nlinarith
  rw [Real.sinh_eq] at hs
  nlinarith

theorem two_re_le (ε : Fin n → Bool) (B : Mode ε → ℂ) :
    2 * (trace (prP ε * pB ε B * pB ε B)).re ≤
      (trace (prP ε * pB ε B * NormedSpace.exp (pB ε B)) - trace (prP ε * pB ε B * NormedSpace.exp (-pB ε B))).re := by
  have hX := pB_isHermitian ε B
  set U : Matrix (Fin n) (Fin n) ℂ := (hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hUdef
  have hU : star U * U = 1 := Unitary.coe_star_mul_self hX.eigenvectorUnitary
  have hU' : U * star U = 1 := Unitary.coe_mul_star_self hX.eigenvectorUnitary
  set l : Fin n → ℝ := hX.eigenvalues
  set d : Fin n → ℂ := fun i => (l i : ℂ) with hd
  have hdec : pB ε B = U * diagonal d * star U := by
    have := hX.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  have hunit : IsUnit U := ⟨⟨U, star U, hU', hU⟩, rfl⟩
  have hinv : U⁻¹ = star U := inv_eq_left_inv hU
  have hexp : ∀ w : Fin n → ℂ, NormedSpace.exp (U * diagonal w * star U) =
      U * diagonal (fun i => Complex.exp (w i)) * star U := by
    intro w
    rw [← hinv, Matrix.exp_conj _ _ hunit, Matrix.exp_diagonal, Pi.exp_def, ← Complex.exp_eq_exp_ℂ]
  have hdn : diagonal (fun i => -d i) = -diagonal d := by
    ext i j; by_cases h : i = j <;> simp [diagonal_apply, h]
  have hneg : -pB ε B = U * diagonal (fun i => -d i) * star U := by
    rw [hdec, hdn, Matrix.mul_neg, Matrix.neg_mul]
  have hmul : ∀ v w : Fin n → ℂ, (U * diagonal v * star U) * (U * diagonal w * star U) =
      U * diagonal (fun i => v i * w i) * star U := by
    intro v w
    calc (U * diagonal v * star U) * (U * diagonal w * star U) = U * diagonal v * (star U * U) * diagonal w * star U := by
          simp only [mul_assoc]
      _ = _ := by rw [hU, mul_one, mul_assoc U, diagonal_mul_diagonal]
  have hE : NormedSpace.exp (pB ε B) = U * diagonal (fun i => Complex.exp (d i)) * star U := by rw [hdec]; exact hexp d
  have hE' : NormedSpace.exp (-pB ε B) = U * diagonal (fun i => Complex.exp (-d i)) * star U := by
    rw [hneg]; exact hexp _
  have t0 : trace (prP ε * pB ε B * pB ε B) = ∑ i, (star U * prP ε * U) i i * (d i * d i) := by
    rw [mul_assoc, hdec, hmul, trace_conj_diag _ hU]
  have t1 : trace (prP ε * pB ε B * NormedSpace.exp (pB ε B)) =
      ∑ i, (star U * prP ε * U) i i * (d i * Complex.exp (d i)) := by
    rw [mul_assoc, hE, hdec, hmul, trace_conj_diag _ hU]
  have t2 : trace (prP ε * pB ε B * NormedSpace.exp (-pB ε B)) =
      ∑ i, (star U * prP ε * U) i i * (d i * Complex.exp (-d i)) := by
    rw [mul_assoc, hE', hdec, hmul, trace_conj_diag _ hU]
  rw [t0, t1, t2, Complex.re_sum, Finset.mul_sum, Complex.sub_re, Complex.re_sum, Complex.re_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  obtain ⟨c, hc, hci⟩ := conjDiag_re_nonneg U ε i
  rw [hci]
  exact re_term c (l i) hc

theorem le_of_le_sqrt_mul {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ≤ Real.sqrt a * Real.sqrt b) : a ≤ b := by
  rcases eq_or_lt_of_le ha with h0 | h0
  · rw [← h0]; exact hb
  · have hs : 0 < Real.sqrt a := Real.sqrt_pos.2 h0
    have h1 : Real.sqrt a * Real.sqrt a ≤ Real.sqrt a * Real.sqrt b := by rwa [Real.mul_self_sqrt ha]
    have h2 : Real.sqrt a ≤ Real.sqrt b := le_of_mul_le_mul_left h1 hs
    have := mul_le_mul h2 h2 (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)
    rwa [Real.mul_self_sqrt ha, Real.mul_self_sqrt hb] at this

theorem stExpLow : StExpLow := by
  intro n ε B
  set E : Matrix (Fin n) (Fin n) ℂ := NormedSpace.exp (pB ε B) with hEdef
  have hH : E.IsHermitian := (pB_isHermitian ε B).exp
  set T := trace (prP ε * pB ε B * E)
  have h2 := two_re_le ε B
  rw [trace_neg_side, trace_projection_mul_modeMatrix_mul_self, Complex.ofReal_re] at h2
  have hT : (∑ x, ‖B x‖ ^ 2) ≤ T.re := by
    have : (T - -T).re = 2 * T.re := by simp [Complex.sub_re, Complex.neg_re]; ring
    rw [this] at h2; linarith
  have hTn : ‖T‖ ≤ ∑ x : Mode ε, ‖B x‖ * ‖E x.1.1 x.1.2‖ := by
    rw [show T = ∑ x : Mode ε, B x * E x.1.2 x.1.1 from trace_projection_mul_modeMatrix_mul ε B E]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
    rw [norm_mul, ← hH.apply x.1.1 x.1.2, norm_star]
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun x : Mode ε => ‖B x‖) (fun x : Mode ε => ‖E x.1.1 x.1.2‖)
  have hr : rM ε E = ∑ x : Mode ε, ‖E x.1.1 x.1.2‖ ^ 2 := rfl
  rw [hr]
  exact le_of_le_sqrt_mul (Finset.sum_nonneg fun _ _ => by positivity) (Finset.sum_nonneg fun _ _ => by positivity)
    (hT.trans ((Complex.re_le_norm T).trans (hTn.trans hcs)))

end GlobalTheory.PsCo.Pc3
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjRelEquiv
section
noncomputable section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.KapLat

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def stdH (w : Pl E) {n : ℕ} (v v' : Fin n → w.adicCompletion E) : w.adicCompletion E :=
  ∑ k, v k * cj w (v' k)

def Bridge (w : Pl E) (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E) : Prop :=
  (∀ x, e (K.c x) = cj w (e x)) ∧ (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) ∧
    (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) ∧ qV E w = K.q ^ 2

def Fits (w : Pl E) {K : GlobalTheory.UnitLemma.UQ} (e : K.E ≃+* w.adicCompletion E) (B : GlobalTheory.UnitLemma.InvAlg K)
    (Q : (w.adicCompletion E)[X]) (u : B.A) : Prop :=
  Algebra.adjoin K.E {u} = ⊤ ∧ aeval u (Q.map e.symm.toRingHom) = 0 ∧ Module.finrank K.E B.A = Q.natDegree ∧
    u * B.σ u = 1

def IsModel (w : Pl E) {K : GlobalTheory.UnitLemma.UQ} (e : K.E ≃+* w.adicCompletion E) (B : GlobalTheory.UnitLemma.InvAlg K)
    (u x : B.A) {n : ℕ} (γ : GLw n w) : Prop :=
  ∃ ψ : B.A ≃+ (Fin n → w.adicCompletion E), (∀ (c : K.E) (y : B.A), ψ (c • y) = e c • ψ y) ∧
    (∀ y, ψ (u * y) = γ.val *ᵥ ψ y) ∧ ∀ y z, stdH w (ψ y) (ψ z) = e (B.herm x y z)

def congSet (w : Pl E) (n k : ℕ) : Set (GLw n w) :=
  {g | g ∈ GlobalTheory.LFun.KGL w n ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤
    WithZero.exp (-(k : ℤ))}

theorem clRel_equiv {K : GlobalTheory.UnitLemma.UQ} (B : GlobalTheory.UnitLemma.InvAlg K) :
    Equivalence (fun x y : {x : B.Aˣ // B.σ (x : B.A) = x} =>
      ∃ u : B.Aˣ, (y.1 : B.A) = x.1 * (u * B.σ (u : B.A))) where
  refl x := ⟨1, by simp⟩
  symm := by
    rintro x y ⟨u, hu⟩
    refine ⟨u⁻¹, ?_⟩
    have h1 : ((u : B.A) * ((u⁻¹ : B.Aˣ) : B.A)) * (B.σ (u : B.A) * B.σ ((u⁻¹ : B.Aˣ) : B.A)) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one, one_mul]
    rw [hu]
    calc (x.1 : B.A) = x.1 * (((u : B.A) * ((u⁻¹ : B.Aˣ) : B.A)) * (B.σ (u : B.A) * B.σ ((u⁻¹ : B.Aˣ) : B.A))) := by
          rw [h1, mul_one]
      _ = _ := by ring
  trans := by
    rintro x y z ⟨u, hu⟩ ⟨v, hv⟩
    exact ⟨u * v, by rw [hv, hu, Units.val_mul, map_mul]; ring⟩

theorem conjRel_equiv (G : Type) [Group G] :
    Equivalence (fun x y : G => ∃ g, y = g⁻¹ * x * (MonoidHom.id G) g) where
  refl x := ⟨1, by simp⟩
  symm := by
    rintro x y ⟨g, rfl⟩
    exact ⟨g⁻¹, by simp [mul_assoc]⟩
  trans := by
    rintro x y z ⟨g, rfl⟩ ⟨h, rfl⟩
    exact ⟨g * h, by simp [mul_assoc]⟩

theorem cast_finsum {α : Type*} (f : α → ℚ) : ((∑ᶠ a, f a : ℚ) : ℂ) = ∑ᶠ a, (f a : ℂ) := by
  by_cases h : (Function.support f).Finite
  · exact map_finsum (Rat.castHom ℂ) h
  · have h' : ¬ (Function.support fun a => (f a : ℂ)).Finite := by
      simpa [Function.support] using h
    rw [finsum_of_infinite_support h, finsum_of_infinite_support h']
    simp

end GlobalTheory.KapLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugatedTensorIntegrality
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

noncomputable section
namespace GlobalTheory.LocIntSpan

theorem isIntB_of_isIntB_conj : ∀ (C : Type) [Ring C] [Algebra ℚ C] [FiniteDimensional ℚ C] (L : Type) [Field L] [NumberField L]
    (ι : L →ₐ[ℚ] C), Function.Injective ι → ∀ (κ : Type) (b : Module.Basis κ ℚ C) (κ' : Type)
    (bL : Module.Basis κ' ℚ L), ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S,
      ∀ (X : (v.adicCompletion ℚ ⊗[ℚ] C)ˣ) (E : v.adicCompletion ℚ ⊗[ℚ] L),
        IsIntB v b (↑X * Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι E * ↑X⁻¹) →
        IsIntB v bL E := by
  intro C _ _ _ L _ _ ι hι κ b κ' bL
  obtain ⟨S₁, h₁⟩ := GlobalTheory.T.exists_finset_adicIntegralTensorBasis_one_mul C κ b
  obtain ⟨S₂, h₂⟩ := GlobalTheory.T.exists_finset_adicIntegralTensorBasis_one_mul L κ' bL
  obtain ⟨S₃, h₃⟩ := GlobalTheory.T.adicIntegralTensorBasis_of_trace_mem_eventually L κ' bL
  refine ⟨S₁ ∪ S₂ ∪ S₃, fun v hv X E hE => ?_⟩
  simp only [Finset.mem_union, not_or] at hv
  obtain ⟨⟨hv1, hv2⟩, hv3⟩ := hv
  have hint := GlobalTheory.T.isIntegral_of_adicIntegralTensorBasis_ring v C κ b (h₁ v hv1).1 (h₁ v hv1).2 _ hE
  have hE' := isIntegral_of_isIntegral_conj X _ hint
  let F : v.adicCompletion ℚ ⊗[ℚ] L →ₐ[v.adicCompletion ℚ] v.adicCompletion ℚ ⊗[ℚ] C :=
    Algebra.TensorProduct.map (AlgHom.id (v.adicCompletion ℚ) (v.adicCompletion ℚ)) ι
  have hF : ∀ x, F x = Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι x := fun x => rfl
  have hinj : Function.Injective (F.restrictScalars (v.adicCompletionIntegers ℚ)) := by
    intro x y hxy
    exact map_id_injective (v.adicCompletion ℚ) ι hι (by simpa [hF] using hxy)
  have hE'' : IsIntegral (v.adicCompletionIntegers ℚ) E :=
    (isIntegral_algHom_iff (F.restrictScalars (v.adicCompletionIntegers ℚ)) hinj).1 (by simpa [hF] using hE')
  refine h₃ v hv3 E fun i => mem_of_isIntegral v ?_
  have hb : IsIntegral (v.adicCompletionIntegers ℚ) ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] bL i) :=
    GlobalTheory.T.isIntegral_of_adicIntegralTensorBasis_ring v L κ' bL (h₂ v hv2).1 (h₂ v hv2).2 _ (isIntB_tmul_basis v bL i)
  exact GlobalTheory.DiscConductor.isIntegral_trace_of_isIntegral _ _ _ _ (hE''.mul hb)

end GlobalTheory.LocIntSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffAtHolomorphicComplexChartOfSmoothAtStatement
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contDiffAt_holomorphicComplexChart_of_smoothAt : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)}, IsHoloChart e → ∀ {f : CxPts X.str σ → ℝ} {y : CxPts X.str σ}, y ∈ e.source → CInfAt f y → ContDiffAt ℝ ∞ (fun v => f (e.symm v)) (e y) := by
  first | exact @GlobalTheory.GoodTop.contDiffAt_holoChart | exact GlobalTheory.GoodTop.contDiffAt_holoChart | (intros; apply GlobalTheory.GoodTop.contDiffAt_holoChart <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAdelicActionRealCoordinates
section
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical

noncomputable section

namespace GlobalTheory.RealWeilF.MCont

theorem continuous_fstA (F : Type) [Field F] [NumberField F] : Continuous (fstA F) := continuous_fst

theorem continuous_comp_infPartF {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {τ : E →+* ℂ} {θ : Ainf F ⊗[F] E →+* ℂ} (h : IsInfEmbF τ θ) : Continuous (θ.comp (infPartF F E)) := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI := isModuleTopology_AE F E
  let b := Module.finBasis F E
  let B := Algebra.TensorProduct.basis (AF F) b
  have hrep : Continuous B.equivFun := IsModuleTopology.continuous_of_linearMap B.equivFun.toLinearMap
  have hg : Continuous fun a : AF F => θ (fstA F a ⊗ₜ[F] (1 : E)) := h.2.comp (continuous_fstA F)
  have e : ∀ z, (θ.comp (infPartF F E)) z = ∑ i, θ (fstA F (B.equivFun z i) ⊗ₜ[F] (1 : E)) * τ (b i) := by
    intro z
    conv_lhs => rw [← B.sum_equivFun z]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one, RingHom.comp_apply]
    have : infPartF F E (B.equivFun z i ⊗ₜ[F] b i) = (fstA F (B.equivFun z i) ⊗ₜ[F] (1 : E)) * ((1 : Ainf F) ⊗ₜ[F] b i) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rfl
    rw [this, map_mul, h.1]
  have : (θ.comp (infPartF F E) : AF F ⊗[F] E → ℂ) = fun z => ∑ i, θ (fstA F (B.equivFun z i) ⊗ₜ[F] (1 : E)) * τ (b i) :=
    funext e
  rw [this]
  exact continuous_finset_sum _ fun i _ => (hg.comp ((continuous_apply i).comp hrep)).mul continuous_const

theorem continuous_mMF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E)
      (θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)),
      IsInfFamF (fun w : InfinitePlace F => (B.emb w).1) θ → Continuous (mMF σ JS JT θ) := by
  intro F E _ _ _ _ _ σ B _ nS nT JS JT θ hθ
  have hc : ∀ (w : InfinitePlace F) (m n : ℕ), Continuous fun x : Matrix (Fin m) (Fin n) (AEF F E) => compAtF θ w x :=
    fun w m n => continuous_id.matrix_map (continuous_comp_infPartF (hθ w))
  have h1 : Continuous fun p : GAF σ JS × GAF σ JT => mtF σ JT p.2 :=
    (Units.continuous_val.comp continuous_subtype_val).comp continuous_snd
  have h2 : Continuous fun p : GAF σ JS × GAF σ JT => mtF σ JS p.1⁻¹ := by
    have : (fun g : GAF σ JS => mtF σ JS g⁻¹) =
        fun g => (((Subtype.val (show HR (AF F) σ JS from g))⁻¹ : GL (Fin nS) (AF F ⊗[F] E)) : Matrix _ _ _) := rfl
    have hi : Continuous fun g : GAF σ JS => mtF σ JS g⁻¹ := by
      rw [this]; exact Units.continuous_coe_inv.comp continuous_subtype_val
    exact hi.comp continuous_fst
  have e : (mMF σ JS JT θ : GAF σ JS × GAF σ JT → _) = fun p =>
      GlobalTheory.RealWeil.blk (fun w => compAtF θ w (mtF σ JT p.2)) fun w => compAtF θ w (mtF σ JS p.1⁻¹) := funext fun p => rfl
  rw [e]
  exact GlobalTheory.RealWeil.continuous_blk (fun w => (hc w _ _).comp h1) fun w => (hc w _ _).comp h2

end GlobalTheory.RealWeilF.MCont

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPolarisedTopChernCoeffStatement
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuousAt_polarisedTopChernCoeff : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] {K : V n → Fin n → EndValuedForm11Coeffs n r} {v : V n}, (∀ i a b p q, ContinuousAt (fun x => K x i a b p q) v) → ContinuousAt (fun x => mixTop (K x)) v := by
  first | exact @GlobalTheory.GoodTop.continuousAt_mixTop | exact GlobalTheory.GoodTop.continuousAt_mixTop | (intros; apply GlobalTheory.GoodTop.continuousAt_mixTop <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtTransgressionTopCoeffComplex
section
set_option autoImplicit false

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
private lemma continuousAt_dbar_ofReal_of_contDiffAt_one {n : ℕ} {ρ : _root_.ReciprocityTheory.L2DbarEstimates.V n → ℝ} {v : _root_.ReciprocityTheory.L2DbarEstimates.V n}
    (hρ : ContDiffAt ℝ 1 ρ v) (w : _root_.ReciprocityTheory.L2DbarEstimates.V n) :
    ContinuousAt (fun x => _root_.GlobalTheory.dbar (fun y => (ρ y : ℂ)) x w) v := by
  have h : ContDiffAt ℝ 1 (fun y => (ρ y : ℂ)) v := Complex.ofRealCLM.contDiff.contDiffAt.comp v hρ
  have hf : ContinuousAt (fderiv ℝ (fun y => (ρ y : ℂ))) v :=
    (h.fderiv_right (m := 0) (by norm_num)).continuousAt
  simp only [_root_.GlobalTheory.dbar_apply]
  fun_prop

set_option autoImplicit false in
open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in

theorem _root_.GlobalTheory.GoodTop.continuousAt_corrC :
    ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] {ρ : _root_.ReciprocityTheory.L2DbarEstimates.V n → ℝ}
      {G₀ G₁ : _root_.ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ} {v : _root_.ReciprocityTheory.L2DbarEstimates.V n},
      ContDiffAt ℝ 1 ρ v → _root_.GlobalTheory.HermFrame.MContDiffAt 2 G₀ v → IsUnit (G₀ v).det →
        _root_.GlobalTheory.HermFrame.MContDiffAt 2 G₁ v → IsUnit (G₁ v).det →
        ContinuousAt (_root_.GlobalTheory.GoodTop.corrC ρ G₀ G₁) v := by
  intro n r _ _ ρ G₀ G₁ v hρ h₀ hd₀ h₁ hd₁
  have hcurv : ∀ {G : _root_.ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ}, _root_.GlobalTheory.HermFrame.MContDiffAt 2 G v → IsUnit (G v).det →
      ∀ a b p q, ContinuousAt (fun x => _root_.GlobalTheory.HermFrame.curv G x (_root_.GlobalTheory.GoodMetric.coordVec a)
        (_root_.GlobalTheory.GoodMetric.coordVec b) p q) v :=
    fun hG hdG a b p q =>
      (hG.curv (j := 0) hdG (by norm_num)
        (_root_.GlobalTheory.GoodMetric.coordVec a) (_root_.GlobalTheory.GoodMetric.coordVec b) p q).continuousAt
  have hconn : ∀ {G : _root_.ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ}, _root_.GlobalTheory.HermFrame.MContDiffAt 2 G v → IsUnit (G v).det →
      ∀ a p q, ContinuousAt
        (fun x => _root_.GlobalTheory.HermFrame.conn G x (_root_.GlobalTheory.GoodMetric.coordVec a) p q) v :=
    fun hG hdG a p q =>
      (hG.conn (j := 0) hdG (by norm_num)
        (_root_.GlobalTheory.GoodMetric.coordVec a) p q).continuousAt
  have hposition : ∀ j : Fin n, ContinuousAt (fun x => _root_.GlobalTheory.GoodTop.mixTop
      (_root_.GlobalTheory.GoodTop.intersection_update_fsHerm_neg_one (_root_.GlobalTheory.GoodTop.curvAt G₁ x)
        (_root_.GlobalTheory.GoodTop.cutForm ρ G₀ G₁ x) (_root_.GlobalTheory.GoodTop.curvAt G₀ x) j)) v := by
    intro j
    apply _root_.GlobalTheory.GoodTop.continuousAt_mixTop
    intro i a b p q
    unfold _root_.GlobalTheory.GoodTop.intersection_update_fsHerm_neg_one _root_.GlobalTheory.GoodTop.curvAt _root_.GlobalTheory.GoodTop.cutForm
    split_ifs
    · exact hcurv h₁ hd₁ a b p q
    · exact (continuousAt_dbar_ofReal_of_contDiffAt_one hρ _).mul ((hconn h₁ hd₁ a p q).sub (hconn h₀ hd₀ a p q))
    · exact hcurv h₀ hd₀ a b p q
  have heq : _root_.GlobalTheory.GoodTop.corrC ρ G₀ G₁ = fun x => ∑ j, _root_.GlobalTheory.GoodTop.mixTop
      (_root_.GlobalTheory.GoodTop.intersection_update_fsHerm_neg_one (_root_.GlobalTheory.GoodTop.curvAt G₁ x)
        (_root_.GlobalTheory.GoodTop.cutForm ρ G₀ G₁ x) (_root_.GlobalTheory.GoodTop.curvAt G₀ x) j) := by
    funext x
    rfl
  rw [heq]
  exact tendsto_finset_sum _ fun j _ => hposition j

end GlobalTheory.GoodTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRepresentativesOfSupport
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult Formalism.IndefR.Links GlobalTheory.SphPar
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.LocalReps.exists_isCosetRep : ∀ {D : D7} (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (e f : Formalism.L2.Theta.AE D) (α : GA D V), IsPrimeIdem P e f → SuppF V f α → ∃ R : Finset (GA D V), (∀ γ ∈ R, SuppF V f γ) ∧ IsCosetRep V {k | k ∈ KsphC V ∅ ∧ SuppF V f k} α R := by
  intro D V P e f α hP hα
  rcases id hP with ⟨he, rfl⟩ | ⟨rfl, -⟩
  · exact (GlobalTheory.SplitPlace.split_local V P e he).2.1 α hα
  · exact (GlobalTheory.InertDoubleCoset.inert_double_cosets V P f hP
      (GlobalTheory.SphericalComm.exists_unif_of_not_dvd P (GlobalTheory.HeckeOrthSum.not_dvd_different D P)) α hα).2.1
end

