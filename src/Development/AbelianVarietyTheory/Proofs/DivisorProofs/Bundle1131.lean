import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1074
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1090
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1091
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0886
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0004
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1092

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorCartanInvolutionInvariantAndPositive
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

namespace GlobalTheory.CartanTensor

open Matrix
open scoped Kronecker ComplexOrder

variable {n d : ℕ}

theorem map_star_mul {a b c : Type} [Fintype b] (A : Matrix a b ℂ) (B : Matrix b c ℂ) : (A * B).map star = A.map star * B.map star := by
  ext i j; simp [mul_apply, star_sum]

theorem cartan_comm {M θ : Matrix (Fin n) (Fin n) ℂ} (h : IsCartan M θ) : M * θ.map star = θᵀ * M := by
  obtain ⟨h1, h2, -⟩ := h
  have h1' : θ.map star * θ.map star = 1 := by
    rw [← map_star_mul, h1]; ext i j; simp [one_apply]
  calc M * θ.map star = θᵀ * M * θ.map star * θ.map star := by rw [h2]
    _ = θᵀ * M := by rw [Matrix.mul_assoc (θᵀ * M), h1', Matrix.mul_one]

theorem cartan_posDef {M θ : Matrix (Fin n) (Fin n) ℂ} (hM : ∀ i j, star (M j i) = M i j) (h : IsCartan M θ) :
    (θᵀ * M).PosDef := by
  have hH : (θᵀ * M).IsHermitian := by
    rw [IsHermitian, conjTranspose_mul, ← cartan_comm h]
    congr 1 <;> ext i j <;> simp [hM]
  refine posDef_iff_dotProduct_mulVec.2 ⟨hH, fun c hc => Complex.pos_iff.2 ⟨?_, (hH.im_star_dotProduct_mulVec_self c).symm⟩⟩
  have hx : star c ≠ 0 := by simpa using hc
  have := h.2.2 (star c) hx
  rw [star_star] at this
  convert this using 2
  rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]

end GlobalTheory.CartanTensor

namespace GlobalTheory.CartanTensor
open Matrix
open scoped Kronecker ComplexOrder
variable {n d : ℕ}

theorem quadruple_sum_eq_trace_transpose_mul (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin d) (Fin d) ℂ) (x y : Matrix (Fin n) (Fin d) ℂ) :
    (∑ i, ∑ j, ∑ k, ∑ l, x i j * A i k * B j l * star (y k l)) = trace (xᵀ * (A * y.map star * Bᵀ)) := by
  rw [← trace_transpose_mul, transpose_transpose]
  simp only [trace, diag_apply, mul_apply, transpose_apply, map_apply, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem quadruple_sum_eq_kronecker_quadraticForm (P : Matrix (Fin n) (Fin n) ℂ) (Q : Matrix (Fin d) (Fin d) ℂ) (x : Matrix (Fin n) (Fin d) ℂ) :
    (∑ i, ∑ j, ∑ k, ∑ l, x i j * P i k * Q j l * star (x k l)) =
      star (fun p : Fin n × Fin d => star (x p.1 p.2)) ⬝ᵥ ((P ⊗ₖ Q) *ᵥ fun p : Fin n × Fin d => star (x p.1 p.2)) := by
  simp only [dotProduct, mulVec, kronecker_apply, Fintype.sum_prod_type, Pi.star_apply, star_star, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

end GlobalTheory.CartanTensor

namespace GlobalTheory.CartanTensor
open Matrix
open scoped Kronecker ComplexOrder
variable {n d : ℕ}

theorem map_star_smulI {a b : Type} (M : Matrix a b ℂ) : (Complex.I • M).map star = (-Complex.I) • M.map star := by
  ext i j; simp

theorem cancelI {A B : Matrix (Fin d) (Fin d) ℂ} (h : Complex.I • A = Complex.I • B) : A = B :=
  smul_right_injective _ Complex.I_ne_zero h

theorem tensor_cartan_invariant_pos : ∀ (n d : ℕ) (JX θX : Matrix (Fin n) (Fin n) ℂ) (JW θW : Matrix (Fin d) (Fin d) ℂ),
    (∀ i j, star (JX j i) = JX i j) → IsCartan JX θX → (∀ i j, star (JW j i) = -JW i j) → IsCartan (Complex.I • JW) θW →
    ∀ x y : Matrix (Fin n) (Fin d) ℂ,
      (∑ i, ∑ j, ∑ k, ∑ l, (Complex.I • (θX * x * θWᵀ)) i j * JX i k * JW j l * star ((Complex.I • (θX * y * θWᵀ)) k l)) =
        (∑ i, ∑ j, ∑ k, ∑ l, x i j * JX i k * JW j l * star (y k l)) ∧
      (x ≠ 0 → 0 < -(∑ i, ∑ j, ∑ k, ∑ l, x i j * JX i k * JW j l * star ((Complex.I • (θX * x * θWᵀ)) k l)).re) := by
  intro n d JX θX JW θW hJX hX hJW hW x y
  have hWc : θWᵀ * JW * θW.map star = JW := by
    have h := hW.2.1
    rw [Matrix.mul_smul, Matrix.smul_mul] at h
    exact cancelI h
  have cW : JW * θW.map star = θWᵀ * JW := by
    have h := cartan_comm hW
    rw [Matrix.mul_smul, Matrix.smul_mul] at h
    exact cancelI h
  have cX := cartan_comm hX
  have hIW : ∀ i j, star ((Complex.I • JW) j i) = (Complex.I • JW) i j := by
    intro i j; simp [hJW]
  constructor
  · rw [quadruple_sum_eq_trace_transpose_mul, quadruple_sum_eq_trace_transpose_mul]
    have e1 : (Complex.I • (θX * x * θWᵀ))ᵀ * (JX * (Complex.I • (θX * y * θWᵀ)).map star * JWᵀ) =
        θW * (xᵀ * (θXᵀ * JX * θX.map star) * y.map star * (θW.map star)ᵀ * JWᵀ) := by
      rw [map_star_smulI, transpose_smul, map_star_mul, map_star_mul, transpose_mul, transpose_mul, transpose_transpose,
        transpose_map]
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc, mul_neg, Complex.I_mul_I, neg_neg, one_smul, neg_mul]
    have e2 : xᵀ * (θXᵀ * JX * θX.map star) * y.map star * (θW.map star)ᵀ * JWᵀ * θW =
        xᵀ * (θXᵀ * JX * θX.map star) * y.map star * (θWᵀ * JW * θW.map star)ᵀ := by
      simp only [transpose_mul, transpose_transpose, Matrix.mul_assoc]
    rw [e1, trace_mul_comm, e2, hX.2.1, hWc]
    simp only [Matrix.mul_assoc]
  · intro hx
    have e3 : xᵀ * (JX * (Complex.I • (θX * x * θWᵀ)).map star * JWᵀ) =
        -(xᵀ * ((θXᵀ * JX) * x.map star * (θWᵀ * (Complex.I • JW))ᵀ)) := by
      have h3 : xᵀ * (JX * (Complex.I • (θX * x * θWᵀ)).map star * JWᵀ) =
          (-Complex.I) • (xᵀ * (JX * θX.map star) * x.map star * (JW * θW.map star)ᵀ) := by
        rw [map_star_smulI, map_star_mul, map_star_mul, transpose_map, transpose_mul]
        simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
      rw [h3, cX, cW]
      simp only [Matrix.smul_mul, Matrix.mul_smul, transpose_smul, neg_smul, Matrix.mul_assoc]
    rw [quadruple_sum_eq_trace_transpose_mul, e3, trace_neg, Complex.neg_re, neg_neg,
      ← quadruple_sum_eq_trace_transpose_mul (θXᵀ * JX) (θWᵀ * (Complex.I • JW)) x x, quadruple_sum_eq_kronecker_quadraticForm]
    have hK := (cartan_posDef hJX hX).kronecker (cartan_posDef hIW hW)
    have hc : (fun p : Fin n × Fin d => star (x p.1 p.2)) ≠ 0 := by
      intro h; apply hx; ext i j; have := congrFun h (i, j); simpa using this
    exact (Complex.pos_iff.1 ((posDef_iff_dotProduct_mulVec.1 hK).2 hc)).1

end GlobalTheory.CartanTensor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionModuleStructure
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.TorCls
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.TorCls.OpenP

theorem mem_range_map_of_entries {R : Type} [CommRing R] (S : Subring R) {n : ℕ} (X : GL (Fin n) R)
    (h1 : ∀ i j, (X : Matrix (Fin n) (Fin n) R) i j ∈ S)
    (h2 : ∀ i j, ((X⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j ∈ S) :
    X ∈ (GeneralLinearGroup.map S.subtype).range := by
  let A : Matrix (Fin n) (Fin n) S := Matrix.of fun i j => ⟨_, h1 i j⟩
  let B : Matrix (Fin n) (Fin n) S := Matrix.of fun i j => ⟨_, h2 i j⟩
  have hA : A.map S.subtype = (X : Matrix (Fin n) (Fin n) R) := by ext i j; rfl
  have hB : B.map S.subtype = ((X⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) := by ext i j; rfl
  have inj : Function.Injective (fun M : Matrix (Fin n) (Fin n) S => M.map S.subtype) :=
    Matrix.map_injective Subtype.val_injective
  have hAB : A * B = 1 := inj (by
    simp only [Matrix.map_mul, hA, hB, Matrix.map_one _ (map_zero S.subtype) (map_one S.subtype)]
    exact X.mul_inv)
  have hBA : B * A = 1 := inj (by
    simp only [Matrix.map_mul, hA, hB, Matrix.map_one _ (map_zero S.subtype) (map_one S.subtype)]
    exact X.inv_mul)
  exact ⟨⟨A, B, hAB, hBA⟩, Units.ext hA⟩

variable (p : ℕ) [Fact p.Prime]

theorem exists_pow_mul_mem (L : IntermediateField ℚ_[p] (PadicAlgCl p)) (x : L) :
    ∃ N : ℕ, (((p : L) ^ N * x : L) : PadicAlgCl p) ∈ ReciprocityTheory.DiscreteGroups.LocalClassField.Obar p := by
  have hp : ‖(p : PadicAlgCl p)‖ < 1 := by
    rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)), PadicAlgCl.norm_extends, Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (Nat.one_lt_cast.2 (Fact.out : p.Prime).one_lt)
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (show 0 < 1 / (‖(x : PadicAlgCl p)‖ + 1) by positivity) hp
  refine ⟨N, ReciprocityTheory.DiscreteGroups.LocalClassField.mem_Obar_iff.2 ?_⟩
  have e : (((p : L) ^ N * x : L) : PadicAlgCl p) = (p : PadicAlgCl p) ^ N * (x : PadicAlgCl p) := by
    simp
  rw [e, norm_mul, norm_pow]
  have h0 : 0 ≤ ‖(x : PadicAlgCl p)‖ := norm_nonneg _
  calc ‖(p : PadicAlgCl p)‖ ^ N * ‖(x : PadicAlgCl p)‖ ≤ 1 / (‖(x : PadicAlgCl p)‖ + 1) * (‖(x : PadicAlgCl p)‖ + 1) :=
        mul_le_mul hN.le (by linarith) h0 (by positivity)
    _ = 1 := by field_simp

end GlobalTheory.TorCls.OpenP

namespace GlobalTheory.TorCls.OpenP
variable (p : ℕ) [Fact p.Prime]

theorem natCast_pow_mem_intKQ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r N : ℕ) :
    (p : KQ p K r) ^ N ∈ intKQ p K r :=
  pow_mem (natCast_mem _ p) N

theorem inclK_mem_intKQ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ) (x : K)
    (h : (x : PadicAlgCl p) ∈ ReciprocityTheory.DiscreteGroups.LocalClassField.Obar p) : inclK p K r x ∈ intKQ p K r :=
  Subring.subset_closure (Or.inl ⟨⟨x, h⟩, rfl⟩)

theorem inclQ_mem_intKQ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ) (x : Qr p r)
    (h : (x : PadicAlgCl p) ∈ ReciprocityTheory.DiscreteGroups.LocalClassField.Obar p) : inclQ p K r x ∈ intKQ p K r :=
  Subring.subset_closure (Or.inr ⟨⟨x, h⟩, rfl⟩)

theorem tmul_eq_inclK_mul_inclQ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ) (a : K) (b : Qr p r) :
    (show KQ p K r from a ⊗ₜ[ℚ_[p]] b) = inclK p K r a * inclQ p K r b := by
  change a ⊗ₜ[ℚ_[p]] b = (a ⊗ₜ[ℚ_[p]] (1 : Qr p r)) * ((1 : K) ⊗ₜ[ℚ_[p]] b)
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem exists_pow_mul_mem_intKQ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ) (x : KQ p K r) :
    ∃ N : ℕ, (p : KQ p K r) ^ N * x ∈ intKQ p K r := by
  refine TensorProduct.induction_on (R := ℚ_[p]) (M := K) (N := Qr p r)
    (motive := fun y : K ⊗[ℚ_[p]] Qr p r => ∃ N : ℕ, (p : KQ p K r) ^ N * (show KQ p K r from y) ∈ intKQ p K r) x
    ⟨0, ?_⟩ ?_ ?_
  · change (p : KQ p K r) ^ 0 * (0 : KQ p K r) ∈ intKQ p K r
    rw [mul_zero]; exact zero_mem _
  · intro a b
    obtain ⟨N₁, h₁⟩ := exists_pow_mul_mem p K a
    obtain ⟨N₂, h₂⟩ := exists_pow_mul_mem p (Qr p r) b
    refine ⟨N₁ + N₂, ?_⟩
    rw [tmul_eq_inclK_mul_inclQ]
    have e : (p : KQ p K r) ^ (N₁ + N₂) * (inclK p K r a * inclQ p K r b) =
        inclK p K r ((p : K) ^ N₁ * a) * inclQ p K r ((p : Qr p r) ^ N₂ * b) := by
      rw [map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast, pow_add]; ring
    rw [e]
    exact mul_mem (inclK_mem_intKQ p K r _ h₁) (inclQ_mem_intKQ p K r _ h₂)
  · rintro x y ⟨N, hN⟩ ⟨M, hM⟩
    refine ⟨N + M, ?_⟩
    change (p : KQ p K r) ^ (N + M) * ((show KQ p K r from x) + (show KQ p K r from y)) ∈ intKQ p K r
    generalize (show KQ p K r from x) = x' at hN ⊢
    generalize (show KQ p K r from y) = y' at hM ⊢
    have e : (p : KQ p K r) ^ (N + M) * (x' + y') =
        (p : KQ p K r) ^ M * ((p : KQ p K r) ^ N * x') + (p : KQ p K r) ^ N * ((p : KQ p K r) ^ M * y') := by
      ring
    rw [e]
    exact add_mem (mul_mem (natCast_pow_mem_intKQ p K r M) hN) (mul_mem (natCast_pow_mem_intKQ p K r N) hM)

theorem exists_pow_mul_entries_mem (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (KQ p K r)) :
    ∃ N : ℕ, ∀ i j, (p : KQ p K r) ^ N * A i j ∈ intKQ p K r := by
  choose f hf using exists_pow_mul_mem_intKQ p K r
  refine ⟨Finset.univ.sup fun ij : Fin n × Fin n => f (A ij.1 ij.2), fun i j => ?_⟩
  have hle : f (A i j) ≤ Finset.univ.sup fun ij : Fin n × Fin n => f (A ij.1 ij.2) :=
    Finset.le_sup (f := fun ij : Fin n × Fin n => f (A ij.1 ij.2)) (Finset.mem_univ (i, j))
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
  rw [hk, add_comm, pow_add, mul_assoc]
  exact mul_mem (natCast_pow_mem_intKQ p K r _) (hf _)

end GlobalTheory.TorCls.OpenP

namespace GlobalTheory.TorCls.OpenP
variable (p : ℕ) [Fact p.Prime]

theorem norm_p_pos : 0 < ‖(p : PadicAlgCl p)‖ :=
  norm_pos_iff.2 (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)

theorem exists_conj_entries_mem (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ) {n : ℕ}
    (R : GL (Fin n) (KQ p K r)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ M : Matrix (Fin n) (Fin n) K,
      (∀ i j, ‖(((M - 1) i j : K) : PadicAlgCl p)‖ < ε) →
      ∀ i l, (((R⁻¹ : GL (Fin n) (KQ p K r)) : Matrix (Fin n) (Fin n) (KQ p K r)) * M.map (inclK p K r) *
        (R : Matrix (Fin n) (Fin n) (KQ p K r))) i l ∈ intKQ p K r := by
  obtain ⟨N₁, h₁⟩ := exists_pow_mul_entries_mem p K r (R : Matrix (Fin n) (Fin n) (KQ p K r))
  obtain ⟨N₂, h₂⟩ := exists_pow_mul_entries_mem p K r ((R⁻¹ : GL (Fin n) (KQ p K r)) : Matrix (Fin n) (Fin n) (KQ p K r))
  refine ⟨‖(p : PadicAlgCl p)‖ ^ (N₁ + N₂), pow_pos (norm_p_pos p) _, fun M hM i l => ?_⟩
  have hp0 : (p : K) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hsplit : M.map (inclK p K r) = 1 + (M - 1).map (inclK p K r) := by
    ext i j
    simp only [Matrix.add_apply, Matrix.map_apply, Matrix.sub_apply, Matrix.one_apply, map_sub]
    split_ifs <;> simp
  rw [hsplit, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Units.inv_mul]
  refine add_mem ?_ ?_
  · rw [Matrix.one_apply]; split_ifs
    · exact one_mem _
    · exact zero_mem _
  rw [Matrix.mul_apply]
  refine sum_mem fun k _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul]
  refine sum_mem fun j _ => ?_
  set B := (M - 1) j k with hB
  set b : K := ((p : K) ^ (N₁ + N₂))⁻¹ * B with hb
  have hBb : B = (p : K) ^ (N₁ + N₂) * b := by rw [hb, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hp0), one_mul]
  have hbint : (b : PadicAlgCl p) ∈ ReciprocityTheory.DiscreteGroups.LocalClassField.Obar p := by
    rw [ReciprocityTheory.DiscreteGroups.LocalClassField.mem_Obar_iff]
    have h := hM j k
    rw [← hB, hBb] at h
    have e : (((p : K) ^ (N₁ + N₂) * b : K) : PadicAlgCl p) = (p : PadicAlgCl p) ^ (N₁ + N₂) * (b : PadicAlgCl p) := by
      simp
    rw [e, norm_mul, norm_pow] at h
    have hpos := pow_pos (norm_p_pos p) (N₁ + N₂)
    by_contra hc
    push_neg at hc
    nlinarith
  have e2 : ((R⁻¹ : GL (Fin n) (KQ p K r)) : Matrix (Fin n) (Fin n) (KQ p K r)) i j * ((M - 1).map (inclK p K r)) j k *
      (R : Matrix (Fin n) (Fin n) (KQ p K r)) k l =
      ((p : KQ p K r) ^ N₂ * ((R⁻¹ : GL (Fin n) (KQ p K r)) : Matrix (Fin n) (Fin n) (KQ p K r)) i j) *
        inclK p K r b * ((p : KQ p K r) ^ N₁ * (R : Matrix (Fin n) (Fin n) (KQ p K r)) k l) := by
    rw [Matrix.map_apply, ← hB, hBb, map_mul, map_pow, map_natCast, pow_add]; ring
  rw [e2]
  exact mul_mem (mul_mem (h₂ i j) (inclK_mem_intKQ p K r b hbint)) (h₁ k l)

end GlobalTheory.TorCls.OpenP

namespace GlobalTheory.TorCls.OpenP

theorem scalar_one_entry {R : Type} [CommRing R] (u : Rˣ) (i j : Fin 1) :
    ((GeneralLinearGroup.scalar (Fin 1) u : GL (Fin 1) R) : Matrix (Fin 1) (Fin 1) R) i j = (u : R) := by
  fin_cases i; fin_cases j; simp [GeneralLinearGroup.scalar]

theorem psiP_fst_mem (p : ℕ) [Fact p.Prime] (G : HTGroup p) (z : (ℚ_[p] ⊗[ℚ] G.C)ˣ × ℚ_[p]ˣ)
    (h1 : ‖(z.2 : ℚ_[p])‖ ≤ 1) (h2 : ‖((z.2⁻¹ : ℚ_[p]ˣ) : ℚ_[p])‖ ≤ 1) :
    (psiP G z).1 ∈ GlobalTheory.LKLoc.Kint p (Q0 p) 1 1 := by
  have hfst : (psiP G z).1 = GeneralLinearGroup.scalar (Fin 1) (Units.map (algebraMap ℚ_[p] (Qr p 1)).toMonoidHom z.2) := rfl
  have hmem : ∀ a : ℚ_[p], ‖a‖ ≤ 1 → algebraMap ℚ_[p] (Qr p 1) a ∈ GlobalTheory.LKLoc.intR p (Q0 p) 1 := by
    intro a ha
    show ((algebraMap ℚ_[p] (Qr p 1) a : Qr p 1) : PadicAlgCl p) ∈ ReciprocityTheory.DiscreteGroups.LocalClassField.Obar p
    rw [ReciprocityTheory.DiscreteGroups.LocalClassField.mem_Obar_iff, IntermediateField.coe_algebraMap_apply, PadicAlgCl.norm_extends]
    exact ha
  refine mem_range_map_of_entries _ _ (fun i j => ?_) (fun i j => ?_)
  · rw [hfst, scalar_one_entry]; exact hmem _ h1
  · rw [hfst, ← map_inv, scalar_one_entry, ← map_inv]; exact hmem _ h2

theorem openp : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (r₂ : Gr G 1),
    letI : TopologicalSpace (ℚ_[p] ⊗[ℚ] G.C) := moduleTopology ℚ_[p] (ℚ_[p] ⊗[ℚ] G.C);
    ∃ O : Set ((ℚ_[p] ⊗[ℚ] G.C)ˣ × ℚ_[p]ˣ), IsOpen O ∧ 1 ∈ O ∧ ∀ z ∈ O, r₂⁻¹ * psiP G z * r₂ ∈ KHT p G.m G.n 1 G.Fw := by
  intro p _ G r₂
  letI : TopologicalSpace (ℚ_[p] ⊗[ℚ] G.C) := moduleTopology ℚ_[p] (ℚ_[p] ⊗[ℚ] G.C)
  haveI : IsModuleTopology ℚ_[p] (ℚ_[p] ⊗[ℚ] G.C) := ⟨rfl⟩
  choose ε hε hM using fun w : Fin G.m => exists_conj_entries_mem p (G.Fw w) 1 (r₂.2 w)
  let e : ∀ (w : Fin G.m) (i j : Fin G.n), ℚ_[p] ⊗[ℚ] G.C → PadicAlgCl p :=
    fun w i j g => (((G.locW w g - 1) i j : G.Fw w) : PadicAlgCl p)
  have hcont : ∀ w i j, Continuous (e w i j) := by
    intro w i j
    let L : ℚ_[p] ⊗[ℚ] G.C →ₗ[ℚ_[p]] PadicAlgCl p :=
      (G.Fw w).val.toLinearMap ∘ₗ (Matrix.entryLinearMap ℚ_[p] (G.Fw w) i j) ∘ₗ (G.locW w).toLinearMap
    have he : e w i j = fun g => L g - (((1 : Matrix (Fin G.n) (Fin G.n) (G.Fw w)) i j : G.Fw w) : PadicAlgCl p) := by
      funext g; simp [e, L, Matrix.sub_apply]
    rw [he]
    exact (IsModuleTopology.continuous_of_linearMap L).sub continuous_const
  have hent : ∀ (w : Fin G.m) (z' : (ℚ_[p] ⊗[ℚ] G.C)ˣ × ℚ_[p]ˣ), (∀ i j, ‖e w i j (z'.1 : ℚ_[p] ⊗[ℚ] G.C)‖ < ε w) →
      ∀ i l, (((r₂⁻¹ * psiP G z' * r₂).2 w : GL (Fin G.n) (KQ p (G.Fw w) 1)) : Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw w) 1)) i l ∈ intKQ p (G.Fw w) 1 := by
    intro w z' h i l
    have hv : (((r₂⁻¹ * psiP G z' * r₂).2 w : GL (Fin G.n) (KQ p (G.Fw w) 1)) : Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw w) 1)) =
        (((r₂.2 w)⁻¹ : GL (Fin G.n) (KQ p (G.Fw w) 1)) : Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw w) 1)) *
          (G.locW w (z'.1 : ℚ_[p] ⊗[ℚ] G.C)).map (inclK p (G.Fw w) 1) * ((r₂.2 w : GL (Fin G.n) (KQ p (G.Fw w) 1)) : Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw w) 1)) := rfl
    rw [hv]
    exact hM w _ h i l
  refine ⟨{z | ‖(z.2 : ℚ_[p])‖ ≤ 1 ∧ ‖((z.2⁻¹ : ℚ_[p]ˣ) : ℚ_[p])‖ ≤ 1 ∧
      ∀ w i j, ‖e w i j (z.1 : ℚ_[p] ⊗[ℚ] G.C)‖ < ε w ∧ ‖e w i j (((z.1)⁻¹ : (ℚ_[p] ⊗[ℚ] G.C)ˣ) : ℚ_[p] ⊗[ℚ] G.C)‖ < ε w},
    ?_, ?_, ?_⟩
  · have hball : IsOpen {x : ℚ_[p] | ‖x‖ ≤ 1} := by
      have := IsUltrametricDist.isOpen_closedBall (0 : ℚ_[p]) (one_ne_zero : (1 : ℝ) ≠ 0)
      simpa [Metric.closedBall, dist_zero_right] using this
    simp only [Set.setOf_and, Set.setOf_forall]
    refine (hball.preimage ((Units.continuous_val (M := ℚ_[p])).comp (continuous_snd (X := (ℚ_[p] ⊗[ℚ] G.C)ˣ) (Y := ℚ_[p]ˣ)))).inter
      ((hball.preimage ((Units.continuous_coe_inv (M := ℚ_[p])).comp (continuous_snd (X := (ℚ_[p] ⊗[ℚ] G.C)ˣ) (Y := ℚ_[p]ˣ)))).inter ?_)
    refine isOpen_iInter_of_finite fun w => isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
    exact (isOpen_lt (continuous_norm.comp ((hcont w i j).comp ((Units.continuous_val (M := ℚ_[p] ⊗[ℚ] G.C)).comp continuous_fst)))
      continuous_const).inter
      (isOpen_lt (continuous_norm.comp ((hcont w i j).comp ((Units.continuous_coe_inv (M := ℚ_[p] ⊗[ℚ] G.C)).comp continuous_fst)))
      continuous_const)
  · refine ⟨by simp, by simp, fun w i j => ⟨?_, ?_⟩⟩ <;> simp [e, hε w]
  · rintro z ⟨h1, h2, h3⟩
    refine Subgroup.mem_prod.2 ⟨?_, ?_⟩
    · have hk := psiP_fst_mem p G z h1 h2
      have := (normal_of_gl_one (GlobalTheory.LKLoc.Kint p (Q0 p) 1 1)).conj_mem _ hk r₂.1⁻¹
      simpa using this
    · refine (Subgroup.mem_pi _).2 fun w _ => ?_
      refine mem_range_map_of_entries _ _ (hent w z fun i j => (h3 w i j).1) ?_
      have hinv : ((r₂⁻¹ * psiP G z * r₂).2 w)⁻¹ = (r₂⁻¹ * psiP G z⁻¹ * r₂).2 w := by
        have hg : (r₂⁻¹ * psiP G z * r₂)⁻¹ = r₂⁻¹ * psiP G z⁻¹ * r₂ := by rw [map_inv]; group
        rw [show ((r₂⁻¹ * psiP G z * r₂).2 w)⁻¹ = ((r₂⁻¹ * psiP G z * r₂)⁻¹).2 w from rfl, hg]
      rw [hinv]
      exact hent w z⁻¹ fun i j => (h3 w i j).2

end GlobalTheory.TorCls.OpenP
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TprodCyclicModuloSpanSomeFactor
section
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

noncomputable section

namespace GlobalTheory.HoweR

theorem tprod_cyclic_top : ∀ (T : Type) [Fintype T] [DecidableEq T] (V : T → Type) [∀ w, AddCommGroup (V w)] [∀ w, Module ℂ (V w)], ∀ (R S : T → ℕ) (a : ∀ w, Mat (R w) (S w) →ₗ[ℂ] Module.End ℂ (V w)) (C : ∀ w, Submodule ℂ (V w)) (v : ∀ w, V w), (∀ w, genSub (a w) {v w} ⊔ C w = ⊤) → ∀ N : Submodule ℂ (PiTensorProduct ℂ V), (∀ w, Stab (actAt w (a w)) N) → tensAny C ≤ N → PiTensorProduct.tprod ℂ v ∈ N → N = ⊤ := by
  intro T _ _ V _ _ R S a C v hgen N hN hC hv
  have key : ∀ s : Finset T, ∀ f : ∀ w, V w, (∀ w, w ∉ s → f w = v w) → PiTensorProduct.tprod ℂ f ∈ N := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro f hf
      have : f = v := funext fun w => hf w (Finset.notMem_empty w)
      rw [this]; exact hv
    | insert w s hws ih =>
      intro f hf
      let K : Submodule ℂ (V w) :=
        Submodule.comap ((PiTensorProduct.tprod ℂ (s := V)).toLinearMap f w) N
      have hmem : ∀ x, x ∈ K ↔ PiTensorProduct.tprod ℂ (Function.update f w x) ∈ N := by
        intro x; simp [K, MultilinearMap.toLinearMap_apply]
      have hstab : ∀ Z, ∀ y ∈ K, a w Z y ∈ K := by
        intro Z y hy
        rw [hmem] at hy ⊢
        have h1 := hN w Z _ hy
        rw [actAt_apply, atPl, PiTensorProduct.map_tprod] at h1
        convert h1 using 2
        funext i
        by_cases h : i = w
        · subst h; simp
        · simp [Function.update_of_ne h]
      have hvK : v w ∈ K := by
        rw [hmem]
        apply ih
        intro u hu
        by_cases h : u = w
        · subst h; simp
        · rw [Function.update_of_ne h]
          exact hf u (by simp [h, hu])
      have hCK : C w ≤ K := by
        intro c hc
        rw [hmem]
        apply hC
        apply Submodule.subset_span
        exact ⟨Function.update f w c, ⟨w, by simpa using hc⟩, rfl⟩
      have hgK : genSub (a w) {v w} ≤ K := by
        apply sInf_le
        refine ⟨?_, hstab⟩
        simpa using hvK
      have htop : K = ⊤ := by
        rw [eq_top_iff, ← hgen w]
        exact sup_le hgK hCK
      have : f w ∈ K := by rw [htop]; trivial
      rw [hmem, Function.update_eq_self] at this
      exact this
  have hall : ∀ f : ∀ w, V w, PiTensorProduct.tprod ℂ f ∈ N :=
    fun f => key Finset.univ f (fun w hw => absurd (Finset.mem_univ w) hw)
  rw [eq_top_iff, ← PiTensorProduct.span_tprod_eq_top, Submodule.span_le]
  rintro _ ⟨f, rfl⟩
  exact hall f

end GlobalTheory.HoweR
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TprodMemTensSpan
section
noncomputable section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.RealLift

namespace GlobalTheory.KFixIrr

def chiOne (P Q R S : ℕ) (x : ℚ) : Submodule ℂ (Formalism.BasicNotions.TH.Pol P Q R S) :=
  ⨅ X : {X : Mat P Q // IsKC X}, LinearMap.ker (fockAct1 P Q R S X.1 - ((x : ℂ) * X.1.trace) • 1)

theorem mem_chiOne {P Q R S : ℕ} (x : ℚ) (f : Formalism.BasicNotions.TH.Pol P Q R S) :
    f ∈ chiOne P Q R S x ↔ ∀ X : Mat P Q, IsKC X → fockAct1 P Q R S X f = ((x : ℂ) * X.trace) • f := by
  simp only [chiOne, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, sub_eq_zero, Subtype.forall]

def lowOne (P Q R S : ℕ) (x : ℚ) (d : ℕ) : Submodule ℂ (Formalism.BasicNotions.TH.Pol P Q R S) :=
  chiOne P Q R S x ⊓ MvPolynomial.restrictTotalDegree (Ln P Q R S) ℂ d

theorem mem_lowOne {P Q R S : ℕ} (x : ℚ) (d : ℕ) (f : Formalism.BasicNotions.TH.Pol P Q R S) :
    f ∈ lowOne P Q R S x d ↔ f ∈ chiOne P Q R S x ∧ f.totalDegree ≤ d := by
  rw [lowOne, Submodule.mem_inf, MvPolynomial.mem_restrictTotalDegree]

def tensSpan {ι V : Type} [Fintype ι] [AddCommGroup V] [Module ℂ V] (H : ι → Submodule ℂ V) :
    Submodule ℂ (⨂[ℂ] _ : ι, V) :=
  Submodule.span ℂ {T | ∃ f : ι → V, (∀ w, f w ∈ H w) ∧ T = PiTensorProduct.tprod ℂ f}

theorem tprod_mem_tensSpan {ι V : Type} [Fintype ι] [AddCommGroup V] [Module ℂ V] (H : ι → Submodule ℂ V)
    (f : ι → V) (hf : ∀ w, f w ∈ H w) : PiTensorProduct.tprod ℂ f ∈ tensSpan H :=
  Submodule.subset_span ⟨f, hf, rfl⟩

end GlobalTheory.KFixIrr

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedNormConjNormalizeAndDegreeOneStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedNormConj_normalize_and_degree_one : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), (∀ (r : ℕ) (γ : Gp G) (δ z : Gr G r), 0 < r → IsNrm G r γ δ z → IsNrm G r γ (z * δ * (sigG G r z)⁻¹) 1) ∧ ∀ γ : Gp G, IsNrm G 1 γ (inclG G 1 γ) 1 := by
  first | (exact @GlobalTheory.nrm_exact) | (exact GlobalTheory.nrm_exact) | (intros; apply GlobalTheory.nrm_exact  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypesSepOfOkIsFam
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.FamSep

theorem typesSep_of_ok_isFam : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) {s : ℕ}, A.fam.Ok s → R.IsFam → A.fam.TypesSep :=
  fun {_ _ _ _ _ _ A _ _ _ _} _ _ hOk hF => typesSep_of_ok A hOk fun P => (hF.degR A.μ0 P).1

end GlobalTheory.FamSep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitarySimilitudeIntegralSubgroupCommensuratedFrStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitarySimilitudeIntegralSubgroup_commensurated_frobenius : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (r : ℕ), 0 < r → (∀ g : Gr G r, Subgroup.Commensurable ((KHT p G.m G.n r G.Fw).map (MulAut.conj g).toMonoidHom) (KHT p G.m G.n r G.Fw)) ∧ (KHT p G.m G.n r G.Fw).comap (inclG G r) = Kp0 G ∧ (KHT p G.m G.n r G.Fw).map (sigG G r) ≤ KHT p G.m G.n r G.Fw := by
  first | (exact @GlobalTheory.heckeOperator_integral) | (exact GlobalTheory.heckeOperator_integral) | (intros; apply GlobalTheory.heckeOperator_integral  <;> assumption)
end

