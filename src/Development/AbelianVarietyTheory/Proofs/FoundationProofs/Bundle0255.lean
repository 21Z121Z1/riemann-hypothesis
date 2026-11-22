import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0239
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0245
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0241
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0233
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0234
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0246
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0244
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0240
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0226

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HalfPeriodThetaDifferentiableAndSignedTranslateI
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.HalfPeriodTheta

theorem parity_mod_two : ∀ a b c d s₁ s₂ x₁ x₂ : ZMod 2,
    a * a + b * c = a → a * b + b * d = b → c * a + d * c = c → c * b + d * d = d →
    ¬ (a * s₁ + c * s₂ = 0 ∧ b * s₁ + d * s₂ = 0) →
    ¬ (s₁ - (a * s₁ + c * s₂) = 0 ∧ s₂ - (b * s₁ + d * s₂) = 0) →
    (((a * x₁ + c * x₂) * x₂ - (b * x₁ + d * x₂) * x₁) + (x₁ * s₂ - x₂ * s₁) = 0 ↔ x₁ = 0 ∧ x₂ = 0) := by
  decide

theorem exists_orthonormal_basis_family (Λ : AddSubgroup ℂ) (ω t : ℂ) (G : ℂ → ℂ) (z : ℂ) :
    U1 Λ ω (U1 Λ t G) z =
      Complex.exp (-(Real.pi : ℂ) * Complex.I * (gl3FieldFirst Λ ω (2 * t) : ℂ)) * U1 Λ t (U1 Λ ω G) z := by
  have h : ((gl3FieldFirst Λ ω (2 * t) : ℝ) : ℂ) * Complex.I =
      (ω * (starRingEnd ℂ) t - t * (starRingEnd ℂ) ω) / (area Λ : ℂ) := by
    have h2 := Complex.sub_conj (ω * (starRingEnd ℂ) t)
    rw [map_mul, Complex.conj_conj, mul_comm ((starRingEnd ℂ) ω) t] at h2
    have h3 : (ω * (starRingEnd ℂ) (2 * t)).im = 2 * (ω * (starRingEnd ℂ) t).im := by
      simp; ring
    rw [h2, gl3FieldFirst, h3]
    push_cast
    ring
  have h' : -(Real.pi : ℂ) * Complex.I * (gl3FieldFirst Λ ω (2 * t) : ℂ) =
      -(Real.pi : ℂ) * ((ω * (starRingEnd ℂ) t - t * (starRingEnd ℂ) ω) / (area Λ : ℂ)) := by
    rw [← h]; ring
  rw [h']
  simp only [U1]
  rw [add_right_comm z t ω, mul_assoc (G _), mul_assoc (G _), ← Complex.exp_add, ← Complex.exp_add,
    mul_left_comm _ (G _), ← Complex.exp_add]
  congr 2
  ring

theorem even_im_hermitian_sub (Λ : AddSubgroup ℂ) (w₁ w₂ : ℂ) (hi : LinearIndependent ℝ ![w₁, w₂])
    (hΛ : Λ = AddSubgroup.closure {w₁, w₂})
    (hsd : ∀ z : ℂ, z ∈ Λ ↔ ∀ w ∈ Λ, ∃ m : ℤ, gl3FieldFirst Λ z w = m)
    (θ : ℂ) (N : ℤ) (hN : Even N) (hθ : θ * θ = θ - N) (hst : ∀ w ∈ Λ, θ * w ∈ Λ)
    (t : ℂ) (ht : 2 * t ∈ Λ) (h1 : θ * t ∉ Λ) (h2 : (1 - θ) * t ∉ Λ) (ω : ℂ) (hω : ω ∈ Λ) :
    ∃ m n : ℤ, gl3FieldFirst Λ (θ * ω) ω = m ∧ gl3FieldFirst Λ ω (2 * t) = n ∧ (Even (m + n) ↔ ω / 2 ∈ Λ) := by
  have mem : ∀ z, z ∈ Λ ↔ ∃ x y : ℤ, z = x * w₁ + y * w₂ := by
    intro z
    rw [hΛ, AddSubgroup.mem_closure_pair]
    simp only [zsmul_eq_mul, eq_comm]
  have uniq : ∀ x y : ℤ, (x : ℂ) * w₁ + y * w₂ = 0 → x = 0 ∧ y = 0 := by
    intro x y h
    have := LinearIndependent.pair_iff.1 hi (x : ℝ) (y : ℝ) (by simpa using h)
    exact_mod_cast this
  have half : ∀ x y : ℤ, ((x : ℂ) * w₁ + y * w₂) / 2 ∈ Λ ↔ (x : ZMod 2) = 0 ∧ (y : ZMod 2) = 0 := by
    intro x y
    rw [mem, ZMod.intCast_eq_zero_iff_even, ZMod.intCast_eq_zero_iff_even]
    constructor
    · rintro ⟨u, v, h⟩
      obtain ⟨e1, e2⟩ := uniq (x - 2 * u) (y - 2 * v) (by push_cast; linear_combination 2 * h)
      exact ⟨⟨u, by omega⟩, ⟨v, by omega⟩⟩
    · rintro ⟨⟨u, rfl⟩, ⟨v, rfl⟩⟩
      exact ⟨u, v, by push_cast; ring⟩
  have hw₁ : w₁ ∈ Λ := (mem _).2 ⟨1, 0, by simp⟩
  have hw₂ : w₂ ∈ Λ := (mem _).2 ⟨0, 1, by simp⟩
  obtain ⟨e, he⟩ := (hsd w₁).1 hw₁ w₂ hw₂
  have EFr : ∀ x y u v : ℝ, gl3FieldFirst Λ (x * w₁ + y * w₂) (u * w₁ + v * w₂) = (x * v - y * u) * e := by
    intro x y u v
    rw [← he]
    simp only [gl3FieldFirst]
    simp
    ring
  have EFi : ∀ x y u v : ℤ, gl3FieldFirst Λ (x * w₁ + y * w₂) (u * w₁ + v * w₂) = (((x * v - y * u) * e : ℤ) : ℝ) := by
    intro x y u v
    have := EFr x y u v
    push_cast at this ⊢
    exact this
  have hodd : (e : ZMod 2) = 1 := by
    rw [ZMod.intCast_eq_one_iff_odd, ← Int.not_even_iff_odd]
    rintro ⟨k, hk⟩
    have : (((1 : ℤ) : ℂ) * w₁ + ((0 : ℤ) : ℂ) * w₂) / 2 ∈ Λ := by
      rw [hsd]
      intro w hw
      obtain ⟨u, v, rfl⟩ := (mem _).1 hw
      refine ⟨v * k, ?_⟩
      have := EFr (1 / 2) 0 u v
      rw [hk] at this
      push_cast at this ⊢
      rw [show (1 * w₁ + 0 * w₂) / 2 = 1 / 2 * w₁ + 0 * w₂ by ring, this]
      ring
    rw [half] at this
    exact absurd this.1 (by decide)
  obtain ⟨a, b, hab⟩ := (mem _).1 (hst _ hw₁)
  obtain ⟨c, d, hcd⟩ := (mem _).1 (hst _ hw₂)
  obtain ⟨s₁, s₂, hs⟩ := (mem _).1 ht
  obtain ⟨x₁, x₂, rfl⟩ := (mem _).1 hω
  have mul : ∀ x y : ℤ, θ * ((x : ℂ) * w₁ + y * w₂) =
      ((a * x + c * y : ℤ) : ℂ) * w₁ + ((b * x + d * y : ℤ) : ℂ) * w₂ := by
    intro x y
    push_cast
    linear_combination (x : ℂ) * hab + (y : ℂ) * hcd
  obtain ⟨r1, r2⟩ := uniq (a * a + b * c - a + N) (a * b + b * d - b) (by
    push_cast
    linear_combination w₁ * hθ - (θ + a - 1) * hab - (b : ℂ) * hcd)
  obtain ⟨r3, r4⟩ := uniq (c * a + d * c - c) (c * b + d * d - d + N) (by
    push_cast
    linear_combination w₂ * hθ - (θ + d - 1) * hcd - (c : ℂ) * hab)
  have hN2 : (N : ZMod 2) = 0 := ZMod.intCast_eq_zero_iff_even.2 hN
  have q1 := congrArg (Int.cast : ℤ → ZMod 2) r1
  have q2 := congrArg (Int.cast : ℤ → ZMod 2) r2
  have q3 := congrArg (Int.cast : ℤ → ZMod 2) r3
  have q4 := congrArg (Int.cast : ℤ → ZMod 2) r4
  push_cast at q1 q2 q3 q4
  have e1 : θ * t = (((a * s₁ + c * s₂ : ℤ) : ℂ) * w₁ + ((b * s₁ + d * s₂ : ℤ) : ℂ) * w₂) / 2 := by
    rw [← mul, ← hs]; ring
  have e2 : (1 - θ) * t = (((s₁ - (a * s₁ + c * s₂) : ℤ) : ℂ) * w₁ + ((s₂ - (b * s₁ + d * s₂) : ℤ) : ℂ) * w₂) / 2 := by
    push_cast at e1 ⊢
    linear_combination (1 / 2) * hs - e1
  rw [e1, half] at h1
  rw [e2, half] at h2
  push_cast at h1 h2
  refine ⟨_, _, by rw [mul, EFi], by rw [hs, EFi], ?_⟩
  rw [half, ← ZMod.intCast_eq_zero_iff_even]
  push_cast
  rw [hodd, mul_one, mul_one]
  exact parity_mod_two _ _ _ _ _ _ _ _ (by linear_combination q1 - hN2) (by linear_combination q2)
    (by linear_combination q3) (by linear_combination q4 - hN2) h1 h2

theorem theta_signed_translation : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ t0, GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → Differentiable ℂ (GL3Theta.th0 (lamOf D cc δ) t0) ∧ ∀ ω ∈ lamOf D cc δ, ∃ m : ℤ, q1 D (lamOf D cc δ) ω = (m : ℝ) ∧ ∀ z, (-1 : ℂ) ^ m * U1 (lamOf D cc δ) ω (GL3Theta.th0 (lamOf D cc δ) t0) z = GL3Theta.th0 (lamOf D cc δ) t0 z := by
  intro D hG cc δ hC t0 ht
  obtain ⟨hb, -, -, -, hst⟩ := GlobalTheory.CurveLattice.lattice_of_curve D hG cc δ hC
  set Λ := lamOf D cc δ
  obtain ⟨⟨hdiff, -, -, hlaw⟩, -⟩ := GlobalTheory.OddTheta.sgStar_laws Λ hb
  obtain ⟨L, hL⟩ := GlobalTheory.OddTheta.exists_periodPair Λ hb
  obtain ⟨-, hsd⟩ := GlobalTheory.PlaneLattice.area_pos_and_selfDual L Λ hL
  obtain ⟨w₁, w₂, hi, hΛ⟩ := hb
  obtain ⟨a, ha⟩ := GlobalTheory.NormSum.exists_integer_map_eq_w0 D
  have hd : D.host.d % 16 = 7 := D.host.hyp.2.2.2.1
  obtain ⟨k, hk⟩ : ∃ k : ℕ, D.host.d = 16 * k + 7 := ⟨D.host.d / 16, by omega⟩
  have hsq : ((Real.sqrt D.host.d : ℝ) : ℂ) * (Real.sqrt D.host.d : ℝ) = 16 * (k : ℂ) + 7 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _), hk]
    push_cast; ring
  refine ⟨?_, fun ω hω => ?_⟩
  · unfold GL3Theta.th0 U1
    refine Differentiable.div_const (Differentiable.mul (hdiff.comp (differentiable_id.add_const _)) ?_) _
    fun_prop
  obtain ⟨m, n, hm, hn, hpar⟩ := even_im_hermitian_sub Λ w₁ w₂ hi hΛ hsd (w0 D) (4 * k + 2) ⟨2 * k + 1, by ring⟩
    (by
      unfold w0
      push_cast
      linear_combination (((Real.sqrt D.host.d : ℝ) : ℂ) ^ 2 / 4) * Complex.I_mul_I - (1 / 4) * hsq)
    (fun w hw => ha ▸ hst a w hw) t0 ht.1 ht.2.1
    (by
      have := ht.2.2
      convert this using 3
      unfold w0; ring) ω hω
  refine ⟨m, ?_, fun z => ?_⟩
  · rw [← hm, q1, gl3FieldFirst, mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq, w0]
    rw [mul_comm ((1 + _) / 2 : ℂ), Complex.im_ofReal_mul]
    simp
    ring
  · have e1 : U1 Λ ω (GL3Theta.th0 Λ t0) z = U1 Λ ω (U1 Λ t0 (sgStar Λ)) z / U1 Λ t0 (sgStar Λ) 0 := by
      conv_lhs => rw [U1]
      conv_rhs => rw [U1]
      simp only [GL3Theta.th0]
      ring
    have e2 : U1 Λ t0 (U1 Λ ω (sgStar Λ)) z = (if ω / 2 ∈ Λ then 1 else -1) * U1 Λ t0 (sgStar Λ) z := by
      conv_lhs => rw [U1]
      rw [hlaw ω hω, mul_assoc]
      rfl
    have e3 : Complex.exp (-(Real.pi : ℂ) * Complex.I * ((n : ℝ) : ℂ)) = (-1) ^ n := by
      rw [show -(Real.pi : ℂ) * Complex.I * ((n : ℝ) : ℂ) = (n : ℂ) * (-(Real.pi * Complex.I)) by push_cast; ring,
        Complex.exp_int_mul, Complex.exp_neg, Complex.exp_pi_mul_I]
      norm_num
    have e4 : (-1 : ℂ) ^ m * (-1) ^ n * (if ω / 2 ∈ Λ then 1 else -1) = 1 := by
      rw [← zpow_add₀ (by norm_num)]
      split_ifs with h
      · rw [(hpar.2 h).neg_one_zpow]; simp
      · rw [(Int.not_even_iff_odd.1 (mt hpar.1 h)).neg_one_zpow]; simp
    rw [e1, exists_orthonormal_basis_family, hn, e2, e3]
    simp only [GL3Theta.th0]
    linear_combination (U1 Λ t0 (sgStar Λ) z / U1 Λ t0 (sgStar Λ) 0) * e4

end GlobalTheory.HalfPeriodTheta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ImaginaryQuadraticFieldStructure
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.GalTheta
open scoped BigOperators

noncomputable section

namespace GlobalTheory.FourCopies

theorem exists_orthogonal_family {K V : Type} [Field K] [AddCommGroup V] [Module K V] (h : V → V →ₗ[K] K)
    (hsym : ∀ x y, h y x = 0 → h x y = 0) (hdef : ∀ x, h x x = 0 → x = 0) (s : Finset V) :
    ∃ (n : ℕ) (v : Fin n → V), (∀ i, v i ≠ 0) ∧ (∀ i j, i ≠ j → h (v j) (v i) = 0) ∧
      ∀ x ∈ s, x ∈ Submodule.span K (Set.range v) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, by simp⟩
  | insert x s _ ih =>
    obtain ⟨n, v, h0, ho, hs⟩ := ih
    set p : V := ∑ i, (h (v i) x / h (v i) (v i)) • v i with hp
    have hpm : p ∈ Submodule.span K (Set.range v) :=
      sum_mem fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    have hx : ∀ j, h (v j) (x - p) = 0 := by
      intro j
      have hj : h (v j) (v j) ≠ 0 := fun e => h0 j (hdef _ e)
      rw [map_sub, hp, map_sum, Finset.sum_eq_single j]
      · rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hj, sub_self]
      · intro i _ hij
        rw [map_smul, ho i j hij, smul_zero]
      · simp
    by_cases hz : x - p = 0
    · refine ⟨n, v, h0, ho, fun y hy => ?_⟩
      rcases Finset.mem_insert.1 hy with rfl | hy
      · rw [sub_eq_zero.1 hz]; exact hpm
      · exact hs y hy
    · have hle : Submodule.span K (Set.range v) ≤
          Submodule.span K (Set.range (Fin.cons (x - p) v : Fin (n + 1) → V)) :=
        Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨i.succ, by simp⟩)
      refine ⟨n + 1, Fin.cons (x - p) v, fun i => ?_, fun i j hij => ?_, fun y hy => ?_⟩
      · refine Fin.cases ?_ (fun i => ?_) i
        · simpa using hz
        · simpa using h0 i
      · revert hij
        refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;> intro hij
        · exact absurd rfl hij
        · exact hx j
        · exact hsym _ _ (hx i)
        · exact ho i j (fun e => hij (by rw [e]))
      · rcases Finset.mem_insert.1 hy with rfl | hy
        · have := add_mem (Submodule.subset_span (Set.mem_range_self 0)) (hle hpm)
          rwa [Fin.cons_zero, sub_add_cancel] at this
        · exact hle (hs y hy)

theorem exists_similitude (a : ℚ) (ha : 0 < a) :
    ∃ A : Fin 4 → Fin 4 → ℚ, (∀ j j', a * ∑ k, A j k * A j' k = if j = j' then 1 else 0) ∧
      ∀ k k', a * ∑ j, A j k * A j k' = if k = k' then 1 else 0 := by
  obtain ⟨p, q, r, s, h⟩ := Nat.sum_four_squares (a.num.natAbs * a.den)
  have hn : (0 : ℚ) < a.num := by exact_mod_cast Rat.num_pos.2 ha
  have h1 : ((a.num.natAbs : ℕ) : ℚ) = a.num := by
    rw [Nat.cast_natAbs, abs_of_pos (Rat.num_pos.2 ha)]
  have h2 : (p : ℚ) ^ 2 + q ^ 2 + r ^ 2 + s ^ 2 = a.num * a.den := by
    rw [← h1]; exact_mod_cast h
  have h3 : a * a.den = a.num := Rat.mul_den_eq_num a
  obtain ⟨p, q, r, s, h⟩ : ∃ p q r s : ℚ, a * (p ^ 2 + q ^ 2 + r ^ 2 + s ^ 2) = 1 := by
    refine ⟨p / a.num, q / a.num, r / a.num, s / a.num, ?_⟩
    simp only [div_pow, ← add_div, h2]
    field_simp
    linear_combination h3
  refine ⟨![![p, q, r, s], ![-q, p, -s, r], ![-r, s, p, -q], ![-s, -r, q, p]], fun j j' => ?_, fun j j' => ?_⟩ <;>
    fin_cases j <;> fin_cases j' <;> simp [Fin.sum_univ_four] <;>
    first | linear_combination h | (right; ring)

variable (D : D7)

theorem exists_rat_of_real (x : D.host.K) (hx : (D.host.φ₀ (x : D.host.E)).im = 0) : ∃ a : ℚ, x = (a : D.host.K) :=
  by apply _root_.GlobalTheory.RationalOfReal.rat_of_real <;> assumption

theorem exists_rat_pos {N N' : ℕ} (x : Matrix (Fin N') (Fin N) D.host.E) (hx : x ≠ 0) :
    ∃ a : ℚ, 0 < a ∧ hYY D x x = (a : D.host.K) := by
  have hc : ∀ (φ : D.host.E →+* ℂ) (z : D.host.E), φ (D.host.conj z) = starRingEnd ℂ (φ z) :=
    fun φ z => D.host.conjE_apply φ z
  have h : D.host.φ₀ ((hYY D x x : D.host.K) : D.host.E) =
      ((∑ τ, ∑ i, ∑ j, Complex.normSq (embT D τ (x i j)) : ℝ) : ℂ) := by
    unfold hYY
    rw [← (GlobalTheory.InducedType.induced_type D).1.2]
    simp only [map_sum, map_mul, hc, Complex.mul_conj]
    push_cast
    rfl
  obtain ⟨a, ha⟩ := exists_rat_of_real D (hYY D x x) (by rw [h, Complex.ofReal_im])
  refine ⟨a, ?_, ha⟩
  obtain ⟨i, j, hij⟩ : ∃ i j, x i j ≠ 0 := by
    by_contra hh
    push Not at hh
    exact hx (Matrix.ext hh)
  have hpos : 0 < ∑ τ, ∑ i, ∑ j, Complex.normSq (embT D τ (x i j)) := by
    have nn := fun τ i j => Complex.normSq_nonneg (embT D τ (x i j))
    refine Finset.sum_pos' (fun τ _ => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => nn τ i j)
      ⟨D.eTau.symm 1, Finset.mem_univ _, ?_⟩
    refine Finset.sum_pos' (fun i _ => Finset.sum_nonneg fun j _ => nn _ i j) ⟨i, Finset.mem_univ _, ?_⟩
    refine Finset.sum_pos' (fun j _ => nn _ i j) ⟨j, Finset.mem_univ _, ?_⟩
    exact Complex.normSq_pos.2 ((map_ne_zero _).2 hij)
  rw [ha] at h
  have h' : ((a : ℝ) : ℂ) = ((∑ τ, ∑ i, ∑ j, Complex.normSq (embT D τ (x i j)) : ℝ) : ℂ) := by
    rw [← h]; simp
  rw [← Complex.ofReal_injective h'] at hpos
  exact_mod_cast hpos

def cols (N : ℕ) : Fin (N + 3 * N) ≃ Fin 4 × Fin N :=
  (finCongr (by ring)).trans finProdFinEquiv.symm

def blocks {N N' : ℕ} (c : Fin 4 → ℚ) :
    Matrix (Fin N') (Fin N) D.host.E →ₗ[D.host.K] Matrix (Fin N') (Fin (N + 3 * N)) D.host.E where
  toFun v := fun i j => (c (cols N j).1 : D.host.E) * v i (cols N j).2
  map_add' v w := by
    funext i j
    exact mul_add _ _ _
  map_smul' a v := by
    funext i j
    exact mul_smul_comm a _ (v i (cols N j).2)

theorem blocks_apply {N N' : ℕ} (c : Fin 4 → ℚ) (v : Matrix (Fin N') (Fin N) D.host.E) (i j) :
    blocks D c v i j = (c (cols N j).1 : D.host.E) * v i (cols N j).2 := rfl

theorem hYY_blocks {N N' : ℕ} (c c' : Fin 4 → ℚ) (v w : Matrix (Fin N') (Fin N) D.host.E) :
    hYY D (blocks D c v) (blocks D c' w) = ((∑ k, c k * c' k : ℚ) : D.host.K) * hYY D v w := by
  unfold hYY
  rw [← smul_eq_mul ((∑ k, c k * c' k : ℚ) : D.host.K), ← map_smul, Finset.smul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← (cols N).symm.sum_comp, Fintype.sum_prod_type, Algebra.smul_def, map_ratCast]
  simp only [blocks_apply, Equiv.apply_symm_apply, map_mul, map_ratCast]
  push_cast
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring

theorem exists_onB_four : ∀ (D : D7) (N N' : ℕ), ∃ (m r : ℕ) (b : Fin r → Matrix (Fin N') (Fin (N + m)) D.host.E), OnB D b := by
  intro D N N'
  obtain ⟨s, hs⟩ : (⊤ : Submodule D.host.K (Matrix (Fin N') (Fin N) D.host.E)).FG := Module.Finite.fg_top
  obtain ⟨n, v, h0, ho, hsp⟩ := exists_orthogonal_family (hYYLeft D (N := N) (N' := N'))
    (fun x y e => by
      have h1 := hYY_herm D (GlobalTheory.InducedType.induced_type D).1.2 x y
      change hYY D x y = 0 at e
      change hYY D y x = 0
      rw [e] at h1
      simpa using h1)
    (fun x e => by
      by_contra hx
      obtain ⟨a, ha, h1⟩ := exists_rat_pos D x hx
      change hYY D x x = 0 at e
      rw [e] at h1
      exact ha.ne' (by exact_mod_cast h1.symm)) s
  have htop : ∀ x, x ∈ Submodule.span D.host.K (Set.range v) := fun x =>
    (Submodule.span_le.2 (fun y hy => hsp y hy) : Submodule.span D.host.K (s : Set _) ≤ _) (by rw [hs]; trivial)
  choose a ha hav using fun i => exists_rat_pos D (v i) (h0 i)
  choose A hA hA' using fun i => exists_similitude (a i) (ha i)
  let e : Fin (n * 4) ≃ Fin n × Fin 4 := finProdFinEquiv.symm
  refine ⟨3 * N, n * 4, fun l => blocks D (A (e l).1 (e l).2) (v (e l).1), fun l l' => ?_, ?_⟩
  · rw [hYY_blocks]
    by_cases hi : (e l).1 = (e l').1
    · rw [← hi, hav, ← Rat.cast_mul, mul_comm, hA]
      have : (e l).2 = (e l').2 ↔ l = l' := ⟨fun h => e.injective (Prod.ext hi h), fun h => by rw [h]⟩
      simp only [this]
      split_ifs <;> simp
    · have : l ≠ l' := fun h => hi (by rw [h])
      rw [if_neg this, show hYY D (v (e l).1) (v (e l').1) = 0 from ho _ _ hi, mul_zero]
  · set W := Submodule.span D.host.K (Set.range fun l => blocks D (A (e l).1 (e l).2) (v (e l).1)) with hW
    have hb : ∀ i j, blocks D (A i j) (v i) ∈ W := fun i j =>
      Submodule.subset_span ⟨e.symm (i, j), by simp only [Equiv.apply_symm_apply]⟩
    have h1 : ∀ (k : Fin 4) i, blocks D (fun k' => if k = k' then 1 else 0) (v i) ∈ W := by
      intro k i
      have : blocks D (fun k' => if k = k' then 1 else 0) (v i) =
          ∑ j, ((a i * A i j k : ℚ) : D.host.K) • blocks D (A i j) (v i) := by
        funext s t
        simp only [Matrix.sum_apply, Matrix.smul_apply, blocks_apply, Algebra.smul_def, map_ratCast]
        rw [← hA' i]
        push_cast
        rw [Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [this]
      exact sum_mem fun j _ => W.smul_mem _ (hb i j)
    have h2 : ∀ (k : Fin 4) x, blocks D (fun k' => if k = k' then 1 else 0) x ∈ W := by
      intro k x
      have : Submodule.span D.host.K (Set.range v) ≤ W.comap (blocks D fun k' => if k = k' then 1 else 0) :=
        Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact h1 k i)
      exact this (htop x)
    rw [eq_top_iff]
    intro x _
    have : x = ∑ k : Fin 4, blocks D (fun k' => if k = k' then 1 else 0)
        (Matrix.of fun i j => x i ((cols N).symm (k, j))) := by
      funext s t
      simp only [Matrix.sum_apply, blocks_apply, Matrix.of_apply]
      rw [Finset.sum_eq_single (cols N t).1]
      · simp
      · intro k _ hk
        simp [hk]
      · simp
    rw [this]
    exact sum_mem fun k _ => h2 k _

end GlobalTheory.FourCopies
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutesStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inducedType_thetaGenusOne_permutes : ∀ D : D7, admG1 D ∧ EmbeddingPermutesTypes D := by
  first | exact @GlobalTheory.InducedType.induced_type | exact GlobalTheory.InducedType.induced_type | (intros; apply GlobalTheory.InducedType.induced_type <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralCexpGaussianPlane
section
open Complex MeasureTheory GlobalTheory.UnitaryTheta
open scoped BigOperators ComplexConjugate Real Classical

namespace GlobalTheory.UnitaryTheta

theorem integral_cexp_gaussian_plane : ∀ l u v : ℂ, 0 < l.re → Integrable (fun z : ℂ => cexp (-(π : ℂ) * l * (z * conj z) + π * (u * conj z) + π * (z * conj v))) ∧ ∫ z : ℂ, cexp (-(π : ℂ) * l * (z * conj z) + π * (u * conj z) + π * (z * conj v)) = l⁻¹ * cexp (π * (u * conj v) / l) := by
  intro l u v hl
  have hl0 : l ≠ 0 := by
    intro h
    simp [h] at hl
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hb : (-(π : ℂ) * l).re < 0 := by
    have := mul_pos Real.pi_pos hl
    simpa using this
  set f : ℝ → ℂ := fun x => cexp ((-(π : ℂ) * l) * x ^ 2 + (π * (u + conj v)) * x + 0) with hf
  set g : ℝ → ℂ := fun y => cexp ((-(π : ℂ) * l) * y ^ 2 + (π * I * (conj v - u)) * y + 0) with hg
  have hfi : Integrable f := integrable_cexp_quadratic' hb _ _
  have hgi : Integrable g := integrable_cexp_quadratic' hb _ _
  have key : (fun z : ℂ => cexp (-(π : ℂ) * l * (z * conj z) + π * (u * conj z) + π * (z * conj v)))
      = (fun p : ℝ × ℝ => f p.1 * g p.2) ∘ Complex.measurableEquivRealProd := by
    funext z
    simp only [hf, hg, Function.comp, Complex.measurableEquivRealProd_apply, ← Complex.exp_add]
    congr 1
    have hz : z = z.re + z.im * I := (Complex.re_add_im z).symm
    have hc : conj z = z.re - z.im * I := by
      apply Complex.ext <;> simp
    rw [hc]
    generalize (z.re : ℂ) = a at hz ⊢
    generalize (z.im : ℂ) = b at hz ⊢
    subst hz
    linear_combination (π * l * b ^ 2) * Complex.I_sq
  have hmp := Complex.volume_preserving_equiv_real_prod
  refine ⟨?_, ?_⟩
  · rw [key, hmp.integrable_comp_emb Complex.measurableEquivRealProd.measurableEmbedding]
    exact hfi.mul_prod hgi
  · rw [key]
    have h1 := hmp.integral_comp' (fun p : ℝ × ℝ => f p.1 * g p.2)
    simp only [Function.comp_def]
    rw [h1, Measure.volume_eq_prod, integral_prod_mul, hf, hg, integral_cexp_quadratic hb,
      integral_cexp_quadratic hb]
    have h2 : (π : ℂ) / -(-(π : ℂ) * l) = l⁻¹ := by field_simp
    have h3 : (l⁻¹ : ℂ) ^ (1 / 2 : ℂ) * (l⁻¹ : ℂ) ^ (1 / 2 : ℂ) = l⁻¹ := by
      rw [← Complex.cpow_add _ _ (inv_ne_zero hl0)]
      norm_num
    rw [h2, mul_mul_mul_comm, h3, ← Complex.exp_add]
    congr 2
    field_simp
    linear_combination (π * (conj v - u) ^ 2) * Complex.I_sq

end GlobalTheory.UnitaryTheta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralUnfoldFundamentalDomain
section
open Complex MeasureTheory GlobalTheory.UnitaryTheta
open scoped BigOperators ComplexConjugate Real Classical

namespace GlobalTheory

theorem integral_unfold_fundamentalDomain : ∀ (V : Type) [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] (μ : Measure V) [μ.IsAddLeftInvariant] (Λ : AddSubgroup V) [Countable Λ] (Fd : Set V), IsAddFundamentalDomain Λ Fd μ → ∀ g : V → ℂ, Integrable g μ → IntegrableOn (fun z => ∑' y : Λ, g (z + y)) Fd μ ∧ ∫ z in Fd, ∑' y : Λ, g (z + y) ∂μ = ∫ z, g z ∂μ := by
  intro V _ _ _ _ μ _ Λ _ Fd hFd g hg
  have hv : ∀ (y : Λ) (z : V), y +ᵥ z = z + y := fun y z => by
    rw [add_comm]; rfl
  have hm : ∀ y : Λ, AEStronglyMeasurable (fun z => g (z + y)) (μ.restrict Fd) := fun y => by
    have h := (hg.comp_add_left (y : V)).aestronglyMeasurable
    simp only [add_comm (y : V)] at h
    exact h.restrict
  have hfin : ∑' y : Λ, ∫⁻ z in Fd, ‖g (z + y)‖ₑ ∂μ ≠ ⊤ := by
    have h := hFd.lintegral_eq_tsum'' (fun z => ‖g z‖ₑ)
    simp only [hv] at h
    rw [← h]
    exact hg.2.ne
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have : AEMeasurable (fun z => ∑' y : Λ, g (z + y)) (μ.restrict Fd) :=
      AEMeasurable.tsum fun y => (hm y).aemeasurable
    exact this.aestronglyMeasurable
  · refine lt_of_le_of_lt (lintegral_mono fun z => enorm_tsum_le_tsum_enorm) ?_
    rw [lintegral_tsum fun y => (hm y).enorm]
    exact hfin.lt_top
  · rw [integral_tsum hm hfin, hFd.integral_eq_tsum'' g hg]
    simp only [hv]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSSRepOfTraceNondegenerateStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSSRep_of_trace_nondegenerate' : ∀ (Γ K : Type) [Group Γ] [Field K] (a : ℕ) (ρ : Γ →* GL (Fin a) K), (∀ x ∈ Submodule.span K (Set.range fun g => ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K)), (∀ g, (x * ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K)).trace = 0) → x = 0) → IsSSRep ρ := by
  first | exact @GlobalTheory.TraceSemisimple.isSSRep_of_trace_nondegenerate | exact GlobalTheory.TraceSemisimple.isSSRep_of_trace_nondegenerate | (intros; apply GlobalTheory.TraceSemisimple.isSSRep_of_trace_nondegenerate <;> assumption)
end

