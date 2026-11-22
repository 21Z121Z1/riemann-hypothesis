import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0165
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0162
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0075
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0077
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0086
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0161
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0157
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0164
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0006
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0120
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0119
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0145
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0163
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0117
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0040
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0167
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.Chapter

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionHeckeUEqSumSlash
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem sum_exp_fin_div (l : ℕ) (hl : 0 < l) (m : ℕ) :
    ∑ j : Fin l, cexp (2 * π * Complex.I * ((j : ℕ) * m : ℂ) / l) = if l ∣ m then (l : ℂ) else 0 := by
  have hl' : l ≠ 0 := hl.ne'
  set ζ : ℂ := cexp (2 * π * Complex.I / l)
  have hζ : IsPrimitiveRoot ζ l := Complex.isPrimitiveRoot_exp l hl'
  have e : ∀ j : ℕ, cexp (2 * π * Complex.I * ((j : ℂ) * m) / l) = (ζ ^ m) ^ j := by
    intro j
    rw [← pow_mul, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  simp_rw [e]
  rw [Fin.sum_univ_eq_sum_range (fun j => (ζ ^ m) ^ j) l]
  split_ifs with h
  · rw [(hζ.pow_eq_one_iff_dvd m).2 h]
    simp
  · have h1 : ζ ^ m ≠ 1 := fun h' => h ((hζ.pow_eq_one_iff_dvd m).1 h')
    rw [geom_sum_eq h1, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow, sub_self, zero_div]

theorem slz_repU (k l : ℕ) (hk : 1 ≤ k) (hl : 0 < l) (j : Fin l) (f : ℍ → ℂ) (τ : ℍ) :
    slz k (repU l j) f τ = (l : ℂ)⁻¹ * f (ofComplex (((τ : ℂ) + (j : ℕ)) / l)) := by
  have hl' : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  simp [slz, repU, Matrix.det_fin_two_of, pow_succ]
  field_simp
  simp

theorem polyB_Uo (l : ℕ) (a : ℕ → ℂ) (hl : 0 < l) (h : PolyB a) : PolyB (Uo l a) := by
  obtain ⟨C, A, hC⟩ := h
  have C0 : 0 ≤ C := by
    have := hC 0
    simp at this
    linarith [norm_nonneg (a 0)]
  refine ⟨C * (l : ℝ) ^ A, A, fun n => ?_⟩
  have h1 := hC (l * n)
  have hlr : (1 : ℝ) ≤ l := by exact_mod_cast hl
  calc ‖Uo l a n‖ = ‖a (l * n)‖ := rfl
    _ ≤ C * (((l * n : ℕ) : ℝ) + 1) ^ A := h1
    _ ≤ C * ((l : ℝ) * ((n : ℝ) + 1)) ^ A := by
        gcongr
        push_cast
        nlinarith
    _ = C * (l : ℝ) ^ A * ((n : ℝ) + 1) ^ A := by rw [mul_pow]; ring

theorem Uo_qs_sum_slz : ∀ (k l : ℕ) (a : ℕ → ℂ), 1 ≤ k → 0 < l → PolyB a → PolyB (Uo l a) ∧
    ∀ τ : ℍ, qs (Uo l a) τ = ∑ j : Fin l, slz k (repU l j) (qs a) τ := by
  intro k l a hk hl ha
  refine ⟨polyB_Uo l a hl ha, fun τ => ?_⟩
  have hl' : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
  have hpos : ∀ j : Fin l, 0 < (((τ : ℂ) + (j : ℕ)) / l).im := by
    intro j
    rw [Complex.div_natCast_im]
    exact div_pos (by simpa using τ.im_pos) (by exact_mod_cast hl)
  simp_rw [slz_repU k l hk hl _ (qs a) τ]
  have hqs : ∀ j : Fin l, qs a (ofComplex (((τ : ℂ) + (j : ℕ)) / l))
      = ∑' n : ℕ, a n * cexp (2 * π * Complex.I * n * (((τ : ℂ) + (j : ℕ)) / l)) := by
    intro j
    rw [ofComplex_apply_of_im_pos (hpos j)]
    rfl
  simp_rw [hqs]
  have hsum : ∀ j ∈ (Finset.univ : Finset (Fin l)),
      Summable fun n : ℕ => a n * cexp (2 * π * Complex.I * n * (((τ : ℂ) + (j : ℕ)) / l)) :=
    fun j _ => ((GlobalTheory.T.qExpansion_polyGrowth_summable_continuous a ha).1 ⟨_, hpos j⟩).of_norm
  rw [← Finset.mul_sum, ← Summable.tsum_finsetSum hsum]
  have hinner : ∀ n : ℕ, ∑ j : Fin l, a n * cexp (2 * π * Complex.I * n * (((τ : ℂ) + (j : ℕ)) / l))
      = a n * cexp (2 * π * Complex.I * n * τ / l) * (if l ∣ n then (l : ℂ) else 0) := by
    intro n
    rw [← sum_exp_fin_div l hl n, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_assoc (a n), ← Complex.exp_add]
    congr 2
    ring
  simp_rw [hinner, ← tsum_mul_left]
  have hg : Function.Injective (fun m : ℕ => l * m) := fun x y h => Nat.eq_of_mul_eq_mul_left hl h
  rw [← hg.tsum_eq]
  · show ∑' m : ℕ, Uo l a m * cexp (2 * π * Complex.I * m * τ) = _
    refine tsum_congr fun m => ?_
    simp only [Uo, dvd_mul_right, if_true]
    rw [show (2 * π * Complex.I * ((l * m : ℕ) : ℂ) * τ / l : ℂ) = 2 * π * Complex.I * m * τ by
      push_cast
      field_simp]
    field_simp
  · intro n hn
    by_cases hd : l ∣ n
    · exact ⟨n / l, Nat.mul_div_cancel' hd⟩
    · exact (hn (by simp [hd])).elim

end GlobalTheory.EisM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.QNotPthPowInClosureAlgebraicPadicInt
section
open GlobalTheory.K5

namespace GlobalTheory.K5.NotPow

theorem exists_derivation_fix_q_kill_padicInt (p : ℕ) [Fact p.Prime] : ∃ D : Derivation ℤ (O0 p) (O0 p), D (qO p) = qO p ∧
    ∀ r : ℤ_[p], D (algebraMap ℤ_[p] (O0 p) r) = 0 := GlobalTheory.T.exists_qDerivation_completion_Zp p

theorem derExt (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω] (h : IsClo p Ω)
    (D : Derivation ℤ (O0 p) (O0 p)) :
    ∃ E : Derivation ℤ Ω Ω, ∀ x, E (algebraMap (O0 p) Ω x) = algebraMap (O0 p) Ω (D x) :=
  GlobalTheory.T.exists_derivation_extend_padicLaurent_to_closure p Ω h D

theorem derAlg (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω] (h : IsClo p Ω)
    (E : Derivation ℤ Ω Ω) (hE : ∀ r : ℤ_[p], E (algebraMap (O0 p) Ω (algebraMap ℤ_[p] (O0 p) r)) = 0) :
    ∀ x : Ω, IsAlgZp p x → E x = 0 := GlobalTheory.T.derivation_eq_zero_of_isAlgebraicOverPadicIntegers p Ω h E hE

theorem repr (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω] (h : IsClo p Ω) :
    ∀ b ∈ Subfield.closure (Set.range (algebraMap (O0 p) Ω) ∪ {x | IsAlgZp p x}),
    ∃ (n : ℕ) (a : Fin n → Ω) (f : Fin n → O0 p) (g : O0 p), (∀ i, IsAlgZp p (a i)) ∧
      LinearIndependent (O0 p) a ∧ g ≠ 0 ∧
      algebraMap (O0 p) Ω g * b = ∑ i, algebraMap (O0 p) Ω (f i) * a i := by
  intro b hb
  obtain ⟨g₁, hg₁, hy⟩ := GlobalTheory.T.exists_mul_mem_span_algebraicOverPadicIntegers p Ω h b hb
  obtain ⟨n, a, f, g₂, ha, hli, hg₂, he⟩ := GlobalTheory.T.exists_mul_linearIndependent_algebraicOverPadicIntegers p Ω h _ hy
  refine ⟨n, a, f, g₂ * g₁, ha, hli, mul_ne_zero hg₂ hg₁, ?_⟩
  rw [map_mul, mul_assoc, he]

theorem primeP (p : ℕ) [Fact p.Prime] : Prime (p : O0 p) := GlobalTheory.T.prime_natCast_completed_laurent_ring p

theorem splitP (p : ℕ) [Fact p.Prime] : ∀ x : O0 p, x ≠ 0 →
    ∃ (k : ℕ) (y : O0 p), x = (p : O0 p) ^ k * y ∧ ¬ (p : O0 p) ∣ y := GlobalTheory.T.exists_eq_prime_pow_mul_not_dvd_O0 p

theorem not_eigen (p : ℕ) [Fact p.Prime] (D : Derivation ℤ (O0 p) (O0 p)) (f g : O0 p)
    (hf : f ≠ 0) (hg : g ≠ 0) : (p : O0 p) * (g * D f - f * D g) ≠ g * f := by
  intro heq
  obtain ⟨a, f0, rfl, hf0⟩ := splitP p f hf
  obtain ⟨c, g0, rfl, hg0⟩ := splitP p g hg
  have hD : ∀ (k : ℕ) (y : O0 p), D ((p : O0 p) ^ k * y) = (p : O0 p) ^ k * D y := by
    intro k y
    rw [Derivation.leibniz, Derivation.leibniz_pow]
    have : D (p : O0 p) = 0 := by
      have := D.map_algebraMap (p : ℤ)
      simpa using this
    simp [this]
  rw [hD, hD] at heq
  have hp0 : (p : O0 p) ≠ 0 := (primeP p).ne_zero
  have h2 : (p : O0 p) ^ (c + a) * ((p : O0 p) * (g0 * D f0 - f0 * D g0)) =
      (p : O0 p) ^ (c + a) * (g0 * f0) := by
    rw [pow_add]; linear_combination heq
  have h3 := mul_left_cancel₀ (pow_ne_zero _ hp0) h2
  have h4 : (p : O0 p) ∣ g0 * f0 := ⟨_, h3.symm⟩
  rcases (primeP p).dvd_or_dvd h4 with h | h
  · exact hg0 h
  · exact hf0 h

theorem q_not_pow : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ b ∈ Subfield.closure (Set.range (algebraMap (O0 p) Ω) ∪ {x | IsAlgZp p x}),
      b ^ p ≠ algebraMap (O0 p) Ω (qO p) := by
  intro p _ Ω _ _ h b hb hbp
  have hp : p.Prime := Fact.out
  haveI : CharZero Ω := Basic.charZero_of_isClo h
  obtain ⟨D, hDq, hDr⟩ := exists_derivation_fix_q_kill_padicInt p
  obtain ⟨E, hE⟩ := derExt p Ω h D
  have hEr : ∀ r : ℤ_[p], E (algebraMap (O0 p) Ω (algebraMap ℤ_[p] (O0 p) r)) = 0 := by
    intro r; rw [hE, hDr, map_zero]
  have hEa := derAlg p Ω h E hEr
  have hq0 : algebraMap (O0 p) Ω (qO p) ≠ 0 :=
    ((Basic.isUnit_qO p).map (algebraMap (O0 p) Ω)).ne_zero
  have hb0 : b ≠ 0 := by
    rintro rfl; rw [zero_pow hp.ne_zero] at hbp; exact hq0 hbp.symm
  have hpΩ : (p : Ω) ≠ 0 := by exact_mod_cast hp.ne_zero

  have hEb : (p : Ω) * E b = b := by
    have h1 := congrArg E hbp
    rw [Derivation.leibniz_pow, hE, hDq, ← hbp] at h1
    have h2 : b ^ (p - 1) * ((p : Ω) * E b) = b ^ (p - 1) * b := by
      rw [← pow_succ, Nat.sub_add_cancel hp.one_lt.le]
      rw [nsmul_eq_mul, smul_eq_mul] at h1
      linear_combination h1
    exact mul_left_cancel₀ (pow_ne_zero _ hb0) h2
  obtain ⟨n, a, f, g, ha, hli, hg, hrep⟩ := repr p Ω h b hb
  set φ := algebraMap (O0 p) Ω with hφ
  have hEsum := congrArg E hrep
  rw [Derivation.leibniz, map_sum] at hEsum
  simp only [Derivation.leibniz, hEa _ (ha _), smul_zero, zero_add, smul_eq_mul, hE, mul_zero] at hEsum
  let c : Fin n → O0 p := fun i => g * f i + (p : O0 p) * D g * f i - (p : O0 p) * g * D (f i)

  have hc : ∑ i, c i • a i = 0 := by
    simp only [c, Algebra.smul_def, ← hφ, map_add, map_sub, map_mul, map_natCast]
    have e1 : ∑ i, (φ g * φ (f i) + (p : Ω) * φ (D g) * φ (f i) - (p : Ω) * φ g * φ (D (f i))) * a i
        = (φ g + (p : Ω) * φ (D g)) * ∑ i, φ (f i) * a i - (p : Ω) * φ g * ∑ i, a i * φ (D (f i)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => by ring
    rw [e1, ← hrep, ← hEsum]
    linear_combination -(φ g * φ g) * hEb
  have hc' := (Fintype.linearIndependent_iff.1 hli) c hc
  have : ∃ i, f i ≠ 0 := by
    by_contra hall
    push_neg at hall
    apply hb0
    have : φ g * b = 0 := by rw [hrep]; simp [hall]
    rcases mul_eq_zero.1 this with h0 | h0
    · exact absurd (h.inj (by rw [h0, map_zero])) hg
    · exact h0
  obtain ⟨i, hi⟩ := this
  apply not_eigen p D (f i) g hi hg
  have := hc' i
  simp only [c] at this
  linear_combination -this

end GlobalTheory.K5.NotPow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RegularizedEisensteinLatticeSumDilate
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM Filter Topology
open scoped MatrixGroups Real ComplexConjugate

namespace GlobalTheory.EisM

theorem dif_comp_add (L : ℕ) (ι : ℤ × ℤ → ℤ × ℤ) (hι : ∀ x v : ℤ × ℤ, ∀ r : ℤ, ι (x + r • v) = ι x + r • ι v)
    (v : ℤ × ℤ) (F : ℤ × ℤ → ℂ) :
    dif L v (fun y => F (ι y)) = fun x => dif L (ι v) F (ι x) := by
  funext x
  simp only [dif, hι]

theorem lat_dilate : ∀ (j L N : ℕ) (v : ℤ × ℤ) (Φ : ℤ × ℤ → ℂ) (τ τ' : ℍ), 0 < N → (τ' : ℂ) = N * τ →
    lat j 0 L v Φ τ' = lat j 0 L ((N : ℤ) * v.1, v.2) (fun y => if (N : ℤ) ∣ y.1 then Φ (y.1 / N, y.2) else 0) τ := by
  intro j L N v Φ τ τ' hN hτ
  set ι : ℤ × ℤ → ℤ × ℤ := fun x => ((N : ℤ) * x.1, x.2) with hιdef
  have hN' : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
  have hinj : Function.Injective ι := by
    intro a b h
    simp only [hιdef, Prod.mk.injEq] at h
    exact Prod.ext (mul_left_cancel₀ hN' h.1) h.2
  have hι : ∀ x v : ℤ × ℤ, ∀ r : ℤ, ι (x + r • v) = ι x + r • ι v := by
    intro x v r
    simp only [hιdef, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.mk_add_mk,
      Prod.smul_mk]
    ext <;> simp only <;> ring
  set T : ℤ × ℤ → ℂ := fun y => trm j 0 ((y.1 : ℂ) * τ + y.2) with hT
  have hG : (fun y : ℤ × ℤ => trm j 0 ((y.1 : ℂ) * (τ' : ℂ) + y.2)) = fun y => T (ι y) := by
    funext y
    simp only [hT, hιdef, hτ]
    congr 1
    push_cast
    ring
  have hvι : ι v = ((N : ℤ) * v.1, v.2) := rfl
  have hdd : ∀ x, dif L v (dif L v fun y => trm j 0 ((y.1 : ℂ) * (τ' : ℂ) + y.2)) x =
      dif L (ι v) (dif L (ι v) T) (ι x) := by
    intro x
    rw [hG, dif_comp_add L ι hι, dif_comp_add L ι hι]
  set Ψ : ℤ × ℤ → ℂ := fun y => if (N : ℤ) ∣ y.1 then Φ (y.1 / N, y.2) else 0 with hΨ
  have hΨι : ∀ x, Ψ (ι x) = Φ x := by
    intro x
    simp only [hΨ, hιdef, dvd_mul_right, if_true, Int.mul_ediv_cancel_left _ hN']
  unfold lat
  rw [← hvι]
  simp_rw [hdd]
  set D := dif L (ι v) (dif L (ι v) T) with hD
  have key : (fun x => Φ x * D (ι x)) = fun x => (fun y => Ψ y * D y) (ι x) := by
    funext x; simp only [hΨι]
  rw [key]
  refine hinj.tsum_eq (f := fun y => Ψ y * D y) ?_
  intro y hy
  simp only [Function.mem_support] at hy
  by_cases h : (N : ℤ) ∣ y.1
  · obtain ⟨c, hc⟩ := h
    exact ⟨(c, y.2), by simp only [hιdef]; exact Prod.ext hc.symm rfl⟩
  · exact absurd (by simp only [hΨ, h, if_false, zero_mul]) hy

end GlobalTheory.EisM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RightGamma0CosetDecompositionAdjugateHeckeT
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem adjugate_mem_intMatricesDetLowerLeftDvd {L q : ℕ} {δ : M2} (h : δ ∈ DT L q) : δ.adjugate ∈ DT L q := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · rw [Matrix.det_adjugate]; simpa using h1
  · rw [Matrix.adjugate_fin_two]; simpa using h2

theorem intMatrixTwo_adjugate_adjugate (δ : M2) : δ.adjugate.adjugate = δ := by
  rw [Matrix.adjugate_fin_two, Matrix.adjugate_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem rrep_DT_adj_repT : ∀ L q : ℕ, q.Prime → ¬ q ∣ L →
    RRep L (DT L q) (fun i => (repT q i).adjugate) := by
  intro L q hq hqL
  have hL := GlobalTheory.T.isLeftGamma0CosetDecomposition_heckeRepTOperator L q hq hqL
  unfold LRep at hL
  unfold RRep
  let φ : Option (Fin q) × Gamma0 L → Gamma0 L × Option (Fin q) := fun p => (p.2⁻¹, p.1)
  have hφ : Set.BijOn φ Set.univ Set.univ := by
    rw [Set.bijOn_univ]
    refine ⟨fun a b h => ?_, fun b => ⟨(b.2, b.1⁻¹), by simp [φ]⟩⟩
    simp only [φ, Prod.mk.injEq, inv_inj] at h
    exact Prod.ext h.2 h.1
  have hA : Set.BijOn (fun δ : M2 => δ.adjugate) (DT L q) (DT L q) :=
    Set.InvOn.bijOn ⟨fun δ _ => intMatrixTwo_adjugate_adjugate δ, fun δ _ => intMatrixTwo_adjugate_adjugate δ⟩
      (fun δ h => adjugate_mem_intMatricesDetLowerLeftDvd h) (fun δ h => adjugate_mem_intMatricesDetLowerLeftDvd h)
  have hc := hA.comp (hL.comp hφ)
  convert hc using 1
  funext p
  simp only [Function.comp, φ]
  rw [Matrix.adjugate_mul_distrib]
  congr 1
  rw [Subgroup.coe_inv, ← Matrix.SpecialLinearGroup.coe_inv, inv_inv]

end GlobalTheory.EisM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SaturationLevelFunctionsIntegralRelation
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN.Sat

theorem mdiff_comp_sl (f : ℍ → ℂ) (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (γ : SL(2, ℤ)) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => f (γ • τ)) := by
  have hg : 0 < ((γ : GL (Fin 2) ℝ)).det.val := by simp
  exact hf.comp (UpperHalfPlane.mdifferentiable_smul hg)

theorem gamma_le {K L : ℕ} (hd : K ∣ L) : CongruenceSubgroup.Gamma L ≤ CongruenceSubgroup.Gamma K := by
  intro γ hγ
  have c : ∀ x y : ℤ, ((x : ZMod L) = y) → ((x : ZMod K) = y) := fun x y h => by
    have := congrArg (ZMod.castHom hd (ZMod K)) h
    simpa using this
  rw [CongruenceSubgroup.Gamma_mem] at hγ ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hγ
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using c _ 1 (by simpa using h1)
  · simpa using c _ 0 (by simpa using h2)
  · simpa using c _ 0 (by simpa using h3)
  · simpa using c _ 1 (by simpa using h4)

theorem alg (m : ℕ) (P : ℕ → ℂ) (x y : ℂ)
    (h : ∑ i ∈ Finset.range (m + 1 + 1), P i * x ^ i * y ^ (m + 1 - i) = 0) :
    (P (m + 1) * x) ^ (m + 1) +
      ∑ j : Fin (m + 1), (P j * P (m + 1) ^ (m - j)) * (P (m + 1) * x) ^ (j : ℕ) * y ^ (m + 1 - j) = 0 := by
  rw [Finset.sum_range_succ, ← Fin.sum_univ_eq_sum_range] at h
  have key : ∀ j : Fin (m + 1), (P j * P (m + 1) ^ (m - j)) * (P (m + 1) * x) ^ (j : ℕ) * y ^ (m + 1 - j) =
      P (m + 1) ^ m * (P j * x ^ (j : ℕ) * y ^ (m + 1 - j)) := by
    intro j
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (Nat.lt_succ_iff.mp j.isLt)
    have e1 : m - j = k := by omega
    have e2 : P (m + 1) ^ m = P (m + 1) ^ k * P (m + 1) ^ (j : ℕ) := by rw [← pow_add]; congr 1; omega
    rw [e1, e2, mul_pow]; ring
  rw [Finset.sum_congr rfl (fun j _ => key j), ← Finset.mul_sum]
  have : (P (m + 1) * x) ^ (m + 1) = P (m + 1) ^ m * (P (m + 1) * x ^ (m + 1) * y ^ (m + 1 - (m + 1))) := by
    simp only [Nat.sub_self, pow_zero, mul_one]; ring
  rw [this]
  linear_combination (P (m + 1) ^ m) * h

theorem sat : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (M n : ℕ) (a b : ℍ → ℂ) (p : ℕ → ℍ → ℂ), 0 < M → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) a → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) b → b ≠ 0 → (∀ γ ∈ CongruenceSubgroup.Gamma M, ∀ τ : ℍ, a (γ • τ) * b τ = a τ * b (γ • τ)) → (∀ i, InR ε.range (p i)) → p n ≠ 0 → (∀ τ, ∑ i ∈ Finset.range (n + 1), p i τ * a τ ^ i * b τ ^ (n - i) = 0) → ∃ h : ℍ → ℂ, InR ε.range h ∧ ∀ τ, p n τ * a τ = h τ * b τ := by
  intro Ω _ _ ε M n a b p hM ha hb hb0 hab hp hpn heq
  obtain ⟨-, hiff, -, -, hmem⟩ := GlobalTheory.T.upperHalfPlane_germ_ringHom_and_restrict
  have hring := GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver ε.range
  have inR_mul : ∀ f g : ℍ → ℂ, InR ε.range f → InR ε.range g → InR ε.range (f * g) := fun f g hf hg =>
    (hring.1 _).1 (Subring.mul_mem _ ((hring.1 _).2 hf) ((hring.1 _).2 hg))
  have inR_pow : ∀ (f : ℍ → ℂ) (k : ℕ), InR ε.range f → InR ε.range (f ^ k) := fun f k hf =>
    (hring.1 _).1 (Subring.pow_mem _ ((hring.1 _).2 hf) k)
  have hol : ∀ i, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (p i) := fun i => GlobalTheory.T.mdifferentiable_of_hasSomeLevelOver _ _ (hp i)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := by
    rcases n with _ | m
    · exfalso; apply hpn; funext τ; have := heq τ; simpa using this
    · exact ⟨m, rfl⟩
  have hHs : IsOpen Hs := by
    show IsOpen {z : ℂ | 0 < z.im}; exact isOpen_lt continuous_const Complex.continuous_im
  have hHc : IsPreconnected Hs := by
    apply Convex.isPreconnected
    show Convex ℝ {z : ℂ | 0 < z.im}
    intro x hx y hy s t hs ht hst
    simp only [Set.mem_setOf_eq, Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero] at hx hy ⊢
    rcases hs.eq_or_lt with rfl | hs'
    · simp at hst; subst hst; simpa using hy
    · nlinarith [mul_pos hs' hx, mul_nonneg ht hy.le]
  have dOn : ∀ f : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f → DifferentiableOn ℂ (up f) Hs := fun f hf => (hiff f).1 hf
  have upc : ∀ (f : ℍ → ℂ) (τ : ℍ), up f (τ : ℂ) = f τ := fun f τ => by
    simp only [up, UpperHalfPlane.ofComplex_apply]
  obtain ⟨τ0, hτ0⟩ : ∃ τ, b τ ≠ 0 := by
    by_contra hc; push_neg at hc; exact hb0 (funext hc)
  obtain ⟨h', hh'd, hAD, hmon⟩ := GlobalTheory.T.exists_differentiableOn_quotient_of_integral Hs (m + 1) (fun z => up (p (m + 1)) z * up a z) (up b)
    (fun j z => up (p j) z * up (p (m + 1)) z ^ (m - j)) hHs hHc
    ((dOn _ (hol _)).mul (dOn _ ha)) (dOn _ hb) (fun j => (dOn _ (hol _)).mul ((dOn _ (hol _)).pow _))
    ⟨τ0, hmem τ0, by rw [upc]; exact hτ0⟩
    (fun z _ => alg m (fun i => p i (UpperHalfPlane.ofComplex z)) (a (UpperHalfPlane.ofComplex z))
      (b (UpperHalfPlane.ofComplex z)) (heq _))
  set h : ℍ → ℂ := fun τ => h' τ with hh
  have hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h := by
    rw [hiff]
    refine hh'd.congr fun z hz => ?_
    show h' (UpperHalfPlane.ofComplex z : ℂ) = h' z
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz]
  have hPA : ∀ τ, p (m + 1) τ * a τ = h τ * b τ := fun τ => by
    have := hAD τ (hmem τ); simpa only [upc] using this
  obtain ⟨N, w, hN, hLv, -⟩ := hp (m + 1)
  have hinv : ∀ γ ∈ CongruenceSubgroup.Gamma (M * N), ∀ τ : ℍ, h (γ • τ) = h τ := by
    intro γ hγ
    have hγM := gamma_le (Dvd.intro N rfl) hγ
    have hγN := gamma_le (Dvd.intro_left M rfl) hγ
    have hprod : ∀ τ, (fun τ => h (γ • τ) - h τ) τ * (fun τ => b τ * b (γ • τ)) τ = 0 := by
      intro τ
      have E1 := hPA (γ • τ)
      have E2 := hPA τ
      have E3 := hLv γ hγN τ
      have E4 := hab γ hγM τ
      simp only
      linear_combination (-(b τ)) * E1 + b (γ • τ) * E2 + (a (γ • τ) * b τ) * E3 + p (m + 1) τ * E4
    rcases GlobalTheory.T.upperHalfPlane_holomorphic_mul_eq_zero_iff _ _ ((mdiff_comp_sl h hhol γ).sub hhol) (hb.mul (mdiff_comp_sl b hb γ)) hprod with h0 | h0
    · intro τ; have := congrFun h0 τ; simpa [sub_eq_zero] using this
    · exfalso
      have hbb : ∀ τ, b τ * (fun τ => b (γ • τ)) τ = 0 := fun τ => congrFun h0 τ
      rcases GlobalTheory.T.upperHalfPlane_holomorphic_mul_eq_zero_iff _ _ hb (mdiff_comp_sl b hb γ) hbb with h1 | h1
      · exact hb0 h1
      · apply hτ0
        have := congrFun h1 (γ⁻¹ • τ0)
        simpa using this
  refine ⟨h, ?_, hPA⟩
  refine GlobalTheory.T.hasSomeLevelOver_of_integral_invariant Ω ε (M * N) (m + 1) h (fun j τ => p j τ * p (m + 1) τ ^ (m - j)) (Nat.mul_pos hM hN)
    hhol hinv (fun j => inR_mul _ _ (hp _) (inR_pow _ _ (hp _))) ?_
  intro τ
  have := hmon τ (hmem τ)
  simpa only [upc] using this

end GlobalTheory.FN.Sat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TsenTheorem
section
open GlobalTheory.NeedB Polynomial

namespace GlobalTheory.NeedB

theorem tsen : Tsen := by
  intro k K _ _ _ _ _
  exact GlobalTheory.T.isFirstChernClass_of_finiteDimensional_of_forms_have_zeros (RatFunc k) K (GlobalTheory.T.exists_common_zero_homogeneous_ratFunc_of_mul_lt k)

end GlobalTheory.NeedB
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ZsEqMulDepEisStatement
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zs_monomial_ratio_eq_mul_dep_eis : ∀ (k l j : ℕ) (u v A A' : ℤ → ℂ) (c c' : ℂ), j + 2 ≤ k → Zs k l u v (fun x y => A x * A' y * ((y : ℂ) / x) ^ j) = mul (dep l (eis (k - 1 - j) c A u)) (dep l (eis (j + 1) c' (fun y => A' y * v y) fun _ => 1)) := by
  first | exact @GlobalTheory.zs_eq_mul_dep_eis | exact GlobalTheory.zs_eq_mul_dep_eis | (intros; apply GlobalTheory.zs_eq_mul_dep_eis <;> assumption)
end

