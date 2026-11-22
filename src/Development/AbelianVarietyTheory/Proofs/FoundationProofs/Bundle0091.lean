import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0006
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0046
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0086
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0082
import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0074

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AdjoinStableAndCommutes
section
namespace GlobalTheory.AdjoinStableCommutes

theorem adjoin_stable_and_commutes {E V G : Type} [Field E] [AddCommGroup V] [Module E V]
    (A : Set GlobalTheory.KZ.Letter) (f : GlobalTheory.KZ.Letter → Module.End E V) (W : Submodule E V)
    (g : G → Module.End E V)
    (hW : ∀ T ∈ A, ∀ x ∈ W, f T x ∈ W)
    (hg : ∀ T ∈ A, ∀ (s : G), ∀ x ∈ W, f T (g s x) = g s (f T x)) :
    ∀ Q ∈ Algebra.adjoin E (FreeAlgebra.ι E '' A), ∀ x ∈ W,
      (FreeAlgebra.lift E f Q) x ∈ W ∧
        ∀ s : G, g s ((FreeAlgebra.lift E f Q) x) = (FreeAlgebra.lift E f Q) (g s x) := by
  intro Q hQ
  induction hQ using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨T, hT, rfl⟩ := hy
    intro x hx
    rw [FreeAlgebra.lift_ι_apply]
    exact ⟨hW T hT x hx, fun s => (hg T hT s x hx).symm⟩
  | algebraMap r =>
    intro x hx
    rw [AlgHom.commutes]
    refine ⟨?_, fun s => ?_⟩
    · rw [Module.algebraMap_end_apply]
      exact W.smul_mem r hx
    · rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply, map_smul]
  | add a b _ _ ha hb =>
    intro x hx
    rw [map_add]
    refine ⟨?_, fun s => ?_⟩
    · rw [LinearMap.add_apply]
      exact W.add_mem (ha x hx).1 (hb x hx).1
    · rw [LinearMap.add_apply, LinearMap.add_apply, map_add, (ha x hx).2 s, (hb x hx).2 s]
  | mul a b _ _ ha hb =>
    intro x hx
    rw [map_mul]
    refine ⟨?_, fun s => ?_⟩
    · rw [Module.End.mul_apply]
      exact (ha _ (hb x hx).1).1
    · rw [Module.End.mul_apply, Module.End.mul_apply, (ha _ (hb x hx).1).2 s, (hb x hx).2 s]

end GlobalTheory.AdjoinStableCommutes
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlgebraicSubringClosureCommonDenominator
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory

theorem finite_subring_common_denominator :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [Algebra.IsAlgebraic ℚ Ω] (S : Finset Ω),
      ∃ D : ℕ, 0 < D ∧ ∀ x ∈ Subring.closure (S : Set Ω),
        ∃ k : ℕ, IsIntegral ℤ ((D : Ω) ^ k * x) := by
  intro Ω _ _ _ S
  have hZQ : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
  have hZ : Algebra.IsAlgebraic ℤ Ω := Algebra.IsAlgebraic.trans ℤ ℚ Ω
  obtain ⟨y, hy0, hy⟩ := Algebra.IsAlgebraic.exists_integral_multiples (R := ℤ) S
  set D : ℕ := y.natAbs with hDdef
  refine ⟨D, Int.natAbs_pos.mpr hy0, ?_⟩
  have hDint : ∀ j : ℕ, IsIntegral ℤ ((D : Ω) ^ j) := by
    intro j
    have h : ((D : Ω) ^ j) = algebraMap ℤ Ω ((D : ℤ) ^ j) := by simp
    rw [h]
    exact isIntegral_algebraMap
  let T : Subring Ω :=
    { carrier := {x | ∃ k : ℕ, IsIntegral ℤ ((D : Ω) ^ k * x)}
      mul_mem' := by
        rintro a b ⟨i, hi⟩ ⟨j, hj⟩
        refine ⟨i + j, ?_⟩
        have : (D : Ω) ^ (i + j) * (a * b) = ((D : Ω) ^ i * a) * ((D : Ω) ^ j * b) := by ring
        rw [this]; exact hi.mul hj
      one_mem' := ⟨0, by simpa using (isIntegral_one : IsIntegral ℤ (1 : Ω))⟩
      add_mem' := by
        rintro a b ⟨i, hi⟩ ⟨j, hj⟩
        refine ⟨i + j, ?_⟩
        have : (D : Ω) ^ (i + j) * (a + b) =
            (D : Ω) ^ j * ((D : Ω) ^ i * a) + (D : Ω) ^ i * ((D : Ω) ^ j * b) := by ring
        rw [this]; exact ((hDint j).mul hi).add ((hDint i).mul hj)
      zero_mem' := ⟨0, by simpa using (isIntegral_zero : IsIntegral ℤ (0 : Ω))⟩
      neg_mem' := by
        rintro a ⟨i, hi⟩
        refine ⟨i, ?_⟩
        have : (D : Ω) ^ i * -a = -((D : Ω) ^ i * a) := by ring
        rw [this]; exact hi.neg }
  have hST : (S : Set Ω) ⊆ T := by
    intro x hx
    refine ⟨1, ?_⟩
    have hx' := hy x hx
    rw [pow_one]
    rcases Int.natAbs_eq y with h | h
    · have e : y • x = (D : Ω) * x := by
        rw [zsmul_eq_mul]; congr 1; rw [h]; simp [hDdef]
      rw [← e]; exact hx'
    · have e : y • x = -((D : Ω) * x) := by
        rw [zsmul_eq_mul, h]; simp [hDdef]
      have := hx'.neg
      rw [e, neg_neg] at this
      exact this
  intro x hx
  exact (Subring.closure_le.mpr hST) hx

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlmostDualTraceDerivationMemSpanValuesStatement
section
open GlobalTheory.AlmostEt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.almostDualTrace_derivation_mem_span_values : ∀ (A S M : Type) [CommRing A] [CommRing S] [Algebra A S] [AddCommGroup M] [Module S M] (B C : Subalgebra A S) (tr : S → S) (n : ℕ) (a b : Fin n → S) (e : S), IsTrData B C tr a b e → ∀ D : S → M, IsDerOn C D → ∀ x ∈ C, (e * e) • D x ∈ Submodule.span S (D '' (B : Set S)) := by
  first | exact @GlobalTheory.AlmostEt.derOn_mem_span_of_trData | exact GlobalTheory.AlmostEt.derOn_mem_span_of_trData | (intros; apply GlobalTheory.AlmostEt.derOn_mem_span_of_trData <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AnMeromorphicAtUpperHalfPlaneStatement
section
open Matrix GlobalTheory.KZ
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.an_meromorphicAt_upperHalfPlane : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (x : X.K) (φ : ℂ → ℂ), X.an x = (φ : Mero) → ∀ τ : ℂ, τ ∈ Hs → MeromorphicAt φ τ ∧ (x ≠ 0 → meromorphicOrderAt φ τ ≠ ⊤) := by
  first | exact @GlobalTheory.KZ.Tower.an_meromorphicAt | exact GlobalTheory.KZ.Tower.an_meromorphicAt | (intros; apply GlobalTheory.KZ.Tower.an_meromorphicAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ApproxPthRootFixedSubfieldOfAlmostEtale
section
open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

theorem approxRoot_fix_of_almostSep : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ),
    p.Prime → 0 < v (p : L) → v (p : L) < 1 → ∀ (G : Type) [Group G] [MulSemiringAction G L],
    (∀ (g : G) (x : L), v (g • x) = v x) → ∀ N : Subgroup G, N.FiniteIndex → AlmostSep v N →
    ApproxRoot p v (Fix L (⊤ : Subgroup G)) → ApproxRoot p v (Fix L N) := by
  intro L _ v p hp hp0 hp1 G _ _ hinv N hN hsep hroot
  haveI : Finite (G ⧸ N) := Subgroup.finite_quotient_of_finiteIndex
  haveI : Fintype (G ⧸ N) := Fintype.ofFinite _
  obtain ⟨θ, hθ1, hθ⟩ := hroot
  set θ₀ : ℝ≥0 := max θ (v (p : L)) with hθ₀
  have hθ₀1 : θ₀ < 1 := max_lt hθ1 hp1
  obtain ⟨s, hs0, hs1⟩ := exists_between hθ₀1
  set r : ℝ≥0 := s ^ (((p + 1 : ℕ) : ℝ)⁻¹) with hr
  have hrpow : r ^ (p + 1) = s := NNReal.rpow_inv_natCast_pow s (by omega)
  have hr1 : r < 1 := NNReal.rpow_lt_one hs1 (by positivity)
  have hrs : θ₀ < r ^ (p + 1) := hrpow ▸ hs0
  have hrpos : 0 < r ^ (p + 1) := lt_of_le_of_lt bot_le hrs
  obtain ⟨n, a, b, c, hc, hrc⟩ := hsep r hr1
  refine ⟨θ₀ / r ^ (p + 1), (div_lt_one hrpos).2 hrs, ?_⟩
  intro x hx
  by_cases hx0 : x = 0
  · refine ⟨0, zero_mem _, ?_⟩
    simp [hx0, hp.ne_zero]
  obtain ⟨d, hdF, hd0, hdr, hd1⟩ :=
    GlobalTheory.T.exists_pth_power_scale_thin_shell L v p hp _ ⟨θ, hθ1, hθ⟩ hp0 hp1 r hr1 x hx0
  have hdN : d ∈ Fix L N := fun σ => hdF ⟨σ.1, Subgroup.mem_top _⟩
  have hx'N : x * d ^ p ∈ Fix L N := mul_mem hx (pow_mem hdN p)
  obtain ⟨w, hwN, hw⟩ :=
    GlobalTheory.T.pow_mul_approx_pow_of_almostEtaleSeparatingFamily L v p hp G hinv N θ hθ1.le hθ n a b c hc (x * d ^ p) hx'N hd1
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, map_zero] at hrc
    exact (not_lt.2 (bot_le : (⊥ : ℝ≥0) ≤ r)) hrc
  refine ⟨w / (c * d), div_mem hwN (mul_mem hc.c_mem hdN), ?_⟩
  have key : x - (w / (c * d)) ^ p = (c ^ p * (x * d ^ p) - w ^ p) / (c ^ p * d ^ p) := by
    have hD0 : c ^ p * d ^ p ≠ 0 := mul_ne_zero (pow_ne_zero _ hc0) (pow_ne_zero _ hd0)
    rw [eq_div_iff hD0, div_pow, mul_pow, sub_mul, div_mul_cancel₀ _ (mul_ne_zero (pow_ne_zero _ hc0) (pow_ne_zero _ hd0))]
    ring
  have hD : 0 < v (c ^ p * d ^ p) := by
    rw [Valuation.pos_iff]
    exact mul_ne_zero (pow_ne_zero _ hc0) (pow_ne_zero _ hd0)
  rw [key, map_div₀, div_le_iff₀ hD]
  have hvx : v (x * d ^ p) = v x * v d ^ p := by rw [map_mul, map_pow]
  have hbig : r ^ (p + 1) ≤ v c ^ p * (v x * v d ^ p) := by
    rw [pow_succ, ← hvx]
    exact mul_le_mul' (pow_le_pow_left₀ bot_le hrc.le p) hdr.le
  calc v (c ^ p * (x * d ^ p) - w ^ p) ≤ θ₀ := hw
    _ = θ₀ / r ^ (p + 1) * r ^ (p + 1) := (div_mul_cancel₀ _ hrpos.ne').symm
    _ ≤ θ₀ / r ^ (p + 1) * (v c ^ p * (v x * v d ^ p)) := by gcongr
    _ = θ₀ / r ^ (p + 1) * v x * v (c ^ p * d ^ p) := by
      rw [map_mul, map_pow, map_pow]; ring

end GlobalTheory.AlmostEt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.BettiFunctionSubMemOfColumnsCongrStatement
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bettiFunction_sub_mem_of_columns_congr : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (N l w : ℕ) [Fact l.Prime] (b : X.Fn l), b ∈ X.B N l w → ∀ (n : ℕ) (u v : Fin 2 → ℤ_[l]), (∀ i, u i - v i ∈ (idl l) ^ n) → b u - b v ∈ (idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Khat l)) := by
  first | exact @GlobalTheory.KZ.Tower.B_sub_mem | exact GlobalTheory.KZ.Tower.B_sub_mem | (intros; apply GlobalTheory.KZ.Tower.B_sub_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.BettiKummerRelationPadicAdd
section
noncomputable section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.BettiB

namespace GlobalTheory.KZ.BettiB.Add

theorem mem_gamma_of_dvd {M N : ℕ} (h : M ∣ N) {δ : SL(2, ℤ)} (hδ : δ ∈ CongruenceSubgroup.Gamma N) :
    δ ∈ CongruenceSubgroup.Gamma M := by
  rw [CongruenceSubgroup.Gamma_mem] at hδ ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hδ
  have e : ∀ x : ℤ, ZMod.castHom h (ZMod M) (x : ZMod N) = (x : ZMod M) := fun x => map_intCast _ x
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← e, h1, map_one]
  · rw [← e, h2, map_zero]
  · rw [← e, h3, map_zero]
  · rw [← e, h4, map_one]

theorem exp_val_add (l n : ℕ) [Fact l.Prime] (x y : ZMod (l ^ n)) :
    Complex.exp (2 * Real.pi * Complex.I * (((x + y).val : ℕ) : ℂ) / ((l : ℂ) ^ n)) =
      Complex.exp (2 * Real.pi * Complex.I * ((x.val : ℕ) : ℂ) / ((l : ℂ) ^ n)) *
        Complex.exp (2 * Real.pi * Complex.I * ((y.val : ℕ) : ℂ) / ((l : ℂ) ^ n)) := by
  have hl : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero n hl⟩
  have hm : (l : ℂ) ^ n ≠ 0 := pow_ne_zero n (Nat.cast_ne_zero.2 hl)
  have hs := Nat.mod_add_div (x.val + y.val) (l ^ n)
  rw [ZMod.val_add, ← Complex.exp_add]
  generalize (x.val + y.val) % l ^ n = r at hs ⊢
  generalize (x.val + y.val) / l ^ n = q at hs
  have hc : (r : ℂ) + (l : ℂ) ^ n * (q : ℂ) = (x.val : ℂ) + (y.val : ℂ) := by exact_mod_cast hs
  have key : 2 * Real.pi * Complex.I * (x.val : ℂ) / (l : ℂ) ^ n + 2 * Real.pi * Complex.I * (y.val : ℂ) / (l : ℂ) ^ n =
      2 * Real.pi * Complex.I * (r : ℂ) / (l : ℂ) ^ n + (q : ℂ) * (2 * Real.pi * Complex.I) := by
    rw [← add_div, ← mul_add, ← hc]
    field_simp
  rw [key, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]

theorem eventually_ne_zero {b : ℂ → ℂ} (hb : DifferentiableOn ℂ b Hs) (h : (b : Mero) ≠ 0) :
    ∀ᶠ z in Filter.codiscreteWithin Hs, b z ≠ 0 := by
  have hopen : IsOpen Hs := isOpen_lt continuous_const Complex.continuous_im
  have hconn : IsPreconnected Hs := (convex_halfSpace_im_gt 0).isPreconnected
  rcases (hb.analyticOnNhd hopen).eqOn_zero_or_eventually_ne_zero_of_preconnected hconn with h0 | h0
  · refine absurd ?_ h
    rw [← Filter.Germ.coe_zero, Filter.Germ.coe_eq]
    filter_upwards [Filter.self_mem_codiscreteWithin Hs] with z hz using h0 hz
  · exact h0

theorem germ_mul_ne_zero {b b' : ℂ → ℂ} (hb : DifferentiableOn ℂ b Hs) (hb' : DifferentiableOn ℂ b' Hs)
    (h : (b : Mero) ≠ 0) (h' : (b' : Mero) ≠ 0) : ((b * b' : ℂ → ℂ) : Mero) ≠ 0 := by
  haveI := hs_codiscrete_neBot
  intro H
  rw [← Filter.Germ.coe_zero, Filter.Germ.coe_eq] at H
  obtain ⟨z, h1, h2, h3⟩ := ((eventually_ne_zero hb h).and ((eventually_ne_zero hb' h').and H)).exists
  exact mul_ne_zero h1 h2 h3

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem cls_mul (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (f f' : X.Kˣ) :
    X.cls l n (f * f') = X.cls l n f + X.cls l n f' := by
  unfold Tower.cls
  rw [ofMul_mul, TensorProduct.tmul_add, Submodule.Quotient.mk_add]

theorem kum_add (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) {x x' : X.Khat l} {χ χ' : SL(2, ℤ) → ZMod (l ^ n)}
    (h : H3.Kum X l n x χ) (h' : H3.Kum X l n x' χ') : H3.Kum X l n (x + x') (χ + χ') := by
  obtain ⟨f, a, b, M, hM, hx, ⟨ha, hb, hb0, hr⟩, hδ⟩ := h
  obtain ⟨f', a', b', M', hM', hx', ⟨ha', hb', hb0', hr'⟩, hδ'⟩ := h'
  refine ⟨f * f', a * a', b * b', M * M', Nat.mul_pos hM hM', ?_,
    ⟨ha.mul ha', hb.mul hb', germ_mul_ne_zero hb hb' hb0 hb0', ?_⟩, ?_⟩
  · rw [map_add, hx, hx', cls_mul]
  · rw [Units.val_mul, map_mul, Filter.Germ.coe_mul, Filter.Germ.coe_mul, mul_pow, mul_pow, ← hr, ← hr']
    ring
  · intro δ hδM z hz
    have e1 := hδ δ (mem_gamma_of_dvd (dvd_mul_right M M') hδM) z hz
    have e2 := hδ' δ (mem_gamma_of_dvd (dvd_mul_left M' M) hδM) z hz
    simp only [Pi.mul_apply, Pi.add_apply]
    rw [exp_val_add]
    linear_combination (a' (mob (ofSL δ) z) * b' z) * e1 +
      (Complex.exp (2 * Real.pi * Complex.I * (((χ δ).val : ℕ) : ℂ) / ((l : ℂ) ^ n)) *
        (a z * b (mob (ofSL δ) z))) * e2

theorem btZ_add : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime]
    (b b' : X.Fn l) (c c' : Gam N l → MvPolynomial (Fin 2) ℤ_[l]),
    BtZ X N l b c → BtZ X N l b' c' → BtZ X N l (b + b') (c + c') := by
  intro Ω _ _ ε X N l _ b b' c c' h h' n u
  obtain ⟨χ, hχ, M, hM, hδ⟩ := h n u
  obtain ⟨χ', hχ', M', hM', hδ'⟩ := h' n u
  refine ⟨χ + χ', kum_add X l n hχ hχ', M * M', Nat.mul_pos hM hM', fun δ hδM => ?_⟩
  have e1 := hδ δ (mem_gamma_of_dvd (dvd_mul_right M M') hδM)
  have e2 := hδ' δ (mem_gamma_of_dvd (dvd_mul_left M' M) hδM)
  simp only [Pi.add_apply, map_add]
  rw [e1, e2]

end GlobalTheory.KZ.BettiB.Add
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.BettiKummerRelationPadicSmul
section
noncomputable section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.BettiB

namespace GlobalTheory.KZ.BettiB

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem smul_cls_eq_cls_pow (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (r : ℤ_[l]) (f : X.Kˣ) :
    r • X.cls l n f = X.cls l n (f ^ (PadicInt.toZModPow n r).val) := by
  have hker : r - ((PadicInt.toZModPow n r).val : ℤ_[l]) ∈ idl l ^ n := by
    rw [Ideal.span_singleton_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker]
    simp
  unfold Tower.cls
  have hk : ∀ (k : ℕ) (y : Additive X.Kˣ), (1 : ℤ_[l]) ⊗ₜ[ℤ] (k • y) = k • ((1 : ℤ_[l]) ⊗ₜ[ℤ] y) :=
    fun k y => map_nsmul (TensorProduct.mk ℤ ℤ_[l] (Additive X.Kˣ) 1) k y
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, ofMul_pow, hk,
    ← Nat.cast_smul_eq_nsmul ℤ_[l], ← sub_smul]
  exact Submodule.smul_mem_smul hker Submodule.mem_top

theorem isRoot_pow (X : Tower Ω ε) {m : ℕ} {f : X.Kˣ} {a b : ℂ → ℂ} (h : H3.IsRoot X m f a b) (k : ℕ) :
    H3.IsRoot X m (f ^ k) (a ^ k) (b ^ k) := by
  obtain ⟨ha, hb, hb0, hab⟩ := h
  refine ⟨ha.pow k, hb.pow k, ?_, ?_⟩
  · intro h0
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · haveI := hs_codiscrete_neBot
      rw [pow_zero] at h0
      exact one_ne_zero (α := Mero) h0
    · apply hb0
      have h1 : (b ^ k) =ᶠ[Filter.codiscreteWithin Hs] 0 := Filter.Germ.coe_eq.1 h0
      have h2 : b =ᶠ[Filter.codiscreteWithin Hs] 0 := by
        filter_upwards [h1] with z hz
        exact pow_eq_zero_iff hk.ne' |>.1 hz
      exact Filter.Germ.coe_eq.2 h2
  · rw [Filter.Germ.coe_pow, Filter.Germ.coe_pow, Units.val_pow_eq_pow_val, map_pow, ← pow_mul, ← pow_mul,
      mul_comm k m, pow_mul, pow_mul, ← mul_pow, hab]

theorem exp_val_mul (l n : ℕ) [Fact l.Prime] (s t : ZMod (l ^ n)) :
    Complex.exp (2 * Real.pi * Complex.I * ((s * t).val : ℂ) / ((l : ℂ) ^ n)) =
      Complex.exp (2 * Real.pi * Complex.I * (t.val : ℂ) / ((l : ℂ) ^ n)) ^ s.val := by
  have hl : (l : ℂ) ^ n ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  rw [← Complex.exp_nat_mul, Complex.exp_eq_exp_iff_exists_int]
  refine ⟨-((s.val * t.val / l ^ n : ℕ) : ℤ), ?_⟩
  have h : (((s * t).val : ℕ) : ℂ) + (l : ℂ) ^ n * ((s.val * t.val / l ^ n : ℕ) : ℂ) = (s.val : ℂ) * t.val := by
    rw [ZMod.val_mul]
    exact_mod_cast Nat.mod_add_div (s.val * t.val) (l ^ n)
  rw [Int.cast_neg, Int.cast_natCast]
  field_simp
  linear_combination h

theorem kum_smul (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (r : ℤ_[l]) {x : X.Khat l}
    {χ : SL(2, ℤ) → ZMod (l ^ n)} (h : H3.Kum X l n x χ) :
    H3.Kum X l n (r • x) (fun δ => PadicInt.toZModPow n r * χ δ) := by
  obtain ⟨f, a, b, M, hM, hx, hroot, hδ⟩ := h
  refine ⟨f ^ (PadicInt.toZModPow n r).val, a ^ (PadicInt.toZModPow n r).val, b ^ (PadicInt.toZModPow n r).val,
    M, hM, ?_, isRoot_pow X hroot _, fun δ hd z hz => ?_⟩
  · rw [map_smul, hx, smul_cls_eq_cls_pow]
  · rw [exp_val_mul]
    simp only [Pi.pow_apply]
    rw [← mul_pow, ← mul_pow, ← mul_pow, hδ δ hd z hz]

theorem btZ_smul (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime] (r : ℤ_[l]) (b : X.Fn l)
    (c : Gam N l → MvPolynomial (Fin 2) ℤ_[l]) (h : BtZ X N l b c) : BtZ X N l (r • b) (r • c) := by
  intro n u
  obtain ⟨χ, hχ, M, hM, hc⟩ := h n u
  refine ⟨fun δ => PadicInt.toZModPow n r * χ δ, kum_smul X l n r hχ, M, hM, fun δ hd => ?_⟩
  have := hc δ hd
  simp only [Pi.smul_apply, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, MvPolynomial.eval_C]
  rw [this]

end GlobalTheory.KZ.BettiB
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.BinaryMonomialDegreeSubstExpansionStatement
section
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.binaryMonomialDegree_subst_expansion : ∀ (R : Type) [CommRing R] (w : ℕ), (∀ (m : Matrix (Fin 2) (Fin 2) ℤ) (k : Fin (w + 1)), slP m (mon R w k) = ∑ i, MvPolynomial.C ((cf w m i k : ℤ) : R) * mon R w i) ∧ (∀ p : MvPolynomial (Fin 2) R, p.IsHomogeneous w → p = ∑ i : Fin (w + 1), MvPolynomial.C (MvPolynomial.coeff (Finsupp.single 0 (i : ℕ) + Finsupp.single 1 (w - (i : ℕ))) p) * mon R w i) ∧ (∀ i, (mon R w i).IsHomogeneous w) ∧ (∀ (u : Fin 2 → R) (i : Fin (w + 1)), MvPolynomial.eval u (mon R w i) = u 0 ^ (i : ℕ) * u 1 ^ (w - (i : ℕ))) ∧ (∀ c : Fin (w + 1) → R, ∑ i, MvPolynomial.C (c i) * mon R w i = 0 → c = 0) := by
  first | exact @GlobalTheory.KZ.H3.mon_expand | exact GlobalTheory.KZ.H3.mon_expand | (intros; apply GlobalTheory.KZ.H3.mon_expand <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.BlockDiagonalPrincipalSeriesCongruenceSubgroupSpStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blockDiagonal_principalSeriesCongruenceSubgroup_split : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (ψ : Fin (r + t) → kˣ →* ℂˣ), Ordered ψ → Cut ψ r → Ordered (fun i => ψ (Fin.castAdd t i)) ∧ Ordered (fun i => ψ (Fin.natAdd r i)) ∧ ∀ (a : GL (Fin r) k) (b : GL (Fin t) k), emb₂ k (stdSum (rfl : r + t = r + t)) (a, b) ∈ grp ψ ↔ a ∈ grp (fun i => ψ (Fin.castAdd t i)) ∧ b ∈ grp (fun i => ψ (Fin.natAdd r i)) := by
  first | exact @GlobalTheory.PsType.block_diag_mem_grp | exact GlobalTheory.PsType.block_diag_mem_grp | (intros; apply GlobalTheory.PsType.block_diag_mem_grp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardGeneralLinearGroupPrimeFieldStatement
section
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_generalLinearGroup_primeField : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), Fintype.card (GG g N) = g ^ (N * (N - 1) / 2) * ∏ i ∈ Finset.range N, (g ^ (i + 1) - 1) := by
  first | exact @GlobalTheory.BadShare.card_GG_eq | exact GlobalTheory.BadShare.card_GG_eq | (intros; apply GlobalTheory.BadShare.card_GG_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardLevelDatumGroupMulPowStatement
section
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_levelDatum_group_mul_pow : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ L : Lev g N, Nat.card {u // L.Mem u} * g ^ (if L.sharp = true then L.k else 0) = g ^ (N * (N - 1) / 2) := by
  first | exact @GlobalTheory.BadShare.lev_card | exact GlobalTheory.BadShare.lev_card | (intros; apply GlobalTheory.BadShare.lev_card <;> assumption)
end

