import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTraceCompatibleTorusEmbeddingStandardTorus
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0234
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0240
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0006

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaIntertwinerPairEqSumCorrespondingRepresenta
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators

namespace GlobalTheory.ThetaConj.IopRepr

theorem mk_eq_iff {V : Type*} [AddCommGroup V] (A₁ A₂ : AddSubgroup V) (a b : A₂) :
    (QuotientAddGroup.mk a : A₂ ⧸ A₁.addSubgroupOf A₂) = QuotientAddGroup.mk b ↔
      (a : V) - (b : V) ∈ A₁ := by
  rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_addSubgroupOf]
  rfl

theorem iop_eq_sum (D : D7) (T : Tor D) {N N' : ℕ} (A₁ A₂ : AddSubgroup (VC D N N'))
    (F : VC D N N' → ℂ) (hF : RepInd D T A₁ A₂ F) {n : ℕ} (x : Fin n → A₂)
    (hx : Function.Bijective
      (fun i => (QuotientAddGroup.mk (x i) : A₂ ⧸ A₁.addSubgroupOf A₂))) :
    Iop D T A₁ A₂ F =
      (fun z => ((Real.sqrt (n : ℝ) : ℝ) : ℂ)⁻¹ * ∑ i, aU D T (x i) F z) := by
  let e := Equiv.ofBijective _ hx
  letI : Fintype (A₂ ⧸ A₁.addSubgroupOf A₂) := Fintype.ofEquiv _ e
  have hn : (A₁.addSubgroupOf A₂).index = n := by
    rw [AddSubgroup.index, ← Nat.card_congr e]; simp
  funext z
  unfold Iop
  rw [hn, finsum_eq_sum_of_fintype, ← e.sum_comp]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : ((Quotient.out (e i) : A₂) : VC D N N') - x i ∈ A₁ := by
    rw [← mk_eq_iff]
    exact Quotient.out_eq (e i)
  exact congrFun (hF _ (Quotient.out (e i) : A₂).2 _ (x i).2 h) z

theorem iop_pair : ∀ (D : D7) (T T' : Tor D) (N N' : ℕ) (A₁ A₂ A₁' A₂' : AddSubgroup (VC D N N')) (F F' : VC D N N' → ℂ) (R : VC D N N' → VC D N N' → Prop), (A₁.addSubgroupOf A₂).FiniteIndex → RepInd D T A₁ A₂ F → RepInd D T' A₁' A₂' F' → (∀ x ∈ A₂, ∃ x' ∈ A₂', R x x') → (∀ x' ∈ A₂', ∃ x ∈ A₂, R x x') → (∀ x x' y y', R x x' → R y y' → (x - y ∈ A₁ ↔ x' - y' ∈ A₁')) → ∃ (n : ℕ) (x x' : Fin n → VC D N N'), (∀ i, x i ∈ A₂ ∧ x' i ∈ A₂' ∧ R (x i) (x' i)) ∧ Iop D T A₁ A₂ F = (fun z => ((Real.sqrt (n : ℝ) : ℝ) : ℂ)⁻¹ * ∑ i, aU D T (x i) F z) ∧ Iop D T' A₁' A₂' F' = (fun z => ((Real.sqrt (n : ℝ) : ℝ) : ℂ)⁻¹ * ∑ i, aU D T' (x' i) F' z) := by
  intro D T T' N N' A₁ A₂ A₁' A₂' F F' R hfin hF hF' h1 h2 h3
  haveI : Finite (A₂ ⧸ A₁.addSubgroupOf A₂) := AddSubgroup.finite_quotient_of_finiteIndex
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin (A₂ ⧸ A₁.addSubgroupOf A₂)
  let x : Fin n → A₂ := fun i => Quotient.out (e.symm i)
  have hxe : ∀ i, (QuotientAddGroup.mk (x i) : A₂ ⧸ A₁.addSubgroupOf A₂) = e.symm i :=
    fun i => Quotient.out_eq _
  have hx : Function.Bijective
      (fun i => (QuotientAddGroup.mk (x i) : A₂ ⧸ A₁.addSubgroupOf A₂)) := by
    have : (fun i => (QuotientAddGroup.mk (x i) : A₂ ⧸ A₁.addSubgroupOf A₂)) = e.symm :=
      funext hxe
    rw [this]; exact e.symm.bijective
  choose y hy hR using fun i => h1 (x i) (x i).2
  let x' : Fin n → A₂' := fun i => ⟨y i, hy i⟩
  have hx' : Function.Bijective
      (fun i => (QuotientAddGroup.mk (x' i) : A₂' ⧸ A₁'.addSubgroupOf A₂')) := by
    constructor
    · intro i j hij
      apply hx.1
      have := (mk_eq_iff _ _ _ _).1 hij
      exact (mk_eq_iff _ _ _ _).2 ((h3 _ _ _ _ (hR i) (hR j)).2 this)
    · intro q
      obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective q
      obtain ⟨a, ha, hab⟩ := h2 b b.2
      obtain ⟨i, hi⟩ := hx.2 (QuotientAddGroup.mk ⟨a, ha⟩)
      refine ⟨i, (mk_eq_iff _ _ _ _).2 ?_⟩
      exact (h3 _ _ _ _ (hR i) hab).1 ((mk_eq_iff _ _ _ _).1 hi)
  exact ⟨n, fun i => x i, y, fun i => ⟨(x i).2, hy i, hR i⟩,
    iop_eq_sum D T A₁ A₂ F hF x hx, iop_eq_sum D T' A₁' A₂' F' hF' x' hx'⟩

end GlobalTheory.ThetaConj.IopRepr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaOddPrimePhaseConjInvariant
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.GalTheta
open scoped BigOperators

namespace GlobalTheory.GalThetaSign

theorem sign_eq {p k k' : ℕ} {m m' : ℤ} {q : ℝ} (hp : Odd p) (h : (p : ℝ) ^ k * q = (m : ℝ))
    (h' : (p : ℝ) ^ k' * q = (m' : ℝ)) : (-1 : ℂ) ^ m' = (-1 : ℂ) ^ m := by
  have key : ∀ {a a' : ℕ} {b b' : ℤ}, a ≤ a' → (p : ℝ) ^ a * q = (b : ℝ) → (p : ℝ) ^ a' * q = (b' : ℝ) →
      (-1 : ℂ) ^ b' = (-1 : ℂ) ^ b := by
    intro a a' b b' hle hb hb'
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hle
    have hr : (b' : ℝ) = ((p : ℤ) ^ j * b : ℤ) := by
      rw [← hb', Int.cast_mul, Int.cast_pow, Int.cast_natCast, ← hb, pow_add]
      ring
    have hi : b' = (p : ℤ) ^ j * b := by exact_mod_cast hr
    have hoddp : Odd ((p : ℤ) ^ j) := (by exact_mod_cast hp : Odd (p : ℤ)).pow
    have hev : Even (b' - b) := by
      rw [hi, show (p : ℤ) ^ j * b - b = ((p : ℤ) ^ j - 1) * b by ring]
      exact (hoddp.sub_odd odd_one).mul_right b
    rw [show b' = b + (b' - b) by ring, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), hev.neg_one_zpow, mul_one]
  rcases le_total k k' with hle | hle
  · exact key hle h h'
  · exact (key hle h' h).symm

theorem wPh_eq (D : D7) (T : Tor D) {N N' : ℕ} (x : VC D N N') {p k : ℕ} {m : ℤ} (hp : p.Prime) (h2 : p ≠ 2)
    (h : (p : ℝ) ^ k * qH D T x = (m : ℝ)) : wPh D T p x = (-1 : ℂ) ^ m := by
  have hodd : Odd p := hp.odd_of_ne_two h2
  rw [wPh, if_neg h2]
  have hex : ∃ s : ℂ, ∃ (k : ℕ) (m : ℤ), (p : ℝ) ^ k * qH D T x = (m : ℝ) ∧ s = (-1 : ℂ) ^ m :=
    ⟨_, k, m, h, rfl⟩
  obtain ⟨k0, m0, h0, hs⟩ := Classical.epsilon_spec hex
  rw [hs]
  exact sign_eq hodd h h0

theorem ee_half_pow (q : ℝ) (n : ℕ) :
    ee (q / 2) ^ n = Complex.exp ((((n : ℝ) * q : ℝ) : ℂ) * ((Real.pi : ℂ) * Complex.I)) := by
  rw [ee, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem exp_int_pi (m : ℤ) : Complex.exp ((m : ℂ) * ((Real.pi : ℂ) * Complex.I)) = (-1 : ℂ) ^ m := by
  rw [Complex.exp_int_mul, Complex.exp_pi_mul_I]

theorem cj_top_pow (σ : (⊤ : IntermediateField ℚ ℂ) →ₐ[ℚ] ℂ) (z : ℂ) (n : ℕ) :
    cj ⊤ σ (z ^ n) = cj ⊤ σ z ^ n := by
  have hl : ∀ w : ℂ, liftM ⊤ w = (⟨w, IntermediateField.mem_top⟩ : (⊤ : IntermediateField ℚ ℂ)) :=
    fun w => dif_pos IntermediateField.mem_top
  simp only [cj]
  rw [hl, hl, ← map_pow]
  congr 1

theorem cj_top_sign (σ : (⊤ : IntermediateField ℚ ℂ) →ₐ[ℚ] ℂ) (m : ℤ) :
    cj ⊤ σ ((-1 : ℂ) ^ m) = (-1 : ℂ) ^ m := by
  have hl : ∀ w : ℂ, liftM ⊤ w = (⟨w, IntermediateField.mem_top⟩ : (⊤ : IntermediateField ℚ ℂ)) :=
    fun w => dif_pos IntermediateField.mem_top
  have he : (⟨(-1 : ℂ) ^ m, IntermediateField.mem_top⟩ : (⊤ : IntermediateField ℚ ℂ)) = (-1) ^ m := by
    apply Subtype.ext
    change (-1 : ℂ) ^ m = (⊤ : IntermediateField ℚ ℂ).val ((-1) ^ m)
    rw [map_zpow₀, map_neg, map_one]
  simp only [cj]
  rw [hl, he, map_zpow₀, map_neg, map_one]

theorem wPh_conj : ∀ (D : D7) (T T' : Tor D) (N N' : ℕ) (x x' : VC D N N') (σ : (⊤ : IntermediateField ℚ ℂ) →ₐ[ℚ] ℂ) (p k : ℕ) (m : ℤ), p.Prime → p ≠ 2 → (p : ℝ) ^ k * qH D T x = (m : ℝ) → cj ⊤ σ (wdPh D T x) = wdPh D T' x' → wPh D T p x = (-1 : ℂ) ^ m ∧ wPh D T' p x' = (-1 : ℂ) ^ m := by
  intro D T T' N N' x x' σ p k m hp h2 h hcj
  refine ⟨wPh_eq D T x hp h2 h, ?_⟩
  have h1 : wdPh D T x ^ (p ^ k) = (-1 : ℂ) ^ m := by
    rw [wdPh, ee_half_pow, Nat.cast_pow, h, ← exp_int_pi m, Complex.ofReal_intCast]
  have h3 : wdPh D T' x' ^ (p ^ k) = (-1 : ℂ) ^ m := by
    rw [← hcj, ← cj_top_pow, h1, cj_top_sign]
  rw [wdPh, ee_half_pow, ← exp_int_pi m, Complex.exp_eq_exp_iff_exists_int] at h3
  obtain ⟨l, hl⟩ := h3
  have hπ : (Real.pi : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) Complex.I_ne_zero
  have hreal : (p : ℝ) ^ k * qH D T' x' = ((m + 2 * l : ℤ) : ℝ) := by
    have hc : (((p : ℝ) ^ k * qH D T' x' : ℝ) : ℂ) = (((m + 2 * l : ℤ) : ℝ) : ℂ) := by
      apply mul_right_cancel₀ hπ
      push_cast at hl ⊢
      linear_combination hl
    exact Complex.ofReal_injective hc
  rw [wPh_eq D T' x' hp h2 hreal, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), (even_two_mul l).neg_one_zpow, mul_one]

end GlobalTheory.GalThetaSign
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslationCombPeriodicTwiceLevel
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.GalTheta
open scoped BigOperators

noncomputable section

namespace GlobalTheory.GalTheta.Period

variable (D : D7) (T : Tor D) {N N' : ℕ}

theorem Hf_two_mul (m : ℕ) (y l : VC D N N') : Hf D T y ((2 * m) • l) = 2 * Hf D T (m • y) l := by
  rw [Hf_nsmul_right, Hf_nsmul_left]; push_cast; ring

theorem qH_add (a b : VC D N N') :
    qH D T (a + b) = qH D T a + qH D T b + Real.sqrt D.host.d * (Hf D T a b).re := by
  simp only [qH, Hf_add_left, Hf_add_right, Complex.add_re, Hf_re_swap D T a b]
  ring

theorem qH_nsmul (n : ℕ) (a : VC D N N') : qH D T (n • a) = (n : ℝ) ^ 2 * qH D T a := by
  simp only [qH, Hf_nsmul_left, Hf_nsmul_right]
  have : ((n : ℂ) * ((n : ℂ) * Hf D T a a)).re = (n : ℝ) ^ 2 * (Hf D T a a).re := by
    simp; ring
  rw [this]; ring

theorem exp_even (r : ℝ) (m : ℤ) (h : r = 2 * m) :
    Complex.exp (-(Real.pi : ℂ) * Complex.I * (r : ℂ)) = 1 := by
  rw [h, Complex.exp_eq_one_iff]
  exact ⟨-m, by push_cast; ring⟩

theorem period (D : D7) (T : Tor D) (N N' : ℕ) (A : AddSubgroup (VC D N N'))
    (hIm : ∀ x ∈ A, ∀ y ∈ A, ∃ m : ℤ, (Hf D T x y).im = m) (hq : ∀ x ∈ A, ∃ m : ℤ, qH D T x = m)
    (k : ℕ) (c : Fin k → ℂ) (t : Fin k → VC D N N') (e₀ : VC D N N' → ℂ) (x : VC D N N') (m₀ : ℕ)
    (he : e₀ ∈ ThSp D T A) (hx : m₀ • x ∈ A) (ht : ∀ i, m₀ • t i ∈ A) (l : VC D N N') (hl : l ∈ A) :
    U D T (x + (2 * m₀) • l) (comb D T c t e₀) = U D T x (comb D T c t e₀) ∧
      wdPh D T (x + (2 * m₀) • l) = wdPh D T x := by
  obtain ⟨ql, hql⟩ := hq l hl
  have hqμ : qH D T ((2 * m₀) • l) = ((2 * (2 * (m₀ : ℤ) ^ 2 * ql) : ℤ) : ℝ) := by
    rw [qH_nsmul, hql]; push_cast; ring
  have hμ : U D T ((2 * m₀) • l) e₀ = e₀ := by
    funext z
    have h := he.2 _ (A.nsmul_mem hl (2 * m₀)) z
    have hal : al D T ((2 * m₀) • l) = 1 := by
      change (-1 : ℂ) ^ (round (qH D T ((2 * m₀) • l))) = 1
      rw [hqμ, round_intCast, zpow_mul]
      norm_num
    rwa [hal, one_mul] at h
  have hev : ∀ y : VC D N N', m₀ • y ∈ A → ∃ m : ℤ, (Hf D T y ((2 * m₀) • l)).im = 2 * m := by
    intro y hy
    obtain ⟨m, hm⟩ := hIm _ hy _ hl
    exact ⟨m, by rw [Hf_two_mul, ← hm]; simp⟩
  refine ⟨?_, ?_⟩
  · have key : ∀ (s : VC D N N'), m₀ • s ∈ A → ∀ z,
        U D T (x + (2 * m₀) • l) (U D T s e₀) z = U D T x (U D T s e₀) z := by
      intro s hs z
      have h1 : U D T (x + s) e₀ z = U D T (x + (2 * m₀) • l + s) e₀ z := by
        obtain ⟨m, hm⟩ := hev (x + s) (by rw [smul_add]; exact A.add_mem hx hs)
        conv_lhs => rw [← hμ]
        rw [U_U, exp_even _ m hm, one_mul, add_right_comm]
      obtain ⟨m, hm⟩ := hev s hs
      have h2 : (Hf D T ((2 * m₀) • l) s).im = 2 * ((-m : ℤ) : ℝ) := by
        rw [Hf_im_swap, hm]; push_cast; ring
      rw [U_U, U_U, h1, Hf_add_left, Complex.add_im, Complex.ofReal_add, mul_add, Complex.exp_add,
        exp_even _ _ h2, mul_one]
    have h : ∀ y z, U D T y (comb D T c t e₀) z = ∑ j, c j * U D T y (U D T (t j) e₀) z := by
      intro y z
      have := U_sum D T Finset.univ y (fun j w => c j * U D T (t j) e₀ w) z
      simp only [U_mul] at this
      exact this
    funext z
    rw [h, h]
    exact Finset.sum_congr rfl fun j _ => by rw [key _ (ht j)]
  · obtain ⟨a, ha⟩ := hq _ hx
    obtain ⟨b, hb⟩ := hq _ (A.add_mem hx hl)
    have h1 := qH_add D T (m₀ • x) l
    have h2 := qH_add D T x ((2 * m₀) • l)
    have h3 : (Hf D T x ((2 * m₀) • l)).re = 2 * (Hf D T (m₀ • x) l).re := by
      rw [Hf_two_mul]; simp
    have h4 : qH D T (x + (2 * m₀) • l) / 2 =
        qH D T x / 2 + ((2 * (m₀ : ℤ) ^ 2 * ql + (b - a - ql) : ℤ) : ℝ) := by
      rw [h2, hqμ, h3]
      rw [ha, hb, hql] at h1
      push_cast
      linarith
    unfold wdPh ee
    rw [h4, Complex.ofReal_add, mul_add, Complex.exp_add, Complex.ofReal_intCast,
      mul_comm _ ((_ : ℤ) : ℂ), Complex.exp_int_mul_two_pi_mul_I, mul_one]

end GlobalTheory.GalTheta.Period
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TwistedTranslateClassInvariantOfMemThetaSpace
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators

namespace GlobalTheory.ThetaConj

theorem ee_intCast_half (n : ℤ) : ee ((n : ℝ) / 2) = (-1 : ℂ) ^ n := by
  unfold ee
  rw [← Complex.exp_pi_mul_I, ← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

theorem al_of_qH (D : D7) (T : Tor D) {N N' : ℕ} (x : VC D N N') (m : ℤ) (h : qH D T x = m) :
    al D T x = (-1 : ℂ) ^ m := by
  unfold qH at h
  unfold al
  rw [h, round_intCast]

theorem qH_add_im (D : D7) (T : Tor D) {N N' : ℕ} (y u : VC D N N') :
    qH D T (y + u) - qH D T y - qH D T u + (Hf D T y u).im = 2 * (Hf D T (w0 D • y) u).im := by
  unfold qH
  rw [Hf_smul_left, Hf_add_left, Hf_add_right, Hf_add_right, Hf_conj D T y u]
  have h1 : (w0 D).re = 1 / 2 := by simp [w0]
  have h2 : (w0 D).im = Real.sqrt D.host.d / 2 := by simp [w0]
  simp only [Complex.add_re, Complex.conj_re, Complex.mul_im, h1, h2]
  ring

theorem repInd_of_thSp (D : D7) (T : Tor D) (N N' : ℕ) (A₁ A₂ : AddSubgroup (VC D N N'))
    (F : VC D N N' → ℂ) (hq : ∀ x ∈ A₂, ∃ m : ℤ, qH D T x = m)
    (hw : ∀ x ∈ A₂, ∀ y ∈ A₂, ∃ m : ℤ, (Hf D T (w0 D • x) y).im = m) (hF : F ∈ ThSp D T A₁) :
    RepInd D T A₁ A₂ F := by
  intro x hx y hy hxy
  have hu2 : x - y ∈ A₂ := A₂.sub_mem hx hy
  obtain ⟨u, rfl⟩ : ∃ u, x = y + u := ⟨x - y, by abel⟩
  rw [add_sub_cancel_left] at hxy hu2
  obtain ⟨a, ha⟩ := hq _ hx
  obtain ⟨b, hb⟩ := hq _ hy
  obtain ⟨c, hc⟩ := hq _ hu2
  obtain ⟨k, hk⟩ := hw _ hy _ hu2
  have h1 := qH_add_im D T y u
  rw [ha, hb, hc, hk] at h1
  have h2 : -(Hf D T y u).im = ((a - b - c - 2 * k : ℤ) : ℝ) := by push_cast; linarith
  funext z
  have h3 := U_U D T y u F z
  rw [h2, ee_intCast_half] at h3
  have h4 : al D T u * U D T y (U D T u F) z = U D T y F z := by
    have := hF.2 u hxy (z + y)
    conv_lhs => rw [U]
    conv_rhs => rw [U]
    rw [← mul_assoc, this]
  unfold aU
  rw [← h4, h3, al_of_qH D T _ _ ha, al_of_qH D T _ _ hb, al_of_qH D T _ _ hc, ← mul_assoc,
    ← mul_assoc, ← zpow_add₀ (by norm_num), ← zpow_add₀ (by norm_num)]
  congr 1
  have : b + c + (a - b - c - 2 * k) = a + 2 * (-k) := by ring
  rw [this, zpow_add₀ (by norm_num), zpow_mul]
  norm_num

end GlobalTheory.ThetaConj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryFiniteGaussSumPhaseRootOfUnity
section
open Complex MeasureTheory GlobalTheory.UnitaryTheta
open scoped BigOperators ComplexConjugate Real Classical

namespace GlobalTheory.UnitaryTheta.GaussPhase

theorem finite_quot {G : Type} [AddCommGroup G] [Module.Free ℤ G] [Module.Finite ℤ G] (P : AddSubgroup G)
    [P.FiniteIndex] (φ : P →+ G) (hφ : Function.Injective φ) : Finite (G ⧸ φ.range) := by
  have h1 : Finite (G ⧸ P.toIntSubmodule) := (inferInstance : Finite (G ⧸ P))
  have h2 := (Submodule.finiteQuotient_iff _).1 h1
  let ψ : P.toIntSubmodule →ₗ[ℤ] G := φ.toIntLinearMap
  have h3 : Module.finrank ℤ (LinearMap.range ψ) = Module.finrank ℤ G := by
    have hψ : Function.Injective ψ := fun x y h => hφ h
    exact (LinearMap.finrank_range_of_inj hψ).trans h2
  have h4 : Finite (G ⧸ (LinearMap.range ψ).toAddSubgroup) :=
    Submodule.finiteQuotientOfFreeOfRankEq (LinearMap.range ψ) h3
  have h5 : (LinearMap.range ψ).toAddSubgroup = φ.range := by
    ext x; exact ⟨fun ⟨y, hy⟩ => ⟨y, hy⟩, fun ⟨y, hy⟩ => ⟨y, hy⟩⟩
  rwa [h5] at h4

noncomputable def ex (t : ℝ) : ℂ := cexp (-((π : ℂ) * I) * (t : ℂ))

theorem ex_add (s t : ℝ) : ex (s + t) = ex s * ex t := by
  simp only [ex, ← Complex.exp_add]; congr 1; push_cast; ring

theorem ex_zero : ex 0 = 1 := by simp [ex]

theorem ex_two (m : ℤ) : ex (2 * m) = 1 := by
  rw [ex, ← Complex.exp_int_mul_two_pi_mul_I (-m)]; congr 1; push_cast; ring

theorem ex_pow (t : ℝ) (k : ℕ) : ex t ^ k = ex (k * t) := by
  simp only [ex, ← Complex.exp_nat_mul]; congr 1; push_cast; ring

theorem gauss_phase : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V), IsPosHerm H → ∀ (a : V ≃ₗ[ℂ] V), (∀ z w, H (a z) (a w) = H z w) → ∀ (B : V →ₗ[ℂ] V), (∀ x, B x - a (B x) = x) → (∀ x, B (x - a x) = x) → ∀ (Λ Λ' : AddSubgroup V), Λ.FG → Λ' ≤ Λ → (Λ'.addSubgroupOf Λ).FiniteIndex → (∀ y ∈ Λ', a y ∈ Λ) → ∀ α : V → ℂ, IsSemichar H Λ α → (∀ y ∈ Λ', α (a y) = α y) → ∃ (M : Type) (_ : Fintype M) (s : M → V), (∀ m, s m ∈ Λ) ∧ (∀ x ∈ Λ, ∃! p : M × Λ', x = s p.1 - ((p.2 : V) - a p.2)) ∧ GlobalTheory.Phase.Ph (∑ m, α (s m) * cexp (-((π : ℂ) * I) * ((H (B (s m)) (s m)).im : ℂ))) := by
  intro V _ _ H hH a ha B hB1 hB2 Λ Λ' hfg hle hfi haΛ α hα hαa
  obtain ⟨hα1, hint, hadd⟩ := hα
  have hanti : ∀ x y, (H x y).im = -(H y x).im := fun x y => by rw [hH.1 x y]; simp
  have hself : ∀ x, (H x x).im = 0 := fun x => by have := hanti x x; linarith
  have hadj : ∀ x y, (H (B x) y).im - (H (B y) x).im = (H x y).im := by
    intro x y
    have h1 : H (B x) y + H x (B y) = H x y := by
      have hx := hB1 x
      have hy := hB1 y
      generalize B x = u at hx ⊢
      generalize B y = v at hy ⊢
      subst hx hy
      simp only [map_sub, LinearMap.sub_apply, ha]
      ring
    have h2 := congrArg Complex.im h1
    rw [Complex.add_im, hanti x (B y)] at h2
    linarith
  let ph : V → ℂ := fun x => α x * ex (H (B x) x).im
  have hadd' : ∀ x ∈ Λ, ∀ y ∈ Λ, α (x + y) = α x * α y * ex (H x y).im := hadd
  have hsq : ∀ x ∈ Λ, α x ^ 2 = 1 := fun x hx => by rcases hα1 x hx with h | h <;> simp [h]
  have hne : ∀ x ∈ Λ, α x ≠ 0 := fun x hx => by rcases hα1 x hx with h | h <;> simp [h]
  have hα0 : α 0 = 1 := by
    have := hadd' 0 Λ.zero_mem 0 Λ.zero_mem
    rw [add_zero, hself, ex_zero, mul_one] at this
    exact (mul_eq_left₀ (hne 0 Λ.zero_mem)).1 this.symm
  have hph0 : ph 0 = 1 := by simp [ph, hα0, ex_zero]
  have hph : ∀ x ∈ Λ, ∀ y ∈ Λ, ph (x + y) = ph x * ph y * ex (2 * (H (B x) y).im) := by
    intro x hx y hy
    have e : (H (B (x + y)) (x + y)).im + (H x y).im =
        (H (B x) x).im + (H (B y) y).im + 2 * (H (B x) y).im := by
      simp only [map_add, LinearMap.add_apply, Complex.add_im, ← hadj x y]; ring
    have e' := congrArg ex e
    rw [ex_add, ex_add, ex_add] at e'
    simp only [ph, hadd' x hx y hy]
    linear_combination α x * α y * e'
  have hmem : ∀ y ∈ Λ', y - a y ∈ Λ := fun y hy => Λ.sub_mem (hle hy) (haΛ y hy)
  have hphA : ∀ y ∈ Λ', ph (y - a y) = 1 := by
    intro y hy
    have h := hadd' _ (hmem y hy) _ (haΛ y hy)
    rw [sub_add_cancel, hαa y hy] at h
    have h' : α (y - a y) * ex (H (y - a y) (a y)).im = 1 :=
      (mul_eq_left₀ (hne y (hle hy))).1 (by linear_combination -h)
    obtain ⟨m, hm⟩ := hint y (hle hy) (a y) (haΛ y hy)
    have e1 : (H (y - a y) (a y)).im = m := by
      simp only [map_sub, LinearMap.sub_apply, Complex.sub_im, hself, hm, sub_zero]
    have e2 : (H (B (y - a y)) (y - a y)).im = m + 2 * ((-m : ℤ) : ℝ) := by
      rw [hB2]
      simp only [map_sub, Complex.sub_im, hself, hm]; push_cast; ring
    simp only [ph]
    rw [e2, ex_add, ex_two, mul_one, ← e1, h']
  have hper : ∀ x ∈ Λ, ∀ y ∈ Λ', ph (y - a y + x) = ph x := by
    intro x hx y hy
    obtain ⟨m, hm⟩ := hint y (hle hy) x hx
    rw [hph _ (hmem y hy) x hx, hphA y hy, hB2, hm, ex_two, one_mul, mul_one]
  let φ : Λ'.addSubgroupOf Λ →+ Λ := AddMonoidHom.mk'
    (fun y => ⟨((y : Λ) : V) - a ((y : Λ) : V), hmem _ y.2⟩)
    (fun y z => Subtype.ext (by simp only [AddSubgroup.coe_add, map_add]; abel))
  have hφ : ∀ y, ((φ y : Λ) : V) = ((y : Λ) : V) - a ((y : Λ) : V) := fun _ => rfl
  have hinj : Function.Injective φ := by
    intro y z h
    have := congrArg (fun t : Λ => B (t : V)) h
    simp only [hφ, hB2] at this
    exact Subtype.ext (Subtype.ext this)
  have : Module.Finite ℤ Λ := Module.Finite.iff_addGroup_fg.2 ((AddGroup.fg_iff_addSubgroup_fg _).2 hfg)
  have : IsAddTorsionFree V := .of_isTorsionFree ℂ V
  have : Module.Free ℤ Λ := inferInstance
  have := finite_quot _ φ hinj
  let _ : Fintype (Λ ⧸ φ.range) := Fintype.ofFinite _
  have hrel : ∀ x x' : Λ, (x : Λ ⧸ φ.range) = x' ↔ ∃ y ∈ Λ', (x' : V) = y - a y + x := by
    intro x x'
    rw [QuotientAddGroup.eq]
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨_, y.2, ?_⟩
      have := congrArg Subtype.val hy
      rw [hφ] at this
      erw [this]; simp
    · rintro ⟨y, hy, h⟩
      refine ⟨⟨⟨y, hle hy⟩, hy⟩, Subtype.ext ?_⟩
      rw [hφ]; simp [h]
  have hf : ∀ x : Λ, ph ((Quotient.out (x : Λ ⧸ φ.range) : Λ) : V) = ph x := by
    intro x
    obtain ⟨y, hy, h⟩ := (hrel x _).1 (QuotientAddGroup.out_eq' _).symm
    rw [h, hper _ x.2 y hy]
  refine ⟨Λ ⧸ φ.range, inferInstance, fun m => ((Quotient.out m : Λ) : V), fun m => (Quotient.out m).2, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, h⟩ := (hrel ⟨x, hx⟩ _).1 (QuotientAddGroup.out_eq' _).symm
    refine ⟨(((⟨x, hx⟩ : Λ) : Λ ⧸ φ.range), ⟨y, hy⟩), by simp only [h]; abel, ?_⟩
    rintro ⟨m, z, hz⟩ h'
    simp only at h'
    have hm : ((⟨x, hx⟩ : Λ) : Λ ⧸ φ.range) = m := by
      rw [← QuotientAddGroup.out_eq' m, hrel]
      exact ⟨z, hz, by simp only [h']; abel⟩
    subst hm
    refine Prod.ext rfl (Subtype.ext ?_)
    rw [h] at h'
    have : z - a z = y - a y := by
      have h'' : x = y - a y + x - (z - a z) := h'
      rw [← sub_eq_zero] at h'' ⊢
      rw [← h'']; abel
    simpa only [hB2] using congrArg B this
  · refine GlobalTheory.Phase.GaussSum.ph_sum _ (fun m : Λ ⧸ φ.range => ph ((Quotient.out m : Λ) : V)) ⟨?_, ?_⟩
    · intro m _
      beta_reduce
      generalize Quotient.out m = x
      set k := Fintype.card (Λ ⧸ φ.range)
      have hk : 0 < k := Fintype.card_pos
      have h0 : ((0 : Λ) : Λ ⧸ φ.range) = ((k • x : Λ) : Λ ⧸ φ.range) := by
        rw [QuotientAddGroup.mk_nsmul, card_nsmul_eq_zero]; rfl
      obtain ⟨y, hy, h⟩ := (hrel _ _).1 h0
      obtain ⟨n, hn⟩ := hint y (hle hy) x x.2
      have hy' : k • B (x : V) = y := by
        rw [← map_nsmul, ← hB2 y]; congr 1; simpa using h
      have e : ((2 * k : ℕ) : ℝ) * (H (B x) x).im = 2 * n := by
        rw [← hn, ← hy', map_nsmul]; simp; ring
      refine ⟨2 * k, by omega, ?_⟩
      simp only [ph]
      rw [mul_pow, ex_pow, e, ex_two, pow_mul, hsq _ x.2]; simp
    · intro x _ y _ z _
      obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective x
      obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective y
      obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective z
      simp only [← QuotientAddGroup.mk_add, ← QuotientAddGroup.mk_zero, hf, AddSubgroup.coe_add,
        AddSubgroup.coe_zero]
      rw [hph _ (Λ.add_mem x.2 y.2) _ z.2, hph _ y.2 _ z.2, hph _ x.2 _ z.2, hph0]
      simp only [map_add, LinearMap.add_apply, Complex.add_im, mul_add, ex_add]
      ring

end GlobalTheory.UnitaryTheta.GaussPhase
end

