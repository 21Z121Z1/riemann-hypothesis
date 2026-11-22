import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0349
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0357
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0361
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0244
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0234
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralWittElementOfEvaluation
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

noncomputable section

namespace GlobalTheory.BSP.HeightSInt
variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l}

theorem smod_iff {R : Type} [CommRing R] (p x y : R) (n : ℕ) :
    x ≡ y [SMOD (Ideal.span {p} ^ n • ⊤ : Submodule R R)] ↔ p ^ n ∣ x - y := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

theorem l_ne_zero_WCb : ((l : ℕ) : WCb l) ≠ 0 := by
  intro h
  have := congrArg (fun x : WCb l => x.coeff 1) h
  simp only [WittVector.coeff_p_one, WittVector.zero_coeff] at this
  exact one_ne_zero this

theorem l_mul_cancel {x y : WCb l} (h : (l : WCb l) * x = (l : WCb l) * y) : x = y :=
  mul_left_cancel₀ l_ne_zero_WCb h

theorem dvd_iff_coeff {a : ℕ} [NeZero a] (w : Wq l a) : (l : Wq l a) ∣ w ↔ w.coeff 0 = 0 := by
  rw [← Ideal.mem_span_singleton, ← WittVector.ker_constantCoeff, RingHom.mem_ker, WittVector.constantCoeff_apply]

theorem dec {a : ℕ} [NeZero a] (s : (Wq l a)⟦X⟧) :
    (∃ s', s = (l : (Wq l a)⟦X⟧) * s') ∨
      ∃ (j : ℕ) (t s' : (Wq l a)⟦X⟧), IsUnit t ∧ s = X ^ j * t + (l : (Wq l a)⟦X⟧) * s' := by
  classical
  have hl' : ((l : (Wq l a)⟦X⟧)) = C (l : Wq l a) := (map_natCast C l).symm
  by_cases h : ∀ k, (l : Wq l a) ∣ coeff k s
  · left
    choose d hd using h
    refine ⟨mk d, ?_⟩
    ext k
    rw [hl', coeff_C_mul, coeff_mk, ← hd]
  · right
    push_neg at h
    let j := Nat.find h
    have hj : ¬ (l : Wq l a) ∣ coeff j s := Nat.find_spec h
    have hlt : ∀ i < j, (l : Wq l a) ∣ coeff i s := fun i hi => by
      have := Nat.find_min h hi
      simpa using this
    let d : ℕ → Wq l a := fun i => if hd : (l : Wq l a) ∣ coeff i s then hd.choose else 0
    refine ⟨j, mk fun i => coeff (i + j) s, mk fun i => if i < j then d i else 0, ?_, ?_⟩
    · rw [isUnit_iff_constantCoeff, ← coeff_zero_eq_constantCoeff_apply, coeff_mk, zero_add]
      exact WittVector.isUnit_of_coeff_zero_ne_zero _ (fun h0 => hj ((dvd_iff_coeff _).2 h0))
    · refine PowerSeries.ext fun k => ?_
      rw [map_add, coeff_X_pow_mul', hl', coeff_C_mul]
      simp only [coeff_mk]
      by_cases hk : j ≤ k
      · rw [if_pos hk, if_neg (not_lt.2 hk), mul_zero, add_zero, Nat.sub_add_cancel hk]
      · have hk' : k < j := not_le.1 hk
        rw [if_neg hk, if_pos hk', zero_add]
        have hdk : (l : Wq l a) ∣ coeff k s := hlt k hk'
        simp only [d, dif_pos hdk]
        exact hdk.choose_spec

variable (bk : BK K)

def e0 : bk.S →+* OCb l := WittVector.constantCoeff.comp bk.ev

theorem reduction_X_eq_flat : e0 bk X = bk.flat := by
  simp [e0, bk.ev_X, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]

theorem reduction_l_mul_eq_zero (s : bk.S) : e0 bk ((l : bk.S) * s) = 0 := by
  rw [map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]

theorem reduction_decomposition (s : bk.S) : (∃ s', s = (l : bk.S) * s') ∨ ∃ (j : ℕ) (t : bk.S), IsUnit (e0 bk t) ∧
    ∃ s' : bk.S, s = X ^ j * t + (l : bk.S) * s' ∧ e0 bk s = bk.flat ^ j * e0 bk t := by
  rcases dec s with h | ⟨j, t, s', ht, h⟩
  · exact Or.inl h
  · refine Or.inr ⟨j, t, ht.map _, s', h, ?_⟩
    rw [h, map_add, reduction_l_mul_eq_zero, add_zero, map_mul, map_pow, reduction_X_eq_flat]

theorem dvd_of_reduction_eq_zero {s : bk.S} (h : e0 bk s = 0) : ∃ s', s = (l : bk.S) * s' := by
  rcases reduction_decomposition bk s with h' | ⟨j, t, ht, s', -, he⟩
  · exact h'
  · rw [he] at h
    exact absurd h (mul_ne_zero (pow_ne_zero _ (FlatDisc.flat_ne_zero bk)) ht.ne_zero)

theorem exists_reduction_of_flat_pow {m : ℕ} {x : OCb l} {s : bk.S} (h : bk.flat ^ m * x = e0 bk s) : ∃ s₀ : bk.S, x = e0 bk s₀ := by
  have hf := FlatDisc.flat_ne_zero bk
  rcases reduction_decomposition bk s with ⟨s', rfl⟩ | ⟨j, t, ht, s', -, he⟩
  · rw [reduction_l_mul_eq_zero] at h
    exact ⟨0, by rw [map_zero]; exact (mul_eq_zero.1 h).resolve_left (pow_ne_zero _ hf)⟩
  · rw [he] at h
    by_cases hmj : m ≤ j
    · refine ⟨X ^ (j - m) * t, ?_⟩
      rw [map_mul, map_pow, reduction_X_eq_flat]
      refine mul_left_cancel₀ (pow_ne_zero m hf) ?_
      rw [h, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hmj]
    · exfalso
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt (not_le.1 hmj)
      have h2 : bk.flat ^ (k + 1) * x = e0 bk t := by
        refine mul_left_cancel₀ (pow_ne_zero j hf) ?_
        rw [← h, ← mul_assoc, ← pow_add]; ring_nf
      rw [← h2, pow_succ, mul_assoc, mul_comm, mul_assoc] at ht
      exact FlatDisc.not_isUnit_flat bk (isUnit_of_mul_isUnit_left ht)

theorem cc_evW (s : bk.S) : WittVector.constantCoeff (bk.evW s) = algebraMap (OCb l) (Cb l) (e0 bk s) := by
  simp [BK.evW, e0, inclW, WittVector.constantCoeff_apply, WittVector.map_coeff]

theorem cc_inclW (a : Ainf l) : WittVector.constantCoeff (inclW l a) = algebraMap (OCb l) (Cb l) (a.coeff 0) := by
  simp [inclW, WittVector.constantCoeff_apply, WittVector.map_coeff]

theorem cc_l_mul (y : WCb l) : WittVector.constantCoeff ((l : WCb l) * y) = 0 := by
  rw [map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]

end GlobalTheory.BSP.HeightSInt

namespace GlobalTheory.BSP.HeightSInt
variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K)

theorem evW_mem (s : bk.S) : bk.evW s ∈ bk.OE := fun _ => ⟨0, s, 0, by simp⟩

theorem mem_of_l_mul_mem {v : WCb l} (h : (l : WCb l) * v ∈ bk.OE) : v ∈ bk.OE := by
  intro n
  obtain ⟨m, s, y, hs⟩ := h (n + 1)
  have h0 : e0 bk s = 0 := by
    have := congrArg WittVector.constantCoeff hs
    rw [map_add, pow_succ', mul_assoc, cc_l_mul, add_zero, cc_evW, mul_left_comm, cc_l_mul] at this
    exact (IsFractionRing.injective (OCb l) (Cb l)) (by rw [← this, map_zero])
  obtain ⟨s', rfl⟩ := dvd_of_reduction_eq_zero bk h0
  refine ⟨m, s', y, l_mul_cancel ?_⟩
  rw [map_mul, map_natCast] at hs
  rw [mul_add, mul_left_comm, hs]; ring

theorem step {a : Ainf l} (h : inclW l a ∈ bk.OE) :
    ∃ (s₀ : bk.S) (a₁ : Ainf l), a = bk.ev s₀ + (l : Ainf l) * a₁ ∧ inclW l a₁ ∈ bk.OE := by
  obtain ⟨m, s, y, hs⟩ := h 1
  have h1 : bk.flat ^ m * a.coeff 0 = e0 bk s := by
    have := congrArg WittVector.constantCoeff hs
    rw [map_add, pow_one, cc_l_mul, add_zero, cc_evW, map_mul, map_pow, cc_evW, cc_inclW, reduction_X_eq_flat, ← map_pow,
      ← map_mul] at this
    exact IsFractionRing.injective (OCb l) (Cb l) this
  obtain ⟨s₀, hs₀⟩ := exists_reduction_of_flat_pow bk h1
  have h2 : a - bk.ev s₀ ∈ Ideal.span {(l : Ainf l)} := by
    rw [← WittVector.ker_constantCoeff, RingHom.mem_ker, map_sub, WittVector.constantCoeff_apply,
      WittVector.constantCoeff_apply, hs₀]
    simp [e0, WittVector.constantCoeff_apply]
  obtain ⟨a₁, ha₁⟩ := Ideal.mem_span_singleton.1 h2
  refine ⟨s₀, a₁, by rw [← ha₁]; ring, mem_of_l_mul_mem bk ?_⟩
  have : (l : WCb l) * inclW l a₁ = inclW l a - bk.evW s₀ := by
    rw [BK.evW, RingHom.comp_apply, ← map_sub, ha₁, map_mul, map_natCast]
  rw [this]
  exact sub_mem h (evW_mem bk s₀)

theorem exists_lim {a : ℕ} [NeZero a] (T : ℕ → (Wq l a)⟦X⟧)
    (hT : ∀ n, (l : (Wq l a)⟦X⟧) ^ n ∣ T (n + 1) - T n) :
    ∃ s : (Wq l a)⟦X⟧, ∀ n, (l : (Wq l a)⟦X⟧) ^ n ∣ T n - s := by
  classical
  have hl' : ∀ n, ((l : (Wq l a)⟦X⟧)) ^ n = C ((l : Wq l a) ^ n) := fun n => by
    rw [map_pow, map_natCast]
  have hmn : ∀ m k, (l : (Wq l a)⟦X⟧) ^ m ∣ T (m + k) - T m := by
    intro m k
    induction k with
    | zero => simp
    | succ k ih =>
      have : T (m + (k + 1)) - T m = (T (m + k + 1) - T (m + k)) + (T (m + k) - T m) := by
        rw [← add_assoc]; ring
      rw [this]
      exact dvd_add ((pow_dvd_pow _ (Nat.le_add_right m k)).trans (hT (m + k))) ih
  have hc : ∀ i, ∃ L : Wq l a, ∀ n, (l : Wq l a) ^ n ∣ coeff i (T n) - L := by
    intro i
    have hpc : IsPrecomplete (Ideal.span {(l : Wq l a)}) (Wq l a) := inferInstance
    obtain ⟨L, hL⟩ := hpc.prec (f := fun n => coeff i (T n)) (fun {m n} hmn' => by
      rw [smod_iff]
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn'
      obtain ⟨q, hq⟩ := hmn m k
      refine ⟨-coeff i q, ?_⟩
      have : T m - T (m + k) = -(T (m + k) - T m) := by ring
      rw [← map_sub, this, hq, hl', map_neg, coeff_C_mul]; ring)
    exact ⟨L, fun n => (smod_iff _ _ _ _).1 (hL n)⟩
  choose L hL using hc
  refine ⟨mk L, fun n => ?_⟩
  choose q hq using fun i => hL i n
  refine ⟨mk fun i => q i, PowerSeries.ext fun i => ?_⟩
  rw [map_sub, coeff_mk, hl', coeff_C_mul, coeff_mk, hq]

theorem main (w : WCb l) (hw : w ∈ bk.OE) (a : Ainf l) (ha : w = inclW l a) : ∃ s : bk.S, a = bk.ev s := by
  classical
  subst ha
  let P : Type := {a : Ainf l // inclW l a ∈ bk.OE}
  have hs : ∀ b : P, ∃ (s₀ : bk.S) (b₁ : P), b.1 = bk.ev s₀ + (l : Ainf l) * b₁.1 := fun b => by
    obtain ⟨s₀, a₁, h, h'⟩ := step bk b.2
    exact ⟨s₀, ⟨a₁, h'⟩, h⟩
  choose σ nx hσ using hs
  let A : ℕ → P := fun n => nx^[n] ⟨a, hw⟩
  have hA : ∀ n, A (n + 1) = nx (A n) := fun n => Function.iterate_succ_apply' nx n _
  let T : ℕ → bk.S := fun n => ∑ i ∈ Finset.range n, (l : bk.S) ^ i * σ (A i)
  have hTa : ∀ n, a = bk.ev (T n) + (l : Ainf l) ^ n * (A n).1 := by
    intro n
    induction n with
    | zero => simp [T, A]
    | succ n ih =>
      rw [ih, hσ (A n), ← hA n]
      simp only [T, Finset.sum_range_succ, map_add, map_mul, map_pow, map_natCast]
      ring
  obtain ⟨s, hs⟩ := exists_lim T (fun n => ⟨σ (A n), by simp [T, Finset.sum_range_succ]⟩)
  refine ⟨s, ?_⟩
  rw [← sub_eq_zero]
  refine (IsHausdorff.eq_iff_smodEq (I := Ideal.span {(l : Ainf l)})).2 fun n => (smod_iff _ _ _ _).2 ?_
  obtain ⟨q, hq⟩ := hs n
  have : T n = s + (l : bk.S) ^ n * q := by rw [← hq]; ring
  refine ⟨bk.ev q + (A n).1, ?_⟩
  rw [sub_zero]
  conv_lhs => rw [hTa n]
  rw [this, map_add, map_mul, map_pow, map_natCast]
  ring

end GlobalTheory.BSP.HeightSInt

theorem GlobalTheory.BSP.ainf_inter_OE : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), ∀ w ∈ bk.OE, ∀ a : Ainf l,
    w = inclW l a → ∃ s : bk.S, a = bk.ev s :=
  fun _ _ _ bk w hw a ha => HeightSInt.main bk w hw a ha
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvariantsVanishAtPrimeOfAdmissible
section
noncomputable section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

namespace GlobalTheory.Cyc.InvKilled

variable {l : ℕ} [Fact l.Prime]

theorem exists_pow_smul_mem (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (v : T.V) :
    ∃ n : ℕ, (l : ↥LL.1) ^ n • v ∈ T.L.T := by
  first
  | exact @_root_.GlobalTheory.IntegerRingPowers.main
  | exact _root_.GlobalTheory.IntegerRingPowers.main
  | (apply _root_.GlobalTheory.IntegerRingPowers.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegerRingPowers.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegerRingPowers.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegerRingPowers.main ..)

theorem killed_of_coordinates {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp]
    [Field LL] [CharZero LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    (T : LocLat G Qp LL O) [Module ℤ_[l] ↥T.L.T]
    (hsm : ∀ (k : ℕ) (t : ↥T.L.T),
      ((((l : ℤ_[l]) ^ k) • t : ↥T.L.T) : T.V) = (l : LL) ^ k • (t : T.V))
    (ac : G → (↥T.L.T →ₗ[ℤ_[l]] ↥T.L.T)) (hac : ∀ g t, ((ac g t : ↥T.L.T) : T.V) = T.ρ g t)
    {d : ℕ} (b : Module.Basis (Fin d) ℤ_[l] ↥T.L.T)
    (M : G → Matrix (Fin d) (Fin d) (PadicComplex l))
    (hb : ∀ g i j, M g i j = zC (b.repr (ac g (b j)) i)) (c : ℕ)
    (H : ∀ y : Fin d → ℚ_[l], (∀ σ,
      (M σ).mulVec (fun a => algebraMap ℚ_[l] (PadicComplex l) (y a)) -
        (fun a => algebraMap ℚ_[l] (PadicComplex l) (y a)) ∈ ball l d) →
      ∀ a, ‖(l : ℚ_[l]) ^ c * y a‖ ≤ 1)
    (v : T.V) (hw : ∀ g, T.ρ g v - v ∈ T.L.T) (n : ℕ) (hn : (l : LL) ^ n • v ∈ T.L.T) :
    (l : LL) ^ c • v ∈ T.L.T := by
  have hl : (l : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hlL : (l : LL) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  set t : ↥T.L.T := ⟨_, hn⟩ with ht
  have hy := H (fun a => ((l : ℚ_[l]) ^ n)⁻¹ * (b.repr t a : ℚ_[l])) (by
    intro σ a
    have e1 : ac σ t - t = (l : ℤ_[l]) ^ n • (⟨_, hw σ⟩ : ↥T.L.T) := by
      apply Subtype.ext
      rw [hsm, Submodule.coe_sub, hac]
      change T.ρ σ ((l : LL) ^ n • v) - (l : LL) ^ n • v = _
      rw [map_smul, smul_sub]
    have e2 : b.repr (ac σ t) a =
        ∑ j, b.repr (ac σ (b j)) a * b.repr t j := by
      conv_lhs => rw [← b.sum_repr t]
      simp only [map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply,
        smul_eq_mul, mul_comm]
    have e3 := congrArg (fun z => ((b.repr z a : ℤ_[l]) : ℚ_[l])) e1
    simp only [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul, e2] at e3
    push_cast at e3
    have e4 : ((M σ).mulVec (fun a => algebraMap ℚ_[l] (PadicComplex l)
          (((l : ℚ_[l]) ^ n)⁻¹ * (b.repr t a : ℚ_[l]))) -
        (fun a => algebraMap ℚ_[l] (PadicComplex l) (((l : ℚ_[l]) ^ n)⁻¹ * (b.repr t a : ℚ_[l])))) a =
        algebraMap ℚ_[l] (PadicComplex l) ((b.repr (⟨_, hw σ⟩ : ↥T.L.T) a : ℤ_[l]) : ℚ_[l]) := by
      have hb' : ∀ i j, M σ i j = zC (b.repr (ac σ (b j)) i) := hb σ
      simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, hb', zC, ← map_mul, ← map_sum, ← map_sub]
      congr 1
      have hp : (l : ℚ_[l]) ^ n ≠ 0 := pow_ne_zero _ hl
      rw [← inv_mul_cancel_left₀ hp (((b.repr (⟨_, hw σ⟩ : ↥T.L.T) a : ℤ_[l]) : ℚ_[l])), ← e3,
        mul_sub, PadicInt.coe_sum, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun j _ => by rw [PadicInt.coe_mul]; ring
    rw [e4, norm_algebraMap']
    exact PadicInt.norm_le_one _)
  let z : Fin d → ℤ_[l] := fun a => ⟨_, hy a⟩
  let t' : ↥T.L.T := ∑ a, z a • b a
  have e5 : (l : ℤ_[l]) ^ c • t = (l : ℤ_[l]) ^ n • t' := by
    apply b.repr.injective
    ext a
    have : b.repr t' a = z a := congrFun (b.repr_sum_self z) a
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, this]
    apply Subtype.ext
    have hz : ((z a : ℤ_[l]) : ℚ_[l]) = (l : ℚ_[l]) ^ c * (((l : ℚ_[l]) ^ n)⁻¹ * (b.repr t a : ℚ_[l])) := rfl
    rw [PadicInt.coe_mul, PadicInt.coe_mul, hz]
    push_cast
    field_simp
  have e6 := congrArg Subtype.val e5
  rw [hsm, hsm] at e6
  change (l : LL) ^ c • (l : LL) ^ n • v = _ at e6
  rw [smul_comm] at e6
  have e7 := smul_right_injective _ (pow_ne_zero n hlL) e6
  rw [e7]
  exact t'.2

theorem pow_smul_compHom {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp]
    [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    (T : LocLat G Qp LL O) (φ : ℤ_[l] →+* O) :
    letI : Module ℤ_[l] ↥T.L.T := Module.compHom ↥T.L.T φ
    ∀ (k : ℕ) (t : ↥T.L.T),
      ((((l : ℤ_[l]) ^ k) • t : ↥T.L.T) : T.V) = (l : LL) ^ k • (t : T.V) := by
  intro k t
  change (φ ((l : ℤ_[l]) ^ k)) • (t : T.V) = _
  rw [← algebraMap_smul LL, map_pow, map_natCast, map_pow, map_natCast]

theorem killed_of_coord (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) {d : ℕ}
    (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l))
    (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)) (hM : IsMat K LL T M A) (c : ℕ)
    (H : ∀ y : Fin d → ℚ_[l], (∀ σ ∈ GK K,
      (M σ).mulVec (fun a => algebraMap ℚ_[l] (PadicComplex l) (y a)) -
        (fun a => algebraMap ℚ_[l] (PadicComplex l) (y a)) ∈ ball l d) →
      ∀ a, ‖(l : ℚ_[l]) ^ c * y a‖ ≤ 1)
    (v : T.V) (hw : ∀ g : ↥(GK K), T.ρ g v - v ∈ T.L.T) : (l : ↥LL.1) ^ c • v ∈ T.L.T := by
  obtain ⟨b, hb, -⟩ := hM
  obtain ⟨n, hn⟩ := exists_pow_smul_mem K LL T v
  refine @killed_of_coordinates l _ _ _ _ _ _ _ _ _ _ _ _ _ _ T (zlMod LL T) ?_
    (fun g => actTZ LL T g) (fun _ _ => rfl) d b (fun g => M g) hb c
    (fun y hy => H y fun σ hσ => hy ⟨σ, hσ⟩) v hw n hn
  exact pow_smul_compHom T (algebraMap ℤ_[l] ↥(OL LL))

theorem killed_quot {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] (T : LocLat G Qp LL O)
    (p c : ℕ) (H : ∀ v : T.V, (∀ g, T.ρ g v - v ∈ T.L.T) → (p : LL) ^ c • v ∈ T.L.T)
    (x : T.V ⧸ T.L.T) (hx : ∀ g, actD T.L g x = x) : ((p : O) ^ c) • x = 0 := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, ← algebraMap_smul LL, map_pow,
    map_natCast]
  exact H v fun g => (Submodule.Quotient.eq _).1 (hx g)

def imBall {r d : ℕ} (P : Matrix (Fin r) (Fin d) (PadicComplex l)) :
    AddSubgroup (Fin r → PadicComplex l) where
  carrier := P.mulVec '' ball l d
  zero_mem' := ⟨0, fun a => by simp, Matrix.mulVec_zero _⟩
  add_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x + y, fun a => (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hx a) (hy a)),
      Matrix.mulVec_add _ _ _⟩
  neg_mem' := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨-x, fun a => by simpa using hx a, Matrix.mulVec_neg _ _⟩

theorem Ks_mono' (K : FinExt l) {i j : ℕ} (h : i ≤ j) : Ks K i ≤ Ks K j := by
  refine sup_le_sup_left (IntermediateField.adjoin.mono _ _ _ ?_) _
  intro x hx
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  simp only [Set.mem_setOf_eq] at hx ⊢
  rw [pow_add, pow_mul, hx, one_pow]

theorem act_algebraMap' {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} (ha : IsActC act)
    (g : GQ l) (x : ℚ_[l]) :
    act g (algebraMap ℚ_[l] (PadicComplex l) x) = algebraMap ℚ_[l] (PadicComplex l) x := by
  have := ha.1 g (algebraMap ℚ_[l] (Om l) x)
  rw [AlgEquiv.commutes] at this
  exact this

theorem invariants_killed : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), adm7 D → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := sit D.loc HW l (D.locA l) K s LL h; let E : S.Comparison₂ := ((F l).E K s LL h).tie; H0at S E := by
  intro D HW F h7 l _ K s LL h S E M0 h0 T τ hW hj x hx
  have hell : ell S = l := (D.loc l).PD_p K
  have hs : S.W.s = s := (HW l).W_s K s LL h
  obtain ⟨d, M, A, hM⟩ := (GlobalTheory.T.exists_continuous_galoisLatticeMatrix_integral l K LL T).1
  obtain ⟨r, P, U, g, J, hJ, hfin, hFr, hHT, hPM, hb1, hb2, hint⟩ :=
    GlobalTheory.T.exists_tau_component_frame_of_lattice D HW F h7 l K s LL h T M0 h0 τ hW d M A hM
  have hact : IsActC (D.locA l).actC := ⟨(D.locA l).actC_ext, (D.locA l).actC_norm⟩
  have hχ : IsCyc (D.loc l).χQ := (D.loc l).χQ_cyc
  set m := mN l s (M0 + h0) with hm
  have hsm : s + 1 ≤ m := by rw [hm, mN]; omega
  have hs1 := h.1
  have hLev : Lev l m := ⟨by omega, fun _ => by omega⟩
  have hG : Gj K m ≤ GK K :=
    IntermediateField.fixingSubgroup_le (h.2.2.1.trans (Ks_mono' K (by omega)))
  have h0J : (0 : ℤ) ∉ J := fun hh => hj (hJ 0 hh)
  have hc0 : c0 S T τ M0 h0 = 2 + ∑ u ∈ hfin.toFinset, (m + padicValInt l u) := by
    rw [c0, hell, hs]
    congr 1
    exact finsum_mem_eq_finite_toFinset_sum (fun u => m + vZ l u) hfin
  rw [hell]
  refine killed_quot T l _ (killed_of_coord K LL T M A hM _ ?_) x hx
  intro y hy
  have hl1 : ‖(l : ℚ_[l])‖ ≤ 1 := (Padic.norm_p_lt_one).le
  rcases J.eq_empty_or_nonempty with rfl | ⟨u0, hu0⟩
  · obtain ⟨e, u, -, hu, -⟩ := hHT
    have : IsEmpty (Fin r) := ⟨fun k => by simpa using hu k⟩
    intro a
    have := hint y ⟨0, fun a => by simp, Subsingleton.elim _ _⟩ a
    rw [norm_mul, norm_pow]
    exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) hl1) (norm_nonneg _) this
  · have key := GlobalTheory.T.prime_pow_smul_mem_of_twistedInvariant_mod_lattice l _ _ hact hχ K m r hLev U g hFr J hHT 0 h0J (imBall P) hb1
      (by rintro _ ⟨z, hz, rfl⟩; exact hb2 z hz)
      (P.mulVec (fun a => algebraMap ℚ_[l] (PadicComplex l) (y a))) (by
        intro σ hσ
        refine ⟨_, hy σ (hG hσ), ?_⟩
        have e1 : (fun a => (D.locA l).actC σ
            (P.mulVec (fun a => algebraMap ℚ_[l] (PadicComplex l) (y a)) a)) =
            (P.map ((D.locA l).actC σ)).mulVec (fun a => algebraMap ℚ_[l] (PadicComplex l) (y a)) := by
          funext a
          simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply,
            act_algebraMap' hact]
        rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, hPM σ hσ, twAct, e1, Matrix.mulVec_mulVec]
        simp [chiC])
    rw [Finset.erase_eq_of_notMem h0J] at key
    simp only [sub_zero] at key
    have hle1 : 1 ≤ ∑ u ∈ J, (m + padicValInt l u) :=
      le_trans (by omega) (Finset.single_le_sum (f := fun u => m + padicValInt l u)
        (fun _ _ => Nat.zero_le _) hu0)
    have hle2 : ∑ u ∈ J, (m + padicValInt l u) ≤ ∑ u ∈ hfin.toFinset, (m + padicValInt l u) :=
      Finset.sum_le_sum_of_subset fun u hu => hfin.mem_toFinset.2 (hJ u hu)
    rw [max_eq_right hle1] at key
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle2
    have hi := hint (fun a => (l : ℚ_[l]) ^ (2 + ∑ u ∈ J, (m + padicValInt l u)) * y a) (by
      have e : (fun a => algebraMap ℚ_[l] (PadicComplex l)
          ((l : ℚ_[l]) ^ (2 + ∑ u ∈ J, (m + padicValInt l u)) * y a)) =
          (l : PadicComplex l) ^ (2 + ∑ u ∈ J, (m + padicValInt l u)) •
            (fun a => algebraMap ℚ_[l] (PadicComplex l) (y a)) := by
        funext a
        simp only [map_mul, map_pow, map_natCast, Pi.smul_apply, smul_eq_mul]
      rw [e, Matrix.mulVec_smul]
      exact key)
    intro a
    rw [hc0, hk, ← add_assoc, add_comm _ k, pow_add, mul_assoc, norm_mul, norm_pow]
    exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) hl1) (norm_nonneg _) (hi a)

end GlobalTheory.Cyc.InvKilled
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPrismCoverOfStableMaximalMapNeTop
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

private lemma map_quotient_mk_proper_of_le_jacobson {B : Type} [CommRing B] (J 𝔟 : Ideal B) (hJ : 𝔟 ≤ Ideal.jacobson ⊥)
    (h : J ≠ ⊤) : J.map (Ideal.Quotient.mk 𝔟) ≠ ⊤ := by
  intro htop
  obtain ⟨x, hx, hx1⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1
    ((Ideal.eq_top_iff_one _).1 htop)
  have h1 : 1 - x ∈ 𝔟 := by
    rw [← Ideal.Quotient.eq, map_one, hx1]
  have hu := Ideal.mem_jacobson_bot.1 (hJ h1) (-1)
  have hx' : (1 - x) * -1 + 1 = x := by ring
  rw [hx'] at hu
  exact h (Ideal.eq_top_of_isUnit_mem _ hx hu)

theorem faithfullyFlat_quotientMap_of_map_ne_top {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (𝔞 : Ideal A) (𝔟 : Ideal B) (hle : 𝔞 ≤ 𝔟.comap f) (hJ : 𝔟 ≤ Ideal.jacobson ⊥)
    (hfl : (Ideal.quotientMap 𝔟 f hle).Flat) (hm : ∀ 𝔪 : Ideal A, 𝔪.IsMaximal → 𝔪.map f ≠ ⊤) :
    (Ideal.quotientMap 𝔟 f hle).FaithfullyFlat := by
  letI : Algebra (A ⧸ 𝔞) (B ⧸ 𝔟) := (Ideal.quotientMap 𝔟 f hle).toAlgebra
  have hfl' : Module.Flat (A ⧸ 𝔞) (B ⧸ 𝔟) := hfl
  show Module.FaithfullyFlat (A ⧸ 𝔞) (B ⧸ 𝔟)
  refine { toFlat := hfl', submodule_ne_top := fun 𝔫 h𝔫 htop => ?_ }
  rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_eq_top_iff] at htop

  set 𝔪 := 𝔫.comap (Ideal.Quotient.mk 𝔞)
  have hmax : 𝔪.IsMaximal := Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  have key : (𝔪.map f).map (Ideal.Quotient.mk 𝔟) = ⊤ := by
    rw [Ideal.map_map, ← Ideal.quotientMap_comp_mk hle, ← Ideal.map_map,
      Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
    exact htop
  exact map_quotient_mk_proper_of_le_jacobson _ _ hJ (hm 𝔪 hmax) key

theorem cover_of_stable_of_map_ne_top : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B C : Obj l R)
    (h : Hom B C), Stable h → (∀ 𝔪 : Ideal B.A, 𝔪.IsMaximal → 𝔪.map h.f ≠ ⊤) → Cover h := by
  intro l _ R _ B C h hs hm
  refine ⟨hs, fun m => ?_⟩
  rcases m with _ | m
  ·
    haveI : Subsingleton (B.A ⧸ adI B ^ 0) := Ideal.Quotient.subsingleton_iff.2 (by simp)
    rw [RingHom.FaithfullyFlat.iff_flat_and_comap_surjective]
    exact ⟨hs.flat 0, fun p => isEmptyElim p⟩
  · haveI := C.complete
    have hJ : adI C ^ (m + 1) ≤ Ideal.jacobson ⊥ :=
      (Ideal.pow_le_self (Nat.succ_ne_zero m)).trans (IsAdicComplete.le_jacobson_bot (adI C))
    exact faithfullyFlat_quotientMap_of_map_ne_top h.f _ _ (adI_pow_le h (m + 1)) hJ (hs.flat (m + 1)) hm

end GlobalTheory.BSP
end

