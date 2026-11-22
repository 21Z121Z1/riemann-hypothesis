import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0006
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0236
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0117
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0119
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0113
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0023
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingCyclotomicTowerLevel

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionAllCoeffsDeltaPowAffineSubst
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FNPole

theorem qAll_monomial (E : Subring ℂ) (M k : ℕ) :
    QAll (· ∈ E) M fun τ => Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * τ / M) := by
  refine ⟨fun n => if n = k then 1 else 0, fun τ => ?_, fun n => ?_⟩
  · have := hasSum_single (f := fun n : ℕ => (if n = k then (1 : ℂ) else 0) *
      Complex.exp (2 * Real.pi * Complex.I * n * τ / M)) k (fun n hn => by simp [hn])
    simpa using this
  · dsimp only; split_ifs
    · exact E.one_mem
    · exact E.zero_mem

theorem qAll_of_int (E : Subring ℂ) {f : ℍ → ℂ} (h : ∃ c : ℕ → ℤ, c 0 = 1 ∧ HasQ 1 f fun n => (c n : ℂ)) :
    QAll (· ∈ E) 1 f := by
  obtain ⟨c, -, hc⟩ := h
  exact ⟨_, hc, fun n => intCast_mem E (c n)⟩

theorem qAll_congr {p : ℂ → Prop} {N : ℕ} {f g : ℍ → ℂ} (hf : QAll p N f) (h : ∀ τ, f τ = g τ) :
    QAll p N g := by
  have : f = g := funext h
  exact this ▸ hf

theorem qAll_pole_affine : ∀ (E : Subring ℂ) (N w a d : ℕ) (b : ℤ) (φ : ℍ → ℂ),
    (∀ x : ℚ, Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ∈ E) → 0 < N → 0 < a → 0 < d →
    QAll (· ∈ E) N (fun τ => DD τ ^ w * φ τ) →
    QAll (· ∈ E) (N * (a * d)) fun τ => DD τ ^ (w * (a * d)) * up φ (((a : ℂ) * τ + b) / d) := by
  intro E N w a d b φ hE hN ha hd hφ
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  have hM : 0 < N * (a * (d' + 1)) := by positivity
  have RC := GlobalTheory.T.qExpansionCoeffsInSubring_ring_closed E (N * (a * (d' + 1))) hM
  obtain ⟨hDq, hqD⟩ := GlobalTheory.T.modularDiscriminant_div_q_integer_qExpansions
  have h1 := QAll.of_dvd hM ⟨a, by ring⟩ E.zero_mem
    (GlobalTheory.T.qExpansionAllCoeffs_comp_upper_triangular E N a (d' + 1) b _ hE hN ha (by omega) hφ)
  have h2 := QAll.of_dvd hM ⟨N * a, by ring⟩ E.zero_mem
    (GlobalTheory.T.qExpansionAllCoeffs_comp_upper_triangular E 1 a (d' + 1) b _ hE one_pos ha (by omega) (qAll_of_int E hqD))
  have h3 := QAll.of_dvd hM (one_dvd _) E.zero_mem (qAll_of_int E hDq)
  have h2w := RC.2.2.2.2.1 _ w h2
  have h3w := RC.2.2.2.2.1 _ (w * (a * (d' + 1))) h3
  have h4 := RC.1 _ (hE (-((w : ℚ) * b) / (d' + 1)))
  have h5 := qAll_monomial E (N * (a * (d' + 1))) (N * w * a * a * (d' * (d' + 2)))
  have hP := RC.2.2.2.1 _ _ (RC.2.2.2.1 _ _ (RC.2.2.2.1 _ _ (RC.2.2.2.1 _ _ h1 h2w) h3w) h4) h5
  refine qAll_congr hP fun τ => ?_
  simp only [up]
  set U := UpperHalfPlane.ofComplex (((a : ℂ) * τ + b) / ((d' + 1 : ℕ) : ℂ)) with hUdef
  have him : 0 < (((a : ℂ) * τ + b) / ((d' + 1 : ℕ) : ℂ)).im := by
    have : (((a : ℂ) * τ + b) / ((d' + 1 : ℕ) : ℂ)).im = a * τ.im / (d' + 1) := by
      rw [Complex.div_natCast_im]; simp
    rw [this]; have := τ.im_pos; positivity
  have hU : (U : ℂ) = ((a : ℂ) * τ + b) / ((d' + 1 : ℕ) : ℂ) := by
    rw [hUdef, UpperHalfPlane.ofComplex_apply_of_im_pos him]
  have key : Complex.exp (2 * Real.pi * Complex.I * (U : ℂ)) ^ w *
      Complex.exp (2 * Real.pi * Complex.I * (((-((w : ℚ) * b) / (d' + 1) : ℚ)) : ℂ)) *
      Complex.exp (2 * Real.pi * Complex.I * ((N * w * a * a * (d' * (d' + 2)) : ℕ) : ℂ) * τ /
        ((N * (a * (d' + 1)) : ℕ) : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I * (τ : ℂ)) ^ (w * (a * (d' + 1))) := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add, ← Complex.exp_add, hU]
    congr 1
    have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
    have hd' : (d' : ℂ) + 1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero d')
    push_cast
    field_simp
    ring
  have hDU := ReciprocityTheory.ChartRestriction.L1.DD_ne_zero U
  have hDτ := ReciprocityTheory.ChartRestriction.L1.DD_ne_zero τ
  have e1 := Complex.exp_ne_zero (2 * Real.pi * Complex.I * (U : ℂ))
  have e2 := Complex.exp_ne_zero (2 * Real.pi * Complex.I * (τ : ℂ))
  have e3 := Complex.exp_ne_zero (2 * Real.pi * Complex.I * (((-((w : ℚ) * b) / (d' + 1) : ℚ)) : ℂ))
  have e4 := Complex.exp_ne_zero (2 * Real.pi * Complex.I * ((N * w * a * a * (d' * (d' + 2)) : ℕ) : ℂ) * τ /
        ((N * (a * (d' + 1)) : ℕ) : ℂ))
  rw [div_pow, div_pow, ← key]
  field_simp

end GlobalTheory.FNPole
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.QzTorsionZmodEmbedding
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology

namespace GlobalTheory

section

variable (l : ℕ) [Fact l.Prime]

private theorem qzTor_smul_mk (x : ℤ_[l]) (q : ℚ_[l]) :
    x • QZ.mk l q = QZ.mk l ((x : ℚ_[l]) * q) := rfl

private theorem qzTor_mk_eq_zero (q : ℚ_[l]) :
    QZ.mk l q = 0 ↔ ∃ z : ℤ_[l], (z : ℚ_[l]) = q :=
  Submodule.Quotient.mk_eq_zero (ZlSub l)

private theorem qzTor_mk_surj (a : QZ l) : ∃ q, QZ.mk l q = a :=
  Submodule.Quotient.mk_surjective (ZlSub l) a

private theorem qzTor_key (r : ℕ) (x : ℤ_[l]) :
    x • QZ.mk l (((l : ℚ_[l]) ^ r)⁻¹) = 0 ↔ PadicInt.toZModPow r x = 0 := by
  have hl : ((l : ℚ_[l]) ^ r) ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero)
  rw [qzTor_smul_mk, qzTor_mk_eq_zero, ← RingHom.mem_ker, PadicInt.ker_toZModPow,
    Ideal.mem_span_singleton']
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, Subtype.ext ?_⟩
    have : ((z * (l : ℤ_[l]) ^ r : ℤ_[l]) : ℚ_[l]) = (z : ℚ_[l]) * (l : ℚ_[l]) ^ r := by
      push_cast; rfl
    rw [this, hz]
    field_simp
  · rintro ⟨z, rfl⟩
    refine ⟨z, ?_⟩
    push_cast
    field_simp

end

theorem qz_torsion_zmod_embedding (l : ℕ) [Fact l.Prime] :
    (∀ a : QZ l, ∃ r : ℕ, (l : ℤ_[l]) ^ r • a = 0) ∧
    ∀ r : ℕ, ∃ ι : ZMod (l ^ r) →+ QZ l, Function.Injective ι ∧
      (∀ a : QZ l, (l : ℤ_[l]) ^ r • a = 0 ↔ a ∈ Set.range ι) ∧
      ∀ (x : ℤ_[l]) (y : ZMod (l ^ r)), ι (PadicInt.toZModPow r x * y) = x • ι y := by
  have hp : l.Prime := Fact.out
  refine ⟨fun a => ?_, fun r => ?_⟩
  · obtain ⟨q, rfl⟩ := qzTor_mk_surj l a
    have hlt : ‖(l : ℚ_[l])‖ < 1 := Padic.norm_p_lt_one
    have hpos : (0 : ℝ) < (‖q‖ + 1)⁻¹ := by positivity
    obtain ⟨r, hr⟩ := exists_pow_lt_of_lt_one hpos hlt
    refine ⟨r, ?_⟩
    rw [qzTor_smul_mk, qzTor_mk_eq_zero]
    have hle : ‖(l : ℚ_[l]) ^ r * q‖ ≤ 1 := by
      rw [norm_mul, norm_pow]
      calc ‖(l : ℚ_[l])‖ ^ r * ‖q‖ ≤ (‖q‖ + 1)⁻¹ * (‖q‖ + 1) :=
            mul_le_mul hr.le (by linarith) (norm_nonneg _) hpos.le
        _ = 1 := inv_mul_cancel₀ (by positivity)
    refine ⟨⟨_, hle⟩, ?_⟩
    push_cast
    rfl
  · have hl : ((l : ℚ_[l]) ^ r) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.ne_zero)
    set e : QZ l := QZ.mk l (((l : ℚ_[l]) ^ r)⁻¹) with he
    have hs : Function.Surjective (PadicInt.toZModPow (p := l) r) := by
      haveI : NeZero (l ^ r) := ⟨pow_ne_zero _ hp.ne_zero⟩
      exact ZMod.ringHom_surjective _
    have hwd : ∀ x x' : ℤ_[l], PadicInt.toZModPow r x = PadicInt.toZModPow r x' →
        x • e = x' • e := by
      intro x x' h
      rw [← sub_eq_zero, ← sub_smul, he, qzTor_key, map_sub, h, sub_self]
    have hinv := Function.surjInv_eq hs
    let ι : ZMod (l ^ r) →+ QZ l := AddMonoidHom.mk' (fun y => Function.surjInv hs y • e) (by
      intro y y'
      rw [← add_smul]
      apply hwd
      rw [map_add, hinv, hinv, hinv])
    have hι : ∀ x : ℤ_[l], ι (PadicInt.toZModPow r x) = x • e := fun x =>
      hwd _ _ (hinv _)
    refine ⟨ι, ?_, fun a => ⟨fun ha => ?_, ?_⟩, fun x y => ?_⟩
    · rw [injective_iff_map_eq_zero]
      intro y hy
      obtain ⟨x, rfl⟩ := hs y
      rw [hι, he, qzTor_key] at hy
      exact hy
    · obtain ⟨q, rfl⟩ := qzTor_mk_surj l a
      rw [qzTor_smul_mk, qzTor_mk_eq_zero] at ha
      obtain ⟨z, hz⟩ := ha
      refine ⟨PadicInt.toZModPow r z, ?_⟩
      rw [hι, he, qzTor_smul_mk, hz]
      congr 1
      push_cast
      field_simp
    · rintro ⟨y, rfl⟩
      obtain ⟨x, rfl⟩ := hs y
      rw [hι, smul_smul, he, qzTor_key, ← RingHom.mem_ker, PadicInt.ker_toZModPow]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    · obtain ⟨x', rfl⟩ := hs y
      rw [← map_mul, hι, hι, mul_smul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamifiedDivisibilityOfUnramifiedDivisibility
section
open scoped MatrixGroups NNReal
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

theorem GlobalTheory.KZ.ramified_divisible_of_unramified : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω] (v : Valuation Ω ℝ≥0) (ψ : O0 p →+* Ω) (E F : ℕ) (π : Ω) (κ : Fin F → Ω), 1 ≤ E → 0 < v (p : Ω) → v (p : Ω) < 1 → v π ^ E = v (p : Ω) → (∀ j, v (κ j) ≤ 1) → (∀ y, v (ψ y) ≤ 1) → (∀ b : Fin F → Lau p, v (∑ j, κ j * ψ (algebraMap (Lau p) (O0 p) (b j))) < 1 → ∀ j, (p : Lau p) ∣ b j) → ∀ b : Fin F → Fin E → Lau p, v (∑ j, ∑ s : Fin E, κ j * π ^ (s : ℕ) * ψ (algebraMap (Lau p) (O0 p) (b j s))) ≤ v (p : Ω) → ∀ j s, (p : Lau p) ∣ b j s := by
  intro p _ Ω _ _ v ψ E F π κ hE hp0 hp1 hπE hκ hψ hunr b htot
  classical
  set a := algebraMap (Lau p) (O0 p) with ha
  set Y : Fin E → Ω := fun s => ∑ j, κ j * ψ (a (b j s)) with hY
  have hsum : (∑ j, ∑ s : Fin E, κ j * π ^ (s : ℕ) * ψ (a (b j s)))
      = ∑ s : Fin E, π ^ (s : ℕ) * Y s := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [hY, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [hsum] at htot

  have hπpos : 0 < v π := by
    rcases eq_or_ne (v π) 0 with h | h
    · exfalso
      have : v π ^ E = 0 := by rw [h]; exact zero_pow (by omega)
      rw [hπE] at this; exact absurd this hp0.ne'
    · exact pos_iff_ne_zero.mpr h
  have hπ1 : v π < 1 := by
    by_contra h
    replace h := not_lt.mp h
    have : 1 ≤ v π ^ E := one_le_pow₀ h
    rw [hπE] at this
    exact absurd hp1 (not_lt.mpr this)
  have hπle : v π ≤ 1 := hπ1.le
  have hY1 : ∀ s, v (Y s) ≤ 1 := by
    intro s
    refine Valuation.map_sum_le v (fun j _ => ?_)
    rw [map_mul]
    calc v (κ j) * v (ψ (a (b j s))) ≤ 1 * 1 := mul_le_mul' (hκ j) (hψ _)
      _ = 1 := one_mul 1
  have hYp : ∀ s, (∀ j, (p : Lau p) ∣ b j s) → v (Y s) ≤ v (p : Ω) := by
    intro s hs
    refine Valuation.map_sum_le v (fun j _ => ?_)
    obtain ⟨c, hc⟩ := hs j
    rw [hc, map_mul, map_mul, map_natCast, map_mul, map_natCast, map_mul]
    calc v (κ j) * (v (p : Ω) * v (ψ (a c))) ≤ 1 * (v (p : Ω) * 1) :=
          mul_le_mul' (hκ j) (mul_le_mul' le_rfl (hψ _))
      _ = v (p : Ω) := by rw [one_mul, mul_one]
  have step : ∀ s : Fin E, (∀ s' : Fin E, s' < s → ∀ j, (p : Lau p) ∣ b j s') →
      ∀ j, (p : Lau p) ∣ b j s := by
    intro s ih
    have hsE : (s : ℕ) + 1 ≤ E := s.isLt
    have hpB : v (p : Ω) ≤ v π ^ ((s : ℕ) + 1) := by
      rw [← hπE]; exact pow_le_pow_of_le_one zero_le hπle hsE
    have hrest : v (∑ s' ∈ Finset.univ.erase s, π ^ (s' : ℕ) * Y s') ≤ v π ^ ((s : ℕ) + 1) := by
      refine Valuation.map_sum_le v (fun s' hs' => ?_)
      have hne : s' ≠ s := Finset.ne_of_mem_erase hs'
      rw [map_mul, map_pow]
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · calc v π ^ (s' : ℕ) * v (Y s') ≤ 1 * v (p : Ω) :=
              mul_le_mul' (pow_le_one₀ zero_le hπle) (hYp s' (ih s' hlt))
          _ ≤ v π ^ ((s : ℕ) + 1) := by rw [one_mul]; exact hpB
      · have hgt' : (s : ℕ) + 1 ≤ (s' : ℕ) := hgt
        calc v π ^ (s' : ℕ) * v (Y s') ≤ v π ^ (s' : ℕ) * 1 := mul_le_mul' le_rfl (hY1 s')
          _ = v π ^ (s' : ℕ) := mul_one _
          _ ≤ v π ^ ((s : ℕ) + 1) := pow_le_pow_of_le_one zero_le hπle hgt'
    have hsplit : π ^ (s : ℕ) * Y s
        = (∑ s' : Fin E, π ^ (s' : ℕ) * Y s') - ∑ s' ∈ Finset.univ.erase s, π ^ (s' : ℕ) * Y s' := by
      rw [← Finset.add_sum_erase Finset.univ (fun s' : Fin E => π ^ (s' : ℕ) * Y s')
        (Finset.mem_univ s)]
      ring
    have hmain : v (π ^ (s : ℕ) * Y s) ≤ v π ^ ((s : ℕ) + 1) := by
      rw [hsplit]
      refine (Valuation.map_sub v _ _).trans (max_le (htot.trans hpB) hrest)
    rw [map_mul, map_pow, pow_succ] at hmain
    have hYs : v (Y s) ≤ v π :=
      le_of_mul_le_mul_left hmain (pow_pos hπpos _)
    exact hunr (fun j => b j s) (lt_of_le_of_lt hYs hπ1)
  intro j s
  exact WellFoundedLT.induction s (fun s ih => step s ih) j
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ResidueTowerPowersLinearIndependent
section
open GlobalTheory.K5

namespace GlobalTheory.K5.ResidueIndep

open Polynomial

theorem field_indep {k : Type} [Field k] (p : ℕ) [hp : Fact p.Prime] [CharP k p] (K : Subfield k)
    (N : ℕ) (t : k) (ha : t ^ p ^ N ∈ K) (hna : ∀ b ∈ K, b ^ p ≠ t ^ p ^ N)
    (c : ℕ → k) (hc : ∀ j < p ^ N, c j ∈ K)
    (hs : ∑ j ∈ Finset.range (p ^ N), c j * t ^ j = 0) : ∀ j < p ^ N, c j = 0 := by
  classical
  haveI : ExpChar K p := ExpChar.prime hp.out
  obtain ⟨n, y, hf⟩ := (minpoly.natSepDegree_eq_one_iff_eq_X_pow_sub_C (F := K) p (x := t)).1
    ((minpoly.natSepDegree_eq_one_iff_pow_mem (F := K) p (x := t)).2 ⟨N, ⟨⟨_, ha⟩, rfl⟩⟩)
  have hy : t ^ p ^ n = (y : k) := by
    have := minpoly.aeval K t
    rw [hf] at this
    simp only [map_sub, map_pow, aeval_X, aeval_C] at this
    exact sub_eq_zero.1 this
  have hNn : N ≤ n := by
    by_contra h
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_lt (not_le.1 h)
    refine hna ((y : k) ^ p ^ r) (K.pow_mem y.2 _) ?_
    rw [← hy, ← pow_mul, ← pow_mul, pow_add, pow_add, pow_one, mul_assoc]
  let c' : ℕ → K := fun j => if h : j < p ^ N then ⟨c j, hc j h⟩ else 0
  let P : K[X] := ∑ j ∈ Finset.range (p ^ N), monomial j (c' j)
  have hP : aeval t P = 0 := by
    rw [← hs, map_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [aeval_monomial]
    simp only [c', dif_pos (Finset.mem_range.1 hj)]
    rfl
  have hP0 : P = 0 := by
    by_contra h
    have h1 := minpoly.degree_le_of_ne_zero K t h hP
    have h2 : P.degree < ((p ^ N : ℕ) : WithBot ℕ) := by
      refine (degree_sum_le _ _).trans_lt ?_
      rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
      intro j hj
      exact (degree_monomial_le _ _).trans_lt (by exact_mod_cast Finset.mem_range.1 hj)
    rw [hf, degree_X_pow_sub_C (pow_pos hp.out.pos n)] at h1
    have h3 := h1.trans_lt h2
    have h4 : p ^ n < p ^ N := by exact_mod_cast h3
    exact absurd (Nat.pow_le_pow_right hp.out.pos hNn) (not_le.2 h4)
  intro j hj
  have h1 : P.coeff j = c' j := by
    simp only [P, finset_sum_coeff, coeff_monomial]
    rw [Finset.sum_ite_eq' , if_pos (Finset.mem_range.2 hj)]
  rw [hP0, coeff_zero] at h1
  have h2 := congrArg Subtype.val h1
  simp only [c', dif_pos hj] at h2
  exact h2.symm

variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem mem_rad_iff (h : IsClo p Ω) (x : integralClosure (O0 p) Ω) :
    x ∈ (Ideal.span {(p : integralClosure (O0 p) Ω)}).radical ↔
      ∃ m : ℕ, 0 < m ∧ IsInt p ((x : Ω) ^ m / (p : Ω)) := by
  haveI := Basic.charZero_of_isClo h
  have hp0 : (p : Ω) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  constructor
  · rintro ⟨n, hn⟩
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 hn
    refine ⟨n + 1, n.succ_pos, ?_⟩
    have h1 : (z : Ω) * p = (x : Ω) ^ n := by exact_mod_cast congrArg Subtype.val hz
    have h2 : (x : Ω) ^ (n + 1) / p = ((z * x : integralClosure (O0 p) Ω) : Ω) := by
      rw [pow_succ, ← h1]; push_cast; field_simp
    rw [h2]
    exact (z * x).2
  · rintro ⟨m, -, hm⟩
    refine ⟨m, Ideal.mem_span_singleton'.2 ⟨⟨_, hm⟩, Subtype.ext ?_⟩⟩
    push_cast
    field_simp

theorem isInt_inv (h : IsClo p Ω) (x : Ω)
    (hx : ¬ ∃ m : ℕ, 0 < m ∧ IsInt p (x ^ m / (p : Ω))) : x ≠ 0 ∧ IsInt p x⁻¹ := by
  haveI := Basic.charZero_of_isClo h
  have hp0 : (p : Ω) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hpi : IsIntegral (O0 p) (p : Ω) := by exact_mod_cast Basic.isInt_intCast (p := p) (Ω := Ω) (p : ℤ)
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hx ⟨1, one_pos, by simpa [IsInt] using isIntegral_zero⟩
  refine ⟨hx0, ?_⟩
  obtain ⟨a, b, hb, h1, h2⟩ := GlobalTheory.T.exists_pow_div_prime_zpow_integralClosure_unit p Ω h x hx0
  by_cases ha : 0 < a
  · exfalso
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, a = (n + 1 : ℕ) := ⟨(a - 1).toNat, by push_cast; omega⟩
    refine hx ⟨b, hb, ?_⟩
    have : x ^ b / (p : Ω) = x ^ b / (p : Ω) ^ ((n + 1 : ℕ) : ℤ) * (p : Ω) ^ n := by
      rw [zpow_natCast]; field_simp; ring
    rw [this]
    exact IsIntegral.mul h1 (hpi.pow n)
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, a = -(n : ℤ) := ⟨(-a).toNat, by omega⟩
    refine IsIntegral.of_pow hb ?_
    have : x⁻¹ ^ b = (p : Ω) ^ (-(n : ℤ)) / x ^ b * (p : Ω) ^ n := by
      rw [zpow_neg, zpow_natCast, inv_pow]; field_simp
    rw [this]
    exact IsIntegral.mul h2 (hpi.pow n)

theorem rad_isMaximal (h : IsClo p Ω) :
    (Ideal.span {(p : integralClosure (O0 p) Ω)}).radical.IsMaximal := by
  haveI := Basic.charZero_of_isClo h
  have hp0 : (p : Ω) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rw [Ideal.isMaximal_iff]
  constructor
  · rw [mem_rad_iff h]
    rintro ⟨m, -, hm⟩
    refine Basic.not_cong_one_zero h 1 one_ne_zero ⟨_, hm, ?_⟩
    simp [hp0]
  · intro J x _ hx hxJ
    rw [mem_rad_iff h] at hx
    obtain ⟨h0, h1⟩ := isInt_inv h _ hx
    have : (1 : integralClosure (O0 p) Ω) = ⟨_, h1⟩ * x :=
      Subtype.ext (inv_mul_cancel₀ h0).symm
    rw [this]
    exact J.mul_mem_left _ hxJ

theorem residue_indep : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ E : Subfield Ω, Set.range (algebraMap (O0 p) Ω) ⊆ (E : Set Ω) →
  (∀ y ∈ E, IsInt p y →
    ¬ ∃ m : ℕ, 0 < m ∧ IsInt p ((y ^ p - algebraMap (O0 p) Ω (qO p)) ^ m / (p : Ω))) →
  ∀ (T : Tower p Ω) (N : ℕ) (d : ℕ → Ω), (∀ j < p ^ N, d j ∈ E ∧ IsInt p (d j)) →
  (∃ m : ℕ, 0 < m ∧ IsInt p ((∑ j ∈ Finset.range (p ^ N), d j * T.qq N ^ j) ^ m / (p : Ω))) →
  ∀ j < p ^ N, ∃ m : ℕ, 0 < m ∧ IsInt p (d j ^ m / (p : Ω)) := by
  intro p hp Ω _ _ h E hE hq T N d hd hs
  classical
  set M := (Ideal.span {(p : integralClosure (O0 p) Ω)}).radical with hM
  have hmem : ∀ x : integralClosure (O0 p) Ω, Ideal.Quotient.mk M x = 0 ↔
      ∃ m : ℕ, 0 < m ∧ IsInt p ((x : Ω) ^ m / (p : Ω)) := fun x => by
    rw [Ideal.Quotient.eq_zero_iff_mem, hM, mem_rad_iff h]
  haveI : M.IsMaximal := rad_isMaximal h
  letI : Field (integralClosure (O0 p) Ω ⧸ M) := Ideal.Quotient.field M
  haveI : CharP (integralClosure (O0 p) Ω ⧸ M) p := by
    rw [CharP.charP_iff_prime_eq_zero hp.out, ← map_natCast (Ideal.Quotient.mk M),
      Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.le_radical (Ideal.mem_span_singleton_self _)
  let K : Subfield (integralClosure (O0 p) Ω ⧸ M) :=
    { (E.toSubring.comap (integralClosure (O0 p) Ω).val.toRingHom).map (Ideal.Quotient.mk M) with
      inv_mem' := by
        rintro _ ⟨y, hy, rfl⟩
        by_cases h0 : Ideal.Quotient.mk M y = 0
        · exact ⟨0, E.zero_mem, by rw [h0, inv_zero, map_zero]⟩
        · obtain ⟨h1, h2⟩ := isInt_inv h (y : Ω) (fun hh => h0 ((hmem y).2 hh))
          refine ⟨⟨_, h2⟩, E.inv_mem hy, ?_⟩
          refine eq_inv_of_mul_eq_one_left ?_
          rw [← map_mul, ← map_one (Ideal.Quotient.mk M)]
          congr 1
          exact Subtype.ext (inv_mul_cancel₀ h1) }
  have hqi : IsIntegral (O0 p) (T.qq N) :=
    IsIntegral.of_pow (pow_pos hp.out.pos N) (by rw [Basic.qq_pow]; exact isIntegral_algebraMap)
  let t : integralClosure (O0 p) Ω := ⟨_, hqi⟩
  have ht : ((t ^ p ^ N : integralClosure (O0 p) Ω) : Ω) = algebraMap (O0 p) Ω (qO p) := by
    rw [← Basic.qq_pow T N]; rfl
  let d' : ℕ → integralClosure (O0 p) Ω := fun j => if hj : j < p ^ N then ⟨d j, (hd j hj).2⟩ else 0
  have hd' : ∀ j < p ^ N, (d' j : Ω) = d j := fun j hj => by simp only [d', dif_pos hj]
  have key := field_indep p K N (Ideal.Quotient.mk M t)
    ⟨t ^ p ^ N, by
      show ((t ^ p ^ N : integralClosure (O0 p) Ω) : Ω) ∈ E
      rw [ht]; exact hE ⟨_, rfl⟩, map_pow _ _ _⟩
    (by
      rintro _ ⟨y, hy, rfl⟩ hb
      refine hq y hy y.2 ?_
      rw [← ht]
      have := (hmem (y ^ p - t ^ p ^ N)).1 (by rw [map_sub, map_pow, map_pow, hb, sub_self])
      exact this)
    (fun j => Ideal.Quotient.mk M (d' j))
    (fun j hj => ⟨d' j, by
      show (d' j : Ω) ∈ E
      rw [hd' j hj]; exact (hd j hj).1, rfl⟩)
    (by
      have e : ((∑ j ∈ Finset.range (p ^ N), d' j * t ^ j : integralClosure (O0 p) Ω) : Ω) =
          ∑ j ∈ Finset.range (p ^ N), d j * T.qq N ^ j := by
        push_cast
        exact Finset.sum_congr rfl fun j hj => by rw [hd' j (Finset.mem_range.1 hj)]
      have := (hmem _).2 (e ▸ hs)
      simpa only [map_sum, map_mul, map_pow] using this)
  intro j hj
  rw [← hd' j hj]
  exact (hmem _).1 (key j hj)

end GlobalTheory.K5.ResidueIndep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerEmbeddingInjective
section
open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

noncomputable section

namespace GlobalTheory.K5.EmbInj

theorem emb_injective : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ (T : Tower p Ω) (n : ℕ), 1 ≤ n → ∀ ι : On p n →ₐ[O0 p] Ω, IsEmb T n ι →
      Function.Injective ι := by
  intro p _ Ω _ _ hc T n hn ι _
  obtain ⟨hdom, -, -⟩ := GlobalTheory.K5.OnDVR.isDVR_On p n hn
  obtain ⟨b, -⟩ := GlobalTheory.K5.OnFree.on_free p n
  haveI : Module.Finite (O0 p) (On p n) := Module.Finite.of_basis b
  haveI : Algebra.IsIntegral (O0 p) (On p n) := Algebra.IsIntegral.of_finite _ _
  rw [injective_iff_map_eq_zero]
  have hker : RingHom.ker (ι : On p n →+* Ω) = ⊥ := by
    apply Ideal.eq_bot_of_comap_eq_bot (R := O0 p)
    rw [eq_bot_iff]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker] at ha
    have : algebraMap (O0 p) Ω a = 0 := by
      rw [← ι.commutes a]; exact ha
    rw [Ideal.mem_bot]
    exact hc.inj (this.trans (map_zero _).symm)
  intro x hx
  have : x ∈ RingHom.ker (ι : On p n →+* Ω) := hx
  rwa [hker, Ideal.mem_bot] at this

end GlobalTheory.K5.EmbInj
end
end

