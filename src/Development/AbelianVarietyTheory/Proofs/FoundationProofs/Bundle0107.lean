import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0006
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0075
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0083
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0086
import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0087

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowerSeriesAsRatHahnSeriesFractionalQ
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory

theorem powerSeries_to_hahnSeries_rat :
    ∀ (Ω : Type) [Field Ω] (N : ℕ), 0 < N → ∃ Φ : PowerSeries Ω →+* HahnSeries ℚ Ω, (∀ (p : PowerSeries Ω) (k : ℕ), (Φ p).coeff ((k : ℚ) / N) = PowerSeries.coeff k p) ∧ ∀ (p : PowerSeries Ω) (r : ℚ), (∀ k : ℕ, r ≠ (k : ℚ) / N) → (Φ p).coeff r = 0 := by
  intro Ω _ N hN
  have hN' : (0 : ℚ) < N := by exact_mod_cast hN
  let f : ℕ →+ ℚ := (AddMonoidHom.mulRight ((N : ℚ)⁻¹)).comp (Nat.castAddMonoidHom ℚ)
  have hf : ∀ k : ℕ, f k = (k : ℚ) / N := fun k => by
    simp [f, div_eq_mul_inv]
  have hfle : ∀ g g' : ℕ, f g ≤ f g' ↔ g ≤ g' := fun g g' => by
    rw [hf, hf, div_le_div_iff_of_pos_right hN', Nat.cast_le]
  have hfi : Function.Injective f := fun g g' h =>
    le_antisymm ((hfle g g').1 h.le) ((hfle g' g).1 h.ge)
  refine ⟨(HahnSeries.embDomainRingHom f hfi hfle).comp
    (HahnSeries.toPowerSeries (R := Ω)).symm.toRingHom, ?_, ?_⟩
  · intro p k
    rw [← hf]
    simp only [RingHom.comp_apply, HahnSeries.embDomainRingHom_apply]
    rw [HahnSeries.embDomain_mk_coeff]
    rfl
  · intro p r hr
    simp only [RingHom.comp_apply, HahnSeries.embDomainRingHom_apply]
    apply HahnSeries.embDomain_notin_image_support
    rintro ⟨k, -, hk⟩
    exact hr k (by rw [← hf]; exact hk.symm)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrimitiveCharacterEntrySumEisensteinProduct
section
open GlobalTheory.KummerEisensteinGalois GlobalTheory.KummerEisensteinGalois.UnitPiece Finset

namespace GlobalTheory.KummerEisensteinGalois.UnitPieceMu

variable {K : Type} [Field K] [CharZero K]

theorem isUnit_iff_not_dvd_val (p m : ℕ) [Fact p.Prime] (hm : 1 ≤ m) (c : ZMod (p ^ m)) :
    IsUnit c ↔ ¬ p ∣ c.val := by
  have hp : p.Prime := Fact.out
  conv_lhs => rw [← ZMod.natCast_zmod_val c]
  rw [ZMod.isUnit_iff_coprime, Nat.coprime_pow_right_iff (by omega), Nat.coprime_comm, hp.coprime_iff_not_dvd]

theorem isUnit_natCast_of_not_dvd (p m N : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) : IsUnit (N : ZMod (p ^ m)) := by
  have hp : p.Prime := Fact.out
  rw [ZMod.isUnit_iff_coprime]
  exact (hp.coprime_iff_not_dvd.mpr hpN).symm.pow_right m

omit [CharZero K] in

theorem sum_pick (p m N : ℕ) [Fact p.Prime] (hm : 1 ≤ m) (hpN : ¬ p ∣ N) (x z : ℤ) (F : ZMod (p ^ m) → K) :
    ∑ u ∈ primeTo p m, (if z ≡ N * u.val + (p : ℤ) ^ m * x [ZMOD (N * p ^ m : ℕ)] then F u else 0) =
    if ¬ (p : ℤ) ∣ z ∧ z ≡ (p : ℤ) ^ m * x [ZMOD N] then
      F ((z : ZMod (p ^ m)) * Ring.inverse (N : ZMod (p ^ m))) else 0 := by
  have hp : p.Prime := Fact.out
  have hU := isUnit_natCast_of_not_dvd p m N hpN
  have h1 : (N : ZMod (p ^ m)) * Ring.inverse (N : ZMod (p ^ m)) = 1 := Ring.mul_inverse_cancel _ hU
  have hP : (p : ZMod (p ^ m)) ^ m = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
  have hcop : (N : ℤ).natAbs.Coprime ((p ^ m : ℕ) : ℤ).natAbs := by
    simp only [Int.natAbs_natCast]
    exact (hp.coprime_iff_not_dvd.mpr hpN).symm.pow_right m
  have key : ∀ u : ZMod (p ^ m), z ≡ N * u.val + (p : ℤ) ^ m * x [ZMOD (N * p ^ m : ℕ)] ↔
      (u = (z : ZMod (p ^ m)) * Ring.inverse (N : ZMod (p ^ m)) ∧ z ≡ (p : ℤ) ^ m * x [ZMOD N]) := by
    intro u
    rw [Nat.cast_mul, ← Int.modEq_and_modEq_iff_modEq_mul hcop, and_comm]
    refine and_congr ?_ ?_
    · rw [← ZMod.intCast_eq_intCast_iff]
      push_cast
      rw [ZMod.natCast_zmod_val, hP, zero_mul, add_zero]
      constructor
      · intro h; rw [h]; linear_combination (-u) * h1
      · intro h; rw [h]; linear_combination (-(z : ZMod (p ^ m))) * h1
    · rw [Int.modEq_iff_dvd, Int.modEq_iff_dvd, add_sub_assoc]
      exact dvd_add_right (dvd_mul_right _ _)
  have hmem : (z : ZMod (p ^ m)) * Ring.inverse (N : ZMod (p ^ m)) ∈ primeTo p m ↔ ¬ (p : ℤ) ∣ z := by
    rw [primeTo, mem_filter, ← isUnit_iff_not_dvd_val p m hm, ← dvd_val_iff p m hm, ← isUnit_iff_not_dvd_val p m hm,
      IsUnit.mul_iff]
    simp [hU.ringInverse]
  simp only [key]
  by_cases hx : z ≡ (p : ℤ) ^ m * x [ZMOD N]
  · simp only [hx, and_true, sum_ite_eq', hmem]
  · simp [hx]

theorem row_sum (p m N j : ℕ) [Fact p.Prime] (hm : 1 ≤ m) (hpN : ¬ p ∣ N) (ζ : K) (x : ℤ) (s : ZMod (p ^ m) → ℤ)
    (Φ : ZMod (p ^ m) → ZMod (p ^ m) → K) (n : ℕ) :
    ∑ u ∈ primeTo p m, ∑ a : ZMod (p ^ m),
      Φ u a * coefPos j (N * p ^ m) ζ (N * u.val + (p : ℤ) ^ m * x) (s a) n =
    ∑ q ∈ (n : ℤ).divisorsAntidiag, if ¬ (p : ℤ) ∣ q.1 ∧ q.1 ≡ (p : ℤ) ^ m * x [ZMOD N] then
      (q.2.sign : K) * ((q.1 : K) / (N * p ^ m : ℕ)) ^ (j - 1) *
        ∑ a : ZMod (p ^ m), Φ ((q.1 : ZMod (p ^ m)) * Ring.inverse (N : ZMod (p ^ m))) a * ζ ^ (s a * q.2)
      else 0 := by
  have e : ∀ u : ZMod (p ^ m),
      ∑ a : ZMod (p ^ m), Φ u a * coefPos j (N * p ^ m) ζ (N * u.val + (p : ℤ) ^ m * x) (s a) n =
      ∑ q ∈ (n : ℤ).divisorsAntidiag, if q.1 ≡ N * u.val + (p : ℤ) ^ m * x [ZMOD (N * p ^ m : ℕ)] then
        (q.2.sign : K) * ((q.1 : K) / (N * p ^ m : ℕ)) ^ (j - 1) *
          ∑ a : ZMod (p ^ m), Φ u a * ζ ^ (s a * q.2) else 0 := by
    intro u
    simp_rw [coefPos_eq, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun q _ => ?_
    split_ifs
    · exact sum_congr rfl fun a _ => by ring
    · simp
  rw [sum_congr rfl fun u _ => e u, sum_comm]
  refine sum_congr rfl fun q _ => ?_
  exact sum_pick p m N hm hpN x q.1 (fun u => (q.2.sign : K) * ((q.1 : K) / (N * p ^ m : ℕ)) ^ (j - 1) *
    ∑ a : ZMod (p ^ m), Φ u a * ζ ^ (s a * q.2))

theorem col_sum_div (p m N : ℕ) [Fact p.Prime] (hm : 1 ≤ m) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (ψ : DirichletCharacter K (p ^ m)) (hψ : ψ.IsPrimitive) (ζ : K) (hζ : IsPrimitiveRoot ζ (N * p ^ m))
    (n₁ n₂ d d' : ℤ) (h₁ : ¬ (p : ℤ) ∣ n₁) (h₂ : ¬ (p : ℤ) ∣ n₂) :
    ∑ a : ZMod (p ^ m), (∑ b : ZMod (p ^ m),
      ψ ((n₁ : ZMod (p ^ m)) * Ring.inverse (N : ZMod (p ^ m)) * b -
        a * ((n₂ : ZMod (p ^ m)) * Ring.inverse (N : ZMod (p ^ m)))) *
        ζ ^ ((N : ℤ) * b.val * d')) * ζ ^ ((N : ℤ) * a.val * d) =
      if (p : ℤ) ^ m ∣ n₁ * d + n₂ * d' ∧ ¬ (p : ℤ) ∣ d ∧ ¬ (p : ℤ) ∣ d' then
        (p : K) ^ m * gaussS p m ψ (ζ ^ N) * (ψ (n₁ : ZMod (p ^ m)) * ψ⁻¹ (N : ZMod (p ^ m))) *
          ψ⁻¹ (d' : ZMod (p ^ m)) else 0 := by
  have hU := isUnit_natCast_of_not_dvd p m N hpN
  have hI := hU.ringInverse
  have hval : ∀ z : ℤ, ¬ (p : ℤ) ∣ z →
      ¬ (p : ℤ) ∣ ((((z : ZMod (p ^ m)) * Ring.inverse (N : ZMod (p ^ m))).val : ℕ) : ℤ) := by
    intro z hz
    rw [Int.natCast_dvd_natCast, ← isUnit_iff_not_dvd_val p m hm]
    refine IsUnit.mul ?_ hI
    rwa [isUnit_iff_not_dvd_val p m hm, dvd_val_iff p m hm]
  have hdvd : ∀ z : ℤ, (p : ℤ) ^ m ∣ z ↔ (z : ZMod (p ^ m)) = 0 := by
    intro z; rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rfl
  have h := col_sum p m N hm hN ψ hψ ζ hζ 0 0 _ _ d d' (hval n₁ h₁) (hval n₂ h₂)
  simp only [mul_zero, add_zero, zero_mul, zpow_zero, mul_one, hdvd, Int.cast_add, Int.cast_mul, Int.cast_natCast,
    ZMod.natCast_zmod_val] at h
  rw [h, map_mul, ← MulChar.inv_apply]
  refine if_congr (and_congr_left' ?_) rfl rfl
  rw [hdvd, ← hI.mul_left_eq_zero (a := ((n₁ * d + n₂ * d' : ℤ) : ZMod (p ^ m)))]
  push_cast
  constructor <;> intro h <;> linear_combination h

theorem entry_sum (p m N k : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharZero K] (hm : 1 ≤ m) (hN : 0 < N)
    (hpN : ¬ p ∣ N) (_hk : 3 ≤ k) (ψ : DirichletCharacter K (p ^ m)) (hψ : ψ.IsPrimitive) (ζ : K)
    (hζ : IsPrimitiveRoot ζ (N * p ^ m)) (a₀ b₀ t : ℤ) (ht : (p : ℤ) ^ m * t ≡ 1 [ZMOD N]) (i j : ℕ) :
    ∑ u ∈ primeTo p m, ∑ a : ZMod (p ^ m), ∑ v ∈ primeTo p m, ∑ b : ZMod (p ^ m), ψ (u * b - a * v) *
      (coefPos (k - 1) (N * p ^ m) ζ (N * u.val + (p : ℤ) ^ m * (a₀ * t)) (N * a.val) i *
        coefPos 1 (N * p ^ m) ζ (N * v.val + (p : ℤ) ^ m * (b₀ * t)) (N * b.val) j) =
    if p ^ m ∣ i + j then (p : K) ^ m * gaussS p m ψ (ζ ^ N) * ψ⁻¹ (N : ZMod (p ^ m)) *
      (((N * p ^ m : ℕ) : K) ^ (k - 2))⁻¹ * (ffMu N p m k ψ a₀ i * eeMu N p m ψ b₀ j) else 0 := by
  have hx : ∀ c z : ℤ, z ≡ (p : ℤ) ^ m * (c * t) [ZMOD N] ↔ z ≡ c [ZMOD N] := by
    intro c z
    have h : (p : ℤ) ^ m * (c * t) ≡ c [ZMOD N] := by
      have := ht.mul_left c
      rwa [mul_one, mul_left_comm] at this
    exact ⟨fun h' => h'.trans h, fun h' => h'.trans h.symm⟩
  have e1 : ∀ u a : ZMod (p ^ m), ∑ v ∈ primeTo p m, ∑ b : ZMod (p ^ m), ψ (u * b - a * v) *
      (coefPos (k - 1) (N * p ^ m) ζ (N * u.val + (p : ℤ) ^ m * (a₀ * t)) (N * a.val) i *
        coefPos 1 (N * p ^ m) ζ (N * v.val + (p : ℤ) ^ m * (b₀ * t)) (N * b.val) j) =
      (∑ q ∈ (j : ℤ).divisorsAntidiag, if ¬ (p : ℤ) ∣ q.1 ∧ q.1 ≡ b₀ [ZMOD N] then (q.2.sign : K) *
        ∑ b : ZMod (p ^ m), ψ (u * b - a * ((q.1 : ZMod (p ^ m)) * Ring.inverse (N : ZMod (p ^ m)))) *
          ζ ^ ((N : ℤ) * b.val * q.2) else 0) *
      coefPos (k - 1) (N * p ^ m) ζ (N * u.val + (p : ℤ) ^ m * (a₀ * t)) (N * a.val) i := by
    intro u a
    have := row_sum p m N 1 hm hpN ζ (b₀ * t) (fun b => (N : ℤ) * b.val) (fun v b => ψ (u * b - a * v)) j
    simp only [Nat.sub_self, pow_zero, mul_one, hx] at this
    rw [← this]
    simp only [sum_mul]
    exact sum_congr rfl fun v _ => sum_congr rfl fun b _ => by ring
  simp only [e1]
  rw [row_sum p m N (k - 1) hm hpN ζ (a₀ * t) (fun a => (N : ℤ) * a.val)
    (fun u a => ∑ q ∈ (j : ℤ).divisorsAntidiag, if ¬ (p : ℤ) ∣ q.1 ∧ q.1 ≡ b₀ [ZMOD N] then (q.2.sign : K) *
        ∑ b : ZMod (p ^ m), ψ (u * b - a * ((q.1 : ZMod (p ^ m)) * Ring.inverse (N : ZMod (p ^ m)))) *
          ζ ^ ((N : ℤ) * b.val * q.2) else 0) i]
  have e2 : ∀ (c : Prop) [Decidable c] (C : K) (A B : ℤ × ℤ → K),
      (if c then C * ((∑ q ∈ (i : ℤ).divisorsAntidiag, A q) * ∑ q ∈ (j : ℤ).divisorsAntidiag, B q) else 0) =
      ∑ q ∈ (i : ℤ).divisorsAntidiag, ∑ q' ∈ (j : ℤ).divisorsAntidiag, if c then C * (A q * B q') else 0 := by
    intro c _ C A B
    split_ifs
    · rw [sum_mul_sum]; simp only [mul_sum]
    · simp
  rw [ffMu_eq, eeMu_eq, e2]
  refine sum_congr rfl fun q hq => ?_
  simp only [hx]
  by_cases h₁ : (p : ℤ) ∣ q.1
  · simp [h₁]
  by_cases g₁ : q.1 ≡ a₀ [ZMOD N]
  swap
  · simp [g₁]
  rw [if_pos ⟨h₁, g₁⟩]
  simp only [sum_mul (j : ℤ).divisorsAntidiag]
  rw [sum_comm, mul_sum]
  refine sum_congr rfl fun q' hq' => ?_
  by_cases h₂ : (p : ℤ) ∣ q'.1
  · simp [h₂]
  by_cases g₂ : q'.1 ≡ b₀ [ZMOD N]
  swap
  · simp [g₂]
  simp only [if_pos (And.intro h₂ g₂), mul_assoc (q'.2.sign : K)]
  rw [← mul_sum, col_sum_div p m N hm hN hpN ψ hψ ζ hζ q.1 q'.1 q.2 q'.2 h₁ h₂,
    (Int.mem_divisorsAntidiag.mp hq).1, (Int.mem_divisorsAntidiag.mp hq').1]
  have hc : (p : ℤ) ^ m ∣ (i : ℤ) + j ↔ p ^ m ∣ i + j := by norm_cast
  simp only [hc]
  rw [show k - 1 - 1 = k - 2 from rfl, div_pow, div_eq_mul_inv]
  by_cases a1 : p ^ m ∣ i + j <;> by_cases a2 : (p : ℤ) ∣ q.2 <;> by_cases a3 : (p : ℤ) ∣ q'.2 <;>
    simp only [a1, a2, a3, h₁, h₂, g₁, g₂, not_true, not_false_iff, and_true, and_false, and_self, if_true, if_false,
      mul_zero, zero_mul, false_and]
  ring

end GlobalTheory.KummerEisensteinGalois.UnitPieceMu
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrimitiveConstMulOfBoundedExpansion
section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.PrimConst

open NumberField

theorem exists_dividing {Ω : Type} [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω)
    {ι : Type} (c : ι → Ω) (E : IntermediateField ℚ Ω) [FiniteDimensional ℚ E] (D : ℕ) (hD : 0 < D)
    (hc : ∀ i, c i ∈ E ∧ IsIntegral ℤ ((D : Ω) * c i))
    (hne : ∃ i, c i ≠ 0) : ∃ i0, c i0 ≠ 0 ∧ ∀ i, c i * (c i0)⁻¹ ∈ A := by
  classical
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : NumberField E := by
    refine { to_charZero := inferInstance, to_finiteDimensional := ?_ }
    convert ‹FiniteDimensional ℚ E›
    exact Subsingleton.elim _ _
  have hmem : ∀ i, (D : Ω) * c i ∈ E := fun i => E.mul_mem (E.natCast_mem D) (hc i).1
  let f : ι → 𝓞 E := fun i => ⟨⟨(D : Ω) * c i, hmem i⟩, by
      rw [mem_integralClosure_iff]
      exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ E Ω) E.val.injective).1 (hc i).2⟩
  have hf : ∀ i, algebraMap (𝓞 E) Ω (f i) = (D : Ω) * c i := fun i => rfl
  obtain ⟨s0, hs0⟩ : ∃ s0 : Finset ι, ∀ i, f i ∈ Submodule.span ℤ ((s0.image f : Finset (𝓞 E)) : Set (𝓞 E)) := by
    have hN : IsNoetherian ℤ (𝓞 E) := inferInstance
    obtain ⟨M, ⟨s0, rfl⟩, hmax⟩ := set_has_maximal_iff_noetherian.2 hN
      (Set.range fun s : Finset ι => Submodule.span ℤ ((s.image f : Finset (𝓞 E)) : Set (𝓞 E))) (Set.range_nonempty _)
    refine ⟨s0, fun i => ?_⟩
    have hle : Submodule.span ℤ ((s0.image f : Finset (𝓞 E)) : Set (𝓞 E)) ≤
        Submodule.span ℤ (((insert i s0).image f : Finset (𝓞 E)) : Set (𝓞 E)) :=
      Submodule.span_mono (by intro y hy; simp only [Finset.coe_image, Finset.coe_insert] at hy ⊢; exact Set.image_mono (Set.subset_insert _ _) hy)
    have heq := eq_of_le_of_not_lt hle (hmax _ ⟨insert i s0, rfl⟩)
    rw [heq]; exact Submodule.subset_span (by simp)
  set v := A.valuation
  have hDv : v (D : Ω) ≠ 0 := by
    rw [Valuation.ne_zero_iff]; exact Nat.cast_ne_zero.2 hD.ne'
  have hint : ∀ z : ℤ, v (z : Ω) ≤ 1 := fun z => (A.valuation_le_one_iff _).2 (intCast_mem A z)
  obtain ⟨i1, hi1⟩ := hne
  have ht : (s0.filter (fun i => c i ≠ 0)).Nonempty := by
    by_contra hcon
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hcon
    have hz : ∀ y ∈ s0.image f, y = 0 := by
      intro y hy
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hy
      have := hcon hj; push_neg at this
      ext; simp [f, this]
    have h1 := hs0 i1
    rw [Submodule.mem_span_finset] at h1
    obtain ⟨g, -, hg⟩ := h1
    rw [Finset.sum_eq_zero (fun y hy => by rw [hz y hy, smul_zero])] at hg
    have := congrArg (algebraMap (𝓞 E) Ω) hg
    rw [hf, map_zero] at this
    exact hi1 ((mul_eq_zero.1 this.symm).resolve_left (Nat.cast_ne_zero.2 hD.ne'))
  obtain ⟨i0, hi0t, hmax⟩ := (s0.filter (fun i => c i ≠ 0)).exists_max_image (fun i => v (c i)) ht
  have hi0 : c i0 ≠ 0 := (Finset.mem_filter.1 hi0t).2
  have hmax' : ∀ j ∈ s0, v (c j) ≤ v (c i0) := by
    intro j hj
    by_cases hcj : c j = 0
    · rw [hcj, map_zero]; exact zero_le'
    · exact hmax j (Finset.mem_filter.2 ⟨hj, hcj⟩)
  refine ⟨i0, hi0, fun i => ?_⟩
  have h1 := hs0 i
  rw [Submodule.mem_span_finset] at h1
  obtain ⟨g, -, hg⟩ := h1
  have h2 := congrArg (algebraMap (𝓞 E) Ω) hg
  rw [hf, map_sum] at h2
  have hle : v ((D : Ω) * c i) ≤ v (D : Ω) * v (c i0) := by
    rw [← h2]
    refine Valuation.map_sum_le _ (fun y hy => ?_)
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hy
    rw [map_zsmul, hf, zsmul_eq_mul, map_mul, map_mul]
    calc v (g (f j) : Ω) * (v (D : Ω) * v (c j)) ≤ 1 * (v (D : Ω) * v (c j)) := by
          gcongr; exact hint _
      _ ≤ v (D : Ω) * v (c i0) := by rw [one_mul]; gcongr; exact hmax' j hj
  rw [map_mul] at hle
  have hle' : v (c i) ≤ v (c i0) := by
    calc v (c i) = (v (D : Ω))⁻¹ * (v (D : Ω) * v (c i)) := (inv_mul_cancel_left₀ hDv _).symm
      _ ≤ (v (D : Ω))⁻¹ * (v (D : Ω) * v (c i0)) := by gcongr
      _ = v (c i0) := inv_mul_cancel_left₀ hDv _
  have hv0 : v (c i0) ≠ 0 := (Valuation.ne_zero_iff _).2 hi0
  rw [← A.valuation_le_one_iff, map_mul, map_inv₀]
  calc v (c i) * (v (c i0))⁻¹ ≤ v (c i0) * (v (c i0))⁻¹ := by gcongr
    _ = 1 := mul_inv_cancel₀ hv0

theorem prim_of_bounded : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
  ∀ (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), ((l : ℕ) : Ω) ∈ A.nonunits → ∀ a : X.K, a ≠ 0 → (∃ (S : Finset Ω) (D : ℕ), 0 < D ∧ ∀ r, (X.exp a).coeff r ∈ IntermediateField.adjoin ℚ (S : Set Ω) ∧ IsIntegral ℤ ((D : Ω) * (X.exp a).coeff r)) → ∃ κ : Ω, κ ≠ 0 ∧ Prim A (X.exp (algebraMap Ω X.K κ * a)) ∧ ∃ S : Finset Ω, ∀ r, (X.exp (algebraMap Ω X.K κ * a)).coeff r ∈ IntermediateField.adjoin ℚ (S : Set Ω) := by
  intro Ω _ _ _ ε X _ l _ A _ a ha hb
  obtain ⟨S, D, hD, hc⟩ := hb
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ (S : Set Ω)) :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  have hne : ∃ r, (X.exp a).coeff r ≠ 0 := by
    by_contra h
    push_neg at h
    have h0 : X.exp a = 0 := HahnSeries.ext (funext h)
    exact ha ((map_eq_zero_iff X.exp (RingHom.injective X.exp.toRingHom)).1 h0)
  obtain ⟨r0, h0, hA⟩ := exists_dividing A (fun r => (X.exp a).coeff r) _ D hD hc hne
  have hcoef : ∀ (κ : Ω) r, (X.exp (algebraMap Ω X.K κ * a)).coeff r = κ * (X.exp a).coeff r := by
    intro κ r
    rw [map_mul, AlgHom.commutes, HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply, HahnSeries.ofPowerSeries_C, HahnSeries.C_mul_eq_smul,
      HahnSeries.coeff_smul, smul_eq_mul]
  refine ⟨((X.exp a).coeff r0)⁻¹, inv_ne_zero h0, ⟨fun r => ?_, r0, ?_⟩, S, fun r => ?_⟩
  · rw [hcoef, mul_comm]; exact hA r
  · rw [hcoef, inv_mul_cancel₀ h0, inv_one]
    exact ⟨one_ne_zero, one_mem A⟩
  · rw [hcoef]
    exact IntermediateField.mul_mem _ (IntermediateField.inv_mem _ (hc r0).1) (hc r).1

end GlobalTheory.PrimConst
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesCongruenceSubgroupInvMem
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

noncomputable section

namespace GlobalTheory.PsType

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

def congrAlg (ψ : Fin n → kˣ →* ℂˣ) (hψ : Ordered ψ) :
    Subalgebra 𝒪[k] (Matrix (Fin n) (Fin n) 𝒪[k]) where
  carrier := {M | ∀ i j : Fin n, i < j → Triv (ψ i / ψ j) ((M i j : 𝒪[k]) : k)}
  mul_mem' := by
    intro A B hA hB i j hij
    simp only [Set.mem_setOf_eq] at hA hB
    rw [Matrix.mul_apply]
    push_cast
    refine Finset.sum_induction _ (fun x => Triv (ψ i / ψ j) x) (fun x y hx hy => triv_add _ x y hx hy)
      (triv_zero _) ?_
    intro l _
    have hAv : valuation k ((A i l : 𝒪[k]) : k) ≤ 1 := (A i l).2
    have hBv : valuation k ((B l j : 𝒪[k]) : k) ≤ 1 := (B l j).2
    have h1 : valuation k ((A i l : 𝒪[k]) : k) * valuation k ((B l j : 𝒪[k]) : k) ≤
        valuation k ((B l j : 𝒪[k]) : k) := mul_le_of_le_one_left' hAv
    have h2 : valuation k ((A i l : 𝒪[k]) : k) * valuation k ((B l j : 𝒪[k]) : k) ≤
        valuation k ((A i l : 𝒪[k]) : k) := mul_le_of_le_one_right' hBv
    rcases le_or_gt l i with hli | hil
    · refine triv_mono _ ((B l j : 𝒪[k]) : k) _ (by rw [map_mul]; exact h1) ?_
      exact hψ l i j j hli hij.le le_rfl _ (hB l j (lt_of_le_of_lt hli hij))
    rcases le_or_gt j l with hjl | hlj
    · refine triv_mono _ ((A i l : 𝒪[k]) : k) _ (by rw [map_mul]; exact h2) ?_
      exact hψ i i j l le_rfl hij.le hjl _ (hA i l hil)
    · have e : ψ i / ψ l * (ψ l / ψ j) = ψ i / ψ j := div_mul_div_cancel _ _ _
      rw [← e]
      exact triv_mul _ _ _ (triv_mono _ ((A i l : 𝒪[k]) : k) _ (by rw [map_mul]; exact h2) (hA i l hil))
        (triv_mono _ ((B l j : 𝒪[k]) : k) _ (by rw [map_mul]; exact h1) (hB l j hlj))
  one_mem' := by
    intro i j hij
    simp [Matrix.one_apply_ne hij.ne, triv_zero]
  add_mem' := by
    intro A B hA hB i j hij
    simp only [Set.mem_setOf_eq] at hA hB
    simpa using triv_add _ _ _ (hA i j hij) (hB i j hij)
  zero_mem' := by
    intro i j hij
    simp [triv_zero]
  algebraMap_mem' := by
    intro c i j hij
    simp [Matrix.algebraMap_eq_diagonal, Matrix.diagonal_apply_ne _ hij.ne, triv_zero]

theorem inv_val_mem_adjoin {R : Type} [CommRing R] {m : ℕ} (g : GL (Fin m) R) :
    ((g⁻¹ : GL (Fin m) R) : Matrix (Fin m) (Fin m) R) ∈ Algebra.adjoin R {(g : Matrix (Fin m) (Fin m) R)} := by
  set A : Matrix (Fin m) (Fin m) R := (g : Matrix (Fin m) (Fin m) R)
  set p := A.charpoly
  have hCH : Polynomial.aeval A p = 0 := Matrix.aeval_self_charpoly A
  have hdec : p.divX * Polynomial.X + Polynomial.C (p.coeff 0) = p := Polynomial.divX_mul_X_add p
  have hdet : A.det = (-1) ^ Fintype.card (Fin m) * p.coeff 0 := Matrix.det_eq_sign_charpoly_coeff A
  have hu : IsUnit (p.coeff 0) := by
    have h := (Matrix.isUnit_iff_isUnit_det A).mp (Units.isUnit g)
    rw [hdet] at h
    exact isUnit_of_mul_isUnit_right h
  obtain ⟨u, hu⟩ := hu
  have h1 : Polynomial.aeval A p.divX * A = -algebraMap R _ (p.coeff 0) := by
    rw [← hdec] at hCH
    simp only [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C] at hCH
    exact eq_neg_of_add_eq_zero_left hCH
  have key : ((-(↑u⁻¹ : R)) • Polynomial.aeval A p.divX) * A = 1 := by
    rw [smul_mul_assoc, h1, Algebra.algebraMap_eq_smul_one, ← hu, neg_smul_neg, smul_smul,
      Units.inv_mul, one_smul]
  have e : ((g⁻¹ : GL (Fin m) R) : Matrix (Fin m) (Fin m) R) = (-(↑u⁻¹ : R)) • Polynomial.aeval A p.divX :=
    Units.inv_eq_of_mul_eq_one_left key
  rw [e]
  exact Subalgebra.smul_mem _ (Polynomial.aeval_mem_adjoin_singleton R A) _

end GlobalTheory.PsType

open GlobalTheory.PsType in

theorem GlobalTheory.PsType.grp_inv_mem : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ), Ordered ψ → ∀ a ∈ grp ψ, a⁻¹ ∈ grp ψ := by
  intro k _ _ _ _ n ψ hψ a ha
  obtain ⟨haK, hat⟩ := ha
  obtain ⟨g, rfl⟩ := haK
  have hg : (g : Matrix (Fin n) (Fin n) 𝒪[k]) ∈ congrAlg ψ hψ := fun i j hij => hat i j hij
  have hinv : ((g⁻¹ : GL (Fin n) 𝒪[k]) : Matrix (Fin n) (Fin n) 𝒪[k]) ∈ congrAlg ψ hψ :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr hg) (inv_val_mem_adjoin g)
  refine ⟨inv_mem ⟨g, rfl⟩, ?_⟩
  intro i j hij
  rw [← map_inv]
  exact hinv i j hij
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesCongruenceSubgroupIsOpenIsCompact
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

theorem grp_isOpen_isCompact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ), (∀ i, IsSmoothChar (ψ i)) → IsOpen (grp ψ) ∧ IsCompact (grp ψ) := by
  intro k _ _ _ _ n ψ hψ
  have hT := (triv_ev_props k).2.2.2.2.2.1
  have hS : ∀ i j, IsOpen {x : k | Triv (ψ i / ψ j) x} ∧ IsClosed {x : k | Triv (ψ i / ψ j) x} := fun i j => by
    refine hT _ ?_
    rw [div_eq_mul_inv]
    exact (hψ i).mul (hψ j).inv
  have hc : ∀ i j : Fin n, Continuous fun g : GL (Fin n) k => g.val i j := fun i j =>
    by
    have h1 : Continuous fun g : GL (Fin n) k => (g.val : Matrix (Fin n) (Fin n) k) := Units.continuous_val
    exact (continuous_apply j).comp ((continuous_apply i).comp h1)
  have hE : grp ψ = (KO k (Fin n) : Set (GL (Fin n) k)) ∩
      ⋂ i : Fin n, ⋂ j : Fin n, ⋂ (_ : i < j), (fun g : GL (Fin n) k => g.val i j) ⁻¹' {x : k | Triv (ψ i / ψ j) x} := by
    ext g; simp [grp]
  rw [hE]
  refine ⟨GlobalTheory.SplitFlip.isOpen_KO.inter (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      isOpen_iInter_of_finite fun _ => (hS i j).1.preimage (hc i j)), ?_⟩
  exact GlobalTheory.SplitFlip.isCompact_KO.inter_right (isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_iInter fun _ => (hS i j).2.preimage (hc i j))

end GlobalTheory.PsType
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesTypeCharacterRankOnePerturbationStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalSeriesTypeCharacter_rankOne_perturbation : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ) (g : GL (Fin n) k) (p q : Fin n → k) (a : Fin n) (u : kˣ), valuation k (u : k) = 1 → g.val = 1 + Matrix.vecMulVec p q → (∀ i, p i * q i = if i = a then (u : k) - 1 else 0) → theta ψ g = (ψ a u : ℂ) := by
  first | exact @GlobalTheory.PsType.theta_rankOne | exact GlobalTheory.PsType.theta_rankOne | (intros; apply GlobalTheory.PsType.theta_rankOne <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesTypeCharacterTriangularStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalSeriesTypeCharacter_triangular : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ) (g : GL (Fin n) k) (t : Fin n → kˣ), (∀ i, valuation k (t i : k) = 1) → (∀ i, g.val i i = t i) → ((∀ i j : Fin n, i < j → g.val i j = 0) ∨ ∀ i j : Fin n, j < i → g.val i j = 0) → theta ψ g = ∏ i, (ψ i (t i) : ℂ) := by
  first | exact @GlobalTheory.PsType.theta_of_triangular | exact GlobalTheory.PsType.theta_of_triangular | (intros; apply GlobalTheory.PsType.theta_of_triangular <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesTypeConstantFamilyDetCharacterStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalSeriesType_constant_family_det_character : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (χ : kˣ →* ℂˣ), grp (fun _ : Fin n => χ) = (KO k (Fin n) : Set (GL (Fin n) k)) ∧ ∀ g ∈ KO k (Fin n), theta (fun _ : Fin n => χ) g = (detChar (Fin n) χ g : ℂ) := by
  first | exact @GlobalTheory.PsType.const_family_main | exact GlobalTheory.PsType.const_family_main | (intros; apply GlobalTheory.PsType.const_family_main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesTypeDataDependOnlyOnUnitsStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalSeriesType_data_depend_only_on_units : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ ω : Fin n → kˣ →* ℂˣ), Agree ψ ω → grp ψ = grp ω ∧ theta ψ = theta ω ∧ (Ordered ψ → Ordered ω) ∧ ∀ r, Cut ψ r → Cut ω r := by
  first | exact @GlobalTheory.PsType.agree_main | exact GlobalTheory.PsType.agree_main | (intros; apply GlobalTheory.PsType.agree_main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RankLevelDatumIdempotentEqOfSameShapeStatement
section
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_levelDatum_idempotent_eq_of_same_shape : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (ρ : Representation ℂ (GG g N) M), ∀ L L' : Lev g N, L.sharp = L'.sharp → L.s = L'.s → L.k = L'.k → rk ρ L.e = rk ρ L'.e := by
  first | exact @GlobalTheory.BadShare.CoDiag.rk_e_eq | exact GlobalTheory.BadShare.CoDiag.rk_e_eq | (intros; apply GlobalTheory.BadShare.CoDiag.rk_e_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RepresentationRootSubgroupExchangeStatement
section
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.representation_root_subgroup_exchange : ∀ (G : Type) [Group G] [Fintype G] (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (ρ : Representation ℂ G M), ∀ (B X Y : Subgroup G) (χ : G → ℂ), (∀ x ∈ X, x ∈ B → x = 1) → (∀ b ∈ B, ∀ x ∈ X, ∃ x' ∈ X, ∃ b' ∈ B, b * x = x' * b' ∧ χ b' = χ b) → (∀ x ∈ X, ∀ y ∈ Y, y⁻¹ * x⁻¹ * y * x ∈ B) → (∀ x ∈ X, ∀ x' ∈ X, x ≠ x' → ∃ y ∈ Y, χ (y⁻¹ * x⁻¹ * y * x) ≠ χ (y⁻¹ * x'⁻¹ * y * x')) → ∀ (n : ℕ) (v : Fin n → M), LinearIndependent ℂ v → (∀ i, (∀ b ∈ B, ρ b (v i) = χ b • v i) ∧ ∀ y ∈ Y, ρ y (v i) = v i) → ∃ w : Fin n → M, LinearIndependent ℂ w ∧ ∀ i, (∀ b ∈ B, ρ b (w i) = χ b • w i) ∧ ∀ x ∈ X, ρ x (w i) = w i := by
  first | exact @GlobalTheory.BadShare.root_exchange | exact GlobalTheory.BadShare.root_exchange | (intros; apply GlobalTheory.BadShare.root_exchange <;> assumption)
end

