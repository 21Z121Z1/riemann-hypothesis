import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalLatticeIsomorphism.LatticeFromNormOne

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalLatticeIsomorphism.IndBasic
section
noncomputable section
open scoped BigOperators
open NumberField

namespace PI.KLW.Ind

open PI.KLW

theorem rp_zero {K : Type} [Field K] [NumberField K] (p : ℕ) : Rp K p 0 :=
  ⟨1, Nat.coprime_one_left p, by rw [mul_zero]; exact zero_mem _⟩

theorem rp_one {K : Type} [Field K] [NumberField K] (p : ℕ) : Rp K p 1 :=
  ⟨1, Nat.coprime_one_left p, by rw [Nat.cast_one, mul_one]; exact one_mem _⟩

theorem rp_add {K : Type} [Field K] [NumberField K] {p : ℕ} {x y : K} (hx : Rp K p x)
    (hy : Rp K p y) : Rp K p (x + y) := by
  obtain ⟨s, hs, hsx⟩ := hx
  obtain ⟨t, ht, hty⟩ := hy
  refine ⟨s * t, Nat.Coprime.mul_left hs ht, ?_⟩
  have e : ((s * t : ℕ) : K) * (x + y) = (t : K) * ((s : K) * x) + (s : K) * ((t : K) * y) := by
    push_cast; ring
  rw [e]
  exact add_mem (mul_mem (natCast_mem _ t) hsx) (mul_mem (natCast_mem _ s) hty)

theorem rp_mul {K : Type} [Field K] [NumberField K] {p : ℕ} {x y : K} (hx : Rp K p x)
    (hy : Rp K p y) : Rp K p (x * y) := by
  obtain ⟨s, hs, hsx⟩ := hx
  obtain ⟨t, ht, hty⟩ := hy
  refine ⟨s * t, Nat.Coprime.mul_left hs ht, ?_⟩
  have e : ((s * t : ℕ) : K) * (x * y) = ((s : K) * x) * ((t : K) * y) := by
    push_cast; ring
  rw [e]
  exact mul_mem hsx hty

theorem rp_neg {K : Type} [Field K] [NumberField K] {p : ℕ} {x : K} (hx : Rp K p x) :
    Rp K p (-x) := by
  obtain ⟨s, hs, hsx⟩ := hx
  exact ⟨s, hs, by rw [mul_neg]; exact neg_mem hsx⟩

theorem hf_add_left {K : Type} [Field K] (c : K →+* K) {ι : Type} [Fintype ι] (v v' w : ι → K) :
    hf c (v + v') w = hf c v w + hf c v' w := by
  simp only [hf, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem hf_add_right {K : Type} [Field K] (c : K →+* K) {ι : Type} [Fintype ι] (v w w' : ι → K) :
    hf c v (w + w') = hf c v w + hf c v w' := by
  simp only [hf, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]

theorem hf_sub_left {K : Type} [Field K] (c : K →+* K) {ι : Type} [Fintype ι] (v v' w : ι → K) :
    hf c (v - v') w = hf c v w - hf c v' w := by
  simp only [hf, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem hf_sub_right {K : Type} [Field K] (c : K →+* K) {ι : Type} [Fintype ι] (v w w' : ι → K) :
    hf c v (w - w') = hf c v w - hf c v w' := by
  simp only [hf, Pi.sub_apply, map_sub, mul_sub, Finset.sum_sub_distrib]

theorem hf_neg_left {K : Type} [Field K] (c : K →+* K) {ι : Type} [Fintype ι] (v w : ι → K) :
    hf c (-v) w = -hf c v w := by
  simp only [hf, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]

theorem hf_neg_right {K : Type} [Field K] (c : K →+* K) {ι : Type} [Fintype ι] (v w : ι → K) :
    hf c v (-w) = -hf c v w := by
  simp only [hf, Pi.neg_apply, map_neg, mul_neg, Finset.sum_neg_distrib]

theorem hf_zero_left {K : Type} [Field K] (c : K →+* K) {ι : Type} [Fintype ι] (w : ι → K) :
    hf c 0 w = 0 := by
  simp only [hf, Pi.zero_apply, zero_mul, Finset.sum_const_zero]

theorem hf_smul_left {K : Type} [Field K] (c : K →+* K) {ι : Type} [Fintype ι] (k : K)
    (v w : ι → K) : hf c (k • v) w = k * hf c v w := by
  simp only [hf, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem hf_smul_right {K : Type} [Field K] (c : K →+* K) {ι : Type} [Fintype ι] (k : K)
    (v w : ι → K) : hf c v (k • w) = c k * hf c v w := by
  simp only [hf, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem hf_conj {K : Type} [Field K] (c : K →+* K) (hc : ∀ x, c (c x) = x) {ι : Type} [Fintype ι]
    (v w : ι → K) : c (hf c v w) = hf c w v := by
  simp only [hf, map_sum, map_mul, hc]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem hf_single_right {K : Type} [Field K] (c : K →+* K) {ι : Type} [Fintype ι] [DecidableEq ι]
    (i0 : ι) (v : ι → K) : hf c v (Pi.single i0 1) = v i0 := by
  unfold hf
  rw [Finset.sum_eq_single i0]
  · rw [Pi.single_eq_same, map_one, mul_one]
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb, map_zero, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem hf_single_left {K : Type} [Field K] (c : K →+* K) {ι : Type} [Fintype ι] [DecidableEq ι]
    (i0 : ι) (w : ι → K) : hf c (Pi.single i0 1) w = c (w i0) := by
  unfold hf
  rw [Finset.sum_eq_single i0]
  · rw [Pi.single_eq_same, one_mul]
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem hf_single_single {K : Type} [Field K] (c : K →+* K) {ι : Type} [Fintype ι]
    [DecidableEq ι] (i0 : ι) : hf c (Pi.single i0 (1 : K)) (Pi.single i0 1) = 1 := by
  rw [hf_single_right, Pi.single_eq_same]

theorem zero_mem_of {K : Type} [Field K] [NumberField K] {c : K →+* K} {p : ℕ} {ι : Type}
    [Fintype ι] {L : Set (ι → K)} (hL : Unimod K c p L) : (0 : ι → K) ∈ L :=
  (hL 0).2 fun w _ => by rw [hf_zero_left]; exact rp_zero p

theorem add_smul_mem {K : Type} [Field K] [NumberField K] {c : K →+* K} {p : ℕ} {ι : Type}
    [Fintype ι] {L : Set (ι → K)} (hL : Unimod K c p L) {a b : ι → K} (ha : a ∈ L) (hb : b ∈ L)
    {r : K} (hr : Rp K p r) : a + r • b ∈ L :=
  (hL _).2 fun w hw => by
    rw [hf_add_left, hf_smul_left]
    exact rp_add ((hL a).1 ha w hw) (rp_mul hr ((hL b).1 hb w hw))

theorem neg_mem_of {K : Type} [Field K] [NumberField K] {c : K →+* K} {p : ℕ} {ι : Type}
    [Fintype ι] {L : Set (ι → K)} (hL : Unimod K c p L) {b : ι → K} (hb : b ∈ L) : -b ∈ L := by
  have h := add_smul_mem hL (zero_mem_of hL) hb (rp_neg (rp_one p))
  rwa [zero_add, neg_one_smul] at h

theorem isom_injective {K : Type} [Field K] (c : K →+* K) {ι : Type} [Fintype ι]
    (f : (ι → K) →ₗ[K] (ι → K)) (hf' : ∀ v w, hf c (f v) (f w) = hf c v w) :
    Function.Injective f := by
  classical
  intro v w hvw
  funext i
  have h := hf' (v - w) (Pi.single i 1)
  rw [map_sub, hvw, sub_self, hf_zero_left, hf_single_right, Pi.sub_apply] at h
  exact sub_eq_zero.mp h.symm

def mkU {K : Type} [Field K] (c : K →+* K) {ι : Type} [Fintype ι]
    (f : (ι → K) →ₗ[K] (ι → K)) (hf' : ∀ v w, hf c (f v) (f w) = hf c v w) :
    (ι → K) ≃ₗ[K] (ι → K) :=
  LinearEquiv.ofInjectiveEndo f (isom_injective c f hf')

theorem mkU_apply {K : Type} [Field K] (c : K →+* K) {ι : Type} [Fintype ι]
    (f : (ι → K) →ₗ[K] (ι → K)) (hf' : ∀ v w, hf c (f v) (f w) = hf c v w) (v : ι → K) :
    mkU c f hf' v = f v := by
  unfold mkU
  rw [LinearEquiv.coe_ofInjectiveEndo]

theorem mkU_unitary {K : Type} [Field K] (c : K →+* K) {ι : Type} [Fintype ι]
    (f : (ι → K) →ₗ[K] (ι → K)) (hf' : ∀ v w, hf c (f v) (f w) = hf c v w) :
    IsUnitary c (mkU c f hf') := fun v w => by
  rw [mkU_apply, mkU_apply]; exact hf' v w

theorem unitary_symm {K : Type} [Field K] {c : K →+* K} {ι : Type} [Fintype ι]
    {u : (ι → K) ≃ₗ[K] (ι → K)} (hu : IsUnitary c u) : IsUnitary c u.symm := fun v w => by
  rw [← hu (u.symm v) (u.symm w), LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

theorem unitary_trans {K : Type} [Field K] {c : K →+* K} {ι : Type} [Fintype ι]
    {u u' : (ι → K) ≃ₗ[K] (ι → K)} (hu : IsUnitary c u) (hu' : IsUnitary c u') :
    IsUnitary c (u.trans u') := fun v w => by
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, hu', hu]

end PI.KLW.Ind
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalLatticeIsomorphism.NormOneP
section
noncomputable section
open scoped BigOperators
open NumberField

namespace PI.KLW

def PairOne : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (c : K →+* K) (p : ℕ) (ι : Type) [Fintype ι] [Nonempty ι]
    (L : Set (ι → K)),
    Module.finrank ℚ K = 2 → (∀ x, c (c x) = x) → p.Prime → SplitK c p →
      Unimod K c p L → Spans K L → ∃ x ∈ L, ∃ y ∈ L, hf c x y = 1

end PI.KLW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalLatticeIsomorphism.RpOfIsIntegral
section
noncomputable section
open scoped BigOperators
open NumberField

namespace PI.KLW

section
variable {K : Type} [Field K] [NumberField K]

theorem mem_range_iff {x : K} : x ∈ (algebraMap (𝓞 K) K).range ↔ IsIntegral ℤ x := by
  constructor
  · rintro ⟨y, rfl⟩
    exact RingOfIntegers.isIntegral_coe y
  · intro h
    exact ⟨⟨x, h⟩, rfl⟩

theorem Rp_of_isIntegral {p : ℕ} {x : K} (h : IsIntegral ℤ x) : Rp K p x :=
  ⟨1, Nat.coprime_one_left p, by rw [Nat.cast_one, one_mul, mem_range_iff]; exact h⟩

theorem Rp_zero {p : ℕ} : Rp K p 0 := Rp_of_isIntegral isIntegral_zero

theorem Rp_one {p : ℕ} : Rp K p 1 := Rp_of_isIntegral isIntegral_one

theorem Rp_natCast {p : ℕ} (m : ℕ) : Rp K p (m : K) := Rp_of_isIntegral (by
  simpa using (isIntegral_algebraMap (R := ℤ) (A := K) (x := (m : ℤ))))

theorem Rp_intCast {p : ℕ} (m : ℤ) : Rp K p (m : K) := Rp_of_isIntegral (by
  simpa using (isIntegral_algebraMap (R := ℤ) (A := K) (x := m)))

theorem Rp_add {p : ℕ} {x y : K} (hx : Rp K p x) (hy : Rp K p y) : Rp K p (x + y) := by
  obtain ⟨s, hs, hsx⟩ := hx
  obtain ⟨t, ht, hty⟩ := hy
  refine ⟨s * t, Nat.Coprime.mul_left hs ht, ?_⟩
  rw [mem_range_iff] at *
  have e : ((s * t : ℕ) : K) * (x + y) = (t : K) * ((s : K) * x) + (s : K) * ((t : K) * y) := by
    push_cast; ring
  rw [e]
  have ht' : IsIntegral ℤ (t : K) := by
    simpa using (isIntegral_algebraMap (R := ℤ) (A := K) (x := (t : ℤ)))
  have hs' : IsIntegral ℤ (s : K) := by
    simpa using (isIntegral_algebraMap (R := ℤ) (A := K) (x := (s : ℤ)))
  exact (ht'.mul hsx).add (hs'.mul hty)

theorem Rp_mul {p : ℕ} {x y : K} (hx : Rp K p x) (hy : Rp K p y) : Rp K p (x * y) := by
  obtain ⟨s, hs, hsx⟩ := hx
  obtain ⟨t, ht, hty⟩ := hy
  refine ⟨s * t, Nat.Coprime.mul_left hs ht, ?_⟩
  rw [mem_range_iff] at *
  have e : ((s * t : ℕ) : K) * (x * y) = ((s : K) * x) * ((t : K) * y) := by
    push_cast; ring
  rw [e]
  exact hsx.mul hty

theorem Rp_neg {p : ℕ} {x : K} (hx : Rp K p x) : Rp K p (-x) := by
  have := Rp_mul (Rp_intCast (K := K) (p := p) (-1)) hx
  simpa using this

theorem Rp_sub {p : ℕ} {x y : K} (hx : Rp K p x) (hy : Rp K p y) : Rp K p (x - y) := by
  simpa [sub_eq_add_neg] using Rp_add hx (Rp_neg hy)

theorem Rp_map {p : ℕ} (c : K →+* K) {x : K} (hx : Rp K p x) : Rp K p (c x) := by
  obtain ⟨s, hs, hsx⟩ := hx
  refine ⟨s, hs, ?_⟩
  rw [mem_range_iff] at *
  have := hsx.map c.toIntAlgHom
  simpa using this

theorem Rp_inv_natCast {p : ℕ} {s : ℕ} (hs : Nat.Coprime s p) : Rp K p ((s : K)⁻¹) := by
  refine ⟨s, hs, ?_⟩
  rw [mem_range_iff]
  by_cases h : (s : K) = 0
  · rw [h, zero_mul]; exact isIntegral_zero
  · rw [mul_inv_cancel₀ h]; exact isIntegral_one

end

section
variable {K : Type} [Field K] {ι : Type} [Fintype ι] (c : K →+* K)

theorem hf_add_left (v v' w : ι → K) : hf c (v + v') w = hf c v w + hf c v' w := by
  simp [hf, add_mul, Finset.sum_add_distrib]

theorem hf_add_right (v w w' : ι → K) : hf c v (w + w') = hf c v w + hf c v w' := by
  simp [hf, mul_add, Finset.sum_add_distrib]

theorem hf_smul_left (a : K) (v w : ι → K) : hf c (a • v) w = a * hf c v w := by
  simp [hf, Finset.mul_sum, mul_assoc]

theorem hf_smul_right (a : K) (v w : ι → K) : hf c v (a • w) = c a * hf c v w := by
  simp only [hf, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem hf_zero_left (w : ι → K) : hf c 0 w = 0 := by simp [hf]

theorem hf_symm (hc : ∀ x, c (c x) = x) (v w : ι → K) : hf c w v = c (hf c v w) := by
  simp only [hf, map_sum, map_mul, hc]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem hf_single_left [DecidableEq ι] (i : ι) (a : K) (w : ι → K) :
    hf c (Pi.single i a) w = a * c (w i) := by
  simp [hf, Pi.single_apply]

end

section
variable {K : Type} [Field K] [NumberField K] {c : K →+* K} {p : ℕ} {ι : Type} [Fintype ι]
  {L : Set (ι → K)}

theorem Unimod.zero_mem (hL : Unimod K c p L) : (0 : ι → K) ∈ L :=
  (hL 0).2 fun w _ => by simpa [hf_zero_left] using (Rp_zero : Rp K p 0)

theorem Unimod.add_mem (hL : Unimod K c p L) {v v' : ι → K} (hv : v ∈ L) (hv' : v' ∈ L) :
    v + v' ∈ L :=
  (hL _).2 fun w hw => by
    rw [hf_add_left]; exact Rp_add ((hL v).1 hv w hw) ((hL v').1 hv' w hw)

theorem Unimod.smul_mem (hL : Unimod K c p L) {a : K} (ha : Rp K p a) {v : ι → K} (hv : v ∈ L) :
    a • v ∈ L :=
  (hL _).2 fun w hw => by
    rw [hf_smul_left]; exact Rp_mul ha ((hL v).1 hv w hw)

theorem Unimod.neg_mem (hL : Unimod K c p L) {v : ι → K} (hv : v ∈ L) : -v ∈ L := by
  simpa using hL.smul_mem (Rp_intCast (-1)) hv

theorem Unimod.sub_mem (hL : Unimod K c p L) {v v' : ι → K} (hv : v ∈ L) (hv' : v' ∈ L) :
    v - v' ∈ L := by
  simpa [sub_eq_add_neg] using hL.add_mem hv (hL.neg_mem hv')

theorem Unimod.hf_mem (hL : Unimod K c p L) {v w : ι → K} (hv : v ∈ L) (hw : w ∈ L) :
    Rp K p (hf c v w) := (hL v).1 hv w hw

end

end PI.KLW
end
end

