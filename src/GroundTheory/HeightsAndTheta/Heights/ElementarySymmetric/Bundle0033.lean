import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0032
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.Bundle0011
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.Bundle0010
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.PLevelOneQExpansion
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.PIntSeriesRing
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.Bundle0003

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PHeckeRatioPoly
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open UpperHalfPlane ModularForm GroundTheory.Global.Elliptic Polynomial Filter Topology

noncomputable section

namespace HeckeRatioPoly

theorem exists_poly (p : ℕ) (hp : p.Prime) (k : ℕ) :
    ∃ Q : ℤ[X], ∀ τ : ℍ, (heckeRatios ⟨p, hp.pos⟩ τ).esymm k = aeval (modularJ τ) Q := by
  obtain ⟨hH, hE⟩ := HeckeRatioExpansion.proof IntSeriesRing.proof IntSeriesInv.proof
    DeltaIntSeries.proof (IntSeriesNorm.proof IntSeriesRing.proof) HeckeRatioHolo.proof p hp k
  exact LevelOneQExpansion.proof JQExpansion.proof _ hH
    (fun γ τ ↦ by simp only [HeckeRatioInvariant.proof p hp γ τ]) hE

theorem natDegree_le (hA : JPolyLeading.Statement) {Q : ℤ[X]} {m : ℕ} {L : ℂ}
    (h : Tendsto (fun τ : ℍ ↦ Function.Periodic.qParam 1 τ ^ m * aeval (modularJ τ) Q)
      atImInfty (𝓝 L)) :
    Q.natDegree ≤ m ∧ (Q.natDegree = m → (Q.leadingCoeff : ℂ) = L) := by
  have hq := qParam_tendsto_atImInfty (h := 1) one_pos
  refine ⟨?_, fun hd ↦ ?_⟩
  · by_contra hlt
    rw [not_le] at hlt
    have h1 := (hq.pow (Q.natDegree - m)).mul h
    rw [zero_pow (by omega), zero_mul] at h1
    have h0 : (Q.leadingCoeff : ℂ) = 0 := tendsto_nhds_unique (hA Q) (h1.congr fun τ ↦ by
      rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hlt.le])
    have hQ : Q = 0 := leadingCoeff_eq_zero.1 (by exact_mod_cast h0)
    simp [hQ] at hlt
  · have h2 := hA Q
    rw [hd] at h2
    exact tendsto_nhds_unique h2 h

theorem limit_eq_zero (hA : JPolyLeading.Statement) {Q : ℤ[X]} {m : ℕ} {L : ℂ}
    (h : Tendsto (fun τ : ℍ ↦ Function.Periodic.qParam 1 τ ^ m * aeval (modularJ τ) Q)
      atImInfty (𝓝 L)) (hlt : Q.natDegree < m) : L = 0 := by
  have hq := qParam_tendsto_atImInfty (h := 1) one_pos
  have h1 := (hq.pow (m - Q.natDegree)).mul (hA Q)
  rw [zero_pow (by omega), zero_mul] at h1
  exact tendsto_nhds_unique h (h1.congr fun τ ↦ by
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hlt.le])

end HeckeRatioPoly

open HeckeRatioPoly in

theorem HeckeRatioPoly.proof (hA : JPolyLeading.Statement) (hB : HeckeRatioPoleOrders.Statement) :
    HeckeRatioPoly.Statement := by
  intro p hp hodd
  choose Q hQ using exists_poly p hp
  obtain ⟨h1, h2, h3⟩ := hB p hp hodd
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    rcases hodd with ⟨r, rfl⟩
    omega
  have ht : ∀ k {L : ℂ}, Tendsto (fun τ : ℍ ↦ Function.Periodic.qParam 1 τ ^ (p - 1) *
      (heckeRatios ⟨p, hp.pos⟩ τ).esymm k) atImInfty (𝓝 L) →
      Tendsto (fun τ : ℍ ↦ Function.Periodic.qParam 1 τ ^ (p - 1) * aeval (modularJ τ) (Q k))
        atImInfty (𝓝 L) := fun k _ h ↦ h.congr fun τ ↦ by rw [hQ]
  refine ⟨Q, hQ, fun k hk ↦ ?_, ?_⟩
  · obtain ⟨hle, heq⟩ := natDegree_le hA (ht k (h1 k hk))
    refine lt_of_le_of_ne hle fun hd ↦ ?_
    have hQ0 : Q k = 0 := leadingCoeff_eq_zero.1 (by exact_mod_cast heq hd)
    rw [hQ0, natDegree_zero] at hd
    omega
  · have htp := ht p h2
    obtain ⟨hle, heq⟩ := natDegree_le hA htp
    have hd : (Q p).natDegree = p - 1 :=
      le_antisymm hle (not_lt.1 fun hlt ↦ one_ne_zero (limit_eq_zero hA htp hlt))
    have hl : (Q p).leadingCoeff = 1 := by exact_mod_cast heq hd
    refine ⟨hl, hd, ?_⟩
    have ht3 : Tendsto (fun τ : ℍ ↦ Function.Periodic.qParam 1 τ ^ 0 *
        aeval (modularJ τ) (Q (p + 1))) atImInfty (𝓝 ((p : ℂ) ^ 12)) :=
      h3.congr fun τ ↦ by rw [hQ, pow_zero, one_mul]
    obtain ⟨hle3, heq3⟩ := natDegree_le hA ht3
    have hd3 : (Q (p + 1)).natDegree = 0 := by omega
    have hc := heq3 hd3
    rw [leadingCoeff, hd3] at hc
    rw [eq_C_of_natDegree_eq_zero hd3]
    congr 1
    exact_mod_cast hc

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PJPolyLeading
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open UpperHalfPlane ModularForm GroundTheory.Global.Elliptic Polynomial Filter Topology

noncomputable section

def JPolyLeading.homog (Q : ℤ[X]) (p : ℂ × ℂ) : ℂ :=
  ∑ i ∈ Finset.range (Q.natDegree + 1), (Q.coeff i : ℂ) * p.1 ^ i * p.2 ^ (Q.natDegree - i)

theorem JPolyLeading.continuous_homog (Q : ℤ[X]) : Continuous (JPolyLeading.homog Q) := by
  unfold JPolyLeading.homog
  fun_prop

theorem JPolyLeading.homog_one_zero (Q : ℤ[X]) :
    JPolyLeading.homog Q (1, 0) = (Q.leadingCoeff : ℂ) := by
  unfold JPolyLeading.homog
  rw [Finset.sum_eq_single Q.natDegree]
  · simp only [one_pow, Nat.sub_self, pow_zero, mul_one]
    rfl
  · intro i hi hid
    have : Q.natDegree - i ≠ 0 := by
      have := Finset.mem_range.mp hi
      omega
    simp [zero_pow this]
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self _)) h

theorem JPolyLeading.pow_mul_aeval (Q : ℤ[X]) (q x : ℂ) :
    q ^ Q.natDegree * aeval x Q = JPolyLeading.homog Q (q * x, q) := by
  rw [aeval_eq_sum_range, Finset.mul_sum]
  unfold JPolyLeading.homog
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi' : i ≤ Q.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hd : Q.natDegree = i + (Q.natDegree - i) := (Nat.add_sub_cancel' hi').symm
  conv_lhs => rw [hd]
  rw [zsmul_eq_mul, pow_add, mul_pow]
  dsimp only
  ring

theorem JPolyLeading.proof : JPolyLeading.Statement := by
  intro Q
  obtain ⟨c, hc0, hc⟩ := JQExpansion.proof
  have h1 : Tendsto (fun τ : ℍ ↦ Function.Periodic.qParam 1 τ * modularJ τ) atImInfty (𝓝 1) := by
    have := LevelOneQExpansion.tendsto_of_hasSum (a := PowerSeries.mk c) (B := 0)
      (F := fun τ : ℍ ↦ Function.Periodic.qParam 1 τ * modularJ τ)
      (fun τ _ ↦ by
        have ht : LevelOneQExpansion.term (PowerSeries.mk c) (Function.Periodic.qParam 1 τ) =
            fun n ↦ (c n : ℂ) * Function.Periodic.qParam 1 τ ^ n :=
          funext fun n ↦ by simp [LevelOneQExpansion.term]
        rw [ht]
        exact hc τ)
    simpa [hc0] using this
  have h2 : Tendsto (fun τ : ℍ ↦ Function.Periodic.qParam 1 (τ : ℂ)) atImInfty (𝓝 0) :=
    UpperHalfPlane.qParam_tendsto_atImInfty one_pos
  have h := ((JPolyLeading.continuous_homog Q).tendsto (1, 0)).comp (h1.prodMk_nhds h2)
  rw [JPolyLeading.homog_one_zero] at h
  refine h.congr fun τ ↦ ?_
  simp only [Function.comp_apply]
  exact (JPolyLeading.pow_mul_aeval Q _ _).symm

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
end

