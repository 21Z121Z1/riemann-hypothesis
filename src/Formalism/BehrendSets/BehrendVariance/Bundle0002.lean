import Formalism.BehrendSets.StatementE
import Mathlib
import Formalism.BehrendSets.BehrendVariance.Bundle0001

-- bundled from Formalism.BehrendSets.BehrendVariance.CoeffPowEqZeroOfLt
section
open PowerSeries Finset

noncomputable section

namespace Formalism.BehrendSets.Level3

section General

variable {R : Type*} [CommRing R]

end General

end Formalism.BehrendSets.Level3

namespace Formalism.BehrendSets.Level3

theorem exists_D (Q : ℕ) : ∃ D : ℤ⟦X⟧, D + X * D ^ Q = 1 := by
  set P : ℤ⟦X⟧ := X * (PowerSeries.mk 1) ^ Q with hP
  have hP0 : constantCoeff P = 0 := by simp [hP]
  have hP1' : coeff 1 P = 1 := by
    rw [hP, show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply,
      map_pow]
    simp
  have hP1 : IsUnit (coeff 1 P) := by rw [hP1']; exact isUnit_one
  set y := P.substInvOfIsUnit hP1
  have hy : HasSubst y := HasSubst.substInvOfIsUnit P hP1
  have e1 : subst y P = X := subst_substInvOfIsUnit_right P hP0 hP1
  set φ := substAlgHom (R := ℤ) hy
  have hφ : ∀ f : ℤ⟦X⟧, subst y f = φ f := fun f => by rw [coe_substAlgHom]
  rw [hφ, hP, map_mul, map_pow, ← hφ X, subst_X hy] at e1
  have e2 : φ (PowerSeries.mk 1) * (1 - y) = 1 := by
    have := congrArg φ (mk_one_mul_one_sub_eq_one ℤ)
    rwa [map_mul, map_sub, map_one, ← hφ X, subst_X hy] at this
  refine ⟨1 - y, ?_⟩
  have : X * (1 - y) ^ Q = y := by
    calc X * (1 - y) ^ Q = y * (φ (PowerSeries.mk 1)) ^ Q * (1 - y) ^ Q := by rw [e1]
      _ = y * (φ (PowerSeries.mk 1) * (1 - y)) ^ Q := by rw [mul_pow, mul_assoc]
      _ = y := by rw [e2, one_pow, mul_one]
  rw [this]
  ring

end Formalism.BehrendSets.Level3

namespace Formalism.BehrendSets.Level3

def tOne (Q : ℕ) (c : ℚ) (D : ℚ⟦X⟧) : ℚ⟦X⟧ := X * subst ((X : ℚ⟦X⟧) ^ (Q - 1)) (rescale c D)

end Formalism.BehrendSets.Level3

namespace Formalism.BehrendSets

end Formalism.BehrendSets
end
end

-- bundled from Formalism.BehrendSets.BehrendVariance.MemWindowIff
section
open Finset

noncomputable section

namespace Formalism.BehrendSets.E4

open Formalism.BehrendSets Formalism.BehrendSets.Rand

variable {α : Type} [DecidableEq α]

lemma residue (o j i : ℕ) (hj : j < o) (hd : o ∣ j + i) : (o - i % o) % o = j := by
  have ho : 0 < o := by omega
  have hr : i % o < o := Nat.mod_lt _ ho
  have h0 : (j + i % o) % o = 0 := by
    rw [Nat.add_mod_mod]
    exact Nat.mod_eq_zero_of_dvd hd
  by_cases hlt : j + i % o < o
  · rw [Nat.mod_eq_of_lt hlt] at h0
    have hi0 : i % o = 0 := by omega
    rw [hi0, Nat.sub_zero, Nat.mod_self]
    omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at h0
    rw [Nat.mod_eq_of_lt (by omega)]
    omega

end Formalism.BehrendSets.E4

namespace Formalism.BehrendSets

open Formalism.BehrendSets.Rand Formalism.BehrendSets.E4

end Formalism.BehrendSets
end
end

-- bundled from Formalism.BehrendSets.BehrendVariance.ProdDimVNeZero
section
open Finset Real

noncomputable section

namespace Formalism.BehrendSets.Count

def F (n : ℕ) : ℝ := ∑ i ∈ range n, Real.log ((i.factorial : ℕ) : ℝ)

end Formalism.BehrendSets.Count

namespace Formalism.BehrendSets

open Formalism.BehrendSets.Count

end Formalism.BehrendSets
end
end

-- bundled from Formalism.BehrendSets.BehrendVariance.SpaceFreeOfBehrendFree
section
open Finset Real

noncomputable section

namespace Formalism.BehrendSets.E3

lemma idx_eq {n Lw : ℕ} {h u t : ZMod n} (hord : Lw < addOrderOf h) {y : ℕ} {a b : ℤ}
    (hab : |a - b| ≤ (Lw : ℤ)) (ea : ((y : ℕ) : ZMod n) + u = t + a • h)
    (eb : ((y : ℕ) : ZMod n) + u = t + b • h) : a = b := by
  have hsm : a • h = b • h := by
    have : t + a • h = t + b • h := by rw [← ea, ← eb]
    exact add_left_cancel this
  have hz : (a - b) • h = 0 := by rw [sub_zsmul, hsm]; abel
  have hd : ((addOrderOf h : ℕ) : ℤ) ∣ (a - b) := addOrderOf_dvd_iff_zsmul_eq_zero.mpr hz
  have hlt : |a - b| < ((addOrderOf h : ℕ) : ℤ) := by
    have : (Lw : ℤ) < ((addOrderOf h : ℕ) : ℤ) := by exact_mod_cast hord
    linarith
  exact sub_eq_zero.mp (Int.eq_zero_of_abs_lt_dvd hd hlt)

lemma core {n Lw : ℕ} [NeZero n] {S : Finset ℕ} (hS : ∀ s ∈ S, 4 * Lw * s < n)
    (hF : SpaceFreePos Lw S) {h u t : ZMod n} (hord : Lw < addOrderOf h) {i₁ i₂ i₃ : ℤ}
    (h12 : i₁ < i₂) (h23 : i₂ < i₃) (hw : i₃ - i₁ ≤ (Lw : ℤ))
    (m₁ : t + i₁ • h ∈ thick n S u) (m₂ : t + i₂ • h ∈ thick n S u)
    (m₃ : t + i₃ • h ∈ thick n S u) : False := by
  obtain ⟨y₁, hy₁, e₁⟩ := Thick.mem_thick.mp m₁
  obtain ⟨y₂, hy₂, e₂⟩ := Thick.mem_thick.mp m₂
  obtain ⟨y₃, hy₃, e₃⟩ := Thick.mem_thick.mp m₃
  set D : ℤ := (i₃ - i₁) * ((y₂ : ℤ) - y₁) - (i₂ - i₁) * ((y₃ : ℤ) - y₁) with hDdef
  have hZ : ((D : ℤ) : ZMod n) = 0 := by
    rw [hDdef]
    push_cast
    have e₁' := e₁
    have e₂' := e₂
    have e₃' := e₃
    rw [zsmul_eq_mul] at e₁' e₂' e₃'
    linear_combination ((i₂ : ZMod n) - i₃) * e₁' + ((i₃ : ZMod n) - i₁) * e₂'
      - ((i₂ : ZMod n) - i₁) * e₃'
  have hdvd : (n : ℤ) ∣ D := (ZMod.intCast_zmod_eq_zero_iff_dvd D n).mp hZ
  have bd : ∀ y ∈ S, (4 * (Lw : ℤ)) * (y : ℤ) < (n : ℤ) := by
    intro y hy
    have := hS y hy
    exact_mod_cast this
  have hL : (0 : ℤ) ≤ 4 * (Lw : ℤ) := by positivity
  have d₂ : 4 * (Lw : ℤ) * |(y₂ : ℤ) - y₁| < n :=
    Thick.mul_abs_sub_lt (by positivity) (by positivity) hL (bd y₂ hy₂) (bd y₁ hy₁)
  have d₃ : 4 * (Lw : ℤ) * |(y₃ : ℤ) - y₁| < n :=
    Thick.mul_abs_sub_lt (by positivity) (by positivity) hL (bd y₃ hy₃) (bd y₁ hy₁)
  have ha : |i₂ - i₁| ≤ (Lw : ℤ) := by rw [abs_le]; constructor <;> linarith
  have hb : |i₃ - i₁| ≤ (Lw : ℤ) := by rw [abs_le]; constructor <;> linarith
  have habsD : |D| ≤ |i₃ - i₁| * |(y₂ : ℤ) - y₁| + |i₂ - i₁| * |(y₃ : ℤ) - y₁| := by
    rw [hDdef, ← abs_mul, ← abs_mul]
    exact abs_sub _ _
  have k₁ : |i₃ - i₁| * |(y₂ : ℤ) - y₁| ≤ (Lw : ℤ) * |(y₂ : ℤ) - y₁| :=
    mul_le_mul_of_nonneg_right hb (abs_nonneg _)
  have k₂ : |i₂ - i₁| * |(y₃ : ℤ) - y₁| ≤ (Lw : ℤ) * |(y₃ : ℤ) - y₁| :=
    mul_le_mul_of_nonneg_right ha (abs_nonneg _)
  have hDlt : |D| < (n : ℤ) := by
    have q₁ : 4 * ((Lw : ℤ) * |(y₂ : ℤ) - y₁|) = 4 * (Lw : ℤ) * |(y₂ : ℤ) - y₁| := by ring
    have q₂ : 4 * ((Lw : ℤ) * |(y₃ : ℤ) - y₁|) = 4 * (Lw : ℤ) * |(y₃ : ℤ) - y₁| := by ring
    have : (0 : ℤ) ≤ |D| := abs_nonneg _
    linarith
  have hD0 : D = 0 := Int.eq_zero_of_abs_lt_dvd hdvd hDlt
  by_cases c12 : y₁ = y₂
  · subst c12
    have := idx_eq hord (by rw [abs_sub_comm]; exact ha) e₁ e₂
    linarith
  by_cases c13 : y₁ = y₃
  · subst c13
    have := idx_eq hord (by rw [abs_sub_comm]; exact hb) e₁ e₃
    linarith
  by_cases c23 : y₂ = y₃
  · subst c23
    have h32 : |i₃ - i₂| ≤ (Lw : ℤ) := by rw [abs_le]; constructor <;> linarith
    have := idx_eq hord (by rw [abs_sub_comm]; exact h32) e₂ e₃
    linarith
  exact hF (i₂ - i₁) (i₃ - i₁) (by linarith) (by linarith) hw y₁ hy₁ y₂ hy₂ y₃ hy₃ c12 c13 c23
    (sub_eq_zero.mp hD0)

end Formalism.BehrendSets.E3

namespace Formalism.BehrendSets

end Formalism.BehrendSets
end
end

-- bundled from Formalism.BehrendSets.BehrendVariance.TotientLeOfIsPrimitiveRoot
section
open Polynomial Module Matrix

namespace Formalism.BehrendSets.Stab

theorem totient_le_of_isPrimitiveRoot {E K : Type} [Field E] [NumberField E] [Field K] [Algebra E K]
    [FiniteDimensional E K] {g : ℕ} (hg : 0 < g) {ζ : K} (hζ : IsPrimitiveRoot ζ g) :
    Nat.totient g ≤ finrank ℚ E * finrank E K := by
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap E K).injective
  have : IsScalarTower ℚ E K := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  have : FiniteDimensional ℚ K := Module.Finite.trans E K
  rw [Module.finrank_mul_finrank ℚ E K]
  have h1 := minpoly.natDegree_le (A := ℚ) ζ
  rw [← cyclotomic_eq_minpoly_rat hζ hg, natDegree_cyclotomic] at h1
  exact h1

theorem sub_one_le_of_pow_eq_one {E : Type} [Field E] [NumberField E] {k g : ℕ} (hg : g.Prime)
    (M : Matrix (Fin k) (Fin k) E) (hM : M ^ g = 1) (hM1 : M ≠ 1) :
    g - 1 ≤ finrank ℚ E * k := by
  have := Fact.mk hg
  have hint : IsIntegral E M := IsIntegral.of_finite E M
  have hμ0 : minpoly E M ≠ 0 := minpoly.ne_zero hint
  have hdvd : minpoly E M ∣ cyclotomic g E * (X - 1) := by
    rw [cyclotomic_prime_mul_X_sub_one]
    apply minpoly.dvd
    simp [hM]
  have hnc : ¬ IsCoprime (minpoly E M) (cyclotomic g E) := by
    intro hc
    have h1 : minpoly E M ∣ X - 1 := hc.dvd_of_dvd_mul_left hdvd
    have h2 := aeval_eq_zero_of_dvd_aeval_eq_zero h1 (minpoly.aeval E M)
    apply hM1
    simpa [sub_eq_zero] using h2
  obtain ⟨q, hq, hqμ, hqΦ⟩ : ∃ q, Irreducible q ∧ q ∣ minpoly E M ∧ q ∣ cyclotomic g E := by
    by_contra h
    push Not at h
    exact hnc (isCoprime_of_irreducible_dvd (fun h' => hμ0 h'.1) fun z hz h1 h2 => h z hz h1 h2)
  have hq0 : q ≠ 0 := hq.ne_zero
  have hqdeg : q.natDegree ≤ k := by
    calc q.natDegree ≤ (minpoly E M).natDegree := natDegree_le_of_dvd hqμ hμ0
      _ ≤ M.charpoly.natDegree :=
          natDegree_le_of_dvd (Matrix.minpoly_dvd_charpoly M) (Matrix.charpoly_monic M).ne_zero
      _ = k := by rw [Matrix.charpoly_natDegree_eq_dim]; simp
  have : Fact (Irreducible q) := ⟨hq⟩
  let pb := AdjoinRoot.powerBasis hq0
  have : FiniteDimensional E (AdjoinRoot q) := pb.finite
  have hfin : finrank E (AdjoinRoot q) = q.natDegree := by
    rw [pb.finrank, AdjoinRoot.powerBasis_dim]
  have hroot : aeval (AdjoinRoot.root q) (cyclotomic g E) = 0 :=
    aeval_eq_zero_of_dvd_aeval_eq_zero hqΦ (by rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self])
  have : CharZero (AdjoinRoot q) := charZero_of_injective_algebraMap (algebraMap E _).injective
  have : NeZero (g : AdjoinRoot q) := ⟨Nat.cast_ne_zero.mpr hg.ne_zero⟩
  have hprim : IsPrimitiveRoot (AdjoinRoot.root q) g := by
    rw [← isRoot_cyclotomic_iff, ← map_cyclotomic g (algebraMap E (AdjoinRoot q)), IsRoot,
      eval_map, ← aeval_def]
    exact hroot
  have h3 := totient_le_of_isPrimitiveRoot (E := E) hg.pos hprim
  rw [Nat.totient_prime hg, hfin] at h3
  exact h3.trans (Nat.mul_le_mul_left _ hqdeg)

end Formalism.BehrendSets.Stab

namespace Formalism.BehrendSets

theorem trivStab : TrivStab := by
  intro E _ _ k g hg hdeg Γ hfin hp
  have := Fact.mk hg
  by_contra hne
  have hcard : g ∣ Nat.card Γ := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hp
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hne (Subgroup.card_eq_one.mp (by simpa using hn))
    rw [hn]
    exact dvd_pow_self g hn0
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' g hcard
  have hA : orderOf (x : GL (Fin k) E) = g := by rw [Subgroup.orderOf_coe]; exact hx
  have hMg : ((x : GL (Fin k) E) : Matrix (Fin k) (Fin k) E) ^ g = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hA, pow_orderOf_eq_one, Units.val_one]
  have hM1 : ((x : GL (Fin k) E) : Matrix (Fin k) (Fin k) E) ≠ 1 := by
    intro h
    have h1 : (x : GL (Fin k) E) = 1 := Units.ext h
    rw [h1, orderOf_one] at hA
    exact hg.one_lt.ne hA
  have := Stab.sub_one_le_of_pow_eq_one hg _ hMg hM1
  omega

end Formalism.BehrendSets
end

