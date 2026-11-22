import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WittVectorRingHomEqMapOfCoeffZero
section
open scoped NNReal

namespace GlobalTheory.WittMapUniq

open WittVector

theorem exists_pow_pow_eq (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] [CharP R l]
    [PerfectRing R l] : ∀ (n : ℕ) (r : R), ∃ s : R, s ^ l ^ n = r := by
  intro n
  induction n with
  | zero => intro r; exact ⟨r, by simp⟩
  | succ n ih =>
    intro r
    obtain ⟨t, ht⟩ := surjective_frobenius R l r
    obtain ⟨s, hs⟩ := ih t
    refine ⟨s, ?_⟩
    rw [pow_succ, pow_mul, hs, ← ht, frobenius_def]

theorem eq_map_of_coeff_zero : ∀ (l : ℕ) [Fact l.Prime] (R O : Type) [CommRing R] [CharP R l]
    [PerfectRing R l] [CommRing O] [CharP O l] [PerfectRing O l]
    (F : WittVector l R →+* WittVector l O) (ψ : R →+* O),
    (∀ a, (F a).coeff 0 = ψ (a.coeff 0)) → F = WittVector.map ψ := by
  intro l _ R O _ _ _ _ _ _ F ψ hF
  have hdiff : ∀ x : WittVector l R, (l : WittVector l O) ∣ F x - WittVector.map ψ x := by
    intro x
    rw [← Ideal.mem_span_singleton, mem_span_p_iff_coeff_zero_eq_zero]
    have h := (WittVector.constantCoeff : WittVector l O →+* O).map_sub (F x) (WittVector.map ψ x)
    simp only [WittVector.constantCoeff_apply] at h
    rw [h, hF, WittVector.map_coeff, sub_self]
  have hteich : ∀ (n : ℕ) (r : R),
      (l : WittVector l O) ^ (n + 1) ∣ F (teichmuller l r) - teichmuller l (ψ r) := by
    intro n r
    obtain ⟨s, rfl⟩ := exists_pow_pow_eq l R n r
    have h1 : (l : WittVector l O) ∣ F (teichmuller l s) - teichmuller l (ψ s) := by
      have := hdiff (teichmuller l s)
      rwa [WittVector.map_teichmuller] at this
    have h2 := dvd_sub_pow_of_dvd_sub h1 n
    rw [map_pow, map_pow, map_pow, map_pow]
    exact h2
  ext x m
  have key : ∀ n : ℕ, F x - WittVector.map ψ x ∈ Ideal.span {((l : WittVector l O) ^ n)} := by
    intro n
    let I : Ideal (WittVector l O) := Ideal.span {((l : WittVector l O) ^ n)}
    have hfg : (Ideal.Quotient.mk I).comp F = (Ideal.Quotient.mk I).comp (WittVector.map ψ) := by
      refine WittVector.eq_of_apply_teichmuller_eq _ _ ⟨n, ?_⟩ ?_
      · rw [← map_natCast (Ideal.Quotient.mk I), ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.subset_span rfl
      · intro r
        simp only [RingHom.comp_apply, WittVector.map_teichmuller]
        rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
        exact dvd_trans (pow_dvd_pow _ n.le_succ) (hteich n r)
    have := congrArg (fun f => f x) hfg
    simp only [RingHom.comp_apply] at this
    exact Ideal.Quotient.eq.mp this
  have h := (mem_span_p_pow_iff_le_coeff_eq_zero _ (m + 1)).mp (key (m + 1))
  have h' := (le_coeff_eq_iff_le_sub_coeff_eq_zero (n := m + 1)).mpr h
  exact h' m (Nat.lt_succ_self m)

end GlobalTheory.WittMapUniq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZRYRCover
section
namespace GlobalTheory.HarmLine

def zR (m n p : ℕ) : Fin (min p m) × Fin n → Fin m × Fin n :=
  fun u => (⟨u.1, lt_of_lt_of_le u.1.2 (min_le_right _ _)⟩, u.2)

def yR (m n p : ℕ) : Fin (m - p) × Fin n → Fin m × Fin n :=
  fun u => (⟨m - 1 - u.1, by have := u.1.2; omega⟩, u.2)

theorem zR_inj (m n p : ℕ) : Function.Injective (zR m n p) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simp only [zR, Prod.mk.injEq, Fin.mk.injEq] at h
  exact Prod.ext (Fin.ext h.1) h.2

theorem yR_inj (m n p : ℕ) : Function.Injective (yR m n p) := by
  rintro ⟨⟨a, ha⟩, b⟩ ⟨⟨c, hc⟩, d⟩ h
  simp only [yR, Prod.mk.injEq, Fin.mk.injEq] at h
  exact Prod.ext (Fin.ext (by simp only; omega)) h.2

theorem zR_ne_yR (m n p : ℕ) (u : Fin (min p m) × Fin n) (v : Fin (m - p) × Fin n) : zR m n p u ≠ yR m n p v := by
  intro h
  simp only [zR, yR, Prod.mk.injEq, Fin.mk.injEq] at h
  have := u.1.2; have := v.1.2
  have := min_le_left p m
  omega

theorem zR_yR_cover (m n p : ℕ) (s : Fin m × Fin n) : (∃ u, zR m n p u = s) ∨ ∃ v, yR m n p v = s := by
  rcases s with ⟨i, a⟩
  by_cases h : (i : ℕ) < p
  · left
    exact ⟨(⟨i, lt_min h i.2⟩, a), rfl⟩
  · right
    refine ⟨(⟨m - 1 - i, by have := i.2; omega⟩, a), ?_⟩
    simp only [yR, Prod.mk.injEq, and_true]
    ext
    simp only
    have := i.2
    omega

end GlobalTheory.HarmLine
end

