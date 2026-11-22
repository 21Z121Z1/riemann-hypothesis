import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreePrimeFactor.BigPrimes
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreePrimeFactor.AnaCore

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreePrimeFactor.Analytic
section
noncomputable section

namespace PI.SqfPrimeFactor.W

theorem analytic_of (hRS : PI.PrimesDyadicRS.Claim) : Analytic := by
  intro g r hr hg
  refine ana_main hRS g r hr hg (bigPrimes r) (fun p => ?_)
  simp only [bigPrimes, Finset.mem_filter, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h; exact ⟨by omega, h⟩

end PI.SqfPrimeFactor.W
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreePrimeFactor.ClaimOf
section
open Polynomial

noncomputable section

namespace PI.SqfPrimeFactor.W

open PI.SqfLab

theorem claim_of (hA : CountA) (hB : IrrLower) (hC : Analytic) : PI.SqfPrimeFactor.Claim := by
  intro g r _ hr hg T hT
  refine (hA g r T hT).trans (le_trans ?_ (hC g r hr hg))
  gcongr with p hp
  have hpp : p.Prime := (Finset.mem_filter.1 hp).2.1
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
  rw [div_le_iff₀ hp0]
  have := hB g p hpp
  linarith

end PI.SqfPrimeFactor.W
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreePrimeFactor.IrreducibleCountLowerBound
section
open Polynomial Finset

noncomputable section

namespace PI.SqfPrimeFactor.W

lemma irr_mem_monicDeg {g d : ℕ} [Fact g.Prime] {q : (ZMod g)[X]} (hq : q.Monic)
    (hd : q.natDegree = d) : q ∈ monicDeg g d := by
  unfold monicDeg
  rw [Finset.mem_image]
  refine ⟨fun i => q.coeff i, Finset.mem_univ _, ?_⟩
  subst hd
  rw [Fin.sum_univ_eq_sum_range (fun i => C (q.coeff i) * X ^ i) q.natDegree]
  exact hq.as_sum.symm

theorem irreducible_count_lower_bound : IrrLower := by
  intro g p _ hp
  classical
  let _ : Fintype (GaloisField g p) := Fintype.ofFinite _
  have hp0 : p ≠ 0 := hp.ne_zero
  have hcardK : Fintype.card (GaloisField g p) = g ^ p := by
    rw [← Nat.card_eq_fintype_card]; exact GaloisField.card g p hp0
  have hfin : Module.finrank (ZMod g) (GaloisField g p) = p := GaloisField.finrank g hp0
  have hint : ∀ x : GaloisField g p, IsIntegral (ZMod g) x :=
    fun x => Algebra.IsIntegral.isIntegral x
  set A := (univ : Finset (GaloisField g p)).filter
    (fun x => x ∉ (algebraMap (ZMod g) (GaloisField g p)).range) with hA
  set B := (univ : Finset (GaloisField g p)).filter
    (fun x => x ∈ (algebraMap (ZMod g) (GaloisField g p)).range) with hB
  have hAB : B.card + A.card = g ^ p := by
    rw [hA, hB, card_filter_add_card_filter_not, card_univ, hcardK]
  have hBle : B.card ≤ g := by
    have hsub : B ⊆ (univ : Finset (ZMod g)).image (algebraMap (ZMod g) (GaloisField g p)) := by
      intro x hx
      rw [hB, mem_filter] at hx
      obtain ⟨y, rfl⟩ := hx.2
      exact mem_image_of_mem _ (mem_univ y)
    calc B.card ≤ _ := card_le_card hsub
      _ ≤ (univ : Finset (ZMod g)).card := card_image_le
      _ = g := by rw [card_univ, ZMod.card]
  have hdegA : ∀ x ∈ A, (minpoly (ZMod g) x).natDegree = p := by
    intro x hx
    rw [hA, mem_filter] at hx
    have hdvd := minpoly.degree_dvd (hint x)
    rw [hfin] at hdvd
    rcases (Nat.dvd_prime hp).1 hdvd with h | h
    · exact absurd (minpoly.natDegree_eq_one_iff.1 h) hx.2
    · exact h
  have himg : A.image (minpoly (ZMod g)) ⊆ irrDeg g p := by
    intro q hq
    rw [mem_image] at hq
    obtain ⟨x, hx, rfl⟩ := hq
    unfold irrDeg
    rw [mem_filter]
    exact ⟨irr_mem_monicDeg (minpoly.monic (hint x)) (hdegA x hx), minpoly.irreducible (hint x)⟩
  have hfib : ∀ q ∈ A.image (minpoly (ZMod g)),
      (A.filter (fun x => minpoly (ZMod g) x = q)).card ≤ p := by
    intro q hq
    obtain ⟨x0, hx0, rfl⟩ := mem_image.1 hq
    have hne : (minpoly (ZMod g) x0).map (algebraMap (ZMod g) (GaloisField g p)) ≠ 0 :=
      Polynomial.map_ne_zero (minpoly.ne_zero (hint x0))
    have hsub : A.filter (fun x => minpoly (ZMod g) x = minpoly (ZMod g) x0) ⊆
        ((minpoly (ZMod g) x0).map (algebraMap (ZMod g) (GaloisField g p))).roots.toFinset := by
      intro y hy
      rw [mem_filter] at hy
      rw [Multiset.mem_toFinset, mem_roots hne, IsRoot.def, eval_map_algebraMap, ← hy.2]
      exact minpoly.aeval _ _
    calc _ ≤ _ := card_le_card hsub
      _ ≤ _ := Multiset.toFinset_card_le _
      _ ≤ _ := card_roots' _
      _ = (minpoly (ZMod g) x0).natDegree := natDegree_map _
      _ = p := hdegA x0 hx0
  have hAle : A.card ≤ p * (A.image (minpoly (ZMod g))).card := card_le_mul_card_image A p hfib
  have hAle' : A.card ≤ p * (irrDeg g p).card :=
    hAle.trans (Nat.mul_le_mul_left _ (card_le_card himg))
  have hN : g ^ p ≤ p * (irrDeg g p).card + g := by omega
  have hR : ((g ^ p : ℕ) : ℝ) ≤ ((p * (irrDeg g p).card + g : ℕ) : ℝ) := by exact_mod_cast hN
  push_cast at hR
  linarith

end PI.SqfPrimeFactor.W
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreePrimeFactor.MonicDegFnNatDegree
section
open Polynomial

noncomputable section

namespace PI.SqfPrimeFactor.W

variable {g : ℕ} [Fact g.Prime]

theorem monicDeg_fn_monic (d : ℕ) (c : Fin d → ZMod g) :
    (X ^ d + ∑ i, C (c i) * X ^ (i : ℕ) : (ZMod g)[X]).Monic :=
  monic_X_pow_add (degree_sum_fin_lt c)

theorem monicDeg_fn_natDegree (d : ℕ) (c : Fin d → ZMod g) :
    (X ^ d + ∑ i, C (c i) * X ^ (i : ℕ) : (ZMod g)[X]).natDegree = d := by
  rw [natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
  rw [degree_X_pow]
  exact degree_sum_fin_lt c

theorem monicDeg_fn_coeff (d : ℕ) (c : Fin d → ZMod g) (i : Fin d) :
    (X ^ d + ∑ j, C (c j) * X ^ (j : ℕ) : (ZMod g)[X]).coeff i = c i := by
  rw [coeff_add, coeff_X_pow, if_neg (Nat.ne_of_lt i.is_lt), zero_add, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [if_neg]
    intro h
    exact hj (Fin.ext h).symm
  · simp

theorem mem_monicDeg {d : ℕ} {f : (ZMod g)[X]} :
    f ∈ monicDeg g d ↔ f.Monic ∧ f.natDegree = d := by
  constructor
  · intro hf
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hf
    exact ⟨monicDeg_fn_monic d c, monicDeg_fn_natDegree d c⟩
  · rintro ⟨hm, hd⟩
    refine Finset.mem_image.2 ⟨fun i => f.coeff i, Finset.mem_univ _, ?_⟩
    show X ^ d + ∑ i : Fin d, C (f.coeff i) * X ^ (i : ℕ) = f
    rw [Fin.sum_univ_eq_sum_range (fun i => C (f.coeff i) * X ^ i) d]
    have h := hm.as_sum
    rw [hd] at h
    exact h.symm

theorem card_monicDeg (d : ℕ) : (monicDeg g d).card = g ^ d := by
  unfold monicDeg
  rw [Finset.card_image_of_injective]
  · simp [Finset.card_univ, ZMod.card]
  · intro c c' h
    funext i
    have := congrArg (fun f : (ZMod g)[X] => f.coeff i) h
    simpa only [monicDeg_fn_coeff] using this

open Classical in
theorem mem_irrDeg {d : ℕ} {q : (ZMod g)[X]} :
    q ∈ irrDeg g d ↔ (q.Monic ∧ q.natDegree = d) ∧ Irreducible q := by
  unfold irrDeg
  rw [Finset.mem_filter, mem_monicDeg]

end PI.SqfPrimeFactor.W
end
end

