import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.AlgebraMapCAt
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0004

-- bundled from Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.ChosenEqOfAllRules
section
noncomputable section

namespace GlobalTheory.SupNormExample

open Formalism.L2.Pj

variable {K : Type} [Field K] {ι : Type} [Fintype ι]
variable (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
variable (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
  (S →ₐ[K] T) → pts S → pts T → Prop)

def conjAt (σ : K →+* ℂ) : CAt σ →ₐ[K] CAt ((starRingEnd ℂ).comp σ) :=
  { (starRingEnd ℂ : ℂ →+* ℂ) with commutes' := fun _ => rfl }

theorem ptNorm_conj (σ : K →+* ℂ) (fn : pts (CAt σ) → ι → ℝ)
    (fn' : pts (CAt ((starRingEnd ℂ).comp σ)) → ι → ℝ) (e : ι → ℕ) (f : Rules pts)
    (y : pts (CAt σ)) (z : pts (CAt ((starRingEnd ℂ).comp σ)))
    (hv : evalAt pts mapR f z = conjAt σ (evalAt pts mapR f y)) (hn : ∀ i, |fn' z i| = |fn y i|) :
    ptNorm pts mapR _ fn' e f z = ptNorm pts mapR σ fn e f y := by
  unfold ptNorm
  rw [hv]
  simp only [hn]
  congr 1
  exact RCLike.norm_conj (K := ℂ) _

theorem bddAt_of_fnorm_zero (σ : K →+* ℂ) (e : ι → ℕ) (i : ι) (hi : e i ≠ 0) (f : Rules pts) :
    BddAt pts mapR σ (fun _ _ => 0) e f ∧ supAt pts mapR σ (fun _ _ => 0) e f = 0 := by
  have h : ∀ y, ptNorm pts mapR σ (fun _ _ => 0) e f y = 0 := fun y => by
    unfold ptNorm
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi]), mul_zero]
  refine ⟨⟨0, ?_⟩, ?_⟩
  · rintro _ ⟨y, rfl⟩; exact (h y).le
  · unfold supAt; simp [h]

theorem exists_fnorm_small (σ : K →+* ℂ) (e : ι → ℕ) (i : ι) (hi : e i ≠ 0) (f : Rules pts) :
    ∃ fnorm : pts (CAt σ) → ι → ℝ, (∀ y j, 0 < fnorm y j) ∧ BddAt pts mapR σ fnorm e f ∧
      supAt pts mapR σ fnorm e f ≤ 1 := by
  classical
  let c : pts (CAt σ) → ℝ := fun y => cabs (evalAt pts mapR f y)
  have hc : ∀ y, 0 ≤ c y := fun y => norm_nonneg _
  have h : ∀ y, ptNorm pts mapR σ (fun y _ => 1 + c y) e f y ≤ 1 := fun y => by
    have hp : 0 < 1 + c y := by linarith [hc y]
    have h1 : (1 + c y)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [hc y])
    have h0 : 0 ≤ (1 + c y)⁻¹ := inv_nonneg.2 hp.le
    show c y * ∏ j, |1 + c y|⁻¹ ^ e j ≤ 1
    rw [abs_of_pos hp, Finset.prod_pow_eq_pow_sum]
    have hs : 1 ≤ ∑ j, e j :=
      (Nat.one_le_iff_ne_zero.2 hi).trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
    have h2 : (1 + c y)⁻¹ ^ ∑ j, e j ≤ (1 + c y)⁻¹ := by
      simpa using pow_le_pow_of_le_one h0 h1 hs
    refine (mul_le_mul_of_nonneg_left h2 (hc y)).trans ?_
    rw [← div_eq_mul_inv, div_le_one hp]; linarith
  refine ⟨fun y _ => 1 + c y, fun y _ => by linarith [hc y], ⟨1, ?_⟩, Real.iSup_le h zero_le_one⟩
  rintro _ ⟨y, rfl⟩; exact h y

end GlobalTheory.SupNormExample
end
end

-- bundled from Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.JetTruncNotInjective
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.JetTest

open MvPolynomial Formalism.L2.Pj

variable {R : Type} [CommRing R] {ι : Type} {m : ℕ}

theorem orig_eq : orig R ι = MvPolynomial.idealOfVars ι R := rfl

theorem mk_eq_zero_iff (p : MvPolynomial ι R) :
    (Ideal.Quotient.mk _ p : Jet R ι m) = 0 ↔ ∀ e : ι →₀ ℕ, e.degree ≤ m → p.coeff e = 0 := by
  rw [Ideal.Quotient.eq_zero_iff_mem, orig_eq, MvPolynomial.mem_pow_idealOfVars_iff']
  simp [Nat.lt_succ_iff]

theorem X_pow_ne_zero [Nontrivial R] (i : ι) :
    (Ideal.Quotient.mk _ (X i ^ m) : Jet R ι m) ≠ 0 := by
  classical
  rw [Ne, mk_eq_zero_iff]
  intro h
  have := h (Finsupp.single i m) (by simp)
  simp [X_pow_eq_monomial] at this

theorem X_pow_succ_eq_zero (i : ι) :
    (Ideal.Quotient.mk _ (X i ^ (m + 1)) : Jet R ι m) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_mem_pow (X_mem_orig i) _)

theorem mem_degLE [Fintype ι] [DecidableEq ι] (e : ι →₀ ℕ) : e ∈ degLE m ↔ e.degree ≤ m := by
  unfold degLE
  rw [Finset.mem_filter]
  have hd : (e.sum fun _ k => k) = e.degree := rfl
  rw [hd]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  refine Finset.mem_image.2 ⟨fun i => ⟨e i, Nat.lt_succ_of_le ((Finsupp.le_degree i e).trans h)⟩,
    Finset.mem_univ _, ?_⟩
  ext i
  simp

theorem coeff_psTrunc [Fintype ι] [DecidableEq ι] (f : MvPowerSeries ι R) (e : ι →₀ ℕ) :
    (psTrunc m f).coeff e = if e.degree ≤ m then MvPowerSeries.coeff e f else 0 := by
  unfold psTrunc
  rw [MvPolynomial.coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  simp [mem_degLE]

theorem psJet_eq_iff [Fintype ι] [DecidableEq ι] (f g : MvPowerSeries ι R) :
    psJet m f = psJet m g ↔
      ∀ e : ι →₀ ℕ, e.degree ≤ m → MvPowerSeries.coeff e f = MvPowerSeries.coeff e g := by
  rw [← sub_eq_zero, psJet, psJet, ← map_sub, mk_eq_zero_iff]
  refine forall_congr' fun e => forall_congr' fun he => ?_
  rw [coeff_sub, coeff_psTrunc, coeff_psTrunc, if_pos he, if_pos he, sub_eq_zero]

theorem jetMap_mk {κ : Type} (φ : ι → MvPolynomial κ R) (hφ : ∀ i, φ i ∈ orig R κ) (p : MvPolynomial ι R) :
    (jetMap (m := m) φ hφ) (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (aeval φ p) := rfl

theorem jetAug_mk (p : MvPolynomial ι R) :
    (jetAug : Jet R ι m →ₐ[R] R) (Ideal.Quotient.mk _ p) = constantCoeff p := by
  change aeval (fun _ => (0 : R)) p = _
  simp

theorem jetTan_X [DecidableEq ι] (l i : ι) :
    (jetTan l : Jet R ι (m + 1) →ₐ[R] DualNumber R) (Ideal.Quotient.mk _ (X i)) =
      if i = l then DualNumber.eps else 0 := by
  change aeval _ (X i) = _
  rw [aeval_X]

theorem jetScale_X (c : ι → R) (i : ι) :
    (jetScale c : Jet R ι m →ₐ[R] Jet R ι m) (Ideal.Quotient.mk _ (X i)) =
      c i • (Ideal.Quotient.mk _ (X i) : Jet R ι m) := by
  rw [jetScale, jetMap_mk, aeval_X, Algebra.smul_def, map_mul]
  rfl

theorem jetTrunc_surjective :
    Function.Surjective (jetTrunc : Jet R ι (m + 1) →ₐ[R] Jet R ι m) := by
  intro a
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact ⟨Ideal.Quotient.mk _ p, rfl⟩

theorem jetTrunc_not_injective [Nontrivial R] (i : ι) :
    ¬ Function.Injective (jetTrunc : Jet R ι (m + 1) →ₐ[R] Jet R ι m) := by
  intro h
  apply X_pow_ne_zero (R := R) (m := m + 1) i
  apply h
  rw [map_zero]
  exact X_pow_succ_eq_zero i

theorem jetSubstPS_add_C {κ : Type} [Fintype κ] [DecidableEq κ] (φ : ι → MvPowerSeries κ R) (c : ι → R) :
    (jetSubstPS (m := m) fun i => φ i + MvPowerSeries.C (c i)) = jetSubstPS (m := m) φ := by
  unfold jetSubstPS
  congr 1
  funext i
  ext e
  simp only [coeff_sub, coeff_psTrunc, constantCoeff_eq, coeff_C, map_add, MvPowerSeries.coeff_C]
  by_cases h : e = 0
  · subst h; simp
  · simp [h, Ne.symm h]

end GlobalTheory.JetTest
end
end

