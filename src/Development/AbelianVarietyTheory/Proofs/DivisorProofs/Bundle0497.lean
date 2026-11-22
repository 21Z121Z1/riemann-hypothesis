import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TiltLatticeBoundSecond
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0228
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0471
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0276
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0235
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0291
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0467
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0466
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0065
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocalRingOfIdem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0151
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0197
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0171
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0125
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0168
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0142
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0460
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0332
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0449
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0477
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TiltLatticeBoundSecondStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tilt_lattice_bound_second : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O →
    ∀ (ε : PreTilt O p), IsPrimitiveRoot (GlobalTheory.Sandwich.root ε).untilt p →
    ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ]
      [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ] (N h : ℕ), h = Module.finrank ℤ_[p] Λ * N →
      ∀ (D : GlobalTheory.Sandwich.Datum ε h Λ) (τ : Λ →+* O),
        (∃! ι, GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps.IsIota C D τ N ι) ∧
          ∀ ι, GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps.IsIota C D τ N ι → Function.Bijective ι := by
  first | exact @GlobalTheory.IotaDet.iota_existsUnique_bijective | exact GlobalTheory.IotaDet.iota_existsUnique_bijective | (intros; apply GlobalTheory.IotaDet.iota_existsUnique_bijective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportPowerSumsModularFamilies
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)

namespace GlobalTheory.QFam

theorem sum_prod_pow_div_pow {ι S : Type} [Fintype ι] [Fintype S] (m μ : S → ℕ) (x : S → ι → ℂ)
    (ω : ℂ) :
    (∑ i, ∏ s, x s i ^ μ s) / ω ^ (∑ s, μ s * m s) = ∑ i, ∏ s, (x s i / ω ^ m s) ^ μ s := by
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [div_pow, Finset.prod_div_distrib, ← pow_mul, Finset.prod_pow_eq_pow_sum]
  simp only [mul_comm]

theorem transport_power_sums : ∀ (g : ℂ ≃+* ℂ) (ι S : Type) [Fintype ι] [Fintype S] (act : ι → SL(2, ℤ) → ι) (N : ℕ) (m : S → ℕ) (f f' : S → ι → ℍ → ℂ) (τ₀ τ₁ : ℍ) (ω₀ ω₁ : ℂ), 0 < N → ActBij act → (∀ s, IsFam act (m s) (f s)) → (∀ s i, QConj g N (f s i) (f' s i)) → g (E₄ τ₀ / ω₀ ^ 4) = E₄ τ₁ / ω₁ ^ 4 → g (E₆ τ₀ / ω₀ ^ 6) = E₆ τ₁ / ω₁ ^ 6 → ∀ μ : S → ℕ, ∑ i, ∏ s, g (f s i τ₀ / ω₀ ^ m s) ^ μ s = ∑ i, ∏ s, (f' s i τ₁ / ω₁ ^ m s) ^ μ s := by
  intro g ι S _ _ act N m f f' τ₀ τ₁ ω₀ ω₁ hN hact hfam hq h4 h6 μ
  obtain ⟨-, -, -, -, hpow, -, hprod, -⟩ := GlobalTheory.T.isSLTwoPermutedModularFamily_algebra_closure ι act
  obtain ⟨-, -, -, -, qpow, qfin⟩ := GlobalTheory.T.qExpansionsCoeffwiseConjugate_ring_closure g N hN
  have hM : IsFam act (((∑ s, μ s * m s : ℕ) : ℤ)) fun i τ => ∏ s, f s i τ ^ μ s := by
    have := hprod S Finset.univ (fun s => (μ s : ℤ) * (m s : ℤ)) (fun s i τ => f s i τ ^ μ s)
      (fun s _ => hpow (m s) (f s) (μ s) (hfam s))
    push_cast
    exact this
  have hQ : QConj g N (fun τ => ∑ i, ∏ s, f s i τ ^ μ s) fun τ => ∑ i, ∏ s, f' s i τ ^ μ s :=
    (qfin ι Finset.univ (fun i τ => ∏ s, f s i τ ^ μ s) (fun i τ => ∏ s, f' s i τ ^ μ s)
      fun i _ => (qfin S Finset.univ (fun s τ => f s i τ ^ μ s) (fun s τ => f' s i τ ^ μ s)
        fun s _ => qpow _ _ (μ s) (hq s i)).2).1
  have key := GlobalTheory.T.levelOne_modularForm_value_galois_transport g (∑ s, μ s * m s) N _ _ τ₀ τ₁ ω₀ ω₁ hN
    (fun γ => (GlobalTheory.T.permutedModularFamily_sum_esymm_slash_invariant ι act _ _ hact hM γ).1) hQ h4 h6
  rw [sum_prod_pow_div_pow m μ (fun s i => f s i τ₀), sum_prod_pow_div_pow m μ (fun s i => f' s i τ₁)] at key
  simpa only [map_sum, map_prod, map_pow] using key

end GlobalTheory.QFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformSerreSections
section
open MvPolynomial

namespace GlobalTheory.UniformSerre

variable {R : Type} [CommRing R] {I : Ideal R} {σ : Type}

noncomputable def comp (e : ℕ) (Q : MvPolynomial σ (reesAlgebra I)) : MvPolynomial σ R :=
  ∑ m ∈ Q.support, monomial m ((coeff m Q).val.coeff e)

theorem coeff_comp (e : ℕ) (Q : MvPolynomial σ (reesAlgebra I)) (m : σ →₀ ℕ) :
    coeff m (comp e Q) = (coeff m Q).val.coeff e := by
  classical
  rw [comp, coeff_sum]
  simp only [coeff_monomial, Finset.sum_ite_eq', mem_support_iff]
  split_ifs with h
  · rfl
  · push_neg at h; rw [h]; simp

open scoped Classical in

noncomputable def liftFun (I : Ideal R) (e : ℕ) (r : R) : reesAlgebra I :=
  if h : r ∈ I ^ e then ⟨Polynomial.monomial e r, (mem_reesAlgebra_iff I _).2 (fun i => by
    rw [Polynomial.coeff_monomial]; split_ifs with hi
    · subst hi; exact h
    · exact zero_mem _)⟩ else 0

theorem liftFun_zero (e : ℕ) : liftFun I e 0 = 0 := by
  unfold liftFun; rw [dif_pos (zero_mem _)]; ext1; simp

noncomputable def lift (I : Ideal R) (e : ℕ) (P : MvPolynomial σ R) : MvPolynomial σ (reesAlgebra I) :=
  ∑ m ∈ P.support, monomial m (liftFun I e (coeff m P))

theorem coeff_lift (e : ℕ) (P : MvPolynomial σ R) (m : σ →₀ ℕ) :
    coeff m (lift I e P) = liftFun I e (coeff m P) := by
  classical
  rw [lift, coeff_sum]
  simp only [coeff_monomial, Finset.sum_ite_eq', mem_support_iff]
  split_ifs with h
  · rfl
  · push_neg at h; rw [h, liftFun_zero]

theorem comp_lift (e e' : ℕ) (P : MvPolynomial σ R) (hP : ∀ m, coeff m P ∈ I ^ e) :
    comp e' (lift I e P) = if e' = e then P else 0 := by
  ext m
  rw [coeff_comp, coeff_lift]
  unfold liftFun; rw [dif_pos (hP m)]
  show (Polynomial.monomial e (coeff m P)).coeff e' = _
  rw [Polynomial.coeff_monomial]
  by_cases h : e' = e
  · subst h; rw [if_pos rfl, if_pos rfl]
  · rw [if_neg (Ne.symm h), if_neg h, coeff_zero]

theorem comp_sub (e : ℕ) (Q₁ Q₂ : MvPolynomial σ (reesAlgebra I)) :
    comp e (Q₁ - Q₂) = comp e Q₁ - comp e Q₂ := by
  ext m; rw [coeff_sub, coeff_comp, coeff_comp, coeff_comp, coeff_sub]
  exact Polynomial.coeff_sub _ _ _

theorem comp_X_pow_mul (e : ℕ) (k : σ) (L : ℕ) (Q : MvPolynomial σ (reesAlgebra I)) :
    comp e (X k ^ L * Q) = X k ^ L * comp e Q := by
  ext m
  rw [coeff_comp, X_pow_eq_monomial, X_pow_eq_monomial, coeff_monomial_mul', coeff_monomial_mul']
  split_ifs <;> simp [coeff_comp]

theorem isHomogeneous_lift {e t : ℕ} {P : MvPolynomial σ R} (hP : P.IsHomogeneous t) :
    (lift I e P).IsHomogeneous t :=
  fun d hd => hP (fun h0 => hd (by rw [coeff_lift, h0, liftFun_zero]))

theorem isHomogeneous_comp {e t : ℕ} {Q : MvPolynomial σ (reesAlgebra I)} (hQ : Q.IsHomogeneous t) :
    (comp e Q).IsHomogeneous t :=
  fun d hd => hQ (fun h0 => hd (by rw [coeff_comp, h0]; simp))

theorem isHomogeneous_sub' {S : Type} [CommRing S] {P Q : MvPolynomial σ S} {t : ℕ}
    (hP : P.IsHomogeneous t) (hQ : Q.IsHomogeneous t) : (P - Q).IsHomogeneous t := by
  rw [← mem_homogeneousSubmodule] at *; exact Submodule.sub_mem _ hP hQ

end GlobalTheory.UniformSerre

open GlobalTheory.UniformSerre in

theorem GlobalTheory.uniform_serre_sections : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), ∀ (n : ℕ) (J : ℕ → Ideal (MvPolynomial (Fin (n + 1)) R)), (∀ (e t : ℕ) (a : R) (F : MvPolynomial (Fin (n + 1)) R), a ∈ I → F.IsHomogeneous t → (∀ m, coeff m F ∈ I ^ e) → F ∈ J e → C a * F ∈ J (e + 1)) → ∃ d₀ : ℕ, ∀ d, d₀ ≤ d → ∀ e : ℕ, ∀ (N : ℕ) (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R), (∀ i, (F i).IsHomogeneous (d + N)) → (∀ i m, coeff m (F i) ∈ I ^ e) → (∀ i j, ∃ L : ℕ, ((X i : MvPolynomial (Fin (n + 1)) R) * X j) ^ L * (X j ^ N * F i - X i ^ N * F j) ∈ J e) → ∃ G : MvPolynomial (Fin (n + 1)) R, G.IsHomogeneous d ∧ (∀ m, coeff m G ∈ I ^ e) ∧ ∀ i, ∃ L : ℕ, (X i : MvPolynomial (Fin (n + 1)) R) ^ L * (F i - X i ^ N * G) ∈ J e := by
  intro R _ _ I n J hJ
  obtain ⟨𝔞, hgr, hmem⟩ := GlobalTheory.T.exists_homogeneous_ideal_over_reesAlgebra R I n J hJ
  obtain ⟨d₀, hd₀⟩ := GlobalTheory.T.exists_homogeneous_form_of_compatible_fractions (reesAlgebra I) n 𝔞 hgr
  refine ⟨d₀, fun d hd e N F hFh hFc hFcomp => ?_⟩
  have hmemiff : ∀ t (H : MvPolynomial (Fin (n+1)) (reesAlgebra I)), H.IsHomogeneous t →
      (H ∈ 𝔞 ↔ ∀ e', comp e' H ∈ J e') := by
    intro t H hH
    rw [hmem t H hH]
    constructor
    · intro h e'; exact h e' _ (fun m => coeff_comp e' H m)
    · intro h e' G hG
      have : G = comp e' H := by ext m; rw [hG m, coeff_comp]
      rw [this]; exact h e'
  obtain ⟨G', hG'h, hG'⟩ := hd₀ d hd N (fun i => lift I e (F i)) (fun i => isHomogeneous_lift (hFh i)) (by
    intro i j
    obtain ⟨L, hL⟩ := hFcomp i j
    refine ⟨L, ?_⟩
    have hhom := ((((isHomogeneous_X (reesAlgebra I) i).mul (isHomogeneous_X _ j)).pow L).mul
      (isHomogeneous_sub' (((isHomogeneous_X _ j).pow N).mul (isHomogeneous_lift (I := I) (e := e) (hFh i)))
        (((isHomogeneous_X _ i).pow N).mul (isHomogeneous_lift (I := I) (e := e) (hFh j)))))
    rw [hmemiff _ _ hhom]
    intro e'
    rw [mul_pow, mul_assoc, comp_X_pow_mul, comp_X_pow_mul, comp_sub, comp_X_pow_mul, comp_X_pow_mul,
      comp_lift _ _ _ (hFc i), comp_lift _ _ _ (hFc j)]
    split_ifs with h
    · subst h; rw [← mul_assoc, ← mul_pow]; exact hL
    · simp)
  refine ⟨comp e G', isHomogeneous_comp hG'h, fun m => ?_, fun i => ?_⟩
  · rw [coeff_comp]; exact (mem_reesAlgebra_iff I _).1 (coeff m G').2 e
  · obtain ⟨L, hL⟩ := hG' i
    refine ⟨L, ?_⟩
    have hhom := ((isHomogeneous_X (reesAlgebra I) i).pow L).mul
      (isHomogeneous_sub' (isHomogeneous_lift (I := I) (e := e) (hFh i))
        (by rw [show d + N = 1 * N + d by ring]; exact ((isHomogeneous_X _ i).pow N).mul hG'h))
    have := (hmemiff _ _ hhom).1 hL e
    rwa [comp_X_pow_mul, comp_sub, comp_X_pow_mul, comp_lift _ _ _ (hFc i), if_pos rfl] at this
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformSerreVanishingCechCocycles
section
open MvPolynomial

namespace GlobalTheory.UniformCocycle

variable {R : Type} [CommRing R] {σ : Type}

noncomputable def proj (I : Ideal R) (e : ℕ) (P : MvPolynomial σ (reesAlgebra I)) :
    MvPolynomial σ R :=
  ∑ m ∈ P.support, monomial m (((coeff m P : reesAlgebra I) : Polynomial R).coeff e)

theorem coeff_proj (I : Ideal R) (e : ℕ) (P : MvPolynomial σ (reesAlgebra I)) (m : σ →₀ ℕ) :
    coeff m (proj I e P) = ((coeff m P : reesAlgebra I) : Polynomial R).coeff e := by
  classical
  simp only [proj, coeff_sum, coeff_monomial, Finset.sum_ite_eq', mem_support_iff]
  split_ifs with h
  · rfl
  · rw [not_not] at h
    simp [h]

theorem proj_add (I : Ideal R) (e : ℕ) (P Q : MvPolynomial σ (reesAlgebra I)) :
    proj I e (P + Q) = proj I e P + proj I e Q := by
  ext m; simp [coeff_proj]

theorem proj_sub (I : Ideal R) (e : ℕ) (P Q : MvPolynomial σ (reesAlgebra I)) :
    proj I e (P - Q) = proj I e P - proj I e Q := by
  ext m; simp [coeff_proj]

theorem proj_X_mul (I : Ideal R) (e : ℕ) (i : σ) (P : MvPolynomial σ (reesAlgebra I)) :
    proj I e (X i * P) = X i * proj I e P := by
  classical
  ext m
  rw [coeff_proj, coeff_X_mul', coeff_X_mul']
  split_ifs <;> simp [coeff_proj]

theorem proj_Xpow_mul (I : Ideal R) (e : ℕ) (i : σ) (k : ℕ) (P : MvPolynomial σ (reesAlgebra I)) :
    proj I e (X i ^ k * P) = X i ^ k * proj I e P := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', mul_assoc, proj_X_mul, ih, ← mul_assoc, ← pow_succ']

open Classical in

noncomputable def liftCoeff (I : Ideal R) (e : ℕ) (r : R) : reesAlgebra I :=
  if h : r ∈ I ^ e then ⟨Polynomial.monomial e r, reesAlgebra.monomial_mem.mpr h⟩ else 0

theorem liftCoeff_zero (I : Ideal R) (e : ℕ) : liftCoeff I e 0 = 0 := by
  unfold liftCoeff
  rw [dif_pos (zero_mem _)]
  apply Subtype.ext; simp

noncomputable def liftE (I : Ideal R) (e : ℕ) (F : MvPolynomial σ R) :
    MvPolynomial σ (reesAlgebra I) :=
  ∑ m ∈ F.support, monomial m (liftCoeff I e (coeff m F))

theorem coeff_liftE (I : Ideal R) (e : ℕ) (F : MvPolynomial σ R) (m : σ →₀ ℕ) :
    coeff m (liftE I e F) = liftCoeff I e (coeff m F) := by
  classical
  simp only [liftE, coeff_sum, coeff_monomial, Finset.sum_ite_eq', mem_support_iff]
  split_ifs with h
  · rfl
  · rw [not_not] at h
    rw [h, liftCoeff_zero]

theorem proj_liftE {I : Ideal R} {e : ℕ} {F : MvPolynomial σ R} (h : ∀ m, coeff m F ∈ I ^ e)
    (e' : ℕ) : proj I e' (liftE I e F) = if e' = e then F else 0 := by
  ext m
  rw [coeff_proj, coeff_liftE, liftCoeff, dif_pos (h m)]
  simp only [Polynomial.coeff_monomial]
  by_cases h1 : e' = e
  · subst h1; simp
  · rw [if_neg (Ne.symm h1), if_neg h1, coeff_zero]

theorem isHomogeneous_liftE {I : Ideal R} {e t : ℕ} {F : MvPolynomial σ R}
    (hF : F.IsHomogeneous t) : (liftE I e F).IsHomogeneous t := by
  intro m hm
  apply hF
  intro h0
  apply hm
  rw [coeff_liftE, h0, liftCoeff_zero]

theorem isHomogeneous_proj {I : Ideal R} {e t : ℕ} {P : MvPolynomial σ (reesAlgebra I)}
    (hP : P.IsHomogeneous t) : (proj I e P).IsHomogeneous t := by
  intro m hm
  apply hP
  intro h0
  apply hm
  rw [coeff_proj, h0]
  simp

end GlobalTheory.UniformCocycle

namespace GlobalTheory

open UniformCocycle in

theorem uniformSerre_cocycle : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), ∀ (n : ℕ) (J : ℕ → Ideal (MvPolynomial (Fin (n + 1)) R)), (∀ (e t : ℕ) (a : R) (F : MvPolynomial (Fin (n + 1)) R), a ∈ I → F.IsHomogeneous t → (∀ m, coeff m F ∈ I ^ e) → F ∈ J e → C a * F ∈ J (e + 1)) → ∃ d₀ : ℕ, ∀ d, d₀ ≤ d → ∀ e : ℕ, ∀ (N : ℕ) (F : Fin (n + 1) → Fin (n + 1) → MvPolynomial (Fin (n + 1)) R), (∀ i j, (F i j).IsHomogeneous (d + 2 * N)) → (∀ i j m, coeff m (F i j) ∈ I ^ e) → (∀ i j l, ∃ L : ℕ, ((X i : MvPolynomial (Fin (n + 1)) R) * X j * X l) ^ L * (X l ^ N * F i j + X i ^ N * F j l - X j ^ N * F i l) ∈ J e) → ∃ (N' : ℕ) (G : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R), (∀ i, (G i).IsHomogeneous (d + N')) ∧ (∀ i m, coeff m (G i) ∈ I ^ e) ∧ ∀ i j, ∃ L : ℕ, ((X i : MvPolynomial (Fin (n + 1)) R) * X j) ^ L * ((X i * X j) ^ N' * F i j - (X i * X j) ^ N * (X j ^ N' * G i - X i ^ N' * G j)) ∈ J e := by
  intro R _ _ I n J hJ
  obtain ⟨𝔞, h𝔞h, h𝔞⟩ := GlobalTheory.T.exists_homogeneous_ideal_over_reesAlgebra R I n J hJ
  obtain ⟨d₀, hd₀⟩ := GlobalTheory.T.exists_coboundary_of_fraction_cocycle_homogeneous_ideal (reesAlgebra I) n 𝔞 h𝔞h
  refine ⟨d₀, fun d hd e N F hFh hFc hcoc => ?_⟩
  have hF'h : ∀ i j, (liftE I e (F i j)).IsHomogeneous (d + 2 * N) :=
    fun i j => isHomogeneous_liftE (hFh i j)
  have hF'p : ∀ e' i j, proj I e' (liftE I e (F i j)) = if e' = e then F i j else 0 :=
    fun e' i j => proj_liftE (hFc i j) e'
  have hcoc' : ∀ i j l, ∃ L : ℕ, ((X i : MvPolynomial (Fin (n + 1)) (reesAlgebra I)) * X j * X l) ^ L *
      (X l ^ N * liftE I e (F i j) + X i ^ N * liftE I e (F j l) - X j ^ N * liftE I e (F i l)) ∈ 𝔞 := by
    intro i j l
    obtain ⟨L, hL⟩ := hcoc i j l
    refine ⟨L, ?_⟩
    have hh := ((((isHomogeneous_X _ i).mul (isHomogeneous_X _ j)).mul (isHomogeneous_X _ l)).pow L).mul
      ((((isHomogeneous_X_pow l N).mul (hF'h i j)).add ((isHomogeneous_X_pow i N).mul (hF'h j l))).sub
        ((isHomogeneous_X_pow j N).mul (hF'h i l)))
    rw [h𝔞 _ _ hh]
    intro e' G hG
    have hGe : G = proj I e' (((X i : MvPolynomial (Fin (n + 1)) (reesAlgebra I)) * X j * X l) ^ L *
      (X l ^ N * liftE I e (F i j) + X i ^ N * liftE I e (F j l) - X j ^ N * liftE I e (F i l))) := by
      ext m; rw [hG, coeff_proj]
    rw [hGe]
    simp only [mul_pow, mul_assoc, proj_add, proj_sub, proj_Xpow_mul, hF'p]
    by_cases he : e' = e
    · subst he
      simp only [↓reduceIte]
      simpa only [mul_pow, mul_assoc] using hL
    · simp [he]
  obtain ⟨N', G', hG'h, hG'⟩ := hd₀ d hd N (fun i j => liftE I e (F i j)) hF'h hcoc'
  refine ⟨N', fun i => proj I e (G' i), fun i => isHomogeneous_proj (hG'h i), fun i m => ?_, fun i j => ?_⟩
  · rw [coeff_proj]
    exact (mem_reesAlgebra_iff I _).mp (coeff m (G' i)).2 e
  · obtain ⟨L, hL⟩ := hG' i j
    refine ⟨L, ?_⟩
    have h2 : (1 + 1) * N + (N' + (d + N')) = (1 + 1) * N' + (d + 2 * N) := by ring
    have hh := (((isHomogeneous_X _ i).mul (isHomogeneous_X _ j)).pow L).mul
      ((((isHomogeneous_X _ i).mul (isHomogeneous_X _ j)).pow N').mul (hF'h i j) |>.sub
        (h2 ▸ (((isHomogeneous_X _ i).mul (isHomogeneous_X _ j)).pow N).mul
          (((isHomogeneous_X_pow j N').mul (hG'h i)).sub ((isHomogeneous_X_pow i N').mul (hG'h j)))))
    rw [h𝔞 _ _ hh] at hL
    have := hL e (proj I e _) (fun m => coeff_proj I e _ m)
    simp only [mul_pow, mul_assoc, proj_add, proj_sub, proj_Xpow_mul, hF'p, ↓reduceIte] at this
    simpa only [mul_pow, mul_assoc] using this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitLemmaLocalAnyResidueCharOfLieAlgebra
section
noncomputable section

namespace GlobalTheory.UnitLemma.UnrAny

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial

section Assembly

variable {K K' : UQ}

def prodEquiv (φ : K.E →+* K'.E) (B₁ B₂ : InvAlg K) (ψ : K'.E →+* (B₁.prod B₂).A)
    (hψ : ∀ e, ψ (φ e) = algebraMap K.E (B₁.prod B₂).A e) (hσ : ∀ e, (B₁.prod B₂).σ (ψ e) = ψ (K'.c e)) :
    ((overExt φ B₁ ((RingHom.fst B₁.A B₂.A).comp ψ) (fun e => congrArg Prod.fst (hψ e))
        (fun e => congrArg Prod.fst (hσ e))).prod
      (overExt φ B₂ ((RingHom.snd B₁.A B₂.A).comp ψ) (fun e => congrArg Prod.snd (hψ e))
        (fun e => congrArg Prod.snd (hσ e)))).A ≃ₐ[K'.E] (overExt φ (B₁.prod B₂) ψ hψ hσ).A :=
  { RingEquiv.refl (B₁.A × B₂.A) with commutes' := fun _ => rfl }

theorem prodEquiv_isIso (φ : K.E →+* K'.E) (B₁ B₂ : InvAlg K) (ψ : K'.E →+* (B₁.prod B₂).A)
    (hψ : ∀ e, ψ (φ e) = algebraMap K.E (B₁.prod B₂).A e) (hσ : ∀ e, (B₁.prod B₂).σ (ψ e) = ψ (K'.c e)) :
    Orbit.IsIso (prodEquiv φ B₁ B₂ ψ hψ hσ) :=
  ⟨fun _ => rfl, rfl⟩

theorem prod_unitary (B₁ B₂ : InvAlg K) (hu₁ : B₁.g * B₁.σ B₁.g = 1) (hu₂ : B₂.g * B₂.σ B₂.g = 1) :
    (B₁.prod B₂).g * (B₁.prod B₂).σ (B₁.prod B₂).g = 1 :=
  Prod.ext hu₁ hu₂

theorem prod_integral (B₁ B₂ : InvAlg K) (hi₁ : IsIntegral K.O B₁.g) (hi₂ : IsIntegral K.O B₂.g) :
    IsIntegral K.O (B₁.prod B₂).g := by
  obtain ⟨p₁, hp₁, e₁⟩ := hi₁
  obtain ⟨p₂, hp₂, e₂⟩ := hi₂
  refine ⟨p₁ * p₂, hp₁.mul hp₂, ?_⟩
  rw [← aeval_def] at e₁ e₂ ⊢
  have h1 : (aeval (B₁.prod B₂).g (p₁ * p₂)).1 = aeval B₁.g (p₁ * p₂) :=
    (aeval_algHom_apply (AlgHom.fst K.O B₁.A B₂.A) (B₁.prod B₂).g (p₁ * p₂)).symm
  have h2 : (aeval (B₁.prod B₂).g (p₁ * p₂)).2 = aeval B₂.g (p₁ * p₂) :=
    (aeval_algHom_apply (AlgHom.snd K.O B₁.A B₂.A) (B₁.prod B₂).g (p₁ * p₂)).symm
  refine Prod.ext ?_ ?_
  · rw [h1, map_mul, e₁, zero_mul]; rfl
  · rw [h2, map_mul, e₂, mul_zero]; rfl

end Assembly

theorem unitLemma_local_of_lie_any : UnitLemmaLie → ∀ (K : UQ) (B₁ B₂ : InvAlg K), B₁.g * B₁.σ B₁.g = 1 → B₂.g * B₂.σ B₂.g = 1 → (B₁.P * B₂.P).Separable → IsIntegral K.O B₁.g → IsIntegral K.O B₂.g → IsLocalRing (Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A)) → InvAlg.Identity B₁ B₂ := by
  intro hL K B₁ B₂ hu₁ hu₂ hsep hi₁ hi₂ hl
  have hsepP : (B₁.prod B₂).P.Separable := by rw [Orbit.prod_P]; exact hsep
  have huP := prod_unitary B₁ B₂ hu₁ hu₂
  have hiP := prod_integral B₁ B₂ hi₁ hi₂
  obtain ⟨d, hd, hcard⟩ := GlobalTheory.T.card_residueField_localOrder_unitary_prod K B₁ B₂ hu₁ hu₂ hsep hi₁ hi₂ hl
  obtain ⟨K', φ, hq, hc, hv, hodd, hfin, hz⟩ := GlobalTheory.T.exists_unramified_odd_degree_quadratic_local_ext K d hd
  have hU : IsUnrExt K K' d φ := ⟨hq, hc, hv, hodd, hfin⟩
  obtain ⟨ψ, hψ, hσ, hO, s, hs, hres⟩ := GlobalTheory.T.exists_unramified_embedding_of_involution_algebra K (B₁.prod B₂) huP hsepP hiP hl d hcard K' φ hU hz
  obtain ⟨Q, hQ1, hQ2⟩ := GlobalTheory.T.charpoly_overExt_integral_reduction_pow K K' d φ hU (B₁.prod B₂) ψ hψ hσ hO hl hsepP hiP s hres
  have hiso := prodEquiv_isIso φ B₁ B₂ ψ hψ hσ
  set ψ₁ := (RingHom.fst B₁.A B₂.A).comp ψ with hψ₁
  set ψ₂ := (RingHom.snd B₁.A B₂.A).comp ψ with hψ₂
  have h₁ : ∀ e, ψ₁ (φ e) = algebraMap K.E B₁.A e := fun e => congrArg Prod.fst (hψ e)
  have h₁' : ∀ e, B₁.σ (ψ₁ e) = ψ₁ (K'.c e) := fun e => congrArg Prod.fst (hσ e)
  have h₂ : ∀ e, ψ₂ (φ e) = algebraMap K.E B₂.A e := fun e => congrArg Prod.snd (hψ e)
  have h₂' : ∀ e, B₂.σ (ψ₂ e) = ψ₂ (K'.c e) := fun e => congrArg Prod.snd (hσ e)
  set C₁ := overExt φ B₁ ψ₁ h₁ h₁' with hC₁
  set C₂ := overExt φ B₂ ψ₂ h₂ h₂' with hC₂
  have hPP : C₁.P * C₂.P = (overExt φ (B₁.prod B₂) ψ hψ hσ).P := by
    rw [← Orbit.prod_P, ← hiso.charpoly_eq_of_isIso]
  have hO₁ : ∀ y : K'.O, ψ₁ (algebraMap K'.O K'.E y) ∈ Algebra.adjoin K.O ({B₁.g} : Set B₁.A) := by
    intro y
    have key : ∀ w ∈ Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A),
        (w : B₁.A × B₂.A).1 ∈ Algebra.adjoin K.O ({B₁.g} : Set B₁.A) := by
      intro w hw
      induction hw using Algebra.adjoin_induction with
      | mem x hx => rw [Set.mem_singleton_iff.1 hx]; exact Algebra.self_mem_adjoin_singleton _ _
      | algebraMap a => exact Subalgebra.algebraMap_mem _ a
      | add x z _ _ hx hz => exact add_mem hx hz
      | mul x z _ _ hx hz => exact mul_mem hx hz
    exact key _ (hO y)
  have hO₂ : ∀ y : K'.O, ψ₂ (algebraMap K'.O K'.E y) ∈ Algebra.adjoin K.O ({B₂.g} : Set B₂.A) := by
    intro y
    have key : ∀ w ∈ Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A),
        (w : B₁.A × B₂.A).2 ∈ Algebra.adjoin K.O ({B₂.g} : Set B₂.A) := by
      intro w hw
      induction hw using Algebra.adjoin_induction with
      | mem x hx => rw [Set.mem_singleton_iff.1 hx]; exact Algebra.self_mem_adjoin_singleton _ _
      | algebraMap a => exact Subalgebra.algebraMap_mem _ a
      | add x z _ _ hx hz => exact add_mem hx hz
      | mul x z _ _ hx hz => exact mul_mem hx hz
    exact key _ (hO y)
  have hO' : ∀ y : K'.O, (ψ₁.prod ψ₂) (algebraMap K'.O K'.E y) ∈
      Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A) := fun y => hO y
  have hQ : ∃ Q : K'.O[X], Q.map (algebraMap K'.O K'.E) = C₁.P * C₂.P ∧
      Q.map (IsLocalRing.residue K'.O) = (X - C (IsLocalRing.residue K'.O (s : K'.O))) ^ Q.natDegree :=
    ⟨Q, hQ1.trans hPP.symm, hQ2⟩

  have hsep' : (C₁.P * C₂.P).Separable := by
    rw [hPP]
    exact GlobalTheory.T.separable_charpoly_invAlgBaseChangeUnramified K K' d φ hU (B₁.prod B₂) ψ hψ hσ hsepP
  have hId := GlobalTheory.T.unitLemma_residuallyUnipotent_cayleyTransform hL K' C₁ C₂ hu₁ hu₂ hsep' s hs hQ

  have hst : ∀ (B : InvAlg K) (ψ : K'.E →+* B.A) (hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e)
      (hσ : ∀ e, B.σ (ψ e) = ψ (K'.c e)),
      (∀ y : K'.O, ψ (algebraMap K'.O K'.E y) ∈ Algebra.adjoin K.O ({B.g} : Set B.A)) →
      (overExt φ B ψ hψ hσ).stSum = B.stSum := by
    intro B ψ hψ hσ hO'
    unfold InvAlg.stSum
    exact finsum_congr fun k => GlobalTheory.T.unramifiedBaseChange_latticeCount_eq K K' d φ hU B ψ hψ hσ hO' _
  have hkap : InvAlg.kapSum C₁ C₂ = InvAlg.kapSum B₁ B₂ := by
    unfold InvAlg.kapSum
    refine finsum_congr fun k => ?_
    have hN : (C₁.prod C₂).N k.rep = (B₁.prod B₂).N k.rep := by
      rw [← hiso.N_eq]
      exact GlobalTheory.T.unramifiedBaseChange_latticeCount_eq K K' d φ hU (B₁.prod B₂) ψ hψ hσ hO _
    rw [hN]
    congr 1
    set x := (Quot.out k).1 with hx
    have hfix : B₁.σ ((x : (C₁.prod C₂).A).1) = (x : (C₁.prod C₂).A).1 := congrArg Prod.fst (Quot.out k).2
    let x₁ : B₁.Aˣ := Units.map (MonoidHom.fst B₁.A B₂.A) x
    have := GlobalTheory.T.eta_gramDet_invAlgBaseChangeUnramified_odd K K' d φ hU hd B₁ ψ₁ h₁ h₁' x₁ hfix
    exact this
  have hres' := GlobalTheory.T.val_resultant_eq_degree_mul_unramifiedExt K K' d φ hU hd B₁ B₂ ψ₁ ψ₂ h₁ h₁' h₂ h₂' hO' hsep s hQ
  unfold InvAlg.Identity at hId ⊢
  rw [hkap, hst B₁ ψ₁ h₁ h₁' hO₁, hst B₂ ψ₂ h₂ h₂' hO₂] at hId
  rw [← hId, hres', hq]
  congr 1
  obtain ⟨m, rfl⟩ := hd
  push_cast
  rw [show -((2 * (m : ℤ) + 1) * val K'.O (resultant C₁.P C₂.P)) =
      (2 * (m : ℤ) + 1) * (-val K'.O (resultant C₁.P C₂.P)) by ring, zpow_mul]
  congr 1
  rw [show (2 * (m : ℤ) + 1) = ((2 * m + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast, Odd.neg_pow ⟨m, rfl⟩]

end GlobalTheory.UnitLemma.UnrAny
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationIntertwinesHeisenbergStatement
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRepresentation_intertwines_heisenberg : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure] (κ : ℂ) (ω : Representation ℂ (UG c (stdJ ν E)) (SB (Matrix α ν E))), IsKW c ψ χ Q μ κ ω → ∀ (g : UG c (stdJ ν E)) (w : Matrix α (ν ⊕ ν) E), Heisenberg₂ c hψ Q w * ω g = ω g * Heisenberg₂ c hψ Q (w * ((g : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E)) := by
  first | exact @GlobalTheory.KSp.weil_heis_intertwine | exact GlobalTheory.KSp.weil_heis_intertwine | (intros; apply GlobalTheory.KSp.weil_heis_intertwine <;> assumption)
end

