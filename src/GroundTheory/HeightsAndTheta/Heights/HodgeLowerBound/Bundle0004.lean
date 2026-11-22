import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0001

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PBlocksLeadSandwich
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

namespace BlocksLeadSandwich

def lineRestr {K : Type*} (p : MvPolynomial K ℚ) (a m : K → ℚ) : Polynomial ℚ :=
  MvPolynomial.aeval (fun k => Polynomial.C (m k) + Polynomial.C (a k) * Polynomial.X) p

theorem eval_lineRestr {K : Type*} (p : MvPolynomial K ℚ) (a m : K → ℚ) (t : ℚ) :
    (lineRestr p a m).eval t = MvPolynomial.eval (fun k => m k + a k * t) p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [lineRestr]
  | add p q hp hq => simp only [lineRestr, map_add, Polynomial.eval_add] at *; rw [hp, hq]
  | mul_X p k hp =>
    simp only [lineRestr, map_mul, Polynomial.eval_mul] at *
    rw [hp]
    simp

theorem eq_map_of_eval_nat {Q : Polynomial ℚ} {r : Polynomial ℝ}
    (h : ∀ t : ℕ, ((Q.eval (t : ℚ) : ℚ) : ℝ) = r.eval (t : ℝ)) : r = Q.map (algebraMap ℚ ℝ) := by
  apply Polynomial.eq_of_infinite_eval_eq
  refine Set.Infinite.mono ?_ (Set.infinite_range_of_injective (Nat.cast_injective (R := ℝ)))
  rintro _ ⟨t, rfl⟩
  show _ = _
  have ht : (t : ℝ) = algebraMap ℚ ℝ (t : ℚ) := by simp
  rw [← h t, ht, Polynomial.eval_map, Polynomial.eval₂_at_apply]
  simp

end BlocksLeadSandwich

open BlocksLeadSandwich in

theorem BlocksLeadSandwich.proof (hLine : GroundTheory.Heights₂.Heights.HilbertSamuel.EventualPolyLine.Statement)
    (hSand : GroundTheory.Heights₂.Heights.HilbertSamuel.PolySandwich.Statement) : BlocksLeadSandwich.Statement := by
  intro K L _ _ n a₀ f g p p' hp hp' hf hg hsand a ha
  classical
  have haq : ∀ k, (((a k).toNat : ℕ) : ℚ) = (a k : ℚ) := fun k => by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (by linarith [ha k])]
  set Q := lineRestr p (fun k => (a k : ℚ)) (fun _ => (a₀ : ℚ)) with hQ
  set Q' := lineRestr p' (fun x => ((Sum.elim a (0 : L → ℤ) x : ℤ) : ℚ)) (fun _ => (a₀ : ℚ)) with hQ'

  have hF : ∀ t : ℕ, (f (fun k => ((t * (a k).toNat + a₀ : ℕ) : ℤ)) : ℚ) = Q.eval (t : ℚ) := by
    intro t
    rw [hf _ (fun k => Nat.le_add_left _ _), hQ, eval_lineRestr]
    refine congrArg (fun x => MvPolynomial.eval x _) (funext fun k => ?_)
    push_cast
    rw [haq]
    ring
  have hG : ∀ t : ℕ, (g (Sum.elim (fun k => ((t * (a k).toNat + a₀ : ℕ) : ℤ)) fun _ => ((a₀ : ℕ) : ℤ)) : ℚ) =
      Q'.eval (t : ℚ) := by
    intro t
    have h1 := hg (Sum.elim (fun k => t * (a k).toNat + a₀) fun _ => a₀)
      (by intro x; cases x <;> simp)
    have h2 : (Sum.elim (fun k => ((t * (a k).toNat + a₀ : ℕ) : ℤ)) fun _ => ((a₀ : ℕ) : ℤ)) =
        fun x => (((Sum.elim (fun k => t * (a k).toNat + a₀) fun _ => a₀ : K ⊕ L → ℕ) x : ℕ) : ℤ) := by
      funext x; cases x <;> rfl
    rw [h2, h1, hQ', eval_lineRestr]
    refine congrArg (fun x => MvPolynomial.eval x _) (funext fun x => ?_)
    cases x with
    | inl k => simp only [Sum.elim_inl]; push_cast; rw [haq]; ring
    | inr l => simp

  obtain ⟨c, hc⟩ := hsand fun _ => a₀
  have hsq : ∀ t : ℕ, Q.eval (t : ℚ) ≤ Q'.eval (t : ℚ) ∧ Q'.eval (t : ℚ) ≤ Q.eval ((t : ℚ) + c) := by
    intro t
    have hδ : ∀ k, c ≤ c * (a k).toNat := fun k => by
      have : 1 ≤ (a k).toNat := by have := ha k; omega
      nlinarith
    obtain ⟨h1, h2⟩ := hc (fun k => t * (a k).toNat + a₀) (fun k => c * (a k).toNat) hδ
    have h3 : (fun k => (((t * (a k).toNat + a₀) + c * (a k).toNat : ℕ) : ℤ)) =
        fun k => (((t + c) * (a k).toNat + a₀ : ℕ) : ℤ) := by
      funext k; push_cast; ring
    rw [h3] at h2
    have e1 := hF t
    have e2 := hG t
    have e3 := hF (t + c)
    push_cast at e3
    rw [← e1, ← e2, ← e3]
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

  obtain ⟨r, hrdeg, hrc, hr⟩ := hLine K n f p a₀ a (fun _ => (a₀ : ℤ)) hp hf
  obtain ⟨r', hr'deg, hr'c, hr'⟩ := hLine (K ⊕ L) n g p' a₀ (Sum.elim a 0) (fun _ => (a₀ : ℤ)) hp' hg
  have hrQ : r = Q.map (algebraMap ℚ ℝ) := by
    refine eq_map_of_eval_nat fun t => ?_
    rw [← hr t, hQ, eval_lineRestr]
    refine congrArg (fun x => ((MvPolynomial.eval x _ : ℚ) : ℝ)) (funext fun k => ?_)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring
  have hr'Q : r' = Q'.map (algebraMap ℚ ℝ) := by
    refine eq_map_of_eval_nat fun t => ?_
    rw [← hr' t, hQ', eval_lineRestr]
    refine congrArg (fun x => ((MvPolynomial.eval x _ : ℚ) : ℝ)) (funext fun x => ?_)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring
  have hQ'deg : Q'.natDegree ≤ n := by
    rw [hr'Q, Polynomial.natDegree_map_eq_of_injective (algebraMap ℚ ℝ).injective] at hr'deg
    exact hr'deg
  obtain ⟨-, hcoeff⟩ := hSand n c Q Q' hQ'deg (Filter.Eventually.of_forall hsq)
  have hfac : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have key : (eventualValue (mixedDiff (fun _ : Fin n => Sum.elim a (0 : L → ℤ)) g) : ℝ) / n.factorial =
      (eventualValue (mixedDiff (fun _ : Fin n => a) f) : ℝ) / n.factorial := by
    rw [← hrc, ← hr'c, hrQ, hr'Q, Polynomial.coeff_map, Polynomial.coeff_map, hcoeff]
  rw [div_left_inj' hfac] at key
  exact_mod_cast key

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PFlagIntMuDegree
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial

namespace FlagIntMuDegree

variable (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ)

omit [DecidableEq Ψ] in

theorem muPoly_isHomogeneous (j : ℕ) : (muPoly Ψ N j).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun p _ => isHomogeneous_X ℚ p

theorem antisym_isHomogeneous {P : RootPoly Ψ N} {m : ℕ} (hP : P.IsHomogeneous m) :
    (antisym Ψ N P).IsHomogeneous m :=
  IsHomogeneous.sum _ _ _ fun w _ =>
    (homogeneousSubmodule (Ψ × Fin N) ℚ m).smul_mem (weylSign Ψ N w) hP.rename_isHomogeneous

omit [DecidableEq Ψ] in

theorem sum_fin_ite (j : ℕ) (hj : j ≤ N) :
    (∑ i : Fin N, if (i : ℕ) < j then N - j else 0) = j * (N - j) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => if i < j then N - j else 0) N, ← Finset.sum_filter,
    show (Finset.range N).filter (· < j) = Finset.range j by
      ext i; simp only [Finset.mem_filter, Finset.mem_range]; omega,
    Finset.sum_const, Finset.card_range, smul_eq_mul]

omit [DecidableEq Ψ] in

theorem rhoMono_degree (j : ℕ) (hj : j ≤ N) :
    (rhoMono Ψ N).degree = dimN Ψ N j + (rhoBlock Ψ N j).degree := by
  simp only [Finsupp.degree_eq_sum, rhoMono, rhoBlock, Finsupp.coe_equivFunOnFinite_symm, dimN]
  have hpt : ∀ p : Ψ × Fin N, N - 1 - (p.2 : ℕ) =
      (if (p.2 : ℕ) < j then N - j else 0) +
        (if (p.2 : ℕ) < j then j - 1 - (p.2 : ℕ) else N - 1 - (p.2 : ℕ)) := by
    intro p
    have := p.2.isLt
    split_ifs <;> omega
  rw [Finset.sum_congr rfl fun p _ => hpt p, Finset.sum_add_distrib]
  congr 1
  rw [Fintype.sum_prod_type]
  simp only [sum_fin_ite N j hj, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_assoc]

theorem proof : FlagIntMuDegree.Statement := by
  intro Ψ _ _ N j hj b hb
  have hP : (muPoly Ψ N j ^ dimN Ψ N j * monomial b (1 : ℚ)).IsHomogeneous
      (dimN Ψ N j + b.degree) := by
    have h := ((muPoly_isHomogeneous Ψ N j).pow (dimN Ψ N j)).mul
      (isHomogeneous_monomial (1 : ℚ) (rfl : b.degree = b.degree))
    rwa [one_mul] at h
  unfold flagInt
  refine (antisym_isHomogeneous Ψ N hP).coeff_eq_zero ?_
  rw [rhoMono_degree Ψ N j hj]
  omega

end FlagIntMuDegree

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PFlagIntMuProd
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial

namespace FlagIntMuProd

variable (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ)

def muOne : MvPolynomial (Fin N) ℚ := ∑ i ∈ Finset.univ.filter (fun i : Fin N => ¬ (i : ℕ) < j), X i

def rhoBlockOne : Fin N →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i => if (i : ℕ) < j then j - 1 - (i : ℕ) else N - 1 - (i : ℕ)

omit [DecidableEq Ψ] in
theorem muPoly_eq_sum : muPoly Ψ N j = ∑ τ, rename (sliceEmb τ) (muOne N j) := by
  unfold muPoly muOne
  simp only [map_sum, rename_X]
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.sum_filter]
  rfl

theorem monomial_rhoBlock :
    (monomial (rhoBlock Ψ N j) (1 : ℚ) : RootPoly Ψ N) =
      ∏ τ, rename (sliceEmb τ) (monomial (rhoBlockOne N j) 1) := by
  simp only [rename_monomial]
  rw [← monomial_sum_prod Finset.univ (fun τ => Finsupp.mapDomain (sliceEmb τ) (rhoBlockOne N j))
    (fun _ => (1 : ℚ)), Finset.prod_const_one, sum_mapDomain_sliceEmb]
  congr 1

theorem flagInt_sum {ι : Type} (s : Finset ι) (P : ι → RootPoly Ψ N) :
    flagInt Ψ N (∑ i ∈ s, P i) = ∑ i ∈ s, flagInt Ψ N (P i) := by
  unfold flagInt antisym
  simp only [map_sum, Finset.smul_sum, coeff_sum]
  exact Finset.sum_comm

theorem flagInt_smul (c : ℚ) (P : RootPoly Ψ N) : flagInt Ψ N (c • P) = c * flagInt Ψ N P := by
  unfold flagInt antisym
  rw [coeff_sum, coeff_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [map_smul, coeff_smul, smul_eq_mul]
  ring

theorem degree_rhoOne {N j : ℕ} (hj : j ≤ N) :
    (rhoOne N).degree = j * (N - j) + (rhoBlockOne N j).degree := by
  rw [Finsupp.degree_eq_sum, Finsupp.degree_eq_sum]
  simp only [rhoOne, rhoBlockOne, Finsupp.coe_equivFunOnFinite_symm]
  have h : ∀ i : Fin N, N - 1 - (i : ℕ) = (if (i : ℕ) < j then N - j else 0) +
      (if (i : ℕ) < j then j - 1 - (i : ℕ) else N - 1 - (i : ℕ)) := by
    intro i
    have := i.isLt
    split_ifs <;> omega
  rw [Finset.sum_congr rfl fun i _ => h i, Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_const_zero,
    add_zero, Finset.sum_const, smul_eq_mul, Fin.card_filter_val_lt, min_eq_right hj]

theorem flagIntOne_muOne_eq_zero {N j : ℕ} (hj : j ≤ N) {k : ℕ} (hk : k ≠ j * (N - j)) :
    flagIntOne N (muOne N j ^ k * monomial (rhoBlockOne N j) 1) = 0 := by
  have hμ : (muOne N j).IsHomogeneous 1 :=
    IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_X ℚ i
  refine flagIntOne_eq_zero_of_isHomogeneous ((hμ.pow k).mul (isHomogeneous_monomial (1 : ℚ) rfl)) ?_
  rw [degree_rhoOne hj]
  omega

theorem flagInt_unit {k : ℕ} :
    flagInt Unit N (muPoly Unit N j ^ k * monomial (rhoBlock Unit N j) 1) =
      flagIntOne N (muOne N j ^ k * monomial (rhoBlockOne N j) 1) := by
  rw [muPoly_eq_sum, monomial_rhoBlock, Fintype.sum_unique, Fintype.prod_unique, ← map_pow, ← map_mul,
    ← Fintype.prod_unique (fun τ : Unit => rename (sliceEmb τ) (muOne N j ^ k * monomial (rhoBlockOne N j) 1)),
    flagInt_prod, Fintype.prod_unique]

end FlagIntMuProd

open FlagIntMuProd in

theorem FlagIntMuProd.proof : FlagIntMuProd.Statement := by
  intro Ψ _ _ N j hj
  set k0 : Ψ → ℕ := fun _ => j * (N - j) with hk0
  have hterm : ∀ k : Ψ → ℕ,
      ((Nat.multinomial Finset.univ k : ℕ) : RootPoly Ψ N) * (∏ τ, rename (sliceEmb τ) (muOne N j) ^ k τ) *
        ∏ τ, rename (sliceEmb τ) (monomial (rhoBlockOne N j) (1 : ℚ)) =
      ((Nat.multinomial Finset.univ k : ℕ) : ℚ) •
        ∏ τ, rename (sliceEmb τ) (muOne N j ^ k τ * monomial (rhoBlockOne N j) 1) := by
    intro k
    rw [mul_assoc, ← Finset.prod_mul_distrib, ← C_mul', map_natCast]
    simp only [map_mul, map_pow]
  rw [muPoly_eq_sum Ψ N j, monomial_rhoBlock Ψ N j, Finset.sum_pow_eq_sum_piAntidiag, Finset.sum_mul,
    flagInt_sum]
  simp_rw [hterm, flagInt_smul, flagInt_prod]
  have hmem : k0 ∈ Finset.piAntidiag Finset.univ (dimN Ψ N j) := by
    rw [Finset.mem_piAntidiag]
    refine ⟨?_, fun i _ => Finset.mem_univ i⟩
    simp [hk0, dimN, mul_assoc]
  rw [Finset.sum_eq_single_of_mem k0 hmem]
  · have hmul : ((Nat.multinomial Finset.univ k0 : ℕ) : ℚ) =
        ((dimN Ψ N j).factorial : ℚ) / ((j * (N - j)).factorial : ℚ) ^ Fintype.card Ψ := by
      rw [eq_div_iff (by positivity)]
      have h := Nat.multinomial_spec (Finset.univ : Finset Ψ) k0
      simp only [hk0, Finset.prod_const, Finset.sum_const, Finset.card_univ, smul_eq_mul] at h
      rw [show dimN Ψ N j = Fintype.card Ψ * (j * (N - j)) by unfold dimN; ring, ← h]
      push_cast
      ring
    rw [hmul, flagInt_unit, hk0, Finset.prod_const, Finset.card_univ]
  · intro k _ hk
    obtain ⟨τ, hτ⟩ : ∃ τ, k τ ≠ j * (N - j) := by
      by_contra h
      push Not at h
      exact hk (funext h)
    rw [Finset.prod_eq_zero (Finset.mem_univ τ) (flagIntOne_muOne_eq_zero hj hτ), mul_zero]

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PFsPotLaplacian
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open InnerProductSpace Laplacian Real MeasureTheory Filter Topology Set

theorem hasFDerivAt_fsPotPlane (z : ℂ) :
    HasFDerivAt fsPotPlane ((1 + ‖z‖ ^ 2)⁻¹ • innerSL ℝ z) z := by
  have hl : HasFDerivAt (fun y : ℂ => Real.log (1 + ‖y‖ ^ 2))
      ((1 + ‖z‖ ^ 2)⁻¹ • (2 • innerSL ℝ z)) z :=
    ((hasStrictFDerivAt_norm_sq z).hasFDerivAt.const_add 1).log (by positivity)
  have e : fsPotPlane = fun y : ℂ => Real.log (1 + ‖y‖ ^ 2) * (1 / 2) := by
    funext y; simp only [fsPotPlane]; ring
  rw [e]
  refine (hl.mul_const (1 / 2 : ℝ)).congr_fderiv ?_
  ext w
  simp
  ring

theorem fderiv_fsPotPlane_apply (z e : ℂ) :
    fderiv ℝ fsPotPlane z e = (1 + ‖z‖ ^ 2)⁻¹ * (z.re * e.re + z.im * e.im) := by
  rw [(hasFDerivAt_fsPotPlane z).fderiv]
  simp [Complex.inner] <;> ring_nf <;> simp

theorem fderiv_fderiv_fsPotPlane_apply (y e : ℂ) :
    fderiv ℝ (fderiv ℝ fsPotPlane) y e e =
      fderiv ℝ (fun z : ℂ => (1 + ‖z‖ ^ 2)⁻¹ * (z.re * e.re + z.im * e.im)) y e := by
  have hd : DifferentiableAt ℝ (fderiv ℝ fsPotPlane) y :=
    ((contDiff_fsPotPlane.fderiv_right (m := 1) (by norm_num)).differentiable
      (by norm_num)) y
  have h := fderiv_clm_apply hd (differentiableAt_const e)
  have hfun : (fun z : ℂ => fderiv ℝ fsPotPlane z e) =
      fun z : ℂ => (1 + ‖z‖ ^ 2)⁻¹ * (z.re * e.re + z.im * e.im) :=
    funext fun z => fderiv_fsPotPlane_apply z e
  rw [hfun] at h
  rw [h]
  simp

theorem hasFDerivAt_partial (y e : ℂ) :
    HasFDerivAt (fun z : ℂ => (1 + ‖z‖ ^ 2)⁻¹ * (z.re * e.re + z.im * e.im))
      ((1 + ‖y‖ ^ 2)⁻¹ • (e.re • Complex.reCLM + e.im • Complex.imCLM) +
        (y.re * e.re + y.im * e.im) •
          (-(((1 + ‖y‖ ^ 2) ^ 2)⁻¹) • (2 • innerSL ℝ y))) y := by
  have h1 : HasFDerivAt (fun z : ℂ => 1 + ‖z‖ ^ 2) (2 • innerSL ℝ y) y :=
    (hasStrictFDerivAt_norm_sq y).hasFDerivAt.const_add 1
  have h2 : HasFDerivAt (fun z : ℂ => (1 + ‖z‖ ^ 2)⁻¹)
      ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (-((1 + ‖y‖ ^ 2) ^ 2)⁻¹)).comp
        (2 • innerSL ℝ y)) y :=
    (hasFDerivAt_inv (by positivity : (1 + ‖y‖ ^ 2) ≠ 0)).comp y h1
  have h3 : HasFDerivAt (fun z : ℂ => z.re * e.re + z.im * e.im)
      (e.re • Complex.reCLM + e.im • Complex.imCLM) y := by
    have hf : (fun z : ℂ => z.re * e.re + z.im * e.im) =
        fun z => (e.re • Complex.reCLM + e.im • Complex.imCLM) z := by
      funext z; simp; ring
    rw [hf]
    exact ContinuousLinearMap.hasFDerivAt _
  refine (h2.mul h3).congr_fderiv ?_
  ext w
  simp <;> ring_nf <;> simp

theorem laplacian_fsPotPlane (y : ℂ) : Δ fsPotPlane y = 2 / (1 + ‖y‖ ^ 2) ^ 2 := by
  rw [laplacian_eq_iteratedFDeriv_complexPlane]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [fderiv_fderiv_fsPotPlane_apply, fderiv_fderiv_fsPotPlane_apply,
    (hasFDerivAt_partial y 1).fderiv, (hasFDerivAt_partial y Complex.I).fderiv]
  have hn : ‖y‖ ^ 2 = y.re ^ 2 + y.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  have hp : (0 : ℝ) < 1 + ‖y‖ ^ 2 := by positivity
  simp [Complex.inner]
  rw [hn] at hp ⊢
  field_simp
  ring

theorem integrable_laplacian_fsPotPlane : Integrable (Δ fsPotPlane) := by
  have h : Δ fsPotPlane = fun y : ℂ => 2 * ((1 : ℝ) + ‖y‖ ^ 2) ^ (-(4 : ℝ) / 2) := by
    funext y
    rw [laplacian_fsPotPlane, show -(4 : ℝ) / 2 = -((2 : ℕ) : ℝ) by norm_num,
      rpow_neg (by positivity), rpow_natCast, div_eq_mul_inv]
  rw [h]
  exact (integrable_rpow_neg_one_add_norm_sq (by simp [Complex.finrank_real_complex]; norm_num)).const_mul 2

theorem integral_radial_fsPot :
    ∫ s in Ioi (0 : ℝ), s ^ (2 - 1) • (2 / (1 + s ^ 2) ^ 2) = 1 := by
  have hderiv : ∀ x ∈ Ici (0 : ℝ), HasDerivAt (fun s : ℝ => -(1 + s ^ 2)⁻¹)
      (x ^ (2 - 1) • (2 / (1 + x ^ 2) ^ 2)) x := by
    intro x _
    have hx : (1 + x ^ 2) ≠ 0 := by positivity
    have h := (((hasDerivAt_pow 2 x).const_add 1).inv hx).neg
    refine h.congr_deriv ?_
    rw [smul_eq_mul, neg_div, neg_neg]
    push_cast
    ring
  have htend : Tendsto (fun s : ℝ => -(1 + s ^ 2)⁻¹) atTop (𝓝 0) := by
    have h : Tendsto (fun s : ℝ => 1 + s ^ 2) atTop atTop :=
      tendsto_atTop_add_const_left _ 1 (tendsto_pow_atTop two_ne_zero)
    simpa using h.inv_tendsto_atTop.neg
  have hint := integrableOn_Ioi_deriv_of_nonneg' hderiv (fun x hx => by
    have : (0 : ℝ) < x := hx
    positivity) htend
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint htend]
  norm_num

theorem integral_laplacian_fsPotPlane : ∫ y, Δ fsPotPlane y = 2 * π := by
  have h : (fun y : ℂ => Δ fsPotPlane y) = fun y : ℂ => (fun s : ℝ => 2 / (1 + s ^ 2) ^ 2) ‖y‖ :=
    funext laplacian_fsPotPlane
  rw [h, integral_fun_norm_addHaar volume (fun s : ℝ => 2 / (1 + s ^ 2) ^ 2),
    Complex.finrank_real_complex, integral_radial_fsPot]
  simp [Measure.real, Complex.volume_ball]

theorem FsPotLaplacian.proof : FsPotLaplacian.Statement :=
  ⟨laplacian_fsPotPlane, integrable_laplacian_fsPotPlane, integral_laplacian_fsPotPlane⟩

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PLaplacianLogGrowth
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open InnerProductSpace Laplacian Real

theorem LaplacianLogGrowth.proof (hA : FsPotLaplacian.Statement) (hD : InvDerivDecay.Statement)
    (hZ : LaplacianDecayZero.Statement) : LaplacianLogGrowth.Statement := by
  intro u F a r hu hr hF heq
  obtain ⟨-, hAi, hA0⟩ := hA
  obtain ⟨v, hv_def⟩ : ∃ v : ℂ → ℝ, v = u - a • fsPotPlane := ⟨_, rfl⟩
  have hφ : ContDiff ℝ 2 (a • fsPotPlane) := contDiff_fsPotPlane.const_smul a
  have hv : ContDiff ℝ 2 v := hv_def ▸ hu.sub hφ
  have hρ : 0 < min r 1 := lt_min hr one_pos
  have hG : ContDiffOn ℝ 2 (F - a • fsPotPlane) (Metric.ball 0 (min r 1)) :=
    (hF.mono (Metric.ball_subset_ball (min_le_left _ _))).sub hφ.contDiffOn
  have hveq : ∀ y : ℂ, max r⁻¹ 1 < ‖y‖ → v y = (F - a • fsPotPlane) y⁻¹ := by
    intro y hy
    have h1 := heq y (lt_of_le_of_lt (le_max_left _ _) hy)
    have h2 := fsPotPlane_eq (y := y) (by rw [inv_one]; exact lt_of_le_of_lt (le_max_right _ _) hy)
    simp only [hv_def, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, h1, h2]
    ring
  obtain ⟨C, R₀, hC⟩ := hD v (F - a • fsPotPlane) (min r 1) (max r⁻¹ 1) hρ hG hveq
  obtain ⟨hvi, hv0⟩ := hZ v C R₀ hv hC
  have hu' : u = a • fsPotPlane + v := by rw [hv_def]; abel
  have hΔ : Δ u = fun y => a * Δ fsPotPlane y + Δ v y := by
    funext y
    rw [hu', ContDiffAt.laplacian_add hφ.contDiffAt hv.contDiffAt,
      laplacian_smul a contDiff_fsPotPlane.contDiffAt, smul_eq_mul]
  rw [hΔ]
  refine ⟨(hAi.const_mul a).add hvi, ?_⟩
  rw [MeasureTheory.integral_add (hAi.const_mul a) hvi, MeasureTheory.integral_const_mul, hA0, hv0]
  ring

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

