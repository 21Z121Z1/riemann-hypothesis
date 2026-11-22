import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0019
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.ContinuousSplitInv

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.CompAtAdd
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.DilBH

variable {D : D7} {n : ℕ}

theorem compAt_add {m : ℕ} (θ : InfFam D) (τ : D.what₂.Tau) (x y : Mx D m n) :
    compAt θ τ (x + y) = compAt θ τ x + compAt θ τ y := by
  ext i j
  simp only [compAt, Matrix.map_apply, Matrix.add_apply, map_add]

theorem pointAt {m : ℕ} (θ : InfFam D) (hθ : IsInfFam θ) (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ)
    (hfr : IsUnit fr.det) (x₀ : Mx D m n) (u : Fin m → Fin n → ℂ) :
    ∃ x : Mx D m n, fr⁻¹ * compAt θ τ x = Matrix.of u ∧ (∀ τ', τ' ≠ τ → compAt θ τ' x = compAt θ τ' x₀) ∧
      x.map (finPart D) = x₀.map (finPart D) := by
  obtain ⟨L, _, hLf, hLz⟩ :=
    Formalism.IndefR.Eqv.lineAtExists_holds D θ hθ m n τ (fr * Matrix.of u - compAt θ τ x₀)
  refine ⟨x₀ + L 1, ?_, ?_, ?_⟩
  · rw [compAt_add, hLz 1 τ, if_pos rfl, Complex.ofReal_one, one_smul]
    have hs : compAt θ τ x₀ + (fr * Matrix.of u - compAt θ τ x₀) = fr * Matrix.of u := by abel
    rw [hs]
    exact Matrix.nonsing_inv_mul_cancel_left _ _ hfr
  · intro τ' h
    rw [compAt_add, hLz 1 τ', if_neg h, add_zero]
  · ext i j
    have h1 := congrFun (congrFun (hLf 1) i) j
    simp only [Matrix.map_apply, Matrix.add_apply, map_add, Matrix.zero_apply] at h1 ⊢
    rw [h1, add_zero]

end PositivityTheory.Rg.Sw.Glob.DilBH
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DCalc
section
noncomputable section

open MeasureTheory Filter Topology

namespace PositivityTheory.Rg.Sw.Glob

open DCalcBH DCalcCH in
theorem dCalc : DCalc := by
  intro m n ε t c e X hc _
  have hfun : ∀ u : Fin m → Fin n → ℂ, (fun s' : ℝ => famC ε t c e 1 X (↑s') u) = fF c X 1 u :=
    fun u => funext fun s => famC_one ε t c e X u s
  refine ⟨fun s r u => ?_, fun r s => ?_⟩
  · rw [hfun, fF_iter]
    rfl
  · simp only [hfun, fF_iter]
    rw [pow_succ']
    exact DCalc2H.l2conv c hc X ((dil c X ^ r) 1) s

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DetMMUnitary
section
noncomputable section

open Matrix Complex

namespace PositivityTheory.Rg.Sw.Glob.VacI

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.Glob PositivityTheory.Rg.Sw.Glob.VacB PositivityTheory.Rg.Sw.Glob.VacD PositivityTheory.Rg.Sw.Glob.VacG

variable {n : ℕ}

theorem blocks_kak (u u' : Matrix (Fin n) (Fin n) ℂ) (hu : uᴴ * u = 1) (hu' : u'ᴴ * u' = 1) (θ : Fin n → ℝ) :
    mM u * kth θ * mM u' = fromBlocks (u * (dR fun j => Real.cos (θ j)) * u') (u * (dR fun j => Real.sin (θ j)) * u')
      (-(u * (dR fun j => Real.sin (θ j)) * u')) (u * (dR fun j => Real.cos (θ j)) * u') := by
  have h1 : uᴴ⁻¹ = u := Matrix.inv_eq_right_inv hu
  have h2 : u'ᴴ⁻¹ = u' := Matrix.inv_eq_right_inv hu'
  simp only [mM, kth, dR, h1, h2, fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, neg_zero, add_zero,
    zero_add, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]

theorem det_mM_unitary (u : Matrix (Fin n) (Fin n) ℂ) (hu : uᴴ * u = 1) : (mM u).det = u.det * u.det := by
  rw [mM_unitary u hu, det_fromBlocks_zero₂₁]

private theorem det_kth_eq_one (θ : Fin n → ℝ) : (kth θ).det = 1 := by
  have hL : (fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) (I • (1 : Matrix (Fin n) (Fin n) ℂ))
      (0 : Matrix (Fin n) (Fin n) ℂ) (1 : Matrix (Fin n) (Fin n) ℂ)).det = 1 := by
    rw [det_fromBlocks_zero₂₁]
    simp
  have hR : (fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) (-(I • (1 : Matrix (Fin n) (Fin n) ℂ)))
      (0 : Matrix (Fin n) (Fin n) ℂ) (1 : Matrix (Fin n) (Fin n) ℂ)).det = 1 := by
    rw [det_fromBlocks_zero₂₁]
    simp
  have key : fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) (I • (1 : Matrix (Fin n) (Fin n) ℂ))
        (0 : Matrix (Fin n) (Fin n) ℂ) (1 : Matrix (Fin n) (Fin n) ℂ) * kth θ *
        fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) (-(I • (1 : Matrix (Fin n) (Fin n) ℂ)))
        (0 : Matrix (Fin n) (Fin n) ℂ) (1 : Matrix (Fin n) (Fin n) ℂ)
      = fromBlocks (diagonal fun j => (Real.cos (θ j) : ℂ) - I * Real.sin (θ j)) (0 : Matrix (Fin n) (Fin n) ℂ)
          (-diagonal fun j => (Real.sin (θ j) : ℂ))
          (diagonal fun j => (Real.cos (θ j) : ℂ) + I * Real.sin (θ j)) := by
    simp only [kth, fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero,
      add_zero, zero_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_neg, Matrix.neg_mul]
    congr 1 <;> ext i j <;> by_cases h : i = j <;> simp [h, diagonal_apply] <;>
      first
      | ring1
      | linear_combination Complex.sin ((θ j : ℝ) : ℂ) * I_sq
  have hprod : ∏ j, (((Real.cos (θ j) : ℂ) - I * Real.sin (θ j)) * ((Real.cos (θ j) : ℂ) + I * Real.sin (θ j))) = 1 := by
    apply Finset.prod_eq_one
    intro j _
    have hp := Real.sin_sq_add_cos_sq (θ j)
    generalize Real.cos (θ j) = c at *
    generalize Real.sin (θ j) = s at *
    have hp' : (s : ℂ) ^ 2 + (c : ℂ) ^ 2 = 1 := by exact_mod_cast hp
    linear_combination hp' - (s : ℂ) ^ 2 * I_sq
  have h := congrArg Matrix.det key
  rw [det_mul, det_mul, hL, hR, det_fromBlocks_zero₁₂, det_diagonal, det_diagonal, ← Finset.prod_mul_distrib,
    hprod, one_mul, mul_one] at h
  exact h

theorem det_kth (θ : Fin n → ℝ) (hθ : ∀ j, -(Real.pi / 2) < θ j ∧ θ j ≤ Real.pi / 2) : (kth θ).det = 1 := by
  exact det_kth_eq_one θ

theorem jF_kak (e : ℤ) (p q : ℕ) (k : GR n) (u u' : Matrix (Fin n) (Fin n) ℂ) (θ : Fin n → ℝ) (hu : uᴴ * u = 1)
    (hu' : u'ᴴ * u' = 1) (hθ : ∀ j, -(Real.pi / 2) < θ j ∧ θ j ≤ Real.pi / 2) (hkm : mR k = mM u * kth θ * mM u') :
    jF e p q k (I • (1 : Matrix (Fin n) (Fin n) ℂ)) =
      (u.det * u.det * (u'.det * u'.det)) ^ e * (u.det * (∏ j, cexp (-(I * (θ j : ℂ)))) * u'.det) ^ (-(p : ℤ)) *
        (u.det * (∏ j, cexp (I * (θ j : ℂ))) * u'.det) ^ (-(q : ℤ)) := by
  have hdet : (mR k).det = u.det * u.det * (u'.det * u'.det) := by
    rw [hkm, det_mul, det_mul, det_mM_unitary u hu, det_mM_unitary u' hu', det_kth θ hθ, mul_one]
  have hk2 := hkm.trans (blocks_kak u u' hu hu' θ)
  have hdm : diagonal (fun j => cexp (-(I * (θ j : ℂ)))) =
      (dR fun j => Real.cos (θ j)) - I • (dR fun j => Real.sin (θ j)) := by
    ext a b
    by_cases h : a = b
    · subst h
      simp only [dR, diagonal_apply_eq, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      rw [show -(I * (θ a : ℂ)) = (-(θ a : ℂ)) * I by ring, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg,
        ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      ring
    · simp [dR, diagonal_apply, h]
  have hdp : diagonal (fun j => cexp (I * (θ j : ℂ))) =
      (dR fun j => Real.cos (θ j)) + I • (dR fun j => Real.sin (θ j)) := by
    ext a b
    by_cases h : a = b
    · subst h
      simp only [dR, diagonal_apply_eq, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      rw [show I * (θ a : ℂ) = (θ a : ℂ) * I by ring, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      ring
    · simp [dR, diagonal_apply, h]
  have hA : toBlocks₂₁ (mR k) * (I • (1 : Matrix (Fin n) (Fin n) ℂ)) + toBlocks₂₂ (mR k) =
      u * diagonal (fun j => cexp (-(I * (θ j : ℂ)))) * u' := by
    rw [hk2, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, hdm]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, smul_neg]
    abel
  have hZ : (I • (1 : Matrix (Fin n) (Fin n) ℂ))ᴴ = -(I • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
    rw [conjTranspose_smul, conjTranspose_one, Complex.star_def, conj_I, neg_smul]
  have hB : toBlocks₂₁ (mR k) * (I • (1 : Matrix (Fin n) (Fin n) ℂ))ᴴ + toBlocks₂₂ (mR k) =
      u * diagonal (fun j => cexp (I * (θ j : ℂ))) * u' := by
    rw [hZ, hk2, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, hdp, Matrix.mul_neg, Matrix.mul_smul, Matrix.mul_one]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, smul_neg, neg_neg]
    abel
  simp only [jF, hdet, hA, hB, det_mul, det_diagonal]

end PositivityTheory.Rg.Sw.Glob.VacI
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussG
section
noncomputable section

open scoped Matrix ComplexOrder
open Matrix

namespace PositivityTheory.Rg.Sw.Glob.GaussH

variable {n : ℕ}

theorem conj_half_smul (Z : Matrix (Fin n) (Fin n) ℂ) : ((1 / 2 : ℂ) • (Z + Zᴴ))ᴴ = (1 / 2 : ℂ) • (Z + Zᴴ) := by
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose, add_comm]
  congr 1
  simp [Complex.ext_iff]

theorem exists_sqrt {Y : Matrix (Fin n) (Fin n) ℂ} (hY : Y.PosDef) : ∃ S : Matrix (Fin n) (Fin n) ℂ, S * Sᴴ = Y ∧ IsUnit S.det := by
  classical
  have hH := hY.1
  let U : Matrix (Fin n) (Fin n) ℂ := (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)
  let d : Matrix (Fin n) (Fin n) ℂ := diagonal (fun i => ((Real.sqrt (hH.eigenvalues i) : ℝ) : ℂ))
  have hd : d * dᴴ = diagonal (RCLike.ofReal ∘ hH.eigenvalues) := by
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    simp only [Function.comp_apply, Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hY.eigenvalues_pos i).le]
    rfl
  have hS : U * d * (U * d)ᴴ = Y := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc d, hd]
    conv_rhs => rw [hH.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply]
    simp [U, Matrix.star_eq_conjTranspose, Matrix.mul_assoc]
  refine ⟨U * d, hS, ?_⟩
  have hYu : IsUnit Y.det := (Matrix.isUnit_iff_isUnit_det Y).mp hY.isUnit
  rw [← hS, Matrix.det_mul] at hYu
  exact isUnit_of_mul_isUnit_left hYu

end PositivityTheory.Rg.Sw.Glob.GaussH
end
end

