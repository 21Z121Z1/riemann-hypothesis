import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0010
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyStatementOfItemsFourSeven
import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
import Formalism.SharpRestriction.CuspSpanNormBounds.BranchingAndRankConstants
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0008
import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.AutomorphicFormsFiniteIdeal
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSigmaList
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0090

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AmplitudeBoundsAtParamsOfAdmittedBounds
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma GlobalTheory.Core.Deg

noncomputable section

namespace GlobalTheory

theorem ampAt_record_of_inputs :
    ∀ Cg CPT CDl hilbertNinetyConstant Ca CS : ℝ, 0 ≤ hilbertNinetyConstant → 0 ≤ Ca → ∃ C C2 Ch : ℝ, 0 ≤ C ∧ 0 ≤ Ch ∧ ∀ Cpr δ : ℝ, 0 < δ → ∃ thr : ℝ,
      ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl cb Cu cT CT C0 : ℝ), thr ≤ C' → thr ≤ Cl → 1 ≤ large₂.CGam →
      VanishingOnXAndXPlusBranching.adm1 D large₂ C' Cl Cg cb Cu cT CT C0 (max Cpr 0) 1 CPT →
      VanishingOnXAndXPlusBranching.adm2 D large₂ C' Cl Cg cb Cu cT CT C0 (max Cpr 0) 1 CDl →
      VanishingOnXAndXPlusBranching.adm5 D large₂ C' Cl Cg cb Cu cT CT C0 →
      VanishingOnXAndXPlusBranching.adm9 D large₂ C' Cl Cg cb Cu cT CT C0 (max Cpr 0) 1 →
      DegreeRatioUnitShiftBound D large₂ C' Cl Cg cb Cu cT CT C0 (max Cpr 0) 1 hilbertNinetyConstant →
      AbsAllParameters D large₂ C' Cl Cg cb Cu cT CT C0 1 1 (max Cpr 0) Ca →
      VanishingOnXAndXPlusBranching.adm11 D large₂ C' Cl Cg cb Cu cT CT C0 1 CS → VanishingOnXAndXPlusBranching.adm12 D →
      AmpAt D large₂ C' Cl Cg cb Cu cT CT C0 Cpr C C2 Ch δ := by
  intro Cg CPT CDl hilbertNinetyConstant Ca CS hilbertNinetyConstant_pos hCa0
  set Cc : ℝ := CS + Cg + 2 with hCc
  set K : ℝ := max CPT 0 + max Cc 0 + 6 with hK
  set Ch : ℝ := max (max CDl 0) (max (CDl + 1) 0) with hChd
  set Cm : ℝ := max (max K Ca) 2 with hCm
  set C : ℝ := max Cm (6 * Real.exp 1 * Real.pi * 1) with hCd
  set C2 : ℝ := max (6 * C) (C ^ 2 + C * Ch) with hC2
  have m1 : K ≤ Cm := le_trans (le_max_left _ _) (le_max_left _ _)
  have m2 : Ca ≤ Cm := le_trans (le_max_right _ _) (le_max_left _ _)
  have m3 : 2 ≤ Cm := le_max_right _ _
  have n1 : Cm ≤ C := le_max_left _ _
  have n4 : 6 * Real.exp 1 * Real.pi * 1 ≤ C := le_max_right _ _
  have hC0 : 0 ≤ C := by linarith
  have hChA : max (CDl + 1) 0 ≤ Ch := le_max_right _ _
  have hCh0 : 0 ≤ Ch := le_trans (le_max_right _ _) hChA
  have hChD : CDl ≤ Ch := le_trans (le_max_left _ _) (le_max_left _ _)
  have h62 : 6 * C ≤ C2 := le_max_left _ _
  have h22 : C ^ 2 + C * Ch ≤ C2 := le_max_right _ _
  refine ⟨C, C2, Ch, hC0, hCh0, fun Cpr δ hδ => ?_⟩
  obtain ⟨thr0, hthr0⟩ := GlobalTheory.T.size_bounds_of_standingHypotheses (max (max (C + 6 * C * Ch) C) (max (1 / δ) hilbertNinetyConstant))
  refine ⟨thr0, fun D large₂ C' Cl cb Cu cT CT C0 hC' hCl hG hA1 hA2 hA5 hA9 hDeg hAbs hA11 hA12 => ?_⟩
  by_cases hH0 : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0
  swap
  · refine ⟨?_, ?_, ?_⟩
    · intro w w' zs zs' γs ps _ hH
      exact absurd hH.1 hH0
    · intro w w' zs zs' γs ps _ hH
      exact absurd hH.1 hH0
    · intro τ w w' hTT θ hθ W hW S hS hdeg γ p hRel θ' hθ' νR hνR hH
      exact absurd hH.1 hH0
  obtain ⟨h1000, -, hMm, hMk, -, -, hrb, hm2k, -⟩ := hthr0 D large₂ C' Cl Cg cb Cu cT CT hC' hCl hH0.1
  have hM1 : C + 6 * C * Ch ≤ (D.R.m : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hMm
  have hMC : C ≤ (D.R.k : ℝ) := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hMk
  have hMd : 1 / δ ≤ (D.R.m : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hMm
  have hM9 : hilbertNinetyConstant ≤ (D.R.m : ℝ) := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hMm
  have hm0 : (0 : ℝ) ≤ D.R.m := Nat.cast_nonneg _
  have hb : 1 ≤ large₂.sc.b := one_le_b large₂

  have hS3 : VanishingOnXAndXPlusBranching.TowerRallisLemma D large₂ C' Cl Cg cb Cu cT CT C0 1 C C2 Ch := by
    refine heightStatement_of_bounds D large₂ C' Cl Cg cb Cu cT CT C0 1 C C2 Ch hC0 hCh0 h62 ?_
    nlinarith
  have hS5 : VanishingOnXAndXPlusBranching.GGFromIrreducibility D large₂ C' Cl Cg cb Cu cT CT C0 1 C C2 Ch :=
    product_clause_at_record D large₂ C' Cl Cg cb Cu cT CT C0 1 C C2 Ch hC0 hCh0 (by linarith) h22

  have hCl1 : 1 / Cl ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have p1 : VanishingOnXAndXPlusBranching.Conclusion1 D large₂ C' Cl Cg cb Cu cT CT C0 1 Cc :=
    constant_clause_schur_weyl D large₂ C' Cl Cg cb Cu cT CT C0 1 CS Cc (by rw [hCc]; linarith) hA11 hA12

  have hn : (D.R.r : ℝ) ^ (hilbertNinetyConstant * (D.R.m : ℝ)) ≤ large₂.sc.b ^ (2 * (D.R.m : ℝ) ^ 2) := by
    calc (D.R.r : ℝ) ^ (hilbertNinetyConstant * (D.R.m : ℝ)) ≤ large₂.sc.b ^ (hilbertNinetyConstant * (D.R.m : ℝ)) :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) hrb (mul_nonneg hilbertNinetyConstant_pos hm0)
      _ ≤ large₂.sc.b ^ (2 * (D.R.m : ℝ) ^ 2) := Real.rpow_le_rpow_of_exponent_le hb (by nlinarith)
  have hmr : (D.R.m : ℝ) = 2 * (D.R.rS : ℝ) + 2 := by exact_mod_cast rank_eq_two_mul_add_two D
  have hr0 : (0 : ℝ) ≤ D.R.rS := Nat.cast_nonneg _
  have hδk : (D.R.rS : ℝ) + 2 ≤ δ * D.R.k := by
    have hmpos : (0 : ℝ) < D.R.m := by rw [hmr]; positivity
    have e1 : 1 ≤ δ * (D.R.m : ℝ) := by
      rw [div_le_iff₀ hδ] at hMd; linarith
    have e3 : (D.R.m : ℝ) ≤ δ * (D.R.m : ℝ) ^ 2 := by
      have := mul_le_mul_of_nonneg_right e1 hmpos.le
      nlinarith
    have e4 : δ * (D.R.m : ℝ) ^ 2 ≤ δ * D.R.k := mul_le_mul_of_nonneg_left hm2k hδ.le
    linarith

  have r1 : HilbertSchmidtBoundWithSizeDecay D large₂ C' Cl Cg cb Cu cT CT C0 1 1 Cpr Cm Ch :=
    L2_decay_of_admissible D large₂ C' Cl Cg cb Cu cT CT C0 1 (max Cpr 0) 1 CPT CDl Cc Cpr Cm Ch (le_max_right _ _) (le_max_left _ _)
      m1 hCh0 hChD hA1 hA2 p1
  have r2 : AbsWithSizeDecay D large₂ C' Cl Cg cb Cu cT CT C0 1 1 Cpr Cm Ch :=
    abs_decay_mono_constants D large₂ hCa0 m2 hChA
      (abs_decay_of_all_parameters D large₂ C' Cl Cg cb Cu cT CT C0 1 (max Cpr 0) 1 CDl hilbertNinetyConstant Cpr Ca (max (CDl + 1) 0) (le_max_right _ _)
        (le_max_left _ _) hCa0 hilbertNinetyConstant_pos (le_max_right _ _) (le_max_left _ _) hn hA2 hA9 hDeg hAbs)
  have q7 : VanishingOnXAndXPlusBranching.division_rows_rational_lattice D large₂ C' Cl Cg cb Cu cT CT C0 1 1 Cpr C Ch δ :=
    decayProp_of_l2AbsDecay D large₂ C' Cl Cg cb Cu cT CT C0 1 1 Cpr Cm C Ch δ m3 n1 hMC hδk n4 hA5 r1 r2
  exact ⟨hS3, hS5, q7⟩

end GlobalTheory

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BoundedSubgroupOfIndefiniteUnitaryEqMaximalCompa
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory GlobalTheory.AutFinLit GlobalTheory.Published.AutFin
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies (LieAt LieInf atPlace IsExpFam IsSmoothInf wordDer)
open scoped TensorProduct DirectSum Classical
open Matrix

namespace GlobalTheory.BoundedUnitary

theorem norm_eigenvalue_le_one {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (C : ℝ)
    (hC : ∀ k : ℕ, ∀ i j, ‖(M ^ k) i j‖ ≤ C) (v : Fin n → ℂ) (hv : v ≠ 0) (μ : ℂ)
    (h : M *ᵥ v = μ • v) : ‖μ‖ ≤ 1 := by
  first
  | exact @_root_.GlobalTheory.EigenvalueNormBound.norm_eigenvalue_le_one
  | exact _root_.GlobalTheory.EigenvalueNormBound.norm_eigenvalue_le_one
  | (apply _root_.GlobalTheory.EigenvalueNormBound.norm_eigenvalue_le_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.EigenvalueNormBound.norm_eigenvalue_le_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.EigenvalueNormBound.norm_eigenvalue_le_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.EigenvalueNormBound.norm_eigenvalue_le_one ..)

open scoped ComplexOrder in

theorem eq_one_of_posSemidef {n : ℕ} (p q : Matrix (Fin n) (Fin n) ℂ) (hp : p.PosSemidef)
    (hqp : q * p = 1) (C : ℝ) (hC : ∀ k : ℕ, ∀ i j, ‖(p ^ k) i j‖ ≤ C)
    (hC' : ∀ k : ℕ, ∀ i j, ‖(q ^ k) i j‖ ≤ C) : p = 1 := by
  have hH := hp.isHermitian
  have hev : ∀ j, hH.eigenvalues j = 1 := by
    intro j
    set v : Fin n → ℂ := ⇑(hH.eigenvectorBasis j) with hvdef
    have hv : v ≠ 0 := by
      intro h0
      have h1 : hH.eigenvectorBasis j = 0 := by
        ext i
        exact congrFun h0 i
      exact hH.eigenvectorBasis.orthonormal.ne_zero j h1
    have h1 : p *ᵥ v = ((hH.eigenvalues j : ℝ) : ℂ) • v := by
      have := hH.mulVec_eigenvectorBasis j
      rw [hvdef, this]
      ext i
      simp
    have h0 : 0 ≤ hH.eigenvalues j := hp.eigenvalues_nonneg j
    have h2 : v = ((hH.eigenvalues j : ℝ) : ℂ) • (q *ᵥ v) := by
      rw [← Matrix.mulVec_smul, ← h1, Matrix.mulVec_mulVec, hqp, Matrix.one_mulVec]
    have hne : ((hH.eigenvalues j : ℝ) : ℂ) ≠ 0 := by
      intro h
      rw [h, zero_smul] at h2
      exact hv h2
    have h3 : q *ᵥ v = ((hH.eigenvalues j : ℝ) : ℂ)⁻¹ • v := by
      conv_rhs => rw [h2]
      rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
    have a1 := norm_eigenvalue_le_one p C hC v hv _ h1
    have a2 := norm_eigenvalue_le_one q C hC' v hv _ h3
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg h0] at a2
    rw [Complex.norm_real, Real.norm_of_nonneg h0] at a1
    have hpos : 0 < hH.eigenvalues j := lt_of_le_of_ne h0 (fun h => hne (by rw [← h]; simp))
    exact le_antisymm a1 ((inv_le_one₀ hpos).mp a2)
  have hbasis : ∀ j, p *ᵥ ⇑(hH.eigenvectorBasis j) = ⇑(hH.eigenvectorBasis j) := by
    intro j
    rw [hH.mulVec_eigenvectorBasis j, hev j, one_smul]
  have hU : p * (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) =
      (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) := by
    ext i j
    have := congrFun (hbasis j) i
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  have hU2 := Matrix.mem_unitaryGroup_iff.mp hH.eigenvectorUnitary.2
  calc p = p * ((hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
        star (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)) := by rw [hU2, mul_one]
    _ = 1 := by rw [← mul_assoc, hU, hU2]

open scoped ComplexOrder in

theorem eq_Kset_of_bounded : ∀ (n : ℕ) (ε : Fin n → Bool) (G' : Set (Matrix (Fin n) (Fin n) ℂ)), G' ⊆ Formalism.MainNotions.S.UJset ε → Formalism.REAL.Kset ε ⊆ G' → (∀ a ∈ G', ∀ b ∈ G', a * b ∈ G') → (∀ a ∈ G', a⁻¹ ∈ G') → (∃ C : ℝ, ∀ a ∈ G', ∀ i j, ‖a i j‖ ≤ C) → G' = Formalism.REAL.Kset ε := by
  intro n ε G' hU hK hmul hinv ⟨C, hC⟩
  refine Set.Subset.antisymm (fun a ha => ?_) hK
  have hJJ := Formalism.REAL.Jm_mul_self ε
  have hJH := Formalism.REAL.Jm_conjTranspose ε
  set J := Formalism.REAL.Jm ε with hJ
  have hJG : J ∈ G' := hK ⟨by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, hJH, hJJ], rfl⟩
  have h1G : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ G' := hJJ ▸ hmul _ hJG _ hJG
  have hpow : ∀ b ∈ G', ∀ k : ℕ, b ^ k ∈ G' := by
    intro b hb k
    induction k with
    | zero => simpa using h1G
    | succ k ih => rw [pow_succ]; exact hmul _ ih _ hb
  have hleft : ∀ b ∈ G', (J * bᴴ * J) * b = 1 := by
    intro b hb
    have hb' : bᴴ * J * b = J := hU hb
    calc (J * bᴴ * J) * b = J * (bᴴ * J * b) := by simp only [mul_assoc]
      _ = 1 := by rw [hb', hJJ]
  have hinv_eq : ∀ b ∈ G', b⁻¹ = J * bᴴ * J := fun b hb => Matrix.inv_eq_left_inv (hleft b hb)
  have haH : aᴴ ∈ G' := by
    have : aᴴ = J * a⁻¹ * J := by
      rw [hinv_eq a ha]
      calc aᴴ = (J * J) * aᴴ * (J * J) := by rw [hJJ, one_mul, mul_one]
        _ = _ := by simp only [mul_assoc]
    rw [this]
    exact hmul _ (hmul _ hJG _ (hinv a ha)) _ hJG
  have hpG : aᴴ * a ∈ G' := hmul _ haH _ ha
  have hp1 : aᴴ * a = 1 := by
    refine eq_one_of_posSemidef (aᴴ * a) (aᴴ * a)⁻¹ (Matrix.posSemidef_conjTranspose_mul_self a) ?_ C
      (fun k => hC _ (hpow _ hpG k)) (fun k => hC _ (hpow _ (hinv _ hpG) k))
    rw [hinv_eq _ hpG]
    exact hleft _ hpG
  have hp2 : a * aᴴ = 1 := mul_eq_one_comm.mp hp1
  refine ⟨by rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, hp1], ?_⟩
  have ha' : aᴴ * J * a = J := hU ha
  calc a * J = a * (aᴴ * J * a) := by rw [ha']
    _ = (a * aᴴ) * J * a := by simp only [mul_assoc]
    _ = J * a := by rw [hp2, one_mul]

end GlobalTheory.BoundedUnitary
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CenterTensorProductMemRange
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory GlobalTheory.AutFinLit GlobalTheory.Published.AutFin
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies (LieAt LieInf atPlace IsExpFam IsSmoothInf wordDer)
open scoped TensorProduct DirectSum Classical

namespace GlobalTheory.CenterTensor

open Algebra.TensorProduct

theorem center_tensorProduct_mem_range {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B]
    (z : A ⊗[ℂ] B) (hz : z ∈ Subalgebra.center ℂ (A ⊗[ℂ] B)) :
    ∃ u : (Subalgebra.center ℂ A) ⊗[ℂ] (Subalgebra.center ℂ B),
      Algebra.TensorProduct.map (Subalgebra.center ℂ A).val (Subalgebra.center ℂ B).val u = z := by
  have h1 : z ∈ Subalgebra.centralizer ℂ
      ((Algebra.TensorProduct.includeRight : B →ₐ[ℂ] A ⊗[ℂ] B).range : Set (A ⊗[ℂ] B)) := by
    rw [Subalgebra.mem_centralizer_iff]
    intro g _
    exact Subalgebra.mem_center_iff.1 hz g
  rw [Subalgebra.centralizer_range_includeRight_eq_center_tensorProduct] at h1
  obtain ⟨w, hw⟩ := h1
  set f := Algebra.TensorProduct.map (AlgHom.id ℂ A) (Subalgebra.center ℂ B).val with hf
  have finj : Function.Injective f := by
    have : (f : A ⊗[ℂ] (Subalgebra.center ℂ B) → A ⊗[ℂ] B) =
        LinearMap.lTensor A (Subalgebra.center ℂ B).val.toLinearMap := by
      funext x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [hf]
      | add x y hx hy => simp only [map_add, hx, hy]
    rw [this]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
  have hw2 : w ∈ Subalgebra.centralizer ℂ
      ((Algebra.TensorProduct.includeLeft : A →ₐ[ℂ] A ⊗[ℂ] (Subalgebra.center ℂ B)).range :
        Set (A ⊗[ℂ] (Subalgebra.center ℂ B))) := by
    rw [Subalgebra.mem_centralizer_iff]
    rintro _ ⟨a, rfl⟩
    have hw' : f w = z := hw
    have h3 : f ((Algebra.TensorProduct.includeLeft : A →ₐ[ℂ] A ⊗[ℂ] (Subalgebra.center ℂ B)) a) = a ⊗ₜ[ℂ] (1 : B) := by simp [hf]
    apply finj
    show f ((Algebra.TensorProduct.includeLeft : A →ₐ[ℂ] A ⊗[ℂ] (Subalgebra.center ℂ B)) a * w) = f (w * (Algebra.TensorProduct.includeLeft : A →ₐ[ℂ] A ⊗[ℂ] (Subalgebra.center ℂ B)) a)
    rw [map_mul, map_mul, hw', h3]
    exact Subalgebra.mem_center_iff.1 hz _
  rw [Subalgebra.centralizer_coe_range_includeLeft_eq_center_tensorProduct] at hw2
  obtain ⟨u, hu⟩ := hw2
  refine ⟨u, ?_⟩
  have hw' : f w = z := hw
  have hu' : Algebra.TensorProduct.map (Subalgebra.center ℂ A).val
      (AlgHom.id ℂ (Subalgebra.center ℂ B)) u = w := hu
  rw [← hw', ← hu']
  clear hw hu hw' hu' hz
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [hf]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem center_eq_adjoin : ∀ (A B C : Type) [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] [Ring C] [Algebra ℂ C] (e : (A ⊗[ℂ] B) ≃ₐ[ℂ] C), Subalgebra.center ℂ C = Algebra.adjoin ℂ ((fun a => e (a ⊗ₜ 1)) '' (Subalgebra.center ℂ A : Set A) ∪ (fun b => e (1 ⊗ₜ b)) '' (Subalgebra.center ℂ B : Set B)) := by
  intro A B C _ _ _ _ _ _ e
  apply le_antisymm
  · intro c hc
    have hz : e.symm c ∈ Subalgebra.center ℂ (A ⊗[ℂ] B) := by
      rw [Subalgebra.mem_center_iff] at hc ⊢
      intro g
      apply e.injective
      rw [map_mul, map_mul, e.apply_symm_apply]
      exact hc (e g)
    obtain ⟨u, hu⟩ := center_tensorProduct_mem_range _ hz
    have hc' : c = e (Algebra.TensorProduct.map (Subalgebra.center ℂ A).val
        (Subalgebra.center ℂ B).val u) := by rw [hu, e.apply_symm_apply]
    rw [hc']
    clear hu hc'
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      have : (Algebra.TensorProduct.map (Subalgebra.center ℂ A).val
          (Subalgebra.center ℂ B).val) (a ⊗ₜ b) = ((a : A) ⊗ₜ (1 : B)) * ((1 : A) ⊗ₜ (b : B)) := by
        simp
      rw [this, map_mul]
      refine Subalgebra.mul_mem _ (Algebra.subset_adjoin ?_) (Algebra.subset_adjoin ?_)
      · exact Or.inl ⟨a, a.2, rfl⟩
      · exact Or.inr ⟨b, b.2, rfl⟩
    | add x y hx hy => rw [map_add, map_add]; exact Subalgebra.add_mem _ hx hy
  · rw [Algebra.adjoin_le_iff]
    rintro _ (⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩)
    · rw [SetLike.mem_coe, Subalgebra.mem_center_iff]
      intro g
      obtain ⟨y, rfl⟩ := e.surjective g
      rw [← map_mul, ← map_mul]
      congr 1
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul x y =>
        simp [Subalgebra.mem_center_iff.1 ha x]
      | add x y hx hy => rw [mul_add, add_mul, hx, hy]
    · rw [SetLike.mem_coe, Subalgebra.mem_center_iff]
      intro g
      obtain ⟨y, rfl⟩ := e.surjective g
      rw [← map_mul, ← map_mul]
      congr 1
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul x y =>
        simp [Subalgebra.mem_center_iff.1 hb y]
      | add x y hx hy => rw [mul_add, add_mul, hx, hy]

end GlobalTheory.CenterTensor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsBoundAbsLocalLatticeCompletionEntries
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain GlobalTheory.AdelicU Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory

theorem absFin_latLoc_le : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L] (v : HeightOneSpectrum (𝓞 F)),
    ∃ C : ℝ≥0, ∀ y ∈ latLoc F L v, ∀ i, absFin F v (y i) ≤ C := by
  first
  | (run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll])); exact @_root_.GlobalTheory.LocalLatticeBound.exists_bound_latLoc
  | (run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll])); exact _root_.GlobalTheory.LocalLatticeBound.exists_bound_latLoc
  | exact @_root_.GlobalTheory.LocalLatticeBound.exists_bound_latLoc
  | exact _root_.GlobalTheory.LocalLatticeBound.exists_bound_latLoc
  | (apply _root_.GlobalTheory.LocalLatticeBound.exists_bound_latLoc <;> assumption)
  | (intros; apply _root_.GlobalTheory.LocalLatticeBound.exists_bound_latLoc <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LocalLatticeBound.exists_bound_latLoc <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LocalLatticeBound.exists_bound_latLoc ..)

example : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L] (v : HeightOneSpectrum (𝓞 F)), ∃ C : ℝ≥0, ∀ y ∈ latLoc F L v, ∀ i, absFin F v (y i) ≤ C := @absFin_latLoc_le

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralKeepsDoublingDiagonalAdicCompletioStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_keepsDoublingDiagonal_adicCompletion : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (ϖ : w.adicCompletion E), IsUnifV E w ϖ → ∀ (d : Fin n → ℤ) (t k₁ k₂ : GL (Fin n) (w.adicCompletion E)), t.1 = Matrix.diagonal (fun i => ϖ ^ d i) → k₁ ∈ KGL w n → k₂ ∈ KGL w n → ∃ κ ∈ KGL w (n + n), KeepsDiag finSumFinEquiv (blkGL finSumFinEquiv (k₁ * t * k₂, 1) * κ).1 ∧ ordL (leviMat finSumFinEquiv (blkGL finSumFinEquiv (k₁ * t * k₂, 1) * κ).1).det = ∑ i, max (d i) 0 ∧ ordL (quotMat finSumFinEquiv (blkGL finSumFinEquiv (k₁ * t * k₂, 1) * κ).1).det = ∑ i, min (d i) 0 := by
  first | exact @GlobalTheory.GraphShear.graph_shear | exact GlobalTheory.GraphShear.graph_shear | (intros; apply GlobalTheory.GraphShear.graph_shear <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingleMemLocalLatticeCompletion
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain GlobalTheory.AdelicU Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.AdelicU

theorem exists_zsmul_mem_of_isLattice {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L] (x : Fin n → E) :
    ∃ m : ℤ, m ≠ 0 ∧ m • x ∈ L := by
  first
  | exact @_root_.GlobalTheory.LatticeIntegerMultiple.exists_zsmul_mem_lattice
  | exact _root_.GlobalTheory.LatticeIntegerMultiple.exists_zsmul_mem_lattice
  | (apply _root_.GlobalTheory.LatticeIntegerMultiple.exists_zsmul_mem_lattice <;> assumption)
  | (intros; apply _root_.GlobalTheory.LatticeIntegerMultiple.exists_zsmul_mem_lattice <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LatticeIntegerMultiple.exists_zsmul_mem_lattice <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LatticeIntegerMultiple.exists_zsmul_mem_lattice ..)

theorem exists_single_mem_latLoc {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L] (v : HeightOneSpectrum (𝓞 F)) :
    ∃ c : Fv F v, c ≠ 0 ∧
      ∀ i : Fin n, (Pi.single i (c ⊗ₜ[F] (1 : E)) : Fin n → Fv F v ⊗[F] E) ∈ latLoc F L v := by
  first
  | exact @_root_.GlobalTheory.LocalLatticeIntegral.exists_single_mem_latLoc
  | exact _root_.GlobalTheory.LocalLatticeIntegral.exists_single_mem_latLoc
  | (apply _root_.GlobalTheory.LocalLatticeIntegral.exists_single_mem_latLoc <;> assumption)
  | (intros; apply _root_.GlobalTheory.LocalLatticeIntegral.exists_single_mem_latLoc <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LocalLatticeIntegral.exists_single_mem_latLoc <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LocalLatticeIntegral.exists_single_mem_latLoc ..)

end GlobalTheory.AdelicU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsThresholdCriticalLevelLowerBoundStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma GlobalTheory.Core.Deg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_threshold_criticalLevel_lower_bound : ∀ cb Cu : ℝ, 0 < cb → ∃ thr : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cT CT C0 : ℝ), thr ≤ Cl → (∀ τ, VV D τ = vand (lamSH D.R (D.hc τ))) → UnitaryVolumeMass.stTcritLow D large₂ C' Cl Cg cb Cu cT CT C0 := by
  first | exact @GlobalTheory.CritLevelSize.tcritLow_sizes | exact GlobalTheory.CritLevelSize.tcritLow_sizes | (intros; apply GlobalTheory.CritLevelSize.tcritLow_sizes <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdeleCharacterFinitePlaceComponentEqMulOfSplitStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideleCharacterFinitePlaceComponent_eq_mul_of_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (χ : (AF F ⊗[F] E)ˣ →* Circle), ∀ (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) (h : w.under (𝓞 F) = v), ∀ (w' : HeightOneSpectrum (𝓞 E)) (h' : w'.under (𝓞 F) = v), w ≠ w' → (∀ u : HeightOneSpectrum (𝓞 E), u.under (𝓞 F) = v ↔ u = w ∨ u = w') → ∀ x : (Fv F v ⊗[F] E)ˣ, ((charAt χ v x : Circle) : ℂ) = (locChar χ w (Units.map (toCompl h).toMonoidHom x) : ℂˣ) * (locChar χ w' (Units.map (toCompl h').toMonoidHom x) : ℂˣ) := by
  first | exact @GlobalTheory.LFun.charAt_eq_locChar_mul_locChar | exact GlobalTheory.LFun.charAt_eq_locChar_mul_locChar | (intros; apply GlobalTheory.LFun.charAt_eq_locChar_mul_locChar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdeleCharacterFinitePlaceComponentEqOfInertStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideleCharacterFinitePlaceComponent_eq_of_inert : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (χ : (AF F ⊗[F] E)ˣ →* Circle), ∀ (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) (h : w.under (𝓞 F) = v), IsInertAt F E v w → ∀ x : (Fv F v ⊗[F] E)ˣ, ((charAt χ v x : Circle) : ℂ) = (locChar χ w (Units.map (toCompl h).toMonoidHom x) : ℂˣ) := by
  first | exact @GlobalTheory.LFun.charAt_eq_locChar_of_isInertAt | exact GlobalTheory.LFun.charAt_eq_locChar_of_isInertAt | (intros; apply GlobalTheory.LFun.charAt_eq_locChar_of_isInertAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InvariantSphericalCoefficientEqZeroOrZonalStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariant_sphericalCoefficient_eq_zero_or_zonal : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : Lˣ) (σ : L →+* L) (q n : ℕ), IsUnramInv (ϖ : L) σ q → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GU σ n) V) (x : V) (α : Fin (n / 2) → ℂˣ), IsSatVecU (ϖ : L) q ρ x α → ∀ ℓ : V →ₗ[ℂ] ℂ, (∀ k ∈ KU σ n, ∀ g, ℓ (ρ (k * g) x) = ℓ (ρ g x)) → (ℓ x = 0 → ∀ g, ℓ (ρ g x) = 0) ∧ (ℓ x ≠ 0 → GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.IsZonal (ϖ : L) q α fun g => ℓ (ρ g x) / ℓ x) := by
  first | exact @GlobalTheory.ZonalCoeff.coeff_zero_or_zonal | exact GlobalTheory.ZonalCoeff.coeff_zero_or_zonal | (intros; apply GlobalTheory.ZonalCoeff.coeff_zero_or_zonal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsLatticeFrameAtPlaceDirectSumBlockDiagonalStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLatticeFrameAtPlace_directSum_blockDiagonal : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (w.adicCompletion E)), IsFrameAt w L a → IsFrameAt w (sumLat finSumFinEquiv L L) (blkGL finSumFinEquiv (a, a)) := by
  first | exact @GlobalTheory.LFun.isFrameAt_sumLat_blkGL | exact GlobalTheory.LFun.isFrameAt_sumLat_blkGL | (intros; apply GlobalTheory.LFun.isFrameAt_sumLat_blkGL <;> assumption)
end

