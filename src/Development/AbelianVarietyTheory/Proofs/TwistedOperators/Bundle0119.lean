import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0114
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0044
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0112
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0001
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0026
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0027
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0115
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0116
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0117

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockVolumeProdStatement
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.volM_blocks_eq_mul : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure]
    (A D : Type) [Fintype A] [Fintype D] (S₁₁ : Set (Matrix A A k)) (S₁₂ : Set (Matrix A D k))
    (S₂₁ : Set (Matrix D A k)) (S₂₂ : Set (Matrix D D k)),
    volM ν (A ⊕ D) (A ⊕ D)
        {x | x.toBlocks₁₁ ∈ S₁₁ ∧ x.toBlocks₁₂ ∈ S₁₂ ∧ x.toBlocks₂₁ ∈ S₂₁ ∧ x.toBlocks₂₂ ∈ S₂₂} =
      volM ν A A S₁₁ * volM ν A D S₁₂ * volM ν D A S₂₁ * volM ν D D S₂₂ := by
  first | exact @GlobalTheory.blockVolume_prod | exact GlobalTheory.blockVolume_prod | (intros; apply GlobalTheory.blockVolume_prod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContractsOfIsoDirectSumStatement
section
open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contracts_of_iso_directSum' : ∀ (H G I F V : Type) [Monoid H] [Monoid G] [AddCommGroup F] [Module ℂ F] [AddCommGroup V] [Module ℂ V] (A B : I → Type) [∀ i, AddCommGroup (A i)] [∀ i, Module ℂ (A i)] [∀ i, AddCommGroup (B i)] [∀ i, Module ℂ (B i)] (a : ∀ i, Representation ℂ H (A i)) (b : ∀ i, Representation ℂ G (B i)) (φ : Representation ℂ (H × G) F) (σ : Representation ℂ H V) (i₀ : I), Iso (Representation.directSum fun i => Representation.tprod ((a i).comp (MonoidHom.fst H G)) ((b i).comp (MonoidHom.snd H G))) φ → (∀ i, i ≠ i₀ → invFun ((a i).tprod σ) = ⊥) → Module.finrank ℂ (invFun ((a i₀).tprod σ)) = 1 → Contracts φ σ (b i₀) := by
  first | exact @GlobalTheory.OneFunctional.contracts_of_iso_directSum | exact GlobalTheory.OneFunctional.contracts_of_iso_directSum | (intros; apply GlobalTheory.OneFunctional.contracts_of_iso_directSum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContractsTensorProductChainStatement
section
open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contracts_tensorProduct_chain : ∀ (m : ℕ) (G : Fin (m + 1) → Type) [∀ j, Monoid (G j)] (F : Fin m → Type) [∀ j, AddCommGroup (F j)] [∀ j, Module ℂ (F j)] (V : Fin (m + 1) → Type) [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)] (φ : ∀ j : Fin m, Representation ℂ (G j.castSucc × G j.succ) (F j)) (σ : ∀ j, Representation ℂ (G j) (V j)), (∀ j : Fin m, Contracts (φ j) (σ j.castSucc) (σ j.succ)) → ∃ π : ((⨂[ℂ] j, F j) ⊗[ℂ] V 0) →ₗ[ℂ] V (Fin.last m), Function.Surjective π ∧ (∀ (g : ∀ j, G j) (f : ⨂[ℂ] j, F j) (v : V 0), π (PiTensorProduct.map (fun j => φ j (g j.castSucc, g j.succ)) f ⊗ₜ[ℂ] σ 0 (g 0) v) = σ (Fin.last m) (g (Fin.last m)) (π (f ⊗ₜ[ℂ] v))) ∧ ∀ l : Module.Dual ℂ ((⨂[ℂ] j, F j) ⊗[ℂ] V 0), (∀ g : ∀ j, G j, g (Fin.last m) = 1 → ∀ (f : ⨂[ℂ] j, F j) (v : V 0), l (PiTensorProduct.map (fun j => φ j (g j.castSucc, g j.succ)) f ⊗ₜ[ℂ] σ 0 (g 0) v) = l (f ⊗ₜ[ℂ] v)) → ∀ x, π x = 0 → l x = 0 := by
  first | exact @GlobalTheory.OneFunctional.contracts_chain | exact GlobalTheory.OneFunctional.contracts_chain | (intros; apply GlobalTheory.OneFunctional.contracts_chain <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubleCoverUpqKsetGeneratedByExp
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

noncomputable section

namespace GlobalTheory.CoverKGen

open GlobalTheory.RealPar GlobalTheory.RealPar.KStabLie GlobalTheory.RealPar.TorusWt Matrix

variable {p q : ℕ}

theorem blockOrd_std (p q : ℕ) :
    BlockOrd (p := p) (q := q) finSumFinEquiv (fun i => (finSumFinEquiv.symm i).isLeft) := by
  refine ⟨fun i => by simp, fun j => by simp, ?_⟩
  rintro (a | a) (b | b) hab
  · have hlt : a < b := hab
    simp only [finSumFinEquiv_apply_left, Fin.lt_def, Fin.val_castAdd]
    exact Fin.lt_def.mp hlt
  · simp [posC] at hab
  · simp [posC] at hab
  · have hlt : a < b := hab
    have := Fin.lt_def.mp hlt
    simp only [finSumFinEquiv_apply_right, Fin.lt_def, Fin.val_natAdd]
    omega

theorem exists_log (T : GrpData p q) {k : T.G} (hk : k ∈ T.Kset) :
    ∃ X, X ∈ upq p q ∧ IsKC X ∧ T.cov (T.expt X) = T.cov k := by
  have hB := blockOrd_std p q
  obtain ⟨Y, hY, hexp, -⟩ := Formalism.REAL.compact_exponential_surjective _ _ _ (mem_Kset hB T hk)
  letI : NormedRing (Mat p q) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℚ (Mat p q) := Matrix.linftyOpNormedAlgebra
  letI : NormedSpace ℂ (Mat p q) := Matrix.linftyOpNormedSpace
  letI : CompleteSpace (Mat p q) := FiniteDimensional.complete ℂ (Mat p q)
  letI : NormedRing (Matrix (Fin (p + q)) (Fin (p + q)) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℚ (Matrix (Fin (p + q)) (Fin (p + q)) ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedSpace ℂ (Matrix (Fin (p + q)) (Fin (p + q)) ℂ) := Matrix.linftyOpNormedSpace
  letI : CompleteSpace (Matrix (Fin (p + q)) (Fin (p + q)) ℂ) :=
    FiniteDimensional.complete ℂ (Matrix (Fin (p + q)) (Fin (p + q)) ℂ)
  let φ := Matrix.reindexAlgEquiv ℂ ℂ (finSumFinEquiv (m := p) (n := q))
  have hφc : Continuous φ := by
    rw [Matrix.coe_reindexAlgEquiv]
    exact continuous_id.matrix_reindex _ _
  have hφX : φ (φ.symm Y) = Y := φ.apply_symm_apply Y
  have hJ : φ (Jm p q) = Formalism.REAL.Jm (fun i => (finSumFinEquiv.symm i).isLeft) := by
    rw [Matrix.coe_reindexAlgEquiv]
    exact hB.reindex_Jm
  have hstar : ∀ M : Mat p q, φ Mᴴ = (φ M)ᴴ := fun M =>
    (Matrix.conjTranspose_reindex _ _ M).symm
  have hX : φ.symm Y ∈ upq p q := by
    show (φ.symm Y)ᴴ * Jm p q + Jm p q * φ.symm Y = 0
    apply φ.injective
    rw [map_add, map_mul, map_mul, hstar, hJ, hφX, map_zero]
    exact hY.1
  refine ⟨φ.symm Y, hX, ?_, ?_⟩
  · rw [isKC_iff]
    apply φ.injective
    rw [map_mul, map_mul, hJ, hφX]
    exact hY.2
  · apply Units.ext
    rw [T.expt_cov _ hX]
    apply φ.injective
    have hm : φ (NormedSpace.exp (φ.symm Y)) = NormedSpace.exp (φ (φ.symm Y)) :=
      NormedSpace.map_exp φ hφc _
    rw [hm, hφX, hexp]
    rfl

theorem torX_isKC (θ : Ix p q → ℝ) : IsKC (torX θ) := by
  intro a b hab
  have hne : a ≠ b := by
    rintro rfl
    exact hab (by cases a <;> trivial)
  simp [torX, Matrix.diagonal_apply_ne _ hne]

theorem cov_expt_torX (T : GrpData p q) (θ : Ix p q → ℝ) :
    ((T.cov (T.expt (torX θ)) : GL (Ix p q) ℂ) : Mat p q) =
      Matrix.diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I) := by
  rw [T.expt_cov _ (torX_mem θ)]
  unfold torX
  rw [Matrix.exp_diagonal, Pi.exp_def, Complex.exp_eq_exp_ℂ]

private theorem sq_expt_torX_sq_eq_exp (T : GrpData p q) (θ : Ix p q → ℝ) :
    ((T.sq (T.expt (torX θ)) : ℂˣ) : ℂ) ^ 2 =
      Complex.exp ((∑ a, (θ a : ℂ)) * Complex.I / 2) ^ 2 := by
  rw [T.sq_sq, cov_expt_torX, Matrix.det_diagonal, ← Complex.exp_sum, ← Complex.exp_nat_mul]
  congr 1
  rw [← Finset.sum_mul]
  push_cast
  ring

theorem sq_expt_torX (T : GrpData p q) (θ : Ix p q → ℝ) :
    ((T.sq (T.expt (torX θ)) : ℂˣ) : ℂ) = Complex.exp ((∑ a, (θ a : ℂ)) * Complex.I / 2) := by
  let f : ℝ → ℂ := fun t => ((T.sq (T.expt (t • torX θ)) : ℂˣ) : ℂ)
  let g : ℝ → ℂ := fun t => Complex.exp ((∑ a, ((t * θ a : ℝ) : ℂ)) * Complex.I / 2)
  have hsq : ∀ t, f t ^ 2 = g t ^ 2 := fun t => by
    simp only [f, g]
    rw [smul_torX]
    exact sq_expt_torX_sq_eq_exp T _
  have hg : ∀ t, g t ≠ 0 := fun t => Complex.exp_ne_zero _
  have hfc : Continuous f := by
    have h1 : Continuous fun t : ℝ => T.expt (t • torX θ) :=
      T.expt_cont.comp_continuous (continuous_id.smul continuous_const)
        (fun t => smul_mem_upq (torX_mem θ) t)
    have h2 : Continuous fun x : T.G => T.sq x := continuous_snd.comp T.emb.continuous
    exact Units.continuous_val.comp (h2.comp h1)
  have hgc : Continuous g := by fun_prop
  have hh : ∀ t, f t / g t = 1 ∨ f t / g t = -1 := fun t => by
    have h2 : (f t / g t) ^ 2 = 1 := by
      rw [div_pow, hsq t, div_self (pow_ne_zero 2 (hg t))]
    exact mul_self_eq_one_iff.mp (by rw [← sq]; exact h2)
  have h0 : f 0 / g 0 = 1 := by
    simp [f, g, T.expt_zero]
  have hcont : Continuous fun t => f t / g t := hfc.div hgc hg
  have h1 : f 1 / g 1 = 1 := by
    rcases hh 1 with h1 | h1
    · exact h1
    exfalso
    have hre : Continuous fun t => (f t / g t).re := Complex.continuous_re.comp hcont
    have hmem : (0 : ℝ) ∈ Set.Icc ((f 1 / g 1).re) ((f 0 / g 0).re) := by
      rw [h0, h1]
      norm_num
    obtain ⟨t, -, ht⟩ := intermediate_value_Icc' zero_le_one hre.continuousOn hmem
    rcases hh t with h2 | h2 <;> simp only [h2] at ht <;> norm_num at ht
  have hfg : f 1 = g 1 := (div_eq_one_iff_eq (hg 1)).mp h1
  simpa [f, g] using hfg

theorem kset_gen : ∀ (p q : ℕ), 1 ≤ p + q → ∀ (T : GrpData p q), ∀ k ∈ T.Kset,
    k ∈ Subgroup.closure (T.expt '' {Y | Y ∈ upq p q ∧ IsKC Y}) := by
  intro p q hpq T k hk
  have mem : ∀ X, X ∈ upq p q → IsKC X →
      T.expt X ∈ Subgroup.closure (T.expt '' {Y | Y ∈ upq p q ∧ IsKC Y}) :=
    fun X h1 h2 => Subgroup.subset_closure ⟨X, ⟨h1, h2⟩, rfl⟩
  obtain ⟨a0⟩ : Nonempty (Ix p q) := by
    rcases Nat.eq_zero_or_pos p with hp | hp
    · exact ⟨Sum.inr ⟨0, by omega⟩⟩
    · exact ⟨Sum.inl ⟨0, hp⟩⟩
  have hc := mem _ (torX_mem (Pi.single a0 (2 * Real.pi))) (torX_isKC (Pi.single a0 (2 * Real.pi)))
  have hcov : T.cov (T.expt (torX (Pi.single a0 (2 * Real.pi)))) = 1 := by
    apply Units.ext
    rw [cov_expt_torX, Units.val_one, ← Matrix.diagonal_one]
    congr 1
    funext a
    by_cases ha : a = a0
    · subst ha
      simp only [Pi.single_eq_same]
      push_cast
      exact Complex.exp_two_pi_mul_I
    · simp [Pi.single_eq_of_ne ha]
  have hsqc : T.sq (T.expt (torX (Pi.single a0 (2 * Real.pi)))) = -1 := by
    apply Units.ext
    rw [sq_expt_torX]
    have hs : (∑ a, (((Pi.single a0 (2 * Real.pi) : Ix p q → ℝ) a : ℝ) : ℂ)) = 2 * (Real.pi : ℂ) := by
      rw [Finset.sum_eq_single a0 (fun b _ hb => by simp [Pi.single_eq_of_ne hb]) (by simp)]
      simp
    have hpi : 2 * (Real.pi : ℂ) * Complex.I / 2 = Real.pi * Complex.I := by ring
    rw [hs, hpi, Complex.exp_pi_mul_I]
    simp
  obtain ⟨X, hX, hXK, hcovX⟩ := exists_log T hk
  have hy := mem X hX hXK
  have huniq : ∀ x : T.G, T.cov x = T.cov k → T.sq x = T.sq k → x = k := fun x h1 h2 =>
    (T.bij (T.cov k) (T.cov_mem k) (T.sq k) (T.sq_sq k)).unique ⟨h1, h2⟩ ⟨rfl, rfl⟩
  have hsq2 : ((T.sq (T.expt X) : ℂˣ) : ℂ) ^ 2 = ((T.sq k : ℂˣ) : ℂ) ^ 2 := by
    rw [T.sq_sq, T.sq_sq, hcovX]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq2 with h | h
  · rw [← huniq _ hcovX (Units.ext h)]
    exact hy
  · have hk' : T.expt X * T.expt (torX (Pi.single a0 (2 * Real.pi))) = k := by
      apply huniq
      · rw [map_mul, hcov, mul_one, hcovX]
      · apply Units.ext
        rw [map_mul, hsqc]
        simp [h]
    rw [← hk']
    exact Subgroup.mul_mem _ hy hc

end GlobalTheory.CoverKGen

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteDimensionalForallMapMemStatement
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteDimensional_forall_map_mem' : ∀ (p q : ℕ) (M : GKMod p q), AdmGK M → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V), IsKLieAct act → ∀ W : Submodule ℂ V, FiniteDimensional ℂ W → KStable act W → (∀ v ∈ W, v ∈ ⨆ μ : Ix p q → ℚ, wtSub act μ) → ∃ E : Submodule ℂ M.V, FiniteDimensional ℂ E ∧ ∀ φ : V →ₗ[ℂ] M.V, (∀ Z, IsKC Z → ∀ v, φ (act Z v) = M.act Z (φ v)) → ∀ v ∈ W, φ v ∈ E := by
  first | exact @GlobalTheory.KHomFinite.exists_finiteDimensional_forall_map_mem | exact GlobalTheory.KHomFinite.exists_finiteDimensional_forall_map_mem | (intros; apply GlobalTheory.KHomFinite.exists_finiteDimensional_forall_map_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGanGrossPrasadColumnWeightsStatement
section
open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ganGrossPrasad_column_weights : ∀ (S : Sizes) (Q : Entries S), Q.Good → ∃ kap : ∀ i : Fin (S.m + 1), DomWeight (S.nC i), (∀ r, (kap 0).dual.w r = hw Q.basePar r) ∧ (∀ r, (kap (Fin.last _)).dual.w r = hw Q.smallPar r) ∧ ∀ i : Fin S.m, StepW (Q.c i.rev - ((S.nC i.succ + 1) / 2 : ℕ)) (-Q.c i.rev + ((S.nC i.castSucc + 1) / 2 : ℕ)) (kap i.castSucc) (kap i.succ) := by
  first | exact @GlobalTheory.OneFunctional.ColumnWeights.exists_column_weights | exact GlobalTheory.OneFunctional.ColumnWeights.exists_column_weights | (intros; apply GlobalTheory.OneFunctional.ColumnWeights.exists_column_weights <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGanGrossPrasadRowWeightsStatement
section
open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ganGrossPrasad_row_weights : ∀ (S : Sizes) (Q : Entries S), Q.Good → ∃ lam : ∀ j : Fin (S.m + 1), DomWeight (S.nR j), (∀ i, (lam 0).w i = hw Q.psiPar i) ∧ (∀ i, (lam (Fin.last _)).w i = hw Q.bigPar i) ∧ ∀ j : Fin S.m, StepW (Q.e j - (S.nR j.succ / 2 : ℕ)) (-Q.e j + (S.nR j.castSucc / 2 : ℕ)) (lam j.castSucc) (lam j.succ) := by
  first | exact @GlobalTheory.OneFunctional.RowWeights.exists_row_weights | exact GlobalTheory.OneFunctional.RowWeights.exists_row_weights | (intros; apply GlobalTheory.OneFunctional.RowWeights.exists_row_weights <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPiTensorMvPolynomialProdEquivStatement
section
open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_piTensor_mvPolynomial_prod_equiv : ∀ (ι σ : Type) [Fintype ι], ∃ e : (⨂[ℂ] _ : ι, MvPolynomial σ ℂ) ≃ₗ[ℂ] MvPolynomial (ι × σ) ℂ, ∀ f : ι → MvPolynomial σ ℂ, e (PiTensorProduct.tprod ℂ f) = ∏ τ, rename (Prod.mk τ) (f τ) := by
  first | exact @GlobalTheory.PolyTensor.exists_piTensor_equiv | exact GlobalTheory.PolyTensor.exists_piTensor_equiv | (intros; apply GlobalTheory.PolyTensor.exists_piTensor_equiv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPiTensorShuffleEquivStatement
section
open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_piTensor_tmul_piTensor_linearEquiv_piTensor_tmul : ∀ (ι : Type) [Fintype ι] (F V : ι → Type) [∀ τ, AddCommGroup (F τ)] [∀ τ, Module ℂ (F τ)] [∀ τ, AddCommGroup (V τ)] [∀ τ, Module ℂ (V τ)], ∃ e : ((⨂[ℂ] τ, F τ) ⊗[ℂ] (⨂[ℂ] τ, V τ)) ≃ₗ[ℂ] (⨂[ℂ] τ, (F τ ⊗[ℂ] V τ)), ∀ (f : ∀ τ, F τ) (v : ∀ τ, V τ), e (PiTensorProduct.tprod ℂ f ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ v) = PiTensorProduct.tprod ℂ (fun τ => f τ ⊗ₜ[ℂ] v τ) := by
  first | exact @GlobalTheory.exists_piTensor_shuffle_equiv | exact GlobalTheory.exists_piTensor_shuffle_equiv | (intros; apply GlobalTheory.exists_piTensor_shuffle_equiv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockOnePlaceIsoDirectSumPartitions
section
open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum

namespace GlobalTheory.OneFunctional

theorem iso_directSum_fockOne : ∀ (a b : ℕ) (α β : ℤ), Iso (Representation.directSum fun i : GlobalTheory.GLDuality.Part (min a b) => Representation.tprod ((twist (detU a ^ α) ((irr a (GlobalTheory.GLDuality.pad a i)).comp (conjU a))).comp (MonoidHom.fst (U a) (U b))) ((twist (detU b ^ β) (irr b (GlobalTheory.GLDuality.pad b i))).comp (MonoidHom.snd (U a) (U b)))) (fockOne a b α β) := by
  intro a b α β
  obtain ⟨e⟩ := GlobalTheory.GLDuality.nonempty_equiv_polyRep a b
  obtain ⟨e, he⟩ := Iso.of_equiv e
  refine ⟨e, fun p x => ?_⟩
  have key : (Representation.directSum fun i : GlobalTheory.GLDuality.Part (min a b) => Representation.tprod
      ((twist (detU a ^ α) ((irr a (GlobalTheory.GLDuality.pad a i)).comp (conjU a))).comp (MonoidHom.fst (U a) (U b)))
      ((twist (detU b ^ β) (irr b (GlobalTheory.GLDuality.pad b i))).comp (MonoidHom.snd (U a) (U b)))) p x =
      ((((detU a ^ α) p.1 * (detU b ^ β) p.2 : ℂˣ) : ℂ)) •
      (Representation.directSum fun i : GlobalTheory.GLDuality.Part (min a b) =>
        GlobalTheory.GLDuality.pieceRep (MonoidHom.id (GL (Fin a) ℂ)) (MonoidHom.id (GL (Fin b) ℂ)) i)
        (unitaryIncl a (conjU a p.1), unitaryIncl b p.2) x := by
    apply DFinsupp.ext
    intro i
    change TensorProduct.map ((((detU a ^ α) p.1 : ℂˣ) : ℂ) • (irr a (GlobalTheory.GLDuality.pad a i) (conjU a p.1)))
        ((((detU b ^ β) p.2 : ℂˣ) : ℂ) • (irr b (GlobalTheory.GLDuality.pad b i) p.2)) (x i) =
      ((((detU a ^ α) p.1 * (detU b ^ β) p.2 : ℂˣ) : ℂ)) •
        TensorProduct.map (irr a (GlobalTheory.GLDuality.pad a i) (conjU a p.1)) (irr b (GlobalTheory.GLDuality.pad b i) p.2) (x i)
    rw [TensorProduct.map_smul_left, TensorProduct.map_smul_right, smul_smul, Units.val_mul, LinearMap.smul_apply]
  rw [key, map_smul, he]
  rfl

end GlobalTheory.OneFunctional
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsoOuterDualStatement
section
open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iso_dual_outer_outer_dual : ∀ (ι G : Type) [Fintype ι] [Group G] (V : ι → Type) [∀ τ, AddCommGroup (V τ)] [∀ τ, Module ℂ (V τ)] [∀ τ, FiniteDimensional ℂ (V τ)] (ρ : ∀ τ, Representation ℂ G (V τ)), Iso (outer ρ).dual (outer fun τ => (ρ τ).dual) := by
  first | exact @GlobalTheory.OneFunctional.iso_outer_dual | exact GlobalTheory.OneFunctional.iso_outer_dual | (intros; apply GlobalTheory.OneFunctional.iso_outer_dual <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsoTwistDetIrrShiftStatement
section
open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iso_twist_detU_pow_irr_of_weight_shift : ∀ (n : ℕ) (c : ℤ) (lam lam' : DomWeight n), (∀ i, lam'.w i = lam.w i + c) → Iso (twist (detU n ^ c) (irr n lam)) (irr n lam') := by
  first | exact @GlobalTheory.OneFunctional.iso_twist_det_irr_shift | exact GlobalTheory.OneFunctional.iso_twist_det_irr_shift | (intros; apply GlobalTheory.OneFunctional.iso_twist_det_irr_shift <;> assumption)
end

