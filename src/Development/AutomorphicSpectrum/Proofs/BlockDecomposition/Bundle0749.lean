import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0742
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegralConjInnerMulInnerOfIsEmptyEquiv
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0518
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0538
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0551
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0739
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0677
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0596
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0220
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0370
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0375
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0016
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0402
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0741
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0407
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0687
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0524
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0535
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ArchimedeanHaarScalingNorm
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0039
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0070
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0094
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0736

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralRightDerivativeEqZero
section
noncomputable section

open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ModelS.SkewInt

open scoped Matrix.Norms.Operator in

theorem exp_entry_hasDerivAt {n : ℕ} (X : Mat n) (t : ℝ) (i j : Fin n) :
    HasDerivAt (fun s : ℝ => (NormedSpace.exp (s • X) : Mat n) i j)
      ((NormedSpace.exp (t • X) * X : Mat n) i j) t := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X t
  let L : Mat n →L[ℝ] ℂ := LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)
  exact L.hasFDerivAt.comp_hasDerivAt t h

theorem exp_hasDerivAt {n : ℕ} (X : Mat n) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (NormedSpace.exp (s • X) : Mat n)) (NormedSpace.exp (t • X) * X) t := by
  have : HasDerivAt (fun s : ℝ => (fun i j => (NormedSpace.exp (s • X) : Mat n) i j : Fin n → Fin n → ℂ))
      (fun i j => (NormedSpace.exp (t • X) * X : Mat n) i j) t := by
    rw [hasDerivAt_pi]
    intro i
    rw [hasDerivAt_pi]
    intro j
    exact exp_entry_hasDerivAt X t i j
  exact this

theorem curve_hasDerivAt {n : ℕ} (k X : Mat n) (t : ℝ) :
    HasDerivAt (fun s : ℝ => k * (NormedSpace.exp (s • X) : Mat n)) (k * NormedSpace.exp (t • X) * X) t := by
  let L : Mat n →L[ℝ] Mat n := LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ k)
  have h := L.hasFDerivAt.comp_hasDerivAt t (exp_hasDerivAt X t)
  have e : L (NormedSpace.exp (t • X) * X) = k * NormedSpace.exp (t • X) * X := by
    rw [Matrix.mul_assoc]
    rfl
  exact h.congr_deriv e

theorem exp_mem_unitary {n : ℕ} {X : Mat n} (hX : Xᴴ = -X) (t : ℝ) :
    (NormedSpace.exp (t • X) : Mat n) ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose, ← Matrix.exp_conjTranspose, conjTranspose_smul,
    star_trivial, hX, smul_neg, Matrix.exp_neg]
  exact Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.isUnit_exp _))

theorem integral_Rd_skew : ∀ (n : ℕ) [MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ)] [BorelSpace (Matrix.unitaryGroup (Fin n) ℂ)] (κ : Measure (Matrix.unitaryGroup (Fin n) ℂ)) [IsFiniteMeasure κ] [κ.IsMulRightInvariant] (u : Mat n → ℂ), ContDiffOn ℝ ∞ u (GLs n) → ∀ X : Mat n, Xᴴ = -X → ∫ k : Matrix.unitaryGroup (Fin n) ℂ, Rd X u k.1 ∂κ = 0 := by
  intro n _ _ κ _ _ u hu X hX
  haveI : CompactSpace (Matrix.unitaryGroup (Fin n) ℂ) := GlobalTheory.compactSpace_unitaryGroup (Fin n) ℂ
  haveI : SecondCountableTopology (Mat n) := inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  haveI : SecondCountableTopology (Matrix.unitaryGroup (Fin n) ℂ) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  let kt : ℝ → Matrix.unitaryGroup (Fin n) ℂ := fun t => ⟨NormedSpace.exp (t • X), exp_mem_unitary hX t⟩
  have hval : ∀ (y : Matrix.unitaryGroup (Fin n) ℂ) (t : ℝ),
      y.1 * (NormedSpace.exp (t • X) : Mat n) = (y * kt t).1 := fun _ _ => rfl
  have hcv : Continuous fun k : Matrix.unitaryGroup (Fin n) ℂ => k.1 := continuous_subtype_val
  have hRd := GlobalTheory.CompanionTheory.RCalc.Rd_contDiffOn X hu
  have cU : Continuous fun k : Matrix.unitaryGroup (Fin n) ℂ => u k.1 :=
    hu.continuousOn.comp_continuous hcv unit_mem
  have cR : Continuous fun k : Matrix.unitaryGroup (Fin n) ℂ => Rd X u k.1 :=
    hRd.continuousOn.comp_continuous hcv unit_mem
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn cR.continuousOn
  have key := GlobalTheory.CompanionTheory.RCalc.ByParts.integral_deriv_eq_zero (μ := κ) (V := ℂ)
    (F := fun t y => u (y.1 * (NormedSpace.exp (t • X) : Mat n)))
    (F' := fun t y => Rd X u (y.1 * (NormedSpace.exp (t • X) : Mat n)))
    (K := Set.univ) isCompact_univ (ε := 1) one_pos C ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simpa using key
  · intro t _
    simp only [hval]
    exact cU.comp (continuous_mul_right (kt t))
  · simp only [hval]
    exact cR.comp (continuous_mul_right (kt 0))
  · intro y t _
    have hg : y.1 * (NormedSpace.exp (t • X) : Mat n) ∈ GLs n := by
      rw [hval]
      exact unit_mem _
    have h := (GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth hu hg).hasFDerivAt.comp_hasDerivAt t
      (curve_hasDerivAt y.1 X t)
    exact h
  · intro y hy
    exact absurd (Set.mem_univ y) hy
  · intro t _ y hy
    exact absurd (Set.mem_univ y) hy
  · intro t _ y _
    simp only [hval]
    exact hC _ (Set.mem_univ _)
  · intro t _
    simp only [hval]
    have h0 : kt 0 = 1 := by
      apply Subtype.ext
      simp [kt]
    rw [h0]
    simp only [mul_one]
    exact integral_mul_right_eq_self (fun y : Matrix.unitaryGroup (Fin n) ℂ => u y.1) (kt t)

end GlobalTheory.CompanionTheory.ModelS.SkewInt
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleSmoothModuleUnique
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

namespace GlobalTheory.CompanionTheory.CuspIrred

open scoped InnerProductSpace

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}
  {μ : Measure (GA E a)} [μ.IsHaarMeasure] [μ.IsMulRightInvariant]

theorem continuous_infGL' : Continuous (infGL E a) :=
  Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map
    ((continuous_infEq E).prodMk continuous_const : Continuous fun x : Cinf E => ((infEq E x, 0) : InfiniteAdeleRing E × Af E))))

theorem map_closure_le {C S : Submodule ℂ (L2 (latticeGL E a) μ)} (hC : C = S.topologicalClosure)
    (T : L2 (latticeGL E a) μ →L[ℂ] L2 (latticeGL E a) μ) (h : ∀ F ∈ S, T F ∈ C) {v : L2 (latticeGL E a) μ}
    (hv : v ∈ C) : T v ∈ C := by
  have hcl : IsClosed (C : Set (L2 (latticeGL E a) μ)) := hC ▸ Submodule.isClosed_topologicalClosure _
  have hle : S.topologicalClosure ≤ C.comap (T : L2 (latticeGL E a) μ →ₗ[ℂ] L2 (latticeGL E a) μ) :=
    Submodule.topologicalClosure_minimal _ h (hcl.preimage T.continuous)
  exact hle (hC ▸ hv)

theorem R_curve_mem {W : Submodule ℂ (Sm E a)} (hs : IsStable W)
    (hW : ∀ φ ∈ W, IsAutForm φ ∧ MemL2Quotient (latticeGL E a) μ φ.1) {c : ℝ → GL (Fin a) (Cinf E)} {X : GlobalTheory.CuspRep.Lie E a}
    (hc : Continuous c) (h0 : c 0 = 1) (hadd : ∀ s t, c (s + t) = c s * c t)
    (hX : HasDerivAt (fun t => toL (c t).val) X 0) {φ : Sm E a} (hφ : φ ∈ W) (h : MemL2Quotient (latticeGL E a) μ φ.1) (t : ℝ) :
    R (latticeGL E a) μ (infGL E a (c t)) h.toL2 ∈ (classes W μ).topologicalClosure := by
  set C := (classes W μ).topologicalClosure with hCdef
  have hCcl : IsClosed (C : Set (L2 (latticeGL E a) μ)) := Submodule.isClosed_topologicalClosure _
  have : CompleteSpace C := hCcl.completeSpace_coe
  let ψ : ℕ → Sm E a := fun k => ((lie E a X) ^ k) φ
  have hψ0 : ψ 0 = φ := rfl
  have hψs : ∀ k, ψ (k + 1) = lie E a X (ψ k) := fun k => by
    simp only [ψ, pow_succ', Module.End.mul_apply]
  have hmem : ∀ k, ψ k ∈ W := fun k => by
    induction k with
    | zero => exact hφ
    | succ k ih => rw [hψs]; exact hs (.lie X) _ ih
  have hM : ∀ k, MemL2Quotient (latticeGL E a) μ (ψ k).1 := fun k => (hW _ (hmem k)).2
  have hcont : ∀ k, Continuous (ψ k).1 := fun k => ContAut.continuous_of_isOpen_stab E a _ (hW _ (hmem k)).1.level
  let F : ℕ → ℝ → L2 (latticeGL E a) μ := fun k t => R (latticeGL E a) μ (infGL E a (c t)) (hM k).toL2
  obtain ⟨M, B, hb⟩ := GlobalTheory.T.lie_power_l2_factorial_bound E a μ W hs hW φ hφ X
  have hd : ∀ k t, HasDerivAt (F k) (F (k + 1) t) t := fun k t =>
    GlobalTheory.T.hasDerivAt_right_translate_toL2 (GA E a) (latticeGL E a) μ (ψ k).1 (ψ (k + 1)).1 (hM k) (hM (k + 1)) (fun t => infGL E a (c t))
      (hcont k) (hcont (k + 1)) (continuous_infGL'.comp hc) (by simp [h0]) (fun s t => by simp [hadd])
      (fun g => by
        have := hasDerivAt_curve (ψ k) g c X h0 hX
        rw [hψs]
        exact this) t
  have hn : ∀ k t, ‖F k t‖ ≤ M * B ^ k * (k.factorial : ℝ) := fun k t => (norm_R _ _).trans_le (hb k (hM k))
  have hF0 : ∀ k, F k 0 ∈ C := fun k => by
    have : F k 0 = (hM k).toL2 := by simp [F, h0]
    rw [this]
    exact Submodule.le_topologicalClosure _ (toL2_mem_classes (hmem k) (hM k))
  have hperp : F 0 t ∈ Cᗮᗮ := (Submodule.mem_orthogonal _ _).2 fun u hu =>
    GlobalTheory.T.analytic_orthogonal_vanishing _ F M B u hd hn (fun k => (Submodule.mem_orthogonal' _ _).1 hu _ (hF0 k)) t
  rw [Submodule.orthogonal_orthogonal] at hperp
  have e : (hM 0).toL2 = h.toL2 := rfl
  exact e ▸ hperp

theorem isSubrep_closure {W : Submodule ℂ (Sm E a)} (hs : IsStable W)
    (hW : ∀ φ ∈ W, IsAutForm φ ∧ MemL2Quotient (latticeGL E a) μ φ.1) :
    IsSubrep (R (latticeGL E a) μ) (classes W μ).topologicalClosure := by
  set C := (classes W μ).topologicalClosure with hCdef
  have hcls : ∀ F ∈ classes W μ, ∃ φ ∈ W, ∃ h : MemL2Quotient (latticeGL E a) μ φ.1, F = h.toL2 := fun F hF => by
    obtain ⟨φ, hφ, e⟩ := mem_classes.1 hF
    exact ⟨φ, hφ, (hW φ hφ).2, l2DiscreteQuotient_ext_iff_lift_ae_eq.2 (e.trans (hW φ hφ).2.lift_toL2_ae_eq.symm)⟩
  have hfin : ∀ k, ∀ v ∈ C, R (latticeGL E a) μ (finGL E a k) v ∈ C := fun k v hv =>
    map_closure_le hCdef _ (fun F hF => Submodule.le_topologicalClosure _
      (R_mem_classes (fun φ hφ => hs (.fin k) φ hφ) hF)) hv
  let S : Subgroup (GL (Fin a) (Cinf E)) :=
    { carrier := {y | (∀ v ∈ C, R (latticeGL E a) μ (infGL E a y) v ∈ C) ∧
        ∀ v ∈ C, R (latticeGL E a) μ (infGL E a y⁻¹) v ∈ C}
      one_mem' := by simp
      mul_mem' := fun {x y} hx hy => ⟨fun v hv => by
          rw [map_mul, map_mul]; exact hx.1 _ (hy.1 v hv), fun v hv => by
          rw [_root_.mul_inv_rev, map_mul, map_mul]; exact hy.2 _ (hx.2 v hv)⟩
      inv_mem' := fun {x} hx => ⟨hx.2, by simpa using hx.1⟩ }
  have hS : S = ⊤ := GlobalTheory.T.subgroup_one_parameter_closed_eq_top E a S fun c X hc h0 hadd hX t => by
    have key : ∀ t, ∀ v ∈ C, R (latticeGL E a) μ (infGL E a (c t)) v ∈ C := fun t v hv =>
      map_closure_le hCdef _ (fun F hF => by
        obtain ⟨φ, hφ, h, rfl⟩ := hcls F hF
        exact R_curve_mem hs hW hc h0 hadd hX hφ h t) hv
    have hinv : (c t)⁻¹ = c (-t) := inv_eq_of_mul_eq_one_right (by rw [← hadd, add_neg_cancel, h0])
    exact ⟨key t, by rw [show (c t)⁻¹ = c (-t) from hinv]; exact key (-t)⟩
  refine ⟨Submodule.isClosed_topologicalClosure _, fun g v hv => ?_⟩
  have hy : GeneralLinearGroup.map (pInf E) g ∈ S := hS ▸ Subgroup.mem_top _
  rw [← infGL_mul_finGL g, map_mul]
  exact hy.1 _ (hfin _ v hv)

theorem irred_module : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (H : Submodule ℂ (L2 (latticeGL E a) μ)), H ≤ L2cusp μ → IsIrredSubrep (R (latticeGL E a) μ) H → ∀ W : Submodule ℂ (Sm E a), IsStable W → W ≠ ⊥ → (∀ φ ∈ W, IsCuspForm φ ∧ (∀ t g, φ.1 (splitCentre E a t * g) = φ.1 g) ∧ ∃ h : MemL2Quotient (latticeGL E a) μ φ.1, h.toL2 ∈ H) → ∀ φ : Sm E a, (IsCuspForm φ ∧ (∀ t g, φ.1 (splitCentre E a t * g) = φ.1 g) ∧ ∃ h : MemL2Quotient (latticeGL E a) μ φ.1, h.toL2 ∈ H) → φ ∈ W := by
  rintro E _ _ _ a μ _ _ H hH hi W hs hne hW φ ⟨hφ, -, h, hh⟩
  have hW' : ∀ ψ ∈ W, IsAutForm ψ ∧ MemL2Quotient (latticeGL E a) μ ψ.1 := fun ψ hψ =>
    ⟨(hW ψ hψ).1.1, (hW ψ hψ).2.2.choose⟩
  have hsub := isSubrep_closure (μ := μ) hs hW'
  have hle : (classes W μ).topologicalClosure ≤ H := by
    refine Submodule.topologicalClosure_minimal _ (fun F hF => ?_) hi.1.1
    obtain ⟨ψ, hψ, e⟩ := mem_classes.1 hF
    obtain ⟨h', hh'⟩ := (hW ψ hψ).2.2
    rwa [show F = h'.toL2 from l2DiscreteQuotient_ext_iff_lift_ae_eq.2 (e.trans h'.lift_toL2_ae_eq.symm)]
  have hcl : (classes W μ).topologicalClosure = H := by
    refine (hi.2.2 _ hle hsub).resolve_left fun h0 => ?_
    obtain ⟨ψ, hψ, hψ0⟩ := (Submodule.ne_bot_iff _).1 hne
    obtain ⟨h', -⟩ := (hW ψ hψ).2.2
    refine toL2_ne_zero h' (ContAut.continuous_of_isOpen_stab E a ψ (hW ψ hψ).1.1.level)
      (fun e => hψ0 (Subtype.ext e)) ?_
    have : h'.toL2 ∈ (classes W μ).topologicalClosure :=
      Submodule.le_topologicalClosure _ (toL2_mem_classes hψ h')
    rw [h0] at this
    exact this
  exact GlobalTheory.T.irreducible_cuspidal_form_l2_mem E a μ H hH hi W hs (fun ψ hψ => ⟨(hW ψ hψ).1.1, (hW ψ hψ).2.2⟩) hcl φ hφ.1 h hh

end GlobalTheory.CompanionTheory.CuspIrred
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaCompactness
section
noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.StdUnn.HeightExists GlobalTheory.StdUnn.LeftInvSect
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ThTot

theorem iwaCpt : IwaCpt := by
  intro D n C hC
  have hCK : IsCompact (C * (K D n : Set (G D n))⁻¹) := hC.mul isCompact_K.inv
  have hQ : IsCompact ((↑) ⁻¹' (C * (K D n : Set (G D n))⁻¹) : Set (P D n)) :=
    (isClosed_P (D := D) (n := n)).isClosedEmbedding_subtypeVal.isCompact_preimage hCK
  have hL := hQ.image (continuous_leviBlock (D := D) (n := n))
  set L := leviBlock (D := D) (n := n) '' ((↑) ⁻¹' (C * (K D n : Set (G D n))⁻¹) : Set (P D n)) with hLdef
  have hR : Continuous fun a : GL (Fin n) (AE D) => (absA D (Matrix.GeneralLinearGroup.det a) : ℝ) :=
    NNReal.continuous_coe.comp (continuous_absE.comp continuous_detGL)
  obtain ⟨R, hRb⟩ := (hL.image hR).bddAbove
  refine ⟨Units.val '' L, (fun a : GL (Fin n) (AE D) => (a⁻¹).1) '' L, R, hL.image Units.continuous_val,
    hL.image Units.continuous_coe_inv, fun h hh => ?_⟩
  obtain ⟨q, hq, k, hk, rfl⟩ := Iwasawa.exists_mul D n h
  have hmem : leviBlock (D := D) (n := n) ⟨q, hq⟩ ∈ L :=
    ⟨⟨q, hq⟩, ⟨q * k, hh, k⁻¹, Set.inv_mem_inv.2 hk, by simp⟩, rfl⟩
  obtain ⟨m, t, b, e, hm, ht⟩ := exists_levi_unip hq (leviBlock (D := D) (n := n) ⟨q, hq⟩) rfl
  exact ⟨m, t, k, _, b, hk, by rw [e], hm, ht, ⟨_, hmem, rfl⟩, ⟨_, hmem, rfl⟩, hRb ⟨_, hmem, rfl⟩⟩

end GlobalTheory.CompanionTheory.ThTot

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaParabolicUnitary
section
open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ModelS

theorem exists_Pb_mul_unitary : ∀ (n : ℕ) (lev : Fin n → ℕ), Monotone lev → ∀ g ∈ GLs n,
    ∃ p ∈ GlobalTheory.CompanionTheory.ModelS.Pb lev, ∃ k : Matrix.unitaryGroup (Fin n) ℂ, g = p * k.1 := by
  intro n lev hlev g hg
  have hdet : g.det ≠ 0 := hg
  have hu : IsUnit gᴴ := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_conjTranspose]
    exact isUnit_iff_ne_zero.2 (by simpa using hdet)
  obtain ⟨k, hk, b, hb, ht⟩ := GlobalTheory.CompanionTheory.QR.exists_unitary_mul_blockTriangular gᴴ hu
  have hg' : g = bᴴ * kᴴ := by
    rw [← Matrix.conjTranspose_mul, ← hb, Matrix.conjTranspose_conjTranspose]
  have hkH : kᴴ ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff]
    have := (Matrix.mem_unitaryGroup_iff').1 hk
    simpa [Matrix.star_eq_conjTranspose] using this
  refine ⟨bᴴ, ⟨?_, ?_⟩, ⟨kᴴ, hkH⟩, hg'⟩
  · intro h0
    apply hdet
    rw [hg', Matrix.det_mul]
    have h0' : (bᴴ).det = 0 := h0
    rw [h0', zero_mul]
  · intro a c hac
    have hlt : a < c := by
      by_contra hn
      exact absurd (hlev (not_lt.1 hn)) (not_le.2 hac)
    have : b c a = 0 := ht hlt
    simp [Matrix.conjTranspose_apply, this]

end GlobalTheory.CompanionTheory.ModelS
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KActionSkewAdjointL2
section
noncomputable section

open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ModelS.KHerm

variable {n : ℕ}

def skA (a b : Fin n) : Mat n := (1 / 2 : ℝ) • (Matrix.single a b (1 : ℂ) - Matrix.single b a (1 : ℂ))

def skB (a b : Fin n) : Mat n := (1 / 2 : ℝ) • (Matrix.single a b Complex.I + Matrix.single b a Complex.I)

theorem skA_skew (a b : Fin n) : (skA a b)ᴴ = -skA a b := by
  ext i j
  simp only [skA, conjTranspose_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.neg_apply, Matrix.single_apply]
  by_cases h1 : a = j <;> by_cases h2 : b = i <;> by_cases h3 : a = i <;> by_cases h4 : b = j <;> simp_all

theorem skB_skew (a b : Fin n) : (skB a b)ᴴ = -skB a b := by
  ext i j
  simp only [skB, conjTranspose_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.neg_apply, Matrix.single_apply]
  by_cases h1 : a = j <;> by_cases h2 : b = i <;> by_cases h3 : a = i <;> by_cases h4 : b = j <;> simp_all

theorem Kf_apply (a b : Fin n) (h : SmF n) {g : Mat n} (hg : g ∈ GLs n) :
    (Kf a b h).1 g = Rd (skA a b) h.1 g - Complex.I * Rd (skB a b) h.1 g := by
  have h1 : (Kf a b h).1 g = (e1 DR a b h).1 g - (f1 DR b a h).1 g := by
    simp [Kf, e2, sub_eq_add_neg]
  rw [h1, orderedCechToCatCochainsOne_apply_valueAtSubset a b h hg, liftOneFormsToCompatible_apply b a h hg]
  simp only [Eu, Rd, skA, skB, Pi.smul_apply, Pi.add_apply, if_true, Bool.false_eq_true, if_false,
    Matrix.mul_smul, mul_sub, mul_add, map_smul, map_sub, map_add, smul_eq_mul, Complex.real_smul]
  push_cast
  ring

theorem Rd_neg (X : Mat n) (f : Mat n → ℂ) (g : Mat n) : Rd (-X) f g = -Rd X f g := by
  simp [Rd]

theorem Kf_apply_swap (a b : Fin n) (h : SmF n) {g : Mat n} (hg : g ∈ GLs n) :
    (Kf b a h).1 g = -Rd (skA a b) h.1 g - Complex.I * Rd (skB a b) h.1 g := by
  have hA : skA b a = -skA a b := by
    simp only [skA, ← smul_neg, neg_sub]
  have hB : skB b a = skB a b := by
    simp only [skB, add_comm]
  rw [Kf_apply b a h hg, hA, hB, Rd_neg]

theorem Rd_conj_mul (X : Mat n) {x y : Mat n → ℂ} (hx : ContDiffOn ℝ ∞ x (GLs n)) (hy : ContDiffOn ℝ ∞ y (GLs n))
    {g : Mat n} (hg : g ∈ GLs n) :
    Rd X (fun g => conj (x g) * y g) g = conj (Rd X x g) * y g + conj (x g) * Rd X y g := by
  have dx := (GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth hx hg).hasFDerivAt
  have dy := (GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth hy hg).hasFDerivAt
  have dc : HasFDerivAt (fun g => conj (x g)) (Complex.conjCLE.toContinuousLinearMap.comp (fderiv ℝ x g)) g :=
    Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp g dx
  have hm : HasFDerivAt (fun g => conj (x g) * y g) _ g := dc.mul dy
  simp only [Rd]
  rw [hm.fderiv]
  change conj (x g) * fderiv ℝ y g (g * X) + y g * conj (fderiv ℝ x g (g * X)) = _
  ring

theorem conj_mul_smooth {x y : Mat n → ℂ} (hx : ContDiffOn ℝ ∞ x (GLs n)) (hy : ContDiffOn ℝ ∞ y (GLs n)) :
    ContDiffOn ℝ ∞ (fun g => conj (x g) * y g) (GLs n) :=
  (Complex.conjCLE.toContinuousLinearMap.contDiff.comp_contDiffOn hx).mul hy

section Int

variable [MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ)] [BorelSpace (Matrix.unitaryGroup (Fin n) ℂ)]
  (κ : Measure (Matrix.unitaryGroup (Fin n) ℂ)) [IsFiniteMeasure κ]

omit [MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ)] [BorelSpace (Matrix.unitaryGroup (Fin n) ℂ)] in
theorem cont_on_unit {f : Mat n → ℂ} (hf : ContinuousOn f (GLs n)) :
    Continuous fun k : Matrix.unitaryGroup (Fin n) ℂ => f k.1 :=
  hf.comp_continuous continuous_subtype_val fun k => unit_mem k

theorem integrable_of_cont {f : Matrix.unitaryGroup (Fin n) ℂ → ℂ} (hf : Continuous f) : Integrable f κ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

end Int

end GlobalTheory.CompanionTheory.ModelS.KHerm

open GlobalTheory.CompanionTheory.ModelS.KHerm in

theorem GlobalTheory.CompanionTheory.ModelS.ipK_Kf_transpose : ∀ (n : ℕ) [MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ)] [BorelSpace (Matrix.unitaryGroup (Fin n) ℂ)] (κ : Measure (Matrix.unitaryGroup (Fin n) ℂ)) [IsFiniteMeasure κ], (∀ u : Mat n → ℂ, ContDiffOn ℝ ∞ u (GLs n) → ∀ X : Mat n, Xᴴ = -X → ∫ k : Matrix.unitaryGroup (Fin n) ℂ, Rd X u k.1 ∂κ = 0) → ∀ (a b : Fin n) (x y : GlobalTheory.CompanionTheory.ModelS.SmF n), GlobalTheory.CompanionTheory.ModelS.ipK κ (GlobalTheory.CompanionTheory.ModelS.Kf a b x) y = GlobalTheory.CompanionTheory.ModelS.ipK κ x (GlobalTheory.CompanionTheory.ModelS.Kf b a y) := by
  intro n _ _ κ _ hI a b x y
  have hx := x.2.1
  have hy := y.2.1
  have i1 : ∀ X : Mat n, Integrable (fun k : Matrix.unitaryGroup (Fin n) ℂ => conj (Rd X x.1 k.1) * y.1 k.1) κ :=
    fun X => integrable_of_cont κ ((Complex.continuous_conj.comp
      (cont_on_unit (GlobalTheory.CompanionTheory.RCalc.Rd_contDiffOn X hx).continuousOn)).mul (cont_on_unit hy.continuousOn))
  have i2 : ∀ X : Mat n, Integrable (fun k : Matrix.unitaryGroup (Fin n) ℂ => conj (x.1 k.1) * Rd X y.1 k.1) κ :=
    fun X => integrable_of_cont κ ((Complex.continuous_conj.comp (cont_on_unit hx.continuousOn)).mul
      (cont_on_unit (GlobalTheory.CompanionTheory.RCalc.Rd_contDiffOn X hy).continuousOn))
  have key : ∀ X : Mat n, Xᴴ = -X → (∫ k, conj (Rd X x.1 k.1) * y.1 k.1 ∂κ) + ∫ k, conj (x.1 k.1) * Rd X y.1 k.1 ∂κ = 0 := by
    intro X hX
    rw [← integral_add (i1 X) (i2 X), ← hI _ (conj_mul_smooth hx hy) X hX]
    exact integral_congr_ae (Filter.Eventually.of_forall fun k => (Rd_conj_mul X hx hy (unit_mem k)).symm)
  have L : ipK κ (Kf a b x) y = (∫ k, conj (Rd (skA a b) x.1 k.1) * y.1 k.1 ∂κ) +
      Complex.I * ∫ k, conj (Rd (skB a b) x.1 k.1) * y.1 k.1 ∂κ := by
    rw [← integral_const_mul, ← integral_add (i1 _) ((i1 _).const_mul _)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp only [Kf_apply a b x (unit_mem k), map_sub, map_mul, Complex.conj_I]
    ring
  have R : ipK κ x (Kf b a y) = -((∫ k, conj (x.1 k.1) * Rd (skA a b) y.1 k.1 ∂κ) +
      Complex.I * ∫ k, conj (x.1 k.1) * Rd (skB a b) y.1 k.1 ∂κ) := by
    rw [← integral_const_mul, ← integral_add (i2 _) ((i2 _).const_mul _), ← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp only [Kf_apply_swap a b y (unit_mem k)]
    ring
  rw [L, R]
  linear_combination key _ (skA_skew a b) + Complex.I * key _ (skB_skew a b)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsInjectiveOfSocle
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

namespace GlobalTheory.CompanionTheory.Multisegment

theorem inShW_of_wd_cosocle {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hSeg : LSegJacquet k)
    {𝔫 : Multiset (Segment k)} {N h h' : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin N) k) V} (Δ : Fin h → Segment k) (Γ : Fin h' → Segment k)
    (v : Fin h' → IrrGL k) (hd : ∑ a, (v a).1 = N) (hΓ : IsOrderedForm Γ 𝔫)
    (hv : ∀ i, IsLSeg (Γ i) (v i).rep) (hc : IsCosocle π (prodIrr v hd)) (hw : Wd π (wtW Δ)) :
    InShW 𝔫 (wtW Δ) := by
  have h1 : Wd (prodIrr v hd) (wtW Δ) :=
    GlobalTheory.T.word_occurs_of_subquotient (prodIrr v hd) π (isSmooth_prodIrr v hd) hc.isSubquotient _ hw
  have h2 := GlobalTheory.T.segment_product_word_in_shuffle hA hSeg v hd Γ hv (wtW Δ) (GlobalTheory.T.ordered_word_letters_cuspidal Δ) h1
  rwa [hΓ.1] at h2

theorem lInjective {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hSoc : LSocleGL k) (hSeg : LSegJacquet k) : LInjective k := by
  intro 𝔪 𝔫 x h𝔪 h𝔫
  obtain ⟨h, u, hd, ⟨Δ, hΔ, hu⟩, hc⟩ := id h𝔪
  obtain ⟨h', v, hd', ⟨Γ, hΓ, hv⟩, hc'⟩ := id h𝔫
  have wΔ : Wd x.rep (wtW Δ) := GlobalTheory.T.langlands_rep_ordered_word_occurs hA hSoc hSeg 𝔪 x.rep h𝔪 h Δ hΔ
  have wΓ : Wd x.rep (wtW Γ) := GlobalTheory.T.langlands_rep_ordered_word_occurs hA hSoc hSeg 𝔫 x.rep h𝔫 h' Γ hΓ
  exact GlobalTheory.T.ordered_forms_mutual_shuffle_eq hA 𝔪 𝔫 h h' Δ Γ hΔ hΓ
    (inShW_of_wd_cosocle hA hSeg Δ Γ v hd' hΓ hv hc' wΔ)
    (inShW_of_wd_cosocle hA hSeg Γ Δ u hd hΔ hu hc wΓ)

end GlobalTheory.CompanionTheory.Multisegment
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatrixPreservesIntegersAlmostAllStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef GlobalTheory.CompanionTheory.SiegelND.Coef.TestN
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_preserves_integers_almost_all : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι F), A.det ≠ 0 → ∃ T : Finset (HeightOneSpectrum (𝓞 F)), ∀ v, v ∉ T → ∀ x : ι → Fv F v, (∀ i, (A.map (algebraMap F (Fv F v))).mulVec x i ∈ v.adicCompletionIntegers F) ↔ ∀ i, x i ∈ v.adicCompletionIntegers F := by
  first | exact @GlobalTheory.CompanionTheory.MatInt.exists_finset_mulVec_integral_iff | exact GlobalTheory.CompanionTheory.MatInt.exists_finset_mulVec_integral_iff | (intros; apply GlobalTheory.CompanionTheory.MatInt.exists_finset_mulVec_integral_iff <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NondegenerateUnipotentPairingSchwartzStatement
section
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd GlobalTheory.SplitWeil GlobalTheory.JHMult GlobalTheory.CompanionTheory.BZShell GlobalTheory.CompanionTheory.MirPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nondegenerate_unipotent_pairing_schwartz : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (d : ℕ) (hd : 0 < d) (R R' : MRep k d) (hR' : IsSmooth R'.ρ) {V V' : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [Nontrivial V]
    (B : R.V →ₗ[ℂ] R'.V →ₗ[ℂ] ℂ) (hB : ∀ x v v', B (R.ρ (uM d x) v) (R'.ρ (uM d x) v') = B v v')
    (hn : ∀ v, v ≠ 0 → ∃ v', B v v' ≠ 0)
    (ι : SchF k d V →ₗ[ℂ] R.V) (hι : Function.Injective ι) (hιs : ∀ x f, ι (shiftF x f) = R.ρ (uM d x) (ι f))
    (ι' : SchF k d V' →ₗ[ℂ] R'.V) (hιs' : ∀ x f, ι' (shiftF x f) = R'.ρ (uM d x) (ι' f))
    (hr : ∀ x v, R'.ρ (uM d x) v - v ∈ LinearMap.range ι')
    (hC : ∀ f f' x, B (ι f) (ι' (shiftF x f')) = B (ι f) (ι' f')),
    False := by
  first | exact @GlobalTheory.CompanionTheory.BZShell.Radical.false_of_translation_invariant | exact GlobalTheory.CompanionTheory.BZShell.Radical.false_of_translation_invariant | (intros; apply GlobalTheory.CompanionTheory.BZShell.Radical.false_of_translation_invariant <;> assumption)
end

