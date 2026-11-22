import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Development.AbelianVarietyTheory.Definitions.Foundations.LatticeIntegralCoordinates
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0013
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0006
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ThetaConstantWeber
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaTaylorCoeffAlgebraicAndConjugate
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsVariableChangeEqLatticeCurve
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.DifferentiableAtDerivAtZero
import Formalism.GL3MeanSquares.HookFormulaTorsion.Bundle0004
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0002
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0011
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FundamentalDomainNeZero
import Formalism.LocalRingCardinality.Lemmas
import Formalism.SharpRestriction.InertJacobiLevels.Bundle0007
import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0003
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LogCondLeThree
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AuxiliaryPrimeMemAvoidedPrimes
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate
import Formalism.LocalToGlobal.GlobalTheory.GL5.PClassDecomp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0169
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0116
import Formalism.LocalRingCardinality.DataCD
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0019
import Formalism.GL3MeanSquares.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0051
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0174
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0037
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoprimeFourMulTwoPow
import Development.AutomorphicArithmetic.CharacterBoxes.ThinChoice

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HalfPeriodWeierstrassValueMemConj
section
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients GlobalTheory.IndefiniteRowSideFullHecke

noncomputable section

namespace GlobalTheory.HalfPeriodValue

open Formalism.MainNotions.StandardLatticesGL3 (wpF cj FixK rhoBar StarPt w0 InRationalLattice)

theorem wpF_add_of_mem {Λ : AddSubgroup ℂ} (h : GlobalTheory.ThetaConj.IsLat Λ) {z ω : ℂ} (hz : z ∉ Λ)
    (hω : ω ∈ Λ) : wpF Λ (z + ω) = wpF Λ z := by
  obtain ⟨L, hL⟩ := h.exists_periodPair
  have hd := GlobalTheory.LatticeInvariants.invariants_dictionary L Λ hL
  have hzω : z + ω ∉ Λ := fun hh => hz (by simpa using Λ.sub_mem hh hω)
  rw [(hd.2.2.2.2.1 _ hzω).1, (hd.2.2.2.2.1 _ hz).1]
  exact L.weierstrassP_add_coe z ⟨ω, (hL ω).1 hω⟩

theorem cmGenerator_mul_mem_curveLattice {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (h : Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ) :
    ∀ z ∈ lamOf D cc δ, w0 D * z ∈ lamOf D cc δ := by
  obtain ⟨a, ha⟩ := GlobalTheory.NormSum.exists_integer_map_eq_w0 D
  rw [← ha]
  exact (GlobalTheory.CurveLattice.lattice_of_curve D (GlobalTheory.InducedType.induced_type D).1 cc δ h).2.2.2.2 a

theorem key_of_fix {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (h : Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ)
    (ρ : (⊤ : IntermediateField ℚ ℂ) →ₐ[ℚ] ℂ) (hK : FixK D ⊤ ρ) {t t' : ℂ}
    (ht : Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t)
    (ht' : Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (lamConj ⊤ ρ (lamOf D cc δ)) t') :
    t' ∉ lamConj ⊤ ρ (lamOf D cc δ) ∧
      wpF (lamConj ⊤ ρ (lamOf D cc δ)) t' = cj ⊤ ρ (wpF (lamOf D cc δ) t) := by
  obtain ⟨hex, -, -, -, hmul, hord, -⟩ :=
    GlobalTheory.T.galStar_complexMultiplication_points D cc δ h ⊤ ρ hK IntermediateField.mem_top IntermediateField.mem_top
  obtain ⟨cc', δ', h', -, hL⟩ :=
    GlobalTheory.T.conjugate_curveDatum_lattice_isCurveLattice D cc δ h ⊤ ρ hK IntermediateField.mem_top IntermediateField.mem_top 1 one_pos
  rw [GlobalTheory.ThetaConj.twoTorsionCMPoint_iff] at ht ht'
  obtain ⟨a, ha⟩ := GlobalTheory.NormSum.exists_integer_map_eq_w0 D
  have ha' : D.host.φ₀ ((((1 - a : 𝓞 D.host.K) : D.host.K) : D.host.E)) = 1 - w0 D := by
    rw [← ha]
    change D.host.φ₀ (algebraMap D.host.K D.host.E (algebraMap (𝓞 D.host.K) D.host.K (1 - a))) = _
    rw [map_sub, map_sub, map_sub, map_one, map_one, map_one]
    rfl
  have htn : t ∉ lamOf D cc δ := fun hh => ht.2.1 (cmGenerator_mul_mem_curveLattice h _ hh)
  obtain ⟨t'', ht''⟩ := hex t ⟨2, by norm_num, by exact_mod_cast ht.1⟩
    (Or.inr ⟨IntermediateField.mem_top, IntermediateField.mem_top⟩)
  have e2 := (hord 2 _ _ ht'').1 (by exact_mod_cast ht.1)
  have ea := (hord 1 _ _ (hmul a _ _ ht'')).2
  have eb := (hord 1 _ _ (hmul (1 - a) _ _ ht'')).2
  rw [ha] at ea
  rw [ha'] at eb
  simp only [Nat.cast_one, one_mul, Nat.cast_ofNat] at e2 ea eb
  obtain ⟨k, hk⟩ := GlobalTheory.ThetaConj.weylMatrix_mul_apply D
  have hlat : GlobalTheory.ThetaConj.IsLat (lamConj ⊤ ρ (lamOf D cc δ)) := hL ▸ GlobalTheory.ThetaConj.isLat_lamOf h'
  have hdiff : t' - t'' ∈ lamConj ⊤ ρ (lamOf D cc δ) :=
    GlobalTheory.ThetaConj.two_torsion_unique hlat (w0 D) k hk ht'.1 ht'.2.1 ht'.2.2 e2
      (fun hh => ht.2.1 (ea hh)) (fun hh => ht.2.2 (eb hh)) (by rw [hL]; exact cmGenerator_mul_mem_curveLattice h')
  rcases ht'' with ⟨hin, -⟩ | ⟨-, hn'', -, -, hwp, -⟩
  · exact absurd hin htn
  · refine ⟨fun hh => hn'' (by simpa using (lamConj ⊤ ρ (lamOf D cc δ)).sub_mem hh hdiff), ?_⟩
    rw [← hwp, ← wpF_add_of_mem hlat hn'' hdiff, add_sub_cancel]

theorem wpF_conj (Λ : AddSubgroup ℂ) (z : ℂ) :
    wpF (Λ.map (starRingEnd ℂ).toAddMonoidHom) (starRingEnd ℂ z) = starRingEnd ℂ (wpF Λ z) := by
  let e : {w : ℂ // w ∈ Λ ∧ w ≠ 0} ≃
      {w : ℂ // w ∈ Λ.map (starRingEnd ℂ).toAddMonoidHom ∧ w ≠ 0} :=
    { toFun := fun w => ⟨starRingEnd ℂ w, by rw [GlobalTheory.ThetaConj.mem_conj, Complex.conj_conj]; exact w.2.1,
        by simpa using w.2.2⟩
      invFun := fun w => ⟨starRingEnd ℂ w, GlobalTheory.ThetaConj.mem_conj.1 w.2.1, by simpa using w.2.2⟩
      left_inv := fun w => by ext; simp
      right_inv := fun w => by ext; simp }
  unfold wpF
  rw [map_add, Complex.conj_tsum, ← e.tsum_eq]
  simp [e, map_sub]
  rfl

theorem key_top {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (h : Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ)
    (ρ : (⊤ : IntermediateField ℚ ℂ) →ₐ[ℚ] ℂ) {t t' : ℂ}
    (ht : Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t)
    (ht' : Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (lamConj ⊤ ρ (lamOf D cc δ)) t') :
    t' ∉ lamConj ⊤ ρ (lamOf D cc δ) ∧
      wpF (lamConj ⊤ ρ (lamOf D cc δ)) t' = cj ⊤ ρ (wpF (lamOf D cc δ) t) := by
  obtain ⟨hK, hT, -⟩ := GlobalTheory.T.cmTheta_complexConjugation_compatible D cc δ h ⊤ ρ
    ⟨fun _ _ => IntermediateField.mem_top, IntermediateField.mem_top, IntermediateField.mem_top⟩
  rcases hK with hK | hK
  · exact key_of_fix h ρ hK ht ht'
  · have hL : lamConj ⊤ (rhoBar ⊤ ρ) (lamOf D cc δ) =
        (lamConj ⊤ ρ (lamOf D cc δ)).map (starRingEnd ℂ).toAddMonoidHom := congrArg Tor.abelian₂ hT
    obtain ⟨hn, hw⟩ := key_of_fix h _ hK (t' := starRingEnd ℂ t') ht (hL ▸ GlobalTheory.ThetaConj.twoTorsionCMPoint_complexConj ht')
    rw [hL, wpF_conj, GlobalTheory.ThetaConj.cj_rhoBar] at hw
    rw [hL, GlobalTheory.ThetaConj.mem_conj, Complex.conj_conj] at hn
    exact ⟨hn, (starRingEnd ℂ).injective hw⟩

theorem halfPeriod_value : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M : IntermediateField ℚ ℂ)
    [FiniteDimensional ℚ M] (t : (M →ₐ[ℚ] ℂ) → ℂ), SignedLogMeans.HidaSetting D cc δ M t →
    ∃ e g : M, (g : ℂ) = g2 (lamOf D cc δ) ∧ lamConj M M.val (lamOf D cc δ) = lamOf D cc δ ∧
      ∀ ρ : M →ₐ[ℚ] ℂ, Formalism.MainNotions.TaylorLogMetric.discr (lamConj M ρ (lamOf D cc δ)) = 1 ∧
        g2 (lamConj M ρ (lamOf D cc δ)) = ρ g ∧ t ρ ∉ lamConj M ρ (lamOf D cc δ) ∧
        Formalism.MainNotions.StandardLatticesGL3.wpF (lamConj M ρ (lamOf D cc δ)) (t ρ) = ρ e := by
  intro D cc δ M _ t hS
  obtain ⟨hcc, hδ, hdata, ht⟩ := hS
  have h : Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ := ⟨hcc, hδ⟩
  have hg2 : g2 (lamOf D cc δ) ∈ M := hdata.2.1
  have hg3 : g3 (lamOf D cc δ) ∈ M := hdata.2.2
  have hlat := GlobalTheory.ThetaConj.isLat_lamOf h
  have hdisc : Formalism.MainNotions.TaylorLogMetric.discr (lamOf D cc δ) = 1 :=
    (GlobalTheory.CurveLattice.lattice_of_curve D (GlobalTheory.InducedType.induced_type D).1 cc δ h).2.2.1
  have hself : lamConj M M.val (lamOf D cc δ) = lamOf D cc δ :=
    GlobalTheory.ThetaConj.lamConj_eq_self hlat
      (by unfold Formalism.MainNotions.StandardLatticesGL3.cj Formalism.MainNotions.TaylorLogMetric.liftM; rw [dif_pos hg2]; rfl)
      (by unfold Formalism.MainNotions.StandardLatticesGL3.cj Formalism.MainNotions.TaylorLogMetric.liftM; rw [dif_pos hg3]; rfl)
  have ht0 : Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) (t M.val) := by
    have := ht M.val
    rw [hself] at this
    exact this
  have he : wpF (lamOf D cc δ) (t M.val) ∈ M := by
    obtain ⟨y, hy⟩ := GlobalTheory.GaloisDescent.complex_mem_range_of_forall_algEquiv (K := M)
      (wpF (lamOf D cc δ) (t M.val)) (fun σ => by
        have hσ : ∀ z ∈ M, cj ⊤ (GlobalTheory.ThetaConj.topHom (σ : ℂ →+* ℂ)) z = z := fun z hz => by
          rw [GlobalTheory.ThetaConj.cj_top]; exact σ.commutes ⟨z, hz⟩
        have hL := GlobalTheory.ThetaConj.lamConj_eq_self hlat (hσ _ hg2) (hσ _ hg3)
        have := (key_top h (GlobalTheory.ThetaConj.topHom (σ : ℂ →+* ℂ)) ht0 (by rw [hL]; exact ht0)).2
        rw [hL, GlobalTheory.ThetaConj.cj_top] at this
        exact this.symm)
    rw [← hy]
    exact y.2
  have hg2M : Formalism.MainNotions.TaylorLogMetric.liftM M (g2 (lamOf D cc δ)) = ⟨_, hg2⟩ := by simp [Formalism.MainNotions.TaylorLogMetric.liftM, hg2]
  have hg3M : Formalism.MainNotions.TaylorLogMetric.liftM M (g3 (lamOf D cc δ)) = ⟨_, hg3⟩ := by simp [Formalism.MainNotions.TaylorLogMetric.liftM, hg3]
  have hone : (⟨_, hg2⟩ : M) ^ 3 - 27 * (⟨_, hg3⟩ : M) ^ 2 = 1 :=
    by
    have := hdisc
    unfold Formalism.MainNotions.TaylorLogMetric.discr at this
    ext; push_cast; exact this
  refine ⟨⟨_, he⟩, ⟨_, hg2⟩, rfl, hself, fun ρ => ?_⟩
  have hρ1 : ρ ⟨_, hg2⟩ ^ 3 - 27 * ρ ⟨_, hg3⟩ ^ 2 = 1 := by
    rw [← map_pow, ← map_pow, ← map_ofNat ρ 27, ← map_mul, ← map_sub, hone, map_one]
  have hspec : g2 (lamConj M ρ (lamOf D cc δ)) = ρ ⟨_, hg2⟩ ∧
      g3 (lamConj M ρ (lamOf D cc δ)) = ρ ⟨_, hg3⟩ := by
    obtain ⟨L0, hL0⟩ := hlat.exists_periodPair
    obtain ⟨L', h2', h3'⟩ := (GlobalTheory.LatticeInvariants.invariants_dictionary L0 _ hL0).2.2.2.2.2.2 _ _
      (by rw [hρ1]; exact one_ne_zero)
    have hw := GlobalTheory.LatticeInvariants.invariants_dictionary L' L'.lattice.toAddSubgroup (fun _ => Iff.rfl)
    have hs := Classical.epsilon_spec (p := fun Λ' : AddSubgroup ℂ =>
      g2 Λ' = ρ (Formalism.MainNotions.TaylorLogMetric.liftM M (g2 (lamOf D cc δ))) ∧
        g3 Λ' = ρ (Formalism.MainNotions.TaylorLogMetric.liftM M (g3 (lamOf D cc δ))))
      ⟨L'.lattice.toAddSubgroup, by rw [hw.1, h2', hg2M], by rw [hw.2.1, h3', hg3M]⟩
    exact ⟨hs.1.trans (congrArg ρ hg2M), hs.2.trans (congrArg ρ hg3M)⟩
  have hcM : Set.Countable (M : Set ℂ) := (Algebraic.countable ℚ ℂ).mono fun x hx =>
    show IsAlgebraic ℚ x from
      (IntermediateField.isAlgebraic_iff (x := (⟨x, hx⟩ : M))).mp (Algebra.IsAlgebraic.isAlgebraic _)
  haveI : Countable M := hcM.to_subtype
  obtain ⟨σ, hσ⟩ := GlobalTheory.GaloisDescent.exists_complex_ringEquiv_comp_eq (K := M) M.val.toRingHom ρ.toRingHom
  have hcj : ∀ z (hz : z ∈ M), cj M ρ z = cj ⊤ (GlobalTheory.ThetaConj.topHom σ.toRingHom) z := fun z hz => by
    rw [GlobalTheory.ThetaConj.cj_of_mem _ _ hz, GlobalTheory.ThetaConj.cj_top]
    exact (hσ ⟨z, hz⟩).symm
  have hL : lamConj M ρ (lamOf D cc δ) = lamConj ⊤ (GlobalTheory.ThetaConj.topHom σ.toRingHom) (lamOf D cc δ) :=
    GlobalTheory.ThetaConj.lamConj_congr (hcj _ hg2) (hcj _ hg3)
  have ht' : Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (lamConj ⊤ (GlobalTheory.ThetaConj.topHom σ.toRingHom) (lamOf D cc δ)) (t ρ) := by
    have := ht ρ
    rw [hL] at this
    exact this
  obtain ⟨hn, hw⟩ := key_top h (GlobalTheory.ThetaConj.topHom σ.toRingHom) ht0 ht'
  refine ⟨?_, hspec.1, hL ▸ hn, ?_⟩
  · unfold Formalism.MainNotions.TaylorLogMetric.discr
    rw [hspec.1, hspec.2, hρ1]
  · rw [hL, hw, GlobalTheory.ThetaConj.cj_top]
    exact hσ ⟨_, he⟩

end GlobalTheory.HalfPeriodValue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsOrthogonalComplementUnitaryFrameOfMatrix
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct

namespace GlobalTheory.PerpFrameOfMatrix

theorem herm_eq_dot {P Q : ℕ} (u v : ActionCoordinates.Wsp P Q) :
    ActionCoordinates.herm u v = star v ⬝ᵥ Formalism.UG.Jpq P Q *ᵥ u := by
  simp [ActionCoordinates.herm, ActionCoordinates.sgn, Formalism.UG.Jpq, fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type,
    mul_comm, neg_mulVec]

theorem isPerpFrame_of_matrix : ∀ (P Q P' Q' : ℕ), P' + Q' + 1 = P + Q → ∀ x : ActionCoordinates.Wsp P Q, ActionCoordinates.qf x ≠ 0 → ∀ C : Matrix (Fin P ⊕ Fin Q) (Fin P' ⊕ Fin Q') ℂ, Cᴴ * Formalism.UG.Jpq P Q * C = Formalism.UG.Jpq P' Q' → (Cᴴ * Formalism.UG.Jpq P Q) *ᵥ x = 0 → ∀ ι : UpqT P' Q' → UpqT P Q, (∀ b, UpqT.mat (ι b) * C = C * UpqT.mat b ∧ UpqT.mat (ι b) *ᵥ x = x) → ActionCoordinates.IsPerpFrame x (Matrix.toLin' C) ι := by
  intro P Q P' Q' hc x hx C h1 h2 ι hι
  have hx' : star x ⬝ᵥ Formalism.UG.Jpq P Q *ᵥ x ≠ 0 := by
    rw [← herm_eq_dot, ActionCoordinates.herm_self]; exact_mod_cast hx
  have hperp : ∀ v, star x ⬝ᵥ Formalism.UG.Jpq P Q *ᵥ (C *ᵥ v) = 0 := fun v => by
    have h3 : star x ᵥ* (Formalism.UG.Jpq P Q * C) = 0 := by
      have := congrArg star h2
      rwa [star_mulVec, conjTranspose_mul, conjTranspose_conjTranspose,
        GlobalTheory.UnfoldingCompare.Jpq_conjTranspose, star_zero] at this
    rw [mulVec_mulVec, dotProduct_mulVec, h3, zero_dotProduct]
  refine ⟨fun v w => ?_, fun y => ⟨fun hy => ?_, ?_⟩, fun g => ⟨(hι g).2, fun v => ?_⟩⟩
  · rw [herm_eq_dot, herm_eq_dot, toLin'_apply, toLin'_apply, star_mulVec, mulVec_mulVec,
      ← dotProduct_mulVec, mulVec_mulVec, ← Matrix.mul_assoc, h1]
  · obtain ⟨N, B, -, hN, -⟩ := GlobalTheory.UnfoldingCompare.exists_frame_inv hc hx' h1 h2
    have e : y = C *ᵥ ((N *ᵥ y) ∘ Sum.inl) + (N *ᵥ y) (Sum.inr ()) • x := by
      conv_lhs => rw [← one_mulVec y, ← hN, ← mulVec_mulVec, fromCols_mulVec]
      congr 1
      funext i
      simp [mulVec, dotProduct, mul_comm]
    have ha : (N *ᵥ y) (Sum.inr ()) = 0 := by
      rw [herm_eq_dot, e, mulVec_add, mulVec_smul, dotProduct_add, hperp, zero_add,
        dotProduct_smul, smul_eq_mul] at hy
      exact (mul_eq_zero.1 hy).resolve_right hx'
    refine ⟨(N *ᵥ y) ∘ Sum.inl, ?_⟩
    rw [ha, zero_smul, add_zero] at e
    rw [toLin'_apply, ← e]
  · rintro ⟨v, rfl⟩
    rw [herm_eq_dot, toLin'_apply, hperp]
  · simp only [ActionCoordinates.act, toLin'_apply, mulVec_mulVec, (hι g).1]

end GlobalTheory.PerpFrameOfMatrix
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemSpanOfSemilinear
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem NumberField

namespace GlobalTheory.EX.OB

theorem mem_span_of_semilinear {B K O Kf V W ι : Type*} [CommRing B] [IsDomain B] [IsPrincipalIdealRing B] [Field K]
    [Algebra B K] [IsFractionRing B K] [CommRing O] [Field Kf] [Algebra O Kf]
    [AddCommGroup V] [Module K V] [Module B V] [IsScalarTower B K V]
    [AddCommGroup W] [Module Kf W] [Module O W] [IsScalarTower O Kf W]
    (σ : K →+* Kf) (hσ : ∀ k, σ k ∈ Set.range (algebraMap O Kf) ↔ k ∈ Set.range (algebraMap B K))
    (φ : V →+ W) (hφ : ∀ (a : K) x, φ (a • x) = σ a • φ x) (b : Module.Basis ι K V)
    (hb : LinearIndependent Kf (φ ∘ b)) (S : Set V) (x : V) (hx : φ x ∈ Submodule.span O (φ '' S)) :
    x ∈ Submodule.span B S := by
  classical
  obtain ⟨T, hTS, hxT⟩ := Submodule.mem_span_finite_of_mem_span hx
  obtain ⟨T', hT'S, rfl⟩ := Finset.subset_set_image_iff.1 hTS
  refine Submodule.span_mono hT'S ?_
  set N := Submodule.span B (T' : Set V) with hN
  have : Module.Finite B N := Module.Finite.span_of_finite B T'.finite_toSet
  have : Module.IsTorsionFree B V := Module.IsTorsionFree.trans_faithfulSMul B K V
  have : Module.Free B N := inferInstance
  let e0 := Module.Free.chooseBasis B N
  let e : Module.Free.ChooseBasisIndex B N → V := fun i => (e0 i : V)
  have heB : LinearIndependent B e := e0.linearIndependent.map' N.subtype N.ker_subtype
  have heK : LinearIndependent K e := (LinearIndependent.iff_fractionRing B K).1 heB
  have hspan : N ≤ Submodule.span B (Set.range e) := by
    intro y hy
    have h1 : (⟨y, hy⟩ : N) ∈ Submodule.span B (Set.range e0) := by rw [e0.span_eq]; trivial
    have h2 := Submodule.mem_map_of_mem (f := N.subtype) h1
    rw [Submodule.map_span, ← Set.range_comp] at h2
    exact h2
  have hxe : φ x ∈ Submodule.span O (Set.range (φ ∘ e)) := by
    refine (Submodule.span_le.2 ?_) hxT
    rw [Finset.coe_image]
    rintro _ ⟨y, hy, rfl⟩
    have hy' := hspan (Submodule.subset_span hy)
    rw [SetLike.mem_coe]
    clear hy
    induction hy' using Submodule.span_induction with
    | mem z hz => obtain ⟨i, rfl⟩ := hz; exact Submodule.subset_span ⟨i, rfl⟩
    | zero => simp
    | add z z' _ _ h h' => rw [map_add]; exact Submodule.add_mem _ h h'
    | smul a z _ h =>
      obtain ⟨o, ho⟩ := (hσ (algebraMap B K a)).2 ⟨a, rfl⟩
      rw [← algebraMap_smul K a z, hφ, ← ho, algebraMap_smul]
      exact Submodule.smul_mem _ _ h
  have hxK : x ∈ Submodule.span K (Set.range e) := by
    by_contra hn
    have h1 : LinearIndependent K (fun o => Option.casesOn' o x e) := heK.option hn
    have h2 := FBC.li_of_basis_li σ φ hφ b hb _ h1
    have h3 : (φ ∘ fun o => Option.casesOn' o x e) = fun o => Option.casesOn' o (φ x) (φ ∘ e) := by
      ext o; cases o <;> rfl
    rw [h3, linearIndependent_option'] at h2
    exact h2.2 (Submodule.span_subset_span O Kf _ hxe)
  obtain ⟨k, hk⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hxK
  obtain ⟨o, ho⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 hxe
  have hli := FBC.li_of_basis_li σ φ hφ b hb _ heK
  have heq : ∀ i, σ (k i) = algebraMap O Kf (o i) := by
    apply Fintype.linearIndependent_iffₛ.1 hli
    simp only [algebraMap_smul, ho]
    rw [← hk, map_sum]
    simp [hφ]
  rw [← hk]
  refine Submodule.sum_mem _ fun i _ => ?_
  obtain ⟨a, ha⟩ := (hσ (k i)).1 ⟨o i, (heq i).symm⟩
  rw [← ha, algebraMap_smul]
  exact Submodule.smul_mem _ _ (e0 i).2

theorem NP_full (D : D7) (L : SizeData₂ D) (X : G.Inst D L) (Y : G.LatInst D) (K : G.Consts) (c : LatCmp D)
    (hv : c.VramDef Y) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    (∀ x, c.cmp u w hg (D.nuIn u x) ∈ G.NP X Y K u w hg → InLoc (D.plEq w) (DV.MramL D u) x) ∧
      ∃ n : ℕ, n ≠ 0 ∧ ∀ x ∈ DV.MramL D u, c.cmp u w hg (D.nuIn u (n • x)) ∈ G.NP X Y K u w hg := by
  constructor
  · intro x hx
    have hM : c.cmp u w hg (D.nuIn u x) ∈ (D.gat u w hg).M := by
      obtain ⟨⟨-, F, hF, hFe⟩, -⟩ := hx
      rw [← hFe]
      exact Submodule.smul_mem _ _ hF
    rw [← c.cmp_M u w hg] at hM
    have := D.intW_dvr w
    have := D.intW_frac w
    have h1 : D.nuIn u x ∈ Submodule.span (intW D.what₂.places w) (((D.fm u).lat 0).L : Set ((D.fm u).lat 0).V) := by
      refine mem_span_of_semilinear (c.embW u w hg) (fun k => ?_) (c.cmp u w hg) (c.cmp_smul u w hg)
        ((D.fm u).lat 0).b (c.cmp_li u w hg) _ _ hM
      rw [← c.embW_int u w hg k]
      exact ⟨fun h => ⟨⟨k, h⟩, rfl⟩, by rintro ⟨a, rfl⟩; exact a.2⟩
    obtain ⟨s, hs, hsx⟩ := (D.mem_locW_iff w ((D.fm u).lat 0).L (D.nuIn u x)).1 h1
    refine ⟨s, hs, ?_⟩
    show ((D.nuIn u).restrictScalars (𝓞 D.what₂.LL)) (s • x) ∈ ((D.fm u).lat 0).L
    rw [map_smul]
    exact hsx
  · set a : ℕ := ∑ t0 ∈ G.VV X K (G.aL L) (G.bL L) (D.what₂.places.resChar w),
      ⌈G.Sv X K (G.aL L) (G.bL L) (D.what₂.places.resChar w) t0⌉.toNat with ha
    set b : ℕ := ⌈G.tauP X K (G.aL L) (G.bL L) (D.what₂.places.resChar w)⌉.toNat with hb
    refine ⟨D.what₂.places.resChar w ^ (b + a), pow_ne_zero _ (D.what₂.places.resChar_prime w).ne_zero, fun x hx => ?_⟩
    have hF1 : c.cmp u w hg (D.nuIn u x) ∈ (D.gat u w hg).M := by
      rw [← c.cmp_M u w hg]
      exact Submodule.subset_span ⟨D.nuIn u x, hx, rfl⟩
    have hF2 : c.cmp u w hg (D.nuIn u x) ∈ Y.Vram u w hg := by
      rw [← SetLike.mem_coe, hv u w hg]
      refine Submodule.subset_span ⟨D.nuIn u x, ?_, rfl⟩
      rw [← D.nuIn_range u]
      exact ⟨x, rfl⟩
    rw [map_nsmul, map_nsmul, ← Nat.cast_smul_eq_nsmul (D.gat u w hg).O, Nat.cast_pow]
    generalize c.cmp u w hg (D.nuIn u x) = F at hF1 hF2
    unfold G.NP
    refine ⟨⟨?_, ?_⟩, Submodule.smul_mem _ _ hF2⟩
    · rw [pow_add, mul_smul]
      apply Submodule.smul_mem
      apply Submodule.subset_span
      refine ⟨∅, Finset.empty_subset _, F, hF1, ?_⟩
      simp [G.yProd, ha]
    · refine ⟨((D.what₂.places.resChar w : ℕ) : (D.gat u w hg).O) ^ a • F, Submodule.smul_mem _ _ hF1, ?_⟩
      rw [pow_add, mul_smul]
      rfl

end GlobalTheory.EX.OB
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NegDefiniteSelfDualStabilizerVolumeOne
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.NegDefStab

theorem jpq_zero_left (n : ℕ) : Formalism.UG.Jpq 0 n = -1 := by
  ext i j
  rcases i with i | i
  · exact i.elim0
  · rcases j with j | j
    · exact j.elim0
    · simp [Formalism.UG.Jpq, Matrix.one_apply]

theorem unitary_of_negative_definite {n m : ℕ} (e : Fin m ≃ Fin 0 ⊕ Fin n) (A : Matrix (Fin 0 ⊕ Fin n) (Fin m) ℂ)
    (Jt X : Matrix (Fin m) (Fin m) ℂ) (hJ : IsUnit Jt.det)
    (hA : A.conjTranspose * Formalism.UG.Jpq 0 n * A = Jt)
    (hX : X.conjTranspose * Jt * X = Jt) : ∃ b : Formalism.BasicNotions.UpqT 0 n, Formalism.BasicNotions.UpqT.mat b * A = A * X := by
  rw [jpq_zero_left, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul] at hA
  have hA' : A.conjTranspose * A = -Jt := by rw [← hA, neg_neg]
  have hJ' : IsUnit (-Jt).det := by
    rw [Matrix.det_neg]; exact ((isUnit_one.neg).pow _).mul hJ
  have hX' : X.conjTranspose * (-Jt) * X = -Jt := by
    rw [Matrix.mul_neg, Matrix.neg_mul, hX]
  let L : Matrix (Fin m) (Fin 0 ⊕ Fin n) ℂ := (-Jt)⁻¹ * A.conjTranspose
  have hLA : L * A = 1 := by
    simp only [L, Matrix.mul_assoc, hA']
    exact Matrix.nonsing_inv_mul _ hJ'
  have hAL : A * L = 1 := (Matrix.mul_eq_one_comm_of_equiv (A := A) (B := L) e.symm).mpr hLA
  let bm : Matrix (Fin 0 ⊕ Fin n) (Fin 0 ⊕ Fin n) ℂ := A * X * L
  have hbb : bm.conjTranspose * bm = 1 := by
    have : bm.conjTranspose * bm = L.conjTranspose * (X.conjTranspose * (A.conjTranspose * A) * X) * L := by
      simp only [bm, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [this, hA', hX', ← hA']
    rw [show L.conjTranspose * (A.conjTranspose * A) * L = (A * L).conjTranspose * (A * L) by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]]
    rw [hAL, Matrix.conjTranspose_one, Matrix.one_mul]
  have hbb' : bm * bm.conjTranspose = 1 :=
    (Matrix.mul_eq_one_comm_of_equiv (A := bm.conjTranspose) (B := bm) (Equiv.refl _)).mp hbb
  let g : GL (Fin 0 ⊕ Fin n) ℂ := ⟨bm, bm.conjTranspose, hbb', hbb⟩
  have hg : g ∈ Formalism.UG.Upq 0 n := by
    show Formalism.UG.cT (starRingEnd ℂ) bm * Formalism.UG.Jpq 0 n * bm = Formalism.UG.Jpq 0 n
    have e' : Formalism.UG.cT (starRingEnd ℂ) bm = bm.conjTranspose := by
      ext i j; simp [Formalism.UG.cT, Matrix.conjTranspose_apply]
    rw [e', jpq_zero_left, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, hbb]
  refine ⟨(⟨g, hg⟩ : Formalism.UG.Upq 0 n), ?_⟩
  show bm * A = A * X
  simp only [bm, Matrix.mul_assoc, hLA, Matrix.mul_one]

open Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.StabFin in

theorem measure_SFin_negDef : ∀ (D : D7) (W : HSpace D.host.E) (n : ℕ), W.SigOK → (∀ τ, W.sig τ = (0, n)) →
    ∀ μ : Measure (HA (AF D.host.F) D.sp.cm.sig W.gram), IsVolMeas D W 0 n μ →
    μ (StabFin.SFin D.sp.cm.sig W.gram (L0c D W) : Set (HA (AF D.host.F) D.sp.cm.sig W.gram)) = 1 := by
  intro D W n hW hsig μ hμ
  obtain ⟨θ, hθ⟩ := hμ.2.1
  obtain ⟨A, hA⟩ := (hμ.2.2 θ hθ).1
  have h := (hμ.2.2 θ hθ).2 A hA (fun _ => Set.univ) (fun _ => MeasurableSet.univ)
  have hp : D.cd.cd 0 n Set.univ = 1 := GlobalTheory.CompactDualSwap.cd_zero_univ D.cd n
  simp only [hp, Finset.prod_const_one] at h
  convert h using 2
  ext g
  constructor
  · intro hg
    refine ⟨hg, fun ρ => ?_⟩
    have h0 := hW (embOf D ρ)
    rw [hsig] at h0
    obtain ⟨e, P', hP⟩ := h0
    have hJ : IsUnit (W.gram.map (embOf D ρ)).det := by
      have hd := congrArg Matrix.det hP
      rw [jpq_zero_left, Matrix.det_mul, Matrix.det_mul, Matrix.det_reindex_self] at hd
      refine isUnit_iff_ne_zero.mpr fun h0 => ?_
      rw [h0, mul_zero, zero_mul, Matrix.det_neg, Matrix.det_one, mul_one] at hd
      exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero) hd.symm
    obtain ⟨b, hb⟩ := unitary_of_negative_definite e (A ρ) _ _ hJ (hA ρ)
      (infMat_unitary D.sp.cm.sig (fun _ => rfl) (fun x => (D.sp.cm.fixed _).mpr ⟨x, rfl⟩) (embOf D ρ)
        (D.sp.cm.cmUnram.2.1 _) (θ ρ) (hθ ρ) W.gram g)
    exact ⟨b, Set.mem_univ _, hb⟩
  · intro hg; exact hg.1

end GlobalTheory.NegDefStab
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PositiveDefiniteUnitSphereMassProofStatement
section
open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.positiveDefiniteUnitSphereMass_proof : GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.SphereMass := by
  first | exact @GlobalTheory.SphereMassProof.sphereMass | exact GlobalTheory.SphereMassProof.sphereMass | (intros; apply GlobalTheory.SphereMassProof.sphereMass <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ThinChoiceOfZeroDensity
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem thinChoice_of_explicit : GlobalTheory.Mem.An.ExplZeta → GlobalTheory.Mem.An.ExplChi → GlobalTheory.Mem.An.LogDerOne → GlobalTheory.Mem.An.ZeroCount →
    Formalism.ZeroFreeDirichlet.ZFRDirichlet → ThinChoice :=
  fun _ _ _ _ _ => thinChoice_host

end GlobalTheory.EX
end

