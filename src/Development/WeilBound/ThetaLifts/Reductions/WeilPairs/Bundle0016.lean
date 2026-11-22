import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1613
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1637
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle0002
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle0003
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.DiagonalLagrangianIntegralSiegelParabolicTransfoAlt
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle0013
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle0005
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle0015
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceThetaFunctionVacuumConjugatePlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1662

-- bundled from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.MfacInvMul
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace PositivityTheory.ThKW.NormModulusHeisenberg

open PositivityTheory.ThKW.ModulusFactorDefinition PositivityTheory.ThKW.ModulusDerivativeNormalisation

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem heisOF_zero (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E)
    (ξ₀ : E) (ψ : AddChar (AF F) ℂ) (f : WOF F E nS nT → ℂ) : heisOF σ JS JT ξ₀ ψ 0 f = f := by
  funext w
  simp [heisOF, symplOHF, symplOF, hOF]

theorem nrm_zero (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E)
    (ξ₀ : E) (ψ : AddChar (AF F) ℂ) (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT))
    (f : WOF F E nS (nT + nT) → ℂ) :
    nrm σ JS JT ξ₀ ψ ν 𝓕 f 0 = ((‖GlobalTheory.LagrTheta.lagrInt ν 𝓕 (dC (AF F ⊗[F] E) nT) f‖ ^ 2 : ℝ) : ℂ) := by
  unfold nrm
  rw [Matrix.mul_zero, heisOF_zero, Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem mfac_inv_mul {nT : ℕ} (nS : ℕ) (t : GL (Fin nT) (AF F ⊗[F] E)) :
    mfac F E nS t⁻¹ * mfac F E nS t = 1 := by
  unfold mfac
  rw [← Real.mul_rpow (NNReal.coe_nonneg _) (NNReal.coe_nonneg _), ← NNReal.coe_mul, ← map_mul, ← map_mul, ← map_mul,
    inv_mul_cancel, map_one, map_one, map_one, NNReal.coe_one, Real.one_rpow]

theorem mfac_pos' {nT : ℕ} (nS : ℕ) (t : GL (Fin nT) (AF F ⊗[F] E)) : 0 < mfac F E nS t := by
  unfold mfac
  refine Real.rpow_pos_of_pos (NNReal.coe_pos.2 (pos_iff_ne_zero.2 fun h0 => ?_)) _
  have := map_mul (adeleClass F).modu (Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F)
    (Matrix.GeneralLinearGroup.det t)) (Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F)
    (Matrix.GeneralLinearGroup.det t))⁻¹
  rw [mul_inv_cancel, map_one, h0, zero_mul] at this
  exact one_ne_zero this

end PositivityTheory.ThKW.NormModulusHeisenberg

end

open PositivityTheory.ThKW.ModulusFactorDefinition PositivityTheory.ThKW.ModulusDerivativeNormalisation PositivityTheory.ThKW.NormModulusHeisenberg in
theorem PositivityTheory.ThKW.PhaseFourierInjectivity.norm_law : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
      ∀ (χS : (AF F ⊗[F] E)ˣ →* Circle) (ωd : GAF σ JS × GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) →*
            Module.End ℂ (WOF F E nS (nT + nT) → ℂ)),
        IsWeilDatumOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)
            (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS 1 ωd →
      ∀ (h : GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)) (t : GL (Fin nT) (AF F ⊗[F] E)),
        mtF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) h * dC (AF F ⊗[F] E) nT = dC (AF F ⊗[F] E) nT * t.1 →
      ∀ f, IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ f →
        ‖GlobalTheory.LagrTheta.lagrInt ν 𝓕 (dC (AF F ⊗[F] E) nT) (ωd (1, h) f)‖ =
          mfac F E nS t * ‖GlobalTheory.LagrTheta.lagrInt ν 𝓕 (dC (AF F ⊗[F] E) nT) f‖ := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ ν 𝓕 hν h𝓕 χS ωd hωd h t hht f hf
  obtain ⟨μW, 𝓕W, κ, hμW, h𝓕W, hκ, hcoef⟩ := PositivityTheory.ThKW.PhaseFourierInjectivity.coef F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ ν 𝓕 hν h𝓕
  have hωf := hωd.om_pres (1, h) f hf
  obtain ⟨c1, i1, e1⟩ := hcoef _ hωf
  obtain ⟨c0, i0, e0⟩ := hcoef f hf
  obtain ⟨cL, iL, eL⟩ := PositivityTheory.ThKW.PhaseFourierInjectivity.change F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ ν 𝓕 hν h𝓕 t _ c0 i0
  have hκ0 : (κ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hκ.ne'
  have key : nrm σ JS JT ξ₀ B.ψ ν 𝓕 (ωd (1, h) f) = fun w =>
      ((mfac F E nS t : ℝ) : ℂ) ^ 2 * nrm σ JS JT ξ₀ B.ψ ν 𝓕 f ((t.1.map (cAF σ))ᵀ * w) := by
    refine PositivityTheory.ThKW.PhaseFourierInjectivity.finj F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ ν 𝓕 hν h𝓕 _ _ c1 (continuous_const.mul cL) i1
      (iL.const_mul _) fun y => ?_
    have hact : actOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) 1 h (dC (AF F ⊗[F] E) nT * ((t⁻¹).1 * y)) = dC (AF F ⊗[F] E) nT * y := by
      unfold actOF
      rw [inv_one, show mtF σ JS 1 = 1 by unfold mtF; rw [map_one, Units.val_one], Matrix.mul_one,
        ← Matrix.mul_assoc, hht, Matrix.mul_assoc, ← Matrix.mul_assoc t.1, ← Units.val_mul, mul_inv_cancel,
        Units.val_one, Matrix.one_mul]
    have u := PositivityTheory.ThKW.PhaseFourierInjectivity.unit_coef F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ χS ωd hωd μW 𝓕W hμW h𝓕W h
      (dC (AF F ⊗[F] E) nT * ((t⁻¹).1 * y)) f hf
    rw [hact, e1 y, e0 ((t⁻¹).1 * y), eL y] at u
    have u' := mul_left_cancel₀ hκ0 u
    rw [u', ← integral_const_mul]
    congr 1
    funext w
    ring
  have k0 := congrFun key 0
  rw [Matrix.mul_zero, nrm_zero, nrm_zero] at k0
  have k1 : ‖GlobalTheory.LagrTheta.lagrInt ν 𝓕 (dC (AF F ⊗[F] E) nT) (ωd (1, h) f)‖ ^ 2 =
      (mfac F E nS t * ‖GlobalTheory.LagrTheta.lagrInt ν 𝓕 (dC (AF F ⊗[F] E) nT) f‖) ^ 2 := by
    rw [mul_pow]
    exact_mod_cast k0
  exact (pow_left_inj₀ (norm_nonneg _) (mul_nonneg (mfac_pos' nS t).le (norm_nonneg _)) two_ne_zero).1 k1
end

-- bundled from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.SmulMemConjHalf
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace GlobalTheory.SplitLagrF

open GlobalTheory.SplitInvFormF GlobalTheory.WeilSchrodinger.DblTargetF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {ξ₀ : E}
  {ψ : AddChar (AF F) ℂ}

theorem dC_mul_eq' (a : WOF F E nS nT) :
    dC F E nT * a = Matrix.of fun i j => Sum.elim (fun p => a p j) (fun p => a p j) (finSumFinEquiv.symm i) := by
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  rcases i with p | p
  · rw [Matrix.of_apply, Equiv.symm_apply_apply]; exact GlobalTheory.LagrThetaInv.dC_mul_inl a p j
  · rw [Matrix.of_apply, Equiv.symm_apply_apply]; exact GlobalTheory.LagrThetaInv.dC_mul_inr a p j

theorem aC_mul_eq (a : WOF F E nS nT) :
    aC F E nT * a = Matrix.of fun i j => Sum.elim (fun p => a p j) (fun p => -a p j) (finSumFinEquiv.symm i) := by
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  rcases i with p | p <;>
    simp only [aC, Matrix.mul_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, id, Matrix.of_apply] <;>
    simp [Matrix.one_apply]

theorem hOF_dC_aC (a y : WOF F E nS nT) :
    hOF σ JS (dblG JT) (dC F E nT * a) (aC F E nT * y) = hOF σ JS JT (a + a) y := by
  rw [dC_mul_eq', aC_mul_eq]
  unfold hOF
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  simp only [← finSumFinEquiv.sum_comp, Matrix.of_apply, Equiv.symm_apply_apply, GlobalTheory.LagrThetaInv.dblG_apply]
  simp only [Fintype.sum_sum_type]
  simp [dbl, Finset.sum_add_distrib, mul_add]

theorem hOF_aC_dC (a y : WOF F E nS nT) :
    hOF σ JS (dblG JT) (aC F E nT * y) (dC F E nT * a) = hOF σ JS JT y (a + a) := by
  rw [dC_mul_eq', aC_mul_eq]
  unfold hOF
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  simp only [← finSumFinEquiv.sum_comp, Matrix.of_apply, Equiv.symm_apply_apply, GlobalTheory.LagrThetaInv.dblG_apply]
  simp only [Fintype.sum_sum_type]
  simp [dbl, Finset.sum_add_distrib, mul_add, add_mul]

theorem commF_aC_dC (a y : WOF F E nS nT) :
    commF σ JS (dblG JT) ξ₀ ψ (aC F E nT * y) (dC F E nT * a) = commF σ JS JT ξ₀ ψ y (a + a) := by
  simp only [commF, symplOHF, symplOF, hOF_dC_aC, hOF_aC_dC]

theorem mul_mem_conjHalf {m : ℕ} {e : AEF F E} (M : Matrix (Fin m) (Fin nT) (AEF F E)) {y : WOF F E nS nT}
    (hy : y ∈ conjHalf σ e nS nT) : (M * y : WOF F E nS m) ∈ conjHalf σ e nS m := fun i j => by
  rw [Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [mul_left_comm, hy k j]

variable (F E) in

def hlf : AEF F E := incAF F E (1 / 2)

theorem hlf_add : hlf F E + hlf F E = 1 := by
  unfold hlf
  rw [← map_add, show (1 / 2 : E) + 1 / 2 = 1 by norm_num, map_one]

theorem exists_decomp {e : AEF F E} {u : WOF F E nS (nT + nT)} (hu : u ∈ conjHalf σ e nS (nT + nT)) :
    ∃ a ∈ conjHalf σ e nS nT, ∃ b ∈ conjHalf σ e nS nT, u = dC F E nT * a + aC F E nT * b := by
  refine ⟨Matrix.of fun p j => hlf F E * (u (finSumFinEquiv (Sum.inl p)) j + u (finSumFinEquiv (Sum.inr p)) j),
    fun p j => ?_,
    Matrix.of fun p j => hlf F E * (u (finSumFinEquiv (Sum.inl p)) j - u (finSumFinEquiv (Sum.inr p)) j),
    fun p j => ?_, ?_⟩
  · rw [Matrix.of_apply, mul_left_comm, mul_add, hu, hu]
  · rw [Matrix.of_apply, mul_left_comm, mul_sub, hu, hu]
  · rw [dC_mul_eq', aC_mul_eq]
    ext i j
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    rcases i with p | p <;>
      simp only [Matrix.add_apply, Matrix.of_apply, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr]
    · linear_combination (-u (finSumFinEquiv (Sum.inl p)) j) * (hlf_add (F := F) (E := E))
    · linear_combination (-u (finSumFinEquiv (Sum.inr p)) j) * (hlf_add (F := F) (E := E))

theorem neg_hlf_add (g : WOF F E nS nT) : (-hlf F E) • g + (-hlf F E) • g = -g := by
  rw [← add_smul, ← neg_add, hlf_add, neg_one_smul]

theorem smul_mem_conjHalf {e : AEF F E} (c : AEF F E) {y : WOF F E nS nT}
    (hy : y ∈ conjHalf σ e nS nT) : c • y ∈ conjHalf σ e nS nT := fun i j => by
  rw [Matrix.smul_apply, smul_eq_mul, mul_left_comm, hy i j]

theorem lagrInt_smul {m : ℕ} (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT))
    (C : Matrix (Fin m) (Fin nT) (AF F ⊗[F] E)) (c : ℂ) (f : WOF F E nS m → ℂ) :
    GlobalTheory.LagrTheta.lagrInt ν 𝓕 C (c • f) = c * GlobalTheory.LagrTheta.lagrInt ν 𝓕 C f := by
  simp only [GlobalTheory.LagrTheta.lagrInt, Pi.smul_apply, smul_eq_mul, integral_const_mul]

theorem prof_smul (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)) (c : ℂ) (f : WOF F E nS (nT + nT) → ℂ)
    (y : WOF F E nS nT) : prof σ JS JT ξ₀ ψ ν 𝓕 (c • f) y = c * prof σ JS JT ξ₀ ψ ν 𝓕 f y := by
  unfold prof
  rw [GlobalTheory.WeilPartsF.heisOF_smul, lagrInt_smul]

theorem prof_zero (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)) (f : WOF F E nS (nT + nT) → ℂ) :
    prof σ JS JT ξ₀ ψ ν 𝓕 f 0 = GlobalTheory.LagrTheta.lagrInt ν 𝓕 (dC F E nT) f := by
  unfold prof
  rw [Matrix.mul_zero, heisOF_zero]

theorem prof_heis_aC (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)) {e : AEF F E} (he : IsSplitIdemF σ e)
    (f : WOF F E nS (nT + nT) → ℂ) {y b : WOF F E nS nT} (hy : y ∈ conjHalf σ e nS nT) (hb : b ∈ conjHalf σ e nS nT) :
    prof σ JS JT ξ₀ ψ ν 𝓕 (heisOF σ JS (dblG JT) ξ₀ ψ (aC F E nT * b) f) y = prof σ JS JT ξ₀ ψ ν 𝓕 f (y + b) := by
  unfold prof
  rw [Matrix.mul_add, GlobalTheory.SplitVacF.heisOF_add_half he (mul_mem_conjHalf _ hy) (mul_mem_conjHalf _ hb)]

theorem integrableOn_dC {ν : Measure (WOF F E nS nT)} {𝓕 : Set (WOF F E nS nT)} (hν : ν.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν) {f : WOF F E nS (nT + nT) → ℂ}
    (hf : IsThetaFunOF σ JS (dblG JT) ξ₀ ψ f) : IntegrableOn (fun u : WOF F E nS nT => f (dC F E nT * u)) 𝓕 ν := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLatticeF.lattice F E nS nT
  haveI : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  haveI : Countable (ratLF F E nS nT) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)
  have hfin := GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact (G := WOF F E nS nT) (ratLF F E nS nT) hK hKc ν h𝓕
  haveI : IsFiniteMeasure (ν.restrict 𝓕) := ⟨by rwa [Measure.restrict_apply_univ]⟩
  have hI : Continuous fun u : WOF F E nS nT => f (dC F E nT * u) :=
    hf.cont.comp (continuous_const.matrix_mul continuous_id)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hI.continuousOn
  refine Integrable.of_bound hI.aestronglyMeasurable C (Filter.Eventually.of_forall fun w => ?_)
  obtain ⟨_, ⟨γ, rfl⟩, h⟩ := hKc w
  have h1 := hC _ h
  have hr : ((incAF F E).toAddMonoidHom.mapMatrix γ : WOF F E nS nT) = ratWF γ := rfl
  have h2 := hf.quasi (GlobalTheory.LagrThetaInv.dC E nT * γ) (dC F E nT * w)
  rw [← dC_mul_ratWF, symplOHF_dC, neg_zero, AddChar.map_zero_eq_one, one_mul] at h2
  simp only [hr, Matrix.mul_add] at h1
  rwa [h2] at h1

variable {B : Base F E}

theorem prof_add (hB : B.IsGood σ) {ν : Measure (WOF F E nS nT)} {𝓕 : Set (WOF F E nS nT)} (hν : ν.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν) {f g : WOF F E nS (nT + nT) → ℂ}
    (hf : IsThetaFunOF σ JS (dblG JT) ξ₀ B.ψ f) (hg : IsThetaFunOF σ JS (dblG JT) ξ₀ B.ψ g) (y : WOF F E nS nT) :
    prof σ JS JT ξ₀ B.ψ ν 𝓕 (f + g) y = prof σ JS JT ξ₀ B.ψ ν 𝓕 f y + prof σ JS JT ξ₀ B.ψ ν 𝓕 g y := by
  unfold prof
  rw [GlobalTheory.WeilPartsF.heisOF_add]
  exact integral_add
    (integrableOn_dC hν h𝓕 (GlobalTheory.HeisThetaF.isThetaFunOF_heisOF F E σ B hB _ _ JS _ ξ₀ (aC F E nT * y) f hf))
    (integrableOn_dC hν h𝓕 (GlobalTheory.HeisThetaF.isThetaFunOF_heisOF F E σ B hB _ _ JS _ ξ₀ (aC F E nT * y) g hg))

theorem prof_heis_dC (hB : B.IsGood σ) (hS : IsHermND σ JS) (hT : IsHermND σ JT) (hξ : ξ₀ ≠ 0) (hσξ : σ ξ₀ = -ξ₀)
    {ν : Measure (WOF F E nS nT)} {𝓕 : Set (WOF F E nS nT)} (hν : ν.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν) {f : WOF F E nS (nT + nT) → ℂ}
    (hf : IsThetaFunOF σ JS (dblG JT) ξ₀ B.ψ f) (a y : WOF F E nS nT) :
    prof σ JS JT ξ₀ B.ψ ν 𝓕 (heisOF σ JS (dblG JT) ξ₀ B.ψ (dC F E nT * a) f) y =
      commF σ JS JT ξ₀ B.ψ y (a + a) * prof σ JS JT ξ₀ B.ψ ν 𝓕 f y := by
  unfold prof
  rw [heisOF_comm, lagrInt_smul, commF_aC_dC, lagrInt_heis_dC F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ ν 𝓕 hν h𝓕 _
    (GlobalTheory.HeisThetaF.isThetaFunOF_heisOF F E σ B hB _ _ JS _ ξ₀ (aC F E nT * y) f hf)]

theorem prof_heis_lift (hB : B.IsGood σ) (hS : IsHermND σ JS) (hT : IsHermND σ JT) (hξ : ξ₀ ≠ 0) (hσξ : σ ξ₀ = -ξ₀)
    {ν : Measure (WOF F E nS nT)} {𝓕 : Set (WOF F E nS nT)} (hν : ν.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν) {f : WOF F E nS (nT + nT) → ℂ}
    (hf : IsThetaFunOF σ JS (dblG JT) ξ₀ B.ψ f) (g y : WOF F E nS nT) :
    prof σ JS JT ξ₀ B.ψ ν 𝓕 (heisOF σ JS (dblG JT) ξ₀ B.ψ (dC F E nT * ((-hlf F E) • g : WOF F E nS nT)) f) y =
      commF σ JS JT ξ₀ B.ψ g y * prof σ JS JT ξ₀ B.ψ ν 𝓕 f y := by
  rw [prof_heis_dC hB hS hT hξ hσξ hν h𝓕 hf, neg_hlf_add, GlobalTheory.SplitVacF.commF_swap]

end GlobalTheory.SplitLagrF

end
end

