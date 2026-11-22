import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodInst
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0266
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SquareIntegrableIffExtension
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0262
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0255
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0249
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0264
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0263
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0275
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0276
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0271
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0267
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.T2SpaceHalfAdelicMatrixAddSubgroup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0269
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientHeightLowerBoundShortIsotropicVector
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentApproximation.AddDense
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0268
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsFundU
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0273

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInstanceFramesOfDiagonalFrameSelfDual
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem frames_of_diagonalising_frame : ∀ (D : D7) (V : HSp D) (A : Fr V) (Λ : Lat V), IsSelfDualC V Λ → ∃ fr : Formalism.IndefR.Eqv.UI.Frames D V, fr.Λ = Λ ∧ ∀ τ, fr.ε (Formalism.L2.Host.tauPl D τ) = A.ε τ ∧ fr.P (Formalism.L2.Host.tauPl D τ) = (A.fr τ)⁻¹ := by
  intro D V A Λ h
  obtain ⟨hlat, hdual⟩ := h
  have hf : ∀ v, IsUnit (A.fr ((Formalism.L2.Host.tauPl D).symm v)) := fun v => A.fr_unit _
  refine ⟨{ ε := fun v => A.ε ((Formalism.L2.Host.tauPl D).symm v)
            P := fun v => (A.fr ((Formalism.L2.Host.tauPl D).symm v))⁻¹
            unit := fun v => (Matrix.isUnit_nonsing_inv_iff).2 (hf v)
            spec := ?_
            Λ := Λ
            Λ_fg := hlat.fg
            Λ_span := hlat.span_eq_top
            Λ_dual := ?_ }, rfl, fun τ => ?_⟩
  · intro v
    set τ := (Formalism.L2.Host.tauPl D).symm v
    have hg : V.gram.map (Formalism.IndefR.Eqv.UI.phiV D v) = (A.fr τ)ᴴ * Formalism.REAL.Jm (A.ε τ) * A.fr τ := by
      rw [A.fr_gram τ]; rfl
    have hd : IsUnit (A.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (hf v)
    have hdH : IsUnit ((A.fr τ)ᴴ).det := by
      rw [Matrix.det_conjTranspose]; exact hd.star
    rw [hg, Matrix.conjTranspose_nonsing_inv]
    calc ((A.fr τ)ᴴ)⁻¹ * ((A.fr τ)ᴴ * Formalism.REAL.Jm (A.ε τ) * A.fr τ) * (A.fr τ)⁻¹
        = (((A.fr τ)ᴴ)⁻¹ * (A.fr τ)ᴴ) * Formalism.REAL.Jm (A.ε τ) * (A.fr τ * (A.fr τ)⁻¹) := by
          simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm (A.ε τ) := by
          rw [Matrix.nonsing_inv_mul _ hdH, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul, Matrix.mul_one]
  · intro x
    rw [hdual x]
    refine forall₂_congr fun y _ => ?_
    unfold Formalism.UG.hform
    simp only [RingHom.mem_range, starRingEnd_apply]
  · simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntegralMatricesSeparatingRationalPairing
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RatPairSep

variable {D : D7}

theorem eq_zero_of_trace_integralBasis (D : D7) (q : D.host.E)
    (h : ∀ k, Algebra.trace ℚ D.host.E (q * integralBasis D.host.E k) = 0) : q = 0 := by
  refine (traceForm_nondegenerate ℚ D.host.E).1 q fun z => ?_
  have hl : (Algebra.traceForm ℚ D.host.E) q = 0 :=
    (integralBasis D.host.E).ext fun k => by
      rw [LinearMap.zero_apply, Algebra.traceForm_apply]; exact h k
  rw [hl, LinearMap.zero_apply]

theorem pairQ_sub (W : HSp D) {r : ℕ} (y y' : Matrix (Fin W.rank) (Fin r) D.host.E) :
    pairQ W y - pairQ W y' = pairQ W (y - y') := by
  have : adj D (y - y') = adj D y - adj D y' := by
    ext i j; simp [adj, Formalism.UG.cT]
  simp only [pairQ, this, Matrix.sub_mul, smul_sub]

theorem eq_of_pairQ_eq (W : HSp D) {r : ℕ} (y y' : Matrix (Fin W.rank) (Fin r) D.host.E)
    (h : pairQ W y = pairQ W y') : y = y' := by
  have h1 : adj D y * W.gram = adj D y' * W.gram := by
    have := congrArg (fun M => (D.host.xi0)⁻¹ • M) h
    simpa [pairQ, smul_smul, inv_mul_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)] using this
  have h2 : adj D y = adj D y' := by
    have := congrArg (fun M => M * W.gram⁻¹) h1
    simpa [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (GlobalTheory.LatVac.gram_det_isUnit W)] using this
  refine Matrix.ext fun i j => ?_
  have := congrFun (congrFun h2 j) i
  simp only [adj, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply] at this
  exact (D.sp.cm.sig : D.host.E →+* D.host.E).injective this

theorem exists_sep (D : D7) (W : HSp D) (r : ℕ) :
    ∃ (n : ℕ) (X : Fin n → Matrix (Fin W.rank) (Fin r) D.host.E), (∀ j a b, IsIntegral ℤ (X j a b)) ∧
      ∀ y y' : Matrix (Fin W.rank) (Fin r) D.host.E, (∀ j, ratPair W y (X j) = ratPair W y' (X j)) → y = y' := by
  let ι := Fin W.rank × Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 D.host.E)
  let e := Fintype.equivFin ι
  let Y : ι → Matrix (Fin W.rank) (Fin r) D.host.E := fun t => Matrix.single t.1 t.2.1 (integralBasis D.host.E t.2.2)
  refine ⟨Fintype.card ι, fun j => Y (e.symm j), ?_, ?_⟩
  · intro j a b
    simp only [Y, Matrix.single_apply]
    split_ifs
    · rw [integralBasis_apply]; exact (RingOfIntegers.basis D.host.E _).isIntegral_coe
    · exact isIntegral_zero
  · intro y y' h
    apply eq_of_pairQ_eq W y y'
    rw [← sub_eq_zero, pairQ_sub]
    refine Matrix.ext fun l i => ?_
    rw [Matrix.zero_apply]
    refine eq_zero_of_trace_integralBasis D _ fun k => ?_
    have hj := h (e (i, l, k))
    simp only [ratPair, Equiv.symm_apply_apply, Y, Rat.cast_inj] at hj
    rw [← sub_eq_zero, ← map_sub, ← Matrix.trace_sub, ← Matrix.sub_mul, pairQ_sub,
      Matrix.trace_mul_single] at hj
    simpa [MulOpposite.smul_eq_mul_unop] using hj

end GlobalTheory.RatPairSep

theorem GlobalTheory.RatPairSep.main : ∀ (D : D7) (W : HSp D) (r : ℕ), ∃ (n : ℕ) (X : Fin n → Matrix (Fin W.rank) (Fin r) D.host.E),
    (∀ j a b, IsIntegral ℤ (X j a b)) ∧ ∀ y y' : Matrix (Fin W.rank) (Fin r) D.host.E,
    (∀ j, ratPair W y (X j) = ratPair W y' (X j)) → y = y' := GlobalTheory.RatPairSep.exists_sep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsCharFnExt
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.OpTrace GlobalTheory.HCChar GlobalTheory.SUChar
open GlobalTheory.Orb (ujMat ujRep CcMat IsCharFn IsRegSS)
open GlobalTheory.DSSU (SUJ SUset Ext)
open GlobalTheory.SqIntSU (scalarMul circleHaar)

noncomputable section

namespace GlobalTheory.ExtChar

theorem exists_isCharFn_ext : ∀ (n : ℕ), 1 ≤ n → ∀ (ε : Fin n → Bool) (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (μ' : Measure (SUJ ε)) [μ'.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (m : ℤ) (π' π : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)) (h' : IsURepOn (SUset ε) π') (h : IsURepOn (UJset ε) π), Ext ε m π' π → ∀ Θ' : SUJ ε → ℂ, IsCharFn (suMat ε) μ' (suRep h') Θ' → ∃ Θ : UJ ε → ℂ, IsCharFn (ujMat ε) μ (ujRep h) Θ ∧ ∀ (z : Circle) (g : SUJ ε), IsRegSS (suMat ε g) → Θ (scalarMul ε (z, g)) = (z : ℂ) ^ m * Θ' g := by
  intro n hn ε μ _ μ' _ V _ _ _ m π' π h' h hE Θ' hΘ'
  haveI : NeZero n := ⟨by omega⟩
  letI := GlobalTheory.SqIntSU.circleBorelMS
  obtain ⟨c, hc0, hμ, hop⟩ := GlobalTheory.ScalarTwist.scalar_twist n hn ε μ μ'
  have hmeas := GlobalTheory.ExtChar.aestronglyMeasurable_extChar n ε μ' m Θ' hΘ'.1.aestronglyMeasurable
  have hli := GlobalTheory.ExtChar.locallyIntegrable_extChar n ε μ' m Θ' hΘ'.1 hmeas
  refine ⟨GlobalTheory.ExtChar.extChar ε m Θ', ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [hμ]
    intro x
    obtain ⟨s, hs, hi⟩ := hli x
    exact ⟨s, hs, by rw [IntegrableOn, Measure.restrict_smul]; exact hi.smul_measure ENNReal.coe_ne_top⟩
  · exact GlobalTheory.ExtCharCont.continuousAt_extChar n ε m Θ' hΘ'.2.1
  · intro f hf
    have hfc : Continuous f := GlobalTheory.Orb.continuous_of_mem_ccSmooth (isInducing_matCoord (ε := ε)).continuous hf
    rw [hop V m π' π h' h hE f hfc hf.1]
    have ht := hΘ'.2.2 _ (GlobalTheory.CentreAvg.avg_mem_ccMat n ε m f hf)
    refine ⟨ht.1.smul _, ?_⟩
    rw [OpTrace.trace_smul, ht.2, hμ, integral_smul_nnreal_measure, GlobalTheory.ExtCharInt.integral_extChar n ε μ' m Θ' hΘ'.1 hli f hfc hf.1,
      NNReal.smul_def, Complex.real_smul]
  · intro z g hg
    rw [GlobalTheory.ExtChar.extChar_scalarMul, GlobalTheory.ExtChar.avgChar_eq_of_ext n ε μ' V m π' π h' hE Θ' hΘ' g hg]

end GlobalTheory.ExtChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsKActOfStable
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix MeasureTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin KVec KMap maxCpt rep_mem_kFin)
open scoped TensorProduct InnerProductSpace Classical
open GlobalTheory.Chain.IoLift

namespace GlobalTheory.Chain.IoLift

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_isKAct_of_stable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    (hs : ∀ x ∈ kFin M τ, x ∈ GlobalTheory.SmVec.smSub (gramAt D V τ) (M.rep τ))
    (hd : ∀ X ∈ lieAt V τ, ∀ x ∈ kFin M τ, dRep (M.rep τ) X x ∈ kFin M τ) :
    ∃ a : Matrix (Fin V.rank) (Fin V.rank) ℂ → Module.End ℂ (kFin M τ), IsKAct M τ a := by
  have hU : IsUnit (M.fr τ) := M.fr_unit τ
  have hG : IsUnit (gramAt D V τ) := GlobalTheory.SmVec.gram_unit hU (M.fr_gram τ)
  have hπ := GlobalTheory.SmVec.isURepOn_trRep hU (M.fr_gram τ) (M.ds τ).2.2.1
  refine ⟨fun X => if hX : X ∈ lieAt V τ then
    { toFun := fun v => ⟨dRep (M.rep τ) X v, hd X hX v v.2⟩
      map_add' := fun v w => Subtype.ext (GlobalTheory.SmVec.dRep_add (hs v v.2) (hs w w.2) hX)
      map_smul' := fun c v => Subtype.ext (GlobalTheory.SmVec.dRep_smul c (hs v v.2) hX) } else 0, ⟨?_, ?_⟩⟩
  · intro X hX v
    rw [dif_pos hX]
    exact GlobalTheory.SmVec.hasDerivAt_dRep (hs v v.2) hX
  · intro X hX v w
    rw [dif_pos hX, Submodule.coe_inner, Submodule.coe_inner]
    have key : ⟪(v : M.H τ), dRep (M.rep τ) X w⟫_ℂ = -⟪dRep (M.rep τ) X v, (w : M.H τ)⟫_ℂ :=
      GlobalTheory.SmVec.inner_dRep hG hπ (hs v v.2) (hs w w.2) hX
    change ⟪dRep (M.rep τ) X v, (w : M.H τ)⟫_ℂ + ⟪(v : M.H τ), dRep (M.rep τ) X w⟫_ℂ = 0
    linear_combination key

theorem kFin_smooth_isKAct : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau) (p q : ℕ) (T : GrpData p q) (R : DSRep T) (φ : Mat p q → Matrix (Fin V.rank) (Fin V.rank) ℂ) (m : ℤ) (U : M.H τ → R.U.H), GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.Matches R M τ φ m U → kFin M τ ≤ M.sm τ ∧ ∃ a : Matrix (Fin V.rank) (Fin V.rank) ℂ → Module.End ℂ (kFin M τ), IsKAct M τ a := by
  intro D V S M τ p q T R φ m U hM
  have hk : ∀ y : M.H τ, y ∈ kFin M τ ↔ U y ∈ Set.range R.ι := fun y => hM.kfin y
  have hsm : ∀ y ∈ kFin M τ, y ∈ GlobalTheory.SmVec.smSub (gramAt D V τ) (M.rep τ) := fun y hy =>
    GlobalTheory.SmVec.mem_smSub.2 (hM.smooth y ((hk y).1 hy))
  refine ⟨fun y hy => Submodule.subset_span (hM.smooth y ((hk y).1 hy)), exists_isKAct_of_stable M τ hsm ?_⟩
  intro X hX y hy
  rw [← hM.lie] at hX
  obtain ⟨Z, hZ, rfl⟩ := hX
  obtain ⟨v, hv⟩ := (hk y).1 hy
  exact (hk _).2 ⟨_, (hM.der Z hZ v y hv.symm).symm⟩

end GlobalTheory.Chain.IoLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsotropicDualFrameOfSplitEmbeddingStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isotropicDualFrame_of_splitEmbedding : ∀ (D : D7) (V V' : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∃ C' : Matrix (Fin V.rank) (Fin r) D.host.E, adj D C * V.gram * C' = 1 ∧ adj D C' * V.gram * C' = 0 ∧ adj D C' * V.gram * B = 0 := by
  first | exact @GlobalTheory.TwistDual.exists_isotropic_dual | exact GlobalTheory.TwistDual.exists_isotropic_dual | (intros; apply GlobalTheory.TwistDual.exists_isotropic_dual <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLeftInverseIsotropicFrameKillingEmbedding
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.HalfAverage
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfAverage

theorem exists_leftInv_frame_kill_emb : ∀ (D : D7) (V V' : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∃ K : Matrix (Fin r) (Fin V.rank) D.host.E, K * C = 1 ∧ K * B = 0 := by
  intro D V V' r C B hs
  have hadj : ∀ {m n : ℕ} (X : Matrix (Fin m) (Fin n) D.host.E), adj D X = Xᴴ := fun X => rfl
  have hG : V.gramᴴ = V.gram := by
    ext i j; simp [Matrix.conjTranspose_apply, GlobalTheory.LatVac.gram_star]
  have hBC : adj D B * V.gram * C = 0 := by
    have h := congrArg Matrix.conjTranspose hs.orth
    rw [hadj] at h ⊢
    simpa [Matrix.conjTranspose_mul, hG, Matrix.mul_assoc] using h
  let f := C.mulVecLin.coprod B.mulVecLin
  have hf : ∀ c b, f (c, b) = C *ᵥ c + B *ᵥ b := fun c b => rfl
  have hker : LinearMap.ker f = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun ⟨c, b⟩ h => ?_
    rw [hf] at h
    have h1 := congrArg ((adj D B * V.gram).mulVec) h
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hBC, hs.isom, Matrix.zero_mulVec,
      zero_add, Matrix.mulVec_zero] at h1
    have hb : b = 0 := Matrix.mulVec_injective_iff_isUnit.2
      ((Matrix.isUnit_iff_isUnit_det _).2 (GlobalTheory.LatVac.gram_det_isUnit V')) (by rw [h1, Matrix.mulVec_zero])
    subst hb
    rw [Matrix.mulVec_zero, add_zero] at h
    have hc : c = 0 := Matrix.mulVec_injective_iff.2 hs.frame.2.1 (by rw [h, Matrix.mulVec_zero])
    subst hc
    rfl
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective f hker
  have key : ∀ c b, g (C *ᵥ c + B *ᵥ b) = (c, b) := fun c b => by
    rw [← hf]; exact LinearMap.congr_fun hg (c, b)
  have k1 : ∀ c, g (C *ᵥ c) = (c, 0) := fun c => by simpa using key c 0
  have k2 : ∀ b, g (B *ᵥ b) = (0, b) := fun b => by simpa using key 0 b
  refine ⟨LinearMap.toMatrix' (LinearMap.fst _ _ _ ∘ₗ g), ?_, ?_⟩
  · apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    simp [Matrix.toLin'_mul, Matrix.toLin'_apply, k1]
  · apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    simp [Matrix.toLin'_mul, Matrix.toLin'_apply, k2]

end GlobalTheory.HalfAverage

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLowerWittTowerIsotropicSplitEmbeddingStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lowerWittTower_isotropicSplitEmbedding : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (_M : DSModel V S) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E), IsIsoFrame V C → ∃ (V' : HSp D) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B ∧ GlobalTheory.IndefiniteRowSideFullHecke.LoweredSignatureVanishing.SigLowered S r V' := by
  first | exact @GlobalTheory.TowerSplit.exists_isoSplit | exact GlobalTheory.TowerSplit.exists_isoSplit | (intros; apply GlobalTheory.TowerSplit.exists_isoSplit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNatMulIntegralMatricesSubsetOpenAddSubgrou
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OpenSubAdele

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]

theorem exists_small_of_mem_nhds {t : Set (FiniteAdeleRing R K)}
    (ht : t ∈ nhds (0 : FiniteAdeleRing R K)) :
    ∃ r : R, r ≠ 0 ∧ ∀ y : FiniteAdeleRing R K,
      (∀ v : HeightOneSpectrum R, Valued.v (y v) ≤ v.intValuation r) → y ∈ t := by
  classical
  have hAopen : ∀ v : HeightOneSpectrum R,
      IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
    fun v => Valued.isOpen_valuationSubring _
  let z0 : ∀ v : HeightOneSpectrum R, (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
    fun v => ⟨0, (v.adicCompletionIntegers K).zero_mem⟩
  let t' : Set (RestrictedProduct (fun v : HeightOneSpectrum R => v.adicCompletion K)
          (fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K))) Filter.cofinite) := t
  have h1' : t' ∈
      nhds (RestrictedProduct.structureMap (fun v : HeightOneSpectrum R => v.adicCompletion K)
        (fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K))) Filter.cofinite z0) := ht
  rw [RestrictedProduct.nhds_eq_map_structureMap hAopen, Filter.mem_map, nhds_pi,
    Filter.mem_pi'] at h1'
  obtain ⟨I, u, hu, hIu⟩ := h1'
  have hW : ∀ v, ∃ W : Set (v.adicCompletion K), W ∈ nhds (0 : v.adicCompletion K) ∧
      ∀ y : v.adicCompletion K, (hy : y ∈ (v.adicCompletionIntegers K : Set (v.adicCompletion K))) →
        y ∈ W → (⟨y, hy⟩ : (v.adicCompletionIntegers K : Set (v.adicCompletion K))) ∈ u v := by
    intro v
    obtain ⟨W, hW, hWu⟩ := (mem_nhds_subtype _ (z0 v) (u v)).mp (hu v)
    exact ⟨W, hW, fun y hy hyW => hWu hyW⟩
  choose W hW0 hWu using hW
  obtain ⟨r, hr, hsmall⟩ :=
    PI.UnipApproxD.IntegersDenseFiniteAdeles.exists_small_finset (R := R) (K := K) I W (fun v _ => hW0 v)
  refine ⟨r, hr, fun y hy => ?_⟩
  have hint : ∀ v : HeightOneSpectrum R,
      y v ∈ (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
    intro v
    rw [SetLike.mem_coe, mem_adicCompletionIntegers]
    exact (hy v).trans (v.intValuation_le_one r)
  let z : ∀ v : HeightOneSpectrum R, (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
    fun v => ⟨y v, hint v⟩
  have hz : z ∈ Set.pi (↑I) u := fun v hv => hWu v _ (hint v) (hsmall v hv _ (hy v))
  have hmem := hIu hz
  have e : RestrictedProduct.structureMap (fun v : HeightOneSpectrum R => v.adicCompletion K)
        (fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K))) Filter.cofinite z = y := by
    ext v; rfl
  rw [← e]
  exact hmem

end GlobalTheory.OpenSubAdele

namespace GlobalTheory.OpenSubAdele

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

theorem exists_nat_mul_mem_of_mem_nhds {F : Type} [Field F] [NumberField F] {t : Set (Af F)}
    (ht : t ∈ nhds (0 : Af F)) :
    ∃ M₀ : ℕ, 0 < M₀ ∧ ∀ b ∈ GlobalTheory.HolDict.ShortVec.intRing F, (M₀ : Af F) * b ∈ t := by
  obtain ⟨r, hr, h⟩ := exists_small_of_mem_nhds (R := 𝓞 F) (K := F) ht
  have hc := Ideal.comap_ne_bot_of_integral_mem (R := ℤ) (I := Ideal.span {r}) hr
    (Ideal.mem_span_singleton_self r) (Algebra.IsIntegral.isIntegral r)
  obtain ⟨m, hm, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc
  rw [Ideal.mem_comap, Ideal.mem_span_singleton] at hm
  have hdvd : r ∣ ((m.natAbs : ℕ) : 𝓞 F) := by
    refine hm.trans ((map_dvd (algebraMap ℤ (𝓞 F)) (Int.dvd_natAbs.mpr dvd_rfl)).trans ?_)
    simp
  obtain ⟨c, hc⟩ := hdvd
  refine ⟨m.natAbs, Int.natAbs_pos.mpr hm0, fun b hb => h _ fun v => ?_⟩
  have hb' : evalV F v b ∈ v.adicCompletionIntegers F := Subring.mem_iInf.mp hb v
  change Valued.v (evalV F v ((m.natAbs : Af F) * b)) ≤ _
  have e : ((m.natAbs : ℕ) : Fv F v) =
      algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F (r * c)) := by
    rw [← hc]; simp
  rw [map_mul, map_natCast, e, Valuation.map_mul, PI.UnipApproxD.IntegersDenseFiniteAdeles.val_R, map_mul]
  calc v.intValuation r * v.intValuation c * Valued.v (evalV F v b)
      ≤ v.intValuation r * 1 * 1 :=
        mul_le_mul' (mul_le_mul' le_rfl (v.intValuation_le_one c))
          ((mem_adicCompletionIntegers _ _ _).mp hb')
    _ = v.intValuation r := by simp

end GlobalTheory.OpenSubAdele

namespace GlobalTheory.OpenSubAdele

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

noncomputable def singleEntry (D : D7) (V W : HSp D) (i : Fin W.rank) (j : Fin V.rank)
    (k : Fin (Module.finrank D.host.F D.host.E)) (c : Af D.host.F) : WO V W :=
  Matrix.of fun i' j' => if i = i' then if j = j' then
    pairA D.host.F 0 c ⊗ₜ[D.host.F] Module.finBasis D.host.F D.host.E k else 0 else 0

theorem continuous_singleEntry (D : D7) (V W : HSp D) (i : Fin W.rank) (j : Fin V.rank)
    (k : Fin (Module.finrank D.host.F D.host.E)) : Continuous (singleEntry D V W i j k) := by
  have hp : Continuous (fun c : Af D.host.F => pairA D.host.F 0 c) := by
    unfold pairA; fun_prop
  have ht : Continuous (fun c : Af D.host.F =>
      (pairA D.host.F 0 c ⊗ₜ[D.host.F] Module.finBasis D.host.F D.host.E k : AE D)) := by
    have e : (fun c : Af D.host.F =>
        (pairA D.host.F 0 c ⊗ₜ[D.host.F] Module.finBasis D.host.F D.host.E k : AE D)) =
        fun c => pairA D.host.F 0 c •
          ((1 : AF D.host.F) ⊗ₜ[D.host.F] Module.finBasis D.host.F D.host.E k : AE D) := by
      funext c; rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [e]
    exact hp.smul (continuous_const (y := ((1 : AF D.host.F) ⊗ₜ[D.host.F] Module.finBasis D.host.F D.host.E k : AE D)))
  unfold singleEntry
  refine continuous_pi fun i' => continuous_pi fun j' => ?_
  simp only [Matrix.of_apply]
  split_ifs
  · exact ht
  · exact continuous_const
  · exact continuous_const

theorem singleEntry_zero (D : D7) (V W : HSp D) (i : Fin W.rank) (j : Fin V.rank)
    (k : Fin (Module.finrank D.host.F D.host.E)) : singleEntry D V W i j k 0 = 0 := by
  ext i' j'
  have h0 : pairA D.host.F 0 0 = 0 := rfl
  simp [singleEntry, h0]

theorem exists_nat_mul_mem_openAddSubgroup : ∀ (D : D7) (V W : HSp D) (U : AddSubgroup (WO V W)),
    IsOpen (U : Set (WO V W)) → ∃ M₀ : ℕ, 0 < M₀ ∧
      ∀ a : Fin W.rank → Fin V.rank → Fin (Module.finrank D.host.F D.host.E) → Af D.host.F,
        (∀ i j k, a i j k ∈ GlobalTheory.HolDict.ShortVec.intRing D.host.F) →
        (Matrix.of fun i j => ∑ k, pairA D.host.F 0 ((M₀ : Af D.host.F) * a i j k) ⊗ₜ[D.host.F]
          Module.finBasis D.host.F D.host.E k : WO V W) ∈ U := by
  intro D V W U hU
  have hnhds : (⋂ x : Fin W.rank × Fin V.rank × Fin (Module.finrank D.host.F D.host.E),
      singleEntry D V W x.1 x.2.1 x.2.2 ⁻¹' (U : Set (WO V W))) ∈ nhds (0 : Af D.host.F) := by
    refine Filter.iInter_mem.mpr fun x => ?_
    refine (continuous_singleEntry D V W x.1 x.2.1 x.2.2).continuousAt.preimage_mem_nhds ?_
    rw [singleEntry_zero]
    exact hU.mem_nhds U.zero_mem
  obtain ⟨M₀, hM₀, hM⟩ := exists_nat_mul_mem_of_mem_nhds hnhds
  refine ⟨M₀, hM₀, fun a ha => ?_⟩
  have hsum : (Matrix.of fun i j => ∑ k, pairA D.host.F 0 ((M₀ : Af D.host.F) * a i j k) ⊗ₜ[D.host.F]
          Module.finBasis D.host.F D.host.E k : WO V W) =
      ∑ i, ∑ j, ∑ k, singleEntry D V W i j k ((M₀ : Af D.host.F) * a i j k) := by
    ext i' j'
    simp [singleEntry, Matrix.sum_apply]
  rw [hsum]
  refine U.sum_mem fun i _ => U.sum_mem fun j _ => U.sum_mem fun k _ => ?_
  have := hM _ (ha i j k)
  exact Set.mem_iInter.mp this (i, j, k)

end GlobalTheory.OpenSubAdele
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNeZeroLatticeVacuumSelfDualStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ne_zero_latticeVacuum_selfDual : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → ∀ Γ ≤ latO S T (LS : Set _) (LT : Set _) (fun _ => True), ∃ f, VacG ψ S T Γ f ∧ f ≠ 0 := by
  first | exact @GlobalTheory.AscFin.VacSub.exists_vacG_ne_zero | exact GlobalTheory.AscFin.VacSub.exists_vacG_ne_zero | (intros; apply GlobalTheory.AscFin.VacSub.exists_vacG_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalFullRankBesselBasePointStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_fullRank_besselBasePoint : ∀ (D : D7) (σ : ℕ) (B : BesL D σ), ∃ x ∈ {x : Matrix (Fin B.V.rank) (Fin (σ + 1)) D.host.E | LinearIndependent D.host.E x.transpose ∧ GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew B.V (rat x : Mx D B.V.rank (σ + 1)) = GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew B.L (zEll B.L (σ + 1) B.ζ)}, (rat x : Mx D B.V.rank (σ + 1)) = xLast B.d (vecB B.o B.ζ) := by
  first | exact @GlobalTheory.Asc.FBx.exists_rat_eq_xLast | exact GlobalTheory.Asc.FBx.exists_rat_eq_xLast | (intros; apply GlobalTheory.Asc.FBx.exists_rat_eq_xLast <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalLeviScalingIsotropicFrameStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rationalLevi_scaling_isotropicFrame : ∀ (D : D7) (V V' : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∃ a : GA D V, a ∈ GQ V ∧ HMul.hMul (matHom V a).1 (C.map (incA D)) = (2 : AE D) • C.map (incA D) ∧ HMul.hMul (matHom V a).1 (B.map (incA D)) = B.map (incA D) ∧ (2 : AE D) • HMul.hMul (matHom V a).1 (C'.map (incA D)) = C'.map (incA D) := by
  first | exact @GlobalTheory.LeviScale.exists_levi_scale | exact GlobalTheory.LeviScale.exists_levi_scale | (intros; apply GlobalTheory.LeviScale.exists_levi_scale <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralEqSetIntegralTsumRationalTranslatesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_eq_setIntegral_tsum_rationalTranslates : ∀ (D : D7) (m n : ℕ) (μ : Measure (Mx D m n)) (𝓕 : Set (Mx D m n)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratMx D m n) 𝓕 μ → ∀ c : Mx D m n → ℂ, Integrable c μ → (∀ᵐ y ∂(μ.restrict 𝓕), Summable fun a : Matrix (Fin m) (Fin n) D.host.E => ‖c (y + a.map (incA D))‖) ∧ ∫ y, c y ∂μ = ∫ y in 𝓕, ∑' a : Matrix (Fin m) (Fin n) D.host.E, c (y + a.map (incA D)) ∂μ := by
  first | exact @GlobalTheory.Twist.Periodize.integral_eq_setIntegral_tsum | exact GlobalTheory.Twist.Periodize.integral_eq_setIntegral_tsum | (intros; apply GlobalTheory.Twist.Periodize.integral_eq_setIntegral_tsum <;> assumption)
end

