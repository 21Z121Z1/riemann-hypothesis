import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0293
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0289
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0238
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUniqueIsometryFixingBothFramesOfFrameAdapt
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0015
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0060
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0290
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0291
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0279
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaugeMeasureQuotientUnitaryJVectorStabiliser
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsNearestPointCosetOrthogonalLieAlgebra
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

noncomputable section

namespace GlobalTheory.IwConstMin

variable {n : ℕ}

private lemma hs_eq_re_trace' (X : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.hs X = ((X * Xᴴ).trace).re := by
  simp only [Formalism.REAL.hs, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

theorem hs_unitary_sub_one {u : Matrix (Fin n) (Fin n) ℂ} (hu : uᴴ * u = 1) :
    Formalism.REAL.hs (u - 1) = 2 * ((1 : Matrix (Fin n) (Fin n) ℂ).trace).re - 2 * (u.trace).re := by
  have h2 : u * uᴴ = 1 := mul_eq_one_comm.mp hu
  rw [hs_eq_re_trace', conjTranspose_sub, conjTranspose_one]
  have e : (u - 1) * (uᴴ - 1) = 1 - u - uᴴ + 1 := by
    rw [sub_mul, mul_sub, mul_sub, h2, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul]
    abel
  rw [e, trace_add, trace_sub, trace_sub, trace_conjTranspose]
  simp only [Complex.add_re, Complex.sub_re, Complex.star_def, Complex.conj_re]
  ring

theorem re_trace_eq_zero_of_max (X u : Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ t : ℝ, ((NormedSpace.exp ((t : ℂ) • X) * u).trace).re ≤ (u.trace).re) : ((X * u).trace).re = 0 := by
  let _ : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  let φ : Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap (Complex.reLm ∘ₗ Matrix.traceLinearMap (Fin n) ℝ ℂ)
  have hφ : ∀ M, φ M = (M.trace).re := fun M => rfl
  have hd : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • X) * u)
      (NormedSpace.exp ((0 : ℝ) • X) * X * u) 0 :=
    (hasDerivAt_exp_smul_const X (0 : ℝ)).mul_const u
  have hf : HasDerivAt (fun t : ℝ => φ (NormedSpace.exp (t • X) * u))
      (φ (NormedSpace.exp ((0 : ℝ) • X) * X * u)) 0 :=
    φ.hasFDerivAt.comp_hasDerivAt 0 hd
  have hmax : IsLocalMax (fun t : ℝ => φ (NormedSpace.exp (t • X) * u)) 0 := by
    refine Filter.Eventually.of_forall fun t => ?_
    simp only [hφ, zero_smul, NormedSpace.exp_zero, Matrix.one_mul]
    have := h t
    rwa [GlobalTheory.IwTangent.coe_smul_eq] at this
  have h0 := hmax.hasDerivAt_eq_zero hf
  simpa [hφ, NormedSpace.exp_zero] using h0

theorem uMat_mul' {ε : Fin n → Bool} (g h : Formalism.REAL.UJ ε) : uMat (g * h) = uMat g * uMat h := rfl

theorem maxK_mul {ε : Fin n → Bool} {g h : Formalism.REAL.UJ ε} (hg : g ∈ maxK ε) (hh : h ∈ maxK ε) : g * h ∈ maxK ε := by
  have hg' : (uMat g)ᴴ * uMat g = 1 := hg
  have hh' : (uMat h)ᴴ * uMat h = 1 := hh
  show (uMat (g * h))ᴴ * uMat (g * h) = 1
  rw [uMat_mul', conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (uMat g)ᴴ, hg',
    Matrix.one_mul, hh']

theorem exists_nearest : ∀ (n : ℕ) (ε : Fin n → Bool) (S : Set (Formalism.REAL.UJ ε)) (d : ℕ) (E : Fin d → Matrix (Fin n) (Fin n) ℂ), IsCut ε S E → S ⊆ maxK ε → (∀ i, (E i)ᴴ = -E i) → ∀ k ∈ maxK ε, ∃ l ∈ S, crd E (uMat (l * k) - 1) = 0 ∧ ∀ l' ∈ S, nrm (uMat (l * k) - 1) ≤ nrm (uMat (l' * k) - 1) := by
  intro n ε S d E hcut hSK hE k hk
  obtain ⟨H, hHS, hSc⟩ := IsCut.subgroup hcut
  have hmemS : ∀ g, g ∈ S ↔ g ∈ H := fun g => by rw [← hHS]; rfl
  have hcpt : IsCompact S := (isCompact_maxK ε).of_isClosed_subset hSc hSK
  have hne : S.Nonempty := ⟨1, (hmemS 1).2 H.one_mem⟩
  have hcont : Continuous fun l : Formalism.REAL.UJ ε => nrm (uMat (l * k) - 1) :=
    (continuous_nrm_uMat ε).comp (continuous_mul_const k)
  obtain ⟨l, hlS, hmin⟩ := hcpt.exists_isMinOn hne hcont.continuousOn
  refine ⟨l, hlS, ?_, fun l' hl' => hmin hl'⟩
  set w := uMat (l * k) with hw
  have hwK : l * k ∈ maxK ε := maxK_mul (hSK hlS) hk
  have hwU : wᴴ * w = 1 := hwK
  funext i
  have hflow := (GlobalTheory.IwTangent.lie_algebra_of_isCut n ε S d E hcut).1 (E i)
    (Submodule.subset_span ⟨i, rfl⟩)
  have hle : ∀ t : ℝ, ((NormedSpace.exp ((t : ℂ) • E i) * w).trace).re ≤ (w.trace).re := by
    intro t
    obtain ⟨g, hgS, hg⟩ := hflow t
    have hgl : g * l ∈ S := (hmemS _).2 (H.mul_mem ((hmemS _).1 hgS) ((hmemS _).1 hlS))
    have hv : uMat (g * l * k) = NormedSpace.exp ((t : ℂ) • E i) * w := by
      rw [mul_assoc, uMat_mul', hg]
    have hvK : (uMat (g * l * k))ᴴ * uMat (g * l * k) = 1 := maxK_mul (hSK hgl) hk
    have hn : nrm (w - 1) ≤ nrm (uMat (g * l * k) - 1) := hmin hgl
    have hsq : Formalism.REAL.hs (w - 1) ≤ Formalism.REAL.hs (uMat (g * l * k) - 1) := by
      rw [← nrm_sq, ← nrm_sq]
      exact pow_le_pow_left₀ (nrm_nonneg _) hn 2
    rw [hs_unitary_sub_one hwU, hs_unitary_sub_one hvK, hv] at hsq
    linarith
  have hz : ((E i * w).trace).re = 0 := re_trace_eq_zero_of_max (E i) w hle
  have htr : ((E i).trace).re = 0 := by
    have h1 := congrArg (fun M => (M.trace).re) (hE i)
    simp only [trace_conjTranspose, Complex.star_def, Complex.conj_re, trace_neg, Complex.neg_re] at h1
    linarith
  have hcomm : ((w * E i).trace).re = ((E i * w).trace).re := by rw [trace_mul_comm]
  show ((( w - 1) * (E i)ᴴ).trace).re = 0
  rw [hE i, sub_mul, Matrix.mul_neg, Matrix.mul_neg, Matrix.one_mul, trace_sub, trace_neg, trace_neg,
    Complex.sub_re, Complex.neg_re, Complex.neg_re, hcomm, hz, htr]
  simp

end GlobalTheory.IwConstMin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsProductChartTangentEquivBallVolumeStatement
section
open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.Tube
open scoped InnerProductSpace ENNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_productChart_tangentEquiv_ballVolume : ∀ (k : ℕ) (η : ℝ), 1 ≤ k → (η = 1 ∨ η = -1) → ∃ L : Par k ≃L[ℝ] lieE (UH (Hd k η)), (∀ v : Par k, unrealify ((L v : lieE (UH (Hd k η))) : EuclideanSpace ℝ _) = tang η v) ∧ ∀ ρ : ℝ, 0 < ρ → volume (L '' Metric.ball (0 : Par k) ρ) = volume (Metric.ball (0 : lieE (UH (1 : Matrix (Fin k) (Fin k) ℂ))) ρ) * ENNReal.ofReal (2 * ρ * (Real.pi ^ k * ρ ^ (2 * k) / (k.factorial : ℝ))) := by
  first | exact @GlobalTheory.TubeLie.exists_tang_equiv | exact GlobalTheory.TubeLie.exists_tang_equiv | (intros; apply GlobalTheory.TubeLie.exists_tang_equiv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSigmaFiniteHaarFiniteAdelicUnitary
section
open MeasureTheory Formalism.MainNotions.S
open scoped InnerProductSpace

namespace GlobalTheory.CongTop

theorem exists_haar_sigmaFinite :
    ∀ (I : AutInst), ∃ μf : Measure I.Gf, μf.IsHaarMeasure ∧ SigmaFinite μf := by
  intro I
  obtain ⟨_, _, _, -⟩ := GlobalTheory.CongTop.adelic_topology I
  exact ⟨Measure.haar, inferInstance, inferInstance⟩

end GlobalTheory.CongTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUniqueIsometryFixingBothFramesOfFrameAdaptStatement
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_isometryFixingBothFrames_of_frameAdapted : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ s, Adapt s F F → Adapt s F' F' → ∃! h, h ∈ H0 F F' ∧ h⁻¹ * s ∈ NRat F ∧ h⁻¹ * s ∈ NRat F' := by
  first | exact @GlobalTheory.Unfold.Inter.common_stabiliser | exact GlobalTheory.Unfold.Inter.common_stabiliser | (intros; apply GlobalTheory.Unfold.Inter.common_stabiliser <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExtendFreeTupleGramHermitianFrame
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.FrameExtend

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem hR_sub_sum_right {m : ℕ} (x w : Fin n → R ⊗[F] E) (c : Fin m → R ⊗[F] E)
    (u : Fin m → Fin n → R ⊗[F] E) :
    hR R σ J x (w - ∑ a, c a • u a) = hR R σ J x w - ∑ a, c a * hR R σ J x (u a) := by
  simp only [hR, Formalism.UG.hform, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

end Alg

open GlobalTheory.FrameGram in

theorem extend_frame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ (r : ℕ) (P : Frame E n r) (T : F), P.IsStd σ J T → ∀ y : Fin (r + 1) → Fin n → Fv F v ⊗[F] E, LinearIndependent (Fv F v ⊗[F] E) y → gramR (Fv F v) σ J y = (gramE σ J (F0 P)).map (inclR (Fv F v)) → ∃ f : Fin r → Fin n → Fv F v ⊗[F] E, gramR (Fv F v) σ J (Fin.append y f) = (gramE σ J (tupH P)).map (inclR (Fv F v)) := by
  intro F E _ _ _ _ _ σ hσ n J hJ v r P T hP y hy hgram
  have hinv : ∀ x, σ (σ x) = x := conj_invol hσ
  obtain ⟨_, hGh, _, hG0, _⟩ := std_frame_gram F E σ hσ n J hJ r P T hP
  have hPs := hP
  obtain ⟨_, hff0, hef, _, hfz, _, _⟩ := hPs
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have : IsArtinianRing (Fv F v ⊗[F] E) := IsArtinianRing.of_finite (Fv F v) (Fv F v ⊗[F] E)
  have : IsReduced (Fv F v ⊗[F] E) := PI.VolStabS.isReduced_tens_field F E (Fv F v)
  have : IsSemisimpleRing (Fv F v ⊗[F] E) := IsArtinianRing.isSemisimpleRing_of_isReduced _
  let s := sigR (Fv F v) σ
  have hsw : ∀ x w, s (hR (Fv F v) σ J x w) = hR (Fv F v) σ J w x :=
    PI.VolStabS.hR_herm (Fv F v) σ hinv J hJ.1
  have hss : ∀ x, s (s x) = x := PI.VolStabS.sigR_invol (Fv F v) σ hinv

  let Z : Fin (r + 1) → Fin n → Fv F v ⊗[F] E := fun i => Matrix.vecMul (fun l => s (y i l)) (JR (F := F) (Fv F v) J)
  have hZh : ∀ i w, hR (Fv F v) σ J (y i) w = ∑ k, Z i k * w k := by
    intro i w
    simp only [hR, Formalism.UG.hform, Z, Matrix.vecMul, dotProduct, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hZ : LinearIndependent (Fv F v ⊗[F] E) Z := by
    have hJu : IsUnit (JR (F := F) (Fv F v) J).det := by
      have e := RingHom.map_det (inclR (F := F) (E := E) (Fv F v)) J
      rw [RingHom.mapMatrix_apply] at e
      show IsUnit (J.map (inclR (Fv F v))).det
      rw [← e]
      exact (isUnit_iff_ne_zero.2 hJ.2).map _
    refine Fintype.linearIndependent_iff.2 fun g hg i => ?_
    let w : Fin n → Fv F v ⊗[F] E := fun l => ∑ i, g i * s (y i l)
    have hv0 : Matrix.vecMul w (JR (F := F) (Fv F v) J) = 0 := by
      funext j
      have := congrFun hg j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Z, Matrix.vecMul, dotProduct,
        Finset.mul_sum, Pi.zero_apply] at this
      simp only [Matrix.vecMul, dotProduct, w, Finset.sum_mul, Pi.zero_apply]
      rw [Finset.sum_comm]
      rw [← this]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring
    have hv : w = 0 := by
      have := congrArg (fun u => Matrix.vecMul u (JR (F := F) (Fv F v) J)⁻¹) hv0
      simp only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hJu, Matrix.vecMul_one,
        Matrix.zero_vecMul] at this
      exact this
    have hX0 : ∑ i, s (g i) • y i = 0 := by
      funext l
      have := congrArg s (congrFun hv l)
      simp only [w, map_sum, map_mul, hss, Pi.zero_apply, map_zero] at this
      simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this
    have := Fintype.linearIndependent_iff.1 hy _ hX0 i
    have e2 := congrArg s this
    simp only [hss, map_zero] at e2
    exact e2
  obtain ⟨q, hq⟩ := PI.VolStabS.exists_leftInv_of_linIndep Z hZ

  let f' : Fin r → Fin n → Fv F v ⊗[F] E := fun b k => q k b.castSucc
  have hyf' : ∀ i b, hR (Fv F v) σ J (y i) (f' b) = if i = b.castSucc then 1 else 0 := by
    intro i b
    rw [hZh]
    exact hq i b.castSucc
  have hyy : ∀ i j, hR (Fv F v) σ J (y i) (y j) =
      inclR (Fv F v) (if i = Fin.last r ∧ j = Fin.last r then algebraMap F E (-T) else 0) := by
    intro i j
    have := congrFun (congrFun hgram i) j
    simp only [Matrix.map_apply, hG0] at this
    exact this
  have hyy0 : ∀ i (a : Fin r), hR (Fv F v) σ J (y i) (y a.castSucc) = 0 := by
    intro i a
    rw [hyy]
    simp [Fin.castSucc_ne_last]
  let h2 : Fv F v ⊗[F] E := algebraMap F (Fv F v ⊗[F] E) (1 / 2)
  have hh : h2 + h2 = 1 := by
    rw [← map_add, show (1 / 2 : F) + 1 / 2 = 1 by norm_num, map_one]
  have hsh : s h2 = h2 := (Algebra.TensorProduct.map (AlgHom.id F (Fv F v)) σ).commutes _
  let c : Fin r → Fin r → Fv F v ⊗[F] E := fun a b => h2 * hR (Fv F v) σ J (f' a) (f' b)
  let f : Fin r → Fin n → Fv F v ⊗[F] E := fun b => f' b - ∑ a, c a b • y a.castSucc
  have hyf : ∀ i b, hR (Fv F v) σ J (y i) (f b) = if i = b.castSucc then 1 else 0 := by
    intro i b
    simp only [f]
    rw [GlobalTheory.FrameExtend.hR_sub_sum_right, hyf']
    simp [hyy0]
  have hfy : ∀ b i, hR (Fv F v) σ J (f b) (y i) = if i = b.castSucc then 1 else 0 := by
    intro b i
    rw [← hsw, hyf]
    split_ifs <;> simp
  have hf'y : ∀ b (d : Fin r), hR (Fv F v) σ J (f' b) (y d.castSucc) = if d = b then 1 else 0 := by
    intro b d
    rw [← hsw, hyf']
    split_ifs with h1 h2 h2 <;> simp_all [Fin.castSucc_inj]
  have hff : ∀ a b, hR (Fv F v) σ J (f a) (f b) = 0 := by
    intro a b
    have e1 : hR (Fv F v) σ J (f a) (f b) = hR (Fv F v) σ J (f a) (f' b) - c a b := by
      simp only [f]
      rw [GlobalTheory.FrameExtend.hR_sub_sum_right]
      congr 1
      have := fun d => hfy a (Fin.castSucc d)
      simp only [f] at this
      simp [this, Fin.castSucc_inj]
    have e2 : hR (Fv F v) σ J (f' b) (f a) = hR (Fv F v) σ J (f' b) (f' a) - c b a := by
      simp only [f]
      rw [GlobalTheory.FrameExtend.hR_sub_sum_right]
      congr 1
      simp [hf'y]
    have e3 : hR (Fv F v) σ J (f a) (f' b) = hR (Fv F v) σ J (f' a) (f' b) - h2 * hR (Fv F v) σ J (f' a) (f' b) := by
      rw [← hsw, e2, map_sub, hsw]
      simp only [c, map_mul, hsh, hsw]
    rw [e1, e3]
    simp only [c]
    linear_combination (-(hR (Fv F v) σ J (f' a) (f' b))) * hh
  refine ⟨f, ?_⟩
  have hTL : ∀ i (b : Fin r), gramE σ J (tupH P) (Fin.castAdd r i) (Fin.natAdd (r + 1) b) =
      if i = b.castSucc then 1 else 0 := by
    intro i b
    simp only [gramE, tupH, Fin.append_left, Fin.append_right, F0]
    refine Fin.lastCases ?_ (fun a => ?_) i
    · rw [Fin.snoc_last, ← hE_swap hinv hJ.1 P.z (P.f b), hfz, map_zero]
      exact (if_neg (Fin.castSucc_ne_last b).symm).symm
    · rw [Fin.snoc_castSucc, hef]
      simp only [Fin.castSucc_inj]
  funext i j
  simp only [Matrix.map_apply]
  show hR (Fv F v) σ J (Fin.append y f i) (Fin.append y f j) = _
  refine Fin.addCases (fun i => ?_) (fun a => ?_) i <;>
    refine Fin.addCases (fun j => ?_) (fun b => ?_) j
  · rw [Fin.append_left, Fin.append_left, hyy, ← hG0]
    simp [gramE, tupH, Fin.append_left]
  · rw [Fin.append_left, Fin.append_right, hyf, hTL]
    split_ifs <;> simp
  · rw [Fin.append_right, Fin.append_left, hfy, ← hGh, hTL]
    split_ifs <;> simp
  · rw [Fin.append_right, Fin.append_right, hff]
    simp [gramE, tupH, Fin.append_right, hff0]

end GlobalTheory.FrameExtend
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopologyStatement
section
open MeasureTheory Formalism.MainNotions.S NumberField
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteAdelicUnitary_congruenceTopology : ∀ I : AutInst, T2Space I.Gf ∧ LocallyCompactSpace I.Gf ∧ SecondCountableTopology I.Gf ∧ IsCompact I.Kset ∧ IsOpen I.Kset ∧ (∃ K : Subgroup I.Gf, (K : Set I.Gf) = I.Kset) ∧ ∀ g : ℕ, 1 ≤ g → IsOpen (I.Kg g) ∧ (∃ K : Subgroup I.Gf, (K : Set I.Gf) = I.Kg g) ∧ ∀ k ∈ I.Kset, ∀ x ∈ I.Kg g, k * x * k⁻¹ ∈ I.Kg g := by
  first | exact @GlobalTheory.CongTop.adelic_topology | exact GlobalTheory.CongTop.adelic_topology | (intros; apply GlobalTheory.CongTop.adelic_topology <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteIsometriesFixingBothFramesStabilizingLattiStatement
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_isometriesFixingBothFrames_stabilizing_lattice : ∀ (D : D7) {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T'), (∀ x ∈ orth (VS D) (Xplus F ⊔ Xplus F'), x ≠ 0 → 0 < Algebra.trace ℚ D.host.E ((VS D).hT x x)) → ∀ Λ₀ : LV D, Submodule.IsLattice D.host.E Λ₀ → {h | h ∈ H0 F F' ∧ Formalism.HermitianLatticesTheory.gmap h Λ₀ = Λ₀}.Finite := by
  first | exact @GlobalTheory.StabFin.stab_finite | exact GlobalTheory.StabFin.stab_finite | (intros; apply GlobalTheory.StabFin.stab_finite <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FixedConvOfIntegralFlagLatticeStatement
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fixed_conv_of_integral_flag_lattice : ∀ (D : D7) (T : D.host.E) (F : FlagG (VS D) D.R.rS T) (Λ : LV D), XLam Λ (lf D F) = XS D F → (∀ c : D.host.E, c • F.z ∈ Lsub Λ (lf D F) → ∃ o : 𝓞 D.host.E, (o : D.host.E) = c) → IsFixedConv Λ (gS D) (lf D F) := by
  first | exact @GlobalTheory.FixConvRow.isFixedConv_of_XLam_eq | exact GlobalTheory.FixConvRow.isFixedConv_of_XLam_eq | (intros; apply GlobalTheory.FixConvRow.isFixedConv_of_XLam_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FixedFlagFrameVectorMemRowLatticeStatement
section
open scoped Classical ENNReal Pointwise
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fixedFlag_frameVector_mem_rowLattice : ∀ (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : LV D), IsRowLat D F0 Λ → ∀ a, frame (lf D F0) a ∈ Λ := by
  first | exact @GlobalTheory.Unfold.RowFrame.frame_mem | exact GlobalTheory.Unfold.RowFrame.frame_mem | (intros; apply GlobalTheory.Unfold.RowFrame.frame_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameAdaptedIsometryMapFlagSpacesStatement
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameAdaptedIsometry_map_flagSpaces : ∀ (D : D7) (T : D.host.E) (F G : LFlag (VS D) D.R.rS T) (g : GV D), Adapt g F G → (∀ j : ℕ, (Xflag F j).map (g : (VS D).V →ₗ[D.host.E] (VS D).V) = Xflag G j) ∧ (Xsp F).map (g : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp G := by
  first | exact @GlobalTheory.adapt_map_flag | exact GlobalTheory.adapt_map_flag | (intros; apply GlobalTheory.adapt_map_flag <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FundamentalDomainNormalisingConstantsStatement
section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fundamental_domain_normalising_constants : ∀ (D : D7), (∀ a, 0 < sc D a) ∧ |(NumberField.discr D.host.F : ℝ)| ^ (-(((D.R.k : ℝ) + 1) * (D.R.rS : ℝ) ^ 2) - 4 * ((D.R.rS : ℝ) ^ 3 - D.R.rS) / 3 - 3 * (D.R.rS : ℝ) / 2) * (∏ a : Fin D.R.rS, sc D a ^ (4 * (D.R.rS - (a : ℕ)) + 2 * D.R.k)) ^ Fintype.card (InfinitePlace D.host.E) = (2 * D.host.v) ^ (((D.R.rS : ℝ) ^ 2 + (D.R.rS : ℝ) * D.R.k + (D.R.rS : ℝ) / 2) * Fintype.card D.what₂.Tau) := by
  first | exact @GlobalTheory.CovDom.normalising_constants | exact GlobalTheory.CovDom.normalising_constants | (intros; apply GlobalTheory.CovDom.normalising_constants <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaugeMeasureQuotientUnitaryJVectorStabiliserStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gauge_measure_quotient_unitaryJ_vector_stabiliser : ∀ (n : ℕ) (ε : Fin (n + 1) → Bool) (ε' : Fin n → Bool) (s : Bool) (x₀ : Fin (n + 1) → ℂ) (B : Matrix (Fin (n + 1)) (Fin n) ℂ) (j : Formalism.REAL.UJ ε' →* Formalism.REAL.UJ ε), qEps ε x₀ = sgn ℝ s → star x₀ ᵥ* (Formalism.REAL.Jm ε * B) = 0 → Bᴴ * Formalism.REAL.Jm ε * B = Formalism.REAL.Jm ε' → (∀ g, uMat (j g) *ᵥ x₀ = x₀ ∧ uMat (j g) * B = B * uMat g) → ∀ c c' : ℝ, IsGauge ε c → IsGauge ε' c' → ∀ b : Formalism.REAL.UJ ε → ENNReal, Measurable b → (∀ g, ENNReal.ofReal c' * ∫⁻ h, b (j h * g) ∂(Formalism.REAL.muG ε') = 1) → ENNReal.ofReal c * ∫⁻ g, ENNReal.ofReal (gauss ((uMat g)⁻¹ *ᵥ x₀)) * b g ∂(Formalism.REAL.muG ε) = ENNReal.ofReal (2 ^ (n + 1) * gaussDens ε (sgn ℝ s)) := by
  first | exact @GlobalTheory.GaugeQuot.gauge_quotient | exact GlobalTheory.GaugeQuot.gauge_quotient | (intros; apply GlobalTheory.GaugeQuot.gauge_quotient <;> assumption)
end

