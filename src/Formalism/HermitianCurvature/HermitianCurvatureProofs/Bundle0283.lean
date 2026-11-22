import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0280
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0282
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0236
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0164
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0201
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0257
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0253
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0281
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0247
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0279
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0259
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0256
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WordInd
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0267
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ProperLeftVariablesDomain
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0189
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0263
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SlicesFiniteRegularityBuilt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MulVecBvecApply
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0276
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0272
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0278

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSEJSliceCut
section
open MeasureTheory Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB Formalism.FourierDecayAlt.P5.HerC
  Formalism.FourierDecayAlt.P5.HerD

def wlv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (A B : E) : ℂ →L[ℝ] E :=
  (ContinuousLinearMap.id ℝ ℂ).smulRight A + Complex.conjCLE.toContinuousLinearMap.smulRight B

section WaveJc

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
variable (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
  (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (D : B.RealPlaceData P.k P.r Wp Wq) (l : Fin P.r)

def IsWaveJc (Ψ : RadSp P.k P.r z z' π π') : Prop :=
  Ψ ∈ lcSub P.k P.r z z' π π' ∧ ∃ (s : ℂ) (ε : ℝ) (G : Mx P.k P.r → (Wq →L[ℂ] Wp)), 0 < ε ∧ JC.NiceCoef D ε G ∧
    HasCompactSupport G ∧ ∀ y ∈ DomR P.k P.r z z', (Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) y.1 y.2 =
      fsv s (y.1 l) • resG P.k P.r (Fin.last P.r) (B.JF D G) y.1 y.2

def waveJc : Submodule ℂ (RadSp P.k P.r z z' π π') :=
  Submodule.span ℂ {Ψ | IsWaveJc P z z' π π' D l Ψ}

end WaveJc

def JSliceGenC : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' →
    ∀ (l : Fin P.r), l.val = 0 →
    ∀ c ∈ OmX P.r, ∀ Ψ : RadSp P.k P.r z z' π π', IsWaveJc P z z' π π' D l Ψ → SliceGood X μ l c Ψ

def JSPointDeriv : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (π : Mx k r → (Wp →L[ℂ] Wp)) (π' : Mx k r → (Wq →L[ℂ] Wq)) (X : ActualOps k r z z' π π') (l : Fin r)
    (Φ : RadSp k r z z' π π') (p : Fin r → ℂ) (g : Mx k r) (t : ℂ), t ≠ 0 →
    HasFDerivAt (fun s : ℂ => (Φ : Fn k r (Wq →L[ℂ] Wp)) (Function.update p l s) g)
      (wlv (((dT X l Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) (Function.update p l t) g)
        (((dTb X l Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) (Function.update p l t) g)) t

def JSSob2 : Prop :=
  ∀ (t0 : ℂ) (δ : ℝ), 0 < δ → ∃ K : ℝ, ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f fx fy fxy : ℂ → E),
    (∀ t ∈ Metric.closedBall t0 (2 * δ),
      HasFDerivAt f (Complex.reCLM.smulRight (fx t) + Complex.imCLM.smulRight (fy t)) t) →
    (∀ t ∈ Metric.closedBall t0 (2 * δ), ∃ fyy : E,
      HasFDerivAt fy (Complex.reCLM.smulRight (fxy t) + Complex.imCLM.smulRight fyy) t) →
    ContinuousOn fx (Metric.closedBall t0 (2 * δ)) → ContinuousOn fxy (Metric.closedBall t0 (2 * δ)) →
    ∀ t ∈ Metric.ball t0 δ, ‖f t‖ ^ 2 ≤
      K * ∫ s in Metric.closedBall t0 (2 * δ), (‖f s‖ ^ 2 + ‖fx s‖ ^ 2 + ‖fy s‖ ^ 2 + ‖fxy s‖ ^ 2)

def JSPairCont : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (π : Mx k r → (Wp →L[ℂ] Wp)) (π' : Mx k r → (Wq →L[ℂ] Wq)) (μ : Measure (Mt k r)),
    B.IsHaarOn (Glev k r (Fin.last r)) μ → ∀ (Φ Ψ : RadSp k r z z' π π'), Φ ∈ lcSub k r z z' π π' →
    Ψ ∈ lcSub k r z z' π π' → ContinuousOn (fun p => pairAt μ Φ Ψ p) (OmX r)

def JSMeas : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (π : Mx k r → (Wp →L[ℂ] Wp)) (π' : Mx k r → (Wq →L[ℂ] Wq)) (l : Fin r) (c : Fin r → ℂ)
    (Φ Ψ : RadSp k r z z' π π'),
    Measurable (fun q : (ℂ × Cf r l.succ) × Mt k r =>
      B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) (glue l.succ (Function.update c l q.1.1) q.1.2) (Matrix.of q.2))
        ((Ψ : Fn k r (Wq →L[ℂ] Wp)) (glue l.succ (Function.update c l q.1.1) q.1.2) (Matrix.of q.2)))

def SpectralL2Locality : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' →
    ∀ (l : Fin P.r), l.val = 0 →
    ∀ c ∈ OmX P.r, ∀ Ψ : RadSp P.k P.r z z' π π', IsWaveJc P z z' π π' D l Ψ → ∀ (js : List (Fin 6)) (t0 : ℂ),
      t0 ≠ 0 → ∃ ε : ℝ, 0 < ε ∧ ∃ M : ℝ, ∀ t ∈ Metric.ball t0 ε,
        LevelSquareIntegrable μ l.succ (wOp X l js Ψ) (Function.update c l t) ∧
          ‖fs μ l (wOp X l js Ψ) (wOp X l js Ψ) c t‖ ≤ M

def JSWordNF : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (π : Mx k r → (Wp →L[ℂ] Wp)) (π' : Mx k r → (Wq →L[ℂ] Wq)) (X : ActualOps k r z z' π π') (l : Fin r)
    (s : ℂ) (Wv : Module.End ℂ (RadSp k r z z' π π')), multiplicationOperator Wv (fun c _ => fsv s (c l)) →
    ∀ js : List (Fin 6), ∃ (K : ℕ) (m : Fin K → ℂ → ℂ) (ab : Fin K → List (Fin 6)),
      (∀ i, ContinuousOn (m i) {0}ᶜ) ∧ (∀ i, ∀ j ∈ ab i, j = 0 ∨ j = 3) ∧
      ∀ (Φ : RadSp k r z z' π π') (p : Fin r → ℂ), p ∈ OmX r → ∀ g : Mx k r,
        (wOp X l js (Wv Φ) : Fn k r (Wq →L[ℂ] Wp)) p g =
          ∑ i, (m i (p l) * fsv s (p l)) • (wOp X l (ab i) Φ : Fn k r (Wq →L[ℂ] Wp)) p g

def JSRadLoc : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' →
    ∀ (l : Fin P.r), l.val = 0 → ∀ (ε : ℝ), 0 < ε → ∀ G : Mx P.k P.r → (Wq →L[ℂ] Wp), JC.NiceCoef D ε G →
    HasCompactSupport G → ∀ Φ : RadSp P.k P.r z z' π π', Φ ∈ lcSub P.k P.r z z' π π' →
    (∀ y ∈ DomR P.k P.r z z', (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) y.1 y.2 =
      resG P.k P.r (Fin.last P.r) (B.JF D G) y.1 y.2) →
    ∀ c ∈ OmX P.r, ∀ js : List (Fin 6), (∀ j ∈ js, j = 0 ∨ j = 3) → ∀ t0 : ℂ, t0 ≠ 0 →
      ∃ ε' : ℝ, 0 < ε' ∧ ∃ M : ℝ, ∀ t ∈ Metric.ball t0 ε',
        LevelSquareIntegrable μ l.succ (wOp X l js Φ) (Function.update c l t) ∧
          ‖fs μ l (wOp X l js Φ) (wOp X l js Φ) c t‖ ≤ M

end Formalism.FourierDecayAlt.P.CutSE
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDBdd
section
open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

theorem norm_fsv_rd (s t : ℂ) : ‖fsv s t‖ = 1 := by
  unfold fsv
  rw [Complex.norm_exp]
  have h : (s * t - (starRingEnd ℂ) s * (starRingEnd ℂ) t).re = 0 := by
    rw [← map_mul, Complex.sub_re, Complex.conj_re, sub_self]
  rw [h, Real.exp_zero]

theorem hsVec_smul_rd {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (c : ℂ) (A : Wq →L[ℂ] Wp) :
    B.hsVec (c • A) = c • B.hsVec A := by
  unfold B.hsVec
  rfl

theorem radial_boundedness : RDBdd := by
  intro k r Wp Wq _ _ _ _ _ _ D F H _ _
  refine ⟨∫ q, ‖(bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) *
      inner ℂ (B.hsVec (B.JF D H (B.gq D q))) (B.hsVec (B.JF D F (B.gq D q)))‖, fun s => ?_⟩
  have h1 : 1 < r + 2 := by omega
  have hinv : ∀ p : B.SS k r, D.inSS p → ∀ g,
      fsv s (Dmin k r D.z D.z' (B.sgs p g) ⟨1, h1⟩) = fsv s (Dmin k r D.z D.z' g ⟨1, h1⟩) := fun p hp g => by
    rw [Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs D hp g]
  have hJ : ∀ g, B.JF D (wvG D.z D.z' s F) g = fsv s (Dmin k r D.z D.z' g ⟨1, h1⟩) • B.JF D F g := fun g =>
    Formalism.FourierDecayAlt.P.PBFV.JF_mul_inv D _ hinv F g
  unfold B.beta betaBig
  refine (norm_integral_le_integral_norm _).trans
    (le_of_eq (integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)))
  show ‖(bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) *
      inner ℂ (B.hsVec (B.JF D H (B.gq D q))) (B.hsVec (B.JF D (wvG D.z D.z' s F) (B.gq D q)))‖ = _
  rw [hJ, hsVec_smul_rd, inner_smul_right]
  simp only [norm_mul, norm_fsv_rd, one_mul]

end Formalism.FourierDecayAlt.P.CutSE
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDBeta
section
open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

theorem radial_beta_identity : RDBeta := by
  intro k r Wp Wq _ _ _ _ _ _ D μ hμ
  obtain ⟨C1, hC1, hpair⟩ := Formalism.FourierDecayAlt.P.JCx2.rb_pairAt D μ hμ
  refine ⟨(C1 : ℂ), by exact_mod_cast hC1.ne', fun F H Φ Ψ hF hH hΦ hΨ c => ?_⟩
  have h := Formalism.FourierDecayAlt.P.JCx2.rb_main D μ C1 hpair (n := 0) (fun _ => F) (fun _ => H) (fun _ => Φ) (fun _ => Ψ)
    (fun _ => hF) (fun _ => hH) (fun _ => hΦ) (fun _ => hΨ)
  have hsum : ∑ _a : Wd.Ix (Fin 0), B.beta D F H = B.beta D F H := by simp
  rw [hsum] at h
  rw [← h]
  unfold LocFacts₂ P5.form
  refine integral_congr_ae (Filter.Eventually.of_forall fun c' => ?_)
  have hg : glue (0 : Fin (r + 1)) c c' = glue 0 0 c' := by
    funext l
    simp only [glue]
    have h0 : ((0 : Fin (r + 1)) : ℕ) ≤ (l : ℕ) := Nat.zero_le _
    rw [dif_pos h0, dif_pos h0]
  simp only [hg, Finset.univ_unique, Finset.sum_singleton]

end Formalism.FourierDecayAlt.P.CutSE
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSEWaveOutJ
section
open MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB Formalism.FourierDecayAlt.P5.HerC
  Formalism.FourierDecayAlt.P5.HerD

theorem wave_outgoing_orbital : WaveOutJ := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D hdat hl0 hle hz hz' hπ hπ' l hl u v hu hv c hc s Wv hW
  have hμ : B.IsHaarOn (Glev P.k P.r (Fin.last P.r)) μ := hdat.2.1
  haveI := sfinite_of_isHaarOn _ μ hμ

  have hl2u := fun b => wave_operator_le_l2_subspace P z z' π π' μ hμ D hz hz' hπ hπ' l (hu b)
  have hl2v := fun b => wave_operator_le_l2_subspace P z z' π π' μ hμ D hz hz' hπ hπ' l (hv b)
  have hW1 : ∀ c' : Fin P.r → ℂ, ‖fsv s (c' l)‖ = 1 := fun c' => HerC.norm_fsv s (c' l)
  have hl' : l.castSucc = 0 := by
    ext
    simp [hl]
  have keyu : ∀ b, LevelSquareIntegrable μ l.castSucc (u b) c := by
    intro b
    rw [hl']
    exact (hl2u b).2 c
  have keyv : ∀ b, LevelSquareIntegrable μ l.castSucc (v b) c := by
    intro b
    rw [hl']
    exact (hl2v b).2 c

  have keyW : ∀ b, LevelSquareIntegrable μ l.castSucc (Wv (u b)) c := by
    intro b
    have h := keyu b
    unfold LevelSquareIntegrable at h ⊢
    simp only [waveOut_pairAt_self μ hW hW1]
    exact h
  have hd := dens_int μ hμ l (fun b => Wv (u b)) v (fun b => mul_lc hW _ (hl2u b).1)
    (fun b => (hl2v b).1) c keyW keyv
  rw [← hd.2]
  simp_rw [waveOut_dens μ l s hW u v c]

end Formalism.FourierDecayAlt.P.CutSE
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSE_RDWave
section
open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

theorem radial_wave_identity : RDWave := by
  intro k r Wp Wq _ _ _ _ _ _ D hr ε s G
  have h1 : 1 < r + 2 := by omega
  refine ⟨fun hG => Formalism.FourierDecayAlt.P.PBFV.good_fsv_dmin D ε s h1 G hG, fun y hy => ?_⟩
  have hinv : ∀ p : B.SS k r, D.inSS p → ∀ g,
      fsv s (Dmin k r D.z D.z' (B.sgs p g) ⟨1, h1⟩) = fsv s (Dmin k r D.z D.z' g ⟨1, h1⟩) := fun p hp g => by
    rw [Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs D hp g]
  simp only [resG]
  rw [show wvG D.z D.z' s G = fun g => fsv s (Dmin k r D.z D.z' g ⟨1, h1⟩) • G g from rfl,
    Formalism.FourierDecayAlt.P.PBFV.JF_mul_inv D _ hinv G]
  rw [Formalism.FourierDecayAlt.P.PBFV.first_minor_cell_eq_coord D.z_mem D.z'_mem hr y.1 hy.2.1 h1]
  exact smul_comm _ _ _

end Formalism.FourierDecayAlt.P.CutSE
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSHChk
section
namespace Formalism.FourierDecayAlt.P

theorem cutSH_sliceStepHer_of_sfg (h7 : CutSH.SliceFamGood) : PTie.SliceStepHer :=
  CutSH.sliceStepHer_of CutSH.family_orbital_valid CutSH.family_algebraic CutSH.representation_linear
    cell_compatibility_identity h7 CutSH.slice_family_orbital operator_class_closed boundary_torus_adjoin
    unipotent_scalar_identity

theorem cutSH_levTransportHer_of_sfg (h7 : CutSH.SliceFamGood) : PTie.LevTransportHer :=
  ptie_levTransportHer_of_sliceStep (cutSH_sliceStepHer_of_sfg h7)

theorem level_transport_hermitian : PTie.LevTransportHer := cutSH_levTransportHer_of_sfg slice_family_good

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadJacquetOfLetterAndHead
section
noncomputable section

namespace Formalism.FourierDecayAlt.P

theorem head_jacquet_of_letter_and_head (hHL : LevelPointCoordinates.HeadLetter) (hB : LevelPointCoordinates.HeadBridge) : LevelPointCoordinates.HeadJ :=
  LevelPointCoordinates.headJ_of (word_induction_of_parts hHL z_only rules_closed) hB

theorem radial_head_of_letter_and_head (hHL : LevelPointCoordinates.HeadLetter) (hB : LevelPointCoordinates.HeadBridge) : KB.RadHead :=
  pb_radHead_of_headJ (head_jacquet_of_letter_and_head hHL hB)

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.Side0PosOf
section
open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.SliceIntegralLemmas

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.LeftFubiniLemmas

theorem side0Pos_of (hW : PartialBesselProperness.PbWords) (hPr : ProperLeftVariablesDomain) (hPts : CutHB.Pts) : CutHB.Side0Pos := by
  intro Wp Wq _ _ _ _ _ _ P p F j hj w h hh γ hj1 hF hw hγ hΩ e τ hτ
  have hPt := hPts Wp Wq P p j hj h hh γ hγ hΩ
  obtain ⟨hab, rfl⟩ := hh
  have hjr : D.ptSize h ≤ P.r := by omega
  have e0 : D.ptSize h + (P.r - D.ptSize h) = P.r := by omega
  have hd : ∀ q, D.ptDiag h q ≠ 0 := fun q => Formalism.FourierDecayAlt.P.JCTx6.Link2.ptScal_ne h hab q q.2
  have hT := p.hT
  obtain ⟨R, hR⟩ := hF.2.1

  have hOm : LevelPointCoordinates.mLev P (D.ptSize h) hj τ γ ∈
      JF.Om P.k (P.r - D.ptSize h) (p.T.bs (D.ptSize h)).z (p.T.bs (D.ptSize h)).z' := by
    have h2 := Formalism.FourierDecayAlt.P.PBH.om_cast (by omega : P.r - (D.ptSize h + 1) + 1 = P.r - D.ptSize h) _ _ _
      (Formalism.FourierDecayAlt.P.PBH.mcOm P.k (P.r - (D.ptSize h + 1)) (p.T.bs (D.ptSize h + 1)).z (p.T.bs (D.ptSize h + 1)).z'
        (p.T.bs (D.ptSize h + 1)).z_mem (p.T.bs (D.ptSize h + 1)).z'_mem τ hτ γ hγ hΩ)
    rw [Formalism.FourierDecayAlt.P.PBH.asm_castM_castM, Formalism.FourierDecayAlt.P.PBH.asm_castV_castV, Formalism.FourierDecayAlt.P.PBH.asm_castV_castV] at h2
    rw [Formalism.FourierDecayAlt.P.PBH.levTower_bs_z_eq_castV_liftVec p.T _ hj, Formalism.FourierDecayAlt.P.PBH.levTower_bs_z'_eq_castV_liftVec p.T _ hj]
    exact h2
  have hHc : ContinuousOn (D.uwG P.k P.r p.T.base.z p.T.base.z' F (D.ptSize h) hjr w e)
      {x | x ∈ B.GV P.k P.r ∧ Dmin P.k P.r p.T.base.z p.T.base.z' x ⟨D.ptSize h, by omega⟩ ≠ 0} :=
    Formalism.FourierDecayAlt.P.PBG.contOn_of_loc (S := Formalism.FourierDecayAlt.P.PBG.Sd p.T.base.z p.T.base.z' (D.ptSize h) hjr)
      (fun x hx hxG => Formalism.FourierDecayAlt.P.PBG.uwG_mem (E := Wq →L[ℂ] Wp) p.T.base.z p.T.base.z' (D.ptSize h) hjr hF.1 w e
        x hx hxG)
  have hR' := Formalism.FourierDecayAlt.P.PBG.uwG_supp p.T.base.z p.T.base.z' F R hR (D.ptSize h) hjr w e
  have key := jfSliceIntN e0 hj1 (D.ptPerm h) (D.ptDiag h) hd (p.T.bs (D.ptSize h)) p.T.base
    (p.T.z_lev _ hjr) (p.T.z'_lev _ hjr) (p.T.π'_lev _ hjr) (hT _ hjr).2.1
    (Formalism.FourierDecayAlt.P.PBM.tower_haarW' p.T hT _ hjr e0) (hT _ hjr).2.2 (hT 0 (Nat.zero_le _)).2.2
    (LevelPointCoordinates.mLev P (D.ptSize h) hj τ γ) hOm _ hHc R hR'
  have hs := slice_eq p.T.base.z p.T.base.z' (D.uwG P.k P.r p.T.base.z p.T.base.z' F (D.ptSize h) hjr w e) h hjr
    rfl e0
  show B.JF (p.T.bs (D.ptSize h)) (D.castF _ (D.sliceAt P.k P.r p.T.base.z p.T.base.z'
    (D.uwG P.k P.r p.T.base.z p.T.base.z' F (D.ptSize h) hjr w e) h)) (LevelPointCoordinates.mLev P (D.ptSize h) hj τ γ) = _
  rw [hs, key]
  congr 1
  funext v
  have hZ : IsUnit (lhOf (D.ptPerm h) v * U.hMat (D.ptPerm h) (D.ptDiag h)).det := by
    rw [Matrix.det_mul]
    exact (lh_unit _ v).mul (Ne.isUnit (Formalism.FourierDecayAlt.P.Ux10.det_hMat_ne _ _ hd))
  have hz : PBQ.zxH h (D.ptSize h) rfl v = lhOf (D.ptPerm h) v * U.hMat (D.ptPerm h) (D.ptDiag h) := by
    simp only [PBQ.zxH, finCongr_refl, Matrix.reindex_refl_refl]
  have hpt : D.castM e0 (U.mMap P.k (D.ptSize h) (P.r - D.ptSize h)
      (lhOf (D.ptPerm h) v * U.hMat (D.ptPerm h) (D.ptDiag h)) (LevelPointCoordinates.mLev P (D.ptSize h) hj τ γ)) =
      LevelPointCoordinates.x0 P.k P.r (D.ptSize h) hj (PBQ.zxH h (D.ptSize h) rfl v) τ γ := by
    rw [hz]
    exact pt_eq hj _ hZ τ hτ γ e0 _
  rw [hpt]
  have hy := (hPt v).2 τ hτ
  have hyG : LevelPointCoordinates.x0 P.k P.r (D.ptSize h) hj (PBQ.zxH h (D.ptSize h) rfl v) τ γ ∈ B.GV P.k P.r :=
    LevelPointCoordinates.x0_GV hj (hPt v).1 hτ hγ
  have hpw := hW P.k (D.ptSize h) (P.r - D.ptSize h) P.r Wp Wq (p.T.bs (D.ptSize h)) p.T.base e0
    (p.T.z_lev _ hjr).symm (D.ptSize h) hjr F {g | B.gN g ≤ R} (fun g hg _ => hF.1 g hg)
    (Formalism.FourierDecayAlt.P.PBE.isCompact_gN_le _ _ R) (fun g hg hgC => by
      by_contra hne
      exact hgC (hR g hg hne))
    (PBQ.domP P.k P.r (D.ptSize h) p.T.base.z p.T.base.z') (PBQ.isOpen_domP _ _ _ _ _)
    (fun g hg => hg.1 ⟨D.ptSize h, by omega⟩ le_rfl hjr)
    (hPr Wp Wq P p (D.ptSize h) hjr _ (Formalism.FourierDecayAlt.P.PBE.isCompact_gN_le _ _ R)) w e _ hy hyG
  unfold PBQ.ellH CutHB.phf
  rw [_root_.smul_apply, ContinuousLinearMap.id_apply, ← hpw]
  rfl

end Formalism.FourierDecayAlt.P.SliceIntegralLemmas

namespace Formalism.FourierDecayAlt.P.SliceIntegralLemmas

end Formalism.FourierDecayAlt.P.SliceIntegralLemmas

namespace Formalism.FourierDecayAlt.P.SliceIntegralLemmas

theorem side0Pos_of'' (hPr : ProperLeftVariablesDomain) : CutHB.Side0Pos :=
  side0Pos_of Formalism.FourierDecayAlt.P.letters_pass_partial_bessel hPr CutHB.pts

end Formalism.FourierDecayAlt.P.SliceIntegralLemmas
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.Side1PosOf
section
open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.LevelPointCoordinates

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.PBQ

theorem side1Pos_of (hC : CutOffStep) (hE : CutOffExists) (h0 : CutHB.Side0Pos) (hW : PartialBesselProperness.PbWords)
    (hPr : PBQ.ProperDomP) : CutHB.Side1Pos := by
  intro Wp Wq _ _ _ _ _ _ P p F j hj w h hh γ hj1 hF hw hγ hΩ t ht e
  have ht0 : t ≠ 0 := (ht.1 (1, t) (List.mem_append_right _ (List.mem_singleton_self _))).2
  obtain ⟨Fc, hFc, hag⟩ := hE Wp Wq P p F j hj w h hh hF hw t ht e
  rw [hC Wp Wq P p F j hj w h hh γ hF hw hγ hΩ t ht e Fc hFc hag]
  rw [h0 Wp Wq P p Fc j hj [] h hh γ hj1 hFc ⟨fun a => a.elim0, fun a => a.elim0⟩ hγ hΩ (fun a => a.elim0) t ht0]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  show ellH h v (CutHB.phf p Fc j hj [] h hh.2 γ v (fun a => a.elim0) t) = ellH h v _
  congr 1
  have hpt := CutHB.pts Wp Wq P p j hj h hh γ hγ hΩ v
  have hyD := hpt.2 t ht0
  have hyG := x0_GV hj hpt.1 ht0 hγ

  obtain ⟨R, hR⟩ := hF.2.1
  set Cs : Set (B.Mat P.k P.r) := {g | B.gN g ≤ R} with hCs
  have hCc : IsCompact Cs := Formalism.FourierDecayAlt.P.PBE.isCompact_gN_le P.k P.r R
  have e' : j + (P.r - j) = P.r := by omega
  have hz : p.T.base.z = D.castV e' (liftVec P.k j (P.r - j) (p.T.bs j).z) := (p.T.z_lev j (by omega)).symm
  have hPW := hW P.k j (P.r - j) P.r Wp Wq (p.T.bs j) p.T.base e' hz (j + 1) hj F Cs (fun g hg _ => hF.1 g hg) hCc
    (fun g hg hgC => by
      by_contra hne
      exact hgC (hR g hg hne))
    (domP P.k P.r j p.T.base.z p.T.base.z') (isOpen_domP _ _ _ _ _)
    (fun g hg => hg.1 ⟨j + 1, by omega⟩ (show j ≤ j + 1 by omega) (show j + 1 ≤ P.r by omega))
    (hPr Wp Wq P p j (by omega) Cs hCc) w e _ hyD hyG
  show pbT p j (by omega) Fc (x0 P.k P.r j hj (zxH h j hh.2 v) t γ) =
    D.uwG P.k P.r p.T.base.z p.T.base.z' (pbT p j (by omega) F) (j + 1) hj w e (x0 P.k P.r j hj (zxH h j hh.2 v) t γ)
  unfold pbT
  rw [hPW]
  have hDv : Dmin P.k P.r p.T.base.z p.T.base.z' (x0 P.k P.r j hj (zxH h j hh.2 v) t γ) ⟨j + 1, by omega⟩ = aVal h t := by
    rw [(CutHL.leading_minors_at_base_point P.k P.r j hj p.T.base.z p.T.base.z' (zxH h j hh.2 v) t γ hpt.1 ht0 hγ).2, zxH_det h j hh v]
    rfl
  exact pbT_agree P p j hj (aVal h t) Fc _ (fun g _ hg => hag g hg) _ hyG hDv

end Formalism.FourierDecayAlt.P.LevelPointCoordinates
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothTruncationInduction
section
namespace Formalism.FourierDecayAlt.P

theorem smooth_truncation_induction : Formalism.FourierDecayAlt.P.LevelPointCoordinates.CutOffStep := by
  intro Wp Wq _ _ _ _ _ _ P p F j hj w h hh γ _ _ hγ hΩ t ht e Fc hFc hag
  exact Formalism.FourierDecayAlt.P.CutHB.truncation_off_induction Wp Wq P p F j hj w h hh γ hγ hΩ t ht e Fc hFc hag

theorem smooth_truncation_exists : Formalism.FourierDecayAlt.P.LevelPointCoordinates.CutOffExists := by
  intro Wp Wq _ _ _ _ _ _ P p F j hj w h hh hF _ t ht e
  exact Formalism.FourierDecayAlt.P.CutHB.truncation_off_exists_formula Wp Wq P p F j hj w h hh hF t ht e

end Formalism.FourierDecayAlt.P
end

