import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0070
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0046
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrechetContinuousContinuousOnOrbitHasDerivAt
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle0001
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0077
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0131
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0081
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0075
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0186
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsPrimeIdempotentIntegralAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0103
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0190
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0175
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFrameFixingIsometrySplitRowLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolEqOfAedisjoint
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0191

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CwContIntegralComm
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.CWIntegral

open PI.UpqRep GlobalTheory.CWDeriv

theorem exists_functional {S E : Type} [AddCommGroup S] [Module ℂ S] [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : S →ₗ[ℂ] E) (φ : S →ₗ[ℂ] ℂ) (C : ℝ) (h : ∀ s, ‖φ s‖ ≤ C * ‖T s‖) :
    ∃ Λ : E →L[ℂ] ℂ, ∀ s, Λ (T s) = φ s := by
  have hker : LinearMap.ker T ≤ LinearMap.ker φ := by
    intro s hs
    rw [LinearMap.mem_ker] at hs ⊢
    have h1 := h s
    rw [hs, norm_zero, mul_zero] at h1
    exact norm_le_zero_iff.mp h1
  let ψ : LinearMap.range T →ₗ[ℂ] ℂ :=
    ((LinearMap.ker T).liftQ φ hker).comp T.quotKerEquivRange.symm.toLinearMap
  have hψT : ∀ s, ψ ⟨T s, LinearMap.mem_range_self T s⟩ = φ s := by
    intro s
    have hq : T.quotKerEquivRange.symm ⟨T s, LinearMap.mem_range_self T s⟩ = (LinearMap.ker T).mkQ s :=
      LinearMap.quotKerEquivRange_symm_apply_image T s _
    simp only [ψ, LinearMap.comp_apply, LinearEquiv.coe_coe, hq, Submodule.mkQ_apply, Submodule.liftQ_apply]
  have hbd : ∀ y : LinearMap.range T, ‖ψ y‖ ≤ max C 0 * ‖y‖ := by
    rintro ⟨y, s, rfl⟩
    rw [hψT]
    calc ‖φ s‖ ≤ C * ‖T s‖ := h s
      _ ≤ max C 0 * ‖T s‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  obtain ⟨Λ, hΛ, -⟩ := exists_extension_norm_eq (LinearMap.range T) (ψ.mkContinuous (max C 0) hbd)
  refine ⟨Λ, fun s => ?_⟩
  have := hΛ ⟨T s, LinearMap.mem_range_self T s⟩
  rw [LinearMap.mkContinuous_apply, hψT] at this
  exact this

variable {k r : ℕ}

def linOn (R : Rep k r) {V : Type} [AddCommGroup V] [Module ℂ V] (B : R.H → V)
    (ha : ∀ v ∈ R.sm, ∀ w ∈ R.sm, B (v + w) = B v + B w) (hs : ∀ (a : ℂ), ∀ v ∈ R.sm, B (a • v) = a • B v) :
    R.smSub →ₗ[ℂ] V where
  toFun v := B v
  map_add' v w := ha _ v.2 _ w.2
  map_smul' a v := hs a _ v.2

theorem dsigW_smul {R : Rep k r} (hD : DerFacts R) (W : List (Mx k r)) (hW : ∀ X ∈ W, InLieHpk k r X)
    (a : ℂ) (v : R.H) (hv : v ∈ R.sm) :
    dsigW (k := k) (r := r) R.σ W (a • v) = a • dsigW (k := k) (r := r) R.σ W v := by
  revert hW
  induction W with
  | nil => intro _; rfl
  | cons X W ih =>
    intro hW
    have hW' : ∀ Y ∈ W, InLieHpk k r Y := fun Y hY => hW Y (List.mem_cons_of_mem X hY)
    have hX : InLieHpk k r X := hW X (List.mem_cons_self ..)
    show dsig (k := k) (r := r) R.σ X (dsigW (k := k) (r := r) R.σ W (a • v)) =
      a • dsig (k := k) (r := r) R.σ X (dsigW (k := k) (r := r) R.σ W v)
    rw [ih hW']
    have hv' := dsigW_mem hD W hW' v hv
    have hd := ((hD X hX).1 _ hv').2.const_smul a
    have hd' : HasDerivAt (fun t : ℝ => R.σ (NormedSpace.exp ((t : ℂ) • X)) (a • dsigW (k := k) (r := r) R.σ W v))
        (a • dsig (k := k) (r := r) R.σ X (dsigW (k := k) (r := r) R.σ W v)) 0 := by
      simpa only [map_smul, Pi.smul_def] using hd
    exact hd'.deriv

theorem dsigW_add {R : Rep k r} (hD : DerFacts R) (W : List (Mx k r)) (hW : ∀ X ∈ W, InLieHpk k r X)
    (v : R.H) (hv : v ∈ R.sm) (w : R.H) (hw : w ∈ R.sm) :
    dsigW (k := k) (r := r) R.σ W (v + w) =
      dsigW (k := k) (r := r) R.σ W v + dsigW (k := k) (r := r) R.σ W w := by
  revert hW
  induction W with
  | nil => intro _; rfl
  | cons X W ih =>
    intro hW
    have hW' : ∀ Y ∈ W, InLieHpk k r Y := fun Y hY => hW Y (List.mem_cons_of_mem X hY)
    have hX : InLieHpk k r X := hW X (List.mem_cons_self ..)
    show dsig (k := k) (r := r) R.σ X (dsigW (k := k) (r := r) R.σ W (v + w)) =
      dsig (k := k) (r := r) R.σ X (dsigW (k := k) (r := r) R.σ W v) +
        dsig (k := k) (r := r) R.σ X (dsigW (k := k) (r := r) R.σ W w)
    rw [ih hW']
    have hv' := dsigW_mem hD W hW' v hv
    have hw' := dsigW_mem hD W hW' w hw
    have hd := ((hD X hX).1 _ hv').2.add ((hD X hX).1 _ hw').2
    have hd' : HasDerivAt (fun t : ℝ => R.σ (NormedSpace.exp ((t : ℂ) • X))
        (dsigW (k := k) (r := r) R.σ W v + dsigW (k := k) (r := r) R.σ W w))
        (dsig (k := k) (r := r) R.σ X (dsigW (k := k) (r := r) R.σ W v) +
          dsig (k := k) (r := r) R.σ X (dsigW (k := k) (r := r) R.σ W w)) 0 := by
      simpa only [map_add, Pi.add_def] using hd
    exact hd'.deriv

theorem dsigW_integral {R : Rep k r} (hD : DerFacts R) (W : List (Mx k r)) (hW : ∀ X ∈ W, InLieHpk k r X)
    {X : Type} [MeasurableSpace X] (μ : Measure X) (f : X → R.H) (hf : ∀ x, f x ∈ R.sm)
    (hi : Integrable f μ) (hi' : Integrable (fun x => dsigW (k := k) (r := r) R.σ W (f x)) μ)
    (hu : (∫ x, f x ∂μ) ∈ R.sm) :
    dsigW (k := k) (r := r) R.σ W (∫ x, f x ∂μ) = ∫ x, dsigW (k := k) (r := r) R.σ W (f x) ∂μ := by
  have hmem : ∀ x, dsigW (k := k) (r := r) R.σ W (f x) ∈ R.smSub := fun x => dsigW_mem hD W hW _ (hf x)
  have hcl : ((R.smSub.topologicalClosure : Submodule ℂ R.H) : Set R.H) = closure R.sm :=
    Submodule.topologicalClosure_coe _
  have hy : (∫ x, dsigW (k := k) (r := r) R.σ W (f x) ∂μ) ∈ R.smSub.topologicalClosure := by
    rw [← Submodule.orthogonal_orthogonal_eq_closure, Submodule.mem_orthogonal]
    intro z hz
    rw [← integral_inner hi']
    refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun x => ?_)
    exact Submodule.inner_left_of_mem_orthogonal (hmem x) hz
  have hd : dsigW (k := k) (r := r) R.σ W (∫ x, f x ∂μ) ∈ R.smSub := dsigW_mem hD W hW _ hu
  refine sub_eq_zero.mp (eq_zero_of_closure ?_ ?_)
  · rw [← hcl]
    exact Submodule.sub_mem _ (R.smSub.le_topologicalClosure hd) hy
  · intro w hw
    obtain ⟨w', hw'⟩ := dsigW_adjoint hD W hW w hw
    rw [inner_sub_right, hw' _ hu, ← integral_inner hi, ← integral_inner hi', sub_eq_zero]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    exact (hw' _ (hf x)).symm

end GlobalTheory.CWIntegral

namespace GlobalTheory

open PI.UpqRep GlobalTheory.CWDeriv GlobalTheory.CWIntegral

theorem cwCont_integral_comm : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] (Bm : R.H → V), (∀ v ∈ R.sm, ∀ w ∈ R.sm, Bm (v + w) = Bm v + Bm w) → (∀ (a : ℂ), ∀ v ∈ R.sm, Bm (a • v) = a • Bm v) → PI.BesselMapUniq.IsCWCont (k := k) (r := r) R.σ Bm → ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] (μ : Measure X) [IsFiniteMeasure μ] (κ : X → Mx k r) (p : X → ℂ), Continuous κ → (∀ x, κ x ∈ GG k r) → Continuous p → ∀ v ∈ R.sm, (∫ x, p x • R.σ (κ x) v ∂μ) ∈ R.sm → Bm (∫ x, p x • R.σ (κ x) v ∂μ) = ∫ x, p x • Bm (R.σ (κ x) v) ∂μ := by
  intro hKS k r ε mu R hR V indexVFirst indexVSecond indexVThird indexVFourth Bm hadd hsmul hcw X iX1 iX2 iX3 iX4 iX5 μ iμ κ p hκ hκG hp v hv hu
  have hD : DerFacts R := fun Y hY =>
    ⟨(GlobalTheory.T.derivedAction_discreteSeries_properties hKS k r ε mu R hR Y hY).1, (GlobalTheory.T.derivedAction_discreteSeries_properties hKS k r ε mu R hR Y hY).2.2.2.2⟩
  have hσ : ∀ x, R.σ (κ x) v ∈ R.sm := fun x => (rep_basic_of_isDS hKS k r ε mu R hR).2.2.2.1 _ (hκG x) v hv
  have hf : ∀ x, p x • R.σ (κ x) v ∈ R.sm := fun x => R.smSub.smul_mem (p x) (hσ x)
  have hint : ∀ {E : Type} [NormedAddCommGroup E] (g : X → E), Continuous g → Integrable g μ :=
    fun g hg => hg.integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset (isClosed_tsupport g) (Set.subset_univ _))
  have hcW : ∀ W : List (Mx k r), (∀ Y ∈ W, InLieHpk k r Y) →
      Continuous (fun x => PI.UpqRep.dsigW (k := k) (r := r) R.σ W (R.σ (κ x) v)) := fun W hW =>
    (smoothOnH_continuousOn (dsigW_orbit_smooth hR hD hv W hW)).comp_continuous hκ hκG
  have hBc : Continuous (fun x => Bm (R.σ (κ x) v)) :=
    (cwCont_continuousOn_hasDerivAt hKS k r ε mu R hR V Bm hadd hsmul hcw v hv).1.comp_continuous hκ hκG
  obtain ⟨C, Ws, hWs, hB⟩ := hcw
  have hWi : ∀ i : Fin Ws.length, ∀ Y ∈ Ws.get i, InLieHpk k r Y := fun i => hWs _ (List.get_mem Ws i)
  let T : R.smSub →ₗ[ℂ] (Fin Ws.length → R.H) :=
    linOn R (fun u i => PI.UpqRep.dsigW (k := k) (r := r) R.σ (Ws.get i) u)
      (fun a ha b hb => funext fun i => dsigW_add hD _ (hWi i) a ha b hb)
      (fun c a ha => funext fun i => dsigW_smul hD _ (hWi i) c a ha)
  refine ext_inner_left ℂ (fun e => ?_)
  let φ : R.smSub →ₗ[ℂ] ℂ := (innerSL ℂ e : V →L[ℂ] ℂ).toLinearMap.comp (linOn R Bm hadd hsmul)
  have hφ : ∀ s, φ s = ⟪e, Bm s⟫_ℂ := fun s => rfl
  have hbound : ∀ s, ‖φ s‖ ≤ (‖e‖ * (|C| * Ws.length)) * ‖T s‖ := by
    intro s
    have h1 : ‖Bm s‖ ≤ C * (Ws.map fun w => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ w s‖).sum := hB s s.2
    have h2 : (Ws.map fun w => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ w s‖).sum ≤ Ws.length * ‖T s‖ := by
      have h3 := List.sum_le_card_nsmul (Ws.map fun w => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ w s‖) ‖T s‖
        (by
          intro y hy
          obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hy
          obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hw
          exact norm_le_pi_norm (T s) i)
      rwa [List.length_map, nsmul_eq_mul] at h3
    have h0 : 0 ≤ (Ws.map fun w => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ w s‖).sum :=
      List.sum_nonneg (fun y hy => by
        obtain ⟨w, -, rfl⟩ := List.mem_map.mp hy
        exact norm_nonneg _)
    have h4 : ‖Bm s‖ ≤ |C| * (Ws.length * ‖T s‖) :=
      h1.trans ((mul_le_mul_of_nonneg_right (le_abs_self C) h0).trans
        (mul_le_mul_of_nonneg_left h2 (abs_nonneg C)))
    rw [hφ]
    calc ‖⟪e, Bm s⟫_ℂ‖ ≤ ‖e‖ * ‖Bm s‖ := norm_inner_le_norm _ _
      _ ≤ ‖e‖ * (|C| * (Ws.length * ‖T s‖)) := mul_le_mul_of_nonneg_left h4 (norm_nonneg e)
      _ = (‖e‖ * (|C| * Ws.length)) * ‖T s‖ := by ring
  obtain ⟨Λ, hΛ⟩ := exists_functional T φ _ hbound
  let F : X → (Fin Ws.length → R.H) := fun x i =>
    p x • PI.UpqRep.dsigW (k := k) (r := r) R.σ (Ws.get i) (R.σ (κ x) v)
  have hFi : Integrable F μ := hint F (continuous_pi fun i => hp.smul (hcW _ (hWi i)))
  have hTu : T ⟨_, hu⟩ = ∫ x, F x ∂μ := by
    funext i
    have hpi := (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin Ws.length => R.H) i).integral_comp_comm hFi
    simp only [ContinuousLinearMap.proj_apply] at hpi
    rw [← hpi]
    show PI.UpqRep.dsigW (k := k) (r := r) R.σ (Ws.get i) (∫ x, p x • R.σ (κ x) v ∂μ) = ∫ x, F x i ∂μ
    have hi0 : Integrable (fun x => p x • R.σ (κ x) v) μ := hint _ (hp.smul (hcW [] (by simp)))
    have hi1 : Integrable (fun x => PI.UpqRep.dsigW (k := k) (r := r) R.σ (Ws.get i) (p x • R.σ (κ x) v)) μ :=
      (hint _ (hp.smul (hcW _ (hWi i)))).congr
        (Filter.Eventually.of_forall fun x => (dsigW_smul hD _ (hWi i) (p x) _ (hσ x)).symm)
    rw [dsigW_integral hD _ (hWi i) μ _ hf hi0 hi1 hu]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => dsigW_smul hD _ (hWi i) (p x) _ (hσ x))
  calc ⟪e, Bm (∫ x, p x • R.σ (κ x) v ∂μ)⟫_ℂ = φ ⟨_, hu⟩ := (hφ ⟨_, hu⟩).symm
    _ = Λ (T ⟨_, hu⟩) := (hΛ ⟨_, hu⟩).symm
    _ = Λ (∫ x, F x ∂μ) := by rw [hTu]
    _ = ∫ x, Λ (F x) ∂μ := (Λ.integral_comp_comm hFi).symm
    _ = ∫ x, ⟪e, p x • Bm (R.σ (κ x) v)⟫_ℂ ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        have hF : F x = p x • T ⟨_, hσ x⟩ := rfl
        show Λ (F x) = ⟪e, p x • Bm (R.σ (κ x) v)⟫_ℂ
        rw [hF, map_smul, hΛ, hφ, inner_smul_right, smul_eq_mul]
    _ = ⟪e, ∫ x, p x • Bm (R.σ (κ x) v) ∂μ⟫_ℂ := integral_inner (hint _ (hp.smul hBc)) e

end GlobalTheory

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsChoiceOfIdem
section
open Formalism.MainNotions.S GlobalTheory.RowLev GlobalTheory.RowLev.Inhab NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.RowIndex

variable {I : AutInst}

theorem sig_sig (z : I.E ⊗[I.F] Af I.F) : sigR I.cm.sig (Af I.F) (sigR I.cm.sig (Af I.F) z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    show star (star a) ⊗ₜ b = _
    rw [star_star]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem sig_hAf (x y : Fin I.n → I.E ⊗[I.F] Af I.F) : sigR I.cm.sig (Af I.F) (hAf I x y) = hAf I y x := by
  unfold hAf hform
  simp only [map_sum, map_mul, sig_sig]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h : star (I.J j i) = I.J i j := congrFun (congrFun I.J_herm i) j
  have h2 : sigR I.cm.sig (Af I.F) (I.J.map (inclE (F := I.F) (Af I.F)) j i) =
      I.J.map (inclE (F := I.F) (Af I.F)) i j := by
    rw [Matrix.map_apply, Matrix.map_apply, ← h]
    rfl
  rw [h2]
  ring

def sigI (I : AutInst) : IntAf I.F I.E →+* IntAf I.F I.E :=
  ((sigR I.cm.sig (Af I.F)).comp (IntAf I.F I.E).subtype).codRestrict _ fun z =>
    (intAf_approx_inter_unit_conj I 1 le_rfl).2.2.2 z.1 z.2

theorem coe_sigI (z : IntAf I.F I.E) : (sigI I z : I.E ⊗[I.F] Af I.F) = sigR I.cm.sig (Af I.F) z := rfl

theorem sigI_sigI (z : IntAf I.F I.E) : sigI I (sigI I z) = z := Subtype.ext (sig_sig _)

def hI (x y : I.Lf) : IntAf I.F I.E :=
  ⟨hAf I x y, (GlobalTheory.AdelicLattice.adelicLattice_selfDual I y).1 y.2 x x.2⟩

theorem coe_hI (x y : I.Lf) : (hI x y : I.E ⊗[I.F] Af I.F) = hAf I x y := rfl

theorem sigI_hI (x y : I.Lf) : sigI I (hI x y) = hI y x := Subtype.ext (sig_hAf _ _)

theorem hI_add (x y z : I.Lf) : hI x (y + z) = hI x y + hI x z := by
  apply Subtype.ext
  show hAf I x (y.1 + z.1) = hAf I x y + hAf I x z
  simp only [hAf, hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hI_smul (a : IntAf I.F I.E) (x y : I.Lf) : hI x (a • y) = a * hI x y := by
  apply Subtype.ext
  show hAf I x ((a : I.E ⊗[I.F] Af I.F) • y.1) = a * hAf I x y
  unfold hAf hform
  simp only [Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => mul_left_comm _ _ _

theorem ker_of_card {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] {p N : ℕ} (hp : p ≠ 0)
    (r : R →+* ZMod p) (c : M →ₛₗ[r] (Fin N → ZMod p)) (hs : Function.Surjective c)
    (hc : Nat.card (M ⧸ (RingHom.ker r • (⊤ : Submodule R M))) = p ^ N) (y : M) :
    c y = 0 ↔ y ∈ RingHom.ker r • (⊤ : Submodule R M) := by
  set S : Submodule R M := RingHom.ker r • (⊤ : Submodule R M) with hS
  have hle : S ≤ LinearMap.ker c := fun y h => by
    refine Submodule.smul_induction_on h (fun a ha x _ => ?_) (fun x y hx hy => add_mem hx hy)
    rw [LinearMap.mem_ker, map_smulₛₗ, RingHom.mem_ker.1 ha, zero_smul]
  refine ⟨fun h => ?_, fun h => hle h⟩
  haveI : NeZero p := ⟨hp⟩
  haveI : Finite (M ⧸ S) := Nat.finite_of_card_ne_zero (by rw [hc]; exact pow_ne_zero _ hp)
  have hb : Function.Bijective (S.liftQ c hle) := by
    rw [Nat.bijective_iff_surjective_and_card]
    refine ⟨fun t => ?_, by rw [hc, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]⟩
    obtain ⟨y, rfl⟩ := hs t
    exact ⟨S.mkQ y, rfl⟩
  rw [← Submodule.Quotient.mk_eq_zero]
  apply hb.1
  rw [map_zero]
  exact h

theorem exists_frame_of_dual {N p : ℕ} {w : HeightOneSpectrum (𝓞 I.E)} (hn : I.n = N) (hp : p.Prime)
    (hw : Ideal.absNorm w.asIdeal = p) (r : IntAf I.F I.E →+* ZMod p)
    (hr : ∀ a, r (psi I.F I.E a) = 0 ↔ a ∈ w.asIdeal) (b b' : Fin N → I.Lf)
    (hb : ∀ i j, r (hI (b' i) (b j)) = if i = j then 1 else 0) :
    ∃ fr : PlFrame I N p w, fr.r = r ∧ ∀ y i, fr.c y i = r (hI (b' i) y) := by
  let c : I.Lf →ₛₗ[r] (Fin N → ZMod p) :=
    { toFun := fun y i => r (hI (b' i) y)
      map_add' := fun x y => funext fun i => by rw [hI_add, map_add]; rfl
      map_smul' := fun a y => funext fun i => by rw [hI_smul, map_mul]; rfl }
  have hs : Function.Surjective c := fun t => by
    choose s hs using ZMod.ringHom_surjective r
    refine ⟨∑ j, s (t j) • b j, ?_⟩
    rw [map_sum]
    funext i
    have : ∀ j, c (b j) i = if i = j then 1 else 0 := fun j => hb i j
    simp [map_smulₛₗ, hs, this]
  have hk := ker_eq_extId hp.ne_zero r hr
  have hc := GlobalTheory.AdelicLattice.card_quot_extId I p w hp hw
  rw [← hk] at hc
  replace hc := hc.trans (congrArg (p ^ ·) hn)
  refine ⟨⟨r, fun a _ => hr a, c, hs, fun y => ?_⟩, rfl, fun _ _ => rfl⟩
  rw [ker_of_card hp.ne_zero r c hs hc, hk]
  exact Submodule.mem_smul_top_iff _ _ y

theorem conj_reduction {p : ℕ} {w w' : HeightOneSpectrum (𝓞 I.E)} (hc : IsConj I w w')
    (r : IntAf I.F I.E →+* ZMod p) (hr : ∀ a, r (psi I.F I.E a) = 0 ↔ a ∈ w.asIdeal) (a : 𝓞 I.E) :
    (r.comp (sigI I)) (psi I.F I.E a) = 0 ↔ a ∈ w'.asIdeal := by
  let st : 𝓞 I.E →+* 𝓞 I.E := RingOfIntegers.mapRingHom (starRingEnd I.E)
  have hst : ∀ a : 𝓞 I.E, (st a : I.E) = star (a : I.E) := fun a => rfl
  have e : sigI I (psi I.F I.E a) = psi I.F I.E (st a) := rfl
  rw [RingHom.comp_apply, e, hr]
  exact hc (st a) a (by rw [hst, star_star])

theorem mem_span_iff {N p : ℕ} {w : HeightOneSpectrum (𝓞 I.E)} (fr : PlFrame I N p w) (S : Set I.Lf) (y : I.Lf) :
    (∃ s ∈ Submodule.span (IntAf I.F I.E) S, y - s ∈ extId I w.asIdeal • (⊤ : Submodule (IntAf I.F I.E) I.Lf)) ↔
      fr.c y ∈ Submodule.span (ZMod p) (fr.c '' S) := by
  haveI : RingHomSurjective fr.r := ⟨ZMod.ringHom_surjective _⟩
  rw [← Submodule.map_span, Submodule.mem_map]
  refine exists_congr fun s => and_congr_right fun _ => ?_
  rw [← fr.c_eq_zero_iff, map_sub, sub_eq_zero, eq_comm]

theorem glue_mod {R M ι : Type} [CommRing R] [AddCommGroup M] [Module R M] (U : Finset ι) (𝔞 : ι → Ideal R)
    (ε : ι → R) (h2 : ∀ u, 1 - ε u ∈ 𝔞 u) (h3 : ∀ u v, u ≠ v → ε u ∈ 𝔞 v) (T : Submodule R M) (y : M) (s : ι → M)
    (hs : ∀ u ∈ U, s u ∈ T) (hs' : ∀ u ∈ U, y - s u ∈ 𝔞 u • (⊤ : Submodule R M)) :
    ∃ t ∈ T, ∀ u ∈ U, y - t ∈ 𝔞 u • (⊤ : Submodule R M) := by
  refine ⟨∑ v ∈ U, ε v • s v, sum_mem fun v hv => T.smul_mem _ (hs v hv), fun u hu => ?_⟩
  rw [← Finset.add_sum_erase _ _ hu]
  have e : y - (ε u • s u + ∑ v ∈ U.erase u, ε v • s v) =
      (y - s u) + (1 - ε u) • s u - ∑ v ∈ U.erase u, ε v • s v := by
    rw [sub_smul, one_smul]; abel
  rw [e]
  exact sub_mem (add_mem (hs' u hu) (Submodule.smul_mem_smul (h2 u) Submodule.mem_top))
    (sum_mem fun v hv => Submodule.smul_mem_smul (h3 v u (Finset.ne_of_mem_erase hv)) Submodule.mem_top)

theorem mem_mod_iff {m : ℕ} (hm : 1 ≤ m) (hrad : (Ideal.span {(m : 𝓞 I.E)}).IsRadical)
    (T : Submodule (IntAf I.F I.E) I.Lf) (y : I.Lf) :
    (∃ s ∈ T, ∃ z ∈ I.Lf, y.1 = s.1 + (m : I.E ⊗[I.F] Af I.F) • z) ↔
      ∀ u : HeightOneSpectrum (𝓞 I.E), (m : 𝓞 I.E) ∈ u.asIdeal →
        ∃ s ∈ T, y - s ∈ extId I u.asIdeal • (⊤ : Submodule (IntAf I.F I.E) I.Lf) := by
  have crt := GlobalTheory.RowLev.SqfCrt.mem_extId_smul_forall_iff I m hm hrad
  constructor
  · rintro ⟨s, hs, z, hz, e⟩ u hu
    refine ⟨s, hs, (Submodule.mem_smul_top_iff _ _ _).2 ?_⟩
    exact (crt _ (y - s).2).2 ⟨z, hz, by rw [Submodule.coe_sub, e, add_sub_cancel_left]⟩ u hu
  · intro H
    have h0 : Ideal.span {(m : 𝓞 I.E)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact_mod_cast (by omega : m ≠ 0)
    have hfin : {u : HeightOneSpectrum (𝓞 I.E) | (m : 𝓞 I.E) ∈ u.asIdeal}.Finite :=
      (Ideal.finite_factors h0).subset fun u hu => Ideal.dvd_span_singleton.2 hu
    choose! s hs hs' using H
    choose ε h1 h2 h3 h4 using GlobalTheory.RowLev.exists_prime_idempotent I
    obtain ⟨t, hT, key⟩ := glue_mod hfin.toFinset (fun u => extId I u.asIdeal) ε h2 (fun u v h => h3 u v h.symm) T y s
      (fun v hv => hs v (hfin.mem_toFinset.1 hv)) (fun v hv => hs' v (hfin.mem_toFinset.1 hv))
    obtain ⟨z, hz, e⟩ := (crt _ (y - t).2).1
      fun u hu => (Submodule.mem_smul_top_iff _ _ _).1 (key u (hfin.mem_toFinset.2 hu))
    have e' : y.1 - t.1 = (m : I.E ⊗[I.F] Af I.F) • z := e
    exact ⟨t, hT, z, hz, sub_eq_iff_eq_add'.1 e'⟩

theorem entry_eq {N p : ℕ} {w : HeightOneSpectrum (𝓞 I.E)} (fr : PlFrame I N p w) (b : Fin N → I.Lf)
    (hb : ∀ j, fr.c (b j) = Pi.single j 1) {x : I.Gf} (hx : x ∈ I.Kset) {M : Matrix (Fin N) (Fin N) (ZMod p)}
    (hM : fr.ActsAs x M) (i j : Fin N) : M i j = fr.c (latEnd hx (b j)) i := by
  have := hM (b j) (mulVec_mem hx (b j).2)
  rw [hb, Matrix.mulVec_single_one] at this
  exact (congrFun this i).symm

theorem hI_latEnd {x : I.Gf} (hx : x ∈ I.Kset) (y z : I.Lf) :
    hI (latEnd hx y) z = hI y (latEnd (x := x⁻¹) ((Ksub I).inv_mem hx) z) := by
  apply Subtype.ext
  have := GlobalTheory.Mem.RowsBundle.hAf_inv_mulVec x⁻¹ y.1 z.1
  rw [inv_inv] at this
  exact this

theorem rows_unitri {R : Type} [CommRing R] {N : ℕ} (A B : Matrix (Fin N) (Fin N) R) (h : B * A = 1) (t : ℕ)
    (hB : ∀ i : Fin N, t ≤ i.1 → B i i = 1 ∧ ∀ j, j < i → B i j = 0) :
    ∀ i : Fin N, t ≤ i.1 → A i i = 1 ∧ ∀ j, j < i → A i j = 0 := by
  intro i
  induction i using WellFoundedGT.induction with
  | ind i ih =>
    intro hi
    have key : ∀ j, j ≤ i → A i j = (1 : Matrix (Fin N) (Fin N) R) i j := fun j hj => by
      rw [← h, Matrix.mul_apply, Finset.sum_eq_single i, (hB i hi).1, one_mul]
      · intro l _ hl
        rcases lt_or_gt_of_ne hl with h1 | h1
        · rw [(hB i hi).2 l h1, zero_mul]
        · rw [(ih l h1 (hi.trans h1.le)).2 j (hj.trans_lt h1), mul_zero]
      · exact fun h => absurd (Finset.mem_univ i) h
    exact ⟨by rw [key i le_rfl, Matrix.one_apply_eq], fun j hj => by rw [key j hj.le, Matrix.one_apply_ne hj.ne']⟩

theorem exists_choice_of_idem (g : Fin 2 → ℕ) (hg : ∀ k, (g k).Prime) (hne : g 0 ≠ g 1)
    (hrad : ∀ k, (Ideal.span {((g k : ℕ) : 𝓞 I.E)}).IsRadical)
    (hsp : ∀ k (v : HeightOneSpectrum (𝓞 I.E)), ((g k : ℕ) : 𝓞 I.E) ∈ v.asIdeal → Ideal.absNorm v.asIdeal = g k)
    {f : ℕ} (hf : 0 < f)
    (hcard : ∀ k, {v : HeightOneSpectrum (𝓞 I.E) | ((g k : ℕ) : 𝓞 I.E) ∈ v.asIdeal}.ncard = 2 * f)
    (ε : IntAf I.F I.E) (h1 : ε * ε = ε) (h2 : ε * sigI I ε = 0)
    (h3 : ∀ k (v : HeightOneSpectrum (𝓞 I.E)), ((g k : ℕ) : 𝓞 I.E) ∈ v.asIdeal → 1 - ε - sigI I ε ∈ extId I v.asIdeal) :
    ∃ w : ∀ _ : Fin 2, Fin f → HeightOneSpectrum (𝓞 I.E), IsChoice I g (fun _ => Fin f) w ∧
      ∀ k v, 1 - ε ∈ extId I (w k v).asIdeal := by
  obtain ⟨cj, hc, hconj, hmem⟩ := GlobalTheory.Mem.RowsBundle.exists_conj_involution I
  have hsig := (extId_mul_sup_natCast_conj I).2.2.2.2.2.2
  have hsig' : ∀ u z, z ∈ extId I u.asIdeal → sigI I z ∈ extId I (cj u).asIdeal := fun u z hz => by
    obtain ⟨z', h, e⟩ := hsig u (cj u) ((hconj _ _).2 rfl) z hz
    rwa [show sigI I z = z' from Subtype.ext e.symm]
  have hpr : ∀ k (v : HeightOneSpectrum (𝓞 I.E)), ((g k : ℕ) : 𝓞 I.E) ∈ v.asIdeal → (extId I v.asIdeal).IsPrime := by
    intro k v hv
    haveI : Fact (g k).Prime := ⟨hg k⟩
    obtain ⟨r, hr⟩ := exists_reduction (F := I.F) (g k) (hg k) v (hsp k v hv)
    rw [← ker_eq_extId (hg k).ne_zero r hr]
    exact RingHom.ker_isPrime r
  let Pl : Fin 2 → Type := fun k =>
    {v : HeightOneSpectrum (𝓞 I.E) // ((g k : ℕ) : 𝓞 I.E) ∈ v.asIdeal ∧ 1 - ε ∈ extId I v.asIdeal}
  have hn : ∀ k (v v' : Pl k), v'.1 ≠ cj v.1 := fun k v v' e => by
    have a1 := hsig' _ _ v.2.2
    rw [← e, map_sub, map_one] at a1
    have a2 := Ideal.add_mem _ v'.2.2 (Ideal.mul_mem_left _ ε a1)
    rw [mul_sub, h2, mul_one, sub_zero, sub_add_cancel] at a2
    exact (hpr k _ v'.2.1).ne_top ((Ideal.eq_top_iff_one _).2 a2)
  have hcov : ∀ k (u : HeightOneSpectrum (𝓞 I.E)), ((g k : ℕ) : 𝓞 I.E) ∈ u.asIdeal →
      ∃ v : Pl k, u = v.1 ∨ u = cj v.1 := fun k u hu => by
    have h0 : ε * (1 - ε) ∈ extId I u.asIdeal := by rw [mul_sub, h1, mul_one, sub_self]; exact zero_mem _
    rcases (hpr k u hu).mem_or_mem h0 with h | h
    · refine ⟨⟨cj u, hmem _ _ hu, ?_⟩, Or.inr (hc u).symm⟩
      have a1 := hsig' _ _ (Ideal.add_mem _ (h3 k u hu) h)
      rwa [show 1 - ε - sigI I ε + ε = 1 - sigI I ε by ring, map_sub, map_one, sigI_sigI] at a1
    · exact ⟨⟨u, hu, h⟩, Or.inl rfl⟩
  have hP : ∀ k, Nat.card (Pl k) = f := fun k =>
    (GlobalTheory.Mem.RowsBundle.meets_iff_card cj hc _ (hmem (g k)) hf (hcard k) (fun v : Pl k => v.1) (fun v => v.2.1)
      Subtype.val_injective (hn k)).1 (hcov k)
  have e : ∀ k, Fin f ≃ Pl k := fun k =>
    haveI : Finite (Pl k) := Nat.finite_of_card_ne_zero (by rw [hP]; omega)
    (Finite.equivFinOfCardEq (hP k)).symm
  refine ⟨fun k v => (e k v).1, ⟨hg, hne, hrad, fun k v => ⟨(e k v).2.1, hsp k _ (e k v).2.1⟩,
    fun k => Subtype.val_injective.comp (e k).injective, fun k v v' h => hn k _ _ ((hconj _ _).1 h),
    fun k u hu => ?_⟩, fun k v => (e k v).2.2⟩
  obtain ⟨v, hv⟩ := hcov k u hu
  obtain ⟨v, rfl⟩ := (e k).surjective v
  exact ⟨v, hv.imp id (hconj _ _).2⟩

end GlobalTheory.RowIndex
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsContinuousLimitUniformCauchyStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuous_limit_uniformCauchy : ∀ (k r : ℕ) (μ : Measure (Mt k r)), IsHaarOn (GG k r) μ → ∀ {Wp : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [CompleteSpace Wp] (f : ℕ → Mat k r → Wp) (g : Mt k r → Wp), (∀ j, ContinuousOn (f j) (GG k r)) → (∀ Q : Set (Mt k r), IsCompact Q → AEStronglyMeasurable g (μ.restrict Q)) → (∀ Q : Set (Mt k r), IsCompact Q → ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ j ≥ N, ∀ l ≥ N, ∀ x ∈ Q, Matrix.of x ∈ GG k r → ‖f j (Matrix.of x) - f l (Matrix.of x)‖ ≤ ε) → (∀ Q : Set (Mt k r), IsCompact Q → Filter.Tendsto (fun j : ℕ => ∫⁻ x in Q, (‖f j (Matrix.of x) - g x‖₊ : ENNReal) ^ 2 ∂μ) Filter.atTop (nhds 0)) → ∃ F : Mat k r → Wp, ContinuousOn F (GG k r) ∧ ((fun x : Mt k r => F (Matrix.of x)) =ᵐ[μ] g) ∧ ∀ x ∈ GG k r, Filter.Tendsto (fun j : ℕ => f j x) Filter.atTop (nhds (F x)) := by
  first | exact @GlobalTheory.SgInf.RegLimit.exists_continuous_limit | exact GlobalTheory.SgInf.RegLimit.exists_continuous_limit | (intros; apply GlobalTheory.SgInf.RegLimit.exists_continuous_limit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFrameFixingIsometrySplitRowLatticeStatement
section
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frameFixing_isometry_split_rowLattice : ∀ (D : D7) (u : D.what₂.Word) (F0 : Fb D u) (Λ : LatV D), IsBase D u F0 → IsRowLat D F0 Λ → 1 ≤ Tu D u → ∃ n : ((hS D).V ≃ₗ[D.host.E] (hS D).V), FixFr D (lf D F0) n ∧ IsSplit D F0 (Formalism.HermitianLatticesTheory.gmap n Λ) ∧ IsRowLat D F0 (Formalism.HermitianLatticesTheory.gmap n Λ) := by
  first | exact @GlobalTheory.LoopC.RowSplit.main | exact GlobalTheory.LoopC.RowSplit.main | (intros; apply GlobalTheory.LoopC.RowSplit.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFundamentalDomainEmbeddedRowsLatticeStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.OrbitTerm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fundamentalDomain_embeddedRowsLattice : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ (k : ℕ) (Λ₀ : Submodule (𝓞 E) (Fin 1 → E)) (Λ' : Submodule (𝓞 E) (Fin k → E)), Submodule.IsLattice E Λ₀ → Submodule.IsLattice E Λ' → ∃ P : Set (VecInf E k), MeasurableSet P ∧ volume P = ENNReal.ofReal (covAt E 1 (latAt E 1 Λ₀ (oneInf E 1)) ^ k * (Formalism.HermitianLatticesTheory.vInv E ^ (Formalism.HermitianLatticesTheory.fDeg E * k) / covAt E k (latAt E k Λ' (oneInf E k)))) ∧ (∀ T : VecInf E k, ∃ τ : Fin k → E, (∀ y ∈ Λ', (fun _ => τ ⬝ᵥ y) ∈ Λ₀) ∧ (fun w b => T w b + w.embedding (τ b)) ∈ P) ∧ ∀ (T : VecInf E k) (τ : Fin k → E), (∀ y ∈ Λ', (fun _ => τ ⬝ᵥ y) ∈ Λ₀) → T ∈ P → (fun w b => T w b + w.embedding (τ b)) ∈ P → τ = 0 := by
  first | exact @GlobalTheory.RowDomain.rowDomain | exact GlobalTheory.RowDomain.rowDomain | (intros; apply GlobalTheory.RowDomain.rowDomain <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsHermitianSqrtInSignedUnitaryGroupStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hermitian_sqrt_in_signedUnitaryGroup : ∀ (n : ℕ) (ε : Fin n → Bool) (C : Matrix (Fin n) (Fin n) ℂ), C.det ≠ 0 → (Cᴴ * C) * Formalism.REAL.Jm ε * (Cᴴ * C) = Formalism.REAL.Jm ε → ∃ s : Formalism.REAL.UJ ε, (uMat s)ᴴ = uMat s ∧ uMat s * uMat s = Cᴴ * C := by
  first | exact @GlobalTheory.LeviIso.exists_hermitian_sqrt_mem_UJ | exact GlobalTheory.LeviIso.exists_hermitian_sqrt_mem_UJ | (intros; apply GlobalTheory.LeviIso.exists_hermitian_sqrt_mem_UJ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsLatticeCovolumeInverseIdealStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.OrbitTerm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lattice_covolume_inverse_ideal : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ 𝔞 : Ideal (𝓞 E), 𝔞 ≠ ⊥ → ∃ Λ₀ : Submodule (𝓞 E) (Fin 1 → E), (∀ y, y ∈ Λ₀ ↔ ∀ t ∈ 𝔞, (t : E) * y 0 ∈ (algebraMap (𝓞 E) E).range) ∧ Submodule.IsLattice E Λ₀ ∧ covAt E 1 (latAt E 1 Λ₀ (oneInf E 1)) = Formalism.HermitianLatticesTheory.vInv E ^ Formalism.HermitianLatticesTheory.fDeg E / (Ideal.absNorm 𝔞 : ℝ) := by
  first | exact @GlobalTheory.CovIdeal.covolume_inv_ideal | exact GlobalTheory.CovIdeal.covolume_inv_ideal | (intros; apply GlobalTheory.CovIdeal.covolume_inv_ideal <;> assumption)
end

