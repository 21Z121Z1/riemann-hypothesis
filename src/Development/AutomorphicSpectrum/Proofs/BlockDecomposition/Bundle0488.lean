import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0460
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.GelfandKazhdanDuality.IsCuspFormDualMap
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0447
import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.EisensteinGrowthForms.LocFinType
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0016
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0462
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0446
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0429
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0461
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0468
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.CuspInvariantsFinite.CuspInvFin
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0360
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0367
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalSatakeAlmostAll
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeepConeWeightRatioBound
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0456
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0008
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0015
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0457
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.HighestVectorsRegularLine
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0422

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjugateInverseRightActionStatement
section
open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair GlobalTheory.DiscSpec PositivityTheory.PRW.GKD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_inverse_right_action : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}, ∀ (o : Op E a) (φ : Sm E a) (h1 : (fun g => star (φ.1 (invA E a g))) ∈ Sm E a) (h2 : (fun g => star ((act (invTOp o) φ).1 (invA E a g))) ∈ Sm E a), act o (⟨fun g => star (φ.1 (invA E a g)), h1⟩ : Sm E a) = ⟨fun g => star ((act (invTOp o) φ).1 (invA E a g)), h2⟩ := by
  first | exact @GlobalTheory.CompanionTheory.DualMapAct.act_dual | exact GlobalTheory.CompanionTheory.DualMapAct.act_dual | (intros; apply GlobalTheory.CompanionTheory.DualMapAct.act_dual <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjugationInvariantValuationFieldStatement
section
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugation_invariant_valuation_field : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}, IsCMExt F E σ → ∀ (v : HeightOneSpectrum (𝓞 F)), IsField (Fv F v ⊗[F] E) → ∃ W : Valuation (Fv F v ⊗[F] E) ℝ≥0, (∀ a, W a = absFin F v a) ∧ ∀ a, W (sigR (Fv F v) σ a) = W a := by
  first | exact @GlobalTheory.CompanionTheory.KFin.FieldVal.exists_valuation | exact GlobalTheory.CompanionTheory.KFin.FieldVal.exists_valuation | (intros; apply GlobalTheory.CompanionTheory.KFin.FieldVal.exists_valuation <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousDerivFamily
section
noncomputable section

namespace GlobalTheory.CompanionTheory.WeakHolo

open Metric Set Filter Topology Complex Real

theorem taylor_two {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) {s₀ : ℂ} {r M : ℝ}
    (hr : 0 < r) (hb : closedBall s₀ (3 * r) ⊆ U) (hM : ∀ z ∈ closedBall s₀ (3 * r), ‖f z‖ ≤ M) {η : ℂ}
    (hη : ‖η‖ ≤ r) : ‖f (s₀ + η) - f s₀ - η * deriv f s₀‖ ≤ M / r ^ 2 * ‖η‖ ^ 2 := by
  have hdf : DifferentiableOn ℂ (deriv f) U :=
    ((hf.analyticOnNhd hU).deriv_of_isOpen hU).differentiableOn
  have h1 : ∀ z ∈ closedBall s₀ (2 * r), ‖deriv f z‖ ≤ M / r := by
    intro z hz
    have hsub : closedBall z r ⊆ closedBall s₀ (3 * r) := by
      refine closedBall_subset_closedBall' ?_
      have := mem_closedBall.1 hz
      linarith
    exact norm_deriv_le_of_forall_mem_sphere_norm_le hr (hf.diffContOnCl_ball (hsub.trans hb))
      fun w hw => hM w (hsub (sphere_subset_closedBall hw))
  have h2 : ∀ z ∈ closedBall s₀ r, ‖deriv (deriv f) z‖ ≤ M / r / r := by
    intro z hz
    have hsub : closedBall z r ⊆ closedBall s₀ (2 * r) := by
      refine closedBall_subset_closedBall' ?_
      have := mem_closedBall.1 hz
      linarith
    have hsub' : closedBall s₀ (2 * r) ⊆ closedBall s₀ (3 * r) :=
      closedBall_subset_closedBall (by linarith)
    exact norm_deriv_le_of_forall_mem_sphere_norm_le hr
      (hdf.diffContOnCl_ball ((hsub.trans hsub').trans hb))
      fun w hw => h1 w (hsub (sphere_subset_closedBall hw))
  have hin : ∀ z ∈ closedBall s₀ r, z ∈ U := fun z hz =>
    hb (closedBall_subset_closedBall (by linarith) hz)
  have hc : s₀ ∈ closedBall s₀ r := mem_closedBall_self hr.le
  have h3 : ∀ z ∈ closedBall s₀ r, ‖deriv f z - deriv f s₀‖ ≤ M / r / r * ‖z - s₀‖ := fun z hz =>
    (convex_closedBall s₀ r).norm_image_sub_le_of_norm_deriv_le
      (fun y hy => (hdf y (hin y hy)).differentiableAt (hU.mem_nhds (hin y hy))) h2 hc hz
  have hMn : 0 ≤ M := (norm_nonneg _).trans (hM s₀ (mem_closedBall_self (by positivity)))
  have hs : closedBall s₀ ‖η‖ ⊆ closedBall s₀ r := closedBall_subset_closedBall hη
  have h4 := (convex_closedBall s₀ ‖η‖).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun z => f z - z * deriv f s₀) (f' := fun z => deriv f z - deriv f s₀) (C := M / r / r * ‖η‖)
    (fun z hz => by
      have a := ((hf z (hin z (hs hz))).differentiableAt (hU.mem_nhds (hin z (hs hz)))).hasDerivAt
      have b := (hasDerivAt_id z).mul_const (deriv f s₀)
      have c : HasDerivAt (fun z => f z - z * deriv f s₀) (deriv f z - 1 * deriv f s₀) z := a.sub b
      rw [one_mul] at c
      exact c.hasDerivWithinAt)
    (fun z hz => (h3 z (hs hz)).trans (by
      have := mem_closedBall_iff_norm.1 hz
      gcongr))
    (mem_closedBall_self (norm_nonneg η)) (x := s₀) (y := s₀ + η) (by simp [mem_closedBall_iff_norm])
  have e : f (s₀ + η) - f s₀ - η * deriv f s₀ =
      (f (s₀ + η) - (s₀ + η) * deriv f s₀) - (f s₀ - s₀ * deriv f s₀) := by ring
  rw [e]
  refine h4.trans (le_of_eq ?_)
  simp only [add_sub_cancel_left]
  field_simp

theorem deriv_circle {f : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r) (hf : DiffContOnCl ℂ f (ball c r)) :
    deriv f c = (2 * π * I)⁻¹ * ∮ z in C(c, r), (1 / (z - c) ^ 2) • f z := by
  have := hf.circleIntegral_one_div_sub_center_pow_smul hr 1
  simp only [zero_add, Nat.reduceAdd, Nat.factorial_one, Nat.cast_one, div_one, iteratedDeriv_one] at this
  rw [this, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (by simp [pi_ne_zero]), one_mul]

theorem continuous_deriv_family {X : Type*} [TopologicalSpace X] {w : ℂ → X → ℂ} {S : Set ℂ} {s₀ : ℂ} {r : ℝ}
    (hr : 0 < r) (hb : closedBall s₀ r ⊆ S) (hd : ∀ x, DifferentiableOn ℂ (fun s => w s x) S)
    (hc : ContinuousOn (fun y : ℂ × X => w y.1 y.2) (S ×ˢ Set.univ)) :
    Continuous fun x => deriv (fun s => w s x) s₀ := by
  have e : (fun x => deriv (fun s => w s x) s₀) = fun x => (2 * π * I : ℂ)⁻¹ *
      ∫ θ in (0 : ℝ)..2 * π, deriv (circleMap s₀ r) θ •
        ((1 / (circleMap s₀ r θ - s₀) ^ 2) • w (circleMap s₀ r θ) x) := by
    funext x
    rw [deriv_circle hr ((hd x).diffContOnCl_ball hb)]
    rfl
  rw [e]
  refine continuous_const.mul
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' ?_ _ _)
  have hA : Continuous fun θ : ℝ => deriv (circleMap s₀ r) θ := by
    simp only [deriv_circleMap]
    exact (continuous_circleMap 0 r).mul continuous_const
  have hB : Continuous fun θ : ℝ => (1 / (circleMap s₀ r θ - s₀) ^ 2 : ℂ) :=
    continuous_const.div (((continuous_circleMap s₀ r).sub continuous_const).pow 2) fun θ =>
      pow_ne_zero 2 (sub_ne_zero.2 (circleMap_ne_center hr.ne'))
  have hC : Continuous fun p : X × ℝ => w (circleMap s₀ r p.2) p.1 :=
    hc.comp_continuous (((continuous_circleMap s₀ r).comp continuous_snd).prodMk continuous_fst)
      fun p => ⟨hb (circleMap_mem_closedBall s₀ hr.le p.2), mem_univ _⟩
  exact (hA.comp continuous_snd).smul ((hB.comp continuous_snd).smul hC)

theorem form_scale {X : Type*} {V : Submodule ℂ (X → ℂ)} (μ : V →ₗ[ℂ] ℂ) {b : X → ℝ} {K : ℝ}
    (hK : ∀ f : V, (∀ x, ‖f.1 x‖ ≤ b x) → ‖μ f‖ ≤ K) (f : V) {l : ℝ} (hl : 0 < l)
    (hf : ∀ x, ‖f.1 x‖ ≤ l * b x) : ‖μ f‖ ≤ K * l := by
  have h := hK (((l⁻¹ : ℝ) : ℂ) • f) fun x => by
    have e : ‖(((l⁻¹ : ℝ) : ℂ) • f).1 x‖ = l⁻¹ * ‖f.1 x‖ := by
      simp [abs_of_pos hl]
    rw [e, inv_mul_le_iff₀ hl]
    exact hf x
  rw [map_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hl),
    inv_mul_le_iff₀ hl] at h
  linarith

theorem differentiableOn_form {X : Type*} [TopologicalSpace X] {h : X → ℝ} (hh : ∀ x, 0 ≤ h x)
    {V : Submodule ℂ (X → ℂ)}
    (hV : ∀ (g : X → ℂ) (A : ℝ) (N : ℕ), Continuous g → (∀ x, ‖g x‖ ≤ A * h x ^ N) → g ∈ V)
    (μ : V →ₗ[ℂ] ℂ) (hμ : ∀ N : ℕ, ∃ C : ℝ, ∀ f : V, (∀ x, ‖f.1 x‖ ≤ h x ^ N) → ‖μ f‖ ≤ C)
    (v : ℂ → V) {S : Set ℂ} (hS : IsOpen S)
    (hd : ∀ x, DifferentiableOn ℂ (fun s => (v s).1 x) S)
    (hc : ContinuousOn (fun y : ℂ × X => (v y.1).1 y.2) (S ×ˢ Set.univ))
    (hb : ∀ Q : Set ℂ, Q ⊆ S → IsCompact Q → ∃ (C : ℝ) (N : ℕ), ∀ s ∈ Q, ∀ x, ‖(v s).1 x‖ ≤ C * h x ^ N) :
    DifferentiableOn ℂ (fun s => μ (v s)) S := by
  intro s₀ hs₀
  obtain ⟨R, hR, hRS⟩ := nhds_basis_closedBall.mem_iff.1 (hS.mem_nhds hs₀)
  obtain ⟨C, N, hCN⟩ := hb _ hRS (isCompact_closedBall s₀ R)
  obtain ⟨r, hr, rfl⟩ : ∃ r : ℝ, 0 < r ∧ R = 3 * r := ⟨R / 3, by positivity, by ring⟩
  have hsub : closedBall s₀ r ⊆ closedBall s₀ (3 * r) := closedBall_subset_closedBall (by linarith)
  let d : X → ℂ := fun x => deriv (fun s => (v s).1 x) s₀
  have dc : Continuous d := continuous_deriv_family (w := fun s => (v s).1) hr (hsub.trans hRS) hd hc
  have dB : ∀ x, ‖d x‖ ≤ C / r * h x ^ N := fun x => by
    have := norm_deriv_le_of_forall_mem_sphere_norm_le (f := fun s => (v s).1 x) (c := s₀) hr
      ((hd x).diffContOnCl_ball (hsub.trans hRS)) (C := C * h x ^ N)
      fun z hz => hCN z (hsub (sphere_subset_closedBall hz)) x
    calc ‖d x‖ ≤ C * h x ^ N / r := this
      _ = C / r * h x ^ N := by ring
  let D : V := ⟨d, hV d _ N dc dB⟩
  obtain ⟨K, hK⟩ := hμ N
  set B : ℝ := |C| / r ^ 2 + 1 with hB
  have hBpos : 0 < B := by positivity
  have key : ∀ η : ℂ, ‖η‖ < r →
      ‖μ (v (s₀ + η)) - μ (v s₀) - η • μ D‖ ≤ K * B * ‖η ^ 2‖ := by
    intro η hη
    by_cases h0 : η = 0
    · simp [h0]
    have hηp : 0 < ‖η‖ := norm_pos_iff.2 h0
    have e : μ (v (s₀ + η)) - μ (v s₀) - η • μ D = μ (v (s₀ + η) - v s₀ - η • D) := by
      simp only [map_sub, map_smul]
    rw [e, norm_pow, mul_assoc]
    refine form_scale μ hK _ (by positivity) fun x => ?_
    have t := taylor_two hS (hd x) hr hRS (fun z hz => hCN z hz x) hη.le
    have hp : 0 ≤ h x ^ N := pow_nonneg (hh x) N
    have e2 : (v (s₀ + η) - v s₀ - η • D).1 x =
        (v (s₀ + η)).1 x - (v s₀).1 x - η * deriv (fun s => (v s).1 x) s₀ := rfl
    rw [e2]
    refine t.trans ?_
    have : C * h x ^ N / r ^ 2 * ‖η‖ ^ 2 = (C / r ^ 2) * (‖η‖ ^ 2 * h x ^ N) := by ring
    rw [this, show B * ‖η‖ ^ 2 * h x ^ N = B * (‖η‖ ^ 2 * h x ^ N) by ring]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    rw [hB]
    have : C / r ^ 2 ≤ |C| / r ^ 2 := by gcongr; exact le_abs_self C
    linarith
  have hO : (fun η : ℂ => μ (v (s₀ + η)) - μ (v s₀) - η • μ D) =O[𝓝 0] fun η => η ^ 2 :=
    Asymptotics.IsBigO.of_bound (K * B) (Filter.eventually_of_mem (ball_mem_nhds (0 : ℂ) hr)
      fun η hη => key η (by simpa using hη))
  exact (hasDerivAt_iff_isLittleO_nhds_zero.2
    (hO.trans_isLittleO (Asymptotics.isLittleO_pow_id one_lt_two))).differentiableAt.differentiableWithinAt

end GlobalTheory.CompanionTheory.WeakHolo

namespace GlobalTheory.CompanionTheory.WeakHolo

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl SiegelEisensteinSeries
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}

theorem mem_modFun {g : G2 σ Y → ℂ} {A : ℝ} {N : ℕ} (hg : Continuous g)
    (hA : ∀ x, ‖g x‖ ≤ A * (ht2 x : ℝ) ^ N) : g ∈ modFun σ Y := by
  have hp : 0 < |A| + 1 := by positivity
  have hq : (((|A| + 1 : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have h1 : ((((|A| + 1 : ℝ)) : ℂ)⁻¹ • g) ∈ modFun σ Y := by
    refine Submodule.subset_span ⟨hg.const_smul _, N, fun x => ?_⟩
    have hh : 0 ≤ (ht2 x : ℝ) ^ N := by positivity
    rw [Pi.smul_apply, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp,
      inv_mul_le_iff₀ hp]
    refine (hA x).trans (mul_le_mul_of_nonneg_right ?_ hh)
    linarith [le_abs_self A]
  have := (modFun σ Y).smul_mem (((|A| + 1 : ℝ)) : ℂ) h1
  rwa [smul_inv_smul₀ hq] at this

theorem wholo_growForms (v : ℂ → modFun σ Y) {S : Set ℂ} (hS : IsOpen S)
    (hd : ∀ x, DifferentiableOn ℂ (fun s => (v s).1 x) S)
    (hc : ContinuousOn (fun y : ℂ × G2 σ Y => (v y.1).1 y.2) (S ×ˢ Set.univ))
    (hb : ∀ Q : Set ℂ, Q ⊆ S → IsCompact Q → ∃ (C : ℝ) (N : ℕ), ∀ s ∈ Q, ∀ x, ‖(v s).1 x‖ ≤ C * (ht2 x : ℝ) ^ N) :
    WHolo {μ | IsGrowForm μ} v S := fun μ hμ =>
  differentiableOn_form (h := fun x : G2 σ Y => (ht2 x : ℝ)) (fun x => NNReal.coe_nonneg _)
    (fun _ _ _ hg hA => mem_modFun hg hA) μ hμ v hS hd hc hb

end GlobalTheory.CompanionTheory.WeakHolo

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOpenCellRetractionStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG GlobalTheory.CompanionTheory.BZPhiPG.OntoO Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_open_cell_retraction : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ), ∃ Θ : Mir k ((i + 1) + t + 1) → GL (Fin (i + (t + 1) + 1)) k, Continuous Θ ∧ Θ 1 = 1 ∧
    ∀ (h : Mir k ((i + 1) + (t + 1))), h ∈ HPG k (i + 1) (t + 1) → ∀ (d : Fin (t + 1) → k) (m : Mir k (i + (t + 1)))
      (x : Mir k ((i + 1) + t + 1)), dEmb k i t d * wEl k i t * sO k i t m = h * wEl k i t * x →
      ∃ p ∈ parab k (ePG i (t + 1)), (m : GL (Fin (i + (t + 1) + 1)) k) = p * Θ x := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.OntoO.Proj.exists_parab_mul | exact GlobalTheory.CompanionTheory.BZPhiPG.OntoO.Proj.exists_parab_mul | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.OntoO.Proj.exists_parab_mul <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousShiftedOrbitMapStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG GlobalTheory.CompanionTheory.BZPhiPG.OntoO Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_shifted_orbit_map : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ), Continuous (sO k i t) := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.OntoO.continuous_sO | exact GlobalTheory.CompanionTheory.BZPhiPG.OntoO.continuous_sO | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.OntoO.continuous_sO <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalConstantTermSmall
section
noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Topology

namespace GlobalTheory.CompanionTheory.RapidDecay

theorem norm_le_of_unipRad_variation : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ φ : GAd σ J → ℂ, (∀ γ ∈ ratPts σ J, ∀ g, φ (γ * g) = φ g) → Continuous φ → IsCuspidal σ J φ → ∀ (k : ℕ) (Cc : Matrix (Fin n) (Fin k) E), 0 < k → GlobalTheory.UAut.IsIsoCols σ J Cc → ∀ (g : GAd σ J) (e : ℝ), (∀ m ∈ unipRad σ J Cc, ‖φ (m * g) - φ g‖ ≤ e) → ‖φ g‖ ≤ e := by
  intro F E _ _ _ _ _ σ hCM n J hJ φ hleft hcont hcusp k Cc hk hC g e he
  haveI := GlobalTheory.UAut.locallyCompact_unipRad hCM hJ hC
  have hc : GlobalTheory.Cusp.Cocompact (ratPts σ J) (unipRad σ J Cc) := GlobalTheory.UAut.cocompact_unipRad hCM hJ hC
  haveI hP := hc.isProbabilityMeasure
  have hL : GlobalTheory.AutomorphicL2Unitary.LeftInv (ratPts σ J) φ := hleft
  have h0 : GlobalTheory.Cusp.constTermOn (ratPts σ J) (unipRad σ J Cc) φ g = 0 :=
    (hc.constTermOn_eq_zero_iff (GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom _ Measure.haar) hL g).2
      (hcusp k Cc ⟨hk, hC.1, hC.2⟩ _ _ inferInstance (GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom _ _) g)
  have hI := hc.integrable hL hcont g
  have key : φ g = ∫ q, (φ g - φ ((q.out : unipRad σ J Cc) * g))
      ∂GlobalTheory.Cusp.probMeasure (ratPts σ J) (unipRad σ J Cc) := by
    rw [integral_sub (integrable_const _) hI]
    have h0' : ∫ q, φ ((q.out : unipRad σ J Cc) * g)
        ∂GlobalTheory.Cusp.probMeasure (ratPts σ J) (unipRad σ J Cc) = 0 := h0
    rw [h0', integral_const]
    simp
  rw [key]
  have hb := norm_integral_le_of_norm_le_const (μ := GlobalTheory.Cusp.probMeasure (ratPts σ J) (unipRad σ J Cc))
    (f := fun q => φ g - φ ((q.out : unipRad σ J Cc) * g)) (C := e)
    (.of_forall fun q => by rw [norm_sub_rev]; exact he _ (q.out : unipRad σ J Cc).2)
  simpa using hb

end GlobalTheory.CompanionTheory.RapidDecay

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalGeneralizedSpaceSpanClosed
section
noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl

namespace GlobalTheory.CompanionTheory.CuspSubspace

theorem mem_of_mem_span_cuspForms :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E)))
      (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Kinf E a) W)
      (J : Set (Module.End ℂ (Sm E a))),
      ∀ φ ∈ Submodule.span ℂ {φ : Sm E a | φ ∈ genSpace L ρ J ∧ IsCuspidal φ.1},
        φ ∈ genSpace L ρ J ∧ IsCuspidal φ.1 := by
  intro E _ _ _ a L W _ _ ρ J φ hφ
  induction hφ using Submodule.span_induction with
  | mem x h => exact h
  | zero =>
    refine ⟨(GlobalTheory.CompanionTheory.AffglAssembly.genSub L ρ J).zero_mem, ?_⟩
    intro r hr hr' inst1 inst2 μ 𝓕 hμ hF g
    change ∫ _ in 𝓕, (0 : ℂ) ∂μ = 0
    simp
  | add x y _ _ hx hy =>
    refine ⟨(GlobalTheory.CompanionTheory.AffglAssembly.genSub L ρ J).add_mem hx.1 hy.1, ?_⟩
    intro r hr hr' inst1 inst2 μ 𝓕 hμ hF g
    have ix := (GlobalTheory.CompanionTheory.ConstTerm.integrableOn_fundamentalDomain E a r x hx.1.1.left hx.1.1.level μ 𝓕 hμ hF).2 g
    have iy := (GlobalTheory.CompanionTheory.ConstTerm.integrableOn_fundamentalDomain E a r y hy.1.1.left hy.1.1.level μ 𝓕 hμ hF).2 g
    have e : ∫ u in 𝓕, (x + y).1 (unip u * g) ∂μ =
        (∫ u in 𝓕, x.1 (unip u * g) ∂μ) + ∫ u in 𝓕, y.1 (unip u * g) ∂μ := integral_add ix iy
    rw [e, hx.2 r hr hr' μ 𝓕 hμ hF g, hy.2 r hr hr' μ 𝓕 hμ hF g, add_zero]
  | smul c x _ hx =>
    refine ⟨(GlobalTheory.CompanionTheory.AffglAssembly.genSub L ρ J).smul_mem c hx.1, ?_⟩
    intro r hr hr' inst1 inst2 μ 𝓕 hμ hF g
    have e : ∫ u in 𝓕, (c • x).1 (unip u * g) ∂μ = c • ∫ u in 𝓕, x.1 (unip u * g) ∂μ :=
      integral_smul c _
    rw [e, hx.2 r hr hr' μ 𝓕 hμ hF g, smul_zero]

end GlobalTheory.CompanionTheory.CuspSubspace

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalSatakeAlmostAllStatement
section
open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair GlobalTheory.DiscSpec PositivityTheory.PRW.GKD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_satake_almost_all : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}, ∀ (π : CuspSub E a), ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ B : Multiset ℂˣ, (CG.mk π).HasSat w B := by
  first | exact @GlobalTheory.CompanionTheory.SatAe.eventually_exists_hasSat | exact GlobalTheory.CompanionTheory.SatAe.eventually_exists_hasSat | (intros; apply GlobalTheory.CompanionTheory.SatAe.eventually_exists_hasSat <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeepConeWeightRatioBoundStatement
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.CFin
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deep_cone_weight_ratio_bound : ∀ (r m : ℕ) (c t₁ : ℝ), 0 < c → 1 ≤ t₁ → ∃ R : ℝ, 0 ≤ R ∧ ∀ t ∈ cone r c, ∀ u v : Idx r m, lev m (deep t₁ t) u = lev m (deep t₁ t) v → wt m t u ≤ R * wt m t v := by
  first | exact @GlobalTheory.CompanionTheory.CFin.Ratio.ratio_bounded | exact GlobalTheory.CompanionTheory.CFin.Ratio.ratio_bounded | (intros; apply GlobalTheory.CompanionTheory.CFin.Ratio.ratio_bounded <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DenominatorBoundByHeight
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH

noncomputable section

namespace GlobalTheory.CompanionTheory.GodementH.Den

theorem local_exponent {F : Type} [Field F] [NumberField F] (v : Pl F) {y : F} (hy : y ≠ 0) :
    ∃ e : ℕ, v.valuation F y ≤ WithZero.exp (e : ℤ) ∧
      max 1 ‖algebraMap F (Fv F v) y‖₊ = (Ideal.absNorm v.asIdeal : ℝ≥0) ^ e := by
  have ha : v.valuation F y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
  have hq : (1 : ℝ≥0) < (Ideal.absNorm v.asIdeal : ℝ≥0) := HeightOneSpectrum.one_lt_absNorm_nnreal v
  have hnorm : ‖algebraMap F (Fv F v) y‖₊ =
      WithZeroMulInt.toNNReal (HeightOneSpectrum.absNorm_ne_zero v) (v.valuation F y) :=
    NNReal.eq (FinitePlace.norm_embedding' v y)
  obtain ⟨n, hn⟩ : ∃ n : ℤ, v.valuation F y = WithZero.exp n := ⟨_, (WithZero.exp_log ha).symm⟩
  have hval : WithZeroMulInt.toNNReal (HeightOneSpectrum.absNorm_ne_zero v) (WithZero.exp n) =
      (Ideal.absNorm v.asIdeal : ℝ≥0) ^ n := by
    rw [WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
    simp [WithZero.exp]
  refine ⟨n.toNat, ?_, ?_⟩
  · rw [hn]
    exact WithZero.exp_le_exp.2 (Int.self_le_toNat n)
  · rw [hnorm, hn, hval]
    rcases le_total n 0 with h | h
    · rw [Int.toNat_of_nonpos h, pow_zero]
      exact max_eq_left (zpow_le_one_of_nonpos₀ hq.le h)
    · have h1 : (Ideal.absNorm v.asIdeal : ℝ≥0) ^ n = (Ideal.absNorm v.asIdeal : ℝ≥0) ^ n.toNat := by
        rw [← zpow_natCast, Int.toNat_of_nonneg h]
      rw [h1]
      exact max_eq_right (one_le_pow₀ hq.le)

theorem finite_mulSupport {F : Type} [Field F] [NumberField F] {y : F} (hy : y ≠ 0) :
    (Function.mulSupport fun v : Pl F => max 1 ‖algebraMap F (Fv F v) y‖₊).Finite := by
  have h := (FinitePlace.hasFiniteMulSupport hy).comp_of_injective
    (FinitePlace.equivHeightOneSpectrum (K := F)).symm.injective
  refine Set.Finite.subset h ?_
  intro v hv
  simp only [Function.mem_mulSupport] at hv ⊢
  intro h1
  apply hv
  have h2 : ‖algebraMap F (Fv F v) y‖₊ = 1 := by
    apply NNReal.eq
    have h3 : ‖FinitePlace.embedding v y‖ = 1 := by
      simpa [FinitePlace.equivHeightOneSpectrum_symm_apply] using h1
    exact h3
  rw [h2, max_self]

theorem denominator_le (F : Type) [Field F] [NumberField F] (y : F) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ≥0) ≤ ∏ᶠ v : Pl F, max 1 ‖algebraMap F (Fv F v) y‖₊ ∧
      IsIntegral ℤ ((m : F) * y) := by
  classical
  by_cases hy : y = 0
  · subst hy
    exact ⟨1, one_pos, by simp, by simpa using isIntegral_zero⟩
  choose e he1 he2 using fun v : Pl F => local_exponent v hy
  have hfin := finite_mulSupport hy
  set S : Finset (Pl F) := hfin.toFinset with hS
  set b : Ideal (𝓞 F) := ∏ v ∈ S, v.asIdeal ^ e v with hb
  have hb0 : b ≠ ⊥ := by
    rw [hb, ← Ideal.zero_eq_bot, Finset.prod_ne_zero_iff]
    intro v _
    exact pow_ne_zero _ v.ne_bot
  have hm : 0 < Ideal.absNorm b :=
    Nat.pos_of_ne_zero fun h => hb0 (Ideal.absNorm_eq_zero_iff.1 h)
  refine ⟨Ideal.absNorm b, hm, le_of_eq ?_, ?_⟩
  · rw [finprod_eq_prod_of_mulSupport_subset _ (s := S) (by simp [hS])]
    simp only [he2]
    simp [hb, map_prod, map_pow]
  · have key : ∀ v : Pl F, v.valuation F ((Ideal.absNorm b : F) * y) ≤ 1 := by
      intro v
      have hmem : ((Ideal.absNorm b : ℕ) : 𝓞 F) ∈ v.asIdeal ^ e v := by
        by_cases hv : v ∈ S
        · exact Ideal.le_of_dvd (Finset.dvd_prod_of_mem _ hv) (Ideal.absNorm_mem b)
        · have h1 : max 1 ‖algebraMap F (Fv F v) y‖₊ = 1 := by
            simpa [hS] using hv
          have h0 : e v = 0 := by
            by_contra hne
            have hq : (1 : ℝ≥0) < (Ideal.absNorm v.asIdeal : ℝ≥0) :=
              HeightOneSpectrum.one_lt_absNorm_nnreal v
            have := one_lt_pow₀ hq hne
            rw [← he2 v, h1] at this
            exact lt_irrefl _ this
          simp [h0]
      have h2 := (v.intValuation_le_pow_iff_mem _ (e v)).2 hmem
      have h3 : v.valuation F (Ideal.absNorm b : F) ≤ WithZero.exp (-(e v : ℤ)) := by
        have : (Ideal.absNorm b : F) = algebraMap (𝓞 F) F ((Ideal.absNorm b : ℕ) : 𝓞 F) := by simp
        rw [this, HeightOneSpectrum.valuation_of_algebraMap]
        exact h2
      rw [map_mul]
      calc _ ≤ WithZero.exp (-(e v : ℤ)) * WithZero.exp (e v : ℤ) := mul_le_mul' h3 (he1 v)
        _ = 1 := by rw [← WithZero.exp_add]; simp
    obtain ⟨c, hc⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F _ key
    rw [← hc]
    exact c.isIntegral_coe

end GlobalTheory.CompanionTheory.GodementH.Den

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeJacquetTwistedQuotientStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir GlobalTheory.CompanionTheory.BZNuPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivative_jacquet_twisted_quotient : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (n j : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin (n + j + 1)) k) V) (hd : ∑ a, (![n, j + 1] a) = n + j + 1),
    ∃ q : V →ₗ[ℂ] TwJacquet (iterPhi k ψ j (resM k π)).ρ (MirUin k n) 1, Function.Surjective q ∧
      LinearMap.ker q = twKer π (derUnip k (n + j + 1) n) (derChar k ψ (n + j + 1) n) ∧
      ∀ (g : GL (Fin n) k) (v : V), q (π (leviEmb k (stdBlocks ![n, j + 1] hd) (firstEmb ![n, j + 1] g)) v) =
        GlobalTheory.BZMir.deriv k ψ j π g (q v) := by
  first | exact @GlobalTheory.CompanionTheory.DerivQuot.exists_deriv_quot | exact GlobalTheory.CompanionTheory.DerivQuot.exists_deriv_quot | (intros; apply GlobalTheory.CompanionTheory.DerivQuot.exists_deriv_quot <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualWeightsDominatedStatement
section
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_weights_dominated : ∀ {n : ℕ} (lam : Fin n → ℤ), Antitone lam → ∀ (E : KMod n) (T : E.V →L[ℂ] E.V), IsLefK lam E T → (⨆ μ, wtDual E μ) = ⊤ ∧ ∀ μ, wtDual E μ ≠ ⊥ → DomLE (wtR μ) (m0 lam) := by
  first | exact @GlobalTheory.CompanionTheory.RealCountG.TopeG.topeG | exact GlobalTheory.CompanionTheory.RealCountG.TopeG.topeG | (intros; apply GlobalTheory.CompanionTheory.RealCountG.TopeG.topeG <;> assumption)
end

