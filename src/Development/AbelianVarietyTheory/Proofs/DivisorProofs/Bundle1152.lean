import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1122
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinear
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0061
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0053
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0028
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.IntegralFderivApplyEqZero
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1117
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1118
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InnerThetaFunctionsReadingTestFunctionFrames
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.Overlap

section Kernel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ} (X : Data E r)

theorem kZero_zero (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ) (x₁ x₂ : Frame X.Ψ r) :
    kZero X idx x₁ x₂ (0 : Fin n → Fin g → ℂ) 0 =
      ∏ τ : X.Ψ, (((aLin X x₁ x₂ τ).det * (aAnti X x₁ x₂ τ).det) ^ (n / 2))⁻¹ := by
  unfold kZero
  refine Finset.prod_congr rfl fun τ _ => ?_
  have h : ∀ k, dblz X idx x₁ x₂ (0 : Fin n → Fin g → ℂ) 0 τ k = 0 := fun k => by
    have e : (fun a : Fin r => if (a : ℕ) < X.p0 then (0 : Fin n → Fin g → ℂ) k (idx.symm (τ, a))
        else (0 : Fin n → Fin g → ℂ) k (idx.symm (τ, a))) = 0 := by
      funext a
      simp
    funext c
    simp only [dblz, Matrix.of_apply, e, mulVec_zero, smul_zero]
  simp only [h, mulVec_zero, dotProduct_zero, Finset.sum_const_zero, mul_zero, Complex.exp_zero, mul_one]

theorem aLin_move {x₁ x₂ y₁ y₂ : Frame X.Ψ r} (τ : X.Ψ) {u : Matrix (Fin r) (Fin r) ℂ} (hu : IsUnit u.det)
    (hh : ∀ v w, hermC τ.1 X.Gm (u *ᵥ v) (u *ᵥ w) = hermC τ.1 X.Gm v w)
    (h₁ : mat y₁ τ = u * mat x₁ τ) (h₂ : mat y₂ τ = u * mat x₂ τ) :
    aLin X y₁ y₂ τ * u = aLin X x₁ x₂ τ := by
  refine Matrix.ext_of_mulVec_single fun c => ?_
  generalize (Pi.single c 1 : Fin r → ℂ) = w
  funext a
  rw [← mulVec_mulVec]
  by_cases ha : (a : ℕ) < X.p0
  · rw [DblPoint.aLin_mulVec_of_lt X _ _ _ _ ha, DblPoint.aLin_mulVec_of_lt X _ _ _ _ ha, h₂, ← hh w]
    rfl
  · rw [DblPoint.aLin_mulVec_of_not_lt X _ _ _ _ ha, DblPoint.aLin_mulVec_of_not_lt X _ _ _ _ ha, h₁,
      Matrix.mul_inv_rev, mulVec_mulVec, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]

theorem det_move {x₁ x₂ y₁ y₂ : Frame X.Ψ r} (τ : X.Ψ) {u : Matrix (Fin r) (Fin r) ℂ}
    (hu : u.det * conj u.det = 1)
    (hh : ∀ v w, hermC τ.1 X.Gm (u *ᵥ v) (u *ᵥ w) = hermC τ.1 X.Gm v w)
    (h₁ : mat y₁ τ = u * mat x₁ τ) (h₂ : mat y₂ τ = u * mat x₂ τ) :
    (aLin X y₁ y₂ τ).det * (aAnti X y₁ y₂ τ).det = (aLin X x₁ x₂ τ).det * (aAnti X x₁ x₂ τ).det := by
  have hu' : IsUnit u.det := IsUnit.of_mul_eq_one _ hu
  have e : ∀ z₁ z₂ : Frame X.Ψ r, (aAnti X z₁ z₂ τ).det = conj (aLin X z₂ z₁ τ).det := fun z₁ z₂ => by
    rw [DblPoint.aLin_swap, ← RingHom.mapMatrix_apply, ← RingHom.map_det, Complex.conj_conj]
  rw [e, e, ← aLin_move X τ hu' hh h₁ h₂, ← aLin_move X τ hu' hh h₂ h₁, det_mul, det_mul, map_mul]
  linear_combination (-((aLin X y₁ y₂ τ).det * conj (aLin X y₂ y₁ τ).det)) * hu

end Kernel

variable {D : D7} {S T : HSp D} (C : GlobalTheory.Ker.Ctx S T)

theorem kZero_mvB {B B' : C.Bas} (hB : C.IsB B) (u : GA D T) :
    kZero C.X C.idx (C.xB (C.mvB u B)) (C.xB (C.mvB u B')) (0 : Fin S.rank → Fin C.g → ℂ) 0 =
      kZero C.X C.idx (C.xB B) (C.xB B') (0 : Fin S.rank → Fin C.g → ℂ) 0 := by
  rw [kZero_zero, kZero_zero]
  refine Finset.prod_congr rfl fun σ _ => ?_
  obtain ⟨τ, rfl⟩ := C.m.e.surjective σ
  have hU := GlobalTheory.Ker.ONBasis.compAt_unitary C τ u
  have hm : ∀ A : C.Bas, mat (C.xB (C.mvB u A)) (C.m.e τ) =
      (compAt C.θ τ (Formalism.L2.Theta.mt T u)).map conj * mat (C.xB A) (C.m.e τ) := fun A => by
    rw [GlobalTheory.Ker.ONBasis.mat_xB, GlobalTheory.Ker.ONBasis.mat_xB, ← Matrix.map_mul]
    rfl
  generalize compAt C.θ τ (Formalism.L2.Theta.mt T u) = U at hU hm
  have hG : (gramAt D T τ).det ≠ 0 := by
    intro h0
    have h1 := congrArg det (hB τ)
    have h2 := congrArg det (GlobalTheory.Ker.ONBasis.sgnM_sq C.X)
    rw [det_mul, det_mul, h0, mul_zero, zero_mul] at h1
    rw [det_mul, ← h1, zero_mul, det_one] at h2
    exact zero_ne_one h2
  rw [det_move C.X (C.m.e τ) (u := U.map conj) ?_ ?_ (hm B) (hm B')]
  · have h1 := congrArg det hU
    rw [det_mul, det_mul, det_conjTranspose] at h1
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, Complex.conj_conj]
    apply mul_right_cancel₀ hG
    rw [one_mul]
    refine Eq.trans ?_ h1
    rw [Complex.star_def]
    ring
  · intro v w
    have e : ∀ v : Fin T.rank → ℂ, U.map conj *ᵥ v = fun a => conj ((U *ᵥ star v) a) := fun v => by
      funext a
      simp [mulVec, dotProduct]
    have e' : ∀ v : Fin T.rank → ℂ, v = fun a => conj (star v a) := fun v => by
      funext a
      simp
    rw [e, e, GlobalTheory.Ker.ONBasis.hermC_conj]
    conv_rhs => rw [e' v, e' w, GlobalTheory.Ker.ONBasis.hermC_conj, ← hU]
    rw [star_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec (star (star v)) Uᴴ]

theorem ipO_Th {μ : Measure (WO S T)} {𝓕 : Set (WO S T)} (hμ : IsCovolOne (ratL T S) μ 𝓕)
    {x₁ x₂ : Frame C.X.Ψ T.rank} (h₁ : x₁ ∈ C.X.dom) (h₂ : x₂ ∈ C.X.dom) {φ₁ φ₂ : TF S.rank C.g}
    (s₁ : GlobalTheory.SW.IsSB φ₁) (s₂ : GlobalTheory.SW.IsSB φ₂) :
    GlobalTheory.Ker.ipO μ 𝓕 (C.Th x₁ φ₁) (C.Th x₂ φ₂) =
      dbl C.X C.bas C.idx φ₁ φ₂ 0 * kZero C.X C.idx x₁ x₂ (0 : Fin S.rank → Fin C.g → ℂ) 0 := by
  have h0 : GlobalTheory.Ker.IsRealPt (0 : WO S T) := Matrix.map_zero _ (map_zero _)
  have h := GlobalTheory.Ker.GaussKer.ipO_rho_Th D S T C μ 𝓕 hμ x₁ h₁ x₂ h₂ φ₁ φ₂ s₁ s₂ 0 0 h0 h0
  have hr : ∀ f, C.rho 0 f = f := fun f => by
    funext w
    simp [GlobalTheory.Ker.Ctx.rho, heisO, symplOH, symplO, hO]
  have hz : ∀ x, C.zOf x (0 : WO S T) = 0 := fun x => by
    funext k i
    simp [GlobalTheory.Ker.Ctx.zOf, GlobalTheory.Ker.zR, GlobalTheory.Ker.Ctx.realPt, compAt, hermC, mulVec, dotProduct]
  have hg : ∀ x, GlobalTheory.Ker.gaussR C.X C.bas C.idx x (0 : Fin S.rank → Fin C.g → ℂ) = 1 := fun x => by
    simp [GlobalTheory.Ker.gaussR, hx]
  rw [hr, hr, hz, hz, hg, hg] at h
  have e : (fun (k : Fin S.rank) (i : Fin C.g) => conj ((0 : Fin S.rank → Fin C.g → ℂ) k i)) = 0 := by
    funext k i
    simp
  rw [h, e, map_one, one_mul, one_mul]

theorem isBasOf_unique {W : HSp D} {X : Data D.host.E W.rank} (hm : IsMod W rfl X) {q0 : ℕ}
    (hq : X.p0 + q0 = W.rank) {x : Frame X.Ψ W.rank} {B B' : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ}
    (h : IsBasOf W rfl X hq x B) (h' : IsBasOf W rfl X hq x B') : B = B' := by
  funext ρ
  ext a i
  have hτ : tauE D ρ ∈ X.Ψ := (hm.psi _).2 ⟨ρ, rfl⟩
  by_cases hi : (i : ℕ) < q0
  · rw [h ρ ⟨_, hτ⟩ rfl (Sum.inl ⟨i, hi⟩) i a rfl, h' ρ ⟨_, hτ⟩ rfl (Sum.inl ⟨i, hi⟩) i a rfl]
  · have h1 : (i : ℕ) - q0 < X.p0 := by have := i.2; omega
    have h2 : (i : ℕ) = q0 + ((i : ℕ) - q0) := by omega
    rw [h ρ ⟨_, hτ⟩ rfl (Sum.inr ⟨_, h1⟩) i a h2, h' ρ ⟨_, hτ⟩ rfl (Sum.inr ⟨_, h1⟩) i a h2]

end GlobalTheory.AdTh.Overlap

open GlobalTheory.AdTh.Overlap in

theorem GlobalTheory.AdTh.inner_of_reads : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsStdChar D ψ (-1) → IsInfFam θ → V.gram = 1 → Even V.rank → IsMod W hr X → IsSympl X bas → ∃ G : Frame X.Ψ r → Frame X.Ψ r → ℂ, ∀ x x' : Frame X.Ψ r, IsONFr X x → IsONFr X x' → G x x' ≠ 0 ∧ (∀ u : GA D W, G (frMove θ W hr X u x) (frMove θ W hr X u x') = G x x') ∧ ∀ v : TF V.rank g, GlobalTheory.SW.IsSB v → v ≠ 0 → ∃ c : ℂ, c ≠ 0 ∧ ∀ y y' : Frame X.Ψ r, IsONFr X y → IsONFr X y' → ∀ (f f' : WO V W → ℂ) (κ κ' : ℂ), IsThetaFunO ψ V W f → IsThetaFunO ψ V W f' → Reads θ V W hr X bas idx f (κ • v) y → Reads θ V W hr X bas idx f' (κ' • v) y' → ∀ (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), IsCovolOne (ratL W V) μ 𝓕 → ∫ w in 𝓕, f w * conj (f' w) ∂μ = κ * conj κ' * (c * G y y') := by
  intro D ψ θ V W r g hr X bas idx hstd hinf hV he hm hs
  subst hr
  obtain ⟨X', m, hq', hq, bas', idx', hs', -, -, -, -, -, -, H⟩ :=
    GlobalTheory.T.orthonormal_frame_reading_eq_conjugate_datum_theta D ψ θ V W g X bas idx hstd hinf he hV hm hs
  let C : GlobalTheory.Ker.Ctx V W := ⟨ψ, hstd, θ, hinf, X', m, g, X.p0, hq', bas', idx', hs', he⟩
  let Bx : Frame X.Ψ W.rank → C.Bas := fun x => Classical.epsilon fun B => IsBasOf W rfl X hq x B
  have hBx : ∀ x, IsONFr X x → IsBasOf W rfl X hq x (Bx x) := fun x hx => Classical.epsilon_spec (H x hx).1
  have hB : ∀ x, IsONFr X x → C.IsB (Bx x) := fun x hx => ((H x hx).2 _ (hBx x hx)).1
  have hd : ∀ x, IsONFr X x → C.xB (Bx x) ∈ C.X.dom := fun x hx =>
    GlobalTheory.Ker.ONBasis.mem_dom C.X (GlobalTheory.Ker.ONBasis.isONFr_xB C (hB x hx))
  have hmv : ∀ x, IsONFr X x → ∀ u, Bx (frMove θ W rfl X u x) = C.mvB u (Bx x) := fun x hx u => by
    obtain ⟨h1, h2⟩ := ((H x hx).2 _ (hBx x hx)).2.2.2.2.2.2.2.1 u
    exact isBasOf_unique hm hq (hBx _ h1) h2
  have hT : ∀ x, IsONFr X x → ∀ (f : WO V W → ℂ) (φ : TF V.rank g), GlobalTheory.SW.IsSB φ →
      ((IsThetaFunO ψ V W f ∧ Reads θ V W rfl X bas idx f φ x) ↔ f = C.Th (C.xB (Bx x)) φ) := fun x hx =>
    ((H x hx).2 _ (hBx x hx)).2.2.2.2.2.2.2.2
  have hne : ∀ x x', IsONFr X x → IsONFr X x' →
      kZero C.X C.idx (C.xB (Bx x)) (C.xB (Bx x')) (0 : Fin V.rank → Fin g → ℂ) 0 ≠ 0 := fun x x' hx hx' => by
    rw [kZero_zero]
    exact Finset.prod_ne_zero_iff.2 fun τ _ => inv_ne_zero (pow_ne_zero _ (mul_ne_zero
      (DblPoint.det_aLin_ne_zero (hd x hx) (hd x' hx') τ) (DblPoint.det_aAnti_ne_zero (hd x hx) (hd x' hx') τ)))
  refine ⟨fun x x' => kZero C.X C.idx (C.xB (Bx x)) (C.xB (Bx x')) (0 : Fin V.rank → Fin g → ℂ) 0,
    fun x x' hx hx' => ⟨hne x x' hx hx', fun u => ?_, fun v hv hv0 => ⟨dbl C.X C.bas C.idx v v 0, fun hc => ?_, ?_⟩⟩⟩
  · beta_reduce
    rw [hmv x hx, hmv x' hx']
    exact kZero_mvB C (hB x hx) u
  · obtain ⟨⟨μ, 𝓕, hμ⟩, hip⟩ := GlobalTheory.Ker.ScalarProduct.ip_basic D V W C
    have h1 := ipO_Th C hμ (hd x hx) (hd x hx) hv hv
    rw [hc, zero_mul] at h1
    have h2 := (hip μ 𝓕 hμ _ ((hT x hx _ v hv).2 rfl).1).2.1 h1
    obtain ⟨l1, l2, -⟩ := GlobalTheory.Ker.Ctx.th_laws D V W C _ (hd x hx) v hv
    have h3 : GlobalTheory.SW.IsSB ((0 : ℂ) • v) := by
      obtain ⟨R, hR, -, -⟩ := hv
      exact ⟨R, hR, fun x hx => absurd (by simp) hx, fun x y hy => by simp⟩
    refine hv0 (((l1 _ h3).2 ?_).trans (zero_smul ℂ v))
    rw [l2, h2, zero_smul]
  · intro y y' hy hy' f f' κ κ' hf hf' rf rf' μ 𝓕 hμ
    have e := (hT y hy f _ rf.1).1 ⟨hf, rf⟩
    have e' := (hT y' hy' f' _ rf'.1).1 ⟨hf', rf'⟩
    rw [(GlobalTheory.Ker.Ctx.th_laws D V W C _ (hd y hy) v hv).2.1] at e
    rw [(GlobalTheory.Ker.Ctx.th_laws D V W C _ (hd y' hy') v hv).2.1] at e'
    have h1 := ipO_Th C hμ (hd y hy) (hd y' hy') hv hv
    refine Eq.trans ?_ (congrArg (κ * conj κ' * ·) h1)
    rw [e, e', GlobalTheory.Ker.ipO, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    ring
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnInvMulLogSqNearZero
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem continuousAt_inv_log_zero : ContinuousAt (fun t : ℝ => (Real.log t)⁻¹) 0 := by
  unfold ContinuousAt
  simp only [Real.log_zero, inv_zero]
  refine Tendsto.mono_left (x := 𝓝[≠] (0:ℝ) ⊔ pure 0) ?_ (nhdsNE_sup_pure (0:ℝ)).ge
  refine Tendsto.sup ?_ ?_
  · exact tendsto_inv_atBot_zero.comp Real.tendsto_log_nhdsNE_zero
  · rw [tendsto_pure_left]
    intro s hs
    simpa using mem_of_mem_nhds hs

theorem integrableOn_inv_mul_log_sq :
    IntegrableOn (fun t : ℝ => t * (t * |Real.log t|)⁻¹ ^ 2) (Set.Ioc 0 (1 / 2)) := by
  have hcont : ContinuousOn (fun t : ℝ => -(Real.log t)⁻¹) (Set.Icc 0 (1 / 2)) := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h | h
    · subst h
      exact (continuousAt_inv_log_zero.neg).continuousWithinAt
    · have hlog : Real.log t ≠ 0 := by
        have : Real.log t < 0 := Real.log_neg h (by linarith [ht.2])
        exact this.ne
      exact ((Real.continuousAt_log h.ne').inv₀ hlog).neg.continuousWithinAt
  refine intervalIntegral.integrableOn_deriv_of_nonneg hcont ?_ ?_
  · intro t ht
    have ht0 : 0 < t := ht.1
    have hlogneg : Real.log t < 0 := Real.log_neg ht0 (by linarith [ht.2])
    have hlog : Real.log t ≠ 0 := hlogneg.ne
    have h1 : HasDerivAt (fun t => -(Real.log t)⁻¹) (-(-t⁻¹ / Real.log t ^ 2)) t :=
      ((Real.hasDerivAt_log ht0.ne').inv hlog).neg
    convert h1 using 1
    rw [abs_of_neg hlogneg]
    field_simp
  · intro t ht
    have := ht.1
    positivity

end GlobalTheory.GoodTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAntiholomorphicDerivCompactSupportEqZero
section
set_option autoImplicit false

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

noncomputable section

namespace GlobalTheory.GoodTop

theorem integral_dbar_eq_zero_of_hasCompactSupport {n : ℕ} {G : V n → ℂ} (hG : ContDiff ℝ 1 G)
    (hc : HasCompactSupport G) (u : V n) :
    Integrable (fun v => dbar G v u) ∧ ∫ v, dbar G v u = 0 := by
  have hint : ∀ w : V n, Integrable (fun y => fderiv ℝ G y w) := fun w =>
    ((hG.continuous_fderiv (by norm_num)).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hc.fderiv_apply (𝕜 := ℝ) w)
  refine ⟨?_, ?_⟩
  · simp only [dbar_apply, smul_eq_mul]
    exact ((hint _).add ((hint _).const_mul _)).const_mul _
  · simp only [dbar_apply, smul_eq_mul]
    rw [integral_const_mul, integral_add (hint _) ((hint _).const_mul _), integral_const_mul,
      ReciprocityTheory.L2DbarEstimates.integral_fderiv_apply_eq_zero n G hG hc,
      ReciprocityTheory.L2DbarEstimates.integral_fderiv_apply_eq_zero n G hG hc]
    simp

theorem setIntegral_dbar_eq_zero {n : ℕ} (U K : Set (V n)) (g : V n → ℂ) (ξ : V n)
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) (hg : ContDiffOn ℝ 1 g U)
    (h0 : ∀ v ∈ U, v ∉ K → g v = 0) :
    IntegrableOn (fun v => dbar g v ξ) U ∧ ∫ v in U, dbar g v ξ = 0 := by
  classical
  set G : V n → ℂ := U.indicator g with hGdef
  have hin : ∀ v ∈ U, G =ᶠ[𝓝 v] g := fun v hv => by
    filter_upwards [hU.mem_nhds hv] with x hx
    exact Set.indicator_of_mem hx g
  have hz : ∀ x, x ∉ K → G x = 0 := fun x hx => by
    by_cases hxU : x ∈ U
    · rw [hGdef, Set.indicator_of_mem hxU, h0 x hxU hx]
    · rw [hGdef, Set.indicator_of_notMem hxU]
  have hout : ∀ v, v ∉ K → G =ᶠ[𝓝 v] fun _ => 0 := fun v hv => by
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hv] with x hx
    exact hz x hx
  have hG : ContDiff ℝ 1 G := by
    rw [contDiff_iff_contDiffAt]
    intro v
    by_cases hv : v ∈ U
    · exact (hg.contDiffAt (hU.mem_nhds hv)).congr_of_eventuallyEq (hin v hv)
    · exact contDiffAt_const.congr_of_eventuallyEq (hout v fun h => hv (hKU h))
  have hc : HasCompactSupport G := HasCompactSupport.intro hK hz
  obtain ⟨hI, hE⟩ := integral_dbar_eq_zero_of_hasCompactSupport hG hc ξ
  have heq : Set.EqOn (fun v => dbar G v ξ) (fun v => dbar g v ξ) U := fun v hv => by
    simp only [dbar_congr (hin v hv)]
  refine ⟨hI.integrableOn.congr_fun heq hU.measurableSet, ?_⟩
  rw [← setIntegral_congr_fun hU.measurableSet heq,
    setIntegral_eq_integral_of_forall_compl_eq_zero, hE]
  intro v hv
  rw [dbar_congr (hout v fun h => hv (hKU h))]
  simp [dbar_apply]

end GlobalTheory.GoodTop
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralBlock
section
set_option autoImplicit false

noncomputable section

open NumberField PowerSeries Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds
open Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.ExpFrame Formalism.CohomologicalDescent.FrobeniusPeriodChange

namespace GlobalTheory.WachBlock

section Galois

variable (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]

def ofOL (LL : FinExt l) : ↥(OL LL) →+* PadicAlgCl l :=
  (LL.1.val.toRingHom).comp ((OL LL).val.toRingHom)

def IntegralBlock (n t : ℕ) (J : (E →+* PadicAlgCl l) → Fin n → ℤ) (bot : (E →+* PadicAlgCl l) → ℤ) : Prop :=
  ∃ (LL : FinExt l) (r : G E Ω →* GL (Fin n) ↥(OL LL)) (ψ : Fin t → G E Ω →* (↥(OL LL))ˣ) (ϖ : ↥(OL LL))
    (R : ℕ) (M : Fin (R + 1) → Submodule ↥(OL LL) (Fin n → ↥(OL LL))) (rs : Fin t → Fin R),
    (∃ ζ : ↥LL.1, IsPrimitiveRoot ζ l) ∧ (∀ (τ : E →+* PadicAlgCl l) (x : E), τ x ∈ LL.1) ∧
    CrysWith ((Matrix.GeneralLinearGroup.map (ofOL l LL)).comp r) (fun τ => Finset.univ.val.map (J τ)) ∧
    (∀ s, CrysWith (GlobalTheory.TripleGal.rk1 ((Units.map (ofOL l LL).toMonoidHom).comp (ψ s)))
      fun τ => {bot τ + ((s : ℕ) : ℤ)}) ∧
    Irreducible ϖ ∧ (∀ x, x ∈ M 0 ↔ ∃ y : Fin n → ↥(OL LL), x = fun a => ϖ * y a) ∧ M (Fin.last R) = ⊤ ∧ Monotone M ∧
    (∀ g k x, x ∈ M k → (r g : Matrix (Fin n) (Fin n) ↥(OL LL)).mulVec x ∈ M k) ∧
    Function.Injective rs ∧
    ∀ s, ∃ x ∈ M (rs s).succ, x ∉ M (rs s).castSucc ∧
      M (rs s).succ = M (rs s).castSucc ⊔ Submodule.span ↥(OL LL) {x} ∧
      ∀ g, (r g : Matrix (Fin n) (Fin n) ↥(OL LL)).mulVec x - (fun a => ((ψ s g : (↥(OL LL))ˣ) : ↥(OL LL)) * x a) ∈
        M (rs s).castSucc

end Galois

section Reduced

variable {F : Type} [Field F] {n : ℕ}

def lau (y : Fin n → F⟦X⟧) : Fin n → LaurentSeries F := fun a => ((y a : F⟦X⟧) : LaurentSeries F)

def phiV (l : ℕ) (P : Matrix (Fin n) (Fin n) F⟦X⟧) (y : Fin n → F⟦X⟧) : Fin n → F⟦X⟧ :=
  P.mulVec fun a => frob0 l (y a)

def gamV (un : F⟦X⟧) (D : Matrix (Fin n) (Fin n) F⟦X⟧) (y : Fin n → F⟦X⟧) : Fin n → F⟦X⟧ :=
  (1 + (X : F⟦X⟧) • D).mulVec fun a => gam0 0 un (y a)

def RedFilt {ι : Type} (σ : Equiv.Perm ι) (l : ℕ) {t : ℕ} (un : F⟦X⟧) (P D : ι → Matrix (Fin n) (Fin n) F⟦X⟧)
    (Pψ Dψ : Fin t → ι → F⟦X⟧) : Prop :=
  ∃ (R : ℕ) (V : ι → Fin (R + 1) → Submodule (LaurentSeries F) (Fin n → LaurentSeries F)) (rs : Fin t → Fin R)
    (e : ι → Fin t → Fin n → F⟦X⟧) (m : ι → Fin t → ℤ),
    Function.Injective rs ∧
    (∀ i, V i 0 = ⊥ ∧ V i (Fin.last R) = ⊤ ∧ Monotone (V i)) ∧
    (∀ k i j, Module.finrank (LaurentSeries F) (V i k) = Module.finrank (LaurentSeries F) (V j k)) ∧
    (∀ i k y, lau y ∈ V (σ i) k → lau (phiV l (P i) y) ∈ V i k) ∧
    (∀ i k y, lau y ∈ V i k → lau (gamV un (D i) y) ∈ V i k) ∧
    (∀ i s, lau (e i s) ∉ V i (rs s).castSucc ∧
      V i (rs s).succ = V i (rs s).castSucc ⊔ Submodule.span (LaurentSeries F) {lau (e i s)}) ∧
    (∀ i s, (((X : F⟦X⟧) : LaurentSeries F) ^ m i s) • lau (phiV l (P i) (e (σ i) s)) -
        (((X : F⟦X⟧) : LaurentSeries F) ^ ((l : ℤ) * m (σ i) s) * ((Pψ s i : F⟦X⟧) : LaurentSeries F)) •
          lau (e i s) ∈ V i (rs s).castSucc) ∧
    ∀ i s, (((X : F⟦X⟧) : LaurentSeries F) ^ m i s) • lau (gamV un (D i) (e i s)) -
        (((gamSer 0 un : F⟦X⟧) : LaurentSeries F) ^ m i s *
          ((1 + X * Dψ s i : F⟦X⟧) : LaurentSeries F)) • lau (e i s) ∈ V i (rs s).castSucc

end Reduced

end GlobalTheory.WachBlock

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralUnitaryMatricesFiniteCardLeStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_unitary_matrices_finite_card_le : ∀ (D : D7) (n : ℕ), {g : Matrix (Fin n) (Fin n) D.host.E | gᴴ * g = 1 ∧ ∀ a b, IsIntegral ℤ (g a b)}.Finite ∧ {g : Matrix (Fin n) (Fin n) D.host.E | gᴴ * g = 1 ∧ ∀ a b, IsIntegral ℤ (g a b)}.ncard ≤ NumberField.Units.torsionOrder D.host.E ^ n * n.factorial := by
  first | exact @GlobalTheory.LowRow.SignedPerm.finite_and_ncard_le | exact GlobalTheory.LowRow.SignedPerm.finite_and_ncard_le | (intros; apply GlobalTheory.LowRow.SignedPerm.finite_and_ncard_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InterPolyEqZeroOfIsHomogeneousNeDim
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.ProjVar.Var

theorem interPoly_eq_zero_of_isHomogeneous (F : Type) [Field F] (Y : Var F) (κ : Type) (gr : κ → Y.Dv) (k : ℕ)
    (P : MvPolynomial κ ℝ) (hP : P.IsHomogeneous k) (hk : k ≠ Y.dim) : Y.interPoly gr P = 0 := by
  rw [P.as_sum, map_sum]
  refine Finset.sum_eq_zero fun d hd => ?_
  have hw : Finsupp.weight 1 d = k := hP (mem_support_iff.mp hd)
  have e : monomial d (coeff d P) = coeff d P • basisMonomials κ ℝ d := by
    rw [coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
  rw [e, map_smul, interPoly, Module.Basis.constr_basis, dif_neg, smul_zero]
  rintro ⟨s, hs⟩
  apply hk
  rw [← hw, ← hs, map_sum]
  simp [Finsupp.weight_apply, Finsupp.sum_single_index]

end GlobalTheory.ProjVar.Var
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionDivisorEqSelfIntersectionPresented
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

namespace GlobalTheory.ChernDegree

theorem inter_const_eq_topSelf_of_presents :
    ∀ (Y : Var ℂ) (Δ : Y.Dv) (L : LB Y.X) (r : L.ι → Y.Fnˣ), L.IsLB → Presents Δ L r → Y.inter (fun _ => Δ) = topSelfIntersection ℂ L Y.dim :=
  fun _ _ _ _ hL h => Var.inter_eq_of_toPic_eq (fun _ => hL) fun _ => h.toPic_eq

end GlobalTheory.ChernDegree
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockUnitaryFiniteSubspaceComapInjectiveIntertStatement
section
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isBlockUnitaryFiniteSubspace_comap_injective_intertwiner : ∀ (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool) (F : ι → ι → Module.End ℂ M), ∀ (M' : Type) [AddCommGroup M'] [Module ℂ M'] (F' : ι → ι → Module.End ℂ M') (f : M →ₗ[ℂ] M'), Function.Injective f → (∀ a b, s a = s b → ∀ x, f (F a b x) = F' a b (f x)) → (∀ U' : Submodule ℂ M', UnitOn s F' U' → UnitOn s F (U'.comap f)) ∧ (LocU s F' → LocU s F) := by
  first | exact @GlobalTheory.HoweR.unitOn_comap_locU | exact GlobalTheory.HoweR.unitOn_comap_locU | (intros; apply GlobalTheory.HoweR.unitOn_comap_locU <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockUnitaryFiniteSubspaceMapIntertwinerStatement
section
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isBlockUnitaryFiniteSubspace_map_intertwiner : ∀ (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool) (F : ι → ι → Module.End ℂ M), ∀ (M' : Type) [AddCommGroup M'] [Module ℂ M'] (F' : ι → ι → Module.End ℂ M') (f : M →ₗ[ℂ] M') (U : Submodule ℂ M), (∀ a b, s a = s b → ∀ x ∈ U, f (F a b x) = F' a b (f x)) → UnitOn s F U → UnitOn s F' (U.map f) := by
  first | exact @GlobalTheory.HoweR.unitOn_map | exact GlobalTheory.HoweR.unitOn_map | (intros; apply GlobalTheory.HoweR.unitOn_map <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockUnitaryFiniteSubspaceOfLeStableStatement
section
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isBlockUnitaryFiniteSubspace_of_le_stable : ∀ (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool) (F : ι → ι → Module.End ℂ M), ∀ U U' : Submodule ℂ M, UnitOn s F U → U' ≤ U → (∀ a b, s a = s b → ∀ u ∈ U', F a b u ∈ U') → UnitOn s F U' := by
  first | exact @GlobalTheory.HoweR.unitOn_of_le | exact GlobalTheory.HoweR.unitOn_of_le | (intros; apply GlobalTheory.HoweR.unitOn_of_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtaleCoordinatesOnOpenBaseChangePreimageStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isEtaleCoordinatesOnOpen_baseChange_preimage : ∀ (R R' : Type) [CommRing R] [CommRing R'] (φ : R →+* R') (X X' : Scheme.{0}) (f : X ⟶ Sp R) (f' : X' ⟶ Sp R') (π : X' ⟶ X) (U : X.Opens) (d : ℕ) (t : Fin d → Γ(X, U)), IsPullback π f' f (spMap φ) → IsAffineOpen U → IsEtCoord f U t → IsAffineOpen (π ⁻¹ᵁ U) ∧ IsEtCoord f' (π ⁻¹ᵁ U) (fun a => (π.app U).hom (t a)) := by
  first | exact @GlobalTheory.LogPair.isEtCoord_baseChange | exact GlobalTheory.LogPair.isEtCoord_baseChange | (intros; apply GlobalTheory.LogPair.isEtCoord_baseChange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtaleCoordinatesOnOpenPullOpenImmersionStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isEtaleCoordinatesOnOpen_pull_openImmersion : ∀ (R : Type) [CommRing R] (X Y : Scheme.{0}) (f : X ⟶ Sp R) (e : Y ⟶ X) [IsOpenImmersion e] (U : X.Opens) (W : Y.Opens) (h : W ≤ e ⁻¹ᵁ U) (d : ℕ) (t : Fin d → Γ(X, U)), IsAffineOpen U → IsAffineOpen W → IsEtCoord f U t → IsEtCoord (e ≫ f) W (fun a => (e.appLE U W h).hom (t a)) := by
  first | exact @GlobalTheory.LogPair.isEtCoord_openImmersion | exact GlobalTheory.LogPair.isEtCoord_openImmersion | (intros; apply GlobalTheory.LogPair.isEtCoord_openImmersion <;> assumption)
end

