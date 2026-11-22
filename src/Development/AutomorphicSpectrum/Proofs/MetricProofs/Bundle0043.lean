import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0035
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PartialFlagBlocks
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0001
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0036
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.IsValueAtOfTorus
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW.TorusAct

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

noncomputable def scaleT (c : K → ℂ) : MvPolynomial K ℂ →ₐ[ℂ] MvPolynomial K ℂ :=
  aeval fun k => C (c k) * X k

omit [Fintype K] in
theorem scaleT_inv_scaleT (c : K → ℂ) (hc : ∀ k, c k ≠ 0) (f : MvPolynomial K ℂ) :
    scaleT (fun k => (c k)⁻¹) (scaleT c f) = f := by
  have h : (scaleT (fun k => (c k)⁻¹)).comp (scaleT c) = AlgHom.id ℂ _ := by
    apply MvPolynomial.algHom_ext
    intro k
    simp only [scaleT, AlgHom.comp_apply, aeval_X, map_mul, algHom_C, AlgHom.id_apply]
    rw [← mul_assoc, algebraMap_eq, ← C_mul, mul_inv_cancel₀ (hc k), C_1, one_mul]
  exact DFunLike.congr_fun h f

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem mConeMap_torus (c : K → ℂ) (z : (Σ k, ι k) → ℂ) (f : MRing ι) :
    mConeMap (fun q : Σ k, ι k => c q.1 * z q) f = scaleT c (mConeMap z f) := by
  have h : mConeMap (fun q : Σ k, ι k => c q.1 * z q) =
      ((scaleT c).restrictScalars ℤ).comp (mConeMap z) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp only [mConeMap, scaleT, AlgHom.comp_apply, aeval_X, AlgHom.restrictScalars_apply, map_mul,
      algHom_C, algebraMap_eq, mul_assoc]
    rw [mul_left_comm]
  rw [h]
  rfl

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem mCoordIdeal_torus (c : K → ℂ) (hc : ∀ k, c k ≠ 0) (z : (Σ k, ι k) → ℂ) :
    mCoordIdeal (fun q : Σ k, ι k => c q.1 * z q) = mCoordIdeal z := by
  ext f
  rw [mCoordIdeal, mCoordIdeal, RingHom.mem_ker, RingHom.mem_ker, mConeMap_torus]
  constructor
  · intro h
    have := congrArg (scaleT fun k => (c k)⁻¹) h
    rwa [scaleT_inv_scaleT c hc, map_zero] at this
  · intro h
    rw [h, map_zero]

theorem isValueAt_torus {x : (Σ k, ι k) → Ω} {s : Ω} {z : (Σ k, ι k) → ℂ} {v : ℂ} (c : K → ℂ)
    (hc : ∀ k, c k ≠ 0) (hv : IsValueAt x s z v) :
    IsValueAt x s (fun q : Σ k, ι k => c q.1 * z q) v := by
  obtain ⟨d, g, h, hg, hh, hy, he, h0, rfl⟩ := hv
  have hu : (∏ k, c k ^ d k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)
  refine ⟨d, g, h, hg, hh, hy, he, ?_, ?_⟩
  · rw [eval_smul_homog h d hh]
    exact mul_ne_zero hu h0
  · rw [eval_smul_homog g d hg, eval_smul_homog h d hh, mul_div_mul_left _ _ hu]

theorem isValueAt_of_torus {x : (Σ k, ι k) → Ω} {s : Ω} {z : (Σ k, ι k) → ℂ} {v : ℂ} (c : K → ℂ)
    (hc : ∀ k, c k ≠ 0) (hv : IsValueAt x s (fun q : Σ k, ι k => c q.1 * z q) v) :
    IsValueAt x s z v := by
  have h := isValueAt_torus (fun k => (c k)⁻¹) (fun k => inv_ne_zero (hc k)) hv
  have e : (fun q : Σ k, ι k => (c q.1)⁻¹ * (c q.1 * z q)) = z := by
    funext q
    exact inv_mul_cancel_left₀ (hc q.1) _
  rwa [e] at h

theorem valAt_torus {x : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} (c : K → ℂ) (hc : ∀ k, c k ≠ 0)
    (hz : z ∈ mcPts (mCoordIdeal x))
    (hcz : (fun q : Σ k, ι k => c q.1 * z q) ∈ mcPts (mCoordIdeal x)) (s : Ω) :
    valAt x s (fun q : Σ k, ι k => c q.1 * z q) = valAt x s z := by
  by_cases h : ∃ v, IsValueAt x s z v
  · obtain ⟨v, hv⟩ := h
    rw [valAt_eq hz hv, valAt_eq hcz (isValueAt_torus c hc hv)]
  · have h' : ¬ ∃ v, IsValueAt x s (fun q : Σ k, ι k => c q.1 * z q) v :=
      fun ⟨v, hv⟩ => h ⟨v, isValueAt_of_torus c hc hv⟩
    rw [valAt, valAt, dif_neg h, dif_neg h']

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (x : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → ℂ) (c : K → ℂ), (∀ k, c k ≠ 0) →
    mCoordIdeal (fun q : Σ k, ι k => c q.1 * z q) = mCoordIdeal z ∧
      (z ∈ mcPts (mCoordIdeal x) → (fun q : Σ k, ι k => c q.1 * z q) ∈ mcPts (mCoordIdeal x) ∧
        ∀ s : Ω, valAt x s (fun q : Σ k, ι k => c q.1 * z q) = valAt x s z) := by
  intro K _ ι _ Ω _ x z c hc
  refine ⟨mCoordIdeal_torus c hc z, fun hz => ?_⟩
  have hcz := mcPts_smul (CoordinateConeArithVar.isMultiHomogIdeal x) c hc hz
  exact ⟨hcz, valAt_torus c hc hz hcz⟩

end GlobalTheory.CompanionTheory.Ar.PB.StepW.TorusAct
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.IsometryPreservesHermitianAndAction
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.PeriodIso

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]

theorem ip_add_left' (R : RiemLat E g Λ) (x x' y : Fin g → ℂ) : R.ip (x + x') y = R.ip x y + R.ip x' y := by
  simp [RiemLat.ip, star_add, Matrix.mulVec_add, dotProduct_add]

theorem ip_add_right' (R : RiemLat E g Λ) (x y y' : Fin g → ℂ) : R.ip x (y + y') = R.ip x y + R.ip x y' := by
  simp [RiemLat.ip, add_dotProduct]

theorem ip_smul_left' (R : RiemLat E g Λ) (c : ℂ) (x y : Fin g → ℂ) :
    R.ip (c • x) y = star c * R.ip x y := by
  simp [RiemLat.ip, star_smul, Matrix.mulVec_smul, dotProduct_smul]

theorem ip_smul_right' (R : RiemLat E g Λ) (c : ℂ) (x y : Fin g → ℂ) : R.ip x (c • y) = c * R.ip x y := by
  simp [RiemLat.ip, smul_dotProduct]

theorem real_smul_eq' (r : ℝ) (x : Fin g → ℂ) : r • x = (r : ℂ) • x := by
  ext i
  simp

theorem ip_period_im (R : RiemLat E g Λ) (x y : Λ) : (R.ip (R.P x) (R.P y)).im = R.form y x :=
  R.im y x

theorem isometry_of_periods (R R' : RiemLat E g Λ) (hs : Submodule.span ℝ (Set.range R.P) = ⊤)
    (γ : Λ ≃ₗ[𝓞 E] Λ) (φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ))
    (hf : ∀ x y, R'.form (γ x) (γ y) = R.form x y) (hP : ∀ x, R'.P (γ x) = φ (R.P x))
    (x y : Fin g → ℂ) : R'.ip (φ x) (φ y) = R.ip x y := by
  let D : (Fin g → ℂ) → (Fin g → ℂ) → ℂ := fun z w => R'.ip (φ z) (φ w) - R.ip z w
  have hl : ∀ z z' w, D (z + z') w = D z w + D z' w := fun z z' w => by
    simp only [D, map_add, ip_add_left']
    ring
  have hr : ∀ z w w', D z (w + w') = D z w + D z w' := fun z w w' => by
    simp only [D, map_add, ip_add_right']
    ring
  have hcl : ∀ (c : ℂ) z w, D (c • z) w = star c * D z w := fun c z w => by
    simp only [D, map_smul, ip_smul_left']
    ring
  have hcr : ∀ (c : ℂ) z w, D z (c • w) = c * D z w := fun c z w => by
    simp only [D, map_smul, ip_smul_right']
    ring
  have h0l : ∀ w, D 0 w = 0 := fun w => by
    simp [D, RiemLat.ip]
  have h0r : ∀ z, D z 0 = 0 := fun z => by
    simp [D, RiemLat.ip]
  have base : ∀ l l', (D (R.P l) (R.P l')).im = 0 := fun l l' => by
    simp only [D, Complex.sub_im]
    rw [← hP, ← hP, ip_period_im, ip_period_im, hf, sub_self]
  have s1 : ∀ l w, (D (R.P l) w).im = 0 := fun l w => by
    have hw : w ∈ Submodule.span ℝ (Set.range R.P) := hs ▸ Submodule.mem_top
    induction hw using Submodule.span_induction with
    | mem w h =>
      obtain ⟨l', rfl⟩ := h
      exact base l l'
    | zero => simp [h0r]
    | add w w' _ _ h h' => simp [hr, h, h']
    | smul r w _ h =>
      rw [real_smul_eq', hcr]
      simp [h]
  have s2 : ∀ z w, (D z w).im = 0 := fun z w => by
    have hz : z ∈ Submodule.span ℝ (Set.range R.P) := hs ▸ Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem z h =>
      obtain ⟨l, rfl⟩ := h
      exact s1 l w
    | zero => simp [h0l]
    | add z z' _ _ h h' => simp [hl, h, h']
    | smul r z _ h =>
      rw [real_smul_eq', hcl]
      simp [h]
  have s3 : (D x y).re = 0 := by
    have h := s2 x (Complex.I • y)
    rw [hcr] at h
    simpa using h
  have s4 : D x y = 0 := Complex.ext s3 (s2 x y)
  exact sub_eq_zero.mp s4

theorem commutes_of_periods (R R' : RiemLat E g Λ) (hs : Submodule.span ℝ (Set.range R.P) = ⊤)
    (γ : Λ ≃ₗ[𝓞 E] Λ) (φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (hP : ∀ x, R'.P (γ x) = φ (R.P x))
    (a : 𝓞 E) (x : Fin g → ℂ) : φ (R.B a x) = R'.B a (φ x) := by
  have hx : x ∈ Submodule.span ℝ (Set.range R.P) := hs ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x h =>
    obtain ⟨l, rfl⟩ := h
    rw [← R.act, ← hP, ← hP, map_smul, R'.act]
  | zero => simp
  | add x x' _ _ h h' => simp [h, h']
  | smul r x _ h =>
    rw [real_smul_eq', map_smul, map_smul, h, map_smul, map_smul]

theorem isometry_and_commutes : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ]
    [Module (𝓞 E) Λ] (R R' : RiemLat E g Λ) (γ : Λ ≃ₗ[𝓞 E] Λ) (φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)),
    (∀ x y, R'.form (γ x) (γ y) = R.form x y) → (∀ x, R'.P (γ x) = φ (R.P x)) →
    (∀ x y, R'.ip (φ x) (φ y) = R.ip x y) ∧ ∀ a x, φ (R.B a x) = R'.B a (φ x) := by
  intro E _ _ _ g Λ _ _ R R' γ φ hf hP
  have hs := (GlobalTheory.T.riemann_lattice_eigen_projection E g Λ Unit R).2.1
  exact ⟨isometry_of_periods R R' hs γ φ hf hP, commutes_of_periods R R' hs γ φ hP⟩

end GlobalTheory.CompanionTheory.Ar.Cusp.PeriodIso
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LeviPullEq
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FA GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.PshPull

open scoped ContDiff

theorem levi_pull_eq {e e' : ℕ} {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z] (A : FinHolAtlas e X)
    (A' : FinHolAtlas e' Z) (h : X → Z) (hh : HoloMap A A' h) (th : LocPot X) (th' : LocPot Z) (u : Z → ℝ)
    (hth : IsPotential A th) (hth' : IsPotential A' th') (hu : A'.Smooth u)
    (hs : SamePot A Set.univ th (th'.pullback h hh.1)) (c : ℝ) (x : X) (j : Fin A.n) (y : Fin e → ℂ)
    (hy : y ∈ (A.chart j).target) (hyU : (A.chart j).symm y ∈ th.U x) (w : Fin e → ℂ) :
    ∃ (j' : Fin A'.n) (y' v : Fin e' → ℂ), y' ∈ (A'.chart j').target ∧
      (A'.chart j').symm y' = h ((A.chart j).symm y) ∧
      levi (fun t => c * (th.φ x ((A.chart j).symm t) + u (h ((A.chart j).symm t)))) y w =
        levi (fun s => c * (th'.φ (h ((A.chart j).symm y)) ((A'.chart j').symm s) + u ((A'.chart j').symm s))) y' v := by
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ :=
    WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤)
  obtain ⟨p, hp⟩ : ∃ p, p = (A.chart j).symm y := ⟨_, rfl⟩
  rw [← hp] at hyU ⊢
  obtain ⟨j', hj'⟩ := A'.cover (h p)
  obtain ⟨W₁, hW₁o, hpW₁, G₁, hG₁, hE₁⟩ := hth.2 x p p ⟨hyU, th.mem_U p⟩
  obtain ⟨W₂, hW₂o, hpW₂, G₂, hG₂, hE₂⟩ := hs p (Set.mem_univ p)
  have hτ : AnalyticAt ℂ (A'.chart j' ∘ h ∘ (A.chart j).symm) y :=
    hh.2 j j' y ⟨hy, by simpa [← hp] using hj'⟩
  have hGa : AnalyticAt ℂ (fun t => G₁ ((A.chart j).symm t) + G₂ ((A.chart j).symm t)) y :=
    AnalyticAt.add (hG₁ j y ⟨hy, by simpa [← hp] using hpW₁⟩) (hG₂ j y ⟨hy, by simpa [← hp] using hpW₂⟩)
  have hτy : (A'.chart j' ∘ h ∘ (A.chart j).symm) y = A'.chart j' (h p) := by simp [← hp]
  have hy' : A'.chart j' (h p) ∈ (A'.chart j').target := (A'.chart j').map_source hj'
  have hsy' : (A'.chart j').symm (A'.chart j' (h p)) = h p := (A'.chart j').left_inv hj'

  have hψ₁ : ContDiffAt ℝ 2 (th'.φ (h p) ∘ (A'.chart j').symm) (A'.chart j' (h p)) := by
    have hO : IsOpen ((A'.chart j').target ∩ (A'.chart j').symm ⁻¹' th'.U (h p)) :=
      (A'.chart j').isOpen_inter_preimage_symm (th'.isOpen_U _)
    have hm : A'.chart j' (h p) ∈ (A'.chart j').target ∩ (A'.chart j').symm ⁻¹' th'.U (h p) :=
      ⟨hy', by simpa [hsy'] using th'.mem_U (h p)⟩
    exact (((hth'.1 (h p) j').contDiffAt (hO.mem_nhds hm))).of_le h2
  have hψ₂ : ContDiffAt ℝ 2 (u ∘ (A'.chart j').symm) (A'.chart j' (h p)) := by
    have hO : IsOpen ((A'.chart j').target ∩ (A'.chart j').symm ⁻¹' Set.univ) := by
      simpa using (A'.chart j').open_target
    have hm : A'.chart j' (h p) ∈ (A'.chart j').target ∩ (A'.chart j').symm ⁻¹' Set.univ :=
      ⟨hy', Set.mem_univ _⟩
    exact ((hu j').contDiffAt (hO.mem_nhds hm)).of_le h2
  have hψ : ContDiffAt ℝ 2 (fun s => c * (th'.φ (h p) ((A'.chart j').symm s) + u ((A'.chart j').symm s)))
      (A'.chart j' (h p)) :=
    contDiffAt_const.mul (hψ₁.add hψ₂)
  have hψτ : ContDiffAt ℝ 2 (fun s => c * (th'.φ (h p) ((A'.chart j').symm s) + u ((A'.chart j').symm s)))
      ((A'.chart j' ∘ h ∘ (A.chart j).symm) y) := by rwa [hτy]
  have hτ2 : ContDiffAt ℝ 2 (A'.chart j' ∘ h ∘ (A.chart j).symm) y :=
    (hτ.restrictScalars (𝕜 := ℝ)).contDiffAt
  have hf : ContDiffAt ℝ 2 ((fun s => c * (th'.φ (h p) ((A'.chart j').symm s) + u ((A'.chart j').symm s))) ∘
      (A'.chart j' ∘ h ∘ (A.chart j).symm)) y := hψτ.comp y hτ2
  have hg : ContDiffAt ℝ 2 (fun t => (G₁ ((A.chart j).symm t) + G₂ ((A.chart j).symm t)).re) y :=
    Complex.reCLM.contDiff.contDiffAt.comp y (hGa.restrictScalars (𝕜 := ℝ)).contDiffAt

  have hev : (fun t => c * (th.φ x ((A.chart j).symm t) + u (h ((A.chart j).symm t)))) =ᶠ[𝓝 y]
      fun t => ((fun s => c * (th'.φ (h p) ((A'.chart j').symm s) + u ((A'.chart j').symm s))) ∘
        (A'.chart j' ∘ h ∘ (A.chart j).symm)) t + c * (G₁ ((A.chart j).symm t) + G₂ ((A.chart j).symm t)).re := by
    have hcs : ContinuousAt (A.chart j).symm y := (A.chart j).continuousAt_symm hy
    have hOx : ∀ᶠ t in 𝓝 y, (A.chart j).symm t ∈ W₁ ∩ W₂ ∩ th.U x ∩ th.U p ∩ h ⁻¹' (A'.chart j').source := by
      apply hcs.eventually_mem
      rw [← hp]
      refine IsOpen.mem_nhds ?_ ⟨⟨⟨⟨hpW₁, hpW₂⟩, hyU⟩, th.mem_U p⟩, hj'⟩
      exact (((hW₁o.inter hW₂o).inter (th.isOpen_U x)).inter (th.isOpen_U p)).inter
        ((A'.chart j').open_source.preimage hh.1)
    filter_upwards [hOx] with t ht
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := ht
    have e1 := hE₁ _ ⟨⟨h1, h3⟩, h4⟩
    have e2 : th.φ p ((A.chart j).symm t) - th'.φ (h p) (h ((A.chart j).symm t)) =
      (G₂ ((A.chart j).symm t)).re := hE₂ _ h2
    have e3 : (A'.chart j').symm (A'.chart j' (h ((A.chart j).symm t))) = h ((A.chart j).symm t) :=
      (A'.chart j').left_inv h5
    simp only [Function.comp_apply, e3, Complex.add_re]
    rw [← e1, ← e2]
    ring
  refine ⟨j', A'.chart j' (h p), fderiv ℂ (A'.chart j' ∘ h ∘ (A.chart j).symm) y w, hy', hsy', ?_⟩
  rw [levi_congr hev w, levi_add_smul c hf hg w, levi_comp w hτ hψτ, levi_re_analytic hGa w, hτy]
  ring

theorem isPsh_pull : ∀ (e e' : ℕ) (X Z : Type) [TopologicalSpace X] [TopologicalSpace Z] (A : FinHolAtlas e X)
    (A' : FinHolAtlas e' Z) (h : X → Z) (hh : HoloMap A A' h) (th : LocPot X) (th' : LocPot Z) (u : Z → ℝ),
    IsPotential A th → IsPotential A' th' → A'.Smooth u → SamePot A Set.univ th (th'.pullback h hh.1) →
    (IsPsh A' (th' + LocPot.ofFun u) → IsPsh A (th + LocPot.ofFun (u ∘ h))) ∧
      (IsPsh A' ((th' + LocPot.ofFun u).rsmul (-1)) → IsPsh A ((th + LocPot.ofFun (u ∘ h)).rsmul (-1))) := by
  intro e e' X Z _ _ A A' h hh th th' u hth hth' hu hs
  refine ⟨fun H x j y hy w => ?_, fun H x j y hy w => ?_⟩
  · obtain ⟨j', y', v, hy', hsy, hl⟩ := levi_pull_eq A A' h hh th th' u hth hth' hu hs 1 x j y hy.1 hy.2.1 w
    have hH := H (h ((A.chart j).symm y)) j' y' ⟨hy', by
      rw [Set.mem_preimage, hsy]; exact LocPot.mem_U _ _⟩ v
    simp only [one_mul] at hl
    exact hl ▸ hH
  · obtain ⟨j', y', v, hy', hsy, hl⟩ := levi_pull_eq A A' h hh th th' u hth hth' hu hs (-1) x j y hy.1 hy.2.1 w
    have hH := H (h ((A.chart j).symm y)) j' y' ⟨hy', by
      rw [Set.mem_preimage, hsy]; exact LocPot.mem_U _ _⟩ v
    exact hl ▸ hH

end GlobalTheory.CompanionTheory.Ar.PB.PshPull
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LiftSystemComplexConjugation
section
open MvPolynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.Cj GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.Cj

open Filter Topology

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem sameOrbit_cross {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') (k : K) (a b : ι k) :
    z ⟨k, a⟩ * z' ⟨k, b⟩ = z ⟨k, b⟩ * z' ⟨k, a⟩ := by
  obtain ⟨c, -, rfl⟩ := h
  simp only
  ring

theorem sameOrbit_of_cross {z z' : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0)
    (hz' : ∀ k, ∃ i, z' ⟨k, i⟩ ≠ 0)
    (h : ∀ (k : K) (a b : ι k), z ⟨k, a⟩ * z' ⟨k, b⟩ = z ⟨k, b⟩ * z' ⟨k, a⟩) :
    SameOrbit z z' := by
  choose j hj using hz'
  refine ⟨fun k => z ⟨k, j k⟩ / z' ⟨k, j k⟩, fun k => ?_, ?_⟩
  · obtain ⟨i, hi⟩ := hz k
    refine div_ne_zero (fun h0 => ?_) (hj k)
    have := h k i (j k)
    rw [h0, zero_mul] at this
    exact (mul_ne_zero hi (hj k)) this
  · funext ⟨k, a⟩
    have := h k a (j k)
    have hjk := hj k
    simp only
    field_simp
    linear_combination this

theorem continuousAt_of_holo {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    {U : Set X} {g : X → ℂ} (hg : A.HoloOn U g) {y : X} (hy : y ∈ U) : ContinuousAt g y := by
  obtain ⟨j, hj⟩ := A.cover y
  have h1 : ContinuousAt ((g ∘ (A.chart j).symm) ∘ A.chart j) y :=
    ContinuousAt.comp (g := g ∘ (A.chart j).symm)
      (hg j _ ⟨(A.chart j).map_source hj, by simpa [(A.chart j).left_inv hj] using hy⟩).continuousAt
      ((A.chart j).continuousAt hj)
  refine h1.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with z hz
  simp [Function.comp, (A.chart j).left_inv hz]

theorem exists_conj_of_isLiftSys {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] {A : FinHolAtlas e X} {P : Ideal (MRing ι)} {U : X → Set X}
    {lift : X → X → (Σ k, ι k) → ℂ} (hS : IsLiftSys A P U lift) :
    ∃ c : X → X, (∀ x, SameOrbit (lift (c x) (c x)) (cj (lift x x))) ∧ Continuous c ∧
      ∀ x, c (c x) = x := by
  obtain ⟨hU, hmem, hholo, hlift, hcompat, hsurj, hinj, -⟩ := hS
  choose c hc using fun x => hsurj _ (cj_mem_mcPts (hlift x x (hmem x)))
  refine ⟨c, hc, ?_, fun x => ?_⟩
  · refine continuous_iff_ultrafilter.2 fun x F hF => ?_
    obtain ⟨x', -, hx'⟩ := isCompact_univ.ultrafilter_le_nhds (F.map c) (by simp)
    have hcF : Tendsto c F (𝓝 x') := hx'
    have hev : ∀ᶠ y in (F : Filter X), y ∈ U x ∧ c y ∈ U x' :=
      Filter.Eventually.and (hF ((hU x).mem_nhds (hmem x))) (hcF ((hU x').mem_nhds (hmem x')))
    have horb : ∀ᶠ y in (F : Filter X), SameOrbit (lift x' (c y)) (cj (lift x y)) := by
      filter_upwards [hev] with y hy
      exact sameOrbit_trans (hcompat x' (c y) (c y) ⟨hy.2, hmem _⟩)
        (sameOrbit_trans (hc y) (sameOrbit_cj (hcompat y x y ⟨hmem y, hy.1⟩)))
    have hl1 : ∀ p, Tendsto (fun y => lift x' (c y) p) F (𝓝 (lift x' x' p)) := fun p =>
      (continuousAt_of_holo A (hholo x' p) (hmem x')).tendsto.comp hcF
    have hl2 : ∀ p, Tendsto (fun y => cj (lift x y) p) F (𝓝 (cj (lift x x) p)) := fun p =>
      (Complex.continuous_conj.tendsto _).comp
        ((continuousAt_of_holo A (hholo x p) (hmem x)).tendsto.mono_left hF)
    have hcross : ∀ (k : K) (a b : ι k),
        lift x' x' ⟨k, a⟩ * cj (lift x x) ⟨k, b⟩ = lift x' x' ⟨k, b⟩ * cj (lift x x) ⟨k, a⟩ :=
      fun k a b => tendsto_nhds_unique_of_eventuallyEq
        ((hl1 ⟨k, a⟩).mul (hl2 ⟨k, b⟩)) ((hl1 ⟨k, b⟩).mul (hl2 ⟨k, a⟩))
        (horb.mono fun y hy => sameOrbit_cross hy k a b)
    have horb' : SameOrbit (lift x' x') (cj (lift x x)) :=
      sameOrbit_of_cross (hlift x' x' (hmem x')).1 (cj_nonzero (hlift x x (hmem x)).1) hcross
    have hxx : x' = c x := hinj _ _ (sameOrbit_trans horb' (sameOrbit_symm (hc x)))
    exact hxx ▸ hcF
  · refine hinj _ _ (sameOrbit_trans (hc (c x)) ?_)
    have := sameOrbit_cj (hc x)
    rwa [cj_cj] at this

end GlobalTheory.CompanionTheory.Ar.PB.Cj
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LinearIndependentComplexOfRealHermitian
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

namespace GlobalTheory.CompanionTheory.Ar.RealFormIndep

theorem pairing_real_combination {g k : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ)
    (u : Fin k → Fin g → ℂ) (a b : Fin k → ℝ) :
    (∑ i, a i • u i) ⬝ᵥ Hm *ᵥ star (∑ j, b j • u j) =
      ∑ i, ∑ j, ((a i * b j : ℝ) : ℂ) * (u i ⬝ᵥ Hm *ᵥ star (u j)) := by
  rw [star_sum, mulVec_sum, sum_dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dotProduct_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [star_smul, star_trivial, mulVec_smul, smul_dotProduct, dotProduct_smul, Complex.real_smul,
    Complex.real_smul, Complex.ofReal_mul]
  ring

theorem linearIndependent_complex_of_real_form :
    ∀ (g k : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ),
      (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm *ᵥ star z).re) →
      ∀ u : Fin k → Fin g → ℂ, LinearIndependent ℝ u →
        (∀ i j, (u i ⬝ᵥ Hm *ᵥ star (u j)).im = 0) → LinearIndependent ℂ u := by
  intro g k Hm hpos u hu hreal
  rw [Fintype.linearIndependent_iff] at hu ⊢
  intro c hc
  have hR : ∀ a b : Fin k → ℝ, ((∑ i, a i • u i) ⬝ᵥ Hm *ᵥ star (∑ j, b j • u j)).im = 0 := by
    intro a b
    rw [pairing_real_combination]
    simp [Complex.im_sum, hreal]
  have hxy : (∑ i, (c i).re • u i) + Complex.I • (∑ i, (c i).im • u i) = 0 := by
    rw [← hc]
    ext t
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_rhs => rw [← Complex.re_add_im (c i)]
    ring
  have hx : (∑ i, (c i).re • u i) = -(Complex.I • ∑ i, (c i).im • u i) := eq_neg_of_add_eq_zero_left hxy
  have hyy : ((∑ i, (c i).im • u i) ⬝ᵥ Hm *ᵥ star (∑ j, (c j).im • u j)).re = 0 := by
    have h := hR (fun i => (c i).re) (fun j => (c j).im)
    rw [hx, neg_dotProduct, smul_dotProduct, smul_eq_mul] at h
    simpa using h
  have hy0 : (∑ i, (c i).im • u i) = 0 := by
    by_contra hne
    have := hpos _ hne
    linarith
  have hx0 : (∑ i, (c i).re • u i) = 0 := by
    rw [hx, hy0, smul_zero, neg_zero]
  intro i
  have h1 := hu (fun i => (c i).re) hx0 i
  have h2 := hu (fun i => (c i).im) hy0 i
  exact Complex.ext (by simpa using h1) (by simpa using h2)

end GlobalTheory.CompanionTheory.Ar.RealFormIndep
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LinearIndependentRealPeriodsBasis
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

namespace GlobalTheory.CompanionTheory.Ar.Cusp

theorem riemLat_basis_periods_linearIndependent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (R : RiemLat E g Λ) (n : ℕ) (b : Module.Basis (Fin n) ℤ Λ), LinearIndependent ℝ (fun j => R.P (b j)) := by
  intro E _ _ _ g Λ _ _ R n b
  have hspan : Submodule.span ℝ (Set.range R.P) = ⊤ := (GlobalTheory.T.riemann_lattice_eigen_projection E g Λ Unit R).2.1
  have hmem : ∀ x : Λ, R.P x ∈ Submodule.span ℝ (Set.range fun j => R.P (b j)) := by
    intro x
    have hx : x ∈ Submodule.span ℤ (Set.range b) := by
      rw [b.span_eq]; trivial
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      exact Submodule.subset_span ⟨j, rfl⟩
    | zero => simp
    | add y z _ _ hy hz =>
      rw [map_add]
      exact Submodule.add_mem _ hy hz
    | smul c y _ hy =>
      rw [map_zsmul]
      exact Submodule.smul_of_tower_mem _ c hy
  have htop : ⊤ ≤ Submodule.span ℝ (Set.range fun j => R.P (b j)) := by
    rw [← hspan]
    apply Submodule.span_le.mpr
    rintro _ ⟨x, rfl⟩
    exact hmem x
  have hcard : Fintype.card (Fin n) = Module.finrank ℝ (Fin g → ℂ) := by
    have h1 : Module.finrank ℤ Λ = Fintype.card (Fin n) := by
      haveI := R.free
      haveI := R.fin
      exact Module.finrank_eq_card_basis b
    have h2 : Module.finrank ℝ (Fin g → ℂ) = 2 * g := by
      simp [Module.finrank_pi_fintype, Complex.finrank_real_complex, mul_comm]
    rw [← h1, R.rank, h2]
  exact linearIndependent_of_top_le_span_of_card_eq_finrank htop hcard

end GlobalTheory.CompanionTheory.Ar.Cusp
end

