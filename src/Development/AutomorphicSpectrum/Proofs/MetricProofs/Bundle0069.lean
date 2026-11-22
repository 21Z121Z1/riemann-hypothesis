import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0042
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0044
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionFunctorialHolomorphic
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0066
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0059
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0041
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0023
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0022
import GroundTheory.HeightsAndTheta.Heights.FactorialBounds.Assembly
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HasSumPolyDerivMulProdAddMatrix
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0018
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsUnitOfLagrangian
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0014
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0065
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaHolomorphic
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0061
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ValueConstantOnOrbitStatement

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionMapLocallyAnalytic
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.CovMap

section Orbit

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P : Ideal (MRing ι)} {D e : ℕ} (R : AnLogRes P ⊤ D) {Y : Type*} [TopologicalSpace Y]
  (B : FinHolAtlas e Y) {V : Y → Set Y} {μ : Y → Y → (Σ k, ι k) → ℂ} {h : Y → R.X}

theorem continuous_of_orbit_of_ne (hVo : ∀ y, IsOpen (V y)) (hVm : ∀ y, y ∈ V y)
    (hμ : ∀ y q, B.HoloOn (V y) fun u => μ y u q) (hne : ∀ y k, ∃ i, μ y y ⟨k, i⟩ ≠ 0)
    (hc : ∀ y y', ∀ u ∈ V y ∩ V y', SameOrbit (μ y u) (μ y' u))
    (hh : ∀ y, SameOrbit (R.lift (h y) (h y)) (μ y y)) : Continuous h := by
  rw [continuous_iff_continuousAt]
  intro y
  rw [ContinuousAt, tendsto_iff_ultrafilter]
  intro F hF
  obtain ⟨x, -, hx⟩ := isCompact_univ.ultrafilter_le_nhds (F.map h) (by simp)
  have hth : Tendsto h F (𝓝 x) := hx
  have hUx : ∀ᶠ y' in (F : Filter Y), h y' ∈ R.U x := hth ((R.isOpen_U x).mem_nhds (R.mem_U x))
  have hVy : ∀ᶠ y' in (F : Filter Y), y' ∈ V y := hF ((hVo y).mem_nhds (hVm y))
  have hcr : ∀ k (i i' : ι k), R.lift x x ⟨k, i⟩ * μ y y ⟨k, i'⟩ =
      R.lift x x ⟨k, i'⟩ * μ y y ⟨k, i⟩ := by
    intro k i i'
    have t1 : ∀ q, Tendsto (fun y' => R.lift x (h y') q) F (𝓝 (R.lift x x q)) := fun q =>
      (Proj.continuousAt_of_holoOn R.A (R.holo x q) (R.mem_U x)).tendsto.comp hth
    have t2 : ∀ q, Tendsto (fun y' => μ y y' q) F (𝓝 (μ y y q)) := fun q =>
      (Proj.continuousAt_of_holoOn B (hμ y q) (hVm y)).tendsto.mono_left hF
    refine tendsto_nhds_unique ((t1 ⟨k, i⟩).mul (t2 ⟨k, i'⟩))
      (((t1 ⟨k, i'⟩).mul (t2 ⟨k, i⟩)).congr' ?_)
    filter_upwards [hUx, hVy] with y' h1 h2
    exact Proj.orbit_cross (Proj.local_orbit R hVm hc hh h1 h2) k i' i
  have hxy : SameOrbit (R.lift x x) (μ y y) :=
    Proj.orbit_of_cross (R.mem x x (R.mem_U x)).1 (hne y) hcr
  have hxe : x = h y :=
    R.inj x (h y) (Proj.not_mem_mcPts_top _) (Proj.orbit_trans hxy (Proj.orbit_symm (hh y)))
  rw [← hxe]
  exact hx

end Orbit

theorem holoMap_of_local_analytic : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (P J : Ideal (MRing ι)) (P' J' : Ideal (MRing ι')) (D D' : ℕ) (R : AnLogRes P J D) (R' : AnLogRes P' J' D') (g : R'.X → R.X), J = ⊤ → (∀ x, ∃ (V : Set ((Σ k, ι' k) → ℂ)) (f : ((Σ k, ι' k) → ℂ) → (Σ k, ι k) → ℂ), IsOpen V ∧ R'.lift x x ∈ V ∧ AnalyticOnNhd ℂ f V ∧ ∀ z' ∈ V ∩ mcPts P', ∀ x', SameOrbit z' (R'.lift x' x') → SameOrbit (f z') (R.lift (g x') (g x'))) → HoloMap R'.A R.A g := by
  intro K _ ι _ K' _ ι' _ P J P' J' D D' R R' g hJ hg
  subst hJ
  choose Vs f hVs hxV hf hcomp using hg
  have hcl : ∀ y, ContinuousOn (R'.lift y) (R'.U y) := fun y =>
    continuousOn_pi.2 fun p x hx =>
      (Proj.continuousAt_of_holoOn R'.A (R'.holo y p) hx).continuousWithinAt
  let V : R'.X → Set R'.X := fun y => R'.U y ∩ R'.lift y ⁻¹' Vs y
  let μ : R'.X → R'.X → (Σ k, ι k) → ℂ := fun y u => f y (R'.lift y u)
  have hVo : ∀ y, IsOpen (V y) := fun y =>
    (hcl y).isOpen_inter_preimage (R'.isOpen_U y) (hVs y)
  have hVm : ∀ y, y ∈ V y := fun y => ⟨R'.mem_U y, hxV y⟩
  have hμ : ∀ y q, R'.A.HoloOn (V y) fun u => μ y u q := by
    rintro y q j w ⟨hw, hwV⟩
    have h1 : AnalyticAt ℂ (fun w' => R'.lift y ((R'.A.chart j).symm w')) w :=
      AnalyticAt.pi fun p => R'.holo y p j w ⟨hw, hwV.1⟩
    have h2 : AnalyticAt ℂ (f y ∘ fun w' => R'.lift y ((R'.A.chart j).symm w')) w :=
      AnalyticAt.comp (hf y _ hwV.2) h1
    exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ k, ι k) => ℂ) q).analyticAt _ |>.comp h2
  have hor : ∀ y, ∀ u ∈ V y, SameOrbit (μ y u) (R.lift (g u) (g u)) := fun y u hu =>
    hcomp y _ ⟨hu.2, R'.mem y u hu.1⟩ u (R'.compat y u u ⟨hu.1, R'.mem_U u⟩)
  have hc : ∀ y y', ∀ u ∈ V y ∩ V y', SameOrbit (μ y u) (μ y' u) := fun y y' u hu =>
    Proj.orbit_trans (hor y u hu.1) (Proj.orbit_symm (hor y' u hu.2))
  have hh : ∀ y, SameOrbit (R.lift (g y) (g y)) (μ y y) := fun y =>
    Proj.orbit_symm (hor y y (hVm y))
  have hne : ∀ y k, ∃ i, μ y y ⟨k, i⟩ ≠ 0 := fun y k => by
    obtain ⟨i, hi⟩ := (R.mem (g y) (g y) (R.mem_U _)).1 k
    exact ⟨i, Proj.orbit_ne (hh y) hi⟩
  have hcont : Continuous g := continuous_of_orbit_of_ne R R'.A hVo hVm hμ hne hc hh
  exact ⟨hcont, Proj.analytic_of_orbit R R'.A hVo hVm hμ hc hh hcont⟩

end GlobalTheory.CompanionTheory.Ar.PB.CovMap
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.PointsIntegralZeroOfLocallyConstantStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.points_integral_zero_of_locally_constant : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ) (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (g : ((Σ k, ι k) → ℂ) → ℝ) (j : Fin e), (∀ z ∈ mcPts P, ∃ c : ℝ, φ j =ᶠ[𝓝 z] fun _ => c) → ptsIntegral P φ g = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.ptsIntegral_eq_zero_of_locConst | exact GlobalTheory.CompanionTheory.Ar.Giv.ptsIntegral_eq_zero_of_locConst | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.ptsIntegral_eq_zero_of_locConst <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.PullbackStatementHoldsStatement
section
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_statement_holds : PullbackStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.pullbackStatement | exact GlobalTheory.CompanionTheory.Ar.Giv.pullbackStatement | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.pullbackStatement <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.RealPartGramInSymplecticGroup
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

namespace GlobalTheory.CompanionTheory.Ar.NformRed

open scoped Matrix

variable {g : ℕ}

theorem hermForm_sum_left {κ : Type*} [Fintype κ] (Hm : Matrix (Fin g) (Fin g) ℂ) (a : κ → ℤ)
    (x : κ → Fin g → ℂ) (w : Fin g → ℂ) :
    hermForm Hm (∑ i, a i • x i) w = ∑ i, (a i : ℂ) * hermForm Hm (x i) w := by
  simp only [hermForm, sum_dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_dotProduct, zsmul_eq_mul]

theorem hermForm_sum_right {κ : Type*} [Fintype κ] (Hm : Matrix (Fin g) (Fin g) ℂ) (b : κ → ℤ)
    (y : κ → Fin g → ℂ) (z : Fin g → ℂ) :
    hermForm Hm z (∑ j, b j • y j) = ∑ j, (b j : ℂ) * hermForm Hm z (y j) := by
  have hs : star (∑ j, b j • y j) = ∑ j, b j • star (y j) := by
    simp [star_sum, star_smul]
  simp only [hermForm]
  rw [hs, Matrix.mulVec_sum, dotProduct_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.mulVec_smul, dotProduct_smul, zsmul_eq_mul]

theorem hermForm_sum_sum {κ : Type*} [Fintype κ] (Hm : Matrix (Fin g) (Fin g) ℂ) (a b : κ → ℤ)
    (x : κ → Fin g → ℂ) :
    hermForm Hm (∑ i, a i • x i) (∑ j, b j • x j) =
      ∑ i, ∑ j, (a i : ℂ) * (b j : ℂ) * hermForm Hm (x i) (x j) := by
  rw [hermForm_sum_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hermForm_sum_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem re_int_mul (m n : ℤ) (c : ℂ) :
    ((m : ℂ) * (n : ℂ) * c).re = (m : ℝ) * (n : ℝ) * c.re := by
  simp [Complex.mul_re]

theorem im_int_mul (m n : ℤ) (c : ℂ) :
    ((m : ℂ) * (n : ℂ) * c).im = (m : ℝ) * (n : ℝ) * c.im := by
  simp [Complex.mul_im]

theorem congr_apply {κ : Type*} [Fintype κ] (P : Matrix κ κ ℤ) (M : Matrix κ κ ℝ) (α δ : κ) :
    (P.map (Int.cast : ℤ → ℝ) * M * (P.map (Int.cast : ℤ → ℝ))ᵀ) α δ =
      ∑ β, ∑ ε, (P α β : ℝ) * (P δ ε : ℝ) * M β ε := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun ε _ => ?_
  ring

theorem J_map_int : (Matrix.J (Fin g) ℤ).map (Int.cast : ℤ → ℝ) = Matrix.J (Fin g) ℝ :=
  Matrix.map_J (Fin g) (Int.castRingHom ℝ)

theorem cast_symplectic {P : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    (hP : P ∈ Matrix.symplecticGroup (Fin g) ℤ) :
    P.map (Int.cast : ℤ → ℝ) * Matrix.J (Fin g) ℝ * (P.map (Int.cast : ℤ → ℝ))ᵀ =
      Matrix.J (Fin g) ℝ := by
  have h := SymplecticGroup.mem_iff.1 hP
  have h2 := congrArg (fun M => M.map (Int.castRingHom ℝ)) h
  simp only [Matrix.map_mul] at h2
  have e : (Int.castRingHom ℝ : ℤ → ℝ) = (Int.cast : ℤ → ℝ) := rfl
  rw [e, J_map_int, Matrix.transpose_map] at h2
  exact h2

theorem left_inv_transpose {P : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    (hP : P ∈ Matrix.symplecticGroup (Fin g) ℤ) :
    (-(Matrix.J (Fin g) ℤ * P * Matrix.J (Fin g) ℤ)) * Pᵀ = 1 := by
  have h := SymplecticGroup.mem_iff.1 hP
  have : Matrix.J (Fin g) ℤ * P * Matrix.J (Fin g) ℤ * Pᵀ =
      Matrix.J (Fin g) ℤ * (P * Matrix.J (Fin g) ℤ * Pᵀ) := by
    simp only [Matrix.mul_assoc]
  rw [Matrix.neg_mul, this, h, Matrix.J_squared, neg_neg]

noncomputable def twist {κ M : Type*} [Fintype κ] [DecidableEq κ] [AddCommGroup M]
    (b : Module.Basis κ ℤ M) (P Q : Matrix κ κ ℤ) (h : Q * Pᵀ = 1) : Module.Basis κ ℤ M :=
  b.map (b.equivFun.trans ((Matrix.toLinearEquiv' Pᵀ ⟨Q, h, mul_eq_one_comm.1 h⟩).trans
    b.equivFun.symm))

theorem twist_apply {κ M : Type*} [Fintype κ] [DecidableEq κ] [AddCommGroup M]
    (b : Module.Basis κ ℤ M) (P Q : Matrix κ κ ℤ) (h : Q * Pᵀ = 1) (α : κ) :
    twist b P Q h α = ∑ β, P α β • b β := by
  have h1 : b.equivFun (b α) = Pi.single α 1 := by
    ext j
    simp [Module.Basis.equivFun_apply, Finsupp.single_apply, Pi.single_apply, eq_comm]
  simp only [twist, Module.Basis.map_apply, LinearEquiv.trans_apply, h1,
    Module.Basis.equivFun_symm_apply]
  refine Finset.sum_congr rfl fun β _ => ?_
  change (Pᵀ *ᵥ Pi.single α 1) β • b β = _
  rw [Matrix.mulVec_single_one]
  rfl

theorem coe_sum_smul {n : ℕ} {κ : Type*} [Fintype κ] (Λ : Submodule ℤ (Fin n → ℂ)) (v : κ → ℤ)
    (x : κ → Λ) : ((∑ α, v α • x α : Λ) : Fin n → ℂ) = ∑ α, v α • (x α : Fin n → ℂ) := by
  simp [Submodule.coe_sum]

theorem symplectic_reduction_basis :
    ∀ (g : ℕ) [NeZero g] (Λ : Submodule ℤ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ)
    (bs : Module.Basis (Fin g ⊕ Fin g) ℤ Λ),
    Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) →
    (∀ α β, (hermForm Hm (bs α : Fin g → ℂ) (bs β : Fin g → ℂ)).im = Matrix.J (Fin g) ℝ α β) →
    (Matrix.of fun α β => (hermForm Hm (bs α : Fin g → ℂ) (bs β : Fin g → ℂ)).re) ∈ Matrix.symplecticGroup (Fin g) ℝ →
    (Matrix.of fun α β => (hermForm Hm (bs α : Fin g → ℂ) (bs β : Fin g → ℂ)).re).PosDef →
    ∃ (bs' : Module.Basis (Fin g ⊕ Fin g) ℤ Λ) (ρ : ℝ),
      0 < ρ ∧ ρ ^ 2 ≤ 2 * g ∧
      (∀ α β, (hermForm Hm (bs' α : Fin g → ℂ) (bs' β : Fin g → ℂ)).im = Matrix.J (Fin g) ℝ α β) ∧
      (hermForm Hm (bs' (Sum.inl 0) : Fin g → ℂ) (bs' (Sum.inl 0) : Fin g → ℂ)).re = ρ ^ 2 ∧
      (∀ l : Λ, l ≠ 0 → ρ ^ 2 ≤ (hermForm Hm (l : Fin g → ℂ) (l : Fin g → ℂ)).re) ∧
      (Matrix.of fun i j : Fin g => (hermForm Hm (bs' (Sum.inl i) : Fin g → ℂ) (bs' (Sum.inl j) : Fin g → ℂ)).re).det ≤
        ρ ^ 2 * (2 * g) ^ (g - 1) := by
  intro g _ Λ Hm bs hHm hpos him hsymp hposdef
  set G : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ :=
    Matrix.of fun α β => (hermForm Hm (bs α : Fin g → ℂ) (bs β : Fin g → ℂ)).re with hG
  obtain ⟨ρsq, hleast, hle, P, hP, hfirst, hdet⟩ := SymplecticReduction.full g G hsymp hposdef
  have hqf : ∀ v : Fin g ⊕ Fin g → ℤ, qf G (intVec v) =
      (hermForm Hm (∑ α, v α • (bs α : Fin g → ℂ)) (∑ α, v α • (bs α : Fin g → ℂ))).re := by
    intro v
    rw [hermForm_sum_sum, Complex.re_sum]
    simp only [Complex.re_sum, re_int_mul, qf, intVec, dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [hG, Matrix.of_apply]
    ring
  have hne : ∀ v : Fin g ⊕ Fin g → ℤ, v ≠ 0 → ∑ α, v α • (bs α : Fin g → ℂ) ≠ 0 := by
    intro v hv h0
    apply hv
    have h1 : (∑ α, v α • bs α : Λ) = 0 := by
      apply Subtype.ext
      rw [coe_sum_smul]
      exact h0
    funext α
    exact Fintype.linearIndependent_iff.1 bs.linearIndependent v h1 α
  have hρpos : 0 < ρsq := by
    obtain ⟨v, hv, hval⟩ := hleast.1
    rw [hval, hqf]
    exact hpos _ (hne v hv)
  have hb' : ∀ α, ((twist bs P _ (left_inv_transpose hP) α : Λ) : Fin g → ℂ) =
      ∑ β, P α β • (bs β : Fin g → ℂ) := by
    intro α
    rw [twist_apply, coe_sum_smul]
  have hre : ∀ α δ, (hermForm Hm ((twist bs P _ (left_inv_transpose hP) α : Λ) : Fin g → ℂ)
      ((twist bs P _ (left_inv_transpose hP) δ : Λ) : Fin g → ℂ)).re =
      (P.map (Int.cast : ℤ → ℝ) * G * (P.map (Int.cast : ℤ → ℝ))ᵀ) α δ := by
    intro α δ
    rw [hb', hb', hermForm_sum_sum, congr_apply]
    simp only [Complex.re_sum, re_int_mul, hG, Matrix.of_apply]
  have him' : ∀ α δ, (hermForm Hm ((twist bs P _ (left_inv_transpose hP) α : Λ) : Fin g → ℂ)
      ((twist bs P _ (left_inv_transpose hP) δ : Λ) : Fin g → ℂ)).im = Matrix.J (Fin g) ℝ α δ := by
    intro α δ
    rw [hb', hb', hermForm_sum_sum, ← cast_symplectic hP, congr_apply]
    simp only [Complex.im_sum, im_int_mul, him]
  refine ⟨twist bs P _ (left_inv_transpose hP), Real.sqrt ρsq, Real.sqrt_pos.2 hρpos, ?_, him', ?_,
    ?_, ?_⟩
  · rw [Real.sq_sqrt hρpos.le]
    exact hle
  · rw [Real.sq_sqrt hρpos.le, hre]
    exact hfirst
  · intro l hl
    rw [Real.sq_sqrt hρpos.le]
    have hv : (fun α => bs.repr l α) ≠ 0 := by
      intro h0
      apply hl
      have : bs.repr l = 0 := by
        ext α
        exact congrFun h0 α
      simpa using this
    have hsum : (l : Fin g → ℂ) = ∑ α, bs.repr l α • (bs α : Fin g → ℂ) := by
      rw [← coe_sum_smul, bs.sum_repr]
    rw [hsum, ← hqf (fun α => bs.repr l α)]
    exact hleast.2 ⟨_, hv, rfl⟩
  · rw [Real.sq_sqrt hρpos.le]
    have : (Matrix.of fun i j : Fin g =>
        (hermForm Hm ((twist bs P _ (left_inv_transpose hP) (Sum.inl i) : Λ) : Fin g → ℂ)
          ((twist bs P _ (left_inv_transpose hP) (Sum.inl j) : Λ) : Fin g → ℂ)).re) =
        (P.map (Int.cast : ℤ → ℝ) * G * (P.map (Int.cast : ℤ → ℝ))ᵀ).toBlocks₁₁ := by
      ext i j
      simp only [Matrix.of_apply, hre, Matrix.toBlocks₁₁]
    rw [this]
    exact hdet

end GlobalTheory.CompanionTheory.Ar.NformRed
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.RealisationPotentialDegreeCompatibilityStatement
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realisation_potential_degree_compatibility : ResExistsStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (D : ℕ) (σ : Type) [Fintype σ] (S : AnSys D σ) (P : Ideal (MRing ι)) (Re : Realis S P), (∀ a t, 0 < t → t ≤ S.t₀ → SamePot Re.R.A Set.univ (potOf Re.R (Re.line a t)) ((S.potT a t).pullback Re.π Re.holo.1)) ∧ (∀ (w : Fin D → σ), ptsIntegral P (pot fun j => Re.ref (w j)) (fun _ => 1) = Re.deg * S.degNum w) ∧ (∀ (w : Fin D → σ) (t : Fin D → ℝ), (∀ j, 0 < t j ∧ t j ≤ S.t₀) → ptsIntegral P (pot fun j => Re.line (w j) (t j)) (fun _ => 1) = Re.deg * S.degNum w) ∧ ∀ n : σ → ℤ, IsSmoothHerm (combLine Re.ref n) ∧ geomDeg P (combLine Re.ref n) D = Re.deg * eval (fun a => (n a : ℝ)) S.degPoly := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.re_pot | exact GlobalTheory.CompanionTheory.Ar.PB.re_pot | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.re_pot <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SemicharacterThetaCharacteristic
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

namespace GlobalTheory.CompanionTheory.Ar.Nform

theorem exists_half_canMult : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (bs : Module.Basis (Fin g ⊕ Fin g) ℤ Λ) (χ : Λ → ℂ),
    (∀ l l' : Λ, χ (l + l') = χ l * χ l' * Complex.exp (Real.pi * Complex.I *
      (((∑ i, (bs.repr l (Sum.inr i) * bs.repr l' (Sum.inl i) - bs.repr l (Sum.inl i) * bs.repr l' (Sum.inr i)) : ℤ) : ℝ) : ℂ))) →
    (∀ l, χ l ^ 2 = 1) →
    ∃ a c : Fin g → ℝ, (∀ i, a i = 0 ∨ a i = 1 / 2) ∧ (∀ i, c i = 0 ∨ c i = 1 / 2) ∧
      ∀ x, χ x = GlobalTheory.CanTh.canMult a c (fun i => bs.repr x (Sum.inl i)) (fun i => bs.repr x (Sum.inr i)) := by
  intro g Λ bs χ hχ hsq
  classical
  have hpm : ∀ l, χ l = 1 ∨ χ l = -1 := fun l =>
    mul_self_eq_one_iff.mp (by rw [← sq]; exact hsq l)
  have hexp : ∀ k : ℤ, Complex.exp (↑Real.pi * Complex.I * ((k : ℝ) : ℂ)) = (-1) ^ k := by
    intro k
    rw [Complex.ofReal_intCast, mul_comm, Complex.exp_int_mul, Complex.exp_pi_mul_I]
  have hhalf : Complex.exp (2 * ↑Real.pi * Complex.I * ((1 / 2 : ℝ) : ℂ)) = -1 := by
    rw [show (2 : ℂ) * ↑Real.pi * Complex.I * ((1 / 2 : ℝ) : ℂ) = ↑Real.pi * Complex.I by
      push_cast; ring, Complex.exp_pi_mul_I]
  have hhalf' : Complex.exp (-(2 * ↑Real.pi * Complex.I * ((1 / 2 : ℝ) : ℂ))) = -1 := by
    rw [Complex.exp_neg, hhalf]
    norm_num
  have hsame : ∀ j k : Fin g ⊕ Fin g, bs.repr (bs j) k = if j = k then 1 else 0 := by
    intro j k
    rw [Module.Basis.repr_self, Finsupp.single_apply]
  have hsingle : ∀ i : Fin g, (fun k => bs.repr (bs (Sum.inl i)) (Sum.inl k)) = Pi.single i 1 ∧
      (fun k => bs.repr (bs (Sum.inl i)) (Sum.inr k)) = 0 ∧
      (fun k => bs.repr (bs (Sum.inr i)) (Sum.inl k)) = 0 ∧
      (fun k => bs.repr (bs (Sum.inr i)) (Sum.inr k)) = Pi.single i 1 := by
    intro i
    refine ⟨funext fun k => ?_, funext fun k => ?_, funext fun k => ?_, funext fun k => ?_⟩ <;>
      by_cases hk : k = i
    · subst hk; simp [hsame]
    · simp [hsame, Pi.single_apply, hk, Ne.symm hk]
    · simp [hsame]
    · simp [hsame]
    · simp [hsame]
    · simp [hsame]
    · subst hk; simp [hsame]
    · simp [hsame, Pi.single_apply, hk, Ne.symm hk]
  have hdot : ∀ (a : Fin g → ℝ) (i : Fin g),
      (a ⬝ᵥ fun k => (((Pi.single i 1 : Fin g → ℤ) k : ℤ) : ℝ)) = a i := by
    intro a i
    simp [dotProduct, Pi.single_apply]
  have hdot0 : ∀ a : Fin g → ℝ, (a ⬝ᵥ fun k => (((0 : Fin g → ℤ) k : ℤ) : ℝ)) = 0 := by
    intro a
    simp [dotProduct]
  have hC_inl : ∀ (a c : Fin g → ℝ) (i : Fin g),
      GlobalTheory.CanTh.canMult a c (fun k => bs.repr (bs (Sum.inl i)) (Sum.inl k))
        (fun k => bs.repr (bs (Sum.inl i)) (Sum.inr k)) =
        Complex.exp (2 * ↑Real.pi * Complex.I * ((a i : ℝ) : ℂ)) := by
    intro a c i
    obtain ⟨h1, h2, -, -⟩ := hsingle i
    rw [h1, h2]
    simp only [GlobalTheory.CanTh.canMult, dotProduct_zero, hdot, hdot0]
    congr 1
    push_cast
    ring
  have hC_inr : ∀ (a c : Fin g → ℝ) (i : Fin g),
      GlobalTheory.CanTh.canMult a c (fun k => bs.repr (bs (Sum.inr i)) (Sum.inl k))
        (fun k => bs.repr (bs (Sum.inr i)) (Sum.inr k)) =
        Complex.exp (-(2 * ↑Real.pi * Complex.I * ((c i : ℝ) : ℂ))) := by
    intro a c i
    obtain ⟨-, -, h3, h4⟩ := hsingle i
    rw [h3, h4]
    simp only [GlobalTheory.CanTh.canMult, zero_dotProduct, hdot, hdot0]
    congr 1
    push_cast
    ring
  obtain ⟨a, ha⟩ : ∃ a : Fin g → ℝ, a = fun i => if χ (bs (Sum.inl i)) = 1 then 0 else 1 / 2 :=
    ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : Fin g → ℝ, c = fun i => if χ (bs (Sum.inr i)) = 1 then 0 else 1 / 2 :=
    ⟨_, rfl⟩
  refine ⟨a, c, fun i => ?_, fun i => ?_, ?_⟩
  · simp only [ha]
    split_ifs <;> norm_num
  · simp only [hc]
    split_ifs <;> norm_num
  have hχ0 : ∀ l, χ l ≠ 0 := by
    intro l h
    have h' := hsq l
    rw [h] at h'
    norm_num at h'
  have hψ0 : ∀ l : Λ, GlobalTheory.CanTh.canMult a c (fun i => bs.repr l (Sum.inl i))
      (fun i => bs.repr l (Sum.inr i)) ≠ 0 := by
    intro l
    simp only [GlobalTheory.CanTh.canMult]
    exact Complex.exp_ne_zero _
  have hψ : ∀ l l' : Λ,
      GlobalTheory.CanTh.canMult a c (fun i => bs.repr (l + l') (Sum.inl i))
                   (fun i => bs.repr (l + l') (Sum.inr i)) =
        GlobalTheory.CanTh.canMult a c (fun i => bs.repr l (Sum.inl i))
                     (fun i => bs.repr l (Sum.inr i)) *
          GlobalTheory.CanTh.canMult a c (fun i => bs.repr l' (Sum.inl i))
            (fun i => bs.repr l' (Sum.inr i)) *
          Complex.exp (Real.pi * Complex.I *
            (((∑ i, (bs.repr l (Sum.inr i) * bs.repr l' (Sum.inl i) -
              bs.repr l (Sum.inl i) * bs.repr l' (Sum.inr i)) : ℤ) : ℝ) : ℂ)) := by
    intro l l'
    have hm : (fun i => bs.repr (l + l') (Sum.inl i)) =
        (fun i => bs.repr l (Sum.inl i)) + (fun i => bs.repr l' (Sum.inl i)) := by
      funext i
      simp [map_add]
    have hn : (fun i => bs.repr (l + l') (Sum.inr i)) =
        (fun i => bs.repr l (Sum.inr i)) + (fun i => bs.repr l' (Sum.inr i)) := by
      funext i
      simp [map_add]
    rw [hm, hn, GlobalTheory.HolTheta.canMult_add, hexp, Finset.sum_sub_distrib]
    rfl
  have hbasis : ∀ j : Fin g ⊕ Fin g, χ (bs j) =
      GlobalTheory.CanTh.canMult a c (fun i => bs.repr (bs j) (Sum.inl i))
        (fun i => bs.repr (bs j) (Sum.inr i)) := by
    rintro (i | i)
    · rw [hC_inl]
      rcases hpm (bs (Sum.inl i)) with h | h
      · simp [ha, h]
      · have h' : χ (bs (Sum.inl i)) ≠ 1 := by rw [h]; norm_num
        simp only [ha, h', if_false]
        rw [h, hhalf]
    · rw [hC_inr]
      rcases hpm (bs (Sum.inr i)) with h | h
      · simp [hc, h]
      · have h' : χ (bs (Sum.inr i)) ≠ 1 := by rw [h]; norm_num
        simp only [hc, h', if_false]
        rw [h, hhalf']
  exact GlobalTheory.HolTheta.eq_of_cocycle bs
    (fun l l' => Complex.exp (Real.pi * Complex.I *
      (((∑ i, (bs.repr l (Sum.inr i) * bs.repr l' (Sum.inl i) -
        bs.repr l (Sum.inl i) * bs.repr l' (Sum.inr i)) : ℤ) : ℝ) : ℂ)))
    (ψ := fun l => GlobalTheory.CanTh.canMult a c (fun i => bs.repr l (Sum.inl i))
      (fun i => bs.repr l (Sum.inr i)))
    (fun _ _ => Complex.exp_ne_zero _) hχ0 hψ0 hχ hψ hbasis

end GlobalTheory.CompanionTheory.Ar.Nform
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwoPointFibreChartFirstStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_point_fibre_chart_first : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a ca cb : Fin N) (X : Type) (q : Fin 2 → X → FA.S.X) (Un : Set (Fin d → ℂ)) (Gn : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (ΦYn : (Fin (d + 1) → ℂ) → FA.S.X) (ΦWn : (Fin (d + 2) → ℂ) → X) (l : Fin BM.q) (H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ) (bp : (Fin d → ℂ) → BM.Rb.X), IsOpen Un → IsFibreData FA τ a ca cb q Un Gn ΦYn ΦWn l H bp → ∃ zex : (Fin (d + 1) → ℂ) → (Σ k, ι k) → ℂ, (∀ q', AnalyticOnNhd ℂ (fun u => zex u q') {u : Fin (d + 1) → ℂ | Fin.tail u ∈ Un}) ∧ ∀ u : Fin (d + 1) → ℂ, Fin.tail u ∈ Un → zex u ∈ mcPts (mCoordIdeal y) ∧ ∀ x₀, FA.Re.π x₀ = ΦYn u → SameOrbit (FA.Re.R.lift x₀ x₀) (zex u) ∧ SameOrbit (basePart M.blk (zex u)) (BM.Rb.lift (bp (Fin.tail u)) (bp (Fin.tail u))) ∧ ∀ τ' i, M.ExactAt (BM.F l) (τ', i) (zex u) (flagAt H τ ca cb (u 0) (Fin.tail u) τ') := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.exact_points_holomorphic | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.exact_points_holomorphic | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.exact_points_holomorphic <;> assumption)
end

