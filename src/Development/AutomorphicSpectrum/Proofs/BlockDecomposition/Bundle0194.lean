import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.UnitTestFunctions.LiftUnit
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CechDifferentialPullback.Bridge
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0187
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0189
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0042
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0044
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0092
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0023
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.NefRR
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0007
import GroundTheory.GlobalFields.TateThesis.GlobalZetaInfinite
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0188
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BumpProfileEqZeroOfLtHalf
section
open PositivityTheory.RgEis PositivityTheory.RgEis.TF

noncomputable section

namespace GlobalTheory.CompanionTheory.TestFun

theorem contDiff_mul_of_vanish {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {N : E → ℝ} (hN : ContDiff ℝ (⊤ : ℕ∞) N) {φ : ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ0 : ∀ s, s < 1 / 2 → φ s = 0) {H : E → ℝ}
    (hH : ∀ y, 0 < N y → ContDiffAt ℝ (⊤ : ℕ∞) H y) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y => φ (N y) * H y) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : 0 < N y
  · exact (hφ.comp hN).contDiffAt.mul (hH y hy)
  · have hlt : N y < 1 / 2 := by linarith [not_lt.mp hy]
    have hev : ∀ᶠ z in nhds y, N z < 1 / 2 :=
      hN.continuous.continuousAt.eventually (gt_mem_nhds hlt)
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [hev] with z hz
    simp [hφ0 _ hz]

def sqSum {ι : Type} [Fintype ι] (y : ι → ℝ) : ℝ := ∑ j, y j ^ 2

theorem sqSum_contDiff {ι : Type} [Fintype ι] : ContDiff ℝ (⊤ : ℕ∞) (sqSum (ι := ι)) := by
  unfold sqSum
  exact ContDiff.sum fun j _ => (contDiff_apply ℝ ℝ j).pow 2

theorem sqSum_smul {ι : Type} [Fintype ι] (t : ℝ) (v : ι → ℝ) :
    sqSum (t • v) = t ^ 2 * sqSum v := by
  unfold sqSum
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by simp [mul_pow]

theorem sq_le_sqSum {ι : Type} [Fintype ι] (y : ι → ℝ) (j : ι) : y j ^ 2 ≤ sqSum y := by
  unfold sqSum
  exact Finset.single_le_sum (f := fun j => y j ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ j)

theorem hasCompactSupport_of_sqSum {ι : Type} [Fintype ι] {F : (ι → ℝ) → ℝ}
    (h : ∀ y, 2 < sqSum y → F y = 0) : HasCompactSupport F := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ι → ℝ) 2) ?_
  intro y hy
  apply h
  have hn : (2 : ℝ) < ‖y‖ := by simpa [mem_closedBall_zero_iff] using hy
  have : ∃ j, 2 < |y j| := by
    by_contra hc
    push Not at hc
    have : ‖y‖ ≤ 2 := (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun j => by
      simpa [Real.norm_eq_abs] using hc j
    linarith
  obtain ⟨j, hj⟩ := this
  have h4 : (2 : ℝ) ^ 2 < y j ^ 2 := by
    rw [← sq_abs (y j)]
    exact pow_lt_pow_left₀ hj (by norm_num) (by norm_num)
  linarith [sq_le_sqSum y j]

def phi0 : ContDiffBump (1 : ℝ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

theorem bumpProfile_one : phi0 1 = 1 :=
  phi0.one_of_mem_closedBall (by simp [phi0])

theorem bumpProfile_eq_zero_of_lt_half (s : ℝ) (hs : s < 1 / 2) : phi0 s = 0 := by
  refine phi0.zero_of_le_dist ?_
  show (1 / 2 : ℝ) ≤ dist s 1
  rw [Real.dist_eq, abs_sub_comm]
  exact le_trans (by linarith) (le_abs_self _)

theorem bumpProfile_eq_zero_of_two_lt (s : ℝ) (hs : 2 < s) : phi0 s = 0 := by
  refine phi0.zero_of_le_dist ?_
  show (1 / 2 : ℝ) ≤ dist s 1
  rw [Real.dist_eq]
  exact le_trans (by linarith) (le_abs_self _)

theorem bumpProfile_contDiff : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => phi0 s) := phi0.contDiff

def bumpAt (δ : ℝ) (hδ : 0 < δ) : ContDiffBump (1 : ℝ) :=
  ⟨δ / 2, δ, half_pos hδ, half_lt_self hδ⟩

theorem bumpAt_one (δ : ℝ) (hδ : 0 < δ) : bumpAt δ hδ 1 = 1 :=
  (bumpAt δ hδ).one_of_mem_closedBall (by simp [bumpAt]; linarith)

theorem bumpAt_ne (δ : ℝ) (hδ : 0 < δ) {s : ℝ} (h : bumpAt δ hδ s ≠ 0) : 1 - δ < s := by
  by_contra hc
  refine h ((bumpAt δ hδ).zero_of_le_dist ?_)
  show δ ≤ dist s 1
  rw [Real.dist_eq, abs_sub_comm]
  exact le_trans (by linarith [not_lt.mp hc]) (le_abs_self _)

def angular {ι : Type} [Fintype ι] (i₀ : ι) (m : ℕ) (δ : ℝ) (hδ : 0 < δ) (y : ι → ℝ) : ℝ :=
  bumpAt δ hδ (y i₀ ^ 2 / sqSum y) * (y i₀ / Real.sqrt (sqSum y)) ^ m

theorem angular_contDiffAt {ι : Type} [Fintype ι] (i₀ : ι) (m : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (y : ι → ℝ) (hy : 0 < sqSum y) : ContDiffAt ℝ (⊤ : ℕ∞) (angular i₀ m δ hδ) y := by
  have hN : ContDiffAt ℝ (⊤ : ℕ∞) (sqSum (ι := ι)) y := sqSum_contDiff.contDiffAt
  have hc : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : ι → ℝ => y i₀) y := (contDiff_apply ℝ ℝ i₀).contDiffAt
  have hq : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : ι → ℝ => y i₀ ^ 2 / sqSum y) y :=
    (hc.pow 2).div hN hy.ne'
  have hbc : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => bumpAt δ hδ s) := (bumpAt δ hδ).contDiff
  have hb : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : ι → ℝ => bumpAt δ hδ (y i₀ ^ 2 / sqSum y)) y :=
    ContDiff.comp_contDiffAt (g := fun s : ℝ => bumpAt δ hδ s)
      (f := fun y : ι → ℝ => y i₀ ^ 2 / sqSum y) y hbc hq
  have hs : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : ι → ℝ => Real.sqrt (sqSum y)) y := hN.sqrt hy.ne'
  exact hb.mul ((hc.div hs (Real.sqrt_pos.2 hy).ne').pow m)

def bigF {ι : Type} [Fintype ι] (i₀ : ι) (m : ℕ) (δ : ℝ) (hδ : 0 < δ) (y : ι → ℝ) : ℝ :=
  phi0 (sqSum y) * angular i₀ m δ hδ y

def smallF (m : ℕ) (t : ℝ) : ℝ := phi0 (t ^ 2) * (t / Real.sqrt (t ^ 2)) ^ m

theorem smallF_contDiff (m : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (smallF m) := by
  refine contDiff_mul_of_vanish (N := fun t : ℝ => t ^ 2) (contDiff_id.pow 2) bumpProfile_contDiff
    bumpProfile_eq_zero_of_lt_half (H := fun t => (t / Real.sqrt (t ^ 2)) ^ m) ?_
  intro y hy
  have hN : ContDiffAt ℝ (⊤ : ℕ∞) (fun t : ℝ => t ^ 2) y := (contDiff_id.pow 2).contDiffAt
  exact (contDiffAt_id.div (hN.sqrt hy.ne') (Real.sqrt_pos.2 hy).ne').pow m

theorem smallF_compact (m : ℕ) : HasCompactSupport (smallF m) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) 2) ?_
  intro t ht
  have hn : (2 : ℝ) < |t| := by simpa [mem_closedBall_zero_iff] using ht
  have h4 : (2 : ℝ) ^ 2 < t ^ 2 := by
    rw [← sq_abs t]
    exact pow_lt_pow_left₀ hn (by norm_num) (by norm_num)
  simp [smallF, bumpProfile_eq_zero_of_two_lt (t ^ 2) (by linarith)]

theorem bigF_unit {ι : Type} [Fintype ι] (i₀ : ι) (m : ℕ) (δ : ℝ) (hδ : 0 < δ) (v : ι → ℝ)
    (hv : sqSum v = 1) : bigF i₀ m δ hδ v = bumpAt δ hδ (v i₀ ^ 2) * v i₀ ^ m := by
  simp [bigF, angular, hv, bumpProfile_one]

theorem bigF_smul {ι : Type} [Fintype ι] (i₀ : ι) (m : ℕ) (δ : ℝ) (hδ : 0 < δ) (v : ι → ℝ)
    (hv : sqSum v = 1) (t : ℝ) :
    bigF i₀ m δ hδ (t • v) = smallF m t * bigF i₀ m δ hδ v := by
  rw [bigF_unit i₀ m δ hδ v hv]
  have hN : sqSum (t • v) = t ^ 2 := by rw [sqSum_smul, hv, mul_one]
  by_cases ht : t = 0
  · subst ht
    have h0 : sqSum (0 : ι → ℝ) = 0 := by simp [sqSum]
    simp [bigF, smallF, h0, bumpProfile_eq_zero_of_lt_half 0 (by norm_num)]
  · have ht2 : t ^ 2 ≠ 0 := pow_ne_zero 2 ht
    have hq : (t • v) i₀ ^ 2 / sqSum (t • v) = v i₀ ^ 2 := by
      rw [hN, Pi.smul_apply, smul_eq_mul, mul_pow]
      field_simp
    have hr : (t • v) i₀ / Real.sqrt (sqSum (t • v)) = t / Real.sqrt (t ^ 2) * v i₀ := by
      rw [hN, Pi.smul_apply, smul_eq_mul]
      ring
    simp only [bigF, angular, smallF]
    rw [hq, hr, hN, mul_pow]
    ring

theorem realBump : RealBump := by
  intro ι _ _ i₀ m δ hδ
  have hone : sqSum (Pi.single i₀ (1 : ℝ) : ι → ℝ) = 1 := by
    unfold sqSum
    rw [Finset.sum_eq_single i₀]
    · simp
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · simp
  refine ⟨bigF i₀ m δ hδ, smallF m, ?_, ?_, smallF_contDiff m, smallF_compact m, ?_, ?_, ?_, ?_, ?_⟩
  · exact contDiff_mul_of_vanish sqSum_contDiff bumpProfile_contDiff bumpProfile_eq_zero_of_lt_half
      (angular_contDiffAt i₀ m δ hδ)
  · refine hasCompactSupport_of_sqSum fun y hy => ?_
    simp [bigF, bumpProfile_eq_zero_of_two_lt _ hy]
  · rw [bigF_unit i₀ m δ hδ _ hone]
    simp [bumpAt_one]
  · simp [smallF, bumpProfile_one]
  · intro t ht
    refine mul_nonneg phi0.nonneg (pow_nonneg (div_nonneg ht (Real.sqrt_nonneg _)) m)
  · intro t
    simp only [smallF, neg_sq, neg_div, neg_pow t]
    ring_nf
  · intro v hv
    have hv' : sqSum v = 1 := hv
    refine ⟨bigF_smul i₀ m δ hδ v hv', ?_, ?_⟩
    · intro h
      rw [bigF_unit i₀ m δ hδ v hv'] at h
      exact bumpAt_ne δ hδ (left_ne_zero_of_mul h)
    · intro h
      rw [bigF_unit i₀ m δ hδ v hv']
      exact mul_nonneg (bumpAt δ hδ).nonneg (pow_nonneg h.le m)

end GlobalTheory.CompanionTheory.TestFun
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechSheafCohomologyPullCompat
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull CrystallineSemistableComparison CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Cech

namespace GlobalTheory.CompanionTheory.CechStep

theorem cechHEquivStep_pull {X Y : TopCat.{0}} (f : X ⟶ Y) {κ ι : Type} (V : κ → Opens Y) (U : ι → Opens X) (τ : ι → κ)
    (hτ : ∀ i, U i ≤ (Opens.map f).obj (V (τ i))) {S : ShortComplex (AbSheaf Y)} {S' : ShortComplex (AbSheaf X)}
    (hS : S.ShortExact) [Injective S.X₂] (hC : IsCechShortExact V S.f.hom S.g.hom) (hI : GroundTheory.Arith.SchemeCoh.CechAcyclic S.X₂.obj V)
    (hS' : S'.ShortExact) [Injective S'.X₂] (hC' : IsCechShortExact U S'.f.hom S'.g.hom) (hI' : GroundTheory.Arith.SchemeCoh.CechAcyclic S'.X₂.obj U)
    (α : S ⟶ S'.map (push f)) (m : ℕ) (e : GroundTheory.Arith.SchemeCoh.cechH S.X₃.obj V (m + 1) ≃+ Sheaf.H.{0} S.X₃ (m + 1))
    (e' : GroundTheory.Arith.SchemeCoh.cechH S'.X₃.obj U (m + 1) ≃+ Sheaf.H.{0} S'.X₃ (m + 1))
    (he : ∀ y, e' (cechPullH f α.τ₃.hom V U τ hτ (m + 1) y) = hPull f α.τ₃ (m + 1) (e y))
    (x : GroundTheory.Arith.SchemeCoh.cechH S.X₁.obj V (m + 2)) :
    cechHEquivStep U hS' hC' hI' m e' (cechPullH f α.τ₁.hom V U τ hτ (m + 2) x) =
      hPull f α.τ₁ (m + 2) (cechHEquivStep V hS hC hI m e x) := by
  have h₁₂ : ∀ W z, α.τ₂.hom.app W (S.f.hom.app W z) =
      S'.f.hom.app ((Opens.map f).op.obj W) (α.τ₁.hom.app W z) := fun W z => by
    have h := congrArg (fun k => k.hom.app W) α.comm₁₂
    exact (ConcreteCategory.congr_hom h z).symm
  have h₂₃ : ∀ W z, α.τ₃.hom.app W (S.g.hom.app W z) =
      S'.g.hom.app ((Opens.map f).op.obj W) (α.τ₂.hom.app W z) := fun W z => by
    have h := congrArg (fun k => k.hom.app W) α.comm₂₃
    exact (ConcreteCategory.congr_hom h z).symm
  obtain ⟨y, rfl⟩ := (hC.deltaEquiv hI m).surjective x
  have hδ : (hC'.deltaEquiv hI' m).symm (cechPullH f α.τ₁.hom V U τ hτ (m + 2) (hC.deltaEquiv hI m y)) =
      cechPullH f α.τ₃.hom V U τ hτ (m + 1) y := by
    rw [AddEquiv.symm_apply_eq]
    obtain ⟨σ, hσ, rfl⟩ := GroundTheory.Arith.SchemeCoh.exists_cls y
    exact (GlobalTheory.T.cech_short_exact_pull_compat f V U τ hτ hC hC' α.τ₁.hom α.τ₂.hom α.τ₃.hom h₁₂ h₂₃ (m + 1)
      ⟨σ, (GroundTheory.Arith.SchemeCoh.mem_cocycles σ).2 hσ⟩).trans rfl
  simp only [cechHEquivStep, AddEquiv.trans_apply, AddEquiv.symm_apply_apply, hδ, he]
  exact (GlobalTheory.T.sheaf_pull_connecting_compat f hS hS' α (m + 1) (e y)).symm

end GlobalTheory.CompanionTheory.CechStep
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartLatticeSpanTwistShiftStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_lattice_span_twist_shift : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (D : ℕ), IsArithVar (mCoordIdeal y) (D + 1) → Birational y → ∃ (e : K → ℕ) (c : Ω), c ≠ 0 ∧ ∀ (a : K → ℤ) (τ : ℕ), ∀ s ∈ Submodule.span ℚ (chartLatNm y a τ : Set Ω), c * s ∈ chartLatQ y ((τ : ℤ) • a + fun k => (e k : ℤ)) 1 := by
  first | exact @GlobalTheory.CompanionTheory.Conductor.exists_conductor_section | exact GlobalTheory.CompanionTheory.Conductor.exists_conductor_section | (intros; apply GlobalTheory.CompanionTheory.Conductor.exists_conductor_section <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartOpenMemCoverOfO1Statement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_open_mem_cover_of_O1 : ∀ {K : Type} [Field K] {X : Scheme.{0}} (D : E.LineData X) (N : ℕ) (i : X ⟶ PSpace K N),
    IsTautologicalLineAt D N i → ∀ j, wch i j ∈ 𝒱D D := by
  first | exact @GlobalTheory.CompanionTheory.ConeWchMem.main | exact GlobalTheory.CompanionTheory.ConeWchMem.main | (intros; apply GlobalTheory.CompanionTheory.ConeWchMem.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousInfiniteIdeleInclusion
section
noncomputable section

open NumberField NumberField.mixedEmbedding IsDedekindDomain Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing SchwartzMap Classical

set_option synthInstance.maxSize 1000

namespace GlobalTheory.CompanionTheory.EisTestFun

open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Global.IdeleGroup PositivityTheory.RgEis PositivityTheory.RgEis.TF

variable {k : Type} [Field k] [NumberField k]

theorem continuous_infinite_idele_inclusion :
    Continuous (ofInfinite : (InfiniteAdeleRing k)ˣ → IdeleGroup k) :=
  (ContinuousMulEquiv.symm (prodEquiv k)).continuous.comp (Continuous.prodMk_left 1)

theorem ideleModule_ofInfinite_eq (a : (InfiniteAdeleRing k)ˣ) :
    (ideleModule k (ofInfinite a) : ℝ) = ∏ w : InfinitePlace k, ‖(a : InfiniteAdeleRing k) w‖ ^ w.mult := by
  have h1 : ∀ w, ((ofInfinite a : IdeleGroup k) : 𝔸[k]).1 w = (a : InfiniteAdeleRing k) w := fun w => by
    have := congrArg (fun u : (InfiniteAdeleRing k)ˣ => (u : InfiniteAdeleRing k) w) (toInfinite_ofInfinite a)
    exact this
  have h2 : ∀ v, ((ofInfinite a : IdeleGroup k) : 𝔸[k]).2 v = 1 := fun v => by
    have := congrArg (fun u : (FiniteAdeleRing (𝓞 k) k)ˣ => (u : FiniteAdeleRing (𝓞 k) k) v) (toFinite_ofInfinite a)
    exact this
  rw [ideleModule_eq]
  simp only [h1, h2, norm_one, finprod_one, mul_one]

theorem exists_norm_rd_le (φ : 𝓢(Unit → mixedSpace k, ℂ)) (K : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ x : InfiniteAdeleRing k,
      ‖rd φ (fun _ => x)‖ ≤ C * ∏ w, ((1 + ‖x w‖) ^ K)⁻¹ := by
  let e : mixedSpace k ≃L[ℝ] (Unit → mixedSpace k) :=
    (ContinuousLinearEquiv.funUnique Unit ℝ (mixedSpace k)).symm
  obtain ⟨C, hC, h⟩ := exists_norm_schwartz_le_prod (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e φ) K
  refine ⟨C, hC, fun x => ?_⟩
  have hx := h x
  have he : (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e φ) (homeomorphMixedSpace k x) =
      rd φ (fun _ => x) := by
    simp only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp, rd]
    congr 1
  rwa [he] at hx

theorem module_rpow_eq (a : (InfiniteAdeleRing k)ˣ) (x : ℝ) :
    (ideleModule k (ofInfinite a) : ℝ) ^ x =
      ∏ w : InfinitePlace k, ‖(a : InfiniteAdeleRing k) w‖ ^ ((w.mult : ℝ) * x) := by
  rw [ideleModule_ofInfinite_eq, ← Real.finset_prod_rpow _ _ (fun w _ => by positivity)]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [Real.rpow_mul (norm_nonneg _), Real.rpow_natCast]

theorem integrable_norm_rd_mul (φ : 𝓢(Unit → mixedSpace k, ℂ)) {x : ℝ} (hx : 1 < x)
    (hc : Continuous fun a : (InfiniteAdeleRing k)ˣ =>
      ‖rd φ (fun _ => (a : InfiniteAdeleRing k))‖ * (ideleModule k (ofInfinite a) : ℝ) ^ x) :
    Integrable (fun a : (InfiniteAdeleRing k)ˣ =>
      ‖rd φ (fun _ => (a : InfiniteAdeleRing k))‖ * (ideleModule k (ofInfinite a) : ℝ) ^ x)
      (infiniteIdeleMeasure k) := by
  obtain ⟨K, hK⟩ := exists_nat_gt (2 * x + 2)
  obtain ⟨C, hC, h⟩ := exists_norm_rd_le φ K
  refine Integrable.mono' ((integrable_infiniteZetaBound (K := k) hx.le hK).const_mul C)
    hc.aestronglyMeasurable (Eventually.of_forall fun a => ?_)
  have hm : 0 ≤ (ideleModule k (ofInfinite a) : ℝ) ^ x := Real.rpow_nonneg (ideleModule k (ofInfinite a)).2.le _
  rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) hm)]
  calc ‖rd φ (fun _ => (a : InfiniteAdeleRing k))‖ * (ideleModule k (ofInfinite a) : ℝ) ^ x
      ≤ (C * ∏ w, ((1 + ‖(a : InfiniteAdeleRing k) w‖) ^ K)⁻¹) * (ideleModule k (ofInfinite a) : ℝ) ^ x :=
        mul_le_mul_of_nonneg_right (h a) hm
    _ = C * infiniteZetaBound x K a := by
        rw [module_rpow_eq, infiniteZetaBound, mul_assoc, ← Finset.prod_mul_distrib]
        congr 1
        refine Finset.prod_congr rfl fun w _ => ?_
        rw [div_eq_mul_inv, mul_comm]

theorem zInf_ne_zero : ZInf := by
  intro k _ _ φ ω h h1 x hx
  have hc0 : Continuous fun a : (InfiniteAdeleRing k)ˣ => rd φ (fun _ => (a : InfiniteAdeleRing k)) :=
    φ.continuous.comp (continuous_pi fun _ =>
      (homeomorphMixedSpace k).continuous.comp Units.continuous_val)
  have hm0 : Continuous fun a : (InfiniteAdeleRing k)ˣ => (ideleModule k (ofInfinite a) : ℝ) :=
    continuous_subtype_val.comp (IdeleGroup.continuous_ideleModule.comp continuous_infinite_idele_inclusion)
  set f : (InfiniteAdeleRing k)ˣ → ℝ := fun a =>
    ‖rd φ (fun _ => (a : InfiniteAdeleRing k))‖ * (ideleModule k (ofInfinite a) : ℝ) ^ x with hf
  have hcf : Continuous f :=
    hc0.norm.mul (hm0.rpow_const fun _ => Or.inr (by linarith))
  have hint : Integrable f (infiniteIdeleMeasure k) := integrable_norm_rd_mul φ hx hcf
  have hnn : 0 ≤ f := fun a => mul_nonneg (norm_nonneg _)
    (Real.rpow_nonneg (ideleModule k (ofInfinite a)).2.le _)
  have hpt : ∀ a : (InfiniteAdeleRing k)ˣ,
      rd φ (fun _ => (a : InfiniteAdeleRing k)) * (ω.toIdele (ofInfinite a) : ℂ) *
        ((ideleModule k (ofInfinite a) : ℝ) : ℂ) ^ (x : ℂ) = ((f a : ℝ) : ℂ) := fun a => by
    obtain ⟨r, hr, e⟩ := h a
    have hn : r = ‖rd φ (fun _ => (a : InfiniteAdeleRing k))‖ := by
      have := congrArg norm e
      rw [norm_mul, Circle.norm_coe, mul_one, Complex.norm_real, Real.norm_of_nonneg hr] at this
      exact this.symm
    rw [e, hn, hf]
    push_cast
    rw [Complex.ofReal_cpow (ideleModule k (ofInfinite a)).2.le]
  have hz : zInf φ ω x = ((∫ a, f a ∂infiniteIdeleMeasure k : ℝ) : ℂ) := by
    rw [zInf, ← integral_complex_ofReal]
    exact integral_congr_ae (Eventually.of_forall hpt)
  have hpos : 0 < ∫ a, f a ∂infiniteIdeleMeasure k := by
    rw [integral_pos_iff_support_of_nonneg hnn hint]
    have hop : IsOpen (Function.support f) := isOpen_compl_singleton.preimage hcf
    refine hop.measure_pos _ ⟨1, ?_⟩
    have hm1 : 0 < (ideleModule k (ofInfinite (1 : (InfiniteAdeleRing k)ˣ)) : ℝ) ^ x :=
      Real.rpow_pos_of_pos (ideleModule k (ofInfinite _)).2 _
    have : f 1 ≠ 0 := by
      simp only [hf, Units.val_one]
      exact mul_ne_zero (norm_ne_zero_iff.2 h1) hm1.ne'
    exact this
  rw [hz]
  exact_mod_cast hpos.ne'

end GlobalTheory.CompanionTheory.EisTestFun
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrystallineFiltrationSaturatedStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalline_filtration_saturated : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (r : ℕ) (z : A.Acr0), (l : A.Acr0) * z ∈ A.Fil0 r → z ∈ A.Fil0 r := by
  first | exact @GlobalTheory.CompanionTheory.PerfFil.crystalline_filtration_l_saturated | exact GlobalTheory.CompanionTheory.PerfFil.crystalline_filtration_l_saturated | (intros; apply GlobalTheory.CompanionTheory.PerfFil.crystalline_filtration_l_saturated <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiagonalTermGood
section
namespace GlobalTheory.CompanionTheory.RgEisDGood

open PositivityTheory.RgEis PositivityTheory.RgEis.MG

theorem gauss_bound (b c : ℝ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℂ, b ≤ z.re → z.re ≤ c →
    ‖Complex.exp (z ^ 2)‖ * (1 + ‖z‖) ^ 3 ≤ M := by
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = max |b| |c| := ⟨_, rfl⟩
  have hbB : |b| ≤ B := hB ▸ le_max_left _ _
  have hcB : |c| ≤ B := hB ▸ le_max_right _ _
  have hB0 : 0 ≤ B := (abs_nonneg b).trans hbB
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = 1 + B := ⟨_, rfl⟩
  have hT : 1 ≤ T := by linarith
  refine ⟨16 * T ^ 4 * Real.exp (B ^ 2), by positivity, fun z h1 h2 => ?_⟩
  obtain ⟨x, hxdef⟩ : ∃ x : ℝ, x = z.re := ⟨_, rfl⟩
  obtain ⟨y, hydef⟩ : ∃ y : ℝ, y = z.im := ⟨_, rfl⟩
  have hx : |x| ≤ B := by
    rw [abs_le]
    constructor
    · have := neg_abs_le b
      rw [hxdef]; linarith
    · have := le_abs_self c
      rw [hxdef]; linarith
  have hx2 : x ^ 2 ≤ B ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg x) hx 2
    rwa [sq_abs] at this
  have hnorm : ‖Complex.exp (z ^ 2)‖ = Real.exp (x ^ 2 - y ^ 2) := by
    rw [Complex.norm_exp]
    congr 1
    simp [pow_two, hxdef, hydef]
  have hz : ‖z‖ ≤ |x| + |y| := by
    rw [hxdef, hydef]; exact Complex.norm_le_abs_re_add_abs_im z
  obtain ⟨u, hudef⟩ : ∃ u : ℝ, u = T + |y| := ⟨_, rfl⟩
  have hy0 := abs_nonneg y
  have hu1 : 1 ≤ u := by linarith
  have h1z : 1 + ‖z‖ ≤ u := by linarith
  obtain ⟨E, hEdef⟩ : ∃ E : ℝ, E = Real.exp (y ^ 2 / 2) := ⟨_, rfl⟩
  have hE0 : 0 < E := hEdef ▸ Real.exp_pos _
  have hE : 1 + y ^ 2 / 2 ≤ E := by
    have := Real.add_one_le_exp (y ^ 2 / 2)
    rw [hEdef]; linarith
  have hEE : E ^ 2 = Real.exp (y ^ 2) := by
    rw [hEdef, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hu2 : u ^ 2 ≤ 4 * T ^ 2 * E := by
    have hsq : |y| ^ 2 = y ^ 2 := sq_abs y
    have hA : u ^ 2 ≤ 2 * T ^ 2 + 2 * y ^ 2 := by
      rw [hudef]
      nlinarith [sq_nonneg (T - |y|)]
    have hT2 : 1 ≤ T ^ 2 := one_le_pow₀ hT
    have hC : 2 * T ^ 2 + 2 * y ^ 2 ≤ 4 * T ^ 2 * (1 + y ^ 2 / 2) := by
      nlinarith [mul_nonneg (sq_nonneg y) (sub_nonneg.2 hT2), sq_nonneg T]
    have hD : 4 * T ^ 2 * (1 + y ^ 2 / 2) ≤ 4 * T ^ 2 * E :=
      mul_le_mul_of_nonneg_left hE (by positivity)
    linarith
  have hu4 : u ^ 4 ≤ 16 * T ^ 4 * Real.exp (y ^ 2) := by
    have h := pow_le_pow_left₀ (by positivity) hu2 2
    calc u ^ 4 = (u ^ 2) ^ 2 := by ring
      _ ≤ (4 * T ^ 2 * E) ^ 2 := h
      _ = 16 * T ^ 4 * E ^ 2 := by ring
      _ = 16 * T ^ 4 * Real.exp (y ^ 2) := by rw [hEE]
  have hz3 : (1 + ‖z‖) ^ 3 ≤ u ^ 4 := by
    have h0 : 0 ≤ 1 + ‖z‖ := by positivity
    calc (1 + ‖z‖) ^ 3 ≤ u ^ 3 := pow_le_pow_left₀ h0 h1z 3
      _ ≤ u ^ 4 := pow_le_pow_right₀ hu1 (by norm_num)
  have hexp : Real.exp (x ^ 2 - y ^ 2) ≤ Real.exp (B ^ 2) * Real.exp (-y ^ 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    linarith
  rw [hnorm]
  calc Real.exp (x ^ 2 - y ^ 2) * (1 + ‖z‖) ^ 3
      ≤ (Real.exp (B ^ 2) * Real.exp (-y ^ 2)) * (16 * T ^ 4 * Real.exp (y ^ 2)) :=
        mul_le_mul hexp (hz3.trans hu4) (by positivity) (by positivity)
    _ = 16 * T ^ 4 * Real.exp (B ^ 2) * (Real.exp (-y ^ 2) * Real.exp (y ^ 2)) := by ring
    _ = 16 * T ^ 4 * Real.exp (B ^ 2) := by
        rw [← Real.exp_add]; simp

theorem dGood : DGood := by
  intro a N ha
  obtain ⟨hd, hg⟩ := ha
  have hE : Differentiable ℂ fun z : ℂ => Complex.exp (z ^ 2) * a z :=
    (Complex.differentiable_exp.comp (differentiable_id.pow 2)).mul hd
  have key : ∀ b c : ℝ, ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℂ, b ≤ z.re → z.re ≤ c →
      ‖Complex.exp (z ^ 2) * a z‖ * (1 + ‖z‖) ≤ M := by
    intro b c
    obtain ⟨M₁, hM₁, h₁⟩ := gauss_bound b c
    obtain ⟨M₂, h₂⟩ := hg b c
    refine ⟨|M₂| * M₁, by positivity, fun z hb hc => ?_⟩
    have hz := h₁ z hb hc
    have ha' : ‖a z‖ ≤ |M₂| * (1 + ‖z‖) ^ 2 :=
      (h₂ z hb hc).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
    rw [norm_mul]
    calc ‖Complex.exp (z ^ 2)‖ * ‖a z‖ * (1 + ‖z‖)
        ≤ ‖Complex.exp (z ^ 2)‖ * (|M₂| * (1 + ‖z‖) ^ 2) * (1 + ‖z‖) := by gcongr
      _ = |M₂| * (‖Complex.exp (z ^ 2)‖ * (1 + ‖z‖) ^ 3) := by ring
      _ ≤ |M₂| * M₁ := by gcongr
  refine ⟨⟨hE, fun b c => ?_⟩, ⟨(differentiable_id.sub_const N).mul hE, fun b c => ?_⟩⟩
  · obtain ⟨M, _, h⟩ := key b c
    refine ⟨M, fun z hb hc => (?_ : _ ≤ _).trans (h z hb hc)⟩
    exact le_mul_of_one_le_right (norm_nonneg _) (by linarith [norm_nonneg z])
  · obtain ⟨M, hM, h⟩ := key b c
    refine ⟨(1 + ‖N‖) * M, fun z hb hc => ?_⟩
    have hzN : ‖z - N‖ ≤ (1 + ‖N‖) * (1 + ‖z‖) := by
      have := norm_sub_le z N
      nlinarith [norm_nonneg z, norm_nonneg N, mul_nonneg (norm_nonneg z) (norm_nonneg N)]
    rw [norm_mul]
    calc ‖z - N‖ * ‖Complex.exp (z ^ 2) * a z‖
        ≤ ((1 + ‖N‖) * (1 + ‖z‖)) * ‖Complex.exp (z ^ 2) * a z‖ := by gcongr
      _ = (1 + ‖N‖) * (‖Complex.exp (z ^ 2) * a z‖ * (1 + ‖z‖)) := by ring
      _ ≤ (1 + ‖N‖) * M := by
          have := h z hb hc
          gcongr

end GlobalTheory.CompanionTheory.RgEisDGood
end

