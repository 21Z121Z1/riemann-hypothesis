import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0384
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0118
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0104
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicFormFrameExpansion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0978
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1155
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTraceSmul
section
noncomputable section

open MeasureTheory Filter Topology Set GlobalTheory.Orb GlobalTheory.OpTrace GlobalTheory.AutomorphicL2Unitary
open Formalism.REAL (UJ KG toM toMK muK expG inG)
open GlobalTheory.PsCo.Pc1
open scoped InnerProductSpace

namespace GlobalTheory.PsCo.Pc3

theorem shapeM_mono {n : ℕ} (ε : Fin n → Bool) {d d' : ℕ} (h : d ≤ d') : ShapeM ε d ≤ ShapeM ε d' :=
  Submodule.span_mono fun _ ⟨H, P, hH, hP, e⟩ => ⟨H, P, hH, hP.trans h, e⟩

theorem hasTrace_add' {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U] [CompleteSpace U]
    {S T : U →L[ℂ] U} {a b : ℂ} (hS : HasTrace S a) (hT : HasTrace T b) : HasTrace (S + T) (a + b) :=
  ⟨hS.1.add hT.1, by rw [trace_add hS.1 hT.1, hS.2, hT.2]⟩

theorem hasTrace_smul' {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U] [CompleteSpace U]
    {T : U →L[ℂ] U} {a : ℂ} (c : ℂ) (hT : HasTrace T a) : HasTrace (c • T) (c * a) :=
  ⟨hT.1.smul c, by rw [trace_smul, hT.2]⟩

theorem toM_mul' {n : ℕ} {ε : Fin n → Bool} (a b : UJ ε) : toM (a * b) = toM a * toM b := rfl

theorem trace_adBas (hSh : StShape) (hBD : StBasDeriv) (hUF : UFin) (hRS : RangeShape) (hTS : TraceSum)
    (hCD : ConjDeriv) {n : ℕ} (ε : Fin n → Bool) (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (U : Type)
    [NormedAddCommGroup U] [InnerProductSpace ℂ U] [CompleteSpace U] (π : UJ ε →* (U →L[ℂ] U))
    (hπ : IsUnitaryRep π) (hirr : IsTopIrreducible π) (Z : Mat n) (H : ℝ → ℝ) (P : Poly n)
    (hZ : LieU ε Z) (hH : IsCutFn H) :
    HasTrace (repOp π μ fun g => adBas ε Z H P (toM g)) 0 := by
  have := GlobalTheory.CompanionTheory.HaarUJ.haar_rinv_UJ n ε μ
  have hZG : inG ε Z := (GlobalTheory.T.indefiniteUnitaryLieAlgebra_mem_iff_entries n ε Z).2 hZ
  obtain ⟨hxc, hxinv⟩ := GlobalTheory.CompanionTheory.ExpOneParam.continuous_expG_and_toM_inv n ε Z hZG
  obtain ⟨hadS, hder⟩ := hBD n ε Z H P hZ hH
  have hbS : bas ε H P ∈ ShapeM ε (P.totalDegree + 2) := Submodule.subset_span ⟨H, P, hH, by omega, rfl⟩
  obtain ⟨-, -, hac, hacs⟩ := hSh n ε _ _ hadS
  obtain ⟨-, -, hbc, hbcs⟩ := hSh n ε _ _ hbS
  obtain ⟨L, hLf, hLmem, hLd⟩ := hUF n ε U π hπ hirr (P.totalDegree + 2)
  have := hLf
  obtain ⟨-, hTr⟩ := hRS n ε μ U π hπ _ _ hadS
  obtain ⟨-, hAr⟩ := hRS n ε μ U π hπ _ _ hbS
  set fad : UJ ε → ℂ := fun g => adBas ε Z H P (toM g) with hfad
  set fb : UJ ε → ℂ := fun g => bas ε H P (toM g) with hfb
  set T := repOp π μ fad with hT
  set A := repOp π μ fb with hA
  set e := stdOrthonormalBasis ℂ L with he
  set x : ℝ → UJ ε := fun t => expG ε Z t with hx
  have hx0 : x 0 = 1 := by
    apply Subtype.ext
    apply Units.ext
    have := Formalism.REAL.toM_expG ε Z 0 hZG
    simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero] at this
    exact this
  have hconj : ∀ (s : ℝ) (g : UJ ε), toM ((x s)⁻¹ * g * x s) =
      NormedSpace.exp (-((s : ℂ) • Z)) * toM g * NormedSpace.exp ((s : ℂ) • Z) := fun s g => by
    rw [toM_mul', toM_mul', hxinv s, Formalism.REAL.toM_expG ε Z s hZG]
  have key : ∀ (y : UJ ε) (v u : U), ⟪v, π y u⟫_ℂ = ⟪π y⁻¹ v, u⟫_ℂ := fun y v u => by
    rw [hπ.inner_apply_left, inv_inv]
  set w : UJ ε → ℂ := fun g => ∑ j, ⟪(e j : U), π g (e j : U)⟫_ℂ with hw
  have hwc : Continuous w := continuous_finsetSum _ fun j _ => continuous_const.inner (hπ.continuous_apply _)

  have hsum : ∑ j, ⟪(e j : U), T (e j : U)⟫_ℂ = ∫ g, fad g * w g ∂μ := by
    have hint : ∀ j ∈ Finset.univ, Integrable (fun g => fad g * ⟪(e j : U), π g (e j : U)⟫_ℂ) μ := fun j _ =>
      (hac.mul (continuous_const.inner (hπ.continuous_apply _))).integrable_of_hasCompactSupport hacs.mul_right
    simp only [hT, hπ.inner_repOp hac hacs, hw, Finset.mul_sum]
    rw [integral_finsetSum _ hint]

  have hid : ∀ t : ℝ, ∑ j, ⟪(e j : U), π (x t) (A (π (x t)⁻¹ (e j : U)))⟫_ℂ =
      ∫ g, fb ((x t)⁻¹ * g * x t) * w g ∂μ := by
    intro t
    set y := x t
    have h1 : ∀ j, ⟪(e j : U), π y (A (π y⁻¹ (e j : U)))⟫_ℂ =
        ∫ g, fb g * ⟪(e j : U), π (y * g * y⁻¹) (e j : U)⟫_ℂ ∂μ := by
      intro j
      rw [key y, hA, hπ.inner_repOp hbc hbcs]
      refine integral_congr_ae (Eventually.of_forall fun g => ?_)
      simp only
      congr 1
      rw [map_mul, map_mul]
      show _ = ⟪(e j : U), π y (π g (π y⁻¹ (e j : U)))⟫_ℂ
      rw [key y]
    have hint : ∀ j ∈ Finset.univ, Integrable (fun g => fb g * ⟪(e j : U), π (y * g * y⁻¹) (e j : U)⟫_ℂ) μ :=
      fun j _ => (hbc.mul (continuous_const.inner ((hπ.continuous_apply _).comp (by fun_prop)))).integrable_of_hasCompactSupport
        hbcs.mul_right
    rw [Finset.sum_congr rfl fun j _ => h1 j, ← integral_finsetSum _ hint]
    have e2 : (fun g => ∑ j, fb g * ⟪(e j : U), π (y * g * y⁻¹) (e j : U)⟫_ℂ) =
        fun g => fb g * w (y * g * y⁻¹) := funext fun g => by simp only [hw, Finset.mul_sum]
    rw [e2]
    have e3 := integral_mul_right_eq_self (μ := μ) (fun g => fb (y⁻¹ * g) * w (y * (y⁻¹ * g) * y⁻¹)) y
    have e4 := integral_mul_left_eq_self (μ := μ) (fun g => fb g * w (y * g * y⁻¹)) y⁻¹
    rw [← e4, ← e3]
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    simp only
    congr 2
    · group
    · group

  have h0 : π (x 0) = 1 := by rw [hx0, map_one]
  have hCD' := hCD U L (fun t => π (x t)) (fun t => π (x t)⁻¹) A h0
    (fun t v u => by
      rw [hπ.inner_apply_left, ← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        ContinuousLinearMap.one_apply])
    (fun t v u => (hπ.inner_apply_left _ v u).symm) (fun v hv => hLd v hv Z hZG)
    (fun u => hLmem _ (hAr u).1) (fun u => hLmem _ (hAr u).2)
  have hfun : (fun t => ∑ j, ⟪(stdOrthonormalBasis ℂ L j : U), π (x t) (A (π (x t)⁻¹
      (stdOrthonormalBasis ℂ L j : U)))⟫_ℂ) = fun t => ∫ g, fb ((x t)⁻¹ * g * x t) * w g ∂μ :=
    funext hid
  rw [hfun] at hCD'

  have hC : IsCompact ((fun p : ℝ × UJ ε => x p.1 * p.2 * (x p.1)⁻¹) '' (Icc (-1 : ℝ) 1 ×ˢ tsupport fad)) :=
    (isCompact_Icc.prod hacs.isCompact).image (by fun_prop)
  obtain ⟨χ, h1, -, hcs, -⟩ := exists_continuous_one_zero_of_isCompact hC isClosed_empty (disjoint_empty _)
  obtain ⟨M, hM⟩ := hacs.exists_bound_of_continuous hac
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 1)
  have keyb : ∀ u ∈ Icc (-1 : ℝ) 1, ∀ g, ‖fad ((x u)⁻¹ * g * x u) * w g‖ ≤ M * ‖(χ g : ℂ)‖ * ‖w g‖ := by
    intro u hu g
    rw [norm_mul]
    by_cases h : fad ((x u)⁻¹ * g * x u) = 0
    · rw [h, norm_zero, zero_mul]
      positivity
    · have hg : g ∈ (fun p : ℝ × UJ ε => x p.1 * p.2 * (x p.1)⁻¹) '' (Icc (-1 : ℝ) 1 ×ˢ tsupport fad) :=
        ⟨(u, (x u)⁻¹ * g * x u), ⟨hu, subset_tsupport fad h⟩, by simp only; group⟩
      have h2 : (χ g : ℂ) = 1 := by simp [h1 hg]
      rw [h2, norm_one, mul_one]
      exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)
  have hχc : Continuous fun g => (χ g : ℂ) := Complex.continuous_ofReal.comp χ.continuous
  have hbint : Integrable (fun g => M * ‖(χ g : ℂ)‖ * ‖w g‖) μ := by
    refine (((hχc.norm.const_mul M).mul hwc.norm)).integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.mul_right ?_
    refine HasCompactSupport.mul_left ?_
    exact (hcs.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero).norm
  have hcontF : ∀ (f : UJ ε → ℂ), Continuous f → ∀ u, Continuous fun g => f ((x u)⁻¹ * g * x u) * w g :=
    fun f hf u => (hf.comp (by fun_prop)).mul hwc
  have hint := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun u g => fb ((x u)⁻¹ * g * x u) * w g) (F' := fun u g => fad ((x u)⁻¹ * g * x u) * w g)
    (x₀ := (0 : ℝ)) (s := Ioo (-1 : ℝ) 1) (bound := fun g => M * ‖(χ g : ℂ)‖ * ‖w g‖)
    (Ioo_mem_nhds (by norm_num) (by norm_num))
    (Eventually.of_forall fun u => (hcontF fb hbc u).aestronglyMeasurable)
    (by
      simp only [hx0, inv_one, one_mul, mul_one]
      exact (hbc.mul hwc).integrable_of_hasCompactSupport hbcs.mul_right)
    (hcontF fad hac 0).aestronglyMeasurable
    (.of_forall fun g u hu => keyb u (Ioo_subset_Icc_self hu) g) hbint
    (.of_forall fun g u _ => by
      have e5 : (fun v : ℝ => fb ((x v)⁻¹ * g * x v) * w g) =
          fun v : ℝ => bas ε H P (NormedSpace.exp (-((v : ℂ) • Z)) * toM g * NormedSpace.exp ((v : ℂ) • Z)) * w g :=
        funext fun v => by simp only [hfb, hconj]
      rw [e5]
      have e6 : fad ((x u)⁻¹ * g * x u) =
          adBas ε Z H P (NormedSpace.exp (-((u : ℂ) • Z)) * toM g * NormedSpace.exp ((u : ℂ) • Z)) := by
        simp only [hfad, hconj]
      rw [e6]
      exact (hder (toM g) u).mul_const (w g))
  have hzero : ∫ g, fad ((x 0)⁻¹ * g * x 0) * w g ∂μ = 0 := hint.2.unique hCD'
  simp only [hx0, inv_one, one_mul, mul_one] at hzero
  have hTL : ∀ u, T u ∈ L := fun u => hLmem _ (hTr u).1
  have := hTS U L T hTL
  rwa [hsum, hzero] at this

theorem stTrAd_of : StShape → StBasDeriv → UFin → RangeShape → TraceSum → ConjDeriv → StTrAd := by
  intro hSh hBD hUF hRS hTS hCD n ε μ _ U _ _ _ π hπ hirr φ hφ
  suffices h : (∃ d, φ ∈ ShapeM ε d) ∧ HasTrace (repOp π μ fun g => φ (toM g)) 0 from h.2
  induction hφ using Submodule.span_induction with
  | mem φ hmem =>
    obtain ⟨Z, H, P, hZ, hH, rfl⟩ := hmem
    exact ⟨⟨_, (hBD n ε Z H P hZ hH).1⟩, trace_adBas hSh hBD hUF hRS hTS hCD ε μ U π hπ hirr Z H P hZ hH⟩
  | zero =>
    refine ⟨⟨0, zero_mem _⟩, ?_⟩
    have h0 : IsRepOp π μ (fun g => (0 : Mat n → ℂ) (toM g)) 0 := fun v => by
      simp only [Pi.zero_apply, zero_smul, integral_zero, ContinuousLinearMap.zero_apply]
      exact ⟨integrable_zero _ _ _, trivial⟩
    rw [h0.repOp_eq]
    exact ⟨isTraceClass_zero, trace_zero⟩
  | add φ₁ φ₂ _ _ h₁ h₂ =>
    obtain ⟨⟨d₁, hd₁⟩, ht₁⟩ := h₁
    obtain ⟨⟨d₂, hd₂⟩, ht₂⟩ := h₂
    refine ⟨⟨max d₁ d₂, add_mem (shapeM_mono ε (le_max_left _ _) hd₁) (shapeM_mono ε (le_max_right _ _) hd₂)⟩, ?_⟩
    have o₁ := (hRS n ε μ U π hπ d₁ φ₁ hd₁).1
    have o₂ := (hRS n ε μ U π hπ d₂ φ₂ hd₂).1
    have hs : IsRepOp π μ (fun g => (φ₁ + φ₂) (toM g))
        (repOp π μ (fun g => φ₁ (toM g)) + repOp π μ (fun g => φ₂ (toM g))) := fun v => by
      refine ⟨?_, ?_⟩
      · refine ((o₁ v).1.add (o₂ v).1).congr (Eventually.of_forall fun g => ?_)
        simp only [Pi.add_apply, add_smul]
      · rw [ContinuousLinearMap.add_apply, (o₁ v).2, (o₂ v).2, ← integral_add (o₁ v).1 (o₂ v).1]
        simp only [Pi.add_apply, add_smul]
    rw [hs.repOp_eq]
    simpa using hasTrace_add' ht₁ ht₂
  | smul c φ _ h =>
    obtain ⟨⟨d, hd⟩, ht⟩ := h
    refine ⟨⟨d, Submodule.smul_mem _ c hd⟩, ?_⟩
    have o := (hRS n ε μ U π hπ d φ hd).1
    have hs : IsRepOp π μ (fun g => (c • φ) (toM g)) (c • repOp π μ (fun g => φ (toM g))) := fun v => by
      refine ⟨?_, ?_⟩
      · refine ((o v).1.smul c).congr (Eventually.of_forall fun g => ?_)
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul]
      · rw [ContinuousLinearMap.smul_apply, (o v).2, ← integral_smul]
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul]
    rw [hs.repOp_eq]
    simpa using hasTrace_smul' c ht

end GlobalTheory.PsCo.Pc3
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightAddMulGeometricDegreeNonnegOfSmallSection
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef GlobalTheory.CechPic GlobalTheory.Points

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSNef

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem nsq_pow_addFn_const {σ : k →+* ℂ} {B : LB X} (φ : Weight p σ B) (c : ℝ) (m : ℕ)
    (s : (lbPow B m).ι → CxPts p σ → ℂ) (y : CxPts p σ) :
    ((φ.addFn fun _ => c).pow m).nsq s y = (φ.pow m).nsq s y * Real.exp (-(m * c)) := by
  simp only [Weight.nsq]
  erw [Weight.zpow_φ, Weight.zpow_φ]
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  simp only [Weight.addFn]
  push_cast
  ring

theorem isometric_pull_id (L : HermLB p) : L.Isometric (L.pull (𝟙 X) (Category.id_comp p)) := by
  have hid {σ : k →+* ℂ} (y : CxPts p σ) : PtsOver.map (𝟙 X) (Category.id_comp p) _ y = y :=
    Subtype.ext (Category.comp_id _)
  refine HermLB.isometric_of_chart (fun c _ => c) (fun c y hy => Set.mem_iInter.2 fun _ => hy)
    (fun z c c' hc hc' => ?_) fun σ c y _ => ?_
  · refine Eq.trans ?_ (gm_pull_g L.B (𝟙 X) (𝟙 X) z (fun _ => c) (fun _ => c')
      (Set.mem_iInter.2 fun _ => hc) (Set.mem_iInter.2 fun _ => hc')).symm
    rw [Category.comp_id]
  · exact ((L.φ σ).pull_φ (𝟙 X) (Category.id_comp p) (fun _ => c) y).trans (congrArg _ (hid y))

theorem recursion_pull_id [IsLocallyNoetherian X] {D : ℕ} (hX : IsArithVar p D) (hD : 1 ≤ D) {L : HermLB p} {h : X → ℝ}
    (H : L.IsArithHeight h) (m : ℕ) {q : X ⟶ Sp k} (hq : 𝟙 X ≫ p = q)
    (r : ((L.pull (𝟙 X) hq).pow m).B.ι → X.functionFieldˣ) (hr : IsRatSec ((L.pull (𝟙 X) hq).pow m).B r) :
    (L.pull (𝟙 X) hq).ArchIntegrable ((L.pull (𝟙 X) hq).pow m) D hr ∧
      (m : ℝ) * h (genericPoint X) = ∑ᶠ z, ((((L.pull (𝟙 X) hq).pow m).div hr).mult z : ℝ) * h z -
        (L.pull (𝟙 X) hq).archInt ((L.pull (𝟙 X) hq).pow m) D hr := by
  subst hq
  have e := H.recursion X (𝟙 X) hX.charZero D hD hX.dim_eq m r hr
  simpa using e

end GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem height_add_mul_gdeg_nonneg_of_smallSec : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → 1 ≤ D → ∀ (C : HermLB p) (h : X → ℝ), C.SemiPos D → C.IsArithHeight h → (∀ z, z ≠ genericPoint X → 0 ≤ h z) → ∀ (m : ℕ) (u : ℝ), 0 < m → 0 ≤ u → (∃ s ∈ ((C.shift (fun _ => u) fun _ => rfl).pow m).smallSec, s ≠ 0) → 0 ≤ h (genericPoint X) + u * gdeg C D := by
  intro HC k _ X _ p D hX hD C h hSP H hnn m u hm hu hex
  obtain ⟨s, hs, hs0⟩ := hex
  have := hX.isLocallyNoetherian
  have := hX.finite_emb
  have hiso := isometric_pull_id C
  set C' := C.pull (𝟙 X) (Category.id_comp p) with hC'
  let s' : (C.pow m).B.Sec := s
  have hg : genericPoint X ∈ nonzeroLocus s' := (sec_ne_zero_iff s').1 hs0
  obtain ⟨r', hr', hdiv, hlog⟩ := (hiso.pow m).exists_isRatSec (isRatSec_ratOfSec s' hg)
  obtain ⟨hI, hrec⟩ := recursion_pull_id hX hD H m (Category.id_comp p) r' hr'

  have hsum : 0 ≤ ∑ᶠ z, (((C'.pow m).div hr').mult z : ℝ) * h z := by
    refine finsum_nonneg fun z => ?_
    rw [hdiv]
    by_cases hz : ((C.pow m).div (isRatSec_ratOfSec s' hg)).mult z = 0
    · simp [hz]
    · exact mul_nonneg (by exact_mod_cast mult_divOfSec_nonneg z)
        (hnn z fun e => CartierDiv.genericPoint_notMem_supp _ (e ▸ CartierDiv.mem_supp_of_mult_ne_zero hz))

  have hneg (σ : k →+* ℂ) : (C.φ σ).chernPart D (-1) = 0 := Weight.chernPart_neg_eq_zero (C.cInf σ) (hSP σ)
  have hfin (σ : k →+* ℂ) : IsFiniteMeasure ((C.φ σ).chernPart D 1) := by
    have hu1 : ∀ σ (y : CxPts p σ), CInfAt (fun _ : CxPts p σ => (1 : ℝ)) y := fun σ y => cInfAt_const 1 y
    have hc1 : ∀ σ σ' : k →+* ℂ, (Weight.ofFun (fun _ : CxPts p σ => (1 : ℝ))).IsConj
        (Weight.ofFun (fun _ : CxPts p σ' => (1 : ℝ))) := fun _ _ _ _ _ _ _ => rfl
    obtain ⟨Φ, hΦ⟩ := ((HC.arExists k X p D hX).2 (Option Unit)
      (fun o : Option Unit => o.elim (ArInt.fnB (fun σ (_ : CxPts p σ) => (1 : ℝ)) hu1 hc1) fun _ => C)).1
    have h1 := ((HC.arMix.fnB HC.arExists hX hΦ (Pi.single () 1)).1 σ).1
    rw [(isometric_comb_single (fun _ : Unit => C) ()).chernPart_eq σ D 1] at h1
    exact (integrable_const_iff.1 (integrableOn_univ.1 h1)).resolve_left one_ne_zero

  have hpt (σ : k →+* ℂ) : ∀ y ∈ offSupp p σ ((C'.pow m).div hr'),
      logNorm ((C'.pow m).φ σ) r' y ≤ m * u := by
    intro y hy
    rw [hdiv] at hy
    rw [hlog σ hy]
    have hy' : y ∈ ptsIn p σ (nonzeroLocus s') := by
      have := hy
      rwa [offSupp_divOfSec] at this
    rw [logNorm_ratOfSec _ hy']
    have h1 := hs σ y
    change (((C.φ σ).addFn fun _ => 2 * u).pow m).nsq (secVal p σ s') y ≤ 1 at h1
    rw [nsq_pow_addFn_const] at h1
    have h2 : ((C.φ σ).pow m).nsq (secVal p σ s') y ≤ Real.exp (m * (2 * u)) := by
      have := Real.exp_pos (m * (2 * u))
      rw [Real.exp_neg] at h1
      rwa [mul_inv_le_iff₀ (Real.exp_pos _), one_mul] at h1
    have h0 := ((C.φ σ).pow m).nsq_nonneg (secVal p σ s') y
    have h3 : Real.log (((C.φ σ).pow m).nsq (secVal p σ s') y) ≤ m * (2 * u) := by
      rcases h0.eq_or_lt with e | e
      · rw [← e, Real.log_zero]; positivity
      · exact (Real.log_le_iff_le_exp e).2 h2
    change Real.log (((C.φ σ).pow m).nsq (secVal p σ s') y) / 2 ≤ _
    linarith
  have hA : C'.archInt (C'.pow m) D hr' ≤ m * u * gdeg C D := by
    rw [HermLB.archInt, gdeg, chInt, mul_finsum]
    refine finsum_le_finsum' (Set.toFinite _) (Set.toFinite _) fun σ => ?_
    have hS : MeasurableSet (offSupp p σ ((C'.pow m).div hr')) := (isOpen_offSupp _).measurableSet
    have hint := hI σ
    rw [← hiso.chernIntegrableOn_eq] at hint
    rw [← hiso.chernInt_eq]
    haveI := hfin σ
    simp only [Weight.chernInt, hneg σ, Measure.restrict_zero, integral_zero_measure, sub_zero,
      setIntegral_const, smul_eq_mul, mul_one]
    calc ∫ y in offSupp p σ ((C'.pow m).div hr'), logNorm ((C'.pow m).φ σ) r' y ∂(C.φ σ).chernPart D 1
        ≤ ∫ y in offSupp p σ ((C'.pow m).div hr'), (m * u : ℝ) ∂(C.φ σ).chernPart D 1 :=
          setIntegral_mono_on hint.1 (integrable_const _).integrableOn hS (hpt σ)
      _ = ((C.φ σ).chernPart D 1).real (offSupp p σ ((C'.pow m).div hr')) * (m * u) := by
          rw [setIntegral_const, smul_eq_mul]
      _ ≤ ((C.φ σ).chernPart D 1).real Set.univ * (m * u) :=
          mul_le_mul_of_nonneg_right (measureReal_mono (Set.subset_univ _) (measure_ne_top _ _))
            (by positivity)
      _ = m * u * ((C.φ σ).chernPart D 1).real Set.univ := by ring
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have : 0 ≤ (m : ℝ) * (h (genericPoint X) + u * gdeg C D) := by
    have := hrec
    nlinarith
  exact nonneg_of_mul_nonneg_right this hmpos

end GlobalTheory.HSNef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairNormIndependentOfFrames
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VolBr.NuEq

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {σ : k →+* ℂ}
  {y : CxPts p σ}

theorem ratVal_one' : ratVal (1 : X.functionField) y = 1 := by
  have h1 := unitAt_one (under y)
  have e := ratVal_mul (y := y) h1.regAt h1.regAt
  rw [mul_one] at e
  exact (mul_eq_left₀ (ratVal_ne_zero h1)).1 e.symm

theorem ratVal_inv' {f : X.functionField} (hf : UnitAt (under y) f) :
    ratVal f⁻¹ y = (ratVal f y)⁻¹ := by
  have e := ratVal_mul hf.regAt hf.inv.regAt
  rw [mul_inv_cancel₀ hf.ne_zero, ratVal_one'] at e
  exact eq_inv_of_mul_eq_one_right e.symm

theorem unitAt_pow {x : X} {u : X.functionField} (h : UnitAt x u) (m : ℕ) : UnitAt x (u ^ m) := by
  induction m with
  | zero => simpa using unitAt_one x
  | succ m ih => rw [pow_succ]; exact ih.mul h

theorem unitAt_zpow {x : X} {u : X.functionField} (h : UnitAt x u) (n : ℤ) : UnitAt x (u ^ n) := by
  cases n with
  | ofNat m => simpa using unitAt_pow h m
  | negSucc m => rw [zpow_negSucc]; exact (unitAt_pow h _).inv

theorem ratVal_pow' {u : X.functionField} (h : UnitAt (under y) u) (m : ℕ) :
    ratVal (u ^ m) y = ratVal u y ^ m := by
  induction m with
  | zero => simpa using ratVal_one'
  | succ m ih => rw [pow_succ, ratVal_mul (unitAt_pow h m).regAt h.regAt, ih, pow_succ]

theorem ratVal_zpow' {u : X.functionField} (h : UnitAt (under y) u) (n : ℤ) :
    ratVal (u ^ n) y = ratVal u y ^ n := by
  cases n with
  | ofNat m => simpa using ratVal_pow' h m
  | negSucc m => rw [zpow_negSucc, zpow_negSucc, ratVal_inv' (unitAt_pow h _), ratVal_pow' h]

end GlobalTheory.VolBr.NuEq

namespace GlobalTheory.VolBr

open NuEq in

theorem nu_eq : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (a b : ℤ) (f : X.functionField), f ∈ P.H a b → ∀ (σ : k →+* ℂ) (y : CxPts p σ) i j, y ∈ ptsIn p σ (P.L.B.U i) → y ∈ ptsIn p σ (P.A.B.U j) → P.nu a b σ y f = ‖ratVal (P.loc a b f i j) y‖ * Real.exp (-(a * (P.L.φ σ).φ i y + b * (P.A.φ σ).φ j y) / 2) := by
  intro k _ X _ p P a b f hf σ y i j hi hj
  have hi₀ : y ∈ ptsIn p σ (P.L.B.U (pick (P.L.φ σ).isLB y)) := mem_pick _ y
  have hj₀ : y ∈ ptsIn p σ (P.A.B.U (pick (P.A.φ σ).isLB y)) := mem_pick _ y
  have hii := mem_ptsIn_inf.2 ⟨hi, hi₀⟩
  have hjj := mem_ptsIn_inf.2 ⟨hj, hj₀⟩
  have gi := gen_mem (mem_ptsIn.1 hii)
  have gj := gen_mem (mem_ptsIn.1 hjj)
  have uG := unitAt_fnOf (mem_ptsIn.1 hii) gi (P.L.B.g i (pick (P.L.φ σ).isLB y))
  have uG' := unitAt_fnOf (mem_ptsIn.1 hjj) gj (P.A.B.g j (pick (P.A.φ σ).isLB y))
  have uGa := unitAt_zpow uG a
  have uGb := unitAt_zpow uG' b
  have hreg : RegAt (under y) (P.loc a b f (pick (P.L.φ σ).isLB y) (pick (P.A.φ σ).isLB y)) :=
    hf _ _ _ (mem_ptsIn.1 hi₀) (mem_ptsIn.1 hj₀)
  have hloc : P.loc a b f i j =
      ((fnOf _ gi (P.L.B.g i (pick (P.L.φ σ).isLB y) : Γ(X, _))) ^ a *
        (fnOf _ gj (P.A.B.g j (pick (P.A.φ σ).isLB y) : Γ(X, _))) ^ b) *
        P.loc a b f (pick (P.L.φ σ).isLB y) (pick (P.A.φ σ).isLB y) := by
    simp only [Pair.loc]
    rw [P.hr i _ gi, P.hr' j _ gj, mul_zpow, mul_zpow]
    ring
  have eG := ratVal_fnOf hii gi (P.L.B.g i (pick (P.L.φ σ).isLB y) : Γ(X, _))
  have eG' := ratVal_fnOf hjj gj (P.A.B.g j (pick (P.A.φ σ).isLB y) : Γ(X, _))
  have c0 : 0 < ‖CxPts.gv p σ P.L.B i (pick (P.L.φ σ).isLB y) y‖ :=
    norm_pos_iff.2 (by rw [CxPts.gv, ← eG]; exact ratVal_ne_zero uG)
  have c0' : 0 < ‖CxPts.gv p σ P.A.B j (pick (P.A.φ σ).isLB y) y‖ :=
    norm_pos_iff.2 (by rw [CxPts.gv, ← eG']; exact ratVal_ne_zero uG')
  rw [Pair.nu, hloc, ratVal_mul (uGa.mul uGb).regAt hreg, ratVal_mul uGa.regAt uGb.regAt,
    ratVal_zpow' uG, ratVal_zpow' uG', eG, eG', (P.L.φ σ).trans i _ y hi hi₀,
    (P.A.φ σ).trans j _ y hj hj₀, norm_mul, norm_mul, norm_zpow, norm_zpow]
  change _ = ‖CxPts.gv p σ P.L.B i _ y‖ ^ a * ‖CxPts.gv p σ P.A.B j _ y‖ ^ b * _ * _
  rw [← Real.rpow_intCast, ← Real.rpow_intCast, Real.rpow_def_of_pos c0, Real.rpow_def_of_pos c0',
    Real.log_pow, Real.log_pow]
  have key : ∀ (N u v s t : ℝ), N * Real.exp (-(a * (s - 2 * u) + b * (t - 2 * v)) / 2) =
      Real.exp (u * a) * Real.exp (v * b) * N * Real.exp (-(a * s + b * t) / 2) := by
    intro N u v s t
    rw [mul_comm (Real.exp (u * a) * Real.exp (v * b)) N, mul_assoc, ← Real.exp_add, ← Real.exp_add]
    congr 2
    ring
  push_cast
  exact key _ _ _ _ _

end GlobalTheory.VolBr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairSectionsMulMemNormMul
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

namespace GlobalTheory.VolBr.NuMul

theorem loc_mul {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} (P : Pair p)
    (a b a' b' : ℤ) (f g : X.functionField) (i : P.L.B.ι) (j : P.A.B.ι) :
    P.loc (a + a') (b + b') (f * g) i j = P.loc a b f i j * P.loc a' b' g i j := by
  have h1 : (P.r i : X.functionField) ≠ 0 := (P.r i).ne_zero
  have h2 : (P.r' j : X.functionField) ≠ 0 := (P.r' j).ne_zero
  simp only [Pair.loc, zpow_add₀ h1, zpow_add₀ h2]
  ring

theorem mul_mem_H_and_nu_mul : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (a b a' b' : ℤ) (f g : X.functionField), f ∈ P.H a b → g ∈ P.H a' b' → f * g ∈ P.H (a + a') (b + b') ∧ ∀ (σ : k →+* ℂ) (y : CxPts p σ), P.nu (a + a') (b + b') σ y (f * g) = P.nu a b σ y f * P.nu a' b' σ y g := by
  intro k _ X _ p P a b a' b' f g hf hg
  refine ⟨fun x i j hi hj => ?_, fun σ y => ?_⟩
  · rw [loc_mul]
    exact (hf x i j hi hj).mul (hg x i j hi hj)
  · have hi := mem_ptsIn.1 (mem_pick (P.L.φ σ).isLB y)
    have hj := mem_ptsIn.1 (mem_pick (P.A.φ σ).isLB y)
    simp only [Pair.nu]
    rw [loc_mul, ratVal_mul (hf _ _ _ hi hj) (hg _ _ _ hi hj), norm_mul]
    have e : -(((a + a' : ℤ) : ℝ) * (P.L.φ σ).φ (pick (P.L.φ σ).isLB y) y + ((b + b' : ℤ) : ℝ) * (P.A.φ σ).φ (pick (P.A.φ σ).isLB y) y) / 2
      = -((a : ℝ) * (P.L.φ σ).φ (pick (P.L.φ σ).isLB y) y + (b : ℝ) * (P.A.φ σ).φ (pick (P.A.φ σ).isLB y) y) / 2
        + -((a' : ℝ) * (P.L.φ σ).φ (pick (P.L.φ σ).isLB y) y + (b' : ℝ) * (P.A.φ σ).φ (pick (P.A.φ σ).isLB y) y) / 2 := by
      push_cast; ring
    rw [e, Real.exp_add]
    ring

end GlobalTheory.VolBr.NuMul
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicFormFrameExpansionStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_form_frame_expansion : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (r : ℕ) (hr : V.rank = r) (X : Data D.host.E r) (x : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (w : D.what₂.Tau → Fin V.rank → ℤ) (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (φ : GA D V → ℂ), IsInfFam θ → ModelOf V hr X → NegFirst V X.p0 x → (∀ (ρ : D.what₂.Tau) (τ : X.Ψ), τ.1 = tauE D ρ → ∀ c : Fin V.rank, la τ (Fin.cast hr c) = w ρ c) → IsHolFor θ V x w φ → ∀ g : GA D V, ∃ Q : Frame X.Ψ r → ℂ, DifferentiableOn ℂ Q X.dom ∧ (∀ y ∈ X.dom, ∀ b ∈ Bor X.Ψ r, Q (rmul y b) = bchar la b * Q y) ∧ ∀ u ∈ GinfC V, ∀ y, FrIs θ V hr X x u y → Q y = φ (g * u) := by
  first | exact @GlobalTheory.HolRead.AdExt.exists_extension | exact GlobalTheory.HolRead.AdExt.exists_extension | (intros; apply GlobalTheory.HolRead.AdExt.exists_extension <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitNatCastFrameCoeffRingNotDvdStatement
section
open GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnit_natCast_frameCoeffRing_not_dvd : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [DecidableEq ι] (N : ℕ) (F : Frame l ι N), F.Ok → ∀ n : ℕ, ¬ l ∣ n → IsUnit (n : F.O) := by
  first | exact @GlobalTheory.ExpFrame.Frame.isUnit_natCast_of_not_dvd | exact GlobalTheory.ExpFrame.Frame.isUnit_natCast_of_not_dvd | (intros; apply GlobalTheory.ExpFrame.Frame.isUnit_natCast_of_not_dvd <;> assumption)
end

