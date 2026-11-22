import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0034
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0036
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0029
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0051
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0019
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Bundle0018
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0015
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0031
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0032
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsVertPointLengthSteps
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0052

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStdBaseChange
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.ChartRestriction.G.AI.I1 MvPolynomial

namespace StandardDualBaseChange

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {T : Type} [Fintype T] [DecidableEq T]

theorem isMultiHomog_linForm (A : ∀ _ : Unit, Fin i → T → ℤ) (q : Σ _ : Unit, Fin i) :
    IsMultiHomog (linForm (ι := dualBlocks T) (ι₂ := PBlk i) A q) fun _ => 1 := by
  classical
  intro m hm k
  obtain ⟨t, -, ht⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hm)
  rw [C_mul_X_eq_monomial] at ht
  have hmt := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset ht)
  subst hmt
  cases k
  simp [Finsupp.single_apply]

omit [DecidableEq T] in

theorem exists_linForm_not_mem (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i)))
    (hP : IsArithVar (dualIdeal b) i)
    (hBP : IsBasePtFree (K₂ := Unit) (ι₂ := PBlk i) (dualIdeal b) (linForm (ι₂ := PBlk i) (dualStdCoordMat b))) :
    ∀ k₂ : Unit, ∃ j, linForm (ι₂ := PBlk i) (dualStdCoordMat b) ⟨k₂, j⟩ ∉ dualIdeal b := by
  intro k₂
  by_contra hall
  simp only [not_exists, not_not] at hall
  obtain ⟨-, ⟨hprime, -, hrel⟩, -, -⟩ := hP
  obtain ⟨t, ht⟩ := hrel ()
  obtain ⟨N, hN⟩ := hBP k₂ fun _ => t
  have hle : Ideal.span (Set.range fun j : Fin i =>
      linForm (ι₂ := PBlk i) (dualStdCoordMat b) ⟨k₂, j⟩) ≤ dualIdeal b :=
    Ideal.span_le.mpr (Set.range_subset_iff.mpr hall)
  rw [sup_eq_left.mpr hle, Fintype.prod_unique] at hN
  exact ht (hprime.mem_of_pow_mem N hN)

end StandardDualBaseChange

open StandardDualBaseChange in

theorem DualStdBaseChange.proof (hCM : ChangeOfModelStatement) (hGr : GraphStatement)
    (hGF : GenFibreExistsStatement)
    (hEU : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
      ExistsUniqueStatement F ι)
    (hBP : DualStdBasePtFree.Statement) (hIm : DualStdImageBot.Statement)
    (hDeg : DualStdGenDeg.Statement) (hMet : DualStdMetricPull.Statement) :
    DualStdBaseChange.Statement := by
  intro K _ _ i T _ _ b hb II hi hII
  have hP : IsArithVar (dualIdeal b) i :=
    DualArithVar.proof (CoordConeArithVar.proof IntDomainDim.proof) K i _ T b hi
  have hBPb := hBP K i T b
  have hGraph := (hGr Unit (dualBlocks T) Unit (PBlk i) (dualIdeal b) i
    (linForm (ι₂ := PBlk i) (dualStdCoordMat b)) (fun _ _ => 1) hP
    (isMultiHomog_linForm _) (exists_linForm_not_mem b hP hBPb)).1
  obtain ⟨G⟩ := hGF Unit (PBlk i) (Unit ⊕ Unit) (Sum.elim (dualBlocks T) (PBlk i)) Sum.inr inrV _ i
    isBlockMap_inr hGraph
  obtain ⟨J, hJ, -⟩ := hEU G.Φ _ (fibreIdx (Sum.elim (dualBlocks T) (PBlk i)) (Sum.inr : Unit → Unit ⊕ Unit))
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
  have hbot : IsArithVar (imageZ (inrV (ι := dualBlocks T) (ι₂ := PBlk (n + 1)))
      (graphIdeal (dualIdeal b) (linForm (ι₂ := PBlk (n + 1)) (dualStdCoordMat b)))) (n + 1) := by
    rw [hIm K (n + 1) T b]
    exact IndefiniteRowSideFullHecke.Inter.isArithVar_bot n
  have key := hCM II hII Unit (dualBlocks T) (PBlk (n + 1)) (dualIdeal b) (n + 1) (dualStdCoordMat b) G J
    (fun _ => fsMulti (PBlk (n + 1))) (fun _ => dualLine (HermLattice.standard K (n + 1)) b hb)
    hP hBPb hbot hJ (fun _ => FsLineSmooth.proof Unit (PBlk (n + 1)))
    (fun _ => (DualLineSemipositive.proof K (n + 1) _ T b hb).1) (fun _ => rfl)
    (fun _ z hz => hMet K (n + 1) T b hb z hz)
  rw [key, hDeg K (n + 1) T b G J hi hJ, hIm K (n + 1) T b]
  push_cast
  rfl

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualTopMetricChange
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 NumberField

noncomputable section

namespace TopDualMetricChange

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {T : Type} [Fintype T] [DecidableEq T]

theorem hermLine_ext {A B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine (dualBlocks T)}
    (ha : A.a = B.a) (hh : A.h = B.h) : A = B := by
  cases A; cases B; cases ha; cases hh; rfl

theorem dualLine_h_zero (F : HermLattice K i) (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (z : (Σ _ : Unit, T) → ℂ)
    (hz : ¬ ∀ k : Unit, ∃ t, z ⟨k, t⟩ ≠ 0) : (dualLine F b hb).h z = 0 := by
  have h0 : (fun t => z ⟨(), t⟩) = 0 := by
    funext t; by_contra h; exact hz fun _ => ⟨t, h⟩
  show Real.sqrt (dualNormSq b hb fun t => z ⟨(), t⟩) = 0
  rw [h0]
  simp [dualNormSq, ← Pi.zero_def]

def weight (F : HermLattice K i) (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) : ((Σ _ : Unit, T) → ℂ) → ℝ :=
  fun z => Real.log ((dualLine F.withStdMetric b hb).h z) - Real.log ((dualLine F b hb).h z)

theorem weight_hom (F : HermLattice K i) (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) :
    ∀ (c : Unit → ℂ) z, (∀ k, c k ≠ 0) → weight F b hb (fun p => c p.1 * z p) = weight F b hb z := by
  intro c z hc
  by_cases hz : ∀ k : Unit, ∃ t, z ⟨k, t⟩ ≠ 0
  · simp only [weight]
    rw [(dualLine F.withStdMetric b hb).smul c z hc, (dualLine F b hb).smul c z hc]
    have ha : (dualLine F.withStdMetric b hb).a = (dualLine F b hb).a := rfl
    have hs : 0 < ∏ k, ‖c k‖ ^ (dualLine F b hb).a k :=
      Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.mpr (hc k)) _
    rw [ha, Real.log_mul hs.ne' ((dualLine F.withStdMetric b hb).pos z hz).ne',
      Real.log_mul hs.ne' ((dualLine F b hb).pos z hz).ne']
    ring
  · have hz0 : ∀ p, z p = 0 := by
      rintro ⟨k, t⟩; by_contra h; exact hz fun _ => ⟨t, h⟩
    congr 1; funext p; simp [hz0 p]

theorem weight_smooth (F : HermLattice K i) (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) : SmoothFn (weight F b hb) :=
  ((DualLineSemipositive.proof K i F.withStdMetric T b hb).1.log fun z hz =>
      ((dualLine F.withStdMetric b hb).pos z hz).ne').sub
    ((DualLineSemipositive.proof K i F T b hb).1.log fun z hz => ((dualLine F b hb).pos z hz).ne')

theorem dualLine_eq_tensor (F : HermLattice K i) (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) :
    dualLine F b hb = (dualLine F.withStdMetric b hb).tensor
      (ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofWeight (weight F b hb) (weight_hom F b hb)) := by
  refine hermLine_ext (funext fun _ => by simp [ReciprocityTheory.ChartRestriction.G.Geo.HermLine.tensor, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofWeight, dualLine]) ?_
  funext z
  show (dualLine F b hb).h z = (dualLine F.withStdMetric b hb).h z * Real.exp (-weight F b hb z)
  by_cases hz : ∀ k : Unit, ∃ t, z ⟨k, t⟩ ≠ 0
  · have h1 := (dualLine F.withStdMetric b hb).pos z hz
    have h2 := (dualLine F b hb).pos z hz
    rw [weight, neg_sub, Real.exp_sub, Real.exp_log h1, Real.exp_log h2]
    field_simp
  · rw [dualLine_h_zero F b hb z hz, dualLine_h_zero F.withStdMetric b hb z hz, zero_mul]

theorem ptsIntegral_neg {κ : Type} [Fintype κ] {ι : κ → Type} [∀ k, Fintype (ι k)] {e : ℕ}
    (P : Ideal (MRing ι)) (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (g : ((Σ k, ι k) → ℂ) → ℝ) :
    ptsIntegral P φ (fun z => -g z) = -ptsIntegral P φ g := by
  have hs : ∀ Ψ y w, sheetDensity P Ψ φ (fun z => -g z) y w = -sheetDensity P Ψ φ g y w := by
    intro Ψ y w
    unfold sheetDensity
    split_ifs <;> simp [neg_mul]
  unfold ptsIntegral ptsIntegralAt
  split_ifs
  · rw [← MeasureTheory.integral_neg]
    simp only [hs, finsum_neg_distrib]
  · simp

theorem degree_withStdMetric_sub (F : HermLattice K i) :
    F.withStdMetric.degree - F.degree = 1 / 2 * ∑ σ : K →+* ℂ, Real.log (F.metric σ).det.re := by
  simp only [HermLattice.degree, subDegree, HermLattice.withStdMetric, IndefiniteRowSideFullHecke.Kernels.gramAt_single,
    Matrix.det_one, Complex.one_re, Real.log_one, Finset.sum_const_zero, mul_zero, sub_zero]
  ring

end TopDualMetricChange

open TopDualMetricChange in

theorem DualTopMetricChange.proof (hTel : TelescopeStatement) (hEnergy : DualMetricEnergy.Statement) :
    DualTopMetricChange.Statement := by
  intro K _ _ i F T _ _ b hb II hi hII
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
  have hP : IsArithVar (dualIdeal b) (n + 1) :=
    DualArithVar.proof (CoordConeArithVar.proof IntDomainDim.proof) K (n + 1) F T b hi
  have hT := hTel Unit (dualBlocks T) (II Unit (dualBlocks T)) (hII Unit (dualBlocks T)) (dualIdeal b) n
    (dualLine F.withStdMetric b hb) (weight F b hb) (weight_hom F b hb) hP
    (DualLineSemipositive.proof K (n + 1) F.withStdMetric T b hb).1 (weight_smooth F b hb)
  rw [← dualLine_eq_tensor F b hb] at hT
  have hw : weight F b hb = fun z =>
      -(Real.log ((dualLine F b hb).h z) - Real.log ((dualLine F.withStdMetric b hb).h z)) := by
    funext z; simp only [weight]; ring
  rw [hw] at hT
  simp only [ptsIntegral_neg, Finset.sum_neg_distrib, neg_neg] at hT
  have hE : ∑ k ∈ Finset.range (n + 1),
      ptsIntegral (dualIdeal b)
        (pot fun j : Fin n => if (j : ℕ) < k then dualLine F b hb else dualLine F.withStdMetric b hb)
        (fun z => Real.log ((dualLine F b hb).h z) - Real.log ((dualLine F.withStdMetric b hb).h z)) =
      1 / 2 * (∑ σ : K →+* ℂ, Real.log (F.metric σ).det.re) *
        geomDeg (grassIdeal 1 1 (n + 1 - 1)) (fsMulti (plBlocks 1 1 (n + 1 - 1))) (1 * 1 * (n + 1 - 1)) :=
    hEnergy K (n + 1) F T b hb hi
  rw [degree_withStdMetric_sub F]
  linarith

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSectionQuotLocal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

noncomputable section

namespace SectionQuotientLocal

variable {T : Type} {K' : Type} [Field K'] (y : (Σ _ : Unit, T) → K')

theorem coord_mem_sectionMod (t : T) : y ⟨(), t⟩ ∈ sectionMod y := by
  show ∀ c : Unit → T, (∀ k, y ⟨k, c k⟩ ≠ 0) → _ ∈ chartRingZ y c
  intro c _
  have hg : y ⟨(), t⟩ / y ⟨(), c ()⟩ ∈ chartRingZ y c := by
    unfold chartRingZ
    exact Algebra.subset_adjoin ⟨⟨(), t⟩, rfl⟩
  simpa [div_eq_mul_inv] using hg

theorem exists_mul_mem_of_mem_chartRingZ (m : Ideal (curveRing y)) (hm : m.IsPrime) (t : T)
    (h : ∀ u : T, ∃ a b : curveRing y, b ∉ m ∧ (b : K') * (y ⟨(), u⟩ / y ⟨(), t⟩) = a)
    {z : K'} (hz : z ∈ chartRingZ y (fun _ => t)) :
    ∃ a b : curveRing y, b ∉ m ∧ (b : K') * z = a := by
  induction hz using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨⟨⟨⟩, u⟩, rfl⟩ := hx
    exact h u
  | algebraMap r =>
    refine ⟨(r : curveRing y), 1, (Ideal.ne_top_iff_one m).mp hm.ne_top, ?_⟩
    simp
  | add x z _ _ hx hz =>
    obtain ⟨a₁, b₁, hb₁, e₁⟩ := hx
    obtain ⟨a₂, b₂, hb₂, e₂⟩ := hz
    refine ⟨b₂ * a₁ + b₁ * a₂, b₁ * b₂, fun hmem => (hm.mem_or_mem hmem).elim hb₁ hb₂, ?_⟩
    push_cast
    rw [← e₁, ← e₂]
    ring
  | mul x z _ _ hx hz =>
    obtain ⟨a₁, b₁, hb₁, e₁⟩ := hx
    obtain ⟨a₂, b₂, hb₂, e₂⟩ := hz
    refine ⟨a₁ * a₂, b₁ * b₂, fun hmem => (hm.mem_or_mem hmem).elim hb₁ hb₂, ?_⟩
    push_cast
    rw [← e₁, ← e₂]
    ring

end SectionQuotientLocal

open SectionQuotientLocal in

theorem SectionQuotLocal.proof : SectionQuotLocal.Statement := by
  intro T _ K' _ _ y s _hy hs hsP m t hm hrat a b hb hba
  set x := aeval y s with hx_def
  have hx0 : x ≠ 0 := SectionQuotientFinite.aeval_ne_zero y hs hsP
  have hyt : y ⟨(), t⟩ ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hba
    rcases mul_eq_zero.mp hba with h | h
    · have hb0 : b = 0 := by exact_mod_cast h
      exact hb (hb0 ▸ m.zero_mem)
    · exact hx0 h

  let e : sectionMod y := ⟨y ⟨(), t⟩, coord_mem_sectionMod y t⟩
  let φ : curveRing y →ₗ[curveRing y] sectionQuot y x :=
    LinearMap.toSpanSingleton (curveRing y) _ (Submodule.Quotient.mk e)
  have hφ : ∀ β : curveRing y, φ β = Submodule.Quotient.mk (β • e) := fun β => by
    simp [φ, Submodule.Quotient.mk_smul]
  have hφ0 : ∀ β : curveRing y, φ β = 0 ↔ ∃ γ : curveRing y, (γ : K') * x = β * y ⟨(), t⟩ := by
    intro β
    rw [hφ, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.mem_span_singleton]
    rfl
  have hle : Ideal.span {a} ≤ LinearMap.ker φ := by
    rw [Ideal.span_singleton_le_iff_mem, LinearMap.mem_ker, hφ0]
    exact ⟨b, hba⟩
  let ψ : (curveRing y ⧸ Ideal.span {a}) →ₗ[curveRing y] sectionQuot y x := (Ideal.span {a}).liftQ φ hle

  have hker : ∀ q, ψ q = 0 → b • q = 0 := by
    intro q hq
    obtain ⟨β, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨γ, hγ⟩ := (hφ0 β).mp hq
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, smul_eq_mul,
      Ideal.mem_span_singleton']
    refine ⟨γ, Subtype.ext ?_⟩
    push_cast
    apply mul_right_cancel₀ hyt
    rw [mul_assoc, ← hba, mul_assoc, ← hγ]
    ring

  have hsurj0 : ∀ n : sectionMod y, ∃ r : curveRing y, r ∉ m ∧ ∃ β : curveRing y, r • n = β • e := by
    intro n
    have hn : (n : K') ∈ chartLat y (fun _ => 1) 1 := n.2
    have hnt : (n : K') * (y ⟨(), t⟩)⁻¹ ∈ chartRingZ y (fun _ => t) := by
      simpa using hn (fun _ => t) (fun _ => hyt)
    obtain ⟨β, r, hr, hβ⟩ := exists_mul_mem_of_mem_chartRingZ y m hm t hrat hnt
    refine ⟨r, hr, β, Subtype.ext ?_⟩
    show (r : K') * n = β * y ⟨(), t⟩
    rw [← hβ]
    field_simp

  let S := m.primeCompl
  let Φ := IsLocalizedModule.map S (LocalizedModule.mkLinearMap S (curveRing y ⧸ Ideal.span {a}))
    (LocalizedModule.mkLinearMap S (sectionQuot y x)) ψ
  have hΦ : ∀ q (r : S), Φ (LocalizedModule.mk q r) = LocalizedModule.mk (ψ q) r :=
    fun q r => IsLocalizedModule.map_LocalizedModules S _ q r
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    intro z
    refine LocalizedModule.induction_on (β := fun z => Φ z = 0 → z = 0) (fun q r hz => ?_) z
    rw [hΦ, ← LocalizedModule.zero_mk r, LocalizedModule.mk_eq] at hz
    obtain ⟨u, hu⟩ := hz
    simp only [smul_zero, Submonoid.smul_def] at hu
    rw [← map_smul, ← map_smul] at hu
    have hq := hker _ hu
    rw [← LocalizedModule.zero_mk r, LocalizedModule.mk_eq]
    refine ⟨⟨b * u, S.mul_mem hb u.2⟩, ?_⟩
    simp only [smul_zero, Submonoid.smul_def, mul_smul]
    exact hq
  have hsurj : Function.Surjective Φ := by
    intro z
    refine LocalizedModule.induction_on (β := fun z => ∃ w, Φ w = z) (fun n r => ?_) z
    obtain ⟨n', rfl⟩ := Submodule.Quotient.mk_surjective _ n
    obtain ⟨r', hr', β, hβ⟩ := hsurj0 n'
    refine ⟨LocalizedModule.mk (Submodule.Quotient.mk β) (⟨r', hr'⟩ * r), ?_⟩
    rw [hΦ]
    have hψ : ψ (Submodule.Quotient.mk β) = Submodule.Quotient.mk (β • e) := by
      rw [← hφ]
      rfl
    rw [hψ, ← hβ, Submodule.Quotient.mk_smul]
    exact LocalizedModule.mk_cancel_common_left ⟨r', hr'⟩ r _
  have := hm
  let E := (LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩).extendScalarsOfIsLocalization S
    (Localization.AtPrime m)
  unfold locLen
  rw [dif_pos hm, dif_pos hm, E.length_eq]

end

end GroundTheory.Heights₂.Heights
end

