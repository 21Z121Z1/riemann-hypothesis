import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0020
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0017
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0008
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0007
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0012
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0013
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0019
import ReciprocityTheory.AnalyticForms.LeviForms.MixedIntegralInclusionExclusion
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0003
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjugateHermitianLineIsometries
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle0007
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0001
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0008
import ReciprocityTheory.AnalyticForms.PotentialTheory.StokesA
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0021

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.BoundedPshCorrectionLocallySmoothStatement
section
open MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar.PB.Flat ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bounded_psh_correction_locally_smooth : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set X), IsSection A L s → IsSNC A L s m W → ∀ (th : LocPot X) (u : X → ℝ) (M : ℝ), IsPotential A th → A.SmoothOn (bdry s)ᶜ u → IsPshOn A (bdry s)ᶜ (th + LocPot.ofFun u) → IsPshOn A (bdry s)ᶜ ((th + LocPot.ofFun u).rsmul (-1)) → (∀ y ∉ bdry s, |u y| ≤ M) → ∀ x, ∃ (N : Set X) (E : X → ℝ), IsOpen N ∧ x ∈ N ∧ A.SmoothOn N E ∧ ∀ y ∈ N, y ∉ bdry s → E y = u y := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.Flat.locExt | exact GlobalTheory.CompanionTheory.Ar.PB.Flat.locExt | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.Flat.locExt <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ConvDensOfOpen
section
open MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

private theorem fderiv2_add_lemma {D : ℕ} {g₁ g₂ : (Fin D → ℂ) → ℝ} {U : Set (Fin D → ℂ)}
    {y : Fin D → ℂ} (hU : IsOpen U) (hy : y ∈ U) (h₁ : ContDiffOn ℝ 2 g₁ U) (h₂ : ContDiffOn ℝ 2 g₂ U) :
    fderiv ℝ (fderiv ℝ (fun z => g₁ z + g₂ z)) y = fderiv ℝ (fderiv ℝ g₁) y + fderiv ℝ (fderiv ℝ g₂) y := by
  have hev : fderiv ℝ (fun z => g₁ z + g₂ z) =ᶠ[𝓝 y] fun z => fderiv ℝ g₁ z + fderiv ℝ g₂ z := by
    filter_upwards [hU.mem_nhds hy] with z hz
    exact fderiv_add ((h₁.contDiffAt (hU.mem_nhds hz)).differentiableAt (by norm_num))
      ((h₂.contDiffAt (hU.mem_nhds hz)).differentiableAt (by norm_num))
  rw [hev.fderiv_eq]
  exact fderiv_add
    (((h₁.contDiffAt (hU.mem_nhds hy)).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
    (((h₂.contDiffAt (hU.mem_nhds hy)).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))

private theorem hessL_add_lemma_2 {D : ℕ} (H₁ H₂ : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ) :
    hessL (H₁ + H₂) = hessL H₁ + hessL H₂ := by
  funext i k
  simp only [hessL, ContinuousLinearMap.add_apply, Pi.add_apply]
  push_cast
  ring

theorem conv_dens_of_open {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (Θ : LocPot X) (V : Set X) (th : Fin e → LocPot X) (ph : Fin e → X → ℝ)
    (phT : Fin e → ℝ → X → ℝ) (hB : IsOpen V) (hΘ : IsPotential A Θ)
    (hth : ∀ i, IsPotential A (th i)) (hph : ∀ i, A.SmoothOn V (ph i))
    (hT : ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0), ∀ i, A.Smooth (phT i t))
    (hC2 : ∀ i, ∀ j, ∀ K' ⊆ (A.chart j).target ∩ (A.chart j).symm ⁻¹' V, IsCompact K' →
      TendstoUniformlyOn (fun t => fderiv ℝ (fderiv ℝ (phT i t ∘ (A.chart j).symm)))
        (fderiv ℝ (fderiv ℝ (ph i ∘ (A.chart j).symm))) (nhdsWithin 0 (Set.Ioi 0)) K')
    (j : Fin A.n) (K : Set (Fin e → ℂ))
    (hK : K ⊆ (A.chart j).target ∩ (A.chart j).symm ⁻¹' V) (hKc : IsCompact K) :
    TendstoUniformlyOn (fun t => locDens A (fun i => th i + LocPot.ofFun (phT i t) + Θ) j)
      (locDens A (fun i => th i + LocPot.ofFun (ph i) + Θ) j) (nhdsWithin 0 (Set.Ioi 0)) K := by
  classical
  have hS : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' V) :=
    (A.chart j).isOpen_inter_preimage_symm hB
  let a : Fin e → (Fin e → ℂ) → (Fin e → Fin e → ℂ) := fun k y =>
    hessC (fun y' => (th k).φ ((A.chart j).symm y) ((A.chart j).symm y')) y
  let b : (Fin e → ℂ) → (Fin e → Fin e → ℂ) := fun y =>
    hessC (fun y' => Θ.φ ((A.chart j).symm y) ((A.chart j).symm y')) y
  let q : Fin e → (Fin e → ℂ) → (Fin e → Fin e → ℂ) := fun k y =>
    hessL (fderiv ℝ (fderiv ℝ (ph k ∘ (A.chart j).symm)) y)
  let p : Fin e → ℝ → (Fin e → ℂ) → (Fin e → Fin e → ℂ) := fun k t y =>
    hessL (fderiv ℝ (fderiv ℝ (phT k t ∘ (A.chart j).symm)) y)

  have hsplit : ∀ (k : Fin e) (u : X → ℝ) (W : Set (Fin e → ℂ)) (y : Fin e → ℂ), IsOpen W → y ∈ W →
      y ∈ (A.chart j).target → ContDiffOn ℝ 2 (u ∘ (A.chart j).symm) W →
      hessC (fun y' => (th k + LocPot.ofFun u + Θ).φ ((A.chart j).symm y) ((A.chart j).symm y')) y =
        a k y + hessL (fderiv ℝ (fderiv ℝ (u ∘ (A.chart j).symm)) y) + b y := by
    intro k u W y hW hyW hyt hu
    have h1 : ContDiffOn ℝ 2 (fun y' => (th k).φ ((A.chart j).symm y) ((A.chart j).symm y'))
        ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (th k).U ((A.chart j).symm y)) :=
      contDiffOn_infty.1 ((hth k).1 ((A.chart j).symm y) j) 2
    have h3 : ContDiffOn ℝ 2 (fun y' => Θ.φ ((A.chart j).symm y) ((A.chart j).symm y'))
        ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Θ.U ((A.chart j).symm y)) :=
      contDiffOn_infty.1 (hΘ.1 ((A.chart j).symm y) j) 2
    have o1 := (A.chart j).isOpen_inter_preimage_symm ((th k).isOpen_U ((A.chart j).symm y))
    have o3 := (A.chart j).isOpen_inter_preimage_symm (Θ.isOpen_U ((A.chart j).symm y))
    have oU := (o1.inter hW).inter o3
    have mU : y ∈ ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (th k).U ((A.chart j).symm y)) ∩ W ∩
        ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Θ.U ((A.chart j).symm y)) :=
      ⟨⟨⟨hyt, (th k).mem_U _⟩, hyW⟩, ⟨hyt, Θ.mem_U _⟩⟩
    have hu' : ContDiffOn ℝ 2 (fun y' => u ((A.chart j).symm y')) W := hu
    have e12 : ContDiffOn ℝ 2 (fun y' => (th k).φ ((A.chart j).symm y) ((A.chart j).symm y') +
        u ((A.chart j).symm y'))
        (((A.chart j).target ∩ (A.chart j).symm ⁻¹' (th k).U ((A.chart j).symm y)) ∩ W ∩
        ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Θ.U ((A.chart j).symm y))) :=
      (h1.mono fun z hz => hz.1.1).add (hu'.mono fun z hz => hz.1.2)
    show hessL (fderiv ℝ (fderiv ℝ (fun y' => ((th k).φ ((A.chart j).symm y) ((A.chart j).symm y') +
      u ((A.chart j).symm y')) + Θ.φ ((A.chart j).symm y) ((A.chart j).symm y'))) y) = _
    rw [fderiv2_add_lemma oU mU e12 (h3.mono fun z hz => hz.2),
      fderiv2_add_lemma oU mU (h1.mono fun z hz => hz.1.1) (hu'.mono fun z hz => hz.1.2),
      hessL_add_lemma_2, hessL_add_lemma_2]
    rfl

  have hq0 : ∀ k, ContinuousOn (fderiv ℝ (fderiv ℝ (ph k ∘ (A.chart j).symm)))
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' V) := fun k =>
    ((contDiffOn_infty.1 (hph k j) 2).fderiv_of_isOpen hS (m := 1) (by norm_num)).continuousOn_fderiv_of_isOpen
      hS (by norm_num)
  have hq_cont : ∀ k, ContinuousOn (q k) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' V) := fun k =>
    continuous_hessL.comp_continuousOn (hq0 k)
  have hpq : ∀ k, TendstoUniformlyOn (p k) (q k) (nhdsWithin 0 (Set.Ioi 0)) K := by
    intro k
    have hbdd : Bornology.IsBounded (fderiv ℝ (fderiv ℝ (ph k ∘ (A.chart j).symm)) '' K) :=
      (hKc.image_of_continuousOn ((hq0 k).mono hK)).isBounded
    exact tendstoUniformlyOn_comp_continuous hessL continuous_hessL _ _ hbdd (hC2 k j K hK hKc)
  have hW : TendstoUniformlyOn (fun t y => fun k => a k y + p k t y + b y)
      (fun y k => a k y + q k y + b y) (nhdsWithin 0 (Set.Ioi 0)) K := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hk : ∀ k, ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0), ∀ y ∈ K, dist (q k y) (p k t y) < ε :=
      fun k => Metric.tendstoUniformlyOn_iff.1 (hpq k) ε hε
    filter_upwards [Filter.eventually_all.2 hk] with t ht y hy
    rw [dist_pi_lt_iff hε]
    intro k
    rw [dist_add_right, dist_add_left]
    exact ht k y hy
  have hWc : ContinuousOn (fun y k => a k y + q k y + b y) K := by
    refine continuousOn_pi.2 fun k => ?_
    have ha : ContinuousOn (a k) (A.chart j).target := hessC_base_continuousOn A (th k) (hth k) j
    have hb : ContinuousOn b (A.chart j).target := hessC_base_continuousOn A Θ hΘ j
    exact ((ha.mono fun z hz => (hK hz).1).add ((hq_cont k).mono hK)).add (hb.mono fun z hz => (hK hz).1)
  have hG : Continuous (fun w : Fin e → Fin e → Fin e → ℂ =>
      (e.factorial : ℝ) * (2 / Real.pi) ^ e * (mdisc fun k => w k).re) := by
    simp only [mdisc]
    refine continuous_const.mul (Complex.continuous_re.comp ?_)
    refine continuous_const.mul (continuous_finsetSum _ fun S _ => continuous_const.mul ?_)
    exact Continuous.matrix_det (continuous_finsetSum _ fun k _ => continuous_apply k)
  have hmain := tendstoUniformlyOn_comp_continuous _ hG _ _
    (hKc.image_of_continuousOn hWc).isBounded hW
  refine (hmain.congr ?_).congr_right ?_
  · filter_upwards [hT] with t ht y hy
    have hfun : (fun k => a k y + p k t y + b y) = fun k => hessC
        (fun y' => (th k + LocPot.ofFun (phT k t) + Θ).φ ((A.chart j).symm y) ((A.chart j).symm y')) y :=
      funext fun k => (hsplit k (phT k t) _ y ((A.chart j).isOpen_inter_preimage_symm isOpen_univ)
        ⟨(hK hy).1, trivial⟩ (hK hy).1 (contDiffOn_infty.1 (ht k j) 2)).symm
    show (e.factorial : ℝ) * (2 / Real.pi) ^ e * (mdisc fun k => (fun k => a k y + p k t y + b y) k).re = _
    rw [hfun]
    rfl
  · intro y hy
    have hfun : (fun k => a k y + q k y + b y) = fun k => hessC
        (fun y' => (th k + LocPot.ofFun (ph k) + Θ).φ ((A.chart j).symm y) ((A.chart j).symm y')) y :=
      funext fun k => (hsplit k (ph k) _ y hS (hK hy) (hK hy).1 (contDiffOn_infty.1 (hph k j) 2)).symm
    show (e.factorial : ℝ) * (2 / Real.pi) ^ e * (mdisc fun k => (fun k => a k y + q k y + b y) k).re = _
    rw [hfun]
    rfl

end GlobalTheory.CompanionTheory.Ar.Giv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsFormDefiningValueStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Small Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_form_defining_value : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω), Birational y → IsRelevant (mCoordIdeal y) → ∀ (a : K → ℤ) (s : Ω), ∃ h : MRing ι, IsFormOff (mCoordIdeal y) h ∧ ∀ (𝕜 : Type) [Field 𝕜] (z : (Σ k, ι k) → 𝕜), aeval z h ≠ 0 → ∃ w, HasVal y a s z w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Small.exists_form_hasVal | exact GlobalTheory.CompanionTheory.Ar.Small.exists_form_hasVal | (intros; apply GlobalTheory.CompanionTheory.Ar.Small.exists_form_hasVal <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FormOffVarietyMulStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Small Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.form_off_variety_mul : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (d : ℕ) (u v : MRing ι), IsArithVar (mCoordIdeal y) d → IsFormOff (mCoordIdeal y) u → IsFormOff (mCoordIdeal y) v → IsFormOff (mCoordIdeal y) (u * v) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Small.isFormOff_mul_of_arith | exact GlobalTheory.CompanionTheory.Ar.Small.isFormOff_mul_of_arith | (intros; apply GlobalTheory.CompanionTheory.Ar.Small.isFormOff_mul_of_arith <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HermitianLineShiftPropertiesStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Small Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_line_shift_properties : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (A : HermLine ι) (t Λ : ℝ), (IsSmoothHerm A → IsSmoothHerm (shiftH A t)) ∧ (IsNefH P A → IsNefH P (shiftH A t)) ∧ (IsGenH P A Λ → IsGenH P (shiftH A t) (Λ * Real.exp (-t))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Small.shiftH_props | exact GlobalTheory.CompanionTheory.Ar.Small.shiftH_props | (intros; apply GlobalTheory.CompanionTheory.Ar.Small.shiftH_props <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LineIsomorphismDefectFunction
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace GlobalTheory.CompanionTheory.Ar.Cmp

theorem defect_exists_smooth : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (e : ℕ) (R : AnLogRes P J e) (A B : HermLine ι) (f g : MRing ι), IsMultiProjPrime P → IsLineIso P A.a B.a f g → IsSmoothHerm A → IsSmoothHerm B → ∃ w : ((Σ k, ι k) → ℂ) → ℝ, IsDefectOn P (mcPts P) f g A B w ∧ (∀ z ∈ mcPts P, ∀ z', SameOrbit z z' → w z = w z') ∧ R.A.Smooth (fun x => w (R.lift x x)) :=
  @PositivityTheory.UnitarySelfGeneration.i_defect

end GlobalTheory.CompanionTheory.Ar.Cmp
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalBruhatCellAnalyticCoordinatesStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_bruhat_cell_analytic_coordinates : ∀ (e N : ℕ) (g : (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ) (x₀ : Fin e → ℂ), (∀ a b, AnalyticAt ℂ (fun x => g x a b) x₀) → (g x₀).BlockTriangular id → IsUnit (g x₀).det → ∃ (z : (Fin e → ℂ) → Pairs N → ℂ) (b : (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ), AnalyticAt ℂ z x₀ ∧ (∀ p q, AnalyticAt ℂ (fun x => b x p q) x₀) ∧ z x₀ = 0 ∧ (∀ᶠ x in 𝓝 x₀, (b x).BlockTriangular id ∧ IsUnit (b x).det ∧ g x = cellMat N (z x) * b x) ∧ ∀ v, fderiv ℂ z x₀ v = 0 ↔ ((g x₀)⁻¹ * Matrix.of fun p q => fderiv ℂ (fun x => g x p q) x₀ v).BlockTriangular id := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.holomorphic_factor_big_cell | exact GlobalTheory.CompanionTheory.Ar.PB.holomorphic_factor_big_cell | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.holomorphic_factor_big_cell <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogDetGramSubharmonicStatement
section
open Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_det_comparable_gram_bound : ∀ (n k : ℕ) (G G₀ : Matrix (Fin n) (Fin n) ℂ) (V : Matrix (Fin n) (Fin k) ℂ) (m : ℝ), 1 ≤ m → G₀.PosDef → G.PosDef → ((m : ℂ) • G₀ - G).PosSemidef → ((m : ℂ) • G - G₀).PosSemidef → LinearIndependent ℂ Vᵀ → |Real.log (Vᴴ * G * V).det.re - Real.log (Vᴴ * G₀ * V).det.re| ≤ k * Real.log m := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.gram_det_log_size | exact GlobalTheory.CompanionTheory.Ar.PB.gram_det_log_size | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.gram_det_log_size <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereIntegralMultilinearExpansion
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem hessC_finset_sum_mul {D : ℕ} {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (f : ι → (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (hf : ∀ a, ContDiffAt ℝ 2 (f a) z) :
    hessC (fun y => ∑ a ∈ s, c a * f a y) z = ∑ a ∈ s, (c a : ℂ) • hessC (f a) z := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using st_hessC_eq_zero (f := fun _ => (0 : ℝ)) (y := z) 0 (Eventually.of_forall fun _ => rfl)
  | insert a s ha ih =>
    have h1 : ContDiffAt ℝ 2 (fun y => c a * f a y) z := contDiffAt_const.mul (hf a)
    have h2 : ContDiffAt ℝ 2 (fun y => ∑ b ∈ s, c b * f b y) z :=
      ContDiffAt.sum fun b _ => contDiffAt_const.mul (hf b)
    simp only [Finset.sum_insert ha]
    rw [hessC_add' _ _ z h1 h2, ih, hessC_const_mul']

theorem mdisc_sum_smul {D : ℕ} {σ : Type*} [Fintype σ] (H : σ → Matrix (Fin D) (Fin D) ℂ)
    (c : Fin D → σ → ℂ) :
    mdisc (fun i => ∑ a, c i a • H a) =
      ∑ w : Fin D → σ, (∏ i, c i (w i)) * mdisc (fun i => H (w i)) := by
  classical
  obtain ⟨M, hM⟩ := ReciprocityTheory.AnForm.A.exists_multilinearMap_eq_mdisc (D := D)
  rw [← hM, M.map_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [M.map_smul_univ, smul_eq_mul]

theorem locDens_sumPot_expand {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    {σ : Type} [Fintype σ] (P : σ → LocPot X) (c : Fin e → σ → ℝ) (j : Fin A.n)
    {y : Fin e → ℂ} (hy : y ∈ (A.chart j).target)
    (hC : ∀ a, IsTwiceDifferentiableAt A (P a) ((A.chart j).symm y)) :
    locDens A (fun i => sumPot (c i) P) j y =
      ∑ w : Fin e → σ, (∏ i, c i (w i)) * locDens A (fun i => P (w i)) j y := by
  classical
  have hf : ∀ a, ContDiffAt ℝ 2
      (fun y' => (P a).φ ((A.chart j).symm y) ((A.chart j).symm y')) y := by
    intro a
    have := hC a j ((A.chart j).map_target hy)
    rwa [(A.chart j).right_inv hy] at this
  have hH : ∀ i, hessC (fun y' => (sumPot (c i) P).φ ((A.chart j).symm y) ((A.chart j).symm y')) y =
      ∑ a, ((c i a : ℝ) : ℂ) •
        hessC (fun y' => (P a).φ ((A.chart j).symm y) ((A.chart j).symm y')) y := fun i =>
    hessC_finset_sum_mul Finset.univ (c i) _ y hf
  simp only [locDens, maDens, hH]
  rw [mdisc_sum_smul, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← Complex.ofReal_prod, Complex.re_ofReal_mul]
  ring

theorem mInt_sumPot_expand (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas e X) (σ : Type) [Fintype σ] (U : Set X) (P : σ → LocPot X)
    (c : Fin e → σ → ℝ) (g : X → ℝ) (hN : IsNull A Uᶜ)
    (hC : ∀ a, ∀ x ∈ U, IsTwiceDifferentiableAt A (P a) x)
    (hI : ∀ w : Fin e → σ, MIntegrable A (fun i => P (w i)) g) :
    MIntegrable A (fun i => sumPot (c i) P) g ∧
      mInt A (fun i => sumPot (c i) P) g =
        ∑ w : Fin e → σ, (∏ i, c i (w i)) * mInt A (fun i => P (w i)) g := by
  classical
  have key : ∀ j, ∀ᵐ y, y ∈ (A.chart j).target →
      locDens A (fun i => sumPot (c i) P) j y =
        ∑ w : Fin e → σ, (∏ i, c i (w i)) * locDens A (fun i => P (w i)) j y := by
    intro j
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (hN j)] with y hy hyt
    have hU : (A.chart j).symm y ∈ U := by
      by_contra h
      exact hy ⟨hyt, h⟩
    exact locDens_sumPot_expand A P c j hyt fun a => hC a _ hU
  refine ⟨fun j K hK hKc => ?_, ?_⟩
  · have h1 : IntegrableOn (fun y => ∑ w : Fin e → σ, (∏ i, c i (w i)) *
        (g ((A.chart j).symm y) * locDens A (fun i => P (w i)) j y)) K :=
      integrable_finsetSum _ fun w _ => (hI w j K hK hKc).const_mul _
    refine Integrable.congr h1 ?_
    filter_upwards [ae_restrict_of_ae (key j), ae_restrict_mem hKc.measurableSet] with y hy hyK
    rw [hy (hK hyK), Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    ring
  · have h : Nonempty (ChartPartition A) := existsPartition A
    simp only [mInt, dif_pos h, integralWith]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hw : ∀ w : Fin e → σ, IntegrableOn (fun y => (∏ i, c i (w i)) *
        (h.some.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) *
          locDens A (fun i => P (w i)) j y)) (A.chart j).target := fun w =>
      (integrableOn_weight A h.some _ g (hI w) j).const_mul _
    simp only [← integral_const_mul]
    rw [← integral_finsetSum _ fun w _ => hw w]
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae (key j),
      ae_restrict_mem (A.chart j).open_target.measurableSet] with y hy hyt
    rw [hy hyt, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    ring

end GlobalTheory.CompanionTheory.Ar.PB
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MultihomogeneousValueWellDefinedStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Small Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multihomogeneous_value_well_defined : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (𝕜 : Type) [Field 𝕜] (a : K → ℤ) (s : Ω) (z : (Σ k, ι k) → 𝕜) (w : 𝕜), z ∈ ptsOver 𝕜 (mCoordIdeal y) → HasVal y a s z w → (∀ (dg dh : K → ℕ) (g h : MRing ι), IsMultiHomog g dg → IsMultiHomog h dh → (∀ k, (dg k : ℤ) = dh k + a k) → aeval y g = s * aeval y h → aeval z g = w * aeval z h) ∧ ∀ w', HasVal y a s z w' → w' = w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Small.hasVal_read_of_rep | exact GlobalTheory.CompanionTheory.Ar.Small.hasVal_read_of_rep | (intros; apply GlobalTheory.CompanionTheory.Ar.Small.hasVal_read_of_rep <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SingularWeightMonotoneRegularizationStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.singular_weight_monotone_regularization : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (Θ : LocPot X) (L : LocPot X) (s : X → X → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set X), IsPotential A L → IsSection A L s → IsSNC A L s m W → (∀ y, logNormSec L s y ≤ 0) → IsPotential A Θ → IsPosPot A Θ → (∀ th ph C₅ C₅', C₅ ≤ C₅' → IsSingWeight A L s th ph C₅ → IsSingWeight A L s th ph C₅') ∧ (∀ th ph phT C t₀ C' t₀', |C| ≤ C' → 0 < t₀' → t₀' ≤ t₀ → t₀' ≤ Real.exp (-1) → IsRegFamily A Θ L s th ph phT C t₀ → IsPotential A th → IsRegFamily A Θ L s th ph phT C' t₀') ∧ ∀ th u, IsPotential A th → A.Smooth u → IsPsh A (th + LocPot.ofFun u) → ∃ C₀, IsSingWeight A L s th u C₀ ∧ IsRegFamily A Θ L s th u (fun _ => u) C₀ (Real.exp (-Real.exp 1)) ∧ IsRegFamilyC2 A s u (fun _ => u) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.enlarging_constants_smooth_members | exact GlobalTheory.CompanionTheory.Ar.PB.enlarging_constants_smooth_members | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.enlarging_constants_smooth_members <;> assumption)
end

