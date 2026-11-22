import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0109
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0110
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0102
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0108
import GroundTheory.HeightsAndTheta.Heights.Intersections.FourierIntegralBound
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0045
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0021
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0006
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0101
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0103
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0107
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPullSectionIntegralInt
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0092
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0099
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0095
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0088
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0098
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0064
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0042
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0024
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0081
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0086
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0052
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0044
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0001

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ComponentResBadNullFlat
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel.ResBridge

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Topology Filter Set

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {W : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {e : ℕ} (R : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.Res ι W e)

theorem isAnalyticSubset_D :
    R.atlas.IsAnalyticSubset {x | R.pt x ∈ ReciprocityTheory.AnForm.R.conePts R.D} := by
  intro x
  set i := R.idx x
  obtain ⟨n, g, hg⟩ :=
    (Submodule.fg_iff_exists_fin_generating_family).mp (IsNoetherian.noetherian (R.R.bd i))
  refine ⟨R.R.src i, R.R.isOpen_alt_bis i, R.mem_src_idx x, n, fun l y => eval (R.R.coord i y) (g l),
    fun l => R.isGoodAtlas.1 i (g l), ?_⟩
  ext y
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hyD, hy⟩
    refine ⟨hy, fun l => ?_⟩
    have hz := (R.R.zero_bd i y hy).mpr ((pt_mem_D_iff R hy).mp hyD)
    have hgl : g l ∈ R.R.bd i := by
      rw [← hg]
      exact Submodule.subset_span ⟨l, rfl⟩
    exact hz _ hgl
  · rintro ⟨hy, hz⟩
    refine ⟨(pt_mem_D_iff R hy).mpr ((R.R.zero_bd i y hy).mp fun h hh => ?_), hy⟩
    rw [← hg] at hh
    induction hh using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨l, rfl⟩ := ha
      exact hz l
    | zero => simp
    | add a b _ _ ha hb => simp [ha, hb]
    | smul a b _ hb => simp [smul_eq_mul, hb]

theorem interior_D : interior {x | R.pt x ∈ ReciprocityTheory.AnForm.R.conePts R.D} = ∅ := by
  by_contra hne
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hne
  set i := R.idx x
  have hxi : x ∈ R.R.src i := R.mem_src_idx x
  set sd := R.R.sncAt i x hxi
  have hcont : ContinuousOn (fun y => eval (R.R.coord i y) sd.h) (R.R.src i) :=
    (MvPolynomial.continuous_eval sd.h).comp_continuousOn
      (continuousOn_iff_continuous_domRestrict.mpr (R.R.isEmbedding i).continuous)
  set O := interior {x | R.pt x ∈ ReciprocityTheory.AnForm.R.conePts R.D} ∩
    (R.R.src i ∩ (fun y => eval (R.R.coord i y) sd.h) ⁻¹' {0}ᶜ) with hOdef
  have hO : IsOpen O :=
    isOpen_interior.inter (hcont.isOpen_inter_preimage (R.R.isOpen_alt_bis i) isOpen_compl_singleton)
  have hxO : x ∈ O := ⟨hx, hxi, sd.eval_h⟩
  obtain ⟨ψ, -, hxψ, hsub, hform⟩ := R.isGoodAtlas.2 i x hxi sd.r sd.span_eq O hO hxO
  have hnull : volume ψ.target = 0 := by
    refine measure_mono_null (t := ⋃ l : Fin e, {u : Fin e → ℂ | u l = 0}) ?_
      (measure_iUnion_null fun l => ?_)
    · intro u hu
      have hy : ψ.symm u ∈ ψ.source := ψ.map_target hu
      have hyO := hsub hy
      have hyD : R.pt (ψ.symm u) ∈ ReciprocityTheory.AnForm.R.conePts R.D :=
        (interior_subset (s := {x | R.pt x ∈ ReciprocityTheory.AnForm.R.conePts R.D}) hyO.1.1 :)
      have hbd := (R.R.zero_bd i (ψ.symm u) hyO.2).mpr ((pt_mem_D_iff R (x := x) hyO.2).mp hyD)
      have h0 := hbd _ sd.mem_bd
      rw [map_mul, map_prod] at h0
      have hprod := (mul_eq_zero.mp h0).resolve_left hyO.1.2.2
      obtain ⟨l, -, hl0⟩ := Finset.prod_eq_zero_iff.mp hprod
      have hu' : u = ReciprocityTheory.AnForm.R.evalFam sd.r (R.R.coord i (ψ.symm u)) :=
        (ψ.right_inv hu).symm.trans (hform _ hy)
      exact Set.mem_iUnion.mpr ⟨l, (congrFun hu' l).trans hl0⟩
    · rw [MeasureTheory.volume_pi]
      exact Measure.pi_hyperplane _ l 0
  exact (ψ.open_target.measure_pos volume ⟨ψ x, ψ.map_source hxψ⟩).ne' hnull

theorem D_null (j : Fin R.atlas.n) :
    volume ((R.atlas.chart j).target ∩
      (R.atlas.chart j).symm ⁻¹' {x | R.pt x ∈ ReciprocityTheory.AnForm.R.conePts R.D}) = 0 := by
  refine measure_mono_null ?_
    (ReciprocityTheory.AnForm.M.analyticNull R.atlas _ (isAnalyticSubset_D R) (interior_D R) j)
  rintro u ⟨hu, hD⟩
  exact ⟨(R.atlas.chart j).symm u, ⟨hD, (R.atlas.chart j).map_target hu⟩, (R.atlas.chart j).right_inv hu⟩

theorem isOpen_chart_notD (j : Fin R.atlas.n) :
    IsOpen ((R.atlas.chart j).target ∩
      (R.atlas.chart j).symm ⁻¹' {x | R.pt x ∉ ReciprocityTheory.AnForm.R.conePts R.D}) := by
  rw [isOpen_iff_mem_nhds]
  rintro u1 ⟨hu1, hB1⟩
  set x1 := (R.atlas.chart j).symm u1
  have hV : (R.atlas.chart j).target ∩ (R.atlas.chart j).symm ⁻¹' R.R.src (R.idx x1) ∈ 𝓝 u1 :=
    ((R.atlas.chart j).isOpen_inter_preimage_symm (R.R.isOpen_alt_bis _)).mem_nhds
      ⟨hu1, R.mem_src_idx x1⟩
  have hnot : ¬ ∀ f ∈ R.D, eval (R.liftAt x1 x1) f = 0 := fun h =>
    hB1 ⟨(GroundTheory.Heights₂.Heights.Inter.res_mem R x1 (R.mem_src_idx x1)).1, h⟩
  push Not at hnot
  obtain ⟨f, hfD, hf0⟩ := hnot
  have hcont : ContinuousAt (fun u => eval (R.liftAt x1 ((R.atlas.chart j).symm u)) f) u1 :=
    (MvPolynomial.continuous_eval _).continuousAt.comp
      (R.analyticAt_liftAt_pi x1 j ⟨hu1, R.mem_src_idx x1⟩).continuousAt
  filter_upwards [hV, hcont.eventually_ne hf0] with u hu hne
  refine ⟨hu.1, fun hB => ?_⟩
  exact hne (((pt_mem_D_iff R hu.2).mp hB).2 f hfD)

theorem not_flat {P : Ideal (MRing ι)} (hP : IsArithVar P (e + 1))
    (hW : W ∈ (P.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (hΨ : IsGoodProj P Ψ) (j : Fin R.atlas.n)
    {O : Set (Fin e → ℂ)} (hO : IsOpen O) (hOt : O ⊆ (R.atlas.chart j).target) (hne : O.Nonempty)
    (h0 : ∀ u ∈ O, Ψ (segre (R.pt ((R.atlas.chart j).symm u))) 0 ≠ 0)
    (han : AnalyticOnNhd ℂ (resProj R Ψ ∘ (R.atlas.chart j).symm) O)
    (hdet : ∀ u ∈ O, LinearMap.det (fderiv ℂ (resProj R Ψ ∘ (R.atlas.chart j).symm) u :
      (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) = 0) : False := by
  set O' := O ∩ ((R.atlas.chart j).target ∩
    (R.atlas.chart j).symm ⁻¹' {x | R.pt x ∉ ReciprocityTheory.AnForm.R.conePts R.D}) with hO'def
  have hO' : IsOpen O' := hO.inter (isOpen_chart_notD R j)
  have hne' : O'.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    obtain ⟨u, hu⟩ := hne
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hO u hu
    have hsub : Metric.ball u r ⊆ (R.atlas.chart j).target ∩
        (R.atlas.chart j).symm ⁻¹' {x | R.pt x ∈ ReciprocityTheory.AnForm.R.conePts R.D} := by
      intro v hv
      have hvO := hball hv
      refine ⟨hOt hvO, ?_⟩
      by_contra hB
      have : v ∈ O' := ⟨hvO, hOt hvO, hB⟩
      rw [h] at this
      exact this
    exact (Metric.measure_ball_pos volume u hr).ne' (measure_mono_null hsub (D_null R j))
  obtain ⟨y, hy⟩ := exists_infinite_fibre hO' hne' (han.mono inter_subset_left)
    (fun u hu => hdet u hu.1)
  refine (resFib_finite R hP hW Ψ hΨ y).not_infinite ((Set.Infinite.image
    ((R.atlas.chart j).symm.injOn.mono fun u hu => hOt hu.1.1) hy).mono ?_)
  rintro _ ⟨u, ⟨huO, hqu⟩, rfl⟩
  exact ⟨hqu, huO.2.2, h0 u huO.1⟩

end GroundTheory.Heights₂.Heights.HilbertSamuel.ResBridge
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PComponentResFibreFinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace ComponentResFibreFinite

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {W : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {e : ℕ}

def resW (R : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.Res ι W e)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (x : R.R.M) : ((k : K) → ι k) → ℂ :=
  (Ψ (segre (R.pt x)) 0)⁻¹ • segre (R.pt x)

theorem pt_mem_conePts (R : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.Res ι W e) (x : R.R.M) :
    R.pt x ∈ ReciprocityTheory.AnForm.R.conePts W :=
  R.R.lift_mem (R.idx x) x (R.mem_src_idx x)

omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] in

theorem mem_mcPts_of_conePts {P : Ideal (MRing ι)}
    (hW : P.map (MvPolynomial.map (Int.castRingHom ℂ)) ≤ W) {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ ReciprocityTheory.AnForm.R.conePts W) : z ∈ mcPts P :=
  ⟨hz.1, fun _ hf => hz.2 _ (hW (Ideal.mem_map_of_mem _ hf))⟩

theorem smul_segre_mem_fibre {P : Ideal (MRing ι)} (hK : Nonempty K) (hPh : IsMultiHomogIdeal P)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P)
    (h0 : Ψ (segre z) 0 ≠ 0) :
    (Ψ (segre z) 0)⁻¹ • segre z ∈
      fibre P Ψ (fun i : Fin e => Ψ (segre z) i.succ / Ψ (segre z) 0) := by
  obtain ⟨k0⟩ := hK
  let c : K → ℂ := Function.update (fun _ => (1 : ℂ)) k0 (Ψ (segre z) 0)⁻¹
  have hc : ∀ k, c k ≠ 0 := by
    intro k
    by_cases hk : k = k0
    · subst hk; simp [c, h0]
    · simp [c, Function.update_of_ne hk]
  have hpc : ∏ k, c k = (Ψ (segre z) 0)⁻¹ := by
    simp [c, Finset.prod_update_of_mem (Finset.mem_univ k0)]
  refine ⟨fun p => c p.1 * z p, mcPts_smul hPh c hc hz, ?_, ?_⟩
  · rw [segre_smul, hpc]
  · funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [h0]
    · simp only [map_smul, Pi.smul_apply, smul_eq_mul, Fin.cons_succ]
      rw [div_eq_inv_mul]

theorem resW_injOn (R : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.Res ι W e)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) :
    Set.InjOn (resW R Ψ)
      {x | R.pt x ∉ ReciprocityTheory.AnForm.R.conePts R.D ∧ Ψ (segre (R.pt x)) 0 ≠ 0} := by
  intro x hx x' hx' hw
  have hseg : segre (R.pt x) =
      (Ψ (segre (R.pt x)) 0 * (Ψ (segre (R.pt x')) 0)⁻¹) • segre (R.pt x') := by
    have := congrArg (fun v => Ψ (segre (R.pt x)) 0 • v) hw
    simp only [resW, smul_smul, mul_inv_cancel₀ hx.2, one_smul] at this
    exact this
  obtain ⟨c, hc, hcz⟩ := sameOrbit_of_segre (pt_mem_conePts R x').1 _ (by simp [hx.2, hx'.2]) hseg
  exact R.R.inj (R.idx x) (R.idx x') x (R.mem_src_idx x) x' (R.mem_src_idx x') hx.1 ⟨c, hc, hcz⟩

theorem proof : ComponentResFibreFinite.Statement := by
  intro K _ _ ι _ P e W R Ψ hP hW hΨ y
  have hle : P.map (MvPolynomial.map (Int.castRingHom ℂ)) ≤ W := hW.1.2
  have hbad : ∀ x ∉ resBad R Ψ,
      R.pt x ∉ ReciprocityTheory.AnForm.R.conePts R.D ∧ Ψ (segre (R.pt x)) 0 ≠ 0 :=
    fun x hx => ⟨fun h => hx (Or.inl (Or.inl h)), fun h => hx (Or.inl (Or.inr h))⟩
  refine Set.Finite.of_finite_image (f := resW R Ψ)
    ((fibreFinite K ι P e Ψ hP hΨ y).subset ?_) ((resW_injOn R Ψ).mono fun x hx => hbad x hx.2)
  rintro _ ⟨x, hx, rfl⟩
  have := smul_segre_mem_fibre hP.1 hP.2.1.2.1 Ψ
    (mem_mcPts_of_conePts hle (pt_mem_conePts R x)) (hbad x hx.2).2
  have hy : resProj R Ψ x = y := hx.1
  rw [← hy]
  exact this

end ComponentResFibreFinite

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PComponentResInt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem ComponentResInt.proof (h₁ : ComponentResBadNull.Statement) (h₂ : ComponentResFibreFinite.Statement)
    (h₃ : ComponentResFibreSum.Statement) : ComponentResInt.Statement := by
  intro K _ _ ι _ P e L W hP hL hW hR
  have hex : ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj P Ψ :=
    goodProjExists K ι P e hP
  unfold ptsIntegral GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.zInt
  rw [dif_pos hex, dif_pos hR]
  set Ψ := hex.choose with hΨdef
  have hΨ : IsGoodProj P Ψ := hex.choose_spec
  set R := hR.some with hRdef
  unfold GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.Res.int
  have hpot : ∀ j, ReciprocityTheory.AnForm.M.IsPotential R.atlas
      (R.pot (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.logH (L j))) := fun j =>
    R.isPotential_pot (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.isSmoothPot_logH
      (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.isSmoothMetric_of_isSmoothHerm W (L j) (hL j)))
  have hgood : ∀ x ∉ resBad R Ψ, ∀ j, x ∈ (R.atlas.chart j).source →
      AnalyticAt ℂ (resProj R Ψ ∘ (R.atlas.chart j).symm) (R.atlas.chart j x) ∧
        LinearMap.det (fderiv ℂ (resProj R Ψ ∘ (R.atlas.chart j).symm) (R.atlas.chart j x) :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0 := by
    intro x hx j hj
    by_contra h
    exact hx (Or.inr ⟨j, hj, h⟩)
  rw [pushForward_null R.atlas _ hpot (resProj R Ψ) (resBad R Ψ) (h₁ K ι P e W R Ψ hP hW hΨ) hgood
    (h₂ K ι P e W R Ψ hP hW hΨ) _ (ReciprocityTheory.AnForm.M.mIntegrableCont R.atlas _ hpot _ continuous_const)]
  refine integral_congr_ae ?_
  filter_upwards [h₃ K ι P e L W R Ψ hP hL hW hΨ] with y hy
  rw [hy]
  exact finsum_mem_congr rfl fun x _ => (one_mul _).symm

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFibreNormGoodPrimeIntegral
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

theorem FibreNormGoodPrimeIntegral.proof (hN : PullConeNullModP.Statement) (hD : PullConeDegreeInt.Statement)
    (hI : PullSectionIntegralInt.Statement) (hP : DehomNormPIntegral.Statement) :
    FibreNormGoodPrimeIntegral.Statement := by
  intro K _ ι _ Ω _ _ y D e L q hA hB he hL hz p hp hgood τ s hs j c hc μ
  classical
  obtain ⟨N, M, hpM, hrel⟩ := hN K ι Ω y D L hz p hp hgood
  have hy : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := by
    obtain ⟨_, ⟨_, _, hrv⟩, _, _⟩ := hA
    obtain ⟨c', hc'⟩ := CoordArithOfFnField.nonzero_of_relevant y hrv
    exact fun k => ⟨c' k, hc' k⟩
  have hM : (M : Ω) ≠ 0 := Nat.cast_ne_zero.mpr (by rintro rfl; exact hpM (dvd_zero p))
  obtain ⟨hj, hfin, -, hch, hcp⟩ := hc
  have := hfin
  have hint := hI K ι Ω y D e L q N M hy he hL hM (hD K ι Ω y D e L N M hy hL hrel) τ s hs j hj
  have hgen := PullFormsGeneric.proof
    (PullRatiosAlgebraic.proof PullConeNull.proof PullConeDegree.proof PullGradedAlgebraic.proof)
    K ι Ω y D e L hA hB he hL hz
  exact hP Ω D (fun i => aeval y (L i)) (pullField y L) rfl hgen p hp M hpM j (q * τ) _ hint c
    (hch _ le_rfl) hcp μ

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNefPlusAmpleDegree
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1

noncomputable section

namespace NefPlusAmpleDegree

theorem genDeg_one_pos (hA : GenDegAmple.Statement) {K : Type} [Fintype K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {W : Ideal (MRing ι)} {d : ℕ} (hW : IsArithVar W (d + 1)) :
    0 < genDeg W d 1 := by
  have : W.IsPrime := hW.2.1.1
  have hEq := CurvePointsFinite.mCoordIdeal_genericPt W hW.2.1.2.1
  have hV : IsArithVar (mCoordIdeal (CurvePointsFinite.genericPt W)) (d + 1) := by rw [hEq]; exact hW
  have h := hA K ι _ (CurvePointsFinite.genericPt W) d 1 hV fun _ => le_rfl
  rwa [hEq] at h

open Classical in

theorem nefOnF_of_nefOnGenericDeg {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} {b : K → ℤ} (hb : NefOnGenericDeg P b) :
    KH.NefOnF (fun V _ L => NumbersDVR.intNum ℚ V L) (P.map (MvPolynomial.map (Int.castRingHom ℚ))) b := by
  intro W hW hle
  obtain ⟨hWar, hWmap⟩ := NefAmpleGeneric.isArithVar_comap_of_isProjVarF hW
  have hPW : P ≤ W.comap (MvPolynomial.map (Int.castRingHom ℚ)) := Ideal.map_le_iff_le_comap.mp hle
  have h := hb _ hWar hPW
  rw [genDeg, hWmap] at h
  have hL : (fun _ : Fin 1 => b) = ![b] := by
    funext j
    fin_cases j
    rfl
  rw [hL] at h
  exact h

end NefPlusAmpleDegree

theorem NefPlusAmpleDegree.proof (hK : KH.KleimanNefFStatement) (hA : GenDegAmple.Statement) :
    NefPlusAmpleDegree.Statement := by
  classical
  intro K _ ι _ P D a hP hnef q
  have : Nonempty K := hP.1
  set Q := P.map (MvPolynomial.map (Int.castRingHom ℚ)) with hQ
  obtain ⟨hprime, hdimq⟩ := ShiftDegreePolynomial.genericFibre hP
  have hd : FieldNumbers.relDim Q = D := by
    rw [FieldNumbers.relDim_of_ringKrullDim_eq _ _ hdimq]
    simp only [Nat.cast_add, add_sub_cancel_right]
    rfl
  let f : (Fin D → K → ℤ) → ℤ := fun bs => NumbersDVR.intNum ℚ Q bs
  have hadd : ∀ (bs : Fin D → K → ℤ) (j : Fin D) (x y : K → ℤ),
      f (Function.update bs j (x + y)) = f (Function.update bs j x) + f (Function.update bs j y) :=
    fun bs j x y => FieldNumbers.IntNumAdd.full ℚ K ι Q hprime.multiHomog hprime.relevant D hd bs j x y
  let I : IFamily ℚ ι := fun V _ L => NumbersDVR.intNum ℚ V L
  have hI : IsFieldIntersection I := NumbersDVR.IntNumIsFieldIntersection.full ℚ K ι
  have hPV : IsProjVarF Q D := isProjVarF_map_of_isArithVar hP
  have hnefA : KH.NefOnF I Q a := NefPlusAmpleDegree.nefOnF_of_nefOnGenericDeg hnef
  have hnefH : KH.NefOnF I Q 1 := NefPlusAmpleDegree.nefOnF_of_nefOnGenericDeg fun W hW _ =>
    (NefPlusAmpleDegree.genDeg_one_pos hA hW).le
  have hterm : ∀ s : Finset (Fin D), 0 ≤ f (s.piecewise (fun _ => a) (fun _ => 1)) := by
    intro s
    refine hK ℚ K ι I Q D _ hI hPV fun i => ?_
    by_cases hi : i ∈ s
    · simpa [Finset.piecewise, hi] using hnefA
    · simpa [Finset.piecewise, hi] using hnefH
  have hg : genDeg P D ((q : ℤ) • a + 1) = f (fun _ => (q : ℤ) • a + 1) := rfl
  rw [hg, ShiftDegreePolynomial.expand f hadd (q : ℤ) a 1]
  refine Finset.sum_pos' (fun s _ => mul_nonneg (pow_nonneg (Int.natCast_nonneg q) _) (hterm s))
    ⟨∅, Finset.mem_univ _, ?_⟩
  rw [Finset.card_empty, pow_zero, one_mul, Finset.piecewise_empty]
  exact NefPlusAmpleDegree.genDeg_one_pos hA hP

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

