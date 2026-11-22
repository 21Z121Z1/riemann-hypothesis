import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0108
import GroundTheory.HeightsAndTheta.Heights.Intersections.UnitChartOperator
import GroundTheory.HeightsAndTheta.Heights.Intersections.FourierIntegralBound
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0003
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0026
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0022
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0104
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0044
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0012
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0027
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0024
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0056
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0107
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0060
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0085
import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ComponentResBadNullLift
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel.ResBridge

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Topology Filter

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {W : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {e : ℕ} (R : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.Res ι W e)

omit [Fintype K] in

theorem homogD : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal R.D :=
  (GroundTheory.Heights₂.Heights.Bridge.isMultiHomogIdeal_iff R.D).mp R.homog

theorem mem_D_of_sameOrbit {z z' : (Σ k, ι k) → ℂ} (h : ReciprocityTheory.AnForm.R.SameOrbit z z')
    (hz' : z' ∈ ReciprocityTheory.AnForm.R.conePts R.D) : z ∈ ReciprocityTheory.AnForm.R.conePts R.D := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => ?_, ReciprocityTheory.AnForm.R.eval_eq_zero_of_smul (homogD R) c z' hz'.2⟩
  obtain ⟨i, hi⟩ := hz'.1 k
  exact ⟨i, mul_ne_zero (hc k) hi⟩

omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] in

theorem sameOrbit_symm {z z' : (Σ k, ι k) → ℂ} (h : ReciprocityTheory.AnForm.R.SameOrbit z z') :
    ReciprocityTheory.AnForm.R.SameOrbit z' z := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), ?_⟩
  funext q
  rw [← mul_assoc, inv_mul_cancel₀ (hc q.1), one_mul]

theorem pt_mem_D_iff {x y : R.R.M} (hy : y ∈ R.R.src (R.idx x)) :
    R.pt y ∈ ReciprocityTheory.AnForm.R.conePts R.D ↔ R.liftAt x y ∈ ReciprocityTheory.AnForm.R.conePts R.D := by
  have h := GroundTheory.Heights₂.Heights.Inter.res_compat R x y hy (R.mem_src_idx y)
  exact ⟨fun hp => mem_D_of_sameOrbit R h hp, fun hl => mem_D_of_sameOrbit R (sameOrbit_symm h) hl⟩

theorem psi_pt_eq {x y : R.R.M} (hy : y ∈ R.R.src (R.idx x))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) :
    ∃ μ : ℂ, μ ≠ 0 ∧ Ψ (segre (R.pt y)) = μ • Ψ (segre (R.liftAt x y)) := by
  obtain ⟨c, hc, hyc⟩ := GroundTheory.Heights₂.Heights.Inter.res_compat R y x (R.mem_src_idx y) hy
  refine ⟨∏ k, c k, Finset.prod_ne_zero_iff.mpr fun k _ => hc k, ?_⟩
  rw [show R.pt y = R.liftAt y y from rfl, hyc, segre_smul, map_smul]

theorem resProj_eq_local (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) {x y : R.R.M}
    (hy : y ∈ R.R.src (R.idx x)) :
    resProj R Ψ y = fun i => Ψ (segre (R.liftAt x y)) i.succ / Ψ (segre (R.liftAt x y)) 0 := by
  obtain ⟨μ, hμ, hμeq⟩ := psi_pt_eq R hy Ψ
  funext i
  simp only [resProj, hμeq, Pi.smul_apply, smul_eq_mul]
  exact mul_div_mul_left _ _ hμ

theorem analyticAt_segre_liftAt (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (x : R.R.M)
    (j : Fin R.atlas.n) {u : Fin e → ℂ}
    (hu : u ∈ (R.atlas.chart j).target ∩ (R.atlas.chart j).symm ⁻¹' R.R.src (R.idx x)) :
    AnalyticAt ℂ (fun v => Ψ (segre (R.liftAt x ((R.atlas.chart j).symm v)))) u := by
  have hl := R.analyticAt_liftAt_pi x j hu
  have hs : AnalyticAt ℂ (fun v => segre (R.liftAt x ((R.atlas.chart j).symm v))) u := by
    refine analyticAt_pi_iff.mpr fun i => ?_
    simp only [segre]
    exact Finset.analyticAt_fun_prod _ fun k _ => analyticAt_pi_iff.mp hl _
  exact (LinearMap.toContinuousLinearMap Ψ).analyticAt _ |>.comp hs

theorem analyticAt_resProj (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (x : R.R.M)
    (j : Fin R.atlas.n) (hj : x ∈ (R.atlas.chart j).source) (h0 : Ψ (segre (R.pt x)) 0 ≠ 0) :
    AnalyticAt ℂ (resProj R Ψ ∘ (R.atlas.chart j).symm) (R.atlas.chart j x) := by
  set u := R.atlas.chart j x
  have hsu : (R.atlas.chart j).symm u = x := (R.atlas.chart j).left_inv hj
  have hu : u ∈ (R.atlas.chart j).target ∩ (R.atlas.chart j).symm ⁻¹' R.R.src (R.idx x) :=
    ⟨(R.atlas.chart j).map_source hj, by rw [Set.mem_preimage, hsu]; exact R.mem_src_idx x⟩
  have hH := analyticAt_segre_liftAt R Ψ x j hu
  have hH0 : AnalyticAt ℂ (fun v => Ψ (segre (R.liftAt x ((R.atlas.chart j).symm v))) 0) u :=
    analyticAt_pi_iff.mp hH 0
  have hne : Ψ (segre (R.liftAt x ((R.atlas.chart j).symm u))) 0 ≠ 0 := by rw [hsu]; exact h0
  have hF : AnalyticAt ℂ (fun v => fun i : Fin e =>
      Ψ (segre (R.liftAt x ((R.atlas.chart j).symm v))) i.succ /
        Ψ (segre (R.liftAt x ((R.atlas.chart j).symm v))) 0) u :=
    analyticAt_pi_iff.mpr fun i => (analyticAt_pi_iff.mp hH i.succ).div hH0 hne
  refine hF.congr ?_
  filter_upwards [((R.atlas.chart j).isOpen_inter_preimage_symm (R.R.isOpen_alt_bis (R.idx x))).mem_nhds hu,
    hH0.continuousAt.eventually_ne hne] with v hv hv0
  exact (resProj_eq_local R Ψ hv.2).symm

theorem det_resProj_chart (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) {x : R.R.M}
    {j k : Fin R.atlas.n} (hj : x ∈ (R.atlas.chart j).source) (hk : x ∈ (R.atlas.chart k).source)
    (h0 : Ψ (segre (R.pt x)) 0 ≠ 0) :
    LinearMap.det (fderiv ℂ (resProj R Ψ ∘ (R.atlas.chart j).symm) (R.atlas.chart j x) :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) =
      LinearMap.det (fderiv ℂ (resProj R Ψ ∘ (R.atlas.chart k).symm) (R.atlas.chart k x) :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) *
      LinearMap.det (fderiv ℂ (R.atlas.chart k ∘ (R.atlas.chart j).symm) (R.atlas.chart j x) :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) := by
  set u := R.atlas.chart j x
  have hsu : (R.atlas.chart j).symm u = x := (R.atlas.chart j).left_inv hj
  set T := R.atlas.chart k ∘ (R.atlas.chart j).symm with hTdef
  have huk : u ∈ (R.atlas.chart j).target ∩ (R.atlas.chart j).symm ⁻¹' (R.atlas.chart k).source :=
    ⟨(R.atlas.chart j).map_source hj, by rw [Set.mem_preimage, hsu]; exact hk⟩
  have hT : AnalyticAt ℂ T u := R.atlas.holo j k u huk
  have hTu : T u = R.atlas.chart k x := by simp only [hTdef, Function.comp_apply, hsu]
  have hQk := analyticAt_resProj R Ψ x k hk h0
  have heq : resProj R Ψ ∘ (R.atlas.chart j).symm =ᶠ[𝓝 u] (resProj R Ψ ∘ (R.atlas.chart k).symm) ∘ T := by
    filter_upwards [((R.atlas.chart j).isOpen_inter_preimage_symm (R.atlas.chart k).open_source).mem_nhds
      huk] with v hv
    simp only [hTdef, Function.comp_apply, (R.atlas.chart k).left_inv hv.2]
  rw [heq.fderiv_eq, fderiv_comp u (by rw [hTu]; exact hQk.differentiableAt) hT.differentiableAt, hTu]
  exact LinearMap.det_comp _ _

omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] in

theorem mcPts_of_conePts {P : Ideal (MRing ι)}
    (hW : W ∈ (P.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes) {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ ReciprocityTheory.AnForm.R.conePts W) : z ∈ mcPts P :=
  ⟨hz.1, fun _ hf => hz.2 _ (hW.1.2 (Ideal.mem_map_of_mem _ hf))⟩

theorem pt_mem_mcPts {P : Ideal (MRing ι)}
    (hW : W ∈ (P.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes) (x : R.R.M) :
    R.pt x ∈ mcPts P :=
  mcPts_of_conePts hW (GroundTheory.Heights₂.Heights.Inter.res_mem R x (R.mem_src_idx x))

def resW (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (x : R.R.M) : ((k : K) → ι k) → ℂ :=
  (Ψ (segre (R.pt x)) 0)⁻¹ • segre (R.pt x)

theorem resW_mem_fibre {P : Ideal (MRing ι)}
    (hW : W ∈ (P.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes) (hK : Nonempty K)
    (hPh : IsMultiHomogIdeal P) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) {x : R.R.M}
    (h0 : Ψ (segre (R.pt x)) 0 ≠ 0) : resW R Ψ x ∈ fibre P Ψ (resProj R Ψ x) := by
  obtain ⟨k0⟩ := hK
  let c : K → ℂ := Function.update (fun _ => (1 : ℂ)) k0 (Ψ (segre (R.pt x)) 0)⁻¹
  have hc : ∀ k, c k ≠ 0 := by
    intro k
    by_cases hk : k = k0
    · subst hk; simp [c, h0]
    · simp [c, Function.update_of_ne hk]
  have hpc : ∏ k, c k = (Ψ (segre (R.pt x)) 0)⁻¹ := by
    simp [c, Finset.prod_update_of_mem (Finset.mem_univ k0)]
  refine ⟨fun p => c p.1 * R.pt x p, mcPts_smul hPh c hc (pt_mem_mcPts R hW x), ?_, ?_⟩
  · rw [segre_smul, hpc]; rfl
  · funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [resW, h0]
    · simp only [resW, map_smul, Pi.smul_apply, smul_eq_mul, Fin.cons_succ, resProj]
      rw [div_eq_inv_mul]

theorem resW_injOn (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) :
    Set.InjOn (resW R Ψ) {x | R.pt x ∉ ReciprocityTheory.AnForm.R.conePts R.D ∧ Ψ (segre (R.pt x)) 0 ≠ 0} := by
  intro x hx x' hx' hw
  refine R.R.inj (R.idx x) (R.idx x') x (R.mem_src_idx x) x' (R.mem_src_idx x') hx.1 ?_
  have hseg : segre (R.pt x) = (Ψ (segre (R.pt x)) 0 * (Ψ (segre (R.pt x')) 0)⁻¹) • segre (R.pt x') := by
    have := congrArg (fun v => Ψ (segre (R.pt x)) 0 • v) hw
    simp only [resW, smul_smul, mul_inv_cancel₀ hx.2, one_smul] at this
    exact this
  obtain ⟨c, hc, h⟩ := sameOrbit_of_segre
    (GroundTheory.Heights₂.Heights.Inter.res_mem R x' (R.mem_src_idx x')).1
    (Ψ (segre (R.pt x)) 0 * (Ψ (segre (R.pt x')) 0)⁻¹) (by simp [hx.2, hx'.2]) hseg
  exact ⟨c, hc, h⟩

theorem resFib_finite {P : Ideal (MRing ι)} (hP : IsArithVar P (e + 1))
    (hW : W ∈ (P.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (hΨ : IsGoodProj P Ψ) (y : Fin e → ℂ) :
    (resProj R Ψ ⁻¹' {y} ∩
      {x | R.pt x ∉ ReciprocityTheory.AnForm.R.conePts R.D ∧ Ψ (segre (R.pt x)) 0 ≠ 0}).Finite := by
  refine Set.Finite.of_finite_image (f := resW R Ψ) ((fibreFinite K ι P e Ψ hP hΨ y).subset ?_)
    ((resW_injOn R Ψ).mono fun x hx => hx.2)
  rintro _ ⟨x, hx, rfl⟩
  have := resW_mem_fibre R hW hP.1 hP.2.1.2.1 Ψ hx.2.2
  rwa [show resProj R Ψ x = y from hx.1] at this

end GroundTheory.Heights₂.Heights.HilbertSamuel.ResBridge
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNefAmpleGeneric
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1

noncomputable section

namespace NefAmpleGeneric

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem isArithVar_comap_of_isProjVarF {K : Type} [Fintype K] [Nonempty K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {W : Ideal (MRingOver ℚ ι)} {d : ℕ} (hW : IsProjVarF W d) :
    IsArithVar (W.comap (MvPolynomial.map (Int.castRingHom ℚ))) (d + 1) ∧
      (W.comap (MvPolynomial.map (Int.castRingHom ℚ))).map (MvPolynomial.map (Int.castRingHom ℚ)) = W := by
  classical
  obtain ⟨⟨hprime, hhom, hrel⟩, hdim⟩ := hW
  set φ : MRing ι →+* MRingOver ℚ ι := MvPolynomial.map (Int.castRingHom ℚ) with hφdef
  set P := W.comap φ with hPdef
  have := hprime
  have hPp : P.IsPrime := Ideal.comap_isPrime φ W
  let S : Submonoid (MRing ι) := (nonZeroDivisors ℤ).map (C (σ := Σ k, ι k))
  have : IsLocalization S (MRingOver ℚ ι) := MvPolynomial.isLocalization (nonZeroDivisors ℤ) ℚ
  have hφ : algebraMap (MRing ι) (MRingOver ℚ ι) = φ := by
    show MvPolynomial.map (algebraMap ℤ ℚ) = _
    rw [RingHom.ext_int (algebraMap ℤ ℚ) (Int.castRingHom ℚ)]
  have hmap : P.map φ = W := by
    have h := IsLocalization.map_under S (MRingOver ℚ ι) W
    rwa [hφ] at h
  have hch : ∀ m : ℤ, (C m : MRing ι) ∈ P → m = 0 := by
    intro m hm
    by_contra h0
    have hu : IsUnit (φ (C m)) := by
      rw [hφdef, map_C]
      exact (isUnit_iff_ne_zero.mpr (by simpa using h0 : ((Int.castRingHom ℚ) m) ≠ 0)).map C
    exact hprime.ne_top (Ideal.eq_top_of_isUnit_mem _ hm hu)
  have hWN : NumbersDVR.IsMultiProjPrime (K := K) W :=
    (GroundTheory.Heights₂.Heights.Bridge.isMultiProjPrime_iff W).mpr ⟨hprime, hhom, hrel⟩
  have hPN : NumbersDVR.IsMultiProjPrime (K := K) P := by
    refine ⟨hPp, fun f hf b => ?_, fun k => ?_⟩
    · show φ _ ∈ W
      rw [hφdef, ← NumbersDVR.weightedHomogeneousComponent_map]
      exact hWN.multiHomog _ hf b
    · obtain ⟨i, hi⟩ := hrel k
      exact ⟨i, fun h => hi (by simpa [hPdef, hφdef] using h)⟩
  obtain ⟨-, hhomP, hrelP⟩ := (GroundTheory.Heights₂.Heights.Bridge.isMultiProjPrime_iff P).mp hPN
  obtain ⟨-, -, hd⟩ := ReciprocityTheory.AnForm.R.extQ_spec P hch
  refine ⟨⟨‹Nonempty K›, ⟨hPp, hhomP, hrelP⟩, ?_, ?_⟩, hmap⟩
  · ext m
    simp only [Ideal.mem_comap, Ideal.mem_bot]
    exact ⟨hch m, fun h => by rw [h, map_zero]; exact P.zero_mem⟩
  · have hext : ReciprocityTheory.AnForm.R.extQ P = W := hmap
    rw [← hd, hext, hdim, show d + 1 + Fintype.card K = (d + Fintype.card K) + 1 by omega, Nat.cast_succ]

end NefAmpleGeneric

theorem NefAmpleGeneric.proof (hKA : KH.KAmpStatement)
    (hDG : GroundTheory.Heights₂.Heights.Inter.DegreeGeneric.Statement) : NefAmpleGeneric.Statement := by
  intro K _ _ ι _ _ Ω _ _ y D M P0 b a hV hP0 hs hb ha
  classical
  have : Nonempty K := hV.1
  let I : IFamily ℚ ι := fun V _ L => NumbersDVR.intNum ℚ V L
  have hI : IsFieldIntersection I := NumbersDVR.IntNumIsFieldIntersection.full ℚ K ι
  have hnef : KH.NefOnF I (KH.genIdeal y) M.a := by
    intro W hW hle
    obtain ⟨hWar, hWmap⟩ := NefAmpleGeneric.isArithVar_comap_of_isProjVarF hW
    have hPW : mCoordIdeal y ≤ W.comap (MvPolynomial.map (Int.castRingHom ℚ)) :=
      Ideal.map_le_iff_le_comap.mp hle
    have h0 : 0 ≤ geomDeg (W.comap (MvPolynomial.map (Int.castRingHom ℚ))) M 1 :=
      NefOnGenericOfSemipos.proof K ι _ P0 M hP0 hs _ hWar hPW
    have hdeg := hDG K ι (W.comap (MvPolynomial.map (Int.castRingHom ℚ))) 1 ![M] hWar (fun j => by fin_cases j; exact hs.1)
    rw [hWmap] at hdeg
    have hpot : pot ![M] = fun (_ : Fin 1) z => Real.log (M.h z) := by
      funext j z
      fin_cases j
      rfl
    have hL : (fun j => (![M] j).a) = ![M.a] := by
      funext j
      fin_cases j
      rfl
    rw [hpot, hL] at hdeg
    have h1 : (0 : ℝ) ≤ (NumbersDVR.intNum ℚ W ![M.a] : ℝ) := by
      rw [← hdeg]
      exact h0
    show 0 ≤ NumbersDVR.intNum ℚ W ![M.a]
    exact_mod_cast h1
  have h := hKA ℚ K ι I (KH.genIdeal y) D M.a b a hI (isProjVarF_map_of_isArithVar hV) hnef hb ha
  rwa [← natCast_zsmul] at h

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPerturbMonomial
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry SectionBoundedMul SmallGenTwist

noncomputable section

namespace PerturbedMonomialBound

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem chartMono_exponent (c : ∀ k, ι k) (d : K → ℕ) :
    ∃ μ : (Σ k, ι k) →₀ ℕ, (∀ k, ∑ i, μ ⟨k, i⟩ = d k) ∧
      ∀ z : (Σ k, ι k) → ℂ, ∏ p, z p ^ μ p = ∏ k, z ⟨k, c k⟩ ^ d k := by
  classical
  refine ⟨∑ k, Finsupp.single (⟨k, c k⟩ : Σ k, ι k) (d k), fun k => ?_, fun z => ?_⟩
  · simp only [Finsupp.finsetSum_apply]
    rw [Finset.sum_comm]
    simp only [sum_single_apply, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · have h : chartMono c d = monomial (∑ k, Finsupp.single (⟨k, c k⟩ : Σ k, ι k) (d k)) (1 : ℤ) := by
      rw [chartMono, monomial_sum_one]
      exact Finset.prod_congr rfl fun k _ => X_pow_eq_monomial
    have e1 := eval_chartMono z c d
    rw [h, map_monomial, eval_monomial, Finsupp.prod_fintype _ _ (fun i => by simp)] at e1
    simpa using e1

theorem smallGen_of_monomialsBounded (y : (Σ k, ι k) → Ω) (A : HermLine ι) (a : K → ℕ)
    (ha : A.a = fun k => (a k : ℤ)) (hB : MonomialsBounded (mCoordIdeal y) A a) : SmallGen y A := by
  classical
  set e := Fintype.equivFin (∀ k, ι k) with he_def
  refine ⟨Fintype.card (∀ k, ι k), fun j => aeval y (chartMono (e.symm j) a), fun j => ?_, ?_, fun j => ?_⟩
  · intro c hc
    beta_reduce
    rw [aeval_chartMono, ← Finset.prod_mul_distrib]
    refine prod_mem fun k _ => ?_
    have hmem : y ⟨k, (e.symm j) k⟩ / y ⟨k, c k⟩ ∈ chartRingZ y c :=
      Algebra.subset_adjoin ⟨⟨k, (e.symm j) k⟩, rfl⟩
    convert pow_mem hmem (a k) using 1
    simp [ha, div_eq_mul_inv, zpow_neg, zpow_natCast, mul_pow, inv_pow]
  · intro c hc
    refine ⟨fun j => if e.symm j = c then 1 else 0, fun j => by beta_reduce; split_ifs <;> simp, ?_⟩
    rw [Fintype.sum_equiv e.symm _ (fun i => (if i = c then (1 : Ω) else 0) *
      (aeval y (chartMono i a) * ∏ k, y ⟨k, c k⟩ ^ (-A.a k))) (fun _ => rfl)]
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [aeval_chartMono, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun k _ => by
      simp [ha, zpow_neg, zpow_natCast, mul_inv_cancel₀ (pow_ne_zero _ (hc k))]
  · intro dg dh g h z hg hh hdeg he hz
    have hd : dg = a + dh := funext fun k => by
      have := hdeg k
      simp only [ha, Nat.cast_one, one_mul] at this
      simp only [Pi.add_apply]
      omega
    have hF : IsMultiHomog (g - chartMono (e.symm j) a * h) dg :=
      isMultiHomog_sub hg (by rw [hd]; exact isMultiHomog_mul (isMultiHomog_chartMono _ a) hh)
    have h0 : aeval y (g - chartMono (e.symm j) a * h) = 0 := by
      rw [map_sub, map_mul, he, sub_self]
    have hz0 := hz.2 _ (mem_mCoordIdeal_of_aeval_eq_zero y hF h0)
    simp only [map_sub, map_mul, sub_eq_zero] at hz0
    rw [hz0, norm_mul, eval_chartMono, pow_one, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    obtain ⟨μ, hμ, hzμ⟩ := chartMono_exponent (e.symm j) a
    rw [← hzμ z]
    exact hB z hz μ hμ

end PerturbedMonomialBound

open PerturbedMonomialBound in

theorem PerturbMonomial.proof (hDeg : GenDegAmple.Statement) : PerturbMonomial.Statement := by
  intro K _ ι _ Ω _ y D a A P0 q _ hV _ ha hP0 hsemi hmono _
  have hBa : (HermLine.zcomb A (fsH ι) q 1).a = fun k => (q : ℤ) * a k + 1 := by
    funext k
    simp [HermLine.zcomb, ha, fsH_a]
  refine ⟨hP0, ?_, ?_, ?_⟩
  · exact PerturbSemipos.proof K ι P0 (mCoordIdeal y) A q 1 hsemi (by positivity) zero_le_one
  · rw [hBa]
    refine hDeg K ι Ω y D _ hV fun k => ?_
    have : (0 : ℤ) ≤ (q : ℤ) * a k := by positivity
    omega
  · have h := smallGen_zcomb y A (smallGen_of_monomialsBounded y A a ha hmono) q 1
    rw [Nat.cast_one] at h
    exact h

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PResolutionDegree
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M Filter Topology
open scoped ContDiff

noncomputable section

namespace ResolutionDegree

theorem hessC_congr {n : ℕ} {φ ψ : (Fin n → ℂ) → ℝ} {z : Fin n → ℂ} (h : φ =ᶠ[𝓝 z] ψ) :
    ReciprocityTheory.AnForm.hessC φ z = ReciprocityTheory.AnForm.hessC ψ z := by
  unfold ReciprocityTheory.AnForm.hessC
  rw [(h.fderiv (𝕜 := ℝ)).fderiv_eq]

theorem maDens_congr {n : ℕ} {φ ψ : Fin n → (Fin n → ℂ) → ℝ} {z : Fin n → ℂ} (h : ∀ i, φ i =ᶠ[𝓝 z] ψ i) :
    ReciprocityTheory.AnForm.maDens φ z = ReciprocityTheory.AnForm.maDens ψ z := by
  have hH : (fun k => ReciprocityTheory.AnForm.hessC (φ k) z) = fun k => ReciprocityTheory.AnForm.hessC (ψ k) z :=
    funext fun k => hessC_congr (h k)
  unfold ReciprocityTheory.AnForm.maDens
  rw [hH]

theorem mInt_congr_of_locDens {e : ℕ} {X : Type*} [TopologicalSpace X] (A : FinHolAtlas e X)
    {Φ Ψ : Fin e → LocPot X} (h : ∀ j, ∀ y ∈ (A.chart j).target, locDens A Φ j y = locDens A Ψ j y)
    (g : X → ℝ) : mInt A Φ g = mInt A Ψ g := by
  unfold mInt
  split_ifs with hP
  · unfold integralWith
    refine Finset.sum_congr rfl fun j _ => ?_
    refine MeasureTheory.setIntegral_congr_fun (A.chart j).open_target.measurableSet fun y hy => ?_
    simp only [h j y hy]
  · rfl

variable {D : ℕ} {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ]

theorem smooth_logRatio_resPt (d : HSMDatum D Ω κ) {m₀ m₁ : ConeMetric ℂ (Ix κ)}
    (h₀ : IsSmoothMetric m₀) (h₁ : IsSmoothMetric m₁) :
    d.R.A.Smooth (fun y => logRatio m₀ m₁ (resPt d y)) := fun j => by
  refine contDiffOn_of_locally_contDiffOn fun y hy => ?_
  refine ⟨(d.R.A.chart j).target ∩ (d.R.A.chart j).symm ⁻¹' d.R.U ((d.R.A.chart j).symm y),
    (d.R.A.chart j).isOpen_inter_preimage_symm (d.R.isOpen_U _), ⟨hy.1, d.R.mem_U _⟩, ?_⟩
  have hsm : ContDiffOn ℝ ∞
      (fun y' => logRatio m₀ m₁ (d.R.lift ((d.R.A.chart j).symm y) ((d.R.A.chart j).symm y')))
      ((d.R.A.chart j).target ∩ (d.R.A.chart j).symm ⁻¹' d.R.U ((d.R.A.chart j).symm y)) :=
    (gbamix_smooth_logRatio h₀ h₁).comp (resLift_contDiffOn d _ j)
      fun y' hy' => gaamix_ne_zero_of_mcPts (d.R.mem _ _ hy'.2)
  refine (hsm.mono Set.inter_subset_right).congr fun y' hy' => ?_
  obtain ⟨c, hc, hcy⟩ := d.R.compat ((d.R.A.chart j).symm y') ((d.R.A.chart j).symm y)
    ((d.R.A.chart j).symm y') ⟨d.R.mem_U _, hy'.2.2⟩
  change logRatio m₀ m₁ (d.R.lift ((d.R.A.chart j).symm y') ((d.R.A.chart j).symm y')) = _
  rw [hcy, gbamix_logRatio_deg c _ hc]

theorem mInt_resPot_eq (d : HSMDatum D Ω κ) {m₀ m₁ : ConeMetric ℂ (Ix κ)} (g : d.R.X → ℝ) :
    mInt d.R.A (fun _ => resPot d m₁) g =
      mInt d.R.A (fun _ => resPot d m₀ + LocPot.ofFun (fun y => logRatio m₀ m₁ (resPt d y))) g := by
  refine mInt_congr_of_locDens _ (fun j y hy => ?_) g
  unfold locDens
  refine maDens_congr fun _ => ?_
  have hmem : (d.R.A.chart j).target ∩ (d.R.A.chart j).symm ⁻¹' d.R.U ((d.R.A.chart j).symm y) ∈ 𝓝 y :=
    ((d.R.A.chart j).isOpen_inter_preimage_symm (d.R.isOpen_U _)).mem_nhds ⟨hy, d.R.mem_U _⟩
  filter_upwards [hmem] with y' hy'
  obtain ⟨c, hc, hcy⟩ := d.R.compat ((d.R.A.chart j).symm y') ((d.R.A.chart j).symm y)
    ((d.R.A.chart j).symm y') ⟨d.R.mem_U _, hy'.2⟩
  have hz := gaamix_ne_zero_of_mcPts (d.R.mem ((d.R.A.chart j).symm y) _ hy'.2)
  have h₀ := m₀.pos _ hz
  have h₁ := m₁.pos _ hz
  change Real.log (m₁.ρ (d.R.lift ((d.R.A.chart j).symm y) ((d.R.A.chart j).symm y'))) =
    Real.log (m₀.ρ (d.R.lift ((d.R.A.chart j).symm y) ((d.R.A.chart j).symm y'))) +
      logRatio m₀ m₁ (d.R.lift ((d.R.A.chart j).symm y') ((d.R.A.chart j).symm y'))
  rw [hcy, gbamix_logRatio_deg c _ hc, logRatio, Real.log_div h₁.ne' h₀.ne']
  ring

theorem mass_eq (d : HSMDatum D Ω κ) {m₀ m₁ : ConeMetric ℂ (Ix κ)} (h₀ : IsSmoothMetric m₀)
    (h₁ : IsSmoothMetric m₁) :
    mInt d.R.A (fun _ => resPot d m₁) (fun _ => 1) = mInt d.R.A (fun _ => resPot d m₀) (fun _ => 1) := by
  rw [mInt_resPot_eq d (m₀ := m₀)]
  exact massIndep d.R.A (fun _ => resPot d m₀) (fun _ y => logRatio m₀ m₁ (resPt d y))
    (fun _ => isPotential_resPot d h₀) (fun _ => smooth_logRatio_resPt d h₀ h₁)

theorem mass_pullFS (hPM : ProjFSMass.Statement) (d : HSMDatum D Ω κ) {e : Fin (D + 1) → Ix κ}
    {m₀ : ConeMetric ℂ (Ix κ)} (hfr : IsProjFrame d.x e) (h₀ : IsSmoothMetric m₀) (hFS : IsPullFS d.x e m₀) :
    mInt d.R.A (fun _ => resPot d m₀) (fun _ => 1) = (projDeg d.x e : ℝ) := by
  obtain ⟨Ψ, hΨ, hmass⟩ := hPM D Ω κ d.x e m₀ hfr hFS
  let A : HermLine (GlobalTheory κ) := HermLine.ofWeight (fun _ => (1 : ℝ)) (fun _ _ _ => rfl)
  have hA : IsSmoothHerm A := contDiffOn_const
  have hlog : logNorm A 1 = fun _ => (1 : ℝ) := by
    funext z
    simp [A, logNorm, HermLine.ofWeight]
  have hsec : IsSectionOn (coordIdeal ℤ d.x) A 1 := by
    refine ⟨fun _ => 0, fun _ => rfl, ?_, ?_⟩
    · intro a ha k
      rw [support_one] at ha
      simp only [Finset.mem_singleton] at ha
      simp [ha]
    · exact (Ideal.ne_top_iff_one _).1 d.arith.2.1.1.ne_top
  have key := AnResBridge.bridge d.R Ψ (fun _ => HermLine.ofCone m₀) A 1 d.arith hΨ
    (fun _ => gbamix_smoothHerm_ofCone h₀) hA hsec
  rw [hlog] at key
  rw [← hmass]
  exact key.symm

end ResolutionDegree

theorem ResolutionDegree.proof (hPF : PullFSExtension.Statement) (hPM : ProjFSMass.Statement) :
    ResolutionDegree.Statement := by
  intro D Ω _ _ κ _ d e m hfr hm
  obtain ⟨m₀, h₀, -, -, hFS⟩ := hPF D Ω κ d.x e hfr
  rw [ResolutionDegree.mass_eq d h₀ hm]
  exact ResolutionDegree.mass_pullFS hPM d hfr h₀ hFS

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

