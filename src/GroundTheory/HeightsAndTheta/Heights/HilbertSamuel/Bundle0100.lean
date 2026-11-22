import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0033
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0018
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0011
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0095
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0026
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0096
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinVertDivIff
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0014
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0091
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0092
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0097
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0087
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0024
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0012
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PZCombLimit
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0034
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsAntisym

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.InverseDerivativeContinuity
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology MeasureTheory

noncomputable section

set_option linter.unusedSectionVars false

namespace G1

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem geoNum_nonneg : ∀ (n : ℕ) (V : Ideal (MRing ι)) (b : Fin n → K → ℤ),
    (∀ j k, 0 ≤ b j k) → 0 ≤ geoNum n V b
  | 0, V, b, _ => by
    unfold geoNum
    split_ifs <;> positivity
  | n + 1, V, b, hb => by
    rw [geoNum]
    split_ifs with h
    · refine Finset.sum_nonneg fun k _ => mul_nonneg (hb _ k) ?_
      exact finsum_nonneg fun W => finsum_nonneg fun _ =>
        mul_nonneg (Nat.cast_nonneg _) (geoNum_nonneg n W (Fin.init b) fun j k => hb _ k)
    · exact le_rfl

theorem finsum_nonpos' {α : Sort*} {g : α → ℝ} (h : ∀ x, g x ≤ 0) : ∑ᶠ x, g x ≤ 0 := by
  have h0 : 0 ≤ ∑ᶠ x, -g x := finsum_nonneg fun x => neg_nonneg.2 (h x)
  rw [finsum_neg_distrib] at h0
  exact neg_nonneg.1 h0

theorem mcPts_anti {P W : Ideal (MRing ι)} (h : P ≤ W) : mcPts W ⊆ mcPts P :=
  fun _ hz => ⟨hz.1, fun f hf => hz.2 f (h hf)⟩

theorem isOpen_blocksNonzero : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  have e : {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} = ⋂ k, ⋃ i, {z | z ⟨k, i⟩ ≠ 0} := by
    ext z
    simp
  rw [e]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

theorem exists_monomial_not_mem {P : Ideal (MRing ι)} (hP : IsMultiProjPrime P) (a : K → ℕ) :
    ∃ μ : (Σ k, ι k) →₀ ℕ, (∀ k, ∑ i, μ ⟨k, i⟩ = a k) ∧ monomial μ (1 : ℤ) ∉ P := by
  classical
  choose c hc using hP.2.2
  let μ : (Σ k, ι k) →₀ ℕ :=
    Finsupp.equivFunOnFinite.symm fun p => if p.2 = c p.1 then a p.1 else 0
  refine ⟨μ, fun k => ?_, ?_⟩
  · simp [μ]
  · intro hmem
    have := hP.1
    rw [monomial_eq, C_1, one_mul, Finsupp.prod] at hmem
    obtain ⟨p, hp, hpP⟩ := Ideal.IsPrime.prod_mem_iff.1 hmem
    have hX := hP.1.mem_of_pow_mem _ hpP
    have hμp : μ p ≠ 0 := Finsupp.mem_support_iff.1 hp
    obtain ⟨k, j⟩ := p
    by_cases hj : j = c k
    · subst hj
      exact hc k hX
    · exact hμp (by simp [μ, hj])

theorem isMultiHomog_monomial {μ : (Σ k, ι k) →₀ ℕ} {a : K → ℕ} (hμ : ∀ k, ∑ i, μ ⟨k, i⟩ = a k) :
    IsMultiHomog (monomial μ (1 : ℤ)) a := by
  intro m hm k
  rw [Finset.mem_singleton.1 (support_monomial_subset hm)]
  exact hμ k

theorem eval_monomial_one (μ : (Σ k, ι k) →₀ ℕ) (z : (Σ k, ι k) → ℂ) :
    eval z (map (Int.castRingHom ℂ) (monomial μ (1 : ℤ))) = ∏ p, z p ^ μ p := by
  rw [map_monomial, eval_monomial, map_one, one_mul, Finsupp.prod_fintype]
  intro p
  simp

theorem isConeTangent_of_sheet {P0 P : Ideal (MRing ι)} (hP0 : P0 ≤ P) {e : ℕ}
    {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ} {y : Fin e → ℂ} (hγ : AnalyticAt ℂ γ y)
    (hpts : ∀ᶠ y' in 𝓝 y, γ y' ∈ mcPts P) (ξ : Fin e → ℂ) :
    IsConeTangent (Int.castRingHom ℂ) P0 (γ y) (fderiv ℂ γ y ξ) := by
  intro f hf
  set F := map (Int.castRingHom ℂ) f
  have hzero : (fun w => eval w F) ∘ γ =ᶠ[𝓝 y] fun _ => (0 : ℂ) := by
    filter_upwards [hpts] with w hw
    exact hw.2 f (hP0 hf)
  have hd := (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adens_hasFDerivAt_eval F (γ y)).comp y
    hγ.differentiableAt.hasFDerivAt
  have h0 : HasFDerivAt ((fun w => eval w F) ∘ γ) (0 : (Fin e → ℂ) →L[ℂ] ℂ) y :=
    (hasFDerivAt_const (0 : ℂ) y).congr_of_eventuallyEq hzero
  have := congrArg (fun L => L ξ) (hd.unique h0)
  simpa [ContinuousLinearMap.sum_apply, smul_eq_mul] using this

theorem maDensity_nonneg_of_sheet {P0 P : Ideal (MRing ι)} (hP0 : P0 ≤ P) {A : HermLine ι}
    (hsp : IsSemipositiveRel P0 P A) {e : ℕ} {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
    {y : Fin e → ℂ} {w : ((k : K) → ι k) → ℂ} {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ}
    (h : IsSheet P Ψ y w γ) :
    0 ≤ maDensity (fun _ y' => Real.log (A.h (γ y'))) y := by
  have hA : AnalyticAt ℂ γ y := sheet_analyticAt osgood h
  have hpts : ∀ᶠ y' in 𝓝 y, γ y' ∈ mcPts P := h.2.mono fun _ hy' => hy'.2.1
  have hy : γ y ∈ mcPts P := hpts.self_of_nhds
  have hh : ContDiffAt ℝ 2 A.h (γ y) :=
    (hsp.1.contDiffAt (isOpen_blocksNonzero.mem_nhds hy.1)).of_le (WithTop.coe_le_coe.2 le_top)
  have hlog : ContDiffAt ℝ 2 (fun z => Real.log (A.h z)) (γ y) := hh.log (A.pos _ hy.1).ne'
  have h2 : ContDiffAt ℝ 2 (fun y' => Real.log (A.h (γ y'))) y :=
    hlog.comp y (hA.contDiffAt.restrict_scalars ℝ)
  rw [ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adens_maDensity_eq_maDens]
  refine ReciprocityTheory.AnForm.A.maDens_nonneg_of_posSemidef _ _ fun _ => ?_
  refine ReciprocityTheory.AnForm.A.hessC_posSemidef_of_levi _ _ h2 fun ξ => ?_
  have hl := ReciprocityTheory.AnForm.levi_comp (φ := fun z => Real.log (A.h z)) ξ hA hlog
  change 0 ≤ ReciprocityTheory.AnForm.levi ((fun z => Real.log (A.h z)) ∘ γ) y ξ
  rw [hl]
  exact hsp.2 _ hy _ (isConeTangent_of_sheet hP0 hA hpts ξ)

theorem arInt_nonpos {P0 P : Ideal (MRing ι)} (hP0 : P0 ≤ P) {A : HermLine ι}
    (hsp : IsSemipositiveRel P0 P A) {s : MRing ι}
    (hs : ∀ z ∈ mcPts P, ‖eval z (map (Int.castRingHom ℂ) s)‖ ≤ A.h z) (e : ℕ) :
    arInt P s A (fun _ : Fin e => A) ≤ 0 := by
  classical
  unfold arInt ptsIntegral
  split_ifs with hΨ
  · unfold ptsIntegralAt
    refine integral_nonpos fun y => ?_
    have key : ∀ w, sheetDensity P hΨ.choose (fun (_ : Fin e) z => Real.log (A.h z))
        (logNorm A s) y w ≤ 0 := by
      intro w
      unfold sheetDensity
      split_ifs with hγ
      · have hsh := hγ.choose_spec
        have hz : hγ.choose y ∈ mcPts P := hsh.2.self_of_nhds.2.1
        have hpos := A.pos _ hz.1
        have hg : logNorm A s (hγ.choose y) ≤ 0 :=
          Real.log_nonpos (div_nonneg (norm_nonneg _) hpos.le)
            ((div_le_one hpos).2 (hs _ hz))
        exact mul_nonpos_of_nonpos_of_nonneg hg (maDensity_nonneg_of_sheet hP0 hsp hsh)
      · exact le_rfl
    exact finsum_nonpos' fun w => finsum_nonpos' fun _ => key w
  · exact le_rfl

theorem nonneg_of_family (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ)
    (hI : IsIntersectionFamily I) (a : K → ℕ) (A : HermLine ι) (hA : A.a = fun k => (a k : ℤ))
    (P0 : Ideal (MRing ι)) (n : ℕ) :
    ∀ P : Ideal (MRing ι), IsArithVar P n → P0 ≤ P → IsSemipositiveRel P0 P A →
      MonomialsBounded P A a → 0 ≤ I P n (fun _ => A) := by
  induction n with
  | zero =>
    intro P hP
    exact (GroundTheory.Heights₂.Heights.Inter.arithVarZero K ι P hP).elim
  | succ m ih =>
    intro P hP hP0 hsp hmb
    obtain ⟨μ, hμ, hμP⟩ := exists_monomial_not_mem hP.2.1 a
    set s : MRing ι := monomial μ (1 : ℤ) with hsdef
    have hsa : IsMultiHomog s a := isMultiHomog_monomial hμ
    have hAa : ∀ k, A.a k = a k := fun k => by rw [hA]
    have hsmall : ∀ z ∈ mcPts P, ‖eval z (map (Int.castRingHom ℂ) s)‖ ≤ A.h z := by
      intro z hz
      rw [hsdef, eval_monomial_one]
      exact hmb z hz μ hμ
    have hR := hI.2.2 P m (fun _ => A) A s a hP (fun _ => hsp.1) hsp.1 hAa hsa hμP
    have hconst : (Fin.snoc (fun _ : Fin m => A) A : Fin (m + 1) → HermLine ι) = fun _ => A := by
      funext j
      refine Fin.lastCases ?_ (fun j => ?_) j <;> simp
    rw [hconst] at hR
    rw [hR, recR]
    refine sub_nonneg.2 (le_trans (arInt_nonpos hP0 hsp hsmall m)
      (finsum_nonneg fun W => finsum_nonneg fun hW => mul_nonneg (Nat.cast_nonneg _) ?_))
    have hPW : P ≤ W := le_sup_left.trans hW.1.1.2
    split_ifs with hH
    · have hWar := (divSuppArith K ι P m A s W hP ⟨a, hAa, hsa, hμP⟩ hW).1 hH
      exact ih W hWar (hP0.trans hPW) ⟨hsp.1, fun z hz w hw => hsp.2 z (mcPts_anti hPW hz) w hw⟩
        (fun z hz μ' hμ' => hmb z (mcPts_anti hPW hz) μ' hμ')
    · refine mul_nonneg (Int.cast_nonneg (geoNum_nonneg m W _ fun j k => ?_))
        (Real.log_natCast_nonneg _)
      simp [hA]

end G1

theorem G1.proof : G1.Statement := by
  intro K _ ι _ Ω _ y D a A P0 II _ hII hP _ hA hP0 hsp hmb _
  exact G1.nonneg_of_family (II K ι) (hII K ι) a A hA P0 (D + 1) _ hP hP0 hsp hmb

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockResolutionFormsIndependent
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry SupBoundCount

noncomputable section

theorem BlockResolutionFormsIndependent.proof (hND : NonvanishingDense.Statement) :
    BlockResolutionFormsIndependent.Statement := by
  intro D K _ _ ι _ Ω _ _ d n r b hb a ha
  choose f hf hbf using hb.1
  obtain ⟨g, hgJ, hgP⟩ := SetLike.not_le_iff_exists.1 d.R.nondeg

  set F : ((Σ k, ι k) → ℂ) → ℂ := fun z => ∑ k, a k * eval z (map (Int.castRingHom ℂ) (f k)) with hF
  have ha' : ∀ x : d.R.X, F (blockPt d x) = 0 := by
    intro x
    have := ha x
    simp only [hbf, eval_map_int_rat] at this
    exact this
  have hli : LinearIndependent ℤ fun k => aeval d.y (f k) := by
    have := hb.2.1
    simp only [hbf, aeval_map_int] at this
    exact this
  have hFc : Continuous F :=
    continuous_finsetSum _ fun k _ => continuous_const.mul (continuous_eval _)

  have hev : ∀ (s : MRing ι) (e : K → ℕ), IsMultiHomog s e → ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ),
      eval (fun p => c p.1 * z p) (map (Int.castRingHom ℂ) s) =
        (∏ k, c k ^ e k) * eval z (map (Int.castRingHom ℂ) s) := by
    intro s e hs c z
    rw [eval_map, eval_map, eval₂_eq', eval₂_eq', Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hc : (∏ i : (Σ k, ι k), c i.1 ^ m i) = ∏ k, c k ^ e k := by
      rw [Fintype.prod_sigma]
      refine Finset.prod_congr rfl fun k _ => ?_
      show ∏ i, c k ^ m ⟨k, i⟩ = _
      rw [Finset.prod_pow_eq_pow_sum, hs m hm k]
    simp only [mul_pow, Finset.prod_mul_distrib, hc]
    ring

  have hsmul : ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ),
      F (fun p => c p.1 * z p) = (∏ k, c k ^ blockDeg d.k₀ n k) * F z := by
    intro c z
    simp only [hF, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hev (f k) _ (hf k) c z]
    ring

  have hoff : ∀ z, z ∈ mcPts (mCoordIdeal d.y) →
      eval z (map (Int.castRingHom ℂ) g) ≠ 0 → F z = 0 := by
    intro z hz hgz
    obtain ⟨x, c, hc, hxz⟩ := d.R.surj z hz (fun hJ => hgz (hJ.2 g hgJ))
    have h1 := ha' x
    rw [show blockPt d x = d.R.lift x x from rfl, hxz, hsmul] at h1
    exact (mul_eq_zero.1 h1).resolve_left
      (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k))

  have hpts : ∀ z ∈ mcPts (mCoordIdeal d.y), F z = 0 := by
    intro z hz
    have hcl := hND K ι (mCoordIdeal d.y) (D + 1) g d.arith hgP hz
    exact (isClosed_eq hFc continuous_const).closure_subset_iff.2 (fun z' hz' => hoff z' hz'.1 hz'.2) hcl
  exact coeff_eq_zero hli (mcPts_nonempty d) hpts

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PClosedPtChartUnit
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

theorem ClosedPtChartUnit.proof : ClosedPtChartUnit.Statement := by
  classical
  intro S _ K _ ι _ P hP I hI hX f a hf hfP
  have : P.IsPrime := hP.1.1

  have hTP : KH.cellMon S I ≤ P.primeCompl :=
    Submonoid.closure_le.mpr (by rintro _ ⟨k, i, hi, rfl⟩; exact hX k i hi)
  have hPh : NumbersDVR.IsMultiHomogIdeal P := (NumbersDVR.Objects.isMultiHomogIdeal_iff P).mpr hP.1.2.1

  obtain ⟨t, htT, htJ⟩ : ∃ t ∈ KH.cellMon S I, t ∈ P ⊔ Ideal.span {f} := by
    by_contra hno
    push Not at hno
    obtain ⟨p, hp, hJp, hdisj⟩ := Ideal.exists_le_prime_disjoint (P ⊔ Ideal.span {f}) (KH.cellMon S I)
      (Set.disjoint_left.mpr fun x hxJ hxT => hno x hxT hxJ)
    obtain ⟨W, hW, hWh, hWp, hWJ, hWf⟩ := NumbersDVR.exists_multiHomog_core hp
    have hPW : P ≤ W := hWJ P hPh (le_sup_left.trans hJp)
    have hfW : f ∈ W :=
      hWf f a ((NumbersDVR.Objects.isMultiHomog_iff f a).mpr hf)
        (hJp (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f)))
    have hrel : IsRelevant W := by
      intro k
      obtain ⟨i, hi⟩ := hI k
      refine ⟨i, fun hXW => Set.disjoint_left.mp hdisj (hWp hXW) ?_⟩
      exact Submonoid.subset_closure ⟨k, i, hi, rfl⟩
    have hWP : W = P := hP.2 W ⟨hW, (NumbersDVR.Objects.isMultiHomogIdeal_iff W).mp hWh, hrel⟩ hPW
    exact hfP (hWP ▸ hfW)

  obtain ⟨e, hte'⟩ : ∃ e, NumbersDVR.IsMultiHomog t e := by
    clear htJ
    induction htT using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨k, i, -, rfl⟩ := hx
      exact ⟨_, isWeightedHomogeneous_X S (NumbersDVR.blockWeight ι) ⟨k, i⟩⟩
    | one => exact ⟨0, isWeightedHomogeneous_one S (NumbersDVR.blockWeight ι)⟩
    | mul x y _ _ hx hy =>
      obtain ⟨c, hc⟩ := hx
      obtain ⟨d, hd⟩ := hy
      exact ⟨c + d, IsWeightedHomogeneous.mul hc hd⟩
  have hf' : NumbersDVR.IsMultiHomog f a := (NumbersDVR.Objects.isMultiHomog_iff f a).mpr hf
  obtain ⟨p, hpP, r, hr, hpr⟩ := Submodule.mem_sup.mp htJ
  obtain ⟨g₀, rfl⟩ := Ideal.mem_span_singleton'.mp hr
  have hcomp : weightedHomogeneousComponent (NumbersDVR.blockWeight ι) e t =
      weightedHomogeneousComponent (NumbersDVR.blockWeight ι) e p +
        weightedHomogeneousComponent (NumbersDVR.blockWeight ι) e (g₀ * f) := by
    rw [← hpr, map_add]
  have htself : weightedHomogeneousComponent (NumbersDVR.blockWeight ι) e t = t := by
    rw [weightedHomogeneousComponent_of_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr hte'), if_pos rfl]
  rw [htself] at hcomp
  have hpe : weightedHomogeneousComponent (NumbersDVR.blockWeight ι) e p ∈ P := hPh p hpP e
  by_cases hae : a ≤ e
  · refine ⟨t, htT, weightedHomogeneousComponent (NumbersDVR.blockWeight ι) (e - a) g₀, e - a, ?_, ?_, ?_⟩
    · rw [add_tsub_cancel_of_le hae]
      exact (NumbersDVR.Objects.isMultiHomog_iff t e).mp hte'
    · exact (NumbersDVR.Objects.isMultiHomog_iff _ _).mp (weightedHomogeneousComponent_isWeightedHomogeneous _ _)
    · rw [NumbersDVR.component_mul_form_of_le hf' hae] at hcomp
      rw [hcomp, add_sub_cancel_right]
      exact hpe
  · rw [NumbersDVR.component_mul_form_of_not_le hf' hae, add_zero] at hcomp
    exact absurd (hcomp ▸ hpe) (hTP htT)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PClosedPtFibreLift
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

theorem ClosedPtFibreLift.proof (hG : GradedSubmodules.Statement) (hSES : KH.CechSESStatement)
    (hSky : ClosedPtSkyscraper.Statement) (hKer : LocIdealKer.Statement) : ClosedPtFibreLift.Statement := by
  intro S _ K _ _ ι _ _ M _ _ _ _ 𝓜 P d _ _ h𝓜 hP hH1 I hI x hx
  have hPh : IsMultiHomogIdeal P := hP.1.2.1
  obtain ⟨h𝓝', h𝓝''⟩ := (hG S K ι M 𝓜 h𝓜).2 P hPh

  have hyd : GenSESStep.locMap (KH.cellMon S I.1) (P • ⊤ : Submodule (MRingOver S ι) M).mkQ x ∈
      KH.locPart ι (quotGrading 𝓜 (P • ⊤ : Submodule (MRingOver S ι) M)) (KH.cellMon S I.1) d := by
    obtain ⟨m, t, a, ht, hm, rfl⟩ := GenSESStep.locPart_normal h𝓜 hx
    rw [GenSESStep.locMap_mk]
    exact GenSESStep.mk_mem_locPart _ t a ht ⟨m, hm, rfl⟩

  have hkill : ∀ p ∈ P, ∀ n : M ⧸ (P • ⊤ : Submodule (MRingOver S ι) M), p • n = 0 := by
    intro p hp n
    induction n using Submodule.Quotient.induction_on with
    | H m =>
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact Submodule.smul_mem_smul hp Submodule.mem_top

  obtain ⟨z'', hz'', hz''I⟩ := hSky S K ι _ _ P d h𝓝'' hP hkill I hI _ hyd

  have hg : KH.IsMGradedMap S ι (subGrading 𝓜 (P • ⊤ : Submodule (MRingOver S ι) M)) 𝓜
      (P • ⊤ : Submodule (MRingOver S ι) M).subtype := fun _ _ hm => hm
  have hh : KH.IsMGradedMap S ι 𝓜 (quotGrading 𝓜 (P • ⊤ : Submodule (MRingOver S ι) M))
      (P • ⊤ : Submodule (MRingOver S ι) M).mkQ := fun _ m hm => ⟨m, hm, rfl⟩
  obtain ⟨z, hz, hzmap⟩ := (hSES S K ι _ M _ _ 𝓜 _ _ _ h𝓝' h𝓜 h𝓝'' hg hh
    (Submodule.injective_subtype _) (Submodule.mkQ_surjective _)
    (by rw [Submodule.range_subtype, Submodule.ker_mkQ]) d 0).2.2.2.2.1 hH1 z'' hz''
  refine ⟨z, hz, ?_⟩
  have hzI : z I ∈ KH.locPart ι 𝓜 (KH.cellMon S I.1) d := Submodule.mem_pi.mp hz.1 I (Set.mem_univ _)

  refine (hKer S K ι M 𝓜 P (KH.cellMon S I.1) d h𝓜 hPh (fun _ ht => GenSESStep.cellMon_homog ht) _
    (sub_mem hx hzI)).2 ?_
  have e : GenSESStep.locMap (KH.cellMon S I.1) (P • ⊤ : Submodule (MRingOver S ι) M).mkQ (z I) = z'' I :=
    congrFun hzmap I
  rw [map_sub]
  change _ - GenSESStep.locMap (KH.cellMon S I.1) (P • ⊤ : Submodule (MRingOver S ι) M).mkQ (z I) = 0
  rw [e, hz''I, sub_self]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFSGeomDegPos
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

theorem FSGeomDegPos.proof (hDeg : DegreeStatement) (hPos : MultiDegreePositive.Statement) :
    FSGeomDegPos.Statement := by
  intro K _ ι _ P e hP
  classical
  have hS : ∀ j : Fin e, IsSmoothHerm ((fun _ : Fin e => fsH ι) j) := fun _ =>
    GroundTheory.Heights₂.Heights.Inter.isSmoothHerm_ofMetrics_fs 1
  have ha : (fun j : Fin e => ((fun _ : Fin e => fsH ι) j).a) = fun _ : Fin e => fun _ : K => (1 : ℤ) := by
    funext j k
    simp [fsH, HermLine.ofMetrics]
  obtain ⟨hq, hd⟩ := ZCombLimit.genericFibre hP
  have hpos := hPos ℚ K ι _ e hq hd
  rw [GroundTheory.Heights₂.Heights.Targets.FibreDegreeSum.proof K ι P e _ 2 hP Nat.prime_two,
    finsum_mem_eq_finite_toFinset_sum _ (divSupp_finite P _)] at hpos
  rw [hDeg K ι P e (fun _ => fsH ι) 2 hP hS Nat.prime_two, ha,
    finsum_mem_eq_finite_toFinset_sum _ (divSupp_finite P _)]
  exact_mod_cast hpos

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFibreNormBadPrimesFinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem aeval_map_intRat_eq {σ : Type} (x : σ → ℂ) (f : MvPolynomial σ ℤ) :
    aeval x (map (algebraMap ℤ ℚ) f) = eval x (map (Int.castRingHom ℂ) f) := by
  rw [aeval_def, eval₂_map, eval_map]
  congr 1

theorem FibreNormBadPrimesFinite.proof : FibreNormBadPrimesFinite.Statement := by
  intro K _ ι _ Ω _ _ y D e L _ _ _ _ hC
  set I : Ideal (MvPolynomial (Σ k, ι k) ℤ) := mCoordIdeal y ⊔ Ideal.span (Set.range L) with hIdef
  have key : ∀ c : ∀ k, ι k, ∃ N : ℤ, N ≠ 0 ∧
      ∃ r : ℕ, C N * (∏ k, X ⟨k, c k⟩ : MvPolynomial (Σ k, ι k) ℤ) ^ r ∈ I := by
    intro c
    set f : MvPolynomial (Σ k, ι k) ℤ := ∏ k, X ⟨k, c k⟩
    set IQ := Ideal.map (algebraMap (MvPolynomial (Σ k, ι k) ℤ) (MvPolynomial (Σ k, ι k) ℚ)) I
    have hv : algebraMap _ (MvPolynomial (Σ k, ι k) ℚ) f ∈ vanishingIdeal ℚ (zeroLocus ℂ IQ) := by
      rw [mem_vanishingIdeal_iff]
      intro x hx
      rw [mem_zeroLocus_iff] at hx
      have h0 : ∀ g ∈ I, eval x (map (Int.castRingHom ℂ) g) = 0 := fun g hg => by
        rw [← aeval_map_intRat_eq, ← algebraMap_def]
        exact hx _ (Ideal.mem_map_of_mem _ hg)
      rw [algebraMap_def, aeval_map_intRat_eq]
      by_contra hne
      simp only [f, map_prod, map_X, eval_X] at hne
      have hblk : ∀ k, x ⟨k, c k⟩ ≠ 0 := fun k => (Finset.prod_ne_zero_iff.1 hne) k (Finset.mem_univ _)
      obtain ⟨j, hj⟩ := hC x ⟨fun k => ⟨c k, hblk k⟩, fun g hg => h0 g (Ideal.mem_sup_left hg)⟩
      exact hj (h0 _ (Ideal.mem_sup_right (Ideal.subset_span ⟨j, rfl⟩)))
    rw [vanishingIdeal_zeroLocus_eq_radical] at hv
    obtain ⟨r, hr⟩ := hv
    rw [← map_pow, IsLocalization.mem_map_algebraMap_iff ((nonZeroDivisors ℤ).map (C (σ := Σ k, ι k)))]
      at hr
    obtain ⟨⟨⟨u, hu⟩, ⟨m, hm⟩⟩, h⟩ := hr
    obtain ⟨n, hn, rfl⟩ := Submonoid.mem_map.1 hm
    refine ⟨n, nonZeroDivisors.ne_zero hn, r, ?_⟩
    have hinj : Function.Injective (map (σ := Σ k, ι k) (algebraMap ℤ ℚ)) :=
      map_injective _ (algebraMap ℤ ℚ).injective_int
    have hu' : f ^ r * C n = u := hinj (by simpa only [algebraMap_def, map_mul] using h)
    rw [mul_comm, hu']
    exact hu
  choose N hN r hr using key
  refine Set.Finite.subset (Set.finite_iUnion fun c => (Set.finite_Iic (N c).natAbs)) ?_
  rintro p ⟨hp, hH⟩
  obtain ⟨z, hz, hP, hL⟩ := hH
  choose c hc using hz
  have : Fact p.Prime := ⟨hp⟩
  have : CharP (AlgebraicClosure (ZMod p)) p :=
    charP_of_injective_algebraMap (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))).injective p
  have hker : I ≤ RingHom.ker ((eval z).comp (map (Int.castRingHom (AlgebraicClosure (ZMod p))))) :=
    sup_le (fun g hg => hP g hg) (Ideal.span_le.2 (by rintro _ ⟨j, rfl⟩; exact hL j))
  have h1 := hker (hr c)
  simp only [RingHom.mem_ker, RingHom.comp_apply, map_mul, map_pow, map_prod, map_X, eval_X, eq_intCast,
    map_intCast] at h1
  have hprod : (∏ k, z ⟨k, c k⟩) ^ r c ≠ 0 :=
    pow_ne_zero _ (Finset.prod_ne_zero_iff.2 fun k _ => hc k)
  have hNz : ((N c : ℤ) : AlgebraicClosure (ZMod p)) = 0 := (mul_eq_zero.1 h1).resolve_right hprod
  rw [CharP.intCast_eq_zero_iff (AlgebraicClosure (ZMod p)) p] at hNz
  simp only [Set.mem_iUnion, Set.mem_Iic]
  exact ⟨c, Nat.le_of_dvd (Int.natAbs_pos.2 (hN c)) (Int.natCast_dvd.1 hNz)⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

