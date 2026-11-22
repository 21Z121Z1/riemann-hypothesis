import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0022
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreChartDim
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0030
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0018
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0017
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0049
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0044
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0079
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCurveVertPointNagata
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0042
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0052

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PChartDivisorComponents
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsArithVar IsSectionOn divSupp IsHorizontal IsRelevant IsMultiHomogIdeal mcPts
  segre divSupp_finite divSuppArith mcPts_smul)
open GroundTheory.Heights₂.Heights (segreChartSet segreChartIdeal segreChartComponents mem_segreChartComponents chartLift
  chartLift_segre_apply segre_chartLift chartLift_blockNonzero)

namespace ChartDivisorComponents

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {m : ℕ}

theorem chartLift_mem_mcPts {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) (σ : Fin m ≃ ((k : K) → ι k))
    (i : (k : K) → ι k) {x : Fin m → ℂ} (hx : x ∈ segreChartSet P σ i) : chartLift σ i x ∈ mcPts P := by
  obtain ⟨z, hz, hzi, rfl⟩ := hx
  have hne : ∀ k, (z ⟨k, i k⟩)⁻¹ ≠ 0 := fun k => inv_ne_zero fun h0 => by
    have : segre z i = 0 := Finset.prod_eq_zero (Finset.mem_univ k) h0
    rw [hzi] at this
    exact one_ne_zero this
  have heq : chartLift σ i (fun a => segre z (σ a)) = fun p => (z ⟨p.1, i p.1⟩)⁻¹ * z p := by
    funext p
    rw [chartLift_segre_apply σ i z hzi p.1 p.2, mul_comm]
  rw [heq]
  exact mcPts_smul hP (fun k => (z ⟨k, i k⟩)⁻¹) hne hz

theorem chartSection_mem {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) (σ : Fin m ≃ ((k : K) → ι k))
    (i : (k : K) → ι k) {f : MRing ι} (hf : f ∈ P) : chartSection σ i f ∈ segreChartIdeal P σ i := by
  rw [segreChartIdeal, mem_vanishingIdeal_iff]
  intro x hx
  change eval x (chartSection σ i f) = 0
  rw [eval_chartSection]
  exact (chartLift_mem_mcPts hP σ i hx).2 f hf

theorem mem_segreChartSet_of_forall {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) (σ : Fin m ≃ ((k : K) → ι k))
    (i : (k : K) → ι k) {x : Fin m → ℂ} (hx : ∀ f ∈ segreChartIdeal P σ i, eval x f = 0) :
    x ∈ segreChartSet P σ i := by
  have hxi : x (σ.symm i) = 1 := by
    have hmem : (X (σ.symm i) - 1 : MvPolynomial (Fin m) ℂ) ∈ segreChartIdeal P σ i := by
      rw [segreChartIdeal, mem_vanishingIdeal_iff]
      rintro _ ⟨z, -, hzi, rfl⟩
      simp [hzi]
    have h := hx _ hmem
    simp only [map_sub, eval_X, map_one] at h
    exact sub_eq_zero.1 h
  have hseg : ∀ a, x a = segre (chartLift σ i x) (σ a) := by
    intro a
    have hmem : (X a - ∏ k, X (σ.symm (Function.update i k (σ a k))) : MvPolynomial (Fin m) ℂ) ∈
        segreChartIdeal P σ i := by
      rw [segreChartIdeal, mem_vanishingIdeal_iff]
      rintro _ ⟨z, -, hzi, rfl⟩
      have h := congrFun (segre_chartLift σ i z hzi) (σ a)
      change eval _ (X a - ∏ k, X (σ.symm (Function.update i k (σ a k)))) = 0
      rw [map_sub, map_prod, sub_eq_zero]
      simp only [eval_X]
      exact h.symm.trans rfl
    have h := hx _ hmem
    simp only [map_sub, eval_X, map_prod] at h
    rw [sub_eq_zero] at h
    rw [h]
    rfl
  refine ⟨chartLift σ i x, ⟨chartLift_blockNonzero σ i hxi, fun f hf => ?_⟩, ?_, funext hseg⟩
  · rw [← eval_chartSection]
    exact hx _ (chartSection_mem hP σ i hf)
  · show ∏ k, x (σ.symm (Function.update i k (i k))) = 1
    simp [hxi]

theorem exists_divSupp_of_eval {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) (σ : Fin m ≃ ((k : K) → ι k))
    (i : (k : K) → ι k) (s : MRing ι) {x : Fin m → ℂ} (hx : x ∈ segreChartSet P σ i)
    (hs : eval x (chartSection σ i s) = 0) :
    ∃ W, (W ∈ divSupp P s ∧ IsHorizontal W) ∧ x ∈ segreChartSet W σ i := by
  have hz := chartLift_mem_mcPts hP σ i hx
  obtain ⟨z₀, -, hz₀i, hxz₀⟩ := hx
  set z := chartLift σ i x with hzdef
  have hsz : segre z = segre z₀ := by rw [hzdef, hxz₀]; exact segre_chartLift σ i z₀ hz₀i
  let φ : MRing ι →+* ℂ := (eval z).comp (map (Int.castRingHom ℂ))
  have hφ : ∀ f, φ f = eval z (map (Int.castRingHom ℂ) f) := fun _ => rfl
  have : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  have hle : P ⊔ Ideal.span {s} ≤ RingHom.ker φ := by
    refine sup_le (fun f hf => by rw [RingHom.mem_ker, hφ]; exact hz.2 f hf) ?_
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, hφ, ← eval_chartSection]
    exact hs
  obtain ⟨W, hW, hWle⟩ := Ideal.exists_minimalPrimes_le hle
  refine ⟨W, ⟨⟨hW, fun k => ?_⟩, ?_⟩, z, ⟨hz.1, fun f hf => hWle hf⟩, ?_, ?_⟩
  · obtain ⟨j, hj⟩ := hz.1 k
    exact ⟨j, fun h => hj (by simpa [hφ] using hWle h)⟩
  · refine eq_bot_iff.2 fun c hc => ?_
    have h := hWle hc
    rw [RingHom.mem_ker, hφ] at h
    simpa using h
  · rw [hsz]; exact hz₀i
  · rw [hsz]; exact hxz₀

theorem eq_of_le_of_dim {Q Q' : Ideal (MvPolynomial (Fin m) ℂ)} [Q.IsPrime] (hle : Q ≤ Q') (n : ℕ)
    (hQ : ringKrullDim (MvPolynomial (Fin m) ℂ ⧸ Q) + 1 = ((n + 1 : ℕ) : WithBot ℕ∞))
    (hQ' : ringKrullDim (MvPolynomial (Fin m) ℂ ⧸ Q') = (n : ℕ)) : Q = Q' := by
  by_contra hne
  have h := SectionComponents.ringKrullDim_quotient_add_one_le_of_lt (lt_of_le_of_ne hle hne)
  rw [hQ'] at h
  have h2 : ((n : ℕ) : WithBot ℕ∞) + 1 + 1 ≤ ((n + 1 : ℕ) : WithBot ℕ∞) := by
    rw [← hQ]
    exact add_le_add h le_rfl
  have h3 : ((n + 1 + 1 : ℕ) : WithBot ℕ∞) ≤ ((n + 1 : ℕ) : WithBot ℕ∞) := by exact_mod_cast h2
  have h4 : n + 1 + 1 ≤ n + 1 := by exact_mod_cast h3
  omega

theorem le_of_common (hNot : ChartSectionNotMem.Statement) {W₁ W₂ : Ideal (MRing ι)} {n : ℕ}
    (h₁ : IsArithVar W₁ (n + 1)) (h₂ : IsMultiHomogIdeal W₂) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    {W' : Ideal (MvPolynomial (Fin m) ℂ)} (hW₁ : W' ∈ segreChartComponents W₁ σ i)
    (hW₂ : W' ∈ segreChartComponents W₂ σ i) : W₂ ≤ W₁ := by
  have h₂' := h₂
  obtain ⟨S, hS, rfl⟩ := h₂
  refine Ideal.span_le.2 fun f hf => ?_
  by_contra hfW
  obtain ⟨a, ha⟩ := hS f hf
  have hsec : IsSectionOn W₁ (HermLine.sqMetric (ι := ι) a) f := ⟨a, fun _ => rfl, ha, hfW⟩
  exact hNot K ι W₁ n m σ i _ f h₁ hsec W' hW₁
    ((mem_segreChartComponents.1 hW₂).1.2 (chartSection_mem h₂' σ i (Ideal.subset_span hf)))

end ChartDivisorComponents

open ChartDivisorComponents in

theorem ChartDivisorComponents.proof (hNot : ChartSectionNotMem.Statement) : ChartDivisorComponents.Statement := by
  classical
  intro K _ _ ι _ P n m σ i A s hP hs
  have hPh : IsMultiHomogIdeal P := hP.2.1.2.1
  have hJdim : ∀ J ∈ segreChartComponents P σ i,
      ringKrullDim (MvPolynomial (Fin m) ℂ ⧸ J) = ((n + 1 : ℕ) : WithBot ℕ∞) :=
    SegreChartDim.proof K ι P (n + 1) m σ i hP
  have hWar : ∀ W, W ∈ divSupp P s ∧ IsHorizontal W → IsArithVar W (n + 1) :=
    fun W hW => (divSuppArith K ι P (n + 1) A s W hP hs hW.1).1 hW.2
  have hWdim : ∀ W, W ∈ divSupp P s ∧ IsHorizontal W → ∀ W'' ∈ segreChartComponents W σ i,
      ringKrullDim (MvPolynomial (Fin m) ℂ ⧸ W'') = (n : ℕ) :=
    fun W hW => SegreChartDim.proof K ι W n m σ i (hWar W hW)
  have hsW : ∀ W, W ∈ divSupp P s ∧ IsHorizontal W → ∀ W'' ∈ segreChartComponents W σ i,
      chartSection σ i s ∈ W'' := fun W hW W'' hW'' =>
    (mem_segreChartComponents.1 hW'').1.2 (chartSection_mem (hWar W hW).2.1.2.1 σ i
      (hW.1.1.1.2 (le_sup_right (a := P) (Ideal.mem_span_singleton_self s))))
  have hnot := hNot K ι P (n + 1) m σ i A s hP hs
  refine ⟨fun J hJ W' => ⟨fun hW' => ?_, fun ⟨hJW', W, hW, hW'c⟩ => ?_⟩, fun W₁ W₂ h₁ h₂ W' hW₁ hW₂ => ?_⟩
  · have hJp : J.IsPrime := (mem_segreChartComponents.1 hJ).1.1
    have hW'p : W'.IsPrime := hW'.1.1
    have hdim := SectionComponents.ringKrullDim_quotient_add_one_eq (hnot J hJ) hW'
    rw [hJdim J hJ] at hdim
    have hJW' : J ≤ W' := le_sup_left.trans hW'.1.2
    have hsW' : chartSection σ i s ∈ W' :=
      ((le_sup_right (a := J)).trans hW'.1.2) (Ideal.mem_span_singleton_self _)

    have key : ∃ W, (W ∈ divSupp P s ∧ IsHorizontal W) ∧ ∃ W'' ∈ segreChartComponents W σ i, W'' ≤ W' := by
      by_contra hcon
      push Not at hcon
      let g : Ideal (MRing ι) → Ideal (MvPolynomial (Fin m) ℂ) → MvPolynomial (Fin m) ℂ := fun W W'' =>
        if h : (W ∈ divSupp P s ∧ IsHorizontal W) ∧ W'' ∈ segreChartComponents W σ i then
          (SetLike.not_le_iff_exists.1 (hcon W h.1 W'' h.2)).choose else 1
      have hg : ∀ W W'', (W ∈ divSupp P s ∧ IsHorizontal W) → W'' ∈ segreChartComponents W σ i →
          g W W'' ∈ W'' ∧ g W W'' ∉ W' := fun W W'' hW hW'' => by
        simp only [g, dif_pos (And.intro hW hW'')]
        exact (SetLike.not_le_iff_exists.1 (hcon W hW W'' hW'')).choose_spec
      set T := (divSupp_finite P s).toFinset.filter IsHorizontal
      have hT : ∀ W, W ∈ T ↔ W ∈ divSupp P s ∧ IsHorizontal W := fun W => by simp [T]
      set G := ∏ W ∈ T, ∏ W'' ∈ segreChartComponents W σ i, g W W''
      apply (show G ∉ W' from fun hG => by
        rw [Ideal.IsPrime.prod_mem_iff] at hG
        obtain ⟨W, hWT, hG⟩ := hG
        rw [Ideal.IsPrime.prod_mem_iff] at hG
        obtain ⟨W'', hW'', hG⟩ := hG
        exact (hg W W'' ((hT W).1 hWT) hW'').2 hG)
      rw [← MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (K := ℂ) W', mem_vanishingIdeal_iff]
      intro x hx
      rw [mem_zeroLocus_iff] at hx
      change ∀ p ∈ W', eval x p = 0 at hx
      change eval x G = 0
      have hxS : x ∈ segreChartSet P σ i := mem_segreChartSet_of_forall hPh σ i fun f hf =>
        hx f (hJW' ((mem_segreChartComponents.1 hJ).1.2 hf))
      obtain ⟨W, hW, hxW⟩ := exists_divSupp_of_eval hPh σ i s hxS (hx _ hsW')
      have : (RingHom.ker (eval x)).IsPrime := RingHom.ker_isPrime _
      have hle : segreChartIdeal W σ i ≤ RingHom.ker (eval x) :=
        fun f hf => (mem_vanishingIdeal_iff.1 hf) x hxW
      obtain ⟨W'', hW''min, hW''x⟩ := Ideal.exists_minimalPrimes_le hle
      have hW'' : W'' ∈ segreChartComponents W σ i := mem_segreChartComponents.2 hW''min
      rw [map_prod]
      refine Finset.prod_eq_zero ((hT W).2 hW) ?_
      rw [map_prod]
      refine Finset.prod_eq_zero hW'' ?_
      exact hW''x (hg W W'' hW hW'').1
    obtain ⟨W, hW, W'', hW'', hW''le⟩ := key
    have hW''p : W''.IsPrime := (mem_segreChartComponents.1 hW'').1.1
    have heq : W'' = W' := by
      by_contra hne
      have h := SectionComponents.ringKrullDim_quotient_add_one_le_of_lt (lt_of_le_of_ne hW''le hne)
      rw [hWdim W hW W'' hW'', hdim] at h
      have h6 : n + 1 ≤ n := by exact_mod_cast h
      omega
    exact ⟨hJW', W, hW, heq ▸ hW''⟩
  · have hJp : J.IsPrime := (mem_segreChartComponents.1 hJ).1.1
    have : W'.IsPrime := (mem_segreChartComponents.1 hW'c).1.1
    have hle : J ⊔ Ideal.span {chartSection σ i s} ≤ W' :=
      sup_le hJW' ((Ideal.span_singleton_le_iff_mem _).2 (hsW W hW W' hW'c))
    obtain ⟨Q, hQ, hQW'⟩ := Ideal.exists_minimalPrimes_le hle
    have hQp : Q.IsPrime := hQ.1.1
    have hdim := SectionComponents.ringKrullDim_quotient_add_one_eq (hnot J hJ) hQ
    rw [hJdim J hJ] at hdim
    rwa [← eq_of_le_of_dim hQW' n hdim (hWdim W hW W' hW'c)]
  · exact le_antisymm
      (le_of_common hNot (hWar W₂ h₂) (hWar W₁ h₁).2.1.2.1 σ i hW₂ hW₁)
      (le_of_common hNot (hWar W₁ h₁) (hWar W₂ h₂).2.1.2.1 σ i hW₁ hW₂)

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveVertPointChart
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo CurveVerticalPointChart

noncomputable section

theorem CurveVertPointChart.proof (hF : CurveRingFinite.Statement) (hCP : CurveClosedPointChart.Statement) :
    CurveVertPointChart.Statement := by
  classical
  intro K _ ι _ Ω _ y s d hy hs hsP W hW c hc
  have hWp : W.IsPrime := hW.1.1.1
  have hPW : mCoordIdeal y ≤ W := le_sup_left.trans hW.1.1.2
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => ne_zero_of_X_notMem fun h => hc k (hPW h)

  have hv := IndefiniteRowSideFullHecke.HeightsSet.CurveDivVertical.full K ι (mCoordIdeal y) s d hy hs hsP W hW
  rw [IsHorizontal, ← Ne, Submodule.ne_bot_iff] at hv
  obtain ⟨n, hn, hn0⟩ := hv
  have hmax := chartPrimeB_isMaximal y (hF K ι Ω y hy) hPW hWp hc hyc hn0 (Ideal.mem_comap.mp hn)
  rw [curvePtIdeal_eq y hPW hWp hc hyc]
  have hmp : (chartPrimeB y c W hyc).IsPrime := hmax.isPrime

  have hrat : ∀ p : Σ k, ι k, y p / y ⟨p.1, c p.1⟩ ∈ locSub y _ hmp := by
    obtain ⟨c', hyc', h'⟩ := hCP K ι Ω y hy _ hmax
    have hinv : ∀ k, y ⟨k, c' k⟩ / y ⟨k, c k⟩ ∈ locSub y _ hmp := by
      intro k
      obtain ⟨a, b, hb, hab⟩ := h' ⟨k, c k⟩
      have hab0 : (b : Ω) * (y ⟨k, c k⟩ / y ⟨k, c' k⟩) = a := hab
      have hab' : (a : Ω) * y ⟨k, c' k⟩ = b * y ⟨k, c k⟩ := by
        rw [← hab0]
        field_simp [hyc' k]
      refine mem_locSub.mpr ⟨b, a, ?_, ?_⟩
      · intro ha
        obtain ⟨e, g, hg, hgW, he⟩ := mem_chartPrimeB.mp ha
        obtain ⟨f, w, hw, hbw⟩ := exists_rep y hyc (mem_chart y hyc b)
        apply hb
        refine mem_chartPrimeB.mpr ⟨f, w, hw, ?_, hbw⟩
        have h1 : X ⟨k, c k⟩ * (HilbertSamuel.SmallSectionsNonzero.chartMono c e * w) ∈ W := by
          refine mem_of_aeval_eq y hPW
            (Inter.AvoidRing.isMultiHomog_mul (Inter.AvoidRing.isMultiHomog_mul hg
              (Inter.AvoidRing.isMultiHomog_X k (c' k)))
              (HilbertSamuel.SmallSectionsNonzero.isMultiHomog_chartMono c f))
            (Inter.AvoidRing.isMultiHomog_mul (Inter.AvoidRing.isMultiHomog_X k (c k))
              (Inter.AvoidRing.isMultiHomog_mul
                (HilbertSamuel.SmallSectionsNonzero.isMultiHomog_chartMono c e) hw))
            (by abel) ?_ (W.mul_mem_right _ (W.mul_mem_right _ hgW))
          simp only [map_mul, aeval_X, HilbertSamuel.SmallSectionsNonzero.aeval_chartMono]
          linear_combination (-(y ⟨k, c' k⟩ * ∏ k, y ⟨k, c k⟩ ^ f k)) * he +
            (y ⟨k, c k⟩ * ∏ k, y ⟨k, c k⟩ ^ e k) * hbw +
            ((∏ k, y ⟨k, c k⟩ ^ e k) * ∏ k, y ⟨k, c k⟩ ^ f k) * hab'
        exact mem_of_chartMono_mul hWp hc ((hWp.mem_or_mem h1).resolve_left (hc k))
      · rw [← hab0]
        field_simp [hyc' k, hyc k]
    intro p
    obtain ⟨a, b, hb, hab⟩ := h' p
    have hu : y p / y ⟨p.1, c' p.1⟩ ∈ locSub y _ hmp := mem_locSub.mpr ⟨a, b, hb, hab⟩
    have hprod := mul_mem hu (hinv p.1)
    have he : y p / y ⟨p.1, c' p.1⟩ * (y ⟨p.1, c' p.1⟩ / y ⟨p.1, c p.1⟩) = y p / y ⟨p.1, c p.1⟩ := by
      field_simp [hyc' p.1, hyc p.1]
    rwa [he] at hprod
  have hY : ∀ e : K → ℕ, ∏ k, y ⟨k, c k⟩ ^ e k ≠ 0 := fun e =>
    Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hyc k)
  refine ⟨hmax, fun p => mem_locSub.mp (hrat p), fun e g hg => ⟨fun hgW => ?_, ?_⟩⟩
  · have hr : aeval y g * ∏ k, y ⟨k, c k⟩ ^ (-(e k : ℤ)) ∈ chartRingZ y c :=
      (HilbertSamuel.LiftBirationalAmple.mem_chartLat_one y).mp
        (HilbertSamuel.LiftBirationalAmple.chartLat_form hg) c hyc
    have hinv : ∏ k, y ⟨k, c k⟩ ^ (-(e k : ℤ)) = (∏ k, y ⟨k, c k⟩ ^ e k)⁻¹ := by
      rw [← Finset.prod_inv_distrib]
      exact Finset.prod_congr rfl fun k _ => by rw [zpow_neg, zpow_natCast]
    rw [hinv] at hr
    obtain ⟨a, b, hb, hab⟩ := mem_locSub.mp (chart_le_locSub y _ hmp c hrat hr)
    have hab' : (b : Ω) * aeval y g = a * ∏ k, y ⟨k, c k⟩ ^ e k := by
      rw [← hab]
      field_simp [hY e]
    refine ⟨a, b, ?_, hb, hab'⟩
    obtain ⟨f, w, hw, hbw⟩ := exists_rep y hyc (mem_chart y hyc b)
    refine mem_chartPrimeB.mpr ⟨f + e, w * g, Inter.AvoidRing.isMultiHomog_mul hw hg, W.mul_mem_left _ hgW, ?_⟩
    rw [prod_pow_add, map_mul]
    linear_combination (-(∏ k, y ⟨k, c k⟩ ^ f k)) * hab' + (aeval y g) * hbw
  · rintro ⟨a, b, ha, hb, hab⟩
    obtain ⟨f, v, hv, hvW, hav⟩ := mem_chartPrimeB.mp ha
    obtain ⟨f', w, hw, hbw⟩ := exists_rep y hyc (mem_chart y hyc b)
    have hwW : w ∉ W := fun h => hb (mem_chartPrimeB.mpr ⟨f', w, hw, h, hbw⟩)
    have h1 : HilbertSamuel.SmallSectionsNonzero.chartMono c f * (w * g) ∈ W := by
      refine mem_of_aeval_eq y hPW
        (Inter.AvoidRing.isMultiHomog_mul (Inter.AvoidRing.isMultiHomog_mul
          (HilbertSamuel.SmallSectionsNonzero.isMultiHomog_chartMono c e)
          (HilbertSamuel.SmallSectionsNonzero.isMultiHomog_chartMono c f')) hv)
        (Inter.AvoidRing.isMultiHomog_mul (HilbertSamuel.SmallSectionsNonzero.isMultiHomog_chartMono c f)
          (Inter.AvoidRing.isMultiHomog_mul hw hg))
        (by abel) ?_ (W.mul_mem_left _ hvW)
      simp only [map_mul, HilbertSamuel.SmallSectionsNonzero.aeval_chartMono]
      linear_combination (-((∏ k, y ⟨k, c k⟩ ^ e k) * ∏ k, y ⟨k, c k⟩ ^ f' k)) * hav +
        ((∏ k, y ⟨k, c k⟩ ^ f k) * aeval y g) * hbw -
        ((∏ k, y ⟨k, c k⟩ ^ f k) * ∏ k, y ⟨k, c k⟩ ^ f' k) * hab
    exact (hWp.mem_or_mem (mem_of_chartMono_mul hWp hc h1)).resolve_left hwW

end

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveVertPointMultChart
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace CurveVerticalPointMultiplicity

variable {K : Type} {ι : K → Type}

theorem aeval_mul_of_homog [Fintype K] [∀ k, Fintype (ι k)] {S : Type*} [CommRing S] [Algebra ℤ S] (r : (Σ k, ι k) → S) (t : K → S) {f : MRing ι}
    {d : K → ℕ} (hf : IsMultiHomog f d) :
    aeval (fun p => r p * t p.1) f = aeval r f * ∏ k, t k ^ d k := by
  classical
  rw [f.as_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [aeval_monomial, aeval_monomial, mul_assoc]
  congr 1
  rw [Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp)]
  simp_rw [mul_pow, Finset.prod_mul_distrib]
  congr 1
  rw [Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun k _ => ?_
  dsimp only
  rw [Finset.prod_pow_eq_pow_sum, hf m hm k]

theorem map_aeval_int {S T : Type*} [CommRing S] [CommRing T] [Algebra ℤ S] [Algebra ℤ T] (φ : S →+* T) (r : (Σ k, ι k) → S)
    (f : MRing ι) : φ (aeval r f) = aeval (fun p => φ (r p)) f := by
  induction f using MvPolynomial.induction_on with
  | C n => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

end CurveVerticalPointMultiplicity

open CurveVerticalPointMultiplicity GroundTheory.Heights₂.Heights.VerticalPointMultiplicityChart in

theorem CurveVertPointMultChart.proof (hCh : CurveVertPointChart.Statement)
    (hN : CurveVertPointNagata.Statement) : CurveVertPointMultChart.Statement := by
  classical
  intro K _ ι _ Ω _ y s d hP hs hsP W hW c hc a b hb hab
  obtain ⟨hmax, hrat, -⟩ := hCh K ι Ω y s d hP hs hsP W hW c hc
  have hWp : W.IsPrime := hW.1.1.1
  have hmp : (curvePtIdeal y W).IsPrime := hmax.isPrime
  choose a' b' hb' hab' using hrat
  obtain ⟨Φ, hsurj, hker, hΦ⟩ := hN K ι Ω y s d hP hs hsP W hW c hc a' b' hb' hab'
  have hPW : mCoordIdeal y ≤ W := le_sup_left.trans hW.1.1.2
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => ne_zero_of_X_notMem fun h => hc k (hPW h)

  have hunit : ∀ x : (curvePtIdeal y W).primeCompl, IsUnit ((curveRing y).subtype x) := fun x =>
    isUnit_iff_ne_zero.mpr fun h => x.2 (by
      rw [show (x : curveRing y) = 0 from Subtype.ext h]; exact zero_mem _)
  let e : Localization.AtPrime (curvePtIdeal y W) →+* Ω := IsLocalization.lift hunit
  have hinj : Function.Injective e := by
    rw [IsLocalization.lift_injective_iff]
    intro x z
    rw [(IsLocalization.injective (M := (curvePtIdeal y W).primeCompl)
      (Localization.AtPrime (curvePtIdeal y W)) (le_nonZeroDivisors_of_noZeroDivisors fun h =>
        h (zero_mem _))).eq_iff]
    exact Subtype.val_injective.eq_iff.symm
  have hbc : b ∈ (curvePtIdeal y W).primeCompl := hb
  let r : (Σ k, ι k) → Localization.AtPrime (curvePtIdeal y W) := fun p =>
    IsLocalization.mk' _ (a' p) (⟨b' p, hb' p⟩ : (curvePtIdeal y W).primeCompl)
  have her : ∀ p, e (r p) = y p / y ⟨p.1, c p.1⟩ := fun p =>
    (IsLocalization.lift_mk'_spec _ _ _ _).mpr (hab' p).symm
  have hsr : aeval r s = IsLocalization.mk' _ a (⟨b, hbc⟩ : (curvePtIdeal y W).primeCompl) := by
    apply hinj
    rw [map_aeval_int, funext her]
    have key : aeval y s = aeval (fun p => y p / y ⟨p.1, c p.1⟩) s * ∏ k, y ⟨k, c k⟩ ^ d k := by
      rw [← aeval_mul_of_homog _ (fun k => y ⟨k, c k⟩) hs]
      exact congrArg (fun v => aeval v s) (funext fun p => (div_mul_cancel₀ _ (hyc p.1)).symm)
    have hpc : ∏ k, y ⟨k, c k⟩ ^ d k ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hyc k)
    symm
    refine (IsLocalization.lift_mk'_spec _ _ _ _).mpr ?_
    change (a : Ω) = (b : Ω) * _
    apply mul_right_cancel₀ hpc
    rw [mul_assoc, ← key, hab]

  have hXk : ∀ k, (X k : MvPolynomial K (Localization.AtPrime (curvePtIdeal y W))) ∈
      ((IsLocalRing.maximalIdeal (Localization.AtPrime (curvePtIdeal y W))).map
        (MvPolynomial.C : _ →+* MvPolynomial K _)).primeCompl := fun k h => by
    have h1 := MvPolynomial.mem_map_C_iff.mp h (Finsupp.single k 1)
    rw [MvPolynomial.coeff_X, if_pos rfl] at h1
    exact (IsLocalRing.maximalIdeal _).ne_top_iff_one.mp (IsLocalRing.maximalIdeal.isMaximal _).ne_top h1
  have hprod : (∏ k, X k ^ d k : MvPolynomial K (Localization.AtPrime (curvePtIdeal y W))) ∈
      ((IsLocalRing.maximalIdeal (Localization.AtPrime (curvePtIdeal y W))).map
        (MvPolynomial.C : _ →+* MvPolynomial K _)).primeCompl :=
    Submonoid.prod_mem _ fun k _ => Submonoid.pow_mem _ (hXk k) _
  have hbu : IsUnit (IsLocalization.mk' (Localization.AtPrime (curvePtIdeal y W)) (1 : curveRing y)
      (⟨b, hbc⟩ : (curvePtIdeal y W).primeCompl)) :=
    isUnit_iff_exists_inv.mpr ⟨algebraMap _ _ b, (IsLocalization.mk'_spec _ _ _).trans (map_one _)⟩
  have hΦs : Φ (algebraMap _ _ s) =
      algebraMap (Localization.AtPrime (curvePtIdeal y W)) (mNagataRing K (Localization.AtPrime (curvePtIdeal y W)))
        (algebraMap (curveRing y) _ a) *
      (algebraMap (MvPolynomial K (Localization.AtPrime (curvePtIdeal y W)))
          (mNagataRing K (Localization.AtPrime (curvePtIdeal y W)))
          (MvPolynomial.C (IsLocalization.mk' (Localization.AtPrime (curvePtIdeal y W)) (1 : curveRing y)
            (⟨b, hbc⟩ : (curvePtIdeal y W).primeCompl))) *
        algebraMap (MvPolynomial K (Localization.AtPrime (curvePtIdeal y W)))
          (mNagataRing K (Localization.AtPrime (curvePtIdeal y W))) (∏ k, X k ^ d k)) := by
    rw [hΦ s, aeval_mul_of_homog (fun p => MvPolynomial.C (r p)) X hs, ← map_aeval_int MvPolynomial.C, hsr,
      IsLocalization.mk'_eq_mul_mk'_one, map_mul, map_mul, map_mul, ← mul_assoc,
      IsScalarTower.algebraMap_apply (Localization.AtPrime (curvePtIdeal y W))
        (MvPolynomial K (Localization.AtPrime (curvePtIdeal y W))) (mNagataRing K _), MvPolynomial.algebraMap_eq]
  have hv : IsUnit (algebraMap (MvPolynomial K (Localization.AtPrime (curvePtIdeal y W)))
          (mNagataRing K (Localization.AtPrime (curvePtIdeal y W)))
          (MvPolynomial.C (IsLocalization.mk' (Localization.AtPrime (curvePtIdeal y W)) (1 : curveRing y)
            (⟨b, hbc⟩ : (curvePtIdeal y W).primeCompl))) *
        algebraMap (MvPolynomial K (Localization.AtPrime (curvePtIdeal y W)))
          (mNagataRing K (Localization.AtPrime (curvePtIdeal y W))) (∏ k, X k ^ d k)) :=
    ((hbu.map MvPolynomial.C).map _).mul (IsLocalization.map_units _ ⟨_, hprod⟩)

  have hJ : ((mCoordIdeal y ⊔ Ideal.span {s}).map (algebraMap _ (Localization.AtPrime W))).map Φ =
      (Ideal.span {algebraMap (curveRing y) (Localization.AtPrime (curvePtIdeal y W)) a}).map
        (algebraMap _ (mNagataRing K (Localization.AtPrime (curvePtIdeal y W)))) := by
    rw [Ideal.map_sup, Ideal.map_sup, (Ideal.map_eq_bot_iff_le_ker _).mpr hker.ge, bot_sup_eq,
      Ideal.map_span, Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton,
      Set.image_singleton, hΦs, Ideal.span_singleton_mul_right_unit hv]

  have hmap : (IsLocalRing.maximalIdeal (Localization.AtPrime (curvePtIdeal y W))).map
      (algebraMap _ (mNagataRing K (Localization.AtPrime (curvePtIdeal y W)))) =
      IsLocalRing.maximalIdeal (mNagataRing K (Localization.AtPrime (curvePtIdeal y W))) := by
    rw [IsScalarTower.algebraMap_eq (Localization.AtPrime (curvePtIdeal y W))
      (MvPolynomial K (Localization.AtPrime (curvePtIdeal y W))) (mNagataRing K _), ← Ideal.map_map,
      MvPolynomial.algebraMap_eq, IsLocalization.AtPrime.map_eq_maximalIdeal]
  have : IsLocalHom (algebraMap (Localization.AtPrime (curvePtIdeal y W))
      (mNagataRing K (Localization.AtPrime (curvePtIdeal y W)))) := by
    refine ⟨fun x hx => ?_⟩
    by_contra hx'
    have h1 : x ∈ IsLocalRing.maximalIdeal _ := hx'
    have h2 := Ideal.mem_map_of_mem
      (algebraMap _ (mNagataRing K (Localization.AtPrime (curvePtIdeal y W)))) h1
    rw [hmap] at h2
    exact h2 hx
  have hfib : Module.length (mNagataRing K (Localization.AtPrime (curvePtIdeal y W)))
      (mNagataRing K (Localization.AtPrime (curvePtIdeal y W)) ⧸
        (IsLocalRing.maximalIdeal (Localization.AtPrime (curvePtIdeal y W))).map
          (algebraMap _ (mNagataRing K (Localization.AtPrime (curvePtIdeal y W))))) = 1 := by
    rw [hmap]
    have : IsSimpleModule (mNagataRing K (Localization.AtPrime (curvePtIdeal y W)))
        (mNagataRing K (Localization.AtPrime (curvePtIdeal y W)) ⧸
          IsLocalRing.maximalIdeal (mNagataRing K (Localization.AtPrime (curvePtIdeal y W)))) :=
      isSimpleModule_iff_quot_maximal.mpr ⟨_, inferInstance, ⟨LinearEquiv.refl _ _⟩⟩
    exact Module.length_eq_one _ _

  rw [multAt, dif_pos hWp, locLen, dif_pos hmp]
  congr 1
  rw [length_localizedModule_quotient, length_localizedModule_quotient,
    length_quotient_of_surjective Φ hsurj _ (hker.le.trans (Ideal.map_mono le_sup_left)), hJ,
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (mNagataRing K (Localization.AtPrime (curvePtIdeal y W)))
      (Ideal.span {algebraMap (curveRing y) (Localization.AtPrime (curvePtIdeal y W)) a})).toLinearEquiv.length_eq,
    IsLocalRing.length_baseChange, hfib, mul_one, Ideal.map_span, Set.image_singleton]

end

end GroundTheory.Heights₂.Heights.Targets
end

