import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0014
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0015
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PPFContracted
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
import GroundTheory.HeightsAndTheta.Heights.Intersections.ProjLineRankTwoPushforwardHypotheses
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ArithModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0016
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0011

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.BaseChange
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.AI.I1 GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver)

noncomputable section

universe u u' v w

namespace BaseChange

variable {F : Type*} [Field F] {F' : Type*} [Field F'] [Algebra F F'] {K : Type*} [Fintype K]
  {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem isProjVarF_of_mem_minimalPrimes {V : Ideal (MRingOver F ι)} {n : ℕ} (hV : IsProjVarF V n)
    {W : Ideal (MRingOver F' ι)}
    (hW : W ∈ (V.map (MvPolynomial.map (algebraMap F F'))).minimalPrimes) : IsProjVarF W n := by
  classical
  have := hV.1.1
  have hc := BaseChangeMin.comap_of_mem_minimalPrimes_map V W hW
  have hVo : NumbersDVR.IsMultiProjPrime V := (Objects.isMultiProjPrime_iff V).mpr hV.1
  have hJ : NumbersDVR.IsMultiHomogIdeal (V.map (MvPolynomial.map (algebraMap F F'))) :=
    FieldNumbers.isMultiHomogIdeal_map hVo.multiHomog
  have hWo : NumbersDVR.IsMultiProjPrime W := by
    refine ⟨hW.1.1, FieldNumbers.PFContracted.isMultiHomogIdeal_of_mem_minimalPrimes hJ hW, ?_⟩
    intro k
    obtain ⟨i, hi⟩ := hVo.relevant k
    refine ⟨i, fun hX => hi ?_⟩
    rw [← hc, Ideal.mem_comap, MvPolynomial.map_X]
    exact hX
  refine ⟨(Objects.isMultiProjPrime_iff W).mp hWo, ?_⟩
  rw [BaseChangeMin.ringKrullDim_of_mem_minimalPrimes_map V W hW]
  exact hV.2

end BaseChange

open BaseChange

theorem BaseChange.of_found (hN : IntNumIsFieldIntersection.Statement.{u})
    (hUq : FieldNumbers.IntNumUnique.Statement.{u}) (hBase : FieldNumbers.IntNumBase.Statement.{u})
    (hN' : IntNumIsFieldIntersection.Statement.{u'})
    (hUq' : FieldNumbers.IntNumUnique.Statement.{u'})
    (hBase' : FieldNumbers.IntNumBase.Statement.{u'})
    (hBC : FieldNumbers.IntNumBaseChange.Statement.{u, u'}) (hAs : IntNumAssoc.Statement.{u'})
    (F : Type u) (F' : Type u') [Field F] [Field F'] [Algebra F F'] {K : Type} [Fintype K]
    (ι : K → Type) [∀ k, Fintype (ι k)] : ReciprocityTheory.ChartRestriction.G.AI.I1.BaseChangeStatement F F' ι := by
  classical
  intro I I' hI hI' V n L hV
  have hEU := ExistsUnique.of_found hN hUq hBase F ι
  have hEU' := ExistsUnique.of_found hN' hUq' hBase' F' ι
  have := hV.1.1
  set J := V.map (MvPolynomial.map (algebraMap F F')) with hJdef
  have hmin : ∀ W ∈ J.minimalPrimes, IsProjVarF W n :=
    fun W hW => isProjVarF_of_mem_minimalPrimes hV hW
  have hVo : NumbersDVR.IsMultiProjPrime V := (Objects.isMultiProjPrime_iff V).mpr hV.1
  have hJ : NumbersDVR.IsMultiHomogIdeal J := FieldNumbers.isMultiHomogIdeal_map hVo.multiHomog
  have hdim : ringKrullDim (MRingOver F' ι ⧸ J) < ((n + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    refine lt_of_le_of_lt (BaseChangeMin.ringKrullDim_quotient_le_of_minimalPrimes _
      (N := ((n + Fintype.card K : ℕ) : WithBot ℕ∞)) fun Z hZ => (hmin Z hZ).2.le) ?_
    exact_mod_cast (show n + Fintype.card K < n + 1 + Fintype.card K by omega)
  rw [Numbers.agree_of_existsUnique hN hEU I hI V n L hV, ← (hBC.1 F F' K ι V).2 n L,
    hAs F' K ι n J hJ hdim L]
  unfold NumbersDVR.cycEval
  rw [finsum_mem_def]
  refine finsum_congr fun W => ?_
  unfold idealCycle
  by_cases hW : W ∈ J.minimalPrimes
  · have : W.IsPrime := hW.1.1
    have hWv := hmin W hW
    rw [dif_pos ⟨hW, (Objects.isMultiProjPrime_iff W).mpr hWv.1 |>.relevant⟩,
      Set.indicator_of_mem hW, Numbers.agree_of_existsUnique hN' hEU' I' hI' W n L hWv]
    simp only [ReciprocityTheory.ChartRestriction.G.Geo.multAt, dif_pos this]
    rfl
  · rw [dif_neg (fun h => hW h.1), Set.indicator_of_notMem hW]
    simp

theorem BaseChange.full (F : Type u) (F' : Type u') [Field F] [Field F'] [Algebra F F'] {K : Type}
    [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] : ReciprocityTheory.ChartRestriction.G.AI.I1.BaseChangeStatement F F' ι :=
  BaseChange.of_found IntNumIsFieldIntersection.full FieldNumbers.IntNumUnique.full
    FieldNumbers.IntNumBase.full IntNumIsFieldIntersection.full FieldNumbers.IntNumUnique.full
    FieldNumbers.IntNumBase.full FieldNumbers.IntNumBaseChange.full IntNumAssoc.full F F' ι

end

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.CoordFibreDeg
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

def CoordFibreDeg.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k', ι' k') → Ω) (d : ℕ) (G : GenFibre v (mCoordIdeal y))
    (i : ∀ k : FibreBlock κ, fibreIdx ι' κ k),
    IsBlockMap κ v → IsArithVar (mCoordIdeal y) d → IsArithVar (imageZ v (mCoordIdeal y)) d →
    IsChart (fibreIdeal κ G) i →
    ptDeg (fibreIdeal κ G) i = IntermediateField.relfinrank (blockFnField (y ∘ v)) (blockFnField y)

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.LelongChartLimit
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

def LelongChartLimit.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ)
    (L : Fin n → HermLine ι) (A : HermLine ι) (s : MRing ι) (g : ((Σ k, ι k) → ℂ) → ℝ)
    (i : (k : K) → ι k) (δ : ℝ),
    IsArithVar P (n + 2) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSectionOn P A s →
    IsDegZeroSmooth g → 0 < δ → (∀ z, ‖segre z i‖ < δ * ‖segre z‖ → g z = 0) →
    Tendsto (fun ε : ℝ =>
        ptsIntegral P
          (Fin.cons (fun z => Real.log (‖eval z (map (Int.castRingHom ℂ) s)‖ ^ 2 + ε * A.h z ^ 2) / 2)
            (pot L)) g)
      (𝓝[>] 0)
      (𝓝 (∑ᶠ (W) (_ : W ∈ divSupp P s ∧ IsHorizontal W),
          (multAt (P ⊔ Ideal.span {s}) W : ℝ) * ptsIntegral W (pot L) g))

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.LelongSectionLimit
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

def LelongSectionLimit.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ)
    (L : Fin n → HermLine ι) (A B : HermLine ι) (s : MRing ι),
    IsArithVar P (n + 2) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSmoothHerm B →
    B.a = 0 → IsSectionOn P A s →
    Tendsto (fun ε : ℝ =>
        ptsIntegral P
          (Fin.cons (fun z => Real.log (‖eval z (map (Int.castRingHom ℂ) s)‖ ^ 2 + ε * A.h z ^ 2) / 2)
            (pot L))
          (fun z => Real.log (B.h z)))
      (𝓝[>] 0)
      (𝓝 (∑ᶠ (W) (_ : W ∈ divSupp P s ∧ IsHorizontal W),
          (multAt (P ⊔ Ideal.span {s}) W : ℝ) * ptsIntegral W (pot L) (fun z => Real.log (B.h z))))

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.MoriwakiBig
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

theorem MoriwakiBig.of_found (hG6 : HilbertSamuel.ArithmeticVolumeBig.Statement) (hC : MoriwakiBigCurve.Statement) :
    ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiBigStatement := by
  intro K _ ι _ Ω _ y D A P0 II hII har hb hP0 hs hc hnef hgen
  rcases Nat.eq_zero_or_pos D with rfl | hD
  · exact hC K ι Ω y A P0 II hII har hb hP0 hs hc hnef hgen
  · exact hG6 K ι Ω y D A P0 II hD hII har hb hP0 hs hnef hc

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.MoriwakiHS
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology

noncomputable section

theorem tendsto_div_of_bounds {h c : ℕ → ℝ} {T : ℝ} (hc : ∀ᶠ n in atTop, 0 < c n)
    (hlo : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, (T - ε) * c n ≤ h n)
    (hup : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, h n ≤ (T + ε) * c n) :
    Tendsto (fun n => h n / c n) atTop (𝓝 T) := by
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · filter_upwards [hc, hlo ((T - a) / 2) (by linarith)] with n hcn hn
    rw [lt_div_iff₀ hcn]
    have := mul_lt_mul_of_pos_right (show a < T - (T - a) / 2 by linarith) hcn
    linarith
  · filter_upwards [hc, hup ((a - T) / 2) (by linarith)] with n hcn hn
    rw [div_lt_iff₀ hcn]
    have := mul_lt_mul_of_pos_right (show T + (a - T) / 2 < a by linarith) hcn
    linarith

theorem eventually_pos_normaliser (D : ℕ) :
    ∀ᶠ n : ℕ in atTop, (0 : ℝ) < (n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ) := by
  filter_upwards [eventually_ge_atTop 1] with n hn
  have : (0 : ℝ) < n := by exact_mod_cast hn
  positivity

theorem MoriwakiHS.of_found (hL : NefCountLower.Statement) (hU : NefCountUpper.Statement) :
    ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiHSStatement := by
  intro K _ ι _ Ω _ y D A P0 II hII har hb hP0 hs hc hnef hgen hht
  exact tendsto_div_of_bounds (h := smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a))
    (c := fun n : ℕ => (n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) (eventually_pos_normaliser D)
    (hL K ι Ω y D A P0 II hII har hb hP0 hs hc hnef hgen hht)
    (hU K ι Ω y D A P0 II hII har hb hP0 hs hc hnef hgen hht)

end

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreCoordGoodProj
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo

namespace SegreCoordGoodProj

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem exists_monic_coeff_zero_ne {A R : Type*} [CommRing A] [Nontrivial A] [CommRing R] [IsDomain R]
    (f : A →+* R) {x : R} (hx : x ≠ 0) (h : f.IsIntegralElem x) :
    ∃ p : Polynomial A, p.Monic ∧ p.eval₂ f x = 0 ∧ p.coeff 0 ≠ 0 := by
  obtain ⟨p, hpm, hp⟩ := h
  induction hn : p.natDegree using Nat.strong_induction_on generalizing p with
  | _ n ih =>
    by_cases h0 : p.coeff 0 = 0
    · obtain ⟨q, rfl⟩ := Polynomial.X_dvd_iff.mpr h0
      have hqm : q.Monic := Polynomial.Monic.of_mul_monic_left Polynomial.monic_X hpm
      have hq : q.eval₂ f x = 0 := by
        rw [Polynomial.eval₂_mul, Polynomial.eval₂_X] at hp
        exact (mul_eq_zero.mp hp).resolve_left hx
      refine ih q.natDegree ?_ q hqm hq rfl
      rw [← hn, Polynomial.Monic.natDegree_mul Polynomial.monic_X hqm, Polynomial.natDegree_X]
      omega
    · exact ⟨p, hpm, hp, h0⟩

theorem evQ_segQ (P : Ideal (MRing ι)) (z : (Σ k, ι k) → ℂ) (hz : z ∈ mcPts P) (t : (k : K) → ι k) :
    evQ P z hz (segQ P t) = segre z t := by
  rw [segQ, evQ_mk, segMon, eval₂_prod]
  simp [segre]

omit [∀ k, Fintype (ι k)] in
theorem segre_scaleBlock (k0 : K) (c : ℂ) (z : (Σ k, ι k) → ℂ) (t : (k : K) → ι k) :
    segre (scaleBlock k0 c z) t = c * segre z t := by
  simp only [segre, scaleBlock, Finset.prod_mul_distrib]
  congr 1
  simp

theorem evQ_forms (P : Ideal (MRing ι)) (z : (Σ k, ι k) → ℂ) (hz : z ∈ mcPts P) {r : ℕ}
    (L : Fin r → ((k : K) → ι k) → ℚ) (j : Fin r) :
    evQ P z hz (forms (segQ P) L j) = ∑ t, (L j t : ℂ) * segre z t := by
  simp only [forms, map_sum, map_rat_smul, evQ_segQ, Rat.smul_def]

omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] in
theorem evQ_aeval (P : Ideal (MRing ι)) (z : (Σ k, ι k) → ℂ) (hz : z ∈ mcPts P) {r : ℕ}
    (ℓ : Fin r → MvPolynomial (Σ k, ι k) ℚ ⧸ qIdeal P) (F : MvPolynomial (Fin r) ℚ) :
    evQ P z hz (aeval ℓ F) = aeval (fun j => evQ P z hz (ℓ j)) F := by
  induction F using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p j hp => simp [hp]

theorem false_of_forms_vanish (P : Ideal (MRing ι)) (hhom : IsMultiHomogIdeal P) (k0 : K) {r : ℕ}
    (L : Fin r → ((k : K) → ι k) → ℚ) (hL : ∀ t, IntOver ℚ (forms (segQ P) L) (segQ P t))
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) (hV : ∀ j, ∑ t, (L j t : ℂ) * segre z t = 0) : False := by
  choose i1 hi1 using hz.1
  have hs : segre z i1 ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hi1 k
  obtain ⟨p, hpm, hp⟩ := hL i1
  let g0 : MvPolynomial (Fin r) ℚ →+* ℂ := eval₂Hom (algebraMap ℚ ℂ) 0
  have key : ∀ c : ℂ, c ≠ 0 → Polynomial.eval (c * segre z i1) (p.map g0) = 0 := by
    intro c hc
    have hzc := scaleBlock_mem_zeroLocus P hhom k0 hc hz
    have hcomp : (evQ P _ hzc).comp
        ((aeval (forms (segQ P) L) : MvPolynomial (Fin r) ℚ →ₐ[ℚ] _) : MvPolynomial (Fin r) ℚ →+* _) =
        g0 := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp [g0]
      · intro j
        have h1 : ∑ t, (L j t : ℂ) * (c * segre z t) = c * ∑ t, (L j t : ℂ) * segre z t := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun t _ => by ring
        simp [g0, evQ_forms, segre_scaleBlock, h1, hV j]
    have := congrArg (evQ P _ hzc) hp
    rw [Polynomial.hom_eval₂, hcomp, evQ_segQ, segre_scaleBlock, map_zero] at this
    rw [Polynomial.eval_map]
    exact this
  have hinf : {x : ℂ | (p.map g0).IsRoot x}.Infinite := by
    refine Set.Infinite.mono ?_ (Set.finite_singleton (0 : ℂ)).infinite_compl
    intro x hx
    have hx0 : x ≠ 0 := hx
    have := key (x / segre z i1) (div_ne_zero hx0 hs)
    rw [div_mul_cancel₀ x hs] at this
    exact this
  exact (hpm.map g0).ne_zero (Polynomial.eq_zero_of_infinite_isRoot _ hinf)

end SegreCoordGoodProj

theorem SegreCoordGoodProj.proof : SegreCoordGoodProj.Statement := by
  intro K _ ι _ P e i hP ⟨z0, hz0, hz0i⟩
  classical
  obtain ⟨r, hr, L, hL⟩ := exists_linear_normalization (k := ℚ) (segQ P) (e + 1)
    (fun r L hr => forms_not_algebraicIndependent P e hP hr L)
  obtain ⟨⟨k0⟩, ⟨hprime, hhom, -⟩, hH, -⟩ := hP
  have := isDomain_qQuot P hprime hH
  cases r with
  | zero => exact (SegreCoordGoodProj.false_of_forms_vanish P hhom k0 L hL hz0 fun j => j.elim0).elim
  | succ r' =>
  have hw : segQ P i ≠ 0 := fun h =>
    hz0i (by rw [← SegreCoordGoodProj.evQ_segQ P z0 hz0, h, map_zero])
  obtain ⟨p, hpm, hp, hc0⟩ := SegreCoordGoodProj.exists_monic_coeff_zero_ne _ hw (hL i)
  set c0 := p.coeff 0 with hc0def
  have hsupp : ∀ m ∈ (homogeneousComponent c0.totalDegree c0).support,
      Finsupp.degree m = c0.totalDegree := by
    intro m hm
    rw [mem_support_iff, coeff_homogeneousComponent] at hm
    by_contra hne
    exact hm (if_neg hne)
  obtain ⟨lam, hlam⟩ := exists_eval_cons_one_ne_zero _ _ hsupp
    (homogeneousComponent_totalDegree_ne_zero hc0)
  let Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ) :=
    { toFun := fun w j => Fin.cases (w i) (fun j' : Fin e => if h : (j' : ℕ) < r' then
          ∑ t, ((L (Fin.succ ⟨j', h⟩) t - lam ⟨j', h⟩ * L 0 t : ℚ) : ℂ) * w t else 0) j
      map_add' := by
        intro w w'
        funext j
        refine Fin.cases ?_ (fun j' => ?_) j
        · simp
        · simp only [Fin.cases_succ, Pi.add_apply]
          split_ifs <;> simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c w
        funext j
        refine Fin.cases ?_ (fun j' => ?_) j
        · simp
        · simp only [Fin.cases_succ, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
          split_ifs <;> simp [Finset.mul_sum, mul_left_comm] }
  refine ⟨Ψ, fun z hz hΨ => ?_, fun w => rfl⟩
  set V : Fin (r' + 1) → ℂ := fun j => ∑ t, (L j t : ℂ) * segre z t with hVdef
  have hzi : segre z i = 0 := congrFun hΨ 0
  have hVs : ∀ j : Fin r', V j.succ = lam j * V 0 := by
    intro j
    have h := congrFun hΨ (Fin.succ ⟨j, by omega⟩)
    simp only [Ψ, LinearMap.coe_mk, AddHom.coe_mk, Fin.cases_succ, dif_pos j.2, Fin.eta,
      Pi.zero_apply] at h
    simp only [hVdef]
    rw [← sub_eq_zero, Finset.mul_sum, ← Finset.sum_sub_distrib, ← h]
    refine Finset.sum_congr rfl fun t _ => ?_
    push_cast
    ring
  by_cases hs : V 0 = 0
  · refine SegreCoordGoodProj.false_of_forms_vanish P hhom k0 L hL hz fun j => ?_
    refine Fin.cases hs (fun j => ?_) j
    exact (hVs j).trans (by rw [hs, mul_zero])
  let g : Polynomial ℂ := (subst lam c0).map
    ((aeval (0 : Fin r' → ℂ) : MvPolynomial (Fin r') ℚ →ₐ[ℚ] ℂ) : MvPolynomial (Fin r') ℚ →+* ℂ)
  have hgD : g.coeff c0.totalDegree ≠ 0 := by
    simp only [g, Polynomial.coeff_map, subst_coeff_totalDegree]
    simpa using hlam
  have hroot : ∀ x : ℂ, x ≠ 0 → g.eval x = 0 := by
    intro x hx
    have hc : x / V 0 ≠ 0 := div_ne_zero hx hs
    have hzc := scaleBlock_mem_zeroLocus P hhom k0 hc hz
    set u : Fin (r' + 1) → ℂ := fun j => x / V 0 * V j with hudef
    have hu0 : u 0 = x := div_mul_cancel₀ x hs
    have hu' : (fun j : Fin r' => u j.succ - lam j • u 0) = 0 := by
      funext j
      simp only [hudef, hVs j, Rat.smul_def, Pi.zero_apply]
      ring
    have h1 : aeval u c0 = 0 := by
      have := congrArg (evQ P _ hzc) hp
      rw [Polynomial.hom_eval₂, SegreCoordGoodProj.evQ_segQ, SegreCoordGoodProj.segre_scaleBlock, hzi,
        mul_zero, Polynomial.eval₂_at_zero, map_zero, RingHom.comp_apply] at this
      rw [← this, AlgHom.coe_toRingHom, SegreCoordGoodProj.evQ_aeval]
      refine congrArg (fun v => aeval v c0) (funext fun j => ?_)
      rw [SegreCoordGoodProj.evQ_forms]
      simp only [SegreCoordGoodProj.segre_scaleBlock, hudef, hVdef, Finset.mul_sum]
      exact Finset.sum_congr rfl fun t _ => by ring
    have h2 := eval₂_subst lam u c0
    rw [hu', hu0, h1] at h2
    rw [Polynomial.eval_map]
    exact h2
  have hg0 : g = 0 := Polynomial.eq_zero_of_infinite_isRoot g
    (Set.Infinite.mono (fun x hx => hroot x hx) (Set.finite_singleton (0 : ℂ)).infinite_compl)
  exact hgD (by rw [hg0, Polynomial.coeff_zero])

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PoincareLelongLimit
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

def PoincareLelongLimit.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ)
    (L : Fin n → HermLine ι) (A B : HermLine ι) (s : MRing ι),
    IsArithVar P (n + 2) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSmoothHerm B →
    B.a = 0 → IsSectionOn P A s →
    Tendsto (fun ε => ptsIntegral P (Fin.cons (regLog A s ε) (pot L)) (fun z => Real.log (B.h z)))
      (𝓝[>] 0)
      (𝓝 ((∑ᶠ (W) (_ : W ∈ divSupp P s ∧ IsHorizontal W),
          (multAt (P ⊔ Ideal.span {s}) W : ℝ) * ptsIntegral W (pot L) (fun z => Real.log (B.h z))) -
        ptsIntegral P (Fin.cons (fun z => Real.log (A.h z)) (pot L)) (fun z => Real.log (B.h z))))

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PoincareLelongRegularised
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

def PoincareLelongRegularised.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ)
    (L : Fin n → HermLine ι) (A B : HermLine ι) (s : MRing ι),
    IsArithVar P (n + 2) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSmoothHerm B →
    B.a = 0 → IsSectionOn P A s →
    Tendsto (fun ε => ptsIntegral P (Fin.cons (fun z => Real.log (B.h z)) (pot L)) (regLog A s ε))
      (𝓝[>] 0) (𝓝 (ptsIntegral P (Fin.cons (fun z => Real.log (B.h z)) (pot L)) (logNorm A s)))

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StPtsIntegralProjIndep
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar IsGoodProj ptsIntegralAt pot PBlk oneLine
  isSmoothHerm_oneLine)

def PtsIntegralProjIndep.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (Ψ Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (L : Fin e → HermLine ι)
    (g : ((Σ k, ι k) → ℂ) → ℝ),
    IsArithVar P (e + 1) → IsGoodProj P Ψ → IsGoodProj P Ψ' → (∀ j, IsSmoothHerm (L j)) →
    IsDegZeroSmooth g → ptsIntegralAt P Ψ (pot L) g = ptsIntegralAt P Ψ' (pot L) g

end GroundTheory.Heights₂.Heights
end
end

