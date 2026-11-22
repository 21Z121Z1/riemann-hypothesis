import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0018
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0021
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0017
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0009
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0017
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0036
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0033
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0034
import GroundTheory.HeightsAndTheta.Heights.Intersections.PullBad

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PConsequences
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

omit [∀ k, Fintype (ι k)] in

theorem ptsIntegral_congr_pts (P : Ideal (MRing ι)) {e : ℕ} (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    {g g' : ((Σ k, ι k) → ℂ) → ℝ} (hg : ∀ z ∈ mcPts P, g z = g' z) :
    ptsIntegral P φ g = ptsIntegral P φ g' := by
  unfold ptsIntegral ptsIntegralAt
  split_ifs with hΨ
  · congr 1
    funext y
    refine finsum_congr fun w ↦ finsum_congr fun _ ↦ ?_
    unfold sheetDensity
    split_ifs with hγ
    · congr 1
      exact hg _ hγ.choose_spec.2.self_of_nhds.2.1
    · rfl
  · rfl

theorem cycR_sub_vertR (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (P : Ideal (MRing ι))
    {n : ℕ} (L : Fin n → HermLine ι) (s : MRing ι) [DecidablePred (IsHorizontal (ι := ι))] :
    cycR I P L s - vertR P L s = ∑ W ∈ (divSupp_finite P s).toFinset.filter IsHorizontal,
      (multAt (P ⊔ Ideal.span {s}) W : ℝ) * I W n L := by
  unfold cycR vertR
  rw [finsum_mem_eq_finite_toFinset_sum _ (divSupp_finite P s),
    finsum_mem_eq_finite_toFinset_sum _ (divSupp_finite P s), ← Finset.sum_sub_distrib, Finset.sum_filter]
  refine Finset.sum_congr rfl fun W _ ↦ ?_
  split_ifs <;> ring

theorem tensor_sqMetric_a {A : HermLine ι} {α β : K → ℕ} (h : ∀ k, (α k : ℤ) - β k = A.a k) (k : K) :
    (A.tensor (HermLine.sqMetric β)).a k = α k := by
  show A.a k + (β k : ℤ) = α k
  rw [← h k]
  ring

theorem ArithmeticIntersectionSecond.proof : ArithmeticIntersectionSecond.Statement := metricChange

theorem Conservation.proof : Conservation.Statement := Conservation.statement_holds

theorem InductiveIntersectionFormula.proof : InductiveIntersectionFormula.Statement := by
  classical
  intro K _ ι _ I hI P n L A f g hP hL hA ⟨α, β, hf, hg, hfP, hgP, hαβ⟩ hhor hmult hnorm
  obtain ⟨-, hAdd, hR⟩ := hI
  have hB : IsSmoothHerm (HermLine.sqMetric (ι := ι) β) := isSmoothHerm_sqMetric β
  have hRf := hR P n L _ f α hP hL (isSmoothHerm_tensor hA hB) (tensor_sqMetric_a hαβ) hf hfP
  have hRg := hR P n L _ g β hP hL hB (fun k ↦ rfl) hg hgP
  have hsum := hAdd P n L A _ hP hL hA hB
  have hint : arInt P f (A.tensor (HermLine.sqMetric β)) L = arInt P g (HermLine.sqMetric β) L := by
    unfold arInt
    refine ptsIntegral_congr_pts P _ fun z hz ↦ ?_
    have hApos := A.pos z hz.1
    show Real.log (‖eval z (map (Int.castRingHom ℂ) f)‖ / (A.h z * (HermLine.sqMetric β).h z)) =
      Real.log (‖eval z (map (Int.castRingHom ℂ) g)‖ / (HermLine.sqMetric β).h z)
    rw [hnorm z hz, mul_comm (A.h z), mul_div_mul_right _ _ hApos.ne']
  have hS : (divSupp_finite P f).toFinset.filter IsHorizontal =
      (divSupp_finite P g).toFinset.filter IsHorizontal := by
    ext W
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨fun h ↦ ⟨(hhor W h.2).1 h.1, h.2⟩, fun h ↦ ⟨(hhor W h.2).2 h.1, h.2⟩⟩
  have hcyc : cycR I P L f - vertR P L f = cycR I P L g - vertR P L g := by
    rw [cycR_sub_vertR, cycR_sub_vertR, hS]
    refine Finset.sum_congr rfl fun W hW ↦ ?_
    rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hW
    rw [hmult W hW.2 ((hhor W hW.2).2 hW.1)]
  rw [recR_eq] at hRf hRg
  linarith

theorem ArithmeticIntersectionFifth.proof (h₀ : ArithVarZeroStatement) : ArithmeticIntersectionFifth.Statement := by
  intro K _ ι _ I hI P A s hP hA ⟨a, ha, hs, hsP⟩
  have hR := hI.2.2 P 0 Fin.elim0 A s a hP (fun j ↦ j.elim0) hA ha hs hsP
  have hsnoc : (Fin.snoc (Fin.elim0 : Fin 0 → HermLine ι) A : Fin (0 + 1) → HermLine ι) = ![A] := by
    funext j
    fin_cases j
    rfl
  rw [hsnoc] at hR
  rw [hR, recR_eq]
  congr 1
  unfold cycR vertR
  refine finsum_mem_congr rfl fun W hW ↦ ?_
  have hnh : ¬ IsHorizontal W := fun hh ↦
    h₀ K ι W ((divSuppArith K ι P 0 A s W hP ⟨a, ha, hs, hsP⟩ hW).1 hh)
  rw [if_neg hnh, if_neg hnh]

theorem ae_eval_ne_zero {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)} {e : ℕ} {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) {h : MRing ι} (hh : ∃ a, IsMultiHomog h a)
    (hhP : h ∉ P) :
    ∀ᵐ y : Fin e → ℂ, ∀ z ∈ mcPts P, Ψ (segre z) = Fin.cons 1 y →
      eval z (map (Int.castRingHom ℂ) h) ≠ 0 := by
  have hJ : IsMultiHomogIdeal (Ideal.span {h} : Ideal (MRing ι)) :=
    ⟨{h}, fun f hf ↦ by rw [Set.mem_singleton_iff.mp hf]; exact hh, rfl⟩
  have hJP : ¬ (Ideal.span {h} : Ideal (MRing ι)) ≤ P := by
    rwa [Ideal.span_singleton_le_iff_mem]
  have hnull := projB_null Ψ hP hΨ hJ hJP
  refine ae_iff.mpr (measure_mono_null (fun y hy ↦ ?_) hnull)
  simp only [Set.mem_ofPred_eq, not_forall, not_not] at hy
  obtain ⟨z, hz, hzy, hz0⟩ := hy
  refine ⟨z, hz, ⟨hz.1, fun q hq ↦ ?_⟩, hzy⟩
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hq
  simp [hz0]

theorem RatR.proof (hInt : PtsIntegrableStatement) : RatR.Statement := by
  intro K _ ι _ I hI P n L A f g hP hL hA ⟨α, β, hf, hg, hfP, hgP, hαβ⟩
  obtain ⟨-, hAdd, hR⟩ := hI
  have hB : IsSmoothHerm (HermLine.sqMetric (ι := ι) β) := isSmoothHerm_sqMetric β
  have hAB := isSmoothHerm_tensor hA hB
  have hRf := hR P n L _ f α hP hL hAB (tensor_sqMetric_a hαβ) hf hfP
  have hRg := hR P n L _ g β hP hL hB (fun k ↦ rfl) hg hgP
  have hsum := hAdd P n L A _ hP hL hA hB
  have hint : arInt P f (A.tensor (HermLine.sqMetric β)) L - arInt P g (HermLine.sqMetric β) L =
      ptsIntegral P (pot L) (logNormRat A f g) := by
    show ptsIntegral P (pot L) _ - ptsIntegral P (pot L) _ = _
    unfold ptsIntegral
    split_ifs with hΨ
    · have hΨg : IsGoodProj P hΨ.choose := hΨ.choose_spec
      unfold ptsIntegralAt
      rw [← integral_sub (hInt K ι P n _ L _ f hP hΨg hL hAB ⟨α, tensor_sqMetric_a hαβ, hf, hfP⟩)
        (hInt K ι P n _ L _ g hP hΨg hL hB ⟨β, fun k ↦ rfl, hg, hgP⟩)]
      refine integral_congr_ae ?_
      filter_upwards [ae_eval_ne_zero hP hΨg ⟨α, hf⟩ hfP, ae_eval_ne_zero hP hΨg ⟨β, hg⟩ hgP]
        with y hyf hyg
      rw [← finsum_mem_sub_distrib _ _ (fibreFinite K ι P n _ hP hΨg y)]
      refine finsum_mem_congr rfl fun w _ ↦ ?_
      unfold sheetDensity
      split_ifs with hγ
      · have hs := hγ.choose_spec.2.self_of_nhds
        set z := hγ.choose y
        have hz : z ∈ mcPts P := hs.2.1
        have hf0 := norm_pos_iff.mpr (hyf z hz hs.2.2)
        have hg0 := norm_pos_iff.mpr (hyg z hz hs.2.2)
        have hA0 := A.pos z hz.1
        have hB0 := (HermLine.sqMetric (ι := ι) β).pos z hz.1
        rw [← sub_mul]
        congr 1
        show Real.log (‖eval z (map (Int.castRingHom ℂ) f)‖ / (A.h z * (HermLine.sqMetric β).h z)) -
          Real.log (‖eval z (map (Int.castRingHom ℂ) g)‖ / (HermLine.sqMetric β).h z) =
          Real.log (‖eval z (map (Int.castRingHom ℂ) f)‖ / ‖eval z (map (Int.castRingHom ℂ) g)‖ / A.h z)
        rw [Real.log_div hf0.ne' (mul_pos hA0 hB0).ne', Real.log_mul hA0.ne' hB0.ne',
          Real.log_div hg0.ne' hB0.ne', Real.log_div (div_pos hf0 hg0).ne' hA0.ne',
          Real.log_div hf0.ne' hg0.ne']
        ring
      · simp
    · simp
  unfold recRRat
  rw [recR_eq] at hRf hRg
  show I P (n + 1) (Fin.snoc L A) = cycR I P L f - cycR I P L g - ptsIntegral P (pot L) (logNormRat A f g)
  rw [← hint]
  linarith

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PPFHoriz
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

namespace PFHoriz

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
  {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {P' : Ideal (MRing ι')}

def genMap (G : GenFibre v P') : MRing ι ⧸ imageZ v P' →+* G.Φ :=
  Ideal.Quotient.lift _ (aeval G.x : MRing ι →ₐ[ℤ] G.Φ).toRingHom
    (fun a ha => by rw [← G.ker_x] at ha; exact RingHom.mem_ker.mp ha)

theorem genMap_mk (G : GenFibre v P') (f : MRing ι) :
    genMap G (Ideal.Quotient.mk _ f) = aeval G.x f := rfl

theorem genMap_injective (G : GenFibre v P') : Function.Injective (genMap G) := by
  refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [genMap_mk] at ha
  rw [Ideal.Quotient.eq_zero_iff_mem, ← G.ker_x]
  exact RingHom.mem_ker.mpr ha

theorem isFractionRing_genMap (G : GenFibre v P') :
    @IsFractionRing (MRing ι ⧸ imageZ v P') _ G.Φ _ (genMap G).toAlgebra := by
  letI := (genMap G).toAlgebra
  haveI : FaithfulSMul (MRing ι ⧸ imageZ v P') G.Φ :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (genMap_injective G)
  refine IsFractionRing.of_field _ _ fun z => ?_
  obtain ⟨f, g, -, rfl⟩ := G.gen z
  exact ⟨Ideal.Quotient.mk _ f, Ideal.Quotient.mk _ g, rfl⟩

def quotIncl (W : Ideal (MRing ι')) [W.IsPrime] (hW : imageZ v W = imageZ v P') :
    MRing ι ⧸ imageZ v P' →+* FractionRing (MRing ι' ⧸ W) :=
  (algebraMap (MRing ι' ⧸ W) (FractionRing (MRing ι' ⧸ W))).comp
    (Ideal.quotientMap W (rename v : MRing ι →ₐ[ℤ] MRing ι').toRingHom hW.symm.le)

theorem quotIncl_injective (W : Ideal (MRing ι')) [W.IsPrime] (hW : imageZ v W = imageZ v P') :
    Function.Injective (quotIncl W hW) :=
  (IsFractionRing.injective (MRing ι' ⧸ W) (FractionRing (MRing ι' ⧸ W))).comp
    (Ideal.quotientMap_injective' (H := hW.symm.le) hW.le)

def genAlg (G : GenFibre v P') (W : Ideal (MRing ι')) [W.IsPrime] (hW : imageZ v W = imageZ v P') :
    G.Φ →+* FractionRing (MRing ι' ⧸ W) :=
  letI := (genMap G).toAlgebra
  haveI := isFractionRing_genMap G
  IsFractionRing.lift (quotIncl_injective W hW)

theorem genAlg_alt (G : GenFibre v P') (W : Ideal (MRing ι')) [W.IsPrime] (hW : imageZ v W = imageZ v P')
    (p : Σ k, ι k) :
    genAlg G W hW (G.x p) =
      algebraMap (MRing ι' ⧸ W) (FractionRing (MRing ι' ⧸ W)) (Ideal.Quotient.mk W (X (v p))) := by
  letI := (genMap G).toAlgebra
  haveI := isFractionRing_genMap G
  have hx : G.x p = algebraMap (MRing ι ⧸ imageZ v P') G.Φ (Ideal.Quotient.mk _ (X p)) := by
    show G.x p = genMap G (Ideal.Quotient.mk _ (X p))
    rw [genMap_mk, aeval_X]
  rw [hx]
  exact (IsFractionRing.lift_algebraMap (quotIncl_injective W hW) _).trans (by
    simp [quotIncl, Ideal.quotientMap_mk])

def xW (W : Ideal (MRing ι')) [W.IsPrime] (q : Σ k', ι' k') : FractionRing (MRing ι' ⧸ W) :=
  algebraMap (MRing ι' ⧸ W) (FractionRing (MRing ι' ⧸ W)) (Ideal.Quotient.mk W (X q))

theorem aeval_xW (W : Ideal (MRing ι')) [W.IsPrime] (f : MRing ι') :
    aeval (R := ℤ) (xW W) f =
      algebraMap (MRing ι' ⧸ W) (FractionRing (MRing ι' ⧸ W)) (Ideal.Quotient.mk W f) := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    rw [aeval_C, eq_intCast (algebraMap ℤ (FractionRing (MRing ι' ⧸ W))) a]
    exact (eq_intCast (((algebraMap (MRing ι' ⧸ W) (FractionRing (MRing ι' ⧸ W))).comp
      (Ideal.Quotient.mk W)).comp C) a).symm
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | mul_X p n hp => rw [map_mul, map_mul, map_mul, hp, aeval_X, xW]

theorem ker_aeval_xW (W : Ideal (MRing ι')) [W.IsPrime] :
    RingHom.ker (aeval (R := ℤ) (xW W)) = W := by
  ext f
  rw [RingHom.mem_ker, aeval_xW, map_eq_zero_iff _ (IsFractionRing.injective _ _),
    Ideal.Quotient.eq_zero_iff_mem]

def genFibreOf (G : GenFibre v P') (W : Ideal (MRing ι')) [W.IsPrime] (hW : imageZ v W = imageZ v P') :
    GenFibre v W where
  Φ := G.Φ
  Φ' := FractionRing (MRing ι' ⧸ W)
  alg := (genAlg G W hW).toAlgebra
  x := G.x
  x' := xW W
  ker_x := by rw [hW]; exact G.ker_x
  gen := G.gen
  genericFibre_ker_target := by
    refine Eq.trans ?_ (ker_aeval_xW W)
    ext f
    simp only [RingHom.mem_ker, aeval_def, algebraMap_int_eq]
    rw [RingHom.ext_int (algebraMap ℤ (FractionRing (MRing ι' ⧸ W))) (Int.castRingHom _)]
  compat p := (genAlg_alt G W hW p).symm

theorem baseSubst_rename (hκv : IsBlockMap κ v) (G : GenFibre v P') (f : MRing ι) :
    baseSubst κ G (rename v f) = C (aeval G.x f) := by
  have e : (baseSubst κ G).comp (rename v : MRing ι →ₐ[ℤ] MRing ι').toRingHom =
      (C : G.Φ →+* MRingOver G.Φ (fibreIdx ι' κ)).comp (aeval G.x : MRing ι →ₐ[ℤ] G.Φ).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun p => ?_)
    · exact RingHom.congr_fun (RingHom.ext_int (((baseSubst κ G).comp
        (rename v : MRing ι →ₐ[ℤ] MRing ι').toRingHom).comp C)
        (((C : G.Φ →+* MRingOver G.Φ (fibreIdx ι' κ)).comp
          (aeval G.x : MRing ι →ₐ[ℤ] G.Φ).toRingHom).comp C)) a
    · have h1 : (v p).1 ∈ Set.range κ := ⟨p.1, (hκv.2.2.1 p).symm⟩
      have h2 : v p ∈ Set.range v := ⟨p, rfl⟩
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_X, aeval_X]
      rw [baseSubst, eval₂Hom_X', dif_pos h1, dif_pos h2, hκv.2.1 h2.choose_spec]
  exact RingHom.congr_fun e f

theorem exists_clear (hκv : IsBlockMap κ v) (G : GenFibre v P') (g : MRingOver G.Φ (fibreIdx ι' κ)) :
    ∃ (b : MRing ι) (F : MRing ι'), aeval G.x b ≠ 0 ∧ C (aeval G.x b) * g = baseSubst κ G F := by
  induction g using MvPolynomial.induction_on with
  | C a =>
    obtain ⟨f, b, hb, rfl⟩ := G.gen a
    refine ⟨b, rename v f, hb, ?_⟩
    rw [baseSubst_rename hκv, ← C_mul, mul_div_cancel₀ _ hb]
  | add p q hp hq =>
    obtain ⟨b₁, F₁, h₁, e₁⟩ := hp
    obtain ⟨b₂, F₂, h₂, e₂⟩ := hq
    refine ⟨b₁ * b₂, rename v b₂ * F₁ + rename v b₁ * F₂, by rw [map_mul]; exact mul_ne_zero h₁ h₂, ?_⟩
    simp only [map_add, map_mul, baseSubst_rename hκv, ← e₁, ← e₂]
    ring
  | mul_X p n hp =>
    obtain ⟨b, F, h, e⟩ := hp
    refine ⟨b, F * X ⟨n.1.1, n.2⟩, h, ?_⟩
    rw [map_mul, ← e, mul_assoc]
    congr 2
    rw [baseSubst, eval₂Hom_X', dif_neg n.1.2]

theorem ker_eq_map {σ τ Φ Φ' : Type} [Field Φ] [Field Φ'] [Algebra Φ Φ']
    (β : MvPolynomial τ ℤ →+* MvPolynomial σ Φ) (y : σ → Φ') (φ : MvPolynomial τ ℤ →+* Φ')
    (W : Ideal (MvPolynomial τ ℤ)) (hφ : RingHom.ker φ = W) (hcomp : ∀ F, aeval y (β F) = φ F)
    (hclear : ∀ g, ∃ c : Φ, c ≠ 0 ∧ ∃ F, C c * g = β F) :
    RingHom.ker (aeval y : MvPolynomial σ Φ →ₐ[Φ] Φ') = Ideal.map β W := by
  apply le_antisymm
  · intro g hg
    obtain ⟨c, hc, F, e⟩ := hclear g
    have hF : F ∈ W := by
      rw [← hφ, RingHom.mem_ker, ← hcomp, ← e, map_mul, RingHom.mem_ker.mp hg, mul_zero]
    have hg' : g = C c⁻¹ * β F := by
      rw [← e, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hc, C_1, one_mul]
    rw [hg']
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hF)
  · rw [Ideal.map_le_iff_le_comap]
    intro F hF
    rw [Ideal.mem_comap, RingHom.mem_ker, hcomp, ← RingHom.mem_ker, hφ]
    exact hF

variable {W : Ideal (MRing ι')} [W.IsPrime] (hW : imageZ v W = imageZ v P')

theorem aeval_baseSubst (hκv : IsBlockMap κ v) (G : GenFibre v P') (f : MRing ι') :
    letI := (genAlg G W hW).toAlgebra
    aeval (fun q : Σ k : FibreBlock κ, ι' k.1 => xW W ⟨q.1.1, q.2⟩) (baseSubst κ G f) =
      aeval (R := ℤ) (xW W) f := by
  letI := (genAlg G W hW).toAlgebra
  have e : (aeval (fun q : Σ k : FibreBlock κ, ι' k.1 => xW W ⟨q.1.1, q.2⟩) :
        MRingOver G.Φ (fibreIdx ι' κ) →ₐ[G.Φ] FractionRing (MRing ι' ⧸ W)).toRingHom.comp (baseSubst κ G) =
      (aeval (R := ℤ) (xW W)).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun q => ?_)
    · rw [RingHom.comp_apply, baseSubst, eval₂Hom_C,
        eq_intCast (algebraMap ℤ (MRingOver G.Φ (fibreIdx ι' κ))) a, eq_intCast (C : ℤ →+* MRing ι') a,
        map_intCast, map_intCast]
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
      rw [baseSubst, eval₂Hom_X']
      by_cases h : q.1 ∈ Set.range κ
      · have h' : q ∈ Set.range v := hκv.2.2.2 q h
        rw [dif_pos h, dif_pos h', aeval_C, RingHom.algebraMap_toAlgebra, genAlg_alt, h'.choose_spec]
        rfl
      · rw [dif_neg h, aeval_X]
  exact RingHom.congr_fun e f

theorem fibreIdeal_genFibreOf (hκv : IsBlockMap κ v) (G : GenFibre v P') :
    fibreIdeal κ (genFibreOf G W hW) = fibreOf κ G W := by
  letI := (genAlg G W hW).toAlgebra
  exact ker_eq_map (baseSubst κ G) (fun q : Σ k : FibreBlock κ, ι' k.1 => xW W ⟨q.1.1, q.2⟩)
    (aeval (R := ℤ) (xW W)).toRingHom W (ker_aeval_xW W) (aeval_baseSubst hW hκv G)
    (fun g => let ⟨_, F, hb, e⟩ := exists_clear hκv G g; ⟨_, hb, F, e⟩)

end PFHoriz

theorem PFHoriz.proof : PFHoriz.Statement := by
  intro I r hPF K _ ι _ K' _ ι' _ κ v P' W d G J L L' N hκv hW hWP hP hJ hL hLL hN
  haveI : W.IsPrime := hW.2.1.1
  have h := hPF K ι K' ι' κ v W d (PFHoriz.genFibreOf G W hWP) J L L' N hκv hW (by rw [hWP]; exact hP)
    hJ hL hLL hN
  rw [PFHoriz.fibreIdeal_genFibreOf hWP hκv G, hWP] at h
  exact h

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PPFVert
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace ProjectionFormulaVertical

open PointVertical

theorem geoNum_mixed_eq_zero
    (hGeo : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], GeoNumStatement ι)
    (hR4 : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
      ExistsUniqueStatement F ι)
    (hCMF : ContractMixedFieldStatement)
    {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
    {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v) {P' : Ideal (MRing ι')} {d r : ℕ}
    (hP : IsArithVar (imageZ v P') d) {W : Ideal (MRing ι')} (hPW : P' ≤ W)
    (hWm : IsMultiProjPrime W) (hpr : (charOf W).Prime)
    (hWd : ringKrullDim (MRing ι' ⧸ W) = ((d + r + Fintype.card K' : ℕ) : WithBot ℕ∞))
    (L : Fin d → K → ℤ) (N : Fin r → K' → ℤ) :
    geoNum (d + r) W (Fin.append (fun j => pullDeg κ (L j)) N) = 0 := by
  set p := charOf W with hpdef
  have : Fact p.Prime := ⟨hpr⟩
  have hpW : ((p : ℕ) : MRing ι') ∈ W := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.natCast_mem_of_charOf W
  have hWp : IsProjVarF (W.map (red p)) (d + r) :=
    ⟨isMultiProjPrime_red p hWm hpW, by rw [ringKrullDim_red p hpW, hWd]⟩
  have hImm : IsMultiProjPrime (imageZ v W) := isMultiProjPrime_imageZ hv hWm
  have hpI : ((p : ℕ) : MRing ι) ∈ imageZ v W := by
    show rename v ((p : ℕ) : MRing ι) ∈ W
    simpa using hpW
  have hVm := isMultiProjPrime_red p hImm hpI
  obtain ⟨D, hKD, hD⟩ := exists_dim_F p _ hVm
  obtain ⟨-, ⟨hQp, -, -⟩, hQh, hQd⟩ := hP
  have := hQp
  have hle : imageZ v P' ≤ imageZ v W := Ideal.comap_mono hPW
  have hpQ : ((p : ℕ) : MRing ι) ∉ imageZ v P' := by
    intro h
    have h2 : ((p : ℕ) : ℤ) ∈ (imageZ v P').comap (C : ℤ →+* MRing ι) := by
      rw [Ideal.mem_comap, map_natCast]
      exact h
    rw [hQh, Ideal.mem_bot] at h2
    exact hpr.ne_zero (by exact_mod_cast h2)
  have hdim := krullDim_quot_add_one_le hle hpI hpQ
  rw [← ringKrullDim_red p hpI, hD, hQd] at hdim
  have hD' : D + 1 ≤ d + Fintype.card K := by exact_mod_cast hdim
  have hVi : IsProjVarF (imageVar (ZMod p) v (W.map (red p))) (D - Fintype.card K) := by
    rw [imageVar_red p v hpW]
    refine ⟨hVm, ?_⟩
    rw [hD, Nat.sub_add_cancel hKD]
  obtain ⟨I, hI, -⟩ := hR4 (ZMod p) K' ι'
  rw [hGeo K' ι' p I hI W (d + r) _ hWm hpW hWp]
  exact hCMF (ZMod p) K ι K' ι' I hI κ v _ (D - Fintype.card K) d r L N hv hWp hVi (by omega)

end ProjectionFormulaVertical

open ProjectionFormulaVertical in

theorem PFVert.proof
    (hGeo : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], GeoNumStatement ι)
    (hR4 : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
      ExistsUniqueStatement F ι)
    (hCMF : ContractMixedFieldStatement) :
    PFVert.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' d r L L' N s a W hv hP' hP hL hs hsP hW hh
  classical
  have hsec : IsSectionOn P' (HermLine.sqMetric (ι := ι') a) s := ⟨a, fun _ => rfl, hs, hsP⟩
  obtain ⟨-, hvert⟩ := divSuppArith K' ι' P' (d + r) _ _ W hP' hsec hW
  obtain ⟨hWm, hpr, hWd⟩ := hvert hh
  have hPW : P' ≤ W := le_sup_left.trans hW.1.1.2
  have e : (fun j => (Fin.append L' N j).a) =
      Fin.append (fun j => pullDeg κ (L j).a) (fun j => (N j).a) := by
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp [(hL i).1]
    · simp
  rw [e]
  exact geoNum_mixed_eq_zero hGeo hR4 hCMF hv hP hPW hWm hpr hWd _ _

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsBlockGenFinite
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

def BlockGenFinite.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (n : ℕ),
    IsBlockMap κ v → IsArithVar P' (n + 1) → IsArithVar (imageZ v P') (n + 1) →
    ∃ (f₀ : MRing ι') (a : K' → ℕ), IsMultiHomog f₀ a ∧ f₀ ∉ P' ∧
      ∀ u : (Σ k, ι k) → ℂ, ∃ T : Finset ((Σ k', ι' k') → ℂ),
        ∀ z' ∈ mcPts P', eval z' (map (Int.castRingHom ℂ) f₀) ≠ 0 →
          SameOrbit (fun p => z' (v p)) u → ∃ t ∈ T, SameOrbit z' t

section Inhabitants

open IndefiniteRowSideFullHecke.Inter

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
end
end

