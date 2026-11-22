import Mathlib
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0013
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0021
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0019
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0044
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0012
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0029
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0033
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0023
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0017
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0018
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
import GroundTheory.HeightsAndTheta.Heights.Intersections.PThmAExpand
import GroundTheory.HeightsAndTheta.Heights.Intersections.PRFormula
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0058
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.SmallSectionCountLeOfInjOn
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0086
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0013

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ChartConeObjects
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial

section Objects

variable {K : Type*} [Fintype K] {ι : K → Type*}

def dehomIdeal (i : (k : K) → ι k) : Ideal (MvPolynomial (Σ k, ι k) ℂ) :=
  Ideal.span (Set.range fun k => (X ⟨k, i k⟩ - 1 : MvPolynomial (Σ k, ι k) ℂ))

abbrev DehomRing (i : (k : K) → ι k) := MvPolynomial (Σ k, ι k) ℂ ⧸ dehomIdeal i

def dehom (i : (k : K) → ι k) : MvPolynomial (Σ k, ι k) ℂ →ₐ[ℂ] DehomRing i :=
  Ideal.Quotient.mkₐ ℂ (dehomIdeal i)

def coneUnit (i : (k : K) → ι k) : MvPolynomial (Σ k, ι k) ℂ :=
  ∏ k, X ⟨k, i k⟩

abbrev ConeRing (i : (k : K) → ι k) := Localization.Away (coneUnit i)

theorem isUnit_coneX (i : (k : K) → ι k) (k : K) :
    IsUnit (algebraMap (MvPolynomial (Σ k, ι k) ℂ) (ConeRing i) (X ⟨k, i k⟩)) :=
  isUnit_of_dvd_unit (map_dvd _ (Finset.dvd_prod_of_mem (fun k => (X ⟨k, i k⟩ : MvPolynomial (Σ k, ι k) ℂ))
    (Finset.mem_univ k))) (IsLocalization.Away.algebraMap_isUnit (coneUnit i))

def coneRatio (i : (k : K) → ι k) : MvPolynomial (Σ k, ι k) ℂ →ₐ[ℂ] ConeRing i :=
  aeval fun p => (((isUnit_coneX i p.1).unit⁻¹ : (ConeRing i)ˣ) : ConeRing i) *
    algebraMap (MvPolynomial (Σ k, ι k) ℂ) (ConeRing i) (X p)

theorem coneRatio_X_self (i : (k : K) → ι k) (k : K) : coneRatio i (X ⟨k, i k⟩) = 1 := by
  rw [coneRatio, aeval_X]
  exact (isUnit_coneX i k).val_inv_mul

def ratioMap (i : (k : K) → ι k) : DehomRing i →+* ConeRing i :=
  Ideal.Quotient.lift (dehomIdeal i) (coneRatio i : MvPolynomial (Σ k, ι k) ℂ →+* ConeRing i) (by
    have hle : dehomIdeal i ≤ RingHom.ker (coneRatio i : MvPolynomial (Σ k, ι k) ℂ →+* ConeRing i) := by
      rw [dehomIdeal, Ideal.span_le]
      rintro _ ⟨k, rfl⟩
      simp [coneRatio_X_self]
    exact fun a ha => hle ha)

theorem ratioMap_dehom (i : (k : K) → ι k) (f : MvPolynomial (Σ k, ι k) ℂ) :
    ratioMap i (dehom i f) = coneRatio i f :=
  Ideal.Quotient.lift_mk _ _ _

omit [Fintype K] in
theorem dehom_X_self (i : (k : K) → ι k) (k : K) : dehom i (X ⟨k, i k⟩) = 1 := by
  rw [← sub_eq_zero, ← map_one (dehom i), ← map_sub]
  exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨k, rfl⟩)

theorem dehom_coneUnit (i : (k : K) → ι k) : dehom i (coneUnit i) = 1 := by
  rw [coneUnit, map_prod]
  exact Finset.prod_eq_one fun k _ => dehom_X_self i k

omit [Fintype K] in
theorem dehom_surjective (i : (k : K) → ι k) : Function.Surjective (dehom i) :=
  Ideal.Quotient.mk_surjective

def evalOne (i : (k : K) → ι k) : ConeRing i →+* DehomRing i :=
  IsLocalization.Away.lift (coneUnit i) (g := (dehom i : MvPolynomial (Σ k, ι k) ℂ →+* DehomRing i))
    (by rw [AlgHom.coe_toRingHom, dehom_coneUnit]; exact isUnit_one)

theorem evalOne_algebraMap (i : (k : K) → ι k) (f : MvPolynomial (Σ k, ι k) ℂ) :
    evalOne i (algebraMap _ (ConeRing i) f) = dehom i f :=
  IsLocalization.lift_eq _ _

theorem evalOne_comp_algebraMap (i : (k : K) → ι k) :
    (evalOne i).comp (algebraMap _ (ConeRing i)) = (dehom i : MvPolynomial (Σ k, ι k) ℂ →+* DehomRing i) :=
  RingHom.ext (evalOne_algebraMap i)

theorem evalOne_comp_ratioMap (i : (k : K) → ι k) : (evalOne i).comp (ratioMap i) = RingHom.id _ := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro c
    simp only [RingHom.comp_apply, RingHom.id_apply]
    have h1 : ratioMap i (Ideal.Quotient.mk (dehomIdeal i) (C c)) =
        algebraMap (MvPolynomial (Σ k, ι k) ℂ) (ConeRing i) (C c) := by
      rw [show Ideal.Quotient.mk (dehomIdeal i) (C c) = dehom i (C c) from rfl, ratioMap_dehom, coneRatio,
        aeval_C, IsScalarTower.algebraMap_apply ℂ (MvPolynomial (Σ k, ι k) ℂ) (ConeRing i),
        MvPolynomial.algebraMap_eq]
    rw [h1, evalOne_algebraMap]
    rfl
  · intro p
    simp only [RingHom.comp_apply, RingHom.id_apply]
    rw [show Ideal.Quotient.mk (dehomIdeal i) (X p) = dehom i (X p) from rfl, ratioMap_dehom, coneRatio, aeval_X,
      map_mul, evalOne_algebraMap]
    have hu : evalOne i (((isUnit_coneX i p.1).unit : (ConeRing i)ˣ) : ConeRing i) = 1 := by
      rw [IsUnit.unit_spec, evalOne_algebraMap, dehom_X_self]
    have hinv : evalOne i (((isUnit_coneX i p.1).unit⁻¹ : (ConeRing i)ˣ) : ConeRing i) = 1 := by
      have := congrArg (evalOne i) ((isUnit_coneX i p.1).unit.inv_mul)
      rwa [map_mul, hu, mul_one, map_one] at this
    rw [hinv, one_mul]

theorem evalOne_ratioMap (i : (k : K) → ι k) (g : DehomRing i) : evalOne i (ratioMap i g) = g :=
  RingHom.congr_fun (evalOne_comp_ratioMap i) g

variable [DecidableEq K]

def segreDehom {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) :
    MvPolynomial (Fin m) ℂ →ₐ[ℂ] DehomRing i :=
  aeval fun a => dehom i (∏ k, X ⟨k, σ a k⟩)

theorem segreDehom_chartSubst {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (f : MvPolynomial (Σ k, ι k) ℂ) : segreDehom σ i (chartSubst σ i f) = dehom i f := by
  have h : (segreDehom σ i).comp (chartSubst σ i) = dehom i := by
    apply MvPolynomial.algHom_ext
    intro p
    rw [AlgHom.comp_apply, chartSubst_X, segreDehom, aeval_X, Equiv.apply_symm_apply, map_prod]
    rw [Finset.prod_eq_single p.1]
    · simp only [Function.update_self]
    · intro k _ hk
      rw [Function.update_of_ne hk, dehom_X_self]
    · intro h
      exact absurd (Finset.mem_univ _) h
  exact AlgHom.congr_fun h f

theorem segreDehom_surjective {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) :
    Function.Surjective (segreDehom σ i) := fun g => by
  obtain ⟨f, rfl⟩ := dehom_surjective i g
  exact ⟨chartSubst σ i f, segreDehom_chartSubst σ i f⟩

end Objects

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveCountLower
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GroundTheory.Heights₂.Heights.Inter

theorem CurveCountLower.proof (hD : CurveDegreeVert.Statement) (hV : CurveVertIndex.Statement)
    (hL : CurveIndexLinear.Statement) (hN : CurveBoxCount.Statement) : CurveCountLower.Statement := by
  intro K _ ι _ Ω _ y A II hII hP hB hS hC
  obtain ⟨c, hcX, hc⟩ := exists_chart hP
  obtain ⟨R, hRP, hRu, -⟩ := regularityPointsSum_holds.proof K ι _ hP
  set b : K → ℕ := fun k => (A.a k).natAbs with hb
  set d : K → ℕ := fun k => (A.a k + b k).toNat with hd'
  have hd : ∀ k, (d k : ℤ) = A.a k + b k := fun k =>
    Int.toNat_of_nonneg (by simp only [hb]; omega)
  have h1 := hD K ι _ A II c R b d hII hP hS hcX hRP hRu hd
  have h2 := hV K ι Ω y _ d hP (isMultiHomog_curveChartMono c d) (curveChartMono_notMem hc d)
  have h3 := hV K ι Ω y _ b hP (isMultiHomog_curveChartMono c b) (curveChartMono_notMem hc b)
  rw [aeval_curveChartMono] at h2 h3
  obtain ⟨hadd, hpow⟩ := hL K ι Ω y c hP hc
  have h4 := hadd A.a (fun k => (b k : ℤ))
  rw [show A.a + (fun k => (b k : ℤ)) = fun k => (d k : ℤ) from funext fun k => (hd k).symm] at h4
  have hI : II K ι (mCoordIdeal y) 1 (fun _ => A) =
      chartIndexLog y c A.a 1 + ∑ t ∈ R, Real.log (chartRadius A c t) := by
    have e2 : vertR (mCoordIdeal y) (Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (curveChartMono c d) =
        chartIndexLog y c (fun k => (d k : ℤ)) 1 := h2
    have e3 : vertR (mCoordIdeal y) (Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (curveChartMono c b) =
        chartIndexLog y c (fun k => (b k : ℤ)) 1 := h3
    rw [h1, e2, e3, h4]
    ring
  obtain ⟨C, hCC⟩ := hN K ι Ω y A c R hP hB hC hc hRP hRu
  refine ⟨C, fun τ hτ => ?_⟩
  have h5 := hCC τ hτ
  rw [hpow A.a τ] at h5
  rw [hI]
  linarith [mul_add (τ : ℝ) (chartIndexLog y c A.a 1) (∑ t ∈ R, Real.log (chartRadius A c t))]

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveDegreeVert
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GroundTheory.Heights₂.Heights.Inter

noncomputable section

namespace CurveDegreeVert

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def fsLine (b : K → ℕ) : HermLine ι :=
  HermLine.ofMetrics (fun k => fsMetric (ι k)) (fun k => (b k : ℤ))

theorem isSmoothHerm_fsLine (b : K → ℕ) : IsSmoothHerm (fsLine b : HermLine ι) := by
  have hfun : (fsLine b : HermLine ι).h =
      fun z => ∏ k, Real.sqrt (∑ i : ι k, ‖z ⟨k, i⟩‖ ^ 2) ^ b k := by
    funext z
    simp only [fsLine, HermLine.ofMetrics, fsMetric, zpow_natCast, EuclideanSpace.norm_eq]
  unfold IsSmoothHerm
  rw [hfun]
  refine contDiffOn_prod fun k _ => (ContDiffOn.sqrt ?_ fun z hz => ?_).pow (b k)
  · exact (ContDiff.sum fun i _ => (contDiff_norm_sq ℝ).comp
      (contDiff_apply ℝ ℂ (⟨k, i⟩ : Σ k, ι k))).contDiffOn
  · obtain ⟨i, hi⟩ := hz k
    exact (Finset.sum_pos' (fun j _ => sq_nonneg ‖z ⟨k, j⟩‖)
      ⟨i, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr hi) 2⟩).ne'

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem sameOrbit_refl (z : (Σ k, ι k) → ℂ) : SameOrbit z z :=
  ⟨fun _ => 1, fun _ => one_ne_zero, by funext p; simp⟩

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem sameOrbit_symm {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') : SameOrbit z' z := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), ?_⟩
  funext p
  simp [← mul_assoc, inv_mul_cancel₀ (hc p.1)]

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem sameOrbit_trans {z z' z'' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') (h' : SameOrbit z' z'') :
    SameOrbit z z'' := by
  obtain ⟨c, hc, rfl⟩ := h
  obtain ⟨d, hd, rfl⟩ := h'
  exact ⟨fun k => c k * d k, fun k => mul_ne_zero (hc k) (hd k), by funext p; simp [mul_assoc]⟩

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem sum_eq_of_transversal {P : Ideal (MRing ι)} {R R' : Finset ((Σ k, ι k) → ℂ)}
    (hRP : ∀ t ∈ R, t ∈ mcPts P) (hRu : ∀ z ∈ mcPts P, ∃! t, t ∈ R ∧ SameOrbit z t)
    (hR'P : ∀ t ∈ R', t ∈ mcPts P) (hR'u : ∀ z ∈ mcPts P, ∃! t, t ∈ R' ∧ SameOrbit z t)
    (h : ((Σ k, ι k) → ℂ) → ℝ) (hh : ∀ z z', z ∈ mcPts P → SameOrbit z z' → h z = h z') :
    ∑ t ∈ R, h t = ∑ t ∈ R', h t := by
  refine Finset.sum_bij (fun t ht => (hR'u t (hRP t ht)).exists.choose)
    (fun t ht => (hR'u t (hRP t ht)).exists.choose_spec.1) ?_ ?_ ?_
  · intro t₁ h₁ t₂ h₂ he
    have e1 := (hR'u t₁ (hRP t₁ h₁)).exists.choose_spec.2
    have e2 := (hR'u t₂ (hRP t₂ h₂)).exists.choose_spec.2
    rw [he] at e1
    exact (hRu t₂ (hRP t₂ h₂)).unique ⟨h₁, sameOrbit_trans e2 (sameOrbit_symm e1)⟩ ⟨h₂, sameOrbit_refl t₂⟩
  · intro t' ht'
    obtain ⟨t, ⟨htR, hto⟩, -⟩ := hRu t' (hR'P t' ht')
    exact ⟨t, htR, (hR'u t (hRP t htR)).unique (hR'u t (hRP t htR)).exists.choose_spec
      ⟨ht', sameOrbit_symm hto⟩⟩
  · intro t ht
    exact hh _ _ (hRP t ht) (hR'u t (hRP t ht)).exists.choose_spec.2

theorem logNorm_sameOrbit {A : HermLine ι} {s : MRing ι} {a : K → ℕ} (ha : ∀ k, A.a k = a k)
    (hs : IsMultiHomog s a) {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    logNorm A s z = logNorm A s z' := by
  obtain ⟨c, hc, rfl⟩ := h
  unfold logNorm
  have hn : ∏ k, ‖c k‖ ^ A.a k = ‖∏ k, c k ^ a k‖ := by
    simp [ha, norm_prod, norm_pow]
  have h0 : ‖∏ k, c k ^ a k‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k))
  rw [eval_smul_homog s a hs c z', A.smul c z' hc, norm_mul, hn, mul_div_mul_left _ _ h0]

omit [∀ k, Fintype (ι k)] in
theorem norm_eval_curveChartMono (c : ∀ k, ι k) (e : K → ℕ) (z : (Σ k, ι k) → ℂ) :
    ‖eval z (map (Int.castRingHom ℂ) (curveChartMono c e))‖ = ∏ k, ‖z ⟨k, c k⟩‖ ^ e k := by
  simp [curveChartMono, map_prod, norm_prod]

theorem proof : CurveDegreeVert.Statement := by
  intro K _ ι _ P A II c R b d hII hP hA hc hRP hRu hd
  have hI := hII K ι
  have hpr : P.IsPrime := hP.2.1.1
  have hL : ∀ j, IsSmoothHerm ((Fin.elim0 : Fin 0 → HermLine ι) j) := fun j => j.elim0
  have hsnoc : ∀ C : HermLine ι,
      (Fin.snoc (Fin.elim0 : Fin 0 → HermLine ι) C : Fin (0 + 1) → HermLine ι) = fun _ => C :=
    fun C => funext fun i => by rw [Fin.fin_one_eq_zero i]; rfl
  have hmono : ∀ e : K → ℕ, curveChartMono c e ∉ P := by
    intro e h
    rw [curveChartMono, hpr.prod_mem_iff] at h
    obtain ⟨k, _, hk⟩ := h
    exact hc k (hpr.mem_of_pow_mem _ hk)
  set B : HermLine ι := fsLine b with hBdef
  have hB : IsSmoothHerm B := isSmoothHerm_fsLine b
  have hBa : ∀ k, B.a k = b k := fun k => rfl
  have hABa : ∀ k, (A.tensor B).a k = d k := fun k => by
    show A.a k + B.a k = d k
    rw [hBa, hd k]
  have hsd : IsSectionOn P (A.tensor B) (curveChartMono c d) :=
    ⟨d, hABa, isMultiHomog_curveChartMono c d, hmono d⟩
  have hsb : IsSectionOn P B (curveChartMono c b) := ⟨b, hBa, isMultiHomog_curveChartMono c b, hmono b⟩

  have hnz : ∀ z ∈ mcPts P, ∀ k, z ⟨k, c k⟩ ≠ 0 := by
    intro z hz k
    have hs1 : IsSectionOn P (fsLine (fun _ => 1) : HermLine ι) (curveChartMono c fun _ => 1) :=
      ⟨fun _ => 1, fun _ => rfl, isMultiHomog_curveChartMono c _, hmono _⟩
    have h1 := norm_ne_zero_iff.mpr (eval_ne_zero_of_dimOne arithVarZero hP hs1 hz)
    rw [norm_eval_curveChartMono] at h1
    have h2 := Finset.prod_ne_zero_iff.mp h1 k (Finset.mem_univ k)
    simpa using h2

  have hadd := hI.2.1 P 0 Fin.elim0 A B hP hL hA hB
  have hRd := hI.2.2 P 0 Fin.elim0 (A.tensor B) (curveChartMono c d) d hP hL
    (hA.mul hB) hABa (isMultiHomog_curveChartMono c d) (hmono d)
  have hRb := hI.2.2 P 0 Fin.elim0 B (curveChartMono c b) b hP hL hB hBa
    (isMultiHomog_curveChartMono c b) (hmono b)
  rw [hsnoc, hsnoc, hsnoc] at hadd
  rw [hsnoc] at hRd hRb
  rw [recR_eq, cycR_eq_vertR_of_dimOne arithVarZero _ hP hsd] at hRd
  rw [recR_eq, cycR_eq_vertR_of_dimOne arithVarZero _ hP hsb] at hRb

  obtain ⟨R', hR'P, hR'u, hsum⟩ := regularityPointsSum_holds.proof K ι P hP
  have hφ : (fun (j : Fin 0) (z : (Σ k, ι k) → ℂ) => Real.log (((Fin.elim0 : Fin 0 → HermLine ι) j).h z)) =
      (Fin.elim0 : Fin 0 → ((Σ k, ι k) → ℂ) → ℝ) := funext fun j => j.elim0
  have hint : ∀ (C : HermLine ι) (s : MRing ι) (e : K → ℕ), (∀ k, C.a k = e k) → IsMultiHomog s e →
      arInt P s C (Fin.elim0 : Fin 0 → HermLine ι) = ∑ t ∈ R, logNorm C s t := by
    intro C s e hCe hse
    have hinv : ∀ z z', z ∈ mcPts P → SameOrbit z z' → logNorm C s z = logNorm C s z' :=
      fun z z' _ h => logNorm_sameOrbit hCe hse h
    rw [arInt, hφ, hsum _ hinv]
    exact (sum_eq_of_transversal hRP hRu hR'P hR'u _ hinv).symm
  rw [hint _ _ d hABa (isMultiHomog_curveChartMono c d)] at hRd
  rw [hint _ _ b hBa (isMultiHomog_curveChartMono c b)] at hRb

  have hpt : ∀ t ∈ R, logNorm B (curveChartMono c b) t - logNorm (A.tensor B) (curveChartMono c d) t =
      Real.log (chartRadius A c t) := by
    intro t ht
    have hz := hRP t ht
    have hk := hnz t hz
    have hApos := A.pos t hz.1
    have hBpos := B.pos t hz.1
    have hpos : ∀ e : K → ℕ, 0 < ∏ k, ‖t ⟨k, c k⟩‖ ^ e k := fun e =>
      Finset.prod_pos fun k _ => pow_pos (norm_pos_iff.mpr (hk k)) _
    have hsplit : ∏ k, ‖t ⟨k, c k⟩‖ ^ d k =
        (∏ k, ‖t ⟨k, c k⟩‖ ^ b k) * ∏ k, ‖t ⟨k, c k⟩‖ ^ A.a k := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (norm_ne_zero_iff.mpr (hk k)), hd k, add_comm]
    unfold logNorm chartRadius
    rw [norm_eval_curveChartMono, norm_eval_curveChartMono, show (A.tensor B).h t = A.h t * B.h t from rfl,
      ← Real.log_div (div_pos (hpos b) hBpos).ne' (div_pos (hpos d) (mul_pos hApos hBpos)).ne', hsplit]
    congr 1
    have := hpos b
    have hq : 0 < ∏ k, ‖t ⟨k, c k⟩‖ ^ A.a k :=
      Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.mpr (hk k)) _
    field_simp
  rw [← Finset.sum_congr rfl hpt, Finset.sum_sub_distrib]
  linarith

end CurveDegreeVert

end

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveRatSectionSum
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable section

namespace CurveRationalSectionSum

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem logNorm_smul {X : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} {s : MRing ι} {a : K → ℕ} (hXa : ∀ k, X.a k = a k)
    (hs : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s a) (c : K → ℂ) (z : (Σ k, ι k) → ℂ) (hc : ∀ k, c k ≠ 0) :
    logNorm X s (fun p => c p.1 * z p) = logNorm X s z := by
  unfold logNorm
  rw [eval_smul_homog s a hs c z, X.smul c z hc, norm_mul]
  have hprod : (∏ k, ‖c k‖ ^ X.a k) = ‖∏ k, c k ^ a k‖ := by
    rw [norm_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [hXa k, zpow_natCast, norm_pow]
  rw [hprod, mul_div_mul_left _ _
    (norm_ne_zero_iff.mpr (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)))]

theorem arInt_eq_sum {P : Ideal (MRing ι)} (hP : IsArithVar P 1) {X : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι}
    {s : MRing ι} {a : K → ℕ} (hXa : ∀ k, X.a k = a k) (hs : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s a) :
    arInt P s X (Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) =
      ∑ᶠ q : projPts P, logNorm X s (Quot.out q : mcPts P) := by
  have : Nonempty K := hP.1
  have hφ : (fun (j : Fin 0) (z : (Σ k, ι k) → ℂ) =>
      Real.log (((Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) j).h z)) = Fin.elim0 :=
    funext fun j => j.elim0
  unfold arInt
  rw [hφ]
  exact PtsIntegralPoints.homogProof K ι P _ hP.2.1.2.1 (HilbertSamuel.CurvePointsFinite.proof K ι P hP)
    fun c z hc _ => logNorm_smul hXa hs c z hc

theorem cycR_eq_vertR (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) → ℝ)
    {P : Ideal (MRing ι)} (hP : IsArithVar P 1) {X : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} {s : MRing ι}
    (hs : IsSectionOn P X s) :
    cycR I P (Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) s =
      vertR P (Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) s := by
  unfold cycR vertR
  refine finsum_mem_congr rfl fun W hW => ?_
  have hnh : ¬ IsHorizontal W := fun hh =>
    Inter.arithVarZero K ι W ((divSuppArith K ι P 0 X s W hP hs hW).1 hh)
  rw [if_neg hnh, if_neg hnh]

omit [∀ k, Fintype (ι k)] in

theorem snoc_elim0 (X : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) :
    (Fin.snoc (Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) X : Fin (0 + 1) → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) =
      fun _ => X := by
  funext j
  fin_cases j
  rfl

end CurveRationalSectionSum

open CurveRationalSectionSum in

theorem CurveRatSectionSum.proof (hNV : CurveFormNonvanishing.Statement) : CurveRatSectionSum.Statement := by
  intro K _ ι _ Ω _ y A II hII har hA n dg dh g h hg hh hd hgy hhy
  obtain ⟨-, hAdd, hR⟩ := hII K ι
  have hB := isSmoothHerm_sqMetric (ι := ι) dh
  have hnA := Inter.isSmoothHerm_hermZpow hA (n : ℤ)
  have hgP : g ∉ mCoordIdeal y := by
    rw [Inter.mCoordIdeal_eq_ker_multiConeMap]
    exact (Inter.DiagRAux.not_mem_ker_iff_aeval_ne y g dg hg).mpr hgy
  have hhP : h ∉ mCoordIdeal y := by
    rw [Inter.mCoordIdeal_eq_ker_multiConeMap]
    exact (Inter.DiagRAux.not_mem_ker_iff_aeval_ne y h dh hh).mpr hhy
  have hda : ∀ k, ((Inter.hermZpow A n).tensor (HermLine.sqMetric dh)).a k = dg k := fun k => by
    show (n : ℤ) • A.a k + (dh k : ℤ) = dg k
    rw [hd k, smul_eq_mul]
    ring
  have hRg := hR _ 0 Fin.elim0 _ g dg har (fun j => j.elim0)
    (ReciprocityTheory.ChartRestriction.G.Geo.isSmoothHerm_tensor hnA hB) hda hg hgP
  have hRh := hR _ 0 Fin.elim0 _ h dh har (fun j => j.elim0) hB (fun k => rfl) hh hhP
  have hsum := hAdd _ 0 Fin.elim0 _ _ har (fun j => j.elim0) hnA hB
  have hpow : II K ι (mCoordIdeal y) 1 (fun _ => Inter.hermZpow A n) =
      (n : ℝ) ^ 1 * II K ι (mCoordIdeal y) 1 (fun _ => A) :=
    HilbertSamuel.Mono.fam_hermZpow (hII K ι) (D := 0) har hA n
  rw [recR_eq, cycR_eq_vertR _ har ⟨dg, hda, hg, hgP⟩, arInt_eq_sum har hda hg, snoc_elim0] at hRg
  rw [recR_eq, cycR_eq_vertR _ har (X := HermLine.sqMetric dh) ⟨dh, fun k => rfl, hh, hhP⟩, arInt_eq_sum har (X := HermLine.sqMetric dh) (fun k => rfl) hh,
    snoc_elim0] at hRh
  rw [snoc_elim0, snoc_elim0, snoc_elim0] at hsum
  rw [pow_one] at hpow
  have := HilbertSamuel.CurvePointsFinite.proof K ι _ har
  have hcomb : ∑ᶠ q : projPts (mCoordIdeal y),
        logNorm ((Inter.hermZpow A n).tensor (HermLine.sqMetric dh)) g (Quot.out q : mcPts (mCoordIdeal y)) -
      ∑ᶠ q : projPts (mCoordIdeal y), logNorm (HermLine.sqMetric dh) h (Quot.out q : mcPts (mCoordIdeal y)) =
      ∑ᶠ q : projPts (mCoordIdeal y), ratLogNormPow A n g h (Quot.out q : mcPts (mCoordIdeal y)) := by
    rw [← finsum_sub_distrib (Set.toFinite _) (Set.toFinite _)]
    refine finsum_congr fun q => ?_
    have hz := (Quot.out q).2
    have hg0 := norm_pos_iff.mpr (hNV K ι Ω y dg g har hg hgy _ hz)
    have hh0 := norm_pos_iff.mpr (hNV K ι Ω y dh h har hh hhy _ hz)
    have hA0 := A.pos _ hz.1
    have hB0 := (HermLine.sqMetric (ι := ι) dh).pos _ hz.1
    unfold logNorm ratLogNormPow
    show Real.log (_ / (A.h _ ^ (n : ℤ) * (HermLine.sqMetric dh).h _)) - Real.log (_ / (HermLine.sqMetric dh).h _) =
      Real.log (_ / (_ * A.h _ ^ n))
    rw [zpow_natCast, Real.log_div hg0.ne' (mul_pos (pow_pos hA0 n) hB0).ne',
      Real.log_mul (pow_pos hA0 n).ne' hB0.ne', Real.log_div hh0.ne' hB0.ne',
      Real.log_div hg0.ne' (mul_pos hh0 (pow_pos hA0 n)).ne', Real.log_mul hh0.ne' (pow_pos hA0 n).ne']
    ring
  have e1 : II K ι (mCoordIdeal y) 1 (fun _ => (Inter.hermZpow A n).tensor (HermLine.sqMetric dh)) =
      II K ι (mCoordIdeal y) 1 (fun _ => Inter.hermZpow A n) +
        II K ι (mCoordIdeal y) 1 (fun _ => HermLine.sqMetric dh) := hsum
  linarith

end

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsChartLatFull
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def ChartLatFull.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [NumberField Ω]
    (y : (Σ k, ι k) → Ω), Birational y →
    ∀ (a : K → ℤ) (τ : ℕ) (s : Ω), ∃ n : ℕ, 0 < n ∧ (n : Ω) * s ∈ chartLat y a τ

end GroundTheory.Heights₂.Heights.Targets
end

