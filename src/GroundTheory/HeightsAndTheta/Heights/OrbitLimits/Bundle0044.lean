import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0042
import GroundTheory.HeightsAndTheta.Heights.Intersections.NotMemOfNonZeroDivisor
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Bundle0012
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0033
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0054
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0028
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0040
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0055
import GroundTheory.HeightsAndTheta.Heights.Intersections.PTorusInvLevi
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0017
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0039
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0012
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0031
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.CurveOrbitEmbedding
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GroundTheory.Heights₂.Heights.Inter

noncomputable section

namespace CurveOrbit

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

omit [Fintype K] in

theorem isMultiHomog_mul {f g : MRing ι} {a b : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g b) :
    IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hf m1 hm1 k, hg m2 hm2 k]

omit [Fintype K] in

theorem isMultiHomog_add {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f + g) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
  · exact hf m h k
  · exact hg m h k

omit [Fintype K] in

theorem isMultiHomog_sub {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f - g) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.mp (MvPolynomial.support_sub _ f g hm) with h | h
  · exact hf m h k
  · exact hg m h k

omit [Fintype K] in

theorem isMultiHomog_one : IsMultiHomog (1 : MRing ι) 0 := by
  classical
  intro m hm k
  rw [MvPolynomial.support_one] at hm
  rcases Finset.mem_singleton.mp hm with rfl
  simp

theorem mem_of_aeval_eq_zero (y : (Σ k, ι k) → Ω) {f : MRing ι} {d : K → ℕ} (hf : IsMultiHomog f d)
    (h0 : aeval y f = 0) : f ∈ mCoordIdeal y := by
  show mConeMap y f = 0
  rw [ConeTrdeg.mConeMap_of_isMultiHomog y hf, h0, map_zero, zero_mul]

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem aeval_eq_zero_of_mem (y : (Σ k, ι k) → Ω) {f : MRing ι} (hf : f ∈ mCoordIdeal y) : aeval y f = 0 := by
  have hc : (MvPolynomial.eval (fun _ : K => (1 : Ω))).comp (mConeMap y).toRingHom = (aeval y).toRingHom :=
    MvPolynomial.ringHom_ext (fun n => by simp) (fun p => by simp [mConeMap])
  have h0 : mConeMap y f = 0 := hf
  have := congrArg (fun φ => φ f) hc
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, h0, map_zero] at this
  exact this.symm

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem eval_map_eq_aeval (w : (Σ k, ι k) → ℂ) (f : MRing ι) :
    eval w (map (Int.castRingHom ℂ) f) = aeval w f := by
  rw [eval_map, aeval_def, algebraMap_int_eq]

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem eval_comp (σ : Ω →+* ℂ) (y : (Σ k, ι k) → Ω) (f : MRing ι) :
    eval (fun p => σ (y p)) (map (Int.castRingHom ℂ) f) = σ (aeval y f) := by
  have : (eval (fun p => σ (y p))).comp (map (Int.castRingHom ℂ)) = σ.comp (aeval y : MRing ι →ₐ[ℤ] Ω).toRingHom :=
    MvPolynomial.ringHom_ext (fun n => by simp) (fun p => by simp)
  exact congrArg (fun φ => φ f) this

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem mem_mcPts (σ : Ω →+* ℂ) (y : (Σ k, ι k) → Ω) {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    (fun p => σ (y p)) ∈ mcPts (mCoordIdeal y) :=
  ⟨fun k => ⟨c k, (map_ne_zero σ).mpr (hc k)⟩, fun f hf => by rw [eval_comp, aeval_eq_zero_of_mem y hf, map_zero]⟩

theorem eval_smul (w : (Σ k, ι k) → ℂ) (l : K → ℂ) {f : MRing ι} {d : K → ℕ} (hf : IsMultiHomog f d) :
    eval (fun p => l p.1 * w p) (map (Int.castRingHom ℂ) f) = (∏ k, l k ^ d k) * eval w (map (Int.castRingHom ℂ) f) := by
  have hc : (MvPolynomial.eval l).comp (mConeMap w).toRingHom = (aeval (fun p => l p.1 * w p)).toRingHom :=
    MvPolynomial.ringHom_ext (fun n => by simp) (fun p => by simp [mConeMap, mul_comm])
  have h1 := congrArg (MvPolynomial.eval l) (ConeTrdeg.mConeMap_of_isMultiHomog w hf)
  have h2 := congrArg (fun φ => φ f) hc
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h2
  rw [eval_map_eq_aeval, eval_map_eq_aeval, ← h2, h1, map_mul, eval_C, map_prod]
  simp only [map_pow, eval_X]
  ring

theorem exists_sameOrbit {y : (Σ k, ι k) → Ω} (hP : IsArithVar (mCoordIdeal y) 1) (hB : Birational y)
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) : ∃ σ : Ω →+* ℂ, SameOrbit z (fun p => σ (y p)) := by
  classical
  set P := mCoordIdeal y
  let φ : MRing ι →+* ℂ := (eval z).comp (map (Int.castRingHom ℂ))
  have hne : ∀ (v : MRing ι) (a : K → ℕ), IsMultiHomog v a → aeval y v ≠ 0 → φ v ≠ 0 := fun v a hv hv0 =>
    eval_ne_zero_of_dimOne arithVarZero hP
      (A := HermLine.ofMetrics (fun k => fsMetric (ι k)) (fun k => (a k : ℤ)))
      ⟨a, fun _ => rfl, hv, fun hm => hv0 (aeval_eq_zero_of_mem y hm)⟩ hz
  choose d g h hg hh hh0 hgh using hB
  let σf : Ω → ℂ := fun s => φ (g s) / φ (h s)
  have hhz : ∀ s, φ (h s) ≠ 0 := fun s => hne _ _ (hh s) (hh0 s)

  have rep : ∀ (s : Ω) (e : K → ℕ) (G H : MRing ι), IsMultiHomog G e → IsMultiHomog H e → aeval y H ≠ 0 →
      aeval y G = s * aeval y H → σf s * φ H = φ G := by
    intro s e G H hG hH hH0 hGs
    have hmem : G * h s - H * g s ∈ P :=
      mem_of_aeval_eq_zero y (isMultiHomog_sub (isMultiHomog_mul hG (hh s)) (isMultiHomog_mul hH (hg s)))
        (by rw [map_sub, map_mul, map_mul, hGs, hgh s]; ring)
    have h1 : φ G * φ (h s) = φ H * φ (g s) := by
      have : φ (G * h s - H * g s) = 0 := hz.2 _ hmem
      rw [map_sub, map_mul, map_mul] at this
      exact sub_eq_zero.mp this
    simp only [σf]
    field_simp [hhz s]
    linear_combination h1.symm
  have hsub : ∀ s t, aeval y (h s * h t) ≠ 0 := fun s t => by rw [map_mul]; exact mul_ne_zero (hh0 s) (hh0 t)
  let σ : Ω →+* ℂ :=
    { toFun := σf
      map_one' := by
        have := rep 1 0 1 1 isMultiHomog_one isMultiHomog_one (by simp) (by simp)
        simpa using this
      map_mul' := fun s t => by
        have := rep (s * t) (d s + d t) (g s * g t) (h s * h t) (isMultiHomog_mul (hg s) (hg t)) (isMultiHomog_mul (hh s) (hh t)) (hsub s t)
          (by rw [map_mul, map_mul, hgh s, hgh t]; ring)
        have hs := rep s _ _ _ (hg s) (hh s) (hh0 s) (hgh s)
        have ht := rep t _ _ _ (hg t) (hh t) (hh0 t) (hgh t)
        rw [map_mul, map_mul, ← hs, ← ht] at this
        exact mul_right_cancel₀ (mul_ne_zero (hhz s) (hhz t)) (by linear_combination this)
      map_zero' := by
        have := rep 0 0 0 1 (fun m hm => by simp at hm) isMultiHomog_one (by simp) (by simp)
        simpa using this
      map_add' := fun s t => by
        have := rep (s + t) (d s + d t) (g s * h t + h s * g t) (h s * h t) (isMultiHomog_add (isMultiHomog_mul (hg s) (hh t)) (isMultiHomog_mul (hh s) (hg t)))
          (isMultiHomog_mul (hh s) (hh t)) (hsub s t)
          (by rw [map_add, map_mul, map_mul, map_mul, hgh s, hgh t]; ring)
        have hs := rep s _ _ _ (hg s) (hh s) (hh0 s) (hgh s)
        have ht := rep t _ _ _ (hg t) (hh t) (hh0 t) (hgh t)
        rw [map_add, map_mul, map_mul, map_mul, ← hs, ← ht] at this
        exact mul_right_cancel₀ (mul_ne_zero (hhz s) (hhz t)) (by linear_combination this) }
  obtain ⟨j, -, hj⟩ := exists_chart hP
  have hzj : ∀ k, z ⟨k, j k⟩ ≠ 0 := fun k => by
    simpa [φ] using hne _ _ (regularityEmbedding_holds.isMultiHomog_X_single k (j k)) (by simpa using hj k)
  refine ⟨σ, fun k => z ⟨k, j k⟩ / σ (y ⟨k, j k⟩), fun k => div_ne_zero (hzj k) ((map_ne_zero σ).mpr (hj k)), ?_⟩
  funext p
  have hr := rep (y p / y ⟨p.1, j p.1⟩) _ _ _ (regularityEmbedding_holds.isMultiHomog_X_single p.1 p.2)
    (regularityEmbedding_holds.isMultiHomog_X_single p.1 (j p.1)) (by simpa using hj p.1) (by simp [div_mul_cancel₀ _ (hj p.1)])
  have hσ : σf (y p / y ⟨p.1, j p.1⟩) = σ (y p) / σ (y ⟨p.1, j p.1⟩) := map_div₀ σ _ _
  rw [hσ] at hr
  simp only [φ, RingHom.comp_apply, map_X, eval_X] at hr
  have hr' : σ (y p) / σ (y ⟨p.1, j p.1⟩) * z ⟨p.1, j p.1⟩ = z p := hr
  show z p = z ⟨p.1, j p.1⟩ / σ (y ⟨p.1, j p.1⟩) * σ (y p)
  rw [← hr']
  ring

end CurveOrbit

end

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PFibreMultiHomog
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
  GroundTheory.Heights₂.Heights.Inter.FibreMultiHomogeneous

attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem FibreMultiHomog.proof : FibreMultiHomog.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' G hv hP
  classical
  refine cyc_isMultiHomogIdeal_of_isHomogeneous fun k n f hf => ?_
  rw [show (DirectSum.decompose (weightedHomogeneousSubmodule G.Φ (cycBlockWt k)) f n : MvPolynomial _ G.Φ) =
    weightedHomogeneousComponent (cycBlockWt k) n f from MvPolynomial.decompose'_apply _ _ f n]
  obtain ⟨b, hb, F, e⟩ := exists_clear G f
  rw [fibreIdeal, RingHom.mem_ker] at hf ⊢
  have hF : liftZ κ v F ∈ P' := by
    rw [← G.genericFibre_ker_target, RingHom.mem_ker, aeval_liftZ, ← e, map_mul, aeval_C]
    simp [hf]
  have hc : weightedHomogeneousComponent (cycBlockWt k.1) n (liftZ κ v F) ∈ P' := by
    have hH := cyc_isHomogeneous_of_isMultiHomogIdeal hP k.1
    have := hH n hF
    rwa [show (DirectSum.decompose (weightedHomogeneousSubmodule ℤ (cycBlockWt k.1)) (liftZ κ v F) n : MRing ι') =
      weightedHomogeneousComponent (cycBlockWt k.1) n (liftZ κ v F) from
        MvPolynomial.decompose'_apply _ _ (liftZ κ v F) n] at this
  rw [liftZ_component hv, ← G.genericFibre_ker_target, RingHom.mem_ker, aeval_liftZ, ← component_map, ← e,
    weightedHomogeneousComponent_C_mul, map_mul, aeval_C] at hc
  exact (mul_eq_zero.1 hc).resolve_left ((map_ne_zero _).2 hb)

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsPosDensIntegrable
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo

theorem PtsPosDensIntegrable.proof (hMass : PtsSemiPosMassFinite.Statement) : PtsPosDensIntegrable.Statement := by
  intro K _ ι _ P e Ψ L g hP hΨ hL hg
  classical
  obtain ⟨M, hMb⟩ := PtsPosDens.exists_bound hg
  choose T hTs hTp hLTp using fun j => Inter.SemiPosTwist.proof Inter.TorusInvLevi.proof K ι (L j) (hL j)
  set N : Fin e → HermLine ι := fun j => ((L j).tensor (T j)).tensor (T j) with hNdef
  have hLT : ∀ j, IsSmoothHerm ((L j).tensor (T j)) := fun j =>
    ReciprocityTheory.ChartRestriction.G.Geo.isSmoothHerm_tensor (hL j) (hTs j)
  have hNs : ∀ j, IsSmoothHerm (N j) := fun j => ReciprocityTheory.ChartRestriction.G.Geo.isSmoothHerm_tensor (hLT j) (hTs j)
  have hNp : ∀ j, Inter.IsSemiPosHerm (N j) := fun j =>
    PtsPosDens.isSemiPosHerm_tensor (hLT j) (hTs j) (hLTp j) (hTp j)
  have hfinM := hMass K ι P e Ψ N hP hΨ hNs hNp
  have hfib := fibreFinite K ι P e Ψ hP hΨ
  set C : ℝ := max M 0 * 3 ^ e with hCdef
  have hC : 0 ≤ C := by positivity

  have key : ∀ y w, max (sheetDensity P Ψ (pot L) g y w) 0 ≤
      C * max (sheetDensity P Ψ (pot N) (fun _ => 1) y w) 0 := by
    intro y w
    unfold sheetDensity
    by_cases hγ : ∃ γ, IsSheet P Ψ y w γ
    · rw [dif_pos hγ, dif_pos hγ]
      have hS := hγ.choose_spec
      have hab : |maDensity (fun j y' => pot L j (hγ.choose y')) y| ≤
          3 ^ e * maDensity (fun j y' => pot N j (hγ.choose y')) y :=
        Inter.PointsAbsIntegrable.abs_maDensity_le hL hTs hTp hLTp hS
      have hmc : hγ.choose y ∈ mcPts P := hS.2.self_of_nhds.2.1
      have hgb : |g (hγ.choose y)| ≤ max M 0 := (hMb _ hmc.1).trans (le_max_left _ _)
      have hn : 0 ≤ maDensity (fun j y' => pot N j (hγ.choose y')) y :=
        nonneg_of_mul_nonneg_right ((abs_nonneg _).trans hab) (by positivity)
      calc max (g (hγ.choose y) * maDensity (fun j y' => pot L j (hγ.choose y')) y) 0
          ≤ |g (hγ.choose y) * maDensity (fun j y' => pot L j (hγ.choose y')) y| :=
            max_le (le_abs_self _) (abs_nonneg _)
        _ = |g (hγ.choose y)| * |maDensity (fun j y' => pot L j (hγ.choose y')) y| := abs_mul _ _
        _ ≤ max M 0 * (3 ^ e * maDensity (fun j y' => pot N j (hγ.choose y')) y) :=
            mul_le_mul hgb hab (abs_nonneg _) (le_max_right _ _)
        _ = C * max (1 * maDensity (fun j y' => pot N j (hγ.choose y')) y) 0 := by
            rw [one_mul, max_eq_left hn, hCdef]
            ring
    · rw [dif_neg hγ, dif_neg hγ, max_self, mul_zero]

  have hpt : ∀ y, ENNReal.ofReal (ptsPosDens P Ψ (pot L) g y) ≤
      ENNReal.ofReal C * ENNReal.ofReal (ptsPosDens P Ψ (pot N) (fun _ => 1) y) := by
    intro y
    rw [← ENNReal.ofReal_mul hC]
    refine ENNReal.ofReal_le_ofReal ?_
    unfold ptsPosDens
    rw [finsum_mem_eq_finite_toFinset_sum _ (hfib y), finsum_mem_eq_finite_toFinset_sum _ (hfib y),
      Finset.mul_sum]
    exact Finset.sum_le_sum fun w _ => key y w
  have hnn : ∀ y, 0 ≤ ptsPosDens P Ψ (pot L) g y := fun y =>
    finsum_nonneg fun w => finsum_nonneg fun _ => le_max_right _ _
  refine ⟨PtsPosDens.aestronglyMeasurable hP hΨ hL hg, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hnn)]
  calc ∫⁻ y, ENNReal.ofReal (ptsPosDens P Ψ (pot L) g y)
      ≤ ∫⁻ y, ENNReal.ofReal C * ENNReal.ofReal (ptsPosDens P Ψ (pot N) (fun _ => 1) y) := lintegral_mono hpt
    _ = ENNReal.ofReal C * ∫⁻ y, ENNReal.ofReal (ptsPosDens P Ψ (pot N) (fun _ => 1) y) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfinM

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PotFinCons
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

theorem pot_fin_cons {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ} (M : HermLine ι)
    (L : Fin e → HermLine ι) :
    pot (Fin.cons M L : Fin (e + 1) → HermLine ι) = Fin.cons (fun z => Real.log (M.h z)) (pot L) := by
  funext j z
  refine Fin.cases ?_ (fun i => ?_) j <;> simp [pot]

theorem PoincareLelongRegularised.proof (hInt : PtsIntegrableStatement)
    (hMeas : GroundTheory.Heights₂.Heights.Inter.PtsAbsMeasurable.Statement) : PoincareLelongRegularised.Statement := by
  intro K _ ι _ P n L A B s hP hL hA hB _ hs
  obtain ⟨a, ha, hsa, hsP⟩ := id hs
  have hM : ∀ j, IsSmoothHerm ((Fin.cons B L : Fin (n + 1) → HermLine ι) j) := fun j =>
    Fin.cases (by simpa using hB) (fun i => by simpa using hL i) j
  have hlim := GroundTheory.Heights₂.Heights.Inter.PtsRegLimit.proof hInt
    (GroundTheory.Heights₂.Heights.Inter.PtsAbsIntegrable.proof hInt hMeas) K ι P (n + 1) (Fin.cons B L) A s
    ⟨a, ha, hsa⟩ hP hM hA hsP
  rw [pot_fin_cons] at hlim
  have hg : ∀ ε, (fun z => Real.log ((GroundTheory.Heights₂.Heights.Inter.regLine A s ⟨a, ha, hsa⟩ ε).h z)) =
      regLog A s ε := by
    intro ε
    funext z
    rw [GroundTheory.Heights₂.Heights.Inter.log_regLine_h]
    rfl
  simpa only [hg] using hlim

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCurveBoxCount
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.Inter

def CurveBoxCount.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (c : ∀ k, ι k) (R : Finset ((Σ k, ι k) → ℂ)),
    IsArithVar (mCoordIdeal y) 1 → Birational y → IsConjInvariantH A → (∀ k, y ⟨k, c k⟩ ≠ 0) →
    (∀ t ∈ R, t ∈ mcPts (mCoordIdeal y)) → (∀ z ∈ mcPts (mCoordIdeal y), ∃! t, t ∈ R ∧ SameOrbit z t) →
    ∃ C : ℝ, ∀ τ : ℕ, 1 ≤ τ →
      (τ : ℝ) * ∑ t ∈ R, Real.log (chartRadius A c t) + chartIndexLog y c A.a τ - C ≤
        smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) τ

namespace CurveBoxCount

end CurveBoxCount

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCurveClosedPointChart
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def CurveClosedPointChart.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω), IsArithVar (mCoordIdeal y) 1 →
      ∀ m : Ideal (curveRing y), m.IsMaximal → ∃ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) ∧
        ∀ p : Σ k, ι k, ∃ a b : curveRing y, b ∉ m ∧ (b : Ω) * (y p / y ⟨p.1, c p.1⟩) = a

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCurveDegreeVert
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GroundTheory.Heights₂.Heights.Inter

def CurveDegreeVert.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι))
    (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (II : IntersectionSystem) (c : ∀ k, ι k)
    (R : Finset ((Σ k, ι k) → ℂ)) (b d : K → ℕ),
    IsIntersectionSystem II → IsArithVar P 1 → IsSmoothHerm A → (∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ P) →
    (∀ t ∈ R, t ∈ mcPts P) → (∀ z ∈ mcPts P, ∃! t, t ∈ R ∧ SameOrbit z t) →
    (∀ k, (d k : ℤ) = A.a k + b k) →
    II K ι P 1 (fun _ => A) =
      vertR P (Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (curveChartMono c d) -
        vertR P (Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (curveChartMono c b) +
        ∑ t ∈ R, Real.log (chartRadius A c t)

namespace CurveDegreeVert

end CurveDegreeVert

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCurveIndexLinear
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def CurveIndexLinear.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k),
    IsArithVar (mCoordIdeal y) 1 → (∀ k, y ⟨k, c k⟩ ≠ 0) →
      (∀ a a' : K → ℤ, chartIndexLog y c (a + a') 1 = chartIndexLog y c a 1 + chartIndexLog y c a' 1) ∧
      ∀ (a : K → ℤ) (τ : ℕ), chartIndexLog y c a τ = τ * chartIndexLog y c a 1

namespace CurveIndexLinear

end CurveIndexLinear

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCurveRingFinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def CurveRingFinite.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω), IsArithVar (mCoordIdeal y) 1 → Module.Finite ℤ (curveRing y)

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCurveVertIndex
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

def CurveVertIndex.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (s : MRing ι) (d : K → ℕ),
    IsArithVar (mCoordIdeal y) 1 → IsMultiHomog s d → s ∉ mCoordIdeal y →
      vertR (mCoordIdeal y) (Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) s =
        Real.log (genIndex (chartLat y (fun k => (d k : ℤ)) 1) (curveMul y (aeval y s)))

namespace CurveVertIndex

end CurveVertIndex

end GroundTheory.Heights₂.Heights.Targets
end

