import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.Bundle0006
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RightRegularIsometricMultiplicative
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyProjectorSectionLocal

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.PjTrInnerPure
section
noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Matrix Finset
open scoped InnerProductSpace ComplexOrder ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

section

variable (X : CData) {n₀ : ℕ} {A : ℝ} (hX : X.HypB n₀ A)

include hX

theorem pj_tr_U (v : InfinitePlace X.I.F) : IsURepOn (UJset (X.I.ε v)) (X.σ v) := (hX.2.1.1 v).2.2.1

theorem pj_tr_ext {M : Type*} [NormedAddCommGroup M] [NormedSpace ℂ M] (S T : X.Hs →L[ℂ] M)
    (h : ∀ x, S (X.tens x) = T (X.tens x)) : S = T :=
  ContinuousLinearMap.ext_on hX.2.1.2.2.1.2.2 (by rintro _ ⟨x, rfl⟩; exact h x)

theorem pj_tr_zero (z : X.Hs) (h : ∀ y, ⟪X.tens y, z⟫_ℂ = 0) : z = 0 := by
  refine hX.2.1.2.2.1.2.2.eq_zero_of_inner_right ℂ fun u hu => ?_
  have hle : Submodule.span ℂ (Set.range X.tens) ≤ (Submodule.span ℂ {z})ᗮ := by
    rw [Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    exact Submodule.mem_orthogonal_singleton_iff_inner_left.2 (h y)
  exact Submodule.mem_orthogonal_singleton_iff_inner_left.1 (hle hu)

theorem pj_tr_mul (g h : X.I.Ginf) : X.σs (g * h) = X.σs g ∘L X.σs h := by
  refine pj_tr_ext X hX _ _ fun x => ?_
  have hT := hX.2.1.2.2.1.2.1
  rw [ContinuousLinearMap.comp_apply, hT, hT, hT]
  congr 1
  funext v
  exact rep_mul_apply' (homOf (X.σ v) (pj_tr_U X hX v)) (g v) (h v) (x v)

theorem pj_tr_one : X.σs 1 = 1 := by
  refine pj_tr_ext X hX _ _ fun x => ?_
  rw [hX.2.1.2.2.1.2.1]
  show X.tens _ = X.tens x
  congr 1
  funext v
  exact rep_one_apply' (homOf (X.σ v) (pj_tr_U X hX v)) (x v)

theorem pj_tr_inner_pure (g : X.I.Ginf) (x y : ∀ v, X.H v) :
    ⟪X.σs g (X.tens x), X.σs g (X.tens y)⟫_ℂ = ⟪X.tens x, X.tens y⟫_ℂ := by
  have hT := hX.2.1.2.2.1
  rw [hT.2.1, hT.2.1, hT.1, hT.1]
  refine Finset.prod_congr rfl fun v _ => ?_
  exact unitary_rep_inner_map (homOf (X.σ v) (pj_tr_U X hX v)) (homOf_norm (X.σ v) (pj_tr_U X hX v)) (g v) (x v) (y v)

theorem pj_tr_adj (g : X.I.Ginf) : ContinuousLinearMap.adjoint (X.σs g) ∘L X.σs g = 1 := by
  refine pj_tr_ext X hX _ _ fun x => ?_
  rw [← sub_eq_zero]
  refine pj_tr_zero X hX _ fun y => ?_
  rw [inner_sub_right, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    pj_tr_inner_pure X hX, one_apply_eq_self, sub_self]

theorem pj_tr_norm (g : X.I.Ginf) (x : X.Hs) : ‖X.σs g x‖ = ‖x‖ := by
  have h : ⟪X.σs g x, X.σs g x⟫_ℂ = ⟪x, x⟫_ℂ := by
    rw [← ContinuousLinearMap.adjoint_inner_right]
    have := congrArg (fun T : X.Hs →L[ℂ] X.Hs => T x) (pj_tr_adj X hX g)
    simp only [ContinuousLinearMap.comp_apply, one_apply_eq_self] at this
    rw [this]
  have h2 : ‖X.σs g x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ), h]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h2

theorem pj_tr_cont_pure (x : ∀ v, X.H v) : Continuous fun g => X.σs g (X.tens x) := by
  have hT := hX.2.1.2.2.1
  set a : X.I.Ginf → ∀ v, X.H v := fun g v => X.σ v (uMat (g v)) (x v) with ha
  have hac : ∀ v, Continuous fun g : X.I.Ginf => a g v := fun v =>
    (homOf_cont (X.σ v) (pj_tr_U X hX v) (x v)).comp (continuous_apply v)
  have hfun : (fun g => X.σs g (X.tens x)) = fun g => X.tens (a g) := funext fun g => hT.2.1 g x
  rw [hfun, continuous_iff_continuousAt]
  intro g0
  set F : X.I.Ginf → ℂ := fun g => (∏ v, ⟪a g v, a g v⟫_ℂ) - (∏ v, ⟪a g v, a g0 v⟫_ℂ) - (∏ v, ⟪a g0 v, a g v⟫_ℂ) +
    ∏ v, ⟪a g0 v, a g0 v⟫_ℂ with hF
  have hFc : Continuous F := by
    refine ((Continuous.sub ?_ ?_).sub ?_).add continuous_const
    · exact continuous_finsetProd _ fun v _ => (hac v).inner (hac v)
    · exact continuous_finsetProd _ fun v _ => (hac v).inner continuous_const
    · exact continuous_finsetProd _ fun v _ => continuous_const.inner (hac v)
  have hN : ∀ g, ‖X.tens (a g) - X.tens (a g0)‖ = Real.sqrt (RCLike.re (F g)) := by
    intro g
    rw [← Real.sqrt_sq (norm_nonneg (X.tens (a g) - X.tens (a g0))), ← inner_self_eq_norm_sq (𝕜 := ℂ),
      inner_sub_left, inner_sub_right, inner_sub_right, hT.1, hT.1, hT.1, hT.1]
    congr 2
    simp only [hF]
    ring
  have hF0 : F g0 = 0 := by simp only [hF]; ring
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  simp only [hN]
  have hc : Continuous fun g => Real.sqrt (RCLike.re (F g)) := Real.continuous_sqrt.comp (RCLike.continuous_re.comp hFc)
  have := hc.tendsto g0
  simpa [hF0] using this

theorem pj_tr_cont (x : X.Hs) : Continuous fun g => X.σs g x := by
  have hspan : ∀ y ∈ Submodule.span ℂ (Set.range X.tens), Continuous fun g => X.σs g y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨z, rfl⟩ := hy
      exact pj_tr_cont_pure X hX z
    | zero => simpa using continuous_const
    | add y z _ _ h1 h2 =>
      simp only [map_add]
      exact h1.add h2
    | smul c y _ h1 =>
      simp only [map_smul]
      exact h1.const_smul c
  refine continuous_of_uniform_approx_of_continuous fun u hu => ?_
  obtain ⟨ε, hε, hu⟩ := Metric.mem_uniformity_dist.1 hu
  obtain ⟨y, hy, hd⟩ := Metric.mem_closure_iff.1 (hX.2.1.2.2.1.2.2 x) ε hε
  refine ⟨fun g => X.σs g y, hspan y hy, fun g => hu ?_⟩
  rw [dist_eq_norm, ← map_sub, pj_tr_norm X hX, ← dist_eq_norm]
  exact hd

theorem pj_tensRep : TensRep X :=
  ⟨pj_tr_mul X hX, pj_tr_one X hX, pj_tr_norm X hX, pj_tr_cont X hX⟩

end

end Formalism.MainNotions.LeviCoordinates

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RrkpCoefCont
section
noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Set
open scoped InnerProductSpace ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

theorem rrkp_coef_cont {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (h : IsURepOn (UJset ε) σ) (w : H) :
    Continuous (coefOn (ε := ε) σ w w) :=
  continuous_const.inner (homOf_cont σ h w)

theorem rrk_phi_meas (X : CData) {n₀ : ℕ} {A : ℝ} (hX : X.HypB n₀ A) : Measurable X.φ := by
  have he : Measurable X.e := (hX.1.2.2.2.2.2.2.1.1).continuous.measurable
  have hc : ∀ v, Measurable (coefOn (ε := X.I.ε v) (X.σ v) (X.w v) (X.w v)) := fun v =>
    (rrkp_coef_cont (hX.2.1.1 v).2.2.1 (X.w v)).measurable
  have hp : Measurable (phOf X.I X.σ X.w) := by
    unfold phOf
    refine measurable_const.mul (continuous_star.measurable.comp ?_)
    exact Finset.measurable_prod _ fun v _ => (hc v).comp (measurable_pi_apply v)
  unfold CData.φ phe
  exact (hp.comp measurable_fst).mul (he.comp measurable_snd)

theorem rrkp_loc (D : Formalism.BasicNotions.D7) (hloc : LocalProjectorRealPlace D) (X : CData) {n₀ : ℕ} {A : ℝ} (hX : X.HypB n₀ A) (h1 : X.GapAboveThreeHalvesPower)
    (v : InfinitePlace X.I.F) :
    (∀ g : Formalism.REAL.UJ (X.I.ε v), phLoc (X.I.ε v) (X.σ v) (X.w v) g⁻¹ = star (phLoc (X.I.ε v) (X.σ v) (X.w v) g)) ∧
      ∀ y : Formalism.REAL.UJ (X.I.ε v),
        ∫ g, phLoc (X.I.ε v) (X.σ v) (X.w v) g * phLoc (X.I.ε v) (X.σ v) (X.w v) (g⁻¹ * y) ∂(Formalism.REAL.muG (X.I.ε v)) =
          phLoc (X.I.ε v) (X.σ v) (X.w v) y := by
  obtain ⟨-, h2, h3, -⟩ := hloc X.I.n (X.I.ε v) (X.lam v) (hX.1.2.2.2.2.1 v) (X.H v) (X.σ v) (hX.2.1.1 v) (X.w v)
    (hX.2.1.2.1 v) X.h (hX.2.2 v) (h1 v)
  refine ⟨fun g => ?_, fun y => ?_⟩
  · rw [← h2 g, star_star]
  · have h := h3 1 y
    have hm : coefOn (X.σ v) (X.w v) (X.w v) (1 : Formalism.REAL.UJ (X.I.ε v)) = 1 := by
      have hσ : X.σ v 1 = 1 := (hX.2.1.1 v).2.2.1.1.1
      have hu : umat (1 : Formalism.REAL.UJ (X.I.ε v)) = 1 := rfl
      unfold coefOn
      rw [hu, hσ, one_apply_eq_self, inner_self_eq_norm_sq_to_K, (hX.2.1.2.1 v).1]
      simp
    rw [hm, one_mul] at h
    rw [← h]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp

theorem rrk_phi_star (D : Formalism.BasicNotions.D7) (hloc : LocalProjectorRealPlace D) (X : CData) {n₀ : ℕ} {A : ℝ} (hX : X.HypB n₀ A)
    (h1 : X.GapAboveThreeHalvesPower) (z : X.I.GA) : X.φ z⁻¹ = star (X.φ z) := by
  have he : ∀ x, X.e x⁻¹ = star (X.e x) := hX.1.2.2.2.2.2.2.1.2.2.1
  unfold CData.φ phe
  rw [star_mul', X.phOf_eq_prod, X.phOf_eq_prod]
  have e1 : (z⁻¹).2 = (z.2)⁻¹ := rfl
  rw [e1, he]
  congr 1
  have e2 : star (∏ v, phLoc (X.I.ε v) (X.σ v) (X.w v) (z.1 v)) =
      ∏ v, star (phLoc (X.I.ε v) (X.σ v) (X.w v) (z.1 v)) := map_prod (starRingEnd ℂ) _ _
  rw [e2]
  refine Finset.prod_congr rfl fun v _ => ?_
  exact (rrkp_loc D hloc X hX h1 v).1 (z.1 v)

theorem rrk_phi_idem (D : Formalism.BasicNotions.D7) (hloc : LocalProjectorRealPlace D) (X : CData) {n₀ : ℕ} {A : ℝ} (hX : X.HypB n₀ A)
    (h1 : X.GapAboveThreeHalvesPower) (z : X.I.GA) : ∫ g, X.φ g * X.φ (g⁻¹ * z) ∂(X.I.muA X.μf) = X.φ z := by
  have he : X.I.convF X.μf X.e X.e = X.e := hX.1.2.2.2.2.2.2.1.2.1
  have he' : ∫ y, X.e y * X.e (y⁻¹ * z.2) ∂X.μf = X.e z.2 := congrFun he z.2
  have hfun : (fun g : X.I.GA => X.φ g * X.φ (g⁻¹ * z)) = fun g : X.I.GA =>
      (fun a : X.I.Ginf => ∏ v, (phLoc (X.I.ε v) (X.σ v) (X.w v) (a v) *
        phLoc (X.I.ε v) (X.σ v) (X.w v) ((a v)⁻¹ * z.1 v))) g.1 *
      (fun y : X.I.Gf => X.e y * X.e (y⁻¹ * z.2)) g.2 := by
    funext g
    unfold CData.φ phe
    beta_reduce
    rw [X.phOf_eq_prod, X.phOf_eq_prod, Finset.prod_mul_distrib]
    have e1 : (g⁻¹ * z).2 = (g.2)⁻¹ * z.2 := rfl
    have e2 : ∀ v, (g⁻¹ * z).1 v = (g.1 v)⁻¹ * z.1 v := fun v => rfl
    simp only [e1, e2]
    ring
  rw [hfun]
  unfold AutInst.muA
  refine (integral_prod_mul (μ := Measure.pi fun v => Formalism.REAL.muG (X.I.ε v)) (ν := X.μf)
    (fun a : X.I.Ginf => ∏ v, (phLoc (X.I.ε v) (X.σ v) (X.w v) (a v) *
        phLoc (X.I.ε v) (X.σ v) (X.w v) ((a v)⁻¹ * z.1 v)))
    (fun y : X.I.Gf => X.e y * X.e (y⁻¹ * z.2))).trans ?_
  rw [he', integral_fintype_prod_eq_prod (fun v (a : Formalism.REAL.UJ (X.I.ε v)) =>
    phLoc (X.I.ε v) (X.σ v) (X.w v) a * phLoc (X.I.ε v) (X.σ v) (X.w v) (a⁻¹ * z.1 v))]
  unfold CData.φ phe
  rw [X.phOf_eq_prod]
  congr 1
  exact Finset.prod_congr rfl fun v _ => (rrkp_loc D hloc X hX h1 v).2 (z.1 v)

end Formalism.MainNotions.LeviCoordinates

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.SchurRelationAddSecond
section
noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Matrix Finset
open scoped InnerProductSpace ComplexOrder ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

section Q

variable {G : Type} [MeasurableSpace G] (μ : Measure G) {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
  (σ : G → (Hs →L[ℂ] Hs)) (d : ℝ)

def pj_Q (x y x' y' : Hs) : Prop :=
  Integrable (fun g => ⟪y, σ g x⟫_ℂ * star ⟪y', σ g x'⟫_ℂ) μ ∧
    ∫ g, ⟪y, σ g x⟫_ℂ * star ⟪y', σ g x'⟫_ℂ ∂μ = ⟪x', x⟫_ℂ * ⟪y, y'⟫_ℂ / (d : ℂ)

variable {μ σ d}

theorem pj_Q_zero1 (y x' y' : Hs) : pj_Q μ σ d 0 y x' y' := by
  unfold pj_Q
  simp

theorem schur_relation_add_first {x1 x2 y x' y' : Hs} (h1 : pj_Q μ σ d x1 y x' y') (h2 : pj_Q μ σ d x2 y x' y') :
    pj_Q μ σ d (x1 + x2) y x' y' := by
  have e : (fun g => ⟪y, σ g (x1 + x2)⟫_ℂ * star ⟪y', σ g x'⟫_ℂ) =
      fun g => ⟪y, σ g x1⟫_ℂ * star ⟪y', σ g x'⟫_ℂ + ⟪y, σ g x2⟫_ℂ * star ⟪y', σ g x'⟫_ℂ := by
    funext g
    rw [map_add, inner_add_right, add_mul]
  unfold pj_Q
  rw [e]
  refine ⟨h1.1.add h2.1, ?_⟩
  rw [integral_add h1.1 h2.1, h1.2, h2.2, inner_add_right]
  ring

theorem pj_Q_smul1 {x y x' y' : Hs} (a : ℂ) (h1 : pj_Q μ σ d x y x' y') : pj_Q μ σ d (a • x) y x' y' := by
  have e : (fun g => ⟪y, σ g (a • x)⟫_ℂ * star ⟪y', σ g x'⟫_ℂ) =
      fun g => a * (⟪y, σ g x⟫_ℂ * star ⟪y', σ g x'⟫_ℂ) := by
    funext g
    rw [map_smul, inner_smul_right, mul_assoc]
  unfold pj_Q
  rw [e]
  refine ⟨h1.1.const_mul a, ?_⟩
  rw [integral_const_mul, h1.2, inner_smul_right]
  ring

theorem pj_Q_zero2 (x x' y' : Hs) : pj_Q μ σ d x 0 x' y' := by
  unfold pj_Q
  simp

theorem schur_relation_add_second {x y1 y2 x' y' : Hs} (h1 : pj_Q μ σ d x y1 x' y') (h2 : pj_Q μ σ d x y2 x' y') :
    pj_Q μ σ d x (y1 + y2) x' y' := by
  have e : (fun g => ⟪y1 + y2, σ g x⟫_ℂ * star ⟪y', σ g x'⟫_ℂ) =
      fun g => ⟪y1, σ g x⟫_ℂ * star ⟪y', σ g x'⟫_ℂ + ⟪y2, σ g x⟫_ℂ * star ⟪y', σ g x'⟫_ℂ := by
    funext g
    rw [inner_add_left, add_mul]
  unfold pj_Q
  rw [e]
  refine ⟨h1.1.add h2.1, ?_⟩
  rw [integral_add h1.1 h2.1, h1.2, h2.2, inner_add_left]
  ring

theorem pj_Q_smul2 {x y x' y' : Hs} (a : ℂ) (h1 : pj_Q μ σ d x y x' y') : pj_Q μ σ d x (a • y) x' y' := by
  have e : (fun g => ⟪a • y, σ g x⟫_ℂ * star ⟪y', σ g x'⟫_ℂ) =
      fun g => (starRingEnd ℂ) a * (⟪y, σ g x⟫_ℂ * star ⟪y', σ g x'⟫_ℂ) := by
    funext g
    rw [inner_smul_left, mul_assoc]
  unfold pj_Q
  rw [e]
  refine ⟨h1.1.const_mul _, ?_⟩
  rw [integral_const_mul, h1.2, inner_smul_left]
  ring

theorem pj_Q_symm {x y x' y' : Hs} (h : pj_Q μ σ d x y x' y') : pj_Q μ σ d x' y' x y := by
  have e : (fun g => ⟪y', σ g x'⟫_ℂ * star ⟪y, σ g x⟫_ℂ) =
      fun g => (starRingEnd ℂ) (⟪y, σ g x⟫_ℂ * star ⟪y', σ g x'⟫_ℂ) := by
    funext g
    rw [map_mul, ← starRingEnd_apply, ← starRingEnd_apply, Complex.conj_conj, mul_comm]
  unfold pj_Q
  rw [e]
  refine ⟨(Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp h.1, ?_⟩
  rw [integral_conj, h.2, map_div₀, map_mul, inner_conj_symm, inner_conj_symm, Complex.conj_ofReal]

theorem schur_relation_span {S : Set Hs} {x' y' : Hs} (hS : ∀ a ∈ S, ∀ b ∈ S, pj_Q μ σ d a b x' y') :
    ∀ x ∈ Submodule.span ℂ S, ∀ y ∈ Submodule.span ℂ S, pj_Q μ σ d x y x' y' := by
  have h1 : ∀ x ∈ Submodule.span ℂ S, ∀ b ∈ S, pj_Q μ σ d x b x' y' := by
    intro x hx b hb
    induction hx using Submodule.span_induction with
    | mem a ha => exact hS a ha b hb
    | zero => exact pj_Q_zero1 _ _ _
    | add u v _ _ hu hv => exact schur_relation_add_first hu hv
    | smul a u _ hu => exact pj_Q_smul1 a hu
  intro x hx y hy
  induction hy using Submodule.span_induction with
  | mem b hb => exact h1 x hx b hb
  | zero => exact pj_Q_zero2 _ _ _
  | add u v _ _ hu hv => exact schur_relation_add_second hu hv
  | smul a u _ hu => exact pj_Q_smul2 a hu

theorem pj_Q_span {S : Set Hs} (hS : ∀ a ∈ S, ∀ b ∈ S, ∀ a' ∈ S, ∀ b' ∈ S, pj_Q μ σ d a b a' b') :
    ∀ x ∈ Submodule.span ℂ S, ∀ y ∈ Submodule.span ℂ S, ∀ x' ∈ Submodule.span ℂ S, ∀ y' ∈ Submodule.span ℂ S,
      pj_Q μ σ d x y x' y' := by
  intro x hx y hy
  refine fun x' hx' y' hy' => pj_Q_symm ?_
  refine schur_relation_span (fun a' ha' b' hb' => pj_Q_symm ?_) x' hx' y' hy'
  exact schur_relation_span (fun a ha b hb => hS a ha b hb a' ha' b' hb') x hx y hy

theorem pj_Q_diag {x y : Hs} (h : pj_Q μ σ d x y x y) :
    Integrable (fun g => ‖⟪y, σ g x⟫_ℂ‖ ^ 2) μ ∧ ∫ g, ‖⟪y, σ g x⟫_ℂ‖ ^ 2 ∂μ = ‖x‖ ^ 2 * ‖y‖ ^ 2 / d := by
  obtain ⟨hi, he⟩ := h
  have hfun : (fun g => ⟪y, σ g x⟫_ℂ * star ⟪y, σ g x⟫_ℂ) = fun g => ((‖⟪y, σ g x⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
    funext g
    exact mul_star_eq _
  rw [hfun] at hi he
  refine ⟨hi.re.congr (Filter.Eventually.of_forall fun g => Complex.ofReal_re _), ?_⟩
  rw [integral_complex_ofReal] at he
  have h2 : ((∫ g, ‖⟪y, σ g x⟫_ℂ‖ ^ 2 ∂μ : ℝ) : ℂ) = ((‖x‖ ^ 2 * ‖y‖ ^ 2 / d : ℝ) : ℂ) := by
    rw [he, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  exact_mod_cast h2

end Q

theorem pj_Q_pure (D : Formalism.BasicNotions.D7) (h1 : adm1 D) (X : CData) {n₀ : ℕ} {A : ℝ} (hX : X.HypB n₀ A)
    (a b a' b' : ∀ v, X.H v) :
    pj_Q (muInf X) X.σs (fdegAll X.I X.σ X.w) (X.tens a) (X.tens b) (X.tens a') (X.tens b') := by
  have hd : ∀ v, IsFdeg (Formalism.REAL.muG (X.I.ε v)) (X.σ v) (fdegOf (Formalism.REAL.muG (X.I.ε v)) (X.σ v) (X.w v)) := by
    intro v
    obtain ⟨d, hd⟩ := h1 X.I.n (X.I.ε v) (X.lam v) (hX.1.2.2.2.2.1 v) (X.H v) (X.σ v) (hX.2.1.1 v)
    rw [fdegOf_eq hd (hX.2.1.2.1 v).1]
    exact hd
  have hc : ∀ (a b : ∀ v, X.H v) (g : X.I.Ginf),
      ⟪X.tens b, X.σs g (X.tens a)⟫_ℂ = ∏ v, coefOn (X.σ v) (a v) (b v) (g v) := by
    intro a b g
    rw [hX.2.1.2.2.1.2.1 g a, hX.2.1.2.2.1.1]
    rfl
  have e : (fun g => ⟪X.tens b, X.σs g (X.tens a)⟫_ℂ * star ⟪X.tens b', X.σs g (X.tens a')⟫_ℂ) =
      fun g : X.I.Ginf => ∏ v, (fun y => coefOn (X.σ v) (a v) (b v) y * star (coefOn (X.σ v) (a' v) (b' v) y)) (g v) := by
    funext g
    rw [hc, hc, Finset.prod_mul_distrib]
    congr 1
    exact map_prod (starRingEnd ℂ) _ _
  unfold pj_Q
  rw [e]
  refine ⟨Integrable.fintype_prod_dep fun v => ((hd v).2 (a v) (b v) (a' v) (b' v)).1, ?_⟩
  refine (integral_fintype_prod_eq_prod (μ := fun v => Formalism.REAL.muG (X.I.ε v))
    (fun v y => coefOn (X.σ v) (a v) (b v) y * star (coefOn (X.σ v) (a' v) (b' v) y))).trans ?_
  simp only [((hd _).2 _ _ _ _).2]
  rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, hX.2.1.2.2.1.1, hX.2.1.2.2.1.1]
  unfold fdegAll
  push_cast
  rfl

theorem pj_schur_span (D : Formalism.BasicNotions.D7) (h1 : adm1 D) (X : CData) {n₀ : ℕ} {A : ℝ} (hX : X.HypB n₀ A) :
    ∀ x ∈ Submodule.span ℂ (Set.range X.tens), ∀ y ∈ Submodule.span ℂ (Set.range X.tens),
      Integrable (fun g => ‖⟪y, X.σs g x⟫_ℂ‖ ^ 2) (muInf X) ∧
        ∫ g, ‖⟪y, X.σs g x⟫_ℂ‖ ^ 2 ∂(muInf X) = ‖x‖ ^ 2 * ‖y‖ ^ 2 / fdegAll X.I X.σ X.w := by
  intro x hx y hy
  refine pj_Q_diag (pj_Q_span ?_ x hx y hy x hx y hy)
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ _ ⟨a', rfl⟩ _ ⟨b', rfl⟩
  exact pj_Q_pure D h1 X hX a b a' b'

end Formalism.MainNotions.LeviCoordinates

end
end

