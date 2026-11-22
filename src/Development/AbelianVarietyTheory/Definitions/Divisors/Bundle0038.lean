import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.KerInfIntegrableOfMemRspan
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory

namespace GlobalTheory.JSW.RapidModel

open GlobalTheory.CuspRep GlobalTheory.JSW

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

omit [IsTotallyComplex E] in

theorem norm_toL_mul (x y : Matrix (Fin a) (Fin a) (Cinf E)) : ‖toL (x * y)‖ ≤ a * (‖toL x‖ * ‖toL y‖) := by
  refine pi_norm_le_iff_of_nonneg (by positivity) |>.2 fun i => pi_norm_le_iff_of_nonneg (by positivity) |>.2 fun j => ?_
  change ‖(x * y) i j‖ ≤ _
  rw [Matrix.mul_apply]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ (‖toL x‖ * ‖toL y‖) fun l _ => ?_).trans_eq (by simp))
  exact (norm_mul_le _ _).trans (mul_le_mul ((norm_le_pi_norm (toL x i) l).trans (norm_le_pi_norm (toL x) i))
    ((norm_le_pi_norm (toL y l) j).trans (norm_le_pi_norm (toL y) l)) (norm_nonneg _) (norm_nonneg _))

omit [IsTotallyComplex E] in

theorem height_mul_le (x y : GL (Fin a) (Cinf E)) : height (x * y) ≤ (1 + 2 * a) * (height x * height y) := by
  have h1 := norm_toL_mul x.val y.val
  have h2 := norm_toL_mul (y⁻¹).val (x⁻¹).val
  have hx := one_le_height x
  have hy := one_le_height y
  have a1 : ‖toL x.val‖ ≤ height x := by unfold height; linarith [norm_nonneg (toL (x⁻¹).val)]
  have a2 : ‖toL (x⁻¹).val‖ ≤ height x := by unfold height; linarith [norm_nonneg (toL x.val)]
  have b1 : ‖toL y.val‖ ≤ height y := by unfold height; linarith [norm_nonneg (toL (y⁻¹).val)]
  have b2 : ‖toL (y⁻¹).val‖ ≤ height y := by unfold height; linarith [norm_nonneg (toL y.val)]
  have c1 : ‖toL x.val‖ * ‖toL y.val‖ ≤ height x * height y := mul_le_mul a1 b1 (norm_nonneg _) (by linarith)
  have c2 : ‖toL (y⁻¹).val‖ * ‖toL (x⁻¹).val‖ ≤ height x * height y := by
    rw [mul_comm]; exact mul_le_mul a2 b2 (norm_nonneg _) (by linarith)
  have c0 : 1 ≤ height x * height y := one_le_mul_of_one_le_of_one_le hx hy
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have e : height (x * y) = 1 + ‖toL (x.val * y.val)‖ + ‖toL ((y⁻¹).val * (x⁻¹).val)‖ := by
    unfold height; rw [mul_inv_rev]; rfl
  rw [e]
  nlinarith [mul_le_mul_of_nonneg_left c1 ha, mul_le_mul_of_nonneg_left c2 ha]

variable (E a) in

def modGr : Submodule ℂ (GA E a → ℂ) where
  carrier := {F | ∀ g, Measurable (chart F g) ∧ ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ y, ‖F (g * infGL E a y)‖ ≤ C * height y ^ N}
  add_mem' := fun {F G} hF hG g => by
    obtain ⟨m1, C, N, h0, h1⟩ := hF g
    obtain ⟨m2, C', N', h0', h2⟩ := hG g
    refine ⟨?_, C + C', N + N', by positivity, fun y => ?_⟩
    · have e : chart (F + G) g = fun x => chart F g x + chart G g x := by
        funext x
        by_cases h : IsUnit (Matrix.of x) <;> simp [chart, h]
      rw [e]; exact m1.add m2
    · have hy := one_le_height y
      have p1 : height y ^ N ≤ height y ^ (N + N') := pow_le_pow_right₀ hy (by omega)
      have p2 : height y ^ N' ≤ height y ^ (N + N') := pow_le_pow_right₀ hy (by omega)
      refine (norm_add_le _ _).trans ?_
      nlinarith [h1 y, h2 y, mul_le_mul_of_nonneg_left p1 h0, mul_le_mul_of_nonneg_left p2 h0']
  zero_mem' g := ⟨by
      have e : chart (0 : GA E a → ℂ) g = fun _ => 0 := by funext x; simp [chart]
      rw [e]; exact measurable_const, 0, 0, le_rfl, fun y => by simp⟩
  smul_mem' c F hF g := by
    obtain ⟨m1, C, N, h0, h1⟩ := hF g
    refine ⟨?_, ‖c‖ * C, N, by positivity, fun y => ?_⟩
    · have e : chart (c • F) g = fun x => c * chart F g x := by
        funext x
        by_cases h : IsUnit (Matrix.of x) <;> simp [chart, h]
      rw [e]; exact m1.const_mul c
    · rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_left (h1 y) (norm_nonneg _)

theorem integrable_of_modGr {F : GA E a → ℂ} (hF : F ∈ modGr E a) {X : Type} [MeasurableSpace X] {ν : Measure X}
    {k : X → ℂ} {γ : X → GL (Fin a) (Cinf E)} (hk : IsRapidInf ν k γ) (g : GA E a) :
    Integrable (fun x => k x * F (g * infGL E a (γ x))) ν := by
  obtain ⟨m, C, N, h0, hC⟩ := hF g
  have h : Measurable fun x => toL (γ x).val := hk.2.1
  have e : (fun x => F (g * infGL E a (γ x))) = fun x => chart F g (toL (γ x).val) :=
    funext fun x => (chart_val F g (γ x)).symm
  have hm : Measurable fun x => F (g * infGL E a (γ x)) := by rw [e]; exact m.comp h
  refine ((hk.2.2 N).const_mul C).mono' (hk.1.mul hm).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  rw [norm_mul]
  calc ‖k x‖ * ‖F (g * infGL E a (γ x))‖ ≤ ‖k x‖ * (C * height (γ x) ^ N) :=
        mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
    _ = C * (‖k x‖ * height (γ x) ^ N) := by ring

theorem rspan_le_modGr (π : CuspSub E a) : rspan π ≤ modGr E a := by
  refine rspan_le (fun φ hφ g => ⟨measurable_chart φ.2 g, ?_⟩) (fun F hF h g => ?_) fun F hF X _ ν _ k γ hk g => ?_
  · obtain ⟨C, N, hC⟩ := (π.cusp φ hφ).1.growth g
    exact ⟨|C|, N, abs_nonneg C, fun y => (hC y).trans
      (mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg (by linarith [one_le_height y]) N))⟩
  · rw [← infGL_mul_finGL h]
    set y := Matrix.GeneralLinearGroup.map (pInf E) h
    set k := Matrix.GeneralLinearGroup.map (pFin E) h
    obtain ⟨m, C, N, h0, hC⟩ := hF (g * finGL E a k)
    refine ⟨?_, C * ((1 + 2 * a) * height y) ^ N, N, by have := one_le_height y; positivity, fun z => ?_⟩
    · have e : (fun x => F (x * (infGL E a y * finGL E a k))) =
          fun x => (fun x => F (x * finGL E a k)) (x * infGL E a y) := by
        funext x; simp only [mul_assoc]
      rw [e, chart_rt_inf (fun x => F (x * finGL E a k)), chart_rt_fin]
      exact m.comp (rmul (toL y.val)).continuous.measurable
    · have e : g * infGL E a z * (infGL E a y * finGL E a k) = g * finGL E a k * infGL E a (z * y) := by
        rw [mul_assoc g (finGL E a k), ← infGL_comm, map_mul]; simp only [mul_assoc]
      change ‖F (g * infGL E a z * (infGL E a y * finGL E a k))‖ ≤ _
      rw [e]
      refine (hC _).trans ?_
      rw [mul_assoc C, ← mul_pow]
      refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith [one_le_height (z * y)]) ?_ N) h0
      exact (height_mul_le z y).trans_eq (by ring)
  · obtain ⟨m, C, N, h0, hC⟩ := hF g
    refine ⟨?_, C * (1 + 2 * a) ^ N * ∫ x, ‖k x‖ * height (γ x) ^ N ∂ν, N, ?_, fun z => ?_⟩
    · have e : chart (kerInf ν k γ F) g = fun x => ∫ t, k t * chart F g (toL (Matrix.of x * (γ t).val)) ∂ν := by
        funext x
        by_cases h : IsUnit (Matrix.of x)
        · obtain ⟨u, hu⟩ := h
          have hx : x = (toL u.val) := hu.symm
          rw [hx, chart_val, kerInf]
          congr 1
          funext t
          rw [mul_assoc, ← map_mul, ← chart_val F g]
          rfl
        · have h' : ∀ t, ¬ IsUnit (Matrix.of (toL (Matrix.of x * (γ t).val))) :=
            fun t h' => h ((Units.isUnit_mul_units _ (γ t)).1 h')
          simp only [chart, dif_neg h, dif_neg (h' _), mul_zero, integral_zero]
      rw [e]
      have hγ : Measurable fun x => toL (γ x).val := hk.2.1
      have hm : Measurable fun p : Lie E a × X => toL (Matrix.of p.1 * (γ p.2).val) := by
        refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
        change Measurable fun p : Lie E a × X => (Matrix.of p.1 * (γ p.2).val) i j
        simp only [Matrix.mul_apply]
        refine Finset.measurable_sum _ fun l _ => Measurable.mul ?_ ?_
        · exact (measurable_pi_apply l).comp ((measurable_pi_apply i).comp measurable_fst)
        · exact (measurable_pi_apply j).comp ((measurable_pi_apply l).comp (hγ.comp measurable_snd))
      have hs : StronglyMeasurable fun p : Lie E a × X => k p.2 * chart F g (toL (Matrix.of p.1 * (γ p.2).val)) :=
        ((hk.1.comp measurable_snd).mul (m.comp hm)).stronglyMeasurable
      exact hs.integral_prod_right'.measurable
    · refine mul_nonneg (by positivity) (integral_nonneg fun x => ?_)
      have := one_le_height (γ x)
      positivity
    · rw [kerInf]
      have hz := one_le_height z
      calc _ ≤ ∫ x, (C * (1 + 2 * a) ^ N * height z ^ N) * (‖k x‖ * height (γ x) ^ N) ∂ν := by
            refine norm_integral_le_of_norm_le ((hk.2.2 N).const_mul _) (Filter.Eventually.of_forall fun x => ?_)
            rw [norm_mul, mul_assoc g, ← map_mul]
            have h1 := (hC (z * γ x)).trans (mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (by linarith [one_le_height (z * γ x)]) (height_mul_le z (γ x)) N) h0)
            refine (mul_le_mul_of_nonneg_left h1 (norm_nonneg _)).trans_eq ?_
            rw [mul_pow, mul_pow]; ring
        _ = _ := by rw [integral_const_mul]; ring

theorem kerInf_integrable_of_mem_rspan {π : CuspSub E a} {F : GA E a → ℂ} (hF : F ∈ rspan π) {X : Type}
    [MeasurableSpace X] {ν : Measure X} {k : X → ℂ} {γ : X → GL (Fin a) (Cinf E)} (hk : IsRapidInf ν k γ) (g : GA E a) :
    Integrable (fun x => k x * F (g * infGL E a (γ x))) ν :=
  integrable_of_modGr (rspan_le_modGr π hF) hk g

theorem kerInf_add {π : CuspSub E a} {F G : GA E a → ℂ} (hF : F ∈ rspan π) (hG : G ∈ rspan π) {X : Type}
    [MeasurableSpace X] {ν : Measure X} {k : X → ℂ} {γ : X → GL (Fin a) (Cinf E)} (hk : IsRapidInf ν k γ) :
    kerInf ν k γ (F + G) = kerInf ν k γ F + kerInf ν k γ G := by
  funext g
  rw [Pi.add_apply, kerInf, kerInf, kerInf, ← integral_add (kerInf_integrable_of_mem_rspan hF hk g)
    (kerInf_integrable_of_mem_rspan hG hk g)]
  simp only [Pi.add_apply, mul_add]

theorem rspan_triv (ha : a ≤ 1) : rspan (CuspSub.triv E ha) = Submodule.span ℂ {fun _ => 1} := by
  rw [rspan_eq_mspanR, WhitModel.mspanR_triv]

theorem rspan_twist_triv (ha : a ≤ 1) (χ : Formalism.L2.Host.HChar E) :
    rspan ((CuspSub.triv E ha).twist χ) = Submodule.span ℂ {fun g => ((chiDet a χ g : ℂˣ) : ℂ)} := by
  apply le_antisymm
  · refine rspan_le ?_ (fun F hF h => ?_) fun F hF X _ ν _ k γ _ => ?_
    · rintro _ ⟨φ, hφ, rfl⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hφ
      exact Submodule.mem_span_singleton.2 ⟨c, by funext g; simp [oneFn]⟩
    · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hF
      exact Submodule.mem_span_singleton.2 ⟨c * ((chiDet a χ h : ℂˣ) : ℂ), by funext g; simp; ring⟩
    · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hF
      refine Submodule.mem_span_singleton.2 ⟨∫ x, k x * (c * ((chiDet a χ (infGL E a (γ x)) : ℂˣ) : ℂ)) ∂ν, ?_⟩
      funext g
      simp only [Pi.smul_apply, smul_eq_mul, kerInf, map_mul, Units.val_mul]
      rw [← integral_mul_const]
      congr 1; funext x; ring
  · refine Submodule.span_le.2 ?_
    rintro _ rfl
    have h := mem_rspan (π := (CuspSub.triv E ha).twist χ) (φ := mulChi a χ (oneFn E a))
      ⟨oneFn E a, Submodule.mem_span_singleton_self _, rfl⟩
    have e : (mulChi a χ (oneFn E a)).1 = fun g => ((chiDet a χ g : ℂˣ) : ℂ) := by funext g; simp [oneFn]
    rw [e] at h
    exact h

theorem plGL_injective (w : InfinitePlace E) : Function.Injective (plGL (a := a) w) := fun g h e => by
  have h1 := map_plGL w g w
  rw [e, map_plGL, if_pos rfl, if_pos rfl] at h1
  exact h1.symm

end GlobalTheory.JSW.RapidModel
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.NotHasNonzeroSecOfIsEmpty
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.QCoh GlobalTheory.CechPic

namespace GlobalTheory.PositivityModel

variable {k : Type} [Field k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)] {H L N A : LB X}

theorem not_hasNonzeroSec_of_isEmpty [IsEmpty X] : ¬ HasNonzeroSec L := by
  rintro ⟨s, hs⟩
  refine hs (DVR.SecOps.sec_ext fun i => ?_)
  have : L.U i = ⊥ := by ext x; exact isEmptyElim x
  have : Subsingleton Γ(X, L.U i) := by rw [this]; infer_instance
  exact Subsingleton.elim _ _

theorem empty_values [IsEmpty X] : ¬ IsBig k L ∧ ¬ IsPsEff L := by
  refine ⟨fun h => not_hasNonzeroSec_of_isEmpty h.frequently_hasNonzeroSec.exists.choose_spec,
    fun h => ?_⟩
  obtain ⟨_, -, hs⟩ := h.2
  obtain ⟨_, -, hr⟩ := hs 1 le_rfl
  exact not_hasNonzeroSec_of_isEmpty hr

theorem isNef_of_dim_le_zero (hX : topologicalKrullDim X ≤ 0) (hL : L.IsLB) : IsNef k L :=
  ⟨hL, fun Z hZ => by
    have h := (topologicalKrullDim_subspace_le X (Z : Set X)).trans hX
    rw [hZ.2] at h
    exact absurd h (by decide)⟩

theorem genericPoint_mem [IsIntegral X] (hd : topologicalKrullDim X = 1) {Z : Closeds X}
    (hZ : IsCompleteCurve k Z) : genericPoint X ∈ Z := by
  by_contra hn
  have h := topologicalKrullDim_add_one_le Z.isClosed isClosed_univ fun x _ =>
    ⟨genericPoint X, trivial, hn, genericPoint_specializes x⟩
  have h' := h.trans ((topologicalKrullDim_subspace_le X Set.univ).trans hd.le)
  rw [hZ.2] at h'
  exact absurd h' (by decide)

theorem isNef_of_isPsEff [IsIntegral X] (hd : topologicalKrullDim X = 1) (h : IsPsEff N) :
    IsNef k N := by
  obtain ⟨A, hA, hs⟩ := h.2
  refine ⟨h.1, fun Z hZ => ?_⟩
  by_contra! hneg
  have key : ∀ m : ℕ, 1 ≤ m → 0 ≤ m * interNumRed k Z ![N] + interNumRed k Z ![A] := by
    intro m hm
    obtain ⟨r, hr, hs⟩ := hs m hm
    obtain ⟨s, hs⟩ := hasNonzeroSec_iff.1 hs
    have hT := isLB_tens (isLB_lbPow h.1 m) hA.isLB
    have h0 := (hZ.interNumRed_nonneg_of_sec hA (isLB_lbPow hT r) s (genericPoint_mem hd hZ) hs).1
    rw [hZ.interNumRed_lbPow hA hT, hZ.interNumRed_of_cls_eq_add hA hT (isLB_lbPow h.1 m) hA.isLB rfl,
      hZ.interNumRed_lbPow hA h.1] at h0
    exact nonneg_of_mul_nonneg_right h0 (Nat.cast_pos.2 hr)
  have hp := hA.interNumRed_pos hZ
  have := key ((interNumRed k Z ![A]).toNat + 1) (by omega)
  push_cast at this
  rw [Int.toNat_of_nonneg hp.le] at this
  nlinarith

section Space
open ProjSpace
variable (k) (D : ℕ)

theorem point_values (n : ℤ) : IsNef k (lbZPow (O1 k 0) n) ∧ IsBig k (lbZPow (O1 k 0) n) ∧
    IsPsEff (lbZPow (O1 k 0) n) := by
  have hO := O1_isLB k 0
  have hn := Twist.isLB_lbZPow hO n
  have hb : IsBig k (lbZPow (O1 k 0) n) := by
    refine (isBig_iff (algebraMap_top_eq k 0) (isProjOver_str k 0) (topologicalKrullDim_eq k 0)).2
      ⟨hn, 1, one_pos, Frequently.of_forall fun m => ?_⟩
    obtain ⟨e⟩ := ProjCoh.nonempty_coh_zero_equiv k (m * n)
    have h1 : lbH0 k (lbZPow (O1 k 0) (m * n)) = 1 := e.finrank_eq.trans (Module.finrank_self k)
    rw [lineBundleGlobalSectionsDim_congr_picardClass (isLB_lbPow hn m) (Twist.isLB_lbZPow hO (m * n))
      (by rw [cls_lbPow hn, cls_lbZPow hO, cls_lbZPow hO]; module), h1]
    simp
  exact ⟨isNef_of_dim_le_zero (topologicalKrullDim_eq k 0).le hn, hb,
    hb.isPsEff (isAmple_projective_O_one k 0)⟩

theorem isPsEff_iff (n : ℤ) : IsPsEff (lbZPow (O1 k (D + 1)) n) ↔ 0 ≤ n := by
  have hO := O1_isLB k (D + 1)
  have hA := isAmple_projective_O_one k (D + 1)
  have := isNoetherian_of_isProjOver (isProjOver_str k (D + 1))
  refine ⟨fun h => ?_, fun h => ?_⟩
  · by_contra! hn
    obtain ⟨r, hr, hs⟩ := h.exists_hasNonzeroSec hA (m := 2) one_le_two
    have hs' : HasNonzeroSec (lbZPow (O1 k (D + 1)) (r * (2 * n + 1))) :=
      hs.of_cls_eq (Twist.isLB_lbZPow hO _) (isLB_lbPow (isLB_tens (isLB_lbPow h.1 2) hO) r) (by
        rw [cls_lbPow_tens_lbPow h.1 hO, cls_lbZPow hO, cls_lbZPow hO]; module)
    have := ProjCoh.subsingleton_coh_zero k (N := D + 1) (by omega) (n := r * (2 * n + 1))
      (mul_neg_of_pos_of_neg (by exact_mod_cast hr) (by omega))
    exact not_nontrivial _ (hasNonzeroSec_iff_nontrivial.1 hs')
  · lift n to ℕ using h
    have : 0 < lbH0 k (lbPow (O1 k (D + 1)) n) := by
      rw [sectionDim_twistingSheaf_pow]; exact Nat.choose_pos (by omega)
    exact ((lineBundleHasNonzeroSection_of_globalSectionsDim_pos this).isPsEff (isLB_lbPow hO n) hA).of_cls_eq
      (Twist.isLB_lbZPow hO _) rfl

theorem isBig_iff' (n : ℤ) : IsBig k (lbZPow (O1 k (D + 1)) n) ↔ 0 < n := by
  have hO := O1_isLB k (D + 1)
  have hA := isAmple_projective_O_one k (D + 1)
  refine ⟨fun h => ?_, fun h => ?_⟩
  · refine ((isPsEff_iff k D n).1 (h.isPsEff hA)).lt_of_ne ?_
    rintro rfl
    exact (triv_nef_not_big k D).2.2 (h.of_cls_eq (LB.isLB_triv _)
      (by rw [cls_lbZPow hO, cls_triv, zero_zsmul]))
  · lift n to ℕ using h.le
    exact ((isBig_twistingSheaf k (D + 1)).pow (algebraMap_top_eq k _) (isProjOver_str k _)
      (n := n) (by omega)).of_cls_eq (Twist.isLB_lbZPow hO _)
      rfl

theorem isNef_iff_line (n : ℤ) : IsNef k (lbZPow (O1 k 1) n) ↔ 0 ≤ n := by
  have hO := O1_isLB k 1
  have hA := isAmple_projective_O_one k 1
  refine ⟨fun h => ?_, fun h => isNef_of_isPsEff (topologicalKrullDim_eq k 1)
    ((isPsEff_iff k 0 n).2 h)⟩
  by_contra! hn
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = -((m + 1 : ℕ) : ℤ) := ⟨(-n - 1).toNat, by push_cast; omega⟩
  have h' : IsNef k (lbPow (dual (O1 k 1)) (m + 1)) := h.of_cls_eq (isLB_lbPow (isLB_dual hO) _)
    (by rw [cls_lbPow (isLB_dual hO), cls_dual hO, cls_lbZPow hO]; module)
  exact not_isNef_dual_twistingSheaf k ((isNef_pow_iff hA (isLB_dual hO) (by omega)).1 h')

theorem degree_line (n : ℤ) :
    interNumRed k (⊤ : Closeds (PSpace k 1)) ![lbZPow (O1 k 1) n] = n := by
  have hO := O1_isLB k 1
  have hn := Twist.isLB_lbZPow hO n
  rw [InterModel.interNumRed_eq_interNumOn k (𝟙 _) ⊤ (by simp), interNumOn_id, interNum_one k _ hn]
  obtain ⟨i⟩ := nonempty_twist_iso_of_cls_eq (structureModule (PSpace k 1))
    (Twist.isLB_lbZPow hn (-1)) (Twist.isLB_lbZPow hO (-n))
    (by rw [cls_lbZPow hn, cls_lbZPow hO, cls_lbZPow hO]; module)
  obtain ⟨j⟩ := nonempty_twist_iso_of_cls_eq (structureModule (PSpace k 1))
    (Twist.isLB_lbZPow hO 0) (LB.isLB_triv _)
    (by rw [cls_lbZPow hO, cls_triv, zero_zsmul])
  have h1 := (chi_congr k i).trans (ProjCoh.chi_sheafO k 1 (-n))
  have h0 := (chi_congr k j).symm.trans (ProjCoh.chi_sheafO k 1 0)
  rw [chi_congr k (Twist.trivIso (structureModule (PSpace k 1))), h0, h1]
  simp

end Space

end GlobalTheory.PositivityModel
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.PointSide
section
noncomputable section

open scoped Classical

namespace GlobalTheory.LKCount

section Vol

variable {G : Type} [Group G]

def vol (C H : Subgroup G) : ℚ := ((C.relIndex H : ℕ) : ℚ) / ((H.relIndex C : ℕ) : ℚ)

def orbC (θ : G →* G) (K C : Subgroup G) (δ : G) (f : G → ℂ) : ℂ :=
  ∑ᶠ q : DoubleCoset.Quotient (GlobalTheory.BCT.twCent θ δ : Set G) (K : Set G),
    ((vol C (GlobalTheory.BCT.twCent θ δ ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom) : ℚ) : ℂ)⁻¹ *
      f ((Quotient.out q)⁻¹ * δ * θ (Quotient.out q))

def orbK (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ) : ℂ :=
  orbC θ K (GlobalTheory.BCT.twCent θ δ ⊓ K) δ f

def massC (Γ' T C : Subgroup G) : ℚ :=
  ∑ᶠ q : DoubleCoset.Quotient ((Γ'.subgroupOf T : Subgroup T) : Set T) ((C.subgroupOf T : Subgroup T) : Set T),
    ((Nat.card ((Γ'.subgroupOf T) ⊓ (C.subgroupOf T).map (MulAut.conj (Quotient.out q)).toMonoidHom : Subgroup T) : ℕ) : ℚ)⁻¹

end Vol

section Count

variable {Γ G₁ G₂ : Type} [Group Γ] [Group G₁] [Group G₂]

def stab (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (x : G₁ × G₂) : Subgroup Γ :=
  (K₁.map (MulAut.conj x.1).toMonoidHom).comap ι₁ ⊓ (K₂.map (MulAut.conj x.2).toMonoidHom).comap ι₂

def pointSum (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (θ : G₂ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (γ : G₁) (δ : G₂)
    (f₁ : G₁ → ℂ) (φ : G₂ → ℂ) : ℂ :=
  ∑ᶠ q : DoubleCoset.Quotient ((ι₁.prod ι₂).range : Set (G₁ × G₂)) ((K₁.prod K₂ : Subgroup (G₁ × G₂)) : Set (G₁ × G₂)),
    ((Nat.card (stab ι₁ ι₂ K₁ K₂ (Quotient.out q)) : ℕ) : ℂ)⁻¹ *
      (f₁ ((Quotient.out q).1⁻¹ * γ * (Quotient.out q).1) * φ ((Quotient.out q).2⁻¹ * δ * θ (Quotient.out q).2))

def pointSide (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (θ : G₂ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (γ : G₁) (δ : G₂)
    (f₁ : G₁ → ℂ) (φ : G₂ → ℂ) : ℂ :=
  ((massC (ι₁.prod ι₂).range (GlobalTheory.BCT.twCent ((MonoidHom.id G₁).prodMap θ) (γ, δ))
      (GlobalTheory.BCT.twCent ((MonoidHom.id G₁).prodMap θ) (γ, δ) ⊓ K₁.prod K₂) : ℚ) : ℂ) *
    (orbK (MonoidHom.id G₁) K₁ γ f₁ * orbK θ K₂ δ φ)

def term (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (θ : G₂ →* G₂) (δ : G₂) (f₁ : G₁ → ℂ) (φ : G₂ → ℂ) (x : G₁ × G₂) (γ : Γ) : ℂ :=
  f₁ (x.1⁻¹ * ι₁ γ * x.1) * φ (x.2⁻¹ * (ι₂ γ * δ) * θ x.2)

def classSum (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (θ : G₂ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (δ : G₂)
    (f₁ : G₁ → ℂ) (φ : G₂ → ℂ) : ℂ :=
  ∑ᶠ q : DoubleCoset.Quotient ((ι₁.prod ι₂).range : Set (G₁ × G₂)) ((K₁.prod K₂ : Subgroup (G₁ × G₂)) : Set (G₁ × G₂)),
    ((Nat.card (stab ι₁ ι₂ K₁ K₂ (Quotient.out q)) : ℕ) : ℂ)⁻¹ *
      ∑ᶠ γ : Γ, term ι₁ ι₂ θ δ f₁ φ (Quotient.out q) γ

def centSum (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (θ : G₂ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (δ : G₂)
    (f₁ : G₁ → ℂ) (φ : G₂ → ℂ) (γ : Γ) : ℂ :=
  ∑ᶠ q : DoubleCoset.Quotient (((Subgroup.centralizer {γ}).map (ι₁.prod ι₂) : Subgroup (G₁ × G₂)) : Set (G₁ × G₂))
      ((K₁.prod K₂ : Subgroup (G₁ × G₂)) : Set (G₁ × G₂)),
    ((Nat.card (stab ι₁ ι₂ K₁ K₂ (Quotient.out q) ⊓ Subgroup.centralizer {γ} : Subgroup Γ) : ℕ) : ℂ)⁻¹ *
      term ι₁ ι₂ θ δ f₁ φ (Quotient.out q) γ

def cent (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (θ : G₂ →* G₂) (δ : G₂) (γ : Γ) : Subgroup (G₁ × G₂) :=
  GlobalTheory.BCT.twCent ((MonoidHom.id G₁).prodMap θ) (ι₁ γ, ι₂ γ * δ)

def classSide (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (θ : G₂ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (δ : G₂)
    (f₁ : G₁ → ℂ) (φ : G₂ → ℂ) : ℂ :=
  ∑ᶠ c : ConjClasses Γ,
    ((massC ((Subgroup.centralizer {Quotient.out c}).map (ι₁.prod ι₂)) (cent ι₁ ι₂ θ δ (Quotient.out c))
        (cent ι₁ ι₂ θ δ (Quotient.out c) ⊓ K₁.prod K₂) : ℚ) : ℂ) *
      (orbK (MonoidHom.id G₁) K₁ (ι₁ (Quotient.out c)) f₁ * orbK θ K₂ (ι₂ (Quotient.out c) * δ) φ)

end Count

section Examples

example {Γ G₁ G₂ : Type} [Group Γ] [Group G₁] [Group G₂] (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (θ : G₂ →* G₂)
    (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (γ : G₁) (δ : G₂) (φ : G₂ → ℂ) :
    pointSum ι₁ ι₂ θ K₁ K₂ γ δ (fun _ => 0) φ = 0 := by
  simp [pointSum]

example {G : Type} [Group G] (C : Subgroup G) : vol C C = 1 := by
  simp [vol, Subgroup.relIndex_self]

example : pointSum (MonoidHom.id Unit) (MonoidHom.id Unit) (MonoidHom.id Unit) ⊤ ⊤ () () (fun _ => 1) (fun _ => 1) = 1 := by
  unfold pointSum
  let U : Unique (DoubleCoset.Quotient (((MonoidHom.id Unit).prod (MonoidHom.id Unit)).range : Set (Unit × Unit))
      (((⊤ : Subgroup Unit).prod (⊤ : Subgroup Unit) : Subgroup (Unit × Unit)) : Set (Unit × Unit))) :=
    { default := DoubleCoset.mk _ _ 1
      uniq := fun q => by
        rw [← DoubleCoset.out_eq' _ _ q]
        exact congrArg _ (Subsingleton.elim _ _) }
  rw [finsum_unique]
  have h : Nat.card (stab (MonoidHom.id Unit) (MonoidHom.id Unit) ⊤ ⊤ (Quotient.out (default : DoubleCoset.Quotient
      (((MonoidHom.id Unit).prod (MonoidHom.id Unit)).range : Set (Unit × Unit))
      (((⊤ : Subgroup Unit).prod (⊤ : Subgroup Unit) : Subgroup (Unit × Unit)) : Set (Unit × Unit))))) = 1 :=
    Nat.card_eq_one_iff_exists.2 ⟨1, fun x => Subsingleton.elim _ _⟩
  rw [h]
  simp

example : pointSide (MonoidHom.id Unit) (MonoidHom.id Unit) (MonoidHom.id Unit) ⊤ ⊤ () () (fun _ => 1) (fun _ => 1) = 1 := by
  have hv : ∀ C H : Subgroup Unit, vol C H = 1 := fun C H => by
    have : H = C := Subsingleton.elim _ _
    subst this; simp [vol, Subgroup.relIndex_self]
  have ho : ∀ (K : Subgroup Unit) (δ : Unit), orbK (MonoidHom.id Unit) K δ (fun _ => 1) = 1 := fun K δ => by
    unfold orbK orbC
    let U : Unique (DoubleCoset.Quotient (GlobalTheory.BCT.twCent (MonoidHom.id Unit) δ : Set Unit) (K : Set Unit)) :=
      { default := DoubleCoset.mk _ _ 1
        uniq := fun q => by
          rw [← DoubleCoset.out_eq' _ _ q] }
    rw [finsum_unique, hv]
    simp
  unfold pointSide
  rw [ho]
  unfold massC
  generalize hT : GlobalTheory.BCT.twCent ((MonoidHom.id Unit).prodMap (MonoidHom.id Unit)) ((), ()) = T
  let U : Unique (DoubleCoset.Quotient
      ((((MonoidHom.id Unit).prod (MonoidHom.id Unit)).range.subgroupOf T : Subgroup T) : Set T)
      (((T ⊓ (⊤ : Subgroup Unit).prod ⊤).subgroupOf T : Subgroup T) : Set T)) :=
    { default := DoubleCoset.mk _ _ 1
      uniq := fun q => by
        rw [← DoubleCoset.out_eq' _ _ q]
        exact congrArg _ (Subsingleton.elim _ _) }
  rw [finsum_unique]
  rw [Nat.card_eq_one_iff_exists.2 ⟨1, fun x => Subsingleton.elim _ _⟩]
  simp

end Examples

end GlobalTheory.LKCount
end
end

