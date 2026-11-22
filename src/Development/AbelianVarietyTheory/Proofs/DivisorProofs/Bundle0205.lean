import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0077
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0163
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegrableMonomialMulConjComplexGaussian
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0136
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstPreorder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0096
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0137
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0138

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSumIntegralCubeDerivatives
section
open MeasureTheory
open scoped ContDiff

namespace GlobalTheory.CubeTaylor

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

open MeasureTheory in
open scoped ContDiff in
private theorem integral_cube_succ_eq_iterated {K : Type} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] (N : ℕ) (s : ℝ) (F : (Fin (N + 1) → ℝ) → K)
    (hF : Continuous F) :
    ∫ t in Set.univ.pi (fun _ : Fin (N + 1) => Set.Icc (0 : ℝ) s), F t =
      ∫ t in Set.univ.pi (fun _ : Fin N => Set.Icc (0 : ℝ) s),
        ∫ r in Set.Icc (0 : ℝ) s, F (Fin.snoc t r) := by
  have hsnoc : Continuous fun p : (Fin N → ℝ) × ℝ => (Fin.snoc p.1 p.2 : Fin (N + 1) → ℝ) :=
    Continuous.finSnoc (A := fun _ => ℝ) continuous_fst continuous_snd
  have hF' : Continuous fun p : (Fin N → ℝ) × ℝ => F (Fin.snoc p.1 p.2) := hF.comp hsnoc
  have hG : Continuous fun t : Fin N → ℝ => ∫ r in Set.Icc (0 : ℝ) s, F (Fin.snoc t r) :=
    continuous_parametric_integral_of_continuous (f := fun t r => F (Fin.snoc t r)) hF'
      isCompact_Icc
  have hcube : IsCompact (Set.univ.pi fun _ : Fin (N + 1) => Set.Icc (0 : ℝ) s) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hcube' : IsCompact (Set.univ.pi fun _ : Fin N => Set.Icc (0 : ℝ) s) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  set X := ∫ t in Set.univ.pi (fun _ : Fin (N + 1) => Set.Icc (0 : ℝ) s), F t with hX
  set Y := ∫ t in Set.univ.pi (fun _ : Fin N => Set.Icc (0 : ℝ) s),
    ∫ r in Set.Icc (0 : ℝ) s, F (Fin.snoc t r) with hY
  have key : ∀ e : K, (inner ℂ e X).re = (inner ℂ e Y).re := by
    intro e
    let L : K →L[ℝ] ℝ := Complex.reCLM.comp ((innerSL ℂ e).restrictScalars ℝ)
    have hL : ∀ x, L x = (inner ℂ e x).re := fun x => rfl
    rw [← hL, ← hL, hX, hY,
      ← L.integral_comp_comm (hF.continuousOn.integrableOn_compact hcube),
      ← L.integral_comp_comm (hG.continuousOn.integrableOn_compact hcube'),
      (_root_.GlobalTheory.integral_cube_succ_last N s (fun t => L (F t)) (L.continuous.comp hF)).2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    exact L.integral_comp_comm
      ((hF.comp (Continuous.finSnoc (A := fun _ => ℝ) continuous_const continuous_id)).continuousOn.integrableOn_compact
        isCompact_Icc)
  have h := key (X - Y)
  have h2 : ‖X - Y‖ ^ 2 = 0 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), inner_sub_right, map_sub]
    simp only [RCLike.re_to_complex]
    rw [h, sub_self]
  exact sub_eq_zero.1 (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h2))

open MeasureTheory in
open scoped ContDiff in
private theorem eq_interval_average_sub_weighted_deriv
    {G : Type} [Group G] [TopologicalSpace G] {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (ρ : G →* (K →L[ℂ] K)) (hcont : ∀ v, Continuous fun g => ρ g v)
    {s : ℝ} (hs : 0 < s) (c : ℝ → G) (hc : Continuous c) (hc0 : c 0 = 1)
    (hadd : ∀ a b, c (a + b) = c a * c b) (w w' : K)
    (hd : HasDerivAt (fun t : ℝ => ρ (c t) w) w' 0) :
    w = (∫ r in Set.Icc 0 s, ((1 / s : ℝ) : ℂ) • ρ (c r) w) -
      ∫ r in Set.Icc 0 s, (((s - r) / s : ℝ) : ℂ) • ρ (c r) w' := by
  have hg : ∀ r, HasDerivAt (fun t => ρ (c t) w) (ρ (c r) w') r := by
    intro r
    have h1 : HasDerivAt (fun t => ρ (c (t - r)) w) w' r := by
      have := hd
      rw [← sub_self r] at this
      exact this.comp_sub_const r r
    have h2 := ((ρ (c r)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt r h1
    refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    simp only [Function.comp_apply, ContinuousLinearMap.coe_restrictScalars']
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, ← hadd, add_sub_cancel]
  have hb : ∀ r : ℝ, HasDerivAt (fun t : ℝ => (((s - t) / s : ℝ) : ℂ)) (((-(1 / s)) : ℝ) : ℂ) r := by
    intro r
    have : HasDerivAt (fun t : ℝ => (s - t) / s) (-(1 / s)) r := by
      simpa [neg_div] using ((hasDerivAt_id r).const_sub s).div_const s
    exact this.ofReal_comp
  have hh : ∀ r ∈ Set.uIcc 0 s, HasDerivAt (fun t => (((s - t) / s : ℝ) : ℂ) • ρ (c t) w)
      ((((s - r) / s : ℝ) : ℂ) • ρ (c r) w' + (((-(1 / s)) : ℝ) : ℂ) • ρ (c r) w) r :=
    fun r _ => (hb r).smul (hg r)
  have hgc : Continuous fun t => ρ (c t) w := (hcont w).comp hc
  have hg'c : Continuous fun t => ρ (c t) w' := (hcont w').comp hc
  have hA : Continuous fun r : ℝ => (((s - r) / s : ℝ) : ℂ) • ρ (c r) w' := by
    exact (Complex.continuous_ofReal.comp ((continuous_const.sub continuous_id).div_const s)).smul hg'c
  have hB : Continuous fun r : ℝ => (((-(1 / s)) : ℝ) : ℂ) • ρ (c r) w :=
    continuous_const.smul hgc
  have hE := intervalIntegral.integral_eq_sub_of_hasDerivAt hh
    ((hA.add hB).intervalIntegrable 0 s)
  rw [intervalIntegral.integral_add (hA.intervalIntegrable 0 s) (hB.intervalIntegrable 0 s),
    intervalIntegral.integral_of_le hs.le, intervalIntegral.integral_of_le hs.le] at hE
  simp only [sub_self, zero_div, Complex.ofReal_zero, zero_smul, sub_zero, div_self hs.ne',
    Complex.ofReal_one, one_smul, hc0, map_one, ContinuousLinearMap.one_apply] at hE
  rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc]
  have hneg : ∫ r in Set.Ioc 0 s, (((-(1 / s)) : ℝ) : ℂ) • ρ (c r) w =
      -∫ r in Set.Ioc 0 s, ((1 / s : ℝ) : ℂ) • ρ (c r) w := by
    rw [← integral_neg]
    congr 1
    funext r
    rw [Complex.ofReal_neg, neg_smul]
  rw [hneg] at hE
  have key : ∀ x A B : K, A + -B = 0 - x → x = B - A := by
    intro x A B h
    calc x = -(0 - x) := by abel
      _ = -(A + -B) := by rw [h]
      _ = B - A := by abel
  exact key _ _ _ hE

open MeasureTheory in
open scoped ContDiff in
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] in

theorem _root_.GlobalTheory.CubeTaylor.eq_sum_integral_cube_derivatives : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K], ∀ (ρ : G →* (K →L[ℂ] K)), (∀ g v, ‖ρ g v‖ = ‖v‖) → (∀ v, Continuous fun g => ρ g v) → ∀ (s : ℝ), 0 < s → ∀ (N : ℕ) (c : Fin N → ℝ → G), (∀ i, Continuous (c i) ∧ c i 0 = 1 ∧ ∀ a b, c i (a + b) = c i a * c i b) → ∃ (J : Type) (_ : Fintype J) (κ : J → (Fin N → ℝ) → ℂ) (l : J → List (Fin N)), (∀ j, Continuous (κ j)) ∧ ∀ (d : Fin N → K → K) (S : Set K), (∀ v ∈ S, ∀ i, d i v ∈ S ∧ HasDerivAt (fun t : ℝ => ρ (c i t) v) (d i v) 0) → ∀ v ∈ S, v = ∑ j, ∫ t in Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s), κ j t • ρ (List.ofFn fun i => c i (t i)).prod ((l j).foldr d v) := by
  intro G _ _ _ K _ _ _ ρ _ hcont s hs N
  induction N with
  | zero =>
    intro c hc
    refine ⟨Unit, inferInstance, fun _ _ => 1, fun _ => [], fun _ => continuous_const, ?_⟩
    intro d S hS v hv
    simp [Measure.real, Real.volume_Icc_pi]
  | succ N ih =>
    intro c hc
    obtain ⟨J, hJ, κ, l, hκ, hrep⟩ := ih (fun i => c (Fin.castSucc i)) (fun i => hc _)
    have hinit : Continuous (fun t : Fin (N + 1) → ℝ => Fin.init t) :=
      continuous_pi fun i => continuous_apply (Fin.castSucc i)
    refine ⟨J × Bool, inferInstance,
      fun p t => κ p.1 (Fin.init t) * (if p.2 then ((1 / s : ℝ) : ℂ)
        else -(((s - t (Fin.last N)) / s : ℝ) : ℂ)),
      fun p => if p.2 then (l p.1).map Fin.castSucc else Fin.last N :: (l p.1).map Fin.castSucc,
      ?_, ?_⟩
    · rintro ⟨j, _ | _⟩
      · simp only [Bool.false_eq_true, if_false]
        exact ((hκ j).comp hinit).mul (by fun_prop)
      · simp only [if_true]
        exact ((hκ j).comp hinit).mul continuous_const
    intro d S hS v hv
    have hS' : ∀ v ∈ S, ∀ i : Fin N, d (Fin.castSucc i) v ∈ S ∧
        HasDerivAt (fun t : ℝ => ρ (c (Fin.castSucc i) t) v) (d (Fin.castSucc i) v) 0 :=
      fun v hv i => hS v hv _
    have h1 := hrep (fun i => d (Fin.castSucc i)) S hS' v hv
    have hmem : ∀ l' : List (Fin N), l'.foldr (fun i => d (Fin.castSucc i)) v ∈ S := by
      intro l'
      induction l' with
      | nil => exact hv
      | cons a l' ihl => exact (hS _ ihl _).1
    have hfold : ∀ l' : List (Fin N),
        (l'.map Fin.castSucc).foldr d v = l'.foldr (fun i => d (Fin.castSucc i)) v := by
      intro l'
      rw [List.foldr_map]
    have hPc : ∀ x : K, Continuous fun t : Fin N → ℝ =>
        ρ (List.ofFn fun i => c (Fin.castSucc i) (t i)).prod x := fun x =>
      (hcont x).comp (_root_.GlobalTheory.continuous_prod_ofFn_curves N _ fun i => (hc _).1)
    have hcF : ∀ (f : (Fin (N + 1) → ℝ) → ℂ) (x : K), Continuous f →
        Continuous fun t => f t • ρ (List.ofFn fun i => c i (t i)).prod x := fun f x hf =>
      hf.smul ((hcont x).comp (_root_.GlobalTheory.continuous_prod_ofFn_curves _ c fun i => (hc i).1))
    have hprod : ∀ (t : Fin N → ℝ) (r : ℝ),
        (List.ofFn fun i => c i ((Fin.snoc t r : Fin (N + 1) → ℝ) i)).prod =
          (List.ofFn fun i => c (Fin.castSucc i) (t i)).prod * c (Fin.last N) r := by
      intro t r
      rw [List.ofFn_succ', List.prod_concat]
      simp
    rw [Fintype.sum_prod_type]
    refine h1.trans (Finset.sum_congr rfl fun j _ => ?_)
    simp only [Fintype.sum_bool, if_true, Bool.false_eq_true, if_false, List.foldr_cons, hfold]
    rw [integral_cube_succ_eq_iterated N s _ (hcF (fun t => κ j (Fin.init t) * ((1 / s : ℝ) : ℂ)) _
        (((hκ j).comp hinit).mul continuous_const)),
      integral_cube_succ_eq_iterated N s _
        (hcF (fun t => κ j (Fin.init t) * -(((s - t (Fin.last N)) / s : ℝ) : ℂ)) _
        (((hκ j).comp hinit).mul (by fun_prop)))]
    simp only [Fin.init_snoc, Fin.snoc_last, hprod, map_mul, ContinuousLinearMap.mul_apply]
    set u := (l j).foldr (fun i => d (Fin.castSucc i)) v with hu_def
    have hu : u ∈ S := hmem _
    set cl := c (Fin.last N) with hcl
    have hA := eq_interval_average_sub_weighted_deriv ρ hcont hs cl (hc _).1 (hc _).2.1
      (hc _).2.2 u (d (Fin.last N) u) (hS u hu _).2
    have hI1 : IntegrableOn (fun r => ((1 / s : ℝ) : ℂ) • ρ (cl r) u) (Set.Icc 0 s) :=
      (continuous_const.smul ((hcont u).comp (hc _).1)).continuousOn.integrableOn_compact
        isCompact_Icc
    have hI2 : IntegrableOn (fun r => (((s - r) / s : ℝ) : ℂ) • ρ (cl r) (d (Fin.last N) u))
        (Set.Icc 0 s) :=
      ((Complex.continuous_ofReal.comp ((continuous_const.sub continuous_id).div_const s)).smul
        ((hcont _).comp (hc _).1)).continuousOn.integrableOn_compact isCompact_Icc
    have e1 : ∀ t : Fin N → ℝ, ∫ r in Set.Icc (0 : ℝ) s, (κ j t * ((1 / s : ℝ) : ℂ)) •
        ρ (List.ofFn fun i => c (Fin.castSucc i) (t i)).prod (ρ (cl r) u) =
        κ j t • ρ (List.ofFn fun i => c (Fin.castSucc i) (t i)).prod
          (∫ r in Set.Icc 0 s, ((1 / s : ℝ) : ℂ) • ρ (cl r) u) := by
      intro t
      rw [← ContinuousLinearMap.integral_comp_comm _ hI1, ← integral_smul]
      congr 1
      funext r
      rw [map_smul, smul_smul]
    have e2 : ∀ t : Fin N → ℝ, ∫ r in Set.Icc (0 : ℝ) s, (κ j t * -(((s - r) / s : ℝ) : ℂ)) •
        ρ (List.ofFn fun i => c (Fin.castSucc i) (t i)).prod (ρ (cl r) (d (Fin.last N) u)) =
        -(κ j t • ρ (List.ofFn fun i => c (Fin.castSucc i) (t i)).prod
          (∫ r in Set.Icc 0 s, (((s - r) / s : ℝ) : ℂ) • ρ (cl r) (d (Fin.last N) u))) := by
      intro t
      rw [← ContinuousLinearMap.integral_comp_comm _ hI2, ← integral_smul, ← integral_neg]
      congr 1
      funext r
      rw [map_smul, smul_smul, mul_neg, neg_smul]
    simp only [e1, e2]
    have hcube : IsCompact (Set.univ.pi fun _ : Fin N => Set.Icc (0 : ℝ) s) :=
      isCompact_univ_pi fun _ => isCompact_Icc
    have hi : ∀ x : K, IntegrableOn (fun t : Fin N → ℝ =>
        κ j t • ρ (List.ofFn fun i => c (Fin.castSucc i) (t i)).prod x)
        (Set.univ.pi fun _ => Set.Icc (0 : ℝ) s) := fun x =>
      ((hκ j).smul (hPc x)).continuousOn.integrableOn_compact hcube
    rw [integral_neg, ← sub_eq_add_neg, ← integral_sub (hi _) (hi _)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only
    rw [← smul_sub, ← map_sub, ← hA]

end GlobalTheory.CubeTaylor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfOrthogonalTranslatesProj
section
open MeasureTheory Complex
open scoped InnerProductSpace Real

namespace GlobalTheory.RealWeil

section Abstract

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {J : V ≃ₗᵢ[ℝ] V}
  {ρ : V → H →L[ℂ] H}

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [CompleteSpace H] in

theorem IsHeis.inner_left (hJ : ∀ x, J (J x) = -x) (h : IsHeis (omJ J) ρ) (u : V) (x y : H) :
    ⟪ρ u x, y⟫_ℂ = ⟪x, ρ (-u) y⟫_ℂ := by
  have h0 : omJ J u (-u) = 0 := by
    have := omJ_skew hJ u u
    have e : omJ J u (-u) = -omJ J u u := by simp [omJ]
    linarith
  have e : ρ u (ρ (-u) y) = y := by
    rw [h.2.1, h0, add_neg_cancel, h.1]
    simp
  have := (⟨(ρ u : H →ₗ[ℂ] H), h.2.2.1 u⟩ : H →ₗᵢ[ℂ] H).inner_map_map x (ρ (-u) y)
  rw [← this]
  change _ = ⟪ρ u x, ρ u (ρ (-u) y)⟫_ℂ
  rw [e]

theorem inner_proj_right {om : V → V → ℝ} (h : IsHeis om ρ) (x y : H) :
    ⟪x, proj h y⟫_ℂ = ∫ u, gau u * ⟪x, ρ u y⟫_ℂ := by
  rw [proj_apply, ← integral_inner (h.integrable y)]
  simp only [inner_smul_right]

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem conj_gau (u : V) : (starRingEnd ℂ) (gau u) = gau u := by
  unfold gau
  rw [← Complex.exp_conj]
  simp [map_ofNat]

theorem inner_proj_left (hJ : ∀ x, J (J x) = -x) (h : IsHeis (omJ J) ρ) (x y : H) :
    ⟪proj h x, y⟫_ℂ = ⟪x, proj h y⟫_ℂ := by
  rw [← inner_conj_symm, inner_proj_right, inner_proj_right, ← integral_conj,
    ← integral_neg_eq_self (fun u => gau u * ⟪x, ρ u y⟫_ℂ)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [map_mul, conj_gau, inner_conj_symm, gau_neg, h.inner_left hJ]

theorem integral_gau_mul_gau : ∫ u : V, gau u * gau u = 1 := by
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have key := GaussianFourier.integral_cexp_neg_mul_sq_norm (V := V) (b := (π : ℂ))
    (by simpa using Real.pi_pos)
  rw [div_self hpi, one_cpow] at key
  rw [← key]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [gau, ← Complex.exp_add]
  congr 1
  ring

theorem proj_idem (hJ : ∀ x, J (J x) = -x) (h : IsHeis (omJ J) ρ) (x : H) :
    proj h (proj h x) = proj h x := by
  have := proj_heis_proj hJ h 0 x
  rwa [h.1, gau_zero, one_smul] at this

theorem proj_eq_self_of_vacuum (hJ : ∀ x, J (J x) = -x) (h : IsHeis (omJ J) ρ) {v : H}
    (hv : ∀ a, ⟪v, ρ a v⟫_ℂ = gau a * ⟪v, v⟫_ℂ) : proj h v = v := by
  have h1 : ⟪v, proj h v⟫_ℂ = ⟪v, v⟫_ℂ := by
    rw [inner_proj_right]
    simp only [hv, ← mul_assoc]
    rw [integral_mul_const, integral_gau_mul_gau, one_mul]
  rw [← sub_eq_zero, ← inner_self_eq_zero (𝕜 := ℂ), inner_sub_left, inner_sub_right, inner_sub_right,
    inner_proj_left hJ, inner_proj_left hJ, proj_idem hJ, h1]
  ring

theorem eq_zero_of_orthogonal_translates_proj (hJ : ∀ x, J (J x) = -x) (h : IsHeis (omJ J) ρ) {x : H}
    (hx : ∀ y a, ⟪ρ a (proj h y), x⟫_ℂ = 0) : x = 0 := by
  have h1 : ∀ a, proj h (ρ (-a) x) = 0 := fun a => by
    refine ext_inner_left ℂ fun y => ?_
    rw [← inner_proj_left hJ, ← h.inner_left hJ, hx, inner_zero_right]
  have hg : Good h x := fun n => by simp [h1]
  rw [← hg.inversion hJ]
  simp [h1]

end Abstract

noncomputable def signUnit (p q : ℕ) : Fin p ⊕ Fin q → Circle :=
  Sum.elim (fun _ => ⟨I, by simp [Submonoid.unitSphere]⟩) (fun _ => ⟨-I, by simp [Submonoid.unitSphere]⟩)

noncomputable def signJ (p q : ℕ) : EuclideanSpace ℂ (Fin p ⊕ Fin q) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin p ⊕ Fin q) :=
  LinearIsometryEquiv.piLpCongrRight 2 fun a => rotation (signUnit p q a)

theorem gau_toLp {ι : Type} [Fintype ι] (z : EuclideanSpace ℂ ι) :
    gau z = Complex.exp (-(Real.pi / 2) * ∑ a, ((‖z a‖ ^ 2 : ℝ) : ℂ)) := by
  rw [gau, ← ofReal_sum, ← EuclideanSpace.norm_sq_eq]
  push_cast
  rfl

end GlobalTheory.RealWeil
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivalenceGeneratedTorusRel
section
open NumberField Matrix GlobalTheory.AdLat GlobalTheory.UCls

noncomputable section
namespace GlobalTheory.UCls
open scoped TensorProduct
open IsDedekindDomain

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

theorem isKM_mul {c : E ≃ₐ[F] E} {G : Matrix (Fin n) (Fin n) E} {L : Set (Fin n → E)} {M : ℕ}
    {k k' : Matrix (Fin n) (Fin n) (RA F E)} (hk : IsKM c G L M k) (hk' : IsKM c G L M k') :
    IsKM c G L M (k * k') := by
  obtain ⟨⟨hd, hh⟩, h2, h3⟩ := hk
  obtain ⟨⟨hd', hh'⟩, h2', h3'⟩ := hk'
  refine ⟨⟨by rw [det_mul]; exact hd.mul hd', fun x y => ?_⟩, fun x hx => ?_, fun x hx => ?_⟩
  · rw [← mulVec_mulVec, ← mulVec_mulVec, hh, hh']
  · obtain ⟨y2, hy2, e2⟩ := h2' x hx
    have hx' : k' *ᵥ x ∈ hat F L := by
      have : k' *ᵥ x = x + M • y2 := by rw [← e2]; abel
      rw [this]; exact add_mem hx (nsmul_mem hy2 _)
    obtain ⟨y1, hy1, e1⟩ := h2 _ hx'
    refine ⟨y1 + y2, add_mem hy1 hy2, ?_⟩
    rw [← mulVec_mulVec, smul_add, ← e1, ← e2]; abel
  · obtain ⟨y1, hy1, e1⟩ := h3 x hx
    obtain ⟨y2, hy2, e2⟩ := h3' y1 hy1
    exact ⟨y2, hy2, by rw [← mulVec_mulVec, e2, e1]⟩

theorem isKM_inv {c : E ≃ₐ[F] E} {G : Matrix (Fin n) (Fin n) E} {L : Set (Fin n → E)} {M : ℕ}
    {k : Matrix (Fin n) (Fin n) (RA F E)} (hk : IsKM c G L M k) :
    IsKM c G L M k⁻¹ := by
  obtain ⟨⟨hd, hh⟩, h2, h3⟩ := hk
  have hkk : k * k⁻¹ = 1 := mul_nonsing_inv k hd
  have hkk' : k⁻¹ * k = 1 := nonsing_inv_mul k hd
  have hmem : ∀ x ∈ hat F L, k *ᵥ x ∈ hat F L := by
    intro x hx
    obtain ⟨y, hy, e⟩ := h2 x hx
    have : k *ᵥ x = x + M • y := by rw [← e]; abel
    rw [this]; exact add_mem hx (nsmul_mem hy _)
  refine ⟨⟨?_, fun x y => ?_⟩, fun x hx => ?_, fun x hx => ?_⟩
  · rw [det_nonsing_inv]; exact hd.ringInverse
  · rw [← hh, mulVec_mulVec, mulVec_mulVec, hkk, one_mulVec, one_mulVec]
  · obtain ⟨y, hy, e⟩ := h3 x hx
    obtain ⟨z, hz, ez⟩ := h2 y hy
    refine ⟨-z, neg_mem hz, ?_⟩
    have : k⁻¹ *ᵥ x = y := by rw [← e, mulVec_mulVec, hkk', one_mulVec]
    rw [this, ← e, smul_neg, ← ez]; abel
  · exact ⟨k *ᵥ x, hmem x hx, by rw [mulVec_mulVec, hkk', one_mulVec]⟩

theorem tEquiv_refl (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (L : Set (Fin n → E)) (M : ℕ) (t : RA F E) :
    TEquiv c G L M t t :=
  ⟨1, by simp, 1, isKM_one c G L M, by simp [Algebra.TensorProduct.one_def.symm]⟩

theorem tEquiv_symm {c : E ≃ₐ[F] E} {G : Matrix (Fin n) (Fin n) E} {L : Set (Fin n → E)} {M : ℕ} {t t' : RA F E}
    (h : TEquiv c G L M t t') : TEquiv c G L M t' t := by
  obtain ⟨u, hu, k, hk, rfl⟩ := h
  have hu0 : u ≠ 0 := left_ne_zero_of_mul_eq_one hu
  refine ⟨u⁻¹, by rw [map_inv₀, ← mul_inv, hu, inv_one], k⁻¹, isKM_inv hk, ?_⟩
  have hd : IsUnit k.det := hk.1.1
  have e1 : ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] u⁻¹) * ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] u) = 1 := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, inv_mul_cancel₀ hu0, Algebra.TensorProduct.one_def]
  have e2 : k.det * k⁻¹.det = 1 := by rw [det_nonsing_inv, Ring.mul_inverse_cancel _ hd]
  calc t = (((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] u⁻¹) * ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] u)) * t * (k.det * k⁻¹.det) := by
        rw [e1, e2, one_mul, mul_one]
    _ = _ := by ring

theorem tEquiv_trans {c : E ≃ₐ[F] E} {G : Matrix (Fin n) (Fin n) E} {L : Set (Fin n → E)} {M : ℕ} {t t' t'' : RA F E}
    (h : TEquiv c G L M t t') (h' : TEquiv c G L M t' t'') : TEquiv c G L M t t'' := by
  obtain ⟨u, hu, k, hk, rfl⟩ := h
  obtain ⟨u', hu', k', hk', rfl⟩ := h'
  refine ⟨u' * u, ?_, k * k', isKM_mul hk hk', ?_⟩
  · rw [map_mul]
    calc u' * u * (c u' * c u) = (u' * c u') * (u * c u) := by ring
      _ = 1 := by rw [hu, hu', one_mul]
  · have e : ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (u' * u)) = ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] u') * ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] u) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rw [det_mul, e]; ring

theorem tEquiv_of_eqvGen {c : E ≃ₐ[F] E} {G : Matrix (Fin n) (Fin n) E} {L : Set (Fin n → E)} {M : ℕ}
    (a b : {t : RA F E // IsTA c t})
    (h : Relation.EqvGen (fun a b : {t : RA F E // IsTA c t} => TEquiv c G L M a.1 b.1) a b) :
    TEquiv c G L M a.1 b.1 :=
  (Equivalence.eqvGen_iff (r := fun a b : {t : RA F E // IsTA c t} => TEquiv c G L M a.1 b.1)
    ⟨fun a => tEquiv_refl c G L M a.1, fun h => tEquiv_symm h, fun h h' => tEquiv_trans h h'⟩).1 h

end GlobalTheory.UCls
end

theorem GlobalTheory.UCls.torus_eqvGen_main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r M : ℕ) (G : Matrix (Fin r) (Fin r) E) (L : Set (Fin r → E)) (a b : {t : RA (maximalRealSubfield E) E // IsTA (IsCMField.complexConj E) t}), Relation.EqvGen (fun a b : {t : RA (maximalRealSubfield E) E // IsTA (IsCMField.complexConj E) t} => TEquiv (IsCMField.complexConj E) G L M a.1 b.1) a b → TEquiv (IsCMField.complexConj E) G L M a.1 b.1 :=
  by intro E _ _ _ r M G L a b h; exact GlobalTheory.UCls.tEquiv_of_eqvGen a b h
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalizationOfInjectiveCokernelKilled
section
open IsLocalRing TensorProduct Pointwise

namespace GlobalTheory

theorem etale_localization_of_cokernel_killed (S : Type) [CommRing S] (A B : Type) [CommRing A]
    [CommRing B] [Algebra S A] [Algebra S B] (ι : A →ₐ[S] B) (hι : Function.Injective ι)
    (p : Ideal S) [p.IsPrime] (s : S) (hs : s ∉ p) (hB : ∀ y : B, s • y ∈ ι.range)
    (hA : Algebra.Etale (Localization.AtPrime p) (TensorProduct S (Localization.AtPrime p) A)) :
    Algebra.Etale (Localization.AtPrime p) (TensorProduct S (Localization.AtPrime p) B) := by
  let Φ : TensorProduct S (Localization.AtPrime p) A →ₐ[Localization.AtPrime p]
      TensorProduct S (Localization.AtPrime p) B :=
    Algebra.TensorProduct.map (AlgHom.id (Localization.AtPrime p) (Localization.AtPrime p)) ι
  have inj : Function.Injective Φ :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := Localization.AtPrime p)
      (ι.toLinearMap.restrictScalars S) hι
  have hu : IsUnit (algebraMap S (Localization.AtPrime p) s) :=
    IsLocalization.map_units (Localization.AtPrime p) (⟨s, hs⟩ : p.primeCompl)
  obtain ⟨u, hu'⟩ := hu
  have surj : Function.Surjective Φ := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | tmul r y =>
      obtain ⟨a, ha⟩ := hB y
      refine ⟨(r * ↑u⁻¹) ⊗ₜ a, ?_⟩
      simp only [Φ, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      rw [show ι a = s • y from ha, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
        Algebra.smul_def, ← hu', mul_left_comm, Units.mul_inv, mul_one]
    | add x y hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a + b, map_add _ _ _⟩
  exact Algebra.Etale.of_equiv (AlgEquiv.ofBijective Φ ⟨inj, surj⟩)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleMaximalQuotientAlgebraicStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_maximal_quotient_algebraic : ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], ¬ IsField B → ∀ (f : B), f ≠ 0 → ∀ (A' : Type) [CommRing A'] [Algebra B A'] [Algebra.Etale B A'] (M : MaximalSpectrum (FractionRing (Localization.Away (algebraMap B A' f)))), ∃ _ : Algebra (RatFunc k) (FractionRing (Localization.Away (algebraMap B A' f)) ⧸ M.asIdeal), Algebra.IsAlgebraic (RatFunc k) (FractionRing (Localization.Away (algebraMap B A' f)) ⧸ M.asIdeal) := by
  first | (exact @GlobalTheory.FracAlgEtale.exists_isAlgebraic_ratFunc_residue) | (exact GlobalTheory.FracAlgEtale.exists_isAlgebraic_ratFunc_residue) | (intros; apply GlobalTheory.FracAlgEtale.exists_isAlgebraic_ratFunc_residue  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleNbhdLocalRingToHenselisationAlgebraMapStatement
section
open IsLocalRing GlobalTheory.Henselisation
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleNbhdLocalRingToHenselisation_algebraMap : ∀ (R : Type) [CommRing R] [IsLocalRing R] (i : EtNbhd R) (r : R), Hens.of i (algebraMap R i.B r) = algebraMap R (Hens R) r := by
  first | exact @GlobalTheory.Henselisation.Hens.of_algebraMap | exact GlobalTheory.Henselisation.Hens.of_algebraMap | (intros; apply GlobalTheory.Henselisation.Hens.of_algebraMap <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleNbhdLocalRingTransitionMapIsLocalHomInjectiStatement
section
open IsLocalRing GlobalTheory.Henselisation
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleNbhdLocalRingTransitionMap_isLocalHom_injective : ∀ (R : Type) [CommRing R] [IsLocalRing R] (i j : EtNbhd R) (h : i ≤ j), IsLocalHom (EtNbhd.trans h) ∧ Function.Injective (EtNbhd.trans h) := by
  first | exact @GlobalTheory.Henselisation.EtNbhd.trans_isLocalHom_injective | exact GlobalTheory.Henselisation.EtNbhd.trans_isLocalHom_injective | (intros; apply GlobalTheory.Henselisation.EtNbhd.trans_isLocalHom_injective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsActionFactorThroughTensorCharacterStatement
section
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_action_factor_through_tensor_character : ∀ (k : Type) [Field k] (C O B : Type) [CommRing C] [Ring O] [Algebra C O] [Algebra C k] [Ring B] [Algebra k B] (e : (k ⊗[C] O) ≃ₐ[k] B) (X : Type) [AddCommGroup X] [Module k X] (σX : O →+* Module.End k X), (∀ c, σX (algebraMap C O c) = algebraMap C k c • 1) → ∃ ρX : B →ₐ[k] Module.End k X, ∀ o, ρX (e (1 ⊗ₜ[C] o)) = σX o := by
  first | (exact @GlobalTheory.tensor_action_factors) | (exact GlobalTheory.tensor_action_factors) | (intros; apply GlobalTheory.tensor_action_factors  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCandidateBorelMoveOpenFramesBaireStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_candidate_borel_move_open_frames_baire : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (S : Set (GL (Fin r) E)) (a c : GL (Fin r) E) (W : Set (Frame X.Ψ r)), IsOpen W → W.Nonempty → W ⊆ X.dom → (∀ z ∈ W, ∃ γ ∈ S, ∃ b ∈ Bor X.Ψ r, lact c z = rmul (lact γ (lact a z)) b) → ∃ γ ∈ S, ∃ V : Set (Frame X.Ψ r), IsOpen V ∧ V.Nonempty ∧ V ⊆ X.dom ∧ ∀ x ∈ V, ∃ b ∈ Bor X.Ψ r, lact ((γ * a)⁻¹ * c) x = rmul x b := by
  first | exact @GlobalTheory.baire_one_candidate | exact GlobalTheory.baire_one_candidate | (intros; apply GlobalTheory.baire_one_candidate <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousRepresentativeAverageStatement
section
open MeasureTheory
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuous_representative_average : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (ι : K → G → ℂ), (∀ C, IsCompact C → ∃ M : ℝ, ∀ v, IntegrableOn (ι v) C μ ∧ ∫ x in C, ‖ι v x‖ ∂μ ≤ M * ‖v‖) → (∀ (a : ℂ) v w, ι (a • v + w) =ᵐ[μ] fun x => a * ι v x + ι w x) → ∀ (ρ : G →* (K →L[ℂ] K)), (∀ g v, ‖ρ g v‖ = ‖v‖) → (∀ v, Continuous fun g => ρ g v) → (∀ g v, ι (ρ g v) =ᵐ[μ] fun x => ι v (x * g)) → ∀ (η : G → ℂ) (v : K), Continuous η → HasCompactSupport η → ∃ φ : G → ℂ, Continuous φ ∧ ι (∫ y, η y • ρ y v ∂μ) =ᵐ[μ] φ := by
  first | exact @GlobalTheory.LocRep.exists_continuous_rep_average | exact GlobalTheory.LocRep.exists_continuous_rep_average | (intros; apply GlobalTheory.LocRep.exists_continuous_rep_average <;> assumption)
end

