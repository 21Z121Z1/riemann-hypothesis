import Mathlib
import ReciprocityTheory.AnalyticForms.MaIntEmpty
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0057
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0059
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0058
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0024
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0060
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRiemannExtensionAnalytic
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0048
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LowerBoundConditional

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLogLogCutHessConst
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A

noncomputable section

theorem hessC_of_eventually_const {D : ℕ} {φ : (Fin D → ℂ) → ℝ} {y : Fin D → ℂ} {c : ℝ}
    (h : φ =ᶠ[𝓝 y] fun _ => c) : hessC φ y = 0 ∧ hessC (fun z => φ z ^ 2 / 2) y = 0 := by
  have h2 : (fun z => φ z ^ 2 / 2) =ᶠ[𝓝 y] fun _ => c ^ 2 / 2 := by
    filter_upwards [h] with z hz
    rw [hz]
  have hc : ∀ a : ℝ, hessC (fun _ : Fin D → ℂ => a) y = 0 := by
    intro a
    ext i j
    simp [hessC]
  exact ⟨(hessC_congr' h).trans (hc c), (hessC_congr' h2).trans (hc _)⟩

theorem cutStep_of_one_le {s : ℝ} (hs : 1 ≤ s) : cutStep s = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem cutStep_of_le_half {s : ℝ} (hs : s ≤ 1 / 2) : cutStep s = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem continuousAt_normSq_eval {m : ℕ} (Q : MvPolynomial (Fin m) ℂ) (y : Fin m → ℂ) :
    ContinuousAt (fun z => ‖eval z Q‖ ^ 2) y :=
  ((AnalyticOnNhd.eval_mvPolynomial Q y (Set.mem_univ y)).continuousAt.norm).pow 2

theorem logLogCut_eventually_zero {m : ℕ} (Q : MvPolynomial (Fin m) ℂ) (k : ℕ) {y : Fin m → ℂ}
    (hy : ‖eval y Q‖ ^ 2 < cutLevel k) : logLogCut Q k =ᶠ[𝓝 y] fun _ => 0 := by
  filter_upwards [(continuousAt_normSq_eval Q y).preimage_mem_nhds (Iio_mem_nhds hy)] with z hz
  have hz : ‖eval z Q‖ ^ 2 < cutLevel k := hz
  have hlt := (cutLevel_mem k).2
  unfold logLogCut
  split_ifs with h0 h1
  · rfl
  · linarith
  · have hw0 : 0 < ‖eval z Q‖ ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm h0)
    have e1 : Real.log (‖eval z Q‖ ^ 2) < -Real.exp ((k : ℝ) + 1) :=
      (Real.log_lt_iff_lt_exp hw0).2 hz
    have e2 : (k : ℝ) + 1 < Real.log (-logAbsSq Q z) :=
      (Real.lt_log_iff_exp_lt (by rw [logAbsSq]; linarith [Real.exp_pos ((k : ℝ) + 1)])).2
        (by rw [logAbsSq]; linarith)
    apply cutStep_of_one_le
    rw [le_div_iff₀ (by positivity)]
    linarith

theorem logLogCut_eventually_one {m : ℕ} (Q : MvPolynomial (Fin m) ℂ) (k : ℕ) {y : Fin m → ℂ}
    (hy : Real.exp (-Real.exp (((k : ℝ) + 1) / 2)) < ‖eval y Q‖ ^ 2) :
    logLogCut Q k =ᶠ[𝓝 y] fun _ => 1 := by
  filter_upwards [(continuousAt_normSq_eval Q y).preimage_mem_nhds (Ioi_mem_nhds hy)] with z hz
  have hz : Real.exp (-Real.exp (((k : ℝ) + 1) / 2)) < ‖eval z Q‖ ^ 2 := hz
  have hw0 : 0 < ‖eval z Q‖ ^ 2 := lt_trans (Real.exp_pos _) hz
  unfold logLogCut
  split_ifs with h0 h1
  · linarith
  · rfl
  · have hw1 : ‖eval z Q‖ ^ 2 < 1 := not_le.1 h1
    have e1 : -Real.exp (((k : ℝ) + 1) / 2) < Real.log (‖eval z Q‖ ^ 2) :=
      (Real.lt_log_iff_exp_lt hw0).2 hz
    have e0 : Real.log (‖eval z Q‖ ^ 2) < 0 := Real.log_neg hw0 hw1
    have e2 : Real.log (-logAbsSq Q z) < ((k : ℝ) + 1) / 2 :=
      (Real.log_lt_iff_lt_exp (by rw [logAbsSq]; linarith)).2 (by rw [logAbsSq]; linarith)
    apply cutStep_of_le_half
    rw [div_le_iff₀ (by positivity)]
    linarith

theorem logLogCut_eventually_step {m : ℕ} (Q : MvPolynomial (Fin m) ℂ) (k : ℕ) {y : Fin m → ℂ}
    (h0 : 0 < ‖eval y Q‖ ^ 2) (h1 : ‖eval y Q‖ ^ 2 < 1) :
    logLogCut Q k =ᶠ[𝓝 y] fun z => cutStep (Real.log (-logAbsSq Q z) / ((k : ℝ) + 1)) := by
  filter_upwards [(continuousAt_normSq_eval Q y).preimage_mem_nhds (Ioo_mem_nhds h0 h1)] with z hz
  have hz : ‖eval z Q‖ ^ 2 ∈ Set.Ioo (0 : ℝ) 1 := hz
  unfold logLogCut
  rw [if_neg hz.1.ne', if_neg (not_le.2 hz.2)]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLogLogCutHessDeriv
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Filter Topology
open scoped ContDiff

noncomputable section

theorem smoothTransition_eventually_const {x : ℝ} (hx : x ∉ Set.Icc (0 : ℝ) 1) :
    ∃ c : ℝ, Real.smoothTransition =ᶠ[𝓝 x] fun _ => c := by
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
  rcases hx with h | h
  · refine ⟨0, ?_⟩
    filter_upwards [Iio_mem_nhds h] with y hy
    exact Real.smoothTransition.zero_of_nonpos (le_of_lt hy)
  · refine ⟨1, ?_⟩
    filter_upwards [Ioi_mem_nhds h] with y hy
    exact Real.smoothTransition.one_of_one_le (le_of_lt hy)

theorem smoothTransition_deriv_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |deriv Real.smoothTransition x| ≤ C ∧
      |deriv (deriv Real.smoothTransition) x| ≤ C := by
  have hsm : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  obtain ⟨-, h1⟩ := contDiff_infty_iff_deriv.1 hsm
  obtain ⟨-, h2⟩ := contDiff_infty_iff_deriv.1 h1
  obtain ⟨C1, hC1⟩ := isCompact_Icc.exists_bound_of_continuousOn (h1.continuous.continuousOn (s := Set.Icc (0 : ℝ) 1))
  obtain ⟨C2, hC2⟩ := isCompact_Icc.exists_bound_of_continuousOn (h2.continuous.continuousOn (s := Set.Icc (0 : ℝ) 1))
  refine ⟨max (max C1 C2) 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : x ∈ Set.Icc (0 : ℝ) 1
  · have a := hC1 x hx
    have b := hC2 x hx
    rw [Real.norm_eq_abs] at a b
    exact ⟨a.trans ((le_max_left _ _).trans (le_max_left _ _)),
      b.trans ((le_max_right _ _).trans (le_max_left _ _))⟩
  · obtain ⟨c, hc⟩ := smoothTransition_eventually_const hx
    have hd := hc.deriv
    have e1 : deriv Real.smoothTransition x = 0 := by rw [hd.eq_of_nhds]; simp
    have e2 : deriv (deriv Real.smoothTransition) x = 0 := by rw [hd.deriv_eq]; simp
    rw [e1, e2, abs_zero]
    exact ⟨le_max_right _ _, le_max_right _ _⟩

theorem logLogStep_arith {C c t p q f v w : ℝ} (hC0 : 0 ≤ C) (hc : 1 ≤ c) (ht : t ≠ 0) (hp : |p| ≤ C)
    (hq : |q| ≤ C) (hf : |f| ≤ 1) (hv : v = -(2 * (t⁻¹ / c))) (hw : w = -(2 * (-(t ^ 2)⁻¹ / c))) :
    |q * v * v + p * w| ≤ (6 * C + 4 * C ^ 2) / (c * t ^ 2) ∧
      |p * v * (p * v) + f * (q * v * v + p * w)| ≤ (6 * C + 4 * C ^ 2) / (c * t ^ 2) := by
  have hc0 : 0 < c := by linarith
  have hD : 0 < c * t ^ 2 := by positivity
  have hvv : v * v ≤ 4 / (c * t ^ 2) := by
    have e : v * v = 4 / (c * t ^ 2) / c := by rw [hv]; field_simp; ring
    rw [e]; exact div_le_self (by positivity) hc
  have hvv0 : 0 ≤ v * v := mul_self_nonneg v
  have hw' : |w| = 2 / (c * t ^ 2) := by
    have e : w = 2 / (c * t ^ 2) := by rw [hw]; field_simp
    rw [e, abs_of_pos (by positivity)]
  have h1 : |q * v * v + p * w| ≤ 6 * C / (c * t ^ 2) := by
    calc |q * v * v + p * w| ≤ |q * v * v| + |p * w| := abs_add_le _ _
      _ = |q| * (v * v) + |p| * |w| := by rw [mul_assoc, abs_mul q, abs_of_nonneg hvv0, abs_mul p]
      _ ≤ C * (4 / (c * t ^ 2)) + C * (2 / (c * t ^ 2)) := by rw [hw']; gcongr
      _ = 6 * C / (c * t ^ 2) := by ring
  have h2 : p * v * (p * v) ≤ 4 * C ^ 2 / (c * t ^ 2) := by
    calc p * v * (p * v) = |p| ^ 2 * (v * v) := by rw [sq_abs]; ring
      _ ≤ C ^ 2 * (4 / (c * t ^ 2)) := by gcongr
      _ = 4 * C ^ 2 / (c * t ^ 2) := by ring
  have hK : 6 * C / (c * t ^ 2) ≤ (6 * C + 4 * C ^ 2) / (c * t ^ 2) := by
    gcongr; nlinarith
  refine ⟨h1.trans hK, ?_⟩
  calc |p * v * (p * v) + f * (q * v * v + p * w)|
      ≤ |p * v * (p * v)| + |f * (q * v * v + p * w)| := abs_add_le _ _
    _ ≤ 4 * C ^ 2 / (c * t ^ 2) + 1 * (6 * C / (c * t ^ 2)) := by
      rw [abs_of_nonneg (mul_self_nonneg (p * v)), abs_mul]; gcongr
    _ = (6 * C + 4 * C ^ 2) / (c * t ^ 2) := by ring

theorem logLogStep_deriv2_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ c : ℝ, 1 ≤ c → ∀ t : ℝ, t < 0 →
      ContDiffAt ℝ 2 (fun x => cutStep (Real.log (-x) / c)) t ∧
      ContDiffAt ℝ 2 (fun x => cutStep (Real.log (-x) / c) ^ 2 / 2) t ∧
      |deriv (deriv fun x => cutStep (Real.log (-x) / c)) t| ≤ K / (c * t ^ 2) ∧
      |deriv (deriv fun x => cutStep (Real.log (-x) / c) ^ 2 / 2) t| ≤ K / (c * t ^ 2) := by
  obtain ⟨C, hC0, hC⟩ := smoothTransition_deriv_bound
  refine ⟨6 * C + 4 * C ^ 2, by positivity, fun c hc t ht => ?_⟩
  have hc0 : 0 < c := by linarith
  set σ := Real.smoothTransition with hσdef
  have hsm : ContDiff ℝ ∞ σ := Real.smoothTransition.contDiff
  obtain ⟨hd0, h1⟩ := contDiff_infty_iff_deriv.1 hsm
  obtain ⟨hd1, -⟩ := contDiff_infty_iff_deriv.1 h1
  let u : ℝ → ℝ := fun x => 2 - 2 * (Real.log (-x) / c)
  let u' : ℝ → ℝ := fun x => -(2 * (x⁻¹ / c))
  let u'' : ℝ → ℝ := fun x => -(2 * (-(x ^ 2)⁻¹ / c))
  have hu : ∀ x, x < 0 → HasDerivAt u (u' x) x := by
    intro x hx
    have hl : HasDerivAt (fun x => Real.log (-x)) x⁻¹ x := by
      have := (hasDerivAt_neg x).log (by simpa using hx.ne)
      rwa [neg_div_neg_eq, one_div] at this
    exact ((hl.div_const c).const_mul 2).const_sub 2
  have hu' : ∀ x, x < 0 → HasDerivAt u' (u'' x) x := fun x hx =>
    (((hasDerivAt_inv hx.ne).div_const c).const_mul 2).neg
  let F : ℝ → ℝ := fun x => cutStep (Real.log (-x) / c)
  let G : ℝ → ℝ := fun x => deriv σ (u x) * u' x
  have hF : ∀ x, x < 0 → HasDerivAt F (G x) x := fun x hx =>
    (hd0 (u x)).hasDerivAt.comp x (hu x hx)
  have hG : HasDerivAt G (deriv (deriv σ) (u t) * u' t * u' t + deriv σ (u t) * u'' t) t :=
    ((hd1 (u t)).hasDerivAt.comp t (hu t ht)).mul (hu' t ht)
  have evF : deriv F =ᶠ[𝓝 t] G := by
    filter_upwards [Iio_mem_nhds ht] with x hx
    exact (hF x hx).deriv
  have hF2 : deriv (deriv F) t = deriv (deriv σ) (u t) * u' t * u' t + deriv σ (u t) * u'' t :=
    (hG.congr_of_eventuallyEq evF).deriv
  have hH : ∀ x, x < 0 → HasDerivAt (fun x => F x ^ 2 / 2) (F x * G x) x := by
    intro x hx
    have := ((hF x hx).fun_mul (hF x hx)).div_const 2
    exact (this.congr_deriv (by ring)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => by ring)
  have evH : deriv (fun x => F x ^ 2 / 2) =ᶠ[𝓝 t] fun x => F x * G x := by
    filter_upwards [Iio_mem_nhds ht] with x hx
    exact (hH x hx).deriv
  have hH2 : deriv (deriv fun x => F x ^ 2 / 2) t =
      G t * G t + F t * (deriv (deriv σ) (u t) * u' t * u' t + deriv σ (u t) * u'' t) :=
    (((hF t ht).fun_mul hG).congr_of_eventuallyEq evH).deriv
  have hucd : ContDiffAt ℝ 2 u t :=
    contDiffAt_const.sub (contDiffAt_const.mul ((contDiffAt_id.neg.log (by simpa using ht.ne)).div_const c))
  have hFcd : ContDiffAt ℝ 2 F t := (Real.smoothTransition.contDiffAt (n := 2)).comp t hucd
  have hf : |F t| ≤ 1 := by
    show |Real.smoothTransition (u t)| ≤ 1
    exact abs_le.2 ⟨by linarith [Real.smoothTransition.nonneg (u t)], Real.smoothTransition.le_one (u t)⟩
  obtain ⟨b1, b2⟩ := logLogStep_arith (p := deriv σ (u t)) (q := deriv (deriv σ) (u t)) hC0 hc ht.ne
    (hC _).1 (hC _).2 hf rfl rfl
  refine ⟨hFcd, (hFcd.pow 2).div_const 2, ?_, ?_⟩
  · rw [show deriv (deriv fun x => cutStep (Real.log (-x) / c)) t = _ from hF2]; exact b1
  · rw [show deriv (deriv fun x => cutStep (Real.log (-x) / c) ^ 2 / 2) t = _ from hH2]; exact b2

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PMassFromLelong
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem ConeIntegralMass.of_slices (hCP : ConeToProjective.Statement)
    (hS : SliceSectionMass.Statement) (hA : SectionHyperplaneAvoid.Statement)
    (hD : SectionDegreeSum.Statement) (hP : PointSliceMass.Statement) :
    ConeIntegralMass.Statement := by
  intro n e
  induction e with
  | zero =>
    intro δ h W f hW hf hδ
    obtain ⟨j, hj⟩ := hW.isRelevant
    have hℓ : linForm (Pi.single j (1 : ℂ)) ∉ W := by rwa [linForm_single]
    rw [hCP n 0 h W f (Pi.single j 1) (fun _ => 1) hW hf hℓ (fun _ _ _ => rfl) continuousOn_const]
    exact hP n δ h W f _ hW hf hδ hℓ
  | succ e ih =>
    intro δ h J f hJ hf hδ
    obtain ⟨j, hj⟩ := hJ.isRelevant
    have hu : linForm (Pi.single j (1 : ℂ)) ∉ J := by rwa [linForm_single]
    obtain ⟨ℓ, hℓ, hℓW⟩ := hA n J (Pi.single j 1) hJ
    obtain ⟨g, δW, hW, hsum⟩ := hD ℂ n e δ J f (Pi.single j 1) hJ hf hδ hu
    rw [hCP n (e + 1) h J f ℓ (fun _ => 1) hJ hf hℓ (fun _ _ _ => rfl) continuousOn_const,
      hS n e h J f (Pi.single j 1) ℓ hJ hf hu hℓ hℓW, hsum]
    push_cast
    refine Finset.sum_congr rfl fun W hWm => ?_
    obtain ⟨hWp, hWc, hWδ⟩ := hW W hWm
    rw [← hCP n e h W (g W) ℓ (fun _ => 1) hWp hWc (hℓW W hWm) (fun _ _ _ => rfl)
      continuousOn_const, ih (δW W) h W (g W) hWp hWc hWδ]

theorem MassFromLelong.proof (hS : SliceSectionMass.Statement)
    (hA : SectionHyperplaneAvoid.Statement) (hD : SectionDegreeSum.Statement)
    (hP : PointSliceMass.Statement) : MassFromLelong.Statement :=
  fun _ _ _ _ _ hCP _ => ConeIntegralMass.of_slices hCP hS hA hD hP

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalLocallyIrreducible
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology

theorem zeroSetIn_subset_closure_diff (hvan : VanishNearPoint.Statement) {σ : Type} [Fintype σ]
    (I : Ideal (MvPolynomial σ ℂ)) (h : MvPolynomial σ ℂ) (hI : I.IsPrime) (hh : h ∉ I) :
    zeroSetIn I ⊆ closure (zeroSetIn I \ {z | eval z h = 0}) := by
  intro z hz
  rw [mem_closure_iff_nhds]
  intro t ht
  by_contra hne
  set e := Fintype.equivFin σ with he
  set J : Ideal (MvPolynomial (Fin (Fintype.card σ)) ℂ) := I.comap (rename e.symm) with hJ
  have hre : ∀ q : MvPolynomial (Fin (Fintype.card σ)) ℂ, rename e (rename e.symm q) = q := by
    intro q
    rw [rename_rename, show (⇑e ∘ ⇑e.symm) = id from funext e.apply_symm_apply, rename_id_apply]
  have hre' : ∀ p : MvPolynomial σ ℂ, rename e.symm (rename e p) = p := by
    intro p
    rw [rename_rename, show (⇑e.symm ∘ ⇑e) = id from funext e.symm_apply_apply, rename_id_apply]
  have hJp : J.IsPrime := Ideal.comap_isPrime _ _
  have hmemJ : ∀ y : Fin (Fintype.card σ) → ℂ, y ∘ e ∈ zeroSetIn I → y ∈ zeroLocus J := by
    intro y hy q hq
    rw [← hre q, eval_rename]
    exact hy _ hq
  have hJZ : ∀ y : Fin (Fintype.card σ) → ℂ, y ∈ zeroLocus J → y ∘ e ∈ zeroSetIn I := by
    intro y hy p hp
    have := hy (rename e p) (by rw [hJ, Ideal.mem_comap, hre']; exact hp)
    rwa [eval_rename] at this
  have hx : z ∘ e.symm ∈ zeroLocus J := hmemJ _ (by
    rw [Function.comp_assoc, show (⇑e.symm ∘ ⇑e) = id from funext e.symm_apply_apply]
    exact hz)
  have hcont : Continuous fun y : Fin (Fintype.card σ) → ℂ => y ∘ e :=
    continuous_pi fun i => continuous_apply _
  have hlim : Filter.Tendsto (fun y : Fin (Fintype.card σ) → ℂ => y ∘ e) (𝓝 (z ∘ e.symm)) (𝓝 z) := by
    have := hcont.tendsto (z ∘ e.symm)
    rwa [Function.comp_assoc, show (⇑e.symm ∘ ⇑e) = id from funext e.symm_apply_apply,
      Function.comp_id] at this
  have hev : ∀ᶠ y in 𝓝 (z ∘ e.symm), y ∈ zeroLocus J → eval y (rename e h) = 0 := by
    filter_upwards [hlim ht] with y hyt hyJ
    rw [eval_rename]
    by_contra hne'
    exact hne ⟨y ∘ e, hyt, hJZ y hyJ, hne'⟩
  have hmem := hvan _ J (rename e h) _ hJp hx hev
  apply hh
  rw [hJ, Ideal.mem_comap, hre'] at hmem
  exact hmem

theorem NormalLocallyIrreducible.proof (hvan : VanishNearPoint.Statement)
    (hcon : NormalComplementConnected.Statement) : NormalLocallyIrreducible.Statement := by
  intro σ _ I h w hI hnorm hh hw U hU
  obtain ⟨B, hBo, hwB, hBU, hpre⟩ := hcon σ I h w hI hnorm hh hw U hU
  refine ⟨B, hBo, hwB, hBU, hpre, ?_⟩
  rintro z ⟨hzZ, hzB⟩
  have h1 : z ∈ B ∩ closure (zeroSetIn I \ {z | eval z h = 0}) :=
    ⟨hzB, zeroSetIn_subset_closure_diff hvan I h hI hh hzZ⟩
  refine closure_mono ?_ (hBo.inter_closure h1)
  rintro y ⟨hyB, hyZ, hyh⟩
  exact ⟨⟨hyZ, hyB⟩, hyh⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PParametricCircleIntegralAnalytic
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Metric Filter Topology Set Complex MeasureTheory

open scoped Real

noncomputable section

namespace ParametricCircleIntegralAnalytic

theorem analyticOnNhd_of_differentiableOn_fd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {O : Set E} {f : E → ℂ} (hO : IsOpen O) (hf : DifferentiableOn ℂ f O) :
    AnalyticOnNhd ℂ f O := by
  let e : E ≃L[ℂ] (Fin (Module.finrank ℂ E) → ℂ) :=
    ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℂ).symm
  have hO' : IsOpen (e.symm ⁻¹' O) := hO.preimage e.symm.continuous
  have hg : DifferentiableOn ℂ (f ∘ e.symm) (e.symm ⁻¹' O) :=
    hf.comp e.symm.differentiableOn (fun y hy => hy)
  have ha := RiemannExtensionAnalytic.analyticOnNhd_of_differentiableOn hO' hg
  intro x hx
  have h1 : AnalyticAt ℂ (f ∘ e.symm) (e x) := ha (e x) (by simpa using hx)
  have h2 := h1.comp (ContinuousLinearMap.analyticAt (e : E →L[ℂ] (Fin (Module.finrank ℂ E) → ℂ)) x)
  simpa [Function.comp_def] using h2

end ParametricCircleIntegralAnalytic

open ParametricCircleIntegralAnalytic in

theorem ParametricCircleIntegralAnalytic.proof : ParametricCircleIntegralAnalytic.Statement := by
  intro ι _ Φ O U c r hr hO hU hΦ hUO x₀ hx₀
  have hcd : ContinuousOn (fderiv ℂ Φ) O :=
    ((analyticOnNhd_of_differentiableOn_fd hO hΦ).contDiffOn_of_completeSpace (n := 1)).continuousOn_fderiv_of_isOpen
      hO le_rfl
  obtain ⟨u, v, hu, -, hx₀u, hsv, huv⟩ := generalized_tube_lemma isCompact_singleton (isCompact_sphere c r) hO
    (by rintro ⟨x, s⟩ ⟨hx, hs⟩; obtain rfl : x = x₀ := hx; exact hUO x hx₀ s hs)
  obtain ⟨ε, hε, hεu⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hu.mem_nhds (hx₀u rfl))
  have hK : closedBall x₀ ε ×ˢ sphere c r ⊆ O := fun p hp => huv ⟨hεu hp.1, hsv hp.2⟩
  obtain ⟨M, hM⟩ := ((isCompact_closedBall x₀ ε).prod (isCompact_sphere c r)).exists_bound_of_continuousOn
    (hcd.mono hK)
  have hmem : ∀ x ∈ closedBall x₀ ε, ∀ θ : ℝ, (x, circleMap c r θ) ∈ O := fun x hx θ =>
    hK ⟨hx, circleMap_mem_sphere c hr θ⟩
  have hcont : ∀ x ∈ closedBall x₀ ε,
      Continuous fun θ : ℝ => (circleMap 0 r θ * I) • Φ (x, circleMap c r θ) := fun x hx =>
    (by fun_prop : Continuous fun θ : ℝ => circleMap 0 r θ * I).smul
      (hΦ.continuousOn.comp_continuous (by fun_prop) (hmem x hx))
  have hdiff : DifferentiableOn ℂ (fun x => ∮ s in C(c, r), Φ (x, s)) (ball x₀ ε) := by
    intro x₁ hx₁
    have hs : ball x₀ ε ∈ 𝓝 x₁ := isOpen_ball.mem_nhds hx₁
    have hx₁c : x₁ ∈ closedBall x₀ ε := ball_subset_closedBall hx₁
    simp only [circleIntegral, deriv_circleMap]
    refine (intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume) (a := 0)
      (b := 2 * π) (F := fun x θ => (circleMap 0 r θ * I) • Φ (x, circleMap c r θ))
      (F' := fun x θ => (circleMap 0 r θ * I) •
        (fderiv ℂ Φ (x, circleMap c r θ)).comp (ContinuousLinearMap.inl ℂ (ι → ℂ) ℂ))
      (bound := fun _ => |r| * (M * ‖ContinuousLinearMap.inl ℂ (ι → ℂ) ℂ‖)) hs ?_ ?_ ?_ ?_ ?_
      ?_).differentiableAt.differentiableWithinAt
    · filter_upwards [hs] with x hx
      exact (hcont x (ball_subset_closedBall hx)).aestronglyMeasurable
    · exact (hcont x₁ hx₁c).intervalIntegrable _ _
    · refine Continuous.aestronglyMeasurable ?_
      exact (by fun_prop : Continuous fun θ : ℝ => circleMap 0 r θ * I).smul
        ((ContinuousLinearMap.compL ℂ (ι → ℂ) ((ι → ℂ) × ℂ) ℂ).flip
          (ContinuousLinearMap.inl ℂ (ι → ℂ) ℂ) |>.continuous.comp
          (hcd.comp_continuous (by fun_prop) (hmem x₁ hx₁c)))
    · refine Eventually.of_forall fun θ _ x hx => ?_
      rw [norm_smul, norm_mul, norm_circleMap_zero, Complex.norm_I, mul_one]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg r)
      refine (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
      exact hM _ ⟨ball_subset_closedBall hx, circleMap_mem_sphere c hr θ⟩
    · exact intervalIntegrable_const
    · refine Eventually.of_forall fun θ _ x hx => ?_
      have h1 : HasFDerivAt Φ (fderiv ℂ Φ (x, circleMap c r θ)) (x, circleMap c r θ) :=
        (hΦ.differentiableAt (hO.mem_nhds (hmem x (ball_subset_closedBall hx) θ))).hasFDerivAt
      exact (h1.comp x (hasFDerivAt_prodMk_left x (circleMap c r θ))).const_smul (circleMap 0 r θ * I)
  exact analyticOnNhd_of_differentiableOn_fd isOpen_ball hdiff x₀ (mem_ball_self hε)

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPrimeGermCanonicalCover
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

theorem PrimeGermCanonicalCover.proof (h₁ : PrimeGermPrimitivePresentation.Statement)
    (h₂ : PrimitivePresentationCover.Statement) : PrimeGermCanonicalCover.Statement := by
  intro σ _ w k p hp hP
  obtain ⟨d, A, ℓ, N, c, δ, hpres, hδ⟩ := h₁ σ w k p hp hP
  have hδa : AnalyticAt ℂ δ (A w) := hpres.2.1
  have hdiv := hpres.2.2.2.2.2.1
  refine ⟨d, A, ℓ, N, δ, hδa, hδ, ?_, h₂ σ w k p d A ℓ N c δ hp hpres⟩
  intro g hg
  obtain ⟨M, a, ha, h, hh, hev⟩ := hdiv g hg
  exact ⟨M, a, h, ha, hh, hev⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPrimitiveFormSheetedOffDiscriminant
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

theorem PrimitiveFormSheetedOffDiscriminant.proof (hcut : PrimitiveFormSheetedLocusCutOut.Statement)
    (hnear : PrimitiveFormSheetedPointsNear.Statement) : PrimitiveFormSheetedOffDiscriminant.Statement := by
  intro σ _ X w d A hX hirr hiso hinj ℓ N a δ q ha hδ hq hδ0 hP hsep hQ
  obtain ⟨c, e, hc, he, hce, hsh⟩ := hcut σ X w d A hX hiso ℓ N a δ q ha hδ hq hδ0 hP hsep hQ
  rcases hirr.2 c e hc he hce with hc0 | he0
  · exact ⟨_, hc0.and hsh, fun y hy hyδ => ((hy.2.2 hy.1 hyδ).1).2 (hy.2.1 hy.1)⟩
  · exfalso
    obtain ⟨z, hz, hzδ, hzs⟩ :=
      hnear σ X w d A hX hirr hiso hinj ℓ N a δ q ha hδ hq hδ0 hP hsep hQ _ (he0.and hsh)
    exact (hz.2.2 hz.1 hzδ).2 hzs (hz.2.1 hz.1)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSectionDegreeSum
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem SectionDegreeSum.proof (h : ChowFormSection.Statement) : SectionDegreeSum.Statement := by
  intro F _ _ n e δ I f u hI hf hδ hu
  obtain ⟨c, hc, g, hg, heq⟩ := h F n (e + 1) I f u hI hf hu
  have hδs : IsMultiHomog δ (specFirst f u) := hδ.specFirst u
  rw [heq] at hδs
  have hne : C c * ∏ W ∈ (divCycle I u).support, g W ^ (divCycle I u) W ≠ 0 :=
    mul_ne_zero (C_ne_zero.mpr hc)
      (Finset.prod_ne_zero_iff.mpr fun W hW => pow_ne_zero _ (hg W hW).1)
  obtain ⟨δW, hδW, hsum⟩ :=
    exists_degrees_of_chowFormCycle (Nat.succ_pos e) (divCycle I u) c g hg hδs hne
  exact ⟨g, δW, fun W hW => ⟨isProjPrime_of_mem_support_divCycle hI u hW, hg W hW, hδW W hW⟩,
    hsum.symm⟩

end GroundTheory.Heights₂.Heights
end

