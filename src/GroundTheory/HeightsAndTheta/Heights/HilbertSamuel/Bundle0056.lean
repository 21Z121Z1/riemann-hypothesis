import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0028
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionBounded
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0027
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0038
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0044
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0043

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionSupBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace SectionSupBound

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def chartPiece (c : ∀ k, ι k) : Set ((Σ k, ι k) → ℂ) :=
  Metric.closedBall 0 1 ∩ {w | ∀ k, w ⟨k, c k⟩ = 1}

theorem isCompact_chartPiece (c : ∀ k, ι k) : IsCompact (chartPiece c) := by
  refine (isCompact_closedBall _ _).inter_right ?_
  rw [Set.ofPred_forall]
  exact isClosed_iInter fun k => isClosed_eq (continuous_apply _) continuous_const

theorem exists_lower (A : HermLine ι) (hA : ContinuousOn A.h {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}) (c : ∀ k, ι k) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z : (Σ k, ι k) → ℂ, (∀ k i, ‖z ⟨k, i⟩‖ ≤ ‖z ⟨k, c k⟩‖) →
      (∀ k, z ⟨k, c k⟩ ≠ 0) → ∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k ≤ M * A.h z := by
  have hsub : chartPiece c ⊆ {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := fun w hw k =>
    ⟨c k, by rw [hw.2 k]; exact one_ne_zero⟩
  have hcont : ContinuousOn (fun w => (A.h w)⁻¹) (chartPiece c) :=
    (hA.mono hsub).inv₀ fun w hw => (A.pos w (hsub hw)).ne'
  obtain ⟨M, hM⟩ := (isCompact_chartPiece c).exists_bound_of_continuousOn hcont
  refine ⟨|M|, abs_nonneg M, fun z hmax hz0 => ?_⟩
  have hr : ∀ k, 0 < ‖z ⟨k, c k⟩‖ := fun k => norm_pos_iff.mpr (hz0 k)
  set s : K → ℂ := fun k => (z ⟨k, c k⟩)⁻¹ with hs
  have hs0 : ∀ k, s k ≠ 0 := fun k => inv_ne_zero (hz0 k)
  set w : (Σ k, ι k) → ℂ := fun p => s p.1 * z p with hw
  have hwS : w ∈ chartPiece c := by
    refine ⟨?_, fun k => inv_mul_cancel₀ (hz0 k)⟩
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
    intro p
    obtain ⟨k, i⟩ := p
    show ‖(z ⟨k, c k⟩)⁻¹ * z ⟨k, i⟩‖ ≤ 1
    rw [norm_mul, norm_inv, inv_mul_le_iff₀ (hr k), mul_one]
    exact hmax k i
  have hwpos : 0 < A.h w := A.pos w (hsub hwS)
  have h1 : 1 ≤ |M| * A.h w := by
    have := (hM w hwS).trans (le_abs_self M)
    rw [Real.norm_eq_abs, abs_inv, abs_of_pos hwpos] at this
    rw [inv_le_iff_one_le_mul₀ hwpos] at this
    exact this
  have hAw : A.h w = (∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k)⁻¹ * A.h z := by
    rw [hw, A.smul s z hs0, ← Finset.prod_inv_distrib]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [hs, norm_inv, inv_zpow]
  have hR : 0 < ∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k := Finset.prod_pos fun k _ => zpow_pos (hr k) _
  rw [hAw] at h1
  calc ∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k = (∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k) * 1 := (mul_one _).symm
    _ ≤ (∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k) * (|M| * ((∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k)⁻¹ * A.h z)) :=
        mul_le_mul_of_nonneg_left h1 hR.le
    _ = |M| * A.h z := by field_simp

end SectionSupBound

open SectionBounded SectionSupBound in

theorem SectionSupBound.proof : SectionSupBound.Statement := by
  intro K _ ι _ Ω _ y A τ e hA he
  classical
  choose M hM0 hM using fun c => SectionSupBound.exists_lower A hA c
  choose B hB0 hB using fun c hc => SectionBounded.exists_upper y A.a τ he c hc
  set S : ℝ := ∑ c : (∀ k, ι k), if hc : (∀ k, y ⟨k, c k⟩ ≠ 0) then B c hc * M c ^ τ else 0 with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun c' _ => by
    split_ifs with hc'
    · exact mul_nonneg (hB0 c' hc') (pow_nonneg (hM0 c') τ)
    · exact le_rfl
  refine ⟨Real.log (1 + S), Real.log_nonneg (by linarith), ?_⟩
  rw [Real.exp_log (by linarith)]
  intro dg dh g h z hg hh hdeg hgy hz
  have hmax : ∀ k, ∃ i, ∀ i', ‖z ⟨k, i'⟩‖ ≤ ‖z ⟨k, i⟩‖ := fun k => by
    obtain ⟨i0, _⟩ := hz.1 k
    obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ (fun i => ‖z ⟨k, i⟩‖) ⟨i0, Finset.mem_univ _⟩
    exact ⟨i, fun i' => hi i' (Finset.mem_univ _)⟩
  choose c hcmax using hmax
  have hz0 : ∀ k, z ⟨k, c k⟩ ≠ 0 := fun k h0 => by
    obtain ⟨i0, hi0⟩ := hz.1 k
    have := hcmax k i0
    rw [h0, norm_zero] at this
    exact hi0 (norm_le_zero_iff.mp this)
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k h0 => hz0 k (by
    have := vanish hz (homog_X ⟨k, c k⟩) (by rw [aeval_X]; exact h0)
    simpa using this)
  have h1 := hB c hyc dg dh g h z hg hh hdeg hgy hz hcmax hz0
  have h2 := hM c z hcmax hz0
  have hpow : ∏ k, ‖z ⟨k, c k⟩‖ ^ ((τ : ℤ) * A.a k) = (∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k) ^ τ := by
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [mul_comm, zpow_mul, zpow_natCast]
  have h3 : ∏ k, ‖z ⟨k, c k⟩‖ ^ ((τ : ℤ) * A.a k) ≤ M c ^ τ * A.h z ^ τ := by
    rw [hpow, ← mul_pow]
    exact pow_le_pow_left₀ (Finset.prod_nonneg fun k _ => zpow_nonneg (norm_nonneg _) _) h2 τ
  have hCge : B c hyc * M c ^ τ ≤ 1 + S := by
    have := Finset.single_le_sum (f := fun c : (∀ k, ι k) =>
        if hc : (∀ k, y ⟨k, c k⟩ ≠ 0) then B c hc * M c ^ τ else 0)
      (fun c' _ => by
        split_ifs with hc'
        · exact mul_nonneg (hB0 c' hc') (pow_nonneg (hM0 c') τ)
        · exact le_rfl) (Finset.mem_univ c)
    simp only [dif_pos hyc] at this
    linarith
  have hAh : 0 ≤ A.h z ^ τ := pow_nonneg (A.pos z hz.1).le τ
  calc ‖eval z (map (Int.castRingHom ℂ) g)‖
      ≤ B c hyc * ‖eval z (map (Int.castRingHom ℂ) h)‖ * ∏ k, ‖z ⟨k, c k⟩‖ ^ ((τ : ℤ) * A.a k) := h1
    _ ≤ B c hyc * ‖eval z (map (Int.castRingHom ℂ) h)‖ * (M c ^ τ * A.h z ^ τ) :=
        mul_le_mul_of_nonneg_left h3 (mul_nonneg (hB0 c hyc) (norm_nonneg _))
    _ = (B c hyc * M c ^ τ) * ‖eval z (map (Int.castRingHom ℂ) h)‖ * A.h z ^ τ := by ring
    _ ≤ _ := by gcongr

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSmallGenTwist
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry SectionBoundedMul

noncomputable section

namespace SmallGenTwist

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

def SmallGen (y : (Σ k, ι k) → Ω) (A : HermLine ι) : Prop :=
  ∃ (n : ℕ) (w : Fin n → Ω), (∀ j, w j ∈ chartLat y A.a 1) ∧ KH.GeneratesOn y A.a w ∧
    ∀ j, IsSmallH (mCoordIdeal y) y A 1 (w j)

theorem exists_chart (y : (Σ k, ι k) → Ω) {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) :
    ∃ c : ∀ k, ι k, (∀ k, z ⟨k, c k⟩ ≠ 0) ∧ ∀ k, y ⟨k, c k⟩ ≠ 0 := by
  choose c hc using hz.1
  refine ⟨c, hc, fun k h0 => ?_⟩
  have hX : IsMultiHomog (X ⟨k, c k⟩ : MRing ι) _ :=
    (by have h := isMultiHomog_monomial (ι := ι) (Finsupp.single (⟨k, c k⟩ : Σ k, ι k) 1) 1
        rwa [← X] at h)
  have hmem := mem_mCoordIdeal_of_aeval_eq_zero y hX (by rw [aeval_X, h0])
  have hz0 := hz.2 _ hmem
  simp only [map_X, eval_X] at hz0
  exact hc k hz0

omit [∀ k, Fintype (ι k)] in

theorem mul_mem_chartLat (y : (Σ k, ι k) → Ω) {a b : K → ℤ} {s t : Ω} (hs : s ∈ chartLat y a 1)
    (ht : t ∈ chartLat y b 1) : s * t ∈ chartLat y (a + b) 1 := by
  intro c hc
  have h := mul_mem (hs c hc) (ht c hc)
  convert h using 1
  rw [mul_mul_mul_comm, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← zpow_add₀ (hc k)]
  congr 1
  simp only [Pi.add_apply, Nat.cast_one, one_mul]
  ring

omit [∀ k, Fintype (ι k)] in

theorem generatesOn_mul (y : (Σ k, ι k) → Ω) {a b : K → ℤ} {n m : ℕ} {w : Fin n → Ω} {v : Fin m → Ω}
    (hw : KH.GeneratesOn y a w) (hv : KH.GeneratesOn y b v) :
    KH.GeneratesOn y (a + b)
      (fun j : Fin (n * m) => w (finProdFinEquiv.symm j).1 * v (finProdFinEquiv.symm j).2) := by
  intro c hc
  obtain ⟨u, hu, hsum⟩ := hw c hc
  obtain ⟨u', hu', hsum'⟩ := hv c hc
  refine ⟨fun j => u (finProdFinEquiv.symm j).1 * u' (finProdFinEquiv.symm j).2,
    fun j => mul_mem (hu _) (hu' _), ?_⟩
  set Pa := ∏ k, y ⟨k, c k⟩ ^ (-a k) with hPa
  set Pb := ∏ k, y ⟨k, c k⟩ ^ (-b k) with hPb
  have hP : ∏ k, y ⟨k, c k⟩ ^ (-((a + b) k)) = Pa * Pb := by
    rw [hPa, hPb, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← zpow_add₀ (hc k)]
    congr 1
    simp only [Pi.add_apply]
    ring
  rw [hP, Fintype.sum_equiv finProdFinEquiv.symm _
    (fun p : Fin n × Fin m => u p.1 * u' p.2 * (w p.1 * v p.2 * (Pa * Pb))) (fun _ => rfl),
    Fintype.sum_prod_type]
  calc ∑ i, ∑ l, u i * u' l * (w i * v l * (Pa * Pb))
      = (∑ i, u i * (w i * Pa)) * ∑ l, u' l * (v l * Pb) := by
        rw [Finset.sum_mul_sum]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring
    _ = 1 := by rw [hsum, hsum', one_mul]

theorem isSmallH_mul (y : (Σ k, ι k) → Ω) (A B C : HermLine ι) (hCa : ∀ k, C.a k = A.a k + B.a k)
    (hCh : ∀ z, C.h z = A.h z * B.h z) {s t : Ω} (hs : s ∈ chartLat y A.a 1) (ht : t ∈ chartLat y B.a 1)
    (hbs : IsSmallH (mCoordIdeal y) y A 1 s) (hbt : IsSmallH (mCoordIdeal y) y B 1 t) :
    IsSmallH (mCoordIdeal y) y C 1 (s * t) := by
  intro dg dh g h z hg hh hdeg he hz
  obtain ⟨c, hc, hy⟩ := exists_chart y hz
  obtain ⟨N, dgs, gs, hgs, hdgs, hvs⟩ := exists_chartForm y A.a 1 hs c hy
  obtain ⟨M, dgt, gt, hgt, hdgt, hvt⟩ := exists_chartForm y B.a 1 ht c hy
  have bs := hbs dgs N gs (chartMono c N) z hgs (isMultiHomog_chartMono c N) hdgs hvs hz
  have bt := hbt dgt M gt (chartMono c M) z hgt (isMultiHomog_chartMono c M) hdgt hvt hz

  have hdeq : dgs + dgt + dh = dg + (N + M) := by
    funext k
    have e1 := hdgs k
    have e2 := hdgt k
    have e3 := hdeg k
    have e4 := hCa k
    simp only [Pi.add_apply]
    have : ((dgs k + dgt k + dh k : ℕ) : ℤ) = ((dg k + (N k + M k) : ℕ) : ℤ) := by
      push_cast at e1 e2 e3 ⊢
      linear_combination e1 + e2 - e3 - e4
    exact_mod_cast this
  have hF : IsMultiHomog (gs * gt * h - g * chartMono c (N + M)) (dgs + dgt + dh) := by
    refine isMultiHomog_sub (isMultiHomog_mul (isMultiHomog_mul hgs hgt) hh) ?_
    rw [hdeq]
    exact isMultiHomog_mul hg (isMultiHomog_chartMono c (N + M))
  have hmono : ∀ (w : (Σ k, ι k) → Ω), aeval w (chartMono c (N + M)) =
      aeval w (chartMono c N) * aeval w (chartMono c M) := fun w => by
    rw [aeval_chartMono, aeval_chartMono, aeval_chartMono, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => by rw [Pi.add_apply, pow_add]
  have hF0 : aeval y (gs * gt * h - g * chartMono c (N + M)) = 0 := by
    rw [map_sub, map_mul, map_mul, map_mul, hvs, hvt, he, hmono]
    ring
  have hz0 := hz.2 _ (mem_mCoordIdeal_of_aeval_eq_zero y hF hF0)
  simp only [map_sub, map_mul] at hz0
  rw [sub_eq_zero] at hz0

  set ev : MRing ι → ℂ := fun f => eval z (map (Int.castRingHom ℂ) f) with hev
  have hmz : ev (chartMono c (N + M)) = ev (chartMono c N) * ev (chartMono c M) := by
    simp only [hev, eval_chartMono, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => by rw [Pi.add_apply, pow_add]
  have hpos : 0 < ‖ev (chartMono c N)‖ * ‖ev (chartMono c M)‖ := by
    refine mul_pos (norm_pos_iff.mpr ?_) (norm_pos_iff.mpr ?_) <;>
    · simp only [hev, eval_chartMono]
      exact Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
  have key : ‖ev g‖ * (‖ev (chartMono c N)‖ * ‖ev (chartMono c M)‖) =
      ‖ev gs‖ * ‖ev gt‖ * ‖ev h‖ := by
    rw [← norm_mul, ← hmz, ← norm_mul, ← norm_mul, ← norm_mul]
    exact congrArg norm hz0.symm
  have hprod : ‖ev gs‖ * ‖ev gt‖ ≤
      (‖ev (chartMono c N)‖ * A.h z ^ 1) * (‖ev (chartMono c M)‖ * B.h z ^ 1) :=
    mul_le_mul bs bt (norm_nonneg _) ((norm_nonneg _).trans bs)
  refine le_of_mul_le_mul_right ?_ hpos
  rw [key]
  calc ‖ev gs‖ * ‖ev gt‖ * ‖ev h‖
      ≤ (‖ev (chartMono c N)‖ * A.h z ^ 1) * (‖ev (chartMono c M)‖ * B.h z ^ 1) * ‖ev h‖ :=
        mul_le_mul_of_nonneg_right hprod (norm_nonneg _)
    _ = ‖ev h‖ * C.h z ^ 1 * (‖ev (chartMono c N)‖ * ‖ev (chartMono c M)‖) := by
        rw [hCh]
        ring

theorem smallGen_mul (y : (Σ k, ι k) → Ω) (A B C : HermLine ι) (hCa : C.a = A.a + B.a)
    (hCh : ∀ z, C.h z = A.h z * B.h z) (hA : SmallGen y A) (hB : SmallGen y B) : SmallGen y C := by
  obtain ⟨n, w, hw, hgw, hsw⟩ := hA
  obtain ⟨m, v, hv, hgv, hsv⟩ := hB
  refine ⟨n * m, fun j => w (finProdFinEquiv.symm j).1 * v (finProdFinEquiv.symm j).2,
    fun j => ?_, ?_, fun j => ?_⟩
  · rw [hCa]
    exact mul_mem_chartLat y (hw _) (hv _)
  · rw [hCa]
    exact generatesOn_mul y hgw hgv
  · exact isSmallH_mul y A B C (fun k => by rw [hCa]; rfl) hCh (hw _) (hv _) (hsw _) (hsv _)

theorem smallGen_of_trivial (y : (Σ k, ι k) → Ω) (E : HermLine ι) (hEa : E.a = 0) (hEh : ∀ z, E.h z = 1) :
    SmallGen y E := by
  refine ⟨1, fun _ => 1, fun _ => ?_, ?_, fun _ => ?_⟩
  · intro c hc
    simp [hEa]
  · intro c hc
    refine ⟨fun _ => 1, fun _ => one_mem _, ?_⟩
    simp [hEa]
  · intro dg dh g h z hg hh hdeg he hz
    have hd : dg = dh := funext fun k => by
      have := hdeg k
      rw [hEa] at this
      simp only [Pi.zero_apply, mul_zero, add_zero] at this
      exact_mod_cast this
    subst hd
    have h0 : aeval y (g - h) = 0 := by rw [map_sub, he, one_mul, sub_self]
    have hz0 := hz.2 _ (mem_mCoordIdeal_of_aeval_eq_zero y (isMultiHomog_sub hg hh) h0)
    simp only [map_sub, sub_eq_zero] at hz0
    rw [hz0, hEh, pow_one, mul_one]

omit [∀ k, Fintype (ι k)] in

theorem fsH_a [∀ k, Fintype (ι k)] : (fsH ι).a = fun _ => 1 := by
  funext k
  simp [fsH, HermLine.ofMetrics]

theorem smallGen_fsH (y : (Σ k, ι k) → Ω) : SmallGen y (fsH ι) := by
  classical
  set e := Fintype.equivFin (∀ k, ι k) with he_def
  refine ⟨Fintype.card (∀ k, ι k), fun j => aeval y (chartMono (e.symm j) 1), fun j => ?_, ?_, fun j => ?_⟩
  · intro c hc
    beta_reduce
    rw [aeval_chartMono, ← Finset.prod_mul_distrib]
    refine prod_mem fun k _ => ?_
    have hmem : y ⟨k, (e.symm j) k⟩ / y ⟨k, c k⟩ ∈ chartRingZ y c :=
      Algebra.subset_adjoin ⟨⟨k, (e.symm j) k⟩, rfl⟩
    convert hmem using 1
    simp [fsH_a, div_eq_mul_inv]
  · intro c hc
    refine ⟨fun j => if e.symm j = c then 1 else 0, fun j => by beta_reduce; split_ifs <;> simp, ?_⟩
    rw [Fintype.sum_equiv e.symm _ (fun i => (if i = c then (1 : Ω) else 0) *
      (aeval y (chartMono i 1) * ∏ k, y ⟨k, c k⟩ ^ (-(fsH ι).a k))) (fun _ => rfl)]
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [aeval_chartMono, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun k _ => by simp [fsH_a, hc k]
  · intro dg dh g h z hg hh hdeg he hz
    have hd : dg = 1 + dh := funext fun k => by
      have := hdeg k
      simp only [fsH_a, Nat.cast_one, one_mul] at this
      simp only [Pi.add_apply, Pi.one_apply]
      omega
    have hF : IsMultiHomog (g - chartMono (e.symm j) 1 * h) dg :=
      isMultiHomog_sub hg (by rw [hd]; exact isMultiHomog_mul (isMultiHomog_chartMono _ 1) hh)
    have h0 : aeval y (g - chartMono (e.symm j) 1 * h) = 0 := by
      rw [map_sub, map_mul, he, sub_self]
    have hz0 := hz.2 _ (mem_mCoordIdeal_of_aeval_eq_zero y hF h0)
    simp only [map_sub, map_mul, sub_eq_zero] at hz0
    rw [hz0, norm_mul, eval_chartMono, pow_one, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    simp only [Pi.one_apply, pow_one, norm_prod]
    have hH : (fsH ι).h z = ∏ k, ‖WithLp.toLp 2 (fun i => z ⟨k, i⟩)‖ := by
      simp [fsH, HermLine.ofMetrics, fsMetric]
    rw [hH]
    refine Finset.prod_le_prod (fun k _ => norm_nonneg _) fun k _ => ?_
    have := PiLp.norm_apply_le (WithLp.toLp 2 (fun i => z ⟨k, i⟩)) ((e.symm j) k)
    rwa [PiLp.toLp_apply] at this

theorem smallGen_zcomb (y : (Σ k, ι k) → Ω) (L : HermLine ι) (hL : SmallGen y L) (q p : ℕ) :
    SmallGen y (HermLine.zcomb L (fsH ι) q p) := by
  induction q with
  | zero =>
    induction p with
    | zero =>
      exact smallGen_of_trivial y _ (by funext k; simp [HermLine.zcomb]) (fun z => by simp [HermLine.zcomb])
    | succ p ih =>
      refine smallGen_mul y _ (fsH ι) _ ?_ (fun z => ?_) ih (smallGen_fsH y)
      · funext k
        simp only [HermLine.zcomb, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        push_cast
        ring
      · simp only [HermLine.zcomb, zpow_natCast, pow_succ]
        ring
  | succ q ih =>
    refine smallGen_mul y _ L _ ?_ (fun z => ?_) ih hL
    · funext k
      simp only [HermLine.zcomb, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      push_cast
      ring
    · simp only [HermLine.zcomb, zpow_natCast, pow_succ]
      ring

theorem proof : SmallGenTwist.Statement := by
  intro K _ ι _ Ω _ y L p q hL
  exact smallGen_zcomb y L hL q p

end SmallGenTwist

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSpanStepLocal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace SpanStepLocal

def powMulSub {Ω : Type*} [Field Ω] (R : Subalgebra ℤ Ω) (v : Ω) (hv : v ∈ R) : Subalgebra ℤ Ω where
  carrier := {x | ∃ E : ℕ, x * v ^ E ∈ R}
  mul_mem' := by
    rintro x z ⟨E₁, h₁⟩ ⟨E₂, h₂⟩
    refine ⟨E₁ + E₂, ?_⟩
    have e : x * z * v ^ (E₁ + E₂) = (x * v ^ E₁) * (z * v ^ E₂) := by ring
    rw [e]; exact R.mul_mem h₁ h₂
  add_mem' := by
    rintro x z ⟨E₁, h₁⟩ ⟨E₂, h₂⟩
    refine ⟨E₁ + E₂, ?_⟩
    have e : (x + z) * v ^ (E₁ + E₂) = (x * v ^ E₁) * v ^ E₂ + (z * v ^ E₂) * v ^ E₁ := by ring
    rw [e]; exact R.add_mem (R.mul_mem h₁ (R.pow_mem hv _)) (R.mul_mem h₂ (R.pow_mem hv _))
  algebraMap_mem' r := ⟨0, by rw [pow_zero, mul_one]; exact R.algebraMap_mem r⟩

theorem pow_twist {K : Type*} [Fintype K] {ι : K → Type*} {Ω : Type*} [Field Ω] (y : (Σ k, ι k) → Ω)
    (a : K → ℤ) (c : ∀ k, ι k) (g w : Ω) (n : ℕ) :
    g * w ^ n * ∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k)) = g * (w * ∏ k, y ⟨k, c k⟩ ^ (-a k)) ^ n := by
  rw [mul_pow, ← Finset.prod_pow, mul_assoc]
  congr 3; funext k
  rw [← zpow_natCast, ← zpow_mul]; ring_nf

end SpanStepLocal

open SpanStepLocal in

theorem SpanStepLocal.proof (hR : RelLatticeFinite.Statement) : SpanStepLocal.Statement := by
  intro K _ ι _ Ω _ y a q w hy hw hgen j hj
  classical
  set P := Algebra.adjoin ℤ (Set.range fun i => w i / w j) with hPdef

  set v : (∀ k, ι k) → Fin q → Ω := fun c i => w i * ∏ k, y ⟨k, c k⟩ ^ (-a k) with hvdef
  have hv : ∀ c, (∀ k, y ⟨k, c k⟩ ≠ 0) → ∀ i, v c i ∈ chartRingZ y c := fun c hc i => by
    simpa [hvdef] using hw i c hc
  have hv0 : ∀ c, (∀ k, y ⟨k, c k⟩ ≠ 0) → v c j ≠ 0 := fun c hc =>
    mul_ne_zero hj (Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k))
  have hquot : ∀ c i, w i / w j * v c j = v c i := fun c i => by
    simp only [hvdef]; rw [← mul_assoc, div_mul_cancel₀ _ hj]
  have hrel : ∀ (g : Ω) (c : ∀ k, ι k), (∀ k, y ⟨k, c k⟩ ≠ 0) → (g ∈ Algebra.adjoin P
      (Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩) ↔
      g * ∏ k, y ⟨k, c k⟩ ^ (-(((0 : ℕ) : ℤ) * (fun _ => (0 : ℤ)) k)) ∈ Algebra.adjoin P
      (Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩)) := fun g c _ => by simp

  have incl₁ : ∀ (g : Ω) (n : ℕ), g * w j ^ n ∈ chartLat y a n → g ∈ relChartLat P y (fun _ => 0) 0 := by
    intro g n hg c hc
    rw [← hrel g c hc]
    set S := Algebra.adjoin P (Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩)
    have hRS : ∀ x ∈ chartRingZ y c, x ∈ S := fun x hx =>
      (Algebra.adjoin_le Algebra.subset_adjoin : chartRingZ y c ≤ S.restrictScalars ℤ) hx
    have hPS : ∀ x ∈ P, x ∈ S := fun x hx => S.algebraMap_mem (⟨x, hx⟩ : P)
    obtain ⟨u, hu, hsum⟩ := hgen c hc
    have hinv : (∑ i, u i * (w i / w j)) = (v c j)⁻¹ := by
      refine eq_inv_of_mul_eq_one_left ?_
      rw [Finset.sum_mul, ← hsum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_assoc, hquot]
    have hinvS : (v c j)⁻¹ ∈ S := hinv ▸ S.sum_mem fun i _ =>
      S.mul_mem (hRS _ (hu i)) (hPS _ (Algebra.subset_adjoin ⟨i, rfl⟩))
    have hgv : g * v c j ^ n ∈ S := hRS _ (by rw [← pow_twist]; exact hg c hc)
    have e : g = g * v c j ^ n * (v c j)⁻¹ ^ n := by
      rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ (hv0 c hc), one_pow, mul_one]
    rw [e]; exact S.mul_mem hgv (S.pow_mem hinvS n)
  have incl₂ : ∀ g ∈ relChartLat P y (fun _ => 0) 0, ∃ n : ℕ, g * w j ^ n ∈ chartLat y a n := by
    intro g hg
    have hE : ∀ c, ∃ E : ℕ, (∀ k, y ⟨k, c k⟩ ≠ 0) → g * v c j ^ E ∈ chartRingZ y c := by
      intro c
      by_cases hc : ∀ k, y ⟨k, c k⟩ ≠ 0
      swap; · exact ⟨0, fun h => absurd h hc⟩
      have hgS := (hrel g c hc).2 (hg c hc)
      have hg' : g ∈ Algebra.adjoin ℤ ((Set.range fun i => w i / w j) ∪
          Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩) := by
        rw [Algebra.adjoin_union_eq_adjoin_adjoin]; exact hgS
      have hle : Algebra.adjoin ℤ ((Set.range fun i => w i / w j) ∪
          Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩) ≤ powMulSub _ _ (hv c hc j) := by
        refine Algebra.adjoin_le (Set.union_subset ?_ ?_)
        · rintro _ ⟨i, rfl⟩; exact ⟨1, by rw [pow_one, hquot]; exact hv c hc i⟩
        · rintro _ ⟨p, rfl⟩; exact ⟨0, by rw [pow_zero, mul_one]; exact Algebra.subset_adjoin ⟨p, rfl⟩⟩
      obtain ⟨E, hE⟩ := hle hg'
      exact ⟨E, fun _ => hE⟩
    choose E hE using hE
    refine ⟨∑ c, E c, fun c hc => ?_⟩
    rw [pow_twist]
    have e : g * v c j ^ (∑ c, E c) = g * v c j ^ E c * v c j ^ (∑ c, E c - E c) := by
      rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ c))]
    rw [e]; exact (chartRingZ y c).mul_mem (hE c hc) ((chartRingZ y c).pow_mem (hv c hc j) _)

  obtain ⟨r, b, hb⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (hR K ι Ω y (fun _ => 0) 0 q (fun i => w i / w j) hy)
  have hbmem : ∀ l, b l ∈ relChartLat P y (fun _ => 0) 0 := fun l =>
    hb ▸ Submodule.subset_span ⟨l, rfl⟩
  refine ⟨r, b, fun l => incl₂ _ (hbmem l), fun g n hg => ?_⟩
  have hgN := incl₁ g n hg
  rw [← hb, Submodule.mem_span_range_iff_exists_fun] at hgN
  obtain ⟨c, hc⟩ := hgN
  exact ⟨fun l => (c l : Ω), fun l => (c l).2, by rw [← hc]; rfl⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

