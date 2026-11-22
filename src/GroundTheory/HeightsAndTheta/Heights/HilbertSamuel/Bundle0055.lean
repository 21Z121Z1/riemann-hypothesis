import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0043
import GroundTheory.HeightsAndTheta.Heights.Intersections.PTorusInvLevi
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsAntisym
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0028
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0038
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0044
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0029
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0016

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PScaledFSHProps
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 Filter Topology
open GroundTheory.Heights₂.Heights.LowerBoundFree.FubiniLevi (sqSum)
open GroundTheory.Heights₂.Heights.Inter.TorusInvariantLevi (levi_Phi leviForm_phi_nonneg isOpen_noZeroBlock blk)

namespace ScaledFSHProps

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isSmoothHerm : IsSmoothHerm (scaledFSH ι) :=
  (GroundTheory.Heights₂.Heights.Inter.isSmoothHerm_ofMetrics_fs (ι := ι) 1).mul
    (contDiffOn_const (c := Real.exp (-(-1 : ℝ))))

theorem log_h_eventuallyEq {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    (fun y => Real.log ((scaledFSH ι).h y)) =ᶠ[𝓝 z]
      fun y => (∑ k, Real.log ((fsMetric (ι k)).ρ (fun i => y ⟨k, i⟩))) + 1 := by
  filter_upwards [isOpen_noZeroBlock.mem_nhds hz] with y hy
  have hρ : ∀ k, (fsMetric (ι k)).ρ (fun i => y ⟨k, i⟩) ≠ 0 := fun k => by
    obtain ⟨i, hi⟩ := hy k
    exact ((fsMetric (ι k)).pos _ fun h0 => hi (congrFun h0 i)).ne'
  rw [scaledFSH_h, Real.log_mul (Finset.prod_ne_zero_iff.2 fun k _ => hρ k) (Real.exp_pos 1).ne',
    Real.log_exp, Real.log_prod fun k _ => hρ k]

theorem leviForm_log_h_nonneg {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (w : (Σ k, ι k) → ℂ) :
    0 ≤ leviForm (fun y => Real.log ((scaledFSH ι).h y)) z w := by
  have hd : fderiv ℝ (fun y => Real.log ((scaledFSH ι).h y)) =ᶠ[𝓝 z]
      fderiv ℝ (fun y => ∑ k, Real.log ((fsMetric (ι k)).ρ (fun i => y ⟨k, i⟩))) := by
    filter_upwards [(log_h_eventuallyEq hz).fderiv (𝕜 := ℝ)] with y hy
    rw [hy]
    exact fderiv_add_const (1 : ℝ)
  have hL : leviForm (fun y => Real.log ((scaledFSH ι).h y)) z w =
      leviForm (fun y => ∑ k, Real.log ((fsMetric (ι k)).ρ (fun i => y ⟨k, i⟩))) z w := by
    unfold leviForm
    rw [hd.fderiv_eq]
  rw [hL, levi_Phi hz w]
  refine Finset.sum_nonneg fun k _ => leviForm_phi_nonneg ?_ _
  obtain ⟨i, hi⟩ := hz k
  refine (lt_of_lt_of_le (pow_pos (norm_pos_iff.2 hi) 2) ?_).ne'
  exact Finset.single_le_sum (f := fun j => ‖blk k z j‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)

theorem isSemipositiveRel (P0 P : Ideal (MRing ι)) : IsSemipositiveRel P0 P (scaledFSH ι) :=
  ⟨isSmoothHerm, fun _ hz w _ => leviForm_log_h_nonneg hz.1 w⟩

theorem isConjInvariantH : IsConjInvariantH (scaledFSH ι) := by
  intro z
  rw [scaledFSH_h, scaledFSH_h]
  simp [fsMetric, EuclideanSpace.norm_eq]

theorem norm_le_rho (z : (Σ k, ι k) → ℂ) (k : K) (i : ι k) :
    ‖z ⟨k, i⟩‖ ≤ (fsMetric (ι k)).ρ (fun i => z ⟨k, i⟩) := by
  show ‖z ⟨k, i⟩‖ ≤ ‖WithLp.toLp 2 (fun i => z ⟨k, i⟩)‖
  simpa using PiLp.norm_apply_le (WithLp.toLp 2 (fun i => z ⟨k, i⟩)) i

theorem monomialsBounded (P : Ideal (MRing ι)) : MonomialsBounded P (scaledFSH ι) (fun _ => 1) := by
  intro z _ μ hμ
  rw [scaledFSH_h, norm_prod, Fintype.prod_sigma]
  have hρ : ∀ k, 0 ≤ (fsMetric (ι k)).ρ (fun i => z ⟨k, i⟩) := fun k => norm_nonneg _
  have hblk : ∀ k, ∏ i, ‖z ⟨k, i⟩ ^ μ ⟨k, i⟩‖ ≤ (fsMetric (ι k)).ρ (fun i => z ⟨k, i⟩) := by
    intro k
    calc ∏ i, ‖z ⟨k, i⟩ ^ μ ⟨k, i⟩‖ ≤ ∏ i, (fsMetric (ι k)).ρ (fun i => z ⟨k, i⟩) ^ μ ⟨k, i⟩ := by
          refine Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => ?_
          rw [norm_pow]
          exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_rho z k i) _
      _ = (fsMetric (ι k)).ρ (fun i => z ⟨k, i⟩) := by
          rw [Finset.prod_pow_eq_pow_sum, hμ k]
          exact pow_one _
  calc ∏ k, ∏ i, ‖z ⟨k, i⟩ ^ μ ⟨k, i⟩‖ ≤ ∏ k, (fsMetric (ι k)).ρ (fun i => z ⟨k, i⟩) :=
        Finset.prod_le_prod (fun k _ => Finset.prod_nonneg fun i _ => norm_nonneg _) fun k _ => hblk k
    _ ≤ (∏ k, (fsMetric (ι k)).ρ (fun i => z ⟨k, i⟩)) * Real.exp 1 :=
        le_mul_of_one_le_right (Finset.prod_nonneg fun k _ => hρ k) (Real.one_le_exp zero_le_one)

end ScaledFSHProps

theorem ScaledFSHProps.proof : ScaledFSHProps.Statement := fun _ _ _ _ P P0 =>
  ⟨ScaledFSHProps.isSemipositiveRel P0 P, ScaledFSHProps.isConjInvariantH, ScaledFSHProps.monomialsBounded P⟩

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionProduct
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace SectionProduct

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

omit [Fintype K] in

theorem isMultiHomog_pow {g : MRing ι} {d : K → ℕ} (hg : IsMultiHomog g d) (j : ℕ) :
    IsMultiHomog (g ^ j) (j • d) := by
  induction j with
  | zero =>
    have h := SectionBoundedMul.isMultiHomog_monomial (ι := ι) 0 1
    have h1 : IsMultiHomog (1 : MRing ι) (fun _ => 0) := by simpa using h
    rw [pow_zero, zero_smul]
    exact h1
  | succ j ih =>
    rw [pow_succ, succ_nsmul]
    exact SectionBoundedMul.isMultiHomog_mul ih hg

end SectionProduct

open SectionBoundedMul SectionProduct in

theorem SectionProduct.proof : SectionProduct.Statement := by
  intro K _ ι _ Ω _ y A B C n j τ s t hdeg hmet hs ht
  have hdk : ∀ k, (τ : ℤ) * C.a k = (n : ℤ) * A.a k + (j : ℤ) * B.a k := fun k => by
    have := congrFun hdeg k
    simpa [smul_eq_mul] using this
  refine ⟨?_, ?_⟩
  ·
    intro c hc
    have hs' := hs c hc
    have ht' := ht c hc
    have heq : s * t ^ j * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * C.a k)) =
        (s * ∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * A.a k))) *
          (t * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * B.a k))) ^ j := by
      have hp : ∀ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * C.a k)) =
          y ⟨k, c k⟩ ^ (-((n : ℤ) * A.a k)) * (y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * B.a k))) ^ j := fun k => by
        have h0 := hc k
        rw [← zpow_natCast (y ⟨k, c k⟩ ^ _) j, ← zpow_mul, ← zpow_add₀ h0, hdk k]
        congr 1
        push_cast
        ring
      simp only [hp, Finset.prod_mul_distrib, Finset.prod_pow]
      ring
    rw [heq]
    exact mul_mem hs' (pow_mem ht' j)
  ·
    intro cc cc' hbs hbt dG dH G H z hG hH hdGH hrep hz
    choose c hc using hz.1
    have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := by
      intro k h0
      have hX : IsMultiHomog (X ⟨k, c k⟩ : MRing ι) _ :=
        (by have h := isMultiHomog_monomial (ι := ι) (Finsupp.single (⟨k, c k⟩ : Σ k, ι k) 1) 1
            rwa [← X] at h)
      have hmem := mem_mCoordIdeal_of_aeval_eq_zero y hX (by rw [aeval_X, h0])
      have hz0 := hz.2 _ hmem
      simp only [map_X, eval_X] at hz0
      exact hc k hz0
    obtain ⟨N, dgs, gs, hgs, hdgs, hvs⟩ := exists_chartForm y A.a n hs c hy
    obtain ⟨M, dgt, gt, hgt, hdgt, hvt⟩ := exists_chartForm y B.a 1 ht c hy
    have bs := hbs dgs N gs (chartMono c N) z hgs (isMultiHomog_chartMono c N) hdgs hvs hz
    have bt := hbt dgt M gt (chartMono c M) z hgt (isMultiHomog_chartMono c M) hdgt hvt hz

    have hdeq : dgs + j • dgt + dH = dG + (N + j • M) := by
      funext k
      have e1 := hdgs k
      have e2 := hdgt k
      have e3 := hdGH k
      have e4 := hdk k
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have : ((dgs k + j * dgt k + dH k : ℕ) : ℤ) = ((dG k + (N k + j * M k) : ℕ) : ℤ) := by
        push_cast at e1 e2 e3 ⊢
        linear_combination e1 + (j : ℤ) * e2 - e3 - e4
      exact_mod_cast this
    have hF : IsMultiHomog (gs * gt ^ j * H - G * chartMono c (N + j • M)) (dgs + j • dgt + dH) := by
      refine isMultiHomog_sub (isMultiHomog_mul (isMultiHomog_mul hgs (isMultiHomog_pow hgt j)) hH) ?_
      rw [hdeq]
      exact isMultiHomog_mul hG (isMultiHomog_chartMono c (N + j • M))
    have hmono : ∀ {R : Type} [CommRing R] (w : (Σ k, ι k) → R),
        ∏ k, w ⟨k, c k⟩ ^ (N + j • M) k = (∏ k, w ⟨k, c k⟩ ^ N k) * (∏ k, w ⟨k, c k⟩ ^ M k) ^ j := by
      intro R _ w
      rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun k _ => by
        rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul, pow_add, pow_mul']
    have hF0 : aeval y (gs * gt ^ j * H - G * chartMono c (N + j • M)) = 0 := by
      rw [map_sub, map_mul, map_mul, map_pow, map_mul, hvs, hvt, hrep, aeval_chartMono, aeval_chartMono,
        aeval_chartMono, hmono]
      ring
    have hz0 := hz.2 _ (mem_mCoordIdeal_of_aeval_eq_zero y hF hF0)
    simp only [map_sub, map_mul, map_pow] at hz0
    rw [sub_eq_zero] at hz0

    set ev : MRing ι → ℂ := fun f => eval z (map (Int.castRingHom ℂ) f) with hev
    have hmz : ev (chartMono c (N + j • M)) = ev (chartMono c N) * ev (chartMono c M) ^ j := by
      simp only [hev, eval_chartMono]
      exact hmono z
    have hpos : 0 < ‖ev (chartMono c N)‖ * ‖ev (chartMono c M)‖ ^ j := by
      refine mul_pos (norm_pos_iff.mpr ?_) (pow_pos (norm_pos_iff.mpr ?_) j) <;>
      · simp only [hev, eval_chartMono]
        exact Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
    have key : ‖ev G‖ * (‖ev (chartMono c N)‖ * ‖ev (chartMono c M)‖ ^ j) =
        ‖ev gs‖ * ‖ev gt‖ ^ j * ‖ev H‖ := by
      rw [← norm_pow, ← norm_mul, ← hmz, ← norm_mul, ← norm_pow, ← norm_mul, ← norm_mul]
      exact congrArg norm hz0.symm
    have hprod : ‖ev gs‖ * ‖ev gt‖ ^ j ≤
        (cc * ‖ev (chartMono c N)‖ * A.h z ^ n) * (cc' * ‖ev (chartMono c M)‖ * B.h z ^ 1) ^ j :=
      mul_le_mul bs (pow_le_pow_left₀ (norm_nonneg _) bt j) (pow_nonneg (norm_nonneg _) j)
        ((norm_nonneg _).trans bs)
    rw [hmet z hz]
    refine le_of_mul_le_mul_right ?_ hpos
    rw [key]
    calc ‖ev gs‖ * ‖ev gt‖ ^ j * ‖ev H‖
        ≤ (cc * ‖ev (chartMono c N)‖ * A.h z ^ n) * (cc' * ‖ev (chartMono c M)‖ * B.h z ^ 1) ^ j * ‖ev H‖ :=
          mul_le_mul_of_nonneg_right hprod (norm_nonneg _)
      _ = cc * cc' ^ j * ‖ev H‖ * (A.h z ^ n * B.h z ^ j) *
            (‖ev (chartMono c N)‖ * ‖ev (chartMono c M)‖ ^ j) := by
          ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionRingFinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

theorem SectionRingFinite.proof (hL : SectionLatticeFinite.Statement) (hS : SectionSpanStep.Statement) :
    SectionRingFinite.Statement := by
  intro K _ ι _ Ω _ y a q w hy hw hgen
  classical
  obtain ⟨n₀, hn₀⟩ := hS K ι Ω y a q w hy hw hgen
  choose G hG using fun m : ℕ => hL K ι Ω y a m hy
  set P : Finset (ℕ × Ω) :=
    (Finset.range (n₀ + 1)).biUnion fun m => (G m).image fun g => (m, g) with hP
  have memP : ∀ m g, m ≤ n₀ → g ∈ G m → (m, g) ∈ P := by
    intro m g hm hg
    rw [hP, Finset.mem_biUnion]
    exact ⟨m, Finset.mem_range.2 (Nat.lt_succ_of_le hm), Finset.mem_image.2 ⟨g, hg, rfl⟩⟩
  have ofP : ∀ x ∈ P, x.2 ∈ chartLat y a x.1 := by
    intro x hx
    rw [hP, Finset.mem_biUnion] at hx
    obtain ⟨m, _, hx⟩ := hx
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hx
    rw [← hG m]
    exact AddSubgroup.subset_closure hg
  let f : Fin P.card → ℕ × Ω := fun i => (P.equivFin.symm i).1
  let T : ℕ → Set Ω := fun n =>
    {s | ∃ (i : Fin P.card) (μ : Fin q → ℕ), (f i).1 + ∑ j, μ j = n ∧ s = (f i).2 * ∏ j, w j ^ μ j}
  have base : ∀ n, n ≤ n₀ → chartLat y a n ≤ AddSubgroup.closure (T n) := by
    intro n hn
    rw [← hG n, AddSubgroup.closure_le]
    intro g hg
    apply AddSubgroup.subset_closure
    refine ⟨P.equivFin ⟨(n, g), memP n g hn hg⟩, 0, ?_, ?_⟩ <;> simp [f]
  have step : ∀ n (j : Fin q), ∀ s ∈ AddSubgroup.closure (T n),
      s * w j ∈ AddSubgroup.closure (T (n + 1)) := by
    intro n j s hs
    induction hs using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨i, μ, hdeg, rfl⟩ := hx
      apply AddSubgroup.subset_closure
      refine ⟨i, μ + Pi.single j 1, ?_, ?_⟩
      · simp only [Pi.add_apply, Finset.sum_add_distrib]
        rw [← hdeg, Finset.sum_pi_single']
        simp [add_assoc]
      · have hprod : ∏ k, w k ^ ((μ + Pi.single j 1 : Fin q → ℕ) k) = (∏ k, w k ^ μ k) * w j := by
          simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]
          congr 1
          rw [Fintype.prod_eq_single j]
          · simp
          · intro k hk
            simp [hk]
        rw [hprod, mul_assoc]
    | zero => simp
    | add x z _ _ hx hz => rw [add_mul]; exact add_mem hx hz
    | neg x _ hx => rw [neg_mul]; exact neg_mem hx
  refine ⟨P.card, fun i => (f i).1, fun i => (f i).2, fun i => ofP _ (P.equivFin.symm i).2, ?_⟩
  intro n
  induction n with
  | zero => exact base 0 (Nat.zero_le _)
  | succ n ih =>
    by_cases h : n + 1 ≤ n₀
    · exact base _ h
    · have hn : n₀ ≤ n := by omega
      refine (hn₀ n hn).trans ?_
      rw [AddSubgroup.closure_le]
      rintro t ⟨s, hs, j, rfl⟩
      exact step n j s (ih hs)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionSpanStep
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace SectionSpanStep

variable {K : Type} [Fintype K] {ι : K → Type} {Ω : Type} [Field Ω]

theorem mul_mem {y : (Σ k, ι k) → Ω} {a : K → ℤ} {n j : ℕ} {s t : Ω} (hs : s ∈ chartLat y a n)
    (ht : t ∈ chartLat y a j) : s * t ∈ chartLat y a (n + j) := by
  intro c hc
  have h : ∏ k, y ⟨k, c k⟩ ^ (-(((n + j : ℕ) : ℤ) * a k)) =
      (∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k))) * ∏ k, y ⟨k, c k⟩ ^ (-((j : ℤ) * a k)) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← zpow_add₀ (hc k)]
    congr 1
    push_cast
    ring
  rw [h, show s * t * ((∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k))) * ∏ k, y ⟨k, c k⟩ ^ (-((j : ℤ) * a k))) =
      (s * ∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k))) * (t * ∏ k, y ⟨k, c k⟩ ^ (-((j : ℤ) * a k))) by ring]
  exact MulMemClass.mul_mem (hs c hc) (ht c hc)

theorem prod_pow_mem {y : (Σ k, ι k) → Ω} {a : K → ℤ} {q : ℕ} {w : Fin q → Ω}
    (hw : ∀ j, w j ∈ chartLat y a 1) (ν : Fin q → ℕ) (S : Finset (Fin q)) :
    ∏ j ∈ S, w j ^ ν j ∈ chartLat y a (∑ j ∈ S, ν j) := by
  have hpow : ∀ (j : Fin q) (e : ℕ), w j ^ e ∈ chartLat y a e := by
    intro j e
    induction e with
    | zero => intro c _; simp
    | succ e ih => rw [pow_succ]; exact mul_mem ih (hw j)
  refine Finset.induction_on S ?_ ?_
  · intro c _
    simp
  · intro j S hj ih
    rw [Finset.prod_insert hj, Finset.sum_insert hj]
    exact mul_mem (hpow j (ν j)) ih

end SectionSpanStep

open SectionSpanStep in

theorem SectionSpanStep.proof (hH : SpanStepHomog.Statement) (hS : SerreGraded.Statement) :
    SectionSpanStep.Statement := by
  intro K _ ι _ Ω _ y a q w hy hw hgen
  obtain ⟨m, r, t, ht, hloc⟩ := hH K ι Ω y a q w hy hw hgen
  have hne : ∃ j, w j ≠ 0 := by
    by_contra h
    push Not at h
    choose c hc using hy
    obtain ⟨u, -, hu⟩ := hgen c hc
    simp [h] at hu
  obtain ⟨n₀, hn₀⟩ := hS Ω q r w (fun _ => m) t hne
  refine ⟨max n₀ m, fun n hn s hs => ?_⟩
  have hs' : s ∈ gradedSpan w (fun _ => m) t (n + 1) :=
    hn₀ (n + 1) (by omega) s fun j hj => hloc (n + 1) s hs j hj
  refine (AddSubgroup.closure_le _).2 ?_ hs'
  rintro x ⟨l, μ, hdeg, rfl⟩
  have hdeg : m + ∑ i, μ i = n + 1 := hdeg
  obtain ⟨j, hj⟩ : ∃ j, 0 < μ j := by
    by_contra h
    push Not at h
    have h0 : ∑ i, μ i = 0 := Finset.sum_eq_zero fun i _ => Nat.le_zero.1 (h i)
    omega
  set μ' : Fin q → ℕ := μ - Pi.single j 1 with hμ'
  have hμ : μ = μ' + Pi.single j 1 := by
    funext i
    by_cases hij : i = j
    · subst hij
      simp [hμ']
      omega
    · simp [hμ', hij]
  have hsum : ∑ i, μ i = ∑ i, μ' i + 1 := by
    rw [hμ]
    simp only [Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single']
    simp
  have hprod : ∏ i, w i ^ μ i = (∏ i, w i ^ μ' i) * w j := by
    rw [hμ]
    simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]
    congr 1
    rw [Fintype.prod_eq_single j]
    · simp
    · intro i hi
      simp [hi]
  apply AddSubgroup.subset_closure
  refine ⟨t l * ∏ i, w i ^ μ' i, ?_, j, by rw [hprod, mul_assoc]⟩
  have hmem := mul_mem (ht l) (prod_pow_mem hw μ' Finset.univ)
  have hdeg' : m + ∑ i, μ' i = n := by omega
  rwa [hdeg'] at hmem

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSmallPacking
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

theorem SmallPacking.proof (hR : NmSectionsRankBound.Statement) (hS : SmallSectionsSeparated.Statement) :
    SmallPacking.Statement := by
  classical
  intro K _ ι _ Ω _ y D A La hX hB hA hLa
  obtain ⟨hfin, C₁, hC₁, hrank⟩ := hR K ι Ω y D A.a hX hB
  obtain ⟨C, hC, hsep⟩ := hS K ι Ω y D A hX hB hA
  have key : ∀ (τ : ℕ) (T : Finset (La τ)), (∀ s ∈ T, IsSmallH (mCoordIdeal y) y A τ (s : Ω)) →
      Real.log T.card ≤ C₁ * ((τ : ℝ) + 1) ^ D * (C * ((τ : ℝ) + 1) + Real.log 3) := by
    intro τ T hT
    obtain ⟨Z, ev, hZ, hrep, hsepτ⟩ := hsep τ
    have hpos : ∀ z : Z, 0 < A.h z := fun z => A.pos _ (hZ z z.2).1
    let φ : chartLatNm y A.a τ →+ (Z → ℂ) :=
      { toFun := fun s z => ev s z / ((A.h z : ℂ) ^ τ)
        map_zero' := by funext z; simp
        map_add' := by intro s t; funext z; simp [add_div] }
    have hφ : ∀ s z, ‖φ s z‖ = ‖ev s z‖ / A.h z ^ τ := fun s z => by
      simp [φ, norm_pow, abs_of_pos (hpos z)]
    have hnorm : ∀ s : chartLatNm y A.a τ, IsSmallH (mCoordIdeal y) y A τ (s : Ω) → ‖φ s‖ ≤ 1 := by
      intro s hs
      refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun z => ?_
      obtain ⟨dg, dh, g, h, hg, hh, hdeg, heq, hz0, hev⟩ := hrep s z
      have hle := hs dg dh g h z hg hh hdeg heq (hZ z z.2)
      rw [← hev, norm_mul] at hle
      rw [hφ, div_le_one (pow_pos (hpos z) τ)]
      exact le_of_mul_le_mul_right (by linarith) (norm_pos_iff.2 hz0)
    have hdist : ∀ s t : chartLatNm y A.a τ, IsSmallH (mCoordIdeal y) y A τ (s : Ω) →
        IsSmallH (mCoordIdeal y) y A τ (t : Ω) → s ≠ t →
        Real.exp (-(C * ((τ : ℝ) + 1))) ≤ ‖φ s - φ t‖ := by
      intro s t hs ht hst
      obtain ⟨z, hz⟩ := hsepτ s t hs ht hst
      refine le_trans ?_ (norm_le_pi_norm (φ s - φ t) z)
      rw [← map_sub φ, hφ, map_sub ev, Pi.sub_apply, le_div_iff₀ (pow_pos (hpos z) τ)]
      exact hz
    let ι' : La τ →+ chartLatNm y A.a τ := AddSubgroup.inclusion (hLa τ)
    have := hfin τ
    let L : Submodule ℤ (Z → ℂ) := LinearMap.range φ.toIntLinearMap
    have hsmall : ∀ s ∈ T, IsSmallH (mCoordIdeal y) y A τ ((ι' s : chartLatNm y A.a τ) : Ω) := hT
    have hinj : Set.InjOn (fun s => φ (ι' s)) T := by
      intro s hs t ht hst
      by_contra hne
      have hne' : ι' s ≠ ι' t := fun h => hne (Subtype.ext (by simpa [ι'] using congrArg Subtype.val h))
      have := hdist _ _ (hsmall s hs) (hsmall t ht) hne'
      simp only at hst
      rw [hst, sub_self, norm_zero] at this
      exact absurd this (not_le.2 (Real.exp_pos _))
    have hP := Packing.proof (Z → ℂ) L (T.image fun s => φ (ι' s)) (C * ((τ : ℝ) + 1)) (by positivity)
      (by intro v hv; obtain ⟨s, -, rfl⟩ := Finset.mem_image.1 hv; exact ⟨ι' s, rfl⟩)
      (by intro v hv; obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hv; exact hnorm _ (hsmall s hs))
      (by
        intro v hv w hw hvw
        obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hv
        obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hw
        exact hdist _ _ (hsmall s hs) (hsmall t ht) fun h => hvw (by rw [h]))
    rw [Finset.card_image_of_injOn hinj] at hP
    have hL : (Module.finrank ℤ L : ℝ) ≤ Module.finrank ℤ (chartLatNm y A.a τ) := by
      exact_mod_cast LinearMap.finrank_range_le φ.toIntLinearMap
    refine hP.trans (mul_le_mul_of_nonneg_right (hL.trans (hrank τ)) (by positivity))
  have hfinite : ∀ τ, {s : La τ | IsSmallH (mCoordIdeal y) y A τ (s : Ω)}.Finite := by
    intro τ
    by_contra hinf
    obtain ⟨T, hTsub, hTcard⟩ := Set.Infinite.exists_subset_card_eq hinf
      (⌈Real.exp (C₁ * ((τ : ℝ) + 1) ^ D * (C * ((τ : ℝ) + 1) + Real.log 3))⌉₊ + 1)
    have h1 := key τ T (fun s hs => hTsub hs)
    rw [hTcard, Real.log_le_iff_le_exp (by positivity)] at h1
    push_cast at h1
    linarith [Nat.le_ceil (Real.exp (C₁ * ((τ : ℝ) + 1) ^ D * (C * ((τ : ℝ) + 1) + Real.log 3)))]
  refine ⟨hfinite, C₁ * (C + Real.log 3), fun τ => ?_⟩
  unfold smallSectionCount
  rw [show Nat.card {s : La τ // IsSmallH (mCoordIdeal y) y A τ (s : Ω)} = (hfinite τ).toFinset.card from
    Nat.card_eq_card_finite_toFinset (hfinite τ)]
  refine (key τ _ fun s hs => (hfinite τ).mem_toFinset.1 hs).trans ?_
  have h1 : (1 : ℝ) ≤ (τ : ℝ) + 1 := by linarith [(Nat.cast_nonneg τ : (0 : ℝ) ≤ τ)]
  have hl : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  calc C₁ * ((τ : ℝ) + 1) ^ D * (C * ((τ : ℝ) + 1) + Real.log 3)
      ≤ C₁ * ((τ : ℝ) + 1) ^ D * ((C + Real.log 3) * ((τ : ℝ) + 1)) := by gcongr; nlinarith
    _ = C₁ * (C + Real.log 3) * ((τ : ℝ) + 1) ^ (D + 1) := by ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

