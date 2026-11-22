import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0013
import GroundTheory.HeightsAndTheta.Heights.Intersections.PRFormula
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0019
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0006
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0020
import GroundTheory.HeightsAndTheta.Heights.Intersections.ProjLineRankTwoPushforwardHypotheses

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PDiagPullI
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 DiagRAux

noncomputable section

set_option linter.unusedSectionVars false

namespace DiagonalPullback

theorem pullDeg_add (j : Fin 2) (a b : T.YBlk → ℤ) :
    I1.pullDeg (diagonalBlockIndex j) (a + b) = I1.pullDeg (diagonalBlockIndex j) a + I1.pullDeg (diagonalBlockIndex j) b := by
  funext k
  by_cases h : ∃ k', diagonalBlockIndex j k' = k
  · obtain ⟨k', rfl⟩ := h
    simp only [Pi.add_apply, pullDeg_segreBlockEmbedding]
  · simp only [I1.pullDeg, Pi.add_apply, Function.extend_apply' _ _ _ h, Pi.zero_apply, add_zero]

theorem pullDeg_eq_alt (j : Fin 2) (c : T.YBlk → ℤ) : I1.pullDeg (diagonalBlockIndex j) c = T.pullDeg j c := by
  funext k
  fin_cases j <;> cases k
  · exact pullDeg_segreBlockEmbedding 0 c .base
  · exact pullDeg_segreBlockEmbedding 0 c .det
  · exact pullDeg_segreBlockEmbedding 0 c .line
  · exact pullDeg_otherLine 0 c
  · exact pullDeg_segreBlockEmbedding 1 c .base
  · exact pullDeg_segreBlockEmbedding 1 c .det
  · exact pullDeg_otherLine 1 c
  · exact pullDeg_segreBlockEmbedding 1 c .line

variable {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ]

theorem isPull_fs (j : Fin 2) (c : T.YBlk → ℤ) :
    IsPullHerm (diagonalBlockIndex j) (T.yyEmb (ι := ι) (ν := ν) (κ := κ) j)
      (HermLine.ofMetrics (fun k => fsMetric (T.yyIdx ι ν κ k)) c)
      (HermLine.ofMetrics (fun k => fsMetric (T.wwIdx ι ν κ k)) (I1.pullDeg (diagonalBlockIndex j) c)) := by
  refine ⟨rfl, fun z => ?_⟩
  rw [ofMetrics_fs_h, ofMetrics_fs_h, prod_WBlk, prod_YBlk, pullDeg_eq_alt]
  fin_cases j
  · simp [T.pullDeg, T.yyEmb]
    rfl
  · simp [T.pullDeg, T.yyEmb]
    rfl

theorem X_mem_diag_iff {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E] {Φ : Type} [Field Φ]
    [Algebra Ω Φ] (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (a₀ : Φ)
    (p : Σ k, T.wwIdx ι ν κ k) :
    (X p : MRing (T.wwIdx ι ν κ)) ∈ T.wwIdeal x δ e φ a₀ a₀ ↔ T.wwCoord x δ e φ a₀ a₀ p = 0 := by
  show X p ∈ RingHom.ker _ ↔ _
  rw [RingHom.mem_ker, T.multiConeMap, eval₂Hom_X', mul_eq_zero, C_eq_zero]
  simp [X_ne_zero]

theorem I_pull_eq {D : ℕ} (S : ProjectiveLineBundle D)
    (I : Ideal (MRing S.WIdx) → (n : ℕ) → (Fin n → HermLine S.WIdx) → ℝ) (hF : IsIntersectionFamily I)
    (hΔ : IsArithVar S.Diag (D + 1)) (hDP : T.DiagPullStatement (Φ := S.Φ) S.x S.δ S.e S.φ)
    (L : Fin D → HermLine S.WIdx) (hL : ∀ j, IsSmoothHerm (L j))
    (A : HermLine S.YIdx) (A₀ A₁ : HermLine S.WIdx) (d : T.YBlk → ℕ) (hd : ∀ k, A.a k = d k)
    (hA : IsSmoothHerm A) (hp0 : IsPullHerm (diagonalBlockIndex 0) (T.yyEmb 0) A A₀)
    (hp1 : IsPullHerm (diagonalBlockIndex 1) (T.yyEmb 1) A A₁) :
    I S.Diag (D + 1) (Fin.snoc L A₀) = I S.Diag (D + 1) (Fin.snoc L A₁) := by
  have hprime : S.Diag.IsPrime := hΔ.2.1.1
  have hrel : IsRelevant S.Diag := hΔ.2.1.2.2
  obtain ⟨ib, hib⟩ := hrel .base
  obtain ⟨il, hil⟩ := hrel .det
  obtain ⟨ik, hik⟩ := hrel .line0
  have hik' : (X ⟨T.WBlk.line1, (ik : S.κ)⟩ : MRing S.WIdx) ∉ S.Diag := by
    intro h
    apply hik
    rw [X_mem_diag_iff] at h ⊢
    exact h

  set s : MRing S.YIdx := X ⟨T.YBlk.base, (ib : S.ι)⟩ ^ d .base * X ⟨T.YBlk.det, (il : S.ν)⟩ ^ d .det *
    X ⟨T.YBlk.line, (ik : S.κ)⟩ ^ d .line with hs_def
  have hs : IsMultiHomog s d := by
    have h := exHomog_mul (exHomog_mul (exHomog_pow (exHomog_X (ι := S.YIdx) T.YBlk.base ib) (d .base))
      (exHomog_pow (exHomog_X (ι := S.YIdx) T.YBlk.det il) (d .det)))
      (exHomog_pow (exHomog_X (ι := S.YIdx) T.YBlk.line ik) (d .line))
    convert h using 1
    funext k
    cases k <;> simp
  have hs0 : rename (T.yyEmb 0) s = X ⟨T.WBlk.base, ib⟩ ^ d .base * X ⟨T.WBlk.det, il⟩ ^ d .det *
      X ⟨T.WBlk.line0, ik⟩ ^ d .line := by
    simp only [hs_def, map_mul, map_pow, rename_X]
    rfl
  have hs1 : rename (T.yyEmb 1) s = X ⟨T.WBlk.base, ib⟩ ^ d .base * X ⟨T.WBlk.det, il⟩ ^ d .det *
      X ⟨T.WBlk.line1, (ik : S.κ)⟩ ^ d .line := by
    simp only [hs_def, map_mul, map_pow, rename_X]
    rfl
  have hpow : ∀ {f : MRing S.WIdx} (n : ℕ), f ∉ S.Diag → f ^ n ∉ S.Diag :=
    fun n hf h => hf (hprime.mem_of_pow_mem n h)
  have hmul : ∀ {f g : MRing S.WIdx}, f ∉ S.Diag → g ∉ S.Diag → f * g ∉ S.Diag :=
    fun hf hg h => (hprime.mem_or_mem h).elim hf hg
  have hn0 : rename (T.yyEmb 0) s ∉ S.Diag := by
    rw [hs0]
    exact hmul (hmul (hpow _ hib) (hpow _ hil)) (hpow _ hik)
  have hn1 : rename (T.yyEmb 1) s ∉ S.Diag := by
    rw [hs1]
    exact hmul (hmul (hpow _ hib) (hpow _ hil)) (hpow _ hik')

  set a0 : T.WBlk → ℕ := d .base • Pi.single T.WBlk.base 1 + d .det • Pi.single T.WBlk.det 1 +
    d .line • Pi.single T.WBlk.line0 1 with ha0
  set a1 : T.WBlk → ℕ := d .base • Pi.single T.WBlk.base 1 + d .det • Pi.single T.WBlk.det 1 +
    d .line • Pi.single T.WBlk.line1 1 with ha1
  have hh0 : IsMultiHomog (rename (T.yyEmb 0) s) a0 := by
    rw [hs0]
    exact exHomog_mul (exHomog_mul (exHomog_pow (exHomog_X (ι := S.WIdx) T.WBlk.base ib) _)
      (exHomog_pow (exHomog_X (ι := S.WIdx) T.WBlk.det il) _)) (exHomog_pow (exHomog_X (ι := S.WIdx) T.WBlk.line0 ik) _)
  have hh1 : IsMultiHomog (rename (T.yyEmb 1) s) a1 := by
    rw [hs1]
    exact exHomog_mul (exHomog_mul (exHomog_pow (exHomog_X (ι := S.WIdx) T.WBlk.base ib) _)
      (exHomog_pow (exHomog_X (ι := S.WIdx) T.WBlk.det il) _))
      (exHomog_pow (exHomog_X (ι := S.WIdx) T.WBlk.line1 (ik : S.κ)) _)
  have hT0 : A₀.a = T.pullDeg 0 A.a := by rw [hp0.1, pullDeg_eq_alt]
  have hT1 : A₁.a = T.pullDeg 1 A.a := by rw [hp1.1, pullDeg_eq_alt]
  have hd0 : ∀ k, A₀.a k = a0 k := by
    intro k
    rw [hT0]
    cases k <;> simp [T.pullDeg, ha0, hd]
  have hd1 : ∀ k, A₁.a k = a1 k := by
    intro k
    rw [hT1]
    cases k <;> simp [T.pullDeg, ha1, hd]

  have e0 := hF.2.2 S.Diag D L A₀ _ a0 hΔ hL (isSmoothHerm_pull 0 hA hp0) hd0 hh0 hn0
  have e1 := hF.2.2 S.Diag D L A₁ _ a1 hΔ hL (isSmoothHerm_pull 1 hA hp1) hd1 hh1 hn1
  rw [e0, e1, recR_eq, recR_eq, cycR_eq_finsum, cycR_eq_finsum, (hDP (S.a 0)).1 s d hs]
  congr 1
  exact ptsIntegral_congr_mcPts _ (fun _ _ _ => rfl) fun z hz =>
    (hDP (S.a 0)).2.2 s d hs A A₀ A₁ hd ⟨hT0, hp0.2⟩ ⟨hT1, hp1.2⟩ z hz

end DiagonalPullback

open DiagonalPullback

theorem DiagPullI.proof (hDD : DiagDiv.Statement) (hDP : DiagPull.Statement) : DiagPullI.Statement := by
  intro I hI D S X X₀ X₁ L hX hp0 hp1 hL
  have hF : IsIntersectionFamily (I T.WBlk S.WIdx) := hI T.WBlk S.WIdx
  have hW : IsArithVar S.WW (D + 2) := S.arithWW

  have hgW : S.g ∉ S.WW := by
    have hh : aeval (T.wwCoord S.x S.δ S.e S.φ (S.a 0) (S.a 1)) S.h ≠ 0 :=
      (not_mem_ker_iff_aeval_ne _ S.h _ S.h_deg).1 S.h_nmem
    refine (not_mem_ker_iff_aeval_ne _ S.g _ S.g_deg).2 ?_
    rw [S.quot]
    refine mul_ne_zero ?_ hh
    exact sub_ne_zero.2 (S.indep.injective.ne (by decide))
  have hdiv := (hDD S.Ω S.ι S.ν S.κ S.E S.Φ S.x S.B S.e S.φ S.δ S.dualSec S.dualGen S.detGen S.chart S.a
    S.indep).2 S.n S.g S.h S.g_deg S.h_deg S.h_nmem S.quot
  have hΔhor : IsHorizontal S.Diag := by
    have h := hW.2.2.1
    unfold IsHorizontal at h ⊢
    rw [← h]
    exact comap_C_ker_multiConeMap _ _
  have hΔmem : S.Diag ∈ divSupp S.WW S.g := by
    refine mem_divSupp_of_divCycle_ne_zero fun h0 => ?_
    have := congrArg (fun z => z S.Diag) hdiv
    simp only [Finsupp.coe_sub, Pi.sub_apply, T.toZCycle, Finsupp.mapRange_apply, h0,
      Finsupp.single_eq_same] at this
    omega
  have hΔ : IsArithVar S.Diag (D + 1) :=
    (divSuppArith T.WBlk S.WIdx S.WW (D + 1)
      (HermLine.ofMetrics (fun k => maxMetric ℂ (S.WIdx k)) (fun k => (T.wwDeg S.n 1 k : ℤ))) S.g S.Diag hW
      ⟨T.wwDeg S.n 1, fun _ => rfl, S.g_deg, hgW⟩ hΔmem).1 hΔhor
  have hDP' := hDP S.Ω S.ι S.ν S.κ S.E S.Φ S.x S.e S.φ S.δ

  set b : T.YBlk → ℤ := fun k => ((X.a k).natAbs : ℤ) with hb
  set B : HermLine S.YIdx := HermLine.ofMetrics (fun k => fsMetric (S.YIdx k)) b with hB
  set B₀ : HermLine S.WIdx := HermLine.ofMetrics (fun k => fsMetric (S.WIdx k)) (I1.pullDeg (diagonalBlockIndex 0) b)
    with hB₀
  set B₁ : HermLine S.WIdx := HermLine.ofMetrics (fun k => fsMetric (S.WIdx k)) (I1.pullDeg (diagonalBlockIndex 1) b)
    with hB₁
  have hsB : IsSmoothHerm B := isSmoothHerm_ofMetrics_fs b
  have hpB0 : IsPullHerm (diagonalBlockIndex 0) (T.yyEmb 0) B B₀ := isPull_fs 0 b
  have hpB1 : IsPullHerm (diagonalBlockIndex 1) (T.yyEmb 1) B B₁ := isPull_fs 1 b
  have hsX0 : IsSmoothHerm X₀ := isSmoothHerm_pull 0 hX hp0
  have hsX1 : IsSmoothHerm X₁ := isSmoothHerm_pull 1 hX hp1
  have hsB0 : IsSmoothHerm B₀ := isSmoothHerm_ofMetrics_fs _
  have hsB1 : IsSmoothHerm B₁ := isSmoothHerm_ofMetrics_fs _
  have hpXB : ∀ (j : Fin 2) {Xj Bj : HermLine S.WIdx}, IsPullHerm (diagonalBlockIndex j) (T.yyEmb j) X Xj →
      IsPullHerm (diagonalBlockIndex j) (T.yyEmb j) B Bj → IsPullHerm (diagonalBlockIndex j) (T.yyEmb j) (X.tensor B) (Xj.tensor Bj) := by
    intro j Xj Bj hXj hBj
    refine ⟨?_, fun z => ?_⟩
    · show Xj.a + Bj.a = I1.pullDeg (diagonalBlockIndex j) (X.a + B.a)
      rw [pullDeg_add, hXj.1, hBj.1]
    · show Xj.h z * Bj.h z = X.h _ * B.h _
      rw [hXj.2, hBj.2]
  have c1 := I_pull_eq S (I T.WBlk S.WIdx) hF hΔ hDP' L hL (X.tensor B) (X₀.tensor B₀) (X₁.tensor B₁)
    (fun k => (X.a k + (X.a k).natAbs).toNat)
    (fun k => by
      show X.a k + ((X.a k).natAbs : ℤ) = _
      rw [Int.toNat_of_nonneg (by omega)])
    (isSmoothHerm_tensor hX hsB) (hpXB 0 hp0 hpB0) (hpXB 1 hp1 hpB1)
  have c2 := I_pull_eq S (I T.WBlk S.WIdx) hF hΔ hDP' L hL B B₀ B₁ (fun k => (X.a k).natAbs) (fun _ => rfl)
    hsB hpB0 hpB1
  have a0 := hF.2.1 S.Diag D L X₀ B₀ hΔ hL hsX0 hsB0
  have a1 := hF.2.1 S.Diag D L X₁ B₁ hΔ hL hsX1 hsB1
  linarith

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PLocRingFrac
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace LocRingFrac

set_option linter.unusedSectionVars false

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem isMultiHomog_add {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f + g) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
  · exact hf m h k
  · exact hg m h k

theorem isMultiHomog_neg {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) : IsMultiHomog (-f) a := by
  intro m hm k
  rw [MvPolynomial.support_neg] at hm
  exact hf m hm k

theorem isMultiHomog_zero (a : K → ℕ) : IsMultiHomog (0 : MRing ι) a := by
  intro m hm
  simp at hm

end LocRingFrac

theorem LocRingFrac.proof : LocRingFrac.Statement := by
  intro K _ ι _ P W _ hW _ y hy
  have h1 : (1 : MRing ι) ∉ W := fun h => hW.ne_top ((Ideal.eq_top_iff_one _).mpr h)
  induction hy using Subring.closure_induction with
  | mem x hx =>
    obtain ⟨u, v, a, hv, hvW, hu, hva, rfl⟩ := hx
    exact ⟨u, v, a, hu, hva, hvW, IsLocalization.mk'_spec _ _ _⟩
  | zero => exact ⟨0, 1, 0, isMultiHomog_zero 0, AvoidRing.isMultiHomog_one, h1, by simp⟩
  | one => exact ⟨1, 1, 0, AvoidRing.isMultiHomog_one, AvoidRing.isMultiHomog_one, h1, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨u, v, a, hu, hv, hvW, e⟩ := hx
    obtain ⟨u', v', a', hu', hv', hvW', e'⟩ := hy
    refine ⟨u * v' + u' * v, v * v', a + a',
      isMultiHomog_add (AvoidRing.isMultiHomog_mul hu hv')
        (by rw [add_comm]; exact AvoidRing.isMultiHomog_mul hu' hv),
      AvoidRing.isMultiHomog_mul hv hv', fun h => (hW.mem_or_mem h).elim hvW hvW', ?_⟩
    rw [map_mul, map_add, map_mul, map_mul, map_add, map_mul, map_mul, map_mul, ← e, ← e']
    ring
  | neg x _ hx =>
    obtain ⟨u, v, a, hu, hv, hvW, e⟩ := hx
    exact ⟨-u, v, a, isMultiHomog_neg hu, hv, hvW, by rw [map_neg, map_neg, ← e]; ring⟩
  | mul x y _ _ hx hy =>
    obtain ⟨u, v, a, hu, hv, hvW, e⟩ := hx
    obtain ⟨u', v', a', hu', hv', hvW', e'⟩ := hy
    refine ⟨u * u', v * v', a + a', AvoidRing.isMultiHomog_mul hu hu', AvoidRing.isMultiHomog_mul hv hv',
      fun h => (hW.mem_or_mem h).elim hvW hvW', ?_⟩
    rw [map_mul, map_mul, map_mul, map_mul, ← e, ← e']
    ring

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PLocRingLocal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace LocRingLocal

set_option linter.unusedSectionVars false

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem isMultiHomog_add {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f + g) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
  · exact hf m h k
  · exact hg m h k

end LocRingLocal

theorem LocRingLocal.proof (hF : LocRingFrac.Statement) : LocRingLocal.Statement := by
  intro K _ ι _ P W hP hW hPW
  have := hP
  set F := FractionRing (MRing ι ⧸ P)
  have hnzd : ∀ w : MRing ι, w ∉ W → Ideal.Quotient.mk P w ∈ nonZeroDivisors (MRing ι ⧸ P) := fun w hw =>
    mem_nonZeroDivisors_of_ne_zero fun h => hw (hPW (Ideal.Quotient.eq_zero_iff_mem.mp h))
  have hne : ∀ w : MRing ι, w ∉ W → algebraMap (MRing ι ⧸ P) F (Ideal.Quotient.mk P w) ≠ 0 := fun w hw =>
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (hnzd w hw)
  have key : ∀ (y : locRing P W) (u v : MRing ι) (a : K → ℕ), IsMultiHomog u a → IsMultiHomog v a → v ∉ W →
      (y : F) * algebraMap (MRing ι ⧸ P) F (Ideal.Quotient.mk P v) = algebraMap (MRing ι ⧸ P) F (Ideal.Quotient.mk P u) →
      (IsUnit y ↔ u ∉ W) := by
    intro y u v a hu hv hvW hy
    constructor
    · rintro hunit huW
      obtain ⟨y', hyy'⟩ := hunit.exists_right_inv
      obtain ⟨u', v', a', -, -, hv'W, hy'⟩ := hF K ι P W hP hW hPW y' y'.2
      have h1 : ((y * y' : locRing P W) : F) = 1 := by rw [hyy']; rfl
      have h2 : algebraMap (MRing ι ⧸ P) F (Ideal.Quotient.mk P (v * v')) =
          algebraMap (MRing ι ⧸ P) F (Ideal.Quotient.mk P (u * u')) := by
        rw [map_mul, map_mul, map_mul, map_mul, ← hy, ← hy']
        rw [Subring.coe_mul] at h1
        linear_combination (-(algebraMap (MRing ι ⧸ P) F (Ideal.Quotient.mk P v) *
          algebraMap (MRing ι ⧸ P) F (Ideal.Quotient.mk P v'))) * h1
      have h3 := Ideal.Quotient.eq.mp (IsFractionRing.injective (MRing ι ⧸ P) F h2)
      have h4 : v * v' ∈ W := by
        have := W.add_mem (hPW h3) (W.mul_mem_right u' huW)
        simpa using this
      rcases hW.mem_or_mem h4 with h | h
      · exact hvW h
      · exact hv'W h
    · intro huW
      have hz : IsLocalization.mk' F (Ideal.Quotient.mk P v) (⟨_, hnzd u huW⟩ : nonZeroDivisors (MRing ι ⧸ P)) ∈
          locRing P W := Subring.subset_closure ⟨v, u, a, hnzd u huW, huW, hv, hu, rfl⟩
      refine IsUnit.of_mul_eq_one (a := y) ⟨_, hz⟩ (Subtype.ext ?_)
      have hspec := IsLocalization.mk'_spec F (Ideal.Quotient.mk P v)
        (⟨_, hnzd u huW⟩ : nonZeroDivisors (MRing ι ⧸ P))
      simp only [Subring.coe_mul, Subring.coe_one]
      apply mul_right_cancel₀ (hne u huW)
      rw [one_mul, mul_assoc, hspec, hy]
  refine ⟨?_, key⟩
  refine IsLocalRing.of_nonunits_add fun x y hx hy => ?_
  obtain ⟨u, v, a, hu, hv, hvW, hxe⟩ := hF K ι P W hP hW hPW x x.2
  obtain ⟨u', v', a', hu', hv', hv'W, hye⟩ := hF K ι P W hP hW hPW y y.2
  have huW : u ∈ W := by
    by_contra h
    exact hx ((key x u v a hu hv hvW hxe).mpr h)
  have hu'W : u' ∈ W := by
    by_contra h
    exact hy ((key y u' v' a' hu' hv' hv'W hye).mpr h)
  have hvv' : v * v' ∉ W := fun h => (hW.mem_or_mem h).elim hvW hv'W
  have hsum : ((x + y : locRing P W) : F) * algebraMap (MRing ι ⧸ P) F (Ideal.Quotient.mk P (v * v')) =
      algebraMap (MRing ι ⧸ P) F (Ideal.Quotient.mk P (u * v' + u' * v)) := by
    simp only [Subring.coe_add, map_mul, map_add]
    rw [← hxe, ← hye]
    ring
  have hnum : IsMultiHomog (u * v' + u' * v) (a + a') :=
    LocRingLocal.isMultiHomog_add (AvoidRing.isMultiHomog_mul hu hv')
      (add_comm a' a ▸ AvoidRing.isMultiHomog_mul hu' hv)
  intro hunit
  exact (key (x + y) _ _ (a + a') hnum (AvoidRing.isMultiHomog_mul hv hv') hvv' hsum).mp hunit
    (W.add_mem (W.mul_mem_right v' huW) (W.mul_mem_right v hu'W))

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PLocRingNoeth
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem LocRingNoeth.proof (hF : LocRingFrac.Statement) : LocRingNoeth.Statement := by
  classical
  intro K _ ι _ P W hP hW hPW hrel
  have := hP
  let L := FractionRing (MRing ι ⧸ P)
  let q : MRing ι →+* L := (algebraMap (MRing ι ⧸ P) L).comp (Ideal.Quotient.mk P)
  have hq : ∀ f, f ∉ W → q f ≠ 0 := fun f hf h => hf (hPW (by
    rwa [RingHom.comp_apply, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem] at h))
  have hnz : ∀ v, v ∉ W → Ideal.Quotient.mk P v ∈ nonZeroDivisors (MRing ι ⧸ P) := fun v hv =>
    mem_nonZeroDivisors_of_ne_zero fun h => hv (hPW (Ideal.Quotient.eq_zero_iff_mem.mp h))

  have hfrac : ∀ u v a, IsMultiHomog u a → IsMultiHomog v a → v ∉ W → q u / q v ∈ locRing P W := by
    intro u v a hu hv hvW
    refine Subring.subset_closure ⟨u, v, a, hnz v hvW, hvW, hu, hv, ?_⟩
    rw [IsFractionRing.mk'_eq_div]
    rfl
  choose c hc using hrel

  let g : (Σ k, ι k) → L := fun p => q (X p) / q (X ⟨p.1, c p.1⟩)
  let B : Subring L := Subring.closure (Set.range g)
  have hBN : IsNoetherianRing B := is_noetherian_subring_closure _ (Set.finite_range g)
  have hBS : B ≤ locRing P W := Subring.closure_le.mpr (by
    rintro _ ⟨p, rfl⟩
    exact hfrac _ _ _ (AvoidRing.isMultiHomog_X p.1 p.2) (AvoidRing.isMultiHomog_X p.1 (c p.1)) (hc p.1))
  let θ : MRing ι →+* L := eval₂Hom (Int.castRingHom L) g
  have hθB : ∀ f, θ f ∈ B := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C r => rw [eval₂Hom_C, eq_intCast]; exact intCast_mem _ r
    | add f₁ f₂ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
    | mul_X f p hf => rw [map_mul, eval₂Hom_X']; exact mul_mem hf (Subring.subset_closure ⟨p, rfl⟩)

  have hkey : ∀ u a, IsMultiHomog u a → q u = θ u * q (∏ k, X ⟨k, c k⟩ ^ a k) := by
    intro u a hu
    conv_lhs => rw [u.as_sum]
    conv_rhs => rw [u.as_sum]
    rw [map_sum, map_sum, Finset.sum_mul, map_prod]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hT : ∏ k, q (X ⟨k, c k⟩ ^ a k) = ∏ p : Σ k, ι k, q (X ⟨p.1, c p.1⟩) ^ m p := by
      rw [Fintype.prod_sigma]
      refine Finset.prod_congr rfl fun k _ => ?_
      show q (X ⟨k, c k⟩ ^ a k) = ∏ y, q (X ⟨k, c k⟩) ^ m ⟨k, y⟩
      rw [map_pow, Finset.prod_pow_eq_pow_sum, hu m hm k]
    have hθm : θ (monomial m (coeff m u)) = ((coeff m u : ℤ) : L) * ∏ p, g p ^ m p := by
      rw [show θ _ = eval₂ (Int.castRingHom L) g _ from rfl, eval₂_monomial, eq_intCast,
        Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    have hqm : q (monomial m (coeff m u)) = ((coeff m u : ℤ) : L) * ∏ p, q (X p) ^ m p := by
      rw [monomial_eq, map_mul, map_finsuppProd, Finsupp.prod_fintype _ _ (fun _ => by simp)]
      simp only [map_pow]
      congr 1
      exact eq_intCast (q.comp C) _
    rw [hT, hθm, hqm, mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [← mul_pow]
    congr 1
    exact (div_mul_cancel₀ _ (hq _ (hc p.1))).symm

  let _ : Algebra B (locRing P W) := (Subring.inclusion hBS).toAlgebra
  let M : Submonoid B := (IsUnit.submonoid (locRing P W)).comap (Subring.inclusion hBS)
  have hLoc : IsLocalization M (locRing P W) := by
    rw [isLocalization_iff]
    refine ⟨fun y => y.2, fun z => ?_, fun {b₁ b₂} h => ⟨1, ?_⟩⟩
    · obtain ⟨u, v, a, hu, hv, hvW, hzv⟩ := hF K ι P W hP hW hPW z z.2
      have hTW := AvoidRing.coordProd_not_mem hW c hc a
      have hu' := hkey u a hu
      have hv' := hkey v a hv
      have hinv := hfrac _ v a (AvoidRing.isMultiHomog_coordProd c a) hv hvW
      have hunit : IsUnit (Subring.inclusion hBS ⟨θ v, hθB v⟩) :=
        IsUnit.of_mul_eq_one ⟨_, hinv⟩ (Subtype.ext (by
          show θ v * (q _ / q v) = 1
          rw [mul_div_assoc', ← hv', div_self (hq v hvW)]))
      refine ⟨(⟨θ u, hθB u⟩, ⟨⟨θ v, hθB v⟩, hunit⟩), Subtype.ext ?_⟩
      show (z : L) * θ v = θ u
      apply mul_right_cancel₀ (hq _ hTW)
      rw [mul_assoc, ← hv', ← hu']
      exact hzv
    · rw [Subring.inclusion_injective hBS h]
  exact IsLocalization.isNoetherianRing M (locRing P W) hBN

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StFlagMinorsTrdeg
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial

def FlagMinorsTrdeg.Statement : Prop :=
  ∀ (F : Type) [Field F] (n : ℕ),
    Algebra.trdeg F (Algebra.adjoin F (Set.range fun q : Σ j, PluckerBlocks n n j => flagMinor (genMat F n) q.1 q.2)) =
      ((flagDim n + (n - 1) : ℕ) : Cardinal)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end
end

