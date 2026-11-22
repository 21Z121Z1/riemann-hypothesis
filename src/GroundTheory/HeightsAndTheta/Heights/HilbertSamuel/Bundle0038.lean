import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0028
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.SectionModuleEqSpanPow
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0006
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0025
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0009

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionBoundedMul
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace SectionBoundedMul

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

omit [Fintype K] in

theorem isMultiHomog_mul {g h : MRing ι} {a b : K → ℕ} (hg : IsMultiHomog g a)
    (hh : IsMultiHomog h b) : IsMultiHomog (g * h) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m₁, hm₁, m₂, hm₂, rfl⟩ := Finset.mem_add.mp (support_mul g h hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply]
  rw [hg m₁ hm₁ k, hh m₂ hm₂ k]

omit [Fintype K] in

theorem isMultiHomog_sub {g h : MRing ι} {d : K → ℕ} (hg : IsMultiHomog g d)
    (hh : IsMultiHomog h d) : IsMultiHomog (g - h) d := by
  classical
  intro m hm
  rcases Finset.mem_union.mp (support_sub _ g h hm) with hm | hm
  · exact hg m hm
  · exact hh m hm

omit [Fintype K] in

theorem isMultiHomog_monomial (e : (Σ k, ι k) →₀ ℕ) (r : ℤ) :
    IsMultiHomog (monomial e r : MRing ι) (fun k => ∑ i, e ⟨k, i⟩) := by
  classical
  intro m hm k
  rw [Finset.mem_singleton.mp (support_monomial_subset hm)]

omit [Fintype K] in
open Classical in

theorem sum_single_apply (k' : K) (j : ι k') (b : ℕ) (k : K) :
    ∑ i, (Finsupp.single (⟨k', j⟩ : Σ k, ι k) b) ⟨k, i⟩ = if k' = k then b else 0 := by
  classical
  by_cases h : k' = k
  · subst h
    simp [Finsupp.single_apply]
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Finsupp.single_apply, if_neg]
    intro he
    exact h (Sigma.mk.inj_iff.mp he).1

def chartMono (c : ∀ k, ι k) (d : K → ℕ) : MRing ι :=
  ∏ k, X ⟨k, c k⟩ ^ d k

theorem isMultiHomog_chartMono (c : ∀ k, ι k) (d : K → ℕ) : IsMultiHomog (chartMono c d) d := by
  classical
  have h : chartMono c d = monomial (∑ k, Finsupp.single (⟨k, c k⟩ : Σ k, ι k) (d k)) (1 : ℤ) := by
    rw [chartMono, monomial_sum_one]
    exact Finset.prod_congr rfl fun k _ => X_pow_eq_monomial
  have hd : (fun k => ∑ i, (∑ k', Finsupp.single (⟨k', c k'⟩ : Σ k, ι k) (d k')) ⟨k, i⟩) = d := by
    funext k
    simp only [Finsupp.finsetSum_apply]
    rw [Finset.sum_comm]
    simp only [sum_single_apply, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [h]
  have hm := isMultiHomog_monomial (ι := ι) (∑ k, Finsupp.single (⟨k, c k⟩ : Σ k, ι k) (d k)) (1 : ℤ)
  rw [hd] at hm
  exact hm

omit [∀ k, Fintype (ι k)] in

theorem aeval_chartMono (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (d : K → ℕ) :
    aeval y (chartMono c d) = ∏ k, y ⟨k, c k⟩ ^ d k := by
  simp [chartMono, map_prod]

omit [∀ k, Fintype (ι k)] in

theorem eval_chartMono (z : (Σ k, ι k) → ℂ) (c : ∀ k, ι k) (d : K → ℕ) :
    eval z (map (Int.castRingHom ℂ) (chartMono c d)) = ∏ k, z ⟨k, c k⟩ ^ d k := by
  simp [chartMono, map_prod]

theorem mem_mCoordIdeal_of_aeval_eq_zero (y : (Σ k, ι k) → Ω) {g : MRing ι} {d : K → ℕ}
    (hg : IsMultiHomog g d) (h0 : aeval y g = 0) : g ∈ mCoordIdeal y := by
  show g ∈ RingHom.ker (mConeMap y)
  rw [RingHom.mem_ker, ProjLine.mConeMap_eq_of_isMultiHomog y hg, h0, map_zero, zero_mul]

theorem exists_form_of_mem_chartRingZ (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {x : Ω}
    (hx : x ∈ chartRingZ y c) :
    ∃ (δ : K → ℕ) (e : MRing ι), IsMultiHomog e δ ∧ aeval y e = x * ∏ k, y ⟨k, c k⟩ ^ δ k := by
  classical
  have hpow : ∀ δ₁ δ₂ : K → ℕ, ∏ k, y ⟨k, c k⟩ ^ (δ₁ + δ₂) k =
      (∏ k, y ⟨k, c k⟩ ^ δ₁ k) * ∏ k, y ⟨k, c k⟩ ^ δ₂ k := fun δ₁ δ₂ => by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => by rw [Pi.add_apply, pow_add]
  rw [chartRingZ] at hx
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    obtain ⟨k₀, j⟩ := p
    refine ⟨fun k => ∑ i, (Finsupp.single (⟨k₀, j⟩ : Σ k, ι k) 1) ⟨k, i⟩, X ⟨k₀, j⟩, ?_, ?_⟩
    · have h := isMultiHomog_monomial (ι := ι) (Finsupp.single (⟨k₀, j⟩ : Σ k, ι k) 1) 1
      rwa [← X] at h
    · have h1 : ∏ k, y ⟨k, c k⟩ ^ (∑ i, (Finsupp.single (⟨k₀, j⟩ : Σ k, ι k) 1) ⟨k, i⟩) = y ⟨k₀, c k₀⟩ := by
        simp only [sum_single_apply]
        rw [Finset.prod_eq_single k₀ (fun k _ hk => by rw [if_neg (Ne.symm hk), pow_zero])
          (fun h => absurd (Finset.mem_univ _) h)]
        simp
      rw [aeval_X, h1, div_mul_cancel₀ _ (hc k₀)]
  | algebraMap r =>
    refine ⟨fun _ => 0, C r, ?_, by simp⟩
    have h := isMultiHomog_monomial (ι := ι) 0 r
    simpa using h
  | add x w _ _ hx hw =>
    obtain ⟨δ₁, e₁, h₁, v₁⟩ := hx
    obtain ⟨δ₂, e₂, h₂, v₂⟩ := hw
    refine ⟨δ₁ + δ₂, e₁ * chartMono c δ₂ + e₂ * chartMono c δ₁, ?_, ?_⟩
    · intro m hm
      rcases Finset.mem_union.mp (support_add hm) with hm | hm
      · exact isMultiHomog_mul h₁ (isMultiHomog_chartMono c δ₂) m hm
      · rw [add_comm δ₁]
        exact isMultiHomog_mul h₂ (isMultiHomog_chartMono c δ₁) m hm
    · rw [map_add, map_mul, map_mul, v₁, v₂, aeval_chartMono, aeval_chartMono, hpow]
      ring
  | mul x w _ _ hx hw =>
    obtain ⟨δ₁, e₁, h₁, v₁⟩ := hx
    obtain ⟨δ₂, e₂, h₂, v₂⟩ := hw
    refine ⟨δ₁ + δ₂, e₁ * e₂, isMultiHomog_mul h₁ h₂, ?_⟩
    rw [map_mul, v₁, v₂, hpow]
    ring

theorem exists_chartForm (y : (Σ k, ι k) → Ω) (a : K → ℤ) (n : ℕ) {s : Ω} (hs : s ∈ chartLat y a n)
    (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    ∃ (N dg : K → ℕ) (g : MRing ι), IsMultiHomog g dg ∧ (∀ k, (dg k : ℤ) = N k + n * a k) ∧
      aeval y g = s * aeval y (chartMono c N) := by
  have hx : s * ∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k)) ∈ chartRingZ y c := hs c hc
  obtain ⟨δ, e, he, hv⟩ := exists_form_of_mem_chartRingZ y c hc hx
  set ex : K → ℕ := fun k => ((n : ℤ) * a k + ((n : ℤ) * a k).natAbs).toNat with hex
  have hexk : ∀ k, (ex k : ℤ) = (n : ℤ) * a k + ((n : ℤ) * a k).natAbs := fun k => by
    rw [hex]
    exact Int.toNat_of_nonneg (by omega)
  refine ⟨fun k => δ k + ((n : ℤ) * a k).natAbs, δ + ex, e * chartMono c ex,
    isMultiHomog_mul he (isMultiHomog_chartMono c ex), fun k => ?_, ?_⟩
  · simp only [Pi.add_apply, Nat.cast_add, hexk k]
    ring
  · rw [map_mul, hv, aeval_chartMono, aeval_chartMono, mul_assoc, mul_assoc, ← Finset.prod_mul_distrib,
      ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    have h0 := hc k
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ h0, ← zpow_add₀ h0, hexk k]
    congr 1
    push_cast
    ring

end SectionBoundedMul

open SectionBoundedMul in

theorem SectionBoundedMul.proof : SectionBoundedMul.Statement := by
  intro K _ ι _ Ω _ y A n m C C' s t hs ht hbs hbt dg dh g h z hg hh hdeg he hz
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
  obtain ⟨M, dgt, gt, hgt, hdgt, hvt⟩ := exists_chartForm y A.a m ht c hy
  have bs := hbs dgs N gs (chartMono c N) z hgs (isMultiHomog_chartMono c N) hdgs hvs hz
  have bt := hbt dgt M gt (chartMono c M) z hgt (isMultiHomog_chartMono c M) hdgt hvt hz

  have hdeq : dgs + dgt + dh = dg + (N + M) := by
    funext k
    have e1 := hdgs k
    have e2 := hdgt k
    have e3 := hdeg k
    simp only [Pi.add_apply]
    have : ((dgs k + dgt k + dh k : ℕ) : ℤ) = ((dg k + (N k + M k) : ℕ) : ℤ) := by
      push_cast at e3 ⊢
      linear_combination e1 + e2 - e3
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
      (C * ‖ev (chartMono c N)‖ * A.h z ^ n) * (C' * ‖ev (chartMono c M)‖ * A.h z ^ m) :=
    mul_le_mul bs bt (norm_nonneg _) ((norm_nonneg _).trans bs)
  refine le_of_mul_le_mul_right ?_ hpos
  rw [key]
  calc ‖ev gs‖ * ‖ev gt‖ * ‖ev h‖
      ≤ (C * ‖ev (chartMono c N)‖ * A.h z ^ n) * (C' * ‖ev (chartMono c M)‖ * A.h z ^ m) * ‖ev h‖ :=
        mul_le_mul_of_nonneg_right hprod (norm_nonneg _)
    _ = C * C' * ‖ev h‖ * A.h z ^ (n + m) * (‖ev (chartMono c N)‖ * ‖ev (chartMono c M)‖) := by
        rw [pow_add]
        ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionsRank
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open scoped Pointwise

noncomputable section

namespace SectionsRank

theorem sec_eq_span (o : Type*) [CommRing o] {Ω : Type*} [CommRing Ω] [Algebra o Ω] {ι : Type*}
    (x : ι → Ω) (n : ℕ) : sec o x n = Submodule.span o (Set.range x ^ n) := by
  unfold sec
  rw [← MvPolynomial.homogeneousSubmodule_one_pow, Submodule.map_pow,
    MvPolynomial.homogeneousSubmodule_one_eq_span_X, Submodule.map_span, ← Set.range_comp,
    Submodule.span_pow]
  congr 3
  ext i
  simp

theorem exists_int_multiple {ι : Type*} (f : MvPolynomial ι ℚ) :
    ∃ N : ℕ, 0 < N ∧ ∃ p : MvPolynomial ι ℤ, map (Int.castRingHom ℚ) p = (N : ℚ) • f := by
  induction f using MvPolynomial.induction_on with
  | C q =>
    refine ⟨q.den, q.pos, C q.num, ?_⟩
    rw [map_C, smul_eq_C_mul, ← C_mul, Rat.den_mul_eq_num]
    rfl
  | add f g hf hg =>
    obtain ⟨a, ha, p, hp⟩ := hf
    obtain ⟨b, hb, r, hr⟩ := hg
    refine ⟨a * b, Nat.mul_pos ha hb, (b : ℤ) • p + (a : ℤ) • r, ?_⟩
    rw [map_add, smul_eq_C_mul, smul_eq_C_mul, map_mul, map_mul, hp, hr, map_C, map_C]
    simp only [smul_eq_C_mul, eq_intCast, Int.cast_natCast, Nat.cast_mul, map_mul]
    ring
  | mul_X f i hf =>
    obtain ⟨a, ha, p, hp⟩ := hf
    refine ⟨a, ha, p * X i, ?_⟩
    rw [map_mul, hp, map_X, smul_mul_assoc]

variable {Ω : Type} [Field Ω] [CharZero Ω] {J : Type}

theorem mem_map_coordIdeal_iff [Fintype J] (x : J → Ω) {n : ℕ} {f : MvPolynomial J ℚ}
    (hf : f.IsHomogeneous n) :
    f ∈ (coordIdeal ℤ x).map (MvPolynomial.map (Int.castRingHom ℚ)) ↔ aeval x f = 0 := by
  constructor
  · intro h
    have hle : (coordIdeal ℤ x).map (MvPolynomial.map (Int.castRingHom ℚ)) ≤
        RingHom.ker (aeval x : MvPolynomial J ℚ →ₐ[ℚ] Ω) := by
      rw [Ideal.map_le_iff_le_comap]
      intro p hp
      rw [Ideal.mem_comap, RingHom.mem_ker, ← algebraMap_int_eq]
      change aeval x (MvPolynomial.map (algebraMap ℤ ℚ) p) = 0
      rw [aeval_map_algebraMap]
      exact aeval_eq_zero_of_mem_coordIdeal hp
    exact hle h
  · intro h
    obtain ⟨N, hN, p, hp⟩ := exists_int_multiple f
    have hpn : p.IsHomogeneous n := by
      refine IsHomogeneous.of_map (f := Int.castRingHom ℚ) (RingHom.injective_int _) ?_
      rw [hp]
      exact (mem_homogeneousSubmodule n _).mp
        (Submodule.smul_mem _ _ ((mem_homogeneousSubmodule n f).mpr hf))
    have hp0 : aeval x p = 0 := by
      rw [← aeval_map_algebraMap ℚ, algebraMap_int_eq, hp, map_smul, h, smul_zero]
    have hmem := Ideal.mem_map_of_mem (MvPolynomial.map (Int.castRingHom ℚ))
      (mem_coordIdeal_of_isHomogeneous ℤ x hpn hp0)
    rw [hp, smul_eq_C_mul] at hmem
    have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
    have := Ideal.mul_mem_left _ (C (N : ℚ)⁻¹) hmem
    rwa [← mul_assoc, ← C_mul, inv_mul_cancel₀ hN', C_1, one_mul] at this

theorem finrank_map_eq {K M N N' : Type*} [Field K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] [AddCommGroup N'] [Module K N'] (V : Submodule K M)
    (f : M →ₗ[K] N) (g : M →ₗ[K] N') (h : ∀ v ∈ V, f v = 0 ↔ g v = 0) :
    Module.finrank K (V.map f) = Module.finrank K (V.map g) := by
  have ef : V.map f = LinearMap.range (f ∘ₗ V.subtype) := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have eg : V.map g = LinearMap.range (g ∘ₗ V.subtype) := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hk : LinearMap.ker (f ∘ₗ V.subtype) = LinearMap.ker (g ∘ₗ V.subtype) := by
    ext v
    simpa using h v v.2
  rw [ef, eg]
  exact ((f ∘ₗ V.subtype).quotKerEquivRange.symm.trans
    ((Submodule.quotEquivOfEq _ _ hk).trans (g ∘ₗ V.subtype).quotKerEquivRange)).finrank_eq

theorem finrank_sec_int [Fintype J] (x : J → Ω) (n : ℕ) :
    Module.finrank ℤ (sec ℤ x n) = Module.finrank ℚ (sec ℚ x n) := by
  have : Module.Finite ℤ (sec ℤ x n) := Module.Finite.iff_fg.mpr (sec_fg x n)
  let b := Module.Free.chooseBasis ℤ (sec ℤ x n)
  let v : Module.Free.ChooseBasisIndex ℤ (sec ℤ x n) → Ω := fun i => (b i : Ω)
  have hli : LinearIndependent ℤ v :=
    b.linearIndependent.map' (sec ℤ x n).subtype (Submodule.ker_subtype _)
  have hliQ : LinearIndependent ℚ v := (LinearIndependent.iff_fractionRing ℤ ℚ).mp hli
  have hspanZ : Submodule.span ℤ (Set.range v) = sec ℤ x n := by
    have : Set.range v = (sec ℤ x n).subtype '' Set.range b := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]
  have hspanQ : Submodule.span ℚ (Set.range v) = sec ℚ x n := by
    rw [← Submodule.span_span_of_tower ℤ, hspanZ, sec_eq_span ℤ, sec_eq_span ℚ,
      Submodule.span_span_of_tower]
  rw [Module.finrank_eq_card_chooseBasisIndex, ← hspanQ, finrank_span_eq_card hliQ]

end SectionsRank

open SectionsRank in

theorem SectionsRank.proof : SectionsRank.Statement := by
  intro Ω _ _ κ _ x n
  set q := (coordIdeal ℤ x).map (MvPolynomial.map (Int.castRingHom ℚ))
  have hw : GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight (GlobalTheory κ) = fun _ _ => 1 := by
    funext v u
    simp [GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight]
  have hV : weightedHomogeneousSubmodule ℚ (GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight (GlobalTheory κ))
      (fun _ => n) = homogeneousSubmodule (Ix κ) ℚ n := by
    ext f
    rw [mem_weightedHomogeneousSubmodule, mem_homogeneousSubmodule, hw]
    have hwt : ∀ d : Ix κ →₀ ℕ,
        Finsupp.weight (fun _ _ => (1 : ℕ) : Ix κ → Unit → ℕ) d = fun _ => Finsupp.weight 1 d := by
      intro d
      funext u
      simp [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
    simp only [IsHomogeneous, IsWeightedHomogeneous, hwt, funext_iff, forall_const]
  have hg : ∀ m : Unit → ℕ, m = (fun _ => n) →
      GroundTheory.Heights₂.Heights.NumbersDVR.gradedPiece q m =
        (homogeneousSubmodule (Ix κ) ℚ n).map (Ideal.Quotient.mkₐ ℚ q).toLinearMap := by
    rintro m rfl
    unfold GroundTheory.Heights₂.Heights.NumbersDVR.gradedPiece
    rw [hV]
  unfold GroundTheory.Heights₂.Heights.NumbersDVR.hilbFn
  rw [if_pos (fun _ => Int.natCast_nonneg n), hg _ (by funext; simp), finrank_sec_int]
  congr 1
  refine finrank_map_eq _ _ _ fun f hf => ?_
  rw [AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem,
    AlgHom.toLinearMap_apply]
  exact mem_map_coordIdeal_iff x ((mem_homogeneousSubmodule n f).mp hf)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSlopeLowerBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

namespace SlopeLowerBound

theorem succ_rpow_isLittleO (D : ℕ) (hD : 1 ≤ D) :
    (fun n : ℕ => ((n : ℝ) + 1) ^ ((D : ℝ) - 1)) =o[atTop] fun n : ℕ => (n : ℝ) ^ D := by
  have hcast : (D : ℝ) - 1 = ((D - 1 : ℕ) : ℝ) := by rw [Nat.cast_sub hD, Nat.cast_one]
  have h1 : (fun n : ℕ => ((n : ℝ) + 1) ^ ((D : ℝ) - 1)) = fun n : ℕ => ((n : ℝ) + 1) ^ (D - 1) := by
    funext n; rw [hcast, Real.rpow_natCast]
  rw [h1]
  have hO : (fun n : ℕ => ((n : ℝ) + 1) ^ (D - 1)) =O[atTop] fun n : ℕ => (n : ℝ) ^ (D - 1) := by
    refine IsBigO.of_bound (2 ^ (D - 1)) ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity),
      ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith) _
  exact hO.trans_isLittleO ((isLittleO_pow_pow_atTop_of_lt (𝕜 := ℝ) (show D - 1 < D by omega)).comp_tendsto
    tendsto_natCast_atTop_atTop)

theorem proof (hHSM : TheoremHSM.Statement) (hRank : RankOfSections.Statement)
    (hGen : GenericFibre.Statement) (hRk : SectionsRank.Statement) (hPos : DegreePositive.Statement) :
    SlopeLowerBound.Statement := by
  intro D Ω _ _ κ _ I d hI ε hε
  obtain ⟨hqP, hqd⟩ := hGen Ω κ d.x D d.arith
  obtain ⟨C, hC⟩ := hRank κ ((coordIdeal ℤ d.x).map (MvPolynomial.map (Int.castRingHom ℚ))) D hqP hqd
  have hδ0 := hPos ℚ κ ((coordIdeal ℤ d.x).map (MvPolynomial.map (Int.castRingHom ℚ))) D hqP hqd
  have hg : genDeg (ι := GlobalTheory κ) (coordIdeal ℤ d.x) D 1 =
      GroundTheory.Heights₂.Heights.NumbersDVR.intNum ℚ ((coordIdeal ℤ d.x).map (MvPolynomial.map (Int.castRingHom ℚ)))
        (fun _ : Fin D => fun _ => (1 : ℤ)) := by
    unfold genDeg
    convert rfl
    simp
  have hδ : (0 : ℝ) < (genDeg (ι := GlobalTheory κ) (coordIdeal ℤ d.x) D 1 : ℝ) := by rw [hg]; exact_mod_cast hδ0
  have hrank : ∀ n : ℕ, |(Module.finrank ℤ (sec ℤ d.x n) : ℝ) -
      (genDeg (ι := GlobalTheory κ) (coordIdeal ℤ d.x) D 1 : ℝ) * (n : ℝ) ^ D / D.factorial| ≤
        C * ((n : ℝ) + 1) ^ ((D : ℝ) - 1) := by
    intro n
    have e : (GroundTheory.Heights₂.Heights.NumbersDVR.hilbFn (ι := GlobalTheory κ)
        ((coordIdeal ℤ d.x).map (MvPolynomial.map (Int.castRingHom ℚ))) (fun _ => (n : ℤ)) : ℝ) =
        (Module.finrank ℤ (sec ℤ d.x n) : ℝ) := by exact_mod_cast hRk Ω κ d.x n
    rw [← e, hg]
    exact hC n
  set δ : ℝ := (genDeg (ι := GlobalTheory κ) (coordIdeal ℤ d.x) D 1 : ℝ) with hδdef
  set T : ℝ := top I d.x d.m D with hTdef
  set r : ℕ → ℝ := fun n => (Module.finrank ℤ (sec ℤ d.x n) : ℝ) with hrdef
  have hfD : (0 : ℝ) < D.factorial := by exact_mod_cast Nat.factorial_pos D
  have hfac : ((D + 1).factorial : ℝ) = ((D : ℝ) + 1) * D.factorial := by
    rw [Nat.factorial_succ]; push_cast; ring
  set c : ℝ := T / (((D : ℝ) + 1) * δ) with hcdef

  have hR : (fun n : ℕ => r n - δ * (n : ℝ) ^ D / D.factorial) =o[atTop] fun n : ℕ => (n : ℝ) ^ D := by
    refine IsBigO.trans_isLittleO ?_ (succ_rpow_isLittleO D d.one_le)
    refine IsBigO.of_bound C (Eventually.of_forall fun n => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    exact hrank n

  have hH : (fun n : ℕ => resChi d n - T * (n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) =o[atTop] pw D :=
    (hHSM D Ω κ I d hI).1

  have hE : (fun n : ℕ => resChi d n - c * n * r n) =o[atTop] pw D := by
    have h2 : (fun n : ℕ => (c * (n : ℝ)) * (r n - δ * (n : ℝ) ^ D / D.factorial)) =o[atTop] pw D := by
      refine (((isBigO_refl (fun n : ℕ => (n : ℝ)) atTop).const_mul_left c).mul_isLittleO hR).congr
        (fun _ => rfl) ?_
      intro n; simp only [pw]; ring
    refine (hH.sub h2).congr (fun n => ?_) (fun _ => rfl)
    rw [hcdef, hfac]
    field_simp
    ring

  have hlow : ∀ᶠ n : ℕ in atTop, δ / (2 * D.factorial) * (n : ℝ) ^ D ≤ r n := by
    filter_upwards [hR.def (show 0 < δ / (2 * D.factorial) by positivity)] with n hn
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ D)] at hn
    have h1 := neg_abs_le (r n - δ * (n : ℝ) ^ D / D.factorial)
    have e : δ * (n : ℝ) ^ D / D.factorial = 2 * (δ / (2 * D.factorial) * (n : ℝ) ^ D) := by
      field_simp
    linarith
  filter_upwards [hlow, hE.def (show 0 < ε * (δ / (2 * D.factorial)) by positivity), eventually_ge_atTop 1]
    with n hn hEn hn1
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hrpos : 0 < r n := lt_of_lt_of_le (by positivity) hn
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ pw D n)] at hEn
  have hslope : T * n / (((D : ℝ) + 1) * δ) = c * n := by rw [hcdef]; ring
  show T * n / (((D : ℝ) + 1) * δ) - ε * n ≤ resChi d n / r n
  rw [hslope, le_div_iff₀ hrpos]
  have h1 : ε * n * (δ / (2 * D.factorial) * (n : ℝ) ^ D) ≤ ε * n * r n :=
    mul_le_mul_of_nonneg_left hn (by positivity)
  have h2 := neg_abs_le (resChi d n - c * n * r n)
  have h4 : ε * (δ / (2 * D.factorial)) * pw D n = ε * n * (δ / (2 * D.factorial) * (n : ℝ) ^ D) := by
    simp only [pw]; ring
  linarith

end SlopeLowerBound

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

