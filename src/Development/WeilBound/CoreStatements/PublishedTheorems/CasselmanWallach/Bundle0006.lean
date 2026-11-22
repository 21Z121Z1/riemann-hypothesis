import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.FunctionalCalculusLaws
import GroundTheory.GlobalFields.Artin.Bundle0001
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirAlgebra.Bundle0001

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.NilpotentOfPowerTraces
section
noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace CharpolyPowerTraces

open Polynomial

theorem coeff_succ {R : Type} [CommRing R] {n : ℕ} (N : Matrix (Fin n) (Fin n) R)
    (h : ∀ k, (N ^ (k + 1)).trace = 0) (m : ℕ) :
    ((m : R) + 1) * N.charpolyRev.coeff (m + 1) = 0 := by
  have hps : (PowerSeries.mk fun k => (N ^ (k + 1)).trace) = 0 := by
    ext k
    simp [h]
  have hd : derivative N.charpolyRev = 0 := by
    have hc := GroundTheory.Global.coe_derivative_charpolyRev N
    rw [hps, mul_zero] at hc
    exact Polynomial.coe_eq_zero_iff.mp hc
  have hm := congrArg (fun p => Polynomial.coeff p m) hd
  simp only [Polynomial.coeff_derivative, Polynomial.coeff_zero] at hm
  rw [mul_comm]
  exact hm

theorem coeff_succ_zero {R : Type} [CommRing R] [Algebra ℚ R] {n : ℕ} (N : Matrix (Fin n) (Fin n) R)
    (h : ∀ k, (N ^ (k + 1)).trace = 0) (m : ℕ) : N.charpolyRev.coeff (m + 1) = 0 := by
  have hu : IsUnit ((m : R) + 1) := by
    have : ((m : R) + 1) = algebraMap ℚ R ((m : ℚ) + 1) := by simp
    rw [this]; exact (IsUnit.mk0 _ (by positivity)).map _
  exact hu.mul_right_eq_zero.mp (coeff_succ N h m)

theorem charpoly_eq {R : Type} [CommRing R] [Algebra ℚ R] [Nontrivial R] {n : ℕ}
    (N : Matrix (Fin n) (Fin n) R) (h : ∀ k, (N ^ (k + 1)).trace = 0) : N.charpoly = X ^ n := by
  have hRev : ∀ i, 1 ≤ i → N.charpolyRev.coeff i = 0 := by
    intro i hi
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hi
    exact coeff_succ_zero N h m
  have hdeg : N.charpoly.natDegree = n := by
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  ext j
  rw [Polynomial.coeff_X_pow]
  rcases lt_trichotomy j n with hj | hj | hj
  · rw [if_neg hj.ne]
    have hz := hRev (n - j) (by omega)
    rw [← Matrix.reverse_charpoly, Polynomial.coeff_reverse, hdeg,
      Polynomial.revAt_le (by omega)] at hz
    rwa [show n - (n - j) = j by omega] at hz
  · rw [if_pos hj]
    have hl := (Matrix.charpoly_monic N).leadingCoeff
    rw [Polynomial.leadingCoeff, hdeg] at hl
    rw [hj]
    exact hl
  · rw [if_neg hj.ne']
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

end CharpolyPowerTraces

theorem nilpotent_of_power_traces : A4 := by
  unfold A4
  intro R _ _ n N h
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Subsingleton.elim _ _
  have hc := Matrix.aeval_self_charpoly N
  rw [CharpolyPowerTraces.charpoly_eq N h, Polynomial.aeval_X_pow] at hc
  exact hc

end PositivityTheory.CW

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.OrthonormalEigenbasisOfBasic
section
noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace EigenvectorBasisSetup

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem casK_apply (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (v : V) :
    casimirK ε E v = ∑ a, ∑ b, if ε b = ε a then E a b (E b a v) else 0 := by
  unfold casimirK
  simp only [Finset.sum_filter, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  split_ifs <;> simp

theorem cas_apply (E : Fin n → Fin n → Module.End ℂ V) (v : V) :
    casimir E v = ∑ a, ∑ b, E a b (E b a v) := by
  unfold casimir
  simp [LinearMap.sum_apply]

theorem nc_sum {M : Type*} [AddCommMonoid M] (ε : Fin n → Bool) (f : Fin n × Fin n → M) :
    ∑ p ∈ nc ε, f p = ∑ a, ∑ b, if ε b = ε a then 0 else f (a, b) := by
  unfold nc
  rw [Finset.sum_filter, ← Finset.univ_product_univ, Finset.sum_product]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases h : ε b = ε a
  · simp [h]
  · have : ε a ≠ ε b := fun h' => h h'.symm
    simp [h, this]

theorem swap_sum {M : Type*} [AddCommMonoid M] (ε : Fin n → Bool) (f g : Fin n → Fin n → M) :
    (∑ a, ∑ b, if ε b = ε a then f a b else g a b) =
      ∑ a, ∑ b, if ε b = ε a then f b a else g b a := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases h : ε b = ε a
  · simp [h]
  · have : ε a ≠ ε b := fun h' => h h'.symm
    simp [h, this]

theorem sq_re (u : V) : ‖u‖ ^ 2 = (inner ℂ u u).re := by
  simpa using (inner_self_eq_norm_sq (𝕜 := ℂ) u).symm

theorem sm_re (r : ℝ) (u : V) : (inner ℂ u ((r : ℂ) • u)).re = r * ‖u‖ ^ 2 := by
  rw [inner_smul_right, Complex.re_ofReal_mul, ← sq_re]

end EigenvectorBasisSetup

open EigenvectorBasisSetup in
theorem orthonormal_eigenbasis_of_basic : A0 := by
  intro n ε V _ _ E hM
  have hU := hM.uni
  have hc : ∀ a b, ε b = ε a → ∀ x y, inner ℂ (E a b x) y = inner ℂ x (E b a y) := by
    intro a b h x y
    rw [hU a b x y]
    simp [adjSign, h.symm]
  have hK : ∀ x y, inner ℂ x (casimirK ε E y) =
      ∑ a, ∑ b, if ε b = ε a then inner ℂ (E b a x) (E b a y) else 0 := by
    intro x y
    rw [casK_apply, inner_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs with h
    · rw [hc b a h.symm]
    · simp
  have hKre : ∀ w, (inner ℂ w (casimirK ε E w)).re =
      ∑ a, ∑ b, if ε b = ε a then ‖E b a w‖ ^ 2 else 0 := by
    intro w
    rw [hK, Complex.re_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs
    · rw [sq_re]
    · simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y
    rw [← inner_conj_symm, hK, hK, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs <;> simp
  · intro μ v hv h0
    have h1 := hKre v
    rw [hv, sm_re] at h1
    have h2 : 0 ≤ μ * ‖v‖ ^ 2 := by
      rw [h1]
      refine Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => ?_
      split_ifs <;> positivity
    have h3 : 0 < ‖v‖ ^ 2 := by positivity
    exact nonneg_of_mul_nonneg_left h2 h3
  · intro a b h
    unfold Z
    exact sub_eq_zero.mpr (casimirK_comm ε hM.gl a b h)
  · intro κ hκ w
    have h3 : ∑ p ∈ nc ε, E p.1 p.2 (E p.2 p.1 w) = (κ : ℂ) • w - casimirK ε E w := by
      rw [← hκ w, cas_apply, casK_apply, nc_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      split_ifs <;> simp
    have hnorm : ∀ a b, ‖E a b w‖ ^ 2 = (adjSign ε a b * inner ℂ w (E b a (E a b w))).re := by
      intro a b
      rw [sq_re, hU]
    have h2 : ∑ p ∈ nc ε, ‖E p.1 p.2 w‖ ^ 2 = (inner ℂ w (casimirK ε E w)).re - κ * ‖w‖ ^ 2 := by
      have e1 : ∑ p ∈ nc ε, ‖E p.1 p.2 w‖ ^ 2 =
          ∑ a, ∑ b, if ε b = ε a then 0 else -(inner ℂ w (E b a (E a b w))).re := by
        rw [nc_sum]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        by_cases h : ε b = ε a
        · simp [h]
        · have : ε a ≠ ε b := fun h' => h h'.symm
          simp [h, hnorm, adjSign, this]
      have e2 : (∑ a, ∑ b, if ε b = ε a then (0 : ℝ) else -(inner ℂ w (E b a (E a b w))).re) =
          -(inner ℂ w (∑ p ∈ nc ε, E p.1 p.2 (E p.2 p.1 w))).re := by
        rw [swap_sum, nc_sum, inner_sum, Complex.re_sum, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [inner_sum, Complex.re_sum, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun b _ => ?_
        split_ifs <;> simp
      rw [e1, e2, h3, inner_sub_right, Complex.sub_re, sm_re]
      ring
    have h1 : ∑ a, ∑ b, ‖E a b w‖ ^ 2 = 2 * (inner ℂ w (casimirK ε E w)).re - κ * ‖w‖ ^ 2 := by
      have e1 : ∑ a, ∑ b, ‖E a b w‖ ^ 2 =
          (∑ a, ∑ b, if ε b = ε a then ‖E a b w‖ ^ 2 else 0) +
            ∑ a, ∑ b, if ε b = ε a then 0 else ‖E a b w‖ ^ 2 := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun b _ => ?_
        split_ifs <;> simp
      have e2 : (∑ a, ∑ b, if ε b = ε a then ‖E a b w‖ ^ 2 else (0 : ℝ)) =
          (inner ℂ w (casimirK ε E w)).re := by
        rw [hKre, swap_sum]
      have e3 : (∑ a, ∑ b, if ε b = ε a then (0 : ℝ) else ‖E a b w‖ ^ 2) =
          ∑ p ∈ nc ε, ‖E p.1 p.2 w‖ ^ 2 := by
        rw [nc_sum]
      rw [e1, e2, e3, h2]
      ring
    exact ⟨h1, h2, h3⟩

end PositivityTheory.CW

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.PMaxPr
section
noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace PMaxPr

theorem hilbert_schmidt_nonneg_alt {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ hs2 g :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

def evalAt {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (g : Matrix (Fin n) (Fin n) ℂ)
    (F : V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ)) : V →ₗ[ℂ] ℂ :=
  (LinearMap.proj (R := ℂ) (φ := fun _ : Matrix (Fin n) (Fin n) ℂ => ℂ) g).comp F

@[simp] theorem evalAt_apply {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (g : Matrix (Fin n) (Fin n) ℂ)
    (F : V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ)) (v : V) : evalAt g F v = F v g := rfl

theorem sq_bound (x C w : ℝ) (N : ℕ) (h : x ≤ C * w ^ N) (hx : 0 ≤ x) : x ^ 2 ≤ C ^ 2 * w ^ (2 * N) := by
  calc x ^ 2 ≤ (C * w ^ N) ^ 2 := pow_le_pow_left₀ hx h 2
    _ = C ^ 2 * w ^ (2 * N) := by rw [mul_pow, ← pow_mul, mul_comm N 2]

end PMaxPr

open PMaxPr in
theorem maxPr_of : CasimirIsRealScalar → EigenbasisExists → A13 → UnitaryGroupFacts → MaximumPrincipleVar → SumSquaresSecondDerivative → B5 → MaxPr := by
  intro hA3c hA11a hA13 _ hB4a hB4b hB5 n ε V _ _ E hM N
  classical
  obtain ⟨κ, hκ⟩ := hA3c n ε V E hM
  obtain ⟨ι, b, μ, hb⟩ := hA11a n ε V E hM
  obtain ⟨c, hc0, hc⟩ := hB4a n ε (2 * N)
  obtain ⟨s, x₀, C₁, hs, hC₁, h13⟩ := hA13 n ε V E hM ι b μ hb κ hκ (c / 2) (div_nonneg hc0 (by norm_num))
  have hTfin : {i | μ i < x₀}.Finite := (hb.fin x₀).subset fun i (hi : μ i < x₀) => show μ i ≤ x₀ from le_of_lt hi
  have hT : ∀ i, i ∈ hTfin.toFinset ↔ μ i < x₀ := fun i => by simp
  have hW1 : 0 ≤ (1 + hs2 (1 : Matrix (Fin n) (Fin n) ℂ)) ^ (2 * N) :=
    pow_nonneg (by linarith [hilbert_schmidt_nonneg_alt (1 : Matrix (Fin n) (Fin n) ℂ)]) _
  have hKK : 0 ≤ 2 * C₁ * (hTfin.toFinset.card : ℝ) * (1 + hs2 (1 : Matrix (Fin n) (Fin n) ℂ)) ^ (2 * N) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC₁) (Nat.cast_nonneg _)) hW1
  refine ⟨s, Real.sqrt (2 * C₁ * hTfin.toFinset.card * (1 + hs2 (1 : Matrix (Fin n) (Fin n) ℂ)) ^ (2 * N)),
    hTfin.toFinset.image b, Real.sqrt_nonneg _, ?_⟩
  intro F hcont hder hgrow B hB hI v
  have hA0 : 0 ≤ 2 * C₁ * (hTfin.toFinset.card : ℝ) * B ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC₁) (Nat.cast_nonneg _)) (sq_nonneg B)
  choose Cf hCf using hgrow
  have key : ∀ (R : ℝ) (S : Finset ι), (∀ i, i ∈ S ↔ μ i < R) →
      ∑ i ∈ S, phiR s R (μ i) * ‖F (b i) 1‖ ^ 2 ≤
        (Real.sqrt (2 * C₁ * hTfin.toFinset.card * (1 + hs2 (1 : Matrix (Fin n) (Fin n) ℂ)) ^ (2 * N)) * B) ^ 2 := by
    intro R S hS
    have hcu : ContinuousOn (fun g => ∑ i ∈ S, phiR s R (μ i) * ‖F (b i) g‖ ^ 2) (UJset ε) :=
      continuousOn_finsetSum _ fun i _ => continuousOn_const.mul ((hcont (b i)).norm.pow 2)
    have hgu : ∃ C : ℝ, ∀ g ∈ UJset ε,
        (∑ i ∈ S, phiR s R (μ i) * ‖F (b i) g‖ ^ 2) ≤ C * (1 + hs2 g) ^ (2 * N) := by
      refine ⟨∑ i ∈ S, phiR s R (μ i) * Cf (b i) ^ 2, fun g hg => ?_⟩
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (sq_bound _ _ _ _ (hCf (b i) g hg) (norm_nonneg _)) (le_max_right _ _)
    have hdu : ∀ g ∈ UJset ε, ∃ d : Fin n × Fin n → ℝ,
        (∀ p ∈ nc ε, ∃ u' : ℝ → ℝ, (∀ t, HasDerivAt (fun t : ℝ =>
          ∑ i ∈ S, phiR s R (μ i) * ‖F (b i) (g * NormedSpace.exp (t • Xp p.1 p.2))‖ ^ 2) (u' t) t) ∧
          HasDerivAt u' (d p) 0) ∧
        c * (∑ i ∈ S, phiR s R (μ i) * ‖F (b i) g‖ ^ 2) -
          2 * C₁ * (hTfin.toFinset.card : ℝ) * B ^ 2 * (1 + hs2 g) ^ (2 * N) ≤ ∑ p ∈ nc ε, d p := by
      intro g hg
      obtain ⟨d, hd, hsum⟩ := hB4b n ε V E hM ι b μ hb κ hκ F hder S (fun i => phiR s R (μ i)) g hg
      refine ⟨d, hd, ?_⟩
      rw [hsum]
      have h13g := h13 R (evalAt g F) S hTfin.toFinset hS hT
      simp only [evalAt_apply] at h13g
      have hTb : ∑ i ∈ hTfin.toFinset, ‖F (b i) g‖ ^ 2 ≤
          hTfin.toFinset.card • (B ^ 2 * (1 + hs2 g) ^ (2 * N)) :=
        Finset.sum_le_card_nsmul _ _ _ fun i hi =>
          sq_bound _ _ _ _ (hI (b i) (Finset.mem_image_of_mem b hi) g hg) (norm_nonneg _)
      rw [nsmul_eq_mul] at hTb
      have h2 := mul_le_mul_of_nonneg_left hTb hC₁
      nlinarith [h2, h13g]
    have h1 := hc (fun g => ∑ i ∈ S, phiR s R (μ i) * ‖F (b i) g‖ ^ 2) _ hA0 hcu hgu hdu
    calc _ ≤ _ := h1
      _ = _ := by rw [mul_pow, Real.sq_sqrt hKK]; ring
  have h5 := hB5 n ε V E hM ι b μ hb (evalAt 1 F) s _
    (mul_nonneg (Real.sqrt_nonneg _) hB) (fun R S hS => by simpa only [evalAt_apply] using key R S hS) hs v
  simpa only [evalAt_apply] using h5

end PositivityTheory.CW

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.SecondDerivativeHolds
section
noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace HilbertSchmidtNorm

variable {n : ℕ}

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in
theorem hasDerivAt_entry (g X Y : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) (i j : Fin n) :
    HasDerivAt (fun s : ℝ => (g * NormedSpace.exp (s • X) * Y) i j)
      ((g * NormedSpace.exp (t • X) * X * Y) i j) t := by
  have h := ((hasDerivAt_exp_smul_const (𝕂 := ℝ) X t).const_mul g).mul_const Y
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] ℂ :=
    { toFun := fun x => x i j
      map_add' := fun x y => rfl
      map_smul' := fun c x => rfl }
  have h2 := (LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt t h
  have e : (g * NormedSpace.exp (t • X) * X * Y) i j = L (g * (NormedSpace.exp (t • X) * X) * Y) := by
    show _ = (g * (NormedSpace.exp (t • X) * X) * Y) i j
    rw [mul_assoc g]
  rw [e]
  exact h2

theorem hilbert_schmidt_nonneg_alt (g : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ hs2 g :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

theorem hilbert_schmidt_mul_le (g X : Matrix (Fin n) (Fin n) ℂ) : hs2 (g * X) ≤ hs2 g * hs2 X := by
  have key : ∀ i j, ‖(g * X) i j‖ ^ 2 ≤ (∑ k, ‖g i k‖ ^ 2) * (∑ k, ‖X k j‖ ^ 2) := by
    intro i j
    have h1 : ‖(g * X) i j‖ ≤ ∑ k, ‖g i k‖ * ‖X k j‖ := by
      rw [Matrix.mul_apply]
      exact (norm_sum_le _ _).trans (le_of_eq (by simp))
    calc ‖(g * X) i j‖ ^ 2 ≤ (∑ k, ‖g i k‖ * ‖X k j‖) ^ 2 := by gcongr
      _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  unfold hs2
  calc ∑ i, ∑ j, ‖(g * X) i j‖ ^ 2 ≤ ∑ i, ∑ j, (∑ k, ‖g i k‖ ^ 2) * (∑ k, ‖X k j‖ ^ 2) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => key i j
    _ = (∑ i, ∑ k, ‖g i k‖ ^ 2) * ∑ j, ∑ k, ‖X k j‖ ^ 2 := by
        rw [Finset.sum_mul]; simp_rw [Finset.mul_sum]
    _ = _ := by rw [Finset.sum_comm (f := fun j k => ‖X k j‖ ^ 2)]

theorem abs_two_inner_le (M N : Matrix (Fin n) (Fin n) ℂ) :
    |∑ i, ∑ j, 2 * inner ℝ (M i j) (N i j)| ≤ hs2 M + hs2 N := by
  unfold hs2
  rw [← Finset.sum_add_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  have := abs_real_inner_le_norm (M i j) (N i j)
  rw [abs_mul, abs_two]
  nlinarith [sq_nonneg (‖M i j‖ - ‖N i j‖)]

theorem hasDerivAt_entry1 (g X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) (i j : Fin n) :
    HasDerivAt (fun s : ℝ => (g * NormedSpace.exp (s • X)) i j)
      ((g * NormedSpace.exp (t • X) * X) i j) t := by
  simpa using hasDerivAt_entry g X 1 t i j

theorem hd1 (g X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => hs2 (g * NormedSpace.exp (s • X)))
      (∑ i, ∑ j, 2 * inner ℝ ((g * NormedSpace.exp (t • X)) i j) ((g * NormedSpace.exp (t • X) * X) i j)) t := by
  unfold hs2
  refine HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun j _ => ?_
  exact (hasDerivAt_entry1 g X t i j).norm_sq

theorem hd2 (g X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => ∑ i, ∑ j, 2 * inner ℝ ((g * NormedSpace.exp (s • X)) i j)
        ((g * NormedSpace.exp (s • X) * X) i j))
      (∑ i, ∑ j, 2 * (inner ℝ ((g * NormedSpace.exp (t • X)) i j) ((g * NormedSpace.exp (t • X) * X * X) i j) +
        inner ℝ ((g * NormedSpace.exp (t • X) * X) i j) ((g * NormedSpace.exp (t • X) * X) i j))) t := by
  refine HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun j _ => ?_
  exact ((hasDerivAt_entry1 g X t i j).inner ℝ (hasDerivAt_entry g X X t i j)).const_mul 2

theorem L1 (r : ℕ) (u : ℝ) (hu : 1 ≤ u) :
    ((r - 1 : ℕ) : ℝ) * u ^ (r - 1 - 1) * u ^ 2 ≤ r * u ^ r := by
  rcases r with _ | _ | k
  · simp
  · simp; linarith
  · have e1 : k + 1 + 1 - 1 = k + 1 := by omega
    have e2 : u ^ k * u ^ 2 = u ^ (k + 1 + 1) := by rw [← pow_add]
    rw [e1, mul_assoc, show k + 1 - 1 = k by omega, e2]
    have h0 : 0 ≤ u ^ (k + 1 + 1) := by positivity
    push_cast
    nlinarith

theorem L2 (r : ℕ) (u : ℝ) : (r : ℝ) * u ^ (r - 1) * u ≤ r * u ^ r := by
  rcases r with _ | k
  · simp
  · simp [pow_succ, mul_assoc]

end HilbertSchmidtNorm

open HilbertSchmidtNorm in
theorem heightFunctionalStatement_of_pairingProperties : B2 := by
  intro n X r
  set A : ℝ := 1 + hs2 X with hA
  set Bc : ℝ := 1 + hs2 (X * X) + 2 * hs2 X with hBc
  have hXn := hilbert_schmidt_nonneg_alt X
  have hXXn := hilbert_schmidt_nonneg_alt (X * X)
  refine ⟨r * r * A ^ 2 + r * Bc, by positivity, fun g => ?_⟩
  set h : ℝ → ℝ := fun s => hs2 (g * NormedSpace.exp (s • X)) with hh
  set h' : ℝ → ℝ := fun t => ∑ i, ∑ j, 2 * inner ℝ ((g * NormedSpace.exp (t • X)) i j)
    ((g * NormedSpace.exp (t • X) * X) i j) with hh'
  set H2 : ℝ := ∑ i, ∑ j, 2 * (inner ℝ ((g * NormedSpace.exp ((0:ℝ) • X)) i j)
    ((g * NormedSpace.exp ((0:ℝ) • X) * X * X) i j) + inner ℝ ((g * NormedSpace.exp ((0:ℝ) • X) * X) i j)
      ((g * NormedSpace.exp ((0:ℝ) • X) * X) i j)) with hH2
  have d1 : ∀ t, HasDerivAt h (h' t) t := fun t => hd1 g X t
  have d2 : HasDerivAt h' H2 0 := hd2 g X 0
  refine ⟨fun t => r * (1 + h t) ^ (r - 1) * h' t,
    r * (((r - 1 : ℕ) : ℝ) * (1 + h 0) ^ (r - 1 - 1) * h' 0) * h' 0 + r * (1 + h 0) ^ (r - 1) * H2,
    fun t => ((d1 t).const_add 1).pow r, (((d1 0).const_add 1).pow (r - 1)).const_mul (r : ℝ) |>.mul d2, ?_⟩
  have e0 : NormedSpace.exp ((0:ℝ) • X) = 1 := by simp
  have hg := hilbert_schmidt_nonneg_alt g
  have h0 : h 0 = hs2 g := by simp [hh]
  have hp : |h' 0| ≤ A * hs2 g := by
    have := abs_two_inner_le g (g * X)
    have := hilbert_schmidt_mul_le g X
    simp only [hh', e0, mul_one]
    nlinarith
  have hpp : |H2| ≤ Bc * hs2 g := by
    have k1 := abs_two_inner_le g (g * (X * X))
    have k2 := abs_two_inner_le (g * X) (g * X)
    have k3 := hilbert_schmidt_mul_le g X
    have k4 := hilbert_schmidt_mul_le g (X * X)
    have : H2 = (∑ i, ∑ j, 2 * inner ℝ (g i j) ((g * (X * X)) i j)) +
        ∑ i, ∑ j, 2 * inner ℝ ((g * X) i j) ((g * X) i j) := by
      simp only [hH2, e0, mul_one, mul_add, Finset.sum_add_distrib, mul_assoc]
    rw [this]
    refine (abs_add_le _ _).trans ?_
    nlinarith
  rw [h0]
  set u : ℝ := 1 + hs2 g with hu
  have hu1 : 1 ≤ u := by linarith
  have hP : 0 ≤ ((r - 1 : ℕ) : ℝ) * u ^ (r - 1 - 1) := by positivity
  have hQ : 0 ≤ u ^ (r - 1) := by positivity
  have hr : (0 : ℝ) ≤ r := by positivity
  have hA0 : 0 ≤ A := by positivity
  have hsq : h' 0 ^ 2 ≤ (A * u) ^ 2 := by
    have : |h' 0| ≤ A * u := hp.trans (by nlinarith)
    exact sq_le_sq' (by linarith [neg_abs_le (h' 0)]) (le_trans (le_abs_self _) this)
  have t1 : r * (((r - 1 : ℕ) : ℝ) * u ^ (r - 1 - 1) * h' 0) * h' 0 ≤ r * A ^ 2 * (r * u ^ r) := by
    calc r * (((r - 1 : ℕ) : ℝ) * u ^ (r - 1 - 1) * h' 0) * h' 0
        = r * (((r - 1 : ℕ) : ℝ) * u ^ (r - 1 - 1)) * h' 0 ^ 2 := by ring
      _ ≤ r * (((r - 1 : ℕ) : ℝ) * u ^ (r - 1 - 1)) * (A * u) ^ 2 := by gcongr
      _ = r * A ^ 2 * (((r - 1 : ℕ) : ℝ) * u ^ (r - 1 - 1) * u ^ 2) := by ring
      _ ≤ r * A ^ 2 * (r * u ^ r) := mul_le_mul_of_nonneg_left (L1 r u hu1) (by positivity)
  have t2 : r * u ^ (r - 1) * H2 ≤ Bc * (r * u ^ r) := by
    have hH : H2 ≤ Bc * u := (le_abs_self _).trans (hpp.trans (by nlinarith))
    calc r * u ^ (r - 1) * H2 ≤ r * u ^ (r - 1) * (Bc * u) := by gcongr
      _ = Bc * (r * u ^ (r - 1) * u) := by ring
      _ ≤ Bc * (r * u ^ r) := mul_le_mul_of_nonneg_left (L2 r u) (by rw [hBc]; positivity)
  nlinarith

end PositivityTheory.CW

end
end

