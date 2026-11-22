import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0024
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0025
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0026
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0027
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0023

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGeneratedOne
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace GeneratedOne

variable {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

omit [Fintype K] in

theorem isMultiHomog_mul {f g : MRingOver S ι} {a b : K → ℕ} (hf : IsMultiHomog f a)
    (hg : IsMultiHomog g b) : IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hf m1 hm1 k, hg m2 hm2 k]

omit [Fintype K] in

theorem isMultiHomog_one : IsMultiHomog (1 : MRingOver S ι) (fun _ => 0) := by
  intro m hm k
  have h := MvPolynomial.support_monomial_subset (s := (0 : (Σ k, ι k) →₀ ℕ)) (a := (1 : S)) hm
  rw [Finset.mem_singleton] at h
  subst h
  simp

omit [Fintype K] in
open Classical in

theorem isMultiHomog_X (k : K) (i : ι k) :
    IsMultiHomog (X ⟨k, i⟩ : MRingOver S ι) (Pi.single k 1) := by
  classical
  intro m hm k'
  have h := MvPolynomial.support_monomial_subset (s := Finsupp.single (⟨k, i⟩ : Σ k, ι k) 1) (a := (1 : S)) hm
  rw [Finset.mem_singleton] at h
  subst h
  by_cases hk : k' = k
  · subst hk
    simp [Finsupp.single_apply]
  · have : ∀ j : ι k', (⟨k, i⟩ : Σ k, ι k) ≠ ⟨k', j⟩ := fun j e => hk (congrArg Sigma.fst e).symm
    simp [hk]

open Classical in

theorem isMultiHomog_prodX (c : ∀ k, ι k) :
    IsMultiHomog (∏ k, (X ⟨k, c k⟩ : MRingOver S ι)) (fun _ => 1) := by
  classical
  have key : ∀ s : Finset K, IsMultiHomog (∏ k ∈ s, (X ⟨k, c k⟩ : MRingOver S ι))
      (∑ k ∈ s, Pi.single k 1) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.prod_empty, Finset.sum_empty]
      exact isMultiHomog_one
    | insert k s hk ih =>
      rw [Finset.prod_insert hk, Finset.sum_insert hk]
      exact isMultiHomog_mul (isMultiHomog_X k (c k)) ih
  have e : (∑ k, (Pi.single k 1 : K → ℕ)) = fun _ => 1 := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  have := key Finset.univ
  rwa [e] at this

end GeneratedOne

theorem GeneratedOne.proof : GeneratedOne.Statement := by
  intro S _ K _ _ ι _ _ V I
  classical
  set M := MRingOver S ι ⧸ V
  choose c hc using I.2.1
  set t : MRingOver S ι := ∏ k, X ⟨k, c k⟩ with ht_def
  have ht : t ∈ KH.cellMon S I.1 :=
    Submonoid.prod_mem _ fun k _ => Submonoid.subset_closure ⟨k, c k, hc k, rfl⟩
  have htH : IsMultiHomog t (fun _ => 1) := GeneratedOne.isMultiHomog_prodX c
  have hres : ∀ F J : ∀ k, Finset (ι k), (∀ l, F l ⊆ J l) →
      KH.cellRes S M F J (LocalizedModule.mk (Ideal.Quotient.mk V t) 1) =
        LocalizedModule.mk (Ideal.Quotient.mk V t) 1 := by
    intro F J hFJ
    have hle : KH.cellMon S F ≤ KH.cellMon S J := by
      apply Submonoid.closure_mono
      rintro f ⟨k, j, hj, rfl⟩
      exact ⟨k, j, hFJ k hj, rfl⟩
    unfold KH.cellRes
    rw [dif_pos hle, ← LocalizedModule.mkLinearMap_apply, IsLocalizedModule.liftOfLE_apply,
      LocalizedModule.mkLinearMap_apply]
  refine ⟨1, fun _ _ => LocalizedModule.mk (Ideal.Quotient.mk V t) 1,
    fun _ => LocalizedModule.mk (Ideal.Quotient.mk V 1) ⟨t, ht⟩, fun _ => ⟨?_, ?_⟩, fun _ => ?_, ?_⟩
  ·
    intro J _
    refine Submodule.subset_span ⟨Ideal.Quotient.mk V t, 1, fun _ => 0, ?_, ?_, rfl⟩
    · simpa using GeneratedOne.isMultiHomog_one (S := S) (ι := ι)
    · have e : ((fun _ : K => (1 : ℤ)) + fun k => (((fun _ : K => (0 : ℕ)) k : ℕ) : ℤ)) = fun _ => 1 := by
        funext k; simp
      rw [e]
      refine Submodule.subset_span ⟨t, ⟨fun _ => zero_le_one, ?_⟩, rfl⟩
      simpa using htH
  ·
    show _ ∈ (LinearMap.ker _).restrictScalars S
    rw [Submodule.restrictScalars_mem, LinearMap.mem_ker]
    funext J
    obtain ⟨J, hJne, hJ⟩ := J
    rw [KH.cechD]
    erw [LinearMap.pi_apply]
    simp only [LinearMap.sum_apply]
    apply Finset.sum_eq_zero
    intro k _
    have hle : (J k).card - 1 ≤ 1 := by
      have : (J k).card - 1 ≤ ∑ l, ((J l).card - 1) :=
        Finset.single_le_sum (f := fun l => (J l).card - 1) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ k)
      omega
    have hpos := (hJne k).card_pos

    have hface : ∀ x ∈ J k, ∀ y ∈ J k,
        ((∀ l, (Function.update J k ((J k).erase x) l).Nonempty) ∧
          ∑ l, ((Function.update J k ((J k).erase x) l).card - 1) = 0) →
        ((∀ l, (Function.update J k ((J k).erase y) l).Nonempty) ∧
          ∑ l, ((Function.update J k ((J k).erase y) l).card - 1) = 0) := by
      rintro x hx y hy ⟨h1, h2⟩
      have hcard : ∀ l, (Function.update J k ((J k).erase y) l).card =
          (Function.update J k ((J k).erase x) l).card := by
        intro l
        rcases eq_or_ne l k with rfl | hl
        · simp [Finset.card_erase_of_mem hx, Finset.card_erase_of_mem hy]
        · simp [Function.update_of_ne hl]
      refine ⟨fun l => Finset.card_pos.mp ?_, ?_⟩
      · rw [hcard]; exact Finset.card_pos.mpr (h1 l)
      · simp only [hcard]; exact h2
    rcases (show (J k).card = 1 ∨ (J k).card = 2 by omega) with h1 | h2
    · obtain ⟨a, hJk⟩ := Finset.card_eq_one.mp h1
      rw [Finset.sum_congr hJk (fun _ _ => rfl), Finset.sum_singleton]
      erw [dif_neg]
      · rfl
      · rintro ⟨hne, -⟩
        have := hne k
        simp [hJk] at this
    · obtain ⟨a, b, hab, hJk⟩ : ∃ a b, a < b ∧ J k = {a, b} := by
        obtain ⟨x, y, hxy, hJk⟩ := Finset.card_eq_two.mp h2
        rcases lt_or_gt_of_ne hxy with h | h
        · exact ⟨x, y, h, hJk⟩
        · exact ⟨y, x, h, by rw [hJk, Finset.pair_comm]⟩
      have ha : a ∈ J k := by rw [hJk]; simp
      have hb : b ∈ J k := by rw [hJk]; simp
      rw [Finset.sum_congr hJk (fun _ _ => rfl), Finset.sum_pair hab.ne]
      by_cases hP : (∀ l, (Function.update J k ((J k).erase a) l).Nonempty) ∧
          ∑ l, ((Function.update J k ((J k).erase a) l).card - 1) = 0
      · erw [dif_pos hP, dif_pos (hface a ha b hb hP)]
        change KH.faceSign J k a • KH.cellRes S M (Function.update J k ((J k).erase a)) J
              (LocalizedModule.mk (Ideal.Quotient.mk V t) 1) +
            KH.faceSign J k b • KH.cellRes S M (Function.update J k ((J k).erase b)) J
              (LocalizedModule.mk (Ideal.Quotient.mk V t) 1) = 0
        rw [hres _ _ (fun l => by
              rcases eq_or_ne l k with rfl | hl
              · simp [Finset.erase_subset]
              · simp [Function.update_of_ne hl]),
          hres _ _ (fun l => by
              rcases eq_or_ne l k with rfl | hl
              · simp [Finset.erase_subset]
              · simp [Function.update_of_ne hl])]
        have hsa : KH.faceSign J k a = (-1) ^ (∑ l ∈ Finset.univ.filter (· < k), ((J l).card - 1)) := by
          unfold KH.faceSign
          rw [hJk]
          simp [Finset.filter_insert, Finset.filter_singleton, not_lt.mpr hab.le]
        have hsb : KH.faceSign J k b = -(-1) ^ (∑ l ∈ Finset.univ.filter (· < k), ((J l).card - 1)) := by
          unfold KH.faceSign
          rw [hJk]
          simp [Finset.filter_insert, Finset.filter_singleton, hab, pow_succ, pow_add]
        erw [hsa, hsb, neg_smul, add_neg_cancel]
      · have hP' := fun h => hP (hface b hb a ha h)
        erw [dif_neg hP, dif_neg hP']
        simp
  ·
    refine Submodule.subset_span ⟨Ideal.Quotient.mk V 1, ⟨t, ht⟩, fun _ => 1, htH, ?_, rfl⟩
    have e : (-(fun _ : K => (1 : ℤ)) + fun k => (((fun _ : K => (1 : ℕ)) k : ℕ) : ℤ)) = fun _ => 0 := by
      funext k; simp
    rw [e]
    refine Submodule.subset_span ⟨1, ⟨fun _ => le_refl 0, ?_⟩, map_one _⟩
    simpa using GeneratedOne.isMultiHomog_one (S := S) (ι := ι)
  ·
    rw [Fin.sum_univ_one, LocalizedModule.mk_mul_mk, OreLocalization.one_def]
    erw [LocalizedModule.mk_eq]
    refine ⟨1, ?_⟩
    simp [Submonoid.smul_def, Algebra.smul_def]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGridSeparation
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

namespace GridSeparation

theorem norm_eval_le_of_torus {e : ℕ} (G : MvPolynomial (Fin e) ℤ) (ζ : Fin e → ℂ) (hζ : ∀ i, ‖ζ i‖ = 1) :
    ‖eval ζ (map (Int.castRingHom ℂ) G)‖ ≤ ∑ d ∈ G.support, ((|G.coeff d| : ℤ) : ℝ) := by
  rw [eval_map, eval₂_eq]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d _ => ?_)
  rw [norm_mul, norm_prod]
  simp [hζ]

theorem grid_finite (e m : ℕ) (hm : 0 < m) : {ζ : Fin e → ℂ | ∀ i, ζ i ^ m = 1}.Finite := by
  have h1 : {x : ℂ | x ^ m = 1}.Finite :=
    (Polynomial.nthRoots m (1 : ℂ)).toFinset.finite_toSet.subset fun x hx => by
      simpa [Polynomial.mem_nthRoots hm] using hx
  convert Set.Finite.pi (t := fun _ : Fin e => {x : ℂ | x ^ m = 1}) fun _ => h1 using 1
  ext ζ
  simp [Set.mem_pi]

theorem norm_of_pow_eq_one {m : ℕ} (hm : 0 < m) {x : ℂ} (hx : x ^ m = 1) : ‖x‖ = 1 :=
  (pow_eq_one_iff_of_nonneg (norm_nonneg x) hm.ne').mp (by rw [← norm_pow, hx, norm_one])

theorem proof (hNL : NormalLocusRep.Statement) (hFN : FibreNormBound.Statement)
    (hRG : RootGridLower.Statement) : GridSeparation.Statement := by
  classical
  intro K _ ι _ Ω _ y D A hV hBir hA
  obtain ⟨df, f, hf, hfP, hrep⟩ := hNL K ι Ω y D hV hBir
  obtain ⟨n, c, B, G, Fib, hn, hB1, hG0, hFib, hnorm⟩ := hFN K ι Ω y D A df f hV hBir hA hf hfP
  set SG : ℝ := ∑ d ∈ G.support, ((|G.coeff d| : ℤ) : ℝ) + 1 with hSG
  have hSG1 : 1 ≤ SG := by
    have : 0 ≤ ∑ d ∈ G.support, ((|G.coeff d| : ℤ) : ℝ) := Finset.sum_nonneg fun d _ => by positivity
    linarith
  have hX : 1 ≤ 2 * B * SG := by nlinarith
  refine ⟨Real.log (2 * B * SG), Real.log_nonneg hX, fun τ => ?_⟩
  set m := G.totalDegree + c * (τ + 1) + 1 with hm
  have hm0 : 0 < m := by omega
  set Z := ((grid_finite (D + 1) m hm0).toFinset.filter
    fun ζ => eval ζ (map (Int.castRingHom ℂ) G) ≠ 0).biUnion Fib with hZ
  have hmem : ∀ ζ : Fin (D + 1) → ℂ, (∀ i, ζ i ^ m = 1) → eval ζ (map (Int.castRingHom ℂ) G) ≠ 0 →
      ∀ z ∈ Fib ζ, z ∈ Z := fun ζ hζ hG z hz =>
    Finset.mem_biUnion.mpr ⟨ζ, Finset.mem_filter.mpr ⟨(Set.Finite.mem_toFinset _).mpr hζ, hG⟩, hz⟩
  have hZpt : ∀ z ∈ Z, z ∈ mcPts (mCoordIdeal y) ∧ eval z (map (Int.castRingHom ℂ) f) ≠ 0 := by
    intro z hz
    obtain ⟨ζ, hζ, hzζ⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨hζg, hGζ⟩ := Finset.mem_filter.mp hζ
    have hζg' : ∀ i, ζ i ^ m = 1 := (Set.Finite.mem_toFinset _).mp hζg
    exact hFib ζ (fun i => norm_of_pow_eq_one hm0 (hζg' i)) hGζ z hzζ
  refine ⟨Z, fun z hz => (hZpt z hz).1, fun s hs z hz => hrep A.a τ s hs z (hZpt z hz).1 (hZpt z hz).2, ?_⟩
  intro u hu hu0
  obtain ⟨F, hF0, hFdeg, hFb⟩ := hnorm τ u hu hu0
  by_contra hcon
  obtain ⟨ζ, hζm, hζ1⟩ := hRG (D + 1) m (G * F) (mul_ne_zero hG0 hF0) fun i => by
    have h1 := degreeOf_mul_le i G F
    have h2 := degreeOf_le_totalDegree G i
    have h3 := hFdeg i
    omega
  have hζn : ∀ i, ‖ζ i‖ = 1 := fun i => norm_of_pow_eq_one hm0 (hζm i)
  rw [map_mul, eval_mul, norm_mul] at hζ1
  have hGζ : eval ζ (map (Int.castRingHom ℂ) G) ≠ 0 := by
    intro h
    rw [h, norm_zero, zero_mul] at hζ1
    linarith
  set E := Real.exp (-(Real.log (2 * B * SG) * ((τ : ℝ) + 1))) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hFle := hFb ζ hζn hGζ E hE0.le fun z hz => by
    obtain ⟨dg, dh, g, h, hg, hh, hd, hy, hz0⟩ :=
      hrep A.a τ u hu z (hFib ζ hζn hGζ z hz).1 (hFib ζ hζn hGζ z hz).2
    refine ⟨dg, dh, g, h, hg, hh, hd, hy, hz0, ?_⟩
    by_contra hlt
    exact hcon ⟨z, hmem ζ hζm hGζ z hz, dg, dh, g, h, hg, hh, hd, hy, hz0, (not_le.mp hlt).le⟩
  have hEX : E * (2 * B * SG) ^ (τ + 1) = 1 := by
    have : -(Real.log (2 * B * SG) * ((τ : ℝ) + 1)) = ((τ + 1 : ℕ) : ℝ) * (-Real.log (2 * B * SG)) := by
      push_cast
      ring
    rw [hE, this, Real.exp_nat_mul, Real.exp_neg, Real.exp_log (by linarith), ← mul_pow,
      inv_mul_cancel₀ (by linarith), one_pow]
  have hE1 : E ≤ 1 := by
    have : 1 ≤ (2 * B * SG) ^ (τ + 1) := one_le_pow₀ hX
    nlinarith
  have hEn : E ^ n ≤ E := pow_le_of_le_one hE0.le hE1 (by omega)
  have hGle : ‖eval ζ (map (Int.castRingHom ℂ) G)‖ ≤ SG := by
    have := norm_eval_le_of_torus G ζ hζn
    linarith
  have hpow : 2 * SG * B ^ (τ + 1) ≤ (2 * B * SG) ^ (τ + 1) := by
    rw [show 2 * B * SG = (2 * SG) * B by ring, mul_pow]
    have hB0 : 0 ≤ B ^ (τ + 1) := pow_nonneg (by linarith) _
    have : 2 * SG ≤ (2 * SG) ^ (τ + 1) := le_self_pow₀ (by linarith) (by omega)
    nlinarith
  have hBp : 0 ≤ B ^ (τ + 1) := pow_nonneg (by linarith) _
  have hFn : ‖eval ζ (map (Int.castRingHom ℂ) F)‖ ≤ B ^ (τ + 1) * E := by
    calc _ ≤ B ^ (τ + 1) * E ^ n := hFle
      _ ≤ B ^ (τ + 1) * E := mul_le_mul_of_nonneg_left hEn hBp
  have key : 2 * (SG * (B ^ (τ + 1) * E)) ≤ 1 := by
    calc 2 * (SG * (B ^ (τ + 1) * E)) = (2 * SG * B ^ (τ + 1)) * E := by ring
      _ ≤ (2 * B * SG) ^ (τ + 1) * E := mul_le_mul_of_nonneg_right hpow hE0.le
      _ = 1 := by rw [mul_comm, hEX]
  have hFnn : 0 ≤ ‖eval ζ (map (Int.castRingHom ℂ) F)‖ := norm_nonneg _
  have : ‖eval ζ (map (Int.castRingHom ℂ) G)‖ * ‖eval ζ (map (Int.castRingHom ℂ) F)‖ ≤
      SG * (B ^ (τ + 1) * E) :=
    mul_le_mul hGle hFn hFnn (by linarith)
  linarith

end GridSeparation

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PHilbFnValueSpan
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace HilbFnValueSpan

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {Ω : Type} [Field Ω] [CharZero Ω]

def coneQ (y : (Σ k, ι k) → Ω) : MvPolynomial (Σ k, ι k) ℚ →ₐ[ℚ] MvPolynomial K Ω :=
  aeval fun p => MvPolynomial.C (y p) * MvPolynomial.X p.1

omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] in

theorem map_mCoordIdeal (y : (Σ k, ι k) → Ω) :
    (mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ)) = RingHom.ker (coneQ y) := by
  have hring : ((coneQ y : MvPolynomial (Σ k, ι k) ℚ →+* MvPolynomial K Ω).comp
      (MvPolynomial.map (Int.castRingHom ℚ))) = (mConeMap y : MRing ι →+* MvPolynomial K Ω) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [coneQ, mConeMap]
    · intro i
      simp [coneQ, mConeMap]
  have hker : mCoordIdeal y =
      (RingHom.ker (coneQ y)).comap (MvPolynomial.map (Int.castRingHom ℚ)) := by
    ext f
    rw [Ideal.mem_comap]
    simp only [mCoordIdeal, RingHom.mem_ker]
    have h := RingHom.congr_fun hring f
    simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe] at h
    rw [h]
  let _ := MvPolynomial.algebraMvPolynomial (σ := Σ k, ι k) (R := ℤ) (S := ℚ)
  have e : algebraMap (MvPolynomial (Σ k, ι k) ℤ) (MvPolynomial (Σ k, ι k) ℚ) =
      MvPolynomial.map (Int.castRingHom ℚ) := by
    rw [MvPolynomial.algebraMap_def, algebraMap_int_eq]
  have h := IsLocalization.map_under ((nonZeroDivisors ℤ).map (C (σ := Σ k, ι k)))
    (MvPolynomial (Σ k, ι k) ℚ) (RingHom.ker (coneQ y))
  rw [e] at h
  rw [hker]
  exact h

theorem weight_blockWeight (m : (Σ k, ι k) →₀ ℕ) (k : K) :
    Finsupp.weight (NumbersDVR.blockWeight ι) m k = ∑ i, m ⟨k, i⟩ := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_sigma]
  simp [NumbersDVR.blockWeight, Pi.single_apply]

theorem isWeightedHomogeneous_iff {R : Type} [CommRing R] (f : MvPolynomial (Σ k, ι k) R) (a : K → ℕ) :
    IsWeightedHomogeneous (NumbersDVR.blockWeight ι) f a ↔ ∀ m ∈ f.support, ∀ k, ∑ i, m ⟨k, i⟩ = a k := by
  constructor
  · intro h m hm k
    rw [← weight_blockWeight, h (mem_support_iff.mp hm)]
  · intro h m hm
    funext k
    rw [weight_blockWeight, h m (mem_support_iff.mpr hm) k]

theorem coneQ_eq (y : (Σ k, ι k) → Ω) {f : MvPolynomial (Σ k, ι k) ℚ} {a : K → ℕ}
    (hf : IsWeightedHomogeneous (NumbersDVR.blockWeight ι) f a) :
    coneQ y f = MvPolynomial.C (aeval y f) * ∏ k, MvPolynomial.X k ^ a k := by
  have hf' := (isWeightedHomogeneous_iff f a).mp hf
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  rw [map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hX : ∏ p : (Σ k, ι k), (MvPolynomial.X p.1 : MvPolynomial K Ω) ^ m p =
      ∏ k, MvPolynomial.X k ^ a k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, (MvPolynomial.X k : MvPolynomial K Ω) ^ m ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hf' m hm k]
  simp only [coneQ, aeval_monomial]
  rw [Finsupp.prod_fintype _ _ (fun i => by simp), Finsupp.prod_fintype _ _ (fun i => by simp)]
  simp only [mul_pow, Finset.prod_mul_distrib, hX, map_mul, map_prod, map_pow,
    MvPolynomial.algebraMap_apply]
  ring

theorem mem_ker_iff (y : (Σ k, ι k) → Ω) {f : MvPolynomial (Σ k, ι k) ℚ} {a : K → ℕ}
    (hf : IsWeightedHomogeneous (NumbersDVR.blockWeight ι) f a) :
    f ∈ RingHom.ker (coneQ y) ↔ aeval y f = 0 := by
  rw [RingHom.mem_ker, coneQ_eq y hf]
  constructor
  · intro h
    have hne : (∏ k, MvPolynomial.X k ^ a k : MvPolynomial K Ω) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (X_ne_zero k)
    rcases mul_eq_zero.mp h with h | h
    · exact MvPolynomial.C_eq_zero.mp h
    · exact absurd h hne
  · intro h
    rw [h, map_zero, zero_mul]

def evalForms (y : (Σ k, ι k) → Ω) (a : K → ℕ) :
    weightedHomogeneousSubmodule ℚ (NumbersDVR.blockWeight ι) a →ₗ[ℚ] Ω :=
  (aeval y : MvPolynomial (Σ k, ι k) ℚ →ₐ[ℚ] Ω).toLinearMap.comp (Submodule.subtype _)

def quotForms (P : Ideal (MvPolynomial (Σ k, ι k) ℚ)) (a : K → ℕ) :
    weightedHomogeneousSubmodule ℚ (NumbersDVR.blockWeight ι) a →ₗ[ℚ] MvPolynomial (Σ k, ι k) ℚ ⧸ P :=
  (Ideal.Quotient.mkₐ ℚ P).toLinearMap.comp (Submodule.subtype _)

theorem range_evalForms (y : (Σ k, ι k) → Ω) (a : K → ℕ) :
    LinearMap.range (evalForms y a) = valueSpan y a := by
  apply le_antisymm
  · rintro _ ⟨⟨f, hf⟩, rfl⟩
    have hf' := (isWeightedHomogeneous_iff f a).mp ((mem_weightedHomogeneousSubmodule _ _ _ _).mp hf)
    show aeval y f ∈ valueSpan y a
    conv => arg 2; rw [f.as_sum]
    rw [map_sum]
    refine Submodule.sum_mem _ fun v hv => ?_
    have hmon : aeval y (monomial v (coeff v f)) =
        coeff v f • aeval y (monomial v (1 : ℤ) : MRing ι) := by
      simp only [aeval_monomial, Algebra.smul_def, map_one, one_mul]
    rw [hmon]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨monomial v 1, ?_, rfl⟩)
    intro m hm k
    rw [support_monomial, if_neg one_ne_zero, Finset.mem_singleton] at hm
    rw [hm]
    exact hf' v hv k
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨g, hg, rfl⟩
    have hmem : MvPolynomial.map (Int.castRingHom ℚ) g ∈
        weightedHomogeneousSubmodule ℚ (NumbersDVR.blockWeight ι) a := by
      rw [mem_weightedHomogeneousSubmodule, isWeightedHomogeneous_iff]
      exact fun m hm k => hg m (support_map_subset _ _ hm) k
    refine ⟨⟨_, hmem⟩, ?_⟩
    show aeval y (MvPolynomial.map (Int.castRingHom ℚ) g) = aeval y g
    rw [← algebraMap_int_eq, aeval_map_algebraMap]

theorem finrank_gradedPiece (y : (Σ k, ι k) → Ω) (a : K → ℕ) :
    Module.finrank ℚ (NumbersDVR.gradedPiece
        ((mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ))) a) =
      Module.finrank ℚ (valueSpan y a) := by
  set P := (mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ))
  have hrange : LinearMap.range (quotForms P a) = NumbersDVR.gradedPiece P a := by
    rw [quotForms, LinearMap.range_comp, Submodule.range_subtype]
    rfl
  have hker : LinearMap.ker (quotForms P a) = LinearMap.ker (evalForms y a) := by
    ext ⟨f, hf⟩
    rw [mem_weightedHomogeneousSubmodule] at hf
    simp only [LinearMap.mem_ker, quotForms, evalForms, LinearMap.coe_comp, Function.comp_apply,
      Submodule.coe_subtype, AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem]
    rw [show P = RingHom.ker (coneQ y) from map_mCoordIdeal y, mem_ker_iff y hf]
  rw [← hrange, ← range_evalForms y a, ← (quotForms P a).quotKerEquivRange.finrank_eq,
    ← (evalForms y a).quotKerEquivRange.finrank_eq]
  exact (Submodule.quotEquivOfEq _ _ hker).finrank_eq

end HilbFnValueSpan

theorem HilbFnValueSpan.proof : HilbFnValueSpan.Statement := by
  intro K _ _ ι _ Ω _ _ y a
  unfold NumbersDVR.hilbFn
  rw [if_pos (fun k => Int.natCast_nonneg _)]
  have ha : (fun k => ((a k : ℤ)).toNat) = a := funext fun k => Int.toNat_natCast _
  rw [ha, HilbFnValueSpan.finrank_gradedPiece]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMetricToFS
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

theorem MetricToFS.proof (hE : PullFSExtension.Statement) (hC : DefectMetricChange.Statement) :
    MetricToFS.Statement := by
  intro D Ω _ _ κ _ I d e hI hF
  obtain ⟨m₀, hs, hc, hp, hpull⟩ := hE D Ω κ d.x e hF
  exact ⟨d.withMetric m₀ ⊥ hs hc bot_le hp, rfl, hpull,
    hC D Ω κ I d m₀ ⊥ hs hc bot_le hp e hI hF⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

