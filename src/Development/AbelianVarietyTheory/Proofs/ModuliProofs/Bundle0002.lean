import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.EntireAntilinearLatticePeriodsConst
section
open Complex Matrix
open scoped ContDiff BigOperators Real

namespace GlobalTheory

theorem eq_zero_of_norm_real_mul_le {c : ℂ} {C : ℝ} (h : ∀ r : ℝ, ‖(r : ℂ) * c‖ ≤ C) : c = 0 := by
  by_contra hc
  have hpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have h0 : 0 ≤ C := (norm_nonneg _).trans (h 0)
  have key := h ((C + 1) / ‖c‖)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (by linarith) hpos.le), div_mul_cancel₀ _ hpos.ne'] at key
  linarith

theorem entire_sub_conj_bounded_const {φ : ℂ → ℂ} {b : ℂ} {C : ℝ} (hφ : Differentiable ℂ φ)
    (h : ∀ s, ‖φ s - (starRingEnd ℂ) s * b‖ ≤ C) : b = 0 ∧ ∀ s, φ s = φ 0 := by

  have hshift : ∀ a s, φ (s + a) - φ s = φ a - φ 0 := by
    intro a
    have hd : Differentiable ℂ (fun s => φ (s + a) - φ s) :=
      (hφ.comp (differentiable_id.add_const a)).sub hφ
    have hbd : Bornology.IsBounded (Set.range (fun s => φ (s + a) - φ s)) := by
      rw [isBounded_iff_forall_norm_le]
      refine ⟨2 * C + ‖(starRingEnd ℂ) a * b‖, ?_⟩
      rintro _ ⟨s, rfl⟩
      show ‖φ (s + a) - φ s‖ ≤ _
      have e : φ (s + a) - φ s = ((φ (s + a) - (starRingEnd ℂ) (s + a) * b)
          - (φ s - (starRingEnd ℂ) s * b)) + (starRingEnd ℂ) a * b := by
        rw [map_add]; ring
      rw [e]
      calc _ ≤ ‖(φ (s + a) - (starRingEnd ℂ) (s + a) * b) - (φ s - (starRingEnd ℂ) s * b)‖
            + ‖(starRingEnd ℂ) a * b‖ := norm_add_le _ _
        _ ≤ (‖φ (s + a) - (starRingEnd ℂ) (s + a) * b‖ + ‖φ s - (starRingEnd ℂ) s * b‖)
            + ‖(starRingEnd ℂ) a * b‖ := by gcongr; exact norm_sub_le _ _
        _ ≤ _ := by linarith [h (s + a), h s]
    intro s
    simpa [zero_add] using hd.apply_eq_apply_of_bounded hbd s 0

  have hderiv : ∀ s, deriv φ s = deriv φ 0 := by
    intro s
    have e1 : (fun x => φ (x + s)) = fun x => φ x + (φ s - φ 0) := by
      funext x
      linear_combination hshift s x
    have e2 := congrArg (fun f => deriv f 0) e1
    simp only [deriv_comp_add_const, deriv_add_const, zero_add] at e2
    exact e2

  obtain ⟨β, hlin⟩ : ∃ β : ℂ, ∀ s, φ s = φ 0 + β * s := by
    refine ⟨deriv φ 0, fun s => ?_⟩
    have hd : Differentiable ℂ (fun s => φ s - deriv φ 0 * s) :=
      hφ.sub (differentiable_id.const_mul _)
    have hz : ∀ x, deriv (fun s => φ s - deriv φ 0 * s) x = 0 := by
      intro x
      have hx : HasDerivAt (fun s => φ s - deriv φ 0 * s) (deriv φ x - deriv φ 0 * 1) x :=
        (hφ x).hasDerivAt.sub ((hasDerivAt_id' x).const_mul _)
      rw [hx.deriv, hderiv x]
      ring
    have := is_const_of_deriv_eq_zero hd hz s 0
    linear_combination this

  have hB : ∀ s, ‖β * s - (starRingEnd ℂ) s * b‖ ≤ C + ‖φ 0‖ := by
    intro s
    have e : β * s - (starRingEnd ℂ) s * b = (φ s - (starRingEnd ℂ) s * b) - φ 0 := by
      rw [hlin s]; ring
    rw [e]
    exact (norm_sub_le _ _).trans (by linarith [h s])
  have h1 : β - b = 0 := eq_zero_of_norm_real_mul_le (C := C + ‖φ 0‖) fun r => by
    have hr := hB r
    rw [Complex.conj_ofReal] at hr
    calc ‖(r : ℂ) * (β - b)‖ = ‖β * (r : ℂ) - (r : ℂ) * b‖ := by congr 1; ring
      _ ≤ _ := hr
  have h2 : Complex.I * (β + b) = 0 := eq_zero_of_norm_real_mul_le (C := C + ‖φ 0‖) fun r => by
    have hr := hB (r * Complex.I)
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I] at hr
    calc ‖(r : ℂ) * (Complex.I * (β + b))‖
        = ‖β * ((r : ℂ) * Complex.I) - (r : ℂ) * -Complex.I * b‖ := by congr 1; ring
      _ ≤ _ := hr
  have h3 : β + b = 0 := (mul_eq_zero.mp h2).resolve_left Complex.I_ne_zero
  have hβ : β = 0 := by linear_combination (h1 + h3) / 2
  refine ⟨by linear_combination (h3 - h1) / 2, fun s => ?_⟩
  rw [hlin s, hβ, zero_mul, add_zero]

theorem entire_antilinear_periods_const :
    ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ →
      Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
      ∀ (v : (Fin g → ℂ) → ℂ) (t : (Fin g → ℂ)), Differentiable ℂ v →
        (∀ (l : Λ) z, v (z + l) = v z + t ⬝ᵥ star (l : (Fin g → ℂ))) →
        t = 0 ∧ ∀ z, v z = v 0 := by
  intro g Λ hdisc hspan v t hv hper
  have : IsZLattice ℝ Λ := ⟨hspan⟩

  have hcont : Continuous (fun z => v z - t ⬝ᵥ star z) :=
    hv.continuous.sub (continuous_const.dotProduct continuous_star)
  have hperw : ∀ z w, w ∈ Λ → (fun z => v z - t ⬝ᵥ star z) (z + w) = (fun z => v z - t ⬝ᵥ star z) z := by
    intro z w hw
    simp only
    rw [hper ⟨w, hw⟩ z, star_add, dotProduct_add]
    ring
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp
    (IsZLattice.isCompact_range_of_periodic Λ _ hcont hperw).isBounded

  have hline : ∀ d : Fin g → ℂ, t ⬝ᵥ star d = 0 ∧ ∀ s : ℂ, v (s • d) = v 0 := by
    intro d
    have hd : Differentiable ℂ (fun s : ℂ => v (s • d)) :=
      hv.comp (differentiable_id.smul_const d)
    have hb : ∀ s : ℂ, ‖v (s • d) - (starRingEnd ℂ) s * (t ⬝ᵥ star d)‖ ≤ M := by
      intro s
      have e : (starRingEnd ℂ) s * (t ⬝ᵥ star d) = t ⬝ᵥ star (s • d) := by
        rw [star_smul, dotProduct_smul, smul_eq_mul, starRingEnd_apply]
      rw [e]
      exact hM _ ⟨s • d, rfl⟩
    obtain ⟨h1, h2⟩ := entire_sub_conj_bounded_const hd hb
    exact ⟨h1, fun s => by simpa using h2 s⟩
  refine ⟨?_, fun z => by simpa using (hline z).2 1⟩
  funext i
  have hi := (hline (Pi.single i 1)).1
  rw [← Pi.single_star, star_one, dotProduct_single, mul_one] at hi
  simpa using hi

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.Imports
section
namespace GlobalTheory.AnalyticLineDerivative

open MvPolynomial

universe u_1 u_2 u_3 u_4

theorem hasDerivAt_line {S : Type*} {J : Type*} [CommRing S] [Fintype J] (φ : S →+* ℂ)
    (u v : J → ℂ) (p : MvPolynomial J S) :
    HasDerivAt (fun t : ℂ => eval₂Hom φ (u + t • v) p)
      (∑ j, v j * eval₂Hom φ u (pderiv j p)) 0 := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp only [eval₂Hom_C, pderiv_C, map_zero, mul_zero, Finset.sum_const_zero]
    exact hasDerivAt_const _ _
  | add p q hp hq =>
    simp only [map_add, mul_add, Finset.sum_add_distrib]
    exact hp.add hq
  | mul_X p i hp =>
    have hlin : HasDerivAt (fun t : ℂ => u i + t * v i) (v i) 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).mul_const (v i)).const_add (u i)
    have hX : ∀ j, eval₂Hom φ u (pderiv j (X i : MvPolynomial J S)) = if j = i then 1 else 0 := by
      intro j
      by_cases h : j = i
      · subst h; simp [pderiv_X]
      · simp [pderiv_X, h, Ne.symm h]

    have key : ∀ j, v j * eval₂Hom φ u (pderiv j (p * X i)) =
        (if j = i then v i * eval₂Hom φ u p else 0) + v j * eval₂Hom φ u (pderiv j p) * u i := by
      intro j
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul, eval₂Hom_X', hX]
      split_ifs with h
      · subst h; ring
      · ring
    simp only [map_mul, eval₂Hom_X', Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    refine (hp.mul hlin).congr_deriv ?_
    rw [Finset.sum_congr rfl fun j _ => key j, Finset.sum_add_distrib, ← Finset.sum_mul]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, zero_smul,
      add_zero, zero_mul]
    ring

theorem analyticAt_eval {E : Type*} {S : Type*} {J : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CommRing S] [Fintype J] (χ : E → S →+* ℂ) (z₀ : E) (u₀ : J → ℂ)
    (h : ∀ a : S, AnalyticAt ℂ (fun z : E => χ z a) z₀) (p : MvPolynomial J S) :
    AnalyticAt ℂ (fun w : E × (J → ℂ) => eval₂Hom (χ w.1) w.2 p) (z₀, u₀) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp only [eval₂Hom_C]
    exact (h a).comp_of_eq analyticAt_fst rfl
  | add p q hp hq =>
    simp only [map_add]
    exact hp.add hq
  | mul_X p i hp =>
    simp only [map_mul, eval₂Hom_X']
    exact hp.mul (((ContinuousLinearMap.proj i).comp
      (ContinuousLinearMap.snd ℂ E (J → ℂ))).analyticAt _)

theorem main {E : Type u_1} {S : Type u_2} {J : Type u_3} {σ : Type u_4}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] [CommRing S] [Fintype J]
    [Fintype σ] [DecidableEq σ] (χ : E → S →+* ℂ) (rel : σ → MvPolynomial J S) (c : σ → J)
    (hc : Function.Bijective c) (z₀ : E) (u₀ : J → ℂ)
    (han : ∀ a : S, AnalyticAt ℂ (fun z : E => χ z a) z₀)
    (hdet : Matrix.det (Matrix.of fun s r : σ =>
      eval₂Hom (χ z₀) u₀ (pderiv (c s) (rel r))) ≠ 0) :
    ∃ Φ : OpenPartialHomeomorph (E × (J → ℂ)) (E × (σ → ℂ)),
      (∀ w : E × (J → ℂ), Φ w = (w.1, fun r : σ => eval₂Hom (χ w.1) w.2 (rel r))) ∧
        (z₀, u₀) ∈ Φ.source ∧ AnalyticOnNhd ℂ Φ.symm Φ.target := by
  classical
  have : CompleteSpace E := FiniteDimensional.complete ℂ E
  set G : E × (J → ℂ) → (σ → ℂ) := fun w r => eval₂Hom (χ w.1) w.2 (rel r)
  set F : E × (J → ℂ) → E × (σ → ℂ) := fun w => (w.1, G w)
  set a₀ : E × (J → ℂ) := (z₀, u₀)
  have hGan : AnalyticAt ℂ G a₀ := AnalyticAt.pi fun r => analyticAt_eval χ z₀ u₀ han (rel r)
  have hFan : AnalyticAt ℂ F a₀ := analyticAt_fst.prod hGan
  have hGd : HasFDerivAt G (fderiv ℂ G a₀) a₀ := hGan.differentiableAt.hasFDerivAt

  have hdirG : ∀ v : J → ℂ, fderiv ℂ G a₀ (0, v) =
      fun r => ∑ j, v j * eval₂Hom (χ z₀) u₀ (pderiv j (rel r)) := by
    intro v
    have hℓ : HasDerivAt (fun t : ℂ => ((z₀, u₀ + t • v) : E × (J → ℂ))) ((0 : E), (1 : ℂ) • v) 0 :=
      (hasDerivAt_const (0 : ℂ) z₀).prodMk (((hasDerivAt_id (0 : ℂ)).smul_const v).const_add u₀)
    have hcomp := hGd.comp_hasDerivAt_of_eq 0 hℓ (by simp [a₀])
    rw [one_smul] at hcomp
    funext r
    exact ((hasDerivAt_pi.mp hcomp) r).unique (hasDerivAt_line (χ z₀) u₀ v (rel r))
  set L : E × (J → ℂ) →L[ℂ] E × (σ → ℂ) :=
    (ContinuousLinearMap.fst ℂ E (J → ℂ)).prod (fderiv ℂ G a₀)
  have hFd : HasFDerivAt F L a₀ := hasFDerivAt_fst.prodMk hGd

  have hLinj : Function.Injective L := by
    refine (injective_iff_map_eq_zero L).mpr ?_
    rintro ⟨h, v⟩ hw
    have hh : h = 0 := by simpa [L] using congrArg Prod.fst hw
    subst hh
    have hv : fderiv ℂ G a₀ (0, v) = 0 := by simpa [L] using congrArg Prod.snd hw
    rw [hdirG] at hv
    have hzero : Matrix.vecMul (fun s => v (c s))
        (Matrix.of fun s r : σ => eval₂Hom (χ z₀) u₀ (pderiv (c s) (rel r))) = 0 := by
      funext r
      have hr := congrFun hv r
      simp only [Pi.zero_apply] at hr ⊢
      rw [← hr]
      simp only [Matrix.vecMul, dotProduct, Matrix.of_apply]
      exact (Equiv.ofBijective c hc).sum_comp
        (fun j => v j * eval₂Hom (χ z₀) u₀ (pderiv j (rel r)))
    have hvc : (fun s => v (c s)) = 0 := by
      by_contra hne
      exact hdet (Matrix.exists_vecMul_eq_zero_iff.mp ⟨_, hne, hzero⟩)
    have hv0 : v = 0 := by
      funext j
      obtain ⟨s, rfl⟩ := hc.2 j
      exact congrFun hvc s
    subst hv0
    rfl
  have hrank : Module.finrank ℂ (E × (J → ℂ)) = Module.finrank ℂ (E × (σ → ℂ)) := by
    simp [Module.finrank_prod, Fintype.card_of_bijective hc]
  have hLsurj : Function.Surjective L :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank
      (f := (L : E × (J → ℂ) →ₗ[ℂ] E × (σ → ℂ)))).mp hLinj
  let i : (E × (J → ℂ)) ≃L[ℂ] (E × (σ → ℂ)) :=
    (LinearEquiv.ofBijective (L : E × (J → ℂ) →ₗ[ℂ] E × (σ → ℂ))
      ⟨hLinj, hLsurj⟩).toContinuousLinearEquiv
  have hi : (i : E × (J → ℂ) →L[ℂ] E × (σ → ℂ)) = L := ContinuousLinearMap.ext fun _ => rfl
  have hstrict : HasStrictFDerivAt F (i : E × (J → ℂ) →L[ℂ] E × (σ → ℂ)) a₀ := by
    rw [hi, ← hFd.fderiv]
    exact hFan.hasStrictFDerivAt

  have hev : ∀ᶠ w in nhds a₀, AnalyticAt ℂ F w ∧
      ∃ j : (E × (J → ℂ)) ≃L[ℂ] (E × (σ → ℂ)), fderiv ℂ F w = j := by
    refine hFan.eventually_analyticAt.and ?_
    have hmem : fderiv ℂ F a₀ ∈
        Set.range ((↑) : ((E × (J → ℂ)) ≃L[ℂ] (E × (σ → ℂ))) → E × (J → ℂ) →L[ℂ] E × (σ → ℂ)) :=
      ⟨i, by rw [hi, hFd.fderiv]⟩
    refine (hFan.fderiv.continuousAt.eventually_mem
      (ContinuousLinearEquiv.isOpen.mem_nhds hmem)).mono fun w hw => ?_
    obtain ⟨j, hj⟩ := hw
    exact ⟨j, hj.symm⟩
  obtain ⟨U, hUsub, hUopen, ha₀U⟩ := mem_nhds_iff.mp hev
  refine ⟨(hstrict.toOpenPartialHomeomorph F).restrOpen U hUopen, fun w => rfl, ?_, ?_⟩
  · rw [OpenPartialHomeomorph.restrOpen_source]
    exact ⟨hstrict.mem_toOpenPartialHomeomorph_source, ha₀U⟩
  · intro b hb
    have hsrc := ((hstrict.toOpenPartialHomeomorph F).restrOpen U hUopen).map_target hb
    rw [OpenPartialHomeomorph.restrOpen_source] at hsrc
    obtain ⟨hA, j, hj⟩ := hUsub hsrc.2
    exact ((hstrict.toOpenPartialHomeomorph F).restrOpen U hUopen).analyticAt_symm hb hA hj

end GlobalTheory.AnalyticLineDerivative
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IntOfPrimeMulSq
section
namespace GlobalTheory.RationalIntegralCoordinates

theorem exists_coords {d : ℕ} (hd : 0 < d) {r : ℂ} (hr : r ^ 2 = -(d : ℂ)) {z : ℂ}
    (hzK : z ∈ IntermediateField.adjoin ℚ ({r} : Set ℂ)) :
    ∃ a b : ℚ, z = (a : ℂ) + (b : ℂ) * r := by
  have hint : IsIntegral ℚ r := by
    refine ⟨Polynomial.X ^ 2 + Polynomial.C (d : ℚ), Polynomial.monic_X_pow_add_C _ two_ne_zero, ?_⟩
    simp [hr]
  rw [← IntermediateField.mem_toSubalgebra,
    IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic] at hzK
  induction hzK using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    exact ⟨0, 1, by simp [hx]⟩
  | algebraMap q => exact ⟨q, 0, by simp [eq_ratCast]⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, b, rfl⟩ := hx
    obtain ⟨c, e, rfl⟩ := hy
    exact ⟨a + c, b + e, by push_cast; ring⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, b, rfl⟩ := hx
    obtain ⟨c, e, rfl⟩ := hy
    refine ⟨a * c - d * b * e, a * e + b * c, ?_⟩
    push_cast
    linear_combination (b : ℂ) * e * hr

theorem conj_eq_neg {d : ℕ} (hd : 0 < d) {r : ℂ} (hr : r ^ 2 = -(d : ℂ)) :
    (starRingEnd ℂ) r = -r := by
  have h1 := congrArg Complex.re hr
  have h2 := congrArg Complex.im hr
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.natCast_re, Complex.natCast_im, neg_zero] at h1 h2
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hre : r.re = 0 := by
    by_contra hne
    have him : r.im = 0 := by
      have hprod : r.re * r.im = 0 := by linarith
      rcases mul_eq_zero.mp hprod with h | h
      · exact absurd h hne
      · exact h
    rw [him] at h1
    nlinarith [mul_self_nonneg r.re]
  apply Complex.ext <;> simp [hre]

theorem rat_int {q : ℚ} (h : IsIntegral ℤ (q : ℂ)) : ∃ m : ℤ, (m : ℚ) = q := by
  have hq : IsIntegral ℤ q := by
    have hinj : Function.Injective (algebraMap ℚ ℂ).toIntAlgHom := (algebraMap ℚ ℂ).injective
    rw [← isIntegral_algHom_iff _ hinj]
    simpa [eq_ratCast] using h
  obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.mp hq
  exact ⟨m, by simpa using hm⟩

theorem int_of_prime_mul_sq {d : ℕ} (hd : d.Prime) {q : ℚ} {n : ℤ}
    (h : (d : ℚ) * q ^ 2 = n) : ∃ k : ℤ, (k : ℚ) = q := by
  have hden : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have hz : (d : ℤ) * q.num ^ 2 = (q.den : ℤ) ^ 2 * n := by
    have hq : q = q.num / q.den := (Rat.num_div_den q).symm
    rw [hq, div_pow] at h
    field_simp at h
    exact_mod_cast h
  have hcop : IsCoprime ((q.den : ℤ) ^ 2) (q.num ^ 2) := by
    apply IsCoprime.pow
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]
    exact q.reduced
  have hdvd : (q.den : ℤ) ^ 2 ∣ d := hcop.dvd_of_dvd_mul_right ⟨n, hz⟩
  have hdvd' : q.den ∣ d := by
    have : q.den ^ 2 ∣ d := by exact_mod_cast hdvd
    exact (dvd_pow_self _ two_ne_zero).trans this
  rcases hd.eq_one_or_self_of_dvd _ hdvd' with h1 | h1
  · exact ⟨q.num, by rw [← Rat.den_eq_one_iff]; exact h1⟩
  · exfalso
    have h2 : q.den ^ 2 ∣ d := by exact_mod_cast hdvd
    rw [h1] at h2
    have h3 := Nat.le_of_dvd hd.pos h2
    have h4 := hd.two_le
    nlinarith

theorem main {d : ℕ} (hd : Nat.Prime d) (hd4 : d % 4 = 3) {r : ℂ} (hr : r ^ 2 = -(d : ℂ))
    (T : Subring ℂ) (hT : (1 + r) / 2 ∈ T) {z : ℂ}
    (hzK : z ∈ IntermediateField.adjoin ℚ ({r} : Set ℂ)) (hz : IsIntegral ℤ z) : z ∈ T := by
  have hd0 : 0 < d := hd.pos
  obtain ⟨a, b, rfl⟩ := exists_coords hd0 hr hzK
  have hc : starRingEnd ℂ ((a : ℂ) + b * r) = a - b * r := by
    rw [map_add, map_mul, conj_eq_neg hd0 hr, map_ratCast, map_ratCast]
    ring
  have hcz : IsIntegral ℤ (starRingEnd ℂ ((a : ℂ) + b * r)) := hz.map (starRingEnd ℂ).toIntAlgHom
  have htr : IsIntegral ℤ (((2 * a : ℚ)) : ℂ) := by
    have e : (((2 * a : ℚ)) : ℂ) = ((a : ℂ) + b * r) + starRingEnd ℂ ((a : ℂ) + b * r) := by
      rw [hc]
      push_cast
      ring
    rw [e]
    exact hz.add hcz
  have hnm : IsIntegral ℤ (((a ^ 2 + d * b ^ 2 : ℚ)) : ℂ) := by
    have e : (((a ^ 2 + d * b ^ 2 : ℚ)) : ℂ) =
        ((a : ℂ) + b * r) * starRingEnd ℂ ((a : ℂ) + b * r) := by
      rw [hc]
      push_cast
      linear_combination (b : ℂ) ^ 2 * hr
    rw [e]
    exact hz.mul hcz
  obtain ⟨m, hm⟩ := rat_int htr
  obtain ⟨N, hN⟩ := rat_int hnm
  obtain ⟨k, hk⟩ := int_of_prime_mul_sq hd (q := 2 * b) (n := 4 * N - m ^ 2) (by
    push_cast
    rw [hm, hN]
    ring)
  have heq : m ^ 2 + (d : ℤ) * k ^ 2 = 4 * N := by
    have : ((m ^ 2 + (d : ℤ) * k ^ 2 : ℤ) : ℚ) = ((4 * N : ℤ) : ℚ) := by
      push_cast
      rw [hm, hk, hN]
      ring
    exact_mod_cast this
  obtain ⟨t, ht⟩ : ∃ t : ℤ, (d : ℤ) = 4 * t + 3 := ⟨(d / 4 : ℕ), by omega⟩
  obtain ⟨j, hj⟩ : ∃ j : ℤ, m - k = 2 * j := by
    obtain ⟨u, hu | hu⟩ := Int.even_or_odd' m <;> obtain ⟨v, hv | hv⟩ := Int.even_or_odd' k
    · exact ⟨u - v, by omega⟩
    · exfalso
      obtain ⟨X, hX⟩ : ∃ X : ℤ, (d : ℤ) = 4 * X :=
        ⟨N - u ^ 2 - d * (v ^ 2 + v), by rw [hu, hv] at heq; linear_combination heq⟩
      omega
    · exfalso
      obtain ⟨X, hX⟩ : ∃ X : ℤ, (1 : ℤ) = 4 * X :=
        ⟨N - u ^ 2 - u - d * v ^ 2, by rw [hu, hv] at heq; linear_combination heq⟩
      omega
    · exact ⟨u - v, by omega⟩
  have hm' : (m : ℂ) = 2 * a := by exact_mod_cast congrArg (fun x : ℚ => (x : ℂ)) hm
  have hk' : (k : ℂ) = 2 * b := by exact_mod_cast congrArg (fun x : ℚ => (x : ℂ)) hk
  have hj' : (m : ℂ) - k = 2 * j := by exact_mod_cast hj
  have hsplit : (a : ℂ) + b * r = (j : ℂ) + (k : ℂ) * ((1 + r) / 2) := by
    linear_combination (-1 / 2 : ℂ) * hm' + (-r / 2) * hk' + (1 / 2 : ℂ) * hj'
  rw [hsplit]
  exact T.add_mem (intCast_mem T j) (T.mul_mem (intCast_mem T k) hT)

end GlobalTheory.RationalIntegralCoordinates
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.MemMapKerOfOneTmulEqZeroOfFlat
section
open scoped TensorProduct

namespace GlobalTheory

theorem mem_map_ker_of_one_tmul_eq_zero_of_flat (B C k : Type) [CommRing B] [CommRing C]
    [Algebra B C] [Module.Flat B C] [Field k] [Algebra B k] (c : C)
    (h : (1 : k) ⊗ₜ[B] c = 0) :
    c ∈ (RingHom.ker (algebraMap B k)).map (algebraMap B C) := by
  classical
  set I : Ideal B := RingHom.ker (algebraMap B k) with hI
  let f : (B ⧸ I) →ₗ[B] k :=
    Submodule.liftQ I (Algebra.linearMap B k) (fun a ha => by simpa [hI] using ha)
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ (fun a ha => by simpa [hI] using ha)
  have hinj : Function.Injective (f.rTensor C) :=
    Module.Flat.rTensor_preserves_injective_linearMap f hf
  have hx : (Ideal.Quotient.mk I 1) ⊗ₜ[B] c = 0 := by
    apply hinj
    have h1 : f (Ideal.Quotient.mk I 1) = 1 := by
      show Submodule.liftQ I (Algebra.linearMap B k) _ (Submodule.Quotient.mk 1) = 1
      rw [Submodule.liftQ_apply, Algebra.linearMap_apply, map_one]
    rw [LinearMap.rTensor_tmul, map_zero, h1]
    exact h
  have hq := congrArg (TensorProduct.quotTensorEquivQuotSMul C I) hx
  rw [TensorProduct.quotTensorEquivQuotSMul_mk_tmul, map_zero, one_smul,
    Submodule.Quotient.mk_eq_zero] at hq
  rw [Ideal.smul_top_eq_map] at hq
  exact hq

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelProdPow
section
namespace GlobalTheory.RelationPowers

theorem rel_pow {G U : Type} [Monoid G] [Monoid U] (R : G → U → Prop) (h1 : R 1 1)
    (hmul : ∀ (x x' : G) (c c' : U), R x c → R x' c' → R (x * x') (c * c'))
    (x : G) (c : U) (h : R x c) (k : ℕ) : R (x ^ k) (c ^ k) := by
  induction k with
  | zero => simpa using h1
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact hmul _ _ _ _ ih h

theorem rel_prod_pow {G U : Type} [Monoid G] [CommMonoid U] (R : G → U → Prop) (h1 : R 1 1)
    (hmul : ∀ (x x' : G) (c c' : U), R x c → R x' c' → R (x * x') (c * c'))
    (n : ℕ) (y : Fin n → G) (c : Fin n → U) (a : Fin n → ℕ) (h : ∀ i, R (y i) (c i)) :
    R (List.prod (List.ofFn fun i : Fin n => y i ^ a i)) (∏ i : Fin n, c i ^ a i) := by
  induction n with
  | zero => simpa using h1
  | succ n ih =>
    rw [List.ofFn_succ, List.prod_cons, Fin.prod_univ_succ]
    exact hmul _ _ _ _ (rel_pow R h1 hmul _ _ (h 0) _)
      (ih (fun i => y i.succ) (fun i => c i.succ) (fun i => a i.succ) (fun i => h i.succ))

end GlobalTheory.RelationPowers
end

