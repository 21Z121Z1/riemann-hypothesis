import Mathlib
import Formalism.DistinguishedUnitIdeals.Bundle0001

-- bundled from Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.AevalApplySubEvalOneMem
section
noncomputable section

namespace Formalism.ExponentWindows

theorem pow_apply_sub_mem {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    (γ : Module.End R M) (U : Submodule R M) (hU : ∀ u ∈ U, γ u ∈ U) (w : M)
    (hw : γ w - w ∈ U) (n : ℕ) : (γ ^ n) w - w ∈ U := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 := hU _ ih
    have e0 : (γ ^ (n + 1)) w = γ ((γ ^ n) w) := by rw [pow_succ']; rfl
    have e : (γ ^ (n + 1)) w - w = γ ((γ ^ n) w - w) + (γ w - w) := by
      rw [e0, map_sub]; abel
    rw [e]
    exact U.add_mem h1 hw

theorem aeval_apply_sub_eval_one_mem {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    (γ : Module.End R M) (U : Submodule R M) (hU : ∀ u ∈ U, γ u ∈ U) (w : M)
    (hw : γ w - w ∈ U) (P : Polynomial R) :
    Polynomial.aeval γ P w - P.eval 1 • w ∈ U := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    have e : Polynomial.aeval γ (p + q) w - (p + q).eval 1 • w =
        (Polynomial.aeval γ p w - p.eval 1 • w) + (Polynomial.aeval γ q w - q.eval 1 • w) := by
      rw [map_add, LinearMap.add_apply, Polynomial.eval_add, add_smul]; abel
    rw [e]
    exact U.add_mem hp hq
  | monomial n a =>
    have e : Polynomial.aeval γ (Polynomial.monomial n a) w - (Polynomial.monomial n a).eval 1 • w =
        a • ((γ ^ n) w - w) := by
      rw [Polynomial.aeval_monomial, Polynomial.eval_monomial, one_pow, mul_one, smul_sub]
      congr 1
      all_goals first
        | rfl
        | simp [Module.algebraMap_end_apply]
    rw [e]
    exact U.smul_mem a (pow_apply_sub_mem γ U hU w hw n)

theorem aeval_sub_eval_one_smul_mem : KillerShift := by
  intro R M _ _ _ γ U hU P w hw
  exact aeval_apply_sub_eval_one_mem γ U hU w hw P

theorem exists_fixed_add_of_sub_mem : InvConst := by
  intro k V _ _ _ γ U hU Q₀ hQ hkill w hw
  have hm := aeval_apply_sub_eval_one_mem γ U hU w hw Q₀
  set c := Q₀.eval 1 with hc
  set x := Polynomial.aeval γ Q₀ w with hx
  refine ⟨c⁻¹ • x, w - c⁻¹ • x, ?_, ?_, by abel⟩
  · have h := hkill w
    rw [map_mul, map_sub, Polynomial.aeval_X, map_one] at h
    change (γ - 1) x = 0 at h
    rw [LinearMap.sub_apply] at h
    change γ x - x = 0 at h
    rw [map_smul, sub_eq_zero.mp h]
  · have e : w - c⁻¹ • x = (-c⁻¹) • (x - c • w) := by
      rw [smul_sub, smul_smul, neg_mul, inv_mul_cancel₀ hQ, neg_smul, neg_smul, one_smul]; abel
    rw [e]
    exact U.smul_mem _ hm

end Formalism.ExponentWindows
end
end

-- bundled from Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.Descent
section
noncomputable section

namespace Formalism.ExponentWindows

open PowerSeries

section Helpers

variable {O : Type} [CommRing O]

theorem algHom_C (φ : PowerSeries O →ₐ[O] PowerSeries O) (a : O) : φ (C a) = C a := by
  simpa [PowerSeries.algebraMap_apply] using φ.commutes a

theorem algHom_eq_const_add (φ : PowerSeries O →ₐ[O] PowerSeries O) (h : PowerSeries O) :
    φ h = C (constantCoeff h) + φ X * φ (mk fun p => coeff (p + 1) h) := by
  conv_lhs => rw [PowerSeries.eq_shift_mul_X_add_const h]
  rw [map_add, map_mul, algHom_C]
  ring

theorem order_map_toNat_of_isDistinguishedAt {I : Ideal O} (hI : I ≠ ⊤) {E : Polynomial O}
    (hE : E.IsDistinguishedAt I) :
    ((E : PowerSeries O).map (Ideal.Quotient.mk I)).order.toNat = E.natDegree := by
  have h := hE.coe_natDegree_eq_order_map (E : PowerSeries O) 1
    (by rw [map_one]; exact (Ideal.ne_top_iff_one I).mp hI) (by rw [mul_one])
  rw [← h, ENat.toNat_coe]

theorem exists_div_of_isDistinguishedAt {I : Ideal O} [IsAdicComplete I O] (hI : I ≠ ⊤)
    {E : Polynomial O} (hE : E.IsDistinguishedAt I) (F : PowerSeries O) :
    ∃ (q : PowerSeries O) (r : Polynomial O), r.degree < E.natDegree ∧
      F = (E : PowerSeries O) * q + r := by
  have H := hE.isWeierstrassDivisorAt hI
  have hd := H.isWeierstrassDivisionAt_div_mod F
  refine ⟨H.div F, H.mod F, ?_, hd.eq_mul_add⟩
  have h1 := hd.degree_lt
  rwa [order_map_toNat_of_isDistinguishedAt hI hE] at h1

theorem eq_zero_of_isDistinguishedAt_mul {I : Ideal O} [IsAdicComplete I O] (hI : I ≠ ⊤)
    {E : Polynomial O} (hE : E.IsDistinguishedAt I) {q : PowerSeries O} {r : Polynomial O}
    (hr : r.degree < E.natDegree) (h : (E : PowerSeries O) * q = r) : r = 0 := by
  have H := hE.isWeierstrassDivisorAt hI
  refine (H.eq_zero_of_mul_eq ?_ h).2
  rwa [order_map_toNat_of_isDistinguishedAt hI hE]

theorem coe_sum_fin {d : ℕ} (a : Fin d → O) :
    ((∑ i : Fin d, Polynomial.C (a i) * Polynomial.X ^ (i : ℕ) : Polynomial O) :
      PowerSeries O) = ∑ i : Fin d, C (a i) * X ^ (i : ℕ) := by
  have h := map_sum (Polynomial.coeToPowerSeries.ringHom (R := O))
    (fun i : Fin d => Polynomial.C (a i) * Polynomial.X ^ (i : ℕ)) Finset.univ
  simp only [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_mul, Polynomial.coe_C,
    Polynomial.coe_pow, Polynomial.coe_X] at h
  exact h

theorem coeff_sum_fin {d : ℕ} (a : Fin d → O) (j : Fin d) :
    (∑ i : Fin d, Polynomial.C (a i) * Polynomial.X ^ (i : ℕ) : Polynomial O).coeff j = a j := by
  simp [Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow, Fin.val_inj]

theorem coe_eq_sum_fin {d : ℕ} {r : Polynomial O} (hr : r.degree < d) :
    (r : PowerSeries O) = ∑ i : Fin d, C (r.coeff i) * X ^ (i : ℕ) := by
  have h : r = ∑ i : Fin d, Polynomial.C (r.coeff i) * Polynomial.X ^ (i : ℕ) := by
    ext j
    rw [Polynomial.finset_sum_coeff]
    simp only [Polynomial.coeff_C_mul_X_pow]
    by_cases hj : j < d
    · rw [Finset.sum_eq_single ⟨j, hj⟩]
      · simp
      · intro b _ hb
        rw [if_neg]
        intro h
        exact hb (Fin.ext h.symm)
      · intro h
        exact absurd (Finset.mem_univ _) h
    · rw [Polynomial.coeff_eq_zero_of_degree_lt
        (lt_of_lt_of_le hr (by exact_mod_cast not_lt.mp hj))]
      symm
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [if_neg]
      intro h
      exact hj (h ▸ i.2)
  rw [← coe_sum_fin]
  exact congrArg _ h

theorem eq_zero_of_forall_pow_dvd {R : Type} [CommRing R] [IsNoetherianRing R] [IsDomain R]
    {P : R} (hP : ¬ IsUnit P) {x : R} (h : ∀ N : ℕ, P ^ N ∣ x) : x = 0 := by
  have hI : Ideal.span {P} ≠ ⊤ := by rwa [Ne, Ideal.span_singleton_eq_top]
  have h0 := Ideal.iInf_pow_eq_bot_of_isDomain _ hI
  have hx : x ∈ ⨅ i, Ideal.span {P} ^ i := Ideal.mem_iInf.mpr fun N => by
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact h N
  rw [h0, Ideal.mem_bot] at hx
  exact hx

theorem exists_sum_algHom_mul_X_pow (φ : PowerSeries O →ₐ[O] PowerSeries O) (d : ℕ)
    (hdiv : ∀ F : PowerSeries O, ∃ (q : PowerSeries O) (r : Polynomial O),
      r.degree < d ∧ F = φ X * q + r)
    (hkrull : ∀ x : PowerSeries O, (∀ N : ℕ, φ X ^ N ∣ x) → x = 0)
    (F : PowerSeries O) : ∃ h : Fin d → PowerSeries O, F = ∑ i, φ (h i) * X ^ (i : ℕ) := by
  choose qf rf hrf hF using hdiv
  let H : PowerSeries O → Fin d → PowerSeries O := fun F i => mk fun k => (rf (qf^[k] F)).coeff i
  have hT : ∀ G i, (mk fun p => coeff (p + 1) (H G i)) = H (qf G) i := by
    intro G i
    ext p
    simp [H, PowerSeries.coeff_mk, Function.iterate_succ_apply]
  have hc : ∀ G i, constantCoeff (H G i) = (rf G).coeff i := by
    intro G i
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]
    rfl
  have hS : ∀ G, ∑ i, φ (H G i) * X ^ (i : ℕ) = rf G + φ X * ∑ i, φ (H (qf G) i) * X ^ (i : ℕ) := by
    intro G
    rw [coe_eq_sum_fin (hrf G), Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [algHom_eq_const_add φ (H G i), hc, hT]
    ring
  have hdvd : ∀ N G, φ X ^ N ∣ G - ∑ i, φ (H G i) * X ^ (i : ℕ) := by
    intro N
    induction N with
    | zero => intro G; simp
    | succ N ih =>
      intro G
      obtain ⟨c, hc'⟩ := ih (qf G)
      refine ⟨c, ?_⟩
      rw [hS G]
      linear_combination (hF G) + φ X * hc'
  refine ⟨H F, ?_⟩
  exact (sub_eq_zero.mp (hkrull _ fun N => hdvd N F))

theorem eq_zero_of_sum_algHom_mul_X_pow [IsDomain O] (φ : PowerSeries O →ₐ[O] PowerSeries O)
    (d : ℕ)
    (huniq : ∀ (a : Fin d → O) (q : PowerSeries O),
      ∑ i, C (a i) * X ^ (i : ℕ) = φ X * q → ∀ i, a i = 0)
    (hP0 : φ X ≠ 0) :
    ∀ (n : ℕ) (h : Fin d → PowerSeries O), ∑ i, φ (h i) * X ^ (i : ℕ) = 0 →
      ∀ i, coeff n (h i) = 0 := by
  have step : ∀ h : Fin d → PowerSeries O, ∑ i, φ (h i) * X ^ (i : ℕ) = 0 →
      (∀ i, constantCoeff (h i) = 0) ∧
        ∑ i, φ (mk fun p => coeff (p + 1) (h i)) * X ^ (i : ℕ) = 0 := by
    intro h hs
    have e : ∑ i, φ (h i) * X ^ (i : ℕ) = ∑ i, C (constantCoeff (h i)) * X ^ (i : ℕ) +
        φ X * ∑ i, φ (mk fun p => coeff (p + 1) (h i)) * X ^ (i : ℕ) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [algHom_eq_const_add φ (h i)]
      ring
    rw [hs] at e
    have h0 := huniq (fun i => constantCoeff (h i))
      (-(∑ i, φ (mk fun p => coeff (p + 1) (h i)) * X ^ (i : ℕ))) (by linear_combination -e)
    refine ⟨h0, ?_⟩
    have hsum0 : ∑ i, C (constantCoeff (h i)) * X ^ (i : ℕ) = 0 :=
      Finset.sum_eq_zero fun i _ => by
        rw [show constantCoeff (h i) = 0 from h0 i, map_zero, zero_mul]
    rw [hsum0, zero_add] at e
    exact (mul_eq_zero.mp e.symm).resolve_left hP0
  intro n
  induction n with
  | zero =>
    intro h hs i
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact (step h hs).1 i
  | succ n ih =>
    intro h hs i
    have h1 := ih _ (step h hs).2 i
    simpa [PowerSeries.coeff_mk] using h1

end Helpers

theorem mem_span_of_frobenius_mem_span : Descent := by
  intro O _ _ _ _ ϖ hϖ φ d hd hU c f g hf
  obtain ⟨u, E, hu, hE, hEd, hP⟩ := hU
  have hmax := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  haveI : IsAdicComplete (Ideal.span {ϖ}) O := by rw [← hmax]; infer_instance
  have hI : Ideal.span {ϖ} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    exact hϖ.not_isUnit
  obtain ⟨uu, rfl⟩ := hu
  have hdiv : ∀ F : PowerSeries O, ∃ (q : PowerSeries O) (r : Polynomial O),
      r.degree < d ∧ F = φ X * q + r := by
    intro F
    obtain ⟨q, r, hr, hFq⟩ := exists_div_of_isDistinguishedAt hI hE F
    refine ⟨(↑uu⁻¹ : PowerSeries O) * q, r, hEd ▸ hr, ?_⟩
    rw [hP, hFq]
    have : (↑uu : PowerSeries O) * ↑uu⁻¹ = 1 := Units.mul_inv uu
    linear_combination (-(E : PowerSeries O) * q) * this
  have hPnu : ¬ IsUnit (φ X) := by
    intro hunit
    rw [PowerSeries.isUnit_iff_constantCoeff, hP, map_mul] at hunit
    have h2 := (IsUnit.mul_iff.mp hunit).2
    have hmem : PowerSeries.constantCoeff (E : PowerSeries O) ∈ Ideal.span {ϖ} := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe]
      exact hE.toIsWeaklyEisensteinAt.mem (by omega)
    exact hI (Ideal.eq_top_of_isUnit_mem _ hmem h2)
  have hkrull : ∀ x : PowerSeries O, (∀ N : ℕ, φ X ^ N ∣ x) → x = 0 :=
    fun x hx => eq_zero_of_forall_pow_dvd hPnu hx
  have hP0 : φ X ≠ 0 := by
    rw [hP]
    refine mul_ne_zero uu.ne_zero ?_
    rw [Ne, Polynomial.coe_eq_zero_iff]
    exact hE.monic.ne_zero
  have huniq : ∀ (a : Fin d → O) (q : PowerSeries O),
      ∑ i, C (a i) * X ^ (i : ℕ) = φ X * q → ∀ i, a i = 0 := by
    intro a q hq i
    have hr0 : (∑ i : Fin d, Polynomial.C (a i) * Polynomial.X ^ (i : ℕ) : Polynomial O) = 0 := by
      refine eq_zero_of_isDistinguishedAt_mul hI hE (q := (↑uu : PowerSeries O) * q)
        (hEd ▸ Polynomial.degree_sum_fin_lt a) ?_
      rw [coe_sum_fin, hq, hP]
      ring
    have := coeff_sum_fin a i
    rw [hr0, Polynomial.coeff_zero] at this
    exact this.symm
  obtain ⟨α, β, hαβ⟩ := Ideal.mem_span_pair.mp hf
  obtain ⟨a, ha⟩ := exists_sum_algHom_mul_X_pow φ d hdiv hkrull α
  obtain ⟨b, hb⟩ := exists_sum_algHom_mul_X_pow φ d hdiv hkrull β
  let i0 : Fin d := ⟨0, hd⟩
  let h : Fin d → PowerSeries O := fun i => C c * a i + g * b i - if i = i0 then f else 0
  have e1 : ∑ i, C c * φ (a i) * X ^ (i : ℕ) = C c * α := by
    rw [ha, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ i, φ g * φ (b i) * X ^ (i : ℕ) = φ g * β := by
    rw [hb, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e3 : ∑ i, φ (if i = i0 then f else 0) * X ^ (i : ℕ) = φ f := by
    rw [Finset.sum_eq_single i0]
    · simp [i0]
    · intro j _ hj
      simp [hj]
    · intro hn
      exact absurd (Finset.mem_univ _) hn
  have hs : ∑ i, φ (h i) * X ^ (i : ℕ) = 0 := by
    simp only [h, map_sub, map_add, map_mul, algHom_C, sub_mul, add_mul, Finset.sum_sub_distrib,
      Finset.sum_add_distrib]
    rw [e1, e2, e3]
    linear_combination hαβ
  have hz := eq_zero_of_sum_algHom_mul_X_pow φ d huniq hP0
  have h0 : h i0 = 0 := by
    ext n
    rw [map_zero]
    exact hz n h hs i0
  simp only [h, if_pos rfl, if_true] at h0
  exact Ideal.mem_span_pair.mpr ⟨a i0, b i0, by linear_combination h0⟩

end Formalism.ExponentWindows
end
end

-- bundled from Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.GroundTheory
section
noncomputable section

namespace Formalism.ExponentWindows

open PowerSeries

section Helpers

variable {O : Type} [CommRing O] [IsDomain O]

theorem C_dvd_of_forall_dvd_coeff (a : O) (w : PowerSeries O) (h : ∀ n, a ∣ coeff n w) :
    C a ∣ w := by
  choose q hq using h
  refine ⟨PowerSeries.mk q, ?_⟩
  ext n
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]
  exact hq n

theorem C_dvd_of_C_dvd_mul (ϖ : O) [(Ideal.span {ϖ}).IsMaximal] (f w : PowerSeries O)
    (hf : PowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ})) f ≠ 0)
    (h : C ϖ ∣ f * w) : C ϖ ∣ w := by
  obtain ⟨q, hq⟩ := h
  have hk : Ideal.Quotient.mk (Ideal.span {ϖ}) ϖ = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self ϖ)
  have h0 : PowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ})) (f * w) = 0 := by
    rw [hq, map_mul, PowerSeries.map_C, hk, map_zero, zero_mul]
  rw [map_mul] at h0
  have hw : PowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ})) w = 0 :=
    (mul_eq_zero.mp h0).resolve_left hf
  apply C_dvd_of_forall_dvd_coeff
  intro n
  have hn := congrArg (PowerSeries.coeff n) hw
  rw [PowerSeries.coeff_map, map_zero, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hn
  exact hn

theorem map_ne_zero_of_unitDist (ϖ : O) [(Ideal.span {ϖ}).IsMaximal] (d : ℕ)
    (p : PowerSeries O) (hp : UnitDist ϖ d p) :
    PowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ})) p ≠ 0 := by
  obtain ⟨u, E, hu, hE, hdeg, rfl⟩ := hp
  subst hdeg
  rw [map_mul]
  refine mul_ne_zero (hu.map _).ne_zero ?_
  intro h0
  have hc := congrArg (PowerSeries.coeff E.natDegree) h0
  rw [PowerSeries.coeff_map, Polynomial.coeff_coe, hE.monic.coeff_natDegree, map_one, map_zero] at hc
  exact one_ne_zero hc

theorem constantCoeff_mem_of_unitDist (ϖ : O) (d : ℕ) (p : PowerSeries O) (hp : UnitDist ϖ d p)
    (hd : 1 ≤ d) : coeff 0 p ∈ Ideal.span {ϖ} := by
  obtain ⟨u, E, hu, hE, hdeg, rfl⟩ := hp
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul]
  refine Ideal.mul_mem_left _ _ ?_
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe]
  exact hE.mem (by omega)

end Helpers

private theorem mem_span_of_C_pow_mul_mem_span {O : Type} [CommRing O] [IsDomain O] (ϖ : O)
    [(Ideal.span {ϖ}).IsMaximal] (hϖ0 : ϖ ≠ 0) (q : PowerSeries O)
    (hq : PowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ})) q ≠ 0) :
    ∀ (N : ℕ) (z : PowerSeries O), C (ϖ ^ N) * z ∈ Ideal.span {q} → z ∈ Ideal.span {q} := by
  have hC : (C ϖ : PowerSeries O) ≠ 0 := fun h =>
    hϖ0 (by simpa using congrArg PowerSeries.constantCoeff h)
  intro N
  induction N with
  | zero =>
    intro z hz
    simpa using hz
  | succ N ih =>
    intro z hz
    apply ih
    rw [Ideal.mem_span_singleton] at hz ⊢
    obtain ⟨y, hy⟩ := hz
    have hdiv : C ϖ ∣ q * y := ⟨C (ϖ ^ N) * z, by rw [← hy, pow_succ, map_mul]; ring⟩
    obtain ⟨y', rfl⟩ := C_dvd_of_C_dvd_mul ϖ q y hq hdiv
    refine ⟨y', ?_⟩
    apply mul_left_cancel₀ hC
    rw [pow_succ, map_mul] at hy
    linear_combination hy

theorem mem_span_pow_of_uniformizer_mul : SatDist := by
  intro O _ _ _ ϖ hϖ d p hp k N z hz
  have := PrincipalIdealRing.isMaximal_of_irreducible hϖ
  have hq : PowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ})) (p ^ k) ≠ 0 := by
    rw [map_pow]
    exact pow_ne_zero k (map_ne_zero_of_unitDist ϖ d p hp)
  exact mem_span_of_C_pow_mul_mem_span ϖ hϖ.ne_zero (p ^ k) hq N z hz

theorem pow_dvd_of_const_mem_span : ConstDist := by
  intro O _ _ _ ϖ hϖ d p hp hd c y N a h
  have key : ∀ (N : ℕ) (z : PowerSeries O), C (ϖ ^ N) * z ∈ Ideal.span {p} → z ∈ Ideal.span {p} :=
    fun N z hz => by simpa using mem_span_pow_of_uniformizer_mul O ϖ hϖ d p hp 1 N z (by simpa using hz)
  have hp0 := constantCoeff_mem_of_unitDist ϖ d p hp hd
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, Ideal.mem_span_singleton] at hp0
  have h1 := key N _ h
  clear h
  induction y generalizing c a with
  | zero => simp
  | succ y ih =>
    have e2 : C (ϖ ^ y) * (C ϖ * a) = C (ϖ ^ (y + 1)) * a := by
      rw [← mul_assoc, ← map_mul, pow_succ]
    have h2 : C c - C (ϖ ^ y) * (C ϖ * a) ∈ Ideal.span {p} := by
      rw [e2]
      exact h1
    obtain ⟨c', rfl⟩ := ih c (C ϖ * a) h2
    have e3 : C (ϖ ^ y) * (C c' - C ϖ * a) = C (ϖ ^ y * c') - C (ϖ ^ (y + 1)) * a := by
      rw [mul_sub, ← map_mul, ← mul_assoc, ← map_mul, ← pow_succ]
    have h3 : C c' - C ϖ * a ∈ Ideal.span {p} := by
      apply key y
      rw [e3]
      exact h1
    obtain ⟨g, hg⟩ := Ideal.mem_span_singleton'.mp h3
    have h4 := congrArg PowerSeries.constantCoeff hg
    simp only [map_mul, map_sub, PowerSeries.constantCoeff_C] at h4
    have hc' : ϖ ∣ c' := by
      have e : c' = PowerSeries.constantCoeff g * PowerSeries.constantCoeff p +
          ϖ * PowerSeries.constantCoeff a := by
        linear_combination (-1 : O) * h4
      rw [e]
      exact dvd_add (dvd_mul_of_dvd_right hp0 _) (dvd_mul_right _ _)
    obtain ⟨c'', rfl⟩ := hc'
    exact ⟨c'', by ring⟩

private theorem coprimeRat_symm' {O : Type} [CommRing O] {ϖ : O} {x y : PowerSeries O}
    (h : CoprimeRat ϖ x y) : CoprimeRat ϖ y x := by
  unfold CoprimeRat at h ⊢
  obtain ⟨N, A, A', hA⟩ := h
  exact ⟨N, A', A, by rw [← hA]; ring⟩

private theorem coprimeRat_mul_left' {O : Type} [CommRing O] {ϖ : O} {x x' y : PowerSeries O}
    (h1 : CoprimeRat ϖ x y) (h2 : CoprimeRat ϖ x' y) : CoprimeRat ϖ (x * x') y := by
  unfold CoprimeRat at h1 h2 ⊢
  obtain ⟨N, A, A', hA⟩ := h1
  obtain ⟨M, B, B', hB⟩ := h2
  refine ⟨N + M, A * B, A * x * B' + A' * (B * x' + B' * y), ?_⟩
  rw [pow_add, map_mul, ← hA, ← hB]
  ring

private theorem coprimeRat_pow_left' {O : Type} [CommRing O] {ϖ : O} {x y : PowerSeries O}
    (h : CoprimeRat ϖ x y) (a : ℕ) : CoprimeRat ϖ (x ^ a) y := by
  induction a with
  | zero =>
    unfold CoprimeRat
    exact ⟨0, 1, 0, by simp⟩
  | succ a ih =>
    rw [pow_succ]
    exact coprimeRat_mul_left' ih h

theorem coprimeProd_statement : CoprimeProd := by
  intro O _ _ _ ϖ hϖ d d' p p' hp hp' hcop a b z hza hzb
  have := PrincipalIdealRing.isMaximal_of_irreducible hϖ
  have hc : CoprimeRat ϖ (p ^ a) (p' ^ b) :=
    coprimeRat_symm' (coprimeRat_pow_left' (coprimeRat_symm' (coprimeRat_pow_left' hcop a)) b)
  unfold CoprimeRat at hc
  obtain ⟨M, B, B', hB⟩ := hc
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp hza
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hzb
  have hq : PowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ})) (p ^ a * p' ^ b) ≠ 0 := by
    rw [map_mul, map_pow, map_pow]
    exact mul_ne_zero (pow_ne_zero a (map_ne_zero_of_unitDist ϖ d p hp))
      (pow_ne_zero b (map_ne_zero_of_unitDist ϖ d' p' hp'))
  refine mem_span_of_C_pow_mul_mem_span ϖ hϖ.ne_zero _ hq M z
    (Ideal.mem_span_singleton'.mpr ⟨B * t + B' * s, ?_⟩)
  rw [← hB]
  linear_combination (B * p ^ a) * ht + (B' * p' ^ b) * hs

end Formalism.ExponentWindows
end
end

