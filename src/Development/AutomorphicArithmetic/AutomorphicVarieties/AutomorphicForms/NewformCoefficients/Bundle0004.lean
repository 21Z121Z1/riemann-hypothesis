import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.CuspCritAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Bundle0002
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0066

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.CharVal
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Af.Nf

private theorem cv_mem {x : Af ℚ} : x ∈ Ohat ℚ ↔ ∀ w : Pl ℚ, Valued.v (pLoc ℚ w x) ≤ 1 := by
  simp [Ohat, Subring.mem_iInf, HeightOneSpectrum.mem_adicCompletionIntegers]

private theorem cv_val (w : Pl ℚ) (x : ℚ) : Valued.v (pLoc ℚ w (algebraMap ℚ (Af ℚ) x)) = w.valuation ℚ x :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x

private theorem cv_nat (w : Pl ℚ) (n : ℕ) : w.valuation ℚ (n : ℚ) = w.intValuation (n : 𝓞 ℚ) := by
  rw [← HeightOneSpectrum.valuation_of_algebraMap (K := ℚ)]
  exact congrArg _ (map_natCast (algebraMap (𝓞 ℚ) ℚ) n).symm

private theorem cv_one (w : Pl ℚ) (n : ℕ) (h : ¬ normV w ∣ n) : w.valuation ℚ (n : ℚ) = 1 := by
  obtain ⟨hp, hI, -⟩ := places w
  rw [cv_nat]
  refine le_antisymm (w.intValuation_le_one _) (not_lt.1 fun hlt => ?_)
  have hn : (n : 𝓞 ℚ) ∈ w.asIdeal := (w.intValuation_lt_one_iff_mem _).1 hlt
  have hq : ((normV w : ℕ) : 𝓞 ℚ) ∈ w.asIdeal := by rw [hI]; exact Ideal.mem_span_singleton_self _
  obtain ⟨a, b, e⟩ : IsCoprime ((normV w : ℕ) : 𝓞 ℚ) (n : 𝓞 ℚ) := ((Nat.Prime.coprime_iff_not_dvd hp).2 h).cast
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (e ▸ add_mem (Ideal.mul_mem_left _ _ hq) (Ideal.mul_mem_left _ _ hn)))

private theorem cv_unif (w : Pl ℚ) : w.valuation ℚ ((normV w : ℕ) : ℚ) = WithZero.exp (-1 : ℤ) := by
  obtain ⟨hp, hI, -⟩ := places w
  rw [cv_nat]
  exact w.intValuation_singleton (by exact_mod_cast hp.ne_zero) hI

private theorem cv_ne {v w : Pl ℚ} (h : v ≠ w) : v.valuation ℚ ((normV w : ℕ) : ℚ) = 1 := by
  refine cv_one v _ fun hd => h (HeightOneSpectrum.ext ?_)
  rw [(places v).2.1, (places w).2.1, (Nat.prime_dvd_prime_iff_eq (places v).1 (places w).1).1 hd]

private theorem cv_div {M : ℕ} (hM : 1 ≤ M) {w : Pl ℚ} (hw : ¬ normV w ∣ M) {x : Af ℚ}
    (h0 : ∀ v, v ≠ w → pLoc ℚ v x = 0) (h1 : Valued.v (pLoc ℚ w x) ≤ 1) : ∃ y ∈ Ohat ℚ, x = M * y := by
  have hM0 : (M : ℚ) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  refine ⟨algebraMap ℚ (Af ℚ) (M : ℚ)⁻¹ * x, cv_mem.2 fun v => ?_, ?_⟩
  · by_cases h : v = w
    · subst h
      rw [map_mul, map_mul, cv_val, map_inv₀, cv_one v M hw, inv_one, one_mul]; exact h1
    · rw [map_mul, h0 v h, mul_zero, map_zero]; exact zero_le_one
  · rw [← mul_assoc, ← map_natCast (algebraMap ℚ (Af ℚ)), ← map_mul, mul_inv_cancel₀ hM0, map_one, one_mul]

private theorem cv_zu {u : (Af ℚ)ˣ} (h : ∀ v : Pl ℚ, Valued.v (pLoc ℚ v u) = 1) : IsZU u := by
  refine ⟨cv_mem.2 fun v => (h v).le, cv_mem.2 fun v => ?_⟩
  rw [map_units_inv, map_inv₀, h v, inv_one]

private theorem cv_same (w : Pl ℚ) (x : w.adicCompletion ℚ) : pLoc ℚ w (finiteSingle ℚ w x) = x := by
  classical
  exact Pi.mulSingle_eq_same (M := fun v : Pl ℚ => v.adicCompletion ℚ) w x

private theorem cv_other {v w : Pl ℚ} (h : v ≠ w) (x : w.adicCompletion ℚ) : pLoc ℚ v (finiteSingle ℚ w x) = 1 := by
  classical
  exact Pi.mulSingle_eq_of_ne (M := fun v : Pl ℚ => v.adicCompletion ℚ) h x

private theorem cv_loc (w : Pl ℚ) (x : (w.adicCompletion ℚ)ˣ) :
    finId ℚ (Units.map (finiteSingle ℚ w) x) = localIdele ℚ w x := by
  refine Units.ext (Prod.ext ?_ ?_)
  · change (1 : InfiniteAdeleRing ℚ) - 0 + 0 = 1
    simp
  · change (1 : Af ℚ) - 1 + finiteSingle ℚ w x = finiteSingle ℚ w x
    simp

private theorem cv_split (x : Ideles ℚ) :
    TR.infId ℚ (Units.map (TR.pInf ℚ).toMonoidHom x) * finId ℚ (Units.map (pFin ℚ).toMonoidHom x) = x := by
  have h : ∀ x, TR.pInf ℚ (TR.sInf ℚ x) = x := fun x => (TR.infEq ℚ).symm_apply_apply x
  have h2 : ∀ x, TR.pInf ℚ (sFin ℚ x) = 0 := fun x => map_zero (TR.infEq ℚ).symm
  have h3 : ∀ x, pFin ℚ (TR.sInf ℚ x) = 0 := fun x => rfl
  have h4 : ∀ x, pFin ℚ (sFin ℚ x) = x := fun x => rfl
  refine Units.ext (TR.ad_ext ?_ ?_)
  · change TR.pInf ℚ ((1 - TR.sInf ℚ 1 + TR.sInf ℚ (TR.pInf ℚ x.val)) * (1 - sFin ℚ 1 + sFin ℚ (pFin ℚ x.val))) = _
    simp [h, h2]
  · change pFin ℚ ((1 - TR.sInf ℚ 1 + TR.sInf ℚ (TR.pInf ℚ x.val)) * (1 - sFin ℚ 1 + sFin ℚ (pFin ℚ x.val))) = _
    simp [h3, h4]

private theorem cv_rat {M : ℕ} {χ : DirichletCharacter ℂ M} {ω : HChar ℚ} (h : IsDirOf χ ω) (r : ℚˣ) (hr : 0 < (r : ℚ)) :
    ω.1 (finId ℚ (Units.map (algebraMap ℚ (Af ℚ)).toMonoidHom r)) = 1 := by
  have h1 := ω.2.2 r
  rw [← cv_split (diagUnits ℚ r), map_mul, h.pos _ fun v => ?_, one_mul] at h1
  · exact h1
  · have e := eq_ratCast ((Pi.evalRingHom (fun _ : InfinitePlace ℚ => ℝ) v).comp
      ((TR.pInf ℚ).comp (algebraMap ℚ (Ad ℚ)))) (r : ℚ)
    exact lt_of_lt_of_eq (Rat.cast_pos.2 hr) e.symm

theorem UpperTheory.V.Af.Nf.charVal :
    UpperTheory.V.Af.Nf.CharVal := by
  intro M hM χ ω h
  haveI : NeZero M := ⟨by omega⟩
  refine ⟨isOfFinOrder_iff_pow_eq_one.2 ⟨2 * Fintype.card (ZMod M)ˣ, by positivity, Subtype.ext (MonoidHom.ext fun z => ?_)⟩,
    fun w hw => ?_⟩
  · change ω.1 z ^ (2 * Fintype.card (ZMod M)ˣ) = 1
    obtain ⟨r, u, hr, hu, e⟩ := ratAd.1 (Units.map (pFin ℚ).toMonoidHom z)
    obtain ⟨d, hd⟩ := ratAd.2.1 M hM _ hu.1
    have h1 := h.unit u hu d hd
    have h2 : IsUnit (d : ZMod M) := by
      by_contra hn
      rw [χ.map_nonunit hn, mul_zero] at h1
      exact zero_ne_one h1
    obtain ⟨c, hc⟩ := h2
    have h3 : ω.1 (finId ℚ u) ^ Fintype.card (ZMod M)ˣ = 1 := by
      have := congrArg (· ^ Fintype.card (ZMod M)ˣ) h1
      simp only [mul_pow, one_pow] at this
      rw [← hc, ← map_pow, ← Units.val_pow_eq_pow_val c, pow_card_eq_one, Units.val_one, map_one, mul_one] at this
      exact Units.ext this
    have h4 : ∀ t, ω.1 (TR.infId ℚ t) ^ 2 = 1 := fun t => by
      rw [← map_pow, ← map_pow]
      exact h.pos _ fun v => by
        rw [Units.val_pow_eq_pow_val, Pi.pow_apply]
        exact sq_pos_of_ne_zero (by simpa using (Units.map (Pi.evalRingHom (fun _ : InfinitePlace ℚ => ℝ) v).toMonoidHom t).ne_zero)
    rw [← cv_split z, e, map_mul, map_mul, map_mul, cv_rat h r hr, one_mul, mul_pow, pow_mul, h4, one_pow, one_mul,
      mul_comm 2, pow_mul, h3, one_pow]
  · have hun : ω.UnrAt w := fun x hx => by
      have h1 := h.unit (Units.map (finiteSingle ℚ w) x) (cv_zu fun v => ?_) 1 (cv_div hM hw (fun v hv => ?_) ?_)
      · rw [cv_loc, Int.cast_one, map_one, mul_one] at h1
        exact Units.ext h1
      · by_cases hv : v = w
        · subst hv; exact (congrArg _ (cv_same v x)).trans hx
        · exact (congrArg _ (cv_other hv x)).trans (map_one _)
      · rw [map_sub, Units.coe_map, cv_other hv, Int.cast_one, map_one, sub_self]
      · rw [map_sub, Units.coe_map, cv_same, Int.cast_one, map_one]
        exact (Valuation.map_sub _ _ _).trans (max_le (le_of_eq hx) (map_one _).le)
    let p : ℚˣ := Units.mk0 ((normV w : ℕ) : ℚ) (by exact_mod_cast (places w).1.ne_zero)
    have hp : 0 < (p : ℚ) := by
      change 0 < ((normV w : ℕ) : ℚ)
      exact_mod_cast (places w).1.pos
    have hU : IsUnifAt w (atFin w p) := (cv_val w p).trans (cv_unif w)
    let u : (Af ℚ)ˣ := Units.map (algebraMap ℚ (Af ℚ)).toMonoidHom p * Units.map (finiteSingle ℚ w) (atFin w p)⁻¹
    have u1 : pLoc ℚ w u = 1 := by
      rw [Units.val_mul, map_mul, Units.coe_map (finiteSingle ℚ w), cv_same]
      exact (atFin w p).mul_inv
    have u2 : ∀ v, v ≠ w → pLoc ℚ v u = pLoc ℚ v (algebraMap ℚ (Af ℚ) p) := fun v hv => by
      rw [Units.val_mul, map_mul, Units.coe_map (finiteSingle ℚ w), cv_other hv, mul_one]
      rfl
    have e : (((normV w : ℕ) : ℤ) : Af ℚ) = algebraMap ℚ (Af ℚ) p := by
      rw [Int.cast_natCast]; exact (map_natCast _ _).symm
    have h1 := h.unit u (cv_zu fun v => ?_) (normV w : ℕ) (cv_div hM hw (fun v hv => ?_) ?_)
    · rw [map_mul, map_mul, cv_rat h p hp, one_mul, cv_loc, map_inv, map_inv, Int.cast_natCast, Units.val_inv_eq_inv_val,
        inv_mul_eq_one₀ (Units.ne_zero _)] at h1
      rw [← ω.val_eq hun _ hU]
      exact h1
    · by_cases hv : v = w
      · subst hv; rw [u1, map_one]
      · rw [u2 v hv, cv_val]; exact cv_ne hv
    · rw [map_sub, u2 v hv, e, sub_self]
    · rw [map_sub, u1, e]
      refine (Valuation.map_sub _ _ _).trans (max_le (map_one _).le ?_)
      rw [cv_val]
      exact (cv_nat w _).trans_le (w.intValuation_le_one _)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.ClassCT
section
open CongruenceSubgroup UpperTheory.V.Af.Nf
open UpperHalfPlane hiding I
open scoped Matrix MatrixGroups ModularForm Pointwise

private lemma aux {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] {k : ℤ} (F : CuspForm Γ k) (z : ℍ) :
    ∃ N : ℕ, 0 < N ∧ Function.Periodic (fun t : ℝ => F (t +ᵥ z)) N ∧
      ∫ t in (0 : ℝ)..N, F (t +ᵥ z) = 0 := by
  have h1 : Matrix.GeneralLinearGroup.upperRightHom (1 : ℝ) ∈ (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)) := by
    rw [← Subgroup.mem_strictPeriods_iff, Subgroup.strictPeriods_SL2Z]
    exact AddSubgroup.mem_zmultiples _
  obtain ⟨N, hN, -, hm⟩ := Subgroup.exists_pow_mem_of_relIndex_ne_zero
    (Subgroup.IsArithmetic.is_commensurable (𝒢 := Γ)).1 h1
  have hP : (N : ℝ) ∈ Γ.strictPeriods := by
    rw [Subgroup.mem_strictPeriods_iff]
    have := (Subgroup.mem_inf.mp hm).1
    rw [← AddChar.map_nsmul_eq_pow] at this
    simpa only [nsmul_eq_mul, mul_one] using this
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hper : ∀ w : ℍ, Function.Periodic (fun t : ℝ => F (t +ᵥ w)) N := fun w t => by
    have := SlashInvariantForm.vAdd_apply_of_mem_strictPeriods F (t +ᵥ w) hP
    simp only
    rw [add_comm, add_vadd]
    exact this
  refine ⟨N, hN, hper z, ?_⟩
  have h0 := CuspFormClass.qExpansion_coeff_zero F hN' hP
  rw [ModularFormClass.qExpansion_coeff_eq_intervalIntegral F hN' hP 0 z.im_pos] at h0
  have hne : (1 / ((N : ℝ) : ℂ)) ≠ 0 := by
    have : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    simpa using this
  have h2 := (mul_eq_zero.mp h0).resolve_left hne
  set w : ℍ := (-z.re) +ᵥ z with hw
  have h3 : ∫ t in (0 : ℝ)..N, F (t +ᵥ w) = 0 := by
    rw [← h2]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [pow_zero, div_one, one_mul]
    congr 1
    apply UpperHalfPlane.ext
    apply Complex.ext <;> simp [hw]
  have h4 := (hper w).intervalIntegral_add_eq z.re 0
  rw [zero_add, h3] at h4
  rw [← h4]
  have h5 := intervalIntegral.integral_comp_add_right (fun t : ℝ => F (t +ᵥ w)) z.re (a := 0) (b := N)
  rw [zero_add, add_comm (N : ℝ)] at h5
  rw [← h5]
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [hw, vadd_vadd]
  congr 2
  ring

private lemma aux2 (k M : ℕ) (hM : 1 ≤ M) (f : CuspForm (Gamma1 M) (k : ℤ)) (γ : GL (Fin 2) ℚ)
    (hγ : 0 < (toR γ).val.det) (z : ℍ) : ∃ N : ℕ, 0 < N ∧
    Function.Periodic (fun t : ℝ => nsl k f (toR γ) (t +ᵥ z)) N ∧
      ∫ t in (0 : ℝ)..N, nsl k f (toR γ) (t +ᵥ z) = 0 := by
  haveI : NeZero M := ⟨by omega⟩
  haveI : (ConjAct.toConjAct (toR γ)⁻¹ • (Gamma1 M : Subgroup (GL (Fin 2) ℝ))).IsArithmetic := by
    have := Subgroup.IsArithmetic.conj (Gamma1 M : Subgroup (GL (Fin 2) ℝ)) γ⁻¹
    rw [← map_inv]
    exact this
  obtain ⟨N, hN, hp, hi⟩ := aux (CuspForm.translate f (toR γ)) z
  refine ⟨N, hN, ?_, ?_⟩
  · intro t
    have := hp t
    simp only [(nslSl k f).2.1 _ hγ, Pi.smul_apply]
    congr 1
  · simp only [(nslSl k f).2.1 _ hγ, Pi.smul_apply, smul_eq_mul]
    rw [intervalIntegral.integral_const_mul]
    exact mul_eq_zero_of_right _ hi

theorem UpperTheory.V.Af.Nf.classCT :
    UpperTheory.V.Af.Nf.ClassCT := by
  intro k M hM f γ z
  have hne : (toR γ).val.det ≠ 0 := (toR γ).det_ne_zero
  rcases hne.lt_or_gt with h | h
  · let e : GL (Fin 2) ℚ := Matrix.GeneralLinearGroup.mkOfDetNeZero !![-1, 0; 0, 1] (by simp)
    have he : (toR (e * γ)).val = eps * (toR γ).val := by
      rw [map_mul, Units.val_mul]
      congr 1
      ext i j
      fin_cases i <;> fin_cases j <;> simp [toR, e, eps]
    have hd : 0 < (toR (e * γ)).val.det := by
      rw [he, Matrix.det_mul]
      simpa [eps] using h
    have := aux2 k M hM f (e * γ) hd z
    rwa [he, (nslMul k f).2.1] at this
  · exact aux2 k M hM f γ h z
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.CoefAt
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V.Sd UpperTheory.V.Af UpperTheory.V.Af.Nf

private theorem ord_diff (w : HeightOneSpectrum (𝓞 ℚ)) : ordI w (differentIdeal ℤ (𝓞 ℚ)) = 0 := by
  have h : differentIdeal ℤ (𝓞 ℚ) = ⊤ := by
    rw [← Ideal.absNorm_eq_one_iff, absNorm_differentIdeal ℚ (𝓞 ℚ), discr_rat]; rfl
  rw [h, ordI, ← Ideal.one_eq_top, Associates.mk_one, Associates.factors_one, Associates.count_zero w.associates_irreducible]

private theorem eq_of_ord {I J : Ideal (𝓞 ℚ)} (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (h : ∀ w, ordI w I = ordI w J) : I = J := by
  rw [← Ideal.finprod_heightOneSpectrum_factorization hI, ← Ideal.finprod_heightOneSpectrum_factorization hJ]
  refine finprod_congr fun w => ?_
  exact congrArg (fun n => w.asIdeal ^ n) (h w)

private theorem val_unit {u : (Af ℚ)ˣ} (hu : IsZU u) (w : HeightOneSpectrum (𝓞 ℚ)) :
    Valued.v (pLoc ℚ w (u : Af ℚ)) = 1 := by
  have h1 : Valued.v (pLoc ℚ w (u : Af ℚ)) ≤ 1 := Subring.mem_iInf.1 hu.1 w
  have h2 : Valued.v (pLoc ℚ w ((u⁻¹ : (Af ℚ)ˣ) : Af ℚ)) ≤ 1 := Subring.mem_iInf.1 hu.2 w
  have h3 : Valued.v (pLoc ℚ w (u : Af ℚ)) * Valued.v (pLoc ℚ w ((u⁻¹ : (Af ℚ)ˣ) : Af ℚ)) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  refine le_antisymm h1 ?_
  calc 1 = _ := h3.symm
    _ ≤ Valued.v (pLoc ℚ w (u : Af ℚ)) * 1 := mul_le_mul_right h2 _
    _ = _ := mul_one _

private theorem genD_iff (q : ℚ) {u : (Af ℚ)ˣ} (hu : IsZU u) (𝔪 : Ideal (𝓞 ℚ)) :
    GenD (algebraMap ℚ (Af ℚ) q * (u : Af ℚ)) 𝔪 ↔
      𝔪 ≠ ⊥ ∧ ∀ w : HeightOneSpectrum (𝓞 ℚ), w.valuation ℚ q = WithZero.exp (-(ordI w 𝔪 : ℤ)) := by
  refine and_congr_right fun _ => forall_congr' fun w => ?_
  have h : Valued.v (pLoc ℚ w (algebraMap ℚ (Af ℚ) q)) = w.valuation ℚ q :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w q
  rw [map_mul, map_mul, val_unit hu, mul_one, h, ord_diff, Nat.cast_zero, zero_sub]

private theorem val_nat {n : ℕ} (hn : n ≠ 0) (w : HeightOneSpectrum (𝓞 ℚ)) :
    w.valuation ℚ (n : ℚ) = WithZero.exp (-(ordI w (Ideal.span {(n : 𝓞 ℚ)}) : ℤ)) := by
  rw [← map_natCast (algebraMap (𝓞 ℚ) ℚ) n, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_if_neg w (Nat.cast_ne_zero.2 hn)]
  rfl

theorem UpperTheory.V.Af.Nf.coefAt :
    UpperTheory.V.Af.Nf.CoefAt := by
  intro a q hq u hu
  by_cases hd : q.den = 1
  · rw [if_pos hd]
    have hnum : 0 < q.num := Rat.num_pos.2 hq
    have hn : q.num.toNat ≠ 0 := by omega
    have hqn : q = (q.num.toNat : ℚ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hnum.le]
      exact ((Rat.den_eq_one_iff q).1 hd).symm
    have hb : Ideal.span {((q.num.toNat : ℕ) : 𝓞 ℚ)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]; exact Nat.cast_ne_zero.2 hn
    have hv : ∀ w : HeightOneSpectrum (𝓞 ℚ),
        w.valuation ℚ q = WithZero.exp (-(ordI w (Ideal.span {((q.num.toNat : ℕ) : 𝓞 ℚ)}) : ℤ)) := fun w => by
      rw [← val_nat hn w, ← hqn]
    have hex : ∃ 𝔪, GenD (algebraMap ℚ (Af ℚ) q * (u : Af ℚ)) 𝔪 := ⟨_, (genD_iff q hu _).2 ⟨hb, hv⟩⟩
    obtain ⟨h1, h2⟩ := (genD_iff q hu _).1 hex.choose_spec
    have he : hex.choose = Ideal.span {((q.num.toNat : ℕ) : 𝓞 ℚ)} := eq_of_ord h1 hb fun w => by
      have := WithZero.exp_injective ((h2 w).symm.trans (hv w))
      omega
    rw [UpperTheory.V.Sd.coefAt, dif_pos hex, he, Ideal.absNorm_span_natCast, RingOfIntegers.rank, Module.finrank_self, pow_one]
  · rw [if_neg hd, UpperTheory.V.Sd.coefAt, dif_neg]
    rintro ⟨𝔪, h⟩
    obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 ℚ) ℚ q fun w => by
      rw [((genD_iff q hu _).1 h).2 w, ← WithZero.exp_zero, WithZero.exp_le_exp]
      omega
    obtain ⟨m, rfl⟩ := Rat.ringOfIntegersEquiv.symm.surjective r
    apply hd
    rw [← hr, eq_intCast Rat.ringOfIntegersEquiv.symm m, map_intCast]
    rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.DirChar
section
open NumberField IsDedekindDomain Topology Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep

namespace UpperTheory.V.Af.Nf

private theorem dc_inv {M : ℕ} (hM : 1 ≤ M) : algebraMap ℚ (Af ℚ) (M : ℚ)⁻¹ * M = 1 := by
  have hM' : (M : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  rw [← map_natCast (algebraMap ℚ (Af ℚ)), ← map_mul, inv_mul_cancel₀ hM', map_one]

private theorem dc_uniq {M : ℕ} (hM : 1 ≤ M) {x : Af ℚ} {d e : ℤ} (hd : ∃ y ∈ Ohat ℚ, x - d = M * y)
    (he : ∃ y ∈ Ohat ℚ, x - e = M * y) : (d : ZMod M) = e := by
  obtain ⟨y, hy, hd⟩ := hd
  obtain ⟨z, hz, he⟩ := he
  have hM' : (M : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have h1 : algebraMap ℚ (Af ℚ) ((M : ℚ)⁻¹ * ((e : ℚ) - d)) = y - z := by
    rw [map_mul, map_sub, map_intCast, map_intCast]
    linear_combination algebraMap ℚ (Af ℚ) (M : ℚ)⁻¹ * (hd - he) + (y - z) * dc_inv hM
  obtain ⟨n, hn⟩ := ratAd.2.2 _ (h1 ▸ sub_mem hy hz)
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
  refine ⟨n, ?_⟩
  rw [inv_mul_eq_iff_eq_mul₀ hM'] at hn
  exact_mod_cast hn

private theorem dc_red {M : ℕ} (hM : 1 ≤ M) : ∃ ρ : ↥(Ohat ℚ) →* ZMod M,
    ∀ (x : ↥(Ohat ℚ)) (d : ℤ), (∃ y ∈ Ohat ℚ, (x : Af ℚ) - d = M * y) → ρ x = d := by
  choose f hf using fun x : ↥(Ohat ℚ) => ratAd.2.1 M hM x x.2
  refine ⟨⟨⟨fun x => f x, ?_⟩, fun a b => ?_⟩, fun x d h => dc_uniq hM (hf x) h⟩
  · have := dc_uniq hM (e := 1) (hf 1) ⟨0, zero_mem _, by simp⟩
    simpa using this
  · obtain ⟨y, hy, h1⟩ := hf a
    obtain ⟨z, hz, h2⟩ := hf b
    have := dc_uniq hM (e := f a * f b) (hf (a * b)) ⟨a * z + f b * y,
      add_mem (mul_mem a.2 hz) (mul_mem (intCast_mem _ _) hy), by
        rw [Subring.coe_mul, Int.cast_mul]
        linear_combination (a : Af ℚ) * h2 + (f b : Af ℚ) * h1⟩
    simpa using this

private noncomputable abbrev pF : Ideles ℚ →* (Af ℚ)ˣ := Units.map (pFin ℚ).toMonoidHom

private noncomputable abbrev pR : Ideles ℚ →* ℝˣ := Units.map (ev.comp (TR.pInf ℚ)).toMonoidHom

private noncomputable abbrev dg : ℚˣ →* Ideles ℚ := Units.map (algebraMap ℚ (Ad ℚ)).toMonoidHom

private theorem pR_dg (r : ℚˣ) : (pR (dg r) : ℝ) = ((r : ℚ) : ℝ) :=
  eq_ratCast ((ev.comp (TR.pInf ℚ)).comp (algebraMap ℚ (Ad ℚ))) (r : ℚ)

private theorem pF_dg (r : ℚˣ) : pF (dg r) = Units.map (algebraMap ℚ (Af ℚ)).toMonoidHom r := Units.ext rfl

private theorem pF_inf (t : (TR.Rinf ℚ)ˣ) : pF (TR.infId ℚ t) = 1 := by
  refine Units.ext ?_
  change (1 : Af ℚ) - 0 + 0 = 1
  simp

private theorem pR_inf (t : (TR.Rinf ℚ)ˣ) : (pR (TR.infId ℚ t) : ℝ) = t.val Rat.infinitePlace := by
  have h : ∀ x, TR.pInf ℚ (TR.sInf ℚ x) = x := fun x => (TR.infEq ℚ).symm_apply_apply x
  change ev (TR.pInf ℚ (1 - TR.sInf ℚ 1 + TR.sInf ℚ t.val)) = ev t.val
  simp [h]

private theorem pF_fin (u : (Af ℚ)ˣ) : pF (finId ℚ u) = u := by
  refine Units.ext ?_
  change (1 : Af ℚ) - 1 + u = u
  simp

private theorem pR_fin (u : (Af ℚ)ˣ) : (pR (finId ℚ u) : ℝ) = 1 := by
  have h : ∀ x, TR.pInf ℚ (sFin ℚ x) = 0 := fun x => map_zero (TR.infEq ℚ).symm
  change ev (TR.pInf ℚ (1 - sFin ℚ 1 + sFin ℚ u.val)) = 1
  simp [h]

private theorem zu_mul {u v : (Af ℚ)ˣ} (hu : IsZU u) (hv : IsZU v) : IsZU (u * v) :=
  ⟨mul_mem hu.1 hv.1, by rw [mul_inv]; exact mul_mem hu.2 hv.2⟩

private theorem zu_one : IsZU 1 := ⟨one_mem _, one_mem _⟩

private noncomputable def PU : Subgroup (Ideles ℚ) where
  carrier := {a | 0 < (pR a : ℝ) ∧ IsZU (pF a)}
  one_mem' := ⟨by rw [map_one]; exact one_pos, by rw [map_one]; exact zu_one⟩
  mul_mem' := fun {a b} ha hb => ⟨by rw [map_mul]; exact mul_pos ha.1 hb.1, by rw [map_mul]; exact zu_mul ha.2 hb.2⟩
  inv_mem' := fun {a} ha => ⟨by rw [map_inv, Units.val_inv_eq_inv_val]; exact inv_pos.2 ha.1,
    by rw [map_inv]; exact ⟨ha.2.2, ha.2.1⟩⟩

private theorem dc_ker (r : ℚˣ) (h : dg r ∈ PU) : r = 1 := by
  obtain ⟨h0, h1, h2⟩ := h
  rw [pR_dg, Rat.cast_pos] at h0
  obtain ⟨n, hn⟩ := ratAd.2.2 r h1
  obtain ⟨m, hm⟩ := ratAd.2.2 (r⁻¹ : ℚˣ) h2
  have e : n * m = 1 := by
    have := r.mul_inv
    rw [hn, hm] at this
    exact_mod_cast this
  rw [hn] at h0
  have := Int.eq_one_of_mul_eq_one_right (by exact_mod_cast h0.le) e
  exact Units.ext (by rw [hn, this]; rfl)

private theorem dc_surj : Function.Surjective (PU.subtype.coprod dg) := by
  intro a
  obtain ⟨r, u, hr, hu, e⟩ := ratAd.1 (pF a)
  have key : ∀ s : ℚˣ, s * s = 1 → IsZU (pF (dg s)) → 0 < ((s : ℚ) : ℝ) * pR a →
      ∃ p, PU.subtype.coprod dg p = a := fun s hs hz hp => by
    refine ⟨(⟨a * dg (s * r⁻¹), ?_, ?_⟩, s * r), ?_⟩
    · rw [map_mul, Units.val_mul, pR_dg, Units.val_mul, Rat.cast_mul, ← mul_assoc, mul_comm _ (((s : ℚ) : ℝ))]
      refine mul_pos hp ?_
      rw [Units.val_inv_eq_inv_val, Rat.cast_pos]
      exact inv_pos.2 hr
    · have : pF (a * dg (s * r⁻¹)) = u * pF (dg s) := by
        rw [map_mul, e, ← pF_dg, map_mul, map_mul, map_inv, map_inv, mul_comm _ u, mul_comm (pF (dg s)),
          mul_assoc, mul_inv_cancel_left]
      rw [this]
      exact zu_mul hu hz
    · change a * dg (s * r⁻¹) * dg (s * r) = a
      rw [mul_assoc, ← map_mul, mul_mul_mul_comm, hs, inv_mul_cancel, mul_one, map_one, mul_one]
  rcases lt_or_gt_of_ne (pR a).ne_zero with h | h
  · refine key (-1) (by simp) ?_ (by simpa using h)
    have : algebraMap ℚ (Af ℚ) (-1) ∈ Ohat ℚ := by rw [map_neg, map_one]; exact neg_mem (one_mem _)
    exact ⟨this, this⟩
  · exact key 1 (by simp) (by rw [map_one, map_one]; exact zu_one) (by simpa using h)

private theorem dc_nhds {M : ℕ} : ∀ᶠ a : Ideles ℚ in 𝓝 1, a ∈ PU ∧
    algebraMap ℚ (Af ℚ) (M : ℚ)⁻¹ * ((pF a : Af ℚ) - (1 : ℤ)) ∈ Ohat ℚ := by
  have c1 : Continuous pF := Continuous.units_map _ continuous_snd
  have c2 : Continuous fun a => (pR a : ℝ) :=
    ((InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal Rat.infinitePlace)).continuous.comp
      ((continuous_apply Rat.infinitePlace).comp continuous_fst)).comp Units.continuous_val
  have c3 : Continuous fun a => (pF a : Af ℚ) := Units.continuous_val.comp c1
  have c4 : Continuous fun a => (((pF a)⁻¹ : (Af ℚ)ˣ) : Af ℚ) := Units.continuous_coe_inv.comp c1
  have c5 : Continuous fun a => algebraMap ℚ (Af ℚ) (M : ℚ)⁻¹ * ((pF a : Af ℚ) - (1 : ℤ)) :=
    continuous_const.mul (c3.sub continuous_const)
  have h2 : ∀ᶠ a : Ideles ℚ in 𝓝 1, 0 < (pR a : ℝ) := (isOpen_lt continuous_const c2).mem_nhds PU.one_mem.1
  have h3 := (isOpen_Ohat.preimage c3).mem_nhds (x := 1) PU.one_mem.2.1
  have h4 := (isOpen_Ohat.preimage c4).mem_nhds (x := 1) PU.one_mem.2.2
  have h5 := (isOpen_Ohat.preimage c5).mem_nhds (x := 1) (by
    rw [Set.mem_preimage, map_one, Units.val_one, Int.cast_one, sub_self, mul_zero]; exact zero_mem (Ohat ℚ))
  filter_upwards [h2, h3, h4, h5] with a a2 a3 a4 a5
  exact ⟨⟨a2, a3, a4⟩, a5⟩

end UpperTheory.V.Af.Nf

theorem UpperTheory.V.Af.Nf.dirChar :
    UpperTheory.V.Af.Nf.DirChar := by
  intro M hM χ
  obtain ⟨ρ, hρ⟩ := dc_red hM
  let j : ↥PU →* ↥(Ohat ℚ) :=
    { toFun := fun p => ⟨pF p, p.2.2.1⟩
      map_one' := Subtype.ext (congrArg Units.val (map_one pF))
      map_mul' := fun a b => Subtype.ext (congrArg Units.val (map_mul pF a.1 b.1)) }
  let ψ : ↥PU →* ℂˣ := (χ.toMonoidHom.comp (ρ.comp j)).toHomUnits
  let φ : ↥PU × ℚˣ →* ℂˣ := ψ⁻¹.comp (MonoidHom.fst _ _)
  have hker : (PU.subtype.coprod dg).ker ≤ φ.ker := fun p hp => by
    have h1 : (p.1 : Ideles ℚ) * dg p.2 = 1 := hp
    have h2 := dc_ker p.2 (by rw [eq_inv_of_mul_eq_one_right h1]; exact PU.inv_mem p.1.2)
    rw [h2, map_one, mul_one] at h1
    change ψ⁻¹ p.1 = 1
    rw [show p.1 = 1 from Subtype.ext h1, map_one]
  let ω : Ideles ℚ →* ℂˣ := MonoidHom.liftOfSurjective _ dc_surj ⟨φ, hker⟩
  have hω : ∀ p, ω (PU.subtype.coprod dg p) = φ p := fun p => MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ p
  have hv : ∀ a (ha : a ∈ PU) (d : ℤ), (∃ y ∈ Ohat ℚ, (pF a : Af ℚ) - d = M * y) → (ω a : ℂ) * χ (d : ZMod M) = 1 := by
    intro a ha d hd
    have h1 : ω (a * dg 1) = (ψ ⟨a, ha⟩)⁻¹ := hω (⟨a, ha⟩, 1)
    rw [map_one, mul_one] at h1
    rw [h1, ← hρ (j ⟨a, ha⟩) d hd]
    exact (ψ ⟨a, ha⟩).inv_mul
  have hone : ∀ a (ha : a ∈ PU), (∃ y ∈ Ohat ℚ, (pF a : Af ℚ) - (1 : ℤ) = M * y) → ω a = 1 := fun a ha h => by
    have := hv a ha 1 h
    rw [Int.cast_one, map_one, mul_one] at this
    exact Units.ext this
  refine ⟨⟨ω, continuous_of_continuousAt_one ω ?_, fun k => ?_⟩, fun t ht => ?_, fun u hu d hd => ?_⟩
  · refine (continuousAt_const (y := (1 : ℂˣ))).congr ?_
    filter_upwards [dc_nhds (M := M)] with a ha
    exact (hone a ha.1 ⟨_, ha.2, by rw [← mul_assoc, mul_comm (M : Af ℚ), dc_inv hM, one_mul]⟩).symm
  · have h1 : ω (1 * dg k) = ψ⁻¹ 1 := hω (1, k)
    rw [map_one, one_mul] at h1
    exact h1
  · exact hone _ ⟨by rw [pR_inf]; exact ht _, by rw [pF_inf]; exact zu_one⟩
      ⟨0, zero_mem _, by rw [pF_inf]; simp⟩
  · exact hv _ ⟨by rw [pR_fin]; exact one_pos, by rw [pF_fin]; exact hu⟩ d (by rw [pF_fin]; exact hd)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.SmCont
section
theorem UpperTheory.V.Af.Nf.smCont :
    UpperTheory.V.Af.Nf.SmCont :=
  UpperTheory.eisenstein_smooth_continuous
end

