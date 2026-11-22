import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.CuspCritAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Bundle0002

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.DvdOfOhat
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual
open GlobalTheory.CuspRep UpperTheory.V.Sd CongruenceSubgroup
open scoped Matrix MatrixGroups

namespace UpperTheory.V.Af.Nf

private theorem dvd_of_ohat {M : ℕ} (hM : 1 ≤ M) (n : ℤ) {y : Af ℚ} (hy : y ∈ Ohat ℚ)
    (h : (n : Af ℚ) = M * y) : (M : ℤ) ∣ n := by
  have hM' : (M : ℚ) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  have e : algebraMap ℚ (Af ℚ) ((n : ℚ) / M) = y := by
    have h1 : algebraMap ℚ (Af ℚ) ((M : ℚ)⁻¹) * (M : Af ℚ) = 1 := by
      rw [← map_natCast (algebraMap ℚ (Af ℚ)), ← map_mul, inv_mul_cancel₀ hM', map_one]
    rw [div_eq_inv_mul, map_mul, map_intCast, h, ← mul_assoc, h1, one_mul]
  obtain ⟨m, hm⟩ := ratAd.2.2 _ (e ▸ hy)
  refine ⟨m, ?_⟩
  have : (n : ℚ) = M * m := by rw [← hm]; field_simp
  exact_mod_cast this

private theorem part1 {M : ℕ} (hM : 1 ≤ M) (γ : GL (Fin 2) ℚ) (hγ : toF γ ∈ K1G M) :
    ∃ δ : SL(2, ℤ), δ ∈ Gamma1 M ∧
      ((toR γ).val = δ.1.map (Int.cast : ℤ → ℝ) ∨ (toR γ).val = eps * δ.1.map (Int.cast : ℤ → ℝ)) := by
  obtain ⟨h1, h2, ⟨y, hy, h3⟩, z, hz, h4⟩ := (memK M _).1 hγ
  rw [← map_inv] at h2
  choose A hA using fun a b => ratAd.2.2 (γ a b) (h1 a b)
  choose B hB using fun a b => ratAd.2.2 ((γ⁻¹ : GL (Fin 2) ℚ) a b) (h2 a b)
  have hA' : γ.val = (Matrix.of A).map (Int.castRingHom ℚ) := Matrix.ext hA
  have hB' : (γ⁻¹).val = (Matrix.of B).map (Int.castRingHom ℚ) := Matrix.ext hB
  have hdet : (Matrix.of A).det * (Matrix.of B).det = 1 := by
    have : γ.val.det * (γ⁻¹).val.det = 1 := by rw [← Matrix.det_mul, Units.mul_inv, Matrix.det_one]
    rw [hA', hB', ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← RingHom.map_det, ← RingHom.map_det] at this
    simp only [eq_intCast] at this
    exact_mod_cast this
  have hc : (M : ℤ) ∣ A 1 0 := by
    refine dvd_of_ohat hM _ hy ?_
    rw [← h3, ← map_intCast (algebraMap ℚ (Af ℚ)), ← hA]; rfl
  have hd : (M : ℤ) ∣ A 1 1 - 1 := by
    refine dvd_of_ohat hM _ hz ?_
    rw [← h4, Int.cast_sub, Int.cast_one, ← map_intCast (algebraMap ℚ (Af ℚ)), ← hA]; rfl
  have hc' : ((A 1 0 : ℤ) : ZMod M) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hc
  have hd' : ((A 1 1 : ℤ) : ZMod M) = 1 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hd
    push_cast at this
    exact sub_eq_zero.1 this
  have hR : ∀ a b, (toR γ).val a b = (A a b : ℝ) := fun a b => by
    show Rat.castHom ℝ (γ a b) = _
    rw [hA]; simp
  have key : ∀ δ : SL(2, ℤ), δ 1 0 = A 1 0 → δ 1 1 = A 1 1 → δ ∈ Gamma1 M := by
    intro δ e1 e2
    rw [Gamma1_mem, e1, e2]
    refine ⟨?_, hd', hc'⟩
    have := congrArg (Int.cast : ℤ → ZMod M) δ.det_coe
    rw [Matrix.det_fin_two] at this
    push_cast at this
    change ((δ 0 0 : ℤ) : ZMod M) * (δ 1 1 : ℤ) - (δ 0 1 : ℤ) * (δ 1 0 : ℤ) = 1 at this
    rw [e1, e2, hc', hd'] at this
    simpa using this
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hdet with h | h
  · refine ⟨⟨Matrix.of A, h⟩, key _ rfl rfl, Or.inl (Matrix.ext hR)⟩
  · refine ⟨⟨!![-A 0 0, -A 0 1; A 1 0, A 1 1], ?_⟩, key _ rfl rfl, Or.inr ?_⟩
    · rw [Matrix.det_fin_two] at h
      simp only [Matrix.of_apply] at h
      rw [Matrix.det_fin_two_of]; linear_combination -h
    · ext a b
      rw [hR]
      fin_cases a <;> fin_cases b <;> simp [eps, Matrix.mul_apply, Fin.sum_univ_two]

private theorem part2 {M : ℕ} (hM : 1 ≤ M) (u : (Af ℚ)ˣ) (hu : IsZU u) :
    ∃ (δ : SL(2, ℤ)) (γ : GL (Fin 2) ℚ), δ ∈ Gamma0 M ∧ γ.val = δ.1.map (Int.cast : ℤ → ℚ) ∧
      (toF γ)⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) u ∈ K1G M ∧
      ∃ y ∈ Ohat ℚ, (u : Af ℚ) - (δ 1 1 : ℤ) = M * y := by
  obtain ⟨d, y, hy, hd⟩ := ratAd.2.1 M hM _ hu.1
  obtain ⟨e, z, hz, he⟩ := ratAd.2.1 M hM _ hu.2
  have hI : ∀ n : ℤ, (n : Af ℚ) ∈ Ohat ℚ := fun n => intCast_mem _ n
  have huu : (u : Af ℚ) * (u⁻¹ : (Af ℚ)ˣ) = 1 := u.mul_inv
  obtain ⟨t, ht⟩ : (M : ℤ) ∣ e * d - 1 := by
    refine dvd_of_ohat hM _ (y := -(z * u + e * y)) (neg_mem (add_mem (mul_mem hz hu.1) (mul_mem (hI e) hy))) ?_
    push_cast
    linear_combination (-(u : Af ℚ)) * he - (e : Af ℚ) * hd + huu
  let δ : SL(2, ℤ) := ⟨!![e, t; M, d], by rw [Matrix.det_fin_two_of]; linear_combination ht⟩
  have hδ : ∀ (δ : SL(2, ℤ)) a b, (toF (Matrix.SpecialLinearGroup.mapGL ℚ δ)).val a b = ((δ a b : ℤ) : Af ℚ) := by
    intro δ a b
    show algebraMap ℚ (Af ℚ) (algebraMap ℤ ℚ (δ a b)) = _
    simp
  have e1 : ∀ a b, ((toF (Matrix.SpecialLinearGroup.mapGL ℚ δ))⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) u).val a b
      = (((δ⁻¹ : SL(2, ℤ)) a b : ℤ) : Af ℚ) * u := by
    intro a b
    rw [← map_inv, ← map_inv, Units.val_mul, ← hδ]
    simp
  have e2 : ∀ a b, (((toF (Matrix.SpecialLinearGroup.mapGL ℚ δ))⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) u)⁻¹).val a b
      = (u⁻¹ : (Af ℚ)ˣ) * ((δ a b : ℤ) : Af ℚ) := by
    intro a b
    rw [mul_inv_rev, inv_inv, ← map_inv, Units.val_mul, ← hδ]
    generalize u⁻¹ = v
    simp
  have i10 : (δ⁻¹ : SL(2, ℤ)) 1 0 = -M := by rw [Matrix.SpecialLinearGroup.SL2_inv_expl]; rfl
  have i11 : (δ⁻¹ : SL(2, ℤ)) 1 1 = e := by rw [Matrix.SpecialLinearGroup.SL2_inv_expl]; rfl
  refine ⟨δ, Matrix.SpecialLinearGroup.mapGL ℚ δ, ?_, rfl, (memK M _).2 ⟨fun a b => ?_, fun a b => ?_, ⟨-u, neg_mem hu.1, ?_⟩,
    -(z * u), neg_mem (mul_mem hz hu.1), ?_⟩, y, hy, hd⟩
  · rw [Gamma0_mem]; simp [δ]
  · rw [e1]; exact mul_mem (hI _) hu.1
  · rw [e2]; exact mul_mem hu.2 (hI _)
  · rw [e1, i10]; push_cast; ring
  · rw [e1, i11]; linear_combination (-(u : Af ℚ)) * he + huu

end UpperTheory.V.Af.Nf

theorem UpperTheory.V.Af.Nf.ratK :
    UpperTheory.V.Af.Nf.RatK := fun _ hM =>
  ⟨fun γ hγ => UpperTheory.V.Af.Nf.part1 hM γ hγ, fun u hu => UpperTheory.V.Af.Nf.part2 hM u hu⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.HkCoef
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual UpperTheory.V.Sd

private theorem le_asIdeal_of_normV_dvd_absNorm (w : Pl ℚ) (𝔪 : Ideal (𝓞 ℚ)) (h𝔪 : 𝔪 ≠ ⊥)
    (hd : normV w ∣ Ideal.absNorm 𝔪) : 𝔪 ≤ w.asIdeal := by
  obtain ⟨hp, hspan, -, -⟩ := UpperTheory.V.Af.Nf.places w
  haveI : Fact (normV w).Prime := ⟨hp⟩
  by_contra h
  have htop : w.asIdeal ⊔ 𝔪 = ⊤ := by
    by_contra hne
    exact h (le_sup_right.trans ((w.isMaximal.eq_of_le hne le_sup_left).symm.le))
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp (htop ▸ Submodule.mem_top : (1 : 𝓞 ℚ) ∈ w.asIdeal ⊔ 𝔪)
  have hne : Ideal.absNorm 𝔪 ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hd hne
  haveI : Finite (𝓞 ℚ ⧸ 𝔪) := Nat.finite_of_card_ne_zero hne
  obtain ⟨y, hy⟩ := exists_prime_addOrderOf_dvd_card' (G := 𝓞 ℚ ⧸ 𝔪) (normV w) hd
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hpx : ((normV w : ℕ) : 𝓞 ℚ) * x ∈ 𝔪 := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, map_natCast, ← nsmul_eq_mul, ← hy]
    exact addOrderOf_nsmul_eq_zero _
  have hx : x ∈ 𝔪 := by
    rw [hspan, Ideal.mem_span_singleton] at ha
    obtain ⟨c, rfl⟩ := ha
    have : x = c * (((normV w : ℕ) : 𝓞 ℚ) * x) + b * x := by
      rw [← mul_assoc, mul_comm c, ← add_mul, hab, one_mul]
    rw [this]
    exact 𝔪.add_mem (𝔪.mul_mem_left _ hpx) (𝔪.mul_mem_right _ hb)
  have h0 : (Ideal.Quotient.mk 𝔪 x) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hx
  rw [h0, addOrderOf_zero] at hy
  exact hp.one_lt.ne hy

private theorem coefDiv_icoef_eq_ite_dvd (g : UpperHalfPlane → ℂ) (w : Pl ℚ) (𝔪 : Ideal (𝓞 ℚ)) (h𝔪 : 𝔪 ≠ ⊥) :
    coefDiv (UpperTheory.V.Af.Nf.icoef g) w.asIdeal 𝔪 =
      if normV w ∣ Ideal.absNorm 𝔪 then UpperTheory.V.Af.coef g (Ideal.absNorm 𝔪 / normV w) else 0 := by
  obtain ⟨hp, -, hnorm, -⟩ := UpperTheory.V.Af.Nf.places w
  unfold coefDiv
  split_ifs with h1 h2 h2
  · have hc := h1.choose_spec
    have habs : Ideal.absNorm 𝔪 = normV w * Ideal.absNorm h1.choose := by
      conv_lhs => rw [hc]
      rw [map_mul, hnorm]
    simp only [UpperTheory.V.Af.Nf.icoef]
    rw [habs, Nat.mul_div_cancel_left _ hp.pos]
  · exfalso
    apply h2
    obtain ⟨n, hn⟩ := h1
    rw [hn, map_mul, hnorm]
    exact dvd_mul_right _ _
  · exfalso
    exact h1 (Ideal.dvd_iff_le.mpr (le_asIdeal_of_normV_dvd_absNorm w 𝔪 h𝔪 h2))
  · rfl

private theorem chiI_eq_of_conductor_eq_zero (ω : Formalism.L2.Host.HChar ℚ) (c : Pl ℚ → ℕ) (w : Pl ℚ) (hc : c w = 0) :
    chiI ω c w.asIdeal = ↑(ω.val w) := by
  classical
  have hirr : ∀ v : Pl ℚ, Irreducible (Associates.mk v.asIdeal) :=
    fun v => Associates.irreducible_mk.mpr v.irreducible
  unfold chiI
  rw [finprod_eq_single _ w]
  · simp only [hc, if_true]
    unfold ordI
    rw [Associates.count_self (hirr w), pow_one]
  · intro v hv
    unfold ordI
    rw [Associates.count_eq_zero_of_ne (hirr v) (hirr w), pow_zero]
    intro he
    apply hv
    rw [Associates.mk_eq_mk_iff_associated, associated_iff_eq] at he
    exact HeightOneSpectrum.ext he

theorem UpperTheory.V.Af.Nf.hkCoef :
    UpperTheory.V.Af.Nf.HkCoef := by
  intro k f ω w hw hω 𝔪 h𝔪
  obtain ⟨hp, -, hnorm, hlev⟩ := UpperTheory.V.Af.Nf.places w
  have hl : UpperTheory.V.Af.Nf.lev f.M w = 0 := hlev f.M f.pos hw
  have hn : 1 ≤ Ideal.absNorm 𝔪 := Nat.one_le_iff_ne_zero.mpr (by rwa [Ne, Ideal.absNorm_eq_zero_iff])
  have heig := f.eig (normV w) hp hw (Ideal.absNorm 𝔪) hn
  unfold UpperTheory.V.Sd.hkCoef
  rw [chiI_eq_of_conductor_eq_zero ω _ w hl, coefDiv_icoef_eq_ite_dvd _ w 𝔪 h𝔪, hω]
  simp only [UpperTheory.V.Af.Nf.icoef, map_mul, hnorm, UpperTheory.V.Af.Newform.a]
  exact heig
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.KOpen
section
open NumberField GlobalTheory.CuspRep UpperTheory.V.Sd UpperTheory.V.Af UpperTheory.V.Af.Nf

theorem UpperTheory.V.Af.Nf.kOpen :
    UpperTheory.V.Af.Nf.KOpen := by
  intro M hM
  refine ⟨Subgroup.isOpen_mono (H₁ := KLev ℚ 2 M) (fun g hg => ?_) (isOpen_KLev hM), fun u hu x hx => ?_⟩
  · obtain ⟨ha, hb, hc⟩ := mem_KLev.1 hg
    refine (memK M g).2 ⟨ha, hb, ?_, ?_⟩
    · simpa using hc 1 0
    · simpa using hc 1 1
  · refine (memK M _).2 ⟨?_, ?_, ⟨0, zero_mem _, ?_⟩, ⟨0, zero_mem _, ?_⟩⟩
    · refine Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2 ⟨hu.1, hx⟩, Fin.forall_fin_two.2 ⟨zero_mem _, one_mem _⟩⟩
    · refine Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2 ⟨hu.2, neg_mem (mul_mem hu.2 hx)⟩,
        Fin.forall_fin_two.2 ⟨zero_mem _, one_mem _⟩⟩
    · exact (mul_zero _).symm
    · exact (sub_self (1 : Af ℚ)).trans (mul_zero _).symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.NslInv
section
open CongruenceSubgroup
open UpperHalfPlane hiding I
open scoped Matrix MatrixGroups ModularForm

namespace UpperTheory.V.Af.Nf

private def cj (δ : SL(2, ℤ)) : SL(2, ℤ) :=
  ⟨!![δ 0 0, -δ 0 1; -δ 1 0, δ 1 1], by
    have h := δ.det_coe
    rw [Matrix.det_fin_two] at h
    rw [Matrix.det_fin_two_of]
    linear_combination h⟩

private theorem eps_mul_cj (δ : SL(2, ℤ)) :
    eps * δ.1.map (Int.cast : ℤ → ℝ) = (cj δ).1.map (Int.cast : ℤ → ℝ) * eps := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eps, cj, Matrix.mul_apply, Fin.sum_univ_two]

private theorem det_map (δ : SL(2, ℤ)) : (δ.1.map (Int.cast : ℤ → ℝ)).det ≠ 0 := by
  have h := (Int.castRingHom ℝ).map_det δ.1
  rw [δ.det_coe, map_one] at h
  have h' : (δ.1.map (Int.cast : ℤ → ℝ)).det = 1 := h.symm
  rw [h']
  exact one_ne_zero

private theorem pos_case (k : ℕ) (f : ℍ → ℂ) (x : Matrix (Fin 2) (Fin 2) ℝ) (hx : 0 < x.det) (δ : SL(2, ℤ)) (c : ℂ)
    (h : f ∣[(k : ℤ)] δ = c • f) : nsl k f (δ.1.map (Int.cast : ℤ → ℝ) * x) = c • nsl k f x := by
  rw [← (nslMul k f).1 _ x (det_map δ) hx, (nslSl k f).1 δ, h, (nslMul k f).2.2.2]

private theorem gen_case (k : ℕ) (f : ℍ → ℂ) (x : Matrix (Fin 2) (Fin 2) ℝ) (hx : x.det ≠ 0) (δ : SL(2, ℤ)) (c : ℂ)
    (h : f ∣[(k : ℤ)] δ = c • f) (h' : f ∣[(k : ℤ)] (cj δ) = c • f) :
    nsl k f (δ.1.map (Int.cast : ℤ → ℝ) * x) = c • nsl k f x := by
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · have hd : 0 < (eps * x).det := by
      rw [Matrix.det_mul]
      have : eps.det = -1 := by simp [eps]
      rw [this]
      linarith
    rw [← (nslMul k f).2.1, ← Matrix.mul_assoc, eps_mul_cj, Matrix.mul_assoc, pos_case k f _ hd _ c h',
      (nslMul k f).2.1]
  · exact pos_case k f x hpos δ c h

end UpperTheory.V.Af.Nf

theorem UpperTheory.V.Af.Nf.nslInv :
    UpperTheory.V.Af.Nf.NslInv := by
  intro k M f x hx
  refine ⟨fun hf δ hδ => ?_, fun χ hχ δ hδ => ?_⟩
  · have hδ' : cj δ ∈ Gamma1 M := by
      rw [Gamma1_mem] at hδ ⊢
      obtain ⟨h1, h2, h3⟩ := hδ
      refine ⟨?_, ?_, ?_⟩
      · exact h1
      · exact h2
      · show (((-δ 1 0 : ℤ)) : ZMod M) = 0
        rw [Int.cast_neg, h3, neg_zero]
    have := gen_case k f x hx δ 1 (by rw [one_smul]; exact hf δ hδ) (by rw [one_smul]; exact hf _ hδ')
    rwa [one_smul] at this
  · have hδ' : cj δ ∈ Gamma0 M := by
      rw [Gamma0_mem] at hδ ⊢
      show (((-δ 1 0 : ℤ)) : ZMod M) = 0
      rw [Int.cast_neg, hδ, neg_zero]
    exact gen_case k f x hx δ _ (hχ δ hδ) (hχ _ hδ')
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.SatHol
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd Matrix
open GlobalTheory.CuspRep (finId locGL finGL)

private theorem fin_scalar {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ) :
    finGL F 2 (locGL F 2 w (GeneralLinearGroup.scalar (Fin 2) x)) = GeneralLinearGroup.scalar (Fin 2) (localIdele F w x) := by
  have h := GlobalTheory.CuspRep.finId_det_locGL w (GeneralLinearGroup.scalar (Fin 1) x)
  rw [locGL, GlobalTheory.CuspRep.cornerGL_scalar] at h ⊢
  rw [finGL, GlobalTheory.CuspRep.cornerGL_scalar]
  congr 1
  exact (congrArg (finId F) (GlobalTheory.CuspRep.CG.det_oneByOne _)).symm.trans
    (h.trans (congrArg (localIdele F w) (GlobalTheory.CuspRep.CG.det_oneByOne _)))

private theorem roots (s : ℂ) (p : ℂˣ) : ∃ α β : ℂˣ, (α : ℂ) + β = s ∧ α * β = p := by
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq (s ^ 2 - 4 * (p : ℂ)) (n := 2) two_pos
  have h : (s + d) / 2 * ((s - d) / 2) = p := by linear_combination (-1 / 4 : ℂ) * hd
  have h0 := h ▸ p.ne_zero
  refine ⟨Units.mk0 _ (left_ne_zero_of_mul h0), Units.mk0 _ (right_ne_zero_of_mul h0), ?_, Units.ext h⟩
  simp only [Units.val_mk0]
  ring

theorem UpperTheory.V.Af.Nf.satHol :
    UpperTheory.V.Af.Nf.SatHol := by
  intro F _ _ _ k c ω φ hφ h0 w lam hw hU
  have hq : (0 : ℝ) < normV w :=
    Nat.cast_pos.2 (zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm w))
  have hne : ∀ t : ℝ, (((normV w : ℝ) ^ t : ℝ) : ℂ) ≠ 0 := fun t =>
    Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos hq t).ne'
  obtain ⟨α, β, h1, h2⟩ := roots (lam / (((normV w : ℝ) ^ (((k : ℝ) - 1) / 2) : ℝ) : ℂ)) (ω.val w)
  have h3 : (((normV w : ℝ) ^ (((k : ℝ) - 1) / 2) : ℝ) : ℂ) * ((α : ℂ) + β) = lam := by
    rw [h1, mul_div_cancel₀ _ (hne _)]
  refine ⟨α, β, UpperTheory.V.Af.Nf.satOfU F w _ _ φ α β h0 (hw ▸ hφ.level w) ?_ ?_, h3, h2⟩
  · refine smul_right_injective _ (hne ((k : ℝ) / 2 - 1)) (hU.trans ?_)
    dsimp only
    rw [smul_smul, ← mul_assoc, ← Complex.ofReal_mul, ← Real.rpow_add hq, ← h3]
    congr 4
    ring
  · rw [h2]
    refine Subtype.ext (funext fun g => ?_)
    change φ.1 (g * finGL F 2 (locGL F 2 w _)) = _
    rw [fin_scalar, ← GlobalTheory.CuspRep.scalar_comm, hφ.cent]
    rfl
end

