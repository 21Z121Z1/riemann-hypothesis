import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.ExistsResQ
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.DirichletGroupPowers.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0004
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.ExistsStrictHenselianAbsolutelyClosedLocalRing
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle0003
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsOnto
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.ExistsInertiaElementAtTwoXiPowFourNeOne
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem not_over_odd {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (h2 : A.valuation ((2 : ℕ) : Ω) < 1) {n : ℕ}
    (hn : Odd n) : ¬ A.valuation (n : Ω) < 1 := by
  intro h
  obtain ⟨k, rfl⟩ := hn
  have h1 : A.valuation (((2 : ℕ) : Ω) * (k : Ω)) < 1 := by
    rw [map_mul]
    exact mul_lt_one_of_lt_of_le h2 ((A.valuation_le_one_iff _).2 (natCast_mem A k))
  have h3 := A.valuation.map_sub_lt h h1
  have e : ((2 * k + 1 : ℕ) : Ω) - ((2 : ℕ) : Ω) * (k : Ω) = 1 := by push_cast; ring
  rw [e, map_one] at h3
  exact lt_irrefl _ h3

private theorem all_mem_range (n : ℕ) (u : (ZMod (2 ^ n))ˣ) : u ∈ (proj 2 (2 ^ n)).range := by
  rw [(projFacts (2 ^ n) 2 Nat.prime_two).2.2.2.2.2.1, MonoidHom.mem_ker]
  have e : ordCompl[2] (2 ^ n) = 1 := by
    rw [Nat.prime_two.factorization_pow, Finsupp.single_eq_same, Nat.div_self (by positivity)]
  have : Subsingleton (ZMod (ordCompl[2] (2 ^ n))) := by rw [e]; infer_instance
  exact Subsingleton.elim _ _

private theorem tot_dvd (k : ℕ) : Nat.totient (2 ^ k) ∣ 2 ^ k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · rw [Nat.totient_prime_pow Nat.prime_two hk]
    simpa using pow_dvd_pow 2 (Nat.sub_le k 1)

private theorem pow_cond {O : Type} [CommRing O] {N : ℕ} [NeZero N] (χ : DirichletCharacter O N) {k : ℕ}
    (h : χ.conductor = 2 ^ k) : χ ^ 2 ^ k = 1 := by
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have h1 : χ.primitiveCharacter ^ Nat.totient χ.conductor = 1 := by
    ext u
    rw [MulChar.pow_apply_coe, ← map_pow, ← Units.val_pow_eq_pow_val, ZMod.pow_totient, Units.val_one, map_one,
      MulChar.one_apply_coe]
  have h2 : Nat.totient χ.conductor ∣ 2 ^ k := by
    rw [h]
    exact tot_dvd k
  obtain ⟨j, hj⟩ := h2
  rw [← χ.changeLevel_primitiveCharacter, ← map_pow, hj, pow_mul, h1, one_pow, map_one]

theorem UpperTheory.V.Ws.exists_inertia_element_at_two_xi_pow_four_ne_one :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), Ctx2 D → ∀ (κ : G ℚ Ω →* c.Oˣ) (j : ℕ), κ ^ l ^ j = 1 → ∀ A : ValuationSubring Ω, A.valuation (2 : Ω) < 1 → ∃ g ∈ Ine (F := ℚ) A, Raw.bar D.Psi g = 1 ∧ κ g = 1 ∧ Raw.bar D.ξ g ^ 4 ≠ 1 := by
  rintro Ω _ _ _ l hl c D ⟨hG, h, t, e, ψ, -, -, -, -, -, -, hψ, -, hp, ξ', ξ₀, hprim, -, -, hξ⟩ κ j hκ A hA0
  have hA : A.valuation ((2 : ℕ) : Ω) < 1 := by rwa [Nat.cast_ofNat]
  have hlp : l.Prime := hl.out
  have hlo : Odd l := hlp.odd_of_ne_two hG.l_odd
  have hom : IsOmT c D.om := ⟨hG.om_pow, fun σ => by
    rw [← residue_eq_zero_iff, map_sub, sub_eq_zero]
    exact hG.om_bar σ⟩
  have h1 : Ine (F := ℚ) A ≤ D.om.ker := ((omT Ω l c).2 D.om hom).2.2.2.2.2.1 _ (not_over_odd _ hA hlo)
  have hq : 0 < h.q := NeZero.pos _
  have ho : 0 < h.o := orderOf_pos _
  obtain ⟨-, b2⟩ := max_le_iff.1 (Nat.le_pow_clog one_lt_two _ : _ ≤ 2 ^ h.nII l ψ)
  have b3 : 2 ^ (c2 ψ + 6) ≤ 2 ^ h.nII l ψ := le_trans (by
      rw [mul_assoc, mul_assoc]
      exact Nat.le_mul_of_pos_right _ (by have := hlp.pos; positivity)) b2
  have p1 := pow_cond (psi2 ψ) (compCond c.O h.N ψ 2 Nat.prime_two).2.2.2.1.symm
  clear b2
  generalize h.nII l ψ = n at *
  generalize c2 ψ = k at *
  have h3 : Nat.Coprime 3 (2 ^ n) := Nat.Coprime.pow_right _ (by norm_num)
  obtain ⟨u, hu, hc⟩ : ZMod.unitOfCoprime 3 h3 ∈ (Ine (F := ℚ) A).map (Chr.cls ℚ Ω (2 ^ n)) := by
    rw [(compIne Ω (2 ^ n) 2 Nat.prime_two _ hA).1]
    exact all_mem_range _ _
  have hξu : D.ξ u = ξ'.toUnitHom (ZMod.unitOfCoprime 3 h3) := by
    have h4 : Chr.cls ℚ Ω 1 u = 1 := Subsingleton.elim _ _
    rw [hξ, MonoidHom.mul_apply, Chr.dirG, Chr.dirG, MonoidHom.comp_apply, MonoidHom.comp_apply, h4, hc, map_one, one_mul]
  have hψu : D.ψ u ^ 2 ^ k = 1 := by
    rw [hψ, ((compIne Ω h.N 2 Nat.prime_two _ hA).2 c.O ψ).1 u hu, Chr.dirG, MonoidHom.comp_apply]
    ext1
    rw [Units.val_pow_eq_pow_val, MulChar.coe_toUnitHom, ← MulChar.pow_apply_coe]
    change (psi2 ψ ^ 2 ^ k) _ = _
    rw [p1, MulChar.one_apply_coe, Units.val_one]
  have hg : u ^ (2 ^ k * l ^ j) ∈ Ine (F := ℚ) A := pow_mem hu _
  refine ⟨u ^ (2 ^ k * l ^ j), hg, ?_, ?_, fun hb => ?_⟩
  · have a1 := hG.om_bar (u ^ (2 ^ k * l ^ j))
    have a2 : D.om (u ^ (2 ^ k * l ^ j)) = 1 := h1 hg
    have a3 : D.ψ (u ^ (2 ^ k * l ^ j)) = 1 := by rw [map_pow, pow_mul, hψu, one_pow]
    simp only [Raw.bar] at a1 ⊢
    rw [a2, Units.val_one, map_one] at a1
    rw [Raw.Psi, Chr.Psi, zpow_natCast, MonoidHom.mul_apply, MonoidHom.pow_apply, a3, mul_one, Units.val_pow_eq_pow_val,
      map_pow (residue c.O), ← a1, one_pow]
  · rw [map_pow, mul_comm, pow_mul, ← MonoidHom.pow_apply κ (l ^ j), hκ, MonoidHom.one_apply, one_pow]
  · have a1 : D.ξ u ^ (2 ^ (k + 2) * l ^ j) = 1 := by
      refine large₂.redOne c (2 ^ n) (Nat.Coprime.pow_right _ ((Nat.coprime_primes hlp Nat.prime_two).2 hG.l_odd)) _ ?_ ?_
      · obtain ⟨m, hm⟩ := tot_dvd n
        have a2 : D.ξ u ^ 2 ^ n = 1 := by
          rw [hξu, ← map_pow]
          have : ZMod.unitOfCoprime 3 h3 ^ (Nat.totient (2 ^ n) * m) = 1 := by
            rw [pow_mul, ZMod.pow_totient, one_pow]
          rw [← hm] at this
          rw [this, map_one]
        rw [← pow_mul, mul_comm, pow_mul, a2, one_pow]
      · simp only [Raw.bar] at hb
        rw [← hb, ← map_pow (residue c.O), ← Units.val_pow_eq_pow_val, map_pow D.ξ, ← pow_mul]
        congr 3
        ring
    have a2 := congrArg Units.val a1
    rw [Units.val_pow_eq_pow_val, hξu, MulChar.coe_toUnitHom, ZMod.coe_unitOfCoprime, Units.val_one] at a2
    have a3 := UpperTheory.two_pow_lt_sq_mul_of_primitive_char_pow_eq_one c.O n ξ' hprim 3 (k + 2) (l ^ j) (by decide) (by norm_num) hlo.pow a2
    have a4 : 2 ^ (k + 6) = 16 * 2 ^ (k + 2) := by ring
    omega
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.QuadEx
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem quadEx_jac (p q : ℕ) (s : ℤˣ) (hq : q.Prime) (h8 : (p : ℤ) ≡ s [ZMOD 8]) (hpq : (p : ℤ) ≡ s [ZMOD q]) :
    jacobiSym q p = 1 := by
  have hp : Odd p := by
    rw [Nat.odd_iff]
    rcases Int.units_eq_one_or s with rfl | rfl <;> simp only [Int.ModEq, Units.val_one, Units.val_neg] at h8 <;> omega
  rcases hq.eq_two_or_odd' with rfl | hq2
  · rw [Nat.cast_ofNat, jacobiSym.at_two hp, ZMod.χ₈_nat_eq_if_mod_eight]
    rcases Int.units_eq_one_or s with rfl | rfl <;> simp only [Int.ModEq, Units.val_one, Units.val_neg] at h8
    · rw [if_neg (by omega), if_pos (by omega)]
    · rw [if_neg (by omega), if_pos (by omega)]
  · have e : jacobiSym p q = jacobiSym s q := jacobiSym.mod_left' hpq
    rcases Int.units_eq_one_or s with rfl | rfl <;> simp only [Int.ModEq, Units.val_one, Units.val_neg] at h8 e
    · rw [jacobiSym.quadratic_reciprocity_one_mod_four' hq2 (by omega), e, jacobiSym.one_left]
    · have hq' := Nat.odd_iff.1 hq2
      rcases (by omega : q % 4 = 1 ∨ q % 4 = 3) with h | h
      · rw [jacobiSym.quadratic_reciprocity_one_mod_four h hp, e, jacobiSym.at_neg_one hq2, ZMod.χ₄_nat_one_mod_four h]
      · rw [jacobiSym.quadratic_reciprocity_three_mod_four h (by omega), e, jacobiSym.at_neg_one hq2,
          ZMod.χ₄_nat_three_mod_four h, neg_neg]

private theorem quadEx_prime (s : ℤˣ) (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) :
    ∃ (p : ℕ) (_ : Fact p.Prime), p ∉ S ∧ p ≠ 2 ∧ quadraticChar (ZMod p) (-1) = s ∧
      ∀ q ∈ S, quadraticChar (ZMod p) (q : ZMod p) = 1 := by
  have h0 : 8 * ∏ q ∈ S, q ≠ 0 := mul_ne_zero (by norm_num) (Finset.prod_ne_zero_iff.2 fun q hq => (hS q hq).ne_zero)
  have hc : IsCoprime (s : ℤ) ((8 * ∏ q ∈ S, q : ℕ) : ℤ) := ⟨(s⁻¹ : ℤˣ), 0, by simp⟩
  obtain ⟨p, hpn, hp, hps⟩ := Nat.forall_exists_prime_gt_and_zmodEq (S.sup id) h0 hc
  have h8 : (p : ℤ) ≡ s [ZMOD 8] := hps.of_dvd (by exact_mod_cast Int.natCast_dvd_natCast.2 (dvd_mul_right 8 _))
  haveI : Fact p.Prime := ⟨hp⟩
  have h2 : p ≠ 2 := by
    rcases Int.units_eq_one_or s with rfl | rfl <;> simp only [Int.ModEq, Units.val_one, Units.val_neg] at h8 <;> omega
  refine ⟨p, inferInstance, fun h => absurd (Finset.le_sup (f := id) h) (not_le.2 hpn), h2, ?_, fun q hq => ?_⟩
  · have e := legendreSym.at_neg_one h2
    rw [legendreSym, Int.cast_neg, Int.cast_one] at e
    rw [e]
    rcases Int.units_eq_one_or s with rfl | rfl <;> simp only [Int.ModEq, Units.val_one, Units.val_neg] at h8 ⊢
    · exact ZMod.χ₄_nat_one_mod_four (by omega)
    · exact ZMod.χ₄_nat_three_mod_four (by omega)
  · have e := quadEx_jac p q s (hS q hq) h8
      (hps.of_dvd (Int.natCast_dvd_natCast.2 ((Finset.dvd_prod_of_mem _ hq).mul_left 8)))
    rwa [← jacobiSym.legendreSym.to_jacobiSym, legendreSym, Int.cast_natCast] at e

private theorem quadEx_cls {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (p q : ℕ) [hp : Fact p.Prime] (γ : G ℚ Ω)
    (h : ((cycZ ℚ Ω p γ : ℤ_[p]ˣ) : ℤ_[p]) = (q : ℤ_[p])) (u : (ZMod p)ˣ) (hu : (u : ZMod p) = q) : UpperTheory.V.Chr.cls ℚ Ω p γ = u := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have : NeZero ((p : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr hp.out.ne_zero⟩
  refine (UpperTheory.V.Chr.clsFacts ℚ Ω p).2.2.1 γ u fun ζ hζ => ?_
  have hζ' : ζ ^ p ^ 1 = 1 := by rwa [pow_one]
  have h1 := cyclotomicCharacter.spec p (MulSemiringAction.toRingAut (Ω ≃ₐ[ℚ] Ω) Ω γ) ζ hζ'
  have h2 : ((cyclotomicCharacter Ω p (MulSemiringAction.toRingAut (Ω ≃ₐ[ℚ] Ω) Ω γ) : ℤ_[p]ˣ) : ℤ_[p]) = (q : ℤ_[p]) := h
  rw [h2, map_natCast, ZMod.val_natCast, ← pow_eq_pow_mod _ hζ'] at h1
  rw [hu, ZMod.val_natCast, ← pow_eq_pow_mod _ hζ]
  exact h1

private theorem quadEx_val {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {p q : ℕ} (h : p.Coprime q)
    (hq : A.valuation (q : Ω) < 1) : ¬ A.valuation (p : Ω) < 1 := fun hp => by
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 h
  have hv : ∀ n : ℤ, A.valuation (n : Ω) ≤ 1 := fun n => (A.valuation_le_one_iff _).mpr (intCast_mem A n)
  have h1 : A.valuation ((a : Ω) * (p : Ω) + (b : Ω) * (q : Ω)) < 1 := by
    refine Valuation.map_add_lt _ ?_ ?_
    · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (hv a)) hp
    · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (hv b)) hq
  have h2 : (a : Ω) * (p : Ω) + (b : Ω) * (q : Ω) = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → Ω) hab
  rw [h2, map_one] at h1
  exact lt_irrefl _ h1

theorem UpperTheory.V.Ws.quadEx :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (s : ℤˣ) (S : Finset ℕ), (∀ q ∈ S, q.Prime) → ∃ (p : ℕ) (η : G ℚ Ω →* ℤˣ), QuadAt p s S η := by
  intro Ω _ _ _ s S hS
  obtain ⟨p, hp, hpS, h2, hs, hq⟩ := quadEx_prime s S hS
  obtain ⟨hopen, -, -, hcc, hine⟩ := Chr.clsFacts ℚ Ω p
  let χ : DirichletCharacter ℤ p := quadraticChar (ZMod p)
  have hval : ∀ g : G ℚ Ω, ((Chr.dirG ℚ Ω χ g : ℤˣ) : ℤ) = quadraticChar (ZMod p) (Chr.cls ℚ Ω p g : (ZMod p)ˣ) := fun g => rfl
  have hle : (Chr.cls ℚ Ω p).ker ≤ (Chr.dirG ℚ Ω χ).ker := fun g hg => by
    rw [MonoidHom.mem_ker] at hg ⊢
    rw [Chr.dirG, MonoidHom.comp_apply, hg, map_one]
  have hopn : IsOpen ((Chr.dirG ℚ Ω χ).ker : Set (G ℚ Ω)) := Subgroup.isOpen_mono hle hopen
  obtain ⟨u, hu⟩ : ∃ u : (ZMod p)ˣ, quadraticChar (ZMod p) u = -1 := by
    obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one (F := ZMod p) (by rwa [ZMod.ringChar_zmod_n])
    have h0 : a ≠ 0 := by
      rintro rfl
      simp at ha
    exact ⟨Units.mk0 a h0, ha⟩
  refine ⟨p, Chr.dirG ℚ Ω χ, hp.out, hpS, hopn, ?_, fun A hA => (hine A hA).trans hle, fun A hA => ?_, fun σ hσ => ?_,
    fun q hqS A hA => ?_⟩
  · obtain ⟨g, hg⟩ := (Chr.clsOnto Ω p).1 u
    have ht : (Chr.dirG ℚ Ω χ).range = ⊤ := by
      refine eq_top_iff.2 fun t _ => ?_
      rcases Int.units_eq_one_or t with rfl | rfl
      · exact one_mem _
      · exact ⟨g, Units.ext (by rw [hval, hg, hu]; rfl)⟩
    rw [Subgroup.index_ker, ht, Subgroup.card_top, Nat.card_eq_fintype_card, Fintype.card_units_int]
  · have hm : u ∈ (proj p p).range := by
      rw [(projFacts p p hp.out).2.2.2.2.2.1, MonoidHom.mem_ker]
      have h1 : ordCompl[p] p = 1 := by
        rw [hp.out.factorization_self, pow_one, Nat.div_self hp.out.pos]
      have : Subsingleton (ZMod (ordCompl[p] p)) := by rw [h1]; infer_instance
      exact Units.ext (Subsingleton.elim _ _)
    rw [← (compIne Ω p p hp.out A hA).1] at hm
    obtain ⟨g, hg, hgu⟩ := hm
    exact ⟨g, hg, Units.ext (by rw [hval, hgu, hu]; rfl)⟩
  · exact Units.ext (by rw [hval, hcc σ hσ, Units.val_neg, Units.val_one, hs])
  · have hne : p ≠ q := fun h => hpS (h ▸ hqS)
    have hc : p.Coprime q := (Nat.coprime_primes hp.out (hS q hqS)).2 hne
    obtain ⟨-, -, γ, -, hD, hγ⟩ := Chr.decCyc Ω q A (hS q hqS) hA
    refine hD.trans (Subgroup.topologicalClosure_minimal _ (sup_le ?_ ((hine A (quadEx_val A hc hA)).trans hle))
      (Subgroup.isClosed_of_isOpen _ hopn))
    rw [Subgroup.zpowers_le, MonoidHom.mem_ker]
    refine Units.ext ?_
    rw [hval, quadEx_cls p q γ (hγ p hne) (ZMod.unitOfCoprime q hc.symm) rfl, ZMod.coe_unitOfCoprime, hq q hqS, Units.val_one]
end

