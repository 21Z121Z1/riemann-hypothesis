import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.HeckeCharacterChoice.Bundle0002

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.HeckeCharacterChoice.IsAntiHecke
section
open NumberField IsDedekindDomain
open scoped nonZeroDivisors

namespace KStar.Choice

open KStar.IdealValuations

abbrev modInt (E : Type*) [Field E] (M : ℕ) : Ideal (𝓞 E) := Ideal.span {(M : 𝓞 E)}

noncomputable def modMap {F E : Type*} [Field F] [Field E] (M : ℕ) (f : 𝓞 F →+* 𝓞 E) :
    (𝓞 F ⧸ modInt F M)ˣ →* (𝓞 E ⧸ modInt E M)ˣ :=
  Units.map (Ideal.quotientMap (I := modInt F M) (modInt E M) f (by
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]
    exact Ideal.mem_span_singleton_self _)).toMonoidHom

variable {E : Type*} [Field E] [NumberField E]

noncomputable def placeRed {M N : ℕ} (h : N ∣ M) (φ : 𝓞 E →+* ZMod N) :
    (𝓞 E ⧸ modInt E M)ˣ →* (ZMod N)ˣ :=
  Units.map (Ideal.Quotient.lift (modInt E M) φ (by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.1 ha
    rw [map_mul, map_natCast, (ZMod.natCast_eq_zero_iff M N).2 h, zero_mul])).toMonoidHom

def HasCondExp (χ : Idele E →* ℂˣ) (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) : Prop :=
  (∀ x ∈ localUnits w, Valued.v (finComp w x - 1) ≤ WithZero.exp (-(n : ℤ)) → χ x = 1) ∧
    ∀ m : ℕ, m < n → ∃ x ∈ localUnits w,
      Valued.v (finComp w x - 1) ≤ WithZero.exp (-(m : ℤ)) ∧ χ x ≠ 1

example (w : HeightOneSpectrum (𝓞 E)) : HasCondExp 1 w 0 := ⟨fun _ _ _ => rfl, by simp⟩

noncomputable def localOrder (χ : Idele E →* ℂˣ) (w : HeightOneSpectrum (𝓞 E)) : ℕ :=
  orderOf (χ.comp (localUnits w).subtype)

section CM

variable [IsCMField E]

noncomputable def antiFin {M : ℕ} (θ : (𝓞 E ⧸ modInt E M)ˣ →* ℂˣ) :
    (𝓞 E ⧸ modInt E M)ˣ →* ℂˣ :=
  θ / θ.comp (modMap M (IsCMField.ringOfIntegersComplexConj E).toRingEquiv.toRingHom)

structure IsAntiHecke {ι : Type*} [Fintype ι] (τ : ι → E →+* ℂ) (e : ι → ℤ)
    (χ : Idele E →* ℂˣ) : Prop where
  continuous : Continuous χ
  principal : ∀ α : Eˣ, χ (principalIdele E α) = 1
  base : χ.comp (ideleMap (maximalRealSubfield E) E) = 1
  infinite : ∀ x : Idele E, (∀ v, finComp v x = 1) →
    χ x = infType conjRatio τ e (infPart E x)

example {ι : Type*} [Fintype ι] (τ : ι → E →+* ℂ) : IsAntiHecke τ 0 1 :=
  ⟨continuous_const, fun _ => rfl, rfl, fun _ _ => by simp [infType]⟩

def TorsionCond {ι : Type*} [Fintype ι] (τ : ι → E →+* ℂ) (e : ι → ℤ) {M : ℕ}
    (θ : (𝓞 E ⧸ modInt E M)ˣ →* ℂˣ) : Prop :=
  ∀ ζ : Units.torsion E, (∏ i, τ i (((ζ : (𝓞 E)ˣ) : 𝓞 E) : E) ^ e i) *
    (θ (Ideal.torsionMapQuot (modInt E M) ζ) : ℂ) = 1

end CM

section Eta

variable (F : Type*) [Field F] [NumberField F] [Algebra F E]

variable {F} (E) in

noncomputable def etaSign (v : HeightOneSpectrum (𝓞 F)) : ℂˣ :=
  if (v.asIdeal.primesOver (𝓞 E)).ncard = 2 then 1 else -1

variable (E) in

noncomputable def etaIdeal : IdealGroup F →* ℂˣ where
  toFun I := ∏ᶠ v : HeightOneSpectrum (𝓞 F),
    etaSign E v ^ FractionalIdeal.count F v (I : FractionalIdeal (𝓞 F)⁰ F)
  map_one' := by simp [FractionalIdeal.count_one]
  map_mul' I J := by
    have h : ∀ I : FractionalIdeal (𝓞 F)⁰ F, Function.HasFiniteMulSupport
        fun v : HeightOneSpectrum (𝓞 F) => etaSign E v ^ FractionalIdeal.count F v I := fun I =>
      (Filter.eventually_cofinite.1 (FractionalIdeal.finite_factors I)).subset
        fun v hv h0 => hv (by simp [h0])
    rw [← finprod_mul_distrib (h _) (h _)]
    refine finprod_congr fun v => ?_
    rw [Units.val_mul, FractionalIdeal.count_mul F _ I.ne_zero J.ne_zero, zpow_add]

noncomputable def signInf : (InfiniteAdeleRing F)ˣ →* ℂˣ :=
  infType phase (fun φ : F →+* ℂ => φ) fun _ => 1

variable (E) in

def EtaRecip : Prop :=
  ∀ a : Fˣ, etaIdeal E F (toPrincipalIdeal (𝓞 F) F a) * signInf F (infDiag F a) = 1

variable (E) in

def IsEta (η : Idele F →* ℂˣ) : Prop :=
  IsHeckeIdele (modInt F 1) (signInf F) 1 η ∧
    HeckeCompat (modInt F 1) (signInf F) 1 η ((etaIdeal E F).comp (primeToMod _).subtype)

end Eta

end KStar.Choice
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.HeckeCharacterChoice.IsOpenIsIdeleResOne
section
open NumberField IsDedekindDomain
open scoped nonZeroDivisors

namespace KStar.Choice

open KStar.IdealValuations

variable {E : Type*} [Field E] [NumberField E] {𝔪 : Ideal (𝓞 E)}

private noncomputable def resExp (𝔪 : Ideal (𝓞 E)) (v : HeightOneSpectrum (𝓞 E)) : ℕ :=
  (Associates.mk v.asIdeal).count (Associates.mk 𝔪).factors

private theorem finite_above (h𝔪 : 𝔪 ≠ ⊥) :
    {v : HeightOneSpectrum (𝓞 E) | 𝔪 ≤ v.asIdeal}.Finite := by
  simpa only [Ideal.dvd_iff_le] using Ideal.finite_factors h𝔪

end KStar.Choice
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.HeckeCharacterChoice.NCField
section
open NumberField

namespace KStar.Choice

noncomputable def rootNu (E : Type*) [Field E] [NumberField E] (l : ℕ) : ℕ :=
  padicValNat l (Units.torsionOrder E)

noncomputable def rootDeg (E : Type*) [Field E] (l : ℕ) : ℕ :=
  Module.finrank E (CyclotomicField l E)

def RamLE (E : Type*) [Field E] [NumberField E] (l e : ℕ) : Prop :=
  ∃ P : Ideal (𝓞 E), P.IsPrime ∧ P.LiesOver (Ideal.span {(l : ℤ)}) ∧ P.ramificationIdx ℤ ≤ e

variable (E : Type*) [Field E] [NumberField E] {l : ℕ}

private theorem rootNu_pos_iff (hl : l.Prime) : 0 < rootNu E l ↔ l ∣ Units.torsionOrder E := by
  have := Fact.mk hl
  unfold rootNu
  rw [Nat.pos_iff_ne_zero, ne_eq, padicValNat.eq_zero_iff]
  have h1 := hl.one_lt
  have h2 := Units.torsionOrder_pos E
  constructor
  · intro h
    by_contra h'
    exact h (Or.inr (Or.inr h'))
  · rintro h (h' | h' | h')
    · omega
    · omega
    · exact h' h

theorem rootDeg_dvd (hl : l.Prime) :
    rootDeg E l ∣ l - 1 ∧ (rootDeg E l = 1 ↔ 0 < rootNu E l) := by
  have := Fact.mk hl
  have : NeZero l := ⟨hl.ne_zero⟩
  have : IsGalois E (CyclotomicField l E) := IsCyclotomicExtension.isGalois {l} E _
  have : FiniteDimensional E (CyclotomicField l E) :=
    IsCyclotomicExtension.finiteDimensional {l} E _
  have hz := IsCyclotomicExtension.zeta_spec l E (CyclotomicField l E)
  have hc : Nat.card (CyclotomicField l E ≃ₐ[E] CyclotomicField l E) = rootDeg E l :=
    IsGalois.card_aut_eq_finrank E _
  refine ⟨?_, ?_, ?_⟩
  · have h := Subgroup.card_dvd_of_injective _ (hz.autToPow_injective E)
    rwa [hc, Nat.card_eq_fintype_card, ZMod.card_units] at h
  · intro h
    rw [rootNu_pos_iff E hl]
    have hb : (⊥ : Subalgebra E (CyclotomicField l E)) = ⊤ :=
      Subalgebra.bot_eq_top_of_finrank_eq_one h
    have hm : IsCyclotomicExtension.zeta l E (CyclotomicField l E) ∈
        (⊥ : Subalgebra E (CyclotomicField l E)) := hb ▸ Algebra.mem_top
    obtain ⟨y, hy⟩ := Algebra.mem_bot.1 hm
    rw [← hy] at hz
    exact Units.dvd_torsionOrder_of_isPrimitiveRoot
      (hz.of_map_of_injective (algebraMap E (CyclotomicField l E)).injective)
  · intro h
    rw [rootNu_pos_iff E hl] at h
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Units.torsion E) l h
    have h1 : IsPrimitiveRoot x l := hx ▸ IsPrimitiveRoot.orderOf x
    have h3 : IsPrimitiveRoot (x : (𝓞 E)ˣ) l :=
      h1.map_of_injective (f := (Units.torsion E).subtype) Subtype.val_injective
    have h4 : IsPrimitiveRoot ((x : (𝓞 E)ˣ) : 𝓞 E) l := IsPrimitiveRoot.coe_units_iff.mpr h3
    have h5 : IsPrimitiveRoot (algebraMap (𝓞 E) E ((x : (𝓞 E)ˣ) : 𝓞 E)) l :=
      h4.map_of_injective (RingOfIntegers.coe_injective)
    generalize algebraMap (𝓞 E) E ((x : (𝓞 E)ˣ) : 𝓞 E) = y at h5
    have h6 : IsPrimitiveRoot (algebraMap E (CyclotomicField l E) y) l :=
      h5.map_of_injective (algebraMap E (CyclotomicField l E)).injective
    rw [← hc, Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun σ τ => h6.autToPow_injective E ?_⟩, ⟨1⟩⟩
    apply Units.ext
    apply ZMod.val_injective
    apply h6.pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
    rw [h6.autToPow_spec E σ, h6.autToPow_spec E τ, σ.commutes, τ.commutes]

private theorem prime_sub_one_le_ramification_degree {E L : Type*} [Field E] [NumberField E] [Field L] [NumberField L]
    [Algebra E L] {l : ℕ} (hl : l.Prime) {z : L} (hz : IsPrimitiveRoot z l) (P : Ideal (𝓞 E))
    [P.IsPrime] [P.LiesOver (Ideal.span {(l : ℤ)})] :
    l - 1 ≤ P.ramificationIdx ℤ * Module.finrank E L := by
  have := Fact.mk hl
  have : NeZero l := ⟨hl.ne_zero⟩
  obtain ⟨⟨Q, hQ1, hQ2⟩⟩ := Ideal.nonempty_primesOver (S := 𝓞 L) P
  have hQ3 : Q.LiesOver (Ideal.span {(l : ℤ)}) := Ideal.LiesOver.trans Q P _
  have hc : IsCyclotomicExtension {l} ℚ (IntermediateField.adjoin ℚ {z}) :=
    hz.intermediateField_adjoin_isCyclotomicExtension ℚ
  set R := Q.under (𝓞 (IntermediateField.adjoin ℚ {z}))
  have hR : R.LiesOver (Ideal.span {(l : ℤ)}) := Ideal.LiesOver.tower_bot Q R _
  have h1 := Ideal.ramificationIdx_below_dvd (R := ℤ) R Q
  rw [IsCyclotomicExtension.Rat.ramificationIdx_eq_of_prime l _ R] at h1
  have h2 := Nat.le_of_dvd (Ideal.ramificationIdx_pos _ _) h1
  rw [Ideal.ramificationIdx_tower (R := ℤ) P Q] at h2
  refine h2.trans (Nat.mul_le_mul_left _ ?_)
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot
    (p := Ideal.span {(l : ℤ)}) (by simpa using hl.ne_zero) P
  have : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hP0
  have := (IsDedekindDomain.primesOver_finite P (𝓞 L)).fintype
  have h3 := Ideal.sum_ramification_inertia_eq_finrank P (𝓞 L)
  rw [← IsFractionRing.finrank_eq (𝓞 E) E (𝓞 L) L] at h3
  rw [← h3]
  refine le_trans ?_ (Finset.single_le_sum (f := fun q : P.primesOver (𝓞 L) =>
    q.1.ramificationIdx (𝓞 E) * q.1.inertiaDeg (𝓞 E)) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ ⟨Q, hQ1, hQ2⟩))
  exact Nat.le_mul_of_pos_right _ (Ideal.inertiaDeg_pos _ _)

theorem RamLE.pred_le {E : Type*} [Field E] [NumberField E] {l e : ℕ} (hl : l.Prime)
    (h : RamLE E l e) : l - 1 ≤ e * rootDeg E l := by
  have : NeZero l := ⟨hl.ne_zero⟩
  obtain ⟨P, hP, hPl, he⟩ := h
  have : NumberField (CyclotomicField l E) := IsCyclotomicExtension.numberField {l} E _
  exact (prime_sub_one_le_ramification_degree hl (IsCyclotomicExtension.zeta_spec l E (CyclotomicField l E)) P).trans
    (Nat.mul_le_mul_right _ he)

theorem rootData_field {S L : Finset ℕ} (hS : ∀ l ∈ S, l.Prime)
    (hunr : ∀ l, l.Prime → l ≠ 2 → l ∉ S → l ∉ L → RamLE E l 1)
    (hL : ∀ l ∈ L, l.Prime ∧ 3 < l ∧ RamLE E l 2) :
    RootData S L (rootNu E) (rootDeg E) where
  prime_small := hS
  nu_two := (rootNu_pos_iff E Nat.prime_two).2 (Units.even_torsionOrder E).two_dvd
  one_lt := fun l hl h0 => by
    obtain ⟨h1, h2⟩ := rootDeg_dvd E hl
    have h3 := hl.two_le
    have h4 : 0 < rootDeg E l := Nat.pos_of_dvd_of_pos h1 (by omega)
    have h5 : rootDeg E l ≠ 1 := fun h => by have := h2.1 h; omega
    omega
  unramified := fun l hl h2 h3 h4 => by
    obtain ⟨h5, h6⟩ := rootDeg_dvd E hl
    have h7 := (hunr l hl h2 h3 h4).pred_le hl
    have h8 := hl.two_le
    have h9 := Nat.le_of_dvd (by omega) h5
    refine ⟨?_, by omega⟩
    by_contra h0
    have := h6.2 (Nat.pos_of_ne_zero h0)
    omega
  large := fun l hm => by
    obtain ⟨hl, h3, h4⟩ := hL l hm
    have h7 := h4.pred_le hl
    refine ⟨?_, by omega⟩
    by_contra h0
    have := (rootDeg_dvd E hl).2.2 (Nat.pos_of_ne_zero h0)
    omega
  small := fun l hm => (rootDeg_dvd E (hS l hm)).1

end KStar.Choice
end

