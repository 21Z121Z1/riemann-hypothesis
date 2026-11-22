import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.DzMatchCut
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0031

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.LpTwistLpTwist
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
  GlobalTheory.PRep GlobalTheory.SplitWeil Module

set_option linter.all false

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section W

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem lpTwist_lpTwist (x : WD h) (α β : Weil h →* ℂˣ) (hα : IsSmooth α) (hβ : IsSmooth β) (hαβ : IsSmooth (α * β)) :
    (x.lpTwist α hα).lpTwist β hβ = x.lpTwist (α * β) hαβ := by
  induction x using WD.ind with
  | hP m a =>
    rw [WD.lpTwist_mk, WD.lpTwist_mk, WD.lpTwist_mk]
    refine WD.sound ⟨LinearEquiv.refl ℂ _, fun σ v => ?_, fun v => rfl⟩
    simp [smul_smul, mul_comm]

variable (h) in

def degDvd (n : ℕ) : Subgroup (Weil h) where
  carrier := {σ | (n : ℤ) ∣ deg σ}
  one_mem' := by simp
  mul_mem' := fun {a b} ha hb => by
    show (n : ℤ) ∣ deg (a * b)
    rw [deg_mul]; exact dvd_add ha hb
  inv_mem' := fun {a} ha => by
    show (n : ℤ) ∣ deg a⁻¹
    rw [deg_inv]; exact (dvd_neg).mpr ha

theorem mem_degDvd {n : ℕ} {σ : Weil h} : σ ∈ degDvd h n ↔ (n : ℤ) ∣ deg σ := Iff.rfl

theorem index_degDvd {n : ℕ} (hn : 0 < n) : (degDvd h n).index = n := by
  haveI : NeZero n := ⟨hn.ne'⟩
  let f : Weil h →* Multiplicative (ZMod n) :=
    (AddMonoidHom.toMultiplicative (Int.castAddHom (ZMod n))).comp (degHom h)
  have hker : f.ker = degDvd h n := by
    ext σ
    rw [MonoidHom.mem_ker, mem_degDvd]
    show Multiplicative.ofAdd ((deg σ : ℤ) : ZMod n) = 1 ↔ _
    rw [← ofAdd_zero, Multiplicative.ofAdd.injective.eq_iff]
    exact ZMod.intCast_zmod_eq_zero_iff_dvd _ _
  have hsurj : Function.Surjective f := by
    intro z
    obtain ⟨k, hk⟩ := ZMod.intCast_surjective (Multiplicative.toAdd z)
    obtain ⟨σ, hσ⟩ := deg_surjective (h := h) k
    refine ⟨σ, ?_⟩
    show Multiplicative.ofAdd ((deg σ : ℤ) : ZMod n) = z
    rw [hσ, hk]; rfl
  rw [← hker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top]
  show Nat.card (ZMod n) = n
  exact Nat.card_zmod n

end W

theorem gs_scaled {g : ℕ} [Fact g.Prime] (ψ₀ : AddChar (ZMod g) Circle) {K : Type} [Field K] [Finite K]
    [Algebra (ZMod g) K] (η : Kˣ →* ℂˣ) (β : Kˣ) :
    ∑ᶠ z : Kˣ, (((η z)⁻¹ : ℂˣ) : ℂ) * (ψ₀ (Algebra.trace (ZMod g) K ((β : K) * z)) : ℂ) =
      (η β : ℂ) * gs ψ₀ η⁻¹ := by
  classical
  haveI := Fintype.ofFinite K
  haveI : Fintype Kˣ := inferInstance
  rw [gs, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Finset.mul_sum]
  rw [← Equiv.sum_comp (Equiv.mulLeft β⁻¹)]
  refine Finset.sum_congr rfl fun z _ => ?_
  have e1 : (β : K) * ((β⁻¹ * z : Kˣ) : K) = (z : K) := by
    rw [Units.val_mul, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
  rw [Equiv.coe_mulLeft, e1]
  simp only [map_mul, map_inv, mul_inv, inv_inv, MonoidHom.inv_apply, Units.val_mul]
  ring

end DiscreteGroups.sglob.DzType

end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.RowFixConj
section
noncomputable section

open Matrix GlobalTheory.LocLanglands

namespace DiscreteGroups.sglob.DzFe

variable {g : ℕ}

theorem colFix_conj [Fact g.Prime] {m k : ℕ} (hk : k < m) (h : GL (Fin (m + 1)) (ZMod g))
    (hh : IsColFix (m - 1 - k) h) :
    ∃ b : GL (Fin m) (ZMod g), (∀ i l : Fin m, i < l → (b : Matrix (Fin m) (Fin m) (ZMod g)) i l = 0) ∧
      corner b = cyc g (m + 1) ^ k * h * (cyc g (m + 1) ^ k)⁻¹ := by
  apply exists_corner
  · intro l
    rw [conj_apply]
    have ha := rot_inv_val hk.le (Fin.last m)
    have hb := rot_inv_val hk.le l
    have hal := ((finRotate (m + 1) ^ k)⁻¹ (Fin.last m)).isLt
    have hll := l.isLt
    rw [Fin.val_last] at ha
    by_cases hb0 : (((finRotate (m + 1) ^ k)⁻¹ l : Fin (m + 1)) : ℕ) = 0
    · rw [hh.2 ((finRotate (m + 1) ^ k)⁻¹ (Fin.last m)) ((finRotate (m + 1) ^ k)⁻¹ l) hb0 (by omega), if_neg]
      intro e
      have := congrArg Fin.val e
      rw [Fin.val_last] at this
      omega
    · rw [hh.1 _ _ hb0]
      by_cases e : l = Fin.last m
      · subst e; rw [if_pos rfl, if_pos rfl]
      · rw [if_neg e, if_neg]
        intro e2; exact e (Equiv.injective _ e2).symm
  · intro i
    rw [conj_apply]
    have hb := rot_inv_val hk.le (Fin.last m)
    have hbl := ((finRotate (m + 1) ^ k)⁻¹ (Fin.last m)).isLt
    rw [Fin.val_last] at hb
    rw [hh.1 ((finRotate (m + 1) ^ k)⁻¹ i) ((finRotate (m + 1) ^ k)⁻¹ (Fin.last m)) (by omega)]
    by_cases e : i = Fin.last m
    · subst e; rw [if_pos rfl, if_pos rfl]
    · rw [if_neg e, if_neg]
      intro e2; exact e (Equiv.injective _ e2)
  · intro i l hil
    rw [conj_apply]
    have ha := rot_inv_val hk.le i.castSucc
    have hb := rot_inv_val hk.le l.castSucc
    have hal := ((finRotate (m + 1) ^ k)⁻¹ i.castSucc).isLt
    have hil' : (i : ℕ) < l := hil
    have hll := l.isLt
    rw [Fin.coe_castSucc] at ha hb
    by_cases hb0 : (((finRotate (m + 1) ^ k)⁻¹ l.castSucc : Fin (m + 1)) : ℕ) = 0
    · exact hh.2 ((finRotate (m + 1) ^ k)⁻¹ i.castSucc) ((finRotate (m + 1) ^ k)⁻¹ l.castSucc) hb0 (by omega)
    · rw [hh.1 _ _ hb0, if_neg]
      intro e2
      have := congrArg Fin.val (Equiv.injective _ e2)
      rw [Fin.coe_castSucc, Fin.coe_castSucc] at this
      omega

theorem rowFix_conj [Fact g.Prime] {m k : ℕ} (hk : k < m) (h : GL (Fin (m + 1)) (ZMod g))
    (hh : IsRowFix (m - 1 - k) h) :
    ∃ b : GL (Fin m) (ZMod g), (∀ i l : Fin m, i < l → (b : Matrix (Fin m) (Fin m) (ZMod g)) i l = 0) ∧
      corner b = cyc g (m + 1) ^ k * h * (cyc g (m + 1) ^ k)⁻¹ := by
  apply exists_corner
  · intro l
    rw [conj_apply]
    have ha := rot_inv_val hk.le (Fin.last m)
    have hal := ((finRotate (m + 1) ^ k)⁻¹ (Fin.last m)).isLt
    rw [Fin.val_last] at ha
    rw [hh.1 ((finRotate (m + 1) ^ k)⁻¹ (Fin.last m)) ((finRotate (m + 1) ^ k)⁻¹ l) (by omega)]
    by_cases e : l = Fin.last m
    · subst e; rw [if_pos rfl, if_pos rfl]
    · rw [if_neg e, if_neg]
      intro e2; exact e (Equiv.injective _ e2).symm
  · intro i
    rw [conj_apply]
    have ha := rot_inv_val hk.le i
    have hb := rot_inv_val hk.le (Fin.last m)
    have hbl := ((finRotate (m + 1) ^ k)⁻¹ (Fin.last m)).isLt
    have hil := i.isLt
    rw [Fin.val_last] at hb
    by_cases ha0 : (((finRotate (m + 1) ^ k)⁻¹ i : Fin (m + 1)) : ℕ) = 0
    · rw [hh.2 ((finRotate (m + 1) ^ k)⁻¹ i) ((finRotate (m + 1) ^ k)⁻¹ (Fin.last m)) ha0 (by omega)
        (by omega), if_neg]
      intro e
      have := congrArg Fin.val e
      rw [Fin.val_last] at this
      omega
    · rw [hh.1 _ _ ha0]
      by_cases e : i = Fin.last m
      · subst e; rw [if_pos rfl, if_pos rfl]
      · rw [if_neg e, if_neg]
        intro e2; exact e (Equiv.injective _ e2)
  · intro i l hil
    rw [conj_apply]
    have ha := rot_inv_val hk.le i.castSucc
    have hb := rot_inv_val hk.le l.castSucc
    have hbl := ((finRotate (m + 1) ^ k)⁻¹ l.castSucc).isLt
    have hil' : (i : ℕ) < l := hil
    have hll := l.isLt
    rw [Fin.coe_castSucc] at ha hb
    by_cases ha0 : (((finRotate (m + 1) ^ k)⁻¹ i.castSucc : Fin (m + 1)) : ℕ) = 0
    · exact hh.2 ((finRotate (m + 1) ^ k)⁻¹ i.castSucc) ((finRotate (m + 1) ^ k)⁻¹ l.castSucc) ha0
        (by omega) (by omega)
    · rw [hh.1 _ _ ha0, if_neg]
      intro e2
      have := congrArg Fin.val (Equiv.injective _ e2)
      rw [Fin.coe_castSucc, Fin.coe_castSucc] at this
      omega

end DiscreteGroups.sglob.DzFe
end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.ValUniformizerPowLt
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.GLp GlobalTheory.GLq GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Whittaker GroundTheory.Automorphic

namespace DiscreteGroups.sglob.DzRed

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem rep_conj {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V) (t u : G) (v : V) :
    π (t * u * t⁻¹) (π t v) = π t (π u v) := by
  simp only [map_mul, Module.End.mul_apply]
  congr 2
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem unipRadical_le_unipB {F : Type} [Field F] {n a : ℕ} {u : GL (Fin n) F}
    (hu : u ∈ GlobalTheory.FiniteGL.unipRadical F (GlobalTheory.FiniteGL.twoBlocks n a)) : u ∈ unipB F (Fin n) := by
  have h := GlobalTheory.FiniteGL.mem_unipRadical.1 hu
  rw [mem_unipB]
  refine ⟨fun p q hqp => ?_, fun p => ?_⟩
  · have := h p q (by
      have : q.val < p.val := hqp
      simp only [GlobalTheory.FiniteGL.twoBlocks]; split_ifs <;> omega)
    rwa [Matrix.sub_apply, Matrix.one_apply_ne (ne_of_gt hqp), sub_zero] at this
  · have := h p p le_rfl
    rwa [Matrix.sub_apply, Matrix.one_apply_eq, sub_eq_zero] at this

theorem val_uniformizer_pow_lt {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (k : ℕ) {y : K} (hy : valuation K y ≤ 1) :
    valuation K ((GLnLocal.uniformizer K : K) ^ (k + 1) * y) < 1 := by
  have hlt := GLnLocal.valuation_uniformizer_lt_one K
  rw [map_mul, map_pow]
  calc valuation K (GLnLocal.uniformizer K : K) ^ (k + 1) * valuation K y
      ≤ valuation K (GLnLocal.uniformizer K : K) ^ (k + 1) := mul_le_of_le_one_right' hy
    _ = valuation K (GLnLocal.uniformizer K : K) ^ k * valuation K (GLnLocal.uniformizer K : K) := pow_succ _ _
    _ ≤ valuation K (GLnLocal.uniformizer K : K) := mul_le_of_le_one_left' (pow_le_one' hlt.le k)
    _ < 1 := hlt

theorem torus_entry {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    {n : ℕ} (d : Fin n → ℤ) (a b : Fin n) (k : ℕ) (hk : d b = d a + ((k + 1 : ℕ) : ℤ)) (y : K) :
    ((Iwasawa.uniformizerUnit K ^ d a : Kˣ) : K) * ((GLnLocal.uniformizer K : K) ^ (k + 1) * y) *
      ((Iwasawa.uniformizerUnit K ^ d b : Kˣ) : K)⁻¹ = y := by
  have hϖ : (GLnLocal.uniformizer K : K) ≠ 0 := fun h =>
    (GLnLocal.irreducible_uniformizer K).ne_zero (Subtype.ext h)
  rw [hk, zpow_add, Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, zpow_natCast,
    Iwasawa.coe_uniformizerUnit]
  have h1 : (GLnLocal.uniformizer K : K) ^ d a ≠ 0 := zpow_ne_zero _ hϖ
  have h2 : (GLnLocal.uniformizer K : K) ^ (k + 1) ≠ 0 := pow_ne_zero _ hϖ
  field_simp

theorem torus_entry' {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    {n : ℕ} (d : Fin n → ℤ) (a b : Fin n) (k : ℕ) (hk : d a = d b + ((k + 1 : ℕ) : ℤ)) (y : K) :
    ((Iwasawa.uniformizerUnit K ^ d a : Kˣ) : K) * y * ((Iwasawa.uniformizerUnit K ^ d b : Kˣ) : K)⁻¹ =
      (GLnLocal.uniformizer K : K) ^ (k + 1) * y := by
  have hϖ : (GLnLocal.uniformizer K : K) ≠ 0 := fun h =>
    (GLnLocal.irreducible_uniformizer K).ne_zero (Subtype.ext h)
  rw [hk, zpow_add, Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, zpow_natCast,
    Iwasawa.coe_uniformizerUnit]
  have h1 : (GLnLocal.uniformizer K : K) ^ d b ≠ 0 := zpow_ne_zero _ hϖ
  field_simp

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {g : ℕ} [Fact g.Prime]
  (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i)
  {ψ₀ : AddChar (ZMod g) Circle} {ψ : AddChar (w.adicCompletion E) Circle}

include hi in
theorem psi_eq_one (hψ : ∀ x : ℤ_[g], ψ (i (x : ℚ_[g])) = ψ₀ (PadicInt.toZMod x)) {y : w.adicCompletion E}
    (hy : valuation (w.adicCompletion E) y < 1) : ψ y = 1 := by
  have h1 : ‖i.symm y‖ < 1 :=
    (DzIso.valuation_lt_iff i hi (i.symm y)).1 (by rwa [RingEquiv.apply_symm_apply])
  let x : ℤ_[g] := ⟨i.symm y, h1.le⟩
  have hx : i (x : ℚ_[g]) = y := RingEquiv.apply_symm_apply i y
  rw [← hx, hψ]
  have h2 : PadicInt.toZMod x = 0 := by
    rw [← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]
    exact h1
  rw [h2, AddChar.map_zero_eq_one]

theorem exists_psi_ne_one (hψ : ∀ x : ℤ_[g], ψ (i (x : ℚ_[g])) = ψ₀ (PadicInt.toZMod x)) (h0 : ψ₀ ≠ 1) :
    ∃ x : ℤ_[g], ψ (i (x : ℚ_[g])) ≠ 1 := by
  obtain ⟨z, hz⟩ : ∃ z, ψ₀ z ≠ 1 := by
    by_contra h
    push Not at h
    exact h0 (AddChar.ext ψ₀ 1 fun z => (h z).trans (AddChar.one_apply z).symm)
  refine ⟨(z.val : ℤ_[g]), ?_⟩
  rw [hψ, map_natCast, ZMod.natCast_zmod_val]
  exact hz

include hi in
theorem fix_of_mem_KOne {n : ℕ} (τ : FDRep ℂ (Gn g n)) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (φ : τ →ₗ[ℂ] V)
    (hφ : ∀ (κ : GL (Fin n) ℤ_[g]) (x : τ),
      φ (τ.ρ (red g n κ) x) = π (Matrix.GeneralLinearGroup.map i.toRingHom (inc g n κ)) (φ x))
    {k : GL (Fin n) (w.adicCompletion E)} (hk : k ∈ KOne (w.adicCompletion E) (Fin n)) (x : τ) :
    π k (φ x) = φ x := by
  obtain ⟨κ, h1, rfl⟩ := DzIso.exists_of_mem_KOne i hi hk
  rw [← hφ, h1, map_one]
  rfl

end DiscreteGroups.sglob.DzRed
end
end

