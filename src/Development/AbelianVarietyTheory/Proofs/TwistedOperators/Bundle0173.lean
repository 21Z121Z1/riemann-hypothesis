import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0140
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0163
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0164
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0072
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0101
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0161
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0155
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0162
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0147
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0137
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0037
import Development.AbelianVarietyTheory.Definitions.Foundations.ContinuousOfMemCcSmooth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FactTypePrime
import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridHeckeCharactersExist
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.ConstRatio

noncomputable section
namespace GlobalTheory.HeckeCharsOfSquare

variable {D : D7}

theorem isHeckeChar_mul {χ ψ : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) (hψ : IsHeckeChar D ψ) :
    IsHeckeChar D (χ * ψ) :=
  ⟨hχ.1.mul hψ.1, fun x => by rw [MonoidHom.mul_apply, hχ.2 x, hψ.2 x, mul_one]⟩

theorem isHeckeChar_inv {χ : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) : IsHeckeChar D χ⁻¹ :=
  ⟨hχ.1.inv, fun x => by rw [MonoidHom.inv_apply, hχ.2 x, inv_one]⟩

theorem isHeckeChar_div {χ ψ : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) (hψ : IsHeckeChar D ψ) :
    IsHeckeChar D (χ / ψ) := by
  rw [div_eq_mul_inv]; exact isHeckeChar_mul hχ (isHeckeChar_inv hψ)

theorem isHeckeChar_pow {χ : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) (n : ℕ) : IsHeckeChar D (χ ^ n) :=
  ⟨hχ.1.pow n, fun x => by rw [MonoidHom.pow_apply, hχ.2 x, one_pow]⟩

theorem resEta_of_mod {χ : (AE D)ˣ →* Circle} {a b : ℕ} (h : ResEta D χ a) (hab : a % 2 = b % 2) : ResEta D χ b := by
  refine ⟨h.1, fun η hη x => ?_⟩
  rw [h.2 η hη x, ← Nat.mod_add_div a 2, ← Nat.mod_add_div b 2, pow_add, pow_add, pow_mul, pow_mul,
    GlobalTheory.EtaTildeOddParity.isEta_sq D η hη x, one_pow, one_pow, hab]

theorem resEta_mul {χ ψ : (AE D)ˣ →* Circle} {a b : ℕ} (hχ : ResEta D χ a) (hψ : ResEta D ψ b) :
    ResEta D (χ * ψ) (a + b) :=
  ⟨hχ.1, fun η hη x => by rw [MonoidHom.mul_apply, hχ.2 η hη x, hψ.2 η hη x, pow_add]⟩

theorem resEta_inv {χ : (AE D)ˣ →* Circle} {a : ℕ} (hχ : ResEta D χ a) : ResEta D χ⁻¹ a := by
  refine ⟨hχ.1, fun η hη x => ?_⟩
  rw [MonoidHom.inv_apply, hχ.2 η hη x, ← inv_pow]
  have h2 := GlobalTheory.EtaTildeOddParity.isEta_sq D η hη x
  rw [inv_eq_of_mul_eq_one_right (by rw [← sq, h2] : η x * η x = 1)]

theorem resEta_pow {χ : (AE D)ˣ →* Circle} {a : ℕ} (hχ : ResEta D χ a) (k : ℕ) : ResEta D (χ ^ k) (a * k) :=
  ⟨hχ.1, fun η hη x => by rw [MonoidHom.pow_apply, hχ.2 η hη x, pow_mul]⟩

theorem resEta_div {χ ψ : (AE D)ˣ →* Circle} {a b : ℕ} (hχ : ResEta D χ a) (hψ : ResEta D ψ b) :
    ResEta D (χ / ψ) (a + b) := by
  rw [div_eq_mul_inv]; exact resEta_mul hχ (resEta_inv hψ)

theorem resEta_of_att {μ η : (AE D)ˣ →* Circle} {a b : ℕ} (ha : ResEta D (Lift.attChr μ η a) a)
    (hb : ResEta D (Lift.attChr μ η b) b) (hab : Odd (a + b)) : ResEta D μ 0 ∧ ResEta D η 1 := by
  rcases Nat.even_or_odd a with hae | hao
  · have hbo : Odd b := (Nat.odd_add'.1 hab).2 hae
    have hna : ¬ Odd a := Nat.not_odd_iff_even.2 hae
    simp only [Lift.attChr, hna, if_false] at ha
    simp only [Lift.attChr, hbo, if_true] at hb
    have hμ : ResEta D μ 0 := resEta_of_mod ha (by rw [Nat.even_iff.1 hae])
    refine ⟨hμ, resEta_of_mod (χ := η) (a := a + b) ?_ (by rw [Nat.odd_iff.1 hab])⟩
    have e : η = μ / (μ * η⁻¹) := by rw [div_mul_eq_div_div, div_self', one_div, inv_inv]
    rw [e]; exact resEta_div ha hb
  · have hbe : Even b := by
      rcases Nat.even_or_odd b with h | h
      · exact h
      · exact absurd hab (Nat.not_odd_iff_even.2 (hao.add_odd h))
    have hnb : ¬ Odd b := Nat.not_odd_iff_even.2 hbe
    simp only [Lift.attChr, hao, if_true] at ha
    simp only [Lift.attChr, hnb, if_false] at hb
    have hμ : ResEta D μ 0 := resEta_of_mod hb (by rw [Nat.even_iff.1 hbe])
    refine ⟨hμ, resEta_of_mod (χ := η) (a := b + a) ?_ (by rw [add_comm, Nat.odd_iff.1 hab])⟩
    have e : η = μ / (μ * η⁻¹) := by rw [div_mul_eq_div_div, div_self', one_div, inv_inv]
    rw [e]; exact resEta_div hb ha

end GlobalTheory.HeckeCharsOfSquare

namespace GlobalTheory.HeckeCharsOfSquare

end GlobalTheory.HeckeCharsOfSquare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharacterFiniteOrderValuesInField
section
namespace HeckeCharacterValueBounds
section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace ComplexOrder

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.ConstRatio

namespace GlobalTheory.CompanionTheory.CharValues

open Formalism.L2.Host

section General

variable {E : Type} [Field E] [NumberField E]

theorem exp_lt_one (m : ℕ) : (WithZero.exp (-((m : ℤ) + 1)) : WithZero (Multiplicative ℤ)) < 1 := by
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
  omega

private theorem valued_v_algebraMap_adicCompletion' (v : HeightOneSpectrum (𝓞 E)) (a : E) :
    Valued.v (algebraMap E (v.adicCompletion E) a) = v.valuation E a := by
  first
    | exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v a
    | (rw [HeightOneSpectrum.algebraMap_adicCompletion]; exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v a)

theorem locK_eq_of_level (χ : HChar E) {v : HeightOneSpectrum (𝓞 E)} {m : ℕ} (h : χ.LevelLe v m) (x y : Eˣ)
    (hxy : v.valuation E ((y : E) - x) ≤ WithZero.exp (-((m : ℤ) + 1)) * v.valuation E (x : E)) :
    χ.locK v y = χ.locK v x := by
  have hx0 : (x : E) ≠ 0 := x.ne_zero
  have hv0 : v.valuation E (x : E) ≠ 0 := ((v.valuation E).ne_zero_iff).mpr hx0

  have hd : ((y * x⁻¹ : Eˣ) : E) - 1 = ((y : E) - x) * (x : E)⁻¹ := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val, sub_mul, mul_inv_cancel₀ hx0]
  have hle : v.valuation E (((y * x⁻¹ : Eˣ) : E) - 1) ≤ WithZero.exp (-((m : ℤ) + 1)) := by
    rw [hd, map_mul, map_inv₀]
    calc v.valuation E ((y : E) - x) * (v.valuation E (x : E))⁻¹
        ≤ WithZero.exp (-((m : ℤ) + 1)) * v.valuation E (x : E) * (v.valuation E (x : E))⁻¹ := by
          first | gcongr | exact mul_le_mul_right' hxy _
      _ = WithZero.exp (-((m : ℤ) + 1)) := by rw [mul_assoc, mul_inv_cancel₀ hv0, mul_one]
  have hlt : v.valuation E (((y * x⁻¹ : Eˣ) : E) - 1) < v.valuation E 1 := by
    rw [map_one]
    exact lt_of_le_of_lt hle (exp_lt_one m)
  have hu : v.valuation E ((y * x⁻¹ : Eˣ) : E) = 1 := ((v.valuation E).map_eq_of_sub_lt hlt).trans (map_one _)

  have hA : IsUnitAt v (atFin v (y * x⁻¹)) := by
    show Valued.v (algebraMap E (v.adicCompletion E) ((y * x⁻¹ : Eˣ) : E)) = 1
    rw [valued_v_algebraMap_adicCompletion']
    exact hu
  have hB : Valued.v (((atFin v (y * x⁻¹) : (v.adicCompletion E)ˣ) : v.adicCompletion E) - 1) ≤
      WithZero.exp (-(m : ℤ)) := by
    show Valued.v (algebraMap E (v.adicCompletion E) ((y * x⁻¹ : Eˣ) : E) - 1) ≤ _
    rw [← map_one (algebraMap E (v.adicCompletion E)), ← map_sub, valued_v_algebraMap_adicCompletion']
    exact le_trans hle (WithZero.exp_le_exp.mpr (by omega))
  have h1 : χ.locK v (y * x⁻¹) = 1 := h _ hA hB
  calc χ.locK v y = χ.locK v (y * x⁻¹ * x) := by rw [mul_assoc, inv_mul_cancel, mul_one]
    _ = χ.locK v x := by rw [map_mul, h1, one_mul]

theorem exists_approx (S : Finset (HeightOneSpectrum (𝓞 E))) (t : HeightOneSpectrum (𝓞 E) → 𝓞 E) (m : HeightOneSpectrum (𝓞 E) → ℕ)
    (ht : ∀ v, t v ≠ 0) : ∃ y : 𝓞 E, ∀ v ∈ S,
      v.valuation E ((y : E) - (t v : E)) ≤ WithZero.exp (-((m v : ℤ) + 1)) * v.valuation E (t v : E) := by
  classical

  have hk : ∀ v : HeightOneSpectrum (𝓞 E),
      WithZero.exp (WithZero.log (v.intValuation (t v))) = v.intValuation (t v) :=
    fun v => WithZero.exp_log (v.intValuation_ne_zero _ (ht v))
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := S) (fun v => v.asIdeal)
    (fun v => ((m v : ℤ) + 1 - WithZero.log (v.intValuation (t v))).toNat)
    (fun v _ => Ideal.prime_of_isPrime v.ne_bot v.isPrime)
    (fun v _ w _ hvw h => hvw (HeightOneSpectrum.ext h))
    (fun v => t v.1)
  refine ⟨y, fun v hv => ?_⟩
  have h1 := (v.intValuation_le_pow_iff_mem (y - t v) _).mpr (hy v hv)
  have h2 : v.valuation E ((y : E) - (t v : E)) = v.intValuation (y - t v) := by
    have h := v.valuation_of_algebraMap (K := E) (y - t v)
    first
      | (push_cast at h; exact h)
      | exact h
      | simpa using h
  have h3 : v.valuation E (t v : E) = v.intValuation (t v) := v.valuation_of_algebraMap (K := E) (t v)
  rw [h2, h3, ← hk v, ← WithZero.exp_add]
  refine le_trans h1 (WithZero.exp_le_exp.mpr ?_)
  have := Int.self_le_toNat ((m v : ℤ) + 1 - WithZero.log (v.intValuation (t v)))
  omega

private theorem exp_neg_succ_mul_lt_self (m : ℕ) {b : WithZero (Multiplicative ℤ)} (hb : b ≠ 0) :
    WithZero.exp (-((m : ℤ) + 1)) * b < b := by
  rw [← WithZero.exp_log hb, ← WithZero.exp_add, WithZero.exp_lt_exp]
  omega

theorem locK_mem (χ : HChar E) (G : Subgroup ℂˣ) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (hunr : ∀ v, v ∉ T → χ.UnrAt v) (hval : ∀ v, v ∉ T → χ.val v ∈ G)
    (hinf : ∀ k, χ.inf k ∈ G) (P : HeightOneSpectrum (𝓞 E)) (x : Eˣ) : χ.locK P x ∈ G := by
  classical
  choose m hm using GlobalTheory.Mem.UnrAe.exists_levelLe χ

  have key : ∀ a : 𝓞 E, a ≠ 0 → ∀ k : Eˣ, (k : E) = (a : E) → χ.locK P k ∈ G := by
    intro a ha k hk

    obtain ⟨y, hy⟩ := exists_approx (insert P T) (fun v => if v = P then a else 1) m
      (fun v => by by_cases h : v = P <;> simp [h, ha])
    have hyP : P.valuation E ((y : E) - (a : E)) ≤ WithZero.exp (-((m P : ℤ) + 1)) * P.valuation E (a : E) := by
      simpa using hy P (Finset.mem_insert_self P T)
    have hva : P.valuation E (a : E) ≠ 0 := by
      rw [(P.valuation E).ne_zero_iff]
      intro h0
      exact ha (RingOfIntegers.ext (by rw [h0]; rfl))
    have hy0 : (y : E) ≠ 0 := by
      intro h0
      rw [h0, zero_sub, Valuation.map_neg] at hyP
      exact absurd hyP (not_le.mpr (exp_neg_succ_mul_lt_self (m P) hva))
    set ky : Eˣ := Units.mk0 (y : E) hy0 with hky
    have hone : ∀ v ∈ insert P T, v ≠ P → χ.locK v ky = 1 := by
      intro v hv hvP
      have h1 : v.valuation E ((ky : E) - ((1 : Eˣ) : E)) ≤
          WithZero.exp (-((m v : ℤ) + 1)) * v.valuation E ((1 : Eˣ) : E) := by
        simpa [hvP, hky] using hy v hv
      rw [locK_eq_of_level χ (hm v) 1 ky h1, map_one]
    have hPk : χ.locK P ky = χ.locK P k := by
      apply locK_eq_of_level χ (hm P) k ky
      simpa [hky, hk] using hyP

    have hS : ∀ v, v ∉ insert P T → χ.UnrAt v := fun v hv => hunr v (fun h => hv (Finset.mem_insert_of_mem h))
    have hPR := GlobalTheory.TypeValues.productRule χ (insert P T) hS ky
    rw [Finset.prod_eq_single_of_mem P (Finset.mem_insert_self P T) hone] at hPR
    have hF : (∏ᶠ (v : HeightOneSpectrum (𝓞 E)) (_ : v ∉ insert P T), χ.val v ^ ordF v ky) ∈ G :=
      finprod_induction (· ∈ G) G.one_mem (fun _ _ => G.mul_mem) fun v =>
        finprod_induction (· ∈ G) G.one_mem (fun _ _ => G.mul_mem) fun hv =>
          G.zpow_mem (hval v fun h => hv (Finset.mem_insert_of_mem h)) _
    have h1 := G.one_mem
    rw [← hPR] at h1
    rw [← hPk]
    exact (G.mul_mem_cancel_left (hinf ky)).mp ((G.mul_mem_cancel_right hF).mp h1)

  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (𝓞 E) (x : E)
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hinj : Function.Injective (algebraMap (𝓞 E) E) := IsFractionRing.injective (𝓞 E) E
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div] at hab
    exact x.ne_zero hab.symm
  have haE : algebraMap (𝓞 E) E a ≠ 0 := (map_ne_zero_iff _ hinj).mpr ha0
  have hbE : algebraMap (𝓞 E) E b ≠ 0 := (map_ne_zero_iff _ hinj).mpr hb0
  have hx : x = Units.mk0 _ haE * (Units.mk0 _ hbE)⁻¹ := by
    ext
    rw [← hab, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, Units.val_mk0, div_eq_mul_inv]
  rw [hx, map_mul, map_inv]
  exact G.mul_mem (key a ha0 _ rfl) (G.inv_mem (key b hb0 _ rfl))

end General

theorem main : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (n : ℕ) (L : Type) [Field L] (σ : L →+* ℂ), ChrEq c χ → 0 < n → χ.OrderDvd n → χ.ValuesIn 0 σ → ∀ x : (AE D)ˣ, ∃ y : Lˣ, σ y = (c x : ℂ) := by
  intro D c χ n L _ σ hc hn ho hv x
  classical
  have hfin := GlobalTheory.Mem.UnrAe.finite_ramified χ
  have hunr : ∀ v, v ∉ hfin.toFinset → χ.UnrAt v := fun v hv => by
    by_contra h
    exact hv (hfin.mem_toFinset.mpr h)
  have hval : ∀ v, v ∉ hfin.toFinset → χ.val v ∈ GlobalTheory.TameVal.unitsIn σ.fieldRange := by
    intro v hv'
    obtain ⟨y, hy⟩ := hv v (hunr v hv')
    have hw : χ.valTw 0 v = ((χ.val v : ℂˣ) : ℂ) := by simp [HChar.valTw]
    exact RingHom.mem_fieldRange.mpr ⟨y, hy.trans hw⟩
  have hinf : ∀ k, χ.inf k ∈ GlobalTheory.TameVal.unitsIn σ.fieldRange := fun k => by
    rw [GlobalTheory.TypeValues.inf_eq_one χ hn ho k]
    exact Subgroup.one_mem _
  have hM : ∀ P k, ((χ.locK P k : ℂˣ) : ℂ) ∈ σ.fieldRange := fun P k =>
    locK_mem χ (GlobalTheory.TameVal.unitsIn σ.fieldRange) hfin.toFinset hunr hval hinf P k
  obtain ⟨y, hy⟩ := RingHom.mem_fieldRange.mp (GlobalTheory.TwistValues.char_mem c χ hc hn ho σ.fieldRange hM x)
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [map_zero] at hy
    exact Circle.coe_ne_zero _ hy.symm
  exact ⟨Units.mk0 y hy0, hy⟩

end GlobalTheory.CompanionTheory.CharValues

end

end

end HeckeCharacterValueBounds
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.ConstRatio
theorem _root_.GlobalTheory.Adopt.heckeCharacter_finiteOrder_values_in_field : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (n : ℕ) (L : Type) [Field L] (σ : L →+* ℂ), ChrEq c χ → 0 < n → χ.OrderDvd n → χ.ValuesIn 0 σ → ∀ x : (AE D)ˣ, ∃ y : Lˣ, σ y = (c x : ℂ) := by
  intro D c χ n L _ σ h₁ h₂ h₃ h₄ x
  exact HeckeCharacterValueBounds.GlobalTheory.CompanionTheory.CharValues.main D c χ n L σ h₁ h₂ h₃ h₄ x

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergDerivativeZeroOrEmptyEqZero
section
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open scoped Classical

namespace GlobalTheory.HeisDerivZero

theorem evI_surj {F : Type} [Field F] [NumberField F] (y : mixedEmbedding.mixedSpace F) : ∃ a : AF F, evI F a = y :=
  ⟨((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm y, 0), (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y⟩

theorem actsD_eq_zero {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ)
    (g h : SInf F (Fin n × Fin d)) (u : Matrix (Fin n) (Fin d) (AE F E))
    (hA : ActsD (evI F) (M.heisLine ψ u) g h) (hc : g = 0 ∨ IsEmpty (Fin n × Fin d)) : h = 0 := by
  have hR : Rest (evI F) g (fun _ => 1) := by
    refine ⟨fun _ _ _ => rfl, ?_⟩
    rcases hc with rfl | hE
    · have : tens (evI F) (⇑(0 : SInf F (Fin n × Fin d))) (fun _ => 1) = 0 := by
        funext x; simp [tens]
      rw [this]; exact Submodule.zero_mem _
    · refine Submodule.subset_span ⟨g, fun _ => 1, ⟨IsLocallyConstant.const 1, ?_⟩, rfl⟩
      exact HasCompactSupport.of_compactSpace _
  have hconst : ∀ t x, M.heisLine ψ u t (tens (evI F) g fun _ => 1) x = tens (evI F) g (fun _ => 1) x := by
    intro t x
    rcases hc with rfl | hE
    · simp [Model.heisLine, GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, tens]
    · simp only [Model.heisLine, GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, dotProduct, Finset.univ_eq_empty,
        Finset.sum_empty, mul_zero, add_zero, AddChar.map_zero_eq_one, one_mul]
      congr 1
      exact Subsingleton.elim _ _
  ext y
  choose x hx using fun i => evI_surj (F := F) (y i)
  have h1 := hA _ hR x
  simp only [hconst] at h1
  have h2 := h1.unique (hasDerivAt_const _ _)
  simpa [tens, hx] using h2

end GlobalTheory.HeisDerivZero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdeleCharRestrictLocalUnitsResidueCharStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideleChar_restrict_localUnits_residueChar : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E), ChrEq c χ → ∀ PP : Pl D.host.E, (∀ a : (kP PP)ˣ →* ℂˣ, χ.TameAt PP → IsRes χ PP a → GlobalTheory.StepLaw.ResAt c PP a) ∧ (χ.UnrAt PP → GlobalTheory.StepLaw.ResAt c PP 1) := by
  first | exact @GlobalTheory.ResLoc.resAt_of_chrEq | exact GlobalTheory.ResLoc.resAt_of_chrEq | (intros; apply GlobalTheory.ResLoc.resAt_of_chrEq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentComponentMemFrameStabilizerStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotentComponent_mem_frameStabilizer : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (g g' : GA D V) (f : AE D), f * f = f → finE V g ∈ St β → Formalism.L2.Theta.mt V g' = f • Formalism.L2.Theta.mt V g + (1 - f) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) → finE V g' ∈ St β := by
  first | exact @GlobalTheory.CompStab.component_mem_St | exact GlobalTheory.CompStab.component_mem_St | (intros; apply GlobalTheory.CompStab.component_mem_St <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentTwistedGroupEndomorphismStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotent_twisted_group_endomorphism : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (ε : AF D.host.F), ε * ε = ε → ∃ κ : GA D V →* GA D V, ∀ g, Formalism.L2.Theta.mt V (κ g) = algebraMap (AF D.host.F) (AE D) ε • Formalism.L2.Theta.mt V g + (1 - algebraMap (AF D.host.F) (AE D) ε) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) ∧ (Stab V β g → Stab V β (κ g)) := by
  first | exact @GlobalTheory.UnitaryIdemCut.exists_cut | exact GlobalTheory.UnitaryIdemCut.exists_cut | (intros; apply GlobalTheory.UnitaryIdemCut.exists_cut <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralCompactOpenTypeIdempotentUnipotentEqZero
section
open MeasureTheory ValuativeRel GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic

noncomputable section

namespace GlobalTheory.TypeIdemAverage

theorem integral_eq_zero_of_sum_translate {N ι : Type} [Group N] [MeasurableSpace N] [MeasurableMul N]
    (ν : Measure N) [ν.IsMulLeftInvariant] [Fintype ι] [Nonempty ι] (n : ι → N) (F : N → ℂ)
    (h : ∀ u, ∑ i, F (n i * u) = 0) : ∫ u, F u ∂ν = 0 := by
  by_cases hF : Integrable F ν
  · have h1 : ∫ u, ∑ i, F (n i * u) ∂ν = ∑ i, ∫ u, F (n i * u) ∂ν :=
      integral_finsetSum _ fun i _ => hF.comp_mul_left (n i)
    simp only [h, integral_zero, integral_mul_left_eq_self, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul] at h1
    exact (mul_eq_zero.1 h1.symm).resolve_left (by exact_mod_cast Fintype.card_ne_zero)
  · exact integral_undef hF

theorem sum_typeIdem_translate {G Q W : Type} [Group G] [MeasurableSpace G] (μ : Measure G) [Group Q]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] {K : Subgroup G} (red : K →* Q)
    (τ : Representation ℂ Q W) (H : Subgroup Q) [Fintype H] (hH : NoFixed τ H) (κ : H → K)
    (hκ : ∀ v, red (κ v) = v) (g : G) : ∑ v, GlobalTheory.Orb.typeIdem μ red τ (κ v * g) = 0 := by
  by_cases hg : g ∈ K
  · obtain ⟨g, rfl⟩ : ∃ g' : K, (g' : G) = g := ⟨⟨g, hg⟩, rfl⟩
    have h0 := GlobalTheory.NoFixedCharSum.noFixedSum Q W τ H hH 1 (red g)
    simp only [← Subgroup.coe_mul, GlobalTheory.Orb.typeIdem_coe, map_mul red, hκ]
    rw [← Finset.mul_sum, ← map_sum]
    simp only [one_mul] at h0
    have h1 : ∑ v : H, τ.character ((v : Q) * red g) = 0 := h0
    rw [h1, map_zero, mul_zero]
  · refine Finset.sum_eq_zero fun v _ => GlobalTheory.Orb.typeIdem_of_notMem μ red τ ?_
    rwa [K.mul_mem_cancel_left (κ v).2]

theorem integral_idemGL_eq_zero (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {r : ℕ}
    {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (τ : Representation ℂ (GL (Fin r) 𝓀[k]) W)
    [MeasurableSpace (GL (Fin r) k)] [BorelSpace (GL (Fin r) k)] (μ : Measure (GL (Fin r) k))
    (N : Subgroup (GL (Fin r) k)) (ν : Measure N) [ν.IsMulLeftInvariant] (H : Subgroup (GL (Fin r) 𝓀[k]))
    (hH : NoFixed τ H) (x : GL (Fin r) k)
    (hx : ∀ v ∈ H, ∃ n ∈ N, ∃ hn : x * n * x⁻¹ ∈ KO k (Fin r),
      GlobalTheory.LocGL.redK k (Fin r) ⟨x * n * x⁻¹, hn⟩ = v)
    (w : GL (Fin r) k) : ∫ u : N, idemGL k μ τ (x * u * w) ∂ν = 0 := by
  classical
  let _ : Fintype H := Fintype.ofFinite H
  choose n hnN hnK hred using hx
  refine integral_eq_zero_of_sum_translate ν (fun v : H => (⟨n v v.2, hnN v v.2⟩ : N))
    (fun u : N => idemGL k μ τ (x * u * w)) fun u => ?_
  have h := sum_typeIdem_translate μ (GlobalTheory.LocGL.redK k (Fin r)) τ H hH
    (fun v => ⟨x * n v v.2 * x⁻¹, hnK v v.2⟩) (fun v => hred v v.2) (x * u * w)
  refine Eq.trans (Finset.sum_congr rfl fun v _ => ?_) h
  simp only [idemGL, Subgroup.coe_mul, mul_assoc, inv_mul_cancel_left]

end GlobalTheory.TypeIdemAverage
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralMulEqZeroOfCosetIntegralEqZeroStatement
section
open MeasureTheory GlobalTheory.AutomorphicL2Unitary
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_mul_eq_zero_of_coset_integral_eq_zero_alt : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (H : Subgroup G), IsClosed (H : Set G) → ∀ (ν : Measure H) [ν.IsHaarMeasure] (μ : Measure G) [μ.IsHaarMeasure] (f w : G → ℂ), Continuous f → HasCompactSupport f → LocallyIntegrable w μ → (∀ u ∈ H, (fun g => w (u * g)) =ᵐ[μ] w) → (∀ g, ∫ u : H, f (u * g) ∂ν = 0) → ∫ g, f g * w g ∂μ = 0 := by
  first | exact @GlobalTheory.CosetIntegralZero.integral_mul_eq_zero_of_coset_integral_eq_zero | exact GlobalTheory.CosetIntegralZero.integral_mul_eq_zero_of_coset_integral_eq_zero | (intros; apply GlobalTheory.CosetIntegralZero.integral_mul_eq_zero_of_coset_integral_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsOfFinOrderOfConjMemSelfDualLatticeStabilizer
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefFree

theorem isOfFinOrder_of_conjIn_mem_St :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E)) (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)), IsDefUnimod hc J Λ → IsFrame β Λ → ∀ (u : UR hc J) (x : UA hc J), conjIn hc J (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) u ∈ St β → IsOfFinOrder u := by
  intro F E _ _ _ _ _ _ hc n J L β hU hβ u x hu
  have hfin := Formalism.UG.Final.AdelicStabFiniteL F E (Fin n) hc.sig J (cm_comp hc) hU.herm hU.unit hU.tdef L
    (Module.Finite.iff_fg.2 hU.lat.fg) hU.lat.span_eq_top x
  have hb := base_level_eq_adelic_level F E hc n J L β hβ
  let H : Subgroup (UR hc J) :=
    (Formalism.UG.levelAfL hc.sig J L).comap (conjIn hc J (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)))
  have hH : Finite H := by
    let f : H → Formalism.UG.stabAt (UQ hc J) ((Formalism.UG.levelAfL hc.sig J L).subgroupOf (UA hc J)) x :=
      fun γ => ⟨ratEl γ.1, (ratEl_mem_stabAt x γ.1).2 γ.2⟩
    refine Finite.of_injective f ?_
    intro a b hab
    exact Subtype.ext (ratEl_injective (congrArg Subtype.val hab))
  have huH : u ∈ H := by
    show conjIn hc J (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) u ∈ Formalism.UG.levelAfL hc.sig J L
    rw [← hb]
    refine ⟨?_, hu⟩
    rw [conjIn_apply]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ x.2) (ratEl u).1.2) x.2
  have := isOfFinOrder_of_finite (⟨u, huH⟩ : H)
  exact H.subtype.isOfFinOrder this

end GlobalTheory.DefFree
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsUnramifiedAtPlaceIdempotentOfHeckeCharUnramifiStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnramifiedAtPlaceIdempotent_of_heckeChar_unramified_above : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E), ChrEq c χ → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), IsPlaceIdem D v ε → (∀ P : Pl D.host.E, P.under (𝓞 D.host.F) = v → χ.UnrAt P) → UnramAt ε c := by
  first | exact @GlobalTheory.UnramOver.unramAt_of_unrAt | exact GlobalTheory.UnramOver.unramAt_of_unrAt | (intros; apply GlobalTheory.UnramOver.unramAt_of_unrAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsUnramifiedEtaTildeOfOddExponentSumStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnramifiedEtaTilde_of_odd_exponentSum : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E), ChrEq c χ → Formalism.L2.Host.IsEtaT D.host χ → ∀ (μ : (AE D)ˣ →* Circle) (n m : ℕ), ResEta D μ n → ResEta D (μ * c⁻¹) m → Odd (n + m) → IsEtaTilde D c := by
  first | exact @GlobalTheory.EtaTildeOddParity.isEtaTilde_of_odd | exact GlobalTheory.EtaTildeOddParity.isEtaTilde_of_odd | (intros; apply GlobalTheory.EtaTildeOddParity.isEtaTilde_of_odd <;> assumption)
end

