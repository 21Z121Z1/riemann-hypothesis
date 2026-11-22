import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0017
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0018
import Development.AbelianVarietyTheory.Definitions.Foundations.IsZetaTW
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0023
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0019
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0380
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0022
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0021
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0020
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0102
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0404
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0054
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0399
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0051

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormEqOneOfIsUnitToZModPow
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.KA
open scoped Matrix MatrixGroups

noncomputable section

namespace GlobalTheory.K4.TwistClauses

variable {l : ℕ} [hl : Fact l.Prime]

theorem mem_O_of_pow_eq_one (c : Coef l) (z : Qbar l) (hz : z ^ (l - 1) = 1) : z ∈ c.O := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod l)ˣ)
  have ho : orderOf g = l - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units]
  haveI : NeZero (l - 1) := ⟨by have := hl.out.two_le; omega⟩
  have h1 : IsPrimitiveRoot g (l - 1) := ho ▸ IsPrimitiveRoot.orderOf g
  have h2 : IsPrimitiveRoot (g : ZMod l) (l - 1) :=
    h1.map_of_injective (f := Units.coeHom (ZMod l)) Units.val_injective
  have hinj : Function.Injective (WittVector.teichmuller l (R := ZMod l)) := fun a b h => by
    simpa [WittVector.teichmuller_coeff_zero] using congrArg (fun x => x.coeff 0) h
  obtain ⟨ω, hω⟩ : ∃ ω : ℤ_[l], IsPrimitiveRoot ω (l - 1) :=
    ⟨_, (h2.map_of_injective hinj).map_of_injective (f := WittVector.equiv l) (WittVector.equiv l).injective⟩
  have hf : Function.Injective (algebraMap ℤ_[l] (Qbar l)) := fun a b h =>
    PadicInt.ext ((algebraMap ℚ_[l] (Qbar l)).injective h)
  obtain ⟨i, -, hi⟩ := (hω.map_of_injective hf).eq_pow_of_pow_eq_one hz
  rw [← hi]
  exact pow_mem (c.O.algebraMap_mem ω) i

theorem norm_algebraMap_padicInt (z : ℤ_[l]) : ‖algebraMap ℤ_[l] (Qbar l) z‖ = ‖z‖ :=
  norm_algebraMap' (Qbar l) (z : ℚ_[l])

theorem norm_eq_one_of_pow {z : Qbar l} (hz : z ^ (l - 1) = 1) : ‖z‖ = 1 := by
  have h : ‖z‖ ^ (l - 1) = 1 := by rw [← norm_pow, hz, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg z) (by have := hl.out.two_le; omega)).1 h

theorem norm_eq_one_of_isUnit_toZModPow {r : ℕ} (hr : r ≠ 0) {a : ℤ_[l]} (ha : IsUnit (PadicInt.toZModPow r a)) : ‖a‖ = 1 := by
  by_contra h
  obtain ⟨k, rfl⟩ := (PadicInt.norm_lt_one_iff_dvd a).1 (lt_of_le_of_ne a.norm_le_one h)
  rw [map_mul, map_natCast] at ha
  have h2 := (ZMod.isUnit_iff_coprime l (l ^ r)).1 (isUnit_of_mul_isUnit_left ha)
  exact hl.out.one_lt.ne' (Nat.Coprime.eq_one_of_dvd h2 (dvd_pow_self l hr))

theorem norm_inv_pow_sub_le {r : ℕ} (hr : r ≠ 0) (e : ℕ) {a b : ℤ_[l]} (ha : IsUnit (PadicInt.toZModPow r a))
    (hab : PadicInt.toZModPow r a = PadicInt.toZModPow r b) :
    ‖(algebraMap ℤ_[l] (Qbar l) a ^ e)⁻¹ - (algebraMap ℤ_[l] (Qbar l) b ^ e)⁻¹‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ := by
  have na : ‖algebraMap ℤ_[l] (Qbar l) a ^ e‖ = 1 := by
    rw [norm_pow, norm_algebraMap_padicInt, norm_eq_one_of_isUnit_toZModPow hr ha, one_pow]
  have nb : ‖algebraMap ℤ_[l] (Qbar l) b ^ e‖ = 1 := by
    rw [norm_pow, norm_algebraMap_padicInt, norm_eq_one_of_isUnit_toZModPow hr (hab ▸ ha), one_pow]
  have hk : b ^ e - a ^ e ∈ RingHom.ker (PadicInt.toZModPow r : ℤ_[l] →+* ZMod (l ^ r)) := by
    rw [RingHom.mem_ker, map_sub, map_pow, map_pow, hab, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hk
  obtain ⟨k, hk⟩ := hk
  have hk' := congrArg (algebraMap ℤ_[l] (Qbar l)) hk
  rw [map_sub, map_pow, map_pow, map_mul, map_pow, map_natCast] at hk'
  rw [inv_sub_inv (norm_ne_zero_iff.1 (by rw [na]; exact one_ne_zero)) (norm_ne_zero_iff.1 (by rw [nb]; exact one_ne_zero)),
    norm_div, norm_mul, na, nb, mul_one, div_one, hk', norm_mul, norm_algebraMap_padicInt]
  exact mul_le_of_le_one_right (norm_nonneg _) k.norm_le_one

theorem val_cast_eq {r : ℕ} (hr : r ≠ 0) (z : ZMod (l ^ r)) :
    ((z.val : ℕ) : ZMod l) = ZMod.castHom (dvd_pow_self l hr) (ZMod l) z := by
  haveI : NeZero (l ^ r) := ⟨pow_ne_zero _ hl.out.ne_zero⟩
  rw [ZMod.natCast_val]; rfl

theorem val_cast_ne_zero {r : ℕ} (hr : r ≠ 0) (x : (ZMod (l ^ r))ˣ) : (((x : ZMod (l ^ r)).val : ℕ) : ZMod l) ≠ 0 := by
  rw [val_cast_eq hr]
  exact (x.isUnit.map _).ne_zero

theorem val_level_zero (z : ZMod (l ^ 0)) : z.val = 0 := by
  haveI : NeZero (l ^ 0) := ⟨pow_ne_zero _ hl.out.ne_zero⟩
  have := ZMod.val_lt z
  simp only [pow_zero] at this
  omega

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

variable (Ω l) in

def cycRes : G ℚ Ω →* ZMod l :=
  (ZMod.castHom (dvd_pow_self l one_ne_zero) (ZMod l)).toMonoidHom.comp ((Units.coeHom (ZMod (l ^ 1))).comp (cycMod ℚ Ω l 1))

theorem cycRes_eq_val (s : G ℚ Ω) : (((cycMod ℚ Ω l 1 s : ZMod (l ^ 1)).val : ℕ) : ZMod l) = cycRes l Ω s :=
  val_cast_eq one_ne_zero _

theorem cycRes_eq_cast {r : ℕ} (hr : r ≠ 0) (s : G ℚ Ω) :
    ZMod.castHom (dvd_pow_self l hr) (ZMod l) (cycMod ℚ Ω l r s : ZMod (l ^ r)) = cycRes l Ω s := by
  have h1r : 1 ≤ r := Nat.one_le_iff_ne_zero.2 hr
  show ZMod.castHom (dvd_pow_self l hr) (ZMod l) (PadicInt.toZModPow r (cycZ ℚ Ω l s : ℤ_[l])) =
    ZMod.castHom (dvd_pow_self l one_ne_zero) (ZMod l) (PadicInt.toZModPow 1 (cycZ ℚ Ω l s : ℤ_[l]))
  rw [← PadicInt.zmod_cast_comp_toZModPow 1 r h1r, RingHom.comp_apply, ← RingHom.comp_apply _ (ZMod.castHom _ (ZMod (l ^ 1))),
    RingHom.ext_zmod (RingHom.comp _ _) (ZMod.castHom (dvd_pow_self l hr) (ZMod l))]

theorem cycRes_ne_zero (s : G ℚ Ω) : cycRes l Ω s ≠ 0 := by
  rw [← cycRes_eq_val]; exact val_cast_ne_zero one_ne_zero _

theorem exists_cycRes_eq [IsAlgClosure ℚ Ω] {r : ℕ} (hr : r ≠ 0) (x : (ZMod (l ^ r))ˣ) :
    ∃ t : G ℚ Ω, cycRes l Ω t = (((x : ZMod (l ^ r)).val : ℕ) : ZMod l) := by
  obtain ⟨t, rfl⟩ := cycMod_surjective Ω l r x
  exact ⟨t, by rw [val_cast_eq hr, cycRes_eq_cast hr]⟩

theorem continuous_cycBar' : Continuous (cycBar ℚ Ω l) :=
  (Continuous.units_map ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom).toMonoidHom
    ((continuous_algebraMap ℚ_[l] (Qbar l)).comp continuous_subtype_val)).comp (continuous_cycZ ℚ Ω l)

theorem cycBar_val (s : G ℚ Ω) : (cycBar ℚ Ω l s : Qbar l) = algebraMap ℤ_[l] (Qbar l) (cycZ ℚ Ω l s : ℤ_[l]) := rfl

theorem cycZ_inertia [IsAlgClosure ℚ Ω] {q : Pl} (hq : ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal) {B : ValuationSubring Ω}
    (hB : IsPlaceOver B q) {s : G ℚ Ω} (hs : s ∈ Ine (F := ℚ) B) : cycZ ℚ Ω l s = 1 :=
  Units.ext (PadicInt.ext_of_toZModPow.mp fun n => by
    rw [ReciprocityTheory.Gal.cycZ_toZModPow_eq hq hB (q := 1) (fun x hx => by simpa using hs.2 x hx) n]
    simp)

theorem chiK_update {r : ℕ} (hr : r ≠ 0) (ψ : ZMod l → Qbar l) (x : (ZMod (l ^ r))ˣ) :
    chiK l (Function.update ψ 0 0) r x = chiK l ψ r x :=
  Function.update_of_ne (val_cast_ne_zero hr x) _ _

theorem chiK_update_zero (ψ : ZMod l → Qbar l) (x : (ZMod (l ^ 0))ˣ) : chiK l (Function.update ψ 0 0) 0 x = 0 := by
  rw [chiK, val_level_zero, Nat.cast_zero, Function.update_self]

section Chi

variable {ψ : ZMod l → Qbar l} {χ : G ℚ Ω →* (Qbar l)ˣ}

theorem chi_eq_one (hχ : ∀ s, (χ s : Qbar l) = ψ (cycRes l Ω s)) {s : G ℚ Ω} (hs : cycRes l Ω s = 1) : χ s = 1 := by
  apply Units.ext
  rw [hχ, hs, ← map_one (cycRes l Ω), ← hχ, map_one]

theorem chi_pow (hχ : ∀ s, (χ s : Qbar l) = ψ (cycRes l Ω s)) (s : G ℚ Ω) : (χ s : Qbar l) ^ (l - 1) = 1 := by
  rw [← Units.val_pow_eq_pow_val, ← map_pow,
    chi_eq_one hχ (by rw [map_pow]; exact ZMod.pow_card_sub_one_eq_one (cycRes_ne_zero s)), Units.val_one]

theorem chiK_pow [IsAlgClosure ℚ Ω] (hχ : ∀ s, (χ s : Qbar l) = ψ (cycRes l Ω s)) {r : ℕ} (hr : r ≠ 0)
    (x : (ZMod (l ^ r))ˣ) : chiK l ψ r x ^ (l - 1) = 1 := by
  obtain ⟨t, ht⟩ := exists_cycRes_eq (Ω := Ω) hr x
  rw [chiK, ← ht, ← hχ]
  exact chi_pow hχ t

theorem chiK_mul_cycMod [IsAlgClosure ℚ Ω] (hχ : ∀ s, (χ s : Qbar l) = ψ (cycRes l Ω s)) {r : ℕ} (hr : r ≠ 0)
    (x : (ZMod (l ^ r))ˣ) (s : G ℚ Ω) : chiK l ψ r (x * cycMod ℚ Ω l r s) = chiK l ψ r x * χ s := by
  obtain ⟨t, ht⟩ := exists_cycRes_eq (Ω := Ω) hr x
  rw [chiK, chiK, val_cast_eq hr, Units.val_mul, map_mul, ← val_cast_eq hr, ← ht, cycRes_eq_cast hr, ← map_mul, ← hχ, ← hχ,
    map_mul, Units.val_mul]

omit hl in
theorem chiK_succ [Fact l.Prime] (ψ : ZMod l → Qbar l) {r : ℕ} (hr : r ≠ 0) (x : (ZMod (l ^ (r + 1)))ˣ) :
    chiK l ψ (r + 1) x =
      chiK l ψ r ((Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom) x) := by
  rw [chiK, chiK, val_cast_eq hr, val_cast_eq (Nat.succ_ne_zero r)]
  congr 1
  exact (RingHom.congr_fun (RingHom.ext_zmod ((ZMod.castHom (dvd_pow_self l hr) (ZMod l)).comp
    (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r)))) (ZMod.castHom (dvd_pow_self l (Nat.succ_ne_zero r)) (ZMod l)))
    (x : ZMod (l ^ (r + 1)))).symm

theorem eta_shift [IsAlgClosure ℚ Ω] (hχ : ∀ s, (χ s : Qbar l) = ψ (cycRes l Ω s)) (e : ℕ) {r : ℕ} (hr : r ≠ 0)
    (s : G ℚ Ω) (x : (ZMod (l ^ r))ˣ) :
    ‖(((((x * cycMod ℚ Ω l r s : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * chiK l ψ r (x * cycMod ℚ Ω l r s) -
      ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * chiK l ψ r x * ((eps l s ^ e)⁻¹ * (χ s : Qbar l))‖ ≤
      ‖((l : ℕ) : Qbar l) ^ r‖ := by
  haveI : NeZero (l ^ r) := ⟨pow_ne_zero _ hl.out.ne_zero⟩
  have h := norm_inv_pow_sub_le (l := l) hr e
    (a := ((((x * cycMod ℚ Ω l r s : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)).val : ℕ) : ℤ_[l]))
    (b := (((x : ZMod (l ^ r)).val : ℕ) : ℤ_[l]) * (cycZ ℚ Ω l s : ℤ_[l]))
    (by rw [map_natCast, ZMod.natCast_zmod_val]; exact Units.isUnit _)
    (by rw [map_mul, map_natCast, map_natCast, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]; rfl)
  rw [map_mul, map_natCast, map_natCast, ← cycBar_val, mul_pow, mul_inv] at h
  rw [chiK_mul_cycMod hχ hr, show ∀ a b c u v : Qbar l, a * (u * v) - b * u * (c * v) = u * v * (a - b * c) from
    fun _ _ _ _ _ => by ring, norm_mul, norm_mul, norm_eq_one_of_pow (chiK_pow hχ hr x), norm_eq_one_of_pow (chi_pow hχ s),
    one_mul, one_mul]
  exact h

end Chi

end GlobalTheory.K4.TwistClauses

namespace GlobalTheory.K4

open TwistClauses in

theorem twist_clauses : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ)
  (gN : Newform (2 * e + 1)) (A : ValuationSubring Ω) (W : R2 Ω l) (ε : Ω →+* ℂ) (X : Tower Ω ε)
  (pr : X.Fn l → Fin 2 → Qbar l) (N : ℕ) [NeZero N] (cw : ZMod N → Qbar l) (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ))
  (ψ : ZMod l → Qbar l) (cf : Coef l) (S : Finset Pl),
  Nf e S A W → l ≠ 2 → (∃ x, cw x ≠ 0) → AdmWn ι e gN A W X pr N cw c d gm ψ cf →
  ∃ θ : G ℚ Ω →* (Qbar l)ˣ, Continuous θ ∧ (∀ s, mat W s = (θ s : Qbar l) • rhoK W e ψ s) ∧
    (∀ c' : Coef l, (∀ s i j, mat W s i j ∈ c'.O) → ∀ s i j, rhoK W e ψ s i j ∈ c'.O) ∧
    (∀ c' : Coef l, ∀ r x, chiK l (Function.update ψ 0 0) r x ∈ c'.O) ∧
    (∀ r (x : (ZMod (l ^ (r + 1)))ˣ), ‖chiK l (Function.update ψ 0 0) (r + 1) x - chiK l (Function.update ψ 0 0) r ((Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom) x)‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) ∧
    (∀ r s x, ‖(fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * chiK l (Function.update ψ 0 0) r x) (x * cycMod ℚ Ω l r s) - (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * chiK l (Function.update ψ 0 0) r x) x * (θ s : Qbar l)‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) ∧
    (∀ q : Pl, ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∀ B : ValuationSubring Ω, IsPlaceOver B q → ∀ s ∈ Ine (F := ℚ) B, θ s = 1) ∧
    (∀ s ∈ Dec (F := ℚ) A, rhoK W e ψ s 1 0 = 0 ∧ rhoK W e ψ s 1 1 = (nuD W e ψ s : Qbar l)) ∧
    (∀ r, (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * chiK l (Function.update ψ 0 0) r x) = (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * chiK l ψ r x)) := by
  intro l hl Ω _ _ _ ι e gN A W ε X pr N _ cw c d gm ψ cf S hNf _ hx hadm
  obtain ⟨x₀, hx₀⟩ := hx
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, χ, hkill, -, hχ'⟩ := hadm.1 x₀ hx₀
  have hχ : ∀ s, (χ s : Qbar l) = ψ (cycRes l Ω s) := fun s => by rw [hχ', cycRes_eq_val]
  set θ : G ℚ Ω →* (Qbar l)ˣ := cycBar ℚ Ω l ^ (-(e : ℤ)) * χ with hθdef
  have hθu : ∀ s, θ s = cycBar ℚ Ω l s ^ (-(e : ℤ)) * χ s := fun s => rfl
  have hθ : ∀ s, (θ s : Qbar l) = (eps l s ^ e)⁻¹ * χ s := fun s => by
    rw [hθu, Units.val_mul, Units.val_zpow_eq_zpow_val, zpow_neg, zpow_natCast]
  have hth : ∀ s, thK l e ψ s = θ s := fun s => by rw [hθ, hχ', thK]
  have hρ : ∀ s i j, rhoK W e ψ s i j = (θ s : Qbar l)⁻¹ * mat W s i j := fun s i j => by
    rw [rhoK, hth, Matrix.smul_apply, smul_eq_mul]
  refine ⟨θ, ?_, fun s => ?_, fun c' hW s i j => ?_, fun c' r x => ?_, fun r x => ?_, fun r s x => ?_,
    fun q hq B hB s hs => ?_, fun s hs => ?_, fun r => funext fun x => ?_⟩
  · exact (continuous_cycBar'.zpow (-(e : ℤ))).mul (GlobalTheory.Ord2.VanishKato.cont_kills l hl.out.one_le χ hkill)
  · rw [rhoK, hth, smul_smul, mul_inv_cancel₀ (θ s).ne_zero, one_smul]
  · rw [hρ, hθ, mul_inv, inv_inv]
    refine mul_mem (mul_mem (pow_mem (c'.O.algebraMap_mem (cycZ ℚ Ω l s : ℤ_[l])) e) ?_) (hW s i j)
    exact mem_O_of_pow_eq_one c' _ (by rw [inv_pow, chi_pow hχ, inv_one])
  · rcases eq_or_ne r 0 with rfl | hr
    · rw [chiK_update_zero]; exact zero_mem _
    · rw [chiK_update hr]; exact mem_O_of_pow_eq_one c' _ (chiK_pow hχ hr x)
  · rcases eq_or_ne r 0 with rfl | hr
    · rw [chiK_update_zero, chiK_update (Nat.succ_ne_zero 0), sub_zero,
        norm_eq_one_of_pow (chiK_pow hχ (Nat.succ_ne_zero 0) x), pow_zero, norm_one]
    · rw [← chiK_succ _ hr, sub_self, norm_zero]; exact norm_nonneg _
  · rcases eq_or_ne r 0 with rfl | hr
    · simp only [chiK_update_zero, mul_zero, zero_mul, sub_self, norm_zero]; exact norm_nonneg _
    · simp only [chiK_update hr, hθ]
      exact eta_shift hχ e hr s x
  · have hz := cycZ_inertia hq hB hs
    have h1 : cycBar ℚ Ω l s = 1 := by rw [cycBar, MonoidHom.comp_apply, hz, map_one]
    have h2 : cycRes l Ω s = 1 := by
      rw [cycRes, MonoidHom.comp_apply, MonoidHom.comp_apply, cycMod, MonoidHom.comp_apply, hz, map_one, map_one, map_one]
    rw [hθu, h1, chi_eq_one hχ h2, one_zpow, one_mul]
  · have h10 := hNf.upper s hs
    have hdet : (mat W s).det ≠ 0 := (Matrix.GeneralLinearGroup.det (W s)).ne_zero
    rw [Matrix.det_fin_two, h10, mul_zero, sub_zero] at hdet
    have h11 : rhoK W e ψ s 1 1 ≠ 0 := by
      rw [hρ]; exact mul_ne_zero (inv_ne_zero (θ s).ne_zero) (right_ne_zero_of_mul hdet)
    refine ⟨by rw [hρ, h10, mul_zero], ?_⟩
    rw [nuD, dif_pos h11, Units.val_mk0]
  · rcases eq_or_ne r 0 with rfl | hr
    · rw [val_level_zero, Nat.cast_zero, zero_pow (Nat.one_le_iff_ne_zero.1 hNf.e_pos), inv_zero, zero_mul, zero_mul]
    · rw [chiK_update hr]

end GlobalTheory.K4

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormLPowLe
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4
open scoped Matrix MatrixGroups

namespace GlobalTheory.HTLawZeta

open GlobalTheory.KummerEisensteinGalois GlobalTheory.LambdaValuationPowers

variable {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω]

theorem norm_l_pow_le (k : ℕ) : ‖((l : ℕ) : Qbar l) ^ k‖ ≤ 1 := by
  rw [norm_pow]
  exact pow_le_one₀ (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ _)

theorem cg_char_sum (n m : ℕ) (f g : (ZMod (l ^ m))ˣ → Qbar l) (ψ : DirichletCharacter (Qbar l) (l ^ m))
    (h : ∀ b, Cg n (f b) (g b)) :
    Cg n (∑ b : (ZMod (l ^ m))ˣ, ψ (b : ZMod (l ^ m)) * f b) (∑ b : (ZMod (l ^ m))ˣ, ψ (b : ZMod (l ^ m)) * g b) := by
  unfold Cg at *
  rw [← Finset.sum_sub_distrib]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun b _ => ?_
  rw [← mul_sub, norm_mul]
  have hψ : ‖ψ (b : ZMod (l ^ m))‖ ≤ 1 := by
    have h1 : (ψ (b : ZMod (l ^ m))) ^ orderOf b = 1 := by
      rw [← map_pow, ← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one, map_one]
    have h2 : ‖ψ (b : ZMod (l ^ m))‖ ^ orderOf b = 1 := by rw [← norm_pow, h1, norm_one]
    have hpos : orderOf b ≠ 0 := (orderOf_pos b).ne'
    exact le_of_eq ((pow_eq_one_iff_of_nonneg (norm_nonneg _) hpos).1 h2)
  calc ‖ψ (b : ZMod (l ^ m))‖ * ‖f b - g b‖ ≤ 1 * ‖f b - g b‖ := by gcongr
    _ ≤ _ := by rw [one_mul]; exact h b

theorem htCoL_mono {A : ValuationSubring Ω} {c : Coef l} {j : Ω →+* Qbar l} {Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l}
    {m a b : ℕ} {y : (ZMod (l ^ m))ˣ} {h : Qbar l} (H : HTCoL A c j Z m a y h) (hab : a ≤ b) : HTCoL A c j Z m b y h := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hab
  obtain ⟨q, o, w, ho, hs⟩ := H
  refine ⟨q, fun i => (l : Qbar l) ^ k * o i, w, fun i => ⟨?_, ?_, (ho i).2.2⟩, fun s h1 h2 => ?_⟩
  · rw [norm_mul]
    exact mul_le_one₀ (norm_l_pow_le k) (norm_nonneg _) (ho i).1
  · intro σ hσ hσ'
    rw [map_mul, map_pow, map_natCast, (ho i).2.1 σ hσ hσ']
  · have h3 := hs s h1 h2
    unfold Cg at *
    have e : (l : Qbar l) ^ (a + k) * Z m s y - ((l : Qbar l) ^ (a + k) * h * lamv l m s +
        ∑ i, (l : Qbar l) ^ k * o i * (j (s (w i)) - j (w i))) =
        (l : Qbar l) ^ k * ((l : Qbar l) ^ a * Z m s y - ((l : Qbar l) ^ a * h * lamv l m s +
        ∑ i, o i * (j (s (w i)) - j (w i)))) := by
      simp only [mul_assoc, ← Finset.mul_sum]
      ring
    rw [e, norm_mul]
    calc _ ≤ 1 * _ := mul_le_mul_of_nonneg_right (norm_l_pow_le k) (norm_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact h3

def unitVal (ε : Ω →+* ℂ) (j : Ω →+* Qbar l) (lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l) (N k : ℕ) (c d w w' : ℤ) (m β : ℕ) :
    Qbar l :=
  haveI : CharZero Ω := algebraRat.charZero Ω
  lam (fun i => (l : Qbar l) ^ m * j (toQ (l ^ m)
    (pieceT N l m m k (1 : DirichletCharacter Ω (l ^ m)) c d (w, 0) (w', 0)
      (eOm ε (1 / ((N : ℚ) * (l : ℚ) ^ m)) ^ β)
      ((unitSet l m).filter fun γ => (γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ m))).det = 1)) i))

theorem sum_unitVal [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (j : Ω →+* Qbar l) (lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l) (N k : ℕ)
    (c d w w' : ℤ) (m : ℕ) (β : (ZMod (l ^ m))ˣ → ℕ) (ψ : DirichletCharacter (Qbar l) (l ^ m)) (F : ℕ → Qbar l) (hN : ¬ l ∣ N)
    (hm : 1 ≤ m) (hβ : ∀ b, ((β b : ℕ) : ZMod (l ^ m)) = b ∧ ((β b : ℕ) : ZMod N) = 1)
    (hE : ∀ ζ : Qbar l, IsPrimitiveRoot ζ (N * l ^ m) → ∀ r : ℕ,
      toQ (l ^ m) (pieceT N l m m k ψ c d (w, 0) (w', 0) ζ (unitSet l m)) r =
        -((l : Qbar l) ^ (-(m : ℤ))) * gaussS l m ψ (ζ ^ N) * ψ⁻¹ (N : ZMod (l ^ m)) * (N : Qbar l) ^ ((2 : ℤ) - k) *
          up (l ^ m) F r) :
    ∑ b : (ZMod (l ^ m))ˣ, ψ b * unitVal ε j lam N k c d w w' m (β b) =
      -((N : Qbar l) ^ ((2 : ℤ) - k)) * (∑ a : ZMod (l ^ m), ψ a * (j (eOm ε (1 / (l : ℚ) ^ m))) ^ a.val) *
        ψ⁻¹ (N : ZMod (l ^ m)) * lam (up (l ^ m) F) := by
  haveI : CharZero Ω := algebraRat.charZero Ω
  have hp : l.Prime := Fact.out
  have hN0 : 0 < N := Nat.pos_of_ne_zero (by rintro rfl; exact hN (dvd_zero _))
  obtain ⟨-, -, hr, hrN⟩ := GlobalTheory.Glue.Roots.eOm_isPrimitiveRoot_compatible Ω ε ε.injective l hp N hN0 m
  set ζ := eOm ε (1 / ((N : ℚ) * (l : ℚ) ^ m)) with hζ
  have hjζ : IsPrimitiveRoot (j ζ) (N * l ^ m) := hr.map_of_injective j.injective
  have hP := GlobalTheory.KummerEisensteinGalois.psum_galois_unitPiece N l m k (Qbar l) ψ c d (w, 0) (w', 0) (j ζ) β hp hN0
    ((Nat.Prime.coprime_iff_not_dvd hp).2 hN) hm hjζ hβ
  have hl0 : (l : Qbar l) ≠ 0 := by exact_mod_cast hp.ne_zero
  have key : ∀ (F : (ZMod (l ^ m))ˣ → ℕ → Qbar l) (C : Qbar l) (g : ℕ → Qbar l),
      (∀ i, ∑ b : (ZMod (l ^ m))ˣ, ψ b * F b i = C * g i) → ∑ b : (ZMod (l ^ m))ˣ, ψ b * lam (F b) = C * lam g := by
    intro F C g h
    have e : ∑ b : (ZMod (l ^ m))ˣ, ψ b • F b = C • g := by
      funext i
      simpa [Finset.sum_apply] using h i
    have e2 := congrArg lam e
    simpa [map_sum, map_smul] using e2
  refine key _ _ _ fun i => ?_
  have h1 := hE (j ζ) hjζ i
  rw [toQ, ← hP, gaussS, ← map_pow, hrN] at h1
  simp only [toQ, GlobalTheory.KummerEisensteinGalois.map_pieceT_one N l m k Ω (Qbar l) j, map_pow, ← hζ]
  simp only [mul_left_comm (ψ _) ((l : Qbar l) ^ m), ← Finset.mul_sum]
  rw [h1, zpow_neg, zpow_natCast]
  field_simp

theorem law_of_parts [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω) (cf : Coef l) (j : Ω →+* Qbar l) (ε : Ω →+* ℂ) (N : ℕ) [NeZero N]
    (cw : ZMod N → Qbar l) (c₀ : ℕ) (K : Qbar l) (U : ZMod N → ℕ → ℕ → ℤ → Qbar l)
    (F : ∀ m : ℕ, DirichletCharacter (Qbar l) (l ^ m) → ZMod N → ℕ → Qbar l) (Zx : ZMod N → ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l)
    (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) (lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l) (per : ℕ → Qbar l) (κ₀ : Qbar l)
    (hZ : ∀ r s y, Z r s y = ∑ x, cw x * Zx x r s y) (hper : ∀ n, ‖per n‖ = 1 ∧ Cg n (per (n + 1)) (per n)) (hκ : κ₀ ≠ 0)
    (hK : K ≠ 0) (hN : ¬ l ∣ N) (hcw : ∀ x, cw x ∈ cf.O)
    (hU : ∀ x, cw x ≠ 0 → ∀ m : ℕ, 1 ≤ m → ∀ ψ : DirichletCharacter (Qbar l) (l ^ m), ψ.IsPrimitive →
      ∀ (β : (ZMod (l ^ m))ˣ → ℕ) (t : ℤ), (∀ b, ((β b : ℕ) : ZMod (l ^ m)) = b ∧ ((β b : ℕ) : ZMod N) = 1) →
      (l : ℤ) ^ m * t ≡ 1 [ZMOD N] → ∑ b : (ZMod (l ^ m))ˣ, ψ b * U x m (β b) t =
        K * (∑ a : ZMod (l ^ m), ψ a * (j (eOm ε (1 / (l : ℚ) ^ m))) ^ a.val) * ψ⁻¹ (N : ZMod (l ^ m)) *
          lam (up (l ^ m) (F m ψ x)))
    (hco : ∀ x, cw x ≠ 0 → ∃ c' : ℕ, ∀ m : ℕ, 1 ≤ m → ∀ (y : (ZMod (l ^ m))ˣ) (β : ℕ) (t : ℤ),
      (β : ZMod (l ^ m)) = (y : ZMod (l ^ m)) → (β : ZMod N) = 1 → (l : ℤ) ^ m * t ≡ 1 [ZMOD N] →
      HTCoL A cf j (Zx x) m c' y ((per m)⁻¹ * (l : Qbar l) ^ c₀ * κ₀ *
        U x m β t))
    (hpres : ∃ m₁ C : ℕ, ∀ m, m₁ ≤ m → ∀ ζ : Ω, IsPrimitiveRoot ζ (l ^ m) →
      ∃ (ι : Type) (_ : Fintype ι) (P : ι → Polynomial Ω) (o : ι → Qbar l), HTPresNuOfPolys A cf m C Z ζ P o)
    (hloc : ∃ c₁ : ℕ, ∀ m C : ℕ, C + c₁ ≤ m → ∀ (ζ : Ω) (ι : Type) [Fintype ι] (P : ι → Polynomial Ω) (o : ι → Qbar l)
      (h : (ZMod (l ^ m))ˣ → Qbar l), HTPresNuOfPolys A cf m C Z ζ P o → (∀ y, HTCoL A cf j Z m C y (h y)) →
      ∀ y : (ZMod (l ^ m))ˣ, Cg (m - C - c₁) (htv j ζ P o (y : ZMod (l ^ m)).val) (h y)) :
    ∃ (m₀ c₁ : ℕ) (κ : Qbar l) (v : ℕ → Qbar l), κ ≠ 0 ∧ (∀ m, ‖v m‖ = 1 ∧ Cg m (v (m + 1)) (v m)) ∧
      HTLawCsOfCoef A cf Z j m₀ c₁
        (fun m ψ z => v m * κ * (∑ a : ZMod (l ^ m), ψ a * z ^ a.val) * ψ⁻¹ (N : ZMod (l ^ m)) *
          lam (up (l ^ m) (fun i => ∑ x : ZMod N, cw x * F m ψ x i))) := by
  classical
  have hp : l.Prime := Fact.out
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hcop : Nat.Coprime l N := (Nat.Prime.coprime_iff_not_dvd hp).2 hN
  obtain ⟨m₁, C₁, hpres⟩ := hpres
  obtain ⟨c₁, hloc⟩ := hloc
  choose! c' hc' using hco
  set C : ℕ := C₁ + ∑ x, c' x with hC
  have hle : ∀ x, c' x ≤ C := fun x =>
    (Finset.single_le_sum (f := c') (fun _ _ => Nat.zero_le _) (Finset.mem_univ x)).trans (Nat.le_add_left _ _)
  have hroot := fun m => GlobalTheory.Glue.Roots.eOm_isPrimitiveRoot_compatible Ω ε ε.injective l hp N hN0 m
  have hl0 : (l : Qbar l) ≠ 0 := by exact_mod_cast hp.ne_zero
  refine ⟨m₁ + C + c₁ + 1, C + c₁, (l : Qbar l) ^ c₀ * κ₀ * K,
    fun m => (per m)⁻¹, mul_ne_zero (mul_ne_zero (pow_ne_zero _ hl0) hκ) hK,
    fun m => ⟨by rw [norm_inv, (hper m).1, inv_one], ?_⟩,
    fun m => eOm ε (1 / (l : ℚ) ^ m), fun m => ⟨(hroot m).1, (hroot m).2.1⟩, fun m hm => ?_⟩
  · have h0 : ∀ n, per n ≠ 0 := fun n h => by simpa [h] using (hper n).1
    have h1 := (hper m).2
    unfold Cg at *
    rw [inv_sub_inv (h0 _) (h0 _), norm_div, norm_mul, (hper m).1, (hper (m + 1)).1, mul_one, div_one, norm_sub_rev]
    exact h1
  obtain ⟨ι, hι, P, o, hP⟩ := hpres m (by omega) _ (hroot m).1
  have hcm : Nat.Coprime (l ^ m) N := Nat.Coprime.pow_left m hcop
  obtain ⟨t, ht⟩ : ∃ t : ℤ, (l : ℤ) ^ m * t ≡ 1 [ZMOD N] := by
    refine ⟨Int.gcdA ((l ^ m : ℕ) : ℤ) N, ?_⟩
    have h := Int.gcd_eq_gcd_ab ((l ^ m : ℕ) : ℤ) (N : ℤ)
    rw [Int.gcd_natCast_natCast, hcm] at h
    refine (Int.modEq_iff_dvd.2 ⟨Int.gcdB ((l ^ m : ℕ) : ℤ) N, ?_⟩)
    push_cast at h ⊢
    linear_combination h
  have hβ : ∀ b : (ZMod (l ^ m))ˣ, ∃ β : ℕ, (β : ZMod (l ^ m)) = b ∧ (β : ZMod N) = 1 := fun b => by
    obtain ⟨β, h1, h2⟩ := Nat.chineseRemainder hcm (b : ZMod (l ^ m)).val 1
    refine ⟨β, ?_, ?_⟩
    · rw [(ZMod.natCast_eq_natCast_iff _ _ _).2 h1, ZMod.natCast_zmod_val]
    · rw [(ZMod.natCast_eq_natCast_iff _ _ _).2 h2, Nat.cast_one]
  choose β hβ using hβ
  set u : ZMod N → (ZMod (l ^ m))ˣ → Qbar l := fun x y => (per m)⁻¹ * (l : Qbar l) ^ c₀ * κ₀ *
    U x m (β y) t with hu
  have hH : ∀ y, HTCoL A cf j Z m C y (∑ x, cw x * u x y) := by
    intro y
    have h1 := GlobalTheory.LambdaValuationPowers.htCoL_sum l Ω A cf j (ZMod N) cw (fun x => if cw x = 0 then 0 else Zx x) m C y
      (fun x => if cw x = 0 then 0 else u x y) (fun x => ⟨GlobalTheory.LambdaValuationPowers.norm_le_one_of_mem (hcw x), fun σ h _ => h _ (hcw x)⟩)
      (fun x => by
        by_cases hx : cw x = 0
        · simp only [hx, if_true]
          exact htCoL_of_eq A cf j _ m C y 0 (fun s => by simp)
        · simp only [hx, if_false]
          exact htCoL_mono (hc' x hx m (by omega) y (β y) t (hβ y).1 (hβ y).2 ht) (hle x))
    convert h1 using 1
    · funext r s y'
      rw [hZ]
      refine Finset.sum_congr rfl fun x _ => ?_
      by_cases hx : cw x = 0 <;> simp [hx]
    · refine Finset.sum_congr rfl fun x _ => ?_
      by_cases hx : cw x = 0 <;> simp [hx]
  have hPC := htPresNu7_mono_loss l Ω A cf Z m C₁ C _ ι P o hP (Nat.le_add_right _ _)
  refine ⟨ι, hι, P, o, htPresNu7_mono_loss l Ω A cf Z m C (C + c₁) _ ι P o hPC (Nat.le_add_right _ _), fun ψ hψ => ?_⟩
  have h2 := cg_char_sum _ m _ _ ψ (hloc m C (by omega) _ ι P o _ hPC hH)
  rw [Nat.sub_sub] at h2
  convert h2 using 1
  have hup : up (l ^ m) (fun i => ∑ x : ZMod N, cw x * F m ψ x i) =
      ∑ x : ZMod N, cw x • up (l ^ m) (F m ψ x) := by
    funext i
    simp [up, Finset.sum_apply]
  have hsw : ∑ b : (ZMod (l ^ m))ˣ, ψ b * ∑ x, cw x * u x b = ∑ x, ∑ b : (ZMod (l ^ m))ˣ, ψ b * (cw x * u x b) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => Finset.mul_sum _ _ _
  beta_reduce
  rw [hsw, hup, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : cw x = 0
  · simp [hx]
  have h3 := hU x hx m (by omega) ψ hψ β t hβ ht
  have h4 : ∑ b : (ZMod (l ^ m))ˣ, ψ b * (cw x * u x b) = cw x * ((per m)⁻¹ * (l : Qbar l) ^ c₀ * κ₀) *
      ∑ b : (ZMod (l ^ m))ˣ, ψ b * U x m (β b) t := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [hu]
    ring
  rw [h4, h3, map_smul, smul_eq_mul]
  ring

end GlobalTheory.HTLawZeta

end
end

