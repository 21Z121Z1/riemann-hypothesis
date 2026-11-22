import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0378
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0017
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0379
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0373
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0012

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LipschitzPadicHomOfContractionPerLevelStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lipschitz_padicHom_of_contraction_per_level : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (P : ℕ → Γ → Prop) (lam : Γ →* Multiplicative ℤ_[l]), (∀ m g, P (m + 1) g → P m g) → (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ g, P N g → ‖(lam g).toAdd‖ ≤ ε) → (∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ g, P (m + 1) g → ∃ h g' : Γ, P m h ∧ P (m + 2) g' ∧ g = h ^ l * g') → ∃ C : ℝ, ∀ (m : ℕ) (g : Γ), P m g → ‖(lam g).toAdd‖ ≤ C * ((l : ℝ)⁻¹) ^ m := by
  first | exact @GlobalTheory.lipschitz_of_contraction_per_level | exact GlobalTheory.lipschitz_of_contraction_per_level | (intros; apply GlobalTheory.lipschitz_of_contraction_per_level <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalCharacterH1FiniteLevelsStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_character_h1_finite_levels : LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (c : Coef l) (A : ValuationSubring Ω), OverL l A → ∀ θ : ↥(Dec (F := ℚ) A) →* c.Oˣ, Continuous (fun g => ((θ g : c.Oˣ) : c.O)) → (∃ g, θ g ≠ 1) → (∃ g, θ g ≠ (UpperTheory.V.Base.chiO ℚ Ω l c.O).comp (Dec (F := ℚ) A).subtype g) → ∃ C : ℕ, ∀ n : ℕ, 1 ≤ n → Finite (H1 (Formalism.GaloisCohomology.scalRep (UpperTheory.V.X.Lev (((l : ℕ) : c.O) ^ n)) θ)) ∧ Nat.card (H1 (Formalism.GaloisCohomology.scalRep (UpperTheory.V.X.Lev (((l : ℕ) : c.O) ^ n)) θ)) ≤ C * Nat.card (UpperTheory.V.X.Lev (((l : ℕ) : c.O) ^ n)) := by
  first | exact @GlobalTheory.LocChar.local_character_h1_bound | exact GlobalTheory.LocChar.local_character_h1_bound | (intros; apply GlobalTheory.LocChar.local_character_h1_bound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalConditionsIndependentOfPlaceOverStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localConditions_independent_of_place_over : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (W : R2 Ω l) (z : G ℚ Ω → Fin 2 → Qbar l), z ∈ Z1 (Loc.colRep W) → ∀ (w : Pl) (B B' : ValuationSubring Ω), IsPlaceOver B w → IsPlaceOver B' w → ((∃ x : Fin 2 → Qbar l, ∀ s ∈ Ine (F := ℚ) B, z s = mat W s *ᵥ x - x) → ∃ x : Fin 2 → Qbar l, ∀ s ∈ Ine (F := ℚ) B', z s = mat W s *ᵥ x - x) ∧ (Triv W B z → Triv W B' z) := by
  first | exact @GlobalTheory.Ord2.place_indep | exact GlobalTheory.Ord2.place_indep | (intros; apply GlobalTheory.Ord2.place_indep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemCoc
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA
open scoped Matrix

namespace GlobalTheory.InertCoh

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

def cob (W : R2 Ω l) (c : Coef l) (I : Subgroup (G ℚ Ω)) : Submodule c.O (G ℚ Ω → Fin 2 → Qbar l) where
  carrier := {z | ∃ v : Fin 2 → Qbar l, ∀ s ∈ I, z s = mat W s *ᵥ v - v}
  zero_mem' := ⟨0, fun s _ => by simp⟩
  add_mem' := by
    rintro a b ⟨v, hv⟩ ⟨w, hw⟩
    refine ⟨v + w, fun s hs => ?_⟩
    simp only [Pi.add_apply, hv s hs, hw s hs, Matrix.mulVec_add]
    abel
  smul_mem' := by
    rintro k a ⟨v, hv⟩
    refine ⟨k • v, fun s hs => ?_⟩
    simp only [Pi.smul_apply, hv s hs, Matrix.mulVec_smul, smul_sub]

def coc (W : R2 Ω l) (c : Coef l) (I : Subgroup (G ℚ Ω)) : Submodule c.O (G ℚ Ω → Fin 2 → Qbar l) where
  carrier := {z | (∀ i, Continuous fun s => z s i) ∧ (∀ s i, z s i ∈ c.O) ∧
    ∀ s ∈ I, ∀ t ∈ I, z (s * t) = z s + mat W s *ᵥ z t}
  zero_mem' := ⟨fun i => continuous_const, fun s i => c.O.zero_mem, fun s _ t _ => by simp⟩
  add_mem' := by
    rintro a b ⟨ha1, ha2, ha3⟩ ⟨hb1, hb2, hb3⟩
    refine ⟨fun i => (ha1 i).add (hb1 i), fun s i => c.O.add_mem (ha2 s i) (hb2 s i), fun s hs t ht => ?_⟩
    simp only [Pi.add_apply, ha3 s hs t ht, hb3 s hs t ht, Matrix.mulVec_add]
    abel
  smul_mem' := by
    rintro k a ⟨ha1, ha2, ha3⟩
    refine ⟨fun i => ?_, fun s i => ?_, fun s hs t ht => ?_⟩
    · simp only [Pi.smul_apply, Subalgebra.smul_def, smul_eq_mul]
      exact continuous_const.mul (ha1 i)
    · simp only [Pi.smul_apply, Subalgebra.smul_def, smul_eq_mul]
      exact c.O.mul_mem k.2 (ha2 s i)
    · simp only [Pi.smul_apply, ha3 s hs t ht, Matrix.mulVec_smul, smul_add]

theorem mem_cob {W : R2 Ω l} {c : Coef l} {I : Subgroup (G ℚ Ω)} {z : G ℚ Ω → Fin 2 → Qbar l} :
    z ∈ cob W c I ↔ ∃ v : Fin 2 → Qbar l, ∀ s ∈ I, z s = mat W s *ᵥ v - v := Iff.rfl

theorem mem_coc {W : R2 Ω l} {c : Coef l} {I : Subgroup (G ℚ Ω)} {z : G ℚ Ω → Fin 2 → Qbar l} :
    z ∈ coc W c I ↔ (∀ i, Continuous fun s => z s i) ∧ (∀ s i, z s i ∈ c.O) ∧
      ∀ s ∈ I, ∀ t ∈ I, z (s * t) = z s + mat W s *ᵥ z t := Iff.rfl

end GlobalTheory.InertCoh

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemIntegersOfNormLeOne
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

private theorem norm_le_one_of_isIntegral_zl (l : ℕ) [Fact l.Prime] (x : PadicAlgCl l)
    (hx : IsIntegral ℤ_[l] x) : ‖x‖ ≤ 1 := by
  first
  | exact @_root_.GlobalTheory.IntegralCoefficientNormBound.norm_le_one_of_isIntegral
  | exact _root_.GlobalTheory.IntegralCoefficientNormBound.norm_le_one_of_isIntegral
  | (apply _root_.GlobalTheory.IntegralCoefficientNormBound.norm_le_one_of_isIntegral <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralCoefficientNormBound.norm_le_one_of_isIntegral <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralCoefficientNormBound.norm_le_one_of_isIntegral <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralCoefficientNormBound.norm_le_one_of_isIntegral ..)

theorem norm_le_one_of_mem_coefO {l : ℕ} [Fact l.Prime] (c : Coef l) (a : c.O) :
    ‖(a : PadicAlgCl l)‖ ≤ 1 :=
  norm_le_one_of_isIntegral_zl l _ ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) a).map c.O.val)

theorem norm_unit_coefO {l : ℕ} [Fact l.Prime] (c : Coef l) (u : c.Oˣ) :
    ‖((u : c.O) : PadicAlgCl l)‖ = 1 := by
  have h1 : ‖((u : c.O) : PadicAlgCl l)‖ * ‖(((u⁻¹ : c.Oˣ) : c.O) : PadicAlgCl l)‖ = 1 := by
    rw [← norm_mul, ← Subalgebra.coe_mul, Units.mul_inv]; simp
  have h2 := norm_le_one_of_mem_coefO c u
  have h3 := norm_le_one_of_mem_coefO c (u⁻¹ : c.Oˣ)
  have h4 := norm_nonneg ((u : c.O) : PadicAlgCl l)
  nlinarith

theorem mem_coefO_of_memE_norm_le_one : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (x : Qbar l),
    MemE c x → ‖x‖ ≤ 1 → x ∈ c.O := by
  intro l _ c x hE hx
  obtain ⟨k, hk⟩ := hE
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · simpa using hk
  set y : c.O := ⟨_, hk⟩ with hy
  set L : c.O := (l : c.O) ^ k with hL
  have hLval : ((L : c.O) : PadicAlgCl l) = (l : PadicAlgCl l) ^ k := by simp [hL]
  have hl0 : (l : PadicAlgCl l) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hL0 : L ≠ 0 := by
    intro h
    have : ((L : c.O) : PadicAlgCl l) = 0 := by rw [h]; rfl
    rw [hLval] at this
    exact pow_ne_zero k hl0 this
  have hnl : ‖(l : PadicAlgCl l)‖ = (l : ℝ)⁻¹ := by
    have : (l : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
    rw [this, norm_algebraMap', Padic.norm_p]
  by_cases hy0 : y = 0
  · have : (l : PadicAlgCl l) ^ k * x = 0 := by
      have := congrArg (fun z : c.O => (z : PadicAlgCl l)) hy0
      simpa [hy] using this
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h (pow_ne_zero k hl0)
    · rw [h]; exact c.O.zero_mem
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible c.O
  have key : ∀ z : c.O, z ≠ 0 → ∃ n : ℕ, ‖(z : PadicAlgCl l)‖ = ‖(ϖ : PadicAlgCl l)‖ ^ n ∧
      ϖ ^ n ∣ z ∧ z ∣ ϖ ^ n := by
    intro z hz
    obtain ⟨n, u, h⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hz hϖ
    refine ⟨n, ?_, ?_, ?_⟩
    · rw [h, Subalgebra.coe_mul, norm_mul, norm_unit_coefO, one_mul, Subalgebra.coe_pow, norm_pow]
    · exact ⟨(u : c.O), by rw [h, mul_comm]⟩
    · exact ⟨((u⁻¹ : c.Oˣ) : c.O), by rw [h, mul_comm, ← mul_assoc, Units.inv_mul, one_mul]⟩
  obtain ⟨a, hya, hdy, -⟩ := key y hy0
  obtain ⟨b, hLb, -, hdL⟩ := key L hL0
  have hϖ1 : ‖(ϖ : PadicAlgCl l)‖ ≤ 1 := norm_le_one_of_mem_coefO c ϖ
  have hϖ0 : 0 < ‖(ϖ : PadicAlgCl l)‖ := by
    rw [norm_pos_iff]
    intro h
    exact hϖ.ne_zero (Subtype.ext h)
  have hlt1 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  have hyx : ((y : c.O) : PadicAlgCl l) = (l : PadicAlgCl l) ^ k * x := rfl
  have hLlt : ‖((L : c.O) : PadicAlgCl l)‖ < 1 := by
    rw [hLval, norm_pow, hnl]
    exact pow_lt_one₀ (by positivity) hlt1 (by omega)
  have hϖlt : ‖(ϖ : PadicAlgCl l)‖ < 1 := by
    rcases lt_or_eq_of_le hϖ1 with h | h
    · exact h
    exfalso
    rw [hLb, h, one_pow] at hLlt
    exact lt_irrefl _ hLlt
  have hab : b ≤ a := by
    have hle : ‖(ϖ : PadicAlgCl l)‖ ^ a ≤ ‖(ϖ : PadicAlgCl l)‖ ^ b := by
      rw [← hya, ← hLb, hyx, hLval, norm_mul]
      calc ‖(l : PadicAlgCl l) ^ k‖ * ‖x‖ ≤ ‖(l : PadicAlgCl l) ^ k‖ * 1 :=
            mul_le_mul_of_nonneg_left hx (norm_nonneg _)
        _ = _ := mul_one _
    exact (pow_le_pow_iff_right_of_lt_one₀ hϖ0 hϖlt).1 hle
  have hdiv : L ∣ y := dvd_trans hdL (dvd_trans (pow_dvd_pow ϖ hab) hdy)
  obtain ⟨z, hz⟩ := hdiv
  have : (l : PadicAlgCl l) ^ k * x = (l : PadicAlgCl l) ^ k * (z : PadicAlgCl l) := by
    rw [← hyx, hz, Subalgebra.coe_mul, hLval]
  rw [mul_left_cancel₀ (pow_ne_zero k hl0) this]
  exact z.2

end GlobalTheory.Ord2
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MobToGQScalar
section
open GlobalTheory.KZ GlobalTheory.Ord2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V
open scoped MatrixGroups

namespace GlobalTheory.KZ

theorem Tower.kmap_refl {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε)
    (l : ℕ) [Fact l.Prime] (x : X.Khat l) : X.kmap l (RingEquiv.refl X.K) x = x := by
  unfold Tower.kmap
  have : (AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive (Units.map (RingEquiv.refl X.K).toMonoidHom))) =
      (LinearMap.id : Additive X.Kˣ →ₗ[ℤ] Additive X.Kˣ) := by
    ext x; rfl
  rw [this, LinearMap.baseChange_id, AdicCompletion.map_id]
  rfl

end GlobalTheory.KZ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NatCastIsUnitPadicInt
section
namespace GlobalTheory.PadicInversePower

open Formalism.ConjugateSelfDual

theorem natCast_isUnit_padicInt (l : ℕ) [Fact (Nat.Prime l)] (n : ℕ) (h : ¬ l ∣ n) : IsUnit (n : ℤ_[l]) := by
  rw [PadicInt.isUnit_iff]
  refine le_antisymm (PadicInt.norm_le_one _) ?_
  by_contra hlt
  push_neg at hlt
  have : ‖((n : ℤ) : ℤ_[l])‖ < 1 := by simpa using hlt
  rw [PadicInt.norm_int_lt_one_iff_dvd] at this
  exact h (Int.natCast_dvd_natCast.mp this)

theorem inv_pow_mem (l : ℕ) [Fact (Nat.Prime l)] (c : UpperTheory.V.HV.Coef l) (e r : ℕ) (x : (ZMod (l ^ r))ˣ) :
    ((((x : ZMod (l ^ r)).val : ℕ) : Formalism.ConjugateSelfDual.Qbar l) ^ e)⁻¹ ∈ UpperTheory.V.HV.Coef.O c := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · have h0 : (x : ZMod (l ^ 0)).val = 0 := by
      haveI : NeZero (l ^ 0) := ⟨by simp⟩
      have := ZMod.val_lt (x : ZMod (l ^ 0))
      simp only [pow_zero] at this
      omega
    rw [h0]
    rcases Nat.eq_zero_or_pos e with rfl | he
    · simp only [pow_zero, inv_one]; exact c.O.one_mem
    · simp only [Nat.cast_zero, zero_pow he.ne', inv_zero]; exact c.O.zero_mem
  · set n := (x : ZMod (l ^ r)).val with hn
    have hcop : Nat.Coprime n (l ^ r) := ZMod.val_coe_unit_coprime x
    have hnd : ¬ l ∣ n := by
      intro hd
      have := Nat.Coprime.coprime_dvd_left hd hcop
      have h1 : Nat.Coprime l l := Nat.Coprime.coprime_dvd_right (dvd_pow_self l hr.ne') this
      have hl1 : l = 1 := by simpa using h1
      exact (Fact.out : Nat.Prime l).one_lt.ne' hl1
    obtain ⟨u, hu⟩ := natCast_isUnit_padicInt l n hnd
    have key : (((n : ℕ) : Formalism.ConjugateSelfDual.Qbar l) ^ e)⁻¹ = algebraMap ℤ_[l] (Formalism.ConjugateSelfDual.Qbar l) ((u⁻¹ : ℤ_[l]ˣ) ^ e : ℤ_[l]ˣ) := by
      rw [Units.val_pow_eq_pow_val, map_pow, ← inv_pow, ← map_natCast (algebraMap ℤ_[l] (Formalism.ConjugateSelfDual.Qbar l)) n, ← hu]
      congr 1
      symm
      apply eq_inv_of_mul_eq_one_left
      rw [← map_mul, Units.inv_mul, map_one]
    rw [key]
    exact c.O.algebraMap_mem _

end GlobalTheory.PadicInversePower
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonzeroClassBoundedTorsion
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2.GwCount

theorem exists_bound_of_mem_span {K E ι : Type} [NormedField K] [AddCommGroup E] [Module K E] (φ : ι → E →ₗ[K] K)
    (f : E →ₗ[K] K) (hf : f ∈ Submodule.span K (Set.range φ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : E) (r : ℝ), 0 ≤ r → (∀ j, ‖φ j p‖ ≤ r) → ‖f p‖ ≤ C * r := by
  first
  | exact @_root_.GlobalTheory.NormBoundOfSpan.norm_le_of_mem_span
  | exact _root_.GlobalTheory.NormBoundOfSpan.norm_le_of_mem_span
  | (apply _root_.GlobalTheory.NormBoundOfSpan.norm_le_of_mem_span <;> assumption)
  | (intros; apply _root_.GlobalTheory.NormBoundOfSpan.norm_le_of_mem_span <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NormBoundOfSpan.norm_le_of_mem_span <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NormBoundOfSpan.norm_le_of_mem_span ..)

theorem exists_bound_multiplier {K Γ : Type} [NormedField K] (M : Γ → Matrix (Fin 2) (Fin 2) K) (Y : Γ → Fin 2 → K)
    (hY : ¬ ∃ x : Fin 2 → K, ∀ s, Y s = M s *ᵥ x - x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : K) (x : Fin 2 → K) (r : ℝ), 0 ≤ r →
      (∀ s i, ‖(a • Y s) i - (M s *ᵥ x - x) i‖ ≤ r) → ‖a‖ ≤ C * r := by
  let φ : Γ × Fin 2 → (K × (Fin 2 → K)) →ₗ[K] K := fun j =>
    (LinearMap.proj j.2).comp (((LinearMap.fst K K (Fin 2 → K)).smulRight (Y j.1)) -
      ((Matrix.toLin' (M j.1) - LinearMap.id).comp (LinearMap.snd K K (Fin 2 → K))))
  have hφ : ∀ s i a x, φ (s, i) (a, x) = (a • Y s) i - (M s *ᵥ x - x) i := by
    intro s i a x
    simp only [φ, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smulRight_apply, LinearMap.fst_apply,
      LinearMap.snd_apply, LinearMap.id_apply, Matrix.toLin'_apply, LinearMap.proj_apply, Pi.sub_apply]
  have hker : ⨅ j, LinearMap.ker (φ j) ≤ LinearMap.ker (LinearMap.fst K K (Fin 2 → K)) := by
    rintro ⟨a, x⟩ h
    simp only [Submodule.mem_iInf, LinearMap.mem_ker] at h
    simp only [LinearMap.mem_ker, LinearMap.fst_apply]
    by_contra ha
    refine hY ⟨a⁻¹ • x, fun s => ?_⟩
    have h1 : a • Y s = M s *ᵥ x - x := by
      funext i
      have := h (s, i)
      rw [hφ] at this
      exact sub_eq_zero.1 this
    rw [Matrix.mulVec_smul, ← smul_sub, ← h1, smul_smul, inv_mul_cancel₀ ha, one_smul]
  obtain ⟨C, hC, h⟩ := exists_bound_of_mem_span φ _ (FiniteDimensional.mem_span_of_iInf_ker_le_ker hker)
  exact ⟨C, hC, fun a x r hr hb => h (a, x) r hr fun j => by rw [show j = (j.1, j.2) from rfl, hφ]; exact hb _ _⟩

theorem closed_multiplier : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (W : R2 Ω l) (c : Coef l) (Y : G ℚ Ω → Fin 2 → Qbar l), (∀ s i j, mat W s i j ∈ c.O) → Y ∈ Z1 (Loc.colRep W) → (∀ s i, Y s i ∈ c.O) → Y ∉ ReciprocityTheory.Gal.B1 (Loc.colRep W) → ∃ k0 : ℕ, ∀ (n : ℕ) (a : Qbar l), a ∈ c.O → Cob1 c n W ⊤ (fun s => a • Y s) → Cg n (a * ((l : ℕ) : Qbar l) ^ k0) 0 := by
  intro l hl Ω _ _ _ W c Y _ _ _ hY
  obtain ⟨C, hC, h⟩ := exists_bound_multiplier (mat W) Y (by
    rintro ⟨x, hx⟩
    refine hY ⟨x, ?_⟩
    funext s
    rw [hx s]
    simp [ReciprocityTheory.Gal.d0, Loc.colRep, Matrix.toLin'_apply])
  have hlt : ‖((l : ℕ) : Qbar l)‖ < 1 := by
    rw [← map_natCast (algebraMap ℚ_[l] (Qbar l)), norm_algebraMap']
    exact Padic.norm_p_lt_one
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < (C + 1)⁻¹ by positivity) hlt
  refine ⟨k, fun n a _ ⟨x, _, hx⟩ => ?_⟩
  have h1 := h a x _ (norm_nonneg _) fun s i => hx s (Subgroup.mem_top s) i
  unfold Cg
  rw [sub_zero, norm_mul, norm_pow _ k]
  have h2 : C * ‖((l : ℕ) : Qbar l)‖ ^ k ≤ 1 := by
    calc C * ‖((l : ℕ) : Qbar l)‖ ^ k ≤ (C + 1) * (C + 1)⁻¹ :=
          mul_le_mul (by linarith) hk.le (by positivity) (by positivity)
      _ = 1 := mul_inv_cancel₀ (by positivity)
  calc ‖a‖ * ‖((l : ℕ) : Qbar l)‖ ^ k ≤ C * ‖((l : ℕ) : Qbar l) ^ n‖ * ‖((l : ℕ) : Qbar l)‖ ^ k :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = ‖((l : ℕ) : Qbar l) ^ n‖ * (C * ‖((l : ℕ) : Qbar l)‖ ^ k) := by ring
    _ ≤ _ := mul_le_of_le_one_right (norm_nonneg _) h2

end GlobalTheory.Ord2.GwCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormIntCastLeOfDvd
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA
open scoped Matrix

namespace GlobalTheory.PowCong

variable {l : ℕ} [Fact l.Prime]

theorem norm_intCast_eq (k : ℤ) : ‖(k : Qbar l)‖ = ‖(k : ℚ_[l])‖ := by
  rw [show (k : Qbar l) = algebraMap ℚ_[l] (PadicAlgCl l) (k : ℚ_[l]) from (map_intCast _ k).symm]
  exact PadicAlgCl.norm_extends l _

theorem norm_natCast_eq (n : ℕ) : ‖(n : Qbar l)‖ = ‖(n : ℚ_[l])‖ := by
  have := norm_intCast_eq (l := l) (n : ℤ)
  simpa using this

theorem norm_l_pow (r : ℕ) : ‖((l : ℕ) : Qbar l) ^ r‖ = (l : ℝ) ^ (-(r : ℤ)) := by
  rw [norm_pow, norm_natCast_eq, Padic.norm_p, zpow_neg, zpow_natCast, inv_pow]

theorem norm_intCast_le_of_dvd (r : ℕ) (k : ℤ) (h : ((l : ℤ) ^ r) ∣ k) : ‖(k : Qbar l)‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ := by
  rw [norm_intCast_eq, norm_l_pow]
  exact (Padic.norm_int_le_pow_iff_dvd k r).mpr h

theorem norm_natCast_eq_one {n : ℕ} (h : ¬ l ∣ n) : ‖(n : Qbar l)‖ = 1 := by
  rw [norm_natCast_eq, Padic.norm_natCast_eq_one_iff]
  exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr h

theorem key (r e a b : ℕ) (ha : ¬ l ∣ a) (hb : b = a % l ^ r) (hb' : 1 ≤ r → ¬ l ∣ b) :
    ‖((a : Qbar l) ^ e)⁻¹ - ((b : Qbar l) ^ e)⁻¹‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ ∧
      ‖(a : Qbar l) ^ e - (b : Qbar l) ^ e‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ := by
  have hcong : ((l : ℤ) ^ r) ∣ (((a ^ e : ℕ) : ℤ) - ((b ^ e : ℕ) : ℤ)) := by
    have h1 := (Nat.mod_modEq a (l ^ r)).pow e
    have h2 := (Nat.modEq_iff_dvd.mp h1)
    rw [hb]
    push_cast at h2 ⊢
    exact h2
  have hsub : ‖(a : Qbar l) ^ e - (b : Qbar l) ^ e‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ := by
    have := norm_intCast_le_of_dvd (l := l) r _ hcong
    push_cast at this
    exact this
  refine ⟨?_, hsub⟩
  have hna : ‖(a : Qbar l)‖ = 1 := norm_natCast_eq_one ha
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    have hb0 : b = 0 := by rw [hb, pow_zero, Nat.mod_one]
    subst hb0
    rcases Nat.eq_zero_or_pos e with he | he
    · subst he; simp
    · rw [Nat.cast_zero, zero_pow he.ne', inv_zero, sub_zero, norm_inv, norm_pow, hna]
      simp
  · have hnb : ‖(b : Qbar l)‖ = 1 := norm_natCast_eq_one (hb' hr)
    have ha0 : ((a : Qbar l) ^ e) ≠ 0 := by
      intro h; have := congrArg norm h; rw [norm_pow, hna] at this; simp at this
    have hb0 : ((b : Qbar l) ^ e) ≠ 0 := by
      intro h; have := congrArg norm h; rw [norm_pow, hnb] at this; simp at this
    rw [inv_sub_inv ha0 hb0, norm_div, norm_mul, norm_pow, norm_pow, hna, hnb, one_pow, mul_one, div_one,
      norm_sub_rev]
    exact hsub

theorem powCong : ∀ (l : ℕ) [Fact l.Prime] (e r : ℕ) (x : (ZMod (l ^ (r + 1)))ˣ), ‖(((x : ZMod (l ^ (r + 1))).val : Qbar l) ^ e)⁻¹ - (((((Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom) x : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)).val : Qbar l) ^ e)⁻¹‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ ∧ ‖((x : ZMod (l ^ (r + 1))).val : Qbar l) ^ e - ((((Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom) x : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)).val : Qbar l) ^ e‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ := by
  intro l hl e r x
  have hp : l.Prime := hl.out
  haveI : NeZero (l ^ (r + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have notdvd : ∀ {k : ℕ}, 1 ≤ k → (u : (ZMod (l ^ k))ˣ) → ¬ l ∣ (u : ZMod (l ^ k)).val := by
    intro k hk u hd
    have hc := ZMod.val_coe_unit_coprime u
    have : l ∣ Nat.gcd (u : ZMod (l ^ k)).val (l ^ k) := Nat.dvd_gcd hd (dvd_pow_self l (by omega))
    rw [hc] at this
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  refine key (l := l) r e _ _ (notdvd (by omega) x) ?_ (fun hr => notdvd hr _)
  rw [Units.coe_map]
  simp only [MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, ZMod.castHom_apply]
  rw [ZMod.cast_eq_val, ZMod.val_natCast]

end GlobalTheory.PowCong
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormLePowIffDvdStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_le_pow_iff_dvd : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (n : ℕ) (x : c.O), ‖((x : c.O) : Qbar l)‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖ ↔ ((l : ℕ) : c.O) ^ n ∣ x := by
  first | exact @GlobalTheory.Coef.norm_le_norm_pow_iff_dvd | exact GlobalTheory.Coef.norm_le_norm_pow_iff_dvd | (intros; apply GlobalTheory.Coef.norm_le_norm_pow_iff_dvd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NotCongruentZeroIntCastMulPrimePow
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2.IntNorm

theorem norm_intCast_qbar (l : ℕ) [Fact l.Prime] (d : ℤ) :
    ‖(d : Qbar l)‖ = ‖(d : ℚ_[l])‖ := by
  have h : (d : Qbar l) = ((d : ℚ_[l]) : PadicAlgCl l) := by simp
  rw [h, PadicAlgCl.norm_extends]

theorem norm_l_qbar (l : ℕ) [Fact l.Prime] : ‖((l : ℕ) : Qbar l)‖ = (l : ℝ)⁻¹ := by
  have h : ((l : ℕ) : Qbar l) = (((l : ℕ) : ℚ_[l]) : PadicAlgCl l) := by simp
  rw [h, PadicAlgCl.norm_extends, Padic.norm_p]

theorem not_cg_int_mul_pow (l : ℕ) [Fact l.Prime] (t k : ℕ) (d : ℤ) (hd : d ≠ 0)
    (hlt : |d| < (l : ℤ) ^ t) : ¬ Cg (t + k) ((d : Qbar l) * ((l : ℕ) : Qbar l) ^ k) 0 := by
  intro h
  unfold Cg at h
  rw [sub_zero, norm_mul, norm_pow, norm_pow, pow_add] at h
  have hlpos : (0 : ℝ) < ‖((l : ℕ) : Qbar l)‖ := by
    rw [norm_l_qbar]; have := (Fact.out : l.Prime).pos; positivity
  have hk : (0 : ℝ) < ‖((l : ℕ) : Qbar l)‖ ^ k := pow_pos hlpos k
  have h1 : ‖(d : Qbar l)‖ ≤ ‖((l : ℕ) : Qbar l)‖ ^ t := le_of_mul_le_mul_right h hk
  rw [norm_intCast_qbar, norm_l_qbar] at h1
  have h2 : ‖(d : ℚ_[l])‖ ≤ (l : ℝ) ^ (-(t : ℤ)) := by
    rw [zpow_neg, zpow_natCast, ← inv_pow]; exact h1
  have h3 : ((l : ℤ) ^ t) ∣ d := (Padic.norm_int_le_pow_iff_dvd d t).mp h2
  have h4 : ((l : ℤ) ^ t) ≤ |d| := by
    have := Int.le_of_dvd (abs_pos.mpr hd) ((dvd_abs _ _).mpr h3)
    exact this
  omega

end GlobalTheory.Ord2.IntNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicHomSmallOnDeepCongruenceSubgroupsStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padicHom_small_on_deep_congruence_subgroups : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ] (r : Γ →* GL (Fin 2) (Qbar l)) (lam : Γ →* Multiplicative ℤ_[l]), Continuous r → Continuous lam → r.ker ≤ lam.ker → ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ g : Γ, (∀ i j, ‖((r g : Matrix (Fin 2) (Fin 2) (Qbar l)) - 1) i j‖ ≤ ‖((l : ℕ) : Qbar l) ^ N‖) → ‖(lam g).toAdd‖ ≤ ε := by
  first | exact @GlobalTheory.lam_small_of_deep_congruence | exact GlobalTheory.lam_small_of_deep_congruence | (intros; apply GlobalTheory.lam_small_of_deep_congruence <;> assumption)
end

