import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0018
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0017
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertiaTorsionQuotientConjInvariantDecomposition
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0385
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0033
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0019
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0394
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0395

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.QuotientCharTrivialInertiaCyclotomicTower
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries

noncomputable section

namespace GlobalTheory.QuotInertia

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem fix_mu [IsAlgClosure ℚ Ω] (s : G ℚ Ω) (hs : cycBar ℚ Ω l s = 1) (ζ : Ω) (hζ : ζ ^ l = 1) :
    s ζ = ζ := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have hinj : Function.Injective ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom) :=
    (algebraMap ℚ_[l] (Qbar l)).injective.comp (fun a b h => Subtype.ext h)
  have hz : cycZ ℚ Ω l s = 1 := by
    apply Units.map_injective (f := ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom).toMonoidHom) hinj
    rw [map_one]
    exact hs
  have hz' : cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G ℚ Ω) Ω s) = 1 := hz
  have h := cyclotomicCharacter.spec l (n := 1) (MulSemiringAction.toRingAut (G ℚ Ω) Ω s) ζ (by rw [pow_one]; exact hζ)
  change s ζ = _ at h
  rw [h, hz', Units.val_one, map_one, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by rw [pow_one]; exact (Fact.out : l.Prime).one_lt), pow_one]

theorem fix_sqrt_unit (hl : l ≠ 2) {A : ValuationSubring Ω} (hA : OverL l A) {s : G ℚ Ω}
    (hs : s ∈ Ine (F := ℚ) A) (N : ℤ) (hN : ¬ (l : ℤ) ∣ N) (β : Ω) (hβ : β ^ 2 = N) : s β = β := by
  have hsq : (s β) ^ 2 = β ^ 2 := by rw [← map_pow, hβ, map_intCast]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
  · exact h
  exfalso
  obtain ⟨-, hI⟩ := hs
  have hβ1 : A.valuation β ≤ 1 := by
    by_contra hc
    push_neg at hc
    have h1 : 1 < A.valuation β ^ 2 := one_lt_pow₀ hc two_ne_zero
    rw [← map_pow, hβ] at h1
    have : A.valuation (N : Ω) ≤ 1 := (A.valuation_le_one_iff _).2 (intCast_mem A N)
    exact absurd h1 (not_lt.2 this)
  have h2 := hI β hβ1
  rw [h] at h2
  have h3 : A.valuation (((4 * N : ℤ) : Ω)) < 1 := by
    have e : ((4 * N : ℤ) : Ω) = (-β - β) ^ 2 := by push_cast; rw [← hβ]; ring
    rw [e, map_pow]
    exact pow_lt_one₀ zero_le' h2 two_ne_zero
  obtain ⟨v, hv, hlv⟩ := hA
  have h4 : ((4 * N : ℤ) : 𝓞 ℚ) ∈ v.asIdeal := by
    rw [← hv]
    convert h3 using 2
    simp only [map_intCast, Int.cast_mul, Int.cast_ofNat, map_mul, map_ofNat, algebraMap.coe_mul, map_ratCast]
  have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp Fact.out
  have hcop : IsCoprime (l : ℤ) (4 * N) := by
    rw [hp.irreducible.coprime_iff_not_dvd]
    intro hd
    rcases hp.dvd_or_dvd hd with h5 | h5
    · have h6 : l ∣ 4 := by exact_mod_cast h5
      have h7 : l ∣ 2 := (Fact.out : l.Prime).dvd_of_dvd_pow (n := 2) (by norm_num; exact h6)
      exact hl ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 h7)
    · exact hN h5
  obtain ⟨a, b, hab⟩ := hcop.map (Int.castRingHom (𝓞 ℚ))
  have hl' : (Int.castRingHom (𝓞 ℚ)) (l : ℤ) ∈ v.asIdeal := by simpa using hlv
  have h1 : (1 : 𝓞 ℚ) ∈ v.asIdeal := by
    rw [← hab]
    exact add_mem (Ideal.mul_mem_left _ _ hl') (Ideal.mul_mem_left _ _ (by simpa using h4))
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)

theorem gauss_fix [IsAlgClosure ℚ Ω] (hl : l ≠ 2) (s : G ℚ Ω) (hs : ∀ ζ : Ω, ζ ^ l = 1 → s ζ = ζ) :
    ∃ (Gs : Ω) (c : ℤ), c ^ 2 = 1 ∧ Gs ^ 2 = ((c * l : ℤ) : Ω) ∧ s Gs = Gs := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω l
  have hF : ringChar (ZMod l) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hl
  set ψ : AddChar (ZMod l) Ω := AddChar.zmodChar l hζ.pow_eq_one with hψdef
  have hψ : ψ.IsPrimitive := AddChar.zmodChar_primitive_of_primitive_root l hζ
  set χ : MulChar (ZMod l) Ω := (quadraticChar (ZMod l)).ringHomComp (Int.castRingHom Ω) with hχdef
  have hχ1 : χ ≠ 1 :=
    (MulChar.ringHomComp_ne_one_iff (Int.cast_injective (α := Ω))).2 (quadraticChar_ne_one hF)
  have hχ2 : χ.IsQuadratic := (quadraticChar_isQuadratic (ZMod l)).comp _
  have hχa : ∀ x, χ x = ((quadraticChar (ZMod l) x : ℤ) : Ω) := fun x => rfl
  refine ⟨gaussSum χ ψ, quadraticChar (ZMod l) (-1), quadraticChar_sq_one (neg_ne_zero.2 one_ne_zero), ?_, ?_⟩
  · rw [gaussSum_sq hχ1 hχ2 hψ, hχa, ZMod.card]
    push_cast
    rfl
  · rw [gaussSum, map_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [map_mul, hχa, map_intCast, hψdef, AddChar.zmodChar_apply, map_pow, hs ζ hζ.pow_eq_one]

theorem fix_sqrt_int [IsAlgClosure ℚ Ω] (hl : l ≠ 2) {A : ValuationSubring Ω} (hA : OverL l A) {s : G ℚ Ω}
    (hs : s ∈ Ine (F := ℚ) A) (hmu : ∀ ζ : Ω, ζ ^ l = 1 → s ζ = ζ) :
    ∀ (N : ℤ) (α : Ω), α ^ 2 = N → s α = α := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  intro N
  induction hn : N.natAbs using Nat.strong_induction_on generalizing N with
  | _ n ih =>
  intro α hα
  by_cases h0 : N = 0
  · subst h0
    have : α = 0 := pow_eq_zero_iff two_ne_zero |>.1 (by simpa using hα)
    rw [this, map_zero]
  by_cases hd : (l : ℤ) ∣ N
  · obtain ⟨N1, rfl⟩ := hd
    obtain ⟨Gs, c, hc, hG, hsG⟩ := gauss_fix hl s hmu
    have hc0 : (c : Ω) ≠ 0 := by
      rintro h
      have : c = 0 := by exact_mod_cast h
      rw [this] at hc
      norm_num at hc
    have hl0 : (l : Ω) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
    have hG0 : Gs ≠ 0 := by
      rintro h
      rw [h] at hG
      push_cast at hG
      exact mul_ne_zero hc0 hl0 (by rw [← hG]; ring)
    have hc' : (c : Ω) ^ 2 = 1 := by exact_mod_cast hc
    have hβ : (α / Gs) ^ 2 = ((c * N1 : ℤ) : Ω) := by
      rw [div_pow, hα, hG]
      push_cast
      rw [div_eq_iff (mul_ne_zero hc0 hl0)]
      linear_combination (-(l : Ω) * N1) * hc'
    have hcabs : c.natAbs = 1 := by
      have h1 : (c ^ 2).natAbs = 1 := by rw [hc]; rfl
      rw [Int.natAbs_pow] at h1
      exact (pow_eq_one_iff.1 h1).resolve_right two_ne_zero
    have hN1 : N1 ≠ 0 := by rintro rfl; exact h0 (mul_zero _)
    have hlt : (c * N1).natAbs < n := by
      rw [← hn, Int.natAbs_mul, Int.natAbs_mul, hcabs, one_mul, Int.natAbs_natCast]
      have := Int.natAbs_pos.2 hN1
      have := (Fact.out : l.Prime).one_lt
      nlinarith
    have h1 := ih _ hlt (c * N1) rfl (α / Gs) hβ
    have e : α = α / Gs * Gs := (div_mul_cancel₀ α hG0).symm
    rw [e, map_mul, h1, hsG]
  · exact fix_sqrt_unit hl hA hs N hd α hα

theorem fix_sqrt_rat [IsAlgClosure ℚ Ω] (hl : l ≠ 2) {A : ValuationSubring Ω} (hA : OverL l A) {s : G ℚ Ω}
    (hs : s ∈ Ine (F := ℚ) A) (hmu : ∀ ζ : Ω, ζ ^ l = 1 → s ζ = ζ) (α : Ω) (q : ℚ)
    (hα : α ^ 2 = algebraMap ℚ Ω q) : s α = α := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have hden : (q.den : Ω) ≠ 0 := Nat.cast_ne_zero.2 q.den_nz
  have hq : algebraMap ℚ Ω q * (q.den : Ω) = (q.num : Ω) := by
    rw [← map_natCast (algebraMap ℚ Ω), ← map_mul, Rat.mul_den_eq_num, map_intCast]
  have h := fix_sqrt_int hl hA hs hmu (q.num * q.den) (α * q.den) (by
    rw [mul_pow, hα]
    push_cast
    rw [← hq]
    ring)
  rw [map_mul, map_natCast] at h
  exact mul_right_cancel₀ hden h

theorem dt_eq_one [IsAlgClosure ℚ Ω] {W : R2 Ω l} (hcont : Continuous W) (hdet2 : dt W ^ 2 = 1) (s : G ℚ Ω)
    (hfix : ∀ (α : Ω) (q : ℚ), α ^ 2 = algebraMap ℚ Ω q → s α = α) : dt W s = 1 := by
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have hval : ∀ g, ((dt W g : (Qbar l)ˣ) : Qbar l) = ((W g : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)).det :=
    fun g => Matrix.GeneralLinearGroup.val_det_apply _
  have hc : Continuous fun g : G ℚ Ω => ((dt W g : (Qbar l)ˣ) : Qbar l) := by
    simp only [hval]
    exact (Units.continuous_val.comp hcont).matrix_det
  have hcl : IsClosed ((dt W).ker : Set (G ℚ Ω)) := by
    have : ((dt W).ker : Set (G ℚ Ω)) = (fun g : G ℚ Ω => ((dt W g : (Qbar l)ˣ) : Qbar l)) ⁻¹' {1} := by
      ext g
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun h => by rw [h, Units.val_one], fun h => Units.ext (by rw [h, Units.val_one])⟩
    rw [this]
    exact isClosed_singleton.preimage hc
  let Hc : ClosedSubgroup (G ℚ Ω) := ⟨(dt W).ker, hcl⟩
  have hpm : ∀ g, dt W g = 1 ∨ dt W g = -1 := by
    intro g
    have h2 : (dt W g) ^ 2 = 1 := by
      have := congrArg (fun f => f g) hdet2
      simpa using this
    have hv : ((dt W g : (Qbar l)ˣ) : Qbar l) * ((dt W g : (Qbar l)ˣ) : Qbar l) = 1 := by
      rw [← Units.val_mul, ← pow_two, h2, Units.val_one]
    rcases mul_self_eq_one_iff.1 hv with h | h
    · exact Or.inl (Units.ext (by rw [h, Units.val_one]))
    · exact Or.inr (Units.ext (by rw [h, Units.val_neg, Units.val_one]))
  have hsub : s ∈ (IntermediateField.fixedField (Hc : Subgroup (G ℚ Ω))).fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    rw [IntermediateField.mem_fixedField_iff] at hx
    have hsame : ∀ g1 g2 : G ℚ Ω, dt W g1 = dt W g2 → g1 x = g2 x := by
      intro g1 g2 h
      have hm : g2⁻¹ * g1 ∈ (Hc : Subgroup (G ℚ Ω)) := by
        show g2⁻¹ * g1 ∈ (dt W).ker
        rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
      have h1 := hx _ hm
      calc g1 x = g2 ((g2⁻¹ * g1) x) := by
            rw [AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]
        _ = g2 x := by rw [h1]
    rcases hpm s with h1 | h1
    · exact hx s (show s ∈ (dt W).ker from h1)
    have hs2 : (s * s) x = x := by
      rw [hsame (s * s) 1 (by rw [map_mul, h1, map_one]; simp)]
      rfl
    have hsα : s (x - s x) = -(x - s x) := by
      rw [map_sub, ← AlgEquiv.mul_apply, hs2]
      ring
    have hgα : ∀ g : G ℚ Ω, (g (x - s x)) ^ 2 = (x - s x) ^ 2 := by
      intro g
      rw [map_sub, ← AlgEquiv.mul_apply]
      rcases hpm g with h2 | h2
      · rw [hsame g 1 (by rw [h2, map_one]), hsame (g * s) s (by rw [map_mul, h2, one_mul])]
        rfl
      · rw [hsame g s (by rw [h2, h1]), hsame (g * s) 1 (by rw [map_mul, h2, h1, map_one]; simp)]
        show (s x - x) ^ 2 = (x - s x) ^ 2
        ring
    obtain ⟨q, hq⟩ : ∃ q : ℚ, (x - s x) ^ 2 = algebraMap ℚ Ω q := by
      have hmem : (x - s x) ^ 2 ∈ IntermediateField.fixedField (⊥ : IntermediateField ℚ Ω).fixingSubgroup := by
        rw [IntermediateField.mem_fixedField_iff]
        intro f _
        rw [map_pow]
        exact hgα f
      rw [InfiniteGalois.fixedField_fixingSubgroup, IntermediateField.mem_bot] at hmem
      obtain ⟨q, hq⟩ := hmem
      exact ⟨q, hq.symm⟩
    have h3 := hfix _ q hq
    rw [hsα] at h3
    have h4 : (2 : Ω) * (x - s x) = 0 := by linear_combination -h3
    have h5 := (mul_eq_zero.1 h4).resolve_left two_ne_zero
    exact (sub_eq_zero.1 h5).symm
  rw [InfiniteGalois.fixingSubgroup_fixedField Hc] at hsub
  exact hsub

end GlobalTheory.QuotInertia

open GlobalTheory.QuotInertia in

theorem GlobalTheory.quot_eq_one_of_cycBar_eq_one : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (ι : Qbar l ≃+* ℂ) (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l) (g : Newform (2 * e + 1)),
    Nf e S A W → SrcUr ι e A W g → ∀ s ∈ Ine (F := ℚ) A, cycBar ℚ Ω l s = 1 → mat W s 1 1 = 1 := by
  intro l _ Ω _ _ _ ι e S A W g hNf hSrc s hs hc
  obtain ⟨-, -, χ, hχ, -, hI⟩ := hSrc
  have hmu := fix_mu s hc
  have hχs : χ s = 1 := hχ s hmu
  have hdt := dt_eq_one hNf.cont hNf.det2 s (fun α q hq => fix_sqrt_rat hNf.l_odd hNf.atL hs hmu α q hq)
  have h := hI s hs
  rw [hc, hχs, hdt] at h
  simpa using h

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ShiftedCocycleLimitIntegral
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA
open scoped Matrix

namespace GlobalTheory.InertCoh

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem norm_le_one_of_isIntegral (x : PadicAlgCl l) (hx : IsIntegral ℤ_[l] x) : ‖x‖ ≤ 1 := by
  have hc : ∀ c : ℤ_[l], ‖algebraMap ℤ_[l] (PadicAlgCl l) c‖ ≤ 1 := by
    intro c
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), norm_algebraMap']
    exact c.2
  by_contra h
  push_neg at h
  obtain ⟨p, hm, hp⟩ := hx
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hm.coeff_natDegree, map_one, one_mul] at hp
  have h1 : x ^ p.natDegree = - ∑ i ∈ Finset.range p.natDegree, algebraMap ℤ_[l] (PadicAlgCl l) (p.coeff i) * x ^ i :=
    eq_neg_of_add_eq_zero_right hp
  rcases Nat.eq_zero_or_pos p.natDegree with hz | hz
  · rw [hz] at h1; simp at h1
  have h2 : ‖∑ i ∈ Finset.range p.natDegree, algebraMap ℤ_[l] (PadicAlgCl l) (p.coeff i) * x ^ i‖ ≤
      ‖x‖ ^ (p.natDegree - 1) := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i hi => ?_
    rw [norm_mul, norm_pow]
    have hi' := Finset.mem_range.1 hi
    calc _ ≤ 1 * ‖x‖ ^ i := mul_le_mul_of_nonneg_right (hc _) (by positivity)
      _ ≤ _ := by rw [one_mul]; exact pow_le_pow_right₀ h.le (by omega)
  rw [← norm_neg, ← h1, norm_pow] at h2
  exact absurd h2 (not_le.2 (pow_lt_pow_right₀ h (by omega)))

theorem norm_le_one_of_mem_O (c : Coef l) {x : Qbar l} (hx : x ∈ c.O) : ‖x‖ ≤ 1 :=
  norm_le_one_of_isIntegral x ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) (⟨x, hx⟩ : c.O)).map c.O.val)

theorem mat_mul (W : R2 Ω l) (s t : G ℚ Ω) : mat W (s * t) = mat W s * mat W t := by
  simp [mat, map_mul, Units.val_mul]

def frobOp (W : R2 Ω l) (c : Coef l) (φ : G ℚ Ω) :
    (G ℚ Ω → Fin 2 → Qbar l) →ₗ[c.O] (G ℚ Ω → Fin 2 → Qbar l) where
  toFun z s := mat W φ *ᵥ z (φ⁻¹ * s * φ)
  map_add' a b := by funext s; simp [Matrix.mulVec_add]
  map_smul' k a := by funext s; simp [Matrix.mulVec_smul]

theorem frobOp_apply (W : R2 Ω l) (c : Coef l) (φ : G ℚ Ω) (z : G ℚ Ω → Fin 2 → Qbar l) (s : G ℚ Ω) :
    frobOp W c φ z s = mat W φ *ᵥ z (φ⁻¹ * s * φ) := rfl

theorem conj_mem_Ine' {B : ValuationSubring Ω} {φ s : G ℚ Ω} (hφ : φ ∈ Dec (F := ℚ) B)
    (hs : s ∈ Ine (F := ℚ) B) : φ⁻¹ * s * φ ∈ Ine (F := ℚ) B := by
  have := conj_mem_Ine ((Dec (F := ℚ) B).inv_mem hφ) hs
  rwa [inv_inv] at this

theorem frobOp_cob (W : R2 Ω l) (c : Coef l) (B : ValuationSubring Ω) {φ : G ℚ Ω} (hφ : φ ∈ Dec (F := ℚ) B) :
    cob W c (Ine (F := ℚ) B) ≤ (cob W c (Ine (F := ℚ) B)).comap (frobOp W c φ) := by
  rintro z ⟨v, hv⟩
  refine ⟨mat W φ *ᵥ v, fun s hs => ?_⟩
  rw [frobOp_apply, hv _ (conj_mem_Ine' hφ hs), Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    ← mat_mul, ← mat_mul]
  congr 2
  group

theorem frobOp_coc (W : R2 Ω l) (c : Coef l) (B : ValuationSubring Ω) (hWO : ∀ s i j, mat W s i j ∈ c.O)
    {φ : G ℚ Ω} (hφ : φ ∈ Dec (F := ℚ) B) :
    ∀ z ∈ coc W c (Ine (F := ℚ) B), frobOp W c φ z ∈ coc W c (Ine (F := ℚ) B) := by
  rintro z ⟨h1, h2, h3⟩
  have hconj : Continuous fun s : G ℚ Ω => φ⁻¹ * s * φ := (continuous_const.mul continuous_id).mul continuous_const
  refine ⟨fun i => ?_, fun s i => ?_, fun s hs t ht => ?_⟩
  · simp only [frobOp_apply, Matrix.mulVec, dotProduct]
    exact continuous_finset_sum _ fun j _ => continuous_const.mul ((h1 j).comp hconj)
  · simp only [frobOp_apply, Matrix.mulVec, dotProduct]
    exact Subalgebra.sum_mem _ fun j _ => Subalgebra.mul_mem _ (hWO _ _ _) (h2 _ _)
  · simp only [frobOp_apply]
    have e : φ⁻¹ * (s * t) * φ = (φ⁻¹ * s * φ) * (φ⁻¹ * t * φ) := by group
    rw [e, h3 _ (conj_mem_Ine' hφ hs) _ (conj_mem_Ine' hφ ht), Matrix.mulVec_add, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, ← mat_mul, ← mat_mul]
    congr 3
    group

variable [IsAlgClosure ℚ Ω]

theorem cycMod_eq_one_of_mem_Ine {B : ValuationSubring Ω} {q : Pl} (hB : IsPlaceOver B q)
    (hl : ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal) (r : ℕ) {s : G ℚ Ω} (hs : s ∈ Ine (F := ℚ) B) :
    cycMod ℚ Ω l r s = 1 := by
  have h := cycZ_toZModPow_eq hl hB (q := 1) (fun x hx => by simpa using hs.2 x hx) r
  ext
  simp only [cycMod, MonoidHom.coe_comp, Function.comp_apply, Units.coe_map, Units.val_one]
  rw [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, h]
  simp

theorem coprime_normV {q : Pl} (hl : ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal) : Nat.Coprime (normV q) l := by
  have hp := GlobalTheory.TameConjInv.prime_normV q
  refine (Nat.coprime_primes hp (Fact.out : l.Prime)).2 fun h => hl ?_
  have hmem : ((normV q : ℕ) : 𝓞 ℚ) ∈ q.asIdeal := Ideal.absNorm_mem q.asIdeal
  rwa [h] at hmem

theorem cycMod_frob {B : ValuationSubring Ω} {q : Pl} (hB : IsPlaceOver B q) (hl : ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal)
    {φ : G ℚ Ω} (hφ : IsFrob B (normV q) φ) (r : ℕ) :
    cycMod ℚ Ω l r φ = ZMod.unitOfCoprime (normV q) (Nat.Coprime.pow_right r (coprime_normV hl)) := by
  have h := cycZ_of_isFrob hl hB hφ
  ext
  simp only [cycMod, MonoidHom.coe_comp, Function.comp_apply, Units.coe_map, ZMod.coe_unitOfCoprime]
  rw [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, h]
  simp

end GlobalTheory.InertCoh

namespace GlobalTheory.InertCoh

theorem not_isUnit_natCast_O {l : ℕ} [Fact l.Prime] (c : Coef l) : ¬ IsUnit ((l : ℕ) : c.O) := by
  rintro ⟨u, hu⟩
  have h1 : ((u : c.O) : Qbar l) * ((u⁻¹ : c.Oˣ) : c.O) = 1 := by
    rw [← Subalgebra.coe_mul, Units.mul_inv, Subalgebra.coe_one]
  have h2 : ((u : c.O) : Qbar l) = ((l : ℕ) : Qbar l) := by rw [hu]; simp
  have hl : ‖((l : ℕ) : Qbar l)‖ < 1 := by
    have e : ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by rw [map_natCast]
    rw [e, PadicAlgCl.norm_extends l (l : ℚ_[l]), Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  have h3 := norm_le_one_of_mem_O c (((u⁻¹ : c.Oˣ) : c.O)).2
  have h4 := congrArg norm h1
  rw [norm_mul, norm_one, h2] at h4
  have : ‖((l : ℕ) : Qbar l)‖ * ‖(((u⁻¹ : c.Oˣ) : c.O) : Qbar l)‖ < 1 :=
    lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) h3) hl
  linarith

theorem unr_of_limit_spec : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (W : R2 Ω l) (c : Coef l) (Y : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l) (η : ∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l) (y : G ℚ Ω → Fin 2 → Qbar l), Continuous W → (∀ s i j, mat W s i j ∈ c.O) → (∀ r x i, Continuous fun s => Y r s x i) → (∀ r s x i, Y r s x i ∈ c.O) → (∀ r, ShCoc (mat W) (cycMod ℚ Ω l r)⁻¹ (Y r)) → (∀ r s, Y r s = push (Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom) (Y (r + 1)) s) → (∀ r x, η r x ∈ c.O) → (∀ r s i, ‖y s i - spec (η r) (Y r) s i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) → ∀ q : Pl, ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∃ B : ValuationSubring Ω, IsPlaceOver B q ∧ ∃ v : Fin 2 → Qbar l, ∀ s ∈ Ine (F := ℚ) B, y s = mat W s *ᵥ v - v := by
  intro l _ Ω _ _ _ W c Y η y hW hWO hYc hYO hsh hnorm hη hy q hl
  obtain ⟨B, hB⟩ := exists_isPlaceOver Ω q
  refine ⟨B, hB, ?_⟩
  obtain ⟨φ, hφ⟩ := exists_isFrob hB
  obtain ⟨γ, hγ⟩ := GlobalTheory.TameInertiaGen.exists_tameGenAt ℚ Ω q B hB
  have hq := coprime_normV hl
  let u : ∀ r : ℕ, (ZMod (l ^ r))ˣ := fun r => ZMod.unitOfCoprime (normV q) (Nat.Coprime.pow_right r hq)
  let z : ∀ r : ℕ, (ZMod (l ^ r))ˣ → G ℚ Ω → Fin 2 → Qbar l := fun r x s => Y r s x
  have hzZ : ∀ r x, z r x ∈ coc W c (Ine (F := ℚ) B) := by
    intro r x
    refine ⟨fun i => hYc r x i, fun s i => hYO r s x i, fun s hs t _ => ?_⟩
    have h := hsh r s t x
    simp only [MonoidHom.inv_apply, cycMod_eq_one_of_mem_Ine hB hl r hs, inv_one, mul_one] at h
    exact h
  have hFB := frobOp_cob W c B hφ.1
  let FH := (cob W c (Ine (F := ℚ) B)).mapQ (cob W c (Ine (F := ℚ) B)) (frobOp W c φ) hFB
  have hFM : ∀ x ∈ (coc W c (Ine (F := ℚ) B)).map (cob W c (Ine (F := ℚ) B)).mkQ,
      FH x ∈ (coc W c (Ine (F := ℚ) B)).map (cob W c (Ine (F := ℚ) B)).mkQ := by
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨frobOp W c φ w, frobOp_coc W c B hWO hφ.1 w hw, rfl⟩
  have hfrob : ∀ r x, FH ((cob W c (Ine (F := ℚ) B)).mkQ (z r x)) =
      (cob W c (Ine (F := ℚ) B)).mkQ (z r (x * u r)) := by
    intro r x
    show Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    rw [← sub_eq_zero, ← Submodule.Quotient.mk_sub, Submodule.Quotient.mk_eq_zero]
    refine ⟨Y r φ (x * u r), fun s hs => ?_⟩
    have h1 := hsh r φ (φ⁻¹ * s * φ) (x * u r)
    have h2 := hsh r s φ (x * u r)
    rw [MonoidHom.inv_apply, cycMod_frob hB hl hφ r] at h1
    rw [MonoidHom.inv_apply, cycMod_eq_one_of_mem_Ine hB hl r hs, inv_one, mul_one] at h2
    have e : φ * (φ⁻¹ * s * φ) = s * φ := by group
    rw [e, h2, mul_inv_cancel_right] at h1
    show mat W φ *ᵥ Y r (φ⁻¹ * s * φ) x - Y r s (x * u r) = mat W s *ᵥ Y r φ (x * u r) - Y r φ (x * u r)
    calc mat W φ *ᵥ Y r (φ⁻¹ * s * φ) x - Y r s (x * u r)
        = (Y r φ (x * u r) + mat W φ *ᵥ Y r (φ⁻¹ * s * φ) x) - Y r φ (x * u r) - Y r s (x * u r) := by abel
      _ = (Y r s (x * u r) + mat W s *ᵥ Y r φ (x * u r)) - Y r φ (x * u r) - Y r s (x * u r) := by rw [h1]
      _ = _ := by abel
  have hN : ∀ r x, (cob W c (Ine (F := ℚ) B)).mkQ (z r x) = ∑ x' ∈ Finset.univ.filter (fun x' : (ZMod (l ^ (r + 1)))ˣ =>
      Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom x' = x),
      (cob W c (Ine (F := ℚ) B)).mkQ (z (r + 1) x') := by
    intro r x
    rw [← map_sum]
    congr 1
    funext s
    rw [Finset.sum_apply]
    show Y r s x = _
    rw [hnorm r s]
    rfl
  have hFG : ((coc W c (Ine (F := ℚ) B)).map (cob W c (Ine (F := ℚ) B)).mkQ).FG :=
    GlobalTheory.T.fg_inertiaCocycles_mod_coboundaries_coefRing l Ω W c (Ine (F := ℚ) B) {σ | ∀ y : Ω, y ≠ 0 → B.valuation (σ y / y - 1) < 1} γ hW hWO
      (fun w hw => GlobalTheory.T.exists_integral_coboundary_wildInertia_away_from_l l Ω W c B q hW hWO hB hl w hw)
      (fun w hw hP h0 => GlobalTheory.T.inertiaCocycle_eq_zero_of_vanish_wild_tameGenerator l Ω W B γ hγ w hw.1 hw.2.2 (fun σ hσ => hP σ hσ) h0)
  have hlO : ¬ IsUnit ((l : ℕ) : c.O) := not_isUnit_natCast_O c
  haveI : IsLocalRing c.O := IsDiscreteValuationRing.toIsLocalRing
  haveI : IsNoetherianRing c.O := inferInstance
  have hzero := GlobalTheory.T.normCompatible_system_frobenius_eq_zero c.O _ l hlO (normV q) hq (GlobalTheory.TameConjInv.prime_normV q).two_le
    ((coc W c (Ine (F := ℚ) B)).map (cob W c (Ine (F := ℚ) B)).mkQ) hFG FH hFM
    (fun r x => (cob W c (Ine (F := ℚ) B)).mkQ (z r x)) (fun r x => Submodule.mem_map_of_mem (hzZ r x)) hfrob hN
  have hspec : ∀ r, spec (η r) (Y r) ∈ cob W c (Ine (F := ℚ) B) := by
    intro r
    have e : spec (η r) (Y r) = ∑ x, (⟨η r x, hη r x⟩ : c.O) • z r x := by
      funext s
      simp only [spec, Finset.sum_apply, Pi.smul_apply, Subalgebra.smul_def]
      rfl
    rw [e]
    refine Submodule.sum_mem _ fun x _ => Submodule.smul_mem _ _ ?_
    have h := hzero r x
    rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h
  exact GlobalTheory.T.coboundary_of_padicAlgCl_uniform_approx l (G ℚ Ω) (Ine (F := ℚ) B : Set (G ℚ Ω)) (mat W) (fun r => spec (η r) (Y r)) y
    (fun s i j => norm_le_one_of_mem_O c (hWO s i j)) (fun r => hspec r) hy

end GlobalTheory.InertCoh

end
end

