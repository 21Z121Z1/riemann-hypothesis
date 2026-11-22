import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SpreadLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0089
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.DedekindZetaEqSumRealEisenstein
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0011
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.SplitK
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.DiscrB
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0025
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0142

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotDvdDiscrIffRamificationIdx
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Mem.RaySplit

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem.Fld

section General

theorem not_dvd_discr_iff_ramificationIdx (E : Type) [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) :
    ¬ (p : ℤ) ∣ discr E ↔ ∀ P : Ideal (𝓞 E), P.IsPrime → (p : 𝓞 E) ∈ P → P.ramificationIdx ℤ = 1 := by
  rw [NumberField.not_dvd_discr_iff_forall_mem E (𝓞 E) (Nat.prime_iff_prime_int.mp hp)]
  refine forall_congr' fun P => forall_congr' fun hP => ?_
  rw [Int.cast_natCast]
  refine forall_congr' fun hlP => ?_
  have hP0 : P ≠ ⊥ := by
    rintro rfl
    exact hp.ne_zero (by simpa using hlP)
  have := hP.isMaximal hP0
  have : (P.under ℤ).IsMaximal := inferInstance
  have hne : P.under ℤ ≠ ⊥ := by
    intro h0
    have h1 : (p : ℤ) ∈ P.under ℤ := by rw [Ideal.under_def, Ideal.mem_comap]; simpa using hlP
    rw [h0] at h1
    exact hp.ne_zero (by simpa using h1)
  have : Finite (ℤ ⧸ P.under ℤ) := Ideal.finiteQuotientOfFreeOfNeBot _ hne
  have : Finite (P.under ℤ).ResidueField := inferInstance
  exact Ideal.ramificationIdx_eq_one_iff.symm

theorem not_mem_sq {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) {P : Ideal (𝓞 E)} [hP : P.IsPrime]
    (hv : (p : 𝓞 E) ∈ P) (he : P.ramificationIdx ℤ = 1) : (p : 𝓞 E) ∉ P ^ 2 := by
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  have hmap : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(p : ℤ)}) = Ideal.span {(p : 𝓞 E)} := by
    rw [Ideal.map_span]; simp
  have hle : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(p : ℤ)}) ≤ P := by
    rw [hmap, Ideal.span_le]; simpa using hv
  have : P.LiesOver (Ideal.span {(p : ℤ)}) :=
    ⟨hmax.eq_of_le (Ideal.comap_ne_top _ hP.ne_top) (Ideal.map_le_iff_le_comap.mp hle)⟩
  have hb : Ideal.span {(p : ℤ)} ≠ ⊥ := by simpa using hp.ne_zero
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {(p : ℤ)}) P hb] at he
  intro h2
  refine (Ideal.ramificationIdx'_ne_one_iff hle).2 ?_ he
  rw [hmap, Ideal.span_le]
  simpa using h2

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem exists_under {p : ℕ} (hp : p.Prime) (P : Ideal (𝓞 L)) [P.IsPrime] (h : (p : 𝓞 L) ∈ P) :
    ∃ 𝔭 : HeightOneSpectrum (𝓞 K), P.LiesOver 𝔭.asIdeal ∧ (p : 𝓞 K) ∈ 𝔭.asIdeal := by
  have h1 : (p : 𝓞 K) ∈ P.under (𝓞 K) := by
    rw [Ideal.under_def, Ideal.mem_comap, map_natCast]; exact h
  refine ⟨⟨P.under (𝓞 K), inferInstance, fun h0 => ?_⟩, ⟨rfl⟩, h1⟩
  rw [h0] at h1
  exact hp.ne_zero (by simpa using h1)

theorem not_dvd_discr_of_unramIn [IsGalois K L] {p : ℕ} (hp : p.Prime) (hK : ¬ (p : ℤ) ∣ discr K)
    (hu : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ 𝔭.asIdeal → UnramIn L 𝔭) : ¬ (p : ℤ) ∣ discr L := by
  rw [not_dvd_discr_iff_ramificationIdx _ hp] at hK ⊢
  intro P hP h
  obtain ⟨𝔭, hPo, h𝔭⟩ := exists_under (K := K) hp P h
  have := 𝔭.isMaximal
  have : Finite (𝓞 K ⧸ 𝔭.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ 𝔭.ne_bot
  have : P.IsMaximal := hP.isMaximal (Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot P)
  have h1 : P.inertia (L ≃ₐ[K] L) = ⊥ := (Subgroup.eq_bot_iff_forall _).2 fun τ hτ => hu 𝔭 h𝔭 τ ⟨P, hP, hPo, hτ⟩
  have h2 := Ideal.card_inertia_eq_ramificationIdxIn (G := L ≃ₐ[K] L) 𝔭.asIdeal P
  rw [h1, Subgroup.card_bot, Ideal.ramificationIdxIn_eq_ramificationIdx _ P (L ≃ₐ[K] L)] at h2
  rw [Ideal.ramificationIdx_tower (R := ℤ) 𝔭.asIdeal P, hK _ 𝔭.isPrime h𝔭, ← h2]

theorem heckeIdeal_asIdeal (χ : (L ≃ₐ[K] L) →* ℂˣ) (𝔮 : HeightOneSpectrum (𝓞 K)) :
    heckeIdeal L χ 𝔮.asIdeal = heckeVal L χ 𝔮 := by
  classical
  unfold heckeIdeal
  rw [finprod_eq_single _ 𝔮]
  · rw [Associates.count_self 𝔮.associates_irreducible, pow_one]
  · intro 𝔭 hne
    rw [Associates.count_eq_zero_of_ne 𝔭.associates_irreducible 𝔮.associates_irreducible, pow_zero]
    intro h
    exact hne (HeightOneSpectrum.ext (associated_iff_eq.1 (Associates.mk_eq_mk_iff_associated.1 h)))

theorem not_dvd_span {p c : ℕ} (hp : p.Prime) (hc : ¬ p ∣ c) (𝔭 : HeightOneSpectrum (𝓞 K))
    (h : (p : 𝓞 K) ∈ 𝔭.asIdeal) : ¬ 𝔭.asIdeal ∣ Ideal.span {(c : 𝓞 K)} := by
  rw [Ideal.dvd_span_singleton]
  intro h'
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hc)
  have h1 := congrArg (Int.cast : ℤ → 𝓞 K) hab
  push_cast at h1
  exact 𝔭.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (h1 ▸ add_mem (Ideal.mul_mem_left _ _ h) (Ideal.mul_mem_left _ _ h')))

theorem absNorm_eq_of_span {𝔮 : Ideal (𝓞 K)} (hR : IsRayField K L 𝔮) (hK : IsEmpty (K →+* ℝ))
    (𝔭 : HeightOneSpectrum (𝓞 K)) {π : 𝓞 K} (hπ : 𝔭.asIdeal = Ideal.span {π}) (h1 : π - 1 ∈ 𝔮)
    (P : Ideal (𝓞 L)) [hP : P.IsPrime] [hPo : P.LiesOver 𝔭.asIdeal] :
    Ideal.absNorm P = Ideal.absNorm 𝔭.asIdeal := by
  have := hR.1
  have hcop : IsCoprime 𝔭.asIdeal 𝔮 := by
    rw [hπ]
    exact Ideal.isCoprime_iff_exists.2 ⟨π, Ideal.mem_span_singleton_self _, -(π - 1), neg_mem h1, by ring⟩
  have hnd : ¬ 𝔭.asIdeal ∣ 𝔮 := fun h => 𝔭.prime.not_unit (hcop.isUnit_of_dvd' dvd_rfl h)
  have hπ0 : π ≠ 0 := by
    rintro rfl
    exact 𝔭.ne_bot (by simpa using hπ)
  have hχ := (hR.2.2.2 𝔭.asIdeal 𝔭.ne_bot hcop).2 ⟨π, 1,
    ⟨hπ0, one_ne_zero, hπ ▸ hcop, by rw [Ideal.span_singleton_one, ← Ideal.one_eq_top]; exact isCoprime_one_left,
      h1, fun φ => hK.elim φ⟩, by simp [hπ]⟩
  have hne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot P
  have hfP : Finite (𝓞 L ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot _ hne
  have hfv : Finite (𝓞 K ⧸ 𝔭.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ 𝔭.ne_bot
  have := 𝔭.isPrime
  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant (𝓞 K) (L ≃ₐ[K] L) P
  have hσ1 : σ = 1 := GlobalTheory.RayMaximal.eq_of_forall_char fun χ => Units.ext (by
    rw [← heckeVal_of_unramIn L χ (hR.2.1 𝔭 hnd) ((isFrob_iff L 𝔭 σ).2 ⟨P, hP, hPo, hσ⟩), ← heckeIdeal_asIdeal,
      hχ χ, map_one, Units.val_one])
  have hle : Nat.card (𝓞 L ⧸ P) ≤ Nat.card (𝓞 K ⧸ 𝔭.asIdeal) := by
    refine card_le_of_pow_eq_self Finite.one_lt_card fun x => ?_
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    have h2 := hσ x
    rw [hσ1, ← hPo.over] at h2
    rw [← map_pow]
    refine (Ideal.Quotient.eq.2 ?_).symm
    simpa using h2
  have hinj : Function.Injective (algebraMap (𝓞 K ⧸ 𝔭.asIdeal) (𝓞 L ⧸ P)) := FaithfulSMul.algebraMap_injective _ _
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact (Nat.card_eq_of_bijective _ (hinj.bijective_of_nat_card_le hle)).symm

theorem dvd_of_dvd_discr {c : ℕ} (hR : IsRayField K L (Ideal.span {(c : 𝓞 K)})) {p : ℕ} (hp : p.Prime)
    (h : (p : ℤ) ∣ discr L) : p ∣ c ∨ (p : ℤ) ∣ discr K := by
  have := hR.1
  by_contra hc
  rw [not_or] at hc
  exact not_dvd_discr_of_unramIn hp hc.2 (fun 𝔭 h𝔭 => hR.2.1 𝔭 (not_dvd_span hp hc.1 𝔭 h𝔭)) h

theorem absNorm_eq_of_mul (h2 : Module.finrank ℚ K = 2) {p : ℕ} (hp : p.Prime) {π π' : 𝓞 K} (h : π * π' = p)
    (hu : ¬ IsUnit π) (hu' : ¬ IsUnit π') : Ideal.absNorm (Ideal.span {π}) = p := by
  have h1 : Ideal.absNorm (Ideal.span {π}) * Ideal.absNorm (Ideal.span {π'}) = p ^ 2 := by
    rw [← map_mul, Ideal.span_singleton_mul_span_singleton, h, Ideal.absNorm_span_singleton,
      ← map_natCast (algebraMap ℤ (𝓞 K)), Algebra.norm_algebraMap, RingOfIntegers.rank, h2]
    simp
  obtain ⟨i, hi, e⟩ := (Nat.dvd_prime_pow hp).1 ⟨_, h1.symm⟩
  interval_cases i
  · exact absurd (Ideal.span_singleton_eq_top.1 (Ideal.absNorm_eq_one_iff.1 (by simpa using e))) hu
  · simpa using e
  · rw [e] at h1
    have h3 := (Nat.mul_eq_left (pow_ne_zero 2 hp.ne_zero)).1 h1
    exact absurd (Ideal.span_singleton_eq_top.1 (Ideal.absNorm_eq_one_iff.1 h3)) hu'

theorem ncard_primesOver_eq {c : ℕ} (hR : IsRayField K L (Ideal.span {(c : 𝓞 K)})) (hK : IsEmpty (K →+* ℝ))
    (h2 : Module.finrank ℚ K = 2) {p : ℕ} (hp : p.Prime) (hd : ¬ (p : ℤ) ∣ discr L) {π π' : 𝓞 K} (h : π * π' = p)
    (hu : ¬ IsUnit π) (hu' : ¬ IsUnit π') (hc : (c : 𝓞 K) ∣ π - 1) (hc' : (c : 𝓞 K) ∣ π' - 1) :
    (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 L)).ncard = Module.finrank ℚ L := by
  refine GlobalTheory.ncard_primesOver_eq_finrank_of_absNorm_eq_of_not_mem_sq L p hp fun P hP hpP => ?_
  refine ⟨?_, not_mem_sq hp hpP ((not_dvd_discr_iff_ramificationIdx L hp).1 hd P hP.isPrime hpP)⟩
  obtain ⟨𝔭, hPo, h𝔭⟩ := exists_under (K := K) hp P hpP
  have key : ∀ a : 𝓞 K, Ideal.absNorm (Ideal.span {a}) = p → (c : 𝓞 K) ∣ a - 1 → a ∈ 𝔭.asIdeal →
      Ideal.absNorm P = p := fun a hN ha hm => by
    have hpr : (Ideal.span {a}).IsPrime := Ideal.isPrime_of_irreducible_absNorm (by rw [hN]; exact hp)
    have hb : Ideal.span {a} ≠ ⊥ := fun h0 => hp.ne_zero (by rw [← hN, h0, Ideal.absNorm_bot])
    have e : Ideal.span {a} = 𝔭.asIdeal :=
      (hpr.isMaximal hb).eq_of_le 𝔭.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 hm)
    rw [absNorm_eq_of_span hR hK 𝔭 e.symm (Ideal.mem_span_singleton.2 ha) P, ← e, hN]
  rcases 𝔭.isPrime.mem_or_mem (h ▸ h𝔭) with hm | hm
  · exact key π (absNorm_eq_of_mul h2 hp h hu hu') hc hm
  · exact key π' (absNorm_eq_of_mul h2 hp ((mul_comm _ _).trans h) hu' hu) hc' hm

end General

section Host

variable {R : Ranks} (H : Host R)

abbrev condIdeal : Ideal (𝓞 H.K) := Ideal.span {((H.QS * H.q * H.d : ℕ) : 𝓞 H.K)}

theorem cond_ne_zero : H.QS * H.q * H.d ≠ 0 := by
  have h1 := H.hyp.1.ne_zero
  have h2 := H.hyp.2.1.ne_zero
  have h3 := H.QS_pos.ne'
  positivity

theorem condIdeal_ne_bot : condIdeal H ≠ ⊥ := by
  rw [Ne, Ideal.span_singleton_eq_bot]
  exact_mod_cast cond_ne_zero H

theorem finrank_K : Module.finrank ℚ H.K = 2 :=
  Formalism.FrobeniusOrbits.SplitK.finrank_K H.hyp.2.1.pos (H.sqd_sq)

theorem discr_K : NumberField.discr H.K = -(H.d : ℤ) :=
  discr_eq_neg_of_sq_eq (finrank_K H) H.hyp.2.1.squarefree (by have := H.hyp.2.2.2.1; omega)
    (Formalism.FrobeniusOrbits.SplitK.bK_sq (H.sqd_sq))

theorem isEmpty_real : IsEmpty (H.K →+* ℝ) := ⟨fun φ => by
  obtain ⟨x, hx⟩ : ∃ x : H.K, x ^ 2 = -(H.d : H.K) := ⟨_, Formalism.FrobeniusOrbits.SplitK.bK_sq (H.sqd_sq)⟩
  have h := congrArg φ hx
  rw [map_pow, map_neg, map_natCast] at h
  have h5 : (0 : ℝ) < H.d := by exact_mod_cast H.hyp.2.1.pos
  nlinarith [sq_nonneg (φ x)]⟩

variable {H} {M : Type} [Field M] [NumberField M] [Algebra H.K M]

theorem isGalois_of_ray (hM : IsRayField H.K M (condIdeal H)) : IsGalois H.K M :=
  have := hM.1
  inferInstance

theorem comm_of_ray (hM : IsRayField H.K M (condIdeal H)) (σ τ : M ≃ₐ[H.K] M) : σ * τ = τ * σ :=
  have := hM.1
  mul_comm' σ τ

theorem unr_of_ray (hM : IsRayField H.K M (condIdeal H)) (p : ℕ) (hp : p.Prime) (h : (p : ℤ) ∣ discr M) :
    p ∣ H.QS * H.q * H.d := by
  rcases dvd_of_dvd_discr hM hp h with h | h
  · exact h
  · rw [discr_K, dvd_neg] at h
    exact Dvd.dvd.mul_left (by exact_mod_cast h) _

end Host

end GlobalTheory.Mem.RaySplit

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrimeDvdOfMemDifferent
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld GlobalTheory.Mem.FieldsEx
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.KPsiRam

theorem prime_dvd_of_mem_different (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (N : ℕ) (hmem : (N : 𝓞 L) ∈ differentIdeal (𝓞 K) (𝓞 L)) {p : ℕ} (hp : p.Prime) (h : p ∣ (discr L).natAbs) :
    p ∣ N ∨ p ∣ (discr K).natAbs := by
  have h1 := NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow K (𝓞 K) L (𝓞 L)
  have h2 : Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 L)) ∣ Ideal.absNorm (Ideal.span {(N : 𝓞 L)}) :=
    Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 hmem)
  rw [Ideal.absNorm_span_natCast] at h2
  rw [h1] at h
  exact ((Nat.Prime.dvd_mul hp).1 h).imp (fun h => hp.dvd_of_dvd_pow (h.trans h2)) hp.dvd_of_dvd_pow

theorem sup_adjoin_root (F : IntermediateField ℚ ℂ) [NumberField F] {k : ℕ} (hk : 0 < k) {y : F}
    (hy : y ∈ powIdealElts F k) {z : ℂ} (hz : z ^ k = (y : ℂ)) :
    ∃ _ : NumberField ↥(F ⊔ ℚ⟮z⟯), ∀ p : ℕ, p.Prime → p ∣ (discr ↥(F ⊔ ℚ⟮z⟯)).natAbs →
      p ∣ k ∨ p ∣ (discr F).natAbs := by
  obtain ⟨hy, I, hI⟩ := hy
  have hI' : (I : Submodule (𝓞 F) F) ^ k = Submodule.span (𝓞 F) {y} := by
    rw [← FractionalIdeal.coe_pow, ← hI, FractionalIdeal.coe_spanSingleton]
  set L : IntermediateField ℚ ℂ := F ⊔ ℚ⟮z⟯ with hLdef
  have hzL : z ∈ L := (le_sup_right : ℚ⟮z⟯ ≤ L) (IntermediateField.mem_adjoin_simple_self ℚ z)
  have hzF : IsIntegral F z := IsIntegral.of_pow hk (by rw [hz]; exact isIntegral_algebraMap (x := y))
  have hzQ : IsIntegral ℚ z := isIntegral_trans z hzF
  haveI : FiniteDimensional ℚ ℚ⟮z⟯ := IntermediateField.adjoin.finiteDimensional hzQ
  have hLfin : FiniteDimensional ℚ L := IntermediateField.finiteDimensional_sup F ℚ⟮z⟯
  letI : NumberField L := NumberField.mk
  letI : Algebra F L := (IntermediateField.inclusion (le_sup_left : F ≤ L)).toRingHom.toAlgebra
  haveI : IsScalarTower F L ℂ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hz' : (⟨z, hzL⟩ : L) ^ k = algebraMap F L y := Subtype.ext hz
  have hzi : IsIntegral F (⟨z, hzL⟩ : L) := Algebra.IsIntegral.isIntegral _
  have htop : F⟮(⟨z, hzL⟩ : L)⟯ = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨w, hw⟩ -
    let M : IntermediateField ℚ ℂ :=
      ((F⟮(⟨z, hzL⟩ : L)⟯).map (IsScalarTower.toAlgHom F L ℂ)).restrictScalars ℚ
    have hM : L ≤ M := by
      refine sup_le (fun v hv => ?_) (IntermediateField.adjoin_simple_le_iff.mpr ?_)
      · exact ((F⟮(⟨z, hzL⟩ : L)⟯).map (IsScalarTower.toAlgHom F L ℂ)).algebraMap_mem ⟨v, hv⟩
      · exact ⟨_, IntermediateField.mem_adjoin_simple_self F _, rfl⟩
    obtain ⟨w', hw', hww⟩ := hM hw
    have : w' = ⟨w, hw⟩ := Subtype.ext hww
    rwa [this] at hw'
  have htop' : Algebra.adjoin F {(⟨z, hzL⟩ : L)} = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hzi.isAlgebraic, htop,
      IntermediateField.top_toSubalgebra]
  have hD := GlobalTheory.FieldSize.natCast_mem_differentIdeal_of_root k hk y hy _ hI' _ hz' htop'
  exact ⟨inferInstance, fun p hp h => prime_dvd_of_mem_different F L k hD hp h⟩

theorem sup_adjoin_roots {E : Type} [Field E] [NumberField E] (φ : E →+* ℂ) {h : ℕ} (hh : 0 < h) (S : Set ℂ)
    (hS : S.Finite) (hS' : ∀ z ∈ S, ∃ y ∈ powIdealElts E h, z ^ h = φ y) :
    ∃ _ : NumberField ↥(imField φ ⊔ IntermediateField.adjoin ℚ S), ∀ p : ℕ, p.Prime →
      p ∣ (discr ↥(imField φ ⊔ IntermediateField.adjoin ℚ S)).natAbs → p ∣ h ∨ p ∣ (discr E).natAbs := by
  induction S, hS using Set.Finite.induction_on with
  | empty =>
    rw [IntermediateField.adjoin_empty, sup_bot_eq]
    let e₀ : E ≃ₐ[ℚ] imField φ := AlgEquiv.ofInjectiveField φ.toRatAlgHom
    have : FiniteDimensional ℚ (imField φ) := e₀.toLinearEquiv.finiteDimensional
    have hN : NumberField (imField φ) := NumberField.of_module_finite ℚ _
    exact ⟨hN, fun p _ hp => Or.inr (by rwa [discr_eq_discr_of_algEquiv _ e₀])⟩
  | @insert z S _ _ ih =>
    obtain ⟨_, ih⟩ := ih fun w hw => hS' w (Set.mem_insert_of_mem _ hw)
    obtain ⟨y, hy, hz⟩ := hS' z (Set.mem_insert _ _)
    have hE : ∀ x, φ x ∈ imField φ ⊔ IntermediateField.adjoin ℚ S := (imField_le_iff φ).1 le_sup_left
    obtain ⟨hN, H⟩ := sup_adjoin_root _ hh (map_mem_pow (φ.codRestrict _ hE) hy) hz
    rw [Set.insert_eq, Set.union_comm, IntermediateField.adjoin_union, ← sup_assoc]
    exact ⟨hN, fun p hp hd => (H p hp hd).elim Or.inl (ih p hp)⟩

theorem typeNorm_mem {R : Ranks} (H : Host R) (p q : ℕ) {h : ℕ} {γ : H.E} (hγ : γ ∈ powIdealElts H.E h) :
    typeNorm H p q γ ∈ powIdealElts H.E h := by
  have hσ : ∀ (σ : H.E ≃ₐ[ℚ] H.E) {x}, x ∈ powIdealElts H.E h → σ x ∈ powIdealElts H.E h :=
    fun σ _ hx => map_mem_pow (σ : H.E →+* H.E) hx
  exact prod_mem_pow _ _ fun g _ => mul_mem_pow (npow_mem_pow (hσ _ hγ) _) (npow_mem_pow (hσ _ (hσ _ hγ)) _)

theorem prime_dvd_discr_iSup_kPsi : ∀ (P : Pre) (δ : FieldDat P),
    ∃ _ : NumberField ↥(⨆ j ∈ Set.Icc 1 P.R.m, δ.KPsi j), ∀ p : ℕ, p.Prime →
      p ∣ (discr ↥(⨆ j ∈ Set.Icc 1 P.R.m, δ.KPsi j)).natAbs → p ∣ classNumber P.host.E * (discr P.host.E).natAbs := by
  intro P δ
  let S : Set ℂ := {rootOne (classNumber P.host.E)} ∪ ⋃ j ∈ Set.Icc 1 P.R.m, ⋃ i,
    {z | z ^ δ.basis.h i = P.host.φ₀ (typeNorm P.host (P.R.sigW j).1 (P.R.sigW j).2 (δ.basis.γ i : P.host.E))}
  have hS : S.Finite := by
    refine (Set.finite_singleton _).union ((Set.finite_Icc _ _).biUnion fun j _ => Set.finite_iUnion fun i => ?_)
    refine Set.Finite.subset (Polynomial.nthRoots (δ.basis.h i) (P.host.φ₀
      (typeNorm P.host (P.R.sigW j).1 (P.R.sigW j).2 (δ.basis.γ i : P.host.E)))).toFinset.finite_toSet fun z hz => ?_
    rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_nthRoots (δ.basis.h_pos i)]
    exact hz
  have hS' : ∀ z ∈ S, ∃ y ∈ powIdealElts P.host.E (classNumber P.host.E), z ^ classNumber P.host.E = P.host.φ₀ y := by
    rintro z (rfl | hz)
    · exact ⟨1, one_mem_pow, by
        rw [map_one]; exact (Complex.isPrimitiveRoot_exp _ (classNumber_ne_zero _)).pow_eq_one⟩
    · simp only [Set.mem_iUnion] at hz
      obtain ⟨j, -, i, hz⟩ := hz
      have hγ : (δ.basis.γ i : P.host.E) ∈ powIdealElts P.host.E (δ.basis.h i) :=
        ⟨(δ.basis.γ i).ne_zero, δ.basis.c i, by
          rw [← coe_toPrincipalIdeal, ← δ.basis.pow_eq i, Units.val_pow_eq_pow_val]; rfl⟩
      obtain ⟨k, hk⟩ : δ.basis.h i ∣ classNumber P.host.E := orderOf_dvd_card
      refine ⟨_, hk ▸ pow_mem_powIdealElts (typeNorm_mem P.host (P.R.sigW j).1 (P.R.sigW j).2 hγ) k, ?_⟩
      rw [hk, pow_mul, map_pow]
      exact congrArg (· ^ k) hz
  obtain ⟨_, H⟩ := sup_adjoin_roots P.host.φ₀ (classNumber_pos P.host.E) S hS hS'
  have hle : (⨆ j ∈ Set.Icc 1 P.R.m, δ.KPsi j) ≤ imField P.host.φ₀ ⊔ IntermediateField.adjoin ℚ S := by
    refine iSup₂_le fun j hj => sup_le (sup_le le_sup_left (le_sup_of_le_right ?_)) (le_sup_of_le_right ?_)
    · exact IntermediateField.adjoin.mono _ _ _ Set.subset_union_left
    · refine IntermediateField.adjoin.mono _ _ _ ?_
      rintro z ⟨i, hz⟩
      exact Or.inr (Set.mem_iUnion₂.2 ⟨j, hj, Set.mem_iUnion.2 ⟨i, hz⟩⟩)
  have : FiniteDimensional ℚ ↥(⨆ j ∈ Set.Icc 1 P.R.m, δ.KPsi j) :=
    Module.Finite.of_injective (IntermediateField.inclusion hle).toLinearMap (IntermediateField.inclusion hle).injective
  have hN : NumberField ↥(⨆ j ∈ Set.Icc 1 P.R.m, δ.KPsi j) := NumberField.mk
  letI := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  refine ⟨hN, fun p hp hd => (Nat.Prime.dvd_mul hp).2 (H p hp (hd.trans ?_))⟩
  exact Int.natAbs_dvd_natAbs.2 (discr_dvd_discr _ _)

end GlobalTheory.Mem.KPsiRam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnramInIffDifferentIdealEqTop
section
set_option autoImplicit false

open NumberField IsDedekindDomain GlobalTheory.NT

namespace GlobalTheory.UnramDiscr

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]

theorem not_dvd_iff_inertia (P : Ideal (𝓞 L)) [P.IsPrime] (hP : P ≠ ⊥) :
    ¬ P ∣ differentIdeal (𝓞 K) (𝓞 L) ↔ P.inertia (L ≃ₐ[K] L) = ⊥ := by
  let _ : Algebra (FractionRing (𝓞 K)) (FractionRing (𝓞 L)) := FractionRing.liftAlgebra _ _
  haveI : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hP
  rw [not_dvd_differentIdeal_iff, ← Ideal.ramificationIdx_eq_one_iff,
    ← Ideal.ramificationIdxIn_eq_ramificationIdx (P.under (𝓞 K)) P (L ≃ₐ[K] L),
    ← Ideal.card_inertia_eq_ramificationIdxIn (G := L ≃ₐ[K] L) (P.under (𝓞 K)) P,
    Subgroup.card_eq_one]

theorem unramIn_iff_differentIdeal_eq_top :
    (∀ 𝔭 : HeightOneSpectrum (𝓞 K), UnramIn L 𝔭) ↔ differentIdeal (𝓞 K) (𝓞 L) = ⊤ := by
  let _ : Algebra (FractionRing (𝓞 K)) (FractionRing (𝓞 L)) := FractionRing.liftAlgebra _ _
  have hD0 : differentIdeal (𝓞 K) (𝓞 L) ≠ ⊥ := differentIdeal_ne_bot
  unfold UnramIn InInertia
  constructor
  · intro h
    by_contra hD
    obtain ⟨M, hM, hDM⟩ := Ideal.exists_le_maximal _ hD
    haveI := hM
    have hMb : M ≠ ⊥ := by
      rintro rfl
      exact hD0 (le_bot_iff.mp hDM)
    have hMu : M.under (𝓞 K) ≠ ⊥ := mt Ideal.eq_bot_of_comap_eq_bot hMb
    have hb : M.inertia (L ≃ₐ[K] L) = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro σ hσ
      exact h ⟨M.under (𝓞 K), inferInstance, hMu⟩ σ ⟨M, inferInstance, ⟨rfl⟩, fun x => hσ x⟩
    exact (not_dvd_iff_inertia K L M hMb).mpr hb (Ideal.dvd_iff_le.mpr hDM)
  · rintro hD 𝔭 σ ⟨P, hP, hPo, hσ⟩
    haveI := hP
    haveI := hPo
    have hPb : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot P
    have hnd : ¬ P ∣ differentIdeal (𝓞 K) (𝓞 L) := by
      rw [hD]
      exact fun hd => hP.ne_top (top_le_iff.mp (Ideal.dvd_iff_le.mp hd))
    have hb := (not_dvd_iff_inertia K L P hPb).mp hnd
    have hmem : σ ∈ P.inertia (L ≃ₐ[K] L) := fun x => hσ x
    rw [hb] at hmem
    exact Subgroup.mem_bot.mp hmem

omit K L in

theorem unramIn_iff_natAbs_discr :
    ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L],
      (∀ 𝔭 : HeightOneSpectrum (𝓞 K), UnramIn L 𝔭) ↔
        (discr L).natAbs = (discr K).natAbs ^ Module.finrank K L := by
  intro K L _ _ _ _ _ _
  rw [unramIn_iff_differentIdeal_eq_top K L,
    natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow K (𝓞 K) L (𝓞 L)]
  have h0 : 0 < (discr K).natAbs ^ Module.finrank K L :=
    pow_pos (Int.natAbs_pos.mpr (discr_ne_zero K)) _
  constructor
  · intro h
    rw [h, Ideal.absNorm_top, one_mul]
  · intro h
    apply Ideal.absNorm_eq_one_iff.mp
    apply Nat.eq_of_mul_eq_mul_right h0
    rw [h, one_mul]

end GlobalTheory.UnramDiscr
end

