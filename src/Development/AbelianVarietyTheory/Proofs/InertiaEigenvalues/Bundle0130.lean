import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0115
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0027
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0082
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0090
import GroundTheory.LocalFields.UnramifiedNormSurj
import GroundTheory.LocalFields.UnramifiedGalois
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0081
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyMeasAndReps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0119
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0096
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0100
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0103
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0105
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0117
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0118
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0065

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqMulIntegralClosureOfSeparableInvolutionAlgebra
section
noncomputable section

open Polynomial

namespace GlobalTheory.UnitLemma.PrincipalLat

theorem isIntegral_pi' {O : Type} [CommRing O] {ι : Type} [Finite ι] {R : ι → Type}
    [∀ i, CommRing (R i)] [∀ i, Algebra O (R i)] (x : ∀ i, R i) (hx : ∀ i, IsIntegral O (x i)) :
    IsIntegral O x := by
  first
  | exact @_root_.GlobalTheory.IntegralPi.main
  | exact _root_.GlobalTheory.IntegralPi.main
  | (apply _root_.GlobalTheory.IntegralPi.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralPi.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralPi.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralPi.main ..)

section General

variable {O E A : Type} [CommRing O] [IsDomain O] [Field E] [Algebra O E] [IsFractionRing O E]
  [CommRing A] [Algebra E A] [Algebra O A] [IsScalarTower O E A] [Module.Finite E A]

variable (E) in
include E in

theorem exists_mul_isIntegral (y : A) : ∃ c : O, c ≠ 0 ∧ IsIntegral O (algebraMap O A c * y) := by
  have : Algebra.IsAlgebraic O A :=
    (IsFractionRing.comap_isAlgebraic_iff (A := O) (K := E) (C := A)).mpr inferInstance
  obtain ⟨c, hc, h⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := O) y).exists_integral_multiple
  exact ⟨c, hc, by rwa [Algebra.smul_def] at h⟩

end General

section General2

variable {O E A : Type} [CommRing O] [IsDomain O] [Field E] [Algebra O E] [IsFractionRing O E]
  [CommRing A] [Algebra E A] [Algebra O A] [IsScalarTower O E A] [Module.Finite E A]

variable (E) in
include E in

theorem exists_mul_le_integral (J : Submodule O A) (hJ : J.FG) :
    ∃ c : O, c ≠ 0 ∧ ∀ z ∈ J, IsIntegral O (algebraMap O A c * z) := by
  classical
  obtain ⟨s, rfl⟩ := hJ
  choose f hf0 hf using fun y : A => exists_mul_isIntegral (O := O) E y
  refine ⟨∏ y ∈ s, f y, Finset.prod_ne_zero_iff.2 fun y _ => hf0 y, fun z hz => ?_⟩
  induction hz using Submodule.span_induction with
  | mem y hy =>
    rw [← Finset.mul_prod_erase s f hy, map_mul, mul_comm (algebraMap O A (f y)), mul_assoc]
    exact isIntegral_algebraMap.mul (hf y)
  | zero => rw [mul_zero]; exact isIntegral_zero
  | add x y _ _ hx hy => rw [mul_add]; exact hx.add hy
  | smul o x _ hx => rw [mul_smul_comm]; exact hx.smul o

theorem eq_mulLat_of_isPrincipalIdealRing [IsPrincipalIdealRing (integralClosure O A)]
    (J : Submodule O A) (hJ : IsLat O E J) (hst : ∀ a ∈ integralClosure O A, ∀ y ∈ J, a * y ∈ J) :
    ∃ a : Aˣ, J = mulLat O (a : A) (Subalgebra.toSubmodule (integralClosure O A)) := by
  classical
  obtain ⟨c, hc0, hc⟩ := exists_mul_le_integral E J hJ.1
  set Λ := integralClosure O A

  have hcu : IsUnit (algebraMap O A c) := by
    rw [IsScalarTower.algebraMap_apply O E A]
    refine (IsUnit.mk0 _ ?_).map _
    exact (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hc0))
  set C := algebraMap O A c
  let I : Ideal Λ :=
    { carrier := {l | ∃ z ∈ J, (l : A) = C * z}
      add_mem' := by
        rintro a b ⟨x, hx, hax⟩ ⟨y, hy, hby⟩
        exact ⟨x + y, J.add_mem hx hy, by rw [Subalgebra.coe_add, hax, hby, mul_add]⟩
      zero_mem' := ⟨0, J.zero_mem, by simp⟩
      smul_mem' := by
        rintro a b ⟨x, hx, hbx⟩
        refine ⟨(a : A) * x, hst _ a.2 _ hx, ?_⟩
        rw [smul_eq_mul, Subalgebra.coe_mul, hbx]; ring }
  obtain ⟨b, hb⟩ := (IsPrincipalIdealRing.principal I).principal
  have hmemI : ∀ l : Λ, l ∈ I ↔ ∃ m : Λ, m * b = l := by
    intro l; rw [hb]; exact Ideal.mem_span_singleton'
  have key : ∀ z, z ∈ J ↔ ∃ l ∈ Λ, C * z = b * l := by
    intro z; constructor
    · intro hz
      obtain ⟨m, hm⟩ := (hmemI ⟨C * z, hc z hz⟩).1 ⟨z, hz, rfl⟩
      have h2 := congrArg Subtype.val hm
      simp only [Subalgebra.coe_mul] at h2
      exact ⟨m, m.2, by rw [← h2, mul_comm]⟩
    · rintro ⟨l, hl, hzl⟩
      obtain ⟨z0, hz0, hbz0⟩ : b ∈ I := by rw [hb]; exact Ideal.mem_span_singleton_self b
      have : C * z = C * (l * z0) := by rw [hzl, hbz0]; ring
      rw [hcu.mul_left_cancel this]
      exact hst l hl z0 hz0

  have hbu : IsUnit (b : A) := by
    have hle : (J : Set A) ⊆ LinearMap.range (LinearMap.mulLeft E (b : A)) := by
      intro z hz
      obtain ⟨l, _, hzl⟩ := (key z).1 hz
      refine ⟨hcu.unit⁻¹ * l, ?_⟩
      simp only [LinearMap.mulLeft_apply]
      calc (b : A) * (↑hcu.unit⁻¹ * l) = ↑hcu.unit⁻¹ * (b * l) := by ring
        _ = z := by rw [← hzl, ← mul_assoc, IsUnit.val_inv_mul, one_mul]
    have h1 : (1 : A) ∈ LinearMap.range (LinearMap.mulLeft E (b : A)) := by
      have := Submodule.span_le.2 hle
      rw [hJ.2] at this
      exact this Submodule.mem_top
    obtain ⟨w, hw⟩ := h1
    exact isUnit_iff_exists_inv.2 ⟨w, by simpa using hw⟩
  refine ⟨hcu.unit⁻¹ * hbu.unit, ?_⟩
  ext z
  rw [key z]
  simp only [mulLat, Submodule.mem_map, LinearMap.mulLeft_apply, Subalgebra.mem_toSubmodule,
    Units.val_mul, IsUnit.unit_spec]
  constructor
  · rintro ⟨l, hl, hzl⟩
    refine ⟨l, hl, ?_⟩
    rw [mul_assoc, ← hzl, ← mul_assoc, IsUnit.val_inv_mul, one_mul]
  · rintro ⟨l, hl, hzl⟩
    refine ⟨l, hl, ?_⟩
    rw [← hzl, ← mul_assoc, ← mul_assoc, IsUnit.mul_val_inv, one_mul]

end General2

theorem isPrincipalIdealRing_integralClosure {O E A : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Field E]
    [Algebra O E] [IsFractionRing O E] [CommRing A] [Algebra E A] [Algebra O A]
    [IsScalarTower O E A] [Module.Finite E A] [IsReduced A] :
    IsPrincipalIdealRing (integralClosure O A) := by
  classical
  haveI : IsArtinianRing A := IsArtinianRing.of_finite E A
  let ψ : A ≃ₐ[O] (∀ I : MaximalSpectrum A, A ⧸ I.asIdeal) :=
    (IsArtinianRing.equivPi A).restrictScalars O
  haveI hpir : ∀ I : MaximalSpectrum A, IsPrincipalIdealRing (integralClosure O (A ⧸ I.asIdeal)) := by
    intro I
    haveI := I.isMaximal
    letI : Field (A ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal
    haveI : FiniteDimensional E (A ⧸ I.asIdeal) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ E I.asIdeal).toLinearMap
        Ideal.Quotient.mk_surjective
    haveI := GlobalTheory.FormalIsogeny.isDiscreteValuationRing_integralClosure O E (A ⧸ I.asIdeal)
    infer_instance
  haveI : Finite (MaximalSpectrum A) := inferInstance
  let G : (∀ I : MaximalSpectrum A, integralClosure O (A ⧸ I.asIdeal)) →ₐ[O]
      (∀ I : MaximalSpectrum A, A ⧸ I.asIdeal) :=
    Pi.algHom O _ fun I => (integralClosure O (A ⧸ I.asIdeal)).val.comp (Pi.evalAlgHom O _ I)
  let F := (ψ.symm.toAlgHom.comp G).codRestrict (integralClosure O A) fun l =>
    (isIntegral_pi' (G l) fun I => (l I).2).map ψ.symm
  refine IsPrincipalIdealRing.of_surjective F ?_
  intro x
  refine ⟨fun I => ⟨ψ x I, x.2.map ((Pi.evalAlgHom O _ I).comp ψ.toAlgHom)⟩, ?_⟩
  apply Subtype.ext
  change ψ.symm (G _) = (x : A)
  have : G (fun I => ⟨ψ x I, x.2.map ((Pi.evalAlgHom O _ I).comp ψ.toAlgHom)⟩) = ψ x := rfl
  rw [this, AlgEquiv.symm_apply_apply]

theorem eq_mulLat_integralClosure : ∀ (K : UQ) (B : InvAlg K), B.P.Separable →
    ∀ J : Submodule K.O B.A, IsLat K.O K.E J → (∀ a ∈ integralClosure K.O B.A, ∀ y ∈ J, a * y ∈ J) →
    ∃ a : B.Aˣ, J = mulLat K.O (a : B.A) (Subalgebra.toSubmodule (integralClosure K.O B.A)) := by
  intro K B hsep J hJ hst
  haveI : IsReduced B.A := ⟨fun a ha => Centraliser.eq_zero_of_isNilpotent B hsep a ha⟩
  haveI := isPrincipalIdealRing_integralClosure (O := K.O) (E := K.E) (A := B.A)
  exact eq_mulLat_of_isPrincipalIdealRing J hJ hst

end GlobalTheory.UnitLemma.PrincipalLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaKEqNegOneOfNotNorm
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.NonNorm

open ValuativeRel GroundTheory.LocalField IntermediateField

theorem not_two_dvd_ord_norm (F K L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Field K] [Algebra F K] [FiniteDimensional F K]
    [Field L] [Algebra K L] (h2 : Module.finrank K L = 2) (ζ : L)
    (hζ : IsPrimitiveRoot ζ (Nat.card 𝓀[F] ^ 2 - 1)) (htop : K⟮ζ⟯ = ⊤) (s : K) (hs0 : s ≠ 0)
    (hs : ¬ ∃ y : L, Algebra.norm K y = s) : ¬ (2 : ℤ) ∣ ord (Algebra.norm F s) := by
  haveI : FiniteDimensional K L := Module.finite_of_finrank_pos (by omega)
  obtain ⟨vK, tK, hK, eK⟩ := exists_isNonarchimedeanLocalField_valuativeExtension F K
  obtain ⟨vL, tL, hL, eL⟩ := exists_isNonarchimedeanLocalField_valuativeExtension K L
  have hm : ((Nat.card 𝓀[F] ^ 2 - 1 : ℕ) : 𝓀[K]) ≠ 0 :=
    natCast_residueField_ne_zero K (natCast_card_pow_sub_one_ne_zero (K := F) two_ne_zero)
  haveI : IsUnramified K L := ⟨ramificationIndex_eq_one_of_adjoin_eq_top hζ hm htop⟩
  have hodd : ¬ (2 : ℤ) ∣ ord s := by
    intro hd
    have h := (mem_range_normUnits_iff (K := K) (L := L) (Units.mk0 s hs0)).2 (by rw [h2]; exact hd)
    obtain ⟨y, hy⟩ := h
    exact hs ⟨y, congrArg Units.val hy⟩
  have hf : ¬ 2 ∣ residueDegree F K := by
    rintro ⟨j, hj⟩
    have hcard : Nat.card 𝓀[K] = Nat.card 𝓀[F] ^ residueDegree F K := by
      rw [residueDegree_eq_finrank]
      exact Module.natCard_eq_pow_finrank
    obtain ⟨z, hz⟩ := exists_isPrimitiveRoot_card_residueField_sub_one (L := K)
    have hz1 : IsPrimitiveRoot (z : K) (Nat.card 𝓀[K] - 1) :=
      hz.map_of_injective (f := (𝒪[K]).subtype) Subtype.val_injective
    have hz2 : IsPrimitiveRoot (algebraMap K L z) (Nat.card 𝓀[K] - 1) :=
      hz1.map_of_injective (algebraMap K L).injective
    haveI : NeZero (Nat.card 𝓀[K] - 1) := ⟨by have := one_lt_card_residueField K; omega⟩
    have hdvd : Nat.card 𝓀[F] ^ 2 - 1 ∣ Nat.card 𝓀[K] - 1 := by
      rw [hcard, hj, pow_mul]
      exact Nat.sub_one_dvd_pow_sub_one _ _
    obtain ⟨i, -, hi⟩ := hz2.eq_pow_of_pow_eq_one ((hζ.pow_eq_one_iff_dvd _).2 hdvd)
    have hbot : K⟮ζ⟯ = ⊥ := by
      rw [adjoin_simple_eq_bot_iff, ← hi, ← map_pow]
      exact IntermediateField.algebraMap_mem _ _
    have h1 : Module.finrank K L = 1 := by
      rw [← finrank_top', ← htop, hbot, IntermediateField.finrank_bot]
    omega
  rw [ord_norm]
  intro hd
  rcases (Int.prime_two.dvd_or_dvd hd) with h | h
  · exact hf (by exact_mod_cast h)
  · exact hodd h

@[reducible] noncomputable def normRel (F : Type) [NormedField F] [IsUltrametricDist F] : ValuativeRel F :=
  ValuativeRel.ofValuation (NormedField.valuation (K := F))

theorem isLocalField (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [LocallyCompactSpace F] :
    letI := normRel F
    IsNonarchimedeanLocalField F := by
  letI := normRel F
  have hc : (NormedField.valuation (K := F)).Compatible := Valuation.Compatible.ofValuation _
  refine { toIsValuativeTopology := ?_, toLocallyCompactSpace := inferInstance, toIsNontrivial := ?_ }
  · exact IsValuativeTopology.of_mem_nhds_zero_iff_vle (NormedField.valuation (K := F))
      (fun {s} => (NormedField.toValued (K := F)).is_topological_valuation s)
  · rw [isNontrivial_iff_isNontrivial (NormedField.valuation (K := F))]
    infer_instance

theorem ord_eq_of_norm_eq (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [LocallyCompactSpace F]
    (x y : F) (h : ‖x‖ = ‖y‖) :
    letI := normRel F
    haveI := isLocalField F
    ord x = ord y := by
  letI := normRel F
  haveI := isLocalField F
  have h1 : x ≤ᵥ y := h.le
  have h2 : y ≤ᵥ x := h.ge
  rw [(valuation F).vle_iff_le] at h1 h2
  unfold ord
  rw [normalizedValuation_eq_iff.2 (le_antisymm h1 h2)]

theorem etaK_eq_neg_one : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), IsField A.K → IsField A.L → ∀ s : A.Kˣ, (¬ ∃ y : A.L, A.NL y = s) → A.etaK s = -1 := by
  intro F E _ _ _ _ hU A hK hL s hs
  haveI := hU.ultraF
  haveI := hU.ultraE
  haveI := hU.lcF
  haveI := hU.lcE
  letI := normRel F
  letI := normRel E
  haveI := isLocalField F
  haveI := isLocalField E
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hU.finrank_eq]; norm_num)
  haveI : ValuativeExtension F E := ⟨fun a b => by
    change ‖algebraMap F E a‖ ≤ ‖algebraMap F E b‖ ↔ ‖a‖ ≤ ‖b‖
    rw [norm_algebraMap', norm_algebraMap']⟩
  have he : ramificationIndex F E = 1 := by
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[E]
    obtain ⟨x, hx⟩ := hU.unram (π : E)
    have h1 := ord_eq_of_norm_eq E (π : E) (algebraMap F E x) (by rw [norm_algebraMap', hx])
    rw [ord_uniformizer hπ, ord_algebraMap] at h1
    have h2 : (ramificationIndex F E : ℤ) ∣ 1 := ⟨_, h1⟩
    exact Nat.dvd_one.1 (by exact_mod_cast h2)
  obtain ⟨ζ, hζ, htop⟩ := exists_isPrimitiveRoot_adjoin_eq_top_of_unramified F E he
  have hcard : Nat.card 𝓀[E] = Nat.card 𝓀[F] ^ 2 := by
    rw [← hU.finrank_eq, ← residueDegree_eq_finrank_of_unramified F E he, residueDegree_eq_finrank]
    exact Module.natCard_eq_pow_finrank
  rw [hcard] at hζ
  obtain ⟨⟨b⟩, -⟩ := Et.quadratic_structure F E A
  letI : Field A.K := hK.toField
  letI : Field A.L := hL.toField
  have h2 : Module.finrank A.K A.L = 2 := by simpa using Module.finrank_eq_card_basis b
  have hζ' : IsPrimitiveRoot (algebraMap E A.L ζ) (Nat.card 𝓀[F] ^ 2 - 1) :=
    hζ.map_of_injective (algebraMap E A.L).injective
  have hE : ∀ e : E, algebraMap E A.L e ∈ A.K⟮algebraMap E A.L ζ⟯ := by
    intro e
    have he' : e ∈ F⟮ζ⟯ := by rw [htop]; trivial
    induction he' using IntermediateField.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff.1 hx]
      exact mem_adjoin_simple_self _ _
    | algebraMap x =>
      rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply F A.K A.L]
      exact IntermediateField.algebraMap_mem _ _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | inv x _ hx => rw [map_inv₀]; exact inv_mem hx
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  have htop' : A.K⟮algebraMap E A.L ζ⟯ = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have hbc := A.push.symm.out
    induction y using hbc.inductionOn with
    | zero => exact zero_mem _
    | tmul e => exact hE e
    | smul k y hy => exact IntermediateField.smul_mem _ (hy trivial)
    | add y z hy hz => exact add_mem (hy trivial) (hz trivial)
  have hodd := not_two_dvd_ord_norm F A.K A.L h2 _ hζ' htop' s s.ne_zero hs
  unfold Et.etaK eta
  rw [if_neg]
  rintro ⟨y, hy⟩
  apply hodd
  have hy0 : y ≠ 0 := by
    rintro rfl
    have h0 : Algebra.norm F (s : A.K) = 0 := norm_eq_zero.1 (by simpa using hy)
    exact s.ne_zero (Algebra.norm_eq_zero_iff.1 h0)
  have h3 := ord_eq_of_norm_eq F (Algebra.norm F (s : A.K)) (y ^ 2) (by rw [norm_pow, hy])
  rw [ord_pow hy0] at h3
  exact ⟨ord y, by exact_mod_cast h3⟩

end GlobalTheory.JR.NonNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleHermitianPairStructureFacts
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

namespace GlobalTheory.JR.EtFacts

theorem normE [U : Unram F E] (z : E) : algebraMap F E (Algebra.norm F z) = z * star z := by
  have := U.charZero
  obtain ⟨b, d, hb0, hs, hd, hd0⟩ := Unram.exists_basis_antifixed F E
  have h2 := (IsUnit.mk0 (2 : F) two_ne_zero)
  exact (quadratic_star_structure b d hb0 hs hd U.star_fix (IsUnit.mk0 d hd0) h2).2.1 z

theorem free_L_E [Unram F E] (A : Et F E) : Module.Free E A.L := by
  have hbc := A.push.out
  exact Module.Free.of_basis (hbc.basis (Module.Free.chooseBasis F A.K))

theorem free_L_K [Unram F E] (A : Et F E) : Module.Free A.K A.L := by
  obtain ⟨⟨b⟩, -⟩ := GlobalTheory.JR.Et.quadratic_structure F E A
  exact Module.Free.of_basis b

theorem eta_NL [U : Unram F E] (A : Et F E) (y : A.L) : A.etaK (A.NL y) = 1 := by
  have := free_L_E A
  have := free_L_K A
  have h1 : Algebra.norm F (A.NL y) = Algebra.norm F (Algebra.norm E y) := by
    rw [Et.NL, Algebra.norm_norm, Algebra.norm_norm]
  rw [Et.etaK, h1, eta]
  obtain ⟨x, hx⟩ := U.unram (Algebra.norm E y)
  have hx2 : ‖Algebra.norm F (Algebra.norm E y)‖ = ‖x‖ ^ 2 := by
    rw [← norm_algebraMap' E, normE, norm_mul, U.norm_star, hx, sq]
  rw [if_pos ⟨x, hx2⟩]

theorem eta_neg_one [Unram F E] (A : Et F E) : A.etaK (-1) = 1 := by
  rw [Et.etaK, eta]
  refine if_pos ⟨1, ?_⟩
  have h : Algebra.norm F (-1 : A.K) * Algebra.norm F (-1 : A.K) = 1 := by
    rw [← map_mul]; simp
  have h' := congrArg norm h
  rw [norm_mul, norm_one] at h'
  have h0 : 0 ≤ ‖Algebra.norm F (-1 : A.K)‖ := norm_nonneg _
  simp only [norm_one, one_pow]
  nlinarith

end GlobalTheory.JR.EtFacts

namespace GlobalTheory.JR.EtFacts

theorem sq_le_range [Unram F E] (A : Et F E) :
    (powMonoidHom 2 : A.Kˣ →* A.Kˣ).range ≤ (EtMeas.normU A).range := by
  obtain ⟨-, hinj, hN, -, -⟩ := GlobalTheory.JR.Et.quadratic_structure F E A
  rintro _ ⟨k, rfl⟩
  refine ⟨Units.map (algebraMap A.K A.L).toMonoidHom k, Units.ext (hinj ?_)⟩
  rw [EtMeas.normU_val, hN]
  simp [A.star_K, sq]

theorem finite_quot [Unram F E] (A : Et F E) (hsq : Finite (A.Kˣ ⧸ (powMonoidHom 2 : A.Kˣ →* A.Kˣ).range)) :
    Finite (A.Kˣ ⧸ (EtMeas.normU A).range) := by
  have : (powMonoidHom 2 : A.Kˣ →* A.Kˣ).range.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have := Subgroup.finiteIndex_of_le (sq_le_range A)
  exact Subgroup.finite_quotient_of_finiteIndex

theorem key_rel (A : Et F E) (a x : A.Kˣ) : (∃ y : A.L, IsUnit y ∧ (a : A.K) = x * A.NL y) ↔
    (QuotientGroup.mk x : A.Kˣ ⧸ (EtMeas.normU A).range) = QuotientGroup.mk a := by
  rw [QuotientGroup.eq]
  constructor
  · rintro ⟨y, hy, h⟩
    refine ⟨hy.unit, Units.ext ?_⟩
    simp [h, Et.NL, EtMeas.normU]
  · rintro ⟨y, h⟩
    refine ⟨y, y.isUnit, ?_⟩
    have := congrArg Units.val h
    simp only [EtMeas.normU, Units.coe_map, Units.val_mul] at this
    rw [Et.NL, this]; simp

theorem finite_reps_exists [Unram F E] (A : Et F E) (hf : Finite (A.Kˣ ⧸ (EtMeas.normU A).range)) :
    ∃ S : Set A.Kˣ, S.Finite ∧ A.IsReps S := by
  refine ⟨Set.range (Quotient.out : A.Kˣ ⧸ (EtMeas.normU A).range → A.Kˣ), Set.finite_range _, fun a =>
    ⟨Quotient.out (QuotientGroup.mk a : A.Kˣ ⧸ (EtMeas.normU A).range),
    ⟨⟨_, rfl⟩, (key_rel A _ _).2 (QuotientGroup.out_eq' _)⟩, ?_⟩⟩
  rintro _ ⟨⟨q, rfl⟩, h⟩
  rw [← (key_rel A _ _).1 h, QuotientGroup.out_eq']

theorem finite_of_reps [Unram F E] (A : Et F E) (hf : Finite (A.Kˣ ⧸ (EtMeas.normU A).range)) (S : Set A.Kˣ)
    (hS : A.IsReps S) : S.Finite := by
  have hinj : Function.Injective (fun x : S => (QuotientGroup.mk (x : A.Kˣ) : A.Kˣ ⧸ (EtMeas.normU A).range)) := by
    rintro ⟨x, hx⟩ ⟨x', hx'⟩ h
    obtain ⟨z, -, hz⟩ := hS x'
    have e1 := hz x ⟨hx, (key_rel A _ _).2 h⟩
    have e2 := hz x' ⟨hx', (key_rel A _ _).2 rfl⟩
    exact Subtype.ext (e1.trans e2.symm)
  exact Set.finite_coe_iff.1 (Finite.of_injective _ hinj)

end GlobalTheory.JR.EtFacts

namespace GlobalTheory.JR.EtFacts

theorem nonunits_null [U : Unram F E] (A : Et F E) (μ : Measure A.K) (hμ : μ.IsAddHaarMeasure) :
    μ {t | ¬ IsUnit t} = 0 := by
  have := U.lcF
  have : IsArtinianRing A.K := IsArtinianRing.of_finite F A.K
  have hfin := IsArtinianRing.setOfPred_isMaximal_finite A.K
  have hsub : {t : A.K | ¬ IsUnit t} ⊆ ⋃ m ∈ {I : Ideal A.K | I.IsMaximal}, (m : Set A.K) := by
    intro t ht
    obtain ⟨m, hm, htm⟩ := exists_max_ideal_of_mem_nonunits (show t ∈ nonunits A.K from ht)
    exact Set.mem_biUnion hm htm
  refine measure_mono_null hsub ((measure_biUnion_null_iff hfin.countable).2 fun m hm => ?_)
  have h := GlobalTheory.T.addHaar_proper_submodule_eq_zero_moduleTopology F A.K μ hμ (m.restrictScalars F) (fun h => hm.ne_top ?_)
  · exact h
  · rw [Ideal.eq_top_iff_one]
    have : (1 : A.K) ∈ m.restrictScalars F := h ▸ Submodule.mem_top
    exact this

theorem main : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), (∀ y : A.L, algebraMap A.K A.L (A.NL y) = y * star y) ∧ (∀ y : A.L, algebraMap A.K A.L (Algebra.trace A.K A.L y) = y + star y) ∧ (Algebra.traceForm F A.K).Nondegenerate ∧ (∀ y : A.L, IsUnit y → A.etaK (A.NL y) = 1) ∧ A.etaK (-1) = 1 ∧ (∀ᶠ v in 𝓝 (1 : A.K), ∃ s : A.K, s ^ 2 = v) ∧ (∃ S : Set A.Kˣ, S.Finite ∧ A.IsReps S) ∧ (∀ S : Set A.Kˣ, A.IsReps S → S.Finite) ∧ (∀ μ : Measure A.K, μ.IsAddHaarMeasure → μ {t | ¬ IsUnit t} = 0) ∧ IsOpen A.OK ∧ IsCompact A.OK ∧ ∃ R : Subring A.K, (R : Set A.K) = A.OK := by
  intro F E _ _ _ _ U A
  have := U.charZero; have := U.lcF
  have : ProperSpace F := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  obtain ⟨-, -, hN, htr, -⟩ := GlobalTheory.JR.Et.quadratic_structure F E A
  have hq := finite_quot A (GlobalTheory.T.finite_units_quot_sq_finiteEtaleHermitianPair F E A)
  refine ⟨hN, htr, ⟨fun x hx => ?_, fun x hx => ?_⟩, fun y _ => eta_NL A y, eta_neg_one A,
    (GlobalTheory.isOpenUnits_and_eventually_sq F A.K).2, finite_reps_exists A hq, finite_of_reps A hq,
    nonunits_null A, GlobalTheory.T.isOpen_finiteEtaleHermitianPair_OK F E A, GlobalTheory.T.isCompact_finiteEtaleHermitianPair_OK F E A, GlobalTheory.T.exists_subring_eq_OK F E A⟩
  · exact EtMeas.eq_zero_of_trace F A.K x fun y => by simpa using hx y
  · exact EtMeas.eq_zero_of_trace F A.K x fun y => by simpa [mul_comm] using hx y

end GlobalTheory.JR.EtFacts
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinsetFixingSubsetOpenInertiaSubgroupStatement
section
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_fixing_subset_open_inertia_subgroup : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (M : Subgroup (Ine (F := E) A)), IsOpen (M : Set (Ine (F := E) A)) → ∃ s : Finset Ω, ∀ σ : Ine (F := E) A, (∀ x ∈ s, (σ : G E Ω) x = x) → σ ∈ M := by
  first | exact @GlobalTheory.WeilDeligne.exists_finset_fix_subset_of_isOpen | exact GlobalTheory.WeilDeligne.exists_finset_fix_subset_of_isOpen | (intros; apply GlobalTheory.WeilDeligne.exists_finset_fix_subset_of_isOpen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFixingActsAsFrobeniusPowerResidueStatement
section
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fixing_actsAsFrobeniusPowerResidue : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (_h : IsPlaceOver A w)
    (K : IntermediateField E Ω) [FiniteDimensional E K], ∀ d ∈ Dec (F := E) A, ∀ j : ℕ,
      (∀ z ∈ K, A.valuation z ≤ 1 → A.valuation (d z - z ^ (normV w ^ j)) < 1) →
      ∃ ρ : G E Ω, (∀ z ∈ K, ρ z = z) ∧ ActsAs A (normV w) (d * ρ) j 0 := by
  first | exact @GlobalTheory.GaloisLift.exists_fixing_actsAs | exact GlobalTheory.GaloisLift.exists_fixing_actsAs | (intros; apply GlobalTheory.GaloisLift.exists_fixing_actsAs <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegerMapIsIntegralUnramifiedInvolutionExStatement
section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integerMap_isIntegral_unramifiedInvolutionExt : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∃ φO : K.O →+* K'.O, (∀ x, algebraMap K'.O K'.E (φO x) = φ (algebraMap K.O K.E x)) ∧ @Algebra.IsIntegral K.O K'.O _ _ φO.toAlgebra := by
  first | exact @GlobalTheory.UnitLemma.Unr.intMap_isIntegral_of_unr | exact GlobalTheory.UnitLemma.Unr.intMap_isIntegral_of_unr | (intros; apply GlobalTheory.UnitLemma.Unr.intMap_isIntegral_of_unr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsotropicIdempotentCentralizerHermitianStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isotropic_idempotent_centralizer_hermitian : ∀ (E : Type) [Field E] [StarRing E] (r : ℕ) (A₀ : Matrix (Fin r) (Fin r) E), A₀.IsHermitian → A₀.charpoly.Separable → ∃ f : Matrix (Fin r) (Fin r) E, f * A₀ = A₀ * f ∧ f * f = f ∧ f * star f = 0 ∧ ∀ y : Matrix (Fin r) (Fin r) E, y * A₀ = A₀ * y → y * (1 - f - star f) * star (y * (1 - f - star f)) = 0 → y * (1 - f - star f) = 0 := by
  first | exact @GlobalTheory.IsoIdem.isoIdem | exact GlobalTheory.IsoIdem.isoIdem | (intros; apply GlobalTheory.IsoIdem.isoIdem <;> assumption)
end

