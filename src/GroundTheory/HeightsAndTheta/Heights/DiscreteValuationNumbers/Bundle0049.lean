import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpFibreSemilocalCut
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpModel
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0036
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0045
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.WithBotLtNatCastOfAddOneLe
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0024
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.LiftFormNotMemBlowUpOf
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0012
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0009
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0019
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0013
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0006
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0044
import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpLocRingIso
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Abstract

variable {D A : Type*} [CommRing D] [IsDomain D] [CommRing A] [IsDomain A]

theorem exists_ringEquiv_closure_div_of_eq_C_mul_X_pow (θ : A →+* Polynomial D)
    (hθ : Function.Injective θ) {I : Type*} (f g : I → A) (a c : I → D) (n : I → ℕ)
    (hf : ∀ i, θ (f i) = Polynomial.C (a i) * Polynomial.X ^ n i)
    (hg : ∀ i, θ (g i) = Polynomial.C (c i) * Polynomial.X ^ n i)
    (s₁ : Subring (FractionRing A)) (s₂ : Subring (FractionRing D))
    (h₁ : s₁ = Subring.closure (Set.range fun i =>
        algebraMap A (FractionRing A) (f i) / algebraMap A (FractionRing A) (g i)))
    (h₂ : s₂ = Subring.closure (Set.range fun i =>
        algebraMap D (FractionRing D) (a i) / algebraMap D (FractionRing D) (c i))) :
    ∃ φ : s₁ ≃+* s₂, ∀ i (hi : algebraMap A (FractionRing A) (f i) / algebraMap A (FractionRing A) (g i) ∈ s₁),
      (φ ⟨_, hi⟩ : FractionRing D) =
        algebraMap D (FractionRing D) (a i) / algebraMap D (FractionRing D) (c i) := by
  subst h₁ h₂
  let M := FractionRing (Polynomial D)
  have hM : Function.Injective (algebraMap (Polynomial D) M) := IsFractionRing.injective _ M
  let g₁ : A →+* M := (algebraMap (Polynomial D) M).comp θ
  let g₂ : D →+* M := (algebraMap (Polynomial D) M).comp Polynomial.C
  have hg₁ : Function.Injective g₁ := hM.comp hθ
  have hg₂ : Function.Injective g₂ := hM.comp Polynomial.C_injective
  let ι₁ : FractionRing A →+* M := IsFractionRing.lift hg₁
  let ι₂ : FractionRing D →+* M := IsFractionRing.lift hg₂
  have hgen : ∀ i, ι₁ (algebraMap A (FractionRing A) (f i) / algebraMap A (FractionRing A) (g i)) =
      ι₂ (algebraMap D (FractionRing D) (a i) / algebraMap D (FractionRing D) (c i)) := by
    intro i
    rw [map_div₀, map_div₀, IsFractionRing.lift_algebraMap, IsFractionRing.lift_algebraMap,
      IsFractionRing.lift_algebraMap, IsFractionRing.lift_algebraMap]
    have hX : algebraMap (Polynomial D) M (Polynomial.X ^ n i) ≠ 0 := fun h =>
      pow_ne_zero _ Polynomial.X_ne_zero (hM (h.trans (map_zero _).symm))
    simp only [g₁, g₂, RingHom.comp_apply, hf, hg, map_mul]
    exact mul_div_mul_right _ _ hX
  have himg : (Subring.closure (Set.range fun i =>
        algebraMap A (FractionRing A) (f i) / algebraMap A (FractionRing A) (g i))).map ι₁ =
      (Subring.closure (Set.range fun i =>
        algebraMap D (FractionRing D) (a i) / algebraMap D (FractionRing D) (c i))).map ι₂ := by
    rw [RingHom.map_closure, RingHom.map_closure]
    congr 1
    ext z
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨_, ⟨i, rfl⟩, (hgen i).symm⟩
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨_, ⟨i, rfl⟩, hgen i⟩
  refine ⟨(Subring.equivMapOfInjective _ ι₁ ι₁.injective).trans ((RingEquiv.subringCongr himg).trans
    (Subring.equivMapOfInjective _ ι₂ ι₂.injective).symm), fun i hi => ?_⟩
  apply ι₂.injective
  rw [← hgen i, ← Subring.coe_equivMapOfInjective_apply _ ι₂ ι₂.injective, RingEquiv.trans_apply,
    RingEquiv.trans_apply, RingEquiv.apply_symm_apply]
  rfl

end Abstract

variable {K : Type*} [DecidableEq K] {ι : K → Type} {J : Type} {R : Type*} [CommRing R]

theorem aeval_blowUpSubst_of_isMultiHomog (P : Ideal (MRing ι R)) (u : J → MRing ι R)
    {F : MRing (extIdx ι J) R} {b : Option K → ℕ} (hF : IsMultiHomog F b) :
    aeval (blowUpSubst P u) F = Polynomial.C (blowUpEval P u F) * Polynomial.X ^ (b none) := by
  classical
  set w := blockWeight (extIdx ι J)
  set ωT : (Σ o, extIdx ι J o) → ℕ := fun v => Pi.evalAddMonoidHom (fun _ => ℕ) none (w v)
  have hT : ∀ d, Finsupp.weight ωT d = Finsupp.weight w d none := fun d =>
    weight_comp_addMonoidHom_apply w (Pi.evalAddMonoidHom (fun _ => ℕ) none) d
  have hsubst : blowUpSubst P u = fun v =>
      Polynomial.C (Ideal.Quotient.mkₐ R P (blowUpAtOne u v)) * Polynomial.X ^ ωT v := by
    funext v
    obtain ⟨o, i⟩ := v
    cases o <;> simp [blowUpSubst, blowUpAtOne, ωT, w, blockWeight]
  have hFT : IsWeightedHomogeneous ωT F (b none) := by
    intro d hd
    rw [hT]
    exact congrFun (hF hd) none
  set c := aeval (fun v => Ideal.Quotient.mkₐ R P (blowUpAtOne u v)) F
  have key : aeval (blowUpSubst P u) F = Polynomial.C c * Polynomial.X ^ (b none) := by
    refine Polynomial.ext fun n => ?_
    rw [hsubst, coeff_aeval_C_mul_X_pow, Polynomial.coeff_C_mul_X_pow]
    split_ifs with hn
    · rw [hn, hFT.weightedHomogeneousComponent_same]
    · rw [hFT.weightedHomogeneousComponent_ne n hn, map_zero]
  have hσ : blowUpEval P u F = c := by
    show Polynomial.eval 1 (aeval (blowUpSubst P u) F) = c
    rw [key]
    simp
  rw [hσ]
  exact key

theorem BlowUpLocRingIso.proof : BlowUpLocRingIso.Statement.{u} := by
  intro R _ K _ ι J P _ u Q _
  have hB : (blowUpOf P u).IsPrime := RingHom.ker_isPrime _
  let θ : MRing (extIdx ι J) R ⧸ blowUpOf P u →+* Polynomial (MRing ι R ⧸ P) :=
    Ideal.Quotient.lift (blowUpOf P u) (aeval (blowUpSubst P u)).toRingHom
      (fun a ha => RingHom.mem_ker.mp ha)
  have hθ : Function.Injective θ := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [Ideal.Quotient.lift_mk] at ha
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (RingHom.mem_ker.mpr ha)
  let I := {t : (Option K → ℕ) × MRing (extIdx ι J) R × MRing (extIdx ι J) R //
    IsMultiHomog t.2.1 t.1 ∧ IsMultiHomog t.2.2 t.1 ∧ t.2.2 ∉ Q}
  have hf : ∀ i : I, θ (Ideal.Quotient.mk (blowUpOf P u) i.1.2.1) =
      Polynomial.C (blowUpEval P u i.1.2.1) * Polynomial.X ^ (i.1.1 none) := fun i => by
    rw [Ideal.Quotient.lift_mk]
    exact aeval_blowUpSubst_of_isMultiHomog P u i.2.1
  have hg : ∀ i : I, θ (Ideal.Quotient.mk (blowUpOf P u) i.1.2.2) =
      Polynomial.C (blowUpEval P u i.1.2.2) * Polynomial.X ^ (i.1.1 none) := fun i => by
    rw [Ideal.Quotient.lift_mk]
    exact aeval_blowUpSubst_of_isMultiHomog P u i.2.2.1
  have h₁ : homLocRing (blowUpOf P u) Q = Subring.closure (Set.range fun i : I =>
      algebraMap _ (FractionRing (MRing (extIdx ι J) R ⧸ blowUpOf P u)) (Ideal.Quotient.mk (blowUpOf P u) i.1.2.1) /
        algebraMap _ (FractionRing (MRing (extIdx ι J) R ⧸ blowUpOf P u)) (Ideal.Quotient.mk (blowUpOf P u) i.1.2.2)) := by
    rw [homLocRing]
    congr 1
    ext z
    constructor
    · rintro ⟨b, F, G, hF, hG, hGQ, rfl⟩
      exact ⟨⟨(b, F, G), hF, hG, hGQ⟩, rfl⟩
    · rintro ⟨⟨⟨b, F, G⟩, hF, hG, hGQ⟩, rfl⟩
      exact ⟨b, F, G, hF, hG, hGQ, rfl⟩
  have h₂ : blowUpLocRing P u Q = Subring.closure (Set.range fun i : I =>
      algebraMap _ (FractionRing (MRing ι R ⧸ P)) (blowUpEval P u i.1.2.1) /
        algebraMap _ (FractionRing (MRing ι R ⧸ P)) (blowUpEval P u i.1.2.2)) := by
    rw [blowUpLocRing]
    congr 1
    ext z
    constructor
    · rintro ⟨b, F, G, hF, hG, hGQ, rfl⟩
      exact ⟨⟨(b, F, G), hF, hG, hGQ⟩, rfl⟩
    · rintro ⟨⟨⟨b, F, G⟩, hF, hG, hGQ⟩, rfl⟩
      exact ⟨b, F, G, hF, hG, hGQ, rfl⟩
  obtain ⟨φ, hφ⟩ := exists_ringEquiv_closure_div_of_eq_C_mul_X_pow θ hθ
    (fun i : I => Ideal.Quotient.mk (blowUpOf P u) i.1.2.1) (fun i : I => Ideal.Quotient.mk (blowUpOf P u) i.1.2.2)
    (fun i : I => blowUpEval P u i.1.2.1) (fun i : I => blowUpEval P u i.1.2.2) (fun i : I => i.1.1 none)
    hf hg _ _ h₁ h₂
  refine ⟨φ, ?_⟩
  intro b F G hF hG hGQ
  exact hφ ⟨(b, F, G), hF, hG, hGQ⟩ _

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpVerticalFibre
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

section Helpers

theorem mem_map_iff_of_ker_le {A B : Type*} [CommRing A] [CommRing B] {f : A →+* B}
    (hf : Function.Surjective f) {I : Ideal A} (hI : RingHom.ker f ≤ I) (a : A) :
    f a ∈ I.map f ↔ a ∈ I := by
  rw [← Ideal.mem_comap, Ideal.comap_map_of_surjective f hf, ← RingHom.ker_eq_comap_bot,
    sup_eq_left.mpr hI]

theorem contractPrime_specialIdeal {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {ϖ : O} (hϖ : Irreducible ϖ) {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {J : Type}
    (W' : Ideal (MRing (extIdx ι J) O)) (hϖW : (C ϖ : MRing (extIdx ι J) O) ∈ W') :
    (FieldNumbers.contractPrime Function.Embedding.some (specialIdeal W') :
        Ideal (MRing ι (IsLocalRing.ResidueField O))) =
      specialIdeal (W'.comap (liftForm (ι := ι) (J := J) (R := O))) := by
  have hres := IsLocalRing.residue_surjective (R := O)
  have hs : Function.Surjective
      (MvPolynomial.map (IsLocalRing.residue O) : MRing ι O →+* MRing ι (IsLocalRing.ResidueField O)) :=
    MvPolynomial.map_surjective _ hres
  have hker' : RingHom.ker (MvPolynomial.map (IsLocalRing.residue O) :
      MRing (extIdx ι J) O →+* MRing (extIdx ι J) (IsLocalRing.ResidueField O)) ≤ W' := by
    rw [ker_map_residue_eq_span hϖ, Ideal.span_le, Set.singleton_subset_iff]
    exact hϖW
  have hker : RingHom.ker (MvPolynomial.map (IsLocalRing.residue O) :
      MRing ι O →+* MRing ι (IsLocalRing.ResidueField O)) ≤
        W'.comap (liftForm (ι := ι) (J := J) (R := O)) := by
    rw [ker_map_residue_eq_span hϖ, Ideal.span_le, Set.singleton_subset_iff]
    change liftForm (J := J) (C ϖ : MRing ι O) ∈ W'
    rw [liftForm_C]
    exact hϖW
  ext y
  obtain ⟨z, rfl⟩ := hs y
  have e : rename (FieldNumbers.blockIncl Function.Embedding.some (extIdx ι J))
      (MvPolynomial.map (IsLocalRing.residue O) z) =
      MvPolynomial.map (IsLocalRing.residue O) (liftForm (J := J) z) :=
    (map_rename (IsLocalRing.residue O) _ z).symm
  refine Iff.trans ?_ (mem_map_iff_of_ker_le hs hker z).symm
  refine Iff.trans ?_ (mem_map_iff_of_ker_le (MvPolynomial.map_surjective _ hres) hker' (liftForm z))
  exact Iff.of_eq (congrArg (· ∈ specialIdeal W') e)

theorem relDim_eq_of_dim {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]
    (I : Ideal (MRing ι F)) (m : ℕ)
    (h : ringKrullDim (MRing ι F ⧸ I) = ((m + Fintype.card K : ℕ) : WithBot ℕ∞)) :
    FieldNumbers.relDim I = (m : WithBot (WithTop ℤ)) := by
  rw [FieldNumbers.relDim, h]
  have : (((m + Fintype.card K : ℕ) : ℤ) - Fintype.card K) = m := by push_cast; ring
  exact congrArg (fun z : ℤ => ((z : WithTop ℤ) : WithBot (WithTop ℤ))) this

theorem relDim_lt_of_dim_lt {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} {F : Type*}
    [Field F] (I : Ideal (MRing ι F)) (m : ℕ)
    (h : ringKrullDim (MRing ι F ⧸ I) < ((m + Fintype.card K : ℕ) : WithBot ℕ∞)) :
    FieldNumbers.relDim I < (m : WithBot (WithTop ℤ)) := by
  unfold FieldNumbers.relDim
  generalize ringKrullDim (MRing ι F ⧸ I) = x at h ⊢
  induction x using WithBot.recBotCoe with
  | bot => exact WithBot.bot_lt_coe _
  | coe y =>
    induction y using ENat.recTopCoe with
    | top => exact absurd h (by simp)
    | coe e =>
      have he : e < m + Fintype.card K := by exact_mod_cast h
      show (((e : ℤ) - Fintype.card K : ℤ) : WithTop ℤ) < (((m : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ))
      exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr (by omega))

theorem lt_of_two_drops {x y : WithBot ℕ∞} {N : ℕ} (h1 : x + 1 ≤ y)
    (h2 : y + 1 ≤ ((N + 1 : ℕ) : WithBot ℕ∞)) : x < (N : WithBot ℕ∞) := by
  have hy := withBot_lt_natCast_of_add_one_le y (N + 1) h2
  have hx : x + 1 < ((N + 1 : ℕ) : WithBot ℕ∞) := lt_of_le_of_lt h1 hy
  have hx' : x + 1 ≤ (N : WithBot ℕ∞) := by
    induction x using WithBot.recBotCoe with
    | bot => simp
    | coe a =>
      induction a using ENat.recTopCoe with
      | top =>
        exfalso
        have h3 : ((⊤ : ℕ∞) + 1 : ℕ∞) < ((N + 1 : ℕ) : ℕ∞) := by exact_mod_cast hx
        simp at h3
      | coe a =>
        have : a + 1 < N + 1 := by exact_mod_cast hx
        exact_mod_cast (by omega : a + 1 ≤ N)
  exact withBot_lt_natCast_of_add_one_le x N hx'

end Helpers

theorem BlowUpVerticalFibre.proof (hmodel : BlowUpModel.Statement.{u})
    (hdeg : BlowUpFibreDegree.Statement.{u})
    (hpf : FieldNumbers.ProjectionFormulaDegree.Statement.{u}) :
    BlowUpVerticalFibre.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP N u hu hu' c x hx hxP a W hϖW
  classical
  have hB : IsModelOver (blowUpOf P u) n := hmodel O K ι J P n hP N u hu hu'
  have hxB : liftForm (J := J) x ∉ blowUpOf P u := liftForm_not_mem_blowUpOf hxP
  have hxl : IsMultiHomog (liftForm (J := J) x) (liftMDeg c) := isMultiHomog_liftForm hx
  have hl : liftDegs a = fun i => FieldNumbers.pullDeg Function.Embedding.some (a i) := by
    funext i
    exact FlagBundlePullbackVanish.liftDeg_eq_pullDeg (a i)

  have key : ∀ W' : Ideal (MRing (extIdx ι J) O), divCycle (blowUpOf P u) (liftForm x) W' ≠ 0 →
      W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W →
      IsMultiProjPrime (specialIdeal W') ∧ FieldNumbers.relDim (specialIdeal W') = (n : ℕ) ∧
        (FieldNumbers.contractPrime Function.Embedding.some (specialIdeal W') :
          Ideal (MRing ι (IsLocalRing.ResidueField O))) = specialIdeal W := by
    intro W' hW' hcomap
    obtain ⟨hWp, hWrel, -, hWh⟩ := divCycle_ne_zero_facts hB.multiProj.multiHomog hxl hW'
    have hϖ' : (C ϖ : MRing (extIdx ι J) O) ∈ W' := by
      rw [← hcomap, Ideal.mem_comap, liftForm_C] at hϖW
      exact hϖW
    obtain ⟨hsp, -, hrel, -⟩ :=
      SpecialIdealCorresp.proof O ϖ hϖ (Option K) (extIdx ι J) (blowUpOf P u) W' hWp hϖ'
    refine ⟨⟨hsp, SpecialIdealMultiHomog.proof O (Option K) (extIdx ι J) W' hWh, hrel.mp hWrel⟩, ?_, ?_⟩
    · apply relDim_eq_of_dim
      rw [SpecialQuotDim.proof O ϖ hϖ (Option K) (extIdx ι J) W' hϖ',
        ComponentDim.proof O ϖ hϖ (Option K) (extIdx ι J) (blowUpOf P u) n hB (liftMDeg c) _ hxl hxB
          W' hW' hϖ']
    · rw [← hcomap]
      exact contractPrime_specialIdeal hϖ W' hϖ'
  by_cases hW : divCycle P x W ≠ 0
  ·
    have hdimW : FieldNumbers.relDim (specialIdeal W) = (n : ℕ) := by
      apply relDim_eq_of_dim
      rw [SpecialQuotDim.proof O ϖ hϖ K ι W hϖW, ComponentDim.proof O ϖ hϖ K ι P n hP c x hx hxP W hW hϖW]
    have hterm : ∀ W' : Ideal (MRing (extIdx ι J) O),
        (if W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W then
          divCycle (blowUpOf P u) (liftForm x) W' * vNum W' (liftDegs a) else 0) =
        (if W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W then
          divCycle (blowUpOf P u) (liftForm x) W' * (specialRelDeg W' : ℤ) else 0) * vNum W a := by
      intro W'
      split_ifs with h1
      · by_cases h0 : divCycle (blowUpOf P u) (liftForm x) W' = 0
        · simp [h0]
        obtain ⟨hmp, hrd, hcon⟩ := key W' h0 h1
        have hpf' := (hpf (IsLocalRing.ResidueField O) K (Option K) Function.Embedding.some (extIdx ι J)
          (specialIdeal W') hmp n hrd (by rw [hcon]; exact hdimW) a).2
        rw [mul_assoc]
        congr 1
        unfold vNum specialRelDeg
        rw [dif_pos hmp.isPrime, hl, hpf', hcon]
        rfl
      · simp
    rw [finsum_congr hterm, ← finsum_mul, hdeg O ϖ hϖ K ι J P n hP N u hu hu' c x hx hxP W hϖW hW]
  ·
    rw [not_not] at hW
    rw [hW, zero_mul]
    refine finsum_eq_zero_of_forall_eq_zero fun W' => ?_
    split_ifs with h1
    · by_cases h0 : divCycle (blowUpOf P u) (liftForm x) W' = 0
      · rw [h0, zero_mul]
      obtain ⟨hmp, hrd, hcon⟩ := key W' h0 h1
      obtain ⟨hWmin', hWrel'⟩ :
          W' ∈ (blowUpOf P u ⊔ Ideal.span {liftForm x}).minimalPrimes ∧ IsRelevant W' := by
        by_contra hc
        exact h0 (by unfold divCycle; rw [dif_neg hc])
      obtain ⟨hWp, hPW, hWrel, -⟩ := comap_liftForm_facts hWmin'.1.1
        (le_sup_left.trans hWmin'.1.2) hWrel'
      rw [h1] at hWp hPW hWrel
      have hxW : x ∈ W := by
        rw [← h1, Ideal.mem_comap]
        exact hWmin'.1.2 (Ideal.mem_sup_right (Ideal.subset_span rfl))
      have hJW : P ⊔ Ideal.span {x} ≤ W := sup_le hPW ((Ideal.span_singleton_le_iff_mem _).mpr hxW)

      have hnmin : W ∉ (P ⊔ Ideal.span {x}).minimalPrimes := by
        intro hWmin
        refine (show divCycle P x W ≠ 0 from ?_) hW
        unfold divCycle
        rw [dif_pos ⟨hWmin, hWrel⟩]
        have := localizedQuot_nontrivial_of_le (P ⊔ Ideal.span {x}) W hJW
        have h0 : multAt (P ⊔ Ideal.span {x}) W ≠ 0 :=
          (Module.length_pos (R := Localization.AtPrime W)
            (M := LocalizedModule W.primeCompl (MRing ι O ⧸ (P ⊔ Ideal.span {x})))).ne'
        have htop := length_localizedQuot_ne_top _ W hWmin
        exact_mod_cast (ENat.toNat_pos h0 htop).ne'
      obtain ⟨Q, hQ, hQW⟩ := Ideal.exists_minimalPrimes_le hJW
      have hQp : Q.IsPrime := hQ.1.1
      have hQW' : Q < W := lt_of_le_of_ne hQW (fun h => hnmin (h ▸ hQ))
      have hPQ : P < Q := lt_of_le_of_ne (le_sup_left.trans hQ.1.2) (fun h =>
        hxP (h ▸ hQ.1.2 (Ideal.mem_sup_right (Ideal.subset_span rfl))))
      have := hP.multiProj.isPrime
      have hd1 := DimStrictDrop.proof (MRing ι O) Q W hQW'
      have hd2 := DimStrictDrop.proof (MRing ι O) P Q hPQ
      rw [hP.dim, show n + 1 + Fintype.card K = (n + Fintype.card K) + 1 by omega] at hd2
      have hlt := lt_of_two_drops hd1 hd2
      have hltW : FieldNumbers.relDim (specialIdeal W) < ((n : ℕ) : WithBot (WithTop ℤ)) :=
        relDim_lt_of_dim_lt _ _ (by rw [SpecialQuotDim.proof O ϖ hϖ K ι W hϖW]; exact hlt)
      have hz := FieldNumbers.ProjectionFormulaContracted.full (IsLocalRing.ResidueField O) K (Option K)
        Function.Embedding.some (extIdx ι J) (specialIdeal W') hmp n hrd (by rw [hcon]; exact hltW) a
      unfold vNum
      rw [hl, hz, mul_zero]
    · rfl

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDvrConeDimTrdeg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

namespace DvrConeDimTrdeg

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem proof : Statement := by
  intro O _ _ _ K _ _ ι _ P hP hPC
  classical
  let F := FractionRing O
  have hPp : P.IsPrime := hP.isPrime
  have hG : (genFib P).IsPrime := (GenericFibProps.full.{0} O K ι P hP hPC).1
  have hdim : ringKrullDim (MRing ι O ⧸ P) = ringKrullDim (MRing ι F ⧸ genFib P) + 1 :=
    le_antisymm (GenericDimGe.proof.{0} O K ι P hPp hPC) (GenericDimBound.full.{0} O K ι P hP hPC)

  have hB : ringKrullDim (MRing ι F ⧸ genFib P) =
      (Algebra.trdeg F (MRing ι F ⧸ genFib P)).toENat :=
    GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg F

  let M : Submonoid (MRing ι O) := (nonZeroDivisors O).map (C : O →+* MRing ι O)
  have : IsLocalization M (MRing ι F) := MvPolynomial.isLocalization (nonZeroDivisors O) F
  have hdisj : Disjoint (M : Set (MRing ι O)) (P : Set (MRing ι O)) := by
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨a, ha, rfl⟩ hmem
    have : a ∈ P.comap (C : O →+* MRing ι O) := hmem
    rw [hPC] at this
    exact nonZeroDivisors.ne_zero ha ((Submodule.mem_bot _).1 this)
  have hcomap : (genFib P).comap (algebraMap (MRing ι O) (MRing ι F)) = P :=
    IsLocalization.under_map_of_isPrime_disjoint M (MRing ι F) hPp hdisj
  let φ : (MRing ι O ⧸ P) →+* (MRing ι F ⧸ genFib P) :=
    Ideal.quotientMap (genFib P) (algebraMap (MRing ι O) (MRing ι F)) hcomap.ge
  have hφ : Function.Injective φ := Ideal.quotientMap_injective' hcomap.le
  let _ : Algebra (MRing ι O ⧸ P) (MRing ι F ⧸ genFib P) := φ.toAlgebra
  have : IsScalarTower O (MRing ι O ⧸ P) (MRing ι F ⧸ genFib P) :=
    IsScalarTower.of_algebraMap_eq fun a => by
      change _ = φ (Ideal.Quotient.mk P (C a))
      simp [φ, Ideal.quotientMap_mk]
      rfl
  have : FaithfulSMul (MRing ι O ⧸ P) (MRing ι F ⧸ genFib P) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hφ
  have : FaithfulSMul O (MRing ι O ⧸ P) := by
    refine (faithfulSMul_iff_algebraMap_injective _ _).2 ((injective_iff_map_eq_zero (algebraMap O (MRing ι O ⧸ P))).2 fun a ha => ?_)
    have h : (C a : MRing ι O) ∈ P :=
      Ideal.Quotient.eq_zero_iff_mem.1 (show Ideal.Quotient.mk P (C a) = 0 from ha)
    have : a ∈ P.comap (C : O →+* MRing ι O) := h
    rw [hPC] at this
    exact (Submodule.mem_bot _).1 this
  have : FaithfulSMul O F :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (IsFractionRing.injective O F)
  have : FaithfulSMul F (MRing ι F ⧸ genFib P) :=
    (faithfulSMul_iff_algebraMap_injective F (MRing ι F ⧸ genFib P)).2 (algebraMap F _).injective
  have : Algebra.IsAlgebraic O F := IsLocalization.isAlgebraic F (nonZeroDivisors O)
  have : Algebra.IsAlgebraic (MRing ι O ⧸ P) (MRing ι F ⧸ genFib P) := by
    refine ⟨fun b => ?_⟩
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective b
    obtain ⟨⟨s, m⟩, rfl⟩ := IsLocalization.mk'_surjective M g
    have hspec := IsLocalization.mk'_spec (MRing ι F) s m
    let y := algebraMap (MRing ι O ⧸ P) (MRing ι F ⧸ genFib P) (Ideal.Quotient.mk P (m : MRing ι O))
    have hy0 : y ≠ 0 := by
      refine (map_ne_zero_iff _ hφ).2 fun h => ?_
      exact Set.disjoint_left.1 hdisj m.2 (Ideal.Quotient.eq_zero_iff_mem.1 h)
    refine IsAlgebraic.of_mul (mem_nonZeroDivisors_of_ne_zero hy0) (isAlgebraic_algebraMap _) ?_
    have : y * Ideal.Quotient.mk (genFib P) (IsLocalization.mk' (MRing ι F) s m) =
        algebraMap (MRing ι O ⧸ P) (MRing ι F ⧸ genFib P) (Ideal.Quotient.mk P s) := by
      change φ _ * _ = φ _
      simp only [φ, Ideal.quotientMap_mk, ← map_mul]
      rw [mul_comm, hspec]
    rw [this]
    exact isAlgebraic_algebraMap _
  have h1 := trdeg_add_eq O F (A := MRing ι F ⧸ genFib P)
  have h2 := trdeg_add_eq O (MRing ι O ⧸ P) (A := MRing ι F ⧸ genFib P)
  rw [trdeg_eq_zero (R := O) (A := F), zero_add] at h1
  rw [trdeg_eq_zero (R := MRing ι O ⧸ P) (A := MRing ι F ⧸ genFib P), add_zero] at h2
  rw [hdim, hB, h1, ← h2]
  rfl

end DvrConeDimTrdeg

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

