import Mathlib
import Formalism.SatakeDualWeyl.Statement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0081
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0130
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0253
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0299
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0317

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryMulIntegralOfNormMaximalOrderUnit
section
noncomputable section

open Polynomial Matrix GlobalTheory.LatOrb

namespace GlobalTheory.UnitAdj

theorem isIntegral_or_isIntegral_inv {O K L : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Field K]
    [Algebra O K] [IsFractionRing O K] [Field L] [Algebra K L] [Algebra O L]
    [IsScalarTower O K L] [FiniteDimensional K L] (y : L) :
    IsIntegral O y ∨ IsIntegral O y⁻¹ := by
  haveI := GlobalTheory.FormalIsogeny.isDiscreteValuationRing_integralClosure O K L
  haveI := integralClosure.isFractionRing_of_finite_extension (A := O) K L
  rcases ValuationRing.isInteger_or_isInteger (integralClosure O L) y with ⟨z, hz⟩ | ⟨z, hz⟩
  · left; rw [← hz]; exact z.2
  · right; rw [← hz]; exact z.2

theorem isIntegral_of_mul_self_eq {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {e : A}
    (he : e * e = e) : IsIntegral O e := by
  refine ⟨X ^ 2 - X, monic_X_pow_sub (degree_X_le.trans_lt (by norm_num)), ?_⟩
  simp [eval₂_sub, pow_two, he]

section Residues

variable {A : Type} [CommRing A] [IsArtinianRing A] [IsReduced A]

theorem eq_zero_of_forall_mem {y : A} (h : ∀ I : MaximalSpectrum A, y ∈ I.asIdeal) : y = 0 := by
  apply (IsArtinianRing.equivPi A).injective
  rw [map_zero]
  funext I
  rw [IsArtinianRing.equivPi_apply]
  exact Ideal.Quotient.eq_zero_iff_mem.2 (h I)

theorem isIntegral_of_residues {O : Type} [CommRing O] [Algebra O A] {y : A}
    (h : ∀ I : MaximalSpectrum A, IsIntegral O (Ideal.Quotient.mk I.asIdeal y)) :
    IsIntegral O y := by
  let ψ : A ≃ₐ[O] (∀ I : MaximalSpectrum A, A ⧸ I.asIdeal) :=
    (IsArtinianRing.equivPi A).restrictScalars O
  refine (isIntegral_algHom_iff ψ.toAlgHom ψ.injective).1 ?_
  refine GlobalTheory.UnitLemma.PrincipalLat.isIntegral_pi' _ fun I => ?_
  have : ψ.toAlgHom y I = Ideal.Quotient.mk I.asIdeal y := IsArtinianRing.equivPi_apply A y I
  rw [this]
  exact h I

theorem exists_residues_indicator (P : MaximalSpectrum A → Prop) :
    ∃ e : A, ∀ I : MaximalSpectrum A, (P I → e - 1 ∈ I.asIdeal) ∧ (¬ P I → e ∈ I.asIdeal) := by
  classical
  let v : ∀ I : MaximalSpectrum A, A ⧸ I.asIdeal := fun I => if P I then 1 else 0
  refine ⟨(IsArtinianRing.equivPi A).symm v, fun I => ⟨fun hP => ?_, fun hP => ?_⟩⟩
  · have h1 := congrFun ((IsArtinianRing.equivPi A).apply_symm_apply v) I
    rw [IsArtinianRing.equivPi_apply] at h1
    rw [← Ideal.Quotient.eq, h1, map_one]
    simp [v, hP]
  · have h1 := congrFun ((IsArtinianRing.equivPi A).apply_symm_apply v) I
    rw [IsArtinianRing.equivPi_apply] at h1
    rw [← Ideal.Quotient.eq_zero_iff_mem, h1]
    simp [v, hP]

end Residues

theorem exists_unitary_mul_integral : ∀ {O K A : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Field K] [Algebra O K] [IsFractionRing O K]
    [CommRing A] [Algebra K A] [Algebra O A] [IsScalarTower O K A] [Module.Finite K A] [IsReduced A]
    (σ : K →+* K), (∀ a : O, ∃ b : O, σ (algebraMap O K a) = algebraMap O K b) →
    ∀ τ : A →+* A, (∀ a, τ (τ a) = a) → (∀ k, τ (algebraMap K A k) = algebraMap K A (σ k)) →
    ∀ x : Aˣ, IsIntegral O (τ (x : A) * x) → IsIntegral O (τ ((x⁻¹ : Aˣ) : A) * ((x⁻¹ : Aˣ) : A)) →
    ∃ t : Aˣ, τ (t : A) * t = 1 ∧ IsIntegral O ((t : A) * ((x⁻¹ : Aˣ) : A)) ∧
      IsIntegral O (((t⁻¹ : Aˣ) : A) * (x : A)) := by
  intro O K A _ _ _ _ _ _ _ _ _ _ _ _ _ σ hσ τ hτ hτσ x hc hci
  haveI : IsArtinianRing A := IsArtinianRing.of_finite K A

  have hinj := IsFractionRing.injective O K
  choose s hs using hσ
  let σO : O →+* O :=
    { toFun := s
      map_one' := hinj (by simp [← hs])
      map_mul' := fun a b => hinj (by simp [← hs])
      map_zero' := hinj (by simp [← hs])
      map_add' := fun a b => hinj (by simp [← hs]) }
  have hτO : ∀ a : O, τ (algebraMap O A a) = algebraMap O A (σO a) := by
    intro a
    rw [IsScalarTower.algebraMap_apply O K A, hτσ]
    change _ = algebraMap O A (s a)
    rw [hs, ← IsScalarTower.algebraMap_apply]

  have hsurj : Function.Surjective τ := fun a => ⟨τ a, hτ a⟩
  obtain ⟨tI, hmem, htt⟩ : ∃ tI : MaximalSpectrum A → MaximalSpectrum A,
      (∀ I y, y ∈ (tI I).asIdeal ↔ τ y ∈ I.asIdeal) ∧ ∀ I, tI (tI I) = I := by
    have hmax : ∀ I : MaximalSpectrum A, (I.asIdeal.comap τ).IsMaximal := fun I => by
      haveI := I.isMaximal
      exact Ideal.comap_isMaximal_of_surjective τ hsurj
    refine ⟨fun I => ⟨I.asIdeal.comap τ, hmax I⟩, fun I y => Iff.rfl, fun I => ?_⟩
    ext y
    change τ (τ y) ∈ I.asIdeal ↔ y ∈ I.asIdeal
    rw [hτ]

  obtain ⟨e, he⟩ := exists_residues_indicator (fun I : MaximalSpectrum A => WellOrderingRel I (tI I))
  have he1 : ∀ I, WellOrderingRel I (tI I) → e - 1 ∈ I.asIdeal := fun I => (he I).1
  have he0 : ∀ I, ¬ WellOrderingRel I (tI I) → e ∈ I.asIdeal := fun I => (he I).2
  have hτe1 : ∀ I, WellOrderingRel (tI I) I → τ e - 1 ∈ I.asIdeal := by
    intro I h
    have := he1 (tI I) (by rw [htt]; exact h)
    rw [hmem, map_sub, map_one] at this
    exact this
  have hτe0 : ∀ I, ¬ WellOrderingRel (tI I) I → τ e ∈ I.asIdeal := by
    intro I h
    exact (hmem I e).1 (he0 (tI I) (by rw [htt]; exact h))
  have hee : e * e = e := by
    refine sub_eq_zero.1 (eq_zero_of_forall_mem fun I => ?_)
    by_cases hP : WellOrderingRel I (tI I)
    · have := I.asIdeal.mul_mem_left e (he1 I hP)
      rwa [mul_sub, mul_one] at this
    · exact I.asIdeal.sub_mem (I.asIdeal.mul_mem_left e (he0 I hP)) (he0 I hP)
  have hgg : τ e * τ e = τ e := by rw [← map_mul, hee]
  have heg : e * τ e = 0 := by
    refine eq_zero_of_forall_mem fun I => ?_
    by_cases hP : WellOrderingRel I (tI I)
    · exact I.asIdeal.mul_mem_left _ (hτe0 I (asymm_of WellOrderingRel hP))
    · exact I.asIdeal.mul_mem_right _ (he0 I hP)

  set f : A := 1 - e - τ e with hf
  have hfix : ∀ I, tI I = I → f - 1 ∈ I.asIdeal := by
    intro I hI
    have h0 : ¬ WellOrderingRel I (tI I) := by rw [hI]; exact irrefl_of WellOrderingRel I
    have h0' : ¬ WellOrderingRel (tI I) I := by rw [hI]; exact irrefl_of WellOrderingRel I
    have : f - 1 = -(e + τ e) := by rw [hf]; ring
    rw [this]
    exact I.asIdeal.neg_mem (I.asIdeal.add_mem (he0 I h0) (hτe0 I h0'))
  have hmov : ∀ I, tI I ≠ I → f ∈ I.asIdeal := by
    intro I hI
    rcases trichotomous_of WellOrderingRel I (tI I) with h | h | h
    · have : f = -(e - 1) - τ e := by rw [hf]; ring
      rw [this]
      exact I.asIdeal.sub_mem (I.asIdeal.neg_mem (he1 I h)) (hτe0 I (asymm_of WellOrderingRel h))
    · exact absurd h.symm hI
    · have : f = -(τ e - 1) - e := by rw [hf]; ring
      rw [this]
      exact I.asIdeal.sub_mem (I.asIdeal.neg_mem (hτe1 I h)) (he0 I (asymm_of WellOrderingRel h))

  set a : A := (x : A) with ha
  set b : A := ((x⁻¹ : Aˣ) : A) with hb
  have hab : a * b = 1 := x.mul_inv
  have hpq : τ a * τ b = 1 := by rw [← map_mul, hab, map_one]

  have hstable : ∀ I : MaximalSpectrum A, tI I = I →
      IsIntegral O (Ideal.Quotient.mk I.asIdeal a) ∧ IsIntegral O (Ideal.Quotient.mk I.asIdeal b) := by
    intro I hI
    have hle : I.asIdeal ≤ I.asIdeal.comap τ := fun y hy => by
      rw [Ideal.mem_comap, ← hmem, hI]; exact hy
    let ρ := Ideal.quotientMap I.asIdeal τ hle
    have hρ : ∀ y, ρ (Ideal.Quotient.mk I.asIdeal y) = Ideal.Quotient.mk I.asIdeal (τ y) :=
      fun y => Ideal.quotientMap_mk
    have hcomp : (algebraMap O (A ⧸ I.asIdeal)).comp σO = ρ.comp (algebraMap O (A ⧸ I.asIdeal)) := by
      ext r
      change Ideal.Quotient.mk _ (algebraMap O A (σO r)) = ρ (Ideal.Quotient.mk _ (algebraMap O A r))
      rw [hρ, hτO]
    have hρi : ∀ z, IsIntegral O z → IsIntegral O (ρ z) := fun z hz =>
      IsIntegral.map_of_comp_eq σO ρ hcomp hz
    have hmk : ∀ y : A, IsIntegral O y → IsIntegral O (Ideal.Quotient.mk I.asIdeal y) :=
      fun y hy => hy.map (Ideal.Quotient.mkₐ O I.asIdeal)
    have hxa : a = (τ a * a) * τ b := by linear_combination -a * hpq
    have hxb : b = (τ b * b) * τ a := by linear_combination -b * hpq
    haveI := I.isMaximal
    letI : Field (A ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal
    haveI : FiniteDimensional K (A ⧸ I.asIdeal) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ K I.asIdeal).toLinearMap
        Ideal.Quotient.mk_surjective
    have hX : Ideal.Quotient.mk I.asIdeal a * Ideal.Quotient.mk I.asIdeal b = 1 := by
      rw [← map_mul, hab, map_one]
    have hinv : (Ideal.Quotient.mk I.asIdeal a)⁻¹ = Ideal.Quotient.mk I.asIdeal b :=
      inv_eq_of_mul_eq_one_right hX
    rcases isIntegral_or_isIntegral_inv (O := O) (K := K) (Ideal.Quotient.mk I.asIdeal a) with h | h
    · refine ⟨h, ?_⟩
      rw [hxb, map_mul, ← hρ]
      exact (hmk _ hci).mul (hρi _ h)
    · rw [hinv] at h
      refine ⟨?_, h⟩
      rw [hxa, map_mul, ← hρ]
      exact (hmk _ hc).mul (hρi _ h)
  have haf : IsIntegral O (a * f) ∧ IsIntegral O (b * f) := by
    constructor <;>
    · refine isIntegral_of_residues fun I => ?_
      by_cases hI : tI I = I
      · have h1 : Ideal.Quotient.mk I.asIdeal f = 1 := by
          rw [← map_one (Ideal.Quotient.mk I.asIdeal)]
          exact Ideal.Quotient.eq.2 (hfix I hI)
        rw [map_mul, h1, mul_one]
        first | exact (hstable I hI).1 | exact (hstable I hI).2
      · rw [Ideal.Quotient.eq_zero_iff_mem.2 (I.asIdeal.mul_mem_left _ (hmov I hI))]
        exact isIntegral_zero

  set T : A := a * e + τ b * τ e + f with hT
  set S : A := b * e + τ a * τ e + f with hS
  have hTS : T * S = 1 := by
    rw [hT, hS, hf]
    linear_combination e ^ 2 * hab + τ e ^ 2 * hpq + (2 - a - b) * hee + (2 - τ a - τ b) * hgg +
      (a * τ a + b * τ b - a - b - τ a - τ b + 2) * heg
  have hτT : τ T = S := by
    rw [hT, hS, hf]
    simp only [map_add, map_sub, map_mul, map_one, hτ]
    ring
  have ie : IsIntegral O e := isIntegral_of_mul_self_eq hee
  have ig : IsIntegral O (τ e) := isIntegral_of_mul_self_eq hgg
  refine ⟨Units.mkOfMulEqOne T S hTS, ?_, ?_, ?_⟩
  · change τ T * T = 1
    rw [hτT, mul_comm, hTS]
  · change IsIntegral O (T * b)
    have : T * b = e + (τ b * b) * τ e + b * f := by
      rw [hT]; linear_combination e * hab
    rw [this]
    exact (ie.add (hci.mul ig)).add haf.2
  · change IsIntegral O (S * a)
    have : S * a = e + (τ a * a) * τ e + a * f := by
      rw [hS]; linear_combination e * hab
    rw [this]
    exact (ie.add (hc.mul ig)).add haf.1

end GlobalTheory.UnitAdj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVirtualCharacterTwistedHarishChandraInduct
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

noncomputable section
namespace GlobalTheory.Shin.HatInd

theorem inPar_gal {F' : Type} [Field F'] (u : F' →+* F') (a : ℕ) {n : ℕ} (x : GL (Fin n) F') :
    InPar a (gal u n x) ↔ InPar a x := by
  unfold InPar gal
  simp only [Matrix.GeneralLinearGroup.map_apply, map_eq_zero]

theorem par_facts {F' : Type} [Field F'] (a b n : ℕ) (h : n = a + b) :
    (∀ x y : GL (Fin n) F', InPar a x → InPar a y → InPar a (x * y)) ∧ InPar a (1 : GL (Fin n) F') ∧
    (∀ x : GL (Fin n) F', InPar a x → InPar a x⁻¹) ∧
    (∀ x y : GL (Fin n) F', InPar a x → InPar a y → tlG a (x * y) = tlG a x * tlG a y) ∧
    (∀ x : GL (Fin n) F', InPar a x →
      ((tlG a x : GL (Fin a) F') : Matrix (Fin a) (Fin a) F') = tl a (x : Matrix (Fin n) (Fin n) F')) := by
  obtain ⟨H, π, hH, -, hπ, hmat, -⟩ := GlobalTheory.T.exists_blockParabolic_subgroup_levi_projection F' a b n h
  refine ⟨fun x y hx hy => (hH _).1 (H.mul_mem ((hH x).2 hx) ((hH y).2 hy)), (hH 1).1 H.one_mem,
    fun x hx => (hH _).1 (H.inv_mem ((hH x).2 hx)), fun x y hx hy => ?_, fun x hx => ?_⟩
  · have := π.map_mul ⟨x, (hH x).2 hx⟩ ⟨y, (hH y).2 hy⟩
    rw [hπ, hπ, hπ] at this
    exact congrArg Prod.fst this
  · have := (hmat ⟨x, (hH x).2 hx⟩).1
    rw [hπ] at this
    exact this

theorem tlG_gal {F' : Type} [Field F'] (u : F' →+* F') (a b n : ℕ) (h : n = a + b) (x : GL (Fin n) F')
    (hx : InPar a x) : tlG a (gal u n x) = gal u a (tlG a x) := by
  have hm := (par_facts (F' := F') a b n h).2.2.2.2
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [hm _ ((inPar_gal u a x).2 hx)]
  unfold gal
  rw [Matrix.GeneralLinearGroup.map_apply, hm _ hx]
  unfold tl ent
  split_ifs <;> simp [Matrix.GeneralLinearGroup.map_apply]

theorem finite_gal (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] :
    Finite (F' ≃ₐ[F] F') :=
  Finite.of_injective (fun e : F' ≃ₐ[F] F' => (e : F' → F')) (fun _ _ h => AlgEquiv.ext (congrFun h))

theorem galAct_symm {F F' : Type} [Field F] [Field F'] [Algebra F F'] (n : ℕ) (u : F' ≃ₐ[F] F')
    (x : GL (Fin n) F') : (galAct F F' n u).symm x = gal ((u⁻¹ : F' ≃ₐ[F] F') : F' →+* F') n x := rfl

theorem hat_ind : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (a b n : ℕ), n = a + b →
    ∀ X ∈ Virt ℂ ℂ (GHat F F' a), ∃ Z ∈ Virt ℂ ℂ (GHat F F' n), ∀ (t : F' ≃ₐ[F] F') (δ : GL (Fin n) F'),
      Z (inl δ * inr t) = hcTw (t : F' →+* F') a b (fun d => X (inl d * inr t)) (fun _ => 1) n δ := by
  intro F F' _ _ _ _ a b n hn X hX
  haveI : Finite (F' ≃ₐ[F] F') := finite_gal F F'
  haveI : Finite (GHat F F' n) := Finite.of_equiv _ SemidirectProduct.equivProd.symm
  haveI : Finite (GHat F F' a) := Finite.of_equiv _ SemidirectProduct.equivProd.symm
  obtain ⟨hmul, hone, hinv, htl, -⟩ := par_facts (F' := F') a b n hn
  let P : Subgroup (GHat F F' n) :=
    { carrier := {x | InPar a x.left}
      mul_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq, mul_left, galAct_apply] at hx hy ⊢
        exact hmul _ _ hx ((inPar_gal _ a _).2 hy)
      one_mem' := by simpa using hone
      inv_mem' := fun {x} hx => by
        simp only [Set.mem_setOf_eq, inv_left, galAct_apply] at hx ⊢
        exact (inPar_gal _ a _).2 (hinv _ hx) }
  have hP : ∀ x : GHat F F' n, x ∈ P ↔ InPar a x.left := fun _ => Iff.rfl
  let πh : P →* GHat F F' a := MonoidHom.mk' (fun p => (⟨tlG a p.1.left, p.1.right⟩ : GHat F F' a))
    (fun p q => by
      have hp := (hP _).1 p.2
      have hq := (hP _).1 q.2
      apply SemidirectProduct.ext
      · simp only [Subgroup.coe_mul, mul_left, galAct_apply]
        rw [htl _ _ hp ((inPar_gal _ a _).2 hq), tlG_gal _ a b n hn _ hq]
      · simp)
  have hcl := (virt_mul_comap_conj_ind_linear (GHat F F' a)).2.2.1 X hX
  set ψ : P → ℂ := fun p => X (πh p) with hψ
  refine ⟨ind P ψ, (virt_mul_comap_conj_ind_linear (GHat F F' n)).2.2.2.1 P ψ
    ((virt_mul_comap_conj_ind_linear (GHat F F' a)).2.1 X hX P πh), fun t δ => ?_⟩

  have key : ∀ (w : GHat F F' n) (u : F' ≃ₐ[F] F'), ext0 P ψ ((inr u)⁻¹ * w * inr u) = ext0 P ψ w := by
    intro w u
    have hl : ((inr u)⁻¹ * w * inr u).left = gal ((u⁻¹ : F' ≃ₐ[F] F') : F' →+* F') n w.left := by
      simp [mul_left, galAct_apply, galAct_symm]
    have hr : ((inr u)⁻¹ * w * inr u).right = u⁻¹ * w.right * u := by simp
    unfold ext0
    by_cases hw : InPar a w.left
    · have hw' : (inr u)⁻¹ * w * inr u ∈ P := by rw [hP, hl]; exact (inPar_gal _ a _).2 hw
      rw [dif_pos hw', dif_pos ((hP w).2 hw)]
      simp only [hψ]
      have : πh ⟨(inr u)⁻¹ * w * inr u, hw'⟩ = (inr u)⁻¹ * πh ⟨w, (hP w).2 hw⟩ * inr u := by
        apply SemidirectProduct.ext
        · change tlG a ((inr u)⁻¹ * w * inr u).left = _
          rw [hl, tlG_gal _ a b n hn _ hw]
          simp [MonoidHom.mk'_apply, mul_left, galAct_apply, galAct_symm, πh]
        · change ((inr u)⁻¹ * w * inr u).right = _
          rw [hr]
          simp [MonoidHom.mk'_apply, πh]
      rw [this]
      have := hcl (πh ⟨w, (hP w).2 hw⟩) (inr u)
      simpa using this
    · have hw' : (inr u)⁻¹ * w * inr u ∉ P := by
        rw [hP, hl]; exact fun h => hw ((inPar_gal _ a _).1 h)
      rw [dif_neg hw', dif_neg (fun h => hw ((hP w).1 h))]
  haveI : Fintype (GHat F F' n) := Fintype.ofFinite _
  haveI : Fintype (GL (Fin n) F') := Fintype.ofFinite _
  haveI : Fintype (F' ≃ₐ[F] F') := Fintype.ofFinite _
  set g : GHat F F' n := inl δ * inr t with hg
  have hval : ∀ y : GL (Fin n) F', ext0 P ψ ((inl y)⁻¹ * g * inl y) =
      if InPar a (y⁻¹ * δ * gal (t : F' →+* F') n y) then
        X (inl (tlG a (y⁻¹ * δ * gal (t : F' →+* F') n y)) * inr t) * 1 else 0 := by
    intro y
    have hl : ((inl y)⁻¹ * g * inl y).left = y⁻¹ * δ * gal (t : F' →+* F') n y := by
      simp [hg, mul_left, galAct_apply]
    have hr : ((inl y)⁻¹ * g * inl y).right = t := by simp [hg]
    unfold ext0
    by_cases hw : InPar a (y⁻¹ * δ * gal (t : F' →+* F') n y)
    · rw [dif_pos (by rw [hP, hl]; exact hw), if_pos hw, mul_one]
      simp only [hψ]
      congr 1
      apply SemidirectProduct.ext
      · change tlG a ((inl y)⁻¹ * g * inl y).left = _
        rw [hl]; simp
      · change ((inl y)⁻¹ * g * inl y).right = _
        rw [hr]; simp
    · rw [dif_neg (by rw [hP, hl]; exact hw), if_neg hw]
  have hz : ∀ (y : GL (Fin n) F') (u : F' ≃ₐ[F] F'),
      ((SemidirectProduct.equivProd (φ := galAct F F' n)).symm (y, u)) = inl y * inr u := by
    intro y u
    apply SemidirectProduct.ext <;> simp [SemidirectProduct.equivProd]
  have hsum : ∑ᶠ z : GHat F F' n, ext0 P ψ (z⁻¹ * g * z) =
      (Nat.card (F' ≃ₐ[F] F') : ℂ) * ∑ᶠ y : GL (Fin n) F', ext0 P ψ ((inl y)⁻¹ * g * inl y) := by
    rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype,
      ← (SemidirectProduct.equivProd (φ := galAct F F' n)).symm.sum_comp, Fintype.sum_prod_type,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    have : ∀ u : F' ≃ₐ[F] F', ext0 P ψ ((inl y * inr u)⁻¹ * g * (inl y * inr u)) =
        ext0 P ψ ((inl y)⁻¹ * g * inl y) := by
      intro u
      have e : (inl y * inr u)⁻¹ * g * (inl y * inr u) = (inr u)⁻¹ * ((inl y)⁻¹ * g * inl y) * inr u := by
        simp only [mul_inv_rev, mul_assoc]
      rw [e, key]
    simp only [hz, this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
  have hcard : Nat.card P = Nat.card {p : GL (Fin n) F' // InPar a p} * Nat.card (F' ≃ₐ[F] F') := by
    rw [← Nat.card_prod]
    exact Nat.card_congr
      { toFun := fun p => (⟨p.1.left, p.2⟩, p.1.right)
        invFun := fun q => ⟨⟨q.1.1, q.2⟩, q.1.2⟩
        left_inv := fun p => rfl
        right_inv := fun q => rfl }
  have hB : (Nat.card (F' ≃ₐ[F] F') : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := F' ≃ₐ[F] F')).ne'
  unfold ind hcTw
  rw [hcard, hsum]
  simp only [hval]
  push_cast
  rw [mul_inv, mul_assoc, ← mul_assoc _ (Nat.card (F' ≃ₐ[F] F') : ℂ), inv_mul_cancel₀ hB, one_mul]

end GlobalTheory.Shin.HatInd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTypeFieldStrictlyHenselian
section
open GlobalTheory.EtC

namespace GlobalTheory

theorem field_finiteType_algClosed_SH : ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [Algebra k B]
    [Algebra.FiniteType k B], IsField B → SH B := by
  intro k B _ _ _ _ _ hB
  letI : Field B := hB.toField
  haveI : Module.Finite k B := finite_of_finite_type_of_isJacobsonRing k B
  have hbk : Function.Bijective (algebraMap k B) := IsAlgClosed.algebraMap_bijective_of_isIntegral
  haveI : IsAlgClosed B := IsAlgClosed.of_ringEquiv k B
    (RingEquiv.ofBijective (algebraMap k B) hbk)
  refine ⟨Field.henselian B, ?_⟩
  have hbij : Function.Bijective (IsLocalRing.residue B) :=
    ⟨(IsLocalRing.residue B).injective, Ideal.Quotient.mk_surjective⟩
  haveI : IsAlgClosed (IsLocalRing.ResidueField B) :=
    IsAlgClosed.of_ringEquiv B _ (RingEquiv.ofBijective _ hbij)
  exact IsSepClosed.of_isAlgClosed _

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsuppMapDomainEqZeroAtFilteredStage
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory

theorem filtered_identify_pairs {J : Type} [SmallCategory J] [IsFiltered J] (P : J ⥤ Type)
    (Q : Type) (ι : ∀ j, P.obj j → Q)
    (hinj : ∀ j (x y : P.obj j), ι j x = ι j y → ∃ (k : J) (f : j ⟶ k), P.map f x = P.map f y)
    (j : J) (T : Finset (P.obj j × P.obj j)) (hT : ∀ p ∈ T, ι j p.1 = ι j p.2) :
    ∃ (k : J) (f : j ⟶ k), ∀ p ∈ T, P.map f p.1 = P.map f p.2 := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨j, 𝟙 j, by simp⟩
  | @insert p T hp ih =>
    obtain ⟨k1, f1, h1⟩ := ih (fun q hq => hT q (Finset.mem_insert_of_mem hq))
    obtain ⟨k2, f2, h2⟩ := hinj j p.1 p.2 (hT p (Finset.mem_insert_self p T))
    have e : f1 ≫ IsFiltered.leftToMax k1 k2 ≫
          IsFiltered.coeqHom (f1 ≫ IsFiltered.leftToMax k1 k2) (f2 ≫ IsFiltered.rightToMax k1 k2) =
        f2 ≫ IsFiltered.rightToMax k1 k2 ≫
          IsFiltered.coeqHom (f1 ≫ IsFiltered.leftToMax k1 k2) (f2 ≫ IsFiltered.rightToMax k1 k2) := by
      simpa only [Category.assoc] using
        IsFiltered.coeq_condition (f1 ≫ IsFiltered.leftToMax k1 k2) (f2 ≫ IsFiltered.rightToMax k1 k2)
    refine ⟨_, f1 ≫ IsFiltered.leftToMax k1 k2 ≫
          IsFiltered.coeqHom (f1 ≫ IsFiltered.leftToMax k1 k2) (f2 ≫ IsFiltered.rightToMax k1 k2), ?_⟩
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · rw [e]
      simp only [FunctorToTypes.map_comp_apply, h2]
    · simp only [FunctorToTypes.map_comp_apply, h1 q hq]

theorem finsupp_mapDomain_eq_zero_at_stage (Λ : Type 1) [AddCommGroup Λ] (J : Type)
    [SmallCategory J] [IsFiltered J] (P : J ⥤ Type) (Q : Type) (ι : ∀ j, P.obj j → Q)
    (hcompat : ∀ (j k : J) (f : j ⟶ k) (x : P.obj j), ι k (P.map f x) = ι j x)
    (hinj : ∀ j (x y : P.obj j), ι j x = ι j y → ∃ (k : J) (f : j ⟶ k), P.map f x = P.map f y)
    (j : J) (x : P.obj j →₀ Λ) (hx : Finsupp.mapDomain (ι j) x = 0) :
    ∃ (k : J) (f : j ⟶ k), Finsupp.mapDomain (P.map f) x = 0 := by
  classical
  obtain ⟨k, f, hf⟩ := filtered_identify_pairs P Q ι hinj j
    ((x.support ×ˢ x.support).filter (fun p => ι j p.1 = ι j p.2))
    (fun p hp => (Finset.mem_filter.mp hp).2)
  refine ⟨k, f, ?_⟩
  have hcomp : Finsupp.mapDomain (ι k) (Finsupp.mapDomain (P.map f) x) =
      Finsupp.mapDomain (ι j) x := by
    rw [← Finsupp.mapDomain_comp]
    congr 1
    funext a
    exact hcompat j k f a
  have hInj : Set.InjOn (ι k) (P.map f '' (x.support : Set (P.obj j))) := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
    rw [hcompat, hcompat] at hab
    exact hf (a, b) (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hab⟩)
  apply Finsupp.mapDomain_injOn _ hInj
  · intro b hb
    have := Finsupp.mapDomain_support (f := P.map f) (s := x) hb
    simpa using this
  · simp
  · rw [hcomp, hx, Finsupp.mapDomain_zero]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatFerrandPushoutOverFibreProduct
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option autoImplicit false

namespace GlobalTheory.FerrandFlat

theorem flat_of_appLE {Y : Scheme.{0}} {P : CommRingCat.{0}} (y : Y ⟶ Spec P) (h : ∀ V : Y.Opens, IsAffineOpen V → (y.appLE ⊤ V (fun _ _ => trivial)).hom.Flat) : Flat y :=
  HasRingHomProperty.of_iSup_eq_top (P := @Flat) (fun V : Y.affineOpens => V) (iSup_affineOpens_eq_top Y) (fun V => h V.1 V.2)

theorem flat_pushout : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → Function.Surjective g₁ → Function.Surjective g₂ → IsNilpotent (RingHom.ker g₁.hom) → IsNilpotent (RingHom.ker g₂.hom) → ∀ (Y₁ Y₂ Y₀ : Scheme.{0}) (p₁ : Y₁ ⟶ Spec R₁) (p₂ : Y₂ ⟶ Spec R₂) (p₀ : Y₀ ⟶ Spec R₀) (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂), IsPullback i₁ p₀ p₁ (Spec.map g₁) → IsPullback i₂ p₀ p₂ (Spec.map g₂) → Flat p₁ → Flat p₂ → ∀ (Y : Scheme.{0}) (j₁ : Y₁ ⟶ Y) (j₂ : Y₂ ⟶ Y) (hw : i₁ ≫ j₁ = i₂ ≫ j₂), IsClosedImmersion j₁ → IsClosedImmersion j₂ → (∀ V : Y.Opens, IsPullback (j₁.app V) (j₂.app V) (i₁.appLE (j₁ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) le_rfl) (i₂.appLE (j₂ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) (by rw [hw]; exact le_rfl))) → ∀ (y : Y ⟶ Spec P), j₁ ≫ y = p₁ ≫ Spec.map f₁ → j₂ ≫ y = p₂ ≫ Spec.map f₂ → IsPullback j₁ p₁ y (Spec.map f₁) ∧ IsPullback j₂ p₂ y (Spec.map f₂) ∧ Flat y := by
  intro P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hg₁ hg₂ hn₁ hn₂ Y₁ Y₂ Y₀ p₁ p₂ p₀ i₁ i₂ h₁ h₂ hf₁ hf₂ Y j₁ j₂ hw hj₁ hj₂ hV y hy₁ hy₂
  have H := GlobalTheory.T.ferrandPushout_affine_flat_and_pushouts P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hg₁ hg₂ hn₁ hn₂ Y₁ Y₂ Y₀ p₁ p₂ p₀ i₁ i₂ h₁ h₂ hf₁ hf₂ Y j₁ j₂ hw
    hj₁ hj₂ hV y hy₁ hy₂
  exact ⟨GlobalTheory.T.isPullback_of_isAffine_of_forall_isPushout_appLE _ _ _ _ j₁ p₁ y (Spec.map f₁) inferInstance inferInstance inferInstance hy₁
      (fun V hV => (H V hV).2.1),
    GlobalTheory.T.isPullback_of_isAffine_of_forall_isPushout_appLE _ _ _ _ j₂ p₂ y (Spec.map f₂) inferInstance inferInstance inferInstance hy₂
      (fun V hV => (H V hV).2.2),
    flat_of_appLE y (fun V hV => (H V hV).1)⟩

end GlobalTheory.FerrandFlat
end

