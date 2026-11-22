import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0117
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0551
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0324
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0024
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Formalism.LocalToGlobal.Columns.HeckeSp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0554
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0359
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0395
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNoetherianModelOfDivisorOfConstants
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0203
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0235
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0552
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0298
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0542

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbedsInRegularRepresentationCopiesOfGroupDeterm
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module

noncomputable section

namespace GlobalTheory.RegEmbed

variable {K Γ R : Type} [Field K] [Group Γ] [CommRing R] [Algebra K R]
  (act : Γ →* (R →ₐ[K] R)) (H : Subgroup Γ) [Fintype H]

theorem act_mul_apply (a b : Γ) (x : R) : act (a * b) x = act a (act b x) := by
  rw [map_mul]; rfl

theorem act_one_apply (x : R) : act 1 x = x := by
  rw [map_one]; rfl

theorem sum_act_act (x : R) (g : H) : ∑ k : H, act k (act g x) = ∑ k : H, act k x := by
  rw [← Equiv.sum_comp (Equiv.mulRight g⁻¹)]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [← act_mul_apply]

theorem act_sum_act (x : R) (g : H) : act g (∑ k : H, act k x) = ∑ k : H, act k x := by
  rw [map_sum]
  rw [← Equiv.sum_comp (Equiv.mulLeft g⁻¹)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Equiv.coe_mulLeft, ← act_mul_apply, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]

def invIn (V₁ : Submodule K R) : Submodule K R where
  carrier := {x | x ∈ V₁ ∧ ∀ h : H, act h x = x}
  add_mem' := fun ha hb => ⟨V₁.add_mem ha.1 hb.1, fun h => by rw [map_add, ha.2, hb.2]⟩
  zero_mem' := ⟨V₁.zero_mem, fun h => map_zero _⟩
  smul_mem' := fun c x hx => ⟨V₁.smul_mem c hx.1, fun h => by rw [map_smul, hx.2]⟩

def trL : R →ₗ[K] R := ∑ g : H, (act g).toLinearMap

theorem trL_apply (x : R) : trL act H x = ∑ g : H, act g x := by
  simp [trL]

theorem trL_mem (V₁ : Submodule K R) (hV₁ : ∀ h : H, ∀ x ∈ V₁, act h x ∈ V₁) (x : R) (hx : x ∈ V₁) :
    trL act H x ∈ invIn act H V₁ := by
  rw [trL_apply]
  exact ⟨V₁.sum_mem fun g _ => hV₁ g x hx, fun g => act_sum_act act H x g⟩

theorem eq_zero_of_traces [DecidableEq H] (u : R)
    (hdet : (Matrix.of fun h g : H => act ((h : Γ) * g) u).det ∈ nonZeroDivisors R) (v : R)
    (hv : ∀ h : H, ∑ g : H, act g (v * act h u) = 0) : v = 0 := by
  have h0 := GlobalTheory.mulVec_eq_zero_of_det_nonZeroDivisor (Matrix.transpose (Matrix.of fun h g : H => act ((h : Γ) * g) u))
    (by rwa [Matrix.det_transpose]) (fun g : H => act g v) (by
      funext h
      rw [Pi.zero_apply, ← hv h]
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.of_apply]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [map_mul (act (g : Γ)), act_mul_apply, mul_comm])
  simpa [act_one_apply] using congrFun h0 1

theorem eq_zero_of_sum [DecidableEq H] (u : R)
    (hdet : (Matrix.of fun h g : H => act ((h : Γ) * g) u).det ∈ nonZeroDivisors R) (F : H → R)
    (hF : ∀ g h : H, act g (F h) = F h) (h0 : ∑ h : H, F h * act h u = 0) : F = 0 := by
  refine GlobalTheory.mulVec_eq_zero_of_det_nonZeroDivisor _ hdet F ?_
  funext g
  have h2 := congrArg (fun x => act (g : Γ) x) h0
  simp only [map_sum, map_zero] at h2
  rw [Pi.zero_apply, ← h2]
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [map_mul (act (g : Γ)), hF, act_mul_apply, mul_comm]

end GlobalTheory.RegEmbed

namespace GlobalTheory.BadCount

open GlobalTheory.RegEmbed in

theorem embReg_of_groupDet : ∀ (K Γ R : Type) [Field K] [Group Γ] [Finite Γ] [CommRing R] [Algebra K R] (act : Γ →* (R →ₐ[K] R)) (H : Subgroup Γ) [Fintype H] [DecidableEq H] (u : R), (Matrix.of fun h g : H => act ((h : Γ) * g) u).det ∈ nonZeroDivisors R → ∀ (V V₁ V₂ : Submodule K R) [FiniteDimensional K V₂] (ρ : Representation K Γ V), (∀ g x, (ρ g x : R) = act g x) → (∀ h : H, ∀ x ∈ V, x * act h u ∈ V₁) → (∀ h : H, ∀ x ∈ V₁, act h x ∈ V₁) → (∀ h : H, ∀ x ∈ V₁, x * act h u ∈ V₂) → ∃ n : ℕ, EmbReg ρ H n ∧ n * Nat.card H ≤ finrank K V₂ := by
  intro K Γ R _ _ _ _ _ act H _ _ u hdet V V₁ V₂ _ ρ hρ hV hV₁ hV₁₂
  let I := invIn act H V₁
  let T : H → (V →ₗ[K] I) := fun h =>
    ((trL act H).comp ((LinearMap.mulRight K (act h u)).comp V.subtype)).codRestrict I
      (fun v => trL_mem act H V₁ hV₁ _ (hV h v v.2))
  have hT : ∀ h v, ((T h v : I) : R) = ∑ g : H, act g (v * act h u) := fun h v => by
    simp [T, trL_apply]
  let Ψ : (H → I) →ₗ[K] V₂ :=
    (∑ h : H, (LinearMap.mulRight K (act h u)).comp (I.subtype.comp (LinearMap.proj h))).codRestrict V₂
      (fun F => by
        simp only [LinearMap.sum_apply, LinearMap.comp_apply]
        exact V₂.sum_mem fun h _ => hV₁₂ h _ (F h).2.1)
  have hΨ : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro F hF
    have h0 := eq_zero_of_sum act H u hdet (fun h => (F h : R)) (fun g h => (F h).2.2 g) (by
      have := congrArg Subtype.val hF
      simpa [Ψ] using this)
    funext h
    exact Subtype.ext (congrFun h0 h)
  haveI : Module.Finite K (H → I) := Module.Finite.of_injective Ψ hΨ
  haveI : Module.Finite K I :=
    Module.Finite.of_surjective (LinearMap.proj (R := K) (φ := fun _ : H => I) 1) (fun x => ⟨fun _ => x, rfl⟩)
  have hle := LinearMap.finrank_le_finrank_of_injective hΨ
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul] at hle
  let b := Module.finBasis K I
  let j : V →ₗ[K] (Fin (finrank K I) → MonoidAlgebra K H) := LinearMap.pi fun i =>
    (MonoidAlgebra.coeffLinearEquiv K).symm.toLinearMap ∘ₗ (Finsupp.linearEquivFunOnFinite K K H).symm.toLinearMap ∘ₗ
      LinearMap.pi (fun h => (LinearMap.proj i ∘ₗ b.equivFun.toLinearMap) ∘ₗ T h)
  have hj : ∀ v i h, (j v i).coeff h = b.equivFun (T h v) i := fun v i h => by
    simp [j]
  refine ⟨finrank K I, ⟨j, ?_, ?_⟩, ?_⟩
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have hTv : ∀ h, T h v = 0 := fun h => by
      apply b.equivFun.injective
      funext i
      rw [← hj, hv]
      simp
    apply Subtype.ext
    refine eq_zero_of_traces act H u hdet (v : R) fun h => ?_
    rw [← hT, hTv]
    rfl
  · intro h v i
    apply MonoidAlgebra.ext
    ext k
    rw [MonoidAlgebra.single_mul_apply, one_mul, hj, hj]
    have : T k (ρ h v) = T (h⁻¹ * k) v := by
      apply Subtype.ext
      rw [hT, hT, hρ]
      conv_rhs => rw [← sum_act_act act H _ h]
      refine Finset.sum_congr rfl fun g _ => ?_
      congr 1
      rw [map_mul (act (h : Γ)), Subgroup.coe_mul, Subgroup.coe_inv, ← act_mul_apply act (h : Γ) ((h : Γ)⁻¹ * k),
        mul_inv_cancel_left]
    rw [this]
  · rw [Nat.card_eq_fintype_card, mul_comm]
    exact hle

end GlobalTheory.BadCount
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleAtPrimeOfRegularOfIsIntegrallyClosedIn
section
open IsLocalRing Polynomial

namespace GlobalTheory.PurityLoc

noncomputable def integralClosureEquiv (R C : Type) [CommRing R] [CommRing C] [Algebra R C]
    [Algebra.IsIntegral R C] (M : Submonoid R)
    (h : IsIntegrallyClosedIn C (Localization (Algebra.algebraMapSubmonoid C M))) :
    C ≃ₐ[R] integralClosure R (Localization (Algebra.algebraMapSubmonoid C M)) :=
  AlgEquiv.ofBijective
    ((IsScalarTower.toAlgHom R C _).codRestrict _ fun c =>
      (Algebra.IsIntegral.isIntegral (R := R) c).map (IsScalarTower.toAlgHom R C _))
    (by
      obtain ⟨hinj, hcl⟩ := isIntegrallyClosedIn_iff.mp h
      refine ⟨fun x y hxy => hinj (congrArg Subtype.val hxy), fun ⟨x, hx⟩ => ?_⟩
      obtain ⟨c, hc⟩ := hcl (hx.tower_top (A := C))
      exact ⟨c, Subtype.ext hc⟩)

theorem isReduced_isArtinianRing_localization (R C : Type) [CommRing R] [IsDomain R] [CommRing C]
    [Algebra R C] [Module.Finite R C]
    (h : Algebra.Etale (Localization.AtPrime (⊥ : Ideal R))
      (TensorProduct R (Localization.AtPrime (⊥ : Ideal R)) C)) :
    IsReduced (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R))) ∧
      IsArtinianRing (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R))) := by
  haveI := h
  haveI hKfr : IsFractionRing R (Localization.AtPrime (⊥ : Ideal R)) := by
    exact (congrArg (fun M : Submonoid R => IsLocalization M (Localization.AtPrime (⊥ : Ideal R)))
      (Ideal.primeCompl_bot (α := R))).mp inferInstance
  letI : Field (Localization.AtPrime (⊥ : Ideal R)) := IsFractionRing.toField R
  haveI : IsReduced (TensorProduct R (Localization.AtPrime (⊥ : Ideal R)) C) :=
    Algebra.FormallyUnramified.isReduced_of_field (Localization.AtPrime (⊥ : Ideal R)) _
  haveI : IsArtinianRing (TensorProduct R (Localization.AtPrime (⊥ : Ideal R)) C) :=
    IsArtinianRing.of_finite (Localization.AtPrime (⊥ : Ideal R)) _
  letI : Algebra C (TensorProduct R (Localization.AtPrime (⊥ : Ideal R)) C) :=
    Algebra.TensorProduct.rightAlgebra
  haveI : IsLocalization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R))
      (TensorProduct R (Localization.AtPrime (⊥ : Ideal R)) C) := by
    exact (congrArg (fun M : Submonoid R => IsLocalization (Algebra.algebraMapSubmonoid C M)
      (TensorProduct R (Localization.AtPrime (⊥ : Ideal R)) C)) (Ideal.primeCompl_bot (α := R))).mp
      (IsLocalization.tensorRight (S := C) (Localization.AtPrime (⊥ : Ideal R)) (⊥ : Ideal R).primeCompl)
  let e := IsLocalization.algEquiv (Algebra.algebraMapSubmonoid C (nonZeroDivisors R))
    (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R)))
    (TensorProduct R (Localization.AtPrime (⊥ : Ideal R)) C)
  exact ⟨isReduced_of_injective e.toRingHom e.injective, e.toRingEquiv.symm.isArtinianRing⟩

theorem etale_atPrime_of_isIntegrallyClosedIn : ∀ (R C : Type) [CommRing R] [IsDomain R] [CommRing C] [Algebra R C] [Module.Finite R C],
    IsIntegrallyClosedIn C (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R))) →
    ∀ (P : Ideal R) [P.IsPrime], IsRegularLocalRing (Localization.AtPrime P) →
    (∀ (P' : Ideal R) [P'.IsPrime], P' ≤ P → P'.height ≤ 1 →
      Algebra.Etale (Localization.AtPrime P') (TensorProduct R (Localization.AtPrime P') C)) →
    Algebra.Etale (Localization.AtPrime P) (TensorProduct R (Localization.AtPrime P) C) := by
  intro R C _ _ _ _ _ hC P _ hreg hP
  haveI := hreg
  obtain ⟨hred, hart⟩ := isReduced_isArtinianRing_localization R C (hP ⊥ bot_le (by simp))
  let iC := integralClosureEquiv R C (nonZeroDivisors R) hC
  have hb := TensorProduct.toIntegralClosure_bijective_of_isLocalization (R := R)
    (S := Localization.AtPrime P)
    (B := Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R))) P.primeCompl
  let Φ : TensorProduct R (Localization.AtPrime P) C ≃ₐ[Localization.AtPrime P]
      integralClosure (Localization.AtPrime P) (TensorProduct R (Localization.AtPrime P)
        (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R)))) :=
    (Algebra.TensorProduct.congr AlgEquiv.refl iC).trans (AlgEquiv.ofBijective _ hb)
  have hRE : IsReduced (TensorProduct R (Localization.AtPrime P)
        (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R)))) ∧
      IsArtinianRing (TensorProduct R (Localization.AtPrime P)
        (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R)))) := by
    letI : Algebra (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R)))
        (TensorProduct R (Localization.AtPrime P)
          (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R)))) :=
      Algebra.TensorProduct.rightAlgebra
    haveI : IsLocalization (Algebra.algebraMapSubmonoid
        (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R))) P.primeCompl)
        (TensorProduct R (Localization.AtPrime P)
          (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R)))) :=
      IsLocalization.tensorRight (Localization.AtPrime P) P.primeCompl
    haveI := hred
    haveI := hart
    let e := IsLocalization.algEquiv (Algebra.algebraMapSubmonoid
        (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R))) P.primeCompl)
      (TensorProduct R (Localization.AtPrime P)
        (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R))))
      (Localization (Algebra.algebraMapSubmonoid
        (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R))) P.primeCompl))
    exact ⟨isReduced_of_injective e.toRingHom e.injective,
      IsArtinianRing.localization_artinian (Algebra.algebraMapSubmonoid
        (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R))) P.primeCompl) _⟩
  have hunit : ∀ s : Localization.AtPrime P, s ≠ 0 → IsUnit (algebraMap (Localization.AtPrime P)
      (TensorProduct R (Localization.AtPrime P)
        (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R)))) s) := by
    intro s hs
    obtain ⟨⟨r, u⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl s
    have hr : r ≠ 0 := by rintro rfl; exact hs (by simp)
    have h0 : IsUnit (algebraMap R (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R))) r) := by
      rw [IsScalarTower.algebraMap_apply R C (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R)))]
      exact IsLocalization.map_units (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R)))
        (⟨algebraMap R C r, Algebra.mem_algebraMapSubmonoid_of_mem
          (⟨r, mem_nonZeroDivisors_of_ne_zero hr⟩ : nonZeroDivisors R)⟩ :
            Algebra.algebraMapSubmonoid C (nonZeroDivisors R))
    have h1 : IsUnit (algebraMap (Localization.AtPrime P) (TensorProduct R (Localization.AtPrime P)
        (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R)))) (algebraMap R _ r)) := by
      rw [← IsScalarTower.algebraMap_apply R (Localization.AtPrime P),
        ← (Algebra.TensorProduct.includeRight (R := R) (A := Localization.AtPrime P)
          (B := Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R)))).commutes r]
      exact h0.map _
    have h2 : algebraMap (Localization.AtPrime P) (TensorProduct R (Localization.AtPrime P)
        (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R))))
          (IsLocalization.mk' (Localization.AtPrime P) r u) *
        algebraMap (Localization.AtPrime P) _ (algebraMap R (Localization.AtPrime P) u) =
        algebraMap (Localization.AtPrime P) _ (algebraMap R (Localization.AtPrime P) r) := by
      rw [← map_mul, IsLocalization.mk'_spec]
    rw [← h2] at h1
    exact isUnit_of_mul_isUnit_left h1
  have hnz : NoZeroSMulDivisors (Localization.AtPrime P) (TensorProduct R (Localization.AtPrime P)
      (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R)))) := ⟨fun {s x} h => by
    by_cases hs : s = 0
    · exact Or.inl hs
    · right
      rw [Algebra.smul_def] at h
      exact (hunit s hs).mul_right_eq_zero.mp h⟩
  haveI hfin : Module.Finite (Localization.AtPrime P) (integralClosure (Localization.AtPrime P)
      (TensorProduct R (Localization.AtPrime P)
        (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R))))) :=
    Module.Finite.equiv Φ.toLinearEquiv
  have hq : ∀ (q : Ideal (Localization.AtPrime P)) [q.IsPrime], q.height ≤ 1 →
      Algebra.Etale (Localization.AtPrime q) (TensorProduct (Localization.AtPrime P)
        (Localization.AtPrime q) (integralClosure (Localization.AtPrime P)
          (TensorProduct R (Localization.AtPrime P)
            (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R)))))) := by
    intro q _ hq1
    have hle : q.comap (algebraMap R (Localization.AtPrime P)) ≤ P := by
      have := Ideal.comap_mono (f := algebraMap R (Localization.AtPrime P))
        (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top ‹q.IsPrime›))
      exact this.trans (Localization.AtPrime.comap_maximalIdeal (I := P)).le
    have hh : (q.comap (algebraMap R (Localization.AtPrime P))).height ≤ 1 :=
      (le_of_eq (IsLocalization.height_comap P.primeCompl q)).trans hq1
    haveI h1 := GlobalTheory.OffDivisor.etale_localization_of_comap R (Localization.AtPrime P) C _ q rfl
      (hP _ hle hh)
    exact Algebra.Etale.of_equiv ((Algebra.TensorProduct.cancelBaseChange R (Localization.AtPrime P)
      (Localization.AtPrime q) (Localization.AtPrime q) C).symm.trans
        (Algebra.TensorProduct.congr AlgEquiv.refl Φ))
  haveI := GlobalTheory.PurityProd.etale_integralClosure_of_isArtinianRing (Localization.AtPrime P) _
    hRE.1 hRE.2 hnz hfin hq
  exact Algebra.Etale.of_equiv Φ.symm

end GlobalTheory.PurityLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleIntegralClosurePiOfEtale
section
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.PiClosure

noncomputable def integralClosurePiEquiv (R : Type) [CommRing R] (ι : Type) [Finite ι]
    (E : ι → Type) [∀ i, CommRing (E i)] [∀ i, Algebra R (E i)] :
    integralClosure R (∀ i, E i) ≃ₐ[R] ∀ i, integralClosure R (E i) :=
  AlgEquiv.ofBijective
    (AlgHom.pi fun i =>
      ((Pi.evalAlgHom R E i).comp (integralClosure R (∀ i, E i)).val).codRestrict
        (integralClosure R (E i)) fun x => x.2.map (Pi.evalAlgHom R E i))
    (by
      constructor
      · intro x y hxy
        apply Subtype.ext
        funext i
        exact congrArg Subtype.val (congrFun hxy i)
      · intro l
        refine ⟨⟨fun i => (l i).1,
          GlobalTheory.PurityProd.isIntegral_of_forall_apply (fun i => (l i).1) fun i => (l i).2⟩, ?_⟩
        funext i
        rfl)

theorem etale_integralClosure_pi : ∀ (R : Type) [CommRing R] (ι : Type) [Fintype ι] (E : ι → Type) [∀ i, CommRing (E i)]
    [∀ i, Algebra R (E i)], (∀ i, Algebra.Etale R (integralClosure R (E i))) →
    Algebra.Etale R (integralClosure R (∀ i, E i)) := by
  intro R _ ι _ E _ _ h
  haveI : Algebra.Etale R (∀ i, integralClosure R (E i)) := inferInstance
  exact Algebra.Etale.of_equiv (integralClosurePiEquiv R ι E).symm

end GlobalTheory.PiClosure
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClopenIntegralOfSmoothOverField
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

namespace GlobalTheory

theorem exists_clopen_integral_of_smooth_over_field :
    ∀ (F : Type) [Field F] (Z : Scheme.{0}) (q : Z ⟶ Sp F), Smooth q → ∀ z : Z,
      ∃ (W' : Scheme.{0}) (j : W' ⟶ Z), IsClosedImmersion j ∧ IsOpenImmersion j ∧ IsIntegral W' ∧
        z ∈ Set.range j := by
  intro F _ Z q hq z
  obtain ⟨hR, hN, hL⟩ := isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field F Z q hq
  have : GlobalTheory.IsNormalScheme Z := by first | exact hN | exact IsNormalScheme.of_pred hN
  have hC : irreducibleComponent z ∈ irreducibleComponents Z := irreducibleComponent_mem_irreducibleComponents z
  let C : Z.Opens := ⟨irreducibleComponent z, IsNormalScheme.isOpen_of_mem_irreducibleComponents hC⟩
  have hzC : z ∈ C := mem_irreducibleComponent
  have hrange : Set.range C.ι = (C : Set Z) := Scheme.Opens.range_ι C
  refine ⟨C.toScheme, C.ι, ?_, inferInstance, ?_, by rw [hrange]; exact hzC⟩
  · apply IsClosedImmersion.of_isPreimmersion
    rw [hrange]
    exact isClosed_of_mem_irreducibleComponents _ hC
  · have : IrreducibleSpace C := Subtype.irreducibleSpace isIrreducible_irreducibleComponent
    have : Nonempty C := ⟨⟨z, hzC⟩⟩
    exact isIntegral_of_irreducibleSpace_of_isReduced C.toScheme

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEigAtInfRangeNeBotOfMemSpan
section
open Formalism.L2.Col

namespace GlobalTheory

theorem map_mem_eigAt_of_semilinear {K V W I : Type} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module ℂ W] (σ : K →+* ℂ) (j : V →ₛₗ[σ] W) (op : I → Module.End K V)
    (T : I → Module.End ℂ W) (hT : ∀ i v, T i (j v) = j (op i v)) (y : I → K) (v : V)
    (hv : v ∈ eigAt op y) : j v ∈ eigAt T (fun i => σ (y i)) := by
  have key : ∀ (i : I) (k : ℕ) (v : V),
      ((T i - σ (y i) • (1 : Module.End ℂ W)) ^ k) (j v)
        = j (((op i - y i • (1 : Module.End K V)) ^ k) v) := by
    intro i k
    induction k with
    | zero => intro v; simp
    | succ k ih =>
      intro v
      rw [pow_succ, Module.End.mul_apply, pow_succ, Module.End.mul_apply, ← ih]
      congr 1
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub,
        map_smulₛₗ, hT]
  rw [eigAt, Submodule.mem_iInf]
  intro i
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 (eigAt_le op y i hv)
  rw [Module.End.mem_maxGenEigenspace]
  exact ⟨k, by rw [key, hk, map_zero]⟩

theorem exists_eigAt_inf_range_ne_bot_of_mem_span :
    ∀ {K V W I : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [AddCommGroup W] [Module ℂ W] (σ : K →+* ℂ) (j : V →ₛₗ[σ] W) (op : I → Module.End K V) (T : I → Module.End ℂ W) (e : Module.End K V) (x : I → ℂ) (w : W), (∀ i v, T i (j v) = j (op i v)) → PairComm op → SplitOver op → (∀ i, Commute (op i) e) → w ∈ Submodule.span ℂ (j '' (LinearMap.range e : Set V)) → w ≠ 0 → (∀ i, T i w = x i • w) → ∃ y : I → K, (∀ i, σ (y i) = x i) ∧ eigAt op y ⊓ LinearMap.range e ≠ ⊥ := by
  intro K V W I _ _ _ _ _ _ σ j op T e x w hT hc hs he hw hw0 hx
  by_contra hno
  push Not at hno
  have hall : ∀ v : V, j (e v) ∈ ⨆ (z : I → ℂ) (_ : z ≠ x), eigAt T z := by
    intro v
    have hv : v ∈ ⨆ y, eigAt op y := by
      rw [iSup_eigAt_eq_top hc hs]; exact Submodule.mem_top
    induction hv using Submodule.iSup_induction' with
    | mem y v hv =>
      have hev : e v ∈ eigAt op y := eigAt_le_comap he y hv
      by_cases hy : ∀ i, σ (y i) = x i
      · have h0 : e v ∈ eigAt op y ⊓ LinearMap.range e := ⟨hev, ⟨v, rfl⟩⟩
        rw [hno y hy, Submodule.mem_bot] at h0
        rw [h0, map_zero]
        exact Submodule.zero_mem _
      · have hne : (fun i => σ (y i)) ≠ x := fun h => hy fun i => congrFun h i
        exact le_iSup₂_of_le (f := fun (z : I → ℂ) (_ : z ≠ x) => eigAt T z) _ hne le_rfl
          (map_mem_eigAt_of_semilinear σ j op T hT y _ hev)
    | zero => rw [map_zero, map_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [map_add, map_add]; exact Submodule.add_mem _ ha hb
  have hw' : w ∈ ⨆ (z : I → ℂ) (_ : z ≠ x), eigAt T z := by
    refine Submodule.span_le.2 ?_ hw
    rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
    exact hall v
  have hd := iSupIndep_eigAt_of_any_family ℂ W I T x
  exact hw0 ((Submodule.mem_bot ℂ).1 (hd.le_bot ⟨mem_eigAt_of_forall_apply hx, hw'⟩))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalGeneratorDivBaseUnitEqGenericStatement
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_globalGenerator_div_baseUnit_eq_generic : ∀ (R K : Type) [CommRing R] [Field K] [Algebra R K] (X : Over (Sp R)) (Y : Scheme.{0}) (φ : Y ⟶ X.left) (p : Y ⟶ Sp K), φ ≫ X.hom = p ≫ spMap (algebraMap R K) → ∀ (M : LB X.left) (c : LB.Gen (M.pull φ)) (a : Kˣ) (b : Rˣ), algebraMap R K (b : R) = (a : K) → ∀ (u : LB.Gen M), u.IsGen → (∀ (i : M.ι) (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z), φ (r z) ∈ M.U i → (gm (r ≫ φ) z (M.U i) (u.s i)).val = gs (r ≫ p) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (a : K)) * (gm r z ((M.pull φ).U fun _ => i) (c.s fun _ => i)).val) → ∃ r' : LB.Gen M, r'.IsGen ∧ LB.genPull M r' φ = c := by
  first | exact @GlobalTheory.DivConst.exists_genPull_eq | exact GlobalTheory.DivConst.exists_genPull_eq | (intros; apply GlobalTheory.DivConst.exists_genPull_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInjectiveCochainModelTrivialProjectiveBundStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_injective_cochainModel_trivialProjectiveBundle : ∀ (q : ℕ) [NeZero q] (N : ℕ) (i : ℤ), ∃ (J : Cx (ZMod q)) (ψ : ∀ j : Fin N, Cocycle (res (ZMod q) (tw q (i - (j : ℕ)))) J (2 * (j : ℕ))), J.IsStrictlyGE 0 ∧ (∀ n, CategoryTheory.Injective (J.X n)) ∧ ∀ F : PSh, Inv q (disc.obj F) → ∀ n : ℤ, ∃ e : CohomologyClass ((chains (ZMod q)).obj (disc.obj F)) J n ≃+ Ht q (pullback (trivV N (disc.obj F)) (PGL.pr N)) n i, ∀ a : ∀ j : Fin N, Ht q (disc.obj F) (n - 2 * (j : ℕ)) (i - (j : ℕ)), e (∑ j, cpost _ (ψ j) (n - 2 * (j : ℕ)) n (by omega) (a j)) = pbfMap q (trivV N (disc.obj F)) n i a := by
  first | (exact @GlobalTheory.EtC.pbf_disc_model) | (exact GlobalTheory.EtC.pbf_disc_model) | (intros; apply GlobalTheory.EtC.pbf_disc_model  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNoetherianModelOfDivisorOfConstantsStatement
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_noetherian_model_of_divisor_of_constants : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (E : Type) [CommRing E] [Algebra (Polynomial T) E] [Algebra T E]
      [IsScalarTower T (Polynomial T) E] [Algebra.Etale (Polynomial T) E]
      (Q : Ideal E) [Q.IsPrime],
      Q.comap (algebraMap (Polynomial T) E) = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (j : Localization.AtPrime Q →+* O),
      j.comp (algebraMap (Polynomial T) (Localization.AtPrime Q)) = algebraMap (Polynomial T) O →
    ∀ (b₁ c₁ : Localization.AtPrime Q) (s : T), s ≠ 0 →
      b₁ * c₁ = algebraMap T (Localization.AtPrime Q) s →
    ∃ (A : Type) (_ : CommRing A) (_ : IsDomain A) (_ : IsLocalRing A) (_ : IsNoetherianRing A)
      (_ : IsIntegrallyClosed A) (_ : Algebra.EssFiniteType ℤ A) (i : A →+* T),
      Function.Injective i ∧ IsLocalHom i ∧
      ∃ (EA : Type) (_ : CommRing EA) (_ : Algebra (Polynomial A) EA) (_ : Algebra A EA)
        (_ : IsScalarTower A (Polynomial A) EA) (_ : Algebra.Etale (Polynomial A) EA)
        (QA : Ideal EA) (_ : QA.IsPrime),
        QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A ∧
      ∃ (jA : Localization.AtPrime QA →+* O),
        jA.comp (algebraMap (Polynomial A) (Localization.AtPrime QA)) =
          (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i) ∧
      ∃ (bA cA : Localization.AtPrime QA) (sA : A), sA ≠ 0 ∧ i sA = s ∧
        bA * cA = algebraMap A (Localization.AtPrime QA) sA ∧ jA bA = j b₁ := by
  first | (exact @GlobalTheory.VertUnitsNoeth.exists_noetherian_model_of_mul_eq) | (exact GlobalTheory.VertUnitsNoeth.exists_noetherian_model_of_mul_eq) | (intros; apply GlobalTheory.VertUnitsNoeth.exists_noetherian_model_of_mul_eq  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalLocalDomainOverHenselianPrimeStatement
section
open IsLocalRing Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normal_local_domain_over_henselian_prime : ∀ (A : Type) [CommRing A] [HenselianLocalRing A] (𝔭 : Ideal A) [𝔭.IsPrime],
    ∃ (S : Type) (_ : CommRing S) (_ : IsDomain S) (_ : IsIntegrallyClosed S) (_ : IsLocalRing S) (f : A →+* S), f.IsIntegral ∧ RingHom.ker f = 𝔭 := by
  first | (exact @GlobalTheory.NormalLocal.exists_normal_local) | (exact GlobalTheory.NormalLocal.exists_normal_local) | (intros; apply GlobalTheory.NormalLocal.exists_normal_local  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrthogonalRationalFrameFlagDomainStatement
section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orthogonal_rational_frame_flagDomain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (u : Fin r → Fin r → E), GlobalTheory.OrthoFrame.frm X.Ψ u ∈ X.dom → ∃ v : Fin r → Fin r → E, (∀ j k, j ≠ k → ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm (v j) (v k) = 0) ∧ GlobalTheory.OrthoFrame.frm X.Ψ v ∈ X.dom := by
  first | exact @GlobalTheory.OrthoFrame.GramSchmidt.exists_ortho_frm | exact GlobalTheory.OrthoFrame.GramSchmidt.exists_ortho_frm | (intros; apply GlobalTheory.OrthoFrame.GramSchmidt.exists_ortho_frm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusAnglesOfUnimodularProdOneStatement
section
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.TorusFrame
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torusAngles_of_unimodular_prod_one : ∀ (r : ℕ) (z : Fin r → ℂ), (∀ a, ‖z a‖ = 1) → ∏ a, z a = 1 → ∃ φ : Fin (r - 1) → ℝ, ∀ a, Complex.exp (Complex.I * (angles φ a : ℂ)) = z a := by
  first | exact @GlobalTheory.TorusAngles.exists_angles_of_prod_eq_one | exact GlobalTheory.TorusAngles.exists_angles_of_prod_eq_one | (intros; apply GlobalTheory.TorusAngles.exists_angles_of_prod_eq_one <;> assumption)
end

