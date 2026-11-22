import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.MemMixedTsub
import Development.AutomorphicSpectrum.PublishedTheorems.Divisibility₂.PrismaticFilteredAtOfIntegersAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0425
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0045
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0131
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSchemeOfThickenings
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0581
import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0578
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LineKroneckerRightMatrixConjTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0579
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0044
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0041
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0583
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0066

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniquePadicOfFrobeniusEigenAinf
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.PDivLat

theorem existsUnique_padic_of_eigen : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O →
    ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ a : Ainf p O,
      WittVector.frobenius a = WittVector.frobenius (xi ε) * a →
        ∃! c : ℤ_[p], ofPadic p O c * Sandwich.mu ε = a := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε a ha
  have h1 : IsPrimitiveRoot (GlobalTheory.Sandwich.root ε).untilt p := by
    simpa [zeta] using hε 1
  haveI : IsDomain (PreTilt O p) := PreTilt.isDomain C v O hv p
  haveI : IsDomain (Ainf p O) := GlobalTheory.Sandwich.Model.isDomain_Ainf hv
  have hμ : Sandwich.mu ε ≠ 0 := GlobalTheory.Sandwich.Model.mu_ne_zero (hε := h1) hv
  obtain ⟨c, hc⟩ := GlobalTheory.CompanionTheory.Ar.Prism.exists_padic_of_eigen h1 ha
  have hinj : Function.Injective (ofPadic p O) :=
    (WittVector.map_injective _ (RingHom.injective _)).comp (WittVector.equiv p).symm.injective
  exact ⟨c, hc, fun c' hc' => hinj (mul_right_cancel₀ hμ (hc'.trans hc.symm))⟩

end GlobalTheory.PDivLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniversalTorsionFamily
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.TorsionFamily

section General

variable {S : Scheme.{0}}

noncomputable def torsionLift (G : Over S) [GrpObj G] {T : Over S} (f : T ⟶ G) (n : ℕ) (hf : f ^ n = 1) :
    T ⟶ torsion G n :=
  pullback.lift f (toUnit T) (by rw [GlobalTheory.GrpTangent.comp_mulN, hf, Hom.one_def])

@[reassoc]
theorem torsionLift_ι (G : Over S) [GrpObj G] {T : Over S} (f : T ⟶ G) (n : ℕ) (hf : f ^ n = 1) :
    torsionLift G f n hf ≫ torsion.ι G n = f :=
  pullback.lift_fst _ _ _

theorem torsion_ι_pow (G : Over S) [GrpObj G] (n : ℕ) : torsion.ι G n ^ n = 1 := by
  rw [← GlobalTheory.GrpTangent.comp_mulN, Hom.one_def]
  exact pullback.condition.trans (congrArg (· ≫ η) (toUnit_unique _ _))

noncomputable def fpow (X : Over S) : ℕ → Over S
  | 0 => 𝟙_ (Over S)
  | k + 1 => X ⊗ fpow X k

noncomputable def fproj (X : Over S) : (k : ℕ) → Fin k → (fpow X k ⟶ X)
  | 0 => fun i => i.elim0
  | k + 1 => fun i => Fin.cases (fst X (fpow X k)) (fun j => snd X (fpow X k) ≫ fproj X k j) i

noncomputable def flift (X : Over S) {T : Over S} : (k : ℕ) → (Fin k → (T ⟶ X)) → (T ⟶ fpow X k)
  | 0 => fun _ => toUnit T
  | k + 1 => fun f => lift (f 0) (flift X k (fun j => f j.succ))

end General

end GlobalTheory.TorsionFamily
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnramifiedFieldOfInertiaProperty
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.InertiaGood

theorem not_dvd_discr_of_inertia_fix (E N : Type) [Field E] [NumberField E] [Field N] [NumberField N]
    [Algebra E N] [IsGalois ℚ N] (q : ℕ) (hq : q.Prime)
    (h : ∀ Q : Ideal (𝓞 N), Q.IsMaximal → (q : 𝓞 N) ∈ Q → ∀ τ : N ≃ₐ[ℚ] N, (∀ x : 𝓞 N, τ • x - x ∈ Q) →
      ∀ y : E, τ (algebraMap E N y) = algebraMap E N y) : ¬ (q : ℤ) ∣ discr E := by
  have hqz : Prime (q : ℤ) := Nat.prime_iff_prime_int.1 hq
  refine (not_dvd_discr_iff_forall_mem E (𝓞 E) hqz).2 fun P hP hqP => ?_
  have hqP' : (q : 𝓞 E) ∈ P := by simpa using hqP
  have hne : P ≠ ⊥ := fun h0 => by
    rw [h0, Ideal.mem_bot] at hqP'
    exact hq.ne_zero (Nat.cast_eq_zero.1 hqP')
  have hPm : P.IsMaximal := hP.isMaximal hne
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 N) P
  have hqQ : (q : 𝓞 N) ∈ Q := by
    have := (Ideal.mem_of_liesOver Q P _).1 hqP'
    rwa [map_natCast] at this
  have h1 := (GlobalTheory.UnramCompositum.ramificationIdx_eq_one_iff_fix ℚ E N Q).2 (h Q hQ hqQ)
  rw [← Ideal.over_def Q P] at h1
  have hu : Algebra.IsUnramifiedAt ℤ (P.under (𝓞 ℚ)) :=
    (not_dvd_discr_iff_forall_mem ℚ (𝓞 ℚ) hqz).1 (by
      rw [Rat.numberField_discr]; exact hqz.not_dvd_one) _ inferInstance (by
      rw [Ideal.under, Ideal.mem_comap, map_intCast]; exact hqP)
  have h2 : P.ramificationIdx ℤ = (P.under (𝓞 ℚ)).ramificationIdx ℤ * P.ramificationIdx (𝓞 ℚ) :=
    Ideal.ramificationIdx_tower (P.under (𝓞 ℚ)) P
  rw [h1, Ideal.ramificationIdx_eq_one (P.under (𝓞 ℚ)) ℤ, Nat.mul_one] at h2
  exact Ideal.ramificationIdx_eq_one_iff.1 h2

theorem exists_unramified_field_good : ∀ (N : IntermediateField ℚ ℂ) [NumberField N] [IsGalois ℚ N] (q : ℕ), q.Prime → ∀ Good : (ℂ ≃+* ℂ) → Prop, (∀ τ τ', Good τ → Good τ' → Good (τ.trans τ')) → (∀ (τ : ℂ ≃+* ℂ) (𝔮 : Ideal (𝓞 N)), 𝔮.IsMaximal → (q : 𝓞 N) ∈ 𝔮 → (∀ x : 𝓞 N, ∃ y : 𝓞 N, ((y : N) : ℂ) = τ ((x : N) : ℂ) ∧ y - x ∈ 𝔮) → Good τ) → ∃ (F' : IntermediateField ℚ ℂ) (_ : NumberField F'), ¬ (q : ℤ) ∣ discr F' ∧ ∀ τ : ℂ ≃+* ℂ, (∀ x ∈ F', τ x = x) → Good τ := by
  intro N _ _ q hq Good hmul hin
  have : Countable N := (Module.finBasis ℚ N).equivFun.injective.countable
  let T : Set (N ≃ₐ[ℚ] N) :=
    {σ | ∃ 𝔮 : Ideal (𝓞 N), 𝔮.IsMaximal ∧ (q : 𝓞 N) ∈ 𝔮 ∧ σ ∈ 𝔮.inertia (N ≃ₐ[ℚ] N)}
  let S : (N ≃ₐ[ℚ] N) → Prop := fun σ => ∀ τ : ℂ ≃+* ℂ, (∀ x : N, τ (x : ℂ) = (σ x : ℂ)) → Good τ
  have hT : ∀ σ ∈ T, S σ := by
    rintro σ ⟨𝔮, h1, h2, h3⟩ τ hτ
    exact hin τ 𝔮 h1 h2 fun x => ⟨σ • x, (hτ x).symm, AddSubgroup.mem_inertia.1 h3 x⟩
  have h1 : (1 : N ≃ₐ[ℚ] N) ∈ T := by
    have hp : Prime (q : ℤ) := Nat.prime_iff_prime_int.1 hq
    have : (Ideal.span {(q : ℤ)}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
    obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 N) (Ideal.span {(q : ℤ)})
    refine ⟨Q, hQ, ?_, one_mem _⟩
    have := (Ideal.mem_of_liesOver Q (Ideal.span {(q : ℤ)}) _).1 (Ideal.mem_span_singleton_self _)
    rwa [map_natCast] at this
  have hSmul : ∀ σ σ', S σ → S σ' → S (σ * σ') := by
    intro σ σ' hσ hσ' τ hτ
    obtain ⟨τ', hτ'⟩ := GlobalTheory.CompRat.exists_ringEquiv_complex_comp_eq N (algebraMap N ℂ)
      ((algebraMap N ℂ).comp (σ' : N →+* N))
    have hτ'' : ∀ x : N, τ' (x : ℂ) = (σ' x : ℂ) := hτ'
    have g2 : Good (τ'.symm.trans τ) := hσ _ fun x => by
      have e : τ'.symm (x : ℂ) = (σ'.symm x : ℂ) := by
        rw [RingEquiv.symm_apply_eq, hτ'', AlgEquiv.apply_symm_apply]
      rw [RingEquiv.trans_apply, e, hτ, AlgEquiv.mul_apply, AlgEquiv.apply_symm_apply]
    have e : τ'.trans (τ'.symm.trans τ) = τ := RingEquiv.ext fun z => by simp
    exact e ▸ hmul _ _ (hσ' τ' hτ'') g2
  have hIS : ∀ σ ∈ Subgroup.closure T, S σ := fun σ hσ =>
    Subgroup.closure_induction'' (p := fun σ _ => S σ) hT
      (fun x ⟨𝔮, a, b, c⟩ => hT _ ⟨𝔮, a, b, inv_mem c⟩) (hT _ h1) (fun x y _ _ => hSmul x y) hσ
  let F₀ := IntermediateField.fixedField (Subgroup.closure T)
  have : NumberField (IntermediateField.lift F₀) :=
    have : FiniteDimensional ℚ (IntermediateField.lift F₀) :=
      (IntermediateField.liftAlgEquiv F₀).toLinearEquiv.finiteDimensional
    ⟨⟩
  refine ⟨IntermediateField.lift F₀, this, ?_, fun τ hτ => ?_⟩
  · rw [← discr_eq_discr_of_algEquiv F₀ (IntermediateField.liftAlgEquiv F₀)]
    exact not_dvd_discr_of_inertia_fix F₀ N q hq fun Q a b σ c y =>
      (IntermediateField.mem_fixedField_iff _ _).1 y.2 σ
        (Subgroup.subset_closure ⟨Q, a, b, AddSubgroup.mem_inertia.2 c⟩)
  · let τa : ℂ ≃ₐ[ℚ] ℂ := AlgEquiv.ofRingEquiv (f := τ) fun x => by simp
    have hr : ∀ x : N, τ (x : ℂ) = (τa.restrictNormal N x : ℂ) := fun x =>
      (AlgEquiv.restrictNormal_commutes τa N x).symm
    refine hIS (τa.restrictNormal N) ?_ τ hr
    rw [← IntermediateField.fixingSubgroup_fixedField (Subgroup.closure T),
      IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact Subtype.ext ((hr x).symm.trans (hτ _ ((IntermediateField.mem_lift x).2 hx)))

end GlobalTheory.InertiaGood
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FerrandPushoutGoodBasicOpen
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace GlobalTheory.FerrandPush

theorem basicOpen_res_eq {Y₀ Y₁ : Scheme.{0}} (i : Y₀ ⟶ Y₁) [IsClosedImmersion i] [Surjective i]
    (U : Y₀.Opens) (b : Γ(Y₁, upOpen i U)) :
    Y₀.basicOpen ((res i U).hom b) = i ⁻¹ᵁ Y₁.basicOpen b := by
  change Y₀.basicOpen (i.appLE (upOpen i U) U (preimage_upOpen i U).ge b) = _
  rw [Scheme.basicOpen_appLE]
  refine inf_eq_right.mpr ?_
  calc i ⁻¹ᵁ Y₁.basicOpen b ≤ i ⁻¹ᵁ upOpen i U := fun x hx => Y₁.basicOpen_le b hx
    _ = U := preimage_upOpen i U

theorem upOpen_basicOpen_res {Y₀ Y₁ : Scheme.{0}} (i : Y₀ ⟶ Y₁) [IsClosedImmersion i] [Surjective i]
    (U : Y₀.Opens) (b : Γ(Y₁, upOpen i U)) :
    upOpen i (Y₀.basicOpen ((res i U).hom b)) = Y₁.basicOpen b := by
  rw [basicOpen_res_eq, upOpen_preimage]

theorem basicOpen_fibπ_mem_good {Y₀ Y₁ Y₂ : Scheme.{0}} (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂)
    [IsClosedImmersion i₁] [Surjective i₁] [IsClosedImmersion i₂] [Surjective i₂] :
    ∀ U ∈ GlobalTheory.FerrandPush.good i₁ i₂, ∀ a : (GlobalTheory.FerrandPush.fib i₁ i₂).obj (op U),
      Y₀.basicOpen (((GlobalTheory.FerrandPush.fibπ i₁ i₂).app (op U)).hom a) ∈
        GlobalTheory.FerrandPush.good i₁ i₂ := by
  intro U hU a
  obtain ⟨h0, h1, h2⟩ := hU
  have e1 : ((fibπ i₁ i₂).app (op U)).hom a = (res i₁ U).hom ((cone i₁ i₂ U).fst.hom a) := rfl
  have e2 : ((fibπ i₁ i₂).app (op U)).hom a = (res i₂ U).hom ((cone i₁ i₂ U).snd.hom a) := by
    rw [e1]
    exact congrArg (fun f : (cone i₁ i₂ U).pt ⟶ Γ(Y₀, U) => f.hom a) (cone i₁ i₂ U).condition
  refine ⟨h0.basicOpen _, ?_, ?_⟩
  · rw [e1, upOpen_basicOpen_res]
    exact h1.basicOpen _
  · rw [e2, upOpen_basicOpen_res]
    exact h2.basicOpen _

end GlobalTheory.FerrandPush
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankEigenCoindMackeyDoubleCosets
section
noncomputable section

namespace GlobalTheory.FinGL.MackeyCosets

open GlobalTheory.FinGL Formalism.L2.DIV Module

theorem mem_eig' {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ G V) (S : Set G)
    (χ : G → ℂ) (v : V) : v ∈ eig τ S χ ↔ ∀ g ∈ S, τ g v = χ g • v := by
  simp [eig, Submodule.mem_iInf, sub_eq_zero]

variable {G : Type} [Group G] {P U : Subgroup G} {V : Type} [AddCommGroup V] [Module ℂ V]
  (σ : Representation ℂ P V) (χ : G → ℂ)

theorem left_eq (φ : eig (Representation.coind P.subtype σ) (U : Set G) χ) (p : P) (g : G) :
    φ.1.1 (p * g) = σ p (φ.1.1 g) := φ.1.2 p g

theorem right_eq (φ : eig (Representation.coind P.subtype σ) (U : Set G) χ) (u : G) (hu : u ∈ U) (g : G) :
    φ.1.1 (g * u) = χ u • φ.1.1 g := by
  have h := (mem_eig' _ _ _ _).1 φ.2 u hu
  exact congrArg (fun f : Representation.coindV P.subtype σ => f.1 g) h

theorem eval_mem (φ : eig (Representation.coind P.subtype σ) (U : Set G) χ) (y : G) :
    φ.1.1 y ∈ eig σ {p | y⁻¹ * (p : G) * y ∈ U} (fun p => χ (y⁻¹ * (p : G) * y)) := by
  rw [mem_eig']
  intro p hp
  rw [← left_eq, ← right_eq σ χ φ _ hp]
  congr 1
  group

theorem eval_dc (φ : eig (Representation.coind P.subtype σ) (U : Set G) χ) (y p u : G) (hp : p ∈ P) (hu : u ∈ U) :
    φ.1.1 (p * y * u) = χ u • σ ⟨p, hp⟩ (φ.1.1 y) := by
  rw [right_eq σ χ φ u hu, ← left_eq]

def evalMap {ι : Type} (x : ι → G) : eig (Representation.coind P.subtype σ) (U : Set G) χ →ₗ[ℂ]
    ∀ i : ι, eig σ {p | (x i)⁻¹ * (p : G) * x i ∈ U} (fun p => χ ((x i)⁻¹ * (p : G) * x i)) where
  toFun φ i := ⟨φ.1.1 (x i), eval_mem σ χ φ (x i)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem key (hχ : ∀ u ∈ U, ∀ u' ∈ U, χ (u * u') = χ u * χ u') (y : G) (v : V)
    (hv : v ∈ eig σ {p | y⁻¹ * (p : G) * y ∈ U} (fun p => χ (y⁻¹ * (p : G) * y)))
    (p p' : P) (u u' : G) (hu : u ∈ U) (hu' : u' ∈ U) (h : (p : G) * y * u = p' * y * u') :
    χ u • σ p v = χ u' • σ p' v := by
  have e : y⁻¹ * ((p'⁻¹ * p : P) : G) * y = u' * u⁻¹ := by
    have : u' = ((p' : G) * y)⁻¹ * (p * y * u) := by rw [h]; group
    rw [this]; push_cast; group
  have hm : u' * u⁻¹ ∈ U := U.mul_mem hu' (U.inv_mem hu)
  have h1 := (mem_eig' _ _ _ _).1 hv (p'⁻¹ * p) (by simp only [Set.mem_setOf_eq, e]; exact hm)
  simp only [e] at h1
  have h2 : σ p v = σ p' (σ (p'⁻¹ * p) v) := by
    rw [← Module.End.mul_apply, ← map_mul]; simp
  have h3 : χ u' = χ (u' * u⁻¹) * χ u := by rw [← hχ _ hm _ hu]; simp
  rw [h2, h1, map_smul, smul_smul, h3, mul_comm]

theorem surj (h1 : χ 1 = 1) (hχ : ∀ u ∈ U, ∀ u' ∈ U, χ (u * u') = χ u * χ u') {ι : Type} (x : ι → G)
    (hx : ∀ i i' : ι, ∀ p ∈ P, ∀ u ∈ U, p * x i = x i' * u → i = i') :
    Function.Surjective (evalMap (U := U) σ χ x) := by
  classical
  intro v
  let R : G → V → Prop := fun g w => ∃ i : ι, ∃ p : P, ∃ u ∈ U, g = p * x i * u ∧ w = χ u • σ p (v i).1
  have huniq : ∀ g w w', R g w → R g w' → w = w' := by
    rintro g w w' ⟨i, p, u, hu, rfl, rfl⟩ ⟨i', p', u', hu', h, rfl⟩
    have hi : i = i' := by
      refine hx i i' ((p' : G)⁻¹ * p) (P.mul_mem (P.inv_mem p'.2) p.2) (u' * u⁻¹) (U.mul_mem hu' (U.inv_mem hu)) ?_
      have : u' = ((p' : G) * x i')⁻¹ * (p * x i * u) := by rw [h]; group
      rw [this]; group
    subst hi
    exact key σ χ hχ (x i) _ (v i).2 p p' u u' hu hu' h
  let f : G → V := fun g => if h : ∃ w, R g w then h.choose else 0
  have hf : ∀ g w, R g w → f g = w := by
    intro g w hw
    have h : ∃ w, R g w := ⟨w, hw⟩
    simp only [f, dif_pos h]
    exact huniq g _ _ h.choose_spec hw
  have hf0 : ∀ g, (¬ ∃ w, R g w) → f g = 0 := by
    intro g h
    simp only [f, dif_neg h]
  have hL : ∀ (q : P) g w, R g w → R (q * g) (σ q w) := by
    rintro q g w ⟨i, p, u, hu, rfl, rfl⟩
    refine ⟨i, q * p, u, hu, by push_cast; group, ?_⟩
    rw [map_smul, map_mul, Module.End.mul_apply]
  have hR : ∀ t ∈ U, ∀ g w, R g w → R (g * t) (χ t • w) := by
    rintro t ht g w ⟨i, p, u, hu, rfl, rfl⟩
    refine ⟨i, p, u * t, U.mul_mem hu ht, by group, ?_⟩
    rw [hχ _ hu _ ht, smul_smul, mul_comm]
  have fL : ∀ (q : P) g, f (q * g) = σ q (f g) := by
    intro q g
    by_cases h : ∃ w, R g w
    · obtain ⟨w, hw⟩ := h
      rw [hf _ _ hw, hf _ _ (hL q g w hw)]
    · rw [hf0 g h, hf0, map_zero]
      rintro ⟨w, hw⟩
      have := hL q⁻¹ _ _ hw
      exact h ⟨_, by simpa using this⟩
  have fR : ∀ t ∈ U, ∀ g, f (g * t) = χ t • f g := by
    intro t ht g
    by_cases h : ∃ w, R g w
    · obtain ⟨w, hw⟩ := h
      rw [hf _ _ hw, hf _ _ (hR t ht g w hw)]
    · rw [hf0 g h, hf0, smul_zero]
      rintro ⟨w, hw⟩
      have := hR t⁻¹ (U.inv_mem ht) _ _ hw
      exact h ⟨_, by simpa using this⟩
  refine ⟨⟨⟨f, fL⟩, (mem_eig' _ _ _ _).2 fun t ht => ?_⟩, ?_⟩
  · ext g
    exact fR t ht g
  · funext i
    apply Subtype.ext
    exact hf _ _ ⟨i, 1, 1, U.one_mem, by simp, by simp [h1]⟩

theorem finrank_eig_coind : ∀ (G : Type) [Group G] (P U : Subgroup G) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (σ : Representation ℂ P V) (χ : G → ℂ), χ 1 = 1 → (∀ u ∈ U, ∀ u' ∈ U, χ (u * u') = χ u * χ u') → ∀ (ι : Type) [Fintype ι] (x : ι → G), (∀ i i' : ι, ∀ p ∈ P, ∀ u ∈ U, p * x i = x i' * u → i = i') → (∀ g : G, (∃ i : ι, ∃ p ∈ P, ∃ u ∈ U, g = p * x i * u) ∨ ∃ y : G, (∃ p ∈ P, ∃ u ∈ U, g = p * y * u) ∧ eig σ {p | y⁻¹ * (p : G) * y ∈ U} (fun p => χ (y⁻¹ * (p : G) * y)) = ⊥) → finrank ℂ (eig (Representation.coind P.subtype σ) (U : Set G) χ) = ∑ i : ι, finrank ℂ (eig σ {p | (x i)⁻¹ * (p : G) * x i ∈ U} (fun p => χ ((x i)⁻¹ * (p : G) * x i))) := by
  intro G _ P U V _ _ _ σ χ h1 hχ ι _ x hx hcov
  have hinj : Function.Injective (evalMap (U := U) σ χ x) := by
    rw [injective_iff_map_eq_zero]
    intro φ hφ
    apply Subtype.ext
    apply Subtype.ext
    funext g
    change φ.1.1 g = 0
    rcases hcov g with ⟨i, p, hp, u, hu, rfl⟩ | ⟨y, ⟨p, hp, u, hu, rfl⟩, hy⟩
    · have : φ.1.1 (x i) = 0 := congrArg Subtype.val (congrFun hφ i)
      rw [eval_dc σ χ φ _ _ _ hp hu, this, map_zero, smul_zero]
    · have : φ.1.1 y = 0 := by
        have := eval_mem σ χ φ y
        rwa [hy, Submodule.mem_bot] at this
      rw [eval_dc σ χ φ _ _ _ hp hu, this, map_zero, smul_zero]
  rw [(LinearEquiv.ofBijective _ ⟨hinj, surj σ χ h1 hχ x hx⟩).finrank_eq, Module.finrank_pi_fintype]

end GlobalTheory.FinGL.MackeyCosets
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankRangeIdempotentLeOfEmbedsInRegular
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module

namespace GlobalTheory.BadCount

theorem finrank_range_idem_le_of_embReg : ∀ (K Γ V : Type) [Field K] [CharZero K] [Group Γ] [Finite Γ] [AddCommGroup V]
    [Module K V] (ρ : Representation K Γ V) (H : Subgroup Γ) (n : ℕ), EmbReg ρ H n → ∀ a : MonoidAlgebra K Γ,
    (∀ g, a.coeff g ≠ 0 → g ∈ H) → a * a = a → ∃ r : ℕ, (r : K) = (Nat.card H : K) * a.coeff 1 ∧
      finrank K (LinearMap.range (ρ.asAlgebraHom a)) ≤ n * r := by
  intro K Γ V _ _ _ _ _ _ ρ H n hE a ha hidem
  obtain ⟨j, hj, hjρ⟩ := hE
  classical
  let ψ := MonoidAlgebra.mapDomainAlgHom K K H.subtype
  have hψinj : Function.Injective ψ := MonoidAlgebra.mapDomain_injective Subtype.val_injective
  let a' : MonoidAlgebra K H :=
    MonoidAlgebra.ofCoeff (Finsupp.comapDomain Subtype.val a.coeff Subtype.val_injective.injOn)
  have hψa : ψ a' = a := by
    apply MonoidAlgebra.coeff_injective
    show Finsupp.mapDomain Subtype.val (Finsupp.comapDomain Subtype.val a.coeff Subtype.val_injective.injOn) = a.coeff
    apply Finsupp.mapDomain_comapDomain _ Subtype.val_injective
    intro g hg
    exact ⟨⟨g, ha g (by simpa using hg)⟩, rfl⟩
  have hidem' : a' * a' = a' := hψinj (by rw [map_mul, hψa, hidem])
  have hc1 : a'.coeff 1 = a.coeff 1 := rfl
  have key : ∀ (b : MonoidAlgebra K H) (v : V) (i : Fin n), j (ρ.asAlgebraHom (ψ b) v) i = b * j v i := by
    intro b
    induction b using MonoidAlgebra.induction_on with
    | of h =>
      intro v i
      have : ψ (MonoidAlgebra.of K H h) = MonoidAlgebra.of K Γ (h : Γ) := by
        simp [ψ]
      rw [this, Representation.asAlgebraHom_of, hjρ h v i]
      rfl
    | add b c hb hc => intro v i; simp [map_add, LinearMap.add_apply, hb, hc, add_mul]
    | smul r b hb => intro v i; simp [map_smul, LinearMap.smul_apply, hb, smul_mul_assoc]
  refine ⟨finrank K (LinearMap.range (LinearMap.mulLeft K a')), ?_, ?_⟩
  · rw [GlobalTheory.T.finrank_range_mulLeft_idempotent_groupAlgebra K H a' hidem', hc1]
  · let R := LinearMap.range (LinearMap.mulLeft K a')
    let g : LinearMap.range (ρ.asAlgebraHom a) →ₗ[K] (Fin n → R) :=
      LinearMap.pi fun i => LinearMap.codRestrict R
        ((LinearMap.proj i).comp (j.comp (LinearMap.range (ρ.asAlgebraHom a)).subtype)) (by
          rintro ⟨x, v, rfl⟩
          refine ⟨j v i, ?_⟩
          simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.proj_apply, LinearMap.mulLeft_apply]
          rw [← hψa, key])
    have hg : Function.Injective g := by
      intro x y hxy
      apply Subtype.val_injective
      apply hj
      funext i
      have := congrArg (fun f => ((f i : R) : MonoidAlgebra K H)) hxy
      simpa [g] using this
    have := LinearMap.finrank_le_finrank_of_injective hg
    rw [Module.finrank_pi_fintype] at this
    simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] using this

end GlobalTheory.BadCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FischerDecompositionFockNoncompactParts
section
noncomputable section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial GlobalTheory.JointHarm

namespace GlobalTheory.FischerParts

theorem exists_fockIP (σ : Type) [DecidableEq σ] :
    ∃ ι : MvPolynomial σ ℂ →ₗ[ℂ] lp (fun _ : σ →₀ ℕ => ℂ) 2,
      IsFockIP ι ∧ Function.Injective ι := by
  classical
  let w : (σ →₀ ℕ) → ℕ := fun α => α.prod fun _ k => k.factorial
  have hw : ∀ α, w α ≠ 0 := fun α => Finset.prod_ne_zero_iff.2 fun _ _ => Nat.factorial_ne_zero _
  let v : (σ →₀ ℕ) → lp (fun _ : σ →₀ ℕ => ℂ) 2 := fun α => lp.single 2 α (√(w α) : ℝ)
  have hv : ∀ α β, inner ℂ (v α) (v β) = if α = β then (w α : ℂ) else 0 := by
    intro α β
    simp only [v, lp.inner_single_left, lp.single_apply, Pi.single_apply]
    split_ifs with h
    · subst h
      simp only [RCLike.inner_apply, Complex.conj_ofReal]
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]
    · simp
  refine ⟨(basisMonomials σ ℂ).constr ℂ v, fun α β => ?_, ?_⟩
  · have e : ∀ α, (basisMonomials σ ℂ).constr ℂ v (monomial α 1) = v α := fun α => by
      have := (basisMonomials σ ℂ).constr_basis ℂ v α
      rwa [coe_basisMonomials] at this
    rw [e, e, hv]
    simp [w, Finsupp.prod]
  · refine (basisMonomials σ ℂ).injective_constr_of_linearIndependent ?_
    refine linearIndependent_of_ne_zero_of_inner_eq_zero (fun α h => hw α ?_) fun α β h => ?_
    · have := hv α α
      rw [h, inner_zero_left, if_pos rfl] at this
      exact_mod_cast this.symm
    · exact (hv α β).trans (if_neg h)

theorem fischer_parts : ∀ (p q r s d : ℕ), (homog (Ix p q × Ix r s) (d + 2) = (homog (Ix p q × Ix r s) (d + 2) ⊓ Submodule.span ℂ (harm2 p q r s)) ⊔ Submodule.span ℂ {R | ∃ Q ∈ homog (Ix p q × Ix r s) d, ∃ Z : Mat p q, IsPC Z ∧ R = plusPart (fockAct1 p q r s Z) Q}) ∧ (homog (Ix p q × Ix r s) (d + 2) = (homog (Ix p q × Ix r s) (d + 2) ⊓ Submodule.span ℂ (harm1 p q r s)) ⊔ Submodule.span ℂ {R | ∃ Q ∈ homog (Ix p q × Ix r s) d, ∃ Z : Mat r s, IsPC Z ∧ R = plusPart (fockAct2 p q r s Z) Q}) ∧ (homog (Ix p q × Ix r s) (d + 2) = (homog (Ix p q × Ix r s) (d + 2) ⊓ Submodule.span ℂ (jointHarm p q r s)) ⊔ Submodule.span ℂ {R | ∃ Q ∈ homog (Ix p q × Ix r s) d, (∃ Z : Mat p q, IsPC Z ∧ R = plusPart (fockAct1 p q r s Z) Q) ∨ ∃ Z : Mat r s, IsPC Z ∧ R = plusPart (fockAct2 p q r s Z) Q}) := by
  intro p q r s d
  obtain ⟨ι, hι, hinj⟩ := exists_fockIP (Ln p q r s)
  refine ⟨fischer hι hinj {M | ∃ Z, IsPC Z ∧ M = kron1 r s Z} ?_ ?_ d _ _ (fun P hP => ?_)
      fun P => ?_,
    fischer hι hinj {M | ∃ Z, IsPC Z ∧ M = kron2 p q Z} ?_ ?_ d _ _ (fun P hP => ?_)
      fun P => ?_,
    fischer hι hinj {M | (∃ Z, IsPC Z ∧ M = kron1 r s Z) ∨ ∃ Z, IsPC Z ∧ M = kron2 p q Z}
      ?_ ?_ d _ _ (fun P hP => ?_) fun P => ?_⟩
  · rintro _ ⟨Z, hZ, rfl⟩
    exact odd_kron1 hZ
  · rintro _ ⟨Z, hZ, rfl⟩
    exact ⟨_, ⟨_, isPC_conjTranspose hZ, rfl⟩, lineKroneckerLeftMatrix_conjTranspose Z⟩
  · exact fun Z hZ => hP _ ⟨Z, hZ, rfl⟩
  · constructor
    · rintro ⟨Q, hQ, Z, hZ, rfl⟩
      exact ⟨Q, hQ, _, ⟨Z, hZ, rfl⟩, rfl⟩
    · rintro ⟨Q, hQ, _, ⟨Z, hZ, rfl⟩, rfl⟩
      exact ⟨Q, hQ, Z, hZ, rfl⟩
  · rintro _ ⟨Z, hZ, rfl⟩
    exact odd_kron2 hZ
  · rintro _ ⟨Z, hZ, rfl⟩
    exact ⟨_, ⟨_, isPC_conjTranspose hZ, rfl⟩, lineKroneckerRightMatrix_conjTranspose Z⟩
  · exact fun Z hZ => hP _ ⟨Z, hZ, rfl⟩
  · constructor
    · rintro ⟨Q, hQ, Z, hZ, rfl⟩
      exact ⟨Q, hQ, _, ⟨Z, hZ, rfl⟩, rfl⟩
    · rintro ⟨Q, hQ, _, ⟨Z, hZ, rfl⟩, rfl⟩
      exact ⟨Q, hQ, Z, hZ, rfl⟩
  · rintro _ (⟨Z, hZ, rfl⟩ | ⟨Z, hZ, rfl⟩)
    exacts [odd_kron1 hZ, odd_kron2 hZ]
  · rintro _ (⟨Z, hZ, rfl⟩ | ⟨Z, hZ, rfl⟩)
    exacts [⟨_, .inl ⟨_, isPC_conjTranspose hZ, rfl⟩, lineKroneckerLeftMatrix_conjTranspose Z⟩,
      ⟨_, .inr ⟨_, isPC_conjTranspose hZ, rfl⟩, lineKroneckerRightMatrix_conjTranspose Z⟩]
  · exact ⟨fun Z hZ => hP _ (.inl ⟨Z, hZ, rfl⟩), fun Z hZ => hP _ (.inr ⟨Z, hZ, rfl⟩)⟩
  · constructor
    · rintro ⟨Q, hQ, ⟨Z, hZ, rfl⟩ | ⟨Z, hZ, rfl⟩⟩
      exacts [⟨Q, hQ, _, .inl ⟨Z, hZ, rfl⟩, rfl⟩, ⟨Q, hQ, _, .inr ⟨Z, hZ, rfl⟩, rfl⟩]
    · rintro ⟨Q, hQ, _, ⟨Z, hZ, rfl⟩ | ⟨Z, hZ, rfl⟩, rfl⟩
      exacts [⟨Q, hQ, .inl ⟨Z, hZ, rfl⟩⟩, ⟨Q, hQ, .inr ⟨Z, hZ, rfl⟩⟩]

end GlobalTheory.FischerParts
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCechOneCoboundaryOfMixedOverlapsStatement
section
open AlgebraicGeometry CategoryTheory Limits
open GlobalTheory.KS (rsT C1 IsCoc IsCob)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCechOneCoboundary_of_mixed_overlaps : ∀ (X : Scheme.{0}) (J K : Type) (V : J → X.Opens) (U : K → X.Opens), ⨆ k, U k = ⊤ → ∀ (z : C1 V) (z' : C1 U) (b : ∀ i k, Γ(X, V i ⊓ U k)), (∀ i i' k, rsT (z i i') (V i ⊓ V i' ⊓ U k) = rsT (b i k) (V i ⊓ V i' ⊓ U k) - rsT (b i' k) (V i ⊓ V i' ⊓ U k)) → (∀ i k k', rsT (z' k k') (V i ⊓ U k ⊓ U k') = rsT (b i k') (V i ⊓ U k ⊓ U k') - rsT (b i k) (V i ⊓ U k ⊓ U k')) → IsCob U z' → IsCob V z := by
  first | exact @GlobalTheory.KS.isCob_of_mixed | exact GlobalTheory.KS.isCob_of_mixed | (intros; apply GlobalTheory.KS.isCob_of_mixed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAffineCurveDivisorUnitDecompositionStatement
section
open GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothAffineCurve_divisor_unit_decomposition : ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B] (q : ℕ), IsUnit (q : k) → ∀ f : B, f ≠ 0 → ∀ b : B, b ≠ 0 → ∀ m : ℕ, ∃ g : B, g ≠ 0 ∧ IsCoprime f g ∧ ∃ u : (Localization.Away (f * g))ˣ, ∃ n d t n' d' : B, IsCoprime f n ∧ IsCoprime f d ∧ IsCoprime g n' ∧ IsCoprime g d' ∧ algebraMap B (Localization.Away (f * g)) (b * d) = (u : Localization.Away (f * g)) * algebraMap B (Localization.Away (f * g)) (n * f ^ m) ∧ (u : Localization.Away (f * g)) * algebraMap B (Localization.Away (f * g)) (t ^ q * d') = algebraMap B (Localization.Away (f * g)) n' := by
  first | (exact @GlobalTheory.KummerDiv.divisor_step) | (exact GlobalTheory.KummerDiv.divisor_step) | (intros; apply GlobalTheory.KummerDiv.divisor_step  <;> assumption)
end

