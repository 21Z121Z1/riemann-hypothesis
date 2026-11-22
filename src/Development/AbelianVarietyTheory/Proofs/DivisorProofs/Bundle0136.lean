import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0020
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0032
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstPreorder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleProdOfEtale
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0096
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0022

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCoordinatesDifferentials
section
open scoped TensorProduct Polynomial

namespace GlobalTheory.EtaleCoordRank

open KaehlerDifferential TensorProduct

theorem finrank_and_linearIndependent_D_unit_mul : ∀ (R B K : Type) [CommRing R] [CommRing B] [Field K] [Algebra R B] [Algebra B K] (d : ℕ) (t : Fin d → B), (MvPolynomial.eval₂Hom (algebraMap R B) t).Etale → Module.finrank K (K ⊗[B] Ω[B⁄R]) = d ∧ ∀ (ι : Type) (e : ι ↪ Fin d) (u : ι → Bˣ), (∀ i, algebraMap B K (t (e i)) = 0) → LinearIndependent K (fun i => (1 : K) ⊗ₜ[B] KaehlerDifferential.D R B ((u i : B) * t (e i))) := by
  intro R B K _ _ _ _ _ d t h
  have key : ∃ b : Module.Basis (Fin d) B Ω[B⁄R], ∀ i, b i = D R B (t i) := by
    letI : Algebra (MvPolynomial (Fin d) R) B := (MvPolynomial.eval₂Hom (algebraMap R B) t).toAlgebra
    haveI : IsScalarTower R (MvPolynomial (Fin d) R) B :=
      IsScalarTower.of_algebraMap_eq fun r => by
        change algebraMap R B r = MvPolynomial.eval₂Hom (algebraMap R B) t (MvPolynomial.C r)
        simp
    haveI : Algebra.Etale (MvPolynomial (Fin d) R) B := h
    obtain ⟨⟨b, hb⟩, _⟩ := GlobalTheory.EtaleCoordJacobian.exists_basis_of_etale R B (Fin d)
    refine ⟨b, fun i => ?_⟩
    rw [hb]
    congr 1
    change MvPolynomial.eval₂Hom (algebraMap R B) t (MvPolynomial.X i) = t i
    simp
  obtain ⟨b, hb⟩ := key
  let b' : Module.Basis (Fin d) K (K ⊗[B] Ω[B⁄R]) := b.baseChange K
  refine ⟨by rw [Module.finrank_eq_card_basis b', Fintype.card_fin], ?_⟩
  intro ι e u ht
  have hli : LinearIndependent K (fun i => b' (e i)) := b'.linearIndependent.comp e e.injective
  have hfun : (fun i => (1 : K) ⊗ₜ[B] KaehlerDifferential.D R B ((u i : B) * t (e i))) =
      (fun i => Units.map (algebraMap B K : B →* K) (u i)) • (fun i => b' (e i)) := by
    funext i
    simp only [Pi.smul_apply', Units.smul_def, Units.coe_map, MonoidHom.coe_coe, b',
      Module.Basis.baseChange_apply, hb]
    rw [Derivation.leibniz, tmul_add, tmul_smul, tmul_smul, ← algebraMap_smul K (u i : B),
      ← algebraMap_smul K (t (e i)), ht, zero_smul, add_zero]
  rw [hfun]
  exact hli.units_smul _

end GlobalTheory.EtaleCoordRank
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalRingOfLocalizationStatement
section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_local_ring_of_localization : ∀ (R A E : Type) [CommRing R] [CommRing A] [CommRing E] [Algebra R A] [Algebra.Etale R A] (q : Ideal A) [q.IsPrime] [Algebra (Localization.AtPrime q) E] [Algebra.Etale (Localization.AtPrime q) E] [Algebra R E] [IsScalarTower R (Localization.AtPrime q) E] (P : Ideal E) [P.IsPrime], (∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Localization.AtPrime P)) := by
  first | exact @GlobalTheory.essEtale_atPrime_of_etale_over_atPrime | exact GlobalTheory.essEtale_atPrime_of_etale_over_atPrime | (intros; apply GlobalTheory.essEtale_atPrime_of_etale_over_atPrime <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalizationAtPrimeIsDomainIsIntegrallyClos
section
open IsLocalRing

namespace GlobalTheory

theorem etale_localization_atPrime_isDomain_isIntegrallyClosed :
    ∀ (R A : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CommRing A] [Algebra R A]
      [Algebra.Etale R A] (p : Ideal A) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) := by
  intro R A _ _ _ _ _ _ p _
  exact isDomain_and_isIntegrallyClosed_atPrime_of_etale R p (Localization.AtPrime p)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleMaximalQuotientAlgebraic
section
namespace GlobalTheory

namespace FracAlgEtale

theorem exists_isAlgebraic_ratFunc_of_ringHom (k B : Type) [Field k] [CommRing B]
    [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B] (hB : ¬ IsField B) (f : B)
    (hf : f ≠ 0) (A' : Type) [CommRing A'] [Algebra B A'] [Algebra.Etale B A'] (R : Type)
    [CommRing R] [Algebra A' R] [IsLocalization.Away (algebraMap B A' f) R] (Q : Type)
    [CommRing Q] [Algebra R Q] [IsFractionRing R Q] (K : Type) [Field K] (π : Q →+* K)
    (hπ : Function.Surjective π) :
    ∃ _ : Algebra (RatFunc k) K, Algebra.IsAlgebraic (RatFunc k) K := by
  let ι : R →+* Q := algebraMap R Q
  letI : Algebra B R := ((algebraMap A' R).comp (algebraMap B A')).toAlgebra
  haveI : IsScalarTower B A' R := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : Algebra A' K := (π.comp (ι.comp (algebraMap A' R))).toAlgebra
  letI : Algebra B K := ((algebraMap A' K).comp (algebraMap B A')).toAlgebra
  haveI : IsScalarTower B A' K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let F := FractionRing B

  haveI : Module.Flat A' R := IsLocalization.flat R (Submonoid.powers (algebraMap B A' f))
  haveI : Module.Flat B R := Module.Flat.trans B A' R
  have hreg : ∀ b ∈ nonZeroDivisors B, algebraMap B R b ∈ nonZeroDivisors R := by
    intro b hb
    have hs := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := R) hb
    rw [mem_nonZeroDivisors_iff]
    refine ⟨fun x hx => hs ?_, fun x hx => hs ?_⟩
    · show b • x = b • (0 : R)
      rw [smul_zero, Algebra.smul_def]
      first | exact hx | (rw [mul_comm]; exact hx)
    · show b • x = b • (0 : R)
      rw [smul_zero, Algebra.smul_def]
      first | exact hx | (rw [mul_comm]; exact hx)
  have hunitR : ∀ s ∈ nonZeroDivisors R, IsUnit (π (ι s)) := fun s hs =>
    (IsLocalization.map_units Q (⟨s, hs⟩ : nonZeroDivisors R)).map π
  have hBK : ∀ b : B, algebraMap B K b = π (ι (algebraMap B R b)) := fun b => rfl
  have hunit : ∀ y : nonZeroDivisors B, IsUnit (algebraMap B K y) := fun y => by
    rw [hBK]; exact hunitR _ (hreg _ y.2)
  letI : Algebra F K := (IsLocalization.lift (M := nonZeroDivisors B) (S := F) hunit).toAlgebra
  haveI : IsScalarTower B F K := IsScalarTower.of_algebraMap_eq fun b =>
    (IsLocalization.lift_eq (M := nonZeroDivisors B) (S := F) hunit b).symm

  haveI : Module.Finite F (TensorProduct B F A') := Algebra.FormallyUnramified.finite_of_free F _
  let ψ : TensorProduct B F A' →ₐ[F] K :=
    Algebra.TensorProduct.lift (Algebra.ofId F K) (IsScalarTower.toAlgHom B A' K)
      (fun _ _ => Commute.all _ _)
  have hA : ∀ a : A', IsIntegral F (algebraMap A' K a) := fun a => by
    have h1 := (Algebra.IsIntegral.isIntegral (R := F) ((1 : F) ⊗ₜ[B] a)).map ψ
    simpa [ψ] using h1
  have hAR : ∀ a : A', π (ι (algebraMap A' R a)) = algebraMap A' K a := fun a => rfl
  have hf' : f ∈ nonZeroDivisors B := mem_nonZeroDivisors_of_ne_zero hf
  have hR : ∀ x : R, IsIntegral F (π (ι x)) := by
    intro x
    obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, hx⟩ := IsLocalization.surj (Submonoid.powers (algebraMap B A' f)) x
    have hx' := congrArg (fun y => π (ι y)) hx
    simp only [map_mul, map_pow] at hx'
    have hfK : π (ι (algebraMap A' R (algebraMap B A' f))) = algebraMap F K (algebraMap B F f) := by
      rw [← IsScalarTower.algebraMap_apply B F K]; rfl
    rw [hfK, hAR] at hx'
    have hu : IsUnit (algebraMap F K (algebraMap B F f)) := by
      rw [← IsScalarTower.algebraMap_apply B F K]; exact hunit ⟨f, hf'⟩
    have hne : (algebraMap F K (algebraMap B F f)) ^ n ≠ 0 := pow_ne_zero _ hu.ne_zero
    have : π (ι x) = algebraMap A' K a * ((algebraMap F K (algebraMap B F f)) ^ n)⁻¹ :=
      (eq_mul_inv_iff_mul_eq₀ hne).2 hx'
    rw [this]
    exact (hA a).mul ((isIntegral_algebraMap (R := F) (A := K) (x := algebraMap B F f)).pow n).inv
  have hall : ∀ z : K, IsIntegral F z := by
    intro z
    obtain ⟨q, rfl⟩ := hπ z
    obtain ⟨⟨x, s⟩, hq⟩ := IsLocalization.surj (nonZeroDivisors R) q
    have hq' : π q * π (ι s) = π (ι x) := by
      rw [← map_mul]; exact congrArg π hq
    have : π q = π (ι x) * (π (ι s))⁻¹ := (eq_mul_inv_iff_mul_eq₀ (hunitR _ s.2).ne_zero).2 hq'
    rw [this]
    exact (hR x).mul (hR s).inv
  haveI : Algebra.IsIntegral F K := ⟨hall⟩
  haveI : Algebra.IsAlgebraic F K := inferInstance

  obtain ⟨algRF, hRF⟩ := GlobalTheory.FracAlgDedekind.exists_isAlgebraic_ratFunc k B hB
  letI algK : Algebra (RatFunc k) K := ((algebraMap F K).comp (algebraMap (RatFunc k) F)).toAlgebra
  haveI : IsScalarTower (RatFunc k) F K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact ⟨algK, Algebra.IsAlgebraic.trans (RatFunc k) F K⟩

theorem exists_isAlgebraic_ratFunc_residue : ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], ¬ IsField B → ∀ (f : B), f ≠ 0 → ∀ (A' : Type) [CommRing A'] [Algebra B A'] [Algebra.Etale B A'] (M : MaximalSpectrum (FractionRing (Localization.Away (algebraMap B A' f)))), ∃ _ : Algebra (RatFunc k) (FractionRing (Localization.Away (algebraMap B A' f)) ⧸ M.asIdeal), Algebra.IsAlgebraic (RatFunc k) (FractionRing (Localization.Away (algebraMap B A' f)) ⧸ M.asIdeal) := by
  intro k B _ _ _ _ _ _ hB f hf A' _ _ _ M
  haveI : M.asIdeal.IsMaximal := M.isMaximal
  letI : Field (FractionRing (Localization.Away (algebraMap B A' f)) ⧸ M.asIdeal) :=
    Ideal.Quotient.field M.asIdeal
  exact exists_isAlgebraic_ratFunc_of_ringHom k B hB f hf A' (Localization.Away (algebraMap B A' f))
    (FractionRing (Localization.Away (algebraMap B A' f)))
    (FractionRing (Localization.Away (algebraMap B A' f)) ⧸ M.asIdeal) (Ideal.Quotient.mk M.asIdeal)
    (Ideal.Quotient.mk_surjective (I := M.asIdeal))

end FracAlgEtale

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleNbhdLocalRingToHenselisationAlgebraMap
section
open IsLocalRing GlobalTheory.Henselisation

namespace GlobalTheory.Henselisation

theorem EtNbhd.base_le_all {R : Type} [CommRing R] [IsLocalRing R] (i : EtNbhd R) :
    EtNbhd.base ≤ i := by
  refine ⟨Ideal.Quotient.liftₐ _ (MvPolynomial.aeval (R := R) (S₁ := i.A) Fin.elim0) ?_, ?_⟩
  · intro a ha
    have hcomp : (MvPolynomial.aeval (R := R) (S₁ := i.A) Fin.elim0) =
        (Algebra.ofId R i.A).comp (MvPolynomial.isEmptyAlgEquiv R (Fin 0)).toAlgHom :=
      MvPolynomial.algHom_ext fun x => x.elim0
    have ha' : (MvPolynomial.isEmptyAlgEquiv R (Fin 0)).toAlgHom a = 0 := ha
    exact (DFunLike.congr_fun hcomp a).trans ((congrArg (Algebra.ofId R i.A) ha').trans (map_zero _))
  · exact Ideal.Quotient.algHom_ext R (MvPolynomial.algHom_ext fun x => x.elim0)

theorem Hens.of_algebraMap (R : Type) [CommRing R] [IsLocalRing R] (i : EtNbhd R) (r : R) :
    Hens.of i (algebraMap R i.B r) = algebraMap R (Hens R) r := by
  have h := EtNbhd.base_le_all i
  change Hens.of i (algebraMap R i.B r) = Hens.of EtNbhd.base (algebraMap R EtNbhd.base.B r)
  have e : Hens.of EtNbhd.base (algebraMap R EtNbhd.base.B r) =
      Hens.of i (EtNbhd.trans h (algebraMap R EtNbhd.base.B r)) :=
    (Ring.DirectLimit.of_f (G := fun i : EtNbhd R => i.B) (f := fun _ _ h => ⇑(EtNbhd.trans h)) h _).symm
  rw [e]
  congr 1
  rw [IsScalarTower.algebraMap_apply R (EtNbhd.base (R := R)).A (EtNbhd.base (R := R)).B r, EtNbhd.trans,
    Localization.localRingHom_to_map, RingHom.coe_coe, AlgHom.commutes,
    ← IsScalarTower.algebraMap_apply R i.A i.B r]

end GlobalTheory.Henselisation
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleNbhdLocalRingTransitionMapIsLocalHomInjecti
section
open IsLocalRing GlobalTheory.Henselisation

namespace GlobalTheory.Henselisation

theorem EtNbhd.trans_isLocalHom_injective (R : Type) [CommRing R] [IsLocalRing R] (i j : EtNbhd R)
    (h : i ≤ j) : IsLocalHom (EtNbhd.trans h) ∧ Function.Injective (EtNbhd.trans h) := by
  have hloc : IsLocalHom (EtNbhd.trans h) := by
    unfold EtNbhd.trans
    exact Localization.isLocalHom_localRingHom _ _ _ _
  refine ⟨hloc, ?_⟩
  set f : i.A →ₐ[R] j.A := h.choose with hfdef
  letI : Algebra i.A j.A := (f : i.A →+* j.A).toAlgebra
  haveI : IsScalarTower R i.A j.A := IsScalarTower.of_algebraMap_eq (fun r => (f.commutes r).symm)
  haveI : Algebra.Etale i.A j.A := Algebra.Etale.of_restrictScalars R i.A j.A
  have hflat : (f : i.A →+* j.A).Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  have hB : (EtNbhd.trans h).Flat := RingHom.Flat.localRingHom hflat j.q i.q _
  letI : Algebra i.B j.B := (EtNbhd.trans h).toAlgebra
  haveI : Module.Flat i.B j.B := RingHom.flat_algebraMap_iff.mp hB
  haveI : IsLocalHom (algebraMap i.B j.B) := hloc
  haveI hff : Module.FaithfullyFlat i.B j.B := Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact RingHom.FaithfullyFlat.injective hff

end GlobalTheory.Henselisation
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleOfEtaleAtHeightOnePrimesStatement
section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_of_etale_at_height_one_primes : ∀ (R A : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] [CommRing A] [Algebra R A] [Module.Free R A] [Module.Finite R A], ¬ IsField R → (∀ (p : Ideal R) [p.IsPrime], p.height = 1 → Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) → Algebra.Etale R A := by
  first | exact @GlobalTheory.PurityDisc.etale_of_etale_height_one | exact GlobalTheory.PurityDisc.etale_of_etale_height_one | (intros; apply GlobalTheory.PurityDisc.etale_of_etale_height_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtalePolynomialSubstitutionStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_polynomial_substitution : ∀ {k A R N : Type} [CommRing k] [CommRing A] [CommRing R] (α : k →+* A) (t : A) (f : A →+* R) (n : N → R) {d : ℕ} (e : Fin (d + 1) ≃ Option N), (MvPolynomial.eval₂Hom α (fun _ : Fin 1 => t)).Etale → Function.Bijective (MvPolynomial.eval₂Hom f n) → (MvPolynomial.eval₂Hom (f.comp α) (fun j => (e j).elim (f t) n)).Etale := by
  first | exact @GlobalTheory.etale_eval₂Hom_option_of_bijective | exact GlobalTheory.etale_eval₂Hom_option_of_bijective | (intros; apply GlobalTheory.etale_eval₂Hom_option_of_bijective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleProdOfEtaleStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_prod_of_etale : ∀ (B A₁ A₂ : Type) [CommRing B] [CommRing A₁] [CommRing A₂] [Algebra B A₁] [Algebra B A₂], Algebra.Etale B A₁ → Algebra.Etale B A₂ → Algebra.Etale B (A₁ × A₂) := by
  first | (exact @GlobalTheory.etale_prod) | (exact GlobalTheory.etale_prod) | (intros; apply GlobalTheory.etale_prod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleUniquePrimeLeMapMaximalStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_unique_prime_le_map_maximal : ∀ (B A : Type) [CommRing B] [CommRing A] [Algebra B A] [Algebra.Etale B A] (P : Ideal B), P.IsMaximal → ∀ (Q : Ideal A), (∀ Q' : Ideal A, Q'.IsPrime → P.map (algebraMap B A) ≤ Q' → Q' = Q) → Q ≤ P.map (algebraMap B A) := by
  first | (exact @GlobalTheory.etale_prime_le_map_of_unique) | (exact GlobalTheory.etale_prime_le_map_of_unique) | (intros; apply GlobalTheory.etale_prime_le_map_of_unique <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsActionFactorThroughTensorCharacter
section
open scoped TensorProduct

namespace GlobalTheory

theorem tensor_action_factors (k : Type) [Field k] (C O B : Type) [CommRing C] [Ring O] [Algebra C O]
    [Algebra C k] [Ring B] [Algebra k B] (e : (k ⊗[C] O) ≃ₐ[k] B) (X : Type) [AddCommGroup X]
    [Module k X] (σX : O →+* Module.End k X)
    (hσ : ∀ c, σX (algebraMap C O c) = algebraMap C k c • 1) :
    ∃ ρX : B →ₐ[k] Module.End k X, ∀ o, ρX (e (1 ⊗ₜ[C] o)) = σX o := by
  letI : Algebra C (Module.End k X) :=
    ((algebraMap k (Module.End k X)).comp (algebraMap C k)).toAlgebra'
      (fun c f => Algebra.commutes (algebraMap C k c) f)
  haveI : IsScalarTower C k (Module.End k X) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let g : O →ₐ[C] Module.End k X :=
    { σX with
      commutes' := fun c => by
        change σX (algebraMap C O c) = algebraMap k (Module.End k X) (algebraMap C k c)
        rw [hσ]; exact (Algebra.algebraMap_eq_smul_one _).symm }
  let F : (k ⊗[C] O) →ₐ[k] Module.End k X :=
    Algebra.TensorProduct.lift (Algebra.ofId k (Module.End k X)) g
      (fun x y => Algebra.commutes x (g y))
  refine ⟨F.comp e.symm.toAlgHom, fun o => ?_⟩
  show F (e.symm (e (1 ⊗ₜ[C] o))) = σX o
  rw [e.symm_apply_apply]
  rw [show F (1 ⊗ₜ[C] o) = Algebra.ofId k (Module.End k X) 1 * g o from
    Algebra.TensorProduct.lift_tmul _ _ _ _ _, map_one, one_mul]
  rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmissibleLagrangianTransverseFieldStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_admissible_lagrangian_transverse_field : ∀ {k : Type} [Field k] (c : k →+* k), (∀ x, c (c x) = x) → (2 : k) ≠ 0 →
    ∀ {n : ℕ} (S : Matrix (Fin n) (Fin n) k), IsUnit S.det → Sᵀ = -S.map c →
    ∀ (A C : Matrix (Fin n) (Fin n) k), (∀ u : Fin n → k, A *ᵥ u = 0 → C *ᵥ u = 0 → u = 0) →
      Aᵀ * S * C.map c + Cᵀ * S * A.map c = 0 →
      ∃ X : Matrix (Fin n) (Fin n) k, Xᵀ * S + S * X.map c = 0 ∧ IsUnit (A + X * C).det := by
  first | exact @GlobalTheory.lagrangian_transverse_field | exact GlobalTheory.lagrangian_transverse_field | (intros; apply GlobalTheory.lagrangian_transverse_field <;> assumption)
end

