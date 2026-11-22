import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRetractionMulP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvEqOneOfForallPairing
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0235
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0249
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0304
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0325
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0316
import GroundTheory.ArithmeticGeometry.SchemeCohomology.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.IsPrecompleteOfBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0317
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreMemInducedSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0296
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothContragredientIrreducibleAndReflexive

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulPowFibreRankEqPDivGroup
section
open CategoryTheory Coalgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.HTPair
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.PDivGroup

theorem exists_mulPow_fibreRank_eq (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O]
    (G : PDivGroup p O) (k m : ℕ) :
    ∃ (r : G.A (k + m) →ₐc[O] G.A k) (μ : G.A k →ₐc[O] G.A (k + m)), Function.Surjective r ∧
      RingHom.ker r = torsionIdeal O (G.A (k + m)) (p ^ k) ∧
      (∀ a, μ (r a) = mulBy O (G.A (k + m)) (p ^ m) a) ∧
      ∀ q, fibreRank (μ : G.A k →ₐ[O] G.A (k + m)).toLinearMap q = fibreDim (G.A k) q := by
  obtain ⟨r, hr, hk⟩ := G.exists_res_le (m := k) (n := k + m) (by omega)
  have hle : RingHom.ker r ≤ RingHom.ker (mulBy O (G.A (k + m)) (p ^ m)) := by
    rw [hk]
    refine (kerIdeal_le_ker_iff _
      (mulBy O (G.A (k + m)) (p ^ m) : G.A (k + m) →ₐ[O] G.A (k + m))).2 fun c => ?_
    change mulBy O _ (p ^ m) (mulBy O _ (p ^ k) c) = _
    rw [mulBy_mulBy, ← pow_add, add_comm m k, mulBy_pow_self]
  let μ := liftSurj r hr (mulBy O (G.A (k + m)) (p ^ m)) hle
  have hμ : ∀ a, μ (r a) = mulBy O (G.A (k + m)) (p ^ m) a := liftSurj_apply r hr _ hle
  refine ⟨r, μ, hr, hk, hμ, fun q => ?_⟩
  obtain ⟨f, hf, hfk⟩ := G.exists_res_le (m := m) (n := k + m) (by omega)
  have hker : kerIdeal μ = RingHom.ker (f : G.A (k + m) →ₐ[O] G.A m) := by
    rw [← kerIdeal_comp_of_surjective μ hr, show μ.comp r = mulBy O (G.A (k + m)) (p ^ m) from
      BialgHom.ext hμ]
    exact hfk.symm
  have h1 := fibreDim_eq_ker_mul_range μ q
  rw [hker, fibreDim_congr (Ideal.quotientKerAlgEquivOfSurjective
    (f := (f : G.A (k + m) →ₐ[O] G.A m)) hf).toLinearEquiv, fibreDim_eq, fibreDim_eq,
    add_mul, pow_add, mul_comm (p ^ (k * G.height))] at h1
  rw [fibreDim_eq]
  have hp : 0 < p ^ (m * G.height) := pow_pos (Fact.out : p.Prime).pos _
  exact (Nat.eq_of_mul_eq_mul_left hp h1).symm

end GlobalTheory.PDivGroup
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroLinearCombinationMemCommonKernel
section
open GlobalTheory.Nef

namespace GlobalTheory

theorem exists_ne_zero_comb_mem_ker :
    ∀ (k F ι : Type) [Field k] [Field F] [Algebra k F] (n m : ℕ) (f : Fin m → F),
  LinearIndependent k f → ∀ (S : Finset ι) (N : ι → ℕ) (ψ : ∀ v, (Fin n → F) →ₗ[k] (Fin (N v) → k)),
    ∑ v ∈ S, N v < n * m → ∃ c : Fin n → Fin m → k, (fun i => ∑ j, c i j • f j) ≠ 0 ∧
      ∀ v ∈ S, ψ v (fun i => ∑ j, c i j • f j) = 0 := by
  intro k F ι _ _ _ n m f hf S N ψ hlt
  let T : (Fin n → Fin m → k) →ₗ[k] (Fin n → F) :=
    { toFun := fun c i => ∑ j, c i j • f j
      map_add' := by
        intro a b; funext i; simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro r a; funext i; simp [Finset.smul_sum, smul_smul] }
  have hT : ∀ c, T c = fun i => ∑ j, c i j • f j := fun c => rfl
  let Ψ : (Fin n → Fin m → k) →ₗ[k] ((v : S) → Fin (N v) → k) :=
    LinearMap.pi fun v => (ψ v).comp T
  have hlt' : Module.finrank k ((v : S) → Fin (N v) → k) < Module.finrank k (Fin n → Fin m → k) := by
    rw [Module.finrank_pi_fintype]
    simp only [Module.finrank_fin_fun]
    rw [Finset.sum_coe_sort S (fun v => N v), Module.finrank_pi_fintype]
    simpa [Module.finrank_fin_fun] using hlt
  have hk : LinearMap.ker Ψ ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt hlt'
  obtain ⟨c, hc, hc0⟩ := (Submodule.ne_bot_iff _).1 hk
  refine ⟨c, ?_, ?_⟩
  · intro h0
    apply hc0
    funext i j
    have hi : ∑ j, c i j • f j = 0 := congrFun h0 i
    exact Fintype.linearIndependent_iff.1 hf (c i) hi j
  · intro v hv
    have := congrFun (LinearMap.mem_ker.1 hc) ⟨v, hv⟩
    simpa [Ψ, hT] using this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalLocalBetween
section
open IsLocalRing Polynomial

noncomputable section
namespace GlobalTheory.LocAcycEmbed

theorem exists_eq_of_aeval_eq_zero {T K : Type} [CommRing T] [IsDomain T] [Field K] [Algebra T K]
    (hT : GlobalTheory.LocAcyc.AbsIntClosed T) :
    ∀ (n : ℕ) (f : T[X]), f.Monic → f.natDegree = n → ∀ x : K, aeval x f = 0 →
      ∃ t : T, algebraMap T K t = x := by
  intro n
  induction n with
  | zero =>
    intro f hf hn x hx
    have h1 : f = 1 := Polynomial.eq_one_of_monic_natDegree_zero hf hn
    subst h1
    simp at hx
  | succ n ih =>
    intro f hf hn x hx
    obtain ⟨r, hr⟩ := hT f hf (by omega)
    have hfg : (X - C r) * (f /ₘ (X - C r)) = f := mul_divByMonic_eq_iff_isRoot.2 hr
    have hg : (f /ₘ (X - C r)).Monic := by
      apply Polynomial.Monic.of_mul_monic_left (monic_X_sub_C r)
      rw [hfg]; exact hf
    have hgn : (f /ₘ (X - C r)).natDegree = n := by
      have := Polynomial.Monic.natDegree_mul (monic_X_sub_C r) hg
      rw [hfg, natDegree_X_sub_C] at this
      omega
    rw [← hfg, map_mul] at hx
    rcases mul_eq_zero.1 hx with h | h
    · refine ⟨r, ?_⟩
      simp at h
      rw [sub_eq_zero] at h
      exact h.symm
    · exact ih _ hg hgn x h

theorem isIntegrallyClosed_of_absIntClosed (T : Type) [CommRing T] [IsDomain T]
    (hT : GlobalTheory.LocAcyc.AbsIntClosed T) : IsIntegrallyClosed T := by
  rw [isIntegrallyClosed_iff (FractionRing T)]
  intro x hx
  obtain ⟨f, hf, h⟩ := hx
  exact exists_eq_of_aeval_eq_zero hT _ f hf rfl x (by rw [aeval_def]; exact h)

theorem isAlgClosed_fractionRing (T : Type) [CommRing T] [IsDomain T]
    (hT : GlobalTheory.LocAcyc.AbsIntClosed T) : IsAlgClosed (FractionRing T) := by
  first
  | exact @_root_.GlobalTheory.MonicRootRange.isAlgClosed_fractionRing
  | exact _root_.GlobalTheory.MonicRootRange.isAlgClosed_fractionRing
  | (apply _root_.GlobalTheory.MonicRootRange.isAlgClosed_fractionRing <;> assumption)
  | (intros; apply _root_.GlobalTheory.MonicRootRange.isAlgClosed_fractionRing <;> assumption)
  | (intros; apply @_root_.GlobalTheory.MonicRootRange.isAlgClosed_fractionRing <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.MonicRootRange.isAlgClosed_fractionRing ..)

end GlobalTheory.LocAcycEmbed

namespace GlobalTheory.LocAcycEmbed

theorem essFiniteType_int_of_finite_localization {A C A₁ : Type} [CommRing A] [CommRing C] [CommRing A₁]
    [Algebra A C] [Algebra C A₁] [Algebra.EssFiniteType ℤ A] [Module.Finite A C] (M : Submonoid C)
    [IsLocalization M A₁] : Algebra.EssFiniteType ℤ A₁ := by
  haveI : IsScalarTower ℤ A C := IsScalarTower.of_algebraMap_eq (fun x => by
    rw [eq_intCast (algebraMap ℤ C), eq_intCast (algebraMap ℤ A), map_intCast])
  haveI : IsScalarTower ℤ C A₁ := IsScalarTower.of_algebraMap_eq (fun x => by
    rw [eq_intCast (algebraMap ℤ A₁), eq_intCast (algebraMap ℤ C), map_intCast])
  haveI : Algebra.EssFiniteType A C := Algebra.EssFiniteType.of_finiteType A C
  haveI : Algebra.EssFiniteType C A₁ := Algebra.EssFiniteType.of_isLocalization A₁ M
  haveI : Algebra.EssFiniteType ℤ C := Algebra.EssFiniteType.comp ℤ A C
  exact Algebra.EssFiniteType.comp ℤ C A₁

theorem exists_fractionRing_hom {C A₁ : Type} [CommRing C] [IsDomain C] [CommRing A₁] [IsDomain A₁]
    [Algebra C A₁] (L : Type) [Field L] [Algebra C L] [IsFractionRing C L]
    (hinj : Function.Injective (algebraMap C A₁)) :
    ∃ κ : L →+* FractionRing A₁,
      κ.comp (algebraMap C L) = (algebraMap A₁ (FractionRing A₁)).comp (algebraMap C A₁) := by
  have hg : Function.Injective ((algebraMap A₁ (FractionRing A₁)).comp (algebraMap C A₁)) :=
    (IsFractionRing.injective A₁ (FractionRing A₁)).comp hinj
  refine ⟨IsFractionRing.lift (A := C) (K := L) hg, ?_⟩
  exact IsLocalization.lift_comp _

end GlobalTheory.LocAcycEmbed

namespace GlobalTheory.LocAcycEmbed

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem exists_normal_local_between : ∀ (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A] (i : A →+* T), Function.Injective i →
    ∀ (L : Type) [Field L] [Algebra (FractionRing A) L] [FiniteDimensional (FractionRing A) L]
      [Algebra.IsSeparable (FractionRing A) L],
    ∃ (A₁ : Type) (_ : CommRing A₁) (_ : IsDomain A₁) (_ : IsLocalRing A₁) (_ : IsNoetherianRing A₁)
      (_ : IsIntegrallyClosed A₁) (_ : Algebra.EssFiniteType ℤ A₁) (j : A →+* A₁) (i₁ : A₁ →+* T),
      Function.Injective j ∧ Function.Injective i₁ ∧ IsLocalHom i₁ ∧ i₁.comp j = i ∧
      ∃ κ : L →+* FractionRing A₁,
        κ.comp ((algebraMap (FractionRing A) L).comp (algebraMap A (FractionRing A))) =
          (algebraMap A₁ (FractionRing A₁)).comp j := by
  intro T _ _ _ hT A _ _ _ _ _ _ i hi L _ _ _ _
  haveI : IsIntegrallyClosed T := isIntegrallyClosed_of_absIntClosed T hT
  haveI : IsAlgClosed (FractionRing T) := isAlgClosed_fractionRing T hT
  have hgi : Function.Injective ((algebraMap T (FractionRing T)).comp i) :=
    (IsFractionRing.injective T (FractionRing T)).comp hi
  let φ : FractionRing A →+* FractionRing T := IsFractionRing.lift hgi
  letI : Algebra (FractionRing A) (FractionRing T) := φ.toAlgebra
  let σ : L →ₐ[FractionRing A] FractionRing T := IsAlgClosed.lift
  letI : Algebra A L := ((algebraMap (FractionRing A) L).comp (algebraMap A (FractionRing A))).toAlgebra
  haveI : IsScalarTower A (FractionRing A) L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hAL : Function.Injective (algebraMap A L) :=
    (algebraMap (FractionRing A) L).injective.comp (IsFractionRing.injective A (FractionRing A))
  have h1 : (algebraMap T (FractionRing T)).comp i = (σ : L →+* FractionRing T).comp (algebraMap A L) := by
    ext a
    show algebraMap T (FractionRing T) (i a) = σ (algebraMap (FractionRing A) L (algebraMap A (FractionRing A) a))
    rw [σ.commutes]
    show _ = φ (algebraMap A (FractionRing A) a)
    rw [IsFractionRing.lift_algebraMap]
    rfl
  let C := integralClosure A L
  haveI : Module.Finite A C := IsIntegralClosure.finite A (FractionRing A) L C
  haveI : IsNoetherianRing C := IsNoetherianRing.of_finite A C
  haveI : IsFractionRing C L := integralClosure.isFractionRing_of_finite_extension (FractionRing A) L
  haveI : IsIntegrallyClosed C := integralClosure.isIntegrallyClosedOfFiniteExtension (FractionRing A)
  have hint : ∀ x : C, ∃ t : T, algebraMap T (FractionRing T) t = σ (x : L) := by
    intro x
    obtain ⟨f, hf, hfx⟩ := x.2
    apply exists_eq_of_aeval_eq_zero hT _ (f.map i) (hf.map i) rfl
    rw [aeval_def, eval₂_map, h1]
    have := Polynomial.hom_eval₂ f (algebraMap A L) (σ : L →+* FractionRing T) (x : L)
    rw [hfx, map_zero] at this
    exact this.symm
  choose ct hct using hint
  have hinjT := IsFractionRing.injective T (FractionRing T)
  let c : C →+* T :=
    { toFun := ct
      map_one' := hinjT (by rw [hct]; simp)
      map_mul' := fun x y => hinjT (by rw [hct, map_mul, hct, hct]; simp)
      map_zero' := hinjT (by rw [hct]; simp)
      map_add' := fun x y => hinjT (by rw [hct, map_add, hct, hct]; simp) }
  have hc : ∀ x, algebraMap T (FractionRing T) (c x) = σ (x : L) := hct
  have hcinj : Function.Injective c := by
    intro x y h
    have := congrArg (algebraMap T (FractionRing T)) h
    rw [hc, hc] at this
    exact Subtype.ext ((σ : L →+* FractionRing T).injective this)
  have hci : c.comp (algebraMap A C) = i := by
    ext a
    apply hinjT
    rw [RingHom.comp_apply, hc]
    exact (RingHom.congr_fun h1 a).symm
  let P : Ideal C := (maximalIdeal T).comap c
  haveI : P.IsPrime := Ideal.comap_isPrime c _
  have hunit : ∀ y : P.primeCompl, IsUnit (c y) := fun y => by
    by_contra h
    exact y.2 ((IsLocalRing.mem_maximalIdeal _).2 h)
  let i₁ : Localization.AtPrime P →+* T := IsLocalization.lift hunit
  let j : A →+* Localization.AtPrime P := (algebraMap C (Localization.AtPrime P)).comp (algebraMap A C)
  have hAC : Function.Injective (algebraMap A C) := fun x y h => hAL (congrArg Subtype.val h)
  have hCA₁ : Function.Injective (algebraMap C (Localization.AtPrime P)) :=
    IsLocalization.injective (Localization.AtPrime P) (Ideal.primeCompl_le_nonZeroDivisors P)
  have hj : Function.Injective j := hCA₁.comp hAC
  have hi₁ : Function.Injective i₁ :=
    (IsLocalization.lift_injective_iff hunit).2 fun x y =>
      ⟨fun h => congrArg c (hCA₁ h), fun h => congrArg _ (hcinj h)⟩
  have hloc : IsLocalHom i₁ := by
    refine ⟨fun x hx => ?_⟩
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (S := Localization.AtPrime P) P.primeCompl x
    have e1 := IsLocalization.mk'_spec (Localization.AtPrime P) a s
    have e2 : IsUnit (c a) := by
      rw [← IsLocalization.lift_eq (S := Localization.AtPrime P) hunit a, ← e1, map_mul, IsLocalization.lift_eq (S := Localization.AtPrime P) hunit]
      exact hx.mul (hunit s)
    have ha : a ∈ P.primeCompl := fun h => ((IsLocalRing.mem_maximalIdeal _).1 h) e2
    exact isUnit_of_mul_isUnit_left (e1 ▸ IsLocalization.map_units (Localization.AtPrime P) ⟨a, ha⟩)
  have hcomp : i₁.comp j = i := by
    ext a
    show i₁ (algebraMap C _ (algebraMap A C a)) = i a
    rw [IsLocalization.lift_eq]
    exact RingHom.congr_fun hci a
  haveI : IsDomain (Localization.AtPrime P) :=
    IsLocalization.isDomain_localization (Ideal.primeCompl_le_nonZeroDivisors P)
  haveI : IsIntegrallyClosed (Localization.AtPrime P) :=
    isIntegrallyClosed_of_isLocalization _ P.primeCompl (Ideal.primeCompl_le_nonZeroDivisors P)
  obtain ⟨κ, hκ⟩ := exists_fractionRing_hom (A₁ := Localization.AtPrime P) L hCA₁
  refine ⟨Localization.AtPrime P, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    essFiniteType_int_of_finite_localization (A := A) (C := C) P.primeCompl, j, i₁, hj, hi₁, hloc, hcomp, κ, ?_⟩
  ext a
  exact RingHom.congr_fun hκ (algebraMap A C a)

end GlobalTheory.LocAcycEmbed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointAlgClosureResidueFieldOfIntegralSurje
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory

theorem exists_ringHom_algClosure_residueField_of_isIntegral (A B : Type) [CommRing A]
    [IsLocalRing A] [CommRing B] (φ : A →+* B) (hφ : φ.IsIntegral) (P : Ideal B) [P.IsPrime]
    (hP : P.comap φ = IsLocalRing.maximalIdeal A) :
    ∃ ψ : B →+* AlgebraicClosure (IsLocalRing.ResidueField A),
      ψ.comp φ = algebraMap A (AlgebraicClosure (IsLocalRing.ResidueField A)) := by
  letI : Algebra A B := φ.toAlgebra
  haveI : Algebra.IsIntegral A B := ⟨hφ⟩
  haveI : P.LiesOver (IsLocalRing.maximalIdeal A) := ⟨hP.symm⟩
  letI : Algebra (IsLocalRing.ResidueField A) (B ⧸ P) :=
    Ideal.Quotient.algebraOfLiesOver P (IsLocalRing.maximalIdeal A)
  haveI : IsScalarTower A (IsLocalRing.ResidueField A) (B ⧸ P) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.IsIntegral A (B ⧸ P) := inferInstance
  haveI : Algebra.IsIntegral (IsLocalRing.ResidueField A) (B ⧸ P) :=
    Algebra.IsIntegral.tower_top (R := A)
  let l : (B ⧸ P) →ₐ[IsLocalRing.ResidueField A] AlgebraicClosure (IsLocalRing.ResidueField A) :=
    IsAlgClosed.lift
  refine ⟨l.toRingHom.comp (Ideal.Quotient.mk P), ?_⟩
  ext a
  have h := l.commutes (algebraMap A (IsLocalRing.ResidueField A) a)
  rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at h
  exact h

theorem exists_point_algClosure_residueField_of_isIntegralHom :
    ∀ (A : Type) [CommRing A] [IsLocalRing A] (Y : Scheme.{0}) (g : Y ⟶ Spec (CommRingCat.of A)),
    IsIntegralHom g → Surjective g → ∃ s : Spec (CommRingCat.of (AlgebraicClosure (IsLocalRing.ResidueField A))) ⟶ Y,
    s ≫ g = Spec.map (CommRingCat.ofHom (algebraMap A (AlgebraicClosure (IsLocalRing.ResidueField A)))) := by
  intro A _ _ Y g hi hs
  haveI : IsAffine Y := isAffine_of_isAffineHom g
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (Y.isoSpec.inv ≫ g)
  have h1 : IsIntegralHom (Spec.map φ) := by rw [hφ]; infer_instance
  have h2 : Surjective (Spec.map φ) := by rw [hφ]; infer_instance
  have h3 : φ.hom.IsIntegral := IsIntegralHom.SpecMap_iff.mp h1
  obtain ⟨P, hP⟩ := h2.surj (IsLocalRing.closedPoint A)
  have hP' : (PrimeSpectrum.asIdeal P).comap φ.hom = IsLocalRing.maximalIdeal A :=
    congrArg PrimeSpectrum.asIdeal hP
  haveI := PrimeSpectrum.isPrime P
  obtain ⟨ψ, hψ⟩ := exists_ringHom_algClosure_residueField_of_isIntegral A Γ(Y, ⊤) φ.hom h3
    (PrimeSpectrum.asIdeal P) hP'
  refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ Y.isoSpec.inv, ?_⟩
  rw [Category.assoc, ← hφ, ← Spec.map_comp, ← hψ]
  rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPreservesFilteredColimitsIsoOnFiniteTypeStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_preservesFilteredColimits_iso_on_finiteType : ∀ (𝒜 : Type 2) [Category.{1} 𝒜] [HasColimitsOfSize.{1, 1} 𝒜] (M : CommRingCat.{0} ⥤ 𝒜), ∃ (N : CommRingCat.{0} ⥤ 𝒜) (ε : N ⟶ M), PreservesFilteredColimitsOfSize.{0, 0} N ∧ ∀ A : CommRingCat.{0}, Algebra.FiniteType ℤ A → IsIso (ε.app A) := by
  first
  | exact @GlobalTheory.FinExt.exists_preservesFilteredColimits_isIso
  | exact GlobalTheory.FinExt.exists_preservesFilteredColimits_isIso
  | (intros; apply GlobalTheory.FinExt.exists_preservesFilteredColimits_isIso <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRegularLocalExtensionWithSimpleRoot
section
open IsLocalRing Polynomial

namespace GlobalTheory.MonicRootExtension

section
variable {A : Type} [CommRing A] [IsLocalRing A] (M : A[X]) (hM : M.Monic)
  (hirr : Irreducible (M.map (residue A)))

include hM hirr

theorem map_maximalIdeal_isMaximal :
    ((maximalIdeal A).map (algebraMap A (AdjoinRoot M))).IsMaximal := by
  haveI : Fact (Irreducible (M.map (residue A))) := ⟨hirr⟩
  have hR : IsField (AdjoinRoot (M.map (residue A))) := Field.toIsField _
  rw [AdjoinRoot.algebraMap_eq]
  exact Ideal.Quotient.maximal_of_isField _
    (MulEquiv.isField hR (AdjoinRoot.quotEquivQuotMap M (maximalIdeal A)).toRingEquiv.toMulEquiv)

theorem isLocalRing : IsLocalRing (AdjoinRoot M) := by
  have : Module.Finite A (AdjoinRoot M) := .of_basis (AdjoinRoot.powerBasis' hM).basis
  refine IsLocalRing.of_unique_max_ideal ⟨_, map_maximalIdeal_isMaximal M hM hirr, fun P hP => ?_⟩
  have hc : (P.comap (algebraMap A (AdjoinRoot M))).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P
  have h1 : P.comap (algebraMap A (AdjoinRoot M)) = maximalIdeal A := IsLocalRing.eq_maximalIdeal hc
  have hle : (maximalIdeal A).map (algebraMap A (AdjoinRoot M)) ≤ P :=
    Ideal.map_le_iff_le_comap.2 h1.ge
  exact ((map_maximalIdeal_isMaximal M hM hirr).eq_of_le hP.ne_top hle).symm

theorem maximalIdeal_eq [IsLocalRing (AdjoinRoot M)] :
    (maximalIdeal A).map (algebraMap A (AdjoinRoot M)) = maximalIdeal (AdjoinRoot M) :=
  IsLocalRing.eq_maximalIdeal (map_maximalIdeal_isMaximal M hM hirr)

theorem isLocalHom [IsLocalRing (AdjoinRoot M)] : IsLocalHom (algebraMap A (AdjoinRoot M)) := by
  constructor
  intro x hx
  by_contra h
  have h2 : algebraMap A (AdjoinRoot M) x ∈ maximalIdeal (AdjoinRoot M) := by
    rw [← maximalIdeal_eq M hM hirr]; exact Ideal.mem_map_of_mem _ h
  exact h2 hx

end

section
variable {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  (M : A[X]) (hM : M.Monic) (hirr : Irreducible (M.map (residue A)))
include hM hirr

theorem isAdicComplete [IsLocalRing (AdjoinRoot M)] [IsAdicComplete (maximalIdeal A) A] :
    IsAdicComplete (maximalIdeal (AdjoinRoot M)) (AdjoinRoot M) := by
  have : Module.Finite A (AdjoinRoot M) := .of_basis (AdjoinRoot.powerBasis' hM).basis
  rw [← maximalIdeal_eq M hM hirr, IsAdicComplete.map_algebraMap_iff]
  haveI : IsPrecomplete (maximalIdeal A) (AdjoinRoot M) :=
    ReciprocityTheory.ChartRestriction.G.Semi.Nb.isPrecomplete_of_basis _ (AdjoinRoot.powerBasis' hM).basis
  exact { toIsHausdorff := inferInstance, toIsPrecomplete := inferInstance }

end

theorem exists_extension : ∀ (A Ω : Type) [CommRing A] [IsRegularLocalRing A] [Field Ω]
    (u : A →+* Ω) (p : Polynomial A) (α : Ω),
    RingHom.ker u = maximalIdeal A → IsAdicComplete (maximalIdeal A) A → p.Monic →
    (p.map u).eval α = 0 → (p.map u).derivative.eval α ≠ 0 →
    ∃ (E : Type) (_ : CommRing E) (_ : IsRegularLocalRing E) (a : A →+* E) (v : E →+* Ω),
      a.Flat ∧ (maximalIdeal A).map a = maximalIdeal E ∧ IsAdicComplete (maximalIdeal E) E ∧
      RingHom.ker v = maximalIdeal E ∧ v.comp a = u ∧ α ∈ v.range := by
  intro A Ω _ _ _ u p α hker hcpl hp hroot _

  let ub : ResidueField A →+* Ω := Ideal.Quotient.lift (maximalIdeal A) u
    (fun x hx => (RingHom.mem_ker).1 (hker ▸ hx))
  have hub : ∀ x, ub (residue A x) = u x := fun x => rfl
  letI : Algebra (ResidueField A) Ω := ub.toAlgebra
  have hpu : p.map u = (p.map (residue A)).map ub := by
    rw [Polynomial.map_map]; congr 1
  have hint : IsIntegral (ResidueField A) α := by
    refine ⟨p.map (residue A), hp.map _, ?_⟩
    rw [← Polynomial.eval_map]; change eval α ((p.map (residue A)).map ub) = 0
    rw [← hpu]; exact hroot
  set m := minpoly (ResidueField A) α
  obtain ⟨q, hq⟩ := Polynomial.map_surjective _ (residue_surjective (R := A)) m
  obtain ⟨M, hMm, -, hM⟩ := lifts_and_natDegree_eq_and_monic ((mem_lifts _).2 ⟨q, hq⟩)
    (minpoly.monic hint)
  have hirr : Irreducible (M.map (residue A)) := hMm ▸ minpoly.irreducible hint
  haveI := isLocalRing M hM hirr
  haveI : Module.Finite A (AdjoinRoot M) := .of_basis (AdjoinRoot.powerBasis' hM).basis
  haveI : Module.Free A (AdjoinRoot M) := .of_basis (AdjoinRoot.powerBasis' hM).basis
  haveI : IsNoetherianRing (AdjoinRoot M) := isNoetherian_of_tower A inferInstance
  haveI := isLocalHom M hM hirr
  haveI : IsRegularLocalRing (AdjoinRoot M) :=
    GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.of_flat_of_map_maximalIdeal (maximalIdeal_eq M hM hirr)
  have hev : M.eval₂ u α = 0 := by
    have h1 : M.eval₂ u α = (M.map (residue A)).eval₂ ub α := by
      rw [Polynomial.eval₂_map]; rfl
    rw [h1, hMm]; exact minpoly.aeval (ResidueField A) α
  let v : AdjoinRoot M →+* Ω := AdjoinRoot.lift u α hev
  have hva : v.comp (algebraMap A (AdjoinRoot M)) = u := by
    ext x; simp [v, AdjoinRoot.algebraMap_eq]
  refine ⟨AdjoinRoot M, inferInstance, inferInstance, algebraMap A (AdjoinRoot M), v, ?_,
    maximalIdeal_eq M hM hirr, isAdicComplete M hM hirr, ?_, hva, ⟨AdjoinRoot.root M, by simp [v]⟩⟩
  · rw [RingHom.flat_algebraMap_iff]; infer_instance
  · apply le_antisymm
    · exact IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top v)
    · rw [← maximalIdeal_eq M hM hirr, Ideal.map_le_iff_le_comap]
      intro x hx
      rw [Ideal.mem_comap, RingHom.mem_ker, ← RingHom.comp_apply, hva, ← RingHom.mem_ker, hker]
      exact hx

end GlobalTheory.MonicRootExtension
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingHomPadicAlgClNeZeroStatement
section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ringHom_padicAlgCl_ne_zero' : ∀ (B : Type) [CommRing B] [IsDomain B] [IsLocalRing B] [IsNoetherianRing B] [CharZero B], Finite (ResidueField B) → ∀ h : B, h ≠ 0 → ∃ (p : ℕ) (_ : Fact p.Prime) (χ : B →+* PadicAlgCl p), (∀ b, ‖χ b‖ ≤ 1) ∧ (∀ b ∈ maximalIdeal B, ‖χ b‖ < 1) ∧ χ h ≠ 0 := by
  first | exact @GlobalTheory.CurvePoint.exists_ringHom_padicAlgCl_ne_zero | exact GlobalTheory.CurvePoint.exists_ringHom_padicAlgCl_ne_zero | (intros; apply GlobalTheory.CurvePoint.exists_ringHom_padicAlgCl_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareZeroLiftBasicOpenPairAgreeStatement
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_squareZeroLift_basicOpen_pair_agree : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ →
    ∀ (X : Over (Sp R)), Smooth X.hom → ∀ g₀ : Sp R₀ ⟶ X.left, g₀ ≫ X.hom = spMap π →
    ∀ (a b : R) (V : X.left.Opens), IsAffineOpen V →
    ∀ (ea : Sp (Localization.Away a) ⟶ X.left), ea ≫ X.hom = spMap (algebraMap R (Localization.Away a)) →
      spMap (Localization.awayMap π a) ≫ ea = spMap (algebraMap R₀ (Localization.Away (π a))) ≫ g₀ → ea ⁻¹ᵁ V = ⊤ →
    ∀ (eb : Sp (Localization.Away b) ⟶ X.left), eb ≫ X.hom = spMap (algebraMap R (Localization.Away b)) →
      spMap (Localization.awayMap π b) ≫ eb = spMap (algebraMap R₀ (Localization.Away (π b))) ≫ g₀ →
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∃ t : Sp (Localization.Away a) ⟶ X.left,
      t ≫ X.hom = spMap (algebraMap R (Localization.Away a)) ∧
      spMap (Localization.awayMap π a) ≫ t = spMap (algebraMap R₀ (Localization.Away (π a))) ≫ g₀ ∧ t ⁻¹ᵁ V = ⊤ ∧
      GlobalTheory.SecGlue.IsCombIn V
        (spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (a * b)) a b) ≫ ea)
        (spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (a * b)) a b) ≫ t)
        ![spMap (IsLocalization.Away.awayToAwayLeft (P := Localization.Away (a * b)) b a) ≫ eb]
        ![algebraMap R (Localization.Away (a * b)) b ^ N] := by
  first | exact @GlobalTheory.SecGlue.exists_pair_lift_comb | exact GlobalTheory.SecGlue.exists_pair_lift_comb | (intros; apply GlobalTheory.SecGlue.exists_pair_lift_comb <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreMemInducedSpaceStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_mem_induced_space : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (a b : ℕ) (ν β : kˣ →* ℂˣ) (Φ : Matrix (Fin a) (Fin (a + b)) k → ℂ), GlobalTheory.RankFibre.fibre ν β a b Φ ∈ GlobalTheory.PRep.indSpace (GlobalTheory.SmGL.parab k (GlobalTheory.RankFibre.blocks a b)) (GlobalTheory.SmGL.ofChar (GlobalTheory.RankFibre.parChar ν β a b)) := by
  first | exact @GlobalTheory.RankFibre.fibre_mem_indSpace | exact GlobalTheory.RankFibre.fibre_mem_indSpace | (intros; apply GlobalTheory.RankFibre.fibre_mem_indSpace <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalCompactFixedVectorsPiTensorSmooStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_compact_fixed_vectors_piTensor_smooth : ∀ {α : Type} [Finite α] {Γ X : α → Type} [∀ a, Group (Γ a)] [∀ a, TopologicalSpace (Γ a)] [∀ a, IsTopologicalGroup (Γ a)] [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (Γ a) (X a)), (∀ a, IsSmooth (ρ a)) → ∀ (K : ∀ a, Subgroup (Γ a)), (∀ a, IsCompact (K a : Set (Γ a))) → (∀ a, FiniteDimensional ℂ (fixed (ρ a) (K a))) → FiniteDimensional ℂ (fixed (piTensor ρ) (Subgroup.pi Set.univ K)) := by
  first | exact @GlobalTheory.PiTensorFixed.finiteDimensional_fixed_piTensor | exact GlobalTheory.PiTensorFixed.finiteDimensional_fixed_piTensor | (intros; apply GlobalTheory.PiTensorFixed.finiteDimensional_fixed_piTensor <;> assumption)
end

