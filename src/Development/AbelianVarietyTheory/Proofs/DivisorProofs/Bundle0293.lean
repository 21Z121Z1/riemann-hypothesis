import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0257
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0203
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0235
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0256
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0241
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0249
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0114
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0258
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0017
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0282
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0034
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0037

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalStageTensorPolynomialOriginStatement
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localStage_tensor_polynomial_origin : ∀ (T O : Type) [CommRing T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O],
    (maximalIdeal O).comap (algebraMap (Polynomial T) O) = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (A : Type) [CommRing A] [IsLocalRing A] (i : A →+* T), IsLocalHom i →
    ∀ (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime],
      QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A →
    ∀ (jA : Localization.AtPrime QA →+* O),
      jA.comp (algebraMap (Polynomial A) (Localization.AtPrime QA)) =
        (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i) →
    ∀ (A' : Type) [CommRing A'] [IsLocalRing A'] (ι : A →+* A') (α : A' →+* T), α.comp ι = i → IsLocalHom α →
    ∃ (E' : Type) (_ : CommRing E') (_ : Algebra (Polynomial A') E') (_ : Algebra.Etale (Polynomial A') E')
      (Q' : Ideal E') (_ : Q'.IsPrime),
      Q'.comap (algebraMap (Polynomial A') E') = GlobalTheory.KeyOriginCut.originIdeal A' ∧
      ∃ (β : Localization.AtPrime QA →+* Localization.AtPrime Q') (γ : Localization.AtPrime Q' →+* O),
        ((algebraMap (Polynomial A') (Localization.AtPrime Q')).comp Polynomial.C).comp ι =
          β.comp ((algebraMap (Polynomial A) (Localization.AtPrime QA)).comp Polynomial.C) ∧
        γ.comp β = jA ∧
        γ.comp ((algebraMap (Polynomial A') (Localization.AtPrime Q')).comp Polynomial.C) =
          (algebraMap T O).comp α := by
  first | (exact @GlobalTheory.LocalStage.localStage) | (exact GlobalTheory.LocalStage.localStage) | (intros; apply GlobalTheory.LocalStage.localStage  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMatrixOfIntertwinerStatement
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_matrix_of_intertwiner : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (N h : ℕ) (ρ ρ' : Λ → Matrix (Fin h) (Fin h) (Ainf p O)) (e e' : (Fin N → RL p O Λ) ≃ₗ[Ainf p O] (Fin h → Ainf p O)) (X : Matrix (Fin h) (Fin h) (Ainf p O)), IsFrame ρ e → IsFrame ρ' e' → (∀ l, X * ρ l = ρ' l * X) → ∃ Y, IsMat e e' X Y := by
  first | exact @GlobalTheory.DetInv.exists_isMat_of_equivariant | exact GlobalTheory.DetInv.exists_isMat_of_equivariant | (intros; apply GlobalTheory.DetInv.exists_isMat_of_equivariant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMaximalOverClosedPointClosedFibreStatement
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_maximal_over_closedPoint_closedFibre : ∀ (T E : Type) [CommRing T] [IsLocalRing T] [CommRing E] [Algebra (Polynomial T) E]
    [Algebra.FiniteType (Polynomial T) E] (Q : Ideal E) [Q.IsPrime],
    Q.comap (algebraMap (Polynomial T) E) =
      (IsLocalRing.maximalIdeal T).map (Polynomial.C : T →+* Polynomial T) →
    ∃ y : Ideal E, y.IsMaximal ∧ Q ≤ y ∧
      y.comap (algebraMap (Polynomial T) E) ≠
        (IsLocalRing.maximalIdeal T).map (Polynomial.C : T →+* Polynomial T) ∧
      (y.comap (algebraMap (Polynomial T) E)).comap (Polynomial.C : T →+* Polynomial T) =
        IsLocalRing.maximalIdeal T := by
  first | (exact @GlobalTheory.exists_maximal_over_closedPt) | (exact GlobalTheory.exists_maximal_over_closedPt) | (intros; apply GlobalTheory.exists_maximal_over_closedPt  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulMemIntegralClosureOverGenericFibre
section
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.KeyOriginNoeth

theorem exists_common_multiple_mem_closure :
    ∀ (A R : Type) [CommRing A] [IsDomain A] [CommRing R] [Algebra A R]
    (D : Type) [CommRing D] [Algebra (GlobalTheory.LocAcyc.GenFib A R) D]
    [Module.Finite (GlobalTheory.LocAcyc.GenFib A R) D] (s : Finset D),
    ∃ a : A, a ≠ 0 ∧ ∀ d ∈ s,
      GlobalTheory.KeyOriginNoeth.baseHom A R D (algebraMap A R a) * d ∈ GlobalTheory.KeyOriginNoeth.closure A R D := by
  intro A R _ _ _ _ D _ _ _ s
  classical
  letI : Algebra R D := (baseHom A R D).toAlgebra
  haveI : IsScalarTower R (GlobalTheory.LocAcyc.GenFib A R) D :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have key : ∀ d : D, ∃ a : A, a ≠ 0 ∧ IsIntegral R (baseHom A R D (algebraMap A R a) * d) := by
    intro d
    have hd : IsIntegral (GlobalTheory.LocAcyc.GenFib A R) d := Algebra.IsIntegral.isIntegral d
    obtain ⟨⟨m, hm⟩, hmi⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
      (Algebra.algebraMapSubmonoid R (nonZeroDivisors A)) (Rₘ := GlobalTheory.LocAcyc.GenFib A R) d hd
    obtain ⟨a, ha, rfl⟩ := hm
    refine ⟨a, nonZeroDivisors.ne_zero ha, ?_⟩
    exact hmi
  have hmem : ∀ x : D, IsIntegral R x → x ∈ closure A R D := fun x hx => hx
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, by simp⟩
  | insert d s hds ih =>
    obtain ⟨a₂, ha₂, h₂⟩ := ih
    obtain ⟨a₁, ha₁, h₁⟩ := key d
    refine ⟨a₁ * a₂, mul_ne_zero ha₁ ha₂, ?_⟩
    intro e he
    apply hmem
    rw [Finset.mem_insert] at he
    rcases he with rfl | he
    · have : baseHom A R D (algebraMap A R (a₁ * a₂)) * e =
          algebraMap R D (algebraMap A R a₂) * (baseHom A R D (algebraMap A R a₁) * e) := by
        simp only [map_mul]; show _ = baseHom A R D _ * _; ring
      rw [this]
      exact isIntegral_algebraMap.mul h₁
    · have : baseHom A R D (algebraMap A R (a₁ * a₂)) * e =
          algebraMap R D (algebraMap A R a₁) * (baseHom A R D (algebraMap A R a₂) * e) := by
        simp only [map_mul]; show _ = baseHom A R D _ * _; ring
      rw [this]
      exact isIntegral_algebraMap.mul (h₂ e he)

end GlobalTheory.KeyOriginNoeth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenAffineHilbertChartBasicLocusStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_affineHilbertChartBasic_locus : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (N r : ℕ) (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N) (Z : Scheme.{0}) (y : (GlobalTheory.HilbAff.functor A B r).obj (op Z)), ∃ W : Z.Opens, (∀ (Z' : Scheme.{0}) (a : Z' ⟶ Z), Set.range a ⊆ (W : Set Z) ↔ GlobalTheory.HilbAff.Basic A B e σ ((GlobalTheory.HilbAff.functor A B r).map a.op y)) ∧ (CompactSpace Z → IsCompact (W : Set Z)) := by
  first | (exact @GlobalTheory.HilbAff.Locus.exists_basic_locus) | (exact GlobalTheory.HilbAff.Locus.exists_basic_locus) | (intros; apply GlobalTheory.HilbAff.Locus.exists_basic_locus  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsParameterFunctionOfFibreDerivZeroStatement
section
open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_parameter_function_of_fibreDeriv_zero : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F), K.Rich → ∀ (a : ∀ k, Hol (K.W k)), (∀ k k' (e : K.le 0 k' k), sh e (a k) = a k') → (∀ k i, dw i (a k) = 0) → ∃ p : Hol F.V, ∀ k, a k = K.cst k p := by
  first | exact @GlobalTheory.AnPer.Charts.exists_cst_of_dw_eq_zero | exact GlobalTheory.AnPer.Charts.exists_cst_of_dw_eq_zero | (intros; apply GlobalTheory.AnPer.Charts.exists_cst_of_dw_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolyVanishingOfFibreStatement
section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_poly_vanishing_of_fiber : ∀ (R : Type) [CommRing R] (A : Type) [CommRing A] [Algebra R A] (g : ℕ) (t : Fin g → A) (h : A), GlobalTheory.DenseSec.EtChart R A t h → ∀ (Ω : Type) [Field Ω] [Algebra R Ω], IrreducibleSpace (PrimeSpectrum (TensorProduct R Ω A)) → ∀ f : TensorProduct R Ω A, ¬ IsNilpotent f → ∃ Q : MvPolynomial (Fin g) Ω, Q ≠ 0 ∧ ∀ a : A →ₐ[R] Ω, a h ≠ 0 → GlobalTheory.DenseSec.pt a f = 0 → MvPolynomial.eval (fun i => a (t i)) Q = 0 := by
  first | exact @GlobalTheory.DenseSec.exists_poly_vanishing_of_fibre | exact GlobalTheory.DenseSec.exists_poly_vanishing_of_fibre | (intros; apply GlobalTheory.DenseSec.exists_poly_vanishing_of_fibre <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqMulOfQuadraticBoundNormalLocal
section
open IsLocalRing ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory

open IsDiscreteValuationRing in

theorem mul_dvd_pow_of_quadratic_bound_dvr {V : Type} [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] {X : Type} [AddCommGroup X] (h h' : X →+ X) (C : ℕ)
    (hq : ∀ q : X → ℤ, (∀ y, 0 ≤ q y) → q 0 = 0 → (∀ y, q (-y) = q y) →
      (∀ x y z, q (x + y + z) + q x + q y + q z = q (x + y) + q (x + z) + q (y + z)) →
      (∀ y z, q (h y + z) + q y + q (h' z) = q (y + h' z) + q (h y) + q z) →
      ∀ y, q (h y) ≤ C * q y) {N : ℕ} (hN : C + 1 ≤ N) (k : X → V) (hk0 : ∀ y, k y ≠ 0)
    (h1 : ∀ y, k (-y) = k y) (h2 : k 0 = 1)
    (h3 : ∀ x y z, k (x + y + z) * k x * k y * k z = k (x + y) * k (x + z) * k (y + z))
    (h4 : ∀ y z, ∃ u : V, IsUnit u ∧
      k (h y + z) * k y * k (h' z) = u * (k (y + h' z) * k (h y) * k z)) (y : X) :
    k y * k (h y) ∣ k y ^ N := by
  have hn : ∀ z, ∃ n : ℕ, addVal V (k z) = n := fun z =>
    (ENat.ne_top_iff_exists.1 (mt addVal_eq_top_iff.1 (hk0 z))).imp fun _ e => e.symm
  choose n hn using hn
  have key := hq (fun z => (n z : ℤ)) (fun _ => Int.natCast_nonneg _)
    (by
      have := hn 0
      rw [h2, addVal_one] at this
      exact_mod_cast this.symm)
    (fun z => by
      have := hn (-z)
      rw [h1, hn] at this
      exact_mod_cast this.symm)
    (fun a b c => by
      have := congrArg (addVal V) (h3 a b c)
      simp only [addVal_mul, hn] at this
      exact_mod_cast this)
    (fun a b => by
      obtain ⟨u, hu, e⟩ := h4 a b
      have := congrArg (addVal V) e
      simp only [addVal_mul, hn, addVal_eq_zero_iff.2 hu, zero_add] at this
      exact_mod_cast this) y
  have key' : n (h y) ≤ C * n y := by exact_mod_cast key
  rw [← addVal_le_iff_dvd, addVal_mul, addVal_pow, hn, hn, nsmul_eq_mul]
  have : n y + n (h y) ≤ N * n y := by nlinarith [Nat.mul_le_mul_right (n y) hN]
  exact_mod_cast this

theorem exists_pow_eq_mul_of_quadratic_bound :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (X : Type) [AddCommGroup X] (h h' : X →+ X) (C : ℕ), (∀ q : X → ℤ, (∀ y, 0 ≤ q y) → q 0 = 0 → (∀ y, q (-y) = q y) → (∀ x y z, q (x + y + z) + q x + q y + q z = q (x + y) + q (x + z) + q (y + z)) → (∀ y z, q (h y + z) + q y + q (h' z) = q (y + h' z) + q (h y) + q z) → ∀ y, q (h y) ≤ C * q y) → ∀ N : ℕ, C + 1 ≤ N → ∀ (κ : X → (FractionRing R)ˣ), (∀ y, κ (-y) = κ y) → κ 0 = 1 → (∀ x y z, κ (x + y + z) * κ x * κ y * κ z = κ (x + y) * κ (x + z) * κ (y + z)) → (∀ y, ∃ r : R, (κ y : FractionRing R) = algebraMap R _ r) → (∀ y z, ∃ u : Rˣ, ((κ (h y + z) * κ y * κ (h' z) : (FractionRing R)ˣ) : FractionRing R) = algebraMap R _ (u : R) * ((κ (y + h' z) * κ (h y) * κ z : (FractionRing R)ˣ) : FractionRing R)) → ∀ y, ∃ r : R, ((κ y ^ N : (FractionRing R)ˣ) : FractionRing R) = algebraMap R _ r * κ y * κ (h y) := by
  intro R _ _ _ hR X _ h h' C hq N hN κ h1 h2 h3 hκ h4 y
  obtain ⟨hno, -, hic, -⟩ := hR
  have hx : ∃ r : R, algebraMap R (FractionRing R) r =
      ((κ y ^ N * (κ y * κ (h y))⁻¹ : (FractionRing R)ˣ) : FractionRing R) := by
    refine exists_algebraMap_eq_of_forall_discreteValuationSubring fun V hV hRV _ => ?_
    have hm : ∀ z, (κ z : FractionRing R) ∈ V := fun z => by
      obtain ⟨r, e⟩ := hκ z
      exact e ▸ hRV r
    obtain ⟨c, hc⟩ := mul_dvd_pow_of_quadratic_bound_dvr (V := V) h h' C hq hN
      (fun z => ⟨κ z, hm z⟩) (fun z e => (κ z).ne_zero (congrArg Subtype.val e))
      (fun z => Subtype.ext (congrArg Units.val (h1 z)))
      (Subtype.ext (congrArg Units.val h2))
      (fun a b c => Subtype.ext (congrArg Units.val (h3 a b c)))
      (fun a b => by
        obtain ⟨u, e⟩ := h4 a b
        exact ⟨(algebraMap R (FractionRing R)).codRestrict V hRV u, u.isUnit.map _,
          Subtype.ext e⟩) y
    have hc' : (κ y : FractionRing R) ^ N = κ y * κ (h y) * (c : FractionRing R) := by
      simpa using congrArg Subtype.val hc
    have : ((κ y ^ N * (κ y * κ (h y))⁻¹ : (FractionRing R)ˣ) : FractionRing R) = c := by
      rw [Units.val_mul, Units.mul_inv_eq_iff_eq_mul, Units.val_pow_eq_pow_val, hc', Units.val_mul, mul_comm]
    exact this ▸ c.2
  obtain ⟨r, hr⟩ := hx
  refine ⟨r, ?_⟩
  rw [hr, mul_assoc, ← Units.val_mul, ← Units.val_mul, inv_mul_cancel_right]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOfKaehlerDifferentialEqZeroOfSmoothDo
section
open TensorProduct

namespace GlobalTheory

theorem exists_pow_eq_of_kaehlerDifferential_eq_zero_of_smooth_domain :
    ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [IsAlgClosed k] (hk : (p : k) = 0) (S : Type)
      [CommRing S] [IsDomain S] [Algebra k S] [Algebra.Smooth k S] (f : S),
      KaehlerDifferential.D k S f = 0 → ∃ h : S, h ^ p = f := by
  intro p hp k _ _ hk S _ _ _ _ f hf
  have hS : IsIntegrallyClosed S :=
    IsIntegrallyClosed.of_localization_maximal fun m _ _ =>
      (isDomain_and_isIntegrallyClosed_atPrime_of_smooth k m _).2
  have hK : KaehlerDifferential.D k (FractionRing S) (algebraMap S (FractionRing S) f) = 0 := by
    rw [← KaehlerDifferential.map_D k k S (FractionRing S) f, hf, map_zero]
  obtain ⟨h, hh⟩ := GlobalTheory.T.exists_pow_eq_of_kaehler_D_eq_zero' p k hk (FractionRing S) _ hK
  have hint : IsIntegral S h :=
    IsIntegral.of_pow hp.out.pos (by rw [hh]; exact isIntegral_algebraMap)
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  refine ⟨y, IsFractionRing.injective S (FractionRing S) ?_⟩
  rw [map_pow, hh]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuaternionNormOneNearReSqNeOne
section
open NumberField IsDedekindDomain GlobalTheory.QSA
open scoped Quaternion Topology
open Filter

namespace GlobalTheory.QSA

theorem exists_nrm_one_re_sq_ne_one : ∀ (K : Type) [Field K] [TopologicalSpace K] [IsTopologicalDivisionRing K] [T2Space K], (2 : K) ≠ 0 → (𝓝[≠] (0 : K)).NeBot → ∀ a b : K, a ≠ 0 → ∀ g : ℍ[K, a, b], nrm g = 1 → ∀ W : Set ℍ[K, a, b], W ∈ 𝓝 g → ∃ g' : ℍ[K, a, b], nrm g' = 1 ∧ g'.re ^ 2 ≠ 1 ∧ W ∈ 𝓝 g' := by
  intro K _ _ _ _ h2 hne a b ha g hg W hW
  by_cases hre : g.re ^ 2 = 1
  swap
  · exact ⟨g, hg, hre, hW⟩
  have hs0 : g.re ≠ 0 := by
    intro h
    rw [h] at hre
    simp at hre
  let X0 : K → K := fun τ => (1 + a * τ ^ 2) / (1 - a * τ ^ 2)
  let X1 : K → K := fun τ => 2 * τ / (1 - a * τ ^ 2)
  let x : K → ℍ[K, a, b] := fun τ => ⟨X0 τ, X1 τ, 0, 0⟩
  have hD : Tendsto (fun τ : K => 1 - a * τ ^ 2) (𝓝 0) (𝓝 1) := by
    have : Continuous (fun τ : K => 1 - a * τ ^ 2) := by fun_prop
    simpa using this.tendsto 0
  have hx0 : Tendsto X0 (𝓝 0) (𝓝 1) := by
    have h1 : Continuous (fun τ : K => 1 + a * τ ^ 2) := by fun_prop
    have := (h1.tendsto 0).div hD one_ne_zero
    simpa [Pi.div_def] using this
  have hx1 : Tendsto X1 (𝓝 0) (𝓝 0) := by
    have h1 : Continuous (fun τ : K => 2 * τ) := by fun_prop
    have := (h1.tendsto 0).div hD one_ne_zero
    simpa [Pi.div_def] using this
  have key : ∀ c d : K, Tendsto (fun τ => c * X0 τ + d * X1 τ) (𝓝 0) (𝓝 c) := by
    intro c d
    simpa using (hx0.const_mul c).add (hx1.const_mul d)
  have hf : Tendsto (fun τ => g * x τ) (𝓝 0) (𝓝 g) := by
    rw [(Topology.IsInducing.induced coords).tendsto_nhds_iff, tendsto_pi_nhds]
    intro i
    fin_cases i
    · refine (key g.re (a * g.imI)).congr fun τ => ?_
      simp [coords, x]
    · refine (key g.imI g.re).congr fun τ => ?_
      simp [coords, x, add_comm]
    · refine (key g.imJ (-(a * g.imK))).congr fun τ => ?_
      simp [coords, x, sub_eq_add_neg]
    · refine (key g.imK (-g.imJ)).congr fun τ => ?_
      simp [coords, x, add_comm]
  have e1 : ∀ᶠ τ in 𝓝[≠] (0 : K), τ ≠ 0 := self_mem_nhdsWithin
  have e2 : ∀ᶠ τ in 𝓝[≠] (0 : K), 1 - a * τ ^ 2 ≠ 0 :=
    (hD.eventually_ne one_ne_zero).filter_mono nhdsWithin_le_nhds
  have e3 : ∀ᶠ τ in 𝓝[≠] (0 : K), g.re + a * τ * g.imI ≠ 0 := by
    have h1 : Continuous (fun τ : K => g.re + a * τ * g.imI) := by fun_prop
    exact ((h1.tendsto 0).eventually_ne (by simpa using hs0)).filter_mono nhdsWithin_le_nhds
  have e4 : ∀ᶠ τ in 𝓝[≠] (0 : K), g.re * τ + g.imI ≠ 0 := by
    by_cases hI : g.imI = 0
    · filter_upwards [e1] with τ hτ
      simpa [hI] using ⟨hs0, hτ⟩
    · have h1 : Continuous (fun τ : K => g.re * τ + g.imI) := by fun_prop
      exact ((h1.tendsto 0).eventually_ne (by simpa using hI)).filter_mono nhdsWithin_le_nhds
  have e5 : ∀ᶠ τ in 𝓝[≠] (0 : K), g * x τ ∈ interior W :=
    (hf.eventually (interior_mem_nhds.2 hW)).filter_mono nhdsWithin_le_nhds
  obtain ⟨τ, h1, h2', h3, h4, h5⟩ := (e1.and (e2.and (e3.and (e4.and e5)))).exists
  refine ⟨g * x τ, ?_, ?_, mem_interior_iff_mem_nhds.1 h5⟩
  · rw [nrm_mul, hg, one_mul]
    simp only [nrm, x, X0, X1]
    field_simp
    ring
  · have hr : (g * x τ).re = g.re * X0 τ + a * g.imI * X1 τ := by simp [x]
    rw [hr]
    intro h
    have hm : g.re * X0 τ + a * g.imI * X1 τ - g.re
        = 2 * a * τ * (g.re * τ + g.imI) / (1 - a * τ ^ 2) := by
      simp only [X0, X1]
      field_simp
      ring
    have hp : g.re * X0 τ + a * g.imI * X1 τ + g.re
        = 2 * (g.re + a * τ * g.imI) / (1 - a * τ ^ 2) := by
      simp only [X0, X1]
      field_simp
      ring
    have hz : (g.re * X0 τ + a * g.imI * X1 τ - g.re) * (g.re * X0 τ + a * g.imI * X1 τ + g.re) = 0 := by
      linear_combination h - hre
    rw [hm, hp] at hz
    exact mul_ne_zero (div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h2 ha) h1) h4) h2')
      (div_ne_zero (mul_ne_zero h2 h3) h2') hz

end GlobalTheory.QSA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRegularCompletionFlat
section
open IsLocalRing

namespace GlobalTheory.RegularCompletionPackage

theorem exists_regular_completion :
    ∀ (R₁ Ω : Type) [CommRing R₁] [IsRegularLocalRing R₁] [Field Ω] (u : R₁ →+* Ω),
      RingHom.ker u = maximalIdeal R₁ →
      ∃ (C : Type) (_ : CommRing C) (_ : IsRegularLocalRing C) (c : R₁ →+* C) (uC : C →+* Ω),
        c.Flat ∧ (maximalIdeal R₁).map c = maximalIdeal C ∧ IsAdicComplete (maximalIdeal C) C ∧
        RingHom.ker uC = maximalIdeal C ∧ uC.comp c = u := by
  intro R₁ Ω _ _ _ u hu
  set C := AdicCompletion (maximalIdeal R₁) R₁
  haveI : IsRegularLocalRing C := GlobalTheory.RegularCompletion.isRegularLocalRing_adicCompletion R₁
  have hbij := AdicCompletion.residueField_map_bijective_of_fg (R := R₁)
    (maximalIdeal R₁).fg_of_isNoetherianRing
  let e : ResidueField R₁ ≃+* ResidueField C :=
    RingEquiv.ofBijective (ResidueField.map (algebraMap R₁ C)) hbij
  let ub : ResidueField R₁ →+* Ω := Ideal.Quotient.lift (maximalIdeal R₁) u
    (fun a ha => by rw [← RingHom.mem_ker, hu]; exact ha)
  let uC : C →+* Ω := (ub.comp e.symm.toRingHom).comp (residue C)
  have hcomp : uC.comp (algebraMap R₁ C) = u := by
    ext r
    simp only [uC, RingHom.comp_apply]
    have : residue C (algebraMap R₁ C r) = e (residue R₁ r) := by
      simp [e, ResidueField.map_residue]
    rw [this]
    simp [ub]
    rfl
  refine ⟨C, inferInstance, inferInstance, algebraMap R₁ C, uC,
    RingHom.flat_algebraMap_iff.2 (AdicCompletion.flat_of_isNoetherian _),
    (AdicCompletion.maximalIdeal_eq_map).symm, inferInstance, ?_, hcomp⟩
  ext x
  rw [RingHom.mem_ker]
  simp only [uC, RingHom.comp_apply]
  constructor
  · intro h
    have h1 : e.symm (residue C x) = 0 := (injective_iff_map_eq_zero ub).1 ub.injective _ h
    have h2 : residue C x = 0 := by simpa using h1
    simpa [residue_eq_zero_iff] using h2
  · intro h
    rw [(residue_eq_zero_iff x).2 h]
    simp

end GlobalTheory.RegularCompletionPackage
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRegularNearOfRegularQuotientPrimeStatement
section
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_regular_near_of_regular_quotient_prime : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (p : Ideal B) [p.IsPrime], IsRegularLocalRing (Localization.AtPrime p) → ∃ g, g ∉ p ∧ ∀ (q : Ideal B) [q.IsPrime], p ≤ q → g ∉ q → IsRegularLocalRing (Localization.AtPrime q ⧸ p.map (algebraMap B (Localization.AtPrime q))) → IsRegularLocalRing (Localization.AtPrime q) := by
  first | exact @GlobalTheory.RegularAscent.exists_regular_near_of_regular_quotient | exact GlobalTheory.RegularAscent.exists_regular_near_of_regular_quotient | (intros; apply GlobalTheory.RegularAscent.exists_regular_near_of_regular_quotient <;> assumption)
end

