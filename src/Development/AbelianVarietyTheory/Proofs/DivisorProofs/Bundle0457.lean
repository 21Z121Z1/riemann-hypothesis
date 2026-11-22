import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PullbackBijectiveDegreesOneTwo
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuationTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0436
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0429
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0410
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0437
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0433
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapMaximalIdealEqOrigin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0427
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0438
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0393
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0424
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjBundleCochainPresheafIsSheaf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0359
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0395
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0400
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0323

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JoinedMapsAgreeCohomologyZeroOneInstances
section
set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace GlobalTheory.CxCoh

namespace CxMap

universe a b

variable {C : Type a} [Category.{0} C] {C' : Type b} [Category.{0} C'] {K : Cx C} {K' : Cx C'}

theorem h0_eq_of_joined (m m' : CxMap K K') (θ : m.G ⟶ m'.G) (hj : m.Joined m' θ) (c : K.H0) :
    m.h0 c = m'.h0 c := by
  obtain ⟨g, hg⟩ := c
  have hg' : K.D0 g = 0 := hg
  have hc : ∀ T T' (φ : T ⟶ T'), g T' = K.M0.map φ (g T) := fun T T' φ => by
    have h := congrArg (fun c => c.1 T T' φ) hg'
    change g T' - K.M0.map φ (g T) = 0 at h
    exact sub_eq_zero.mp h
  apply Subtype.ext
  funext T
  change m.a0 T (g _) = m'.a0 T (g _)
  rw [hc _ _ (θ.app T), hj.e0]

theorem p1_eq_add_D0_of_joined_of_cocycle (m m' : CxMap K K') (θ : m.G ⟶ m'.G) (hj : m.Joined m' θ) (c : K.T1)
    (hc : K.D1 c = 0) :
    m'.p1 c = m.p1 c + K'.D0 (fun T => m'.a0 T (c.1 _ _ (θ.app T))) := by
  have e1 : ∀ A A' A'' (α : A ⟶ A') (β : A' ⟶ A''),
      c.1 A A'' (α ≫ β) = K.M0.map β (c.1 A A' α) + c.1 A' A'' β := by
    intro A A' A'' α β
    have h := congrArg (fun x => x.1 A A' A'' α β) hc
    change K.M0.map β (c.1 A A' α) - c.1 A A'' (α ≫ β) + c.1 A' A'' β = 0 at h
    linear_combination (norm := abel1) -h
  have e2 : ∀ A A' (α : A ⟶ A'), c.2 A' = K.M1.map α (c.2 A) + K.d0 A' (c.1 A A' α) := by
    intro A A' α
    have h := congrArg (fun x => x.2.1 A A' α) hc
    change c.2 A' - K.M1.map α (c.2 A) - K.d0 A' (c.1 A A' α) = 0 at h
    linear_combination (norm := abel1) h
  refine Prod.ext ?_ ?_
  · funext T T' φ
    change m'.a0 T' (c.1 _ _ (m'.G.map φ)) = m.a0 T' (c.1 _ _ (m.G.map φ)) +
      (m'.a0 T' (c.1 _ _ (θ.app T')) - K'.M0.map φ (m'.a0 T (c.1 _ _ (θ.app T))))
    have k1 := e1 _ _ _ (m.G.map φ) (θ.app T')
    have k2 := e1 _ _ _ (θ.app T) (m'.G.map φ)
    rw [θ.naturality φ] at k1
    have k := congrArg (m'.a0 T') (k1.symm.trans k2)
    rw [map_add, map_add, hj.e0, m'.compDegreeZero_natural] at k
    linear_combination (norm := abel1) -k
  · funext T
    change m'.a1 T (c.2 _) = m.a1 T (c.2 _) + K'.d0 T (m'.a0 T (c.1 _ _ (θ.app T)))
    rw [e2 _ _ (θ.app T), map_add, hj.e1, m'.comp_commutes_diffZero]

theorem h1_eq_of_joined (m m' : CxMap K K') (θ : m.G ⟶ m'.G) (hj : m.Joined m' θ) (c : K.H1) :
    m.h1 c = m'.h1 c := by
  obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientAddGroup.mk_surjective c
  change (QuotientAddGroup.mk (m.z1 ⟨x, hx⟩) : K'.H1) = QuotientAddGroup.mk (m'.z1 ⟨x, hx⟩)
  rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
  refine ⟨fun T => m'.a0 T (x.1 _ _ (θ.app T)), ?_⟩
  have h := p1_eq_add_D0_of_joined_of_cocycle m m' θ hj x (AddMonoidHom.mem_ker.mp hx)
  change _ = -(m.p1 x) + m'.p1 x
  rw [h]; abel

end CxMap

theorem joinedOne_cohomology.{a, b} : JoinedOne.{a, b} := fun m m' θ hj =>
  ⟨CxMap.h0_eq_of_joined m m' θ hj, CxMap.h1_eq_of_joined m m' θ hj⟩

theorem joinedOne_inst : JoinedOne.{1, 1} ∧ JoinedOne.{1, 0} ∧ JoinedOne.{0, 0} :=
  ⟨joinedOne_cohomology, joinedOne_cohomology, joinedOne_cohomology⟩

end GlobalTheory.CxCoh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeFormalGroupDeterminantPowDepthOfRadii
section
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory.DepthCount

variable {C : Type} [Field C]

theorem prod_X_col {i : ℕ} (b : Fin i) (d : Fin i →₀ ℕ) :
    (d.prod fun s e => (X (⟨b, s⟩ : Σ _ : Fin i, Fin i) : MvPowerSeries (Σ _ : Fin i, Fin i) C) ^ e)
      = monomial (Finsupp.mapDomain (Sigma.mk b) d) 1 := by
  induction d using Finsupp.induction with
  | zero => simp
  | single_add s n d hs hn ih =>
    rw [Finsupp.prod_add_index' (by simp) (by intros; rw [pow_add]), ih, Finsupp.mapDomain_add,
      Finsupp.mapDomain_single, Finsupp.prod_single_index (by simp), X_pow_eq,
      monomial_mul_monomial, one_mul]

theorem hasSubst_col {i : ℕ} (b : Fin i) :
    HasSubst (fun a : Fin i => (X ⟨b, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C)) :=
  hasSubst_of_constantCoeff_zero (fun a => constantCoeff_X _)

theorem constantCoeff_col {i : ℕ} (b : Fin i) (g : MvPowerSeries (Fin i) C)
    (hg : constantCoeff g = 0) :
    constantCoeff (subst (fun a : Fin i => (X ⟨b, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C)) g)
      = 0 := by
  have hs := hasSubst_col (C := C) b
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_subst hs]
  convert finsum_zero with d
  rw [prod_X_col, coeff_monomial, smul_eq_mul]
  split_ifs with h
  · have hd : d = 0 := by
      have h' := h.symm
      rw [← Finsupp.mapDomain_zero (f := Sigma.mk b)] at h'
      exact Finsupp.mapDomain_injective (sigma_mk_injective (i := b)) h'
    subst hd
    simp [hg]
  · simp

theorem wt_col {i : ℕ} (v : AddValuation C (WithTop ℝ)) (ρ : Fin i → ℝ) (b : Fin i)
    (g : MvPowerSeries (Fin i) C) (hg : OrdGe v ρ g 0) (β : (Σ _ : Fin i, Fin i) →₀ ℕ) :
    (((0 - β.sum (fun y e => ρ y.2 * (e : ℝ)) : ℝ)) : WithTop ℝ) ≤
      v (coeff β (subst (fun a : Fin i => (X ⟨b, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C)) g)) := by
  have hs := hasSubst_col (C := C) b
  rw [coeff_subst hs, finsum_eq_sum _ (coeff_subst_finite hs g β)]
  apply v.map_le_sum
  intro d _
  rw [prod_X_col, coeff_monomial, smul_eq_mul]
  split_ifs with h
  · rw [mul_one]
    subst h
    rw [Finsupp.sum_mapDomain_index (by simp) (by intros; push_cast; ring),
      Finsupp.sum_fintype _ _ (by simp)]
    exact hg d
  · simp

theorem depth_count : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (i d c : ℕ) (ρ : Fin i → ℝ) (t : Fin d → MvPowerSeries (Fin i) C) (B : ℝ), (∀ a, constantCoeff (t a) = 0) → (∀ a, OrdGe v ρ (t a) 0) → (∀ α ∈ (detPow C i c).support, (((B + c * ∑ a, ρ a : ℝ)) : WithTop ℝ) ≤ v ((detPow C i c).coeff α * mfact α)) → ∀ f : MvPowerSeries (Σ _ : Fin i, Fin d) C, MvIsInt v f → ((B : ℝ) : WithTop ℝ) ≤ v (derivAt0 (detPow C i c) (subst (fun x : (Σ _ : Fin i, Fin d) => subst (fun a : Fin i => (X ⟨x.1, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C)) (t x.2)) f)) := by
  intro C _ _ v i d c ρ t B ht0 ht hP f hf
  have hw := GlobalTheory.WeightSubst.weight_subst_nonneg C v (Σ _ : Fin i, Fin i) (Σ _ : Fin i, Fin d)
    (fun y => ρ y.2) f
    (fun x : (Σ _ : Fin i, Fin d) => subst (fun a : Fin i =>
      (X ⟨x.1, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C)) (t x.2)) hf
    (fun x => constantCoeff_col x.1 _ (ht0 x.2)) (fun x => wt_col v ρ x.1 _ (ht x.2))
  unfold derivAt0
  apply v.map_le_sum
  intro α hα
  have hrow := ((GlobalTheory.T.matrixVariablesDeterminantPow_monomial_shape C i c).2.2.2 α hα).1
  rw [v.map_mul]
  have e : B = (B + c * ∑ a, ρ a) + (0 - α.sum (fun y e => ρ y.2 * (e : ℝ))) := by
    rw [Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sigma, Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    have hc : ∀ a : Fin i, (∑ b : Fin i, ((α ⟨b, a⟩ : ℕ) : ℝ)) = c := fun a => by
      exact_mod_cast hrow a
    simp_rw [hc]
    rw [← Finset.sum_mul]
    ring
  rw [e, WithTop.coe_add]
  exact add_le_add (hP α hα) (hw α)

end GlobalTheory.DepthCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelOneModularFormValueGaloisTransport
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)

namespace GlobalTheory.QFam

theorem isobaric_monomial_div (c x y ω : ℂ) (a b w : ℕ) (h : 4 * a + 6 * b = w) :
    c * (x ^ a * y ^ b) / ω ^ w = c * ((x / ω ^ 4) ^ a * (y / ω ^ 6) ^ b) := by
  rw [div_pow, div_pow, ← pow_mul, ← pow_mul, div_mul_div_comm, ← pow_add, h, mul_div_assoc]

theorem levelOne_value_transport : ∀ (g : ℂ ≃+* ℂ) (w N : ℕ) (F F' : ℍ → ℂ) (τ₀ τ₁ : ℍ) (ω₀ ω₁ : ℂ), 0 < N → (∀ γ : SL(2, ℤ), F ∣[(w : ℤ)] γ = F) → QConj g N F F' → g (E₄ τ₀ / ω₀ ^ 4) = E₄ τ₁ / ω₁ ^ 4 → g (E₆ τ₀ / ω₀ ^ 6) = E₆ τ₁ / ω₁ ^ 6 → g (F τ₀ / ω₀ ^ w) = F' τ₁ / ω₁ ^ w := by
  intro g w N F F' τ₀ τ₁ ω₀ ω₁ hN hF hq h4 h6
  obtain ⟨s, c, hs, h0, h1⟩ := GlobalTheory.T.exists_conj_eisensteinPolynomial_levelOne g w N F F' hN hF hq
  rw [h0, h1, Finset.sum_div, Finset.sum_div, map_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [isobaric_monomial_div _ _ _ _ _ _ _ (hs p hp), isobaric_monomial_div _ _ _ _ _ _ _ (hs p hp),
    map_mul, map_mul, map_pow, map_pow, h4, h6]

end GlobalTheory.QFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MappingConeShortExactAugmentationClassEqStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mappingCone_shortExact_augmentation_class_eq : ∀ (R : Type) [CommRing R] (S : ShortComplex (Shv R)), S.ShortExact →
    ∀ (hc : (CochainComplex.singleFunctor (Shv R) 0).map S.f ≫ resAug S.X₂ = resAug S.X₁ ≫ resMap R S.f)
    (e : HomotopyEquiv (mappingCone (resMap R S.f)) (res R S.X₃)),
    Homotopy (mappingCone.inr (resMap R S.f) ≫ e.hom) (resMap R S.g) →
    CohomologyClass.mk (Cocycle.ofHom
        (mappingCone.descShortComplex (S.map (CochainComplex.singleFunctor (Shv R) 0)) ≫ resAug S.X₃)) =
      CohomologyClass.mk (Cocycle.ofHom
        (mappingCone.map _ (resMap R S.f) (resAug S.X₁) (resAug S.X₂) hc ≫ e.hom)) := by
  first | (exact @GlobalTheory.EtC.ConeClass.cone_class_eq) | (exact GlobalTheory.EtC.ConeClass.cone_class_eq) | (intros; apply GlobalTheory.EtC.ConeClass.cone_class_eq  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRegularFormsOfWedgePairingPerfectStatement
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_regularForms_of_wedge_pairing_perfect : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (B : Subalgebra k K) [IsFractionRing B K] [Algebra.Smooth k B] (d p q : ℕ), Module.finrank K Ω[K⁄k] = d → p + q = d → ∀ y ∈ ⋀[K]^q Ω[K⁄k], (∀ a ∈ omB k K B p, a * y ∈ omB k K B d) → y ∈ omB k K B q := by
  first | (exact @GlobalTheory.PD.mem_omB_of_mul_mem_omB) | (exact GlobalTheory.PD.mem_omB_of_mul_mem_omB) | (intros; apply GlobalTheory.PD.mem_omB_of_mul_mem_omB  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalLocalRingEtaleBaseChange
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normal_local_ring_etale_base_change : ∀ (T O : Type) [CommRing T] [CommRing O] [IsLocalRing O] [Algebra T O] [Algebra T[X] O]
    [IsScalarTower T T[X] O]
    (A A₁ : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [Algebra.EssFiniteType ℤ A] [CommRing A₁] [IsDomain A₁] [IsLocalRing A₁] [IsNoetherianRing A₁]
    [IsIntegrallyClosed A₁] [Algebra.EssFiniteType ℤ A₁] (f : A →+* A₁) (i : A →+* T)
    (i₁ : A₁ →+* T) (hf : Function.Injective f)
    (EA : Type) [CommRing EA] [Algebra A[X] EA] [Algebra A EA] [IsScalarTower A A[X] EA]
    [Algebra.Etale A[X] EA]
    (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O) (hcomp : i₁.comp f = i)
    (hj : jA.comp (algebraMap A[X] (Localization.AtPrime QA)) =
      (algebraMap T[X] O).comp (Polynomial.mapRingHom i))
    (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA] (q : ℕ)
    (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
    0 < q → IsUnit (q : A) →
    GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA q actA →
    ∀ a : A, a ≠ 0 →
    (∀ (P : Ideal (Localization.AtPrime QA)) [P.IsPrime],
      algebraMap A (Localization.AtPrime QA) a ∉ P →
      GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt A (Localization.AtPrime QA) DA P) →
    ∀ (P₁ : Ideal (GlobalTheory.KeyOriginBC.Loc₁ f i i₁ EA QA jA hcomp hj)) [P₁.IsPrime], algebraMap A₁ (GlobalTheory.KeyOriginBC.Loc₁ f i i₁ EA QA jA hcomp hj) (f a) ∉ P₁ →
      GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt A₁ (GlobalTheory.KeyOriginBC.Loc₁ f i i₁ EA QA jA hcomp hj) (GlobalTheory.KeyOriginBC.BC (GlobalTheory.KeyOriginBC.fibBC f i i₁ EA QA jA hcomp hj hf) DA) P₁ := by
  first | (exact @GlobalTheory.KeyOriginBCEt.closureEtaleAt_baseChange) | (exact GlobalTheory.KeyOriginBCEt.closureEtaleAt_baseChange) | (intros; apply GlobalTheory.KeyOriginBCEt.closureEtaleAt_baseChange  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneFormEqZeroOfVanishingOnPairs
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR Opposite KaehlerDifferential

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechDR

theorem form_pow_smul_eq_zero_of_basicOpen {R' : Type} [CommRing R'] {X' : Scheme.{0}}
    (s' : X' ⟶ Sp R') (W : X'.affineOpens) (f : Γ(X', W.1)) (hU : IsAffineOpen (X'.basicOpen f))
    (hle : (⟨X'.basicOpen f, hU⟩ : X'.affineOpens) ≤ W) (ω : Ω[(OAff s').obj (op W)⁄R'])
    (h : p1 (OAff s') (homOfLE hle).op ω = 0) :
    ∃ n : ℕ, ((show (OAff s').obj (op W) from f) ^ n) • ω = 0 := by
  let A := (OAff s').obj (op W)
  let B := (OAff s').obj (op (⟨X'.basicOpen f, hU⟩ : X'.affineOpens))
  let ψ : A →ₐ[R'] B := mp (OAff s') (homOfLE hle).op
  letI : Algebra A B := (ψ : A →+* B).toAlgebra
  haveI : IsScalarTower R' A B :=
    IsScalarTower.of_algebraMap_eq fun r ↦ (ψ.commutes r).symm
  haveI : IsLocalization.Away (show A from f) B := W.2.isLocalization_basicOpen f
  have e := (semiHom_mp (OAff s') (homOfLE hle).op).oneFormMap_eq_kaehlerDifferential_map (R := R') (B := A) (B' := B)
    (fun b ↦ rfl) ω
  have h' : KaehlerDifferential.map R' R' A B ω = 0 := e.symm.trans h
  obtain ⟨⟨c, hc⟩, hc0⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers (show A from f))
    (f := KaehlerDifferential.map R' R' A B)).1 h'
  obtain ⟨n, rfl⟩ := hc
  exact ⟨n, hc0⟩

theorem form_eq_zero_of_pair {R' : Type} [CommRing R'] {X X' : Scheme.{0}} (φ : X' ⟶ X)
    (s' : X' ⟶ Sp R') (W : X'.affineOpens) (ω : Ω[(OAff s').obj (op W)⁄R'])
    (h : ∀ (p : Pair φ) (hp : p.1.1 ≤ W), p1 (OAff s') (homOfLE hp).op ω = 0) : ω = 0 := by
  let A := (OAff s').obj (op W)
  let J : Ideal A := (Submodule.span A {ω}).annihilator
  let I : Set Γ(X', W.1) := {a | (show A from a) ∈ J}
  have hcov : W.1 ≤ ⨆ a : I, X'.basicOpen a.1 := by
    intro x hx
    obtain ⟨p, f, e, hxp⟩ := Pair.exists_basicOpen φ W hx
    obtain ⟨⟨⟨U, hU⟩, V⟩, hpV⟩ := p
    dsimp only at e hxp
    subst e
    have hle : (⟨X'.basicOpen f, hU⟩ : X'.affineOpens) ≤ W := X'.basicOpen_le f
    obtain ⟨n, hn⟩ := form_pow_smul_eq_zero_of_basicOpen s' W f hU hle ω
      (h ⟨(⟨X'.basicOpen f, hU⟩, V), hpV⟩ hle)
    have hxn : x ∈ X'.basicOpen (f ^ n) := by
      rcases n with _ | n
      · rw [pow_zero, X'.basicOpen_of_isUnit isUnit_one]; exact hx
      · rwa [X'.basicOpen_pow f n.succ_pos]
    exact TopologicalSpace.Opens.mem_iSup.2
      ⟨⟨f ^ n, show ((show A from f) ^ n) ∈ J from
        (Submodule.mem_annihilator_span_singleton ω _).2 hn⟩, hxn⟩
  have hI := (W.2.self_le_iSup_basicOpen_iff).1 hcov
  have hJ : Ideal.span I ≤ J := Ideal.span_le.2 fun a ha ↦ ha
  have h1 : (1 : A) ∈ J := hJ (hI ▸ Submodule.mem_top)
  simpa using (Submodule.mem_annihilator_span_singleton _ _).1 h1

end GlobalTheory.CechDR
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivCocycleMemRangeCobOfPullbackMulPStatement
section
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pDivCocycle_mem_range_cob_of_pullback_mulP : ∀ {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] (G : PDivGroup p R) (c : G.cocycles) (B : G.funs), G.cob B = cocyclesMap ((p : ℤ_[p]) • 𝟙 G) c → B.1 1 = 0 → c ∈ LinearMap.range G.cob := by
  first | exact @GlobalTheory.cocycle_mem_range_cob_of_pullback_mulP | exact GlobalTheory.cocycle_mem_range_cob_of_pullback_mulP | (intros; apply GlobalTheory.cocycle_mem_range_cob_of_pullback_mulP <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveSemilinearLiftBaseChangeBijective
section
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

namespace PDiv

section PrimBaseChange

variable {R A : Type} (R' : Type) [CommRing R] [CommRing A] [Bialgebra R A] [Module.Finite R A]
  [Module.Projective R A] [IsCocomm R A] [CommRing R'] [Algebra R R']

theorem counit_comp_cartierBaseChange :
    (counitAlgHom R' (CartierDual R' (R' ⊗[R] A))).comp
        ((CartierDual.baseChange R R' A).toAlgEquiv : R' ⊗[R] CartierDual R A →ₐ[R'] _) =
      AugCot.baseChangeAug R' (counitAlgHom R (CartierDual R A)) := by
  refine AlgHom.ext fun x => ?_
  induction x with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul r φ =>
    simp [Algebra.TensorProduct.one_def, Algebra.smul_def, mul_comm]

def cotBaseChange :
    Cot R' (CartierDual R' (R' ⊗[R] A)) ≃ₗ[R'] R' ⊗[R] Cot R (CartierDual R A) :=
  ((AugCot.baseChangeEquiv R' (counitAlgHom R (CartierDual R A))).trans
    (AugCot.congr (CartierDual.baseChange R R' A).toAlgEquiv
      (counit_comp_cartierBaseChange R'))).symm

theorem cotBaseChange_d (φ : CartierDual R A) :
    cotBaseChange R' (dUnit R' (CartierDual.baseChange R R' A ((1 : R') ⊗ₜ φ))) =
      (1 : R') ⊗ₜ dUnit R φ := by
  rw [cotBaseChange, LinearEquiv.symm_apply_eq, LinearEquiv.trans_apply,
    AugCot.baseChangeEquiv_tmul_d, one_smul, AugCot.congr_d]
  rfl

theorem cotBaseChange_hom_ext {N : Type} [AddCommGroup N] [Module R' N]
    {f g : Cot R' (CartierDual R' (R' ⊗[R] A)) →ₗ[R'] N}
    (h : ∀ φ : CartierDual R A, f (dUnit R' (CartierDual.baseChange R R' A ((1 : R') ⊗ₜ φ))) =
      g (dUnit R' (CartierDual.baseChange R R' A ((1 : R') ⊗ₜ φ)))) : f = g := by
  refine AugCot.hom_ext fun ψ => ?_
  obtain ⟨x, rfl⟩ := EquivLike.surjective (CartierDual.baseChange R R' A) ψ
  induction x with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul r φ =>
    have e : r ⊗ₜ[R] φ = r • ((1 : R') ⊗ₜ[R] φ) := by simp [smul_tmul']
    rw [e, map_smul, map_smul, map_smul, map_smul]
    exact congrArg (r • ·) (h φ)

end PrimBaseChange

theorem liftSemi_prim_toBaseChange_bijective {R A : Type} (R' : Type) [CommRing R] [CommRing A]
    [Bialgebra R A] [Module.Finite R A] [Module.Projective R A] [IsCocomm R A] [CommRing R']
    [Algebra R R'] (hC : Module.Projective R (Cot R (CartierDual R A))) :
    Function.Bijective (liftSemi (toBaseChange R R' A).prim) := by
  let u := (CartierDual.toDual R (Cot R (CartierDual R A))).symm.toLinearMap ∘ₗ primTangent R A
  have hu : Function.Bijective u :=
    (CartierDual.toDual R _).symm.bijective.comp (GlobalTheory.T.additiveFunctionCartierDualTangent_bijective (R := R) (A := A))
  have key : ⇑(primTangent R' (R' ⊗[R] A)) ∘ ⇑(liftSemi (toBaseChange R R' A).prim) =
      ⇑(CartierDual.toDual R' _) ∘
        ⇑(CartierDual.transpose (cotBaseChange (R := R) (A := A) R').toLinearMap) ∘
        ⇑(CartierDual.baseChangeLinear R R' (Cot R (CartierDual R A))) ∘
        ⇑(LinearMap.lTensor R' u) := by
    funext x
    induction x with
    | zero => simp
    | add x y hx hy => simp only [Function.comp_apply, map_add] at hx hy ⊢; rw [hx, hy]
    | tmul r b =>
      refine cotBaseChange_hom_ext R' fun φ => ?_
      have h1 : primTangent R' (R' ⊗[R] A) (liftSemi (toBaseChange R R' A).prim (r ⊗ₜ b))
          (dUnit R' (CartierDual.baseChange R R' A ((1 : R') ⊗ₜ φ))) = φ b.1 • r := by
        rw [liftSemi_tmul, map_smul, LinearMap.smul_apply, primTangent_d, SemiBialgHom.prim_val,
          toBaseChange_apply, CartierDual.baseChange_tmul_tmul, smul_comm, mul_one, smul_eq_mul,
          mul_one]
      refine h1.trans (Eq.symm ?_)
      change CartierDual.baseChangeLinear R R' (Cot R (CartierDual R A)) (r ⊗ₜ u b)
        (cotBaseChange R' (dUnit R' (CartierDual.baseChange R R' A ((1 : R') ⊗ₜ φ)))) = _
      rw [cotBaseChange_d, CartierDual.baseChangeLinear_tmul_tmul, mul_one]
      exact congrArg (· • r) (primTangent_d b φ)
  refine (Function.Bijective.of_comp_iff' (GlobalTheory.T.additiveFunctionCartierDualTangent_bijective (R := R') (A := R' ⊗[R] A)) _).1 ?_
  rw [key]
  exact (CartierDual.toDual R' _).bijective.comp <|
    (CartierDual.transpose_bijective (cotBaseChange R').bijective).comp <|
    (CartierDual.baseChangeLinear_bijective R').comp
      (LinearEquiv.lTensor R' (LinearEquiv.ofBijective u hu)).bijective

end PDiv

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjBundleCochainPresheafIsSheafStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projBundleCochainPresheaf_isSheaf : ∀ (R : Type) [CommRing R] (q N : ℕ) (I : Cx R) (n : ℤ), Presheaf.IsSheaf Scheme.etaleTopology.{0} (cotPre R q N I n) := by
  first | (exact @GlobalTheory.EtC.CotSheaf.cotPre_isSheaf) | (exact GlobalTheory.EtC.CotSheaf.cotPre_isSheaf) | (intros; apply GlobalTheory.EtC.CotSheaf.cotPre_isSheaf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjBundleModelCochainComplexIsStrictlyGEStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projBundleModelCochainComplex_isStrictlyGE : ∀ (R : Type) [CommRing R] (q N : ℕ) (I : Cx R), I.IsStrictlyGE 0 → (Jcx R q N I).IsStrictlyGE 0 := by
  first | (exact @GlobalTheory.EtC.Jcx_isStrictlyGE) | (exact GlobalTheory.EtC.Jcx_isStrictlyGE) | (intros; apply GlobalTheory.EtC.Jcx_isStrictlyGE  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveBundleCochainApplyBisimplexStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec GlobalTheory.EZ GlobalTheory.PBFc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projectiveBundleCochain_apply_bisimplex : ∀ (q : ℕ) {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) {B : Spc} (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B) (i : ℤ) (z : ∀ j : Fin N, Cochain ((chains (ZMod q)).obj B) (res _ (tw q ((j : ℕ) : ℤ))) (2 * ((j : ℕ) : ℤ))) (n : ℤ) (α : ∀ j : Fin N, Cochain ((chains (ZMod q)).obj E) (res _ (tw q (i - ((j : ℕ) : ℤ)))) (n - 2 * ((j : ℕ) : ℤ))) (a b : ℕ) (s : ℤ) (h : -((a + b : ℕ) : ℤ) + n = s) (U : Scheme.{0}) (y : BSx (twX E V) a b U), evT (phi q V ℓ i z n α) a b s h U y = ∑ j : Fin N, (twPairI q i ((j : ℕ) : ℤ)).mul U (-(a : ℤ) + (n - 2 * ((j : ℕ) : ℤ))) (-(b : ℤ) + 2 * ((j : ℕ) : ℤ)) s (by push_cast at h; omega) (ev (α j) a _ rfl U (baseS V y)) (ev (z j) b _ rfl U (vertS V ℓ y)) := by
  first | (exact @GlobalTheory.PBFc.evT_phi) | (exact GlobalTheory.PBFc.evT_phi) | (intros; apply GlobalTheory.PBFc.evT_phi  <;> assumption)
end

