import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0011
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0588
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0089
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2409
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0316
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0327
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0134
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNonzeroLocusFormMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0311
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1230
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0083
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0871
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLiftOneParameterQuotientTorus
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsIsGenOfUniqueFactorizationMonoid
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2382
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDVRFiniteMapOfFiniteAlgebra
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.CdvrFiniteAlgebra

theorem exists_cdvr_map_of_finite : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V →
    ∀ (R₁ : Type) [CommRing R₁] [Algebra (FractionRing V) R₁], Module.Finite (FractionRing V) R₁ → Nontrivial R₁ →
      ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (f : V →+* W) (ψ : R₁ →+* FractionRing W),
        GlobalTheory.LN.CDvr W ∧ Function.Injective f ∧ IsLocalHom f ∧ f.Finite ∧
        ∀ a, ψ (algebraMap (FractionRing V) R₁ (algebraMap V _ a)) = algebraMap W _ (f a) := by
  intro V _ _ _ hV R₁ _ _ hfin hnt
  obtain ⟨hdvr, hcomp, hchar⟩ := (GlobalTheory.LN.cDvr_iff V).1 hV
  let K := FractionRing V
  let F := AlgebraicClosure K
  have hchK : CharZero K := IsFractionRing.charZero_of_isFractionRing V
  have hchF : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective

  obtain ⟨m, hm⟩ := Ideal.exists_maximal R₁
  letI : Field (R₁ ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite K (R₁ ⧸ m) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ K m).toLinearMap (Ideal.Quotient.mkₐ_surjective K m)
  haveI : Algebra.IsAlgebraic K (R₁ ⧸ m) := Algebra.IsAlgebraic.of_finite K (R₁ ⧸ m)
  let t : R₁ →ₐ[K] F := (IsAlgClosed.lift : (R₁ ⧸ m) →ₐ[K] F).comp (Ideal.Quotient.mkₐ K m)

  haveI : IsScalarTower V K F := inferInstance
  haveI : FaithfulSMul V F := (faithfulSMul_iff_algebraMap_injective V F).2 (by
    rw [IsScalarTower.algebraMap_eq V K F]
    exact (algebraMap K F).injective.comp (IsFractionRing.injective V K))
  haveI : Algebra.IsAlgebraic V F :=
    (IsFractionRing.comap_isAlgebraic_iff (A := V) (K := K) (C := F)).mpr inferInstance
  obtain ⟨n, b, hb⟩ := Module.Finite.exists_fin (R := K) (M := R₁)
  let s : Finset F := Finset.univ.image (fun i => t (b i))
  obtain ⟨W, hWd, hWc, -, hWfin, -, hWloc, hfrac, -⟩ :=
    GlobalTheory.exists_complete_dvr_finite_subalgebra V F s
  have hWch : CharZero W := ⟨fun m n h => Nat.cast_injective (R := F) (by simpa using congrArg Subtype.val h)⟩
  let φ : FractionRing W →+* F := IsFractionRing.lift (g := W.val.toRingHom) Subtype.val_injective
  have hφ : Function.Injective φ := φ.injective
  have hφa : ∀ w : W, φ (algebraMap W (FractionRing W) w) = w := fun w =>
    IsFractionRing.lift_algebraMap (g := W.val.toRingHom) Subtype.val_injective w
  have hVa : ∀ a : V, ((algebraMap V W a : W) : F) = algebraMap V F a := fun a => rfl
  have hK : ∀ c : K, algebraMap K F c ∈ φ.range := by
    intro c
    obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := V) c
    refine ⟨algebraMap W _ (algebraMap V W x) / algebraMap W _ (algebraMap V W y), ?_⟩
    rw [map_div₀, map_div₀, hφa, hφa, hVa, hVa, IsScalarTower.algebraMap_apply V K F,
      IsScalarTower.algebraMap_apply V K F]
  have hs : ∀ x ∈ s, x ∈ φ.range := by
    intro x hx
    obtain ⟨a, ha, c, hc, hc0, hxc⟩ := hfrac x hx
    refine ⟨algebraMap W _ ⟨a, ha⟩ / algebraMap W _ ⟨c, hc⟩, ?_⟩
    rw [map_div₀, hφa, hφa]
    show a / c = x
    rw [← hxc, mul_div_cancel_right₀ x hc0]
  have hrange : ∀ r, t r ∈ φ.range := by
    intro r
    have hr : r ∈ Submodule.span K (Set.range b) := hb ▸ Submodule.mem_top
    induction hr using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact hs _ (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩)
    | zero => simpa using φ.range.zero_mem
    | add x y _ _ hx hy => simpa using φ.range.add_mem hx hy
    | smul c x _ hx =>
      rw [map_smul, Algebra.smul_def]
      exact φ.range.mul_mem (hK c) hx
  let e : FractionRing W ≃+* φ.range := RingEquiv.ofBijective φ.rangeRestrict
    ⟨fun x y h => hφ (congrArg Subtype.val h), φ.rangeRestrict_surjective⟩
  let ψ : R₁ →+* FractionRing W := e.symm.toRingHom.comp (t.toRingHom.codRestrict φ.range hrange)
  have hψ : ∀ r, φ (ψ r) = t r := fun r =>
    congrArg Subtype.val (e.apply_symm_apply ⟨t r, hrange r⟩)
  refine ⟨W, inferInstance, inferInstance, inferInstance, algebraMap V W, ψ,
    (GlobalTheory.LN.cDvr_iff W).2 ⟨hWd, hWc, hWch⟩, ?_, hWloc, RingHom.finite_algebraMap.2 hWfin, ?_⟩
  · intro x y h
    exact FaithfulSMul.algebraMap_injective V F (congrArg Subtype.val h)
  · intro a
    apply hφ
    rw [hψ, hφa, AlgHom.commutes, hVa, ← IsScalarTower.algebraMap_apply V K F]

end GlobalTheory.CdvrFiniteAlgebra
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDvrFieldValuesDeeperPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ValField

theorem exists_fg_values {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω]
    (M : RatModel o Ω) {K : Type} [Field K] (y : Sp K ⟶ M.Z) :
    ∃ (R : Type) (_ : CommRing R) (_ : Algebra.FiniteType ℤ R) (y₀ : R →+* K),
      ∀ E : Subfield K, (∀ r, y₀ r ∈ E) → ∀ a ∈ M.O (y (closedPoint K)), M.val y a ∈ E := by
  set z := y (closedPoint K) with hz
  obtain ⟨U, hU, hzU, -⟩ := exists_isAffineOpen_mem_and_subset (X := M.Z) (x := z) (U := ⊤) trivial
  have hne : (U : Set M.Z).Nonempty := ⟨z, hzU⟩
  have hr : Set.range y = {z} := RatModel.range_eq_singleton y _
  let φ : M.O z →+* K := RatModel.valHom y z hr
  let y₀ : Γ(M.Z, U) →+* K :=
    φ.comp ((Subalgebra.inclusion (RatModel.ringOn_le_O (M := M) hzU)).toRingHom.comp
      (M.sectionsEquiv U hne).toRingHom)
  have hy₀ : ∀ f, y₀ f = φ ⟨valF M.pt U f, RatModel.valF_mem_O hzU f⟩ := fun f => by
    show φ _ = φ _
    congr 1
    exact Subtype.ext (RatModel.coe_sectionsEquiv U hne f)
  have hft : Algebra.FiniteType ℤ Γ(M.Z, U) := by
    have h1 : (M.s.appLE ⊤ U (by simp)).hom.FiniteType :=
      M.lft.finiteType_appLE (isAffineOpen_top _) hU _
    have h2 : (Scheme.ΓSpecIso (CommRingCat.of o)).inv.hom.FiniteType :=
      RingHom.FiniteType.of_surjective _
        (Scheme.ΓSpecIso (CommRingCat.of o)).commRingCatIsoToRingEquiv.symm.surjective
    have h3 : (algebraMap ℤ o).FiniteType := RingHom.finiteType_algebraMap.2 (ArithBase.ft (o := o) (Ω := Ω))
    have h4 := (h1.comp h2).comp h3
    rw [← RingHom.finiteType_algebraMap]
    convert h4
    exact Subsingleton.elim _ _
  refine ⟨Γ(M.Z, U), inferInstance, hft, y₀, fun E hE a ha => ?_⟩
  let Wo : M.Z.Opens := ⟨{w | a ∈ M.O w}, M.isOpen_setOf_mem_O a⟩
  obtain ⟨f, hfW, hzf⟩ := hU.exists_basicOpen_le (V := Wo) ⟨z, ha⟩ hzU
  have hnef : ((M.Z.basicOpen f : M.Z.Opens) : Set M.Z).Nonempty := ⟨z, hzf⟩
  have har : a ∈ M.ringOn (M.Z.basicOpen f) := RatModel.mem_ringOn.2 fun w hw => hfW hw
  obtain ⟨s, hs⟩ := (RatModel.mem_ringOn_iff_exists hnef).1 har
  letI := hU.isLocalization_basicOpen f
  obtain ⟨n, r, hrn⟩ := IsLocalization.Away.surj f s
  have halg : ∀ g : Γ(M.Z, U), algebraMap Γ(M.Z, U) Γ(M.Z, M.Z.basicOpen f) g = resG M.Z (M.Z.basicOpen_le f) g :=
    fun _ => rfl
  have he := congrArg (M.res _ hnef) hrn
  rw [map_mul, map_pow, halg, halg, RatModel.res_resG, RatModel.res_resG, RatModel.res_apply, hs,
    RatModel.res_apply, RatModel.res_apply] at he

  have hO : (⟨a, ha⟩ : M.O z) * ⟨valF M.pt U f, RatModel.valF_mem_O hzU f⟩ ^ n =
      ⟨valF M.pt U r, RatModel.valF_mem_O hzU r⟩ := Subtype.ext (by simpa using he)
  have hφ := congrArg φ hO
  rw [map_mul, map_pow, ← hy₀, ← hy₀] at hφ
  have hf0 : y₀ f ≠ 0 := by
    rw [hy₀]
    exact (RatModel.val_ne_zero_iff hr _).2 ((RatModel.isUnit_valF_iff hzU f).2 hzf)
  have hval : M.val y a = y₀ r / y₀ f ^ n := by
    rw [← hφ, mul_div_cancel_right₀ _ (pow_ne_zero _ hf0)]
    rfl
  rw [hval]
  exact div_mem (hE r) (pow_mem (hE f) n)

end GlobalTheory.ValField

namespace GlobalTheory.Poinc

theorem exists_complete_dvr_values : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (c : CTrait X₁ p z₁) (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra (FractionRing V) (PadicAlgCl p)], IsAdicComplete (IsLocalRing.maximalIdeal V) V → (∀ x : FractionRing V, ‖algebraMap (FractionRing V) (PadicAlgCl p) x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V))) →
  ∃ (V₂ : Type) (_ : CommRing V₂) (_ : IsDomain V₂) (_ : IsDiscreteValuationRing V₂) (_ : Algebra (FractionRing V₂) (PadicAlgCl p)), IsAdicComplete (IsLocalRing.maximalIdeal V₂) V₂ ∧ (∀ x : FractionRing V₂, ‖algebraMap (FractionRing V₂) (PadicAlgCl p) x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V₂ (FractionRing V₂))) ∧
    ∃ σ : FractionRing V →+* FractionRing V₂, (algebraMap (FractionRing V₂) (PadicAlgCl p)).comp σ = algebraMap (FractionRing V) (PadicAlgCl p) ∧
      ∀ a ∈ D.X.M.O ((gPt p ≫ y) (closedPoint (PadicAlgCl p))), D.X.M.val (gPt p ≫ y) a ∈ (algebraMap (FractionRing V₂) (PadicAlgCl p)).range := by
  intro g n F W Z i X₁ _ _ _ _ _ _ _ ε₁ _ D p _ z₁ c y h V _ _ _ _ hc hV
  obtain ⟨R, _, hR, y₀, hval⟩ := GlobalTheory.ValField.exists_fg_values D.X.M (gPt p ≫ y)
  let κ : FractionRing V →+* PadicAlgCl p := algebraMap (FractionRing V) (PadicAlgCl p)
  haveI : CharZero V := RingHom.charZero (κ.comp (algebraMap V (FractionRing V)))
  have hQ := GlobalTheory.PadicUnitBall.padic_mem_range p V hc κ hV
  obtain ⟨W₂, i₁, i₂, i₃, hcW, -, fV, fK, κ', -, -, -, -, hκ', hunit, hy⟩ :=
    GlobalTheory.DvrFinExt.exists_finite_extension p V hc κ hV hQ R y₀
  letI : Algebra (FractionRing W₂) (PadicAlgCl p) := κ'.toAlgebra
  refine ⟨W₂, i₁, i₂, i₃, κ'.toAlgebra, hcW, hunit, fK, hκ', fun a ha => ?_⟩
  have hm := hval κ'.fieldRange (fun r => by obtain ⟨x, hx⟩ := hy r; exact ⟨x, hx⟩) a ha
  obtain ⟨x, hx⟩ := hm
  exact ⟨x, hx⟩

end GlobalTheory.Poinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoprimeMulPrimePowMemConductor
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open IsDedekindDomain
open GlobalTheory.CMVal (OF Af lattice IsBaseCond IsFinSetSplitPlacesCoprimeConductor condQ hatO)
open GlobalTheory.LatVal (OneOver)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (a0)

namespace GlobalTheory.HilbFam.CondNumber

theorem exists_mul_pow_mem {K : Type} [Field K] [NumberField K] {l : ℕ} (hl : l.Prime) {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    ∃ M j : ℕ, ¬ l ∣ M ∧ (M : 𝓞 K) * (l : 𝓞 K) ^ j ∈ I := by
  have h0 : Ideal.absNorm I ≠ 0 := fun h => hI (Ideal.absNorm_eq_zero_iff.1 h)
  obtain ⟨j, M, hM, he⟩ := Nat.exists_eq_pow_mul_and_not_dvd h0 l hl.ne_one
  refine ⟨M, j, hM, ?_⟩
  have := Ideal.absNorm_mem I
  rw [he] at this
  push_cast at this
  rwa [mul_comm] at this

theorem mem_of_forall_pow {R : Type} [CommRing R] [IsDedekindDomain R] {I : Ideal R} (hI : I ≠ ⊥) {x : R}
    (h : ∀ (v : HeightOneSpectrum R) (n : ℕ), v.asIdeal ^ n ∣ I → x ∈ v.asIdeal ^ n) : x ∈ I := by
  have e := Ideal.iInf_maxPowDividing_eq (I := I) hI
  rw [← e, Submodule.mem_iInf]
  intro v
  apply h v
  rw [Ideal.dvd_iff_le]
  exact e.ge.trans (iInf_le _ v)

theorem exists_mem_condQ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))), l.Prime → IsBaseCond 𝔣 → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) → ∃ M : ℕ, ¬ l ∣ M ∧ ((M * l ^ a0 𝔣 l : ℕ) : OF E) ∈ condQ 𝔣 Q := by
  intro E _ _ _ l 𝔣 Q hl h𝔣 hQ
  obtain ⟨M₁, j, hM₁, hj⟩ := exists_mul_pow_mem hl h𝔣.1
  have h1 : (M₁ : OF E) * (l : OF E) ^ a0 𝔣 l ∈ 𝔣 := by
    refine mem_of_forall_pow h𝔣.1 fun v n hn => ?_
    by_cases hv : (l : OF E) ∈ v.asIdeal
    · have hfin : FiniteMultiplicity v.asIdeal 𝔣 :=
        FiniteMultiplicity.of_not_isUnit v.irreducible.not_isUnit h𝔣.1
      have hle : n ≤ a0 𝔣 l :=
        (hfin.le_multiplicity_of_pow_dvd hn).trans (GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.expIn_le_maxConductorExponentOverPrime h𝔣 hv)
      exact Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right hle (Ideal.pow_mem_pow hv _))
    · have h2 := Ideal.le_of_dvd hn hj
      have := v.isPrime
      rcases Ideal.IsPrime.mem_pow_mul v.asIdeal h2 with h3 | h3
      · exact Ideal.mul_mem_right _ _ h3
      · exact absurd (v.isPrime.mem_of_pow_mem _ h3) hv
  have h2 : ∀ q : HeightOneSpectrum (OF E), ∃ M : ℕ, ¬ l ∣ M ∧ (q ∈ Q → (M : OF E) ∈ q.asIdeal) := by
    intro q
    obtain ⟨M, i, hM, hi⟩ := exists_mul_pow_mem hl q.ne_bot
    refine ⟨M, hM, fun hq => ?_⟩
    rcases q.isPrime.mem_or_mem hi with h3 | h3
    · exact h3
    · exact absurd (q.isPrime.mem_of_pow_mem _ h3) (hQ q hq)
  choose N hN hNq using h2
  refine ⟨M₁ * ∏ q ∈ Q, N q, ?_, ?_⟩
  · intro h
    rcases (Nat.Prime.dvd_mul hl).1 h with h | h
    · exact hM₁ h
    · obtain ⟨q, -, hq⟩ := (Prime.dvd_finset_prod_iff hl.prime _).1 h
      exact hN q hq
  · have h3 : (∏ q ∈ Q, (N q : OF E)) ∈ ∏ q ∈ Q, q.asIdeal := Ideal.prod_mem_prod fun q hq => hNq q hq
    have h4 := Ideal.mul_mem_mul h1 h3
    unfold condQ
    convert h4 using 1
    push_cast
    ring

end GlobalTheory.HilbFam.CondNumber
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoverFunctionFieldEmbedding
section
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.Mean4 GlobalTheory.Mean4O

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Mean4O.NormCover

theorem exists_cover (F : Type) [Field F] [NumberField F] (Y : Var F) (M : TrueGeo.Model Y) (K : Type) [Field K]
    [Algebra Y.Fn K] [FiniteDimensional Y.Fn K] :
    ∃ (V : Cover Y) (ρ : V.X ⟶ M.X) (ψ : K →+* V.G.functionField),
      V.j ≫ ρ = V.π ≫ M.j ∧ ψ.comp (algebraMap Y.Fn K) = V.φ := by
  have := M.ar.isIntegral
  have := M.ar.isLocallyNoetherian
  have : IsProper M.p := CommonModel.isProper_of_isProjOver M.ar.isProjOver
  have : IsPreimmersion M.j := GlobalTheory.TrueGeo.SmallSec.isPreimmersion_j M
  have : CharZero Y.Fn := charZero_of_injective_algebraMap (algebraMap F Y.Fn).injective
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap Y.Fn K).injective
  let η := genericPoint Y.X
  let α : Y.X.presheaf.stalk η ⟶ CommRingCat.of K := CommRingCat.ofHom (algebraMap Y.Fn K)
  let g : Spec (.of K) ⟶ Y.X := Spec.map α ≫ Y.X.fromSpecStalk η
  let β : M.X.presheaf.stalk (M.j η) ⟶ CommRingCat.of K := M.j.stalkMap η ≫ α
  let f : Spec (.of K) ⟶ M.X := Spec.map β ≫ M.X.fromSpecStalk (M.j η)
  have hf : f = g ≫ M.j := by
    simp only [f, g, β, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk]
  have hfin : IsFinite f.fromNormalization := by
    refine GlobalTheory.isFinite_fromNormalization_SpecMap_fromSpecStalk M.p (M.j η) β ?_
    have h1 : (M.j.stalkMap η).hom.FiniteType :=
      RingHom.FiniteType.of_surjective _ (M.j.stalkMap_surjective η)
    have h2 : (algebraMap Y.Fn K).FiniteType := (RingHom.finite_algebraMap.2 inferInstance).finiteType
    exact (RingHom.FiniteType.comp h2 h1).essFiniteType
  have hb := GlobalTheory.isPullback_normalizationMap_of_isLocalization (nonZeroDivisors (𝓞 F)) M.pb
    (GlobalTheory.isPullback_id_of_mono g M.j f hf)
  have : IsFinite g.fromNormalization := MorphismProperty.of_isPullback hb hfin
  let pt : Spec (.of K) := IsLocalRing.closedPoint (CommRingCat.of K)
  have hgη : g pt = η := by
    change Y.X.fromSpecStalk η (Spec.map α pt) = η
    rw [show Spec.map α pt = IsLocalRing.closedPoint (Y.X.presheaf.stalk η) from
      Subsingleton.elim (α := PrimeSpectrum (Y.X.presheaf.stalk η)) _ _]
    exact Scheme.fromSpecStalk_closedPoint
  have hg0 : η ∈ Set.range g := ⟨pt, hgη⟩
  have : IsDominant g := ⟨(dense_iff_closure_eq.2 (genericPoint_spec Y.X)).mono
    (Set.singleton_subset_iff.2 hg0)⟩
  have hfη : f pt = M.j η := by
    rw [hf]
    change M.j (g pt) = M.j η
    rw [hgη]
  have : IsDominant f := by
    refine ⟨?_⟩
    have h0 : M.j η ∈ Set.range f := ⟨pt, hfη⟩
    have h1 : genericPoint M.X ∈ closure (Set.range f) :=
      closure_mono (Set.singleton_subset_iff.2 h0)
        (specializes_iff_mem_closure.1 (GlobalTheory.TrueGeo.SmallSec.j_gen_specializes M) :
          genericPoint M.X ∈ closure ({M.j η} : Set M.X))
    have h2 : closure ({genericPoint M.X} : Set M.X) ⊆ closure (Set.range f) :=
      closure_minimal (Set.singleton_subset_iff.2 h1) isClosed_closure
    rw [show closure ({genericPoint M.X} : Set M.X) = Set.univ from genericPoint_spec M.X] at h2
    exact dense_iff_closure_eq.2 (Set.eq_univ_of_univ_subset h2)
  have : IsDominant g.fromNormalization := by
    have : IsDominant (g.toNormalization ≫ g.fromNormalization) := by
      rw [Scheme.Hom.toNormalization_fromNormalization]; infer_instance
    exact IsDominant.of_comp g.toNormalization g.fromNormalization
  have : IsDominant f.fromNormalization := by
    have : IsDominant (f.toNormalization ≫ f.fromNormalization) := by
      rw [Scheme.Hom.toNormalization_fromNormalization]; infer_instance
    exact IsDominant.of_comp f.toNormalization f.fromNormalization
  have : Surjective g.fromNormalization :=
    surjective_of_isDominant_of_isClosed_range _ g.fromNormalization.isClosedMap.isClosed_range
  have hρs : Surjective f.fromNormalization :=
    surjective_of_isDominant_of_isClosed_range _ f.fromNormalization.isClosedMap.isClosed_range
  have hdim : topologicalKrullDim f.normalization = (Y.dim + 1 : ℕ) := by
    rw [← M.ar.dim_eq]
    refine le_antisymm (ProperCover.dim_le_of_residueDegree_pos f.fromNormalization
      (apply_genericPoint_of_isDominant f.fromNormalization) ?_)
      (PosBaseChange.dim_le_of_isClosedMap f.fromNormalization.isClosedMap hρs.surj)
    let := (f.fromNormalization.residueFieldMap (genericPoint f.normalization)).hom.toAlgebra
    have : Module.Finite (M.X.residueField (f.fromNormalization (genericPoint f.normalization)))
        (f.normalization.residueField (genericPoint f.normalization)) :=
      residueFieldMap_finite_of_locallyQuasiFinite f.fromNormalization _
    exact Module.finrank_pos
  have hc : f ≫ M.p = (g ≫ Y.str) ≫ spMap (algebraMap (𝓞 F) F) := by
    simp only [hf, Category.assoc, M.pb.w]
  have hfl : Flat (f.fromNormalization ≫ M.p) := GlobalTheory.flat_fromNormalization_comp f F M.p (g ≫ Y.str) hc
  have hfZ : Flat (spMap (Int.castRingHom (𝓞 F))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat ℤ (𝓞 F))
  have : GlobalTheory.IsNormalScheme f.normalization := GlobalTheory.IsNormalScheme.normalization_of_isIntegral f
  obtain ⟨hη, ψ, hψ⟩ := GlobalTheory.T.generic_point_morphism_factorization Y.X K g rfl
  let V : Cover Y :=
    { X := f.normalization
      p := f.fromNormalization ≫ M.p
      ar := ⟨M.ar.isDomain, M.ar.finite, inferInstance,
        GlobalTheory.isProjOver_comp_of_finite _ _ _ _ _ hfin M.ar.isProjOver, inferInstance, hdim⟩
      normal := GlobalTheory.IsNormalScheme.pred _
      G := g.normalization
      j := GlobalTheory.normalizationMap g f (𝟙 _) M.j (by simp [hf])
      π := g.fromNormalization
      pb := hb.paste_vert M.pb
      φ := SmallSec.fnMap g.fromNormalization hη
      φ_spec := by
        change _ = Spec.map (Y.X.presheaf.stalkSpecializes hη ≫ g.fromNormalization.stalkMap _) ≫ _
        rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
          Scheme.SpecMap_stalkMap_fromSpecStalk] }
  exact ⟨V, f.fromNormalization, ψ, hb.w, hψ⟩

end GlobalTheory.Mean4O.NormCover
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCubicalStructureMapClosedFibreLocalHom
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option autoImplicit false

noncomputable section
namespace GlobalTheory.UU.ClosedFib

theorem le_comap_max {R W : Type} [CommRing R] [IsLocalRing R] [CommRing W] [IsLocalRing W] (φ : R →+* W)
    (hφ : IsLocalHom φ) : maximalIdeal R ^ (0 + 1) ≤ (maximalIdeal W ^ (0 + 1)).comap φ := by
  simp only [zero_add, pow_one]
  exact fun x hx => (mem_maximalIdeal _).2 fun h => (mem_maximalIdeal _).1 hx (isUnit_of_map_unit φ x h)

theorem spMap_thick {R W : Type} [CommRing R] [IsLocalRing R] [CommRing W] [IsLocalRing W] (φ : R →+* W)
    (hφ : IsLocalHom φ) :
    spMap (Ideal.quotientMap (maximalIdeal W ^ (0 + 1)) φ (le_comap_max φ hφ)) ≫ thick R (maximalIdeal R) 0 =
      thick W (maximalIdeal W) 0 ≫ spMap φ := by
  simp only [spMap, thick, ← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.quotientMap_comp_mk]

theorem exists_isCPMap_closedFibre : ∀ (R W : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing W] [IsDomain W] [IsLocalRing W] (φ : R →+* W), IsLocalHom φ → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (G' : Over (Sp W)) [GrpObj G'] [IsCommMonObj G'] (β : G'.left ⟶ G.left) (hβ : IsGrpPullback G' G (spMap φ) β) (P : GlobalTheory.UU.CP G) (P' : GlobalTheory.UU.CP G') (w : LB.Iso P'.L.L (P.L.L.pull β)), GlobalTheory.UU.IsCPMap P' P (spMap φ) β hβ.1.w w → ∀ (P₀ : GlobalTheory.UU.CP (thickObj R (maximalIdeal R) 0 G)) (P'₀ : GlobalTheory.UU.CP (thickObj W (maximalIdeal W) 0 G')), GlobalTheory.UU.IsLevelCP (maximalIdeal R) 0 P₀ P → GlobalTheory.UU.IsLevelCP (maximalIdeal W) 0 P'₀ P' → ∃ (ρ : R ⧸ maximalIdeal R ^ (0 + 1) →+* W ⧸ maximalIdeal W ^ (0 + 1)) (β₀ : (thickObj W (maximalIdeal W) 0 G').left ⟶ (thickObj R (maximalIdeal R) 0 G).left) (hβ₀ : IsGrpPullback (thickObj W (maximalIdeal W) 0 G') (thickObj R (maximalIdeal R) 0 G) (spMap ρ) β₀) (w₀ : LB.Iso P'₀.L.L (P₀.L.L.pull β₀)), GlobalTheory.UU.IsCPMap P'₀ P₀ (spMap ρ) β₀ hβ₀.1.w w₀ := by
  intro R W _ _ _ _ _ _ φ hφ G _ _ G' _ _ β hβ P P' w hP P₀ P'₀ h₀ h₀'
  let ρ := Ideal.quotientMap (maximalIdeal W ^ (0 + 1)) φ (le_comap_max φ hφ)
  have sq : spMap ρ ≫ thick R (maximalIdeal R) 0 = thick W (maximalIdeal W) 0 ≫ spMap φ := spMap_thick φ hφ
  let β₀ : (thickObj W (maximalIdeal W) 0 G').left ⟶ (thickObj R (maximalIdeal R) 0 G).left :=
    pullback.lift (pullback.fst G'.hom (thick W (maximalIdeal W) 0) ≫ β)
      (pullback.snd G'.hom (thick W (maximalIdeal W) 0) ≫ spMap ρ) (by
        rw [Category.assoc, hβ.1.w, ← Category.assoc, pullback.condition, Category.assoc, Category.assoc, sq])
  have e₁ : β₀ ≫ pullback.fst G.hom (thick R (maximalIdeal R) 0) =
      pullback.fst G'.hom (thick W (maximalIdeal W) 0) ≫ β := pullback.lift_fst _ _ _
  have e₂ : β₀ ≫ (thickObj R (maximalIdeal R) 0 G).hom = (thickObj W (maximalIdeal W) 0 G').hom ≫ spMap ρ :=
    pullback.lift_snd _ _ _
  have n : IsGrpPullback (thickObj W (maximalIdeal W) 0 G') G (spMap ρ ≫ thick R (maximalIdeal R) 0)
      (β₀ ≫ pullback.fst G.hom (thick R (maximalIdeal R) 0)) :=
    (IsGrpPullback.comp (isGrpPullback_pullback G' (thick W (maximalIdeal W) 0)) hβ).congr sq.symm e₁.symm
  have hβ₀ : IsGrpPullback (thickObj W (maximalIdeal W) 0 G') (thickObj R (maximalIdeal R) 0 G) (spMap ρ) β₀ :=
    (isGrpPullback_pullback G (thick R (maximalIdeal R) 0)).cancel n e₂
  obtain ⟨_, hR⟩ := h₀
  obtain ⟨_, hW⟩ := h₀'
  obtain ⟨_, -, hc⟩ := hP.exists_comp hW (by
    rw [Category.assoc, hβ.1.w, ← Category.assoc, pullback.condition, Category.assoc]; rfl)
  obtain ⟨w₀, hw₀⟩ := GlobalTheory.UU.TowerEx.exists_cancel hR hc hβ₀ sq e₁
  exact ⟨ρ, β₀, hβ₀, w₀, hw₀⟩

end GlobalTheory.UU.ClosedFib
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCubicalTrivialisationSplitTorusField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.TorusCubTriv

open GlobalTheory GlobalTheory.UU GlobalTheory.EvenGenTorus TorusCube

theorem exists_cubTriv : ∀ (k : Type) [CommRing k], IsField k → ∀ (G₀ : Over (Sp k)) [GrpObj G₀] [IsCommMonObj G₀] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (P₀ : GlobalTheory.UU.CP G₀) (i : splitTorus (Sp k) X ⟶ G₀), IsMonHom i → Nonempty (GlobalTheory.UU.CubTriv P₀.c i) := by
  intro k _ hk G₀ _ _ X _ _ _ P₀ i hi
  letI := hk.toField
  haveI := hi
  haveI : IsAffine (splitTorus (Sp k) X).left := isAffine_of_isAffineHom (splitTorus (Sp k) X).hom
  haveI := GlobalTheory.SS.LiftTorus.subsingleton_pic_torus k X
  obtain ⟨τ, hτ⟩ := GlobalTheory.LB.exists_isGen_of_subsingleton_pic_top
    (ReciprocityTheory.ChartRestriction.G.Semi.LB.isLB_linComb P₀.L.isLB (K := PUnit) (fun _ => i.left) (fun _ => 1))
  have e1 : (1 : splitTorus (Sp k) X ⟶ splitTorus (Sp k) X).left ≫ i.left = (1 : splitTorus (Sp k) X ⟶ G₀).left := by
    rw [← Over.comp_left, MonObj.one_comp]
  obtain ⟨σ, hσ, vσ⟩ := exists_gen (φ' := ![i.left, (1 : splitTorus (Sp k) X ⟶ G₀).left]) (ε' := ![1, -1]) P₀.L.isLB
    (fun U _ h => (Fintype.prod_sum_type _).trans (by simp [Fin.prod_univ_two, e1]))
    (LB.mulGen _ _ _ _ _ τ (LB.invGen _ _ _ (LB.pullGen P₀.L.L (fun _ : PUnit => i.left) (fun _ => 1) τ
      (1 : splitTorus (Sp k) X ⟶ splitTorus (Sp k) X).left)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hτ (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hτ _)))
  have v : ∀ (T : Over (Sp k)) (x : T ⟶ splitTorus (Sp k) X) (z : T.left) (J), Good P₀.L.L z J →
      val σ x.left z J = val τ x.left z J * (val τ (1 : T ⟶ splitTorus (Sp k) X).left z J)⁻¹ := by
    intro T x z J hJ
    rw [vσ _ _ z J hJ, val_mul hJ, val_inv, val_pull hJ, ← Over.comp_left, MonObj.comp_one]
  refine ⟨⟨σ, hσ, fun T x y u z J hJ => ?_⟩⟩
  have a := cube k X G₀ i P₀.L P₀.c τ hτ T x y u z J hJ
  simp only [v T _ z J hJ]
  apply Additive.ofMul.injective
  have a' := congrArg Additive.ofMul a
  simp only [ofMul_mul, ofMul_inv] at a' ⊢
  linear_combination (norm := abel) a'

end GlobalTheory.Mum.TorusCubTriv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationExtendAdicCompletionLocalizationStatement
section
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_derivation_extend_adicCompletion_localization : ∀ (S : Type) [CommRing S] (P : Ideal S) [P.IsPrime] (d : Derivation ℤ S S), ∃ D : Derivation ℤ (AdicCompletion (maximalIdeal (Localization.AtPrime P)) (Localization.AtPrime P)) (AdicCompletion (maximalIdeal (Localization.AtPrime P)) (Localization.AtPrime P)), ∀ x, D (algebraMap S _ x) = algebraMap S _ (d x) := by
  first | exact @GlobalTheory.derivation_extend_completion_localization_atPrime | exact GlobalTheory.derivation_extend_completion_localization_atPrime | (intros; apply GlobalTheory.derivation_extend_completion_localization_atPrime <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentMorphismToLocalSchemeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_descent_morphism_to_local_scheme : ∀ (R : Type) [CommRing R] [IsDomain R] (f : R), f ≠ 0 → ∀ (x : Sp R) (S₁ B Z B₀ B₁ : Scheme.{0}) (ξ' : S₁ ⟶ Spec ((Sp R).presheaf.stalk x)), Flat ξ' → Surjective ξ' → QuasiCompact ξ' → ∀ (pB : B ⟶ Sp R) (pZ : Z ⟶ Sp R), Flat pB → IsSeparated pZ → ∀ (φ₀ : B₀ ⟶ B) (q₀ : B₀ ⟶ Sp (Localization.Away f)) (u₀ : B₀ ⟶ Z) (φ₁ : B₁ ⟶ B) (q₁ : B₁ ⟶ S₁) (u₁ : B₁ ⟶ Z), IsPullback φ₀ q₀ pB (awayMap f) → IsPullback φ₁ q₁ pB (ξ' ≫ (Sp R).fromSpecStalk x) → u₁ ≫ pZ = φ₁ ≫ pB → (∀ (T : Scheme.{0}) (t₀ : T ⟶ B₀) (t₁ : T ⟶ B₁), t₀ ≫ φ₀ = t₁ ≫ φ₁ → t₀ ≫ u₀ = t₁ ≫ u₁) → ∃ u : Limits.pullback pB ((Sp R).fromSpecStalk x) ⟶ Z, u ≫ pZ = Limits.pullback.fst _ _ ≫ pB ∧ ∀ (T : Scheme.{0}) (t₀ : T ⟶ B₀) (t : T ⟶ Limits.pullback pB ((Sp R).fromSpecStalk x)), t₀ ≫ φ₀ = t ≫ Limits.pullback.fst _ _ → t₀ ≫ u₀ = t ≫ u := by
  first | exact @GlobalTheory.Desc.exists_desc_specStalk | exact GlobalTheory.Desc.exists_desc_specStalk | (intros; apply GlobalTheory.Desc.exists_desc_specStalk <;> assumption)
end

