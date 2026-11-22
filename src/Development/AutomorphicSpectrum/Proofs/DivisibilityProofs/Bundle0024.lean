import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0022
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0016
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GenericFibreLinearEquations
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0019
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0020
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0011
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.IsMultiProjPrimeExtTo

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.DivisorCycleListAdditiveStatement
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divisor_cycle_list_additive : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P d → ∀ (a : K → ℕ) (f : MRing ι O), IsMultiHomog f a → f ∉ P → ∀ (b b' : K → ℤ) (l : List (K → ℤ)), l.length + 1 = d → cycList (divCycle P f) ((b + b') :: l) = cycList (divCycle P f) (b :: l) + cycList (divCycle P f) (b' :: l) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.cycList_divCycle_add_first | exact GlobalTheory.CompanionTheory.Ar.Num.cycList_divCycle_add_first | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.cycList_divCycle_add_first <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FiniteVerticalRecursionStatement
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_vertical_recursion : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι ℤ)) (D : ℕ), IsArithVar P (D + 1) → ∀ (I : Ideal (MRing ι ℤ) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (a : K → ℕ) (s : MRing ι ℤ), IsMultiHomog s a → s ∉ P → ∀ (L : Fin D → HermLine ι) (A : HermLine ι), (Function.support fun p : Nat.Primes => vertAt p P s (List.ofFn fun j => (L j).a)).Finite ∧ recR I P L A s = (∑ᶠ W, (divCycle P s W : ℝ) * Set.indicator {W | IsHorizontal W} (fun W => I W D L) W) + (∑ᶠ p : Nat.Primes, Real.log (p : ℕ) * (vertAt p P s (List.ofFn fun j => (L j).a) : ℝ)) - arInt P s A L := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.RecSplit.recR_split | exact GlobalTheory.CompanionTheory.Ar.Num.RecSplit.recR_split | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.RecSplit.recR_split <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GenericFibreLinearEquationsStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Top.FlDeg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_fibre_linear_equations : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (K : Type) [Fintype K] [DecidableEq K] (j : K → FlBlock Ψ N), IsChain j → ∀ k₀ : K, (∀ k, ((j k).2 : ℕ) ≤ (j k₀).2) → (∃ k, k ≠ k₀) → ∃ G : GenFibre (dropV j k₀) (PPart j), ∃ S : Set (MRingOver G.Φ (fibreIdx (PIdx j) (Subtype.val : {k // k ≠ k₀} → K))), (∀ f ∈ S, IsMultiHomog f fun _ => 1) ∧ fibreIdeal (Subtype.val : {k // k ≠ k₀} → K) G = Ideal.span S := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.FlDeg.FibreLin.fibre_lin | exact GlobalTheory.CompanionTheory.Ar.Top.FlDeg.FibreLin.fibre_lin | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.FlDeg.FibreLin.fibre_lin <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.HodgeComponentFactorPoint
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GenOpen

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
open scoped TensorProduct

theorem mem_range_of_tmul_eq {L Ω : Type} [Field L] [Field Ω] [Algebra L Ω] (x : Ω)
    (h : x ⊗ₜ[L] (1 : Ω) = (1 : Ω) ⊗ₜ[L] x) : x ∈ (algebraMap L Ω).range := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap L Ω)
    (LinearMap.ker_eq_bot.2 (algebraMap L Ω).injective)
  have hg1 : g 1 = 1 := by
    have := LinearMap.congr_fun hg 1
    simpa using this
  let m : Ω ⊗[L] Ω →ₗ[L] Ω := TensorProduct.lid L Ω ∘ₗ TensorProduct.map g LinearMap.id
  have e := congrArg m h
  simp only [m, LinearMap.comp_apply, TensorProduct.map_tmul, TensorProduct.lid_tmul, LinearMap.id_apply, hg1,
    one_smul, LinearEquiv.coe_coe] at e
  exact ⟨g x, by rw [Algebra.algebraMap_eq_smul_one]; exact e⟩

theorem factor_of_epi {O F Ω₀ Ω : Type} [CommRing O] [Field F] [Field Ω₀] [Field Ω]
    (β : O →+* F) (hβ : Epi (CommRingCat.ofHom β)) (a : O →+* Ω₀) (fn : Ω₀ →+* Ω) (cst : F →+* Ω)
    (h : fn.comp a = cst.comp β) : ∃ a' : F →+* Ω₀, a'.comp β = a := by
  let _ := fn.toAlgebra
  have e : CommRingCat.ofHom β ≫
      CommRingCat.ofHom ((Algebra.TensorProduct.includeLeftRingHom : Ω →+* Ω ⊗[Ω₀] Ω).comp cst) =
      CommRingCat.ofHom β ≫
      CommRingCat.ofHom ((Algebra.TensorProduct.includeRight : Ω →ₐ[Ω₀] Ω ⊗[Ω₀] Ω).toRingHom.comp cst) := by
    ext o
    have ho : cst (β o) = algebraMap Ω₀ Ω (a o) := by
      rw [RingHom.algebraMap_toAlgebra]; exact (RingHom.congr_fun h o).symm
    change cst (β o) ⊗ₜ[Ω₀] (1 : Ω) = (1 : Ω) ⊗ₜ[Ω₀] cst (β o)
    rw [ho, Algebra.TensorProduct.tmul_one_eq_one_tmul]
  have e2 := hβ.left_cancellation _ _ e
  have key : ∀ u : F, ∃ w : Ω₀, fn w = cst u := by
    intro u
    have hu := RingHom.congr_fun (congrArg CommRingCat.Hom.hom e2) u
    change cst u ⊗ₜ[Ω₀] (1 : Ω) = (1 : Ω) ⊗ₜ[Ω₀] cst u at hu
    obtain ⟨w, hw⟩ := mem_range_of_tmul_eq (L := Ω₀) (cst u) hu
    exact ⟨w, by rw [← hw, RingHom.algebraMap_toAlgebra]⟩
  choose g hg using key
  have inj := fn.injective
  refine ⟨{ toFun := g
            map_one' := inj (by rw [hg, map_one, map_one])
            map_mul' := fun x y => inj (by rw [hg, map_mul, map_mul, hg, hg])
            map_zero' := inj (by rw [hg, map_zero, map_zero])
            map_add' := fun x y => inj (by rw [hg, map_add, map_add, hg, hg]) }, ?_⟩
  ext o
  apply inj
  change fn (g (β o)) = fn (a o)
  rw [hg]
  exact (RingHom.congr_fun h o).symm

theorem eq_genPt_of_specializes {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (h : IsCptGen ξ) (y : X) (hy : y ⤳ genPt ξ) : y = genPt ξ := by
  have hf : IsField (X.presheaf.stalk (genPt ξ)) :=
    (RingEquiv.ofBijective _ h.bij).toMulEquiv.isField (Field.toIsField Ω)
  have : y ∈ Set.range (X.fromSpecStalk (genPt ξ)) := by rwa [Scheme.range_fromSpecStalk]
  obtain ⟨q, rfl⟩ := this
  let _ := hf.toField
  have : q = IsLocalRing.closedPoint (X.presheaf.stalk (genPt ξ)) :=
    Subsingleton.elim (α := PrimeSpectrum _) _ _
  rw [this, Scheme.fromSpecStalk_closedPoint]

theorem mem_of_dense_of_noGen {P : Type} [TopologicalSpace P] [TopologicalSpace.NoetherianSpace P] [QuasiSober P]
    {U : Set P} (hU : IsOpen U) (hd : Dense U) {y : P} (hy : ∀ y', y' ⤳ y → y' = y) : y ∈ U := by
  classical
  have hCi : IsIrreducible (irreducibleComponent y) := isIrreducible_irreducibleComponent
  have hCc : IsClosed (irreducibleComponent y) := isClosed_irreducibleComponent
  have hgen := hCi.isGenericPoint_genericPoint_closure
  rw [hCc.closure_eq] at hgen
  have hη : hCi.genericPoint = y := hy _ (hgen.specializes mem_irreducibleComponent)
  rw [hη] at hgen
  have hmax := irreducibleComponent_mem_irreducibleComponents y
  set D : Set P := ⋃₀ (irreducibleComponents P \ {irreducibleComponent y}) with hD
  have hDc : IsClosed D := by
    rw [hD, Set.sUnion_eq_biUnion]
    exact Set.Finite.isClosed_biUnion
      (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.subset Set.sdiff_subset)
      fun C hC => isClosed_of_mem_irreducibleComponents C hC.1
  have hyD : y ∉ D := by
    rintro ⟨C, ⟨hC, hne⟩, hyC⟩
    have hle : irreducibleComponent y ⊆ C := by
      rw [← hgen.def]
      exact (isClosed_of_mem_irreducibleComponents C hC).closure_subset_iff.2 (by simpa using hyC)
    exact hne (le_antisymm (hmax.2 hC.1 hle) hle)
  obtain ⟨u, huD, huU⟩ := hd.inter_open_nonempty Dᶜ hDc.isOpen_compl ⟨y, hyD⟩
  have huC : u ∈ irreducibleComponent y := by
    by_contra hne
    refine huD ⟨irreducibleComponent u, ⟨irreducibleComponent_mem_irreducibleComponents u, ?_⟩,
      mem_irreducibleComponent⟩
    intro e
    exact hne (by
      have : u ∈ irreducibleComponent u := mem_irreducibleComponent
      rw [Set.mem_singleton_iff.1 e] at this
      exact this)
  exact (hgen.specializes huC).mem_open hU huU

theorem noetherianSpace_baseChange {X : Scheme.{0}} {O F : Type} [CommRing O] [Field F] {s : X ⟶ Sp O}
    (hs : IsProjOver s) (β : O →+* F) : TopologicalSpace.NoetherianSpace ↥(pullback s (spMap β)) := by
  obtain ⟨N, i, hi, rfl⟩ := hs
  have := isProper_str O N
  have : IsProper (i ≫ PSpace.str O N) := inferInstance
  have hl : LocallyOfFiniteType (pullback.snd (i ≫ PSpace.str O N) (spMap β)) := inferInstance
  have hq : QuasiCompact (pullback.snd (i ≫ PSpace.str O N) (spMap β)) := inferInstance
  have : IsLocallyNoetherian (pullback (i ≫ PSpace.str O N) (spMap β)) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd _ _)
  have : CompactSpace ↥(pullback (i ≫ PSpace.str O N) (spMap β)) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd _ _)
  have : IsNoetherian (pullback (i ≫ PSpace.str O N) (spMap β)) := {}
  infer_instance

theorem gen_open : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H)
    (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ)
    (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (A : HodgeCpt Y S y),
    Mono (spMap β) → ∃ x : Sp A.Ω₀ ⟶ Xo.XF c, A.ξ₀ = x ≫ Y.j := by
  intro E _ _ _ H D l Xo c O _ β Y S Ω _ K _ J y A hmono
  have hepi : Epi (CommRingCat.ofHom β) := by
    have h1 : Mono (Scheme.Spec.map (CommRingCat.ofHom β).op) := hmono
    have h2 : Mono (CommRingCat.ofHom β).op := Scheme.Spec.mono_of_mono_map h1
    exact unop_epi_of_mono (CommRingCat.ofHom β).op
  let a : O →+* A.Ω₀ := (Spec.preimage (A.ξ₀ ≫ Y.s)).hom
  have ha : spMap a = A.ξ₀ ≫ Y.s := by
    simp only [spMap, a, CommRingCat.ofHom_hom, Spec.map_preimage]
  have hfa : A.fn.comp a = A.cst.comp β := by
    have h1 : spMap (A.fn.comp a) = spMap (A.cst.comp β) := by
      rw [← A.cst_over]
      have hd : A.ξ ≫ A.f = spMap A.fn ≫ A.ξ₀ := A.fn_over
      calc spMap (A.fn.comp a) = spMap A.fn ≫ spMap a := by
            simp only [spMap, ← Spec.map_comp]; rfl
        _ = A.ξ ≫ A.f ≫ Y.s := by rw [ha, ← Category.assoc, ← hd, Category.assoc]
    have h2 := Spec.map_injective h1
    exact congrArg CommRingCat.Hom.hom h2
  obtain ⟨a', ha'⟩ := factor_of_epi β hepi a A.fn A.cst hfa
  have hsq : A.ξ₀ ≫ Y.s = spMap a' ≫ spMap β := by
    rw [← ha, ← ha']
    simp only [spMap, ← Spec.map_comp]; rfl
  let z : Sp A.Ω₀ ⟶ pullback Y.s (spMap β) := pullback.lift A.ξ₀ (spMap a') hsq
  have hz : z ≫ pullback.fst _ _ = A.ξ₀ := pullback.lift_fst _ _ _
  let y0 : ↥(pullback Y.s (spMap β)) := z (IsLocalRing.closedPoint A.Ω₀)
  have hfst : pullback.fst Y.s (spMap β) y0 = genPt A.ξ₀ := by
    show (pullback.fst Y.s (spMap β)) (z _) = A.ξ₀ _
    rw [← hz]
    rfl
  have hmax : ∀ y', y' ⤳ y0 → y' = y0 := by
    intro y' hy
    have h1 : pullback.fst Y.s (spMap β) y' ⤳ genPt A.ξ₀ := hfst ▸ hy.map (pullback.fst Y.s (spMap β)).continuous
    have h2 := eq_genPt_of_specializes A.ξ₀ A.gen₀ _ h1
    exact (pullback.fst Y.s (spMap β)).injective (h2.trans hfst.symm)
  have := noetherianSpace_baseChange Y.proj β
  have := Y.jQ_open
  have hy0 : y0 ∈ Set.range Y.jQ :=
    mem_of_dense_of_noGen Y.jQ.isOpenEmbedding.isOpen_range Y.jQ_dense hmax
  have hrange : Set.range z ⊆ Set.range Y.jQ := by
    rintro _ ⟨p, rfl⟩
    have : p = IsLocalRing.closedPoint A.Ω₀ := Subsingleton.elim (α := PrimeSpectrum A.Ω₀) _ _
    rw [this]
    exact hy0
  refine ⟨IsOpenImmersion.lift Y.jQ z hrange, ?_⟩
  show A.ξ₀ = IsOpenImmersion.lift Y.jQ z hrange ≫ Y.jQ ≫ pullback.fst _ _
  rw [← Category.assoc, IsOpenImmersion.lift_fac, hz]

end GlobalTheory.CompanionTheory.Ar.GenOpen
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.IntersectionNumberFieldEquivStatement
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersection_number_field_equiv : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (F F' : Type) [Field F] [Field F'] (e : F ≃+* F') (V : Ideal (MRing ι F)) (l : List (K → ℤ)), intNumL F' (V.map (MvPolynomial.map (e : F →+* F'))) l = intNumL F V l := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.intNumL_map_ringEquiv | exact GlobalTheory.CompanionTheory.Ar.Num.intNumL_map_ringEquiv | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.intNumL_map_ringEquiv <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.IntersectionSystemDegreeStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersection_system_degree : ∀ II : IntersectionSystem, IsIntersectionSystem II → ReciprocityTheory.ChartRestriction.G.Geo.DegreeStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.degreeStatement_of_intersectionSystem | exact GlobalTheory.CompanionTheory.Ar.Top.degreeStatement_of_intersectionSystem | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.degreeStatement_of_intersectionSystem <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.LinRootRemainderBoundStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lin_root_remainder_bound : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ) (bad : Finset ℕ) (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ) (u : Wt Ψ N) (g : ℝ) (B : ℕ) (Q : Ψ → ℕ → RP Ψ N), 1 ≤ j → j < N → WeightHyp j u g → bigB0 u g < B + 1 → IsDecomp (linRoot u ^ (dimFl Ψ N + 1)) Q → |∑ τ, ∑ k ∈ Finset.Icc 1 N, restSum j bad frob B τ k (Q τ k)| ≤ 2 * (((dimFl Ψ N : ℝ) + 1) * flagDeg u) * ((min j (N - j) : ℕ) * spread u) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.restSum_total_bound | exact GlobalTheory.CompanionTheory.Ar.Top.restSum_total_bound | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.restSum_total_bound <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.VerticalNumberLocalCycle
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

namespace GlobalTheory.CompanionTheory.Ar.Num.ZpVert

noncomputable section

attribute [local instance] MvPolynomial.algebraMvPolynomial

variable {K : Type} {ι : K → Type}

theorem nonempty_residue_equiv (p : Nat.Primes) [Fact (p : ℕ).Prime] :
    Nonempty (ZMod (p : ℕ) ≃+* IsLocalRing.ResidueField (ZP p)) := by
  haveI hmax : (Ideal.span {((p : ℕ) : ℤ)}).IsMaximal :=
    Ideal.IsPrime.isMaximal inferInstance
      (by rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast p.2.ne_zero)
  exact ⟨(Int.quotientSpanNatEquivZMod (p : ℕ)).symm.trans
    (IsLocalization.AtPrime.equivQuotMaximalIdeal (Ideal.span {((p : ℕ) : ℤ)}) (ZP p))⟩

theorem map_extTo {R S : Type} [CommRing R] [CommRing S] (g : R →+* S) (Q : Ideal (MRing ι ℤ)) :
    (extTo R Q).map (MvPolynomial.map g) = extTo S Q := by
  unfold extTo
  rw [Ideal.map_map]
  congr 1
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
  · simp
  · simp

theorem vNumL_extTo [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] (p : Nat.Primes)
    [Fact (p : ℕ).Prime] (Q : Ideal (MRing ι ℤ)) (l : List (K → ℤ)) :
    vNumL (extTo (ZP p) Q) l = intNumL (ZMod (p : ℕ)) (extTo (ZMod (p : ℕ)) Q) l := by
  obtain ⟨e⟩ := nonempty_residue_equiv p
  have h : specialIdeal (extTo (ZP p) Q) =
      (extTo (ZMod (p : ℕ)) Q).map (MvPolynomial.map (e : ZMod (p : ℕ) →+* _)) := by
    unfold specialIdeal
    rw [map_extTo, map_extTo]
  have h2 := intNumL_map_ringEquiv K ι (ZMod (p : ℕ)) (IsLocalRing.ResidueField (ZP p)) e
    (extTo (ZMod (p : ℕ)) Q) l
  rw [← h2, ← h]
  rfl

theorem divCycle_extTo [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] (p : Nat.Primes)
    (P : Ideal (MRing ι ℤ)) (f : MRing ι ℤ) (W' : Ideal (MRing ι (ZP p))) (hW' : W'.IsPrime) :
    divCycle (extTo (ZP p) P) (MvPolynomial.map (Int.castRingHom (ZP p)) f) W' =
      divCycle P f (W'.comap (MvPolynomial.map (Int.castRingHom (ZP p)))) := by
  have h := divCycle_map_localisation K ι ℤ (ZP p) (Ideal.span {((p : ℕ) : ℤ)}).primeCompl P f W' hW'
  have e : algebraMap ℤ (ZP p) = Int.castRingHom (ZP p) := RingHom.ext_int _ _
  rw [e] at h
  exact h

theorem isPrime_of_ne {R : Type} [CommRing R] {P : Ideal (MRing ι R)} {f : MRing ι R}
    {W : Ideal (MRing ι R)} (h : divCycle P f W ≠ 0) : W.IsPrime := by
  unfold divCycle at h
  split_ifs at h with hc
  · exact hc.1.1.1
  · exact absurd rfl h

theorem disjoint_consts_of_mem (p : Nat.Primes) {W : Ideal (MRing ι ℤ)} (hW : W.IsPrime)
    (hp : (C ((p : ℕ) : ℤ) : MRing ι ℤ) ∈ W) :
    Disjoint (ZpModel.consts ι p : Set (MRing ι ℤ)) (W : Set (MRing ι ℤ)) := by
  refine Set.disjoint_left.2 ?_
  rintro _ ⟨s, hs, rfl⟩ hmem
  have hs' : s ∉ Ideal.span {((p : ℕ) : ℤ)} := hs
  have hdvd : ¬ ((p : ℕ) : ℤ) ∣ s := fun h => hs' (Ideal.mem_span_singleton.2 h)
  obtain ⟨u, v, huv⟩ := (Nat.prime_iff_prime_int.1 p.2).irreducible.coprime_iff_not_dvd.2 hdvd
  have h1 : (C (u * ((p : ℕ) : ℤ) + v * s) : MRing ι ℤ) ∈ W := by
    rw [C_add, C_mul, C_mul]
    exact W.add_mem (W.mul_mem_left _ hp) (W.mul_mem_left _ hmem)
  rw [huv, C_1] at h1
  exact hW.ne_top ((Ideal.eq_top_iff_one W).2 h1)

theorem finsum_eq_mem {α : Type*} (g : α → ℤ) (t : Set α) (h : Function.support g ⊆ t) :
    ∑ᶠ x, g x = ∑ᶠ x ∈ t, g x := by
  rw [← finsum_mem_univ g]
  refine finsum_mem_inter_support_eq g _ _ ?_
  rw [Set.univ_inter, Set.inter_eq_right.2 h]

theorem extTo_comap (p : Nat.Primes) (W' : Ideal (MRing ι (ZP p))) :
    extTo (ZP p) (W'.comap (MvPolynomial.map (Int.castRingHom (ZP p)))) = W' := by
  haveI := ZpModel.isLocalization_consts ι p
  rw [ZpModel.extTo_eq, ← ZpModel.algebraMap_eq]
  exact IsLocalization.map_comap (ZpModel.consts ι p) (MRing ι (ZP p)) W'

theorem bijOn_comap [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] (p : Nat.Primes)
    (P : Ideal (MRing ι ℤ)) (f : MRing ι ℤ) :
    Set.BijOn (fun W' : Ideal (MRing ι (ZP p)) => W'.comap (MvPolynomial.map (Int.castRingHom (ZP p))))
      {W' | divCycle (extTo (ZP p) P) (MvPolynomial.map (Int.castRingHom (ZP p)) f) W' ≠ 0 ∧
        (C ((p : ℕ) : ZP p) : MRing ι (ZP p)) ∈ W'}
      {W | divCycle P f W ≠ 0 ∧ (C ((p : ℕ) : ℤ) : MRing ι ℤ) ∈ W} := by
  have hCmap : MvPolynomial.map (Int.castRingHom (ZP p)) (C ((p : ℕ) : ℤ) : MRing ι ℤ) =
      (C ((p : ℕ) : ZP p) : MRing ι (ZP p)) := by
    rw [map_C]
    simp
  haveI := ZpModel.isLocalization_consts ι p
  refine ⟨?_, ?_, ?_⟩
  · rintro W' ⟨hW', hp⟩
    refine ⟨?_, ?_⟩
    · rw [← divCycle_extTo p P f W' (isPrime_of_ne hW')]
      exact hW'
    · show MvPolynomial.map (Int.castRingHom (ZP p)) (C ((p : ℕ) : ℤ) : MRing ι ℤ) ∈ W'
      rwa [hCmap]
  · rintro W₁ - W₂ - h
    calc W₁ = extTo (ZP p) (W₁.comap (MvPolynomial.map (Int.castRingHom (ZP p)))) := (extTo_comap p W₁).symm
      _ = extTo (ZP p) (W₂.comap (MvPolynomial.map (Int.castRingHom (ZP p)))) := congrArg _ h
      _ = W₂ := extTo_comap p W₂
  · rintro W ⟨hW, hp⟩
    have hWp : W.IsPrime := isPrime_of_ne hW
    have hd := disjoint_consts_of_mem p hWp hp
    have hprime : (extTo (ZP p) W).IsPrime := by
      rw [ZpModel.extTo_eq]
      exact IsLocalization.isPrime_of_isPrime_disjoint (ZpModel.consts ι p) _ W hWp hd
    have hcomap : (extTo (ZP p) W).comap (MvPolynomial.map (Int.castRingHom (ZP p))) = W := by
      have h := IsLocalization.under_map_of_isPrime_disjoint (ZpModel.consts ι p) (MRing ι (ZP p)) hWp hd
      rw [ZpModel.extTo_eq, ← ZpModel.algebraMap_eq]
      exact h
    refine ⟨extTo (ZP p) W, ⟨?_, ?_⟩, hcomap⟩
    · rw [divCycle_extTo p P f _ hprime, hcomap]
      exact hW
    · rw [← hCmap]
      exact Ideal.mem_map_of_mem _ hp

end

end GlobalTheory.CompanionTheory.Ar.Num.ZpVert

open GlobalTheory.CompanionTheory.Ar.Num.ZpVert in

theorem GlobalTheory.CompanionTheory.Ar.Num.vertAt_eq_cycList : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι ℤ)) (D : ℕ), IsArithVar P (D + 1) → ∀ (p : Nat.Primes) (a : K → ℕ) (f : MRing ι ℤ), IsMultiHomog f a → f ∉ P → ∀ l : List (K → ℤ), l.length = D → vertAt p P f l = cycList (divCycle (extTo (ZP p) P) (MvPolynomial.map (Int.castRingHom (ZP p)) f)) l := by
  intro K _ _ ι _ P D hP p a f hf hfP l hl
  classical
  haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
  obtain ⟨hirr, hmodel, -⟩ := zp_model K ι P D hP p
  have hfP' : MvPolynomial.map (Int.castRingHom (ZP p)) f ∉ extTo (ZP p) P :=
    fun h => hfP (ZpModel.mem_of_map_mem p hP.2.1.1 hP.2.2.1 h)
  have hf' : IsMultiHomog (MvPolynomial.map (Int.castRingHom (ZP p)) f) a := by
    intro d hd
    refine hf fun h0 => hd ?_
    rw [coeff_map, h0, map_zero]
  unfold vertAt cycList cycEval
  rw [finsum_eq_mem _ {W | divCycle P f W ≠ 0 ∧ (C ((p : ℕ) : ℤ) : MRing ι ℤ) ∈ W},
    finsum_eq_mem _ {W' | divCycle (extTo (ZP p) P) (MvPolynomial.map (Int.castRingHom (ZP p)) f) W' ≠ 0 ∧
        (C ((p : ℕ) : ZP p) : MRing ι (ZP p)) ∈ W'}]
  · symm
    refine finsum_mem_eq_of_bijOn _ (bijOn_comap p P f) ?_
    rintro W' ⟨hW', hp⟩
    have hWp : W'.IsPrime := isPrime_of_ne hW'
    have hQp : (C ((p : ℕ) : ℤ) : MRing ι ℤ) ∈ W'.comap (MvPolynomial.map (Int.castRingHom (ZP p))) := by
      show MvPolynomial.map (Int.castRingHom (ZP p)) (C ((p : ℕ) : ℤ) : MRing ι ℤ) ∈ W'
      rw [map_C]
      simpa using hp
    rw [divCycle_extTo p P f W' hWp]
    beta_reduce
    rw [if_pos hQp]
    congr 1
    have h := vNumL_extTo p (W'.comap (MvPolynomial.map (Int.castRingHom (ZP p)))) l
    rw [extTo_comap] at h
    exact h
  · intro W' hW'
    have h1 := left_ne_zero_of_mul hW'
    refine ⟨h1, ?_⟩
    by_contra hp
    have h0 := GlobalTheory.T.vertical_number_zero_of_horizontal (ZP p) ((p : ℕ) : ZP p) hirr K ι (extTo (ZP p) P) D hmodel a _ hf' hfP' W' h1 hp l hl
    exact right_ne_zero_of_mul hW' h0
  · intro W hW
    have h1 := left_ne_zero_of_mul hW
    refine ⟨h1, ?_⟩
    by_contra hp
    exact right_ne_zero_of_mul hW (if_neg hp)
end

