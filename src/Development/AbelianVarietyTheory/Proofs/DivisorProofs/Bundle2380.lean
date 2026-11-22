import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2319
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2347
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2353
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2321
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2322
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2323
import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0018
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0659
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0112
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2336
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2320
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0067
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0151
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0102
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2267
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2287
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2364
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2324
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2291

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartierLocusOverDenseOpenBase
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.DivStart

theorem exists_locus_over_dense_open : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [IsDomain R] [IsIntegrallyClosed R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ V : A.left.Opens, IsAffineOpen V → (∀ s : Sp R, ∃ x ∈ V, A.hom x = s) → ∃ (U : (Sp R).Opens) (c : Pic (A.hom ⁻¹ᵁ U ⊔ V).toScheme), (U : Set (Sp R)).Nonempty ∧ IsLocus c ((A.hom ⁻¹ᵁ U ⊔ V).ι ⁻¹ᵁ V) := by
  intro R _ _ _ _ A _ hA V hV hsurj
  have := hA.smooth
  have := hA.proper
  have : GeometricallyIntegral A.hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hA.smooth hA.geomConnected
  have : IsLocallyNoetherian (Sp R) := inferInstance
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian A.hom
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  have : A.left.IsSeparated := ⟨by rw [← terminal.comp_from A.hom]; infer_instance⟩
  let s₀ : Sp R := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)
  obtain ⟨x₀, hx₀, -⟩ := hsurj s₀
  obtain ⟨W₀, hVW, hufd, c₀, hc₀⟩ := GlobalTheory.FactorialLocus.exists_isLocus A.left V hV ⟨x₀, hx₀⟩
  have hfib : ∀ x, A.hom x = s₀ → x ∈ W₀ := fun x hx =>
    hufd x (GlobalTheory.GenericFibreFactorial.ufd_stalk_of_generic R A.left A.hom x (by rw [hx]))
  obtain ⟨U, -, hsU, hUW⟩ := GlobalTheory.Tube.exists_affine_preimage_le A.left (Sp R) A.hom s₀ W₀ hfib
  have hle : A.hom ⁻¹ᵁ U ⊔ V ≤ W₀ := sup_le hUW hVW
  refine ⟨U, GlobalTheory.CechPic.pull (A.left.homOfLE hle) c₀, ⟨s₀, hsU⟩, ?_⟩
  have h := GlobalTheory.LocusPull.isLocus_pull (A.left.homOfLE hle) hc₀
  convert h using 1
  ext x
  change (A.hom ⁻¹ᵁ U ⊔ V).ι x ∈ V ↔ W₀.ι (A.left.homOfLE hle x) ∈ V
  rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]

end GlobalTheory.DivStart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartierSectionLocusOfAmpleSpan
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

noncomputable section

namespace GlobalTheory.Desc

theorem unitAt_of_mul_right {X : Scheme.{0}} [IsIntegral X] {x : X} {a b : X.functionField}
    (ha : RegAt x a) (hb : RegAt x b) (h : UnitAt x (a * b)) : UnitAt x b := by
  obtain ⟨a', rfl⟩ := ha
  obtain ⟨b', rfl⟩ := hb
  obtain ⟨w, hw, e⟩ := h
  rw [← map_mul] at e
  obtain rfl := IsFractionRing.injective (X.presheaf.stalk x) X.functionField e
  exact ⟨b', isUnit_of_mul_isUnit_right hw, rfl⟩

theorem regAt_cst {R : Type} [CommRing R] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp R) (x : X) (r : R) :
    RegAt x (cst p r) :=
  regAt_fnOf (x := x) (U := ⊤) trivial trivial _

theorem exists_locus_of_span : ∀ (R₁ F : Type) [CommRing R₁] [Field F] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp R₁) (θ : F →+* Y.functionField) (N : ℕ → Set F) (D₁ : CartierDiv Y), AmpleDiv D₁ → (∀ k, Sec D₁ k = spanBy (GlobalTheory.Desc.cst q) (θ '' N k)) → ∀ y : Y, ∃ k, 1 ≤ k ∧ ∃ b ∈ N k, y ∈ locus D₁ k (θ b) := by
  intro R₁ F _ _ Y _ q θ N D₁ hA hS y
  obtain ⟨k, hk, u, hu, U, -, hU, hy⟩ := hA y
  have hyu : y ∈ locus D₁ k u := hU ▸ hy
  have hu' : u ∈ spanBy (cst q) (θ '' N k) := hS k ▸ hu
  obtain ⟨n, r, t, ht, rfl⟩ := hu'
  obtain ⟨g, hg⟩ := (k • D₁).exists_isEqn y
  have hunit : UnitAt y ((∑ i, cst q (r i) * t i) * g) := hg.generatesAt_iff.1 hyu
  have hsec : ∀ i, RegAt y (t i * g) := fun i => by
    have : t i ∈ Sec D₁ k := by rw [hS k]; exact subset_spanBy _ _ (ht i)
    exact hg.regularAt_iff.1 (this y)
  by_contra hne
  push_neg at hne
  apply (zeroAt_iff.1 ?_).2 hunit
  rw [Finset.sum_mul]
  refine Finset.sum_induction _ (ZeroAt y) (fun _ _ => ZeroAt.add) (zeroAt_zero y) fun i _ => ?_
  rw [_root_.mul_assoc]
  refine zeroAt_iff.2 ⟨(regAt_cst q y (r i)).mul (hsec i), fun hu => ?_⟩
  obtain ⟨b, hb, hbt⟩ := ht i
  apply hne k hk b hb
  show (k • D₁).GeneratesAt y (θ b)
  rw [hg.generatesAt_iff, hbt]
  exact unitAt_of_mul_right (regAt_cst q y (r i)) (hsec i) hu

end GlobalTheory.Desc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechCocycleOneOnThickeningStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cechCocycle_one_on_thickening : ∀ (X X₀ : Scheme.{0}) (i : X₀ ⟶ X) [IsClosedImmersion i] [Surjective i] (c : Pic X), GlobalTheory.CechPic.pull i c = 0 → ∃ (D : LB X) (hD : D.IsLB), cls D hD = c ∧ ∀ a b, pullU i _ (D.g a b) = 1 := by
  first | exact @GlobalTheory.CechPic.exists_cocycle_one_on_thickening | exact GlobalTheory.CechPic.exists_cocycle_one_on_thickening | (intros; apply GlobalTheory.CechPic.exists_cocycle_one_on_thickening <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechPicardGlueFiniteDisjointCoverStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cechPicard_glue_finite_disjoint_cover : ∀ {Y : Scheme.{0}} {κ : Type} [Finite κ] {Z : κ → Scheme.{0}} (f : ∀ i, Z i ⟶ Y) [∀ i, IsOpenImmersion (f i)], (⨆ i, (f i).opensRange = ⊤) → (Pairwise fun i i' => Disjoint (f i).opensRange (f i').opensRange) → ∀ c : ∀ i, Pic (Z i), ∃ d : Pic Y, ∀ i, GlobalTheory.CechPic.pull (f i) d = c i := by
  first | exact @GlobalTheory.CechPic.Glue.exists_pic_glue | exact GlobalTheory.CechPic.Glue.exists_pic_glue | (intros; apply GlobalTheory.CechPic.Glue.exists_pic_glue <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChartFiniteEtaleCoverGenericPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

noncomputable section
namespace GlobalTheory.Poinc.Chart

theorem stalkMap_finite_of_chart (K A : Type) [Field K] [CommRing A] {X Y : Scheme.{0}} (q : Y ⟶ X) (j : Sp A ⟶ Y)
    (φ : A →+* K) [IsFinite q] [IsOpenImmersion j] (hφ : ∀ z : K, ∃ a c : A, z = φ a / φ c) (g : Sp K ⟶ X)
    (hg : g = spMap φ ≫ j ≫ q) : (g.stalkMap (genericPoint (Sp K))).hom.Finite := by
  rw [← Category.assoc] at hg
  subst hg
  have hpt : genericPoint (Sp K) = closedPoint (CommRingCat.of K) := Subsingleton.elim _ _
  rw [hpt]
  have h1 : ((spMap φ ≫ j) ≫ q).stalkMap (closedPoint (CommRingCat.of K)) =
      Scheme.stalkClosedPointTo ((spMap φ ≫ j) ≫ q) ≫ (stalkClosedPointIso (CommRingCat.of K)).inv :=
    (Iso.eq_comp_inv _).2 rfl
  rw [h1]
  refine RingHom.Finite.comp (RingHom.Finite.of_surjective _
    (ConcreteCategory.bijective_of_isIso (stalkClosedPointIso (CommRingCat.of K)).inv).2) ?_
  rw [Scheme.stalkClosedPointTo_comp]
  set τ := Scheme.stalkClosedPointTo (spMap φ ≫ j) with hτdef
  have h2 : q.stalkMap _ ≫ τ = (X.residue _ ≫ q.residueFieldMap _) ≫ Y.descResidueField τ := by
    rw [Scheme.residue_residueFieldMap, Category.assoc, Scheme.residue_descResidueField]
  have hτ : ∀ a : A, ∃ s, τ.hom s = φ a := by
    intro a
    have h3 : τ = j.stalkMap _ ≫ Scheme.stalkClosedPointTo (spMap φ) := Scheme.stalkClosedPointTo_comp _ _
    have h5 : (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
        (Spec (CommRingCat.of A)).presheaf.germ ⊤ ((spMap φ) (closedPoint (CommRingCat.of K))) trivial ≫
        inv (j.stalkMap ((spMap φ) (closedPoint (CommRingCat.of K)))) ≫
        j.stalkMap ((spMap φ) (closedPoint (CommRingCat.of K))) ≫ Scheme.stalkClosedPointTo (spMap φ) =
        CommRingCat.ofHom φ := by
      rw [IsIso.inv_hom_id_assoc, Scheme.germ_stalkClosedPointTo_Spec, Iso.inv_hom_id_assoc]
    refine ⟨((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
        (Spec (CommRingCat.of A)).presheaf.germ ⊤ ((spMap φ) (closedPoint (CommRingCat.of K))) trivial ≫
        inv (j.stalkMap ((spMap φ) (closedPoint (CommRingCat.of K))))).hom a, ?_⟩
    rw [h3]
    exact congrArg (fun m => m.hom a) h5
  have hsurj : Function.Surjective (Y.descResidueField τ).hom := by
    intro z
    obtain ⟨a, c, rfl⟩ := hφ z
    obtain ⟨s, hs⟩ := hτ a
    obtain ⟨t, ht⟩ := hτ c
    refine ⟨Y.residue _ s / Y.residue _ t, ?_⟩
    rw [map_div₀, ← hs, ← ht]
    rfl
  rw [h2]
  exact (RingHom.Finite.of_surjective _ hsurj).comp ((GlobalTheory.residueFieldMap_finite_of_locallyQuasiFinite q _).comp
    (RingHom.Finite.of_surjective _ (Scheme.residue_surjective X _)))

theorem exists_chart : ∀ (n N : ℕ) (X Y : Scheme.{0}) (sX : X ⟶ Sp (cycAway n)) (sY : Y ⟶ Sp (cycAway N)) (q : Y ⟶ X), 0 < n → 0 < N → Smooth sX → Smooth sY → IsFinite q → Etale q → Surjective q → ∀ η ∈ genericPoints X, ∃ (Ω : Type) (_ : Field Ω) (_ : Algebra (cycAway N) Ω) (_ : ArithBase (cycAway N) Ω) (R : Subalgebra (cycAway N) Ω) (y : Sp R ⟶ Y), R.FG ∧ (∀ z : Ω, ∃ a ∈ R, ∃ c ∈ R, z = a / c) ∧ y ≫ sY = spMap (algebraMap (cycAway N) R) ∧ (∀ w, (spMap R.val.toRingHom ≫ y ≫ q) w = η) ∧ ((spMap R.val.toRingHom ≫ y ≫ q).stalkMap (genericPoint (Sp Ω))).hom.Finite := by
  intro n N X Y sX sY q hn hN hsX hsY hq he hs η hη
  obtain ⟨η', hη', rfl⟩ := GlobalTheory.QuotTriple.genericPoints_subset_image (π := q) hη
  have hgen : (sY η').asIdeal = ⊥ := by
    let b : Sp (cycAway N) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (cycAway N))
    have hb : b ⤳ sY η' := (PrimeSpectrum.le_iff_specializes _ _).1 (show (⊥ : Ideal _) ≤ _ from bot_le)
    obtain ⟨z', hz', e⟩ := Flat.generalizingMap sY hb
    have h1 : closure {η'} ⊆ closure ({z'} : Set Y) := hz'.closure_subset
    have h2 : closure ({z'} : Set Y) ⊆ closure {η'} := hη'.2 isIrreducible_singleton.closure h1
    have h3 : η' ⤳ z' := specializes_iff_closure_subset.2 h2
    have : z' = η' := (hz'.antisymm h3).eq
    rw [← this, e]
  obtain ⟨_, ⟨U, hU, rfl⟩, hηU, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ η') isOpen_univ
  replace hU : IsAffineOpen U := hU
  haveI : LocallyOfFiniteType sY := inferInstance
  let P : PrimeSpectrum Γ(Y, U) := hU.primeIdealOf ⟨η', hηU⟩
  have hP : hU.fromSpec P = η' := hU.fromSpec_primeIdealOf _
  let ψ : cycAway N →+* Γ(Y, U) := (Spec.preimage (hU.fromSpec ≫ sY)).hom
  have hψ : spMap ψ = hU.fromSpec ≫ sY := Spec.map_preimage _
  have hft : ψ.FiniteType := by
    have : LocallyOfFiniteType (spMap ψ) := by rw [hψ]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 this
  have hker : Ideal.comap ψ P.asIdeal = ⊥ := by
    have h1 : spMap ψ P = sY (hU.fromSpec P) := by rw [hψ]; rfl
    change (spMap ψ P).asIdeal = ⊥
    rw [h1, hP]; exact hgen
  letI : Algebra (cycAway N) Γ(Y, U) := ψ.toAlgebra
  let Ω := FractionRing (Γ(Y, U) ⧸ P.asIdeal)
  let φ : Γ(Y, U) →+* Ω := (algebraMap (Γ(Y, U) ⧸ P.asIdeal) Ω).comp (Ideal.Quotient.mk P.asIdeal)
  have hφker : ∀ a, φ a = 0 ↔ a ∈ P.asIdeal := fun a => by
    simp only [φ, RingHom.comp_apply]
    rw [(IsFractionRing.injective (Γ(Y, U) ⧸ P.asIdeal) Ω).eq_iff' (map_zero _), Ideal.Quotient.eq_zero_iff_mem]
  letI : Algebra (cycAway N) Ω := (φ.comp ψ).toAlgebra
  let f : Γ(Y, U) →ₐ[cycAway N] Ω := { φ with commutes' := fun _ => rfl }
  have hinj : Function.Injective (algebraMap (cycAway N) Ω) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have : x ∈ Ideal.comap ψ P.asIdeal := (hφker (ψ x)).1 hx
    rwa [hker, Ideal.mem_bot] at this
  haveI : CharZero Ω := charZero_of_injective_algebraMap hinj
  haveI : ArithBase (cycAway N) Ω := ⟨GlobalTheory.CycAwayReg.isDedekindDomain_cycAway N, finiteType_cycAway N, inferInstance, hinj⟩
  refine ⟨Ω, inferInstance, inferInstance, inferInstance, f.range, spMap f.rangeRestrict.toRingHom ≫ hU.fromSpec,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Algebra.map_top]
    haveI : Algebra.FiniteType (cycAway N) Γ(Y, U) := hft
    exact Algebra.FiniteType.out.map f
  · intro z
    obtain ⟨x, s, -, rfl⟩ := IsFractionRing.div_surjective (A := Γ(Y, U) ⧸ P.asIdeal) z
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective s
    exact ⟨f a, ⟨a, rfl⟩, f c, ⟨c, rfl⟩, rfl⟩
  · rw [Category.assoc, ← hψ, ← Spec.map_comp]
    rfl
  · intro w
    have hw : spMap f.rangeRestrict.toRingHom (spMap f.range.val.toRingHom w) = P := by
      refine PrimeSpectrum.ext ?_
      change Ideal.comap (f.rangeRestrict.toRingHom) (Ideal.comap f.range.val.toRingHom w.asIdeal) = P.asIdeal
      rw [@Ideal.eq_bot_of_prime _ _ w.asIdeal (PrimeSpectrum.isPrime (show PrimeSpectrum Ω from w))]
      ext a
      simp only [Ideal.mem_comap, Ideal.mem_bot]
      exact hφker a
    show q (hU.fromSpec (spMap f.rangeRestrict.toRingHom (spMap f.range.val.toRingHom w))) = q η'
    rw [hw, hP]
  · have e : spMap f.range.val.toRingHom ≫ spMap f.rangeRestrict.toRingHom =
        spMap (f.range.val.toRingHom.comp f.rangeRestrict.toRingHom) := (Spec.map_comp _ _).symm
    refine stalkMap_finite_of_chart Ω Γ(Y, U) q hU.fromSpec (f.range.val.toRingHom.comp f.rangeRestrict.toRingHom)
      (fun z => ?_) _ (by rw [← e]; simp only [Category.assoc])
    obtain ⟨x, s, -, rfl⟩ := IsFractionRing.div_surjective (A := Γ(Y, U) ⧸ P.asIdeal) z
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective s
    exact ⟨a, c, rfl⟩

end GlobalTheory.Poinc.Chart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClassicalAbelianPartValuesOfNormalForm
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix
noncomputable section

namespace GlobalTheory.MBLow.Cl.GeoOne

open GlobalTheory.CubeValues GlobalTheory.SymmetricSemicharacter GlobalTheory.EigenNorm GlobalTheory.FrameValue

def frW {x : KeyIn ℂ} {Y : Scheme.{0}} {M : LB Y} {φ : x.P.A.left ⟶ Y} (w : LB.Iso x.P.L (M.pull φ)) {g : ℕ}
    (u : HolUnif x.P.A x.P.L g) (j : M.ι) (z : Fin g → ℂ) : ℂ :=
  valAt' (u.ex z).left _ (w.s (fun _ => j, FrameValue.chartAt x.P.isLB (u.ex z).left)).val *
    u.fr (FrameValue.chartAt x.P.isLB (u.ex z).left) z

variable {x : KeyIn ℂ} {Y : Scheme.{0}} {M : LB Y} {φ : x.P.A.left ⟶ Y} {w : LB.Iso x.P.L (M.pull φ)} {g : ℕ}

theorem frW_eq (hM : M.IsLB) (hw : w.IsGen) (u : HolUnif x.P.A x.P.L g) (j : M.ι) (z : Fin g → ℂ) (k : x.P.L.ι)
    (hj : ⊤ ≤ ((u.ex z).left ≫ φ) ⁻¹ᵁ M.U j) (hk : ⊤ ≤ (u.ex z).left ⁻¹ᵁ x.P.L.U k) :
    frW w u j z = valAt' (u.ex z).left _ (w.s (fun _ => j, k)).val * u.fr k z := by
  unfold frW
  have hi := le_chartAt x.P.isLB (u.ex z).left
  rw [u.fr_compat _ k z ((le_preimage_inf _ _ _).2 ⟨hi, hk⟩), ← _root_.mul_assoc]
  exact congrArg (· * u.fr k z) (GlobalTheory.Ex.Arch.FibEx.val_iso _ (pull_isLB hM φ) hw _ _ _
    ((le_preimage_wchart _ _ _ _).2 fun _ => hj) hi hk)

theorem frW_ne (u : HolUnif x.P.A x.P.L g) (j : M.ι) (z : Fin g → ℂ) (hj : ⊤ ≤ ((u.ex z).left ≫ φ) ⁻¹ᵁ M.U j) :
    frW w u j z ≠ 0 := by
  have hi := le_chartAt x.P.isLB (u.ex z).left
  exact mul_ne_zero (val_unit_ne_zero _ valueRules
    ((le_preimage_inf _ _ _).2 ⟨(le_preimage_wchart _ _ _ _).2 fun _ => hj, hi⟩) _) (u.fr_ne _ _ hi)

theorem frW_compat (hw : w.IsGen) (u : HolUnif x.P.A x.P.L g) (i j : M.ι) (z : Fin g → ℂ)
    (hi : ⊤ ≤ ((u.ex z).left ≫ φ) ⁻¹ᵁ M.U i) (hj : ⊤ ≤ ((u.ex z).left ≫ φ) ⁻¹ᵁ M.U j) :
    frW w u i z = valAt' ((u.ex z).left ≫ φ) (M.U i ⊓ M.U j) (M.g i j).val * frW w u j z := by
  unfold frW
  rw [← _root_.mul_assoc]
  exact congrArg (· * _) (GlobalTheory.Ex.Arch.val_iso_chart x.P.isLB hw _ i j _ hi hj (le_chartAt x.P.isLB (u.ex z).left))

theorem frW_hol (hM : M.IsLB) (hw : w.IsGen) (u : HolUnif x.P.A x.P.L g) (j : M.ι) :
    DifferentiableOn ℂ (frW w u j) {z | ⊤ ≤ ((u.ex z).left ≫ φ) ⁻¹ᵁ M.U j} := by
  intro z₀ hz₀
  have hk := le_chartAt x.P.isLB (u.ex z₀).left
  have a : ⊤ ≤ (u.ex z₀).left ⁻¹ᵁ (((M.pull φ).div x.P.L).U (fun _ => j, FrameValue.chartAt x.P.isLB (u.ex z₀).left)) :=
    (le_preimage_inf _ _ _).2 ⟨(le_preimage_wchart _ _ _ _).2 fun _ => hz₀, hk⟩
  obtain ⟨o₂, d₂⟩ := u.hol _ (w.s (fun _ => j, FrameValue.chartAt x.P.isLB (u.ex z₀).left)).val
  have n₂ := o₂.mem_nhds a
  have d := (d₂.differentiableAt n₂).fun_mul ((u.fr_hol _).differentiableAt ((u.hol _ 0).1.mem_nhds hk))
  refine (d.congr_of_eventuallyEq ?_).differentiableWithinAt
  filter_upwards [n₂] with z hz
  obtain ⟨h₁, h₂⟩ := (le_preimage_inf _ _ _).1 hz
  exact frW_eq hM hw u j z _ ((le_preimage_wchart _ _ _ _).1 h₁ PUnit.unit) h₂

theorem valAt'_appLE_comp {X X' : Scheme.{0}} (p : Sp ℂ ⟶ X) (f : X ⟶ X') (U : X'.Opens) (V : X.Opens) (h : V ≤ f ⁻¹ᵁ U)
    (hV : ⊤ ≤ p ⁻¹ᵁ V) (s : Γ(X', U)) : valAt' p V ((f.appLE U V h).hom s) = valAt' (p ≫ f) U s := by
  show valAt' p V (resG X h ((f.app U).hom s)) = _
  rw [valAt'_res _ h _ hV, valAt'_comp]

end GlobalTheory.MBLow.Cl.GeoOne

namespace GlobalTheory.MBLow.Cl.GeoOne

open GlobalTheory.CubeValues GlobalTheory.SymmetricSemicharacter GlobalTheory.EigenNorm GlobalTheory.FrameValue

theorem tf_hom (R : Type) [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ] :
    (TF (R := R) ℂ).hom = spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R))) := by
  simp only [TF, jFK, jK, spMap, Over.mk_hom]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem eq_dualMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (F : DualNumber A →+* DualNumber B)
    (h1 : ∀ a, F (algebraMap A _ a) = algebraMap B _ (f a)) (h2 : F DualNumber.eps = DualNumber.eps) : F = dualMap f := by
  refine RingHom.ext fun z => ?_
  have hz : z = algebraMap A _ z.fst + algebraMap A _ z.snd * DualNumber.eps := by
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  rw [hz, map_add, map_mul, h1, h1, h2]
  ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl, dualMap]

theorem eu_gen (x : KeyIn ℂ) (g : ℕ) (hg : x.P.g = g) (u : HolUnif x.P.A x.P.L g) :
    ∀ w, IsTangent w → ∃! W, u.IsDiff W w := by
  subst hg
  exact (GlobalTheory.LamT.existsUnique_isDiff_and_linear x u).1

theorem one_left {S : Scheme.{0}} (X : Over S) [GrpObj X] : (1 : 𝟙_ (Over S) ⟶ X).left = eSec X := by
  have : (1 : 𝟙_ (Over S) ⟶ X) = η[X] := by
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  rw [this]; rfl

end GlobalTheory.MBLow.Cl.GeoOne

namespace GlobalTheory.MBLow.Cl

open GlobalTheory.CubeValues GlobalTheory.SymmetricSemicharacter GlobalTheory.EigenNorm GlobalTheory.FrameValue GlobalTheory.MBLow.Cl.GeoOne

theorem exists_ab_geo_of_nf : AllC fun {R} _ _ {D} _ {N} ν => ∀ (y : KeyIn R) (_ : y.P = D.P), HEq y.rig D.rig → (∃ th : D.P.L.Sec, HEq y.th th ∧ ∀ i : D.P.L.ι, ∀ h : LB.wchart D.P.L (fun _ : Fin 1 => 𝟙 D.P.A.left) (fun _ => i) ≤ D.P.L.U i, ν.th.f (fun _ => i) = resG _ h (th.f i)) → ∀ (x : KeyIn ℂ) (hg : x.P.g = D.P.g) (hy : y.P.g = D.P.g) (u : HolUnif x.P.A x.P.L D.P.g) (τ : Matrix (Fin D.P.g) (Fin D.P.g) ℂ) (a b : Fin D.P.g → ℂ) (c : ℂ) (W : Fin D.P.g → Fin D.P.g → ℂ), KeyPB x y ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R))) → NF x hg u τ a b c W → ∃ (d : AB N.toNumB D.P.g) (_ : Geo ν d), d.c = c ∧ ∀ (vB : Fin D.P.g → (epsR R ⟶ D.P.A)), (∀ i, HEq (y.v (i.cast hy.symm)) (vB i)) → ∀ i (bb : TE R ℂ ⟶ D.P.A), bb.left = spMap (dualMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R)))) ≫ (vB i).left → ∀ W', IsD ν d W' bb ↔ W' = W i := by
  intro R _ _ _ _ D hψ hτ _ N ν y hyP hrig hth x hg hy u τ a b c W hpb hnf
  obtain ⟨P, gpos, rig, rig_gen, th, th_ne, v, basis⟩ := y
  subst hyP
  cases hrig
  obtain ⟨th', hth', hνth⟩ := hth
  cases hth'
  obtain ⟨φ, he, w, hg', F, hφ, hw, hrigm, hthm, hF1, hF2, hv⟩ := hpb
  have hnf' := hnf
  obtain ⟨hs, hp, ha, hb, hc, hΛ, hrigu, hfn, hdiff⟩ := hnf'
  obtain ⟨e, he'⟩ := LiePull.exists_pushEquiv hφ (𝟙_ (Over (Sp ℂ))) (TF (R := R) ℂ).hom
    (by rw [tf_hom]; exact (Category.id_comp _).symm)
  have hJ := ν.good
  have hex0 : u.ex 0 = 1 := by
    have := u.ex_add 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have h0 : (u.ex 0).left ≫ φ = spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R))) ≫ eSec D.P.A := by rw [hex0, one_left]; exact he
  have hrg0 : frW w u (ν.J (spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R))) ≫ eSec D.P.A)) 0 = ν.rg := by
    unfold NumOf.rg vF
    rw [tf_hom]
    exact GlobalTheory.T.uniformisedFibre_frame_at_origin_eq_rigidification R D x φ he w hw hrigm _ u hrigu _ _ (le_chartAt _ _) (hJ _)
  have hrgne : ν.rg ≠ 0 := by
    rw [← hrg0]
    refine frW_ne u _ 0 ?_
    rw [h0]; exact hJ _
  have hthz : ∀ z, sF ν.th ((u.ex z).left ≫ φ) ν.J =
      c * thetaChar τ a b z * frW w u (ν.J ((u.ex z).left ≫ φ)) z := by
    intro z
    have hj : ⊤ ≤ ((u.ex z).left ≫ φ) ⁻¹ᵁ D.P.L.U (ν.J ((u.ex z).left ≫ φ)) := hJ _
    have hle : (D.P.L.wchart (fun _ : Fin 1 => 𝟙 D.P.A.left) fun _ => ν.J ((u.ex z).left ≫ φ)) ≤
        D.P.L.U (ν.J ((u.ex z).left ≫ φ)) := fun q hq => Set.mem_iInter.1 hq 0
    have e0 : sF ν.th ((u.ex z).left ≫ φ) ν.J = valAt' ((u.ex z).left ≫ φ) _ (resG _ hle (th.f (ν.J ((u.ex z).left ≫ φ)))) := by
      rw [← hνth _ hle]; rfl
    rw [e0, valAt'_res _ hle _ ((le_preimage_wchart _ _ _ _).2 fun _ => by rw [Category.comp_id]; exact hj)]
    have hk := le_chartAt x.P.isLB (u.ex z).left
    have hV : ((D.P.L.pull φ).U (fun _ => ν.J ((u.ex z).left ≫ φ))) ⊓ x.P.L.U (FrameValue.chartAt x.P.isLB (u.ex z).left) ≤
        φ ⁻¹ᵁ D.P.L.U (ν.J ((u.ex z).left ≫ φ)) := inf_le_left.trans (LB.wchart_le _ _ _ PUnit.unit)
    have hpV : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (((D.P.L.pull φ).U (fun _ => ν.J ((u.ex z).left ≫ φ))) ⊓
        x.P.L.U (FrameValue.chartAt x.P.isLB (u.ex z).left)) :=
      (le_preimage_inf _ _ _).2 ⟨(le_preimage_wchart _ _ _ _).2 fun _ => hj, hk⟩
    have hm := congrArg (valAt' (u.ex z).left _) (hthm (fun _ => ν.J ((u.ex z).left ≫ φ)) _ hV)
    rw [valAt'_appLE_comp _ _ _ _ hV hpV, valAt'_mul, valAt'_res _ _ _ hpV, hfn _ z hk] at hm
    dsimp only at hm
    rw [hm]
    unfold frW
    have key : ∀ A B C E : ℂ, A = B → A * (C * E) = C * (B * E) := by intros; subst_vars; ring
    exact key _ _ _ _ rfl
  let d : AB N.toNumB D.P.g :=
    { τ := τ, a := a, b := b, c := c, symm := hs, pos := hp, ha := ha, hb := hb, hc := hc
      ex := fun z => ν.eA.symm (e (u.ex z))
      ex_add := fun z w => by simp only [u.ex_add, map_mul]
      onto := fun q => by
        obtain ⟨p, hp⟩ := e.surjective (ν.eA q)
        obtain ⟨z, rfl⟩ := u.ex_onto p
        exact ⟨z, show ν.eA.symm (e (u.ex z)) = q by rw [hp, MulEquiv.symm_apply_apply]⟩
      ker := fun z => by
        rw [MulEquiv.map_eq_one_iff, MulEquiv.map_eq_one_iff, u.ker, hΛ]
      fr := fun z => Units.mk0 (frW w u (ν.J ((u.ex z).left ≫ φ)) z / ν.rg) (div_ne_zero (frW_ne u _ z (hJ _)) hrgne)
      fr_zero := by
        ext
        rw [Units.val_mk0, Units.val_one, h0, hrg0, div_self hrgne]
      fr_per := fun M N z => by
        simp only [Units.val_mk0]
        have hl : u.ex (z + perV τ M N) = u.ex z := by
          rw [u.ex_add, (u.ker _).2 ((hΛ _).2 ⟨M, N, rfl⟩), _root_.mul_one]
        unfold frW
        rw [hl, frame_eq_autV_mul _ x hg u τ a b c W hnf M N _ z (le_chartAt _ _)]
        ring
      th := fun z => by
        have h1 := ν.th_eq (ν.eA.symm (e (u.ex z)))
        rw [MulEquiv.apply_symm_apply, he'] at h1
        change N.th _ * ν.rg = _ at h1
        rw [hthz z] at h1
        rw [Units.val_mk0]
        field_simp
        exact h1 }
  have hE : ∀ z, (ν.eA (d.ex z)).left = (u.ex z).left ≫ φ := fun z => by
    show (ν.eA (ν.eA.symm (e (u.ex z)))).left = _
    rw [MulEquiv.apply_symm_apply, he']
  refine ⟨d, ⟨fun i z => frW w u i z, GlobalTheory.T.holomorphic_functionValues_classicalUniformisation R D N ν _ d x u φ hφ hE, fun i => ?_, fun i j z h => ?_, fun z => ?_,
    fun bb hbb => ?_⟩, rfl, ?_⟩
  · simp only [hE]
    exact frW_hol D.P.isLB hw u i
  · rw [hE] at h ⊢
    exact frW_compat hw u i j z ((le_preimage_inf _ _ _).1 h).1 ((le_preimage_inf _ _ _).1 h).2
  · rw [hE]
    show (frW w u (ν.J ((u.ex z).left ≫ φ)) z / ν.rg) * ν.rg = _
    exact div_mul_cancel₀ _ hrgne
  · obtain ⟨b', hb't, hb'⟩ := GlobalTheory.T.dualPointOverOrigin_lifts_tangentVector_uniformised R D x φ hφ he bb hbb
    obtain ⟨W', hW', -⟩ := eu_gen x _ hg u b' hb't
    exact ⟨W', (GlobalTheory.T.holomorphic_uniformization_complex_base_change R D N ν _ d x u φ hφ hE b' bb hb't hb' W').2 hW'⟩
  · intro vB hvB i bb hbb W'
    have hvi : v i = vB i := by
      have := eq_of_heq (hvB i)
      rwa [Fin.cast_eq_self] at this
    have hF : F = dualMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R))) := eq_dualMap _ F hF1 hF2
    have hb' : (x.v (i.cast hg.symm)).left ≫ φ = bb.left := by
      rw [hv, hbb, hF, ← hvi]
      rfl
    rw [GlobalTheory.T.holomorphic_uniformization_complex_base_change R D N ν _ d x u φ hφ hE _ bb (x.basis.1 _) hb' W']
    obtain ⟨W0, -, huniq⟩ := eu_gen x _ hg u _ (x.basis.1 (i.cast hg.symm))
    constructor
    · intro h
      exact (huniq _ h).trans (huniq _ (hdiff i)).symm
    · rintro rfl
      exact hdiff i

end GlobalTheory.MBLow.Cl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedSubschemeAdditiveFamiliesAgreeStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_closedSubscheme_additiveFamilies_agree : ∀ (S : Scheme.{0}) (A T : Over S) [GrpObj A] [IsLocallyNoetherian T.left], IsAbelianScheme A → ∀ (N N' : LB (A ⊗ T).left), Fam A N → Fam A N' → ∃ (G : Over S) (i : G ⟶ T), IsClosedImmersion i.left ∧ ∀ (Y : Over S) (y : Y ⟶ T), Same A N N' y y ↔ ∃ z : Y ⟶ G, z ≫ i = y := by
  first | exact @GlobalTheory.DualLocus.exists_closed_same | exact GlobalTheory.DualLocus.exists_closed_same | (intros; apply GlobalTheory.DualLocus.exists_closed_same <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstantComponentFunctionComplexValuesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_constant_component_function_complexValues : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : (Xo.XF c).Opens) (e : c.F →+* ℂ) (f : Γ(Xo.XF c, U)), GeometricallyConnected (U.ι ≫ toF Xo c) → (∀ y y' : Sp ℂ ⟶ Xo.XF c, y ≫ toF Xo c = spMap e → y' ≫ toF Xo c = spMap e → Set.range y ⊆ U → Set.range y' ⊆ U → valR y U f = valR y' U f) → ∃ a : c.F, f = ReciprocityTheory.ChartRestriction.G.Geo.Tor.constFn (toF Xo c) U a := by
  first | exact @GlobalTheory.OneValue.exists_eq_constFn_of_one_value | exact GlobalTheory.OneValue.exists_eq_constFn_of_one_value | (intros; apply GlobalTheory.OneValue.exists_eq_constFn_of_one_value <;> assumption)
end

