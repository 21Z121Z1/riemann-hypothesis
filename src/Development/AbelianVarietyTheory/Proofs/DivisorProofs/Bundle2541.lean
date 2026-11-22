import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2259
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2289
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0201
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2405
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2373
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2411
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0119
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0197
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0028
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0071
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0406
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0169
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0505
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RingKrullDimQuotientAddOneOfMemMinimalPrimesSup
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2436
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0075
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2370
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTauLattice
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0208
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGen
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGeneratorOfBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2437
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2318

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictionStatementHolds
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FlatModel

theorem geomIrr_restrict : ∀ (V : Type) [CommRing V] (X : Scheme.{0}) (s : X ⟶ Sp V) (U Xw : X.Opens), Xw ≤ U →
    GeomIrr s Xw → GeomIrr (U.ι ≫ s) (U.ι ⁻¹ᵁ Xw) := by
  intro V _ X s U Xw hle h k _ f hf
  have hr : Set.range ((U.ι ⁻¹ᵁ Xw).ι ≫ U.ι) = Set.range Xw.ι := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι, Scheme.Opens.range_ι]
    have : ((U.ι ⁻¹ᵁ Xw : U.toScheme.Opens) : Set U.toScheme) = U.ι ⁻¹' (Xw : Set X) := rfl
    rw [this, Set.image_preimage_eq_inter_range, Scheme.Opens.range_ι]
    exact Set.inter_eq_left.2 hle
  let e := IsOpenImmersion.isoOfRangeEq ((U.ι ⁻¹ᵁ Xw).ι ≫ U.ι) Xw.ι hr
  have he : e.hom ≫ Xw.ι = (U.ι ⁻¹ᵁ Xw).ι ≫ U.ι := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have h0 := h k f hf
  let m := pullback.map (Xw.ι ≫ s) (spMap f) ((U.ι ⁻¹ᵁ Xw).ι ≫ U.ι ≫ s) (spMap f) e.inv (𝟙 _) (𝟙 _)
    (by rw [Category.comp_id, ← Category.assoc _ U.ι s, ← he]; simp) (by simp)
  haveI : IsIso m := by unfold m; infer_instance
  exact Function.Surjective.irreducibleSpace m.homeomorph.continuous m.homeomorph.surjective

theorem range_subset_of_bot_mem {R : Type} [CommRing R] [IsDomain R] {X : Scheme.{0}} (g : Sp R ⟶ X) {C : Set X}
    (hC : IsClosed C) (h : g (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) ∈ C) : Set.range g ⊆ C := by
  rintro _ ⟨z, rfl⟩
  have h1 : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) ⤳ z := (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
  exact (h1.map g.continuous).mem_closed hC h

theorem isTest_comp {p : ℕ} [Fact p.Prime] {X : Scheme.{0}} (U Xw : X.Opens) {yb : Sp 𝓞_ℂ_[p] ⟶ U.toScheme}
    (h : IsTest p (U.ι ⁻¹ᵁ Xw) yb) : IsTest p Xw (yb ≫ U.ι) := by
  obtain ⟨⟨T, kO, yT, hT, hk, e⟩, hr⟩ := h
  refine ⟨⟨T, kO, yT ≫ U.ι, hT, hk, by rw [← Category.assoc, e]⟩, ?_⟩
  rintro _ ⟨z, rfl⟩
  have := hr ⟨z, rfl⟩
  rw [← Category.assoc]
  exact this

theorem restrictSt : RestrictSt := by
  intro F _ _ V p _ hpV X s Xw hnorm hproj hflat hXw hirr n K hK hchart
  haveI : IsNoetherianRing V := GlobalTheory.ModelNoeth.isNoetherianRing_valuationSubring V
  haveI : IsLocallyNoetherian X := GlobalTheory.ZM.isLocallyNoetherian_of_isQProjOver (by
    obtain ⟨N, i, hi, e⟩ := hproj
    exact ⟨N, i, inferInstance, inferInstance, e⟩)
  haveI : GlobalTheory.IsNormalScheme X := GlobalTheory.IsNormalScheme.of_pred hnorm
  haveI : Flat s := hflat
  have hXi : IsIrreducible (Xw : Set X) := GlobalTheory.T.geometrically_irreducible_open_irreducible F V p hpV X s Xw hXw hirr
  obtain ⟨W, hW, hXwW⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _ hXi
  have hWcl : W ⊆ closure (Xw : Set X) := by
    have h1 := subset_closure_inter_of_isPreirreducible_of_isOpen hW.1.2 Xw.isOpen
      (by rw [Set.inter_eq_right.2 hXwW]; exact hXi.nonempty)
    rwa [Set.inter_eq_right.2 hXwW] at h1
  let Z : irreducibleComponents X := ⟨W, hW⟩
  let U : X.Opens := GlobalTheory.IsNormalScheme.component Z
  have hU : (U : Set X) = W := rfl
  have hWc : IsClosed W := isClosed_of_mem_irreducibleComponents W hW
  refine ⟨U.toScheme, U.ι ≫ s, U.ι ⁻¹ᵁ Xw, fun yb => K (yb ≫ U.ι), inferInstance,
    GlobalTheory.IsNormalScheme.pred U.toScheme, ?_, inferInstance, ?_, geomIrr_restrict V X s U Xw hXwW hirr,
    fun yb hyb => hK _ (isTest_comp U Xw hyb), fun x => GlobalTheory.T.chart_restrict_open p n X U Xw K x (hchart _ (hWcl x.2)), ?_⟩
  · obtain ⟨N, i, hi, e⟩ := hproj
    exact ⟨N, U.ι ≫ i, inferInstance, by rw [Category.assoc, e]⟩
  · intro x hx
    have h := hXw hx
    have e := Scheme.preimage_basicOpen_top U.ι (p : Γ(X, ⊤))
    rw [map_natCast] at e
    rw [← e]
    exact h
  · intro yb ⟨⟨T, kO, yT, hT, hk, e⟩, hr⟩
    have hb : yb (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum 𝓞_ℂ_[p]) ∈ (Xw : Set X) := by
      rw [← bot_map (φ := algebraMap 𝓞_ℂ_[p] ℂ_[p]) (fun a b h => Subtype.ext h) yb]
      exact hr ⟨_, rfl⟩
    have hbT : yT (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum T.V) ∈ W := by
      rw [← bot_map hk yT, e]; exact hXwW hb
    have r1 : Set.range yb ⊆ Set.range U.ι := by
      rw [Scheme.Opens.range_ι]; exact range_subset_of_bot_mem yb hWc (hXwW hb)
    have r2 : Set.range yT ⊆ Set.range U.ι := by
      rw [Scheme.Opens.range_ι]; exact range_subset_of_bot_mem yT hWc hbT
    have f1 := IsOpenImmersion.lift_fac U.ι yb r1
    have f2 := IsOpenImmersion.lift_fac U.ι yT r2
    refine ⟨IsOpenImmersion.lift U.ι yb r1, ⟨⟨T, kO, IsOpenImmersion.lift U.ι yT r2, hT, hk, ?_⟩, ?_⟩, ?_⟩
    · rw [← cancel_mono U.ι, Category.assoc, f2, f1, e]
    · rintro _ ⟨z, rfl⟩
      show _ ∈ Xw
      rw [← Scheme.Hom.comp_apply, Category.assoc, f1]
      exact hr ⟨z, rfl⟩
    · simp only [f1]; exact le_rfl

end GlobalTheory.FlatModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannTheoremNonprincipalPolarisedTorus
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.riemann_polarised_torus : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ),
    DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → Hm.IsHermitian →
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) →
    (∀ l ∈ Λ, ∀ l' ∈ Λ, ∃ n : ℤ, (l ⬝ᵥ Hm.mulVec (star l')).im = n) →
    ∃ (A : Over (Sp ℂ)) (_ : GrpObj A), IsAbelianScheme A ∧ SmoothOfRelativeDimension g A.hom ∧
      ∃ (L : LB A.left) (u : HolUnif A L g) (χ : u.Λ → ℂ), L.IsLB ∧ (∀ w, w ∈ u.Λ ↔ w ∈ Λ) ∧ u.IsAH Hm χ := by
  intro g Λ Hm hd hf hH hpos hint
  obtain ⟨Λ₁, N, Ef, hle, hN, hNΛ, hd₁, hf₁, hE, hbij⟩ := GlobalTheory.T.exists_polarized_superlattice_of_riemann_form g Λ Hm hd hf hH hpos hint
  obtain ⟨P, u, χ, hPg, hu, hAH, -, -⟩ := GlobalTheory.principalTorus_algebraic g Λ₁ Hm Ef hd₁ hf₁ hH hpos hE hbij
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  set e : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ P.A) := fun z => u.ex ((N : ℂ)⁻¹ • z) with he
  have e_add : ∀ z w, e (z + w) = e z * e w := fun z w => by simp only [he, smul_add, u.ex_add]
  have e_zero : e 0 = 1 := by
    have h := e_add 0 0
    rw [add_zero] at h
    exact (mul_eq_left.1 h.symm)
  have e_nsmul : ∀ (n : ℕ) z, e ((n : ℂ) • z) = e z ^ n := by
    intro n z
    induction n with
    | zero => simp [e_zero]
    | succ n ih => rw [Nat.cast_succ, add_smul, one_smul, e_add, ih, pow_succ]
  have e_N : ∀ z, e ((N : ℂ) • z) = u.ex z := fun z => by
    simp only [he, smul_smul, inv_mul_cancel₀ hNc, one_smul]
  have e_sub : ∀ z w, e (z - w) * e w = e z := fun z w => by rw [← e_add, sub_add_cancel]
  let C : Subgroup (𝟙_ (Over (Sp ℂ)) ⟶ P.A) :=
    { carrier := e '' (Λ : Set (Fin g → ℂ))
      mul_mem' := by
        rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        exact ⟨a + b, Λ.add_mem ha hb, e_add a b⟩
      one_mem' := ⟨0, Λ.zero_mem, e_zero⟩
      inv_mem' := by
        rintro _ ⟨a, ha, rfl⟩
        refine ⟨-a, Λ.neg_mem ha, ?_⟩
        refine eq_inv_of_mul_eq_one_left ?_
        rw [← e_add, neg_add_cancel, e_zero] }
  have hCfin : Finite C := by
    have := (GlobalTheory.T.finite_image_lattice_of_hom_trivial_on_multiples g Λ _ e N hd hf e_add hN fun l hl => by
      rw [e_N, u.ker, hu]; exact hle hl).to_subtype
    exact this
  have hA := P.isAb
  have := hA.proper
  have := hA.comm
  obtain ⟨A, _, ψ, hA', hψ, hψf, hψe, hψs, hker⟩ := GlobalTheory.exists_quotient_abelian_by_finite_points ℂ P.A hA C hCfin
  have := hA'.smooth
  have hmon : IsMonHom (𝟙 P.A ^ N) := GlobalTheory.GrpTangent.mulN_eq_pow P.A _ ▸ GlobalTheory.GrpTangent.isMonHom_mulN P.A _
  obtain ⟨⟨φ, hφ, hc⟩, -⟩ := GlobalTheory.exists_monHom_factor_of_flat_surjective _ P.A A P.A ψ (𝟙 P.A ^ N) hψ hmon
    inferInstance hψs inferInstance fun T z hz => by
      rw [MonObj.comp_pow, Category.comp_id]
      refine GlobalTheory.SS.PrincIsog.pow_eq_one_of_etale ψ N (fun y hy => ?_) T z hz
      obtain ⟨c, ⟨l, hl, rfl⟩, rfl⟩ := (hker ℂ (𝟙 _) y).1 hy
      rw [← MonObj.comp_pow, ← e_nsmul, e_N, (u.ker l).2 (hu ▸ hle hl), MonObj.comp_one]
  have htu : toUnit (Over.mk (𝟙 (Sp ℂ))) = 𝟙 (𝟙_ (Over (Sp ℂ))) := toUnit_unique _ _
  let exA : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ A) := fun z => e z ≫ ψ
  have exA_add : ∀ z w, exA (z + w) = exA z * exA w := fun z w => by
    simp only [exA, e_add, MonObj.mul_comp]
  have exA_onto : Function.Surjective exA := by
    intro x
    obtain ⟨b, hb⟩ := GlobalTheory.SS.PrincIsog.exists_lift_point (F := ℂ) ψ.left x.left
    let b' : 𝟙_ (Over (Sp ℂ)) ⟶ P.A := Over.homMk b (by
      rw [← Over.w ψ, ← Category.assoc, hb]; exact Over.w _)
    have hb' : b' ≫ ψ = x := Over.OverMorphism.ext hb
    obtain ⟨w, hw⟩ := u.ex_onto b'
    exact ⟨(N : ℂ) • w, by simp only [exA, e_N, hw, hb']⟩
  have exA_ker : ∀ z, exA z = 1 ↔ z ∈ Λ := by
    intro z
    constructor
    · intro h
      obtain ⟨c, ⟨l, hl, rfl⟩, hc'⟩ := (hker ℂ (𝟙 _) (e z)).1 h
      rw [htu] at hc'
      replace hc' : e z = e l := hc'.trans (Category.id_comp _)
      have h1 : e (z - l) = 1 := by
        have := e_sub z l
        rw [hc'] at this
        exact mul_eq_right.1 this
      have h2 := (u.ker _).1 h1
      rw [hu] at h2
      have h3 := hNΛ _ h2
      rw [smul_smul, mul_inv_cancel₀ hNc, one_smul] at h3
      have := Λ.add_mem h3 hl
      rwa [sub_add_cancel] at this
    · intro hz
      exact (hker ℂ (𝟙 _) (e z)).2 ⟨e z, ⟨z, hz, rfl⟩, by rw [htu]; exact (Category.id_comp _).symm⟩
  have hcl : Continuous (fun z : Fin g → ℂ => (N : ℂ)⁻¹ • z) := continuous_const_smul _
  have exA_hol : ∀ (U : A.left.Opens) (f : Γ(A.left, U)), IsOpen {z | ⊤ ≤ (exA z).left ⁻¹ᵁ U} ∧
      DifferentiableOn ℂ (fun z => valAt' (exA z).left U f) {z | ⊤ ≤ (exA z).left ⁻¹ᵁ U} := by
    intro U f
    have hs : {z | ⊤ ≤ (exA z).left ⁻¹ᵁ U} =
        (fun z => (N : ℂ)⁻¹ • z) ⁻¹' {w | ⊤ ≤ (u.ex w).left ⁻¹ᵁ (ψ.left ⁻¹ᵁ U)} := by
      ext z
      simp only [exA, he, Over.comp_left, Scheme.Hom.comp_preimage, Set.mem_setOf_eq, Set.mem_preimage]
    have hv : (fun z => valAt' (exA z).left U f) =
        (fun w => valAt' (u.ex w).left (ψ.left ⁻¹ᵁ U) ((ψ.left.app U).hom f)) ∘ (fun z => (N : ℂ)⁻¹ • z) := by
      funext z
      simp only [Function.comp, exA, he, Over.comp_left, GlobalTheory.valAt'_comp]
    refine ⟨hs ▸ (u.hol _ ((ψ.left.app U).hom f)).1.preimage hcl, ?_⟩
    rw [hs, hv]
    exact (u.hol _ _).2.comp ((differentiable_id (𝕜 := ℂ) (E := Fin g → ℂ)).const_smul ((N : ℂ)⁻¹)).differentiableOn (fun z hz => hz)
  have hcomp : ∀ z, exA z ≫ φ = u.ex z := fun z => by
    simp only [exA, Category.assoc, hc, MonObj.comp_pow, Category.comp_id]
    rw [← e_nsmul, e_N]
  obtain ⟨uA, χA, hΛA, hAHA⟩ := GlobalTheory.T.exists_holUnif_pull_along_groupHom A P.A φ P.L g u exA Λ Hm χ exA_add exA_onto exA_ker hd hf
    exA_hol hcomp (hu ▸ hle) hAH
  have hsm : SmoothOfRelativeDimension g A.hom :=
    GlobalTheory.SmoothDescent.smoothOfRelativeDimension_of_etale_cover ℂ _ _ ψ.left A.hom g hψe hψs inferInstance
      (by rw [Over.w]; exact hPg ▸ P.smoothDim)
  exact ⟨A, inferInstance, hA', hsm, P.L.pull φ.left, uA, χA, pull_isLB P.isLB _, hΛA, hAHA⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingKrullDimAddEqOfTrBasis
section
set_option autoImplicit false

noncomputable section

open Algebra

namespace GlobalTheory.LocModelDim

theorem isAlgebraic_of_forall_mul {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    (h : ∀ s : S, ∃ a b : R, algebraMap R S b ≠ 0 ∧ s * algebraMap R S b = algebraMap R S a) :
    Algebra.IsAlgebraic R S := by
  refine ⟨fun s => ?_⟩
  obtain ⟨a, b, hb, e⟩ := h s
  refine ⟨Polynomial.C b * Polynomial.X - Polynomial.C a, fun h0 => hb ?_, ?_⟩
  · have h1 := congrArg (fun p => Polynomial.coeff p 1) h0
    simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul_X, Polynomial.coeff_C_succ,
      sub_zero, Polynomial.coeff_zero, if_true] at h1
    rw [h1, map_zero]
  · rw [map_sub, map_mul, Polynomial.aeval_X, Polynomial.aeval_C, Polynomial.aeval_C, mul_comm, e,
      sub_self]

theorem ringKrullDim_add_trdeg {k R Ω : Type} [Field k] [CommRing R] [IsDomain R]
    [IsLocalRing R] [Algebra k R] [Algebra.EssFiniteType k R] [Field Ω] [Algebra R Ω]
    [Algebra k Ω] [IsScalarTower k R Ω] (hχ : Function.Surjective (algebraMap R Ω)) {n m : ℕ}
    (hn : trdeg k Ω = n) (hm : trdeg k R = m) : ringKrullDim R + n = m := by
  set A := EssFiniteType.subalgebra k R
  set ι := algebraMap A R
  set f : A →+* Ω := (algebraMap R Ω).comp ι with hf
  set P := RingHom.ker f with hP
  haveI : P.IsPrime := RingHom.ker_isPrime f
  have hmax : RingHom.ker (algebraMap R Ω) = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ hχ)
  have hunit : ∀ r : R, IsUnit r ↔ algebraMap R Ω r ≠ 0 := by
    intro r
    have := congrArg (r ∈ ·) hmax
    simp only [RingHom.mem_ker, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at this
    rw [Ne, this, not_not]
  have hM : EssFiniteType.submonoid k R = P.primeCompl := by
    ext x
    simp only [EssFiniteType.submonoid, Submonoid.mem_comap, IsUnit.mem_submonoid_iff,
      Ideal.mem_primeCompl_iff, hP, RingHom.mem_ker, hf, RingHom.comp_apply, hunit]
    rfl
  haveI : IsLocalization.AtPrime R P := by
    unfold IsLocalization.AtPrime
    rw [← hM]
    infer_instance

  have hdimR : ringKrullDim R = P.height := IsLocalization.AtPrime.ringKrullDim_eq_height P R
  have hform := GlobalTheory.height_add_ringKrullDim_quotient_of_finiteType k P
  obtain ⟨s, hs1, hs2⟩ := ReciprocityTheory.CA.exists_dim_trdeg_field (K := k) (A := A)
  haveI : Algebra.FiniteType k (A ⧸ P) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k P) Ideal.Quotient.mk_surjective
  obtain ⟨s', hs1', hs2'⟩ := ReciprocityTheory.CA.exists_dim_trdeg_field (K := k) (A := A ⧸ P)

  haveI : FaithfulSMul A R := (faithfulSMul_iff_algebraMap_injective _ _).2 Subtype.val_injective
  haveI : Algebra.IsAlgebraic A R := IsLocalization.isAlgebraic R (EssFiniteType.submonoid k R)
  have hAR := trdeg_add_eq k A (A := R)
  rw [trdeg_eq_zero (R := A) (A := R), add_zero, hs2, hm] at hAR

  letI : Algebra (A ⧸ P) Ω := (RingHom.kerLift f).toAlgebra
  haveI : IsScalarTower k (A ⧸ P) Ω := IsScalarTower.of_algebraMap_eq fun x => by
    change algebraMap k Ω x = f (algebraMap k A x)
    rw [hf, RingHom.comp_apply, IsScalarTower.algebraMap_apply k R Ω]
    rfl
  haveI : FaithfulSMul (A ⧸ P) Ω :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.kerLift_injective f)
  haveI : Algebra.IsAlgebraic (A ⧸ P) Ω := by
    apply isAlgebraic_of_forall_mul
    intro ω
    obtain ⟨r, rfl⟩ := hχ ω
    obtain ⟨⟨a, t⟩, e⟩ := IsLocalization.surj (EssFiniteType.submonoid k R) r
    refine ⟨Ideal.Quotient.mk P a, Ideal.Quotient.mk P t, ?_, ?_⟩
    · change f t ≠ 0
      exact (hunit _).1 t.2
    · change algebraMap R Ω r * f t = f a
      rw [hf, RingHom.comp_apply, RingHom.comp_apply, ← map_mul]
      exact congrArg (algebraMap R Ω) e
  haveI hdom : IsDomain (A ⧸ P) := Ideal.Quotient.isDomain P
  haveI : Nontrivial (A ⧸ P) := hdom.toNontrivial
  haveI : FaithfulSMul k (A ⧸ P) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap k (A ⧸ P)).injective
  have hPΩ := trdeg_add_eq k (A ⧸ P) (A := Ω)
  rw [trdeg_eq_zero (R := A ⧸ P) (A := Ω), add_zero, hs2', hn] at hPΩ
  have hss : s' = n := by exact_mod_cast hPΩ
  have hsm : s = m := by exact_mod_cast hAR
  rw [hdimR, ← hss, ← hsm, ← hs1', ← hs1]
  exact hform

end GlobalTheory.LocModelDim

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingOnPreimageIntegralOfFiniteModelMap
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Points RatModel

theorem GlobalTheory.Poinc.finite_preimage_integral : ∀ (o₁ Ω₁ o₂ Ω₂ : Type) [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂] [Algebra Ω₁ Ω₂] (M₁ : RatModel o₁ Ω₁) (M₂ : RatModel o₂ Ω₂) (q : M₂.Z ⟶ M₁.Z), IsFinite q → M₂.pt ≫ q = spMap (algebraMap Ω₁ Ω₂) ≫ M₁.pt → ∀ U : M₁.Z.Opens, IsAffineOpen U → (U : Set M₁.Z).Nonempty → ∀ b ∈ M₂.ringOn ((q ⁻¹ᵁ U : M₂.Z.Opens) : Set M₂.Z), ∃ f : Polynomial Ω₁, f.Monic ∧ (∀ i, f.coeff i ∈ M₁.ringOn (U : Set M₁.Z)) ∧ Polynomial.eval₂ (algebraMap Ω₁ Ω₂) b f = 0 := by
  intro o₁ Ω₁ o₂ Ω₂ _ _ _ _ _ _ _ M₁ M₂ q hq hg U hUa hU b hb
  have hpt : ⊤ ≤ (M₂.pt ≫ q) ⁻¹ᵁ U := by
    rw [hg]
    exact fun x _ => M₁.top_le_preimage_pt hU (x := (spMap (algebraMap Ω₁ Ω₂)) x) trivial
  have hV : (((q ⁻¹ᵁ U : M₂.Z.Opens)) : Set M₂.Z).Nonempty :=
    ⟨M₂.pt (IsLocalRing.closedPoint Ω₂), hpt (x := IsLocalRing.closedPoint Ω₂) trivial⟩
  have h1 : ∀ a : Γ(M₁.Z, U), valF M₂.pt (q ⁻¹ᵁ U) ((q.app U).hom a) = algebraMap Ω₁ Ω₂ (valF M₁.pt U a) := by
    intro a
    refine (valR_comp M₂.pt q U a).symm.trans ?_
    rw [hg]
    exact valR_spMap_comp _ M₁.pt U (M₁.top_le_preimage_pt hU) a
  have hint : (q.app U).hom.IsIntegral := RingHom.IsIntegral.of_finite (hq.finite_app U hUa)
  obtain ⟨g, rfl⟩ := (RatModel.mem_ringOn_iff_exists hV).1 hb
  obtain ⟨P, hPm, hP⟩ := hint g
  refine ⟨P.map (M₁.res U hU), hPm.map _, fun i => ?_, ?_⟩
  · rw [Polynomial.coeff_map]
    exact (RatModel.mem_ringOn_iff_exists hU).2 ⟨P.coeff i, (M₁.res_apply U hU _).symm⟩
  · have hc : (algebraMap Ω₁ Ω₂).comp (M₁.res U hU) = (M₂.res (q ⁻¹ᵁ U) hV).comp (q.app U).hom := by
      ext a
      simp only [RingHom.comp_apply, RatModel.res_apply]
      exact (h1 a).symm
    rw [Polynomial.eval₂_map, hc, ← RatModel.res_apply _ _ hV, ← Polynomial.hom_eval₂, hP, map_zero]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiConditionOfGrpPullbackSquare
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

noncomputable section

namespace GlobalTheory.RosatiPull

theorem sq_left_ext {H : Scheme.{0}} {G : Over H} {Z : Scheme.{0}} {a b : Z ⟶ (G ⊗ G).left}
    (h1 : a ≫ (fst G G).left = b ≫ (fst G G).left) (h2 : a ≫ (snd G G).left = b ≫ (snd G G).left) : a = b :=
  pullback.hom_ext h1 h2

theorem rosatiFor_pull : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (S H E : Scheme.{0}) (A₀ : Over S) [GrpObj A₀] (P : LB (G2 A₀).left), P.IsLB → ∀ (AH : Over H) [GrpObj AH] (AE : Over E) [GrpObj AE] (f : E ⟶ H) (φ : AE.left ⟶ AH.left) (φ₂ : (G2 AE).left ⟶ (G2 AH).left) (φ₂H : (G2 AH).left ⟶ (G2 A₀).left) (actH : OActN D.O AH) (actE : OActN D.O AE), IsGrpPullback AE AH f φ → IsSquare φ φ₂ → (∀ a : D.O, (actE.act a).left ≫ φ = φ ≫ (actH.act a).left) → RosatiFor D actH (P.pull φ₂H) → RosatiFor D actE (P.pull (φ₂ ≫ φ₂H)) := by
  intro p _ D S H E A₀ _ P hP AH _ AE _ f φ φ₂ φ₂H actH actE _ hsq hact hR c
  have hu : (lift (fst AE AE ≫ actE.act c) (snd AE AE)).left ≫ φ₂ =
      φ₂ ≫ (lift (fst AH AH ≫ actH.act c) (snd AH AH)).left := by
    apply sq_left_ext
    · simp only [Category.assoc, ← Over.comp_left, lift_fst]
      rw [hsq.1]
      simp only [← Category.assoc, ← Over.comp_left, lift_fst]
      simp only [Over.comp_left, Category.assoc, hact]
      rw [← Category.assoc φ₂, hsq.1, Category.assoc]
    · simp only [Category.assoc, ← Over.comp_left, lift_snd]
      rw [hsq.2]
      simp only [← Category.assoc, ← Over.comp_left, lift_snd]
  have hv : (lift (fst AE AE) (snd AE AE ≫ actE.act (D.star c).unop)).left ≫ φ₂ =
      φ₂ ≫ (lift (fst AH AH) (snd AH AH ≫ actH.act (D.star c).unop)).left := by
    apply sq_left_ext
    · simp only [Category.assoc, ← Over.comp_left, lift_fst]
      rw [hsq.1]
      simp only [← Category.assoc, ← Over.comp_left, lift_fst]
    · simp only [Category.assoc, ← Over.comp_left, lift_snd]
      rw [hsq.2]
      simp only [← Category.assoc, ← Over.comp_left, lift_snd]
      simp only [Over.comp_left, Category.assoc, hact]
      rw [← Category.assoc φ₂, hsq.2, Category.assoc]
  have hQ : (P.pull φ₂H).IsLB := pull_isLB hP _
  have hR' : (P.pull (φ₂ ≫ φ₂H)).IsLB := pull_isLB hP _
  have e3 := GlobalTheory.GenSpread.lbIso_pull_comp (L := P.pull φ₂H) (M := P.pull φ₂H) φ₂ hu hv (hR c)
  have e1u := GlobalTheory.GenSpread.lbIso_pull_pull hP
    (lift (fst AE AE ≫ actE.act c) (snd AE AE)).left (a := φ₂ ≫ φ₂H) rfl
  have e2u := GlobalTheory.GenSpread.lbIso_pull_pull hP
    ((lift (fst AE AE ≫ actE.act c) (snd AE AE)).left ≫ φ₂) (a := φ₂H) (Category.assoc _ _ _).symm
  have e1v := GlobalTheory.GenSpread.lbIso_pull_pull hP
    (lift (fst AE AE) (snd AE AE ≫ actE.act (D.star c).unop)).left (a := φ₂ ≫ φ₂H) rfl
  have e2v := GlobalTheory.GenSpread.lbIso_pull_pull hP
    ((lift (fst AE AE) (snd AE AE ≫ actE.act (D.star c).unop)).left ≫ φ₂) (a := φ₂H) (Category.assoc _ _ _).symm
  exact LBIso.trans (pull_isLB hR' _) (pull_isLB hP _) (pull_isLB hR' _) e1u.symm
    (LBIso.trans (pull_isLB hP _) (pull_isLB hQ _) (pull_isLB hR' _) e2u
      (LBIso.trans (pull_isLB hQ _) (pull_isLB hQ _) (pull_isLB hR' _) e3
        (LBIso.trans (pull_isLB hQ _) (pull_isLB hP _) (pull_isLB hR' _) e2v.symm e1v)))

end GlobalTheory.RosatiPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiGeneratorValueAddEndomorphismsCubical
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.RosAddPair

open GlobalTheory.TauBalAdd

theorem ros_val_padd : ∀ {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {Lr : RigLB A} (cu : CubicalStr A Lr), GlobalFnsSt →
    IsAbelianScheme A →
    ∀ (f₁ g₁ f₂ g₂ f g : A ⟶ A) [IsMonHom f₁] [IsMonHom g₁] [IsMonHom f₂] [IsMonHom g₂], f = padd A f₁ f₂ → g = padd A g₁ g₂ →
    ∀ (u₁ : LB.Gen (LB.LinComb Lr.L (rosatiφ A f₁ g₁) rosatiε)) (u₂ : LB.Gen (LB.LinComb Lr.L (rosatiφ A f₂ g₂) rosatiε))
      (u : LB.Gen (LB.LinComb Lr.L (rosatiφ A f g) rosatiε)), u₁.IsGen → u₂.IsGen → u.IsGen →
    LB.Gen.Corr Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ u₁ (zero2 A)) (LB.oneGen Lr.L) →
    LB.Gen.Corr Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ u₂ (zero2 A)) (LB.oneGen Lr.L) →
    LB.Gen.Corr Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ u (zero2 A)) (LB.oneGen Lr.L) →
    ∀ {T : Over S} {z : T.left} {J : (T.left ⟶ A.left) → Lr.L.ι}, Good Lr.L z J → ∀ x y : T ⟶ A,
    val₂ u z J x y * cubV cu z J (y ≫ g₁) (y ≫ g₂) x =
      cubV cu z J (x ≫ f₁) (x ≫ f₂) y * (val₂ u₁ z J x y * val₂ u₂ z J x y) := by
  intro S A _ _ Lr cu hG hA f₁ g₁ f₂ g₂ f g _ _ _ _ hf hg u₁ u₂ u hu₁ hu₂ hu h₁ h₂ h₀ T z J hJ x y
  subst hf hg
  have key := ros_sum cu hG hA f₁ g₁ f₂ g₂ u₁ hu₁ h₁ u₂ hu₂ h₂ u hu h₀ hJ x y
  have C : IsCub (cubV cu z J) := isCub_cubV cu hJ
  rw [C.s01 x, C.s12 _ x] at key
  exact key

end GlobalTheory.RosAddPair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecIsMulOfBaseMultipleThetaSection
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.PsiRing

theorem secIsMul_of_mult : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (th g : GlobalTheory.UU.SecBT D (𝟙_ _) 1 0) (b : R), GlobalTheory.PsiRing.Mult D th g b → ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul (𝟙_ _ ⊗ D.P.A).hom b g th := by
  intro R _ _ D th g b h
  refine GlobalTheory.IndivisibleSection.secIsMul_of_sval D.P.isLB fun y J hJ => ?_
  have e := h _ (𝟙 _) y J hJ
  rwa [Category.id_comp] at e

end GlobalTheory.PsiRing
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianCoordinateDualBasisVectorStatement
section
open NumberField MeasureTheory Matrix GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CovTop.VolUp GlobalTheory.CovTop.VolUp.FrameBox
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.skewHermitianCoordinate_dual_basisVector : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ)) (d : Ψ → Fin r → ℝ) (z : Fin r), (∀ τ a, d τ a = 1 ∨ d τ a = -1) → ∀ j k, boxCoord z j (boxVec d z k) = if j = k then 1 else 0 := by
  first | exact @GlobalTheory.CovTop.VolUp.FrameBox.boxCoord_boxVec | exact GlobalTheory.CovTop.VolUp.FrameBox.boxCoord_boxVec | (intros; apply GlobalTheory.CovTop.VolUp.FrameBox.boxCoord_boxVec <;> assumption)
end

