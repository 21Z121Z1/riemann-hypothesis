import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0006
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0024
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0038
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0068
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0007
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0069
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0005
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0001
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle0011
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0004
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0002
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ZarhinBundleKernelFirstCoordEquations
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0067
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0057
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0050
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0018
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenericCentreSpecializes

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateDualEqOfOmegaEq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem htDual_htW_relabel : ∀ (E : Type) [Field E] [NumberField E] (s : 𝓞 E ≃+* 𝓞 E) (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (G G' : Over X) [GrpObj G] [GrpObj G'] (L : LB G.left) (L' : LB G'.left) (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel G ξ V) (M' : LieModel G' ξ V) (n n' : ℕ) (ρ : 𝓞 E →+* Module.End Ω V) (τ : 𝓞 E →+* Ω) (q : Cpt ξ), M'.htOm L' n' q = M.htOm L n q → M'.htDual L' n' (ρ.comp s.toRingHom) (τ.comp s.toRingHom) q = M.htDual L n ρ τ q ∧ M'.htW L' n' (ρ.comp s.toRingHom) (τ.comp s.toRingHom) (differentIdeal ℤ (𝓞 E)) q = M.htW L n ρ τ (differentIdeal ℤ (𝓞 E)) q := by
  intro E _ _ s X Ω _ ξ G G' _ _ L L' V _ _ M M' n n' ρ τ q h
  have hE : eigSp (ρ.comp s.toRingHom) (τ.comp s.toRingHom) = eigSp ρ τ :=
    eigSp_comp_ringEquiv Ω V (𝓞 E) ρ s τ
  have h1 : M'.htDual L' n' (ρ.comp s.toRingHom) (τ.comp s.toRingHom) q = M.htDual L n ρ τ q := by
    unfold LieModel.htDual
    rw [hE, h]
  refine ⟨h1, ?_⟩
  unfold LieModel.htW
  rw [hE, h1]
  congr 1
  ext e
  constructor
  · rintro ⟨he, H⟩
    refine ⟨he, fun d hd => ?_⟩
    have hd' : s.symm d ∈ differentIdeal ℤ (𝓞 E) :=
      (GlobalTheory.T.different_ideal_automorphism_invariant E s (s.symm d)).1 (by simpa using hd)
    simpa using H _ hd'
  · rintro ⟨he, H⟩
    exact ⟨he, fun d hd => H _ ((GlobalTheory.T.different_ideal_automorphism_invariant E s d).2 hd)⟩

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateEigenLatticeEqStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_tate_eigen_lattice_eq : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (G : Over X) [GrpObj G] (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (L : LB G.left) (n g : ℕ) (O : Type) [CommRing O] (ρ : O →+* Module.End Ω Li) (σ : O →+* Ω) (q : Cpt ξ), M.lat.IsVBOn {q} g ⊤ → M.htOm L n q = M.omLat q → M.htDual L n ρ σ q = M.eigLat ρ σ q ∧ ∀ 𝔡 : Ideal O, (∀ a, σ a ∈ regAt ξ q) → (∃ d ∈ 𝔡, unitAt ξ q (σ d)) → M.htW L n ρ σ 𝔡 q = M.eigLat ρ σ q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LieModel.htDual_htW_eq_eigLat_of_htOm_eq_omLat | exact GlobalTheory.CompanionTheory.Ar.LieModel.htDual_htW_eq_eigLat_of_htOm_eq_omLat | (intros; apply GlobalTheory.CompanionTheory.Ar.LieModel.htDual_htW_eq_eigLat_of_htOm_eq_omLat <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateWeilEndomorphismStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_tate_weil_endomorphism : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), IsCptGen ξ → Flat.NormalCpt ξ → ∀ (G : Over X) [GrpObj G], IsSemiAbelian G → ∀ (L : LB G.left) (n : ℕ), 1 ≤ n → FullTorsion G ξ n → ∀ e, GenWeil G L ξ n e → ∀ (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (a : G ⟶ G) [IsMonHom a] (A : E →ₗ[Ω] E), M.IsDiffOf a A → ∀ (y y' : Over.mk ξ ⟶ G), y ^ n = 1 → y' ^ n = 1 → (∀ g, g ^ n = 1 → e y' g = e y (g ≫ a)) → ∀ (q : Cpt ξ) (w : Module.Dual Ω E), M.IsHTAt L n y q w → M.IsHTAt L n y' q (w ∘ₗ A) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LieModel.isHTAt_end | exact GlobalTheory.CompanionTheory.Ar.LieModel.isHTAt_end | (intros; apply GlobalTheory.CompanionTheory.Ar.LieModel.isHTAt_end <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IdealSaturatedVectorBundleStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideal_saturated_vector_bundle : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (Li : Type) [AddCommGroup Li] [Module Ω Li] (O : Type) [CommRing O] [IsDedekindDomain O] (σ : O →+* Ω) (𝔡 : Ideal O) (L : Lat ξ Li) (T : Set (Cpt ξ)) (r : ℕ) (V : Submodule Ω Li), Function.Injective σ → 𝔡 ≠ ⊥ → (∀ q ∈ T, ∀ a, σ a ∈ regAt ξ q) → L.IsVBOn T r V → Lat.IsVBOn (fun q => Submodule.span (regAt ξ q) {e | e ∈ V ∧ ∀ d ∈ 𝔡, σ d • e ∈ L q} : Lat ξ Li) T r V := by
  first | exact @GlobalTheory.CompanionTheory.Relay.ideal_saturated_vector_bundle | exact GlobalTheory.CompanionTheory.Relay.ideal_saturated_vector_bundle | (intros; apply GlobalTheory.CompanionTheory.Relay.ideal_saturated_vector_bundle <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsCombFieldExtensionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.is_comb_field_extension : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (F : Type) [Field F] (x : Sp F ⟶ S) (F' : Type) [Field F'] (f : F →+* F') (x' : Sp F' ⟶ S), spMap f ≫ x = x' → ∀ (n : ℕ) (v : Fin n → (epsAt x ⟶ G)) (cf : Fin n → F) (w : epsAt x ⟶ G) (v' : Fin n → (epsAt x' ⟶ G)) (w' : epsAt x' ⟶ G), (∀ i, (v' i).left = spMap (dualMap f) ≫ (v i).left) → w'.left = spMap (dualMap f) ≫ w.left → IsComb cf v w → IsComb (fun i => f (cf i)) v' w' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.CombBase.isComb_base | exact GlobalTheory.CompanionTheory.Ar.CombBase.isComb_base | (intros; apply GlobalTheory.CompanionTheory.Ar.CombBase.isComb_base <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsCombIdentityMatrixStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.is_comb_identity_matrix : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (F : Type) [Field F] (x : Sp F ⟶ S) (n : ℕ) (v : Fin n → (epsAt x ⟶ G)), (∀ i, IsTanAt G x (v i)) → ∀ i, IsComb ((1 : Matrix (Fin n) (Fin n) F) i) v (v i) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.isComb_unit_row | exact GlobalTheory.CompanionTheory.Ar.Flat.isComb_unit_row | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.isComb_unit_row <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsCombMatrixMulStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.is_comb_matrix_mul : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (F : Type) [Field F] (x : Sp F ⟶ S) (m n k : ℕ) (v : Fin n → (epsAt x ⟶ G)) (u : Fin m → (epsAt x ⟶ G)) (w : Fin k → (epsAt x ⟶ G)) (A : Matrix (Fin k) (Fin m) F) (C : Matrix (Fin m) (Fin n) F), (∀ i, IsTanAt G x (v i)) → (∀ i, IsComb (C i) v (u i)) → (∀ i, IsComb (A i) u (w i)) → ∀ i, IsComb ((A * C) i) v (w i) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.CombMul.isComb_mul | exact GlobalTheory.CompanionTheory.Ar.CombMul.isComb_mul | (intros; apply GlobalTheory.CompanionTheory.Ar.CombMul.isComb_mul <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsPullWedge
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.CptIn

def IsPullWedge {Ω₀ Ω V₀ V : Type} [Field Ω₀] [Field Ω] [AddCommGroup V₀] [Module Ω₀ V₀] [AddCommGroup V] [Module Ω V]
    (i : Ω₀ →+* Ω) (j : V₀ →+ V) {n : ℕ} (a : ⋀[Ω₀]^n V₀) (a' : ⋀[Ω]^n V) : Prop :=
  ∀ (b : Fin n → V₀) (α : Ω₀), a = α • exteriorPower.ιMulti Ω₀ n b →
    a' = i α • exteriorPower.ιMulti Ω n fun k => j (b k)

section Comparison₂

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {U : Set (Xo.XF c)} {S : Finset ℕ} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type}
  {y : (Σ k, J k) → Ω}

def IsTie (Z : CptOver Y U) (𝔐 : HodgeCpt Y S y) (i : Z.Ω →+* Ω) (j : Z.V →+ 𝔐.Li) : Prop :=
  Dominates 𝔐.ξ (Z.ξ₀ ≫ Y.j) 𝔐.f i ∧ i.comp Z.inc = 𝔐.cst ∧ IsExtOver i j ∧
    ∀ e, (𝔐.M.pt (j e)).left ≫ 𝔐.m.φ = spMap (dualMap i) ≫ (Z.M.pt e).left

end Comparison₂

end GlobalTheory.CompanionTheory.Ar.Flat.CptIn
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsoLineOnEquivalence
section
open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)

namespace GlobalTheory.CompanionTheory.Ar.Cmp.IsoLines

theorem isoLineOn_comb_trans_symm_pull : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (Xo : Set ((Σ k, ι k) → ℂ)), IsMultiProjPrime P → Xo ⊆ mcPts P → (∀ (J : Type) [Fintype J] (ℓ ℓ' : J → HermLine ι) (n : J → ℤ), (∀ j, IsoLineOn P Xo (ℓ j) (ℓ' j)) → IsoLineOn P Xo (Top.combLine ℓ n) (Top.combLine ℓ' n)) ∧ (∀ A B C : HermLine ι, IsoLineOn P Xo A B → IsoLineOn P Xo B C → IsoLineOn P Xo A C) ∧ (∀ A B : HermLine ι, IsoLineOn P Xo A B → IsoLineOn P Xo B A) ∧ ∀ (K₁ : Type) [Fintype K₁] (ι₁ : K₁ → Type) [∀ k, Fintype (ι₁ k)] (κ : K₁ → K) (v : (Σ k, ι₁ k) → Σ k, ι k) (J : Type) [Fintype J] (ℓ : J → HermLine ι₁) (ℓ' : J → HermLine ι) (n : J → ℤ), IsBlockMap κ v → (∀ j, IsPullHerm κ v (ℓ j) (ℓ' j)) → IsPullHerm κ v (Top.combLine ℓ n) (Top.combLine ℓ' n) :=
  @PositivityTheory.UnitarySelfGeneration.i_comb

end GlobalTheory.CompanionTheory.Ar.Cmp.IsoLines
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.JoinCoordsCoordTie
section
noncomputable section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace GlobalTheory.CompanionTheory.Ar.Retie

open GlobalTheory.CompanionTheory.Ar.ProjCoord

section Transport

variable {X Y : Scheme.{0}} {Ω : Type} [Field Ω]

theorem specializes_of_iso (η : Spec (CommRingCat.of Ω) ⟶ Y) (f : Y ⟶ X) [IsIso f] {y : Y}
    (h : genPt (η ≫ f) ⤳ f y) : genPt η ⤳ y := by
  have h1 := h.map (inv f).continuous
  have e : ∀ z : Y, (inv f) (f z) = z := fun z => by
    rw [← Scheme.Hom.comp_apply, IsIso.hom_inv_id]; rfl
  have e2 : genPt (η ≫ f) = f (genPt η) := Scheme.Hom.comp_apply _ _ _
  rw [e2, e, e] at h1
  exact h1

theorem exists_push (η : Spec (CommRingCat.of Ω) ⟶ Y) (f : Y ⟶ X) [IsIso f] (q : Cpt (η ≫ f)) :
    ∃ p : Cpt η, push η f p = q := by
  obtain ⟨q, hq⟩ := q
  obtain ⟨y, rfl⟩ : ∃ y, f y = q := ⟨(inv f) q, by
    rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl⟩
  exact ⟨⟨y, specializes_of_iso η f hq⟩, rfl⟩

theorem inChart_push (η : Spec (CommRingCat.of Ω) ⟶ Y) (f : Y ⟶ X) [IsIso f] {κ : Type} (x : κ → Ω) (c : κ)
    (p : Cpt η) : InChart (η ≫ f) x c (push η f p) ↔ InChart η x c p := by
  unfold InChart
  rw [regAt_push]

theorem coordTie_comp_iso {o : Type} [CommRing o] [Algebra o Ω] {κ : Type} {x : κ → Ω}
    (η : Spec (CommRingCat.of Ω) ⟶ Y) (f : Y ⟶ X) [IsIso f] (h : CoordTie o η x) :
    CoordTie o (η ≫ f) x := by
  refine ⟨⟨?_, fun q => ?_⟩, fun q => ?_, fun c hc => ?_, fun c hc a => ?_⟩
  · rw [Scheme.stalkClosedPointTo_comp η f]
    have hb : Function.Bijective (f.stalkMap (η (IsLocalRing.closedPoint Ω))).hom :=
      ConcreteCategory.bijective_of_isIso _
    exact h.gen.bij.comp hb
  · obtain ⟨p, rfl⟩ := exists_push η f q
    exact genMap_push_injective η f p (h.gen.inj p)
  · obtain ⟨p, rfl⟩ := exists_push η f q
    obtain ⟨c, hc⟩ := h.cover p
    exact ⟨c, (inChart_push η f x c p).2 hc⟩
  · obtain ⟨U, hU, hq⟩ := h.affine c hc
    refine ⟨(inv f) ⁻¹ᵁ U, hU.preimage (inv f), fun q => ?_⟩
    obtain ⟨y, rfl⟩ : ∃ y, f y = q := ⟨(inv f) q, by
      rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl⟩
    have e : (inv f) (f y) = y := by
      rw [← Scheme.Hom.comp_apply, IsIso.hom_inv_id]; rfl
    have e1 : f y ∈ (inv f) ⁻¹ᵁ U ↔ y ∈ U := by
      change (inv f) (f y) ∈ U ↔ _
      rw [e]
    rw [e1, hq y]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(push η f ⟨y, h1⟩).2, (inChart_push η f x c ⟨y, h1⟩).2 h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨specializes_of_iso η f h1, (inChart_push η f x c ⟨y, specializes_of_iso η f h1⟩).1 h2⟩
  · rw [h.ring c hc a]
    constructor
    · intro H q hq
      obtain ⟨p, rfl⟩ := exists_push η f q
      rw [regAt_push]
      exact H p ((inChart_push η f x c p).1 hq)
    · intro H p hp
      have := H (push η f p) ((inChart_push η f x c p).2 hp)
      rwa [regAt_push] at this

end Transport

theorem dominates_id_iff {X Y : Scheme.{0}} {Ω : Type} [Field Ω] {ξ' : Spec (CommRingCat.of Ω) ⟶ Y}
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {f : Y ⟶ X} : Dominates ξ' ξ f (RingHom.id Ω) ↔ ξ' ≫ f = ξ := by
  unfold Dominates
  rw [show CommRingCat.ofHom (RingHom.id Ω) = 𝟙 (CommRingCat.of Ω) from rfl, Spec.map_id, Category.id_comp]

theorem mem_ctrSet_self {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} [Finite κ]
    {x : κ → Ω} (M : PModel o x) (p : Cpt M.ξ) : p ∈ ctrSet o x (RingHom.id Ω) M.ξ := by
  obtain ⟨c, hc⟩ := M.tie.cover p
  exact ⟨c, hc.1, fun a ha => (GlobalTheory.T.regAt_chart_localization o Ω κ x M c p hc).1 a ha⟩

theorem mem_ctrSet_join {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} [Finite κ]
    {x : κ → Ω} (M : PModel o x) {κ' : Type} {w : κ' → Ω} (p : Cpt M.ξ) (hw : ∃ l, InChart M.ξ w l p) :
    p ∈ ctrSet o (joinCo (RingHom.id Ω) x w) (RingHom.id Ω) M.ξ := by
  obtain ⟨c, hc⟩ := M.tie.cover p
  obtain ⟨l, hl⟩ := hw
  refine ⟨(c, l), mul_ne_zero hc.1 hl.1, fun a ha => ?_⟩
  change a ∈ regAt M.ξ p
  induction ha using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨⟨j, m⟩, rfl⟩ := hy
    have e : joinCo (RingHom.id Ω) x w (j, m) / joinCo (RingHom.id Ω) x w (c, l) =
        (x j / x c) * (w m / w l) := by
      simp only [joinCo, RingHom.id_apply]
      rw [mul_div_mul_comm]
    beta_reduce
    rw [e]
    exact mul_mem (hc.2 j) (hl.2 m)
  | algebraMap r =>
    exact (GlobalTheory.T.regAt_chart_localization o Ω κ x M c p hc).1 _ (Subalgebra.algebraMap_mem _ r)
  | add y z _ _ hy hz => exact add_mem hy hz
  | mul y z _ _ hy hz => exact mul_mem hy hz

theorem coordTie_join_of_charts : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ]
    (x : κ → Ω) (M : PModel o x) (κ' : Type) [Finite κ'] (w : κ' → Ω),
    (∀ p : Cpt M.ξ, ∃ l, InChart M.ξ w l p) → CoordTie o M.ξ (joinCo (RingHom.id Ω) x w) := by
  intro o _ Ω _ _ κ _ x M κ' _ w hw
  have hl : ∃ l, w l ≠ 0 := by
    obtain ⟨l, h⟩ := hw ⟨genPt M.ξ, specializes_rfl⟩
    exact ⟨l, h.1⟩
  obtain ⟨M', f, hf⟩ := GlobalTheory.T.exists_join_model_dominates o Ω κ x M Ω (RingHom.id Ω) κ' w (fun _ => rfl) hl
    (eq_top_iff.2 fun a _ => Subfield.subset_closure (Or.inl ⟨a, rfl⟩))
  obtain ⟨g, hg, -⟩ := GlobalTheory.T.existsUnique_dominating_map o Ω (κ × κ') _ M' o Ω κ x M (RingHom.id Ω)
    (fun p => mem_ctrSet_join M p (hw p))
  rw [dominates_id_iff] at hf hg
  have u1 := GlobalTheory.T.existsUnique_dominating_map o Ω κ x M o Ω κ x M (RingHom.id Ω) (mem_ctrSet_self M)
  have u2 := GlobalTheory.T.existsUnique_dominating_map o Ω (κ × κ') _ M' o Ω (κ × κ') _ M' (RingHom.id Ω) (mem_ctrSet_self M')
  have e1 : g ≫ f = 𝟙 _ := u1.unique (dominates_id_iff.2 (by rw [← Category.assoc, hg, hf]))
    (dominates_id_iff.2 (Category.comp_id _))
  have e2 : f ≫ g = 𝟙 _ := u2.unique (dominates_id_iff.2 (by rw [← Category.assoc, hf, hg]))
    (dominates_id_iff.2 (Category.comp_id _))
  haveI : IsIso f := ⟨g, e2, e1⟩
  have := coordTie_comp_iso M'.ξ f M'.tie
  rwa [hf] at this

end GlobalTheory.CompanionTheory.Ar.Retie
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelBaseChangeAction
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.ActBC

theorem exists_act_extends : ∀ (L L' : Type) [Field L] [Field L'] (e : L →+* L') (G : Over (Sp L)) (G' : Over (Sp L')) [GrpObj G] [GrpObj G'] (φ : G'.left ⟶ G.left), IsGrpPullback G' G (spMap e) φ → ∀ (O : Type) [CommRing O] (act : OAct O G) (act' : OAct O G'), (∀ a, (act'.act a).left ≫ φ = φ ≫ (act.act a).left) → ∀ (V V' : Type) [AddCommGroup V] [Module L V] [AddCommGroup V'] [Module L' V'] (MV : LieModel G (𝟙 (Sp L)) V) (MV' : LieModel G' (𝟙 (Sp L')) V') (j : V →+ V'), (∀ x, (MV'.pt (j x)).left ≫ φ = spMap (dualMap e) ≫ (MV.pt x).left) → Submodule.span L' (Set.range j) = ⊤ → ∀ ρ : O →+* Module.End L V, MV.IsActOf act.act ρ → ∃ ρ' : O →+* Module.End L' V', MV'.IsActOf act'.act ρ' ∧ ∀ a x, ρ' a (j x) = j (ρ a x) := by
  intro L L' _ _ e G G' _ _ φ hpb O _ act act' hcomm V V' _ _ _ _ MV MV' j hj hspan ρ hρ
  obtain ⟨ρ', hρ', -⟩ := lieModel_exists_unique_act _ _ _ _ _ MV' _ act'.act act'.hom act'.one
    act'.mul act'.add
  refine ⟨ρ', hρ', fun a x => ?_⟩
  apply MV'.inj
  apply Over.OverMorphism.ext
  apply hpb.1.hom_ext
  · rw [hρ' a (j x), Over.comp_left, Category.assoc, hcomm a, ← Category.assoc, hj x, Category.assoc,
      ← Over.comp_left, ← hρ a x, hj (ρ a x)]
  · rw [Over.w, Over.w]

end GlobalTheory.CompanionTheory.Ar.ActBC
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LineDegreeSpecialFibreStatement
section
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.line_degree_special_fibre : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)) [IsProper s] (ϖ : O), Irreducible ϖ → Function.Injective (algebraMap O Ω) → ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → IsCptGen ξ → NormalCpt ξ → _root_.IsConnected (zeroSet ξ (algebraMap O Ω ϖ)) → ∀ (L : Lat ξ Ω) (σ : Ω), L.IsVB 1 ⊤ → NumTrivMod L (algebraMap O Ω ϖ) → (∀ p ∈ genFibre O ξ, L.IsGenAt p σ) → ∃ (M : ℕ) (a : ℤ), 0 < M ∧ ∀ p : Cpt ξ, OrderAt L σ (algebraMap O Ω ϖ) M a p := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.propZ_numerical | exact GlobalTheory.CompanionTheory.Ar.Flat.propZ_numerical | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.propZ_numerical <;> assumption)
end

