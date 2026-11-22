import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0085
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DvrModelOfNumberFieldPlace
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0075
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0001
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AbelianPartHeightLinear
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.MorphismEqOfGenericPointEq
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0016
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0004
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0008
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GermSys
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrData
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.WchartLePreimage
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0011
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0041
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteExtensionCoordsCompare
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EtaleLocalizationAtPrimeTensorOfLowHeight
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0084
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0039
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0050
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0072
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DvrLocalizationConstantsStatement
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvr_localization_constants : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω), CoordTie ℤ ξ (mseg y) → ∀ (A : Type) [CommRing A] [Algebra A Ω], HasConstants ℤ A y → ∀ (m : Ideal A) [m.IsPrime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω] (c : ∀ k, J k), mseg y c ≠ 0 → (∀ a ∈ chartRing O (mseg y) c, ∀ q : Cpt ξ, InChart ξ (mseg y) c q → (∀ o : O, algebraMap O Ω o ∈ regAt ξ q) → a ∈ regAt ξ q) ∧ (∀ P : Ideal (chartRing O (mseg y) c), P.IsPrime → ∃ q : Cpt ξ, InChart ξ (mseg y) c q ∧ (∀ o : O, algebraMap O Ω o ∈ regAt ξ q) ∧ ∀ s : chartRing O (mseg y) c, s ∉ P ↔ unitAt ξ q (s : Ω)) ∧ (∀ q : Cpt ξ, InChart ξ (mseg y) c q → (∀ o : O, algebraMap O Ω o ∈ regAt ξ q) → ∀ a ∈ regAt ξ q, ∃ s ∈ chartRing O (mseg y) c, unitAt ξ q s ∧ s * a ∈ chartRing O (mseg y) c) ∧ (∀ q : Cpt ξ, InChart ξ (mseg y) c q → (∀ o : O, algebraMap O Ω o ∈ regAt ξ q) → ∀ U : X.Opens, q.1 ∈ U → ∃ g ∈ chartRing O (mseg y) c, unitAt ξ q g ∧ ∀ q' : Cpt ξ, InChart ξ (mseg y) c q' → (∀ o : O, algebraMap O Ω o ∈ regAt ξ q') → unitAt ξ q' g → q'.1 ∈ U) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.FamEx.chart_points_over_place | exact GlobalTheory.CompanionTheory.Ar.Num.FamEx.chart_points_over_place | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.FamEx.chart_points_over_place <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DvrModelOfNumberFieldPlaceStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvr_model_of_number_field_place : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (κ : Type) [Finite κ] (x : κ → Ω) (F' : Type) [Field F'] [NumberField F'] (ψ : F' →+* Ω) (v : HeightOneSpectrum (𝓞 F')) (π : F'), (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ x → NormalCpt ξ → v.valuation F' π = WithZero.exp (-1 : ℤ) → ∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (_ : IsDiscreteValuationRing O) (_ : Algebra O Ω) (X' : Scheme.{0}) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (s : X' ⟶ Spec (CommRingCat.of O)) (g : X' ⟶ X) (ϖ : O), IsProper s ∧ Irreducible ϖ ∧ Function.Injective (algebraMap O Ω) ∧ ξ' ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) ∧ ξ' ≫ g = ξ ∧ IsCptGen ξ' ∧ (∀ q' : X', genPt ξ' ⤳ q') ∧ algebraMap O Ω ϖ = ψ π ∧ (∀ a : Ω, a ∈ (algebraMap O Ω).range ↔ ∃ b : F', v.valuation F' b ≤ 1 ∧ ψ b = a) ∧ (∀ (p' : Cpt ξ') (p : Cpt ξ), p.1 = g p'.1 → ∀ a : Ω, a ∈ regAt ξ' p' ↔ a ∈ regAt ξ p) ∧ ∀ p : Cpt ξ, (∀ a : F', v.valuation F' a ≤ 1 → ψ a ∈ regAt ξ p) → ∃ p' : Cpt ξ', g p'.1 = p.1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.LocModel.exists_localisation | exact GlobalTheory.CompanionTheory.Ar.Flat.LocModel.exists_localisation | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.LocModel.exists_localisation <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenspaceDecompositionInternal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

open Polynomial NumberField

theorem iSupIndep_eigSp {Ω E F I : Type} [Field Ω] [CharZero Ω] [AddCommGroup E] [Module Ω E] [Field F] [NumberField F]
    (ρ : 𝓞 F →+* Module.End Ω E) (σ : I → (𝓞 F →+* Ω)) (hσ : Function.Injective σ) :
    iSupIndep fun s => eigSp ρ (σ s) := by
  obtain ⟨θ, -, -, -, -, hgen⟩ := Cusp.exists_integral_generator F
  have hagree : ∀ (τ : 𝓞 F →+* Ω) (P : ℤ[X]), τ (aeval θ P) = aeval (τ θ) P := fun τ P =>
    (aeval_algHom_apply τ.toIntAlgHom θ P).symm
  have hinj : Function.Injective fun s => σ s θ := by
    intro s t hst
    apply hσ
    ext a
    obtain ⟨n, P, hn, hP⟩ := hgen a
    have h1 := hagree (σ s) P
    have h2 := hagree (σ t) P
    have hst' : σ s θ = σ t θ := hst
    rw [hst', ← h2, ← hP, map_mul, map_mul, map_intCast, map_intCast] at h1
    exact mul_left_cancel₀ (by exact_mod_cast hn) h1
  refine ((Module.End.eigenspaces_iSupIndep (ρ θ)).comp hinj).mono fun s x hx => ?_
  have hx' := (Submodule.mem_iInf _).1 hx θ
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hx'
  exact Module.End.mem_eigenspace_iff.2 hx'

theorem isInternal_eigSp : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (E : Type) [AddCommGroup E] [Module Ω E] (F : Type) [Field F] [NumberField F] (ρ : NumberField.RingOfIntegers F →+* Module.End Ω E) (I : Type) [Fintype I] [DecidableEq I] (σ : I → (NumberField.RingOfIntegers F →+* Ω)), Function.Injective σ → Fintype.card I = Module.finrank ℚ F → DirectSum.IsInternal fun s => eigSp ρ (σ s) := by
  intro Ω _ _ E _ _ F _ _ ρ I _ _ σ hσ hcard
  exact DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top (iSupIndep_eigSp ρ σ hσ)
    (Cusp.iSup_eigSp_eq_top ρ σ hσ hcard)

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EqOfEqGenericProjective
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem maps_eq_of_eq_at_generic : ∀ (R : Type) [CommRing R] (Z W : Scheme.{0}) [IsIntegral Z] (s : W ⟶ Sp R) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ Z) (f g : Z ⟶ W), IsProjOver s → (∀ q : Z, genPt ξ ⤳ q) → ξ ≫ f = ξ ≫ g → f = g :=
  @PositivityTheory.UnitarySelfGeneration.morphism_eq_of_generic_point_eq

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsIsometricHermLineStatement
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isometric_herm_line : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MvPolynomial (Σ k, ι k) ℤ)) (D : ℕ), IsArithVar P (D + 1) → ∀ (S : Finset Nat.Primes) (T : LocPair ι ℤ Unit), T.IsVertOff P S → ∀ A : HermLine ι, A.a = T.x () → IsSmoothHerm A → IsConjInvariantH A → ∃ A' : HermLine ι, IsSmoothHerm A' ∧ IsConjInvariantH A' ∧ T.IsIsometric P (fun _ => A) (fun _ => A') := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.twist_line | exact GlobalTheory.CompanionTheory.Ar.Num.twist_line | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.twist_line <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsStandardSmoothLocalizationStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.SncRes
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_standard_smooth_localization : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (e : ℕ) (hA : IsArithVar (mCoordIdeal y) (e + 1)) (N : ℕ) (E : Fin (N + 1) ≃ ((k : K) → ι k)) (c₀ : Fin (N + 1)) (hc : ∀ k, y ⟨k, E c₀ k⟩ ≠ 0), ∃ s : Algebra.adjoin ℚ (Set.range fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩), s ≠ 0 ∧ Algebra.IsStandardSmoothOfRelativeDimension e ℚ (Localization.Away s) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SegreChart.exists_away_standardSmooth | exact GlobalTheory.CompanionTheory.Ar.SegreChart.exists_away_standardSmooth | (intros; apply GlobalTheory.CompanionTheory.Ar.SegreChart.exists_away_standardSmooth <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsSubMemEigW
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.DegZ

open Module

section Map

variable {R S : Type} [CommRing R] [CommRing S] {d : ℕ}

def vmap (f : R →+* S) (y : (Fin d → R) × (Fin d → R)) : (Fin d → S) × (Fin d → S) :=
  (fun i => f (y.1 i), fun i => f (y.2 i))

theorem vmap_add (f : R →+* S) (y y' : (Fin d → R) × (Fin d → R)) :
    vmap f (y + y') = vmap f y + vmap f y' := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> simp [vmap]

theorem vmap_sub (f : R →+* S) (y y' : (Fin d → R) × (Fin d → R)) :
    vmap f (y - y') = vmap f y - vmap f y' := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> simp [vmap]

theorem vmap_zero (f : R →+* S) : vmap f (0 : (Fin d → R) × (Fin d → R)) = 0 := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> simp [vmap]

theorem vmap_smul (f : R →+* S) (c : R) (y : (Fin d → R) × (Fin d → R)) :
    vmap f (c • y) = f c • vmap f y := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> simp [vmap]

theorem vmap_sum {A : Type} (s : Finset A) (f : R →+* S) (y : A → (Fin d → R) × (Fin d → R)) :
    vmap f (∑ i ∈ s, y i) = ∑ i ∈ s, vmap f (y i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using vmap_zero f
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, vmap_add, ih]

theorem vmap_comp {T : Type} [CommRing T] (f : R →+* S) (g : S →+* T) (y : (Fin d → R) × (Fin d → R)) :
    vmap g (vmap f y) = vmap (g.comp f) y := rfl

theorem lin_map (f : R →+* S) (φ : Germ.Pt R 1 d) (m : ℕ) :
    lin (fun i => MvPowerSeries.map f (φ i)) m = (lin φ m).map f := by
  ext i j
  simp [lin, Matrix.map_apply, MvPowerSeries.coeff_map]

theorem bil_map (f : R →+* S) (g : Germ.PS R 2 d) (m n : ℕ) :
    bil (MvPowerSeries.map f g) m n = (bil g m n).map f := by
  ext i j
  simp [bil, Matrix.map_apply, MvPowerSeries.coeff_map]

theorem map_mulVec' (f : R →+* S) (M : Matrix (Fin d) (Fin d) R) (v : Fin d → R) :
    (fun i => f (M.mulVec v i)) = (M.map f).mulVec fun i => f (v i) :=
  funext fun i => RingHom.map_mulVec _ _ _ _

theorem vmap_transH (f : R →+* S) (φ ψ : Germ.Pt R 1 d) (lam : Germ.PS R 2 d)
    (y : (Fin d → R) × (Fin d → R)) :
    vmap f (transH φ ψ lam y) = transH (fun i => MvPowerSeries.map f (φ i)) (fun i => MvPowerSeries.map f (ψ i))
      (MvPowerSeries.map f lam) (vmap f y) := by
  rw [transH_apply, transH_apply, lin_map, lin_map, bil_map]
  refine Prod.ext ?_ ?_
  · exact map_mulVec' f _ _
  · have h1 := map_mulVec' f (lin ψ 1).transpose (y.2 + (bil lam 1 1).transpose.mulVec y.1)
    have h2 := map_mulVec' f (bil lam 1 1).transpose y.1
    change (fun i => f ((lin ψ 1).transpose.mulVec (y.2 + (bil lam 1 1).transpose.mulVec y.1) i)) = _
    rw [h1, Matrix.transpose_map]
    congr 1
    change _ = (fun i => f (y.2 i)) + ((bil lam 1 1).map f).transpose.mulVec fun i => f (y.1 i)
    rw [← Matrix.transpose_map, ← h2]
    funext i
    simp

variable {O : Type} [CommRing O] [StarRing O]

theorem rho_map {f : R →+* S} {B : Germ.FB R d O} {B₂ : Germ.FB S d O} (h : IsMapOf f B B₂) (a : O) :
    rho B₂ a = (rho B a).map f := by
  have : B₂.A.act a = fun i => MvPowerSeries.map f (B.A.act a i) := funext (h.act a)
  rw [rho, this, lin_map]
  rfl

theorem vmap_rhoH {f : R →+* S} {B : Germ.FB R d O} {B₂ : Germ.FB S d O} (h : IsMapOf f B B₂) (a : O)
    (y : (Fin d → R) × (Fin d → R)) : vmap f (rhoH B a y) = rhoH B₂ a (vmap f y) := by
  rw [rhoH_apply, rhoH_apply, rho_map h, rho_map h, h.ad, bil_map]
  refine Prod.ext ?_ ?_
  · exact map_mulVec' f _ _
  · have h1 := map_mulVec' f (rho B (star a)).transpose y.2
    have h2 := map_mulVec' f (bil (B.ad a) 1 1).transpose y.1
    rw [Matrix.transpose_map] at h1 h2
    change (fun i => f (((rho B (star a)).transpose.mulVec y.2 - (bil (B.ad a) 1 1).transpose.mulVec y.1) i)) = _
    change _ = ((rho B (star a)).map f).transpose.mulVec (fun i => f (y.2 i)) -
      ((bil (B.ad a) 1 1).map f).transpose.mulVec fun i => f (y.1 i)
    rw [← Matrix.transpose_map, ← Matrix.transpose_map] at *
    rw [← h1, ← h2]
    funext i
    simp

end Map

end GlobalTheory.CompanionTheory.Ar.Flat.DegZ

namespace GlobalTheory.CompanionTheory.Ar.Flat.DegZ

section H

variable {E : Type} [Field E] [NumberField E] [StarRing (𝓞 E)]

def IsHBasis {R : Type} [CommRing R] {d r : ℕ} (B : Germ.FB R d (𝓞 E))
    (x : Fin r → (Fin d → R) × (Fin d → R)) : Prop :=
  LinearIndependent R (fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) =>
      rhoH B (RingOfIntegers.basis E q.2) (x q.1)) ∧
    Submodule.span R (Set.range fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) =>
      rhoH B (RingOfIntegers.basis E q.2) (x q.1)) = ⊤

def eigW {R : Type} [CommRing R] {d : ℕ} (B : Germ.FB R d (𝓞 E)) (τ : 𝓞 E →+* R) :
    Submodule R ((Fin d → R) × (Fin d → R)) :=
  ⨆ a : 𝓞 E, LinearMap.range (rhoH B a - τ a • LinearMap.id)

theorem vmap_mem_eigW {R S : Type} [CommRing R] [CommRing S] {d : ℕ} {f : R →+* S} {B : Germ.FB R d (𝓞 E)}
    {B₂ : Germ.FB S d (𝓞 E)} (h : IsMapOf f B B₂) (τ : 𝓞 E →+* R) {y : (Fin d → R) × (Fin d → R)}
    (hy : y ∈ eigW B τ) : vmap f y ∈ eigW B₂ (f.comp τ) := by
  refine Submodule.iSup_induction (motive := fun y => vmap f y ∈ eigW B₂ (f.comp τ)) _ hy ?_ ?_ ?_
  · rintro a _ ⟨w, rfl⟩
    refine Submodule.mem_iSup_of_mem a ⟨vmap f w, ?_⟩
    simp [vmap_sub, vmap_smul, vmap_rhoH h]
  · simp [vmap_zero]
  · intro y y' h1 h2
    rw [vmap_add]
    exact add_mem h1 h2

theorem eigW_induction {R : Type} [CommRing R] {d : ℕ} {B : Germ.FB R d (𝓞 E)} {τ : 𝓞 E →+* R}
    {P : (Fin d → R) × (Fin d → R) → Prop} {w : (Fin d → R) × (Fin d → R)} (hw : w ∈ eigW B τ)
    (hg : ∀ a y, P (rhoH B a y - τ a • y)) (h0 : P 0) (hadd : ∀ y y', P y → P y' → P (y + y')) : P w := by
  refine Submodule.iSup_induction (motive := P) _ hw ?_ h0 hadd
  rintro a _ ⟨y, rfl⟩
  exact hg a y

theorem exists_sub_mem_eigW {R : Type} [CommRing R] {d r : ℕ} {B : Germ.FB R d (𝓞 E)}
    {x : Fin r → (Fin d → R) × (Fin d → R)} (h : IsHBasis B x) (τ : 𝓞 E →+* R)
    (y : (Fin d → R) × (Fin d → R)) : ∃ m : Fin r → R, y - ∑ l, m l • x l ∈ eigW B τ := by
  have hy : y ∈ Submodule.span R (Set.range fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) =>
      rhoH B (RingOfIntegers.basis E q.2) (x q.1)) := h.2 ▸ trivial
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨q, rfl⟩ := hy
    classical
    refine ⟨Pi.single q.1 (τ (RingOfIntegers.basis E q.2)), ?_⟩
    refine Submodule.mem_iSup_of_mem (RingOfIntegers.basis E q.2) ⟨x q.1, ?_⟩
    simp [Pi.single_apply, ite_smul]
  | zero => exact ⟨0, by simp⟩
  | add y y' _ _ h1 h2 =>
    obtain ⟨m, hm⟩ := h1
    obtain ⟨m', hm'⟩ := h2
    refine ⟨m + m', ?_⟩
    have := add_mem hm hm'
    convert this using 1
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
    abel
  | smul c y _ h1 =>
    obtain ⟨m, hm⟩ := h1
    refine ⟨c • m, ?_⟩
    have := (eigW B τ).smul_mem c hm
    convert this using 1
    simp only [Pi.smul_apply, smul_sub, Finset.smul_sum, smul_eq_mul, mul_smul]

theorem vmap_rel {R R' K L : Type} [CommRing R] [CommRing R'] [CommRing K] [CommRing L] {d r : ℕ} (v₀ : R →+* K)
    (v : R' →+* L) (j : L →+* K) (c : R' →+* R) (h : j.comp v = v₀.comp c) (φ' ψ' : Germ.Pt R 1 d)
    (lam' : Germ.PS R 2 d) (x' : (Fin d → R') × (Fin d → R')) (m : Fin r → R)
    (x : Fin r → (Fin d → R) × (Fin d → R)) :
    vmap v₀ (transH φ' ψ' lam' (vmap c x') - ∑ l, m l • x l) =
      transH (fun i => MvPowerSeries.map v₀ (φ' i)) (fun i => MvPowerSeries.map v₀ (ψ' i))
        (MvPowerSeries.map v₀ lam') (vmap j (vmap v x')) - ∑ l, v₀ (m l) • vmap v₀ (x l) := by
  rw [vmap_sub, vmap_transH, vmap_comp, vmap_comp, h, vmap_sum]
  simp only [vmap_smul]

end H

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} [StarRing (𝓞 E)]
  {Ω : Type} [Field Ω] {t : SAB H X} {ξ : Spec (CommRingCat.of Ω) ⟶ X} {d : ℕ}
  {M : LieModel t.G ξ (Fin d → Ω)}

def toVec (Ω : Type) [Field Ω] (d : ℕ) :
    ((Fin d → Ω) × (Fin d → Ω)) →ₗ[Ω] (Fin d → Ω) × Module.Dual Ω (Fin d → Ω) :=
  LinearMap.prodMap LinearMap.id (dotProductBilin Ω Ω)

def toH (S : GermSys t ξ M) (p : Cpt ξ) (y : (Fin d → X.presheaf.stalk p.1) × (Fin d → X.presheaf.stalk p.1)) :
    (Fin d → Ω) × Module.Dual Ω (Fin d → Ω) :=
  toVec Ω d (transH (S.φ p) (S.ψ p) (S.lam p) (vmap (genMap ξ p) y))

theorem toH_add (S : GermSys t ξ M) (p : Cpt ξ)
    (y y' : (Fin d → X.presheaf.stalk p.1) × (Fin d → X.presheaf.stalk p.1)) :
    toH S p (y + y') = toH S p y + toH S p y' := by
  simp [toH, vmap_add]

theorem toH_sub (S : GermSys t ξ M) (p : Cpt ξ)
    (y y' : (Fin d → X.presheaf.stalk p.1) × (Fin d → X.presheaf.stalk p.1)) :
    toH S p (y - y') = toH S p y - toH S p y' := by
  simp [toH, vmap_sub]

theorem toH_zero (S : GermSys t ξ M) (p : Cpt ξ) :
    toH S p (0 : (Fin d → X.presheaf.stalk p.1) × (Fin d → X.presheaf.stalk p.1)) = 0 := by
  simp [toH, vmap_zero]

theorem toH_smul (S : GermSys t ξ M) (p : Cpt ξ) (c : X.presheaf.stalk p.1)
    (y : (Fin d → X.presheaf.stalk p.1) × (Fin d → X.presheaf.stalk p.1)) :
    toH S p (c • y) = genMap ξ p c • toH S p y := by
  simp [toH, vmap_smul]

theorem toH_sum {A : Type} (s : Finset A) (S : GermSys t ξ M) (p : Cpt ξ)
    (y : A → (Fin d → X.presheaf.stalk p.1) × (Fin d → X.presheaf.stalk p.1)) :
    toH S p (∑ i ∈ s, y i) = ∑ i ∈ s, toH S p (y i) := by
  simp [toH, vmap_sum]

theorem toH_spec (S : GermSys t ξ M) (p q : Cpt ξ) (h : q.1 ⤳ p.1) {φ' ψ' : Germ.Pt (X.presheaf.stalk q.1) 1 d}
    {lam' : Germ.PS (X.presheaf.stalk q.1) 2 d}
    (he : transH (S.φ p) (S.ψ p) (S.lam p) = transH (S.φ q) (S.ψ q) (S.lam q) ∘ₗ
      transH (fun i => MvPowerSeries.map (genMap ξ q) (φ' i)) (fun i => MvPowerSeries.map (genMap ξ q) (ψ' i))
        (MvPowerSeries.map (genMap ξ q) lam'))
    (y : (Fin d → X.presheaf.stalk p.1) × (Fin d → X.presheaf.stalk p.1)) :
    toH S p y = toH S q (transH φ' ψ' lam' (vmap (X.presheaf.stalkSpecializes h).hom y)) := by
  have h1 : (genMap ξ q).comp (X.presheaf.stalkSpecializes h).hom = genMap ξ p :=
    RingHom.ext fun s => ProjectiveLinePlaces.genMap_specializes h q.2 p.2 s
  rw [toH, toH, vmap_transH, vmap_comp, h1, he]
  rfl

end Gen

end GlobalTheory.CompanionTheory.Ar.Flat.DegZ
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FieldPointLiftsGenericFibre
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.M0
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.M0

theorem fieldPoint_lifts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), (letI := β.toAlgebra; IsFractionRing O c.F) → ∀ (K : Type) [Field K] (x : Sp K ⟶ Y.X), Set.range x ⊆ Set.range Y.j → ∃ y : Sp K ⟶ Xo.XF c, y ≫ Y.j = x :=
  @PositivityTheory.HtPt.Ml.lift_generic_point

end GlobalTheory.CompanionTheory.Ar.M0
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteExtensionCoordsCompareStatement
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_extension_coords_compare : ∀ (Ω₁ Ω₂ Ω : Type) [Field Ω₁] [Field Ω₂] [Field Ω] [CharZero Ω] (i₁ : Ω₁ →+* Ω) (i₂ : Ω₂ →+* Ω) (K₁ K₂ : Type) [Fintype K₁] [Fintype K₂] (J₁ : K₁ → Type) (J₂ : K₂ → Type) [∀ k, Fintype (J₁ k)] [∀ k, Fintype (J₂ k)] (y₁ : (Σ k, J₁ k) → Ω₁) (y₂ : (Σ k, J₂ k) → Ω₂) (X₁ X₂ : Scheme.{0}) (ξ₁ : Spec (CommRingCat.of Ω₁) ⟶ X₁) (ξ₂ : Spec (CommRingCat.of Ω₂) ⟶ X₂), (letI := i₁.toAlgebra; Module.Finite Ω₁ Ω) → (∀ q : X₁, genPt ξ₁ ⤳ q) → (∀ q : X₂, genPt ξ₂ ⤳ q) → CoordTie ℤ ξ₁ (fun c' : (k : K₁) → J₁ k => ∏ k, y₁ ⟨k, c' k⟩) → CoordTie ℤ ξ₂ (fun c' : (k : K₂) → J₂ k => ∏ k, y₂ ⟨k, c' k⟩) → ∃ (m : ℕ) (w : Fin m → Ω) (y : (Σ k : K₁ ⊕ K₂ ⊕ Unit, Sum.elim J₁ (Sum.elim J₂ fun _ => Fin m) k) → Ω) (Z : Scheme.{0}) (ξ : Spec (CommRingCat.of Ω) ⟶ Z) (h₁ : Z ⟶ X₁) (h₂ : Z ⟶ X₂), (∀ k a, y ⟨.inl k, a⟩ = i₁ (y₁ ⟨k, a⟩)) ∧ (∀ k a, y ⟨.inr (.inl k), a⟩ = i₂ (y₂ ⟨k, a⟩)) ∧ (∀ a, y ⟨.inr (.inr ()), a⟩ = w a) ∧ (∀ q : Z, genPt ξ ⤳ q) ∧ CoordTie ℤ ξ (fun c' : (k : K₁ ⊕ K₂ ⊕ Unit) → Sum.elim J₁ (Sum.elim J₂ fun _ => Fin m) k => ∏ k, y ⟨k, c' k⟩) ∧ (∀ q : Z, IsDomain (Z.presheaf.stalk q) ∧ IsIntegrallyClosed (Z.presheaf.stalk q)) ∧ Dominates ξ ξ₁ h₁ i₁ ∧ Dominates ξ ξ₂ h₂ i₂ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HtJoin.exists_normal_join | exact GlobalTheory.CompanionTheory.Ar.HtJoin.exists_normal_join | (intros; apply GlobalTheory.CompanionTheory.Ar.HtJoin.exists_normal_join <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagModelStatementHoldsStatement
section
open GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.FlagModelStatement_holds : FlagModelStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagModel.flagModel | exact GlobalTheory.CompanionTheory.Ar.FlagModel.flagModel | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagModel.flagModel <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatHermUnitSectionAvoid
section
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem isOpen_blockNonzero {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] :
    IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  simp only [Set.setOf_forall, Set.setOf_exists]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

theorem PtOver.eventually_ptOver {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    {F : Type} [Field F] [NumberField F] {y : (Σ k, ι k) → Ω} {φ : F →+* Ω} (hO : OverInt y φ)
    {σ : F →+* ℂ} {z : (Σ k, ι k) → ℂ} (hz : PtOver y φ σ z) :
    ∀ᶠ w in nhds z, w ∈ mcPts (mCoordIdeal y) → PtOver y φ σ w := by
  classical
  let e := Finite.equivFin (F →+* ℂ)
  let t : (F →+* ℂ) → ℝ := fun τ => ((e τ : ℕ) : ℝ)
  have ht : Function.Injective t := fun a b hab => by
    have h0 : ((e a : ℕ) : ℝ) = ((e b : ℕ) : ℝ) := hab
    have : ((e a : ℕ)) = (e b : ℕ) := by exact_mod_cast h0
    exact e.injective (Fin.ext this)
  obtain ⟨u, hu, -⟩ := GlobalTheory.T.exists_place_weight_conj_invariant K ι Ω F y φ t hO
  filter_upwards [hu.near σ z hz] with w hw hwP
  obtain ⟨τ, hτ, -⟩ := GlobalTheory.T.complex_point_existsUnique_embedding K ι Ω F y φ hO w hwP
  have h1 : u w = t τ := (hu.near τ w hτ).self_of_nhds
  have h2 : τ = σ := ht (h1.symm.trans hw)
  exact h2 ▸ hτ

theorem FlatHerm.exists_rep : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) (A : HermLine ι) (S : FlatHerm y φ A) (d : ℕ) (W : Ideal (MRing ι)), OverInt y φ → IsArithVar (mCoordIdeal y) d → IsSmoothHerm A → IsMultiProjPrime W → mCoordIdeal y ≤ W → ∃ (f' g' : MRing ι) (df' dg' : K → ℕ), IsMultiHomog f' df' ∧ IsMultiHomog g' dg' ∧ (∀ k, (df' k : ℤ) - dg' k = S.M * A.a k) ∧ f' ∉ W ∧ g' ∉ W ∧ f' * S.g - g' * S.f ∈ mCoordIdeal y ∧ IsUnitSec (mCoordIdeal y) f' g' ∧ ∀ σ z, PtOver y φ σ z → ‖evC z f'‖ = (S.κ σ * A.h z) ^ S.M * ‖evC z g'‖ := by
  intro K _ ι _ Ω _ F _ _ y φ A S d W hO hV hA hW hPW
  obtain ⟨f', g', df', dg', hf', hg', hdeg, hfW, hgW, hrel, hunit⟩ :=
    GlobalTheory.T.unit_section_avoid_prime K ι (mCoordIdeal y) W S.f S.g S.df S.dg hV.2.1 hW hPW S.hf S.hg S.g_ne S.unit
  refine ⟨f', g', df', dg', hf', hg', fun k => (hdeg k).trans (S.deg k), hfW, hgW, hrel, hunit, ?_⟩
  intro σ z hz
  have hcl := GlobalTheory.T.complex_points_dense_nonvanishing K ι (mCoordIdeal y) d S.g hV S.g_ne hz.1
  have hfreq := mem_closure_iff_frequently.mp hcl
  have hnear := PtOver.eventually_ptOver hO hz
  have hcontA : ContinuousAt A.h z :=
    (hA.continuousOn).continuousAt (isOpen_blockNonzero.mem_nhds hz.1.1)
  have hcf : Continuous fun w : (Σ k, ι k) → ℂ => evC w f' := MvPolynomial.continuous_eval _
  have hcg : Continuous fun w : (Σ k, ι k) → ℂ => evC w g' := MvPolynomial.continuous_eval _
  have hL : Filter.Tendsto (fun w => ‖evC w f'‖) (nhds z) (nhds ‖evC z f'‖) :=
    hcf.norm.continuousAt
  have hR : Filter.Tendsto (fun w => (S.κ σ * A.h w) ^ S.M * ‖evC w g'‖) (nhds z)
      (nhds ((S.κ σ * A.h z) ^ S.M * ‖evC z g'‖)) :=
    (((continuousAt_const.mul hcontA).pow S.M).mul hcg.norm.continuousAt)
  refine tendsto_nhds_unique_of_frequently_eq hL hR ?_
  refine (hfreq.and_eventually hnear).mono ?_
  rintro w ⟨⟨hwP, hgw⟩, hwσ⟩
  have hover := hwσ hwP
  have hn := S.norm σ w hover
  have h0 : evC w f' * evC w S.g - evC w g' * evC w S.f = 0 := by
    have := hwP.2 _ hrel
    simpa [evC, map_sub, map_mul] using this
  have h1 : ‖evC w f'‖ * ‖evC w S.g‖ = ‖evC w g'‖ * ‖evC w S.f‖ := by
    rw [← norm_mul, ← norm_mul, sub_eq_zero.mp h0]
  have hg0 : ‖evC w S.g‖ ≠ 0 := norm_ne_zero_iff.mpr hgw
  apply mul_right_cancel₀ hg0
  rw [h1, hn]
  ring

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FullTorsionPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HcptPull

theorem fullTorsion_of_dominates : ∀ (X X' : Scheme.{0}) (Ω Ω' : Type) [Field Ω] [Field Ω'] (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω' ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω') (G : Over X) (G' : Over X') [GrpObj G] [GrpObj G'] [IsCommMonObj G] [IsCommMonObj G'] (φ : G'.left ⟶ G.left) (n : ℕ), GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → IsGrpPullback G' G f φ → FullTorsion G ξ n → FullTorsion G' ξ' n := by
  intro X X' Ω Ω' _ _ ξ ξ' f i G G' _ _ _ _ φ n hd hp hf k _ i' g hg
  have hd' : ξ' ≫ f = spMap i ≫ ξ := hd
  have e : (spMap i' ≫ ξ') ≫ f = spMap (i'.comp i) ≫ ξ := by
    rw [Category.assoc, hd', ← Category.assoc]
    congr 1
    simp only [spMap]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  let ρ : (Over.mk (spMap i' ≫ ξ') ⟶ G') →* (Over.mk ((spMap i' ≫ ξ') ≫ f) ⟶ G) :=
    MonoidHom.mk' (pushPt hp.1.w) fun x y => Over.OverMorphism.ext (hp.2 _ x y _ _ rfl rfl).symm
  have ha : (ρ g) ^ n = 1 := by rw [← map_pow, hg, map_one]
  have tr : ∀ {a b : Sp k ⟶ X} (_ : a = b) (u : Over.mk a ⟶ G), u ^ n = 1 →
      ∃ u' : Over.mk b ⟶ G, u'.left = u.left ∧ u' ^ n = 1 := by
    intro a b h u hu
    subst h
    exact ⟨u, rfl, hu⟩
  obtain ⟨u, hl, hu⟩ := tr e (ρ g) ha
  obtain ⟨x, hx⟩ := hf k (i'.comp i) u hu
  have hxw : x.left ≫ G.hom = ξ := by simpa using Over.w x
  have hw : (spMap i ≫ x.left) ≫ G.hom = ξ' ≫ f := by
    rw [Category.assoc, hxw, hd']
  have hs : spMap (i'.comp i) = spMap i' ≫ spMap i := by
    simp only [spMap]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  refine ⟨Over.homMk (hp.1.lift (spMap i ≫ x.left) ξ' hw) (hp.1.lift_snd _ _ _), ?_⟩
  apply hp.1.hom_ext
  · have h1 : g.left ≫ φ = spMap (i'.comp i) ≫ x.left := by
      rw [← hx, hl]
      rfl
    simp only [Over.homMk_left, Category.assoc, IsPullback.lift_fst]
    rw [h1, hs, Category.assoc]
  · have h2 : g.left ≫ G'.hom = spMap i' ≫ ξ' := by simpa using Over.w g
    simp only [Over.homMk_left, Category.assoc, IsPullback.lift_snd]
    exact h2

end GlobalTheory.CompanionTheory.Ar.HcptPull
end
end

