import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0020
import ReciprocityTheory.DualLattices.Bundle0005
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0003
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0004
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0016
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0009
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.Avoid
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsFinFlatSub
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.Bundle0001
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0002
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0010

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderSubgroupLengthStatement
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stable_hopf_order_subgroup_length : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (K : Submodule F N) (t : N) (τ : MulChar F R) (c : R), c ∈ idealD p AA.carrier K t τ → c ^ p ∈ idealD p AA.carrier K t (τ ^ p) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.idealD_pow_mem | exact GlobalTheory.CompanionTheory.Ar.GR.idealD_pow_mem | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.idealD_pow_mem <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TeichmullerLiftOfEmbedding
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num NumberField

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem teichmuller_lift_of_embedding : ∀ (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O] (F : Type) [Field F] [Fintype F] (p : ℕ) [Fact p.Prime] [CharP F p] (ζ : O), IsPrimitiveRoot ζ (Fintype.card F - 1) → ∀ σ : F →+* IsLocalRing.ResidueField O, (∃! χ : F →*₀ O, ∀ a, IsLocalRing.residue O (χ a) = σ a) ∧ ∀ (σ' : F →+* IsLocalRing.ResidueField O) (χ χ' : F →*₀ O), (∀ a, σ' a = σ a ^ p) → (∀ a, IsLocalRing.residue O (χ a) = σ a) → (∀ a, IsLocalRing.residue O (χ' a) = σ' a) → ∀ a, χ' a = χ a ^ p :=
  PositivityTheory.HtPt.Teich.glue_teich

end GlobalTheory.CompanionTheory.Ar.Num
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TopAvoid
section
namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem topAvoid : ReciprocityTheory.ChartRestriction.G.AI.I2.AvoidStatement :=
  GroundTheory.Heights₂.Heights.ForSecondHalf.avoid

end GlobalTheory.CompanionTheory.Ar.Giv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TorsionPointsFinite
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem tors_pts_finite : ∀ (R : Type) [CommRing R] [IsDomain R] (p : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] (T : TorsRep G p) (N : Type) [AddCommGroup N] (pt : N → (sp (R₀ := R) R ⟶ G)), IsTorsPts G p pt → Finite N := by
  intro R _ _ p G _ T N _ pt h
  haveI := T.free
  haveI := T.fin
  have hx : ∀ x, ∃ φ : T.A →ₐ[R] R, spMap φ ≫ T.y = pt x := fun x =>
    (T.univ R (pt x) ((h.range _).2 ⟨x, rfl⟩)).exists
  choose f hf using hx
  refine Finite.of_injective f fun x y e => h.inj ?_
  rw [← hf x, ← hf y, e]

end GlobalTheory.CompanionTheory.Ar.GR
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TrivialPolarizedAbelianPointEqOneStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trivial_polarized_abelian_point_eq_one : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (P : Out.PolAV (Spec (CommRingCat.of R))), P.g = 0 → ∀ z : sp (R₀ := R) R ⟶ P.A, z = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.DimZero.eq_one_of_g_eq_zero | exact GlobalTheory.CompanionTheory.Ar.DimZero.eq_one_of_g_eq_zero | (intros; apply GlobalTheory.CompanionTheory.Ar.DimZero.eq_one_of_g_eq_zero <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TwistedModuleFiniteProjectiveRank
section
namespace GlobalTheory.CompanionTheory.Ar.TwModule

open GlobalTheory.CompanionTheory.Ar

variable {O : Type} [CommRing O] (s : O ≃+* O) (L : Type) [AddCommGroup L] [Module O L]

theorem twMod_smul (c : O) (x : L) :
    (c • (show TwMod s L from x) : TwMod s L) = (show TwMod s L from s c • x) := rfl

def twOut {n : ℕ} (f : (Fin n → O) →ₗ[O] L) : (Fin n → O) →ₗ[O] TwMod s L where
  toFun v := (show TwMod s L from f (fun i => s (v i)))
  map_add' v w := by
    have : (fun i => s ((v + w) i)) = (fun i => s (v i)) + (fun i => s (w i)) := by
      funext i; simp
    show f (fun i => s ((v + w) i)) = f (fun i => s (v i)) + f (fun i => s (w i))
    rw [this, map_add]
  map_smul' c v := by
    have : (fun i => s ((c • v) i)) = s c • (fun i => s (v i)) := by
      funext i; simp
    show f (fun i => s ((c • v) i)) = s c • f (fun i => s (v i))
    rw [this, map_smul]

def twIn {n : ℕ} (r : L →ₗ[O] (Fin n → O)) : TwMod s L →ₗ[O] (Fin n → O) where
  toFun x := fun i => s.symm (r (show L from x) i)
  map_add' x y := by
    funext i
    have h : r (show L from x + y) i = r (show L from x) i + r (show L from y) i :=
      congrFun (map_add r (show L from x) (show L from y)) i
    exact (congrArg s.symm h).trans (map_add s.symm _ _)
  map_smul' c x := by
    funext i
    have h : r (show L from c • x) i = s c * r (show L from x) i :=
      congrFun (map_smul r (s c) (show L from x)) i
    refine (congrArg s.symm h).trans ?_
    show s.symm (s c * r (show L from x) i) = c * s.symm (r (show L from x) i)
    rw [map_mul, s.symm_apply_apply]

theorem twOut_twIn {n : ℕ} (f : (Fin n → O) →ₗ[O] L) (r : L →ₗ[O] (Fin n → O)) (h : f ∘ₗ r = LinearMap.id)
    (x : TwMod s L) : twOut s L f (twIn s L r x) = x := by
  have hx : f (r (show L from x)) = (show L from x) := LinearMap.congr_fun h _
  show f (fun i => s (s.symm (r (show L from x) i))) = (show L from x)
  simpa using hx

theorem twOut_surjective {n : ℕ} (f : (Fin n → O) →ₗ[O] L) (hf : Function.Surjective f) :
    Function.Surjective (twOut s L f) := by
  intro x
  obtain ⟨v, hv⟩ := hf (show L from x)
  refine ⟨fun i => s.symm (v i), ?_⟩
  show f (fun i => s (s.symm (v i))) = (show L from x)
  simpa using hv

theorem finite_twMod [Module.Finite O L] : Module.Finite O (TwMod s L) := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' O L
  exact Module.Finite.of_surjective _ (twOut_surjective s L f hf)

theorem projective_twMod [Module.Finite O L] [Module.Projective O L] : Module.Projective O (TwMod s L) := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' O L
  obtain ⟨r, hr⟩ := Module.projective_lifting_property f LinearMap.id hf
  exact Module.Projective.of_split (twIn s L r) (twOut s L f)
    (LinearMap.ext (twOut_twIn s L f r hr))

theorem rank_twMod : Module.rank O (TwMod s L) = Module.rank O L :=
  (rank_eq_of_equiv_equiv (s : O → O) (AddEquiv.refl (TwMod s L) : TwMod s L ≃+ L) s.bijective
    (fun _ _ => rfl))

theorem finrank_twMod : Module.finrank O (TwMod s L) = Module.finrank O L := by
  rw [Module.finrank, Module.finrank, rank_twMod]

end GlobalTheory.CompanionTheory.Ar.TwModule

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem GlobalTheory.CompanionTheory.Ar.TwModule.twMod_finite_projective_finrank :
    ∀ (O : Type) [CommRing O] [IsDomain O] (s : O ≃+* O) (L : Type) [AddCommGroup L] [Module O L]
      [Module.Finite O L] [Module.Projective O L],
      Module.Finite O (TwMod s L) ∧ Module.Projective O (TwMod s L) ∧
        Module.finrank O (TwMod s L) = Module.finrank O L := by
  intro O _ _ s L _ _ _ _
  exact ⟨finite_twMod s L, projective_twMod s L, finrank_twMod s L⟩
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.UnramifiedPrimeIdempotent
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num NumberField

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem unramified_prime_idempotent : ∀ (E : Type) [Field E] [NumberField E] (p : ℕ), p.Prime → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (w : Ideal (𝓞 E)) [w.IsPrime], (p : 𝓞 E) ∈ w → ∃ ε : 𝓞 E, ε - 1 ∈ w ∧ (∀ w' : Ideal (𝓞 E), w'.IsPrime → (p : 𝓞 E) ∈ w' → w' ≠ w → ε ∈ w') ∧ (∀ a : 𝓞 E, (p : 𝓞 E) ∣ ε * a ↔ a ∈ w) ∧ (p : 𝓞 E) ∣ ε * ε - ε ∧ IsCoprime (Ideal.span {(p : 𝓞 E)}) (differentIdeal ℤ (𝓞 E)) :=
  PositivityTheory.HtPt.Gsplit.glue_split

end GlobalTheory.CompanionTheory.Ar.Num
end

