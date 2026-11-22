import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2945
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorPartTorusExtension
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2828
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2803
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0714
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0084
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2946
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2801
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionFramePowEqIntegralGenerator
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ProdSumReindex
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueAtOrigin
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0567
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOneBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2843
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2707
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2744
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2936
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2687
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0085
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1618
import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataPsiMemMaximalIdealTendstoZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2617
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvenCubicalTensorPosDefFormPositive
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0059
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0080
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0064
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2940
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2947
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2739
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2510
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0078
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2918
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2627
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2337
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0036
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0062
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValueStatementHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2844
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2880
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2835
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2822

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormTauLineBundleCoordinateEqExpStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_tauLineBundleCoordinate_eq_exp : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (a b : u.D.toPre.X) (x : (FractionRing u.V)ˣ), GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord u.D.toPre a b x → ‖algebraMap (FractionRing u.V) (PadicAlgCl p) (x : FractionRing u.V)‖ = Real.exp (-(l.q (a + b) - l.q a - l.q b)) := by
  first | exact @GlobalTheory.Poinc.TauNorm.main | exact GlobalTheory.Poinc.TauNorm.main | (intros; apply GlobalTheory.Poinc.TauNorm.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalSchemeExtensionThroughFiniteCoverStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normal_scheme_extension_through_finite_cover : ∀ (o : Type) [CommRing o] (N : ℕ) (S' X Z : Scheme.{0}) (U : S'.Opens) (c : U.toScheme ⟶ X) (i : X ⟶ Z) (p : Z ⟶ PSpace o N) (h : S' ⟶ PSpace o N), IsIntegral S' → Geo.Tor.IsNormalScheme S' → IsIntegral Z → Dense (U : Set S') → IsDominant c → IsFinite p → IsOpenImmersion i → Dense (Set.range i) → U.ι ≫ h = c ≫ i ≫ p → ∃ π : S' ⟶ Z, U.ι ≫ π = c ≫ i ∧ π ≫ p = h := by
  first | exact @GlobalTheory.NormalFiniteLift.exists_lift_of_finite | exact GlobalTheory.NormalFiniteLift.exists_lift_of_finite | (intros; apply GlobalTheory.NormalFiniteLift.exists_lift_of_finite <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedMulIsoUniformisationGenericFibreOneConStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalisedMulIso_uniformisation_genericFibre_one_constant : ∀ (V : Type) [CommRing V] [IsDomain V] (I : Ideal V) (D : DegData V I) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (w₀ : W0 U), w₀.IsGen → ∀ (N : ℕ) (α : LB.Gen (LB.LinComb A.L (K := Fin 2) ![𝟙 A.A.left, (mulA A.A N).left] ![(N : ℤ) ^ 2, -1])), α.IsGen → ∀ (β : LB.Gen (LB.LinComb U.LG.L (K := Fin 2) ![𝟙 G.left, (mulA G N).left] ![(N : ℤ) ^ 2, -1])), β.IsGen → ∃ c : FractionRing V, c ≠ 0 ∧ ∀ (r : (TF (R := V) (FractionRing V)).left ⟶ ((Over.pullback (jK V)).obj G).left), r ≫ ((Over.pullback (jK V)).obj G).hom = 𝟙 _ → ∀ (z : (TF (R := V) (FractionRing V)).left) (JA : ((TF (R := V) (FractionRing V)).left ⟶ A.A.left) → A.L.ι) (JG : ((TF (R := V) (FractionRing V)).left ⟶ G.left) → U.LG.L.ι), Good A.L z JA → Good U.LG.L z JG → (val β (r ≫ pullback.fst G.hom (jK V)) z JG).val = GlobalTheory.UT.cst (FractionRing V) z c * (GlobalTheory.TorsFrameInt.wv w₀ r z JG JA ^ ((N : ℤ) ^ 2) * (GlobalTheory.TorsFrameInt.wv w₀ (r ≫ (mulA ((Over.pullback (jK V)).obj G) N).left) z JG JA)⁻¹ * val α (r ≫ U.gen.hom.left) z JA).val := by
  first | exact @GlobalTheory.GenericMove.move_one_const | exact GlobalTheory.GenericMove.move_one_const | (intros; apply GlobalTheory.GenericMove.move_one_const <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedTwistedFactorValueAtLatticePointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalisedTwistedFactor_value_at_latticePoint : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ (n j : ℤ) (ν mu β₀ β₁ : D.toPre.X), β₁ = β₀ + shift h h' n j ν → ∀ (u₁ : LB.Gen (LB.LinComb D.toPre.P.L (dφ D.toPre a ν β₀ β₁) (dε n j))), IsFac D.toPre a h n j ν β₀ β₁ u₁ → ∀ (z : (TF (R := R) (FractionRing R)).left) (J : ((TF (R := R) (FractionRing R)).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), Good D.toPre.P.L z J → val u₁ ((DegPre.zF D.toPre (FractionRing R)).left ≫ (DegPre.trF D.toPre (FractionRing R) mu).left) z J = (val (D.toPre.psi (ν + mu)) (jFK (R := R) (FractionRing R)) z J ^ n * val (D.toPre.psi (h (ν + mu))) (jFK (R := R) (FractionRing R)) z J ^ j * val (D.toPre.tau (ν + mu) β₀) (jFK (R := R) (FractionRing R)) z J * val D.toPre.rigK (jFK (R := R) (FractionRing R)) z J ^ (n + j)) * (val (D.toPre.psi mu) (jFK (R := R) (FractionRing R)) z J ^ n * val (D.toPre.psi (h mu)) (jFK (R := R) (FractionRing R)) z J ^ j * val (D.toPre.tau mu β₁) (jFK (R := R) (FractionRing R)) z J * val D.toPre.rigK (jFK (R := R) (FractionRing R)) z J ^ (n + j))⁻¹ := by
  first | exact @GlobalTheory.TwFacVal.val_fac_at_point | exact GlobalTheory.TwFacVal.val_fac_at_point | (intros; apply GlobalTheory.TwFacVal.val_fac_at_point <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneOverLIdeleCharacterValue
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.LatModel

theorem exists_detGen_wedge_val_le : GlobalTheory.Published.AbelianDeRham → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (I : Type) [Fintype I] (d : ℕ)
      (φ : I → E →+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ → ∀ (𝔣 : Ideal (OF E)), IsBaseCond 𝔣 →
    ∀ (l : ℕ) [Fact l.Prime] (Q : Finset (HeightOneSpectrum (OF E))), IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) →
    ∀ y : (Af E)ˣ, OneOver l y → ∀ (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (𝔠 : FracId (FR E)) (R : Subring ℂ)
      [IsDiscreteValuationRing R], GlobalTheory.LatModel.IsPlaceRing E l lam R →
    ∀ (X₀ : Obj (FR E) 𝔠 (Sp R)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ (lattice (condQ 𝔣 Q) y) 0 X)
      (p : X.A.left ⟶ X₀.A.left) (cm : OAct (orderC (condQ 𝔣 Q)) X₀.A), X.IsPullBy X₀ (spMap R.subtype) p →
      (∀ a : OF E, cm.act (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF (condQ 𝔣 Q) a) = X₀.rm.act a) →
      (∀ a : orderC (condQ 𝔣 Q), ∃ (α : X.A ⟶ X.A) (_ : IsMonHom α), α.left ≫ p = p ≫ (cm.act a).left ∧
        ∀ w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α) →
    ∀ (j : FractionRing R →+* ℂ), (∀ x : R, j (algebraMap R (FractionRing R) x) = x) →
    ∀ (φK : I → E →+* FractionRing R), (∀ i, j.comp (φK i) = φ i) →
    ∀ (e : I → (X₀.Lie →ₗ[R] R)) (a : I → ℂ), (∀ i, a i ≠ 0 ∧ GlobalTheory.LatModel.IsPeriodGen X₀ U p i (e i) (a i) ∧
        ∀ (e' : X₀.Lie →ₗ[R] R) (a' : ℂ), GlobalTheory.LatModel.IsPeriodGen X₀ U p i e' a' → ∃ t : R, e' = t • e i) →
    ∀ (D : R), D ≠ 0 → GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ClearsIdem (FractionRing R) (condQ 𝔣 Q) D →
    ∃ (δ₀ : X₀.DetGen) (u₀ : R),
      (Matrix.detRowAlternating.compLinearMap (LinearMap.pi fun k ↦ e (U.e k)) : X₀.DetOmega) = u₀ • δ₀.1 ∧
      GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (algebraMap R (FractionRing R) u₀) ≤
        Fintype.card I • GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (algebraMap R (FractionRing R) D) := by
  classical
  intro _hdR E _ _ _ _ I _ d φ hφ 𝔣 _h𝔣 l _ Q _hQ _hQl y _hy lam 𝔠 R _ _hR X₀ X U p cm hpull _hcm hα j hj φK hφK e a he D hD hcl
  have hinj : Function.Injective φ := by
    intro i i' h
    obtain ⟨k, -, hk⟩ := hφ.2.2.2.2.2.2.1 (φ i)
    exact (hk i (Or.inl rfl)).trans (hk i' (Or.inl h)).symm
  have hKinj : Function.Injective φK := fun i i' h ↦ hinj (by rw [← hφK i, ← hφK i', h])
  obtain ⟨hfree, hfin, hrk⟩ := GlobalTheory.T.lie_algebra_free_rank_degree R X₀
  obtain ⟨cd, hcd1, hcd2, hlam⟩ := GlobalTheory.T.lie_algebra_period_coordinates R X₀ X U p hpull
  choose t ht using fun i ↦ hcl (φK i)
  choose T hT using fun i ↦ GlobalTheory.T.cm_order_action_descends R X₀ X U p (condQ 𝔣 Q) cm hα cd hcd1 hcd2 (t i)
  have hfac : ∀ i k, Algebra.TensorProduct.productMap ((φ (U.e k)).comp (orderC (condQ 𝔣 Q)).subtype).toIntAlgHom
      (algebraMap R ℂ).toIntAlgHom (t i) = if U.e k = i then ((D : R) : ℂ) else 0 := by
    intro i k
    have h2 : ∀ x : orderC (condQ 𝔣 Q) ⊗[ℤ] R, Algebra.TensorProduct.productMap
        ((φ (U.e k)).comp (orderC (condQ 𝔣 Q)).subtype).toIntAlgHom (algebraMap R ℂ).toIntAlgHom x =
        j (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.coordAt R (condQ 𝔣 Q) (φK (U.e k)) x) := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a x =>
        show φ (U.e k) (a : E) * (x : ℂ) = j (φK (U.e k) (a : E) * algebraMap R (FractionRing R) x)
        rw [map_mul, hj, ← hφK (U.e k)]
        rfl
      | add x z hx hz => rw [map_add, map_add, hx, hz, map_add]
    rw [h2, ht i (φK (U.e k))]
    by_cases h : U.e k = i
    · subst h
      simp [hj]
    · rw [if_neg (fun h' ↦ h (hKinj h')), if_neg h]
      simp
  have hspan : ∀ ω : X₀.Lie →ₗ[R] R, D • ω ∈ Submodule.span R (Set.range fun k ↦ e (U.e k)) := by
    intro ω
    obtain ⟨lm, hlm⟩ := hlam ω
    have hval : ∀ i v, (((ω ∘ₗ T i) v : R) : ℂ) =
        ∑ k, lm k * ((if U.e k = i then ((D : R) : ℂ) else 0) * cd v k) := by
      intro i v
      rw [LinearMap.comp_apply, hlm]
      simp_rw [hT i v, hfac i]
    have hg : ∀ i, ∃ s : R, ω ∘ₗ T i = s • e i := by
      intro i
      refine (he i).2.2 _ ((D : ℂ) * lm (U.e.symm i)) ?_
      intro v v' W hv hW
      rw [hcd2 v v' W hv hW, hval i v, Finset.sum_eq_single (U.e.symm i)]
      · simp only [Equiv.apply_symm_apply, if_true]
        ring
      · intro k _ hk
        rw [if_neg (fun (h : U.e k = i) ↦ hk (by rw [← h, Equiv.symm_apply_apply]))]
        simp
      · intro h
        exact absurd (Finset.mem_univ _) h
    choose s hs using hg
    have heq : D • ω = ∑ i, s i • e i := by
      ext v
      rw [LinearMap.smul_apply, LinearMap.sum_apply, AddSubmonoidClass.coe_finsetSum]
      have key : ∀ i, (((s i • e i) v : R) : ℂ) =
          ∑ k, lm k * ((if U.e k = i then ((D : R) : ℂ) else 0) * cd v k) := by
        intro i
        rw [← hs i, hval]
      simp_rw [key]
      rw [Finset.sum_comm]
      simp only [ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [smul_eq_mul, Subring.coe_mul, hlm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      ring
    rw [heq]
    exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _
      (Submodule.subset_span ⟨U.e.symm i, by simp⟩)
  haveI := hfree
  haveI := hfin
  obtain ⟨δ₀, u₀, hδ, hu, hv⟩ := GlobalTheory.T.exists_generator_top_exterior_power R X₀.Lie _ hrk (fun k ↦ e (U.e k)) D hD hspan l
  refine ⟨⟨δ₀, hδ⟩, u₀, hu, ?_⟩
  have hc : Fintype.card I = Module.finrank ℚ (FR E) := by
    rw [← Fintype.card_congr U.e, Fintype.card_fin]
  rw [hc]
  exact hv

end GlobalTheory.LatModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartFirstChernFormOfWeightPowEqChernPart
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChernCalc.TopPow

open ReciprocityTheory.L2DbarEstimates (cHess)
open GlobalTheory.HermFrame (ddc kappa)
open GlobalTheory.GoodMetric (coordVec)

theorem ddc_coordVec (n : ℕ) (u : V n → ℝ) (v : V n) (hu : ContDiffAt ℝ 2 u v) (a b : Fin n) :
    ddc u v (coordVec a) (coordVec b) = kappa * cHess n (fun w => (u w : ℂ)) v a b := by
  rw [GlobalTheory.HermFrame.ddc, GlobalTheory.leviForm, GlobalTheory.ddbar_eq_del_dbar (contDiffAt_ofReal_comp hu)]
  congr 1
  have hg : (fun x => GlobalTheory.dbar (fun w => (u w : ℂ)) x (coordVec b)) =
      ReciprocityTheory.L2DbarEstimates.wdb n b (fun w => (u w : ℂ)) := by
    funext x
    simp only [GlobalTheory.dbar, GlobalTheory.antilinPart, ReciprocityTheory.L2DbarEstimates.wdb, ReciprocityTheory.L2DbarEstimates.bas,
      ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul]
    ring
  rw [hg]
  simp only [GlobalTheory.del, GlobalTheory.linPart, cHess, Matrix.of_apply, ReciprocityTheory.L2DbarEstimates.wd, ReciprocityTheory.L2DbarEstimates.bas,
    ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul]
  ring

theorem dens_ofValues_ddc_pow (n : ℕ) (u : V n → ℝ) (v : V n) (hu : ContDiffAt ℝ 2 u v) :
    (dens ((ofValues (ddc u v) ^ n : Ev n) : Alt n)).re =
      n.factorial / Real.pi ^ n * (cHess n (fun w => (u w : ℂ)) v).det.re := by
  have e : ofValues (ddc u v) = ∑ a, ∑ b, (kappa • cHess n (fun w => (u w : ℂ)) v) a b • sym (a, b) := by
    simp only [ofValues, ddc_coordVec n u v hu, Matrix.smul_apply, smul_eq_mul]
  rw [e, GlobalTheory.CxForm.DensPow.dens_pow, Matrix.det_smul, Fintype.card_fin]
  have hk : kappa = Complex.I / 2 * ((Real.pi : ℂ)⁻¹) := by
    rw [GlobalTheory.HermFrame.kappa]; field_simp
  have h2 : (Complex.I / 2) ^ n ≠ 0 := pow_ne_zero _ (by simp)
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [hk, show ∀ d : ℂ, (n.factorial : ℂ) * ((Complex.I / 2 * ((Real.pi : ℂ))⁻¹) ^ n * d) / (Complex.I / 2) ^ n =
      (((n.factorial / Real.pi ^ n : ℝ)) : ℂ) * d from fun d => by
    rw [mul_pow]; field_simp; push_cast; ring, Complex.re_ofReal_mul]

variable {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {L : LB X.X}

theorem dens_loc_c1W_pow (ψ : Weight X.str σ L) (hψ : ψ.IsCInf) (c : AlgChart X.str σ X.dim)
    (y : CxPts X.str σ) (hy : y ∈ c.e.source) :
    (dens ((atlas X σ).loc (fld (atlas X σ) (c1W ψ ^ X.dim)) c (c.e y))).re = c.chernDens ψ y := by
  have e := (atlas X σ).loc_crd (fld (atlas X σ) (c1W ψ ^ X.dim)) (⟨(c, y), hy⟩ : (atlas X σ).Pt)
  erw [e]
  have hs := hψ.contDiffAt c hy (mem_pick ψ.isLB y)
  erw [fld, Pi.pow_apply, c1W, dens_ofValues_ddc_pow X.dim _ _ hs]
  rfl

theorem part_c1W_pow : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (L : LB X.X) (ψ : Weight X.str σ L),
    ψ.IsCInf → ∀ ε : ℤˣ, (atlas X σ).part (fld (atlas X σ) (c1W ψ ^ X.dim)) ε = ψ.chernPart X.dim ε := by
  intro F _ σ X L ψ hψ ε
  unfold HolAtlas.part Weight.chernPart ChartGlue.glueMeas
  refine iSup_congr fun c => ?_
  unfold ChartGlue.chartMeas
  congr 1
  refine withDensity_congr_ae (ae_restrict_of_forall_mem c.e.open_target.measurableSet fun v hv => ?_)
  have hy := c.e.map_target hv
  simp only [Function.comp_apply]
  erw [dens_loc_c1W_pow ψ hψ c _ hy]

end GlobalTheory.ChernCalc.TopPow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodScalarCoordinatesSymmBimultUpToUnits
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum
open GlobalTheory.Mum.TensPos GlobalTheory.PsiScalUnit GlobalTheory.Mum.TensPol

noncomputable section

namespace GlobalTheory.Mum.TensPolRel

theorem tauCoord_rel : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (Q : GlobalTheory.PolDeg.Data R) (k : Q.X → Q.X → (FractionRing R)ˣ), (∀ a b, Q.TauCoord a b (k a b)) → (∀ a b, ∃ u ∈ unitsK R, k b a = u * k a b) ∧ ∀ a a' b, ∃ u ∈ unitsK R, k (a + a') b = u * (k a b * k a' b) := by
  intro R _ _ _ Q k hk
  obtain ⟨z⟩ : Nonempty (TK R).left := inferInstanceAs (Nonempty (PrimeSpectrum (FractionRing R)))
  haveI := Q.isAb.proper
  obtain ⟨J, hJ, iJ⟩ := GlobalTheory.Mum.TensPol.exists_int Q.B Q.M.L Q.M.isLB z
  let E : (FractionRing R)ˣ →* ((TK R).left.presheaf.stalk z)ˣ := Units.map (ev z).toMonoidHom
  have hE : Function.Injective E := Units.map_injective (ev_inj z)
  have hτ : ∀ a b, ∃ v ∈ unitsS z, val (Q.tau a b) (𝟙 _) z J = E (k a b) * v := fun a b => by
    obtain ⟨u, -, hu⟩ := hk a b
    refine ⟨_, GlobalTheory.Mum.TensPol.val_mem z iJ _ (fun i => ?_) _ u, (hu z J hJ).trans (congrArg (· * _) (gm_unitOn z _))⟩
    fin_cases i <;> exact Over.w _
  choose v hv ev' using hτ
  refine ⟨fun a b => ?_, fun a a' b => ?_⟩
  · refine ⟨k b a * (k a b)⁻¹, mem_unitsK z ?_, by rw [inv_mul_cancel_right]⟩
    have e := Q.tau_symm a b z J hJ
    rw [ev', ev'] at e
    have : E (k b a * (k a b)⁻¹) = v a b * (v b a)⁻¹ := by
      rw [map_mul, map_inv]
      apply Additive.ofMul.injective
      have e' := congrArg Additive.ofMul e
      simp only [ofMul_mul, ofMul_inv] at e' ⊢
      linear_combination (norm := abel) -e'
    exact this ▸ mul_mem (hv a b) (inv_mem (hv b a))
  · refine ⟨k (a + a') b * (k a b * k a' b)⁻¹, mem_unitsK z ?_, by rw [inv_mul_cancel_right]⟩
    have e := Q.tau_add a a' b z J hJ
    have hc : cubV Q.cub z J (toUnit (TK R) ≫ Q.c a) (toUnit (TK R) ≫ Q.c a') (toUnit (TK R) ≫ Q.c b) ∈ unitsS z := by
      rw [← val_cub Q.cub (toUnit (TK R)) hJ]
      refine GlobalTheory.Mum.TensPol.val_mem z iJ _ (fun i => ?_) _ _
      exact Over.w (lift (Q.c a) (lift (Q.c a') (Q.c b)) ≫ psum Q.B (x3 Q.B) i.down)
    rw [ev', ev', ev'] at e
    generalize cubV Q.cub z J (toUnit (TK R) ≫ Q.c a) (toUnit (TK R) ≫ Q.c a') (toUnit (TK R) ≫ Q.c b) = w at e hc
    have : E (k (a + a') b * (k a b * k a' b)⁻¹) = v a b * v a' b * (v (a + a') b)⁻¹ * w⁻¹ := by
      rw [map_mul, map_inv, map_mul]
      apply Additive.ofMul.injective
      have e' := congrArg Additive.ofMul e
      simp only [ofMul_mul, ofMul_inv] at e' ⊢
      linear_combination (norm := abel) e'
    exact this ▸ mul_mem (mul_mem (mul_mem (hv a b) (hv a' b)) (inv_mem (hv _ b))) (inv_mem hc)

end GlobalTheory.Mum.TensPolRel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodsOfGoodReductionModelStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periods_of_good_reduction_model : GlobalTheory.Published.AbelianDeRham → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ)
    (L : Set E) (𝔠 : FracId (FR E)) (R : Subring ℂ) [IsDiscreteValuationRing R]
    (X₀ : Obj (FR E) 𝔠 (Sp R)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ L 0 X)
    (p : X.A.left ⟶ X₀.A.left), X.IsPullBy X₀ (spMap R.subtype) p →
    ∀ (e : I → (X₀.Lie →ₗ[R] R)) (a : I → ℂ), (∀ i, GlobalTheory.LatModel.IsPeriodGen X₀ U p i (e i) (a i)) →
    ∀ (δ₀ : X₀.DetGen) (u₀ : R), u₀ ≠ 0 →
      (Matrix.detRowAlternating.compLinearMap (LinearMap.pi fun k ↦ e (U.e k)) : X₀.DetOmega) = u₀ • δ₀.1 →
    ∃ δ : X.DetGen, Obj.DetCorr R.subtype p δ₀.1 δ.1 ∧ U.IsDet δ.1 ((∏ i, a i) / (u₀ : ℂ)) := by
  first | exact @GlobalTheory.PeriodDet.exists_detGen_isDet | exact GlobalTheory.PeriodDet.exists_detGen_isDet | (intros; apply GlobalTheory.PeriodDet.exists_detGen_isDet <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodsSumDegenerationDataFstCubeIsoStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periods_sumDegenerationData_fst_cube_iso : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D₁ D₂ : DegData R I) (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (q₁ : D.toPre.X →+ D₁.toPre.X) (q₂ : D.toPre.X →+ D₂.toPre.X), IsSumDeg D.toPre D₁.toPre D₂.toPre p₁ p₂ q₁ q₂ → ∀ (i₁ : D₁.toPre.P.A ⟶ D.toPre.P.A) (j₁ : D₁.toPre.X →+ D.toPre.X), i₁ ≫ p₁ = 𝟙 _ → i₁ ≫ p₂ = toUnit _ ≫ η[D₂.toPre.P.A] → (∀ y, q₁ (j₁ y) = y) → (∀ y, q₂ (j₁ y) = 0) → ∀ (wM : LB.Iso D.toPre.P.L (extLB D₁.toPre.P.L D₂.toPre.P.L p₁.left p₂.left)), wM.IsGen → (∃ b₁ b₂, MapsAt₂ wM (eSec D.toPre.P.A) 1 D.toPre.rig b₁ b₂ ∧ LB.Gen.Corr D₁.toPre.P.L _ _ _ _ b₁ D₁.toPre.rig ∧ LB.Gen.Corr D₂.toPre.P.L _ _ _ _ b₂ D₂.toPre.rig) → (∀ x, ∃ b₁ b₂, MapsAt₂ wM (D.toPre.xK x) (-1) (D.toPre.psi x) b₁ b₂ ∧ LB.Gen.Corr D₁.toPre.P.L _ _ _ _ b₁ (D₁.toPre.psi (q₁ x)) ∧ LB.Gen.Corr D₂.toPre.P.L _ _ _ _ b₂ (D₂.toPre.psi (q₂ x))) → ∀ (w : LB.Iso (cubeLB D.toPre.P.A ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A] D.toPre.P.L) (cubeLB D₁.toPre.P.A ![fst D₁.toPre.P.A D.toPre.P.A, snd D₁.toPre.P.A D.toPre.P.A ≫ p₁] D₁.toPre.P.L)), (∀ (Z : Scheme.{0}) (f : Z ⟶ (D₁.toPre.P.A ⊗ D.toPre.P.A).left) (z : Z) (jC : ULift.{0} (Finset (Fin 2)) → D₁.toPre.P.L.ι) (jA : ULift.{0} (Finset (Fin 2)) → D.toPre.P.L.ι) (β : ULift.{0} (Finset (Fin 2)) → D₂.toPre.P.L.ι), f z ∈ (cubeLB D₁.toPre.P.A ![fst D₁.toPre.P.A D.toPre.P.A, snd D₁.toPre.P.A D.toPre.P.A ≫ p₁] D₁.toPre.P.L).U jC → f z ∈ (cubeLB D.toPre.P.A ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A] D.toPre.P.L).U jA → (∀ I, (f ≫ (psum D.toPre.P.A ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A] I.down).left ≫ p₂.left) z ∈ D₂.toPre.P.L.U (β I)) → (∀ I, β I = β ⟨insert 0 I.down⟩) → gm f z _ (w.s (jC, jA)) = ∏ I, gm (f ≫ (psum D.toPre.P.A ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A] I.down).left) z _ (wM.s (extIdx (f₁ := p₁.left) (f₂ := p₂.left) (jC I) (β I), jA I)) ^ ((-1 : ℤ) ^ (2 - I.down.card))) → ∀ (y : D₁.toPre.X) (y' : D.toPre.X) (z : (TK R).left) (J₁ : ((TK R).left ⟶ D₁.toPre.P.A.left) → D₁.toPre.P.L.ι) (J₂ : ((TK R).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), Good D₁.toPre.P.L z J₁ → Good D.toPre.P.L z J₂ → val ((pol D).tau (j₁ y) y') (𝟙 _) z J₂ = adjVal w (lift (toUnit (TK R) ≫ D₁.toPre.c y) (toUnit (TK R) ≫ D.toPre.c y')).left z J₁ J₂ * val ((pol D₁).tau y (q₁ y')) (𝟙 _) z J₁ := by
  first | exact @GlobalTheory.MumProd.tau_sum_fst | exact GlobalTheory.MumProd.tau_sum_fst | (intros; apply GlobalTheory.MumProd.tau_sum_fst <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareClassAdditiveInDualVariable
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

theorem GlobalTheory.AbDual.poincare_evc_mul_right : ∀ (K : Type) [Field K] (A A' : AbVar K) (P : LB (A.X ⊗ A'.X).left)
    (hP : AbDual.IsDual A.X A'.X P) (Y : Over (Sp K)) (a : Y ⟶ A.X) (b b' : Y ⟶ A'.X),
    AbDual.evc hP.isLB a (b * b') = AbDual.evc hP.isLB a b + AbDual.evc hP.isLB a b' := by
  intro K _ A A' P hP Y a b b'
  have hs : (AbDual.swap P).IsLB := pull_isLB hP.isLB _
  have h := (AbDual.isAdditive_iff hs).1 (AbDual.isDual_isAdditive_swap _ A.X A'.X P A'.ab hP) Y b b' a
  rwa [AbDual.evc_swap hP.isLB hs, AbDual.evc_swap hP.isLB hs, AbDual.evc_swap hP.isLB hs] at h
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareCrystalPairingSwapEqNegFlip
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem pairing_swap_eq_neg_flip : ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left), P.IsLB → ∀ φ : HdR A →ₗ[R] HdR B →ₗ[R] R, AbDual.IsCorrForm (dp0 R) (𝟙 _) A B P φ → AbDual.IsCorrForm (dp0 R) (𝟙 _) B A (AbDual.swap P) (-φ.flip) := by
  intro R _ A B _ _ P _ φ H
  exact SymmPoincare.isCorrForm_swap H

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointCountOfEigenCovolumeHypotheses
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open scoped NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.FlatModel GlobalTheory.Toroidal
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.VertForm
open GlobalTheory.DetHT
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.ShFam.Descent

namespace GlobalTheory.DetHT

theorem pointSt_of : BridgeSt → EigSt → CovolSt → PointSt := by
  intro hB hE hC E _ _ _ _ H Dw τ p _
  obtain ⟨δ, hδ, hEδ⟩ := hE E H p
  refine ⟨-(Dw.mult τ.1 : ℝ) * Real.log ‖δ‖, ?_⟩
  intro l Xo c Z _ f hf P y z yb hyP Q π ψ hPt hHT hfy
  letI := H.starRing
  obtain ⟨g, a, x, hchg, -, -, htie, hlat⟩ := hHT
  have hPy : P.x = y.x := by rw [← Descent.ptF_fst P, ← hyP, Descent.ptF_fst]
  have hzy : z.x = y.x := hchg.1.symm
  have hzP : ptF z = ptF P := by
    refine pullback.hom_ext ?_ ?_
    · rw [Descent.ptF_fst, Descent.ptF_fst, hzy, hPy]
    · rw [Descent.ptF_snd, Descent.ptF_snd]
  have LT := fun σ j => GlobalTheory.T.p_adic_frobenius_point_comparison E H Dw l Xo c Z p P z yb hzP Q π ψ hPt σ j (x σ j) (htie σ j)
  have LE := fun σ j => GlobalTheory.T.p_adic_point_period_relation E H Dw l Xo c Z p z yb (ptF P) Q π ψ hPt σ j (x σ j) (htie σ j)
  have uY := fun σ => GlobalTheory.T.combinatorial_tangent_point_condition E H Dw l Xo c (𝓞 c.F) (algebraMap (𝓞 c.F) c.F) Z ℂ_[p] y σ
  set vY := (frameOf Z y).v with hvY
  set vZ := (frameOf Z z).v with hvZ
  have tY : ∀ σ k, IsTanAtG Z.t (ptF y ≫ Z.j) (vY σ k) := (frameOf Z y).tan
  have rY : ∀ σ k, TanRel Z (ptF y) (y.u σ k) (vY σ k) := (tie_frameOf Z y).2.2
  have tZ : ∀ σ k, IsTanAtG Z.t (ptF z ≫ Z.j) (vZ σ k) := (frameOf Z z).tan
  have rZ : ∀ σ k, TanRel Z (ptF z) (z.u σ k) (vZ σ k) := (tie_frameOf Z z).2.2
  clear_value vY vZ
  rw [hyP] at tY rY uY
  rw [hzP] at tZ rZ
  have Cz : ∀ σ i, IsCombAtG Z.t (ptF P ≫ Z.j) (vZ σ) (g σ i) (vY σ i) := fun σ i =>
    (TanRel.comb_iff ((Descent.ptF_fst P).trans (hPy.trans hzy.symm)) rfl (rZ σ) (rY σ i) _).1 (hchg.2.1 σ i)
  obtain ⟨G, b, hGu, hG⟩ := (GlobalTheory.Frames.frChg_exists_unique E H Dw l Xo c ℂ_[p] y P).1 hPy
  have Cy : ∀ σ i, IsCombAtG Z.t (ptF P ≫ Z.j) (vY σ) (G σ i) ((frameOf Z P).v σ i) := fun σ i =>
    (TanRel.comb_iff ((Descent.ptF_fst P).trans hPy) rfl (rY σ) ((tie_frameOf Z P).2.2 σ i) _).1 (hG.2.1 σ i)
  have hev := GlobalTheory.FlatGL.evR_flat_chg τ hf P y hPy (G τ.1) (G (conjEmb τ.1)) (hG.2.1 τ.1) (hG.2.1 _)
  have hL := fun σ => GlobalTheory.T.p_adic_point_tangent_map_formula hB E H Dw l Xo c Z p (ptF P) yb Q π ψ hPt (Dw.mult σ) (x σ) (vZ σ) (vY σ) (g σ)
    (tZ σ) (LT σ) (Cz σ)
  have h1 := hC E H Z.X Z.t ℂ_[p] (ptF P ≫ Z.j) (GlobalTheory.ShFam.Pad.latHT Z.t p (ptF P ≫ Z.j)) (Dw.mult τ.1)
    ((frameOf Z P).v τ.1) (vY τ.1) (G τ.1) δ⁻¹ (inv_ne_zero hδ) (tY τ.1) (uY τ.1)
    (fun a w hw => (hL τ.1 a w hw).trans (GlobalTheory.T.lattice_eigenvector_height_matrix E H p δ hδ l c Q τ (hEδ l c Q τ) _ (x τ.1) (g τ.1)
      (LE τ.1) (hlat τ.1) a)) (Cy τ.1) (hGu τ.1).ne_zero
  have h2 := hC E H Z.X Z.t ℂ_[p] (ptF P ≫ Z.j) (GlobalTheory.ShFam.Pad.latHT Z.t p (ptF P ≫ Z.j)) (Dw.mult (conjEmb τ.1))
    ((frameOf Z P).v (conjEmb τ.1)) (vY (conjEmb τ.1)) (G (conjEmb τ.1)) 1 one_ne_zero (tY _) (uY _)
    (fun a w hw => (hL _ a w hw).trans (GlobalTheory.T.height_lattice_basis_of_eigenvectors E H p l c Q τ _ (x (conjEmb τ.1)) (g (conjEmb τ.1))
      (LE _) (hlat _) a)) (Cy _) (hGu _).ne_zero
  have d1 := (hGu τ.1).ne_zero
  have d2 := (hGu (conjEmb τ.1)).ne_zero
  have hP0 : evR Xo c f P ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hev
    exact mul_ne_zero d2 hfy hev.symm
  refine ⟨hP0, ?_⟩
  have e := congrArg (fun t => Real.log ‖t‖) hev
  simp only [norm_mul] at e
  rw [Real.log_mul (norm_ne_zero_iff.2 hP0) (norm_ne_zero_iff.2 d1),
    Real.log_mul (norm_ne_zero_iff.2 d2) (norm_ne_zero_iff.2 hfy)] at e
  unfold lnDet
  rw [h1, h2, norm_inv, Real.log_inv, norm_one, Real.log_one]
  linarith

end GlobalTheory.DetHT
end
end

