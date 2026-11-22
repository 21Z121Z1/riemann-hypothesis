import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0046
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2688
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2736
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2657
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2700
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2306
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2654
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2650
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusTorsionPointsCorrespondValues
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FamiliesValuesCorrespond
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0133
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCountableModel
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0033
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0140
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0138
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0595
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0137
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2758
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0208
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGen
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyUWit
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2472
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2701
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0781
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2627
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0010
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsStableBasOfPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2696
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2694
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2514
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2410
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2581
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2290

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonDenomFramePolynomialsCmPointGenerato
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.GeometryOfNumbersTheory TopologicalSpace Limits
open GlobalTheory.HSApp
open GlobalTheory.LamT (CMPt)
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.LatFull.CMIntZ

theorem exists_coeff_denom_intWt_any : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (f : ℕ) (La : ℝ), z.Good f La →
    ∀ (e : Formalism.L2.Pj.Ix Dw → ℤ) (k : (E →+* ℂ) → ℕ),
    ∃ t : 𝓞 z.K, t ≠ 0 ∧ ∀ F ∈ GlobalTheory.AllWt.secZ Xo c e, (∀ v, ∀ w ∈ valSet Xo c (algCls Xo c) v, 0 ≤ w F) →
      ∀ G : MvPolynomial (Formalism.L2.LamCM.FrVar Dw.mult) z.K,
        (∀ (y' : FrPt Xo c z.K) (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) z.K),
          (∀ b, (Y b).det ≠ 0) → GlobalTheory.Frames.FrChg (fun b => (Y b).transpose) 1 z.y y' →
          (∏ b, (Y b).det ^ k b) * evR Xo c F y' = Formalism.L2.LamCM.evalFr G Y) →
        ∀ μ, IsIntegral ℤ ((t : z.K) * MvPolynomial.coeff μ G) := by
  intro E _ _ _ H Dw l Xo c _ z f La hz e k
  classical
  obtain ⟨S, hS⟩ := GlobalTheory.CoeffIntZ.coeff_valuation_le_one_almost_all_any E H Dw l Xo c z f La hz e k
  choose x hx0 hx using GlobalTheory.CoeffDenomZ.exists_clear_coeff_at_prime_any E H Dw l Xo c z f La hz e k
  refine ⟨∏ p ∈ S, x p, Finset.prod_ne_zero_iff.2 fun p _ => hx0 p, fun F hF hv G hG μ => ?_⟩
  have hint : ∀ r : 𝓞 z.K, ∀ p : IsDedekindDomain.HeightOneSpectrum (𝓞 z.K), p.valuation z.K (r : z.K) ≤ 1 :=
    fun r p => p.valuation_le_one r
  have hv1 : ∀ p : IsDedekindDomain.HeightOneSpectrum (𝓞 z.K),
      p.valuation z.K (((∏ q ∈ S, x q : 𝓞 z.K) : z.K) * MvPolynomial.coeff μ G) ≤ 1 := by
    intro p
    by_cases hp : p ∈ S
    · rw [← Finset.mul_prod_erase S x hp]
      have e1 : (((x p * ∏ q ∈ S.erase p, x q : 𝓞 z.K)) : z.K) * MvPolynomial.coeff μ G =
          ((∏ q ∈ S.erase p, x q : 𝓞 z.K) : z.K) * (((x p : 𝓞 z.K) : z.K) * MvPolynomial.coeff μ G) := by
        push_cast; ring
      rw [e1, map_mul]
      exact mul_le_one' (hint _ p) (hx p F hF hv G hG μ)
    · rw [map_mul]
      exact mul_le_one' (hint _ p) (hS p hp F hF hv G hG μ)
  obtain ⟨r, hr⟩ := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one z.K _ hv1
  rw [← hr]
  exact RingOfIntegers.isIntegral_coe r

end GlobalTheory.LatFull.CMIntZ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonExtensionDvrFractionFields
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.FieldTraitExt

theorem exists_normalization (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hR : Base R)
    (K' : Type) [Field K'] (io : FractionRing R →+* K') (hio : io.Finite) :
    ∃ (R₂ : Type) (_ : CommRing R₂) (_ : IsDomain R₂) (_ : IsLocalRing R₂) (ρ : R →+* R₂) (i : K' ≃+* FractionRing R₂)
      (e : R₂ →+* K'), FinExt ρ ∧ Function.Injective e ∧ (∀ r, e (ρ r) = io (algebraMap R _ r)) ∧
      ∀ y, i (e y) = algebraMap R₂ _ y := by
  obtain ⟨⟨hnoeth, -, hic, hcomp⟩, hchar⟩ := hR
  letI : Algebra (FractionRing R) K' := io.toAlgebra
  letI : Algebra R K' := (io.comp (algebraMap R (FractionRing R))).toAlgebra
  haveI : IsScalarTower R (FractionRing R) K' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : FiniteDimensional (FractionRing R) K' := hio
  haveI : CharZero (FractionRing R) := IsFractionRing.charZero_of_isFractionRing R
  let R₂ := integralClosure R K'
  haveI hfin : Module.Finite R R₂ := IsIntegralClosure.finite R (FractionRing R) K' R₂
  haveI : IsLocalRing R₂ := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isLocalRing_finite_domain (R := R) R₂
  haveI : IsFractionRing R₂ K' := IsIntegralClosure.isFractionRing_of_finite_extension R (FractionRing R) K' R₂
  have hRK : Function.Injective (algebraMap R K') := io.injective.comp (IsFractionRing.injective R _)
  have hinj : Function.Injective (algebraMap R R₂) := fun x y h => hRK (congrArg Subtype.val h)
  haveI : IsNoetherianRing R₂ := IsNoetherianRing.of_finite R R₂
  refine ⟨R₂, inferInstance, inferInstance, inferInstance, algebraMap R R₂,
    (IsLocalization.algEquiv (nonZeroDivisors R₂) K' (FractionRing R₂)).toRingEquiv, algebraMap R₂ K',
    ⟨⟨inferInstance, inferInstance, integralClosure.isIntegrallyClosedOfFiniteExtension (FractionRing R),
      GlobalTheory.CompleteFiniteExtension.isAdicComplete_of_finite_local R R₂⟩, hinj, RingHom.finite_algebraMap.2 hfin⟩,
    Subtype.val_injective, fun r => rfl, fun y => ?_⟩
  exact (IsLocalization.algEquiv (nonZeroDivisors R₂) K' (FractionRing R₂)).commutes y

theorem exists_trait (R R₂ W : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R₂] [IsDomain R₂]
    [IsLocalRing R₂] [CommRing W] [IsDomain W] [IsLocalRing W] (hW : GlobalTheory.LN.CDvr W) (φ : R →+* W)
    (hφ : IsLocalHom φ) (ρ : R →+* R₂) (hρ : ρ.Finite) (Ω : Type) [Field Ω] (j : FractionRing W →+* Ω)
    (m : R₂ →+* Ω) (hm : Function.Injective m) (hc : ∀ r, m (ρ r) = j (algebraMap W _ (φ r))) :
    ∃ (W₂ : Type) (_ : CommRing W₂) (_ : IsDomain W₂) (_ : IsLocalRing W₂) (σ : W →+* W₂) (φ₂ : R₂ →+* W₂)
      (j₂ : FractionRing W₂ →+* Ω), GlobalTheory.LN.CDvr W₂ ∧ FinExt σ ∧ IsLocalHom σ ∧ Function.Injective φ₂ ∧
      IsLocalHom φ₂ ∧ φ₂.comp ρ = σ.comp φ ∧ (∀ w, j₂ (algebraMap W₂ _ (σ w)) = j (algebraMap W _ w)) ∧
      ∀ r, j₂ (algebraMap W₂ _ (φ₂ r)) = m r := by
  first
  | exact @_root_.GlobalTheory.FiniteCompletionLocalHom.exists_extension
  | exact _root_.GlobalTheory.FiniteCompletionLocalHom.exists_extension
  | (apply _root_.GlobalTheory.FiniteCompletionLocalHom.exists_extension <;> assumption)
  | (intros; apply _root_.GlobalTheory.FiniteCompletionLocalHom.exists_extension <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FiniteCompletionLocalHom.exists_extension <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FiniteCompletionLocalHom.exists_extension ..)

end GlobalTheory.FieldTraitExt

namespace GlobalTheory.FieldTraitExt

theorem exists_finite_extension_of_trait : ∀ (R W : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing W] [IsDomain W] [IsLocalRing W], Base R → GlobalTheory.LN.CDvr W → ∀ φ : R →+* W, Function.Injective φ → IsLocalHom φ → ∀ (K' Ω : Type) [Field K'] [Field Ω] (io : FractionRing R →+* K') (j : FractionRing W →+* Ω) (l : K' →+* Ω), io.Finite → (∀ r, l (io (algebraMap R _ r)) = j (algebraMap W _ (φ r))) → ∃ (R₂ : Type) (_ : CommRing R₂) (_ : IsDomain R₂) (_ : IsLocalRing R₂) (ρ : R →+* R₂) (i : K' ≃+* FractionRing R₂) (W₂ : Type) (_ : CommRing W₂) (_ : IsDomain W₂) (_ : IsLocalRing W₂) (σ : W →+* W₂) (φ₂ : R₂ →+* W₂) (j₂ : FractionRing W₂ →+* Ω), FinExt ρ ∧ GlobalTheory.LN.CDvr W₂ ∧ FinExt σ ∧ IsLocalHom σ ∧ Function.Injective φ₂ ∧ IsLocalHom φ₂ ∧ φ₂.comp ρ = σ.comp φ ∧ (∀ r, i (io (algebraMap R _ r)) = algebraMap R₂ _ (ρ r)) ∧ (∀ w, j₂ (algebraMap W₂ _ (σ w)) = j (algebraMap W _ w)) ∧ ∀ r, j₂ (algebraMap W₂ _ (φ₂ r)) = l (i.symm (algebraMap R₂ _ r)) := by
  intro R W _ _ _ _ _ _ hR hW φ _ hφ K' Ω _ _ io j l hio hc
  obtain ⟨R₂, _, _, _, ρ, i, e, hfe, he, heρ, hie⟩ := exists_normalization R hR K' io hio
  obtain ⟨W₂, _, _, _, σ, φ₂, j₂, hW₂, hσ, hσl, hφ₂i, hφ₂l, hcomm, hj₁, hj₂⟩ :=
    exists_trait R R₂ W hW φ hφ ρ hfe.2.2 Ω j (l.comp e) (l.injective.comp he)
      (fun r => by rw [RingHom.comp_apply, heρ, hc])
  refine ⟨R₂, _, _, _, ρ, i, W₂, _, _, _, σ, φ₂, j₂, hfe, hW₂, hσ, hσl, hφ₂i, hφ₂l, hcomm, fun r => ?_, hj₁,
    fun r => ?_⟩
  · rw [← heρ, hie]
  · rw [hj₂, RingHom.comp_apply]
    congr 1
    rw [RingEquiv.eq_symm_apply, hie]

end GlobalTheory.FieldTraitExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompatiblePrimitiveRootsThroughStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compatible_primitiveRoots_through : ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (A : ℕ) (ω : K), 0 < A → IsPrimitiveRoot ω A → ∃ ζ : ℕ → Kˣ, (∀ n, 0 < n → IsPrimitiveRoot (ζ n) n) ∧ (∀ n m, 0 < n → 0 < m → ζ (n * m) ^ m = ζ n) ∧ (ζ A : K) = ω := by
  first | exact @GlobalTheory.RootSystem.exists_compatible_roots_through | exact GlobalTheory.RootSystem.exists_compatible_roots_through | (intros; apply GlobalTheory.RootSystem.exists_compatible_roots_through <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompatibleSymplecticBasesLevelPoints
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.SympQ.compatible_symplectic_bases : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (ζ : ℕ → Fˣ), (∀ n, 0 < n → IsPrimitiveRoot (ζ n) n) → (∀ n m, 0 < n → 0 < m → ζ (n * m) ^ m = ζ n) → ∀ g : ℕ, g = D.toPre.P.g + Module.finrank ℤ D.toPre.X → ∃ ev : ∀ n : ℕ, ((Fin g → ℤ) × (Fin g → ℤ)) → QkPt D.toPre F n, (∀ n, 0 < n → ∀ a b, QkAdd (ev n a) (ev n b) (ev n (a + b))) ∧ (∀ n, 0 < n → ∀ a b, QkPt.Equiv D.toPre F (ev n a) (ev n b) ↔ ∃ e, a = b + n • e) ∧ (∀ n, 0 < n → ∀ p, ∃ a, QkPt.Equiv D.toPre F (ev n a) p) ∧ (∀ n m, 0 < n → 0 < m → ∀ a, ∃ q : QkPt D.toPre F n, q.y = (ev (n * m) a).y ∧ GtPtF.IsNsmul m (ev (n * m) a).g q.g ∧ QkPt.Equiv D.toPre F q (ev n a)) ∧ ∀ n, 0 < n → ∀ a b, WeilQkIs D.toPre F n (ev n a) (ev n b) ((ζ n ^ (a.1 ⬝ᵥ b.2 - a.2 ⬝ᵥ b.1) : Fˣ) : F) := by
  intro R _ _ _ hR D F _ _ _ ζ hζ hζc g hg
  subst hg
  have hL : Laws := GlobalTheory.allSixLaws.1
  have gt : GlobalTheory.Ex.BrGtSt := GlobalTheory.Ex.GtValues.points_correspond
  have wp : GlobalTheory.Ex.BrWpSt := GlobalTheory.WeilValues.weil_eq_values gt (GlobalTheory.Ex.brFam hL GlobalTheory.allSixLaws.2.1)
  haveI : IsNoetherianRing R := hR.1.1
  obtain ⟨N, ν, -⟩ := GlobalTheory.T.exists_integral_degeneration_values hL R D.toPre D.psi_even D.tau_bimult F ⊤ (fun _ => trivial)
  obtain ⟨-, -, gAdd, -, gQ⟩ := gt R D.toPre D.psi_even D.tau_bimult F N ν
  have hW := wp R D.toPre D.psi_even D.tau_bimult F N ν
  have hcl : ∀ n (p p' : QkPt D.toPre F n) v v', ν.QPt p v → ν.QPt p' v' →
      (QkPt.Equiv D.toPre F p p' ↔ (QuotientGroup.mk v : GlobalTheory.SympQ.Qq N n) = QuotientGroup.mk v') :=
    fun n p p' v v' h h' => ((gQ n).2.2 p p' v v' h h').trans (GlobalTheory.SympQ.qEq_iff_mk_eq N v v')
  have h1 : ∀ n (x y z : Additive (GlobalTheory.SympQ.Qq N n)), GlobalTheory.SympQ.wpQ N n (x + y).toMul z.toMul = GlobalTheory.SympQ.wpQ N n x.toMul z.toMul * GlobalTheory.SympQ.wpQ N n y.toMul z.toMul := by
    intro n x y z
    obtain ⟨p, hp⟩ := QuotientGroup.mk_surjective (Additive.toMul x)
    obtain ⟨p', hp'⟩ := QuotientGroup.mk_surjective (Additive.toMul y)
    obtain ⟨p'', hp''⟩ := QuotientGroup.mk_surjective (Additive.toMul z)
    simp only [toMul_add]
    rw [← hp, ← hp', ← hp'', ← QuotientGroup.mk_mul, GlobalTheory.SympQ.wpQ_mk, GlobalTheory.SympQ.wpQ_mk, GlobalTheory.SympQ.wpQ_mk,
      GlobalTheory.Ex.WpPairing.wp_mul_left]
  have h2 : ∀ n (x y z : Additive (GlobalTheory.SympQ.Qq N n)), GlobalTheory.SympQ.wpQ N n x.toMul (y + z).toMul = GlobalTheory.SympQ.wpQ N n x.toMul y.toMul * GlobalTheory.SympQ.wpQ N n x.toMul z.toMul := by
    intro n x y z
    obtain ⟨p, hp⟩ := QuotientGroup.mk_surjective (Additive.toMul x)
    obtain ⟨p', hp'⟩ := QuotientGroup.mk_surjective (Additive.toMul y)
    obtain ⟨p'', hp''⟩ := QuotientGroup.mk_surjective (Additive.toMul z)
    simp only [toMul_add]
    rw [← hp, ← hp', ← hp'', ← QuotientGroup.mk_mul, GlobalTheory.SympQ.wpQ_mk, GlobalTheory.SympQ.wpQ_mk, GlobalTheory.SympQ.wpQ_mk,
      GlobalTheory.Ex.WpPairing.wp_mul_right]
  have h3 : ∀ n (x : Additive (GlobalTheory.SympQ.Qq N n)), GlobalTheory.SympQ.wpQ N n x.toMul x.toMul = 1 := by
    intro n x
    obtain ⟨p, hp⟩ := QuotientGroup.mk_surjective (Additive.toMul x)
    rw [← hp, GlobalTheory.SympQ.wpQ_mk, GlobalTheory.Ex.NumD.wp_self]
  have h4 : ∀ n, 0 < n → ∀ x : Additive (GlobalTheory.SympQ.Qq N n), (∀ y : Additive (GlobalTheory.SympQ.Qq N n), GlobalTheory.SympQ.wpQ N n x.toMul y.toMul = 1) → x = 0 := by
    intro n hn x hx
    exact Additive.toMul.injective (GlobalTheory.T.reprModTrivialQuotient_pairing_nondegenerate R hR D F N ν n hn x.toMul fun y => hx (Additive.ofMul y))
  have h5 : ∀ n m, 0 < n → 0 < m → ∀ x y : Additive (GlobalTheory.SympQ.Qq N (n * m)), GlobalTheory.SympQ.wpQ N n ((GlobalTheory.SympQ.pushQ N (n * m) n).toAdditive x).toMul ((GlobalTheory.SympQ.pushQ N (n * m) n).toAdditive y).toMul = GlobalTheory.SympQ.wpQ N (n * m) x.toMul y.toMul ^ m := by
    intro n m hn hm x y
    obtain ⟨p, hp⟩ := QuotientGroup.mk_surjective (Additive.toMul x)
    obtain ⟨p', hp'⟩ := QuotientGroup.mk_surjective (Additive.toMul y)
    change GlobalTheory.SympQ.wpQ N n (GlobalTheory.SympQ.pushQ N (n * m) n x.toMul) (GlobalTheory.SympQ.pushQ N (n * m) n y.toMul) =
      GlobalTheory.SympQ.wpQ N (n * m) x.toMul y.toMul ^ m
    rw [← hp, ← hp', GlobalTheory.SympQ.pushQ_mk, GlobalTheory.SympQ.pushQ_mk, GlobalTheory.SympQ.wpQ_mk, GlobalTheory.SympQ.wpQ_mk]
    exact GlobalTheory.T.reprModTrivialQuotient_pairing_levelPush_eq_pow R hR D F N ν n m hn hm p p'
  have h6 : ∀ M n k, 0 < k → 0 < M → k ∣ n → n ∣ M → ∀ x : Additive (GlobalTheory.SympQ.Qq N M), (GlobalTheory.SympQ.pushQ N n k).toAdditive ((GlobalTheory.SympQ.pushQ N M n).toAdditive x) = (GlobalTheory.SympQ.pushQ N M k).toAdditive x := by
    intro M n k hk hM hkn hnM x
    obtain ⟨p, hp⟩ := QuotientGroup.mk_surjective (Additive.toMul x)
    apply Additive.toMul.injective
    change GlobalTheory.SympQ.pushQ N n k (GlobalTheory.SympQ.pushQ N M n x.toMul) = GlobalTheory.SympQ.pushQ N M k x.toMul
    rw [← hp, GlobalTheory.SympQ.pushQ_mk, GlobalTheory.SympQ.pushQ_mk, GlobalTheory.SympQ.pushQ_mk]
    congr 1
    refine Subtype.ext (Prod.ext ?_ ?_)
    · rw [GlobalTheory.SympQ.pushRep_fst N hkn, GlobalTheory.SympQ.pushRep_fst N hnM, GlobalTheory.SympQ.pushRep_fst N (hkn.trans hnM)]
    · have e : M / n * (n / k) = M / k := by
        obtain ⟨b, rfl⟩ := hkn
        obtain ⟨a, rfl⟩ := hnM
        have hb : 0 < b := Nat.pos_of_ne_zero (by rintro rfl; simp at hM)
        rw [Nat.mul_div_cancel_left _ (Nat.mul_pos hk hb), Nat.mul_div_cancel_left _ hk, Nat.mul_assoc,
          Nat.mul_div_cancel_left _ hk, Nat.mul_comm]
      rw [GlobalTheory.SympQ.pushRep_snd N hkn, GlobalTheory.SympQ.pushRep_snd N hnM, GlobalTheory.SympQ.pushRep_snd N (hkn.trans hnM), ← pow_mul, e]
  obtain ⟨ev', hker, hsurj, htow, hweil⟩ := GlobalTheory.T.exists_compatible_symplectic_alt F ζ hζ hζc (D.toPre.P.g + Module.finrank ℤ D.toPre.X)
    (fun n => Additive (GlobalTheory.SympQ.Qq N n)) (fun n x y => GlobalTheory.SympQ.wpQ N n x.toMul y.toMul)
    (fun M n => (GlobalTheory.SympQ.pushQ N M n).toAdditive) (GlobalTheory.T.reprModTrivialQuotient_free_rank_twice_dimension R hR D F N ν) h1 h2 h3 h4 h5 h6
  have hrep : ∀ n a, ∃ q : N.QT n, (QuotientGroup.mk q : GlobalTheory.SympQ.Qq N n) = (ev' n a).toMul :=
    fun n a => QuotientGroup.mk_surjective _
  choose q hq using hrep
  choose P hP using fun n a => (gQ n).2.1 (q n a)
  refine ⟨P, fun n hn a b => ?_, fun n hn a b => ?_, fun n hn p => ?_, fun n m hn hm a => ?_, fun n hn a b => ?_⟩
  · obtain ⟨r, hr⟩ := (gQ n).2.1 (q n a * q n b)
    refine ⟨r, ?_, (gAdd _ _ _ _ _ _ (hP n a).2 (hP n b).2 hr.2).2 rfl, ?_⟩
    · rw [← hr.1, ← (hP n a).1, ← (hP n b).1, ← map_add]
      rfl
    · rw [hcl n _ _ _ _ hr (hP n (a + b)), QuotientGroup.mk_mul, hq, hq, hq, map_add, toMul_add]
  · rw [hcl n _ _ _ _ (hP n a) (hP n b), hq, hq, Additive.toMul.injective.eq_iff]
    exact hker n hn a b
  · obtain ⟨v, hv⟩ := ((gQ n).1 p).exists
    obtain ⟨a, ha⟩ := hsurj n hn (Additive.ofMul (QuotientGroup.mk v))
    exact ⟨a, (hcl n _ _ _ _ (hP n a) hv).2 (by rw [hq, ha]; rfl)⟩
  · have hd : n ∣ n * m := dvd_mul_right n m
    obtain ⟨r, hr⟩ := (gQ n).2.1 (GlobalTheory.SympQ.pushRep N (n * m) n (q (n * m) a))
    refine ⟨r, ?_, ?_, ?_⟩
    · rw [← hr.1, ← (hP (n * m) a).1, GlobalTheory.SympQ.pushRep_fst N hd]
    · refine (GlobalTheory.Ex.GtValues.isNsmul_val ν m (hP (n * m) a).2 hr.2).2 ?_
      rw [GlobalTheory.SympQ.pushRep_snd N hd, Nat.mul_div_cancel_left m hn]
    · rw [hcl n _ _ _ _ hr (hP n a), ← GlobalTheory.SympQ.pushQ_mk, hq, hq, ← htow n m hn hm a]
      rfl
  · refine (hW n hn (P n a) (P n b) (q n a) (q n b) _ (hP n a) (hP n b)).2 ?_
    rw [← GlobalTheory.SympQ.wpQ_mk, hq, hq]
    exact congrArg Units.val (hweil n hn a b).symm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDVRComparisonPreUniformisedStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_completeDVR_comparison_preUniformised : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : GlobalTheory.UU.PreU (maximalIdeal R) D A G), EvenOn U.P → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (φ : R →+* V) (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (G' : Over (Sp V)) (_ : GrpObj G') (_ : IsCommMonObj G') (U' : GlobalTheory.UU.PreU (maximalIdeal V) D'.toPre A' G') (U₀ : Unif (maximalIdeal V) D' A' G') (F : G'.left ⟶ G.left) (_ : GlobalTheory.LN.Cmp φ U U' F), GlobalTheory.LN.CDvr V ∧ Function.Injective φ ∧ (maximalIdeal V).comap φ = maximalIdeal R ∧ GlobalTheory.LN.Under U' U₀.toUnifPre := by
  first | exact @GlobalTheory.Mum.TraitCompare.exists_cmp_under | exact GlobalTheory.Mum.TraitCompare.exists_cmp_under | (intros; apply GlobalTheory.Mum.TraitCompare.exists_cmp_under <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDvrValuesUnitary
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.UPoinc

theorem exists_complete_dvr_values_unitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X₁ : USetup C) (D : UDeep X₁) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (ct : UCTrait X₁ p z₁) (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = ct.y) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra (FractionRing V) (PadicAlgCl p)], IsAdicComplete (IsLocalRing.maximalIdeal V) V → (∀ x : FractionRing V, ‖algebraMap (FractionRing V) (PadicAlgCl p) x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V))) →
  ∃ (V₂ : Type) (_ : CommRing V₂) (_ : IsDomain V₂) (_ : IsDiscreteValuationRing V₂) (_ : Algebra (FractionRing V₂) (PadicAlgCl p)), IsAdicComplete (IsLocalRing.maximalIdeal V₂) V₂ ∧ (∀ x : FractionRing V₂, ‖algebraMap (FractionRing V₂) (PadicAlgCl p) x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V₂ (FractionRing V₂))) ∧
    ∃ σ : FractionRing V →+* FractionRing V₂, (algebraMap (FractionRing V₂) (PadicAlgCl p)).comp σ = algebraMap (FractionRing V) (PadicAlgCl p) ∧
      ∀ a ∈ D.X.M.O ((gPt p ≫ y) (closedPoint (PadicAlgCl p))), D.X.M.val (gPt p ≫ y) a ∈ (algebraMap (FractionRing V₂) (PadicAlgCl p)).range := by
  intro E _ _ _ H Dw l Xo cf C X₁ D p _ z₁ c y h V _ _ _ _ hc hV
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

end GlobalTheory.UPoinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteNormalGaloisCoverOfFiniteStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.Poinc GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_completeNormal_galois_cover_of_finite : ∀ (A R : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [CommRing R] [IsDomain R] (b : A →+* R), IsCN A → b.Finite → Function.Injective b → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (θ : R →+* R'), IsCN R' ∧ IsLocalHom θ ∧ Function.Injective θ ∧ θ.Finite ∧ ∀ r : R, (∀ σ : R' ≃+* R', IsOfFinOrder σ → (∀ a, σ (θ (b a)) = θ (b a)) → σ (θ r) = θ r) → r ∈ b.range := by
  first | exact @GlobalTheory.GalCover.exists_isCN_galois_of_finite | exact GlobalTheory.GalCover.exists_isCN_galois_of_finite | (intros; apply GlobalTheory.GalCover.exists_isCN_galois_of_finite <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteTraitOverClosedPointModificationStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_completeTrait_over_closedPoint_modification : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (M : Modif R) (x₀ : M.S), M.π x₀ = closedPoint R → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (φ : R →+* W) (ξ : Sp W ⟶ M.S), GlobalTheory.LN.CDvr W ∧ Function.Injective φ ∧ IsLocalHom φ ∧ ξ ≫ M.π = spMap φ ∧ ξ (closedPoint W) = x₀ := by
  first | exact @GlobalTheory.Mum.exists_trait_over_closedPoint | exact GlobalTheory.Mum.exists_trait_over_closedPoint | (intros; apply GlobalTheory.Mum.exists_trait_over_closedPoint <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompletedLocalRingEndomorphismCharacterAct
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.UPoinc

theorem exists_endChar_pull : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE) (x : M.Z) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (j : M.Z.presheaf.stalk x →+* R), GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (gm : G.left ⟶ FinalForm.G.left), IsGrpPullback G FinalForm.G (spMap j ≫ M.Z.fromSpecStalk x) gm → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (f : FinalForm.G ⟶ FinalForm.G), IsMonHom f → ∃ (fR : G ⟶ G) (m : D.toPre.X →+ D.toPre.X), IsMonHom fR ∧ fR.left ≫ gm = gm ≫ f.left ∧ EndChar U fR m := by
  intro o' Ω _ _ _ _ S ρ M U₀ EE FinalForm x R _ _ _ j hR G _ _ gm hpb D A U f hf
  have hG : IsSemiAbelian G := GlobalTheory.Mum.isSemiAbelian_of_isGrpPullback_square _ _ _ FinalForm.G G gm hpb FinalForm.semi
  let fR : G ⟶ G :=
    Over.homMk (hpb.1.lift (gm ≫ f.left) G.hom (by rw [Category.assoc, Over.w f, hpb.1.w])) (hpb.1.lift_snd _ _ _)
  have e : fR.left ≫ gm = gm ≫ f.left := hpb.1.lift_fst _ _ _
  have hfR : IsMonHom fR := Out.PullGtPf.isMonHom_of_grpPullback hpb hpb f fR e
  obtain ⟨m, hm⟩ := GlobalTheory.Poinc.Eq8.endChar_exists_of_isMonHom R hR G hG D A U fR hfR
  exact ⟨fR, m, hfR, e, hm⟩

end GlobalTheory.UPoinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplexFibreExponentialFullLatticeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_complexFibreExponential_full_lattice : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (g : ℕ), IsAbelianScheme G → SmoothOfRelativeDimension g G.hom → ∀ y : Sp ℂ ⟶ X, ∃ (e : (Fin g → ℂ) → (Over.mk y ⟶ G)) (Λ : Submodule ℤ (Fin g → ℂ)), IsExp y e ∧ DiscreteTopology Λ ∧ Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ ∧ ∀ z, e z = 1 ↔ z ∈ Λ := by
  first | exact @GlobalTheory.FibreExp.exists_exp_lattice | exact GlobalTheory.FibreExp.exists_exp_lattice | (intros; apply GlobalTheory.FibreExp.exists_exp_lattice <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoordinatePolynomialSubMemMaximalIdealPowStatement
section
open IsLocalRing GlobalTheory.FormalOrigin GlobalTheory.FormalOrigin.Extend
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coordinate_polynomial_sub_mem_maximalIdeal_pow : ∀ (R A : Type) [CommRing R] [IsLocalRing R] [CommRing A] [IsLocalRing A] (inc : R →+* A) (ev : A →+* R), (∀ r, ev (inc r) = r) → ∀ (n : ℕ) (z : Fin n → A), maximalIdeal A = (maximalIdeal R).map inc ⊔ Ideal.span (Set.range z) → ∀ (k : ℕ) (f : A), ∃ p ∈ Subring.closure (Set.range inc ∪ Set.range z), f - p ∈ maximalIdeal A ^ k := by
  first | exact @GlobalTheory.exists_mem_closure_sub_mem_maximalIdeal_pow | exact GlobalTheory.exists_mem_closure_sub_mem_maximalIdeal_pow | (intros; apply GlobalTheory.exists_mem_closure_sub_mem_maximalIdeal_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoordinatesLogVectorFieldsDeterminantStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coordinates_logVectorFields_determinant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (U : TF.Y.X.affineOpens) (b : Module.Basis (Fin Dw.dim) Γ(TF.Y.X, U.1) (LogKS.logDer TF.Y.s (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U)) (x₀ : TF.Y.X), x₀ ∈ U.1 → ∃ (x : Fin Dw.dim → Γ(TF.Y.X, U.1)) (U' : TF.Y.X.affineOpens) (hU' : U'.1 ≤ U.1), x₀ ∈ U'.1 ∧ TopForm.IsFrame (TopForm.dOn TF.Y.s fun i => resG TF.Y.X hU' (x i)) ∧ (LogKS.boundary TF.Y).ideal U' = Ideal.span {resG TF.Y.X hU' (logDet (fun j => (b j).1) x)} := by
  first | exact @GlobalTheory.LogPole.exists_coord_logDet | exact GlobalTheory.LogPole.exists_coord_logDet | (intros; apply GlobalTheory.LogPole.exists_coord_logDet <;> assumption)
end

