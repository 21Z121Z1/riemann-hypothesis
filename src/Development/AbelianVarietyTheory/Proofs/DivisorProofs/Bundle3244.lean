import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2755
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3228
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3222
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3223
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0607
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOneBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2843
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3224
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3183
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2984
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2291
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0082
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3132
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3238
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2766
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPsiCoordOfIsPsiCoord
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0110
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3230
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1226
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0345
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1142
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0256
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2649
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1580
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0084
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePointsCycAway
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIffEighthPowerPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaObjectEighthPowerPrincipalSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2907
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3210
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftAdicCompletion
section
open IsLocalRing GlobalTheory.Poinc.Eq8
open scoped TensorProduct

namespace GlobalTheory.TraitLift

theorem exists_lift_adicCompletion (A V : Type) [CommRing A] [IsLocalRing A] [Algebra.EssFiniteType ℤ A]
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra A V] :
    ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (h : V →+* V')
      (g : AdicCompletion (maximalIdeal A) A →+* V'), IsAdicComplete (maximalIdeal V') V' ∧
      g.comp (algebraMap A _) = h.comp (algebraMap A V) ∧ ∀ ϖ : V, Irreducible ϖ → Irreducible (h ϖ) := by
  haveI : IsNoetherianRing A := Algebra.EssFiniteType.isNoetherianRing ℤ A
  let R := AdicCompletion (maximalIdeal A) A
  haveI : Module.FaithfullyFlat A R := Module.FaithfullyFlat.of_flat_of_isLocalHom
  letI : Field (V ⧸ maximalIdeal V) := Ideal.Quotient.field _
  let C := V ⊗[A] R
  let e : (C ⧸ (maximalIdeal V).map (algebraMap V C)) ≃+* R ⊗[A] (V ⧸ maximalIdeal V) :=
    ((Algebra.TensorProduct.quotIdealMapEquivQuotTensor C (maximalIdeal V)).toRingEquiv.trans
      (Algebra.TensorProduct.cancelBaseChange A V V (V ⧸ maximalIdeal V) R).toRingEquiv).trans
      (Algebra.TensorProduct.comm A _ _).toRingEquiv
  haveI := formalFibre_isReduced_of_field A (V ⧸ maximalIdeal V)
  haveI : Nontrivial (R ⊗[A] (V ⧸ maximalIdeal V)) := inferInstance
  obtain ⟨V', i1, i2, i3, h₀, hc, hirr⟩ := GlobalTheory.ReducedFibre.exists_cdvr_of_flat_of_isReduced V C
    e.toEquiv.nontrivial (isReduced_of_injective e e.injective)
  refine ⟨V', i1, i2, i3, h₀.comp (algebraMap V C),
    h₀.comp (Algebra.TensorProduct.includeRight (R := A) (A := V) (B := R)).toRingHom, hc, ?_, hirr⟩
  ext a
  simp only [RingHom.comp_apply]
  congr 1
  rw [← IsScalarTower.algebraMap_apply]
  exact (Algebra.TensorProduct.includeRight (R := A) (A := V) (B := R)).commutes a

theorem isLocalHom_and_injective {V V' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [CommRing V'] [IsDomain V'] (h : V →+* V') (hh : ∀ ϖ : V, Irreducible ϖ → Irreducible (h ϖ)) :
    Function.Injective h ∧ IsLocalHom h := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  refine ⟨(injective_iff_map_eq_zero h).mpr fun x hx => ?_, ⟨fun x hx => ?_⟩⟩
  · by_contra h0
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hϖ
    rw [map_mul, map_pow] at hx
    exact mul_ne_zero (u.isUnit.map h).ne_zero (pow_ne_zero n (hh ϖ hϖ).ne_zero) hx
  · by_contra hu
    have hm : x ∈ maximalIdeal V := hu
    rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hm
    exact (hh ϖ hϖ).not_isUnit (isUnit_of_dvd_unit (map_dvd h hm) hx)

theorem exists_lift_of_isCpl : ∀ (A R V : Type) [CommRing A] [IsLocalRing A] [Algebra.EssFiniteType ℤ A] [CommRing R] (j : A →+* R), IsCpl j → ∀ [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (f : A →+* V), ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (h : V →+* V') (g : R →+* V'), IsAdicComplete (maximalIdeal V') V' ∧ Function.Injective h ∧ IsLocalHom h ∧ g.comp j = h.comp f ∧ ∀ ϖ : V, Irreducible ϖ → Irreducible (h ϖ) := by
  intro A R V _ _ _ _ j hj _ _ _ f
  obtain ⟨e, he⟩ := hj
  letI : Algebra A V := f.toAlgebra
  obtain ⟨V', i1, i2, i3, h, g, hc, hcomp, hirr⟩ := exists_lift_adicCompletion A V
  obtain ⟨hinj, hloc⟩ := isLocalHom_and_injective h hirr
  refine ⟨V', i1, i2, i3, h, g.comp e.symm.toRingHom, hc, hinj, hloc, ?_, hirr⟩
  ext a
  have := RingHom.congr_fun hcomp a
  simp only [RingHom.comp_apply] at this ⊢
  rw [← he a]
  simpa [RingHom.algebraMap_toAlgebra] using this

end GlobalTheory.TraitLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearFunctionalArchIntegralChernPowerStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linear_functional_arch_integral_chern_power : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k), IsAmb q → ∀ (e : ℕ) (ι : Type) [Fintype ι] (L : ι → HermLB q) (M : HermLB q) (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r), (∀ n, (comb L n).ArchIntegrable M e hr) → ∃ Ψ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ, ∀ n : ι → ℤ, Ψ (lin (fun i => (n i : ℝ)) ^ e) = (comb L n).archInt M e hr := by
  first | exact @GlobalTheory.MixFun.exists_functional_archInt | exact GlobalTheory.MixFun.exists_functional_archInt | (intros; apply GlobalTheory.MixFun.exists_functional_archInt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocallyClosedUniversalHomMatrixSchemeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_locallyClosed_universal_hom_matrix_scheme : ∀ (Rg : Type) [CommRing Rg] [IsNoetherianRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (k : ℕ) (mA mB : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))) (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))), Hyps L M k bA bB eA eB → ∃ (X : Scheme.{0}) (cE : X ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)) (H : Scheme.{0}) (i : H ⟶ X) (AH : Over H) (_ : GrpObj AH) (BH : Over H) (_ : GrpObj BH) (φA : AH.left ⟶ A.left) (φB : BH.left ⟶ B.left) (Φ : AH ⟶ BH), IsClosedImmersion cE ∧ IsOpenImmersion i ∧ IsTest A B L M (i ≫ cE ≫ affπ Rg (mA * mB)) AH BH φA φB Φ ∧ (∀ (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B') (c : Fin mA → Fin mB → Γ(Sp R, ⊤)), IsTest A B L M t A' B' φA' φB' Φ' → IsMat L M k bA bB eA eB t A' B' φA' φB' Φ' c → ∃ h : Sp R ⟶ H, h ≫ i ≫ cE ≫ affπ Rg (mA * mB) = t ∧ matOf (h ≫ i ≫ cE) = c) ∧ ∀ (R : Type) [CommRing R] (h : Sp R ⟶ H) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B'), IsTest A B L M (h ≫ i ≫ cE ≫ affπ Rg (mA * mB)) A' B' φA' φB' Φ' → IsPullD φA φB Φ φA' φB' Φ' h → IsMat L M k bA bB eA eB (h ≫ i ≫ cE ≫ affπ Rg (mA * mB)) A' B' φA' φB' Φ' (matOf (h ≫ i ≫ cE)) := by
  first | (exact @GlobalTheory.HomFixUniv.exists_universal_matrix) | (exact GlobalTheory.HomFixUniv.exists_universal_matrix) | (intros; apply GlobalTheory.HomFixUniv.exists_universal_matrix  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordFormalSectionCoefficientFamily
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

namespace GlobalTheory.MumCoef

theorem shift_add' {X : Type} [AddCommGroup X] (h h' : X →+ X) (n j : ℤ) (a b : X) :
    shift h h' n j (a + b) = shift h h' n j a + shift h h' n j b := by
  simp only [shift, map_add, smul_add]; abel

theorem shift_zero' {X : Type} [AddCommGroup X] (h h' : X →+ X) (n j : ℤ) :
    shift h h' n j 0 = 0 := by
  simp [shift]

theorem coef : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ N : ℕ, 1 ≤ N → GlobalTheory.MumMult.PosN D a h h' N → ∀ (σ₀ : LB.Sec (LB.LinComb D.toPre.P.L (K := Fin 2) ![𝟙 D.toPre.P.A.left, a.left] ![(N : ℤ), -1])), ∃ g : ∀ β, SecT D.toPre a N (-1) β, Small (maximalIdeal R) (w := id) g ∧ TFE h h' g ∧ (∀ β, β ≠ 0 → Van (maximalIdeal R) (g β) 0) ∧ ∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R (maximalIdeal R) 0 D.toPre.P.A).left) (z : Z) (J), Good D.toPre.P.L z J → sval (g 0) (x ≫ pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) 0)) z J = sval σ₀ (x ≫ pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) 0)) z J := by
  classical
  intro R _ _ _ hB D a a' h h' hE N hN hP σ₀
  obtain ⟨s₀, s, hrel, hsmall, hvan, hσ⟩ := GlobalTheory.T.exists_terms_mumfordFormalSection_translates R hB D a a' h h' hE N hN hP σ₀
  obtain ⟨F, hsum, hFs⟩ := GlobalTheory.T.exists_adicSum_twistedSectionFamily_tendsToZero R hB D a (N : ℤ) (-1) D.toPre.X (shift h h' (N : ℤ) (-1)) s hsmall
  have hw0 : shift h h' (N : ℤ) (-1) (0 : D.toPre.X) = 0 := shift_zero' h h' _ _
  have hfe : TFE h h' F := by
    refine GlobalTheory.T.twistedFunctionalEquation_of_adicSum_termwise R hB D a a' h h' hE (N : ℤ) (-1) D.toPre.X (shift h h' (N : ℤ) (-1)) s F
      (fun mu => Equiv.addRight mu) hsmall hsum ?_ ?_
    · intro mu i
      exact shift_add' h h' _ _ i mu
    · intro mu i
      exact GlobalTheory.T.twistedRelation_cocycle_in_translation R hB D a a' h h' hE (N : ℤ) (-1) i mu 0 _ _ s₀ (s i) (s (i + mu))
        (zero_add _).symm (shift_add' h h' _ _ i mu) (hrel i) (hrel (i + mu))
  have hv0 : ∀ i ∉ ({0} : Finset D.toPre.X), Van (maximalIdeal R) (s i) 0 := fun i hi =>
    hvan i (by simpa using hi)
  refine ⟨F, hFs, hfe, ?_, ?_⟩
  · intro β hβ Z x z J hJ
    rw [hsum 0 {0} hv0 β Z x z J hJ]
    have : ({0} : Finset D.toPre.X).filter (fun i => shift h h' (N : ℤ) (-1) i = β) = ∅ := by
      rw [Finset.filter_singleton, hw0, if_neg (Ne.symm hβ)]
    rw [this, Finset.sum_empty]
  · intro Z x z J hJ
    rw [hsum 0 {0} hv0 0 Z x z J hJ]
    have : ({0} : Finset D.toPre.X).filter (fun i => shift h h' (N : ℤ) (-1) i = 0) = {0} := by
      rw [Finset.filter_singleton, hw0, if_pos rfl]
    rw [this, Finset.sum_singleton]
    exact hσ Z _ z J hJ

end GlobalTheory.MumCoef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonvanishingDetLineSectionOfHorizontalStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonvanishing_detLine_section_of_horizontal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (τ : E →+* ℂ) (e : c.F →+* ℂ) (h : CxFr Y e → ℂ) (B : GlobalTheory.ProjVar.Var c.F) (io : B.X ⟶ gen Y) (V : Set (gen Y)), IsOpenImmersion io → Set.range io = V → io ≫ genStr Y = B.str → τ (H.rt : E) = H.rt0 → HorFn τ h → ∃ σb : RuleY Y, SecY Y V τ σb ∧ NzY Y V τ σb := by
  first | exact @GlobalTheory.DetLine.FromHorizontal.exists_section_of_horFn | exact GlobalTheory.DetLine.FromHorizontal.exists_section_of_horFn | (intros; apply GlobalTheory.DetLine.FromHorizontal.exists_section_of_horFn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroSectionClosedFibreOfPrimitiveThetaStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonzero_section_closed_fibre_of_primitive_theta : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (g m N : ℕ) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (χ : Sp V ⟶ S) (θ : SecAt t.G t.PP.L (spMap (algebraMap V (FractionRing V)) ≫ χ)) (pt : Fin N → (Over.mk (spMap (algebraMap V (FractionRing V)) ≫ χ) ⟶ t.G)) (c : Fin N → FractionRing V), Odd m → 3 ≤ m → IsUnit (m : V) → PolFib t.G t.PP.L g (spMap (algebraMap V (FractionRing V)) ≫ χ) → ThList t.G t.PP.L t.PP.rig m _ θ pt c → Prim (algebraMap V (FractionRing V)) c → ∃ σ : SecAt t.G t.PP.L χ, SecM.ofSec t.G (SecAt.pull t.G t.PP.L σ (algebraMap V (FractionRing V))) = SecM.ofSec t.G θ ∧ NZ t.G t.PP.L χ σ := by
  first | exact @GlobalTheory.UMin.exists_sec_nz_of_prim | exact GlobalTheory.UMin.exists_sec_nz_of_prim | (intros; apply GlobalTheory.UMin.exists_sec_nz_of_prim <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOriginNormalisationUnitAtTraitsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_origin_normalisation_unit_at_traits : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D), ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ Φ : IntFam (maximalIdeal R) D.toPre k → SecK C.P.L.L C.α k, (∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ a b : W, a ≠ 0 ∧ b ≠ 0 ∧ ∀ F, T.Exp a b (Φ F) F) → ∃ Φ' : IntFam (maximalIdeal R) D.toPre k → SecK C.P.L.L C.α k, ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, ∀ F, T.Exp 1 u (Φ' F) F := by
  first | exact @GlobalTheory.Mum.exists_unit_normalisation | exact GlobalTheory.Mum.exists_unit_normalisation | (intros; apply GlobalTheory.Mum.exists_unit_normalisation <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimitiveWithCotangentOfDualHeightOneStatement
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_primitive_with_cotangent_of_dual_height_one : ∀ (p : ℕ) [Fact p.Prime] (K H : Type) [Field K] [CharP K p] [CommRing H] [HopfAlgebra K H] [IsCocomm K H] [Module.Finite K H], (∀ φ ∈ augIdeal K (CartierDual K H), φ ^ p = 0) → ∀ w : Cot K H, ∃ b : H, cobOne K H b = 0 ∧ dUnit K b = w := by
  first | exact @GlobalTheory.PDiv.exists_primitive_dUnit_eq | exact GlobalTheory.PDiv.exists_primitive_dUnit_eq | (intros; apply GlobalTheory.PDiv.exists_primitive_dUnit_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullUnif
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.TraitPull

theorem isMonomial_pull {V R : Type} [CommRing V] [IsDomain V] [CommRing R] [IsDomain R]
    {Dg : DegPre V} {Dg' : DegPre R} {ϖ : V} {β : LinearMap.BilinForm ℤ Dg.X} (hm : IsMonomial Dg ![ϖ] ![β])
    (h : V →+* R) (ε : Dg'.X ≃+ Dg.X)
    (hc : ∀ y r, PsiCoord Dg (ε y) r → ∃ u : Rˣ, PsiCoord Dg' y (u * h r)) :
    IsMonomial Dg' ![h ϖ]
      ![β.compl₁₂ (ε : Dg'.X →+ Dg.X).toIntLinearMap (ε : Dg'.X →+ Dg.X).toIntLinearMap] := by
  intro y
  obtain ⟨u, n, hn, hy⟩ := hm (ε y)
  obtain ⟨u', hu'⟩ := hc y _ hy
  refine ⟨u' * Units.map h.toMonoidHom u, n, Fin.forall_fin_one.2 (hn 0), ?_⟩
  have e : (u' : R) * h ((u : V) * ∏ i, ![ϖ] i ^ n i) =
      ((u' * Units.map h.toMonoidHom u : Rˣ) : R) * ∏ i, ![h ϖ] i ^ n i := by
    simp [Fin.prod_univ_one, map_mul, map_pow]
    ring
  exact e ▸ hu'

theorem exists_pull_unif : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (T : Trait F) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → IsDiscreteValuationRing R → ∀ (h : T.V →+* R) (hK : FractionRing T.V →+* FractionRing R), IsLocalHom h → (∀ a, hK (algebraMap T.V _ a) = algebraMap R _ (h a)) → ∃ (G : Over (Sp R)) (_ : GrpObj G) (_ : IsCommMonObj G) (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (_ : Unif (maximalIdeal R) D A G) (α : A.A.left ⟶ F.univ.A.left) (α₂ : (G2 A.A).left ⟶ (G2 F.univ.A).left) (ε : D.toPre.X ≃+ T.D.toPre.X), IsSemiAbelian G ∧ IsGrpPullback A.A F.univ.A (spMap hK ≫ T.y) α ∧ IsSquare α α₂ ∧ LBIso (abelian₂ A.A A.L) (F.univ.P.pull α₂) ∧ ∀ a b' (x : (FractionRing R)ˣ), GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D.toPre a b' x → ∃ u : Rˣ, (x : FractionRing R) = algebraMap R (FractionRing R) (u : R) * algebraMap R (FractionRing R) (h T.ϖ) ^ (T.β (ε a) (ε b')) := by
  intro g n o _ ζ F T R _ _ _ hB hdvr h hK hl hhK
  have hinj : Function.Injective h := by
    intro a b hab
    have e := congrArg (algebraMap R (FractionRing R)) hab
    rw [← hhK, ← hhK] at e
    exact IsFractionRing.injective T.V (FractionRing T.V) (hK.injective e)
  have hϖ : h T.ϖ ≠ 0 := fun e => T.irr.ne_zero (hinj (e.trans (map_zero h).symm))
  have hRC := TraitUniq.isCN_of_base hB
  obtain ⟨κ, hκ, hκβ⟩ := TraitUniq.genFib T h hK hhK
  have hα := hκ.comp T.cart
  have w₁ := hα.1.w
  let α₂B := pullback.map ((Over.pullback (jK R)).obj ((Over.pullback (spMap h)).obj T.G)).hom
    ((Over.pullback (jK R)).obj ((Over.pullback (spMap h)).obj T.G)).hom F.univ.A.hom F.univ.A.hom
    (κ ≫ T.α) (κ ≫ T.α) (spMap hK ≫ T.y) w₁.symm w₁.symm
  have hsqB : IsSquare (κ ≫ T.α) α₂B := ⟨pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  obtain ⟨D', A', U', ε, L, hLl, hL, hΛ, hc⟩ := TraitUniq.pull T hRC h hinj hl hK _ _
    (isGrpPullback_pullback T.G (spMap h)) κ hκ hκβ α₂B hsqB
  haveI := U'.gen_hom
  haveI : IsMonHom U'.gen.symm.hom := inferInstanceAs (IsMonHom U'.gen.inv)
  have hgi := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_of_iso U'.gen.symm
  have hα' := (hgi.comp hα).congr (Category.id_comp _) rfl
  let H : G2 A'.A ⟶ G2 ((Over.pullback (jK R)).obj ((Over.pullback (spMap h)).obj T.G)) :=
    lift (fst A'.A A'.A ≫ U'.gen.inv) (snd A'.A A'.A ≫ U'.gen.inv)
  have hP := F.univ.isLB
  have hAL := A'.isLB
  have hΛA : (abelian₂ A'.A A'.L).IsLB := LB.isLB_linComb hAL _ _
  have hΛB : (abelian₂ _ L).IsLB := LB.isLB_linComb hLl _ _
  have e1 : GlobalTheory.CechPic.pull U'.gen.hom.left (GlobalTheory.CechPic.cls _ hAL) = GlobalTheory.CechPic.cls _ hLl := by
    rw [← GlobalTheory.CechPic.cls_pull hAL _ (pull_isLB hAL _)]
    exact (GlobalTheory.CechPic.cls_eq_iff _ hLl).2
      (LBIso.trans (pull_isLB hAL _) (pull_isLB U'.LG.isLB _) hLl U'.ext hL.symm)
  have hgi' : U'.gen.inv.left ≫ U'.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have e2 : GlobalTheory.CechPic.cls _ hAL = GlobalTheory.CechPic.pull U'.gen.inv.left (GlobalTheory.CechPic.cls _ hLl) := by
    rw [← e1, ← GlobalTheory.CechPic.pull_comp, hgi', GlobalTheory.CechPic.pull_id]
  have eB : GlobalTheory.CechPic.cls _ hΛB = GlobalTheory.CechPic.pull α₂B (GlobalTheory.CechPic.cls _ hP) := by
    rw [← GlobalTheory.CechPic.cls_pull hP _ (pull_isLB hP _)]
    exact (GlobalTheory.CechPic.cls_eq_iff _ _).2 hΛ
  have cA : GlobalTheory.CechPic.cls _ hΛA = GlobalTheory.CechPic.lam (GlobalTheory.CechPic.cls _ hAL) (fst A'.A A'.A) (snd A'.A A'.A) :=
    GlobalTheory.CechPic.cls_cube_two hAL _ _ hΛA
  have cB : GlobalTheory.CechPic.cls _ hΛB = GlobalTheory.CechPic.lam (GlobalTheory.CechPic.cls _ hLl) (fst _ _) (snd _ _) :=
    GlobalTheory.CechPic.cls_cube_two hLl _ _ hΛB
  have eA : GlobalTheory.CechPic.cls _ hΛA = GlobalTheory.CechPic.pull (H.left ≫ α₂B) (GlobalTheory.CechPic.cls _ hP) := by
    rw [cA, e2, GlobalTheory.CechPic.lam_pull, GlobalTheory.CechPic.pull_comp, ← eB, cB, GlobalTheory.CechPic.pull_lam, lift_fst, lift_snd]
  refine ⟨_, inferInstance, inferInstance, D', A', U', U'.gen.inv.left ≫ κ ≫ T.α, H.left ≫ α₂B, ε,
    IsSemiAbelian.pullback (spMap h) T.G T.semi, hα', ⟨?_, ?_⟩,
    (GlobalTheory.CechPic.cls_eq_iff hΛA (pull_isLB hP _)).1 (eA.trans (GlobalTheory.CechPic.cls_pull hP _ _).symm), ?_⟩
  · rw [Category.assoc, hsqB.1, ← Category.assoc, ← Over.comp_left, lift_fst, Over.comp_left, Category.assoc]
  · rw [Category.assoc, hsqB.2, ← Category.assoc, ← Over.comp_left, lift_snd, Over.comp_left, Category.assoc]
  · intro a b' x hx
    obtain ⟨x₁, h₁⟩ := GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.exists_isPsiCoord D'.toPre (a + b')
    obtain ⟨x₂, h₂⟩ := GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.exists_isPsiCoord D'.toPre a
    obtain ⟨x₃, h₃⟩ := GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.exists_isPsiCoord D'.toPre b'
    obtain ⟨u₀, hu₀⟩ := GlobalTheory.TauCoordQuot.main R D'.toPre a b' x x₁ x₂ x₃ hx h₁ h₂ h₃
    obtain ⟨r₁, c₁, e₁⟩ :=
      GlobalTheory.PeriodFormCompare.exists_psiCoord_of_isPsiCoord (GlobalTheory.PeriodFormCompare.psiIn_top D' _) h₁
    obtain ⟨r₂, c₂, e₂⟩ :=
      GlobalTheory.PeriodFormCompare.exists_psiCoord_of_isPsiCoord (GlobalTheory.PeriodFormCompare.psiIn_top D' _) h₂
    obtain ⟨r₃, c₃, e₃⟩ :=
      GlobalTheory.PeriodFormCompare.exists_psiCoord_of_isPsiCoord (GlobalTheory.PeriodFormCompare.psiIn_top D' _) h₃
    have hm := isMonomial_pull T.mono h ε hc
    obtain ⟨u, hu⟩ := hm.tau (fun i y z => by fin_cases i; exact T.symm (ε y) (ε z))
      (Fin.forall_fin_one.2 hϖ) c₂ c₃ c₁
    simp only [Fin.prod_univ_one, Matrix.cons_val_zero, LinearMap.compl₁₂_apply,
      AddMonoidHom.coe_toIntLinearMap, AddMonoidHom.coe_coe] at hu
    refine ⟨u₀ * u, ?_⟩
    have key : algebraMap R (FractionRing R) (u₀ : R) * algebraMap R (FractionRing R) r₁ *
        (algebraMap R (FractionRing R) r₂)⁻¹ * (algebraMap R (FractionRing R) r₃)⁻¹ =
        algebraMap R (FractionRing R) (u₀ : R) * (algebraMap R (FractionRing R) r₁ /
          (algebraMap R (FractionRing R) r₂ * algebraMap R (FractionRing R) r₃)) := by
      rw [div_eq_mul_inv, mul_inv]; ring
    rw [hu₀, e₁, e₂, e₃, key, hu]
    simp only [Units.val_mul, map_mul]
    ring

end GlobalTheory.Poinc.TraitPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionsNefPlusAmpleGeneratedGenericFibre
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

set_option autoImplicit false

namespace GlobalTheory.GenFibreGen

theorem nefFib_pow : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (L : HermLB p) (n : ℕ), NefFib L → NefFib (L.pow n) := by
  intro k _ X _ p D hX L n hL
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine AmpleTwistNef.nefFib_of_cls_eq ?_ (nefFib_of_isNef (HermLB.isNef_triv (p := p) (D := D)))
    erw [CechPic.cls_lbPow L.isLB 0, zero_smul]
    rfl
  · have := hX.finite
    exact (nefFib_pow_iff k X p hX.isProjOver L n hn).2 hL

theorem exists_fst_eq : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (x : X), CharZero (X.residueField x) → ∃ y : ↥(Limits.pullback (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ))), Limits.pullback.fst (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ)) y = x :=
  fun k _ X p x hx => RatDegZeros.mem_range_fst k X p x hx

theorem isProjOver_snd {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ}
    (h : IsArithVar p D) : IsProjOver (Limits.pullback.snd (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ))) := by
  have := h.finite
  have := h.isIntegral
  have : IsFinite (spMap (Int.castRingHom k)) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.2 h.finite
  obtain ⟨_, L, hL⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB p).1 h.isProjOver
  have hP : IsProjOver (p ≫ spMap (Int.castRingHom k)) := hL.isProjOver _
  exact ProjSpace.isProjOver_pullback_snd (Int.castRingHom ℚ) hP

theorem exists_secs_generic : GlobalTheory.Published.NefNumerics → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (L A : HermLB p) (n : ℕ), NefFib L → IsAmpleLB A.B → ∃ (m : ℕ) (N : ℕ) (s : Fin N → (((L.pow n).tens A).pow m).B.Sec), 1 ≤ m ∧ ∀ x : X, CharZero (X.residueField x) → ∃ i, x ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (s i) := by
  intro hNN k _ X _ p D hX L A n hL hA
  have hN := GlobalTheory.T.isNef_rationalFibre_of_nef_finiteFieldFibres k X p D hX (L.pow n) (nefFib_pow k X p D hX L n hL)
  have : IsAffineHom (Limits.pullback.fst (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ))) :=
    isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _).flip inferInstance
  have hA' : IsAmpleLB (A.B.pull (Limits.pullback.fst (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ)))) :=
    hA.pull_of_isAffineHom _
  have hK := IsAmpleLB.tens_of_isNef hNN ℚ _ _ (isProjOver_snd hX) _ _ hA' hN
  obtain ⟨m, hm, N, t, ht⟩ := hK.exists_isGenerated_pow
  have hM := pull_isLB (((L.pow n).tens A).pow m).isLB (Limits.pullback.fst (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ)))
  obtain ⟨v, hv⟩ := CechPic.exists_generating_secs_of_cls_eq _ _ _ (isLB_lbPow hK.isLB m) hM (by
      rw [CechPic.cls_lbPow hK.isLB m, CechPic.cls_pull (((L.pow n).tens A).pow m).isLB _ hM]
      erw [CechPic.cls_lbPow ((L.pow n).tens A).isLB m]
      rw [map_nsmul]
      congr 1
      erw [CechPic.cls_tens (pull_isLB A.isLB _) (pull_isLB (L.pow n).isLB _), CechPic.cls_tens (L.pow n).isLB A.isLB]
      rw [map_add, CechPic.cls_pull A.isLB, CechPic.cls_pull (L.pow n).isLB, add_comm]) (Fin N) t ht
  choose s hs using fun i => GlobalTheory.T.exists_section_extending_rationalGenericFibre_mul_int k X p D hX _ (((L.pow n).tens A).pow m).isLB (v i)
  refine ⟨m, N, s, hm, fun x hx => ?_⟩
  obtain ⟨y, rfl⟩ := exists_fst_eq k X p x hx
  have hy : y ∈ ⨆ i, ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (v i) := hv ▸ trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
  exact ⟨i, (hs i y).2 hi⟩

end GlobalTheory.GenFibreGen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymmetricThetaConstantsEqThetaMapCoordsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_symmetric_theta_constants_eq_thetaMap_coords : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (P : PolAV F.X) (rig : LB.Gen (P.L.pull (eSec P.A))) (m N : ℕ) (f : F.X ⟶ PSpace (cycAway n) N), ThAt F W P rig m f → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (β : cycAway n →+* o) (S : ThetaSys o Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X), SysAt F W β S ρ u → ∃ e : Fin (N + 1) → Ω, SymE ρ m e ∧ ∀ (h : Sp Ω ⟶ PSpace (cycAway n) N), h = spMap (algebraMap S.R Ω) ≫ u ≫ f → PCrd h e := by
  first | exact @GlobalTheory.SiegTh.exists_symE_pCrd | exact GlobalTheory.SiegTh.exists_symE_pCrd | (intros; apply GlobalTheory.SiegTh.exists_symE_pCrd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticLevelPrincipalSiegelAlgClosedStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.SiegLev GlobalTheory.SiegLevCalc GlobalTheory.SiegelPullComp GlobalTheory.SiegelPull
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_symplecticLevel_principalSiegel_algClosed : ∀ (g n N : ℕ) (B : Type) [CommRing B] (ζ : B) (K : Type) [Field K] [IsAlgClosed K] (s : Sp K ⟶ Sp B) (c : SiegPre g n ζ s) (b : TBase K N), Odd N → 3 ≤ N → c.Principal → SmoothOfRelativeDimension g c.A.hom → ∃ C : SiegPre g N (b.ζ : K) (𝟙 (Sp K)), SRel C c 0 0 (𝟙 _) := by
  first | exact @GlobalTheory.SiegLift.exists_level_of_forget | exact GlobalTheory.SiegLift.exists_level_of_forget | (intros; apply GlobalTheory.SiegLift.exists_level_of_forget <;> assumption)
end

