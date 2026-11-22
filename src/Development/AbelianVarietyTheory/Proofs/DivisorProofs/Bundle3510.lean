import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3485
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0615
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3484
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3471
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3265
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdlAlongEqSpanMonomial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2971
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2831
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2336
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0026
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
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2496
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0031
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfAppInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2997
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0036
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0031
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsScalarFormTraceForm
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0013
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnivIdentity
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0140
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GtActIffEqGtSmul

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointDefinedOverSubfieldOfIsIntegralHom
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DefOverIntegral

theorem mem_of_isIntegral {K : Type} [Field K] (k₀ : Subfield K) (hk : IsAlgClosed k₀) {x : K}
    (hx : IsIntegral k₀ x) : x ∈ k₀ := by
  obtain ⟨a, ha⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k₀)
    (K := integralClosure k₀ K)).2 ⟨x, hx⟩
  have h1 : ((algebraMap k₀ (integralClosure k₀ K) a : integralClosure k₀ K) : K) = x := congrArg Subtype.val ha
  have h2 : ((algebraMap k₀ (integralClosure k₀ K) a : integralClosure k₀ K) : K) = (a : K) := rfl
  rw [← h1, h2]
  exact a.2

theorem defOver_of_isIntegralHom : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) [IsIntegralHom f] {K : Type} [Field K]
    (k₀ : Subfield K), IsAlgClosed k₀ → ∀ P : Sp K ⟶ X, GlobalTheory.UChart.DefOver k₀ (P ≫ f) → GlobalTheory.UChart.DefOver k₀ P := by
  intro X Y f _ K _ k₀ hk P ⟨Q₀, hQ⟩
  let g := pullback.snd f Q₀
  let Pt : Sp K ⟶ pullback f Q₀ := pullback.lift P (spMap k₀.subtype) hQ.symm
  haveI : IsAffine (pullback f Q₀) := isAffine_of_isAffineHom g
  have hint : (g.app ⊤).hom.IsIntegral := g.isIntegral_app ⊤ (isAffineOpen_top _)
  let φc : Γ(pullback f Q₀, ⊤) ⟶ CommRingCat.of K := Pt.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom
  have hPt : Pt = Spec.map φc ≫ (pullback f Q₀).isoSpec.inv := by
    have h := Scheme.isoSpec_inv_naturality Pt
    rw [Scheme.isoSpec_Spec_inv] at h
    rw [Spec.map_comp, Category.assoc, h, ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id,
      Category.id_comp]
  have hg : Pt ≫ g = spMap k₀.subtype := pullback.lift_snd _ _ _
  have hcomp : g.appTop ≫ φc = (Scheme.ΓSpecIso (CommRingCat.of k₀)).hom ≫ CommRingCat.ofHom k₀.subtype := by
    have h := congrArg Scheme.Hom.appTop hg
    rw [Scheme.Hom.comp_appTop] at h
    simp only [φc, ← Category.assoc, h]
    exact Scheme.ΓSpecIso_naturality _
  have hmem : ∀ r, φc.hom r ∈ k₀ := by
    intro r
    obtain ⟨p, hpm, hp⟩ := hint r
    refine mem_of_isIntegral k₀ hk ⟨p.map (Scheme.ΓSpecIso (CommRingCat.of k₀)).hom.hom, hpm.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have e : (algebraMap k₀ K).comp (Scheme.ΓSpecIso (CommRingCat.of k₀)).hom.hom = φc.hom.comp (g.app ⊤).hom := by
      have := congrArg CommRingCat.Hom.hom hcomp
      exact this.symm
    rw [e]
    have h3 := Polynomial.hom_eval₂ p (g.app ⊤).hom φc.hom r
    rw [hp] at h3
    exact h3.symm.trans (RingHom.map_zero _)
  let φ₀ : Γ(pullback f Q₀, ⊤) →+* k₀ := φc.hom.codRestrict k₀ hmem
  refine ⟨Spec.map (CommRingCat.ofHom φ₀) ≫ (pullback f Q₀).isoSpec.inv ≫ pullback.fst f Q₀, ?_⟩
  have e2 : spMap k₀.subtype ≫ Spec.map (CommRingCat.ofHom φ₀) = Spec.map φc := by
    rw [spMap, ← Spec.map_comp]
    rfl
  rw [← Category.assoc, e2, ← Category.assoc, ← hPt]
  exact pullback.lift_fst _ _ _

end GlobalTheory.DefOverIntegral
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialGoodReductionOfDivisionAlgebraLeftActioStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.potentialGoodReduction_of_divisionAlgebra_leftAction : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (A : Over (Sp K)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (O : Type) [Ring O] (act : O → (A ⟶ A)), (∀ a, IsMonHom (act a)) → act 1 = 𝟙 A → (∀ a b, act (a * b) = act b ≫ act a) → (∀ a b, act (a + b) = act a * act b) → ∀ (B : Type) [Ring B] [Algebra ℚ B] [Module.Finite ℚ B] (jj : O →+* B), (∀ x : B, x ≠ 0 → IsUnit x) → Function.Injective jj → Submodule.span ℚ (Set.range jj) = ⊤ → g < Module.finrank ℚ B → GlobalTheory.SS.PotModel V K A (fun _ _ _ G _ => IsAbelianScheme G) := by
  first | exact @GlobalTheory.potModel_of_divAlg_leftAction | exact GlobalTheory.potModel_of_divAlg_leftAction | (intros; apply GlobalTheory.potModel_of_divAlg_leftAction <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialGoodReductionOfLieMultZeroStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.potentialGoodReduction_of_lieMult_zero : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (F : Type) [Field F] [NumberField F] (act : OAct (𝓞 F) A) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (g : K →+* Ω) (σ : 𝓞 F →+* Ω), LieMult act (spMap g) σ 0 → GlobalTheory.SS.PotModel V K A (fun _ _ _ G _ => IsAbelianScheme G) := by
  first | exact @GlobalTheory.PotGoodLie.potGood_of_lieMult_zero | exact GlobalTheory.PotGoodLie.potGood_of_lieMult_zero | (intros; apply GlobalTheory.PotGoodLie.potGood_of_lieMult_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreChartOfTautologicalChartEtaleCompletion
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.Poinc GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TChartPre

theorem essFiniteType_int_stalk (n : ℕ) (X : Scheme.{0}) (s : X ⟶ Sp (cycAway n)) [LocallyOfFiniteType s] (x : X) :
    Algebra.EssFiniteType ℤ (X.presheaf.stalk x) := by
  have h1 : (s.stalkMap x).hom.EssFiniteType := LocallyOfFiniteType.stalkMap s x
  let p : PrimeSpectrum (cycAway n) := s x
  have h2 : (algebraMap (cycAway n) ((Spec.structureSheaf (cycAway n)).presheaf.stalk p)).EssFiniteType :=
    RingHom.essFiniteType_algebraMap.2 (Algebra.EssFiniteType.of_isLocalization _ p.asIdeal.primeCompl)
  haveI := finiteType_cycAway n
  have h3 : (algebraMap ℤ (cycAway n)).EssFiniteType := RingHom.essFiniteType_algebraMap.2 inferInstance
  have h4 := (h3.comp h2).comp h1
  rw [← RingHom.essFiniteType_algebraMap]
  convert h4
  exact RingHom.ext_int _ _

theorem eq_of_jK_comp_eq {R o : Type} [CommRing R] [IsDomain R] [CommRing o] {u v : Sp R ⟶ Sp o}
    (h : jK R ≫ u = jK R ≫ v) : u = v := by
  obtain ⟨u, rfl⟩ := Spec.map_surjective u
  obtain ⟨v, rfl⟩ := Spec.map_surjective v
  have h' : u ≫ CommRingCat.ofHom (algebraMap R (FractionRing R)) = v ≫ CommRingCat.ofHom (algebraMap R (FractionRing R)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp]
    exact h
  congr 1
  ext a
  exact IsFractionRing.injective R (FractionRing R) (congrArg (fun f => f.hom a) h')

theorem preChart_of_isEtaleCompletion : ∀ g : ℕ, 1 ≤ g → ∀ φ : InvFun ℤ, IsPolFan id g φ → NoSelfInt id g φ → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (OZ : LB Z) (d : ℕ) (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), MinAt5 F z i OZ → BlowAt F z i φ d π j BD → ∀ (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) [GrpObj G₁] [IsCommMonObj G₁] (y : Sp (FractionRing C.R) ⟶ F.X) (α₁ : pullback G₁.hom (jK C.R) ⟶ F.univ.A.left) (ξ : Sp C.R ⟶ S), C.IsFam F G₁ y α₁ → y ≫ j = jK C.R ≫ ξ → IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → ((residue C.R).comp (Scheme.stalkClosedPointTo ξ).hom).FormallyUnramified → PreChart F (π ≫ z) j φ BD d (ξ (closedPoint C.R)) := by
  intro g hg φ hφ _ n hn _ F Z z i OZ d S π j _ BD hM hB C G₁ _ _ y α₁ ξ hF hy het hfu
  obtain ⟨J, -, -, -, -, hP, -, hji, -, -, hval⟩ := hB
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, ⟨-, -, -, hiz, -⟩, -⟩ := hM
  obtain ⟨hsa, hab, hgen, hmum, hbase⟩ := hF
  obtain ⟨hreg, hch, -, -, hrel, -⟩ := GlobalTheory.TChart.Taut.isRegularLocalRing_and_isRelParam g n φ hn C
  obtain ⟨hmono, hrk, hcone, hdef, -⟩ := GlobalTheory.TChart.Taut.monomial_chart g n φ (by omega) C
  haveI : IsProper (π ≫ z) := by
    obtain ⟨N, ιP, hιP, e⟩ := hP
    rw [← e]
    haveI := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str (cycAway n) N
    infer_instance
  haveI : S.IsSeparated := ⟨by
    rw [← terminal.comp_from (π ≫ z)]
    infer_instance⟩
  haveI : Algebra.EssFiniteType ℤ (S.presheaf.stalk (ξ (closedPoint C.R))) :=
    essFiniteType_int_stalk n S (π ≫ z) _
  haveI : IsNoetherianRing C.R := C.compl.1
  have hc : IsAdicComplete (maximalIdeal C.R) C.R := C.compl.2.1
  have hξ : ξ ≫ π ≫ z = spMap C.b := eq_of_jK_comp_eq (by
    rw [← hbase, ← Category.assoc, ← hy, Category.assoc, ← Category.assoc j, hji, hiz])
  have hrad := GlobalTheory.EtaleCompletionRadical.isRadical_map_of_isEtaleCompletion _ _ (Scheme.stalkClosedPointTo ξ).hom hc het hfu
  obtain ⟨hb₁, hb₂⟩ := GlobalTheory.BdEqChart.boundary_eq g n F S j C.R C.b ξ G₁ y ((Over.pullback (jK C.R)).obj G₁)
    (pullback.fst G₁.hom (jK C.R)) α₁ hsa (isGrpPullback_pullback G₁ (jK C.R)) hgen hy hrad C.m C.t hrel hab
  haveI : Module.Free ℤ C.Q.X := Module.Free.of_equiv C.e.toIntLinearEquiv.symm
  have hnat : ∀ k, ∃ c : ℕ, φ.evalZ ((n : ℤ) • C.δ k) = c := fun k =>
    (hφ C.Q.X hrk).exists_nat (Submodule.smul_mem _ _ (hcone.mem k)) fun w =>
      mul_nonneg (Int.natCast_nonneg n) (hcone.nonneg k w)
  choose c hcn using hnat
  have ha : ∀ k, ((d * c k : ℕ) : ℝ) = d * φ.evalZ ((n : ℤ) • C.δ k) := fun k => by rw [hcn, Nat.cast_mul]
  have hBD := GlobalTheory.ChartIdeal.idlAlong_eq_span_monomial g n F S j φ hφ d BD.idealSheaf hval C.R hc C.b ξ C.Q G₁ y α₁ hsa hgen
    hy.symm hmum C.m C.t C.δ (fun k => d * c k) hrel hab hcone hdef hmono ha
  exact ⟨C.R, inferInstance, hreg, inferInstance, C.b, ξ, C.m, C.t, C.Q, C.δ, fun k => d * c k, G₁, inferInstance, y, α₁,
    ⟨hc, hch, hξ, rfl, het, hfu⟩, ⟨hrel, hb₂, hb₁⟩, ⟨hsa, hab, hy, hgen⟩, ⟨hmum, hrk, hcone, hdef, hmono⟩, ha, hBD⟩

end GlobalTheory.TChartPre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveH1StructureAbelianStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitive_h1_structure_abelian : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → StructureSheafH1Primitive A := by
  first | exact @GlobalTheory.AbCoh.primO1_of_isAbelianScheme | exact GlobalTheory.AbCoh.primO1_of_isAbelianScheme | (intros; apply GlobalTheory.AbCoh.primO1_of_isAbelianScheme <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalPolarisationIsoExtendsDescendedGroupStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalPolarisationIso_extends_descendedGroup : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → (∀ x : S, x ∉ Set.range j → UPre Xo c φ j BD d x) → ∀ (tF : SAB H (Xo.XF c)), SABMap tF Xo.univ.t (pullback.fst _ _) → ∀ (G : Over S) [GrpObj G] [IsCommMonObj G] (e : tF.G.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback tF.G G j e → (∀ {k : Type} [Field k] {m n : ℕ} (C : MonoFam Xo c φ (ChartRing k m n)), IsTaut C → ∀ ξ : Sp (ChartRing k m n) ⟶ S, C.y ≫ j = jK _ ≫ ξ → ∀ (tK : SAB H (Sp (FractionRing (ChartRing k m n)))) (a : SABMap tK C.t (jK _)) (b : SABMap tK tF C.y), ∃ πC : C.t.G.left ⟶ G.left, IsGrpPullback C.t.G G ξ πC ∧ a.φ ≫ πC = b.φ ≫ e) → ∀ (act : OAct (𝓞 E) G), (∀ a, (tF.act.act a).left ≫ e = e ≫ (act.act a).left) → ∀ (PP : RigLB G) (cub : CubicalStr G PP) (cm : CubeMap tF.G G), cm.F = e → cm.e = j → cm.IsPullCubical tF.cub cub → LBIso PP.L (cubeLB G ![𝟙 G, act.act H.w0] PP.L) := by
  first | exact @GlobalTheory.PrimExt.lbIso_prim_ext | exact GlobalTheory.PrimExt.lbIso_prim_ext | (intros; apply GlobalTheory.PrimExt.lbIso_prim_ext <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProportionalPositiveVolumesStatement
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.proportional_positive_volumes : Hypotheses2 → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → Proport Y.U ∧ ∀ Z, 0 < CompHt.vZero Y.U Z := by
  first | exact @GlobalTheory.CompProport.proport_good | exact GlobalTheory.CompProport.proport_good | (intros; apply GlobalTheory.CompProport.proport_good <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiSqGenericPointEqMonomialMulSymmetric
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.Poinc.Sep.Frames GlobalTheory.UT.CoefBasic
noncomputable section

namespace GlobalTheory.PsiSqGeneric

theorem jFK_self (V : Type) [CommRing V] [IsDomain V] :
    jFK (R := V) (FractionRing V) = 𝟙 (Spec (CommRingCat.of (FractionRing V))) := by
  show Spec.map (CommRingCat.ofHom (algebraMap (FractionRing V) (FractionRing V))) = 𝟙 _
  rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]

theorem cst_eq_gm {V : Type} [CommRing V] [IsDomain V] (z : Spec (CommRingCat.of (FractionRing V)))
    (k : (FractionRing V)ˣ) :
    cst (R := V) (FractionRing V) z (k : FractionRing V) =
      (gm (𝟙 (Spec (CommRingCat.of (FractionRing V)))) z ⊤ (unitOn k)).val := by
  rw [← gs_unit _ z ⊤ trivial]
  rfl

end GlobalTheory.PsiSqGeneric

namespace GlobalTheory.PsiSqGeneric

theorem core (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (hE : D.PsiEven)
    (h0 : ∀ (Z : Scheme.{0}) (r : Z ⟶ (TK V).left) (z : Z) J, Good D.P.L z J →
      val (D.psi 0) r z J * val D.rigK r z J = 1)
    (τ₀ : GlobalTheory.UChart.Gens D) (N : ℕ) (s : Fin N → V) (ε : Fin N → LinearMap.BilinForm ℤ D.X)
    (hT : GlobalTheory.UChart.TauIn D τ₀ s ε) (mu : D.X) : ∃ k : (FractionRing V)ˣ,
      (k : FractionRing V) = ∏ i, algebraMap V (FractionRing V) (s i) ^ ε i mu mu ∧
      ∀ (z : Spec (CommRingCat.of (FractionRing V)))
        (J : (Spec (CommRingCat.of (FractionRing V)) ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J →
        (val (D.psi mu) (jFK (R := V) (FractionRing V)) z J).val ^ 2 =
          cst (R := V) (FractionRing V) z (k : FractionRing V) *
            (val D.sym ((toUnit (TF (R := V) (FractionRing V))).left ≫ (D.c mu).left) z J *
              (val (τ₀ mu (-mu)) (toUnit (TF (R := V) (FractionRing V))).left z J)⁻¹ *
              (rigV D (toUnit (TF (R := V) (FractionRing V))).left z J ^ 2)⁻¹).val := by
  obtain ⟨-, k', hk', hv⟩ := hT mu (-mu)
  refine ⟨k'⁻¹, ?_, fun z J hJ => ?_⟩
  · rw [Units.val_inv_eq_inv_val, hk']
    simp only [map_neg, zpow_neg, Finset.prod_inv_distrib, inv_inv]
  · have hv' : val (D.tau mu (-mu)) (𝟙 (Spec (CommRingCat.of (FractionRing V)))) z J =
        gm (𝟙 (Spec (CommRingCat.of (FractionRing V)))) z ⊤ (unitOn k') * val (τ₀ mu (-mu)) (jK V) z J :=
      hv z J hJ
    have ev := val_corr hJ (hE mu) (𝟙 (Spec (CommRingCat.of (FractionRing V))))
    rw [val_mul hJ, val_pull hJ, Category.id_comp] at ev
    have p0 := h0 _ (𝟙 (Spec (CommRingCat.of (FractionRing V)))) z J hJ
    have hrig : val D.rigK (𝟙 (Spec (CommRingCat.of (FractionRing V)))) z J = rigV D (jK V) z J := by
      rw [DegPre.rigK, val_pull hJ, Category.id_comp]; rfl
    have hx : D.xK mu = jK V ≫ (D.c mu).left := rfl
    unfold DegPre.tau at hv'
    rw [val_mul hJ, val_mul hJ, val_mul hJ, val_inv, val_inv, val_inv,
      congrArg (fun w => val (D.psi w) (𝟙 (Spec (CommRingCat.of (FractionRing V)))) z J) (add_neg_cancel mu)] at hv'
    rw [hx] at ev
    rw [hrig] at p0 hv'
    rw [jFK_self, GlobalTheory.Poinc.Sep.Frames.toUnit_left_eq, cst_eq_gm]
    have hg : gm (𝟙 (Spec (CommRingCat.of (FractionRing V)))) z ⊤ (unitOn k'⁻¹) =
        (gm (𝟙 (Spec (CommRingCat.of (FractionRing V)))) z ⊤ (unitOn k'))⁻¹ := by
      rw [← map_inv]; rfl
    rw [hg, ← Units.val_pow_eq_pow_val, ← Units.val_mul]
    congr 1
    have hp := eq_inv_of_mul_eq_one_left p0
    have hb := eq_mul_inv_of_mul_eq ev
    have hG := eq_mul_inv_of_mul_eq hv'.symm
    rw [hG, hp, hb]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_pow]
    abel

end GlobalTheory.PsiSqGeneric

theorem GlobalTheory.PsiSqGeneric.main : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V), D.PsiEven →
    (∀ (Z : Scheme.{0}) (r : Z ⟶ (TK V).left) (z : Z) J, Good D.P.L z J →
      val (D.psi 0) r z J * val D.rigK r z J = 1) →
    ∀ (τ₀ : GlobalTheory.UChart.Gens D) (N : ℕ) (s : Fin N → V) (ε : Fin N → LinearMap.BilinForm ℤ D.X),
    GlobalTheory.UChart.TauIn D τ₀ s ε → ∀ mu : D.X, ∃ k : (FractionRing V)ˣ,
      (k : FractionRing V) = ∏ i, algebraMap V (FractionRing V) (s i) ^ ε i mu mu ∧
      ∀ z J, Good D.P.L z J →
        (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (D.psi mu) (jFK (R := V) (FractionRing V)) z J)).val ^ 2 =
          cst (FractionRing V) z (k : FractionRing V) *
            (val D.sym ((toUnit (TF (R := V) (FractionRing V))).left ≫ (D.c mu).left) z J *
              (val (τ₀ mu (-mu)) (toUnit (TF (R := V) (FractionRing V))).left z J)⁻¹ *
              (rigV D (toUnit (TF (R := V) (FractionRing V))).left z J ^ 2)⁻¹).val := by
  intro V _ _ D hE h0 τ₀ N s ε hT mu
  exact GlobalTheory.PsiSqGeneric.core V D hE h0 τ₀ N s ε hT mu
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiUnitOnOfRescaledPsiUnitOn
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PolDeg

theorem isUnit_res_of_le_basicOpen' {X : Scheme.{0}} {U V : X.Opens} (f : Γ(X, U)) (hVU : V ≤ U)
    (h : V ≤ X.basicOpen f) : IsUnit ((X.presheaf.map (homOfLE hVU).op).hom f) := by
  have hu := (X.toRingedSpace.isUnit_res_basicOpen f).map (X.presheaf.map (homOfLE h).op).hom
  have e : X.presheaf.map (homOfLE hVU).op =
      X.presheaf.map (homOfLE (X.basicOpen_le f)).op ≫ X.presheaf.map (homOfLE h).op := by
    rw [← Functor.map_comp]; rfl
  rw [e]
  exact hu

theorem psiUnitOn_of_rescale : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (g : D.X → (FractionRing R)ˣ) (y : D.X) (U : Set (Sp R)) (a b : R), (g y : FractionRing R) * algebraMap R (FractionRing R) a = algebraMap R (FractionRing R) b → (∀ p ∈ U, a ∉ (p : PrimeSpectrum R).asIdeal ∧ b ∉ (p : PrimeSpectrum R).asIdeal) → PsiUnitOn (GlobalTheory.PolDeg.rescale D g) y U → PsiUnitOn D y U := by
  intro R _ _ D g y U a b hab hU hR j V hV hVU hj h
  obtain ⟨r₀, hr₀u, hr₀⟩ := hR j V hV hVU hj h
  have hle : (V : (Sp R).Opens) ≤ ⊤ := le_top
  have hVa : V ≤ (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a) := by
    intro x hx
    show x ∈ ((Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a) : Set (Sp R))
    rw [basicOpen_eq_of_affine]
    exact (hU x (hVU hx)).1
  have hVb : V ≤ (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv b) := by
    intro x hx
    show x ∈ ((Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv b) : Set (Sp R))
    rw [basicOpen_eq_of_affine]
    exact (hU x (hVU hx)).2
  obtain ⟨Au, hAu⟩ := isUnit_res_of_le_basicOpen' _ hle hVa
  obtain ⟨Bu, hBu⟩ := isUnit_res_of_le_basicOpen' _ hle hVb
  refine ⟨Au.val * r₀ * (Bu⁻¹ : Γ(Sp R, V)ˣ).val, ((Au.isUnit.mul hr₀u).mul (Bu⁻¹).isUnit), ?_⟩
  set K := FractionRing R
  set c : K →+* Γ((TK R).left, jK R ⁻¹ᵁ V) :=
    ((TK R).left.presheaf.map (homOfLE (le_top : jK R ⁻¹ᵁ V ≤ ⊤)).op).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
    with hc
  have hnat : ∀ x : R, ((jK R).app V).hom ((Sp R).presheaf.map (homOfLE hle).op |>.hom
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom x)) = c (algebraMap R K x) := by
    intro x
    have e := congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom x))
      ((jK R).naturality (homOfLE hle).op)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
    rw [e]
    have e2 := congrArg (fun q => q.hom x) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R K)))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e2
    rw [hc, RingHom.comp_apply, e2]
    rfl
  have hA : ((jK R).app V).hom Au.val = c (algebraMap R K a) := by rw [hAu]; exact hnat a
  have hB : ((jK R).app V).hom Bu.val = c (algebraMap R K b) := by rw [hBu]; exact hnat b
  have hG : ∀ (W : (TK R).left.Opens) (h₁ : jK R ⁻¹ᵁ V ≤ W) (h₂ : W ≤ ⊤), ((TK R).left.presheaf.map (homOfLE h₁).op).hom (res h₂ (unitOn (g y))).val = c (g y) := by
    intro W h₁ h₂
    show ((TK R).left.presheaf.map (homOfLE h₁).op).hom (((TK R).left.presheaf.map (homOfLE h₂).op).hom (unitOn (g y)).val) = _
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl
  have hBB : ((jK R).app V).hom Bu.val * ((jK R).app V).hom (Bu⁻¹ : Γ(Sp R, V)ˣ).val = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have hab' : c (algebraMap R K a) * c (g y) = c (algebraMap R K b) := by
    rw [← map_mul, _root_.mul_comm, hab]
  rw [map_mul, map_mul, hr₀]
  show _ * (((TK R).left.presheaf.map (homOfLE h).op).hom (_ * _)) * _ = _
  erw [map_mul]
  rw [hG, hA]
  rw [← hB] at hab'
  rw [← _root_.mul_assoc, hab', _root_.mul_right_comm, hBB, _root_.one_mul]

end GlobalTheory.PolDeg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiUnitOnUnivOfPullbackGenerating
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PullGenAll

theorem pullgen : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R') (D : DegPre R) (D' : DegPre R'), IsPullDeg φ D D' → (∀ χ, PsiUnitOn D χ Set.univ) → ∀ x, PsiUnitOn D' x Set.univ := by
  intro R R' _ _ _ _ φ D D' hD h x
  choose t ht H using fun χ => (GlobalTheory.ArcPull.psiUnitOn_univ_iff D χ).1 (h χ)
  have hpsi : ∀ χ, hD.psiW.psi χ = LB.pullGen D.P.L _ _ (t χ) hD.W.ι := by
    intro χ
    rw [GlobalTheory.GtRestrictCompare.psiOn_unique hD.psiW
      ⟨fun χ => LB.pullGen D.P.L _ _ (t χ) hD.W.ι,
        fun χ => ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ _ (ht χ) _,
        fun χ => corr_of_val D.P.isLB fun y J hJ => by
          refine (val_pull hJ _ _ _).trans ((val_pull hJ (t χ) _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm))
          rw [← val_corr hJ (H χ), val_pull hJ, Category.assoc, Category.assoc, morphismRestrict_ι]⟩]
  obtain ⟨a, ha, va⟩ := GlobalTheory.ArcPull.exists_down_om hD.w_gen D.P.isLB D'.P.isLB (Y' := Sp R') (K := PUnit)
    (φ' := fun _ => (D'.c x).left) (spMap φ) (fun _ => hD.c_pr x) (t (hD.xe x)) (ht _)
  refine (GlobalTheory.ArcPull.psiUnitOn_univ_iff D' x).2 ⟨a, ha, corr_of_val D'.P.isLB fun y J' hJ' => ?_⟩
  obtain ⟨J, hJ⟩ := DegPull.exists_good' D.P.isLB y
  have c : val (hD.psiW.psi (hD.xe x)) (𝟙 _ ≫ hD.g) y J = val (t (hD.xe x)) ((𝟙 _ ≫ jK R') ≫ spMap φ) y J := by
    rw [hpsi]
    refine (val_pull hJ (t (hD.xe x)) _ _).trans ?_
    have q : (𝟙 _ ≫ hD.g) ≫ hD.W.ι = (𝟙 _ ≫ jK R') ≫ spMap φ := by
      rw [Category.assoc, hD.g_comm, Category.assoc]
      rfl
    exact congrArg (fun q => val (t (hD.xe x)) q y J) q
  have e := ((GlobalTheory.PsiEvenPull.psi_pull hD x (𝟙 _) y hJ hJ').symm.trans c).trans
    (va _ (𝟙 _ ≫ jK R') y J J' hJ hJ')
  rw [Fintype.prod_unique, zpow_neg_one, Category.assoc] at e
  exact (val_pull hJ' _ _ _).trans (mul_left_cancel e).symm

end GlobalTheory.PullGenAll
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiUnitOnUnivOfPullbackReadTop
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PullTopUnit
open GlobalTheory.ArcPull
open GlobalTheory.PsiEvenPull (proj)

theorem psiUnitOn_pull_top {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'}
    {D : DegPre R} {D' : DegPre R'} (hD : IsPullDeg φ D D') (hW : hD.W = ⊤) (x : D'.X) :
    PsiUnitOn D' x Set.univ := by
  have hI : IsIso hD.W.ι := by rw [hW, ← Scheme.topIso_hom]; infer_instance
  let h : Sp R' ⟶ (TW hD.W).left := specOf φ ≫ inv hD.W.ι
  have hh : h ≫ hD.W.ι = specOf φ := by simp [h]
  have hg : hD.g = jK R' ≫ h := by
    rw [← cancel_mono hD.W.ι, hD.g_comm, Category.assoc, hh]
  have sq : (D'.c x).left ≫ proj hD = h ≫ (toUnit (TW hD.W) ≫ D.c (hD.xe x)).left := by
    rw [hD.c_pr x, ← hh, Category.assoc]; rfl
  obtain ⟨a, ha, va⟩ := exists_down_om hD.w_gen D.P.isLB D'.P.isLB (Y' := Sp R') (K := PUnit)
    (φ' := fun _ => (D'.c x).left) h (fun _ => sq) (hD.psiW.psi (hD.xe x)) (hD.psiW.psi_gen _)
  refine (psiUnitOn_univ_iff D' x).2 ⟨a, ha, corr_of_val D'.P.isLB fun y J' hJ' => ?_⟩
  obtain ⟨J, hJ⟩ := DegPull.exists_good' D.P.isLB y
  have e₁ := PsiEvenPull.psi_pull hD x (𝟙 _) y hJ hJ'
  have e₂ := va _ (𝟙 _ ≫ jK R') y J J' hJ hJ'
  rw [Fintype.prod_unique, zpow_neg_one, Category.assoc (𝟙 _) (jK R') h, ← hg] at e₂
  have e := e₁.symm.trans e₂
  exact (val_pull hJ' _ _ _).trans (mul_left_cancel e).symm

end GlobalTheory.PullTopUnit
end

