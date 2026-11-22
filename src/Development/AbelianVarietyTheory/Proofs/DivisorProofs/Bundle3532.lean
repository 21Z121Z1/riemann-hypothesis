import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3511
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3512
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3485
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3448
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3381
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3513
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0082
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3181
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3066
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2925
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3094
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3501
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2968
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2948
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0155
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0143
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSinglePolarisationGeneratorAllTraits
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcGenericPointDescendsToPowerSeries
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0117
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2496
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0160
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaCoordinatesExistUniqueSeparatePoints
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValuationThetaRatioEqBilinear
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0052
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0533
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0218
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0817
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0106
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0084
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTermsSeparationAlgebraicallyClosed

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionShimuraObjectAbelianSchStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothOfRelativeDimension_shimuraObject_abelianScheme : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) (l : Geo.Tor.Level H) {S : Scheme.{0}} (s : S ⟶ Sp (KA l)) (o : Obj D l (baseKA l) s), SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (D.p + D.q)) o.t.G.hom := by
  first | exact @GlobalTheory.UObjDim.smoothOfRelativeDimension_obj | exact GlobalTheory.UObjDim.smoothOfRelativeDimension_obj | (intros; apply GlobalTheory.UObjDim.smoothOfRelativeDimension_obj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkValueClosedPointDefinedOverSubfieldStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stalkValue_closedPoint_definedOver_subfield : ∀ (X : Scheme.{0}) (R : Type) [CommRing R] [IsLocalRing R] (ξ₁ : Sp R ⟶ X) (K : Type) [Field K] (ev₁ : R →+* K) (k₀ : Subfield K), (∀ p, (spMap ev₁ ≫ ξ₁) p = ξ₁ (closedPoint R)) → GlobalTheory.UChart.DefOver k₀ (spMap ev₁ ≫ ξ₁) → ∀ h ∈ (Scheme.stalkClosedPointTo ξ₁).hom.range, ev₁ h ∈ k₀ ∧ (h ∈ maximalIdeal R → ev₁ h = 0) := by
  first | exact @GlobalTheory.USep.stalkVal_closedPoint | exact GlobalTheory.USep.stalkVal_closedPoint | (intros; apply GlobalTheory.USep.stalkVal_closedPoint <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonCharacterGroupOfGoodReductionTraitStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subsingleton_characterGroup_of_goodReduction_trait : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (Y : RatModel X₁.o₁ X₁.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X₁.S.J) (out : ZHOut X₁.ρ Y U₀ EE), X₁.S.admitted Y U₀ → ∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ Y.Z), Set.range ξ ⊆ (U₀ : Set Y.Z) → (∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ ξ ∧ X₁.Lies (ξ₀ ≫ out.u₀) T.y) → Subsingleton T.P.D.toPre.X := by
  first | exact @GlobalTheory.UPoinc.GoodRedU.subsingleton_lattice_of_range_subset | exact GlobalTheory.UPoinc.GoodRedU.subsingleton_lattice_of_range_subset | (intros; apply GlobalTheory.UPoinc.GoodRedU.subsingleton_lattice_of_range_subset <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymbolEntriesRegularAffineOpenStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symbol_entries_regular_affineOpen : ∀ (K : Type) [Field K] [CharZero K] (P₀ : Out.PolAV (Sp K)) (n : ℕ) (v : Module.Basis (Fin n) K (TanM (𝟙 (Sp K)) P₀.A)) (dd : Fin n → Fld P₀.A.left), (∀ a, IsInv P₀.A (v a) (dd a)) → ∀ (F : Type) [Field F] (ψ : K →+* F) (ξ : Sp F ⟶ P₀.A.left), ξ ≫ P₀.A.hom = spMap ψ → (∀ O (f : Γ(P₀.A.left, O)), ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O f = 0 → f = 0) → ∀ (δ : Fin n → Derivation ℤ F F), (∀ a O f, ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O (dd a O f) = δ a (valR ξ O f)) → ∀ (Λ : Matrix (Fin n) (Fin n) F) (W : P₀.A.left.Opens), IsAffineOpen W → ⊤ ≤ ξ ⁻¹ᵁ W → (∀ f f' : Γ(P₀.A.left, W), ∃ h : Γ(P₀.A.left, W), valR ξ _ h = ∑ a, ∑ e, Λ a e * δ a (valR ξ _ f) * δ e (valR ξ _ f')) → ∀ a e, ∃ h : Γ(P₀.A.left, W), valR ξ W h = Λ a e := by
  first | exact @GlobalTheory.Heat.SymReg.entry_regular | exact GlobalTheory.Heat.SymReg.entry_regular | (intros; apply GlobalTheory.Heat.SymReg.entry_regular <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentVectorEqZeroOfLogDerivCoboundaryStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangentVector_eq_zero_of_logDeriv_coboundary : ∀ (R : Type) [CommRing R] [IsLocalRing R] (P : PolAV (Sp R)) (w : TanM (𝟙 (Sp R)) P.A) (δ : Fld P.A.left), IsInv P.A w δ → ∀ (K : Type) (V : K → P.A.left.Opens) (jk : K → P.L.ι), ⨆ k, V k = ⊤ → (∀ k, V k ≤ P.L.U (jk k)) → ∀ (b : ∀ k, Γ(P.A.left, V k)), (∀ k k', rsT (b k') (V k ⊓ V k') - rsT (b k) (V k ⊓ V k') = dlg P.A (𝟙 _) P.L δ (jk k) (jk k') (V k ⊓ V k')) → w = 0 := by
  first | exact @GlobalTheory.LieRigid.lie_inj | exact GlobalTheory.LieRigid.lie_inj | (intros; apply GlobalTheory.LieRigid.lie_inj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoLogDetGramChangeSemiPositiveMetricStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_logDet_gram_change_semiPositive_metric : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → GenSmooth p D → ∀ (P : Pair p), P.L.SemiPos D → ∀ (ω : ∀ σ, VolDens p σ D) (r : ℕ → ℕ) (f : ∀ m, Fin (r m) → X.functionField), (∀ (m : ℕ) i, f m i ∈ P.H m 1) → (∀ m, LinearIndependent ℤ (f m)) → Tendsto (fun m : ℕ => (r m : ℝ) / (m : ℝ) ^ D) atTop (𝓝 (gdeg P.L D / D.factorial)) → ∀ (u : SmFn p) (a a' : ℝ), (up P.L u).SemiPos D → P.L.IsSelfInter a → (up P.L u).IsSelfInter a' → Tendsto (fun m : ℕ => (Real.log (gram (fun σ => (ω σ).meas) (vals P m 1 (f m))).det.re - Real.log (gram (fun σ => (ω σ).meas) (vals (upperParabolic P u) m 1 (f m))).det.re) / (m : ℝ) ^ (D + 1)) atTop (𝓝 (2 * (a' - a) / (D + 1).factorial)) := by
  first | exact @GlobalTheory.HSAmpDet.tendsto_logDet_gram_sub | exact GlobalTheory.HSAmpDet.tendsto_logDet_gram_sub | (intros; apply GlobalTheory.HSAmpDet.tendsto_logDet_gram_sub <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsTwoLevelsSameScaleAtTrait
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMin.CmpTrait

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

theorem spMap_id' (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 _ := by
  rw [← Spec.map_id]; rfl

theorem comp_pow'' {S : Scheme.{0}} {A T T₀ : Over S} [GrpObj A] (ρ : T₀ ⟶ T) (x : T ⟶ A) (n : ℕ) :
    ρ ≫ x ^ n = (ρ ≫ x) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, MonObj.comp_one]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]

theorem card_le_of_thList {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left} {ρ : LB.Gen (L.pull (eSec G))}
    {m : ℕ} {K : Type} [Field K] [IsAlgClosed K] {x : Sp K ⟶ S} {θ θ' : SecAt G L x} {N N' : ℕ}
    {pt : Fin N → (Over.mk x ⟶ G)} {pt' : Fin N' → (Over.mk x ⟶ G)} {c : Fin N → K} {c' : Fin N' → K}
    (h : ThList G L ρ m x θ pt c) (h' : ThList G L ρ m x θ' pt' c') : N ≤ N' := by
  let e : Over.mk (spMap (RingHom.id K) ≫ x) ⟶ Over.mk x := Over.homMk (spMap (RingHom.id K)) rfl
  have key : ∀ a, ∃ b, pt a = pt' b := fun a => by
    have hp : (e ≫ pt a) ^ (m ^ 2) = 1 := by
      rw [← comp_pow'', (h.2.1 a).1, MonObj.comp_one]
    obtain ⟨b, hb⟩ := h'.2.2 K (RingHom.id K) (e ≫ pt a) hp
    refine ⟨b, Over.OverMorphism.ext ?_⟩
    have hb' : spMap (RingHom.id K) ≫ (pt a).left = spMap (RingHom.id K) ≫ (pt' b).left := hb
    rwa [spMap_id', Category.id_comp, Category.id_comp] at hb'
  choose s hs using key
  have hs' : Function.Injective s := fun a a' he => h.1 ((hs a).trans ((congrArg pt' he).trans (hs a').symm))
  simpa using Fintype.card_le_of_injective s hs'

theorem card_eq_of_thList {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left} {ρ : LB.Gen (L.pull (eSec G))}
    {m : ℕ} {K : Type} [Field K] [IsAlgClosed K] {x : Sp K ⟶ S} {θ θ' : SecAt G L x} {N N' : ℕ}
    {pt : Fin N → (Over.mk x ⟶ G)} {pt' : Fin N' → (Over.mk x ⟶ G)} {c : Fin N → K} {c' : Fin N' → K}
    (h : ThList G L ρ m x θ pt c) (h' : ThList G L ρ m x θ' pt' c') : N = N' :=
  le_antisymm (card_le_of_thList h h') (card_le_of_thList h' h)

theorem isGenSec_of_nz {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left} (hL : L.IsLB) {g : ℕ} {K : Type}
    [Field K] {x : Sp K ⟶ S} (hP : PolFib G L g x) {θ : SecAt G L x} (hθ : NZ G L x θ) : IsGenSec G L _ θ := by
  obtain ⟨P, α, -, hp, hw⟩ := hP
  obtain ⟨e, he⟩ := exists_univBasis_of_fibre abelianSchemeLaws_all.2 S (Sp K) G L hL P x α hp hw K (𝟙 _) x
    (Category.id_comp x)
  have h0 : spMap (RingHom.id K) ≫ x = x := by rw [spMap_id', Category.id_comp]
  obtain ⟨a, ha⟩ := he.ex (RingHom.id K) h0 (SecM.ofSec G θ)
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_smul] at ha
    obtain ⟨q, -, hq⟩ := hθ
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hq
    have e0 : θ.f j = 0 := congrArg (fun s => s.1 j) ha
    rw [e0, Scheme.basicOpen_zero] at hj
    exact hj
  refine (isGenSec_iff θ).2 fun s => ?_
  obtain ⟨b, hb⟩ := he.ex (RingHom.id K) h0 s
  refine ⟨fnR x (b * a⁻¹), ?_⟩
  rw [hb, ha, smul_smul, ← map_mul, _root_.mul_assoc, inv_mul_cancel₀ ha0, _root_.mul_one]

theorem prim_of_finite {V V' K : Type} [CommRing V] [CommRing V'] [Field K] (f : V →+* V') (i : V' →+* K) {J : Type}
    (c : J → K) (hf : f.Finite) (h : Prim i c) : Prim (i.comp f) c := by
  letI := f.toAlgebra
  letI := i.toAlgebra
  letI := (i.comp f).toAlgebra
  haveI : IsScalarTower V V' K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Module.Finite V V' := hf
  haveI : Algebra.IsIntegral V V' := Algebra.IsIntegral.of_finite V V'
  have key : ∀ z : K, i.IsIntegralElem z → (i.comp f).IsIntegralElem z := fun z hz =>
    isIntegral_trans (R := V) (A := V') z hz
  obtain ⟨h1, a, ha, ha'⟩ := h
  exact ⟨fun b => key _ (h1 b), a, ha, key _ ha'⟩

theorem exists_ext {V V' : Type} [CommRing V] [IsDomain V] [CommRing V'] [IsDomain V'] (f : V →+* V')
    (fK : FractionRing V →+* FractionRing V') {K : Type} [Field K] [IsAlgClosed K] (io : FractionRing V →+* K)
    (hf : f.Finite) (hfK : ∀ a, fK (algebraMap V _ a) = algebraMap V' _ (f a)) :
    ∃ io' : FractionRing V' →+* K, io'.comp fK = io := by
  letI := fK.toAlgebra
  letI := io.toAlgebra
  letI := f.toAlgebra
  haveI : Module.Finite V V' := hf
  haveI : Algebra.IsIntegral V V' := Algebra.IsIntegral.of_finite V V'
  have hint : ∀ b : V', IsAlgebraic (FractionRing V) (algebraMap V' (FractionRing V') b) := fun b => by
    obtain ⟨p, hp, hp0⟩ := Algebra.IsIntegral.isIntegral (R := V) b
    refine (show IsIntegral (FractionRing V) (algebraMap V' (FractionRing V') b) from
      ⟨p.map (algebraMap V (FractionRing V)), hp.map _, ?_⟩).isAlgebraic
    rw [Polynomial.eval₂_map]
    have e : (algebraMap (FractionRing V) (FractionRing V')).comp (algebraMap V (FractionRing V)) =
        (algebraMap V' (FractionRing V')).comp (algebraMap V V') := RingHom.ext hfK
    rw [e, ← Polynomial.hom_eval₂, hp0, map_zero]
  haveI : Algebra.IsAlgebraic (FractionRing V) (FractionRing V') := ⟨fun z => by
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := V') z
    exact (hint a).mul (hint b).inv⟩
  let φ : FractionRing V' →ₐ[FractionRing V] K := IsAlgClosed.lift
  exact ⟨φ.toRingHom, RingHom.ext fun a => φ.commutes a⟩

theorem prim_comp {V K : Type} [CommRing V] [Field K] {i : V →+* K} {J J' : Type} {c : J → K} (h : Prim i c)
    (s : J' → J) (hs : Function.Surjective s) : Prim i (c ∘ s) := by
  obtain ⟨h1, a, ha, ha'⟩ := h
  obtain ⟨b, rfl⟩ := hs a
  exact ⟨fun b => h1 _, b, ha, ha'⟩

theorem cmp_trait : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (y : Sp (FractionRing V) ⟶ Xo.XF c) (K : Type) [Field K] [IsAlgClosed K] (io : FractionRing V →+* K) (m m' N N' : ℕ) (d : Fin N → K) (d' : Fin N' → K), Odd m → 3 ≤ m → IsUnit (m : V) → Odd m' → 3 ≤ m' → IsUnit (m' : V) → HasTh₂ Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig m m' (spMap io ≫ y ≫ pullback.fst _ _) d d' → ∃ a : K, a ≠ 0 ∧ Prim (io.comp (algebraMap V (FractionRing V))) (fun b => d b / a) ∧ Prim (io.comp (algebraMap V (FractionRing V))) (fun b => d' b / a) := by
  intro E _ _ _ H Dw l Xo c V _ _ _ hV y K _ _ io m m' N N' d d' hmo hm3 hmu hmo' hm3' hmu' hd
  have hbase : GlobalTheory.Mum.Base V := ⟨ArcPointDescent.admissibleBase_maximalIdeal_completeDVR hV, hV.2.2⟩
  obtain ⟨T, f, fK, -, -, hff, hfK, hTy⟩ := GlobalTheory.T.exists_unitaryTrait_through_moduliGenericPoint E H Dw l Xo c V hbase hV.1 y
  obtain ⟨io', hio'⟩ := exists_ext f fK io hff hfK
  set i : T.V →+* K := io'.comp (algebraMap T.V (FractionRing T.V)) with hi
  have hinj : Function.Injective i := io'.injective.comp (IsFractionRing.injective T.V (FractionRing T.V))
  haveI : IsDiscreteValuationRing T.V := T.cdvr.1
  obtain ⟨tK, ⟨mK⟩, ⟨mx⟩⟩ := T.gen
  obtain ⟨m0, -⟩ := ObjMaps.exists_sab_id T.t
  have hpol : GlobalTheory.LN.PolAt T.t (jK T.V) := UnifAfterExt.polAt_of_sabMap m0 mK mx Xo.univ.proper Xo.univ.ample
    Xo.univ.ktriv (jK T.V) (𝟙 _) (by rw [Category.comp_id, Category.id_comp])
  obtain ⟨σ, hσ⟩ := exists_nz_of_polAt abelianSchemeLaws_all.1 abelianSchemeLaws_all.2 E H (Sp T.V) T.t T.V (𝟙 _) T.t m0
    hpol
  have h0 : spMap (RingHom.id T.V) ≫ 𝟙 (Sp T.V) = 𝟙 _ := by rw [Category.comp_id, spMap_id']
  have hσσ : VVRank.pullS T.t.G _ (Over.homMk (spMap (RingHom.id T.V)) h0 : Over.mk (𝟙 (Sp T.V)) ⟶ Over.mk (𝟙 _)) σ = σ := by
    have e : (Over.homMk (spMap (RingHom.id T.V)) h0 : Over.mk (𝟙 (Sp T.V)) ⟶ Over.mk (𝟙 _)) = 𝟙 _ :=
      Over.OverMorphism.ext (spMap_id' T.V)
    rw [e]
    have := VVRank.pullM_id T.t.G T.t.PP.isLB ((1 : ℕ) : ℤ) (SecM.ofSec T.t.G σ)
    rw [VVRank.pullM_ofSec] at this
    exact congrArg (SecM.toSec T.t.G) this
  have hnz : NZ T.t.G T.t.PP.L (𝟙 _) σ := by
    have := hσ T.V (RingHom.id _) _ h0
    rwa [hσσ] at this
  have hmT : ∀ {k : ℕ}, IsUnit (k : V) → IsUnit (k : T.V) := fun h => by simpa using h.map f
  have hmK : ∀ {k : ℕ}, IsUnit (k : V) → (k : K) ≠ 0 := fun h => by
    have := h.map (io.comp (algebraMap V (FractionRing V))); simpa using this.ne_zero
  set x₁ : Sp K ⟶ Sp T.V := spMap i ≫ 𝟙 (Sp T.V) with hx₁
  have ex₁ : spMap io' ≫ jK T.V = x₁ := by rw [hx₁, Category.comp_id, hi, spMap_comp']
  set x : Sp K ⟶ Xo.X := spMap io ≫ y ≫ pullback.fst _ _ with hx
  have ex : spMap io' ≫ T.y ≫ pullback.fst _ _ = x := by rw [hx, hTy, ← hio', spMap_comp']; simp only [Category.assoc]
  set g := Module.finrank ℚ E / 2 * (Dw.p + Dw.q) with hg
  have hPx : PolFib Xo.univ.t.G Xo.univ.t.PP.L g x := GlobalTheory.T.universalTriple_fibre_principallyPolarised_dimension E H Dw l Xo c K x
  obtain ⟨wK, hwK, -⟩ := mK.lin
  obtain ⟨wx, hwx, -⟩ := mx.lin
  have hPK : PolFib tK.G tK.PP.L g (spMap io') :=
    ((GlobalTheory.T.principallyPolarisedFibre_iff_of_grpPullback _ _ _ _ _ _ _ _ Xo.univ.t.PP.isLB tK.PP.isLB mx.cart ⟨wx, hwx⟩ g K (spMap io')).1).2 (ex ▸ hPx)
  have hP₁ : PolFib T.t.G T.t.PP.L g x₁ :=
    ex₁ ▸ ((GlobalTheory.T.principallyPolarisedFibre_iff_of_grpPullback _ _ _ _ _ _ _ _ T.t.PP.isLB tK.PP.isLB mK.cart ⟨wK, hwK⟩ g K (spMap io')).1).1 hPK
  set θ := SecAt.pull T.t.G T.t.PP.L σ i with hθdef
  have hθnz : NZ T.t.G T.t.PP.L x₁ θ := hσ K i x₁ rfl
  have hθ : IsGenSec T.t.G T.t.PP.L _ θ := isGenSec_of_nz T.t.PP.isLB hP₁ hθnz
  obtain ⟨pt, cc, hc⟩ := GlobalTheory.T.exists_thetaConstantList_algClosed _ T.t.G T.t.PP.L T.t.PP.rig T.t.PP.isLB T.t.PP.rigGen g m _ K x₁ θ hmo (hmK hmu)
    rfl hP₁
  obtain ⟨pt', cc', hc'⟩ := GlobalTheory.T.exists_thetaConstantList_algClosed _ T.t.G T.t.PP.L T.t.PP.rig T.t.PP.isLB T.t.PP.rigGen g m' _ K x₁ θ hmo'
    (hmK hmu') rfl hP₁
  have hpr : Prim i cc := GlobalTheory.T.thetaConstants_primitive_at_uniformisedTrait E H (Sp T.V) T.t T.V T.cdvr (𝟙 _) T.t ⟨m0⟩ ⟨T.P⟩ σ hnz m _ hmo hm3 (hmT hmu)
    K i pt cc hinj hc
  have hpr' : Prim i cc' := GlobalTheory.T.thetaConstants_primitive_at_uniformisedTrait E H (Sp T.V) T.t T.V T.cdvr (𝟙 _) T.t ⟨m0⟩ ⟨T.P⟩ σ hnz m' _ hmo' hm3'
    (hmT hmu') K i pt' cc' hinj hc'
  have h₁ : HasTh₂ T.t.G T.t.PP.L T.t.PP.rig m m' x₁ cc cc' := ⟨θ, pt, pt', hθ, hc, hc'⟩
  have hK : HasTh₂ tK.G tK.PP.L tK.PP.rig m m' (spMap io') cc cc' :=
    (GlobalTheory.T.hasThetaConstantsTwoLevels_move_cartesian _ T.t.G T.t.PP.L T.t.PP.rig T.t.PP.isLB T.t.PP.rigGen _ tK.G tK.PP.L tK.PP.rig (jK T.V) mK.φ
      tK.PP.isLB tK.PP.rigGen mK.cart ⟨wK, hwK⟩ m m' _ _ K (spMap io') cc cc').2 (ex₁ ▸ h₁)
  have hX : HasTh₂ Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig m m' x cc cc' :=
    ex ▸ (GlobalTheory.T.hasThetaConstantsTwoLevels_move_cartesian _ Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig Xo.univ.t.PP.isLB Xo.univ.t.PP.rigGen _ tK.G
      tK.PP.L tK.PP.rig (T.y ≫ pullback.fst _ _) mx.φ tK.PP.isLB tK.PP.rigGen mx.cart ⟨wx, hwx⟩ m m' _ _ K (spMap io')
      cc cc').1 hK
  have eN : N = m ^ (4 * g) := by
    obtain ⟨_, _, _, _, hd1, -⟩ := hd
    obtain ⟨_, _, _, _, hc1, -⟩ := hX
    exact card_eq_of_thList hd1 hc1
  have eN' : N' = m' ^ (4 * g) := by
    obtain ⟨_, _, _, _, -, hd2⟩ := hd
    obtain ⟨_, _, _, _, -, hc2⟩ := hX
    exact card_eq_of_thList hd2 hc2
  subst eN eN'
  obtain ⟨a, s, s', ha, hds, hds'⟩ := (GlobalTheory.T.thetaConstantLists_unique_up_to_perm_scalar _ Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig Xo.univ.t.PP.isLB
    Xo.univ.t.PP.rigGen g m m' _ _ K x hmo (hmK hmu) hmo' (hmK hmu') hPx).2 cc d cc' d' hX hd
  have ei : i.comp f = io.comp (algebraMap V (FractionRing V)) := by
    ext v
    simp only [hi, RingHom.comp_apply, ← hfK, ← hio']
  have e1 : (fun b => d b / a) = cc ∘ s := funext fun b => by
    rw [hds b, Function.comp_apply, mul_div_cancel_left₀ _ ha]
  have e2 : (fun b => d' b / a) = cc' ∘ s' := funext fun b => by
    rw [hds' b, Function.comp_apply, mul_div_cancel_left₀ _ ha]
  refine ⟨a, ha, ?_, ?_⟩
  · rw [e1, ← ei]
    exact prim_of_finite f i _ hff (prim_comp hpr s s.surjective)
  · rw [e2, ← ei]
    exact prim_of_finite f i _ hff (prim_comp hpr' s' s'.surjective)

end GlobalTheory.UMin.CmpTrait
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFamilyCoefficientIntegralTorusPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.Poinc.Sep.Frames GlobalTheory.UT.CoefBasic
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaFamily_coefficient_integral_torusPoint : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V)
    (θ : SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)))
    (lam : FractionRing V) (th : Fam D (FractionRing V) 1),
    famProj D (FractionRing V) 1 0 th = lam • termF D (FractionRing V) 1 0 θ →
    (∀ (Z : Scheme.{0}) (r : Z ⟶ (TK V).left) (z : Z) J, Good D.P.L z J →
      val (D.psi 0) r z J * val D.rigK r z J = 1) →
    ∀ (χ : D.X) (g : GtPtF D (FractionRing V)) (b : 𝟙_ (Over (Sp V)) ⟶ D.P.A), g.b = toUnit _ ≫ b →
    ∀ (w : Frm D (FractionRing V) 1 g.b) (x : FractionRing V), IsCoef 1 g w χ (th.s χ) x →
    ∀ z J, Good D.P.L z J →
      cst (FractionRing V) z x = cst (FractionRing V) z lam *
        (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (D.psi χ) (jFK (R := V) (FractionRing V)) z J)).val *
        sval (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)))
          ((toUnit (TF (R := V) (FractionRing V))).left ≫ (b * D.c χ).left) z J *
        (val (g.s χ) (𝟙 _) z J).val * (val w (𝟙 _) z J).val := by
  first | exact @GlobalTheory.UT.CoefInt.coef_int | exact GlobalTheory.UT.CoefInt.coef_int | (intros; apply GlobalTheory.UT.CoefInt.coef_int <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFamilyTermZeroIntegralTorusPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.FieldBaseChange GlobalTheory.UT
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.Poinc.Sep.Frames GlobalTheory.UT.CoefBasic
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaFamily_term_zero_integral_torusPoint : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (θ : SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))), (∀ (R' : Type) [CommRing R'] (f : V →+* R') θ', IsPullSecLC D.P.L (D.famφB 0) (DegPre.famε 1) (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left θ θ' → ThetaOne.OneBasisAt D f θ') → ∀ (th : Fam D (FractionRing V) 1), ∃ lam : FractionRing V, ∀ (g : GtPtF D (FractionRing V)) (b : 𝟙_ (Over (Sp V)) ⟶ D.P.A), g.b = toUnit _ ≫ b → ∀ (w : Frm D (FractionRing V) 1 g.b) (x : FractionRing V), IsCoef 1 g w 0 (th.s 0) x → ∀ z J, Good D.P.L z J → cst (FractionRing V) z x * (rigV D (TF (R := V) (FractionRing V)).hom z J).val = cst (FractionRing V) z lam * sval (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) ((toUnit (TF (R := V) (FractionRing V))).left ≫ b.left) z J * (val w (𝟙 _) z J).val := by
  first | exact @GlobalTheory.UT.CoefZeroInt.coef_zero_int | exact GlobalTheory.UT.CoefZeroInt.coef_zero_int | (intros; apply GlobalTheory.UT.CoefZeroInt.coef_zero_int <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFibreSectionEqScalarMulIntegralThetaStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.FieldBaseChange GlobalTheory.UT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaFibre_section_eq_scalar_mul_integralTheta : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] (D : DegPre V₁) (θ : SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))), (∀ (R' : Type) [CommRing R'] (f : V₁ →+* R') θ', IsPullSecLC D.P.L (D.famφB 0) (DegPre.famε 1) (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left θ θ' → ThetaOne.OneBasisAt D f θ') → ∀ (K : Type) [Field K] (ev : V₁ →+* K) (th : LB.Sec (LPow D.P.A D.P.L ((1 : ℕ) : ℤ) (Over.mk (spMap ev)))), ∃ Λ : K, ∀ (Z : Scheme) (r : Z ⟶ (Over.mk (spMap ev) ⊗ D.P.A).left) (z : Z) J, Good D.P.L z J → sval th r z J = gs (r ≫ (fst (Over.mk (spMap ev)) D.P.A).left) z ⊤ (GlobalTheory.Ex.fnOf Λ) * sval (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) (r ≫ (snd (Over.mk (spMap ev)) D.P.A).left) z J := by
  first | exact @GlobalTheory.ThetaFibreScalar.thetaFibre_scalar | exact GlobalTheory.ThetaFibreScalar.thetaFibre_scalar | (intros; apply GlobalTheory.ThetaFibreScalar.thetaFibre_scalar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegralFiniteRelation
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ThetaFinRelDef

open GlobalTheory.SquareComm
open scoped ComplexOrder

theorem thetaInt_finRel_eq_zero : GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (M X : HSp D) (A : GlobalTheory.ChainFr.Fr M) (B : GlobalTheory.ChainFr.Fr X) (χ χ' : (AE D)ˣ →* Circle) (ω : GlobalTheory.Grid.WRep M X), GlobalTheory.Grid.IsWeil ψ false M X χ χ' ω → (∀ τ, Formalism.UG.HasSignature (gramAt D M τ) M.rank 0) → ∀ (ν : Measure (GA D M)) (𝓕 : Set (GA D M)), IsHaarFD M ν 𝓕 → ∀ Φ ∈ finRel ω (algF ψ θ false A B), thetaInt ω ν 𝓕 Φ = 0 := by
  intro _ D ψ θ hψ hθ M X A B χ χ' ω hω hsig ν 𝓕 hF
  have hω' : IsWeilDatumO ψ M X χ χ' ω := hω
  have hpd : ∀ τ, (gramAt D M τ).PosDef := fun τ => GlobalTheory.Core.CoefGram.posDef_of_hasSignature _ (hsig τ)
  have hcc : GlobalTheory.Unf.CoCpt M := (GlobalTheory.Unf.CoCptOf.coCpt_of_isAniso_or_posDef D M).2 hpd
  have hth : ∀ Φ ∈ algF ψ θ false A B, IsThetaFunO ψ M X Φ := fun Φ hΦ =>
    GlobalTheory.SquareComm.ThetaLeft.isThetaFunO_of_mem_algF hψ hθ A B hΦ
  have hleft := GlobalTheory.SquareComm.ThetaLeft.main D ψ θ hθ M X A B χ χ' ω hω
  have hsub : ∀ g k (Φ Ψ : WO M X → ℂ), thetaKO ω g k (Φ - Ψ) = thetaKO ω g k Φ - thetaKO ω g k Ψ := by
    intros; simp [thetaKO, map_sub]
  have hadd : ∀ g k (Φ Ψ : WO M X → ℂ), thetaKO ω g k (Φ + Ψ) = thetaKO ω g k Φ + thetaKO ω g k Ψ := by
    intros; simp [thetaKO, map_add]
  have hsmul : ∀ g k (c : ℂ) (Φ : WO M X → ℂ), thetaKO ω g k (c • Φ) = c * thetaKO ω g k Φ := by
    intros; simp [thetaKO, map_smul]
  have hzero : ∀ g k, thetaKO ω g k (0 : WO M X → ℂ) = 0 := by
    intros; simp [thetaKO]
  have hint : ∀ Φ ∈ algF ψ θ false A B, ∀ h, IntegrableOn (fun g => thetaKO ω g h Φ) 𝓕 ν := by
    intro Φ hΦ h
    exact (GlobalTheory.Unf.contAut_rapidDec_bounded_integrable D M hcc _
      ⟨fun γ hγ g => hleft Φ hΦ γ hγ g h, (hω'.om_cont Φ (hth Φ hΦ) 0).comp (Continuous.prodMk_left h)⟩).2.2
      ⟨ν, 𝓕, hF.1, hF.2⟩
  intro Φ hΦ
  suffices key : (∀ h, IntegrableOn (fun g => thetaKO ω g h Φ) 𝓕 ν) ∧ thetaInt ω ν 𝓕 Φ = 0 from key.2
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, -, Ψ, hΨ, rfl⟩ := hx
    have e : ∀ g k, thetaKO ω g k (ω (u, 1) Ψ) = thetaKO ω (g * u) k Ψ := fun g k => by
      unfold thetaKO
      rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
    have tr := fun k => integral_rightTranslate hF (f := fun g => thetaKO ω g k Ψ)
      (fun γ hγ g => hleft Ψ hΨ γ hγ g k) u
    have i1 : ∀ k, IntegrableOn (fun g => thetaKO ω g k (ω (u, 1) Ψ)) 𝓕 ν := fun k => by
      simp only [e]; exact (tr k).1.2 (hint Ψ hΨ k)
    refine ⟨fun k => ?_, ?_⟩
    · simp only [hsub]; exact (i1 k).sub (hint Ψ hΨ k)
    · funext k
      simp only [thetaInt, hsub, Pi.zero_apply]
      rw [integral_sub (i1 k) (hint Ψ hΨ k)]
      simp only [e]
      rw [(tr k).2, sub_self]
  | zero =>
    exact ⟨fun k => by simp only [hzero]; exact integrableOn_zero, by funext k; simp [thetaInt, hzero]⟩
  | add x y _ _ hx hy =>
    refine ⟨fun k => by simp only [hadd]; exact (hx.1 k).add (hy.1 k), ?_⟩
    funext k
    have := integral_add (hx.1 k) (hy.1 k)
    have ex := congrFun hx.2 k
    have ey := congrFun hy.2 k
    simp only [thetaInt, Pi.zero_apply] at ex ey
    simp only [thetaInt, hadd, Pi.zero_apply, this, ex, ey, add_zero]
  | smul c x _ hx =>
    refine ⟨fun k => by simp only [hsmul]; exact (hx.1 k).const_mul c, ?_⟩
    funext k
    have ex := congrFun hx.2 k
    simp only [thetaInt, Pi.zero_apply] at ex
    simp only [thetaInt, hsmul, Pi.zero_apply, integral_const_mul, ex, mul_zero]

end GlobalTheory.ThetaFinRelDef

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTermsSeparationAlgebraicallyClosedStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_terms_separation_algebraically_closed : ∀ (m : ℕ), Odd m → 3 ≤ m → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → IsUnit (m : V₁) → ∀ (D : DegPre V₁) (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V₁) (mo : X → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → GlobalTheory.Poinc.Sep.IsThetaTerms D (m ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (ρ₀ : LB.Gen (D.P.L.pull (eSec D.P.A))), ρ₀.IsGen → ∀ (th : LB.Sec (LPow D.P.A D.P.L ((1 : ℕ) : ℤ) (Over.mk (spMap ev)))), IsGenSec D.P.A D.P.L ((1 : ℕ) : ℤ) th → ∃ (M : ℕ) (lam : K), 1 ≤ M ∧ ∀ (x : Over.mk (spMap ev) ⟶ D.P.A) (τ : LB.Gen (LB.LinComb D.P.L (Y := (Over.mk (spMap ev)).left) (K := Fin 1) (fun _ => x.left) (fun _ => 1))) (c : K), IsTorsFrame D.P ρ₀ (m ^ 2) x τ → IsValueAt D.P.A D.P.L ((1 : ℕ) : ℤ) th x (powFrame D.P.A D.P.L x τ ((1 : ℕ) : ℤ)) (GlobalTheory.Ex.fnOf c) → ∃ (c₀ : C) (ζ : K), ζ ^ M = 1 ∧ c = lam * ζ * ev (u 0 c₀) := by
  first | exact @GlobalTheory.Poinc.Sep.TorsValue.values_in_torsFrames | exact GlobalTheory.Poinc.Sep.TorsValue.values_in_torsFrames | (intros; apply GlobalTheory.Poinc.Sep.TorsValue.values_in_torsFrames <;> assumption)
end

