import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3000
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3431
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3443
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2514
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0618
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3025
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanSectionFlatWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsHorizontalGeneratorOfCharts
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactification
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InjectiveOfSmulMemRange
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3432
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0597
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2530
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2875
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0066
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivPullCompIff
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeTorusCompare
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0469
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SplitsAt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianLocusOpenFamilyOverLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3388

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianLiftingOfFour
section
namespace GlobalTheory.LiftFour

theorem abelianLifting_of_four :
    GlobalTheory.Published.AbelianHodgeDeRham → GlobalTheory.Published.DualAbelianScheme →
      GlobalTheory.Published.PoincareDeRhamDuality → GlobalTheory.Published.AbelianUnobstructed →
      GlobalTheory.Published.AbelianLifting :=
  fun a c d e => GlobalTheory.T.abelianSchemeHomLiftingNilDP_of_hodge_cube_duality_unobstructed a GlobalTheory.T.theoremOfCubeAbelianScheme_over_arbitrary_base c d e

end GlobalTheory.LiftFour
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianLocusPointMemRangeSiegelModuliOpenImmersiStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_locus_point_mem_range_siegelModuli_openImmersion : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (S : Scheme.{0}) [S.IsSeparated] (j : F.X ⟶ S) [IsOpenImmersion j] (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] [CharZero R] (b : cycAway n →+* R) (ξ : Sp R ⟶ S) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (y : Sp (FractionRing R) ⟶ F.X) (A₁ : Over (Sp (FractionRing R))) [GrpObj A₁] (i₁ : A₁.left ⟶ G₁.left) (β : A₁.left ⟶ F.univ.A.left), IsSemiAbelian G₁ → IsGrpPullback A₁ G₁ (jK R) i₁ → IsGrpPullback A₁ F.univ.A y β → y ≫ j = jK R ≫ ξ → ∀ p : Sp R, p ∈ abLocus G₁ → ξ p ∈ Set.range j := by
  first | exact @GlobalTheory.AbChart.mem_range_of_mem_abLocus | exact GlobalTheory.AbChart.mem_range_of_mem_abLocus | (intros; apply GlobalTheory.AbChart.mem_range_of_mem_abLocus <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianPartConstantHeatOperatorSymbolInMaximalIdStatement
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
theorem _root_.GlobalTheory.T.abelian_part_constant_heat_operator_symbol_in_maximal_ideal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r))) → ∃ (B' : Over (Sp (DualNumber k))) (_ : GrpObj B') (π₁ π₂ : B'.left ⟶ P.D.toPre.P.A.left), IsGrpPullback B' P.D.toPre.P.A (spMap ρ) π₁ ∧ IsGrpPullback B' P.D.toPre.P.A (spMap (constHom ρ)) π₂ ∧ (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) := by
  first | exact @GlobalTheory.Heat.AbConstAlong.abelian_part_const | exact GlobalTheory.Heat.AbConstAlong.abelian_part_const | (intros; apply GlobalTheory.Heat.AbConstAlong.abelian_part_const <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianStructureCohomologyStatementStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_structure_cohomology_statement : GlobalTheory.AbCoh.OStr := by
  first | exact @GlobalTheory.AbCoh.oStr | exact GlobalTheory.AbCoh.oStr | (intros; apply GlobalTheory.AbCoh.oStr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveTorsionFamiliesEqualLocusOpen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.TorsEqOpen

theorem exists_open_eqLocus {S X Y : Scheme.{0}} (f : X ⟶ Y) [IsOpenImmersion (pullback.diagonal f)]
    (u v : S ⟶ X) (huv : u ≫ f = v ≫ f) :
    ∃ U : S.Opens, (∀ V : S.Opens, V ≤ U → V.ι ≫ u = V.ι ≫ v) ∧
      ∀ (T : Scheme.{0}) (g : T ⟶ S), g ≫ u = g ≫ v → Set.range g.base ⊆ (U : Set S) := by
  refine ⟨(pullback.lift u v huv) ⁻¹ᵁ (pullback.diagonal f).opensRange, ?_, ?_⟩
  · intro V hV
    have hr : Set.range (V.ι ≫ pullback.lift u v huv).base ⊆ Set.range (pullback.diagonal f).base := by
      rintro _ ⟨p, rfl⟩
      have hp : V.ι.base p ∈ V := by
        have h0 : V.ι.base p ∈ Set.range V.ι.base := ⟨p, rfl⟩
        rwa [Scheme.Opens.range_ι] at h0
      have := hV hp
      simpa using this
    have hl := IsOpenImmersion.lift_fac (pullback.diagonal f) (V.ι ≫ pullback.lift u v huv) hr
    have h1 := congrArg (· ≫ pullback.fst f f) hl
    have h2 := congrArg (· ≫ pullback.snd f f) hl
    simp only [Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd, pullback.lift_fst,
      pullback.lift_snd, Category.comp_id] at h1 h2
    rw [← h1, ← h2]
  · intro T g hg
    rintro _ ⟨p, rfl⟩
    have e : g ≫ pullback.lift u v huv = g ≫ u ≫ pullback.diagonal f := by
      apply pullback.hom_ext
      · simp only [Category.assoc, pullback.lift_fst, pullback.diagonal_fst, Category.comp_id]
      · simp only [Category.assoc, pullback.lift_snd, pullback.diagonal_snd, Category.comp_id, hg]
    have e2 := congrArg (fun h => h.base p) e
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at e2
    show (pullback.lift u v huv).base (g.base p) ∈ (pullback.diagonal f).opensRange
    rw [← SetLike.mem_coe, Scheme.Hom.coe_opensRange]
    exact ⟨_, e2.symm⟩

end GlobalTheory.TorsEqOpen

namespace GlobalTheory.TorsEqOpen

theorem comp_pow_pt {S : Scheme.{0}} {X Y G : Over S} [GrpObj G] (f : X ⟶ Y) (g : Y ⟶ G) (n : ℕ) :
    f ≫ g ^ n = (f ≫ g) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, MonObj.comp_one]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]

theorem eq_of_eq_single {S : Scheme.{0}} {κ : Type} [Fintype κ] [DecidableEq κ] {A Z W : Over S} [GrpObj A] [IsCommMonObj A]
    (x y : (κ → ℤ) → (W ⟶ A)) (hx : ∀ a b, x (a + b) = x a * x b) (hy : ∀ a b, y (a + b) = y a * y b)
    (φ : Z ⟶ W) (hφ : ∀ i, φ ≫ x (Pi.single i 1) = φ ≫ y (Pi.single i 1)) (a : κ → ℤ) :
    φ ≫ x a = φ ≫ y a := by
  let F : (κ → ℤ) →+ Additive (Z ⟶ A) :=
    AddMonoidHom.mk' (fun a => Additive.ofMul (φ ≫ x a)) (fun a b => by
      rw [hx, MonObj.comp_mul]; rfl)
  let G : (κ → ℤ) →+ Additive (Z ⟶ A) :=
    AddMonoidHom.mk' (fun a => Additive.ofMul (φ ≫ y a)) (fun a b => by
      rw [hy, MonObj.comp_mul]; rfl)
  have hFG : F = G := by
    refine AddMonoidHom.functions_ext _ F G fun i k => ?_
    have e : (Pi.single i k : κ → ℤ) = k • Pi.single i 1 := by
      ext j
      by_cases h : j = i
      · subst h; simp
      · simp [Pi.single_apply, h]
    rw [e, map_zsmul, map_zsmul]
    congr 1
    simpa [F, G] using congrArg Additive.ofMul (hφ i)
  exact congrArg Additive.toMul (DFunLike.congr_fun hFG a)

end GlobalTheory.TorsEqOpen

namespace GlobalTheory

theorem torsFamily_eq_isOpen : ∀ (m M : ℕ) (S' : Scheme.{0}) [IsLocallyNoetherian S'] (t : S' ⟶ Sp (cycAway M))
    (A : Over S') [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → 1 ≤ M →
    ∀ (x y : (Fin m ⊕ Fin m → ℤ) → (𝟙_ (Over S') ⟶ A)), (∀ a b, x (a + b) = x a * x b) →
    (∀ a b, y (a + b) = y a * y b) → (∀ a, x a ^ M = 1) → (∀ a, y a ^ M = 1) →
    ∃ U : S'.Opens, (∀ V : S'.Opens, V ≤ U → ∀ a, V.ι ≫ (x a).left = V.ι ≫ (y a).left) ∧
      ∀ (T : Scheme.{0}) (g : T ⟶ S'), (∀ a, g ≫ (x a).left = g ≫ (y a).left) →
        Set.range g.base ⊆ (U : Set S') := by
  intro m M S' _ t A _ _ hA hM x y hx hy hxM hyM
  have hu : IsUnit (M : Γ(S', ⊤)) := by
    have h1 : IsUnit (M : cycAway M) := isUnit_natCast (by omega)
    have h2 := h1.map (Scheme.ΓSpecIso (CommRingCat.of (cycAway M))).inv.hom
    have h3 := h2.map t.appTop.hom
    simpa using h3
  haveI := hA.smooth
  haveI : Etale (𝟙 A ^ M).left := GlobalTheory.GrpTangent.etale_id_pow A hu
  have hpow : ∀ z : 𝟙_ (Over S') ⟶ A, z ^ M = 1 →
      z.left ≫ (𝟙 A ^ M).left = (1 : 𝟙_ (Over S') ⟶ A).left := by
    intro z hz
    rw [← Over.comp_left, TorsEqOpen.comp_pow_pt, Category.comp_id, hz]
  choose U hU1 hU2 using fun i : Fin m ⊕ Fin m =>
    TorsEqOpen.exists_open_eqLocus (S := S') (𝟙 A ^ M).left (x (Pi.single i 1)).left (y (Pi.single i 1)).left
      ((hpow _ (hxM _)).trans (hpow _ (hyM _)).symm)
  refine ⟨⟨⋂ i, (U i : Set S'), isOpen_iInter_of_finite fun i => (U i).2⟩, ?_, ?_⟩
  · intro V hV a
    have hVi : ∀ i, V ≤ U i := fun i => (show (V : Set S') ⊆ U i from
      (show (V : Set S') ⊆ ⋂ i, (U i : Set S') from hV).trans (Set.iInter_subset _ i))
    have key := TorsEqOpen.eq_of_eq_single x y hx hy (toUnit (Over.mk V.ι)) (fun i =>
      Over.OverMorphism.ext (by
        rw [Over.comp_left, Over.comp_left, Over.toUnit_left]
        exact hU1 i V (hVi i))) a
    have := congrArg Over.Hom.left key
    rwa [Over.comp_left, Over.comp_left, Over.toUnit_left] at this
  · intro T g hg
    exact Set.subset_iInter fun i => hU2 i T g (hg _)

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmplePullbackIntersectionDegreePosOfNeZeroStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ample_pullback_intersection_degree_pos_of_ne_zero : ∀ (K : Type) [Field K] (A B : AbVar K) (n : ℕ), A.dim = n + 1 → ∀ (c : Pic A.X.left) (d : Pic B.X.left), IsAmpleCls c → IsAmpleCls d → ∀ f : A ⟶ B, f ≠ 0 → 0 < inter A (Fin.cons (CechPic.pull f.hom.left d) (fun _ : Fin n => c) : Fin (n + 1) → Pic A.X.left) := by
  first | (exact @GlobalTheory.AV.AbVar.inter_pull_ample_pos) | (exact GlobalTheory.AV.AbVar.inter_pull_ample_pos) | (intros; apply GlobalTheory.AV.AbVar.inter_pull_ample_pos  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanSectionFlatWeightStatement
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
open AlgebraicGeometry CategoryTheory GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits ReciprocityTheory.ChartRestriction.G.Semi

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_section_flat_weight : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.CanonicalExtensionRankOne → GlobalTheory.Published.DeRhamCanonicalExtension →
  GlobalTheory.Published.PrismaticDieudonneHodge →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x →
  ∀ (Z : Comp Xo c) (τ : Psi H) (s : ArchSec U x Z (flatWt Dw τ)) (la : HeightOneSpectrum (𝓞 c.F)),
  ∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (_ : IsDiscreteValuationRing O)
    (_ : IsAdicComplete (IsLocalRing.maximalIdeal O) O) (ϖ : O) (_ : Irreducible ϖ) (Zs : Scheme.{0})
    (f : Zs ⟶ Spec (.of O)) (D : LB Zs),
    IsIntegral Zs ∧ (∀ z : Zs, IsIntegrallyClosed (Zs.presheaf.stalk z)) ∧ IsProper f ∧ Flat f ∧ D.IsLB ∧
    (∃ t : (D.pull (reducedSpecialι f)).Gen, t.IsGen) ∧
    ∃ (sig : (D.pull (genericι f)).Gen) (κ : ℝ), sig.IsGen ∧
      ∀ w ∈ htValOn Z la, ∃ (p : ℕ) (_ : Fact p.Prime) (R : Type) (_ : CommRing R) (_ : Algebra R ℂ_[p])
        (φ : O →+* R), (Valued.v : Valuation ℂ_[p] NNReal).Integers R ∧ Function.Injective φ ∧ IsLocalHom φ ∧
        ∃ (ybar : Spec (.of R) ⟶ Zs) (y : Spec (.of ℂ_[p]) ⟶ genericFibre f) (e : (D.pull ybar).Gen)
          (cc : ℂ_[p]ˣ),
          ybar ≫ f = Spec.map (CommRingCat.ofHom φ) ∧
          y ≫ genericι f = Spec.map (CommRingCat.ofHom (algebraMap R ℂ_[p])) ≫ ybar ∧
          e.IsGen ∧ IsCoord f D sig ybar y e cc ∧
          w s.sig = val_vw la p (Valued.v : Valuation ℂ_[p] NNReal) (cc : ℂ_[p]) ∧
          val_vw la p (Valued.v : Valuation ℂ_[p] NNReal) (algebraMap R ℂ_[p] (φ ϖ)) = (κ : EReal) := by
  first | exact @GlobalTheory.FlatModel.exists_model | exact GlobalTheory.FlatModel.exists_model | (intros; apply GlobalTheory.FlatModel.exists_model <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithVarietyReciprocityAtComplexEmbeddingStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arith_variety_reciprocity_at_complex_embedding : GlobalTheory.Published.Principalisation → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp k) (e : ℕ), IsArithVar p (e + 1) → ∀ (σ : k →+* ℂ) (L : Fin e → MLine p σ) (M N : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (t : N.B.Sec) (ht : genericPoint X ∈ nonzeroLocus t), (∀ z : X, Order.coheight z = 1 → z ∈ nonzeroLocus s ∨ z ∈ nonzeroLocus t) → side N L (M.logSec s) (N.logSec t) (divOfSec M.φ.isLB s hs) = side M L (N.logSec t) (M.logSec s) (divOfSec N.φ.isLB t ht) := by
  first | exact @GlobalTheory.MixRec.side_symm | exact GlobalTheory.MixRec.side_symm | (intros; apply GlobalTheory.MixRec.side_symm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticCurveDegreeIndependentOfSectionStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithmetic_curve_degree_independent_of_section : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k), IsAmb q → topologicalKrullDim Y = (0 + 1 : ℕ) → ∀ (N : HermLB q) (L : Fin 0 → HermLB q) (r : N.B.ι → Y.functionFieldˣ) (hr : IsRatSec N.B r) (r' : N.B.ι → Y.functionFieldˣ) (hr' : IsRatSec N.B r'), recVal (fun z => Real.log (Nat.card (Y.residueField z))) L N hr = recVal (fun z => Real.log (Nat.card (Y.residueField z))) L N hr' := by
  first | exact @GlobalTheory.CurveIndep.main | exact GlobalTheory.CurveIndep.main | (intros; apply GlobalTheory.CurveIndep.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BiextensionTrivialOfTranslateDifferenceTrivialStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.biextension_trivial_of_translate_difference_trivial : ∀ {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A →
    ∀ (P : LB (A ⊗ A).left), P.IsLB →
    (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) →
    (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) →
    LBIso P (P.pull (lift (snd A A) (fst A A)).left) →
    ∀ (T : Over S), (∀ c : GlobalTheory.CechPic.Pic T.left, c = 0) →
    ∀ (h₀ : 𝟙_ (Over S) ⟶ A) (h' : T ⟶ A) (m : ℕ), h' ^ 2 = toUnit T ≫ h₀ →
    (∃ t : (Out.translDiff A (P.pull (lift (𝟙 A) (𝟙 A)).left) (h' ^ m)).Gen, t.IsGen) →
    ∃ t : (((GlobalTheory.UPel.HT.Hecke.lbPow P m).pull (lift (toUnit A ≫ h₀) (𝟙 A)).left).pull (fst A T).left).Gen, t.IsGen := by
  first | (exact @GlobalTheory.PicBilin.triv_pow_of_translDiff) | (exact GlobalTheory.PicBilin.triv_pow_of_translDiff) | (intros; apply GlobalTheory.PicBilin.triv_pow_of_translDiff  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalSectionModificationWeightStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.canonical_section_modification_weight : GlobalTheory.CovTop.Hypotheses₂ → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed Xo c → ∀ (M : Modif (str₀ TF.X Z) (U₀ TF.X Z) (dimFlag Dw)) (ω : CanId M) (la : AllWt.Weight Dw) (g : H0 M.str (tens M.K.bundle ((L₀ TF.X Z (la - FlagTan.kap Dw)).pull M.σ)) ⊤) (z : M.X), z ∈ M.off → z ∈ nonzeroLocus (toSec g) → ∃ s ∈ vanBd TF.X Z la, M.σ z ∈ nonzeroLocus (toSec s) := by
  first | exact @GlobalTheory.CuspNonvanishing.exists_vanBd_nonzero | exact GlobalTheory.CuspNonvanishing.exists_vanBd_nonzero | (intros; apply GlobalTheory.CuspNonvanishing.exists_vanBd_nonzero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechComparisonStructureH1Affine
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

set_option autoImplicit false

noncomputable section

open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechCmp

namespace GlobalTheory.CechCmp

theorem appLE_resG_tr {A B : Scheme.{0}} (f : A ⟶ B) {O O' : B.Opens} {V V' : A.Opens} (h : O' ≤ O)
    (h' : V' ≤ V) (e : V ≤ f ⁻¹ᵁ O) (e' : V' ≤ f ⁻¹ᵁ O') (x : Γ(B, O)) :
    (f.appLE O' V' e').hom (resG B h x) = resG A h' ((f.appLE O V e).hom x) := by
  simp only [resG, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]

theorem ι_appLE_bijective_of_image {T : Scheme.{0}} (Vo O : T.Opens) (W : Vo.toScheme.Opens)
    (e : W ≤ Vo.ι ⁻¹ᵁ O) (hW : Vo.ι ''ᵁ W = O) : Function.Bijective (Vo.ι.appLE O W e).hom := by
  rw [Scheme.Opens.ι_appLE]
  have k : (homOfLE (Set.image_subset_iff.mpr e) : Vo.ι ''ᵁ W ⟶ O) = eqToHom hW := Subsingleton.elim _ _
  rw [k]
  exact (T.presheaf.mapIso (eqToIso hW).op).commRingCatIsoToRingEquiv.bijective

theorem exists_cech_ho1_cmp : ∀ (X T : Scheme.{0}) (p : T ⟶ X), IsSeparated p → ∀ (U : X.affineOpens) (J : Type) (W : J → T.Opens), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = p ⁻¹ᵁ U.1 → ∀ (hWU : ∀ i, W i ≤ p ⁻¹ᵁ U.1), ∃ Φ : (∀ i i' : J, Γ(T, W i ⊓ W i')) → GlobalTheory.CechDR.HO1 ((p ∣_ U.1) ≫ U.2.isoSpec.hom : (p ⁻¹ᵁ U.1).toScheme ⟶ Sp Γ(X, U.1)), (∀ c : ∀ i i' : J, Γ(T, W i ⊓ W i'), (∀ i i' i'', resG T (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c i i') + resG T (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (c i' i'') = resG T (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (c i i'')) → ∀ (N : ℕ) (r : Fin N → Γ(X, U.1)) (e : Fin N → ∀ i i' : J, Γ(T, W i ⊓ W i')), (∀ k, (∀ i i' i'', resG T (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') ((e k) i i') + resG T (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') ((e k) i' i'') = resG T (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') ((e k) i i''))) → Φ (fun i i' => c i i' - ∑ k, (p.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (r k) * e k i i') = Φ c - ∑ k, r k • Φ (e k)) ∧ (∀ c : ∀ i i' : J, Γ(T, W i ⊓ W i'), (∀ i i' i'', resG T (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c i i') + resG T (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (c i' i'') = resG T (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (c i i'')) → Φ c = 0 → ∃ h : ∀ i : J, Γ(T, W i), ∀ i i', c i i' = resG T inf_le_left (h i) - resG T inf_le_right (h i')) ∧ (∀ x, ∃ c : ∀ i i' : J, Γ(T, W i ⊓ W i'), (∀ i i' i'', resG T (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c i i') + resG T (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (c i' i'') = resG T (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (c i i'')) ∧ Φ c = x) ∧ ∀ (R' : Type) [CommRing R'] (σ : Γ(X, U.1) →+* R') (Y : Scheme.{0}) (s' : Y ⟶ Sp R') (ι : Y ⟶ T) (ι' : Y ⟶ (p ⁻¹ᵁ U.1).toScheme), ι' ≫ (p ⁻¹ᵁ U.1).ι = ι → ∀ (w : ι' ≫ ((p ∣_ U.1) ≫ U.2.isoSpec.hom : (p ⁻¹ᵁ U.1).toScheme ⟶ Sp Γ(X, U.1)) = s' ≫ spMap σ) (c : ∀ i i' : J, Γ(T, W i ⊓ W i')), (∀ i i' i'', resG T (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c i i') + resG T (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (c i' i'') = resG T (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (c i i'')) → (∃ h' : ∀ i, Γ(Y, ι ⁻¹ᵁ W i), ∀ i i', (ι.appLE (W i ⊓ W i') (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx)).hom (c i i') = resG Y inf_le_left (h' i) - resG Y inf_le_right (h' i')) → GlobalTheory.CechDR.pullHO1 w (Φ c) = 0 := by
  intro X T p hp U J W hWa hWcov hWU
  have hsepV : (p ⁻¹ᵁ U.1).toScheme.IsSeparated := by
    haveI : IsAffine U.1 := U.2
    constructor
    rw [← Limits.terminal.comp_from (p ∣_ U.1)]
    infer_instance
  have himg : ∀ O : T.Opens, O ≤ p ⁻¹ᵁ U.1 → (p ⁻¹ᵁ U.1).ι ''ᵁ ((p ⁻¹ᵁ U.1).ι ⁻¹ᵁ O) = O := by
    intro O hO
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr hO
  let W' : J → (p ⁻¹ᵁ U.1).toScheme.Opens := fun i => (p ⁻¹ᵁ U.1).ι ⁻¹ᵁ W i
  have hW' : ⨆ i, W' i = ⊤ := by
    simp only [W', ← Scheme.Hom.preimage_iSup, hWcov, Scheme.Opens.ι_preimage_self]
  have hWa' : ∀ i, IsAffineOpen (W' i) := fun i => by
    rw [← Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion (p ⁻¹ᵁ U.1).ι, himg _ (hWU i)]
    exact hWa i
  let τ : ∀ i i', Γ(T, W i ⊓ W i') →+* Γ((p ⁻¹ᵁ U.1).toScheme, W' i ⊓ W' i') := fun i i' =>
    ((p ⁻¹ᵁ U.1).ι.appLE (W i ⊓ W i') (W' i ⊓ W' i') (fun _ hx => hx)).hom
  have hcoc : ∀ c : ∀ i i' : J, Γ(T, W i ⊓ W i'), (∀ i i' i'', resG T (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c i i') + resG T (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (c i' i'') = resG T (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (c i i'')) →
      IsCocycle W' (fun i i' => τ i i' (c i i')) := by
    intro c hc i i' i''
    have e := congrArg ((p ⁻¹ᵁ U.1).ι.appLE (W i ⊓ W i' ⊓ W i'') (W' i ⊓ W' i' ⊓ W' i'') (fun _ hx => hx)).hom (hc i i' i'')
    rw [map_add, appLE_resG_tr (f := (p ⁻¹ᵁ U.1).ι) (O := W i ⊓ W i') (O' := W i ⊓ W i' ⊓ W i'') (V := W' i ⊓ W' i') (V' := W' i ⊓ W' i' ⊓ W' i'') inf_le_left inf_le_left (fun _ hx => hx) (fun _ hx => hx),
      appLE_resG_tr (f := (p ⁻¹ᵁ U.1).ι) (O := W i' ⊓ W i'') (O' := W i ⊓ W i' ⊓ W i'') (V := W' i' ⊓ W' i'') (V' := W' i ⊓ W' i' ⊓ W' i'') (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (fun _ hx => hx) (fun _ hx => hx),
      appLE_resG_tr (f := (p ⁻¹ᵁ U.1).ι) (O := W i ⊓ W i'') (O' := W i ⊓ W i' ⊓ W i'') (V := W' i ⊓ W' i'') (V' := W' i ⊓ W' i' ⊓ W' i'') (le_inf (inf_le_left.trans inf_le_left) inf_le_right) (le_inf (inf_le_left.trans inf_le_left) inf_le_right) (fun _ hx => hx) (fun _ hx => hx)] at e
    exact e
  have hb2 : ∀ i i', Function.Bijective (τ i i') := fun i i' =>
    ι_appLE_bijective_of_image _ _ _ _ (himg _ (inf_le_left.trans (hWU i)))
  refine ⟨fun c => cmp ((p ∣_ U.1) ≫ U.2.isoSpec.hom : (p ⁻¹ᵁ U.1).toScheme ⟶ Sp Γ(X, U.1)) W' hW'
    (fun i i' => τ i i' (c i i')), ?_, ?_, ?_, ?_⟩
  · intro c hc N r e he
    have h1 := GlobalTheory.T.cechClassMap_sub_sum_const_linear Γ(X, U.1) _ ((p ∣_ U.1) ≫ U.2.isoSpec.hom : (p ⁻¹ᵁ U.1).toScheme ⟶ Sp Γ(X, U.1)) _ W' hW'
      (fun i i' => τ i i' (c i i')) (hcoc c hc) N r (fun k i i' => τ i i' (e k i i')) (fun k => hcoc _ (he k))
    refine Eq.trans ?_ h1
    dsimp only
    congr 1
    funext i i'
    simp only [map_sub, map_sum, map_mul]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    exact GlobalTheory.T.appLE_opensInclusion_appLE_eq_secMap_isoSpec X T p U (W i ⊓ W i') _ (W' i ⊓ W' i') (fun _ hx => hx) (r k)
  · intro c hc h0
    haveI := hsepV
    obtain ⟨h'', hh⟩ := GlobalTheory.T.cechCocycle_isCoboundary_of_class_eq_zero _ _ _ _ W' hW' hWa' (fun i i' => (hWa' i).inf (hWa' i')) _ (hcoc c hc) h0
    choose h hh1 using fun i => (ι_appLE_bijective_of_image (p ⁻¹ᵁ U.1) (W i) (W' i) le_rfl (himg _ (hWU i))).2 (h'' i)
    refine ⟨h, fun i i' => (hb2 i i').1 ?_⟩
    change ((p ⁻¹ᵁ U.1).ι.appLE (W i ⊓ W i') (W' i ⊓ W' i') (fun _ hx => hx)).hom (c i i') = ((p ⁻¹ᵁ U.1).ι.appLE (W i ⊓ W i') (W' i ⊓ W' i') (fun _ hx => hx)).hom (resG T inf_le_left (h i) - resG T inf_le_right (h i'))
    rw [map_sub, appLE_resG_tr (f := (p ⁻¹ᵁ U.1).ι) (O := W i) (O' := W i ⊓ W i') (V := W' i) (V' := W' i ⊓ W' i') inf_le_left inf_le_left le_rfl (fun _ hx => hx), appLE_resG_tr (f := (p ⁻¹ᵁ U.1).ι) (O := W i') (O' := W i ⊓ W i') (V := W' i') (V' := W' i ⊓ W' i') inf_le_right inf_le_right le_rfl (fun _ hx => hx), hh1, hh1]
    exact hh i i'
  · intro x
    haveI := hsepV
    obtain ⟨c', hc', hx⟩ := GlobalTheory.T.cech_h1_class_eq_of_cocycle_affine_cover _ _ ((p ∣_ U.1) ≫ U.2.isoSpec.hom : (p ⁻¹ᵁ U.1).toScheme ⟶ Sp Γ(X, U.1)) _ W' hW' hWa'
      (fun i i' => (hWa' i).inf (hWa' i')) (fun i i' i'' => ((hWa' i).inf (hWa' i')).inf (hWa' i'')) x
    choose c hc using fun i i' => (hb2 i i').2 (c' i i')
    refine ⟨c, ?_, ?_⟩
    · intro i i' i''
      apply (ι_appLE_bijective_of_image (p ⁻¹ᵁ U.1) (W i ⊓ W i' ⊓ W i'') (W' i ⊓ W' i' ⊓ W' i'') (fun _ hx => hx)
        (himg _ (inf_le_left.trans (inf_le_left.trans (hWU i))))).1
      rw [map_add, appLE_resG_tr (f := (p ⁻¹ᵁ U.1).ι) (O := W i ⊓ W i') (O' := W i ⊓ W i' ⊓ W i'') (V := W' i ⊓ W' i') (V' := W' i ⊓ W' i' ⊓ W' i'') inf_le_left inf_le_left (fun _ hx => hx) (fun _ hx => hx),
        appLE_resG_tr (f := (p ⁻¹ᵁ U.1).ι) (O := W i' ⊓ W i'') (O' := W i ⊓ W i' ⊓ W i'') (V := W' i' ⊓ W' i'') (V' := W' i ⊓ W' i' ⊓ W' i'') (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (fun _ hx => hx) (fun _ hx => hx),
        appLE_resG_tr (f := (p ⁻¹ᵁ U.1).ι) (O := W i ⊓ W i'') (O' := W i ⊓ W i' ⊓ W i'') (V := W' i ⊓ W' i'') (V' := W' i ⊓ W' i' ⊓ W' i'') (le_inf (inf_le_left.trans inf_le_left) inf_le_right) (le_inf (inf_le_left.trans inf_le_left) inf_le_right) (fun _ hx => hx) (fun _ hx => hx)]
      have e1 := hc i i'
      have e2 := hc i' i''
      have e3 := hc i i''
      simp only [τ] at e1 e2 e3
      rw [e1, e2, e3]
      exact hc' i i' i''
    · have e : (fun i i' => τ i i' (c i i')) = c' := funext fun i => funext fun i' => hc i i'
      change cmp _ W' hW' (fun i i' => τ i i' (c i i')) = x
      rw [e]
      exact hx
  · intro R' _ σ Y s' ι ι' hι w c hc hcob
    obtain ⟨h', hh'⟩ := hcob
    subst hι
    haveI := hsepV
    refine GlobalTheory.T.cechClass_pullHO1_eq_zero_of_pullback_coboundary _ _ _ _ W' hW' hWa' R' σ Y s' ι' w _ (hcoc c hc) ⟨h', fun i i' => ?_⟩
    refine Eq.trans ?_ (hh' i i')
    rw [← Scheme.Hom.appLE_comp_appLE ι' (p ⁻¹ᵁ U.1).ι _ (W' i ⊓ W' i')]
    rfl
end GlobalTheory.CechCmp
end
end

