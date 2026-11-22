import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0071
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0165
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0131
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0112
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0164
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0205
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0104
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0129
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0135
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0145
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0021
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsWeightZeroSectionUnitIntegralTorsionPoint
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0196
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.BaseFactsHasGeoExistsClos
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH

theorem baseFacts_hasGeo_exists_clos : GlobalTheory.UT.LL → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), S.Big → ρ.HasU → S.Over₀ M U₀ → S.IsEE M U₀ EE → BaseFacts S M U₀ EE ∧ ρ.HasGeo ∧ ∃ (Q : Clos ρ M U₀ EE) (ex : Q.Ext), ex.core.HasTests ∧ ex.core.Indep ∧ ex.core.Fib ∧ ex.core.HasCharts := by
  intro hL hT o Ω _ _ _ _ S ρ M U₀ EE hB hU hO hE
  have hTests : S.HasTests := by
    intro p _ y hy
    obtain ⟨_, _, τ, _⟩ := hU p y hy ∅
    exact ⟨τ⟩
  have hF : BaseFacts S M U₀ EE := baseFacts_of_isEE o Ω S M U₀ EE hTests hO hE
  have hG : ρ.HasGeo := GlobalTheory.T.hasGeometricTest_of_hasUniformisedTest hL hT o Ω S ρ hB hU
  obtain ⟨Q⟩ := GlobalTheory.T.nonempty_abelianSchemeProjectiveClosure hL o Ω S ρ M U₀ EE hF
  obtain ⟨ex⟩ := GlobalTheory.T.nonempty_closureExtension_abelianScheme hL o Ω S ρ M U₀ EE hF Q
  obtain ⟨h₁, h₂⟩ := GlobalTheory.T.closure_tests_exist_and_reduction_independent hL o Ω S ρ M U₀ EE hF Q ex hB hG
  have h₃ : ex.core.Fib := GlobalTheory.T.fibre_eq_specialFibre_of_reduction_indep ex.core h₂
  exact ⟨hF, hG, Q, ex, h₁, h₂, h₃, GlobalTheory.T.hasGradedCharts_near_generic_point_closure hL o Ω S ρ M U₀ EE hF Q ex hB hG h₃⟩

end GlobalTheory.ZH
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorsionIsometryUniformisedModel
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.ModelData

namespace GlobalTheory.ModelData.ModelTate

attribute [local instance] GlobalTheory.TorusExt.gtGroup

theorem exists_level_down {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] (hB : D.TauBimult) (n m : ℕ) (p : QkPt D F (n * m)) :
    ∃ q : QkPt D F n, q.y = p.y ∧ GtPtF.IsNsmul m p.g q.g :=
  ⟨TorusExt.qkMk hB p.y (m • p.g) (by rw [← mul_nsmul', TorusExt.qk_nsmul hB p]), rfl,
    (TorusExt.isNsmul_iff_eq _ _ _).2 rfl⟩

theorem weilIs_of_pull {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] [IsCommMonObj G']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} {L : LB G.left} {L' : LB G'.left} (hL : L.IsLB) (hL' : L'.IsLB)
    (hp : IsGrpPullback G' G f φ) (hw : LBIso L' (L.pull φ)) (T : Over S') (g : T.left ⟶ S) (hg : g = T.hom ≫ f)
    (k : ℤ) (x y : T ⟶ G') (x₀ y₀ : Over.mk g ⟶ G) (c : Γ(T.left, ⊤)ˣ) (ex : x₀.left = x.left ≫ φ)
    (ey : y₀.left = y.left ≫ φ) (h : WeilIs G' L' k x y c) : WeilIs G L k x₀ y₀ c := by
  subst hg
  exact (weilIs_grpPullback_of_comm' _ _ _ _ _ _ _ _ hL hL' hp hw T k x y x₀ y₀ c ex ey).1 h

theorem exists_tateIsoQ_of_model : GlobalTheory.UT.LL → BrGtSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (C : Type) [NormedField C] (o : Full D C) (M : Mdl o) (N' : NumD C) (_ : NumOf M.P.D.toPre C N'), ∃ I : TateIsoQ D M.P.D.toPre M.P.oD C, I.ζ = o.I.ζ ∧ ∀ k, 0 < k → ∀ x p' (z : TFK (R := M.W) C ⟶ M.P.A.A), QkPt.Equiv _ C (I.ev k x) p' → z.left = (o.I.ev k x).left ≫ M.φ → M.P.ToA C k p' z := by
  intro hL _ E _ _ _ H D C _ o M _ _
  letI := H.starRing
  have := o.closed
  have := o.P.isAb.comm
  have hB := M.P.D.tau_bimult
  obtain ⟨hA, h0⟩ := M.admissible_base_of_complete_dvr
  obtain ⟨-, l₁, l₂, l₃, l₄⟩ := GlobalTheory.twistBaseChange_and_valuation_statements
  have hT := GlobalTheory.UT.torsionIso_of_pelUnif hL l₁ l₂ l₃ l₄ E H M.W _ hA M.t M.P
  choose f f₁ f₂ f₃ f₄ f₅ f₆ using hT C
  have hg : jFK (R := M.W) C = (baseOver (Sp C)).hom ≫ jFK (R := M.W) C := (Category.id_comp _).symm
  obtain ⟨e, he⟩ : ∃ e : (baseOver (Sp C) ⟶ o.P.A) ≃* (TFK (R := M.W) C ⟶ M.P.A.A), ∀ x, (e x).left = x.left ≫ M.φ :=
    LiePull.exists_pushEquiv M.cart (baseOver (Sp C)) _ hg
  have eact : ∀ c x, e (x ≫ o.oa.act c) = e x ≫ M.P.oA.act c := fun c x => Over.OverMorphism.ext (by
    rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, M.act, Category.assoc])
  have tors : ∀ n (hn : 0 < n) p, f n hn p ^ n = 1 := fun n hn p => by
    obtain ⟨w, hw⟩ := M.P.U.ext
    exact ((f₁ n hn p _).2 rfl w hw).1
  have hev : ∀ n a, ∃ p : QkPt M.P.D.toPre C n, ∀ hn : 0 < n, f n hn p = e (o.I.ev n a) := fun n a => by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨TorusExt.qkZero hB C 0, fun h => absurd h (lt_irrefl 0)⟩
    · obtain ⟨p, hp⟩ := f₂ n hn (e (o.I.ev n a)) (by rw [← map_pow, (o.I.onto n hn _).2 ⟨a, rfl⟩, map_one])
      exact ⟨p, fun _ => hp⟩
  choose ev evp using hev
  refine ⟨{ ζ := o.I.ζ, ζ_prim := o.I.ζ_prim, ζ_pow := o.I.ζ_pow, ev := ev
            add := fun n hn a b => ?_, lin := fun n hn c a => ?_, ker := fun n hn a b => ?_,
            onto := fun n hn p => ?_, tower := fun n m hn hm a => ?_, isom := fun n hn a b => ?_ },
    rfl, fun k hk x p' z h hz => ?_⟩
  · refine (TorusExt.qkAdd_iff hB _ _ _).2 ((f₃ n hn _ _).1 ?_)
    rw [f₄ n hn _ _ _ (TorusExt.qkAdd_qkAdd hB _ _), evp, evp, evp, o.I.add, map_mul]
  · obtain ⟨p, hp⟩ := qkAct_exists hL.1.globalFns hB M.P.oD c (ev n a)
    have h₁ := f₅ n hn _ _ _ hp
    obtain ⟨q, q₁, q₂, q₃⟩ := hp
    refine ⟨q, q₁, q₂, TorusExt.equiv_trans hB q₃ ((f₃ n hn _ _).1 ?_)⟩
    rw [h₁, evp, evp, o.I.lin, eact]
  · rw [← f₃ n hn, evp, evp, e.injective.eq_iff]
    have h₁ : o.I.ev n a = o.I.ev n b * o.I.ev n (a - b) := by rw [← o.I.add, add_sub_cancel]
    rw [h₁, mul_eq_left, o.I.ker n hn]
    exact exists_congr fun c => sub_eq_iff_eq_add'
  · obtain ⟨a, ha⟩ := (o.I.onto n hn (e.symm (f n hn p))).1 (by rw [← map_pow, tors, map_one])
    exact ⟨a, (f₃ n hn _ _).1 (by rw [evp, ha, MulEquiv.apply_symm_apply])⟩
  · obtain ⟨q, q₁, q₂⟩ := exists_level_down hB n m (ev (n * m) a)
    have hN := Nat.mul_pos hn hm
    have h := (GlobalTheory.LevelCompat.qkToAkU_level hL M.W _ hA M.P.D M.P.A M.t.G M.t.semi M.P.U C n m _ hn hm rfl q
      (ev (n * m) a) _).2 q₁ q₂ ((f₁ _ hN _ _).2 rfl)
    refine ⟨q, q₁, q₂, (f₃ n hn _ _).1 ?_⟩
    rw [← (f₁ n hn _ _).1 h, evp, evp, ← map_pow, o.I.tower n m hn hm]
  · refine (f₆ n hn _ _ _).2 ?_
    rw [evp, evp]
    exact weilIs_of_pull M.P.A.isLB o.P.isLB M.cart M.lb (baseOver (Sp C)) _ hg n _ _ _ _ _ (he _) (he _)
      (o.I.isom n hn a b)
  · refine (f₁ k hk _ _).2 ?_
    rw [← (f₃ k hk _ _).2 h]
    exact (Over.OverMorphism.ext (hz.trans (he _).symm)).trans (evp k x hk).symm

end GlobalTheory.ModelData.ModelTate
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsWeightZeroSectionUnitIntegralTorsionPointStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weightZeroSection_unit_integralTorsionPoint : Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → (∀ h ∈ l.yy.ker, ∃ i, ‖∑ j, y₀ (algebraMap o S.R (S.proj _ (l.wt 0) j i)) * y₀ ⟨S.ev h j, S.ev_mem h j⟩‖ = S.delta y₀) := by
  first | exact @GlobalTheory.ZH.WeightZeroUnit.main | exact GlobalTheory.ZH.WeightZeroUnit.main | (intros; apply GlobalTheory.ZH.WeightZeroUnit.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PotentialSemistableOfRationalLTorsionStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.potentialSemistable_of_rational_lTorsion : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K], Finite (IsLocalRing.ResidueField V) → ∀ (l : ℕ), l.Prime → 3 ≤ l → IsUnit (l : V) → ∀ (P : Out.PolAV (Sp K)), (∀ (τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (x : Over.mk (spMap (algebraMap K (AlgebraicClosure K))) ⟶ P.A), x ^ l = 1 → spMap τ.toRingEquiv.toRingHom ≫ x.left = x.left) → PotModel V K P.A (fun _ _ _ G _ => IsSemiAbelian G) := by
  first | exact @GlobalTheory.SS.potModel_of_rational_torsion | exact GlobalTheory.SS.potModel_of_rational_torsion | (intros; apply GlobalTheory.SS.potModel_of_rational_torsion <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusOperatorEigenOfExpansionSingleClassStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusOperator_eigen_of_expansion_single_class : Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∀ (x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)) (rig : LB.Gen (u.A.L.pull (eSec u.A.A))) (e : ∀ a, FrameAt u.A (x a)) (th : SecA u.A (PadicAlgCl p) 1) (s : S.J → SecA u.A (PadicAlgCl p) S.N), PtsOver u x → SecsOver u x rig e th s → ∀ (w₀ : W0 u.U.toUnifPre), w₀.IsGen → ∀ (α : u.D.toPre.X) (b : S.J → PadicAlgCl p) (σ : SecA u.A (PadicAlgCl p) S.N) (Φ : Fam u.D.toPre (PadicAlgCl p) S.N), IsComb u.A s b σ → u.U.ExpandsF (PadicAlgCl p) S.N w₀ σ Φ → (∀ β, (∀ z : u.D.toPre.X, β ≠ α + S.N • z) → ∀ j, (Φ.s β).f j = 0) → ∀ (t : S.perp l.yy.ker) (h : S.Gam), ∑ j, (∑ i, y₀ (algebraMap o S.R (S.ρ t j i)) * b i) * y₀ ⟨S.ev h j, S.ev_mem h j⟩ = y₀ (algebraMap o S.R S.ζN) ^ (l.wt α t).val * ∑ j, b j * y₀ ⟨S.ev h j, S.ev_mem h j⟩ := by
  first | exact @GlobalTheory.TestFibre.eigen_of_expansion_in_class | exact GlobalTheory.TestFibre.eigen_of_expansion_in_class | (intros; apply GlobalTheory.TestFibre.eigen_of_expansion_in_class <;> assumption)
end

