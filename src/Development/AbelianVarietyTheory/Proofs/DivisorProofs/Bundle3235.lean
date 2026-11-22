import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3210
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3200
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2511
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3211
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSymplecticOfTranslFixed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2387
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0034
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0028
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRefinementOfIsLimit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1017
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsNoethModel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0163
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0130
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.ExistsGenTransfer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1696
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothBaseDimEqPeriodSpaceDim
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3125
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3105
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3202
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3189
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3100
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2976
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1560
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3186
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0023
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3145
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2883
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3212
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3036
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3205
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2983
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyDeeperLevelOfDvdStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelFamily_deeper_level_of_dvd : ∀ (h n N : ℕ) (o : Type) [CommRing o] [IsNoetherianRing o] (b : TBase o N), 3 ≤ n → Odd N → n ∣ N → Nonempty (SFam h n ((b.ζ : o) ^ (N / n))) → Nonempty (SFam h N (b.ζ : o)) := by
  first | exact @GlobalTheory.SiegLev.sFam_of_dvd | exact GlobalTheory.SiegLev.sFam_of_dvd | (intros; apply GlobalTheory.SiegLev.sFam_of_dvd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelIntegralToroidalOfPolarisedCharts
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolDeg

theorem siegelToroidalIntegral_of_polCharts
    (hfan : ∀ g : ℕ, ∃ φ : InvFun ℤ, IsPolFan (id : ℤ → ℤ) g φ ∧ NoSelfInt (id : ℤ → ℤ) g φ)
    (h : GlobalTheory.Published.SiegelToroidalPolCharts) : GlobalTheory.Published.SiegelToroidalIntegral := by
  intro g hg
  obtain ⟨φ, hφ, hns⟩ := hfan g
  refine ⟨φ, hφ, fun n hn hodd => ?_⟩
  obtain ⟨F, S, s, j, hj, G, hG, e, BD, d, N, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, k, hk⟩ :=
    h g hg φ hφ hns n hn hodd
  have hn0 : n ≠ 0 := by omega
  refine ⟨F, S, s, j, hj, G, hG, e, BD, d, N, h1, h2, h3, h4, h5, h6, h7, h8, h9,
    fun x => GlobalTheory.T.hasSiegelChart_of_polarisedMonomialPeriodChart F s j e φ BD d x hn0 (h10 x), h11, h12, k, fun k' hk' => ?_⟩
  exact GlobalTheory.T.isAmple_tensor_lbPow_mono_of_generated S (hodge G g) (CechPic.dual BD.lb) N k (isLB_hodge G g)
    (CechPic.isLB_dual BD.isLB_lb) h12 hk k' hk'

example : (∀ g : ℕ, ∃ φ : InvFun ℤ, IsPolFan (id : ℤ → ℤ) g φ ∧ NoSelfInt (id : ℤ → ℤ) g φ) →
    GlobalTheory.Published.SiegelToroidalPolCharts → GlobalTheory.Published.SiegelToroidalIntegral := siegelToroidalIntegral_of_polCharts

end GlobalTheory.PolDeg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelLevelLoweringQuotientRepresentsReducedStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelLevelLoweringQuotient_represents_reduced : ∀ (h n N : ℕ) (F : SFam h N (zetaAway N)) (j : cycAway n →+* cycAway N) (Q : SQuot F n (zetaAway n) j), 3 ≤ n → Odd N → n ∣ N → Function.Injective j → j (zetaAway n) = zetaAway N ^ (N / n) → IsFinite (spMap j) → Etale (spMap j) → Surjective (spMap j) → ∀ (S : Scheme.{0}) (s' : S ⟶ Sp (cycAway n)) (c : SiegPre h n (zetaAway n) s'), IsReduced S → Dense {x : S | (s' x).asIdeal = ⊥} → c.Principal → ∃ f : S ⟶ Q.X, f ≫ Q.s = s' ∧ SiegPB c Q.univ f := by
  first | exact @GlobalTheory.quotFam_represents | exact GlobalTheory.quotFam_represents | (intros; apply GlobalTheory.quotFam_represents <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelObjectDataDescendsFiniteTypeSubringStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelObject_data_descends_finiteType_subring : ∀ (g n : ℕ), 3 ≤ n → ∀ (R : Type) [CommRing R] (β : cycAway n →+* R) (c : SiegPre g n (zetaAway n) (spMap β)), ∃ (R₁ : Subring R) (β₁ : cycAway n →+* R₁) (A₁ : Over (Sp R₁)) (_ : GrpObj A₁) (P₁ : LB (A₁ ⊗ A₁).left) (lv₁ : Std g n → (𝟙_ (Over (Sp R₁)) ⟶ A₁)), Algebra.FiniteType ℤ R₁ ∧ R₁.subtype.comp β₁ = β ∧ IsAbelianScheme A₁ ∧ SmoothOfRelativeDimension g A₁.hom ∧ P₁.IsLB ∧ IsPullbackTriple c.A c.P (lvOf c) A₁ P₁ lv₁ (spMap R₁.subtype) := by
  first | exact @GlobalTheory.SiegFg.siegPre_data_descends_fg | exact GlobalTheory.SiegFg.siegPre_data_descends_fg | (intros; apply GlobalTheory.SiegFg.siegPre_data_descends_fg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallRouteKernelEqUnitNormMulThetaStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.small_route_kernel_eq_unit_norm_mul_theta : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G)
    (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j))
    (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ') (g₁ : GA D (G.V (.grid (i + 1) j)))
    (e : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Num G i j) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j)
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.IsTripleOf W M t i j e Bs Γ X) (hTr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om')
    (hv : ∀ w ∈ locPl G t, w.under (𝓞 D.host.F) ≠ Bs.v₁),
    ∀ ΦB, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.IsDatumB W e Γ Θ' ΦB →
    ∃ ξ : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid (i + 1) j)) → ℂ, (∀ x, ‖ξ x‖ = 1) ∧
      ∀ g u, kerSmall W Θ' g g₁ u =
        ξ (g, g₁) * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om' ΦB (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU _ (-1) h.JW₁ u) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (g, g₁)) := by
  first | exact @GlobalTheory.SmallKernel.kerSmall_eq_theta | exact GlobalTheory.SmallKernel.kerSmall_eq_theta | (intros; apply GlobalTheory.SmallKernel.kerSmall_eq_theta <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothBaseDimEqPeriodSpaceDimStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothBase_dim_eq_periodSpace_dim : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (Λ : Type) (F : Fam ℂ O Λ g) (N : ℕ) (C : ∀ D' : PLat O bar, (Λ → D'.La) → Prop) (d d' : ℕ) (D' : PLat O bar) (t : Λ → D'.La), 0 < N → (∀ a, F.eta a ^ N = 1) → SmoothOfRelativeDimension d F.s → QuasiCompact F.s → FineAt F (RingHom.id ℂ) ρ N C → C D' t → (∃ P, IsPeriod D' ρ P) → PerCoord D' ρ d' → d = d' := by
  first | exact @GlobalTheory.DimEq.dim_eq | exact GlobalTheory.DimEq.dim_eq | (intros; apply GlobalTheory.DimEq.dim_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothFormsCalculusHolomorphicAtlas
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical

set_option autoImplicit false

namespace GlobalTheory

theorem formCalculus : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n),
    A.IsForm 1 ∧ (∀ (c : ℂ) (α β : A.Fld), A.IsForm α → A.IsForm β → A.IsForm (α + β) ∧ A.IsForm (α * β) ∧ A.IsForm (c • α) ∧
      A.IsForm (A.del α) ∧ A.IsForm (A.dbar α) ∧ A.del (α + β) = A.del α + A.del β ∧ A.dbar (α + β) = A.dbar α + A.dbar β ∧
      A.del (c • α) = c • A.del α ∧ A.dbar (c • α) = c • A.dbar α) ∧
    (∀ (w : A.Pt → Ev n) (β : A.Fld), A.IsForm (fld A w) → A.IsForm β →
      A.del (fld A w * β) = A.del (fld A w) * β + fld A w * A.del β ∧ A.dbar (fld A w * β) = A.dbar (fld A w) * β + fld A w * A.dbar β) ∧
    (∀ (ι : Type) (w : ι → A.Pt → Ev n) (P : MvPolynomial ι ℝ), (∀ i, A.IsForm (fld A (w i))) → A.IsForm (evalF A w P) ∧
      ((∀ i, A.del (fld A (w i)) = 0) → A.del (evalF A w P) = 0) ∧ ((∀ i, A.dbar (fld A (w i)) = 0) → A.dbar (evalF A w P) = 0)) ∧
    ∀ (M' : Type) [TopologicalSpace M'] (n' : ℕ) (A' : HolAtlas M' n') (f : M' → M), A.IsHolo A' f →
      A.pullback A' f 1 = 1 ∧ ∀ (c : ℂ) (α β : A.Fld), A.pullback A' f (α + β) = A.pullback A' f α + A.pullback A' f β ∧
        A.pullback A' f (α * β) = A.pullback A' f α * A.pullback A' f β ∧ A.pullback A' f (c • α) = c • A.pullback A' f α ∧
        (A.IsForm α → A'.IsForm (A.pullback A' f α) ∧ A'.del (A.pullback A' f α) = A.pullback A' f (A.del α) ∧
          A'.dbar (A.pullback A' f α) = A.pullback A' f (A.dbar α)) := by
  intro M _ n A
  refine ⟨(GlobalTheory.T.isForm_one_add_mul_smul M n A).1, fun c α β hα hβ => ?_, fun w β hw hβ => GlobalTheory.T.del_dbar_leibniz_evenForm_mul M n A w β hw hβ, fun ι w P hw => ?_,
    fun M' _ n' A' f hf => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := (GlobalTheory.T.isForm_one_add_mul_smul M n A).2 c α β hα hβ
    obtain ⟨d1, d2⟩ := GlobalTheory.T.holAtlas_isForm_del_dbar_smooth M n A α hα
    obtain ⟨e1, e2, e3, e4⟩ := (GlobalTheory.T.del_dbar_additive_complexLinear_one M n A).2 c α β hα hβ
    exact ⟨h1, h2, h3, d1, d2, e1, e2, e3, e4⟩
  · induction P using MvPolynomial.induction_on with
    | C r =>
      have e : evalF A w (C r) = ((r : ℂ) • (1 : A.Fld)) := by
        funext x
        simp [evalF, fld, Algebra.algebraMap_eq_smul_one]
        first | rfl | exact Subalgebra.coe_smul _ _ _ | (rw [SetLike.val_smul]; simp) | simp [Subalgebra.coe_algebraMap]
      have h1 := (GlobalTheory.T.isForm_one_add_mul_smul M n A).1
      have hf := ((GlobalTheory.T.isForm_one_add_mul_smul M n A).2 (r : ℂ) 1 1 h1 h1).2.2
      obtain ⟨⟨z1, z2⟩, hl⟩ := GlobalTheory.T.del_dbar_additive_complexLinear_one M n A
      obtain ⟨-, -, s1, s2⟩ := hl (r : ℂ) 1 1 h1 h1
      rw [e]
      exact ⟨hf, fun _ => by rw [s1, z1, smul_zero], fun _ => by rw [s2, z2, smul_zero]⟩
    | add p q hp hq =>
      have e : evalF A w (p + q) = evalF A w p + evalF A w q := by
        funext x
        simp [evalF, fld]
      obtain ⟨hp1, hp2, hp3⟩ := hp
      obtain ⟨hq1, hq2, hq3⟩ := hq
      obtain ⟨a1, -, -⟩ := (GlobalTheory.T.isForm_one_add_mul_smul M n A).2 1 _ _ hp1 hq1
      obtain ⟨l1, l2, -, -⟩ := (GlobalTheory.T.del_dbar_additive_complexLinear_one M n A).2 1 _ _ hp1 hq1
      rw [e]
      exact ⟨a1, fun h => by rw [l1, hp2 h, hq2 h, add_zero], fun h => by rw [l2, hp3 h, hq3 h, add_zero]⟩
    | mul_X p i hp =>
      have e : evalF A w (p * X i) = evalF A w p * fld A (w i) := by
        funext x
        simp [evalF, fld]
      obtain ⟨hp1, hp2, hp3⟩ := hp
      obtain ⟨-, a2, -⟩ := (GlobalTheory.T.isForm_one_add_mul_smul M n A).2 1 _ _ hp1 (hw i)
      obtain ⟨b1, b2⟩ := GlobalTheory.T.del_dbar_leibniz_evenForm_mul M n A (fun x => aeval (fun i => w i x) (p.map (algebraMap ℝ ℂ))) (fld A (w i)) hp1 (hw i)
      rw [e]
      refine ⟨a2, fun h => ?_, fun h => ?_⟩
      · change A.del (fld A _ * fld A (w i)) = 0
        rw [b1]
        change A.del (evalF A w p) * _ + _ = 0
        rw [hp2 h, h i, zero_mul, mul_zero, add_zero]
      · change A.dbar (fld A _ * fld A (w i)) = 0
        rw [b2]
        change A.dbar (evalF A w p) * _ + _ = 0
        rw [hp3 h, h i, zero_mul, mul_zero, add_zero]
  · refine ⟨funext fun x => map_one _, fun c α β => ⟨funext fun x => map_add _ _ _, funext fun x => map_mul _ _ _,
      funext fun x => map_smul (pull _) c _, fun hα => ?_⟩⟩
    obtain ⟨d1, d2⟩ := GlobalTheory.T.holAtlas_isForm_del_dbar_smooth M n A α hα
    exact ⟨GlobalTheory.T.holAtlas_isForm_pullback_holomorphic M M' n n' A A' f α hf hα, GlobalTheory.T.del_dbar_comm_pullback_of_smooth_del_dbar M M' n n' A A' f α hf hα d1 d2⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafCohomologyAbelianVarietyAlgClosed
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem exists_fin_affineOpen_cover_of_compactSpace (X : Scheme.{0}) [CompactSpace X] :
    ∃ (n : ℕ) (D : Fin n → X.Opens), (∀ i, IsAffineOpen (D i)) ∧ ⨆ i, D i = ⊤ := by
  obtain ⟨Us, hUs, hfin, hU⟩ :=
    X.isBasis_affineOpens.exists_finite_of_isCompact (U := ⊤) isCompact_univ
  let s := hfin.toFinset
  refine ⟨s.card, fun i => (s.equivFin.symm i).1, fun i => ?_, ?_⟩
  · have h := (s.equivFin.symm i).2
    exact hUs (hfin.mem_toFinset.mp h)
  · apply le_antisymm le_top
    rw [hU]
    refine sSup_le fun u hu => ?_
    have hs : u ∈ s := hfin.mem_toFinset.mpr hu
    refine le_iSup_of_le (s.equivFin ⟨u, hs⟩) ?_
    simp

theorem structureSheafCoh_abelianVariety_algClosed :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] (g : ℕ),
      IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
      Module.Finite K (HO1 A.hom) ∧ Module.finrank K (HO1 A.hom) = g ∧
        GlobalTheory.AbCoh.WedgeO (OAff A.hom) ∧ GlobalTheory.AbCoh.NoPrimitiveStructureSheafH2 A ∧ GlobalTheory.AbCoh.AxesVanishingStructureSheafDegOne A := by
  intro K _ _ A _ g hA hg
  obtain ⟨hax, -, hrk⟩ := GlobalTheory.T.abelian_variety_h1_axes_primitive_rank K A g hA hg
  obtain ⟨hw, hno⟩ := GlobalTheory.T.abelian_variety_wedge_no_primitive_h2 K A g hA hg
  refine ⟨?_, hrk, hw, hno, hax⟩
  haveI : IsProper A.hom := hA.proper
  haveI : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  obtain ⟨n, D, hD, hcov⟩ := exists_fin_affineOpen_cover_of_compactSpace A.left
  obtain ⟨⟨e⟩, -⟩ := GlobalTheory.T.cech_cohomology_structure_sheaf_iso K A.left A.hom (Fin n) D inferInstance hD hcov
  obtain ⟨hfin, -, -⟩ := GlobalTheory.T.cech_cohomology_trivial_bundle_abelian K A g hA hg (Fin n) D hD hcov
  exact Module.Finite.equiv e.symm

end GlobalTheory.AbCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentValuePullbackCrystallineFormDualNumbersStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
open MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_value_pullback_crystalline_form_dual_numbers : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (A : Over (Sp R)) (A' : Over (Sp R')) (φ : A'.left ⟶ A.left) (m : IsMor (dp0 R) (A.hom ≫ 𝟙 (Sp R)) (dp0 R') (A'.hom ≫ 𝟙 (Sp R')) (algebraMap R R') φ) (v : epsR R' ⟶ A') (hy : (v.left ≫ φ) ≫ A.hom ≫ 𝟙 (Sp R) = spMap (algebraMap R (DualNumber R'))) (f : Form (A.hom ≫ 𝟙 (Sp R))), tanVal v (m.pullForm f) = TrivSqZeroExt.snd ((SqExt.ofModule R R' R').val (v.left ≫ φ) hy f.1) := by
  first | exact @GlobalTheory.ParPt.tanVal_pullForm_ofModule | exact GlobalTheory.ParPt.tanVal_pullForm_ofModule | (intros; apply GlobalTheory.ParPt.tanVal_pullForm_ofModule <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateModuleGaloisImagesCommuteOfComplexMultiplicaStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateModule_galoisImages_commute_of_complexMultiplication : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (F : Type) [Field F] [NumberField F], HasCMBy A F → ∀ (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 → ∀ σ τ : Ω ≃ₐ[K] Ω, galTate A l σ * galTate A l τ = galTate A l τ * galTate A l σ := by
  first | exact @GlobalTheory.CMComm.galTate_commute_of_hasCMBy | exact GlobalTheory.CMComm.galTate_commute_of_hasCMBy | (intros; apply GlobalTheory.CMComm.galTate_commute_of_hasCMBy <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalCoordsEqOfMatchingData
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
noncomputable section

namespace GlobalTheory.TInj

theorem gm_unitOn_inj {V : Type} [CommRing V] [IsDomain V] {F : Type} [Field F] [Algebra (FractionRing V) F]
    (z : (TF (R := V) F).left) {k₁ k₂ : Fˣ}
    (h : gm (𝟙 (TF (R := V) F).left) z ⊤ (unitOn k₁) = gm (𝟙 (TF (R := V) F).left) z ⊤ (unitOn k₂)) : k₁ = k₂ := by
  have e : unitOn k₁ = unitOn k₂ := unit_ext fun x _ => by
    have : x = z := Subsingleton.elim (α := PrimeSpectrum F) x z
    rw [this]; exact h
  revert e
  apply Units.map_injective
  intro x y h
  have := congrArg (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom h
  simpa using this

theorem cancel_four {G : Type} [CommGroup G] {V₁ V₂ K₁ K₂ L₁ L₂ U τ : G} (h₁ : V₁ = K₁ * (L₁ * τ))
    (h₂ : V₂ = K₂ * (L₂ * τ)) (h₃ : V₂ = V₁ * U) (h₄ : L₂ = L₁ * U) : K₁ = K₂ := by
  rw [h₄, h₃, h₁] at h₂
  have e : K₁ * (L₁ * U * τ) = K₂ * (L₁ * U * τ) := by rw [← h₂]; ac_rfl
  exact mul_right_cancel e

theorem coords_eq_of_match : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (V : Type) [CommRing V] [IsDomain V] (ω : W →+* V) (D₁ D₂ : DegPre V) (s₁ : I → V) (e₁ : D₁.X ≃+ (Fin T.r → ℤ)) (β₁ : D₁.P.A.left ⟶ T.B.left) (ββ₁ : (G2 D₁.P.A).left ⟶ (G2 T.B).left) (w₁ : LB.Iso (abelian₂ D₁.P.A D₁.P.L) ((abelian₂ T.B T.M.L).pull ββ₁)) (s₂ : I → V) (e₂ : D₂.X ≃+ (Fin T.r → ℤ)) (β₂ : D₂.P.A.left ⟶ T.B.left) (ββ₂ : (G2 D₂.P.A).left ⟶ (G2 T.B).left) (w₂ : LB.Iso (abelian₂ D₂.P.A D₂.P.L) ((abelian₂ T.B T.M.L).pull ββ₂)) (b : D₁.P.A ⟶ D₂.P.A) (φ : D₁.X ≃+ D₂.X) (F : Type) [Field F] [Algebra (FractionRing V) F], 1 ≤ n → (∃ ε₀ : Module.Basis I ℤ (balForms (id : ℤ → ℤ) (Fin T.r → ℤ)), ∀ i, ε i = ε₀ i) → D₁.TauBimult → D₂.TauBimult → From T ω s₁ ε n D₁ e₁ β₁ ββ₁ w₁ → From T ω s₂ ε n D₂ e₂ β₂ ββ₂ w₂ → (∀ i, s₁ i ≠ 0) → (∀ i, s₂ i ≠ 0) → Match D₁ D₂ b φ F → (∀ y, e₂ (φ y) = e₁ y) → b.left ≫ β₂ = β₁ → (∀ a : Fin T.r → ℤ, ∃ (p₁ : QkPt D₁ F n) (p₂ : QkPt D₂ F n), p₁.y = e₁.symm a ∧ TautPt T ω s₁ ε n D₁ e₁ β₁ ββ₁ w₁ F a p₁.g ∧ p₂.y = e₂.symm a ∧ TautPt T ω s₂ ε n D₂ e₂ β₂ ββ₂ w₂ F a p₂.g ∧ QImg b φ p₁ p₂) → s₁ = s₂ := by
  intro o W _ _ _ T I _ ε n V _ _ ω D₁ D₂ s₁ e₁ β₁ ββ₁ w₁ s₂ e₂ β₂ ββ₂ w₂ b φ F _ _ hn hε hD₁ hD₂ hF₁ hF₂ hs₁ hs₂ hM he hb H
  obtain ⟨ε₀, hε₀⟩ := hε
  obtain ⟨hbm, -, -, hu, -⟩ := hM
  let f : V →+* F := (algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V))
  have hf : Function.Injective f :=
    (algebraMap (FractionRing V) F).injective.comp (IsFractionRing.injective V (FractionRing V))
  have key : ∀ c a : Fin T.r → ℤ, ∏ i, f (s₁ i) ^ ε i c a = ∏ i, f (s₂ i) ^ ε i c a := by
    intro c a
    obtain ⟨p₁, p₂, hy₁, ht₁, hy₂, ht₂, p', hy', hA, hE⟩ := H a
    have hg : p'.g = p₂.g := GlobalTheory.T.torsionPoint_torusPart_eq_of_equiv_same_lattice V D₂ hD₂ F n hn p' p₂ (by
      rw [hy', hy₁, hy₂]; apply e₂.injective; rw [he, e₁.apply_symm_apply, e₂.apply_symm_apply]) hE
    rw [hg] at hA
    have hχ : e₁ (φ.symm (e₂.symm c)) = e₂ (e₂.symm c) := by rw [← he, φ.apply_symm_apply]
    obtain ⟨u, hun⟩ := hu (e₂.symm c)
    obtain ⟨k₁, hk₁, hv₁⟩ := ht₁.2 (φ.symm (e₂.symm c))
    obtain ⟨k₂, hk₂, hv₂⟩ := ht₂.2 (e₂.symm c)
    let z : (TF (R := V) F).left := (⊥ : PrimeSpectrum F)
    obtain ⟨J, hJ, -⟩ := exists_good (JN D₁ D₂) (jn_isLB D₁ D₂) z (K := Empty) Empty.elim Empty.elim
      (fun a => a.elim) (fun k => k.elim)
    obtain ⟨J₀, hJ₀, -⟩ := exists_good T.M.L T.M.isLB z (K := Empty) Empty.elim Empty.elim
      (fun a => a.elim) (fun k => k.elim)
    have a₁ := hv₁ z J₀ (rl J) hJ₀ ((isPart_inl D₁.P.L D₂.P.L).good hJ)
    have a₂ := hv₂ z J₀ (rr J) hJ₀ ((isPart_inr D₁.P.L D₂.P.L).good hJ)
    have a₃ := hA.2 (e₂.symm c) u hun z J hJ
    have a₄ := GlobalTheory.T.mumfordBundleIso_comparison_normalisedGenerator T ε n V ω D₁ D₂ s₁ e₁ β₁ ββ₁ w₁ s₂ e₂ β₂ ββ₂ w₂ b hD₁ hD₂ hF₁ hF₂ hbm hb
      (φ.symm (e₂.symm c)) (e₂.symm c) hχ u hun (TF (R := V) F) p₁.g.b z J J₀ hJ hJ₀
    rw [← hA.1] at a₄
    rw [hχ] at a₁
    have hk : k₁ = k₂ := by
      apply gm_unitOn_inj z
      exact cancel_four a₁ a₂ a₃ a₄
    have := congrArg Units.val hk
    rw [hk₁, hk₂, hχ, e₂.apply_symm_apply] at this
    exact this
  simp only [hε₀] at key
  have hx := GlobalTheory.T.eq_of_prod_zpow_symmetricFormBasis_eq F T.r I ε₀ (fun i => f (s₁ i)) (fun i => f (s₂ i))
    (fun i => (map_ne_zero_iff f hf).2 (hs₁ i)) (fun i => (map_ne_zero_iff f hf).2 (hs₂ i)) (fun a b => key a b)
  funext i
  exact hf (congrFun hx i)

end GlobalTheory.TInj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalPointTorusExtensionAdd
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

noncomputable section

namespace GlobalTheory.TInj

theorem toUnit_left_eq {S : Scheme.{0}} (X : Over S) : (toUnit X).left = X.hom := by
  simpa using Over.w (toUnit X)

theorem prod_zpow_add {F : Type} [Field F] {I : Type} [Fintype I] (x : I → F) (p q : I → ℤ)
    (hp : ∏ i, x i ^ p i ≠ 0) (hq : ∏ i, x i ^ q i ≠ 0) :
    ∏ i, x i ^ (p i + q i) = (∏ i, x i ^ p i) * ∏ i, x i ^ q i := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => zpow_add' ?_
  rcases eq_or_ne (x i) 0 with h | h
  · refine Or.inr (Or.inr ⟨?_, ?_⟩)
    · by_contra hn
      exact hp (Finset.prod_eq_zero (Finset.mem_univ i) (by rw [h, zero_zpow _ hn]))
    · by_contra hn
      exact hq (Finset.prod_eq_zero (Finset.mem_univ i) (by rw [h, zero_zpow _ hn]))
  · exact Or.inl h

theorem tautPt_isAdd : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (ω : W →+* V) (s : I → V) (e : D.X ≃+ (Fin T.r → ℤ)) (β : D.P.A.left ⟶ T.B.left) (ββ : (G2 D.P.A).left ⟶ (G2 T.B).left) (w : LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ T.B T.M.L).pull ββ)), D.TauBimult → From T ω s ε n D e β ββ w → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (a a' : Fin T.r → ℤ) (g g' g'' : GtPtF D F), TautPt T ω s ε n D e β ββ w F a g → TautPt T ω s ε n D e β ββ w F a' g' → TautPt T ω s ε n D e β ββ w F (a + a') g'' → g.IsAdd g' g'' := by
  intro o W _ _ _ T I _ ε n V _ _ D ω s e β ββ w hB hF F _ _ a a' g g' g'' hg hg' hg''
  obtain ⟨ρ, hρ⟩ : ∃ ρ : Over.mk ((TF (R := V) F).hom ≫ spMap ω) ⟶ 𝟙_ (Over (Sp W)),
      ρ.left = (TF (R := V) F).hom ≫ spMap ω := ⟨toUnit _, toUnit_left_eq _⟩
  have hpt : ∀ (x : TF (R := V) F ⟶ D.P.A) (b : Fin T.r → ℤ),
      x.left ≫ β = (TF (R := V) F).hom ≫ spMap ω ≫ (T.c₀ b).left → x.left ≫ β = (ρ ≫ T.c₀ b).left :=
    fun x b h => by rw [h, Over.comp_left, hρ, Category.assoc]
  have hb : g''.b = g.b * g'.b := by
    obtain ⟨hpb, hmul⟩ := hF.1
    have e1 := hmul (TF (R := V) F) g.b g'.b (ρ ≫ T.c₀ a) (ρ ≫ T.c₀ a') (hpt _ _ hg.1).symm (hpt _ _ hg'.1).symm
    apply Over.OverMorphism.ext
    apply hpb.hom_ext
    · rw [hpt _ _ hg''.1, ← e1, ← MonObj.comp_mul, ← T.c₀_add]
    · rw [Over.w, Over.w]
  refine (ReciprocityTheory.ChartRestriction.G.Geo.Tor.isAdd_iff g g' g'').2 ⟨hb, fun χ y J hJ => ?_⟩
  obtain ⟨J₀, hJ₀⟩ : ∃ J₀, Good T.M.L y J₀ :=
    ⟨fun ψ => (exists_chart T.M.isLB (ψ y)).choose, fun ψ => (exists_chart T.M.isLB (ψ y)).choose_spec⟩
  obtain ⟨k, hk, hv⟩ := hg.2 χ
  obtain ⟨k', hk', hv'⟩ := hg'.2 χ
  obtain ⟨k'', hk'', hv''⟩ := hg''.2 χ
  have v := hv y J₀ J hJ₀ hJ
  have v' := hv' y J₀ J hJ₀ hJ
  have v'' := hv'' y J₀ J hJ₀ hJ
  have hl : lamVal w (lift (DegPre.cF D F χ) g''.b).left y J₀ J =
      lamVal w (lift (DegPre.cF D F χ) (g.b * g'.b)).left y J₀ J := by rw [hb]
  rw [hl] at v''

  have hkk : k'' = k * k' := by
    refine Units.ext ?_
    rw [Units.val_mul, hk'', hk, hk']
    simp only [map_add]
    exact prod_zpow_add _ _ _ (hk ▸ k.ne_zero) (hk' ▸ k'.ne_zero)
  have hG : gm (𝟙 (TF (R := V) F).left) y ⊤ (unitOn k'') =
      gm (𝟙 (TF (R := V) F).left) y ⊤ (unitOn k) * gm (𝟙 (TF (R := V) F).left) y ⊤ (unitOn k') := by
    rw [hkk, unitOn, unitOn, unitOn, map_mul, map_mul]

  have hyc : (DegPre.cF D F χ).left ≫ β = (ρ ≫ T.c₀ ((n : ℤ) • e χ)).left := by
    rw [Over.comp_left, Category.assoc, hF.2.2.2.1 χ, Over.comp_left, hρ, toUnit_left_eq, Category.assoc]
  have wa := (GlobalTheory.T.mumfordBundleIso_additive_cubicalStructure T ε n V D ω s e β ββ w hB hF (TF (R := V) F) g.b g'.b (DegPre.cF D F χ)
    (ρ ≫ T.c₀ a) (ρ ≫ T.c₀ a') (ρ ≫ T.c₀ ((n : ℤ) • e χ)) (hpt _ _ hg.1) (hpt _ _ hg'.1) hyc y J₀ J hJ₀ hJ).2
  simp only [id] at wa

  have C := isCub_cubV T.cub hJ₀ (T := Over.mk ((TF (R := V) F).hom ≫ spMap ω))
  have hC := (C.s01 (ρ ≫ T.c₀ ((n : ℤ) • e χ)) (ρ ≫ T.c₀ a) (ρ ≫ T.c₀ a')).trans
    (C.s12 (ρ ≫ T.c₀ a) (ρ ≫ T.c₀ ((n : ℤ) • e χ)) (ρ ≫ T.c₀ a'))
  have corr := corr_of_val T.M.isLB
    (t := LB.mulGen T.M.L _ _ _ _ (T.τ₀ (a + a') ((n : ℤ) • e χ))
      (LB.pullGen T.M.L (thφ T.B (x3 T.B)) thε T.cub.t
        (lift (T.c₀ a) (lift (T.c₀ a') (T.c₀ ((n : ℤ) • e χ)))).left))
    (t' := LB.mulGen T.M.L _ _ _ _ (T.τ₀ a ((n : ℤ) • e χ)) (T.τ₀ a' ((n : ℤ) • e χ))) (fun y' J' hJ' =>
      (val_mul hJ' _ _ _).trans (Eq.trans (congrArg (_ * ·) ((val_pull hJ' _ _ _).trans
        (congrArg (fun r => val T.cub.t r y' J') (Category.id_comp _)))) ((T.τ₀_add a a' _ y' J' hJ').trans
          (val_mul hJ' _ _ _).symm)))
  have et := (val_mul hJ₀ _ _ ρ.left).symm.trans ((val_corr hJ₀ corr ρ.left).trans (val_mul hJ₀ _ _ _))
  rw [val_cub T.cub ρ hJ₀] at et
  have sy : ∀ b b', val (T.τ₀ b b') ((TF (R := V) F).hom ≫ spMap ω) y J₀ = val (T.τ₀ b' b) ρ.left y J₀ :=
    fun b b' => (congrArg (fun r => val (T.τ₀ b b') r y J₀) hρ).symm.trans
      (val_corr hJ₀ (corr_of_val T.M.isLB (T.τ₀_symm b b')) ρ.left)
  rw [sy] at v v' v''
  have hth : DVR.th D y J (DVR.cP D (TF (R := V) F) χ) g.b g'.b = cubV D.cub y J (DegPre.cF D F χ) g.b g'.b := rfl
  rw [v, v', v'', hth]
  apply Additive.ofMul.injective
  have a₁ := congrArg Additive.ofMul hG
  have a₂ := congrArg Additive.ofMul wa
  have a₃ := congrArg Additive.ofMul hC
  have a₄ := congrArg Additive.ofMul et
  simp only [ofMul_mul] at a₁ a₂ a₃ a₄ ⊢
  linear_combination (norm := abel) a₁ + a₂ + a₃ + a₄

end GlobalTheory.TInj
end
end

