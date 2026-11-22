import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2955
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1224
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1235
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2954
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2731
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1345
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1412
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0085
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0084
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2761
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2624
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2210
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2633
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorPartTorusExtension
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2964
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2827
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0023
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2527
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2511
import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2921
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2956

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SizeBoundsForFamilyStatement
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.size_bounds_for_family : Size → Covers fun Fm x _ ι p i Y PP _ => LawsJ p.T ∧ InR (Fm.D x ι) ((i : ℕ) + 1) ∧ 1 ≤ (Fm.L x ι).sc.L ∧ Real.log Y.d.l₂.M ≤ 30 * (Fm.L x ι).sc.L ∧ fieldSz (Fm.D x ι).host.E ≤ 3 * (Fm.L x ι).sc.L ∧ Real.log ((Fm.D x ι).R.f * (Fm.D x ι).R.r) ≤ (Fm.L x ι).sc.L ∧ 4 ≤ expL (Fm.L x ι).sc.L ∧ (∀ k, (Fm.D x ι).R.r + 1 < (Fm.D x ι).host.g k) ∧ 8 ≤ (Fm.D x ι).R.f ∧ 100 ≤ (Fm.D x ι).R.r ∧ |GlobalTheory.FlatLine.flatDegVal (dat p i) (Formalism.L2.DIV.ofRecord (Fm.D x ι) (Fm.L x ι) p.Del p.h0).logOm| ≤ 9 * (Fm.D x ι).R.r * (Fm.L x ι).sc.L ∧ Real.log (kap p i) ≤ 2 * (Fm.L x ι).sc.L ∧ zBase (Fm.L x ι) ^ 12 ≤ PP ∧ (lenT p i PP : ℝ) * PP ≤ Real.sqrt (Fm.L x ι).sc.b ∧ zed p i PP (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ * (PP * kap p i) ≤ (Fm.L x ι).sc.b ∧ zed p i PP (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ ≤ 1 / 2 ∧ (∀ la ∈ ({(⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁, (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₂} : Set (AllWt.Weight (dat p i))), ∑ τ, ∑ k, |(la τ k : ℝ)| ≤ zBase (Fm.L x ι) ^ 2 * (kap p i / lenT p i PP + 1)) ∧ ∀ j ≤ lenT p i PP, ∑ τ, ∑ k, |((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt j τ k : ℝ)| ≤ zBase (Fm.L x ι) ^ 2 * kap p i := by
  first | exact @GlobalTheory.CovTop.CovSz.size_rows | exact GlobalTheory.CovTop.CovSz.size_rows | (intros; apply GlobalTheory.CovTop.CovSz.size_rows <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionCountContinuousFromAbove
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

namespace GlobalTheory.VolBr

theorem log_add_le_of_mul_le (a b c d e : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (h : a * b ≤ c * d) (hce : c ≤ e) :
    Real.log a + Real.log b ≤ Real.log e + Real.log d := by
  have hab : 1 ≤ a * b := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hcd : 1 ≤ c * d := hab.trans h
  have hc : c ≠ 0 := by rintro rfl; simp at hcd
  have hd : d ≠ 0 := by rintro rfl; simp at hcd
  have he : e ≠ 0 := by omega
  have h1 : Real.log ((a : ℝ) * b) ≤ Real.log ((e : ℝ) * d) := by
    apply Real.log_le_log
    · have : (1 : ℝ) ≤ (a : ℝ) * b := by exact_mod_cast hab
      linarith
    · have : a * b ≤ e * d := h.trans (Nat.mul_le_mul_right d hce)
      exact_mod_cast this
  rwa [Real.log_mul (by exact_mod_cast (by omega : a ≠ 0)) (by exact_mod_cast (by omega : b ≠ 0)),
    Real.log_mul (by exact_mod_cast he) (by exact_mod_cast hd)] at h1

theorem lc_add_A_le : GlobalTheory.Published.ArithHilbertSamuel → GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0})
    [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (b : ℕ) (s t : X.functionField),
    P.Good D b s t → ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ᶠ m : ℕ in atTop,
    P.lc (n * m : ℕ) m 1 ≤ P.lc (n * m : ℕ) 0 1 + ε * ((n : ℝ) * m) ^ (D + 1) := by
  intro hHS hAC k _ X _ p D hD P b s t hG ε hε
  have hfin : ∀ (a c : ℤ) (R : ℝ), (P.Bl a c R).Finite := fun a c R =>
    GlobalTheory.T.hermLineBundlePair_balls_finite hHS k X p D hD P b s t hG a c R hAC
  have hball : ∀ a c : ℤ, IsBallFam (P.H a c) (P.Bl a c) := GlobalTheory.T.isSeminormBallFamily_sectionBalls k X p P
  have hpos : ∀ (a c : ℤ) (R : ℝ), 0 ≤ R → 1 ≤ (P.Bl a c R).ncard := fun a c R hR =>
    Nat.one_le_iff_ne_zero.mpr ((Set.ncard_pos (hfin a c R)).mpr ⟨0, (hball a c).zero_mem R hR⟩).ne'
  obtain ⟨C0, hC0⟩ := GlobalTheory.T.smallSectionCount_le_pow_goodPair hHS hAC k X p D hD P b s t hG
  obtain ⟨δ, hδ, hrad⟩ := GlobalTheory.T.exists_log_ncard_seminormBall_exp_small_le X.functionField (fun N => P.H (N : ℤ) 0) (fun N => P.Bl (N : ℤ) 0) (D + 1)
    (Nat.succ_pos D) (fun N => hball N 0) (fun N R => hfin N 0 R) C0 hC0 (ε / 3) (by positivity)
  obtain ⟨C, hC, hdiv⟩ := GlobalTheory.T.mem_smallSectionBall_of_mul_pow_section k X p D hD P s hG.s_mem.1 hG.s_ne (δ / 2) (by positivity)
  have hdA := GlobalTheory.T.smallSectionCount_nearPowers_le hHS hAC k X p D hD P b s t hG (ε / 3) (by positivity)
  have hn : ∀ᶠ n : ℕ in atTop, (2 * C + 2) / δ ≤ (n : ℝ) ∧ 1 ≤ n :=
    (tendsto_natCast_atTop_atTop.eventually_ge_atTop _).and (eventually_ge_atTop 1)
  filter_upwards [hdA, hn] with n hdAn hnn
  obtain ⟨hnC, hn1⟩ := hnn
  have htend : Tendsto (fun m : ℕ => n * m) atTop atTop :=
    tendsto_atTop_mono (fun m => Nat.le_mul_of_pos_left m hn1) tendsto_id
  filter_upwards [hdAn, htend.eventually hrad, eventually_ge_atTop 1] with m hdm hradm hm1
  have hnδ : 2 * C + 2 ≤ (n : ℝ) * δ := (div_le_iff₀ hδ).mp hnC
  have hm1' : (1 : ℝ) ≤ m := by exact_mod_cast hm1

  have hrad_le : 2 * Real.exp (δ / 2 * ((n * m : ℕ) : ℝ) + C * m) ≤ Real.exp (δ * ((n * m : ℕ) : ℝ)) := by
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp 1; linarith
    calc 2 * Real.exp (δ / 2 * ((n * m : ℕ) : ℝ) + C * m)
        ≤ Real.exp 1 * Real.exp (δ / 2 * ((n * m : ℕ) : ℝ) + C * m) :=
          mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
      _ = Real.exp (1 + (δ / 2 * ((n * m : ℕ) : ℝ) + C * m)) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (δ * ((n * m : ℕ) : ℝ)) := by
          apply Real.exp_le_exp.mpr
          push_cast
          nlinarith [mul_le_mul_of_nonneg_right hnδ (by linarith : (0 : ℝ) ≤ m)]
  have hSsub : {f | f ∈ P.H (n * m : ℕ) 0 ∧ f * s ^ m ∈ P.Bl (n * m : ℕ) m 2} ⊆
      P.Bl (n * m : ℕ) 0 (Real.exp (δ * ((n * m : ℕ) : ℝ))) := by
    rintro f ⟨hf1, hf2⟩
    have hf := hdiv (n * m) m f hf1 hf2
    exact ⟨hf.1, fun σ y => (hf.2 σ y).trans hrad_le⟩
  have hEfin := hfin (n * m : ℕ) 0 (Real.exp (δ * ((n * m : ℕ) : ℝ)))
  have hSfin := hEfin.subset hSsub
  have hlev := GlobalTheory.T.arith_small_sections_encard_mul_le_finite_level k X p D hD P b s t hG (n * m) m (hfin _ _ _)
  rw [← (hfin _ _ _).cast_ncard_eq, ← (hfin _ _ _).cast_ncard_eq, ← hSfin.cast_ncard_eq,
    ← (hfin _ _ _).cast_ncard_eq] at hlev
  norm_cast at hlev
  have hkey := log_add_le_of_mul_le _ _ _ _ _ (hpos _ _ _ zero_le_one) (hpos _ _ _ zero_le_one) hlev
    (Set.ncard_le_ncard hSsub hEfin)
  have hX : (0 : ℝ) ≤ ((n : ℝ) * m) ^ (D + 1) := by positivity
  have hX3 := mul_nonneg (by positivity : (0 : ℝ) ≤ ε / 3) hX
  simp only [Pair.lc] at hdm ⊢
  push_cast at hradm hkey hdm ⊢
  linarith

end GlobalTheory.VolBr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothCoefficientFormsClosedUnderOperations
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

theorem smooth_coeff_closure : ∀ (n : ℕ) (v : V n), (∀ γ : Alt n, (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr ((fun _ : V n => γ) x) S) v)) ∧ (∀ (J : Type) (s : Finset J) (α : J → V n → Alt n), (∀ j ∈ s, ∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (α j x) S) v) → (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (∑ j ∈ s, α j x) S) v)) ∧ (∀ (g : V n → ℂ) (α : V n → Alt n), ContDiffAt ℝ ∞ g v → (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (α x) S) v) → (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (g x • α x) S) v)) ∧ (∀ α β : V n → Alt n, (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (α x) S) v) → (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (β x) S) v) → (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (α x * β x) S) v)) := by
  intro n v
  have hc : ∀ γ : Alt n, (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr ((fun _ : V n => γ) x) S) v) :=
    fun γ S => contDiffAt_const
  have hs : ∀ (J : Type) (s : Finset J) (α : J → V n → Alt n), (∀ j ∈ s, ∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (α j x) S) v) → (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (∑ j ∈ s, α j x) S) v) := by
    intro J s α h S
    simp only [map_sum, Finsupp.coe_finset_sum, Finset.sum_apply]
    exact ContDiffAt.sum fun j hj => h j hj S
  have hg : ∀ (g : V n → ℂ) (α : V n → Alt n), ContDiffAt ℝ ∞ g v → (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (α x) S) v) → (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (g x • α x) S) v) := by
    intro g α h1 h2 S
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact h1.mul (h2 S)
  refine ⟨hc, hs, hg, ?_⟩
  intro α β ha hb U
  have key : ∀ x, α x * β x = ∑ S, (bas n).repr (α x) S • ∑ T, (bas n).repr (β x) T • (bas n S * bas n T) := by
    intro x
    conv_lhs => rw [← (bas n).sum_repr (α x), ← (bas n).sum_repr (β x)]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [smul_mul_assoc, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [mul_smul_comm]
  simp only [key]
  refine hs _ Finset.univ (fun S x => (bas n).repr (α x) S • ∑ T, (bas n).repr (β x) T • (bas n S * bas n T)) (fun S _ => ?_) U
  refine hg _ _ (ha S) ?_
  refine hs _ Finset.univ (fun T x => (bas n).repr (β x) T • (bas n S * bas n T)) (fun T _ => ?_)
  exact hg _ (fun _ => bas n S * bas n T) (hb T) (hc _)

end GlobalTheory.ChernCalc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothCompositionFormStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_composition_form : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n) (f : M → ℝ) (s : Set ℝ) (G : ℝ → ℝ), Continuous f → A.SmoothOn Set.univ (fun y => (f y : ℂ)) →
    IsOpen s → (∀ y, f y ∈ s) → ContDiffOn ℝ (⊤ : ℕ∞) G s →
      Continuous (fun y => G (f y)) ∧ A.SmoothOn Set.univ (fun y => (G (f y) : ℂ)) ∧ A.IsForm (A.fn (fun y => G (f y))) := by
  first | exact @GlobalTheory.SmoothComp.smooth_comp | exact GlobalTheory.SmoothComp.smooth_comp | (intros; apply GlobalTheory.SmoothComp.smooth_comp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothConeSumGeneratorsEqOfCommonInteriorPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothCone_sum_generators_eq_of_common_interiorPoint : ∀ (φ : InvFun ℤ) (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (m m' : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X) (δ' : Fin m' → LinearMap.BilinForm ℤ X), IsCone id φ δ → IsCone id φ δ' → ∀ (c : Fin m → ℕ) (c' : Fin m' → ℕ), (∀ k, 0 < c k) → (∀ k, 0 < c' k) → ∑ k, c k • δ k = ∑ k, c' k • δ' k → ∑ k, δ k = ∑ k, δ' k := by
  first | exact @GlobalTheory.TInj.coneSum_eq | exact GlobalTheory.TInj.coneSum_eq | (intros; apply GlobalTheory.TInj.coneSum_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionOfEighthPowerStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothOfRelativeDimension_of_eighth_power : ∀ {S : Scheme.{0}} [IsIntegral S] (G H : Over S) [GrpObj G] [GrpObj H] (g : ℕ) (pr : Fin 8 → (H ⟶ G)) (huniv : ∀ (T : Over S) (y : Fin 8 → (T ⟶ G)), ∃! x : T ⟶ H, ∀ u, x ≫ pr u = y u) (hG : IsSemiAbelian G) (hH : SmoothOfRelativeDimension (8 * g) H.hom), SmoothOfRelativeDimension g G.hom := by
  first | exact @GlobalTheory.PowDim.smoothOfRelativeDimension_of_eighthPower | exact GlobalTheory.PowDim.smoothOfRelativeDimension_of_eighthPower | (intros; apply GlobalTheory.PowDim.smoothOfRelativeDimension_of_eighthPower <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SncChartSingleEquationStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affine_snc_chart_cartier_single_equation : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp ℂ) (n : ℕ) [SmoothOfRelativeDimension n q] (B : Closeds Y), FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal B) → ∀ (A : CartierDiv Y) (ι : Type) (s : ι → Y.functionField), (∀ i, s i ∈ A.sections) → ∀ y₀ : Y, ∃ (W : Y.Opens) (hW : y₀ ∈ W) (z : Fin n → Γ(Y, W)) (w : Fin n → Y) (u : Fin n → Y.functionFieldˣ) (e : Y.functionFieldˣ) (f : ι → Γ(Y, W)), IsFrame (dOn q z) ∧ (∀ y ∈ W, A.IsEqn y e) ∧ (∀ i, fnOf W (gen_mem hW) (f i) = s i * e) ∧ ∀ (y : Y) (hy : y ∈ W), ∃ J : Finset (Fin n), IsSncChart q n B y W hy z J w u ∧ ∀ j ∈ J, y ∉ Y.basicOpen (z j) := by
  first | exact @GlobalTheory.PairStep.exists_sncChart_isEqn_affine | exact GlobalTheory.PairStep.exists_sncChart_isEqn_affine | (intros; apply GlobalTheory.PairStep.exists_sncChart_isEqn_affine <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecMapCompEqOfCompInjectiveLocalSchemeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.specMap_comp_eq_of_comp_injective_localScheme : ∀ {Y : Scheme.{0}} {W R' V : Type} [CommRing W] [IsLocalRing W] [CommRing R'] [CommRing V] (u : Sp W ⟶ Y) (g₁ g₂ : W →+* R') (η' : R' →+* V), Function.Injective η' → spMap (η'.comp g₁) ≫ u = spMap (η'.comp g₂) ≫ u → spMap g₁ ≫ u = spMap g₂ ≫ u := by
  first | exact @GlobalTheory.TInj.spMap_comp_eq_of_injective | exact GlobalTheory.TInj.spMap_comp_eq_of_injective | (intros; apply GlobalTheory.TInj.spMap_comp_eq_of_injective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusPartGenericFibreClosedFibreDvr
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8

namespace GlobalTheory.Poinc.FibClosed

open GlobalTheory.SplitTorus (torusMap bcMap bcIso)

section General

variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G'] {f : S' ⟶ S}
  {φ : G'.left ⟶ G.left} {X : Type} [AddCommGroup X]

theorem pullTorus_left_comp_iso (h : IsGrpPullback G' G f φ) (i : splitTorus S X ⟶ G) :
    (pullTorus h i).left ≫ h.1.isoPullback.hom = (bcIso f X).hom.left ≫ ((Over.pullback f).map i).left := by
  apply pullback.hom_ext
  · rw [Category.assoc, IsPullback.isoPullback_hom_fst, pullTorus_left, Category.assoc]
    have : ((Over.pullback f).map i).left ≫ pullback.fst G.hom f = pullback.fst (splitTorus S X).hom f ≫ i.left := by
      simp; exact pullback.lift_fst _ _ _
    rw [this, ← Category.assoc, GlobalTheory.SplitTorus.bcIso_hom_fst]
  · rw [Category.assoc, IsPullback.isoPullback_hom_snd, Category.assoc]
    have : ((Over.pullback f).map i).left ≫ pullback.snd G.hom f = pullback.snd (splitTorus S X).hom f := by
      simp; exact pullback.lift_snd _ _ _
    rw [this, Over.w (pullTorus h i)]
    exact (Over.w (bcIso f X).hom).symm

theorem mono_pullTorus (h : IsGrpPullback G' G f φ) (i : splitTorus S X ⟶ G)
    (hc : IsClosedImmersion ((Over.pullback f).map i).left) : Mono (pullTorus h i) := by
  have k := pullTorus_left_comp_iso h i
  have : Mono ((bcIso f X).hom.left ≫ ((Over.pullback f).map i).left) := inferInstance
  rw [← k] at this
  have : Mono (pullTorus h i).left := mono_of_mono _ h.1.isoPullback.hom
  exact (Over.forget _).mono_of_mono_map this

theorem closedImm_of_pullTorus (h : IsGrpPullback G' G f φ) (i : splitTorus S X ⟶ G)
    (hc : IsClosedImmersion (pullTorus h i).left) : IsClosedImmersion ((Over.pullback f).map i).left := by
  have k := pullTorus_left_comp_iso h i
  have e : ((Over.pullback f).map i).left = (bcIso f X).inv.left ≫ (pullTorus h i).left ≫ h.1.isoPullback.hom := by
    rw [k, ← Category.assoc, ← Over.comp_left, Iso.inv_hom_id, Over.id_left, Category.id_comp]
  haveI : IsIso (bcIso f X).inv.left := inferInstanceAs (IsIso ((Over.forget _).map (bcIso f X).inv))
  rw [e]
  infer_instance

theorem isClosedImmersion_of_isTorPart {tι : splitTorus S X ⟶ G} (h : IsTorPart tι) : IsClosedImmersion tι.left := by
  obtain ⟨-, B, _, q, hB, -, hk⟩ := h
  have h₁ : IsClosedImmersion (η[B].left ≫ B.hom) := by
    rw [Over.w]; exact inferInstanceAs (IsClosedImmersion (𝟙 S))
  have h₂ : IsClosedImmersion η[B].left := IsClosedImmersion.of_comp _ B.hom
  exact MorphismProperty.of_isPullback (P := @IsClosedImmersion) (hk.map (Over.forget S)).flip h₂

theorem isIso_torusMap (T : Scheme.{0}) {Y : Type} [AddCommGroup Y] (e : X ≃+ Y) :
    IsIso (torusMap T e.toAddMonoidHom) :=
  ⟨torusMap T e.symm.toAddMonoidHom, by
    rw [← GlobalTheory.SplitTorus.torusMap_comp, ← GlobalTheory.SplitTorus.torusMap_id]; congr 1; ext x; simp, by
    rw [← GlobalTheory.SplitTorus.torusMap_comp, ← GlobalTheory.SplitTorus.torusMap_id]; congr 1; ext x; simp⟩

end General

theorem spMap_fractionRing_closedPoint (V : Type) [CommRing V] [IsDomain V] :
    (spMap (algebraMap V (FractionRing V))) (closedPoint (FractionRing V)) = genericPoint (Sp V) := by
  rw [genericPoint_eq_bot_of_affine]
  apply PrimeSpectrum.ext
  change Ideal.comap (algebraMap V (FractionRing V)) (maximalIdeal (FractionRing V)) = ⊥
  rw [maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot]
  exact (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective V _)

theorem bijective_of_mono_torusMap {κ : Type} [Field κ] {X₀ X₁ : Type} [AddCommGroup X₀] [AddCommGroup X₁]
    [Module.Free ℤ X₀] [Module.Finite ℤ X₀] [Module.Free ℤ X₁] [Module.Finite ℤ X₁]
    (hr : Module.finrank ℤ X₀ = Module.finrank ℤ X₁) (ρ : X₀ →+ X₁) [Mono (torusMap (Sp κ) ρ)] :
    Function.Bijective ρ := by
  have hs : Function.Surjective ρ := by
    let l : X₁ →+ X₁ ⧸ ρ.range := QuotientAddGroup.mk' ρ.range
    have e : torusMap (Sp κ) l ≫ torusMap (Sp κ) ρ =
        torusMap (Sp κ) (0 : X₁ →+ X₁ ⧸ ρ.range) ≫ torusMap (Sp κ) ρ := by
      rw [← GlobalTheory.SplitTorus.torusMap_comp, ← GlobalTheory.SplitTorus.torusMap_comp]
      congr 1
      ext x
      simp [l]
    have e2 := GlobalTheory.SplitTorus.torusMap_injective ((cancel_mono _).1 e)
    intro y
    have hy : QuotientAddGroup.mk' ρ.range y = 0 := DFunLike.congr_fun e2 y
    obtain ⟨x, hx⟩ := (QuotientAddGroup.eq_zero_iff y).1 hy
    exact ⟨x, hx⟩
  let e₀ : X₁ ≃ₗ[ℤ] X₀ := LinearEquiv.ofFinrankEq X₁ X₀ hr.symm
  have hinj := OrzechProperty.injective_of_surjective_endomorphism (e₀.toLinearMap ∘ₗ ρ.toIntLinearMap)
    (e₀.surjective.comp hs)
  exact ⟨fun a b hab => hinj (by simp [hab]), hs⟩

end GlobalTheory.Poinc.FibClosed

namespace GlobalTheory.Poinc.FibClosed

open GlobalTheory.SplitTorus (torusMap bcMap bcIso)

theorem isTorPart_pullTorus_closed : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (G₁ : Over (Sp V)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (X₁ : Type) [AddCommGroup X₁] [Module.Free ℤ X₁] [Module.Finite ℤ X₁] (j : splitTorus (Sp V) X₁ ⟶ G₁), IsMonHom j → ∀ (GK : Over (Sp (FractionRing V))) [GrpObj GK] (ψ : GK.left ⟶ G₁.left) (hψ : IsGrpPullback GK G₁ (spMap (algebraMap V (FractionRing V))) ψ), IsTorPart (pullTorus hψ j) → ∀ (κ : Type) [Field κ] (b : V →+* κ), IsLocalHom b → ∀ (G₀ : Over (Sp κ)) [GrpObj G₀] (ψ₀ : G₀.left ⟶ G₁.left) (hψ₀ : IsGrpPullback G₀ G₁ (spMap b) ψ₀) (X₀ : Type) [AddCommGroup X₀] [Module.Free ℤ X₀] [Module.Finite ℤ X₀] (t₀ : splitTorus (Sp κ) X₀ ⟶ G₀), IsTorPart t₀ → Module.finrank ℤ X₀ = Module.finrank ℤ X₁ → IsTorPart (pullTorus hψ₀ j) := by
  intro V _ _ _ G₁ _ _ hG X₁ _ _ _ j hj GK _ ψ hψ hgen κ _ b hb G₀ _ ψ₀ hψ₀ X₀ _ _ _ t₀ ht₀ hr
  haveI := hj
  let e : X₁ ≃+ (Fin (Module.finrank ℤ X₁) → ℤ) := (Module.finBasis ℤ X₁).equivFun.toAddEquiv
  let u : splitTorus (Sp V) (Fin (Module.finrank ℤ X₁) → ℤ) ⟶ G₁ := torusMap (Sp V) e.toAddMonoidHom ≫ j
  have hu : IsMonHom u := inferInstance
  have hgenU : ∀ (k : Type) [Field k] (g : Sp k ⟶ Sp V), g (closedPoint k) = genericPoint (Sp V) →
      IsClosedImmersion ((Over.pullback g).map u).left := by
    intro k _ g hg
    rw [GlobalTheory.TorusFibreImm.closedImm_iff_residue u k g, hg, ← spMap_fractionRing_closedPoint V,
      ← GlobalTheory.TorusFibreImm.closedImm_iff_residue u (FractionRing V) _]
    refine closedImm_of_pullTorus hψ u ?_
    rw [pullTorus_torusMap_comp, Over.comp_left]
    haveI := isClosedImmersion_of_isTorPart hgen
    haveI := isIso_torusMap (Sp (FractionRing V)) e
    haveI : IsIso (torusMap (Sp (FractionRing V)) e.toAddMonoidHom).left :=
      inferInstanceAs (IsIso ((Over.forget _).map (torusMap (Sp (FractionRing V)) e.toAddMonoidHom)))
    infer_instance
  have hsp := GlobalTheory.TorusFibre.isClosedImmersion_special_of_local V (FractionRing V) G₁ hG _ u hu
    (by
      haveI := hgenU (FractionRing V) _ (spMap_fractionRing_closedPoint V)
      exact (Over.forget _).mono_of_mono_map
        (inferInstanceAs (Mono ((Over.pullback (spMap (algebraMap V (FractionRing V)))).map u).left)))
  have hfib : IsClosedImmersion ((Over.pullback (spMap b)).map u).left := by
    have h2 := (GlobalTheory.TorusFibreImm.closedImm_iff_residue u (ResidueField V) _).1 hsp
    have h3 : (Spec.map (CommRingCat.ofHom (algebraMap V (ResidueField V)))) (closedPoint (ResidueField V)) =
        (spMap b) (closedPoint κ) :=
      (IsLocalRing.comap_closedPoint (residue V)).trans (IsLocalRing.comap_closedPoint b).symm
    rw [GlobalTheory.TorusFibreImm.closedImm_iff_residue, ← h3]
    exact h2
  have hmono : Mono (pullTorus hψ₀ u) := mono_pullTorus hψ₀ u hfib
  have hmono' : Mono (pullTorus hψ₀ j) := by
    have k : pullTorus hψ₀ j = torusMap _ e.symm.toAddMonoidHom ≫ pullTorus hψ₀ u := by
      rw [pullTorus_torusMap_comp, ← Category.assoc, ← GlobalTheory.SplitTorus.torusMap_comp,
        show e.symm.toAddMonoidHom.comp e.toAddMonoidHom = AddMonoidHom.id X₁ from by ext x; simp,
        GlobalTheory.SplitTorus.torusMap_id, Category.id_comp]
    haveI := isIso_torusMap (Sp κ) e.symm
    rw [k]
    infer_instance
  obtain ⟨ρ, hρ⟩ := ht₀.factor (pullTorus hψ₀ j) inferInstance
  haveI : Mono (torusMap (Sp κ) ρ) := by
    rw [hρ] at hmono'
    exact mono_of_mono _ t₀
  have hbij := bijective_of_mono_torusMap (κ := κ) hr ρ
  have h := ht₀.equiv (AddEquiv.ofBijective ρ hbij)
  rw [hρ]
  exact h

end GlobalTheory.Poinc.FibClosed
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareZeroLiftSystemFiltrationDirectSummand
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.LiftSys.summand_of_full : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Good s₀ → RhoBC hI hk s₀ → ∀ S' : Sys I π s₀, S'.Full hI → (∃ N, IsCompl (S'.K hI) N) → ∀ S : Sys I π s₀, (∃ N, IsCompl (S.K hI) N) ∧ S.K hI ⊔ I • (⊤ : Submodule R (Cr hI π s₀)) = S'.K hI ⊔ I • (⊤ : Submodule R (Cr hI π s₀)) := by
  intro R R₀ _ _ I hI π hπ hk X₀ s₀ hG hρ S' hS' hN S
  obtain ⟨N, hN⟩ := hN
  obtain ⟨hinf, hfull⟩ := GlobalTheory.T.squareZeroLiftSystem_filtration_inf_eq_and_full R R₀ I hI π hπ hk X₀ s₀ hG.const S' S
  have hS : S.Full hI := hfull hS'
  have hsup : S.K hI ⊔ I • (⊤ : Submodule R (Cr hI π s₀)) = S'.K hI ⊔ I • (⊤ : Submodule R (Cr hI π s₀)) := by
    ext c
    rw [GlobalTheory.T.mem_liftSystemFiltration_sup_iff_hodgeFiltration R R₀ I hI π hπ hk X₀ s₀ S hρ hS c, GlobalTheory.T.mem_liftSystemFiltration_sup_iff_hodgeFiltration R R₀ I hI π hπ hk X₀ s₀ S' hρ hS' c]
  exact ⟨⟨N, (GlobalTheory.T.isCompl_of_agree_mod_sqZero_ideal R I hI (Cr hI π s₀) (S'.K hI) (S.K hI) N hN hsup).1 hinf.symm⟩, hsup⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkEvaluationRootOfUnityValueMember
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep.BaseTerms

noncomputable section

namespace GlobalTheory.Poinc.Sep.MemberZeta

open GlobalTheory.Points

theorem valR_through_stalk {X : Scheme.{0}} {x : X} {C : Type} [CommRing C] (ψ : X.presheaf.stalk x →+* C)
    {U : X.Opens} (hU : x ∈ U) (a : Γ(X, U)) :
    valR (spMap ψ ≫ X.fromSpecStalk x) U a = ψ (X.presheaf.germ U x hU a) := by
  have h : ⊤ ≤ X.fromSpecStalk x ⁻¹ᵁ U := fun w _ => by
    have : X.fromSpecStalk x w ∈ Set.range (X.fromSpecStalk x) := ⟨w, rfl⟩
    rw [Scheme.range_fromSpecStalk] at this
    exact Specializes.mem_open (x := X.fromSpecStalk x w) this U.isOpen hU
  have e : (X.fromSpecStalk x).appLE U ⊤ h = X.presheaf.germ U x hU ≫ (Scheme.ΓSpecIso _).inv := by
    rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hU, Category.assoc, Category.assoc, ← Functor.map_comp]
    exact congrArg (_ ≫ ·) ((congrArg (_ ≫ ·) ((Spec (X.presheaf.stalk x)).presheaf.map_id _)).trans (Category.comp_id _))
  refine (valR_appLE (spMap ψ) (X.fromSpecStalk x) h (le_preimage_top _) a).symm.trans ?_
  rw [e]
  exact valR_specMap (CommRingCat.ofHom ψ) _

theorem val_germ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω} {V : Type} [CommRing V] [IsDomain V]
    {z : M.Z} (ev : M.Z.presheaf.stalk z →+* V) (x : M.Z.presheaf.stalk z) :
    M.val (jK V ≫ spMap ev ≫ M.Z.fromSpecStalk z) (M.stalkHom z x) = algebraMap V (FractionRing V) (ev x) := by
  obtain ⟨U, hz, f, rfl⟩ := M.Z.presheaf.germ_exist x
  have hr : Set.range (jK V ≫ spMap ev ≫ M.Z.fromSpecStalk z) ⊆ U := by
    rintro _ ⟨w, rfl⟩
    have : (jK V ≫ spMap ev ≫ M.Z.fromSpecStalk z) w ∈ Set.range (M.Z.fromSpecStalk z) := ⟨_, rfl⟩
    rw [Scheme.range_fromSpecStalk] at this
    exact Specializes.mem_open (x := (jK V ≫ spMap ev ≫ M.Z.fromSpecStalk z) w) this U.isOpen hz
  have e : jK V ≫ spMap ev = spMap ((algebraMap V (FractionRing V)).comp ev) := by
    rw [← Spec.map_comp]; rfl
  rw [RatModel.val_eq hr (RatModel.stalkHom_germ hz f).symm]
  show valR _ U f = _
  rw [← Category.assoc, e, valR_through_stalk _ hz]
  rfl

theorem algebraMap_ev_eq_yK : ∀ {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
    (X : Setup F W i) (z : X.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X.ρ.P.A ⟶ X.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V]
    [IsLocalRing V] (ev : X.M.Z.presheaf.stalk z →+* V) (Y : Type) [AddCommGroup Y] (m : ℕ) (t : Fin m → V)
    (δ : Fin m → LinearMap.BilinForm ℤ Y) (𝔪 : UMem X z act V ev Y t δ) (zt : X.M.Z.presheaf.stalk z),
    X.M.stalkHom z zt = algebraMap X.o₁ X.Ω₁ X.S.ζ →
    algebraMap V (FractionRing V) (ev zt) = 𝔪.yK ⟨algebraMap X.o₁ X.Ω₁ X.S.ζ, X.S.R.algebraMap_mem _⟩ := by
  intro g n F W Z i X z act V _ _ _ ev Y _ m t δ 𝔪 zt h
  rw [𝔪.yK_eq]
  exact (val_germ ev zt).symm.trans (congrArg (X.M.val _) h)

end GlobalTheory.Poinc.Sep.MemberZeta
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkHomStalkMapEqFunctionFieldExtensionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stalkHom_stalkMap_eq_functionFieldExtension : ∀ (o₁ Ω₁ o₂ Ω₂ : Type) [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂] [Algebra Ω₁ Ω₂] (M₁ : RatModel o₁ Ω₁) (M₂ : RatModel o₂ Ω₂) (p : M₂.Z ⟶ M₁.Z), M₂.pt ≫ p = spMap (algebraMap Ω₁ Ω₂) ≫ M₁.pt → ∀ (z₂ : M₂.Z) (x : M₁.Z.presheaf.stalk (p z₂)), M₂.stalkHom z₂ ((p.stalkMap z₂).hom x) = algebraMap Ω₁ Ω₂ (M₁.stalkHom (p z₂) x) := by
  first | exact @GlobalTheory.ZH.RatModel.stalkHom_stalkMap_algebraMap | exact GlobalTheory.ZH.RatModel.stalkHom_stalkMap_algebraMap | (intros; apply GlobalTheory.ZH.RatModel.stalkHom_stalkMap_algebraMap <;> assumption)
end

