import Mathlib
import Formalism.HermitianCurvature.BesselNonvanishingReduction
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0154
import Formalism.LocalToGlobal.SiegelLatticeTheory.BesselDiscreteSeries.DecInfPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.GgExistsAddCharNeOne
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.Bundle0001
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0179
import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0004
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AutomorphicArithmetic.CMTraceForms.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Jets.ExistsSecTieFOfTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0038
import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.OEOsInjective
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0033
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0027
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GramSpace
import Formalism.SharpRestriction.Divisibility.WeightAlgebra
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0037
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0041
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0039
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroSplitOfLocalAndSum
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.SpanResCharNeBot
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0141
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0160
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0137
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0143
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0138
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0145
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaGeneratorsLeastValueOverLevelPrime

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DecLowAndDecInfAndKFinSmooth
section
namespace GlobalTheory.DecInputs

theorem decLow_and_decInf_and_kFinSmooth :
    Formalism.FourierDecayAlt.ThreeDimData.DecLow ∧ Formalism.FourierDecayAlt.ThreeDimData.DecInf ∧ PI.KFinSmooth :=
  ⟨GlobalTheory.DecTransport.decLow_holds, Formalism.L2.SG.BesselDiscreteSeries.decInf,
    Formalism.L2.SG.LitS.kFinSmooth_pi Formalism.L2.SG.Pf.admitted.kFinSmooth'⟩

end GlobalTheory.DecInputs
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DepthLeafGoodPrimesOfPointDataStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.FormalSeriesBounds GlobalTheory.GoodDepth GlobalTheory.RunDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.depthLeaf_goodPrimes_of_point_data : ∃ C0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (T : Core D), LawsM T → ∀ (EX : ErrX D) [StarRing (𝓞 D.host.E)] (K : Type) [Field K] [NumberField K] [StarRing K] [Algebra (𝓞 T.Q.c.F) (𝓞 K)] [Algebra.IsIntegral (𝓞 T.Q.c.F) (𝓞 K)] [Algebra (𝓞 D.host.E) K] (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (P : Type) [Group P] [Finite P] (oc : OnConst) (O : OnObj S P oc) (ι : Bs.J → ℕ) (Nm : IndefNum Bs),
  RunTie T EX Tp hK O ι → (∀ j, PkgSt (T.Q.Xo (ι j)) T.Q.c) → C0 ≤ oc.C → LeafPage O → LeafSizes O → 10 ≤ Pm.CnW → 3 ≤ L.sc.x ^ (L.sc.ez / 5) → 3 ≤ L.sc.x → (D.R.k : ℝ) * L.sc.b' ≤ L.sc.b →
  DepthCond.ContentEqualsDatumContent Nm (numOf D L) ι → LeafDepthGood Nm O := by
  first | exact @GlobalTheory.GoodDepth.leafGood_run | exact GlobalTheory.GoodDepth.leafGood_run | (intros; apply GlobalTheory.GoodDepth.leafGood_run <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DepthSumRecord
section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps.EtaleWeightGaps
open GlobalTheory.PtTie GlobalTheory.PlusRec
namespace GlobalTheory.DepthSum

noncomputable def primeBound (N Q q d : ℕ) (g : Fin 2 → ℕ) (a b : ℝ) (p : ℕ) : ℝ :=
  (if p ∈ (Finset.range (N + 1)).filter Nat.Prime then (N : ℝ) / ((p : ℝ) - 1) else 0) +
    ((padicValNat p Q : ℝ) * a + (if p = q then b else 0) + (if p = d then b else 0)) +
    ∑ i : Fin 2, if p = g i then (N : ℝ) / ((g i : ℝ) - 1) else 0

theorem div_pred_nonneg (N : ℕ) {p : ℕ} (hp : p.Prime) : 0 ≤ (N : ℝ) / ((p : ℝ) - 1) := by
  have : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  exact div_nonneg (by positivity) (by linarith)

theorem sum_primeBound (N Q q d : ℕ) (g : Fin 2 → ℕ) (a b : ℝ) (S : Finset ℕ)
    (hA : (Finset.range (N + 1)).filter Nat.Prime ⊆ S) (h2 : Q.primeFactors ⊆ S) (hS : ∀ p ∈ S, p.Prime) (hq : q ∈ S) (hd : d ∈ S) (hg : ∀ i, g i ∈ S) :
    ∑ p ∈ S, primeBound N Q q d g a b p * Real.log p =
      (N : ℝ) * (∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, Real.log p / ((p : ℝ) - 1)) +
        (a * Real.log Q + b * Real.log q + b * Real.log d) + ∑ i : Fin 2, (N : ℝ) / ((g i : ℝ) - 1) * Real.log (g i) := by
  have hQ : ∑ p ∈ S, (padicValNat p Q : ℝ) * a * Real.log p = a * Real.log Q := by
    rw [Real.log_nat_eq_sum_factorization, Finsupp.sum, Nat.support_factorization, Finset.mul_sum]
    symm
    refine Finset.sum_subset_zero_on_sdiff h2 (fun p hp => ?_) fun p hp => ?_
    · obtain ⟨h3, h4⟩ := Finset.mem_sdiff.1 hp
      rw [← Nat.factorization_def _ (hS p h3), Finsupp.notMem_support_iff.1 (Nat.support_factorization Q ▸ h4)]; simp
    · rw [Nat.factorization_def _ (Nat.prime_of_mem_primeFactors hp)]; ring
  unfold primeBound
  simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_mul]
  rw [hQ, Finset.sum_ite_mem, Finset.inter_eq_right.2 hA, Finset.sum_comm]
  simp only [Finset.sum_ite_eq', hq, hd, hg, if_true, Finset.mul_sum]
  congr 2
  refine Finset.sum_congr rfl fun p _ => ?_
  ring

theorem depth_sum {D : D7} (B : WeightFamilies.Prov D) {j : ℕ} (large₂ : SizeData₂ D) (w : WeightFamilies.Wt D j)
    (hn : 2 * D.R.f * D.R.r ≤ w.n) (hL : Real.log (WeightAlgebra.DF w) ≤ 2 * large₂.sc.L)
    (nu : HeightOneSpectrum (𝓞 B.KO) → ℝ) (h0 : ∀ la, 0 ≤ nu la)
    (h1 : ∀ la, nu la ≤ (WeightAlgebra.DF w : ℝ) / ((resCharOf la : ℝ) - 1)) (h2 : ∀ la, WeightAlgebra.DF w < resCharOf la → nu la = 0) :
    (∀ la, 0 ≤ nusOf B w nu la) ∧ (Function.support (nusOf B w nu)).Finite ∧
      (∑ᶠ la, |nusOf B w nu la| * lw B.KO la) ≤ WeightAlgebra.PN D large₂ * w.size := by
  classical
  have hq : D.host.q.Prime := D.host.hyp.1
  have hd : D.host.d.Prime := D.host.hyp.2.1
  have hg := D.host.g_prime
  have hn1 : 1 ≤ w.n := by
    have hf : 1 ≤ D.R.f := by
      unfold Ranks.f Ranks.n
      have := And.intro (Nat.one_le_two_pow (n := D.R.e)) (show 0 < D.R.ord by positivity)
      omega
    have hr : 1 ≤ D.R.r := by
      have := D.R.two_le_m
      have := D.R.m_add_three_le_k
      unfold Ranks.r
      omega
    have : 1 ≤ 2 * D.R.f * D.R.r := Nat.mul_pos (by omega) hr
    omega
  have hpos : ∀ la, 0 ≤ nusOf B w nu la := by
    intro la
    unfold nusOf
    split_ifs with ha hb hc
    · rw [mul_div_assoc]
      exact mul_nonneg (by positivity) (div_pred_nonneg _ (hg _))
    all_goals exact mul_nonneg (by positivity) (add_nonneg (h0 la) (by positivity))
  set N := WeightAlgebra.DF w with hN
  set A := (Finset.range (N + 1)).filter Nat.Prime with hA
  set S : Finset ℕ := A ∪ (D.host.small ∪ {D.host.q, D.host.d, D.host.g 0, D.host.g 1}) with hS
  have hgS : ∀ i, D.host.g i ∈ S := by
    intro i
    fin_cases i <;> simp [hS]
  have e1 : ∀ p, 0 ≤ (if p ∈ A then (N : ℝ) / ((p : ℝ) - 1) else 0) := by
    intro p
    split_ifs with hp
    · exact div_pred_nonneg _ (Finset.mem_filter.1 hp).2
    · exact le_rfl
  have e2 : ∀ (p x c : ℕ), (0 : ℝ) ≤ (if p = x then (c : ℝ) else 0) := by
    intro p x c
    split_ifs <;> positivity
  have e3 : ∀ p i, 0 ≤ (if p = D.host.g i then (N : ℝ) / ((D.host.g i : ℝ) - 1) else 0) := by
    intro p i
    split_ifs with hp
    · exact div_pred_nonneg _ (hg _)
    · exact le_rfl
  have e4 : ∀ la : HeightOneSpectrum (𝓞 B.KO),
      nu la ≤ (if resCharOf la ∈ A then (N : ℝ) / ((resCharOf la : ℝ) - 1) else 0) := by
    intro la
    split_ifs with hp
    · exact h1 la
    · refine (h2 la ?_).le
      by_contra hlt
      exact hp (Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), Crude.resCharOf_prime la⟩)
  have hsm : D.host.small ⊆ S := Finset.subset_union_left.trans Finset.subset_union_right
  have hSp : ∀ p ∈ S, p.Prime := by
    intro p hp
    simp only [hS, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with hp | hp | rfl | rfl | rfl | rfl
    exacts [(Finset.mem_filter.1 hp).2, (D.host.mem_small_iff.1 hp).1, hq, hd, hg _, hg _]
  have hQ : ∀ la : HeightOneSpectrum (𝓞 B.KO), ((D.host.QS : ℕ) : 𝓞 B.KO) ∈ la.asIdeal ↔ resCharOf la ∈ D.host.small :=
    fun la => (UpperTheory.cmDatum_natCast_mem_heightOneSpectrum_iff D.host.toHostRaw B.KO la).1
  have e5 : ∀ p : ℕ, (0 : ℝ) ≤ (padicValNat p D.host.QS : ℝ) * (c2 D w : ℝ) := fun p => by positivity
  have key := GlobalTheory.T.sum_finitePlaces_le_sum_over_primes B.KO (primeBound N D.host.QS D.host.q D.host.d D.host.g (c2 D w) (cHalf w)) S hSp ?_
    (nusOf B w nu) hpos ?_ ?_
  · refine ⟨hpos, key.1, key.2.trans ?_⟩
    rw [sum_primeBound _ _ _ _ _ _ _ S Finset.subset_union_left hsm hSp (by simp [hS]) (by simp [hS]) hgS]
    refine le_trans ?_ (GlobalTheory.T.sum_log_prime_depth_bounds_le_mul_weight_size D large₂ j w hn1 hL)
    have := mul_le_mul_of_nonneg_left (GlobalTheory.T.sum_prime_log_div_pred_le_log_add N) (Nat.cast_nonneg (α := ℝ) N)
    linarith
  · intro p
    unfold primeBound
    exact add_nonneg (add_nonneg (e1 p) (add_nonneg (add_nonneg (e5 _) (e2 _ _ _)) (e2 _ _ _)))
      (Finset.sum_nonneg fun i _ => e3 p i)
  · intro la
    have s3 := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => e3 (resCharOf la) i
    have a1 := e1 (resCharOf la)
    have a2 := e5 (resCharOf la)
    have a3 := e2 (resCharOf la) D.host.q (cHalf w)
    have a4 := e2 (resCharOf la) D.host.d (cHalf w)
    have a5 := e4 la
    unfold nusOf primeBound
    rw [H1algLink.eWL_eq]
    by_cases ha : ∃ i : Fin 2, ((D.host.g i : ℕ) : 𝓞 B.KO) ∈ la.asIdeal
    · rw [dif_pos ha, mul_div_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have hc := (H1algLink.prime_mem_iff la (hg _)).1 (Classical.choose_spec ha)
      have := Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) => e3 (resCharOf la) i)
        (Finset.mem_univ (Classical.choose ha))
      rw [if_pos hc] at this
      linarith
    · rw [dif_neg ha]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      by_cases hb : ((D.host.QS : ℕ) : 𝓞 B.KO) ∈ la.asIdeal
      · rw [if_pos hb, show ringChar (𝓞 B.KO ⧸ la.asIdeal) = resCharOf la from rfl]
        linarith
      · rw [if_neg hb]
        by_cases hc : ((D.host.q : ℕ) : 𝓞 B.KO) ∈ la.asIdeal ∨ ((D.host.d : ℕ) : 𝓞 B.KO) ∈ la.asIdeal
        · rw [if_pos hc]
          rw [H1algLink.prime_mem_iff la hq, H1algLink.prime_mem_iff la hd] at hc
          rcases hc with hc | hc
          · rw [if_pos hc]
            linarith
          · rw [if_pos hc]
            linarith
        · rw [if_neg hc]
          linarith
  · intro la hla
    have hne : ∀ p ∈ S, p.Prime → ((p : ℕ) : 𝓞 B.KO) ∉ la.asIdeal := fun p hp hpp hm =>
      hla ((H1algLink.prime_mem_iff la hpp).1 hm ▸ hp)
    have hnA : resCharOf la ∉ A := fun h => hla (Finset.mem_union_left _ h)
    have a5 := e4 la
    rw [if_neg hnA] at a5
    unfold nusOf
    rw [dif_neg (fun ⟨i, hi⟩ => hne _ (hgS i) (hg i) hi), if_neg (fun h => hla (hsm ((hQ la).1 h))),
      if_neg (not_or.2 ⟨hne _ (by simp [hS]) hq, hne _ (by simp [hS]) hd⟩), le_antisymm a5 (h0 la)]
    simp

theorem depth_sum_record : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (w : WeightFamilies.Wt D j), 2 * D.R.f * D.R.r ≤ w.n → Real.log (WeightAlgebra.DF w) ≤ 2 * large₂.sc.L → WeightedPrimeSumBoundAlt large₂ (recPJ h j hj) w (nusOf (recB h.toLawsCore) w (nuWt T w)) ∧ ∀ (Nd : NormDatum (recB h.toLawsCore)), WeightedPrimeSumBoundAlt large₂ (Nd.X' (recPJ h j hj) (extAll h j hj) (intAtExt_extAll h j hj)) w (nusOf (recB h.toLawsCore) w (nuWt T w)) := by
  intro D T h j hj large₂ w hn hL
  have hb := GlobalTheory.T.unscaledWeightDepth_finite_bounded_above_charts D T h j hj w hn
  have key := depth_sum (recB h.toLawsCore) large₂ w hn hL (nuWt T w) (fun la => (hb la).2.1) (fun la => (hb la).2.2.1)
    (fun la => (hb la).2.2.2.1)
  exact ⟨key, fun _ => key⟩

end GlobalTheory.DepthSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IInfThetaGeneratorsLeLocalDepthPrimeToLevelStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iInf_theta_generators_le_local_depth_prime_to_level : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l),
 letI := H.starRing
 ∀ (nab : NabV Xo c), IsNab Xo c nab → ThValTot Xo c nab → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT → ∀ (P : PELUnif (maximalIdeal T.V) C.I.G), P.TorsionIso → y.IsAlg → ∀ (ϖ : T.V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q → ∀ (Φ M0 : ℝ) (r : ℕ) (b : Module.Basis (Fin r) ℤ P.D.toPre.X), 0 ≤ Φ → (∀ j, (Q (b j) : ℝ) ≤ Φ) → (∀ j z, |((Q (b j + z) - Q (b j) - Q z : ℤ) : ℝ)| ≤ M0 * Q z) → ∀ (α : 𝓞 E), α * star α = ((l.M : ℕ) : 𝓞 E) → l.Mb = Ideal.span {star α} → IsUnit ((l.M : ℕ) : T.V) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n Dg e : ℕ), 1 ≤ n → 0 < e → DF Dw a ≤ Dg → 4 * Dg + 4 ≤ l.M → (Dg : ℝ) * M0 < l.M → (⨅ f ∈ thGen Xo c nab a n, nval T.V e (evI y f)) ≤ nuLocC C e l.M a n + (((Dg : ℝ) ^ 2 * Φ / l.M / e : ℝ) : EReal) := by
  first | exact @GlobalTheory.ThetaLeast.iInf_thGen_le_nuLocC | exact GlobalTheory.ThetaLeast.iInf_thGen_le_nuLocC | (intros; apply GlobalTheory.ThetaLeast.iInf_thGen_le_nuLocC <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LeafDepthLevelRun
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth

namespace GlobalTheory.RunDepth

theorem leafDepthLevel_run : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (T : Core D) (EX : ErrX D) [StarRing (𝓞 D.host.E)] (K : Type) [Field K] [NumberField K] [StarRing K] [Algebra (𝓞 T.Q.c.F) (𝓞 K)] [Algebra.IsIntegral (𝓞 T.Q.c.F) (𝓞 K)] [Algebra (𝓞 D.host.E) K] (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (P : Type) [Group P] [Finite P] (oc : OnConst) (O : OnObj S P oc) (ι : Bs.J → ℕ) (N : IndefNum Bs), LawsM T → RunTie T EX Tp hK O ι → LeafPage O → LeafSizes O → 3 ≤ L.sc.x → (D.R.k : ℝ) * L.sc.b' ≤ L.sc.b → ContentEqualsDatumContent N (numOf D L) ι → LeafDepthLevel N O := by
  intro D L Pm Tp hK T EX _ K _ _ _ _ _ _ Bs Df S P _ _ oc O ι N hM hR hPg _ hx hb tF
  have hL := (GlobalTheory.T.runDepthData_laws_and_finite_local_depth D L Pm Tp hK T EX hM hR.star_eq).1
  refine DepthTie.leafDepthLevel_core T (depOf T EX Tp hK) O ι N (numOf D L) hL hR.E_eq hR.σ_eq hR.nn_eq hR.T_eq
    ⟨hR.jets_eq_fact, hR.g2_eq, hR.cmQuadraticForm_eq_alternatingForm, hR.dd_eq, hR.sm_eq⟩ hR.conj (fun j => GlobalTheory.T.depthParams_plusMinusCounts_eq_kappa D L Pm Tp hK (ι j) (hR.inR j)) hPg tF
    ⟨hR.jets_eq_fact, hR.g2_eq, hR.cmQuadraticForm_eq_alternatingForm, hR.dd_eq, hR.sm_eq⟩ (fun j => (WeightAlgebra.DF (kaR Tp hK (ι j)) : ℝ)) ?_ ?_ ?_
  · intro j
    have h1 : DF (T.Q.Dw (ι j)) ((depOf T EX Tp hK).aL (ι j)) = WeightAlgebra.DF (lR Tp hK (ι j)) :=
      (GlobalTheory.T.weightExponents_embeddings_degree D T.Q hM.pins (ι j) (hR.inR j) (lR Tp hK (ι j))).1
    have h2 := (GlobalTheory.T.mul_rows_scaledWeight_le_kappaRows D L Pm Tp hK (ι j) (plOf D (false, 0))).2.2
    simp only [h1, hR.T_eq]
    exact_mod_cast h2
  · intro j
    have h := (GlobalTheory.T.degree_weightKappa_le_pageBound D L Pm Tp hK hx hb (ι j) (hR.inR j)).2
    rw [hR.jets_eq_fact, hR.g2_eq]
    exact ⟨h 0, h 1⟩
  · intro w _ hw
    have key : ∀ v : HeightOneSpectrum (𝓞 K), plc v = plc w → (plc w : ℝ) - 1 ≤ DepthTie.e2 T.Q.c v := by
      intro v hv
      have hc : resCharOf (placeBelow (K := T.Q.c.F) v) = plc w := (DepthTie.resChar_below v).trans hv
      have hd : resCharOf (placeBelow (K := T.Q.c.F) v) ∣ T.Q.l.M := by
        rw [hc, level_M T hM]
        rcases hw with h | h
        · rw [h, hR.jets_eq_fact]; exact Dvd.intro _ rfl
        · rw [h, hR.g2_eq]; exact Dvd.intro_left _ rfl
      have h := GlobalTheory.T.ramificationIndex_ge_of_resChar_dvd_level _ _ T.Q.l T.Q.c _ hd
      rw [hc] at h
      have h' : plc w ≤ DepthTie.e2 T.Q.c v + 1 := by unfold DepthTie.e2; omega
      have h'' : (plc w : ℝ) ≤ (DepthTie.e2 T.Q.c v : ℝ) + 1 := by exact_mod_cast h'
      linarith
    exact ⟨key w rfl, key _ (plc_conjPl w)⟩

end GlobalTheory.RunDepth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaGeneratorsLeastValueOverLevelPrimeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_generators_least_value_over_level_prime : (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.HTFSt p) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l),
 letI := H.starRing
 ∀ (nab : NabV Xo c), IsNab Xo c nab → ThValTot Xo c nab → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT → ∀ (P : PELUnif (maximalIdeal T.V) C.I.G), P.TorsionIso → y.IsAlg → ∀ (ϖ : T.V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q → ∀ (Φ M0 : ℝ) (r : ℕ) (b : Module.Basis (Fin r) ℤ P.D.toPre.X), 0 ≤ Φ → (∀ j, (Q (b j) : ℝ) ≤ Φ) → (∀ j z, |((Q (b j + z) - Q (b j) - Q z : ℤ) : ℝ)| ≤ M0 * Q z) → ∀ (g g' : ℕ), g.Prime → g'.Prime → g ≠ g' → l.M = g' * g → ∀ (π π' : 𝓞 E), π * star π = (g : 𝓞 E) → π' * star π' = (g' : 𝓞 E) → l.Mb = Ideal.span {π * π'} → (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(g : 𝓞 E)})).card = Module.finrank ℚ E → (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(g : 𝓞 E)})).Nodup → ¬ IsUnit ((g : ℕ) : T.V) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n e : ℕ), (∀ τ, Antitone fun i => a (τ, i)) → 2 * (Dw.p + Dw.q) ≤ n → 1 ≤ n → 0 < e → DF Dw a < g - 1 → 4 * DF Dw a + 4 ≤ g' → (DF Dw a : ℝ) * M0 < g' → (⨅ f ∈ thGen Xo c nab a n, nval T.V e (evI y f)) + nval T.V e (∏ τ : E →+* ℂ, (io (embK c τ (star π * star π'))) ^ (∑ i : Fin (Dw.mult τ), a (τ, i))) ≤ ((((vV T.V ((g : ℕ) : T.Fr) : ℤ) : ℝ) * DF Dw a / (g - 1) + (Dw.p + Dw.q : ℕ) * r * Φ / (4 * g') + 2 * (DF Dw a : ℝ) ^ 2 * Φ / g') / e : ℝ) := by
  first | exact @GlobalTheory.LevelPrimePoint.least_value_le | exact GlobalTheory.LevelPrimePoint.least_value_le | (intros; apply GlobalTheory.LevelPrimePoint.least_value_le <;> assumption)
end

