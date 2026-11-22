import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0003
import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
import Formalism.SharpRestriction.CuspSpanNormBounds.OnePlaceEstimates
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0191
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0115
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0137
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0139
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0151
import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ThetaLeMsupOfSetC
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0042
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0122
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0159
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0133
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0176
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0192
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0178
import Formalism.HermitianCurvature.Bundle0007
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0304
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0002
import Formalism.HermitianCurvature.Bundle0004
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsNormBoundThreeFamilies
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftClosedUnderOperations
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0156
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0160
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Jets.ExistsSecTieFOfTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0033
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0027
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GramSpace
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0026
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0037
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0041
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0039
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroSplitOfLocalAndSum
import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.BesselXiIntegrable
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0185
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0069
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0188
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0072
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0184
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0183
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0093
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0297
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0063
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularityAtPlaceOfSubadditive
import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsLocalSectionBounds
section
open BpJoin Formalism.FourierDecayAlt Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.QuantumDeterminants GlobalTheory.ThA

namespace GlobalTheory

theorem pointwiseBound_at_place_of_locBessel : ThmBpDS → ∀ Ch : ℝ, ∃ C₄ Cg₀ : ℝ, 0 ≤ C₄ ∧ ∀ Cg : ℝ, Cg₀ ≤ Cg → ∀ (D : D7) (L : LocBessel D.R.k D.R.rS) (lam0 : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (f : B.Mat D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp)) (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ) (ka b : ℝ), LocOk D Ch Cg L lam0 ka b 1 → AllGaps lam0 (200 * l1 L.lam lam0) → IsKFinCoefH L.σ f → IsSection D.R.k D.R.rS L.z L.z' μsec → ∃ (U U' : ℕ → ℝ) (p : KB.Pl ⟨D.R.k, D.R.rS, Tz D.R.k D.R.rS L.z, Tz D.R.k D.R.rS L.z', U, U'⟩ L.Wp L.Wq) (n₀ : ℕ), IsStdOf L μsec p.T.base ∧ n₀ ≤ 30 * (D.R.rS + 1) ^ 2 + 6 ∧ TBB.ThmBpAt p f b C₄ n₀ (2 * (D.R.rS + 1)) := by
  classical
  intro hT Ch
  obtain ⟨C₄, G₀, hC₄, h⟩ := hT Ch 2 (by norm_num)
  refine ⟨C₄, G₀, hC₄, fun Cg hCg D L lam0 f μsec ka b hL hg hf hsec => ?_⟩
  obtain ⟨-, hε, -, -, -, hS, -⟩ := hL
  have hk : 2 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  obtain ⟨U, U', p, hU, hstd⟩ :=
    GlobalTheory.T.exists_place_of_localBesselDatum_interlacing D.R.k D.R.rS L μsec lam0 (by omega) hk hsec hS.2.1 hS.2.2.1
  have hu : (fun i : Fin D.R.k => U (i.val + 1)) = L.u := funext fun i => (hU i).1
  have hu' : (fun i : Fin D.R.k => U' (i.val + 1)) = L.u' := funext fun i => (hU i).2
  have he : L.ε = PI.BesselPeriodGGP.eps48 D.R.k D.R.rS := by
    rw [hε]; funext i; rfl
  obtain ⟨v1, v2, -⟩ := GlobalTheory.upqRep_vocabulary_agree D.R.k D.R.rS L.Hs L.σ L.ε L.lam
  have hone : (1 : B.Mat D.R.k D.R.rS) ∈ UH (Hpk D.R.k D.R.rS) := by simp [UH]
  refine ⟨U, U', p, if ∀ i ∈ Finset.Icc 1 D.R.k, U i = U' i then 30 * (D.R.rS + 1) ^ 2 + 6 else 0, hstd,
    by split_ifs <;> omega, ?_⟩
  refine h Cg hCg ⟨D.R.k, D.R.rS, Tz D.R.k D.R.rS L.z, Tz D.R.k D.R.rS L.z', U, U'⟩ L.Wp L.Wq p lam0 L.lam ka b _ _
    ⟨L.Hs, L.σ⟩ f ?_ hg ?_ ?_ (fun e => if_pos e) (fun e => if_neg e) ?_ ?_
  · show StdHyp Ch Cg D.R.k D.R.rS _ lam0 (fun i : Fin D.R.k => U (i.val + 1))
      (fun i : Fin D.R.k => U' (i.val + 1)) _ _ ka b
    rw [hu, hu', ← he]
    exact hS
  · show BranchingSupport.Rep.IsDS (k := D.R.k) (r := D.R.rS) ⟨L.Hs, L.σ⟩ (PI.BesselPeriodGGP.eps48 D.R.k D.R.rS) L.lam
    rw [← he]
    exact ⟨L.hlam, v1.1 L.hσ⟩
  · obtain ⟨P, Q, hQ, hP, hfe⟩ := hf
    exact ⟨1, hone, 1, hone, P, Q, fun w => (v2 _).1 (hQ w), fun x => (v2 _).1 (hP x), fun g => by
      simpa using hfe g⟩
  · show 3 * (D.R.rS + 1) ≤ 2 * (2 * (D.R.rS + 1))
    omega
  · show ((2 * (D.R.rS + 1) : ℕ) : ℝ) ≤ 2 * ((D.R.rS : ℝ) + 1) ^ 2
    have hr : (0 : ℝ) ≤ D.R.rS := Nat.cast_nonneg _
    push_cast
    nlinarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.InertPrimeDepthDataExistsAtPointsProofStatement
section
open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPrimeDepthDataExistsAtPoints_proof : (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], PkgInertSt Xo c := by
  first | exact @GlobalTheory.InertPackage.pkgInert | exact GlobalTheory.InertPackage.pkgInert | (intros; apply GlobalTheory.InertPackage.pkgInert <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LargePrimeDepthDataExistsAtPointsProofStatement
section
open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.largePrimeDepthDataExistsAtPoints_proof : (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], PkgZeroSt Xo c := by
  first | exact @GlobalTheory.LargePkg.pkgZero | exact GlobalTheory.LargePkg.pkgZero | (intros; apply GlobalTheory.LargePkg.pkgZero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LeafDepth2Run
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth

theorem GlobalTheory.RunDepth.leafDepth2_run : (∀ (p : ℕ) [Fact p.Prime], AvFSt p) → (∀ (p : ℕ) [Fact p.Prime], HTFSt p) → ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (T : Core D) (EX : ErrX D) [StarRing (𝓞 D.host.E)] (K : Type) [Field K] [NumberField K] [StarRing K] [Algebra (𝓞 T.Q.c.F) (𝓞 K)] [Algebra.IsIntegral (𝓞 T.Q.c.F) (𝓞 K)] [Algebra (𝓞 D.host.E) K] (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (P : Type) [Group P] [Finite P] (oc : OnConst) (O : OnObj S P oc) (ι : Bs.J → ℕ) (N : IndefNum Bs), LawsM T → RunTie T EX Tp hK O ι → LeafPage O → LeafSizes O → 3 ≤ L.sc.x → (D.R.k : ℝ) * L.sc.b' ≤ L.sc.b → ContentEqualsDatumContent N (numOf D L) ι → LeafDepth2 N O := by
  intro hAv hHT D L Pm Tp hK T EX _ K _ _ _ _ _ _ Bs Df S P _ _ oc O ι N hM hR hPg _ hx hb tF
  have hr1 : 1 ≤ D.R.r := by
    have := D.R.two_le_m; have := D.R.m_add_three_le_k; unfold Ranks.r; omega
  have hn : ∀ j, InR D j → 2 * D.R.f * D.R.r ≤ (lR Tp hK j).n := by
    intro j _
    show _ ≤ Tp.nWn
    refine le_trans ?_ Tp.nW_lo.1
    nlinarith [Nat.mul_le_mul_left (D.R.f * D.R.r) (show 2 ≤ D.R.r + 1 by omega)]
  have hL : LawsPi T (depOf T EX Tp hK) := lawsPi_depRun hM EX _ _ _ _ _ hn
  refine GlobalTheory.T.depthAtTwo_of_unscaled_depth_bound D.host.E T.Q.H T.Q.l T.Q.Dw T.Q.Xo T.Q.c (depOf T EX Tp hK) K Bs Df S P oc O ι N (numOf D L)
    hR.E_eq hR.σ_eq hR.T_eq ⟨hR.jets_eq_fact, hR.g2_eq, hR.cmQuadraticForm_eq_alternatingForm, hR.dd_eq, hR.sm_eq⟩ hL.piSplit hPg tF
    ⟨hR.jets_eq_fact, hR.g2_eq, hR.cmQuadraticForm_eq_alternatingForm, hR.dd_eq, hR.sm_eq⟩ ?_
  intro la hla j
  obtain ⟨Ap, hAp0, hAp, hle⟩ := GlobalTheory.T.sizes_bound_at_two_first_rows_weights D L Pm Tp hK T.Q hM.pins hx hb O.C hPg.1 (ι j) (hR.inR j)
  haveI : Fact (resCharOf la).Prime := ⟨Crude.resCharOf_prime la⟩
  obtain ⟨hsp, h2, hvd, hup⟩ := GlobalTheory.T.hostField_two_conjugate_places_over_two D T.Q.H hM.pins.1.1 (resCharOf la) (hR.sm_eq ▸ hla)
  refine ⟨_, ?_, GlobalTheory.T.unscaledDepth_le_placeOverTwo (resCharOf la) (hAv _) (hHT _) D.host.E T.Q.H (T.Q.Dw (ι j)) T.Q.l (T.Q.Xo (ι j)) T.Q.c
    hR.star_eq D.R.f (D.host.vdH (resCharOf la)) hvd hsp h2 la rfl _ _ _ (fun τ _ _ h => (hL.wts _ (hR.inR j)).1 τ h)
    (DepthTie.card_of_laws T _ hL hM.pins (ι j) (hR.inR j)) Ap hAp0 hAp⟩
  unfold OnObj.sC OnObj.Se
  rw [hR.T_eq, hR.m_eq, hR.vd_eq, hR.wt_eq, hR.f_eq, hR.Sc_eq, hR.eta_eq]
  refine le_trans (mul_le_mul_of_nonneg_left (add_le_add_left ?_ _) (Nat.cast_nonneg _)) hle
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) hAp0
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LeavesSupSpanLemmaSOfFormTieK
section
open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct

namespace GlobalTheory.FormTies

theorem leaves_sup_span_lemmaS_of_formTieK : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (K : Type) [Field K] [NumberField K] [StarRing K] (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (P : Type) [Group P] [Finite P] (oc : OnConst) (O : OnObj S P oc), (∀ (v : HeightOneSpectrum (𝓞 K)) (i : Bs.J), ∃ (T : Full D) (h : LawsP T.toTop) (j : ℕ) (hj : InR D j) (p : ℕ) (_ : Algebra (recB h.toLawsCore).KO K), ∃ z act, ∃ ℓ : P → (LaMod (T.Q.Dw j) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw j) T.Q.l), FormTieK (recPJ h j hj) hinj EX p (kaR Tp hK j) (lR Tp hK j) (fR Tp hK j) Tp.TO O v i z act ∧ IsLevAct T.toTop h j (kaR Tp hK j) ℓ act ∧ LawsFull T ∧ (∀ γ₀ ∈ Formalism.L2.Theta.GQ (T.V j T.σ₀), T.xi (Matrix.GeneralLinearGroup.det (Formalism.L2.Theta.finHom (T.V j T.σ₀) γ₀)) = 1) ∧ OneCover T.toTop j ∧ 0 < p ∧ Formalism.MainNotions.Gaps.EtaleWeightGaps.LatAt (recB h.toLawsCore) j (kaR Tp hK j) ∧ ReciprocityTheory.ChartRestriction.G.PullbackSections.SpanAt (recPJ h j hj) (kaR Tp hK j) ∧ WeightAlgebra.H2 (recPJ h j hj) (scalOfP (recB h.toLawsCore) hinj EX p (kaR Tp hK j) (lR Tp hK j) (fR Tp hK j) Tp.TO) (kaR Tp hK j) (lR Tp hK j) (fR Tp hK j)) → LeafSup O ∧ LeafSpan O ∧ LeafLemmaS O := by
  intro hCI D L Pm Tp hK hinj EX K _ _ _ Bs Df S P _ _ oc O H
  have key : ∀ (v : HeightOneSpectrum (𝓞 K)) (i : Bs.J),
      (IsLatIn ⊤ (O.Ms i) ∧ ∀ g : P, (O.Ms i).map ((O.ρ i g).restrictScalars (𝓞 K)) ≤ O.Ms i) ∧
      (IsLatIn ⊤ (O.Th v i) ∧ IsLatIn ⊤ (O.ThK v i)) ∧
      (O.Th v i ≤ O.Ms i ∧ (∀ g : P, (O.Th v i).map ((O.ρ i g).restrictScalars (𝓞 K)) ≤ O.Th v i) ∧
        O.σ v i ≠ 0 ∧ O.Th v i ≤ Formalism.EigenvalueLevelCeiling.sc (O.σ v i) (O.ThK v i)) := by
    intro v i
    obtain ⟨T, h, j, hj, p, inst, z, act, ℓ, hFK, hA, hFull, hxi, hO, hp, hLat, hSp, hH⟩ := H v i
    obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.RunDepth.run_weights_sum D L Pm Tp hK j hj
    have hF := hFK.toFormTie (shortTh_fg _ hinj EX hp _ _ _ _ hLat hH)
      (productsShort_rec hCI D T.toTop h j hj hFull.sh hO (hFull.lvA j hj 0) _ _ _ _ h1 h2 h3 h4 (kaWt_n _ _ _ _))
    exact ⟨supLattice_isLatIn_stable D _ _ j _ hinj EX p _ _ _ _ K Bs Df S P oc O v i z act hF hLat
        (levAct_mem_Mlat D T.toTop h j hj _ P ℓ act hA),
      theta_spans_isLatIn D _ _ j _ hinj EX p _ _ _ _ K Bs Df S P oc O v i z act hF hp h1 h2 h3 hLat hSp hH,
      GlobalTheory.scaledSpan_clauses D _ _ j _ hinj EX p _ _ _ _ K Bs Df S P oc O v i z act hF h1 h2 h3 hH
        (levAct_theta hCI D T h j hj hFull hxi _ _ _ _ _ h1 h2 h3 h4 P ℓ act hA)⟩
  obtain ⟨v₀, -⟩ := exists_place3 K
  exact ⟨fun i => (key v₀ i).1,
    fun w _ => ⟨fun i => (key w i).2.1, fun i => (key (conjPl w) i).2.1⟩,
    fun w _ => ⟨fun i => (key w i).2.2, fun i => (key (conjPl w) i).2.2⟩⟩

end GlobalTheory.FormTies
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelZeroPairingCutoffLocality
section
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

namespace GlobalTheory

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in

theorem beta_fold_cut_eq_beta_fold_of_cut : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (s : ℂ) (w : List (Bool × ℝ)) (χ : ℝ → ℝ) (δ ε ε₁ : ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), C6.IsCut0 χ → (∀ x, x < δ → χ x = 0) → 0 < ε → 0 < ε₁ → ε₁ < δ * ε → B.CkOn ⊤ (B.GV P.k P.r) F → B.beta p.T.base (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV P.k P.r (a.2 : ℂ) G) ((D.cutF p.T.base χ F ε₁)) w) (D.cutF p.T.base χ F ε) = B.beta p.T.base (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV P.k P.r (a.2 : ℂ) G) (F) w) (D.cutF p.T.base χ F ε) := by
  intro Wp Wq _ _ _ _ _ _ P p s w χ δ ε ε₁ F hχ hδ hε hε₁ hlt hF
  unfold B.beta betaBig
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  by_cases hq : bcWeight P.k P.r (Tz P.k P.r p.T.base.z) (Tz P.k P.r p.T.base.z') q = 0
  · simp only [hq, Complex.ofReal_zero, zero_mul]
  obtain ⟨hgG, -⟩ := Formalism.FourierDecayAlt.P.CutBP.bigCell_pos p q hq
  by_cases hG : Gf P.k P.r p.T.base.z p.T.base.z' (bigCell P.k P.r q.1 (p.T.base.μsec q.2)) < δ * ε
  · have h0 : B.JF p.T.base (D.cutF p.T.base χ F ε) (bigCell P.k P.r q.1 (p.T.base.μsec q.2)) = 0 := by
      rw [Formalism.FourierDecayAlt.P.CutBP.jf_congr_level p.T.base (Y := fun _ => 0) hgG (fun x _ hGx => by
        unfold D.cutF
        rw [hGx, hδ _ ((div_lt_iff₀ hε).2 hG)]
        simp)]
      unfold B.JF besselJ
      simp
    have h1 : B.hsVec (0 : Wq →L[ℂ] Wp) = 0 := by
      unfold B.hsVec
      ext i
      simp
    simp only [h0, h1, inner_zero_left]
  · have hge : ε₁ < Gf P.k P.r p.T.base.z p.T.base.z' (bigCell P.k P.r q.1 (p.T.base.μsec q.2)) :=
      lt_of_lt_of_le hlt (not_lt.1 hG)
    have hU : IsOpen {x : B.Mat P.k P.r | ε₁ < Gf P.k P.r p.T.base.z p.T.base.z' x} :=
      isOpen_lt continuous_const (Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf p.T.base.z p.T.base.z').continuous
    have he : ∀ x ∈ {x : B.Mat P.k P.r | ε₁ < Gf P.k P.r p.T.base.z p.T.base.z' x} ∩ B.GV P.k P.r,
        D.cutF p.T.base χ F ε₁ x = F x := by
      intro x hx
      unfold D.cutF
      rw [hχ.2.2 _ ((one_le_div hε₁).2 (le_of_lt hx.1))]
      simp
    have hcut := Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_cutF p.T.base hχ hF ε₁
    have hlev : ∀ x ∈ B.GV P.k P.r, Gf P.k P.r p.T.base.z p.T.base.z' x =
        Gf P.k P.r p.T.base.z p.T.base.z' (bigCell P.k P.r q.1 (p.T.base.μsec q.2)) →
        x ∈ {x : B.Mat P.k P.r | ε₁ < Gf P.k P.r p.T.base.z p.T.base.z' x} ∩ B.GV P.k P.r :=
      fun x hx hGx => ⟨by show ε₁ < _; rw [hGx]; exact hge, hx⟩
    have key := Formalism.FourierDecayAlt.P.CutBP.jf_congr_level p.T.base hgG (fun x hx hGx =>
      Formalism.FourierDecayAlt.P.CutBP.fold_congr_open s hU hcut hF he w x (hlev x hx hGx))
    exact congrArg (fun A => (bcWeight P.k P.r (Tz P.k P.r p.T.base.z) (Tz P.k P.r p.T.base.z') q : ℂ) *
      inner ℂ (B.hsVec (B.JF p.T.base (D.cutF p.T.base χ F ε) (bigCell P.k P.r q.1 (p.T.base.μsec q.2))))
        (B.hsVec A)) key

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelZeroPairingEqBigCellIntegralTopVectors
section
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.TopVec Filter Topology MeasureTheory

namespace GlobalTheory.TopVecPol

theorem integrable_inner_of_memLp {α E : Type} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {u v : α → E} (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) :
    Integrable (fun c => inner ℂ (u c) (v c)) μ := by
  refine (L2.integrable_inner (𝕜 := ℂ) (hu.toLp u) (hv.toLp v)).congr ?_
  filter_upwards [hu.coeFn_toLp, hv.coeFn_toLp] with c h1 h2
  rw [h1, h2]

theorem integral_inner_expand {α E : Type} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {u v : α → E} (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) (a : ℂ) :
    ∫ c, inner ℂ (u c + a • v c) (u c + a • v c) ∂μ =
      ∫ c, inner ℂ (u c) (u c) ∂μ + a * ∫ c, inner ℂ (u c) (v c) ∂μ +
        (starRingEnd ℂ) a * ∫ c, inner ℂ (v c) (u c) ∂μ +
        a * (starRingEnd ℂ) a * ∫ c, inner ℂ (v c) (v c) ∂μ := by
  have h1 := integrable_inner_of_memLp hu hu
  have h2 := (integrable_inner_of_memLp hu hv).const_mul a
  have h3 := (integrable_inner_of_memLp hv hu).const_mul ((starRingEnd ℂ) a)
  have h4 := (integrable_inner_of_memLp hv hv).const_mul (a * (starRingEnd ℂ) a)
  rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul, ← integral_add h1 h2]
  have h12 : Integrable (fun c => inner ℂ (u c) (u c) + a * inner ℂ (u c) (v c)) μ := h1.add h2
  have h123 : Integrable (fun c => inner ℂ (u c) (u c) + a * inner ℂ (u c) (v c) +
      (starRingEnd ℂ) a * inner ℂ (v c) (u c)) μ := h12.add h3
  rw [← integral_add h12 h3, ← integral_add h123 h4]
  refine integral_congr_ae (Eventually.of_forall fun c => ?_)
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right]
  ring

theorem beta_eq_integral_inner_tv : P5.ThmPActualCpt → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (Cb : ℝ) (H H' : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base H → KB.CptCoef p.T.base H' → KB.CutWord P p.l0 w → B.beta p.T.base (List.foldr (fun (a : Bool × ℝ) G => M.sgn P p.l0 • Q.CV P.k P.r (a.2 : ℂ) G) (H) w) H' = ∫ c, inner ℂ (tv p H' w c) (tv p H w c) := by
  intro hP Wp Wq _ _ _ _ _ _ P p Cb H H' w hD hH hH' hw
  have hS : ∀ (a : ℂ) (x y : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), KB.CptCoef p.T.base x → KB.CptCoef p.T.base y →
      KB.CptCoef p.T.base (x + a • y) := fun a x y hx hy => Formalism.FourierDecayAlt.P.PBL.cpt_add hx (Formalism.FourierDecayAlt.P.PBL.cpt_smul a hy)
  have hcc : ∀ x : B.Mat P.k P.r → (Wq →L[ℂ] Wp), KB.CptCoef p.T.base x → ∀ (A : ℝ) (m : ℕ), B.InCC A m x := by
    intro x hx
    obtain ⟨ε, -, h⟩ := Formalism.FourierDecayAlt.P.TLB.nice_of_cpt hx
    exact h.2.1
  refine GlobalTheory.polarisation_on_subspace (B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (KB.CptCoef p.T.base)
    (fun x y => B.beta p.T.base
      (List.foldr (fun (a : Bool × ℝ) G => M.sgn P p.l0 • Q.CV P.k P.r (a.2 : ℂ) G) x w) y)
    (fun x y => ∫ c, inner ℂ (tv p y w c) (tv p x w c)) hS ?_ ?_ ?_ H H' hH hH'
  · intro a x y hx hy
    have hs := GlobalTheory.T.capelliProduct_levelZeroPairing_sesquilinear P.k P.r Wp Wq p.T.base (M.sgn P p.l0) w (B.AB P.k P.r) le_rfl a
    have hz := hS a x y hx hy
    have e1 := (hs x y (x + a • y) x hx.1 hy.1 (hcc x hx _ _) (hcc y hy _ _) (hcc _ hz _ _) (hcc x hx _ _)).1
    have e2 := (hs x y x y hx.1 hy.1 (hcc x hx _ _) (hcc y hy _ _) (hcc x hx _ _) (hcc y hy _ _)).2
    have e3 := (hs y y x y hy.1 hy.1 (hcc y hy _ _) (hcc y hy _ _) (hcc x hx _ _) (hcc y hy _ _)).2
    beta_reduce
    rw [e1, e2, e3]
    ring
  · intro a x y hx hy
    have hx2 := (GlobalTheory.T.levelZeroForm_eq_bigCell_integral_topDensity_compact hP Wp Wq P p Cb x w hD hx hw).1
    have hy2 := (GlobalTheory.T.levelZeroForm_eq_bigCell_integral_topDensity_compact hP Wp Wq P p Cb y w hD hy hw).1
    have e : ∀ c, tv p (x + a • y) w c = tv p x w c + a • tv p y w c := fun c =>
      GlobalTheory.TopVec.tv_add_smul Wp Wq P p Cb a x y w c hD hw hx hy
    beta_reduce
    simp only [e]
    exact integral_inner_expand hx2 hy2 a
  · intro x hx
    beta_reduce
    rw [(GlobalTheory.T.levelZeroForm_eq_bigCell_integral_topDensity_compact hP Wp Wq P p Cb x w hD hx hw).2, ← integral_complex_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun c => ?_)
    beta_reduce
    rw [inner_self_eq_norm_sq_to_K]
    simp

end GlobalTheory.TopVecPol
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.PackagesExistFrobeniusComplexConjugationStatement
section
open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.packages_exist_frobeniusComplexConjugation : (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], PkgPhiCSt Xo c ∧ PkgZeroCSt Xo c := by
  first | exact @GlobalTheory.PkgConj.packages_conj | exact GlobalTheory.PkgConj.packages_conj | (intros; apply GlobalTheory.PkgConj.packages_conj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SplitPrimeDepthDataExistsAtPointsProofStatement
section
open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPrimeDepthDataExistsAtPoints_proof : (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], PkgSplitSt Xo c := by
  first | exact @GlobalTheory.SplitPackage.pkgSplit | exact GlobalTheory.SplitPackage.pkgSplit | (intros; apply GlobalTheory.SplitPackage.pkgSplit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaLatticeDepthLeUnscaledAddBoundaryStatement
section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps.EtaleWeightGaps
open GlobalTheory.PtTie
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLattice_depth_le_unscaled_add_boundary : (∀ (p : ℕ) [Fact p.Prime], Pdiv.ChartF.HTFSt p) → ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (w : WeightFamilies.Wt D j) (c : ℝ), Oriented T EX → RunNum D w c → ∀ (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : T.PtA j la), (recPJ h j hj).depth (sWt (recB h.toLawsCore) hinj EX w) w la y ≤ ((nusOf (recB h.toLawsCore) w (nuWt T w) la + c * (recPJ h j hj).phiC la y : ℝ) : EReal) := by
  first | exact @GlobalTheory.RecDepth.depth_le | exact GlobalTheory.RecDepth.depth_le | (intros; apply GlobalTheory.RecDepth.depth_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TopDensityDominated
section
namespace GlobalTheory.HatNF

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory

theorem dom_pow_le (G : ℝ) (hG : 0 < G) (m q : ℕ) (h : m ≤ q) : G ^ m ≤ 1 + G ^ q := by
  rcases le_total G 1 with h1 | h1
  · have := pow_le_one₀ (n := m) hG.le h1
    have := pow_pos hG q
    linarith
  · have := pow_le_pow_right₀ h1 h
    linarith

theorem dom_real_bound {ι κ : Type} [Fintype ι] [Fintype κ] (E Ct n D G C S C' : ℝ) (L a p₀ : ℕ)
    (u : ι → ℝ) (v : κ → ℝ) (hCt : 0 ≤ Ct) (hn : 0 ≤ n) (hD : 0 < D) (hG : 0 < G) (hC : 0 ≤ C)
    (hS0 : 0 ≤ S) (hS : S ≤ C' * G ^ p₀) (hu0 : ∀ e, 0 ≤ u e) (hv0 : ∀ t, 0 ≤ v t)
    (hL : L * (1 + 2 * a) ≤ 2 * p₀)
    (hu : ∀ e, u e ≤ C * (D⁻¹ ^ L * G⁻¹ ^ (a * L)) * S * ∑ t, v t)
    (hE : E ≤ Ct * n * (D ^ 2 / G) ^ L * ∑ e, u e ^ 2) :
    E ≤ (Ct * Fintype.card ι * (C * C') ^ 2 * Fintype.card κ) *
      ∑ t, (n * v t ^ 2 + n * ((G ^ p₀) ^ 2 * v t ^ 2)) := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hL
  have hT0 : 0 ≤ ∑ t, v t := Finset.sum_nonneg fun t _ => hv0 t
  have hT : (∑ t, v t) ^ 2 ≤ Fintype.card κ * ∑ t, v t ^ 2 := by
    simpa using sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset κ)) (f := v)
  have hV0 : 0 ≤ ∑ t, v t ^ 2 := Finset.sum_nonneg fun t _ => sq_nonneg _
  have h1 : ∑ e, u e ^ 2 ≤ Fintype.card ι * (C * (D⁻¹ ^ L * G⁻¹ ^ (a * L)) * (C' * G ^ p₀) * ∑ t, v t) ^ 2 := by
    have : ∀ e ∈ (Finset.univ : Finset ι),
        u e ^ 2 ≤ (C * (D⁻¹ ^ L * G⁻¹ ^ (a * L)) * (C' * G ^ p₀) * ∑ t, v t) ^ 2 := by
      intro e _
      refine pow_le_pow_left₀ (hu0 e) ((hu e).trans ?_) 2
      gcongr
    simpa using Finset.sum_le_card_nsmul _ _ _ this
  have h2 : (D ^ 2 / G) ^ L * ((D⁻¹ ^ L * G⁻¹ ^ (a * L)) * G ^ p₀) ^ 2 = G ^ m := by
    have e : (G ^ p₀) ^ 2 = G ^ L * (G ^ (a * L)) ^ 2 * G ^ m := by
      rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
      congr 1
      rw [mul_comm p₀ 2, hm]; ring
    rw [mul_pow, e, div_pow, inv_pow, inv_pow, ← pow_mul D 2 L, mul_comm 2 L, pow_mul D L 2]
    have := pow_pos hD L
    have := pow_pos hG L
    have := pow_pos hG (a * L)
    field_simp
  have h3 : G ^ m ≤ 1 + (G ^ p₀) ^ 2 := by
    rw [← pow_mul]
    exact dom_pow_le G hG _ _ (by omega)
  have h4 : ∑ t, (n * v t ^ 2 + n * ((G ^ p₀) ^ 2 * v t ^ 2)) = n * (1 + (G ^ p₀) ^ 2) * ∑ t, v t ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun t _ => by ring
  calc E ≤ Ct * n * (D ^ 2 / G) ^ L * ∑ e, u e ^ 2 := hE
    _ ≤ Ct * n * (D ^ 2 / G) ^ L *
        (Fintype.card ι * (C * (D⁻¹ ^ L * G⁻¹ ^ (a * L)) * (C' * G ^ p₀) * ∑ t, v t) ^ 2) := by gcongr
    _ = Ct * n * Fintype.card ι * (C * C') ^ 2 *
        ((D ^ 2 / G) ^ L * ((D⁻¹ ^ L * G⁻¹ ^ (a * L)) * G ^ p₀) ^ 2) * (∑ t, v t) ^ 2 := by ring
    _ ≤ Ct * n * Fintype.card ι * (C * C') ^ 2 * (1 + (G ^ p₀) ^ 2) * (Fintype.card κ * ∑ t, v t ^ 2) := by
        rw [h2]; gcongr
    _ = _ := by rw [h4]; ring

theorem dom_thr (Cc r k : ℝ) (N L : ℝ) (hCc : 8 ≤ Cc) (hr : 0 ≤ r) (hk : 0 ≤ k) (hL : L ≤ N) (hN : 0 ≤ N) :
    L * (8 * (r + 1) * (2 * r + k + 1)) ≤ Cc * (r + 1) ^ 4 * (N * (2 * r + k + 1) ^ 2) := by
  have h1 : r + 1 ≤ (r + 1) ^ 4 := le_self_pow₀ (by linarith) (by norm_num)
  have h2 : 2 * r + k + 1 ≤ (2 * r + k + 1) ^ 2 := le_self_pow₀ (by linarith) (by norm_num)
  calc L * (8 * (r + 1) * (2 * r + k + 1)) ≤ N * (Cc * (r + 1) ^ 4 * (2 * r + k + 1) ^ 2) := by
        have : 0 ≤ Cc := by linarith
        gcongr
    _ = _ := by ring

theorem top_density_dominated : GlobalTheory.HCXi.BesselXiIntegrable → ∀ a : ℕ → ℕ, BasicLiftAll a → ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ) (p₀ : ℕ) (χ : ℝ → ℝ) (N : ℕ) (w : List C.Letter), C6.IsCut0 χ → KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A₀ m f) → Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) → N * (1 + 2 * a P.r) ≤ 2 * p₀ → KB.CutWord P p.l0 w → w.length ≤ N → (∀ ε : ℝ, 0 < ε → AEStronglyMeasurable (fun c : Fin (P.r + 1) → ℂ => TBB.Ew p (fun _ => 1) (mulG p.T.base (fun y => χ (y / ε) * y ^ p₀) f) (P.r + 1) w (TBB.bigPt P.r c)) volume) ∧ ∃ h : (Fin (P.r + 1) → ℂ) → ℝ, Integrable h ∧ ∀ ε : ℝ, 0 < ε → ∀ c₀ : Fin (P.r + 1) → ℂ, ‖(fun c : Fin (P.r + 1) → ℂ => TBB.Ew p (fun _ => 1) (mulG p.T.base (fun y => χ (y / ε) * y ^ p₀) f) (P.r + 1) w (TBB.bigPt P.r c)) c₀‖ ≤ h c₀ := by
  intro hXi a ha Cb
  obtain ⟨C1, h1⟩ := GlobalTheory.T.wordBound_smooth_decaying_coefficients a ha Cb
  obtain ⟨C2, h2⟩ := GlobalTheory.T.integrable_emptyWordDensity_decayingCoefficients hXi
  refine ⟨max C1 (max C2 8), ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f A₀ p₀ χ N w hχ hDD hf hfA hth hN hw hwN
  have hc1 : C1 ≤ max C1 (max C2 8) := le_max_left _ _
  have hc2 : C2 ≤ max C1 (max C2 8) := (le_max_left _ _).trans (le_max_right _ _)
  have hc8 : 8 ≤ max C1 (max C2 8) := (le_max_right _ _).trans (le_max_right _ _)
  generalize max C1 (max C2 8) = Cc at hth hc1 hc2 hc8
  obtain ⟨C, J, Θs, hC, hpoly, hb⟩ := h1 Wp Wq P p N w hDD hw hwN
  obtain ⟨hcut, C', hC', hld⟩ := ld_cut_pow χ p₀ J hχ
  obtain ⟨Ct, hCt, htop⟩ := GlobalTheory.TopDensityBound.top_density_le Wp Wq P p w
  constructor
  · intro ε hε
    have hs := (GlobalTheory.HatNF.mulG_ckOn_inCC Wp Wq P p.T.base p₀ 0 _ f A₀ (hcut ε hε) hf (hfA 0)).1
    have hm := GlobalTheory.TopVec.aestronglyMeasurable_tv Wp Wq P p Cb _ w hDD hw hs
    simp only [GlobalTheory.TopVec.Ew_eq_norm_tv_sq]
    exact hm.norm.pow 2
  have hth1 : C1 * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
      A₀ - (2 * (P.r : ℝ) + 2) * p₀ := by
    refine le_trans ?_ (hth.trans (le_of_eq (by push_cast; ring)))
    gcongr
  set d : ℝ := ((w.length * (8 * (P.r + 1) * (2 * P.r + P.k + 1)) : ℕ) : ℝ) with hd
  have hth2 : C2 * ((P.r : ℝ) + 1) ^ 4 * (2 * (P.r : ℝ) + P.k + 1) ^ 3 ≤ A₀ - d - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) := by
    have e1 := dom_thr Cc P.r P.k N w.length hc8 (by positivity) (by positivity) (by exact_mod_cast hwN) (by positivity)
    have e2 : C2 * ((P.r : ℝ) + 1) ^ 4 * (2 * (P.r : ℝ) + P.k + 1) ^ 3 ≤
        Cc * ((P.r : ℝ) + 1) ^ 4 * (2 * (P.r : ℝ) + P.k + 1) ^ 3 := by gcongr
    have e3 : d = (w.length : ℝ) * (8 * ((P.r : ℝ) + 1) * (2 * (P.r : ℝ) + P.k + 1)) := by
      rw [hd]; push_cast; ring
    rw [mul_add] at hth
    linarith
  have hΘ : ∀ t : Fin Θs.length, B.CkOn ⊤ (B.GV P.k P.r) (B.opApply Θs[t.1] f) ∧
      ∀ m : ℕ, B.InCC (A₀ - d) m (B.opApply Θs[t.1] f) := fun t =>
    Formalism.FourierDecayAlt.P.CutMP.class_lower_decay_holds P.k P.r Wp Wq _ d A₀ (by positivity)
      ((polyOp_ok P.k P.r Wp Wq _ _ _ (hpoly _ (List.getElem_mem t.2))).2.1 d le_rfl) f hf hfA
  refine ⟨fun c => (Ct * Fintype.card (Ix (Fin w.length)) * (C * ((J + 1) * C')) ^ 2 * Fintype.card (Fin Θs.length)) *
    ∑ t : Fin Θs.length, (TBB.Ew p (fun _ => 1) (B.opApply Θs[t.1] f) (P.r + 1) [] (TBB.bigPt P.r c) +
      TBB.Ew p (fun _ => 1) (fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ p₀ : ℝ) : ℂ) • B.opApply Θs[t.1] f g)
        (P.r + 1) [] (TBB.bigPt P.r c)), ?_, ?_⟩
  · refine Integrable.const_mul (integrable_finset_sum _ fun t _ => Integrable.add ?_ ?_) _
    · refine h2 Wp Wq P p _ (A₀ - d) (hΘ t).1 (hΘ t).2 (hth2.trans ?_)
      have : (0 : ℝ) ≤ (((2 * P.r + 2) * p₀ : ℕ) : ℝ) := by positivity
      linarith
    · exact h2 Wp Wq P p _ _ (Formalism.FourierDecayAlt.P.CutBP.ckOn_Gpow_smul _ _ p₀ (hΘ t).1)
        (Formalism.FourierDecayAlt.P.CutBP.inCC_Gpow_smul _ _ p₀ (hΘ t).2) hth2
  intro ε hε c
  beta_reduce
  by_cases hc : (∀ l, c l ≠ 0) ∧ 0 < TBB.Gp p (TBB.bigPt P.r c)
  swap
  · rw [(htop _ c).1 hc, norm_zero]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun t _ =>
      add_nonneg (Formalism.FourierDecayAlt.P.TBBx4.ew_nonneg _ _ _) (Formalism.FourierDecayAlt.P.TBBx4.ew_nonneg _ _ _))
  obtain ⟨hc0, hG⟩ := hc
  obtain ⟨hn, -, hE⟩ := (htop (mulG p.T.base (fun y => χ (y / ε) * y ^ p₀) f) c).2 hc0 hG
  have hGp : ∀ F : B.Mat P.k P.r → (Wq →L[ℂ] Wp),
      p.V (fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ p₀ : ℝ) : ℂ) • F g) (TBB.bigPt P.r c) =
        ((TBB.Gp p (TBB.bigPt P.r c) ^ p₀ : ℝ) : ℂ) • p.V F (TBB.bigPt P.r c) := by
    intro F
    by_cases hl : D.IsLocPt (TBB.bigPt P.r c) (P.r + 1)
    · exact Formalism.FourierDecayAlt.P.TBBx4.vec_Gpow p F p₀ hl hG
    · rw [Formalism.FourierDecayAlt.P.TBBx4.V_zero p _ (fun h => hl h.1), Formalism.FourierDecayAlt.P.TBBx4.V_zero p _ (fun h => hl h.1), smul_zero]
  simp only [fun H => ((htop H c).2 hc0 hG).2.1, hGp, Formalism.FourierDecayAlt.P.TBBx4.hsVec_real_smul_sq]
  rw [Real.norm_eq_abs]
  refine dom_real_bound _ Ct _ ‖∏ l, c l‖ _ C
    (∑ j ∈ Finset.range (J + 1), |LE.ld j (fun y => χ (y / ε) * y ^ p₀) (TBB.Gp p (TBB.bigPt P.r c))|) _
    w.length (a P.r) p₀ _ (fun t : Fin Θs.length => ‖B.hsVec (p.V (B.opApply Θs[t.1] f) (TBB.bigPt P.r c))‖)
    hCt hn (norm_pos_iff.mpr (Finset.prod_ne_zero_iff.mpr fun l _ => hc0 l)) hG hC
    (Finset.sum_nonneg fun _ _ => abs_nonneg _) ?_ (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    ((Nat.mul_le_mul_right _ hwN).trans hN) ?_ hE
  · have := Finset.sum_le_card_nsmul (Finset.range (J + 1)) _ _ fun j hj =>
      hld ε _ hε hG j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
    simpa [mul_assoc] using this
  · intro e
    have := hb _ f ⟨p₀, A₀, hcut ε hε, hf, hfA, hth1⟩ e c hc0 hG
    rwa [← Fin.sum_univ_fun_getElem] at this

end GlobalTheory.HatNF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.WignerShiftedPlacesExistProofStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wignerShiftedPlacesExist_proof : GlobalTheory.WigSh.ShiftExists := by
  first | exact @GlobalTheory.wignerShiftedPlacesExist_proof.shiftExists | exact GlobalTheory.wignerShiftedPlacesExist_proof.shiftExists | (intros; apply GlobalTheory.wignerShiftedPlacesExist_proof.shiftExists <;> assumption)
end

