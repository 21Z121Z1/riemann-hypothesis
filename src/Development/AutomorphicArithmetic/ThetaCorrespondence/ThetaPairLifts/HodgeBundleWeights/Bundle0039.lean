import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3602
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0038
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0029
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0028
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0034
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3607
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3605
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0037
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0031
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0018
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3609
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3610

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.BinomialFlagDimensionDegreeBound
section
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
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CovTop.DgShare
section Weights
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
end Weights
theorem nef_share_lower_bound (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) (hG : GlobalTheory.Published.GrothendieckDeformation) (hQ : GlobalTheory.HSCore.Quoted)
    (hSi : GlobalTheory.Published.SiegelToroidalIntegral) (hFa : GlobalTheory.Published.ToroidalChartsForFan) (hSA : GlobalTheory.Published.SemiAbelianLieSeminegative) {D : D7} {T : CoreJ D}
    (hT : LawsJ T) {j : ℕ} (hp : 1 ≤ (T.Q.Dw j).p) (hq : 1 ≤ (T.Q.Dw j).q) (hf : 2 < Module.finrank ℚ D.host.E / 2)
    (hj : InR D j) (Y : Deep T.toCore j) {e : ℕ} {o : ℝ} (hY : Y.Good e o) (P : WtPar (T.Q.Dw j)) (hB : WtBig P)
    (Z : Comp Y.d.Xo₂ Y.d.c₂) (hbir : BirOn Y.U Z (wtOf _ P.u₁ 0)) :
    (P.T - 1).choose (CompHt.dimFlag (T.Q.Dw j)) * CompHt.compDeg Y.U Z (wtOf _ P.u₁ 0) ≤
      Module.finrank Y.d.c₂.F (cuspOn Y.U Z (wtOf _ (P.wt P.T) 0)) := by
  have hP1 := _root_.GlobalTheory.T.covering_topology_refinement hP
  obtain ⟨g1, g2, g3⟩ := gapGe_of_wtBig hB
  have good : ∀ la, GapGe 1 la → _ := fun la h =>
    _root_.GlobalTheory.T.covering_domain_lattice_regularity hP D T hT j hp hq hf hj Y e o hY la (antitone_of_gapGe hp hq h).1
      (antitone_of_gapGe hp hq h).2
  obtain ⟨TF, R, ω, h⟩ := _root_.GlobalTheory.T.exists_weight_hodge_bundle_generated hP1 hG hQ hP.q15 hP.q16 hSi hFa hSA D T.toCore j Y e o hY hf Z P hB fun i _ => (good _ (g3 i)).1
  obtain ⟨f₁⟩ := nonempty_cuspFrame ((good _ g1).2 Z)
  obtain ⟨f₂⟩ := nonempty_cuspFrame ((good _ g2).2 Z)
  let k : CompHS.Consts := ⟨1, 1, 1, 1, 1, le_rfl, le_rfl, le_rfl⟩
  let th : R.L.Sec := GlobalTheory.CompHS.toSec (R.Δ₁.lift 0)
  obtain ⟨a1, a2⟩ := _root_.GlobalTheory.T.hodge_bundle_isNef_isBig_of_weight hP1 hP.q7 hSi hFa hSA _ _ _ _ _ _ TF Z _ Y.U P R ω _ D _ _ h f₁ f₂ th k hY.geo hB
  have a3 := birational_of_ratGen TF.X Z Y.U P R ω _ _ _ h f₁ f₂ th k
    (ratGen_of_birOn TF.X Z Y.U P.u₁ ⟨R.toModif⟩ hbir)
  exact GlobalTheory.HSCore.CompShare.choose_mul_compDeg_le hQ _ _ _ _ _ _ _ _ Z _ Y.U P R ω _ D _ _ h f₁ f₂ th k a1 a2 a3
theorem choose_mul_compDeg_le_alt : GlobalTheory.CovTop.HypothesesX → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted →
    GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → DeepGood → Size → FlatDeg →
    Covers fun Fm x _ ι p i Y PP _ => ∀ Z, (lenT p i PP - 1).choose (GlobalTheory.CompHt.dimFlag (dat p i)) *
      GlobalTheory.CompHt.compDeg Y.U Z (wtOf (dat p i) (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ :
        WtPar (dat p i)).u₁ 0) ≤
      Module.finrank Y.d.c₂.F (cuspOn Y.U Z (wtOf (dat p i) ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2,
        lenT p i PP⟩ : WtPar (dat p i)).wt (lenT p i PP)) 0)) := by
  intro hX hP hG hQ hSi hKS hSA _ hS _
  have hFa := hKS.toroidalChartsForFan
  have h4 := GlobalTheory.T.size_bounds_for_family hS
  have h5 := _root_.GlobalTheory.T.birOn_weightPair_both_components hX hG hQ hSi hP hS
  unfold Covers at h4 h5
  have all := lifts_and (lifts_and (GlobalTheory.T.weight_parameter_strict_antitone hS) wtBig_run) (lifts_and h4 h5)
  clear h4 h5
  refine Closed.imp all fun Fm _ _ ⟨C, hC, x0, h⟩ => ⟨C, hC, x0, fun x hx hle ι p hp i hi Y hY Z => ?_⟩
  obtain ⟨⟨_, ⟨_, hq⟩, _, hB⟩, _, ⟨_, hz⟩, _, hb⟩ := h x hx hle ι p hp i
  obtain ⟨hp1, hq1, hf, -⟩ := hq hi
  obtain ⟨hT, hj, -⟩ := hz hi Y hY
  exact _root_.GlobalTheory.CovTop.DgShare.nef_share_lower_bound hP hG hQ hSi hFa hSA hT hp1 hq1 hf hj Y hY.1 _ (hB hi) Z (hb hi Y hY Z).1
end GlobalTheory.CovTop.DgShare
end
end

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
theorem _root_.GlobalTheory.T.binomial_flag_dimension_degree_bound_alt : GlobalTheory.CovTop.HypothesesX → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → DeepGood → Size → FlatDeg → Covers fun Fm x _ ι p i Y PP _ => ∀ Z, (lenT p i PP - 1).choose (GlobalTheory.CompHt.dimFlag (dat p i)) * GlobalTheory.CompHt.compDeg Y.U Z (wtOf (dat p i) (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ 0) ≤ Module.finrank Y.d.c₂.F (cuspOn Y.U Z (wtOf (dat p i) ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt (lenT p i PP)) 0)) := by
  first | exact @_root_.GlobalTheory.CovTop.DgShare.choose_mul_compDeg_le_alt | exact _root_.GlobalTheory.CovTop.DgShare.choose_mul_compDeg_le_alt | (intros; apply _root_.GlobalTheory.CovTop.DgShare.choose_mul_compDeg_le_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.RankGrowthBoundSmallScale
section
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
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace GlobalTheory.CovTop.HodgeSteps
theorem covering_goodAt_shift (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) (D : D7) (T : CoreJ D) (hL : LawsJ T) (j : ℕ) (hj : InR D j) (Y : Deep T.toCore j) (e : ℕ)
    (o : ℝ) (hY : Y.Good e o) (hpq : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q)
    (hC : GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum.IsComplexData Y.U (fun _ => D.sp.W j) Y.dict) (hl : ∀ q : ℕ, q.Prime → Y.d.l₂.GoodAt q)
    (hF : GlobalTheory.FlatLine.FlatExists Y.U (xiR D)) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n kc : ℕ) (s : ℤ) (hn : Even n)
    (h : Y.GoodAt (wtOf _ (uWt (T.Q.Dw j) a n kc + s • hodgeWt (T.Q.Dw j)) 0)) : Y.GoodAt (shiftG (T.Q.Dw j) a n s) := by
  obtain ⟨m, rfl⟩ := hn
  have h1 := (((GlobalTheory.T.flatLine_thetaRoot_twist_twistingSection hP.p5 D T.Q.H (T.Q.Dw j) Y.d.l₂ Y.d.Xo₂ Y.d.c₂ D.R.r Y.U _ Y.dict hC hY.geo hpq hl hF
    (_root_.GlobalTheory.T.unramified_points_of_deep_cover hP D T j Y e o hL hj hY) (anchor (T.Q.Dw j) a (m + m) kc) m).2 _ 0).2 h).1
  have e1 : uWt (T.Q.Dw j) a (m + m) kc + s • hodgeWt (T.Q.Dw j) +
      GlobalTheory.FlatLine.parWt (T.Q.Dw j) (anchor (T.Q.Dw j) a (m + m) kc) =
      laOf (T.Q.Dw j) a (m + m) + s • hodgeWt (T.Q.Dw j) := by
    rw [add_right_comm, uWt_add_anchor]
  rw [e1, add_comm (0 : ℤ), AllWt.wtOf_add] at h1
  have e2 : exZ (T.Q.Dw j) (wtOf (T.Q.Dw j) (laOf (T.Q.Dw j) a (m + m)) m + wtOf (T.Q.Dw j) (s • hodgeWt (T.Q.Dw j)) 0) =
      exZ (T.Q.Dw j) (shiftG (T.Q.Dw j) a (m + m) s) := by
    rw [shiftG, FlatTw.exZ_add_eq, FlatTw.exZ_add_eq]
    congr 1
    have := AllWt.exOf_weightOf (Dw := T.Q.Dw j) (fun x => (a x : ℤ)) m
    rw [AllWt.exOf] at this
    rw [laOf, show (m + m) / 2 = m by omega, this, wtZ]
    push_cast
    rw [two_mul]
  have e3 : cuspW Y.d.Xo₂ Y.d.c₂ Y.U
      (wtOf (T.Q.Dw j) (laOf (T.Q.Dw j) a (m + m)) m + wtOf (T.Q.Dw j) (s • hodgeWt (T.Q.Dw j)) 0) =
      cuspW Y.d.Xo₂ Y.d.c₂ Y.U (shiftG (T.Q.Dw j) a (m + m) s) := by
    ext f
    rw [AllWt.mem_cuspW, AllWt.mem_cuspW, e2]
    exact and_congr_right fun _ => forall₂_congr fun σ hσ => by
      rw [AllWt.modelWt_congr (Y.U σ) hσ (hY.unf σ hσ) e2]
  have key : ∀ C C' : Submodule Y.d.c₂.F (Rul Y.d.Xo₂ Y.d.c₂), C = C' →
      ((AllWt.supLat C).FG ∧ Submodule.span Y.d.c₂.F (AllWt.supLat C : Set C) = ⊤) →
      (AllWt.supLat C').FG ∧ Submodule.span Y.d.c₂.F (AllWt.supLat C' : Set C') = ⊤ := by
    rintro C _ rfl h
    exact h
  exact ⟨hasGram_nrm_of_good D _ j Y e o hY _, key _ _ e3 h1.2⟩
theorem rk_le_one_add_min_mul_rk_neg : GlobalTheory.CovTop.HypothesesX → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SemiAbelianLieSeminegative → DeepGood → Size → FlatDeg → Deg → Share → Covers fun Fm x _ ι p i Y PP _ => ∀ s : ℕ, 1 ≤ s → s ≤ 2 → (Y.rk (Gs p i (s * cZero (Fm.D x ι) ((i : ℕ) + 1))) : ℝ) ≤ (1 + min (1 / 2) ((Fm.L x ι).sc.b / (PP * kap p i))) * Y.rk (Gs p i (-(cZero (Fm.D x ι) ((i : ℕ) + 1)))) := by
  intro hX hP hSi hTo hG hQ hN hDG hS hFD hDeg hSh
  refine ((((((((((hDG.and hS).and hFD).and hDeg).and hSh).and (GlobalTheory.T.weight_parameter_strict_antitone hS)).and (GlobalTheory.T.size_bounds_for_family hS)).and
    (_root_.GlobalTheory.T.valuation_multiplicity_run_estimate hP hG hQ hSi hTo hN hDG hS hFD)).and (GlobalTheory.T.flat_line_c1_log_bound hFD)).and wtBig_run).and WtShape.wtN).imp fun Fm CH _ h => ?_
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, -, a1⟩, A, -, a2⟩, _, -, a3⟩, _, -, a4⟩, _, -, a5⟩, _, -, a6⟩, _, -, a7⟩, _, -, a8⟩, _, -, a9⟩,
    _, -, a10⟩, _, -, a11⟩ := h
  obtain ⟨x0, h⟩ := (((((((((a1.and a2).and a3).and a4).and a5).and a6).and a7).and a8).and a9).and a10).and a11
  refine ⟨0, le_rfl, x0, fun x hx hle ι p hp i hi Y hY s hs1 hs2 => ?_⟩
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨b1, b2⟩, b3⟩, b4⟩, b5⟩, b6⟩, b7⟩, b8⟩, b9⟩, b10⟩, b11⟩ := h x hx hle ι p hp
  clear h a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11
  obtain ⟨-, g1, -, -, -, hfin, -, -⟩ := b1 i hi Y hY
  obtain ⟨hb1, -, -, -, -, hbk, hq⟩ := b2 i
  obtain ⟨⟨u1, hu⟩, hq⟩ := hq hi
  obtain ⟨-, hρ0, hρ1, -⟩ := hq u1 hu
  obtain ⟨δ, hδ, hdg⟩ := b4 i hi Y hY u1 hu
  have hsh := b5 i hi Y hY u1 hu
  obtain ⟨hp1, hq1, hf, hu1, hA, -, hanti⟩ := b6 i hi
  obtain ⟨hL, hj, hL1, -, -, -, -, -, hf8, hr100, -, -, hPP, -, hz1, hz2, -⟩ := b7 i hi Y hY
  have hval := b8 i hi Y hY
  obtain ⟨hC, hl, hF, -⟩ := b9 i hi Y hY
  have hgap := (b10 i hi).gaps
  have hdom := (b11 i).dom
  have hfl := b3 i hi Y hY
  clear b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 hq
  rw [← hu1 u1 hu] at hA hanti hz1 hz2 hval hgap
  clear hu1
  generalize (Fm.parT x hx ι).PP = PP at *
  rw [← CompHS.dimFlag_eq] at hgap
  have hd3 : 3 ≤ CompHt.dimFlag (dat p i) := by
    rw [CompHS.dimFlag_eq, FlagTan.dimFlag]
    exact le_trans hf (Nat.le_mul_of_pos_right _ (Nat.choose_pos (by omega)))
  have hPP100 : 100 ≤ PP := by
    refine le_trans ?_ hPP
    have c1 : (8 : ℝ) ≤ (Fm.D x ι).R.f := by exact_mod_cast hf8
    have c2 : (100 : ℝ) ≤ (Fm.D x ι).R.r := by exact_mod_cast hr100
    have c3 : (8 * 100 * 1 : ℝ) ≤ zBase (Fm.L x ι) := by
      unfold zBase
      gcongr
    exact le_trans (by linarith) (le_self_pow₀ (by linarith) (by norm_num))
  have hT : 1000 * (CompHt.dimFlag (dat p i) : ℝ) ^ 2 ≤ lenT p i PP := by
    refine le_trans ?_ (Nat.le_ceil _)
    have c1 := (Fm.D x ι).R.two_le_m
    have c2 := (Fm.D x ι).R.m_add_three_le_k
    have c3 : (0 : ℝ) < (Fm.D x ι).R.m := by exact_mod_cast (by omega : 0 < (Fm.D x ι).R.m)
    have c4 : ((Fm.D x ι).R.m : ℝ) ≤ (Fm.D x ι).R.k := by exact_mod_cast (by omega : (Fm.D x ι).R.m ≤ (Fm.D x ι).R.k)
    have c5 : 1000 ≤ PP ^ 2 := by nlinarith
    rw [le_div_iff₀ c3]
    gcongr
  obtain ⟨a, ha1, ha2⟩ := exists_jet_order _ _ _ (by omega) hT hρ0 hz2
  have hbir := _root_.GlobalTheory.T.birOn_wtOf_of_consecutive_gap_bound hX hG hQ hSi (_root_.GlobalTheory.T.covering_topology_refinement hP) hP.q15 hP.q16 _ p.T hL _ hp1 hq1 Y _ _ hY.1 u1 fun τ a b hb => by
    rw [← gap_eq _ hb]
    refine le_trans ?_ (hgap τ a (hb ▸ b.2))
    exact_mod_cast bir_gap_le _ _ hd3
  have hboth := GlobalTheory.T.componentImageDegree_between_of_proportionality _ _ _ _ _ _ _ Y.U hY.1.unf (_root_.GlobalTheory.T.proportionality_principle_compactification hP hSi hTo hN _ p.T hL _ hp1 hq1 hf hj Y _ _ hY.1).1
    (_root_.GlobalTheory.T.compactification_top_chern_eq_volume hP hSi hTo hN _ p.T hL _ hp1 hq1 hf hj Y _ _ hY.1) u1 (fun τ => (hA τ).1) (fun τ => (hA τ).2) hbir hval
  have hc0 : 1 ≤ cZero (Fm.D x ι) ((i : ℕ) + 1) := by
    have := (cZeroN_isLeast (Fm.D x ι) ((i : ℕ) + 1)).1.2.2
    unfold cZero
    omega
  have ew : uW p i + (s * cZero (Fm.D x ι) ((i : ℕ) + 1)) • hodgeWt (dat p i) =
      fun τ => uM p i τ + (((s + 1 : ℕ) : ℤ) * cZero (Fm.D x ι) ((i : ℕ) + 1)) • hodgeWt (dat p i) τ := by
    funext τ k
    simp only [uM, uW, uMinus, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring
  have em : uW p i + (-(cZero (Fm.D x ι) ((i : ℕ) + 1))) • hodgeWt (dat p i) = uM p i := by
    rw [neg_smul, ← sub_eq_add_neg]
    rfl
  have hl1 : ∀ τ, Antitone ((uW p i + (s * cZero (Fm.D x ι) ((i : ℕ) + 1)) • hodgeWt (dat p i)) τ) := fun τ => by
    rw [ew]
    exact (hanti (s + 1) (by omega) τ).1
  have hl2 : ∀ τ, Antitone (((lenT p i PP + CompHt.dimFlag (dat p i) + 4 : ℕ) : ℤ) • u1 τ -
      (uW p i + (s * cZero (Fm.D x ι) ((i : ℕ) + 1)) • hodgeWt (dat p i)) τ) := fun τ => by
    rw [ew]
    have := (hanti (s + 1) (by omega) τ).2
    rwa [if_neg (Nat.succ_ne_zero s)] at this
  have hl3 : ∀ τ, 1 ≤ gap ((uW p i + (s * cZero (Fm.D x ι) ((i : ℕ) + 1)) • hodgeWt (dat p i)) τ) ((dat p i).p - 1) :=
    fun τ => by
      rw [ew]
      refine le_trans ?_ (le_gap_bar (dat p i) hp1 hq1 (uM p i) τ ?_ _)
      · push_cast
        nlinarith [Int.natCast_nonneg s]
      · simpa using (hanti 0 (by omega) τ).1
  have hev : Even (p.κ i).n := (p.κ i).n_even
  have g2 : Y.GoodAt (Gs p i (s * cZero (Fm.D x ι) ((i : ℕ) + 1))) :=
    _root_.GlobalTheory.CovTop.HodgeSteps.covering_goodAt_shift hP _ p.T hL _ hj Y _ _ hY.1 (le_add_right hp1) hC hl hF _ _ ((Fm.D x ι).R.k - 1) _ hev
      (_root_.GlobalTheory.T.covering_domain_lattice_regularity hP _ p.T hL _ hp1 hq1 hf hj Y _ _ hY.1 _ hl1 hl3).1
  have htw := ((_root_.GlobalTheory.T.twisted_flat_bundle_ranks hP _ p.T hL _ hp1 hq1 hf hj Y _ _ hY.1 _ hfl).2 _ (p.κ i).n ((Fm.D x ι).R.k - 1) · hdom hev)
  rw [htw _ g1, htw _ g2]
  have hk : 0 < PP * kap p i := by linarith
  have hz : zed p i PP u1 ≤ min (1 / 2) ((Fm.L x ι).sc.b / (PP * kap p i)) := le_min hz2 ((le_div_iff₀ hk).2 hz1)
  have hz0 : 0 ≤ zed p i PP u1 := by
    unfold zed
    positivity
  first
    | have hJ := _root_.GlobalTheory.T.jet_rank_complex_le hX hP hSi hTo hG hQ hN
    | have hJ := _root_.GlobalTheory.T.jet_rank_complex_le hP hSi hTo hG hQ hN
  letI := Fintype.ofFinite (Comp Y.d.Xo₂ Y.d.c₂)
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Finset.mul_sum]
  refine Finset.sum_le_sum fun Z _ => ?_
  have d0 : 0 < Y.dg u1 Z := hδ.trans_le (hdg Z).1
  have d1 : (1 - CompHt.rhoB (dat p i) u1) * CompHt.topDeg Y.U Z u1 ≤ Y.dg u1 Z :=
    (CompHt.delPrime_eq Y.U Z (CompHt.vdm_pos fun τ => (hA τ).1).ne').ge.trans (hboth Z Z).1
  have d2 := hJ _ p.T hL _ hp1 hq1 hf hj Y _ _ hY.1 Z u1 _ _ a hgap hl1 hl2 (by
    have h1 : 0 < 1 - CompHt.rhoB (dat p i) u1 := by linarith
    refine lt_of_mul_lt_mul_left ?_ h1.le
    have e1 := mul_le_mul_of_nonneg_left d1 (Nat.cast_nonneg (lenT p i PP + CompHt.dimFlag (dat p i) + 4))
    have e2 := mul_lt_mul_of_pos_right ha1 d0
    linarith)
  calc _ ≤ _ := d2
    _ ≤ (1 + zed p i PP u1) * binT p i PP * Y.dg u1 Z := mul_le_mul_of_nonneg_right ha2 d0.le
    _ ≤ (1 + zed p i PP u1) * Y.rkC (uM p i) Z := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (hsh Z).1 (by linarith)
    _ ≤ _ := by
      rw [← em]
      exact mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
end GlobalTheory.CovTop.HodgeSteps
end
end

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
theorem _root_.GlobalTheory.T.rk_small_scale_le_of_share : GlobalTheory.CovTop.HypothesesX → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SemiAbelianLieSeminegative → DeepGood → Size → FlatDeg → Deg → Share → Covers fun Fm x _ ι p i Y PP _ => ∀ s : ℕ, 1 ≤ s → s ≤ 2 → (Y.rk (Gs p i (s * cZero (Fm.D x ι) ((i : ℕ) + 1))) : ℝ) ≤ (1 + min (1 / 2) ((Fm.L x ι).sc.b / (PP * kap p i))) * Y.rk (Gs p i (-(cZero (Fm.D x ι) ((i : ℕ) + 1)))) := by
  first | exact @_root_.GlobalTheory.CovTop.HodgeSteps.rk_le_one_add_min_mul_rk_neg | exact _root_.GlobalTheory.CovTop.HodgeSteps.rk_le_one_add_min_mul_rk_neg | (intros; apply _root_.GlobalTheory.CovTop.HodgeSteps.rk_le_one_add_min_mul_rk_neg <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ShareStatementOfKnownTheorems
section
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
namespace GlobalTheory.CovTop.ShareRowsNef
section Weights
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
end Weights
theorem nef_share_lower_bound (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) (hSI : GlobalTheory.Published.SiegelToroidalIntegral) (hKS : GlobalTheory.Published.ToroidalForFanKS)
    (hG : GlobalTheory.Published.GrothendieckDeformation) (hQ : GlobalTheory.HSCore.Quoted) (hSL : GlobalTheory.Published.SemiAbelianLieSeminegative) {D : D7} {T : CoreJ D}
    (hT : LawsJ T) {j : ℕ} (hp : 1 ≤ (T.Q.Dw j).p) (hq : 1 ≤ (T.Q.Dw j).q) (hf : 2 < Module.finrank ℚ D.host.E / 2) (hj : InR D j)
    (Y : Deep T.toCore j) {e : ℕ} {o : ℝ} (hY : Y.Good e o) (P : WtPar (T.Q.Dw j)) (hB : WtBig P)
    (Z : Comp Y.d.Xo₂ Y.d.c₂) (hbir : BirOn Y.U Z (wtOf _ P.u₁ 0)) :
    (((P.T - 1).choose (CompHt.dimFlag (T.Q.Dw j)) : ℕ) : ℝ) * Y.dg P.u₁ Z ≤ Y.rkC (P.wt P.T) Z := by
  have hP1 := _root_.GlobalTheory.T.covering_topology_refinement hP
  obtain ⟨g1, g2, g3⟩ := gapGe_of_wtBig hB
  have good : ∀ la, GapGe 1 la → _ := fun la h =>
    _root_.GlobalTheory.T.covering_domain_lattice_regularity hP D T hT j hp hq hf hj Y e o hY la (antitone_of_gapGe hp hq h).1 (antitone_of_gapGe hp hq h).2
  obtain ⟨TF, R, ω, h⟩ := _root_.GlobalTheory.T.exists_weight_hodge_bundle_generated hP1 hG hQ hP.q15 hP.q16 hSI hKS.toroidalChartsForFan hSL D T.toCore j Y e o hY hf Z P hB fun i _ => (good _ (g3 i)).1
  obtain ⟨f₁⟩ := nonempty_cuspFrame ((good _ g1).2 Z)
  obtain ⟨f₂⟩ := nonempty_cuspFrame ((good _ g2).2 Z)
  let k : CompHS.Consts := ⟨1, 1, 1, 1, 1, le_rfl, le_rfl, le_rfl⟩
  let th : R.L.Sec := GlobalTheory.CompHS.toSec (R.Δ₁.lift 0)
  have hA := _root_.GlobalTheory.T.hodge_bundle_isNef_isBig_of_weight hP1 hQ.nef hSI hKS.toroidalChartsForFan hSL _ _ _ _ _ _ TF Z _ Y.U P R ω _ D _ _ h f₁ f₂ th k hY.geo hB
  have a3 := GlobalTheory.T.hilbertSamuel_map_birational_of_cuspForms_generate TF.X Z Y.U P R ω _ _ _ h f₁ f₂ th k (GlobalTheory.T.cuspForm_ratios_generate_at_flagSpace_genericPoint TF.X Z Y.U P.u₁ ⟨R.toModif⟩ hbir)
  obtain ⟨a1, a2⟩ := hA
  have key := GlobalTheory.T.choose_mul_componentDegree_le_dimension hQ _ _ _ _ _ _ _ _ Z _ Y.U P R ω _ D _ _ h f₁ f₂ th k a1 a2 a3
  have hr : rankOn Y.U Z (wtOf _ (P.wt P.T) 0) = Module.finrank Y.d.c₂.F (cuspOn Y.U Z (wtOf _ (P.wt P.T) 0)) := by
    rw [rankOn, Formalism.HN.rkK, ((good _ (g3 P.T)).2 Z).2.2, finrank_top]
  rw [← hr] at key
  exact_mod_cast key
theorem nef_share_upper_bound (hX : GlobalTheory.CovTop.HypothesesX) (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) (hSI : GlobalTheory.Published.SiegelToroidalIntegral) (hKS : GlobalTheory.Published.ToroidalForFanKS) (hG : GlobalTheory.Published.GrothendieckDeformation) (hQ : GlobalTheory.HSCore.Quoted)
    (hSL : GlobalTheory.Published.SemiAbelianLieSeminegative) {D : D7} {T : CoreJ D}
    (hT : LawsJ T) {j : ℕ} (hp : 1 ≤ (T.Q.Dw j).p) (hq : 1 ≤ (T.Q.Dw j).q) (hf : 2 < Module.finrank ℚ D.host.E / 2) (hj : InR D j)
    (Y : Deep T.toCore j) {e : ℕ} {o : ℝ} (hY : Y.Good e o) (P : WtPar (T.Q.Dw j)) (hB : WtBig P)
    (hs : ∀ τ, StrictAnti (P.u₁ τ) ∧ StrictAnti (CompHt.uPrime _ P.u₁ τ))
    (hbir : ∀ Z, BirOn Y.U Z (wtOf _ P.u₁ 0))
    (hV : ∀ Z, ValMult Y.U Z (wtOf _ P.u₁ 0) (wtOf _ (CompHt.uPrime _ P.u₁) 0))
    (h0 : 0 ≤ CompHt.rhoB _ P.u₁) (h1 : CompHt.rhoB _ P.u₁ ≤ 1 / 2) (la : AllWt.Weight (T.Q.Dw j)) (hla : ∀ τ, Antitone (la τ))
    (hd : ∀ τ, Antitone (((P.T + CompHt.dimFlag (T.Q.Dw j) + 3 : ℕ) : ℤ) • P.u₁ τ - la τ))
    (Z : Comp Y.d.Xo₂ Y.d.c₂) (hδ : 0 < Y.dg P.u₁ Z) :
    (1 - 7 * ((CompHt.dimFlag (T.Q.Dw j) : ℝ) ^ 2 / P.T + CompHt.dimFlag (T.Q.Dw j) * CompHt.rhoB _ P.u₁)) * Y.rkC la Z ≤
      (((P.T - 1).choose (CompHt.dimFlag (T.Q.Dw j)) : ℕ) : ℝ) * Y.dg P.u₁ Z := by
  have hD := GlobalTheory.CompHS.dimFlag_eq (T.Q.Dw j)
  have hg := hB.gaps
  have hT1 := hB.le_T
  have hD2 := two_le_dimFlag hp hq hf
  rw [← hD] at hg hT1 hD2
  have hle := (GlobalTheory.T.componentImageDegree_between_of_proportionality _ _ _ _ _ _ _ Y.U hY.unf (_root_.GlobalTheory.T.proportionality_principle_compactification hP hSI hKS hSL D T hT j hp hq hf hj Y e o hY).1
    (_root_.GlobalTheory.T.compactification_top_chern_eq_volume hP hSI hKS hSL D T hT j hp hq hf hj Y e o hY) P.u₁ (fun τ => (hs τ).1) (fun τ => (hs τ).2) hbir hV Z Z).1
  rw [CompHt.delPrime_eq _ _ (CompHt.vdm_pos fun τ => (hs τ).1).ne'] at hle
  set ρ := CompHt.rhoB _ P.u₁ with hρ
  set n := P.T + CompHt.dimFlag (T.Q.Dw j) + 3 with hn
  have hρ1 : 0 < 1 - ρ := by linarith
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have ha1 : ((⌊(n : ℝ) / (1 - ρ)⌋₊ : ℕ) : ℝ) ≤ n / (1 - ρ) := Nat.floor_le (by positivity)
  have ha2 : (n : ℝ) / (1 - ρ) < (⌊(n : ℝ) / (1 - ρ)⌋₊ : ℕ) + 1 := Nat.lt_floor_add_one _
  have ha3 : n ≤ ⌊(n : ℝ) / (1 - ρ)⌋₊ := Nat.le_floor (by rw [le_div_iff₀ hρ1]; nlinarith)
  have hjet := _root_.GlobalTheory.T.jet_rank_complex_le hX hP hSI hKS hG hQ hSL D T hT j hp hq hf hj Y e o hY Z P.u₁ la n ⌊(n : ℝ) / (1 - ρ)⌋₊ hg hla hd (by
    have h2 : CompHt.topDeg Y.U Z P.u₁ ≤ Y.dg P.u₁ Z / (1 - ρ) := by
      rw [le_div_iff₀ hρ1, mul_comm]; exact hle
    calc (n : ℝ) * CompHt.topDeg Y.U Z P.u₁ ≤ n * (Y.dg P.u₁ Z / (1 - ρ)) := mul_le_mul_of_nonneg_left h2 hn0
      _ = n / (1 - ρ) * Y.dg P.u₁ Z := by ring
      _ < _ := mul_lt_mul_of_pos_right ha2 hδ)
  refine GlobalTheory.share_bound_of_jet_count _ _ _ ρ _ _ hD2 hT1 h0 h1 ha3 ?_ hδ.le (Nat.cast_nonneg _) hjet
  rw [hn] at ha1 ⊢
  push_cast at ha1 ⊢
  exact ha1
theorem share_of_deg : GlobalTheory.CovTop.HypothesesX → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS →
    GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SemiAbelianLieSeminegative →
    DeepGood → Size → FlatDeg → Deg → Share := by
  intro hX hP hSI hKS hG hQ hSL hDG hS hF hD
  have h1 := hS
  have h2 := hF
  have h3 := hD
  have h4 := GlobalTheory.T.size_bounds_for_family hS
  have h5 := _root_.GlobalTheory.T.valuation_multiplicity_run_estimate hP hG hQ hSI hKS hSL hDG hS hF
  have h6 := _root_.GlobalTheory.T.birOn_weightPair_both_components hX hG hQ hSI hP hS
  unfold Size at h1
  unfold FlatDeg Covers at h2
  unfold Deg Covers at h3
  unfold Covers at h4 h5 h6
  have all := lifts_and (lifts_and (lifts_and (lifts_and h1 h2) (lifts_and h3 wtBig_run))
    (lifts_and (GlobalTheory.T.weight_parameter_strict_antitone hS) h4)) (lifts_and h5 h6)
  clear h1 h2 h3 h4 h5 h6
  refine Closed.imp all fun Fm _ _ ⟨C, hC, x0, h⟩ => ⟨C, hC, x0, fun x hx hle ι p hp i hi Y hY u1 hu Z => ?_⟩
  obtain ⟨⟨_, ⟨_, ⟨_, ⟨_, hs⟩, _, hfl⟩, _, ⟨_, hdg⟩, _, hB⟩, _, ⟨_, hq⟩, _, hz⟩, _, ⟨_, hv⟩, _, hbi⟩ := h x hx hle ι p hp i
  obtain ⟨hp1, hq1, hf, hqu, hsa, ⟨w, -, hw⟩, hdom⟩ := hq hi
  obtain ⟨hT, hj, -⟩ := hz hi Y hY
  obtain ⟨-, h0, -, hz1⟩ := (hs.2.2.2.2.2.2 hi).2 u1 hu
  obtain ⟨δ, hδ, hδ2⟩ := hdg hi Y hY u1 hu
  obtain rfl := hqu u1 hu
  have htw := (_root_.GlobalTheory.T.twisted_flat_bundle_ranks hP _ p.T hT _ hp1 hq1 hf hj Y _ _ hY.1 _ (hfl hi Y hY)).1
  refine ⟨?_, ?_⟩
  · rw [hw, htw]
    exact _root_.GlobalTheory.CovTop.ShareRowsNef.nef_share_lower_bound hP hSI hKS hG hQ hSL hT hp1 hq1 hf hj Y hY.1 _ (hB hi) Z (hbi hi Y hY Z).1
  · have hD2 : (2 : ℝ) ≤ CompHt.dimFlag (dat p i) := by
      rw [GlobalTheory.CompHS.dimFlag_eq]; exact_mod_cast two_le_dimFlag hp1 hq1 hf
    refine _root_.GlobalTheory.CovTop.ShareRowsNef.nef_share_upper_bound hX hP hSI hKS hG hQ hSL hT hp1 hq1 hf hj Y hY.1 _ (hB hi) hsa (fun Z => (hbi hi Y hY Z).1) (hv hi Y hY) h0 ?_ (uM p i) (fun τ => ?_) (fun τ => ?_) Z
      (hδ.trans_le (hδ2 Z).1)
    · unfold zed at hz1
      have : 0 ≤ (CompHt.dimFlag (dat p i) : ℝ) ^ 2 / lenT p i (Fm.parT x hx ι).PP := by positivity
      nlinarith [mul_le_mul_of_nonneg_right hD2 h0]
    · simpa using (hdom 0 (by norm_num) τ).1
    · simpa using (hdom 0 (by norm_num) τ).2
end GlobalTheory.CovTop.ShareRowsNef
end
end

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
theorem _root_.GlobalTheory.T.share_of_prints_deg_flatDeg : GlobalTheory.CovTop.HypothesesX → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SemiAbelianLieSeminegative → DeepGood → Size → FlatDeg → Deg → Share := by
  first | exact @_root_.GlobalTheory.CovTop.ShareRowsNef.share_of_deg | exact _root_.GlobalTheory.CovTop.ShareRowsNef.share_of_deg | (intros; apply _root_.GlobalTheory.CovTop.ShareRowsNef.share_of_deg <;> assumption)
end
end

