import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3589
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0029
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0037
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3597
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3591
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0034
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0031
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0030
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0028
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3594
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3599
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankComponentWeightInvariance
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0014
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3600

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.BirOnWeightPairBothComponents
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
namespace GlobalTheory.HSApp
theorem birOn_u₁_u₂_alt : GlobalTheory.CovTop.HypothesesX → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → Size → Covers fun Fm x _ ι p i Y PP _ => ∀ Z, BirOn Y.U Z (wtOf (dat p i) (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ 0) ∧ BirOn Y.U Z (wtOf (dat p i) (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₂ 0) := by
  intro hX hG hQ hSi hP2 hS
  have hP := _root_.GlobalTheory.T.covering_topology_refinement hP2
  have hBir : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q →
      ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ (u : GlobalTheory.AllWt.Weight (T.Q.Dw j)),
      (∀ τ (a b : Fin ((T.Q.Dw j).p + (T.Q.Dw j).q)), (b : ℕ) = a + 1 →
        (((CompHt.dimFlag (T.Q.Dw j) + 3) ^ 2 + 2 * ((T.Q.Dw j).p + (T.Q.Dw j).q) : ℕ) : ℤ) ≤ u τ a - u τ b) →
      ∀ Z : Comp Y.d.Xo₂ Y.d.c₂, BirOn Y.U Z (wtOf (T.Q.Dw j) u 0) :=
    _root_.GlobalTheory.T.birOn_wtOf_of_consecutive_gap_bound hX hG hQ hSi hP hP2.q15 hP2.q16
  refine Closed.imp (((GlobalTheory.T.size_bounds_for_family hS).and (GlobalTheory.T.weight_parameter_strict_antitone hS)).and wtBig_run) ?_
  rintro eps Fm CH - ⟨⟨⟨C1, -, H1⟩, ⟨C2, -, H2⟩⟩, ⟨C3, -, H3⟩⟩
  refine ⟨0, le_rfl, ?_⟩
  obtain ⟨x0, H⟩ := (H1.and H2).and H3
  refine ⟨x0, fun x hx hle ι p hp i hi Y hY => ?_⟩
  obtain ⟨⟨a1, a2⟩, a3⟩ := H x hx hle ι p hp
  have s1 := a1 i hi Y hY
  have s2 := a2 i hi
  have hB := a3 i hi
  intro Z
  have G := gaps_u₁_u₂_of_wtBig _ hB
  exact ⟨hBir (Fm.D x ι) p.T s1.1 ((i : ℕ) + 1) s2.1 s2.2.1 Y _ _ hY.1 _ (fun τ a b h => (G τ a b h).1) Z,
    hBir (Fm.D x ι) p.T s1.1 ((i : ℕ) + 1) s2.1 s2.2.1 Y _ _ hY.1 _ (fun τ a b h => (G τ a b h).2) Z⟩
end GlobalTheory.HSApp
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
theorem _root_.GlobalTheory.T.birOn_weightPair_both_components : GlobalTheory.CovTop.HypothesesX → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → Size → Covers fun Fm x _ ι p i Y PP _ => ∀ Z, BirOn Y.U Z (wtOf (dat p i) (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ 0) ∧ BirOn Y.U Z (wtOf (dat p i) (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₂ 0) := by
  first | exact @_root_.GlobalTheory.HSApp.birOn_u₁_u₂_alt | exact _root_.GlobalTheory.HSApp.birOn_u₁_u₂_alt | (intros; apply _root_.GlobalTheory.HSApp.birOn_u₁_u₂_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CoveringDegreeMultiplicative
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
namespace GlobalTheory.CovTop.DegProof
set_option maxHeartbeats 1000000 in
theorem covering_degree_eq : HypothesesX → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.GrothendieckDeformation →
    GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SemiAbelianLieSeminegative → DeepGood → Size → FlatDeg → Deg := by
  intro hX h2 hS hT hG hQ hN hDG hSz hF
  have hP := _root_.GlobalTheory.T.covering_topology_refinement h2
  refine Closed.imp (Closed.and (Closed.and (_root_.GlobalTheory.T.valuation_multiplicity_run_estimate h2 hG hQ hS hT hN hDG hSz hF) wtBig_run)
    (Closed.and (Closed.and (GlobalTheory.T.weight_parameter_strict_antitone hSz) (GlobalTheory.T.size_bounds_for_family hSz)) hDG)) ?_
  rintro eps Fm CH - ⟨⟨⟨_, -, a₁⟩, _, -, a₂⟩, ⟨⟨_, -, a₃⟩, _, -, a₄⟩, _, -, a₅⟩
  obtain ⟨x0, a⟩ := (a₁.and a₂).and ((a₃.and a₄).and a₅)
  clear a₁ a₂ a₃ a₄ a₅
  refine ⟨0, le_rfl, x0, fun x hx hle ι p hp i hi Y hY u1 hu1 => ?_⟩
  obtain ⟨⟨a₁, a₂⟩, ⟨a₃, a₄⟩, a₅⟩ := a x hx hle ι p hp
  clear a
  obtain ⟨hp1, hq1, hE, hQuo, hAnti, -, -⟩ := a₃ i hi
  obtain ⟨hLaw, hIn, -⟩ := a₄ i hi Y hY
  obtain ⟨-, -, -, -, -, -, ⟨Z'⟩, -⟩ := a₅ i hi Y hY
  have hW := a₂ i hi
  have hV := a₁ i hi Y hY
  rw [hQuo u1 hu1]
  have hPr := _root_.GlobalTheory.T.proportionality_principle_compactification h2 hS hT hN _ p.T hLaw _ hp1 hq1 hE hIn Y _ _ hY.1
  have hEq := _root_.GlobalTheory.T.compactification_top_chern_eq_volume h2 hS hT hN _ p.T hLaw _ hp1 hq1 hE hIn Y _ _ hY.1
  have hBir := _root_.GlobalTheory.T.birOn_wtOf_of_consecutive_gap_bound hX hG hQ hS hP h2.q15 h2.q16 _ p.T hLaw _ hp1 hq1 Y _ _ hY.1 _ (fun τ a b hab => by
    have hb := b.2
    have h := hW.gaps τ a (by rw [← hab]; exact hb)
    rw [gap_eq _ hab] at h
    refine le_trans ?_ h
    have e : ∀ d C N : ℕ, (d + 3) ^ 2 + 2 * N ≤ (d + 3) * (C + 4 * N + d + 3) := fun d C N => by nlinarith
    rw [GlobalTheory.CompHS.dimFlag_eq]
    exact_mod_cast e _ _ _)
  have key := GlobalTheory.T.componentImageDegree_between_of_proportionality _ _ _ _ _ _ _ Y.U hY.1.unf hPr.1 hEq _ (fun τ => (hAnti τ).1) (fun τ => (hAnti τ).2) hBir hV
  refine ⟨CompHt.delPrime Y.U Z' _, ?_, fun Z => key Z Z'⟩
  exact mul_pos (hPr.2 Z') (Int.cast_pos.2 (CompHt.vdm_pos fun τ => (hAnti τ).2))
end GlobalTheory.CovTop.DegProof
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
theorem _root_.GlobalTheory.T.covering_degree_multiplicative : GlobalTheory.CovTop.HypothesesX → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SemiAbelianLieSeminegative → DeepGood → Size → FlatDeg → Deg := by
  first | exact @_root_.GlobalTheory.CovTop.DegProof.covering_degree_eq | exact _root_.GlobalTheory.CovTop.DegProof.covering_degree_eq | (intros; apply _root_.GlobalTheory.CovTop.DegProof.covering_degree_eq <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.DeepGoodReductionStatement
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
namespace GlobalTheory.CovTop.DeepGoodAll
theorem deepGood_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted →
    GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → DeepGood := by
  intro hP hG hQ hS hT hN
  have R := GlobalTheory.T.weight_conditions_at_index
  have P := _root_.GlobalTheory.T.covers_rk_pos_of_semiAbelianLieSeminegative hP hG hQ hS hT hN
  unfold DeepGood Covers Lifts at *
  refine (R.and P).imp fun Fm CH _ h => ?_
  obtain ⟨⟨C1, h1, e1⟩, ⟨C2, h2, e2⟩⟩ := h
  refine ⟨C1, h1, ?_⟩
  obtain ⟨x0, hx0⟩ := e1.and e2
  refine ⟨x0, fun x hx hle ι p hp i hi Y hY => ?_⟩
  obtain ⟨hA, hB⟩ := hx0 x hx hle ι p hp
  obtain ⟨hL, hp1, hq1, hf, hj, hn, hu1, hu2, hs⟩ := hA i hi
  have hpos := hB i hi Y hY
  have hYg := hY.1
  have g := fun s hs' => _root_.GlobalTheory.T.covering_shift_preserves_goodAt hP _ p.T hL _ hp1 hq1 hf hj Y _ _ hYg (wtA (p.κ i)) (p.κ i).n s hn
    (hs s hs').1 (hs s hs').2
  have hon := _root_.GlobalTheory.T.covering_domain_lattice_regularity hP _ p.T hL _ hp1 hq1 hf hj Y _ _ hYg (uM p i) hu1 hu2
  refine ⟨?_, g _ (Or.inl rfl), g _ (Or.inr (Or.inr rfl)), hon.1, hpos, CompFin.finite_comp _ _,
    GlobalTheory.CovTop.good_comp_nonempty _ p.T hL _ hj Y _ _ hYg, hon.2⟩
  have := g 0 (Or.inr (Or.inl rfl))
  rwa [shiftG_zero] at this
end GlobalTheory.CovTop.DeepGoodAll
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
theorem _root_.GlobalTheory.T.deepGood_of_published_inputs : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → DeepGood := by
  first | exact @_root_.GlobalTheory.CovTop.DeepGoodAll.deepGood_alt | exact _root_.GlobalTheory.CovTop.DeepGoodAll.deepGood_alt | (intros; apply _root_.GlobalTheory.CovTop.DeepGoodAll.deepGood_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.GeometricOfHyp
section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace GlobalTheory.CovHt.GeomBound
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)
theorem geometric_height_bound_at_place (hX : GlobalTheory.CovTop.HypothesesX) (hG : GlobalTheory.Published.GrothendieckDeformation) (hQ : GlobalTheory.HSCore.Quoted)
    (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) (hS1 : GlobalTheory.Published.SiegelToroidalIntegral) (hS2 : GlobalTheory.Published.ToroidalForFanKS)
    (hS3 : GlobalTheory.Published.SemiAbelianLieSeminegative)
    {PP C A M : ℝ} (hsz : SizeAt p i PP C) (hN : HostNum D L PP A M) (hw : WtNum p i PP) (hi : (i : ℕ) + 1 < D.R.m)
    (Y : Cov p i) (hY : GoodCov p i Y) (u1 : AllWt.Weight (dat p i)) (hu : Quo p i PP u1) : GeomAt p i Y u1 := by
  obtain ⟨hsig1, hsig2, -⟩ := hw.sig
  have hk := D.R.m_add_three_le_k
  have hp1 : 1 ≤ (dat p i).p := by rw [hsig1]; simp only [Ranks.sigW]; omega
  have hq1 : 1 ≤ (dat p i).q := by rw [hsig2]; simp only [Ranks.sigW]; omega
  have hf : 2 < Module.finrank ℚ D.host.E / 2 := by rw [hN.deg]; have := hN.f8; omega
  have hj : InR D ((i : ℕ) + 1) := ⟨by omega, hi.le⟩
  have hL : LawsJ p.T := p.fw.laws
  have hYg := hY.1
  obtain ⟨-, -, -, -, -, -, hq⟩ := hsz
  obtain ⟨-, hq⟩ := hq hi
  obtain ⟨-, -, hρ1, -⟩ := hq u1 hu
  have hgap := quo_gaps p i hN hw hi u1 hu
  have hsa : ∀ τ, StrictAnti (u1 τ) := fun τ => strictAnti_of_step fun a b hb => by
    have := hgap τ a b hb
    have : (0 : ℤ) ≤ (((dimFlag (dat p i) + 3) ^ 2 + 2 * ((dat p i).p + (dat p i).q) : ℕ) : ℤ) := by positivity
    omega
  have hg1 : ∀ τ, 1 ≤ GlobalTheory.CompHS.gap (u1 τ) ((dat p i).p - 1) := fun τ => by
    have e := GlobalTheory.CompHS.gap_eq (u1 τ) (i := ⟨(dat p i).p - 1, by omega⟩) (j := ⟨(dat p i).p, by omega⟩)
      (by simp only; omega)
    simp only at e
    rw [e]
    have := hgap τ ⟨(dat p i).p - 1, by omega⟩ ⟨(dat p i).p, by omega⟩ (by simp only; omega)
    have : (0 : ℤ) ≤ ((dimFlag (dat p i) + 3) ^ 2 + 2 * ((dat p i).p + (dat p i).q) : ℕ) := by positivity
    push_cast at *
    nlinarith
  have hgood := _root_.GlobalTheory.T.covering_domain_lattice_regularity hP _ p.T hL _ hp1 hq1 hf hj Y _ _ hYg u1 (fun τ => (hsa τ).antitone) hg1
  have hbir := _root_.GlobalTheory.T.birOn_wtOf_of_consecutive_gap_bound hX hG hQ hS1 (_root_.GlobalTheory.T.covering_topology_refinement hP) hP.q15 hP.q16 _ p.T hL _ hp1 hq1 Y _ _ hYg u1 hgap
  have hprop := (_root_.GlobalTheory.T.proportionality_principle_compactification hP hS1 hS2 hS3 _ p.T hL _ hp1 hq1 hf hj Y _ _ hYg).1
  intro Z
  refine ⟨hgood.2 Z, hbir Z, ?_⟩
  have hv : vdm u1 ≠ 0 := (GlobalTheory.CompHt.vdm_pos hsa).ne'
  rw [delPrime_eq Y.U Z hv]
  exact mul_le_mul_of_nonneg_left (GlobalTheory.DegTop.compDeg_le hprop Z hsa) (by linarith)
end Point
theorem geom_of_deepGood_size : GlobalTheory.CovTop.HypothesesX → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems →
    GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS →
    GlobalTheory.Published.SemiAbelianLieSeminegative → DeepGood → Size → Geom := by
  intro hX hG hQ hP h1 h2 h3 _ hS
  have hH := Sizes.hostN 0
  have hW := WtShape.wtN
  unfold Geom Covers Lifts
  unfold Size Lifts at hS
  unfold HostN Lifts at hH
  unfold WtN Lifts at hW
  refine ((hS.and hH).and hW).imp fun Fm CH _ h => ?_
  obtain ⟨⟨⟨C1, -, e1⟩, ⟨C2, -, e2⟩⟩, ⟨C3, -, e3⟩⟩ := h
  obtain ⟨x0, hx0⟩ := (e1.and e2).and e3
  refine ⟨0, le_rfl, x0, fun x hx hle ι p hp i hi Y hY u1 hu => ?_⟩
  obtain ⟨⟨b1, b2⟩, b3⟩ := hx0 x hx hle ι p hp
  exact _root_.GlobalTheory.CovHt.GeomBound.geometric_height_bound_at_place p i hX hG hQ hP h1 h2 h3 (b1 i) (b2 i) (b3 i) hi Y hY u1 hu
end GlobalTheory.CovHt.GeomBound
end
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geom_of_published_inputs : GlobalTheory.CovTop.HypothesesX → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → DeepGood → Size → Geom := by
  first | exact @_root_.GlobalTheory.CovHt.GeomBound.geom_of_deepGood_size | exact _root_.GlobalTheory.CovHt.GeomBound.geom_of_deepGood_size | (intros; apply _root_.GlobalTheory.CovHt.GeomBound.geom_of_deepGood_size <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.JetRankComplexLe
section
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic
open GlobalTheory.ThickeningDetermines (secIdeal)
open scoped TensorProduct
open Limits
namespace GlobalTheory.JetRank
section Nef
variable {k : Type} [Field k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)]
end Nef
section
open NumberField Formalism.L2.Pj Formalism.BasicNotions GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.HSApp
open GlobalTheory.AllWt (wtOf cuspOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
section Moving
open GlobalTheory.Vanishing.H0 GlobalTheory.LB GlobalTheory.TangentOrigin
open GlobalTheory.AllWt (secZ exOf)
open GlobalTheory.CompHt (genVal)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : FlagCover Y} {Z : Comp Xo c} {r : ℕ}
  {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r}
end Moving
section Comp
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : FlagCover Y} {Z : Comp Xo c} {r : ℕ}
  {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r}
end Comp
end
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
theorem jet_bundle_rank_le : GlobalTheory.CovTop.HypothesesX → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SemiAbelianLieSeminegative → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (u la : AllWt.Weight (T.Q.Dw j)) (n a : ℕ), GapGe (((CompHt.dimFlag (T.Q.Dw j) + 3) * ((CompHt.dimFlag (T.Q.Dw j) + 1).choose 2 + 4 * ((T.Q.Dw j).p + (T.Q.Dw j).q) + CompHt.dimFlag (T.Q.Dw j) + 3) : ℕ) : ℤ) u → (∀ τ, Antitone (la τ)) → (∀ τ, Antitone ((n : ℤ) • u τ - la τ)) → (n : ℝ) * CompHt.topDeg Y.U Z u < (a + 1) * Y.dg u Z → Y.rkC la Z ≤ ((a + CompHt.dimFlag (T.Q.Dw j)).choose (CompHt.dimFlag (T.Q.Dw j)) : ℕ) * Y.dg u Z := by
  intro hX hP2 hSi hTo hGD hQ hSe D T hT j hp hq hf hj Y e o hY Z u la n a hu hla hnu hlt
  have hP := _root_.GlobalTheory.T.covering_topology_refinement hP2
  have hDe := dimFlag_eq (T.Q.Dw j)
  have hD : 1 ≤ FlagTan.dimFlag (T.Q.Dw j) :=
    Nat.mul_pos (by omega) (Nat.choose_pos (by omega))
  obtain ⟨TF⟩ := _root_.GlobalTheory.T.torFlag_nonempty_of_one_le_dimFlag hP _ _ _ _ Y.d.Xo₂ Y.d.c₂ hD
  have hV := GlobalTheory.VarFlag.isVariety₀_flag _ _ _ _ _ _ TF Z hY.geo
  have hC : ∀ la, CuspIso TF.X Z Y.U la := fun la =>
    ⟨GlobalTheory.T.cuspForms_extend_vanish_compactifiedFlagSpace D T.toCore j Y e o hY hf Z TF la, GlobalTheory.HSApp.vanBd_le_space D T.toCore j Y e o hY hf Z TF la⟩
  have hC0 : (0 : ℤ) ≤ (((CompHt.dimFlag (T.Q.Dw j) + 1).choose 2 : ℕ) : ℤ) := Int.natCast_nonneg _
  have hD0 : (0 : ℤ) ≤ (CompHt.dimFlag (T.Q.Dw j) : ℤ) := Int.natCast_nonneg _
  have hp0 : (0 : ℤ) ≤ ((T.Q.Dw j).p : ℤ) := Int.natCast_nonneg _
  have hq0 : (0 : ℤ) ≤ ((T.Q.Dw j).q : ℤ) := Int.natCast_nonneg _
  have hF : FreeOnOpen TF.X Z Y.U u := by
    refine _root_.GlobalTheory.T.hodge_bundle_base_point_free_on_open hP hGD hQ hP2.q15 hP2.q16 hSi hTo.toroidalChartsForFan hSe _ _ _ _ _ _ TF Z _ Y.U hY.geo hD _ (fun τ k hk => ?_) (hC _)
    have h₁ := hu τ k hk
    have h₂ := gap_kap_le (Dw := T.Q.Dw j) τ hk
    rw [Pi.sub_apply, gap_sub, ← hDe]
    push_cast at h₁ h₂ ⊢
    nlinarith
  have hB : BirOn Y.U Z (wtOf (T.Q.Dw j) u 0) := by
    refine _root_.GlobalTheory.T.birOn_wtOf_of_consecutive_gap_bound hX hGD hQ hSi hP hP2.q15 hP2.q16 D T hT j hp hq Y e o hY u (fun τ a b hab => ?_) Z
    have h₁ := hu τ a (hab ▸ b.2)
    rw [gap_eq _ hab] at h₁
    push_cast at h₁ ⊢
    nlinarith
  have hu1 : GapGe 1 u := hu.mono (by push_cast; nlinarith)
  have hsa : ∀ τ, StrictAnti (u τ) := fun τ => by
    have key : ∀ (m : ℕ) (w : Fin m → ℤ), (∀ k, k + 1 < m → 1 ≤ gap w k) → StrictAnti w := fun m w hw => by
      cases m with
      | zero => exact fun a => a.elim0
      | succ m =>
        refine Fin.strictAnti_iff_succ_lt.2 fun i => ?_
        have := hw i (by omega)
        rw [show (i : ℕ) = (i.castSucc : ℕ) from rfl, gap_eq w (j := i.succ) rfl] at this
        omega
    exact key _ _ (hu1 τ)
  obtain ⟨hPr, hv⟩ := _root_.GlobalTheory.T.proportionality_principle_compactification hP2 hSi hTo hSe D T hT j hp hq hf hj Y e o hY
  have hnef := _root_.GlobalTheory.T.base_weight_line_bundle_is_nef hP hQ.nef hSe _ _ _ _ _ _ TF Z hY.geo
  have key := finrank_cusp_le (n := n) (a := a) (la := la) hQ hP2.q16 hV hD hC hF hB
    (mul_nonneg (hv Z).le (Int.cast_pos.2 (CompHt.vdm_pos hsa)).le) (hPr Z u hsa)
    ⟨hnef _ (hu1.mono zero_le_one), hnef _ (gapGe_zero_of_antitone hla), hnef _ (gapGe_zero_of_antitone fun τ => by
      simpa using hnu τ)⟩ hlt
  rw [← hDe] at key
  have := Vanishing.finite_top hV.2.1 (isLB_L₀ TF.X Z la)
  have : Module.Finite Y.d.c₂.F (Cusp Z Y.U la) := .equiv (hC la).1.equiv.symm
  exact_mod_cast (Submodule.finrank_le _).trans key
end
end GlobalTheory.JetRank
end
end

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
theorem _root_.GlobalTheory.T.jet_rank_complex_le : GlobalTheory.CovTop.HypothesesX → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SemiAbelianLieSeminegative → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (u la : AllWt.Weight (T.Q.Dw j)) (n a : ℕ), GapGe (((CompHt.dimFlag (T.Q.Dw j) + 3) * ((CompHt.dimFlag (T.Q.Dw j) + 1).choose 2 + 4 * ((T.Q.Dw j).p + (T.Q.Dw j).q) + CompHt.dimFlag (T.Q.Dw j) + 3) : ℕ) : ℤ) u → (∀ τ, Antitone (la τ)) → (∀ τ, Antitone ((n : ℤ) • u τ - la τ)) → (n : ℝ) * CompHt.topDeg Y.U Z u < (a + 1) * Y.dg u Z → Y.rkC la Z ≤ ((a + CompHt.dimFlag (T.Q.Dw j)).choose (CompHt.dimFlag (T.Q.Dw j)) : ℕ) * Y.dg u Z := by
  first | exact @_root_.GlobalTheory.JetRank.jet_bundle_rank_le | exact _root_.GlobalTheory.JetRank.jet_bundle_rank_le | (intros; apply _root_.GlobalTheory.JetRank.jet_bundle_rank_le <;> assumption)
end
end

