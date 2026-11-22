import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3421
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0025
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0003
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3440
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3415
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0027
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3433
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3414
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Hypotheses2
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3432

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CoveringDomainLatticeRegularity
section
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
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.GeometryOfNumbersTheory TopologicalSpace Limits
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LamT (CMPt)
noncomputable section
namespace GlobalTheory.CovTop.GoodDom
set_option maxHeartbeats 1000000 in
theorem weight_lattice_fg_on_domain : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o →
    2 < Module.finrank ℚ D.host.E / 2 → 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → ∀ la : GlobalTheory.AllWt.Weight (T.Q.Dw j), (∀ τ, Antitone (la τ)) → (∀ τ, 1 ≤ gap (la τ) ((T.Q.Dw j).p - 1)) →
    FiniteDimensional Y.d.c₂.F (Y.V (wtOf _ la 0)) → (GlobalTheory.AllWt.latW Y.U (wtOf _ la 0)).FG := by
  intro hP D T j Y e o hG hE hp hq la hA hb hfd
  letI := T.Q.H.starRing
  refine GlobalTheory.fg_of_integral_functionals Y.d.c₂.F (Y.V (wtOf _ la 0)) _ fun x hx => ?_
  obtain ⟨z, La, y, hz, hyx, hne⟩ := _root_.GlobalTheory.T.cmPoint_detects_dominant_covering hP D T j Y e o hG hE hp hq la hA hb (fun _ => rfl) x.1 x.2
    (fun h => hx (Subtype.ext h))
  obtain ⟨N, hN, hint⟩ := GlobalTheory.T.exists_frame_denominator_dominant_weight_cm _ _ _ _ _ _ z _ La hz y hyx hp hq la hA hb
  refine ⟨z.K, inferInstance, inferInstance, inferInstance,
    { toFun := fun F => N * evR Y.d.Xo₂ Y.d.c₂ F.1 y
      map_add' := fun F G => ?_
      map_smul' := fun s F => ?_ }, mul_ne_zero hN hne, fun F hF => hint F.1 (GlobalTheory.AllWt.cuspW_le_secZ _ F.2) hF⟩
  · rw [← mul_add]
    exact congrArg _ (evalAt_add _ _ F.1 G.1 y)
  · have e1 : evR Y.d.Xo₂ Y.d.c₂ (s • F).1 y = algebraMap Y.d.c₂.F z.K s * evR Y.d.Xo₂ Y.d.c₂ F.1 y :=
      evalAt_smul _ _ s F.1 y
    rw [e1, RingHom.id_apply, Algebra.smul_def, mul_left_comm]
set_option maxHeartbeats 800000 in
theorem weight_lattice_span_on_domain : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ),
    Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → ∀ la : GlobalTheory.AllWt.Weight (T.Q.Dw j), (∀ τ, Antitone (la τ)) → (∀ τ, 1 ≤ gap (la τ) ((T.Q.Dw j).p - 1)) →
    Submodule.span Y.d.c₂.F (GlobalTheory.AllWt.latW Y.U (wtOf _ la 0) : Set (Y.V (wtOf _ la 0))) = ⊤ := by
  intro hP D T j Y e o hY hE hp hq la hA hb
  refine eq_top_iff.2 fun f _ => ?_
  obtain ⟨k, a, n, g, h, t, hdom, hn, hmem, ht, hgh, hh⟩ := _root_.GlobalTheory.T.weight_match_pow_mul_cuspidal hP D T j Y e o hY hE hp hq la hA hb f.1 f.2
  obtain ⟨s, hs, hsv⟩ := _root_.GlobalTheory.T.divisor_multiple_nonneg_eventually hP D T j Y e o hY hE a n hdom hn _ hmem
  have key : ∀ la', ∀ v ∈ valSet Y.d.Xo₂ Y.d.c₂ (algCls Y.d.Xo₂ Y.d.c₂) la',
      0 ≤ v ((s * t) • ((f : Rul Y.d.Xo₂ Y.d.c₂) ^ (k + 1))) := by
    intro la' v hv
    have hV := isVal_valSet la' v hv
    have e1 : (s • ((f : Rul Y.d.Xo₂ Y.d.c₂) ^ (k + 1) * g)) * h = (s * t) • ((f : Rul Y.d.Xo₂ Y.d.c₂) ^ (k + 1)) := by
      rw [smul_mul_assoc, mul_assoc, hgh, mul_smul_comm, mul_one, smul_smul]
    rw [← e1, hV.mul]
    exact add_nonneg (hsv la' v hv) (hh la' v hv)
  obtain ⟨s', hs', h'⟩ := GlobalTheory.SupFull.exists_smul_nonneg_of_pow (valSet Y.d.Xo₂ Y.d.c₂ (algCls Y.d.Xo₂ Y.d.c₂))
    (fun la => isVal_valSet la) {(f : Rul Y.d.Xo₂ Y.d.c₂) ^ (k + 1)}
    (by rintro g' rfl; exact ⟨s * t, mul_ne_zero hs ht, key⟩) (f : Rul Y.d.Xo₂ Y.d.c₂) k
    (Submodule.subset_span rfl)
  have hmem' : s' • f ∈ GlobalTheory.AllWt.latW Y.U (wtOf _ la 0) :=
    GlobalTheory.AllWt.mem_supLat.2 fun la v hv => h' la v hv
  rw [← inv_smul_smul₀ hs' f]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hmem')
set_option maxHeartbeats 1000000 in
theorem covering_regular_at_domain : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ la : AllWt.Weight (T.Q.Dw j), (∀ τ, Antitone (la τ)) → (∀ τ, 1 ≤ gap (la τ) ((T.Q.Dw j).p - 1)) → Y.GoodAt (wtOf _ la 0) ∧ ∀ Z, GoodOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf _ la 0) := by
  intro hP D T hL j hp hq hE _ Y e o hY la hA hb
  have hfd := GlobalTheory.Deep.finiteDimensional_V_of_good D T.toCore j Y e o hY (wtOf _ la 0)
  have hG : Y.GoodAt (wtOf _ la 0) :=
    ⟨hasGram_nrm_of_good D T.toCore j Y e o hY _, _root_.GlobalTheory.CovTop.GoodDom.weight_lattice_fg_on_domain hP D T.toCore j Y e o hY hE hp hq la hA hb hfd,
      _root_.GlobalTheory.CovTop.GoodDom.weight_lattice_span_on_domain hP D T.toCore j Y e o hY hE hp hq la hA hb⟩
  exact ⟨hG, fun Z => goodOn_of_goodAt D T.toCore j Y e o hY hE Z _ hG⟩
end GlobalTheory.CovTop.GoodDom
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
theorem _root_.GlobalTheory.T.covering_domain_lattice_regularity : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ la : AllWt.Weight (T.Q.Dw j), (∀ τ, Antitone (la τ)) → (∀ τ, 1 ≤ gap (la τ) ((T.Q.Dw j).p - 1)) → Y.GoodAt (wtOf _ la 0) ∧ ∀ Z, GoodOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf _ la 0) := by
  first | exact @_root_.GlobalTheory.CovTop.GoodDom.covering_regular_at_domain | exact _root_.GlobalTheory.CovTop.GoodDom.covering_regular_at_domain | (intros; apply _root_.GlobalTheory.CovTop.GoodDom.covering_regular_at_domain <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsCuspValueLePhiOfHilbertSamuel
section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HSApp
set_option maxHeartbeats 2000000 in
theorem exists_cusp_value_le_phi_of_hilbertSamuel : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → DeepGood → Size → FlatDeg → Covers fun Fm x _ ι p i Y PP _ => ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂), ∀ la ∈ ({(⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁, (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).ub} : Set (AllWt.Weight (dat p i))), ∀ y ∈ (U₀ TF.X Z : Set (Y₀ TF.X Z))ᶜ, ∀ (T : CDVR) (io : Y.d.c₂.F →+* T.Fr) (y' : IntFr Y.d.Xo₂ Y.d.c₂ T io) (g : (Y₀ TF.X Z).presheaf.stalk y →+* T.V) (φT : ℝ), IsLocalHom g → GlobalTheory.SlopeRec.HasPhi y' φT → (letI := io.toAlgebra; TF.X.ptY y'.1 = Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫ (Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z) → ∃ w : space TF.X Z Y.U la, evI y' ((ofSpace TF.X Z Y.U la w : Cusp Z Y.U la) : Rul Y.d.Xo₂ Y.d.c₂) ≠ 0 ∧ (vV T.V (evI y' ((ofSpace TF.X Z Y.U la w : Cusp Z Y.U la) : Rul Y.d.Xo₂ Y.d.c₂)) : ℝ) ≤ φT / 2500 := by
  intro h1 h2 h3 h4
  refine ((((_root_.GlobalTheory.T.jets_constant_section_eq h1 h2 h3 h4).and (GlobalTheory.T.jet_number_upper_weight h3)).and (GlobalTheory.T.weight_parameter_strict_antitone h3)).and ((GlobalTheory.T.jet_number_quotient_bounds h3).and h3)).imp fun Fm CH _ h => ?_
  obtain ⟨⟨⟨⟨C, hC, x0, hJ⟩, ⟨C1, hC1, x1, hN⟩⟩, ⟨C2, hC2, x2, hA⟩⟩, ⟨⟨C3, hC3, x3, hB⟩, ⟨C4, hC4, x4, hS⟩⟩⟩ := h
  refine ⟨C, hC, max (max x0 x1) (max x2 (max x3 x4)), fun x hx' hle ι p hp i hi Y hY Z TF la hla y hy T io y' g φT hg hφT hpt => ?_⟩
  have l0 : x0 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hle
  have l1 : x1 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hle
  have l2 : x2 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hle
  have l3 : x3 ≤ x := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hle
  have l4 : x4 ≤ x := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hle
  obtain ⟨-, -, hfin, hquo, -⟩ := hA x hx' l2 ι p hp i hi
  obtain ⟨⟨u1, hu1⟩, -⟩ := (hS x hx' l4 ι p hp i).2.2.2.2.2.2 hi
  have hnum : GlobalTheory.RefSum.JetNum (Fm.D x ι) (DF (dat p i) (GlobalTheory.RefSum.thA (dat p i) la (GlobalTheory.RefSum.nCol (dat p i)))) (1 / 2500) := by
    rcases hla with rfl | hla
    · have := (hB x hx' l3 ι p hp i hi u1 hu1).1
      rwa [hquo u1 hu1] at this
    · rw [Set.mem_singleton_iff] at hla
      subst hla
      exact hN x hx' l1 ι p hp i hi
  obtain ⟨f, hf0, hfb⟩ := hJ x hx' l0 ι p hp i hi Y hY Z TF la hla (1 / 2500) hnum y hy T io y' g φT hg hφT hpt
  have hE : Extends TF.X Z Y.U la := GlobalTheory.T.cuspForms_extend_vanish_compactifiedFlagSpace (Fm.D x ι) p.T.toCore ((i : ℕ) + 1) Y _ _ hY.1 hfin Z TF la
  refine ⟨hE.equiv f, ?_⟩
  have e : ofSpace TF.X Z Y.U la (hE.equiv f) = f := hE.equiv.symm_apply_apply f
  rw [e]
  refine ⟨hf0, ?_⟩
  rw [div_eq_mul_one_div, mul_comm]
  exact hfb
end GlobalTheory.HSApp
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_form_cusp_value_bound : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → DeepGood → Size → FlatDeg → Covers fun Fm x _ ι p i Y PP _ => ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂), ∀ la ∈ ({(⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁, (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).ub} : Set (AllWt.Weight (dat p i))), ∀ y ∈ (U₀ TF.X Z : Set (Y₀ TF.X Z))ᶜ, ∀ (T : CDVR) (io : Y.d.c₂.F →+* T.Fr) (y' : IntFr Y.d.Xo₂ Y.d.c₂ T io) (g : (Y₀ TF.X Z).presheaf.stalk y →+* T.V) (φT : ℝ), IsLocalHom g → GlobalTheory.SlopeRec.HasPhi y' φT → (letI := io.toAlgebra; TF.X.ptY y'.1 = Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫ (Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z) → ∃ w : space TF.X Z Y.U la, evI y' ((ofSpace TF.X Z Y.U la w : Cusp Z Y.U la) : Rul Y.d.Xo₂ Y.d.c₂) ≠ 0 ∧ (vV T.V (evI y' ((ofSpace TF.X Z Y.U la w : Cusp Z Y.U la) : Rul Y.d.Xo₂ Y.d.c₂)) : ℝ) ≤ φT / 2500 := by
  first | exact @_root_.GlobalTheory.HSApp.exists_cusp_value_le_phi_of_hilbertSamuel | exact _root_.GlobalTheory.HSApp.exists_cusp_value_le_phi_of_hilbertSamuel | (intros; apply _root_.GlobalTheory.HSApp.exists_cusp_value_le_phi_of_hilbertSamuel <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.HodgeBundleIsNefIsBigOfWeight
section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
namespace GlobalTheory.HSApp
theorem hodge_bundle_nef_and_big : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.NefNumerics → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalChartsForFan → GlobalTheory.Published.SemiAbelianLieSeminegative → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (P : WtPar Dw) (R : Choice TF.X Z U P) (ω : CanId R.toModif) (x : ℝ) (D : D7) (V : (c.F →+* ℂ) → TH.HSp D) (dict : ∀ σ, Formalism.L2.Theta.GA D (V σ) → Σ k, FD.Frame ((U σ).X k).Ψ r) (h : Ready R ω x V dict) (f₁ : CuspFrame Z U x V dict P.u₁) (f₂ : CuspFrame Z U x V dict P.u₂) (th : R.L.Sec) (k : Consts), FnAlgClosed Xo c → WtBig P → IsNef c.F (h.geo f₁ f₂ th k).LA ∧ IsBig c.F (h.geo f₁ f₂ th k).LA := by
  intro hP hN hS hC hL E _ _ _ H Dw l Xo c TF Z r U P R ω x D V dict h f₁ f₂ th k hF hW
  obtain ⟨hsm, hpr, hgc⟩ := GlobalTheory.VarFlag.isVariety₀_flag E H Dw l Xo c TF Z hF
  have hsm' : Smooth (str₀ TF.X Z) := SmoothOfRelativeDimension.smooth (dimFlag Dw) (str₀ TF.X Z)
  haveI : IsIntegral (Y₀ TF.X Z) := isIntegral_of_smooth_of_geometricallyConnected (str₀ TF.X Z)
  set la : AllWt.Weight Dw := P.u₂ + dimFlag Dw • P.u₁ with hla
  have hg₁ := (GlobalTheory.HSApp.gaps_of_wtBig E H Dw P hW P.u₁ (by simp)).1
  have hg₂ := (GlobalTheory.HSApp.gaps_of_wtBig E H Dw P hW P.u₂ (by simp)).1
  have hgla : GapGe 1 la := by
    intro τ k hk
    have a₁ := hg₁ τ k hk
    have a₂ := hg₂ τ k hk
    simp only [hla, Pi.add_apply, Pi.smul_apply, gap_add, gap_nsmul]
    nlinarith
  letI := algebraΓOfHom (str₀ TF.X Z)
  have hf₀ : ∀ r : c.F, algebraMap c.F Γ(Y₀ TF.X Z, ⊤) r =
      (str₀ TF.X Z).appTop ((Scheme.ΓSpecIso (.of c.F)).inv r) := fun _ => rfl
  have hs₀ : strHom c.F (Y₀ TF.X Z) = str₀ TF.X Z := strHom_eq hf₀
  have hp₀ : IsProjOver (strHom c.F (Y₀ TF.X Z)) := hs₀ ▸ hpr
  obtain ⟨hprop₀, H₀, hH₀⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hpr
  have nef : ∀ w : AllWt.Weight Dw, GapGe 0 w → IsNef c.F (L₀ TF.X Z w) :=
    fun w hw => _root_.GlobalTheory.T.base_weight_line_bundle_is_nef hP hN hL E H Dw l Xo c TF Z hF w hw
  have nef₀ : IsNef c.F (L₀ TF.X Z la) := nef la (hgla.mono (by norm_num))
  have big₀ : IsBig c.F (L₀ TF.X Z la) := by
    obtain ⟨y₀⟩ : Nonempty (Y₀ TF.X Z) := by
      obtain ⟨z⟩ : Nonempty (Sp c.F) := inferInstance
      obtain ⟨y, -⟩ := (str₀ TF.X Z).surjective z
      exact ⟨y⟩
    have hne : (U₀ TF.X Z : Set (Y₀ TF.X Z)).Nonempty := (dense_U₀ TF.X Z).nonempty
    obtain ⟨y, hy⟩ := hne
    obtain ⟨mu, hmu0, m, hm, hA⟩ := _root_.GlobalTheory.T.hodge_bundle_ample_on_regular_locus hP hN hS hC E H Dw l Xo c TF Z hF la hgla y hy
    obtain ⟨m', Aa, s, hm', hAa, hAamp, hys⟩ := hA
    have hNn := isLB_L₀ TF.X Z (m • la - mu)
    have hdiv : (LB.div (lbPow (L₀ TF.X Z (m • la - mu)) m') Aa).IsLB := Semi.LB.isLB_div (isLB_lbPow hNn m') hAa
    have nefmu := nef mu hmu0
    have hB := (nefmu.pow hAamp m').isBig_tens_ample hN hp₀ hAamp
    have hcls0 : cls (L₀ TF.X Z 0) (isLB_L₀ TF.X Z 0) = 0 := by
      have h := cls_common_add (common₀ TF.X Z) 0 0
      simp only [add_zero] at h
      exact left_eq_add.1 h
    have hnsmul : ∀ n : ℕ, cls (L₀ TF.X Z (n • la)) (isLB_L₀ TF.X Z _) = n • cls (L₀ TF.X Z la) (isLB_L₀ TF.X Z la) := by
      intro n
      induction n with
      | zero => simpa only [zero_nsmul] using hcls0
      | succ n ih => rw [succ_nsmul, cls_common_add (common₀ TF.X Z), ih, succ_nsmul]
    have h1 := cls_common_add (common₀ TF.X Z) (m • la - mu) mu
    rw [sub_add_cancel] at h1
    have hP' := isLB_lbPow (isLB_L₀ TF.X Z la) (m * m')
    have e : cls (lbPow (L₀ TF.X Z la) (m * m')) hP' = cls _ hB.isLB + cls _ hdiv := by
      rw [cls_lbPow (isLB_L₀ TF.X Z la), cls_tens (isLB_lbPow nefmu.isLB m') hAa, cls_div (isLB_lbPow hNn m') hAa,
        cls_lbPow nefmu.isLB, cls_lbPow hNn, mul_nsmul, ← hnsmul m, h1, smul_add]
      abel
    have hbigP : IsBig c.F (lbPow (L₀ TF.X Z la) (m * m')) :=
      hB.of_cls_eq_add hf₀ hpr hdiv ⟨s, sec_ne_zero_of_mem hys⟩ hP' e
    exact hbigP.of_pow (isLB_L₀ TF.X Z la) (Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hm.ne' hm'.ne'))
      (fun j => finite_coh_zero_twist_of_isProjOver hf₀ hpr (isLB_lbPow (isLB_L₀ TF.X Z la) j))
  have bigpull : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (g : Y ⟶ X), IsProjOver (g ≫ p) → topologicalKrullDim Y = topologicalKrullDim X → Dense (Set.range g) → ∀ N : LB X, (letI := algebraΓOfHom p; IsBig k N) → (letI := algebraΓOfHom (g ≫ p); IsBig k (N.pull g)) := fun k _ X Y _ p g hp hd hg N hN => GlobalTheory.BigPull.isBig_pull k X Y p g hp hd hg N hN
  obtain ⟨hprop₁, H₁, hH₁⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB _).1 R.proj
  haveI : IsProper (strHom c.F (Y₀ TF.X Z)) := hs₀ ▸ hprop₀
  haveI : IsProper (R.σ ≫ str₀ TF.X Z) := hprop₁
  haveI : IsProper R.σ := IsProper.of_comp R.σ (str₀ TF.X Z)
  have hcl : IsClosedMap R.σ := Scheme.Hom.isClosedMap R.σ
  haveI : Nonempty R.X := by
    obtain ⟨z⟩ : Nonempty (Sp c.F) := inferInstance
    haveI : GeometricallyConnected R.str := h.conn
    obtain ⟨y, -⟩ := R.str.surjective z
    exact ⟨y⟩
  haveI : Nonempty (Y₀ TF.X Z) := ⟨R.σ (Classical.arbitrary R.X)⟩
  have hdim : topologicalKrullDim R.X = topologicalKrullDim (Y₀ TF.X Z) := by
    rw [GlobalTheory.HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth R.str (dimFlag Dw) R.smooth,
      GlobalTheory.HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth (str₀ TF.X Z) (dimFlag Dw) hsm]
  have hdense : Dense (Set.range R.σ) := by
    refine (dense_U₀ TF.X Z).mono fun y hy => ?_
    have := R.iso
    obtain ⟨x, hx⟩ := (R.σ ∣_ U₀ TF.X Z).surjective ⟨y, hy⟩
    refine ⟨(R.σ ⁻¹ᵁ U₀ TF.X Z).ι x, ?_⟩
    have e := congrArg (fun q => q x) (morphismRestrict_ι R.σ (U₀ TF.X Z))
    simp only [Scheme.Hom.comp_apply] at e
    rw [← e, hx]
    rfl
  letI := algebraΓOfHom R.str
  change IsNef c.F ((L₀ TF.X Z la).pull R.σ) ∧ IsBig c.F ((L₀ TF.X Z la).pull R.σ)
  exact ⟨GlobalTheory.PosBaseChange.isNef_pull nef₀ hH₀ hH₁ R.σ hcl,
    bigpull c.F (Y₀ TF.X Z) R.X (str₀ TF.X Z) R.σ R.proj hdim hdense _ big₀⟩
end GlobalTheory.HSApp
end

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
theorem _root_.GlobalTheory.T.hodge_bundle_isNef_isBig_of_weight : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.NefNumerics → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalChartsForFan → GlobalTheory.Published.SemiAbelianLieSeminegative → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (P : WtPar Dw) (R : Choice TF.X Z U P) (ω : CanId R.toModif) (x : ℝ) (D : D7) (V : (c.F →+* ℂ) → TH.HSp D) (dict : ∀ σ, Formalism.L2.Theta.GA D (V σ) → Σ k, FD.Frame ((U σ).X k).Ψ r) (h : Ready R ω x V dict) (f₁ : CuspFrame Z U x V dict P.u₁) (f₂ : CuspFrame Z U x V dict P.u₂) (th : R.L.Sec) (k : Consts), FnAlgClosed Xo c → WtBig P → IsNef c.F (h.geo f₁ f₂ th k).LA ∧ IsBig c.F (h.geo f₁ f₂ th k).LA := by
  first | exact @_root_.GlobalTheory.HSApp.hodge_bundle_nef_and_big | exact _root_.GlobalTheory.HSApp.hodge_bundle_nef_and_big | (intros; apply _root_.GlobalTheory.HSApp.hodge_bundle_nef_and_big <;> assumption)
end
end

