import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0033
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0062
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0161
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0140
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0115
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0124
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0094
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle1008
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0200
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0138
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0211
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0208
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle1009
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0141
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0212
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0197
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0043
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0009
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0024
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0018
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0209
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.AbsCentralAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2304
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0084
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0057
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0813
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0133
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0027
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0035
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0134
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0017
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0202
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0203
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0142
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0845
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0012
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0213
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.UnitaryReadS

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ShortVectorsSpanCuspLattice
section
set_option synthInstance.maxHeartbeats 200000

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
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.CovTop.ShortSpanUnitCover
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
end GlobalTheory.CovTop.ShortSpanUnitCover
namespace GlobalTheory.CovTop.ShortSpanUnitCover
end GlobalTheory.CovTop.ShortSpanUnitCover
namespace GlobalTheory.CovTop.ShortSpanUnitCover
set_option maxHeartbeats 1000000 in
theorem short_vectors_span_uc_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ Z, ∃ (m : ℕ) (v : Fin m → Cusp Z Y.U ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt 0)), (∀ q, v q ∈ latOn Y.U Z _) ∧ Submodule.span Y.d.c₂.F (Set.range v) = ⊤ ∧ ∀ q σ, petOn Y.U (xiR (Fm.D x ι)) (fun _ => (Fm.D x ι).sp.W ((i : ℕ) + 1)) Y.dict Z (wtOf (dat p i) ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt 0) 0) σ (v q).1 ≤ Real.exp (CompHt.dimFlag (dat p i) * PP * (kap p i / lenT p i PP + 1)) := by
  intro hP2 _hDG hSz hFD
  obtain ⟨C, hC0, hH3⟩ := _root_.GlobalTheory.T.short_generator_norm_comparison hP2
  have hGd := _root_.GlobalTheory.T.covering_domain_lattice_regularity hP2
  refine ((((((_root_.GlobalTheory.T.size_bounds_for_family_alt hSz).and (_root_.GlobalTheory.T.weight_parameter_strict_antitone_alt hSz)).and (_root_.GlobalTheory.CovTop.Sizes.hostN_alt (4 * C + 1))).and _root_.GlobalTheory.CovTop.WtShape.wtN_z).and
    _root_.GlobalTheory.HSApp.wtBig_run_alt).and hFD).imp fun Fm CH _ hh => ?_
  obtain ⟨⟨⟨⟨⟨⟨C1, -, a1, h1⟩, ⟨C2, -, a2, h2⟩⟩, ⟨C3, -, a3, h3⟩⟩, ⟨C4, -, a4, h4⟩⟩, ⟨C5, -, a5, h5⟩⟩, ⟨C6, -, a6, h6⟩⟩ := hh
  refine ⟨0, le_rfl, max a1 (max a2 (max a3 (max a4 (max a5 a6)))), fun x hx hle ι p hp i hi Y hY => ?_⟩
  have s1 := h1 x hx (le_trans (by simp) hle) ι p hp i hi Y hY
  have s2 := h2 x hx (le_trans (by simp) hle) ι p hp i hi
  have s3 := h3 x hx (le_trans (by simp) hle) ι p hp i
  have s4 := h4 x hx (le_trans (by simp) hle) ι p hp i
  have s5 := h5 x hx (le_trans (by simp) hle) ι p hp i hi
  have s6 := h6 x hx (le_trans (by simp) hle) ι p hp i hi Y hY
  obtain ⟨hLaws, hInR, hL1, hM, hfs, hfr, -, -, hf8, hr100, hflat, hkap, hPP, -, -, -, hu12, hwt⟩ := s1
  obtain ⟨hp1, hq1, hfin, -, hsa, -⟩ := s2
  intro Z
  set P : WtPar (dat p i) := (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i (Fm.parT x hx ι).PP⟩ :
    WtPar (dat p i)) with hP
  have hpq : (dat p i).p + (dat p i).q = (Fm.D x ι).R.r := s4.sig.2.2
  have hr2 : 0 < (Fm.D x ι).R.r.choose 2 := Nat.choose_pos (by omega)
  have hDf : (Fm.D x ι).R.f ≤ FlagTan.dimFlag (dat p i) := by
    rw [← GlobalTheory.CompHS.dimFlag_eq, s4.dim]; exact Nat.le_mul_of_pos_right _ hr2
  have hD2 : 2 ≤ FlagTan.dimFlag (dat p i) + 0 := by omega
  have hAnt := fun τ => GlobalTheory.CompHS.WtPar.antitone_wt_gap_bar (dat p i) P 0 (fun τ => (hsa τ).1) hD2 hp1 hq1 τ
  have hgap : ∀ τ, ((8 * (Fm.D x ι).R.f * (Fm.D x ι).R.r + 10 : ℕ) : ℤ) ≤ gap (P.wt 0 τ) ((dat p i).p - 1) := by
    intro τ
    have hk : (dat p i).p - 1 + 1 < (dat p i).p + (dat p i).q := by omega
    obtain ⟨G, hG⟩ : ∃ G : ℕ, G = (FlagTan.dimFlag (dat p i) + 3) * ((FlagTan.dimFlag (dat p i) + 1).choose 2 +
        4 * ((dat p i).p + (dat p i).q) + FlagTan.dimFlag (dat p i) + 3) := ⟨_, rfl⟩
    have hg : (G : ℤ) ≤ gap (P.u₁ τ) ((dat p i).p - 1) := hG ▸ s5.gaps τ _ hk
    have h1 := consecutiveGap_weightZero_ge (dat p i) P τ hk _ hg
    have hG12 : 12 * (Fm.D x ι).R.r ≤ G := by
      rw [hG, hpq]
      have := Nat.mul_le_mul (show 3 ≤ FlagTan.dimFlag (dat p i) + 3 by omega)
        (show 4 * (Fm.D x ι).R.r ≤ (FlagTan.dimFlag (dat p i) + 1).choose 2 + 4 * (Fm.D x ι).R.r +
          FlagTan.dimFlag (dat p i) + 3 by omega)
      omega
    have hN : 8 * (Fm.D x ι).R.f * (Fm.D x ι).R.r + 12 ≤ (FlagTan.dimFlag (dat p i) + 1) * G := by
      have := Nat.mul_le_mul (show (Fm.D x ι).R.f + 1 ≤ FlagTan.dimFlag (dat p i) + 1 by omega) hG12
      nlinarith
    have hN' : ((8 * (Fm.D x ι).R.f * (Fm.D x ι).R.r + 12 : ℕ) : ℤ) ≤ (((FlagTan.dimFlag (dat p i) + 1) * G : ℕ) : ℤ) := by
      exact_mod_cast hN
    push_cast at hN' ⊢
    linarith
  have hf1 : (1 : ℝ) ≤ (Fm.D x ι).R.f := by exact_mod_cast (by omega : 1 ≤ (Fm.D x ι).R.f)
  have hr1 : (1 : ℝ) ≤ (Fm.D x ι).R.r := by exact_mod_cast (by omega : 1 ≤ (Fm.D x ι).R.r)
  have hfr1 : (1 : ℝ) ≤ (Fm.D x ι).R.f * (Fm.D x ι).R.r := by nlinarith
  have hS0 : 0 ≤ ∑ τ, ∑ k, |(P.wt 0 τ k : ℝ)| := by positivity
  have hw0 := hwt 0 (Nat.zero_le _)
  have hlog := log_sum_le hS0 hw0 hkap hfr hL1 hfr1
  obtain ⟨n, w, abelian₂, hSG, hLam, -⟩ := hH3 (Fm.D x ι) p.T hLaws ((i : ℕ) + 1) hp1 hq1 hfin hInR Y _ _ hY.1 _ hL1 hM hfs
    hfr le_rfl _ s6 (by rw [abs_neg]; exact hflat) (P.wt 0) (fun τ => (hAnt τ).1) hgap hlog Z
  refine ⟨n, w, fun q => (hSG.gen _).2 (Submodule.subset_span ⟨q, rfl⟩), ?_, fun q σ => ?_⟩
  · have hGO := ((hGd (Fm.D x ι) p.T hLaws _ hp1 hq1 hfin hInR Y _ _ hY.1 (P.wt 0) (fun τ => (hAnt τ).1)
      (fun τ => (hAnt τ).2)).2 Z).2.2
    rw [eq_top_iff, ← hGO]
    exact Submodule.span_le.2 fun y hy => Submodule.span_le_restrictScalars ℤ _ _ ((hSG.gen y).1 hy)
  · refine (hSG.le q σ).trans ?_
    rw [← Real.exp_log (lt_of_lt_of_le one_pos hSG.one_le), GlobalTheory.CompHS.dimFlag_eq]
    refine Real.exp_le_exp.2 ?_
    have hZ : 0 < zBase (Fm.L x ι) := by unfold zBase; positivity
    have hkap0 : 0 ≤ kap p i := by
      have : 0 ≤ zBase (Fm.L x ι) ^ 2 * kap p i := hS0.trans hw0
      exact (mul_nonneg_iff_of_pos_left (by positivity)).1 this
    have hX : 1 ≤ kap p i / lenT p i (Fm.parT x hx ι).PP + 1 := by
      have := div_nonneg hkap0 (Nat.cast_nonneg (lenT p i (Fm.parT x hx ι).PP)); linarith
    have hW : 0 ≤ zBase (Fm.L x ι) ^ 2 * (kap p i / lenT p i (Fm.parT x hx ι).PP + 1) := by positivity
    have hcard : Fintype.card (Psi p.T.Q.H) = (Fm.D x ι).R.f := by rw [← Nat.card_eq_fintype_card]; exact s4.card
    have hK : ∑ τ, ∑ k, |(FlagTan.kap (dat p i) τ k : ℝ)| ≤
        zBase (Fm.L x ι) ^ 2 * (kap p i / lenT p i (Fm.parT x hx ι).PP + 1) := by
      refine (sum_abs_kap_le (dat p i)).trans ?_
      rw [hcard, hpq]
      have a : 1 ≤ ((Fm.D x ι).R.f : ℝ) * (Fm.L x ι).sc.L ^ 2 := by nlinarith
      have b : ((Fm.D x ι).R.f : ℝ) * ((Fm.D x ι).R.r : ℝ) ^ 2 ≤ zBase (Fm.L x ι) ^ 2 := by
        unfold zBase
        calc ((Fm.D x ι).R.f : ℝ) * ((Fm.D x ι).R.r : ℝ) ^ 2 = ((Fm.D x ι).R.f : ℝ) * ((Fm.D x ι).R.r : ℝ) ^ 2 * 1 :=
              (mul_one _).symm
          _ ≤ ((Fm.D x ι).R.f : ℝ) * ((Fm.D x ι).R.r : ℝ) ^ 2 * (((Fm.D x ι).R.f : ℝ) * (Fm.L x ι).sc.L ^ 2) :=
              mul_le_mul_of_nonneg_left a (by positivity)
          _ = _ := by ring
      calc _ ≤ zBase (Fm.L x ι) ^ 2 := by push_cast; exact b
        _ ≤ _ := le_mul_of_one_le_right (by positivity) hX
    have hDc : (1 : ℝ) ≤ (FlagTan.dimFlag (dat p i) : ℝ) := by exact_mod_cast (by omega : 1 ≤ FlagTan.dimFlag (dat p i))
    have hSs := sum_le (sum_abs_weightZero_le_components (dat p i) P) hK (hu12 _ (Set.mem_insert _ _))
      (hu12 _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))) hDc hW
    have hZL : (Fm.L x ι).sc.L ≤ zBase (Fm.L x ι) := le_mul_of_one_le_left (by linarith) hfr1
    exact final_le hC0 s3.big.1 hZL hPP hDc hX (by linarith) hLam
end GlobalTheory.CovTop.ShortSpanUnitCover
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
theorem _root_.GlobalTheory.T.short_vectors_span_cusp_lattice_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ Z, ∃ (m : ℕ) (v : Fin m → Cusp Z Y.U ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt 0)), (∀ q, v q ∈ latOn Y.U Z _) ∧ Submodule.span Y.d.c₂.F (Set.range v) = ⊤ ∧ ∀ q σ, petOn Y.U (xiR (Fm.D x ι)) (fun _ => (Fm.D x ι).sp.W ((i : ℕ) + 1)) Y.dict Z (wtOf (dat p i) ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt 0) 0) σ (v q).1 ≤ Real.exp (CompHt.dimFlag (dat p i) * PP * (kap p i / lenT p i PP + 1)) := by
  first | exact @_root_.GlobalTheory.CovTop.ShortSpanUnitCover.short_vectors_span_uc_alt | exact _root_.GlobalTheory.CovTop.ShortSpanUnitCover.short_vectors_span_uc_alt | (intros; apply _root_.GlobalTheory.CovTop.ShortSpanUnitCover.short_vectors_span_uc_alt <;> assumption)
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SphericalLocalComponentAtSmallPlaces
section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.RowSphSmall
theorem spherical_localComponent_of_small_prime_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, OverRows fun _ _ _ _ w Z _ _ z _ Y =>
    ∀ Rw, _root_.GlobalTheory.HeightCounting.Up.ParityConditions hL (w.st Z).toD7 (TC.cf w.I w.l Z) (repOf Y) Rw → ∀ σ, RowLoc (w.st Z).toD7 Rw σ := by
  intro hP hL
  refine EvG.imp (_root_.GlobalTheory.T.exists_spherical_loc_comp_at_split_place_off_g hP) fun K _ _ _ _ hK => large₂.imp hK fun B f T _ H => ?_
  intro hKP w hpin Z Wt hX z p0 Y hH hEx hGeo hGrp hGA Rw hPar σ w' hsplit hoff
  have H' := H hKP w hpin Z Wt hX z p0 Y hH hEx hGeo hGrp hGA σ
  obtain ⟨s, rfl⟩ := GlobalTheory.OffBad.splitPlace_of_isSplitPl _ w' hsplit
  obtain ⟨τ, hloc, hsph⟩ := H' s hoff
  obtain ⟨Bf, k1, k2, k3, k4⟩ := exists_form_rowRepR hP.hc hP.decay _ _ _ _ _ _ _ z.R z.F z.cG p0 Y z.pins σ
  have hunit := isUnitarisable_of_isLocS (repOf Y σ) Bf k1 k2 k3 k4 s τ hloc
  have he := hPar.row.1 σ s τ hloc
  obtain ⟨hu, hb⟩ := _root_.GlobalTheory.RowSphSmall.reciprocity_unramified_and_norm_frobenius_eigenvalue_le hL ((w.st Z).toD7.nd.plOm.2 s.w) τ hsph hunit
  rw [← he] at hu hb
  have hu' := (hPar.T.unr _ _).2 hu
  refine ⟨hu', fun α hα => ?_⟩
  rw [hPar.T.frobEig _ _ hu'] at hα
  have h1 := hb α hα
  have hq : (1 : ℝ) < ((Formalism.ConjugateSelfDual.normV s.w : ℕ) : ℝ) := by exact_mod_cast GlobalTheory.WeilDeligne.one_lt_normV s.w
  have hrt : (((w.st Z).toD7.R.r : ℝ) - 1) / 2 < (((w.st Z).toD7.R.t : ℝ) - 1) / 2 := by
    have := (w.st Z).toD7.R.rank_add_five_le
    have h2 : (w.st Z).toD7.R.r < (w.st Z).toD7.R.t := by unfold Ranks.r; omega
    have h3 : ((w.st Z).toD7.R.r : ℝ) < ((w.st Z).toD7.R.t : ℝ) := by exact_mod_cast h2
    linarith
  calc ‖α‖ ≤ ((Formalism.ConjugateSelfDual.normV s.w : ℕ) : ℝ) ^ ((((w.st Z).toD7.R.r : ℝ) - 1) / 2) := h1
    _ < ((Formalism.ConjugateSelfDual.normV s.w : ℕ) : ℝ) ^ ((((w.st Z).toD7.R.t : ℝ) - 1) / 2) := Real.rpow_lt_rpow_of_exponent_lt hq hrt
    _ = ((Ideal.absNorm s.w.asIdeal : ℕ) : ℝ) ^ ((((w.st Z).toD7.R.t : ℝ) - 1) / 2) := rfl
end GlobalTheory.RowSphSmall
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_component_of_par_in_third_layer : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, OverRows fun _ _ _ _ w Z _ _ z _ Y => ∀ Rw, _root_.GlobalTheory.HeightCounting.Up.ParityConditions hL (w.st Z).toD7 (TC.cf w.I w.l Z) (repOf Y) Rw → ∀ σ, RowLoc (w.st Z).toD7 Rw σ := by
  first | exact @_root_.GlobalTheory.RowSphSmall.spherical_localComponent_of_small_prime_alt | exact _root_.GlobalTheory.RowSphSmall.spherical_localComponent_of_small_prime_alt | (intros; apply _root_.GlobalTheory.RowSphSmall.spherical_localComponent_of_small_prime_alt <;> assumption)
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SplitReferencePairOfTrivialMu
section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin
noncomputable section
namespace GlobalTheory.RefPair
end GlobalTheory.RefPair
namespace GlobalTheory.RefPair
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin
set_option maxHeartbeats 1000000 in
theorem referencePair_split_of_mu_eq_zero_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.LiftRef.ForallRowSideParameters hL fun D cf rep _ _ M => ∀ (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (σ : D.what₂.FT) (S : Submodule ℂ (Formalism.AUTREP.GAf D.host.E D.R.nV → (M D.what₂.mu0 j h1 h2).wt.W)), NG.IsIrrRep (M D.what₂.mu0 j h1 h2).wt.ρ S → (∃ y ∈ D.what₂.isot j σ, ∃ F ∈ (NG.isoTyp (M D.what₂.mu0 j h1 h2).wt.ρ S).comap (M D.what₂.mu0 j h1 h2).real, inner ℂ F (D.what₂.thetaT D.what₂.mu0 j y) ≠ 0) → ∀ (s : SplitPlace D.host.E) (π : GlobalTheory.SmGL.IrrRep (GL (Fin (D.R.r + D.R.t)) (s.w.adicCompletion D.host.E))) (τ : GlobalTheory.SmGL.IrrRep (GL (Fin D.R.r) (s.w.adicCompletion D.host.E))), IsLocS (n := D.R.nV) S s π → IsLocS (rep σ).S s τ → GlobalTheory.ThetaGL.ThetaPair ((cf.mu0 ⟨j - 1, by omega⟩).loc s.w) τ.ρ (GlobalTheory.SmGL.twist π.ρ (GlobalTheory.SmGL.detChar (Fin (D.R.r + D.R.t)) (cf.eta.loc s.w))) := by
  intro hN hL
  have hA := _root_.GlobalTheory.T.exists_theta_at_of_third_layer hN hL
  unfold _root_.GlobalTheory.LiftRef.ForallRowSideParameters at hA ⊢
  refine GlobalTheory.LiftRef.overRows_and_mono hA hA ?_
  intro K B f T w Z Wt hX z p0 Y hA1 _ Rw a M tup Q hMA hMI j h1 h2 σ S hS hPair s π τ hπ hτ
  obtain ⟨X, hXd⟩ := hA1 Rw a M tup Q hMA hMI j h1 h2
  obtain ⟨Bf, k1, k2, k3, k4⟩ := GlobalTheory.RowSphSmall.exists_form_rowRepR hN.hc hN.decay _ _ _ _ _ _ _ z.R z.F z.cG p0 Y z.pins σ
  exact thetaPair_of_hasThetaAt hN.what₂.bz _ _ X _ _ hXd σ S hS hPair s π τ hπ hτ
    (GlobalTheory.RowSphSmall.isUnitarisable_of_isLocS _ Bf k1 k2 k3 k4 s τ hτ)
end GlobalTheory.RefPair
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_reference_pair_of_trivial_mu_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.LiftRef.ForallRowSideParameters hL fun D cf rep _ _ M => ∀ (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (σ : D.what₂.FT) (S : Submodule ℂ (Formalism.AUTREP.GAf D.host.E D.R.nV → (M D.what₂.mu0 j h1 h2).wt.W)), NG.IsIrrRep (M D.what₂.mu0 j h1 h2).wt.ρ S → (∃ y ∈ D.what₂.isot j σ, ∃ F ∈ (NG.isoTyp (M D.what₂.mu0 j h1 h2).wt.ρ S).comap (M D.what₂.mu0 j h1 h2).real, inner ℂ F (D.what₂.thetaT D.what₂.mu0 j y) ≠ 0) → ∀ (s : SplitPlace D.host.E) (π : GlobalTheory.SmGL.IrrRep (GL (Fin (D.R.r + D.R.t)) (s.w.adicCompletion D.host.E))) (τ : GlobalTheory.SmGL.IrrRep (GL (Fin D.R.r) (s.w.adicCompletion D.host.E))), IsLocS (n := D.R.nV) S s π → IsLocS (rep σ).S s τ → GlobalTheory.ThetaGL.ThetaPair ((cf.mu0 ⟨j - 1, by omega⟩).loc s.w) τ.ρ (GlobalTheory.SmGL.twist π.ρ (GlobalTheory.SmGL.detChar (Fin (D.R.r + D.R.t)) (cf.eta.loc s.w))) := by
  first | exact @_root_.GlobalTheory.RefPair.referencePair_split_of_mu_eq_zero_alt | exact _root_.GlobalTheory.RefPair.referencePair_split_of_mu_eq_zero_alt | (intros; apply _root_.GlobalTheory.RefPair.referencePair_split_of_mu_eq_zero_alt <;> assumption)
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TameUniformizerPower
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace DiscreteGroups.sglob.DzType.Rt
open ValuativeRel GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.DepthZeroRankOneLabel
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {g : ℕ} [Fact g.Prime]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
open GlobalTheory.WeilDeligne in
theorem lab_eq_of_tameRep_alt : _root_.DiscreteGroups.sglob.DzType.DepthZeroInertiaBigAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (Γ : GrpSide D) (k : Fin 2) (v : D.nd.PlG k) (μ : ((D.naut.plGw k v).adicCompletion D.host.E)ˣ →* ℂˣ) (hμ : GlobalTheory.SmGL.IsSmoothChar μ), GlobalTheory.SplitWeil.IsTame μ → ∀ (u : 𝓞 D.host.E) (hu : (u : D.host.E) ≠ 0), (∃ (ϖ : 𝓞 D.host.E) (π : D.nd.Om), ϖ ∈ (D.naut.plGw k v).asIdeal ∧ ϖ ∉ (D.naut.plGw k v).asIdeal ^ 2 ∧ π ^ (normV (D.naut.plGw k v) - 1) = algebraMap D.host.E D.nd.Om (ϖ : D.host.E) ∧ (D.nd.plOm.1 (D.naut.plGw k v)).valuation (D.ntypes.tg k v π / π - algebraMap D.host.E D.nd.Om (u : D.host.E)) < 1) → ∀ c : ZMod (D.host.g k), D.ntypes.teichC k (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) c) = ((μ (Units.map (algebraMap D.host.E ((D.naut.plGw k v).adicCompletion D.host.E)).toMonoidHom (Units.mk0 (u : D.host.E) hu)) : ℂˣ) : ℂ) → _root_.GlobalTheory.PendOf.localLabelPolynomial hL D k v (Irr.ofDet 1 μ hμ) = X - C c := by
  intro hDZ hL D Γ k v μ hμ hT u hu hex c hc
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  haveI : IsTotallyComplex D.host.E := D.sp.cm.cmUnram.1
  first | (have hOpn := UpperTheory.One.M.opn _ (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 (D.naut.plGw k v))); obtain ⟨a, ha, ε, hl⟩ := hOpn) | obtain ⟨a, ha, ε, hε, hl⟩ := _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 (D.naut.plGw k v))
  have hSet : GlobalTheory.WeilDeligne.TeichmullerInertiaLabelCondition (D.nd.plOm.1 (D.naut.plGw k v)) (D.naut.plGw k v) (D.ntypes.teichC k)
      (D.ntypes.tg k v) :=
    .of_tameGenAt (GlobalTheory.TameLabels.normV_eq_of_split (D.host.g_prime k) (D.nd.g_split k)
      (D.naut.plGw_over k v)) (D.ntypes.tg_gen k v) (D.ntypes.teichC_inj k)
  have e1 : _root_.GlobalTheory.NPin.weilDeligneOfLocalIrrep hL D (D.naut.plGw k v) 1 (Irr.ofDet 1 μ hμ) =
      GlobalTheory.WeilDeligne.WD.lpOfChar _ (μ.comp a) (ha.smooth hμ) := hl.one μ hμ
  have hwild : ∀ σ : GlobalTheory.WeilDeligne.Weil (D.nd.plOm.2 (D.naut.plGw k v)),
      (σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om) ∈ GlobalTheory.WeilDeligne.Wild D.host.E (D.nd.plOm.1 (D.naut.plGw k v)) → (μ.comp a) σ = 1 :=
    _root_.GlobalTheory.DepthZeroRankOneLabel.wild_trivial_m_alt D k v μ hμ hT a ha ε _ hl
  have hval : μ (a ⟨D.ntypes.tg k v, GlobalTheory.WeilDeligne.Ine_le_Weil _ hSet.2.1⟩) =
      μ (Units.map (algebraMap D.host.E ((D.naut.plGw k v).adicCompletion D.host.E)).toMonoidHom (Units.mk0 (u : D.host.E) hu)) := by
    obtain ⟨I⟩ := GlobalTheory.TypeRec.Model.nonempty_ident D
    have hw := D.naut.plGw_over k v
    have hN := GlobalTheory.TameLabels.normV_eq_of_split (D.host.g_prime k) (D.nd.g_split k) hw
    have hw2 : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∉ (D.naut.plGw k v).asIdeal ^ 2 := fun h2 => by
      have h0 : Ideal.span {((D.host.g k : ℕ) : 𝓞 D.host.E)} ≠ 0 := by
        rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
        exact_mod_cast (D.host.g_prime k).ne_zero
      have hs := (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors h0).2
        (Formalism.MainNotions.ModuliIntegralCharts.H1.GSplit.split_of_ncard (D.host.g_prime k) (D.nd.g_split k)).2
      have := hs (D.naut.plGw k v).asIdeal (by rw [← sq, Ideal.dvd_span_singleton]; exact h2)
      exact (D.naut.plGw k v).isPrime.ne_top (Ideal.isUnit_iff.1 this)
    obtain ⟨ϖ, π, hϖ, hϖ2, hπ, hv⟩ := hex
    obtain ⟨n, hn, hun, hgen⟩ := GlobalTheory.DepthZeroRankOneLabel.residue_of_cong _ _ _ (D.nd.plOm.2 _) hN hw hw2
      (Γ.kv k v) _ (Γ.ζ k) (D.ntypes.tg_mem k v) (Γ.ζ_gen k) (Γ.tg_tame k v) u ϖ π hϖ hϖ2 hπ hv
    have hx := GlobalTheory.DepthZeroRankOneLabel.val_lt_of_mem hun
    exact _root_.DiscreteGroups.sglob.DzType.Rt.character_inertia_eq_of_congruent_generator hDZ hl (I.i k v) (I.cont k v) hw (Γ.kv k v)
      (GlobalTheory.DepthZeroRankOneLabel.labDatum (D.ntypes.teichC k) (D.ntypes.teichC_inj k) (Γ.ζ k) (Γ.ζ_gen k))
      _ (D.ntypes.tg_mem k v) (Γ.tg_tame k v) μ hμ hT n hn hgen _ (by simpa using hx)
  unfold _root_.GlobalTheory.PendOf.localLabelPolynomial
  rw [e1, GlobalTheory.WeilDeligne.WD.lab_lpOfChar_eq_iff hSet _ hwild c, hc, MonoidHom.comp_apply, hval]
set_option maxHeartbeats 1000000 in
theorem tame_uniformizer_power_alt : _root_.DiscreteGroups.sglob.DzType.DepthZeroInertiaBigAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (Γ : GrpSide D) (k : Fin 2) (v : D.nd.PlG k) (μ : ((D.naut.plGw k v).adicCompletion D.host.E)ˣ →* ℂˣ) (hμ : GlobalTheory.SmGL.IsSmoothChar μ), GlobalTheory.SplitWeil.IsTame μ → ∀ (u : 𝓞 D.host.E) (hu : (u : D.host.E) ≠ 0), (∃ (ϖ : 𝓞 D.host.E) (π : D.nd.Om), ϖ ∈ (D.naut.plGw k v).asIdeal ∧ ϖ ∉ (D.naut.plGw k v).asIdeal ^ 2 ∧ π ^ (normV (D.naut.plGw k v) - 1) = algebraMap D.host.E D.nd.Om (ϖ : D.host.E) ∧ (D.nd.plOm.1 (D.naut.plGw k v)).valuation (D.ntypes.tg k v π / π - algebraMap D.host.E D.nd.Om (u : D.host.E)) < 1) → ∀ c : ZMod (D.host.g k), D.ntypes.teichC k (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) c) = ((μ (Units.map (algebraMap D.host.E ((D.naut.plGw k v).adicCompletion D.host.E)).toMonoidHom (Units.mk0 (u : D.host.E) hu)) : ℂˣ) : ℂ) → _root_.GlobalTheory.PendOf.localLabelPolynomial hL D k v (Irr.ofDet 1 μ hμ) = X - C c :=
  _root_.DiscreteGroups.sglob.DzType.Rt.lab_eq_of_tameRep_alt
end DiscreteGroups.sglob.DzType.Rt
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThmAUpperStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toric_ratio_family_estimate' : GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.ToricRatioConjugates → _root_.GlobalTheory.BigTop.Fun.SettingAtPoint → (Closed FamHyp fun Fm _ => _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun x _ i _ => |(Fm.L x i).logDerivativeAtOne| ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) → FieldDat → TorEx → (_root_.GlobalTheory.BigTop.Fun.LeafConditions (Fitted @Comparison₂) fun p _ d _ _ => ThA d.G p.P.A3.A.μ0 p.R.mu) := by
  first | exact @_root_.GlobalTheory.ThmAUpper.thmA_upper_alt | exact _root_.GlobalTheory.ThmAUpper.thmA_upper_alt | (intros; apply _root_.GlobalTheory.ThmAUpper.thmA_upper_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TiedConditionOfLayer
section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.HeightCounting.Up.RealOfReading
noncomputable section
namespace GlobalTheory.HeightCounting.Up
open RealOfReading
theorem isTied_of_layer_member_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c =>
    ∃ X : _root_.GlobalTheory.NRows.LinkedData hL (w.D Z), _root_.GlobalTheory.HeightCounting.Up.PinnedAtCharacterChoice c.a X.P ∧ HEq X.X.R t.r.z.R.toRealDat := by
  intro hP hL
  refine _root_.GlobalTheory.HeightCounting.Up.Model.AtMem.at_member_imp (_root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z (_root_.GlobalTheory.T.exists_character_choice_pin_at_of_third_layer hP hL) (_root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z (_root_.GlobalTheory.T.coefField_eq_TC_cf_at_member_of_published_inputs hP hL)
    (_root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z (_root_.GlobalTheory.T.xiH_tupT_eq_tp_xi_of_used0_at_member hP hL) (_root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z (_root_.GlobalTheory.T.exists_parameter_choice_and_lamAt_gap_at_member hP hL)
    (_root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z (_root_.GlobalTheory.T.typesTrue_at_member_of_published_inputs hP hL) (_root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z (_root_.GlobalTheory.T.exists_eigIdx_labeling_at_member hP hL)
    (_root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z (_root_.GlobalTheory.T.nonempty_agree_realOfRead_at_member hP hL) (_root_.GlobalTheory.T.good_idempotent_reads_as_type_projector_at_member hP hL)))))))) ?_
  rintro K B f T w Z Wt p0 t nch n c ⟨⟨P, hPin⟩, hC, htup, ⟨hPar, hGap⟩, hTT, ⟨Xd, E, ⟨labPi⟩⟩, hAg, hE0⟩
  have hg : GlobalTheory.LiftRows.Given t.r.z.R.toRealDat t.r.z.F.lv2 :=
    ⟨(GlobalTheory.CoreOfWeak.core_of_weak t.r.z.R t.r.z.F t.r.z.pins.char t.exAt).1, hPar, t.r.intersectionNumber_baseChange.ok.ok2.irr,
      GlobalTheory.HeightCounting.goodTypes_of_typesTrue_real _ _ _ _ _ _ _ t.r.z.pins.char.base.lev hTT, t.r.z.pins.keep.guard, hGap⟩
  obtain ⟨ag⟩ := hAg hC Xd E labPi t.r.z.pins.char.base htup hg t.r.z.pins.char.fullP
  obtain ⟨T0, hT0, hR⟩ := _root_.GlobalTheory.HeightCounting.Up.RealOfReading.exists_linked_data_of_agreement P (realOfRead t.r.z.R.toRealDat t.r.z.F.lv2 t.r.Y n.tp hC Xd E labPi
    t.r.z.pins.char.base htup hg t.r.z.pins.char.fullP) hPin.cf_eq hPin.C_eq hPin.tp_eq
    hPin.M_eq (hPin.rep_eq.trans c.row.rep_eq) ag (hE0 hC Xd E labPi t.r.z.pins.char.base htup hg t.r.z.pins.char.fullP)
  exact ⟨T0, by rw [hT0]; exact hPin, hR⟩
end GlobalTheory.HeightCounting.Up
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linked_data_pinned_at_layer : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c => ∃ X : _root_.GlobalTheory.NRows.LinkedData hL (w.D Z), _root_.GlobalTheory.HeightCounting.Up.PinnedAtCharacterChoice c.a X.P ∧ HEq X.X.R t.r.z.R.toRealDat := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.isTied_of_layer_member_alt | exact _root_.GlobalTheory.HeightCounting.Up.isTied_of_layer_member_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.isTied_of_layer_member_alt <;> assumption)
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UnitaryOfLocalLanglands
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_of_local_langlands' : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (A : _root_.GlobalTheory.HeightCounting.AUSideAlt D), _root_.GlobalTheory.HeightCounting.AutomorphicSideRealised hL D T A → _root_.UpperTheory.One.M.Ud.UnitaryReadS D.nbc (_root_.GlobalTheory.FormDict.recT_alt T hL) := by
  first | exact @_root_.UpperTheory.One.M.unitaryRead_true_alt trivial | exact (_root_.UpperTheory.One.M.unitaryRead_true_alt trivial) | (intros; apply (_root_.UpperTheory.One.M.unitaryRead_true_alt trivial) <;> assumption)
end
end

