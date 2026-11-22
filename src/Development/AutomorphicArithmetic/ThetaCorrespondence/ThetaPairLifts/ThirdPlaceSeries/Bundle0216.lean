import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0380
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0197
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0018
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0012
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0207
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0199
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0017
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0141
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0027
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0032
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0062
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0140
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0161
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0094
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.PotentialCrystallinity.InertialTypeOfTameM
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0024
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0200
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.Bundle0002
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0202
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0790
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0128
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0030
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0209
import Development.DiscreteGroups.GlobalIrreducibility.LocTypeOfSerParamLe

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GaloisRepLocalGlobalCompatible
section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.L2.Host
namespace GlobalTheory.LocCompTy
open GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
set_option maxHeartbeats 2000000 in
theorem localGlobal_compatible_at_place_alt (hPr : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D)
    (hCen : GlobalTheory.HeightCounting.Up.CenLoc D P.M) (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) (w : PlE D.host)
    (hw : w = D.naut.plGw k v) (e : ℚ_[D.host.g k] ≃+* w.adicCompletion D.host.E) (he : Continuous e)
    (rcw : ∀ n, QRep (D.host.g k) n → D.naut.LP w)
    (hrc : ∀ n (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (w.adicCompletion D.host.E))) (π : QRep (D.host.g k) n),
      Nonempty (π ≅ Rep.of (σ.ρ.comp (Matrix.GeneralLinearGroup.map e.toRingHom))) →
      P.T.e w (rcw n π) = _root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 w) (GlobalTheory.LocLanglands.cls σ)) :
    ∃ (μ : ℚ_[D.host.g k]ˣ →* ℂˣ) (χ : (ZMod (D.host.g k))ˣ →* ℂˣ), TamePart μ χ ∧
      D.naut.locG (D.naut.muC i) w = rcw 1 (Rep.of (Model.detRep 1 μ)) ∧
      ∀ Q : D.naut.AV i, ∃ π : QRep (D.host.g k) D.R.nV, IrrSm π ∧ D.naut.locV i Q w = rcw D.R.nV π ∧
        ActsThrough π D.R.r D.R.t χ (D.naut.typeV i Q)
          fun a => D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v a) := by
  classical
  have hjr := D.nd.j_range i
  let j0 : Fin D.R.m := ⟨D.nd.j i - 1, by omega⟩
  have hj0 : j0.1 + 1 = D.nd.j i := by simp only [j0]; omega
  have hsp : IsSplitPl D.host w := hw ▸ GlobalTheory.FixedPlaceSplit.isSplitPl_plGw D k v
  obtain ⟨s, hs⟩ := GlobalTheory.TypeBlockPf.splitAt D _ hsp
  subst hs
  have htame : GlobalTheory.SplitWeil.IsTame ((P.tp.tup (D.nd.mu i) j0).loc s.w) :=
    GlobalTheory.MuTameQS.isTame_loc (GlobalTheory.MuTameQS.tameAt_mul ((P.cf.isMu0 j0).tame _) (P.tp.xi_tame _ _))
  obtain ⟨χ, hχ⟩ := GlobalTheory.T.exists_tameInflationCharacter_of_padic_iso _ _ e he _ htame
  refine ⟨_, χ, hχ, _root_.GlobalTheory.T.local_langlands_split_qp_alt_alt hPr hL D P i j0 hj0 k s.w e rcw hrc, fun Q => ?_⟩
  obtain ⟨σ, hσ, -⟩ := GlobalTheory.T.splitPlaceLocalComponent_exists_unique_class D.host.E D.R.nV (P.H.av.rep i Q) s
  have hσ' : IsLocS (n := D.R.nV) (P.H.av.S i Q) s σ := hσ
  refine ⟨Rep.of (σ.ρ.comp (Matrix.GeneralLinearGroup.map e.toRingHom)), GlobalTheory.T.isIrreducibleSmooth_pullback_padic_ringIso _ _ e he _ σ, ?_, ?_⟩
  · apply (P.T.e s.w).injective
    rw [hrc _ σ _ ⟨CategoryTheory.Iso.refl _⟩, D.nbc.embAV_loc, P.H.emb]
    exact P.au _ _ _ _ s _ hσ'
  obtain ⟨c, T, hc, hci, -, -, -⟩ := hσ
  set ξ := (P.tp.tup (D.nd.mu i) j0).loc s.w with hξ
  have hT : ∀ F, F ∈ D.naut.typeV i Q ↔
      (P.M.loc i).real F ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q) := fun F => by
    rw [P.H.av.typeV]; exact Submodule.mem_comap
  let J := {φ : (GAf D.host.E D.R.nV → (P.M.loc i).wt.W) →ₗ[ℂ] σ.V // ∀ x, TrivOutside {s.v} x →
    ∀ f' ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q),
      φ (NG.rt D.host.E D.R.nV x f') = σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)) (φ f')}
  let ι : D.naut.typeV i Q →ₗ[ℂ] (J → σ.V) :=
    LinearMap.pi fun φ => φ.1.comp ((P.M.loc i).real.comp (D.naut.typeV i Q).subtype)
  have hpar : ∀ (φ : J) (F : D.naut.typeV i Q),
      IsParVec (σ.ρ.comp (Matrix.GeneralLinearGroup.map e.toRingHom)) D.R.r D.R.t χ (φ.1 ((P.M.loc i).real F)) := by
    intro φ F
    refine GlobalTheory.T.isParahoricTypeVector_of_blockTypeVector_padic_iso _ _ e he ξ χ hχ D.R.r D.R.t σ.V σ.ρ _ ?_
    refine GlobalTheory.BlockType.isBlockVec_of (r := D.R.r) (t := D.R.t) ξ σ.ρ _ fun h hh => ?_
    obtain ⟨x, hx, hxe⟩ := GlobalTheory.SplitLift.exists_trivOutside_loc_eq D.R.nV s
      (Matrix.GeneralLinearGroup.map c.symm.toRingHom h)
    have hmap : Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x) = h := by
      rw [hxe]; exact Units.ext (Matrix.ext fun a b => c.apply_symm_apply _)
    have hF := (hT F).1 F.2
    have hh2 : Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x) ∈
        GlobalTheory.BlockType.blockGrp (s.w.adicCompletion D.host.E) D.R.r D.R.t := by rw [hmap]; exact hh
    have h3 := φ.2 x hx _ hF
    rw [_root_.GlobalTheory.LocCompTy.blockEig_alt hL D P i Q k v j0 hj0 s hw c hc hci F x hx hh2, map_smul] at h3
    rw [← hmap]; exact h3.symm
  have hinj : Function.Injective ι := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro F hF
    by_contra hne
    have h1 : (P.M.loc i).real F ≠ 0 := fun h0 =>
      hne (Subtype.ext ((P.M.loc i).real_inj (h0.trans (map_zero _).symm)))
    obtain ⟨φ, hφ, hφe⟩ := GlobalTheory.T.isotypic_local_component_fixed D.host.E D.R.nV (P.M.loc i).wt (P.H.av.S i Q) (P.H.av.irr i Q) s σ hσ' c hc hci _
      ((hT F).1 F.2) h1
    exact hφ (congrFun (LinearMap.mem_ker.1 hF) ⟨φ, hφe⟩)
  refine ⟨J, ι, hinj, fun F φ => hpar φ F, fun a ha F => ?_⟩
  have hzc : ∀ b, a * b = b * a := fun b => (Subalgebra.mem_center_iff.1 ha b).symm
  have hcz := GlobalTheory.SeriesSupportTest.atPlace_central D k v a hzc
  obtain ⟨L, hLift, hCL⟩ := hCen i
  have e0 : (P.M.loc i).real (D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v a) F) =
      actSum D L (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v a) ((P.M.loc i).real F) := by
    rw [NTypes.onMt, dif_pos hcz]; exact hCL ⟨_, hcz⟩ F
  let g : GL (Fin D.R.r) (ZMod (D.host.g k)) → G0g D.nd := fun h =>
    Pi.mulSingle (M := fun kv : (Σ k : Fin 2, D.nd.PlG k) => GL (Fin D.R.r) (ZMod (D.host.g kv.1))) ⟨k, v⟩ h
  have hsum : actSum D L (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v a) ((P.M.loc i).real F) =
      ∑ h, a.coeff h • NG.rt D.host.E D.R.nV (L (g h)) ((P.M.loc i).real F) := by
    unfold actSum Formalism.MainNotions.ArithmeticCylinders.atPlace
    rw [MonoidAlgebra.coeff_ofCoeff, Finsupp.sum_mapDomain_index
      (h := fun g c => c • NG.rt D.host.E D.R.nV (L g) ((P.M.loc i).real F))
      (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)]
    exact Finsupp.sum_fintype _ _ (fun _ => zero_smul _ _)
  have hg : ∀ h, ∃ x : GAf D.host.E D.R.nV, TrivOutside {s.v} x ∧
      IsLiftN h (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)) ∧
      NG.rt D.host.E D.R.nV (L (g h)) ((P.M.loc i).real F) = NG.rt D.host.E D.R.nV x ((P.M.loc i).real F) := fun h =>
    _root_.GlobalTheory.T.lift_through_completion_iso_alt hL D P i Q k v s hw c hc hci L hLift F F.2 h (g h) (by simp [g])
      (fun kv hkv => by simp [g, Pi.mulSingle_eq_of_ne hkv])
  choose xs hxs using hg
  have hF := (hT F).1 F.2
  have e1 : (P.M.loc i).real (D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v a) F) =
      ∑ h, a.coeff h • NG.rt D.host.E D.R.nV (xs h) ((P.M.loc i).real F) := by
    rw [e0, hsum]; exact Finset.sum_congr rfl fun h _ => by rw [(hxs h).2.2]
  have hmem : D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v a) F ∈ D.naut.typeV i Q := by
    rw [hT, e1]
    exact Submodule.sum_mem _ fun h _ => Submodule.smul_mem _ _ (rt_mem_isoTyp _ _ _ hF)
  refine ⟨hmem, fun φ => ?_⟩
  have hu := (hpar φ F).1
  change φ.1 ((P.M.loc i).real (D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v a) F)) =
    actTop (σ.ρ.comp (Matrix.GeneralLinearGroup.map e.toRingHom)) D.R.r D.R.t a (φ.1 ((P.M.loc i).real F))
  rw [e1, map_sum, actTop, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [map_smul, φ.2 _ (hxs h).1 _ hF, LinearMap.smul_apply, MonoidHom.comp_apply]
  congr 1
  exact GlobalTheory.T.blockLift_action_on_principalCongruenceFixedVectors _ _ e he D.R.r D.R.t σ.V σ.ρ _ hu h _ (hxs h).2.1
theorem locComp_of_isRc_classMapD_cenLoc : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (I : Ident D) (rc : GlobalTheory.SerSys.Corr D), _root_.GlobalTheory.TypeRec.IsSeriesCorrespondence hL P.T I rc → (∀ k v, _root_.GlobalTheory.SerSys.IsClassMapD D.naut.lpDim (rc k v)) → GlobalTheory.HeightCounting.Up.CenLoc D P.M → _root_.GlobalTheory.SerSys.LocalCompatibility D rc := by
  intro hPr hL D P I rc hRc hCM hCen
  exact ⟨hCM, fun i k v => _root_.GlobalTheory.LocCompTy.localGlobal_compatible_at_place_alt hPr hL D P hCen i k v _ rfl (I.i k v) (I.cont k v) (rc k v)
    fun n σ π h => hRc k v n σ π h⟩
end GlobalTheory.LocCompTy
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.locComp_of_isRc_of_classMap_of_cenLoc : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (I : Ident D) (rc : GlobalTheory.SerSys.Corr D), _root_.GlobalTheory.TypeRec.IsSeriesCorrespondence hL P.T I rc → (∀ k v, _root_.GlobalTheory.SerSys.IsClassMapD D.naut.lpDim (rc k v)) → GlobalTheory.HeightCounting.Up.CenLoc D P.M → _root_.GlobalTheory.SerSys.LocalCompatibility D rc := by
  first | exact @_root_.GlobalTheory.LocCompTy.locComp_of_isRc_classMapD_cenLoc | exact _root_.GlobalTheory.LocCompTy.locComp_of_isRc_classMapD_cenLoc | (intros; apply _root_.GlobalTheory.LocCompTy.locComp_of_isRc_classMapD_cenLoc <;> assumption)
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HilbertSamuelBergmanFrameBound
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
noncomputable section
namespace GlobalTheory.FrameBerg
end GlobalTheory.FrameBerg
namespace GlobalTheory.FrameBerg
set_option maxHeartbeats 2000000 in
theorem bergman_frames_of_short_range_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ Z, Nonempty (CuspFrame Z Y.U (xiR (Fm.D x ι)) (fun _ => (Fm.D x ι).sp.W ((i : ℕ) + 1)) Y.dict (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₂) ∧ ∃ (f₁ : CuspFrame Z Y.U (xiR (Fm.D x ι)) (fun _ => (Fm.D x ι).sp.W ((i : ℕ) + 1)) Y.dict (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁) (Λ β : ℝ), 1 ≤ Λ ∧ 1 ≤ β ∧ Real.log f₁.n ≤ PP ∧ Real.log β ≤ PP ∧ Real.log Λ ≤ PP * (kap p i / lenT p i PP + 1) ∧ (∀ q σ, ChowHt.frameNorm (f₁.A σ) (fun a => σ (f₁.w.col q a)) ≤ Λ) ∧ BergLe Z Y.U (fun _ => (Fm.D x ι).sp.W ((i : ℕ) + 1)) Y.dict (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ β := by
  intro hP2 _hDG hS hFD
  obtain ⟨C1, hC1, H1⟩ := _root_.GlobalTheory.T.short_generator_norm_comparison hP2
  obtain ⟨C2, hC2, H2⟩ := _root_.UpperTheory.Lit.Tam.tamagawa_number_formula hP2
  have H0 := _root_.GlobalTheory.T.covering_domain_lattice_regularity hP2
  refine (((_root_.GlobalTheory.T.weight_parameter_strict_antitone_alt hS).and (_root_.GlobalTheory.T.size_bounds_for_family_alt hS)).and (_root_.GlobalTheory.HSApp.wtBig_run_alt.and hFD)).imp fun Fm CH _ hh => ?_
  obtain ⟨⟨⟨_, _, a, ha⟩, ⟨_, _, b, hb⟩⟩, ⟨⟨_, _, c, hc⟩, ⟨_, _, d, hd⟩⟩⟩ := hh
  obtain ⟨e, he⟩ := GlobalTheory.family_sizes_eventually_large _ Fm (2 * C1 + C2 + 1)
  refine ⟨0, le_rfl, max (max a b) (max (max c d) e), fun x hx hle ι p hp i hi Y hY => ?_⟩
  have hA := ha x hx ((le_max_left _ _).trans ((le_max_left _ _).trans hle)) ι p hp i hi
  have hB := hb x hx ((le_max_right _ _).trans ((le_max_left _ _).trans hle)) ι p hp i hi Y hY
  have hW := hc x hx ((le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hle))) ι p hp i hi
  have hF := hd x hx ((le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hle))) ι p hp i hi Y hY
  have hLM := (he x ((le_max_right _ _).trans ((le_max_right _ _).trans hle)) ι).2.2.1
  clear ha hb hc hd he
  obtain ⟨h1p, h1q, hfin, -, hanti, -⟩ := hA
  obtain ⟨hLaws, hInR, hL1, hM, hfs, hfr, -, -, h8f, h100r, hflat, hkap, hZ12, -, -, -, hsum, -⟩ := hB
  obtain ⟨hr, hdim, -⟩ := GlobalTheory.RecGaps.gaps p (Fm.params x hx ι) i hi
  intro Zc
  set P : WtPar (dat p i) := ⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i (Fm.parT x hx ι).PP⟩ with hPdef
  have hq : (dat p i).p - 1 + 1 < (dat p i).p + (dat p i).q := by omega
  have hg1 : ∀ τ, 1 ≤ gap (P.u₁ τ) ((dat p i).p - 1) := fun τ => one_le_gap_of_strictAnti (hanti τ).1 hq
  have ha1 : ∀ τ, Antitone (P.u₁ τ) := fun τ => (hanti τ).1.antitone
  have hgap2 : ∀ τ k, k + 1 < (dat p i).p + (dat p i).q → 1 ≤ gap (P.u₂ τ) k := by
    intro τ k hk
    have e : P.u₂ τ = P.u₁ τ + P.rem τ := rfl
    rw [e, gap_add]
    have := one_le_gap_of_strictAnti (hanti τ).1 hk
    have := (P.gap_rem τ k).1
    omega
  have ha2 : ∀ τ, Antitone (P.u₂ τ) := fun τ =>
    antitone_of_gap_nonneg fun k hk => (zero_lt_one.le).trans (hgap2 τ k hk)
  have hG := H0 (Fm.D x ι) p.T hLaws ((i : ℕ) + 1) h1p h1q hfin hInR Y _ _ hY.1
  refine ⟨nonempty_cuspFrame ((hG P.u₂ ha2 fun τ => hgap2 τ _ hq).2 Zc), ?_⟩
  have hgapBig : ∀ τ, ((8 * (Fm.D x ι).R.f * (Fm.D x ι).R.r + 10 : ℕ) : ℤ) ≤ gap (P.u₁ τ) ((dat p i).p - 1) := by
    intro τ
    refine le_trans ?_ (hW.gaps τ ((dat p i).p - 1) hq)
    have h9 : 9 * (Fm.D x ι).R.r ≤ (Fm.D x ι).R.r.choose 2 := by
      rw [Nat.choose_two_right]
      apply (Nat.le_div_iff_mul_le two_pos).2
      have : 100 ≤ (Fm.D x ι).R.r := h100r
      have : 99 ≤ (Fm.D x ι).R.r - 1 := by omega
      nlinarith
    rw [hdim, hr]
    generalize (Fm.D x ι).R.r.choose 2 = c at h9 ⊢
    generalize ((Fm.D x ι).R.f * c + 1).choose 2 = B
    have h1 : 9 * (Fm.D x ι).R.f * (Fm.D x ι).R.r ≤ (Fm.D x ι).R.f * c := by
      rw [mul_assoc, mul_comm 9, mul_assoc, mul_comm (Fm.D x ι).R.r]; exact Nat.mul_le_mul_left _ h9
    have h2 : B + 4 * (Fm.D x ι).R.r + (Fm.D x ι).R.f * c + 3 ≤
        ((Fm.D x ι).R.f * c + 3) * (B + 4 * (Fm.D x ι).R.r + (Fm.D x ι).R.f * c + 3) :=
      Nat.le_mul_of_pos_left _ (by omega)
    have h3 : 8 ≤ (Fm.D x ι).R.f := h8f
    have h4 : 8 * (Fm.D x ι).R.f * (Fm.D x ι).R.r + 10 ≤ 9 * (Fm.D x ι).R.f * (Fm.D x ι).R.r := by
      have : 10 ≤ (Fm.D x ι).R.f * (Fm.D x ι).R.r := by nlinarith
      nlinarith
    exact_mod_cast (h4.trans (h1.trans (by omega))).trans h2
  have hL1' : (1 : ℝ) ≤ (Fm.L x ι).sc.L := hL1
  have hZdef : ((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r * (Fm.L x ι).sc.L = zBase (Fm.L x ι) := rfl
  have hf8 : (8 : ℝ) ≤ (Fm.D x ι).R.f := by exact_mod_cast h8f
  have hr100 : (100 : ℝ) ≤ (Fm.D x ι).R.r := by exact_mod_cast h100r
  have hfrpos : (0 : ℝ) < ((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r := by positivity
  have hE2 : (2 : ℝ) ≤ Real.exp (Fm.L x ι).sc.L := by linarith [Real.add_one_le_exp (Fm.L x ι).sc.L]
  have hfrE : ((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r ≤ Real.exp (Fm.L x ι).sc.L := by
    have := Real.exp_le_exp.2 hfr
    rwa [Real.exp_log (by exact_mod_cast hfrpos)] at this
  have hLE : (Fm.L x ι).sc.L ≤ Real.exp (Fm.L x ι).sc.L := by linarith [Real.add_one_le_exp (Fm.L x ι).sc.L]
  have hZE : zBase (Fm.L x ι) ≤ Real.exp (Fm.L x ι).sc.L ^ 2 := by
    rw [← hZdef, sq]; exact mul_le_mul hfrE hLE (by linarith) (Real.exp_pos _).le
  have hZL : (Fm.L x ι).sc.L ≤ zBase (Fm.L x ι) := by
    rw [← hZdef]
    have : (1 : ℝ) ≤ ((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r := by nlinarith
    nlinarith
  have hZ1 : (1 : ℝ) ≤ zBase (Fm.L x ι) := hL1'.trans hZL
  have hkap0 : 0 ≤ kap p i := by unfold CovTop.kap sizeK; positivity
  have hkapE : kap p i ≤ Real.exp (Fm.L x ι).sc.L ^ 2 := by
    rcases hkap0.eq_or_lt with h0 | h0
    · rw [← h0]; positivity
    · have := Real.exp_le_exp.2 hkap
      rw [Real.exp_log h0] at this
      rw [← Real.exp_nat_mul]; push_cast; linarith
  have hK1 : (1 : ℝ) ≤ kap p i / lenT p i (Fm.parT x hx ι).PP + 1 := by
    have : 0 ≤ kap p i / lenT p i (Fm.parT x hx ι).PP := div_nonneg hkap0 (Nat.cast_nonneg _)
    linarith
  have hKle : kap p i / lenT p i (Fm.parT x hx ι).PP ≤ kap p i := by
    rcases Nat.eq_zero_or_pos (lenT p i (Fm.parT x hx ι).PP) with h0 | h0
    · rw [h0]; simp [hkap0]
    · exact div_le_self hkap0 (by exact_mod_cast h0)
  have hS := hsum P.u₁ (by simp)
  have hS0 : 0 ≤ ∑ τ, ∑ k, |(P.u₁ τ k : ℝ)| := by positivity
  have hSE : ∑ τ, ∑ k, |(P.u₁ τ k : ℝ)| ≤ Real.exp (7 * (Fm.L x ι).sc.L) := by
    have e7 : Real.exp (7 * (Fm.L x ι).sc.L) = Real.exp (Fm.L x ι).sc.L ^ 7 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [e7]
    refine hS.trans ?_
    have hZ2 : zBase (Fm.L x ι) ^ 2 ≤ Real.exp (Fm.L x ι).sc.L ^ 4 := by
      calc zBase (Fm.L x ι) ^ 2 ≤ (Real.exp (Fm.L x ι).sc.L ^ 2) ^ 2 := pow_le_pow_left₀ (by linarith) hZE 2
        _ = _ := by ring
    have hK3 : kap p i / lenT p i (Fm.parT x hx ι).PP + 1 ≤ Real.exp (Fm.L x ι).sc.L ^ 3 := by
      nlinarith
    calc zBase (Fm.L x ι) ^ 2 * (kap p i / lenT p i (Fm.parT x hx ι).PP + 1)
        ≤ Real.exp (Fm.L x ι).sc.L ^ 4 * Real.exp (Fm.L x ι).sc.L ^ 3 :=
          mul_le_mul hZ2 hK3 (by linarith) (by positivity)
      _ = _ := by ring
  have hlogS : Real.log (∑ τ, ∑ k, |(P.u₁ τ k : ℝ)|) ≤ 7 * (Fm.L x ι).sc.L := by
    rcases hS0.eq_or_lt with h0 | h0
    · rw [← h0, Real.log_zero]; linarith
    · exact (Real.log_le_iff_le_exp h0).2 hSE
  have ho : 391 * zBase (Fm.L x ι) ^ 2 ≤ 391 * (((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r * (Fm.L x ι).sc.L) ^ 2 := by
    rw [hZdef]
  have hc₁ : |-GlobalTheory.FlatLine.flatDegVal (dat p i) (Formalism.L2.DIV.ofRecord (Fm.D x ι) (Fm.L x ι) p.Del p.h0).logOm| ≤
      9 * (Fm.D x ι).R.r * (Fm.L x ι).sc.L := by rw [abs_neg]; exact hflat
  obtain ⟨n, w, abelian₂, hsg, hLam, hn⟩ := H1 (Fm.D x ι) p.T hLaws ((i : ℕ) + 1) h1p h1q hfin hInR Y _ _ hY.1
    (Fm.L x ι).sc.L hL1 hM hfs hfr ho _ hF hc₁ P.u₁ ha1 hgapBig (by linarith) Zc
  obtain ⟨f, hfn, -, hfN⟩ := exists_latFrame_of_isShortGen _ _ _ _ n w abelian₂
    (nonempty_cuspFrame ((hG P.u₁ ha1 hg1).2 Zc)) hsg
  have hb := (H2 (Fm.D x ι) p.T hLaws ((i : ℕ) + 1) h1p h1q hfin hInR Y _ _ hY.1
    (Fm.L x ι).sc.L hL1 hM hfs hfr ho P.u₁ ha1 (by linarith) Zc).1
  rw [hZdef] at hLam hn hb
  have hMZ : 2 * C1 + C2 + 1 ≤ zBase (Fm.L x ι) := hLM.trans hZL
  have hZ35 : zBase (Fm.L x ι) ^ 3 ≤ zBase (Fm.L x ι) ^ 5 := pow_le_pow_right₀ hZ1 (by norm_num)
  have hZ612 : zBase (Fm.L x ι) ^ 6 ≤ zBase (Fm.L x ι) ^ 12 := pow_le_pow_right₀ hZ1 (by norm_num)
  have hZ5 : 0 ≤ zBase (Fm.L x ι) ^ 5 := by positivity
  have hkey : (2 * C1 + C2) * zBase (Fm.L x ι) ^ 5 ≤ zBase (Fm.L x ι) ^ 12 := by
    have : (2 * C1 + C2) * zBase (Fm.L x ι) ^ 5 ≤ zBase (Fm.L x ι) * zBase (Fm.L x ι) ^ 5 :=
      mul_le_mul_of_nonneg_right (by linarith) hZ5
    nlinarith
  have hPP0 : 0 ≤ (Fm.parT x hx ι).PP := le_trans (by positivity) hZ12
  have hC1Z : C1 * zBase (Fm.L x ι) ^ 3 ≤ (Fm.parT x hx ι).PP := by nlinarith
  have hC2Z : C2 * zBase (Fm.L x ι) ^ 3 ≤ (Fm.parT x hx ι).PP := by nlinarith
  refine ⟨f, max abelian₂ 1, Real.exp (C2 * zBase (Fm.L x ι) ^ 3), le_max_right _ _,
    Real.one_le_exp (by positivity), ?_, ?_, ?_, fun q σ => (hfN q σ).trans (le_max_left _ _), hb⟩
  · rw [hfn]; exact hn.trans hC1Z
  · rw [Real.log_exp]; exact hC2Z
  · rcases le_total abelian₂ 1 with hl | hl
    · rw [max_eq_right hl, Real.log_one]; positivity
    · rw [max_eq_left hl]
      refine hLam.trans ?_
      have h3 : zBase (Fm.L x ι) ^ 3 * ∑ τ, ∑ k, |(P.u₁ τ k : ℝ)| ≤
          zBase (Fm.L x ι) ^ 5 * (kap p i / lenT p i (Fm.parT x hx ι).PP + 1) := by
        have := mul_le_mul_of_nonneg_left hS (by positivity : (0 : ℝ) ≤ zBase (Fm.L x ι) ^ 3)
        nlinarith
      have h4 : C1 * (zBase (Fm.L x ι) ^ 3 * ∑ τ, ∑ k, |(P.u₁ τ k : ℝ)| + zBase (Fm.L x ι) ^ 5) ≤
          (2 * C1 * zBase (Fm.L x ι) ^ 5) * (kap p i / lenT p i (Fm.parT x hx ι).PP + 1) := by
        have h6 := mul_le_mul_of_nonneg_left h3 hC1
        have h5 : C1 * zBase (Fm.L x ι) ^ 5 ≤ C1 * zBase (Fm.L x ι) ^ 5 * (kap p i / lenT p i (Fm.parT x hx ι).PP + 1) :=
          le_mul_of_one_le_right (by positivity) hK1
        linarith [h6, h5]
      refine h4.trans (mul_le_mul_of_nonneg_right ?_ (by linarith))
      nlinarith
end GlobalTheory.FrameBerg
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
theorem _root_.GlobalTheory.T.hilbertSamuel_bergman_frame_bound_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ Z, Nonempty (CuspFrame Z Y.U (xiR (Fm.D x ι)) (fun _ => (Fm.D x ι).sp.W ((i : ℕ) + 1)) Y.dict (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₂) ∧ ∃ (f₁ : CuspFrame Z Y.U (xiR (Fm.D x ι)) (fun _ => (Fm.D x ι).sp.W ((i : ℕ) + 1)) Y.dict (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁) (Λ β : ℝ), 1 ≤ Λ ∧ 1 ≤ β ∧ Real.log f₁.n ≤ PP ∧ Real.log β ≤ PP ∧ Real.log Λ ≤ PP * (kap p i / lenT p i PP + 1) ∧ (∀ q σ, ChowHt.frameNorm (f₁.A σ) (fun a => σ (f₁.w.col q a)) ≤ Λ) ∧ BergLe Z Y.U (fun _ => (Fm.D x ι).sp.W ((i : ℕ) + 1)) Y.dict (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ β := by
  first | exact @_root_.GlobalTheory.FrameBerg.bergman_frames_of_short_range_alt | exact _root_.GlobalTheory.FrameBerg.bergman_frames_of_short_range_alt | (intros; apply _root_.GlobalTheory.FrameBerg.bergman_frames_of_short_range_alt <;> assumption)
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.InertialTypeOfTameM
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead
namespace GlobalTheory.TameType
theorem inertialType_of_tame_m_alt : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N) (T : WDTie N A) (S : Reading T) (i : N.Loc) (w : PlE H) (hw : IsSplitPl H w), TameSplitAll H.E → _root_.GlobalTheory.SplitRead.LawsAlt S → TypeTame S i w hw → (∀ σ ∈ Ine (F := H.E) (N.plOm.1 w), A.inePol (A.locG (A.muC i) w) σ = X - C (iotaO N A i (chi1 N i σ))) → ∀ P : A.AV i, A.mono0 (A.locV i P w) ∧ ∀ σ ∈ Ine (F := H.E) (N.plOm.1 w), A.inePol (A.locV i P w) σ = (X - 1) ^ R.r * (X - C (iotaO N A i (chi1 N i σ))) ^ R.t := by
  intro R H what₂ N A T S i w hw hTS hL hT hmu P
  obtain ⟨htame, hram, hv⟩ := hT
  obtain ⟨v, hv0, hv⟩ := hv P
  have L := hL i w hw
  have hs := (S i w hw).mu_ok.1
  obtain ⟨π₁, π₂, h1, h2, he⟩ := hTS w _ _ _ _ v hs htame hram hv0 hv
  let c : Irr (w.adicCompletion H.E) 1 :=
    { V := ℂ, π := detRep (Fin 1) (S i w hw).mu, smooth := (isSmooth_ofChar_iff _).2 hs.detChar,
      irr := isIrreducible_ofChar _ }
  let τ : Irr (w.adicCompletion H.E) R.t :=
    { V := π₂.V, π := GlobalTheory.SmGL.twist π₂.π (detChar (Fin R.t) (S i w hw).mu), smooth := isSmooth_twist π₂.smooth hs.detChar,
      irr := irreducible_twist π₂.irr _ }
  have hc : Nonempty (c.π.Equiv (detRep (Fin 1) (S i w hw).mu)) := ⟨Representation.Equiv.refl _⟩
  have e1 := L.prod _ _ π₁ τ _ he
  have e2 := _root_.UpperTheory.One.M.RecLawsH.twist L _ _ c π₂ τ (UpperTheory.One.M.goodI_of_sph π₂ h2) hc ⟨Representation.Equiv.refl _⟩
  have u1 := (L.sph _ π₁).2 h1
  have u2 := (L.sph _ π₂).2 h2
  have eV := (S i w hw).locV P
  have eM := (S i w hw).locMu c hc
  rw [e1, e2] at eV
  refine ⟨?_, fun σ hσ => ?_⟩
  · rw [T.mono0, eV, WeilDeligne.WD.monomial_sum_iff, WeilDeligne.WD.monomial_char_iff _ _ (L.dim 1 c)]
    exact ⟨weilDeligneParameter_monodromy_zero_of_unramified u1, weilDeligneParameter_monodromy_zero_of_unramified u2⟩
  · have hz := hmu σ hσ
    rw [T.inePol _ _ _ hσ, eM] at hz
    rw [T.inePol _ _ _ hσ, eV, WeilDeligne.WD.inePol_sum, inePol_of_unr u1 hσ,
      inePol_char_of_unr u2 (L.dim 1 c) hσ hz, L.dim, L.dim]
end GlobalTheory.TameType
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
namespace GlobalTheory.DepthZeroAssembly
open GlobalTheory.WeilDeligne (WD)
open GlobalTheory.SplitRead.BlockParam (twistIrr)
theorem locDZ_of_split_reg_m_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7), _root_.GlobalTheory.PendOf.SplitLocalCondition hL D → _root_.GlobalTheory.PendOf.RegularLocalCondition hL D → _root_.GlobalTheory.PendOf.LocalDatumCondition hL D := by
  intro hL D hS hR k v χ hχ u π ρ f ht hlab hser hsq hnr hx
  obtain ⟨π₁, π₂, hsph, e, y, hy1, hy2⟩ := hS k v χ hχ u π ρ f ht hlab hser hnr hx
  obtain ⟨hm1, hl1⟩ := hR k v π₁ ρ f hser hsq ⟨y, hy1, hy2⟩
  have L : _root_.UpperTheory.One.M.RecLawsH (_root_.GlobalTheory.NPin.weilDeligneOfLocalIrrep hL D (D.naut.plGw k v)) :=
    (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 (D.naut.plGw k v))).recLaws
  have e' : Nonempty (π.π.Equiv (GlobalTheory.SmGL.prod₂ π₁.π (twistIrr π₂ χ hχ).π)) := e
  have e1 := L.prod D.R.r D.R.t π₁ (twistIrr π₂ χ hχ) π e'
  have e2 := _root_.UpperTheory.One.M.RecLawsH.twist L D.R.t χ (Irr.ofDet 1 χ hχ) π₂ (twistIrr π₂ χ hχ) (UpperTheory.One.M.goodI_of_sph π₂ hsph) ⟨.refl _⟩ ⟨.refl _⟩
  have hu := (L.sph _ π₂).2 hsph
  refine ⟨?_, ?_⟩
  · rw [e1, WD.monomial_sum_iff, e2, WD.monomial_char_iff _ _ (L.dim _ _)]
    exact ⟨hm1, WD.unr_mono0 _ hu⟩
  · unfold _root_.GlobalTheory.PendOf.localLabelPolynomial at hl1 hlab ⊢
    rw [e1, WD.lab_lpSum, e2, lab_lpChar_of_unr _ _ _ _ hu (L.dim _ _) u hlab, hl1, L.dim]
end GlobalTheory.DepthZeroAssembly
end
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftOfMovedTwist
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open GlobalTheory.Mem.R3.Tr
namespace GlobalTheory.HeightCounting.Up.LiTw
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000
section Gen
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}
end Gen
variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} {x : St P} {N : TwNew (Dof x)}
def liftOfMovedTwist {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (l : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x) (m : Moved (oTw x N)) (hc : m.Copy) (hh : m.Coh) (r : ReadPk m (sideTw x N))
    (hp : r.Pin) (e : HEq (repOf r.Y) (repOf x.r.Y)) (mt : InMt r.Y (cfOf (stTw x N m hc hh r hp)) w.I.xi (QOf P)) (rat : InRat r.Y m.z.cG) :
    _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL (stTw x N m hc hh r hp) where
  a := (by with_unfolding_all exact (((_root_.UpperTheory.One.M.stageAOfSwitch trivial) N l.a ((by with_unfolding_all exact ((repOf r.Y) :))) ((by with_unfolding_all exact (e :)))) :))
  Pq := (by with_unfolding_all exact (l.Pq :))
  Pq_over := (by with_unfolding_all exact (l.Pq_over :))
  sel := (by with_unfolding_all exact (l.sel :))
  mt := (by with_unfolding_all exact (mt :))
  rat := (by with_unfolding_all exact (rat :))
  cusp := (by with_unfolding_all exact ((cusp N l.cusp) :))
theorem li_copy_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (l : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x) (N : TwNew (Dof x)) (m : Moved (oTw x N)) (hm : m.z = datTw x N) (hc : m.Copy) (hh : m.Coh) (r : ReadPk m (sideTw x N)) (hp : r.Pin), HEq (repOf r.Y) (repOf x.r.Y) → (∀ μ h i y, HEq (r.Y.IL.jMt μ h i y).1 (x.r.Y.IL.jMt μ h i y).1) → (∀ i y, HEq (r.Y.mj.eW i y) (x.r.Y.mj.eW i y)) → ∃ l' : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL (stTw x N m hc hh r hp), HEq l'.a.A.row (N.row l.a.A.row) ∧ HEq l'.Pq l.Pq ∧ HEq l'.rat.S (N.rat l.rat.S) ∧ HEq l'.rat.In.Sb l.rat.In.Sb ∧ HEq l'.rat.In.hL l.rat.In.hL ∧ HEq l'.rat.In.eig l.rat.In.eig ∧ HEq l'.rat.In.θ l.rat.In.θ := by
  intro hL K B f T w P x l N m hm hc hh r hp e H1 H2
  cases m
  dsimp only at hm
  subst hm
  have G1 : ∀ μ h i y, (x.r.Y.IL.jMt μ h i y).1 = jMtB (N := N) ((by with_unfolding_all exact (r.Y :))) μ h i y := fun μ h i y =>
    eq_of_heq ((by with_unfolding_all exact ((HEq.symm (H1 ((μ)) ((h)) ((i)) ((y)))) : _)))
  have G2 : ∀ i y, x.r.Y.mj.eW i y = eWB (N := N) ((by with_unfolding_all exact (r.Y :))) i y := fun i y =>
    eq_of_heq ((by with_unfolding_all exact ((HEq.symm (H2 ((i)) ((y)))) : _)))
  refine Exists.intro (_root_.GlobalTheory.HeightCounting.Up.LiTw.liftOfMovedTwist l _ hc hh r hp e ((by with_unfolding_all exact ((inMt (N := N) ((r.Y)) ((G1)) l.mt) : _))) ((by with_unfolding_all exact ((inRat (N := N) ((r.Y)) ((G2)) l.rat) : _)))) ?_
  exact (by with_unfolding_all exact ((And.intro (HEq.refl (N.row l.a.A.row)) (And.intro (HEq.refl l.Pq) (And.intro (HEq.refl (N.rat l.rat.S))
    (And.intro (HEq.refl l.rat.In.Sb) (And.intro (HEq.refl l.rat.In.hL) (And.intro (HEq.refl l.rat.In.eig) (HEq.refl l.rat.In.θ))))))) :))
end GlobalTheory.HeightCounting.Up.LiTw
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocTypeOfSerParamLe
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace DiscreteGroups.sglob.DzType.Rt
open Polynomial GlobalTheory.GLq GlobalTheory.GLp Formalism.BasicNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders GlobalTheory.SerSys
open scoped Classical
attribute [local instance] GlobalTheory.SerSys.factTypePrime
variable {g : ℕ} [Fact g.Prime]
theorem locType_of_serParamLe_alt {D : D7} {S : ∀ k, Sys (D.host.g k)} {rc : Corr D} (hC : _root_.GlobalTheory.SerSys.LocalCompatibility D rc)
    (hP : ∀ k v, SerParamLe D.R.nV (S k).e (D.ntypes.teichC k) fun n π => D.naut.inePol (rc k v n π) (D.ntypes.tg k v)) :
    LocType D S := by
  intro i P k v
  obtain ⟨μ, χ, hμ, h1, h2⟩ := hC.2 i k v
  obtain ⟨π, hπ, h3, h4⟩ := h2 P
  obtain ⟨f, hf, hm, hd, -⟩ := Loc.exists_charIn (S k) χ 1
  obtain ⟨c, rfl⟩ : ∃ c, f = X - C c := ⟨-f.coeff 0, by rw [C_neg, sub_neg_eq_add]; exact hm.eq_X_add_C hd⟩
  refine ⟨π, χ, c, fun F hF a ha h0 => h4.exists_parVec hF ha h0, Loc.charIn_pow _ χ hf _, ?_,
    fun f' hf' => h3 ▸ hP k v _ le_rfl π hπ f' hf'⟩
  rw [h1, ← Loc.prod_linear]
  exact hP k v 1 (one_le_nV D) _ (Loc.irrSm_det hμ) _ ((Loc.has_det hμ (S k) _).2 hf)
theorem locType_of_labTie_locComp_labParamLe {D : D7} {L : ∀ k, LabelDatum (D.host.g k)} {S : ∀ k, Sys (D.host.g k)} {rc : Corr D}
    (hL : LabTie D L) (hS : ∀ k, (S k).IsOf (L k)) (hC : _root_.GlobalTheory.SerSys.LocalCompatibility D rc) (hP : LabParamLe D.R.nV D L rc) :
    LocType D S :=
  _root_.DiscreteGroups.sglob.DzType.Rt.locType_of_serParamLe_alt hC fun k v => by
    rw [← (hL k).1, show (S k).e = eSerC (L k) from _root_.funext fun n => _root_.funext (hS k n)]
    exact hP k v
end DiscreteGroups.sglob.DzType.Rt
end
end
end

