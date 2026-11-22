import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0013
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0223
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0215
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0249
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0250
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryTrivialOutsideSplitPlaceLocEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0386
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0803
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0214
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0205
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0204
import Development.AbelianVarietyTheory.Counterexamples.DegenerateExamples.NotAdmissibleWithAmbientTop
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PadicIntGLSmulMemPrincipalCongruenceFixed
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0217
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0220
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0216
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0319
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0320
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0377
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RealAt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0031
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EquivFrameBTheta
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0350
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0349
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0363
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0362
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0372
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0348
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0376
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0374
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0026
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0008
import Formalism.LocalToGlobal.GroupLattices.Joint0
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0032
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0292
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0293
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0343
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0299
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0289
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0291
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0551
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianChartComplexRationalIntegralForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0452
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0450
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0158

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalCompatibilityOfClassMaps
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.L2.Host

namespace GlobalTheory.LocCompTy

open GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf

theorem rt_mem_isoTyp {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (a : NG.AlgWt L n)
    (S : Submodule ℂ (GAf L n → a.W)) (h : GAf L n) {f : GAf L n → a.W}
    (hf : f ∈ NG.isoTyp a.ρ S) : NG.rt L n h f ∈ NG.isoTyp a.ρ S := by
  have : NG.isoTyp a.ρ S ≤ (NG.isoTyp a.ρ S).comap (NG.rt L n h) := by
    refine sSup_le fun S' hS' => ?_
    intro y hy
    exact le_sSup hS' (hS'.1.1.stable h y hy)
  exact this hf

set_option maxHeartbeats 1000000 in
theorem blockEig (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D) (i : D.nd.Loc) (PI : D.naut.AV i)
    (k : Fin 2) (v : D.nd.PlG k) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i) (s : SplitPlace D.host.E)
    (hsw : s.w = D.naut.plGw k v) (c : s.v.adicCompletion (maximalRealSubfield D.host.E) ≃+* s.w.adicCompletion D.host.E)
    (hcont : Continuous c) (hci : ∀ x : D.host.E, c (s.i x) = algebraMap D.host.E (s.w.adicCompletion D.host.E) x)
    (F : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) (x : GAf D.host.E D.R.nV) (hx : TrivOutside {s.v} x)
    (hh : Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x) ∈
      GlobalTheory.BlockType.blockGrp (s.w.adicCompletion D.host.E) D.R.r D.R.t) :
    NG.rt D.host.E D.R.nV x ((P.M.loc i).real F) = GlobalTheory.BlockType.blockChar ((P.tp.tup (D.nd.mu i) j).loc s.w)
      (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)) • (P.M.loc i).real F := by
  obtain ⟨ψ₀, ξ, hψ, hξ, hlev⟩ := P.H.level.uni i j hj k v s hsw
  have hcv := GlobalTheory.SplitConjVal.valuation_eq s c hcont hci
  obtain ⟨h1, h2⟩ := GlobalTheory.BlockConj.facts_of_mem s D.R.r D.R.t c hcv (s.loc D.R.nV x) hh
  obtain ⟨i1, -⟩ := GlobalTheory.BlockConj.facts_of_mem s D.R.r D.R.t c hcv (s.loc D.R.nV x)⁻¹
    (by
      have := (GlobalTheory.BlockType.blockGrp _ _ _).inv_mem hh
      convert this using 1
      exact map_inv (Matrix.GeneralLinearGroup.map (n := Fin (D.R.r + D.R.t)) c.toRingHom) _)
  have huni : NG.UniRT s D.R.r (s.loc D.R.nV x) := by
    refine ⟨⟨GlobalTheory.BlockConj.mem_GLint_of (fun a b => ?_) (fun a b => ?_), fun a b ha hb => ?_⟩,
      fun a b ha hb => ⟨fun hlt => ?_, fun he => ?_⟩⟩
    · exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (h1 a b)
    · exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (i1 a b)
    · have := h2 a b hb
      split_ifs at this with e
      · rw [e] at ha; omega
      · rwa [sub_zero] at this
    · have := h2 a b hb
      split_ifs at this with e
      · rw [e] at hlt; omega
      · rwa [sub_zero] at this
    · subst he
      have := h2 a a ha
      split_ifs at this with e
      · exact this
      · exact absurd rfl e
  have hxJ : x ∈ (P.M.loc i).J := (hlev.mem x hx).2 huni
  have hTS : (P.M.loc i).real F ∈ NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ := by
    rw [← (P.M.loc i).real_range]; exact LinearMap.mem_range_self _ _
  have hrt := hTS.2 ⟨x, hxJ⟩
  let h : GL (Fin (D.R.r + D.R.t)) (s.w.adicCompletion D.host.E) :=
    Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)
  have hh' : h ∈ GlobalTheory.BlockType.blockGrp (s.w.adicCompletion D.host.E) D.R.r D.R.t := hh
  have hdet := GlobalTheory.BlockConjDet.val_det_mul_sub_one_lt hh'
  have hne2 : (h.val.submatrix (Fin.natAdd D.R.r) (Fin.natAdd D.R.r)).det ≠ 0 := by
    intro h0
    rw [h0, mul_zero, zero_sub, Valuation.map_neg, map_one] at hdet
    exact lt_irrefl _ hdet
  have hc_det : c (NG.detDD s D.R.r (s.loc D.R.nV x)) =
      (h.val.submatrix (Fin.natAdd D.R.r) (Fin.natAdd D.R.r)).det := by
    let e : Fin D.R.t ≃ {y : Fin D.R.nV // D.R.r ≤ y.val} :=
      { toFun := fun a => ⟨Fin.natAdd D.R.r a, by simp⟩
        invFun := fun y => ⟨y.1.val - D.R.r, by
          have h1 := y.1.2; have h2 := y.2; change y.1.val < D.R.r + D.R.t at h1; omega⟩
        left_inv := fun a => by ext; simp
        right_inv := fun y => by ext; simp; have := y.2; omega }
    rw [NG.detDD, ← Matrix.det_submatrix_equiv_self e]
    rw [show c _ = c.toRingHom _ from rfl, RingHom.map_det]
    congr 1
  have hF0 : NG.detDD s D.R.r (s.loc D.R.nV x) ≠ 0 := fun h0 => hne2 (by rw [← hc_det, h0, map_zero])
  let u := Units.mk0 _ hF0
  have hchr := hlev.chr x hxJ hx u rfl
  have hsup : ψ₀ (NG.supDiag s D.R.r (s.loc D.R.nV x)) = 1 := hψ.1 _ (by
    unfold NG.supDiag
    refine Valuation.map_sum_lt _ one_ne_zero fun p _ => Valuation.map_sum_lt _ one_ne_zero fun q _ => ?_
    split_ifs with h
    · have := h2 p q h.2
      split_ifs at this with e
      · rw [e] at h; omega
      · rwa [sub_zero] at this
    · rw [map_zero]; exact zero_lt_one)
  have hμ : GlobalTheory.NPin.IsComp (P.tp.tup (D.nd.mu i) j) s.w ((P.tp.tup (D.nd.mu i) j).loc s.w) :=
    ⟨GlobalTheory.HeckeComp.smooth_loc _ _, fun _ => rfl⟩
  have hξμ := GlobalTheory.ConjDense.eq_of_agree s c hcont hci ((P.tp.tup (D.nd.mu i) j).loc s.w) ξ hμ.1 hξ.1
    (fun k => by rw [hξ.2 k, hμ.2 k]) u
  have hbc : GlobalTheory.BlockType.blockChar ((P.tp.tup (D.nd.mu i) j).loc s.w) h =
      ((((P.tp.tup (D.nd.mu i) j).loc s.w) (Units.map c.toMonoidHom u) : ℂˣ) : ℂ) :=
    GlobalTheory.BlockType.blockChar_eq _ _ _ (by rw [← hc_det]; rfl)
  change _ = GlobalTheory.BlockType.blockChar ((P.tp.tup (D.nd.mu i) j).loc s.w) h • _
  rw [hbc, ← hξμ, hrt, hchr, hsup, one_mul]

set_option maxHeartbeats 2000000 in
theorem compAt (hPr : GlobalTheory.NRows.Hypotheses₂) (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D)
    (hCen : GlobalTheory.HeightCounting.Up.CenLoc D P.M) (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) (w : PlE D.host)
    (hw : w = D.naut.plGw k v) (e : ℚ_[D.host.g k] ≃+* w.adicCompletion D.host.E) (he : Continuous e)
    (rcw : ∀ n, QRep (D.host.g k) n → D.naut.LP w)
    (hrc : ∀ n (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (w.adicCompletion D.host.E))) (π : QRep (D.host.g k) n),
      Nonempty (π ≅ Rep.of (σ.ρ.comp (Matrix.GeneralLinearGroup.map e.toRingHom))) →
      P.T.e w (rcw n π) = GlobalTheory.CuspRep.ParLaws.locRec hL (D.nd.plOm.2 w) (GlobalTheory.LocLanglands.cls σ)) :
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
  refine ⟨_, χ, hχ, GlobalTheory.T.local_langlands_split_qp hPr hL D P i j0 hj0 k s.w e rcw hrc, fun Q => ?_⟩
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
    rw [blockEig hL D P i Q k v j0 hj0 s hw c hc hci F x hx hh2, map_smul] at h3
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
    GlobalTheory.T.lift_through_completion_iso hL D P i Q k v s hw c hc hci L hLift F F.2 h (g h) (by simp [g])
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

theorem main : GlobalTheory.NRows.Hypotheses₂ → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : GlobalTheory.NPin.Pin hL D) (I : Ident D) (rc : GlobalTheory.SerSys.Corr D), IsRc hL P.T I rc → (∀ k v, IsClassMap D.naut.lpDim (rc k v)) → GlobalTheory.HeightCounting.Up.CenLoc D P.M → LocComp D rc := by
  intro hPr hL D P I rc hRc hCM hCen
  exact ⟨hCM, fun i k v => compAt hPr hL D P hCen i k v _ rfl (I.i k v) (I.cont k v) (rc k v)
    fun n σ π h => hRc k v n σ π h⟩

end GlobalTheory.LocCompTy
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepDeterminantConstantUnitIndependentStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stepDeterminantConstant_unit_independent : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → ∀ j (hj : j + 1 ≤ D.R.m) (a : Lv.comp j) (a' : Lv.comp (j + 1)), ‖cKs S ι j hj a a'‖ = 1 ∧ ι (kS J j (Nat.le_of_succ_le hj) a * cOp (sysS H X std) D (hT.gat_pos u w hg) j (t.O u μ).dgen) ≠ 0 ∧ ∀ b b', cKs S ι j hj b b' = cKs S ι j hj a a') := by
  first | exact @GlobalTheory.TwV.DelA.cKs_unit_indep | exact GlobalTheory.TwV.DelA.cKs_unit_indep | (intros; apply GlobalTheory.TwV.DelA.cKs_unit_indep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TargetFrameMapEqComplexBlockActionScalar
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.TwV.DelA.targetFrameMap_eq_complexBlockAction_scalar_alt : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra (Formalism.MainNotions.FormalGroupSystem.K0 p) Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v), PosTie X D pos Kc ι ρ → ∀ (fd : FData X D) (c : Kc), c ≠ 0 → ∀ (j : ℕ) (hN : RankTie X D j) (La' : X.Lt (j + 1)) (M : GL (Fin (D.R.N (j + 1))) D.host.E), StdU D M → FrIs fd ρ (j + 1) La' (rkT X D hN) M → ∀ (ν : D.what₂.Tau → Fin (D.R.N j) → ℕ), NuIs X D pos j ν → ∀ P : MvPolynomial (GL3Theta.FrV D (D.R.N (j + 1))) ℂ, P ∈ WtPol ℂ (extNu (D.R.N (j + 1)) ν) → GlobalTheory.FrameB.tauV Kc fd c j La' (phi0 X D pos ι j P) = (c ^ (∑ τ, szT X D pos j τ) * ι (∏ τ, embT D τ M.1.det ^ wT X D pos j τ)) • MvPolynomial.map ι (actC X D pos (j + 1) (rkT X D hN) M⁻¹ (phiC X D pos (j + 1) (rkT X D hN) (wT X D pos j) P)) := by
  intro p _ X D pos Kc _ _ _ ι ρ hPT fd c hc j hN La' M hU hFr ν hν P hP
  obtain ⟨-, -, hsz', hle, -⟩ := GlobalTheory.T.modelPartition_size_extension_firstLast_rows X D pos j hN ν hν
  obtain ⟨R0, hR0⟩ := GlobalTheory.T.frame_polynomials_weight_realised_next_level X D pos j (rkT X D hN) (extNu (D.R.N (j + 1)) ν) hle P hP
  have hRR : phiC X D pos (j + 1) (rkT X D hN) (wT X D pos j) P = R0 := GlobalTheory.T.linearChoice_eq_realisingPolynomial X D pos (j + 1) (rkT X D hN) _ P R0 hR0
  have hdeg := GlobalTheory.T.realising_polynomial_blockwise_homogeneous X D pos (j + 1) (rkT X D hN) (wT X D pos j) (extNu _ ν) P R0 hP hR0
  have hphi : phi0 X D pos ι j P = MvPolynomial.map ι R0 := by
    unfold phi0
    rw [dif_pos (rkT X D hN)]
    show MvPolynomial.map ι (phiC X D pos (j + 1) (rkT X D hN) (wT X D pos j) P) = _
    rw [hRR]
  have hhom : ∀ m ∈ (MvPolynomial.map ι R0).support, ∀ τ, ¬ IsOddPos (pos.symm τ).2 →
      (∑ x : Var (X.Pj (j + 1)), if (⟨x.1, x.2.1⟩ : Σ v : Fin (X.Pj (j + 1)).nV, Fin ((X.Pj (j + 1)).n' v)) =
        (posJ X D pos (j + 1)).symm τ then (m x : ℤ) else 0) = szT X D pos j τ := by
    intro m hm τ ho
    rw [hdeg m (MvPolynomial.support_map_subset _ _ hm) τ, if_neg ho, (GlobalTheory.T.realPlaceBlockWeightLastEntry_consecutive_levels X D pos j τ).2, if_neg ho, ← hsz' τ]
    ring
  rw [hphi, hRR]
  unfold GlobalTheory.FrameB.tauV
  rw [LinearMap.smul_apply, AlgHom.toLinearMap_apply, GlobalTheory.T.evenFrameBlock_scaling_homogeneous_polynomial_alt X D pos Kc fd c j La' (fun τ => szT X D pos j τ) _ hhom,
    GlobalTheory.T.latticeTupleFrame_scalar_oddPositions_det X D pos Kc ι ρ hPT fd c hc j hN La' M hU hFr ν hν, GlobalTheory.T.complex_block_action_inv_read_as_substitution X D pos Kc ι ρ hPT fd j hN La' M hU hFr R0, smul_smul, smul_smul]
  congr 1
  have hε : ∀ τ, ι (embT D τ (M : Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) D.host.E).det) ≠ 0 := fun τ =>
    (((Matrix.isUnit_iff_isUnit_det _).1 M.isUnit).map ((ι.comp (embT D τ)))).ne_zero
  have hsum : c ^ (∑ τ, szT X D pos j τ) = ∏ τ, c ^ szT X D pos j τ := by
    classical
    induction (Finset.univ : Finset D.what₂.Tau) using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, zpow_add₀ hc, ih]
  rw [hsum, mul_assoc, ← map_mul, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_mul, map_zpow₀, map_zpow₀]
  split_ifs with ho
  · rw [mul_one, ← zpow_add₀ (hε τ)]
    ring_nf
  · rw [one_mul, ← zpow_add₀ (hε τ)]
    simp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueColumnExistsChainChartsKernelDataForms
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 4000000 in

theorem GlobalTheory.Port.jIn_nonempty_true : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex) (C : ColsTiedSym (I.rec7 l Z)) (full : ColsFullS C) (g : Formalism.L2.G.GroupCompatibilityAll (I.rec7 l Z) hT ex.cmp), I.IsTw → ColIn.JetsIn I → ex.tw = I.tw l l0 Z → ex.errX.piT = X.piT → I.StdKer l Z t → GlobalTheory.Pdv.StdRd I l Z t → (∀ (u : B.Word) (a : I.ι) (i : ℕ) (c : ((I.rec7 l Z).chTw u a).cls i), (t.rd u a).pin i c ↔ (i + 1 ≤ B.R.m ∨ ∃ d, OverRow (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u d ((I.stp u a i).rep c).1.1)) → I.StdC l Z C → I.StdDt l Z full.1.base.dt → g.herm = full.1.to0 → (g.forms = fun u => (C.forms u).to0) → (∀ z : (I.rec7 l Z).Dt, ∃ r : (I.rec7 l Z).what₂.LL, (I.rec7 l Z).what₂.embLL r = (((I.rec7 l Z).chiD z : ℂˣ) : ℂ)) → ∀ (u : B.Word) (a : I.ι), Nonempty (GlobalTheory.Port.JIn t u a) := by
  intro B X I hI hP l Z l0 L hT Gi Gl K Y cX ex t C full g hTw hJets hex hpi hSK hRd hpin hSC hDt hherm hforms hchiD u a
  classical
  let Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) := (I.Q a).image (fun P => P.under (𝓞 B.host.F))
  have hQ : ∀ v, v ∈ Q ↔ I.UnderQ a v := by
    intro v
    exact Finset.mem_image
  obtain ⟨Ch, chOf, eY, Kc, hK, hCh0, hlev0, hy0⟩ := GlobalTheory.T.trueColumnChoice_goodCharts_every_stage I hI hP l Z u (C.forms u) a Q hQ (hSC u)
  have hbad : ∀ v ∈ badQ (I.rec7 l Z) Q, v ∈ badG (I.rec7 l Z) ∨ I.UnderQ a v := by
    intro v hv
    rcases hv with hv | hv
    · exact Or.inl hv
    · exact Or.inr ((hQ v).1 hv)
  obtain ⟨A, hpins, htie⟩ := GlobalTheory.T.trueColumn_kernelData_compatible_stepCharts I hI hP l Z L hT Gi Gl K Y cX ex t u a (badQ (I.rec7 l Z) Q) Ch chOf eY Kc
    full.1.base.dt hTw hSK hRd hpin hpi hDt hbad
    (fun i hi => ⟨(hK i hi).2.2.1.readsK, (hK i hi).2.1⟩) (fun i hi β => ((hK i hi).2.2.2 β).1)
    (fun i hi β => by
      obtain ⟨n, hn, h⟩ := ((hK i hi).2.2.2 β).2
      exact ⟨n, hn, fun κ _ => h κ⟩) (fun _ i hi c y hy => by
    obtain ⟨k, hR, hk1⟩ := (hK i hi).2.2.1
    obtain ⟨p, hp, hN⟩ := hR.k_std (chOf i hi c)
    have e := GlobalTheory.Mem.Col2.FullDt.detPt_eq_u1Dt_of_level B.R B.host _ _ _ _ I.SQ _ _ (k (chOf i hi c)) y
      (GlobalTheory.Mem.LevTwist.levOk_twists B X I hI).1 (hR.pt c) hp.uni (hN ▸ hp.lat)
      (fun P hP => hk1 _ _ (GlobalTheory.Mem.LevTwist.T_notMem_under_uSG B X I hI u P hP)) hy
    obtain ⟨b, hb⟩ := GlobalTheory.Mem.Col2.FullDt.exists_lift B.host y
    rw [e, GlobalTheory.Mem.Col2.FullDt.normOneFiniteAdeleDetClass_of_isDetLift B.host I.SQ y b hb, hDt y b hb])
  have hf : g.forms u = (C.forms u).to0 := congrFun hforms u
  refine ⟨{
      Gd := g
      Hh := full.1.base
      rel := full.1.relDet
      St := charts I l Z u a (badQ (I.rec7 l Z) Q) Ch chOf eY Kc
      A := A
      a := B.fields.conjO (X.piT u)
      pins := hpins
      tie := htie
      val := ?val
      fin := fun i hi => (hK i hi).1
      ord := fun i hi β => ((hK i hi).2.2.2 β).2
      base := ?base
      joint0 := GlobalTheory.hServTwoSidesJoint0 hT ex.cmp g C full hherm hforms u
      e0 := I.eCls0 l u a
      jointCmpEmbeddingY := Equiv.refl _
      e0Tw := ?e0Tw
      lev0 := ?lev0
      ch0 := hCh0
      y0 := ?y0
      fr0 := ?fr0
      rat := fun j hj => GlobalTheory.T.trueColumnTupleKernels_rational I hI hP l Z l0 ex.tw hJets hex u a j hj
      kin := GlobalTheory.T.kernelCoefficientField_le_coefficientField I hI hP l Z L hT Gi Gl K Y cX ex t hSK
      chiD := hchiD }⟩
  case val =>
    intro i hi
    rw [hex]
    exact GlobalTheory.Mem.Col2.TC.val_tied I hI hP l Z u a i hi _ (Ch i hi) (chOf i hi) (Kc i hi) (eY i hi)
      (hK i hi).2.2.1.readsK (hK i hi).2.1
  case base =>
    intro i hi β
    obtain ⟨k, hR, _⟩ := (hK i hi).2.2.1
    rw [GlobalTheory.T.trueColumn_orthonormalCoords_eq_given I hI hP l Z L hT Gi Gl K Y cX ex t u a _ Ch chOf eY Kc full.1.base.dt A hSK (fun i hi => (hK i hi).2.1) hpins i hi]
    exact GlobalTheory.T.companionLattice_trueColumn_baseLattice_eq_standard I hI hP l Z u i hi _ (fun x => hR.lb β x)
  case e0Tw =>
    intro φ c y
    change φ ((I.eCls0 l u a).symm (I.eCls0 l u a c)) y = φ c y
    exact congrFun (congrArg φ ((I.eCls0 l u a).symm_apply_apply c)) y
  case lev0 =>
    rw [hf]
    exact hlev0
  case y0 =>
    rw [hf]
    intro c
    obtain ⟨κ, h1, h2, h3⟩ := hy0 c
    refine ⟨κ, h1, h2, fun v hv => h3 v fun hvQ => ?_⟩
    obtain ⟨q, hq, hqv⟩ := GlobalTheory.T.placeUnderTwistPrime_over_tupleRamifiedPrime I hI hP l Z L hT Gi Gl K Y cX ex t hSK a v ((hQ v).1 hvQ)
    exact hv q hq hqv
  case fr0 =>
    rw [hf]
    intro y
    apply Subtype.ext
    exact ((hK 0 (Nat.zero_le _)).2.1 y).trans ((hSC u).eY 0 (Nat.zero_le _) (Or.inl rfl) y).symm
end

