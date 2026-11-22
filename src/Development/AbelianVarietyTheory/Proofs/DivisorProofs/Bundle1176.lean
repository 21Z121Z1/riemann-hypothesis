import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0042
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0050
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0028
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.TangentEqLcZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0248
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1137
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsBasisKaehlerOfAlgebraicIndependent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaTildeHeckeCharSplitMulSignOfNormFormula
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1104
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0229
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupportPushforwardSubschemeSubset
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0317
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1140
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetFactorDepthInChartChartIndependent
section
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.FactorDepth

section Series
open MvPowerSeries ReciprocityTheory.PGsh GlobalTheory.FGDepth

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)}

theorem exp_eq_of_log_hom {d : ℕ} (G G' : LogFGL v d) (Φ : Fin d → MvPowerSeries (Fin d) C)
    (h0 : ∀ e, constantCoeff (Φ e) = 0) (M : Matrix (Fin d) (Fin d) C)
    (hl : ∀ e, subst Φ (G.lg e) = ∑ f, M e f • G'.lg f) {τ : Type} (w w' : Fin d → MvPowerSeries τ C)
    (hw' : ∀ e, constantCoeff (w' e) = 0) (hw : ∀ e, w e = ∑ f, M e f • w' f) (e : Fin d) :
    subst w (expOf G e) = subst (fun f => subst w' (expOf G' f)) (Φ e) := by
  have s1 : HasSubst w' := hasSubst_of_constantCoeff_zero hw'
  have c2 : ∀ f, constantCoeff (subst w' (expOf G' f) : MvPowerSeries τ C) = 0 := fun f =>
    constantCoeff_subst_eq_zero s1 hw' ((isExp_expOf G').1 f)
  have s2 := hasSubst_of_constantCoeff_zero c2
  have s3 : HasSubst (fun e => (subst (fun f => (subst w' (expOf G' f) : MvPowerSeries τ C)) (Φ e) :
      MvPowerSeries τ C)) :=
    hasSubst_of_constantCoeff_zero fun e => constantCoeff_subst_eq_zero s2 c2 (h0 e)
  have key : (fun j => subst (fun e => (subst (fun f => (subst w' (expOf G' f) : MvPowerSeries τ C)) (Φ e) :
      MvPowerSeries τ C)) (G.lg j)) = w := by
    funext j
    rw [← subst_comp_subst_apply (hasSubst_of_constantCoeff_zero h0) s2, hl, hw, ← coe_substAlgHom s2, map_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [map_smul, coe_substAlgHom,
      ← subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (isExp_expOf G').1) s1, (isExp_expOf G').2,
      subst_X s1]
  have := subst_comp_subst_apply (hasSubst_of_constantCoeff_zero G.lg_const) s3 (expOf G e)
  rw [subst_lg_expOf, subst_X s3, key] at this
  exact this.symm

theorem depth_le_of_log_hom {κ : Type} [Finite κ] {d : κ → ℕ} (G G' : ∀ b, LogFGL v (d b)) {ι : κ → Type}
    [∀ b, Fintype (ι b)] (u u' : ∀ b, ι b → Fin (d b) → C) (Φ : ∀ b, Fin (d b) → MvPowerSeries (Fin (d b)) C)
    (h0 : ∀ b e, constantCoeff (Φ b e) = 0) (hI : ∀ b e, MvIsInt v (Φ b e))
    (M : ∀ b, Matrix (Fin (d b)) (Fin (d b)) C)
    (hl : ∀ b e, subst (Φ b) ((G b).lg e) = ∑ f, M b e f • (G' b).lg f)
    (hu : ∀ b a, u b a = (M b).mulVec (u' b a)) (P : MvPolynomial (Σ b, ι b) C) :
    depth G' u' P ≤ depth G u P := by
  classical
  have cX : ∀ b (e : Fin (d b)), constantCoeff (X ⟨b, e⟩ : MvPowerSeries (Σ b, Fin (d b)) C) = 0 := fun b e => by simp
  let Ψ : (Σ b, Fin (d b)) → MvPowerSeries (Σ b, Fin (d b)) C :=
    fun x => subst (fun e : Fin (d x.1) => (X ⟨x.1, e⟩ : MvPowerSeries (Σ b, Fin (d b)) C)) (Φ x.1 x.2)
  have cΨ : ∀ x, constantCoeff (Ψ x) = 0 := fun x =>
    constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero (cX x.1)) (cX x.1) (h0 x.1 x.2)
  have iΨ : ∀ x, MvIsInt v (Ψ x) := fun x =>
    ReciprocityTheory.ChartRestriction.G.Sh.PTb.mvIsInt_subst v (hI x.1 x.2)
      (fun e α => by rw [coeff_X]; split_ifs <;> simp [IsIntV]) (cX x.1)
  have cw : ∀ b (e : Fin (d b)),
      constantCoeff (∑ a, u' b a e • (X ⟨b, a⟩ : MvPowerSeries (Σ b, ι b) C)) = 0 := fun b e => by simp
  have cE : ∀ x, constantCoeff (expAlong G' u' x) = 0 := fun x =>
    constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero (cw x.1)) (cw x.1) ((isExp_expOf _).1 _)
  have sE := hasSubst_of_constantCoeff_zero cE
  have key : expAlong G u = fun x => subst (expAlong G' u') (Ψ x) := by
    funext x
    rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (cX x.1)) sE]
    simp only [subst_X sE]
    refine exp_eq_of_log_hom (G x.1) (G' x.1) (Φ x.1) (h0 x.1) (M x.1) (hl x.1) _ _ (cw x.1) (fun e => ?_) x.2
    simp only [hu, Matrix.mulVec, dotProduct, Finset.sum_smul, Finset.smul_sum, smul_smul]
    exact Finset.sum_comm
  refine le_iInf fun f => iInf_le_of_le
    ⟨subst Ψ f.1, ReciprocityTheory.ChartRestriction.G.Sh.PTb.mvIsInt_subst v f.2 iΨ cΨ⟩ (le_of_eq ?_)
  rw [key, subst_comp_subst_apply (hasSubst_of_constantCoeff_zero cΨ) sE]

end Series

section Law
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open GlobalTheory.GermDerivativeLinearMaps GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.LawLog

variable {C : Type} [Field C] [CharZero C] {d : ℕ}

theorem logOf_spec (G : FGLaw C d) : GP (GlobalTheory.FormalLog.logOf G) ∧ dLin (GlobalTheory.FormalLog.logOf G) = 1 ∧
    comp1 (GlobalTheory.FormalLog.logOf G) (addOf G.F (pt C (n := 2) d 0) (pt C (n := 2) d 1)) =
      comp1 (GlobalTheory.FormalLog.logOf G) (pt C (n := 2) d 0) + comp1 (GlobalTheory.FormalLog.logOf G) (pt C (n := 2) d 1) := by
  refine ⟨fun i => GlobalTheory.FormalLog.constantCoeff_prim _, ?_, ?_⟩
  · refine Matrix.ext fun i j => ?_
    show coeff (Finsupp.single ((0 : Fin 1), j) 1) (GlobalTheory.FormalLog.logOf G i) = (1 : Matrix (Fin d) (Fin d) C) i j
    have h := congrArg constantCoeff (GlobalTheory.FormalLog.pderiv_logOf G i j)
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv, zero_add] at h
    have h2 := congrFun (congrFun (GlobalTheory.FormalLog.cc_om G) i) j
    simp only [Matrix.map_apply] at h2
    simpa [h2] using h
  · have e : addOf G.F (pt C (n := 2) d 0) (pt C (n := 2) d 1) = G.F := add_pt G
    rw [e]
    funext i
    exact GlobalTheory.FormalLog.logOf_add G i

theorem logOf_comp_hom (G G' : FGLaw C d) (φ : Pt C 1 d) (hφ : GP φ)
    (hhom : comp1 φ G'.F = addOf G.F (comp1 φ (pt C (n := 2) d 0)) (comp1 φ (pt C (n := 2) d 1))) :
    comp1 (GlobalTheory.FormalLog.logOf G) φ = fun i => ∑ j : Fin d, dLin φ i j • GlobalTheory.FormalLog.logOf G' j := by
  obtain ⟨a0, a1, a2⟩ := logOf_spec G
  obtain ⟨b0, b1, b2⟩ := logOf_spec G'
  obtain ⟨ε, hi⟩ := ChartInv.exists_isInvPair C d _ b0 (by rw [b1, Matrix.det_one]; exact isUnit_one)
  have p0 : GP (pt C (n := 2) d 0) := gp_pt 0
  have p1 : GP (pt C (n := 2) d 1) := gp_pt 1
  have e : addOf G'.F (pt C (n := 2) d 0) (pt C (n := 2) d 1) = G'.F := add_pt G'
  have e1 := additive_eq_lin _ G'.const _ ε (comp1 (GlobalTheory.FormalLog.logOf G) φ) b1 b2 hi
    (gp_comp1 _ _ a0 hφ) (by
    rw [e, gt_comp1_comp1 _ _ hφ _ G'.const, hhom,
      additive_at _ G.const _ a2 _ _ (gp_comp1 _ _ hφ p0) (gp_comp1 _ _ hφ p1),
      gt_comp1_comp1 _ _ hφ _ p0, gt_comp1_comp1 _ _ hφ _ p1])
  rw [dLin_comp _ _ hφ, a1, one_mul] at e1
  rw [e1]
  funext i
  rw [germComp_matrixLinearMap_apply _ _ b0]
  simp only [MvPowerSeries.smul_eq_C_mul]

open ReciprocityTheory.PGsh GlobalTheory.FGDepth in

theorem detDepth_le_of_transF {R : Type} [CommRing R] (v : AddValuation C (WithTop ℝ)) (j : R →+* C)
    (hj : ∀ r, IsIntV v (j r)) (F F' : Fin d → PS R 2 d) (hF : ∀ a, constantCoeff (F a) = 0)
    (φ φi : Pt R 1 d) (hi : IsInvPair φ φi)
    (ht : ∀ a, F' a = transF F φ φi a) (L L' : FGLaw C d) (hL : ∀ a, L.F a = MvPowerSeries.map j (F a))
    (hL' : ∀ a, L'.F a = MvPowerSeries.map j (F' a))
    (hI : ∀ a, MvIsInt v (subst (twoVars C d) (L.F a))) (hI' : ∀ a, MvIsInt v (subst (twoVars C d) (L'.F a)))
    {i : ℕ} (u u' : Fin i → Fin d → R) (hu : ∀ a, u a = (dLin φ).mulVec (u' a)) (k : ℕ) :
    detDepth (logFGLOf v L' hI') (fun a e => j (u' a e)) k ≤ detDepth (logFGLOf v L hI) (fun a e => j (u a e)) k := by
  have hφ : GP φ := hi.1
  have p0 : GP (pt R (n := 2) d 0) := gp_pt 0
  have p1 : GP (pt R (n := 2) d 1) := gp_pt 1
  have q := gp_addOf F hF _ _ (gp_comp1 _ _ hφ p0) (gp_comp1 _ _ hφ p1)
  have e0 : F' = comp1 φi (addOf F (comp1 φ (pt R (n := 2) d 0)) (comp1 φ (pt R (n := 2) d 1))) := funext ht
  have hF' : GP F' := e0 ▸ gp_comp1 _ _ hi.2.1 q
  have e1 : comp1 φ F' = addOf F (comp1 φ (pt R (n := 2) d 0)) (comp1 φ (pt R (n := 2) d 1)) := by
    rw [e0, gt_comp_inv hi _ q]
  have e2 := congrArg (GlobalTheory.FBMap.mapPt j) e1
  rw [GlobalTheory.FBMap.mapPt_comp1 j _ hF', GlobalTheory.FBMap.mapPt_addOf j _ (gp_comp1 _ _ hφ p0) (gp_comp1 _ _ hφ p1),
    GlobalTheory.FBMap.mapPt_comp1 j _ p0, GlobalTheory.FBMap.mapPt_comp1 j _ p1, GlobalTheory.FBMap.mapPt_pt, GlobalTheory.FBMap.mapPt_pt,
    show GlobalTheory.FBMap.mapPt j F = L.F from (funext hL).symm, show GlobalTheory.FBMap.mapPt j F' = L'.F from (funext hL').symm] at e2
  have hψ : GP (GlobalTheory.FBMap.mapPt j φ) := fun a => by simp [GlobalTheory.FBMap.mapPt, hφ a]
  have e3 := logOf_comp_hom L L' _ hψ e2
  refine depth_le_of_log_hom _ _ _ _ (fun _ a => subst (oneVar C d) (GlobalTheory.FBMap.mapPt j φ a))
    (fun _ a => constantCoeff_subst_eq_zero hs_oneVar cc_oneVar (hψ a)) (fun _ a α => ?_)
    (fun _ => dLin (GlobalTheory.FBMap.mapPt j φ)) (fun _ a => ?_) (fun _ a => ?_) _
  · have e : subst (oneVar C d) (GlobalTheory.FBMap.mapPt j φ a) = MvPowerSeries.map j (subst (oneVar R d) (φ a)) := by
      rw [MvPowerSeries.map_subst hs_oneVar]
      congr 1
      funext q
      simp [oneVar]
    rw [e, coeff_map]
    exact hj _
  · show subst _ (subst (oneVar C d) (GlobalTheory.FormalLog.logOf L a)) =
      ∑ f, _ • subst (oneVar C d) (GlobalTheory.FormalLog.logOf L' f)
    rw [subst_oneVar _ cc_oneVar _ hψ]
    refine (congrArg (subst (oneVar C d)) (congrFun e3 a)).trans ?_
    rw [← coe_substAlgHom hs_oneVar, map_sum]
    simp only [map_smul]
  · funext e
    rw [hu, RingHom.map_mulVec]
    rfl

end Law

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp GlobalTheory.CharDepth ReciprocityTheory.PGsh GlobalTheory.FGDepth GlobalTheory.LawLog

theorem detDepth_le_of_charts {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    [StarRing (𝓞 E)] (hs : ∀ a : 𝓞 E, star a = H.bar a)
    (V : Type) [CommRing V] [IsLocalRing V] (t t' : SAB H (Sp V)) (n : SABMap t t' (𝟙 (Sp V)))
    (hsurj : Function.Surjective (t'.G ⊗ t'.G).hom.appTop.hom) (d d' : ℕ)
    (B : FB V d (𝓞 E)) (B' : FB V d' (𝓞 E))
    (tg : Fin d → (Sp (DualNumber V) ⟶ t.G.left)) (tg' : Fin d' → (Sp (DualNumber V) ⟶ t'.G.left))
    (uv : Fin d → Fin d → V) (uv' : Fin d' → Fin d' → V)
    (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp V)) d' m 1 ⟶ t'.G)
    (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m) (e' : ∀ m, FrTyG t' (𝟙 (Sp V)) d' x' m)
    (hc : IsChartG t (𝟙 (Sp V)) d B.G.F B.A.act tg uv x)
    (hc' : IsChartG t' (𝟙 (Sp V)) d' B'.G.F B'.A.act tg' uv' x')
    (hu : GlobalTheory.PowGerm.IsUnivJ t.G (Fin 1 × Fin d) x) (hu' : GlobalTheory.PowGerm.IsUnivJ t'.G (Fin 1 × Fin d') x')
    (hf : IsFrameG t (𝟙 (Sp V)) d x B.G.F B.A.act B.ph1 B.ph2 B.sy B.ad e)
    (hf' : IsFrameG t' (𝟙 (Sp V)) d' x' B'.G.F B'.A.act B'.ph1 B'.ph2 B'.sy B'.ad e')
    {i : ℕ} (u : Fin i → Fin d → V) (u' : Fin i → Fin d' → V)
    (w : Fin i → (Sp (DualNumber V) ⟶ t.G.left))
    (hw : ∀ ℓ, IsCombAtG t (𝟙 (Sp V)) (dirs x) (u ℓ) (w ℓ))
    (hw' : ∀ ℓ, IsCombAtG t' (𝟙 (Sp V)) (dirs x') (u' ℓ) (w ℓ ≫ n.φ))
    {C : Type} [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (j : V →+* C) (hj : ∀ r, IsIntV v (j r))
    (L : FGLaw C d) (L' : FGLaw C d') (hL : ∀ a, L.F a = MvPowerSeries.map j (B.G.F a))
    (hL' : ∀ a, L'.F a = MvPowerSeries.map j (B'.G.F a))
    (hI : ∀ a, MvIsInt v (MvPowerSeries.subst (twoVars C d) (L.F a)))
    (hI' : ∀ a, MvIsInt v (MvPowerSeries.subst (twoVars C d') (L'.F a))) (k : ℕ) :
    detDepth (logFGLOf v L' hI') (fun a e => j (u' a e)) k ≤ detDepth (logFGLOf v L hI) (fun a e => j (u a e)) k := by
  have hd : d = d' := by
    obtain ⟨x'', -, h2, -⟩ := GlobalTheory.T.pushChartAlt E H V t t' n d x
    exact GlobalTheory.T.universalJetCoordinates_dim_unique V t'.G d d' x'' x' (h2 hu) hu'
  subst hd
  obtain ⟨φ, φi, hJ, hdir⟩ := GlobalTheory.T.formal_biextensions_related_of_triple_map_over_id E H hs V t t' n hsurj d B B' (Fin d) (Fin d) tg tg' uv uv' x x' e e'
    hc hc' hu hu' hf hf'
  obtain ⟨ε, hε⟩ := hJ 0
  exact detDepth_le_of_transF v j hj _ _ B.G.const φ φi hε.inv hε.law L L' hL hL' hI hI' u u'
    (fun a => hdir _ _ _ (hw a) (hw' a)) k

theorem nuFacC_le {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) :
    letI := H.starRing
    ∀ (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io)
      (C C' : IntegralChartA3 Xo c T io y) (X : ValExt T p) (f : Lt1 Dw) (k : ℕ), nuFacC C' X f k ≤ nuFacC C X f k := by
  letI := H.starRing
  intro p _ T io y C C' X f k
  letI := io.toAlgebra
  obtain ⟨n, hn⟩ := GlobalTheory.T.exists_iso_integralModels_matching_lieBases E H Dw l Xo c T io y.1 C.I C'.I
  obtain ⟨B, b1, b2, b3, b4, b5, b6, -⟩ := GlobalTheory.integralChart_formalBiext E H Dw l Xo c T io y C
  obtain ⟨B', b1', b2', b3', b4', b5', b6', -⟩ := GlobalTheory.integralChart_formalBiext E H Dw l Xo c T io y C'
  refine detDepth_le_of_charts (fun _ => rfl) T.V C.I.G C'.I.G n (GlobalTheory.T.surjective_appTop_integralModel_square E H Dw l Xo c T io y.1 C'.I) _ _ B B'
    C.tgT C'.tgT (fun j => Pi.single j 1) (fun j => Pi.single j 1) C.xT C'.xT C.eT C'.eT ?_ ?_
    (GlobalTheory.PowGerm.univSt_holds E H Dw l Xo c T io y C) (GlobalTheory.PowGerm.univSt_holds E H Dw l Xo c T io y C') ?_ ?_
    (fun a => C.uvecT ⟨f.1, Fin.castLE (rk_le f) a⟩) (fun a => C'.uvecT ⟨f.1, Fin.castLE (rk_le f) a⟩)
    (fun a => (C.I.ub f.1 (Fin.castLE (rk_le f) a)).left) (fun a => C.dirT ⟨f.1, Fin.castLE (rk_le f) a⟩) ?_
    (vX_vp X) (jX X) (isIntV_jX X) (lawX C X) (lawX C' X) ?_ ?_ (fgl C X).F_int (fgl C' X).F_int k
  · rw [b1, b2]; exact C.chartT
  · rw [b1', b2']; exact C'.chartT
  · rw [b1, b2, b3, b4, b5, b6]; exact C.frameT
  · rw [b1', b2', b3', b4', b5', b6']; exact C'.frameT
  · intro a
    rw [hn]
    exact C'.dirT ⟨f.1, Fin.castLE (rk_le f) a⟩
  · intro a; rw [b1]; exact lawX_F C X a
  · intro a; rw [b1']; exact lawX_F C' X a

theorem nuFacC_chart_indep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (T : CDVR)
    (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch Ch' : IntegralChartA3 Xo c T io y) (X : ValExt T p) (f : Lt1 Dw) (k : ℕ),
    nuFacC Ch X f k = nuFacC Ch' X f k :=
  fun _ _ _ _ _ _ _ Xo c p _ T io y Ch Ch' X f k =>
    le_antisymm (nuFacC_le Xo c p T io y Ch' Ch X f k) (nuFacC_le Xo c p T io y Ch Ch' X f k)

end GlobalTheory.FactorDepth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryCharacterTrivialOfSiegel
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

noncomputable section

namespace GlobalTheory.SiegelChar

theorem eq_one_of_siegel : (∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (ε : ℤˣ), (∀ i j, σ (J j i) = ((ε : ℤ) : E) * J i j) → J.det ≠ 0 → ∀ c : UG (cA σ) (dbl (incM F J)) →* ℂˣ, Continuous c → (∀ (p : UG (cA σ) (dbl (incM F J))) (t : GL (Fin n) (AE F E)), (p.1.1 : Matrix _ _ (AE F E)) * diagCols (Fin n) = diagCols (Fin n) * t.1 → c p = 1) → c = 1) := by
  intro F E _ _ _ _ _ σ hCM n J ε hJ hdet c hc hP
  letI i2 : Invertible (2 : AE F E) :=
    (Invertible.map (algebraMap (AF F) (AE F E)) (2 : AF F)).copy 2 (map_ofNat _ 2).symm
  have hw1 : (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) *
      Matrix.fromBlocks 1 0 0 (-1) = 1 := by
    rw [Matrix.fromBlocks_multiply]; simp [Matrix.fromBlocks_one]
  let w0 : GL (Fin n ⊕ Fin n) (AE F E) := ⟨_, _, hw1, hw1⟩
  have hwm : w0 ∈ UG (cA σ) (dbl (incM F J)) := by
    show (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E))ᵀ * dbl (incM F J) *
      (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)).map (cA σ) = dbl (incM F J)
    rw [dbl, Matrix.fromBlocks_map, Matrix.fromBlocks_transpose]
    simp [Matrix.fromBlocks_multiply, Matrix.map_one _ (map_zero (cA σ)) (map_one (cA σ)),
      Matrix.map_neg _ (map_neg (cA σ))]
  have hw0 : (w0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) = Matrix.fromBlocks 1 0 0 (-1) := rfl
  let w : UG (cA σ) (dbl (incM F J)) := ⟨w0, hwm⟩
  have hww : w * w = 1 := Subtype.ext (Units.ext hw1)
  have hwD : (w0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) * Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AE F E)) (1 : Matrix (Fin n) (Fin n) (AE F E)) = Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AE F E)) (-1 : Matrix (Fin n) (Fin n) (AE F E)) := by
    rw [hw0, Matrix.fromBlocks_mul_fromRows]; simp
  have hwN : (w0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) * Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AE F E)) (-1 : Matrix (Fin n) (Fin n) (AE F E)) = Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AE F E)) (1 : Matrix (Fin n) (Fin n) (AE F E)) := by
    rw [hw0, Matrix.fromBlocks_mul_fromRows]; simp
  have hq : ∀ (q : UG (cA σ) (dbl (incM F J))) (s : GL (Fin n) (AE F E)),
      ((q : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) * Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AE F E)) (-1 : Matrix (Fin n) (Fin n) (AE F E)) =
        Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AE F E)) (-1 : Matrix (Fin n) (Fin n) (AE F E)) * (s : Matrix (Fin n) (Fin n) (AE F E)) → c q = 1 := by
    intro q s hs
    have key : (w0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) *
        ((q : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) *
        (w0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) * Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AE F E)) (1 : Matrix (Fin n) (Fin n) (AE F E)) =
        Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AE F E)) (1 : Matrix (Fin n) (Fin n) (AE F E)) * (s : Matrix (Fin n) (Fin n) (AE F E)) := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, hwD, hs, ← Matrix.mul_assoc, hwN]
    have h1 : c (w * q * w) = 1 := hP _ s key
    have h2 : c w * c w = 1 := by rw [← map_mul, hww, map_one]
    rw [map_mul, map_mul, mul_comm (c w), mul_assoc, h2, mul_one] at h1
    exact h1
  have hΩ : ∀ h : UG (cA σ) (dbl (incM F J)), (∃ (p : UG (cA σ) (dbl (incM F J))) (t : GL (Fin n) (AE F E)),
      (p.1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) * diagCols (Fin n) = diagCols (Fin n) * t.1 ∧
      IsUnit (Matrix.fromCols (1 : Matrix (Fin n) (Fin n) (AE F E)) (-1 : Matrix (Fin n) (Fin n) (AE F E)) * ((h * p).1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) * Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AE F E)) (-1 : Matrix (Fin n) (Fin n) (AE F E))).det) →
      c h = 1 := by
    rintro h ⟨p, t, hp, hu⟩
    obtain ⟨p', q, t', s, hp', hq', e⟩ := GlobalTheory.T.bigCell_factorisation_doubledUnitaryGroup (AF F) (AE F E) (cA σ) (Fin n) (incM F J) (h * p) hu
    have h1 : c (h * p) = 1 := by rw [e, map_mul, hP p' t' hp', hq q s hq', one_mul]
    rwa [map_mul, hP p t hp, mul_one] at h1
  have hcl : IsClosed {g : UG (cA σ) (dbl (incM F J)) | c g = 1} := isClosed_eq hc continuous_const
  refine MonoidHom.ext fun g => ?_
  exact hcl.closure_subset_iff.2 (fun h hh => hΩ h hh) (GlobalTheory.T.dense_invertible_antidiagonal_corner_doubledUnitary F E σ hCM n J ε hJ hdet g)

end GlobalTheory.SiegelChar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrPlaceDiscKaehlerWedgePermNeg
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

namespace GlobalTheory.FieldPair.Place

variable {k K : Type} [Field k] [Field K] {c : k →+* K} (E : Place c) {n : ℕ}

theorem ord_neg (f : K) : E.ord (-f) = E.ord f := by
  by_cases hf : f = 0
  · simp [hf]
  have h1 : ((-1 : E.ring) : K) = -1 := rfl
  have hu : IsUnit (-1 : E.ring) := isUnit_one.neg
  have h0 : E.ord (-1) = 0 := by rw [← h1]; exact E.ord_eq_zero hu
  rw [neg_eq_neg_one_mul, E.ord_mul (by norm_num) hf, h0, zero_add]

theorem isFormOrd_neg_iff (η : Forms c n) (a : ℤ) : E.IsFormOrd (-η) a ↔ E.IsFormOrd η a := by
  have key : ∀ η : Forms c n, E.IsFormOrd η a → E.IsFormOrd (-η) a := by
    rintro η ⟨ω, hω, f, rfl, hf⟩
    refine ⟨ω, hω, -f, ?_, ?_⟩
    · rw [Units.val_neg, neg_smul]
    · rw [Units.val_neg, E.ord_neg, hf]
  exact ⟨fun h => by simpa using key _ h, key η⟩

theorem formOrd_neg (η : Forms c n) : E.formOrd (-η) = E.formOrd η := by
  by_cases h : ∃ a, E.IsFormOrd η a
  · obtain ⟨a, ha⟩ := h
    rw [((E.isFormOrd_neg_iff η a).2 ha).formOrd_eq, ha.formOrd_eq]
  · have h' : ¬ ∃ a, E.IsFormOrd (-η) a := fun ⟨a, ha⟩ => h ⟨a, (E.isFormOrd_neg_iff η a).1 ha⟩
    rw [formOrd, formOrd, dif_neg h, dif_neg h']

theorem disc_neg (η : Forms c n) (φ : K →₀ ℚ) : E.disc (-η) φ = E.disc η φ := by
  rw [disc, disc, formOrd_neg]

end GlobalTheory.FieldPair.Place

namespace GlobalTheory.FieldPair

theorem dForm_comp_perm {k K : Type} [Field k] [Field K] (c : k →+* K) {n : ℕ} (x : Fin n → K)
    (σ : Equiv.Perm (Fin n)) : dForm c (x ∘ σ) = Equiv.Perm.sign σ • dForm c x := by
  rw [dForm_eq, dForm_eq]
  exact (exteriorPower.ιMulti K n).map_perm (fun i => dFun c (x i)) σ

theorem disc_dForm_perm_neg {k K : Type} [Field k] [CharZero k] [Field K] (c : k →+* K) (n : ℕ)
    (x : Fin n → K) (σ : Equiv.Perm (Fin n)) (E : Place c) (φ : K →₀ ℚ) :
    E.disc (dForm c (x ∘ σ)) φ = E.disc (dForm c x) φ ∧ E.disc (-dForm c x) φ = E.disc (dForm c x) φ := by
  refine ⟨?_, E.disc_neg _ φ⟩
  rw [dForm_comp_perm]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · rw [h, one_smul]
  · rw [h, Units.neg_smul, one_smul, E.disc_neg]

end GlobalTheory.FieldPair
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrPlaceTopFormOrdersApi
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

namespace GlobalTheory.FieldPair

open CategoryTheory AlgebraicGeometry TopologicalSpace in
open scoped TensorProduct in

theorem _root_.GlobalTheory.FieldPair.isFreeGen_dForm_of_trBasis {k K : Type} [Field k] [CharZero k]
    [Field K] (c : k →+* K) {n : ℕ} {x : Fin n → K} (hx : _root_.GlobalTheory.FieldPair.TrBasis c x) :
    _root_.GlobalTheory.TopForm.IsFreeGen K (_root_.GlobalTheory.TopForm.dForm c x) := by
  letI : Algebra k K := c.toAlgebra
  have hb : IsTranscendenceBasis k x := hx
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  haveI : Algebra.IsAlgebraic (IntermediateField.adjoin k (Set.range x)) K :=
    hb.isAlgebraic_field
  haveI : Algebra.IsSeparable (IntermediateField.adjoin k (Set.range x)) K :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  obtain ⟨b, hbx⟩ := _root_.GlobalTheory.exists_basis_kaehler_of_algebraicIndependent hb.1
  exact _root_.GlobalTheory.TopForm.isFreeGen_dForm x b (fun i => by rw [hbx i])

open CategoryTheory AlgebraicGeometry TopologicalSpace in
open scoped TensorProduct in

theorem _root_.GlobalTheory.FieldPair.formOrd_api : ∀ {k K : Type} [Field k] [CharZero k] [Field K]
    (c : k →+* K) (n : ℕ) (x : Fin n → K), _root_.GlobalTheory.FieldPair.TrBasis c x →
  _root_.GlobalTheory.TopForm.IsFreeGen K (_root_.GlobalTheory.TopForm.dForm c x) ∧
  ∀ E : _root_.GlobalTheory.FieldPair.Place c,
    (∃ ω : _root_.GlobalTheory.TopForm.Forms E.const n, _root_.GlobalTheory.TopForm.IsFreeGen E.ring ω) ∧
    (∀ η : _root_.GlobalTheory.TopForm.Forms c n, η ≠ 0 → E.IsFormOrd η (E.formOrd η)) ∧
    (∀ (η : _root_.GlobalTheory.TopForm.Forms c n) (f : K), η ≠ 0 → f ≠ 0 →
      E.formOrd (f • η) = E.ord f + E.formOrd η) ∧
    (∀ (η : _root_.GlobalTheory.TopForm.Forms c n) (a : ℤ), η ≠ 0 → E.IsFormOrd η a →
      E.formOrd η = a) := by
  intro k K _ _ _ c n x hx
  refine ⟨_root_.GlobalTheory.FieldPair.isFreeGen_dForm_of_trBasis c hx, fun E => ⟨?_, ?_, ?_, ?_⟩⟩
  · exact E.exists_isFreeGen hx
  · intro η hη
    exact E.isFormOrd_formOrd hx hη
  · intro η f hη hf
    exact E.formOrd_smul hx hη hf
  · intro η a _ h
    exact h.formOrd_eq

end GlobalTheory.FieldPair
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaTildeHeckeCharSplitMulSignOfNormFormulaStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts GlobalTheory.FinWeil GlobalTheory.FinWeilO GlobalTheory.FockCompare GlobalTheory.VacUnique GlobalTheory.RatAut
open scoped TensorProduct Kronecker ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaTildeHeckeChar_split_mul_sign_of_norm_formula : ∀ (D : D7) (η : (AE D)ˣ →* Circle), IsEtaTilde D η → ∀ (lam : ℕ →* ℂ), GoodNorm (GlobalTheory.FinWeil.sgO D) lam → (∀ n : ℕ, n ≠ 0 → (∀ q : ℕ, q.Prime → Formalism.MainNotions.StandardLatticesGL3.InertQ D q → ¬ q ∣ n) → lam n = (Real.sqrt n : ℂ)) → ∀ ε, IsHalfIdem D ε → ∀ (x : D.host.E) (k : ℕ), x ≠ 0 → (k : ℚ) = |Algebra.norm ℚ x| → ∀ y : (AE D)ˣ, (y : AE D) = (ε + cA D ε) * incA D x + (1 - (ε + cA D ε)) → ∃ r : ℝ, 0 < r ∧ (η y : ℂ) * lam k * ∏ τ, tauE D τ x = r := by
  first | exact @GlobalTheory.EtaProduct.eta_split_mul_lam_pos | exact GlobalTheory.EtaProduct.eta_split_mul_lam_pos | (intros; apply GlobalTheory.EtaProduct.eta_split_mul_lam_pos <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EulerCharH0H1BoundHigher
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory.NefRR

theorem abs_chi_sub_hdim_zero_add_hdim_one_le : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k X) → ∀ (n : ℕ) (L : LB X), L.IsLB → ∀ (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (n : ℕ) → ∀ e : ℕ → ℕ, (∀ i, 2 ≤ i → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist F (lbPow L m)) i ≤ C * e m)) → ∃ C : ℕ, ∀ m : ℕ, |chi k (twist F (lbPow L m)) - (hdim k (twist F (lbPow L m)) 0 : ℤ) + (hdim k (twist F (lbPow L m)) 1 : ℤ)| ≤ C * (e m : ℤ) := by
  intro k _ _ X _ hp n L hL F _ hF e he
  choose C hC using fun i : ℕ => he (i + 2) (by omega)
  refine ⟨∑ i ∈ Finset.range n, C i, fun m => ?_⟩
  have hM : (lbPow L m).IsLB := isLB_lbPow hL m
  haveI : IsFiniteQC (twist F (lbPow L m)) := isFiniteQC_twist hM
  have hv : ∀ i, n + 2 ≤ i → Subsingleton (coh (twist F (lbPow L m)) i) := fun i hi =>
    subsingleton_coh_of_isProjOver hp _
      (((suppDim_twist hM).trans_le hF).trans_lt (by exact_mod_cast (by omega : n < i)))
  rw [chi_eq_sum_range k (n + 2) hv, Finset.sum_range_succ', Finset.sum_range_succ']
  have h : ∀ a b c : ℤ, a + (-1 : ℤ) ^ (0 + 1) * b + (-1 : ℤ) ^ 0 * c - c + b = a := by
    intro a b c; ring
  rw [h]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Nat.cast_sum, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast]
  exact_mod_cast hC i m

end GlobalTheory.NefRR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyCompletedTensorMatrixSplitSemilocalStatement
section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_completedTensor_matrix_split_semilocal : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (γ : G.C), (minpoly G.F γ).natDegree = G.n → (minpoly G.F γ).Separable → ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), ∃ (K : Type) (_ : CommRing K) (R : Subring K) (Φ : Matrix (Fin G.n) (Fin G.n) K ≃+* Qv v ⊗[ℚ] G.C), Set.Finite {I : Ideal R | I.IsMaximal} ∧ (∀ a : Qv v ⊗[ℚ] G.C, IsIntV G v a ↔ ∀ i j, Φ.symm a i j ∈ R) ∧ ∃ Q : Polynomial R, Q.Separable ∧ Q.map R.subtype = (Φ.symm ((1 : Qv v) ⊗ₜ[ℚ] γ)).charpoly := by
  first | (exact @GlobalTheory.OrbFinAf.split_eventually) | (exact GlobalTheory.OrbFinAf.split_eventually) | (intros; apply GlobalTheory.OrbFinAf.split_eventually  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleSectionNonvanishingAtNotSpecializing
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem exists_sec_mem_not_mem_of_not_specializes :
    ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (N : LB X) (x z : X), IsAmpleLB N → ¬ z ⤳ x →
      ∃ (l : ℕ) (s : (lbPow N l).Sec), 0 < l ∧ x ∈ nonzeroLocus s ∧ z ∉ nonzeroLocus s := by
  intro X _ _ N x z hN hzx
  let U : X.Opens := ⟨(closure ({z} : Set X))ᶜ, isClosed_closure.isOpen_compl⟩
  have hx : x ∈ U := fun h => hzx (specializes_iff_mem_closure.2 h)
  obtain ⟨n, hn, s, hs, hle, -⟩ := hN.exists_affine_le hx
  exact ⟨n, s, hn, hs, fun h => hle h (subset_closure rfl)⟩

end GlobalTheory.PairStep
end

