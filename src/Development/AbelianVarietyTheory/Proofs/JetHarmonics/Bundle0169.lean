import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0115
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0102
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsContraction
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0036
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0160
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointMoveCalculus
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0016
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CabsDiagEqOne
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.UnitFramesGeneratorRatioModulusOne
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.BoundedSectionAlgebra
import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0005
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFibreSimplyTransitiveOfLaws
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicIndexSums
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0015

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrameFreeFiniteOrderRuleConstPeriodSpace
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct
open GlobalTheory.ShortMove

namespace GlobalTheory.FiniteOrderConst

open GlobalTheory.IndefiniteRowSideFullHecke.DeltaDatumCombinedCoefficient

theorem isHolTo_of_eqOn {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X : Scheme.{0}} {B : Set V}
    {y y' : V → (Sp ℂ ⟶ X)} (h : IsHolTo B y) (e : ∀ b ∈ B, y' b = y b) : IsHolTo B y' := by
  intro U f
  have hs : {b ∈ B | ⊤ ≤ y' b ⁻¹ᵁ U} = {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U} :=
    Set.ext fun b => and_congr_right fun hb => by rw [e b hb]
  rw [hs]
  exact ⟨(h U f).1, (h U f).2.congr fun b hb => by rw [e b hb.1]⟩

theorem valAt'_top {X : Scheme.{0}} (y : Sp ℂ ⟶ X) (f : Γ(X, ⊤)) : valAt' y ⊤ f = fnAt y f := by
  rw [valAt', dif_pos (show (⊤ : (Sp ℂ).Opens) ≤ y ⁻¹ᵁ ⊤ from le_rfl), valAt, fnAt]
  have : y.appLE ⊤ ⊤ le_rfl = y.appTop := Scheme.Hom.appLE_eq_app y
  exact congrArg (fun q => (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom (q.hom f)) this

theorem fnAt_eq_of_pow {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X : Scheme.{0}} {B : Set V}
    {a : V → (Sp ℂ ⟶ X)} (hB : IsPreconnected B) (h : IsHolTo B a) (f : Γ(X, ⊤)) {N : ℕ} (hN : 0 < N)
    (hp : ∀ b ∈ B, fnAt (a b) f ^ N = 1) {b b' : V} (hb : b ∈ B) (hb' : b' ∈ B) : fnAt (a b) f = fnAt (a b') f := by
  have hc : ContinuousOn (fun b => fnAt (a b) f) B := by
    have := (h ⊤ f).2.continuousOn
    simp only [valAt'_top] at this
    exact this.mono fun b hb => ⟨hb, le_rfl⟩
  have hfin : {z : ℂ | z ^ N = 1}.Finite :=
    (Polynomial.nthRoots N (1 : ℂ)).toFinset.finite_toSet.subset fun z hz => by
      simpa [Polynomial.mem_nthRoots hN] using hz
  exact hB.constant_of_mapsTo hfin.isDiscrete hc hp hb hb'

theorem const_on_period_space : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (f : Rul Xo c), f ∈ sec Xo c 0 0 → (∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra c.F K] (y y' : FrPt Xo c K), y'.x = y.x → evR Xo c f y' = evR Xo c f y) → (∃ N : ℕ, 0 < N ∧ ∀ y : FrPt Xo c (CAt σ), evR Xo c f y ^ N = 1) → ∀ (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty), IsTypeFn H Dw.p Dw.q ty → ∀ (i : Fin F.n) (P P' : (F.Di i).La →+ (Fin g → ℂ)) (y y' : FrPt Xo c (CAt σ)), IsPeriod (F.Di i) ty P → IsPeriod (F.Di i) ty P' → y.x = F.u i P → y'.x = F.u i P' → evR Xo c f y = evR Xo c f y' := by
  classical
  rintro E _ _ _ H Dw l Xo c σ f hf hfree ⟨N, hN, hp⟩ g ty F hty i P P' y y' hP hP' hy hy'
  let _ : Algebra c.F ℂ := σ.toAlgebra
  obtain ⟨f₀, hf₀⟩ := GlobalTheory.FrameFreeRule.exists_fn E H Dw l Xo c f hf hfree
  obtain ⟨m, B, Q, -, hB, hconv, h0, hQ0, hQ, hall⟩ := GlobalTheory.PeriodChart.period_chart E H (F.Di i) g ty
    (by rw [(F.sig i).1, (F.sig i).2]; exact hty) P hP
  obtain ⟨b, ⟨hb, h, hh⟩, -⟩ := hall P' hP'
  have hbP : F.u i (Q b) = F.u i P' :=
    (F.fibre i (Q b) P' (hQ.1 b hb) hP').2 ⟨LinearEquiv.refl _ _, h, fun _ _ => rfl, fun a _ => ⟨0, by simp⟩,
      fun a => ⟨0, by simp⟩, hh⟩
  have hex : ∀ t, ∃ z : FrPt Xo c ℂ, t ∈ B → z.x = F.u i (Q t) := fun t => by
    by_cases ht : t ∈ B
    · obtain ⟨z, hz⟩ := GlobalTheory.NonIntegralFrameExample.exists_framed (c := c) (S := ℂ) (F.u i (Q t)) (F.over_σ i _ (hQ.1 t ht))
      exact ⟨z, fun _ => hz⟩
    · exact ⟨y, fun h => absurd h ht⟩
  choose z hz using hex
  have hhol : IsHolTo B fun t => basePt (z t) :=
    GlobalTheory.HolFibre.isHolTo_of_isPullback (IsPullback.of_hasPullback _ _)
      (isHolTo_of_eqOn (F.hol i m B Q hB hQ).1 fun t ht => (pullback.lift_fst _ _ _).trans (hz t ht))
      (isHolTo_of_eqOn (GlobalTheory.HolFibre.isHolTo_const hB (spMap σ)) fun t _ => pullback.lift_snd _ _ _)
  have key := fnAt_eq_of_pow hconv.isPreconnected hhol f₀ hN
    (fun t _ => by rw [← hf₀ ℂ (z t)]; exact hp (z t)) h0 hb
  rw [← hf₀ ℂ, ← hf₀ ℂ] at key
  exact (hfree ℂ (z 0) y (hy.trans (by rw [hz 0 h0, hQ0]))).trans
    (key.trans (hfree ℂ y' (z b) ((hz b hb).trans (hbP.trans hy'.symm))))

end GlobalTheory.FiniteOrderConst
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MemCuspFormsOfMultipleRationalIsometryMove
section
noncomputable section

namespace GlobalTheory.LevelCusp.Transport

open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LevelCusp
open ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity ReciprocityTheory.ChartRestriction.G.FD.FlowMeanContinuity
open GlobalTheory.Dict (castFr)
open scoped Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem integral_eq_zero_cast {α : Type} {Ψ Ψ' : Finset α} (h : Ψ = Ψ') {L : AddSubgroup (Ψ → ℝ)}
    {L' : AddSubgroup (Ψ' → ℝ)} [Countable L] [Countable L'] {D : Set (Ψ → ℝ)} {D' : Set (Ψ' → ℝ)}
    {g : (Ψ → ℝ) → ℂ} {g' : (Ψ' → ℝ) → ℂ} {c : ℂ}
    (hg : ∀ s, g s = c * g' (fun τ => s ⟨τ.1, h ▸ τ.2⟩))
    (hD : IsAddFundamentalDomain L D volume) (hD' : IsAddFundamentalDomain L' D' volume)
    (hf : volume D < ⊤) (hf' : volume D' < ⊤) (hp' : 0 < volume D') (hc : Continuous g)
    (hb : ∃ C : ℝ, ∀ s, ‖g s‖ ≤ C) (hL : ∀ p ∈ L, ∀ s, g (p + s) = g s)
    (hL' : ∀ p ∈ L', ∀ s, g' (p + s) = g' s) (h0 : ∫ s in D', g' s = 0) : ∫ s in D, g s = 0 := by
  subst h
  have hg' : ∀ s, g s = c * g' s := hg
  have key := GlobalTheory.mean_fundamentalDomain_eq_of_periodic Ψ L L' D D' g hD hD' hf hf' hc hb (fun p hp s => by rw [add_comm, hL p hp])
    (fun p hp s => by rw [hg', hg', add_comm, hL' p hp])
  have e : ∫ s in D', g s = 0 := by
    simp only [hg']
    rw [integral_const_mul, h0, mul_zero]
  rw [e, mul_zero] at key
  refine (mul_eq_zero.1 key.symm).resolve_left ?_
  exact_mod_cast (ENNReal.toReal_pos hp'.ne' hf'.ne).ne'

variable {X X' : Data E r} {a : GL (Fin r) E}

theorem nfac_eq (h : IsMatch X X' a) {la : Wt X.Ψ r} {la' : Wt X'.Ψ r}
    (hl : ∀ (τ : X'.Ψ) i, la' τ i = la ⟨τ.1, h.mem τ⟩ i) (x : Frame X.Ψ r) :
    X'.nfac la' (lact a (castFr h.psi x)) = X.nfac la x := by
  unfold Data.nfac
  simp only [h.dmin_eq]
  exact (GlobalTheory.Dict.Pull.cast_wt h.psi rfl hl (castFr h.psi x)).symm

theorem isIso_map (h : IsMatch X X' a) {ξ : Fin r → E} (hξ : X.IsIso ξ) :
    X'.IsIso ((a : Matrix (Fin r) (Fin r) E) *ᵥ ξ) := by
  refine ⟨(h.lat ξ).1 hξ.1, by rw [h.iso, hξ.2.1], fun e => hξ.2.2 ?_⟩
  rw [← GlobalTheory.Dict.Pull.inv_mulVec a ξ, e, Matrix.mulVec_zero]

theorem map_mul_flowMat (h : IsMatch X X' a) (ξ : Fin r → E) (τ : X'.Ψ) (s : ℂ) :
    (a : Matrix (Fin r) (Fin r) E).map τ.1 * X.flowMat ξ ⟨τ.1, h.mem τ⟩ s =
      X'.flowMat ((a : Matrix (Fin r) (Fin r) E) *ᵥ ξ) τ s * (a : Matrix (Fin r) (Fin r) E).map τ.1 := by
  have he : Data.emb τ.1 ((a : Matrix (Fin r) (Fin r) E) *ᵥ ξ) =
      (a : Matrix (Fin r) (Fin r) E).map τ.1 *ᵥ Data.emb τ.1 ξ := by
    funext i
    simp [Data.emb, Matrix.mulVec, dotProduct]
  have hc : X'.c τ = X.c ⟨τ.1, h.mem τ⟩ := by simp only [Data.c, h.xi]
  refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
  simp only [Matrix.toLin'_apply]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, flowMat_mulVec, flowMat_mulVec, he, h.hermC_eq, hc,
    Matrix.mulVec_add, Matrix.mulVec_smul]

theorem lact_flow (h : IsMatch X X' a) (ξ : Fin r → E) (s : X.Ψ → ℂ) (x : Frame X.Ψ r) :
    lact a (castFr h.psi (X.flow ξ s x)) =
      X'.flow ((a : Matrix (Fin r) (Fin r) E) *ᵥ ξ) (fun τ => s ⟨τ.1, h.mem τ⟩) (lact a (castFr h.psi x)) := by
  funext τ
  show (a : Matrix (Fin r) (Fin r) E).map τ.1 * (X.flowMat ξ ⟨τ.1, h.mem τ⟩ (s ⟨τ.1, h.mem τ⟩) *
      mat x ⟨τ.1, h.mem τ⟩) = X'.flowMat ((a : Matrix (Fin r) (Fin r) E) *ᵥ ξ) τ (s ⟨τ.1, h.mem τ⟩) *
      ((a : Matrix (Fin r) (Fin r) E).map τ.1 * mat x ⟨τ.1, h.mem τ⟩)
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, map_mul_flowMat h]

theorem freq_zero (X : Data E r) (la : Wt X.Ψ r) :
    ∀ p ∈ X.periods la, ∃ k : ℤ, 2 * ∑ τ, (0 : X.Ψ → ℝ) τ * p τ = k := fun p _ => ⟨0, by simp⟩

theorem fjI_zero (X : Data E r) (ξ : Fin r → E) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) (s : X.Ψ → ℝ) :
    fjI X ξ 0 P x s = P (X.flow ξ (cR X s) x) := by
  simp [fjI]
  rfl

theorem fj_zero_eq (X : Data E r) (la : Wt X.Ψ r) (ξ : Fin r → E) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) :
    X.fj la ξ 0 P x = ((volume (ExponentialGrowthExclusion.exists_fd X la).choose).toReal : ℂ)⁻¹ *
      ∫ s in (ExponentialGrowthExclusion.exists_fd X la).choose, fjI X ξ 0 P x s := by
  rw [Data.fj, if_pos (freq_zero X la), dif_pos (ExponentialGrowthExclusion.exists_fd X la)]
  rfl

end GlobalTheory.LevelCusp.Transport

end

open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.LevelCusp
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix

open GlobalTheory.LevelCusp.Transport ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity ReciprocityTheory.ChartRestriction.G.FD.RealEmbeddingCharacters
  ReciprocityTheory.ChartRestriction.G.FD.FlowMeanContinuity in

theorem GlobalTheory.LevelCusp.mem_SS_of_isMatch : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X X' : Data E r) (a : GL (Fin r) E) (h : IsMatch X X' a) (la : Wt X.Ψ r) (la' : Wt X'.Ψ r), (∀ (τ : X'.Ψ) i, la' τ i = la ⟨τ.1, h.mem τ⟩ i) → ∀ (P : Frame X.Ψ r → ℂ) (Q : Frame X'.Ψ r → ℂ) (c : ℂ), X.IsSec la P → Q ∈ X'.SS la' → (∀ x ∈ X.dom, P x = c * Q (lact a (castFr h.psi x))) → P ∈ X.SS la := by
  intro E _ _ _ r X X' a h la la' hl P Q c hP hQ hPQ
  obtain ⟨⟨hQs, C, hC⟩, hQ0⟩ := hQ
  have hb : ∀ x ∈ X.dom, X.pnorm la P x ≤ ‖c‖ * C := fun x hx => by
    have := hC _ (h.mem_dom hx)
    rw [BoundedSectionAlgebra.pnorm_eq, nfac_eq h hl] at this
    rw [BoundedSectionAlgebra.pnorm_eq, hPQ x hx, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left this (norm_nonneg _)
  refine ⟨⟨hP, _, hb⟩, fun ξ hξ x hx => ?_⟩
  have hξ' := isIso_map h hξ
  have hx' := h.mem_dom hx
  have h0 := hQ0 _ hξ' _ hx'
  obtain ⟨-, hD, -, hf⟩ := (ExponentialGrowthExclusion.exists_fd X la).choose_spec
  obtain ⟨-, hD', hp', hf'⟩ := (ExponentialGrowthExclusion.exists_fd X' la').choose_spec
  rw [fj_zero_eq] at h0 ⊢
  have hne : ((MeasureTheory.volume (ExponentialGrowthExclusion.exists_fd X' la').choose).toReal : ℂ)⁻¹ ≠ 0 :=
    inv_ne_zero (by exact_mod_cast (ENNReal.toReal_pos hp'.ne' hf'.ne).ne')
  have : Countable (X.periods la) := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  have : Countable (X'.periods la') := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  rw [integral_eq_zero_cast h.psi (c := c) (fun s => ?_) hD hD' hf hf' hp'
    (fjI_continuous X la P hP hξ.2.1 0 hx) ⟨‖c‖ * C / X.nfac la x, fun s => ?_⟩
    (fjI_periodic X la P hP hξ.1 hξ.2.1 0 (freq_zero X la) hx)
    (fjI_periodic X' la' Q hQs hξ'.1 hξ'.2.1 0 (freq_zero X' la') hx')
    ((mul_eq_zero.1 h0).resolve_left hne), mul_zero]
  · rw [fjI_zero, fjI_zero, hPQ _ (flow_real_mem_dom X hξ.2.1 s x hx), lact_flow h]
    rfl
  · have hT := hb _ (flow_real_mem_dom X hξ.2.1 s x hx)
    rw [BoundedSectionAlgebra.pnorm_eq, BoundedSectionAlgebra.nfac_flow_real X hξ.2.1] at hT
    rw [fjI_zero, le_div_iff₀ (BoundedSectionAlgebra.nfac_pos X hx la)]
    exact hT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NonemptyTateIsometryIntegralFramedPointChart
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open IsDedekindDomain

namespace GlobalTheory.IntegralTate

theorem nonempty_tateIso_pull {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (m : SABMap t' t f) {k : Type} [Field k]
    (x : Sp k ⟶ S')
    (I : TateIso D k (Over.mk (x ≫ f) ⟶ t.G) (fun a g => g ≫ t.act.act a)
      (fun n g g' c => WeilIs t.G t.PP.L n g g' (unitOn c))) :
    Nonempty (TateIso D k (Over.mk x ⟶ t'.G) (fun a g => g ≫ t'.act.act a)
      (fun n g g' c => WeilIs t'.G t'.PP.L n g g' (unitOn c))) := by
  have hL : LBIso t'.PP.L (t.PP.L.pull m.cm.F) := by
    obtain ⟨w, hw, -⟩ := m.lin
    exact ⟨w, hw⟩
  refine ⟨ObjPull.tateMove (ObjPull.pushEquiv m.cart (Over.mk x)) (fun c g => ?_) (fun n g g' c hc => ?_) I⟩
  · apply Over.OverMorphism.ext
    show (g.left ≫ _) ≫ _ = (g.left ≫ _) ≫ _
    rw [Category.assoc, m.act, Category.assoc]
  · exact (weilIs_grpPullback_of_comm S S' t.G t'.G f m.cm.F t.PP.L t'.PP.L t.PP.isLB t'.PP.isLB m.cart hL
      (Over.mk x) n g g' _ _ _ rfl rfl).2 hc

theorem nonempty_tateIso_of_intChart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l),
 letI := H.starRing
 ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y) (P : PELUnif (maximalIdeal T.V) C.I.G) (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F], Nonempty (TateIso Dw F (TFK (R := T.V) F ⟶ P.A.A) (fun a x => x ≫ P.oA.act a) (fun k x x' z => WeilIs P.A.A P.A.L k x x' (unitOn z))) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro T io y C P F _ _ _ _ _ _
  letI := io.toAlgebra
  obtain ⟨β, hβ⟩ := GlobalTheory.LevelFibre.exists_spMap ((jFK (R := T.V) F ≫ y.1.x) ≫ Xo.s)
  obtain ⟨-, I₀, -⟩ := Xo.univ.geom F (jFK (R := T.V) F ≫ y.1.x) β hβ
  obtain ⟨I₁⟩ := nonempty_tateIso_pull C.I.m1 (jFK (R := T.V) F) I₀
  obtain ⟨I₂, -⟩ := GlobalTheory.LevelFibre.exists_tate_push_comm C.I.m2 (jFK (R := T.V) F) _ rfl
    (ObjPull.pushEquiv C.I.m2.cart (Over.mk (jFK (R := T.V) F))) (fun _ => rfl) I₁
  obtain ⟨I₃, -⟩ := ReciprocityTheory.ChartRestriction.G.H1.tateTransport_holds GlobalTheory.firstFiveLaws.1.weil E H T.V _ C.I.G P F Dw I₂
  exact ⟨I₃⟩

end GlobalTheory.IntegralTate
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NotAntiIsometryOfTriangularRelatedPeriods
section
open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.LevelCusp
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
open scoped ComplexConjugate

noncomputable section

namespace GlobalTheory.AntiIsom

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def hermL (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (y : Fin r → ℂ) : (Fin r → ℂ) →ₗ[ℂ] ℂ where
  toFun w := hermC τ G w y
  map_add' u v := by simp [hermC, add_mul, Finset.sum_add_distrib]
  map_smul' c v := by simp [hermC, Finset.mul_sum, mul_assoc]

open NumberField AlgebraicGeometry CategoryTheory in
open scoped Matrix in
open scoped ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
private theorem exists_emb_not_mem_conjEmb_mem_Ψ (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) :
    ∃ σ τ : E →+* ℂ, σ ∉ X.Ψ ∧ τ ∈ X.Ψ ∧ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb σ = τ := by
  have hconj : ∀ σ : E →+* ℂ, _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb σ = ComplexEmbedding.conjugate σ := fun σ => by
    ext t; simp [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb, ComplexEmbedding.conjugate_coe_eq]
  obtain ⟨ρ⟩ : Nonempty (E →+* ℂ) := inferInstance
  by_cases hρ : ρ ∈ X.Ψ
  · refine ⟨ComplexEmbedding.conjugate ρ, ρ, (X.cmType ρ).1 hρ, hρ, ?_⟩
    ext t
    simp [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb, ComplexEmbedding.conjugate_coe_eq]
  · refine ⟨ρ, _, hρ, ?_, rfl⟩
    rw [hconj]
    by_contra h
    exact hρ ((X.cmType ρ).2 h)

open NumberField AlgebraicGeometry CategoryTheory in
open scoped Matrix in
open scoped ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
private theorem hermC_self_re_eq_neg_sum_normSq_of_p0_eq_zero (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (h0 : X.p0 = 0) (τ : X.Ψ) :
    ∃ P : Matrix (Fin r) (Fin r) ℂ, P.det ≠ 0 ∧ ∀ p : Fin r → ℂ,
      (_root_.ReciprocityTheory.ChartRestriction.G.FD.hermC (↑τ) X.Gm p p).re = -∑ a, Complex.normSq ((P⁻¹ *ᵥ p) a) := by
  obtain ⟨P, hP, hG⟩ := X.signature τ
  refine ⟨P, hP, fun p => ?_⟩
  rw [_root_.ReciprocityTheory.ChartRestriction.G.FD.IntegralBasisReduction.hermC_normal X hP _ hG p p]
  simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn, h0, mul_assoc, Complex.mul_conj, Complex.re_sum]

open NumberField AlgebraicGeometry CategoryTheory in
open scoped Matrix in
open scoped ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
private theorem hermC_col_emb_eq_of_not_mem_Ψ (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) (v : Fin r → E)
    {σ τ : E →+* ℂ} (hσ : σ ∉ X.Ψ) (hτ : τ ∈ X.Ψ) (hστ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb σ = τ) (i : ℕ)
    (hi : X.p0 - 1 - i < r) :
    _root_.Formalism.L2.PjFree.perFr X x v σ i =
      _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.col (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x ⟨τ, hτ⟩) ⟨X.p0 - 1 - i, hi⟩) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ v) := by
  subst hστ
  unfold _root_.Formalism.L2.PjFree.perFr
  rw [dif_neg hσ, dif_pos hτ, dif_pos hi]

open NumberField AlgebraicGeometry CategoryTheory in
open scoped Matrix in
open scoped ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
private theorem hermC_first_col_self_re_pos (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) {x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r} (hx : x ∈ X.dom)
    (τ : X.Ψ) (hp : 0 < X.p0) (hr : 0 < r) :
    0 < (_root_.ReciprocityTheory.ChartRestriction.G.FD.hermC (↑τ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.col (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) ⟨0, hr⟩)
      (_root_.ReciprocityTheory.ChartRestriction.G.FD.col (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) ⟨0, hr⟩)).re := by
  have hx' : x ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.GG X.Ψ X.Gm X.p0 := hx
  have h := (hx' τ).2 ⟨1, by omega⟩
  have h1 : _root_.ReciprocityTheory.ChartRestriction.G.FD.psgn X.p0 1 = 1 := by simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.psgn, _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn, hp]
  simp only [h1, one_mul] at h
  simp only [_root_.ReciprocityTheory.ChartRestriction.G.FD.dmin, _root_.ReciprocityTheory.ChartRestriction.G.FD.lminor, _root_.ReciprocityTheory.ChartRestriction.G.FD.gram, Matrix.det_fin_one] at h
  exact h

open NumberField AlgebraicGeometry CategoryTheory in
open scoped Matrix in
open scoped ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in

theorem _root_.GlobalTheory.AntiIsom.not_antiIsometry : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X X' : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r), X.Ψ = X'.Ψ → X.p0 = X'.p0 → 1 ≤ r → ∀ (a : GL (Fin r) E), (∀ u v, _root_.ReciprocityTheory.ChartRestriction.G.FD.herm X'.Gm ((a : Matrix (Fin r) (Fin r) E) *ᵥ u) ((a : Matrix (Fin r) (Fin r) E) *ᵥ v) = -1 * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm u v) → ∀ (m : (E →+* ℂ) → ℕ), (∀ τ ∈ X.Ψ, m τ = r - X.p0) → (∀ τ ∉ X.Ψ, m τ = X.p0) → ∀ x ∈ X.dom, ∀ x' ∈ X'.dom, ∀ (A : (E →+* ℂ) → ℕ → ℕ → ℂ), (∀ τ i j, j < i → A τ i j = 0) → (∀ τ, ∀ i < m τ, ∀ v ∈ X.Λ, _root_.Formalism.L2.PjFree.perFr X' x' ((a : Matrix (Fin r) (Fin r) E) *ᵥ v) τ i = ∑ j ∈ Finset.range (m τ), A τ i j * _root_.Formalism.L2.PjFree.perFr X x v τ j) → False := by
  intro E _ _ _ r X X' hΨ hp r1 a ha m _ hmout x hx x' hx' A hA hrel
  have hr : 0 < r := r1
  have hiso : ∀ (τ : E →+* ℂ) (u v : Fin r → ℂ),
      _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ X'.Gm (((a : Matrix (Fin r) (Fin r) E).map τ) *ᵥ u)
        (((a : Matrix (Fin r) (Fin r) E).map τ) *ᵥ v) = -_root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ X.Gm u v := by
    intro τ u v
    have h := _root_.GlobalTheory.LevelCusp.hermC_of_herm (ε := -1) ha τ u v
    simpa using h
  obtain ⟨σ, τ, hσ, hτ, hστ⟩ := exists_emb_not_mem_conjEmb_mem_Ψ X
  have hτ' : τ ∈ X'.Ψ := hΨ ▸ hτ
  have hσ' : σ ∉ X'.Ψ := hΨ ▸ hσ
  rcases Nat.eq_zero_or_pos X.p0 with h0 | hp0
  · obtain ⟨P, hP, hPf⟩ := hermC_self_re_eq_neg_sum_normSq_of_p0_eq_zero X h0 ⟨τ, hτ⟩
    obtain ⟨P', _, hPf'⟩ := hermC_self_re_eq_neg_sum_normSq_of_p0_eq_zero X' (hp ▸ h0) ⟨τ, hτ'⟩
    let p : Fin r → ℂ := Pi.single ⟨0, hr⟩ 1
    have e1 := hPf p
    have e2 := hPf' ((a : Matrix (Fin r) (Fin r) E).map τ *ᵥ p)
    simp only at e1 e2
    rw [hiso, Complex.neg_re, e1] at e2
    have s1 : 0 ≤ ∑ i, Complex.normSq ((P⁻¹ *ᵥ p) i) :=
      Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
    have s2 : 0 ≤ ∑ i, Complex.normSq ((P'⁻¹ *ᵥ ((a : Matrix (Fin r) (Fin r) E).map τ *ᵥ p)) i) :=
      Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
    have hzero : ∑ i, Complex.normSq ((P⁻¹ *ᵥ p) i) = 0 := by linarith
    have hw : P⁻¹ *ᵥ p = 0 := by
      funext i
      have h := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Complex.normSq_nonneg _)).1
        hzero i (Finset.mem_univ _)
      simpa using h
    have hu : IsUnit P.det := isUnit_iff_ne_zero.2 hP
    have hp0 : p = 0 := by
      calc p = (P * P⁻¹) *ᵥ p := by rw [Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
        _ = 0 := by rw [← Matrix.mulVec_mulVec, hw, Matrix.mulVec_zero]
    have h := congrFun hp0 ⟨0, hr⟩
    simp [p] at h
  · have hi : X.p0 - 1 - (X.p0 - 1) < r := by omega
    have hi' : X'.p0 - 1 - (X.p0 - 1) < r := by omega
    have hlat : ∀ v ∈ X.Λ,
        _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ X'.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.col (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x' ⟨τ, hτ'⟩) ⟨0, hr⟩)
          ((a : Matrix (Fin r) (Fin r) E).map τ *ᵥ _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ v) =
        A σ (X.p0 - 1) (X.p0 - 1) *
          _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.col (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x ⟨τ, hτ⟩) ⟨0, hr⟩) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ v) := by
      intro v hv
      have h := hrel σ (X.p0 - 1) (by rw [hmout σ hσ]; omega) v hv
      rw [hmout σ hσ, Finset.sum_eq_single (X.p0 - 1)] at h
      · rw [hermC_col_emb_eq_of_not_mem_Ψ X' x' _ hσ' hτ' hστ _ hi', hermC_col_emb_eq_of_not_mem_Ψ X x v hσ hτ hστ _ hi] at h
        have e1 : (⟨X.p0 - 1 - (X.p0 - 1), hi⟩ : Fin r) = ⟨0, hr⟩ := Fin.ext (by simp)
        have e2 : (⟨X'.p0 - 1 - (X.p0 - 1), hi'⟩ : Fin r) = ⟨0, hr⟩ := Fin.ext (by simp; omega)
        have emb_mul : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ ((a : Matrix (Fin r) (Fin r) E) *ᵥ v) =
            (a : Matrix (Fin r) (Fin r) E).map τ *ᵥ _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ v := by
          funext k
          exact RingHom.map_mulVec τ (a : Matrix (Fin r) (Fin r) E) v k
        rw [e1, e2, emb_mul] at h
        exact h
      · intro j hj hne
        rw [hA σ _ _ (by simp at hj; omega), zero_mul]
      · intro h
        simp at h
        omega
    have emb_add : ∀ v w : Fin r → E,
        _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ (v + w) = _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ v + _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ w := by
      intro v w; funext k; simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb]
    have emb_smul : ∀ (e : E) (v : Fin r → E),
        _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ (e • v) = τ e • _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ v := by
      intro e v; funext k; simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb]
    have hE : ∀ v : Fin r → E,
        _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ X'.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.col (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x' ⟨τ, hτ'⟩) ⟨0, hr⟩)
          ((a : Matrix (Fin r) (Fin r) E).map τ *ᵥ _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ v) =
        A σ (X.p0 - 1) (X.p0 - 1) *
          _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.col (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x ⟨τ, hτ⟩) ⟨0, hr⟩) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ v) := by
      intro v
      have hv : v ∈ Submodule.span E (X.Λ : Set (Fin r → E)) := by
        rw [X.Λ_span]; trivial
      induction hv using Submodule.span_induction with
      | mem v hv => exact hlat v hv
      | zero =>
        have h0 : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ (0 : Fin r → E) = (0 : ℂ) • _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ 0 := by
          funext k; simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb]
        rw [h0, Matrix.mulVec_smul, _root_.ReciprocityTheory.ChartRestriction.G.FD.hC_smul_right, _root_.ReciprocityTheory.ChartRestriction.G.FD.hC_smul_right]
        simp
      | add v w _ _ h1 h2 =>
        rw [emb_add, Matrix.mulVec_add, _root_.ReciprocityTheory.ChartRestriction.G.FD.hC_add_right, _root_.ReciprocityTheory.ChartRestriction.G.FD.hC_add_right, h1, h2, mul_add]
      | smul e v _ h =>
        rw [emb_smul, Matrix.mulVec_smul, _root_.ReciprocityTheory.ChartRestriction.G.FD.hC_smul_right, _root_.ReciprocityTheory.ChartRestriction.G.FD.hC_smul_right, h]
        ring
    have hC : ∀ z : Fin r → ℂ,
        _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ X'.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.col (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x' ⟨τ, hτ'⟩) ⟨0, hr⟩)
          ((a : Matrix (Fin r) (Fin r) E).map τ *ᵥ z) =
        A σ (X.p0 - 1) (X.p0 - 1) *
          _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.col (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x ⟨τ, hτ⟩) ⟨0, hr⟩) z := by
      intro z
      rw [pi_eq_sum_univ z, Matrix.mulVec_sum, _root_.ReciprocityTheory.ChartRestriction.G.FD.IsotropicIndexSums.hC_sum_right, _root_.ReciprocityTheory.ChartRestriction.G.FD.IsotropicIndexSums.hC_sum_right, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Matrix.mulVec_smul, _root_.ReciprocityTheory.ChartRestriction.G.FD.hC_smul_right, _root_.ReciprocityTheory.ChartRestriction.G.FD.hC_smul_right]
      have h := hE (Pi.single k 1)
      have hs : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ (Pi.single k (1 : E)) = fun j => if k = j then (1 : ℂ) else 0 := by
        funext j
        by_cases hkj : k = j
        · subst hkj; simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb]
        · simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb, Pi.single_apply, hkj, Ne.symm hkj]
      rw [hs] at h
      rw [h]
      ring
    obtain ⟨u, hu⟩ : ∃ u, (a : Matrix (Fin r) (Fin r) E).map τ *ᵥ u =
        _root_.ReciprocityTheory.ChartRestriction.G.FD.col (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x' ⟨τ, hτ'⟩) ⟨0, hr⟩ := by
      refine ⟨((a⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ *ᵥ
        _root_.ReciprocityTheory.ChartRestriction.G.FD.col (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x' ⟨τ, hτ'⟩) ⟨0, hr⟩, ?_⟩
      rw [Matrix.mulVec_mulVec, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← map_mul,
        Units.mul_inv, map_one, Matrix.one_mulVec]
    have k1 := hC (_root_.ReciprocityTheory.ChartRestriction.G.FD.col (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x ⟨τ, hτ⟩) ⟨0, hr⟩)
    have k2 := hiso τ u (_root_.ReciprocityTheory.ChartRestriction.G.FD.col (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x ⟨τ, hτ⟩) ⟨0, hr⟩)
    rw [hu] at k2
    have k3 := hC u
    rw [hu] at k3
    have k4 := _root_.ReciprocityTheory.ChartRestriction.G.FD.hC_symm τ X.Gm X.Gm_herm u (_root_.ReciprocityTheory.ChartRestriction.G.FD.col (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x ⟨τ, hτ⟩) ⟨0, hr⟩)
    have k5 : _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ X.Gm u (_root_.ReciprocityTheory.ChartRestriction.G.FD.col (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x ⟨τ, hτ⟩) ⟨0, hr⟩) =
        -(A σ (X.p0 - 1) (X.p0 - 1) * _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.col (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x ⟨τ, hτ⟩) ⟨0, hr⟩)
          (_root_.ReciprocityTheory.ChartRestriction.G.FD.col (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x ⟨τ, hτ⟩) ⟨0, hr⟩)) := by
      linear_combination k2 - k1
    rw [k4, k5] at k3
    have hd := hermC_first_col_self_re_pos X hx ⟨τ, hτ⟩ hp0 hr
    have hd' := hermC_first_col_self_re_pos X' hx' ⟨τ, hτ'⟩ (hp ▸ hp0) hr
    simp only at hd hd'
    rw [k3] at hd'
    simp [Complex.mul_re, Complex.conj_re, Complex.conj_im] at hd'
    nlinarith [Complex.normSq_nonneg (A σ (X.p0 - 1) (X.p0 - 1)), Complex.normSq_apply (A σ (X.p0 - 1) (X.p0 - 1)),
      sq_nonneg (A σ (X.p0 - 1) (X.p0 - 1)).re, sq_nonneg (A σ (X.p0 - 1) (X.p0 - 1)).im]

end GlobalTheory.AntiIsom
end
end

