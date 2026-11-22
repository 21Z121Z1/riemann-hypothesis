import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0014
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0027
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.Bundle0001
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0008
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0450
import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0469
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0538
import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocGen
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0475
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0468
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0506
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0241
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MarkedIsometryHalf
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0084

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueChainsKernelDatumSourceSideLattice
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000

namespace GlobalTheory.KerLatS

theorem charts_read_step {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (hPins : TC.Pins B X) (l : I.Laws)
    (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (him : i < B.R.m) :
    ∃ (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch)
      (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1)
        (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))), I.ReadsK l Z u a i hi chOf K := by
  classical
  rcases Nat.eq_zero_or_pos i with rfl | h1
  · exact GlobalTheory.T.exists_charts_reading_step_zero I hOk hPins l Z u a
  · obtain ⟨Ch0, _, chOf0, K0, hK0, -⟩ := GlobalTheory.T.exists_memberStep_charts I hOk hPins l Z u i hi
    obtain ⟨Ch, _, chOf, K, -, hK, -⟩ := GlobalTheory.T.tupleChain_middleStage_charts_joined_member I hOk hPins l Z u a ((I.Q a).image fun P => P.under (𝓞 B.host.F)) i hi
      Ch0 chOf0 K0 h1 him (fun v => Finset.mem_image) hK0
    exact ⟨_, Ch, chOf, K, hK⟩

theorem kerEntHyp_latS : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (Pl : Examples₂.EntPl (I.rec7 l Z)) (Bs : PlaceMatrixFamily (I.rec7 l Z)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → BasOk Pl O Bs → (∀ u a w, LevFree Y u a w → ∀ i, i ≤ B.R.m → ∀ c τ j k, ∃ x : (I.rec7 l Z).what₂.LL, Bs u a w i c τ j k = Pl.iL w x) → (∀ u a i, i < B.R.m → UnfIsAll (O u a) i) → ColIn.JetsIn I → ∀ u μ w, LevFree Y u μ w → ∀ i, i < (I.rec7 l Z).R.m → ∀ φ : ((I.rec7 l Z).chTw u μ).cls i → ((I.rec7 l Z).chTw u μ).Y i → ℂ, (∃ x ∈ locW (I.rec7 l Z).what₂.places w (((I.tw l l0 Z).fm u μ).lat i).L, ((I.tw l l0 Z).fm u μ).emb i x = φ) ↔ (φ ∈ ((I.tw l l0 Z).fm u μ).Fi i ∧ ∀ c, ∃ v : ValQ O u μ i, evC O u μ i v = φ c ∧ ∀ J : KM.ColChoice ((I.rec7 l Z).R.N i) (nuD (I.rec7 l Z) u i), ‖prSC Pl O Bs u μ w i c v (MvPolynomial.map (Int.castRingHom _) (KM.nablaX ((I.rec7 l Z).R.N i) (nuD (I.rec7 l Z) u i) J))‖ ≤ 1) := by
  intro B X I hOk hPins l Z l0 Y O Pl Bs hQp hStd hBas hEnt _hUnf _hJets u μ w hw i hi φ
  obtain ⟨bad, Ch, chOf, K, hK⟩ := charts_read_step I hOk hPins l Z u μ i hi.le hi
  have hY : I.IdY l Z u μ i hi.le (Equiv.refl _) := fun _ => rfl
  have V := GlobalTheory.T.hermitianChart_complex_rational_integral_forms I hOk hPins l Z u μ i hi.le bad Ch chOf K (Equiv.refl _) hK hY
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hrat := (V.rat ((I.fm l u μ).emb i x)).1 ⟨x, rfl⟩
    have hlat := (V.lat w trivial x).1 hx
    refine ⟨hrat.1, fun c => ?_⟩
    obtain ⟨Bm, hBm⟩ := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB.exists_isLocBasis ((I.rec7 l Z).what₂.places.resChar w) _ _
      ((I.stp u μ i).rep c).1.1.deco.2.lat.fg ((I.stp u μ i).rep c).1.1.deco.2.lat.span_eq_top
    have hBm' := (GlobalTheory.T.dualLattice_localBasis_iff_unimodularCompanion I hOk hPins l Z Y u μ w hw i hi.le c Bm).2 hBm
    exact (GlobalTheory.T.formsLattice_atClass_iff_twistedPolynomial I hOk hPins l Z Y O Pl Bs hQp hStd hBas hEnt u μ w hw i hi (Equiv.refl _) hY c _ (hrat.2 c) Bm
      hBm).1 (hlat c Bm hBm')
  · rintro ⟨hFi, hc⟩
    have hrat : ∀ c, ∃ P ∈ Formalism.L2.Forms.RatSpan (I.rec7 l Z) ((I.fm l u μ).lam i), ∀ z, φ c z =
        fnOf (gramC (gramN (I.rec7 l Z) i hi.le) (embT (I.rec7 l Z))) (shiftOf (lamTG (I.fm l u μ) i)) 1 P
          ((Equiv.refl _) z) := by
      intro c
      obtain ⟨v, hv, -⟩ := hc c
      rw [← hv]
      exact GlobalTheory.T.complexValue_det_shift_mul_ratSpan I hOk hPins l Z Y O hQp hStd u μ i hi (Equiv.refl _) hY v
    obtain ⟨x, hx⟩ := (V.rat φ).2 ⟨hFi, hrat⟩
    refine ⟨x, (V.lat w trivial x).2 fun c Bm hBm => ?_, hx⟩
    have hBm' := (GlobalTheory.T.dualLattice_localBasis_iff_unimodularCompanion I hOk hPins l Z Y u μ w hw i hi.le c Bm).1 hBm
    have h1 := (GlobalTheory.T.formsLattice_atClass_iff_twistedPolynomial I hOk hPins l Z Y O Pl Bs hQp hStd hBas hEnt u μ w hw i hi (Equiv.refl _) hY c _ (hrat c) Bm
      hBm').2 (hc c)
    rw [hx]
    exact h1

end GlobalTheory.KerLatS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitCOfCXiAt
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.Datum
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

theorem GlobalTheory.OneMapTuples.unitC_of_cXiAt : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (V : HSp D) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n r : ℕ) (d : DeltaDat Xo c n) (hr : V.rank = r) (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)), GlobalTheory.Member.IotaOK Dw V io → 1 ≤ Dw.p + Dw.q → ∀ (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ), (∀ τ : D.host.E →+* ℂ, τ (H.rt : D.host.E) = H.rt0 → ReciprocityTheory.ChartRestriction.G.FD.gram τ (-(Matrix.reindex (finCongr hr) (finCongr hr) V.gram).transpose) (x₀ τ) = Matrix.diagonal fun a : Fin r => ((ReciprocityTheory.ChartRestriction.G.FD.sgn Dw.q (a : ℕ) : ℝ) : ℂ)) → d.IsLev → d.l₂.A = 1 → ∀ (xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ) (N : ℕ), 0 < N → (∀ h : GA D V, xi (Matrix.GeneralLinearGroup.det (finHom V h)) ^ N = 1) → ∀ (U₂ : Unf d.Xo₂ d.c₂ (c.F.val.toRingHom.comp (d.eF.symm : d.c₂.F →+* c.F)) r) (dict₂ : GA D V → Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame (U₂.X k).Ψ r) (c0 : ℂ), c0 ^ N = 1 → GlobalTheory.OneMapAll.CXiAt V hr c.F.val.toRingHom d U₂ dict₂ io x₀ xi c0 → GlobalTheory.Dict.UnitC d := by
  intro D H Dw V l Xo c n r d hr io hι hpq x₀ hx₀ hd hA xi N hN hxN U dict c0 hc0 hv A y
  subst hr
  obtain ⟨hU, hW, g₀, e₀, F, ik, φ, th, hth, hD, hval⟩ := hv
  obtain ⟨-, -, -, -, -, -, -, hsec, -⟩ := hd
  have hc0' : c0 ≠ 0 := by rintro rfl; rw [zero_pow hN.ne'] at hc0; exact zero_ne_one hc0
  have hσ : GoodEmb d.c₂ (c.F.val.toRingHom.comp (d.eF.symm : d.c₂.F →+* c.F)) := rfl
  have val₀ : ∀ h : GA D V, ∃ hx : (dict h).2 ∈ (U.X (dict h).1).dom,
      toC (evR d.Xo₂ d.c₂ d.cδ (U.un _ ⟨_, hx⟩)) ^ N = 1 := by
    intro h
    obtain ⟨γ, hγ, hΛ, hm, -⟩ := hD.2 h
    have hv := hval h γ ⟨hγ, hΛ, hm⟩
    obtain ⟨hx, ex⟩ := GlobalTheory.ShortMove.rdU_eq U d.cδ _ _ (hv ▸ mul_ne_zero hc0' (Units.ne_zero _))
    refine ⟨hx, ?_⟩
    rw [ex.symm.trans hv, mul_pow, hc0, ← Units.val_pow_eq_pow_val, hxN, Units.val_one, one_mul]
  choose hdom val₀ using val₀
  have hx : ∀ k, IsOrthogonalFrame (U.X k) x₀ := fun k τ hτ => by
    rw [(hW k).1, (hU.2.1 k).1]
    exact hx₀ τ (((hU.2.1 k).2 τ).1 hτ)
  have hroot : ∀ z : FrPt d.Xo₂ d.c₂ (CAt (c.F.val.toRingHom.comp (d.eF.symm : d.c₂.F →+* c.F))),
      evR d.Xo₂ d.c₂ d.cδ z ^ N = 1 := fun z => by
    obtain ⟨h, hh⟩ := GlobalTheory.TwistTie.exists_dict_over V U dict io e₀ F ik φ th x₀ hσ hA hpq hU hW hD hι hth hx hdom z
    rw [GlobalTheory.WeightZeroValue.evR_eq_of_same_point hsec hh]
    exact val₀ h
  have hS : ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeSt := GlobalTheory.firstFiveLaws.1.secBaseChange
  have h1 := GlobalTheory.FiniteOrderRule.pow_eq_one_of_complex (K := d.c₂.F) (fun S _ _ => FrPt d.Xo₂ d.c₂ S)
    (fun φ y z => FrMap φ y z) (GlobalTheory.Frames.algebraic_laws hS _ H Dw d.l₂ d.Xo₂ d.c₂).2.2.1
    (fun S _ _ T _ _ φ y => GlobalTheory.Frames.FramedBaseChange.exists_frMap hS _ H Dw d.l₂ d.Xo₂ d.c₂ S T φ y)
    _ d.cδ hsec.1 N hroot
  have h3 := @GlobalTheory.FiniteOrderRule.evalAt_pow_eq_one d.c₂.F _ (fun S _ _ => FrPt d.Xo₂ d.c₂ S)
    (fun φ y z => FrMap φ y z) d.cδ N h1 ℂ _ A y
    (@GlobalTheory.Frames.allTest_of_secBaseChange hS _ _ _ _ H Dw d.l₂ d.Xo₂ d.c₂ ℂ _ inferInstance A y)
  exact Complex.norm_eq_one_of_pow_eq_one h3 hN.ne'

end
end

