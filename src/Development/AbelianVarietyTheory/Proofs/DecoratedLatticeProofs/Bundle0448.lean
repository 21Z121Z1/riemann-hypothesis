import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0378
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0427
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0115
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0120
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0167
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0404
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0308
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1451
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0150
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationSplitSupportProjectsVacuum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0380
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0369
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0371
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0373
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0393
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0035
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OffTypePinnedLocalGroups
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0390
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0428
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0046
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0036
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MovedVacuumInvariantUnderSingleSplitPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

noncomputable section
namespace GlobalTheory.AdForm.VacSplit

open Formalism.L2.Th1.H

theorem inter_ne_zero {V : Type} [AddCommGroup V] [Module ℂ V] {H : Sesq V} {α : V → ℂ} {A₁ A₂ : AddSubgroup V} {F : V → ℂ}
    (h : inter H α A₁ A₂ F ≠ 0) : relIdx A₁ A₂ ≠ 0 := by
  intro h0
  apply h
  funext z
  simp [inter, h0]

theorem inter_zero {V : Type} [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (A₁ A₂ : AddSubgroup V) :
    inter H α A₁ A₂ 0 = 0 := by
  funext z
  simp [inter, opU]

theorem inter_const_mul {V : Type} [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (A₁ A₂ : AddSubgroup V)
    (c : ℂ) (F : V → ℂ) (z : V) : inter H α A₁ A₂ (fun w => c * F w) z = c * inter H α A₁ A₂ F z := by
  unfold inter
  have e : ∀ q : A₂ ⧸ A₁.addSubgroupOf A₂, α ((Quotient.out q : A₂) : V) * opU H ((Quotient.out q : A₂) : V) (fun w => c * F w) z =
      c * (α ((Quotient.out q : A₂) : V) * opU H ((Quotient.out q : A₂) : V) F z) := fun q => by
    simp only [opU]; ring
  simp only [e]
  rw [← mul_finsum]
  ring

theorem mem_LamC_toHom {D : D7} (S T : HSp D) {a b : ℕ} (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ)
    (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E))
    (z : VCx D.what₂.Tau a b) (hz : z ∈ LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') :
    ∃ γ, z = embH (tauE D) δ (toHom S T hS hT γ) := by
  obtain ⟨x, -, rfl⟩ := hz
  refine ⟨(LinearMap.toMatrix' x).reindex (finCongr hT).symm (finCongr hS).symm, ?_⟩
  congr 1
  subst hS hT
  simp [toHom]

end GlobalTheory.AdForm.VacSplit

namespace GlobalTheory.AdForm.VacSplit

open GlobalTheory.ThetaMove Formalism.L2.Th1.H

set_option maxHeartbeats 1600000 in

theorem moveT_split : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) ψ θ, IsStdChar (I.rec7 l Z) ψ (-1) → IsInfFam θ → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) vac, IsVacO ψ θ ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) (fun _ => 1) (fun _ => 1) (intVec _ _) (intVec _ _) vac → ∀ (a : I.ι) μ om, ChrEq μ (I.C.mu0 ⟨i, hi⟩ * I.xi a) → IsWeilDatumO ψ _ _ μ μ om → ∀ c₀ g h, g ∈ GfC _ → h ∈ GfC _ → GlobalTheory.AdForm.VacAll.MoveT I l Z θ i hi c₀ μ om vac (g) (h) → ∀ e, IsSplitIdem (I.rec7 l Z) e → ∀ s s', SuppAt e _ s → SuppAt e _ s' → GlobalTheory.AdForm.VacAll.MoveT I l Z θ i hi c₀ μ om vac (s * g) (s' * h) := by
  intro B X I hI hP l Z ψ θ hψ hθ i hi vac0 hvac _a μ om _hμ hW c₀ g h hg hh hmv e he s s' hs hs'
  intro N₁ N₁' hN₁ hN₁' x₁ y₁ hx₁ hy₁
  have hi0 : i ≤ B.R.m := Nat.le_of_succ_le hi
  obtain ⟨hstdAll, -, hemb, -, hroot⟩ := GlobalTheory.AdForm.StdStepsT.stdPair_steps_all I hI hP l Z ψ θ hψ hθ
  have hstd := hstdAll i hi
  have hAA : I.A.AA = ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E) := I.A_AA
  have hSr := rankN (I.rec7 l Z) i hi0
  have hTr := rankN (I.rec7 l Z) (i + 1) hi
  obtain ⟨N, hN⟩ := (GlobalTheory.T.adelicTranslate_standardLattice_isSelfDual _ _ _ hSr hstd.gS).1 g
  obtain ⟨N', hN'⟩ := (GlobalTheory.T.adelicTranslate_standardLattice_isSelfDual _ _ _ hTr hstd.gT).1 h
  obtain ⟨x, hx⟩ := hroot _ g
  obtain ⟨y, hy⟩ := hroot _ h
  have key := hmv N N' hN hN' x y hx hy
  have hsG : s ∈ GfC _ := GlobalTheory.WeilProduct.mem_GfC_of_suppAt he hs
  have hs'G : s' ∈ GfC _ := GlobalTheory.WeilProduct.mem_GfC_of_suppAt he hs'
  have xv := fun g₀ (hg₀ : g₀ ∈ GfC _) h₀ (hh₀ : h₀ ∈ GfC _) M M' (hM : Moves _ hSr g₀ M) (hM' : Moves _ hTr h₀ M') =>
    GlobalTheory.T.movedWeilVacuum_eq_vacuum_of_movedLattices (I.rec7 l Z) ψ θ _ _ _ _ hSr hTr I.A.δ I.A.sc hstd (μ) (om) hW (vac0) hvac g₀ hg₀ h₀ hh₀ M M' hM hM'

  have hX := GlobalTheory.Mem.FieldsLaws.fields_ok B
  have hcc : Formalism.MainNotions.TaylorLogMetric.IsCurveIdeal (I.rec7 l Z) ⊤ := ⟨top_ne_bot, by simp⟩
  have hδ := ((I.J.ok_iff B (I.cols l) Z.W Z.V Z.S Z.N Z.G).1 hI.amb_ok).1
  have hχ := GlobalTheory.Mem.ChiIdeal.isChi_chiId (I.rec7 l Z) I.C.chiPsi I.C.isChi
  have hE := (GlobalTheory.Core.Ht2.family_laws I hI hX l Z).1
  have hfam := GlobalTheory.NatFamily.family (I.rec7 l Z) ⊤ I.J.δ (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G) I.chi hcc hδ hχ
  have ha : Even (B.R.N i) := hSr ▸ hstd.rk.2.2.1
  have hb : Even (B.R.N (i + 1)) := hTr ▸ hstd.rk.2.2.2
  have hMv : GlobalTheory.ThetaMove.Moves I.A (B.R.N i) (B.R.N (i + 1)) := by
    show GlobalTheory.ThetaMove.Moves (I.J.amb B I.chi) _ _
    rw [AmbIn.amb_eq_ambOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G]
    exact GlobalTheory.ThetaMove.SeamMoves.moves_ambOf B.fields _ (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) ⊤ I.J.δ
      (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G) I.chi I.J.cD _ _ hX (seamOf_ok B (I.cols l) Z.W Z.V Z.S Z.N Z.G) hcc hχ hE
      hfam.2.1 (hfam.2.2 _ _) ha hb
  have hemb' : B.fields.embC I.A.σ₀ = tauE (I.rec7 l Z) := funext hemb
  have hlam : ∀ M M', lam I.A (a := B.R.N i) (b := B.R.N (i + 1)) M M' =
      LamC (tauE (I.rec7 l Z)) I.A.δ ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E) M M' := by
    intro M M'
    show LamC (B.fields.embC I.A.σ₀) I.A.δ I.A.AA M M' = _
    rw [hemb', hAA]
    rfl
  have hvacT : ∀ M M', Formalism.L2.Col.IsSdLat M → Formalism.L2.Col.IsSdLat M' →
      vac I.A (a := B.R.N i) (b := B.R.N (i + 1)) M M' = I.J.V.thMoved (B.R.N i) (B.R.N (i + 1)) M M' := by
    intro M M' hM hM'
    funext z
    exact inv_mul_cancel_left₀ (hMv.2.2.2.2.1 M M' hM hM').1 _
  obtain ⟨hNsd, ΛS, hcS, hΛS⟩ := (GlobalTheory.T.adelicTranslate_standardLattice_isSelfDual _ _ _ hSr hstd.gS).2 g N hN
  obtain ⟨hN'sd, ΛT, hcT, hΛT⟩ := (GlobalTheory.T.adelicTranslate_standardLattice_isSelfDual _ _ _ hTr hstd.gT).2 h N' hN'
  obtain ⟨hN₁sd, ΛS₁, hcS₁, hΛS₁⟩ := (GlobalTheory.T.adelicTranslate_standardLattice_isSelfDual _ _ _ hSr hstd.gS).2 (s * g) N₁ hN₁
  obtain ⟨hN₁'sd, ΛT₁, hcT₁, hΛT₁⟩ := (GlobalTheory.T.adelicTranslate_standardLattice_isSelfDual _ _ _ hTr hstd.gT).2 (s' * h) N₁' hN₁'
  have v0 := xv g hg h hh N N' hN hN'
  have v1 := xv (s * g) (mul_mem hsG hg) h hh N₁ N' hN₁ hN'
  have v2 := xv (s * g) (mul_mem hsG hg) (s' * h) (mul_mem hs'G hh) N₁ N₁' hN₁ hN₁'
  have hc1 : om (s, 1) (om (g, h) (vac0)) = om (s * g, h) (vac0) := by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]
  have hc2 : om (1, s') (om (s * g, h) (vac0)) = om (s * g, s' * h) (vac0) := by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]
  have hth0 : I.J.V.thMoved (B.R.N i) (B.R.N (i + 1)) N N' ≠ 0 := by
    intro h0
    apply v0.2.2
    refine key.trans (funext fun z => ?_)
    show _ = (0 : ℂ)
    rw [h0, Pi.zero_apply, mul_zero]
  have hv1 : I.J.V.thMoved (B.R.N i) (B.R.N (i + 1)) N₁ N' ≠ 0 := by
    intro h0
    apply hth0
    rw [← hvacT N N' hNsd hN'sd, hMv.2.2.2.2.2.2 N₁ N N' hN₁sd hNsd hN'sd, hvacT N₁ N' hN₁sd hN'sd, h0, inter_zero]
  have hv2 : I.J.V.thMoved (B.R.N i) (B.R.N (i + 1)) N₁ N₁' ≠ 0 := by
    intro h0
    apply hv1
    rw [← hvacT N₁ N' hN₁sd hN'sd, hMv.2.2.2.2.2.1 N₁ N₁' N' hN₁sd hN₁'sd hN'sd, hvacT N₁ N₁' hN₁sd hN₁'sd, h0, inter_zero]
  have hrel1 : relIdx (lam I.A (a := B.R.N i) (b := B.R.N (i + 1)) N N') (lam I.A N₁ N') ≠ 0 := by
    apply inter_ne_zero (H := HV I.A.sc) (α := alV I.A.d I.A.sc) (F := vac I.A (a := B.R.N i) (b := B.R.N (i + 1)) N N')
    rw [← hMv.2.2.2.2.2.2 N N₁ N' hNsd hN₁sd hN'sd, hvacT N₁ N' hN₁sd hN'sd]
    exact hv1
  have hrel2 : relIdx (lam I.A (a := B.R.N i) (b := B.R.N (i + 1)) N₁ N') (lam I.A N₁ N₁') ≠ 0 := by
    apply inter_ne_zero (H := HV I.A.sc) (α := alV I.A.d I.A.sc) (F := vac I.A (a := B.R.N i) (b := B.R.N (i + 1)) N₁ N')
    rw [← hMv.2.2.2.2.2.1 N₁ N' N₁' hN₁sd hN'sd hN₁'sd, hvacT N₁ N₁' hN₁sd hN₁'sd]
    exact hv2
  rw [hlam N N', hlam N₁ N'] at hrel1
  rw [hlam N₁ N', hlam N₁ N₁'] at hrel2
  have hfacts : ∀ (M : Submodule (𝓞 (I.rec7 l Z).host.E) (Fin (B.R.N i) → (I.rec7 l Z).host.E)) (M' : Submodule (𝓞 (I.rec7 l Z).host.E) (Fin (B.R.N (i + 1)) → (I.rec7 l Z).host.E)), Formalism.L2.Col.IsSdLat M → Formalism.L2.Col.IsSdLat M' →
      IsSelfDual (HV I.A.sc) (LamC (tauE (I.rec7 l Z)) I.A.δ ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E) M M') ∧
      IsSemiChar (HV I.A.sc) (LamC (tauE (I.rec7 l Z)) I.A.δ ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E) M M')
        (alV (I.rec7 l Z).host.d I.A.sc) := by
    intro M M' hM hM'
    have := (hMv.2.2.2.2.1 M M' hM hM').2.2
    rw [← hlam M M']
    exact this
  haveI : Nonempty (I.rec7 l Z).what₂.Tau := Fintype.card_pos_iff.1 hX.f_pos
  have hinj := GlobalTheory.ThetaMove.embH_injective (a := B.R.N i) (b := B.R.N (i + 1)) (tauE (I.rec7 l Z)) hstd.ne
  have memL : ∀ (M : Submodule (𝓞 (I.rec7 l Z).host.E) (Fin (B.R.N i) → (I.rec7 l Z).host.E)) (M' : Submodule (𝓞 (I.rec7 l Z).host.E) (Fin (B.R.N (i + 1)) → (I.rec7 l Z).host.E)) x, embH (tauE (I.rec7 l Z)) I.A.δ x ∈
      LamC (tauE (I.rec7 l Z)) I.A.δ ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E) M M' ↔
      x ∈ perO ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E) M M' := by
    intro M M' x
    exact ⟨fun ⟨y, hy, e⟩ => hinj e ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩
  obtain ⟨x₀, hx₀⟩ := GlobalTheory.AdTh.SplitClass.exists_detAt _ he.1 s
  obtain ⟨y₀, hy₀⟩ := GlobalTheory.AdTh.SplitClass.exists_detAt _ he.1 s'
  have st1 := GlobalTheory.T.splitPlacePair_moves_latticeVacuumReading (I.rec7 l Z) ψ θ _ _ _ _ hSr hTr I.A.δ I.A.sc hstd (μ) (om) hW ΛS ΛS₁ ΛT ΛT hΛS hΛS₁
    hΛT hΛT e he s 1 hs (GlobalTheory.LeviSplitChar.suppAt_one e _) x₀ 1 hx₀ (GlobalTheory.LeviSplitChar.isDetAt_one e _)
    (by rw [hcS, hcS₁, hcT]; exact GlobalTheory.T.homLatticeCompletion_moves_by_translatePair _ _ _ _ _ hSr hTr g s h 1 N N' N₁ N' hN hN' hN₁ (by rwa [one_mul]))
    _ _ (fun γ v hv => by rw [hcS, hcT]; exact (GlobalTheory.T.rationalFinitePart_mem_homLatticeCompletion_iff _ ψ θ _ _ _ _ hSr hTr _ _ hstd ΛS ΛT N N' hcS hcT hΛS hΛT γ v hv).trans (memL N N' _).symm)
    (fun γ v hv => by rw [hcS₁, hcT]; exact (GlobalTheory.T.rationalFinitePart_mem_homLatticeCompletion_iff _ ψ θ _ _ _ _ hSr hTr _ _ hstd ΛS₁ ΛT N₁ N' hcS₁ hcT hΛS₁ hΛT γ v hv).trans (memL N₁ N' _).symm)
    (mem_LamC_toHom _ _ hSr hTr _ N₁ N') (hfacts N₁ N' hN₁sd hN'sd).1 (hfacts N N' hNsd hN'sd).2 (hfacts N₁ N' hN₁sd hN'sd).2 hrel1
    (om (g, h) (vac0)) (by rw [hcS, hcT]; exact v0.1) v0.2.1.2 (by rw [hc1]; exact v1.2.1.2) (by rw [hc1]; exact v1.2.2)
  have mv1 : inter (HV I.A.sc) (alV (I.rec7 l Z).host.d I.A.sc)
      (LamC (tauE (I.rec7 l Z)) I.A.δ ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E) N N')
      (LamC (tauE (I.rec7 l Z)) I.A.δ ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E) N₁ N')
      (I.J.V.thMoved (B.R.N i) (B.R.N (i + 1)) N N') = I.J.V.thMoved (B.R.N i) (B.R.N (i + 1)) N₁ N' := by
    have c7 := hMv.2.2.2.2.2.2 N N₁ N' hNsd hN₁sd hN'sd
    rw [hvacT N N' hNsd hN'sd, hvacT N₁ N' hN₁sd hN'sd, hlam N N', hlam N₁ N'] at c7
    exact c7.symm
  have mv2 : inter (HV I.A.sc) (alV (I.rec7 l Z).host.d I.A.sc)
      (LamC (tauE (I.rec7 l Z)) I.A.δ ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E) N₁ N')
      (LamC (tauE (I.rec7 l Z)) I.A.δ ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E) N₁ N₁')
      (I.J.V.thMoved (B.R.N i) (B.R.N (i + 1)) N₁ N') = I.J.V.thMoved (B.R.N i) (B.R.N (i + 1)) N₁ N₁' := by
    have c6 := hMv.2.2.2.2.2.1 N₁ N' N₁' hN₁sd hN'sd hN₁'sd
    rw [hvacT N₁ N' hN₁sd hN'sd, hvacT N₁ N₁' hN₁sd hN₁'sd, hlam N₁ N', hlam N₁ N₁'] at c6
    exact c6.symm
  have e1 : xiN θ _ _ hSr hTr I.A.δ I.A.sc (om (s * g, h) (vac0)) = fun z =>
      ((μ x₀ : ℂ))⁻¹ * (c₀ * ((μ x : ℂ))⁻¹ * (μ y : ℂ)) * I.J.V.thMoved (B.R.N i) (B.R.N (i + 1)) N₁ N' z := by
    rw [← hc1]
    refine st1.trans (funext fun z => ?_)
    rw [show xiN θ _ _ hSr hTr I.A.δ I.A.sc (om (g, h) (vac0)) = _ from key]
    erw [inter_const_mul]
    erw [mv1]
    simp only [map_one, Circle.coe_one, mul_one]
    ring
  have st2 := GlobalTheory.T.splitPlacePair_moves_latticeVacuumReading (I.rec7 l Z) ψ θ _ _ _ _ hSr hTr I.A.δ I.A.sc hstd (μ) (om) hW ΛS₁ ΛS₁ ΛT ΛT₁ hΛS₁ hΛS₁
    hΛT hΛT₁ e he 1 s' (GlobalTheory.LeviSplitChar.suppAt_one e _) hs' 1 y₀ (GlobalTheory.LeviSplitChar.isDetAt_one e _) hy₀
    (by rw [hcS₁, hcT, hcT₁]; exact GlobalTheory.T.homLatticeCompletion_moves_by_translatePair _ _ _ _ _ hSr hTr (s * g) 1 h s' N₁ N' N₁ N₁' hN₁ hN' (by rwa [one_mul]) hN₁')
    _ _ (fun γ v hv => by rw [hcS₁, hcT]; exact (GlobalTheory.T.rationalFinitePart_mem_homLatticeCompletion_iff _ ψ θ _ _ _ _ hSr hTr _ _ hstd ΛS₁ ΛT N₁ N' hcS₁ hcT hΛS₁ hΛT γ v hv).trans (memL N₁ N' _).symm)
    (fun γ v hv => by rw [hcS₁, hcT₁]; exact (GlobalTheory.T.rationalFinitePart_mem_homLatticeCompletion_iff _ ψ θ _ _ _ _ hSr hTr _ _ hstd ΛS₁ ΛT₁ N₁ N₁' hcS₁ hcT₁ hΛS₁ hΛT₁ γ v hv).trans (memL N₁ N₁' _).symm)
    (mem_LamC_toHom _ _ hSr hTr _ N₁ N₁') (hfacts N₁ N₁' hN₁sd hN₁'sd).1 (hfacts N₁ N' hN₁sd hN'sd).2
    (hfacts N₁ N₁' hN₁sd hN₁'sd).2 hrel2
    (om (s * g, h) (vac0)) (by rw [hcS₁, hcT]; exact v1.1) v1.2.1.2 (by rw [hc2]; exact v2.2.1.2) (by rw [hc2]; exact v2.2.2)
  have rx := GlobalTheory.T.splitPlace_detRootChar_mul _ _ (μ) _ hstd.rk.2.2.1 hW.resS e he s g hs x₀ x x₁ hx₀ hx hx₁
  have ry := GlobalTheory.T.splitPlace_detRootChar_mul _ _ (μ) _ hstd.rk.2.2.2 hW.resT e he s' h hs' y₀ y y₁ hy₀ hy hy₁
  rw [← hc2]
  refine st2.trans (funext fun z => ?_)
  rw [e1]
  erw [inter_const_mul]
  erw [mv2]
  rw [rx, ry]
  simp only [map_one, Circle.coe_one, inv_one, one_mul, Circle.coe_mul, mul_inv]
  ring

end GlobalTheory.AdForm.VacSplit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormLastValuationNeOfRankZero
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.MiStar.normLast_valuation : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : GlobalTheory.FinPl.SplitPt D k) (q : GlobalTheory.LatPair.Unif k) (S A L : HSp D) (o : OrthDec S A L), 0 < S.rank → S.gram = 1 → ∀ (ζ : Fin L.rank → D.host.E) (π : D.host.E), (∀ r : Fin S.rank, vecB o ζ r = if r.1 + 1 = S.rank then π else 0) → valuation k (p.pr (incA D π)) = valuation k ((q.1 : 𝒪[k]) : k) → valuation k (p.pr (incA D (star π))) = 1 → valuation k (p.pr (incA D (star ζ ⬝ᵥ L.gram *ᵥ ζ))) = valuation k ((q.1 : 𝒪[k]) : k) := by
  intro D k _ _ _ _ p q S A L o hpos hS ζ π hv h1 h2
  have key : star ζ ⬝ᵥ L.gram *ᵥ ζ = star π * π := by
    have hB := o.isoB
    rw [hS, Matrix.mul_one] at hB
    rw [← hB, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
    have hfun : o.iB *ᵥ ζ = fun r : Fin S.rank => if r.1 + 1 = S.rank then π else 0 := by
      funext r; exact hv r
    rw [hfun]
    let r0 : Fin S.rank := ⟨S.rank - 1, by omega⟩
    have hr : ∀ r : Fin S.rank, (r.1 + 1 = S.rank) ↔ r = r0 := by
      intro r; constructor
      · intro h; ext; simp [r0]; omega
      · intro h; subst h; simp [r0]; omega
    simp only [dotProduct, Pi.star_apply, hr]
    simp [apply_ite star]
  rw [key, map_mul, map_mul, map_mul, h2, h1, one_mul]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OffTypePinnedLocalGroupsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.off_type_pinned_local_groups : ∀ (D : D7) (u : D.what₂.Word) (F₀ : ∀ u, Formalism.L2.Forms.Forms0 D u) (S : STrue D F₀) (d : GlobalTheory.SeeSaw.Dat D u) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : GlobalTheory.FinPl.OffDat d k ι) (G : ∀ PP : d.c.Pg, GlobalTheory.LocMod.GAt d o.τ PP.1) (h0 : 0 + 2 * D.R.rS + 2 = D.R.m), GlobalTheory.Core.Mi.IdE S.X → d.Base → IsTypePlaces d.c.Pg → GlobalTheory.FinPl.PinOff o → GlobalTheory.LocMod.PinGBy G o.cG → (∀ z, z ∈ (d.x 0).L ↔ z ∈ (F₀ u).cls0.lev.Lb.map ((LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)))).toLinearMap.restrictScalars (𝓞 D.host.E))) → LevX (F₀ u) d h0 → ∀ (B : SBes S.X S.inst u d.c.ψ (D.sp.X 0)), B.lev = d.B 0 D.R.rS h0 → B.Adapted (S.tr u).wt → ∀ a₀ : GA D (D.sp.X 0), IsTransportAdelicCorrection (S.tr u) a₀ → ∀ a ∈ GfC (D.sp.X 0), a ∈ Subgroup.center (GA D (D.sp.X 0)) → (∀ κ : GA D (D.sp.Y 0), (κ ∈ GfC (D.sp.Y 0) ∧ finE (D.sp.Y 0) κ ∈ St (finE (D.sp.Y 0) (((iotaX S.X S.inst).symm (1, S.X.xu u))⁻¹ * embA B.d B.o (a₀ * a) * (show GA D (D.sp.Y 0) from d.t 0)) * d.bot.β)) ↔ ((iotaX S.X S.inst κ).1 = 1 ∧ (iotaX S.X S.inst κ).2 ∈ S.X.B.I.Kset)) → ∀ (hr : D.R.r ≤ (D.sp.Y 0).rank) (κ : GA D (D.sp.Y 0)), κ ∈ GfC (D.sp.Y 0) → finE (D.sp.Y 0) κ ∈ St (finE (D.sp.Y 0) (((iotaX S.X S.inst).symm (1, S.X.xu u))⁻¹ * embA B.d B.o (a₀ * a) * (show GA D (D.sp.Y 0) from d.t 0)) * d.bot.β) → ((iotaX S.X S.inst κ).2 ∈ S.X.K2 ↔ (fun PP : d.c.Pg => upperLeftBlock hr (redFn (finE (D.sp.Y 0) (((iotaX S.X S.inst).symm (1, S.X.xu u))⁻¹ * embA B.d B.o (a₀ * a) * (show GA D (D.sp.Y 0) from d.t 0)) * d.bot.β) PP.1 (finE (D.sp.Y 0) κ))) ∈ d.c.P.H) := by
  first | exact @GlobalTheory.Core.Mi.memMatch | exact GlobalTheory.Core.Mi.memMatch | (intros; apply GlobalTheory.Core.Mi.memMatch <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrthogonalEmbeddingKeepsGluedCoreIffFixesPair
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LatMatch.StabPair

open GlobalTheory.FinPl.FrameLat

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mt_sec_any (p : SplitPt D k) {S : HSp D} (h : GA D S) (y : Fin S.rank → k) :
    Formalism.L2.Theta.mt S h *ᵥ (fun i => p.sec (y i)) = fun i => p.sec ((((Formalism.L2.Theta.mt S h).map p.pr) *ᵥ y) i) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, map_sum, Matrix.map_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sec_mul, p.sec_pr, mul_comm p.e, mul_assoc, e_mul_sec]

theorem col_mulVec {m : Type} [Fintype m] (Y : m → k) (t : Fin 1 → k) :
    Matrix.replicateCol (Fin 1) Y *ᵥ t = t 0 • Y := by
  funext i
  simp [Matrix.mulVec, dotProduct, Matrix.replicateCol, mul_comm]

theorem vec_emb {p : SplitPt D k} {S A L : HSp D} (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) {n : Type} [Fintype n]
    [DecidableEq n] {β : GlobalTheory.FinPl.Frame p A n} {β₀ : GlobalTheory.FinPl.Frame p S (n ⊕ Fin 1)} (hs : IsSumFrame o ζ β β₀)
    (g : GL n k) (x : n ⊕ Fin 1 → k) :
    (Formalism.L2.Theta.mt S (o.emb (β.gl g, 1))).map p.pr *ᵥ (β₀.b *ᵥ x) =
      β₀.b *ᵥ Sum.elim (g.val *ᵥ (x ∘ Sum.inl)) (x ∘ Sum.inr) := by
  have hA : (Formalism.L2.Theta.mt S (o.emb (β.gl g, 1))).map p.pr * o.jA.map p.pr = o.jA.map p.pr * (β.b * g.val * β.b') := by
    rw [← Matrix.map_mul, o.emb_jA, Matrix.map_mul, β.gl_mat]
  have hB : (Formalism.L2.Theta.mt S (o.emb (β.gl g, 1))).map p.pr * o.jB.map p.pr = o.jB.map p.pr := by
    rw [← Matrix.map_mul, o.emb_jB]
    simp
  have hz : (fun i => p.pr (ratV (vecB o ζ) i)) = o.jB.map p.pr *ᵥ (fun j => p.pr (incA D (ζ j))) := by
    funext i
    simp [ratV, vecB, Matrix.mulVec, dotProduct, OrthDec.jB, rat]
  have hY : (Formalism.L2.Theta.mt S (o.emb (β.gl g, 1))).map p.pr *ᵥ (fun i => p.pr (ratV (vecB o ζ) i)) =
      (fun i => p.pr (ratV (vecB o ζ) i)) := by
    rw [hz, Matrix.mulVec_mulVec, hB]
  rw [hs, Matrix.fromCols_mulVec, Matrix.fromCols_mulVec, col_mulVec, col_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul, hY,
    Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hA]
  have e : o.jA.map p.pr * (β.b * g.val * β.b') * β.b = (o.jA.map p.pr * β.b) * g.val := by
    simp only [Matrix.mul_assoc, β.b'b, Matrix.mul_one]
  rw [e, ← Matrix.mulVec_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr]

theorem mem_glued_iff {p : SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n]
    {β₀ : GlobalTheory.FinPl.Frame p S (n ⊕ Fin 1)} {M : Lat S} {q : GlobalTheory.LatPair.Unif k} {m : k} {P : GlobalTheory.LatPair.Pair k n}
    (hG : GluedW β₀ M q m P) (x : n ⊕ Fin 1 → k) :
    (fun i => p.sec ((β₀.b *ᵥ x) i)) ∈ latV S M (· = p.v) ↔
      ∃ s : 𝒪[k], x ∘ Sum.inl - s • P.vec ∈ P.ker ∧ m * x (Sum.inr 0) = q.inv * s := by
  rw [hG x, GlobalTheory.LevelUnfold.mem_gluedS, Sum.elim_comp_inl]
  refine exists_congr fun s => and_congr_right fun _ => ?_
  simp [Fin.forall_fin_one]

theorem glued_stab {n : Type} [Fintype n] [DecidableEq n] {q : GlobalTheory.LatPair.Unif k} {m : k} {P : GlobalTheory.LatPair.Pair k n}
    {g : GL n k} (hP : g • P = P) {u : n → k} {t : k}
    (h : ∃ s : 𝒪[k], u - s • P.vec ∈ P.ker ∧ m * t = q.inv * s) :
    ∃ s : 𝒪[k], g.val *ᵥ u - s • P.vec ∈ P.ker ∧ m * t = q.inv * s := by
  obtain ⟨hk, hv⟩ := (GlobalTheory.LatPair.Pair.smul_eq_iff P.hasVal_vec).1 hP
  obtain ⟨s, h1, h2⟩ := h
  refine ⟨s, ?_, h2⟩
  have h3 : g • (u - s • P.vec) ∈ P.ker := hk ▸ Submodule.smul_mem_pointwise_smul _ g _ h1
  have e : g.val *ᵥ u - s • P.vec = g • (u - s • P.vec) + s • (g • P.vec - P.vec) := by
    rw [smul_sub, smul_sub, smul_comm g s]
    change _ = g • u - _ + _
    change _ = g.val *ᵥ u - _ + _
    abel
  rw [e]
  exact add_mem h3 (P.ker.smul_mem s hv)

theorem glued_zero {n : Type} [Fintype n] [DecidableEq n] {q : GlobalTheory.LatPair.Unif k} {m : k} {P : GlobalTheory.LatPair.Pair k n}
    (u : n → k) : (∃ s : 𝒪[k], u - s • P.vec ∈ P.ker ∧ m * 0 = q.inv * s) ↔ u ∈ P.ker := by
  constructor
  · rintro ⟨s, h1, h2⟩
    have hs : (s : k) = 0 := by
      rw [mul_zero, eq_comm, mul_eq_zero] at h2
      exact h2.resolve_left (inv_ne_zero q.ne_zero)
    have hs' : s = 0 := Subtype.ext hs
    simpa [hs'] using h1
  · intro h
    exact ⟨0, by simpa using h, by simp⟩

end GlobalTheory.Core.Mi.LatMatch.StabPair

open GlobalTheory.Core.Mi.LatMatch.StabPair in

theorem GlobalTheory.Core.Mi.LatMatch.moves_emb_iff_smul_eq : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S A L : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (n : Type) [Fintype n] [DecidableEq n] (β : GlobalTheory.FinPl.Frame p A n) (β₀ : GlobalTheory.FinPl.Frame p S (n ⊕ Fin 1)) (M : Lat S) (q : GlobalTheory.LatPair.Unif k) (m : k) (P : GlobalTheory.LatPair.Pair k n), IsSumFrame o ζ β β₀ → IsSelfDualC S M → m ≠ 0 → GluedW β₀ M q m P → ∀ g : GL n k, Moves S (o.emb (β.gl g, 1)) M M (· = p.v) ↔ g • P = P := by
  intro D k _ _ _ _ p S A L o ζ n _ _ β β₀ M q m P hs hM hm hG g
  have hE : ∀ x : n ⊕ Fin 1 → k, Formalism.L2.Theta.mt S (o.emb (β.gl g, 1)) *ᵥ (fun i => p.sec ((β₀.b *ᵥ x) i)) =
      fun i => p.sec ((β₀.b *ᵥ Sum.elim (g.val *ᵥ (x ∘ Sum.inl)) (x ∘ Sum.inr)) i) := fun x => by
    rw [mt_sec_any, vec_emb o ζ hs]
  constructor
  · intro hmov
    have hGG : ∀ (u : n → k) (t : k), (∃ s : 𝒪[k], u - s • P.vec ∈ P.ker ∧ m * t = q.inv * s) ↔
        ∃ s : 𝒪[k], g.val *ᵥ u - s • P.vec ∈ P.ker ∧ m * t = q.inv * s := fun u t => by
      have := hmov (fun i => p.sec ((β₀.b *ᵥ Sum.elim u fun _ => t) i)) (fun i => GlobalTheory.FinPl.FrameLat.sec_mem_idAt p _)
      rw [hE, mem_glued_iff hG, mem_glued_iff hG] at this
      simpa only [Sum.elim_comp_inl, Sum.elim_comp_inr, Sum.elim_inr, Function.comp_apply] using this
    rw [GlobalTheory.LatPair.Pair.smul_eq_iff P.hasVal_vec]
    have hker : ∀ u, u ∈ P.ker ↔ g.val *ᵥ u ∈ P.ker := fun u => by
      rw [← glued_zero (q := q) (m := m), ← glued_zero (q := q) (m := m), hGG]
    refine ⟨?_, ?_⟩
    · ext y
      rw [GlobalTheory.LatPair.mem_smul_iff, hker]
      change g.val *ᵥ ((g⁻¹ : GL n k).val *ᵥ y) ∈ P.ker ↔ _
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    · have h1 : ∃ s : 𝒪[k], P.vec - s • P.vec ∈ P.ker ∧ m * (m⁻¹ * q.inv) = q.inv * s :=
        ⟨1, by simp, by rw [← mul_assoc, mul_inv_cancel₀ hm, one_mul]; simp⟩
      obtain ⟨s, h2, h3⟩ := (hGG _ _).1 h1
      have hq : q.inv ≠ 0 := inv_ne_zero q.ne_zero
      have hs : (s : k) = 1 := by
        rw [← mul_assoc, mul_inv_cancel₀ hm, one_mul] at h3
        exact mul_left_cancel₀ hq (h3.symm.trans (mul_one _).symm)
      have hs' : s = 1 := Subtype.ext hs
      change g.val *ᵥ P.vec - P.vec ∈ P.ker
      simpa [hs'] using h2
  · intro hP
    refine (sMoves_one _ _ _ _).1 (GlobalTheory.T.normOneHomothety_carries_selfDual_of_splitComponent D k p S M M 1 _ hM hM (normOneAt_one _) fun x => ?_)
    rw [map_one, one_smul]
    obtain ⟨y, rfl⟩ : ∃ y, x = β₀.b *ᵥ y := ⟨β₀.b' *ᵥ x, by rw [Matrix.mulVec_mulVec, β₀.bb', Matrix.one_mulVec]⟩
    rw [vec_emb o ζ hs, mem_glued_iff hG, mem_glued_iff hG]
    simp only [Sum.elim_comp_inl, Sum.elim_inr, Function.comp_apply]
    refine ⟨glued_stab hP, fun h => ?_⟩
    have := glued_stab (inv_smul_eq_iff.2 hP.symm) h
    rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrthogonalEmbeddingSplitPlaceBlockDiagonalStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
open GlobalTheory.RootEx (embX)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthogonalEmbedding_splitPlace_blockDiagonal : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n : Type) [Fintype n] [DecidableEq n] (σ : ℕ) (B : BesLev D σ) (β : Frame p B.A n) (β₀ : Frame p B.V₀ (n ⊕ Fin 1)), IsSumFrame B.o B.ζ β β₀ → ∀ g : GL n k, B.o.emb (β.gl g, 1) = β₀.gl (embX 1 g) := by
  first | exact @GlobalTheory.FinPl.emb_gl_sumFrame | exact GlobalTheory.FinPl.emb_gl_sumFrame | (intros; apply GlobalTheory.FinPl.emb_gl_sumFrame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ParahoricTestFunctionIntegralAdelicReduction
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.AdForm ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FunObj.Comparison₂ (IsRed Compat IsIx)

namespace GlobalTheory.QTw.LocFn

section Red

variable {S F K : Type} [CommRing S] [CommRing F] [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {φ : S →+* F} {ψ : S →+* K}

theorem parPhi_eq_of_equiv (h : IsRed φ ψ) {R : Type} [Fintype R] [DecidableEq R] {r t j j' a b : ℕ} (f : Fin r ≃ R)
    {ea : Ix R (Fin t) j ≃ Fin a} {eb : Ix R (Fin t) j' ≃ Fin b}
    (ha : IsIx ((Equiv.sumCongr f (Equiv.refl (Fin j × Fin t))).trans ea))
    (hb : IsIx ((Equiv.sumCongr f (Equiv.refl (Fin j' × Fin t))).trans eb))
    {c : Fˣ →* ℂˣ} {δ : Kˣ →* ℂˣ} (hc : Compat φ ψ c δ⁻¹) (N : Matrix (Fin b) (Fin a) S) :
    parPhi δ ((N.map ψ).submatrix eb ea) =
      if H : LowZero r (N.map φ) ∧ IsUnit (topL r (N.map φ)).det then (c H.2.unit : ℂ) else 0 := by
  have e1 : (topL r (N.map φ)).det = ((N.submatrix eb ea).toBlocks₁₁.map φ).det := by
    rw [GlobalTheory.FunObj.Comparison₂.topL_r ha hb, ← det_submatrix_equiv_self f]
    rfl
  have e2 : LowZero r (N.map φ) ↔ MaxM ((N.map ψ).submatrix eb ea).toBlocks₂₁ :=
    (GlobalTheory.FunObj.Comparison₂.lowZero_r h ha hb N).trans
      ⟨fun H i l => by
        obtain ⟨l, rfl⟩ := f.surjective l
        exact H i l, fun H i l => H i (f l)⟩
  split_ifs with H
  · obtain ⟨g, hg, e⟩ := (h.isUnit_det_iff _).1 (e1 ▸ H.2)
    rw [parPhi_of_mem (x := (N.map ψ).submatrix eb ea) _ hg e (e2.1 H.1) (fun _ _ => h.int _) (fun _ _ => h.int _),
      hc.det (k := Matrix.GeneralLinearGroup.det g) _ (H.2.unit_spec.trans e1) (congrArg Matrix.det e),
      MonoidHom.inv_apply]
  · by_contra h0
    obtain ⟨h1, h2, -⟩ := (parPhi_ne_zero_iff _).1 h0
    exact H ⟨e2.2 h2, e1 ▸ (h.isUnit_det_iff _).2 h1⟩

theorem tame_congr {δ : Kˣ →* ℂˣ} (hδ : IsTame δ) {x y : Kˣ} (hx : valuation K (x : K) = 1)
    (h : valuation K ((x : K) - y) < 1) : δ y = δ x := by
  rw [← mul_inv_eq_one, ← map_inv, ← map_mul]
  refine hδ _ ?_
  rwa [Units.val_mul, Units.val_inv_eq_inv_val, ← mul_inv_cancel₀ x.ne_zero, ← sub_mul, map_mul, map_inv₀, hx, inv_one,
    mul_one, Valuation.map_sub_swap]

end Red

theorem isIx_of_isOrd {κ l r t j a : ℕ} (h : κ + l = r) {e : Ix (Fin κ ⊕ Fin l) (Fin t) j ≃ Fin a}
    (he : GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e) :
    IsIx ((Equiv.sumCongr (finSumFinEquiv.trans (finCongr h)).symm (Equiv.refl (Fin j × Fin t))).trans e) := by
  refine ⟨?_, fun i => ?_, fun c s => ?_⟩
  · simpa [h] using (Fintype.card_congr e).symm
  · obtain ⟨i, rfl⟩ := (finSumFinEquiv.trans (finCongr h)).surjective i
    rw [Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Equiv.symm_apply_apply, he]
    rcases i with i | i <;> rfl
  · refine (he (.inr (c, s))).trans ?_
    change κ + l + c.val * t + s.val = _
    rw [h, mul_comm]; omega

theorem parPhi_component : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (PP : Formalism.L2.DIV.Pl D.host.E) (π' : EAf D →+* k), (∀ a, π' (toEAf D a) = q.pr a) → GlobalTheory.FunObj.Comparison₂.IsRed (Formalism.L2.DIV.resS D.host.F PP) (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) → ∀ (δ : kˣ →* ℂˣ), IsTame δ → ∀ (ξ : (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), (∀ (z : 𝓞 D.host.E) (x : kˣ) (u : (Formalism.L2.DIV.kP PP)ˣ), (x : k) = (ofSplit q).pr (z : D.host.E) → (u : Formalism.L2.DIV.kP PP) = Ideal.Quotient.mk PP.asIdeal z → δ x = (ξ u)⁻¹) → ∀ (κ l r t j j' a b : ℕ), r = κ + l → ∀ (ea : Ix (Fin κ ⊕ Fin l) (Fin t) j ≃ Fin a) (eb : Ix (Fin κ ⊕ Fin l) (Fin t) j' ≃ Fin b), GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos ea → GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos eb → ∀ N : Matrix (Fin b) (Fin a) (Formalism.L2.Herm.intAf D.host.F D.host.E), parPhi δ ((N.map (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype)).submatrix eb ea) = if H : LowZero r (N.map (Formalism.L2.DIV.resS D.host.F PP)) ∧ IsUnit (topL r (N.map (Formalism.L2.DIV.resS D.host.F PP))).det then ((ξ H.2.unit : ℂˣ) : ℂ) else 0 := by
  intro D k _ _ _ _ q PP π' hπ hred δ hδ ξ hξ κ l r t j j' a b hr ea eb ha hb N
  refine parPhi_eq_of_equiv hred _ (isIx_of_isOrd hr.symm ha) (isIx_of_isOrd hr.symm hb) (fun s u x hu hx => ?_) N
  obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (u : Formalism.L2.DIV.kP PP)
  have h1 : (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) (Formalism.L2.DIV.oToS D.host.F D.host.E z) =
      (ofSplit q).pr (z : D.host.E) := hπ (incA D (z : D.host.E))
  have h2 : valuation k ((x : k) - (ofSplit q).pr (z : D.host.E)) < 1 := by
    rw [hx, ← h1, ← RingHom.map_sub, ← hred.ker, RingHom.map_sub, Formalism.L2.DIV.resS_oToS, sub_eq_zero]
    exact (hz.trans hu).symm
  have h3 : valuation k (x : k) = 1 := by
    rw [hx]; exact (hred.isUnit_iff s).1 (hu ▸ u.isUnit)
  have h4 : (ofSplit q).pr (z : D.host.E) ≠ 0 := fun h => by
    rw [h, sub_zero, h3] at h2
    exact lt_irrefl _ h2
  rw [MonoidHom.inv_apply, ← tame_congr hδ (y := Units.mk0 _ h4) h3 h2, hξ z (Units.mk0 _ h4) u rfl hz.symm, inv_inv]

end GlobalTheory.QTw.LocFn

end
end

