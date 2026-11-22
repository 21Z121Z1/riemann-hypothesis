import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0810
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0490
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1702
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3307
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1827
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1805
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0327
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0376
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0155
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumAtPlaceEqLatticeIntertwinerMulDetChar
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0194
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0808
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0554
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0809
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0667
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0252
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0505
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0372
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0533
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0785
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0778
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1771
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0811
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0174
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0273
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0589
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GivenPathRepresentationFiniteStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.given_path_representation_finite : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∃ Pg : GlobalTheory.FlipRun.PolE ch.G →₀ ℂ, ∀ t : T, ∃ z : ℂˣ, z ∈ GlobalTheory.RowClaim.xiVals R.toLevCh t ∧ ∀ Φ : ch.G.Datum, ∃ τg : TotT ch.G (GlobalTheory.FunObj.givenPath t D.R.m), GlobalTheory.FlipRun.RepFin ch.S.B ch.rm t (GlobalTheory.FunObj.givenPath t D.R.m) τg (fun w => (givenStage t w ch.S.B Φ).tensor) ∧ ∀ M : Vol ch.G, M.Is t → ∀ y, TotConv ch.W M _ (GlobalTheory.FlipRun.tensE ch.W _ Pg τg) (GlobalTheory.RowClaim.formTop ch t y) ∧ thetaChi ch.W ch.M ch.ρ Φ (ch.cv.lift t y) = (z : ℂ)⁻¹ • liftT ch.W M _ (GlobalTheory.FlipRun.tensE ch.W _ Pg τg) (GlobalTheory.RowClaim.formTop ch t y) := by
  first | exact @GlobalTheory.FlipStart.start | exact GlobalTheory.FlipStart.start | (intros; apply GlobalTheory.FlipStart.start <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsUnramifiedAtPlaceIdempotentOfUnramifiedOverPla
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.RouteSeesaw GlobalTheory.ChainFr
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.UnrOverPlaceConv

open GlobalTheory.IdemSupport

theorem unramAt_of_unrAt_all : ∀ {D : D7} {χ : (AE D)ˣ →* Circle} {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F},
    IsPlaceIdem D v ε → (∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v → GlobalTheory.LFun.UnrAt χ w) →
    GlobalTheory.WeilParts.UnramAt ε χ := by
  intro D χ v ε hε hu x hx h1 h2
  obtain ⟨w, hw⟩ : ∃ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v := by
    have := v.isMaximal
    obtain ⟨Q, hQ, hl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 D.host.E) v.asIdeal
    exact ⟨⟨Q, hQ.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, HeightOneSpectrum.ext hl.over.symm⟩
  have hΦ : Comp D (GlobalTheory.LFun.EulerTie.finComp D.host.F D.host.E) := by
    obtain ⟨a, b, c, d, e⟩ := (GlobalTheory.LFun.EulerTie.comp_finComp (F := D.host.F) (E := D.host.E))
    exact ⟨a, b, c, d, e⟩
  obtain ⟨e, f, hp⟩ := exists_isPrimeIdem hΦ w
  obtain ⟨-, ε', hε', hf⟩ := of_isPrimeIdem hΦ hp
  rw [hw] at hε'
  have hee : ε = ε' := placeIdem_unique hε hε'
  subst hee
  subst hf
  exact GlobalTheory.UnrPlDict.unrPl_of_unrAt D v w hw χ hu e _ hp x hx h1 h2

end GlobalTheory.UnrOverPlaceConv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftTOppTens
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowVal

section Lin

variable {T : Type} {D : D7} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {M : Vol G}
  {ρ : RealMatch W} {t : T}

theorem rowFam_cusp (hS : GlobalTheory.FlipRun.CuspStep W M ρ t) {e : AE D} (he : IsIdemSum e (locPl G t))
    {F : Fn G (.grid 0 D.R.m)} (hF : GlobalTheory.FlipRun.IsCuspListed W.θ (.grid 0 D.R.m) F) :
    ∀ n, n ≤ D.R.m → ∀ (f : ∀ i : Fin n, Sch G (.right i D.R.m)),
      (∀ i : Fin n, ∃ φ g Q, IsLocVec W (.chi i D.R.m) e (ρ.vX i D.R.m) φ g ∧ f i = W.fock (.chi i D.R.m) g Q) →
      GlobalTheory.FlipRun.IsCuspListed W.θ (.grid n D.R.m) (liftP W M (rowPath T D.R.m n) (rowFam D.R.m n f) F)
  | 0, _, _, _ => hF
  | n + 1, hn, f, hf => by
    obtain ⟨φ, g, Q, hl, e1⟩ := hf (Fin.last n)
    have ih := rowFam_cusp hS he hF n (by omega) (fun i => f i.castSucc) (fun i => hf i.castSucc)
    have h1 := (hS (.right n D.R.m) (Or.inl ⟨n, D.R.m, by omega, le_rfl, rfl⟩) e he φ g hl Q _ ih).2
    show GlobalTheory.FlipRun.IsCuspListed W.θ (.grid (n + 1) D.R.m)
      (liftA W M (.right n D.R.m) (f (Fin.last n)) (liftP W M (rowPath T D.R.m n) (rowFam D.R.m n fun i => f i.castSucc) F))
    rw [e1]
    exact h1

theorem downFam_cusp (hS : GlobalTheory.FlipRun.CuspStep W M ρ t) {e : AE D} (he : IsIdemSum e (locPl G t)) :
    ∀ n, n ≤ D.R.m → ∀ (f : ∀ j : Fin n, Sch G (.down t D.R.m j)),
      (∀ j : Fin n, ∃ φ g Q, IsLocVec W (.mu t D.R.m j) e (ρ.vT D.R.m j) φ g ∧ f j = W.fock (.mu t D.R.m j) g Q) →
      ∀ F : Fn G (.grid D.R.m n), GlobalTheory.FlipRun.IsCuspListed W.θ (.grid D.R.m n) F →
      GlobalTheory.FlipRun.IsCuspListed W.θ (.grid D.R.m 0) (liftP W M (downPath t D.R.m n) (downFam t D.R.m n f) F)
  | 0, _, _, _, _, hF => hF
  | n + 1, hn, f, hf, F, hF => by
    obtain ⟨φ, g, Q, hl, e1⟩ := hf (Fin.last n)
    have h1 := (hS (.down t D.R.m n) (Or.inr ⟨D.R.m, n, le_rfl, by omega, rfl⟩) e he φ g hl Q F hF).2
    have h1' : GlobalTheory.FlipRun.IsCuspListed W.θ (.grid D.R.m n) (liftA W M (.down t D.R.m n) (f (Fin.last n)) F) := by
      rw [e1]; exact h1
    have key : liftP W M (downPath t D.R.m (n + 1)) (downFam t D.R.m (n + 1) f) F =
        liftP W M (downPath t D.R.m n) (downFam t D.R.m n fun j => f j.castSucc)
          (liftA W M (.down t D.R.m n) (f (Fin.last n)) F) :=
      pathLift_comp W M (Path.one (.down t D.R.m n)) ((), f (Fin.last n)) F (downPath t D.R.m n)
        (downFam t D.R.m n fun j => f j.castSucc)
    rw [key]
    exact downFam_cusp hS he n (by omega) (fun j => f j.castSucc) (fun j => hf j.castSucc) _ h1'

theorem opp_contAut (hP : GlobalTheory.Published.CuspRapidDecay) (hθ : IsInfFam W.θ) (hS : GlobalTheory.FlipRun.CuspStep W M ρ t) {e : AE D}
    (he : IsIdemSum e (locPl G t)) {F : Fn G (.grid 0 D.R.m)} (hF : GlobalTheory.FlipRun.IsCuspListed W.θ (.grid 0 D.R.m) F)
    (P : PolRow G × PolDown G) (d φ : SchRow G × SchDown G t)
    (hd : (∀ i : Fin D.R.m, IsLocVec W (.chi i D.R.m) e (ρ.vX i D.R.m) (φ.1 i) (d.1 i)) ∧
      ∀ j : Fin D.R.m, IsLocVec W (.mu t D.R.m j) e (ρ.vT D.R.m j) (φ.2 j) (d.2 j)) :
    GlobalTheory.Unf.IsContAut (G.V (.grid D.R.m 0)) (liftP W M (oppPath t D.R.m) (oppPure W t P d) F) := by
  have hr := rowFam_cusp (M := M) hS he hF D.R.m le_rfl _ fun i => ⟨φ.1 i, d.1 i, P.1 i, hd.1 i, rfl⟩
  have hdn := downFam_cusp hS he D.R.m le_rfl _ (fun j => ⟨φ.2 j, d.2 j, P.2 j, hd.2 j, rfl⟩) _ hr
  have key : liftP W M (oppPath t D.R.m) (oppPure W t P d) F =
      liftP W M (downPath t D.R.m D.R.m) (downFam t D.R.m D.R.m fun j => W.fock (.mu t D.R.m j) (d.2 j) (P.2 j))
        (liftP W M (rowPath T D.R.m D.R.m) (rowFam D.R.m D.R.m fun i => W.fock (.chi i D.R.m) (d.1 i) (P.1 i)) F) :=
    pathLift_comp W M _ _ F _ _
  rw [key]
  have hrd := rapidDec_of_cuspForm hP hθ hdn.1 hdn.2.1
  exact ⟨hrd.1, hrd.2.1⟩

theorem bplus_fsum {M₀ : Vol G} (h₀ : M₀.IsRow) (hM : M.Is t) {φ : Fn G (.top 0)} (hφ : GlobalTheory.Unf.IsContAut _ φ) {I : Type}
    (s : Finset I) (a : I → ℂ) (f : I → Fn G (.grid D.R.m 0)) (hf : ∀ i ∈ s, GlobalTheory.Unf.IsContAut _ (f i)) :
    Bplus W M₀ φ (∑ i ∈ s, a i • f i) = ∑ i ∈ s, a i * Bplus W M₀ φ (f i) := by
  rw [bplus_indep G W M₀ M h₀ hM.isRow φ _ hφ (GlobalTheory.SeeSaw.TrcProof.contAut_sum s a f hf), bplus_eq_per G W t M hM]
  refine ((per_linear_trc D W.ψ W.ψ_std _ (topLev G hM) φ hφ).1 I s a f hf).trans ?_
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [bplus_indep G W M₀ M h₀ hM.isRow φ _ hφ (hf i hi), bplus_eq_per G W t M hM]

theorem liftT_oppTens (τi : PolRow G × PolDown G →₀ ℂ) (τ : SchRow G × SchDown G t →₀ ℂ) (F : Fn G (.grid 0 D.R.m)) :
    liftT W M (oppPath t D.R.m) (oppTens W t τi τ) F =
      ∑ P ∈ τi.support, τi P • ∑ d ∈ τ.support, τ d • liftP W M (oppPath t D.R.m) (oppPure W t P d) F := by
  have e : liftT W M (oppPath t D.R.m) (oppTens W t τi τ) F =
      AddMonoidHom.mk' (fun x => liftT W M (oppPath t D.R.m) x F) (fun x y => liftT_add W M _ x y F) (oppTens W t τi τ) := rfl
  rw [e]
  simp only [oppTens, Finsupp.sum, map_sum, AddMonoidHom.mk'_apply, liftT_single, Finset.smul_sum, smul_smul]

end Lin

theorem linAt_big : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → Big fun ch => LinAt ch := by
  intro hP hL
  obtain ⟨a0, ha⟩ := Big.and (Big.and (GlobalTheory.T.cuspidal_flip_on_volumes hL hP) (GlobalTheory.EndCusp.formTop_isCuspListed hP)) colFn_cont_left
  refine ⟨a0, fun ε CF hC => ?_⟩
  obtain ⟨x, hx⟩ := ha ε CF hC
  refine ⟨x, fun D large₂ he hxx Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch hsc => ?_⟩
  obtain ⟨⟨hstep, htop⟩, hcol⟩ := hx D large₂ he hxx Γ Pl0 T A Ks R F hS ch hch hsc
  have hθ : IsInfFam ch.W.θ := by
    rw [hch.toIsBase.weil.θ]
    exact hS.core.models.inf
  intro t a τ hτ M hM τi y
  obtain ⟨e, he', φ, hφ, -⟩ := hτ
  have hca : GlobalTheory.Unf.IsContAut _ (colFn ch a) := ⟨(hcol a).2, (hcol a).1⟩
  have hFP : ∀ P : PolRow ch.G × PolDown ch.G, GlobalTheory.Unf.IsContAut _
      (∑ d ∈ τ.support, τ d • liftP ch.W M (oppPath t D.R.m) (oppPure ch.W t P d) (formTop ch t y)) := fun P =>
    GlobalTheory.SeeSaw.TrcProof.contAut_sum _ _ _ fun d hd =>
      opp_contAut hP.cuspRapidDecay hθ (hstep t M hM) he' (htop t y) P d (φ d) (hφ d hd)
  simp only [lhs, liftT_oppTens]
  rw [bplus_fsum hch.toIsBase.vol hM hca _ _ _ fun P _ => hFP P, Finsupp.sum]
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton, Finsupp.single_eq_same, one_smul]

end GlobalTheory.RowVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsDoublingFrameStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matched_maps_doubling_frame : GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7) (W W₁ X : HSp D) (e : Fin (W.rank + W₁.rank) ≃ Fin X.rank) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
    (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank) (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps D.host.F W.rank W₁.rank) (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps D.host.F W.rank W₁.rank),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
    ∀ (hJ : Γ.W.J = D.host.xi0 • (X.gramᵀ).submatrix e e), ∀ g ∈ GfC X,
    ∃ hv : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl D.host.F → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Γ.W.J,
      (∀ v, hv v ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt D.sp.cm.sig Γ.W (GlobalTheory.AdelicU.evFin D.host.F v)) ∧
      (∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin W.rank × Fin (W.rank + W₁.rank)))
        (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl D.host.F, (Fin W.rank × Fin (W.rank + W₁.rank) → Fv D.host.F v) → ℂ),
        (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = Γ.M.vac v) →
        ∃ φ₁ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl D.host.F, (Fin W.rank × Fin (W.rank + W₁.rank) → Fv D.host.F v) → ℂ,
          (∀ v, φ₁ v ∈ GlobalTheory.WeilM.SB _) ∧ (∀ᶠ v in Filter.cofinite, φ₁ v = Γ.M.vac v) ∧
          (∀ v, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin D.host.F v) (om (1, hv v)) (φ v) (φ₁ v)) ∧
          om (1, GlobalTheory.TripleRead.toUX X e hJ g) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ₁) ∧
      ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin W₁.rank × Fin (W.rank + W₁.rank)))
        (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl D.host.F, (Fin W₁.rank × Fin (W.rank + W₁.rank) → Fv D.host.F v) → ℂ),
        (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = Γ.M'.vac v) →
        ∃ φ₁ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl D.host.F, (Fin W₁.rank × Fin (W.rank + W₁.rank) → Fv D.host.F v) → ℂ,
          (∀ v, φ₁ v ∈ GlobalTheory.WeilM.SB _) ∧ (∀ᶠ v in Filter.cofinite, φ₁ v = Γ.M'.vac v) ∧
          (∀ v, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin D.host.F v) (om' (1, hv v)) (φ v) (φ₁ v)) ∧
          om' (1, GlobalTheory.TripleRead.toUX X e hJ g) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ₁ := by
  first | exact @GlobalTheory.PlacePureFin.placePure | exact GlobalTheory.PlacePureFin.placePure | (intros; apply GlobalTheory.PlacePureFin.placePure <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalFormBottom
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.RowEx.BotField

theorem field_of_gens {T Hh κ : Type} [Finite T] (v : T → Hh → κ → ℂ) (good : Set Hh)
    (hab : ∃ (H : Finset Hh) (K : Finset κ) (M₀ : IntermediateField ℚ ℂ), FiniteDimensional ℚ M₀ ∧ (∀ h ∈ H, h ∈ good) ∧
      ∀ t, ∀ h ∈ good, ∀ k, ∃ c : Hh → κ → ℂ, (∀ a b, c a b ∈ M₀) ∧ v t h k = ∑ h' ∈ H, ∑ k' ∈ K, c h' k' * v t h' k')
    (hc : ∃ Ω : ℂ, Ω ≠ 0 ∧ ∀ t, ∀ h ∈ good, ∀ k, IsAlgebraic ℚ (v t h k / Ω)) :
    ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ ∃ Ω : ℂ, Ω ≠ 0 ∧ ∀ t, ∀ h ∈ good, ∀ k, v t h k / Ω ∈ M := by
  obtain ⟨H, K, M₀, hM₀, hH, hv⟩ := hab
  obtain ⟨Ω, hΩ, halg⟩ := hc
  let S : Set ℂ := Set.range fun x : T × H × K => v x.1 x.2.1 x.2.2 / Ω
  haveI : Finite S := Set.finite_range _ |>.to_subtype
  have hS : ∀ z ∈ S, IsIntegral ℚ z := by
    rintro _ ⟨⟨t, h, k⟩, rfl⟩
    exact (halg t h (hH h h.2) k).isIntegral
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ S) := IntermediateField.finiteDimensional_adjoin hS
  refine ⟨M₀ ⊔ IntermediateField.adjoin ℚ S, inferInstance, Ω, hΩ, fun t h hh k => ?_⟩
  obtain ⟨c, hc, e⟩ := hv t h hh k
  rw [e, Finset.sum_div]
  refine sum_mem fun h' hh' => ?_
  rw [Finset.sum_div]
  refine sum_mem fun k' hk' => ?_
  rw [mul_div_assoc]
  refine mul_mem ((le_sup_left : M₀ ≤ _) (hc h' k')) ((le_sup_right : IntermediateField.adjoin ℚ S ≤ _) ?_)
  exact IntermediateField.subset_adjoin ℚ S ⟨⟨t, ⟨h', hh'⟩, ⟨k', hk'⟩⟩, rfl⟩

theorem sumsIn_bottom (hP : GlobalTheory.FunPr.Hypotheses₂) (hI : ∀ D, GlobalTheory.NormSum.Inp D) {D : D7} {T : Type} [Finite T] {L : LevCh D T}
    {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}
    (hL : L.Is μ₀) (hX : IsBottomTri W i j X) :
    ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ SumsIn W (algebraMap M ℂ) X := by
  obtain ⟨M₁, h₁, Ω, hΩ, e₁⟩ := field_of_gens (fun t h k => X.I W.ψ W.θ t (MvPolynomial.monomial k 1) h)
    (GfC WW : Set (GA D WW)) (GlobalTheory.T.bottom_triangle_algebraicity_finite_data hP hI hL hX) (GlobalTheory.T.bottom_triangle_period_algebraic hP hI hL hX)
  obtain ⟨M₂, h₂, Ω', hΩ', e₂⟩ := field_of_gens (fun t h k => X.I' W.ψ W.θ t (MvPolynomial.monomial k 1) h)
    (GfC WW : Set (GA D WW)) (GlobalTheory.T.bottom_triangle_dual_algebraicity_finite_data hP hI hL hX) (GlobalTheory.T.bottom_triangle_dual_period_algebraic hP hI hL hX)
  refine ⟨M₁ ⊔ M₂, inferInstance, Ω, Ω', hΩ, hΩ', fun t h hh => ⟨fun k _ => ?_, fun k _ => ?_⟩⟩
  · exact ⟨⟨_, (le_sup_left : M₁ ≤ _) (e₁ t h hh k)⟩, rfl⟩
  · exact ⟨⟨_, (le_sup_right : M₂ ≤ _) (e₂ t h hh k)⟩, rfl⟩

theorem sumsIn_mono {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {A A' WW : HSp D}
    {X : Tri T A A' WW} {K K' : Type} [Field K] [Field K'] {σ : K →+* ℂ} {σ' : K' →+* ℂ} (h : SumsIn W σ X)
    (hσ : Set.range σ ⊆ Set.range σ') : SumsIn W σ' X := by
  obtain ⟨Ω, Ω', h0, h0', H⟩ := h
  exact ⟨Ω, Ω', h0, h0', fun t g hg => ⟨fun k hk => hσ ((H t g hg).1 k hk), fun k hk => hσ ((H t g hg).2 k hk)⟩⟩

end GlobalTheory.RowEx.BotField

theorem GlobalTheory.RowEx.nfBot_holds : GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → NFBot := by
  intro hP hI
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch _ _ => ?_⟩⟩
  haveI : Finite T := hS.fin
  have hL : R.toLevCh.Is A.μ0 := hS.core.lev
  have hex : ∀ ij : Fin D.R.m × Fin D.R.m, ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧
      ∃ (A₁ A₂ WW : HSp D) (X : Tri T A₁ A₂ WW), IsBottomTri ch.W ij.1 ij.2 X ∧ SumsIn ch.W (algebraMap M ℂ) X := by
    intro ij
    obtain ⟨A₁, A₂, WW, X, hX⟩ := exists_bottomTri hL ch.G ch.W ij.1 ij.2
    obtain ⟨M, hM, hs⟩ := GlobalTheory.RowEx.BotField.sumsIn_bottom hP hI hL hX
    exact ⟨M, hM, A₁, A₂, WW, X, hX, hs⟩
  choose M hM hB using hex
  haveI := hM
  refine ⟨⨆ ij, M ij, IntermediateField.finiteDimensional_iSup_of_finite, fun i j => ?_⟩
  obtain ⟨A₁, A₂, WW, X, hX, hs⟩ := hB (i, j)
  refine ⟨A₁, A₂, WW, X, hX, GlobalTheory.RowEx.BotField.sumsIn_mono hs ?_⟩
  rintro _ ⟨z, rfl⟩
  exact ⟨⟨z, (le_iSup M (i, j) : M (i, j) ≤ _) z.2⟩, rfl⟩

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotDvdDifferentIdealOfStandardAddCharUnramified
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.RouteSeesaw GlobalTheory.ChainFr
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.PsiDifferent

open GlobalTheory.Idele WithZero
open scoped nonZeroDivisors
open GlobalTheory.StdDual (codiff codiff_ne_zero)

theorem not_dvd_different_of_psiUnr : ∀ {F : Type} [Field F] [NumberField F] {ψ : AddChar (AF F) ℂ},
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → ∀ {v : HeightOneSpectrum (𝓞 F)}, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PsiUnr ψ v →
    ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 F) := by
  intro F _ _ ψ hψ v hU hdvd
  have h0 : differentIdeal ℤ (𝓞 F) ≠ 0 := differentIdeal_ne_bot
  have hD : ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) = (codiff F)⁻¹ :=
    coeIdeal_differentIdeal ℤ ℚ F (𝓞 F)
  have hcnt := FractionalIdeal.count_coe F v h0
  rw [hD, FractionalIdeal.count_inv] at hcnt
  have hne := (Associates.count_ne_zero_iff_dvd h0 v.irreducible).2 hdvd
  set c := FractionalIdeal.count F v (codiff F) with hc
  have hc1 : c ≤ -1 := by omega
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  set x : Fv F v := algebraMap F (Fv F v) (π ^ c) with hx
  have hval : Valued.v x = WithZero.exp (-c) := by
    rw [hx, valued_algebraMap, map_zpow₀, hπ, ← WithZero.exp_zsmul, smul_eq_mul]
    congr 1; ring
  have hmem : GlobalTheory.AdelicU.singleFin v x ∈ adelicIdeal (codiff F) := by
    refine (mem_adelicIdeal_iff codiff_ne_zero).2 fun u => ?_
    by_cases hu : u = v
    · subst hu
      rw [show (GlobalTheory.AdelicU.singleFin u x) u = x from GlobalTheory.AdelicU.evalV_singleFin_self u x, hval]
    · rw [show (GlobalTheory.AdelicU.singleFin v x) u = 0 from GlobalTheory.AdelicU.evalV_singleFin_ne hu x, map_zero]
      exact zero_le'
  rw [GlobalTheory.SplitUnram.mem_adelicIdeal_codiff_iff hψ.1 (GlobalTheory.PsiNontriv.isStd_fin_rat hψ)] at hmem
  have hint : x ∈ v.adicCompletionIntegers F := by
    refine (hU x).1 fun y hy => ?_
    have hα : ∀ u, (GlobalTheory.AdelicU.singleFin v y) u ∈ u.adicCompletionIntegers F := by
      intro u
      by_cases hu : u = v
      · subst hu
        rw [show (GlobalTheory.AdelicU.singleFin u y) u = y from GlobalTheory.AdelicU.evalV_singleFin_self u y]
        exact hy
      · rw [show (GlobalTheory.AdelicU.singleFin v y) u = 0 from GlobalTheory.AdelicU.evalV_singleFin_ne hu y]
        exact zero_mem _
    have e : GlobalTheory.AdelicU.singleFin v y * GlobalTheory.AdelicU.singleFin v x = GlobalTheory.AdelicU.singleFin v (x * y) := by
      apply GlobalTheory.AdelicU.af_ext
      intro u
      by_cases hu : u = v
      · subst hu
        rw [map_mul, GlobalTheory.AdelicU.evalV_singleFin_self, GlobalTheory.AdelicU.evalV_singleFin_self,
          GlobalTheory.AdelicU.evalV_singleFin_self, mul_comm]
      · rw [map_mul, GlobalTheory.AdelicU.evalV_singleFin_ne hu, GlobalTheory.AdelicU.evalV_singleFin_ne hu,
          GlobalTheory.AdelicU.evalV_singleFin_ne hu, mul_zero]
    have := hmem _ hα
    rw [e] at this
    exact this
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, hval, ← WithZero.exp_zero, WithZero.exp_le_exp] at hint
  omega

end GlobalTheory.PsiDifferent

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawUnfoldingNormalizedStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kapX_finite_action_mem_of_isStabW : GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ N, GlobalTheory.CoinvKer.IsStabW om Bs.emb (algD Γ.M Bs.ψ Bs.emb) N → ∀ g ∈ GfC X, ∀ ΦD ∈ N, om (1, kapX X e hO.JX g) ΦD ∈ N := by
  first | exact @GlobalTheory.StabFinAdelic.stab_kapX_of_isStabW | exact GlobalTheory.StabFinAdelic.stab_kapX_of_isStabW | (intros; apply GlobalTheory.StabFinAdelic.stab_kapX_of_isStabW <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TripleGeometryHermitianFormStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.triple_geometry_hermitian_form : GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7) (X : HSp D) (a a' : ℕ) (e : Fin X.rank ≃ Fin (a + a'))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' → ∀ (hJ : Γ.W.J = D.host.xi0 • reindex e e X.gramᵀ)
    (N' : Submodule ℂ ((Fin a' × Fin (a + a') → AF D.host.F) → ℂ)),
    IsThetaSubG Γ.M' Bs.ψ Bs.emb om' N' → ∀ g ∈ GfC X, ∀ Φ ∈ N', om' (1, kapX X e hJ g) Φ ∈ N' := by
  first | exact @GlobalTheory.StabFinAdelic.stab_kapX_of_isThetaSubG | exact GlobalTheory.StabFinAdelic.stab_kapX_of_isThetaSubG | (intros; apply GlobalTheory.StabFinAdelic.stab_kapX_of_isThetaSubG <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnramifiedPlacesVacuumFixedStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_places_vacuum_fixed : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' →
    ∃ S₀ : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F), ∀ v ∉ S₀,
      (∀ k ∈ GlobalTheory.InertSph.KAt σ G.V v,
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om (k, 1)) (G.M.vac v) (G.M.vac v)) ∧
      ∀ k ∈ GlobalTheory.InertSph.KAt σ G.V' v,
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om' (k, 1)) (G.M'.vac v) (G.M'.vac v) := by
  first | exact @GlobalTheory.LatStabVac.vacuum_fixed_off_finite | exact GlobalTheory.LatStabVac.vacuum_fixed_off_finite | (intros; apply GlobalTheory.LatStabVac.vacuum_fixed_off_finite <;> assumption)
end

