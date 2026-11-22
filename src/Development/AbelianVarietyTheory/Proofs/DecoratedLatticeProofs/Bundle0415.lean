import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0023
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0393
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0145
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0159
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0482
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0283
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0278
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0747
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Formalism.LocalRingCardinality.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0230
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0101
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0114
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0226
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0390

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaTensorRuleTargetOrthogonalSum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.TensorTargetRule

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger

variable {D : D7}

theorem heisO_zero' (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (f : WO S T → ℂ) : heisO ψ S T 0 f = f := by
  funext w
  simp [heisO, symplOH, symplO, hO]

theorem dagger_resT_symm {T A B : HSp D} (d : OrthDec T A B) (S : HSp D) (u : WO S A) (v : WO S B) :
    dagger S T ((d.resT S).symm (u, v)) = (d.resS S).symm (dagger S A u, dagger S B v) := by
  rw [d.resT_symm_apply, d.resS_symm_apply, d.pA_eq, d.pB_eq]
  simp only [dagger, adj_add, adj_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, cancel₂ (gA_mul_giA A),
    cancel₂ (gA_mul_giA B), Matrix.one_mul]

theorem dagger_resS_symm {T A B : HSp D} (d : OrthDec T A B) (S : HSp D) (u : WO A S) (v : WO B S) :
    dagger T S ((d.resS S).symm (u, v)) = (d.resT S).symm (dagger A S u, dagger B S v) := by
  have h := dagger_resT_symm d S (dagger A S u) (dagger B S v)
  rw [dagger_dagger, dagger_dagger] at h
  rw [← h, dagger_dagger]

theorem resT_dagger {T A B : HSp D} (d : OrthDec T A B) (S : HSp D) (y : WO T S) :
    d.resT S (dagger T S y) = (dagger A S (d.resS S y).1, dagger B S (d.resS S y).2) := by
  have h := dagger_resS_symm d S (d.resS S y).1 (d.resS S y).2
  rw [Prod.mk.eta, AddEquiv.symm_apply_apply] at h
  rw [h, AddEquiv.apply_symm_apply]

theorem resS_dagger {T A B : HSp D} (d : OrthDec T A B) (S : HSp D) (x : WO S T) :
    d.resS S (dagger S T x) = (dagger S A (d.resT S x).1, dagger S B (d.resT S x).2) := by
  have h := dagger_resT_symm d S (d.resT S x).1 (d.resT S x).2
  rw [Prod.mk.eta, AddEquiv.symm_apply_apply] at h
  rw [h, AddEquiv.apply_symm_apply]

theorem cj_boxT {T A B : HSp D} (d : OrthDec T A B) (S : HSp D) (fA : WO S A → ℂ) (fB : WO S B → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger T S) (d.boxT S fA fB) = d.boxS S (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger A S) fA) (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger B S) fB) := by
  funext y
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, OrthDec.boxT, OrthDec.boxS, resT_dagger, map_mul]

theorem conjAdjoint_cj {S T : HSp D} (om : Rep S T) (g : GA D S) (h : GA D T) (f : WO S T → ℂ) :
    conjAdjoint om (h, g) (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger T S) f) = GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger T S) (om (g, h) f) :=
  cjEnd_cj (daggerEquiv S T) (om (g, h)) f

theorem cj_mem_span {X Y : Type} (e : Y → X) {s : Set (X → ℂ)} {s' : Set (Y → ℂ)} (h : ∀ g ∈ s, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj e g ∈ s')
    {g : X → ℂ} (hg : g ∈ Submodule.span ℂ s) : GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj e g ∈ Submodule.span ℂ s' := by
  induction hg using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span (h x hx)
  | zero =>
    have e0 : GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj e (0 : X → ℂ) = 0 := by funext y; simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj]
    rw [e0]; exact zero_mem _
  | add x y _ _ hx hy =>
    have e1 : GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj e (x + y) = GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj e x + GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj e y := by funext z; simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj]
    rw [e1]; exact add_mem hx hy
  | smul c x _ hx =>
    have e1 : GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj e (c • x) = starRingEnd ℂ c • GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj e x := by funext z; simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj]
    rw [e1]; exact Submodule.smul_mem _ _ hx

theorem tensorTarget : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (T A B : HSp D) (d : OrthDec T A B) (S : HSp D), GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.TensorTarget ψ d S := by
  intro D ψ hψ T A B d S
  have thd : ∀ (S T : HSp D) (f : WO S T → ℂ), IsThetaFunO ψ T S (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger T S) f) ↔ IsThetaFunO ψ S T f :=
    fun S T => (GlobalTheory.T.hermitianAdjoint_symplectic_action_theta_heisenberg D ψ hψ S T).2.2.1
  have src := GlobalTheory.T.thetaTensorRule_orthogonalSum_source D ψ hψ T A B d S
  have cc : ∀ f : WO S T → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger S T) (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger T S) f) = f := fun f => cj_cj _ _ (dagger_dagger S T) f
  refine
    { box_theta := fun fA fB hA hB => d.isThetaFunO_boxT hA hB
      box_zero := fun fA fB => d.boxT_zero S fA fB
      heis_box := fun fA fB => ⟨fun u => ?_, fun v => ?_⟩
      slice_theta := fun f hf => ⟨fun v => ?_, fun u => ?_⟩
      dense := fun f hf => ?_
      om_box := ?_
      om_slice := ?_ }
  · rw [d.heisO_boxT, AddEquiv.apply_symm_apply, heisO_zero']
  · rw [d.heisO_boxT, AddEquiv.apply_symm_apply, heisO_zero']
  · have h1 := (src.slice_theta (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger T S) f) ((thd S T f).2 hf)).1 (dagger S B v)
    rw [← thd S A]
    convert h1 using 1
    funext u
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, dagger_resS_symm, dagger_dagger]
  · have h1 := (src.slice_theta (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger T S) f) ((thd S T f).2 hf)).2 (dagger S A u)
    rw [← thd S B]
    convert h1 using 1
    funext v
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, dagger_resS_symm, dagger_dagger]
  · intro ε hε
    obtain ⟨g, hg, hgε⟩ := src.dense _ ((thd S T f).2 hf) ε hε
    refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger S T) g, cj_mem_span _ ?_ hg, fun x => ?_⟩
    · rintro _ ⟨f1, f2, h1, h2, rfl⟩
      refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger S A) f1, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger S B) f2, (thd A S f1).2 h1, (thd B S f2).2 h2, ?_⟩
      funext x
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, resS_dagger, map_mul]
    · have h := hgε (dagger S T x)
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, dagger_dagger] at h ⊢
      rw [← Complex.norm_conj, map_sub, Complex.conj_conj]
      exact h
  · intro χS χA χB omT omA omB hT hA hB g a b fA fB hfA hfB
    have key := src.om_box χA χB χS (conjAdjoint omT) (conjAdjoint omA) (conjAdjoint omB)
      (GlobalTheory.T.conj_weil_datum_via_adjoint_exchanged_pair D ψ S T χS (χA * χB) omT hT) (GlobalTheory.T.conj_weil_datum_via_adjoint_exchanged_pair D ψ S A χS χA omA hA)
      (GlobalTheory.T.conj_weil_datum_via_adjoint_exchanged_pair D ψ S B χS χB omB hB) a b g (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger A S) fA) (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger B S) fB)
      ((thd S A fA).2 hfA) ((thd S B fB).2 hfB)
    rw [conjAdjoint_cj, conjAdjoint_cj, ← cj_boxT, ← cj_boxT, conjAdjoint_cj] at key
    have := congrArg (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger S T)) key
    rwa [cc, cc] at this
  · intro χS χA χB omT omA omB hT hA hB g a b f hf v
    have key := src.om_slice χA χB χS (conjAdjoint omT) (conjAdjoint omA) (conjAdjoint omB)
      (GlobalTheory.T.conj_weil_datum_via_adjoint_exchanged_pair D ψ S T χS (χA * χB) omT hT) (GlobalTheory.T.conj_weil_datum_via_adjoint_exchanged_pair D ψ S A χS χA omA hA)
      (GlobalTheory.T.conj_weil_datum_via_adjoint_exchanged_pair D ψ S B χS χB omB hB) a b g (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger T S) f) ((thd S T f).2 hf) (dagger S B v)
    have e1 : (fun u'' => conjAdjoint omB (b, g) (fun v'' => GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger T S) f ((d.resS S).symm (u'', v''))) (dagger S B v)) =
        GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger A S) (fun u' => omB (g, b) (fun v' => f ((d.resT S).symm (u', v'))) v) := by
      funext u''
      have hfun : (fun v'' => GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger T S) f ((d.resS S).symm (u'', v''))) =
          GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger B S) (fun v' => f ((d.resT S).symm (dagger A S u'', v'))) := by
        funext v''
        simp only [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, dagger_resS_symm]
      rw [hfun, conjAdjoint_cj]
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, dagger_dagger]
    obtain ⟨k1, k2⟩ := key
    rw [e1] at k1 k2
    refine ⟨(thd S A _).1 k1, fun u => ?_⟩
    have h := k2 (dagger S A u)
    rw [conjAdjoint_cj, conjAdjoint_cj] at h
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, dagger_resS_symm, dagger_dagger] at h
    exact (starRingEnd ℂ).injective h

end GlobalTheory.TensorTargetRule

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TowerAtPre
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR.Cx
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto.RelInh

variable {D : D7}

theorem mem_S (W : GlobalTheory.Core.Rk.Tower D) (h : W.Pre) (k : Fin 2) (P : Pl D.host.E)
    (hk : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) : P.under (𝓞 D.host.F) ∈ (comOf W).S := by
  classical
  unfold Com.S
  rw [Finset.mem_image]
  rcases GlobalTheory.ConjOverQuad.div_or_conj_div D W.C.P k P hk with h1 | ⟨P', h1, hc⟩
  · exact ⟨P, (h.chars.Pg P).2 ⟨k, h1⟩, rfl⟩
  · refine ⟨P', (h.chars.Pg P').2 ⟨k, h1⟩, ?_⟩
    ext x
    show algebraMap _ _ x ∈ P'.asIdeal ↔ algebraMap _ _ x ∈ P.asIdeal
    rw [hc, Formalism.L2.Col.mem_conjIdeal]
    have : Formalism.L2.Col.cO D.host.E (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x) = algebraMap _ _ x := by
      apply RingOfIntegers.ext
      exact (D.sp.cm.fixed _).2 ⟨x, rfl⟩
    rw [this]

theorem Q_empty (W : GlobalTheory.Core.Rk.Tower D) (h : W.Pre) : W.Q () = ∅ := by
  ext PP
  simp only [Finset.notMem_empty, iff_false]
  intro hP
  have := (h.chars.Q_ram () PP).2 (Or.inl hP)
  rw [h.chars.xi_base] at this
  exact this fun x _ => rfl

theorem com_is (W : GlobalTheory.Core.Rk.Tower D) (h : W.Pre) : (comOf W).Is := by
  have hQ := Q_empty W h
  have hL := h.chars
  have hμ : ∀ j : Fin D.R.m, ChrEq (W.toLevCh.mu () ((j : ℕ) + 1)) (W.C.mu0 j) := fun j => by
    have := GlobalTheory.Mem.TupChar.chrEq_mul (hL.mu0 j) (hL.xi ())
    rw [hL.xi_base, mul_one] at this
    exact this
  refine ⟨h.inf, h.std, ⟨hL.eta.1, GlobalTheory.Mem.TupChar.unramEverywhere hL.eta W.C.isEta.unr, GlobalTheory.HeckeCharacterRestriction.resEta_eta hL, fun τ => ?_, fun j hj => ?_⟩,
    fun j τ => ?_, fun j w hw => ?_, fun j => ⟨_, hμ j, hL.chi j⟩, ?_⟩
  · exact GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ hL.eta
      (GlobalTheory.InnerSteps.hasInfQ_tauE (a := fun _ => 1 / 2) ⟨fun _ => 1, fun _ => by norm_num, W.C.isEta.inf⟩) τ
  · obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    exact ⟨GlobalTheory.HeckeCharacterRestriction.isHecke_mu hL () ⟨i, by omega⟩, GlobalTheory.HeckeCharacterRestriction.resEta_mu hL () ⟨i, by omega⟩⟩
  · have h1 := GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ (hμ j) (GlobalTheory.InnerSteps.hasInfQ_tauE (W.C.isMu0 j).inf) τ
    simp only [Formalism.L2.Host.eExp, Equiv.symm_apply_apply] at h1
    exact h1
  · exact (GlobalTheory.LFun.unrAt_iff_of_chrEq (hμ j) w).2 ((W.C.isMu0 j).unr w fun k hk => hw (mem_S W h k w hk))
  · obtain ⟨e, he, -⟩ := h.vX.2
    rw [hQ] at he
    exact ⟨e, by simp only [Finset.union_empty] at he; exact he⟩

theorem stageY_is (W : GlobalTheory.Core.Rk.Tower D) (h : W.Pre) (j : ℕ) (hj : j < D.R.m) : (stageY W j).Is (comOf W) j := by
  have hQ := Q_empty W h
  have hm : min j D.R.m = j := min_eq_left hj.le
  obtain ⟨c, hc⟩ := h.chars.βY j hj
  have hν : (W.νY j).IsHaarMeasure ∧ IsFundamentalDomain (GQ (Yc D j)) (W.fdY j) (W.νY j) := by
    by_cases h1 : j + 1 < D.R.m
    · exact ⟨(h.νY j h1).1.1, (h.νY j h1).2⟩
    · have : j = D.R.m - 1 := by omega
      subst this
      exact ⟨h.νY'.1.1, h.νY'.2⟩
  refine ⟨?_, D.sp.Y_sig _, fun τ => ?_, ?_, GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ ⟨c, hc⟩, hc.1, ⟨_, hc, fun P hP hN => hP ?_⟩, ⟨r_le_Y j, W.xiR (), ?_⟩, hν.1, hν.2⟩
  · show (D.sp.Y (min j D.R.m)).rank = _
    rw [D.sp.Y_rank _ (min_le_right _ _), hm]
  · show (D.sp.Y (min j D.R.m)).sig τ = _
    rw [D.Y_sigval _ (min_le_right _ _), hm]
  · show parB _ (min j D.R.m) = _
    rw [hm]
  · push_cast at hN
    have := P.isPrime.mem_of_pow_mem _ hN
    rcases P.isPrime.mem_or_mem this with h0 | h0
    · exact mem_S W h 0 P h0
    · exact mem_S W h 1 P h0
  · show Lev.datY _ _ _ _ _ _ (W.Q ()) _ _ _ _ = _
    rw [hQ]; rfl

theorem stepY_is (W : GlobalTheory.Core.Rk.Tower D) (h : W.Pre)
    (hio : Lift.IsChainIo W.CC (D.R.m - 1) W.νY W.fdY (fun k => thetaKO (W.ωY k)) W.ptY W.ItY W.ioY)
    (k : ℕ) (hk : k + 1 < D.R.m) : (stepY W k).Is (k + 1) := by
  have hQ := Q_empty W h
  refine ⟨h.ωY k hk, ⟨W.xiR (), W.vac k, ?_⟩, h.ptY k hk, h.ItY k hk, hio k (by omega)⟩
  have := h.vY k hk; rw [hQ] at this; exact this

end GlobalTheory.ChainOnto.RelInh

namespace GlobalTheory.ChainOnto.RelInh

section Real

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

set_option maxHeartbeats 2000000 in

def towerAt (R : RealDat D A Ks) (t : T) : GlobalTheory.Core.Rk.Tower D where
  toLevCh := GlobalTheory.Core.Rk.TowerModel.levAt R.toLevCh t
  θ := R.θ
  ψ := R.ψ
  MY := R.MY
  MX := R.MX
  νY := R.νY t
  fdY := R.fdY t
  νX := R.νX t
  fdX := R.fdX t
  ωY := R.ωY t
  ωX := R.ωX t
  vac := R.vac
  vacX := R.vacX
  vY := R.vY t
  vX := R.vX t
  ItY := R.ItY
  ItX := R.ItX
  ioY := R.ioY t
  ioX := 0

end Real

end GlobalTheory.ChainOnto.RelInh

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TowerIsChain
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TowerChain

theorem under_mem_S (D : D7) (W : GlobalTheory.Core.Rk.Tower D) (h : W.Is) (k : Fin 2) (P : Pl D.host.E)
    (hk : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) : P.under (𝓞 D.host.F) ∈ (comOf W).S := by
  classical
  unfold Com.S
  rw [Finset.mem_image]
  rcases GlobalTheory.ConjOverQuad.div_or_conj_div D W.C.P k P hk with h1 | ⟨P', h1, hc⟩
  · exact ⟨P, (h.chars.Pg P).2 ⟨k, h1⟩, rfl⟩
  · refine ⟨P', (h.chars.Pg P').2 ⟨k, h1⟩, ?_⟩
    ext x
    show algebraMap _ _ x ∈ P'.asIdeal ↔ algebraMap _ _ x ∈ P.asIdeal
    rw [hc, Formalism.L2.Col.mem_conjIdeal]
    have : Formalism.L2.Col.cO D.host.E (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x) = algebraMap _ _ x := by
      apply RingOfIntegers.ext
      exact (D.sp.cm.fixed _).2 ⟨x, rfl⟩
    rw [this]

theorem com_is (D : D7) (W : GlobalTheory.Core.Rk.Tower D) (h : W.Is) (hQ : W.Q () = ∅) : (comOf W).Is := by
  have hL := h.chars
  have hμ : ∀ j : Fin D.R.m, ChrEq (W.toLevCh.mu () ((j : ℕ) + 1)) (W.C.mu0 j) := fun j => by
    have := GlobalTheory.Mem.TupChar.chrEq_mul (hL.mu0 j) (hL.xi ())
    rw [hL.xi_base, mul_one] at this
    exact this
  refine ⟨h.inf, h.std, ⟨hL.eta.1, GlobalTheory.Mem.TupChar.unramEverywhere hL.eta W.C.isEta.unr, GlobalTheory.HeckeCharacterRestriction.resEta_eta hL, fun τ => ?_, fun j hj => ?_⟩,
    fun j τ => ?_, fun j w hw => ?_, fun j => ⟨_, hμ j, hL.chi j⟩, ?_⟩
  · exact GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ hL.eta
      (GlobalTheory.InnerSteps.hasInfQ_tauE (a := fun _ => 1 / 2) ⟨fun _ => 1, fun _ => by norm_num, W.C.isEta.inf⟩) τ
  · obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    exact ⟨GlobalTheory.HeckeCharacterRestriction.isHecke_mu hL () ⟨i, by omega⟩, GlobalTheory.HeckeCharacterRestriction.resEta_mu hL () ⟨i, by omega⟩⟩
  · have h1 := GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ (hμ j) (GlobalTheory.InnerSteps.hasInfQ_tauE (W.C.isMu0 j).inf) τ
    simp only [Formalism.L2.Host.eExp, Equiv.symm_apply_apply] at h1
    exact h1
  · exact (GlobalTheory.LFun.unrAt_iff_of_chrEq (hμ j) w).2 ((W.C.isMu0 j).unr w fun k hk => hw (under_mem_S D W h k w hk))
  · obtain ⟨e, he, -⟩ := h.vX.2
    rw [hQ] at he
    exact ⟨e, by simp only [Finset.union_empty] at he; exact he⟩

theorem Q_eq_empty (D : D7) (W : GlobalTheory.Core.Rk.Tower D) (h : W.Is) : W.Q () = ∅ := by
  ext PP
  simp only [Finset.notMem_empty, iff_false]
  intro hP
  have := (h.chars.Q_ram () PP).2 (Or.inl hP)
  rw [h.chars.xi_base] at this
  exact this fun x _ => rfl

theorem stages (D : D7) (W : GlobalTheory.Core.Rk.Tower D) (h : W.Is) (hQ : W.Q () = ∅) :
  (∀ j < D.R.m, (stageY W j).Is (comOf W) j) ∧ (stageX W).Is (comOf W) D.R.m := by
  refine ⟨fun j hj => ?_, ?_⟩
  · have hm : min j D.R.m = j := min_eq_left hj.le
    obtain ⟨c, hc⟩ := h.chars.βY j hj
    have hν : (W.νY j).IsHaarMeasure ∧ IsFundamentalDomain (GQ (Yc D j)) (W.fdY j) (W.νY j) := by
      by_cases h1 : j + 1 < D.R.m
      · exact ⟨(h.νY j h1).1.1, (h.νY j h1).2⟩
      · have : j = D.R.m - 1 := by omega
        subst this
        exact ⟨h.νY'.1.1, h.νY'.2⟩
    refine ⟨?_, D.sp.Y_sig _, fun τ => ?_, ?_, GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ ⟨c, hc⟩, hc.1, ⟨_, hc, fun P hP hN => hP ?_⟩, ⟨r_le_Y j, W.xiR (), ?_⟩, hν.1, hν.2⟩
    · show (D.sp.Y (min j D.R.m)).rank = _
      rw [D.sp.Y_rank _ (min_le_right _ _), hm]
    · show (D.sp.Y (min j D.R.m)).sig τ = _
      rw [D.Y_sigval _ (min_le_right _ _), hm]
    · show parB _ (min j D.R.m) = _
      rw [hm]
    · push_cast at hN
      have := P.isPrime.mem_of_pow_mem _ hN
      rcases P.isPrime.mem_or_mem this with h0 | h0
      · exact under_mem_S D W h 0 P h0
      · exact under_mem_S D W h 1 P h0
    · show Lev.datY _ _ _ _ _ _ (W.Q ()) _ _ _ _ = _
      rw [hQ]; rfl
  · obtain ⟨c, hc⟩ := h.chars.βX
    refine ⟨D.sp.X'_rank, D.sp.X'_sig, fun τ => ?_, rfl, GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ ⟨c, hc⟩, hc.1, ⟨_, hc, fun P _ hN => ?_⟩, ⟨r_le_X, W.xiR (), ?_⟩, h.νX.1.1, h.νX.2⟩
    · show D.sp.X'.sig τ = _
      rw [D.X'_posDef τ, D.sp.X'_rank]; simp [sigYD, Ranks.rankY, Ranks.rankX']
    · rw [one_pow, Nat.cast_one] at hN
      exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 hN)
    · show Lev.datY _ _ _ _ _ _ (W.Q ()) _ _ _ _ = _
      rw [hQ]; rfl

theorem tower_isChain (D : D7) (W : GlobalTheory.Core.Rk.Tower D) (h : W.Is) : TowerIsChain W := by
  have hQ := Q_eq_empty D W h
  refine ⟨com_is D W h hQ, (stages D W h hQ).1, (stages D W h hQ).2, fun k hk => ⟨h.ωY k hk, ⟨W.xiR (), W.vac k, ?_⟩, h.ptY k hk, h.ItY k hk, h.ioY k (by omega)⟩, ⟨h.ωX, ⟨W.xiR (), W.vacX, ?_⟩, h.ptX, h.ItX, h.ioX⟩⟩
  · have := h.vY k hk; rw [hQ] at this; exact this
  · have := h.vX; rw [hQ] at this; exact this

end GlobalTheory.TowerChain

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransportCorrectionCarriesColumnLatticeRowTrace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

namespace GlobalTheory.Core.Mi.LatMatch.TraceX

theorem mulVec_mem_ideal {R : Type} [CommRing R] {I : Ideal R} {m n : ℕ} (A : Matrix (Fin m) (Fin n) R) {y : Fin n → R}
    (hy : ∀ i, y i ∈ I) (k : Fin m) : (A *ᵥ y) k ∈ I := by
  simp only [Matrix.mulVec, dotProduct]
  exact Ideal.sum_mem _ fun i _ => I.mul_mem_left _ (hy i)

theorem latV_iff_hatL {D : D7} (S : HSp D) (L : Lat S) (P : GlobalTheory.FinPl.Pl D → Prop) (y : Fin S.rank → AE D)
    (hy : ∀ i, y i ∈ idAt D P) :
    y ∈ latV S L P ↔ (fun i => toEAf D (y i)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) L :=
  ⟨GlobalTheory.LatVHat.latV_mem_hatL D S L P y, GlobalTheory.HatLatV.mem_latV_of_hatL D S L P y hy⟩

theorem hat_reindex {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {m n : ℕ} (hn : m = n)
    (L : Submodule (𝓞 E) (Fin n → E)) (z : Fin m → E ⊗[F] Formalism.L2.Herm.Af F) :
    z ∈ Formalism.L2.Herm.hatL (F := F) (L.map ((LinearEquiv.funCongrLeft E E (finCongr hn)).toLinearMap.restrictScalars (𝓞 E))) ↔
      (fun j => z (Fin.cast hn.symm j)) ∈ Formalism.L2.Herm.hatL (F := F) L := by
  subst hn
  have e : L.map ((LinearEquiv.funCongrLeft E E (finCongr (rfl : m = m))).toLinearMap.restrictScalars (𝓞 E)) = L := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  rw [e]
  rfl

theorem transport (D : D7) (I : AutInst) (ιE : I.E ≃+* D.host.E) (hId : ∀ y, HEq (ιE y) y)
    (hI : I = Formalism.L2.SG.InstExistsPf.instOf D) (hr : (D.sp.Y 0).rank = I.n)
    (ιA : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F ≃+* D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)
    (hrat : ∀ x : I.E, ιA (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) x) =
      Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (ιE x))
    (hint : ∀ a, a ∈ IntAf I.F I.E ↔ ιA a ∈ IntAf D.host.F D.host.E)
    {n : ℕ} (q : Fin n → Fin I.n → I.E) (c : Fin n → GlobalTheory.AdForm.EF D) :
    (∑ i, ιA.symm (c i) • incl I (q i)) ∈ I.Lf ↔
      (∑ i, c i • fun k => Formalism.UG.inclE (F := D.host.F) (Formalism.MainNotions.S.Af D.host.F) (ιE (q i (Fin.cast hr k)))) ∈
        Formalism.L2.Herm.hatL (F := D.host.F) (latS D) := by
  subst hI
  have hid : ∀ y, ιE y = y := fun y => eq_of_heq (hId y)
  have hA : ∀ a, ιA a = a := GlobalTheory.Core.Mi.FinFrame.eq_self_of_rat_of_int (Formalism.L2.SG.InstExistsPf.instOf D).F
    (Formalism.L2.SG.InstExistsPf.instOf D).E ιA.toRingHom
    (fun x => (hrat x).trans (congrArg _ (hid x))) (fun a ha => (hint a).1 ha)
  have hA' : ∀ a, ιA.symm a = a := fun a => (hA _).symm.trans (ιA.apply_symm_apply a)
  simp only [hid, hA']
  have e : latS D = GlobalTheory.PlaceModel.latFrame (Yc D 0) := GlobalTheory.ConjPlaceRed.crdLat_eq_latFrame (D.sp.Y 0)
  rw [e]
  exact (GlobalTheory.ConjPlaceRed.mem_Lf D _).symm

theorem fin_emb {D : D7} {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) (w : Fin A.rank → AE D) :
    (fun k => toEAf D ((d.j0 *ᵥ (o.jA *ᵥ w)) k)) =
      ∑ i, toEAf D (w i) • fun k => Formalism.UG.inclE (F := D.host.F) (Formalism.MainNotions.S.Af D.host.F) ((d.i₀ * o.iA) k i) := by
  have h2 : HMul.hMul d.j0 o.jA = (d.i₀ * o.iA).map (incA D) := (Matrix.map_mul (f := incA D)).symm
  rw [Matrix.mulVec_mulVec, h2]
  funext k
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    GlobalTheory.Core.Mi.FinFrame.toEAf_incA]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem fin_mt {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n) (g : GA D V) (y : Fin V.rank → AE D) :
    GlobalTheory.AdForm.finM V hn g *ᵥ (fun j => toEAf D (y (Fin.cast hn.symm j))) =
      fun j => toEAf D ((Formalism.L2.Theta.mt V g *ᵥ y) (Fin.cast hn.symm j)) := by
  subst hn
  funext i
  exact (RingHom.map_mulVec (toEAf D) (Formalism.L2.Theta.mt V g) y i).symm

set_option maxHeartbeats 1600000 in

theorem trace_iff : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (F : Formalism.L2.Forms.Forms0 D u) (tr : Formalism.L2.SG.ColDict.Transport X u F) (hK : X.LevelSubgroupCharacter) (B : SBes X h u ψ (D.sp.X 0)) (a₀ : GA D (D.sp.X 0)), GlobalTheory.Core.Mi.IdE X → Formalism.L2.SG.ColDict.LevelMatch X tr hK → B.Adapted tr.wt → IsTransportAdelicCorrection tr a₀ → ∀ (v : GlobalTheory.FinPl.Pl D) (y : Fin (D.sp.X 0).rank → AE D), (∀ i, y i ∈ idAt D (· = v)) → (y ∈ latV (D.sp.X 0) (lat0 F) (· = v) ↔ B.d.j0 *ᵥ (B.o.jA *ᵥ (Formalism.L2.Theta.mt (D.sp.X 0) a₀ *ᵥ y)) ∈ latV (D.sp.Y 0) (latS D) (· = v)) := by
  intro D X h u ψ F tr hK B a₀ hId hL hAd h0 v y hy
  have hn := Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)
  have hy' : ∀ k, (B.d.j0 *ᵥ (B.o.jA *ᵥ (Formalism.L2.Theta.mt (D.sp.X 0) a₀ *ᵥ y))) k ∈ idAt D (· = v) :=
    mulVec_mem_ideal _ (mulVec_mem_ideal _ (mulVec_mem_ideal _ hy))
  refine (latV_iff_hatL _ _ _ _ hy).trans
    (Iff.trans ?_ (latV_iff_hatL _ _ _ _ hy').symm)
  change (fun i => toEAf D (y i)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (lat0 F) ↔
    (fun k => toEAf D ((B.d.j0 *ᵥ (B.o.jA *ᵥ (Formalism.L2.Theta.mt (D.sp.X 0) a₀ *ᵥ y))) k)) ∈
      Formalism.L2.Herm.hatL (F := D.host.F) (latS D)
  refine (hat_reindex hn F.cls0.lev.Lb _).trans ?_
  have H := hL.1 (tr.h0.1.1 *ᵥ fun j => toEAf D (y (Fin.cast hn.symm j)))
  have e1 : (tr.h0⁻¹).1.1 *ᵥ (tr.h0.1.1 *ᵥ fun j => toEAf D (y (Fin.cast hn.symm j))) =
      fun j => toEAf D (y (Fin.cast hn.symm j)) := by
    rw [Matrix.mulVec_mulVec]
    have : HMul.hMul (tr.h0⁻¹).1.1 tr.h0.1.1 = 1 := Units.inv_mul tr.h0.1
    rw [this, Matrix.one_mulVec]
  rw [e1] at H
  refine H.trans ?_
  rw [← h0.2, fin_mt, fin_emb]
  refine (transport D X.B.I X.ιE hId h (rank_eq X h) tr.ιA tr.ιA_rat tr.ιA_int
    (fun i => X.crd (Formalism.L2.SG.ColDict.qFr tr.wt i)) _).trans ?_
  simp only [hAd _ _]
  refine iff_of_eq (congrArg (· ∈ Formalism.L2.Herm.hatL (F := D.host.F) (latS D)) ?_)
  exact (Fintype.sum_equiv (finCongr hn) _ _ fun i => rfl).symm

end GlobalTheory.Core.Mi.LatMatch.TraceX
end

