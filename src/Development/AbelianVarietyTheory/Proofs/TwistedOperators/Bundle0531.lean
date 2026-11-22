import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.HeckeNonvanishing.Imports
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0284
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0268
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0393
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0298

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TrEasy
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

namespace GlobalTheory.RowEx

set_option maxHeartbeats 1000000 in

theorem trEasy : TrEasy := by
  intro X X' T T' L L' sc G G' W W' S S' μ₀ μ₀' ι h M σ
  obtain ⟨⟨hpre, -, -, hC, hbase, hxi, hQ, -⟩, hg, -, hs⟩ := h
  obtain ⟨B, C, Wr, V, Sg, N, Gj⟩ := X
  obtain ⟨B', C', Wr', V', Sg', N', Gj'⟩ := X'
  cases B
  cases B'
  dsimp only at hpre
  subst hpre
  obtain ⟨f, f', hff, hLC, hLC'⟩ := hC
  have hf : f' = f := eq_of_heq hff
  subst hf
  have hv0 : G'.pl.v0 = G.pl.v0 := eq_of_heq hg.v0
  have hw : G'.pl.w = G.pl.w := eq_of_heq hg.w
  have hchi : G'.ch.chiH = G.ch.chiH := eq_of_heq hg.chiH
  have hxi' : ∀ t, L'.xiH t = L.xiH (ι t) := fun t => eq_of_heq (hxi t)
  have hQ' : ∀ t, L'.Q t = L.Q (ι t) := fun t => eq_of_heq (hQ t)
  have hPA : S'.PA = S.PA := eq_of_heq hs.PA
  have hW0 : G'.pl.W0 = G.pl.W0 := by
    unfold Places.W0 Places.S0
    rw [hv0, hw]
    rfl
  have hloc : ∀ t, locPl G' t = locPl G (ι t) := fun t => by
    unfold locPl
    rw [hW0, hQ' t]
    rfl
  have hdep : ∀ w, depthAt G' w = depthAt G w := fun w => by
    unfold depthAt cosExp Places.depth
    rw [hW0, hv0]
    rfl
  refine ⟨fun hch => ?_, fun hr => ?_, fun hr => ?_⟩
  · refine ⟨fun j => ?_, fun t => ?_, fun i h1 h2 => ?_, ?_, ?_, ?_, ?_⟩
    · have := hch.mu0 j
      rw [hLC] at this
      rw [hLC']
      exact this
    · rw [hxi' t]
      exact hch.xi (ι t)
    · rw [hchi]
      exact hch.chi i h1 h2
    · have := hch.eta
      rw [hLC] at this
      rw [hLC']
      exact this
    · have := hch.chiPsi
      rw [hLC] at this
      rw [hLC']
      exact this
    · have := hch.del
      rw [hLC] at this
      rw [hLC']
      exact this
    · have := hch.del'
      rw [hLC] at this
      rw [hLC']
      exact this
  · refine ⟨hr.1, fun t w hwt => ?_, fun w hw' => ?_⟩
    · rw [hdep]
      rw [hloc] at hwt
      exact hr.2.1 (ι t) w hwt
    · rcases hw' with hw' | ⟨t, hw'⟩
      · rw [hPA] at hw'
        exact hr.2.2 w (Or.inl hw')
      · rw [hloc] at hw'
        exact hr.2.2 w (Or.inr ⟨ι t, hw'⟩)
  · intro i j t Λ Λ₀ h1 h2 s hs1 hs2 hΛ
    have hν : ∀ t, SqNum.nuH G' t i j = SqNum.nuH G (ι t) i j := fun t => by
      unfold SqNum.nuH
      rw [hLC', hLC, hxi' t, hchi]
      rfl
    rw [hν] at h1
    rw [hν, hbase] at h2
    exact hr i j (ι t) Λ Λ₀ h1 h2 s hs1 hs2 hΛ

end GlobalTheory.RowEx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TrPhaseOfTrFlip
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

open GlobalTheory.SplitWeil GlobalTheory.SplitFlip MeasureTheory
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

noncomputable section

namespace GlobalTheory.RowEx.PhaseCarry

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k]
  [BorelSpace k] {K : Type} [Field K] (σ : K →+* ℂ)

def PhW (Γ : Grid k) (hs : 1 ≤ Γ.s) (J : Γ.Level) (ψ : AddChar k Circle) (ν : Measure k) (keep : Bool) (ϖ : kˣ) (c : ℕ)
    (T : Γ.Args → ℂ) (β : Cosets hs J) : Prop :=
  ∀ x y e, (unfTerm ψ ν keep (Reps.through hs J (stair Γ ϖ c)) T β).datum x y ≠ 0 →
    moved Γ keep ((Reps.through hs J (stair Γ ϖ c)).elt β) T (fill hs x y e) ≠ 0 → (ψ (phase x e) : ℂ) ∈ Set.range σ

def SuW (Γ : Grid k) (hs : 1 ≤ Γ.s) (J : Γ.Level) (ψ : AddChar k Circle) (ν : Measure k) (keep : Bool) (ϖ : kˣ) (c : ℕ)
    (T : Γ.Args → ℂ) (β : Cosets hs J) : Prop :=
  β ∈ unfSupport ψ ν keep (Reps.through hs J (stair Γ ϖ c)) T

end Loc

section Loc2

variable {k : Type} {_ : Field k} {_ : ValuativeRel k} {_ : TopologicalSpace k} {_ : IsNonarchimedeanLocalField k}
  {_ : MeasurableSpace k} {_ : BorelSpace k} {K : Type} [Field K] (σ : K →+* ℂ)

theorem congrW {Γ Γ' : Grid k} (hΓ : Γ = Γ') {hs : 1 ≤ Γ.s} {hs' : 1 ≤ Γ'.s} {J : Γ.Level} {J' : Γ'.Level} (hJ : HEq J J')
    {ψ ψ' : AddChar k Circle} (hψ : ψ = ψ') {ν ν' : Measure k} (hν : ν = ν') {keep keep' : Bool} (hk : keep = keep')
    (ϖ : kˣ) {c c' : ℕ} (hc : c = c') {T : Γ.Args → ℂ} {T' : Γ'.Args → ℂ} (hT : HEq T T') {β : Cosets hs J}
    {β' : Cosets hs' J'} (hβ : HEq β β') :
    (PhW σ Γ hs J ψ ν keep ϖ c T β ↔ PhW σ Γ' hs' J' ψ' ν' keep' ϖ c' T' β') ∧
      (SuW Γ hs J ψ ν keep ϖ c T β ↔ SuW Γ' hs' J' ψ' ν' keep' ϖ c' T' β') := by
  subst hΓ hψ hν hk hc
  obtain rfl := eq_of_heq hJ
  obtain rfl := eq_of_heq hT
  obtain rfl := eq_of_heq hβ
  exact ⟨Iff.rfl, Iff.rfl⟩

def castCos {Γ Γ' : Grid k} (hΓ : Γ = Γ') {hs : 1 ≤ Γ.s} {hs' : 1 ≤ Γ'.s} {J : Γ.Level} {J' : Γ'.Level} (hJ : HEq J J')
    (β : Cosets hs J) : Cosets hs' J' := by
  subst hΓ
  obtain rfl := eq_of_heq hJ
  exact β

theorem castCos_heq {Γ Γ' : Grid k} (hΓ : Γ = Γ') {hs : 1 ≤ Γ.s} {hs' : 1 ≤ Γ'.s} {J : Γ.Level} {J' : Γ'.Level}
    (hJ : HEq J J') (β : Cosets hs J) : HEq (castCos hΓ (hs' := hs') hJ β) β := by
  subst hΓ
  obtain rfl := eq_of_heq hJ
  rfl

end Loc2

set_option maxHeartbeats 4000000 in

theorem trPhase_of_trFlip : TrFlip → TrPhase := by
  intro hF X X' T T' L L' sc G G' W W' S S' μ₀ μ₀' ι hA M σ hS t' Φ' β' hβ'
  obtain ⟨Φ, hΦ⟩ := hF X X' T T' L L' sc G G' W W' S S' μ₀ μ₀' ι hA Φ'
  have hpre := hA.l.pre
  have hv0 := hA.g.v0
  have hw := hA.g.w
  have hQ := hA.l.Q t'
  have hψ := hA.w.ψ
  clear hF hA
  rcases X with ⟨⟨P⟩, _, _, _, _, _, _⟩
  rcases X' with ⟨⟨P'⟩, _, _, _, _, _, _⟩
  dsimp only at hpre
  subst hpre
  replace hv0 := eq_of_heq hv0
  replace hw := eq_of_heq hw
  replace hQ := eq_of_heq hQ
  replace hψ := eq_of_heq hψ
  have hW0 : G'.pl.W0 = G.pl.W0 := by
    unfold Places.W0 Places.S0
    rw [hv0, hw]
    rfl
  have hloc : locPl G' t' = locPl G (ι t') := by
    unfold locPl
    rw [hW0, hQ]
    rfl
  have hcos : ∀ w, cosExp G' w = cosExp G w := fun w => by
    unfold cosExp Places.depth
    rw [hW0, hv0]
    rfl
  have hkeep : ∀ w, keepAt G' w = keepAt G w := fun w => by
    unfold keepAt
    rw [hW0]
    rfl
  have hpsi : ∀ w, psiAt W' w = psiAt W w := fun w => by
    ext x
    show (W'.ψ _ : ℂ) = W.ψ _
    rw [hψ]
    rfl
  have hmem : ∀ w, w ∈ locPl G (ι t') → w ∈ locPl G' t' := fun w h => hloc ▸ h
  have hF3 := fun w (h : w ∈ locPl G' t') => hΦ t' w w HEq.rfl h
  have hΓ : ∀ w (h : w ∈ locPl G' t'), locGrid G' t' w = locGrid G (ι t') w := fun w h => eq_of_heq (hF3 w h).1
  let β : CosFam G (ι t') := fun w => castCos (hΓ w.1 (hmem _ w.2)) (hF3 w.1 (hmem _ w.2)).2.1 (β' ⟨w.1, hmem _ w.2⟩)
  have hβh : ∀ w : locPl G (ι t'), HEq (β' ⟨w.1, hmem _ w.2⟩) (β w) := fun w => (castCos_heq _ _ _).symm
  have hβ : β ∈ S.supp (ι t') Φ := fun w =>
    ((congrW σ (hΓ w.1 (hmem _ w.2)) (hF3 w.1 (hmem _ w.2)).2.1 (hpsi w.1) rfl (hkeep w.1) (unifAt w.1)
      (hcos w.1) (hF3 w.1 (hmem _ w.2)).2.2 (hβh w)).2).mp (hβ' ⟨w.1, hmem _ w.2⟩)
  intro w'
  have hw' : w'.1 ∈ locPl G (ι t') := hloc ▸ w'.2
  exact ((congrW σ (hΓ w'.1 w'.2) (hF3 w'.1 w'.2).2.1 (hpsi w'.1) rfl (hkeep w'.1) (unifAt w'.1)
      (hcos w'.1) (hF3 w'.1 w'.2).2.2 (hβh ⟨w'.1, hw'⟩)).1).mpr (hS (ι t') Φ β hβ ⟨w'.1, hw'⟩)

end GlobalTheory.RowEx.PhaseCarry
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TransferBottom
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

noncomputable section

namespace GlobalTheory.RowEx

local macro:max "kc% " e:term:max : term => `((by kexactB $e))

theorem triIs_congr {D : D7} {T : Type} {A A' WW : HSp D} {X : Tri T A A' WW} {ψ ψ' : AddChar (AF D.host.F) ℂ} {θ θ' : InfFam D}
    {α α' β β' : T → ((AE D)ˣ →* Circle)} {ν ν' : T → Formalism.L2.Host.HChar D.host.E} {S S' : T → Finset (Pl D.host.E)}
    (h : X.Is ψ θ α β ν S) (e1 : ψ' = ψ) (e2 : θ' = θ) (e3 : ∀ t, α' t = α t) (e4 : ∀ t, β' t = β t) (e5 : ∀ t, ν' t = ν t)
    (e6 : ∀ t, S' t = S t) : X.Is ψ' θ' α' β' ν' S' := by
  obtain rfl := e1
  obtain rfl := e2
  obtain rfl := funext e3
  obtain rfl := funext e4
  obtain rfl := funext e5
  obtain rfl := funext e6
  exact h

set_option maxHeartbeats 1000000 in

theorem trBot_holds : TrBot := by
  intro X X' T T' L L' sc G G' W W' S S' μ₀ μ₀' ι hA M σ hB
  obtain ⟨hl, hg, hw, -⟩ := hA
  have pre := hl.pre
  cases X with | mk B C Wr V Sg N Gj =>
  cases X' with | mk B' C' Wr' V' Sg' N' Gj' =>
  cases B
  cases B'
  dsimp only at pre
  subst pre
  let DX := GlobalTheory.Mem.Stages.toD7 ⟨_, C, Wr, V, Sg, N, Gj⟩
  let DX' := GlobalTheory.Mem.Stages.toD7 ⟨_, C', Wr', V', Sg', N', Gj'⟩
  obtain ⟨f, f', hff, hC, hC'⟩ := hl.C
  obtain rfl : f' = f := eq_of_heq hff
  have hψ : W'.ψ = (by with_unfolding_all exact (W.ψ :)) := eq_of_heq hw.ψ
  have hθ : W'.θ = (by with_unfolding_all exact (W.θ :)) := eq_of_heq hw.θ
  have hxiH : ∀ t, L'.xiH t = (by with_unfolding_all exact ((L.xiH (ι t)) :)) := fun t => eq_of_heq (hl.xi t)
  have hQ : ∀ t, L'.Q t = (by with_unfolding_all exact ((L.Q (ι t)) :)) := fun t => eq_of_heq (hl.Q t)
  have hchi : G'.ch.chi = (by with_unfolding_all exact (G.ch.chi :)) := eq_of_heq hg.chi
  have hchiH : G'.ch.chiH = (by with_unfolding_all exact (G.ch.chiH :)) := eq_of_heq hg.chiH
  have hv0 : G'.pl.v0 = (by with_unfolding_all exact (G.pl.v0 :)) := eq_of_heq hg.v0
  have hwp : G'.pl.w = (by with_unfolding_all exact (G.pl.w :)) := eq_of_heq hg.w
  have hCmu : ∀ j, L'.C.mu0 j = (by with_unfolding_all exact ((L.C.mu0 j) :)) := fun j => by
    have a : L.C.mu0 j = f'.mu0 j := by rw [hC]; rfl
    have b : L'.C.mu0 j = f'.mu0 j := by rw [hC']; rfl
    exact b.trans ((by with_unfolding_all exact (a.symm :)))
  have hCeta : L'.C.eta = (by with_unfolding_all exact (L.C.eta :)) := by
    have a : L.C.eta = f'.eta := by rw [hC]; rfl
    have b : L'.C.eta = f'.eta := by rw [hC']; rfl
    exact b.trans ((by with_unfolding_all exact (a.symm :)))
  have hmu0 : ∀ j : Fin DX'.R.m, L'.mu0 (↑j + 1) = (by with_unfolding_all exact ((L.mu0 (↑j + 1)) :)) := fun j => by
    have h1 : ChrEq ((by with_unfolding_all exact ((L.mu0 (↑j + 1)) :))) (L'.C.mu0 j) := by rw [hCmu j]; exact (by with_unfolding_all exact ((hl.is.mu0 j) :))
    exact (GlobalTheory.ChrEqUnique.chrEq_unique DX').2.1 _ _ _ (hl.is'.mu0 j) h1
  have heta : L'.eta = (by with_unfolding_all exact (L.eta :)) := by
    have h1 : ChrEq ((by with_unfolding_all exact (L.eta :))) L'.C.eta := by rw [hCeta]; exact (by with_unfolding_all exact (hl.is.eta :))
    exact (GlobalTheory.ChrEqUnique.chrEq_unique DX').2.1 _ _ _ hl.is'.eta h1
  have hxi : ∀ t, L'.xi t = (by with_unfolding_all exact ((L.xi (ι t)) :)) := fun t => by
    have h1 : ChrEq ((by with_unfolding_all exact ((L.xi (ι t)) :))) (L'.xiH t) := by rw [hxiH t]; exact (by with_unfolding_all exact ((hl.is.xi (ι t)) :))
    exact (GlobalTheory.ChrEqUnique.chrEq_unique DX').2.1 _ _ _ (hl.is'.xi t) h1

  have thImp : ∀ ψ S T f, @IsThetaFunO DX ψ S T f → @IsThetaFunO DX' ((by with_unfolding_all exact (ψ :))) ((by with_unfolding_all exact (S :))) ((by with_unfolding_all exact (T :))) ((by with_unfolding_all exact (f :))) :=
    fun ψ S T f h => ⟨(by with_unfolding_all exact (h.quasi :)), (by with_unfolding_all exact (h.level :)), (by with_unfolding_all exact (h.cont :)), (by with_unfolding_all exact (h.smooth :))⟩
  have thImp' : ∀ ψ S T f, @IsThetaFunO DX' ψ S T f → @IsThetaFunO DX ((by with_unfolding_all exact (ψ :))) ((by with_unfolding_all exact (S :))) ((by with_unfolding_all exact (T :))) ((by with_unfolding_all exact (f :))) :=
    fun ψ S T f h => ⟨(by with_unfolding_all exact (h.quasi :)), (by with_unfolding_all exact (h.level :)), (by with_unfolding_all exact (h.cont :)), (by with_unfolding_all exact (h.smooth :))⟩
  have thEq : @IsThetaFunO DX' = fun ψ S T f => @IsThetaFunO DX ((by with_unfolding_all exact (ψ :))) ((by with_unfolding_all exact (S :))) ((by with_unfolding_all exact (T :))) ((by with_unfolding_all exact (f :))) := by
    funext ψ S T f
    exact propext ⟨fun h => (by with_unfolding_all exact ((thImp' _ _ _ _ h) :)), fun h => (by with_unfolding_all exact ((thImp _ _ _ _ h) :))⟩
  have wImp : ∀ ψ S T x1 x2 ω, @IsWeilDatumO DX ψ S T x1 x2 ω →
      @IsWeilDatumO DX' ((by with_unfolding_all exact (ψ :))) ((by with_unfolding_all exact (S :))) ((by with_unfolding_all exact (T :))) ((by with_unfolding_all exact (x1 :))) ((by with_unfolding_all exact (x2 :))) ((by with_unfolding_all exact (ω :))) := fun ψ S T x1 x2 ω h =>
    { std := (by with_unfolding_all exact (h.std :))
      hecS := (by with_unfolding_all exact (h.hecS :))
      hecT := (by with_unfolding_all exact (h.hecT :))
      resS := (by with_unfolding_all exact (h.resS :))
      resT := (by with_unfolding_all exact (h.resT :))
      om_pres := by rewrite [thEq]; exact (by with_unfolding_all exact (h.om_pres :))
      om_heis := by rewrite [thEq]; exact (by with_unfolding_all exact (h.om_heis :))
      om_aut := by rewrite [thEq]; exact (by with_unfolding_all exact (h.om_aut :))
      om_cont := by rewrite [thEq]; exact (by with_unfolding_all exact (h.om_cont :))
      om_unit := by rewrite [thEq]; exact (by with_unfolding_all exact (h.om_unit :))
      om_split := by rewrite [thEq]; exact (by with_unfolding_all exact (h.om_split :)) }
  have vacImp : ∀ ψ θ S T sS sT LS LT f, @IsVacO DX ψ θ S T sS sT LS LT f →
      @IsVacO DX' ((by with_unfolding_all exact (ψ :))) ((by with_unfolding_all exact (θ :))) ((by with_unfolding_all exact (S :))) ((by with_unfolding_all exact (T :))) ((by with_unfolding_all exact (sS :))) ((by with_unfolding_all exact (sT :))) ((by with_unfolding_all exact (LS :))) ((by with_unfolding_all exact (LT :))) ((by with_unfolding_all exact (f :))) :=
    fun ψ θ S T sS sT LS LT f h => by
      unfold IsVacO
      rewrite [thEq]
      exact ⟨(by with_unfolding_all exact (h.1 :)), (by with_unfolding_all exact (h.2.inf :)), (by with_unfolding_all exact (h.2.theta :)), (by with_unfolding_all exact (h.2.lat :)), (by with_unfolding_all exact (h.2.fock :)), (by with_unfolding_all exact (h.2.norm :))⟩
  have pmImp : ∀ m n ψ B hs e Λ c f₀ T, @IsPlaceModel DX m n ψ B hs e Λ c f₀ T →
      @IsPlaceModel DX' m n ((by with_unfolding_all exact (ψ :))) ((by with_unfolding_all exact (B :))) ((by with_unfolding_all exact (hs :))) ((by with_unfolding_all exact (e :))) ((by with_unfolding_all exact (Λ :))) c ((by with_unfolding_all exact (f₀ :))) ((by with_unfolding_all exact (T :))) :=
    fun m n ψ B hs e Λ c f₀ T h => ⟨(by with_unfolding_all exact (h.trans :)), (by with_unfolding_all exact (h.modul :)), (by with_unfolding_all exact (h.vac :))⟩
  have pmImp' : ∀ m n ψ B hs e Λ c f₀ T, @IsPlaceModel DX' m n ψ B hs e Λ c f₀ T →
      @IsPlaceModel DX m n ((by with_unfolding_all exact (ψ :))) ((by with_unfolding_all exact (B :))) ((by with_unfolding_all exact (hs :))) ((by with_unfolding_all exact (e :))) ((by with_unfolding_all exact (Λ :))) c ((by with_unfolding_all exact (f₀ :))) ((by with_unfolding_all exact (T :))) :=
    fun m n ψ B hs e Λ c f₀ T h => ⟨(by with_unfolding_all exact (h.trans :)), (by with_unfolding_all exact (h.modul :)), (by with_unfolding_all exact (h.vac :))⟩
  have pmEq : @IsPlaceModel DX' = fun m n ψ B hs e Λ c f₀ T =>
      @IsPlaceModel DX m n ((by with_unfolding_all exact (ψ :))) ((by with_unfolding_all exact (B :))) ((by with_unfolding_all exact (hs :))) ((by with_unfolding_all exact (e :))) ((by with_unfolding_all exact (Λ :))) c ((by with_unfolding_all exact (f₀ :))) ((by with_unfolding_all exact (T :))) := by
    funext m n ψ B hs e Λ c f₀ T
    exact propext ⟨fun h => (by with_unfolding_all exact ((pmImp' _ _ _ _ _ _ _ _ _ _ h) :)), fun h => (by with_unfolding_all exact ((pmImp _ _ _ _ _ _ _ _ _ _ h) :))⟩
  intro i j
  obtain ⟨A, A', WW, Y, hb, hsum⟩ := hB i j
  have hmu : ∀ t, L'.mu t (↑j + 1) = (by with_unfolding_all exact ((L.mu (ι t) (↑j + 1)) :)) := fun t => by
    show L'.mu0 (↑j + 1) * L'.xi t = _
    rw [hmu0 j, hxi t]
    exact (by with_unfolding_all exact ((Eq.refl (L.mu (ι t) (↑j + 1))) :))
  have hnu : ∀ t, SqNum.nuH G' t i j = (by with_unfolding_all exact ((SqNum.nuH G (ι t) i j) :)) := fun t => by
    show L'.C.mu0 j * L'.xiH t / G'.ch.chiH (DX'.R.m - ↑i) = _
    rw [hCmu j, hxiH t, hchiH]
    exact (by with_unfolding_all exact ((Eq.refl (SqNum.nuH G (ι t) i j)) :))
  have hloc : ∀ t, locPl G' t = (by with_unfolding_all exact ((locPl G (ι t)) :)) := fun t => by
    unfold locPl GlobalTheory.ChiGrid.Places.W0 GlobalTheory.ChiGrid.Places.S0
    rw [hQ t, hv0, hwp]
    exact (by with_unfolding_all exact ((Eq.refl (locPl G (ι t))) :))
  refine ⟨A, A', WW,
    ⟨⟨(by with_unfolding_all exact (Y.rA.Λ :)), (by with_unfolding_all exact (Y.rA.β :)), (by with_unfolding_all exact (Y.rA.s :)), (by with_unfolding_all exact (Y.rA.B :))⟩, ⟨(by with_unfolding_all exact (Y.rA'.Λ :)), (by with_unfolding_all exact (Y.rA'.β :)), (by with_unfolding_all exact (Y.rA'.s :)), (by with_unfolding_all exact (Y.rA'.B :))⟩,
      ⟨(by with_unfolding_all exact (Y.rW.Λ :)), (by with_unfolding_all exact (Y.rW.β :)), (by with_unfolding_all exact (Y.rW.s :)), (by with_unfolding_all exact (Y.rW.B :))⟩, fun t => (by with_unfolding_all exact ((Y.ω (ι t)) :)), fun t => (by with_unfolding_all exact ((Y.ω' (ι t)) :)), (by with_unfolding_all exact (Y.vac :)),
      (by with_unfolding_all exact (Y.vac' :)), fun t => (by with_unfolding_all exact ((Y.e (ι t)) :)), fun t => (by with_unfolding_all exact ((Y.c (ι t)) :)), fun t => (by with_unfolding_all exact ((Y.f (ι t)) :)), fun t => (by with_unfolding_all exact ((Y.f' (ι t)) :)),
      (by with_unfolding_all exact (Y.m :)), (by with_unfolding_all exact (Y.fd :)), (by with_unfolding_all exact (Y.m' :)), (by with_unfolding_all exact (Y.fd' :))⟩, ⟨(by with_unfolding_all exact (hb.rank :)), (by with_unfolding_all exact (hb.rank' :)), (by with_unfolding_all exact (hb.std :)), (by with_unfolding_all exact (hb.std' :)), (by with_unfolding_all exact (hb.stdW :)), ?_⟩, ?_⟩
  · have e3 : ∀ t, L'.mu t (↑j + 1) * L'.eta ^ (rankV DX' i j % 2) =
        (by with_unfolding_all exact ((L.mu (ι t) (↑j + 1) * L.eta ^ (rankV DX i j % 2)) :)) := fun t => by
      rw [hmu t, heta]
      exact (by with_unfolding_all exact ((Eq.refl (L.mu (ι t) (↑j + 1) * L.eta ^ (rankV DX i j % 2))) :))
    have e4 : ∀ _ : T', G'.ch.chi (DX'.R.m - ↑i) * L'.eta ^ (rankV DX' i j % 2) =
        (by with_unfolding_all exact ((G.ch.chi (DX.R.m - ↑i) * L.eta ^ (rankV DX i j % 2)) :)) := fun _ => by
      rw [hchi, heta]
      exact (by with_unfolding_all exact ((Eq.refl (G.ch.chi (DX.R.m - ↑i) * L.eta ^ (rankV DX i j % 2))) :))
    refine triIs_congr ?_ hψ hθ e3 e4 hnu hloc
    exact ⟨(by with_unfolding_all exact (hb.is.rank :)), (by with_unfolding_all exact (hb.is.rigA :)), (by with_unfolding_all exact (hb.is.rigA' :)), (by with_unfolding_all exact (hb.is.rigW :)),
      fun t => by unfold GlobalTheory.Grid.IsWeil; exact (by with_unfolding_all exact ((wImp _ _ _ _ _ _ (hb.is.weil (ι t))) :)),
      fun t => by unfold GlobalTheory.Grid.IsWeil; exact (by with_unfolding_all exact ((wImp _ _ _ _ _ _ (hb.is.weil' (ι t))) :)),
      (by with_unfolding_all exact ((vacImp _ _ _ _ _ _ _ _ _ hb.is.isVac) :)), (by with_unfolding_all exact ((vacImp _ _ _ _ _ _ _ _ _ hb.is.isVac') :)),
      fun t => (by with_unfolding_all exact ((hb.is.idem (ι t)) :)), fun t => (by with_unfolding_all exact ((hb.is.expo (ι t)) :)),
      fun t => by unfold IsThetaAt; rewrite [pmEq]; exact (by with_unfolding_all exact ((hb.is.fst (ι t)) :)),
      fun t => by unfold IsThetaAt; rewrite [pmEq]; exact (by with_unfolding_all exact ((hb.is.snd (ι t)) :)),
      (by with_unfolding_all exact (hb.is.meas :)), (by with_unfolding_all exact (hb.is.meas' :))⟩
  · obtain ⟨Ω, Ω', h0, h0', H⟩ := hsum
    refine ⟨Ω, Ω', h0, h0', fun t h hh => ?_⟩
    rw [hψ, hθ]
    have H3 := H (ι t) ((by with_unfolding_all exact (h :))) ((by with_unfolding_all exact (hh :)))
    exact (by with_unfolding_all exact (H3 :))

end GlobalTheory.RowEx

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VecMulEntry
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open ValuativeRel

noncomputable section
namespace GlobalTheory.FrameScale

theorem vecMul_entry {E k ι : Type} [Field E] [Field k] [Fintype ι] {n c : ℕ} (φ : E →+* k) (σ : E →+* E)
    (a : Matrix (Fin n) (Fin c) E) (g : Matrix (Fin n) (Fin n) E) (b : Matrix (Fin n) ι k) (x : k) (q r : Fin c) (m : ι)
    (hb : ∀ i, b i m = x * φ (a i r)) :
    ((fun i => φ (σ (a i q))) ᵥ* (g.map φ * b)) m = x * φ ((Formalism.UG.cT σ a * g * a) q r) := by
  simp only [Matrix.vecMul, dotProduct, Matrix.mul_apply, hb, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply,
    map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring

end GlobalTheory.FrameScale
end

theorem GlobalTheory.FrameScale.clauses : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h' : 2 * σ + 2 ≤ D.R.m)
  (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (p : GlobalTheory.FinPl.SplitPt D k) (β : GlobalTheory.FinPl.Frame p (G.V (.grid (2 * σ + 2) 0)) (Fin (G.V (.grid (2 * σ + 2) 0)).rank))
  (j : Fin (2 * σ + 2 - 1) → Fin (G.V (.grid (2 * σ + 2) 0)).rank) (ϖ : k) (e : ℕ), ϖ ≠ 0 → Function.Injective j →
  (∀ r i, β.b i (j r) = ϖ ^ (e * (r.1 + 1)) * p.pr (incA D ((G.colDec (2 * σ + 2) (by omega) h').a i r))) →
  (∀ m, m ∉ Set.range j → ∀ r, ((fun i => p.pr (incA D (star ((G.colDec (2 * σ + 2) (by omega) h').a i r)))) ᵥ* (((G.V (.grid (2 * σ + 2) 0)).gram.map (fun c => p.pr (incA D c))) * β.b)) m = 0) →
  (∀ q : Fin (σ + 1), (ϖ ^ (e * (q.1 + 1)) * (p.pr (incA D (-D.host.xi0)))⁻¹ ^ (q.1 + 1)) •
      (β.b' *ᵥ fun i => p.pr (xFB F σ h' i q)) = Pi.single (j ⟨q.1, by omega⟩) 1) ∧
  (∀ q : Fin (σ + 1), (ϖ ^ (e * (2 * σ + 1 - q.1)) * p.pr (incA D (star (-D.host.xi0))) ^ (q.1 + 1) *
      (if q.1 = σ then -1 else 1))⁻¹ • ((fun i => p.pr (cA D (xFB F σ h' i q))) ᵥ* (((G.V (.grid (2 * σ + 2) 0)).gram.map (fun c => p.pr (incA D c))) * β.b)) =
      Pi.single (j ⟨2 * σ - q.1, by omega⟩) 1) := by
  intro D _ T L _ _ sc G W _ _ F hF σ h' k _ _ _ _ p β j ϖ e hϖ hj hb hout
  have hne : (-D.host.xi0) ≠ 0 := neg_ne_zero.2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)
  have hc : p.pr (incA D (-D.host.xi0)) ≠ 0 := ((hne.isUnit.map (incA D)).map p.pr).ne_zero
  have hc' : p.pr (incA D (star (-D.host.xi0))) ≠ 0 :=
    (((star_ne_zero.2 hne).isUnit.map (incA D)).map p.pr).ne_zero
  have hcol : ∀ (q : Fin (σ + 1)) i, xFB F σ h' i q = incA D ((-D.host.xi0) ^ (q.1 + 1)) * incA D ((G.colDec (2 * σ + 2) (by omega) h').a i ⟨q.1, by omega⟩) := by
    intro q i
    have := congrFun (GlobalTheory.CharXFB.xFB_col F hF σ h' q) i
    simp only [Pi.smul_apply, smul_eq_mul] at this
    rw [this]
    rfl
  have key : ∀ m, β.b' *ᵥ (fun i => β.b i m) = Pi.single m 1 := by
    intro m
    have : (fun i => β.b i m) = β.b *ᵥ Pi.single m 1 := by
      funext i; simp [Matrix.mulVec_single]
    rw [this, Matrix.mulVec_mulVec, β.b'b, Matrix.one_mulVec]
  refine ⟨fun q => ?_, fun q => ?_⟩
  · have hv : (fun i => p.pr (xFB F σ h' i q)) =
        (p.pr (incA D (-D.host.xi0)) ^ (q.1 + 1) * (ϖ ^ (e * (q.1 + 1)))⁻¹) • fun i => β.b i (j ⟨q.1, by omega⟩) := by
      funext i
      rw [hcol]
      simp only [map_mul, map_pow, Pi.smul_apply, smul_eq_mul, hb]
      field_simp
    rw [hv, Matrix.mulVec_smul, key, smul_smul]
    convert one_smul k _
    rw [inv_pow]
    field_simp
  · have hv : (fun i => p.pr (cA D (xFB F σ h' i q))) = p.pr (incA D (star (-D.host.xi0))) ^ (q.1 + 1) •
        fun i => p.pr (incA D (star ((G.colDec (2 * σ + 2) (by omega) h').a i ⟨q.1, by omega⟩))) := by
      funext i
      rw [hcol]
      simp only [map_mul, GlobalTheory.DualPairCheck.cA_incA, star_pow, map_pow, Pi.smul_apply, smul_eq_mul]
    have hsm : ∀ (x : k) (u : Fin (G.V (.grid (2 * σ + 2) 0)).rank → k)
        (M : Matrix (Fin (G.V (.grid (2 * σ + 2) 0)).rank) (Fin (G.V (.grid (2 * σ + 2) 0)).rank) k),
        (x • u) ᵥ* M = x • (u ᵥ* M) := by
      intro x u M
      funext m
      simp only [Matrix.vecMul, dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
    have hg := (G.colDec (2 * σ + 2) (by omega) h').gram
    have hw : ((fun i => p.pr (incA D (star ((G.colDec (2 * σ + 2) (by omega) h').a i ⟨q.1, by omega⟩)))) ᵥ*
        (((G.V (.grid (2 * σ + 2) 0)).gram.map (fun c => p.pr (incA D c))) * β.b)) =
        (ϖ ^ (e * (2 * σ + 1 - q.1)) * (if q.1 = σ then -1 else 1)) • Pi.single (j ⟨2 * σ - q.1, by omega⟩) 1 := by
      funext m
      by_cases hm : m ∈ Set.range j
      · obtain ⟨r, rfl⟩ := hm
        refine (GlobalTheory.FrameScale.vecMul_entry (p.pr.comp (incA D)) (D.sp.cm.sig : D.host.E →+* D.host.E)
          (G.colDec (2 * σ + 2) (by omega) h').a _ β.b _ ⟨q.1, by omega⟩ r (j r) (hb r)).trans ?_
        rw [hg]
        simp only [Pi.smul_apply, smul_eq_mul, GlobalTheory.ChiGrid.antiDiagonalSignGramMatrix, RingHom.coe_comp, Function.comp_apply]
        by_cases hr : r = ⟨2 * σ - q.1, by omega⟩
        · subst hr
          have e1 : 2 * σ - q.1 + 1 = 2 * σ + 1 - q.1 := by omega
          rw [Pi.single_eq_same, if_pos (by simp only; omega), e1]
          by_cases hq : q.1 = σ
          · rw [if_pos (Fin.ext (by simp only; omega)), if_pos hq]
            simp
          · rw [if_neg (fun h => hq (by have := congrArg Fin.val h; simp only at this; omega)), if_neg hq]
            simp
        · rw [Pi.single_eq_of_ne (hj.ne hr), if_neg (fun h => hr (Fin.ext (by simp only; omega)))]
          simp
      · rw [hout m hm ⟨q.1, by omega⟩, Pi.smul_apply, Pi.single_eq_of_ne (fun h => hm ⟨_, h.symm⟩), smul_zero]
    have hs : (if q.1 = σ then (-1 : k) else 1) ≠ 0 := by split_ifs <;> norm_num
    rw [hv, hsm, hw, smul_smul, smul_smul]
    refine (congrArg (· • Pi.single (j ⟨2 * σ - q.1, by omega⟩) (1 : k)) ?_).trans (one_smul k _)
    field_simp
end

