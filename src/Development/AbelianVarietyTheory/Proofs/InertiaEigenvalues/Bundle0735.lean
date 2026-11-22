import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle0005
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0191
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0691
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0725
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
import Formalism.LocalToGlobal.Columns.Bundle0015
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPotCrysAtOfMono0
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EqOfPowEqOneOfNormSubLt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0068
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0311

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisRepBaseChangeTwist
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass

noncomputable section

namespace GlobalTheory.BCAllPlaces

open Formalism.MainNotions.SumRepresentations.At GlobalTheory.TwistLG GlobalTheory.BCGal

section Glob

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) (i : N.Loc)

def AllRep (m : ℕ) (L : ∀ w, A.LP w) : Prop :=
  ∃ r : Formalism.ConjugateSelfDual.G H.E N.Om →* GL (Fin m) (Qbar (N.l i)), ContQ N i r ∧ IsSSRep r ∧
    ∀ w, WDok N A i r w ∧ A.wdOf i r w = L w

theorem AllRep.congr {m m' : ℕ} {L L' : ∀ w, A.LP w} (h : AllRep N A i m L) (hm : m = m')
    (hL : ∀ w, L w = L' w) : AllRep N A i m' L' := by
  subst hm
  obtain ⟨r, c, s, f⟩ := h
  exact ⟨r, c, s, fun w => ⟨(f w).1, (f w).2.trans (hL w)⟩⟩

theorem AllRep.sum (hGal : TieGal N A) {m m' : ℕ} {L L' : ∀ w, A.LP w} (h : AllRep N A i m L)
    (h' : AllRep N A i m' L') : AllRep N A i (m + m') fun w => A.lpSum (L w) (L' w) := by
  obtain ⟨r, c, s, f⟩ := h
  obtain ⟨r', c', s', f'⟩ := h'
  obtain ⟨-, -, hsum, -⟩ := hGal.2.2.2 i
  refine ⟨sumRep r r', cont_sumRep r r' c c', ss_sumRep r r' s s', fun w => ⟨?_, ?_⟩⟩
  · by_cases hw : w ∈ placesOver H.E (N.l i)
    · exact Or.inr (((hsum m m' r r' c c').1 w hw).2
        ⟨(f w).1.resolve_left (not_not.2 hw), (f' w).1.resolve_left (not_not.2 hw)⟩)
    · exact Or.inl hw
  · rw [(hsum m m' r r' c c').2.1 w (f w).1 (f' w).1, (f w).2, (f' w).2]

theorem allw {a : ℕ} (ρ : Formalism.ConjugateSelfDual.G H.E N.Om →* GL (Fin a) (Qbar (N.l i))) (L : ∀ w, A.LP w)
    (h1 : ∀ w, w ∉ placesOver H.E (N.l i) → A.wdOf i ρ w = L w)
    (h2 : ∀ w ∈ placesOver H.E (N.l i), A.IsdRW i ρ w ∧ A.wdOf i ρ w = L w) :
    ∀ w, WDok N A i ρ w ∧ A.wdOf i ρ w = L w := by
  intro w
  by_cases hw : w ∈ placesOver H.E (N.l i)
  · exact ⟨Or.inr (h2 w hw).1, (h2 w hw).2⟩
  · exact ⟨Or.inl hw, h1 w hw⟩

theorem allTw (hGal : TieGal N A) {a : ℕ} (ρ : Formalism.ConjugateSelfDual.G H.E N.Om →* GL (Fin a) (Qbar (N.l i)))
    (χ : Formalism.ConjugateSelfDual.G H.E N.Om →* GL (Fin 1) (Qbar (N.l i))) (cρ : ContQ N i ρ) (cχ : ContQ N i χ)
    {L M : ∀ w, A.LP w} (hρ : ∀ w, WDok N A i ρ w ∧ A.wdOf i ρ w = L w)
    (hχ : ∀ w, WDok N A i χ w ∧ A.wdOf i χ w = M w) :
    ∀ w, WDok N A i (twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) w ∧
      A.wdOf i (twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) w = A.lpChar (L w) (M w) := by
  obtain ⟨-, -, -, htw⟩ := hGal.2.2.2 i
  have ht := htw a ρ χ cρ cχ
  intro w
  refine ⟨?_, ?_⟩
  · by_cases hw : w ∈ placesOver H.E (N.l i)
    · exact Or.inr ((ht.1 w hw ((hχ w).1.resolve_left (not_not.2 hw))).2
        ((hρ w).1.resolve_left (not_not.2 hw)))
    · exact Or.inl hw
  · rw [ht.2.1 w (hρ w).1 (hχ w).1, (hρ w).2, (hχ w).2]

theorem allRep_foldr (hGal : TieGal N A) {α : Type} (m : α → ℕ) (L : α → ∀ w, A.LP w) :
    ∀ xs : List α, xs ≠ [] → (∀ x ∈ xs, AllRep N A i (m x) (L x)) →
      AllRep N A i (xs.map m).sum fun w => xs.foldr (fun x acc => A.lpSum (L x w) acc) (A.lpZero w)
  | [], h, _ => absurd rfl h
  | [x], _, h => (h x (by simp)).congr N A i (by simp) fun w => by simp [A.lpSum_zero]
  | x :: y :: ys, _, h =>
      ((h x (by simp)).sum N A i hGal (allRep_foldr hGal m L (y :: ys) (by simp)
        fun z hz => h z (List.mem_cons_of_mem _ hz))).congr N A i (by simp) fun w => rfl

theorem lpTw_foldr {α : Type} (L : α → ∀ w, A.LP w) (w : PlE H) (c : ℝ) (xs : List α) :
    A.lpTw (xs.foldr (fun x acc => A.lpSum (L x w) acc) (A.lpZero w)) c =
      xs.foldr (fun x acc => A.lpSum (A.lpTw (L x w) c) acc) (A.lpZero w) := by
  induction xs with
  | nil => exact lpTw_lpZero N A w c
  | cons x xs ih => rw [List.foldr_cons, List.foldr_cons, A.lpTw_sum, ih]

theorem allRep_isoLoc (hGal : TieGal N A) (c : ℝ) (Pa : List (Part A.CG)) (hne : Pa ≠ [])
    (hd : ∀ p ∈ Pa, 1 ≤ p.d)
    (h : ∀ p ∈ Pa, ∀ k < p.d, AllRep N A i p.a fun w =>
      A.lpTw (A.locG p.π w) (((p.d : ℝ) - 1) / 2 - k + c)) :
    AllRep N A i (rankIso N A Pa) fun w => A.lpTw (isoLoc N A Pa w) c := by
  have hp : ∀ p ∈ Pa, AllRep N A i (p.a * p.d) fun w => A.lpTw (spehLoc N A p w) c := by
    intro p hpm
    have hmem : ∀ k ∈ ((List.range p.d : List ℕ) : List ℝ), ∃ n : ℕ, n < p.d ∧ (n : ℝ) = k := by
      intro k hk
      simp [Lean.Internal.coeM] at hk
      obtain ⟨n, hn, rfl⟩ := hk
      exact ⟨n, hn, rfl⟩
    have hr : ((List.range p.d : List ℕ) : List ℝ) ≠ [] := by
      have h1 : 0 < p.d := hd p hpm
      intro h0
      have : ((0 : ℕ) : ℝ) ∈ ((List.range p.d : List ℕ) : List ℝ) := by
        simp [Lean.Internal.coeM]
        exact ⟨0, h1, by simp⟩
      rw [h0] at this
      simp at this
    refine (allRep_foldr N A i hGal (fun _ => p.a)
      (fun (k : ℝ) w => A.lpTw (A.locG p.π w) (((p.d : ℝ) - 1) / 2 - k + c)) _ hr
      fun k hk => ?_).congr N A i ?_ fun w => ?_
    · obtain ⟨n, hn, rfl⟩ := hmem k hk
      exact h p hpm n hn
    · simp [Lean.Internal.coeM, mul_comm]
    · rw [spehLoc, lpTw_foldr N A (fun (k : ℝ) w => A.lpTw (A.locG p.π w) (((p.d : ℝ) - 1) / 2 - k)) w c]
      simp only [A.lpTw_add]
  exact (allRep_foldr N A i hGal (fun p => p.a * p.d) (fun p w => A.lpTw (spehLoc N A p w) c) Pa hne hp).congr
    N A i rfl fun w => (lpTw_foldr N A (fun p w => spehLoc N A p w) w c Pa).symm

end Glob

section Piece

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) (i : N.Loc)

theorem allRep_piece (hLP : TieLP N A) (hAut : TieAut N A) (hGal : TieGal N A) (hG : exists_galois_rep_local_global_compatible N A)
    {a : ℕ} (ha : 1 ≤ a) (π : A.CG a) (hc : A.csd π) (m : ℤ)
    (hinf : ∀ τ, (A.infG π τ).Nodup ∧
      ∀ z ∈ A.infG π τ, ∃ n : ℤ, z + (((m : ℝ) / 2 : ℝ) : ℂ) = (n : ℂ) + ((a : ℂ) - 1) / 2) :
    AllRep N A i a fun w => A.lpTw (A.locG π w) ((m : ℝ) / 2 + (1 - (a : ℝ)) / 2) := by
  rcases Int.even_or_odd' m with ⟨k, hk | hk⟩ <;> subst hk
  ·
    have hralg : A.ralg π := (A.ralg_def π).2 fun τ => ⟨(hinf τ).1, fun z hz => by
      obtain ⟨n, hn⟩ := (hinf τ).2 z hz
      exact ⟨n - k, by push_cast at hn ⊢; linear_combination hn⟩⟩
    obtain ⟨ρ1, c1, ss1, away1, over1⟩ := (hG i).1 a ha π hc hralg
    obtain ⟨χA, cA, awayA, overA⟩ := (hG i).2.2 A.etaT (1 / 2) fun τ z hz => by
      obtain ⟨n, hn⟩ := (eta_alg N A hAut 0 τ).1 z hz
      exact ⟨n, by push_cast at hn ⊢; linear_combination hn⟩
    obtain ⟨χB, cB, awayB, overB⟩ := (hG i).2.2 A.etaTinv ((k : ℝ) - 1 / 2) fun τ z hz => by
      obtain ⟨n, hn⟩ := (eta_alg N A hAut (k - 1) τ).2 z hz
      exact ⟨n, by push_cast at hn ⊢; linear_combination hn⟩
    have f1 := allw N A i ρ1 _ (fun w hw => (away1 w hw).1) fun w hw => ⟨(over1 w hw).1, (over1 w hw).2.2⟩
    have fA := allw N A i χA _ awayA fun w hw => ⟨(overA w hw).1, (overA w hw).2.1⟩
    have fB := allw N A i χB _ awayB fun w hw => ⟨(overB w hw).1, (overB w hw).2.1⟩
    let ρ2 := twGL ρ1 (Matrix.GeneralLinearGroup.det.comp χA)
    have c2 : ContQ N i ρ2 := cont_twGL ρ1 χA c1 cA
    have f2 := allTw N A i hGal ρ1 χA c1 cA f1 fA
    have f3 := allTw N A i hGal ρ2 χB c2 cB f2 fB
    refine ⟨twGL ρ2 (Matrix.GeneralLinearGroup.det.comp χB), cont_twGL ρ2 χB c2 cB,
      isSSRep_twGL _ _ (isSSRep_twGL _ _ ss1), fun w => ⟨(f3 w).1, ?_⟩⟩
    rw [(f3 w).2, param_int N A hLP]
    congr 1
    push_cast
    ring
  ·
    have hcsd : A.csd (A.tw π A.etaT) := A.csd_tw π A.etaT hAut.1.1 hc
    have hralg : A.ralg (A.tw π A.etaT) := (A.ralg_def _).2 fun τ => by
      obtain ⟨e, he⟩ := Multiset.card_eq_one.mp (A.infG_card A.etaT τ)
      rw [A.infG_tw π A.etaT τ e he]
      refine ⟨(hinf τ).1.map (add_left_injective e), fun y hy => ?_⟩
      obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.1 hy
      obtain ⟨n, hn⟩ := (hinf τ).2 z hz
      obtain ⟨j, hj⟩ := (eta_alg N A hAut 0 τ).1 e (by rw [he]; exact Multiset.mem_singleton_self e)
      exact ⟨n + j - k - 1, by push_cast at hn hj ⊢; linear_combination hn + hj⟩
    obtain ⟨ρ1, c1, ss1, away1, over1⟩ := (hG i).1 a ha _ hcsd hralg
    obtain ⟨χ1, cχ, awayχ, overχ⟩ := (hG i).2.2 A.etaTinv ((k : ℝ) + 1 / 2) (eta_alg N A hAut k · |>.2)
    have f1 := allw N A i ρ1 _ (fun w hw => (away1 w hw).1) fun w hw => ⟨(over1 w hw).1, (over1 w hw).2.2⟩
    have fχ := allw N A i χ1 _ awayχ fun w hw => ⟨(overχ w hw).1, (overχ w hw).2.1⟩
    have f2 := allTw N A i hGal ρ1 χ1 c1 cχ f1 fχ
    refine ⟨twGL ρ1 (Matrix.GeneralLinearGroup.det.comp χ1), cont_twGL ρ1 χ1 c1 cχ, isSSRep_twGL _ _ ss1,
      fun w => ⟨(f2 w).1, ?_⟩⟩
    rw [(f2 w).2, param_twist N A hLP]
    congr 1
    push_cast
    ring

end Piece

theorem main : ∀ D : D7, SumRepresentations.tie0 D → SumRepresentations.adm2 D → ∀ (i : D.nd.Loc) (PI : D.naut.AV i)
    (Pa : List (Part D.naut.CG)), IsBCV D.nd D.naut i PI Pa →
    ∃ ρ : GE D.nd →* GL (Fin D.R.nV) (Qbar (D.nd.l i)), SumRepresentations.At.ContQ D.nd i ρ ∧ IsSSRep ρ ∧
      ∀ w, SumRepresentations.At.WDok D.nd D.naut i ρ w ∧
        D.naut.wdOf i ρ w = D.naut.lpTw (isoLoc D.nd D.naut Pa w) ((1 - (D.R.nV : ℝ)) / 2) := by
  intro D hT hG i P Pa hB
  obtain ⟨hLP, hAut, hGal⟩ := hT
  have hne : Pa ≠ [] := by
    rintro rfl
    have h0 := hB.2.2.1
    simp only [rankIso, List.map_nil, List.sum_nil] at h0
    have : 1 ≤ D.R.nV := by
      have := D.R.t_odd.pos
      unfold Ranks.nV
      omega
    omega
  have hreal := allRep_isoLoc D.nd D.naut i hGal ((1 - (D.R.nV : ℝ)) / 2) Pa hne
    (fun p hp => (hB.1 p hp).2.1) fun p hp k hk => by
    obtain ⟨ha, -, hc⟩ := hB.1 p hp
    refine (allRep_piece D.nd D.naut i hLP hAut hGal hG ha p.π hc
      ((p.d : ℤ) - 1 - 2 * k + p.a - D.R.nV) fun τ => ?_).congr D.nd D.naut i rfl fun w => ?_
    · have hW : (D.naut.infWt i τ).Nodup ∧
          ∀ z ∈ D.naut.infWt i τ, ∃ k : ℤ, z = (k : ℂ) + ((D.R.nV : ℂ) - 1) / 2 := by
        rw [D.nbc.embAV_inf i P]
        exact D.nbc.infW_alg _ _ τ
      have hle : (D.naut.infG p.π τ).map (· + (((p.d : ℂ) - 1) / 2 - k)) ≤ D.naut.infWt i τ := by
        rw [← hB.2.2.2.2.2 τ]
        refine le_trans (List.single_le_sum (fun _ _ => Multiset.zero_le _) _ ?_)
          (List.single_le_sum (fun _ _ => Multiset.zero_le _) _ (List.mem_map_of_mem hp))
        exact List.mem_map.2 ⟨k, by simpa using hk, rfl⟩
      refine ⟨(Multiset.nodup_of_le hle hW.1).of_map _, fun z hz => ?_⟩
      obtain ⟨n, hn⟩ := hW.2 _ (Multiset.mem_of_le hle (Multiset.mem_map_of_mem _ hz))
      exact ⟨n, by push_cast at hn ⊢; linear_combination hn⟩
    · congr 1
      push_cast
      ring
  obtain ⟨r, c, s, f⟩ := hreal.congr D.nd D.naut i hB.2.2.1 fun _ => rfl
  exact ⟨r, c, s, f⟩

end GlobalTheory.BCAllPlaces

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMemThPsiOfMemSpan
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum
  IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries
open Formalism.IndefR.Links
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx)
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.SeriesTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Ser

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

open Classical in

def specXi (ρ : Setup X) (Y : NExp D.R D.host D.what₂ D.LL0 N X) (i : X.Tw) (j : Fin D.R.m) (b : Bool) (k : ℕ)
    (Q : Finset (Pl D.host.E)) (M : ℕ) (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ) (h : GA D (Vc D j))
    (P : PolF D (Wc D j).rank (Vc D j).rank) : GA D (Wc D j) → ℂ :=
  ∑ a, ρ.eOk i b k (χ (Multiplicative.ofAdd (spread Y i Q M (ρ.ch i) a)) : X.Ok i k) • ρ.xi i j b Y Q M h P a

theorem exists_mem_thPsi_of_mem_span {ρ : Setup X} {hρ : ρ.Good} {Y : NExp D.R D.host D.what₂ D.LL0 N X} {i : X.Tw}
    {j : Fin D.R.m} {b : Bool} {rd : Rd ρ Y i j b} (T : CellTie hρ Y rd) (hR : RatTwist hρ rd) {k : ℕ}
    {Q : Finset (Pl D.host.E)} {ψ : G D.host.E N.Om →* (X.Ok i k)ˣ} (hψ : TwOK i k Q ψ) (hQ : ClsQ (D := D) Q)
    (d : Y.Dat i ((j : ℕ) + 1) b) {f : GA D (Wc D j) → ℂ}
    (hf : f ∈ Submodule.span (ρ.eOk i b k).range (ρ.gens i j b k Q ψ (T.cls d) (T.coef d))) :
    ∃ z ∈ Formalism.MainNotions.IntegralHeckeForms.ThPsi Y i ((j : ℕ) + 1) b k Q ψ {d}, rdK rd hρ k z = f := by
  induction hf using Submodule.span_induction with
  | mem s hs =>
    obtain ⟨z, hz⟩ := hR k Q ψ hψ hQ _ _ _ (T.dat d) hs
    refine ⟨z, Submodule.subset_span ?_, hz⟩
    exact Set.mem_biUnion (Set.mem_singleton d) ((T.thPsi_iff k Q ψ hψ d z).2 (hz ▸ hs))
  | zero => exact ⟨0, zero_mem _, map_zero _⟩
  | add f g _ _ hf hg =>
    obtain ⟨z, hz, rfl⟩ := hf
    obtain ⟨z', hz', rfl⟩ := hg
    exact ⟨z + z', add_mem hz hz', map_add _ _ _⟩
  | smul c f _ hf =>
    obtain ⟨z, hz, rfl⟩ := hf
    obtain ⟨c', hc'⟩ := c.2
    refine ⟨c' • z, Submodule.smul_mem _ _ hz, ?_⟩
    rw [map_smulₛₗ]
    change ρ.eOk i b k c' • rdK rd hρ k z = (c : ℂ) • rdK rd hρ k z
    rw [hc']

end Ser

end GlobalTheory.SeriesTie

namespace GlobalTheory.SeriesTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section SpecLoc

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

open Classical in

def specLoc (ρ : Setup X) (Y : NExp D.R D.host D.what₂ D.LL0 N X) (i : X.Tw) (j : Fin D.R.m) (b : Bool) (k : ℕ)
    (Q : Finset (Pl D.host.E)) (M : ℕ) (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ)
    (PP : ↥(half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M))) (y : Matrix (Fin (Wc D j).rank) (Fin (Vc D j).rank) (kP PP.1)) : ℂ :=
  ∑ c : ZMod (X.l i ^ M), ρ.eOk i b k (χ (Multiplicative.ofAdd (spread Y i Q M (ρ.ch i) (Pi.single PP c))) : X.Ok i k) *
    ((Base.univFam (univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc) (ρ.β j) PP.1 c y : ℚ) : ℂ)

def specSer (ρ : Setup X) (Y : NExp D.R D.host D.what₂ D.LL0 N X) (i : X.Tw) (j : Fin D.R.m) (b : Bool) (k : ℕ)
    (Q : Finset (Pl D.host.E)) (M : ℕ) (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ) (h : GA D (Vc D j))
    (P : PolF D (Wc D j).rank (Vc D j).rank) : GA D (Wc D j) → ℂ :=
  twistBy (Wc D j) (ρ.tw i b k Q (χ.comp (Y.delU i Q M))).chi
    (series (ρ.B i j b).F (ρ.om i j b 1) ((ρ.B i j b).vecAt (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) (specLoc ρ Y i j b k Q M χ)) h P)

end SpecLoc

end GlobalTheory.SeriesTie

namespace GlobalTheory.SeriesTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Ser2

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

open Classical in
theorem rdK_specU_grpSum {ρ : Setup X} (hρ : ρ.Good) {Y : NExp D.R D.host D.what₂ D.LL0 N X} {i : X.Tw}
    {j : Fin D.R.m} {b : Bool} (rd : Rd ρ Y i j b) (k : ℕ) (Q : Finset (Pl D.host.E)) (M : ℕ)
    (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ)
    (x : (↥(half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) → ZMod (X.l i ^ M)) → Y.Fm i ((j : ℕ) + 1) b) :
    rdK rd hρ k (Formalism.MainNotions.IntegralHeckeForms.specU Y i ((j : ℕ) + 1) b Q M k χ (grpSum Y (ρ.ch i) Q M x)) =
      ∑ a, ρ.eOk i b k (χ (Multiplicative.ofAdd (spread Y i Q M (ρ.ch i) a)) : X.Ok i k) • rd (x a) := by
  rw [grpSum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Formalism.MainNotions.IntegralHeckeForms.specU, LinearMap.coe_comp, Function.comp_apply, LinearMap.lTensor_tmul,
    LinearEquiv.coe_coe, TensorProduct.comm_tmul, AlgHom.toLinearMap_apply, AddMonoidAlgebra.lift_single, one_smul,
    MonoidHom.coe_comp, Units.coeHom_apply]
  rw [rdK_tmul]

end Ser2

end GlobalTheory.SeriesTie
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockHarmonicLatticeFgAndSpansValueSpace
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ExportSeries.HarmLattice

theorem fg_span_comap {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (O : Subring ℂ)
    (H : Submodule ℂ V) (f : V →ₗ[ℂ] W) (hinj : ∀ P ∈ H, f P = 0 → P = 0) (L : Submodule O W) (hfg : L.FG)
    (hsp : Submodule.span ℂ (L : Set W) = H.map f) :
    (H.restrictScalars O ⊓ L.comap (f.restrictScalars O)).FG ∧
      Submodule.span ℂ ((H.restrictScalars O ⊓ L.comap (f.restrictScalars O) : Submodule O V) : Set V) = H := by
  have him : f '' ((H.restrictScalars O ⊓ L.comap (f.restrictScalars O) : Submodule O V) : Set V) = L := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx.2
    · intro hy
      have : y ∈ H.map f := hsp ▸ Submodule.subset_span hy
      obtain ⟨x, hx, rfl⟩ := this
      exact ⟨x, ⟨hx, hy⟩, rfl⟩
  constructor
  · refine Submodule.fg_of_fg_map_of_fg_inf_ker (f.restrictScalars O) ?_ ?_
    · have : (H.restrictScalars O ⊓ L.comap (f.restrictScalars O)).map (f.restrictScalars O) = L :=
        SetLike.coe_injective him
      rw [this]
      exact hfg
    · have : (H.restrictScalars O ⊓ L.comap (f.restrictScalars O)) ⊓ LinearMap.ker (f.restrictScalars O) = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        exact hinj x hx.1.1 hx.2
      rw [this]
      exact Submodule.fg_bot
  · have hle : Submodule.span ℂ ((H.restrictScalars O ⊓ L.comap (f.restrictScalars O) : Submodule O V) : Set V) ≤ H :=
      Submodule.span_le.2 fun x hx => hx.1
    refine le_antisymm hle fun x hx => ?_
    have : f x ∈ (Submodule.span ℂ ((H.restrictScalars O ⊓ L.comap (f.restrictScalars O) : Submodule O V) : Set V)).map f := by
      rw [Submodule.map_span, him, hsp]
      exact Submodule.mem_map_of_mem hx
    obtain ⟨y, hy, e⟩ := this
    have h0 : x - y = 0 := hinj _ (sub_mem hx (hle hy)) (by rw [map_sub, e, sub_self])
    rw [sub_eq_zero.1 h0]
    exact hy

variable {D : D7} {n : ℕ}

def cf (lam : D.what₂.Tau → DomWeight n) : VV ℂ lam →ₗ[ℂ] (GLR D n → ℂ) where
  toFun F := coefFn (RingHom.id ℂ) lam (F : Pol ℂ D.what₂.Tau n)
  map_add' F G := by
    funext x
    simp only [coefFn, Submodule.coe_add, map_add, Pi.add_apply, mul_add]
  map_smul' c F := by
    funext x
    simp only [coefFn, Submodule.coe_smul, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval₂Hom_C, RingHom.id_apply,
      Pi.smul_apply, smul_eq_mul]
    ring

theorem coefFn_eq {K : Type} [Field K] (σ : K →+* ℂ) (lam : D.what₂.Tau → DomWeight n) (F : VV K lam) :
    coefFn σ lam (F : Pol K D.what₂.Tau n) = cf lam (GlobalTheory.CoefModel.mapVV σ lam F) := by
  funext x
  change _ = coefFn (RingHom.id ℂ) lam (MvPolynomial.map σ F.1) x
  simp only [coefFn, MvPolynomial.eval₂Hom_map_hom, RingHom.id_comp]

variable {K : Type} [Field K] [NumberField K] {σ : K →+* ℂ} {emb : D.what₂.Tau → (D.host.E →+* K)} {O : Subring ℂ}

theorem coefLatFn_fg (hc : IsCoefRing σ emb O) (lam : D.what₂.Tau → DomWeight n)
    {M : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (hM : Submodule.IsLattice D.host.E M) :
    (coefLatFn σ emb O lam M).FG := by
  obtain ⟨s, hs, e⟩ := Submodule.fg_def.1 (nabAtr_isLattice emb lam M hM).fg
  refine Submodule.fg_def.2 ⟨(fun F => cf lam (GlobalTheory.CoefModel.mapVV σ lam F)) '' s, hs.image _, le_antisymm ?_ ?_⟩
  · refine Submodule.span_mono ?_
    rintro _ ⟨F, hF, rfl⟩
    exact ⟨F, e ▸ Submodule.subset_span hF, (coefFn_eq σ lam F).symm⟩
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨F, hF, rfl⟩
    rw [coefFn_eq, SetLike.mem_coe]
    rw [← e] at hF
    induction hF using Submodule.span_induction with
    | mem F h => exact Submodule.subset_span ⟨F, h, rfl⟩
    | zero => rw [map_zero, map_zero]; exact zero_mem _
    | add _ _ _ _ h1 h2 => rw [map_add, map_add]; exact add_mem h1 h2
    | smul a F _ h1 =>
      rw [← algebraMap_smul K a F, LinearMap.map_smulₛₗ, map_smul]
      exact Submodule.smul_mem _ (⟨σ a, hc.int a⟩ : O) h1

theorem span_coefLatFn (lam : D.what₂.Tau → DomWeight n)
    {M : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (hM : Submodule.IsLattice D.host.E M) :
    Submodule.span ℂ (coefLatFn σ emb O lam M : Set (GLR D n → ℂ)) =
      Submodule.span ℂ {φ | ∃ F : VV ℂ lam, φ = coefFn (RingHom.id ℂ) lam (F : Pol ℂ D.what₂.Tau n)} := by
  rw [coefLatFn, Submodule.span_span_of_tower]
  refine le_antisymm (Submodule.span_mono ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨F, -, rfl⟩
    exact ⟨_, coefFn_eq σ lam F⟩
  · rintro _ ⟨F, rfl⟩
    have key : ∀ G : VV K lam, cf lam (GlobalTheory.CoefModel.mapVV σ lam G) ∈
        Submodule.span ℂ {φ | ∃ F ∈ nabAtr emb lam M, φ = coefFn σ lam (F : VV K lam)} := by
      intro G
      have hG : G ∈ Submodule.span K (nabAtr emb lam M : Set (VV K lam)) := by
        rw [(nabAtr_isLattice emb lam M hM).span_eq_top]; trivial
      induction hG using Submodule.span_induction with
      | mem F h => exact Submodule.subset_span ⟨F, h, (coefFn_eq σ lam F).symm⟩
      | zero => rw [map_zero, map_zero]; exact zero_mem _
      | add _ _ _ _ h1 h2 => rw [map_add, map_add]; exact add_mem h1 h2
      | smul a F _ h1 =>
        rw [LinearMap.map_smulₛₗ, map_smul]
        exact Submodule.smul_mem _ _ h1
    have hF : F ∈ Submodule.span ℂ (Set.range fun i => GlobalTheory.CoefModel.mapVV σ lam (bVV K lam i)) := by
      rw [GlobalTheory.CoefModel.span_mapVV]; trivial
    change cf lam F ∈ _
    have := Submodule.mem_map_of_mem (f := cf lam) hF
    rw [Submodule.map_span] at this
    refine Submodule.span_le.2 ?_ this
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact key _

theorem harmLat_fg_span : ∀ (D : D7) (m n : ℕ) (w : Weight D n) (B : GLR D n) (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (emb : D.what₂.Tau → (D.host.E →+* K)) (O : Subring ℂ) (M : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), w.Good → (∀ τ, w.p τ + w.q τ ≤ m) → IsCoefRing σ emb O → Submodule.IsLattice D.host.E M → (harmLat σ emb O m w B M).FG ∧ Submodule.span ℂ (harmLat σ emb O m w B M : Set (PolF D m n)) = harm m w B := by
  intro D m n w B K _ _ σ emb O M hw hm hc hM
  exact fg_span_comap O (harm m w B) (harmFn m w B) (GlobalTheory.T.harmonic_polynomial_eq_zero_of_function D m n w B hw hm) _ (coefLatFn_fg hc w.lam hM)
    ((span_coefLatFn w.lam hM).trans (GlobalTheory.T.fockHarmonicValueSpace_map_eq_dualWeylModuleFunctions D m n w B hw hm).symm)

end GlobalTheory.ExportSeries.HarmLattice

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisCharacterEqOneOfTrivialDegreeOneFrobenius
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.Pst
  GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory

namespace GlobalTheory.FrobTrivChar

theorem eq_one_of_frob_trivial : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]
    (φ : G E Ω →* (Qbar l)ˣ), Continuous φ →
    (∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, w.asIdeal.inertiaDeg ℤ = 1 → w.asIdeal.ramificationIdx ℤ = 1 →
      ∀ (A : ValuationSubring Ω) (σ : G E Ω), IsPlaceOver (F := E) A w → IsFrob (F := E) A (normV w) σ → φ σ = 1) →
    φ = 1 := by
  classical
  intro E Ω _ _ _ _ _ l _ φ hφ hev
  have : IsGalois E Ω := {}
  refine MonoidHom.ext fun g => ?_
  rw [MonoidHom.one_apply]
  by_contra hg
  have hV : IsOpen {x : G E Ω | φ x ≠ 1} := isOpen_ne_fun hφ continuous_const
  have hn : (fun u : G E Ω => u * g) ⁻¹' {x : G E Ω | φ x ≠ 1} ∈ nhds (1 : G E Ω) :=
    (hV.preimage (continuous_mul_const g)).mem_nhds (by simpa using hg)
  obtain ⟨L, hfd, hN, hL⟩ := (krullTopology_mem_nhds_one_iff_of_normal E Ω _).1 hn
  have hgal : IsGalois E L := {}
  have hS := Filter.eventually_cofinite.1 hev
  obtain ⟨v, hv, hf, he, B, hB, -, σ, hσ, hU⟩ := GlobalTheory.Published.cheb_holds E Ω L.fixingSubgroup
    L.fixingSubgroup_isOpen ((InfiniteGalois.normal_iff_isGalois L).2 hgal) g hS.toFinset
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hv
  have h1 := hL hU
  simp only [Set.mem_preimage, Set.mem_setOf_eq, inv_mul_cancel_right] at h1
  exact h1 (hv hf he B σ hB hσ)

end GlobalTheory.FrobTrivChar
end
end

