import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0170
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PolarizedGaloisRep
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0053
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0170
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0036
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspidalTwistRamifiedCharNeSelf
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0606
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0222
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0187
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0020

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AwayRepIsoLoc
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCGal

open Formalism.MainNotions.SumRepresentations.At GlobalTheory.TwistLG

section Rep

variable {Γ : Type} [Group Γ] {k : Type} [Field k] {a b : ℕ}

theorem sumRep_val (ρ : Γ →* GL (Fin a) k) (ρ' : Γ →* GL (Fin b) k) (g : Γ) :
    ((sumRep ρ ρ' g : GL (Fin (a + b)) k) : Matrix (Fin (a + b)) (Fin (a + b)) k) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (ρ g : Matrix (Fin a) (Fin a) k) 0 0 (ρ' g : Matrix (Fin b) (Fin b) k)) := rfl

theorem cont_sumRep [TopologicalSpace Γ] [TopologicalSpace k] [IsTopologicalRing k]
    (ρ : Γ →* GL (Fin a) k) (ρ' : Γ →* GL (Fin b) k)
    (c : Continuous fun g => ((ρ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k))
    (c' : Continuous fun g => ((ρ' g : GL (Fin b) k) : Matrix (Fin b) (Fin b) k)) :
    Continuous fun g => ((sumRep ρ ρ' g : GL (Fin (a + b)) k) : Matrix (Fin (a + b)) (Fin (a + b)) k) := by
  simp only [sumRep_val]
  exact (c.matrix_fromBlocks continuous_const continuous_const c').matrix_reindex _ _

theorem ss_sumRep (ρ : Γ →* GL (Fin a) k) (ρ' : Γ →* GL (Fin b) k) (h : IsSSRep ρ) (h' : IsSSRep ρ') :
    IsSSRep (sumRep ρ ρ') := by
  refine GlobalTheory.Proof.SemisimpleRepresentationIntegralConjugate.isSSRep_of_prod ((LinearEquiv.funCongrLeft k k finSumFinEquiv).trans
      (LinearEquiv.sumArrowLequivProdArrow _ _ k k)) (fun g v => ?_) h h'
  rw [sumRep_val]
  ext i <;>
    simp [Matrix.submatrix_mulVec_equiv, Matrix.fromBlocks_mulVec, LinearMap.funLeft] <;> rfl

theorem ss_zero (ρ : Γ →* GL (Fin 0) k) : IsSSRep ρ := fun W _ =>
  ⟨⊥, fun g v hv => by simp [Subsingleton.elim v 0], by rw [Subsingleton.elim W ⊤]; exact isCompl_top_bot⟩

end Rep

section Glob

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) (i : N.Loc)

def AwayRep (m : ℕ) (L : ∀ w, A.LP w) : Prop :=
  ∃ r : Formalism.ConjugateSelfDual.G H.E N.Om →* GL (Fin m) (Qbar (N.l i)), ContQ N i r ∧ IsSSRep r ∧
    ∀ w, w ∉ placesOver H.E (N.l i) → A.wdOf i r w = L w

theorem eq_lpZero {w : PlE H} (x : A.LP w) (hu : A.unr x) (hd : A.lpDim x = 0) : x = A.lpZero w := by
  have h1 : A.frobEig x = 0 := Multiset.card_eq_zero.1 (by rw [A.frobEig_card _ hu, hd])
  have h2 := A.unr_eq_lpUnr _ (A.lpZero_unr w)
  rw [A.frobEig_zero] at h2
  rw [A.unr_eq_lpUnr _ hu, h1, h2]

theorem lpTw_lpZero (w : PlE H) (c : ℝ) : A.lpTw (A.lpZero w) c = A.lpZero w :=
  eq_lpZero N A _ ((A.unr_tw _ _).2 (A.lpZero_unr w)) (by rw [A.lpDim_tw, A.lpDim_zero])

theorem awayRep_zero : AwayRep N A i 0 A.lpZero := by
  refine ⟨1, continuous_const, ss_zero _, fun w hw => eq_lpZero N A _ ?_ (A.wdOf_dim i _ w)⟩
  exact (A.wdOf_unr i _ w hw continuous_const).2 fun σ _ => rfl

theorem AwayRep.congr {m m' : ℕ} {L L' : ∀ w, A.LP w} (h : AwayRep N A i m L) (hm : m = m')
    (hL : ∀ w, L w = L' w) : AwayRep N A i m' L' := by
  subst hm
  obtain ⟨r, c, s, f⟩ := h
  exact ⟨r, c, s, fun w hw => (f w hw).trans (hL w)⟩

theorem AwayRep.sum (hGal : TieGal N A) {m m' : ℕ} {L L' : ∀ w, A.LP w} (h : AwayRep N A i m L)
    (h' : AwayRep N A i m' L') : AwayRep N A i (m + m') fun w => A.lpSum (L w) (L' w) := by
  obtain ⟨r, c, s, f⟩ := h
  obtain ⟨r', c', s', f'⟩ := h'
  obtain ⟨-, -, hsum, -⟩ := hGal.2.2.2 i
  refine ⟨sumRep r r', cont_sumRep r r' c c', ss_sumRep r r' s s', fun w hw => ?_⟩
  rw [(hsum m m' r r' c c').2.1 w (Or.inl hw) (Or.inl hw), f w hw, f' w hw]

theorem param_int (hLP : TieLP N A) {a : ℕ} (π : A.CG a) (w : PlE H) (u t : ℝ) :
    A.lpChar (A.lpChar (A.lpTw (A.locG π w) u) (A.lpTw (A.locG A.etaT w) (1 / 2)))
      (A.lpTw (A.locG A.etaTinv w) (t - 1 / 2)) = A.lpTw (A.locG π w) (u + t) := by
  have d1 : A.lpDim (A.locG A.etaT w) = 1 := A.locG_dim _ w
  have d2 : A.lpDim (A.locG A.etaTinv w) = 1 := A.locG_dim _ w
  set X := A.lpTw (A.locG π w) u
  have c3a := (hLP w (A.lpChar X (A.lpTw (A.locG A.etaT w) (1 / 2))) (A.lpZero w) (A.locG A.etaTinv w)
    (A.locG A.etaTinv w) (t - 1 / 2) d2 d2).2.2.1
  have c3b := (hLP w X (A.lpZero w) (A.locG A.etaT w) (A.locG A.etaT w) (1 / 2) d1 d1).2.2.1
  have c2 := (hLP w (A.lpChar X (A.locG A.etaT w)) (A.lpZero w) (A.locG A.etaTinv w) (A.locG A.etaTinv w)
    (1 / 2) d2 d2).2.1
  have c4 := (hLP w X (A.lpZero w) (A.locG A.etaT w) (A.locG A.etaTinv w) 0 d1 d2).2.2.2.1
  have c5 := (hLP w X (A.lpZero w) (A.locG A.etaT w) (A.locG A.etaTinv w) 0 d1 d2).2.2.2.2.1
  rw [c3a, c3b, c2, c4, etaT_char_etaTinv N A w, c5, A.lpTw_add, A.lpTw_add]
  congr 1
  ring

end Glob

section Piece

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) (i : N.Loc)

theorem eta_alg (hAut : TieAut N A) (m : ℤ) (τ : H.E →+* ℂ) :
    (∀ z ∈ A.infG A.etaT τ, ∃ k : ℤ, z + (((m : ℝ) + 1 / 2 : ℝ) : ℂ) = (k : ℂ)) ∧
    (∀ z ∈ A.infG A.etaTinv τ, ∃ k : ℤ, z + (((m : ℝ) + 1 / 2 : ℝ) : ℂ) = (k : ℂ)) := by
  obtain ⟨h1, h2⟩ := hAut.2.1 τ
  rw [h2]
  rcases h1 with h1 | h1 <;> rw [h1] <;> refine ⟨fun z hz => ?_, fun z hz => ?_⟩ <;>
    simp only [Multiset.map_singleton, Multiset.mem_singleton] at hz <;> subst hz
  · exact ⟨m + 1, by push_cast; ring⟩
  · exact ⟨m, by push_cast; ring⟩
  · exact ⟨m, by push_cast; ring⟩
  · exact ⟨m + 1, by push_cast; ring⟩

theorem awayRep_piece (hLP : TieLP N A) (hAut : TieAut N A) (hGal : TieGal N A) (hG : exists_galois_rep_local_global_compatible N A)
    {a : ℕ} (ha : 1 ≤ a) (π : A.CG a) (hc : A.csd π) (m : ℤ)
    (hinf : ∀ τ, (A.infG π τ).Nodup ∧
      ∀ z ∈ A.infG π τ, ∃ n : ℤ, z + (((m : ℝ) / 2 : ℝ) : ℂ) = (n : ℂ) + ((a : ℂ) - 1) / 2) :
    AwayRep N A i a fun w => A.lpTw (A.locG π w) ((m : ℝ) / 2 + (1 - (a : ℝ)) / 2) := by
  obtain ⟨-, -, -, htw⟩ := hGal.2.2.2 i
  rcases Int.even_or_odd' m with ⟨k, hk | hk⟩ <;> subst hk
  ·
    have hralg : A.ralg π := (A.ralg_def π).2 fun τ => ⟨(hinf τ).1, fun z hz => by
      obtain ⟨n, hn⟩ := (hinf τ).2 z hz
      exact ⟨n - k, by push_cast at hn ⊢; linear_combination hn⟩⟩
    obtain ⟨ρ1, c1, ss1, away1, -⟩ := (hG i).1 a ha π hc hralg
    obtain ⟨χA, cA, awayA, -⟩ := (hG i).2.2 A.etaT (1 / 2) fun τ z hz => by
      obtain ⟨n, hn⟩ := (eta_alg N A hAut 0 τ).1 z hz
      exact ⟨n, by push_cast at hn ⊢; linear_combination hn⟩
    obtain ⟨χB, cB, awayB, -⟩ := (hG i).2.2 A.etaTinv ((k : ℝ) - 1 / 2) fun τ z hz => by
      obtain ⟨n, hn⟩ := (eta_alg N A hAut (k - 1) τ).2 z hz
      exact ⟨n, by push_cast at hn ⊢; linear_combination hn⟩
    let ρ2 := twGL ρ1 (Matrix.GeneralLinearGroup.det.comp χA)
    have c2 : ContQ N i ρ2 := cont_twGL ρ1 χA c1 cA
    refine ⟨twGL ρ2 (Matrix.GeneralLinearGroup.det.comp χB), cont_twGL ρ2 χB c2 cB,
      isSSRep_twGL _ _ (isSSRep_twGL _ _ ss1), fun w hw => ?_⟩
    rw [(htw a ρ2 χB c2 cB).2.1 w (Or.inl hw) (Or.inl hw), (htw a ρ1 χA c1 cA).2.1 w (Or.inl hw) (Or.inl hw),
      (away1 w hw).1, awayA w hw, awayB w hw, param_int N A hLP]
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
    obtain ⟨ρ1, c1, ss1, away1, -⟩ := (hG i).1 a ha _ hcsd hralg
    obtain ⟨χ1, cχ, awayχ, -⟩ := (hG i).2.2 A.etaTinv ((k : ℝ) + 1 / 2) (eta_alg N A hAut k · |>.2)
    refine ⟨twGL ρ1 (Matrix.GeneralLinearGroup.det.comp χ1), cont_twGL ρ1 χ1 c1 cχ, isSSRep_twGL _ _ ss1,
      fun w hw => ?_⟩
    rw [(htw a ρ1 χ1 c1 cχ).2.1 w (Or.inl hw) (Or.inl hw), (away1 w hw).1, awayχ w hw, param_twist N A hLP]
    congr 1
    push_cast
    ring

end Piece

section List

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) (i : N.Loc)

theorem awayRep_isoLoc (hGal : TieGal N A) (c : ℝ) (Pa : List (Part A.CG))
    (h : ∀ p ∈ Pa, ∀ k < p.d, AwayRep N A i p.a fun w =>
      A.lpTw (A.locG p.π w) (((p.d : ℝ) - 1) / 2 - k + c)) :
    AwayRep N A i (rankIso N A Pa) fun w => A.lpTw (isoLoc N A Pa w) c := by
  induction Pa with
  | nil =>
    exact (awayRep_zero N A i).congr N A i rfl fun w => (lpTw_lpZero N A w c).symm
  | cons p Pa ih =>
    have h1 : ∀ ks : List ℝ, (∀ k ∈ ks, ∃ n : ℕ, n < p.d ∧ (n : ℝ) = k) → AwayRep N A i (p.a * ks.length)
        fun w => A.lpTw (ks.foldr
        (fun (k : ℝ) acc => A.lpSum (A.lpTw (A.locG p.π w) (((p.d : ℝ) - 1) / 2 - k)) acc) (A.lpZero w)) c := by
      intro ks hks
      induction ks with
      | nil => exact (awayRep_zero N A i).congr N A i (by simp) fun w => (lpTw_lpZero N A w c).symm
      | cons k ks ihk =>
        obtain ⟨n, hn, rfl⟩ := hks k List.mem_cons_self
        refine ((h p List.mem_cons_self n hn).sum N A i hGal
          (ihk fun k' hk' => hks k' (List.mem_cons_of_mem _ hk'))).congr N A i
          (by rw [List.length_cons, mul_add, mul_one, add_comm]) fun w => ?_
        rw [List.foldr_cons, A.lpTw_sum, A.lpTw_add]
    have h2 := h1 ((List.range p.d : List ℕ) : List ℝ) fun k hk => by
      simp [Lean.Internal.coeM] at hk
      obtain ⟨n, hn, rfl⟩ := hk
      exact ⟨n, hn, rfl⟩
    refine (h2.sum N A i hGal (ih fun q hq => h q (List.mem_cons_of_mem _ hq))).congr N A i
      (by simp [rankIso, Lean.Internal.coeM]) fun w => ?_
    simp only [isoLoc, spehLoc, List.foldr_cons, A.lpTw_sum]

end List

theorem main : ∀ D : D7, Formalism.MainNotions.SumRepresentations.tie0 D → Formalism.MainNotions.SumRepresentations.adm2 D → Formalism.MainNotions.SumRepresentations.adm7 D → ∀ i, GalIso D.nd D.naut i := by
  intro D hT hG _ i P Pa hB
  obtain ⟨hLP, hAut, hGal⟩ := hT
  have hreal := awayRep_isoLoc D.nd D.naut i hGal ((1 - (D.R.nV : ℝ)) / 2) Pa fun p hp k hk => by
    obtain ⟨ha, -, hc⟩ := hB.1 p hp
    refine (awayRep_piece D.nd D.naut i hLP hAut hGal hG ha p.π hc
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
  exact (hreal.congr D.nd D.naut i hB.2.2.1 fun _ => rfl)

end GlobalTheory.BCGal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlocksLtOfParabolicUnipotentRadicalNeBot
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

namespace GlobalTheory.UnipRadProper

theorem blocks_lt_of_unipRad_ne_bot : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n), unipRad k e ≠ ⊥ → ∀ a, d a < n := by
  intro k _ _ _ _ n s d e h a
  by_contra hle
  push_neg at hle
  apply h
  have hcard : ∑ b, d b = n := by simpa using (Fintype.card_congr e)
  have hzero : ∀ b, b ≠ a → d b = 0 := by
    intro b hb
    have h2 : d a + d b ≤ ∑ c, d c :=
      Finset.add_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ a) (Finset.mem_univ b) (Ne.symm hb)
    omega
  have hblk : ∀ (b : Fin s) (j : Fin (d b)), b = a := by
    intro b j
    by_contra hb
    exact (hzero b hb ▸ j).elim0
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  ext i j
  obtain ⟨⟨b, i⟩, rfl⟩ := e.surjective i
  obtain ⟨⟨c, j⟩, rfl⟩ := e.surjective j
  obtain rfl := hblk b i
  obtain rfl := hblk c j
  rw [(mem_unipRad.1 hg).2]
  simp [Matrix.one_apply]

end GlobalTheory.UnipRadProper
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjSPV
section
open NumberField IsDedekindDomain ReciprocityTheory.Aut

namespace GlobalTheory.TypeTame

noncomputable abbrev conjSP {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) : SplitPlace L :=
  ⟨s.v, s.i.comp (IsCMField.complexConj L).toAlgHom⟩

theorem conjSP_i {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (x : L) :
    (conjSP s).i x = s.i (IsCMField.complexConj L x) := rfl

end GlobalTheory.TypeTame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspidalJacquetSubquotientAtMostOneNonemptyBlock
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SmGL.CuspRow

theorem block_unique_of_isCuspidal : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (d : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL (Fin d) k) V) (s' : ℕ) (b : Fin s' → ℕ) (f : (Σ j, Fin (b j)) ≃ Fin d) (X : Fin s' → Type) [∀ j, AddCommGroup (X j)] [∀ j, Module ℂ (X j)] (ρ : ∀ j, Representation ℂ (GL (Fin (b j)) k) (X j)), GlobalTheory.SmGL.IsCuspidal σ → (∀ j, Nontrivial (X j)) → GlobalTheory.SmGL.IsSubquotient (GlobalTheory.SmGL.piTensor ρ) (GlobalTheory.SmGL.jac f σ) → ∀ j j', 0 < b j → 0 < b j' → j = j' := by
  intro k _ _ _ _ d V _ _ σ s' b f X _ _ ρ hσ hX hsub j j' hj hj'
  by_contra hne
  have hU : GlobalTheory.SmGL.unipRad k f ≠ ⊥ := by
    refine GlobalTheory.SmGL.CuspMax.unipRad_ne_bot_iff.2 ?_
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨f ⟨j, ⟨0, hj⟩⟩, f ⟨j', ⟨0, hj'⟩⟩, by rwa [GlobalTheory.SmGL.blk_apply, GlobalTheory.SmGL.blk_apply]⟩
    · exact ⟨f ⟨j', ⟨0, hj'⟩⟩, f ⟨j, ⟨0, hj⟩⟩, by rwa [GlobalTheory.SmGL.blk_apply, GlobalTheory.SmGL.blk_apply]⟩
  have hs := hσ.2 s' b f hU
  have hn := GlobalTheory.ProdSupport.nontrivial_piTensor X hX
  obtain ⟨S, g, hg⟩ := hsub
  have hS : Subsingleton S.toSubmodule := inferInstance
  exact not_subsingleton _ (Function.Surjective.subsingleton hg)

end GlobalTheory.SmGL.CuspRow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspidalTwistRamifiedCharNeSelfStatement
section
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_twist_ramified_char_ne_self : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ (π : CG E a) (η : HChar E) (v : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ), π.HasSat v B → ¬ η.UnrAt v → π.twist η ≠ π := by
  first | exact @GlobalTheory.TwistRamified.twist_ne | exact GlobalTheory.TwistRamified.twist_ne | (intros; apply GlobalTheory.TwistRamified.twist_ne <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeRhamCharacterTwistIffLocalEmbedding
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.TwistBridgeDR

open Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.TwistAbove

theorem twGL_eq {Γ K : Type} [Group Γ] [CommRing K] {a : ℕ} (r : Γ →* GL (Fin a) K) (μ : Γ →* Kˣ) :
    Formalism.MainNotions.SumRepresentations.At.twGL r μ = GlobalTheory.TwistAbove.twGL μ r := by
  ext g i j
  simp [Formalism.MainNotions.SumRepresentations.At.twGL, GlobalTheory.TwistAbove.twGL, Algebra.algebraMap_eq_smul_one, Matrix.smul_apply]

theorem characterAsRankOneRep_det_comp {Γ K : Type} [Group Γ] [CommRing K] (c : Γ →* GL (Fin 1) K) :
    GlobalTheory.TripleGal.rk1 (Matrix.GeneralLinearGroup.det.comp c) = c := by
  ext g i j
  fin_cases i; fin_cases j
  simp [GlobalTheory.TripleGal.rk1, Matrix.det_unique]

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω Gw O) {a : ℕ}

theorem repE_twGL' {L : FinExt l} (χ : ↥Gw →* (↥L.1)ˣ) (s : ↥Gw →* GL (Fin a) ↥L.1)
    (g : ↥(GK Bw.Kw)) (x : Fin a → ↥L.1) :
    Bw.repE L (GlobalTheory.TwistAbove.twGL χ s) g x = ((χ (Bw.e.symm g) : (↥L.1)ˣ) : ↥L.1) • Bw.repE L s g x := by
  change Matrix.toLin' ((GlobalTheory.TwistAbove.twGL χ s (Bw.e.symm g) : GL (Fin a) ↥L.1) : Matrix (Fin a) (Fin a) ↥L.1) x =
    ((χ (Bw.e.symm g) : (↥L.1)ˣ) : ↥L.1) •
      Matrix.toLin' ((s (Bw.e.symm g) : GL (Fin a) ↥L.1) : Matrix (Fin a) (Fin a) ↥L.1) x
  rw [twGL_val, Matrix.toLin'_apply, Matrix.toLin'_apply]
  exact Matrix.smul_mulVec _ _ _

theorem isModel_untwist {L : FinExt l} {r : ↥Gw →* GL (Fin a) (Om l)} {c : ↥Gw →* GL (Fin 1) (Om l)}
    {t : ↥Gw →* GL (Fin a) ↥L.1} {cc : ↥Gw →* GL (Fin 1) ↥L.1}
    (mt : IsModel Bw (Formalism.MainNotions.SumRepresentations.At.twGL r (Matrix.GeneralLinearGroup.det.comp c)) L t)
    (mc : IsModel Bw c L cc) : IsModel Bw r L (GlobalTheory.TwistAbove.twGL (chr cc)⁻¹ t) := by
  refine ⟨mt.1, ?_⟩
  ext g i j
  have e1 := congrArg (fun f : ↥Gw →* GL (Fin a) (Om l) =>
    ((f g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i j) mt.2
  have e2 := congrArg (fun f : ↥Gw →* GL (Fin 1) (Om l) =>
    ((f g : GL (Fin 1) (Om l)) : Matrix (Fin 1) (Fin 1) (Om l)) 0 0) mc.2
  rw [twGL_eq] at e1
  simp only [mapRep] at e1 e2 ⊢
  simp [Matrix.det_unique] at e1 e2 ⊢
  have hne : ((c g : GL (Fin 1) (Om l)) : Matrix (Fin 1) (Fin 1) (Om l)) 0 0 ≠ 0 := by
    have := (Matrix.GeneralLinearGroup.det (c g)).ne_zero
    simpa [Matrix.det_unique] using this
  rw [e1, e2, inv_mul_cancel_left₀ hne]

theorem isdRAt_twist_iff : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] (Gw : Subgroup (Ω ≃ₐ[E] Ω)) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) (a : ℕ) (r : ↥Gw →* GL (Fin a) (Loc.Om l)) (c : ↥Gw →* GL (Fin 1) (Loc.Om l)), Continuous (fun g => ((r g : GL (Fin a) (Loc.Om l)) : Matrix (Fin a) (Fin a) (Loc.Om l))) → Continuous (fun g => ((c g : GL (Fin 1) (Loc.Om l)) : Matrix (Fin 1) (Fin 1) (Loc.Om l))) → GlobalTheory.Pst.IsdRAt P Bw c → (GlobalTheory.Pst.IsdRAt P Bw (Formalism.MainNotions.SumRepresentations.At.twGL r (Matrix.GeneralLinearGroup.det.comp c)) ↔ GlobalTheory.Pst.IsdRAt P Bw r) := by
  intro l _ P AI hT E Ω _ _ _ Gw O _ _ _ Bw a r c _ _ hc
  obtain ⟨T⟩ := hT
  obtain ⟨L₂, c₂, m₂, d₂⟩ := hc
  constructor
  · rintro ⟨L₁, t₁, m₁, d₁⟩
    have l₁ : L₁.1 ≤ (supExt L₁ L₂).1 := le_sup_left
    have l₂ : L₂.1 ≤ (supExt L₁ L₂).1 := le_sup_right
    have mt := m₁.enlarge l₁
    have mc := m₂.enlarge l₂
    have dt := (local_ext P Bw l₁ t₁).2.1.2 d₁
    have dc := (local_ext P Bw l₂ c₂).2.1.2 d₂
    set t := mapRep (IntermediateField.inclusion l₁).toRingHom t₁
    set cc := mapRep (IntermediateField.inclusion l₂).toRingHom c₂
    refine ⟨_, _, isModel_untwist Bw mt mc, ?_⟩
    have hν := repE_rank_one Bw cc
    have hρ : ∀ g x, Bw.repE (supExt L₁ L₂) t g x =
        ((chr cc (Bw.e.symm g) : (↥(supExt L₁ L₂).1)ˣ) : ↥(supExt L₁ L₂).1) •
          Bw.repE (supExt L₁ L₂) (GlobalTheory.TwistAbove.twGL (chr cc)⁻¹ t) g x := by
      intro g x
      rw [repE_twGL', smul_smul, MonoidHom.inv_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        one_smul]
    rw [← isDR_iff] at dt dc ⊢
    exact (GlobalTheory.TwistDR.isDR_twist_iff l P AI T Bw.Kw (supExt L₁ L₂) (Fin a → ↥(supExt L₁ L₂).1)
      _ _ _ _ hν hρ dc).2 dt
  · rintro ⟨L₁, r₁, m₁, d₁⟩
    have l₁ : L₁.1 ≤ (supExt L₁ L₂).1 := le_sup_left
    have l₂ : L₂.1 ≤ (supExt L₁ L₂).1 := le_sup_right
    have mc : IsModel Bw (GlobalTheory.TripleGal.rk1 (Matrix.GeneralLinearGroup.det.comp c)) (supExt L₁ L₂)
        (mapRep (IntermediateField.inclusion l₂).toRingHom c₂) := by
      rw [characterAsRankOneRep_det_comp]; exact m₂.enlarge l₂
    refine ⟨_, _, isModel_twGL Bw (r' := Formalism.MainNotions.SumRepresentations.At.twGL r (Matrix.GeneralLinearGroup.det.comp c))
      (μ := Matrix.GeneralLinearGroup.det.comp c) (fun g => by rw [twGL_eq]; exact twGL_val _ _ _)
      (m₁.enlarge l₁) mc, (twist_common Bw _ _ T).1 ((local_ext P Bw l₁ r₁).2.1.2 d₁)
        ((local_ext P Bw l₂ c₂).2.1.2 d₂)⟩

end GlobalTheory.TwistBridgeDR
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeRhamGaloisSideIffDeRhamAtLocalEmbedding
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.DeRhamRead
open Formalism.BasicNotions.Loc

theorem exists_model_of_mem {l : ℕ} [Fact l.Prime] {Γ : Type} [Group Γ] [TopologicalSpace Γ] {a : ℕ}
    (r : Γ →* GL (Fin a) (Om l)) (hr : Continuous (fun g => (r g : Matrix (Fin a) (Fin a) (Om l)))) (L : FinExt l)
    (hL : ∀ g i j, (r g : Matrix (Fin a) (Fin a) (Om l)) i j ∈ L.1) :
    ∃ ρ : Γ →* GL (Fin a) ↥L.1, Continuous (fun g => (ρ g : Matrix (Fin a) (Fin a) ↥L.1)) ∧
      mapRep (algebraMap ↥L.1 (Om l)) ρ = r := by
  let f : ↥L.1 →+* Om l := algebraMap ↥L.1 (Om l)
  let M : Γ → Matrix (Fin a) (Fin a) ↥L.1 :=
    fun g => Matrix.of fun i j => ⟨(r g : Matrix (Fin a) (Fin a) (Om l)) i j, hL g i j⟩
  have hinj : Function.Injective (f.mapMatrix : Matrix (Fin a) (Fin a) ↥L.1 →+* Matrix (Fin a) (Fin a) (Om l)) :=
    fun A B h => Matrix.ext fun i j => f.injective (by simpa using congrFun (congrFun h i) j)
  have hM : ∀ g, f.mapMatrix (M g) = (r g : Matrix (Fin a) (Fin a) (Om l)) := fun g => Matrix.ext fun i j => rfl
  let ρ : Γ →* GL (Fin a) ↥L.1 :=
    { toFun := fun g => ⟨M g, M g⁻¹,
        hinj (by rw [map_mul, hM, hM, map_one, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]),
        hinj (by rw [map_mul, hM, hM, map_one, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one])⟩
      map_one' := Units.ext (hinj (by rw [hM, map_one, Units.val_one, Units.val_one, map_one]))
      map_mul' := fun g h => Units.ext (hinj (by
        show f.mapMatrix (M (g * h)) = f.mapMatrix (M g * M h)
        rw [map_mul, hM, hM, hM, map_mul, Units.val_mul])) }
  refine ⟨ρ, ?_, ?_⟩
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    exact continuous_induced_rng.2 ((continuous_apply j).comp ((continuous_apply i).comp hr))
  · exact MonoidHom.ext fun g => Units.ext (hM g)

theorem isdRW_iff_isdRAt : ∀ (D : D7) (T : WDTie D.nd D.naut) (W : WDSide D T) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (w : HeightOneSpectrum (𝓞 D.host.E)), w ∈ placesOver D.host.E l → ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l D.host.E D.nd.Om (Dec (F := D.host.E) (D.nd.plOm.1 w)) O), GlobalTheory.Pst.Induces Bw → ∀ (a : ℕ) (r : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)), Continuous (fun g => ((r g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) → (W.IsdRW l ι r w ↔ GlobalTheory.Pst.IsdRAt (D.loc l) Bw (GlobalTheory.Pst.resDec D.nd.plOm.1 r w)) := by
  intro D T W l _ ι w hw O _ _ _ B hj a r hr
  obtain ⟨LL', hL, hmem⟩ := GlobalTheory.CompactRepField.exists_finExt_entries_mem l (G D.host.E D.nd.Om) a r hr B.LL
  obtain ⟨r₁, c₁, rfl⟩ := exists_model_of_mem r hr LL' hmem
  obtain ⟨-, H⟩ := W.loc l ι w hw _ B hj ((algebraMap ↥B.LL.1 (Om l)).comp B.toLL) (fun _ => rfl)
  have hm : GlobalTheory.Pst.IsModel B (GlobalTheory.Pst.resDec D.nd.plOm.1 (mapRep (algebraMap ↥LL'.1 (Qbar l)) r₁) w) LL'
      (r₁.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) := ⟨hL, rfl⟩
  exact (H LL' hL a r₁ c₁).2.1.trans (hm.isdRAt_iff (D.loc l)).symm

end GlobalTheory.DeRhamRead
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqOrIsConjPlaceOfOverSplitPlace
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SplitPlaceOver

theorem host_conj_eq' (D : D7) (x : D.host.E) : D.host.conj x = IsCMField.complexConj D.host.E x :=
  D.host.φ₀.injective (by
    rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply])

theorem eq_or_isConjPl : ∀ (D : D7) (s : SplitPlace D.host.E) (w : PlE D.host), NG.OverPl w s.v →
    s.w = w ∨ IsConjPl D.host w s.w := by
  intro D s w hov
  rcases GlobalTheory.SplitConjPlace.eq_or_eq_conjPlE s.w w (hov.trans s.w_under.symm) with e | e
  · exact Or.inl e.symm
  · right
    intro x y hxy
    have hy : y = IsCMField.ringOfIntegersComplexConj D.host.E x := by
      apply RingOfIntegers.ext
      rw [hxy, IsCMField.coe_ringOfIntegersComplexConj, host_conj_eq']
    rw [e, GlobalTheory.SplitConjPlace.mem_conjPlE, hy]

end GlobalTheory.SplitPlaceOver
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsWeilGroupRestrictExtensionStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weilGroup_restrict_extension : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A v) (h' : IsPlaceOver A v') (σ' : Weil h'), ∃ σ : Weil h, (∀ z : Ω, (σ : G K Ω) z = (σ' : G L Ω) z) ∧ (deg σ = 0 ↔ deg σ' = 0) := by
  first | exact @GlobalTheory.AboveL.exists_weil_restrict | exact GlobalTheory.AboveL.exists_weil_restrict | (intros; apply GlobalTheory.AboveL.exists_weil_restrict <;> assumption)
end

