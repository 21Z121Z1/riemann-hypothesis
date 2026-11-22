import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsetTwistExceptionalPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0716
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0810
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0833
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0829
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0824
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0835
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0823
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0528
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0838
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0160
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0830
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0719
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0705

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraicFormsLevelGroupEqTwistLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MtRead
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.MtLev

theorem blockSizes_sub_eq_twoBlock {n : ℕ} (r : ℕ) : (Formalism.L2.DIV.blkOf (n := n) r (n - r)) = Formalism.L2.DIV.blk2 r := by
  funext a
  unfold Formalism.L2.DIV.blkOf Formalism.L2.DIV.blk2
  split_ifs with h
  · rfl
  · have : (a.val - r) / (n - r) = 0 := Nat.div_eq_of_lt (by omega)
    rw [this]

theorem mem_levJ_iff {D : D7} {S T : HSp D} {n : ℕ} (B : Base S T) (t : Twist D Circle) (P : principalLevelFrame.RowPsi S n) (g : GAf D.host.E n) :
    frameEquiv P g ∈ B.levJ t ↔ Lev.finE S (P.ψ g) ∈ Formalism.L2.DIV.lev D.sp.cm S.gram B.F.βS (B.levS t) := Iff.rfl

end GlobalTheory.MtLev

namespace GlobalTheory.MtLev

variable {D : D7} {V : HSp D} {n : ℕ} {hF : D.host.F = maximalRealSubfield D.host.E} {P : principalLevelFrame.RowPsi V n}

theorem loc_zero (hP : IdFrame hF P) (hn : V.rank = n) {κ : GAf D.host.E n} (hκ : κ ∈ ReciprocityTheory.Aut.Umax D.host.E n)
    (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (a c : Fin V.rank) :
    Valued.v (NX.locM s κ (Fin.cast hn a) (Fin.cast hn c)) < 1 ↔
      (Formalism.L2.DIV.redFn 1 s.w (Lev.finE V (P.ψ κ)) : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.DIV.kP s.w)) a c = 0 := by
  have h := ((GlobalTheory.T.frameKeepsMatrices_splitPlace_reduction_local D V n hF P hP hn κ).2 s hκ a c).2 0
  simp only [map_zero, zero_sub, Valuation.map_neg] at h
  exact h

theorem loc_one (hP : IdFrame hF P) (hn : V.rank = n) {κ : GAf D.host.E n} (hκ : κ ∈ ReciprocityTheory.Aut.Umax D.host.E n)
    (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (a : Fin V.rank) :
    Valued.v (NX.locM s κ (Fin.cast hn a) (Fin.cast hn a) - 1) < 1 ↔
      (Formalism.L2.DIV.redFn 1 s.w (Lev.finE V (P.ψ κ)) : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.DIV.kP s.w)) a a = 1 := by
  have h := ((GlobalTheory.T.frameKeepsMatrices_splitPlace_reduction_local D V n hF P hP hn κ).2 s hκ a a).2 1
  simp only [map_one] at h
  rw [Valuation.map_sub_swap] at h
  exact h

theorem cast_surj (hn : V.rank = n) (a : Fin n) : ∃ a' : Fin V.rank, Fin.cast hn a' = a :=
  ⟨Fin.cast hn.symm a, by simp⟩

theorem inParah_iff (hP : IdFrame hF P) (hn : V.rank = n) {κ : GAf D.host.E n} (hκ : κ ∈ ReciprocityTheory.Aut.Umax D.host.E n)
    (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (r : ℕ) :
    NX.InParah s.v r (NX.locM s κ) ↔ Formalism.L2.DIV.redFn 1 s.w (Lev.finE V (P.ψ κ)) ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r) := by
  constructor
  · rintro ⟨-, h⟩ i j hij
    unfold Formalism.L2.DIV.blk2 at hij
    split_ifs at hij with h1 h2 <;> try omega
    exact (loc_zero hP hn hκ s i j).1 (h _ _ (by simpa using h2) (by simpa using h1))
  · intro h
    refine ⟨fun a b => ?_, fun a b ha hb => ?_⟩
    · obtain ⟨a', rfl⟩ := cast_surj hn a
      obtain ⟨b', rfl⟩ := cast_surj hn b
      exact ((GlobalTheory.T.frameKeepsMatrices_splitPlace_reduction_local D V n hF P hP hn κ).2 s hκ a' b').1
    · obtain ⟨a', rfl⟩ := cast_surj hn a
      obtain ⟨b', rfl⟩ := cast_surj hn b
      refine (loc_zero hP hn hκ s a' b').2 (Formalism.L2.DIV.mem_blockTri.1 h a' b' ?_)
      simp only [Fin.coe_cast] at ha hb
      unfold Formalism.L2.DIV.blk2
      rw [if_pos hb, if_neg (by omega)]
      exact Nat.zero_lt_one

end GlobalTheory.MtLev

namespace GlobalTheory.MtLev

variable {D : D7} {V : HSp D} {n : ℕ} {hF : D.host.F = maximalRealSubfield D.host.E} {P : principalLevelFrame.RowPsi V n}

def UT {m : ℕ} {k : Type} [CommRing k] (r : ℕ) (M : Matrix (Fin m) (Fin m) k) : Prop :=
  ∀ a c : Fin m, (a : ℕ) < r → (c : ℕ) < r → (c < a → M a c = 0) ∧ (a = c → M a c = 1)

theorem inLevG_iff (hP : IdFrame hF P) (hn : V.rank = n) {κ : GAf D.host.E n} (hκ : κ ∈ ReciprocityTheory.Aut.Umax D.host.E n)
    (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (r : ℕ) :
    NX.InLevG s.v r (NX.locM s κ) ↔ Formalism.L2.DIV.redFn 1 s.w (Lev.finE V (P.ψ κ)) ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r) ∧
      UT r (Formalism.L2.DIV.redFn 1 s.w (Lev.finE V (P.ψ κ)) : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.DIV.kP s.w)) := by
  unfold NX.InLevG
  refine and_congr (inParah_iff hP hn hκ s r) ⟨fun h a c ha hc => ?_, fun h a b ha hb => ?_⟩
  · have h' := h (Fin.cast hn a) (Fin.cast hn c) (by simpa using ha) (by simpa using hc)
    refine ⟨fun hca => (loc_zero hP hn hκ s a c).1 (h'.1 hca), fun hac => ?_⟩
    subst hac
    exact (loc_one hP hn hκ s a).1 (h'.2 rfl)
  · obtain ⟨a', rfl⟩ := cast_surj hn a
    obtain ⟨b', rfl⟩ := cast_surj hn b
    have h' := h a' b' (by simpa using ha) (by simpa using hb)
    refine ⟨fun hba => (loc_zero hP hn hκ s a' b').2 (h'.1 hba), fun hab => ?_⟩
    have e : a' = b' := by simpa using hab
    subst e
    exact (loc_one hP hn hκ s a').2 (h'.2 rfl)

theorem UT_iff {m r : ℕ} {k : Type} [CommRing k] (hr : r ≤ m) (M : Matrix (Fin m) (Fin m) k) :
    UT r M ↔ ∀ a c : Fin r, (c < a → M (Fin.castLE hr a) (Fin.castLE hr c) = 0) ∧
      (a = c → M (Fin.castLE hr a) (Fin.castLE hr c) = 1) := by
  constructor
  · intro h a c
    have h' := h (Fin.castLE hr a) (Fin.castLE hr c) a.2 c.2
    exact ⟨fun hca => h'.1 hca, fun hac => h'.2 (by rw [hac])⟩
  · intro h a c ha hc
    have h' := h ⟨a, ha⟩ ⟨c, hc⟩
    have ea : Fin.castLE hr ⟨a, ha⟩ = a := Fin.ext rfl
    have ec : Fin.castLE hr ⟨c, hc⟩ = c := Fin.ext rfl
    rw [ea, ec] at h'
    refine ⟨fun hca => h'.1 hca, fun hac => h'.2 (by subst hac; rfl)⟩

end GlobalTheory.MtLev

namespace GlobalTheory.MtLev

theorem rTup_mem_iff (D : D7) (j : Fin D.R.m) (B : Base (Vc D j) (Wc D j)) (t : Twist D Circle)
    (x : GL (Fin (Vc D j).rank) (Lev.EAf D)) (hPg : ∀ PP, PP ∈ B.G.Pg ↔ ∃ kv, PP = NX.pG D kv)
    (iso : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), ZMod (D.host.g kv.1) ≃+* kP (NX.pG D kv))
    (eG : G0g D.nd ≃* G0 B.G.Pg (Wc D j).rank)
    (hiso : ∀ (g : G0g D.nd) kv (h : NX.pG D kv ∈ B.G.Pg) (a c : Fin (Wc D j).rank), (eG g ⟨NX.pG D kv, h⟩).val a c =
      iso kv ((g kv).val (Fin.cast (FWT.rank_Wc j) a) (Fin.cast (FWT.rank_Wc j) c)))
    (hH : ∀ g, eG g ∈ B.G.P.H ↔ g ∈ D.nexp.U)
    (hU : D.nexp.U = NX.Uup (fun kv : (Σ kk : Fin 2, D.nd.PlG kk) => D.host.g kv.1) D.R.r)
    (hblk : ∀ kv, Formalism.L2.DIV.redFn 1 (NX.pG D kv) x ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 (Wc D j).rank)) :
    Formalism.L2.DIV.rTup 1 (B.levS t) x ∈ B.G.P.H ↔ ∀ kv, ∀ a c : Fin (Wc D j).rank,
      (c < a → (Formalism.L2.DIV.redFn 1 (NX.pG D kv) x : Matrix (Fin (Vc D j).rank) (Fin (Vc D j).rank) (kP (NX.pG D kv))) (Fin.castLE B.hr a) (Fin.castLE B.hr c) = 0) ∧
      (a = c → (Formalism.L2.DIV.redFn 1 (NX.pG D kv) x : Matrix (Fin (Vc D j).rank) (Fin (Vc D j).rank) (kP (NX.pG D kv))) (Fin.castLE B.hr a) (Fin.castLE B.hr c) = 1) := by
  set y : G0 B.G.Pg (Wc D j).rank := Formalism.L2.DIV.rTup 1 (B.levS t) x with hy
  have key : ∀ kv (h : NX.pG D kv ∈ B.G.Pg) (a c : Fin (Wc D j).rank),
      ((eG.symm y) kv).val (Fin.cast (FWT.rank_Wc j) a) (Fin.cast (FWT.rank_Wc j) c) =
        (iso kv).symm ((Formalism.L2.DIV.redFn 1 (NX.pG D kv) x : Matrix (Fin (Vc D j).rank) (Fin (Vc D j).rank) (kP (NX.pG D kv))) (Fin.castLE B.hr a) (Fin.castLE B.hr c)) := by
    intro kv h a c
    have e := hiso (eG.symm y) kv h a c
    rw [MulEquiv.apply_symm_apply] at e
    rw [RingEquiv.eq_symm_apply, ← e]
    have e2 : (y ⟨NX.pG D kv, h⟩ : Matrix (Fin (Wc D j).rank) (Fin (Wc D j).rank) (kP (NX.pG D kv))) =
        (Formalism.L2.DIV.upperLeftBlock B.hr (Formalism.L2.DIV.redFn 1 (NX.pG D kv) x) : Matrix (Fin (Wc D j).rank) (Fin (Wc D j).rank) (kP (NX.pG D kv))) := rfl
    rw [e2, Formalism.L2.DIV.upper_block_val_submatrix B.hr (hblk kv)]
    rfl
  have hmem := hH (eG.symm y)
  rw [MulEquiv.apply_symm_apply] at hmem
  refine hmem.trans ?_
  rw [hU, NX.mem_Uup]
  refine forall_congr' fun kv => ?_
  have h : NX.pG D kv ∈ B.G.Pg := (hPg _).2 ⟨kv, rfl⟩
  have hc : ∀ a' : Fin D.R.r, ∃ a : Fin (Wc D j).rank, Fin.cast (FWT.rank_Wc j) a = a' :=
    fun a' => ⟨Fin.cast (FWT.rank_Wc j).symm a', by simp⟩
  constructor
  · rintro ⟨h1, h2⟩ a c
    refine ⟨fun hca => ?_, fun hac => ?_⟩
    · have e : ((eG.symm y) kv).val (Fin.cast (FWT.rank_Wc j) a) (Fin.cast (FWT.rank_Wc j) c) = 0 := h1 hca
      rw [key kv h] at e
      exact (map_eq_zero_iff _ (iso kv).symm.injective).1 e
    · subst hac
      have e := h2 (Fin.cast (FWT.rank_Wc j) a)
      rw [key kv h] at e
      exact (iso kv).symm.injective (by rw [e, map_one])
  · intro H
    refine ⟨fun a' c' hca => ?_, fun a' => ?_⟩
    · obtain ⟨a, rfl⟩ := hc a'
      obtain ⟨c, rfl⟩ := hc c'
      rw [key kv h, (H a c).1 hca, map_zero]
    · obtain ⟨a, rfl⟩ := hc a'
      rw [key kv h, (H a a).2 rfl, map_one]

end GlobalTheory.MtLev

namespace GlobalTheory.MtLev

theorem levMem : ∀ (D : D7) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host)) (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (e : ℤ) (W₀ : Type) [AddCommGroup W₀] [Module (FractionRing (D.ntw.O i)) W₀] (ρ₀ : Representation (FractionRing (D.ntw.O i)) (ReciprocityTheory.Aut.GQ D.host.E D.R.nV) W₀) (τ : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ) (M : NX.MtVReal D i (j.1 + 1) b k Q ψ e W₀ ρ₀ τ) (B : GlobalTheory.ExportSeries.Base (Vc D j) (Wc D j)) (t : Twist D Circle) (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi (Vc D j) D.R.nV), IdFrame hF P → B.F.βS = 1 → (∀ PP, PP ∈ B.G.Pg ↔ ∃ kv, PP = NX.pG D kv) → Function.Injective (NX.pG D) → t.Q = M.QP → B.de.Q = M.DP → ∀ (iso : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), ZMod (D.host.g kv.1) ≃+* kP (NX.pG D kv)) (eG : G0g D.nd ≃* G0 B.G.Pg (Wc D j).rank), (∀ (g : G0g D.nd) kv (h : NX.pG D kv ∈ B.G.Pg) (a c : Fin (Wc D j).rank), (eG g ⟨NX.pG D kv, h⟩).val a c = iso kv ((g kv).val (Fin.cast (FWT.rank_Wc j) a) (Fin.cast (FWT.rank_Wc j) c))) → (∀ g, eG g ∈ B.G.P.H ↔ g ∈ D.nexp.U) → D.nexp.U = NX.Uup (fun kv : (Σ kk : Fin 2, D.nd.PlG kk) => D.host.g kv.1) D.R.r → ∀ g, g ∈ M.J ↔ frameEquiv P g ∈ B.levJ t := by
  intro D i j b k Q ψ e W₀ _ _ ρ₀ τ M B t hF P hP hβ hPg hinj htQ hdQ iso eG hiso hH hU g
  classical
  obtain ⟨hn, -⟩ := id hP
  have hrW : (Wc D j).rank = D.R.r := FWT.rank_Wc j
  have hSt := (GlobalTheory.T.frameKeepsMatrices_splitPlace_reduction_local D (Vc D j) D.R.nV hF P hP hn g).1
  have hUA := GlobalTheory.LevSplit.finE_mem_UA (Vc D j) (P.ψ g)
  have levG_iff : ∀ (hU' : g ∈ ReciprocityTheory.Aut.Umax D.host.E D.R.nV) kv,
      NX.InLevG (M.sp (NX.pG D kv)).v D.R.r (NX.locM (M.sp (NX.pG D kv)) g) ↔
        Formalism.L2.DIV.redFn 1 (NX.pG D kv) (Lev.finE (Vc D j) (P.ψ g)) ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 (Wc D j).rank) ∧
        UT (Wc D j).rank (Formalism.L2.DIV.redFn 1 (NX.pG D kv) (Lev.finE (Vc D j) (P.ψ g)) :
          Matrix (Fin (Vc D j).rank) (Fin (Vc D j).rank) (kP (NX.pG D kv))) := by
    intro hU' kv
    have h := inLevG_iff hP hn hU' (M.sp (NX.pG D kv)) D.R.r
    rw [M.sp_w _ (Or.inr (Or.inr ⟨kv, rfl⟩))] at h
    rw [h, hrW]
  have par_iff : ∀ (hU' : g ∈ ReciprocityTheory.Aut.Umax D.host.E D.R.nV) PP, (PP ∈ M.QP ∨ PP ∈ M.DP) →
      (NX.InParah (M.sp PP).v D.R.r (NX.locM (M.sp PP) g) ↔
        Formalism.L2.DIV.redFn 1 PP (Lev.finE (Vc D j) (P.ψ g)) ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 (Wc D j).rank)) := by
    intro hU' PP hPP
    have h := inParah_iff hP hn hU' (M.sp PP) D.R.r
    rw [M.sp_w _ (hPP.elim Or.inl (fun h => Or.inr (Or.inl h)))] at h
    rw [h, hrW]
  have hblkOf : Formalism.L2.DIV.blkOf (n := (Vc D j).rank) (Wc D j).rank ((Vc D j).rank - (Wc D j).rank) =
      Formalism.L2.DIV.blk2 (Wc D j).rank := blockSizes_sub_eq_twoBlock _
  rw [M.J_mem, mem_levJ_iff, hβ, Formalism.L2.DIV.mem_lev, Formalism.L2.DIV.mem_parLev]
  constructor
  · rintro ⟨hU', hG, hQ, hD⟩
    have hGk := fun kv => (levG_iff hU' kv).1 (hG kv)
    have hblk : ∀ kv, Formalism.L2.DIV.redFn 1 (NX.pG D kv) (Lev.finE (Vc D j) (P.ψ g)) ∈
        Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 (Wc D j).rank) := fun kv => (hGk kv).1
    refine ⟨⟨hUA, hSt.1 hU', fun PP hPP => ?_, fun PP hPP => ?_⟩, ?_⟩
    · obtain ⟨kv, rfl⟩ := (hPg PP).1 hPP
      change _ ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf (Wc D j).rank ((Vc D j).rank - (Wc D j).rank))
      rw [hblkOf]
      exact hblk kv
    · change PP ∈ B.de.Q ∪ t.Q at hPP
      rw [hdQ, htQ] at hPP
      rcases Finset.mem_union.1 hPP with h | h
      · exact (par_iff hU' PP (Or.inr h)).1 (hD PP h)
      · exact (par_iff hU' PP (Or.inl h)).1 (hQ PP h)
    · exact (rTup_mem_iff D j B t _ hPg iso eG hiso hH hU hblk).2 fun kv => (UT_iff B.hr _).1 (hGk kv).2
  · rintro ⟨⟨-, hSt', hPg', hQ'⟩, hR⟩
    have hU' := hSt.2 hSt'
    have hblk : ∀ kv, Formalism.L2.DIV.redFn 1 (NX.pG D kv) (Lev.finE (Vc D j) (P.ψ g)) ∈
        Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 (Wc D j).rank) := fun kv => by
      have h := hPg' (NX.pG D kv) ((hPg _).2 ⟨kv, rfl⟩)
      change _ ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf (Wc D j).rank ((Vc D j).rank - (Wc D j).rank)) at h
      rwa [hblkOf] at h
    have hR' := (rTup_mem_iff D j B t _ hPg iso eG hiso hH hU hblk).1 hR
    have hQm : ∀ PP, PP ∈ M.QP ∨ PP ∈ M.DP → PP ∈ (B.levS t).Q := fun PP h => by
      change PP ∈ B.de.Q ∪ t.Q
      rw [hdQ, htQ]
      exact h.elim (Finset.mem_union_right _) (Finset.mem_union_left _)
    refine ⟨hU', fun kv => (levG_iff hU' kv).2 ⟨hblk kv, (UT_iff B.hr _).2 (hR' kv)⟩,
      fun PP hPP => (par_iff hU' PP (Or.inl hPP)).2 (hQ' PP (hQm PP (Or.inl hPP))),
      fun PP hPP => (par_iff hU' PP (Or.inr hPP)).2 (hQ' PP (hQm PP (Or.inr hPP)))⟩

end GlobalTheory.MtLev
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralFlipScalarMemCoefficientFieldStatement
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centralFlipScalar_mem_coefficientField : ∀ (E : Type) [Field E] [NumberField E] (χ : Formalism.L2.Host.HChar E) (M₀ r w : ℕ) (u a : Eˣ) (T : Finset (HeightOneSpectrum (𝓞 E))) (k : Type) [Field k] (σ : k →+* ℂ), Odd w → (u : E) = ((M₀ : ℕ) : E) → IsIntegral ℤ (a : E) → (∀ v ∈ T, ((M₀ : ℕ) : 𝓞 E) ∈ v.asIdeal) → (∀ v : HeightOneSpectrum (𝓞 E), ((M₀ : ℕ) : 𝓞 E) ∉ v.asIdeal → χ.UnrAt v) → χ.ValuesIn (-1 / 2) σ → (∃ y : k, ((χ.inf a : ℂˣ) : ℂ) = σ y * ((|((Algebra.norm ℚ (a : E) : ℚ) : ℝ)| ^ (-(w : ℝ) / 2) : ℝ) : ℂ)) → (∀ v ∈ T, χ.locK v a = χ.locK v u ∧ v.valuation E (a : E) = v.valuation E ((M₀ : ℕ) : E)) → (∀ v : HeightOneSpectrum (𝓞 E), ((M₀ : ℕ) : 𝓞 E) ∈ v.asIdeal → v ∉ T → χ.locK v a = 1 ∧ v.valuation E (a : E) = 1) → (∏ PP ∈ T, ((χ.locK PP u : ℂˣ) : ℂ) ^ r) * ((Real.sqrt ((∏ PP ∈ T, Ideal.absNorm (PP.maxPowDividing (Ideal.span {((M₀ : ℕ) : 𝓞 E)})) ^ (r * w) : ℕ) : ℝ) : ℝ) : ℂ)⁻¹ ∈ σ.fieldRange := by
  first | exact @GlobalTheory.FlipScalField.mem_fieldRange | exact GlobalTheory.FlipScalField.mem_fieldRange | (intros; apply GlobalTheory.FlipScalField.mem_fieldRange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharInvCentralFlipIdeleEqProdLocalComponentsStatement
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.char_inv_centralFlipIdele_eq_prod_local_components : ∀ (D : D7) (V : HSp D) (χW : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (M₀ : ℕ) (u : D.host.Eˣ) (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (eT : AE D) (x : (AE D)ˣ), ChrEq χW χ → (u : D.host.E) = ((M₀ : ℕ) : D.host.E) → IsIdemSum eT T → IsFlipDet V eT M₀ x → ((χW x : Circle) : ℂ)⁻¹ = ∏ PP ∈ T, ((χ.locK PP u : ℂˣ) : ℂ) ^ V.rank := by
  first | exact @GlobalTheory.FlipCharFormula.char_inv_eq_prod_locK_of_flip | exact GlobalTheory.FlipCharFormula.char_inv_eq_prod_locK_of_flip | (intros; apply GlobalTheory.FlipCharFormula.char_inv_eq_prod_locK_of_flip <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoefLatLeTranslateSplitPlacesPrimeToL
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LatTranslate

theorem coefFn_natCast_smul {D : D7} {n : ℕ} {K : Type} [Field K] (σ : K →+* ℂ) (lam : D.what₂.Tau → Formalism.BasicNotions.DomWeight n)
    (N : ℕ) (F : Formalism.L2.DIV.Pol K D.what₂.Tau n) (x : GLR D n) :
    coefFn σ lam ((N : K) • F) x = (N : ℂ) * coefFn σ lam F x := by
  simp only [coefFn, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval₂Hom_C, map_natCast]
  ring

theorem coefLatFn_transfer {D : D7} {n : ℕ} {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ)
    (emb : D.what₂.Tau → D.host.E →+* K) (lam : D.what₂.Tau → Formalism.BasicNotions.DomWeight n) {O O' : Subring ℂ} (hOO : O ≤ O')
    {M M' : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (N : ℕ) (hN : N ≠ 0) (hinv : ((N : ℂ))⁻¹ ∈ O')
    (hF : ∀ F ∈ Formalism.L2.DIV.nabAtr emb lam M, (N : K) • F ∈ Formalism.L2.DIV.nabAtr emb lam M')
    {φ : GLR D n → ℂ} (hφ : φ ∈ coefLatFn σ emb O lam M) : φ ∈ coefLatFn σ emb O' lam M' := by
  induction hφ using Submodule.span_induction with
  | mem _ h =>
    obtain ⟨F, hFm, rfl⟩ := h
    have h1 : coefFn σ lam (((N : K) • F : Formalism.L2.DIV.VV K lam) : Formalism.L2.DIV.Pol K D.what₂.Tau n) ∈ coefLatFn σ emb O' lam M' :=
      Submodule.subset_span ⟨_, hF F hFm, rfl⟩
    have h2 := Submodule.smul_mem _ (⟨_, hinv⟩ : O') h1
    convert h2 using 1
    funext x
    have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN
    change _ = (N : ℂ)⁻¹ * _
    rw [Submodule.coe_smul, coefFn_natCast_smul, inv_mul_cancel_left₀ hN']
  | zero => exact zero_mem _
  | add _ _ _ _ h1 h2 => exact add_mem h1 h2
  | smul c _ _ h1 => exact Submodule.smul_mem _ (⟨c, hOO c.2⟩ : O') h1

theorem normProd_ne_zero {D : D7} (Q : Finset (Pl D.host.E)) : normProd Q ≠ 0 := by
  unfold normProd
  refine Finset.prod_ne_zero_iff.2 fun v _ => ?_
  rw [Ne, Ideal.absNorm_eq_zero_iff]
  exact v.ne_bot

set_option maxHeartbeats 800000 in

theorem lat_translate : ∀ (D : D7) (ρ : Setup D.ntw), ρ.Good → ∀ (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool), ∀ k (Q : Finset (Pl D.host.E)) (h hQ : GA D (Vc D j)) P, SplitSet Q → Disjoint Q (D.ntw.S0 i) → h ∈ GfC (Vc D j) → SuppAt (idem Q) (Vc D j) hQ → P ∈ ρ.lat i j b (ρ.eO i b).range h → P ∈ ρ.lat i j b (ρ.eOk i b k).range (h * hQ) := by
  intro D ρ hρ i j b k Q h hQ P hS hD hh hsupp hP
  unfold GlobalTheory.SeriesTie.Setup.lat GlobalTheory.ExportSeries.Base.coefLat at *
  rw [GlobalTheory.ExportSeries.mem_harmLat] at *
  refine ⟨hP.1, ?_⟩
  obtain ⟨c, h1, h2⟩ := GlobalTheory.T.splitPlaces_translation_lattice_bounded_norm D ρ hρ i j b Q h hQ hS hsupp
  have hN0 : normProd Q ^ c ≠ 0 := pow_ne_zero _ (normProd_ne_zero Q)
  obtain ⟨a, ha⟩ := GlobalTheory.T.dualWeylLattice_exists_natPow_smul_mem _ _ _ _ (labLL0 D) (ρ.B i j b).w.lam _ _ (normProd Q ^ c) hN0 (GlobalTheory.T.finite_adelic_point_lattice_isLattice D ρ hρ i j b h)
    (GlobalTheory.T.finite_adelic_point_lattice_isLattice D ρ hρ i j b (h * hQ)) h1 h2
  have hu : ((normProd Q : ℕ) : ℂ)⁻¹ ∈ (ρ.eOk i b k).range := hρ.range_le i b k (GlobalTheory.T.inv_place_norm_product_mem_coefficient_ring D ρ i b Q hD)
  have hinv : (((normProd Q ^ c) ^ a : ℕ) : ℂ)⁻¹ ∈ (ρ.eOk i b k).range := by
    rw [Nat.cast_pow, Nat.cast_pow, ← inv_pow, ← inv_pow]
    exact Subring.pow_mem _ (Subring.pow_mem _ hu _) _
  have hF : ∀ F ∈ Formalism.L2.DIV.nabAtr (labLL0 D) (ρ.B i j b).w.lam ((ρ.B i j b).latAt (finPt (Vc D j) h)),
      (((normProd Q ^ c) ^ a : ℕ) : ↥D.LL0) • F ∈
        Formalism.L2.DIV.nabAtr (labLL0 D) (ρ.B i j b).w.lam ((ρ.B i j b).latAt (finPt (Vc D j) (h * hQ))) := by
    intro F hF
    have := ha F hF
    rwa [Nat.cast_pow (α := ↥D.LL0) (normProd Q ^ c) a]
  exact coefLatFn_transfer (Formalism.L2.Host.embLL0 D) (labLL0 D) (ρ.B i j b).w.lam (hρ.range_le i b k)
    ((normProd Q ^ c) ^ a) (pow_ne_zero _ hN0) hinv hF hP.2

end GlobalTheory.LatTranslate

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CongruenceLengthTwistedPlacesOfHeckeIntegralityStatement
section
open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.congruenceLength_twistedPlaces_of_heckeIntegrality : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (m : ℕ) (A : FamIn D.what₂.LL G Pl0 T m) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (Zs : DefSub A.fam.amb) (tup : T → D.what₂.Tup) (eMt : ∀ (i : Fin m) (t : T), (Fin (lDim D A P ψ i t) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL (tup t) ((i : ℕ) + 1)) (s : ℕ), A.fam.Ok s → m ≤ D.R.m → ∀ (S0 : IndefData (A.side P ψ Zs)) (M : MtFam D) (Tn : NormalizedLocalCompatibility D M), TupTie D A S0 tup → (∀ y, y ∈ S0.Tw ↔ S0.μ y ≠ A.μ0) → (∀ (i : Fin m), ∀ y ∈ S0.Tw, FormsTie D.what₂.embLL ((D.what₂.jMt (tup (S0.μ y)) ((i : ℕ) + 1)).comp (eMt i (S0.μ y)).toLinearMap) (lH D A P ψ i (S0.μ y)) (lE D A P ψ i (S0.μ y)) (D.what₂.eMt (tup (S0.μ y)) ((i : ℕ) + 1)) ∧ OLatTie D.what₂.embLL (D.what₂.MtLat (tup (S0.μ y)) ((i : ℕ) + 1)) ((D.what₂.jMt (tup (S0.μ y)) ((i : ℕ) + 1)).comp (eMt i (S0.μ y)).toLinearMap) (lNab D A P ψ i (S0.μ y)) ∧ Idx.Z0 D (tup (S0.μ y)) ((i : ℕ) + 1) = Submodule.span ℂ (Set.range fun k => (D.what₂.jMt (tup (S0.μ y)) ((i : ℕ) + 1)) (eMt i (S0.μ y) ((lZ0 D A P ψ Zs i (S0.μ y)).mulVec (Pi.single k 1))))) → HeckeStdTw Tn.B → ∀ (Q : D.what₂.places.Pl → Finset (PlE D.host)), (∀ i, D.nd.Q i = Q (D.nd.w i)) → (∀ j h1 h2 w, D.what₂.muAt w ≠ D.what₂.mu0 → LatInt D M (Q w) j h1 h2 w) → HeckeTied D M → HeckeRational D M → AVTied D M → (∀ i : D.nd.Loc, ClassSum (M.loc i)) → ∀ (jW : ∀ i : Fin m, (Fin (S0.dW i) → D.what₂.LL) →ₛₗ[D.what₂.embLL] D.what₂.Mj ((i : ℕ) + 1)), m = D.R.m → (∀ (i : Fin m), ∀ y ∈ S0.Tw, ∀ x, D.what₂.thetaP (tup (S0.μ y)) ((i : ℕ) + 1) (D.what₂.jMt (tup (S0.μ y)) ((i : ℕ) + 1) (eMt i (S0.μ y) x)) = jW i ((S0.θ i (S0.μ y)).mulVec ((lPrj D A P ψ Zs i (S0.μ y)).mulVec x))) → D.nd.EigSpan → Rows.IsotInternal D.what₂ → Formalism.MainNotions.SumRepresentations.Conclusion42 D → Formalism.MainNotions.SumRepresentations.ConclusionZ D → GoodFTAll D → ∀ (i : Fin m) w, D.what₂.etaJ ((i : ℕ) + 1) w = @ite _ (D.plEq w ∈ S0.Tw) (Classical.propDecidable _) (A.fam.etaJ P ψ Zs i (S0.μ (D.plEq w)) (D.plEq w)) 0 := by
  first | exact @GlobalTheory.etaJ_join_closed | exact GlobalTheory.etaJ_join_closed | (intros; apply GlobalTheory.etaJ_join_closed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DetCharacterProductFormula
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries GlobalTheory.ExportSeries.DualType
open Formalism.IndefR.Links (PolF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.TwistDetStab

open Classical

variable {D : D7}

theorem infPart_idemAt (P : Pl D.host.E) (e : AE D) (h : Formalism.L2.NTheta.IsIdemAt e P) : infPart D e = 0 := by
  obtain ⟨⟨h1, h2, v, ε, ⟨α, rfl, -⟩, h3⟩, -⟩ := h
  have k1 := congrArg (infPart D) h1
  have k2 := congrArg (infPart D) h2
  have k3 := congrArg (infPart D) h3
  simp only [RingHom.map_mul, RingHom.map_add, RingHom.map_zero] at k1 k2 k3
  have k4 : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) = 0 := by
    simp [infPart, Algebra.TensorProduct.algebraMap_apply]
    show (0 : Ainf D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
    exact TensorProduct.zero_tmul _ _
  rw [k4] at k3
  linear_combination -k1 + infPart D e * k3 - k2

theorem idemAt_mul_idem {Q : Finset (Pl D.host.E)} (h : SplitSet Q) {P : Pl D.host.E} (hP : P ∈ Q) :
    idemAt P * idem Q = idemAt P :=
  GlobalTheory.PlaceModelSum.mul_sum_orth (fun a ha => (h.isIdemAt ha).1) (fun a ha b hb hab => h.mul_eq_zero ha hb hab) hP

theorem idem_mul_self {Q : Finset (Pl D.host.E)} (h : SplitSet Q) : idem Q * idem Q = idem Q := by
  show (∑ P ∈ Q, idemAt P) * idem Q = idem Q
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun P hP => idemAt_mul_idem h hP

theorem idem_mul_idem_of_disjoint {Q s s' : Finset (Pl D.host.E)} (h : SplitSet Q) (hs : s ⊆ Q) (hs' : s' ⊆ Q)
    (hd : Disjoint s s') : idem s * idem s' = 0 := by
  rw [idem, idem, Finset.sum_mul_sum]
  exact Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj =>
    h.mul_eq_zero (hs hi) (hs' hj) fun e => Finset.disjoint_left.1 hd hi (e ▸ hj)

theorem idem_mul_conj {Q s s' : Finset (Pl D.host.E)} (h : SplitSet Q) (hs : s ⊆ Q) (hs' : s' ⊆ Q) :
    idem s * cA D (idem s') = 0 := by
  rw [idem, idem, map_sum, Finset.sum_mul_sum]
  exact Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => h.mul_conj (hs hi) (hs' hj)

theorem val_mul (d e₁ e₂ : AE D) (h : e₁ * e₂ = 0) :
    (e₁ * d + (1 - e₁)) * (e₂ * d + (1 - e₂)) = (e₁ + e₂) * d + (1 - (e₁ + e₂)) := by
  linear_combination (d * d - 2 * d + 1) * h

theorem prod_val (d : AE D) {Q : Finset (Pl D.host.E)} (h : SplitSet Q) :
    ∀ s ⊆ Q, ∏ P ∈ s, (idemAt P * d + (1 - idemAt P)) = idem s * d + (1 - idem s) := by
  intro s
  induction s using Finset.induction_on with
  | empty => intro _; simp
  | insert a s ha ih =>
    intro hs
    rw [Finset.prod_insert ha, ih ((Finset.subset_insert a s).trans hs)]
    have e1 : idem (insert a s) = idemAt a + idem s := Finset.sum_insert ha
    rw [e1]
    refine val_mul d _ _ ?_
    have := idem_mul_idem_of_disjoint h (s := {a}) (s' := s)
      (Finset.singleton_subset_iff.2 (hs (Finset.mem_insert_self a s))) ((Finset.subset_insert a s).trans hs)
      (Finset.disjoint_singleton_left.2 ha)
    rwa [show idem ({a} : Finset (Pl D.host.E)) = idemAt a from Finset.sum_singleton _ _] at this

theorem detChar_eq_prod_res : ∀ {D : D7} {V : HSp D} {A : Type} [CommGroup A] (t : Twist D A), t.Good →
    ∀ (β : GL (Fin V.rank) (Lev.EAf D)) {Q' : Finset (Pl D.host.E)}, SplitSet Q' → t.Q ⊆ Q' → ∀ {κ : GA D V},
    κ ∈ GfC V → Lev.finE V κ ∈ St β → SuppAt (idem Q') V κ →
    detChar V t.chi κ = ∏ PP ∈ t.Q, t.res PP (Matrix.GeneralLinearGroup.det (redFn β PP (Lev.finE V κ))) := by
  intro D V A _ t ht β Q' hQ' hsub κ _ hst hsupp
  have he : idem Q' * idem Q' = idem Q' := idem_mul_self hQ'
  have hce : idem Q' * cA D (idem Q') = 0 := hQ'.isIdemSum.2
  have hroot : IsDetRoot V κ (GlobalTheory.VecInv.detAt (idem Q') he V κ) := by
    have hx : IsDetAt (idem Q') V κ (GlobalTheory.VecInv.detAt (idem Q') he V κ) := GlobalTheory.VecInv.isDetAt_detAt _ he V κ
    unfold IsDetAt at hx
    unfold IsDetRoot
    rw [hx]
    exact idempotent_det_conj_identity (cA D) (idem Q') he hce (mt V κ) hsupp (det_conj_mul V κ)
  rw [detChar_eq ht.real hroot]
  have hR : Q' \ t.Q ⊆ Q' := Finset.sdiff_subset
  have heR : idem (Q' \ t.Q) * idem (Q' \ t.Q) = idem (Q' \ t.Q) := idem_mul_self (hQ'.mono hR)
  have hPi : ∀ P ∈ t.Q, idemAt P * idemAt P = idemAt P := fun P hP => (hQ'.isIdemAt (hsub hP)).1.1
  have hsum : idem (Q' \ t.Q) + idem t.Q = idem Q' := Finset.sum_sdiff hsub
  have hRQ : idem (Q' \ t.Q) * idem t.Q = 0 := idem_mul_idem_of_disjoint hQ' hR hsub Finset.sdiff_disjoint
  have hsplit : GlobalTheory.VecInv.detAt (idem Q') he V κ = GlobalTheory.VecInv.detAt (idem (Q' \ t.Q)) heR V κ *
      ∏ P ∈ t.Q.attach, GlobalTheory.VecInv.detAt (idemAt P.1) (hPi P.1 P.2) V κ := by
    ext
    rw [Units.val_mul, Units.coe_prod]
    show idem Q' * (mt V κ).det + (1 - idem Q') = (idem (Q' \ t.Q) * (mt V κ).det + (1 - idem (Q' \ t.Q))) *
      ∏ P ∈ t.Q.attach, (idemAt P.1 * (mt V κ).det + (1 - idemAt P.1))
    rw [Finset.prod_attach t.Q (fun P => idemAt P * (mt V κ).det + (1 - idemAt P)),
      prod_val _ ht.split t.Q (Finset.Subset.refl _), val_mul _ _ _ hRQ, hsum]
  have hw : t.chi (GlobalTheory.VecInv.detAt (idem (Q' \ t.Q)) heR V κ) = 1 := by
    refine ht.unram _ ?_ (GlobalTheory.PlaceDatum.finPart_mem_of_toEAf (GlobalTheory.StabDet.toEAf_detAt_mem hst _ heR))
      (GlobalTheory.PlaceDatum.finPart_mem_of_toEAf (GlobalTheory.StabDet.toEAf_detAt_inv_mem hst _ heR)) ?_
    · have hinf : infPart D (idem (Q' \ t.Q)) = 0 := by
        rw [idem, map_sum]
        exact Finset.sum_eq_zero fun P hP => infPart_idemAt P _ (hQ'.isIdemAt (hR hP))
      show infPart D (idem (Q' \ t.Q) * (mt V κ).det + (1 - idem (Q' \ t.Q))) = 1
      rw [map_add, map_mul, map_sub, map_one, hinf]
      ring
    · have a1 : idem t.Q * idem (Q' \ t.Q) = 0 := idem_mul_idem_of_disjoint hQ' hsub hR Finset.disjoint_sdiff
      have a2 : idem (Q' \ t.Q) * cA D (idem t.Q) = 0 := idem_mul_conj hQ' hR hsub
      show (idem t.Q + cA D (idem t.Q)) * (idem (Q' \ t.Q) * (mt V κ).det + (1 - idem (Q' \ t.Q))) =
        idem t.Q + cA D (idem t.Q)
      linear_combination ((mt V κ).det - 1) * (a1 + a2)
  rw [hsplit, map_mul, hw, one_mul, map_prod,
    ← Finset.prod_attach t.Q (fun PP => t.res PP (Matrix.GeneralLinearGroup.det (redFn β PP (Lev.finE V κ))))]
  refine Finset.prod_congr rfl fun P _ => ?_
  refine ht.res P.1 P.2 _ ?_ (GlobalTheory.StabDet.toEAf_detAt_mem hst _ (hPi P.1 P.2)) _
    (GlobalTheory.StabDet.res_detAt hst _ (hPi P.1 P.2) P.1 (hQ'.isIdemAt (hsub P.2))).symm
  show (1 - idemAt P.1) * (idemAt P.1 * (mt V κ).det + (1 - idemAt P.1)) = 1 - idemAt P.1
  linear_combination (1 - (mt V κ).det) * hPi P.1 P.2

end GlobalTheory.TwistDetStab

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsToricCharactersInTwistCoefficientRingsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_toricCharacters_in_twistCoefficientRings : GlobalTheory.Published.ChebotarevDegreeOne → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.ToricRational.RatioConj → ∀ (D : D7) (hE : IsEmpty D.nd.Loc) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (b0 b1 : Big D) (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T) (Z : GlobalTheory.LamTie.LamDat D), Z.C = cf → Z.Ok → (∀ a, GlobalTheory.LamTie.TeichTriv D.host (Z.chi a)) → ValLL0 D cf → (∀ a, (Z.chi a).ValuesIn 0 (embLL0 D)) → (∀ i P, (GlobalTheory.ToricDenom.below P).asIdeal ∣ GlobalTheory.LamTie.cond0 D.host Z.w0 → P ∈ T.S0 i) → ∃ L : TwL T, ∀ F : TwF T, GlobalTheory.LamTie.IsLamTieFull (T.ntw hE F L) Z ∧ ∀ (ex : NExp D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F (TwL.empty T))) (h0 : _) th, Nonempty (SideB (⟨T.ntw hE F (TwL.empty T), ex, h0, th, Sp.br, Sp.br_ind⟩ : TwNew D).toD7 ((⟨T.ntw hE F (TwL.empty T), ex, h0, th, Sp.br, Sp.br_ind⟩ : TwNew D).cf cf) ((⟨T.ntw hE F (TwL.empty T), ex, h0, th, Sp.br, Sp.br_ind⟩ : TwNew D).row Rw) low Pq ((⟨T.ntw hE F (TwL.empty T), ex, h0, th, Sp.br, Sp.br_ind⟩ : TwNew D).rat S) hL eig θ) → ∀ th', Nonempty (SideB (⟨T.ntw hE F L, ({ ex with } : NExp D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F L)), h0, th', Sp.br, Sp.br_ind⟩ : TwNew D).toD7 ((⟨T.ntw hE F L, ({ ex with } : NExp D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F L)), h0, th', Sp.br, Sp.br_ind⟩ : TwNew D).cf cf) ((⟨T.ntw hE F L, ({ ex with } : NExp D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F L)), h0, th', Sp.br, Sp.br_ind⟩ : TwNew D).row Rw) low Pq ((⟨T.ntw hE F L, ({ ex with } : NExp D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F L)), h0, th', Sp.br, Sp.br_ind⟩ : TwNew D).rat S) hL eig θ) := by
  first | exact @GlobalTheory.LamInstall.exists_twL_installed | exact GlobalTheory.LamInstall.exists_twL_installed | (intros; apply GlobalTheory.LamInstall.exists_twL_installed <;> assumption)
end

