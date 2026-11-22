import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0049
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FiberCount
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.PairValPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ZzPlusSecondProjection
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountNonIntegrality.Bundle0005
import Mathlib

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CoefDensTh
section
noncomputable section

namespace Formalism.L2.SG.Pf.Coef

open Formalism.MainNotions.S.LocalSplitGroups

theorem densTh_of_ga {D : Formalism.BasicNotions.D7} {M : ∀ p : PlF D, Formalism.MainNotions.S.Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
    {δ : ∀ p : PlF D, (D.s.atP p).Fp} {L : Formalism.L2.SG.CntLocal.LocSp D M} {u u' : D.what₂.Word}
    (hG : GaPlusTh M δ u u') : FCount.DensTh M δ L u u' :=
  densTh_of Formalism.L2.SG.Pf.density_congruence_holds hG

end Formalism.L2.SG.Pf.Coef
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CoefPhase
section
noncomputable section

namespace Formalism.L2.SG.Pf.Coef

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Steps

variable {D : Formalism.BasicNotions.D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word)
  (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

def PhaseAtRep : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (L U : PairVal.MatR D),
    γ.relevant → γ.generic → PairVal.NormRep γ w F' L U →
    (Function.mulSupport fun p => phL M δ (D.mem u).A.T (D.mem u').A.T p w
      (CntLocal.ZZP (M := M) δ u u' p (ZhatL (lf D F0) F') * sgnP p)).Finite ∧
    PairVal.phasePair (gS D) L U = ∏ᶠ p, phL M δ (D.mem u).A.T (D.mem u').A.T p w
      (CntLocal.ZZP (M := M) δ u u' p (ZhatL (lf D F0) F') * sgnP p)

def PhaseLoc : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (L U : PairVal.MatR D),
    γ.relevant → γ.generic → PairVal.NormRep γ w F' L U → ∀ p : PlF D,
    phL M δ (D.mem u).A.T (D.mem u').A.T p w (CntLocal.ZZP (M := M) δ u u' p (ZhatL (lf D F0) F') * sgnP p) =
      (D.s.atP p).psiE ((D.s.atP p).ιE (-((PairVal.sgLo L + PairVal.sgUp U) / ((gS D : ℕ) : D.host.E))))

end Steps

variable (D : Formalism.BasicNotions.D7) in

def PsiProdE : Prop :=
  ∀ x : D.host.E,
    (Function.mulSupport fun p : PlF D => (D.s.atP p).psiE ((D.s.atP p).ιE x)).Finite ∧
    ∏ᶠ p : PlF D, (D.s.atP p).psiE ((D.s.atP p).ιE x) =
      Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ D.host.E x : ℚ) : ℂ))

section Assembly

variable {D : Formalism.BasicNotions.D7} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
  {δ : ∀ p : PlF D, (D.s.atP p).Fp} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem trace_neg_div (E : Type) [Field E] [NumberField E] (s : E) (g : ℕ) :
    Algebra.trace ℚ E (-(s / (g : E))) = -(Algebra.trace ℚ E s / (g : ℚ)) := by
  have hg : ((g : ℕ) : E) = algebraMap ℚ E (g : ℚ) := by simp
  rw [hg, div_eq_mul_inv, ← map_inv₀, mul_comm, ← Algebra.smul_def, map_neg, LinearMap.map_smul, smul_eq_mul]
  ring

theorem phaseAtRep_of (hL : PhaseLoc M δ u u' F0 what₂) (hP : PsiProdE D) : PhaseAtRep M δ u u' F0 what₂ := by
  intro γ w F' L U hrel hgen hN
  have hfun : (fun p => phL M δ (D.mem u).A.T (D.mem u').A.T p w
      (CntLocal.ZZP (M := M) δ u u' p (ZhatL (lf D F0) F') * sgnP p)) = fun p =>
      (D.s.atP p).psiE ((D.s.atP p).ιE (-((PairVal.sgLo L + PairVal.sgUp U) / ((gS D : ℕ) : D.host.E)))) :=
    funext (hL γ w F' L U hrel hgen hN)
  rw [hfun]
  obtain ⟨hf, hp⟩ := hP (-((PairVal.sgLo L + PairVal.sgUp U) / ((gS D : ℕ) : D.host.E)))
  refine ⟨hf, ?_⟩
  rw [hp, trace_neg_div, map_add]
  unfold PairVal.phasePair PairVal.psiInf
  rw [← Complex.exp_neg, ← Complex.exp_neg, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem phaseProd_of (hrows : IsRowReps D F0 what₂) (hN : PairVal.NormRepExists D u u' F0 what₂)
    (hW : PairVal.PhaseWellDef D u u' F0 what₂) (hR : PhaseAtRep M δ u u' F0 what₂) : PhaseProd M δ u u' F0 what₂ := by
  intro γ w hγ
  have hrel := PCount.eligRel_holds γ w hγ
  have hex := normRepElig_of hN γ w hγ
  have hz : zT γ = ZhatL (lf D F0) hex.choose.2.1 := by
    unfold zT nrep
    rw [dif_pos hex]
  have hpt : ptT γ = hex.choose.1 := by
    unfold ptT nrep
    rw [dif_pos hex]
  have hw : hex.choose.1 = w := hpt.symm.trans (FCount.ptT_eq hN hrows hγ hrel)
  have h0 : PairVal.NormRep γ w hex.choose.2.1 hex.choose.2.2.1 hex.choose.2.2.2 := by
    have := hex.choose_spec
    rw [hw] at this
    exact this
  obtain ⟨hf, hp⟩ := hR γ w _ _ _ hrel hγ.1.1 h0
  have hyT : ∀ p, yT M δ u u' F0 what₂ γ p =
      CntLocal.ZZP (M := M) δ u u' p (ZhatL (lf D F0) hex.choose.2.1) * sgnP p := fun p => by
    unfold yT; rw [hz]
  simp only [hyT]
  refine ⟨hf, ?_⟩
  rw [← hp]
  have hex1 : ∃ x : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E) × PairVal.MatR D × PairVal.MatR D,
      PairVal.NormRep γ w x.1 x.2.1 x.2.2 := ⟨(hex.choose.2.1, hex.choose.2.2.1, hex.choose.2.2.2), h0⟩
  unfold PairVal.phaseAt
  rw [dif_pos hex1]
  exact hW γ w hrel _ _ _ _ _ _ hex1.choose_spec h0

end Assembly

end Formalism.L2.SG.Pf.Coef
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CoefXiTyped
section
noncomputable section

namespace Formalism.L2.SG.Pf.PCount

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB
open Classical ValuativeRel
open Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section QMul

variable {K : Type} [Field K] [ValuativeRel K] (q : K)

def QM (x : K) : Prop := ∃ t ∈ 𝒪[K], x = q * t

theorem qm_zero : QM q 0 := ⟨0, zero_mem _, by ring⟩

theorem qm_add {x y : K} (hx : QM q x) (hy : QM q y) : QM q (x + y) := by
  obtain ⟨t, ht, rfl⟩ := hx
  obtain ⟨t', ht', rfl⟩ := hy
  exact ⟨t + t', add_mem ht ht', by ring⟩

theorem qm_neg {x : K} (hx : QM q x) : QM q (-x) := by
  obtain ⟨t, ht, rfl⟩ := hx
  exact ⟨-t, neg_mem ht, by ring⟩

theorem qm_mul_int {x y : K} (hx : QM q x) (hy : y ∈ 𝒪[K]) : QM q (x * y) := by
  obtain ⟨t, ht, rfl⟩ := hx
  exact ⟨t * y, mul_mem ht hy, by ring⟩

theorem qm_sum {ι : Type*} (s : Finset ι) (f : ι → K) (h : ∀ i ∈ s, QM q (f i)) : QM q (∑ i ∈ s, f i) :=
  Finset.sum_induction _ (QM q) (fun _ _ => qm_add q) (qm_zero q) h

theorem qm_inv_entry {R : Type} [CommRing R] (φ : R →+* K) (hφ : ∀ x, φ x ∈ 𝒪[K]) {n : ℕ}
    (ξ : Matrix (Fin n) (Fin n) R) (h1 : ∀ a b, b < a → ξ a b = 0) (h2 : ∀ a, ξ a a = 1)
    (hc : ∀ a c, a < c → QM q (φ (ξ a c))) {k b : Fin n} (hkb : k < b) : QM q (φ (ξ⁻¹ k b)) := by
  have hbt : ξ.BlockTriangular id := fun i j hij => h1 i j hij
  have hdet : ξ.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular hbt]
    simp [h2]
  have hmul : ξ * ξ⁻¹ = 1 := Matrix.mul_nonsing_inv ξ (by rw [hdet]; exact isUnit_one)
  have e1 := congrFun (congrFun hmul k) b
  rw [Matrix.mul_apply, Matrix.one_apply_ne (ne_of_lt hkb), ← Finset.add_sum_erase _ _ (Finset.mem_univ k),
    h2, one_mul] at e1
  have e2 : ξ⁻¹ k b = -∑ c ∈ Finset.univ.erase k, ξ k c * ξ⁻¹ c b := by
    linear_combination e1
  rw [e2, map_neg, map_sum]
  refine qm_neg q (qm_sum q _ _ fun c hc' => ?_)
  rw [map_mul]
  rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hc') with hlt | hgt
  · rw [h1 k c hlt, map_zero, zero_mul]
    exact qm_zero q
  · exact qm_mul_int q (hc k c hgt) (hφ _)

end QMul

section XiPf

variable {D : Formalism.BasicNotions.D7}

set_option maxHeartbeats 1000000 in

theorem xiTyped_of_ctx {Zd : LocDat D} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
    {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (hctx : CtxP u u' F0 what₂) : XiTyped Zd u u' F0 what₂ := by
  intro γ w hγ p g hs k b hkb
  have hN := normRepExists_ctx hctx
  have hrows := hctx.2.1
  have hex := Formalism.L2.SG.Pf.Coef.normRepElig_of hN γ w hγ
  have hrep : repF γ = hex.choose.2.1 := by
    unfold repF nrep
    rw [dif_pos hex]
  have hA1 : AdmWit γ.lam (gS D) (lf D F0) (repF γ) 1 := by
    rw [hrep]
    exact hex.choose_spec.2.1
  have hadm : IsAdmissible γ.lam (gS D) (lf D F0) (repF γ) := ⟨1, hA1⟩
  have hW : AdmWit γ.lam (gS D) (lf D F0) (repF γ) (admXi D γ.lam (lf D F0) (repF γ)) := by
    unfold admXi
    rw [dif_pos hadm]
    exact hadm.choose_spec
  generalize admXi D γ.lam (lf D F0) (repF γ) = ξ at hW ⊢

  obtain ⟨hq, hell⟩ := PI.CntNotIntW.split_ell Zd.δ Zd.agree p g hs
  obtain ⟨kk, hk⟩ := PI.CntNotIntW.gS_split p hell
  have hl0 : Loc.resChar p ≠ 0 := (D.s.atP p).ellPrime.out.ne_zero
  have hl : valuation (D.s.atP p).Fp ((Loc.resChar p : ℕ) : (D.s.atP p).Fp) < 1 := by
    rw [← hq]; exact PI.CntNotIntW.val_q_lt p g
  have hg : ((gS D : ℕ) : (D.s.atP p).Fp) =
      (g.q : (D.s.atP p).Fp) ^ 1 * ((kk : 𝒪[(D.s.atP p).Fp]) : (D.s.atP p).Fp) := by
    rw [hk, hq]; push_cast; ring
  have hgv : valuation (D.s.atP p).Fp ((gS D : ℕ) : (D.s.atP p).Fp) < 1 := by
    rw [hg, pow_one, Valuation.map_mul]
    exact mul_lt_of_lt_of_le_one (PI.CntNotIntW.val_q_lt p g)
      ((Valuation.mem_integer_iff _ _).1 (kk : 𝒪[(D.s.atP p).Fp]).2)
  have hgP : ∀ σ : D.host.E →+* (D.s.atP p).Fp,
      ((gS D : ℕ) : 𝓞 D.host.E) ∈ (PI.CntNotIntW.vPrime σ (Loc.resChar p) hl0 hl).asIdeal := fun σ => by
    show _ ∈ PI.CntNotIntW.vIdeal σ
    rw [PI.CntNotIntW.mem_vIdeal]
    simpa using hgv

  obtain ⟨-, ⟨-, -, -, hFC⟩, -⟩ := hrows.1 γ.lam γ.mem
  have hlast : ∀ c : Fin (D.R.rS + 1), ((ξ (Fin.last D.R.rS) c : 𝓞 D.host.E) : D.host.E) -
      (if Fin.last D.R.rS = c then 1 else 0) = 0 := by
    intro c
    by_cases hc : Fin.last D.R.rS = c
    · rw [if_pos hc, ← hc, hW.2.1]; simp
    · rw [if_neg hc, hW.1 _ _ (lt_of_le_of_ne (Fin.le_last c) (Ne.symm hc))]; simp

  have hcoef : ∀ σ : D.host.E →+* (D.s.atP p).Fp, ∀ a c : Fin (D.R.rS + 1), a < c →
      QM (g.q : (D.s.atP p).Fp) (σ ((ξ a c : 𝓞 D.host.E) : D.host.E)) := by
    intro σ a c hac
    have hy : ModG (VS D) γ.lam (gS D) (frameAct (frame (lf D F0)) ξ c - frame (lf D F0) c) := by
      intro Q hQ
      have h1 := hA1.2.2 c Q hQ
      have h2 := hW.2.2 c Q hQ
      rw [PI.CntNotIntW.frameAct_one] at h1
      have h3 := Submodule.sub_mem _ h1 h2
      convert h3 using 1
      abel

    have hyexp : frameAct (frame (lf D F0)) ξ c - frame (lf D F0) c =
        ∑ i : Fin D.R.rS, (((ξ (Fin.castSucc i) c : 𝓞 D.host.E) : D.host.E) -
          (if Fin.castSucc i = c then 1 else 0)) • F0.e i := by
      have e1 : frame (lf D F0) c = ∑ a : Fin (D.R.rS + 1), (if a = c then (1 : D.host.E) else 0) • F0.fvec a := by
        rw [Finset.sum_eq_single c]
        · simp
        · intro a _ ha; simp [ha]
        · simp
      unfold frameAct
      rw [e1, ← Finset.sum_sub_distrib, Fin.sum_univ_castSucc]
      simp only [← sub_smul]
      rw [hlast c, zero_smul, add_zero]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [FlagG.fvec, Fin.snoc_castSucc]
    set P := PI.CntNotIntW.vPrime σ (Loc.resChar p) hl0 hl with hPdef
    obtain ⟨s, hsP, l, hlΛ, hsl⟩ := PI.CntNotIntW.modG_at D γ.lam hy P (hgP σ)

    have hgE : ((gS D : ℕ) : D.host.E) ≠ 0 := by
      have : (gS D : ℕ) ≠ 0 := by
        unfold Lat.gS
        exact Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
      exact_mod_cast this
    have hlX : l ∈ (lf D F0).fl.X := by
      have hl2 : l = (((gS D : ℕ) : D.host.E)⁻¹ * (s : D.host.E)) •
          (frameAct (frame (lf D F0)) ξ c - frame (lf D F0) c) := by
        rw [mul_smul, hsl, ← mul_smul, inv_mul_cancel₀ hgE, one_smul]
      rw [hl2, hyexp]
      refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_)
      exact Submodule.subset_span ⟨i, rfl⟩
    have hlXL : l ∈ XLam γ.lam (lf D F0) := ⟨hlΛ, hlX⟩
    obtain ⟨cc, -, hc1, hloc⟩ := hFC.1 P
    have hcc : ∀ i, cc i = 1 := hc1 (hgP σ)
    have hlloc : l ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (XLam γ.lam (lf D F0)) := by
      show ∃ s ∈ P.asIdeal.primeCompl, s • l ∈ XLam γ.lam (lf D F0)
      exact ⟨1, P.asIdeal.primeCompl.one_mem, by simpa using hlXL⟩
    rw [hloc] at hlloc
    obtain ⟨t, htP, htl⟩ := hlloc
    simp only [hcc, one_smul] at htl
    obtain ⟨o, ho⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 D.host.E)).1 htl

    have hcomb : ∑ i : Fin D.R.rS, ((t : D.host.E) * s * (((ξ (Fin.castSucc i) c : 𝓞 D.host.E) : D.host.E) -
        (if Fin.castSucc i = c then 1 else 0)) - ((gS D : ℕ) : D.host.E) * (o i : D.host.E)) • F0.e i = 0 := by
      have hto : (t : D.host.E) • l = ∑ i, (o i : D.host.E) • F0.e i := by
        rw [show (t : D.host.E) = algebraMap (𝓞 D.host.E) D.host.E t from rfl, algebraMap_smul, ← ho]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [show (o i : D.host.E) = algebraMap (𝓞 D.host.E) D.host.E (o i) from rfl, algebraMap_smul]
      have e2 : (t : D.host.E) • ((s : D.host.E) • (frameAct (frame (lf D F0)) ξ c - frame (lf D F0) c)) =
          ((gS D : ℕ) : D.host.E) • ∑ i, (o i : D.host.E) • F0.e i := by
        rw [hsl, smul_comm, hto]
      rw [hyexp, Finset.smul_sum, Finset.smul_sum, Finset.smul_sum] at e2
      simp only [smul_smul] at e2
      rw [Finset.sum_congr rfl fun i _ => sub_smul _ _ _, Finset.sum_sub_distrib, sub_eq_zero]
      convert e2 using 2 <;> ring_nf
    have hz := (Fintype.linearIndependent_iff.1 F0.e_indep) _ hcomb
    have ha : a ≠ Fin.last D.R.rS := fun h => by
      rw [h] at hac; exact absurd hac (not_lt.2 (Fin.le_last c))
    obtain ⟨i, rfl⟩ : ∃ i : Fin D.R.rS, Fin.castSucc i = a := ⟨a.castPred ha, Fin.castSucc_castPred a ha⟩
    have hzi := hz i
    rw [if_neg (ne_of_lt hac), sub_zero, sub_eq_zero] at hzi
    have hv : valuation (D.s.atP p).Fp (σ ((t : D.host.E) * s)) = 1 := by
      rw [map_mul, Valuation.map_mul, PI.CntNotIntW.val_one_of_not_mem σ _ hl0 hl t htP,
        PI.CntNotIntW.val_one_of_not_mem σ _ hl0 hl s hsP, one_mul]
    obtain ⟨t', ht'⟩ := PI.CntNotIntW.div_q σ g.q kk 1 (gS D) ((t : D.host.E) * s) _ (o i) hv hg hzi
    exact ⟨t', t'.2, by rw [ht', pow_one]⟩

  have hcoe : ∀ z : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E z = (z : D.host.E) := fun z => rfl
  have hinv : ∀ σ : D.host.E →+* (D.s.atP p).Fp,
      QM (g.q : (D.s.atP p).Fp) (σ ((ξ⁻¹ k b : 𝓞 D.host.E) : D.host.E)) := by
    intro σ
    obtain ⟨φ, hφ⟩ : ∃ φ : 𝓞 D.host.E →+* (D.s.atP p).Fp, ∀ o : 𝓞 D.host.E, φ o = σ (o : D.host.E) :=
      ⟨σ.comp (algebraMap (𝓞 D.host.E) D.host.E), fun o => rfl⟩
    rw [← hφ]
    exact qm_inv_entry _ φ (fun o => by rw [hφ]; exact PI.CntNotIntW.sig_int σ o) ξ hW.1 hW.2.1
      (fun a c hac => by rw [hφ]; exact hcoef σ a c hac) hkb
  obtain ⟨σ1, hσ1⟩ : ∃ σ1 : D.host.E →+* (D.s.atP p).Fp, ∀ y, σ1 y = (g.e ((D.s.atP p).ιE y)).1 :=
    ⟨(RingHom.fst _ _).comp (g.e.toRingEquiv.toRingHom.comp (D.s.atP p).ιE), fun y => rfl⟩
  obtain ⟨σ2, hσ2⟩ : ∃ σ2 : D.host.E →+* (D.s.atP p).Fp, ∀ y, σ2 y = (g.e ((D.s.atP p).ιE y)).2 :=
    ⟨(RingHom.snd _ _).comp (g.e.toRingEquiv.toRingHom.comp (D.s.atP p).ιE), fun y => rfl⟩
  refine ⟨?_, ?_⟩
  · obtain ⟨x, hx, hxe⟩ := hinv σ1
    refine ⟨x, hx, ?_⟩
    rw [adeleInfiniteComponent_apply, Matrix.map_apply, hcoe, ← hσ1]
    exact hxe
  · obtain ⟨x, hx, hxe⟩ := hinv σ2
    refine ⟨x, hx, ?_⟩
    rw [adele_ext_components, Matrix.map_apply, hcoe, ← hσ2]
    exact hxe

theorem tau_one_holds {Zd : LocDat D} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
    {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)} : TauOneReduction Zd u u' F0 what₂ :=
  tauOne_of_typed xiTyped_of_ctx

end XiPf

end Formalism.L2.SG.Pf.PCount
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarGlob
section
noncomputable section

open scoped Classical
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

def starInU (γ : TermDef.Term D u u' F0 what₂) (F'₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) : Prop :=
  ∀ b, frame F'₂ b ∈ Submodule.span D.host.E (Set.range (Sum.elim (frame (lf D F0)) (starFrame γ)))

def starOmL (f f' : Fin (D.R.rS + 1) → (VS D).V) : (VS D).V :=
  ∑ a, star ((starZh f f').adjugate (Fin.last D.R.rS) a) • f a

theorem star_frame_lead_minor (γ : TermDef.Term D u u' F0 what₂) (l : ℕ) :
    leadMinorE (starZh (frame (lf D F0)) (starFrame γ)) l = leadMinorE (ZhatL (lf D F0) (repF γ)) l := by
  obtain ⟨hξ1, hξ2⟩ := inv_unitri _ (admissibility_witness_unitriangular γ.lam (lf D F0) (repF γ)).1 (admissibility_witness_unitriangular γ.lam (lf D F0) (repF γ)).2
  have hZ : starZh (frame (lf D F0)) (starFrame γ) =
      1 * ZhatL (lf D F0) (repF γ) *
        (Matrix.of fun a b => (((admXi D γ.lam (lf D F0) (repF γ))⁻¹ a b : 𝓞 D.host.E) : D.host.E)) := by
    rw [Matrix.one_mul]
    exact FsLA.gram_comb_left (S := VS D) (frame (repF γ)) _ (frame (lf D F0))
  rw [hZ, Formalism.L2.SG.Pf.leadMinor_uni 1 _ _ (fun a c h => Matrix.one_apply_ne (ne_of_lt h))
    (fun a => Matrix.one_apply_eq a) (fun d b h => by simp [Matrix.of_apply, hξ1 d b h])
    (fun b => by simp [Matrix.of_apply, hξ2 b]) l]

theorem starG_ne (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)) (hγ : EligAt γ w) :
    (starZh (frame (lf D F0)) (starFrame γ)).det * star (starZh (frame (lf D F0)) (starFrame γ)).det -
      CntLocal.Tn u * ((Tu D u' : ℕ) : D.host.E) *
        (leadMinorE (starZh (frame (lf D F0)) (starFrame γ)) D.R.rS *
          star (leadMinorE (starZh (frame (lf D F0)) (starFrame γ)) D.R.rS)) ≠ 0 := by
  obtain ⟨-, hG⟩ := hγ.1
  obtain ⟨h2, h2e⟩ := starRepF_rep γ
  have hrel2 := (Formalism.L2.SG.Pf.double_coset_equivalence γ.lam (lf D F0) (PD D γ.lam (lf D F0) u') (Quot.out γ.cls)
    ⟨repF γ, h2⟩).1 ((Quot.out_eq γ.cls).trans h2e.symm)
  have hGv : Gval (lf D F0) (repF γ) ≠ 0 := by
    rw [Formalism.L2.SG.Pf.gval_rel (lf D F0) hrel2]; exact hG
  rw [← FsLA.leadMinorE_full, star_frame_lead_minor, star_frame_lead_minor]
  exact hGv

theorem starGlob (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D) (hC : Ctx γ Z)
    (F'₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (hZ : ZhatL (lf D F0) F'₂ = Z)
    (hU : starInU γ F'₂) :
    ∃ (g : (VS D).V ≃ₗ[D.host.E] (VS D).V) (y : Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1) → (VS D).V),
      (∀ x x', (VS D).hT (g x) (g x') = (VS D).hT x x') ∧ (∀ b, g (starFrame γ b) = frame F'₂ b) ∧
      (∀ v, g v = v + ∑ k, (VS D).hT (Sum.elim (frame (lf D F0)) (starFrame γ) k) v • y k) ∧
      star (starZh (frame (lf D F0)) (starFrame γ)).det • starOmL (frame (lf D F0)) (frame F'₂) -
        star Z.det • g (starOmL (frame (lf D F0)) (starFrame γ)) ∈ Xsp F'₂ := by
  obtain ⟨w, hγ, -⟩ := id hC
  obtain ⟨hZd, hZ₁d, hx⟩ := starMinors_holds u u' F0 what₂ γ Z hC
  set f := frame (lf D F0) with hf
  set f₁ := starFrame γ with hf₁
  set Z₁ := starZh f f₁ with hZ₁
  set F₂ := F'₂.fl with hF₂
  have hfF : f = F0.fvec := rfl
  have hf₂ : frame F'₂ = F₂.fvec := rfl
  have hZe : ∀ a b, (VS D).hT (f a) (F₂.fvec b) = Z a b := fun a b => by rw [← hZ]; rfl
  have hg2 : FsLA.gram (VS D) f F₂.fvec = Zᴴ := by
    refine Matrix.ext fun i j => ?_
    simp only [FsLA.gram, Matrix.conjTranspose_apply]
    rw [← hZe, ← (LinearMap.isSymm_def.1 (VS D).herm) (f j) (F₂.fvec i), starRingEnd_apply]
  have hZ1e : FsLA.gram (VS D) f₁ F0.fvec = Z₁ := rfl
  obtain ⟨hf1a, hf1b⟩ := star_frame_orthogonal γ
  have h1f : ∀ a b, (a ≠ Fin.last D.R.rS ∨ b ≠ Fin.last D.R.rS) → (VS D).hT (f a) (f b) = 0 :=
    fun a b h => FsLA.gram_fvec_zero F0 a b h
  have h2f : (VS D).hT (f (Fin.last D.R.rS)) (f (Fin.last D.R.rS)) = -CntLocal.Tn u := FsLA.gram_fvec_last F0
  have hdZ1h : Z₁ᴴ.det ≠ 0 := by rw [Matrix.det_conjTranspose]; exact star_ne_zero.2 hZ₁d
  have hdg2 : (FsLA.gram (VS D) f F₂.fvec).det ≠ 0 := by
    rw [hg2, Matrix.det_conjTranspose]; exact star_ne_zero.2 hZd
  have hx2 : leadMinorE (FsLA.gram (VS D) f F₂.fvec) D.R.rS * Z₁ᴴ.det =
      leadMinorE Z₁ᴴ D.R.rS * (FsLA.gram (VS D) f F₂.fvec).det := by
    rw [hg2, FsLA.lm_conjTranspose, FsLA.lm_conjTranspose, Matrix.det_conjTranspose, Matrix.det_conjTranspose,
      ← star_mul', ← star_mul', mul_comm (leadMinorE Z D.R.rS), hx, mul_comm]
  obtain ⟨F₃, hZ3, hom3, hsp3⟩ := FsLA.frame_la F₂ f h1f h2f Z₁ᴴ hdZ1h hdg2 hx2
  set h := F₃.fvec with hh
  set uu := Sum.elim f f₁ with huu
  set uu' := Sum.elim h F₂.fvec with huu'
  have hZ3e : ∀ a b, (VS D).hT (F₂.fvec a) (h b) = Z₁ᴴ a b := fun a b => congrFun (congrFun hZ3 a) b
  have k1 : ∀ a b, (VS D).hT (h a) (h b) = (VS D).hT (f a) (f b) := by
    intro a b
    by_cases hab : a ≠ Fin.last D.R.rS ∨ b ≠ Fin.last D.R.rS
    · exact (FsLA.gram_fvec_zero F₃ a b hab).trans (FsLA.gram_fvec_zero F0 a b hab).symm
    · push_neg at hab
      rw [hab.1, hab.2]
      exact (FsLA.gram_fvec_last F₃).trans (FsLA.gram_fvec_last F0).symm
  have k2 : ∀ a b, (VS D).hT (h a) (F₂.fvec b) = (VS D).hT (f a) (f₁ b) := by
    intro a b
    rw [← (LinearMap.isSymm_def.1 (VS D).herm) (F₂.fvec b) (h a), hZ3e, starRingEnd_apply,
      Matrix.conjTranspose_apply, star_star]
    rfl
  have k3 : ∀ a b, (VS D).hT (F₂.fvec a) (h b) = (VS D).hT (f₁ a) (f b) := by
    intro a b
    rw [hZ3e, Matrix.conjTranspose_apply, ← starRingEnd_apply]
    exact (LinearMap.isSymm_def.1 (VS D).herm) (f b) (f₁ a)
  have k4 : ∀ a b, (VS D).hT (F₂.fvec a) (F₂.fvec b) = (VS D).hT (f₁ a) (f₁ b) := by
    intro a b
    by_cases hab : a ≠ Fin.last D.R.rS ∨ b ≠ Fin.last D.R.rS
    · exact (FsLA.gram_fvec_zero F₂ a b hab).trans (hf1a a b hab).symm
    · push_neg at hab
      rw [hab.1, hab.2]
      exact (FsLA.gram_fvec_last F₂).trans hf1b.symm
  have hGr : FsLA.gram (VS D) uu' uu' = FsLA.gram (VS D) uu uu := by
    refine Matrix.ext fun i j => ?_
    rcases i with a | a <;> rcases j with b | b
    · exact k1 a b
    · exact k2 a b
    · exact k3 a b
    · exact k4 a b
  have hdet : (FsLA.gram (VS D) uu uu).det ≠ 0 :=
    FsLA.gram_pair_det F0 f₁ hf1a hf1b hZ₁d (starG_ne γ w hγ)
  have hsp : ∀ i, uu' i ∈ Submodule.span D.host.E (Set.range uu) := by
    have hsub : Set.range (Sum.elim F₂.fvec f) ⊆ Submodule.span D.host.E (Set.range uu) := by
      rintro _ ⟨k, rfl⟩
      rcases k with b | a
      · exact hU b
      · exact Submodule.subset_span ⟨Sum.inl a, rfl⟩
    intro i
    rcases i with a | b
    · exact Submodule.span_le.2 hsub (hsp3 a)
    · exact hU b
  obtain ⟨g, hiso, hgu, -, hform⟩ := FsLA.isom_ext uu uu' hGr hdet hsp
  refine ⟨g, fun k => ∑ m, (FsLA.gram (VS D) uu uu)⁻¹ m k • (uu' m - uu m), hiso, fun b => hgu (Sum.inr b),
    hform, ?_⟩

  have homf : FsLA.om (VS D) F₂.fvec f = starOmL f (frame F'₂) := by
    rw [FsLA.om, hg2, ← Matrix.adjugate_conjTranspose]
    simp only [starOmL, Matrix.conjTranspose_apply]
    rw [← hZ]
    rfl
  have homh : FsLA.om (VS D) F₂.fvec h = g (starOmL f f₁) := by
    simp only [FsLA.om, starOmL, map_sum, map_smul]
    have e : FsLA.gram (VS D) h F₂.fvec = Z₁ᴴ := hZ3
    rw [e]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Matrix.adjugate_conjTranspose, Matrix.conjTranspose_apply]
    congr 1
    exact (hgu (Sum.inl a)).symm
  have e1 : Z₁ᴴ.det = star Z₁.det := Matrix.det_conjTranspose _
  have e2 : (FsLA.gram (VS D) f F₂.fvec).det = star Z.det := by rw [hg2, Matrix.det_conjTranspose]
  rw [e1, e2, homf, homh] at hom3
  exact hom3

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

