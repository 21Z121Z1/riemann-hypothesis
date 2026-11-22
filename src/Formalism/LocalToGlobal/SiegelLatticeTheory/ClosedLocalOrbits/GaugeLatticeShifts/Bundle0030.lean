import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHLIso
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.Bundle0004
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.Bundle0002
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.VolumeIndexBCongruence
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RelativeIndexFlags.VolumeIndexRepresentationOfData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.PairValPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.GenericRatioOfBoundHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0028

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHDim
section
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace Formalism.L2.SG.Pf.BH.Sw

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf Formalism.L2.SG.Pf.BH Formalism.MainNotions.BridgeCSB Formalism.QuantumDeterminants.WeylGroupFacts

variable {k r : ℕ}

theorem lieE_G : Formalism.MainNotions.S.lieE (UH (Hpk k r)) = (uH k r).map RL := by
  have h : Formalism.MainNotions.S.lieOf (UH (Hpk k r)) = ((uH k r : Submodule ℝ (Mat k r)) : Set (Mat k r)) := BH.lieG k r
  unfold Formalism.MainNotions.S.lieE
  rw [h]
  change Submodule.span ℝ (⇑(RL (k := k) (r := r)) '' ↑(uH k r)) = _
  rw [Submodule.span_image, Submodule.span_eq]

theorem lieG' : LieG := fun k r => lieE_G

theorem mulVec_bvec (X : Mat k r) (j i : Fin (2 * r + k + 1)) : (X *ᵥ bvec j) i = X i j := by
  simp [Formalism.QuantumDeterminants.bvec, Matrix.mulVec_single_one]

theorem mid_or (j : Fin (2 * r + k + 1)) (h : ¬ Mid k r j) :
    (∃ a : Fin r, j = eI k r a) ∨ (∃ a : Fin r, j = esI k r a) := by
  simp only [Mid, not_and_or, not_le] at h
  rcases h with h | h
  · exact Or.inl ⟨⟨j, h⟩, Fin.ext rfl⟩
  · refine Or.inr ⟨⟨2 * r + k - j, by omega⟩, Fin.ext ?_⟩
    have hj := j.isLt
    show (j : ℕ) = 2 * r + k - (2 * r + k - j)
    omega

private theorem mul_hpk_apply_lemma (A : Mat k r) (i j : Fin (2 * r + k + 1)) :
    (A * Hpk k r) i j = A i (tau k r j) * sgn k r j := by
  rw [Matrix.mul_apply]
  simp_rw [Formalism.QuantumDeterminants.WeylGroupFacts.hpk_row]
  rw [Finset.sum_eq_single (tau k r j)]
  · rw [tau_tau, if_pos rfl, sgn_tau]
  · intro m _ hm
    rw [if_neg (fun h => hm (by rw [h, tau_tau])), mul_zero]
  · simp

private theorem adjH_apply_lemma_2 (X : Mat k r) (i j : Fin (2 * r + k + 1)) :
    (Hpk k r * Xᴴ * Hpk k r) i j = sgn k r i * star (X (tau k r j) (tau k r i)) * sgn k r j := by
  rw [mul_hpk_apply_lemma, Formalism.QuantumDeterminants.WeylGroupFacts.hpk_mul_apply, Matrix.conjTranspose_apply]

theorem lieWb_set : Formalism.MainNotions.S.lieOf (Formalism.FourierDecayAlt.B2.UWb k r) = (uWb k r : Set (Mat k r)) := by
  rw [BH.lieWb k r]
  ext X
  change _ ↔ (adjH X + X = 0 ∧ ∀ i j, ¬(Mid k r i ∧ Mid k r j) → X i j = 0)
  rw [adjH_def]
  constructor
  · rintro ⟨hX, hc⟩
    have hcol : ∀ i j, ¬ Mid k r j → X i j = 0 := by
      intro i j hj
      rcases mid_or j hj with ⟨a, rfl⟩ | ⟨a, rfl⟩
      · rw [← mulVec_bvec X (eI k r a) i, (hc a).1]; rfl
      · rw [← mulVec_bvec X (esI k r a) i, (hc a).2]; rfl
    refine ⟨hX, fun i j hij => ?_⟩
    rcases not_and_or.1 hij with hi | hj
    · have h := congrFun (congrFun hX i) j
      simp only [Matrix.add_apply, Matrix.zero_apply] at h
      rw [adjH_apply_lemma_2] at h
      have htau : ¬ Mid k r (tau k r i) := by
        have := tau_out i (by simp only [Mid, not_and_or, not_le] at hi; exact hi)
        simp only [Mid, not_and_or, not_le]; exact this
      rw [hcol _ _ htau, star_zero, mul_zero, zero_mul, zero_add] at h
      exact h
    · exact hcol i j hj
  · rintro ⟨hX, hz⟩
    refine ⟨hX, fun a => ⟨?_, ?_⟩⟩
    · funext i
      rw [mulVec_bvec]
      apply hz
      intro h
      have h1 : r ≤ (a : ℕ) := h.2.1
      have := a.isLt
      omega
    · funext i
      rw [mulVec_bvec]
      apply hz
      intro h
      have h2 : 2 * r + k - (a : ℕ) ≤ r + k := h.2.2
      have := a.isLt
      omega

theorem lieWb' : LieWb := by
  intro k r
  refine ⟨fun Z hZ => ?_, ?_⟩
  · have h : Z ∈ Formalism.MainNotions.S.lieOf (Formalism.FourierDecayAlt.B2.UWb k r) := by rw [lieWb_set]; exact hZ
    simpa using h 1
  · unfold Formalism.MainNotions.S.lieE
    rw [lieWb_set]
    have : (fun X => (WithLp.equiv 2 _).symm (Formalism.MainNotions.S.realifyFun X)) '' (uWb k r : Set (Mat k r)) =
        (RL : Mat k r → _) '' (uWb k r : Set (Mat k r)) := rfl
    rw [this, Submodule.span_image, Submodule.span_eq]

def prodEquiv {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (p : Submodule R M) (q : Submodule R N) : ↥(p.prod q) ≃ₗ[R] ↥p × ↥q where
  toFun x := (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩)
  invFun y := ⟨(y.1.1, y.2.1), ⟨y.1.2, y.2.2⟩⟩
  map_add' x y := rfl
  map_smul' c x := rfl
  left_inv x := rfl
  right_inv y := rfl

theorem finrank_prodS {R M N : Type*} [Field R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (p : Submodule R M) (q : Submodule R N) [FiniteDimensional R p] [FiniteDimensional R q] :
    Module.finrank R ↥(p.prod q) = Module.finrank R p + Module.finrank R q := by
  rw [(prodEquiv p q).finrank_eq, Module.finrank_prod]

private theorem eq_zero_of_RL_lemma_3 (M : Mat k r) (h : ‖RL (k := k) (r := r) M‖ ^ 2 = 0) : M = 0 := by
  rw [RL_sq] at h
  ext i j
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg ‖M i j‖))).1 h i (Finset.mem_univ _)
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg ‖M i j‖)).1 h1 j (Finset.mem_univ _)
  simpa using h2

theorem lm_inj {v : Mat k r × (Fin r → ℂ) × Mat k r × Mat k r} (hv : v ∈ Vs k r) (h : Lm k r v = 0) : v = 0 := by
  have hn := lm_norm hv
  rw [h, map_zero, norm_zero] at hn
  have h1 := sq_nonneg ‖RL (k := k) (r := r) v.1‖
  have h2 : 0 ≤ ∑ a : Fin r, ‖v.2.1 a‖ ^ 2 := Finset.sum_nonneg (fun a _ => sq_nonneg _)
  have h3 := sq_nonneg ‖RL (k := k) (r := r) v.2.2.1‖
  have h4 := sq_nonneg ‖RL (k := k) (r := r) v.2.2.2‖
  have e1 : ‖RL (k := k) (r := r) v.1‖ ^ 2 = 0 := by nlinarith
  have e2 : ∑ a : Fin r, ‖v.2.1 a‖ ^ 2 = 0 := by nlinarith
  have e3 : ‖RL (k := k) (r := r) v.2.2.1‖ ^ 2 = 0 := by nlinarith
  have e4 : ‖RL (k := k) (r := r) v.2.2.2‖ ^ 2 = 0 := by nlinarith
  have hx : v.2.1 = 0 := by
    funext a
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => sq_nonneg ‖v.2.1 a‖)).1 e2 a (Finset.mem_univ _)
    simpa using this
  exact Prod.ext (eq_zero_of_RL_lemma_3 _ e1)
    (Prod.ext hx (Prod.ext (eq_zero_of_RL_lemma_3 _ e3) (eq_zero_of_RL_lemma_3 _ e4)))

def lmEquiv (k r : ℕ) : ↥(Vs k r) ≃ₗ[ℝ] ↥(uH k r) :=
  LinearEquiv.ofBijective ((Lm k r).toLinearMap.restrict fun v hv => lm_mem hv)
    ⟨fun a b hab => by
      have h : Lm k r (a.1 - b.1) = 0 := by
        have := congrArg Subtype.val hab
        simp only [LinearMap.restrict_apply] at this
        rw [map_sub]; exact sub_eq_zero.2 this
      exact Subtype.ext (sub_eq_zero.1 (lm_inj ((Vs k r).sub_mem a.2 b.2) h)),
     fun y => by
      obtain ⟨v, hv, hvy⟩ := lm_surj y.2
      exact ⟨⟨v, hv⟩, Subtype.ext hvy⟩⟩

theorem dimG : Formalism.L2.SG.Pf.BH.DimG := by
  intro k r
  have eG : Module.finrank ℝ ↥(Formalism.MainNotions.S.lieE (UH (Hpk k r))) = Module.finrank ℝ ↥(uH k r) := by
    rw [lieE_G]; exact ((Submodule.equivMapOfInjective _ RL_injective (uH k r)).finrank_eq).symm
  have eN : Module.finrank ℝ ↥(Formalism.MainNotions.S.lieE (Nset k r)) = Module.finrank ℝ ↥(lieNS k r) := by
    rw [lieE_N]; exact ((Submodule.equivMapOfInjective _ RL_injective (lieNS k r)).finrank_eq).symm
  have eW : Module.finrank ℝ ↥(Formalism.MainNotions.S.lieE (Formalism.FourierDecayAlt.B2.UWb k r)) = Module.finrank ℝ ↥(uWb k r) := by
    rw [(lieWb' k r).2]; exact ((Submodule.equivMapOfInjective _ RL_injective (uWb k r)).finrank_eq).symm
  rw [eG, eN, eW, ← (lmEquiv k r).finrank_eq]
  unfold Vs
  rw [finrank_prodS, finrank_prodS, finrank_prodS, finrank_top, Module.finrank_pi_fintype]
  simp only [Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  ring

end Formalism.L2.SG.Pf.BH.Sw
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.PairValG
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef Formalism.L2.SG.PairVal

namespace Formalism.L2.SG.Pf.PairValG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem gval_eq_G (hrows : IsRowReps D F0 what₂) {t : Term D u u' F0 what₂}
    {F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)} (hrep : Rep t.lam (lf D F0) (PD D t.lam (lf D F0) u') t.cls F') :
    Gval (lf D F0) F' = t.G := by
  obtain ⟨h, hmk⟩ := hrep
  have hGF := (Formalism.L2.SG.Closed.TermFun_holds D u u' F0 t.lam (hrows.1 t.lam t.mem)).1
  change _ = Gt t.lam (lf D F0) (PD D t.lam (lf D F0) u') t.cls
  rw [← hmk]
  exact (Gt_mk hGF ⟨F', h⟩).symm

theorem atPt_of_normRep {t : Term D u u' F0 what₂} {w : Point D.host.E (D.R.rS + 1)}
    {F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)} {L U : MatR D} (hN : NormRep t w F' L U)
    (hG : Gval (lf D F0) F' ≠ 0) : t.atPt w :=
  ⟨F', hN.1, hG, ⟨L, U, hN.2.2.1, hN.2.2.2.1, hN.2.2.2.2⟩⟩

theorem vRdef_eq_of (hV : Formalism.L2.SG.Pf.RelativeIndexFlags.VolumeIndexRepresentationNonzero D u u' F0 what₂) (hrows : IsRowReps D F0 what₂)
    (δ : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, (D.s.atP p).Fp)
    (M : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, Formalism.MainNotions.S.Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (hAg : ∀ p, Formalism.MainNotions.S.LocalSplitGroups.Agree δ M p) (t : Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (L U : MatR D) (hr : t.relevant) (hg : t.generic)
    (hN : NormRep t w F' L U) (hG : Gval (lf D F0) F' ≠ 0) :
    vRdef D u u' F0 what₂ δ M t = volIdx D u u' F0 what₂ δ M t w F' L := by
  have hex : t.relevant ∧ t.generic ∧
      ∃ x : Point D.host.E (D.R.rS + 1) × LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E) × MatR D × MatR D,
        NormRep t x.1 x.2.1 x.2.2.1 x.2.2.2 := ⟨hr, hg, ⟨(w, F', L, U), hN⟩⟩
  unfold vRdef
  rw [dif_pos hex]
  have hx := hex.2.2.choose_spec
  set x := hex.2.2.choose with hxdef
  have hGx : Gval (lf D F0) x.2.1 ≠ 0 := by
    rw [gval_eq_G hrows hx.1, ← gval_eq_G hrows hN.1]; exact hG
  have hw : x.1 = w := cell_point_unique_of_term_fun (Formalism.L2.SG.Closed.TermFun_holds D u u') hrows t x.1 w
    (atPt_of_normRep hx hGx) (atPt_of_normRep hN hG)
  have hx' : NormRep t w x.2.1 x.2.2.1 x.2.2.2 := hw ▸ hx
  have e1 : volIdx D u u' F0 what₂ δ M t x.1 x.2.1 x.2.2.1 = volIdx D u u' F0 what₂ δ M t w x.2.1 x.2.2.1 := by rw [hw]
  rw [e1]
  exact hV δ M hAg t w x.2.1 F' x.2.2.1 x.2.2.2 L U hr hg hx' hGx hN hG

theorem vRdef_pos_of (hFin : Formalism.L2.SG.Pf.RelativeIndexFlags.VolIdxFinP D u u' F0 what₂) (hrows : IsRowReps D F0 what₂)
    (δ : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, (D.s.atP p).Fp)
    (M : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, Formalism.MainNotions.S.Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (hAg : ∀ p, Formalism.MainNotions.S.LocalSplitGroups.Agree δ M p) (t : Term D u u' F0 what₂) (hG : t.G ≠ 0) :
    0 < vRdef D u u' F0 what₂ δ M t := by
  unfold vRdef
  split_ifs with h
  · have hx := h.2.2.choose_spec
    have hGx : Gval (lf D F0) h.2.2.choose.2.1 ≠ 0 := by rw [gval_eq_G hrows hx.1]; exact hG
    obtain ⟨h1, h2⟩ := hFin δ M hAg t _ _ _ _ h.1 h.2.1 hx hGx
    unfold volIdx
    exact div_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero h1)) (Nat.cast_pos.2 (Nat.pos_of_ne_zero h2))
  · exact one_pos

theorem volIdxFinP_of (hyps : Formalism.L2.SG.Pf.StabilizerIndexVolumes.Hyps D u u' F0 what₂)
    (hDel : ∀ δ M, Formalism.L2.SG.Pf.StabilizerIndexVolumes.DeltaAE D δ M)
    (hAbdd : ∀ δ M, Formalism.L2.SG.Pf.StabilizerIndexVolumes.ABddOf D u u' F0 what₂ δ M)
    (hAcong : ∀ δ M, Formalism.L2.SG.Pf.StabilizerIndexVolumes.ACong D u u' F0 what₂ δ M) :
    Formalism.L2.SG.Pf.RelativeIndexFlags.VolIdxFinP D u u' F0 what₂ := fun δ M =>
  Formalism.L2.SG.Pf.StabilizerIndexVolumes.volume_index_finite_of_hyps D u u' F0 what₂ δ M hyps Formalism.L2.SG.Pf.StabilizerIndexVolumes.commens
    Formalism.L2.SG.Pf.StabilizerIndexVolumes.stClosed (hDel δ M) (Formalism.L2.SG.Pf.StabilizerIndexVolumes.volume_index_a_stable D u u' F0 what₂ δ M) (hAbdd δ M)
    (hAcong δ M) (Formalism.L2.SG.Pf.StabilizerIndexVolumes.volume_index_b_stable D u u' F0 what₂ δ M) (Formalism.L2.SG.Pf.StabilizerIndexVolumes.volume_index_b_bounded D u u' F0 what₂ δ M)
    (Formalism.L2.SG.Pf.StabilizerIndexVolumes.volume_index_b_congruence D u u' F0 what₂ δ M)

theorem volume_index_representation_of_hyps (hyps : Formalism.L2.SG.Pf.StabilizerIndexVolumes.Hyps D u u' F0 what₂)
    (hDel : ∀ δ M, Formalism.L2.SG.Pf.StabilizerIndexVolumes.DeltaAE D δ M)
    (hAbdd : ∀ δ M, Formalism.L2.SG.Pf.StabilizerIndexVolumes.ABddOf D u u' F0 what₂ δ M)
    (hAcong : ∀ δ M, Formalism.L2.SG.Pf.StabilizerIndexVolumes.ACong D u u' F0 what₂ δ M) :
    Formalism.L2.SG.Pf.RelativeIndexFlags.VolumeIndexRepresentationNonzero D u u' F0 what₂ :=
  volume_index_representation_of_data D u u' F0 what₂ hyps.1 hyps.2.1 hyps.2.2.1 hyps.2.2.2.1 hyps.2.2.2.2.1 hyps.2.2.2.2.2
    (volIdxFinP_of hyps hDel hAbdd hAcong)

end Formalism.L2.SG.Pf.PairValG
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.UpMatZero
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal ComplexConjugate
open Matrix

namespace Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting

def mulU {r : ℕ} (a b : UC r) : UC r := fun p => (upMat a * upMat b) p.1.1 p.1.2

structure IsClSub {n : ℕ} {ε : Fin n → Bool} (H : Set (Formalism.REAL.UJ ε)) : Prop where
  one_mem : (1 : Formalism.REAL.UJ ε) ∈ H
  mul_mem : ∀ x ∈ H, ∀ y ∈ H, x * y ∈ H
  inv_mem : ∀ x ∈ H, x⁻¹ ∈ H
  closed : IsClosed H

def SSHaar : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Set (Formalism.REAL.UJ ε)), IsClSub H →
    (∃ μ, IsHaarS H μ) ∧
    ∀ μ m : Measure (Formalism.REAL.UJ ε), IsHaarS H μ → m Hᶜ = 0 → (∀ s ∈ H, m.map (fun x => s * x) = m) →
      IsFiniteMeasureOnCompacts m → ∃ c : ℝ≥0∞, c ≠ ∞ ∧ m = c • μ

def SSGrp : Prop :=
  ∀ (n r k : ℕ) (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ) (T T' : ℝ),
    FrameLoc ε k e z z' T T' → IsClSub (SLoc ε e z) ∧ IsClSub (GradedDegreeZeroIsLocal ε e z)

def SSSec : Prop :=
  ∀ (n r k : ℕ) (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ) (T T' sc : ℝ),
    FrameLoc ε k e z z' T T' → 0 < sc →
    ∃ σ : UC r → Formalism.REAL.UJ ε, Continuous σ ∧ (∀ y, σ y ∈ SLoc ε e z) ∧
      ∀ y b, uMat (σ y)⁻¹ *ᵥ famSc sc e z b = ∑ a, upMat y a b • famSc sc e z a

def SSCoord : Prop :=
  ∀ (n r k : ℕ) (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ) (T T' sc : ℝ),
    FrameLoc ε k e z z' T T' → 0 < sc →
    ∃ π : Formalism.REAL.UJ ε → UC r, Continuous π ∧
      (∀ g ∈ SLoc ε e z, ∀ y : UC r,
        (∀ b, uMat g⁻¹ *ᵥ famSc sc e z b = ∑ a, upMat y a b • famSc sc e z a) → π g = y) ∧
      (∀ g ∈ SLoc ε e z, ∀ h ∈ SLoc ε e z, π (g * h) = mulU (π h) (π g)) ∧
      (∀ g ∈ SLoc ε e z, ∀ h ∈ SLoc ε e z, π g = π h → g * h⁻¹ ∈ GradedDegreeZeroIsLocal ε e z) ∧
      (∀ g ∈ GradedDegreeZeroIsLocal ε e z, g ∈ SLoc ε e z ∧ π g = 0)

def SSBiInv0 : Prop :=
  ∀ (n r k : ℕ) (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ) (T T' : ℝ),
    FrameLoc ε k e z z' T T' →
    ∀ μ0 : Measure (Formalism.REAL.UJ ε), IsHaarS (GradedDegreeZeroIsLocal ε e z) μ0 →
    ∀ t ∈ SLoc ε e z, ∀ u ∈ SLoc ε e z, t * u ∈ GradedDegreeZeroIsLocal ε e z → μ0.map (fun x => t * x * u) = μ0

def SSLebU : Prop :=
  ∀ (r : ℕ) (b : UC r), MeasurePreserving (fun a : UC r => mulU a b) volume volume

theorem upMat_zero {r : ℕ} : upMat (0 : UC r) = 1 := by
  ext a b
  simp only [upMat, Matrix.of_apply, Pi.zero_apply, Matrix.one_apply]
  split_ifs <;> rfl

theorem mulU_zero {r : ℕ} (y : UC r) : mulU y 0 = y := by
  funext p
  simp only [mulU]
  rw [upMat_zero, Matrix.mul_one]
  simp only [upMat, Matrix.of_apply]
  rw [if_neg (ne_of_lt p.2), dif_pos p.2]

end Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL
end
end

