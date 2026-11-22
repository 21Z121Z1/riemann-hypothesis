import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocalDiscriminantIsUnit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0392
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0401
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0260
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0256
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0460
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0388
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0395
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0394
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0396
import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalFlagExistsUniqueSemistable
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0222
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0246
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0459
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0158
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0149
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0164

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MovedTermLatticeIsLocalTermAtPlace
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HL.MovedTermLoc

theorem uni_mul {R : Type} [CommRing R] {n : ℕ} (A B : Matrix (Fin n) (Fin n) R) (hA : Uni A) (hB : Uni B) :
    Uni (A * B) := by
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    rcases lt_or_ge c a with h | h
    · rw [hA.1 a c h, zero_mul]
    · rw [hB.1 c b (lt_of_lt_of_le hab h), mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [hA.2 a, hB.2 a, one_mul]
    · intro c _ hc
      rcases lt_or_gt_of_ne hc with h | h
      · rw [hA.1 a c h, zero_mul]
      · rw [hB.1 c a h, mul_zero]
    · intro h; exact absurd (Finset.mem_univ a) h

theorem uni_map {R S : Type} [CommRing R] [CommRing S] {n : ℕ} (f : R →+* S) (A : Matrix (Fin n) (Fin n) R)
    (hA : Uni A) : Uni (A.map f) :=
  ⟨fun a b h => by simp [Matrix.map_apply, hA.1 a b h], fun a => by simp [Matrix.map_apply, hA.2 a]⟩

theorem map_inv_of_det {R S : Type} [CommRing R] [CommRing S] {n : ℕ} (f : R →+* S)
    (A : Matrix (Fin n) (Fin n) R) (hA : IsUnit A.det) : (A⁻¹).map f = (A.map f)⁻¹ := by
  symm
  refine Matrix.inv_eq_right_inv ?_
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hA, Matrix.map_one _ f.map_zero f.map_one]

theorem chg_scaled {D : D7} (Z : LocDat D) (p : PlF D) (f g : Fin (D.R.rS + 1) → (VS D).V)
    (A : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) (hg : Chg f A g) :
    Chg (scaled Z p f) (fun a b => Ring.inverse (frFac Z.δ p a) * frFac Z.δ p b * (D.s.atP p).ιE (A a b))
      (scaled Z p g) := by
  intro b
  simp only [scaled]
  rw [hg b, Formalism.L2.SG.Pf.BBTie.bt_bc_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [smul_smul, smul_smul]
  congr 1
  have h := Ring.inverse_mul_cancel _ (Formalism.L2.SG.Pf.BBTie.bt_frFac_unit Z p a)
  linear_combination (-(frFac Z.δ p b * (D.s.atP p).ιE (A a b))) * h

set_option maxHeartbeats 1600000 in

theorem main : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F'0 : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → ∀ (p : PlF D) (ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E)), AdmWit t₀.lam (gS D) (lf D (X.Fu u)) t₀.frame ξ → ∀ (N N' : G.GLV), (∀ b, N (G.f b) = ∑ a, U a b • G.f a) → (∀ b, N' (G.f' b) = ∑ a, (U' * (ξ.map (algebraMap (𝓞 D.host.E) D.host.E))⁻¹) a b • G.f' a) → ∀ (m m' : (G.S p).GLV), (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).Ext p N m → (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).Ext p N' m' → ∃ (t : Loc.Term (Vp D p) (Y.M p) D.R.rS) (d : LocNG.Datum (FP p)), LocNG.IsTermOver (FP p) d t ∧ (c.c p).lat t.abelian₂ = (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).lat p (c.lat ρ t₀.lam) ∧ (∀ b, (c.c p).e (t.f b) = m ((G.S p).f b)) ∧ ∀ b, (c.c p).e (t.f' b) = m' ((G.S p).f' b) := by
  intro D X Y u u' hSt hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hMv p ξ hξ N N' hN hN' m m' hm hm'
  have hR : IsRowLat D (X.Fu u) t₀.lam := (Y.rowsOK u).1 t₀.lam t₀.mem
  have hPD : Formalism.L2.SG.TermDef.PD D t₀.lam (lf D (X.Fu u)) u' t₀.frame := t₀.rep.2.2.2.2
  have hGt : Gval (lf D (X.Fu u)) t₀.frame ≠ 0 := fun h0 => hG ((GlobalTheory.T.frame_pair_gram_invariant_unchanged_isometry D _ _ _ _ ρ U U' hMv).symm.trans h0)
  obtain ⟨g, hgE, hgU⟩ := GlobalTheory.T.exists_unitary_extension_rational_isometry D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p ρ hMv.1
  obtain ⟨hT0, -⟩ := GlobalTheory.T.unsignedLocalTerm_row_lattice_isTerm D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) u u' (X.Fu u) t₀.lam hR t₀.frame hPD hGt p
  set ξ0 := admXi D t₀.lam (lf D (X.Fu u)) t₀.frame with hξ0
  set t0 := locU (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p t₀.lam (lf D (X.Fu u)) t₀.frame (Tu D u) (Tu D u') with ht0
  have hTg := GlobalTheory.T.isTerm_unitary_move_localTerm (Y.M p) (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS g t0 hgU hT0

  have hUu : Uni U := ⟨fun a b h => (hMv.2.1 a b).1 h, fun a => (hMv.2.1 a a).2 rfl⟩
  have hU'u : Uni U' := ⟨fun a b h => (hMv.2.2.1 a b).1 h, fun a => (hMv.2.2.1 a a).2 rfl⟩
  have hξ0u : Uni ξ0 := admissibility_witness_unitriangular t₀.lam (lf D (X.Fu u)) t₀.frame
  have hξ0i : Uni ξ0⁻¹ := inv_unitri _ hξ0u.1 hξ0u.2
  have hξu : Uni ξ := ⟨hξ.1, hξ.2.1⟩
  have hξi : Uni ξ⁻¹ := inv_unitri _ hξu.1 hξu.2
  have hξ0w : AdmWit t₀.lam (gS D) (lf D (X.Fu u)) t₀.frame ξ0 := by
    rw [hξ0]; unfold admXi; rw [dif_pos hPD.2.1]; exact hPD.2.1.choose_spec
  set alg := algebraMap (𝓞 D.host.E) D.host.E with halg
  set B0 := U' * (ξ0⁻¹).map alg with hB0
  set B1 := U' * (ξ.map alg)⁻¹ with hB1
  set C := (ξ0 * ξ⁻¹).map alg with hC
  have hB0u : Uni B0 := uni_mul _ _ hU'u (uni_map _ _ hξ0i)
  have hCu : Uni C := uni_map _ _ (uni_mul _ _ hξ0u hξi)
  have hBC : B0 * C = B1 := by
    rw [hB0, hB1, hC, Matrix.map_mul, ← map_inv_of_det alg ξ (Formalism.L2.SG.Pf.BBTie.bt_unitri_det _ hξu.1 hξu.2),
      Matrix.mul_assoc, ← Matrix.mul_assoc ((ξ0⁻¹).map alg), ← Matrix.map_mul,
      Matrix.nonsing_inv_mul _ (Formalism.L2.SG.Pf.BBTie.bt_unitri_det _ hξ0u.1 hξ0u.2),
      Matrix.map_one _ alg.map_zero alg.map_one, Matrix.one_mul]

  have hf : ∀ b, (move g t0).f b = scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (fun b => ∑ a, U a b • frame F00 a) b := by
    intro b
    show g (frFac (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).δ p b • baseChange₂ D p (frame (lf D (X.Fu u)) b)) = frFac (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).δ p b • baseChange₂ D p _
    rw [map_smul, hgE]
    exact congrArg (fun x => frFac _ p b • baseChange₂ D p x) (hMv.2.2.2.1 b)
  have hf' : ∀ b, (move g t0).f' b = scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (fun b => ∑ a, B0 a b • frame F'0 a) b := by
    intro b
    show g (frFac (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).δ p b • baseChange₂ D p (frameAct (frame t₀.frame) ξ0⁻¹ b)) = frFac (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).δ p b • baseChange₂ D p _
    rw [map_smul, hgE]
    congr 2
    simp only [frameAct, map_sum, map_smul, hMv.2.2.2.2, Finset.smul_sum, smul_smul, hB0, Matrix.mul_apply,
      Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
    rw [Matrix.map_apply, mul_comm]
  have hTri1 : Tri (D.s.atP p).Ep (FP p).A.f (move g t0).f := by
    obtain ⟨Ap, hAp, -⟩ := tri_scaled D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) (frame F00) (fun b => ∑ a, U a b • frame F00 a) U hUu (fun b => rfl)
    rw [(hAt p).1.1]
    exact ⟨Ap p, (hAp p).1, fun b => by rw [hf b]; exact (hAp p).2 b⟩
  have hTri2 : Tri (D.s.atP p).Ep (FP p).B.f (move g t0).f' := by
    obtain ⟨Ap, hAp, -⟩ := tri_scaled D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) (frame F'0) (fun b => ∑ a, B0 a b • frame F'0 a) B0 hB0u (fun b => rfl)
    rw [(hAt p).1.2.1]
    exact ⟨Ap p, (hAp p).1, fun b => by rw [hf' b]; exact (hAp p).2 b⟩
  obtain ⟨d, hd⟩ := GlobalTheory.T.exists_datum_of_two_congruent_frames (Y.M p) (Y.agree p).1 (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS (FP p) (move g t0) hTg
    (hAt p).1.2.2.1.symm (hAt p).1.2.2.2.symm hTri1 hTri2

  set A' : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep :=
    fun a b => Ring.inverse (frFac (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).δ p a) * frFac (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).δ p b * (D.s.atP p).ιE (C a b) with hA'
  set tf' := scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (fun b => ∑ a, B1 a b • frame F'0 a) with htf'
  have hChg1 : Chg (move g t0).f (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep) (move g t0).f := by
    intro b
    simp [Matrix.one_apply]
  have hChg2 : Chg (move g t0).f' A' tf' := by
    have hc : Chg (fun b => ∑ a, B0 a b • frame F'0 a) C (fun b => ∑ a, B1 a b • frame F'0 a) := by
      intro b
      rw [← hBC]
      simp only [Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
      rw [mul_comm]
    have h := chg_scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p _ _ C hc
    intro b
    refine (h b).trans ?_
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hf' a]
  have hfin : Module.finrank (D.s.atP p).Ep (Vp D p) = D.R.k + 2 * D.R.rS + 1 := by
    rw [finrank_Vp]
    obtain ⟨j, hj⟩ := D.R.m_even
    have := D.R.two_le_m
    simp only [Ranks.r, Ranks.rS]
    omega
  have hA'u : Uni A' := by
    refine ⟨fun a b h => ?_, fun a => ?_⟩
    · simp [hA', hCu.1 a b h]
    · show Ring.inverse (frFac (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).δ p a) * frFac (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).δ p a * (D.s.atP p).ιE (C a a) = 1
      rw [hCu.2 a, map_one, mul_one, Ring.inverse_mul_cancel _ (Formalism.L2.SG.Pf.BBTie.bt_frFac_unit (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p a)]
  have hcong := GlobalTheory.T.admissibility_witnesses_congr_mod_theta_local D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) u u' (X.Fu u) t₀.lam t₀.frame hR hPD ξ0 ξ hξ0w hξ p
  have hint : ∀ a b, (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep) a b ∈ (Y.M p).L.O ∧
      A' a b ∈ (Y.M p).L.O ∧ (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep) a b - A' a b ∈
        Submodule.span (Y.M p).L.O {algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Formalism.MainNotions.S.LocNG.theta (Y.M p))} := by
    intro a b
    rcases lt_or_ge b a with h | h
    · have e0 : A' a b = 0 := by simp [hA', hCu.1 a b h]
      rw [e0, Matrix.one_apply_ne (ne_of_lt h).symm, sub_zero]
      exact ⟨Subring.zero_mem _, Subring.zero_mem _, Submodule.zero_mem _⟩
    · obtain ⟨k, hkO, hkb⟩ := Formalism.L2.SG.Pf.BBTie.bt_frFac_step (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (Formalism.L2.SG.Pf.locDiffC_holds D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) a b h
      have e1 : A' a b = k * (D.s.atP p).ιE (C a b) := by
        show Ring.inverse (frFac (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).δ p a) * frFac (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).δ p b * (D.s.atP p).ιE (C a b) = _
        rw [hkb, mul_comm k, ← mul_assoc, Ring.inverse_mul_cancel _ (Formalism.L2.SG.Pf.BBTie.bt_frFac_unit (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p a), one_mul]
      have hCO : (D.s.atP p).ιE (C a b) ∈ (Y.M p).L.O := Formalism.L2.SG.Pf.BBTie.bt_iota_int (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p ((ξ0 * ξ⁻¹) a b)
      have hAO : A' a b ∈ (Y.M p).L.O := by rw [e1]; exact Subring.mul_mem _ hkO hCO
      refine ⟨?_, hAO, ?_⟩
      · by_cases hab : a = b
        · subst hab; rw [Matrix.one_apply_eq]; exact Subring.one_mem _
        · rw [Matrix.one_apply_ne hab]; exact Subring.zero_mem _
      · rcases eq_or_lt_of_le h with hab | hab
        · subst hab
          rw [hA'u.2 a, Matrix.one_apply_eq, sub_self]; exact Submodule.zero_mem _
        · have hc := hcong a b
          rw [Matrix.one_apply_ne (ne_of_lt hab), sub_zero] at hc
          rw [Matrix.one_apply_ne (ne_of_lt hab), zero_sub, e1, ← neg_mul]
          have := Submodule.smul_mem _ (⟨-k, Subring.neg_mem _ hkO⟩ : (Y.M p).L.O) hc
          exact this
  have hT := GlobalTheory.T.hermitian_frame_witness_integral_change (Y.M p) (Y.agree p).1 (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS D.R.k (FP p) hfin (hAt p).2 d (move g t0) hd
    1 A' (move g t0).f tf' (⟨fun a b h => Matrix.one_apply_ne (ne_of_lt h).symm, fun a => Matrix.one_apply_eq a⟩)
    hA'u hint hChg1 hChg2
  have hlat := (GlobalTheory.T.rational_unipotent_groups_lattices_global_coordinates D X Y u u' hSt hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hMv).2.2.2.2.1 ρ hMv.1 p g
    t₀.lam hgE
  have hfc := GlobalTheory.T.scaled_unitriangular_change_eq_local_image D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G c p N m hm U
  have hfc' := GlobalTheory.T.scaled_unitriangular_change_eq_local_image D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G c p N' m' hm' B1
  refine ⟨⟨(move g t0).abelian₂, (move g t0).f, tf', (move g t0).T, (move g t0).T'⟩, d, hT, hlat.symm, fun b => ?_,
    fun b => ?_⟩
  · show (c.c p).e ((move g t0).f b) = _
    rw [hf b]; exact hfc.1 hN b
  · exact hfc'.2 hN' b

end GlobalTheory.HL.MovedTermLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NonzeroFlagProbabilityBoundOfVolumeRatioInductio
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.NonzeroFlag

theorem telescope : ∀ (a : ℕ) (r : Fin (a + 1) → ℕ) (j : Fin a → ℕ),
    (∀ i : Fin a, r i.succ = r i.castSucc + j i) → r (Fin.last a) = r 0 + ∑ i, j i := by
  intro a
  induction a with
  | zero => intro r j _; simp
  | succ a ih =>
    intro r j h
    have h1 := ih (fun i => r i.castSucc) (fun i => j i.castSucc) (fun i => h i.castSucc)
    have h2 := h (Fin.last a)
    rw [Fin.sum_univ_castSucc]
    have h3 : r (Fin.last (a + 1)) = r (Fin.last a).castSucc + j (Fin.last a) := h2
    have h4 : r (Fin.last a).castSucc = r 0 + ∑ i : Fin a, j i.castSucc := h1
    omega

theorem exists_composition (a : ℕ) (j : Fin a → ℕ) (hj : ∀ i, 1 ≤ j i) (J : ℕ) (hJ : ∑ i, j i = J)
    (P : ∀ a : ℕ, (Fin a → ℕ) → Prop) (h : P a j) :
    ∃ c : Composition J, P c.length c.blocksFun := by
  have key : ∀ (b : ℕ) (e : b = a) (j' : Fin b → ℕ), (∀ i, j' i = j (Fin.cast e i)) → P b j' := by
    intro b e j' hh
    subst e
    have : j' = j := funext hh
    rw [this]; exact h
  refine ⟨⟨List.ofFn j, ?_, ?_⟩, key _ (by simp [Composition.length]) _ ?_⟩
  · intro i hi
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hi
    exact hj k
  · rw [List.sum_ofFn, hJ]
  · intro i
    simp [Composition.blocksFun]
    rfl

theorem measurableSet_simplexH (a : ℕ) : MeasurableSet (simplexH a) := by
  have : simplexH a = (⋂ i : Fin a, ⋂ k : Fin a, ⋂ _ : i < k, {τ : Fin a → ℝ | τ i < τ k}) ∩
      ⋂ i : Fin a, ({τ : Fin a → ℝ | 0 < τ i} ∩ {τ : Fin a → ℝ | τ i < 1 / 2}) := by
    ext τ
    simp [simplexH, StrictMono]
  rw [this]
  refine MeasurableSet.inter ?_ ?_
  · exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
      measurableSet_lt (measurable_pi_apply i) (measurable_pi_apply k)
  · exact MeasurableSet.iInter fun i => (measurableSet_lt measurable_const (measurable_pi_apply i)).inter
      (measurableSet_lt (measurable_pi_apply i) measurable_const)

theorem mem_typeSet (I : AutInst) (p q : ℕ) (hs : HasSig I p q) (x : I.GA) (hx : stepLt I x (1 / 2) ≠ ⊥) :
    ∃ J ∈ Finset.Icc 1 q, ∃ c : Composition J, x ∈ typeSet I c.blocksFun (simplexH c.length) := by
  obtain ⟨⟨a, S, τ, hF⟩, -, h3⟩ := GlobalTheory.PointFlag.flag_spec I x
  have h3 := (h3 a S τ hF).1
  set j : Fin a → ℕ := fun i => Formalism.HN.rkK (S i.succ) - Formalism.HN.rkK (S i.castSucc) with hjdef
  have hj1 : ∀ i, 1 ≤ j i := fun i => by have := (h3 i).2.1; simp only [hjdef]; omega
  have hj2 : ∀ i, Formalism.HN.rkK (S i.succ) = Formalism.HN.rkK (S i.castSucc) + j i := fun i => by
    have := (h3 i).2.1; simp only [hjdef]; omega
  have htel := telescope a (fun i => Formalism.HN.rkK (S i)) j hj2
  obtain ⟨v⟩ : Nonempty (InfinitePlace I.F) := inferInstance
  have hr := (GlobalTheory.T.canonicalLatticeFlag_isotropic_selfDual I x).2.1 v
  have hq : rkR (I.ε v) ≤ q := by
    rw [← (hs v).2]; exact min_le_right _ _
  have hle : ∑ i, j i ≤ q := by
    simp only [hF.2.2.1] at htel
    omega
  have ha : a ≠ 0 := by
    rintro rfl
    apply hx
    rw [← hF.2.2.1, ← hF.1]; rfl
  have hge : 1 ≤ ∑ i, j i :=
    (hj1 ⟨0, Nat.pos_of_ne_zero ha⟩).trans (Finset.single_le_sum (fun i _ => Nat.zero_le (j i)) (mem_univ _))
  refine ⟨∑ i, j i, Finset.mem_Icc.mpr ⟨hge, hle⟩, ?_⟩
  refine exists_composition a j hj1 _ rfl (fun a j => x ∈ typeSet I j (simplexH a)) ?_
  exact ⟨τ, ⟨hF.2.2.2.1, fun i => ⟨(hF.2.2.2.2.1 i).1, (hF.2.2.2.2.1 i).2.1⟩⟩, S, hF, hj2⟩

theorem nonzeroFlagBound : VolumeStep → NonzeroFlagBound := by
  intro hV I μf _ _ fund hfund p q hs hn hq hrd hf
  obtain ⟨hfd, hv, -, hf1, -, hpq⟩ := GlobalTheory.T.autInst_degree_rootDiscriminant_rank I
  have hpq := hpq p q hs
  have hn16 : 16 ≤ I.n := by
    have hpos : (0 : ℝ) < I.n := by
      rcases Nat.eq_zero_or_pos I.n with h | h
      · rw [h] at hn; simp at hn; linarith
      · exact_mod_cast h
    have := Real.log_le_sub_one_of_pos hpos
    have : (16 : ℝ) ≤ I.n := by linarith
    exact_mod_cast this
  have h2q : 2 * q + 2 ≤ I.n := by nlinarith
  set X : ℝ := I.n * I.f * Real.log I.n with hX
  have hX15 : 15 ≤ X := by
    have h1 : (1 : ℝ) ≤ I.n := by exact_mod_cast (by omega : 1 ≤ I.n)
    have h2 : (1 : ℝ) ≤ I.f := by exact_mod_cast hf1
    have h3 : (1 : ℝ) ≤ I.n * I.f := one_le_mul_of_one_le_of_one_le h1 h2
    rw [hX]; nlinarith
  have hone : ∀ J ∈ Finset.Icc 1 q, ∀ c : Composition J,
      I.muA μf (typeSet I c.blocksFun (simplexH c.length) ∩ fund) / I.muA μf fund ≤
        ENNReal.ofReal (Real.exp (-(1 / 2 * J * X))) := by
    intro J hJ c
    obtain ⟨hJ1, hJq⟩ := Finset.mem_Icc.mp hJ
    have hsum := c.sum_blocksFun
    have hT := (GlobalTheory.T.isotropicFlagProbabilityBound_of_volumeRatio hV I μf fund hfund p q hs h2q c.length c.blocksFun
      (c.length_pos_of_pos hJ1) c.one_le_blocksFun (by omega) _ (measurableSet_simplexH _) subset_rfl).2.2.2
    have hD := GlobalTheory.T.lintegral_flagSizeDensity_le_one I.n I.f c.length c.blocksFun hf1 c.one_le_blocksFun (by omega)
    have hK := GlobalTheory.T.flag_explicit_constant_le_exp_neg_half I.E I.cm.cmUnram p q c.length c.blocksFun c.one_le_blocksFun (by omega)
      (by rw [hpq]; exact hn) (by rw [hpq]; exact hq) (by rw [hpq, hv]; exact hrd) (by rw [hpq, hfd]; exact hf)
    rw [hpq, hfd, hsum] at hK
    refine hT.trans ((mul_le_mul_right hD _).trans ?_)
    rw [mul_one]
    refine ENNReal.ofReal_le_ofReal (hK.trans (le_of_eq ?_))
    rw [hX]; congr 1; ring
  have hsub : {x | stepLt I x (1 / 2) ≠ ⊥} ∩ fund ⊆
      ⋃ J ∈ Finset.Icc 1 q, ⋃ c ∈ (Finset.univ : Finset (Composition J)),
        typeSet I c.blocksFun (simplexH c.length) ∩ fund := by
    rintro x ⟨hx, hxf⟩
    obtain ⟨J, hJ, c, hc⟩ := mem_typeSet I p q hs x hx
    simp only [Set.mem_iUnion]
    exact ⟨J, hJ, c, mem_univ _, hc, hxf⟩
  have hμ : I.muA μf ({x | stepLt I x (1 / 2) ≠ ⊥} ∩ fund) ≤
      ∑ J ∈ Finset.Icc 1 q, ∑ c : Composition J,
        I.muA μf (typeSet I c.blocksFun (simplexH c.length) ∩ fund) :=
    (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans
      (Finset.sum_le_sum fun J _ => measure_biUnion_finset_le _ _))
  calc I.muA μf ({x | stepLt I x (1 / 2) ≠ ⊥} ∩ fund) / I.muA μf fund
      ≤ (∑ J ∈ Finset.Icc 1 q, ∑ c : Composition J,
        I.muA μf (typeSet I c.blocksFun (simplexH c.length) ∩ fund)) / I.muA μf fund :=
        ENNReal.div_le_div_right hμ _
    _ = ∑ J ∈ Finset.Icc 1 q, ∑ c : Composition J,
        I.muA μf (typeSet I c.blocksFun (simplexH c.length) ∩ fund) / I.muA μf fund := by
        simp only [div_eq_mul_inv, Finset.sum_mul]
    _ ≤ ∑ J ∈ Finset.Icc 1 q, ∑ _c : Composition J, ENNReal.ofReal (Real.exp (-(1 / 2 * J * X))) :=
        Finset.sum_le_sum fun J hJ => Finset.sum_le_sum fun c _ => hone J hJ c
    _ = ENNReal.ofReal (∑ J ∈ Finset.Icc 1 q, (2 : ℝ) ^ (J - 1) * Real.exp (-(1 / 2 * J * X))) := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun J _ => by positivity)]
        refine Finset.sum_congr rfl fun J _ => ?_
        rw [Finset.sum_const, Finset.card_univ, composition_card, nsmul_eq_mul,
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num)]
        simp
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ((GlobalTheory.T.sum_two_pow_pred_mul_exp_neg_le_exp_neg_third q X hX15).trans (le_of_eq ?_))
        rw [hX]; congr 1; ring

end GlobalTheory.NonzeroFlag
end

