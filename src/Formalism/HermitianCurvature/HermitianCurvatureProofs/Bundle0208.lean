import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousUnipotentVectorScalar
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0202
import Formalism.UnipotentAdelicQuotients.EllRegCheck
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0201

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CcCoefMMono
section
open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.LastBlockContinuity

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem xs_eq_phi {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    (T : D.LevTower k r Wp Wq) (χ : ℝ → ℝ) (ε : ℝ) (i : ℕ) (hi : i ≤ r) (w : List C.Letter)
    (a : Wd.Ix (Fin w.length)) (h0 : C.LPt) (n : ℕ) (t : ℂ) (hc : r - i = r - D.ptSize (h0 ++ [(n + 1, t)]))
    (hpb : ∀ b ∈ h0, 1 ≤ b.1 ∧ b.2 ≠ 0) (ht : t ≠ 0) (hsz : D.ptSize (h0 ++ [(n + 1, t)]) = i)
    (e1 : r = D.ptSize h0 + (n + 1) + (r - i)) (e2 : D.ptSize h0 + (n + 1) + (r - i) = r)
    (hh : B.Mat k r → (Wq →L[ℂ] Wp)) :
    PBE.xs T χ ε i hi w (h0 ++ [(n + 1, t)]) hc hh a =
      fun γ => U.PhiFun (p := D.ptSize h0 + (n + 1)) (s := 0) k (r - i) (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h0))
        (Formalism.FourierDecayAlt.P.Dx2.SL.dP (D.ptDiag h0) t) (D.castV e1 T.base.z) (D.castV e1 T.base.z')
        (D.castF e2 (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ hh ε) i hi w a)) (fun a => a.elim0) γ := by
  subst hsz
  have hP : D.ptSize (h0 ++ [(n + 1, t)]) = D.ptSize h0 + (n + 1) := Formalism.FourierDecayAlt.P.Dx2.SL.ptSize_append h0 (n + 1) t
  have hloc : D.IsLocPt (h0 ++ [(n + 1, t)]) (D.ptSize (h0 ++ [(n + 1, t)])) := by
    refine ⟨fun b hb => ?_, rfl⟩
    rcases List.mem_append.mp hb with hb | hb
    · exact hpb b hb
    · simp only [List.mem_singleton] at hb
      subst hb
      exact ⟨by omega, ht⟩
  have hlocH := Formalism.FourierDecayAlt.P.Dx2.SL.isLocPt_head hloc
  have hspec := (Formalism.FourierDecayAlt.P.ptPerm_spec _ _ hloc).1
  have hspec' := (Formalism.FourierDecayAlt.P.ptPerm_spec _ _ hlocH).1
  have hσ : ∀ q : Fin (D.ptSize (h0 ++ [(n + 1, t)])),
      ((Formalism.FourierDecayAlt.P.Dx2.SL.sigP (n := n) (D.ptPerm h0)) (Fin.cast hP q)).val = (D.ptPerm (h0 ++ [(n + 1, t)]) q).val := by
    intro q
    rw [hspec q, Formalism.FourierDecayAlt.P.Dx2.SL.partner_append (n + 1) t h0 q.val (by have := q.isLt; omega)]
    by_cases h1 : q.val < D.ptSize h0
    · rw [if_pos h1]
      have e : Fin.cast hP q = Fin.castAdd (n + 1) ⟨q.val, h1⟩ := Fin.ext rfl
      rw [e, Formalism.FourierDecayAlt.P.Dx2.SL.blockPerm_castAdd]
      exact hspec' ⟨q.val, h1⟩
    · rw [if_neg h1]
      have e : Fin.cast hP q = Fin.natAdd (D.ptSize h0) ⟨q.val - D.ptSize h0, by have := q.isLt; omega⟩ :=
        Fin.ext (by simp; omega)
      rw [e, Formalism.FourierDecayAlt.P.Dx2.SL.blockPerm_natAdd]
      simp only [Fin.val_natAdd, Fin.val_rev]
      omega
  have hd : ∀ q : Fin (D.ptSize (h0 ++ [(n + 1, t)])),
      Formalism.FourierDecayAlt.P.Dx2.SL.dP (n := n) (D.ptDiag h0) t (Fin.cast hP q) = D.ptDiag (h0 ++ [(n + 1, t)]) q := by
    intro q
    simp only [D.ptDiag]
    rw [Formalism.FourierDecayAlt.P.Dx2.SL.scal_append (n + 1) t h0 q.val (by have := q.isLt; omega)]
    by_cases h1 : q.val < D.ptSize h0
    · rw [if_pos h1]
      have e : Fin.cast hP q = Fin.castAdd (n + 1) ⟨q.val, h1⟩ := Fin.ext rfl
      rw [e, Formalism.FourierDecayAlt.P.Dx2.SL.dP, Fin.addCases_left]; rfl
    · rw [if_neg h1]
      have e : Fin.cast hP q = Fin.natAdd (D.ptSize h0) ⟨q.val - D.ptSize h0, by have := q.isLt; omega⟩ :=
        Fin.ext (by simp; omega)
      rw [e, Formalism.FourierDecayAlt.P.Dx2.SL.dP, Fin.addCases_right]
  set ρ := r - D.ptSize (h0 ++ [(n + 1, t)]) with hρ
  have hS : ∀ (Gx : B.Mat k r → (Wq →L[ℂ] Wp)) (γ : B.Mat k ρ), D.sliceAt k r T.base.z T.base.z' Gx (h0 ++ [(n + 1, t)]) γ =
      U.PhiFun (p := D.ptSize h0 + (n + 1)) (s := 0) k ρ (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h0))
        (Formalism.FourierDecayAlt.P.Dx2.SL.dP (D.ptDiag h0) t) (D.castV (by omega) T.base.z) (D.castV (by omega) T.base.z')
        (D.castF (by omega) Gx) (fun a => a.elim0) γ := by
    intro Gx γ
    obtain ⟨-, hT2⟩ := Formalism.FourierDecayAlt.P.Dx2.SL.phi_transport (k := k) (ρ := ρ) hP _ _ hσ _ _ hd
      (D.castV (by omega) T.base.z) (D.castV (by omega) T.base.z') (D.castF (by omega) Gx) γ
    unfold D.sliceAt
    rw [dif_pos (by omega), hT2]
    simp only [Formalism.FourierDecayAlt.P.Dx2.SL.castV_castV, Formalism.FourierDecayAlt.P.Dx2.SL.castF_castF]
  unfold PBE.xs
  rw [Formalism.FourierDecayAlt.P.JCTx6.Link2.castF_self]
  funext γ
  exact hS _ γ

theorem ccCoefM_mono {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] {Bs : B.RealPlaceData k r Wp Wq} {A : ℝ} {mm : ℕ} {e e' : ℝ} {F : B.Mat k r → (Wq →L[ℂ] Wp)}
    (h : JC.CCCoefM Bs A mm e F) (he : e' ≤ e) : JC.CCCoefM Bs A mm e' F :=
  ⟨h.1, h.2.1, fun g hg hne => le_trans he (h.2.2 g hg hne)⟩

theorem sliceContQa : ∃ Cs : ℝ, 0 ≤ Cs ∧ ∀ Cc : ℝ, Cs ≤ Cc →
    ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (T : D.LevTower k r Wp Wq) (χ : ℝ → ℝ) (A₀ : ℝ) (N : ℕ) (P0 : M.Par),
    P0.k = k → P0.r = r → 2 ≤ k → C6.IsCut0 χ →
    Cc * ((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (r : ℝ) + k + 1) ^ 2 + (2 * (r : ℝ) + k + 1) ^ 3) ≤ A₀ →
    ∀ ε : ℝ, 0 < ε → ∀ (i : ℕ) (hi : i ≤ r) (w : List C.Letter), w.length ≤ N →
    ∀ (h0 : C.LPt) (m : ℕ) (hc : ∀ t : ℂ, r - i = r - D.ptSize (h0 ++ [(m, t)])),
    (∀ b ∈ h0, 1 ≤ b.1 ∧ b.2 ≠ 0) → 1 ≤ m → D.ptSize h0 + m = i →
    ∀ t0 : ℂ, t0 ≠ 0 → ∀ (a : Wd.Ix (Fin w.length)), ∃ ε' : ℝ, 0 < ε' ∧
      ∀ (h : B.Mat k r → (Wq →L[ℂ] Wp)) (c : ℝ), B.CkOn ⊤ (B.GV k r) h →
        B.CCle A₀ (3 * (11 * (N * (2 * r + k + 1) ^ 2 + (2 * r + k + 1) ^ 3) + 5)) h c →
        ∃ (δ Kb : ℝ) (Dd : ℂ → ℝ), 0 < δ ∧ Tendsto Dd (𝓝 t0) (𝓝 0) ∧ ∀ t : ℂ, dist t t0 < δ → t ≠ 0 ∧
          JC.CCCoefM (T.bs i) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε' (PBE.xs T χ ε i hi w (h0 ++ [(m, t)]) (hc t) h a) ∧
          B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (PBE.xs T χ ε i hi w (h0 ++ [(m, t)]) (hc t) h a) Kb ∧
          JC.CCCoefM (T.bs i) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε'
            (PBE.xs T χ ε i hi w (h0 ++ [(m, t)]) (hc t) h a - PBE.xs T χ ε i hi w (h0 ++ [(m, t0)]) (hc t0) h a) ∧
          B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N)
            (PBE.xs T χ ε i hi w (h0 ++ [(m, t)]) (hc t) h a - PBE.xs T χ ε i hi w (h0 ++ [(m, t0)]) (hc t0) h a) (Dd t) := by
  obtain ⟨Cp, hCp0, hCp⟩ := posCoreCont
  refine ⟨16 * Cp, by positivity, ?_⟩
  intro Cc hCc k r Wp Wq _ _ _ _ _ _ T χ A₀ N P0 hPk hPr hk2 hχ hA₀ ε hε i hi w hw h0 m hc hpb hm hsz t0 ht0 a
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hPt : ∀ t : ℂ, D.ptSize (h0 ++ [(n + 1, t)]) = i := fun t => by
    rw [Formalism.FourierDecayAlt.P.Dx2.SL.ptSize_append]; exact hsz
  have hd0 : ∀ q, D.ptDiag h0 q ≠ 0 := fun q => Formalism.FourierDecayAlt.P.JCTx6.Link2.ptScal_ne h0 hpb q q.2
  have e1 : r = D.ptSize h0 + (n + 1) + (r - i) := by omega
  have e2 : D.ptSize h0 + (n + 1) + (r - i) = r := by omega
  have hj1 : 1 ≤ D.ptSize h0 + (n + 1) := by omega
  obtain ⟨Θ, hΘ, hΘF⟩ := Formalism.FourierDecayAlt.P.JCTx6.Let.lettersDD k (D.ptSize h0 + (n + 1)) (r - i) Wp Wq (D.castV e1 T.base.z)
    (D.castV e1 T.base.z') (by omega) w a hj1
  have hU : ∀ hh : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) hh →
      ∀ g ∈ B.GV k (D.ptSize h0 + (n + 1) + (r - i)), U.DjU k (D.ptSize h0 + (n + 1)) (r - i) g ≠ 0 →
      D.castF e2 (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ hh ε) i hi w a) g =
        B.opApply Θ (D.castF e2 (D.cutF T.base χ hh ε)) g := by
    intro hh hsm g hg hD
    have hFc : B.CkOn ⊤ (B.GV k r) (D.cutF T.base χ hh ε) := Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_cutF T.base hχ hsm ε
    have h1 : D.castF e2 (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ hh ε) i hi w a) =
        D.uwG k (D.ptSize h0 + (n + 1) + (r - i)) (D.castV e1 T.base.z) (D.castV e1 T.base.z')
          (D.castF e2 (D.cutF T.base χ hh ε)) (D.ptSize h0 + (n + 1)) (by omega) w a := by
      rw [Formalism.FourierDecayAlt.P.JCTx6.Link2.castF_uwG e2 _ _ _ _ hi (by omega)]
      exact Formalism.FourierDecayAlt.P.JCTx6.Link2.uwG_level _ _ _ hsz.symm _ _ w a
    rw [h1, hΘF _ (Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_castF e2 hFc) g hg hD]
  have hFrel : ∀ hh : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) hh →
      ∀ g ∈ B.GV k (D.ptSize h0 + (n + 1) + (r - i)), U.DjU k (D.ptSize h0 + (n + 1)) (r - i) g ≠ 0 →
      D.castF e2 (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ hh ε) i hi w a) g =
        B.opApply Θ (fun x => ((χ (Gf k (D.ptSize h0 + (n + 1) + (r - i)) (D.castV e1 T.base.z)
          (D.castV e1 T.base.z') x / ε) : ℝ) : ℂ) • D.castF e2 hh x) g := by
    intro hh hsm g hg hD
    rw [hU hh hsm g hg hD, Formalism.FourierDecayAlt.P.JCTx6.Link2.castF_cutF e2]
  set nd := 2 * r + k + 1 with hnd
  set As := 11 * (N * nd ^ 2 + nd ^ 3) + 5 with hAs
  obtain ⟨b1, b2, b3, b4, b5⟩ := Formalism.FourierDecayAlt.P.JCTx6.Link2.budgetAs r k N w.length (D.ptSize h0 + (n + 1)) hk2 hw (by omega)
  have hmmU : P5.mmUser P0 N = 5 + 3 * (r + 1) * (N + 2) * nd + N * r := by
    simp only [P5.mmUser, P5.nV, hPk, hPr, hnd]
  have hAU : P5.Auser P0 N = 127 * ((r : ℝ) + 1) ^ 3 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3) := by
    simp only [P5.Auser, P5.nV, hPk, hPr, hnd]
    try (push_cast; try ring)
  have hX1 : (1 : ℝ) ≤ (N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3 := by exact_mod_cast b5
  have hAsR : (As : ℝ) = 11 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3) + 5 := by
    rw [hAs]; push_cast; ring
  have hR1 : (1 : ℝ) ≤ (r : ℝ) + 1 := by have : (0 : ℝ) ≤ r := Nat.cast_nonneg r; linarith
  have hsumR : (((D.ptSize h0 + (n + 1) + (r - i) : ℕ) : ℝ)) = (r : ℝ) := by exact_mod_cast e2
  obtain ⟨ε', hε', hQ⟩ := hCp k (D.ptSize h0) n (r - i) Wp Wq (D.castV e1 T.base.z) (D.castV e1 T.base.z')
    (Formalism.FourierDecayAlt.P.Dx1.SN.castV_inWb e1 _ T.base.z_mem) (Formalism.FourierDecayAlt.P.Dx1.SN.castV_inWb e1 _ T.base.z'_mem)
    Θ _ _ hΘ χ A₀ ε hχ hε (D.ptPerm h0) (D.ptDiag h0) t0 hd0 ht0 As (P5.mmUser P0 N) (P5.Auser P0 N + 1)
    b1 b2 (by rw [hmmU]; exact b3) (by rw [e2]; exact b4)
    (by
      rw [hsumR, hAU, hAsR]
      have hR3 : (1 : ℝ) ≤ ((r : ℝ) + 1) ^ 3 := one_le_pow₀ hR1
      have : 0 ≤ ((r : ℝ) + 1) ^ 3 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3) := by positivity
      nlinarith)
    (by
      rw [hsumR, hAsR]
      have hR4 : 0 ≤ ((r : ℝ) + 1) ^ 4 := by positivity
      have hX0 : 0 ≤ (N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3 := by linarith
      have s1 : Cp * ((r : ℝ) + 1) ^ 4 * (11 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3) + 5) ≤
          Cp * ((r : ℝ) + 1) ^ 4 * (16 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
      have s2 : 16 * Cp * (((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3)) ≤
          Cc * (((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3)) :=
        mul_le_mul_of_nonneg_right hCc (by positivity)
      have s3 : Cc * ((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3) ≤ A₀ := by
        have hndR : (nd : ℝ) = 2 * (r : ℝ) + k + 1 := by rw [hnd]; push_cast; ring
        rw [hndR]; exact hA₀
      nlinarith)
  have hz1 : U.lowV k (D.ptSize h0 + (n + 1)) (r - i) (D.castV e1 T.base.z) = (T.bs i).z := by
    have hzl : T.base.z = D.castV (by omega) (liftVec k i (r - i) (T.bs i).z) := (T.z_lev _ hi).symm
    rw [hzl, Formalism.FourierDecayAlt.P.Dx2.SL.castV_castV]
    exact Formalism.FourierDecayAlt.P.JCTx6.Link2.lowV_liftVec hsz _ _
  have hz1' : U.lowV k (D.ptSize h0 + (n + 1)) (r - i) (D.castV e1 T.base.z') = (T.bs i).z' := by
    have hzl' : T.base.z' = D.castV (by omega) (liftVec k i (r - i) (T.bs i).z') := (T.z'_lev _ hi).symm
    rw [hzl', Formalism.FourierDecayAlt.P.Dx2.SL.castV_castV]
    exact Formalism.FourierDecayAlt.P.JCTx6.Link2.lowV_liftVec hsz _ _
  refine ⟨ε', hε', fun hh c hsm hcl => ?_⟩
  obtain ⟨δ, Kb, Dd, hδ, hDd, hnear⟩ := hQ (D.castF e2 hh) c (PBE.ccle_castF e2 hcl) _ (hFrel hh hsm)
  have key : ∀ t : ℂ, t ≠ 0 → PBE.xs T χ ε i hi w (h0 ++ [(n + 1, t)]) (hc t) hh a =
      fun γ => U.PhiFun (p := D.ptSize h0 + (n + 1)) (s := 0) k (r - i) (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h0))
        (Formalism.FourierDecayAlt.P.Dx2.SL.dP (D.ptDiag h0) t) (D.castV e1 T.base.z) (D.castV e1 T.base.z')
        (D.castF e2 (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ hh ε) i hi w a)) (fun a => a.elim0) γ :=
    fun t ht => xs_eq_phi T χ ε i hi w a h0 n t (hc t) hpb ht (hPt t) e1 e2 hh
  obtain ⟨-, -, hsupp0, -⟩ := hnear t0 (by rw [dist_self]; exact hδ)
  refine ⟨δ, Kb, Dd, hδ, hDd, fun t ht => ?_⟩
  obtain ⟨htne, hB, hsupp, hD⟩ := hnear t ht
  have hsub : PBE.xs T χ ε i hi w (h0 ++ [(n + 1, t)]) (hc t) hh a -
      PBE.xs T χ ε i hi w (h0 ++ [(n + 1, t0)]) (hc t0) hh a =
      fun γ => U.PhiFun (p := D.ptSize h0 + (n + 1)) (s := 0) k (r - i) (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h0))
        (Formalism.FourierDecayAlt.P.Dx2.SL.dP (D.ptDiag h0) t) (D.castV e1 T.base.z) (D.castV e1 T.base.z')
        (D.castF e2 (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ hh ε) i hi w a)) (fun a => a.elim0) γ -
        U.PhiFun (p := D.ptSize h0 + (n + 1)) (s := 0) k (r - i) (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h0))
        (Formalism.FourierDecayAlt.P.Dx2.SL.dP (D.ptDiag h0) t0) (D.castV e1 T.base.z) (D.castV e1 T.base.z')
        (D.castF e2 (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ hh ε) i hi w a)) (fun a => a.elim0) γ := by
    rw [key t htne, key t0 ht0]; rfl
  rw [hsub, key t htne]
  refine ⟨htne, ⟨hB.1, ⟨_, hB⟩, fun γ hγ hne => ?_⟩, hB, ⟨hD.1, ⟨_, hD⟩, fun γ hγ hne => ?_⟩, hD⟩
  · have := hsupp γ hγ hne
    rwa [hz1, hz1'] at this
  · by_cases h1 : U.PhiFun (p := D.ptSize h0 + (n + 1)) (s := 0) k (r - i) (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h0))
        (Formalism.FourierDecayAlt.P.Dx2.SL.dP (D.ptDiag h0) t) (D.castV e1 T.base.z) (D.castV e1 T.base.z')
        (D.castF e2 (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ hh ε) i hi w a)) (fun a => a.elim0) γ = 0
    · have hne0 : U.PhiFun (p := D.ptSize h0 + (n + 1)) (s := 0) k (r - i) (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h0))
          (Formalism.FourierDecayAlt.P.Dx2.SL.dP (D.ptDiag h0) t0) (D.castV e1 T.base.z) (D.castV e1 T.base.z')
          (D.castF e2 (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ hh ε) i hi w a)) (fun a => a.elim0) γ ≠ 0 := by
        intro h2; apply hne; simp only [h1, h2, sub_zero]
      have := hsupp0 γ hγ hne0
      rwa [hz1, hz1'] at this
    · have := hsupp γ hγ h1
      rwa [hz1, hz1'] at this

theorem sliceContQ : ∃ Cs : ℝ, 0 ≤ Cs ∧ ∀ Cc : ℝ, Cs ≤ Cc →
    ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (T : D.LevTower k r Wp Wq) (χ : ℝ → ℝ) (A₀ : ℝ) (N : ℕ) (P0 : M.Par),
    P0.k = k → P0.r = r → 2 ≤ k → C6.IsCut0 χ →
    Cc * ((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (r : ℝ) + k + 1) ^ 2 + (2 * (r : ℝ) + k + 1) ^ 3) ≤ A₀ →
    ∀ ε : ℝ, 0 < ε → ∀ (i : ℕ) (hi : i ≤ r) (w : List C.Letter), w.length ≤ N →
    ∀ (h0 : C.LPt) (m : ℕ) (hc : ∀ t : ℂ, r - i = r - D.ptSize (h0 ++ [(m, t)])),
    (∀ b ∈ h0, 1 ≤ b.1 ∧ b.2 ≠ 0) → 1 ≤ m → D.ptSize h0 + m = i →
    ∀ t0 : ℂ, t0 ≠ 0 → ∃ ε' : ℝ, 0 < ε' ∧ ∀ (a : Wd.Ix (Fin w.length))
      (h : B.Mat k r → (Wq →L[ℂ] Wp)) (c : ℝ), B.CkOn ⊤ (B.GV k r) h →
        B.CCle A₀ (3 * (11 * (N * (2 * r + k + 1) ^ 2 + (2 * r + k + 1) ^ 3) + 5)) h c →
        ∃ (δ Kb : ℝ) (Dd : ℂ → ℝ), 0 < δ ∧ Tendsto Dd (𝓝 t0) (𝓝 0) ∧ ∀ t : ℂ, dist t t0 < δ → t ≠ 0 ∧
          JC.CCCoefM (T.bs i) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε' (PBE.xs T χ ε i hi w (h0 ++ [(m, t)]) (hc t) h a) ∧
          B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (PBE.xs T χ ε i hi w (h0 ++ [(m, t)]) (hc t) h a) Kb ∧
          JC.CCCoefM (T.bs i) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε'
            (PBE.xs T χ ε i hi w (h0 ++ [(m, t)]) (hc t) h a - PBE.xs T χ ε i hi w (h0 ++ [(m, t0)]) (hc t0) h a) ∧
          B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N)
            (PBE.xs T χ ε i hi w (h0 ++ [(m, t)]) (hc t) h a - PBE.xs T χ ε i hi w (h0 ++ [(m, t0)]) (hc t0) h a) (Dd t) := by
  obtain ⟨Cs, hCs0, hCs⟩ := sliceContQa
  refine ⟨Cs, hCs0, ?_⟩
  intro Cc hCc k r Wp Wq _ _ _ _ _ _ T χ A₀ N P0 hPk hPr hk2 hχ hA₀ ε hε i hi w hw h0 m hc hpb hm hsz t0 ht0
  have H := fun a : Wd.Ix (Fin w.length) =>
    hCs Cc hCc k r Wp Wq T χ A₀ N P0 hPk hPr hk2 hχ hA₀ ε hε i hi w hw h0 m hc hpb hm hsz t0 ht0 a
  choose ef hef hP using H
  refine ⟨Finset.univ.inf' Finset.univ_nonempty ef,
    (Finset.lt_inf'_iff Finset.univ_nonempty).2 (fun a _ => hef a), fun a hh c hsm hcl => ?_⟩
  have hle : Finset.univ.inf' Finset.univ_nonempty ef ≤ ef a := Finset.inf'_le _ (Finset.mem_univ a)
  obtain ⟨δ, Kb, Dd, hδ, hDd, hn⟩ := hP a hh c hsm hcl
  refine ⟨δ, Kb, Dd, hδ, hDd, fun t ht => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := hn t ht
  exact ⟨h1, ccCoefM_mono h2 hle, h3, ccCoefM_mono h4 hle, h5⟩

end Formalism.FourierDecayAlt.P.LastBlockContinuity
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CccoefMono
section
open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBE

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem cccoef_mono {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] {Bs : B.RealPlaceData k r Wp Wq} {A : ℝ} {mm : ℕ} {ε ε' : ℝ}
    {F : B.Mat k r → (Wq →L[ℂ] Wp)} (h : JC.CCCoefM Bs A mm ε' F) (he : ε ≤ ε') : JC.CCCoefM Bs A mm ε F :=
  ⟨h.1, h.2.1, fun g hg hne => he.trans (h.2.2 g hg hne)⟩

theorem cut_eq {k r : ℕ} (cut : ℕ → B.Mat k r → ℂ)
    (hcut : ∀ n g, cut n g = ((Real.smoothTransition
      ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ)) (n : ℕ) (g : B.Mat k r) :
    cut n g = 1 - JCx2.pdPsi ((n : ℝ) + 1) g := by
  rw [hcut]
  simp [JCx2.pdPsi, JCx2.pdPhi, JCx2.pdChi, JCx2.pdSq]

theorem belowTop : ∃ Cl : ℝ, 0 ≤ Cl ∧ ∀ Cc : ℝ, Cl ≤ Cc →
    ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (ε A : ℝ) (N : ℕ) (cut : ℕ → B.Mat P.k P.r → ℂ),
    C6.IsCut0 χ → 0 < ε → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A m f) →
    Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A →
    (∀ n g, cut n g = ((Real.smoothTransition
      ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ)) →
    ∀ i, i ≤ P.r → ∀ w : List C.Letter, w.length ≤ N → ∀ a b,
      Tendsto (fun n => p.RR (fun g => cut n g • D.cutF p.T.base χ f ε g) i w a b) atTop
        (𝓝 (p.RR (D.cutF p.T.base χ f ε) i w a b)) := by
  obtain ⟨Cs, hCs0, hSQ⟩ := sliceQ
  refine ⟨Cs + 1, by positivity, ?_⟩
  intro Cc hCc Wp Wq _ _ _ _ _ _ P p f χ ε A N cut hχ hε hf hfA hA hcut i hi w hw a b
  have hk2 : 2 ≤ P.k := p.hl.2.2
  set X : ℝ := (N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3 with hX
  have hX1 : 1 ≤ X := by
    have h1 : (1 : ℝ) ≤ 2 * (P.r : ℝ) + P.k + 1 := by
      have : (0 : ℝ) ≤ P.r := Nat.cast_nonneg _
      have : (0 : ℝ) ≤ P.k := Nat.cast_nonneg _
      linarith
    have : 1 ≤ (2 * (P.r : ℝ) + P.k + 1) ^ 3 := one_le_pow₀ h1
    have : 0 ≤ (N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 := by positivity
    linarith
  have hR4 : 1 ≤ ((P.r : ℝ) + 1) ^ 4 := one_le_pow₀ (by have : (0 : ℝ) ≤ P.r := Nat.cast_nonneg _; linarith)
  have hA' : Cs * ((P.r : ℝ) + 1) ^ 4 * X ≤ A - 1 := by
    have h1 : (Cs + 1) * ((P.r : ℝ) + 1) ^ 4 * X ≤ A :=
      le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCc (by positivity)) (by positivity)) hA
    have h2 : 1 ≤ ((P.r : ℝ) + 1) ^ 4 * X := by nlinarith
    nlinarith
  set M := 3 * (11 * (N * (2 * P.r + P.k + 1) ^ 2 + (2 * P.r + P.k + 1) ^ 3) + 5) with hM
  obtain ⟨bf, hbf⟩ := hfA M
  have hbf0 : 0 ≤ bf := JCx2.pd_ccle_nonneg hbf
  have hbf' : B.CCle (A - 1) M f bf := BetaSesquilinearity.CCle_mono_A (by linarith) hbf
  obtain ⟨Kp, hKp0, hKp⟩ := JCx2.pd_cut_ccle (k := P.k) (r := P.r) (E := Wq →L[ℂ] Wp) M
  have hψ : ∀ n : ℕ, B.CCle (A - 1) M (fun g => JCx2.pdPsi ((n : ℝ) + 1) g • f g) (Kp * bf / ((n : ℝ) + 1)) :=
    fun n => hKp _ (by positivity) A f bf hbf
  have hψs : ∀ n : ℕ, B.CkOn ⊤ (B.GV P.k P.r) (fun g => JCx2.pdPsi ((n : ℝ) + 1) g • f g) :=
    fun n => JCx2.pd_smooth_smul (JCx2.pd_psi_cd _) hf
  set hn : ℕ → B.Mat P.k P.r → (Wq →L[ℂ] Wp) := fun n g => cut n g • f g with hhn
  have hneq : ∀ n, hn n = fun g => f g + (-1 : ℂ) • (JCx2.pdPsi ((n : ℝ) + 1) g • f g) := by
    intro n; funext g
    simp only [hhn, cut_eq cut hcut n g, sub_smul, one_smul]
    simp [sub_eq_add_neg]
  have hnC : ∀ n, B.CCle (A - 1) M (hn n) (bf + Kp * bf) := by
    intro n
    rw [hneq n]
    refine JCx2.pd_ccle_mono_c (BetaSesquilinearity.CCle_add hbf' (BetaSesquilinearity.CCle_smul (-1) (hψ n))) ?_
    have h1 : Kp * bf / ((n : ℝ) + 1) ≤ Kp * bf := div_le_self (by positivity) (by
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
    simp only [norm_neg, norm_one, one_mul]
    linarith
  have hns : ∀ n, B.CkOn ⊤ (B.GV P.k P.r) (hn n) := by
    intro n
    rw [hneq n]
    exact BetaSesquilinearity.CkOn_add hf (BetaSesquilinearity.CkOn_smul (-1) (hψs n))
  have hsub : ∀ n, (fun g => f g - hn n g) = fun g => JCx2.pdPsi ((n : ℝ) + 1) g • f g := by
    intro n; funext g
    rw [hneq n]; simp
  have hFn : ∀ n, (fun g => cut n g • D.cutF p.T.base χ f ε g) = D.cutF p.T.base χ (hn n) ε := by
    intro n; funext g
    simp only [D.cutF, hhn]
    rw [smul_comm]
  simp only [KB.Pl.RR, hFn]
  unfold D.RRplace
  by_cases hab : D.IsLocPt a i ∧ D.IsLocPt b i
  swap
  · simp only [dif_neg hab]; exact tendsto_const_nhds
  simp only [dif_pos hab, dif_pos hi]
  have hca : P.r - i = P.r - D.ptSize a := by simp [hab.1.2]
  have hcb : P.r - i = P.r - D.ptSize b := by simp [hab.2.2]
  have hQa := fun e => hSQ Cs le_rfl P.k P.r Wp Wq p.T χ (A - 1) N P rfl rfl hk2 hχ hA' ε hε i hi w hw a hca hab.1 e
  have hQb := fun e => hSQ Cs le_rfl P.k P.r Wp Wq p.T χ (A - 1) N P rfl rfl hk2 hχ hA' ε hε i hi w hw b hcb hab.2 e
  choose εa Ka hεa hKa hQ1a hQ2a using hQa
  choose εb Kb hεb hKb hQ1b hQ2b using hQb
  set S : ℝ := ∑ e, (εa e)⁻¹ + ∑ e, (εb e)⁻¹ with hS
  have hSa : ∀ e, (εa e)⁻¹ ≤ S := by
    intro e
    have h1 : (εa e)⁻¹ ≤ ∑ e, (εa e)⁻¹ :=
      Finset.single_le_sum (f := fun e => (εa e)⁻¹) (fun e _ => (inv_pos.2 (hεa e)).le) (Finset.mem_univ e)
    have h2 : 0 ≤ ∑ e, (εb e)⁻¹ := Finset.sum_nonneg fun e _ => (inv_pos.2 (hεb e)).le
    linarith
  have hSb : ∀ e, (εb e)⁻¹ ≤ S := by
    intro e
    have h1 : (εb e)⁻¹ ≤ ∑ e, (εb e)⁻¹ :=
      Finset.single_le_sum (f := fun e => (εb e)⁻¹) (fun e _ => (inv_pos.2 (hεb e)).le) (Finset.mem_univ e)
    have h2 : 0 ≤ ∑ e, (εa e)⁻¹ := Finset.sum_nonneg fun e _ => (inv_pos.2 (hεa e)).le
    linarith
  have hS0 : 0 < S := lt_of_lt_of_le (inv_pos.2 (hεa Wd.e1)) (hSa Wd.e1)
  have hε₀a : ∀ e, S⁻¹ ≤ εa e := fun e => by
    have := inv_anti₀ (inv_pos.2 (hεa e)) (hSa e); rwa [inv_inv] at this
  have hε₀b : ∀ e, S⁻¹ ≤ εb e := fun e => by
    have := inv_anti₀ (inv_pos.2 (hεb e)) (hSb e); rwa [inv_inv] at this
  set KK : ℝ := ∑ e, Ka e + ∑ e, Kb e with hKK
  have hKa' : ∀ e, Ka e ≤ KK := by
    intro e
    have h1 : Ka e ≤ ∑ e, Ka e := Finset.single_le_sum (f := Ka) (fun e _ => hKa e) (Finset.mem_univ e)
    have h2 : 0 ≤ ∑ e, Kb e := Finset.sum_nonneg fun e _ => hKb e
    linarith
  have hKb' : ∀ e, Kb e ≤ KK := by
    intro e
    have h1 : Kb e ≤ ∑ e, Kb e := Finset.single_le_sum (f := Kb) (fun e _ => hKb e) (Finset.mem_univ e)
    have h2 : 0 ≤ ∑ e, Ka e := Finset.sum_nonneg fun e _ => hKa e
    linarith
  have hKK0 : 0 ≤ KK := le_trans (hKa Wd.e1) (hKa' Wd.e1)
  have hB1 : bf ≤ bf + Kp * bf := by nlinarith

  have main : ∀ (q : C.LPt) (hcq : P.r - i = P.r - D.ptSize q) (εq Kq : Wd.Ix (Fin w.length) → ℝ),
      (∀ e, S⁻¹ ≤ εq e) → (∀ e, 0 ≤ Kq e) → (∀ e, Kq e ≤ KK) →
      (∀ e (h : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (c : ℝ), B.CkOn ⊤ (B.GV P.k P.r) h → B.CCle (A - 1) M h c →
        JC.CCCoefM (p.T.bs i) (P5.Auser P N + 1) (P5.mmUser P N) (εq e) (xs p.T χ ε i hi w q hcq h e) ∧
        B.CCle (P5.Auser P N + 1) (P5.mmUser P N) (xs p.T χ ε i hi w q hcq h e) (Kq e * c)) →
      (∀ e (h₁ h₂ : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (c₁ c₂ : ℝ), B.CkOn ⊤ (B.GV P.k P.r) h₁ →
        B.CkOn ⊤ (B.GV P.k P.r) h₂ → B.CCle (A - 1) M h₁ c₁ → B.CCle (A - 1) M h₂ c₂ →
        ∀ γ ∈ B.GV P.k (P.r - i), xs p.T χ ε i hi w q hcq h₁ e γ - xs p.T χ ε i hi w q hcq h₂ e γ =
          xs p.T χ ε i hi w q hcq (fun g => h₁ g - h₂ g) e γ) →
      (∀ e, JC.CCCoefM (p.T.bs i) (P5.Auser P N + 1) (P5.mmUser P N) S⁻¹ (xs p.T χ ε i hi w q hcq f e) ∧
        B.CCle (P5.Auser P N + 1) (P5.mmUser P N) (xs p.T χ ε i hi w q hcq f e) (KK * (bf + Kp * bf))) ∧
      (∀ n e, JC.CCCoefM (p.T.bs i) (P5.Auser P N + 1) (P5.mmUser P N) S⁻¹ (xs p.T χ ε i hi w q hcq (hn n) e) ∧
        B.CCle (P5.Auser P N + 1) (P5.mmUser P N) (xs p.T χ ε i hi w q hcq (hn n) e) (KK * (bf + Kp * bf))) ∧
      (∀ n e, JC.CCCoefM (p.T.bs i) (P5.Auser P N + 1) (P5.mmUser P N) S⁻¹
          (xs p.T χ ε i hi w q hcq (hn n) e - xs p.T χ ε i hi w q hcq f e) ∧
        B.CCle (P5.Auser P N + 1) (P5.mmUser P N)
          (xs p.T χ ε i hi w q hcq (hn n) e - xs p.T χ ε i hi w q hcq f e) (KK * (Kp * bf / ((n : ℝ) + 1)))) := by
    intro q hcq εq Kq hεq hKq hKq' hQ1 hQ2
    refine ⟨fun e => ?_, fun n e => ?_, fun n e => ?_⟩
    · obtain ⟨h1, h2⟩ := hQ1 e f bf hf hbf'
      exact ⟨cccoef_mono h1 (hεq e), JCx2.pd_ccle_mono_c h2 (mul_le_mul (hKq' e) hB1 hbf0 hKK0)⟩
    · obtain ⟨h1, h2⟩ := hQ1 e (hn n) _ (hns n) (hnC n)
      exact ⟨cccoef_mono h1 (hεq e), JCx2.pd_ccle_mono_c h2 (mul_le_mul_of_nonneg_right (hKq' e) (by positivity))⟩
    · obtain ⟨h1, h2⟩ := hQ1 e _ _ (hψs n) (hψ n)
      have hd : ∀ γ ∈ B.GV P.k (P.r - i), (fun γ => (-1 : ℂ) • xs p.T χ ε i hi w q hcq
          (fun g => JCx2.pdPsi ((n : ℝ) + 1) g • f g) e γ) γ =
          (xs p.T χ ε i hi w q hcq (hn n) e - xs p.T χ ε i hi w q hcq f e) γ := by
        intro γ hγ
        have := hQ2 e f (hn n) bf _ hf (hns n) hbf' (hnC n) γ hγ
        rw [hsub n] at this
        simp only [Pi.sub_apply, ← this]
        simp
      have hC2 := Formalism.FourierDecayAlt.P.Ux1.cc_congr hd (BetaSesquilinearity.CCle_smul (-1) h2)
      simp only [norm_neg, norm_one, one_mul] at hC2
      have hC3 := JCx2.pd_ccle_mono_c hC2 (mul_le_mul_of_nonneg_right (hKq' e) (by positivity))
      refine ⟨⟨hC3.1, ⟨_, hC3⟩, fun γ hγ hne => ?_⟩, hC3⟩
      rw [← hd γ hγ] at hne
      have hne' : xs p.T χ ε i hi w q hcq (fun g => JCx2.pdPsi ((n : ℝ) + 1) g • f g) e γ ≠ 0 := by
        intro h0; apply hne; simp [h0]
      exact (hεq e).trans (h1.2.2 γ hγ hne')
  obtain ⟨ma1, ma2, ma3⟩ := main a hca εa Ka hε₀a hKa hKa' hQ1a hQ2a
  obtain ⟨mb1, mb2, mb3⟩ := main b hcb εb Kb hε₀b hKb hKb' hQ1b hQ2b
  have hdn : Tendsto (fun n : ℕ => KK * (Kp * bf / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat.congr
      (fun n => by simp)
    have := (h1.const_mul (Kp * bf)).const_mul KK
    simpa [div_eq_mul_inv, mul_assoc] using this
  exact formLev_limit P p.T _ ⟨i, by omega⟩ w N hw S⁻¹ (inv_pos.2 hS0)
    (xs p.T χ ε i hi w a hca f) (xs p.T χ ε i hi w b hcb f)
    (fun n => xs p.T χ ε i hi w a hca (hn n)) (fun n => xs p.T χ ε i hi w b hcb (hn n))
    (KK * (bf + Kp * bf)) (fun n => KK * (Kp * bf / ((n : ℝ) + 1))) hdn ma1 mb1 ma2 mb2 ma3 mb3

theorem cutCpt {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (ε : ℝ) (cut : ℕ → B.Mat P.k P.r → ℂ)
    (hχ : C6.IsCut0 χ) (hε : 0 < ε) (hf : B.CkOn ⊤ (B.GV P.k P.r) f)
    (hcut : ∀ n g, cut n g = ((Real.smoothTransition
      ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ)) (n : ℕ) :
    KB.CptCoef Bs fun g => cut n g • D.cutF Bs χ f ε g := by
  have hcs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cut n) := by
    have e : cut n = fun g => 1 - JCx2.pdPsi ((n : ℝ) + 1) g := funext fun g => cut_eq cut hcut n g
    rw [e]
    exact contDiff_const.sub (JCx2.pd_psi_cd _)
  refine ⟨JCx2.pd_smooth_smul hcs (Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_cutF Bs hχ hf ε), ⟨2 * ((n : ℝ) + 1), ?_⟩, ?_⟩
  · intro g _ hne
    have hc : cut n g ≠ 0 := by intro h0; apply hne; simp [h0]
    rw [hcut] at hc
    have hpos : 0 < (4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3 := by
      by_contra hle
      push_neg at hle
      apply hc
      rw [Real.smoothTransition.zero_of_nonpos hle]
      simp
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hsum : ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j) =
        ((n : ℝ) + 1)⁻¹ ^ 2 * ∑ i, ∑ j, Complex.normSq (g i j) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.smul_apply, Complex.real_smul, Complex.normSq_mul, Complex.normSq_ofReal]
      ring
    have hlt : ∑ i, ∑ j, Complex.normSq (g i j) < 4 * ((n : ℝ) + 1) ^ 2 := by
      rw [hsum] at hpos
      have h1 : ((n : ℝ) + 1)⁻¹ ^ 2 * ∑ i, ∑ j, Complex.normSq (g i j) < 4 := by linarith
      have h2 : ((n : ℝ) + 1) ^ 2 * (((n : ℝ) + 1)⁻¹ ^ 2 * ∑ i, ∑ j, Complex.normSq (g i j)) =
          ∑ i, ∑ j, Complex.normSq (g i j) := by
        field_simp
      have h3 : ((n : ℝ) + 1) ^ 2 * (((n : ℝ) + 1)⁻¹ ^ 2 * ∑ i, ∑ j, Complex.normSq (g i j)) < ((n : ℝ) + 1) ^ 2 * 4 :=
        mul_lt_mul_of_pos_left h1 (by positivity)
      rw [h2] at h3
      linarith
    unfold B.gN
    rw [show (2 * ((n : ℝ) + 1)) = Real.sqrt ((2 * ((n : ℝ) + 1)) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith)
  · obtain ⟨δ, hδ, hδ0⟩ := hχ.2.1
    refine ⟨δ * ε, by positivity, fun g _ hne => ?_⟩
    have hc : χ (Gf P.k P.r Bs.z Bs.z' g / ε) ≠ 0 := by
      intro h0; apply hne; simp [D.cutF, h0]
    have h1 : δ ≤ Gf P.k P.r Bs.z Bs.z' g / ε := by
      by_contra hlt; push_neg at hlt; exact hc (hδ0 _ hlt)
    rw [le_div_iff₀ hε] at h1
    linarith

end Formalism.FourierDecayAlt.P.PBE
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEllRegW
section
namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

theorem elliptic_regularity_weighted : EllRegW := elliptic_regularity_transfer_holds ZetaZeros.D.EllReg.elliptic_regularity_of_parts

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

