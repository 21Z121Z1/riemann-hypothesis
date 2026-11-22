import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0265
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0283
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0281
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0160
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0278
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelOneSquareIntegrableGeneral

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXSliceTop
section
open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutEXSlice

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.LeftFubiniLemmas

section gen

variable {k p ρ n : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem slice_integral_level_reduction (e : p + ρ = n) (hp : 1 ≤ p) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (hd : ∀ i, d i ≠ 0)
    (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k n Wp Wq)
    (hz : D.castV e (liftVec k p ρ Bj.z) = B0.z) (hz' : D.castV e (liftVec k p ρ Bj.z') = B0.z')
    (hπ' : ∀ y : B.Mat k ρ, Bj.π' y = B0.π' (D.castM e (ιLev k p ρ y)))
    (hW' : Bj.μW' Set.univ = 1) (hW0' : B0.μW' = Bj.μW'.map (Formalism.FourierDecayAlt.P.PBM.levMt p ρ e))
    (hNj : Bj.μN = D.muN k ρ) (hN0 : B0.μN = D.muN k n)
    (g : B.Mat k ρ) (hg : g ∈ JF.Om k ρ Bj.z Bj.z') (H : B.Mat k n → (Wq →L[ℂ] Wp))
    (hHc : ContinuousOn H {x | x ∈ B.GV k n ∧ Dmin k n B0.z B0.z' x ⟨p, by omega⟩ ≠ 0}) (R : ℝ)
    (hR : ∀ x ∈ B.GV k n, H x ≠ 0 → B.gN x ≤ R) :
    Integrable (fun v : U.LW σ → ℂ =>
        SliceIntegralLemmas.psiH σ v • PBQ.pbF Bj B0 e H (D.castM e (U.mMap k p ρ (lhOf σ v * U.hMat σ d) g))) volume ∧
    B.JF Bj (U.PhiFun (s := 0) k ρ σ d (D.castV e.symm B0.z) (D.castV e.symm B0.z') (D.castF e H)
        (fun a => a.elim0)) g =
      ∫ v : U.LW σ → ℂ, SliceIntegralLemmas.psiH σ v • PBQ.pbF Bj B0 e H (D.castM e (U.mMap k p ρ (lhOf σ v * U.hMat σ d) g)) := by
  subst e
  have hz1 : B0.z = liftVec k p ρ Bj.z := by rw [← hz, JCTx5.castV_rfl]
  have hz1' : B0.z' = liftVec k p ρ Bj.z' := by rw [← hz', JCTx5.castV_rfl]
  have hπ1 : ∀ y, Bj.π' y = B0.π' (U.embG k p ρ y) := fun y => by
    rw [hπ' y, Dx2.MN.castM_rfl, Dx2.Tower.lev_eq_embG]
  have hHc' : ContinuousOn H {x | x ∈ B.GV k (p + ρ) ∧ U.DjU k p ρ x ≠ 0} := by
    refine hHc.mono ?_
    intro x hx
    refine ⟨hx.1, ?_⟩
    rw [Ux3.zhDmin]
    exact hx.2
  obtain ⟨hi, heq⟩ := SliceIntegralLemmas.jfSliceInt hp σ d hd Bj B0 hz1' hπ1 hW' hW0' hNj hN0 g hg H hHc' R hR
  refine ⟨?_, ?_⟩
  · simpa only [Dx2.MN.castM_rfl] using hi
  · rw [JCTx5.castV_rfl, JCTx5.castV_rfl, hz1, hz1']
    simp only [Dx2.MN.castM_rfl]
    exact heq

end gen

section top

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem slice_gen (P : M.Par) (p : KB.Pl P Wp Wq) (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (hG : B.CkOn ⊤ (B.GV P.k P.r) G) (R : ℝ) (hR : ∀ x ∈ B.GV P.k P.r, G x ≠ 0 → B.gN x ≤ R)
    (h : C.LPt) (j : ℕ) (hjr : j ≤ P.r) (hh : D.IsLocPt h j) (hj1 : 1 ≤ j) (γ : B.Mat P.k (P.r - j))
    (hOm : γ ∈ JF.Om P.k (P.r - j) (p.T.bs j).z (p.T.bs j).z') :
    Integrable (fun v : PBQ.XH h => PBQ.ellH h v (PBQ.pbF (p.T.bs j) p.T.base (by omega : j + (P.r - j) = P.r) G
        (D.castM (by omega : j + (P.r - j) = P.r) (U.mMap P.k j (P.r - j) (PBQ.zxH h j hh.2 v) γ)))) ∧
    B.JF (p.T.bs j) (D.castF (by rw [hh.2]) (D.sliceAt P.k P.r p.T.base.z p.T.base.z' G h)) γ =
      ∫ v, PBQ.ellH h v (PBQ.pbF (p.T.bs j) p.T.base (by omega : j + (P.r - j) = P.r) G
        (D.castM (by omega : j + (P.r - j) = P.r) (U.mMap P.k j (P.r - j) (PBQ.zxH h j hh.2 v) γ))) := by
  obtain ⟨hh1, rfl⟩ := hh
  have e : D.ptSize h + (P.r - D.ptSize h) = P.r := by omega
  have hzj := p.T.z_lev (D.ptSize h) hjr
  have hzj' := p.T.z'_lev (D.ptSize h) hjr
  have hπj : ∀ y, (p.T.bs (D.ptSize h)).π' y = p.T.base.π' (D.castM e (ιLev P.k _ _ y)) :=
    fun y => p.T.π'_lev _ hjr y
  obtain ⟨hWj, hW'j, hNj⟩ := p.hT (D.ptSize h) hjr
  obtain ⟨hW0, hW'0, hN0⟩ := p.hT 0 (Nat.zero_le _)
  have hW0' : p.T.base.μW' = (p.T.bs (D.ptSize h)).μW'.map (PBM.levMt (D.ptSize h) (P.r - D.ptSize h) e) :=
    PBM.haar_lev _ _ e _ _ hzj' _ _ p.T.base.haarW' (p.T.bs _).haarW' hW'0 hW'j
  have hGc : ContinuousOn G {x | x ∈ B.GV P.k P.r ∧
      Dmin P.k P.r p.T.base.z p.T.base.z' x ⟨D.ptSize h, by omega⟩ ≠ 0} :=
    (PBE.ckOn_continuousOn' subset_rfl hG).mono fun x hx => hx.1
  obtain ⟨H1i, H1e⟩ := slice_integral_level_reduction e hj1 (D.ptPerm h) (D.ptDiag h) (CutHB.ptDiag_ne ⟨hh1, rfl⟩)
    (p.T.bs (D.ptSize h)) p.T.base hzj hzj' hπj hW'j hW0' hNj hN0 γ hOm G hGc R hR
  have hcf : ∀ (e' : P.r - D.ptSize h = P.r - D.ptSize h) (F : B.Mat P.k (P.r - D.ptSize h) → (Wq →L[ℂ] Wp)),
      D.castF e' F = F := fun e' F => by
    funext x
    simp only [D.castF, Dx2.MN.castM_rfl]
  refine ⟨?_, ?_⟩
  · simp only [PBQ.ellH, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply]
    simp only [SliceIntegralLemmas.psiH] at H1i
    exact H1i
  · rw [hcf, D.sliceAt, dif_pos hjr]
    simp only [PBQ.ellH, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply]
    exact H1e

theorem om_zero {k ρ : ℕ} (hρ : ρ = 0) (z z' : Fin (2 * ρ + k + 1) → ℂ) (γ : B.Mat k ρ) (hγ : γ ∈ B.GV k ρ)
    (hG : 0 < Q.GGl k ρ z z' γ) : γ ∈ JF.Om k ρ z z' := by
  subst hρ
  have h0 : ∀ (hl : 0 < 0 + 2), Dmin k 0 z z' γ ⟨0, hl⟩ = 1 := by
    intro hl
    simp [Dmin]
  have h1 : Dmin k 0 z z' γ (Fin.last (0 + 1)) = Q.zetaL k 0 z z' (Fin.last 0) γ := by
    rw [PBI.zetaL_eq_zhat]
    simp [Dmin, Matrix.det_unique]
  refine ⟨hγ, ?_, ?_⟩
  · intro l hl
    have hl0 : l = ⟨0, by omega⟩ := Fin.ext (by simpa using hl)
    rw [hl0, h0]
    exact one_ne_zero
  · unfold Gf
    rw [h1, h0]
    simpa [Q.GGl] using hG

end top

end Formalism.FourierDecayAlt.P.CutEXSlice

namespace Formalism.FourierDecayAlt.P.CutEXSlice

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

theorem sliceTop_pos (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (hr : 1 ≤ P.r) (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (hG : CutEX.TopCls p.T.base G)
    (h : C.LPt) (hh : D.IsLocPt h P.r) (γ : B.Mat P.k (P.r - P.r)) (hγ : γ ∈ B.GV P.k (P.r - P.r))
    (hGG : 0 < Q.GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' γ) :
    Integrable (fun v : PBQ.XH h => PBQ.ellH h v (CutEX.pbTop p G (PBQ.zxH h P.r hh.2 v) γ)) ∧
      B.JF (p.T.bs P.r) (D.castF (by rw [hh.2]) (D.sliceAt P.k P.r p.T.base.z p.T.base.z' G h)) γ =
        ∫ v, PBQ.ellH h v (CutEX.pbTop p G (PBQ.zxH h P.r hh.2 v) γ) := by
  have hOm : γ ∈ JF.Om P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' :=
    om_zero (Nat.sub_self _) _ _ γ hγ hGG
  obtain ⟨R, hR⟩ := hG.1.2.1
  exact slice_gen P p G hG.1.1 R hR h P.r le_rfl hh hr γ hOm

end Formalism.FourierDecayAlt.P.CutEXSlice

namespace Formalism.FourierDecayAlt.P

theorem slice_top_exhaustion : CutEX.SliceTop := by
  intro Wp Wq _ _ _ _ _ _ P p G hG h hh γ hγ hGG
  rcases Nat.eq_zero_or_pos P.r with h0 | h1
  · exact CutEXSl0.sliceTop_zero Wp Wq P p h0 G hG h hh γ hγ hGG
  · exact CutEXSlice.sliceTop_pos Wp Wq P p h1 G hG h hh γ hγ hGG

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSEJSMeas
section
open MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB Formalism.FourierDecayAlt.P5.HerC
  Formalism.FourierDecayAlt.P5.HerD

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section MeasJ

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

def glueMapS (l : Fin r) (c : Fin r → ℂ) (q : (ℂ × Cf r l.succ) × Mt k r) : (Fin r → ℂ) × Mx k r :=
  (glue l.succ (Function.update c l q.1.1) q.1.2, Matrix.of q.2)

theorem glueMapS_continuous (l : Fin r) (c : Fin r → ℂ) : Continuous (glueMapS (k := k) l c) := by
  unfold glueMapS
  refine Continuous.prodMk ?_ ?_
  · refine continuous_pi fun m => ?_
    by_cases h : (l.succ : Fin (r + 1)).val ≤ m.val
    · simp only [glue, h, dif_pos]
      exact (continuous_apply _).comp (continuous_snd.comp continuous_fst)
    · simp only [glue, h, dif_neg, not_false_eq_true, Function.update_apply]
      by_cases hm : m = l
      · simp only [hm, eq_self_iff_true, if_true, ite_true] <;> fun_prop
      · simp only [hm, if_false, ite_false] <;> fun_prop
  · exact continuous_matrix fun i j => by simp only [Matrix.of_apply]; fun_prop

theorem measurableSet_glueMapS_DomR (l : Fin r) (c : Fin r → ℂ) :
    MeasurableSet (glueMapS (k := k) l c ⁻¹' DomR k r z z') := by
  rw [DomR_eq, Set.preimage_inter]
  exact ((Formalism.FourierDecayAlt.P.Qx5.isOpen_OpR k r z z').preimage (glueMapS_continuous l c)).measurableSet.inter
    (((Formalism.FourierDecayAlt.P.Qx5.Glev_closed (Fin.last r)).preimage continuous_snd).preimage
      (glueMapS_continuous l c)).measurableSet

end MeasJ

theorem spectral_measurability : JSMeas := by
  intro k r z z' Wp Wq _ _ _ _ _ _ π π' l c Φ Ψ
  have hmaps : Set.MapsTo (glueMapS (k := k) l c) (glueMapS (k := k) l c ⁻¹' DomR k r z z') (DomR k r z z') :=
    fun q hq => hq
  have hΦc := (radSp_continuousOn Φ).comp (glueMapS_continuous l c).continuousOn hmaps
  have hΨc := (radSp_continuousOn Ψ).comp (glueMapS_continuous l c).continuousOn hmaps
  refine measurable_of_continuousOn_zero (measurableSet_glueMapS_DomR l c)
    ((Formalism.FourierDecayAlt.P.B6.hsInner_continuous (Wp := Wp) (Wq := Wq)).comp_continuousOn (hΦc.prodMk hΨc)) ?_
  intro q hq
  have h0 : (Φ : Fn k r (Wq →L[ℂ] Wp)) (glue l.succ (Function.update c l q.1.1) q.1.2) (Matrix.of q.2) = 0 :=
    radSp_zero_off Φ hq
  show B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) (glue l.succ (Function.update c l q.1.1) q.1.2) (Matrix.of q.2)) _ = 0
  rw [h0, Formalism.FourierDecayAlt.P.B6.hilbert_schmidt_inner_basis_sum]
  simp

end Formalism.FourierDecayAlt.P.CutSE
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSEJSRadLocCut
section
open MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5

def FamCCUnif : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (T : D.LevTower P.k P.r Wp Wq) (j : ℕ) (G : ℂ → B.Mat P.k (P.r - (j + 1)) → (Wq →L[ℂ] Wp)),
    CutSH.GoodFam T j G → ∀ K : Set ℂ, IsCompact K → (∀ t ∈ K, t ≠ 0) → ∀ (A : ℝ) (m : ℕ),
      ∃ c : ℝ, ∀ t ∈ K, B.CCle A m (G t) c

end Formalism.FourierDecayAlt.P.CutSE
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDAsm
section
open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

theorem rd_iter_pow (hI : RDIdent) : RDHyp fun k r Wp Wq _ _ _ _ _ _ D =>
    ∀ (M : ℕ) (F F' : B.Mat k r → (Wq →L[ℂ] Wp)), NiceAll D F → NiceAll D F' →
      ∃ K : ℝ, ∀ s : ℂ, ‖s‖ ^ M * ‖B.beta D (wvG D.z D.z' s F) F'‖ ≤ K := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' hr M
  obtain ⟨Θ, hΘ, hid⟩ := hI Wp Wq P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' hr
  induction M with
  | zero =>
    intro F F' hF hF'
    obtain ⟨_, _, -, hFc, -⟩ := hF
    obtain ⟨_, _, -, hFc', -⟩ := hF'
    obtain ⟨K, hK⟩ := radial_boundedness P.k P.r Wp Wq D F F' hFc hFc'
    exact ⟨K, fun s => by simpa using hK s⟩
  | succ M ih =>
    intro F F' hF hF'
    obtain ⟨K1, hK1⟩ := ih (Θ 1 F) (Θ 0 F') (hΘ 1 F hF) (hΘ 0 F' hF')
    obtain ⟨K2, hK2⟩ := ih (Θ 3 F) (Θ 2 F') (hΘ 3 F hF) (hΘ 2 F' hF')
    refine ⟨K1 + K2, fun s => ?_⟩
    have e := hid s F F' hF hF'
    calc ‖s‖ ^ (M + 1) * ‖B.beta D (wvG D.z D.z' s F) F'‖
        = ‖s‖ ^ M * ‖s * B.beta D (wvG D.z D.z' s F) F'‖ := by rw [norm_mul, pow_succ]; ring
      _ = ‖s‖ ^ M * ‖B.beta D (wvG D.z D.z' s (Θ 1 F)) (Θ 0 F') -
            B.beta D (wvG D.z D.z' s (Θ 3 F)) (Θ 2 F')‖ := by rw [e]
      _ ≤ ‖s‖ ^ M * (‖B.beta D (wvG D.z D.z' s (Θ 1 F)) (Θ 0 F')‖ +
            ‖B.beta D (wvG D.z D.z' s (Θ 3 F)) (Θ 2 F')‖) :=
        mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)
      _ ≤ K1 + K2 := by rw [mul_add]; exact add_le_add (hK1 s) (hK2 s)

theorem rd_pow_le (x : ℝ) (hx : 0 ≤ x) (N : ℕ) : (1 + x) ^ N ≤ 2 ^ N * (1 + x ^ N) := by
  rcases le_total x 1 with h | h
  · calc (1 + x) ^ N ≤ 2 ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
      _ ≤ 2 ^ N * (1 + x ^ N) := le_mul_of_one_le_right (by positivity) (by linarith [pow_nonneg hx N])
  · calc (1 + x) ^ N ≤ (2 * x) ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
      _ = 2 ^ N * x ^ N := mul_pow _ _ _
      _ ≤ 2 ^ N * (1 + x ^ N) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

theorem rd_decay (hI : RDIdent) : RDHyp fun k r Wp Wq _ _ _ _ _ _ D =>
    ∀ (F F' : B.Mat k r → (Wq →L[ℂ] Wp)), NiceAll D F → NiceAll D F' → ∀ n : ℕ,
      ∃ C : ℝ, ∀ s : ℂ, ‖B.beta D (wvG D.z D.z' s F) F'‖ ≤ C * (1 + ‖s‖) ^ (-((n : ℝ) + 3)) := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' hr F F' hF hF' n
  have hp := rd_iter_pow hI Wp Wq P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' hr
  obtain ⟨K0, hK0⟩ := hp 0 F F' hF hF'
  obtain ⟨KN, hKN⟩ := hp (n + 3) F F' hF hF'
  refine ⟨2 ^ (n + 3) * (K0 + KN), fun s => ?_⟩
  have hx : 0 ≤ ‖s‖ := norm_nonneg _
  have hb : 0 ≤ ‖B.beta D (wvG D.z D.z' s F) F'‖ := norm_nonneg _
  have hb0 : ‖B.beta D (wvG D.z D.z' s F) F'‖ ≤ K0 := by simpa using hK0 s
  have hbN := hKN s
  have hpos : 0 < 1 + ‖s‖ := by linarith
  have main : (1 + ‖s‖) ^ (n + 3) * ‖B.beta D (wvG D.z D.z' s F) F'‖ ≤ 2 ^ (n + 3) * (K0 + KN) := by
    calc (1 + ‖s‖) ^ (n + 3) * ‖B.beta D (wvG D.z D.z' s F) F'‖
        ≤ 2 ^ (n + 3) * (1 + ‖s‖ ^ (n + 3)) * ‖B.beta D (wvG D.z D.z' s F) F'‖ :=
          mul_le_mul_of_nonneg_right (rd_pow_le _ hx _) hb
      _ = 2 ^ (n + 3) * (‖B.beta D (wvG D.z D.z' s F) F'‖ +
            ‖s‖ ^ (n + 3) * ‖B.beta D (wvG D.z D.z' s F) F'‖) := by ring
      _ ≤ 2 ^ (n + 3) * (K0 + KN) := mul_le_mul_of_nonneg_left (add_le_add hb0 hbN) (by positivity)
  have hr' : (1 + ‖s‖) ^ (-((n : ℝ) + 3)) = ((1 + ‖s‖) ^ (n + 3))⁻¹ := by
    rw [Real.rpow_neg hpos.le]
    congr 1
    rw [show ((n : ℝ) + 3) = ((n + 3 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  rw [hr', ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  linarith [main]

theorem radDecay_of_cut (hI : RDIdent) : RadDecay := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' l hl ε G H hε hG hH Φ Ψ hΦ hΨ
    c hc n
  have hr : 0 < P.r := lt_of_le_of_lt (Nat.zero_le _) l.isLt
  have hl' : l = ⟨0, hr⟩ := Fin.ext hl
  have hl0 : l.castSucc = (0 : Fin (P.r + 1)) := Fin.ext (by simp [hl])
  obtain ⟨C', hC'⟩ := rd_decay hI Wp Wq P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' hr G H
    ⟨ε, hε, hG⟩ ⟨ε, hε, hH⟩ n
  subst hz hz' hπ hπ'
  obtain ⟨C1, -, hC1⟩ := radial_beta_identity P.k P.r Wp Wq D μ hD.2.1
  refine ⟨‖C1‖ * C', fun s Wv hW => ?_⟩
  have hwv := radial_wave_identity P.k P.r Wp Wq D hr ε s G
  have hΦ' : ∀ y ∈ DomR P.k P.r D.z D.z', ((Wv Φ : RadSp P.k P.r D.z D.z' D.π D.π') :
      Fn P.k P.r (Wq →L[ℂ] Wp)) y.1 y.2 = resG P.k P.r (Fin.last P.r) (B.JF D (wvG D.z D.z' s G)) y.1 y.2 := by
    intro y hy
    rw [hW Φ y.1 y.2, hΦ y hy, hwv.2 y hy, hl']
  rw [hl0, hC1 (wvG D.z D.z' s G) H (Wv Φ) Ψ (hwv.1 hG).2.1 hH.2.1 hΦ' hΨ c, norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hC' s) (norm_nonneg _)

end Formalism.FourierDecayAlt.P.CutSE
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.SideOnePositive
section
noncomputable section

namespace Formalism.FourierDecayAlt.P

theorem side_one_positive : CutHB.Side1Pos :=
  LevelPointCoordinates.side1Pos_of smooth_truncation_induction smooth_truncation_exists (SliceIntegralLemmas.side0Pos_of'' proper_left_variables_domain)
    letters_pass_partial_bessel proper_left_variables_domain

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.SideZeroOfLocalProperness
section
namespace Formalism.FourierDecayAlt.P.SliceIntegralLemmas

open Formalism.FourierDecayAlt

theorem side_zero_of_local_properness (hPr : ProperLeftVariablesDomain) : CutHB.Side0 :=
  CutHB.side_zero_of_positive_and_zero (side0Pos_of'' hPr) (side0Zero_of Formalism.FourierDecayAlt.P.letters_pass_partial_bessel hPr CutHB.pts)

end Formalism.FourierDecayAlt.P.SliceIntegralLemmas

namespace Formalism.FourierDecayAlt.P

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPCompactOfStepSquare
section
namespace Formalism.FourierDecayAlt.P5.HerD

theorem thmPActualCpt_of_stepExp0 (h0 : StepExp0) : ThmPActualCpt :=
  theorem_P_compact_of_step_density Formalism.FourierDecayAlt.P.level_transport_hermitian h0

end Formalism.FourierDecayAlt.P5.HerD
end

