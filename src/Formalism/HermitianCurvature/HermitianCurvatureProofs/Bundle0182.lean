import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0178
import Formalism.HermitianCurvature.HeisenbergConjugationMeasurePreserving
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitTailEstimates
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WirtingerIntegrationByParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SlicesFiniteRegularityBuilt

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJALocToolsOp
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.BetaSesquilinearity
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA.LT

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section op

variable {k r : ℕ} {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']

theorem coefLeib {O UU : Set (B.Mat k r)} (hO : IsOpen O) (hcov : ∀ g ∈ B.GV k r, g ∈ O ∨ g ∈ UU)
    {a : B.Mat k r → (E →L[ℂ] E')} {Φ : B.Mat k r → E} {d Bg A : ℝ} (hBg : 0 ≤ Bg)
    (ha : B.CkOn ⊤ UU a)
    (hab : ∀ m : ℕ, ∃ C : ℝ, ∀ u v : List (B.Mat k r), (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ v, B.unitLie k r X) →
      u.length + v.length ≤ m → ∀ g ∈ B.GV k r, g ∉ O → ‖B.dLR u v a g‖ ≤ C * B.gN g ^ (d + Bg * m))
    (hΦ : B.CkOn ⊤ (B.GV k r) Φ) (hΦg : ∀ m : ℕ, B.InCC (A - Bg * m) m Φ)
    (hz : ∀ g ∈ B.GV k r, g ∈ O → Φ g = 0) :
    B.CkOn ⊤ (B.GV k r) (ap a Φ) ∧ ∀ n : ℕ, B.InCC (A - d - Bg * n) n (ap a Φ) := by
  have hP : Pr O UU ⊤ a Φ := ⟨ha, hΦ, hz⟩
  refine ⟨hP.ck hO hcov, fun n => ?_⟩
  choose Ca hCa using hab
  choose cF hcF using hΦg
  set Ka : ℝ := ∑ j ∈ Finset.range (n + 1), |Ca j| with hKa
  set K : ℝ := ∑ j ∈ Finset.range (n + 1), |cF j| with hK
  have hKaj : ∀ j ≤ n, |Ca j| ≤ Ka := fun j hj =>
    Finset.single_le_sum (f := fun j => |Ca j|) (fun i _ => abs_nonneg _)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hj))
  have hKj : ∀ j ≤ n, |cF j| ≤ K := fun j hj =>
    Finset.single_le_sum (f := fun j => |cF j|) (fun i _ => abs_nonneg _)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hj))
  have hKa0 : 0 ≤ Ka := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hCK : 0 ≤ Ka * K := mul_nonneg hKa0 hK0
  refine ⟨2 ^ n * (Ka * K), sCkOn_mono le_top (hP.ck hO hcov), fun u v hu hv hl g hg => ?_⟩
  have hlie := lie_LR (unit_lie hu) (unit_lie hv)
  have hw : (wL u ++ wR v).length = u.length + v.length := len_LR u v
  have hP' : Pr O UU ((wL u ++ wR v).length : ℕ) a Φ := hP.mono le_top
  have hp := gN_pos hg
  have hg1 := gN_ge_one hg
  rw [dLR_eq]
  by_cases hgO : g ∈ O
  · rw [Dw_vanish hO hlie (hP'.mono zero_le).apz g hg hgO]
    simp only [norm_zero, mul_zero]
    exact mul_nonneg (by positivity) hCK
  · have hb := leib_bound hO hcov g hg (Ka * K * B.gN g ^ (d + Bg * (((wL u ++ wR v).length : ℕ) : ℝ) - A))
      (wL u ++ wR v) a Φ hlie hP' (by
        intro w₁ w₂ hs₁ hs₂ hl₁₂
        obtain ⟨u₁, v₁, hu₁, hv₁, rfl⟩ := sub_LR hs₁
        obtain ⟨u₂, v₂, hu₂, hv₂, rfl⟩ := sub_LR hs₂
        rw [len_LR, len_LR] at hl₁₂
        have hl₁ : u₁.length + v₁.length ≤ n := by
          have := hu₁.length_le; have := hv₁.length_le; omega
        have hl₂ : u₂.length + v₂.length ≤ n := by
          have := hu₂.length_le; have := hv₂.length_le; omega
        have hu₁' : ∀ X ∈ u₁, B.unitLie k r X := fun X hX => hu X (hu₁.subset hX)
        have hv₁' : ∀ X ∈ v₁, B.unitLie k r X := fun X hX => hv X (hv₁.subset hX)
        have hu₂' : ∀ X ∈ u₂, B.unitLie k r X := fun X hX => hu X (hu₂.subset hX)
        have hv₂' : ∀ X ∈ v₂, B.unitLie k r X := fun X hX => hv X (hv₂.subset hX)
        set L₁ : ℝ := ((u₁.length + v₁.length : ℕ) : ℝ) with hL₁
        set L₂ : ℝ := ((u₂.length + v₂.length : ℕ) : ℝ) with hL₂
        have b1 : ‖Dw (wL u₁ ++ wR v₁) a g‖ ≤ Ka * B.gN g ^ (d + Bg * L₁) := by
          rw [← dLR_eq]
          have h1 := hCa (u₁.length + v₁.length) u₁ v₁ hu₁' hv₁' le_rfl g hg hgO
          calc _ ≤ Ca (u₁.length + v₁.length) * B.gN g ^ (d + Bg * L₁) := by rw [hL₁]; exact h1
            _ ≤ |Ca (u₁.length + v₁.length)| * B.gN g ^ (d + Bg * L₁) :=
              mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg hp.le _)
            _ ≤ Ka * B.gN g ^ (d + Bg * L₁) :=
              mul_le_mul_of_nonneg_right (hKaj _ hl₁) (Real.rpow_nonneg hp.le _)
        have b2 : ‖Dw (wL u₂ ++ wR v₂) Φ g‖ ≤ K * B.gN g ^ (Bg * L₂ - A) := by
          rw [← dLR_eq]
          have h1 := (hcF (u₂.length + v₂.length)).2 u₂ v₂ hu₂' hv₂' le_rfl g hg
          have e : B.gN g ^ (Bg * L₂ - A) * B.gN g ^ (A - Bg * L₂) = 1 := by
            rw [← Real.rpow_add hp]; simp
          have h4 : ‖B.dLR u₂ v₂ Φ g‖ =
              B.gN g ^ (Bg * L₂ - A) * (B.gN g ^ (A - Bg * L₂) * ‖B.dLR u₂ v₂ Φ g‖) := by
            rw [← mul_assoc, e, one_mul]
          rw [h4]
          have h5 : B.gN g ^ (A - Bg * L₂) * ‖B.dLR u₂ v₂ Φ g‖ ≤ K := by
            refine le_trans ?_ (hKj _ hl₂)
            refine le_trans ?_ (le_abs_self _)
            simpa [hL₂] using h1
          calc _ ≤ B.gN g ^ (Bg * L₂ - A) * K := mul_le_mul_of_nonneg_left h5 (Real.rpow_nonneg hp.le _)
            _ = K * B.gN g ^ (Bg * L₂ - A) := mul_comm _ _
        have hsum : (d + Bg * L₁) + (Bg * L₂ - A) = d + Bg * (((wL u ++ wR v).length : ℕ) : ℝ) - A := by
          rw [← hl₁₂, hL₁, hL₂]; push_cast; ring
        calc ‖Dw (wL u₁ ++ wR v₁) a g‖ * ‖Dw (wL u₂ ++ wR v₂) Φ g‖
            ≤ (Ka * B.gN g ^ (d + Bg * L₁)) * (K * B.gN g ^ (Bg * L₂ - A)) :=
              mul_le_mul b1 b2 (norm_nonneg _) (mul_nonneg hKa0 (Real.rpow_nonneg hp.le _))
          _ = Ka * K * (B.gN g ^ (d + Bg * L₁) * B.gN g ^ (Bg * L₂ - A)) := by ring
          _ = Ka * K * B.gN g ^ (d + Bg * (((wL u ++ wR v).length : ℕ) : ℝ) - A) := by
              rw [← Real.rpow_add hp, hsum])
    have hlen : ((wL u ++ wR v).length : ℕ) ≤ n := by rw [hw]; exact hl
    have e2 : B.gN g ^ (A - d - Bg * n) * B.gN g ^ (d + Bg * (((wL u ++ wR v).length : ℕ) : ℝ) - A) ≤ 1 := by
      rw [← Real.rpow_add hp]
      refine Real.rpow_le_one_of_one_le_of_nonpos hg1 ?_
      have h6 : (((wL u ++ wR v).length : ℕ) : ℝ) ≤ n := by exact_mod_cast hlen
      nlinarith [mul_le_mul_of_nonneg_left h6 hBg]
    have e3 : (2 : ℝ) ^ (wL u ++ wR v).length ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hlen
    calc B.gN g ^ (A - d - Bg * n) * ‖Dw (wL u ++ wR v) (ap a Φ) g‖
        ≤ B.gN g ^ (A - d - Bg * n) * (2 ^ (wL u ++ wR v).length *
            (Ka * K * B.gN g ^ (d + Bg * (((wL u ++ wR v).length : ℕ) : ℝ) - A))) :=
          mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hp.le _)
      _ = 2 ^ (wL u ++ wR v).length * (Ka * K) *
            (B.gN g ^ (A - d - Bg * n) * B.gN g ^ (d + Bg * (((wL u ++ wR v).length : ℕ) : ℝ) - A)) := by ring
      _ ≤ 2 ^ (wL u ++ wR v).length * (Ka * K) * 1 :=
          mul_le_mul_of_nonneg_left e2 (mul_nonneg (by positivity) hCK)
      _ ≤ 2 ^ n * (Ka * K) := by rw [mul_one]; exact mul_le_mul_of_nonneg_right e3 hCK

theorem rwG {w : List (B.Mat k r)} (hw : ∀ X ∈ w, B.inLie k r X) {Φ : B.Mat k r → E} {A Bg : ℝ}
    (hΦ : B.CkOn ⊤ (B.GV k r) Φ) (hΦg : ∀ m : ℕ, B.InCC (A - Bg * m) m Φ) :
    B.CkOn ⊤ (B.GV k r) (B.Rw w Φ) ∧ ∀ m : ℕ, B.InCC (A - Bg * w.length - Bg * m) m (B.Rw w Φ) := by
  refine ⟨?_, fun m => ?_⟩
  · rw [← Dw_wR]
    apply CkOn_Dw (fun x hx => lie_LR (u := []) (by simp) hw x (by simpa [wL] using hx))
    simpa using hΦ
  · have h := InCC_Rw (m := m) hw (hΦg (m + w.length))
    have e : A - Bg * ((m + w.length : ℕ) : ℝ) = A - Bg * w.length - Bg * m := by push_cast; ring
    rwa [e] at h

theorem listSumG {ι : Type*} (l : List ι) (f : ι → B.Mat k r → E) {A Bg : ℝ}
    (h : ∀ i ∈ l, B.CkOn ⊤ (B.GV k r) (f i) ∧ ∀ m : ℕ, B.InCC (A - Bg * m) m (f i)) :
    B.CkOn ⊤ (B.GV k r) (fun g => (l.map fun i => f i g).sum) ∧
      ∀ m : ℕ, B.InCC (A - Bg * m) m (fun g => (l.map fun i => f i g).sum) := by
  induction l with
  | nil =>
    simp only [List.map_nil, List.sum_nil]
    exact ⟨CkOn_zero, fun m => ⟨0, CCle_zero⟩⟩
  | cons i l ih =>
    have hi := h i (by simp)
    have hl := ih (fun j hj => h j (by simp [hj]))
    simp only [List.map_cons, List.sum_cons]
    refine ⟨CkOn_add hi.1 hl.1, fun m => ?_⟩
    obtain ⟨c, hc⟩ := hi.2 m
    obtain ⟨c', hc'⟩ := hl.2 m
    exact ⟨c + c', CCle_add hc hc'⟩

end op

theorem operator_in_class_holds : OpCCg := by
  intro k r Wp Wq _ _ _ _ _ _ Bs Θ d Bg A η F hη hBg hSC hCG hF hFg hz
  set O : Set (B.Mat k r) := {g | Gf k r Bs.z Bs.z' g < η} with hOdef
  have hO : IsOpen O := isOpen_lt (Gf_cont _ _) continuous_const
  have hcov : ∀ g ∈ B.GV k r, g ∈ O ∨ g ∈ B.GPos Bs := by
    intro g hg
    by_cases h : Gf k r Bs.z Bs.z' g < η
    · exact Or.inl h
    · exact Or.inr ⟨hg, lt_of_lt_of_le hη (not_lt.1 h)⟩
  have hzO : ∀ g ∈ B.GV k r, g ∈ O → F g = 0 := fun g hg h => hz g hg h
  have hoff : ∀ g, g ∉ O → η ≤ Gf k r Bs.z Bs.z' g := fun g h => not_lt.1 h
  have hab1 : ∀ T ∈ Θ, ∀ m : ℕ, ∃ C : ℝ, ∀ u v : List (B.Mat k r), (∀ X ∈ u, B.unitLie k r X) →
      (∀ X ∈ v, B.unitLie k r X) → u.length + v.length ≤ m → ∀ g ∈ B.GV k r, g ∉ O →
        ‖B.dLR u v T.coef g‖ ≤ C * B.gN g ^ (d + Bg * m) := by
    intro T hT m
    obtain ⟨C, hC⟩ := hCG T hT η hη m
    exact ⟨C, fun u v hu hv hl g hg hgO => (hC u v hu hv hl g hg (hoff g hgO)).1⟩
  have hab2 : ∀ T ∈ Θ, ∀ m : ℕ, ∃ C : ℝ, ∀ u v : List (B.Mat k r), (∀ X ∈ u, B.unitLie k r X) →
      (∀ X ∈ v, B.unitLie k r X) → u.length + v.length ≤ m → ∀ g ∈ B.GV k r, g ∉ O →
        ‖B.dLR u v T.coefAdj g‖ ≤ C * B.gN g ^ (d + Bg * m) := by
    intro T hT m
    obtain ⟨C, hC⟩ := hCG T hT η hη m
    exact ⟨C, fun u v hu hv hl g hg hgO => (hC u v hu hv hl g hg (hoff g hgO)).2⟩
  have hApp : ∀ T ∈ Θ, B.CkOn ⊤ (B.GV k r) (ap T.coef (B.Rw T.word F)) ∧
      ∀ m : ℕ, B.InCC (A - d - Bg * (B.opOrder Θ : ℝ) - Bg * m) m (ap T.coef (B.Rw T.word F)) := by
    intro T hT
    have hR := rwG T.word_lie hF hFg
    have hzR : ∀ g ∈ B.GV k r, g ∈ O → B.Rw T.word F g = 0 := Rw_vanish hO T.word_lie hzO
    have hc := coefLeib hO hcov hBg (hSC T hT).1 (hab1 T hT) hR.1 hR.2 hzR
    have hlen : (T.word.length : ℝ) ≤ (B.opOrder Θ : ℝ) := by
      exact_mod_cast Formalism.FourierDecayAlt.P.B5.len_le_order Θ hT
    refine ⟨hc.1, fun m => sInCC_mono ?_ le_rfl (hc.2 m)⟩
    nlinarith [mul_le_mul_of_nonneg_left hlen hBg]
  have hAdj : ∀ T ∈ Θ, B.CkOn ⊤ (B.GV k r)
        (fun g => ((-1 : ℂ) ^ T.word.length) • B.Rw T.word.reverse (fun x => T.coefAdj x (F x)) g) ∧
      ∀ m : ℕ, B.InCC (A - d - Bg * (B.opOrder Θ : ℝ) - Bg * m) m
        (fun g => ((-1 : ℂ) ^ T.word.length) • B.Rw T.word.reverse (fun x => T.coefAdj x (F x)) g) := by
    intro T hT
    have hc := coefLeib hO hcov hBg (hSC T hT).2 (hab2 T hT) hF hFg hzO
    have hR := rwG (w := T.word.reverse) (fun X hX => T.word_lie X (List.mem_reverse.1 hX)) hc.1 hc.2
    have hlen : (T.word.length : ℝ) ≤ (B.opOrder Θ : ℝ) := by
      exact_mod_cast Formalism.FourierDecayAlt.P.B5.len_le_order Θ hT
    refine ⟨CkOn_smul _ hR.1, fun m => ?_⟩
    have h2 := hR.2 m
    rw [List.length_reverse] at h2
    obtain ⟨c, hcc⟩ := sInCC_mono (A := A - d - Bg * (B.opOrder Θ : ℝ) - Bg * m) (by
      nlinarith [mul_le_mul_of_nonneg_left hlen hBg]) le_rfl h2
    exact ⟨_, CCle_smul _ hcc⟩
  exact ⟨listSumG Θ (fun T => ap T.coef (B.Rw T.word F)) hApp,
    listSumG Θ (fun T g => ((-1 : ℂ) ^ T.word.length) • B.Rw T.word.reverse (fun x => T.coefAdj x (F x)) g) hAdj⟩

end Formalism.FourierDecayAlt.P.CutMP.JA.LT

end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrableBlockIntegrand
section
namespace Formalism.FourierDecayAlt.P.FormNormSumIdentities

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.G MeasureTheory Filter

noncomputable section

section om

variable {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]

theorem maxpow_le_onepow {x y a : ℝ} (hy : 0 ≤ y) (hxy : y ≤ x) (ha : 0 ≤ a) :
    (1 + x) ^ (-a) ≤ (max 1 y) ^ (-a) := by
  refine Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le one_pos (le_max_left _ _)) ?_ (by linarith)
  exact max_le (by linarith) (by linarith)

theorem continuous_lowRow (n : ℕ) : Continuous (fun a : Fin n → ℂ => lowRow a) := by
  unfold lowRow
  exact P.G7.continuous_blk continuous_const continuous_const continuous_id continuous_const

theorem continuous_blkU (n : ℕ) :
    Continuous (fun p : (UT n → ℂ) × (Fin n → ℂ) => blk (upper p.1) p.2 0 1) :=
  P.G7.continuous_blk (P.Dx2.SL.cont_upper.comp continuous_fst) continuous_snd continuous_const continuous_const

theorem continuous_orbM (n : ℕ) (t c : ℂ) : Continuous (orbM n t c) := by
  unfold orbM
  refine Continuous.matrix_mul (Continuous.matrix_mul ((continuous_lowRow n).comp continuous_fst) continuous_const) ?_
  exact (continuous_blkU n).comp (continuous_snd)

theorem integrable_blockIntegrand (β : ℂ) (m : ℕ) (Φ : Mat (m + 2) → V) (t c : ℂ) (ht : t ≠ 0) (K a : ℝ)
    (ha : ((m : ℝ) + 1) * ((m : ℝ) + 4) < a) (hc : ∀ p, ContinuousAt Φ (orbM (m + 1) t c p))
    (hb : ∀ p, ‖Φ (orbM (m + 1) t c p)‖ ≤ K * (1 + ‖orbM (m + 1) t c p‖) ^ (-a)) :
    Integrable (blockIntegrand β (m + 1) Φ t c) (muBlock β (m + 1)) := by
  have ha0 : 0 ≤ a := le_trans (by positivity) ha.le
  have hK : 0 ≤ K := by
    have h := hb 0
    by_contra hn
    have : K * (1 + ‖orbM (m + 1) t c 0‖) ^ (-a) < 0 :=
      mul_neg_of_neg_of_pos (lt_of_not_ge hn) (Real.rpow_pos_of_pos (by positivity) _)
    linarith [norm_nonneg (Φ (orbM (m + 1) t c 0))]
  have hpt : ∀ p : BlockCoord (m + 1),
      ‖blockIntegrand β (m + 1) Φ t c p‖ ≤ K * (max 1 ‖coordMap (m + 1) t p‖) ^ (-a) := by
    intro p
    rw [P.OrbitTailEstimates.norm_blockIntegrand]
    refine (hb p).trans (mul_le_mul_of_nonneg_left ?_ hK)
    exact maxpow_le_onepow (norm_nonneg _) (P.OrbitTailEstimates.norm_coordMap_le (m + 1) t c p) ha0
  obtain ⟨k, hk⟩ := P.G7.muBlock_eq β (m + 1)
  have i3 : BorelSpace (BlockCoord (m + 1)) := inferInstance
  have j1 : (volume : Measure ((UT (m + 1) → ℂ) × (Fin (m + 1) → ℂ))).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  have j2 : (volume : Measure (BlockCoord (m + 1))).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  have hfr : (Module.finrank ℝ (BlockCoord (m + 1)) : ℝ) < a := by
    rw [P.OrbitTailEstimates.finrank_block_cast]; exact ha
  have hI : Integrable (fun q : BlockCoord (m + 1) => (max 1 ‖q‖) ^ (-a)) (muBlock β (m + 1)) := by
    rw [hk]; exact (P.OrbitTailEstimates.integrable_maxpow volume a hfr).smul_measure_nnreal
  have hJ := P.G7.jacobian (m + 1) β t ht
  have hI' : Integrable (fun p : BlockCoord (m + 1) => (max 1 ‖coordMap (m + 1) t p‖) ^ (-a))
      (muBlock β (m + 1)) := by
    have h2 : Integrable (fun q : BlockCoord (m + 1) => (max 1 ‖q‖) ^ (-a))
        (Measure.map (coordMap (m + 1) t) (muBlock β (m + 1))) := hJ ▸ hI.smul_measure_nnreal
    exact (P.G7.embedding_coordMap _ t ht).integrable_map_iff.1 h2
  have hcont : Continuous (blockIntegrand β (m + 1) Φ t c) := by
    unfold blockIntegrand
    refine Continuous.smul ?_ ?_
    · have h1 : Continuous fun p : BlockCoord (m + 1) => G.subSum (lowRow p.1) := by
        unfold G.subSum
        exact continuous_finsetSum _ fun i _ =>
          (continuous_apply _).comp ((continuous_apply _).comp ((continuous_lowRow (m + 1)).comp continuous_fst))
      have h2 : Continuous fun p : BlockCoord (m + 1) => G.superSum (blk (upper p.2.1) p.2.2 0 1) := by
        unfold G.superSum
        exact continuous_finsetSum _ fun i _ =>
          (continuous_apply _).comp ((continuous_apply _).comp ((continuous_blkU (m + 1)).comp continuous_snd))
      exact ((P.G7.continuous_psi β).comp h1).mul ((P.G7.continuous_psi β).comp h2)
    · exact continuous_iff_continuousAt.2 fun p => (hc p).comp (continuous_orbM (m + 1) t c).continuousAt
  exact (hI'.const_mul K).mono' hcont.aestronglyMeasurable (Eventually.of_forall hpt)

theorem integrable_longIntegrand (n : ℕ) (Φ : Mat (n + 1) → V) (z : ℂ) (hz : z ≠ 0) (K a : ℝ)
    (ha : (Module.finrank ℝ (UT (n + 1) → ℂ) : ℝ) < a)
    (hc : ∀ v, ContinuousAt Φ (P.JCTx6.Pos.Zv n z v))
    (hb : ∀ v, ‖Φ (P.JCTx6.Pos.Zv n z v)‖ ≤ K * (1 + ‖P.JCTx6.Pos.Zv n z v‖) ^ (-a)) :
    Integrable (fun v : UT (n + 1) → ℂ => psi U.betaU (superSum (upper v)) • Φ (P.JCTx6.Pos.Zv n z v))
      (muPi U.betaU (UT (n + 1))) := by
  have ha0 : 0 ≤ a := le_trans (Nat.cast_nonneg _) ha.le
  have hK : 0 ≤ K := by
    have h := hb 0
    by_contra hn
    have : K * (1 + ‖P.JCTx6.Pos.Zv n z 0‖) ^ (-a) < 0 :=
      mul_neg_of_neg_of_pos (lt_of_not_ge hn) (Real.rpow_pos_of_pos (by positivity) _)
    linarith [norm_nonneg (Φ (P.JCTx6.Pos.Zv n z 0))]
  have hZc : Continuous (fun v : UT (n + 1) → ℂ => P.JCTx6.Pos.Zv n z v) := by
    show Continuous (fun v : UT (n + 1) → ℂ =>
      ((ptLong (n + 1) z * upper v : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) : Mat (n + 1)))
    exact continuous_const.matrix_mul P.Dx2.SL.cont_upper
  have hΦc : Continuous (fun v : UT (n + 1) → ℂ => Φ (P.JCTx6.Pos.Zv n z v)) :=
    continuous_iff_continuousAt.2 fun v => (hc v).comp hZc.continuousAt
  have hψc : Continuous (fun v : UT (n + 1) → ℂ => psi U.betaU (superSum (upper v))) := by
    have h1 : Continuous fun v : UT (n + 1) → ℂ => superSum (upper v) := by
      unfold superSum
      exact continuous_finsetSum _ fun i _ =>
        (continuous_apply _).comp ((continuous_apply _).comp P.Dx2.SL.cont_upper)
    exact (P.G7.continuous_psi _).comp h1
  have hbound : ∀ v : UT (n + 1) → ℂ, ‖psi U.betaU (superSum (upper v)) • Φ (P.JCTx6.Pos.Zv n z v)‖ ≤
      K * (min 1 ‖z‖) ^ (-a) * (1 + ‖v‖) ^ (-a) := by
    intro v
    rw [norm_smul, P.WirtingerIntegrationByParts.norm_psi, one_mul]
    refine (hb v).trans ?_
    have := mul_le_mul_of_nonneg_left (P.JCTx6.Pos.Zv_decay n hz v ha0) hK
    rw [← mul_assoc] at this
    exact this
  rw [P.Dx2.SL.muPi_betaU]
  apply Integrable.smul_measure_nnreal
  exact ((integrable_one_add_norm ha).const_mul (K * (min 1 ‖z‖) ^ (-a))).mono'
    (hψc.smul hΦc).aestronglyMeasurable (Eventually.of_forall hbound)

theorem clm_omBlock [CompleteSpace V] [CompleteSpace W] (L : V →L[ℂ] W) (β : ℂ) (n : ℕ) (Φ : Mat (n + 1) → V)
    (t c : ℂ) (hI : Integrable (blockIntegrand β n Φ t c) (muBlock β n)) :
    L (OmBlock β n Φ t c) = OmBlock β n (fun Z => L (Φ Z)) t c := by
  unfold OmBlock
  rw [← L.integral_comp_comm hI]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp only [blockIntegrand, L.map_smul]

theorem clm_omLong [CompleteSpace V] [CompleteSpace W] (L : V →L[ℂ] W) (β : ℂ) (n : ℕ) (Φ : Mat (n + 1) → V)
    (z : ℂ) (hI : Integrable (fun v : UT (n + 1) → ℂ => psi β (superSum (upper v)) • Φ (ptLong (n + 1) z * upper v))
      (muPi β (UT (n + 1)))) :
    L (OmLong β n Φ z) = OmLong β n (fun Z => L (Φ Z)) z := by
  unfold OmLong
  rw [← L.integral_comp_comm hI]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [L.map_smul]

end om

end

end Formalism.FourierDecayAlt.P.FormNormSumIdentities
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrableSliceAppendSingle
section
open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

theorem point_size_append_single (h : C.LPt) (c : ℂ) : D.ptSize (h ++ [(1, c)]) = D.ptSize h + (0 + 1) := by
  rw [Dx2.SL.ptSize_append]

theorem integrable_slice_append_single {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (z z' : Fin (2 * r + k + 1) → ℂ) (F : B.Mat k r → E) (h : C.LPt) (c : ℂ)
    (hle : D.ptSize (h ++ [(1, c)]) ≤ r) (hloc : D.IsLocPt (h ++ [(1, c)]) (D.ptSize (h ++ [(1, c)])))
    (γ' : B.Mat k (r - D.ptSize (h ++ [(1, c)])))
    (hI : Integrable (JCTx6.gInt k (D.ptSize h) 0 (r - D.ptSize (h ++ [(1, c)])) (D.ptPerm h) (D.ptDiag h) c
        (D.castV (by have := point_size_append_single h c; omega) z) (D.castV (by have := point_size_append_single h c; omega) z')
        (D.castF (by have := point_size_append_single h c; omega) F) γ')
      (JCTx6.muG k (D.ptSize h) 0 (r - D.ptSize (h ++ [(1, c)])) (D.ptPerm h))) :
    Integrable (fun ξ : U.Xi k (D.ptSize (h ++ [(1, c)])) 0 (r - D.ptSize (h ++ [(1, c)])) (D.ptPerm (h ++ [(1, c)])) =>
        U.psiStar k (r - D.ptSize (h ++ [(1, c)])) (D.ptPerm (h ++ [(1, c)])) (D.castV (by omega) z)
            (D.castV (by omega) z') ξ •
          D.castF (by omega) F (U.gaXi k (r - D.ptSize (h ++ [(1, c)])) (D.ptPerm (h ++ [(1, c)]))
            (D.ptDiag (h ++ [(1, c)])) ξ (fun a => a.elim0) γ'))
      (U.muXi k (D.ptSize (h ++ [(1, c)])) 0 (r - D.ptSize (h ++ [(1, c)])) (D.ptPerm (h ++ [(1, c)]))) := by
  have hP : D.ptSize (h ++ [(1, c)]) = D.ptSize h + (0 + 1) := point_size_append_single h c
  have hspec := (Formalism.FourierDecayAlt.P.ptPerm_spec _ _ hloc).1
  have hspec' := (Formalism.FourierDecayAlt.P.ptPerm_spec _ _ (Dx2.SL.isLocPt_head hloc)).1
  have hσ : ∀ a : Fin (D.ptSize (h ++ [(1, c)])),
      ((Dx2.SL.sigP (n := 0) (D.ptPerm h)) (Fin.cast hP a)).val = (D.ptPerm (h ++ [(1, c)]) a).val := by
    intro a
    rw [hspec a, Dx2.SL.partner_append 1 c h a.val (by have := a.isLt; omega)]
    by_cases h1 : a.val < D.ptSize h
    · rw [if_pos h1]
      have e : Fin.cast hP a = Fin.castAdd (0 + 1) ⟨a.val, h1⟩ := Fin.ext rfl
      rw [e, Dx2.SL.blockPerm_castAdd]
      exact hspec' ⟨a.val, h1⟩
    · rw [if_neg h1]
      have e : Fin.cast hP a = Fin.natAdd (D.ptSize h) ⟨a.val - D.ptSize h, by have := a.isLt; omega⟩ :=
        Fin.ext (by simp; omega)
      rw [e, Dx2.SL.blockPerm_natAdd]
      simp only [Fin.val_natAdd, Fin.val_rev]
      omega
  have hd : ∀ a : Fin (D.ptSize (h ++ [(1, c)])),
      Dx2.SL.dP (n := 0) (D.ptDiag h) c (Fin.cast hP a) = D.ptDiag (h ++ [(1, c)]) a := by
    intro a
    simp only [D.ptDiag]
    rw [Dx2.SL.scal_append 1 c h a.val (by have := a.isLt; omega)]
    by_cases h1 : a.val < D.ptSize h
    · rw [if_pos h1]
      have e : Fin.cast hP a = Fin.castAdd (0 + 1) ⟨a.val, h1⟩ := Fin.ext rfl
      rw [e, Dx2.SL.dP, Fin.addCases_left]; rfl
    · rw [if_neg h1]
      have e : Fin.cast hP a = Fin.natAdd (D.ptSize h) ⟨a.val - D.ptSize h, by have := a.isLt; omega⟩ :=
        Fin.ext (by simp; omega)
      rw [e, Dx2.SL.dP, Fin.addCases_right]

  have hσ' : ∀ b : Fin (D.ptSize h + (0 + 1)),
      (D.ptPerm (h ++ [(1, c)]) (Fin.cast hP.symm b)).val = ((Dx2.SL.sigP (n := 0) (D.ptPerm h)) b).val := by
    intro b
    have := hσ (Fin.cast hP.symm b)
    rw [show Fin.cast hP (Fin.cast hP.symm b) = b from Fin.ext rfl] at this
    exact this.symm
  have hd' : ∀ b : Fin (D.ptSize h + (0 + 1)),
      D.ptDiag (h ++ [(1, c)]) (Fin.cast hP.symm b) = Dx2.SL.dP (n := 0) (D.ptDiag h) c b := by
    intro b
    have := hd (Fin.cast hP.symm b)
    rw [show Fin.cast hP (Fin.cast hP.symm b) = b from Fin.ext rfl] at this
    exact this.symm
  have h1 := JCTx6.Int.orbit_slice_integrable k (D.ptSize h) 0 (r - D.ptSize (h ++ [(1, c)])) (D.ptPerm h) (D.ptDiag h) c
    (D.castV (by have := point_size_append_single h c; omega) z) (D.castV (by have := point_size_append_single h c; omega) z') E
    (D.castF (by have := point_size_append_single h c; omega) F) γ' hI
  have h2 := (Dx2.SL.phi_transport (k := k) (ρ := r - D.ptSize (h ++ [(1, c)])) hP.symm _ _ hσ' _ _ hd'
    (D.castV (by have := point_size_append_single h c; omega) z) (D.castV (by have := point_size_append_single h c; omega) z')
    (D.castF (by have := point_size_append_single h c; omega) F) γ').1 h1
  simpa only [Dx2.SL.castV_castV, Dx2.SL.castF_castF] using h2

end Formalism.FourierDecayAlt.P.PBH
end
end

