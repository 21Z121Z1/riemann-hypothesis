import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0261
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DirectionsInParabolic
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixTranspose
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0051
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0033
import Formalism.FormalDegreeBessel.Bundle0002

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelPointEntryContDiffOn
section
open Matrix Filter Topology
open scoped ComplexConjugate ContDiff

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace Formalism.FourierDecayAlt.P.WirtingerOperators.XiPf

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.LevelPointCoordinates

theorem fsym (m n : ℕ) (i : Fin (m + n)) : finSumFinEquiv.symm i =
    if h : i.val < m then Sum.inl ⟨i, h⟩ else Sum.inr ⟨i - m, by omega⟩ := by
  split_ifs with h
  · rw [Equiv.symm_apply_eq]; ext; simp
  · rw [Equiv.symm_apply_eq]; ext; simp; omega

theorem castM_apply' {k a b : ℕ} (h : a = b) (g : B.Mat k a) (p q : Fin (2 * b + k + 1)) :
    D.castM h g p q = g (Fin.cast (by omega) p) (Fin.cast (by omega) q) := by
  subst h; simp [D.castM, Matrix.reindex_apply]

theorem castM_GV' {k a b : ℕ} (h : a = b) {g : B.Mat k a} (hg : g ∈ B.GV k a) : D.castM h g ∈ B.GV k b := by
  subst h; simpa [D.castM] using hg

theorem zfull_apply {j : ℕ} (Z : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ) (c d : Fin (j + 1)) :
    zfull Z τ c d = if hc : c.val < j then (if hd : d.val < j then Z ⟨c.val, hc⟩ ⟨d.val, hd⟩ else 0)
      else (if d.val < j then 0 else τ) := by
  simp only [zfull, U.blk2, Matrix.reindex_apply, Matrix.submatrix_apply, fsym]
  split_ifs <;> simp [Matrix.fromBlocks]

theorem det_zfull {j : ℕ} (Z : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ) : (zfull Z τ).det = Z.det * τ := by
  unfold zfull U.blk2
  rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]
  simp [Matrix.det_unique]

theorem wMat_mul_apply {d n : ℕ} (M : Matrix (Fin d) (Fin n) ℂ) (i : Fin d) (c : Fin n) :
    (G.wMat d * M) i c = M i.rev c := by
  simp [G.wMat, Matrix.mul_apply]

theorem level_point_first_lines (k r j : ℕ) (hj : j + 1 ≤ r) (Z : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ) (γ : B.Mat k (r - (j + 1)))
    (a : Fin j) (q : Fin (2 * r + k + 1)) :
    x0 k r j hj Z τ γ (esI k r (Fin.castLE (by omega) a)) q = if hq : q.val < j then Z a ⟨q.val, hq⟩ else 0 := by
  unfold x0
  rw [castM_apply']
  have hrow : (Fin.cast (by omega) (esI k r (Fin.castLE (by omega) a)) : Fin (2 * (j + 1 + (r - (j + 1))) + k + 1)) =
      U.eB k (j + 1) (r - (j + 1)) (Sum.inr ⟨j - a.val, by omega⟩) := by
    ext; rw [Ux4.block_index_last_val_eq]; simp [esI]; omega
  rw [hrow]
  obtain ⟨y, hy⟩ : ∃ y, U.eB k (j + 1) (r - (j + 1)) y = Fin.cast (by omega) q := ⟨_, Equiv.apply_symm_apply _ _⟩
  rw [← hy]
  unfold U.mMap
  rw [Ux4.block3_apply]
  rcases y with ((c | c) | c)
  · have hq : q.val = c.val := by
      have := congrArg Fin.val hy; rw [Ux4.block_index_first_val_eq] at this; simp at this; omega
    simp only [Matrix.fromBlocks_apply₂₁, Matrix.fromCols_apply_inl]
    rw [wMat_mul_apply]
    have hrev : (⟨j - a.val, by omega⟩ : Fin (j + 1)).rev = ⟨a.val, by omega⟩ := by
      ext; simp [Fin.rev]; omega
    rw [hrev, zfull_apply, dif_pos (by simp)]
    by_cases h : c.val < j
    · rw [dif_pos h, dif_pos (by omega)]
      exact congrArg₂ Z (Fin.ext rfl) (Fin.ext hq.symm)
    · rw [dif_neg h, dif_neg (by omega)]
  · have hq : q.val = j + 1 + c.val := by
      have := congrArg Fin.val hy; rw [Ux4.block_index_middle_val_eq] at this; simp at this; omega
    simp only [Matrix.fromBlocks_apply₂₁, Matrix.fromCols_apply_inr, Matrix.zero_apply]
    rw [dif_neg (by omega)]
  · have hq : q.val = j + 1 + (2 * (r - (j + 1)) + k + 1) + c.val := by
      have := congrArg Fin.val hy; rw [Ux4.block_index_last_val_eq] at this; simp at this; omega
    simp only [Matrix.fromBlocks_apply₂₂, Matrix.zero_apply]
    rw [dif_neg (by omega)]

theorem Hpk_eI_row (k r : ℕ) (a : Fin r) (s : Fin (2 * r + k + 1)) :
    Hpk k r (eI k r a) s = if s = esI k r a then 1 else 0 := by
  simp only [Hpk, eI, esI, Fin.ext_iff, Fin.val_mk]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem Hpk_eI_col (k r : ℕ) (a : Fin r) (s : Fin (2 * r + k + 1)) :
    Hpk k r s (eI k r a) = if s = esI k r a then 1 else 0 := by
  simp only [Hpk, eI, esI, Fin.ext_iff, Fin.val_mk]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem Hpk_low (k r : ℕ) (p s : Fin (2 * r + k + 1)) (hs : s.val < r) :
    Hpk k r p s = if p.val + s.val = 2 * r + k then 1 else 0 := by
  simp only [Hpk, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem xiCoef : XiCoef := by
  intro k r j hj Z τ γ a p
  have h1 : ∀ v : Fin (2 * r + k + 1) → ℂ, herm (Hpk k r) v (bvec (eI k r (Fin.castLE (by omega) a))) =
      ∑ s, Hpk k r (eI k r (Fin.castLE (by omega) a)) s * v s := by
    intro v
    simp [herm, bvec, dotProduct, Matrix.mulVec, Pi.single_apply]
  rw [h1]
  simp only [Hpk_eI_row, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [bvec, Matrix.mulVec_single_one, Matrix.transpose_apply]
  exact level_point_first_lines k r j hj Z τ γ a p

theorem x0_GV (k r j : ℕ) (hj : j + 1 ≤ r) (Z : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ) (γ : B.Mat k (r - (j + 1)))
    (hZ : Z.det ≠ 0) (hτ : τ ≠ 0) (hγ : γ ∈ B.GV k (r - (j + 1))) : x0 k r j hj Z τ γ ∈ B.GV k r := by
  unfold x0
  apply castM_GV'
  exact (Ux2.sliceMem k (j + 1) (r - (j + 1))).1 _ _ (by rw [det_zfull]; exact mul_ne_zero hZ hτ) hγ

theorem xiMem : XiMem := by
  intro k r j hj Z τ γ hZ hτ hγ
  exact ⟨x0_GV k r j hj Z τ γ hZ hτ hγ, fun a ha => absurd ha (by simp)⟩

theorem xiCoefV : XiCoefV := by
  intro k r j hj Z τ γ hZ hτ hγ a p
  have hinv := PBG.inv_GV (x0_GV k r j hj Z τ γ hZ hτ hγ)
  rw [hinv, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hH : Hpk k r *ᵥ bvec (eI k r (Fin.castLE (by omega) a)) = bvec (esI k r (Fin.castLE (by omega) a)) := by
    ext s
    simp only [bvec, Matrix.mulVec_single_one, Matrix.col_apply, Hpk_eI_col, Pi.single_apply]
  rw [hH]
  simp only [bvec, Matrix.mulVec_single_one, Matrix.col_apply, Matrix.conjTranspose_apply, level_point_first_lines]
  simp only [Matrix.mulVec, dotProduct]
  simp only [Matrix.col_apply, Matrix.conjTranspose_apply, level_point_first_lines]
  split_ifs with hp
  · rw [Fintype.sum_eq_single ⟨2 * r + k - p.val, by omega⟩]
    · have hH1 : Hpk k r p ⟨2 * r + k - p.val, by omega⟩ = 1 := by
        rw [Hpk_low _ _ _ _ (by simp only [Fin.val_mk]; omega), if_pos (by simp only [Fin.val_mk]; omega)]
      rw [hH1, one_mul, dif_pos (by simp only [Fin.val_mk]; omega)]
      rfl
    · intro s hs
      by_cases h : s.val < j
      · rw [dif_pos h]
        have : Hpk k r p s = 0 := by
          rw [Hpk_low _ _ _ _ (by omega), if_neg (by intro h'; apply hs; ext; simp only [Fin.val_mk]; omega)]
        rw [this, zero_mul]
      · rw [dif_neg h, star_zero, mul_zero]
  · refine Finset.sum_eq_zero fun s _ => ?_
    by_cases h : s.val < j
    · rw [dif_pos h]
      have : Hpk k r p s = 0 := by
        rw [Hpk_low _ _ _ _ (by omega), if_neg (by omega)]
      rw [this, zero_mul]
    · rw [dif_neg h, star_zero, mul_zero]

section smooth

variable {j : ℕ}

theorem contDiff_zfull (τ : ℂ) (c d : Fin (j + 1)) {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun Z : MJ j => zfull Z τ c d) := by
  simp only [zfull_apply]
  split_ifs
  · exact contDiff_apply_apply ℝ ℂ _ _
  · exact contDiff_const
  · exact contDiff_const
  · exact contDiff_const

theorem contDiff_adj_zfull (τ : ℂ) (c d : Fin (j + 1)) :
    ContDiff ℝ ⊤ (fun Z : MJ j => (zfull Z τ).adjugate c d) := by
  simp only [Matrix.adjugate_apply]
  apply PBG.contDiff_det'
  intro a b
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact contDiff_const
  · exact contDiff_zfull τ a b

theorem contDiffOn_inv_zfull (τ : ℂ) (c d : Fin (j + 1)) :
    ContDiffOn ℝ ∞ (fun Z : MJ j => (zfull Z τ)⁻¹ c d) {Z | Z.det ≠ 0} := by
  have he : ∀ Z : MJ j, (zfull Z τ)⁻¹ c d = (Z.det)⁻¹ * τ⁻¹ * (zfull Z τ).adjugate c d := by
    intro Z
    rw [Matrix.inv_def, Matrix.smul_apply, det_zfull, Ring.inverse_eq_inv', mul_inv, smul_eq_mul]
  simp only [he]
  have hdet : ContDiff ℝ ⊤ (fun Z : MJ j => Z.det) :=
    PBG.contDiff_det' (fun Z : MJ j => Z) (fun a b => contDiff_apply_apply ℝ ℂ a b)
  exact ((((hdet.of_le le_top).contDiffOn.inv (fun Z hZ => hZ)).mul contDiffOn_const).mul
    ((contDiff_adj_zfull τ c d).of_le le_top).contDiffOn)

theorem level_point_entry_contDiffOn (k r j : ℕ) (hj : j + 1 ≤ r) (τ : ℂ) (γ : B.Mat k (r - (j + 1)))
    (p q : Fin (2 * r + k + 1)) :
    ContDiffOn ℝ ∞ (fun Z : MJ j => x0 k r j hj Z τ γ p q) {Z | Z.det ≠ 0} := by
  obtain ⟨x, hx⟩ : ∃ x, U.eB k (j + 1) (r - (j + 1)) x = Fin.cast (by omega) p := ⟨_, Equiv.apply_symm_apply _ _⟩
  obtain ⟨y, hy⟩ : ∃ y, U.eB k (j + 1) (r - (j + 1)) y = Fin.cast (by omega) q := ⟨_, Equiv.apply_symm_apply _ _⟩
  have he : ∀ Z : MJ j, x0 k r j hj Z τ γ p q =
      Matrix.fromBlocks (Matrix.fromBlocks 0 0 0 γ) (Matrix.fromRows ((zfull Z τ)ᴴ⁻¹ * G.wMat (j + 1)) 0)
        (Matrix.fromCols (G.wMat (j + 1) * zfull Z τ) 0) 0 x y := by
    intro Z
    unfold x0 U.mMap
    rw [castM_apply', ← hx, ← hy, Ux4.block3_apply]
  simp only [he]
  have h13 : ∀ c d : Fin (j + 1),
      ContDiffOn ℝ ∞ (fun Z : MJ j => ((zfull Z τ)ᴴ⁻¹ * G.wMat (j + 1)) c d) {Z | Z.det ≠ 0} := by
    intro c d
    simp only [Matrix.mul_apply, ← Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_apply]
    exact ContDiffOn.sum fun t _ =>
      (PBG.contDiff_starC.comp_contDiffOn (contDiffOn_inv_zfull τ t c)).mul contDiffOn_const
  have h31 : ∀ c d : Fin (j + 1),
      ContDiffOn ℝ ∞ (fun Z : MJ j => (G.wMat (j + 1) * zfull Z τ) c d) {Z | Z.det ≠ 0} := by
    intro c d
    simp only [Matrix.mul_apply]
    exact ContDiffOn.sum fun t _ => contDiffOn_const.mul (contDiff_zfull τ t d).contDiffOn
  rcases x with ((c | c) | c) <;> rcases y with ((d | d) | d) <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl,
      Matrix.fromCols_apply_inr, Matrix.zero_apply]
  · exact contDiffOn_const
  · exact contDiffOn_const
  · exact h13 c d
  · exact contDiffOn_const
  · exact contDiffOn_const
  · exact contDiffOn_const
  · exact h31 c d
  · exact contDiffOn_const
  · exact contDiffOn_const

theorem xiSmooth : XiSmooth := by
  intro k r j hj τ γ
  exact contDiffOn_pi.2 fun p => contDiffOn_pi.2 fun q => level_point_entry_contDiffOn k r j hj τ γ p q

end smooth

end Formalism.FourierDecayAlt.P.WirtingerOperators.XiPf

namespace Formalism.FourierDecayAlt.P

theorem xi_coefficient : WirtingerOperators.XiCoef := WirtingerOperators.XiPf.xiCoef

theorem xi_coefficient_vector : WirtingerOperators.XiCoefV := WirtingerOperators.XiPf.xiCoefV

theorem xiMem_statement : WirtingerOperators.XiMem := WirtingerOperators.XiPf.xiMem

theorem xi_smooth : WirtingerOperators.XiSmooth := WirtingerOperators.XiPf.xiSmooth

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LocOfSmoothOnH
section
open Matrix
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.SingleEntryHermitianProducts

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.PBG

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem glev0 {g : Mat k r} (hg : g ∈ GV k r) : g ∈ Q.Glev k r 0 :=
  ⟨hg, fun a ha => by simp at ha⟩

theorem fold_congrV (V : Set (Mat k r)) :
    ∀ (L : List ((Mat k r → E) → (Mat k r → E))),
    (∀ T ∈ L, ∀ h₁ h₂ : Mat k r → E, (∀ x ∈ V, x ∈ GV k r → h₁ x = h₂ x) →
      ∀ x ∈ V, x ∈ GV k r → T h₁ x = T h₂ x) →
    ∀ h₁ h₂ : Mat k r → E, (∀ x ∈ V, x ∈ GV k r → h₁ x = h₂ x) →
      ∀ x ∈ V, x ∈ GV k r → L.foldr (fun T h => T h) h₁ x = L.foldr (fun T h => T h) h₂ x
  | [], _, _, _, he => by simpa using he
  | T :: L, hT, h₁, h₂, he => by
    intro x hx hxG
    simp only [List.foldr_cons]
    exact hT T (by simp) _ _ (fold_congrV V L (fun T' hT' => hT T' (by simp [hT'])) h₁ h₂ he) x hx hxG

theorem qminorOp_congr {t : ℕ} (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ) {V : Set (Mat k r)} (hV : IsOpen V)
    {f₁ f₂ : Mat k r → E} (he : ∀ x ∈ V, x ∈ GV k r → f₁ x = f₂ x) (x : Mat k r) (hx : x ∈ V)
    (hxG : x ∈ GV k r) : qminorOp (EabH (Hpk k r)) a b u f₁ x = qminorOp (EabH (Hpk k r)) a b u f₂ x := by
  unfold qminorOp
  rw [Finset.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [Pi.smul_apply]
  congr 1
  refine fold_congrV V _ ?_ f₁ f₂ he x hx hxG
  intro T hT h₁ h₂ he' y hy hyG
  obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hT
  exact top_congr' V hV _ _ _ he' y hy hyG

theorem vLet_congr (z z' : Fin (2 * r + k + 1) → ℂ) (i : ℕ) (hi : i ≤ r) (l : C.Letter) (e : Fin 2)
    {V : Set (Mat k r)} (hV : IsOpen V) {f₁ f₂ : Mat k r → E} (he : ∀ x ∈ V, x ∈ GV k r → f₁ x = f₂ x)
    (x : Mat k r) (hx : x ∈ V) (hxG : x ∈ GV k r) :
    D.vLet k r z z' i hi l e f₁ x = D.vLet k r z z' i hi l e f₂ x := by
  unfold D.vLet C3.AAop C3.AAvop
  split_ifs
  · rfl
  · congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    split_ifs
    · rw [qminorOp_congr _ _ _ hV he x hx hxG]
    · rfl
  · congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    split_ifs
    · rw [qminorOp_congr _ _ _ hV he x hx hxG]
    · rfl

theorem loc_of_smoothOnH {f : Mat k r → E} (hf : SmoothOnH (Hpk k r) f) (g : Mat k r) (hg : g ∈ GV k r) :
    Loc (⊤ : ℕ∞) f g := by
  obtain ⟨U, F, a, b, c, d⟩ := hf g hg
  exact ⟨U, F, a, b, c, d⟩

theorem bump_ext {Φ : Mat k r → E} {Dm : Set (Mat k r)} (hDm : IsOpen Dm) (hΦ : Q.SmoothLev k r 0 Dm Φ)
    {p : Mat k r} (hp : p ∈ Dm) (hpG : p ∈ GV k r) :
    ∃ V : Set (Mat k r), IsOpen V ∧ p ∈ V ∧ V ⊆ Dm ∧
      ∃ f : Mat k r → E, SmoothOnH (Hpk k r) f ∧ ∀ x ∈ V, x ∈ GV k r → f x = Φ x := by
  obtain ⟨U, F, hU, hpU, hF, hΦF⟩ := hΦ p ⟨glev0 hpG, hp⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (hU.inter hDm) p ⟨hpU, hp⟩
  let χ : ContDiffBump p := ⟨ε / 3, ε / 2, by positivity, by linarith⟩
  refine ⟨Metric.ball p (ε / 3), Metric.isOpen_ball, Metric.mem_ball_self (by positivity),
    fun x hx => (hball (Metric.ball_subset_ball (by linarith) hx)).2,
    fun x => ((χ x : ℝ) : ℂ) • F x, ?_, ?_⟩
  · intro g₀ hg₀
    by_cases hg : g₀ ∈ U
    · exact ⟨U, fun x => ((χ x : ℝ) : ℂ) • F x, hU, hg,
        ((Complex.ofRealCLM.contDiff.comp χ.contDiff).contDiffOn).smul hF, fun _ _ _ => rfl⟩
    · refine ⟨(tsupport χ)ᶜ, fun _ => 0, (isClosed_tsupport _).isOpen_compl, ?_, contDiffOn_const,
        fun x hx _ => ?_⟩
      · intro hs
        apply hg
        have h2 : g₀ ∈ Metric.closedBall p (ε / 2) := χ.tsupport_eq.subset hs
        exact (hball (Metric.closedBall_subset_ball (by linarith) h2)).1
      · have h0 : χ x = 0 := by
          by_contra h
          exact hx (subset_tsupport χ (Function.mem_support.2 h))
        simp [h0]
  · intro x hx hxG
    have h1 : χ x = 1 := χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hx)
    show ((χ x : ℝ) : ℂ) • F x = Φ x
    rw [h1, Complex.ofReal_one, one_smul]
    exact (hΦF x (hball (Metric.ball_subset_ball (by linarith) hx)).1 (glev0 hxG)).symm

theorem vLet_smul (z z' : Fin (2 * r + k + 1) → ℂ) (i : ℕ) (hi : i ≤ r) (l : C.Letter) (e : Fin 2)
    {f : Mat k r → E} (hf : SmoothOnH (Hpk k r) f) {x : Mat k r} (hx : x ∈ GV k r) (c : ℂ) :
    D.vLet k r z z' i hi l e (fun y => c • f y) x = c • D.vLet k r z z' i hi l e f x := by
  let fW : Wsm (E := E) (Set.univ : Set (Mat k r)) := ⟨f, fun g _ hgG => loc_of_smoothOnH hf g hgG⟩
  have ec : ((c • fW : Wsm (E := E) (Set.univ : Set (Mat k r))) : Mat k r → E) = fun y => c • f y := rfl
  have hA : ∀ m (hm : m ≤ r) u, C3.AAop k r m hm u (fun y => c • f y) x = c • C3.AAop k r m hm u f x := by
    intro m hm u
    have e1 := AAop_eq Set.univ isOpen_univ m hm u (c • fW) x trivial hx
    have e2 := AAop_eq Set.univ isOpen_univ m hm u fW x trivial hx
    rw [ec] at e1
    rw [e1, e2, map_smul]
    rfl
  have hAv : ∀ m (hm : m ≤ r) u, C3.AAvop k r m hm u (fun y => c • f y) x = c • C3.AAvop k r m hm u f x := by
    intro m hm u
    have e1 := AAvop_eq Set.univ isOpen_univ m hm u (c • fW) x trivial hx
    have e2 := AAvop_eq Set.univ isOpen_univ m hm u fW x trivial hx
    rw [ec] at e1
    rw [e1, e2, map_smul]
    rfl
  unfold D.vLet
  split_ifs
  · simp
  · rw [hA, smul_comm]
  · rw [hAv, smul_comm]

theorem vLet_transl (z z' : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (hz' : inWb k r z') (i : ℕ) (hi : i ≤ r)
    (l : C.Letter) (e : Fin 2) {f : Mat k r → E} (hf : SmoothOnH (Hpk k r) f) {s s' : Mat k r}
    (hs : s ∈ Sset k r z) (hs' : s' ∈ Sset k r z') {g : Mat k r} (hg : g ∈ GV k r) :
    D.vLet k r z z' i hi l e f (s * g * s') = D.vLet k r z z' i hi l e (fun x => f (s * x * s')) g := by
  have hD : ∀ l', Dmin k r z z' (s * g * s') l' = Dmin k r z z' g l' :=
    fun l' => dInv k r z z' hz hz' s hs s' hs' g l'
  have hX := fun m (hm : m ≤ r) u ell => operators_commute_translations E k r z z' m hm u ell f hz hz' hf s hs s' hs' g hg
  unfold D.vLet
  split_ifs
  · rfl
  · rw [hD, (hX _ _ _ 0).1]
  · rw [hD, (hX _ _ 0 _).2]

theorem smooth_vLet (z z' : Fin (2 * r + k + 1) → ℂ) (i : ℕ) (hi : i ≤ r) (l : C.Letter) (e : Fin 2)
    {Dm : Set (Mat k r)} (hDm : IsOpen Dm) {Φ : Mat k r → E} (hΦ : Q.SmoothLev k r 0 Dm Φ)
    (hne : ∀ g ∈ Dm, Dmin k r z z' g ⟨i, by omega⟩ ≠ 0) :
    Q.SmoothLev k r 0 Dm (D.vLet k r z z' i hi l e Φ) := by
  rintro g₀ ⟨hg₀G', hg₀D⟩
  have hg₀G : g₀ ∈ GV k r := hg₀G'.1
  obtain ⟨V, hV, hpV, hVD, f, hf, hfe⟩ := bump_ext hDm hΦ hg₀D hg₀G
  let fW : Wsm (E := E) (Sd z z' i hi) := ⟨f, fun g _ hgG => loc_of_smoothOnH hf g hgG⟩
  have hL : Loc (⊤ : ℕ∞) (D.vLet k r z z' i hi l e f) g₀ :=
    vLet_mem z z' i hi l e fW g₀ (hne g₀ hg₀D) hg₀G
  have hL2 : Loc (⊤ : ℕ∞) (D.vLet k r z z' i hi l e Φ) g₀ :=
    loc_of_eq hL hV hpV (fun x hx hxG =>
      vLet_congr z z' i hi l e hV (fun y hy hyG => (hfe y hy hyG).symm) x hx hxG)
  obtain ⟨U, F, hU, hgU, hF, hFe⟩ := hL2
  exact ⟨U, F, hU, hgU, hF, fun g hg hgl => hFe g hg hgl.1⟩

theorem one_mem_S (z : Fin (2 * r + k + 1) → ℂ) {n : Mat k r} (hn : n ∈ Nset k r) : n ∈ Sset k r z :=
  ⟨1, BigCellZetaMinors.one_uw z, n, hn, (Matrix.one_mul n).symm⟩

theorem rulesOn_vLet (k r j : ℕ) (hj : j + 1 ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (E : Type)
    [NormedAddCommGroup E] [NormedSpace ℂ E] (Dm : Set (Q.Mx k r)) (Φ : Q.Mx k r → E) (hz : inWb k r z)
    (hz' : inWb k r z') (hDm : IsOpen Dm) (hDJ : Dm ⊆ LevelPointCoordinates.domJ k r j hj z z')
    (hR : LevelPointCoordinates.RulesOn k r j hj z z' Dm Φ) (i : ℕ) (hi : i ≤ j + 1) (hij : i = j ∨ i = j + 1)
    (l : C.Letter) (e : Fin 2) :
    LevelPointCoordinates.RulesOn k r j hj z z' Dm (D.vLet k r z z' i (by omega) l e Φ) := by
  obtain ⟨hS, hRt, hLt⟩ := hR
  have hne : ∀ g ∈ Dm, Dmin k r z z' g ⟨i, by omega⟩ ≠ 0 := by
    intro g hg
    obtain ⟨h1, h2, _⟩ := hDJ hg
    rcases hij with rfl | rfl
    · exact h1
    · exact h2
  refine ⟨smooth_vLet z z' i (by omega) l e hDm hS hne, ?_, ?_⟩
  · rintro g ⟨hgG', hgD⟩ n hn
    have hgnD := (hRt g ⟨hgG', hgD⟩ n hn).1
    refine ⟨hgnD, ?_⟩
    have hgG : g ∈ GV k r := hgG'.1
    have hgnG : g * n ∈ GV k r := AAInvW.inUH_mul hgG hn.1
    obtain ⟨Va, hVa, hpa, _, fa, hfa, hfae⟩ := bump_ext hDm hS hgnD hgnG
    obtain ⟨Vb, hVb, hpb, hVbD, fb, hfb, hfbe⟩ := bump_ext hDm hS hgD hgG
    have hW : IsOpen (Vb ∩ (fun x : Mat k r => x * n) ⁻¹' Va) :=
      hVb.inter (hVa.preimage (continuous_id.matrix_mul continuous_const))
    calc D.vLet k r z z' i _ l e Φ (g * n) = D.vLet k r z z' i _ l e fa (1 * g * n) := by
          rw [Matrix.one_mul]
          exact vLet_congr z z' i _ l e hVa (fun y hy hyG => (hfae y hy hyG).symm) _ hpa hgnG
      _ = D.vLet k r z z' i _ l e (fun x => fa (1 * x * n)) g :=
          vLet_transl z z' hz hz' i _ l e hfa (one_mem_S z WeylGroupFacts.mem_n_one) (one_mem_S z' hn) hgG
      _ = D.vLet k r z z' i _ l e (fun x => psi k r z' cStd n • fb x) g := by
          refine vLet_congr z z' i _ l e hW (fun y hy hyG => ?_) g ⟨hpb, hpa⟩ hgG
          rw [Matrix.one_mul, hfae (y * n) hy.2 (AAInvW.inUH_mul hyG hn.1),
            (hRt y ⟨glev0 hyG, hVbD hy.1⟩ n hn).2, hfbe y hy.1 hyG]
      _ = psi k r z' cStd n • D.vLet k r z z' i _ l e fb g := vLet_smul z z' i _ l e hfb hgG _
      _ = psi k r z' cStd n • D.vLet k r z z' i _ l e Φ g := by
          rw [vLet_congr z z' i _ l e hVb (fun y hy hyG => hfbe y hy hyG) g hpb hgG]
  · rintro g ⟨hgG', hgD⟩ a
    have hgnD := (hLt g ⟨hgG', hgD⟩ a).1
    refine ⟨hgnD, ?_⟩
    set s := LevelPointCoordinates.nL k r j hj a with hs_def
    have hsN : s ∈ Nset k r := nL_mem j hj a
    have hgG : g ∈ GV k r := hgG'.1
    have hsgG : s * g ∈ GV k r := AAInvW.inUH_mul hsN.1 hgG
    obtain ⟨Va, hVa, hpa, _, fa, hfa, hfae⟩ := bump_ext hDm hS hgnD hsgG
    obtain ⟨Vb, hVb, hpb, hVbD, fb, hfb, hfbe⟩ := bump_ext hDm hS hgD hgG
    have hW : IsOpen (Vb ∩ (fun x : Mat k r => s * x) ⁻¹' Va) :=
      hVb.inter (hVa.preimage (continuous_const.matrix_mul continuous_id))
    calc D.vLet k r z z' i _ l e Φ (s * g) = D.vLet k r z z' i _ l e fa (s * g * 1) := by
          rw [Matrix.mul_one]
          exact vLet_congr z z' i _ l e hVa (fun y hy hyG => (hfae y hy hyG).symm) _ hpa hsgG
      _ = D.vLet k r z z' i _ l e (fun x => fa (s * x * 1)) g :=
          vLet_transl z z' hz hz' i _ l e hfa (one_mem_S z hsN) (one_mem_S z' WeylGroupFacts.mem_n_one) hgG
      _ = D.vLet k r z z' i _ l e (fun x => psi k r z cStd s • fb x) g := by
          refine vLet_congr z z' i _ l e hW (fun y hy hyG => ?_) g ⟨hpb, hpa⟩ hgG
          rw [Matrix.mul_one, hfae (s * y) hy.2 (AAInvW.inUH_mul hsN.1 hyG),
            (hLt y ⟨glev0 hyG, hVbD hy.1⟩ a).2, hfbe y hy.1 hyG]
      _ = psi k r z cStd s • D.vLet k r z z' i _ l e fb g := vLet_smul z z' i _ l e hfb hgG _
      _ = psi k r z cStd s • D.vLet k r z z' i _ l e Φ g := by
          rw [vLet_congr z z' i _ l e hVb (fun y hy hyG => hfbe y hy hyG) g hpb hgG]

end Formalism.FourierDecayAlt.P.SingleEntryHermitianProducts

namespace Formalism.FourierDecayAlt.P

theorem rules_closed : Formalism.FourierDecayAlt.P.LevelPointCoordinates.RulesClosed :=
  fun k r j hj z z' E _ _ Dm Φ hz hz' hDm hDJ hR i hi hij l e =>
    SingleEntryHermitianProducts.rulesOn_vLet k r j hj z z' E Dm Φ hz hz' hDm hDJ hR i hi hij l e

end Formalism.FourierDecayAlt.P
end
end

