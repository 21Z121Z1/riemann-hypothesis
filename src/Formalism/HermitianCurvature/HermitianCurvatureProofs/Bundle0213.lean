import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0164
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0203
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CoordinateSizesOfHypotheses
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0183
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0166
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGLet
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MulVecBvecApply
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0200
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PhiBoundPartsOfRadicalParametrisation
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SlicesFiniteRegularityBuilt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0147
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0207
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0112
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0150
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0202
import Formalism.HermitianCurvature.HermitianCurvatureProofs.QxChain
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HasFDerivAtFsvOther
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0204
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0085

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSH_SFG_PtGV
section
noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSH.SFG

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.PBH

theorem radial_embedding_mem_unitary_group {k ρ m : ℕ} (e : ρ + 1 = m) (x : U.RC k 1 ρ) : rn1 e x ∈ B.GV k m := by
  exact PBE.castM_GV e (PBE.castM_GV _ (Ux6.Rn_mem x))

private theorem mMap_mem_GV_of_isUnit_det_of_mem_GV {k j ρ : ℕ} (Z : Matrix (Fin j) (Fin j) ℂ) (hZ : IsUnit Z.det)
    (γ : B.Mat k ρ) (hγ : γ ∈ B.GV k ρ) : U.mMap k j ρ Z γ ∈ B.GV k (j + ρ) := by
  have hr : ∀ a b : Fin j, a = b.rev ↔ b = a.rev := fun a b =>
    ⟨fun h => by rw [h, Fin.rev_rev], fun h => by rw [h, Fin.rev_rev]⟩
  have hw : G.wMat j * G.wMat j = 1 := by
    ext a b
    simp only [G.wMat, Matrix.mul_apply, Matrix.one_apply, Matrix.of_apply]
    rw [Finset.sum_eq_single b.rev]
    · simp [Fin.rev_rev, Fin.rev_inj, eq_comm]
    · intro c _ hc
      rw [if_neg (fun h => hc ((hr c b).2 h))]
      simp
    · simp
  have hwh : (G.wMat j).conjTranspose = G.wMat j := by
    ext a b
    simp only [G.wMat, Matrix.conjTranspose_apply, Matrix.of_apply]
    split_ifs with h1 h2 h2 <;> simp_all [hr]
  have hZ' : IsUnit Z.conjTranspose.det := by
    rw [Matrix.det_conjTranspose]
    exact hZ.star
  have hγ' : Matrix.conjTranspose γ * Hpk k ρ * γ = Hpk k ρ := hγ
  have h1 : Z.conjTranspose * (G.wMat j).conjTranspose * G.wMat j * (Z.conjTranspose⁻¹ * G.wMat j)
      = G.wMat j := by
    rw [hwh, Matrix.mul_assoc Z.conjTranspose, hw, Matrix.mul_one, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hZ', Matrix.one_mul]
  have h3 : (G.wMat j).conjTranspose * Z.conjTranspose⁻¹.conjTranspose * G.wMat j * (G.wMat j * Z)
      = G.wMat j := by
    rw [hwh, Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc, ← Matrix.mul_assoc (G.wMat j) (G.wMat j) Z, hw, Matrix.one_mul,
      Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hZ, Matrix.mul_one]
  show Matrix.conjTranspose (U.mMap k j ρ Z γ) * Hpk k (j + ρ) * U.mMap k j ρ Z γ = Hpk k (j + ρ)
  rw [Ux6.hpkBlocks k j ρ]
  unfold U.mMap
  rw [Ux6.block3_conjTranspose, Ux6.block3_mul, Ux6.block3_mul]
  simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.conjTranspose_zero,
    Matrix.conjTranspose_mul]
  rw [h1, hγ', h3]

theorem mc_GV {k ρ m : ℕ} (e : ρ + 1 = m) {t : ℂ} (ht : t ≠ 0) {γ : B.Mat k ρ} (hγ : γ ∈ B.GV k ρ) :
    mc e t γ ∈ B.GV k m := by
  unfold mc
  refine PBE.castM_GV e (PBE.castM_GV _ (mMap_mem_GV_of_isUnit_det_of_mem_GV _ ?_ γ hγ))
  simp [Matrix.det_unique, ht]

theorem point_mem_unitary_group : PtGV := by
  intro k ρ m e t ht γ hγ xx
  unfold pt
  exact HermitianFormFactor.UH_mul (HermitianFormFactor.UH_mul (HermitianFormFactor.UH_inv (B2x5.isUnit_det_Hpk k m) (radial_embedding_mem_unitary_group e xx.1))
    (mc_GV e ht hγ)) (radial_embedding_mem_unitary_group e xx.2)

end Formalism.FourierDecayAlt.P.CutSH.SFG
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.EmbeddingMapApplyFirstBlock
section
open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.LeftFubiniLemmas

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

def NFHypL : Prop :=
  ∀ (k r : ℕ) (a : C.LPt) (hle : D.ptSize a ≤ r) (g' : B.Mat k (r - D.ptSize a)), g' ∈ B.GV k (r - D.ptSize a) →
    D.IsLocPt a (D.ptSize a) →
    levelZeroPointOver a hle g' ∈ B.GV k r ∧
    (∀ (a' : Fin r) (q : Fin (2 * r + k + 1)) (ha' : a'.val < D.ptSize a),
      PBG.xi0 (levelZeroPointOver a hle g') a' q =
        if hq : q.val < D.ptSize a then U.hMat (D.ptPerm a) (D.ptDiag a) ⟨a'.val, ha'⟩ ⟨q.val, hq⟩ else 0) ∧
    (∀ (a' : Fin r) (q : Fin (2 * r + k + 1)) (ha' : a'.val < D.ptSize a),
      PBG.y0 (levelZeroPointOver a hle g') a' q =
        if hq : r + k < q.val ∧ 2 * r + k - q.val < D.ptSize a then
          star (U.hMat (D.ptPerm a) (D.ptDiag a) ⟨a'.val, ha'⟩ ⟨2 * r + k - q.val, hq.2⟩) else 0)

theorem castM_apply' {k a b : ℕ} (h : a = b) (g : B.Mat k a) (i j : Fin (2 * b + k + 1)) :
    D.castM h g i j = g (Fin.cast (by rw [h]) i) (Fin.cast (by rw [h]) j) := rfl

theorem embedding_map_apply_last_block {k p ρ : ℕ} (Z : Matrix (Fin p) (Fin p) ℂ) (γ : B.Mat k ρ) (c : Fin p)
    (j : Fin (2 * (p + ρ) + k + 1)) :
    U.mMap k p ρ Z γ (U.eB k p ρ (Sum.inr c)) j =
      if hj : j.val < p then Z c.rev ⟨j.val, hj⟩ else 0 := by
  obtain ⟨y, rfl⟩ := (U.eB k p ρ).surjective j
  rw [U.mMap, Ux3.block3_apply]
  rcases y with (y | y) | y
  · rw [dif_pos (by rw [Ux3.block_index_first_val]; exact y.isLt)]
    simp only [Matrix.fromBlocks_apply₂₁, Matrix.fromCols_apply_inl]
    rw [Ux3.wMat_mul_apply]
    exact congrArg (Z c.rev) (Fin.ext (Ux3.block_index_first_val (k := k) (ρ := ρ) y).symm)
  · rw [dif_neg (by rw [Ux3.block_index_middle_val]; omega)]
    simp [Matrix.fromBlocks_apply₂₁, Matrix.fromCols_apply_inr]
  · rw [dif_neg (by rw [Ux3.block_index_last_val]; omega)]
    simp [Matrix.fromBlocks_apply₂₂]

theorem embedding_map_apply_first_block {k p ρ : ℕ} (Z : Matrix (Fin p) (Fin p) ℂ) (γ : B.Mat k ρ) (b : Fin p)
    (i : Fin (2 * (p + ρ) + k + 1)) :
    U.mMap k p ρ Z γ i (U.eB k p ρ (Sum.inl (Sum.inl b))) =
      if hi : p + (2 * ρ + k + 1) ≤ i.val then
        (G.wMat p * Z) ⟨i.val - (p + (2 * ρ + k + 1)), by omega⟩ b else 0 := by
  obtain ⟨y, rfl⟩ := (U.eB k p ρ).surjective i
  rw [U.mMap, Ux3.block3_apply]
  rcases y with (y | y) | y
  · rw [dif_neg (by rw [Ux3.block_index_first_val]; omega)]
    simp [Matrix.fromBlocks_apply₁₁]
  · rw [dif_neg (by rw [Ux3.block_index_middle_val]; omega)]
    simp [Matrix.fromBlocks_apply₁₁]
  · rw [dif_pos (by rw [Ux3.block_index_last_val]; omega)]
    simp only [Matrix.fromBlocks_apply₂₁, Matrix.fromCols_apply_inl]
    exact congrArg (fun c => (G.wMat p * Z) c b) (Fin.ext (by
      show (U.eB k p ρ (Sum.inr y)).val - (p + (2 * ρ + k + 1)) = y.val
      rw [Ux3.block_index_last_val]; omega)).symm

theorem normal_form_left_hypothesis : NFHypL := by
  intro k r a hle g' hg' hloc
  have hd : ∀ i, D.ptDiag a i ≠ 0 := fun i => Formalism.FourierDecayAlt.P.JCTx6.Link2.ptScal_ne a hloc.1 i i.2
  have hZ : (U.hMat (D.ptPerm a) (D.ptDiag a)).det ≠ 0 := Formalism.FourierDecayAlt.P.Ux10.det_hMat_ne _ _ hd
  have hM : U.mMap k (D.ptSize a) (r - D.ptSize a) (U.hMat (D.ptPerm a) (D.ptDiag a)) g' ∈
      B.GV k (D.ptSize a + (r - D.ptSize a)) :=
    (Formalism.FourierDecayAlt.P.slice_membership k (D.ptSize a) (r - D.ptSize a)).1 _ g' hZ hg'
  refine ⟨Formalism.FourierDecayAlt.P.PBE.castM_GV _ hM, fun a' q ha' => ?_, fun a' q ha' => ?_⟩
  · unfold PBG.xi0
    rw [Formalism.FourierDecayAlt.P.PBM.herm_bvec_eI', Formalism.FourierDecayAlt.P.PBM.mulVec_bvec_apply]
    unfold levelZeroPointOver
    rw [castM_apply']
    have hi : (Fin.cast (by omega) (esI k r a') : Fin (2 * (D.ptSize a + (r - D.ptSize a)) + k + 1)) =
        U.eB k (D.ptSize a) (r - D.ptSize a) (Sum.inr ⟨D.ptSize a - 1 - a'.val, by omega⟩) := by
      ext; rw [Ux3.block_index_last_val]; simp [esI]; omega
    rw [hi, embedding_map_apply_last_block]
    by_cases hq : q.val < D.ptSize a
    · rw [dif_pos (by simpa using hq), dif_pos hq]
      congr 1; ext; simp [Fin.val_rev]; omega
    · rw [dif_neg (by simpa using hq), dif_neg hq]
  · unfold PBG.y0
    rw [Formalism.FourierDecayAlt.P.PBM.mulVec_bvec_apply]
    have hgu : IsUnit g'.det := WeylGroupFacts.isUnit_of_uh hg'
    unfold levelZeroPointOver
    rw [← Formalism.FourierDecayAlt.P.PBH.asm_castM_inv, Formalism.FourierDecayAlt.P.PBM.mMap_inv _ _ (isUnit_iff_ne_zero.mpr hZ) hgu, castM_apply']
    have hj : (Fin.cast (by omega) (eI k r a') : Fin (2 * (D.ptSize a + (r - D.ptSize a)) + k + 1)) =
        U.eB k (D.ptSize a) (r - D.ptSize a) (Sum.inl (Sum.inl ⟨a'.val, ha'⟩)) := by
      ext; rw [Ux3.block_index_first_val]; simp [eI]
    rw [hj, embedding_map_apply_first_block]
    by_cases hq : r + k < q.val ∧ 2 * r + k - q.val < D.ptSize a
    · rw [dif_pos (by simp; omega), dif_pos hq, Ux3.wMat_mul_apply, Matrix.conjTranspose_apply]
      congr 2 <;> ext <;> simp [Fin.val_rev] <;> omega
    · rw [dif_neg (by simp; omega), dif_neg hq]

end Formalism.FourierDecayAlt.P.LeftFubiniLemmas
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadTopOfRadialExhaustion
section
noncomputable section

open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.PBI

def ExhPic : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F)
    (w : List C.Letter)
    (X : Q.ActualOps (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π')
    (μ : Measure (Mt P.k (P.r - P.r)))
    (L : R.LevelData (Q.Pr (Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z'
      (p.T.bs P.r).π (p.T.bs P.r).π')) (JC.parLev P P.r).r)
    (st : Fr.Start (Q.Pr (Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z'
      (p.T.bs P.r).π (p.T.bs P.r).π'))) (Cb : ℝ)
    (X₀ : Q.ActualOps P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π') (μ₀ : Measure (Mt P.k P.r))
    (L₀ : R.LevelData (Q.Pr (Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π')) P.r)
    (st₀ : Fr.Start (Q.Pr (Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π'))),
    P5.IsData (JC.parLev P P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π' X μ L st p.l0 →
    P5.IsData P p.T.base.z p.T.base.z' p.T.base.π p.T.base.π' X₀ μ₀ L₀ st₀ p.l0 →
    KB.IsTopLift2 P p.l0 p.T.base L₀ st₀ p.Θ →
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base F → KB.CutWord P p.l0 w →
    ∀ (e : Wd.Ix (Fin w.length)) (h : C.LPt) (hh : D.IsLocPt h P.r),
      ∃ F₁ F₂ : B.Mat P.k P.r → (Wq →L[ℂ] Wp), KB.CptCoef p.T.base F₁ ∧ KB.CptCoef p.T.base F₂ ∧
      (∀ ζ : ℂ, p.V (p.Θ.Θ w e F) (h ++ [(1, ζ)]) = p.V (p.Θ.Θ w e F₁) (h ++ [(1, ζ)])) ∧
      (∀ Φ₁ : Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π', Top.IsRadOf P p.T.base Φ₁ F₁ →
        Top.IsRadOf P p.T.base
          (P5.act ((Fr.ofWord L₀ st₀ (D.positionted w)).F * P5.bTall L₀ (D.positionted w)) (Top.firstStateVector Φ₁) e) F₂) ∧
      ∀ (Φ : Wd.Ix (Fin w.length) → Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z'
          (p.T.bs P.r).π (p.T.bs P.r).π'),
        (∀ e', Top.IsRadOf (JC.parLev P P.r) (p.T.bs P.r) (Φ e') (KB.slv p.T F P.r le_rfl w h hh.2 e')) →
        ∀ (c : Fin (JC.parLev P P.r).r → ℂ) (γ : B.Mat P.k (P.r - P.r)), γ ∈ B.GV P.k (P.r - P.r) →
          0 < Q.GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' γ →
          B.JF (p.T.bs P.r) (D.castF (by simp [hh.2]) (D.sliceAt P.k P.r p.T.base.z p.T.base.z' F₂ h)) γ =
            (P5.act (Fr.ofWord L st (D.positionted w)).F Φ e :
              Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) c γ

end Formalism.FourierDecayAlt.P.PBI

namespace Formalism.FourierDecayAlt.P

theorem exhaustion_of_radial_form : PBI.ExhPic → PBI.Exh := by
  intro hPic Wp Wq _ _ _ _ _ _ P p F w X μ L st Cb hD hdd hF hcut e h hh
  obtain ⟨X₀, μ₀, L₀, st₀, hD₀, hTL⟩ := p.hΘ
  obtain ⟨F₁, F₂, hF₁, hF₂, hloc, hpic, hii⟩ :=
    hPic Wp Wq P p F w X μ L st Cb X₀ μ₀ L₀ st₀ hD hD₀ hTL hdd hF hcut e h hh
  obtain ⟨F', hF', hagree, hVeq⟩ := theta_compact_support Wp Wq P p F₁ w e Cb hdd hF₁ hcut
  refine ⟨F₂, hF₂, fun ζ => ?_, hii⟩
  obtain ⟨Φ₁, hΦ₁⟩ := PBN.radExists p hF₁
  have hΘpic := hTL w hcut F₁ hF₁ Φ₁ hΦ₁ e
  have hF'pic := PBN.isRadOf_congr p.T.base hΘpic hagree
  rw [hloc ζ, hVeq]
  exact PBN.vecV_eq_of_rad density_constant p hF' hF₂ hF'pic (hpic Φ₁ hΦ₁) _

theorem head_top_of_radial_exhaustion (hU5 : PBI.HighestUnipotentIntegral) (hPic : PBI.ExhPic) (hW : PBI.HeadWeightAt) : KB.HeadTop :=
  head_top_of_parts hU5 (exhaustion_of_radial_form hPic) hW

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.HermSelfNeZero
section
open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JfS.Sym

noncomputable section

variable {k r : ℕ}

theorem herm_self_ne_zero {z : Fin (2 * r + k + 1) → ℂ} (hT : 0 < Tz k r z) : herm (Hpk k r) z z ≠ 0 := by
  intro h
  rw [Tz, h] at hT
  simp at hT

theorem herm_proj_zero (x z : Fin (2 * r + k + 1) → ℂ) (hc : herm (Hpk k r) z z ≠ 0) :
    herm (Hpk k r) (x - (herm (Hpk k r) x z / herm (Hpk k r) z z) • z) z = 0 := by
  rw [herm_sub_left, herm_smul_left]
  field_simp
  ring

theorem coreW {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z) (ξ : B.Mat k r)
    (h1 : ∀ u, inWb k r u → inWb k r (ξ *ᵥ u))
    (h2 : ∀ u v, inWb k r u → inWb k r v → herm (Hpk k r) (ξ *ᵥ u) v = -herm (Hpk k r) u (ξ *ᵥ v))
    (h3 : ∀ u v, inWb k r u → inWb k r v → herm (Hpk k r) u z = 0 → herm (Hpk k r) v z = 0 →
      herm (Hpk k r) (ξ *ᵥ u) v = 0)
    (N : ℕ) (h4 : ∀ u, inWb k r u → (ξ ^ N) *ᵥ u = 0) :
    ∀ u, inWb k r u → ξ *ᵥ u = 0 := by
  set c := herm (Hpk k r) z z with hcdef
  have hc0 : c ≠ 0 := herm_self_ne_zero hT

  have stepA : ∀ w, inWb k r w → herm (Hpk k r) w z = 0 →
      ξ *ᵥ w = (herm (Hpk k r) (ξ *ᵥ w) z / c) • z := by
    intro w hw hwz
    set y := ξ *ᵥ w - (herm (Hpk k r) (ξ *ᵥ w) z / c) • z with hydef
    have hy : inWb k r y := inWb_sub (h1 w hw) (inWb_smul _ hz)
    have hyz : herm (Hpk k r) y z = 0 := herm_proj_zero _ _ hc0
    have hyy : herm (Hpk k r) y y = 0 := by
      have e1 : herm (Hpk k r) (ξ *ᵥ w) y = 0 := h3 w y hw hy hwz hyz
      have e2 : herm (Hpk k r) z y = 0 := by rw [herm_swap, hyz, star_zero]
      calc herm (Hpk k r) y y
          = herm (Hpk k r) (ξ *ᵥ w) y - (herm (Hpk k r) (ξ *ᵥ w) z / c) * herm (Hpk k r) z y := by
            conv_lhs => rw [hydef]
            rw [herm_sub_left, herm_smul_left]
        _ = 0 := by rw [e1, e2]; ring
    have : y = 0 := wb_definite hz hT hy hyz (by rw [hyy]; simp)
    exact sub_eq_zero.1 this
  set μ := herm (Hpk k r) (ξ *ᵥ z) z / c with hμ
  set b := ξ *ᵥ z - μ • z with hbdef
  have hb : inWb k r b := inWb_sub (h1 z hz) (inWb_smul _ hz)
  have hbz : herm (Hpk k r) b z = 0 := herm_proj_zero _ _ hc0
  have hξz : ξ *ᵥ z = μ • z + b := by rw [hbdef]; abel

  have stepB : ∀ w, inWb k r w → herm (Hpk k r) w z = 0 →
      ξ *ᵥ w = (-(herm (Hpk k r) w b) / c) • z := by
    intro w hw hwz
    rw [stepA w hw hwz, h2 w z hw hz, hξz, herm_add_right, herm_smul_right, hwz]
    congr 1
    ring
  have hξb : ξ *ᵥ b = (-(herm (Hpk k r) b b) / c) • z := stepB b hb hbz
  have hNz := h4 z hz

  have hb0 : b = 0 := by
    by_contra hb0
    have hbb : herm (Hpk k r) b b ≠ 0 := by
      intro h
      exact hb0 (wb_definite hz hT hb hbz (by rw [h]; simp))
    set l := -(herm (Hpk k r) b b) / c with hl
    have hl0 : l ≠ 0 := div_ne_zero (neg_ne_zero.2 hbb) hc0
    let f : ℕ → ℂ × ℂ := fun m => Nat.rec (motive := fun _ => ℂ × ℂ) (1, 0)
      (fun _ pq => (μ * pq.1 + l * pq.2, pq.1)) m
    have hf0 : f 0 = (1, 0) := rfl
    have hfs : ∀ m, f (m + 1) = (μ * (f m).1 + l * (f m).2, (f m).1) := fun m => rfl
    have hpow : ∀ m, (ξ ^ m) *ᵥ z = (f m).1 • z + (f m).2 • b := by
      intro m
      induction m with
      | zero => rw [hf0, pow_zero, one_mulVec]; simp
      | succ m ih =>
        rw [pow_succ', ← mulVec_mulVec, ih, mulVec_add, mulVec_smul, mulVec_smul, hξz, hξb, hfs]
        module
    rw [hpow] at hNz
    have hp : (f N).1 = 0 := by
      have := congrArg (fun x => herm (Hpk k r) x z) hNz
      simp only [herm_add_left, herm_smul_left, hbz, herm_zero_left, mul_zero, add_zero] at this
      exact (mul_eq_zero.1 this).resolve_right hc0
    have hq : (f N).2 = 0 := by
      rw [hp, zero_smul, zero_add] at hNz
      exact (smul_eq_zero.1 hNz).resolve_right hb0
    have hnz : ∀ m, (f m).1 ≠ 0 ∨ (f m).2 ≠ 0 := by
      intro m
      induction m with
      | zero => left; rw [hf0]; exact one_ne_zero
      | succ m ih =>
        by_contra hcon
        push Not at hcon
        rw [hfs] at hcon
        obtain ⟨e1, e2⟩ := hcon
        simp only at e1 e2
        rw [e2, mul_zero, zero_add] at e1
        have : (f m).2 = 0 := (mul_eq_zero.1 e1).resolve_left hl0
        rcases ih with h | h
        · exact h e2
        · exact h this
    rcases hnz N with h | h
    · exact h hp
    · exact h hq

  have hξz' : ξ *ᵥ z = μ • z := by rw [hξz, hb0, add_zero]
  have hpow2 : ∀ m, (ξ ^ m) *ᵥ z = μ ^ m • z := by
    intro m
    induction m with
    | zero => rw [pow_zero, one_mulVec, pow_zero, one_smul]
    | succ m ih => rw [pow_succ', ← mulVec_mulVec, ih, mulVec_smul, hξz', smul_smul, pow_succ]
  rw [hpow2] at hNz
  have hμ0 : μ = 0 := by
    have := congrArg (fun x => herm (Hpk k r) x z) hNz
    simp only [herm_smul_left, herm_zero_left] at this
    exact pow_eq_zero_iff'.1 ((mul_eq_zero.1 this).resolve_right hc0) |>.1
  have hξz0 : ξ *ᵥ z = 0 := by rw [hξz', hμ0, zero_smul]
  intro u hu
  set α := herm (Hpk k r) u z / c
  have hu' : inWb k r (u - α • z) := inWb_sub hu (inWb_smul _ hz)
  have hu'z : herm (Hpk k r) (u - α • z) z = 0 := herm_proj_zero _ _ hc0
  have e : u = α • z + (u - α • z) := by abel
  rw [e, mulVec_add, mulVec_smul, hξz0, stepB _ hu' hu'z, hb0, herm_zero_right]
  simp

end

end Formalism.FourierDecayAlt.P.CutMP.JfS.Sym
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianInvariantCellAction
section
open Matrix
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

namespace Formalism.FourierDecayAlt.P.CutMP.TemperedBoundGL3

noncomputable section

variable {k r : ℕ}

def lr (hr : 1 ≤ r) : Fin r := ⟨r - 1, by omega⟩

theorem lr_succ (hr : 1 ≤ r) : (lr hr).succ = Fin.last r := Fin.ext (by simp [lr]; omega)

section Br1

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
  {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem br1 (hz : inWb k r z) (hz' : inWb k r z') {D : Set (Mx k r)} (hD : IsDom k r z z' 0 D)
    {J : Mx k r → (Wq →L[ℂ] Wp)} (hJ : J ∈ FFl k r z z' π π' 0 D) {c : Fin r → ℂ} (hc : c ∈ OmX r) (l : Fin r) :
    resG k r l.castSucc J c ∈ FFl k r z z' π π' l.castSucc (Qx6.Dcell D l.castSucc c) ∧
      IsDom k r z z' l.castSucc (Qx6.Dcell D l.castSucc c) :=
  ⟨(Formalism.FourierDecayAlt.P.restriction_good_family Wp Wq k r z z' π π' D hz hz' hD J hJ l.castSucc).2 c hc,
    Qx6.dom_Dcell Formalism.FourierDecayAlt.P.restriction_mem hz hz' hD l.castSucc c hc⟩

end Br1

theorem cell_preimage_mem_domain {D : Set (Mx k r)} {c : Fin r → ℂ} (l : Fin r) {g : Mx k r}
    (hg : wCell k r l.succ c * g ∈ D) : g ∈ Qx6.Dc1 l (Qx6.Dcell D l.castSucc c) c := by
  show wCell k r l.castSucc c * (w1 k r l (c l) * g) ∈ D
  rw [← Matrix.mul_assoc, ← Qx6.wCell_succ]
  exact hg

section Br2

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

theorem br2 (l : Fin r) (Θ : (Mx k r → X) → (Mx k r → X)) (hS : Formalism.FourierDecayAlt.P5.SmulC Θ) (c : Fin r → ℂ)
    (hL : ∀ f : Mx k r → X,
      Θ (fun x => f (wCell k r l.castSucc c * x)) = fun x => Θ f (wCell k r l.castSucc c * x))
    (J : Mx k r → X) (g : Mx k r) :
    resG k r l.succ (Θ J) c g =
      ((‖c l‖ ^ (Mdim k r l - 1) : ℝ) : ℂ) • Θ (resG k r l.castSucc J c) (w1 k r l (c l) * g) := by
  rw [Qx6.resG_succ]
  show ((‖c l‖ ^ (Mdim k r l - 1) : ℝ) : ℂ) • resG k r l.castSucc (Θ J) c (w1 k r l (c l) * g) = _
  congr 1
  have e : resG k r l.castSucc J c =
      ((Qx6.gam k r l.castSucc c : ℝ) : ℂ) • fun x => J (wCell k r l.castSucc c * x) := by
    funext x
    rfl
  rw [e, hS, hL]
  rfl

def sumQ {ι : Type} (s : Finset ι) {t : ℕ} (κ : ι → Mx k r → ℂ) (a b : ι → Fin t → Fin (2 * r + k + 1))
    (u : ι → ℂ) (f : Mx k r → X) : Mx k r → X :=
  fun x => ∑ i ∈ s, κ i x • qminorOp (EH k r) (a i) (b i) (u i) f x

theorem sumQ_smulC {ι : Type} (s : Finset ι) {t : ℕ} (κ : ι → Mx k r → ℂ)
    (a b : ι → Fin t → Fin (2 * r + k + 1)) (u : ι → ℂ) : Formalism.FourierDecayAlt.P5.SmulC (sumQ (X := X) s κ a b u) := by
  intro α f
  funext x
  simp only [sumQ, Pi.smul_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Formalism.FourierDecayAlt.P5.qminorOp_smulC (fun a b => Formalism.FourierDecayAlt.P5.eabH_smulC _ a b) (a i) (b i) (u i) α f]
  rw [Pi.smul_apply, smul_comm]

theorem sumQ_left {ι : Type} (s : Finset ι) {t : ℕ} (κ : ι → Mx k r → ℂ)
    (a b : ι → Fin t → Fin (2 * r + k + 1)) (u : ι → ℂ) (P : Mx k r) (hκ : ∀ i ∈ s, ∀ x, κ i (P * x) = κ i x)
    (f : Mx k r → X) : sumQ s κ a b u (fun x => f (P * x)) = fun x => sumQ s κ a b u f (P * x) := by
  funext x
  simp only [sumQ]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [hκ i hi x]
  congr 1
  exact congrFun (Formalism.FourierDecayAlt.P.quantum_minor_left_hermitian X _ _ (Hpk k r) f (a i) (b i) (u i) P) x

end Br2

theorem unipotent_fixes_base_vector (l : Fin r) (a : ℂ) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) :
    w1 k r l a *ᵥ z = z := by
  have hl := l.isLt
  have ze : z (eI k r l) = 0 := hz _ (Or.inl (by simp [eI]))
  have zs : z (esI k r l) = 0 := hz _ (Or.inr (by simp [esI]; omega))
  funext p
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single (Qx3.sw k l p)]
  · rw [Qx3.w1_apply, Qx3.sw_sw, if_pos rfl]
    rcases Qx3.tri l p with h | h | ⟨h1, h2⟩
    · subst h; rw [Qx3.sw_e, zs, ze, mul_zero]
    · subst h; rw [Qx3.sw_es, ze, zs, mul_zero]
    · rw [Qx3.sw_o l h1 h2, Qx3.dd_o l a h1 h2, one_mul]
  · intro q _ hq
    have : p ≠ Qx3.sw k l q := fun h => hq (by rw [h, Qx3.sw_sw])
    rw [Qx3.w1_apply, if_neg this, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem wCell_fix_wb (i : Fin (r + 1)) (c : Fin r → ℂ) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) :
    wCell k r i c *ᵥ z = z := by
  unfold wCell
  induction ((List.finRange r).filter fun a => a.val < i.val) with
  | nil => simp
  | cons a l ih => rw [List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec, ih, unipotent_fixes_base_vector a _ hz]

theorem hermitian_invariant_unipotent (l : Fin r) {a : ℂ} (ha : a ≠ 0) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z)
    (x : Mx k r) (v : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) ((w1 k r l a * x) *ᵥ v) z = herm (Hpk k r) (x *ᵥ v) z := by
  rw [← Matrix.mulVec_mulVec]
  conv_lhs => rw [← unipotent_fixes_base_vector l a hz]
  exact Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_UH (Qx3.weyl_cell_mem_unitary l ha) _ _

theorem hermitian_invariant_cell_action (i : Fin (r + 1)) {c : Fin r → ℂ} (hc : c ∈ OmX r) {z : Fin (2 * r + k + 1) → ℂ}
    (hz : inWb k r z) (x : Mx k r) (v : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) ((wCell k r i c * x) *ᵥ v) z = herm (Hpk k r) (x *ᵥ v) z := by
  rw [← Matrix.mulVec_mulVec]
  conv_lhs => rw [← wCell_fix_wb i c hz]
  exact Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_UH (Formalism.FourierDecayAlt.P.PBF.prod_w1_mem_unitary_Hpk c hc _) _ _

end

end Formalism.FourierDecayAlt.P.CutMP.TemperedBoundGL3
end

