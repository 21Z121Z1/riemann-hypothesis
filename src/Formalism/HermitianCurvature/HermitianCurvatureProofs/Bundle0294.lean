import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0292
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0227
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0247
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0219
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0252
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0112
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SlicesFiniteRegularityBuilt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsAdmissibleSplittingCharPairMulTwist

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSPOp
section
open MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Help

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem rdsp_rw_vanish {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (F : B.Mat k r → E) (w : List (B.Mat k r)) :
    ∀ g, g ∉ tsupport F → B.Rw w F g = 0 := by
  intro g hg
  rw [Formalism.FourierDecayAlt.P.JCTx6.Pos.rw_congr_open (isClosed_tsupport F).isOpen_compl (f₁ := F) (f₂ := 0)
    (fun x hx => image_eq_zero_of_notMem_tsupport hx) w g hg, Formalism.FourierDecayAlt.P.CutMP.JA.GA.rw_zero_fn]
  rfl

theorem rdsp_tsupport_sub {E E' : Type*} [Zero E] [Zero E'] {G : B.Mat k r → E} {F : B.Mat k r → E'}
    (h : ∀ g, g ∉ tsupport F → G g = 0) : tsupport G ⊆ tsupport F := by
  apply closure_minimal _ (isClosed_tsupport F)
  intro g hg
  by_contra hc
  exact hg (h g hc)

variable [FiniteDimensional ℂ Wq]

theorem rdsp_opApply_vanishP (Θ : B.DiffOp k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) :
    ∀ g, g ∉ tsupport F → B.opApply Θ F g = 0 := by
  have hz : ∀ x ∈ (tsupport F)ᶜ, F x = 0 := by
    intro x hx
    by_contra hne
    exact hx (subset_tsupport F (Function.mem_support.mpr hne))
  intro g hg
  unfold Formalism.FourierDecayAlt.B.opApply
  have h0 : ∀ T ∈ Θ, T.coef g (B.Rw T.word F g) = 0 := by
    intro T _
    rw [Formalism.FourierDecayAlt.P.Ux8.Rw_vanish (isClosed_tsupport F).isOpen_compl hz T.word g hg, map_zero]
  first
    | (apply List.sum_eq_zero
       intro x hx
       obtain ⟨T, hT, rfl⟩ := List.mem_map.mp hx
       exact h0 T hT)
    | (apply Multiset.sum_eq_zero
       intro x hx
       obtain ⟨T, hT, rfl⟩ := Multiset.mem_map.mp hx
       exact h0 T hT)

theorem rdsp_opAdj_vanishP (Θ : B.DiffOp k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) :
    ∀ g, g ∉ tsupport F → B.opAdj Θ F g = 0 := by
  have hz : ∀ x ∈ (tsupport F)ᶜ, F x = 0 := by
    intro x hx
    by_contra hne
    exact hx (subset_tsupport F (Function.mem_support.mpr hne))
  intro g hg
  unfold Formalism.FourierDecayAlt.B.opAdj
  have h0 : ∀ T ∈ Θ, ((-1 : ℂ) ^ T.word.length) • B.Rw T.word.reverse (fun x => T.coefAdj x (F x)) g = 0 := by
    intro T _
    have hz' : ∀ x ∈ (tsupport F)ᶜ, T.coefAdj x (F x) = 0 := by
      intro x hx
      rw [hz x hx, map_zero]
    rw [Formalism.FourierDecayAlt.P.Ux8.Rw_vanish (isClosed_tsupport F).isOpen_compl hz' T.word.reverse g hg, smul_zero]
  first
    | (apply List.sum_eq_zero
       intro x hx
       obtain ⟨T, hT, rfl⟩ := List.mem_map.mp hx
       exact h0 T hT)
    | (apply Multiset.sum_eq_zero
       intro x hx
       obtain ⟨T, hT, rfl⟩ := Multiset.mem_map.mp hx
       exact h0 T hT)

end Help

theorem spectral_pairing_operator : RDSPOp := by
  intro k r Wp Wq _ _ _ _ _ _ D Θ hS hC F hF hFc hFO
  have hOP : tsupport F ⊆ B.GPos D := fun g hg => ⟨(hFO hg).1, (hFO hg).2.2⟩
  have hsuppF : B.SuppIn (B.GPos D) F :=
    (closure_mono (fun g hg => hg.2)).trans ((closure_minimal subset_closure (isClosed_tsupport F)).trans hOP)
  have hA1t : tsupport (B.opApply Θ F) ⊆ tsupport F := rdsp_tsupport_sub (rdsp_opApply_vanishP Θ F)
  have hB1t : tsupport (B.opAdj Θ F) ⊆ tsupport F := rdsp_tsupport_sub (rdsp_opAdj_vanishP Θ F)
  have hA1s : B.CkOn ⊤ (B.GV k r) (B.opApply Θ F) := by
    refine Formalism.FourierDecayAlt.P.PBJ.ckOn_opApply_list (B.GPos D) F hF hsuppF Θ (fun T hT => (hS T hT).1) fun T _ => ?_
    refine (closure_minimal (fun g hg => ?_) (isClosed_tsupport F)).trans hOP
    by_contra hgF
    exact hg.2 (rdsp_rw_vanish F T.word g hgF)
  have hB1s : B.CkOn ⊤ (B.GV k r) (B.opAdj Θ F) := Formalism.FourierDecayAlt.P.CutMP.JA.FFS.AC.ckOn_opAdj D Θ hS hF hsuppF
  refine ⟨⟨hA1s, hFc.of_isClosed_subset (isClosed_tsupport _) hA1t, hA1t⟩,
    ⟨hB1s, hFc.of_isClosed_subset (isClosed_tsupport _) hB1t, hB1t⟩, ?_⟩

  have hpos : ∃ ε : ℝ, 0 < ε ∧ ∀ g ∈ tsupport F, ε ≤ Formalism.QuantumDeterminants.Gf k r D.z D.z' g := by
    rcases (tsupport F).eq_empty_or_nonempty with h | h
    · exact ⟨1, one_pos, by simp [h]⟩
    · obtain ⟨g₀, hg₀, hmin⟩ := hFc.exists_isMinOn h (Formalism.FourierDecayAlt.P.PositiveOrbitOpen.gf_cont D.z D.z').continuousOn
      exact ⟨_, (hFO hg₀).2.2, fun g hg => isMinOn_iff.mp hmin g hg⟩
  obtain ⟨ε, hε, hεG⟩ := hpos
  have hCk : B.CkOn ⊤ (JF.Om k r D.z D.z') (B.JF D F) :=
    (radial_orbital_niceness k r Wp Wq D F ⟨ε, hε, hF, fun A m => Formalism.FourierDecayAlt.P.JFxG.cptInCC_G hF hFc
      (fun g _ hg => image_eq_zero_of_notMem_tsupport hg) A m,
      fun g _ hg => hεG g (subset_tsupport F hg)⟩).2
  have hIn := Formalism.FourierDecayAlt.P.JFxG.cptInCC_G hF hFc (fun g _ hg => image_eq_zero_of_notMem_tsupport hg)
    (6 * (r : ℝ) * (B.opOrder Θ : ℝ) + (r : ℝ) * (4 * (r : ℝ) + 2 * (k : ℝ)) * (6 * (r : ℝ) + 1) + 1) (B.opOrder Θ)
  obtain ⟨hT1, hT2⟩ := Formalism.FourierDecayAlt.P.CutMP.JA.LT.thetaJ_of_adjComm Formalism.FourierDecayAlt.P.CutMP.JA.FFS.adjoint_commutation_holds k r Wp Wq D Θ _ F
    (JF.Om k r D.z D.z') (Formalism.FourierDecayAlt.P.CutMP.JA.SA.thrW_sa k r (B.opOrder Θ)) hS hC hF hIn subset_rfl
    (Formalism.FourierDecayAlt.P.B5.ckOn_mono le_top hCk)
  exact fun g hg => ⟨hT1 g hg, hT2 g hg⟩

end Formalism.FourierDecayAlt.P.CutSE
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSRhvR
section
open MeasureTheory
open scoped Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

namespace RhvRPf

open RhRPf

theorem pbOp_loc {r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (l : Fin r)
    {f₁ f₂ : (Fin r → ℂ) → E} (h : ∀ c ∈ OmX r, f₁ c = f₂ c) {c : Fin r → ℂ} (hc : c ∈ OmX r) :
    pbOp l f₁ c = pbOp l f₂ c := by
  have hev : f₁ =ᶠ[nhds c] f₂ := by
    filter_upwards [(Formalism.FourierDecayAlt.P.Qx3.isOpen_OmX r).mem_nhds hc] with c' hc' using h c' hc'
  simp only [pbOp, wirtBar, if_pos hc, hev.fderiv_eq]

theorem vABs_loc {r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (Y : ℂ) :
    ∀ (i : ℕ) (f₁ f₂ : (Fin r → ℂ) → E), (∀ c ∈ OmX r, f₁ c = f₂ c) →
      ∀ c ∈ OmX r, (vABs r Y i).1 f₁ c = (vABs r Y i).1 f₂ c ∧ (vABs r Y i).2 f₁ c = (vABs r Y i).2 f₂ c
  | 0, f₁, f₂, h, c, hc => ⟨h c hc, rfl⟩
  | i + 1, f₁, f₂, h, c, hc => by
    by_cases hi : i < r
    · simp only [vABs, dif_pos hi]
      have hsub : ∀ c' ∈ OmX r, (Y • f₁ - pbOp ⟨i, hi⟩ f₁) c' = (Y • f₂ - pbOp ⟨i, hi⟩ f₂) c' := by
        intro c' hc'
        simp only [Pi.sub_apply, Pi.smul_apply]
        rw [h c' hc', pbOp_loc _ h hc']
      have hcb : ∀ c' ∈ OmX r, cbOp ⟨i, hi⟩ f₁ c' = cbOp ⟨i, hi⟩ f₂ c' := by
        intro c' hc'
        simp only [cbOp]
        rw [h c' hc']
      have hcbi : ∀ c' ∈ OmX r, cbiOp ⟨i, hi⟩ f₁ c' = cbiOp ⟨i, hi⟩ f₂ c' := by
        intro c' hc'
        simp only [cbiOp]
        rw [h c' hc']
      refine ⟨?_, ?_⟩
      · simp only [Pi.sub_apply]
        rw [(vABs_loc Y i _ _ hsub c hc).1, (vABs_loc Y i _ _ hcb c hc).2]
      · exact (vABs_loc Y i _ _ hcbi c hc).1
    · simp only [vABs, dif_neg hi]
      exact vABs_loc Y i f₁ f₂ h c hc

def rowP {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ} (L : R.LevelData A r) (Y : ℂ) (n : ℕ) :
    Matrix (Fin 2) (Fin 2) A :=
  ((List.ofFn fun l => (L.Tvl Y l)ᵀ).take n).prod

theorem partialProduct_succ {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ} (L : R.LevelData A r) (Y : ℂ) (n : ℕ) (h : n < r) :
    rowP L Y (n + 1) = rowP L Y n * (L.Tvl Y ⟨n, h⟩)ᵀ := by
  unfold rowP
  rw [List.take_add_one, List.prod_append]
  have e : (List.ofFn fun l => (L.Tvl Y l)ᵀ)[n]? = some ((L.Tvl Y ⟨n, h⟩)ᵀ) := by simp [h]
  rw [e]
  simp

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem rowSide_chain (X : ActualOps k r z z' π π') (L : R.LevelData (Pr (RadSp k r z z' π π')) r)
    (hL : IsActualLevel X L) (Y : ℂ) :
    ∀ n, n ≤ r → ∀ (Ψ : RadSp k r z z' π π'), ∀ x ∈ DomR k r z z',
      (((rowP L Y n 0 0).1 Ψ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 =
          crd (vABs r Y n).1 (Ψ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 ∧
        (((rowP L Y n 0 1).1 Ψ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 =
          crd (vABs r Y n).2 (Ψ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2
  | 0, _, Ψ, x, _ => by
    have e : rowP L Y 0 = 1 := by simp [rowP]
    rw [e]
    refine ⟨rfl, ?_⟩
    simp [vABs, crd, fst_zero_apply]
  | n + 1, hn, Ψ, x, hx => by
    have h : n < r := by omega
    have ih := rowSide_chain X L hL Y n (by omega)
    have ev : vABs (E := Wq →L[ℂ] Wp) r Y (n + 1) =
        (fun f => (vABs r Y n).1 (Y • f - pbOp ⟨n, h⟩ f) - (vABs r Y n).2 (cbOp ⟨n, h⟩ f),
          fun f => (vABs r Y n).1 (cbiOp ⟨n, h⟩ f)) := by
      show (if h : n < r then _ else _) = _
      rw [dif_pos h]
    have e00 : rowP L Y (n + 1) 0 0 =
        rowP L Y n 0 0 * (algebraMap ℂ _ Y - L.pb ⟨n, h⟩) + rowP L Y n 0 1 * (-L.cb ⟨n, h⟩) := by
      rw [partialProduct_succ L Y n h]
      simp [Matrix.mul_apply, Fin.sum_univ_two, R.LevelData.Tvl]
    have e01 : rowP L Y (n + 1) 0 1 = rowP L Y n 0 0 * L.cbi ⟨n, h⟩ := by
      rw [partialProduct_succ L Y n h]
      simp [Matrix.mul_apply, Fin.sum_univ_two, R.LevelData.Tvl]
    have hpb : (L.pb ⟨n, h⟩).1 = X.op ⟨n, h⟩ 3 := by rw [hL.2.1]; rfl
    have hcb : (L.cb ⟨n, h⟩).1 = X.op ⟨n, h⟩ 4 := by rw [hL.2.2.2.2.1]; rfl
    have hcbi : (L.cbi ⟨n, h⟩).1 = X.op ⟨n, h⟩ 5 := by rw [hL.2.2.2.2.2.1]; rfl
    refine ⟨?_, ?_⟩
    · have h1 : (((rowP L Y (n + 1) 0 0).1 Ψ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 =
          (((rowP L Y n 0 0).1 (Y • Ψ - X.op ⟨n, h⟩ 3 Ψ) : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 -
            (((rowP L Y n 0 1).1 (X.op ⟨n, h⟩ 4 Ψ) : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 := by
        rw [e00]
        simp only [fst_add_apply, fst_mul_apply, fst_sub_apply, fst_neg_apply, fst_algebraMap_apply, hpb, hcb,
          map_neg, ← sub_eq_add_neg, Submodule.coe_sub, Pi.sub_apply]
      rw [h1, (ih _ x hx).1, (ih _ x hx).2, ev]
      simp only [Submodule.coe_sub, Submodule.coe_smul, X.op_apply]
      rfl
    · have h1 : (((rowP L Y (n + 1) 0 1).1 Ψ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 =
          (((rowP L Y n 0 0).1 (X.op ⟨n, h⟩ 5 Ψ) : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 := by
        rw [e01, fst_mul_apply, hcbi]
      rw [h1, (ih _ x hx).1, ev]
      simp only [X.op_apply]
      rfl

end RhvRPf

open RhRPf RhvRPf in
theorem spectral_adjoint_rho_action : RDSRhvR := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 hD hl1 hl2 hr Y hY
  obtain ⟨_, _, hL, hQQ, -⟩ := hD
  refine ⟨M.sgn P l0, ?_⟩
  intro J hJ Φ hΦ x hx
  have hT : (L.Tvprod Y)ᵀ = rowP L Y P.r := by
    rw [Formalism.FourierDecayAlt.P.MAx3.Q.Tvprod_transpose L Y, rowP, List.take_of_length_le (by simp)]
  have eA : L.Avr Y = rowP L Y P.r 0 0 := by rw [← hT]; rfl
  have eB : L.Bvr Y = rowP L Y P.r 0 1 := by rw [← hT]; rfl
  have hch := rowSide_chain X L hL Y P.r le_rfl
  have hA : ∀ y ∈ Glev P.k P.r (Fin.last P.r) ∩ Qx8.Dp P.k P.r z z',
      (((L.Avr Y).1 Φ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 y =
        crd (Q.cmp (vABs P.r Y P.r) 0) (resG P.k P.r (Fin.last P.r) J) x.1 y := by
    intro y hy
    have hxy : (x.1, y) ∈ DomR P.k P.r z z' := ⟨hx.1, hy.1, hy.2⟩
    rw [eA, (hch Φ (x.1, y) hxy).1]
    simp only [crd, Q.cmp, if_true]
    exact (vABs_loc Y P.r _ _ (fun c' hc' => hΦ (c', y) ⟨hc', hy.1, hy.2⟩) x.1 hx.1).1
  have hB : ∀ y ∈ Glev P.k P.r (Fin.last P.r) ∩ Qx8.Dp P.k P.r z z',
      (((L.Bvr Y).1 Φ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 y =
        crd (Q.cmp (vABs P.r Y P.r) 1) (resG P.k P.r (Fin.last P.r) J) x.1 y := by
    intro y hy
    have hxy : (x.1, y) ∈ DomR P.k P.r z z' := ⟨hx.1, hy.1, hy.2⟩
    rw [eB, (hch Φ (x.1, y) hxy).2]
    simp only [crd, Q.cmp, if_neg (show (1 : Fin 2) ≠ 0 by decide)]
    exact (vABs_loc Y P.r _ _ (fun c' hc' => hΦ (c', y) ⟨hc', hy.1, hy.2⟩) x.1 hx.1).2
  have e1 : (((RhvR L st Y).1 Φ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 =
      (((L.Dr).1 ((st.QQ Y 0 1).1 ((L.Avr Y).1 Φ) + (st.QQ Y 1 1).1 ((L.Bvr Y).1 Φ)) :
        RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 := rfl
  rw [e1, dr_apply X L hL, st_fst X st l0 hQQ, st_fst X st l0 hQQ]
  simp only [CutMP.dMul, CutMP.rhvGrp, Submodule.coe_add, Pi.add_apply, LinearMap.smul_apply,
    Submodule.coe_smul, Pi.smul_apply, QL, grp]
  rw [X.t_apply Y 0 1 _ x hx, X.t_apply Y 1 1 _ x hx,
    t_slice_congr X Y 0 1 _ _ x hx hA, t_slice_congr X Y 1 1 _ _ x hx hB]
  simp only [smul_add, smul_comm (CutMP.drF P.r x.1) (M.sgn P l0)]

end Formalism.FourierDecayAlt.P.CutSE
end
end

