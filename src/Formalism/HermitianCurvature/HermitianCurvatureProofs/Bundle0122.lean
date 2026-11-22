import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0115
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0110
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadCorrespondenceOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelsOfBuiltSetting
import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0116
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0113
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LowerParabolicCoordinates
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0094
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CastVMulVecLift
section
open Matrix Finset
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.DiagonalScalarMatrices

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

section lift

variable {k : ℕ}

theorem frame_lift_list {i r' m : ℕ} (vs : List (Fin (2 * r' + k + 1) → ℂ)) (Bs : Fin m → Fin (2 * r' + k + 1) → ℂ)
    (h : IsFrameOf k r' vs Bs) :
    IsFrameOf k (i + r') (vs.map (liftVec k i r')) (fun c => liftVec k i r' (Bs c)) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun a => (PI.QnLevBasicsW.level_group_isotropic_vector k i r' (Bs a) (h1 a)).1, fun a b => ?_, fun a x hx => ?_⟩
  · rw [PIQnLT.herm_liftVec]; exact h2 a b
  · obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hx
    rw [PIQnLT.herm_liftVec]
    exact h3 a v hv

theorem frame_lift_cast {i r' n m : ℕ} (hn : i + r' = n) (vs : List (Fin (2 * r' + k + 1) → ℂ))
    (Bs : Fin m → Fin (2 * r' + k + 1) → ℂ) (h : IsFrameOf k r' vs Bs) :
    IsFrameOf k n (vs.map fun v => D.castV hn (liftVec k i r' v)) (fun c => D.castV hn (liftVec k i r' (Bs c))) := by
  subst hn
  simp only [JCTx5.castV_rfl]
  exact frame_lift_list vs Bs h

theorem capRep_lift_cast {Wp : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] {i r' n m : ℕ} (hn : i + r' = n)
    (π0 : Mx k n → (Wp →L[ℂ] Wp)) (Bs : Fin m → Fin (2 * r' + k + 1) → ℂ) (w : ℂ) (v : Wp) :
    capRep k n π0 (fun c => D.castV hn (liftVec k i r' (Bs c))) w v =
      capRep k r' (fun y => π0 (D.castM hn (ιLev k i r' y))) Bs w v := by
  subst hn
  simp only [JCTx5.castV_rfl, JCTx5.castM_rfl]
  exact JCTx5.capRep_lift π0 Bs w v

theorem castV_mulVec_lift {i r' n : ℕ} (hn : i + r' = n) (M : B.Mat k r') (v : Fin (2 * r' + k + 1) → ℂ) :
    D.castM hn (ιLev k i r' M) *ᵥ D.castV hn (liftVec k i r' v) = D.castV hn (liftVec k i r' (M *ᵥ v)) := by
  subst hn
  simp only [JCTx5.castV_rfl, JCTx5.castM_rfl]
  exact PIQnLT.mulVec_liftVec M v

end lift

section types

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem tp_eigen_lev {P : M.Par} (p : KB.Pl P Wp Wq) (ν'r : Fin (2 * (P.r - P.r) + P.k + 1) → ℂ)
    (m₀r : B.Mat P.k (P.r - P.r)) (hLF : PBI.LevFrame p ν'r m₀r)
    {Bs' : Fin (P.k - 1) → Fin (2 * (P.r - P.r) + P.k + 1) → ℂ}
    (hB : IsFrameOf P.k (P.r - P.r) [(p.T.bs P.r).z', ν'r] Bs') (ρ : M.Ty P) (w : ℂ) (u : Wp) :
    capRep P.k (P.r - P.r) (p.T.bs P.r).π (fun a => m₀r *ᵥ Bs' a) w (p.TP.E ρ u) =
      M.xC P ρ (w - ((P.k : ℂ) - 2) / 2) • p.TP.E ρ u := by
  have hn : P.r + (P.r - P.r) = P.r := by omega
  obtain ⟨hν, hm, hbase⟩ := hLF
  have hB1 := Topx1.vecw_frame_fwd (p.T.bs P.r) hbase hB
  have hB2 := frame_lift_cast hn _ _ hB1
  have ez : D.castV hn (liftVec P.k P.r (P.r - P.r) (p.T.bs P.r).z) = p.T.base.z := p.T.z_lev P.r le_rfl
  have ee : D.castV hn (liftVec P.k P.r (P.r - P.r) (m₀r *ᵥ ν'r)) = p.m₀ *ᵥ p.ν' := by
    rw [← castV_mulVec_lift hn, hm, hν]
  simp only [List.map_cons, List.map_nil, ez, ee] at hB2
  have h := p.TP.eigen _ hB2 ρ w u
  rw [capRep_lift_cast hn] at h
  have hπ : (fun y => p.T.base.π (D.castM hn (ιLev P.k P.r (P.r - P.r) y))) = (p.T.bs P.r).π :=
    funext fun y => (p.T.π_lev P.r le_rfl y).symm
  rw [hπ] at h
  exact h

theorem aeval_intertwine (V : Wq →L[ℂ] Wp) (R : Module.End ℂ Wq) (Lf : Module.End ℂ Wp)
    (h : ∀ v, V (R v) = Lf (V v)) (p : Polynomial ℂ) : ∀ v, V (Polynomial.aeval R p v) = Polynomial.aeval Lf p (V v) := by
  induction p using Polynomial.induction_on with
  | C a => intro v; simp
  | add p q hp hq => intro v; simp [hp, hq]
  | monomial n a ih =>
    intro v
    have e1 : Polynomial.C a * Polynomial.X ^ (n + 1) = (Polynomial.C a * Polynomial.X ^ n) * Polynomial.X := by ring
    have eR : Polynomial.aeval R (Polynomial.C a * Polynomial.X ^ n * Polynomial.X) =
        Polynomial.aeval R (Polynomial.C a * Polynomial.X ^ n) * R := by rw [map_mul, Polynomial.aeval_X]
    have eL : Polynomial.aeval Lf (Polynomial.C a * Polynomial.X ^ n * Polynomial.X) =
        Polynomial.aeval Lf (Polynomial.C a * Polynomial.X ^ n) * Lf := by rw [map_mul, Polynomial.aeval_X]
    rw [e1, eR, eL, Module.End.mul_apply, Module.End.mul_apply, ih, h]

theorem aeval_eigen (Lf : Module.End ℂ Wp) (x : Wp) (c : ℂ) (h : Lf x = c • x) (p : Polynomial ℂ) :
    Polynomial.aeval Lf p x = p.eval c • x := by
  induction p using Polynomial.induction_on with
  | C a => simp [Algebra.algebraMap_eq_smul_one]
  | add p q hp hq => simp [hp, hq, add_smul]
  | monomial n a ih =>
    have e1 : Polynomial.C a * Polynomial.X ^ (n + 1) = (Polynomial.C a * Polynomial.X ^ n) * Polynomial.X := by ring
    have eL : Polynomial.aeval Lf (Polynomial.C a * Polynomial.X ^ n * Polynomial.X) =
        Polynomial.aeval Lf (Polynomial.C a * Polynomial.X ^ n) * Lf := by rw [map_mul, Polynomial.aeval_X]
    have ev : (Polynomial.C a * Polynomial.X ^ n * Polynomial.X).eval c =
        (Polynomial.C a * Polynomial.X ^ n).eval c * c := by rw [Polynomial.eval_mul, Polynomial.eval_X]
    rw [e1, eL, Module.End.mul_apply, h, map_smul, ih, smul_smul, ev, mul_comm]

theorem poly_types {P : M.Par} (p : KB.Pl P Wp Wq) (ν'r : Fin (2 * (P.r - P.r) + P.k + 1) → ℂ)
    (m₀r : B.Mat P.k (P.r - P.r)) (hLF : PBI.LevFrame p ν'r m₀r)
    {Bs' : Fin (P.k - 1) → Fin (2 * (P.r - P.r) + P.k + 1) → ℂ}
    (hB : IsFrameOf P.k (P.r - P.r) [(p.T.bs P.r).z', ν'r] Bs') (V : Wq →L[ℂ] Wp)
    (hV : PBI.GrpInt (p.T.bs P.r) ν'r m₀r V) (hex : ∑ ρ : M.Ty P, (p.TP.E ρ).comp V = V)
    (Y₀ : ℂ) (q : Polynomial ℂ) (v : Wq) :
    V (Polynomial.aeval (qdet (Qr.EB (p.T.bs P.r).π' Bs') (Y₀ + ((P.k : ℂ) - 2) / 2)) q v) =
      ∑ ρ : M.Ty P, q.eval (M.xC P ρ Y₀) • p.TP.E ρ (V v) := by
  set S := p.T.bs P.r
  have hbase := hLF.2.2
  have hBz' : IsFrameOf P.k (P.r - P.r) [S.z'] Bs' :=
    Topx1.vecw_frame_sub (fun v hv => by simp at hv; simp [hv]) hB
  have hBz : IsFrameOf P.k (P.r - P.r) [S.z] (fun a => m₀r *ᵥ Bs' a) :=
    Topx1.vecw_frame_sub (fun v hv => by simp at hv; simp [hv]) (Topx1.vecw_frame_fwd S hbase hB)
  have hglR := Formalism.FourierDecayAlt.P.frame_general_linear Wq P.k (P.r - P.r) (P.k - 1) S.z' S.π' Bs' ⟨S.π'_rep, S.π'_cont⟩ hBz'
  have hglL := Formalism.FourierDecayAlt.P.frame_general_linear Wp P.k (P.r - P.r) (P.k - 1) S.z S.π (fun a => m₀r *ᵥ Bs' a)
    ⟨S.π_rep, S.π_cont⟩ hBz
  set w0 : ℂ := Y₀ + ((P.k : ℂ) - 2) / 2
  have hint : ∀ v, V (qdet (Qr.EB S.π' Bs') w0 v) = qdet (Qr.EB S.π (fun a => m₀r *ᵥ Bs' a)) w0 (V v) := by
    intro v
    rw [← hglR.2, ← hglL.2]
    exact (PBI.gen_capRep_intertwine S hbase V hV hB w0 v).symm
  rw [aeval_intertwine V _ _ hint q v]
  conv_lhs => rw [← hex]
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.comp_apply, map_sum]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  refine aeval_eigen _ _ _ ?_ q
  rw [← hglL.2, tp_eigen_lev p ν'r m₀r hLF hB ρ w0 (V v)]
  congr 2
  ring

end types

end Formalism.FourierDecayAlt.P.DiagonalScalarMatrices
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CptCoefContSupp
section
noncomputable section

open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CompactCoefficientAppend

section coef

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem cptCoef_cont_supp (Bs : B.RealPlaceData k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (hF : KB.CptCoef Bs F) :
    ContinuousOn F (B.GV k r) ∧ ∃ R : ℝ, ∀ g ∈ B.GV k r, F g ≠ 0 → B.gN g ≤ R :=
  ⟨Formalism.FourierDecayAlt.P.B5.ckOn_continuousOn hF.1, hF.2.1⟩

end coef

section point

theorem cast_perm_val {m n : ℕ} (e : m = n) (σ : Equiv.Perm (Fin m)) (x : Fin n) :
    ((e ▸ σ) x).val = (σ (Fin.cast e.symm x)).val := by
  subst e; rfl

theorem cast_diag_apply {m n : ℕ} (e : m = n) (d : Fin m → ℂ) (x : Fin n) :
    (e ▸ d) x = d (Fin.cast e.symm x) := by
  subst e; rfl

theorem ptSize_app (h : C.LPt) (n : ℕ) (hh : D.IsLocPt h n) (ζ : ℂ) : D.ptSize (h ++ [(1, ζ)]) = n + 1 := by
  rw [Formalism.FourierDecayAlt.P.Dx2.SL.ptSize_append, hh.2]

theorem perm_app (h : C.LPt) (n : ℕ) (hh : D.IsLocPt h n) (ζ : ℂ) (hζ : ζ ≠ 0) :
    U.hMat (hh.2 ▸ D.ptPerm h) (hh.2 ▸ D.ptDiag h) = D.ptMatN h n ∧ (∀ a, (hh.2 ▸ D.ptDiag h) a ≠ 0) ∧
    D.ptMatN (h ++ [(1, ζ)]) (n + 1) =
      C2.monoP (ptSize_app h n hh ζ ▸ D.ptPerm (h ++ [(1, ζ)])) (ptSize_app h n hh ζ ▸ D.ptDiag (h ++ [(1, ζ)])) ∧
    (∀ a, (ptSize_app h n hh ζ ▸ D.ptDiag (h ++ [(1, ζ)])) a ≠ 0) ∧
    (∀ a : Fin n, (ptSize_app h n hh ζ ▸ D.ptPerm (h ++ [(1, ζ)])).symm a.castSucc =
      ((hh.2 ▸ D.ptPerm h) a).castSucc) := by
  have hq : D.IsLocPt (h ++ [(1, ζ)]) (n + 1) := Formalism.FourierDecayAlt.P.PBI.isLocPt_app h n hh ζ hζ
  obtain ⟨h1, h2⟩ := Formalism.FourierDecayAlt.P.Dx2.VV.ptMatN_monoP' h n hh.2 hh.1
  obtain ⟨h3, h4⟩ := Formalism.FourierDecayAlt.P.Dx2.VV.ptMatN_monoP' (h ++ [(1, ζ)]) (n + 1) (ptSize_app h n hh ζ) hq.1
  refine ⟨?_, h2, h3, h4, ?_⟩
  · rw [h1]
    refine (Formalism.FourierDecayAlt.P.Dx1.monomialMatrix_eq_hMat _ _ ?_).symm
    intro a
    apply Fin.ext
    have e : Fin.cast hh.2.symm ((hh.2 ▸ D.ptPerm h) a) = D.ptPerm h (Fin.cast hh.2.symm a) :=
      Fin.ext (by rw [Fin.val_cast, cast_perm_val])
    rw [cast_perm_val, e, Formalism.FourierDecayAlt.P.Dx1.ptPerm_invol, Fin.val_cast]
  · intro a
    rw [Equiv.symm_apply_eq]
    apply Fin.ext
    have hs := hh.2
    have hb := ((hh.2 ▸ D.ptPerm h) a).isLt
    rw [cast_perm_val, Formalism.FourierDecayAlt.P.Dx1.ptPerm_val, Formalism.FourierDecayAlt.P.Dx2.SL.partner_append 1 ζ h _ (by
      simp only [Fin.val_cast, Fin.val_castSucc]; omega)]
    rw [if_pos (by simp only [Fin.val_cast, Fin.val_castSucc]; omega)]
    simp only [Fin.val_cast, Fin.val_castSucc]
    rw [cast_perm_val]
    have e1 := Formalism.FourierDecayAlt.P.Dx1.ptPerm_val h (D.ptPerm h (Fin.cast hh.2.symm a))
    rw [Formalism.FourierDecayAlt.P.Dx1.ptPerm_invol] at e1
    rw [← e1, Fin.val_cast]

end point

section frame

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem baseFrame_last (p : KB.Pl P Wp Wq) (ν'r : Fin (2 * (P.r - P.r) + P.k + 1) → ℂ) (m₀r : B.Mat P.k (P.r - P.r))
    (hν : D.castV (by omega) (liftVec P.k P.r (P.r - P.r) ν'r) = p.ν')
    (hm : D.castM (by omega) (ιLev P.k P.r (P.r - P.r) m₀r) = p.m₀) :
    D.IsBaseFrame (p.T.bs P.r) ν'r m₀r := by
  have h : P.r + (P.r - P.r) = P.r := by omega
  have e1 : ν'r = Formalism.FourierDecayAlt.P.PBI.nuR p := by
    rw [Formalism.FourierDecayAlt.P.PBI.nuR, ← hν, Formalism.FourierDecayAlt.P.PBI.zL_lift]
  have e2 : m₀r = Formalism.FourierDecayAlt.P.PBI.m0R p := by
    ext i j
    rw [Formalism.FourierDecayAlt.P.PBI.m0R, ← hm]
    simp only [D.castM, Matrix.reindex_apply, Matrix.submatrix_apply, ιLev]
    rw [dif_pos (by simp; omega), dif_pos (by simp; omega)]
    congr 1 <;> ext <;> simp
  rw [e1, e2]
  exact (Formalism.FourierDecayAlt.P.PBI.levFrame_nuR p).2.2

end frame

end Formalism.FourierDecayAlt.P.CompactCoefficientAppend
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXMTA
section
noncomputable section

open Matrix
open scoped ComplexOrder

namespace Formalism.FourierDecayAlt.P.CutEXMT

open Formalism.FourierDecayAlt

variable {n : ℕ}

theorem sum_lt_castLE {j : ℕ} (hj : j ≤ n) (f : Fin n → ℂ) :
    ∑ i : Fin n, (if i.val < j then f i else 0) = ∑ b : Fin j, f (Fin.castLE hj b) := by
  rw [← Finset.sum_filter]
  have e : (Finset.univ.filter fun i : Fin n => i.val < j) = Finset.univ.map (Fin.castLEEmb hj) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Fin.castLEEmb_apply]
    constructor
    · intro h; exact ⟨⟨i.val, h⟩, Fin.ext rfl⟩
    · rintro ⟨b, rfl⟩; simp
  rw [e, Finset.sum_map]
  rfl

def gram (Z : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := Zᴴ * Z

def blkJ (A : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) : Matrix (Fin j) (Fin j) ℂ :=
  Matrix.of fun a b => A (Fin.castLE j.isLt.le a) (Fin.castLE j.isLt.le b)

def colJ (A : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) : Fin j → ℂ := fun a => A (Fin.castLE j.isLt.le a) j

def Wm (Z : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j =>
  if h : i.val < j.val then -(((blkJ (gram Z) j)⁻¹ *ᵥ colJ (gram Z) j) ⟨i.val, h⟩) else if i = j then 1 else 0

theorem Wm_ut (Z : Matrix (Fin n) (Fin n) ℂ) : Wm Z ∈ C2.UTset n := by
  refine ⟨fun i j h => ?_, fun i => ?_⟩
  · simp only [Wm, Matrix.of_apply]
    rw [dif_neg (by have : j.val < i.val := h; omega), if_neg (by intro e; rw [e] at h; exact lt_irrefl _ h)]
  · simp [Wm]

theorem mul_col_split (A V : Matrix (Fin n) (Fin n) ℂ) (hV : V ∈ C2.UTset n) (l j : Fin n) :
    (A * V) l j = ∑ b : Fin j, A l (Fin.castLE j.isLt.le b) * V (Fin.castLE j.isLt.le b) j + A l j := by
  rw [Matrix.mul_apply, ← sum_lt_castLE j.isLt.le (fun i => A l i * V i j)]
  have hsplit : ∀ i : Fin n, A l i * V i j = (if i.val < j.val then A l i * V i j else 0) +
      (if i = j then A l j else 0) := by
    intro i
    rcases lt_trichotomy i.val j.val with h | h | h
    · rw [if_pos h, if_neg (by intro e; rw [e] at h; exact lt_irrefl _ h), add_zero]
    · have e : i = j := Fin.ext h
      subst e
      rw [if_neg (lt_irrefl _), if_pos rfl, hV.2, mul_one, zero_add]
    · rw [if_neg (by omega), if_neg (by intro e; rw [e] at h; exact lt_irrefl _ h), hV.1 i j h, mul_zero, add_zero]
  rw [Finset.sum_congr rfl fun i _ => hsplit i, Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

theorem blk_gram_eq (Z : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) :
    blkJ (gram Z) j = (Matrix.of fun a (b : Fin j) => Z a (Fin.castLE j.isLt.le b))ᴴ *
      Matrix.of fun a (b : Fin j) => Z a (Fin.castLE j.isLt.le b) := by
  ext a b
  simp [blkJ, gram, Matrix.mul_apply, Matrix.conjTranspose_apply]

theorem blk_det_ne {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : Z.det ≠ 0) (j : Fin n) : (blkJ (gram Z) j).det ≠ 0 := by
  rw [blk_gram_eq]
  refine (Matrix.PosDef.det_pos (Matrix.PosDef.conjTranspose_mul_self _ ?_)).ne'
  intro x y hxy
  set ex : (Fin j → ℂ) → Fin n → ℂ := fun x l => if h : l.val < j.val then x ⟨l.val, h⟩ else 0 with hex
  have hm : ∀ x : Fin j → ℂ, (Matrix.of fun a (b : Fin j) => Z a (Fin.castLE j.isLt.le b)) *ᵥ x = Z *ᵥ ex x := by
    intro x
    ext a
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
    set f : Fin n → ℂ := fun l => Z a l * ex x l with hf
    calc ∑ b : Fin j, Z a (Fin.castLE j.isLt.le b) * x b = ∑ b : Fin j, f (Fin.castLE j.isLt.le b) := by
          refine Finset.sum_congr rfl fun b _ => ?_
          simp only [hf, hex, Fin.val_castLE, dif_pos b.isLt]
      _ = ∑ l : Fin n, (if l.val < j.val then f l else 0) := (sum_lt_castLE _ f).symm
      _ = ∑ l : Fin n, f l := by
          refine Finset.sum_congr rfl fun l _ => ?_
          by_cases h : l.val < j.val
          · rw [if_pos h]
          · rw [if_neg h]; simp only [hf, hex, dif_neg h, mul_zero]
  rw [hm, hm] at hxy
  have hinj : Function.Injective (Z *ᵥ ·) := Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det Z).mpr (isUnit_iff_ne_zero.mpr hZ))
  have := hinj hxy
  funext a
  have h2 := congrFun this (Fin.castLE j.isLt.le a)
  simp only [hex, Fin.val_castLE, dif_pos a.isLt] at h2
  exact h2

theorem Wm_spec {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : Z.det ≠ 0) (l j : Fin n) (hlj : l.val < j.val) :
    (gram Z * Wm Z) l j = 0 := by
  rw [mul_col_split _ _ (Wm_ut Z)]
  have hBc : blkJ (gram Z) j *ᵥ ((blkJ (gram Z) j)⁻¹ *ᵥ colJ (gram Z) j) = colJ (gram Z) j := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (blk_det_ne hZ j)), Matrix.one_mulVec]
  have hrow := congrFun hBc ⟨l.val, hlj⟩
  simp only [Matrix.mulVec, dotProduct, blkJ, colJ, Matrix.of_apply] at hrow
  have hl : Fin.castLE j.isLt.le ⟨l.val, hlj⟩ = l := Fin.ext rfl
  rw [hl] at hrow
  have hW : ∀ b : Fin j, Wm Z (Fin.castLE j.isLt.le b) j =
      -(((blkJ (gram Z) j)⁻¹ *ᵥ colJ (gram Z) j) b) := by
    intro b
    simp only [Wm, Matrix.of_apply, Fin.val_castLE, dif_pos b.isLt, Fin.eta]
  simp only [hW, mul_neg, Finset.sum_neg_distrib]
  rw [show ∑ x : Fin j, gram Z l (Fin.castLE j.isLt.le x) * ((blkJ (gram Z) j)⁻¹ *ᵥ colJ (gram Z) j) x =
      gram Z l j from hrow]
  ring

theorem Wm_unique {Z V : Matrix (Fin n) (Fin n) ℂ} (hZ : Z.det ≠ 0) (hV : V ∈ C2.UTset n)
    (hlow : ∀ l j : Fin n, l.val < j.val → (gram Z * V) l j = 0) : V = Wm Z := by
  ext i j
  rcases lt_trichotomy i.val j.val with h | h | h
  · have hu : IsUnit (blkJ (gram Z) j).det := isUnit_iff_ne_zero.mpr (blk_det_ne hZ j)
    set x : Fin j → ℂ := fun b => V (Fin.castLE j.isLt.le b) j with hx
    have hB : blkJ (gram Z) j *ᵥ x = -colJ (gram Z) j := by
      ext a
      have h0 := hlow (Fin.castLE j.isLt.le a) j (by simp [a.isLt])
      rw [mul_col_split _ _ hV] at h0
      simp only [Matrix.mulVec, dotProduct, blkJ, colJ, Matrix.of_apply, hx, Pi.neg_apply]
      linear_combination h0
    have hx' : x = -((blkJ (gram Z) j)⁻¹ *ᵥ colJ (gram Z) j) := by
      have e : x = (blkJ (gram Z) j)⁻¹ *ᵥ (blkJ (gram Z) j *ᵥ x) := by
        rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
      rw [e, hB, Matrix.mulVec_neg]
    have h1 := congrFun hx' ⟨i.val, h⟩
    simp only [hx, Pi.neg_apply] at h1
    rw [show Fin.castLE j.isLt.le ⟨i.val, h⟩ = i from Fin.ext rfl] at h1
    rw [h1]
    simp only [Wm, Matrix.of_apply, dif_pos h]
  · have e : i = j := Fin.ext h
    subst e
    rw [hV.2, (Wm_ut Z).2]
  · rw [hV.1 i j h, (Wm_ut Z).1 i j h]

theorem gram_mul (Z u : Matrix (Fin n) (Fin n) ℂ) : gram (Z * u) = uᴴ * gram Z * u := by
  simp only [gram, Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem Wm_mul {Z u : Matrix (Fin n) (Fin n) ℂ} (hZ : Z.det ≠ 0) (hu : u ∈ C2.UTset n) :
    Wm (Z * u) = u⁻¹ * Wm Z := by
  have hZu : (Z * u).det ≠ 0 := by rw [Matrix.det_mul, C2x2.ut_det hu, mul_one]; exact hZ
  refine (Wm_unique hZu (C2x2.ut_mul (C2x2.ut_inv hu) (Wm_ut Z)) ?_).symm
  intro l j hlj
  rw [gram_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ (C2x2.ut_unit hu), Matrix.mul_assoc,
    Matrix.mul_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases hi : i.val ≤ l.val
  · rw [Wm_spec hZ i j (by omega), mul_zero]
  · rw [Matrix.conjTranspose_apply, hu.1 i l (by show l.val < i.val; omega), star_zero, zero_mul]

def Sm (Z : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := (Wm Z).adjugate

theorem Sm_eq_inv (Z : Matrix (Fin n) (Fin n) ℂ) : Sm Z = (Wm Z)⁻¹ := by
  rw [Sm, Matrix.inv_def, C2x2.ut_det (Wm_ut Z), Ring.inverse_one, one_smul]

theorem Sm_ut (Z : Matrix (Fin n) (Fin n) ℂ) : Sm Z ∈ C2.UTset n := by
  rw [Sm_eq_inv]; exact C2x2.ut_inv (Wm_ut Z)

theorem Sm_mul {Z u : Matrix (Fin n) (Fin n) ℂ} (hZ : Z.det ≠ 0) (hu : u ∈ C2.UTset n) :
    Sm (Z * u) = Sm Z * u := by
  rw [Sm_eq_inv, Sm_eq_inv, Wm_mul hZ hu, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ (C2x2.ut_unit hu)]

theorem Wm_mul_Sm (Z : Matrix (Fin n) (Fin n) ℂ) : Wm Z * Sm Z = 1 := by
  rw [Sm_eq_inv]; exact Matrix.mul_nonsing_inv _ (C2x2.ut_unit (Wm_ut Z))

end Formalism.FourierDecayAlt.P.CutEXMT
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGQQSSFCut
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.GQ

noncomputable section

def GQBridge : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    2 ≤ P.k → ∀ (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    ActHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), Gauge.IsFrameB P Bs e → GQQ P Bs e →
    ∀ (Y : ℝ) (a b : Fin 2), Gauge.GC.Intw P Bs e (X.QQ (Y : ℂ) a b) (MA.QQr P (MA.DQ P) (Y : ℂ) a b)

def GQKap : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    2 ≤ P.k → ∀ (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    ActHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), Gauge.IsFrameB P Bs e →
    (∀ (Y : ℝ) (a b : Fin 2), Gauge.GC.Intw P Bs e (d.QQ (Y : ℂ) a b) (MA.QQr P (MA.DQ P) (Y : ℂ) a b)) →
    ∀ f : M.Ty P → ℂ, Gauge.GC.Intw P Bs e (d.κ f) (MA.kap P (MA.DQ P) f)

def GQSS : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    2 ≤ P.k → ∀ (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    ActHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), Gauge.IsFrameB P Bs e →
    (∀ (Y : ℝ) (a b : Fin 2), Gauge.GC.Intw P Bs e (d.QQ (Y : ℂ) a b) (MA.QQr P (MA.DQ P) (Y : ℂ) a b)) →
    (∀ f : M.Ty P → ℂ, Gauge.GC.Intw P Bs e (d.κ f) (MA.kap P (MA.DQ P) f)) →
    ∀ l ∈ Finset.Icc 1 (P.k - 1),
      Gauge.GC.Intw P Bs e (d.SS l) (MA.SS P (MA.DQ P) l) ∧
      Gauge.GC.Intw P Bs e (star (d.SS l)) (star (MA.SS P (MA.DQ P) l))

def GQQSSFOfCut : Prop := GQBridge → GQKap → GQSS → GQQSSF

theorem gQQSSF_of_cut : GQQSSFOfCut := by
  intro hB hK hS Wp Wq _ _ _ _ _ _ P Bs hk X d hA e he hg
  have hQ : ∀ (Y : ℝ) (a b : Fin 2), Gauge.GC.Intw P Bs e (d.QQ (Y : ℂ) a b) (MA.QQr P (MA.DQ P) (Y : ℂ) a b) := by
    intro Y a b
    rw [← hA.2.2.2.2 (Y : ℂ)]
    exact hB Wp Wq P Bs hk X d hA e he hg Y a b
  have hκ := hK Wp Wq P Bs hk X d hA e he hQ
  intro l hl Φ
  exact ⟨(hS Wp Wq P Bs hk X d hA e he hQ hκ l hl).1 Φ, (hS Wp Wq P Bs hk X d hA e he hQ hκ l hl).2 Φ⟩

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.GQ
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRCPDecompDefs
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP.Dc

open Formalism.FourierDecayAlt.P.B2x3 Formalism.FourierDecayAlt.P.SettingConstruction Formalism.FourierDecayAlt.P.TheSec Formalism.FourierDecayAlt.B2

noncomputable section

abbrev Mb (k : ℕ) := Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ

def e0 (k r : ℕ) (X : Mb k) : Q.Mx k r := Em k r * X * (Em k r)ᵀ

def dnu (k : ℕ) (a b c : ℂ) : Mb k :=
  a • Matrix.single 0 0 1 + b • (Matrix.single 0 (Fin.last k) 1 + Matrix.single (Fin.last k) 0 1) +
    c • Matrix.single (Fin.last k) (Fin.last k) 1

def kap (T T' : ℝ) : ℂ := ((Real.sqrt T * Real.sqrt T' : ℝ) : ℂ)

def nuI (k : ℕ) (T T' : ℝ) (ζ : ℂ) : Mb k := nu k (star (wZ T T' ζ)) (-sZ T T' ζ)

def H1 (k : ℕ) (T T' : ℝ) (ζ : ℂ) : Mb k :=
  nuI k T T' ζ * dnu k 0 ((2 * kap T T')⁻¹ * conj ζ * (sig (T * T') ζ)⁻¹) (-(kap T T')⁻¹)

def H2 (k : ℕ) (T T' : ℝ) (ζ : ℂ) : Mb k :=
  nuI k T T' ζ * dnu k (-(kap T T')⁻¹) ((2 * kap T T')⁻¹ * ζ * (sig (T * T') ζ)⁻¹) 0

def InL (k : ℕ) (C : Mb k) : Prop := ∀ i, C i (Fin.last k) = 0 ∧ C (Fin.last k) i = 0

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP.Dc
end

