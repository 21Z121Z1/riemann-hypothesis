import Formalism.LocalToGlobal.GlobalTheory.Bundle0006
import Formalism.LocalToGlobal.GlobalTheory.GL4.PCoordH

-- bundled from Formalism.LocalToGlobal.GlobalTheory.ColValOfTiedSOfRest
section
noncomputable section

open NumberField Matrix

namespace Formalism.L2.GlobalTheoryTheory.ColValS

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.Inhab

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem hT_self_of_on {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E)
    (b : Module.Basis (Fin S.rank) E S.V) (hb : ∀ a a', S.hT (b a) (b a') = if a = a' then 1 else 0) (y : S.V) :
    S.hT y y = ∑ a, star (b.repr y a) * b.repr y a := by
  conv_lhs => rw [← b.sum_repr y]
  simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, map_smul, hb,
    smul_eq_mul, starRingEnd_apply]
  simp [mul_ite, Finset.sum_ite_eq]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem posFrame_of_std (D : D7) (h : Formalism.L2.Herm.IsStd (D.sp.X 0)) : PosFrame D := by
  obtain ⟨b, hb, -⟩ := h
  intro σ
  refine ⟨(b.toMatrix (D.sp.X 0).frame).map σ, ?_, ?_⟩
  · haveI := b.invertibleToMatrix (D.sp.X 0).frame
    have hu : IsUnit (σ (b.toMatrix (D.sp.X 0).frame).det) :=
      (Matrix.isUnit_det_of_invertible _).map σ
    rwa [RingHom.map_det, RingHom.mapMatrix_apply] at hu
  · intro y
    have hrepr : ∀ i, ((b.toMatrix (D.sp.X 0).frame).map σ *ᵥ
        fun j => σ ((D.sp.X 0).frame.repr y j)) i = σ (b.repr y i) := by
      intro i
      rw [← (D.sp.X 0).frame.toMatrix_mulVec_repr b y, RingHom.map_mulVec]
      rfl
    simp only [hrepr]
    rw [hT_self_of_on (D.sp.X 0) b hb y, map_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_mul, host_emb_star, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

theorem colBase_of_sym {D : D7} (F : Formalism.L2.Forms.ColsTiedSym D) (u : D.what₂.Word)
    (rho : D.what₂.Tau → (D.host.E →+* D.what₂.LL)) : ∃ B : ColBase D u, B.rho = rho :=
  ColBase_exists D u (posFrame_of_std D (F.herm.std.1 0 (Nat.zero_le _))) rho

theorem colValOfTiedS_of_rest'
    (h : ∀ D : D7, Formalism.L2.Forms.ColsTiedSym D → Formalism.MainNotions.flipTwoThree.adm3 D → ∀ u : D.what₂.Word,
      ∃ rho : D.what₂.Tau → (D.host.E →+* D.what₂.LL), ∀ B : ColBase D u, B.rho = rho → ColRest B) :
    Formalism.MainNotions.RT.ColumnValuationFromTwistCompatibility := by
  refine colValOfTiedS_of_rest fun D F ha u => ?_
  obtain ⟨rho, hr⟩ := h D F ha u
  obtain ⟨B, hB⟩ := colBase_of_sym F u rho
  exact ⟨B, hr B hB⟩

end Formalism.L2.GlobalTheoryTheory.ColValS
end
end

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GramNDetNe
section
noncomputable section

open NumberField Matrix

namespace Formalism.L2.GlobalTheoryTheory.ColValS

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms Formalism.MainNotions.GlobalTheoryTheory.Inhab

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem map_inv_mat {K L : Type} [Field K] [Field L] (f : K →+* L) {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (hA : A.det ≠ 0) :
    A⁻¹.map f = (A.map f)⁻¹ := by
  refine (Matrix.inv_eq_right_inv ?_).symm
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hA), Matrix.map_one _ (map_zero f) (map_one f)]

variable {D : D7}

theorem gramN_det_ne : (gramN D 0 (Nat.zero_le _)).det ≠ 0 := by
  unfold gramN
  rw [Matrix.det_reindex_self]
  exact Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Cc.gram_det_ne (D.sp.X 0) (D.sp.X 0).frame

variable {u : D.what₂.Word} (B : ColBase D u)

theorem Mb_det_ne (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) : (Mb B c τ).det ≠ 0 := by
  intro h0
  have hY := congrArg Matrix.det (gram_Y B (InfinitePlace.mk D.what₂.embLL) c τ)
  have e1 : (Ymat B (InfinitePlace.mk D.what₂.embLL) c τ).det = 0 := by
    rw [Ymat, Matrix.det_mul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero, mul_zero]
  rw [Matrix.det_mul, e1, mul_zero, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at hY
  exact gramN_det_ne (((InfinitePlace.mk D.what₂.embLL).embedding.comp (B.rho τ)).injective (by rw [← hY, map_zero]))

def gC (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) : GL (Fin (D.R.N 0)) D.what₂.LL :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Mb B c τ * ((gramN D 0 (Nat.zero_le _)).map (B.rho τ))⁻¹) (by
    rw [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact mul_ne_zero (Mb_det_ne B c τ) (inv_ne_zero ((map_ne_zero _).2 gramN_det_ne)))

theorem gC_coe (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) :
    ((gC B c τ : GL (Fin (D.R.N 0)) D.what₂.LL) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL) =
      Mb B c τ * ((gramN D 0 (Nat.zero_le _)).map (B.rho τ))⁻¹ := rfl

def Zc (v : InfinitePlace D.what₂.LL) (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ :=
  Ymat B v c τ * ((gramN D 0 (Nat.zero_le _)).map (v.embedding.comp (B.rho τ)))⁻¹

theorem R_gC (v : InfinitePlace D.what₂.LL) (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) :
    Matrix.reindex (B.eQ c τ) (B.eQ c τ) ((B.Q c τ).X v)⁻¹ *
      ((gC B c τ : GL (Fin (D.R.N 0)) D.what₂.LL) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL).map v.embedding =
      Zc B v c τ := by
  have hd : ((gramN D 0 (Nat.zero_le _)).map (B.rho τ)).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero _).2 gramN_det_ne
  rw [gC_coe, Matrix.map_mul, map_inv_mat _ _ hd, Matrix.map_map, Zc, Ymat, Matrix.mul_assoc]
  rfl

theorem Y_det_ne (v : InfinitePlace D.what₂.LL) (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) : (Ymat B v c τ).det ≠ 0 := by
  intro h0
  have hY := congrArg Matrix.det (gram_Y B v c τ)
  rw [Matrix.det_mul, h0, mul_zero, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at hY
  exact gramN_det_ne ((v.embedding.comp (B.rho τ)).injective (by rw [← hY, map_zero]))

theorem Zc_det_ne (v : InfinitePlace D.what₂.LL) (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) : (Zc B v c τ).det ≠ 0 := by
  rw [Zc, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact mul_ne_zero (Y_det_ne B v c τ) (inv_ne_zero ((map_ne_zero _).2 gramN_det_ne))

theorem Zc_on (hB : B.rho = rhoC D) (v : InfinitePlace D.what₂.LL) (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) :
    ((Zc B v c τ)ᵀ)ᴴ * (gramN D 0 (Nat.zero_le _)).map (embS D v.embedding τ) * (Zc B v c τ)ᵀ = 1 := by
  set P := (gramN D 0 (Nat.zero_le _)).map (v.embedding.comp (B.rho τ)) with hPdef
  set Y := Ymat B v c τ
  set G' := (gramN D 0 (Nat.zero_le _)).map (embS D v.embedding τ)
  have hYP : Yᴴ * Y = P := gram_Y B v c τ
  have hGs : ∀ i j, star (gramN D 0 (Nat.zero_le _) j i) = gramN D 0 (Nat.zero_le _) i j := fun i j => by
    have := congrFun (congrFun (gramN_herm (D := D)) i) j
    rwa [Matrix.conjTranspose_apply] at this
  have hP : Pᴴ = P := by
    ext i j
    rw [Matrix.conjTranspose_apply, hPdef, Matrix.map_apply, Matrix.map_apply, ← hGs i j, RingHom.comp_apply,
      RingHom.comp_apply]
    have h1 := host_emb_star D (v.embedding.comp (B.rho τ)) (gramN D 0 (Nat.zero_le _) j i)
    simp only [RingHom.comp_apply] at h1
    rw [h1]
    rfl
  have hG' : G'ᵀ = P := by
    ext i j
    simp only [G', hPdef, Matrix.transpose_apply, Matrix.map_apply, RingHom.comp_apply]
    rw [hB, rhoC_conj, ← host_emb_star D (embS D v.embedding τ), hGs j i]
  have hdY : IsUnit Y.det := isUnit_iff_ne_zero.2 (Y_det_ne B v c τ)
  have hdYh : IsUnit Yᴴ.det := by rw [Matrix.det_conjTranspose]; exact hdY.star
  have hdP : IsUnit P.det := by rw [← hYP, Matrix.det_mul]; exact hdYh.mul hdY
  have key : Zc B v c τ * G'ᵀ * (Zc B v c τ)ᴴ = 1 := by
    rw [hG', Zc, ← hPdef, Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, hP]
    calc Y * P⁻¹ * P * (P⁻¹ * Yᴴ) = Y * (P⁻¹ * P) * P⁻¹ * Yᴴ := by simp only [Matrix.mul_assoc]
      _ = Y * P⁻¹ * Yᴴ := by rw [Matrix.nonsing_inv_mul _ hdP, Matrix.mul_one]
      _ = Y * (Y⁻¹ * (Yᴴ)⁻¹) * Yᴴ := by rw [← hYP, Matrix.mul_inv_rev]
      _ = (Y * Y⁻¹) * ((Yᴴ)⁻¹ * Yᴴ) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [Matrix.mul_nonsing_inv _ hdY, Matrix.nonsing_inv_mul _ hdYh, Matrix.mul_one]
  have ht : ((Zc B v c τ)ᵀ)ᴴ * G' * (Zc B v c τ)ᵀ = (Zc B v c τ * G'ᵀ * (Zc B v c τ)ᴴ)ᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rfl
  rw [ht, key, Matrix.transpose_one]

end Formalism.L2.GlobalTheoryTheory.ColValS
end
end

