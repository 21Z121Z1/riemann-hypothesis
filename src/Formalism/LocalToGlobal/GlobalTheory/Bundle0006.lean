import Formalism.LocalToGlobal.GlobalTheory.Bundle0005
import Formalism.LocalToGlobal.GlobalTheory.LevelZeroClassLatticeIntegral
import Formalism.LocalToGlobal.HermitianForms.Bundle0006
import Formalism.SharpRestriction.GlobalSchurBounds.StandardIntegralLatticeExists
import Formalism.LocalToGlobal.HermitianForms.FormsTied

-- bundled from Formalism.LocalToGlobal.GlobalTheory.ClassesLevelZeroNonempty
section
noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.L2.GlobalTheoryTheory.ColValS

open Formalism.UG Formalism.UG.CS Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Herm Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.Comp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem class_lattice_eq_global {D : D7} (Lv : LevelData D) (u : D.what₂.Word) (c : (D.mem u).C.cls 0) :
    (K0 D).lat (D.clsLat u 0 c) = globLat ((Lv u).y c).1 (Lv u).Lb :=
  eq_glob_of_hat ((K0 D).isLat_lat (D.clsLat_lat u 0 c)) _ (fun v => by exact (Lv u).y_lat c v)

theorem Lb_le_dl_lv {D : D7} (Lv : LevelData D) (u : D.what₂.Word) :
    (Lv u).Lb ≤ dl D.sp.cm.sig (K0 D).J (Lv u).Lb := by
  intro x hx
  exact Submodule.subset_span ((Lv u).Lb_int x hx)

theorem class_lattice_integral {D : D7} (Lv : LevelData D) (u : D.what₂.Word) (c : (D.mem u).C.cls 0) :
    D.clsLat u 0 c ≤ Formalism.HermitianLatticesTheory.dual (D.sp.X 0).hT (D.clsLat u 0 c) := by
  have h1 : (K0 D).lat (D.clsLat u 0 c) ≤ (K0 D).lat (Formalism.HermitianLatticesTheory.dual (D.sp.X 0).hT (D.clsLat u 0 c)) := by
    rw [(K0 D).lat_dual, class_lattice_eq_global Lv u c]
    exact le_trans (glob_mono _ (Lb_le_dl_lv Lv u)) (glob_dl_le _ _ _ _ (by exact ((Lv u).y c).2))
  intro x hx
  have h2 := h1 ⟨x, hx, rfl⟩
  rw [(K0 D).mem_lat] at h2
  simpa using h2

theorem latT_of_sym {D : D7} (F : Formalism.L2.Forms.ColsTiedSym D) (u : D.what₂.Word) (c : (D.mem u).C.cls 0) :
    flipTwoThree.LatT (D.sp.X 0) (flipTwoThree.Tu D u ^ (2 * D.R.f)) (D.clsLat u 0 c) := by
  refine ⟨fun x hx => ?_, ?_⟩
  · rw [dualSub_eq]
    exact class_lattice_integral F.herm.base.lev0 u c hx
  · obtain ⟨e⟩ := (F.herm.atT u).disc 0 (Nat.zero_le _) c
    rw [dualSub_eq, AddSubgroup.relIndex, ← card_ringOfIntegers_quot_natCast_eq_pow D (flipTwoThree.Tu D u)]
    have := Nat.card_congr e.toEquiv
    have hT : flipTwoThree.Tu D u = (D.mem u).A.T := rfl
    rw [hT, ← this]
    rfl

theorem classes_level_zero_nonempty {D : D7} (F : Formalism.L2.Forms.ColsTiedSym D) (u : D.what₂.Word) :
    Nonempty ((D.mem u).C.cls 0) := by
  obtain ⟨c, -⟩ := (F.herm.base.lev0 u).y_bij.2 (Quotient.mk'' 1)
  exact ⟨c⟩

def ColRest {D : D7} {u : D.what₂.Word} (B : Formalism.MainNotions.GlobalTheoryTheory.Inhab.ColBase D u) : Prop :=
  ∃ co : ((D.fm u).lat 0).V →ₗ[D.what₂.LL]
      ((D.mem u).C.cls 0 → MvPolynomial (D.what₂.Tau × Fin (D.R.N 0) × Fin (D.R.N 0)) D.what₂.LL),
    Function.Injective co ∧
    (∀ F, (∃ x, co x = F) ↔ ∀ c, F c ∈ flipTwoThree.TSpan D.what₂.LL ((D.fm u).lam 0)) ∧
    (∀ w : D.what₂.places.Pl, ∃ γ : (D.mem u).C.cls 0 → D.what₂.Tau → Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL,
      (∀ c τ, flipTwoThree.LocBasis D w (B.Q c τ) (B.eQ c τ) (γ c τ)) ∧
      ∀ x, x ∈ locW D.what₂.places w ((D.fm u).lat 0).L ↔
        ∀ c, flipTwoThree.actAll ((D.fm u).lam 0) (fun τ => (γ c τ)⁻¹) (co x c) ∈ flipTwoThree.IntSpanAt D w ((D.fm u).lam 0)) ∧
    ∀ (v : NumberField.InfinitePlace D.what₂.LL) x,
      (Formalism.HermitianLatticesTheory.majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x x).re =
        ∑ c, (flipTwoThree.nfAll ((D.fm u).lam 0)
          (flipTwoThree.actAll ((D.fm u).lam 0) (fun τ => Matrix.reindex (B.eQ c τ) (B.eQ c τ) ((B.Q c τ).X v)⁻¹)
            (MvPolynomial.map v.embedding (co x c)))
          (flipTwoThree.actAll ((D.fm u).lam 0) (fun τ => Matrix.reindex (B.eQ c τ) (B.eQ c τ) ((B.Q c τ).X v)⁻¹)
            (MvPolynomial.map v.embedding (co x c)))).re

theorem colValOfTiedS_of_rest
    (h : ∀ D : D7, Formalism.L2.Forms.ColsTiedSym D → flipTwoThree.adm3 D →
      ∀ u : D.what₂.Word, ∃ B : Formalism.MainNotions.GlobalTheoryTheory.Inhab.ColBase D u, ColRest B) :
    Formalism.MainNotions.RT.ColumnValuationFromTwistCompatibility :=
  column_value_of_tie_local_bases fun D F h3 u => by
    obtain ⟨B, co, h1, h2, h3', h4⟩ := h D F h3 u
    exact ⟨B, classes_level_zero_nonempty F u, latT_of_sym F u, co, h1, h2, h3', h4⟩

end Formalism.L2.GlobalTheoryTheory.ColValS
end
end

-- bundled from Formalism.LocalToGlobal.GlobalTheory.SigDEqStar
section
noncomputable section

open NumberField Matrix

namespace Formalism.L2.GlobalTheoryTheory.ColValS

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms Formalism.MainNotions.GlobalTheoryTheory.Inhab

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem sigD_eq_star (a : D.host.E) : sigD D a = star a := rfl

def rhoC (D : D7) (τ : D.what₂.Tau) : D.host.E →+* D.what₂.LL :=
  D.embE.comp ((sigD D : D.host.E →+* D.host.E).comp
    (D.host.sigmaOf (D.eTau τ : D.R.GG) : D.host.E →+* D.host.E))

theorem rhoC_conj (s : D.what₂.LL →+* ℂ) (τ : D.what₂.Tau) (a : D.host.E) :
    s (rhoC D τ a) = starRingEnd ℂ (embS D s τ a) := by
  unfold rhoC embS
  simp only [RingHom.coe_comp, Function.comp_apply]
  have hs : ∀ b : D.host.E, (sigD D : D.host.E →+* D.host.E) b = star b := fun b => sigD_eq_star b
  rw [hs]
  first
    | exact NumberField.IsCMField.complexEmbedding_complexConj (s.comp D.embE) _
    | exact NumberField.IsCMField.complexEmbedding_complexConj _ (s.comp D.embE) _
    | (erw [NumberField.IsCMField.complexEmbedding_complexConj]; rfl)
    | exact (NumberField.IsCMField.complexEmbedding_complexConj (K := D.host.E) (φ := s.comp D.embE) _)
    | (simp only [NumberField.IsCMField.complexEmbedding_star]; rfl)
    | exact NumberField.IsCMField.complexEmbedding_star _ (s.comp D.embE) _
    | exact NumberField.IsCMField.complexConj_apply_apply (s.comp D.embE) _
    | exact (NumberField.IsCMField.complexEmbedding_complexConj (s.comp D.embE) _ : _)

theorem exists_im_ne (φ : D.host.E →+* ℂ) : ∃ t : D.host.E, (φ t).im ≠ 0 := by
  by_contra h
  push_neg at h
  have hr : NumberField.ComplexEmbedding.IsReal φ := by
    first
      | (rw [NumberField.ComplexEmbedding.isReal_iff]; ext t; simp [Complex.conj_eq_iff_im, h t])
      | (intro t; simp [Complex.conj_eq_iff_im, h t])
      | (ext t; simp [Complex.conj_eq_iff_im, h t])
  have hc : (NumberField.InfinitePlace.mk φ).IsComplex := by
    first
      | exact NumberField.IsTotallyComplex.isComplex _
      | exact IsTotallyComplex.isComplex _
      | exact NumberField.InfinitePlace.IsTotallyComplex.isComplex _
  exact (NumberField.InfinitePlace.isComplex_mk_iff.mp hc) hr

def crd (y : (D.sp.X 0).V) : Fin (D.R.N 0) → D.host.E :=
  fun i => (D.sp.X 0).frame.repr y ((finCongr (rankN D 0 (Nat.zero_le _))).symm i)

theorem gramN_herm : (gramN D 0 (Nat.zero_le _))ᴴ = gramN D 0 (Nat.zero_le _) := by
  unfold gramN
  rw [Matrix.conjTranspose_reindex]
  congr 1
  first
    | exact (D.sp.X 0).gram_isHermitian
    | exact (D.sp.X 0).isHermitian_gram
    | exact (D.sp.X 0).gram_herm
    | exact (D.sp.X 0).gram_conjTranspose
    | exact (D.sp.X 0).herm
    | (ext i j; exact (D.sp.X 0).herm _ _)
    | (ext i j; exact (D.sp.X 0).herm.eq _ _)
    | (ext i j; exact LinearMap.IsSymm.eq (D.sp.X 0).herm _ _)

theorem hT_crd (y : (D.sp.X 0).V) :
    (D.sp.X 0).hT y y = star (crd y) ⬝ᵥ (gramN D 0 (Nat.zero_le _) *ᵥ crd y) := by
  unfold crd gramN
  have hy := (D.sp.X 0).frame.sum_repr y
  conv_lhs => rw [← hy]
  simp only [map_sum, LinearMap.map_smulₛₗ, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply]
  simp only [dotProduct, Matrix.mulVec, Matrix.reindex_apply, Matrix.submatrix_apply, Pi.star_apply, Finset.mul_sum]
  rw [← (finCongr (rankN D 0 (Nat.zero_le _))).sum_comp]
  simp only [Equiv.symm_apply_apply]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [← (finCongr (rankN D 0 (Nat.zero_le _))).sum_comp]
  simp only [Equiv.symm_apply_apply, Formalism.BasicNotions.HSpace.gram]
  apply Finset.sum_congr rfl
  intro l _
  first
    | ring1
    | (clear hy; generalize ((D.sp.X 0).frame.repr y) k = a; generalize ((D.sp.X 0).frame.repr y) l = b; generalize (D.sp.X 0).hT ((D.sp.X 0).frame k) ((D.sp.X 0).frame l) = h1; generalize (D.sp.X 0).hT ((D.sp.X 0).frame l) ((D.sp.X 0).frame k) = h2; done)

variable {u : D.what₂.Word} (B : ColBase D u)

def Mb (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL :=
  fun j i => (B.Q c τ).b.repr (B.bc c τ ((D.sp.X 0).frame ((finCongr (rankN D 0 (Nat.zero_le _))).symm i)))
    ((B.eQ c τ).symm j)

theorem repr_bc (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) (y : (D.sp.X 0).V) (j : Fin (D.R.N 0)) :
    (B.Q c τ).b.repr (B.bc c τ y) ((B.eQ c τ).symm j) = (Mb B c τ *ᵥ fun i => B.rho τ (crd y i)) j := by
  unfold Mb crd
  conv_lhs => rw [← (D.sp.X 0).frame.sum_repr y]
  simp only [map_sum, B.bc_smul, LinearMap.map_smulₛₗ, map_smulₛₗ, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, RingHom.id_apply]
  rw [← (finCongr (rankN D 0 (Nat.zero_le _))).sum_comp]
  simp only [Equiv.symm_apply_apply]
  apply Finset.sum_congr rfl
  intro k _
  first
    | ring1
    | (simp only [RingHom.id_apply]; ring1)
    | (rw [mul_comm]; rfl)
    | done

def Ymat (v : InfinitePlace D.what₂.LL) (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) :
    Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ :=
  Matrix.reindex (B.eQ c τ) (B.eQ c τ) ((B.Q c τ).X v)⁻¹ * (Mb B c τ).map v.embedding

theorem fcoord_bc (v : InfinitePlace D.what₂.LL) (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) (y : (D.sp.X 0).V)
    (j : Fin (D.R.N 0)) :
    Formalism.HermitianLatticesTheory.fcoord (B.Q c τ).b (B.Q c τ).X v (B.bc c τ y) ((B.eQ c τ).symm j) =
      (Ymat B v c τ *ᵥ fun i => v.embedding (B.rho τ (crd y i))) j := by
  have hv : (fun i => v.embedding (B.rho τ (crd y i))) = fun i => v.embedding (B.rho τ (crd y i)) := rfl
  rw [Ymat, ← Matrix.mulVec_mulVec]
  unfold Formalism.HermitianLatticesTheory.fcoord Formalism.HermitianLatticesTheory.vecAt
  rw [Matrix.mulVec, Matrix.mulVec, dotProduct, dotProduct, ← (B.eQ c τ).symm.sum_comp]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [repr_bc, RingHom.map_mulVec]
  rfl

theorem maj_bc (v : InfinitePlace D.what₂.LL) (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) (y : (D.sp.X 0).V) :
    Formalism.HermitianLatticesTheory.majAt (B.Q c τ).b (B.Q c τ).X v (B.bc c τ y) (B.bc c τ y) =
      star (Ymat B v c τ *ᵥ fun i => v.embedding (B.rho τ (crd y i))) ⬝ᵥ
        (Ymat B v c τ *ᵥ fun i => v.embedding (B.rho τ (crd y i))) := by
  unfold Formalism.HermitianLatticesTheory.majAt
  rw [← (B.eQ c τ).symm.sum_comp]
  simp only [fcoord_bc]
  first
    | rfl
    | simp [dotProduct]
    | simp [Matrix.dotProduct]

theorem gram_Y (v : InfinitePlace D.what₂.LL) (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) :
    (Ymat B v c τ)ᴴ * Ymat B v c τ = (gramN D 0 (Nat.zero_le _)).map (v.embedding.comp (B.rho τ)) := by
  obtain ⟨t, ht⟩ := exists_im_ne (v.embedding.comp (B.rho τ))
  refine gram_of_norm (v.embedding.comp (B.rho τ)) (host_emb_star D _) _ _ gramN_herm t ht fun x => ?_
  let y : (D.sp.X 0).V := (D.sp.X 0).frame.equivFun.symm fun a => x (finCongr (rankN D 0 (Nat.zero_le _)) a)
  have hy : crd y = x := by
    funext i
    show (D.sp.X 0).frame.repr y _ = _
    rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    simp
  have h := B.bc_norm c τ v y
  rw [maj_bc, hT_crd, hy] at h
  exact h

end Formalism.L2.GlobalTheoryTheory.ColValS
end
end

