import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0023
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.SpanPerpZero
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.VolumeIndexBStable

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NinfConjIff
section
noncomputable section

open scoped Classical ComplexConjugate
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.KappaOffDiagonal

open Matrix

namespace Formalism.L2.SG.CovariantRepresentation

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Mat

variable {n r : ℕ}

theorem hJ_unitary (ε : Fin n → Bool) (P : Matrix (Fin n) (Fin n) ℂ) (hU : Pᴴ * Formalism.REAL.Jm ε * P = Formalism.REAL.Jm ε)
    (x y : Fin n → ℂ) : hJ ε (P *ᵥ x) (P *ᵥ y) = hJ ε x y := by
  delta hJ
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hU]

theorem fix_span (e : Fin r → Fin n → ℂ) (Q : Matrix (Fin n) (Fin n) ℂ) (he : ∀ a, Q *ᵥ e a = e a) (k : ℕ) :
    ∀ x ∈ spanLt e k, Q *ᵥ x = x := by
  delta spanLt
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, -, rfl⟩ := hy
    exact he a
  | zero => exact Matrix.mulVec_zero Q
  | add y z _ _ hy hz => rw [Matrix.mulVec_add, hy, hz]
  | smul c y _ hy => rw [Matrix.mulVec_smul, hy]

theorem inN_conj (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (P Q g : Matrix (Fin n) (Fin n) ℂ)
    (hQP : Q * P = 1) (hU : Pᴴ * Formalism.REAL.Jm ε * P = Formalism.REAL.Jm ε) (he : ∀ a, P *ᵥ e a = e a) (hz : P *ᵥ z = z)
    (hg : InN ε e z g) : InN ε e z (Q * g * P) := by
  have hQv' : ∀ v, Q *ᵥ (P *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, hQP, Matrix.one_mulVec]
  have hQv : ∀ v, P *ᵥ v = v → Q *ᵥ v = v := fun v hv =>
    calc Q *ᵥ v = Q *ᵥ (P *ᵥ v) := by rw [hv]
      _ = v := hQv' v
  have hQe : ∀ a, Q *ᵥ e a = e a := fun a => hQv (e a) (he a)
  have key : ∀ (v : Fin n → ℂ) (k : ℕ), P *ᵥ v = v → (g - 1) *ᵥ v ∈ spanLt e k →
      (Q * g * P - 1) *ᵥ v ∈ spanLt e k := by
    intro v k hv hw
    have h : (Q * g * P - 1) *ᵥ v = Q *ᵥ ((g - 1) *ᵥ v) := by
      rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
        ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_sub, hQv v hv]
    rw [h, fix_span e Q hQe k _ hw]
    exact hw
  obtain ⟨⟨h1a, h1b⟩, h2⟩ := hg
  refine ⟨⟨fun a => key (e a) a (he a) (h1a a), key z r hz h1b⟩, fun y hy => ?_⟩
  have hy' : ∀ a, hJ ε (e a) (P *ᵥ y) = 0 := fun a =>
    calc hJ ε (e a) (P *ᵥ y) = hJ ε (P *ᵥ e a) (P *ᵥ y) := by rw [he a]
      _ = hJ ε (e a) y := hJ_unitary ε P hU (e a) y
      _ = 0 := hy a
  have hw := h2 (P *ᵥ y) hy'
  have h : (Q * g * P - 1) *ᵥ y = Q *ᵥ ((g - 1) *ᵥ (P *ᵥ y)) := by
    rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.one_mulVec,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_sub, hQv' y]
  rw [h, fix_span e Q hQe r _ hw]
  exact hw

end Mat

section Grp

variable {D : D7} (X : HidaSetting D)

theorem fix_inv (s : X.B.I.Ginf) {v : InfinitePlace X.B.I.F} {x : Fin X.B.I.n → ℂ} (hx : uMat (s v) *ᵥ x = x) :
    uMat (s⁻¹ v) *ᵥ x = x := by
  have h1 : uMat (s⁻¹ v) * uMat (s v) = 1 := by
    delta uMat
    simp
  calc uMat (s⁻¹ v) *ᵥ x = uMat (s⁻¹ v) *ᵥ (uMat (s v) *ᵥ x) := by rw [hx]
    _ = x := by rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]

theorem ninf_conj (u : D.what₂.Word) (s : X.B.I.Ginf)
    (he : ∀ v a, uMat (s v) *ᵥ rv X.B.I v (X.eR a) = rv X.B.I v (X.eR a))
    (hz : ∀ v, uMat (s v) *ᵥ rv X.B.I v (X.zR u) = rv X.B.I v (X.zR u))
    {r : X.B.I.Ginf} (hr : r ∈ X.NinfU u) : s⁻¹ * r * s ∈ X.NinfU u := by
  dsimp [HidaSetting.NinfU, Ninf] at hr ⊢
  intro v
  have h1 : uMat (s⁻¹ v) * uMat (s v) = 1 := by
    delta uMat
    simp
  have hmul : uMat ((s v)⁻¹ * r v * s v) = uMat (s⁻¹ v) * uMat (r v) * uMat (s v) := by
    delta uMat
    simp
  have hU : (uMat (s v))ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * uMat (s v) = Formalism.REAL.Jm (X.B.I.ε v) := by
    delta uMat
    first
    | exact (s v).2
    | exact (s v).1.2
    | simpa using (s v).2
  rw [hmul]
  exact inN_conj _ _ _ (uMat (s v)) (uMat (s⁻¹ v)) (uMat (r v)) h1 hU (he v) (hz v) (hr v)

theorem ninf_conj_iff (u : D.what₂.Word) (s : X.B.I.Ginf)
    (he : ∀ v a, uMat (s v) *ᵥ rv X.B.I v (X.eR a) = rv X.B.I v (X.eR a))
    (hz : ∀ v, uMat (s v) *ᵥ rv X.B.I v (X.zR u) = rv X.B.I v (X.zR u)) (r : X.B.I.Ginf) :
    r ∈ X.NinfU u ↔ s⁻¹ * r * s ∈ X.NinfU u := by
  constructor
  · exact ninf_conj X u s he hz
  · intro h
    have he' : ∀ v a, uMat (s⁻¹ v) *ᵥ rv X.B.I v (X.eR a) = rv X.B.I v (X.eR a) :=
      fun v a => fix_inv X s (he v a)
    have hz' : ∀ v, uMat (s⁻¹ v) *ᵥ rv X.B.I v (X.zR u) = rv X.B.I v (X.zR u) :=
      fun v => fix_inv X s (hz v)
    have h2 := ninf_conj X u s⁻¹ he' hz' h
    simpa [mul_assoc] using h2

end Grp

open Formalism.L2.SG.TermOp.Vanish in

theorem fixNormC : FixNormC := by
  intro D X Y u u' t h hh r
  have hfe : ∀ v a, uMat (h v) *ᵥ rv X.B.I v (X.eR a) = rv X.B.I v (X.eR a) :=
    fun v a => fix_rv hh (basis_mem_fixedSubspace t.rep a) v
  have hfz : ∀ v, uMat (h v) *ᵥ rv X.B.I v (X.zR u) = rv X.B.I v (X.zR u) :=
    fun v => fix_rv hh (zu_mem_fixedSubspaceOfRepresentative t.rep) v
  have hfe' : ∀ v a, uMat ((t.pt.1⁻¹ * h * t.pt.1) v) *ᵥ rv X.B.I v (X.eR a) = rv X.B.I v (X.eR a) :=
    fun v a => fix'_rv hh (ge_mem_fixedSubspace t.rep a) v
  have hfz' : ∀ v, uMat ((t.pt.1⁻¹ * h * t.pt.1) v) *ᵥ rv X.B.I v (X.zR u') = rv X.B.I v (X.zR u') :=
    fun v => fix'_rv hh (gz_mem_fixedSubspace t.rep) v
  have e : t.pt.1⁻¹ * (h⁻¹ * r * h) * t.pt.1 =
      (t.pt.1⁻¹ * h * t.pt.1)⁻¹ * (t.pt.1⁻¹ * r * t.pt.1) * (t.pt.1⁻¹ * h * t.pt.1) := by group
  show (r ∈ X.NinfU u ∧ t.pt.1⁻¹ * r * t.pt.1 ∈ X.NinfU u') ↔
    (h⁻¹ * r * h ∈ X.NinfU u ∧ t.pt.1⁻¹ * (h⁻¹ * r * h) * t.pt.1 ∈ X.NinfU u')
  rw [e, ← ninf_conj_iff X u h hfe hfz r, ← ninf_conj_iff X u' _ hfe' hfz' (t.pt.1⁻¹ * r * t.pt.1)]

end Formalism.L2.SG.CovariantRepresentation
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ZsVolKey
section
noncomputable section

namespace Formalism.L2.SG.Pf.ZsVolKey

open Formalism.L2.SG.Pf.StabilizerIndexVolumes Matrix

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E} {r : ℕ} {T T' : E}

theorem act_inv (f : Fin (r + 1) → S.V) (s : S.V ≃ₗ[E] S.V) (P : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hP : P * P⁻¹ = 1) (hs : ∀ b, s (f b) = ∑ c, P c b • f c) (b : Fin (r + 1)) :
    s (∑ c, P⁻¹ c b • f c) = f b := by
  simp only [map_sum, map_smul, hs, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
  have h1 : ∀ d, ∑ c, P⁻¹ c b * P d c = (P * P⁻¹) d b := fun d => by
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun c _ => mul_comm _ _
  simp only [h1, hP, Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

theorem up_inv_mul {P : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (hP : Formalism.MainNotions.S.IsUpUni P) : P * P⁻¹ = 1 := by
  have htri : P.BlockTriangular id := fun i j hij => (hP i j).1 hij
  have hdet : P.det = 1 := by
    rw [Matrix.det_of_upperTriangular htri]
    exact Finset.prod_eq_one fun i _ => (hP i i).2 rfl
  exact Matrix.mul_nonsing_inv P (by rw [hdet]; exact isUnit_one)

theorem eq_sL (F : Formalism.MainNotions.S.FlagG S r T) (F' : Formalism.MainNotions.S.FlagG S r T') (hG : IsUnit (gramOf (gg F F')).det)
    (s : S.V ≃ₗ[E] S.V) (hs : ∀ x y, S.hT (s x) (s y) = S.hT x y)
    (P Q : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (hP : Formalism.MainNotions.S.IsUpUni P) (hQ : Formalism.MainNotions.S.IsUpUni Q)
    (hsf : ∀ b, s (F.fvec b) = ∑ c, P c b • F.fvec c) (hsf' : ∀ b, s (F'.fvec b) = ∑ c, Q c b • F'.fvec c)
    (hsX : ∀ x, (∀ i, S.hT (F.e i) x = 0) → s x - x ∈ Submodule.span E (Set.range F.e)) (x : S.V) :
    s x = sL (gg F F') (UU P Q) x := by
  classical
  have hframe : ∀ m, s (gg F F' m) = sL (gg F F') (UU P Q) (gg F F' m) := by
    intro m
    cases m with
    | inl b =>
      show s (F.fvec b) = sL (gg F F') (UU P Q) (F.fvec b)
      rw [hsf, sL_frame (F := F) (F' := F') hG P Q b]
    | inr b =>
      show s (F'.fvec b) = sL (gg F F') (UU P Q) (F'.fvec b)
      rw [hsf', sL_frame' (F := F) (F' := F') hG P Q b]
  have hy : ∀ l, S.hT (gg F F' l) (x - ∑ m, cOf (gg F F') x m • gg F F' m) = 0 := by
    intro l
    have h1 := congrFun (gram_cOf (gg F F') hG x) l
    rw [map_sub, map_sum, ← h1]
    simp only [map_smul, smul_eq_mul, Matrix.mulVec, dotProduct, gramOf]
    rw [sub_eq_zero]
    exact Finset.sum_congr rfl fun m _ => mul_comm _ _
  have hspan0 : ∀ w ∈ Submodule.span E (Set.range (gg F F')),
      S.hT w (x - ∑ m, cOf (gg F F') x m • gg F F' m) = 0 := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨l, rfl⟩ := hv
      exact hy l
    | zero => rw [map_zero, LinearMap.zero_apply]
    | add a b _ _ ha hb => rw [map_add, LinearMap.add_apply, ha, hb, add_zero]
    | smul a v _ hv => rw [map_smulₛₗ, LinearMap.smul_apply, hv, smul_zero]
  have hpre : ∀ l, ∃ w ∈ Submodule.span E (Set.range (gg F F')), s w = gg F F' l := by
    intro l
    cases l with
    | inl b =>
      refine ⟨∑ c, P⁻¹ c b • F.fvec c, Submodule.sum_mem _ fun c _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inl c, rfl⟩), ?_⟩
      exact act_inv F.fvec s P (up_inv_mul hP) hsf b
    | inr b =>
      refine ⟨∑ c, Q⁻¹ c b • F'.fvec c, Submodule.sum_mem _ fun c _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr c, rfl⟩), ?_⟩
      exact act_inv F'.fvec s Q (up_inv_mul hQ) hsf' b
  have hsy : s (x - ∑ m, cOf (gg F F') x m • gg F F' m) = x - ∑ m, cOf (gg F F') x m • gg F F' m := by
    have hy' : ∀ i, S.hT (F.e i) (x - ∑ m, cOf (gg F F') x m • gg F F' m) = 0 := by
      intro i
      have h2 := hy (Sum.inl i.castSucc)
      simpa [gg, Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_castSucc] using h2
    have hmem := hsX _ hy'
    have hdspan : s (x - ∑ m, cOf (gg F F') x m • gg F F' m) - (x - ∑ m, cOf (gg F F') x m • gg F F' m) ∈
        Submodule.span E (Set.range (gg F F')) := by
      refine Submodule.span_mono ?_ hmem
      rintro _ ⟨i, rfl⟩
      exact ⟨Sum.inl i.castSucc, by simp [gg, Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_castSucc]⟩
    have hdperp : ∀ l, S.hT (gg F F' l)
        (s (x - ∑ m, cOf (gg F F') x m • gg F F' m) - (x - ∑ m, cOf (gg F F') x m • gg F F' m)) = 0 := by
      intro l
      obtain ⟨w, hw, hwl⟩ := hpre l
      rw [map_sub, hy l, sub_zero, ← hwl, hs, hspan0 w hw]
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hdspan
    have hc0 : cOf (gg F F') (s (x - ∑ m, cOf (gg F F') x m • gg F F' m) -
        (x - ∑ m, cOf (gg F F') x m • gg F F' m)) = 0 := by
      rw [cOf_eq]
      have hz : (fun l => S.hT (gg F F' l) (s (x - ∑ m, cOf (gg F F') x m • gg F F' m) -
          (x - ∑ m, cOf (gg F F') x m • gg F F' m))) = 0 := funext hdperp
      rw [hz, Matrix.mulVec_zero]
    have hca : cOf (gg F F') (∑ m, a m • gg F F' m) = a := by
      have h3 := cOf_comb (gg F F') hG 0 a
      rw [zero_add] at h3
      rw [h3]
      have h4 := cOf_smul (gg F F') 0 0
      rw [zero_smul, zero_smul] at h4
      rw [h4, zero_add]
    rw [ha] at hca
    rw [hc0] at hca
    rw [← sub_eq_zero, ← ha, ← hca]
    simp
  have hx : x = (x - ∑ m, cOf (gg F F') x m • gg F F' m) + ∑ m, cOf (gg F F') x m • gg F F' m := by
    rw [sub_add_cancel]
  rw [hx, map_add, map_add, map_sum, map_sum, hsy, sL_perp (F := F) (F' := F') hG _ hy]
  congr 1
  exact Finset.sum_congr rfl fun m _ => by rw [map_smul, map_smul, hframe m]

theorem nlam_of_frames (F : Formalism.MainNotions.S.FlagG S r T) (F' : Formalism.MainNotions.S.FlagG S r T') (hG : IsUnit (gramOf (gg F F')).det)
    (hZu : IsUnit (Formalism.MainNotions.S.Zhat F F').det)
    (s : S.V ≃ₗ[E] S.V) (hs : ∀ x y, S.hT (s x) (s y) = S.hT x y)
    (P Q : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (hP : Formalism.MainNotions.S.IsUpUni P) (hQ : Formalism.MainNotions.S.IsUpUni Q)
    (hsf : ∀ b, s (F.fvec b) = ∑ c, P c b • F.fvec c) (hsf' : ∀ b, s (F'.fvec b) = ∑ c, Q c b • F'.fvec c)
    (hsX : ∀ x, (∀ i, S.hT (F.e i) x = 0) → s x - x ∈ Submodule.span E (Set.range F.e)) :
    (∀ j, ∀ x ∈ F'.Xa (j + 1), s x - x ∈ F'.Xa j) ∧
      (∀ x, (∀ i, S.hT (F'.e i) x = 0) → s x - x ∈ Submodule.span E (Set.range F'.e)) := by
  have hQd : Q.det = 1 := by
    have htri : Q.BlockTriangular id := fun i j hij => (hQ i j).1 hij
    rw [Matrix.det_of_upperTriangular htri]
    exact Finset.prod_eq_one fun i _ => (hQ i i).2 rfl
  have hmat : P.conjTranspose * Formalism.MainNotions.S.Zhat F F' * Q = Formalism.MainNotions.S.Zhat F F' := by
    ext a b
    have h := hs (F.fvec a) (F'.fvec b)
    rw [hsf, hsf'] at h
    simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, map_smul, smul_eq_mul,
      Finset.mul_sum] at h
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Formalism.MainNotions.S.Zhat, Formalism.MainNotions.S.brS]
    rw [← h, Finset.sum_comm]
    simp only [Finset.sum_mul, RingHom.id_apply, starRingEnd_apply]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => by ring
  have hZH : IsUnit (Formalism.MainNotions.S.Zhat F F').conjTranspose.det := by
    rw [Matrix.det_conjTranspose]
    exact hZu.star
  have hQH : IsUnit Q.conjTranspose.det := by
    rw [Matrix.det_conjTranspose, hQd, star_one]
    exact isUnit_one
  have h2 : Q.conjTranspose * (Formalism.MainNotions.S.Zhat F F').conjTranspose * P = (Formalism.MainNotions.S.Zhat F F').conjTranspose := by
    have h3 := congrArg Matrix.conjTranspose hmat
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      ← Matrix.mul_assoc] at h3
  have e1 : (Formalism.MainNotions.S.Zhat F F').conjTranspose * P = (Q.conjTranspose)⁻¹ * (Formalism.MainNotions.S.Zhat F F').conjTranspose := by
    conv_rhs => rw [← h2]
    rw [Matrix.mul_assoc Q.conjTranspose, ← Matrix.mul_assoc (Q.conjTranspose)⁻¹, Matrix.nonsing_inv_mul _ hQH,
      Matrix.one_mul]
  have hrel : P = ((Formalism.MainNotions.S.Zhat F F').conjTranspose)⁻¹ * (Q.conjTranspose)⁻¹ * (Formalism.MainNotions.S.Zhat F F').conjTranspose := by
    rw [Matrix.mul_assoc, ← e1, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hZH, Matrix.one_mul]
  have hQl : Formalism.MainNotions.S.IsLoUni Q.conjTranspose := fun i j =>
    ⟨fun h => by simp [Matrix.conjTranspose_apply, (hQ j i).1 h],
     fun h => by subst h; simp [Matrix.conjTranspose_apply, (hQ i i).2 rfl]⟩
  refine ⟨fun j x hx => ?_, fun x hx => ?_⟩
  · rw [eq_sL F F' hG s hs P Q hP hQ hsf hsf' hsX x]
    exact sL_Xa' (F := F) (F' := F') hG hQ j x hx
  · rw [eq_sL F F' hG s hs P Q hP hQ hsf hsf' hsX x]
    exact sL_orth' (F := F) (F' := F') hG hQ hZH hrel (loUni_inv hQl) x hx

end Formalism.L2.SG.Pf.ZsVolKey

end
end

