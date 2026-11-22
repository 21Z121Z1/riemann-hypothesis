import Formalism.LocalToGlobal.ProjectiveLattices.AlgebraMapCAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0001

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.RhoWApply
section
noncomputable section

namespace Formalism.L2.Pj

section Act

variable {K : Type} [Field K] {ι : Type}
variable (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
variable (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
  (S →ₐ[K] T) → pts S → pts T → Prop)
variable (borR : ∀ {S : Type} [CommRing S] [Algebra K S], (ι → Sˣ) → pts S → pts S → Prop)
variable {G : Type} [Group G]
variable (actR : ∀ {S : Type} [CommRing S] [Algebra K S], G → pts S → pts S → Prop)

def mvPt (g : G) {S : Type} [CommRing S] [Algebra K S] (y : pts S) : pts S :=
  open Classical in if h : ∃ y', actR g y y' then h.choose else y

def actRule (g : G) (f : Rules pts) : Rules pts := fun p y => f p (mvPt pts actR g y)

def actL (g : G) : Rules pts →ₗ[K] Rules pts where
  toFun := actRule pts actR g
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem actL_apply (g : G) (f : Rules pts) (p : TRing K) (y : pts p.R) :
    actL pts actR g f p y = f p (mvPt pts actR g y) := rfl

def ActTotal : Prop :=
  ∀ (g : G) (S : Type) [CommRing S] [Algebra K S] (y : pts S), ∃ y', actR g y y'

def ActFun : Prop :=
  ∀ (g : G) (S : Type) [CommRing S] [Algebra K S] (y y' y'' : pts S),
    actR g y y' → actR g y y'' → mapR (AlgHom.id K S) y' y''

def ActOne : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra K S] (y : pts S), actR 1 y y

def ActMul : Prop :=
  ∀ (g h : G) (S : Type) [CommRing S] [Algebra K S] (y y' y'' : pts S),
    actR g y y' → actR h y' y'' → actR (g * h) y y''

def ActNat : Prop :=
  ∀ (g : G) (S T : Type) [CommRing S] [Algebra K S] [CommRing T] [Algebra K T] (φ : S →ₐ[K] T)
    (y y' : pts S) (z z' : pts T), mapR φ y z → actR g y y' → actR g z z' → mapR φ y' z'

def ActBor : Prop :=
  ∀ (g : G) (S : Type) [CommRing S] [Algebra K S] (t : ι → Sˣ) (y y' z z' : pts S),
    borR t y z → actR g y y' → actR g z z' → borR t y' z'

variable {pts actR}

theorem mvPt_spec (hT : ActTotal pts actR) (g : G) {S : Type} [CommRing S] [Algebra K S] (y : pts S) :
    actR g y (mvPt pts actR g y) := by
  have h := hT g S y
  unfold mvPt
  rw [dif_pos h]
  exact h.choose_spec

variable (pts actR)

theorem actL_mem [Fintype ι] (hT : ActTotal pts actR) (hN : ActNat pts mapR actR) (hB : ActBor pts borR actR)
    (e : ι → ℕ) (g : G) {f : Rules pts} (hf : f ∈ secW pts mapR borR e) :
    actL pts actR g f ∈ secW pts mapR borR e := by
  obtain ⟨h1, h2⟩ := hf
  refine ⟨?_, ?_⟩
  · intro p q φ y z hyz
    exact h1 p q φ _ _ (hN g p.R q.R φ y (mvPt pts actR g y) z (mvPt pts actR g z) hyz
      (mvPt_spec hT g y) (mvPt_spec hT g z))
  · intro p t y y' hyy
    exact h2 p t _ _ (hB g p.R t y (mvPt pts actR g y) y' (mvPt pts actR g y') hyy
      (mvPt_spec hT g y) (mvPt_spec hT g y'))

theorem actL_one (hT : ActTotal pts actR) (hF : ActFun pts mapR actR) (hO : ActOne pts actR)
    {f : Rules pts} (hf : IsNatural pts mapR f) : actL pts actR 1 f = f := by
  funext p y
  show f p (mvPt pts actR 1 y) = f p y
  exact hf p p (AlgHom.id K p.R) y _ (hF 1 p.R y y _ (hO p.R y) (mvPt_spec hT 1 y))

theorem actL_mul (hT : ActTotal pts actR) (hF : ActFun pts mapR actR) (hM : ActMul pts actR)
    (g h : G) {f : Rules pts} (hf : IsNatural pts mapR f) :
    actL pts actR (g * h) f = actL pts actR g (actL pts actR h f) := by
  funext p y
  show f p (mvPt pts actR (g * h) y) = f p (mvPt pts actR h (mvPt pts actR g y))
  have h1 : actR (g * h) y (mvPt pts actR h (mvPt pts actR g y)) :=
    hM g h p.R y _ _ (mvPt_spec hT g y) (mvPt_spec hT h _)
  exact (hf p p (AlgHom.id K p.R) _ _ (hF (g * h) p.R y _ _ (mvPt_spec hT (g * h) y) h1)).symm

structure ActLaws : Prop where
  total : ActTotal pts actR
  func : ActFun pts mapR actR
  one : ActOne pts actR
  mul : ActMul pts actR
  nat : ActNat pts mapR actR
  bor : ActBor pts borR actR

variable {pts mapR borR actR}

def rhoW [Fintype ι] (hL : ActLaws pts mapR borR actR) (e : ι → ℕ) :
    G →* Module.End K (secW pts mapR borR e) where
  toFun g :=
    { toFun := fun f => ⟨actL pts actR g f, actL_mem pts mapR borR actR hL.total hL.nat hL.bor e g f.2⟩
      map_add' := fun f f' => Subtype.ext (map_add (actL pts actR g) f.1 f'.1)
      map_smul' := fun c f => Subtype.ext (map_smul (actL pts actR g) c f.1) }
  map_one' := by
    ext f : 1
    exact Subtype.ext (actL_one pts mapR actR hL.total hL.func hL.one f.2.1)
  map_mul' g h := by
    ext f : 1
    exact Subtype.ext (actL_mul pts mapR actR hL.total hL.func hL.mul g h f.2.1)

def RhoStabW [Fintype ι] (hL : ActLaws pts mapR borR actR) (e : ι → ℕ) (W : Submodule K (secW pts mapR borR e)) :
    Prop :=
  ∀ (g : G) (f : secW pts mapR borR e), f ∈ W → rhoW hL e g f ∈ W

def chiDet {D L : Type} [CommGroup D] [Monoid L] (det : G →* D) (χ : D →* Lˣ) : G →* Lˣ := χ.comp det

end Act

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.UnifDom
section
noncomputable section

namespace Formalism.L2.Pj

open ReciprocityTheory.ChartRestriction.G.FD NumberField Complex
open scoped ComplexConjugate Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem gram_eq (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (P : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G P = Pᵀ * G.map τ * P.map (starRingEnd ℂ) := by
  ext a b
  simp only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul]
  exact Finset.sum_comm

theorem gram_mul (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (P Q : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G (P * Q) = Qᵀ * gram τ G P * Q.map (starRingEnd ℂ) := by
  rw [gram_eq, gram_eq, Matrix.transpose_mul, Matrix.map_mul]
  simp only [Matrix.mul_assoc]

theorem sum_castLE {R : Type} [AddCommMonoid R] {i n : ℕ} (h : i ≤ n) (f : Fin n → R)
    (hf : ∀ c : Fin n, i ≤ (c : ℕ) → f c = 0) : ∑ c, f c = ∑ c : Fin i, f (Fin.castLE h c) := by
  refine (Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h)
    (fun c => f (Fin.castLE h c)) f (fun c hc => hf c ?_) (fun _ => rfl)).symm
  by_contra hlt
  push_neg at hlt
  exact hc ⟨⟨c, hlt⟩, rfl⟩

theorem sub_mul_tri {i : ℕ} (h : i ≤ r) (Q A : Matrix (Fin r) (Fin r) ℂ) (hQ : Q.IsUpperTriangular) :
    (Qᵀ * A * Q.map (starRingEnd ℂ)).submatrix (Fin.castLE h) (Fin.castLE h) =
      (Q.submatrix (Fin.castLE h) (Fin.castLE h))ᵀ * A.submatrix (Fin.castLE h) (Fin.castLE h) *
        (Q.submatrix (Fin.castLE h) (Fin.castLE h)).map (starRingEnd ℂ) := by
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
  rw [sum_castLE h]
  · refine Finset.sum_congr rfl fun l _ => ?_
    rw [sum_castLE h]
    intro k hk
    have hz : Q k (Fin.castLE h a) = 0 :=
      hQ (by simp only [id_eq, Fin.lt_iff_val_lt_val, Fin.coe_castLE]; exact lt_of_lt_of_le a.isLt hk)
    rw [hz, zero_mul]
  · intro l hl
    have hz : Q l (Fin.castLE h b) = 0 :=
      hQ (by simp only [id_eq, Fin.lt_iff_val_lt_val, Fin.coe_castLE]; exact lt_of_lt_of_le b.isLt hl)
    rw [hz, map_zero, mul_zero]

theorem lminor_mul_tri (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (P Q : Matrix (Fin r) (Fin r) ℂ)
    (hQ : Q.IsUpperTriangular) (i : Fin (r + 1)) :
    lminor (gram τ G (P * Q)) i =
      ((Complex.normSq (Q.submatrix (Fin.castLE (Nat.le_of_lt_succ i.isLt))
        (Fin.castLE (Nat.le_of_lt_succ i.isLt))).det : ℝ) : ℂ) * lminor (gram τ G P) i := by
  unfold lminor
  rw [gram_mul, sub_mul_tri (Nat.le_of_lt_succ i.isLt) Q (gram τ G P) hQ, Matrix.det_mul,
    Matrix.det_mul, Matrix.det_transpose]
  generalize Q.submatrix (Fin.castLE (Nat.le_of_lt_succ i.isLt)) (Fin.castLE (Nat.le_of_lt_succ i.isLt)) = M
  rw [show (M.map (starRingEnd ℂ)).det = starRingEnd ℂ M.det from (RingHom.map_det _ M).symm,
    ← Complex.mul_conj]
  ring

theorem det_sub_tri_ne {i : ℕ} (h : i ≤ r) (Q : Matrix (Fin r) (Fin r) ℂ) (hQ : Q.IsUpperTriangular)
    (hd : Q.det ≠ 0) : (Q.submatrix (Fin.castLE h) (Fin.castLE h)).det ≠ 0 := by
  have hsub : (Q.submatrix (Fin.castLE h) (Fin.castLE h)).BlockTriangular id := by
    intro a b hab
    simp only [Matrix.submatrix_apply]
    exact hQ (by simp only [id_eq, Fin.lt_iff_val_lt_val, Fin.coe_castLE] at hab ⊢; exact hab)
  rw [Matrix.det_of_upperTriangular hsub]
  rw [Matrix.det_of_upperTriangular hQ] at hd
  rw [Finset.prod_ne_zero_iff] at hd ⊢
  intro c _
  exact hd _ (Finset.mem_univ _)

theorem bor_upper {Ψ : Finset (E →+* ℂ)} {b : Frame Ψ r} (hb : b ∈ Bor Ψ r) (τ : Ψ) :
    (mat b τ).IsUpperTriangular := by
  intro a c hac
  exact (hb τ).2 a c hac

theorem dom_rmul (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) :
    rmul x b ∈ X.dom := by
  simp only [Data.dom, GG, Set.mem_setOf_eq] at hx ⊢
  intro τ
  obtain ⟨hdet, hpos⟩ := hx τ
  have hQ := bor_upper hb τ
  have hbd : (mat b τ).det ≠ 0 := (hb τ).1
  have hm : mat (rmul x b) τ = mat x τ * mat b τ := rfl
  refine ⟨?_, fun i => ?_⟩
  · rw [hm, Matrix.det_mul]
    exact mul_ne_zero hdet hbd
  · have hi := hpos i
    simp only [dmin] at hi ⊢
    rw [hm, lminor_mul_tri τ.1 X.Gm _ _ hQ i, Complex.re_ofReal_mul]
    have hn : 0 < Complex.normSq ((mat b τ).submatrix (Fin.castLE (Nat.le_of_lt_succ i.isLt))
        (Fin.castLE (Nat.le_of_lt_succ i.isLt))).det :=
      Complex.normSq_pos.mpr (det_sub_tri_ne _ _ hQ hbd)
    rw [mul_left_comm]
    exact mul_pos hn hi

theorem ustab_mat {G : Matrix (Fin r) (Fin r) E} {Λ : Submodule (𝓞 E) (Fin r → E)} {γ : GL (Fin r) E}
    (h : IsUStab G Λ γ) :
    (γ : Matrix (Fin r) (Fin r) E)ᵀ * G * (γ : Matrix (Fin r) (Fin r) E).map cc = G := by
  ext k l
  have h1 := h.1 (Pi.single k 1) (Pi.single l 1)
  have hR : herm G (Pi.single k 1) (Pi.single l 1) = G k l := by
    have hs : ∀ b, cc ((Pi.single l (1 : E) : Fin r → E) b) = (Pi.single l (1 : E) : Fin r → E) b := by
      intro b
      by_cases hb : b = l <;> simp [hb, cc]
    simp only [herm, hs]
    simp [Pi.single_apply]
  have hL : herm G (Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) (Pi.single k 1))
      (Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) (Pi.single l 1)) =
      ((γ : Matrix (Fin r) (Fin r) E)ᵀ * G * (γ : Matrix (Fin r) (Fin r) E).map cc) k l := by
    simp only [herm, Matrix.mulVec_single_one, Matrix.transpose_apply, Matrix.mul_apply,
      Matrix.map_apply, Finset.sum_mul]
    exact Finset.sum_comm
  rw [← hL, h1, hR]

theorem dom_lact (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) {γ : GL (Fin r) E}
    (hγ : IsUStab X.Gm X.Λ γ) : lact γ x ∈ X.dom := by
  have hU := ustab_mat hγ
  have hcc : ∀ (σ : E →+* ℂ) (a : E), σ (cc a) = starRingEnd ℂ (σ a) := by
    intro σ a
    exact NumberField.IsCMField.complexEmbedding_complexConj E σ a
  simp only [Data.dom, GG, Set.mem_setOf_eq] at hx ⊢
  intro τ
  obtain ⟨hdet, hpos⟩ := hx τ
  have hm : mat (lact γ x) τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ := rfl
  have hc : ((γ : Matrix (Fin r) (Fin r) E).map cc).map τ.1 =
      ((γ : Matrix (Fin r) (Fin r) E).map τ.1).map (starRingEnd ℂ) := by
    ext a b
    simp only [Matrix.map_apply]
    exact hcc _ _
  have key : ((γ : Matrix (Fin r) (Fin r) E).map τ.1)ᵀ * X.Gm.map τ.1 *
      ((γ : Matrix (Fin r) (Fin r) E).map τ.1).map (starRingEnd ℂ) = X.Gm.map τ.1 := by
    rw [← hc, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hU]
  have hgr : gram τ.1 X.Gm (mat (lact γ x) τ) = gram τ.1 X.Gm (mat x τ) := by
    rw [hm, gram_eq, gram_eq, Matrix.transpose_mul, Matrix.map_mul]
    rw [show ∀ M1 M2 M3 M4 M5 : Matrix (Fin r) (Fin r) ℂ,
        M1 * M2 * M3 * (M4 * M5) = M1 * (M2 * M3 * M4) * M5 from
      fun M1 M2 M3 M4 M5 => by simp only [Matrix.mul_assoc], key]
  refine ⟨?_, fun i => ?_⟩
  · rw [hm, Matrix.det_mul]
    refine mul_ne_zero ?_ hdet
    rw [show ((γ : Matrix (Fin r) (Fin r) E).map τ.1).det = τ.1 (γ : Matrix (Fin r) (Fin r) E).det from
      (RingHom.map_det τ.1 _).symm]
    exact (map_ne_zero τ.1).mpr ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit γ)).ne_zero
  · have hi := hpos i
    simp only [dmin] at hi ⊢
    rw [hgr]
    exact hi

end Formalism.L2.Pj
end
end

