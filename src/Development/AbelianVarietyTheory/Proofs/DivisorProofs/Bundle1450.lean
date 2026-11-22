import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1430
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0128
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1432
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1416

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviElementAdapted
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.LeviPlane

variable {R : Type} [CommRing R] (c : R →+* R) {n : ℕ}

def fm (J : Matrix (Fin n) (Fin n) R) (u v : Fin n → R) : R := u ⬝ᵥ J *ᵥ (fun i => c (v i))

def lev (J : Matrix (Fin n) (Fin n) R) (X Y : Fin n → R) (s r : R) : Matrix (Fin n) (Fin n) R :=
  1 + (s - 1) • Matrix.vecMulVec X (J *ᵥ fun i => c (Y i)) - (r - 1) • Matrix.vecMulVec Y (J *ᵥ fun i => c (X i))

theorem lev_mulVec (J : Matrix (Fin n) (Fin n) R) (X Y : Fin n → R) (s r : R) (w : Fin n → R) :
    lev c J X Y s r *ᵥ w = w + ((s - 1) * fm c J w Y) • X - ((r - 1) * fm c J w X) • Y := by
  ext i
  simp only [lev, fm, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    Matrix.vecMulVec_mulVec, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
    MulOpposite.unop_op, dotProduct_comm w]
  ring

theorem fm_skew (hc : ∀ x, c (c x) = x) (J : Matrix (Fin n) (Fin n) R) (hJ : ∀ i j, c (J j i) = -J i j)
    (p q : Fin n → R) : fm c J p q = -c (fm c J q p) := by
  simp only [fm, dotProduct, Matrix.mulVec, map_sum, map_mul, hc, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hJ]; ring

variable {c}

theorem fm_add_left (J : Matrix (Fin n) (Fin n) R) (u u' v : Fin n → R) : fm c J (u + u') v = fm c J u v + fm c J u' v := by
  simp [fm, add_dotProduct]

theorem fm_sub_left (J : Matrix (Fin n) (Fin n) R) (u u' v : Fin n → R) : fm c J (u - u') v = fm c J u v - fm c J u' v := by
  simp [fm, sub_dotProduct]

theorem fm_smul_left (J : Matrix (Fin n) (Fin n) R) (a : R) (u v : Fin n → R) : fm c J (a • u) v = a * fm c J u v := by
  simp [fm, smul_dotProduct]

theorem fm_add_right (J : Matrix (Fin n) (Fin n) R) (u v v' : Fin n → R) : fm c J u (v + v') = fm c J u v + fm c J u v' := by
  have : (fun i => c ((v + v') i)) = (fun i => c (v i)) + fun i => c (v' i) := by ext i; simp
  simp only [fm, this, Matrix.mulVec_add, dotProduct_add]

theorem fm_sub_right (J : Matrix (Fin n) (Fin n) R) (u v v' : Fin n → R) : fm c J u (v - v') = fm c J u v - fm c J u v' := by
  have : (fun i => c ((v - v') i)) = (fun i => c (v i)) - fun i => c (v' i) := by ext i; simp
  simp only [fm, this, Matrix.mulVec_sub, dotProduct_sub]

theorem fm_smul_right (J : Matrix (Fin n) (Fin n) R) (a : R) (u v : Fin n → R) : fm c J u (a • v) = c a * fm c J u v := by
  have : (fun i => c ((a • v) i)) = c a • fun i => c (v i) := by ext i; simp
  simp only [fm, this, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem entry (J M : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    (Mᵀ * J * M.map c) i j = fm c J (M *ᵥ Pi.single i 1) (M *ᵥ Pi.single j 1) := by
  rw [Matrix.mulVec_single_one, Matrix.mulVec_single_one]
  simp only [fm, Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.map_apply, Matrix.col_apply,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

end GlobalTheory.LeviPlane

namespace GlobalTheory.LeviPlane
variable {R : Type} [CommRing R] {c : R →+* R} {n : ℕ}

section Plane
variable (hc : ∀ x, c (c x) = x) {J : Matrix (Fin n) (Fin n) R} (hJ : ∀ i j, c (J j i) = -J i j) {X Y : Fin n → R}
  (hxx : fm c J X X = 0) (hyy : fm c J Y Y = 0) (hxy : fm c J X Y = 1)
include hc hJ hxx hyy hxy

theorem fm_yx : fm c J Y X = -1 := by rw [fm_skew c hc J hJ, hxy, map_one]

theorem lev_mul (s r s' r' : R) : lev c J X Y s r * lev c J X Y s' r' = lev c J X Y (s * s') (r * r') := by
  have hyx := fm_yx hc hJ hxx hyy hxy
  have key : ∀ w, (lev c J X Y s r * lev c J X Y s' r') *ᵥ w = lev c J X Y (s * s') (r * r') *ᵥ w := by
    intro w
    rw [← Matrix.mulVec_mulVec, lev_mulVec, lev_mulVec, lev_mulVec]
    simp only [fm_add_left, fm_sub_left, fm_smul_left, hxx, hyy, hxy, hyx]
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  ext i j
  have := congrFun (key (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using this

theorem lev_one : lev c J X Y 1 1 = 1 := by simp [lev]

theorem lev_unitary (s r : R) (hsr : s * c r = 1) :
    (lev c J X Y s r)ᵀ * J * (lev c J X Y s r).map c = J := by
  have hyx := fm_yx hc hJ hxx hyy hxy
  have hrs : r * c s = 1 := by
    have := congrArg c hsr; rw [map_mul, hc, map_one] at this; rw [mul_comm]; exact this
  have key : ∀ u v, fm c J (lev c J X Y s r *ᵥ u) (lev c J X Y s r *ᵥ v) = fm c J u v := by
    intro u v
    rw [lev_mulVec, lev_mulVec]
    simp only [fm_add_left, fm_sub_left, fm_smul_left, fm_add_right, fm_sub_right, fm_smul_right, hxx, hyy, hxy, hyx]
    rw [fm_skew c hc J hJ X v, fm_skew c hc J hJ Y v]
    simp only [map_mul, map_sub, map_one, map_neg]
    linear_combination (-(fm c J u Y * c (fm c J v X))) * hsr + (fm c J u X * c (fm c J v Y)) * hrs
  ext i j
  rw [entry, key]
  have h1 := entry (c := c) J 1 i j
  simp only [Matrix.transpose_one, Matrix.one_mul, Matrix.map_one _ (map_zero c) (map_one c), Matrix.mul_one,
    Matrix.one_mulVec] at h1
  exact h1.symm

end Plane

theorem lev_X {J : Matrix (Fin n) (Fin n) R} {X Y : Fin n → R} (hxx : fm c J X X = 0) (hxy : fm c J X Y = 1) (s r : R) :
    lev c J X Y s r *ᵥ X = s • X := by
  rw [lev_mulVec, hxx, hxy]; ext i; simp; ring

theorem lev_Y (hc : ∀ x, c (c x) = x) {J : Matrix (Fin n) (Fin n) R} (hJ : ∀ i j, c (J j i) = -J i j) {X Y : Fin n → R}
    (hxx : fm c J X X = 0) (hyy : fm c J Y Y = 0) (hxy : fm c J X Y = 1) (s r : R) :
    lev c J X Y s r *ᵥ Y = r • Y := by
  rw [lev_mulVec, hyy, fm_yx hc hJ hxx hyy hxy]; ext i; simp; ring

theorem lev_mul_ι {J : Matrix (Fin n) (Fin n) R} {X Y : Fin n → R} {k : ℕ} (ι : Matrix (Fin n) (Fin k) R)
    (hι : ∀ j, fm c J (fun i => ι i j) X = 0 ∧ fm c J (fun i => ι i j) Y = 0) (s r : R) :
    lev c J X Y s r * ι = ι := by
  ext i j
  have h := congrFun (lev_mulVec c J X Y s r (fun i => ι i j)) i
  rw [(hι j).1, (hι j).2] at h
  simp only [mul_zero, zero_smul, add_zero, sub_zero] at h
  rw [Matrix.mul_apply]
  simpa [Matrix.mulVec, dotProduct] using h

end GlobalTheory.LeviPlane

namespace GlobalTheory.LeviPlane
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sigma_invol {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  let τ : E →+* ℂ := (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := E)).toRingHom
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem cA_invol {σ : E →ₐ[F] E} (h : ∀ x, σ (σ x) = x) (x : AE F E) : cA σ (cA σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [cA, Algebra.TensorProduct.map_tmul, h]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem cA_inclR (σ : E →ₐ[F] E) (e : E) : cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := by
  simp [cA, inclR, Algebra.TensorProduct.map_tmul]

theorem cAr_inclR (σ : E →ₐ[F] E) (e : E) :
    (cA σ).toRingHom (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := cA_inclR σ e

theorem fm_inc (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    fm (cA σ).toRingHom (incM F J) (incV F x) (incV F y) = inclR (F := F) (AF F) (form σ J x y) := by
  simp only [fm, form, incV, incM, dotProduct, Matrix.mulVec, Matrix.map_apply, map_sum, map_mul,
    AlgHom.coe_toRingHom, cAr_inclR, cA_inclR]

end GlobalTheory.LeviPlane

open GlobalTheory.LeviPlane in

theorem GlobalTheory.LeviPlane.levi_exists : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B G.W W₁ i₀ i₁ → ∀ t : (AE F E)ˣ, ∃ m : UA σ G.W.J, IsLevi (W₁ := W₁) H' t 1 m := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hH t
  set c : AE F E →+* AE F E := (cA σ).toRingHom with hcdef
  have hσ := sigma_invol hT.base.cm
  have hc : ∀ x, c (c x) = x := fun x => cA_invol hσ x
  have hJ : ∀ i j, c (incM F G.W.J j i) = -incM F G.W.J i j := by
    intro i j
    simp only [hcdef, incM, Matrix.map_apply, cAr_inclR, hT.geo.hW.skew, map_neg]
  have hxx : fm c (incM F G.W.J) (incV F H'.x) (incV F H'.x) = 0 := by rw [fm_inc, hH.xx, map_zero]
  have hyy : fm c (incM F G.W.J) (incV F H'.y) (incV F H'.y) = 0 := by rw [fm_inc, hH.yy, map_zero]
  have hxy : fm c (incM F G.W.J) (incV F H'.x) (incV F H'.y) = 1 := by rw [fm_inc, hH.xy, map_one]
  have hι : ∀ j, fm c (incM F G.W.J) (fun i => incM F H'.ι i j) (incV F H'.x) = 0 ∧
      fm c (incM F G.W.J) (fun i => incM F H'.ι i j) (incV F H'.y) = 0 := by
    intro j
    have hcol : (fun i => incM F H'.ι i j) = incV F (H'.ι *ᵥ Pi.single j 1) := by
      ext i; simp [incV, incM, Matrix.mulVec_single_one]
    rw [hcol, fm_inc, fm_inc, (hH.orth _).1, (hH.orth _).2, map_zero]; exact ⟨rfl, rfl⟩
  let L : AE F E → AE F E → Matrix (Fin (a + a')) (Fin (a + a')) (AE F E) :=
    fun s r => lev c (incM F G.W.J) (incV F H'.x) (incV F H'.y) s r
  have hmul : ∀ s r s' r', L s r * L s' r' = L (s * s') (r * r') := fun s r s' r' =>
    lev_mul hc hJ hxx hyy hxy s r s' r'
  have h1 : L 1 1 = 1 := lev_one hc hJ hxx hyy hxy
  let g : GL (Fin (a + a')) (AE F E) :=
    ⟨L (t : AE F E) (cA σ ((t⁻¹ : (AE F E)ˣ) : AE F E)), L ((t⁻¹ : (AE F E)ˣ) : AE F E) (cA σ (t : AE F E)),
      by rw [hmul, ← map_mul, Units.mul_inv, Units.inv_mul, map_one, h1],
      by rw [hmul, ← map_mul, Units.inv_mul, Units.mul_inv, map_one, h1]⟩
  have hg : g ∈ GlobalTheory.WeilM.UG (cA σ) (incM F G.W.J) := by
    show (L _ _)ᵀ * incM F G.W.J * (L _ _).map (cA σ) = incM F G.W.J
    have := lev_unitary hc hJ hxx hyy hxy (t : AE F E) (cA σ ((t⁻¹ : (AE F E)ˣ) : AE F E))
      (by show (t : AE F E) * cA σ (cA σ _) = 1; rw [cA_invol hσ, Units.mul_inv])
    exact this
  refine ⟨⟨g, hg⟩, ?_, ?_, ?_⟩
  · exact lev_X hxx hxy _ _
  · exact lev_Y hc hJ hxx hyy hxy _ _
  · have : mat (1 : UA σ W₁.J) = 1 := rfl
    rw [this, Matrix.mul_one]
    exact lev_mul_ι _ hι _ _
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviElementTorusPart
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.AdelicPlaneLevi

open Matrix

section Gen

variable {R : Type} [CommRing R] {n : ℕ} (c : R →+* R) (J : Matrix (Fin n) (Fin n) R)

def fR (u v : Fin n → R) : R := u ⬝ᵥ J *ᵥ (fun i => c (v i))

theorem fR_add_left (u u' v : Fin n → R) : fR c J (u + u') v = fR c J u v + fR c J u' v := by
  simp [fR, add_dotProduct]

theorem fR_sub_left (u u' v : Fin n → R) : fR c J (u - u') v = fR c J u v - fR c J u' v := by
  simp [fR, sub_dotProduct]

theorem fR_smul_left (r : R) (u v : Fin n → R) : fR c J (r • u) v = r * fR c J u v := by
  simp [fR, smul_dotProduct]

theorem fR_add_right (u v v' : Fin n → R) : fR c J u (v + v') = fR c J u v + fR c J u v' := by
  have h : (fun i => c ((v + v') i)) = (fun i => c (v i)) + fun i => c (v' i) := by funext i; simp
  unfold fR; rw [h, Matrix.mulVec_add, dotProduct_add]

theorem fR_sub_right (u v v' : Fin n → R) : fR c J u (v - v') = fR c J u v - fR c J u v' := by
  have h : (fun i => c ((v - v') i)) = (fun i => c (v i)) - fun i => c (v' i) := by funext i; simp
  unfold fR; rw [h, Matrix.mulVec_sub, dotProduct_sub]

theorem fR_smul_right (r : R) (u v : Fin n → R) : fR c J u (r • v) = c r * fR c J u v := by
  have h : (fun i => c ((r • v) i)) = c r • fun i => c (v i) := by funext i; simp
  unfold fR; rw [h, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem fR_skew (hc : ∀ r, c (c r) = r) (hJ : ∀ i j, c (J j i) = -J i j) (u v : Fin n → R) :
    c (fR c J u v) = -fR c J v u := by
  simp only [fR, dotProduct, Matrix.mulVec, map_sum, map_mul, hc, Finset.mul_sum, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ]; ring

theorem fR_mulVec (A : Matrix (Fin n) (Fin n) R) (u v : Fin n → R) :
    fR c J (A *ᵥ u) (A *ᵥ v) = u ⬝ᵥ (Aᵀ * J * A.map c) *ᵥ (fun i => c (v i)) := by
  have h : (fun i => c ((A *ᵥ v) i)) = A.map c *ᵥ fun i => c (v i) := by
    funext i; exact RingHom.map_mulVec c A v i
  simp only [fR, h]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec u Aᵀ, Matrix.vecMul_transpose]

theorem eq_of_form (M N : Matrix (Fin n) (Fin n) R)
    (h : ∀ u v : Fin n → R, u ⬝ᵥ M *ᵥ (fun i => c (v i)) = u ⬝ᵥ N *ᵥ (fun i => c (v i))) : M = N := by
  ext i j
  have hs : (fun k => c ((Pi.single j (1 : R) : Fin n → R) k)) = Pi.single j 1 := by
    funext k; by_cases hk : k = j
    · subst hk; simp
    · simp [hk]
  have := h (Pi.single i 1) (Pi.single j 1)
  rw [hs] at this
  simpa [Matrix.mulVec_single_one] using this

theorem eq_of_mulVec (M N : Matrix (Fin n) (Fin n) R) (h : ∀ u, M *ᵥ u = N *ᵥ u) : M = N := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using this

def lev (x y : Fin n → R) (t s : R) : Matrix (Fin n) (Fin n) R :=
  1 + (t - 1) • vecMulVec x (J *ᵥ fun i => c (y i)) - (s - 1) • vecMulVec y (J *ᵥ fun i => c (x i))

theorem lev_mulVec (x y : Fin n → R) (t s : R) (u : Fin n → R) :
    lev c J x y t s *ᵥ u = u + ((t - 1) * fR c J u y) • x - ((s - 1) * fR c J u x) • y := by
  simp only [lev, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    Matrix.vecMulVec_mulVec, op_smul_eq_smul, smul_smul, fR]
  rw [dotProduct_comm (J *ᵥ _) u, dotProduct_comm (J *ᵥ _) u]

variable {c J}
variable {x y : Fin n → R} (hxx : fR c J x x = 0) (hyy : fR c J y y = 0) (hxy : fR c J x y = 1)
  (hyx : fR c J y x = -1)
include hxx hyy hxy hyx

theorem levi_element_fixes_first_vector (t s : R) : lev c J x y t s *ᵥ x = t • x := by
  rw [lev_mulVec, hxy, hxx]; module

theorem lev_y (t s : R) : lev c J x y t s *ᵥ y = s • y := by
  rw [lev_mulVec, hyy, hyx]; module

theorem lev_mul (t s t' s' : R) (h1 : t * t' = 1) (h2 : s * s' = 1) :
    lev c J x y t s * lev c J x y t' s' = 1 := by
  apply eq_of_mulVec; intro u
  rw [← Matrix.mulVec_mulVec, Matrix.one_mulVec, lev_mulVec c J x y t' s' u, lev_mulVec c J x y t s]
  simp only [fR_add_left, fR_sub_left, fR_smul_left, hxx, hyy, hxy, hyx]
  linear_combination (norm := module) (fR c J u y) • h1 • x - (fR c J u x) • h2 • y

theorem lev_orth (t s : R) (z : Fin n → R) (hz : fR c J z x = 0) (hz' : fR c J z y = 0) :
    lev c J x y t s *ᵥ z = z := by
  rw [lev_mulVec, hz, hz']; simp

theorem lev_unitary (hc : ∀ r, c (c r) = r) (hJ : ∀ i j, c (J j i) = -J i j) (t s : R) (h1 : c t * s = 1) (h2 : t * c s = 1) :
    (lev c J x y t s)ᵀ * J * (lev c J x y t s).map c = J := by
  apply eq_of_form c; intro u v
  rw [← fR_mulVec]
  change fR c J (lev c J x y t s *ᵥ u) (lev c J x y t s *ᵥ v) = fR c J u v
  have hxv : fR c J x v = -c (fR c J v x) := by rw [fR_skew c J hc hJ]; ring
  have hyv : fR c J y v = -c (fR c J v y) := by rw [fR_skew c J hc hJ]; ring
  rw [lev_mulVec, lev_mulVec]
  simp only [fR_add_left, fR_sub_left, fR_smul_left, fR_add_right, fR_sub_right, fR_smul_right, hxx, hyy, hxy, hyx,
    hxv, hyv, map_mul, map_sub, map_one]
  linear_combination (c (fR c J v y) * fR c J u x) * h1 - (fR c J u y * c (fR c J v x)) * h2

end Gen

end GlobalTheory.AdelicPlaneLevi

namespace GlobalTheory.AdelicPlaneLevi

open Matrix

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem cA_incl (σ : E →ₐ[F] E) (e : E) : cA σ (inclR (AF F) e) = inclR (AF F) (σ e) := by
  simp [cA, inclR]

theorem cA_cA (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) (a : AE F E) : cA σ (cA σ a) = a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [cA, hσ]
  | add a b ha hb => simp only [map_add, ha, hb]

theorem sigma_invol {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) (e : E) : σ (σ e) = e := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [hcm.2.2.2 τ, hcm.2.2.2 τ, star_star]

theorem fR_inc (σ : E →ₐ[F] E) {d : ℕ} (J : Matrix (Fin d) (Fin d) E) (a b : Fin d → E) :
    fR (cA σ).toRingHom (incM F J) (incV F a) (incV F b) = inclR (AF F) (form σ J a b) := by
  simp [fR, form, incV, incM, dotProduct, Matrix.mulVec, map_sum, map_mul, cA_incl]

end Main

theorem exists_levi : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (d : ℕ)
    (W : Spc F E d) (r s d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ), IsCMExt F E σ → W.IsSkew σ B r s →
    H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ t : (AE F E)ˣ, ∃ m : UA σ W.J, IsLevi (W₁ := W₁) H' t 1 m := by
  intro F E _ _ _ _ _ σ B d W r s d₁ W₁ H' i₀ i₁ hcm hW hH t
  have hσ : ∀ e, σ (σ e) = e := sigma_invol hcm
  let c : AE F E →+* AE F E := (cA σ).toRingHom
  have hc : ∀ a, c (c a) = a := cA_cA σ hσ
  have hJ : ∀ i j, c (incM F W.J j i) = -incM F W.J i j := by
    intro i j; simp [c, incM, cA_incl, hW.skew]
  have hxx : fR c (incM F W.J) (incV F H'.x) (incV F H'.x) = 0 := by rw [fR_inc, hH.xx, map_zero]
  have hyy : fR c (incM F W.J) (incV F H'.y) (incV F H'.y) = 0 := by rw [fR_inc, hH.yy, map_zero]
  have hxy : fR c (incM F W.J) (incV F H'.x) (incV F H'.y) = 1 := by rw [fR_inc, hH.xy, map_one]
  have hyx : fR c (incM F W.J) (incV F H'.y) (incV F H'.x) = -1 := by
    have := fR_skew c (incM F W.J) hc hJ (incV F H'.x) (incV F H'.y)
    rw [hxy, map_one] at this
    linear_combination this
  let s' : AE F E := c ((t⁻¹ : (AE F E)ˣ) : AE F E)
  let M := lev c (incM F W.J) (incV F H'.x) (incV F H'.y) t s'
  let M' := lev c (incM F W.J) (incV F H'.x) (incV F H'.y) ((t⁻¹ : (AE F E)ˣ) : AE F E) (c t)
  have e1 : s' * c t = 1 := by simp only [s', ← map_mul, Units.inv_mul, map_one]
  have e2 : c t * s' = 1 := by simp only [s', ← map_mul, Units.mul_inv, map_one]
  have hMM' : M * M' = 1 := lev_mul hxx hyy hxy hyx _ _ _ _ t.mul_inv e1
  have hM'M : M' * M = 1 := lev_mul hxx hyy hxy hyx _ _ _ _ t.inv_mul e2
  have hU : Mᵀ * incM F W.J * M.map c = incM F W.J := by
    refine lev_unitary hxx hyy hxy hyx hc hJ _ _ e2 ?_
    simp only [s', hc, Units.mul_inv]
  refine ⟨⟨⟨M, M', hMM', hM'M⟩, by exact hU⟩, ?_, ?_, ?_⟩
  · exact levi_element_fixes_first_vector hxx hyy hxy hyx _ _
  · exact lev_y hxx hyy hxy hyx _ _
  · show M * incM F H'.ι = incM F H'.ι * mat (1 : UA σ W₁.J)
    have h1 : mat (1 : UA σ W₁.J) = 1 := rfl
    rw [h1, Matrix.mul_one]
    ext i j
    have e : (fun k => incM F H'.ι k j) = incV F (H'.ι *ᵥ Pi.single j 1) := by
      funext k; simp [incV, incM, Matrix.mulVec_single_one]
    have hz : fR c (incM F W.J) (fun k => incM F H'.ι k j) (incV F H'.x) = 0 := by
      rw [e, fR_inc, (hH.orth _).1, map_zero]
    have hz' : fR c (incM F W.J) (fun k => incM F H'.ι k j) (incV F H'.y) = 0 := by
      rw [e, fR_inc, (hH.orth _).2, map_zero]
    have := congrFun (lev_orth hxx hyy hxy hyx t s' _ hz hz') i
    simpa [M, Matrix.mul_apply, Matrix.mulVec, dotProduct] using this

end GlobalTheory.AdelicPlaneLevi

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSkewHermitianCorrectionIsUnitAntidiagCorneStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_skewHermitian_correction_isUnit_antidiag_corner : ∀ (O : Type) [CommRing O] (c : O →+* O), IsUnit (2 : O) →
    (∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) O), (∀ i j, c (J j i) = J i j) → IsUnit J.det →
      ∀ g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O, IsUnit g.det →
        gᵀ * Matrix.fromBlocks 0 J J 0 * g.map c = Matrix.fromBlocks 0 J J 0 →
        ∃ Z : Matrix (Fin n) (Fin n) O, Zᵀ * J + J * Z.map c = 0 ∧ IsUnit (g.toBlocks₂₁ * Z + g.toBlocks₂₂).det) →
    ∀ (n : ℕ) (JL : Matrix (Fin n) (Fin n) O) (G G' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O),
    (∀ i j, c (JL j i) = JL i j) → IsUnit JL.det → G * G' = 1 →
    Gᵀ * Matrix.fromBlocks JL 0 0 (-JL) * G.map c = Matrix.fromBlocks JL 0 0 (-JL) →
    ∃ Z : Matrix (Fin n) (Fin n) O, Zᵀ * JL + JL * Z.map c = 0 ∧
      IsUnit (((Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O))ᵀ : Matrix (Fin n) (Fin n ⊕ Fin n) O) * G * (Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O) : Matrix (Fin n ⊕ Fin n) (Fin n) O) +
        ((Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O))ᵀ : Matrix (Fin n) (Fin n ⊕ Fin n) O) * G * (Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (1 : Matrix (Fin n) (Fin n) O) : Matrix (Fin n ⊕ Fin n) (Fin n) O) * Z).det := by
  first | exact @GlobalTheory.HermBlockChange.exists_unit_lower_block | exact GlobalTheory.HermBlockChange.exists_unit_lower_block | (intros; apply GlobalTheory.HermBlockChange.exists_unit_lower_block <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSupportedAtInfinityAdeleWithComplexCompone
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.RealLift

theorem exists_atInf_piInf_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (emb : ∀ w : InfinitePlace F, EmbOver E w) (f : InfinitePlace F → ℂ),
    ∃ z : AE F E, At (evI F) z ∧ ∀ w, piInf (emb w) z = f w := by
  intro F E _ _ _ _ _ σ h emb f
  have := h.1

  have him : ∀ (τ : E →+* ℂ) (e : E), σ e ≠ e → (τ e).im ≠ 0 := fun τ e he him => by
    apply he
    apply τ.injective
    rw [h.2.2.2 τ e]
    exact Complex.conj_eq_iff_im.2 him
  by_cases hσ : ∃ e : E, σ e ≠ e
  swap
  · push_neg at hσ
    refine ⟨0, fun u _ => smul_zero u, fun w => ?_⟩
    exfalso
    have := h.2.1
    refine (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex (InfinitePlace.mk (emb w).1)))
      (InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => ?_)))
    exact (h.2.2.2 (emb w).1 x).symm.trans (congrArg _ (hσ x))
  obtain ⟨e, he⟩ := hσ
  let lift : ∀ w : InfinitePlace F, ℝ → w.Completion := fun w t =>
    (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm t
  have hlift : ∀ w t, InfinitePlace.Completion.extensionEmbedding w (lift w t) = (t : ℂ) := fun w t => by
    rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (IsTotallyReal.isReal w)]
    exact congrArg _ ((InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).apply_symm_apply t)
  let c : InfinitePlace F → ℝ := fun w => (f w).im / ((emb w).1 e).im
  let a : InfinitePlace F → ℝ := fun w => (f w).re - c w * ((emb w).1 e).re
  let A : AF F := ((fun w => lift w (a w) : Ainf F), 0)
  let C : AF F := ((fun w => lift w (c w) : Ainf F), 0)
  refine ⟨A ⊗ₜ[F] (1 : E) + C ⊗ₜ[F] e, fun u hu => ?_, fun w => ?_⟩
  · have hu1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (hu.trans (map_zero _).symm)
    have hA : u * A = 0 := by
      show ((u.1 * A.1, u.2 * (0 : Af F)) : Ainf F × Af F) = ((0, 0) : Ainf F × Af F)
      rw [hu1, zero_mul, mul_zero]
    have hC : u * C = 0 := by
      show ((u.1 * C.1, u.2 * (0 : Af F)) : Ainf F × Af F) = ((0, 0) : Ainf F × Af F)
      rw [hu1, zero_mul, mul_zero]
    rw [smul_add, TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul, hA, hC,
      TensorProduct.zero_tmul, TensorProduct.zero_tmul, add_zero]
  · change infEmb (emb w) (compInf F E w (A ⊗ₜ[F] (1 : E) + C ⊗ₜ[F] e)) = f w
    rw [map_add]
    change infEmb (emb w) (evInf F w A ⊗ₜ[F] (1 : E) + evInf F w C ⊗ₜ[F] e) = f w
    rw [map_add, infEmb_tmul, infEmb_tmul, map_one, mul_one]
    change InfinitePlace.Completion.extensionEmbedding w (lift w (a w)) +
      InfinitePlace.Completion.extensionEmbedding w (lift w (c w)) * (emb w).1 e = f w
    rw [hlift, hlift]
    have hne := him (emb w).1 e he
    apply Complex.ext
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero, a]
      ring
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, zero_mul, add_zero, zero_add, c]
      field_simp

end GlobalTheory.RealLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalOfCommutingFiniteAlgebraJointEiStatement
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_of_commuting_finiteAlgebra_jointEigen : ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (S : Set (Module.End ℂ M)), (∀ s ∈ S, ∀ t ∈ S, s * t = t * s) → FiniteDimensional ℂ (Algebra.adjoin ℂ S) → (∀ c : Module.End ℂ M → ℂ, FiniteDimensional ℂ ↥(⨅ s ∈ S, LinearMap.ker (s - algebraMap ℂ (Module.End ℂ M) (c s)))) → FiniteDimensional ℂ M := by
  first | exact @GlobalTheory.AutGrowth.finiteDimensional_of_commuting_finite_eigen | exact GlobalTheory.AutGrowth.finiteDimensional_of_commuting_finite_eigen | (intros; apply GlobalTheory.AutGrowth.finiteDimensional_of_commuting_finite_eigen <;> assumption)
end

