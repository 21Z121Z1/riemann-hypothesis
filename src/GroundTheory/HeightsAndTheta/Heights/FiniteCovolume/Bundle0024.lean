import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PStabilizerLeviMatrices
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsStabilizerLevi
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0017
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0019
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0020
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnipotentModulusMatrix

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PStabilizerLeviPlaces
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume.StabilizerLevi

open NumberField GroundTheory.Automorphic Module Matrix

noncomputable section

set_option linter.unusedSectionVars false

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

def colMat (v : Basis ι E W) {κ : Type*} (u : κ → W) (w : InfinitePlace E) : Matrix ι κ ℂ :=
  Matrix.of fun i k => vecAt v (u k) w i

theorem vecAt_add (v : Basis ι E W) (x y : W) (w : InfinitePlace E) :
    vecAt v (x + y) w = vecAt v x w + vecAt v y w := by
  funext i; simp [vecAt]

theorem vecAt_smul (v : Basis ι E W) (a : E) (x : W) (w : InfinitePlace E) :
    vecAt v (a • x) w = w.embedding a • vecAt v x w := by
  funext i; simp [vecAt]

theorem vecAt_basis (v : Basis ι E W) (i : ι) (w : InfinitePlace E) :
    vecAt v (v i) w = Pi.single i 1 := by
  funext j; simp [vecAt, Finsupp.single_apply, Pi.single_apply, eq_comm]

theorem vecAt_sum_smul (v : Basis ι E W) {κ : Type*} [Fintype κ] (c : κ → E) (u : κ → W)
    (w : InfinitePlace E) :
    vecAt v (∑ k, c k • u k) w = colMat v u w *ᵥ fun k => w.embedding (c k) := by
  funext i
  simp [vecAt, colMat, mulVec, dotProduct, map_sum, mul_comm]

theorem vecAt_coe {W' : Submodule E W} {n : ℕ} (v : Basis ι E W) (v' : Basis (Fin n) E W') (x : W')
    (w : InfinitePlace E) :
    vecAt v (x : W) w = colMat v (fun k => (v' k : W)) w *ᵥ vecAt v' x w := by
  conv_lhs => rw [← v'.sum_repr x]
  rw [Submodule.coe_sum]
  simp only [Submodule.coe_smul]
  exact vecAt_sum_smul v _ _ w

theorem conjTranspose_mulVec_colMat (v : Basis ι E W) {κ : Type*} [Fintype κ] (u : κ → W)
    (w : InfinitePlace E) (z : ι → ℂ) (k : κ) :
    ((colMat v u w)ᴴ *ᵥ z) k = star (vecAt v (u k) w) ⬝ᵥ z := rfl

theorem conjT_eq {m n : Type*} (M : Matrix m n ℂ) : (M.map (starRingEnd ℂ))ᵀ = Mᴴ := by
  ext i j
  simp [conjTranspose_apply]

theorem archEmbed_apply (h : HermitianForm F E W) (v : Basis ι E W) (γ : h.unitaryGroup)
    (w : InfinitePlace E) :
    (((archEmbed h v γ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) =
      (LinearMap.toMatrix v v ((γ : W ≃ₗ[E] W) : W →ₗ[E] W)).map w.embedding := by
  rw [← unitaryGroupEquivMatrix_apply]
  rfl

theorem map_toMatrix_mulVec_vecAt (v : Basis ι E W) (f : W →ₗ[E] W) (x : W)
    (w : InfinitePlace E) :
    (LinearMap.toMatrix v v f).map w.embedding *ᵥ vecAt v x w = vecAt v (f x) w := by
  funext i
  change _ = w.embedding (v.repr (f x) i)
  rw [← LinearMap.toMatrix_mulVec_repr v v, RingHom.map_mulVec]
  rfl

variable {h : HermitianForm F E W} {x₀ w₀ : W} {n : ℕ}

theorem gramAt_complement (v : Basis ι E W) (h' : HermitianForm F E (hypComplement h x₀ w₀))
    (hh' : ∀ x y, h'.toSesq x y = h.toSesq x y) (v' : Basis (Fin n) E (hypComplement h x₀ w₀))
    (w : InfinitePlace E) :
    gramAt h' v' w = (colMat v (fun k => (v' k : W)) w)ᴴ * gramAt h v w *
      colMat v (fun k => (v' k : W)) w := by
  ext k l
  have e := sesq_mul (gramAt h v w) (colMat v (fun k => (v' k : W)) w)
    (colMat v (fun k => (v' k : W)) w) (Pi.single k 1) (Pi.single l 1)
  rw [← vecAt_basis v' k w, ← vecAt_basis v' l w, ← vecAt_coe, ← vecAt_coe,
    ← HermAtPlace.proof, ← hh', vecAt_basis, vecAt_basis] at e
  change w.embedding (h'.toSesq (v' k) (v' l)) = _
  rw [← e]
  simp [dotProduct, Pi.single_apply]

theorem frame (v : Basis ι E W) (hp : IsHyperbolicPair h x₀ w₀)
    (h' : HermitianForm F E (hypComplement h x₀ w₀)) (hh' : ∀ x y, h'.toSesq x y = h.toSesq x y)
    (v' : Basis (Fin n) E (hypComplement h x₀ w₀)) (w : InfinitePlace E) :
    (gramAt h v w)ᴴ = gramAt h v w ∧
    IsUnit ((colMat v (fun k => (v' k : W)) w)ᴴ * gramAt h v w *
      colMat v (fun k => (v' k : W)) w).det ∧
    (colMat v (fun k => (v' k : W)) w)ᴴ *ᵥ (gramAt h v w *ᵥ vecAt v x₀ w) = 0 ∧
    (colMat v (fun k => (v' k : W)) w)ᴴ *ᵥ (gramAt h v w *ᵥ vecAt v w₀ w) = 0 ∧
    star (vecAt v x₀ w) ⬝ᵥ (gramAt h v w *ᵥ vecAt v x₀ w) = 0 ∧
    star (vecAt v w₀ w) ⬝ᵥ (gramAt h v w *ᵥ vecAt v w₀ w) = 0 ∧
    star (vecAt v x₀ w) ⬝ᵥ (gramAt h v w *ᵥ vecAt v w₀ w) = 1 ∧
    ∀ z, ∃ (a b : ℂ) (c : Fin n → ℂ), z = a • vecAt v x₀ w + b • vecAt v w₀ w +
      colMat v (fun k => (v' k : W)) w *ᵥ c := by
  refine ⟨(GramAtData.proof h v w).1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← gramAt_complement v h' hh' v' w]
    exact (GramAtData.proof h' v' w).2
  · funext k
    rw [conjTranspose_mulVec_colMat, ← HermAtPlace.proof, Pi.zero_apply,
      ComplementExtension.toSesq_swap_eq_zero (mem_hypComplement.1 (v' k).2).1, map_zero]
  · funext k
    rw [conjTranspose_mulVec_colMat, ← HermAtPlace.proof, Pi.zero_apply,
      ComplementExtension.toSesq_swap_eq_zero (mem_hypComplement.1 (v' k).2).2, map_zero]
  · rw [← HermAtPlace.proof, hp.1, map_zero]
  · rw [← HermAtPlace.proof, hp.2.1, map_zero]
  · rw [← HermAtPlace.proof, hp.2.2, map_one]
  · have hx : ∀ x : W, vecAt v x w = w.embedding (h.toSesq w₀ x) • vecAt v x₀ w +
        w.embedding (h.toSesq x₀ x) • vecAt v w₀ w +
        colMat v (fun k => (v' k : W)) w *ᵥ vecAt v' (ComplementExtension.proj hp x) w := by
      intro x
      conv_lhs => rw [← ComplementExtension.split hp x]
      rw [vecAt_add, vecAt_add, vecAt_smul, vecAt_smul, vecAt_coe v v']
      abel
    intro z
    have hz : z = ∑ i, z i • vecAt v (v i) w := by
      funext j
      simp only [Finset.sum_apply, Pi.smul_apply, vecAt_basis, Pi.single_apply, smul_eq_mul, mul_ite,
        mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    refine ⟨∑ i, z i * w.embedding (h.toSesq w₀ (v i)), ∑ i, z i * w.embedding (h.toSesq x₀ (v i)),
      ∑ i, z i • vecAt v' (ComplementExtension.proj hp (v i)) w, ?_⟩
    have hx' : ∀ i, vecAt v (v i) w = _ := fun i => hx (v i)
    conv_lhs => rw [hz]
    simp only [hx', smul_add, Finset.sum_add_distrib, Finset.sum_smul, smul_smul, mulVec_sum,
      mulVec_smul]

end

end GroundTheory.Heights₂.Heights.FiniteCovolume.StabilizerLevi
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PTorusEmbedding
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix

noncomputable section

namespace TorusEmbedding

section Linear

variable {ι : Type*} [Fintype ι]

def pair (H : Matrix ι ι ℂ) (u z : ι → ℂ) : ℂ := star u ⬝ᵥ (H *ᵥ z)

variable {H : Matrix ι ι ℂ} {X Y : ι → ℂ}

theorem pair_add (u z z' : ι → ℂ) : pair H u (z + z') = pair H u z + pair H u z' := by
  simp [pair, mulVec_add, dotProduct_add]

theorem pair_smul (u z : ι → ℂ) (c : ℂ) : pair H u (c • z) = c * pair H u z := by
  simp [pair, mulVec_smul, dotProduct_smul]

theorem add_pair (u u' z : ι → ℂ) : pair H (u + u') z = pair H u z + pair H u' z := by
  simp [pair, add_dotProduct]

theorem smul_pair (u z : ι → ℂ) (c : ℂ) : pair H (c • u) z = starRingEnd ℂ c * pair H u z := by
  simp [pair, star_smul, smul_dotProduct]

theorem pair_swap (hH : H.IsHermitian) (u z : ι → ℂ) :
    pair H u z = starRingEnd ℂ (pair H z u) := by
  rw [pair, pair, dotProduct_mulVec, ← RCLike.star_def, ← star_dotProduct_star, star_star,
    star_mulVec, hH.eq]

variable [DecidableEq ι]

def torusMat (H : Matrix ι ι ℂ) (X Y : ι → ℂ) (s t : ℂ) : Matrix ι ι ℂ :=
  1 + (s - 1) • vecMulVec X (star Y ᵥ* H) + (t - 1) • vecMulVec Y (star X ᵥ* H)

theorem torusMat_mulVec (s t : ℂ) (z : ι → ℂ) :
    torusMat H X Y s t *ᵥ z = z + ((s - 1) * pair H Y z) • X + ((t - 1) * pair H X z) • Y := by
  simp only [torusMat, add_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec, pair,
    dotProduct_mulVec, op_smul_eq_smul, smul_smul]

theorem torusMat_one_one : torusMat H X Y 1 1 = 1 := by
  simp [torusMat]

theorem pair_Y_torusMat (hYY : pair H Y Y = 0) (hYX : pair H Y X = 1) (s t : ℂ) (z : ι → ℂ) :
    pair H Y (torusMat H X Y s t *ᵥ z) = s * pair H Y z := by
  rw [torusMat_mulVec, pair_add, pair_add, pair_smul, pair_smul, hYX, hYY]; ring

theorem pair_X_torusMat (hXX : pair H X X = 0) (hXY : pair H X Y = 1) (s t : ℂ) (z : ι → ℂ) :
    pair H X (torusMat H X Y s t *ᵥ z) = t * pair H X z := by
  rw [torusMat_mulVec, pair_add, pair_add, pair_smul, pair_smul, hXX, hXY]; ring

theorem torusMat_mul (hXX : pair H X X = 0) (hYY : pair H Y Y = 0) (hXY : pair H X Y = 1)
    (hYX : pair H Y X = 1) (s t s' t' : ℂ) :
    torusMat H X Y s t * torusMat H X Y s' t' = torusMat H X Y (s * s') (t * t') := by
  refine mulVec_injective (funext fun z => ?_)
  rw [← mulVec_mulVec, torusMat_mulVec s t, pair_Y_torusMat hYY hYX, pair_X_torusMat hXX hXY,
    torusMat_mulVec s' t', torusMat_mulVec]
  module

theorem torusMat_mulVec_X (hXX : pair H X X = 0) (hYX : pair H Y X = 1) (s t : ℂ) :
    torusMat H X Y s t *ᵥ X = s • X := by
  rw [torusMat_mulVec, hYX, hXX]; module

theorem torusMat_mulVec_Y (hYY : pair H Y Y = 0) (hXY : pair H X Y = 1) (s t : ℂ) :
    torusMat H X Y s t *ᵥ Y = t • Y := by
  rw [torusMat_mulVec, hYY, hXY]; module

theorem torusMat_mulVec_orth (s t : ℂ) (z : ι → ℂ) (hX : pair H X z = 0) (hY : pair H Y z = 0) :
    torusMat H X Y s t *ᵥ z = z := by
  rw [torusMat_mulVec, hX, hY]; simp

theorem torusMat_unitary (hH : H.IsHermitian) (hXX : pair H X X = 0) (hYY : pair H Y Y = 0)
    (hXY : pair H X Y = 1) (hYX : pair H Y X = 1) (s t : ℂ) (hst : starRingEnd ℂ s * t = 1) :
    (torusMat H X Y s t)ᴴ * H * torusMat H X Y s t = H := by
  have hts : starRingEnd ℂ t * s = 1 := by
    have := congrArg (starRingEnd ℂ) hst
    simpa [mul_comm] using this
  have key : ∀ u z : ι → ℂ, pair H (torusMat H X Y s t *ᵥ u) (torusMat H X Y s t *ᵥ z) =
      pair H u z := by
    intro u z
    conv_lhs => rw [torusMat_mulVec s t u]
    rw [add_pair, add_pair, smul_pair, smul_pair, pair_Y_torusMat hYY hYX,
      pair_X_torusMat hXX hXY, torusMat_mulVec, pair_add, pair_add, pair_smul, pair_smul,
      pair_swap hH u X, pair_swap hH u Y]
    simp only [map_mul, map_sub, map_one]
    linear_combination (pair H X z * starRingEnd ℂ (pair H Y u)) * hst +
      (pair H Y z * starRingEnd ℂ (pair H X u)) * hts
  refine mulVec_injective (funext fun z => ?_)
  refine dotProduct_eq _ _ fun u => ?_
  rw [dotProduct_comm, dotProduct_comm (H *ᵥ z)]
  have := key (star u) z
  simp only [pair, star_star] at this
  rw [← this, star_mulVec, star_star]
  simp only [dotProduct_mulVec, vecMul_vecMul]

def torusGL (H : Matrix ι ι ℂ) (X Y : ι → ℂ) (hXX : pair H X X = 0) (hYY : pair H Y Y = 0)
    (hXY : pair H X Y = 1) (hYX : pair H Y X = 1) (a : ℂˣ) : GL ι ℂ where
  val := torusMat H X Y a (starRingEnd ℂ ↑a⁻¹)
  inv := torusMat H X Y ↑a⁻¹ (starRingEnd ℂ a)
  val_inv := by
    rw [torusMat_mul hXX hYY hXY hYX, Units.mul_inv, ← map_mul, Units.inv_mul, map_one,
      torusMat_one_one]
  inv_val := by
    rw [torusMat_mul hXX hYY hXY hYX, Units.inv_mul, ← map_mul, Units.mul_inv, map_one,
      torusMat_one_one]

end Linear

section Places

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {h : HermitianForm F E W} {v : Basis ι E W}

omit [NumberField F] [NumberField E] [IsTotallyReal F] [IsTotallyComplex E] in

theorem place_pairs (h1 : HermAtPlace.Statement h v) (h2 : GramAtData.Statement h v) {x₀ w₀ : W}
    (hp : IsHyperbolicPair h x₀ w₀) (w : InfinitePlace E) :
    pair (gramAt h v w) (vecAt v x₀ w) (vecAt v x₀ w) = 0 ∧
      pair (gramAt h v w) (vecAt v w₀ w) (vecAt v w₀ w) = 0 ∧
      pair (gramAt h v w) (vecAt v x₀ w) (vecAt v w₀ w) = 1 ∧
      pair (gramAt h v w) (vecAt v w₀ w) (vecAt v x₀ w) = 1 := by
  obtain ⟨hxx, hww, hxw⟩ := hp
  have e : ∀ x y, pair (gramAt h v w) (vecAt v x w) (vecAt v y w) = w.embedding (h.toSesq x y) :=
    fun x y => (h1 w x y).symm
  refine ⟨by rw [e, hxx, map_zero], by rw [e, hww, map_zero], by rw [e, hxw, map_one], ?_⟩
  rw [pair_swap (h2 w).1, e, hxw, map_one, map_one]

variable (h1 : HermAtPlace.Statement h v) (h2 : GramAtData.Statement h v) {x₀ w₀ : W}
  (hp : IsHyperbolicPair h x₀ w₀)

def torusAt (w : InfinitePlace E) (a : ℂˣ) : GL ι ℂ :=
  torusGL (gramAt h v w) (vecAt v x₀ w) (vecAt v w₀ w) (place_pairs h1 h2 hp w).1
    (place_pairs h1 h2 hp w).2.1 (place_pairs h1 h2 hp w).2.2.1 (place_pairs h1 h2 hp w).2.2.2 a

omit [NumberField F] [NumberField E] [IsTotallyReal F] [IsTotallyComplex E] in
theorem torusAt_mem (a : InfinitePlace E → ℂˣ) :
    (fun w => torusAt h1 h2 hp w (a w)) ∈ archUnitary h v := by
  rw [mem_archUnitary]
  intro w
  obtain ⟨hXX, hYY, hXY, hYX⟩ := place_pairs h1 h2 hp w
  have hc : ∀ M : Matrix ι ι ℂ, (M.map (starRingEnd ℂ))ᵀ = Mᴴ := fun M => by
    ext i j; simp [conjTranspose_apply]
  rw [hc]
  refine torusMat_unitary (h2 w).1 hXX hYY hXY hYX _ _ ?_
  rw [← map_mul, Units.mul_inv, map_one]

def torusHom : (InfinitePlace E → ℂˣ) →* archUnitary h v where
  toFun a := ⟨fun w => torusAt h1 h2 hp w (a w), torusAt_mem h1 h2 hp a⟩
  map_one' := Subtype.ext (funext fun w => Units.ext (by
    simp [torusAt, torusGL, torusMat_one_one]))
  map_mul' a b := Subtype.ext (funext fun w => Units.ext (by
    obtain ⟨hXX, hYY, hXY, hYX⟩ := place_pairs h1 h2 hp w
    simp only [torusAt, torusGL, Subgroup.coe_mul, Pi.mul_apply, Units.val_mul]
    rw [torusMat_mul hXX hYY hXY hYX, ← map_mul, ← Units.val_mul, ← Units.val_mul,
      ← _root_.mul_inv_rev, mul_comm (b w)]))

theorem continuous_torusHom : Continuous (torusHom h1 h2 hp) := by
  refine Continuous.subtype_mk (continuous_pi fun w => Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · change Continuous fun a : InfinitePlace E → ℂˣ => torusMat (gramAt h v w) (vecAt v x₀ w)
      (vecAt v w₀ w) (a w : ℂ) (starRingEnd ℂ ↑(a w)⁻¹)
    unfold torusMat
    fun_prop
  · change Continuous fun a : InfinitePlace E → ℂˣ => torusMat (gramAt h v w) (vecAt v x₀ w)
      (vecAt v w₀ w) ↑(a w)⁻¹ (starRingEnd ℂ (a w : ℂ))
    unfold torusMat
    fun_prop

end Places

section Main

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem proof (h : HermitianForm F E W) (v : Basis ι E W) (h1 : HermAtPlace.Statement h v)
    (h2 : GramAtData.Statement h v) : TorusEmbedding.Statement h v := by
  intro x₀ w₀ hp
  refine ⟨torusHom h1 h2 hp, continuous_torusHom h1 h2 hp, fun a w => ?_⟩
  obtain ⟨hXX, hYY, hXY, hYX⟩ := place_pairs h1 h2 hp w
  refine ⟨torusMat_mulVec_X hXX hYX _ _, ?_, fun z hX hY => torusMat_mulVec_orth _ _ z hX hY⟩
  change torusMat _ _ _ _ _ *ᵥ _ = _
  rw [torusMat_mulVec_Y hYY hXY, Units.val_inv_eq_inv_val, map_inv₀]

theorem closed (h : HermitianForm F E W) (v : Basis ι E W) : TorusEmbedding.Statement h v :=
  proof h v (HermAtPlace.proof h v) (GramAtData.proof h v)

end Main

end TorusEmbedding

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PTorusModulus
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix MeasureTheory
open scoped ENNReal NNReal

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [NumberField F] [NumberField E] [IsTotallyReal F] [IsTotallyComplex E] in

theorem TorusModulus.commute (h : HermitianForm F E W) (v : Basis ι E W)
    (h1 : HermAtPlace.Statement h v) (h2 : GramAtData.Statement h v) {x₀ w₀ : W}
    (hp : IsHyperbolicPair h x₀ w₀) (g : archUnitary h v) (a : InfinitePlace E → ℂ)
    (hgx : ∀ w, ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w =
      a w • vecAt v x₀ w)
    (hgw : ∀ w, ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v w₀ w =
      (starRingEnd ℂ (a w))⁻¹ • vecAt v w₀ w)
    (hgY : ∀ w (z : ι → ℂ), star (vecAt v x₀ w) ⬝ᵥ (gramAt h v w *ᵥ z) = 0 →
      star (vecAt v w₀ w) ⬝ᵥ (gramAt h v w *ᵥ z) = 0 →
      ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ z = z)
    (k : archUnitary h v) (hk : k ∈ vecFixGroup h v x₀ ⊓ vecFixGroup h v w₀) : g * k = k * g := by
  obtain ⟨hkx, hkw⟩ := Subgroup.mem_inf.1 hk
  apply Subtype.ext
  funext w
  apply Units.ext
  simp only [Subgroup.coe_mul, Pi.mul_apply, Units.val_mul]
  refine matrix_ext_mulVec fun z => ?_
  have hH := (h2 w).1
  have hAA : hForm (gramAt h v w) (vecAt v x₀ w) (vecAt v x₀ w) = 0 := by
    rw [hForm, ← h1 w, hp.1, map_zero]
  have hBB : hForm (gramAt h v w) (vecAt v w₀ w) (vecAt v w₀ w) = 0 := by
    rw [hForm, ← h1 w, hp.2.1, map_zero]
  have hAB : hForm (gramAt h v w) (vecAt v x₀ w) (vecAt v w₀ w) = 1 := by
    rw [hForm, ← h1 w, hp.2.2, map_one]
  have hBA : hForm (gramAt h v w) (vecAt v w₀ w) (vecAt v x₀ w) = 1 := by
    rw [← hForm_conj hH, hAB, map_one]
  have hKu : (((k : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ))ᴴ * gramAt h v w *
      ((k : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) = gramAt h v w :=
    mem_archUnitary.1 k.2 w
  set H := gramAt h v w
  set A := vecAt v x₀ w
  set B := vecAt v w₀ w
  set G := ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ)
  set K := ((k : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ)
  have hKA : K *ᵥ A = A := hkx w
  have hKB : K *ᵥ B = B := hkw w
  set y := z - hForm H B z • A - hForm H A z • B with hy
  have hyA : hForm H A y = 0 := by
    rw [hy, hForm_sub_right, hForm_sub_right, hForm_smul_right, hForm_smul_right, hAA, hAB]
    ring
  have hyB : hForm H B y = 0 := by
    rw [hy, hForm_sub_right, hForm_sub_right, hForm_smul_right, hForm_smul_right, hBA, hBB]
    ring
  have hKyA : hForm H A (K *ᵥ y) = 0 := by
    have e := hForm_mulVec_of_unitary H hKu A y
    rw [hKA] at e
    rw [e, hyA]
  have hKyB : hForm H B (K *ᵥ y) = 0 := by
    have e := hForm_mulVec_of_unitary H hKu B y
    rw [hKB] at e
    rw [e, hyB]
  have hGy : G *ᵥ y = y := hgY w y hyA hyB
  have hGKy : G *ᵥ (K *ᵥ y) = K *ᵥ y := hgY w _ hKyA hKyB
  have hGA : G *ᵥ A = a w • A := hgx w
  have hGB : G *ᵥ B = (starRingEnd ℂ (a w))⁻¹ • B := hgw w
  have hz : z = y + hForm H B z • A + hForm H A z • B := by rw [hy]; abel
  rw [← mulVec_mulVec, ← mulVec_mulVec, hz]
  simp only [mulVec_add, mulVec_smul, hKA, hKB, hGy, hGKy, hGA, hGB]

theorem TorusModulus.proof (h : HermitianForm F E W) (v : Basis ι E W)
    (h1 : HermAtPlace.Statement h v) (h2 : GramAtData.Statement h v)
    (h3 : ComplementForm.Statement h) (h4 : StabilizerLevi.Statement h v)
    (h5 : UnipotentModulus.Statement h v) (h6 : RadicalTorusModulus.Statement h v)
    (h7 : ∀ (x₀ w₀ : W) (h' : HermitianForm F E (hypComplement h x₀ w₀)) (n : ℕ)
      (v' : Basis (Fin n) E (hypComplement h x₀ w₀)),
      SemidirectHaar.Statement (archUnitary h v) (archUnitary h' v')) :
    TorusModulus.Statement h v := by
  classical
  intro x₀ w₀ hp g a hgx hgw hgY ν _ f hf
  have : FiniteDimensional E W := Module.Finite.of_basis v
  obtain ⟨h', hh'⟩ := h3 x₀ w₀ hp
  let v' := Module.finBasis E (hypComplement h x₀ w₀)
  obtain ⟨i, q, hic, hqc, hqi, hker, hiw, -⟩ := h4 x₀ w₀ hp h' hh' _ v'
  let τ : archUnitary h' v' →* archUnitary h v := (vecFixGroup h v x₀).subtype.comp i
  have hτc : Continuous τ := continuous_subtype_val.comp hic
  have hτmem : ∀ t, τ t ∈ vecFixGroup h v x₀ ⊓ vecFixGroup h v w₀ :=
    fun t => Subgroup.mem_inf.2 ⟨(i t).2, hiw t⟩
  have hnorm : ∀ t, ∀ x ∈ unipRadical h v x₀, τ t * x * (τ t)⁻¹ ∈ unipRadical h v x₀ := by
    intro t x hx
    have hxP : x ∈ vecFixGroup h v x₀ := unipRadical_le_vecFixGroup h v x₀ hx
    have e := (hker (i t * ⟨x, hxP⟩ * (i t)⁻¹)).1 (by
      rw [map_mul, map_mul, map_inv, hqi, (hker ⟨x, hxP⟩).2 hx, mul_one, mul_inv_cancel])
    simpa [τ] using e
  have hinj : ∀ t, τ t ∈ unipRadical h v x₀ → t = 1 := by
    intro t ht
    rw [← hqi t]
    exact (hker (i t)).2 ht
  have hdec : ∀ p : vecFixGroup h v x₀, (p : archUnitary h v) * (τ (q p))⁻¹ ∈ unipRadical h v x₀ := by
    intro p
    have e := (hker (p * (i (q p))⁻¹)).1 (by rw [map_mul, map_inv, hqi, mul_inv_cancel])
    simpa [τ] using e
  let νN : Measure (unipRadical h v x₀) := Measure.haar
  let ρ : Measure (archUnitary h' v') := Measure.haar
  have hδ : ∀ (t : archUnitary h' v') (f : archUnitary h v → ℝ≥0∞), Measurable f →
      ∫⁻ x, f (τ t * x * (τ t)⁻¹) ∂νN = ((1 : ℝ≥0) : ℝ≥0∞) * ∫⁻ x, f x ∂νN := by
    intro t f hf
    have e := h5 x₀ w₀ hp νN (τ t) (hτmem t)
    have hm : Measurable fun n : unipRadical h v x₀ => τ t * (n : archUnitary h v) * (τ t)⁻¹ :=
      ((continuous_const.mul continuous_subtype_val).mul continuous_const).measurable
    rw [ENNReal.coe_one, one_mul, ← lintegral_map hf hm, e, lintegral_map hf measurable_subtype_coe]
  obtain ⟨c, -, hc⟩ := h7 x₀ w₀ h' _ v' (vecFixGroup h v x₀) (unipRadical h v x₀)
    (isClosed_vecFixGroup h v x₀) (isClosed_unipRadical h v x₀) (unipRadical_le_vecFixGroup h v x₀)
    τ q (fun _ => 1) hτc hqc continuous_const (fun t => (i t).2) hnorm hinj hdec ν νN ρ hδ
  have hconj : ∀ t (n : archUnitary h v), g * (n * τ t) * g⁻¹ = g * n * g⁻¹ * τ t := by
    intro t n
    have e : τ t * g⁻¹ = g⁻¹ * τ t := by
      rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, TorusModulus.commute h v h1 h2 hp g a hgx hgw hgY _
        (hτmem t), mul_inv_cancel_right]
    calc g * (n * τ t) * g⁻¹ = g * n * (τ t * g⁻¹) := by group
      _ = g * n * (g⁻¹ * τ t) := by rw [e]
      _ = g * n * g⁻¹ * τ t := by group
  set K := ∏ w, ‖a w‖ₑ⁻¹ ^ (2 * (finrank E W - 1))
  have hφ : Measurable fun y : archUnitary h v => f (g * y * g⁻¹) :=
    hf.comp ((continuous_const.mul continuous_id).mul continuous_const).measurable
  have step : ∀ t, ∫⁻ x : unipRadical h v x₀, f (g * (x * τ t) * g⁻¹) ∂νN =
      K * ∫⁻ x : unipRadical h v x₀, f (x * τ t) ∂νN := by
    intro t
    simp_rw [hconj t]
    exact h6 x₀ w₀ hp g a hgx hgw hgY νN (fun y => f (y * τ t))
      (hf.comp (continuous_id.mul continuous_const).measurable)
  have hmeas : Measurable fun t => ∫⁻ x : unipRadical h v x₀, f (x * τ t) ∂νN :=
    Measurable.lintegral_prod_right' (f := fun p : archUnitary h' v' × unipRadical h v x₀ =>
      f (p.2 * τ p.1)) (hf.comp ((continuous_subtype_val.comp continuous_snd).mul
        (hτc.comp continuous_fst)).measurable)
  calc ∫⁻ x, f (g * x * g⁻¹) ∂ν
      = c * ∫⁻ t, ((1 : ℝ≥0) : ℝ≥0∞) *
          ∫⁻ x : unipRadical h v x₀, f (g * (x * τ t) * g⁻¹) ∂νN ∂ρ := hc _ hφ
    _ = c * ∫⁻ t, K * ∫⁻ x : unipRadical h v x₀, f (x * τ t) ∂νN ∂ρ := by
        simp_rw [ENNReal.coe_one, one_mul, step]
    _ = K * (c * ∫⁻ t, ((1 : ℝ≥0) : ℝ≥0∞) * ∫⁻ x : unipRadical h v x₀, f (x * τ t) ∂νN ∂ρ) := by
        rw [lintegral_const_mul _ hmeas]
        simp only [ENNReal.coe_one, one_mul]
        ring
    _ = K * ∫⁻ x, f x ∂ν := by rw [hc f hf]

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

