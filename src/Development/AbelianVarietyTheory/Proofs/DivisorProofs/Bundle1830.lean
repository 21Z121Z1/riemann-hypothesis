import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixTwoByTwoFinTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureUAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1796
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0031
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0032
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1799
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0492
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0702

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviChartBlockDiagonalAdjoint
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.MixModel GlobalTheory.SWLit
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (UA incM ratU)
open GlobalTheory.WeilM (Darboux symp schA thetaSum UG)
open GlobalTheory.SiegelFormula (coord)
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SWLink

namespace GlobalTheory.SWLink.LeviChart
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model

theorem exists_blockMatrixTwoByTwoFin_eq {R : Type} {n : ℕ} (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : ∃ a b c d, M = blk4 a b c d := by
  refine ⟨(M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁, (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₂,
    (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁, (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂, ?_⟩
  unfold blk4
  rw [Matrix.fromBlocks_toBlocks]
  simp

theorem submatrix_fromBlocks_levi {R : Type} {n : ℕ} (a b c d : Matrix (Fin n) (Fin n) R) :
    (blk4 a b c d).submatrix finSumFinEquiv finSumFinEquiv = Matrix.fromBlocks a b c d := by
  simp [blk4]

theorem diag_blocks {R : Type} [CommRing R] {n : ℕ} (h2 : ∀ z : Matrix (Fin n) (Fin n) R, z + z = 0 → z = 0)
    {U : Matrix (Fin (n + n)) (Fin (n + n)) R} {Z Z' a b c d : Matrix (Fin n) (Fin n) R} (hZ : Z' * Z = 1)
    (h : U * blk4 1 Z 1 (-Z) = blk4 1 Z 1 (-Z) * blk4 a b c d) (hU : KeepsDiag finSumFinEquiv U) :
    c = 0 ∧ a = leviMat finSumFinEquiv U := by
  obtain ⟨p, q, r, s, rfl⟩ := exists_blockMatrixTwoByTwoFin_eq U
  rw [submatrix_fromBlocks_mul, submatrix_fromBlocks_mul] at h
  obtain ⟨h1, -, h3, -⟩ := blockMatrixTwoByTwoFin_injective h
  simp only [KeepsDiag, leviMat, submatrix_fromBlocks_levi, Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂,
    Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂] at hU ⊢
  simp only [mul_one, one_mul, neg_mul] at h1 h3
  have h4 : Z * c = 0 := h2 _ (by
    have : a + Z * c = a + -(Z * c) := by rw [← h1, ← h3, hU]
    exact eq_neg_iff_add_eq_zero.1 (add_left_cancel this))
  refine ⟨by rw [← one_mul c, ← hZ, mul_assoc, h4, mul_zero], by rw [h1, h4, add_zero]⟩

theorem anti_blocks {R : Type} [CommRing R] {n : ℕ} (h2 : ∀ z : Matrix (Fin n) (Fin n) R, z + z = 0 → z = 0)
    {U : Matrix (Fin (n + n)) (Fin (n + n)) R} {Z a b c d : Matrix (Fin n) (Fin n) R}
    (h : U * blk4 1 Z 1 (-Z) = blk4 1 Z 1 (-Z) * blk4 a b c d)
    (hU : ∀ w ∈ antiSub R finSumFinEquiv, U *ᵥ w ∈ antiSub R finSumFinEquiv) : b = 0 := by
  obtain ⟨p, q, r, s, rfl⟩ := exists_blockMatrixTwoByTwoFin_eq U
  rw [submatrix_fromBlocks_mul, submatrix_fromBlocks_mul] at h
  obtain ⟨-, h1, -, h3⟩ := blockMatrixTwoByTwoFin_injective h
  have h4 : p * Z + q * -Z = -(r * Z + s * -Z) := by
    refine Matrix.ext_of_mulVec_single fun j => ?_
    have := hU _ ((pairVec_mem_antiSub finSumFinEquiv).2
      (neg_neg _).symm : pairVec finSumFinEquiv (Z *ᵥ Pi.single j 1) (-(Z *ᵥ Pi.single j 1)) ∈ _)
    rw [mulVec_pairVec, pairVec_mem_antiSub, submatrix_fromBlocks_levi] at this
    simp only [Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂,
      Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂, ← Matrix.neg_mulVec, Matrix.mulVec_mulVec,
      ← Matrix.add_mulVec] at this
    exact this
  rw [h1, h3] at h4
  simp only [one_mul, neg_mul] at h4
  refine h2 _ ?_
  have := eq_neg_iff_add_eq_zero.1 h4
  rw [← this]; abel

theorem inv_cancel {M : Type} [Monoid M] {x y d : M} (h1 : y * x = 1) (h2 : x * d = 1) : d = y := by
  rw [← one_mul d, ← h1, mul_assoc, h2, mul_one]

variable {D : D7} {n : ℕ}

theorem adj_inv_mul (a : GL (Fin n) (AE D)) : (adj (a⁻¹).1 : Mx D n n) * adj a.1 = 1 := by
  rw [← adj_mul]; simp [adj_one]

theorem adj_mul_eq_one {g : G D n} {a b d : Mx D n n} (hg : mat g = blk4 a b 0 d) : adj a * d = 1 := by
  have h : adj (mat g) * JR (AF D.host.F) (Jst D n) * mat g = JR (AF D.host.F) (Jst D n) := g.2
  rw [JR_Jst, hg] at h
  simp only [adelicConjTranspose_blockMatrixTwoByTwoFin, submatrix_fromBlocks_mul, adj_zero, mul_zero, zero_mul, mul_one, add_zero, zero_add] at h
  exact (blockMatrixTwoByTwoFin_injective h).2.1

theorem rat_witt {J : Matrix (Fin n) (Fin n) D.host.E} {T : GL (Fin (n + n)) D.host.E}
    (hT : IsWittBasis D.sp.cm.sig J 1 T) :
    ∃ Z Z' : Mx D n n, Z' * Z = 1 ∧ (rat T.1 : Mx D (n + n) (n + n)) = blk4 1 Z 1 (-Z) := by
  obtain ⟨Z, hZ, hT⟩ := hT
  rw [one_smul, ← Matrix.smul_mul] at hZ
  have h1 : (rat ((2 : D.host.E) • J) : Mx D n n) * cj (rat Z) = 1 := by rw [cj_rat, ← rat_mul, hZ, rat_one]
  have h2 : (cj (rat ((2 : D.host.E) • J)) : Mx D n n) * rat Z = 1 := by
    have := congrArg cj h1
    rwa [cj_mul, cj_cj, cj_one] at this
  exact ⟨rat Z, _, h2, by rw [hT, blk_eq, rat_fromBlocks_map, rat_one, rat_neg]⟩

theorem levi_form {M : Mx D (n + n) (n + n)} {x b d : Mx D n n} (a : GL (Fin n) (AE D)) (e : x = a.1)
    (h : M = blk4 x b 0 d) (hb : b = 0) (hd : adj x * d = 1) : M = blk4 a.1 0 0 (adj (a⁻¹).1) := by
  subst e
  rw [h, hb, inv_cancel (adj_inv_mul a) hd]

section
variable {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E} {T : GL (Fin (n + n)) D.host.E} {κ : UD D J₂ ≃* G D n}
  {J : Matrix (Fin n) (Fin n) D.host.E}

theorem siegel_blocks (hκ : IsChartW T κ) (hT : IsWittBasis D.sp.cm.sig J 1 T) {g : UD D J₂}
    (hk : KeepsDiag finSumFinEquiv (umat g)) : ∃ b d : Mx D n n,
      mat (κ g) = blk4 (leviMat finSumFinEquiv (umat g)) b 0 d ∧ adj (leviMat finSumFinEquiv (umat g)) * d = 1 ∧
      ((∀ w ∈ antiSub (AE D) finSumFinEquiv, umat g *ᵥ w ∈ antiSub (AE D) finSumFinEquiv) → b = 0) := by
  obtain ⟨Z, Z', hZ, hT⟩ := rat_witt hT
  obtain ⟨a, b, c, d, h⟩ := exists_blockMatrixTwoByTwoFin_eq (mat (κ g))
  have h1 := hκ.mul_eq g
  rw [hT, h] at h1
  have h2 : ∀ z : Mx D n n, z + z = 0 → z = 0 := fun z hz => eq_zero_of_add_self hz
  obtain ⟨hc, ha⟩ := diag_blocks (R := AE D) h2 hZ h1 hk
  have h3 := anti_blocks (R := AE D) h2 h1
  rw [hc, ha] at h
  exact ⟨b, d, h, adj_mul_eq_one h, h3⟩

theorem levi_chart (hκ : IsChartW T κ) (hT : IsWittBasis D.sp.cm.sig J 1 T) {g : UD D J₂}
    (hp : g ∈ leviSubOf finSumFinEquiv (uinc D J₂)) (a : GL (Fin n) (AE D))
    (e : leviMat finSumFinEquiv (umat g) = a.1) : mat (κ g) = blk4 a.1 0 0 (adj (a⁻¹).1) := by
  obtain ⟨hp1, hp2⟩ := Subgroup.mem_inf.1 hp
  obtain ⟨b, d, h, hd, hb⟩ := siegel_blocks hκ hT (g := g) (mem_siegelOf.1 hp1)
  exact levi_form a e h (hb fun w hw => (hp2 w).1 hw) hd

theorem unip_chart (hκ : IsChartW T κ) (hT : IsWittBasis D.sp.cm.sig J 1 T) {g : UD D J₂}
    (hg : g ∈ unipOf finSumFinEquiv (uinc D J₂)) : ∃ β : Mx D n n, mat (κ g) = blk4 1 β 0 1 := by
  obtain ⟨hg1, hg2⟩ := mem_unipOf.1 hg
  obtain ⟨b, d, h, hd, -⟩ := siegel_blocks hκ hT (g := g) (mem_siegelOf.1 hg1)
  have e : leviMat finSumFinEquiv (umat g) = 1 := hg2
  rw [e] at h hd
  rw [adj_one, one_mul] at hd
  exact ⟨b, by rw [h, hd]⟩

end

theorem levi_unip_chart : ∀ (D : D7) (n : ℕ) (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E) (T : GL (Fin (n + n)) D.host.E) (κ : UD D J₂ ≃* GlobalTheory.StdUnn.G D n), IsChartW T κ → ∀ J : Matrix (Fin n) (Fin n) D.host.E, IsWittBasis D.sp.cm.sig J 1 T → (∀ p : siegelOf finSumFinEquiv (uinc D J₂), (p : UD D J₂) ∈ leviSubOf finSumFinEquiv (uinc D J₂) → GlobalTheory.StdUnn.mat (κ p) = GlobalTheory.StdUnn.blk4 (leviOf finSumFinEquiv (uinc D J₂) p).1 0 0 (adj ((leviOf finSumFinEquiv (uinc D J₂) p)⁻¹).1)) ∧ ∀ b ∈ unipOf finSumFinEquiv (uinc D J₂), ∃ β : Mx D n n, GlobalTheory.StdUnn.mat (κ b) = GlobalTheory.StdUnn.blk4 1 β 0 1 :=
  fun _ _ _ _ _ hκ _ hT => ⟨fun p hp => levi_chart hκ hT hp _ (val_leviOf p).symm, fun _ hg => unip_chart hκ hT hg⟩

end GlobalTheory.SWLink.LeviChart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftECompFinOfAt
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HoweLocal
open scoped TensorProduct Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.HoweLocal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem singleFin_mul (v : Pl F) (a b : Fv F v) :
    GlobalTheory.AdelicU.singleFin v (a * b) = GlobalTheory.AdelicU.singleFin v a * GlobalTheory.AdelicU.singleFin v b := by
  apply GlobalTheory.AdelicU.af_ext
  intro u
  rw [map_mul (evalV F u)]
  by_cases hu : u = v
  · subst hu
    rw [GlobalTheory.AdelicU.evalV_singleFin_self, GlobalTheory.AdelicU.evalV_singleFin_self, GlobalTheory.AdelicU.evalV_singleFin_self]
  · rw [GlobalTheory.AdelicU.evalV_singleFin_ne hu, GlobalTheory.AdelicU.evalV_singleFin_ne hu, zero_mul]

theorem liftV_mul (v : Pl F) (a b : Fv F v) :
    GlobalTheory.LatVac.liftV v (a * b) = GlobalTheory.LatVac.liftV v a * GlobalTheory.LatVac.liftV v b := by
  change ((0 : Ainf F), GlobalTheory.AdelicU.singleFin v (a * b)) =
    ((0 : Ainf F), GlobalTheory.AdelicU.singleFin v a) * ((0 : Ainf F), GlobalTheory.AdelicU.singleFin v b)
  rw [Prod.mk_mul_mk, mul_zero, singleFin_mul]

theorem liftE_mul (v : Pl F) (x y : Fv F v ⊗[F] E) : liftE v (x * y) = liftE v x * liftE v y := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => rw [add_mul, map_add, hx, hx', map_add, add_mul]
  | tmul a e =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' hy hy' => rw [mul_add, map_add, hy, hy', map_add, mul_add]
    | tmul b f =>
      simp only [liftE, Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.map_tmul, LinearMap.id_coe, id_eq,
        liftV_mul]

theorem one_add_liftE_mul (v : Pl F) (x y : Fv F v ⊗[F] E) :
    (1 + liftE v (x - 1)) * (1 + liftE v (y - 1)) = 1 + liftE v (x * y - 1) := by
  have : x * y - 1 = (x - 1) + (y - 1) + (x - 1) * (y - 1) := by ring
  rw [this, map_add, map_add, liftE_mul]
  ring

theorem one_add_liftV_mul (v : Pl F) (x y : Fv F v) :
    (1 + GlobalTheory.LatVac.liftV v (x - 1)) * (1 + GlobalTheory.LatVac.liftV v (y - 1)) = 1 + GlobalTheory.LatVac.liftV v (x * y - 1) := by
  have : x * y - 1 = (x - 1) + (y - 1) + (x - 1) * (y - 1) := by ring
  rw [this, map_add, map_add, liftV_mul]
  ring

def liftU (v : Pl F) : (Fv F v ⊗[F] E)ˣ →* (AE F E)ˣ where
  toFun z := ⟨1 + liftE v ((z : Fv F v ⊗[F] E) - 1), 1 + liftE v (((z⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) - 1),
    by rw [one_add_liftE_mul, Units.mul_inv, sub_self, map_zero, add_zero],
    by rw [one_add_liftE_mul, Units.inv_mul, sub_self, map_zero, add_zero]⟩
  map_one' := by ext; simp
  map_mul' z w := by ext; simp only [Units.val_mul, Units.val_mk]; rw [one_add_liftE_mul]

def liftUF (v : Pl F) : (Fv F v)ˣ →* (AF F)ˣ where
  toFun a := ⟨1 + GlobalTheory.LatVac.liftV v ((a : Fv F v) - 1), 1 + GlobalTheory.LatVac.liftV v (((a⁻¹ : (Fv F v)ˣ) : Fv F v) - 1),
    by rw [one_add_liftV_mul, Units.mul_inv, sub_self, map_zero, add_zero],
    by rw [one_add_liftV_mul, Units.inv_mul, sub_self, map_zero, add_zero]⟩
  map_one' := by ext; simp
  map_mul' z w := by ext; simp only [Units.val_mul, Units.val_mk]; rw [one_add_liftV_mul]

theorem liftU_val (v : Pl F) (z : (Fv F v ⊗[F] E)ˣ) :
    ((liftU v z : (AE F E)ˣ) : AE F E) = 1 + liftE v ((z : Fv F v ⊗[F] E) - 1) := rfl

theorem liftUF_val (v : Pl F) (a : (Fv F v)ˣ) :
    ((liftUF v a : (AF F)ˣ) : AF F) = 1 + GlobalTheory.LatVac.liftV v ((a : Fv F v) - 1) := rfl

def locChr (χ : Chr F E) (v : Pl F) : (Fv F v ⊗[F] E)ˣ →* Circle := χ.comp (liftU v)

end GlobalTheory.HoweLocal

namespace GlobalTheory.HoweLocal

theorem norm_map_tensor {F E A B : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    [CommRing A] [CommRing B] [Algebra F A] [Algebra F B] (f : A →ₐ[F] B) (x : A ⊗[F] E) :
    Algebra.norm B (Algebra.TensorProduct.map f (AlgHom.id F E) x) = f (Algebra.norm A x) := by
  classical
  let b := Module.finBasis F E
  let bA := Algebra.TensorProduct.basis A b
  let bB := Algebra.TensorProduct.basis B b
  have hrep : ∀ (y : A ⊗[F] E) i, bB.repr (Algebra.TensorProduct.map f (AlgHom.id F E) y) i = f (bA.repr y i) := by
    intro y i
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' hy hy' => simp [map_add, hy, hy']
    | tmul a e =>
      simp [bA, bB, Algebra.TensorProduct.basis_repr_tmul, Algebra.smul_def]
  have hb : ∀ j, bB j = Algebra.TensorProduct.map f (AlgHom.id F E) (bA j) := by
    intro j; simp [bA, bB, Algebra.TensorProduct.basis_apply]
  rw [Algebra.norm_eq_matrix_det bB, Algebra.norm_eq_matrix_det bA]
  show _ = (f : A →+* B) _
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp only [Algebra.leftMulMatrix_eq_repr_mul, RingHom.mapMatrix_apply, Matrix.map_apply]
  rw [hb, ← map_mul, hrep]
  rfl

end GlobalTheory.HoweLocal

namespace GlobalTheory.HoweLocal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem liftU_algebraMap (v : Pl F) (a : (Fv F v)ˣ) :
    liftU (E := E) v (Units.map (algebraMap (Fv F v) (Fv F v ⊗[F] E) : Fv F v →* Fv F v ⊗[F] E) a) =
      Units.map (algebraMap (AF F) (AE F E) : AF F →* AE F E) (liftUF v a) := by
  ext
  rw [liftU_val, Units.coe_map, Units.coe_map, liftUF_val, MonoidHom.coe_coe, MonoidHom.coe_coe, map_add, map_one]
  congr 1
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.one_def,
    Algebra.algebraMap_self, RingHom.id_apply, Algebra.algebraMap_self, RingHom.id_apply, ← TensorProduct.sub_tmul]
  simp only [liftE, TensorProduct.map_tmul, LinearMap.id_coe, id_eq]

end GlobalTheory.HoweLocal

namespace GlobalTheory.HoweLocal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem liftE_compFin_of_at (v : Pl F) {z : AE F E} (hz : At (evFin F v) z) : liftE v (compFin F E v z) = z := by
  rw [← GlobalTheory.HoweLocal.LocCoords.liftV_one_smul]
  have h : (1 - GlobalTheory.LatVac.liftV v 1) • z = 0 := hz _ (by rw [map_sub, map_one, GlobalTheory.LatVac.evFin_liftV, sub_self])
  rw [sub_smul, one_smul, sub_eq_zero] at h
  exact h.symm

theorem liftU_compFin_of_at (v : Pl F) (a : (AE F E)ˣ) (ha : At (evFin F v) ((a : AE F E) - 1)) :
    liftU v (Units.map (compFin F E v : AE F E →* Fv F v ⊗[F] E) a) = a := by
  ext
  rw [liftU_val, Units.coe_map, MonoidHom.coe_coe, ← map_one (compFin F E v), ← map_sub, liftE_compFin_of_at v ha,
    add_sub_cancel]

end GlobalTheory.HoweLocal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFourierDoubleReflection
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeylFour
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.WeylFour.LocInv

variable {F : Type} [Field F] [NumberField F]

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

local instance borelFvLoc (v : Pl F) : BorelSpace (Fv F v) := ⟨rfl⟩

open GlobalTheory.SplitWeil

theorem norm_addChar_eq_one {v : Pl F} (χ : AddChar (Fv F v) ℂ) (hχ : Continuous χ) (x : Fv F v) :
    ‖χ x‖ = 1 := by
  have hb : ∀ y : Fv F v, ‖χ y‖ ≤ 1 := by
    intro y
    obtain ⟨s, hs⟩ : ∃ s : (Fv F v)ˣ, y ∈ cball s := by
      by_cases hy : y = 0
      · exact ⟨1, by simp [hy, cball]⟩
      · exact ⟨Units.mk0 y hy, by simp [cball]⟩
    obtain ⟨M, hM⟩ := (isCompact_cball s).exists_bound_of_continuousOn hχ.continuousOn
    have hn : ∀ n : ℕ, ‖χ y‖ ^ n ≤ M := by
      intro n
      have hmem : n • y ∈ cball s := by
        induction n with
        | zero => simp [cball]
        | succ n ih => rw [succ_nsmul]; exact add_mem_cball ih hs
      rw [← norm_pow, ← AddChar.map_nsmul_eq_pow]
      exact hM _ hmem
    by_contra h
    push_neg at h
    obtain ⟨n, hn'⟩ := pow_unbounded_of_one_lt M h
    exact absurd (hn n) (not_le.mpr hn')
  have h1 := hb x
  have h2 := hb (-x)
  have h3 : χ x * χ (-x) = 1 := by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have h4 : ‖χ x‖ * ‖χ (-x)‖ = 1 := by rw [← norm_mul, h3, norm_one]
  refine le_antisymm h1 ?_
  nlinarith [norm_nonneg (χ x), norm_nonneg (χ (-x))]

def toCirc {v : Pl F} (χ : AddChar (Fv F v) ℂ) (h : ∀ x, ‖χ x‖ = 1) : AddChar (Fv F v) Circle where
  toFun x := ⟨χ x, by simpa [Submonoid.unitSphere, mem_sphere_zero_iff_norm] using h x⟩
  map_zero_eq_one' := by
    apply Circle.ext
    simp
  map_add_eq_mul' a b := by
    apply Circle.ext
    exact χ.map_add_eq_mul a b

theorem coe_toCirc {v : Pl F} (χ : AddChar (Fv F v) ℂ) (h : ∀ x, ‖χ x‖ = 1) (x : Fv F v) :
    ((toCirc χ h x : Circle) : ℂ) = χ x := rfl

theorem continuous_psiAt' (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ) (v : Pl F) :
    Continuous (GlobalTheory.LatVac.psiAt ψ v) := by
  have hj : Continuous (GlobalTheory.LatVac.liftV (F := F) v) := by
    change Continuous fun a => ((0 : Ainf F), GlobalTheory.AdelicU.singleFin v a)
    exact continuous_const.prodMk (GlobalTheory.AdelicU.continuous_singleFin v)
  exact hψ.comp hj

theorem measV_selfDual (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (v : Pl F) (hne : ∃ x, psiLoc ψ v x ≠ 1) :
    ∃ (h : ∀ x, ‖GlobalTheory.LatVac.psiAt ψ v x‖ = 1) (c : (Fv F v)ˣ),
      HasConductor (toCirc _ h) c ∧ IsSelfDual (toCirc _ h) (measV ψ v) := by
  have hc := continuous_psiAt' ψ hψ.1 v
  have hn : ∀ x, ‖GlobalTheory.LatVac.psiAt ψ v x‖ = 1 := norm_addChar_eq_one _ hc
  have hcc : Continuous (toCirc _ hn) := Continuous.subtype_mk hc _
  have hne1 : toCirc _ hn ≠ 1 := by
    obtain ⟨x, hx⟩ := hne
    intro h1
    apply hx
    have := congrArg (fun χ : AddChar (Fv F v) Circle => ((χ x : Circle) : ℂ)) h1
    simpa [coe_toCirc, GlobalTheory.LatVac.psiAt_apply] using this
  obtain ⟨c, hcond⟩ := exists_hasConductor_of_continuous _ hcc hne1
  obtain ⟨ν, hν⟩ := exists_isSelfDual_of_hasConductor hcond
  have hex : ∃ ν, IsSelfDualFor (GlobalTheory.LatVac.psiAt ψ v) ν := ⟨ν, hν.1, fun f hf => hν.2 f hf⟩
  refine ⟨hn, c, hcond, ?_⟩
  have hm : measV ψ v = hex.choose := by
    unfold measV
    rw [dif_pos hex]
  rw [hm]
  exact ⟨hex.choose_spec.1, fun f hf => hex.choose_spec.2 f hf⟩

end GlobalTheory.WeylFour.LocInv

namespace GlobalTheory.WeylFour.LocInv

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem fourV_fourV : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ v : Pl F,
    (∃ x, psiLoc ψ v x ≠ 1) →
    ∀ (κ : Type) [Fintype κ], ∀ φ ∈ SB (κ → Fv F v), fourV ψ v (fourV ψ v φ) = fun x => φ (-x) := by
  intro F _ _ ψ hψ v hne κ _ φ hφ
  classical
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨hn, c, hcond, hself⟩ := measV_selfDual ψ hψ v hne
  haveI := hself.1
  haveI := GlobalTheory.SplitWeil.secondCountable (Fv F v)
  haveI := GlobalTheory.SplitWeil.t2Space (Fv F v)
  funext z
  have hinner : ∀ y, fourV ψ v φ y * GlobalTheory.LatVac.psiAt ψ v (y ⬝ᵥ z) =
      ∫ x, φ (x - z) * ((toCirc _ hn (x ⬝ᵥ y) : Circle) : ℂ) ∂(Measure.pi fun _ : κ => measV ψ v) := by
    intro y
    unfold fourV
    rw [← integral_mul_const]
    have h1 : ∀ x : κ → Fv F v, φ x * GlobalTheory.LatVac.psiAt ψ v (x ⬝ᵥ y) * GlobalTheory.LatVac.psiAt ψ v (y ⬝ᵥ z) =
        φ x * GlobalTheory.LatVac.psiAt ψ v ((x + z) ⬝ᵥ y) := by
      intro x
      rw [add_dotProduct, AddChar.map_add_eq_mul, dotProduct_comm z y, mul_assoc]
    simp only [h1]
    rw [← integral_sub_right_eq_self (μ := Measure.pi fun _ : κ => measV ψ v)
      (fun x => φ x * GlobalTheory.LatVac.psiAt ψ v ((x + z) ⬝ᵥ y)) z]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [sub_add_cancel, coe_toCirc]
  have hg : (fun x : κ → Fv F v => φ (x - z)) ∈ GlobalTheory.SplitWeil.SB (κ → Fv F v) :=
    ⟨hφ.1.comp_continuous (continuous_id.sub continuous_const),
      hφ.2.comp_homeomorph (Homeomorph.subRight z)⟩
  have h2 := (GlobalTheory.SplitWeil.FourierPi.fourier_pi_of_conductor hcond hself hg).2
  show ∫ y, fourV ψ v φ y * GlobalTheory.LatVac.psiAt ψ v (y ⬝ᵥ z) ∂(Measure.pi fun _ : κ => measV ψ v) = φ (-z)
  simp only [hinner]
  rw [h2, zero_sub]

end GlobalTheory.WeylFour.LocInv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFourierSchrodingerIntertwine
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeylFour
open scoped GlobalTheory.VacAny

namespace GlobalTheory.WeylFour

theorem schr_fourV_loc : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (v : Pl F) (κ : Type) [Fintype κ]
    (w : (κ → Fv F v) × (κ → Fv F v)) (φ : (κ → Fv F v) → ℂ),
    fourV ψ v (schr (GlobalTheory.LatVac.psiAt ψ v) w φ) = schr (GlobalTheory.LatVac.psiAt ψ v) (w.2, -w.1) (fourV ψ v φ) := by
  intro F _ _ ψ _ v κ _ w φ
  haveI hOc : CompactSpace (v.adicCompletionIntegers F) :=
    GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v
  haveI : LocallyCompactSpace (Fv F v) :=
    (isCompact_iff_compactSpace.2 hOc).locallyCompactSpace_of_mem_nhds_of_addGroup
      ((Valued.isOpen_valuationSubring _).mem_nhds (zero_mem (v.adicCompletionIntegers F)))
  haveI : SecondCountableTopology (Fv F v) := by
    have : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
    have : TopologicalSpace.SeparableSpace (Fv F v) :=
      ⟨⟨Set.range (algebraMap F (Fv F v)), Set.countable_range _,
        IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap F v⟩⟩
    exact UniformSpace.secondCountable_of_separable (Fv F v)
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  have hinv : (measV ψ v).IsAddLeftInvariant ∧ SigmaFinite (measV ψ v) := by
    unfold measV
    split_ifs with h
    · haveI := h.choose_spec.1
      exact ⟨inferInstance, inferInstance⟩
    · exact ⟨⟨fun g => by simp⟩, inferInstance⟩
  haveI := hinv.1
  haveI := hinv.2
  have h2 : (⅟2 : Fv F v) + ⅟2 = 1 := by rw [← two_mul, mul_invOf_self]
  funext y
  simp only [fourV, schr]
  set χ := GlobalTheory.LatVac.psiAt ψ v
  set μ := Measure.pi fun _ : κ => measV ψ v
  let g : (κ → Fv F v) → ℂ := fun x =>
    χ ((x - w.1) ⬝ᵥ w.2 + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2)) * φ x * χ ((x - w.1) ⬝ᵥ y)
  have hg : ∀ x, χ (x ⬝ᵥ w.2 + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2)) * φ (x + w.1) * χ (x ⬝ᵥ y) = g (x + w.1) := by
    intro x; simp only [g, add_sub_cancel_right]
  simp_rw [hg]
  rw [integral_add_right_eq_self g w.1, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [g]
  have key : (x - w.1) ⬝ᵥ w.2 + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2) + (x - w.1) ⬝ᵥ y =
      y ⬝ᵥ (-w.1) + ⅟(2 : Fv F v) * (w.2 ⬝ᵥ (-w.1)) + x ⬝ᵥ (y + w.2) := by
    simp only [sub_dotProduct, dotProduct_add, dotProduct_neg]
    rw [dotProduct_comm y w.1, dotProduct_comm w.2 w.1]
    linear_combination (w.1 ⬝ᵥ w.2) * h2
  calc χ ((x - w.1) ⬝ᵥ w.2 + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2)) * φ x * χ ((x - w.1) ⬝ᵥ y)
      = φ x * (χ ((x - w.1) ⬝ᵥ w.2 + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2)) * χ ((x - w.1) ⬝ᵥ y)) := by ring
    _ = φ x * χ (y ⬝ᵥ (-w.1) + ⅟(2 : Fv F v) * (w.2 ⬝ᵥ (-w.1)) + x ⬝ᵥ (y + w.2)) := by
      rw [← AddChar.map_add_eq_mul, key]
    _ = _ := by rw [AddChar.map_add_eq_mul]; ring

end GlobalTheory.WeylFour
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRationalPointsOfUnipotentCoordsRationalStatement
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_rationalPoints_of_unipotentCoords_rational : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ (u : GAd σ J) (b₀ : Matrix (Fin j) (Fin m) E) (c₀ : Matrix (Fin j) (Fin j) E), Crd σ J C D Z J₀ u (adMat F b₀) (adMat F c₀) → u ∈ ratPts σ J := by
  first | exact @GlobalTheory.SphEis.mem_ratPts_of_crd_rat | exact GlobalTheory.SphEis.mem_ratPts_of_crd_rat | (intros; apply GlobalTheory.SphEis.mem_ratPts_of_crd_rat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormCompletedHeckeLCMOneLePhragmenLindelofStatement
section
open NumberField IsDedekindDomain GlobalTheory.CMVal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_completedHeckeL_CM_one_le_phragmenLindelof : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
    GlobalTheory.Published.HeckeFunctionalEquationAbs → GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.CompletedLBoundedInStrips → IsCMType φ →
    ∀ (χ : HChar E) (m : I → ℤ) (a : HeightOneSpectrum (𝓞 E) →₀ ℕ) (Λ : ℂ → ℂ),
    IsUnitary χ → TrivOnF χ → HasInf χ φ m → (∀ i, 0 < m i) → (∀ v, ExpAt χ v (a v)) → IsHeckeL χ Λ →
    ‖Λ 1‖ ≤ ‖riemannZeta (3 / 2)‖ ^ Module.finrank ℚ E *
      ((((discr E).natAbs * a.prod fun v k => Ideal.absNorm v.asIdeal ^ k : ℕ) : ℝ)) * ∏ i, (1 + (m i : ℝ)) := by
  first | exact @GlobalTheory.HeckeLOneBound.norm_heckeL_one_le | exact GlobalTheory.HeckeLOneBound.norm_heckeL_one_le | (intros; apply GlobalTheory.HeckeLOneBound.norm_heckeL_one_le <;> assumption)
end

