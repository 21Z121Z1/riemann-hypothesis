import Mathlib
import ReciprocityTheory.GaloisValuations.SeparatedDvrSecondCohomologyMem
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0008
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0007
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0010

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CocycleEqAddUniformizerSmulAddCoboundary
section
open ReciprocityTheory.Gal

namespace GlobalTheory

theorem cocycle_lift_mod_uniformizer
    {O : Type} [CommRing O] {M : Type} [AddCommGroup M] [Module O M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [ContinuousConstSMul O M] {G : Type} [Group G] [TopologicalSpace G]
    (ρ : Representation O G M) (hρ : ContAction ρ) (ϖ : O)
    (hemb : Topology.IsEmbedding (fun m : M => ϖ • m)) (s : Finset (Z1 ρ))
    (hs : ∀ c : Z1 ρ, ∃ i ∈ s, ∃ x : M, ∀ g, (c : G → M) g - (i : G → M) g - (ρ g x - x) ∈
      LinearMap.range (LinearMap.lsmul O M ϖ))
    (c : Z1 ρ) : ∃ (a : Z1 ρ → O) (c' : Z1 ρ) (x : M),
      (c : G → M) = ∑ i ∈ s, a i • (i : G → M) + ϖ • (c' : G → M) + d0 ρ x := by
  classical
  obtain ⟨i, his, x, hx⟩ := hs c
  let d : Z1 ρ := ⟨d0 ρ x, coboundaries_le_cocycles ρ hρ ⟨x, rfl⟩⟩
  let E : Z1 ρ := c - i - d
  have hE : ∀ g, (E : G → M) g = (c : G → M) g - (i : G → M) g - (ρ g x - x) := fun g => rfl
  have hx' : ∀ g, ∃ y : M, ϖ • y = (E : G → M) g := by
    intro g
    obtain ⟨y, hy⟩ := hx g
    exact ⟨y, by rw [hE]; simpa using hy⟩
  choose f hf using hx'
  have hfE : (fun g => ϖ • f g) = (E : G → M) := funext hf
  have hfc : Continuous f := by
    rw [hemb.continuous_iff]
    change Continuous (fun g => ϖ • f g)
    rw [hfE]
    exact E.2.1
  have hfco : ∀ g h, f (g * h) = f g + ρ g (f h) := by
    intro g h
    apply hemb.injective
    change ϖ • f (g * h) = ϖ • (f g + ρ g (f h))
    rw [smul_add, ← map_smul, hf, hf, hf]
    exact E.2.2 g h
  refine ⟨fun j => if j = i then 1 else 0, ⟨f, hfc, hfco⟩, x, ?_⟩
  have hsum : ∑ j ∈ s, (if j = i then (1 : O) else 0) • (j : G → M) = (i : G → M) := by
    simp only [ite_smul, one_smul, zero_smul]
    rw [Finset.sum_ite_eq' s i (fun j => (j : G → M))]
    simp [his]
  rw [hsum]
  funext g
  have := hf g
  rw [hE] at this
  simp only [Pi.add_apply, Pi.smul_apply, amitsur_d0_apply]
  rw [this]
  abel

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompanionMatrixOfCoeffsPowMulVecFirstBasisVector
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.ImgSec

section Alg
variable {k : Type} [CommRing k] {r : ℕ}

def e1 : Fin r → k := fun i => if (i : ℕ) = 0 then 1 else 0

theorem companionMatrixOfCoeffs_pow_mulVec_firstBasisVector (p : Fin r → k) : ∀ (j : ℕ) (hj : j < r),
    (companion p ^ j) *ᵥ e1 = Pi.single (⟨j, hj⟩ : Fin r) 1
  | 0, hj => by
    ext i; simp [e1, Pi.single_apply, Fin.ext_iff]
  | j + 1, hj => by
    rw [pow_succ', ← mulVec_mulVec, companionMatrixOfCoeffs_pow_mulVec_firstBasisVector p j (by omega), Matrix.mulVec_single_one]
    ext i
    have : j + 1 ≠ r := by omega
    simp [companion, Pi.single_apply, Fin.ext_iff, this]

theorem mom_sec_add (a : Inv r k) (n : ℕ) (j : Fin r) :
    mom (sec a) (n + j) = (a.2.1 ᵥ* (companion a.1 ^ n)) j := by
  have h1 : mom (sec a) (n + j) = a.2.1 ⬝ᵥ ((companion a.1 ^ n) *ᵥ ((companion a.1 ^ (j : ℕ)) *ᵥ e1)) := by
    simp only [mom, sec, pow_add, ← mulVec_mulVec]; rfl
  rw [h1, companionMatrixOfCoeffs_pow_mulVec_firstBasisVector a.1 j j.2, dotProduct_mulVec, dotProduct_single_one]

theorem hankel_apply' (a : Inv r k) (i j : Fin r) : hankel a i j = (a.2.1 ᵥ* (companion a.1 ^ (i : ℕ))) j :=
  mom_sec_add a i j

theorem hankel_isSymm (a : Inv r k) : (hankel a).IsSymm := by
  ext i j; simp [hankel, add_comm]

def hankelShift (a : Inv r k) : Matrix (Fin r) (Fin r) k := Matrix.of fun i j => mom (sec a) ((i : ℕ) + (j : ℕ) + 1)

theorem hankelShift_isSymm (a : Inv r k) : (hankelShift a).IsSymm := by
  ext i j; simp [hankelShift]; ring_nf

theorem hankel_mul_companion (a : Inv r k) : hankel a * companion a.1 = hankelShift a := by
  ext i j
  have h2 : hankelShift a i j = mom (sec a) (((i : ℕ) + 1) + j) := by simp [hankelShift]; ring_nf
  rw [h2, mom_sec_add, Matrix.mul_apply, pow_succ, ← Matrix.vecMul_vecMul]
  simp only [Matrix.vecMul, dotProduct, hankel_apply']

theorem companion_map {k' : Type} [CommRing k'] (φ : k →+* k') (p : Fin r → k) :
    (companion p).map φ = companion (fun i => φ (p i)) := by
  ext i j; simp only [companion, Matrix.map_apply, Matrix.of_apply]; split_ifs <;> simp

end Alg

section Herm
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  [Unram F E] {r : ℕ}

theorem map_isSelfAdjoint {N : Matrix (Fin r) (Fin r) F} (hN : N.IsSymm) :
    IsSelfAdjoint (N.map (algebraMap F E)) := by
  rw [IsSelfAdjoint, Matrix.star_eq_conjTranspose]
  ext i j
  simp [Matrix.conjTranspose_apply, Unram.star_fix, hN.apply i j]

theorem conjTranspose_map (N : Matrix (Fin r) (Fin r) F) :
    (N.map (algebraMap F E))ᴴ = Nᵀ.map (algebraMap F E) := by
  ext i j; simp [Matrix.conjTranspose_apply, Unram.star_fix]

def mkX (a : Inv r F) (h : Matrix (Fin r) (Fin r) E) : Hn r F E :=
  (⟨star h⁻¹ * (hankelShift a).map (algebraMap F E) * h⁻¹, by
      have h1 := (map_isSelfAdjoint (E := E) (hankelShift_isSymm a)).conjugate (star h⁻¹)
      rw [star_star] at h1
      exact h1⟩, h *ᵥ e1, a.2.2)

theorem mkX_snd_fst (a : Inv r F) (h : Matrix (Fin r) (Fin r) E) : (mkX a h).2.1 = h *ᵥ e1 := rfl

variable {a : Inv r F} {h : Matrix (Fin r) (Fin r) E}

theorem mkX_fst (hh : hᴴ * h = (hankel a).map (algebraMap F E)) (hd : IsUnit h.det) :
    (mkX a h).1.1 = h * (companion a.1).map (algebraMap F E) * h⁻¹ := by
  have hd' : IsUnit hᴴ.det := by rw [Matrix.det_conjTranspose]; exact hd.star
  simp only [mkX]
  rw [← hankel_mul_companion, Matrix.map_mul, ← hh, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_nonsing_inv,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd', Matrix.one_mul]

theorem pow_mulVec_mkX (hh : hᴴ * h = (hankel a).map (algebraMap F E)) (hd : IsUnit h.det) (j : Fin r) :
    ((mkX a h).1.1 ^ (j : ℕ)) *ᵥ (h *ᵥ e1) = h *ᵥ Pi.single j 1 := by
  rw [mkX_fst hh hd]
  have key : ∀ n : ℕ, (h * (companion a.1).map (algebraMap F E) * h⁻¹) ^ n =
      h * ((companion a.1).map (algebraMap F E)) ^ n * h⁻¹ := by
    intro n; induction n with
    | zero => simp [Matrix.mul_nonsing_inv _ hd]
    | succ n ih =>
      rw [pow_succ, ih, pow_succ]
      simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hd]
  rw [key, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.mul_one, ← Matrix.mulVec_mulVec,
    companion_map, companionMatrixOfCoeffs_pow_mulVec_firstBasisVector _ j j.2]

theorem bm_mkX (hh : hᴴ * h = (hankel a).map (algebraMap F E)) (hd : IsUnit h.det) :
    Bm (mkX a h).toGl = h := by
  ext i j
  simp only [Bm, Hn.toGl, Matrix.of_apply]
  rw [mkX_snd_fst, pow_mulVec_mkX hh hd, Matrix.mulVec_single_one]; rfl

theorem mom_mkX (hh : hᴴ * h = (hankel a).map (algebraMap F E)) (hd : IsUnit h.det) (j : Fin r) :
    mom (mkX a h).toGl j = algebraMap F E (a.2.1 j) := by
  have h0 : 0 < r := j.pos
  simp only [mom, Hn.toGl]
  rw [mkX_snd_fst, pow_mulVec_mkX hh hd, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hh]
  have he : star (e1 : Fin r → E) = Pi.single (⟨0, h0⟩ : Fin r) 1 := by
    ext i; by_cases hi : (i : ℕ) = 0 <;> simp [e1, hi, Pi.single_apply, Fin.ext_iff]
  rw [he, Matrix.mulVec_single_one, single_one_dotProduct]
  simp only [Matrix.col_apply, Matrix.transpose_apply, Matrix.map_apply]
  rw [hankel_apply']
  simp
end Herm

section Top
variable {k : Type} [CommRing k] [TopologicalSpace k] [IsTopologicalRing k] {r : ℕ}

theorem continuous_companion : Continuous (fun p : Fin r → k => companion p) :=
  continuous_matrix fun i j => by
    simp only [companion, Matrix.of_apply]
    split_ifs
    · exact (continuous_apply i).neg
    · exact continuous_const
    · exact continuous_const

theorem continuous_mom_sec (n : ℕ) : Continuous (fun a : Inv r k => mom (sec a) n) := by
  simp only [mom, sec]
  exact (continuous_fst.comp continuous_snd).dotProduct
    (((continuous_companion.comp continuous_fst).pow n).matrix_mulVec continuous_const)

theorem continuous_hankel : Continuous (fun a : Inv r k => hankel a) :=
  continuous_matrix fun _ _ => continuous_mom_sec _

theorem continuous_hankelShift : Continuous (fun a : Inv r k => hankelShift a) :=
  continuous_matrix fun _ _ => continuous_mom_sec _

theorem continuous_delta : Continuous (fun a : Inv r k => Delta a) :=
  continuous_hankel.matrix_det

end Top

section Unit
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  [Unram F E] {r : ℕ}

omit [Unram F E] in

theorem continuousStar (F : Type) [NontriviallyNormedField F] [NormedAlgebra F E] [Unram F E] : ContinuousStar E :=
  ⟨(Isometry.of_dist_eq fun x y => by
    rw [dist_eq_norm, dist_eq_norm, ← star_sub, Unram.norm_star (F := F)]).continuous⟩

theorem bm_actU (g : Matrix.unitaryGroup (Fin r) E) (X : Hn r F E) : Bm (actU g X).toGl = g.1 * Bm X.toGl := by
  have hg : star g.1 * g.1 = 1 := (Matrix.mem_unitaryGroup_iff').1 g.2
  have key : ∀ n : ℕ, (g.1 * X.1.1 * star g.1) ^ n * g.1 = g.1 * X.1.1 ^ n := by
    intro n; induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', Matrix.mul_assoc, ih, ← Matrix.mul_assoc, Matrix.mul_assoc _ (star g.1), hg, Matrix.mul_one,
        Matrix.mul_assoc, ← pow_succ']
  ext i j
  simp only [Bm, Hn.toGl, actU, Matrix.of_apply]
  rw [Matrix.mulVec_mulVec, key, ← Matrix.mulVec_mulVec]
  simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]

end Unit

end GlobalTheory.JR.ImgSec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjTransposeVecMulVecSelf
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.UnitWitt

variable {E : Type} [Field E] [StarRing E] {r : ℕ}

theorem vecMulVec_mulVec_eq (w v z : Fin r → E) : vecMulVec w v *ᵥ z = (v ⬝ᵥ z) • w := by
  ext i
  simp [mulVec, vecMulVec, dotProduct, Finset.mul_sum, mul_comm, mul_left_comm]

theorem conjTranspose_vecMulVec_self (w : Fin r → E) : (vecMulVec w (star w))ᴴ = vecMulVec w (star w) := by
  ext i j
  simp [vecMulVec, conjTranspose_apply, mul_comm]

theorem vecMulVec_self_mul (w : Fin r → E) :
    vecMulVec w (star w) * vecMulVec w (star w) = (star w ⬝ᵥ w) • vecMulVec w (star w) := by
  ext i j
  simp only [mul_apply, vecMulVec_apply, Matrix.smul_apply, smul_eq_mul, dotProduct, Pi.star_apply, Finset.sum_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem refl_mem (w : Fin r → E) (a : E) (ha : a ≠ 0) (hN : star w ⬝ᵥ w = a + star a) :
    (1 - a⁻¹ • vecMulVec w (star w)) ∈ unitaryGroup (Fin r) E := by
  rw [mem_unitaryGroup_iff']
  have hs : star (1 - a⁻¹ • vecMulVec w (star w)) = 1 - (star a)⁻¹ • vecMulVec w (star w) := by
    rw [star_sub, star_one, star_smul, star_inv₀]
    congr 2
    exact conjTranspose_vecMulVec_self w
  have ha' : star a ≠ 0 := by simpa using ha
  rw [hs]
  have key : (star a)⁻¹ + a⁻¹ - (star a)⁻¹ * a⁻¹ * (star w ⬝ᵥ w) = 0 := by
    rw [hN]; field_simp; ring
  calc (1 - (star a)⁻¹ • vecMulVec w (star w)) * (1 - a⁻¹ • vecMulVec w (star w))
      = 1 - ((star a)⁻¹ + a⁻¹ - (star a)⁻¹ * a⁻¹ * (star w ⬝ᵥ w)) • vecMulVec w (star w) := by
        rw [sub_mul, mul_sub, mul_sub, one_mul, mul_one, one_mul, smul_mul_smul_comm, vecMulVec_self_mul,
          smul_smul, sub_smul, add_smul]
        abel
    _ = 1 := by rw [key, zero_smul, sub_zero]

theorem refl_mulVec (w u : Fin r → E) (a : E) (ha : star w ⬝ᵥ u = a) (ha0 : a ≠ 0) :
    (1 - a⁻¹ • vecMulVec w (star w)) *ᵥ u = u - w := by
  have h1 : (a⁻¹ • vecMulVec w (star w)) *ᵥ u = a⁻¹ • (vecMulVec w (star w) *ᵥ u) := by
    ext i; simp [mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  rw [sub_mulVec, one_mulVec, h1, vecMulVec_mulVec_eq, ha, smul_smul, inv_mul_cancel₀ ha0, one_smul]

theorem star_dot (x y : Fin r → E) : star (star x ⬝ᵥ y) = star y ⬝ᵥ x := by
  simp [dotProduct, star_sum, mul_comm]

theorem exists_of_ne (u v : Fin r → E) (hc : star u ⬝ᵥ u = star v ⬝ᵥ v) (ha : star (u - v) ⬝ᵥ u ≠ 0) :
    ∃ g : unitaryGroup (Fin r) E, g.1 *ᵥ u = v := by
  have hN : star (u - v) ⬝ᵥ (u - v) = star (u - v) ⬝ᵥ u + star (star (u - v) ⬝ᵥ u) := by
    rw [star_dot]
    simp only [star_sub, sub_dotProduct, dotProduct_sub]
    rw [← hc]
    ring
  refine ⟨⟨_, refl_mem (u - v) _ ha hN⟩, ?_⟩
  show (1 - (star (u - v) ⬝ᵥ u)⁻¹ • vecMulVec (u - v) (star (u - v))) *ᵥ u = v
  rw [refl_mulVec (u - v) u _ rfl ha]
  abel

theorem exists_unitary_mulVec (h2 : (2 : E) ≠ 0) (u v : Fin r → E) (hc : star u ⬝ᵥ u = star v ⬝ᵥ v)
    (h0 : star u ⬝ᵥ u ≠ 0) : ∃ g : unitaryGroup (Fin r) E, g.1 *ᵥ u = v := by
  by_cases ha : star (u - v) ⬝ᵥ u = 0
  · have hvu : star v ⬝ᵥ u = star u ⬝ᵥ u := by
      rw [star_sub, sub_dotProduct, sub_eq_zero] at ha; exact ha.symm
    have hc' : star (-u) ⬝ᵥ (-u) = star v ⬝ᵥ v := by simpa using hc
    have ha' : star (-u - v) ⬝ᵥ (-u) ≠ 0 := by
      have : star (-u - v) ⬝ᵥ (-u) = 2 * (star u ⬝ᵥ u) := by
        simp only [star_sub, star_neg, sub_dotProduct, neg_dotProduct, dotProduct_neg, hvu]
        ring
      rw [this]; exact mul_ne_zero h2 h0
    obtain ⟨g, hg⟩ := exists_of_ne (-u) v hc' ha'
    refine ⟨⟨-g.1, ?_⟩, ?_⟩
    · rw [mem_unitaryGroup_iff', star_neg, neg_mul_neg]; exact mem_unitaryGroup_iff'.1 g.2
    · show (-g.1) *ᵥ u = v
      rw [← hg, neg_mulVec, mulVec_neg]
  · exact exists_of_ne u v hc ha

end GlobalTheory.UnitWitt

theorem GlobalTheory.unitary_transitive_of_norm : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (u v : Fin r → E), star u ⬝ᵥ u = star v ⬝ᵥ v →
    star u ⬝ᵥ u ≠ 0 → ∃ g : Matrix.unitaryGroup (Fin r) E, g.1 *ᵥ u = v := by
  intro F E _ _ _ _ hU r u v hc h0
  haveI : CharZero F := hU.charZero
  have h2 : (2 : E) ≠ 0 := by
    intro h
    apply (two_ne_zero : (2 : F) ≠ 0)
    apply (algebraMap F E).injective
    rw [map_ofNat, map_zero]; exact h
  exact GlobalTheory.UnitWitt.exists_unitary_mulVec h2 u v hc h0
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DetSuccEqSubSumUpdateRow
section
namespace GlobalTheory.PsChar

open Matrix

theorem det_succ_eq_sub_sum_updateRow {A : Type*} [CommRing A] {m : ℕ} (N : Matrix (Fin (m + 1)) (Fin (m + 1)) A) :
    N.det = N 0 0 * (N.submatrix Fin.succ Fin.succ).det -
      ∑ c : Fin m, N c.succ 0 * ((N.submatrix Fin.succ Fin.succ).updateRow c (fun b => N 0 b.succ)).det := by
  rw [Matrix.det_apply', Finset.univ_perm_fin_succ, Finset.sum_map, Fintype.sum_prod_type, Fin.sum_univ_succ,
    sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  · rw [Matrix.det_apply', Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp [Fin.prod_univ_succ, Equiv.Perm.decomposeFin.symm_sign]
    ring
  · refine Finset.sum_congr rfl fun c _ => ?_
    rw [Matrix.det_apply', Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    have h : ∀ i : Fin m, N (Equiv.swap 0 c.succ (e i).succ) i.succ =
        (N.submatrix Fin.succ Fin.succ).updateRow c (fun b => N 0 b.succ) (e i) i := by
      intro i
      by_cases hc : e i = c
      · simp [hc]
      · rw [Matrix.updateRow_ne hc, Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _)
          (fun h => hc (Fin.succ_injective _ h))]
        rfl
    simp [Fin.prod_univ_succ, Equiv.Perm.decomposeFin.symm_sign, h]
    ring

theorem alt_trace_eq_sum_det {M A : Type*} [Monoid M] [CommRing A] {n : ℕ} (r : M →* Matrix (Fin n) (Fin n) A) :
    ∀ (m : ℕ) (x : Fin m → M), alt (fun g => (r g).trace) m x =
      ∑ i : Fin m → Fin n, (Matrix.of fun a b => r (x a) (i b) (i a)).det
  | 0, x => by simp [alt]
  | m + 1, x => by
    rw [alt, ← (Fin.consEquiv (fun _ : Fin (m + 1) => Fin n)).sum_comp, Fintype.sum_prod_type]
    simp only [alt_trace_eq_sum_det r m, det_succ_eq_sub_sum_updateRow, Finset.sum_sub_distrib]
    congr 1
    · rw [Matrix.trace, Finset.sum_mul_sum]
      rfl
    · rw [Finset.sum_comm]
      conv_rhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => ?_
      have h1 : (Matrix.of fun a b => r (Function.update (Fin.tail x) c (x 0 * Fin.tail x c) a) (i b) (i a)) =
          (Matrix.of fun a b => r (x a.succ) (i b) (i a)).updateRow c
            (∑ j : Fin n, r (x c.succ) j (i c) • fun b => r (x 0) (i b) j) := by
        ext a b
        by_cases h : a = c
        · subst h
          simp [Fin.tail, Matrix.mul_apply, mul_comm]
        · simp [Fin.tail, h]
      rw [h1]
      have h2 : ∀ (P : Matrix (Fin m) (Fin m) A) (s : Finset (Fin n)) (w : Fin n → A) (v : Fin n → Fin m → A),
          (P.updateRow c (∑ j ∈ s, w j • v j)).det = ∑ j ∈ s, w j * (P.updateRow c (v j)).det := by
        intro P s w v
        induction s using Finset.induction_on with
        | empty =>
          simp only [Finset.sum_empty]
          exact Matrix.det_eq_zero_of_row_eq_zero c (by simp)
        | insert j s hj ih =>
          rw [Finset.sum_insert hj, Finset.sum_insert hj, Matrix.det_updateRow_add, ih, Matrix.det_updateRow_smul]
      rw [h2]
      rfl

theorem isPsChar_trace (M A : Type) [Monoid M] [CommRing A] (n : ℕ) (r : M →* Matrix (Fin n) (Fin n) A) :
    IsPsChar n (fun g => (r g).trace) where
  one := by simp
  comm x y := by simp only [map_mul]; exact Matrix.trace_mul_comm _ _
  alt_eq_zero x := by
    rw [alt_trace_eq_sum_det]
    refine Finset.sum_eq_zero fun i _ => ?_
    obtain ⟨b, b', hne, hb⟩ := Fintype.exists_ne_map_eq_of_card_lt i (by simp)
    exact Matrix.det_zero_of_column_eq hne (fun a => by simp [hb])

end GlobalTheory.PsChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DetTraceGramBlockMatrixStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_trace_gram_block_eq_pow_mul_norm_det : ∀ {E E' : Type} [Field E] [Field E'] [Algebra E E'] [FiniteDimensional E E'] {d n : ℕ} (w : Module.Basis (Fin d) E E') (H : Matrix (Fin n) (Fin n) E') (v : Fin d → E'), (Matrix.of fun (p q : Fin d × Fin n) => Algebra.trace E E' (w p.1 * H p.2 q.2 * v q.1)).det = (Matrix.of fun k l => Algebra.trace E E' (w k * v l)).det ^ n * Algebra.norm E H.det := by
  first | exact @GlobalTheory.det_traceGram_blockMatrix | exact GlobalTheory.det_traceGram_blockMatrix | (intros; apply GlobalTheory.det_traceGram_blockMatrix <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DisjointFinsetSupOfSupIndepSupStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.disjoint_finset_sup_of_supIndep_sup' : ∀ (R V ι : Type) [Ring R] [AddCommGroup V] [Module R V] (F : Finset ι) (G B : ι → Submodule R V), F.SupIndep (fun i => G i ⊔ B i) → (∀ i ∈ F, Disjoint (G i) (B i)) → Disjoint (F.sup G) (F.sup B) := by
  first | exact @GlobalTheory.disjoint_finset_sup_of_supIndep_sup | exact GlobalTheory.disjoint_finset_sup_of_supIndep_sup | (intros; apply GlobalTheory.disjoint_finset_sup_of_supIndep_sup <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvrMatrixProjPreimageStatement
section
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvr_matrix_proj_preimage_alt : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] (n : Type) [Fintype n] [DecidableEq n] (S : Submodule K (n → K)), ∃ P : Matrix n n O, (∀ v : n → O, (fun i => algebraMap O K ((P.mulVec v) i)) ∈ S) ∧ ∀ u : n → O, (fun i => algebraMap O K (u i)) ∈ S → P.mulVec u = u := by
  first | exact @GlobalTheory.dvr_matrix_proj_preimage | exact GlobalTheory.dvr_matrix_proj_preimage | (intros; apply GlobalTheory.dvr_matrix_proj_preimage <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EchelonProjectorKernelFrobeniusStatement
section
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.echelon_projector_kernel_frobenius : ∀ (l : ℕ) [Fact l.Prime] (C : Type) [Field C] [CharP C l] (d : ℕ) (Y A : Matrix (Fin d) (Fin d) C), A.det ≠ 0 → Y.map (frobenius C l) = Y * A → ∃ (I : Finset (Fin d)) (Q Λ : Matrix (Fin d) (Fin d) C), Y * Q = 0 ∧ (∀ v, Y.mulVec v = 0 → Q.mulVec v = v) ∧ (∀ i ∈ I, ∀ j, Q i j = if i = j then 1 else 0) ∧ (∀ i, ∀ j ∉ I, Q i j = 0) ∧ Q = A * Q.map (frobenius C l) * Λ := by
  first | exact @GlobalTheory.echelon_projector_frobenius | exact GlobalTheory.echelon_projector_frobenius | (intros; apply GlobalTheory.echelon_projector_frobenius <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EmbeddingIntegralContinuousStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.embedding_integral_continuous : ∀ (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [TopologicalSpace O] [IsTopologicalRing O], IsAdic (IsLocalRing.maximalIdeal O) → ∀ (ι : O →+* PadicAlgCl l), (∀ z : ℤ_[l], ι (algebraMap ℤ_[l] O z) = algebraMap ℚ_[l] (PadicAlgCl l) (z : ℚ_[l])) → (∀ a, ‖ι a‖ ≤ 1) ∧ (∀ a ∈ IsLocalRing.maximalIdeal O, ‖ι a‖ < 1) ∧ Continuous ι := by
  first | exact @GlobalTheory.padicAlgCl_embedding_bounded_continuous | exact GlobalTheory.padicAlgCl_embedding_bounded_continuous | (intros; apply GlobalTheory.padicAlgCl_embedding_bounded_continuous <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOfRootCongrOfDerivUnitStatement
section
open NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_roots_congr_of_derivative_unit : ∀ {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (f : Polynomial ℤ) (β β' : Ω),
    A.valuation β ≤ 1 → A.valuation β' ≤ 1 → Polynomial.aeval β f = 0 → Polynomial.aeval β' f = 0 →
    ¬ A.valuation (Polynomial.aeval β (Polynomial.derivative f)) < 1 → A.valuation (β - β') < 1 → β = β' := by
  first | exact @GlobalTheory.eq_of_root_congr_of_deriv_unit | exact GlobalTheory.eq_of_root_congr_of_deriv_unit | (intros; apply GlobalTheory.eq_of_root_congr_of_deriv_unit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfSumMulEmbeddingsEqZeroStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_sum_mul_embeddings_eq_zero' : ∀ (F Ω L : Type) [Field F] [CharZero F] [Field Ω] [IsAlgClosed Ω] [Algebra F Ω] [Field L] [Algebra F L] [FiniteDimensional F L] (m : ℕ) (e : Fin m → Ω), LinearIndependent F e → (∀ t, IsAlgebraic F (e t)) → ∀ a : Fin m → L, (∀ σ : L →ₐ[F] Ω, ∑ t, e t * σ (a t) = 0) → a = 0 := by
  first | exact @GlobalTheory.eq_zero_of_sum_mul_embeddings_eq_zero | exact GlobalTheory.eq_zero_of_sum_mul_embeddings_eq_zero | (intros; apply GlobalTheory.eq_zero_of_sum_mul_embeddings_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedFrameOfIsotropicColumnsStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adapted_frame_of_isotropic_columns' : ∀ (E : Type) [Field E] (r : ℕ) (Y : Submodule E ((Fin r → E) × (Fin r → E))), Module.finrank E Y = r → ∀ (C : Matrix (Fin r) (Fin r) E × Matrix (Fin r) (Fin r) E), Submodule.span E (Set.range fun j => ((fun a => C.1 a j), (fun a => C.2 a j))) = Y → ∀ (s : ℕ) (I : Matrix (Fin r) (Fin s) E), LinearIndependent E I.transpose → (∀ j, ((fun a => I a j), (0 : Fin r → E)) ∈ Y) → ∃ (t : ℕ) (J : Matrix (Fin r) (Fin s) E) (K : Matrix (Fin r) (Fin t) E) (L : Matrix (Fin s) (Fin r) E) (M : Matrix (Fin t) (Fin r) E), C.1 * J = I ∧ C.2 * J = 0 ∧ L * J = 1 ∧ L * K = 0 ∧ M * J = 0 ∧ M * K = 1 ∧ J * L + K * M = 1 := by
  first | exact @GlobalTheory.exists_adapted_frame_of_isotropic_columns | exact GlobalTheory.exists_adapted_frame_of_isotropic_columns | (intros; apply GlobalTheory.exists_adapted_frame_of_isotropic_columns <;> assumption)
end

