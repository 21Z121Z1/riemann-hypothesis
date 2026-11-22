import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0005
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointRationalEquivariance
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0111
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0112
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselTorusElementProperties

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointMajorantFramesGiveMajorants
section
open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset

namespace GlobalTheory.Count.FrameMajorant

theorem signed_cs {n : ℕ} (ε : Fin n → Bool) (a b : Fin n → ℂ) :
    ‖star a ⬝ᵥ (Jm ε *ᵥ b)‖ ≤ Formalism.HermitianLatticesTheory.cnorm a * Formalism.HermitianLatticesTheory.cnorm b := by
  unfold Formalism.HermitianLatticesTheory.cnorm
  have h1 : ‖star a ⬝ᵥ (Jm ε *ᵥ b)‖ ≤ ∑ i, ‖a i‖ * ‖b i‖ := by
    unfold dotProduct
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => le_of_eq ?_)
    simp only [Jm, Matrix.mulVec_diagonal, norm_mul, Pi.star_apply, norm_star]
    split_ifs <;> simp
  exact h1.trans (Real.sum_mul_le_sqrt_mul_sqrt _ _ _)

theorem cnorm_unitary {n : ℕ} (u : Matrix (Fin n) (Fin n) ℂ) (hu : uᴴ * u = 1) (a : Fin n → ℂ) :
    Formalism.HermitianLatticesTheory.cnorm (u *ᵥ a) = Formalism.HermitianLatticesTheory.cnorm a := by
  have key : ∀ c : Fin n → ℂ, ((∑ i, ‖c i‖ ^ 2 : ℝ) : ℂ) = star c ⬝ᵥ c := by
    intro c
    unfold dotProduct
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.star_apply, Complex.star_def, Complex.conj_mul']
  unfold Formalism.HermitianLatticesTheory.cnorm
  congr 1
  have : star (u *ᵥ a) ⬝ᵥ (u *ᵥ a) = star a ⬝ᵥ a := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hu, Matrix.one_mulVec]
  exact_mod_cast (key _).trans (this.trans (key _).symm)

theorem cnorm_inv_mul_unitary {n : ℕ} (X u : Matrix (Fin n) (Fin n) ℂ) (hu : uᴴ * u = 1) (a : Fin n → ℂ) :
    Formalism.HermitianLatticesTheory.cnorm ((X * u)⁻¹ *ᵥ a) = Formalism.HermitianLatticesTheory.cnorm (X⁻¹ *ᵥ a) := by
  rw [Matrix.mul_inv_rev, Matrix.inv_eq_left_inv hu, ← Matrix.mulVec_mulVec]
  apply cnorm_unitary
  rw [Matrix.conjTranspose_conjTranspose]
  exact mul_eq_one_comm.1 hu

variable (I : AutInst)

theorem comap_bijective :
    Function.Bijective (fun w : InfinitePlace I.E => w.comap (algebraMap I.F I.E)) := by
  refine ⟨fun w w' h => ?_, ?_⟩
  · have hw : ∀ w : InfinitePlace I.E, w = InfinitePlace.mk (I.φ (w.comap (algebraMap I.F I.E))) := by
      intro w
      rcases Test.embedding_cases I w with h | h
      · rw [← h, InfinitePlace.mk_embedding]
      · rw [← InfinitePlace.mk_conjugate_eq, ← h, InfinitePlace.mk_embedding]
    have h' : w.comap (algebraMap I.F I.E) = w'.comap (algebraMap I.F I.E) := h
    rw [hw w, hw w', h']
  · intro v
    refine ⟨InfinitePlace.mk (I.φ v), ?_⟩
    have h2 : (I.φ v).comp (algebraMap I.F I.E) = v.embedding := RingHom.ext (I.φ_over v)
    show (InfinitePlace.mk (I.φ v)).comap _ = v
    rw [InfinitePlace.comap_mk, h2, InfinitePlace.mk_embedding]

theorem card_places : Fintype.card (InfinitePlace I.F) = I.f := by
  have hR := I.cm.totReal
  rw [AutInst.f, IsTotallyReal.finrank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsTotallyReal.nrComplexPlaces_eq_zero, add_zero]

theorem frm_unit (x : I.GA) (w : InfinitePlace I.E) : IsUnit (frm I x w).det := by
  have h := congrArg (fun M => (Jm (I.ε (w.comap (algebraMap I.F I.E))) * M).det) (Test.frm_frame I x w)
  simp only [Jm_mul_self, Matrix.det_mul, Matrix.det_one] at h
  refine isUnit_iff_ne_zero.2 fun h0 => ?_
  simp [h0] at h

theorem hform_le (x : I.GA) (w : InfinitePlace I.E) (y z : Fin I.n → I.E) :
    ‖w.embedding (Formalism.UG.hform (starRingEnd I.E) I.J y z)‖ ≤
      Formalism.HermitianLatticesTheory.normAt (bas I) (frm I x) w y * Formalism.HermitianLatticesTheory.normAt (bas I) (frm I x) w z := by
  have hc := I.cm.cmUnram.2.1
  have hX := frm_unit I x w
  have hback : ∀ y, frm I x w *ᵥ Formalism.HermitianLatticesTheory.fcoord (bas I) (frm I x) w y = fun i => w.embedding (y i) := by
    intro y
    unfold Formalism.HermitianLatticesTheory.fcoord
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hX, Matrix.one_mulVec]
    funext i
    simp [Formalism.HermitianLatticesTheory.vecAt]
  have h1 : w.embedding (Formalism.UG.hform (starRingEnd I.E) I.J y z) =
      star (fun i => w.embedding (y i)) ⬝ᵥ (I.J.map w.embedding *ᵥ fun i => w.embedding (z i)) := by
    simp only [Formalism.UG.hform, map_sum, map_mul, dotProduct, Matrix.mulVec, Matrix.map_apply, Pi.star_apply,
      Finset.mul_sum, starRingEnd_apply, hc, mul_assoc]
  rw [h1, ← hback y, ← hback z, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, Test.frm_frame I x w]
  exact signed_cs _ _ _

theorem normAt_mul (x : I.GA) (w : InfinitePlace I.E) (k : I.GA) (hk : ∀ v, uMat (k.1 v) ∈ Kset (I.ε v))
    (y : Fin I.n → I.E) :
    Formalism.HermitianLatticesTheory.normAt (bas I) (frm I (x * k)) w y = Formalism.HermitianLatticesTheory.normAt (bas I) (frm I x) w y := by
  set v := w.comap (algebraMap I.F I.E) with hv
  have hu : (uMat (k.1 v))ᴴ * uMat (k.1 v) = 1 := (hk v).1.1
  have hm : uMat ((x * k).1 v) = uMat (x.1 v) * uMat (k.1 v) := rfl
  unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.fcoord frm
  simp only [← hv]
  split_ifs with h
  · rw [hm, ← Matrix.mul_assoc]
    exact cnorm_inv_mul_unitary _ _ hu _
  · rw [hm, ← Matrix.mul_assoc, Matrix.map_mul]
    apply cnorm_inv_mul_unitary
    have hT : ∀ M : Matrix (Fin I.n) (Fin I.n) ℂ, (M.map (starRingEnd ℂ))ᴴ = Mᴴ.map (starRingEnd ℂ) := by
      intro M; ext i j; simp
    rw [hT, ← Matrix.map_mul, hu]
    simp

theorem frames_give_majorants : ∀ (I : AutInst) (x : I.GA), IsTotallyComplex I.E ∧ nPl I.E = I.f ∧ Fintype.card (InfinitePlace I.F) = I.f ∧ Function.Bijective (fun w : InfinitePlace I.E => w.comap (algebraMap I.F I.E)) ∧ ∀ w : InfinitePlace I.E, IsUnit (frm I x w).det ∧ (frm I x w)ᴴ * I.J.map w.embedding * frm I x w = Jm (I.ε (w.comap (algebraMap I.F I.E))) ∧ (∀ y z : (Fin I.n → I.E), ‖w.embedding (Formalism.UG.hform (starRingEnd I.E) I.J y z)‖ ≤ Formalism.HermitianLatticesTheory.normAt (bas I) (frm I x) w y * Formalism.HermitianLatticesTheory.normAt (bas I) (frm I x) w z) ∧ ∀ k : I.GA, (∀ v, uMat (k.1 v) ∈ Kset (I.ε v)) → ∀ y, Formalism.HermitianLatticesTheory.normAt (bas I) (frm I (x * k)) w y = Formalism.HermitianLatticesTheory.normAt (bas I) (frm I x) w y := by
  intro I x
  refine ⟨I.cm.cmUnram.1, ?_, card_places I, comap_bijective I, fun w =>
    ⟨frm_unit I x w, Test.frm_frame I x w, hform_le I x w, normAt_mul I x w⟩⟩
  rw [nPl, Fintype.card_of_bijective (comap_bijective I), card_places]

end GlobalTheory.Count.FrameMajorant
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointRationalEquivarianceStatement
section
open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.autPoint_rational_equivariance : ∀ (I : AutInst) (x : I.GA) (γ : GL (Fin I.n) I.E) (a : I.GA), γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J → (∀ v, uMat (a.1 v) = (I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v) → I.fmat a.2 = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F)) → lamX I (a * x) = (lamX I x).map ((Matrix.toLin' (γ : Matrix (Fin I.n) (Fin I.n) I.E)).restrictScalars (𝓞 I.E)) ∧ (∀ w y, Formalism.HermitianLatticesTheory.normAt (bas I) (frm I (a * x)) w ((γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ y) = Formalism.HermitianLatticesTheory.normAt (bas I) (frm I x) w y) ∧ least I (a * x) = least I x ∧ (∀ t, stepLe I (a * x) t = (stepLe I x t).map ((Matrix.toLin' (γ : Matrix (Fin I.n) (Fin I.n) I.E)).restrictScalars (𝓞 I.E)) ∧ stepLt I (a * x) t = (stepLt I x t).map ((Matrix.toLin' (γ : Matrix (Fin I.n) (Fin I.n) I.E)).restrictScalars (𝓞 I.E))) ∧ (∀ (m : ℕ) (j : Fin m → ℕ) (τ : Fin m → ℝ), HasType I (a * x) j τ ↔ HasType I x j τ) ∧ ((x⁻¹ * a * x).2 ∈ I.Kset ↔ (lamX I x).map ((Matrix.toLin' (γ : Matrix (Fin I.n) (Fin I.n) I.E)).restrictScalars (𝓞 I.E)) = lamX I x) ∧ ∀ w, (frm I x w)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map w.embedding * frm I x w = uMat ((x⁻¹ * a * x).1 (w.comap (algebraMap I.F I.E))) ∨ (frm I x w)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map w.embedding * frm I x w = (uMat ((x⁻¹ * a * x).1 (w.comap (algebraMap I.F I.E)))).map (starRingEnd ℂ) := by
  first | exact @GlobalTheory.PointEquivariance.equivariance | exact GlobalTheory.PointEquivariance.equivariance | (intros; apply GlobalTheory.PointEquivariance.equivariance <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BernsteinZelevinskyDerivativeGLnEqTwistedSum
section
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm.DerFormula

variable {g : ℕ} [Fact g.Prime]

theorem isUnit_of_isUniUp {N : ℕ} {M : Mt g N} (hM : IsUniUp M) : IsUnit M := by
  have htri : M.BlockTriangular id := fun i j hij => (hM i j).1 hij
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_of_isUpperTriangular htri]
  simp [(hM _ _).2 rfl]

theorem card_lt_pairs (N : ℕ) : Fintype.card {p : Fin N × Fin N // p.1 < p.2} = N * (N - 1) / 2 := by
  rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type, Finset.sum_comm]
  have hb : ∀ b : Fin N, (∑ a : Fin N, if a < b then 1 else 0) = (b : ℕ) := by
    intro b
    rw [← Finset.card_filter, ← Fin.card_Iio b]
    congr 1
    ext a
    simp
  simp only [hb]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) N, Finset.sum_range_id]

def ofUpper {N : ℕ} (f : {p : Fin N × Fin N // p.1 < p.2} → ZMod g) : Mt g N :=
  fun a b => if h : a < b then f ⟨(a, b), h⟩ else if a = b then 1 else 0

theorem isUniUp_ofUpper {N : ℕ} (f : {p : Fin N × Fin N // p.1 < p.2} → ZMod g) : IsUniUp (ofUpper f) := by
  intro a b
  refine ⟨fun hba => ?_, fun hab => ?_⟩
  · simp only [ofUpper, dif_neg (not_lt.mpr hba.le), if_neg hba.ne']
  · subst hab
    simp [ofUpper]

theorem card_uniUp (N : ℕ) :
    (Finset.univ.filter fun u : Gn g N => IsUniUp (u : Mt g N)).card = g ^ (N * (N - 1) / 2) := by
  rw [← Fintype.card_subtype]
  have e : {u : Gn g N // IsUniUp (u : Mt g N)} ≃ ({p : Fin N × Fin N // p.1 < p.2} → ZMod g) :=
    { toFun := fun u p => (u.1 : Mt g N) p.1.1 p.1.2
      invFun := fun f => ⟨(isUnit_of_isUniUp (isUniUp_ofUpper f)).unit, isUniUp_ofUpper f⟩
      left_inv := by
        rintro ⟨u, hu⟩
        apply Subtype.ext
        apply Units.ext
        dsimp only
        rw [IsUnit.unit_spec]
        funext a b
        show ofUpper _ a b = (u : Mt g N) a b
        rcases lt_trichotomy a b with hab | rfl | hab
        · simp only [ofUpper, dif_pos hab]
        · simp only [ofUpper, dif_neg (lt_irrefl a)]
          exact ((hu a a).2 rfl).symm
        · simp only [ofUpper, dif_neg (not_lt.mpr hab.le), if_neg hab.ne']
          exact ((hu a b).1 hab).symm
      right_inv := by
        intro f
        funext p
        dsimp only
        rw [IsUnit.unit_spec]
        show ofUpper f p.1.1 p.1.2 = f p
        simp only [ofUpper, dif_pos p.2] }
  rw [Fintype.card_congr e, Fintype.card_fun, ZMod.card, card_lt_pairs]

theorem eU_coeff (ψ : AddChar (ZMod g) ℂ) (N : ℕ) (u : Gn g N) :
    (eU g N ψ).coeff u = if IsUniUp (u : Mt g N) then
      ((g : ℂ) ^ (N * (N - 1) / 2))⁻¹ * (ψ (∑ i ∈ Finset.range (N - 1), entN (u : Mt g N) i (i + 1)))⁻¹ else 0 := by
  unfold eU eDat
  rw [MonoidAlgebra.coeff_smul_apply, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  simp only [MonoidAlgebra.coeff_single, Finsupp.single_apply, Finset.sum_ite_eq', Finset.mem_filter,
    Finset.mem_univ, true_and, card_uniUp, Nat.cast_pow, smul_eq_mul]
  split_ifs <;> simp

theorem sum_br (i n : ℕ) (M : Mt g n) :
    ∑ j ∈ Finset.range (n - i - 1), entN (br i (n - i) M) j (j + 1) = supFrom i M := by
  unfold supFrom
  rw [Finset.sum_Ico_eq_sum_range, show n - 1 - i = n - i - 1 by omega]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  have h1 : j < n - i := by omega
  have h2 : j + 1 < n - i := by omega
  have hbr : entN (br i (n - i) M) j (j + 1) = entN M (i + j) (i + (j + 1)) := by
    conv_lhs => unfold entN
    rw [dif_pos ⟨h1, h2⟩]
    rfl
  rw [hbr, add_assoc]

end GlobalTheory.GLm.DerFormula

namespace GlobalTheory.GLm

open DerFormula

theorem der_eq_sum : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) (i n : ℕ) (F : Gn g n → ℂ) (h : Gn g i), i ≤ n → der ψ i F h = ((g : ℂ) ^ (i * (n - i) + (n - i) * (n - i - 1) / 2))⁻¹ * ∑ x : Gn g n, if InR i (x : Mt g n) ∧ tl i (x : Mt g n) = (h : Mt g i) then F x * (ψ (supFrom i (x : Mt g n)))⁻¹ else 0 := by
  intro g _ ψ i n F h _
  have key : ∀ x : Gn g n, (∑ v : Gn g (n - i),
      (if IsUniUp (v : Mt g (n - i)) then
        (ψ (∑ j ∈ Finset.range (n - i - 1), entN (v : Mt g (n - i)) j (j + 1)))⁻¹ else 0) *
      (if InPar i (x : Mt g n) ∧ tl i (x : Mt g n) = (h : Mt g i) ∧
          br i (n - i) (x : Mt g n) = (v : Mt g (n - i)) then F x else 0)) =
      if InR i (x : Mt g n) ∧ tl i (x : Mt g n) = (h : Mt g i) then
        F x * (ψ (supFrom i (x : Mt g n)))⁻¹ else 0 := by
    intro x
    unfold InR
    by_cases hx : (InPar i (x : Mt g n) ∧ IsUniUp (br i (n - i) (x : Mt g n))) ∧
        tl i (x : Mt g n) = (h : Mt g i)
    · obtain ⟨⟨hP, hU⟩, ht⟩ := hx
      have hv0 : ((isUnit_of_isUniUp hU).unit : Mt g (n - i)) = br i (n - i) (x : Mt g n) :=
        IsUnit.unit_spec _
      rw [Finset.sum_eq_single (isUnit_of_isUniUp hU).unit]
      · rw [if_pos (by rw [hv0]; exact hU), if_pos ⟨hP, ht, hv0.symm⟩, if_pos ⟨⟨hP, hU⟩, ht⟩, hv0, sum_br,
          mul_comm]
      · intro v _ hv
        refine mul_eq_zero_of_right _ (if_neg ?_)
        rintro ⟨-, -, hb⟩
        exact hv (Units.ext (hb.symm.trans hv0.symm))
      · intro hv
        exact absurd (Finset.mem_univ _) hv
    · rw [if_neg hx]
      refine Finset.sum_eq_zero fun v _ => ?_
      by_cases hv : IsUniUp (v : Mt g (n - i))
      · refine mul_eq_zero_of_right _ (if_neg ?_)
        rintro ⟨hP, ht, hb⟩
        exact hx ⟨⟨hP, by rw [hb]; exact hv⟩, ht⟩
      · rw [if_neg hv, zero_mul]
  simp only [der, wh, tr, res, eU_coeff]
  calc _ = ∑ v : Gn g (n - i), ((g : ℂ) ^ (i * (n - i)))⁻¹ * ((g : ℂ) ^ ((n - i) * (n - i - 1) / 2))⁻¹ *
        ∑ x : Gn g n, (if IsUniUp (v : Mt g (n - i)) then
          (ψ (∑ j ∈ Finset.range (n - i - 1), entN (v : Mt g (n - i)) j (j + 1)))⁻¹ else 0) *
          (if InPar i (x : Mt g n) ∧ tl i (x : Mt g n) = (h : Mt g i) ∧
            br i (n - i) (x : Mt g n) = (v : Mt g (n - i)) then F x else 0) := by
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [← Finset.mul_sum]
        split_ifs <;> ring
    _ = _ := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        simp only [key]
        rw [pow_add, mul_inv]

end GlobalTheory.GLm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselConstantBoundsOfGeTwoNPowFiveStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bessel_constant_bounds_of_ge_two_n_pow_five : ∀ (k r : ℕ) (a : ℝ), 1 ≤ k → 2 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 5 ≤ a → 2 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 < a / 2 ∧ (2 * ((2 * (r ^ 2 + r + 1) : ℕ) : ℝ) * (2 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2) + 1) + 2 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + 1 ≤ a := by
  first | exact @GlobalTheory.SgInf.a_bounds_of_ge_two_n_pow_five | exact GlobalTheory.SgInf.a_bounds_of_ge_two_n_pow_five | (intros; apply GlobalTheory.SgInf.a_bounds_of_ge_two_n_pow_five <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFormalDegreeEqOfSchurOrthogonalityStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselFormalDegree_eq_of_schurOrthogonality : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mat k r → (H →L[ℂ] H)) (μG : Measure (Mt k r)) (d : ℝ) (w : H), SchurH μG σ d → w ≠ 0 → fdegH μG σ w = d := by
  first | exact @GlobalTheory.SgInf.fdegH_eq_of_schurH | exact GlobalTheory.SgInf.fdegH_eq_of_schurH | (intros; apply GlobalTheory.SgInf.fdegH_eq_of_schurH <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselModelEqOnOfContinuousOnAeEqStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselModel_eqOn_of_continuousOn_ae_eq : ∀ (k r : ℕ) {B : Type} [NormedAddCommGroup B] (μG : Measure (Mt k r)) (f g : Mat k r → B), IsHaarOn (GG k r) μG → ContinuousOn f (GG k r) → ContinuousOn g (GG k r) → (fun x : Mt k r => f (Matrix.of x)) =ᵐ[μG] (fun x => g (Matrix.of x)) → ∀ x ∈ GG k r, f x = g x := by
  first | exact @GlobalTheory.SgInf.AeqCont.eqOn_of_ae | exact GlobalTheory.SgInf.AeqCont.eqOn_of_ae | (intros; apply GlobalTheory.SgInf.AeqCont.eqOn_of_ae <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselModelUnitaryGroupOpNormPropertiesStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselModelUnitaryGroup_opNorm_properties : ∀ (k r : ℕ) , (∀ g ∈ GG k r, opn g⁻¹ = opn g ∧ 1 ≤ opn g) ∧ (∀ x y : Mat k r, opn (x * y) ≤ opn x * opn y) ∧ Continuous (fun x : Mat k r => opn x) ∧ (∀ (x : Mat k r) i j, ‖x i j‖ ≤ opn x) ∧ (∀ (x : Mat k r) (v : Fin (2 * r + k + 1) → ℂ), eucl (x *ᵥ v) ≤ opn x * eucl v) ∧ (∀ u v : Fin (2 * r + k + 1) → ℂ, ‖herm (Hpk k r) u v‖ ≤ eucl u * eucl v) ∧ (∀ x ∈ GG k r, ∀ y ∈ GG k r, opn x / opn y ≤ opn (x * y) ∧ opn y / opn x ≤ opn (x * y)) ∧ (∀ x : Mat k r, opn x ≤ Real.sqrt (Formalism.REAL.hs x) ∧ Real.sqrt (Formalism.REAL.hs x) ≤ ((2 * r + k + 1 : ℕ) : ℝ) * opn x) := by
  first | exact @GlobalTheory.SgInf.opn_facts | exact GlobalTheory.SgInf.opn_facts | (intros; apply GlobalTheory.SgInf.opn_facts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselSchurTranslatedMatrixCoefficientStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselSchur_translated_matrixCoefficient : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ), Std σ w a μG d → ∀ u u₁ v : H, ∀ t ∈ GG k r, ∫ y, coef σ u v (Matrix.of y) * star (coef σ u₁ v (t * Matrix.of y)) ∂μG = ⟪u₁, u⟫_ℂ * ⟪v, σ t⁻¹ v⟫_ℂ / (d : ℂ) := by
  first | exact @GlobalTheory.SgInf.schur_translated_coef | exact GlobalTheory.SgInf.schur_translated_coef | (intros; apply GlobalTheory.SgInf.schur_translated_coef <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselSubgroupRepTwistedIsUnitaryRepStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselSubgroupRepTwisted_isUnitaryRep : ∀ (k r : ℕ) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)), inWb k r z → 0 < Tz k r z → IsURepOn (UWset k r z) π → (∀ h ∈ UWset k r z, ∀ m ∈ Nset k r, hPart k r (h * m) = h ∧ PiS (psiGen k r z c) π (h * m) = psiGen k r z c m • π h) ∧ IsURepOn (Sset k r z) (PiS (psiGen k r z c) π) ∧ (∀ s ∈ Sset k r z, ‖PiS (psiGen k r z c) π s‖ ≤ 1 ∧ ContinuousLinearMap.adjoint (PiS (psiGen k r z c) π s) = PiS (psiGen k r z c) π s⁻¹) ∧ ContinuousOn (PiS (psiGen k r z c) π) (Sset k r z) ∧ (∀ m ∈ Nset k r, ‖psiGen k r z c m‖ = 1 ∧ ∀ m' ∈ Nset k r, psiGen k r z c (m * m') = psiGen k r z c m * psiGen k r z c m') := by
  first | exact @GlobalTheory.SgInf.PiUnitary.piS_unitary | exact GlobalTheory.SgInf.PiUnitary.piS_unitary | (intros; apply GlobalTheory.SgInf.PiUnitary.piS_unitary <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselSubgroupsClosedUnitaryWCompactStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bessel_subgroups_closed_unitaryW_compact : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), inWb k r z → 0 < Tz k r z → IsClosedSub k r (GG k r) ∧ IsClosedSub k r (Nset k r) ∧ IsClosedSub k r (UWset k r z) ∧ IsClosedSub k r (Sset k r z) ∧ IsCompact (UWset k r z) := by
  first | exact @GlobalTheory.SgInf.closedSub_groups | exact GlobalTheory.SgInf.closedSub_groups | (intros; apply GlobalTheory.SgInf.closedSub_groups <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselTorusElementPropertiesStatement
section
open Formalism.FourierDecayAlt GlobalTheory.ThA MeasureTheory Formalism.QuantumDeterminants Matrix
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselTorusElement_properties : ∀ (k r : ℕ) (α : ℂ), α ≠ 0 → aT k r α ∈ B.GV k r ∧ (∀ z, inWb k r z → (∀ h ∈ UWset k r z, aT k r α * h = h * aT k r α) ∧ ∀ n ∈ Nset k r, aT k r α * n * (aT k r α)⁻¹ ∈ Nset k r ∧ (aT k r α)⁻¹ * n * aT k r α ∈ Nset k r ∧ ell k r z (aT k r α * n * (aT k r α)⁻¹) = α * ell k r z n) ∧ (∀ z z', inWb k r z → inWb k r z' → ∀ (g : B.Mat k r) (a b : Fin (r + 1)), Zhat k r z z' ((aT k r α)⁻¹ * g * aT k r α) a b = (star α) ^ (r - a.val) * α ^ (r - b.val) * Zhat k r z z' g a b) ∧ ∀ (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ), (aT k r α)⁻¹ * bigCell k r c μ * aT k r α = bigCell k r (fun a => ((‖α‖ ^ (2 * (r - a.val)) : ℝ) : ℂ) * c a) μ := by
  first | exact @GlobalTheory.ThA.TorusElt.torusElt | exact GlobalTheory.ThA.TorusElt.torusElt | (intros; apply GlobalTheory.ThA.TorusElt.torusElt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselZhatInvAndRegularIffStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselZhat_inv_and_regular_iff : ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : Mat k r), γ ∈ GG k r → Zhat k r z' z γ⁻¹ = (Zhat k r z z' γ)ᴴ ∧ (γ ∈ Greg k r z z' ↔ γ⁻¹ ∈ Greg k r z' z) := by
  first | exact @GlobalTheory.SgInf.RegInv.zhat_inv_and_reg | exact GlobalTheory.SgInf.RegInv.zhat_inv_and_reg | (intros; apply GlobalTheory.SgInf.RegInv.zhat_inv_and_reg <;> assumption)
end

