import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0518
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsValuedHeckeCharRamified
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0493
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0507
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0517
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0529
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstMeasurableSpaceRealSU
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0523
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0524
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeIdealEuclideanLatticeIsZLattice
section
open NumberField MeasureTheory
open scoped RealInnerProductSpace FourierTransform

noncomputable section

namespace GlobalTheory.HeckePoisson

open GlobalTheory.CMVal InfinitePlace ComplexConjugate
open scoped nonZeroDivisors

variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] {I : Type} [Fintype I]

def toMixed {φ : I → K →+* ℂ} (h : IsCMType φ) : EuclideanSpace ℂ I ≃ₗ[ℝ] mixedEmbedding.mixedSpace K := by
  classical
  haveI : IsEmpty {w : InfinitePlace K // w.IsReal} :=
    ⟨fun w => InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w.1) w.2⟩
  let b : I ≃ InfinitePlace K := Equiv.ofBijective _ (GlobalTheory.CMVal.Model.IsCMType.bijective h)
  exact
  { toFun := fun z => (0, fun w => if φ (b.symm w.1) = (InfinitePlace.mk (φ (b.symm w.1))).embedding
        then z (b.symm w.1) else conj (z (b.symm w.1)))
    invFun := fun x => WithLp.toLp 2 (fun i => if φ i = (InfinitePlace.mk (φ i)).embedding
        then x.2 ⟨InfinitePlace.mk (φ i), IsTotallyComplex.isComplex _⟩
        else conj (x.2 ⟨InfinitePlace.mk (φ i), IsTotallyComplex.isComplex _⟩))
    map_add' := fun x y => Prod.ext (by simp) (funext fun w => by
      simp only [Prod.snd_add, Pi.add_apply, PiLp.add_apply]; split_ifs <;> simp)
    map_smul' := fun r x => Prod.ext (by simp) (funext fun w => by
      simp only [Prod.smul_snd, Pi.smul_apply, PiLp.smul_apply, RingHom.id_apply]
      split_ifs <;> simp [Complex.real_smul])
    left_inv := fun z => by
      ext i
      have hi : b.symm (InfinitePlace.mk (φ i)) = i := b.symm_apply_apply i
      simp only [hi]
      split_ifs <;> simp
    right_inv := fun x => by
      refine Prod.ext (Subsingleton.elim _ _) (funext fun w => ?_)
      have e : (⟨InfinitePlace.mk (φ (b.symm w.1)), IsTotallyComplex.isComplex _⟩ : {w : InfinitePlace K // w.IsComplex}) = w :=
        Subtype.ext (b.apply_symm_apply w.1)
      simp only [e]
      split_ifs <;> simp }

theorem toMixed_embA {φ : I → K →+* ℂ} (h : IsCMType φ) (α : 𝓞 K) :
    toMixed h (embA φ α) = mixedEmbedding K (α : K) := by
  classical
  haveI : IsEmpty {w : InfinitePlace K // w.IsReal} :=
    ⟨fun w => InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w.1) w.2⟩
  refine Prod.ext (Subsingleton.elim _ _) (funext fun w => ?_)
  rw [mixedEmbedding.mixedEmbedding_apply_isComplex]
  simp only [toMixed, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, embA_apply]
  set i := (Equiv.ofBijective _ (GlobalTheory.CMVal.Model.IsCMType.bijective h)).symm w.1 with hi
  have hw : InfinitePlace.mk (φ i) = w.1 :=
    (Equiv.ofBijective _ (GlobalTheory.CMVal.Model.IsCMType.bijective h)).apply_symm_apply w.1
  split_ifs with hs
  · rw [hs, hw]
  · have hc := (InfinitePlace.embedding_mk_eq (φ i)).resolve_left (fun e => hs e.symm)
    rw [← hw, hc]
    simp [ComplexEmbedding.conjugate_coe_eq]

open Classical in
theorem lat_eq_comap {φ : I → K →+* ℂ} (h : IsCMType φ) (M : Ideal (𝓞 K)) (hM : M ≠ ⊥) :
    lat φ M = ZLattice.comap (E := mixedEmbedding.mixedSpace K) (F := EuclideanSpace ℂ I) ℝ (mixedEmbedding.idealLattice K
      (Units.mk0 (M : FractionalIdeal (𝓞 K)⁰ K) (FractionalIdeal.coeIdeal_ne_zero.2 hM)))
      (toMixed h).toContinuousLinearEquiv.toLinearMap := by
  ext z
  rw [mem_lat]
  change _ ↔ toMixed h z ∈ mixedEmbedding.idealLattice K _
  rw [mixedEmbedding.mem_idealLattice]
  constructor
  · rintro ⟨μ, hμ, rfl⟩
    exact ⟨(μ : K), (FractionalIdeal.mem_coeIdeal _).2 ⟨μ, hμ, rfl⟩, (toMixed_embA h μ).symm⟩
  · rintro ⟨y, hy, hyz⟩
    have hy' : y ∈ (M : FractionalIdeal (𝓞 K)⁰ K) := hy
    obtain ⟨μ, hμ, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy'
    exact ⟨μ, hμ, (toMixed h).injective (by rw [toMixed_embA]; exact hyz)⟩

theorem lat_isZLattice : ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I]
    (φ : I → K →+* ℂ), GlobalTheory.CMVal.IsCMType φ → ∀ M : Ideal (𝓞 K), M ≠ ⊥ →
      ∃ _ : DiscreteTopology (GlobalTheory.HeckePoisson.lat φ M), IsZLattice ℝ (GlobalTheory.HeckePoisson.lat φ M) := by
  intro K _ _ _ I _ φ h M hM
  classical
  rw [lat_eq_comap h M hM]
  exact ⟨inferInstance, inferInstance⟩

end GlobalTheory.HeckePoisson
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeMellinGaussIntegrandUnitMul
section
open NumberField MeasureTheory

noncomputable section

namespace GlobalTheory.HeckeShift

theorem hmon_mul_unit {ζ : ℂ} (hζ : ‖ζ‖ = 1) (n : ℤ) (v : ℂ) :
    GlobalTheory.HeckeTheta.hmon n (ζ * v) = ζ ^ (-n) * GlobalTheory.HeckeTheta.hmon n v := by
  have hζ0 : ζ ≠ 0 := by rintro rfl; simp at hζ
  unfold GlobalTheory.HeckeTheta.hmon
  split_ifs with h
  · have hc : starRingEnd ℂ ζ = ζ⁻¹ := by
      rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hζ]; simp
    rw [map_mul, mul_pow, hc, inv_pow, ← zpow_natCast, ← zpow_neg, Int.toNat_of_nonneg h]
  · rw [mul_pow, ← zpow_natCast ζ, Int.toNat_of_nonneg (by omega)]

theorem factor_shift (n : ℤ) (y : ℝ) {z : ℂ} (hz : z ≠ 0) (w : ℂ) :
    GlobalTheory.HeckeTheta.hmon n ((Real.exp (y / 2) : ℂ) * (z * w)) *
                 Complex.exp ((-2 * Real.pi * ‖(Real.exp (y / 2) : ℂ) * (z * w)‖ ^ 2 : ℝ) : ℂ) =
      (z / ((‖z‖ : ℝ) : ℂ)) ^ (-n) *
        (GlobalTheory.HeckeTheta.hmon n ((Real.exp ((y + Real.log (‖z‖ ^ 2)) / 2) : ℂ) * w) *
          Complex.exp ((-2 * Real.pi * ‖(Real.exp ((y + Real.log (‖z‖ ^ 2)) / 2) : ℂ) * w‖ ^ 2 : ℝ) : ℂ)) := by
  have hn0 : (0 : ℝ) < ‖z‖ := norm_pos_iff.2 hz
  have hE : Real.exp ((y + Real.log (‖z‖ ^ 2)) / 2) = Real.exp (y / 2) * ‖z‖ := by
    rw [Real.log_pow, add_div, Real.exp_add]
    congr 1
    rw [show ((2 : ℕ) : ℝ) * Real.log ‖z‖ / 2 = Real.log ‖z‖ by push_cast; ring, Real.exp_log hn0]
  have hzc : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
  have hζ : ‖z / ((‖z‖ : ℝ) : ℂ)‖ = 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm, div_self hn0.ne']
  have hv : (Real.exp (y / 2) : ℂ) * (z * w) =
      (z / ((‖z‖ : ℝ) : ℂ)) * ((Real.exp ((y + Real.log (‖z‖ ^ 2)) / 2) : ℂ) * w) := by
    rw [hE]; push_cast; field_simp
  rw [hv, hmon_mul_unit hζ, norm_mul, hζ, one_mul, mul_assoc]

theorem sum_ulog {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] {I : Type} [Fintype I]
    (φ : I → K →+* ℂ) (hφ : GlobalTheory.CMVal.IsCMType φ) (u : (𝓞 K)ˣ) : ∑ i, GlobalTheory.HeckeTheta.ulog φ u i = 0 := by
  have hbij : Function.Bijective (fun i => InfinitePlace.mk (φ i)) := by
    constructor
    · intro i j hij
      obtain ⟨k, _, hk⟩ := hφ (φ i)
      have hi := hk i (Or.inl rfl)
      rcases InfinitePlace.mk_eq_iff.1 hij with h | h
      · rw [hi, hk j (Or.inl h)]
      · rw [hi, hk j (Or.inr (by rw [← h]; ext x; simp [ComplexEmbedding.conjugate_coe_eq]))]
    · intro w
      obtain ⟨k, hk, _⟩ := hφ w.embedding
      refine ⟨k, ?_⟩
      rcases hk with h | h
      · simp only; rw [← h, InfinitePlace.mk_embedding]
      · simp only; rw [← InfinitePlace.mk_conjugate_eq (φ k), ← h, InfinitePlace.mk_embedding]
  have h0 := NumberField.Units.sum_mult_mul_log u
  rw [← (Equiv.ofBijective _ hbij).sum_comp] at h0
  rw [← h0]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hm : (InfinitePlace.mk (φ i)).mult = 2 :=
    InfinitePlace.mult_isComplex ⟨_, IsTotallyComplex.isComplex _⟩
  simp only [Equiv.ofBijective_apply, InfinitePlace.apply, hm, GlobalTheory.HeckeTheta.ulog, Real.log_pow]

end GlobalTheory.HeckeShift

theorem GlobalTheory.HeckeShift.term_unit_mul : ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I]
    (φ : I → K →+* ℂ), GlobalTheory.CMVal.IsCMType φ → ∀ (n : I → ℤ) (s : ℂ) (u : (𝓞 K)ˣ) (α : K) (y : I → ℝ),
    GlobalTheory.HeckeMellin.term n s (GlobalTheory.HeckeTheta.emb φ (((u : 𝓞 K) : K) * α)) y =
      GlobalTheory.HeckeStrip.wt φ n ((u : 𝓞 K) : K) *
        GlobalTheory.HeckeMellin.term n s (GlobalTheory.HeckeTheta.emb φ α) (y + GlobalTheory.HeckeTheta.ulog φ u) := by
  intro K _ _ _ I _ φ hφ n s u α y
  have hsum : (∑ i, (y + GlobalTheory.HeckeTheta.ulog φ u) i) = ∑ i, y i := by
    simp only [Pi.add_apply, Finset.sum_add_distrib, GlobalTheory.HeckeShift.sum_ulog φ hφ u, add_zero]
  have hu0 : ((u : 𝓞 K) : K) ≠ 0 := by
    intro h
    exact (Units.ne_zero u) (by exact_mod_cast h)
  unfold GlobalTheory.HeckeMellin.term
  rw [hsum, ← mul_assoc]
  congr 1
  unfold GlobalTheory.HeckeTheta.gauss GlobalTheory.HeckeStrip.wt
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [GlobalTheory.HeckeTheta.dil, GlobalTheory.HeckeTheta.emb, GlobalTheory.HeckeTheta.ulog, Pi.add_apply, map_mul]
  exact GlobalTheory.HeckeShift.factor_shift (n i) (y i) ((map_ne_zero _).2 hu0) (φ i α)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianAdjointProperties
section
noncomputable section

namespace GlobalTheory.LieDisc.HAdjAlg

open NumberField Matrix GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LieDisc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem map_mul_cc (A B : Matrix (Fin r) (Fin r) E) : (A * B).map cc = A.map cc * B.map cc :=
  Matrix.map_mul (f := (IsCMField.complexConj E : E →+* E))

theorem map_map_cc (A : Matrix (Fin r) (Fin r) E) : (A.map cc).map cc = A := by
  ext i j; simp [cc_cc]

theorem herm_eq_dot (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) :
    herm G x y = x ⬝ᵥ (G *ᵥ fun b => cc (y b)) := by
  simp [herm, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

theorem cc_mulVec (A : Matrix (Fin r) (Fin r) E) (y : Fin r → E) :
    (fun b => cc ((A *ᵥ y) b)) = A.map cc *ᵥ fun b => cc (y b) := by
  ext i; simp [mulVec, dotProduct, cc, map_sum, map_mul]

theorem map_one_cc : (1 : Matrix (Fin r) (Fin r) E).map cc = 1 := by
  ext i j; by_cases h : i = j <;> simp [one_apply, h, cc]

theorem map_smul_cc (c : E) (A : Matrix (Fin r) (Fin r) E) : (c • A).map cc = cc c • A.map cc := by
  ext i j; simp [cc, map_mul]

theorem trace_map_cc (A : Matrix (Fin r) (Fin r) E) : (A.map cc).trace = cc A.trace := by
  simp [Matrix.trace, cc, map_sum]

end GlobalTheory.LieDisc.HAdjAlg

open NumberField Matrix GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LieDisc GlobalTheory.LieDisc.HAdjAlg

theorem GlobalTheory.LieDisc.hAdj_algebra : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E), (∀ a b, cc (G a b) = G b a) → G.det ≠ 0 → (∀ (Y : Matrix (Fin r) (Fin r) E) (x y : Fin r → E), herm G (Y *ᵥ x) y = herm G x (hAdj G Y *ᵥ y)) ∧ (∀ Y Z : Matrix (Fin r) (Fin r) E, hAdj G (Y * Z) = hAdj G Z * hAdj G Y) ∧ (∀ Y Z : Matrix (Fin r) (Fin r) E, hAdj G (Y + Z) = hAdj G Y + hAdj G Z) ∧ (∀ (c : E) (Y : Matrix (Fin r) (Fin r) E), hAdj G (c • Y) = cc c • hAdj G Y) ∧ hAdj G 1 = 1 ∧ (∀ Y : Matrix (Fin r) (Fin r) E, hAdj G (hAdj G Y) = Y) ∧ (∀ Y : Matrix (Fin r) (Fin r) E, (hAdj G Y).trace = cc Y.trace) ∧ (∀ Y : Matrix (Fin r) (Fin r) E, IsSkew G Y ↔ hAdj G Y = -Y) := by
  intro E _ _ _ r G hG hdet
  have hu : IsUnit G.det := isUnit_iff_ne_zero.mpr hdet
  have hGi : G * G⁻¹ = 1 := mul_nonsing_inv G hu
  have hiG : G⁻¹ * G = 1 := nonsing_inv_mul G hu
  have hGt : G.map cc = Gᵀ := by ext a b; simp [hG]
  have adj1 : ∀ (Y : Matrix (Fin r) (Fin r) E) (x y : Fin r → E),
      herm G (Y *ᵥ x) y = herm G x (hAdj G Y *ᵥ y) := by
    intro Y x y
    rw [herm_eq_dot, herm_eq_dot, cc_mulVec, hAdj, map_map_cc, mulVec_mulVec,
      show G * (G⁻¹ * Yᵀ * G) = Yᵀ * G by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hGi, Matrix.one_mul],
      ← mulVec_mulVec, dotProduct_mulVec x Yᵀ, vecMul_transpose]
  refine ⟨adj1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Y Z
    rw [hAdj, hAdj, hAdj, ← map_mul_cc, transpose_mul]
    congr 1
    simp only [Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ hu]
  · intro Y Z
    simp only [hAdj, transpose_add, Matrix.mul_add, Matrix.add_mul]
    ext i j; simp [cc]
  · intro c Y
    rw [hAdj, hAdj, ← map_smul_cc, transpose_smul, Matrix.mul_smul, Matrix.smul_mul]
  · rw [hAdj, transpose_one, Matrix.mul_one, hiG, map_one_cc]
  · intro Y
    have h1 : (G⁻¹).map cc * Gᵀ = 1 := by rw [← hGt, ← map_mul_cc, hiG, map_one_cc]
    have h2 : (G⁻¹)ᵀ * Gᵀ = 1 := by rw [← transpose_mul, hGi, transpose_one]
    rw [hAdj, hAdj, map_mul_cc, map_mul_cc, hGt, ← transpose_map, map_map_cc, transpose_mul, transpose_mul,
      transpose_transpose]
    calc _ = ((G⁻¹).map cc * Gᵀ) * Y * (G⁻¹ᵀ * Gᵀ) := by
          simp only [Matrix.mul_assoc]
      _ = Y := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
  · intro Y
    rw [hAdj, trace_map_cc, trace_mul_comm, ← Matrix.mul_assoc, hGi, Matrix.one_mul, trace_transpose]
  · intro Y
    have hadd : ∀ u w, herm G (Y *ᵥ u) w + herm G u (Y *ᵥ w) = herm G u ((hAdj G Y + Y) *ᵥ w) := by
      intro u w
      rw [adj1, herm_eq_dot, herm_eq_dot, herm_eq_dot, ← dotProduct_add, ← mulVec_add]
      congr 2
      ext b; simp [add_mulVec, cc, map_add]
    constructor
    · intro hs
      have hv : ∀ w, (hAdj G Y + Y) *ᵥ w = 0 := by
        intro w
        set v := (hAdj G Y + Y) *ᵥ w
        have h0 : ∀ u, herm G u v = 0 := fun u => by rw [← hadd]; exact hs u w
        have hGv : G *ᵥ (fun b => cc (v b)) = 0 := by
          ext i
          have := h0 (Pi.single i 1)
          rw [herm_eq_dot, single_dotProduct, one_mul] at this
          simpa using this
        have hcv : (fun b => cc (v b)) = 0 := by
          rw [← one_mulVec (fun b => cc (v b)), ← hiG, ← mulVec_mulVec, hGv, mulVec_zero]
        ext b
        have := congrFun hcv b
        simp only [Pi.zero_apply] at this
        rw [← cc_cc (v b), this]; simp [cc]
      have hA : hAdj G Y + Y = 0 := by
        ext i j
        have := congrFun (hv (Pi.single j 1)) i
        simpa [mulVec_single] using this
      exact eq_neg_of_add_eq_zero_left hA
    · intro h u w
      rw [hadd, h, neg_add_cancel, zero_mulVec]
      simp [herm, cc]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianGramDiagonalSignatureUnitary
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

noncomputable section
namespace GlobalTheory.SUCovolConj
open MeasureTheory Set
open scoped Pointwise

section General

variable {X : Type} [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [MeasurableSpace X]
  [BorelSpace X] [SecondCountableTopology X]

theorem isFundamentalDomain_conj (μ : Measure X) [μ.IsMulLeftInvariant] [SFinite μ]
    (H H' : Subgroup X) (s : X) (hH : ∀ g, g ∈ H' ↔ s⁻¹ * g * s ∈ H) {D : Set X}
    (hD : IsFundamentalDomain H D μ) :
    IsFundamentalDomain H' ((MulAut.conj s).toEquiv '' D) μ := by
  refine hD.image_of_equiv (MulAut.conj s).toEquiv ?_
    { toFun := fun g => ⟨s⁻¹ * g.1 * s, (hH g.1).1 g.2⟩
      invFun := fun g => ⟨s * g.1 * s⁻¹, (hH _).2 (by simpa [mul_assoc] using g.2)⟩
      left_inv := fun g => by ext; simp [mul_assoc]
      right_inv := fun g => by ext; simp [mul_assoc] } ?_
  · have : ((MulAut.conj s).toEquiv.symm : X → X) = (fun x => x * s) ∘ (fun x => s⁻¹ * x) := by
      funext x; simp [mul_assoc]
    rw [this]
    exact (quasiMeasurePreserving_mul_right μ s).comp
      (measurePreserving_mul_left μ s⁻¹).quasiMeasurePreserving
  · intro g x
    simp [Subgroup.smul_def, mul_assoc]

theorem covolume_conj (μ : Measure X) [μ.IsMulLeftInvariant] [SFinite μ]
    (H H' : Subgroup X) [Countable H] [Countable H'] (s : X)
    (hH : ∀ g, g ∈ H' ↔ s⁻¹ * g * s ∈ H) :
    covolume H' X μ = covolume H X μ := by
  have hH2 : ∀ g, g ∈ H ↔ s⁻¹⁻¹ * g * s⁻¹ ∈ H' := fun g => by rw [hH]; simp [mul_assoc]
  by_cases h : HasFundamentalDomain H X μ
  · obtain ⟨D, hD⟩ := h.ExistsIsFundamentalDomain
    have h1 := isFundamentalDomain_conj μ H H' s hH hD
    have h2 : IsFundamentalDomain H ((Equiv.mulRight s⁻¹) '' D) μ := by
      refine hD.image_of_equiv (Equiv.mulRight s⁻¹) ?_ (Equiv.refl _) ?_
      · have : ((Equiv.mulRight s⁻¹).symm : X → X) = fun x => x * s := by funext x; simp
        rw [this]; exact quasiMeasurePreserving_mul_right μ s
      · intro g x; simp [Subgroup.smul_def, mul_assoc]
    rw [h1.covolume_eq_volume, hD.covolume_eq_volume, hD.measure_eq h2]
    have : (MulAut.conj s).toEquiv '' D = s • ((Equiv.mulRight s⁻¹) '' D) := by
      rw [← Set.image_smul, Set.image_image]
      refine Set.image_congr fun y _ => ?_
      simp [mul_assoc]
    rw [this, measure_smul]
  · have h' : ¬ HasFundamentalDomain H' X μ := by
      rintro ⟨D, hD⟩; exact h ⟨_, isFundamentalDomain_conj μ H' H s⁻¹ hH2 hD⟩
    simp [covolume, h, h']

end General
section Concrete

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem gram_eq_mul (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (M : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G M = Mᵀ * G.map τ * M.map (starRingEnd ℂ) := by
  ext a b
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, hermC, ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul]
  exact Finset.sum_comm

theorem det_gram (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (M : Matrix (Fin r) (Fin r) ℂ) :
    (gram τ G M).det = M.det * (G.map τ).det * starRingEnd ℂ M.det := by
  rw [gram_eq_mul, det_mul, det_mul, det_transpose, (starRingEnd ℂ).map_det M, RingHom.mapMatrix_apply]

theorem col_eq_mulVec (M : Matrix (Fin r) (Fin r) ℂ) (a : Fin r) :
    ReciprocityTheory.ChartRestriction.G.FD.col M a = M *ᵥ ReciprocityTheory.ChartRestriction.G.FD.col (1 : Matrix (Fin r) (Fin r) ℂ) a := by
  ext k; simp [ReciprocityTheory.ChartRestriction.G.FD.col, mulVec, dotProduct, Matrix.one_apply]

theorem hermC_map_of_herm (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (γ : Matrix (Fin r) (Fin r) E)
    (h2 : ∀ x y, herm G (γ *ᵥ x) (γ *ᵥ y) = herm G x y) (u w : Fin r → ℂ) :
    hermC τ G (γ.map τ *ᵥ u) (γ.map τ *ᵥ w) = hermC τ G u w := by
  have key (a b : Fin r) : ∑ c, ∑ d, τ (γ c a) * τ (G c d) * (starRingEnd ℂ) (τ (γ d b)) =
      τ (G a b) := by
    have h := congrArg τ (h2 (Pi.single a 1) (Pi.single b 1))
    simp only [herm, cc, mulVec_single_one, Matrix.col_apply, map_sum, map_mul,
      IsCMField.complexEmbedding_complexConj] at h
    rw [h, Finset.sum_eq_single a (by intro c _ hc; simp [hc]) (by simp),
      Finset.sum_eq_single b (by intro c _ hc; simp [hc]) (by simp)]
    simp
  have hR : hermC τ G u w = ∑ a, ∑ b, u a *
      (∑ c, ∑ d, τ (γ c a) * τ (G c d) * (starRingEnd ℂ) (τ (γ d b))) * (starRingEnd ℂ) (w b) := by
    simp only [hermC, key]
  rw [hR]
  simp only [hermC, mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul, Finset.mul_sum,
    Finset.sum_mul]
  calc _ = ∑ c, ∑ d, ∑ a, ∑ b,
        u a * (τ (γ c a) * τ (G c d) * (starRingEnd ℂ) (τ (γ d b))) * (starRingEnd ℂ) (w b) := by
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    _ = _ := by
        refine (Finset.sum_congr rfl fun c _ => Finset.sum_comm).trans (Finset.sum_comm.trans ?_)
        refine Finset.sum_congr rfl fun a _ => ?_
        exact (Finset.sum_congr rfl fun c _ => Finset.sum_comm).trans Finset.sum_comm

theorem hermC_smul (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (c : ℂ) (u w : Fin r → ℂ) :
    hermC τ G (c • u) (c • w) = c * starRingEnd ℂ c * hermC τ G u w := by
  simp only [hermC, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem countable_inReal (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E)
    (Γ : Subgroup (GL (Fin r) E)) : Countable (inReal Ψ G Γ) := by
  haveI : Countable E :=
    Countable.of_equiv _ (Module.finBasis ℚ E).equivFun.toEquiv.symm
  haveI : Countable (Matrix (Fin r) (Fin r) E) := inferInstanceAs (Countable (Fin r → Fin r → E))
  haveI : Countable (GL (Fin r) E) :=
    Function.Injective.countable (f := (Units.val : GL (Fin r) E → _)) fun _ _ h => Units.ext h
  have : ((inReal Ψ G Γ : Subgroup (realSU Ψ G)) : Set (realSU Ψ G)).Countable := by
    refine ((Set.countable_range (embGL Ψ r)).preimage Subtype.val_injective).mono fun g hg => ?_
    obtain ⟨δ, -, hδ⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hg)
    exact ⟨δ, hδ⟩
  exact this.to_subtype

end Concrete

theorem covolume_inReal_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r p0 : ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (γ : GL (Fin r) E) (Δ : Subgroup (GL (Fin r) E)), (∀ a b, cc (G a b) = G b a) → (∀ τ : Ψ, gram τ.1 G (mat x τ) = Matrix.diagonal fun a : Fin r => ((sgn p0 (a : ℕ) : ℝ) : ℂ)) → (∀ u v, herm G ((γ : Matrix (Fin r) (Fin r) E) *ᵥ u) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) = herm G u v) → covolume (inReal Ψ G (Δ.map (MulAut.conj γ).toMonoidHom)) (realSU Ψ G) (riemHaar Ψ G x) = covolume (inReal Ψ G Δ) (realSU Ψ G) (riemHaar Ψ G x) := by
  intro E _ _ _ r p0 Ψ G x γ Δ _hG hx hγ
  set A : Ψ → GL (Fin r) ℂ := embGL Ψ r γ with hAdef
  have hAv : ∀ τ : Ψ, ((A τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) =
      (γ : Matrix (Fin r) (Fin r) E).map τ.1 := fun τ => rfl
  have hA : ∀ τ : Ψ, ∀ u w, hermC τ.1 G ((A τ : Matrix (Fin r) (Fin r) ℂ) *ᵥ u)
      ((A τ : Matrix (Fin r) (Fin r) ℂ) *ᵥ w) = hermC τ.1 G u w := by
    intro τ u w; rw [hAv]; exact hermC_map_of_herm τ.1 G _ hγ u w
  have hdet : ∀ τ : Ψ, (A τ : Matrix (Fin r) (Fin r) ℂ).det *
      starRingEnd ℂ (A τ : Matrix (Fin r) (Fin r) ℂ).det = 1 := by
    intro τ
    have hg : (G.map τ.1).det ≠ 0 := by
      intro h0
      have h1 := congrArg Matrix.det (hx τ)
      rw [det_gram, h0, mul_zero, zero_mul, det_diagonal] at h1
      refine (Finset.prod_ne_zero_iff.2 fun a _ => ?_) h1.symm
      simp only [sgn]; split_ifs <;> norm_num
    have e1 : ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 G (A τ : Matrix (Fin r) (Fin r) ℂ) =
        ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 G 1 := by
      ext a b
      simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, Matrix.of_apply]
      rw [col_eq_mulVec (A τ : Matrix (Fin r) (Fin r) ℂ) a, col_eq_mulVec (A τ : Matrix (Fin r) (Fin r) ℂ) b, hA]
    have h2 := congrArg Matrix.det e1
    rw [det_gram, det_gram, det_one, map_one, one_mul, mul_one] at h2
    apply mul_right_cancel₀ hg
    linear_combination h2
  have hroot : ∀ τ : Ψ, ∃ m : ℂ, m ^ r = (A τ : Matrix (Fin r) (Fin r) ℂ).det ∧ m * starRingEnd ℂ m = 1 := by
    intro τ
    rcases Nat.eq_zero_or_pos r with hr | hr
    · refine ⟨1, ?_, by simp⟩
      subst hr; simp
    · obtain ⟨m, hm⟩ := IsAlgClosed.exists_pow_nat_eq ((A τ : Matrix (Fin r) (Fin r) ℂ).det) hr
      refine ⟨m, hm, ?_⟩
      have h1 : (m * starRingEnd ℂ m) ^ r = 1 := by rw [mul_pow, ← map_pow, hm, hdet τ]
      rw [Complex.mul_conj] at h1 ⊢
      have h3 : (Complex.normSq m) ^ r = 1 := by exact_mod_cast h1
      rw [(pow_eq_one_iff_of_nonneg (Complex.normSq_nonneg m) hr.ne').1 h3]; simp
  choose m hm using hroot
  have hm0 : ∀ τ, m τ ≠ 0 := fun τ h => by simpa [h] using (hm τ).2
  let z : Ψ → GL (Fin r) ℂ := fun τ =>
    Units.map (algebraMap ℂ (Matrix (Fin r) (Fin r) ℂ)).toMonoidHom (Units.mk0 (m τ)⁻¹ (inv_ne_zero (hm0 τ)))
  have hzv : ∀ τ, ((z τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = (m τ)⁻¹ • (1 : Matrix (Fin r) (Fin r) ℂ) := by
    intro τ; simp [z, Algebra.algebraMap_eq_smul_one]
  have hzc : ∀ g : Ψ → GL (Fin r) ℂ, z * g = g * z := by
    intro g; funext τ; ext1
    simp only [Pi.mul_apply, Units.val_mul, hzv, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one]
  have hs0 : A * z ∈ realSU Ψ G := by
    intro τ
    have e : (((A * z) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) =
        (m τ)⁻¹ • (A τ : Matrix (Fin r) (Fin r) ℂ) := by
      simp only [Pi.mul_apply, Units.val_mul, hzv, Matrix.mul_smul, mul_one]
    rw [e]
    refine ⟨?_, fun u w => ?_⟩
    · rw [det_smul, Fintype.card_fin, inv_pow, (hm τ).1]
      have : (A τ : Matrix (Fin r) (Fin r) ℂ).det ≠ 0 := fun h => by simpa [h] using hdet τ
      exact inv_mul_cancel₀ this
    · rw [Matrix.smul_mulVec, Matrix.smul_mulVec, hermC_smul, hA, map_inv₀, ← mul_inv,
        (hm τ).2, inv_one, one_mul]
  let s : realSU Ψ G := ⟨A * z, hs0⟩
  have hconj : ∀ g : Ψ → GL (Fin r) ℂ, (A * z)⁻¹ * g * (A * z) = A⁻¹ * g * A := by
    intro g
    calc (A * z)⁻¹ * g * (A * z) = z⁻¹ * (A⁻¹ * g * A) * z := by group
      _ = z⁻¹ * (z * (A⁻¹ * g * A)) := by rw [mul_assoc, ← hzc]
      _ = A⁻¹ * g * A := by group
  haveI := countable_inReal Ψ G Δ
  haveI := countable_inReal Ψ G (Δ.map (MulAut.conj γ).toMonoidHom)
  haveI : (riemHaar Ψ G x).IsMulLeftInvariant := by unfold riemHaar; infer_instance
  haveI : SFinite (riemHaar Ψ G x) := by unfold riemHaar tangentHaar; infer_instance
  have key : ∀ δ, embGL Ψ r ((MulAut.conj γ).toMonoidHom δ) = A * embGL Ψ r δ * A⁻¹ := by
    intro δ; simp [hAdef, MulAut.conj_apply, map_mul, map_inv]
  refine covolume_conj (riemHaar Ψ G x) _ _ s fun g => ?_
  simp only [inReal, Subgroup.mem_subgroupOf, Subgroup.mem_map, Subgroup.coe_mul, Subgroup.coe_inv]
  rw [hconj]
  constructor
  · rintro ⟨δ', ⟨δ, hδ, rfl⟩, h⟩
    refine ⟨δ, hδ, ?_⟩
    rw [← h, key]
    group
  · rintro ⟨δ, hδ, h⟩
    refine ⟨_, ⟨δ, hδ, rfl⟩, ?_⟩
    rw [key, h]
    group

end GlobalTheory.SUCovolConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousCorrectionNextLevelStatement
section
open MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homogeneous_correction_next_level_alt : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), ∀ (n : ℕ) (K : ℕ → Ideal (MvPolynomial (Fin (n + 1)) R)), (∀ (e t : ℕ) (F : MvPolynomial (Fin (n + 1)) R), F.IsHomogeneous t → (∀ i, ∃ N : ℕ, (X i : MvPolynomial (Fin (n + 1)) R) ^ N * F ∈ K e) → F ∈ K e) → (∀ e, ∀ a ∈ I ^ (e + 1), C a ∈ K e) → (∀ (e t : ℕ) (F : MvPolynomial (Fin (n + 1)) R), F.IsHomogeneous t → F ∈ K e → ∀ i, ∃ (N : ℕ) (G : MvPolynomial (Fin (n + 1)) R), G.IsHomogeneous (t + N) ∧ (∀ m, coeff m G ∈ I ^ (e + 1)) ∧ (X i : MvPolynomial (Fin (n + 1)) R) ^ N * F - G ∈ K (e + 1)) → ∃ t₀ : ℕ, ∀ t, t₀ ≤ t → ∀ (e : ℕ) (F : MvPolynomial (Fin (n + 1)) R), F.IsHomogeneous t → F ∈ K e → ∃ G : MvPolynomial (Fin (n + 1)) R, G.IsHomogeneous t ∧ (∀ m, coeff m G ∈ I ^ (e + 1)) ∧ F - G ∈ K (e + 1) := by
  first | exact @GlobalTheory.homogeneous_correction_next_level | exact GlobalTheory.homogeneous_correction_next_level | (intros; apply GlobalTheory.homogeneous_correction_next_level <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyNoetherianOfIsQProjOverNoethStatement
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLocallyNoetherian_of_isQProjOver_noetherian : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0}) (f : X ⟶ Sp R), IsQProjOver f → IsLocallyNoetherian X := by
  first | exact @GlobalTheory.isLocallyNoetherian_of_isQProjOver_noeth | exact GlobalTheory.isLocallyNoetherian_of_isQProjOver_noeth | (intros; apply GlobalTheory.isLocallyNoetherian_of_isQProjOver_noeth <;> assumption)
end

