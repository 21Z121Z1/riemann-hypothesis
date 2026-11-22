import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0059
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0039
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0060
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0041
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0044
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0036
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenTwistGenerated
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0061
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PNefProductNonneg
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0013
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PCutRegular
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0016

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFibreRelLift
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace FibreRelLift

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (ℓ : ℕ)

def ratio (p : Σ k, ι k) : chartRingZ y c :=
  ⟨y p / y ⟨p.1, c p.1⟩, Algebra.subset_adjoin ⟨p, rfl⟩⟩

def dehom : MRing ι →ₐ[ℤ] chartRingZ y c := aeval (ratio y c)

theorem coe_dehom (f : MRing ι) :
    ((dehom y c f : chartRingZ y c) : Ω) = aeval (fun k => (y ⟨k, c k⟩)⁻¹) (mConeMap y f) := by
  show ((chartRingZ y c).val.toRingHom.comp (dehom y c).toRingHom) f =
    ((aeval (fun k => (y ⟨k, c k⟩)⁻¹) : MvPolynomial K Ω →ₐ[Ω] Ω).toRingHom.comp (mConeMap y).toRingHom) f
  refine RingHom.congr_fun (MvPolynomial.ringHom_ext (fun r => ?_) (fun p => ?_)) f
  · simp
  · simp [dehom, ratio, mConeMap, div_eq_mul_inv]

theorem coe_dehom_of_homog {f : MRing ι} {d : K → ℕ} (hf : IsMultiHomog f d) :
    ((dehom y c f : chartRingZ y c) : Ω) = aeval y f * ∏ k, (y ⟨k, c k⟩)⁻¹ ^ d k := by
  rw [coe_dehom, ProjLine.mConeMap_eq_of_isMultiHomog y hf, map_mul, aeval_C, map_prod]
  simp only [map_pow, aeval_X, Algebra.algebraMap_self, RingHom.id_apply]

theorem dehom_eq_zero {f : MRing ι} (hf : f ∈ mCoordIdeal y) : dehom y c f = 0 := by
  have h0 : mConeMap y f = 0 := RingHom.mem_ker.mp hf
  apply Subtype.ext
  rw [coe_dehom, h0]
  simp

abbrev ChartQ := chartRingZ y c ⧸ Ideal.span {((ℓ : ℕ) : chartRingZ y c)}

theorem natCast_chartQ : ((ℓ : ℕ) : ChartQ y c ℓ) = 0 := by
  rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {((ℓ : ℕ) : chartRingZ y c)})) ℓ]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)

def dehomMod : MRingOver (ZMod ℓ) ι →+* ChartQ y c ℓ :=
  eval₂Hom (ZMod.castHom (ringChar.dvd (natCast_chartQ y c ℓ)) (ChartQ y c ℓ))
    (fun p => Ideal.Quotient.mk _ (ratio y c p))

theorem dehomMod_map (f : MRing ι) :
    dehomMod y c ℓ (MvPolynomial.map (Int.castRingHom (ZMod ℓ)) f) =
      Ideal.Quotient.mk (Ideal.span {((ℓ : ℕ) : chartRingZ y c)}) (dehom y c f) := by
  show ((dehomMod y c ℓ).comp (MvPolynomial.map (Int.castRingHom (ZMod ℓ)))) f =
    ((Ideal.Quotient.mk (Ideal.span {((ℓ : ℕ) : chartRingZ y c)})).comp (dehom y c).toRingHom) f
  refine RingHom.congr_fun (MvPolynomial.ringHom_ext (fun r => ?_) (fun p => ?_)) f
  · simp [dehomMod]
  · simp [dehomMod, dehom]

theorem idealOver_le_ker : GenOnFibres.idealOver y (ZMod ℓ) ≤ RingHom.ker (dehomMod y c ℓ) := by
  refine Ideal.map_le_iff_le_comap.mpr fun f hf => ?_
  rw [Ideal.mem_comap, RingHom.mem_ker, dehomMod_map, dehom_eq_zero y c hf, map_zero]

def dehomQuot : MRingOver (ZMod ℓ) ι ⧸ GenOnFibres.idealOver y (ZMod ℓ) →+* ChartQ y c ℓ :=
  Ideal.Quotient.lift _ (dehomMod y c ℓ) fun _ hf => RingHom.mem_ker.mp (idealOver_le_ker y c ℓ hf)

theorem dehomQuot_smul (r : MRingOver (ZMod ℓ) ι) (m : MRingOver (ZMod ℓ) ι ⧸ GenOnFibres.idealOver y (ZMod ℓ)) :
    dehomQuot y c ℓ (r • m) = dehomMod y c ℓ r * dehomQuot y c ℓ m := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective m
  rw [GenOnFibres.smul_mk, dehomQuot, Ideal.Quotient.lift_mk, Ideal.Quotient.lift_mk, map_mul]

theorem dehomMod_cellMon (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {I : ∀ k, Finset (ι k)} (hI : ∀ k, ∀ i ∈ I k, i = c k)
    {t : MRingOver (ZMod ℓ) ι} (ht : t ∈ KH.cellMon (ZMod ℓ) I) : dehomMod y c ℓ t = 1 := by
  have hle : KH.cellMon (ZMod ℓ) I ≤ (⊥ : Submonoid (ChartQ y c ℓ)).comap (dehomMod y c ℓ).toMonoidHom := by
    unfold KH.cellMon
    refine Submonoid.closure_le.mpr ?_
    rintro f ⟨k, i, hi, rfl⟩
    obtain rfl := hI k i hi
    have h1 : ratio y c ⟨k, c k⟩ = 1 := Subtype.ext (by simp [ratio, div_self (hc k)])
    rw [SetLike.mem_coe, Submonoid.mem_comap, Submonoid.mem_bot]
    simp [dehomMod, h1]
  exact Submonoid.mem_bot.mp (hle ht)

variable {y c ℓ}

def dehomLocFun (T : Submonoid (MRingOver (ZMod ℓ) ι)) (hT : ∀ t ∈ T, dehomMod y c ℓ t = 1)
    (x : LocalizedModule T (MRingOver (ZMod ℓ) ι ⧸ GenOnFibres.idealOver y (ZMod ℓ))) : ChartQ y c ℓ :=
  x.liftOn (fun p => dehomQuot y c ℓ p.1) (by
    rintro ⟨m, s⟩ ⟨m', s'⟩ ⟨u, hu⟩
    have h := congrArg (dehomQuot y c ℓ) hu
    simp only [Submonoid.smul_def, dehomQuot_smul, hT _ u.2, hT _ s.2, hT _ s'.2, one_mul] at h
    exact h)

theorem dehomLocFun_mk (T : Submonoid (MRingOver (ZMod ℓ) ι)) (hT : ∀ t ∈ T, dehomMod y c ℓ t = 1)
    (m : MRingOver (ZMod ℓ) ι ⧸ GenOnFibres.idealOver y (ZMod ℓ)) (t : T) :
    dehomLocFun T hT (LocalizedModule.mk m t) = dehomQuot y c ℓ m := by
  unfold dehomLocFun
  rw [LocalizedModule.liftOn_mk]

def dehomLoc (T : Submonoid (MRingOver (ZMod ℓ) ι)) (hT : ∀ t ∈ T, dehomMod y c ℓ t = 1) :
    LocalizedModule T (MRingOver (ZMod ℓ) ι ⧸ GenOnFibres.idealOver y (ZMod ℓ)) →+* ChartQ y c ℓ where
  toFun := dehomLocFun T hT
  map_one' := by
    rw [show (1 : LocalizedModule T (MRingOver (ZMod ℓ) ι ⧸ GenOnFibres.idealOver y (ZMod ℓ))) =
      LocalizedModule.mk 1 1 by rw [OreLocalization.one_def], dehomLocFun_mk, map_one]
  map_mul' x x' := by
    induction x, x' using LocalizedModule.induction_on₂ with
    | h m m' s s' =>
      rw [LocalizedModule.mk_mul_mk, dehomLocFun_mk, dehomLocFun_mk, dehomLocFun_mk, map_mul]
  map_zero' := by
    rw [← LocalizedModule.zero_mk 1, dehomLocFun_mk, map_zero]
  map_add' x x' := by
    induction x, x' using LocalizedModule.induction_on₂ with
    | h m m' s s' =>
      rw [LocalizedModule.mk_add_mk, dehomLocFun_mk, dehomLocFun_mk, dehomLocFun_mk, map_add,
        Submonoid.smul_def, Submonoid.smul_def, dehomQuot_smul, dehomQuot_smul, hT _ s.2, hT _ s'.2,
        one_mul, one_mul]

theorem dehomLoc_mk (T : Submonoid (MRingOver (ZMod ℓ) ι)) (hT : ∀ t ∈ T, dehomMod y c ℓ t = 1)
    (m : MRingOver (ZMod ℓ) ι ⧸ GenOnFibres.idealOver y (ZMod ℓ)) (t : T) :
    dehomLoc T hT (LocalizedModule.mk m t) = dehomQuot y c ℓ m :=
  dehomLocFun_mk T hT m t

end FibreRelLift

open FibreRelLift in

theorem FibreRelLift.proof : FibreRelLift.Statement := by
  intro K _ _ ι _ _ Ω _ y ℓ a r s J u hs hc _ hrel
  set c := GenOnFibres.cellChart J with hcdef
  have hI : ∀ k, ∀ i ∈ J.1 k, i = c k := by
    intro k i hi
    have h1 : (J.1 k).card - 1 = 0 := (Finset.sum_eq_zero_iff.mp J.2.2) k (Finset.mem_univ k)
    exact Finset.card_le_one.mp (by omega) i hi (c k) (GenOnFibres.cellChart_mem J k)
  have hT : ∀ t ∈ KH.cellMon (ZMod ℓ) J.1, dehomMod y c ℓ t = 1 := fun t ht =>
    dehomMod_cellMon y c ℓ hc hI ht
  have hw : ∀ j, s j * ∏ k, y ⟨k, c k⟩ ^ (-a k) ∈ chartRingZ y c := fun j => by
    simpa using hs j c hc
  have hz : ∀ j, dehomLoc _ hT (GenOnFibres.secCoch y (ZMod ℓ) (s j) a J) =
      Ideal.Quotient.mk (Ideal.span {((ℓ : ℕ) : chartRingZ y c)}) ⟨_, hw j⟩ := by
    intro j
    obtain ⟨e, F, ⟨d, hF, hd, hv⟩, h, he⟩ := GenOnFibres.secCoch_spec (S := ZMod ℓ) (hs j) J hc
    rw [he, dehomLoc_mk, dehomQuot, Ideal.Quotient.lift_mk, dehomMod_map]
    congr 1
    apply Subtype.ext
    rw [coe_dehom_of_homog y c hF, hv, mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [inv_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ (hc k)]
    congr 1
    have := hd k
    omega
  have h1 := congrArg (dehomLoc _ hT) hrel
  rw [map_sum, map_one] at h1
  simp only [map_mul, hz] at h1
  choose b hb using fun j => Ideal.Quotient.mk_surjective (dehomLoc _ hT (u j))
  simp only [← hb, ← map_mul, ← map_sum] at h1
  rw [← map_one (Ideal.Quotient.mk (Ideal.span {((ℓ : ℕ) : chartRingZ y c)})), Ideal.Quotient.eq,
    Ideal.mem_span_singleton'] at h1
  obtain ⟨q, hq⟩ := h1
  refine ⟨fun j => (b j : Ω), -(q : Ω), fun j => (b j).2, neg_mem q.2, ?_⟩
  have h2 := congrArg (fun x : chartRingZ y c => (x : Ω)) hq
  push_cast at h2
  linear_combination (-1 : Ω) * h2

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenTwistVanish
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

theorem GenTwistVanish.proof (hS : KH.TheoremSStatement) (hG : QuotPartGraded.Statement)
    (hK : GenKoszulStep.Statement) : GenTwistVanish.Statement := by
  intro S _ K _ _ ι _ _ V α hV hα e
  obtain ⟨-, ⟨c₁, hc₁⟩, -⟩ := hS S K ι (MRingOver S ι ⧸ V) (KH.quotPart S V) inferInstance
    inferInstance (hG S K ι V hV)
  obtain ⟨R, hR⟩ := hK S K ι V α hV hα
  set B : ℤ := ∑ k, (|e k| + (R : ℤ) * |α k|) with hB
  refine ⟨(c₁ + B).toNat, ?_⟩

  have key : ∀ j n : ℕ, (c₁ + B).toNat ≤ n → ∀ i : ℕ, 1 ≤ i →
      Subsingleton (KH.cechHc ι (KH.quotPart S V) (e + ((j : ℤ) - R) • α + fun _ => (n : ℤ)) i) := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro n hn i hi
      by_cases hj : j < R
      · refine hc₁ _ i hi fun k => ?_
        have h1 : |e k| + (R : ℤ) * |α k| ≤ B :=
          Finset.single_le_sum (f := fun k => |e k| + (R : ℤ) * |α k|)
            (fun k _ => by positivity) (Finset.mem_univ k)
        have h2 : c₁ + B ≤ n := by omega
        have h3 : |((j : ℤ) - R) * α k| ≤ (R : ℤ) * |α k| := by
          rw [abs_mul]
          refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
          rw [abs_le]
          constructor <;> omega
        have h4 := neg_abs_le (((j : ℤ) - R) * α k)
        have h5 := neg_abs_le (e k)
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        linarith
      · rw [not_lt] at hj
        refine hR _ (fun p hp1 hpR i' hi' => ?_) i hi
        have heq : (e + ((j : ℤ) - R) • α + fun _ => (n : ℤ)) - (p : ℤ) • α =
            e + (((j - p : ℕ) : ℤ) - R) • α + fun _ => (n : ℤ) := by
          funext k
          simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
          push_cast [Nat.cast_sub (le_trans hpR hj)]
          ring
        rw [heq]
        exact ih (j - p) (by omega) n hn i' hi'
  intro m n hn
  have h := key (m + R) n hn 1 le_rfl
  have heq : (e + (((m + R : ℕ) : ℤ) - R) • α + fun _ => (n : ℤ)) =
      e + (m : ℤ) • α + fun _ => (n : ℤ) := by
    funext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring
  rwa [heq] at h

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGeneratedMixedNonneg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

theorem GeneratedMixedNonneg.proof (hGP : GeneratedProductNonneg.Statement) :
    GeneratedMixedNonneg.Statement := by
  intro F _ K _ _ ι _ _ V n bs hV hgen
  exact hGP F K ι (fun V _ L => NumbersDVR.intNum F V L) V n bs
    (NumbersDVR.IntNumIsFieldIntersection.full F K ι) hV hgen

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGeneratedPow
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

theorem GeneratedPow.proof : GeneratedPow.Statement := by
  intro S _ K _ _ ι _ _ V n t hn
  induction t with
  | zero =>
    have h0 := GenTwistGenerated.generated_diag (S := S) (ι := ι) (V := V) 0
    have e : (fun _ : K => ((0 : ℕ) : ℤ)) = (0 • n : K → ℤ) := by
      funext k
      simp
    rw [← e]
    exact h0
  | succ t ih =>
    rw [succ_nsmul']
    exact GenTwistGenerated.generated_add hn ih

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGramContraction
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

namespace GramContraction

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem det_gram_le_prod {α : Type*} [Fintype α] [DecidableEq α] (y : α → V) :
    (Matrix.gram ℝ y).det ≤ ∏ a, ‖y a‖ ^ 2 := by
  by_cases hy : LinearIndependent ℝ y
  · let e := Fintype.equivFin α
    have h := HadamardGramBound.det_gram_le_prod_norm_sq (y ∘ e.symm) (hy.comp _ e.symm.injective)
    have hg : Matrix.gram ℝ (y ∘ e.symm) = (Matrix.gram ℝ y).submatrix e.symm e.symm := by
      ext i j; simp [Matrix.gram_apply]
    rw [hg, Matrix.det_submatrix_equiv_self] at h
    rwa [Fintype.prod_equiv e.symm (fun i => ‖(y ∘ e.symm) i‖ ^ 2) (fun a => ‖y a‖ ^ 2) (fun _ => rfl)] at h
  · have h0 : (Matrix.gram ℝ y).det = 0 := by
      by_contra h; exact hy (Matrix.det_gram_ne_zero_iff_linearIndependent.mp h)
    rw [h0]; exact Finset.prod_nonneg fun _ _ => sq_nonneg _

theorem gram_comb {α : Type*} [Fintype α] (M : Matrix α α ℝ) (y : α → V) :
    Matrix.gram ℝ (fun a => ∑ b, M a b • y b) = M * Matrix.gram ℝ y * M.transpose := by
  ext i k
  simp only [Matrix.gram_apply, Matrix.mul_apply, Matrix.transpose_apply, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end GramContraction

theorem GramContraction.proof : GramContraction.Statement := by
  intro ι κ _ _ _ _ V _ _ Ψ u w hΨ
  let e := EuclideanSpace.basisFun ι ℝ
  let U : Matrix ι ι ℝ := Matrix.of fun i j => u i j
  let M : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ := Matrix.fromBlocks U 0 0 1
  let y : ι ⊕ κ → V := Sum.elim (fun i => Ψ (e i)) w
  have hu : ∀ i, Ψ (u i) = ∑ j, U i j • Ψ (e j) := fun i => by
    conv_lhs => rw [← e.sum_repr (u i)]
    simp [U, e, map_sum, map_smul]
  have hfam : Sum.elim (Ψ ∘ u) w = fun a => ∑ b, M a b • y b := by
    funext a
    rcases a with i | k
    · simp [Fintype.sum_sum_type, M, y, hu]
    · simp [Fintype.sum_sum_type, M, y, Matrix.one_apply]
  have hGu : Matrix.gram ℝ u = U * U.transpose := by
    ext i j
    rw [Matrix.mul_apply]
    simp [Matrix.gram_apply, U, PiLp.inner_apply, mul_comm]
  have hdet : (Matrix.gram ℝ (Sum.elim (Ψ ∘ u) w)).det = U.det ^ 2 * (Matrix.gram ℝ y).det := by
    rw [hfam, GramContraction.gram_comb, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
      Matrix.det_fromBlocks_zero₂₁, Matrix.det_one]
    ring
  have hP : ∏ i, ‖Ψ (e i)‖ ^ 2 ≤ 1 :=
    Finset.prod_le_one (fun _ _ => sq_nonneg _) fun i _ => by
      have := hΨ (e i); rw [e.orthonormal.1 i] at this
      nlinarith [norm_nonneg (Ψ (e i))]
  have hW : 0 ≤ ∏ j, ‖w j‖ ^ 2 := Finset.prod_nonneg fun _ _ => sq_nonneg _
  have hH := GramContraction.det_gram_le_prod y
  rw [Fintype.prod_sum_type] at hH
  rw [hdet, hGu, Matrix.det_mul, Matrix.det_transpose, ← sq]
  refine mul_le_mul_of_nonneg_left (hH.trans ?_) (sq_nonneg _)
  simpa [y] using mul_le_of_le_one_left hW hP

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PKleimanNefF
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace KleimanNefF

variable {F : Type} [Field F] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isMultiProjPrime_dvr [DecidableEq K] {V : Ideal (MRingOver F ι)} (hV : IsMultiProjPrime V) :
    NumbersDVR.IsMultiProjPrime (R := F) (ι := ι) V :=
  ⟨hV.1, (NumbersDVR.VocabMultiHomogIdeal.proof NumbersDVR.VocabMultiHomog.proof F K ι V).1 hV.2.1, hV.2.2⟩

theorem isProjVarF_of_mem_support [DecidableEq K] {V : Ideal (MRingOver F ι)} {n : ℕ}
    (hV : IsProjVarF V (n + 1)) {f g : MRingOver F ι} {bf bg : K → ℕ}
    (hf : NumbersDVR.IsMultiHomog f bf) (hg : NumbersDVR.IsMultiHomog g bg) (hfV : f ∉ V) (hgV : g ∉ V)
    {W : Ideal (MRingOver F ι)} (hW : W ∈ (ReciprocityTheory.ChartRestriction.G.AI.I1.ratDiv V f g).support) :
    IsProjVarF W n := by
  have hVd := isMultiProjPrime_dvr hV.1
  have hrel : FieldNumbers.relDim V = ((n + 1 : ℕ) : WithBot (WithTop ℤ)) :=
    (FieldNumbers.CutRegular.relDim_eq_natCast_iff V (n + 1)).2 hV.2
  have key : ∀ (s : MRingOver F ι) (b : K → ℕ), NumbersDVR.IsMultiHomog s b → s ∉ V →
      ReciprocityTheory.ChartRestriction.G.Geo.divCycle V s W ≠ 0 → IsProjVarF W n := by
    intro s b hs hsV hne
    have hne' : NumbersDVR.divCycle V s W ≠ 0 := by
      rw [← NumbersDVR.VocabDivCycle.proof F K ι V s W]
      exact_mod_cast hne
    obtain ⟨hW1, hW2⟩ := FieldNumbers.DivCycleSupport.full F K ι V hVd n hrel b s hs hsV W hne'
    exact ⟨⟨hW1.isPrime, (NumbersDVR.VocabMultiHomogIdeal.proof NumbersDVR.VocabMultiHomog.proof F K ι W).2
      hW1.multiHomog, hW1.relevant⟩, (FieldNumbers.CutRegular.relDim_eq_natCast_iff W n).1 hW2⟩
  rw [Finsupp.mem_support_iff, ReciprocityTheory.ChartRestriction.G.AI.I1.ratDiv, Finsupp.sub_apply, Finsupp.mapRange_apply,
    Finsupp.mapRange_apply] at hW
  by_cases hfW : ReciprocityTheory.ChartRestriction.G.Geo.divCycle V f W = 0
  · refine key g bg hg hgV fun h => hW ?_
    rw [hfW, h]
    simp
  · exact key f bf hf hfV hfW

theorem eq_intNum [DecidableEq K] {I : IFamily F ι} (hI : IsFieldIntersection I) :
    ∀ (n : ℕ) (V : Ideal (MRingOver F ι)) (L : Fin n → K → ℤ), IsProjVarF V n →
      I V n L = NumbersDVR.intNum F V L := by
  have hJ : IsFieldIntersection (F := F) (ι := ι) (fun V _ L => NumbersDVR.intNum F V L) :=
    NumbersDVR.IntNumIsFieldIntersection.full F K ι
  intro n
  induction n with
  | zero =>
    intro V L hV
    choose i hi using hV.1.2.2
    exact (hI.1 V L i hV hi).trans (hJ.1 V L i hV hi).symm
  | succ n ih =>
    intro V L hV
    obtain ⟨bf, bg, f, g, hf, hg, hfV, hgV, hb⟩ :=
      FieldNumbers.ExistsForm.full F K ι V (isMultiProjPrime_dvr hV.1) (L (Fin.last n))
    have hs : IsRatSection V (L (Fin.last n)) f g :=
      ⟨bf, bg, (NumbersDVR.VocabMultiHomog.proof F K ι f bf).2 hf,
        (NumbersDVR.VocabMultiHomog.proof F K ι g bg).2 hg, hfV, hgV, fun k => congrFun hb k⟩
    have e1 : I V (n + 1) L = ReciprocityTheory.ChartRestriction.G.AI.I1.cycEval (fun W => I W n (Fin.init L))
        (ReciprocityTheory.ChartRestriction.G.AI.I1.ratDiv V f g) := by
      have h := hI.2 V n (Fin.init L) (L (Fin.last n)) f g hV hs
      rwa [Fin.snoc_init_self] at h
    have e2 : NumbersDVR.intNum F V L = ReciprocityTheory.ChartRestriction.G.AI.I1.cycEval
        (fun W => NumbersDVR.intNum F W (Fin.init L)) (ReciprocityTheory.ChartRestriction.G.AI.I1.ratDiv V f g) := by
      have h := hJ.2 V n (Fin.init L) (L (Fin.last n)) f g hV hs
      rwa [Fin.snoc_init_self] at h
    rw [e1, e2, ReciprocityTheory.ChartRestriction.G.AI.I1.cycEval, ReciprocityTheory.ChartRestriction.G.AI.I1.cycEval]
    refine Finsupp.sum_congr fun W hW => ?_
    rw [ih W _ (isProjVarF_of_mem_support hV hf hg hfV hgV hW)]

theorem map_update_add₂ {I : IFamily F ι} (hI : IsFieldIntersection I) {V : Ideal (MRingOver F ι)} {n : ℕ}
    (hV : IsProjVarF V n) (L : Fin n → K → ℤ) (j : Fin n) (x y : K → ℤ) :
    I V n (Function.update L j (x + y)) = I V n (Function.update L j x) + I V n (Function.update L j y) := by
  classical
  rw [eq_intNum hI n V _ hV, eq_intNum hI n V _ hV, eq_intNum hI n V _ hV]
  have hVd := isMultiProjPrime_dvr hV.1
  exact FieldNumbers.IntNumAdd.full F K ι V hVd.multiHomog hVd.relevant n
    ((FieldNumbers.CutRegular.relDim_eq_natCast_iff V n).2 hV.2) L j x y

theorem nsmul_position {I : IFamily F ι} (hI : IsFieldIntersection I) {V : Ideal (MRingOver F ι)} {n : ℕ}
    (hV : IsProjVarF V n) (L : Fin n → K → ℤ) (j : Fin n) (m : ℕ) (x : K → ℤ) :
    I V n (Function.update L j ((m : ℤ) • x)) = m * I V n (Function.update L j x) := by
  induction m with
  | zero =>
    have h := map_update_add₂ hI hV L j 0 0
    rw [add_zero] at h
    rw [Nat.cast_zero, zero_smul, zero_mul]
    linarith
  | succ m ih =>
    rw [Nat.cast_succ, add_smul, one_smul, map_update_add₂ hI hV, ih]
    ring

end KleimanNefF

theorem KleimanNefF.proof (hKA : KH.KAmpStatement) (hGP : GeneratedProductNonneg.Statement) :
    KH.KleimanNefFStatement := by
  classical
  intro F _ K _ ι _ I V n a hI hV hnef
  let _ : LinearOrder K := LinearOrder.lift' (Fintype.equivFin K) (Fintype.equivFin K).injective
  let _ : ∀ k, LinearOrder (ι k) := fun k =>
    LinearOrder.lift' (Fintype.equivFin (ι k)) (Fintype.equivFin (ι k)).injective
  let H : K → ℤ := fun _ => ((1 : ℕ) : ℤ)
  let c : Finset (Fin n) → ℤ := fun S => I V n (fun i => if i ∈ S then H else a i)
  have key : ∀ q : ℕ, 1 ≤ q → 0 ≤ ∑ S : Finset (Fin n), (q : ℤ) ^ Sᶜ.card * c S := by
    intro q hq
    have hamp := fun j => hKA F K ι I V n (a j) q 1 hI hV (hnef j) hq le_rfl
    choose p hp hgen _ using hamp
    let B : Fin n → K → ℤ := fun j => p j • (q • a j + H)
    have hB : 0 ≤ I V n B := hGP F K ι I V n B hI hV hgen
    have hposition : ∀ (L : Fin n → K → ℤ) (i : Fin n), I V n (Function.update L i (B i)) =
        ((q : ℤ) * p i) * I V n (Function.update L i (a i)) + (p i : ℤ) * I V n (Function.update L i H) := by
      intro L i
      have e : B i = ((q * p i : ℕ) : ℤ) • a i + ((p i : ℕ) : ℤ) • H := by
        funext k
        simp only [B, Pi.add_apply, Pi.smul_apply]
        simp only [H, nsmul_eq_mul, smul_eq_mul]
        push_cast
        ring
      rw [e, KleimanNefF.map_update_add₂ hI hV, KleimanNefF.nsmul_position hI hV, KleimanNefF.nsmul_position hI hV]
      push_cast
      ring
    have hexp := Kleiman.sum_expand_positions (I V n) B a (fun _ => H) (fun i => (q : ℤ) * p i)
      (fun i => (p i : ℤ)) hposition
    have hw : ∀ S : Finset (Fin n), (∏ i ∈ S, (p i : ℤ)) * (∏ i ∈ Sᶜ, ((q : ℤ) * p i)) =
        (∏ i, (p i : ℤ)) * (q : ℤ) ^ Sᶜ.card := by
      intro S
      rw [Finset.prod_mul_distrib, Finset.prod_const, ← mul_assoc, mul_comm _ ((q : ℤ) ^ _), mul_assoc,
        Finset.prod_mul_prod_compl, mul_comm]
    simp only [hw, mul_assoc] at hexp
    rw [← Finset.mul_sum] at hexp
    have hprod : 0 < ∏ i, (p i : ℤ) := Finset.prod_pos fun i _ => by exact_mod_cast hp i
    rw [hexp] at hB
    exact (mul_nonneg_iff_of_pos_left hprod).mp hB
  have h0 := Kleiman.nonneg_of_poly c key
  simpa [c] using h0

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

