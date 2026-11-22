import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0029
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Bundle0019
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Bundle0017
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.POneBlockPoints
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLineDegreeDual
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0029
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0033
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0045
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0044
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Bundle0005

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualLineIndex
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField Matrix

noncomputable section

namespace DualLineIndexAlt

theorem genIndex_span_eq_finprod {L : Type*} [Field L] [NumberField L] {ι : Type*} [Fintype ι] {y : ι → L}
    (hy : y ≠ 0) :
    genIndex (Submodule.span (𝓞 L) (Set.range y)).toAddSubgroup (1 : Submodule (𝓞 L) L).toAddSubgroup =
      ∏ᶠ w : FinitePlace L, ⨆ i, w (y i) := by
  obtain ⟨⟨b, hb⟩, hint⟩ :=
    IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 L)) y
  choose z hz using hint
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbL : (b : L) ≠ 0 := by rwa [Ne, RingOfIntegers.coe_eq_zero_iff]
  have hzy : ∀ i, ((z i : 𝓞 L) : L) = (b : L) * y i := fun i ↦ by
    have h := hz i
    simp only [Algebra.smul_def] at h
    exact h
  let g : 𝓞 L →ₗ[𝓞 L] L :=
    (LinearMap.mulLeft (𝓞 L) ((b : L)⁻¹)).comp (Algebra.linearMap (𝓞 L) L)
  have hg : ∀ t, g t = (b : L)⁻¹ * t := fun t ↦ rfl
  have hginj : Function.Injective g := fun s t h ↦ by
    rw [hg, hg] at h
    exact RingOfIntegers.ext (mul_left_cancel₀ (inv_ne_zero hbL) h)
  set J : Ideal (𝓞 L) := Ideal.span (Set.range z) with hJdef
  have hS : Submodule.span (𝓞 L) (Set.range y) = Submodule.map g J := by
    rw [hJdef]
    change _ = Submodule.map g (Submodule.span (𝓞 L) _)
    rw [Submodule.map_span, ← Set.range_comp]
    congr 2
    funext i
    rw [Function.comp_apply, hg, hzy]
    field_simp
  have h1 : (1 : Submodule (𝓞 L) L) = Submodule.map g (Ideal.span {b}) := by
    change _ = Submodule.map g (Submodule.span (𝓞 L) _)
    rw [Submodule.map_span, Set.image_singleton, hg, inv_mul_cancel₀ hbL,
      Submodule.one_eq_span]
  have hmap : ∀ A : Ideal (𝓞 L), (Submodule.map g A).toAddSubgroup = A.toAddSubgroup.map g.toAddMonoidHom :=
    fun _ ↦ rfl
  have hz0 : z ≠ 0 := by
    intro h
    apply hy
    funext i
    have := hzy i
    rw [h, Pi.zero_apply] at this
    exact (mul_eq_zero.mp (by rw [← this]; rfl)).resolve_left hbL
  have hJ0 : J ≠ ⊥ := by
    obtain ⟨i0, hi0⟩ := Function.ne_iff.mp hz0
    intro h
    exact hi0 ((Ideal.span_eq_bot.mp h) _ ⟨i0, rfl⟩)
  have hB0 : Ideal.span {b} ≠ ⊥ := by rw [Ne, Ideal.span_singleton_eq_bot]; exact hb0
  rw [hS, h1, hmap, hmap, genIndex, AddSubgroup.relIndex_map_map_of_injective _ _ hginj,
    AddSubgroup.relIndex_map_map_of_injective _ _ hginj, ← genIndex,
    IdealIndexPlaces.genIndex_ideal hJ0 hB0, Ideal.absNorm_span_singleton, Nat.cast_natAbs]

  have hprodz := absNorm_mul_finprod_finitePlace_eq_one hz0
  have hsup : ∀ w : FinitePlace L, ⨆ i, w (z i : L) = w (b : L) * ⨆ i, w (y i) := by
    intro w
    simp_rw [hzy, map_mul]
    exact (Real.mul_iSup_of_nonneg (apply_nonneg w _) _).symm
  simp_rw [hsup] at hprodz
  rw [finprod_mul_distrib (FinitePlace.hasFiniteMulSupport hbL) (hasFiniteMulSupport_iSup_place hy),
    FinitePlace.prod_eq_inv_abs_norm_int hb0] at hprodz
  rw [← hJdef] at hprodz
  set P := ∏ᶠ w : FinitePlace L, ⨆ i, w (y i)
  have hbn : |((Algebra.norm ℤ b : ℤ) : ℝ)| ≠ 0 := by
    rw [abs_ne_zero, Int.cast_ne_zero, Ne, Algebra.norm_eq_zero_iff]; exact hb0
  have hJn : (J.absNorm : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hJ0)
  have hinv := mul_inv_cancel₀ hbn
  push_cast
  rw [div_eq_iff hJn]
  linear_combination (-|((Algebra.norm ℤ b : ℤ) : ℝ)|) * hprodz + ((J.absNorm : ℝ) * P) * hinv

theorem dualPointCoord_ne_zero {K : Type} [Field K] [NumberField K] {i : ℕ} (F : HermLattice K i) {T : Type}
    (b : Module.Basis T ℤ (dualLattice F)) {K' : Type} [Field K'] [Algebra K K'] {v : Fin i → K'}
    (hv : v ≠ 0) : dualPointCoord b v ≠ 0 := by
  classical
  intro h0
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hv
  obtain ⟨D, hD, hmem⟩ := exists_int_smul_mem_latticeDual F.lattice F.fg (Pi.single j (1 : K))
  have hmem' : D • (Pi.single j (1 : K) : Fin i → K) ∈ dualLattice F := fun x hx ↦ by
    obtain ⟨c, hc⟩ := hmem x hx
    exact ⟨c, hc⟩
  let Λ : dualLattice F →ₗ[ℤ] K' :=
    { toFun := fun ψ ↦ ∑ k, algebraMap K K' ((ψ : Fin i → K) k) * v k
      map_add' := fun ψ χ ↦ by
        simp only [Submodule.coe_add, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
      map_smul' := fun c ψ ↦ by
        simp only [Submodule.coe_smul, Pi.smul_apply, zsmul_eq_mul, map_mul, map_intCast,
          RingHom.id_apply, Finset.mul_sum, mul_assoc] }
  have hΛ : Λ = 0 := b.ext fun t ↦ by
    have := congrFun h0 ⟨(), t⟩
    simpa [Λ, dualPointCoord] using this
  have := congrArg (fun f : dualLattice F →ₗ[ℤ] K' ↦ f ⟨_, hmem'⟩) hΛ
  simp only [Λ, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.zero_apply,
    zsmul_eq_mul, Pi.mul_apply, Pi.intCast_apply, Pi.single_apply, mul_ite, mul_one, mul_zero,
    apply_ite (algebraMap K K'), map_intCast, map_zero, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at this
  rcases mul_eq_zero.mp this with h | h
  · apply hD
    have h' : algebraMap K K' (D : K) = 0 := by rw [map_intCast]; exact h
    exact_mod_cast (map_eq_zero_iff _ (algebraMap K K').injective).mp h'
  · exact hj h

end DualLineIndexAlt

open DualLineIndexAlt in

theorem DualLineIndex.proof : DualLineIndex.Statement := by
  intro K _ _ i F T _ _ b K' _ _ _ v hv
  classical
  have hi : i ≠ 0 := by
    rintro rfl
    exact hv (Subsingleton.elim _ _)
  obtain ⟨r, rfl⟩ : ∃ r, i = r + 1 := ⟨i - 1, by omega⟩
  set y := dualPointCoord b v with hy
  have hy0 : y ≠ 0 := dualPointCoord_ne_zero F b hv
  have hT : Fintype.card T ≠ 0 := by
    obtain ⟨p, _⟩ := Function.ne_iff.mp hy0
    exact (Fintype.card_pos_iff.mpr ⟨p.2⟩).ne'
  obtain ⟨N, hN⟩ : ∃ N, Fintype.card T = N + 1 := ⟨Fintype.card T - 1, by omega⟩
  let e : T ≃ Fin (N + 1) := Fintype.equivFinOfCardEq hN
  let φ : Fin (N + 1) → Fin (r + 1) → K := fun k ↦ (b (e.symm k) : Fin (r + 1) → K)
  have hφ : IsDualBasis F.lattice φ :=
    { independent :=
        (b.linearIndependent.map' (dualLattice F).subtype (Submodule.ker_subtype _)).comp e.symm
          e.symm.injective
      span_eq := by
        have hr : Set.range φ = (dualLattice F).subtype '' Set.range b := by
          rw [← Set.range_comp]
          exact EquivLike.range_comp (fun t ↦ (b t : Fin (r + 1) → K)) e.symm
        rw [hr, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_subtype]
        ext ψ
        exact ⟨fun h x hx ↦ by obtain ⟨c, hc⟩ := h x hx; exact ⟨c, hc⟩,
          fun h x hx ↦ by obtain ⟨c, hc⟩ := h x hx; exact ⟨c, hc⟩⟩ }

  have hval : ∀ a : K', (∀ k, a * latticeValue φ v k ∈ Set.range (algebraMap (𝓞 K') K')) ↔
      a ∈ multiplierIdeal y := by
    intro a
    constructor
    · rintro h ⟨⟨⟩, t⟩
      have := h (e t)
      simpa [φ, latticeValue, hy, dualPointCoord] using this
    · intro h k
      exact h ⟨(), e.symm k⟩

  let f : K' →+ (Fin (r + 1) → K') :=
    { toFun := fun a ↦ a • v, map_zero' := zero_smul _ _, map_add' := fun a a' ↦ add_smul a a' v }
  have hf : Function.Injective f := smul_left_injective K' hv
  have e1 : (Submodule.span (𝓞 K')
        ((fun w : Fin (r + 1) → K ↦ fun j ↦ algebraMap K K' (w j)) '' F.lattice) ⊓
        (Submodule.span K' (Set.range fun _ : Fin 1 ↦ v)).restrictScalars (𝓞 K')).toAddSubgroup =
      (multiplierIdeal y).toAddSubgroup.map f := by
    ext x
    simp only [Submodule.mem_toAddSubgroup, Submodule.mem_inf, Submodule.restrictScalars_mem,
      Set.range_const, Submodule.mem_span_singleton, AddSubgroup.mem_map]
    constructor
    · rintro ⟨hxL, a, rfl⟩
      exact ⟨a, (hval a).mp ((LineIdealDual.proof K r N F φ hφ K' v a).mp hxL), rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨(LineIdealDual.proof K r N F φ hφ K' v a).mpr ((hval a).mpr ha), a, rfl⟩
  have e2 : (Submodule.span (𝓞 K') (Set.range fun _ : Fin 1 ↦ v)).toAddSubgroup =
      (1 : Submodule (𝓞 K') K').toAddSubgroup.map f := by
    ext x
    simp only [Submodule.mem_toAddSubgroup, Set.range_const, Submodule.mem_span_singleton,
      AddSubgroup.mem_map, Submodule.mem_one]
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨algebraMap (𝓞 K') K' c, ⟨c, rfl⟩, (algebraMap_smul K' c v)⟩
    · rintro ⟨a, ⟨c, rfl⟩, rfl⟩
      exact ⟨c, (algebraMap_smul K' c v).symm⟩
  rw [e1, e2, genIndex, AddSubgroup.relIndex_map_map_of_injective _ _ hf,
    AddSubgroup.relIndex_map_map_of_injective _ _ hf, ← genIndex, genIndex_span_eq_finprod hy0]
  exact IdealIndexPlaces.proof K' _ y hy0

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualPointLineDegree
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 MvPolynomial Matrix NumberField
open scoped ComplexOrder

noncomputable section

namespace DualPointLineDegreeAlt

theorem sum_log_norm {L : Type*} [Field L] [NumberField L] {x : L} (hx : x ≠ 0) :
    ∑ σ : L →+* ℂ, Real.log ‖σ x‖ = Real.log |(Algebra.norm ℚ x : ℝ)| := by
  classical
  rw [← Real.log_prod (fun σ _ => norm_ne_zero_iff.mpr ((map_ne_zero σ).mpr hx))]
  congr 1
  rw [Fintype.prod_equiv (RingHom.equivRatAlgHom L ℂ) _ (fun φ => ‖φ x‖)
    (fun _ => by simp [RingHom.equivRatAlgHom_apply]), ← norm_prod,
    ← Algebra.norm_eq_prod_embeddings ℚ ℂ x, eq_ratCast, ← Complex.ofReal_ratCast, Complex.norm_real,
    Real.norm_eq_abs]

theorem isMultiHomog_X {T : Type} [Fintype T] (t : T) :
    IsMultiHomog (X ⟨(), t⟩ : MRing (fun _ : Unit => T)) (fun _ => 1) := by
  classical
  intro m hm k
  obtain ⟨⟩ := k
  rw [support_X, Finset.mem_singleton] at hm
  subst hm
  rw [Finset.sum_eq_single t]
  · simp
  · intro c _ hc
    rw [Finsupp.single_apply, if_neg]
    intro h
    exact hc (sigma_mk_injective h).symm
  · simp

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {F : HermLattice K i} {T : Type} {K' : Type} [Field K'] [NumberField K'] [Algebra K K']

theorem dualNormSq_point (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (v : Fin i → K') (σ' : K' →+* ℂ) :
    dualNormSq b hb (fun t => σ' (dualPointCoord b v ⟨(), t⟩)) =
      (gramAt (F.metric (σ'.comp (algebraMap K K'))) σ' (fun _ : Fin 1 => v)).det.re := by
  classical
  set σ := σ'.comp (algebraMap K K') with hσ
  let w : (K →+* ℂ) × Fin i → ℂ := fun q => if q.1 = σ then σ' (v q.2) else 0
  have hw : dualRecover b hb (fun t => σ' (dualPointCoord b v ⟨(), t⟩)) = w := by
    rw [dualRecover, LinearEquiv.symm_apply_eq]
    funext t
    simp only [LinearEquiv.ofBijective_apply, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
      dualEmbMatrix, w, Fintype.sum_prod_type, mul_ite, mul_zero, dualPointCoord, map_sum, map_mul]
    rw [Finset.sum_eq_single σ (fun τ _ hτ => by simp [hτ]) (by simp)]
    simp [hσ]
  rw [dualNormSq, hw, Finset.sum_eq_single σ, Matrix.det_unique]
  · simp only [w, if_true, gramAt]
    rfl
  · intro τ _ hτ
    have h0 : (fun j => w (τ, j)) = 0 := by
      funext j
      simp [w, hτ]
    rw [h0]
    simp
  · simp

end DualPointLineDegreeAlt

open DualPointLineDegreeAlt in

theorem DualPointLineDegree.proof (hPt : DualCurvePoint.Statement) (hPos : PointDegCPos.Statement)
    (hAr : PointArInt.Statement) (hVert : PointVertR.Statement) (hIdx : DualLineIndex.Statement)
    (hSemi : DualLineSemipositive.Statement) : DualPointLineDegree.Statement := by
  intro K _ _ i F T _ _ b hb II hII W hW hbW
  obtain ⟨K', _, _, _, v, hv, rfl⟩ := hPt K i F T b W hW hbW
  set y := dualPointCoord b v with hy
  set A := dualLine F b hb with hA
  refine ⟨hPos T K' y hW, K', inferInstance, inferInstance, inferInstance, v, hv, ?_⟩
  obtain ⟨t₀, ht₀⟩ := hW.2.1.2.2 ()
  set s : MRing (dualBlocks T) := X ⟨(), t₀⟩ with hs
  have hs1 : IsMultiHomog s (fun _ => 1) := isMultiHomog_X t₀
  have hsec : IsSectionOn (mCoordIdeal y) A s := ⟨fun _ => 1, fun _ => rfl, hs1, ht₀⟩
  have hsm : IsSmoothHerm A := (hSemi K i F T b hb).1
  have hy0 : y ⟨(), t₀⟩ ≠ 0 := by
    intro h
    apply ht₀
    change mConeMap y (X ⟨(), t₀⟩) = 0
    simp [mConeMap, h]

  have hR := (hII Unit (dualBlocks T)).2.2 (mCoordIdeal y) 0 Fin.elim0 A s (fun _ => 1) hW
    (fun j => j.elim0) hsm (fun _ => rfl) hs1 ht₀
  have hsnoc : (Fin.snoc (Fin.elim0 : Fin 0 → HermLine (dualBlocks T)) A : Fin 1 → HermLine (dualBlocks T)) =
      ![A] := by
    funext j
    fin_cases j
    rfl
  rw [hsnoc, Inter.SpecIntHeightFormula.proof Inter.arithVarZero Unit (dualBlocks T) _ _ A s hW hsm hsec] at hR

  have hV := hVert T K' y s hW hs1 ht₀
  have hI := hAr T K' y A s hW hsec
  have hL := hIdx K i F T b K' v hv
  have hys : aeval y s = y ⟨(), t₀⟩ := by simp [hs]
  have hlog : ∀ σ' : K' →+* ℂ, logNorm A s (fun p => σ' (y p)) =
      Real.log ‖σ' (y ⟨(), t₀⟩)‖ -
        1 / 2 * Real.log (gramAt (F.metric (σ'.comp (algebraMap K K'))) σ' (fun _ : Fin 1 => v)).det.re := by
    intro σ'
    have hq : dualNormSq b hb (fun t => σ' (y ⟨(), t⟩)) =
        (gramAt (F.metric (σ'.comp (algebraMap K K'))) σ' (fun _ : Fin 1 => v)).det.re :=
      dualNormSq_point b hb v σ'
    have hpos : 0 < dualNormSq b hb (fun t => σ' (y ⟨(), t⟩)) := by
      have := A.pos (fun p => σ' (y p)) (fun _ => ⟨t₀, (map_ne_zero σ').mpr hy0⟩)
      simpa [hA, dualLine] using this
    have hne : ‖σ' (y ⟨(), t₀⟩)‖ ≠ 0 := norm_ne_zero_iff.mpr ((map_ne_zero σ').mpr hy0)
    simp only [logNorm, hs, map_X, eval_X, hA, dualLine]
    rw [Real.log_div hne (Real.sqrt_pos.mpr hpos).ne', Real.log_sqrt hpos.le, ← hq]
    ring
  rw [Finset.sum_congr rfl fun σ' _ => hlog σ', Finset.sum_sub_distrib,
    sum_log_norm hy0, ← Finset.mul_sum] at hI
  rw [hys] at hV
  have hn : (0 : ℝ) < Module.finrank ℚ K' := by exact_mod_cast Module.finrank_pos
  have hd : (0 : ℝ) < degC (mCoordIdeal y) := by exact_mod_cast hPos T K' y hW
  rw [← hy] at hL
  have hdeg : F.lineDegree K' v = (-Real.log (genIndex (Submodule.span (𝓞 K') (Set.range y)).toAddSubgroup
      (1 : Submodule (𝓞 K') K').toAddSubgroup) - 1 / 2 * ∑ σ' : K' →+* ℂ,
        Real.log (gramAt (F.metric (σ'.comp (algebraMap K K'))) σ' (fun _ : Fin 1 => v)).det.re) /
      Module.finrank ℚ K' := by
    unfold HermLattice.lineDegree subDegree normalise
    rw [eq_inv_of_mul_eq_one_left hL, Real.log_inv]
  have hR' : II Unit (dualBlocks T) (mCoordIdeal y) 1 ![A] =
      vertR (mCoordIdeal y) Fin.elim0 s - arInt (mCoordIdeal y) s A Fin.elim0 := hR
  have key : (vertR (mCoordIdeal y) Fin.elim0 s - arInt (mCoordIdeal y) s A Fin.elim0) *
      Module.finrank ℚ K' = degC (mCoordIdeal y) * (Real.log (genIndex
        (Submodule.span (𝓞 K') (Set.range y)).toAddSubgroup (1 : Submodule (𝓞 K') K').toAddSubgroup) +
        1 / 2 * ∑ σ' : K' →+* ℂ,
          Real.log (gramAt (F.metric (σ'.comp (algebraMap K K'))) σ' (fun _ : Fin 1 => v)).det.re) := by
    linear_combination hV - hI
  rw [hdeg, hR', neg_div, ← neg_div, div_eq_div_iff hn.ne' hd.ne']
  linear_combination key

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStackedExcLinear
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial NumberField

noncomputable section

namespace StackedExceptionalLinearForms

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {F F' : HermLattice K i} {T : Type} [Fintype T]
  {k : Type} [Field k] {b : Module.Basis T ℤ (dualLattice F)} {b' : Module.Basis T ℤ (dualLattice F')}
  {α : T → k} {M : T → Fin i → k}

theorem span_alpha (h : IsExcResidueData b b' α M) : Submodule.span ℤ (Set.range α) = ⊤ := by
  obtain ⟨-, ρ', -, -, hρ', -, -, -, -, hα, -⟩ := h
  refine eq_top_iff.mpr fun x _ => ?_
  obtain ⟨φ, rfl⟩ := hρ' x
  rw [← b'.sum_repr φ, map_sum]
  refine Submodule.sum_mem _ fun t _ => ?_
  rw [map_zsmul, ← hα t]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, rfl⟩)

theorem linFormsIndep (h : IsExcResidueData b b' α M) : LinFormsIndep M := by
  obtain ⟨-, -, σ, -, -, hσ, -, -, -, -, hM⟩ := h
  intro w hw
  funext j
  obtain ⟨φ, hφ⟩ := hσ (Pi.single j 1)
  have hcomb : ∀ j', σ φ j' = ∑ t, (b.repr φ t : k) * M t j' := by
    intro j'
    have hs : σ φ = ∑ t, b.repr φ t • M t := by
      conv_lhs => rw [← b.sum_repr φ]
      rw [map_sum]
      simp_rw [map_zsmul, hM]
    rw [hs, Finset.sum_apply]
    simp only [Pi.smul_apply, zsmul_eq_mul]
  have key : ∑ j', σ φ j' * w j' = 0 := by
    simp only [hcomb, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun t _ => ?_
    simp only [mul_assoc, ← Finset.mul_sum, hw t, mul_zero]
  rw [hφ] at key
  simpa [Pi.single_apply] using key

end StackedExceptionalLinearForms

open StackedExceptionalLinearForms in

theorem DualStackedExcLinear.proof (hEx : DualStackedExcResidueExists.Statement)
    (hBase : DualStackedExcBaseLe.Statement) (hLe : DualStackedExcLinPrimeLe.Statement) :
    DualStackedExcLinear.Statement := by
  intro K _ _ i F F' T _ _ b b' a hi hlt hcov hab E hE
  obtain ⟨k, hk, hkf, α, M, hD, hcard⟩ := hEx K i F F' T b b' a hi hlt hcov hab
  have h1 : stackedBase b' a ≤ linPrime α M := hBase K i F F' T b b' a hi hlt hcov hab k α M hD
  have h2 : linPrime α M ≤ E := hLe K i F F' T b b' a hi hlt hcov hab k α M hD E hE.1.1.1 hE.1.1.2 hE.2
  have hprime : (linPrime α M).IsPrime := RingHom.ker_isPrime _
  exact ⟨k, hk, hkf, α, M, span_alpha hD, linFormsIndep hD, le_antisymm (hE.1.2 ⟨hprime, h1⟩ h2) h2, hcard⟩

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStdFibreRatios
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.ChartRestriction.G.AI.I1 NumberField MvPolynomial

namespace StandardDualFibreRatios

theorem nonempty_of_basis {K : Type} [Field K] [NumberField K] {i : ℕ} {F : HermLattice K i} {T : Type} [Fintype T]
    (b : Module.Basis T ℤ (dualLattice F)) (hi : 1 ≤ i) : Nonempty T := by
  by_contra hT
  rw [not_nonempty_iff] at hT
  have h := DualArithmeticVariety.span_basis (K := K) b
  rw [Set.range_eq_empty, Submodule.span_empty] at h
  have h1 : (Pi.single (⟨0, hi⟩ : Fin i) 1 : Fin i → K) ∈ (⊥ : Submodule K (Fin i → K)) := h ▸ Submodule.mem_top
  rw [Submodule.mem_bot] at h1
  have h2 := congrFun h1 ⟨0, hi⟩
  simp at h2

end StandardDualFibreRatios

open StandardDualFibreRatios in

theorem DualStdFibreRatios.proof (hTr : GenFibreModelTransport.Statement) (hMod : DualStdGraphModel.Statement)
    (hRk : DualStdModelRank.Statement) (hTc : DualStdModelTransc.Statement) : DualStdFibreRatios.Statement := by
  intro K _ _ i T _ _ b G hi
  obtain ⟨c⟩ := nonempty_of_basis b hi
  let Φ₀ : Subfield (dualStdModelField K i) :=
    Subfield.closure (Set.range (dualStdModelPt b ∘ inrV (ι := dualBlocks T) (ι₂ := PBlk i)))
  have hΦ₀ : (algebraMap Φ₀ (dualStdModelField K i)).fieldRange = Φ₀ := Subfield.fieldRange_subtype _
  obtain ⟨h0, hrk, htr⟩ := hTr Unit (PBlk i) (Unit ⊕ Unit) (Sum.elim (dualBlocks T) (PBlk i))
    (inrV (ι := dualBlocks T) (ι₂ := PBlk i))
    (graphIdeal (dualIdeal b) (linForm (ι₂ := PBlk i) (dualStdCoordMat b))) G (dualStdModelField K i)
    (dualStdModelPt b) (hMod K i T b) Φ₀ hΦ₀ T
    (fun t => (⟨Sum.inl (), t⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k))
    (⟨Sum.inl (), c⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k)
  obtain ⟨hz, hrk₀⟩ := hRk K i T b Φ₀ hΦ₀ hi c
  refine ⟨c, fun h => hz (h0.mp h), ?_, ?_⟩
  · exact hrk.trans hrk₀
  · exact htr.mpr (hTc K i T b Φ₀ hΦ₀ hi c)

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PPointDegCPos
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 NumberField

noncomputable section

namespace PointDegreeComplexPositive

theorem card_algHom_pos {K' : Type} [Field K'] [NumberField K'] (E : IntermediateField ℚ K') :
    0 < Nat.card (E →ₐ[ℚ] ℂ) := by
  have : FiniteDimensional ℚ E := inferInstance
  have : Algebra.IsAlgebraic ℚ E := Algebra.IsAlgebraic.of_finite ℚ E
  have : Nonempty (E →ₐ[ℚ] ℂ) := ⟨IsAlgClosed.lift⟩
  exact Nat.card_pos

end PointDegreeComplexPositive

theorem PointDegCPos.proof : PointDegCPos.Statement := by
  intro T _ K' _ _ y hP
  rw [IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree.full Unit (fun _ => T) K' y hP]
  exact PointDegreeComplexPositive.card_algHom_pos _

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualCotangentKer
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

noncomputable section

def DualCotangentKer.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F : HermLattice K i) (T : Type) [Fintype T]
    (_b : Module.Basis T ℤ (dualLattice F)) (k : Type) [Field k] (ρ : 𝓞 K →+* k)
    (σ : dualLattice F →+ (Fin i → k)),
    Function.Surjective ρ → Function.Surjective σ →
    (∀ (μ : 𝓞 K) (φ ψ : dualLattice F),
      (ψ : Fin i → K) = algebraMap (𝓞 K) K μ • (φ : Fin i → K) → σ ψ = ρ μ • σ φ) →
    ∀ ψ : dualLattice F, σ ψ = 0 →
      ψ ∈ Submodule.span ℤ {v : dualLattice F | ∃ (μ : 𝓞 K) (φ : dualLattice F), ρ μ = 0 ∧
        (v : Fin i → K) = algebraMap (𝓞 K) K μ • (φ : Fin i → K)}

end

end GroundTheory.Heights₂.Heights
end

