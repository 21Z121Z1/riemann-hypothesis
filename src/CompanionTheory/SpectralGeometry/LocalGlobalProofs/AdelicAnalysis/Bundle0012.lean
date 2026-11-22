import Mathlib
import Formalism.UnipotentAdelicQuotients.SWXSDefs
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0006
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0007
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.WeilOrthogonalGroupInvariance

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.MatrixTransvectionDiagonalDecomposition
section
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.SW.ArtinElem

variable {K K' : Type*} [CommRing K] [CommRing K'] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {M : Type*} [DecidableEq M] {F : M → Type*} [∀ m, CommRing (F m)]

noncomputable def coord (e : K ≃+* ∀ m, F m) (m : M) : K →+* F m :=
  (Pi.evalRingHom F m).comp e.toRingHom

noncomputable def liftT (e : K ≃+* ∀ m, F m) (m : M) (t : TransvectionStruct ι (F m)) :
    TransvectionStruct ι K :=
  ⟨t.i, t.j, t.hij, e.symm (Pi.single m t.c)⟩

lemma coord_symm_single (e : K ≃+* ∀ m, F m) (m m' : M) (c : F m) :
    coord e m' (e.symm (Pi.single m c)) = (Pi.single m c : ∀ m, F m) m' := by
  simp [coord]

lemma mapMatrix_single (f : K →+* K') (a b : ι) (c : K) :
    f.mapMatrix (single a b c) = single a b (f c) := by
  ext x y
  simp only [RingHom.mapMatrix_apply, map_apply, single_apply]
  split_ifs <;> simp

lemma liftT_toMatrix (e : K ≃+* ∀ m, F m) (m : M) (t : TransvectionStruct ι (F m)) :
    (liftT e m t).toMatrix = 1 + single t.i t.j (e.symm (Pi.single m t.c)) := rfl

lemma mapMatrix_liftT_same (e : K ≃+* ∀ m, F m) (m : M) (t : TransvectionStruct ι (F m)) :
    (coord e m).mapMatrix (liftT e m t).toMatrix = t.toMatrix := by
  rw [liftT_toMatrix, map_add, map_one, mapMatrix_single, coord_symm_single, Pi.single_eq_same]
  rfl

lemma mapMatrix_liftT_ne (e : K ≃+* ∀ m, F m) {m m' : M} (h : m' ≠ m)
    (t : TransvectionStruct ι (F m)) :
    (coord e m').mapMatrix (liftT e m t).toMatrix = 1 := by
  rw [liftT_toMatrix, map_add, map_one, mapMatrix_single, coord_symm_single,
    Pi.single_eq_of_ne h, single_zero, add_zero]

lemma mapMatrix_prod_same (e : K ≃+* ∀ m, F m) (m : M) (T : List (TransvectionStruct ι (F m))) :
    (coord e m).mapMatrix (((T.map (liftT e m)).map TransvectionStruct.toMatrix).prod) =
      (T.map TransvectionStruct.toMatrix).prod := by
  induction T with
  | nil => simp
  | cons t T ih => simp only [List.map_cons, List.prod_cons, map_mul, ih, mapMatrix_liftT_same]

lemma mapMatrix_prod_ne (e : K ≃+* ∀ m, F m) {m m' : M} (h : m' ≠ m)
    (T : List (TransvectionStruct ι (F m))) :
    (coord e m').mapMatrix (((T.map (liftT e m)).map TransvectionStruct.toMatrix).prod) = 1 := by
  induction T with
  | nil => simp
  | cons t T ih =>
    simp only [List.map_cons, List.prod_cons, map_mul, ih, mapMatrix_liftT_ne e h, mul_one]

noncomputable def big (e : K ≃+* ∀ m, F m) (T : ∀ m, List (TransvectionStruct ι (F m))) (l : List M) :
    List (TransvectionStruct ι K) :=
  l.flatMap fun m => (T m).map (liftT e m)

lemma mapMatrix_big (e : K ≃+* ∀ m, F m) (T : ∀ m, List (TransvectionStruct ι (F m)))
    (m' : M) (l : List M) (hl : l.Nodup) :
    (coord e m').mapMatrix (((big e T l).map TransvectionStruct.toMatrix).prod) =
      if m' ∈ l then ((T m').map TransvectionStruct.toMatrix).prod else 1 := by
  induction l with
  | nil => simp [big]
  | cons m l ih =>
    have ih' := ih (List.nodup_cons.mp hl).2
    have hm : m ∉ l := (List.nodup_cons.mp hl).1
    have hb : big e T (m :: l) = (T m).map (liftT e m) ++ big e T l := by simp [big]
    rw [hb, List.map_append, List.prod_append, map_mul, ih']
    by_cases h : m' = m
    · subst h
      rw [mapMatrix_prod_same]
      simp [hm]
    · rw [mapMatrix_prod_ne e h, one_mul]
      simp [h]

lemma matrix_ext_coord (e : K ≃+* ∀ m, F m) {A B : Matrix ι ι K}
    (h : ∀ m, (coord e m).mapMatrix A = (coord e m).mapMatrix B) : A = B := by
  ext a b
  apply e.injective
  funext m
  have := congrFun (congrFun (h m) a) b
  simpa [coord] using this

theorem factor_of_pi [Fintype M] (e : K ≃+* ∀ m, F m)
    (hF : ∀ (m : M) (A : Matrix ι ι (F m)),
      ∃ (L L' : List (TransvectionStruct ι (F m))) (D : ι → F m),
        A = (L.map TransvectionStruct.toMatrix).prod * diagonal D *
          (L'.map TransvectionStruct.toMatrix).prod)
    (A : Matrix ι ι K) :
    ∃ (L L' : List (TransvectionStruct ι K)) (D : ι → K),
      A = (L.map TransvectionStruct.toMatrix).prod * diagonal D *
        (L'.map TransvectionStruct.toMatrix).prod := by
  choose L L' D hD using fun m => hF m ((coord e m).mapMatrix A)
  refine ⟨big e L Finset.univ.toList, big e L' Finset.univ.toList,
    fun i => e.symm (fun m => D m i), matrix_ext_coord e fun m => ?_⟩
  have hnd := Finset.nodup_toList (Finset.univ : Finset M)
  have hdiag : (coord e m).mapMatrix (diagonal fun i => e.symm (fun m => D m i)) =
      diagonal (D m) := by
    ext a b
    by_cases hab : a = b
    · subst hab; simp [coord]
    · simp [hab]
  rw [map_mul, map_mul, mapMatrix_big e L m _ hnd, mapMatrix_big e L' m _ hnd, hdiag]
  simpa using hD m

end GlobalTheory.CompanionTheory.SW.ArtinElem

namespace GlobalTheory.CompanionTheory.SW

theorem artinian_reduced_list_transvec_mul_diagonal_mul_list_transvec
    (K : Type) [CommRing K] [IsArtinianRing K] [IsReduced K] (ι : Type) [Fintype ι]
    [DecidableEq ι] (A : Matrix ι ι K) :
    ∃ (L L' : List (Matrix.TransvectionStruct ι K)) (D : ι → K),
      A = (L.map Matrix.TransvectionStruct.toMatrix).prod * Matrix.diagonal D *
        (L'.map Matrix.TransvectionStruct.toMatrix).prod := by
  classical
  letI : Fintype (MaximalSpectrum K) := Fintype.ofFinite _
  refine ArtinElem.factor_of_pi (F := fun m : MaximalSpectrum K => K ⧸ m.asIdeal)
    (IsArtinianRing.equivPi K).toRingEquiv (fun m B => ?_) A
  letI : Field (K ⧸ m.asIdeal) := Ideal.Quotient.field m.asIdeal
  exact Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec B

end GlobalTheory.CompanionTheory.SW
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.MeasureEqHaarProdOfLeftInvariant
section
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.SW.InvariantProduct

theorem exists_const_rect {Q Z : Type} [Group Q] [TopologicalSpace Q] [LocallyCompactSpace Q]
    [SecondCountableTopology Q] [T2Space Q] [MeasurableSpace Q] [BorelSpace Q]
    [IsTopologicalGroup Q] [TopologicalSpace Z] [T2Space Z]
    [MeasurableSpace Z] [BorelSpace Z] (η : Measure Q) [η.IsHaarMeasure]
    (ρ : Measure (Q × Z)) [IsLocallyFiniteMeasure ρ]
    (hinv : ∀ q : Q, ρ.map (fun p => (q * p.1, p.2)) = ρ)
    {A C : Set Z} (hA : MeasurableSet A) (hC : IsCompact C) (hAC : A ⊆ C) :
    ∃ c : ℝ≥0, ∀ U : Set Q, MeasurableSet U → ρ (U ×ˢ A) = c * η U := by
  let μ : Measure Q := (ρ.restrict (Set.univ ×ˢ A)).map Prod.fst
  have hμ : ∀ U : Set Q, MeasurableSet U → μ U = ρ (U ×ˢ A) := by
    intro U hU
    rw [Measure.map_apply measurable_fst hU, Measure.restrict_apply (measurable_fst hU)]
    congr 1
    ext ⟨x, z⟩
    simp
  haveI : μ.IsMulLeftInvariant := ⟨fun q => by
    ext U hU
    have hT : Measurable (fun p : Q × Z => (q * p.1, p.2)) :=
      (measurable_fst.const_mul q).prodMk measurable_snd
    rw [Measure.map_apply (measurable_const_mul q) hU, hμ _ (measurable_const_mul q hU), hμ U hU]
    conv_rhs => rw [← hinv q]
    rw [Measure.map_apply hT (hU.prod hA)]
    rfl⟩
  haveI : IsFiniteMeasureOnCompacts μ := ⟨fun L hL => by
    rw [hμ L hL.isClosed.measurableSet]
    exact (measure_mono (Set.prod_mono subset_rfl hAC)).trans_lt (hL.prod hC).measure_lt_top⟩
  refine ⟨Measure.haarScalarFactor μ η, fun U hU => ?_⟩
  have h := congrArg (fun ν : Measure Q => ν U) (Measure.isMulLeftInvariant_eq_smul μ η)
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h
  rw [← hμ U hU]
  exact h

end GlobalTheory.CompanionTheory.SW.InvariantProduct

namespace GlobalTheory.CompanionTheory.SW

theorem measure_eq_haar_prod_of_left_invariant :
    ∀ (Q Z : Type) [Group Q] [TopologicalSpace Q] [LocallyCompactSpace Q]
      [SecondCountableTopology Q] [T2Space Q] [MeasurableSpace Q] [BorelSpace Q]
      [IsTopologicalGroup Q] [TopologicalSpace Z] [LocallyCompactSpace Z]
      [SecondCountableTopology Z] [T2Space Z] [MeasurableSpace Z] [BorelSpace Z]
      (η : Measure Q) [η.IsHaarMeasure] (ρ : Measure (Q × Z)) [IsLocallyFiniteMeasure ρ],
      (∀ q : Q, ρ.map (fun p => (q * p.1, p.2)) = ρ) →
        ∃ m : Measure Z, IsLocallyFiniteMeasure m ∧ ρ = η.prod m := by
  intro Q Z _ _ _ _ _ _ _ _ _ _ _ _ _ _ η _ ρ _ hinv
  obtain ⟨K, hKc, hK1⟩ := exists_compact_mem_nhds (1 : Q)
  have hKpos : η K ≠ 0 := (lt_of_lt_of_le (isOpen_interior.measure_pos η ⟨1, mem_interior_iff_mem_nhds.2 hK1⟩)
    (measure_mono interior_subset)).ne'
  have hKfin : η K ≠ ∞ := hKc.measure_lt_top.ne
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  let m : Measure Z := (η K)⁻¹ • (ρ.restrict (K ×ˢ Set.univ)).map Prod.snd
  have hm : ∀ A : Set Z, MeasurableSet A → m A = (η K)⁻¹ * ρ (K ×ˢ A) := by
    intro A hA
    have hset : Prod.snd ⁻¹' A ∩ (K ×ˢ (Set.univ : Set Z)) = K ×ˢ A := by
      ext ⟨x, z⟩
      simp [and_comm]
    simp only [m, Measure.smul_apply, smul_eq_mul]
    rw [Measure.map_apply measurable_snd hA, Measure.restrict_apply (measurable_snd hA), hset]
  have hrect : ∀ (U : Set Q) (A C : Set Z), MeasurableSet U → MeasurableSet A → IsCompact C →
      A ⊆ C → ρ (U ×ˢ A) = η U * m A := by
    intro U A C hU hA hC hAC
    obtain ⟨c, hc⟩ := InvariantProduct.exists_const_rect η ρ hinv hA hC hAC
    rw [hc U hU, hm A hA, hc K hKm, ← mul_assoc (η K)⁻¹, mul_comm (η K)⁻¹,
      mul_assoc (c : ℝ≥0∞), ENNReal.inv_mul_cancel hKpos hKfin, mul_one, mul_comm]
  have hmC : ∀ C : Set Z, IsCompact C → m C < ∞ := by
    intro C hC
    rw [hm C hC.isClosed.measurableSet]
    exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 (pos_iff_ne_zero.2 hKpos))
      (hKc.prod hC).measure_lt_top
  haveI hmfc : IsFiniteMeasureOnCompacts m := ⟨fun C hC => hmC C hC⟩
  refine ⟨m, inferInstance, ?_⟩
  symm
  let CQ : Set (Set Q) := {U | MeasurableSet U ∧ ∃ L, IsCompact L ∧ U ⊆ L}
  let CZ : Set (Set Z) := {A | MeasurableSet A ∧ ∃ L, IsCompact L ∧ A ⊆ L}
  have genAux : ∀ (X : Type) [TopologicalSpace X] [SigmaCompactSpace X] [T2Space X]
      [MeasurableSpace X] [BorelSpace X],
      MeasurableSpace.generateFrom {U : Set X | MeasurableSet U ∧ ∃ L, IsCompact L ∧ U ⊆ L} =
        ‹MeasurableSpace X› := by
    intro X _ _ _ M _
    apply le_antisymm
    · exact MeasurableSpace.generateFrom_le fun U hU => hU.1
    · intro B hB
      have : B = ⋃ n, B ∩ compactCovering X n := by
        rw [← Set.inter_iUnion, iUnion_compactCovering, Set.inter_univ]
      rw [this]
      exact MeasurableSet.iUnion fun n => MeasurableSpace.measurableSet_generateFrom
        ⟨hB.inter (isCompact_compactCovering X n).isClosed.measurableSet,
          _, isCompact_compactCovering X n, Set.inter_subset_right⟩
  have piAux : ∀ (X : Type) [TopologicalSpace X] [MeasurableSpace X],
      IsPiSystem {U : Set X | MeasurableSet U ∧ ∃ L, IsCompact L ∧ U ⊆ L} := by
    intro X _ _ U hU V hV _
    obtain ⟨hUm, L, hL, hUL⟩ := hU
    exact ⟨hUm.inter hV.1, L, hL, Set.inter_subset_left.trans hUL⟩
  have spanAux : ∀ (X : Type) [TopologicalSpace X] [SigmaCompactSpace X] [T2Space X]
      [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ],
      μ.FiniteSpanningSetsIn {U : Set X | MeasurableSet U ∧ ∃ L, IsCompact L ∧ U ⊆ L} := by
    intro X _ _ _ _ _ μ _
    exact ⟨compactCovering X,
      fun n => ⟨(isCompact_compactCovering X n).isClosed.measurableSet, _,
        isCompact_compactCovering X n, subset_rfl⟩,
      fun n => (isCompact_compactCovering X n).measure_lt_top,
      iUnion_compactCovering X⟩
  refine Measure.prod_eq_generateFrom (genAux Q) (genAux Z) (piAux Q) (piAux Z)
    (spanAux Q η) (spanAux Z m) ?_
  rintro U ⟨hU, -⟩ A ⟨hA, L, hL, hAL⟩
  exact (hrect U A L hU hA hL hAL)

end GlobalTheory.CompanionTheory.SW
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.QuadraticSetupInvariantUnderIsometry
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker

namespace GlobalTheory.CompanionTheory.SW.ThW

theorem qsetup_conj_majorant (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι]
    (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ)
    (gi : InfinitePlace F → Matrix ι ι ℝ) (h : QSetup M B ρ P)
    (hg : ∀ w, (gi w)ᵀ * B.map (ρ w) * gi w = B.map (ρ w)) :
    QSetup M B ρ (fun w => (gi w)ᵀ * P w * gi w) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  have hb : ∀ w, (B.map (ρ w)).det ≠ 0 := by
    intro w
    have e : (B.map (ρ w)).det = ρ w B.det := ((ρ w).map_det B).symm
    rw [e]
    exact (map_ne_zero _).2 h4
  have hd : ∀ w, (gi w).det ≠ 0 := by
    intro w h0
    have e := congrArg Matrix.det (hg w)
    rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at e
    exact hb w e.symm
  refine ⟨h1, h2, h3, h4, h5, ?_, ?_⟩
  · intro w
    have hinj : Function.Injective (gi w).mulVec :=
      Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (hd w)))
    have := (h6 w).conjTranspose_mul_mul_same hinj
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using this
  · intro w
    set g := gi w with hgdef
    set b := B.map (ρ w) with hbdef
    have hbu : IsUnit b.det := isUnit_iff_ne_zero.2 (hb w)
    have hgw : gᵀ * b * g = b := hg w
    have e1 : (b⁻¹ * gᵀ * b) * g = 1 := by
      rw [Matrix.mul_assoc b⁻¹ gᵀ b, Matrix.mul_assoc b⁻¹, hgw,
        Matrix.nonsing_inv_mul _ hbu]
    have e2 : g * (b⁻¹ * gᵀ * b) = 1 := mul_eq_one_comm.1 e1
    have e3 : (g * b⁻¹ * gᵀ) * b = 1 := by
      rw [← e2]; simp only [Matrix.mul_assoc]
    have e4 : g * b⁻¹ * gᵀ = b⁻¹ := (Matrix.inv_eq_left_inv e3).symm
    calc gᵀ * P w * g * b⁻¹ * (gᵀ * P w * g)
        = gᵀ * P w * (g * b⁻¹ * gᵀ) * P w * g := by simp only [Matrix.mul_assoc]
      _ = gᵀ * (P w * b⁻¹ * P w) * g := by rw [e4]; simp only [Matrix.mul_assoc]
      _ = b := by rw [h7 w, hgw]

end GlobalTheory.CompanionTheory.SW.ThW
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelMatrixSymmetricPosdefImag
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.ThW

theorem dotProduct_blockDiagonal_mulVec {R ι W : Type} [CommSemiring R] [Fintype ι] [DecidableEq ι]
    [Fintype W] [DecidableEq W] (f : W → Matrix ι ι R) (y : ι × W → R) :
    y ⬝ᵥ (blockDiagonal f *ᵥ y) = ∑ w, (fun i => y (i, w)) ⬝ᵥ (f w *ᵥ fun i => y (i, w)) := by
  simp only [dotProduct, mulVec]
  rw [Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun i _ => ?_
  congr 1
  rw [Fintype.sum_prod_type_right, Finset.sum_eq_single w]
  · simp [blockDiagonal_apply]
  · intro v _ hv
    refine Finset.sum_eq_zero fun j _ => ?_
    simp [blockDiagonal_apply, hv.symm]
  · simp

theorem dotProduct_block_ofReal {ι : Type} [Fintype ι] (a b : ℝ) (C P : Matrix ι ι ℝ)
    (y : ι → ℝ) :
    (fun i => (y i : ℂ)) ⬝ᵥ
        ((Matrix.of fun i j => (a : ℂ) * ((C i j : ℝ) : ℂ) +
          Complex.I * (b : ℂ) * ((P i j : ℝ) : ℂ)) *ᵥ fun i => (y i : ℂ)) =
      (a : ℂ) * ((y ⬝ᵥ (C *ᵥ y) : ℝ) : ℂ) + Complex.I * (b : ℂ) * ((y ⬝ᵥ (P *ᵥ y) : ℝ) : ℂ) := by
  simp only [dotProduct, mulVec, Matrix.of_apply, Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

def ZB {F : Type} [Field F] {ι : Type} {W : Type} (B : Matrix ι ι F) (ρ : W → (F →+* ℝ))
    (P : W → Matrix ι ι ℝ) (τ : W → ℂ) (w : W) : Matrix ι ι ℂ :=
  Matrix.of fun i j =>
    ((τ w).re : ℂ) * ((ρ w (B i j) : ℝ) : ℂ) + Complex.I * ((τ w).im : ℂ) * ((P w i j : ℝ) : ℂ)

theorem ZM_eq_blockDiagonal {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι]
    [DecidableEq ι] [DecidableEq (InfinitePlace F)] (B : Matrix ι ι F)
    (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ)
    (τ : InfinitePlace F → ℂ) : ZM B ρ P τ = blockDiagonal (ZB B ρ P τ) := rfl

theorem ZM_map_im {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι]
    [DecidableEq (InfinitePlace F)] (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ))
    (P : InfinitePlace F → Matrix ι ι ℝ) (τ : InfinitePlace F → ℂ) :
    (ZM B ρ P τ).map Complex.im = blockDiagonal fun w => (τ w).im • P w := by
  rw [ZM_eq_blockDiagonal]
  ext ⟨i, v⟩ ⟨j, u⟩
  by_cases h : v = u
  · subst h
    simp [ZB, blockDiagonal_apply]
  · simp [ZB, blockDiagonal_apply, h]

theorem ZM_symm_posDef_gauss (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι]
    [DecidableEq ι] [DecidableEq (InfinitePlace F)] (M : ℕ) (B : Matrix ι ι F)
    (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ) :
    QSetup M B ρ P → ∀ τ : InfinitePlace F → ℂ, (∀ w, 0 < (τ w).im) →
      (ZM B ρ P τ).IsSymm ∧ ((ZM B ρ P τ).map Complex.im).PosDef ∧
        ∀ x : ι × InfinitePlace F → ℝ,
          Complex.exp ((Real.pi : ℂ) * Complex.I *
            ((fun i => (x i : ℂ)) ⬝ᵥ (ZM B ρ P τ *ᵥ fun i => (x i : ℂ)))) =
              gauss B ρ P τ (cur x) := by
  rintro ⟨-, -, hB, -, -, hP, -⟩ τ hτ
  have hPs : ∀ w i j, P w j i = P w i j := fun w i j => by
    simpa using (hP w).isHermitian.apply i j
  refine ⟨?_, ?_, fun x => ?_⟩
  · rw [Matrix.IsSymm, ZM_eq_blockDiagonal, blockDiagonal_transpose]
    congr 1
    funext w
    ext i j
    simp only [transpose_apply, ZB, Matrix.of_apply]
    rw [hB.apply i j, hPs w i j]
  · rw [ZM_map_im]
    have hq : ∀ w (y : ι → ℝ), y ≠ 0 → 0 < y ⬝ᵥ (P w *ᵥ y) := fun w y hy => by
      simpa using (hP w).dotProduct_mulVec_pos hy
    refine posDef_iff_dotProduct_mulVec.2 ⟨?_, fun x hx => ?_⟩
    · ext ⟨i, v⟩ ⟨j, u⟩
      by_cases h : v = u
      · subst h
        simp [blockDiagonal_apply, hPs v i j]
      · have h' : ¬ u = v := fun e => h e.symm
        simp [blockDiagonal_apply, h, h']
    · obtain ⟨⟨i, w⟩, hiw⟩ := Function.ne_iff.1 hx
      have hstar : star x = x := by
        funext p
        simp
      rw [hstar, dotProduct_blockDiagonal_mulVec]
      have hterm : ∀ v, (fun i => x (i, v)) ⬝ᵥ (((τ v).im • P v) *ᵥ fun i => x (i, v)) =
          (τ v).im * ((fun i => x (i, v)) ⬝ᵥ (P v *ᵥ fun i => x (i, v))) := fun v => by
        simp [smul_mulVec, dotProduct_smul]
      simp only [hterm]
      refine Finset.sum_pos' (fun v _ => ?_) ⟨w, Finset.mem_univ w, ?_⟩
      · by_cases hy : (fun i => x (i, v)) = 0
        · simp [hy]
        · exact (mul_pos (hτ v) (hq v _ hy)).le
      · refine mul_pos (hτ w) (hq w _ fun h0 => hiw ?_)
        simpa using congrFun h0 i
  · unfold gauss
    congr 1
    rw [ZM_eq_blockDiagonal, dotProduct_blockDiagonal_mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    have h := dotProduct_block_ofReal (τ w).re (τ w).im (B.map (ρ w)) (P w) (cur x w)
    simp only [Matrix.map_apply] at h
    have h2 : (fun i => ((x (i, w) : ℝ) : ℂ)) = fun i => ((cur x w i : ℝ) : ℂ) := rfl
    have h3 : ZB B ρ P τ w = Matrix.of fun i j => ((τ w).re : ℂ) * ((ρ w (B i j) : ℝ) : ℂ) +
        Complex.I * ((τ w).im : ℂ) * ((P w i j : ℝ) : ℂ) := rfl
    rw [h2, h3, h]
    linear_combination ((Real.pi : ℂ) * ((τ w).im : ℂ) * ((cur x w ⬝ᵥ (P w *ᵥ cur x w) : ℝ) : ℂ)) *
      Complex.I_mul_I

end GlobalTheory.CompanionTheory.SW.ThW
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TotallyRealIntegralBasisExists
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker

namespace GlobalTheory.CompanionTheory.SW.ThW

theorem exists_integralBasis_infinitePlace (F : Type) [Field F] [NumberField F]
    (hF : IsTotallyReal F) : Nonempty (Module.Basis (InfinitePlace F) ℤ (𝓞 F)) := by
  have hcard : Fintype.card (InfinitePlace F) = Module.finrank ℚ F := by
    have h1 := InfinitePlace.card_add_two_mul_card_eq_rank F
    have h3 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := F)
    have h2 : InfinitePlace.nrComplexPlaces F = 0 := IsTotallyReal.nrComplexPlaces_eq_zero F
    omega
  have e : Module.Free.ChooseBasisIndex ℤ (𝓞 F) ≃ InfinitePlace F :=
    Fintype.equivOfCardEq (by
      rw [hcard, ← Module.finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank])
  exact ⟨(RingOfIntegers.basis F).reindex e⟩

end GlobalTheory.CompanionTheory.SW.ThW
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitBalancingImaginaryPartsStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unit_balancing_imaginary_parts : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ ρ : InfinitePlace F → (F →+* ℝ), (∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) → ∃ κ : ℝ, 0 < κ ∧ ∀ y : InfinitePlace F → ℝ, (∀ w, 0 < y w) → ∃ u : (𝓞 F)ˣ, ∀ v w, κ * (ρ w ((u : 𝓞 F) : F) ^ 2 * y w) ≤ ρ v ((u : 𝓞 F) : F) ^ 2 * y v := by
  first | exact @GlobalTheory.CompanionTheory.SW.UnitBalance.balance_by_units | exact GlobalTheory.CompanionTheory.SW.UnitBalance.balance_by_units | (intros; apply GlobalTheory.CompanionTheory.SW.UnitBalance.balance_by_units <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.WeilOrthogonalGroupInvarianceStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_orthogonal_group_invariance : ∀ (R : Type) [CommRing R] [TopologicalSpace R] [MeasurableSpace R] (ι : Type) [Fintype ι] [DecidableEq ι] (ψ : AddChar R ℂ) (h : R) (B : Matrix ι ι R) (μ : Measure (ι → R)), NAQuad ψ h B μ → ∀ g : Matrix ι ι R, IsUnit g.det → gᵀ * B * g = B → Measure.map (fun x => g *ᵥ x) μ = μ ∧ ∀ φ : (ι → R) → ℂ, SB φ → SB (fun x => φ (g *ᵥ x)) ∧ ∀ y, fou (chiB ψ B) μ (fun x => φ (g *ᵥ x)) y = fou (chiB ψ B) μ φ (g *ᵥ y) := by
  first | exact @GlobalTheory.CompanionTheory.SW.Core.OrthMeas.orth_meas | exact GlobalTheory.CompanionTheory.SW.Core.OrthMeas.orth_meas | (intros; apply GlobalTheory.CompanionTheory.SW.Core.OrthMeas.orth_meas <;> assumption)
end

