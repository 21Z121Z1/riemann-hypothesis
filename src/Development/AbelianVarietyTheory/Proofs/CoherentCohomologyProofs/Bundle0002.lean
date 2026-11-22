import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsIsRegularQuotSMulTop
section
universe u_1 u_2

open CategoryTheory Abelian Limits RingTheory.Sequence Pointwise

namespace GlobalTheory.RegularElementQuotient

theorem maximalIdeal_smul_top_lt_top {R : Type u_1} [CommRing R] [IsLocalRing R]
    (M : Type u_2) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M] :
    IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) < ⊤ := by
  rw [lt_top_iff_ne_top]
  intro h

  have hbot : (⊤ : Submodule R M) = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal R) ⊤
      Module.Finite.fg_top h.ge (IsLocalRing.maximalIdeal_le_jacobson ⊥)
  exact top_ne_bot hbot

theorem exists_isRegular_quotSMulTop {R : Type u_1} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] [Small.{u_2, u_1} R] {M : Type u_2} [AddCommGroup M] [Module R M]
    [Module.Finite R M] {xs : List R} (hxs : IsRegular M xs) {n : ℕ}
    (hn : n + 1 ≤ xs.length) {y : R} (hy : y ∈ IsLocalRing.maximalIdeal R)
    (hreg : IsSMulRegular M y) :
    ∃ zs : List R, zs.length = n ∧ IsRegular (QuotSMulTop y M) zs := by
  set 𝔪 := IsLocalRing.maximalIdeal R

  have : Nontrivial M :=
    (Submodule.nontrivial_iff R).mp (nontrivial_of_ne _ _ hxs.top_ne_smul)

  have hmem : ∀ x ∈ xs, x ∈ 𝔪 := by
    intro x hx
    by_contra hx𝔪
    have hu : IsUnit x := by
      by_contra hnu
      exact hx𝔪 ((IsLocalRing.mem_maximalIdeal x).mpr hnu)
    have htop : Ideal.ofList xs = ⊤ :=
      Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span hx) hu
    apply hxs.top_ne_smul
    rw [htop, Submodule.top_smul]

  have : Nontrivial (QuotSMulTop y M) := by
    apply Submodule.Quotient.nontrivial_iff.mpr
    refine ne_top_of_le_ne_top (maximalIdeal_smul_top_lt_top (R := R) M).ne ?_
    rw [← Submodule.ideal_span_singleton_smul]
    exact Submodule.smul_mono_left ((Ideal.span_singleton_le_iff_mem _).mpr hy)
  have hltM : 𝔪 • (⊤ : Submodule R M) < ⊤ := maximalIdeal_smul_top_lt_top M
  have hltQ : 𝔪 • (⊤ : Submodule R (QuotSMulTop y M)) < ⊤ :=
    maximalIdeal_smul_top_lt_top (QuotSMulTop y M)

  have hM := (ModuleCat.exists_isRegular_tfae 𝔪 xs.length (ModuleCat.of R M) hltM).out 3 1
  have hExtM := hM.mp ⟨xs, rfl, hmem, hxs⟩

  have hS := IsSMulRegular.smulShortComplex_shortExact (M := ModuleCat.of R M) hreg
  have hExtQ : ∀ i < n, Subsingleton (Abelian.Ext
      (ModuleCat.of R (Shrink.{u_2} (R ⧸ 𝔪))) (ModuleCat.of R (QuotSMulTop y M)) i) := by
    intro i hi
    have hE := Abelian.Ext.covariant_sequence_exact₃'
      (ModuleCat.of R (Shrink.{u_2} (R ⧸ 𝔪))) hS i (i + 1) rfl
    rw [ShortComplex.ab_exact_iff_function_exact] at hE
    have h0 := hExtM i (by omega)
    have h1 := hExtM (i + 1) (by omega)
    have key : ∀ x : Abelian.Ext (ModuleCat.of R (Shrink.{u_2} (R ⧸ 𝔪)))
        (ModuleCat.of R (QuotSMulTop y M)) i, x = 0 := by
      intro x
      obtain ⟨w, hw⟩ := (hE x).mp (h1.elim _ _)
      rw [← hw, h0.elim w 0]
      exact map_zero _
    exact ⟨fun a b => by rw [key a, key b]⟩

  have hQ := (ModuleCat.exists_isRegular_tfae 𝔪 n
    (ModuleCat.of R (QuotSMulTop y M)) hltQ).out 1 3
  obtain ⟨zs, hlen, -, hzs⟩ := hQ.mp hExtQ
  exact ⟨zs, hlen, hzs⟩

end GlobalTheory.RegularElementQuotient
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearEquivMapLatticeEq
section
universe u_1 u_2 u_3

namespace GlobalTheory.LatticeLinearEquivBasis

open Module

theorem span_range_basis_coe {R : Type*} [CommRing R] {V : Type*} [AddCommGroup V] [Module R V]
    {ι : Type*} (A : Submodule R V) (b : Basis ι R A) :
    Submodule.span R (Set.range fun i => (b i : V)) = A := by
  have h : Set.range (fun i => (b i : V)) = A.subtype '' Set.range b := by
    rw [← Set.range_comp]; rfl
  rw [h, ← Submodule.map_span, b.span_eq, Submodule.map_top, Submodule.range_subtype]

theorem exists_linearEquiv_map_lattice_eq : ∀ {R : Type u_1} [inst : CommRing R] [inst_1 : IsDomain R] [IsDiscreteValuationRing R] (K : Type u_2) [inst_3 : Field K] [inst_4 : Algebra R K] [IsFractionRing R K] {V : Type u_3} [inst_6 : AddCommGroup V] [inst_7 : Module K V] [inst_8 : Module R V] [inst_9 : IsScalarTower R K V] (A B : Submodule R V) [Submodule.IsLattice K A] [Submodule.IsLattice K B], Exists fun (g : LinearEquiv (RingHom.id K) V V) ↦ Eq (Submodule.map (LinearMap.restrictScalars R (LinearEquiv.toLinearMap g)) A) B := by
  intro R _ _ _ K _ _ _ V _ _ _ _ A B _ _
  let bA := Free.chooseBasis R A
  let bB := Free.chooseBasis R B
  let eA := bA.extendOfIsLattice K
  let eB := bB.extendOfIsLattice K
  let e := eA.indexEquiv eB
  refine ⟨eA.equiv eB e, ?_⟩
  have hA := span_range_basis_coe A bA
  have hB := span_range_basis_coe B bB
  suffices h : Submodule.map ((eA.equiv eB e : V ≃ₗ[K] V).toLinearMap.restrictScalars R)
      (Submodule.span R (Set.range fun i => (bA i : V))) =
      Submodule.span R (Set.range fun j => (bB j : V)) by
    rw [hA, hB] at h; exact h
  rw [Submodule.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    refine ⟨e i, ?_⟩
    have h1 : (bA i : V) = eA i := (bA.extendOfIsLattice_apply K i).symm
    have h2 : (bB (e i) : V) = eB (e i) := (bB.extendOfIsLattice_apply K (e i)).symm
    simp only [LinearMap.restrictScalars_apply, LinearEquiv.coe_coe]
    rw [h1, h2, Basis.equiv_apply]
  · rintro ⟨j, rfl⟩
    refine ⟨(bA (e.symm j) : V), ⟨e.symm j, rfl⟩, ?_⟩
    have h1 : (bA (e.symm j) : V) = eA (e.symm j) := (bA.extendOfIsLattice_apply K _).symm
    have h2 : (bB j : V) = eB j := (bB.extendOfIsLattice_apply K j).symm
    simp only [LinearMap.restrictScalars_apply, LinearEquiv.coe_coe]
    rw [h1, h2, Basis.equiv_apply, Equiv.apply_symm_apply]

end GlobalTheory.LatticeLinearEquivBasis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.FstHomCompSqzOfLeibniz
section
namespace GlobalTheory.SquareZeroLeibnizPoint

open TrivSqZeroExt

section PointsOfDual

variable {O C : Type*} [CommRing O] [CommRing C] {ι : Type*} [Fintype ι]

def sqzPoint (φ : O →+* C) (n : ι → C) (hn : ∀ a b, n a * n b = 0) :
    TrivSqZeroExt O (ι → O) →+* C where
  toFun x := φ x.fst + ∑ i, φ (x.snd i) * n i
  map_one' := by simp
  map_zero' := by simp
  map_add' x y := by
    simp only [fst_add, snd_add, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
    ring
  map_mul' x y := by
    have hcross : (∑ i, φ (x.snd i) * n i) * (∑ j, φ (y.snd j) * n j) = 0 := by
      rw [Finset.sum_mul_sum]
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
      calc φ (x.snd i) * n i * (φ (y.snd j) * n j)
          = φ (x.snd i) * φ (y.snd j) * (n i * n j) := by ring
        _ = 0 := by rw [hn, mul_zero]
    have hs : ∀ i, (x * y).snd i = x.fst * y.snd i + x.snd i * y.fst := fun i => by
      rw [snd_mul]; rfl
    have h1 : ∑ i, φ ((x * y).snd i) * n i
        = φ x.fst * ∑ i, φ (y.snd i) * n i + φ y.fst * ∑ i, φ (x.snd i) * n i := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [hs, map_add, map_mul, map_mul]; ring
    rw [h1, fst_mul, map_mul]
    linear_combination (-1 : C) * hcross

theorem sqzPoint_apply (φ : O →+* C) (n : ι → C) (hn : ∀ a b, n a * n b = 0)
    (x : TrivSqZeroExt O (ι → O)) :
    sqzPoint φ n hn x = φ x.fst + ∑ i, φ (x.snd i) * n i := rfl

@[simp] theorem sqzPoint_inl (φ : O →+* C) (n : ι → C) (hn : ∀ a b, n a * n b = 0) (a : O) :
    sqzPoint φ n hn (inl a) = φ a := by
  rw [sqzPoint_apply]
  simp

@[simp] theorem sqzPoint_inr (φ : O →+* C) (n : ι → C) (hn : ∀ a b, n a * n b = 0) (v : ι → O) :
    sqzPoint φ n hn (inr v) = ∑ i, φ (v i) * n i := by
  rw [sqzPoint_apply]
  simp

end PointsOfDual

section Leibniz

variable {A O M : Type*} [CommRing A] [CommRing O] [AddCommGroup M] [Module O M]

theorem leibniz_map_one (ε : A →+* O) (d : A →+ M)
    (hd : ∀ f f', d (f * f') = ε f • d f' + ε f' • d f) : d 1 = 0 := by
  have h := hd 1 1
  simpa using h

variable [Module Oᵐᵒᵖ M] [IsCentralScalar O M]

def sqzOfLeibniz (ε : A →+* O) (d : A →+ M)
    (hd : ∀ f f', d (f * f') = ε f • d f' + ε f' • d f) : A →+* TrivSqZeroExt O M where
  toFun f := (ε f, d f)
  map_one' := TrivSqZeroExt.ext (map_one ε) (leibniz_map_one ε d hd)
  map_zero' := TrivSqZeroExt.ext (map_zero ε) (map_zero d)
  map_add' f f' := TrivSqZeroExt.ext (map_add ε f f') (map_add d f f')
  map_mul' f f' := TrivSqZeroExt.ext (map_mul ε f f') (by
    change d (f * f') = ε f • d f' + MulOpposite.op (ε f') • d f
    rw [op_smul_eq_smul]
    exact hd f f')

@[simp] theorem sqzOfLeibniz_fst (ε : A →+* O) (d : A →+ M)
    (hd : ∀ f f', d (f * f') = ε f • d f' + ε f' • d f) (f : A) :
    (sqzOfLeibniz ε d hd f).fst = ε f := rfl

@[simp] theorem sqzOfLeibniz_snd (ε : A →+* O) (d : A →+ M)
    (hd : ∀ f f', d (f * f') = ε f • d f' + ε f' • d f) (f : A) :
    (sqzOfLeibniz ε d hd f).snd = d f := rfl

end Leibniz

end GlobalTheory.SquareZeroLeibnizPoint
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Imports
section
universe u_1 u_2

namespace GlobalTheory.AdditiveValuationProduct

theorem addVal_prod : ∀ {R : Type u_1} [inst : CommRing R] [inst_1 : IsDomain R] [inst_2 : IsDiscreteValuationRing R] {ι : Type u_2} (s : Finset ι) (a : ι → R), (IsDiscreteValuationRing.addVal R : R → ℕ∞) (∏ i ∈ s, a i) = ∑ i ∈ s, (IsDiscreteValuationRing.addVal R : R → ℕ∞) (a i) := by
  intro R _ _ _ ι s a
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j t hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj, AddValuation.map_mul, ih]

end GlobalTheory.AdditiveValuationProduct
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IntegralAgainstLinearApply
section
open MeasureTheory

namespace GlobalTheory.IntegralAgainstMeasure

variable {K B : Type*} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K]
  [OpensMeasurableSpace K] [NormedAddCommGroup B] [NormedSpace ℂ B]

theorem integrable_smul (μ : Measure K) [IsFiniteMeasure μ] (p : C(K, B)) (f : C(K, ℂ)) :
    Integrable (fun k => f k • p k) μ :=
  (f.continuous.smul p.continuous).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

noncomputable def integralAgainstLinear (μ : Measure K) [IsFiniteMeasure μ] (p : C(K, B)) :
    C(K, ℂ) →ₗ[ℂ] B where
  toFun f := ∫ k, f k • p k ∂μ
  map_add' f g := by
    simp only [ContinuousMap.add_apply, add_smul]
    exact integral_add (integrable_smul μ p f) (integrable_smul μ p g)
  map_smul' c f := by
    simp only [ContinuousMap.smul_apply, smul_assoc, RingHom.id_apply]
    exact integral_smul c _

@[simp] theorem integralAgainstLinear_apply (μ : Measure K) [IsFiniteMeasure μ] (p : C(K, B))
    (f : C(K, ℂ)) : integralAgainstLinear μ p f = ∫ k, f k • p k ∂μ := rfl

theorem norm_integral_smul_le (μ : Measure K) [IsFiniteMeasure μ] (p : C(K, B)) (f : C(K, ℂ)) :
    ‖∫ k, f k • p k ∂μ‖ ≤ (μ.real Set.univ * ‖p‖) * ‖f‖ := by
  have h : ∀ᵐ k ∂μ, ‖f k • p k‖ ≤ ‖p‖ * ‖f‖ := Filter.Eventually.of_forall fun k => by
    rw [norm_smul, mul_comm]
    exact mul_le_mul (p.norm_coe_le_norm k) (f.norm_coe_le_norm k) (norm_nonneg _) (norm_nonneg _)
  calc ‖∫ k, f k • p k ∂μ‖ ≤ ‖p‖ * ‖f‖ * μ.real Set.univ := norm_integral_le_of_norm_le_const h
    _ = (μ.real Set.univ * ‖p‖) * ‖f‖ := by ring

noncomputable def integralAgainst (μ : Measure K) [IsFiniteMeasure μ] (p : C(K, B)) :
    C(K, ℂ) →L[ℂ] B :=
  (integralAgainstLinear μ p).mkContinuous (μ.real Set.univ * ‖p‖) (norm_integral_smul_le μ p)

@[simp] theorem integralAgainst_apply (μ : Measure K) [IsFiniteMeasure μ] (p : C(K, B))
    (f : C(K, ℂ)) : integralAgainst μ p f = ∫ k, f k • p k ∂μ := rfl

end GlobalTheory.IntegralAgainstMeasure
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsCounitDerivationCounitComp
section
open TensorProduct

namespace GlobalTheory.LeftRightDerivations

variable {k : Type*} {H : Type*} [CommSemiring k] [CommSemiring H] [Bialgebra k H]

def IsCounitDerivation (φ : H →ₗ[k] k) : Prop :=
  ∀ a b : H, φ (a * b) =
    Coalgebra.counit (R := k) a * φ b + Coalgebra.counit (R := k) b * φ a

theorem isCounitDerivation_iff (φ : H →ₗ[k] k) :
    IsCounitDerivation φ ↔ ∀ a b : H, φ (a * b) =
      Coalgebra.counit (R := k) a * φ b + Coalgebra.counit (R := k) b * φ a := Iff.rfl

noncomputable def contrRight (φ : H →ₗ[k] k) : H ⊗[k] H →ₗ[k] H :=
  (TensorProduct.rid k H).toLinearMap ∘ₗ LinearMap.lTensor H φ

noncomputable def contrLeft (φ : H →ₗ[k] k) : H ⊗[k] H →ₗ[k] H :=
  (TensorProduct.lid k H).toLinearMap ∘ₗ LinearMap.rTensor H φ

@[simp] theorem contrRight_tmul (φ : H →ₗ[k] k) (a b : H) :
    contrRight φ (a ⊗ₜ[k] b) = φ b • a := by
  simp [contrRight]

@[simp] theorem contrLeft_tmul (φ : H →ₗ[k] k) (a b : H) :
    contrLeft φ (a ⊗ₜ[k] b) = φ a • b := by
  simp [contrLeft]

theorem contrRight_counit_comul (a : H) :
    contrRight (Coalgebra.counit (R := k)) (Coalgebra.comul (R := k) a) = a := by

  simp [contrRight, Coalgebra.lTensor_counit_comul]

theorem contrLeft_counit_comul (a : H) :
    contrLeft (Coalgebra.counit (R := k)) (Coalgebra.comul (R := k) a) = a := by
  simp [contrLeft, Coalgebra.rTensor_counit_comul]

theorem contrRight_mul {φ : H →ₗ[k] k} (hφ : IsCounitDerivation φ) (s t : H ⊗[k] H) :
    contrRight φ (s * t) =
      contrRight (Coalgebra.counit (R := k)) s * contrRight φ t +
        contrRight (Coalgebra.counit (R := k)) t * contrRight φ s := by

  induction s using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [add_mul, map_add, hx, hy]; ring
  | tmul a b =>
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [mul_add, map_add, hx, hy]; ring
    | tmul c d =>
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      simp only [contrRight_tmul, hφ b d, Algebra.smul_def, map_add, map_mul]
      ring

theorem contrLeft_mul {φ : H →ₗ[k] k} (hφ : IsCounitDerivation φ) (s t : H ⊗[k] H) :
    contrLeft φ (s * t) =
      contrLeft (Coalgebra.counit (R := k)) s * contrLeft φ t +
        contrLeft (Coalgebra.counit (R := k)) t * contrLeft φ s := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [add_mul, map_add, hx, hy]; ring
  | tmul a b =>
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [mul_add, map_add, hx, hy]; ring
    | tmul c d =>
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      simp only [contrLeft_tmul, hφ a c, Algebra.smul_def, map_add, map_mul]
      ring

theorem contrRight_one (φ : H →ₗ[k] k) : contrRight φ 1 = φ 1 • (1 : H) := by
  rw [Algebra.TensorProduct.one_def, contrRight_tmul]

theorem contrLeft_one (φ : H →ₗ[k] k) : contrLeft φ 1 = φ 1 • (1 : H) := by
  rw [Algebra.TensorProduct.one_def, contrLeft_tmul]

theorem counit_contrRight (φ : H →ₗ[k] k) (s : H ⊗[k] H) :
    Coalgebra.counit (R := k) (contrRight φ s) =
      φ (contrLeft (Coalgebra.counit (R := k)) s) := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [mul_comm]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem counit_contrLeft (φ : H →ₗ[k] k) (s : H ⊗[k] H) :
    Coalgebra.counit (R := k) (contrLeft φ s) =
      φ (contrRight (Coalgebra.counit (R := k)) s) := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [mul_comm]
  | add x y hx hy => simp only [map_add, hx, hy]

section Ring

variable {k : Type*} {H : Type*} [CommRing k] [CommRing H] [Bialgebra k H]

theorem IsCounitDerivation.map_one {φ : H →ₗ[k] k} (hφ : IsCounitDerivation φ) : φ 1 = 0 := by

  have h := hφ 1 1
  rw [mul_one, Bialgebra.counit_one, one_mul] at h
  simpa using h

noncomputable def derivRight (φ : H →ₗ[k] k) (hφ : IsCounitDerivation φ) : Derivation k H H where
  toLinearMap := contrRight φ ∘ₗ Coalgebra.comul (R := k)
  map_one_eq_zero' := by
    rw [LinearMap.comp_apply, Bialgebra.comul_one, contrRight_one, hφ.map_one, zero_smul]
  leibniz' a b := by
    simp only [LinearMap.comp_apply, Bialgebra.comul_mul, contrRight_mul hφ,
      contrRight_counit_comul, smul_eq_mul]

noncomputable def derivLeft (φ : H →ₗ[k] k) (hφ : IsCounitDerivation φ) : Derivation k H H where
  toLinearMap := contrLeft φ ∘ₗ Coalgebra.comul (R := k)
  map_one_eq_zero' := by
    rw [LinearMap.comp_apply, Bialgebra.comul_one, contrLeft_one, hφ.map_one, zero_smul]
  leibniz' a b := by
    simp only [LinearMap.comp_apply, Bialgebra.comul_mul, contrLeft_mul hφ,
      contrLeft_counit_comul, smul_eq_mul]

theorem derivRight_apply (φ : H →ₗ[k] k) (hφ : IsCounitDerivation φ) (y : H) :
    derivRight φ hφ y =
      TensorProduct.rid k H (LinearMap.lTensor H φ (Coalgebra.comul (R := k) y)) := rfl

theorem derivLeft_apply (φ : H →ₗ[k] k) (hφ : IsCounitDerivation φ) (y : H) :
    derivLeft φ hφ y =
      TensorProduct.lid k H (LinearMap.rTensor H φ (Coalgebra.comul (R := k) y)) := rfl

theorem counit_derivRight (φ : H →ₗ[k] k) (hφ : IsCounitDerivation φ) (y : H) :
    Coalgebra.counit (R := k) (derivRight φ hφ y) = φ y := by
  have h : derivRight φ hφ y = contrRight φ (Coalgebra.comul (R := k) y) := rfl
  rw [h, counit_contrRight, contrLeft_counit_comul]

theorem counit_derivLeft (φ : H →ₗ[k] k) (hφ : IsCounitDerivation φ) (y : H) :
    Coalgebra.counit (R := k) (derivLeft φ hφ y) = φ y := by
  have h : derivLeft φ hφ y = contrLeft φ (Coalgebra.comul (R := k) y) := rfl
  rw [h, counit_contrLeft, contrRight_counit_comul]

theorem isCounitDerivation_counit_comp (D : Derivation k H H) :
    IsCounitDerivation (Coalgebra.counit (R := k) ∘ₗ D.toLinearMap) := by

  intro a b
  simp [Derivation.leibniz, Bialgebra.counit_mul]

end Ring

end GlobalTheory.LeftRightDerivations
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthQuotientSpanSingleton
section
universe u_1 u_2

namespace GlobalTheory.LengthQuotientValuationDet

open Module IsDiscreteValuationRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

theorem addVal_prod {ι : Type*} (s : Finset ι) (f : ι → R) :
    addVal R (∏ i ∈ s, f i) = ∑ i ∈ s, addVal R (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.prod_insert hj, Finset.sum_insert hj, AddValuation.map_mul, ih]

theorem length_quotient_span_singleton {x : R} (hx : x ≠ 0) :
    Module.length R (R ⧸ Ideal.span ({x} : Set R)) = addVal R x := by
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
  obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible hx hϖ
  rw [Ideal.span_singleton_mul_left_unit u.isUnit, ← Ideal.span_singleton_pow,
    ← hϖ.maximalIdeal_eq, length_quotient_pow_maximalIdeal, addVal_def' u hϖ]

theorem length_quotient_eq_addVal_det {R : Type u_1} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {M : Type u_2} [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M] (N : Submodule R M) (e : M ≃ₗ[R] N) :
    Module.length R (M ⧸ N) =
      (addVal R : R → ℕ∞) (LinearMap.det (N.subtype ∘ₗ (e : M →ₗ[R] N))) := by
  classical
  let b := Module.Free.chooseBasis R M
  have h : Module.finrank R N = Module.finrank R M := e.symm.finrank_eq
  let a := Submodule.smithNormalFormCoeffs b h
  let b' := Submodule.smithNormalFormTopBasis b h
  let ab := Submodule.smithNormalFormBotBasis b h
  have ab_eq := Submodule.smithNormalFormBotBasis_def b h
  let e' : M ≃ₗ[R] N := b'.equiv ab (Equiv.refl _)
  let f : M →ₗ[R] M := N.subtype ∘ₗ (e' : M →ₗ[R] N)
  have hassoc : Associated (LinearMap.det (N.subtype ∘ₗ (e : M →ₗ[R] N))) (LinearMap.det f) :=
    LinearMap.associated_det_comp_equiv _ _ _
  rw [(addVal_eq_iff_associated _ _).mpr hassoc]
  have ha : ∀ i, f (b' i) = a i • b' i := by
    intro i
    change ((b'.equiv ab (Equiv.refl _)) (b' i) : M) = _
    rw [b'.equiv_apply, Equiv.refl_apply]
    exact ab_eq i
  have hdet : LinearMap.det f = ∏ i, a i := by
    rw [← LinearMap.det_toMatrix b', ← Matrix.det_diagonal]
    congr 1
    ext i j
    rw [LinearMap.toMatrix_apply, ha, map_smul, Basis.repr_self, Finsupp.smul_single,
      smul_eq_mul, mul_one]
    by_cases hij : i = j
    · subst hij; rw [Matrix.diagonal_apply_eq, Finsupp.single_eq_same]
    · rw [Matrix.diagonal_apply_ne _ hij, Finsupp.single_eq_of_ne hij]
  rw [hdet, addVal_prod, (N.quotientEquivPiSpan b h).length_eq, Module.length_pi_of_fintype]
  exact Finset.sum_congr rfl fun i _ =>
    length_quotient_span_singleton (Submodule.smithNormalFormCoeffs_ne_zero b h i)

end GlobalTheory.LengthQuotientValuationDet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RootCharOfAddNatCast
section
namespace GlobalTheory.RootCharacter

open scoped BigOperators

variable {B : Type*} [CommMonoid B] {I : Type*} [Fintype I] {n : ℕ} [NeZero n]

theorem pow_val_add {x : B} (hx : x ^ n = 1) (a b : ZMod n) :
    x ^ (a + b).val = x ^ a.val * x ^ b.val := by
  rw [ZMod.val_add, ← pow_add, ← pow_eq_pow_mod _ hx]

def rootChar (u : I → B) (hu : ∀ q, u q ^ n = 1) : Multiplicative (I → ZMod n) →* B where
  toFun a := ∏ q, u q ^ (Multiplicative.toAdd a q).val
  map_one' := by simp
  map_mul' a b := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun q _ => pow_val_add (hu q) _ _

end GlobalTheory.RootCharacter
end

