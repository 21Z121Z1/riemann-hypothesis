import Mathlib

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CardFilterResCharLe
section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.IdealNormInequalities

variable {K : Type} [Field K] [NumberField K]

def resChar (P : Ideal (𝓞 K)) : ℕ := Ideal.absNorm (P.under ℤ)

theorem span_resChar (P : Ideal (𝓞 K)) : Ideal.span {(resChar P : ℤ)} = P.under ℤ := Int.ideal_span_absNorm_eq_self _

theorem under_ne_bot {P : Ideal (𝓞 K)} (hP : P.IsMaximal) : P.under ℤ ≠ ⊥ := by
  intro h
  have hPb : P = ⊥ := Ideal.eq_bot_of_comap_eq_bot h
  exact Ring.ne_bot_of_isMaximal_of_not_isField hP (NumberField.RingOfIntegers.not_isField K) hPb

theorem under_isMaximal {P : Ideal (𝓞 K)} (hP : P.IsMaximal) : (P.under ℤ).IsMaximal := by
  haveI := hP
  exact Ideal.IsMaximal.under ℤ P

theorem resChar_prime {P : Ideal (𝓞 K)} (hP : P.IsMaximal) : (resChar P).Prime := by

  have h1 := span_resChar P
  have hmax := under_isMaximal hP
  rw [← h1] at hmax
  have hne : ((resChar P : ℕ) : ℤ) ≠ 0 := by
    intro h0
    apply under_ne_bot hP
    rw [← h1, h0]
    simp
  have hpr := (Ideal.span_singleton_prime hne).mp hmax.isPrime
  exact Nat.prime_iff_prime_int.mpr hpr

theorem exists_absNorm_eq_pow {P : Ideal (𝓞 K)} (hP : P.IsMaximal) :
    ∃ k : ℕ, 1 ≤ k ∧ Ideal.absNorm P = resChar P ^ k := by

  have hp := resChar_prime hP
  haveI : P.LiesOver (Ideal.span {((resChar P : ℕ) : ℤ)}) := ⟨span_resChar P⟩
  have h1 := Ideal.absNorm_eq_pow_inertiaDeg P (Nat.prime_iff_prime_int.mp hp)
  rw [show (((resChar P : ℕ) : ℤ)).natAbs = resChar P by simp] at h1
  refine ⟨_, ?_, h1⟩
  rw [Nat.one_le_iff_ne_zero]
  intro h0
  rw [h0, pow_zero, Ideal.absNorm_eq_one_iff] at h1
  exact hP.ne_top h1

theorem resChar_le_absNorm {P : Ideal (𝓞 K)} (hP : P.IsMaximal) :
    resChar P ≤ Ideal.absNorm P := by

  obtain ⟨k, hk, hk2⟩ := exists_absNorm_eq_pow hP
  rw [hk2]
  exact Nat.le_self_pow (by omega) _

theorem resChar_le_of_sq {P : Ideal (𝓞 K)} (hP : P.IsMaximal) {q : ℕ}
    (hq : Ideal.absNorm P = q ^ 2) : resChar P ≤ q := by

  obtain ⟨k, hk, hk2⟩ := exists_absNorm_eq_pow hP
  have hp := resChar_prime hP
  have hdvd : resChar P ∣ q ^ 2 := by
    rw [← hq, hk2]
    exact dvd_pow_self _ (by omega)
  have hq0 : q ≠ 0 := by
    rintro rfl
    have h0 : resChar P ^ k = 0 := by rw [← hk2, hq]; simp
    exact hp.ne_zero (pow_eq_zero_iff (by omega) |>.mp h0)
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero hq0) (hp.dvd_of_dvd_pow hdvd)

set_option linter.deprecated false in
theorem card_filter_resChar_le (s : Finset {P : Ideal (𝓞 K) // P.IsMaximal}) (n : ℕ) :
    (s.filter (fun P => resChar P.1 = n)).card ≤ finrank ℚ K := by

  classical
  by_cases hn : ∃ P ∈ s, resChar P.1 = n
  · obtain ⟨P0, -, hP0⟩ := hn
    have hJ : Ideal.span {((n : ℕ) : ℤ)} = P0.1.under ℤ := by
      rw [← hP0]
      exact span_resChar P0.1
    haveI : (Ideal.span {((n : ℕ) : ℤ)}).IsMaximal := by
      rw [hJ]
      exact under_isMaximal P0.2
    have hJne : Ideal.span {((n : ℕ) : ℤ)} ≠ ⊥ := by
      rw [hJ]
      exact under_ne_bot P0.2
    calc (s.filter (fun P => resChar P.1 = n)).card
        ≤ (IsDedekindDomain.primesOverFinset (Ideal.span {((n : ℕ) : ℤ)}) (𝓞 K)).card := by
          refine Finset.card_le_card_of_injOn (fun P => P.1) (by
            intro P hP
            rw [Finset.mem_coe, IsDedekindDomain.mem_primesOverFinset_iff hJne]
            obtain ⟨-, hPn⟩ := Finset.mem_filter.mp hP
            refine ⟨P.2.isPrime, ⟨?_⟩⟩
            rw [← hPn]
            exact span_resChar P.1) (fun a _ b _ h => Subtype.ext h)
      _ ≤ finrank ℚ K := Ideal.card_primesOverFinset_le_finrank (𝓞 K) ℚ K hJne
  · push_neg at hn
    rw [Finset.filter_false_of_mem (fun P hP => hn P hP)]
    simp

theorem summable_resChar_sq :
    Summable (fun P : {P : Ideal (𝓞 K) // P.IsMaximal} => ((resChar P.1 : ℝ) ^ 2)⁻¹) := by

  classical
  have hs : Summable (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) := Real.summable_nat_pow_inv.mpr (by norm_num)
  refine summable_of_sum_le (c := (finrank ℚ K : ℝ) * ∑' n : ℕ, ((n : ℝ) ^ 2)⁻¹) (fun P => by positivity)
    (fun u => ?_)
  calc ∑ P ∈ u, ((resChar P.1 : ℝ) ^ 2)⁻¹
      = ∑ n ∈ u.image (fun P => resChar P.1),
          ∑ P ∈ u.filter (fun P => resChar P.1 = n), ((resChar P.1 : ℝ) ^ 2)⁻¹ :=
        (Finset.sum_fiberwise_of_maps_to (fun P hP => Finset.mem_image_of_mem _ hP) _).symm
    _ = ∑ n ∈ u.image (fun P => resChar P.1),
          ((u.filter (fun P => resChar P.1 = n)).card : ℝ) * ((n : ℝ) ^ 2)⁻¹ := by
        refine Finset.sum_congr rfl (fun n _ => ?_)
        rw [Finset.sum_congr rfl (fun P hP => by rw [(Finset.mem_filter.mp hP).2]), Finset.sum_const,
          nsmul_eq_mul]
    _ ≤ ∑ n ∈ u.image (fun P => resChar P.1), (finrank ℚ K : ℝ) * ((n : ℝ) ^ 2)⁻¹ := by
        refine Finset.sum_le_sum (fun n _ => ?_)
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast card_filter_resChar_le u n
    _ = (finrank ℚ K : ℝ) * ∑ n ∈ u.image (fun P => resChar P.1), ((n : ℝ) ^ 2)⁻¹ := by
        rw [Finset.mul_sum]
    _ ≤ (finrank ℚ K : ℝ) * ∑' n : ℕ, ((n : ℝ) ^ 2)⁻¹ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact hs.sum_le_tsum _ (fun n _ => by positivity)

end Formalism.HermitianLattices.Ext.L3.IdealNormInequalities
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.DetMulLeftCompMulRight
section
open Matrix TensorProduct

namespace Formalism.HermitianLattices.Ext.L3.LITr

section Det

variable {R : Type*} [CommRing R] {m : ℕ}

end Det

section Herm

variable {K F : Type*} [Field K] [CharZero K] [StarRing K] [Field F] [Algebra F K] {m : ℕ}

def hermSub (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) (m : ℕ) :
    Submodule F (Matrix (Fin m) (Fin m) K) where
  carrier := {B | Bᴴ = B}
  add_mem' := by
    intro a b ha hb
    change (a + b)ᴴ = a + b
    rw [Matrix.conjTranspose_add, show aᴴ = a from ha, show bᴴ = b from hb]
  zero_mem' := Matrix.conjTranspose_zero
  smul_mem' := by
    intro c B hB
    change (c • B)ᴴ = c • B
    rw [← algebraMap_smul K c B, Matrix.conjTranspose_smul, show Bᴴ = B from hB, (hF _).2 ⟨c, rfl⟩]

variable (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K))

theorem mem_hermSub (B : Matrix (Fin m) (Fin m) K) : B ∈ hermSub hF m ↔ Bᴴ = B := Iff.rfl

noncomputable def toMat (m : ℕ) : K ⊗[F] (hermSub hF m) →ₗ[K] Matrix (Fin m) (Fin m) K :=
  (hermSub hF m).subtype.liftBaseChange K

theorem toMat_tmul (a : K) (B : hermSub hF m) :
    toMat hF m (a ⊗ₜ B) = a • (B : Matrix (Fin m) (Fin m) K) := by
  simp [toMat]

include hF in
theorem exists_decomp {δ : K} (hδ : star δ = -δ) (hδ0 : δ ≠ 0) (a : K) :
    ∃ x y : F, a = algebraMap F K x + δ * algebraMap F K y := by
  obtain ⟨x, hx⟩ := (hF ((a + star a) / 2)).1 (by
    rw [star_div₀, star_add, star_star, star_ofNat, add_comm])
  obtain ⟨y, hy⟩ := (hF ((a - star a) / (2 * δ))).1 (by
    rw [star_div₀, star_sub, star_star, star_mul', star_ofNat, hδ]
    field_simp
    ring)
  refine ⟨x, y, ?_⟩
  rw [hx, hy]
  field_simp
  ring

theorem exists_tensor_decomp {δ : K} (hδ : star δ = -δ) (hδ0 : δ ≠ 0) (t : K ⊗[F] (hermSub hF m)) :
    ∃ B C : hermSub hF m, t = (1 : K) ⊗ₜ B + δ ⊗ₜ C := by
  induction t with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul a B =>
    obtain ⟨x, y, rfl⟩ := exists_decomp hF hδ hδ0 a
    refine ⟨x • B, y • B, ?_⟩
    rw [TensorProduct.add_tmul, TensorProduct.tmul_smul, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul', TensorProduct.smul_tmul', Algebra.smul_def, Algebra.smul_def, mul_one,
      mul_comm δ]
  | add s t hs ht =>
    obtain ⟨B, C, rfl⟩ := hs
    obtain ⟨B', C', rfl⟩ := ht
    refine ⟨B + B', C + C', ?_⟩
    rw [TensorProduct.tmul_add, TensorProduct.tmul_add]
    abel

theorem toMat_injective {δ : K} (hδ : star δ = -δ) (hδ0 : δ ≠ 0) :
    Function.Injective (toMat hF m) := by
  rw [injective_iff_map_eq_zero]
  intro t ht
  obtain ⟨B, C, rfl⟩ := exists_tensor_decomp hF hδ hδ0 t
  rw [map_add, toMat_tmul, toMat_tmul, one_smul] at ht
  have ht' := congrArg Matrix.conjTranspose ht
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, (mem_hermSub hF _).1 B.2,
    (mem_hermSub hF _).1 C.2, hδ, Matrix.conjTranspose_zero, neg_smul] at ht'
  have hB : (B : Matrix (Fin m) (Fin m) K) = 0 := by
    have : (2 : K) • (B : Matrix (Fin m) (Fin m) K) = 0 := by
      rw [two_smul]
      calc _ = ((B : Matrix (Fin m) (Fin m) K) + δ • (C : Matrix (Fin m) (Fin m) K)) +
            ((B : Matrix (Fin m) (Fin m) K) + -(δ • (C : Matrix (Fin m) (Fin m) K))) := by abel
        _ = 0 := by rw [ht, ht', add_zero]
    exact (smul_eq_zero.1 this).resolve_left two_ne_zero
  have hC : (C : Matrix (Fin m) (Fin m) K) = 0 := by
    rw [hB, zero_add] at ht
    exact (smul_eq_zero.1 ht).resolve_left hδ0
  rw [Subtype.ext (a1 := B) (a2 := 0) hB, Subtype.ext (a1 := C) (a2 := 0) hC]
  simp

theorem toMat_surjective {δ : K} (hδ : star δ = -δ) (hδ0 : δ ≠ 0) :
    Function.Surjective (toMat hF m) := by
  intro X
  have h1 : ((2 : K)⁻¹ • (X + Xᴴ)) ∈ hermSub hF m := by
    rw [mem_hermSub, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
      Matrix.conjTranspose_conjTranspose, star_inv₀, star_ofNat, add_comm]
  have h2 : ((2 * δ)⁻¹ • (X - Xᴴ)) ∈ hermSub hF m := by
    rw [mem_hermSub, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_conjTranspose, star_inv₀, star_mul', star_ofNat, hδ, mul_neg, inv_neg,
      neg_smul, ← smul_neg, neg_sub]
  refine ⟨(1 : K) ⊗ₜ ⟨_, h1⟩ + δ ⊗ₜ ⟨_, h2⟩, ?_⟩
  rw [map_add, toMat_tmul, toMat_tmul, one_smul, smul_smul]
  have : δ * (2 * δ)⁻¹ = (2 : K)⁻¹ := by field_simp
  rw [this, ← smul_add]
  have : X + Xᴴ + (X - Xᴴ) = (2 : K) • X := by rw [two_smul]; abel
  rw [this, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]

noncomputable def toMatEquiv {δ : K} (hδ : star δ = -δ) (hδ0 : δ ≠ 0) (m : ℕ) :
    K ⊗[F] (hermSub hF m) ≃ₗ[K] Matrix (Fin m) (Fin m) K :=
  LinearEquiv.ofBijective (toMat hF m) ⟨toMat_injective hF hδ hδ0, toMat_surjective hF hδ hδ0⟩

def conjHerm (P : Matrix (Fin m) (Fin m) K) : hermSub hF m →ₗ[F] hermSub hF m where
  toFun B := ⟨Pᴴ * (B : Matrix (Fin m) (Fin m) K) * P, by
    rw [mem_hermSub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, (mem_hermSub hF _).1 B.2, Matrix.mul_assoc]⟩
  map_add' B C := by
    apply Subtype.ext
    simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c B := by
    apply Subtype.ext
    simp

end Herm

end Formalism.HermitianLattices.Ext.L3.LITr
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.DiscreteTopologyOfZsmul
section
open MeasureTheory Module ZSpan Filter Topology Pointwise Bornology

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.BallA

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] (μ : Measure E) [μ.IsAddHaarMeasure]

private theorem volume_image_equivFun_eq_map_symm {ι : Type*} [Fintype ι] (B : Basis ι ℝ E)
    (s : Set E) : volume (B.equivFun '' s) = Measure.map B.equivFunL.symm volume s := by
  rw [LinearEquiv.image_eq_preimage_symm]
  exact (B.equivFunL.symm.toHomeomorph.toMeasurableEquiv.map_apply s).symm

private theorem volume_image_equivFun_fundamentalDomain_eq_one {ι : Type*} [Fintype ι] (B : Basis ι ℝ E) :
    volume (B.equivFun '' fundamentalDomain B) = 1 := by
  have h : B.equivFun '' fundamentalDomain B = Set.univ.pi fun _ : ι ↦ Set.Ico (0 : ℝ) 1 := by
    ext x
    simp only [Set.mem_image, mem_fundamentalDomain, Set.mem_univ_pi]
    constructor
    · rintro ⟨m, hm, rfl⟩ i
      simpa [Basis.equivFun_apply] using hm i
    · intro hx
      refine ⟨B.equivFun.symm x, fun i ↦ ?_, B.equivFun.apply_symm_apply x⟩
      have hxi := congrFun (B.equivFun.apply_symm_apply x) i
      rw [Basis.equivFun_apply] at hxi
      rw [hxi]
      exact hx i
  rw [h, volume_pi_pi]
  simp

private theorem covolume_eq_addHaarScalarFactor_mul_covolume (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (ν ν' : Measure E) [ν.IsAddHaarMeasure] [ν'.IsAddHaarMeasure] :
    ZLattice.covolume Λ ν =
      (Measure.addHaarScalarFactor ν ν' : ℝ) * ZLattice.covolume Λ ν' := by
  have h := Measure.isAddLeftInvariant_eq_smul ν ν'
  let b := Module.Free.chooseBasis ℤ Λ
  rw [ZLattice.covolume_eq_measure_fundamentalDomain Λ ν (ZLattice.isAddFundamentalDomain b ν),
    ZLattice.covolume_eq_measure_fundamentalDomain Λ ν' (ZLattice.isAddFundamentalDomain b ν')]
  generalize Measure.addHaarScalarFactor ν ν' = c at h ⊢
  rw [h]
  exact measureReal_nnreal_smul_apply _

theorem volume_image_equivFun {ι : Type*} [Fintype ι] (b : Basis ι ℤ L) (s : Set E) :
    volume ((b.ofZLatticeBasis ℝ L).equivFun '' s) =
      μ s / ENNReal.ofReal (ZLattice.covolume L μ) := by
  obtain ⟨ν, hν⟩ : ∃ ν : Measure E,
      ν = Measure.map (b.ofZLatticeBasis ℝ L).equivFunL.symm volume := ⟨_, rfl⟩
  have : ν.IsAddHaarMeasure := hν ▸ inferInstance
  have hcov : ZLattice.covolume L ν = 1 := by
    rw [ZLattice.covolume_eq_measure_fundamentalDomain L ν (ZLattice.isAddFundamentalDomain b ν),
      measureReal_def, hν, ← volume_image_equivFun_eq_map_symm, volume_image_equivFun_fundamentalDomain_eq_one,
      ENNReal.toReal_one]
  rw [volume_image_equivFun_eq_map_symm, ← hν, covolume_eq_addHaarScalarFactor_mul_covolume L μ ν, hcov, mul_one,
    ENNReal.ofReal_coe_nnreal]
  have hc := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ ν
  have h := Measure.isAddLeftInvariant_eq_smul μ ν
  generalize Measure.addHaarScalarFactor μ ν = c at hc h ⊢
  have hc0 : (c : ENNReal) ≠ 0 := by simpa using hc.ne'
  rw [h, Measure.coe_nnreal_smul_apply, mul_comm, ENNReal.mul_div_cancel_right hc0 ENNReal.coe_ne_top]

theorem tendsto_card_div_pow {s : Set E} (hs₁ : IsBounded s) (hs₂ : MeasurableSet s)
    (hs₃ : μ (frontier s) = 0) :
    Tendsto (fun n : ℕ ↦ (Nat.card (s ∩ (n : ℝ)⁻¹ • L : Set E) : ℝ) / n ^ finrank ℝ E)
      atTop (𝓝 (μ.real s / ZLattice.covolume L μ)) := by
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ L) = finrank ℝ E := by
    rw [← finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ L]
  have hfr : frontier (((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L).equivFun '' s) =
      ((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L).equivFun '' frontier s :=
    (((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L).equivFunL.toHomeomorph.image_frontier
      s).symm
  have hlim : volume.real (((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L).equivFun '' s) =
      μ.real s / ZLattice.covolume L μ := by
    rw [measureReal_def, volume_image_equivFun L μ, ENNReal.toReal_div,
      ENNReal.toReal_ofReal (ZLattice.covolume_pos L μ).le, measureReal_def]
  have key := ZLattice.covolume.tendsto_card_div_pow'' (Module.Free.chooseBasis ℤ L) hs₁ hs₂
    (by rw [hfr, volume_image_equivFun L μ, hs₃, ENNReal.zero_div])
  rw [hlim, hcard] at key
  exact key

set_option backward.isDefEq.respectTransparency.types false in
theorem covolume_div_covolume (L₁ L₂ : Submodule ℤ E) [DiscreteTopology L₁] [IsZLattice ℝ L₁]
    [DiscreteTopology L₂] [IsZLattice ℝ L₂] (h : L₁ ≤ L₂) :
    ZLattice.covolume L₁ μ / ZLattice.covolume L₂ μ =
      L₁.toAddSubgroup.relIndex L₂.toAddSubgroup := by
  obtain ⟨ν, hν⟩ : ∃ ν : Measure E,
      ν = Measure.map (Module.finBasis ℝ E).equivFunL.symm volume := ⟨_, rfl⟩
  have : ν.IsAddHaarMeasure := hν ▸ inferInstance
  have he : MeasurePreserving (Module.finBasis ℝ E).equivFunL.symm volume ν := by
    rw [hν]
    exact (Module.finBasis ℝ E).equivFunL.symm.continuous.measurable.measurePreserving _
  have hc := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ ν
  rw [covolume_eq_addHaarScalarFactor_mul_covolume L₁ μ ν, covolume_eq_addHaarScalarFactor_mul_covolume L₂ μ ν,
    mul_div_mul_left _ _ (NNReal.coe_pos.mpr hc).ne', ← ZLattice.covolume_comap L₁ ν volume he,
    ← ZLattice.covolume_comap L₂ ν volume he,
    ZLattice.covolume_div_covolume_eq_relIndex _ _ (fun _ h' ↦ h h'),
    ZLattice.comap_toAddSubgroup, ZLattice.comap_toAddSubgroup, Nat.cast_inj,
    LinearEquiv.toAddMonoidHom_commutes, AddSubgroup.comap_equiv_eq_map_symm',
    AddSubgroup.comap_equiv_eq_map_symm',
    AddSubgroup.relIndex_map_map_of_injective _ _ (Module.finBasis ℝ E).equivFunL.injective]

theorem discreteTopology_of_zsmul {Λ₁ Λ : Submodule ℤ E} [DiscreteTopology Λ₁] {N : ℤ}
    (hN : N ≠ 0) (h : ∀ y ∈ Λ, N • y ∈ Λ₁) : DiscreteTopology Λ := by
  refine DiscreteTopology.of_continuous_injective (β := Λ₁)
    (f := fun y : Λ ↦ (⟨N • (y : E), h y y.2⟩ : Λ₁)) ?_ ?_
  · exact ((continuous_zsmul N).comp continuous_subtype_val).subtype_mk _
  · intro y z hyz
    have h' : N • (y : E) = N • (z : E) := congrArg Subtype.val hyz
    rw [← Int.cast_smul_eq_zsmul ℝ N (y : E), ← Int.cast_smul_eq_zsmul ℝ N (z : E)] at h'
    exact Subtype.ext (smul_right_injective E (Int.cast_ne_zero.mpr hN) h')

theorem tendsto_card_of_le (Λ₁ Λ : Submodule ℤ E) [DiscreteTopology Λ₁] [IsZLattice ℝ Λ₁]
    (hle : Λ₁ ≤ Λ) {N : ℤ} (hN : N ≠ 0) (h : ∀ y ∈ Λ, N • y ∈ Λ₁) {s : Set E}
    (hs₁ : IsBounded s) (hs₂ : MeasurableSet s) (hs₃ : Convex ℝ s) :
    Λ₁.toAddSubgroup.relIndex Λ.toAddSubgroup ≠ 0 ∧
    Tendsto (fun n : ℕ ↦ (Nat.card (s ∩ (n : ℝ)⁻¹ • Λ : Set E) : ℝ) / n ^ finrank ℝ E)
      atTop (𝓝 (μ.real s * (Λ₁.toAddSubgroup.relIndex Λ.toAddSubgroup : ℝ) /
        ZLattice.covolume Λ₁ μ)) := by
  have : DiscreteTopology Λ := discreteTopology_of_zsmul hN h
  have : IsZLattice ℝ Λ := ⟨by
    rw [eq_top_iff, ← IsZLattice.span_top (K := ℝ) (L := Λ₁)]
    exact Submodule.span_mono hle⟩
  have hidx := covolume_div_covolume μ Λ₁ Λ hle
  have h₁ := (ZLattice.covolume_pos Λ₁ μ).ne'
  have h₂ := (ZLattice.covolume_pos Λ μ).ne'
  have hne : (Λ₁.toAddSubgroup.relIndex Λ.toAddSubgroup : ℝ) ≠ 0 := by
    rw [← hidx]
    exact div_ne_zero h₁ h₂
  refine ⟨by exact_mod_cast hne, ?_⟩
  have key := tendsto_card_div_pow Λ μ hs₁ hs₂ (hs₃.addHaar_frontier μ)
  convert key using 2
  rw [← hidx]
  field_simp

end Formalism.HermitianLattices.Ext.L3.BallA
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.FundamentalDomainPiBasis
section
open NumberField NumberField.mixedEmbedding MeasureTheory Module

open scoped Classical

set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.BallC

variable (K : Type*) [Field K] [NumberField K] (ι : Type*) [Fintype ι]

def psi [IsEmpty {w : InfinitePlace K // w.IsReal}] :
    (ι → mixedSpace K) ≃ₗ[ℝ] ({w : InfinitePlace K // w.IsComplex} → ι → ℂ) where
  toFun y := fun w i => (y i).2 w
  invFun z := fun i => (fun w => isEmptyElim w, fun w => z w i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv y := by
    funext i
    exact Prod.ext (Subsingleton.elim _ _) rfl
  right_inv z := rfl

theorem psi_apply [IsEmpty {w : InfinitePlace K // w.IsReal}] (y : ι → mixedSpace K)
    (w : {w : InfinitePlace K // w.IsComplex}) (i : ι) : psi K ι y w i = (y i).2 w := rfl

theorem measurePreserving_psi [IsEmpty {w : InfinitePlace K // w.IsReal}] :
    MeasurePreserving (psi K ι) volume volume := by
  let e := (psi K ι).toContinuousLinearEquiv
  have he : ∀ y, e y = psi K ι y := fun y => rfl
  refine ⟨e.continuous.measurable, ?_⟩
  change Measure.map e volume = volume
  have : (Measure.map e volume).IsAddHaarMeasure := e.isAddHaarMeasure_map volume
  let K₀ : TopologicalSpace.PositiveCompacts
      ({w : InfinitePlace K // w.IsComplex} → ι → ℂ) :=
    ⟨⟨Metric.closedBall 0 1, isCompact_closedBall 0 1⟩, by
      change (interior (Metric.closedBall 0 1)).Nonempty
      rw [interior_closedBall _ one_ne_zero]
      exact ⟨0, Metric.mem_ball_self one_pos⟩⟩
  have hK₀ : (K₀ : Set ({w : InfinitePlace K // w.IsComplex} → ι → ℂ)) = Metric.closedBall 0 1 := rfl
  rw [Measure.addHaarMeasure_unique (Measure.map e volume) K₀,
    Measure.addHaarMeasure_unique (volume : Measure ({w : InfinitePlace K // w.IsComplex} → ι → ℂ)) K₀]
  congr 1
  rw [hK₀, Measure.map_apply e.continuous.measurable Metric.isClosed_closedBall.measurableSet]
  have h1 : e ⁻¹' Metric.closedBall 0 1 = Set.pi Set.univ fun _ : ι =>
      (Set.univ : Set ({w : InfinitePlace K // w.IsReal} → ℝ)) ×ˢ
        Set.pi Set.univ fun _ : {w : InfinitePlace K // w.IsComplex} => Metric.closedBall (0 : ℂ) 1 := by
    ext y
    simp only [Set.mem_preimage, mem_closedBall_zero_iff, he, Set.mem_pi, Set.mem_univ,
      Set.mem_prod, true_and, forall_true_left, pi_norm_le_iff_of_nonneg zero_le_one, psi_apply]
    exact forall_comm
  have h2 : (Metric.closedBall 0 1 : Set ({w : InfinitePlace K // w.IsComplex} → ι → ℂ)) =
      Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Metric.closedBall (0 : ℂ) 1 := by
    ext z
    simp only [mem_closedBall_zero_iff, Set.mem_pi, Set.mem_univ, forall_true_left,
      pi_norm_le_iff_of_nonneg zero_le_one]
  have h3 : volume (Set.univ : Set ({w : InfinitePlace K // w.IsReal} → ℝ)) = 1 := by
    rw [volume_pi, Measure.pi_univ]
    simp
  rw [h1, h2, volume_pi_pi, volume_pi_pi]
  simp only [volume_pi_pi, Measure.volume_eq_prod, Measure.prod_prod, h3, one_mul]
  exact Finset.prod_comm

def piBasis : Basis (Σ _ : ι, Free.ChooseBasisIndex ℤ (𝓞 K)) ℝ (ι → mixedSpace K) :=
  Pi.basis fun _ => latticeBasis K

theorem fundamentalDomain_piBasis : ZSpan.fundamentalDomain (piBasis K ι) =
    Set.pi Set.univ fun _ => ZSpan.fundamentalDomain (latticeBasis K) := by
  ext y
  simp only [ZSpan.mem_fundamentalDomain, Set.mem_pi, Set.mem_univ, true_implies, forall_const, piBasis,
    Pi.basis_repr, Sigma.forall]

theorem mem_span_piBasis (y : ι → mixedSpace K) :
    y ∈ Submodule.span ℤ (Set.range (piBasis K ι)) ↔
      ∀ i, ∃ a : 𝓞 K, mixedEmbedding K (algebraMap (𝓞 K) K a) = y i := by
  simp only [Basis.mem_span_iff_repr_mem ℤ, piBasis, Pi.basis_repr, Sigma.forall]
  refine forall_congr' fun i => ?_
  refine (Basis.mem_span_iff_repr_mem ℤ (latticeBasis K) (y i)).symm.trans ?_
  rw [mem_span_latticeBasis]
  simp [NumberField.mixedEmbedding.integerLattice, LinearMap.mem_range]

theorem covolume_piBasis :
    ZLattice.covolume (Submodule.span ℤ (Set.range (piBasis K ι))) volume =
      ((2⁻¹ : ℝ) ^ InfinitePlace.nrComplexPlaces K * Real.sqrt |(discr K : ℝ)|) ^ Fintype.card ι := by
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ _ (ZSpan.isAddFundamentalDomain (piBasis K ι) volume),
    measureReal_def, fundamentalDomain_piBasis, volume_pi_pi, ENNReal.toReal_prod, Finset.prod_const,
    Finset.card_univ, ← measureReal_def,
    ← ZLattice.covolume_eq_measure_fundamentalDomain _ _ (ZSpan.isAddFundamentalDomain (latticeBasis K) volume),
    span_latticeBasis, covolume_integerLattice]

end Formalism.HermitianLattices.Ext.L3.BallC
end
end

