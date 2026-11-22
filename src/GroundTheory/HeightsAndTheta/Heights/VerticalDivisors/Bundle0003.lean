import Mathlib
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle0002

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PChartTorsion
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

namespace ChartTorsion

variable {D : Type} [CommRing D] {n : ℕ} (k : ℕ) (P : Ideal (MvPolynomial (Fin n) D)) (j : Fin n)

abbrev Base := Localization.Away (Ideal.Quotient.mk P (X j))

def toBase : MvPolynomial (Fin n) D →+* Base P j :=
  (algebraMap (MvPolynomial (Fin n) D ⧸ P) (Base P j)).comp (Ideal.Quotient.mk P)

def solve (i : Fin k) (m : Fin n) : MvPolynomial (Fin k × Fin n) (Base P j) :=
  if m = j then
    -(C (IsLocalization.Away.invSelf (Ideal.Quotient.mk P (X j))) *
      ∑ l ∈ Finset.univ.erase j, C (toBase P j (X l)) * X (i, l))
  else X (i, m)

def toChart : MvPolynomial (Fin n ⊕ (Fin k × Fin n)) D →+* MvPolynomial (Fin k × Fin n) (Base P j) :=
  eval₂Hom (C.comp ((toBase P j).comp C))
    (Sum.elim (fun m => C (toBase P j (X m))) (fun im => solve k P j im.1 im.2))

theorem toChart_rename (p : MvPolynomial (Fin n) D) :
    toChart k P j (rename Sum.inl p) = C (toBase P j p) := by
  induction p using MvPolynomial.induction_on with
  | C d => simp [toChart]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p m hp => simp only [map_mul, hp, rename_X]; simp [toChart]

theorem incIdeal_le_ker : incIdeal P k ≤ RingHom.ker (toChart k P j) := by
  refine sup_le (Ideal.map_le_iff_le_comap.2 fun p hp => ?_)
    (Ideal.span_le.2 (Set.range_subset_iff.2 fun i => ?_))
  · show toChart k P j (rename Sum.inl p) = 0
    rw [toChart_rename]
    simp [toBase, Ideal.Quotient.eq_zero_iff_mem.2 hp]
  · show toChart k P j _ = 0
    simp only [map_sum, map_mul]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    have hs : ∀ l ∈ Finset.univ.erase j,
        toChart k P j (X (Sum.inr (i, l))) * toChart k P j (X (Sum.inl l)) =
          C (toBase P j (X l)) * X (i, l) := by
      intro l hl
      simp [toChart, solve, Finset.ne_of_mem_erase hl, mul_comm]
    rw [Finset.sum_congr rfl hs]
    have h1 : C (IsLocalization.Away.invSelf (Ideal.Quotient.mk P (X j))) * C (toBase P j (X j)) =
        (1 : MvPolynomial (Fin k × Fin n) (Base P j)) := by
      rw [← C_mul, mul_comm, toBase, RingHom.comp_apply, IsLocalization.Away.mul_invSelf, C_1]
    simp only [toChart, eval₂Hom_X', Sum.elim_inl, Sum.elim_inr, solve, ↓reduceIte]
    linear_combination (-(∑ l ∈ Finset.univ.erase j, C (toBase P j (X l)) * X (i, l))) * h1

abbrev Loc := Localization.Away (Ideal.Quotient.mk (incIdeal P k) (X (Sum.inl j)))

def toLoc : MvPolynomial (Fin n ⊕ (Fin k × Fin n)) D →+* Loc k P j :=
  (algebraMap _ (Loc k P j)).comp (Ideal.Quotient.mk (incIdeal P k))

theorem toLoc_mem {g : MvPolynomial (Fin n ⊕ (Fin k × Fin n)) D} (hg : g ∈ incIdeal P k) :
    toLoc k P j g = 0 := by
  simp [toLoc, Ideal.Quotient.eq_zero_iff_mem.2 hg]

def quotToLoc : MvPolynomial (Fin n) D ⧸ P →+* Loc k P j :=
  Ideal.Quotient.lift P ((toLoc k P j).comp (rename Sum.inl).toRingHom) fun _ hp =>
    toLoc_mem k P j (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hp))

theorem quotToLoc_mk (p : MvPolynomial (Fin n) D) :
    quotToLoc k P j (Ideal.Quotient.mk P p) = toLoc k P j (rename Sum.inl p) := rfl

theorem isUnit_quotToLoc : IsUnit (quotToLoc k P j (Ideal.Quotient.mk P (X j))) := by
  rw [quotToLoc_mk, rename_X]
  exact IsLocalization.Away.algebraMap_isUnit (Ideal.Quotient.mk (incIdeal P k) (X (Sum.inl j)))

def baseToLoc : Base P j →+* Loc k P j :=
  IsLocalization.Away.lift _ (isUnit_quotToLoc k P j)

theorem baseToLoc_toBase (p : MvPolynomial (Fin n) D) :
    baseToLoc k P j (toBase P j p) = toLoc k P j (rename Sum.inl p) := by
  simp [baseToLoc, toBase, quotToLoc_mk]

def back : MvPolynomial (Fin k × Fin n) (Base P j) →+* Loc k P j :=
  eval₂Hom (baseToLoc k P j) fun im => toLoc k P j (X (Sum.inr im))

theorem back_toChart (g : MvPolynomial (Fin n ⊕ (Fin k × Fin n)) D) :
    back k P j (toChart k P j g) = toLoc k P j g := by
  suffices h : (back k P j).comp (toChart k P j) = toLoc k P j from congrArg (· g) h
  apply MvPolynomial.ringHom_ext
  · intro d
    have := baseToLoc_toBase k P j (C d)
    simpa [back, toChart] using this
  · rintro (m | ⟨i, m⟩)
    · have := baseToLoc_toBase k P j (X m)
      simpa [back, toChart] using this
    · by_cases hm : m = j
      · subst hm
        have hinc : toLoc k P m (∑ l, X (Sum.inr (i, l)) * X (Sum.inl l)) = 0 :=
          toLoc_mem k P m (Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩))
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ m), map_add, map_sum] at hinc
        have hinv : baseToLoc k P m (IsLocalization.Away.invSelf (Ideal.Quotient.mk P (X m))) *
            toLoc k P m (X (Sum.inl m)) = 1 := by
          have e := baseToLoc_toBase k P m (X m)
          rw [rename_X] at e
          rw [← e, toBase, RingHom.comp_apply, ← map_mul, mul_comm, IsLocalization.Away.mul_invSelf,
            map_one]
        simp only [RingHom.comp_apply, toChart, eval₂Hom_X', Sum.elim_inr, solve, ↓reduceIte,
          back, map_neg, map_mul, map_sum, eval₂Hom_C, eval₂Hom_X', baseToLoc_toBase, rename_X]
        simp only [map_mul] at hinc
        set u := toLoc k P m (X (Sum.inr (i, m)))
        set xm := toLoc k P m (X (Sum.inl m))
        set inv := baseToLoc k P m (IsLocalization.Away.invSelf (Ideal.Quotient.mk P (X m)))
        have hS : ∑ l ∈ Finset.univ.erase m, toLoc k P m (X (Sum.inl l)) *
              toLoc k P m (X (Sum.inr (i, l))) =
            ∑ l ∈ Finset.univ.erase m, toLoc k P m (X (Sum.inr (i, l))) *
              toLoc k P m (X (Sum.inl l)) :=
          Finset.sum_congr rfl fun _ _ => mul_comm _ _
        rw [hS]
        linear_combination (-inv) * hinc + u * hinv
      · simp [back, toChart, solve, hm]

end ChartTorsion

open ChartTorsion in

theorem ChartTorsion.proof : ChartTorsion.Statement := by
  intro D _ _ n k P hP hPD c g hc hcg j
  by_cases hj : (X j : MvPolynomial (Fin n) D) ∈ P
  · refine ⟨1, Ideal.mul_mem_right _ _ (Ideal.mem_sup_left ?_)⟩
    simpa using Ideal.mem_map_of_mem (rename (R := D) (Sum.inl (β := Fin k × Fin n))) hj
  have hx : Ideal.Quotient.mk P (X j) ≠ 0 := fun h => hj (Ideal.Quotient.eq_zero_iff_mem.1 h)
  have hle : Submonoid.powers (Ideal.Quotient.mk P (X j)) ≤ nonZeroDivisors _ :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hx
  have : IsDomain (Base P j) := IsLocalization.isDomain_localization hle
  have hcz : toChart k P j (C c) ≠ 0 := by
    simp only [toChart, eval₂Hom_C, RingHom.comp_apply, ne_eq, C_eq_zero, toBase]
    rw [map_eq_zero_iff _ (IsLocalization.injective (Base P j) hle)]
    intro h
    exact hc (hPD c (Ideal.Quotient.eq_zero_iff_mem.1 h))
  have hg0 : toChart k P j g = 0 := by
    have h := incIdeal_le_ker k P j hcg
    rw [RingHom.mem_ker, map_mul] at h
    exact (mul_eq_zero.1 h).resolve_left hcz
  have hl : toLoc k P j g = 0 := by
    rw [← back_toChart, hg0, map_zero]
  obtain ⟨⟨_, N, rfl⟩, hN⟩ := (IsLocalization.map_eq_zero_iff
    (Submonoid.powers (Ideal.Quotient.mk (incIdeal P k) (X (Sum.inl j)))) _ _).1 hl
  refine ⟨N, Ideal.Quotient.eq_zero_iff_mem.1 ?_⟩
  simpa [map_mul, map_pow] using hN

end

end GroundTheory.Heights₂.Heights.Vertical
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PIncidenceNull
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

theorem IncidenceNull.proof : IncidenceNull.Statement := by
  intro F _ n k I f hf
  have hvan : ∀ j : Fin n, rename Sum.inr f * X (Sum.inl j) ∈
      MvPolynomial.vanishingIdeal F
        (MvPolynomial.zeroLocus (AlgebraicClosure F) (incIdeal I k)) := by
    intro j z hz
    have hI : ∀ g ∈ I, aeval (z ∘ Sum.inl) g = 0 := by
      intro g hg
      have hmem : rename Sum.inl g ∈ incIdeal I k :=
        Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hg)
      have h := hz _ hmem
      rwa [aeval_rename] at h
    have hlin : ∀ i : Fin k, ∑ j, (z ∘ Sum.inr) (i, j) * (z ∘ Sum.inl) j = 0 := by
      intro i
      have hmem : (∑ j, X (Sum.inr (i, j)) * X (Sum.inl j) :
          MvPolynomial (Fin n ⊕ (Fin k × Fin n)) F) ∈ incIdeal I k :=
        Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩)
      have h := hz _ hmem
      simpa using h
    rw [map_mul, aeval_rename, aeval_X]
    by_cases hx : z ∘ Sum.inl = 0
    · have h0 : z (Sum.inl j) = 0 := congrFun hx j
      rw [h0, mul_zero]
    · have hu : z ∘ Sum.inr ∈ incidence I k := ⟨z ∘ Sum.inl, hx, hI, hlin⟩
      rw [(hf.2 f).2 dvd_rfl _ hu, zero_mul]
  have hrad : ∀ j : Fin n, ∃ m, (rename Sum.inr f * X (Sum.inl j)) ^ m ∈ incIdeal I k := by
    intro j
    have h := hvan j
    rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical] at h
    exact h
  choose m hm using hrad
  exact ⟨Finset.univ.sup m, fun j =>
    Ideal.pow_mem_of_pow_mem _ (hm j) (Finset.le_sup (Finset.mem_univ j))⟩

end GroundTheory.Heights₂.Heights.Vertical
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PLengthDecomp
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open Module IsLocalRing LinearMap Submodule

noncomputable section

namespace LengthDecomp

open Classical

variable {B : Type*} [CommRing B]

theorem length_localizedModule_eq_of_isLocalizedModule (p : Ideal B) [p.IsPrime]
    {X Y : Type*} [AddCommGroup X] [Module B X] [AddCommGroup Y] [Module B Y]
    [Module (Localization.AtPrime p) Y] [IsScalarTower B (Localization.AtPrime p) Y]
    (g : X →ₗ[B] Y) [IsLocalizedModule p.primeCompl g] :
    length (Localization.AtPrime p) (LocalizedModule p.primeCompl X) =
      length (Localization.AtPrime p) Y :=
  ((IsLocalizedModule.iso p.primeCompl g).extendScalarsOfIsLocalization p.primeCompl
    (Localization.AtPrime p)).length_eq

theorem length_localizedModule_quotient (n m : MaximalSpectrum B) :
    length (Localization.AtPrime n.asIdeal) (LocalizedModule n.asIdeal.primeCompl (B ⧸ m.asIdeal)) =
      if n = m then 1 else 0 := by
  have hn := n.isMaximal
  have hm := m.isMaximal
  split_ifs with h
  · subst h
    rw [length_localizedModule_eq_of_isLocalizedModule n.asIdeal
      (n.asIdeal.toLocalizedQuotient' (Localization.AtPrime n.asIdeal) n.asIdeal.primeCompl
        (Algebra.linearMap B (Localization.AtPrime n.asIdeal)))]
    have hmax : n.asIdeal.localized' (Localization.AtPrime n.asIdeal) n.asIdeal.primeCompl
        (Algebra.linearMap B (Localization.AtPrime n.asIdeal)) =
          maximalIdeal (Localization.AtPrime n.asIdeal) := by
      rw [Submodule.localized'_eq_span, ← Localization.AtPrime.map_eq_maximalIdeal]
      rfl
    rw [hmax]
    have : IsSimpleModule (Localization.AtPrime n.asIdeal)
        (Localization.AtPrime n.asIdeal ⧸ maximalIdeal (Localization.AtPrime n.asIdeal)) :=
      isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp inferInstance)
    exact Module.length_eq_one _ _
  · rw [Module.length_eq_zero_iff, LocalizedModule.subsingleton_iff]
    obtain ⟨s, hsm, hsn⟩ : ∃ s ∈ m.asIdeal, s ∉ n.asIdeal := by
      by_contra! hc
      exact h (MaximalSpectrum.ext (hm.eq_of_le hn.ne_top hc).symm)
    intro x
    refine ⟨s, hsn, ?_⟩
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.mpr hsm,
      zero_mul]

variable {R : Type*} [CommRing R] [Algebra R B]
variable {N : Type*} [AddCommGroup N] [Module B N] [Module R N] [IsScalarTower R B N]

theorem step {p q : Submodule B N} (h : p ⋖ q) :
    ∃ m : MaximalSpectrum B, length R q = length R p + length R (B ⧸ m.asIdeal) ∧
      ∀ n : MaximalSpectrum B,
        length (Localization.AtPrime n.asIdeal) (LocalizedModule n.asIdeal.primeCompl q) =
          length (Localization.AtPrime n.asIdeal) (LocalizedModule n.asIdeal.primeCompl p) +
            if n = m then 1 else 0 := by
  let f : p →ₗ[B] q := inclusion h.le
  have key : IsSimpleModule B (q ⧸ range f) := by
    rwa [range_inclusion, ← covBy_iff_quot_is_simple h.le]
  obtain ⟨m, hm, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp key
  let g : q →ₗ[B] B ⧸ m := e.toLinearMap.comp (range f).mkQ
  have hf : Function.Injective f := inclusion_injective _
  have hg : Function.Surjective g := e.surjective.comp (range f).mkQ_surjective
  have hfg : Function.Exact f g := exact_iff.mpr ((e.ker_comp _).trans (range f).ker_mkQ)
  refine ⟨⟨m, hm⟩, length_eq_add_of_exact (f.restrictScalars R) (g.restrictScalars R) hf hg hfg,
    fun n => ?_⟩
  rw [← length_localizedModule_quotient n ⟨m, hm⟩]
  exact length_eq_add_of_exact
    ((IsLocalizedModule.map n.asIdeal.primeCompl (LocalizedModule.mkLinearMap _ p)
      (LocalizedModule.mkLinearMap _ q) f).extendScalarsOfIsLocalization n.asIdeal.primeCompl
        (Localization.AtPrime n.asIdeal))
    ((IsLocalizedModule.map n.asIdeal.primeCompl (LocalizedModule.mkLinearMap _ q)
      (LocalizedModule.mkLinearMap _ (B ⧸ m)) g).extendScalarsOfIsLocalization
        n.asIdeal.primeCompl (Localization.AtPrime n.asIdeal))
    (IsLocalizedModule.map_injective _ _ _ f hf) (IsLocalizedModule.map_surjective _ _ _ g hg)
    (LocalizedModule.map_exact _ f g hfg)

theorem length_eq_sum [Fintype (MaximalSpectrum B)] (hN : IsFiniteLength B N) :
    length R N = ∑ n : MaximalSpectrum B,
      length (Localization.AtPrime n.asIdeal) (LocalizedModule n.asIdeal.primeCompl N) *
        length R (B ⧸ n.asIdeal) := by
  obtain ⟨s, hs_bot, hs_top⟩ := isFiniteLength_iff_exists_compositionSeries.mp hN
  have H : ∀ k, length R (s k) = ∑ n : MaximalSpectrum B,
      length (Localization.AtPrime n.asIdeal) (LocalizedModule n.asIdeal.primeCompl (s k)) *
        length R (B ⧸ n.asIdeal) := by
    intro k
    induction k using Fin.induction with
    | zero =>
      rw [← RelSeries.head, hs_bot]
      simp [Module.length_eq_zero]
    | succ i hi =>
      obtain ⟨m, h1, h2⟩ := step (R := R) (s.step i)
      rw [h1, hi]
      simp_rw [h2, add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have := H (Fin.last _)
  rw [← RelSeries.last, hs_top] at this
  rw [← ((Submodule.topEquiv (R := B) (M := N)).restrictScalars R).length_eq, this]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [length_localizedModule_eq_of_isLocalizedModule n.asIdeal
    ((LocalizedModule.mkLinearMap n.asIdeal.primeCompl N).comp
      (Submodule.topEquiv (R := B) (M := N)).toLinearMap)]

theorem finite_maximalSpectrum [IsLocalRing R] [Module.Finite R B] :
    Finite (MaximalSpectrum B) := by
  have hfin := Algebra.QuasiFinite.finite_primesOver (R := R) (S := B) (maximalIdeal R)
  have := hfin.to_subtype
  refine Finite.of_injective (β := (maximalIdeal R).primesOver B)
    (fun n => ⟨n.asIdeal, n.isMaximal.isPrime, ⟨(IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := R) n.asIdeal)).symm⟩⟩) ?_
  intro n n' hnn'
  exact MaximalSpectrum.ext (congrArg Subtype.val hnn')

end LengthDecomp

theorem LengthDecomp.proof : LengthDecomp.Statement := by
  intro R B _ _ _ _ _ _ b hfin
  have := LengthDecomp.finite_maximalSpectrum (R := R) (B := B)
  let _ : Fintype (MaximalSpectrum B) := Fintype.ofFinite _
  have hB : IsFiniteLength B (B ⧸ Ideal.span {b}) := by
    rw [length_ne_top_iff, isFiniteLength_iff_isNoetherian_isArtinian] at hfin
    rw [isFiniteLength_iff_isNoetherian_isArtinian]
    exact hfin.imp (isNoetherian_of_tower R) (isArtinian_of_tower R)
  rw [LengthDecomp.length_eq_sum (R := R) hB, finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun n _ => ?_
  congr 1
  have hspan : (Ideal.span {b}).localized' (Localization.AtPrime n.asIdeal) n.asIdeal.primeCompl
      (Algebra.linearMap B (Localization.AtPrime n.asIdeal)) =
        Ideal.span {algebraMap B (Localization.AtPrime n.asIdeal) b} := by
    rw [Ideal.span, Submodule.localized'_span, Set.image_singleton]
    rfl
  rw [Ring.ord, LengthDecomp.length_localizedModule_eq_of_isLocalizedModule n.asIdeal
    ((Ideal.span {b}).toLocalizedQuotient' (Localization.AtPrime n.asIdeal) n.asIdeal.primeCompl
      (Algebra.linearMap B (Localization.AtPrime n.asIdeal))), hspan]

end

end GroundTheory.Heights₂.Heights.Vertical
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PNormFormEval
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial TensorProduct

noncomputable section

attribute [local instance] MvPolynomial.algebraMvPolynomial

section Basis

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {n : ℕ}

def polyTensorAlgEquiv (R A : Type*) [CommRing R] [CommRing A] [Algebra R A] (n : ℕ) :
    (MvPolynomial (Fin n) R ⊗[R] A) ≃ₐ[R] MvPolynomial (Fin n) A :=
  (Algebra.TensorProduct.comm R (MvPolynomial (Fin n) R) A).trans
    ((algebraTensorAlgEquiv R A).restrictScalars R)

theorem polyTensorAlgEquiv_tmul (p : MvPolynomial (Fin n) R) (a : A) :
    polyTensorAlgEquiv R A n (p ⊗ₜ a) = a • MvPolynomial.map (algebraMap R A) p := by
  simp [polyTensorAlgEquiv]

def polyTensorEquiv (R A : Type*) [CommRing R] [CommRing A] [Algebra R A] (n : ℕ) :
    (MvPolynomial (Fin n) R ⊗[R] A) ≃ₗ[MvPolynomial (Fin n) R] MvPolynomial (Fin n) A where
  toFun := polyTensorAlgEquiv R A n
  invFun := (polyTensorAlgEquiv R A n).symm
  map_add' := map_add _
  left_inv := (polyTensorAlgEquiv R A n).symm_apply_apply
  right_inv := (polyTensorAlgEquiv R A n).apply_symm_apply
  map_smul' q t := by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul p a =>
      rw [smul_tmul', smul_eq_mul, polyTensorAlgEquiv_tmul, polyTensorAlgEquiv_tmul, RingHom.id_apply,
        Algebra.smul_def q, MvPolynomial.algebraMap_def, map_mul, mul_smul_comm]
    | add s t hs ht =>
      rw [smul_add, map_add, map_add, hs, ht, smul_add]

def polyBasis {ι : Type*} (b : Module.Basis ι R A) (n : ℕ) :
    Module.Basis ι (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) A) :=
  (Algebra.TensorProduct.basis (MvPolynomial (Fin n) R) b).map (polyTensorEquiv R A n)

theorem polyBasis_apply {ι : Type*} (b : Module.Basis ι R A) (n : ℕ) (i : ι) :
    polyBasis b n i = C (b i) := by
  simp [polyBasis, polyTensorEquiv, Algebra.TensorProduct.basis_apply, polyTensorAlgEquiv_tmul,
    smul_eq_C_mul]

end Basis

theorem normForm_eq_det {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {n : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R A) (x : Fin n → A) :
    normForm A x = (∑ j, (X j : MvPolynomial (Fin n) R) • (Algebra.leftMulMatrix b (x j)).map C).det := by
  let bP := polyBasis b n
  let M : Fin n → Matrix ι ι R := fun j => Algebra.leftMulMatrix b (x j)
  have hM : ∀ j k, x j * b k = ∑ i, M j i k • b i := fun j k => by
    simp only [M, Algebra.leftMulMatrix_eq_repr_mul]
    exact (b.sum_repr (x j * b k)).symm
  have key : ∀ (q : MvPolynomial (Fin n) R) (a : A),
      q • (C a : MvPolynomial (Fin n) A) = MvPolynomial.map (algebraMap R A) q * C a := fun q a => by
    rw [Algebra.smul_def, MvPolynomial.algebraMap_def]
  have hmat : Algebra.leftMulMatrix bP (∑ j, X j * C (x j) : MvPolynomial (Fin n) A) =
      ∑ j, (X j : MvPolynomial (Fin n) R) • (M j).map C := by
    refine Matrix.ext fun i k => ?_
    rw [Algebra.leftMulMatrix_eq_repr_mul, polyBasis_apply]
    have hsum : (∑ j, X j * C (x j) : MvPolynomial (Fin n) A) * C (b k) =
        ∑ i', (∑ j, (X j : MvPolynomial (Fin n) R) * C (M j i' k)) • bP i' := by
      calc (∑ j, X j * C (x j) : MvPolynomial (Fin n) A) * C (b k)
          = ∑ j, ∑ i', (X j : MvPolynomial (Fin n) A) * C (M j i' k • b i') := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [mul_assoc, ← C_mul, hM j k, map_sum, Finset.mul_sum]
        _ = ∑ i', ∑ j, (X j : MvPolynomial (Fin n) A) * C (M j i' k • b i') := Finset.sum_comm
        _ = ∑ i', (∑ j, (X j : MvPolynomial (Fin n) R) * C (M j i' k)) • bP i' := by
            refine Finset.sum_congr rfl fun i' _ => ?_
            rw [polyBasis_apply, key, map_sum, Finset.sum_mul]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [map_mul, map_X, map_C, Algebra.smul_def, C_mul, mul_assoc]
    rw [hsum, bP.repr_sum_self, Matrix.sum_apply]
    simp [Matrix.map_apply]
  rw [normForm, Algebra.norm_eq_matrix_det bP, hmat]

theorem NormFormEval.proof : NormFormEval.Statement := by
  intro R A _ _ _ _ _ n x u
  classical
  let b := Module.Free.chooseBasis R A
  let M : Fin n → Matrix (Module.Free.ChooseBasisIndex R A) (Module.Free.ChooseBasisIndex R A) R :=
    fun j => Algebra.leftMulMatrix b (x j)
  rw [normForm_eq_det b, RingHom.map_det]
  have hev : (MvPolynomial.eval u).mapMatrix (∑ j, (X j : MvPolynomial (Fin n) R) • (M j).map C) =
      Algebra.leftMulMatrix b (∑ j, algebraMap R A (u j) * x j) := by
    ext i k
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply,
      smul_eq_mul, map_sum, map_mul, eval_X, eval_C, M]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.one_mul,
      Matrix.smul_apply, smul_eq_mul]
  rw [hev, ← Algebra.norm_eq_matrix_det b]

end

end GroundTheory.Heights₂.Heights.Vertical
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsOrd
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

noncomputable section

def FiniteOrd.Statement : Prop :=
  ∀ (R B : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing B] [Algebra R B]
    [Module.Finite R B] (b : B), Function.Injective (fun x : B => b * x) →
      ∀ 𝔫 : MaximalSpectrum B,
        Ring.ord (Localization.AtPrime 𝔫.asIdeal) (algebraMap B (Localization.AtPrime 𝔫.asIdeal) b) ≠ ⊤

end

end GroundTheory.Heights₂.Heights.Vertical
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsSpecFirst
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

def SpecFirstNeField.Statement : Prop :=
  ∀ (F : Type) [Field F] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) (u : Fin n → F),
    IsProjPrime I → IsChowForm I (e + 1) f → linForm u ∉ I → specFirst f u ≠ 0

end

end GroundTheory.Heights₂.Heights.Vertical
end

