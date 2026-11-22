import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfForallMemFilV
import ReciprocityTheory.DualLattices.Bundle0018
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0127
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0079
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0116
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0032
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0119
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0085
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0120
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0098
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.CoboundaryTransfers.Statement
import Formalism.WeaklyAdmissibleFiltrations.Statement
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.PointRingCommRing
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.LocalRingStructure
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0121
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0122
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0065

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankMulLeFinrankDdROfSpans
section
noncomputable section

namespace GlobalTheory.DRFil

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct Module

theorem finrank_le_of_span_subspace {K F M : Type} [Field K] [CommRing F] [Nontrivial F] [Algebra K F]
    [AddCommGroup M] [Module K M] [Module F M] [IsScalarTower K F M] (D : Submodule K M)
    [FiniteDimensional K D] (h : Submodule.span F (D : Set M) = ⊤) :
    finrank F M ≤ finrank K D := by
  classical
  let bD := Module.finBasis K D
  let s : Finset M := Finset.univ.image fun i => ((bD i : D) : M)
  have hs : Submodule.span F (s : Set M) = ⊤ := by
    rw [eq_top_iff, ← h, Submodule.span_le]
    intro x hx
    have hx' := congrArg Subtype.val (bD.sum_repr ⟨x, hx⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hx'
    rw [← hx']
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← algebraMap_smul F]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp [s]))
  calc finrank F M = finrank F (⊤ : Submodule F M) := (finrank_top F M).symm
    _ = finrank F (Submodule.span F (s : Set M)) := by rw [hs]
    _ ≤ s.card := finrank_span_finset_le_card s
    _ ≤ (Finset.univ : Finset (Fin (finrank K D))).card := Finset.card_image_le
    _ = finrank K D := by simp

theorem finrank_mul_le_finrank_DdR_of_spans {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B F : Type} [CommRing B] [CommRing F]
    [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp F] [Algebra K₀ F] [Algebra K F]
    [IsScalarTower Qp K F] [IsScalarTower K₀ K F] [IsScalarTower Qp K₀ F] (PD : PeriodData G Qp K₀ K B F)
    {LL : Type} [Field LL] [Algebra Qp LL] [FiniteDimensional Qp LL] [FiniteDimensional Qp K] [CharZero Qp]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] [FiniteDimensional LL V]
    (ρ : Representation LL G V) (hfin : FiniteDimensional LL ↥(DdR PD ρ)) (hs : Spans PD ρ) :
    Module.finrank Qp K * Module.finrank LL V ≤ Module.finrank LL ↥(DdR PD ρ) := by
  classical
  haveI : Nontrivial F := by
    refine nontrivial_of_ne (PD.ι PD.t) 0 fun h0 => PD.not_mem_filtration_two ?_
    rw [h0]
    exact (PD.Fil 2).zero_mem
  unfold Spans mulR at hs
  set W := DdR PD ρ with hW
  let e : V ⊗[Qp] F ≃ₗ[Qp] F ⊗[Qp] V := TensorProduct.comm Qp V F

  have he : ∀ (b : F) (x : V ⊗[Qp] F),
      e (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (LinearMap.mulLeft Qp b) x) = b • e x := by
    intro b x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v y => simp [e, TensorProduct.smul_tmul']
    | add x y hx hy => simp only [map_add, smul_add, hx, hy]

  have hK : ∀ (c : K) (x : V ⊗[Qp] F), x ∈ W →
      AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (LinearMap.mulLeft Qp (algebraMap K F c)) x ∈ W := by
    intro c x hx
    simp only [hW, DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero] at hx ⊢
    intro g
    have hcomm : ∀ y : V ⊗[Qp] F, actVdR PD ρ g
        (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (LinearMap.mulLeft Qp (algebraMap K F c)) y) =
        AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (LinearMap.mulLeft Qp (algebraMap K F c))
          (actVdR PD ρ g y) := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul v z => simp [actVdR]
      | add y y' hy hy' => simp only [map_add, hy, hy']
    rw [hcomm, hx g]

  let D' : Submodule K (F ⊗[Qp] V) :=
    { carrier := e '' (W : Set (V ⊗[Qp] F))
      add_mem' := by
        rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
        exact ⟨x + y, W.add_mem hx hy, map_add e x y⟩
      zero_mem' := ⟨0, W.zero_mem, map_zero e⟩
      smul_mem' := by
        rintro c _ ⟨x, hx, rfl⟩
        refine ⟨_, hK c x hx, ?_⟩
        rw [he, algebraMap_smul] }
  have hspan : Submodule.span F (D' : Set (F ⊗[Qp] V)) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨m, b, d, hd, hy⟩ := hs (e.symm y)
    have hy' : y = ∑ i, b i • e (d i) := by
      rw [← e.apply_symm_apply y, hy, map_sum]
      simp only [he]
    rw [hy']
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span (show e (d i) ∈ (D' : Set (F ⊗[Qp] V)) from ⟨d i, hd i, rfl⟩))
  haveI : FiniteDimensional LL W := hfin
  haveI : FiniteDimensional Qp W := Module.Finite.trans LL W
  let φ : W ≃ₗ[Qp] D' :=
    LinearEquiv.ofBijective
      ({ toFun := fun w => ⟨e (w : V ⊗[Qp] F), (w : V ⊗[Qp] F), w.2, rfl⟩
         map_add' := fun x y => Subtype.ext (map_add e (x : V ⊗[Qp] F) y)
         map_smul' := fun a x => Subtype.ext (map_smul e a (x : V ⊗[Qp] F)) } : W →ₗ[Qp] D')
      ⟨fun x y hxy => Subtype.ext (e.injective (congrArg Subtype.val hxy)),
        by rintro ⟨_, w, hw, rfl⟩; exact ⟨⟨w, hw⟩, rfl⟩⟩
  haveI : FiniteDimensional Qp D' := Module.Finite.equiv φ
  haveI : FiniteDimensional K D' := Module.Finite.of_restrictScalars_finite Qp K D'
  have h1 := finrank_le_of_span_subspace D' hspan
  rw [Module.finrank_baseChange] at h1
  have h2 : finrank Qp K * finrank K D' = finrank Qp LL * finrank LL W := by
    rw [Module.finrank_mul_finrank, ← φ.finrank_eq, Module.finrank_mul_finrank]
  have h3 : finrank Qp LL * finrank LL V = finrank Qp V := Module.finrank_mul_finrank _ _ _
  have hpos : 0 < finrank Qp LL := Module.finrank_pos
  have key : finrank Qp LL * (finrank Qp K * finrank LL V) ≤ finrank Qp LL * finrank LL W :=
    calc finrank Qp LL * (finrank Qp K * finrank LL V)
        = finrank Qp K * finrank Qp V := by rw [← h3]; ring
      _ ≤ finrank Qp K * finrank K D' := Nat.mul_le_mul_left _ h1
      _ = finrank Qp LL * finrank LL W := h2
  exact Nat.le_of_mul_le_mul_left key hpos

end GlobalTheory.DRFil
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FisSelfReNonneg
section
noncomputable section

open MvPolynomial

namespace GlobalTheory.FockIsotypic

variable {σ : Type} [Fintype σ]

def flat (σ : Type) [Fintype σ] : σ ≃ Fin (Fintype.card σ) × Unit :=
  (Fintype.equivFin σ).trans (Equiv.prodPUnit _).symm

def fis (P Q : MvPolynomial σ ℂ) : ℂ :=
  ReciprocityTheory.PGsh.fischer (rename (flat σ) P) (rename (flat σ) Q)

theorem fis_conj (P Q : MvPolynomial σ ℂ) : starRingEnd ℂ (fis P Q) = fis Q P := by
  classical
  unfold fis
  set P' := rename (flat σ) P
  set Q' := rename (flat σ) Q
  rw [ReciprocityTheory.PGsh.fischer_eq_sum P' Q' (P'.support ∪ Q'.support) Finset.subset_union_left,
    ReciprocityTheory.PGsh.fischer_eq_sum Q' P' (P'.support ∪ Q'.support) Finset.subset_union_right, map_sum]
  refine Finset.sum_congr rfl fun A _ => ?_
  simp only [ReciprocityTheory.PGsh.fw, map_mul, Complex.conj_conj, map_natCast]
  ring

theorem fis_self_re_nonneg (P : MvPolynomial σ ℂ) : 0 ≤ (fis P P).re := by
  classical
  unfold fis
  set P' := rename (flat σ) P
  rw [ReciprocityTheory.PGsh.fischer_eq_sum P' P' P'.support subset_rfl, Complex.re_sum]
  refine Finset.sum_nonneg fun A _ => ?_
  rw [Complex.mul_conj, ReciprocityTheory.PGsh.fw, ← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.ofReal_re]
  exact mul_nonneg (Complex.normSq_nonneg _) (Nat.cast_nonneg _)

theorem fis_self_ne_zero {P : MvPolynomial σ ℂ} (hP : P ≠ 0) : fis P P ≠ 0 :=
  ReciprocityTheory.PGsh.fischer_self_ne_zero _ fun h =>
    hP (rename_injective _ (flat σ).injective (h.trans (map_zero _).symm))

theorem fis_add_right (P Q Q' : MvPolynomial σ ℂ) : fis P (Q + Q') = fis P Q + fis P Q' := by
  unfold fis
  rw [map_add, ReciprocityTheory.PGsh.fischer_add_right]

theorem fis_smul_right (c : ℂ) (P Q : MvPolynomial σ ℂ) : fis P (c • Q) = starRingEnd ℂ c * fis P Q := by
  unfold fis
  rw [map_smul, ReciprocityTheory.PGsh.fischer_smul_right]

theorem fis_add_left (P P' Q : MvPolynomial σ ℂ) : fis (P + P') Q = fis P Q + fis P' Q := by
  unfold fis
  rw [map_add, ReciprocityTheory.PGsh.fischer_add_left]

theorem fis_smul_left (c : ℂ) (P Q : MvPolynomial σ ℂ) : fis (c • P) Q = c * fis P Q := by
  unfold fis
  rw [map_smul, ReciprocityTheory.PGsh.fischer_smul_left]

@[reducible] def fisCore (S : Submodule ℂ (MvPolynomial σ ℂ)) : InnerProductSpace.Core ℂ S where
  inner x y := fis y.1 x.1
  conj_inner_symm x y := fis_conj _ _
  re_inner_nonneg x := fis_self_re_nonneg _
  add_left x y z := fis_add_right _ _ _
  smul_left x y r := fis_smul_right _ _ _
  definite x hx := by
    by_contra h
    exact fis_self_ne_zero (fun h' => h (Subtype.ext h')) hx

end GlobalTheory.FockIsotypic

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FourierIndicatorHermitianIntegralLattice
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR

theorem fourB_indicator_intLattice : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (r : ℕ) (j : A.L ≃ₗ[E] (Fin r → E)) (B : A.L → A.L → ℂ), (∀ y' y, B y' y = ψ (Algebra.trace F E (star (j y') ⬝ᵥ j y))) → IsOpen {y : A.L | ∀ i, ‖j y i‖ ≤ 1} → IsCompact {y : A.L | ∀ i, ‖j y i‖ ≤ 1} → ∀ μ : Measure A.L, μ.IsAddHaarMeasure → ∀ y, fourB μ B (Set.indicator {y : A.L | ∀ i, ‖j y i‖ ≤ 1} 1) y = ((μ {y : A.L | ∀ i, ‖j y i‖ ≤ 1}).toReal : ℂ) * Set.indicator {y : A.L | ∀ i, ‖j y i‖ ≤ 1} 1 y := by
  intro F E _ _ _ _ hU A ψ hψ r j B hB hO _hC μ hμ y
  haveI := hU.ultraE
  set Λ : Set A.L := {y : A.L | ∀ i, ‖j y i‖ ≤ 1} with hΛ
  have key : ∀ z : E, (∀ e : E, ‖e‖ ≤ 1 → ψ (Algebra.trace F E (e * z)) = 1) ↔ ‖z‖ ≤ 1 :=
    ((GlobalTheory.T.unramifiedStandardAddChar_conductor_properties F E).2 ψ hψ).2.2.2
  have hmem_add : ∀ a x, a ∈ Λ → (a + x ∈ Λ ↔ x ∈ Λ) := by
    intro a x ha
    constructor
    · intro h i
      have e1 : j x i = j (a + x) i + -(j a i) := by simp
      rw [e1]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h i) (by rw [norm_neg]; exact ha i))
    · intro h i
      rw [map_add, Pi.add_apply]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha i) (h i))
  have hBadd : ∀ a x, B (a + x) y = B a y * B x y := by
    intro a x
    rw [hB, hB, hB, map_add, star_add, add_dotProduct, map_add, AddChar.map_add_eq_mul]
  haveI : ContinuousAdd A.L := IsModuleTopology.toContinuousAdd F A.L
  unfold fourB
  by_cases hy : y ∈ Λ
  · have h1 : ∀ x, Set.indicator Λ 1 x * B x y = Set.indicator Λ (fun _ => (1:ℂ)) x := by
      intro x
      by_cases hx : x ∈ Λ
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, Pi.one_apply, one_mul, hB]
        simp only [dotProduct, Pi.star_apply, map_sum]
        refine Finset.sum_induction _ (fun t => ψ t = 1) (fun u v hu hv => by
          rw [AddChar.map_add_eq_mul, hu, hv, one_mul]) (AddChar.map_zero_eq_one ψ) fun i _ => ?_
        exact (key (j y i)).2 (hy i) _ (by rw [hU.norm_star]; exact hx i)
      · simp [hx]
    simp_rw [h1]
    rw [integral_indicator_const _ hO.measurableSet, Set.indicator_of_mem hy, Pi.one_apply, mul_one]
    simp [Measure.real]
  · obtain ⟨i, hi⟩ : ∃ i, ¬ ‖j y i‖ ≤ 1 := by
      by_contra h
      push_neg at h
      exact hy h
    obtain ⟨e, he, hne⟩ : ∃ e : E, ‖e‖ ≤ 1 ∧ ψ (Algebra.trace F E (e * j y i)) ≠ 1 := by
      by_contra h
      push_neg at h
      exact hi ((key _).1 h)
    set a := j.symm (Pi.single i (star e)) with ha_def
    have hja : j a = Pi.single i (star e) := by simp [ha_def]
    have ha : a ∈ Λ := by
      intro k
      rw [hja]
      by_cases hk : k = i
      · subst hk; simp [hU.norm_star, he]
      · simp [Pi.single_eq_of_ne hk]
    have hst : star (Pi.single i (star e) : Fin r → E) = Pi.single i e := by
      ext k
      by_cases hk : k = i
      · subst hk; simp
      · simp [Pi.single_eq_of_ne hk]
    have hBa : B a y = ψ (Algebra.trace F E (e * j y i)) := by
      rw [hB, hja, hst, single_dotProduct]
    have hint : ∫ x, Set.indicator Λ 1 x * B x y ∂μ = B a y * ∫ x, Set.indicator Λ 1 x * B x y ∂μ := by
      rw [← integral_const_mul]
      calc ∫ x, Set.indicator Λ 1 x * B x y ∂μ
          = ∫ x, Set.indicator Λ 1 (a + x) * B (a + x) y ∂μ :=
            (integral_add_left_eq_self (fun x => Set.indicator Λ 1 x * B x y) a).symm
        _ = ∫ x, B a y * (Set.indicator Λ 1 x * B x y) ∂μ := by
            congr 1; ext x
            rw [hBadd]
            by_cases hx : x ∈ Λ
            · rw [Set.indicator_of_mem ((hmem_add a x ha).2 hx), Set.indicator_of_mem hx, Pi.one_apply, Pi.one_apply]; ring
            · have hx' : a + x ∉ Λ := fun h => hx ((hmem_add a x ha).1 h)
              simp [hx, hx']
    have h0 : ∫ x, Set.indicator Λ 1 x * B x y ∂μ = 0 := by
      have : (1 - B a y) * ∫ x, Set.indicator Λ 1 x * B x y ∂μ = 0 := by
        rw [sub_mul, one_mul, ← hint, sub_self]
      rcases mul_eq_zero.1 this with h | h
      · exact absurd (by rw [hBa] at h; exact (sub_eq_zero.1 h).symm) hne
      · exact h
    rw [h0]
    simp [hy]

end GlobalTheory.JR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FullLatticeSandwichBetweenIntegralElements
section
open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma.Sandwich

theorem exists_dvd_pow {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (a : O)
    (ha : a ∈ IsLocalRing.maximalIdeal O) (d : O) (hd : d ≠ 0) : ∃ k : ℕ, d ∣ a ^ k := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨k, hk⟩ := IsDiscreteValuationRing.associated_pow_irreducible hd hϖ
  refine ⟨k, ?_⟩
  have h1 : ϖ ∣ a := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer] at hϖ
    rw [hϖ] at ha
    exact Ideal.mem_span_singleton.1 ha
  exact hk.dvd.trans (pow_dvd_pow_of_dvd h1 k)

theorem eventually_pow_mul_mem {O A : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing A] [Algebra O A] (a : O) (ha : a ∈ IsLocalRing.maximalIdeal O) (S : Submodule O A)
    (x : A) (d : O) (hd : d ≠ 0) (hx : d • x ∈ S) :
    ∃ k : ℕ, ∀ n : ℕ, k ≤ n → algebraMap O A a ^ n * x ∈ S := by
  obtain ⟨k, c, hc⟩ := exists_dvd_pow a ha d hd
  refine ⟨k, fun n hn => ?_⟩
  have e : algebraMap O A a ^ n * x = (a ^ (n - k) * c) • (d • x) := by
    rw [smul_smul, Algebra.smul_def, ← map_pow]
    congr 2
    rw [mul_assoc, mul_comm c d, ← hc, ← pow_add, Nat.sub_add_cancel hn]
  rw [e]
  exact S.smul_mem _ hx

end GlobalTheory.UnitLemma.Sandwich

namespace GlobalTheory.UnitLemma.Sandwich

variable {K : UQ} (B : InvAlg K)

theorem exists_smul_isIntegral (x : B.A) : ∃ d : K.O, d ≠ 0 ∧ IsIntegral K.O (d • x) := by
  have h : IsAlgebraic K.E x := Algebra.IsAlgebraic.isAlgebraic x
  have h' : IsAlgebraic K.O x := (IsFractionRing.isAlgebraic_iff K.O K.E B.A).2 h
  obtain ⟨d, hd, hi⟩ := h'.exists_integral_multiple
  exact ⟨d, hd, hi⟩

theorem exists_smul_mem (L : Submodule K.O B.A) (hL : Submodule.span K.E (L : Set B.A) = ⊤) (x : B.A) :
    ∃ d : K.O, d ≠ 0 ∧ d • x ∈ L := by
  first
  | exact @_root_.GlobalTheory.DenominatorOfSpan.exists_denominator
  | exact _root_.GlobalTheory.DenominatorOfSpan.exists_denominator
  | (apply _root_.GlobalTheory.DenominatorOfSpan.exists_denominator <;> assumption)
  | (intros; apply _root_.GlobalTheory.DenominatorOfSpan.exists_denominator <;> assumption)
  | (intros; apply @_root_.GlobalTheory.DenominatorOfSpan.exists_denominator <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.DenominatorOfSpan.exists_denominator ..)

end GlobalTheory.UnitLemma.Sandwich

namespace GlobalTheory.UnitLemma.Sandwich

variable {K : UQ} (B : InvAlg K)

theorem exists_aeval (hP : B.P.Separable) (x : B.A) : ∃ f : K.E[X], x = aeval B.g f := by
  obtain ⟨e, he⟩ := exists_basis_pow_of_separable K B hP
  refine ⟨∑ i, C (e.repr x i) * X ^ (i : ℕ), ?_⟩
  conv_lhs => rw [← e.sum_repr x]
  simp [map_sum, he, Algebra.smul_def]

theorem traceForm_nondegenerate (hP : B.P.Separable) : (Algebra.traceForm K.E B.A).Nondegenerate := by
  refine ⟨fun w hw => ?_, fun w hw => ?_⟩
  · exact TraceNondeg.eq_zero_of_trace_mul_eq_zero K B hP (exists_aeval B hP) w
      (fun y => by simpa [Algebra.traceForm_apply] using hw y)
  · exact TraceNondeg.eq_zero_of_trace_mul_eq_zero K B hP (exists_aeval B hP) w
      (fun y => by simpa [Algebra.traceForm_apply, mul_comm] using hw y)

theorem integral_sub (hP : B.P.Separable) (a : K.O) (ha : a ∈ IsLocalRing.maximalIdeal K.O)
    (L : Submodule K.O B.A) (hL : Submodule.span K.E (L : Set B.A) = ⊤) :
    ∃ m : ℕ, ∀ n, m ≤ n → ∀ y : B.A, IsIntegral K.O y → algebraMap K.O B.A a ^ n * y ∈ L := by
  classical
  have hnd := traceForm_nondegenerate B hP
  let b0 := Module.finBasis K.E B.A
  choose d hd0 hdi using fun i => exists_smul_isIntegral B (b0 i)
  have hu : ∀ i, IsUnit (algebraMap K.O K.E (d i)) := fun i =>
    isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ (IsFractionRing.injective K.O K.E)).2 (hd0 i))
  let b := b0.isUnitSMul hu
  have hb : ∀ i, IsIntegral K.O (b i) := by
    intro i
    rw [Module.Basis.isUnitSMul_apply, algebraMap_smul]
    exact hdi i
  let bd := (Algebra.traceForm K.E B.A).dualBasis hnd b
  choose c hc0 hc using fun i => exists_smul_mem B L hL (bd i)
  choose k hk using fun i => eventually_pow_mul_mem a ha L (bd i) (c i) (hc0 i) (hc i)
  refine ⟨Finset.univ.sup k, fun n hn y hy => ?_⟩
  have hrep := bd.sum_repr y
  have hint : ∀ i, ∃ o : K.O, algebraMap K.O K.E o = bd.repr y i := by
    intro i
    rw [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply]
    exact IsIntegrallyClosed.isIntegral_iff.1
      (GlobalTheory.DiscConductor.isIntegral_trace_of_isIntegral K.O K.E B.A _ (hy.mul (hb i)))
  choose o ho using hint
  rw [← hrep, Finset.mul_sum]
  refine L.sum_mem fun i _ => ?_
  rw [← ho i, algebraMap_smul, mul_smul_comm]
  exact L.smul_mem _ (hk i n ((Finset.le_sup (Finset.mem_univ i)).trans hn))

theorem sub_integral (a : K.O) (ha : a ∈ IsLocalRing.maximalIdeal K.O) (L : Submodule K.O B.A) (hL : L.FG) :
    ∃ m : ℕ, ∀ n, m ≤ n → ∀ y ∈ L, IsIntegral K.O (algebraMap K.O B.A a ^ n * y) := by
  classical
  obtain ⟨s, hs⟩ := hL
  have hk : ∀ x : B.A, ∃ k : ℕ, ∀ n, k ≤ n →
      algebraMap K.O B.A a ^ n * x ∈ Subalgebra.toSubmodule (integralClosure K.O B.A) := by
    intro x
    obtain ⟨d, hd, hi⟩ := exists_smul_isIntegral B x
    exact eventually_pow_mul_mem a ha _ x d hd hi
  choose k hk using hk
  refine ⟨s.sup k, fun n hn y hy => ?_⟩
  rw [← hs] at hy
  induction hy using Submodule.span_induction with
  | mem x hx => exact hk x n ((Finset.le_sup hx).trans hn)
  | zero => simpa using isIntegral_zero
  | add x z _ _ hx hz => rw [mul_add]; exact hx.add hz
  | smul r x _ hx => rw [mul_smul_comm, Algebra.smul_def]; exact isIntegral_algebraMap.mul hx

end GlobalTheory.UnitLemma.Sandwich

namespace GlobalTheory.UnitLemma

theorem lattice_sandwich : ∀ (K : UQ) (B : InvAlg K), B.LieReg → ∀ a : K.O, K.Small a →
    ∀ L : Submodule K.O B.A, IsLat K.O K.E L → ∃ m : ℕ, ∀ n : ℕ, m ≤ n →
      (∀ y : B.A, IsIntegral K.O y → algebraMap K.O B.A a ^ n * y ∈ L) ∧
        ∀ y ∈ L, IsIntegral K.O (algebraMap K.O B.A a ^ n * y) := by
  intro K B hB a ha L hL
  obtain ⟨m₁, h₁⟩ := Sandwich.integral_sub B hB.2 a ha.2.1 L hL.2
  obtain ⟨m₂, h₂⟩ := Sandwich.sub_integral B a ha.2.1 L hL.1
  exact ⟨max m₁ m₂, fun n hn => ⟨h₁ n (le_of_max_le_left hn), h₂ n (le_of_max_le_right hn)⟩⟩

end GlobalTheory.UnitLemma
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HaarMeasureLUnitSmulAbsKSqStatement
section
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_measure_L_unit_smul_absK_sq : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (μ : Measure A.L), μ.IsAddHaarMeasure → ∀ (c : A.Kˣ) (S : Set A.L), μ {y : A.L | ∃ z ∈ S, y = algebraMap A.K A.L (c : A.K) * z} = ENNReal.ofReal (A.absK (c : A.K) ^ 2) * μ S := by
  first | exact @GlobalTheory.JR.ScaleHaarL.main | exact GlobalTheory.JR.ScaleHaarL.main | (intros; apply GlobalTheory.JR.ScaleHaarL.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSumInnerEulerProductQuotientInjectiveStatement
section
open scoped InnerProductSpace BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_inner_eulerProduct_quotient_injective : ∀ (Γ : Type) [Group Γ] (K : Subgroup Γ) (ι : Type) [DecidableEq ι] (c : ι → Γ →* Γ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (a : Γ → ℂ) (B : Γ → (H →L[ℂ] H)) (s : ι → ℝ) (e : Γ ⧸ K ≃ {f : ∀ v, Γ ⧸ K.comap (c v) // {w | f w ≠ (QuotientGroup.mk 1 : Γ ⧸ K.comap (c w))}.Finite}), (∀ (g : Γ) v, (e (QuotientGroup.mk g)).1 v = (QuotientGroup.mk g : Γ ⧸ K.comap (c v))) → (∀ g, g ∈ K ↔ ∀ v, c v g ∈ K) → (∀ v g, c v (c v g) = c v g) → (∀ v w g, v ≠ w → c w (c v g) = 1) → (∀ g k, k ∈ K → a (g * k) = a g) → a 1 = 1 → (∀ g, a g = ∏ᶠ v, a (c v g)) → (∀ g, ‖B g‖ ≤ 1) → B 1 = 1 → (∀ g k, k ∈ K → B (g * k) = B g) → Summable s → (∀ v, s v < 1) → (∀ v (C : Finset Γ), (∀ g ∈ C, c v g = g ∧ g ∉ K) → (∀ g ∈ C, ∀ g' ∈ C, g⁻¹ * g' ∈ K → g = g') → ∑ g ∈ C, ‖a g‖ ≤ s v) → (∀ v γ, HasSum (fun x : Γ ⧸ K.comap (c v) => a (c v (Quotient.out x)) • B (γ * c v (Quotient.out x))) (B γ * ∑' x : Γ ⧸ K.comap (c v), a (c v (Quotient.out x)) • B (c v (Quotient.out x)))) → ∃ W : H →L[ℂ] H, Function.Injective W ∧ ∀ x y, HasSum (fun q : Γ ⧸ K => a (Quotient.out q) * ⟪x, B (Quotient.out q) y⟫_ℂ) ⟪x, W y⟫_ℂ := by
  first | exact @GlobalTheory.hasSum_inner_quotient_eulerProduct_injective | exact GlobalTheory.hasSum_inner_quotient_eulerProduct_injective | (intros; apply GlobalTheory.hasSum_inner_quotient_eulerProduct_injective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharOnIdMulSqrtAbsNormInvMemSubringStatement
section
open NumberField IsDedekindDomain

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeChar_onId_mul_sqrt_absNorm_inv_mem_subring : ∀ (L : Type) [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L) (O : Subring ℂ) (cc : Ideal (𝓞 L)), cc ≠ ⊥ → (∀ P : HeightOneSpectrum (𝓞 L), cc ≤ P.asIdeal → (((χ.val P : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm P.asIdeal) : ℝ) : ℂ))⁻¹ ∈ O) → (((χ.onId (cc : FractionalIdeal (nonZeroDivisors (𝓞 L)) L) : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm cc) : ℝ) : ℂ))⁻¹ ∈ O := by
  first | exact @GlobalTheory.HeckeIdealValue.inv_mem | exact GlobalTheory.HeckeIdealValue.inv_mem | (intros; apply GlobalTheory.HeckeIdealValue.inv_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeightsFromJumpsIff
section
noncomputable section

namespace GlobalTheory.HeightsFromJumpsCompare

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.IndefiniteRowSideFullHecke

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

variable {W : LocWach PD LL O v n} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}

end Generic

open TensorProduct in

theorem _root_.GlobalTheory.HeightsFromJumpsCompare.heightsFromJumps_iff (l : ℕ) [Fact l.Prime] (P : _root_.Formalism.BasicNotions.LocPrime l) (AI : _root_.Formalism.BasicNotions.LocAinf l P)
    (H : _root_.Formalism.BasicNotions.LocHW l P) (F : _root_.Formalism.BasicNotions.LocFon l P AI H) (C : _root_.Formalism.BasicNotions.LocCmpT l P AI H F) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.PointRingCommRing.HeightsFromJumps l P AI H F C ↔
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.LocalRingStructure.HeightsFromJumps l P AI H F C :=
  Iff.rfl

end GlobalTheory.HeightsFromJumpsCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralClosureFgDvrOfSeparableCharpolyStatement
section
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralClosure_fg_dvr_of_separable_charpoly : ∀ (O E A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field E] [Algebra O E] [IsFractionRing O E] [CommRing A] [Algebra O A] [Algebra E A] [IsScalarTower O E A] [Module.Finite E A] (g : A), (LinearMap.mulLeft E g).charpoly.Separable → (Subalgebra.toSubmodule (integralClosure O A)).FG := by
  first | exact @GlobalTheory.IntClosureSep.integralClosure_fg_of_separable_charpoly | exact GlobalTheory.IntClosureSep.integralClosure_fg_of_separable_charpoly | (intros; apply GlobalTheory.IntClosureSep.integralClosure_fg_of_separable_charpoly <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIntegralIntegersUnramifiedInvolutionExtStatement
section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_integers_unramifiedInvolutionExt : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → d ≠ 0 → ∀ y : K'.O, @IsIntegral K.O K'.E _ _ (φ.comp (algebraMap K.O K.E)).toAlgebra (algebraMap K'.O K'.E y) := by
  first | exact @GlobalTheory.UnitLemma.Unr.intO | exact GlobalTheory.UnitLemma.Unr.intO | (intros; apply GlobalTheory.UnitLemma.Unr.intO <;> assumption)
end

