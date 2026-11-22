import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0031
import GroundTheory.HeightsAndTheta.Heights.ArithDegreeExact
import GroundTheory.HeightsAndTheta.Heights.ArithDegreeIdeal
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.Bundle0008
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0042
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0040
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualLatticeIndex
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0020
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0017
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.GeoNum
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0009
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsExamples
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.InhDivCycleOfSuppEmpty

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.DegreeRangeIncl
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels

open NumberField TensorProduct GroundTheory.Heights₂.Heights

noncomputable section

theorem HermitianExtension.degree_range_incl {K : Type} [Field K] [NumberField K]
    {E' E E'' : HermitianBundle.{0} K} (Y : HermitianExtension E' E E'') :
    E.degree (LinearMap.range Y.incl) = E'.arithDegree := by
  rw [HermitianBundle.degree_eq_arithDegree]
  symm
  refine LatticeLemmas.arithDegree_congr _ _ (LinearEquiv.ofInjective Y.incl Y.incl_injective)
    fun σ x y ↦ ?_
  rw [HermitianMetric.comap_inner, fibreMap_tmul, fibreMap_tmul]
  have h := Y.incl_isometric σ ((1 : ComplexAt σ) ⊗ₜ x) ((1 : ComplexAt σ) ⊗ₜ y)
  simp only [LinearMap.lTensor_tmul] at h
  exact h.symm

theorem S6.ExtensionDegree.proof : S6.ExtensionDegree.Statement := by
  intro K _ _ E' E E'' Y
  rw [HermitianBundle.degree_top_eq_arithDegree, HermitianBundle.degree_top_eq_arithDegree,
    HermitianExtension.degree_range_incl, Y.arithDegree_eq_add]
  ring

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStackedGraphFibre
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField

noncomputable section

namespace StackedGraphFibre

variable {K' : Type} [Fintype K'] {ι : K' → Type} [∀ k, Fintype (ι k)]

open Classical in

def vertWeight {n : ℕ} (L : Fin n → HermLine ι) (W : Ideal (MRing ι)) : ℝ :=
  if IsHorizontal W then 0 else (geoNum n W (fun j => (L j).a) : ℝ) * Real.log (charOf W)

theorem vertR_eq_finsum (P : Ideal (MRing ι)) {n : ℕ} (L : Fin n → HermLine ι) (s : MRing ι) :
    vertR P L s = ∑ᶠ W, (divCycle P s W : ℝ) * vertWeight L W := by
  classical
  rw [vertR, finsum_mem_def]
  refine finsum_congr fun W => ?_
  simp only [Set.indicator, divCycle, Finsupp.ofSupportFinite_coe, vertWeight]
  by_cases hW : W ∈ divSupp P s
  · rw [if_pos hW, if_pos hW]
  · rw [if_neg hW, if_neg hW, Nat.cast_zero, zero_mul]

theorem finite_support (P : Ideal (MRing ι)) {n : ℕ} (L : Fin n → HermLine ι) (s : MRing ι) :
    (Function.support fun W => (divCycle P s W : ℝ) * vertWeight L W).Finite :=
  (divCycle P s).support.finite_toSet.subset fun W hW =>
    Finsupp.mem_support_iff.mpr fun h0 => hW (by simp [h0])

theorem vertR_sub (P : Ideal (MRing ι)) {n : ℕ} (L : Fin n → HermLine ι) (s₁ s₂ : MRing ι)
    (E : Ideal (MRing ι)) (hhor : ¬ IsHorizontal E)
    (hE : (divCycle P s₂ E : ℤ) = divCycle P s₁ E + 1)
    (hW : ∀ W, ¬ IsHorizontal W → W ≠ E → divCycle P s₂ W = divCycle P s₁ W) :
    vertR P L s₁ - vertR P L s₂ = -((geoNum n E (fun j => (L j).a) : ℝ) * Real.log (charOf E)) := by
  classical
  rw [vertR_eq_finsum, vertR_eq_finsum, ← finsum_sub_distrib (finite_support P L s₁) (finite_support P L s₂)]
  have hpt : ∀ W, (divCycle P s₁ W : ℝ) * vertWeight L W - (divCycle P s₂ W : ℝ) * vertWeight L W =
      if W = E then -vertWeight L E else 0 := by
    intro W
    by_cases hWh : IsHorizontal W
    · have hne : W ≠ E := fun h => hhor (h ▸ hWh)
      simp [vertWeight, hWh, hne]
    · by_cases hWE : W = E
      · subst hWE
        have hR : (divCycle P s₂ W : ℝ) = divCycle P s₁ W + 1 := by exact_mod_cast hE
        rw [if_pos rfl, hR]
        ring
      · rw [if_neg hWE, hW W hWh hWE, sub_self]
  rw [finsum_congr hpt, finsum_eq_single _ E (fun W hW => if_neg hW), if_pos rfl]
  simp [vertWeight, hhor]

end StackedGraphFibre

open StackedGraphFibre in

theorem DualStackedGraphFibre.proof (hCyc : DualStackedExcCycle.Statement)
    (hSec : DualStackedExcGeoSecond.Statement) (hFir : DualStackedExcGeoFirst.Statement) :
    DualStackedGraphFibre.Statement := by
  intro K _ _ i F F' T _ _ b b' a hi hlt hcov hab t L hL
  obtain ⟨E, hE, hhor, hEt⟩ := hCyc K i F F' T b b' a hi hlt hcov hab
  have key := vertR_sub (stackedGraph b' a) L (graphSecond t) (C (a t) * graphFirst t) E hhor (hEt t).1
    (hEt t).2
  have ha : ∀ s, a s ≠ 0 := fun s hs =>
    b.ne_zero s (Subtype.ext (by rw [hab s, hs, zero_smul]; rfl))
  refine ⟨fun hall => ?_, fun ⟨j, hj⟩ => ?_⟩
  · have hd : (fun j => (L j).a) = fun _ => degSecond := funext hall
    rw [key, hd, hSec K i F F' T b b' a hi hlt hcov hab E hE, ← DualLatticeIndex.proof K i F F' hlt.le,
      DualStackedDegreeAlt.relIndex_stacked hlt.le b b' a hab,
      Real.log_prod (fun s _ => abs_ne_zero.mpr (Int.cast_ne_zero.mpr (ha s)))]
  · rw [key, hFir K i F F' T b b' a hi hlt hcov hab E hE (fun j => (L j).a) hL ⟨j, hj⟩]
    simp

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGrassFibreDegree
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 MvPolynomial

noncomputable section

namespace GrassmannianFibreDegree

variable (n p : ℕ) [Fact p.Prime]

theorem span_eq_ker :
    (Ideal.span {C (p : ℤ)} : Ideal (MRing (plBlocks 1 1 n))) =
      RingHom.ker (Bridge.GeoNum.red (ι := plBlocks 1 1 n) p) :=
  (Bridge.GeoNum.ker_red p).symm

theorem isPrime : (Ideal.span {C (p : ℤ)} : Ideal (MRing (plBlocks 1 1 n))).IsPrime := by
  rw [span_eq_ker]
  exact RingHom.ker_isPrime _

theorem isRelevant : IsRelevant (Ideal.span {C (p : ℤ)} : Ideal (MRing (plBlocks 1 1 n))) := by
  intro k
  refine ⟨plAnchor 1 n, ?_⟩
  rw [span_eq_ker, RingHom.mem_ker, Bridge.GeoNum.red, map_X]
  exact X_ne_zero _

theorem divSupp_eq :
    divSupp (⊥ : Ideal (MRing (plBlocks 1 1 n))) (C (p : ℤ)) = {Ideal.span {C (p : ℤ)}} := by
  have := isPrime n p
  ext W
  simp only [divSupp, bot_sup_eq, Ideal.minimalPrimes_eq_subsingleton_self, Set.mem_ofPred_eq,
    Set.mem_singleton_iff]
  constructor
  · exact fun h => h.1
  · rintro rfl
    exact ⟨rfl, isRelevant n p⟩

theorem ringKrullDim_quot :
    ringKrullDim (MRing (plBlocks 1 1 n) ⧸ (Ideal.span {C (p : ℤ)} : Ideal (MRing (plBlocks 1 1 n)))) =
      ((n + Fintype.card (Fin 1) : ℕ) : WithBot ℕ∞) := by
  rw [span_eq_ker, ringKrullDim_eq_of_ringEquiv
      (RingHom.quotientKerEquivOfSurjective (Bridge.GeoNum.red_surjective p)),
    MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add]
  have hc : Nat.card ((_ : Fin 1) × PlIdx 1 n) = n + 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
    simp
    omega
  rw [hc, Fintype.card_fin]

def coordEquiv : (Σ _ : Unit, Fin (n + 1)) ≃ (Σ _ : Fin 1, PlIdx 1 n) :=
  Equiv.ofBijective (GrassmannianLinesProjective.coordMap n)
    ⟨(GrassmannianLinesProjective.isBlockMap n).2.1, GrassmannianLinesProjective.coordMap_surjective n⟩

theorem intNum_bot :
    NumbersDVR.intNum (ZMod p) (⊥ : Ideal (NumbersDVR.MRing (plBlocks 1 1 n) (ZMod p)))
      (fun _ : Fin n => fun _ : Fin 1 => (1 : ℤ)) = 1 := by
  have h := FieldNumbers.Relabel.intNum_map_rename (F := ZMod p) (Equiv.ofUnique Unit (Fin 1))
    (coordEquiv n) (fun _ => Subsingleton.elim _ _)
    (⊥ : Ideal (NumbersDVR.MRing (FieldNumbers.ProjIdx n) (ZMod p)))
    (fun _ : Fin n => fun _ : Fin 1 => (1 : ℤ))
  rw [Ideal.map_bot] at h
  rw [h]
  exact FieldNumbers.intNum_projectiveSpace (ZMod p) n

theorem geoNum_span :
    geoNum n (Ideal.span {C (p : ℤ)} : Ideal (MRing (plBlocks 1 1 n)))
      (fun _ : Fin n => fun _ : Fin 1 => (1 : ℤ)) = 1 := by
  have := isPrime n p
  have hV : IsMultiProjPrime (Ideal.span {C (p : ℤ)} : Ideal (MRing (plBlocks 1 1 n))) :=
    ⟨isPrime n p, ⟨{C (p : ℤ)}, fun f hf => ⟨0, by
      rw [Set.mem_singleton_iff.mp hf]
      exact Inter.Conservation.isMultiHomog_C _⟩, rfl⟩, isRelevant n p⟩
  rw [← Bridge.intNum_map_eq_geoNum p n _ hV (Ideal.mem_span_singleton_self _) (ringKrullDim_quot n p)]
  have hb : (Ideal.span {C (p : ℤ)} : Ideal (MRing (plBlocks 1 1 n))).map
      (MvPolynomial.map (Int.castRingHom (ZMod p))) = ⊥ :=
    (Ideal.map_eq_bot_iff_le_ker _).mpr (span_eq_ker n p).le
  rw [hb]
  exact intNum_bot n p

end GrassmannianFibreDegree

open GrassmannianFibreDegree in

theorem GrassFibreDegree.proof : GrassFibreDegree.Statement := by
  intro n p hp
  have : Fact p.Prime := ⟨hp⟩
  have := isPrime n p
  have hW : (Ideal.span {C (p : ℤ)} : Ideal (MRing (plBlocks 1 1 n))) ∈
      divSupp (⊥ : Ideal (MRing (plBlocks 1 1 n))) (C (p : ℤ)) := by
    rw [divSupp_eq]
    rfl
  have hg : geoNum n (Ideal.span {C (p : ℤ)} : Ideal (MRing (plBlocks 1 1 n)))
      (fun j => ((fun _ : Fin n => fsMulti (plBlocks 1 1 n)) j).a) = 1 :=
    geoNum_span n p
  rw [GrassmannianLinesProjective.grassIdeal_eq_bot]
  unfold vertR
  rw [divSupp_eq, finsum_mem_singleton, if_neg (Inter.Conservation.not_horizontal hp hW),
    Inter.Conservation.charOf_eq hp hW, bot_sup_eq, ReciprocityTheory.ChartRestriction.G.AI.I1.inh_multAt_self, hg]
  simp

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualStackedExcLinear
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField

noncomputable section

def linPointMap {T : Type} [Fintype T] {k : Type} [Field k] {n : ℕ} (α : T → k) (M : T → Fin n → k) :
    MRing (stackedBlocks T) →+* MvPolynomial (Option (Fin n)) k :=
  eval₂Hom (Int.castRingHom _) fun
    | ⟨.inl _, t⟩ => C (α t) * X none
    | ⟨.inr _, t⟩ => ∑ j, C (M t j) * X (some j)

def linPrime {T : Type} [Fintype T] {k : Type} [Field k] {n : ℕ} (α : T → k) (M : T → Fin n → k) :
    Ideal (MRing (stackedBlocks T)) :=
  RingHom.ker (linPointMap α M)

def LinFormsIndep {T : Type} {k : Type} [Field k] {n : ℕ} (M : T → Fin n → k) : Prop :=
  ∀ w : Fin n → k, (∀ t, ∑ j, M t j * w j = 0) → w = 0

def DualStackedExcLinear.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F'))
    (a : T → ℤ),
    1 ≤ i → F'.lattice < F.lattice →
    (∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice) →
    (∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) →
    ∀ E : Ideal (MRing (stackedBlocks T)), IsStackedExc b' a E →
      ∃ (k : Type) (_ : Field k) (_ : Fintype k) (α : T → k) (M : T → Fin i → k),
        Submodule.span ℤ (Set.range α) = ⊤ ∧ LinFormsIndep M ∧ E = linPrime α M ∧
          Fintype.card k = F'.lattice.toAddSubgroup.relIndex F.lattice.toAddSubgroup

def LinPrimeCut.Statement : Prop :=
  ∀ (T : Type) [Fintype T] (k : Type) [Field k] (n : ℕ) (α : T → k) (M : T → Fin (n + 2) → k),
    Submodule.span ℤ (Set.range α) = ⊤ → LinFormsIndep M →
    ∀ c : T, graphSecond c ∉ linPrime α M →
      ∃ M' : T → Fin (n + 1) → k, LinFormsIndep M' ∧
        divSupp (linPrime α M) (graphSecond c) = {linPrime α M'} ∧
        multAt (linPrime α M ⊔ Ideal.span {graphSecond c}) (linPrime α M') = 1

def LinPrimeBase.Statement : Prop :=
  ∀ (T : Type) [Fintype T] (k : Type) [Field k] (α : T → k) (M : T → Fin 1 → k),
    Submodule.span ℤ (Set.range α) = ⊤ → LinFormsIndep M →
    ∀ c : (κ : Unit ⊕ Unit) → stackedBlocks T κ,
      (∀ κ, (X ⟨κ, c κ⟩ : MRing (stackedBlocks T)) ∉ linPrime α M) →
      Nonempty ((MRing (stackedBlocks T) ⧸ (linPrime α M ⊔
        Ideal.span (Set.range fun κ => (X ⟨κ, c κ⟩ : MRing (stackedBlocks T)) - 1))) ≃+* k)

namespace LinPrimeExample

theorem linPointMap_first {T : Type} [Fintype T] {k : Type} [Field k] {n : ℕ} (α : T → k) (M : T → Fin n → k)
    (t : T) : linPointMap α M (graphFirst t) = C (α t) * X none := by
  simp [linPointMap, graphFirst]

theorem linPointMap_second {T : Type} [Fintype T] {k : Type} [Field k] {n : ℕ} (α : T → k) (M : T → Fin n → k)
    (t : T) : linPointMap α M (graphSecond t) = ∑ j, C (M t j) * X (some j) := by
  simp [linPointMap, graphSecond]

def idForms : Fin 2 → Fin 2 → ZMod 2 := fun t j => if t = j then 1 else 0

theorem two_mem_not_one : (C 2 : MRing (stackedBlocks Unit)) ∈
      linPrime (fun _ : Unit => (1 : ZMod 2)) (fun (_ : Unit) (_ : Fin 1) => (1 : ZMod 2)) ∧
    (1 : MRing (stackedBlocks Unit)) ∉
      linPrime (fun _ : Unit => (1 : ZMod 2)) (fun (_ : Unit) (_ : Fin 1) => (1 : ZMod 2)) := by
  refine ⟨?_, ?_⟩
  · rw [linPrime, RingHom.mem_ker, linPointMap, coe_eval₂Hom, eval₂_C, eq_intCast,
      ← map_intCast (C : ZMod 2 →+* MvPolynomial (Option (Fin 1)) (ZMod 2)),
      show ((2 : ℤ) : ZMod 2) = 0 by decide, map_zero]
  · rw [linPrime, RingHom.mem_ker, map_one]
    exact one_ne_zero

end LinPrimeExample

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualStackedExcReduced
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField

noncomputable section

def DualStackedExcReduced.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F'))
    (a : T → ℤ),
    1 ≤ i → F'.lattice < F.lattice →
    (∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice) →
    (∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) →
    ∃ E : Ideal (MRing (stackedBlocks T)), IsStackedExc b' a E ∧
      (∀ W : Ideal (MRing (stackedBlocks T)), IsStackedExc b' a W → W = E) ∧
      multAt (stackedBase b' a) E = 1

end

end GroundTheory.Heights₂.Heights
end

