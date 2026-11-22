import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0034
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsPointVertRSteps
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0001

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualTopSimpleSub
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo NumberField

noncomputable section

def DualTopSimpleSub.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i) (T T' : Type) [Fintype T]
    [DecidableEq T] [Fintype T'] [DecidableEq T'] (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b)))
    (b' : Module.Basis T' ℤ (dualLattice F'))
    (hb' : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b'))) (II : IntersectionSystem),
    1 ≤ i → IsIntersectionSystem II → F'.lattice < F.lattice →
    (∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice) →
    II Unit (dualBlocks T') (dualIdeal b') i (fun _ => dualLine F'.withStdMetric b' hb') =
      II Unit (dualBlocks T) (dualIdeal b) i (fun _ => dualLine F.withStdMetric b hb) +
        (F.withStdMetric.degree - F'.withStdMetric.degree) *
          geomDeg (grassIdeal 1 1 (i - 1)) (fsMulti (plBlocks 1 1 (i - 1))) (1 * 1 * (i - 1))

namespace DualTopSimpleSubExample

def oneVec : Fin 1 → ℚ := fun _ => 1

theorem oneVec_mem : oneVec ∈ (HermLattice.standard ℚ 1).lattice := by
  apply Submodule.subset_span
  refine ⟨0, ?_⟩
  funext j
  fin_cases j
  rfl

theorem coord_of_mem {v : Fin 1 → ℚ} (hv : v ∈ (HermLattice.standard ℚ 1).lattice) : ∃ n : ℤ, v 0 = n := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 ℚ)).mp hv
  refine ⟨Rat.ringOfIntegersEquiv (c 0), ?_⟩
  rw [← hc, Rat.ringOfIntegersEquiv_apply_coe]
  simp [Algebra.smul_def]

theorem coord_of_mem_two {v : Fin 1 → ℚ} (hv : v ∈ HermLattice.twiceStandardExample.lattice) :
    ∃ m : ℤ, v 0 = 2 * m := by
  obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hv
  refine ⟨Rat.ringOfIntegersEquiv r, ?_⟩
  rw [Rat.ringOfIntegersEquiv_apply_coe]
  simp [twoVecExample, Algebra.smul_def, mul_comm]

theorem evenVec_mem (m : ℤ) :
    (fun _ : Fin 1 => 2 * (m : ℚ)) ∈ HermLattice.twiceStandardExample.lattice := by
  have h : (fun _ : Fin 1 => 2 * (m : ℚ)) = (m : 𝓞 ℚ) • twoVecExample := by
    funext j
    simp [twoVecExample, Algebra.smul_def, mul_comm]
  rw [h]
  exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)

theorem twice_lt : HermLattice.twiceStandardExample.lattice < (HermLattice.standard ℚ 1).lattice := by
  refine lt_of_le_of_ne twiceStandardExample_le fun h => ?_
  obtain ⟨m, hm⟩ := coord_of_mem_two (h ▸ oneVec_mem)
  have h1 : (1 : ℤ) = 2 * m := by
    simp only [oneVec] at hm
    exact_mod_cast hm
  omega

theorem twice_cover (N : Submodule (𝓞 ℚ) (Fin 1 → ℚ))
    (h₁ : HermLattice.twiceStandardExample.lattice ≤ N) (h₂ : N ≤ (HermLattice.standard ℚ 1).lattice) :
    N = HermLattice.twiceStandardExample.lattice ∨ N = (HermLattice.standard ℚ 1).lattice := by
  by_cases hN : N ≤ HermLattice.twiceStandardExample.lattice
  · exact Or.inl (le_antisymm hN h₁)
  right
  refine le_antisymm h₂ ?_
  obtain ⟨u, huN, hu2⟩ := SetLike.not_le_iff_exists.mp hN
  obtain ⟨n, hn⟩ := coord_of_mem (h₂ huN)
  have hu : u = fun _ => (n : ℚ) := by
    funext j
    fin_cases j
    exact hn
  have hodd : ¬ ∃ m : ℤ, n = 2 * m := by
    rintro ⟨m, rfl⟩
    apply hu2
    rw [hu]
    push_cast
    exact evenVec_mem m
  have hm : n = 2 * (n / 2) + 1 := by
    by_contra hne
    exact hodd ⟨n / 2, by omega⟩
  have hone : oneVec ∈ N := by
    have h1 : oneVec = u - fun _ => 2 * ((n / 2 : ℤ) : ℚ) := by
      rw [hu]
      funext j
      simp only [oneVec, Pi.sub_apply]
      have : (n : ℚ) = 2 * ((n / 2 : ℤ) : ℚ) + 1 := by exact_mod_cast hm
      linarith
    rw [h1]
    exact sub_mem huN (h₁ (evenVec_mem _))
  show Submodule.span (𝓞 ℚ) _ ≤ N
  rw [Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  have : (Pi.single j 1 : Fin 1 → ℚ) = oneVec := by
    funext k
    fin_cases j
    fin_cases k
    rfl
  show (Pi.single j 1 : Fin 1 → ℚ) ∈ N
  rw [this]
  exact hone

end DualTopSimpleSubExample

open DualTopSimpleSubExample in

example : ∃ (T : Type) (_ : Fintype T) (_ : DecidableEq T)
    (b' : Module.Basis T ℤ (dualLattice HermLattice.twiceStandardExample)),
    Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b')) ∧
      Function.Bijective (Matrix.mulVecLin
        (dualEmbMatrix (F := HermLattice.standard ℚ 1) dualBasisStandard)) ∧
      HermLattice.twiceStandardExample.lattice < (HermLattice.standard ℚ 1).lattice ∧
      (∀ N : Submodule (𝓞 ℚ) (Fin 1 → ℚ), HermLattice.twiceStandardExample.lattice ≤ N →
        N ≤ (HermLattice.standard ℚ 1).lattice →
        N = HermLattice.twiceStandardExample.lattice ∨ N = (HermLattice.standard ℚ 1).lattice) ∧
      1 ≤ 1 := by
  obtain ⟨T, hT, hdT, ⟨b'⟩⟩ := DualLatticeBasisExists.proof ℚ 1 HermLattice.twiceStandardExample
  exact ⟨T, hT, hdT, b', DualEmbBijective.proof ℚ 1 _ T b', dualEmbMatrix_standard_bijective, twice_lt,
    twice_cover, le_rfl⟩

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualTopStacked
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo NumberField
open scoped ComplexOrder

noncomputable section

namespace DualTopStackedExistence

variable {K : Type} [Field K] [NumberField K] {i : ℕ}

theorem dualLattice_mono {F F' : HermLattice K i} (h : F'.lattice ≤ F.lattice) :
    dualLattice F ≤ dualLattice F' :=
  fun _ hφ x hx => hφ x (h hx)

theorem card_eq_of_bijective {F : HermLattice K i} {T : Type} [Fintype T] [DecidableEq T]
    (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) :
    Fintype.card T = Fintype.card ((K →+* ℂ) × Fin i) := by
  have h := (LinearEquiv.ofBijective (Matrix.mulVecLin (dualEmbMatrix b)) hb).finrank_eq
  rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card] at h
  exact h.symm

theorem exists_stacked {F F' : HermLattice K i} (h : F'.lattice ≤ F.lattice) {T T' : Type} [Fintype T]
    [DecidableEq T] [Fintype T'] [DecidableEq T'] (b : Module.Basis T ℤ (dualLattice F))
    (b' : Module.Basis T' ℤ (dualLattice F')) (hcard : Fintype.card T = Fintype.card T') :
    ∃ (b₁ : Module.Basis T' ℤ (dualLattice F)) (b₁' : Module.Basis T' ℤ (dualLattice F')) (a : T' → ℤ),
      ∀ t, (b₁ t : Fin i → K) = a t • (b₁' t : Fin i → K) := by
  let eN := Submodule.comapSubtypeEquivOfLe (dualLattice_mono h)
  have hrank : Module.finrank ℤ ((dualLattice F).comap (dualLattice F').subtype) =
      Module.finrank ℤ (dualLattice F') := by
    rw [eN.finrank_eq, Module.finrank_eq_card_basis b, Module.finrank_eq_card_basis b', hcard]
  obtain ⟨b₁', a, ab, hab⟩ := Submodule.exists_smith_normal_form_of_rank_eq b' hrank
  refine ⟨ab.map eN, b₁', a, fun t => ?_⟩
  have h1 := congrArg (fun x : dualLattice F' => (x : Fin i → K)) (hab t)
  simp only [Module.Basis.map_apply]
  rw [Submodule.comapSubtypeEquivOfLe_apply_coe]
  simpa using h1

end DualTopStackedExistence

def DualTopStacked.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b)))
    (b' : Module.Basis T ℤ (dualLattice F'))
    (hb' : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b'))) (a : T → ℤ) (II : IntersectionSystem),
    1 ≤ i → IsIntersectionSystem II → F'.lattice ≤ F.lattice →
    (∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) →
    II Unit (dualBlocks T) (dualIdeal b') i (fun _ => dualLine F'.withStdMetric b' hb') =
      II Unit (dualBlocks T) (dualIdeal b) i (fun _ => dualLine F.withStdMetric b hb) +
        (∑ t, Real.log |(a t : ℝ)|) *
          geomDeg (grassIdeal 1 1 (i - 1)) (fsMulti (plBlocks 1 1 (i - 1))) (1 * 1 * (i - 1))

example : ∃ (T : Type) (_ : Fintype T) (_ : DecidableEq T)
    (b : Module.Basis T ℤ (dualLattice (HermLattice.standard ℚ 1)))
    (b' : Module.Basis T ℤ (dualLattice HermLattice.twiceStandardExample)) (a : T → ℤ),
    Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b)) ∧
      Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b')) ∧
      HermLattice.twiceStandardExample.lattice ≤ (HermLattice.standard ℚ 1).lattice ∧
      (∀ t, (b t : Fin 1 → ℚ) = a t • (b' t : Fin 1 → ℚ)) ∧ 1 ≤ 1 := by
  obtain ⟨T', hT', hdT', ⟨b'⟩⟩ := DualLatticeBasisExists.proof ℚ 1 HermLattice.twiceStandardExample
  have hcard : Fintype.card Unit = Fintype.card T' := by
    rw [DualTopStackedExistence.card_eq_of_bijective dualBasisStandard dualEmbMatrix_standard_bijective,
      DualTopStackedExistence.card_eq_of_bijective b' (DualEmbBijective.proof ℚ 1 _ T' b')]
  obtain ⟨b₁, b₁', a, hab⟩ := DualTopStackedExistence.exists_stacked twiceStandardExample_le
    dualBasisStandard b' hcard
  exact ⟨T', hT', hdT', b₁, b₁', a, DualEmbBijective.proof ℚ 1 _ T' b₁,
    DualEmbBijective.proof ℚ 1 _ T' b₁', twiceStandardExample_le, hab, le_rfl⟩

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsVertRIndexSteps
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 MvPolynomial NumberField

noncomputable section

section Objects

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {Ω : Type*} [Field Ω]

def sectionMod (y : (Σ k, ι k) → Ω) : Submodule (curveRing y) Ω where
  carrier := chartLat y (fun _ => 1) 1
  zero_mem' := (chartLat y (fun _ => 1) 1).zero_mem
  add_mem' := fun ha hb => (chartLat y (fun _ => 1) 1).add_mem ha hb
  smul_mem' := fun b m hm c hc => by
    have hb : (b : Ω) ∈ chartRingZ y c := mem_curveRing.mp b.2 c hc
    have hm' := hm c hc
    rw [Subring.smul_def, smul_eq_mul, mul_assoc]
    exact mul_mem hb hm'

abbrev sectionQuot (y : (Σ k, ι k) → Ω) (x : Ω) : Type _ :=
  ↥(sectionMod y) ⧸ (Submodule.span (curveRing y) {x}).comap (sectionMod y).subtype

def curvePtIdeal (y : (Σ k, ι k) → Ω) (W : Ideal (MRing ι)) : Ideal (curveRing y) :=
  Ideal.span {b | ∃ (d : K → ℕ) (g h : MRing ι), IsMultiHomog g d ∧ IsMultiHomog h d ∧ g ∈ W ∧ h ∉ W ∧
    (b : Ω) * aeval y h = aeval y g}

end Objects

def SectionQuotFinite.Statement : Prop :=
  ∀ (T : Type) [Fintype T] (K' : Type) [Field K'] [NumberField K'] (y : (Σ _ : Unit, T) → K')
    (s : MRing (fun _ : Unit => T)),
    IsArithVar (mCoordIdeal y) 1 → IsMultiHomog s (fun _ => 1) → s ∉ mCoordIdeal y →
      Finite (sectionQuot y (aeval y s))

def VertPointLength.Statement : Prop :=
  ∀ (T : Type) [Fintype T] (K' : Type) [Field K'] [NumberField K'] (y : (Σ _ : Unit, T) → K')
    (s : MRing (fun _ : Unit => T)),
    IsArithVar (mCoordIdeal y) 1 → IsMultiHomog s (fun _ => 1) → s ∉ mCoordIdeal y →
      Set.BijOn (curvePtIdeal y) (divSupp (mCoordIdeal y) s)
          {m | m.IsMaximal ∧ locLen m (sectionQuot y (aeval y s)) ≠ 0} ∧
        ∀ W ∈ divSupp (mCoordIdeal y) s,
          multAt (mCoordIdeal y ⊔ Ideal.span {s}) W =
            locLen (curvePtIdeal y W) (sectionQuot y (aeval y s))

def VertPointResidue.Statement : Prop :=
  ∀ (T : Type) [Fintype T] (K' : Type) [Field K'] [NumberField K'] (y : (Σ _ : Unit, T) → K')
    (s : MRing (fun _ : Unit => T)),
    IsArithVar (mCoordIdeal y) 1 → IsMultiHomog s (fun _ => 1) → s ∉ mCoordIdeal y →
      ∀ W ∈ divSupp (mCoordIdeal y) s,
        (geoNum 0 W Fin.elim0 : ℝ) * Real.log (charOf W) =
          Real.log (Nat.card (curveRing y ⧸ curvePtIdeal y W))

end

end GroundTheory.Heights₂.Heights
end

