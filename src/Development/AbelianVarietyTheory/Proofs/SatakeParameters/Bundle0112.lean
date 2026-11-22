import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0107
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0106
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.Columns.HeckeSp
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0031
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.OmegaPullOmegaTraceOfSecTraceOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0024
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0009
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0010
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0012
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.TransportFirstLevel
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KurComplete
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.SecondLevelOfNorm
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.BiextensionRelation
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.Bundle0004
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSplitIdempotentsOfRelTraceOneModTwo

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardCosetsEqSubspacesKernelResidue
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitHecke.Cosets

open IsLocalRing

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
  [IsFractionRing O K] {p : O}

theorem map_res_eq_zero_iff (hp : Irreducible p) {m n : ℕ} (X : Matrix (Fin m) (Fin n) O) :
    X.map (residue O) = 0 ↔ ∃ C : Matrix (Fin m) (Fin n) O, X = p • C := by
  have hm : maximalIdeal O = Ideal.span {p} := hp.maximalIdeal_eq
  constructor
  · intro h
    have : ∀ i j, ∃ c, X i j = p * c := by
      intro i j
      have h1 : residue O (X i j) = 0 := congrFun (congrFun h i) j
      rw [residue_eq_zero_iff, hm, Ideal.mem_span_singleton] at h1
      exact h1
    choose C hC using this
    exact ⟨Matrix.of C, Matrix.ext hC⟩
  · rintro ⟨C, rfl⟩
    ext i j
    have : residue O (p * C i j) = 0 := by
      rw [residue_eq_zero_iff, hm, Ideal.mem_span_singleton]
      exact dvd_mul_right _ _
    exact this

theorem map_inj {m n : ℕ} {X Y : Matrix (Fin m) (Fin n) O}
    (h : X.map (algebraMap O K) = Y.map (algebraMap O K)) : X = Y := by
  ext i j
  exact IsFractionRing.injective O K (congrFun (congrFun h i) j)

omit [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K] in
theorem map_smul' {m n : ℕ} (c : O) (X : Matrix (Fin m) (Fin n) O) :
    (c • X).map (algebraMap O K) = algebraMap O K c • X.map (algebraMap O K) := by
  ext i j
  simp

theorem intM_inv_smul_iff (hp : Irreducible p) {m n : ℕ} (X : Matrix (Fin m) (Fin n) O) :
    IntM O ((algebraMap O K p)⁻¹ • X.map (algebraMap O K)) ↔ X.map (residue O) = 0 := by
  have h0 : algebraMap O K p ≠ 0 := by
    intro h
    exact hp.ne_zero (IsFractionRing.injective O K (by rw [h, map_zero]))
  rw [map_res_eq_zero_iff hp, intM_iff]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, map_inj (K := K) ?_⟩
    rw [map_smul', hC, smul_smul, mul_inv_cancel₀ h0, one_smul]
  · rintro ⟨C, rfl⟩
    refine ⟨C, ?_⟩
    rw [map_smul', smul_smul, inv_mul_cancel₀ h0, one_smul]

theorem exists_of_range_le (hp : Irreducible p) {n : ℕ} {A A' : Matrix (Fin n) (Fin n) O}
    (h : LinearMap.range (A'.map (residue O)).mulVecLin ≤ LinearMap.range (A.map (residue O)).mulVecLin) :
    ∃ B C : Matrix (Fin n) (Fin n) O, A' = A * B + p • C := by
  have h1 : ∀ j, ∃ b : Fin n → O, (A.map (residue O)) *ᵥ (fun i => residue O (b i)) =
      (A'.map (residue O)) *ᵥ Pi.single j 1 := by
    intro j
    obtain ⟨y, hy⟩ := h ⟨Pi.single j 1, rfl⟩
    choose b hb using fun i => residue_surjective (R := O) (y i)
    refine ⟨b, ?_⟩
    have : (fun i => residue O (b i)) = y := funext hb
    rw [this]
    exact hy
  choose b hb using h1
  obtain ⟨C, hC⟩ := (map_res_eq_zero_iff hp (A' - A * Matrix.of fun i j => b j i)).1 (by
    ext i j
    have := congrFun (hb j) i
    rw [Matrix.mulVec_single_one] at this
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.col_apply] at this
    simp [Matrix.mul_apply, ← this])
  exact ⟨_, C, by rw [← hC]; abel⟩

theorem range_le_of_mul {n : ℕ} {A A' : Matrix (Fin n) (Fin n) O} {a a' : GL (Fin n) K}
    (hA : A.map (algebraMap O K) = a.1) (hA' : A'.map (algebraMap O K) = a'.1) (h : IntM O (a⁻¹ * a').1) :
    LinearMap.range (A'.map (residue O)).mulVecLin ≤ LinearMap.range (A.map (residue O)).mulVecLin := by
  obtain ⟨B, hB⟩ := intM_iff.1 h
  have : A' = A * B := by
    refine map_inj (K := K) ?_
    rw [Matrix.map_mul, hA, hA', hB, ← Units.val_mul, mul_inv_cancel_left]
  rw [this, Matrix.map_mul, Matrix.mulVecLin_mul]
  exact LinearMap.range_comp_le_range _ _

theorem intM_of_range_le (hp : Irreducible p) {n : ℕ} {A A' : Matrix (Fin n) (Fin n) O} {a a' : GL (Fin n) K}
    (hA : A.map (algebraMap O K) = a.1) (hA' : A'.map (algebraMap O K) = a'.1)
    (ha : IntM O (algebraMap O K p • (a⁻¹).1))
    (h : LinearMap.range (A'.map (residue O)).mulVecLin ≤ LinearMap.range (A.map (residue O)).mulVecLin) :
    IntM O (a⁻¹ * a').1 := by
  obtain ⟨B, C, hBC⟩ := exists_of_range_le hp h
  have : (a⁻¹ * a').1 = B.map (algebraMap O K) + (algebraMap O K p • (a⁻¹).1) * C.map (algebraMap O K) := by
    rw [Units.val_mul, ← hA', hBC, Matrix.map_add _ (map_add _), Matrix.map_mul, map_smul', hA, Matrix.mul_add,
      ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul, Matrix.mul_smul,
      Matrix.smul_mul]
  rw [this]
  exact (intM_iff.2 ⟨B, rfl⟩).add (ha.mul (intM_iff.2 ⟨C, rfl⟩))

theorem GInt.exists_det {n : ℕ} {k : GL (Fin n) K} (hk : GInt O k) : ∃ u : Oˣ, k.1.det = algebraMap O K u := by
  obtain ⟨A, hA⟩ := intM_iff.1 hk.1
  obtain ⟨B, hB⟩ := intM_iff.1 hk.2
  have : A * B = 1 := by
    refine map_inj (K := K) ?_
    rw [Matrix.map_mul, hA, hB, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hu : IsUnit A.det := Matrix.isUnit_det_of_right_inverse this
  refine ⟨hu.unit, ?_⟩
  rw [← hA, IsUnit.unit_spec, RingHom.map_det]
  rfl

theorem hk_mul {n j : ℕ} {α k₁ k₂ : GL (Fin n) K} (hα : Hk O p j α) (h₁ : GInt O k₁) (h₂ : GInt O k₂) :
    Hk O p j (k₁ * α * k₂) := by
  refine ⟨(h₁.1.mul hα.1).mul h₂.1, ?_, ?_⟩
  · have := (h₂.2.mul hα.2.1).mul h₁.2
    rw [_root_.mul_inv_rev, _root_.mul_inv_rev, Units.val_mul, Units.val_mul]
    rwa [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc] at this
  · obtain ⟨u, hu⟩ := hα.2.2
    obtain ⟨u₁, hu₁⟩ := GInt.exists_det h₁
    obtain ⟨u₂, hu₂⟩ := GInt.exists_det h₂
    refine ⟨u₁ * u * u₂, ?_⟩
    rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hu, hu₁, hu₂, ← map_mul, ← map_mul]
    congr 1
    push_cast
    ring

omit [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K] in
theorem gInt_map {n : ℕ} (g : GL (Fin n) O) : GInt O (Matrix.GeneralLinearGroup.map (algebraMap O K) g) :=
  ⟨intM_iff.2 ⟨g.1, rfl⟩, by rw [← map_inv]; exact intM_iff.2 ⟨(g⁻¹).1, rfl⟩⟩

theorem cond_iff (hp : Irreducible p) {m n : ℕ} (z : Matrix (Fin m) (Fin n) O) {A : Matrix (Fin n) (Fin n) O}
    {a : Matrix (Fin n) (Fin n) K} (hA : A.map (algebraMap O K) = a) :
    IntM O (((algebraMap O K p)⁻¹ • z.map (algebraMap O K)) * a) ↔
      LinearMap.range (A.map (residue O)).mulVecLin ≤ LinearMap.ker (z.map (residue O)).mulVecLin := by
  rw [← hA, Matrix.smul_mul, ← Matrix.map_mul, intM_inv_smul_iff hp, LinearMap.range_le_ker_iff,
    ← Matrix.mulVecLin_mul, Matrix.map_mul]
  constructor
  · intro h
    rw [h, Matrix.mulVecLin_zero]
  · intro h
    apply Matrix.toLin'.injective
    rw [map_zero]
    exact h

theorem card_cosets : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] (p : O), Irreducible p → ∀ (m n j : ℕ) (ι : Type) (α : GL (Fin n) K) (R : Finset ι) (ρ : ι → GL (Fin n) K) (z : Matrix (Fin m) (Fin n) O), j ≤ n → Hk O p j α → Reps O α R ρ → Nat.card {γ : ι // γ ∈ R ∧ IntM O (((algebraMap O K p)⁻¹ • z.map (algebraMap O K)) * (ρ γ).1)} = Nat.card {W : Submodule (IsLocalRing.ResidueField O) (Fin n → IsLocalRing.ResidueField O) // Module.finrank (IsLocalRing.ResidueField O) W + j = n ∧ W ≤ LinearMap.ker (z.map (IsLocalRing.residue O)).mulVecLin} := by
  intro O K _ _ _ _ _ _ p hp m n j ι α R ρ z hj hα hR
  have hH : ∀ γ ∈ R, Hk O p j (ρ γ) := by
    intro γ hγ
    obtain ⟨k₁, k₂, h₁, h₂, h⟩ := hR.1 γ hγ
    rw [h]
    exact hk_mul hα h₁ h₂
  choose A hA using fun γ (hγ : γ ∈ R) => intM_iff.1 (hH γ hγ).1
  refine Nat.card_eq_of_bijective (fun γ => ⟨LinearMap.range ((A γ.1 γ.2.1).map (residue O)).mulVecLin,
    GlobalTheory.SplitHecke.finrank_range_reduction O K p hp n j _ _ hj (hH _ γ.2.1) (hA _ γ.2.1), (cond_iff hp z (hA _ γ.2.1)).1 γ.2.2⟩) ⟨?_, ?_⟩
  · rintro ⟨γ, hγ, hγ1⟩ ⟨γ', hγ', hγ2⟩ h
    have h' : LinearMap.range ((A γ hγ).map (residue O)).mulVecLin =
        LinearMap.range ((A γ' hγ').map (residue O)).mulVecLin := congrArg Subtype.val h
    have hG : GInt O ((ρ γ)⁻¹ * ρ γ') := by
      refine ⟨intM_of_range_le hp (hA γ hγ) (hA γ' hγ') (hH γ hγ).2.1 h'.ge, ?_⟩
      rw [_root_.mul_inv_rev, inv_inv]
      exact intM_of_range_le hp (hA γ' hγ') (hA γ hγ) (hH γ' hγ').2.1 h'.le
    obtain ⟨k₁, k₂, h₁, h₂, he⟩ := hR.1 γ' hγ'
    have hu := hR.2 k₁ k₂ h₁ h₂
    rw [← he] at hu
    exact Subtype.ext (hu.unique ⟨hγ, hG⟩ ⟨hγ', by rw [inv_mul_cancel]; exact gInt_one⟩)
  · rintro ⟨W, hW, hWz⟩
    obtain ⟨A₀, hA₀⟩ := intM_iff.1 hα.1
    have h0 := GlobalTheory.SplitHecke.finrank_range_reduction O K p hp n j _ _ hj hα hA₀
    obtain ⟨g, hg⟩ := GlobalTheory.SplitHecke.exists_gl_map_residue_eq O n (LinearMap.range (A₀.map (residue O)).mulVecLin) W (by omega)
    obtain ⟨γ, ⟨hγ, hG⟩, -⟩ := hR.2 _ 1 (gInt_map g) gInt_one
    rw [mul_one] at hG
    have hgA : (g.1 * A₀).map (algebraMap O K) =
        (Matrix.GeneralLinearGroup.map (algebraMap O K) g * α).1 := by
      rw [Matrix.map_mul, hA₀]
      rfl
    have hr : LinearMap.range ((A γ hγ).map (residue O)).mulVecLin = W := by
      rw [← hg, ← LinearMap.range_comp, ← Matrix.mulVecLin_mul, ← Matrix.map_mul]
      refine le_antisymm (range_le_of_mul hgA (hA γ hγ) ?_) (range_le_of_mul (hA γ hγ) hgA hG.1)
      have := hG.2
      rwa [_root_.mul_inv_rev, inv_inv] at this
    exact ⟨⟨γ, hγ, (cond_iff hp z (hA γ hγ)).2 (hr ▸ hWz)⟩, Subtype.ext hr⟩

end GlobalTheory.SplitHecke.Cosets
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardSubspacesKerTransposeEqCardRangeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_subspaces_ker_transpose_eq_card_range : ∀ (k : Type) [Field k] (m n j : ℕ) (z : Matrix (Fin m) (Fin n) k), Nat.card {W : Submodule k (Fin m → k) // Module.finrank k W + j = m ∧ W ≤ LinearMap.ker zᵀ.mulVecLin} = Nat.card {W' : Submodule k (Fin m → k) // Module.finrank k W' = j ∧ LinearMap.range z.mulVecLin ≤ W'} := by
  first | exact @GlobalTheory.SplitHecke.card_le_ker_transpose_eq_card_range_le | exact GlobalTheory.SplitHecke.card_le_ker_transpose_eq_card_range_le | (intros; apply GlobalTheory.SplitHecke.card_le_ker_transpose_eq_card_range_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAdelicUnitarySplitPlaceComponentStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelic_unitary_split_place_component : ∀ {D : D7} (V : HSp D) (e : Formalism.L2.Theta.AE D), IsSplitIdem D e → ∀ m m' : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E), finPart D e • (m * m') = finPart D e • (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) → ∃ g : GA D V, Formalism.L2.Theta.SuppAt e V g ∧ finPart D e • finMat D.sp.cm.sig V.gram g = finPart D e • m := by
  first | exact @GlobalTheory.SplitLift.split_lift | exact GlobalTheory.SplitLift.split_lift | (intros; apply GlobalTheory.SplitLift.split_lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegralClopenDecompositionOfSmooth
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR KaehlerDifferential GlobalTheory.W1

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SmoothComponents

open Topology TopologicalSpace

theorem irreducibleComponent_eq_closure (Z : Scheme.{0})
    (hdom : ∀ x : Z, IsDomain (Z.presheaf.stalk x)) {C : Set Z} (hC : C ∈ irreducibleComponents Z)
    {x : Z} (hx : x ∈ C) :
    haveI := hdom x
    C = closure {Z.fromSpecStalk x (genericPoint (Spec (Z.presheaf.stalk x)))} := by
  haveI := hdom x
  set ξ := Z.fromSpecStalk x (genericPoint (Spec (Z.presheaf.stalk x)))
  have hCc : IsClosed C := isClosed_of_mem_irreducibleComponents C hC
  have hgen : IsGenericPoint hC.1.genericPoint C := by
    simpa [hCc.closure_eq] using hC.1.isGenericPoint_genericPoint_closure
  have hηx : hC.1.genericPoint ⤳ x := hgen.specializes hx
  have hmem : hC.1.genericPoint ∈ Set.range (Z.fromSpecStalk x) := by
    rw [Scheme.range_fromSpecStalk]; exact hηx
  obtain ⟨p, hp⟩ := hmem
  have hξη : ξ ⤳ hC.1.genericPoint := by
    rw [← hp]
    exact ((genericPoint_spec (Spec (Z.presheaf.stalk x))).specializes trivial).map
      (Z.fromSpecStalk x).continuous
  have hsub : C ⊆ closure {ξ} := by
    rw [← hgen.def]
    exact closure_minimal (by simpa using specializes_iff_mem_closure.mp hξη) isClosed_closure
  have hirr : IsIrreducible (closure {ξ}) := isIrreducible_singleton.closure
  exact le_antisymm hsub (hC.2 hirr hsub)

end GlobalTheory.SmoothComponents

namespace GlobalTheory.SmoothComponents

open Topology TopologicalSpace

theorem main : ∀ (Z : Scheme.{0}) (s : Z ⟶ Sp ℂ) (d : ℕ) [SmoothOfRelativeDimension d s]
    [CompactSpace Z], ∃ (J : Type) (_ : Fintype J) (V : J → Z.Opens),
      (∀ i j, i ≠ j → V i ⊓ V j = ⊥) ∧ iSup V = ⊤ ∧ ∀ j, IsIntegral (V j).toScheme := by
  intro Z s d _ _
  have hs : Smooth s := SmoothOfRelativeDimension.smooth d s
  obtain ⟨hred, -, hln⟩ :=
    isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field ℂ Z s hs
  have hdom : ∀ x : Z, IsDomain (Z.presheaf.stalk x) := fun x ↦
    (forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth s
      (isDomain_and_isIntegrallyClosed_stalk_Sp ℂ) x).1
  haveI : IsNoetherian Z := ⟨⟩
  have hfin : (irreducibleComponents Z).Finite := finite_irreducibleComponents_of_isNoetherian
  have disj : ∀ C ∈ irreducibleComponents Z, ∀ D ∈ irreducibleComponents Z, C ≠ D →
      Disjoint C D := by
    intro C hC D hD hne
    rw [Set.disjoint_left]
    intro x hxC hxD
    exact hne ((irreducibleComponent_eq_closure Z hdom hC hxC).trans
      (irreducibleComponent_eq_closure Z hdom hD hxD).symm)
  have cover : ∀ x : Z, ∃ C ∈ irreducibleComponents Z, x ∈ C := fun x ↦
    ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x,
      mem_irreducibleComponent⟩
  have hopen : ∀ C ∈ irreducibleComponents Z, IsOpen C := by
    intro C hC
    have hc : Cᶜ = ⋃ D ∈ irreducibleComponents Z \ {C}, D := by
      ext x
      simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_diff, Set.mem_singleton_iff,
        exists_prop]
      constructor
      · intro hx
        obtain ⟨D, hD, hxD⟩ := cover x
        exact ⟨D, ⟨hD, fun h ↦ hx (h ▸ hxD)⟩, hxD⟩
      · rintro ⟨D, ⟨hD, hne⟩, hxD⟩ hxC
        exact Set.disjoint_left.mp (disj D hD C hC hne) hxD hxC
    rw [← isClosed_compl_iff, hc]
    exact (hfin.subset Set.diff_subset).isClosed_biUnion fun D hD ↦ isClosed_of_mem_irreducibleComponents D hD.1
  letI : Fintype (irreducibleComponents Z) := hfin.fintype
  refine ⟨irreducibleComponents Z, inferInstance, fun C ↦ ⟨C.1, hopen C.1 C.2⟩, ?_, ?_, ?_⟩
  · intro i j hij
    apply Opens.ext
    simp only [Opens.coe_inf, Opens.coe_bot]
    exact Set.disjoint_iff_inter_eq_empty.mp (disj i.1 i.2 j.1 j.2 fun h ↦ hij (Subtype.ext h))
  · refine eq_top_iff.mpr fun x _ ↦ ?_
    rw [Opens.mem_iSup]
    obtain ⟨C, hC, hxC⟩ := cover x
    exact ⟨⟨C, hC⟩, hxC⟩
  · intro C
    have hirr : IsIrreducible C.1 := C.2.1
    haveI : IrreducibleSpace (C.1 : Set Z) := Subtype.irreducibleSpace hirr
    let U : Z.Opens := ⟨C.1, hopen C.1 C.2⟩
    change IsIntegral U.toScheme
    haveI : IrreducibleSpace U.toScheme := this
    exact isIntegral_of_irreducibleSpace_of_isReduced _

end GlobalTheory.SmoothComponents
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfInertPrimeEllipticCurveLocalData
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

namespace GlobalTheory.KerStd

theorem BeData.exists_of_curveData : ∀ (p : ℕ) [Fact p.Prime] (g2 g3 s2 ε : MaximalUnramifiedExtension p) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p)
    (F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension p)), CurveData p g2 g3 s2 ε σ F → ∀ (d : ℕ) [NeZero d], Even d →
    ∃ (om oms : Fin (d / 2) → MaximalUnramifiedExtension p) (ζ : MaximalUnramifiedExtension p), BeData p d σ F (cob F (phFF p g2 g3 s2 ε)) om oms ζ := by
  intro p _ g2 g3 s2 ε σ F hC d _ hd
  obtain ⟨-, hg2, hg3, hε, hth, hσ, hF, hN⟩ := hC
  have hff := Formalism.L2.Th1.D.FAux.ffs (l := p) Formalism.L2.Th1.D.first_level_on_curve g2 g3 ε hg2 hg3 hε hth σ hσ F hF s2 hN
  have hp : p.Prime := Fact.out
  have hd0 : d ≠ 0 := NeZero.ne d
  have h1 : 1 < p ^ d := Nat.one_lt_pow hd0 hp.one_lt
  obtain ⟨ζ, hζ⟩ := Formalism.L2.Th1.D.kurRoots p (p ^ d - 1) (by omega) (fun hdv => by
    have h2 : p ∣ p ^ d := dvd_pow_self p hd0
    have h3 : p ∣ 1 := by
      have := Nat.dvd_sub h2 hdv
      rwa [Nat.sub_sub_self h1.le] at this
    exact hp.one_lt.ne' (Nat.dvd_one.1 h3))
  obtain ⟨om, oms, hO, hT⟩ := Formalism.L2.Th1.D.trDualExists (MaximalUnramifiedExtension p) p d σ hσ hd ζ hζ
  exact ⟨om, oms, ζ, hσ, hF, hff.1, hff.2.1, hO, hT, hζ⟩

end GlobalTheory.KerStd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPlaceChartOfSplitIdempotent
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitChart

open GlobalTheory.IdemModTwo GlobalTheory.SplitIdem

variable {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {e : AE D}

def sc (he : SplitAt D v e) (z : AE D) : Fv D.host.F v := (he.exists_scalar z).choose

theorem sc_spec (he : SplitAt D v e) (z : AE D) : e * z = fj D (singleV D.host.F v (sc he z)) * e :=
  (he.exists_scalar z).choose_spec

theorem sc_eq (he : SplitAt D v e) {z : AE D} {α : Af D.host.F} (h : e * z = fj D α * e) :
    sc he z = evalV D.host.F v α := by
  rw [sc_spec he] at h
  rw [← he.scalar_inj h, evalV_singleV_same]

def comp (he : SplitAt D v e) : AE D →+* Fv D.host.F v where
  toFun := sc he
  map_one' := by rw [sc_eq he (α := 1) (by rw [he.one_mul', mul_one]), map_one]
  map_zero' := by rw [sc_eq he (α := 0) (by rw [map_zero, mul_zero, zero_mul]), map_zero]
  map_mul' x y := by
    rw [sc_eq he (α := singleV D.host.F v (sc he x) * singleV D.host.F v (sc he y)), map_mul,
      evalV_singleV_same, evalV_singleV_same]
    rw [map_mul]
    linear_combination y * sc_spec he x + fj D (singleV D.host.F v (sc he x)) * sc_spec he y
  map_add' x y := by
    rw [sc_eq he (α := singleV D.host.F v (sc he x) + singleV D.host.F v (sc he y)), map_add,
      evalV_singleV_same, evalV_singleV_same]
    rw [map_add]
    linear_combination sc_spec he x + sc_spec he y

theorem comp_apply (he : SplitAt D v e) (z : AE D) : comp he z = sc he z := rfl

theorem comp_fj (he : SplitAt D v e) (α : Af D.host.F) : comp he (fj D α) = evalV D.host.F v α :=
  sc_eq he (mul_comm _ _)

theorem comp_self (he : SplitAt D v e) : comp he e = 1 := by
  rw [comp_apply, sc_eq he (α := 1) (by rw [he.one_mul', he.1]), map_one]

theorem comp_algebraMap (he : SplitAt D v e) (y : AF D.host.F) :
    comp he (algebraMap (AF D.host.F) (AE D) y) = evalV D.host.F v y.2 := by
  rw [comp_apply, sc_eq he (α := y.2 * 1), mul_one]
  rw [← algebraMap_mul_fj, mul_assoc, he.one_mul', mul_comm]

theorem isIntegral_of_int (O : Type) {K L : Type} [CommRing O] [CommRing K] [CommRing L] [Algebra O K]
    (f : L →+* K) {x : L} (hx : IsIntegral ℤ x) : IsIntegral O (f x) :=
  (map_isIntegral_int f hx).tower_top

theorem comp_mem (he : SplitAt D v e) {z : AE D} (hz : z ∈ intL D) :
    comp he z ∈ v.adicCompletionIntegers D.host.F := by
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, o, rfl⟩ := hw
    have h1 : (pairA D.host.F 0 α ⊗ₜ[D.host.F] (o : D.host.E) : AE D) =
        fj D α * (1 : AF D.host.F) ⊗ₜ[D.host.F] (o : D.host.E) := by
      show _ = (_ ⊗ₜ _) * _
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    rw [h1, map_mul, comp_fj]
    refine mul_mem (hα v) ?_
    have h3 : IsIntegral (v.adicCompletionIntegers D.host.F)
        (comp he ((1 : AF D.host.F) ⊗ₜ[D.host.F] (o : D.host.E))) :=
      isIntegral_of_int _ ((comp he).comp
        (Algebra.TensorProduct.includeRight (R := D.host.F) (A := AF D.host.F) (B := D.host.E)).toRingHom) o.2
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h3
    rw [← hy]
    exact y.2
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

theorem finPart_mem {z : AE D} (hz : z ∈ intL D) : finPart D z ∈ intAE D := by
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, o, rfl⟩ := hw
    exact AddSubgroup.subset_closure ⟨α, hα, o, rfl⟩
  | zero => rw [RingHom.map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [RingHom.map_add]; exact add_mem hx hy
  | neg x _ hx => rw [RingHom.map_neg]; exact neg_mem hx

theorem chart_comp (he : SplitAt D v e) : Chart e v (comp he) := by
  refine ⟨fun a => ⟨fj D (singleV D.host.F v a), by rw [comp_fj, evalV_singleV_same]⟩, fun a => ⟨fun h => ?_, fun h => ?_⟩,
    comp_algebraMap he, fun a => ⟨fun h => ?_, fun h => ?_⟩⟩
  · have h0 : singleV D.host.F v 0 = 0 := by
      rw [← sub_self (0 : Fv D.host.F v), singleV_sub, sub_self]
    rw [sc_spec he, ← comp_apply, h, h0, map_zero, zero_mul]
  · rw [← one_mul (comp he a), ← comp_self he, ← map_mul, h, map_zero]
  · have h1 := comp_mem he (inF_mem h)
    rw [inF_finPart, ← mul_assoc, he.one_mul', map_mul, comp_self, one_mul] at h1
    exact isInt_Ov.2 h1
  · rw [sc_spec he]
    exact finPart_mem (fj_mul_mem (singleV_mem_intAf D.host.F v ⟨_, isInt_Ov.1 h⟩) he.mem)

theorem exists_chart : ∀ {D : D7} (e : AE D), IsSplitIdem D e →
    ∃ (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v), Chart e v π := by
  intro D e h
  obtain ⟨v, he⟩ := (isSplitIdem_iff e).1 h
  exact ⟨v, comp he, chart_comp he⟩

end GlobalTheory.SplitChart

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitSupportedUnitaryComponentStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_splitSupported_unitary_component : ∀ {D : D7} (e : AE D) (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v), IsSplitIdem D e → Chart e v π → ∀ (V : HSp D) (β x : GL (Fin V.rank) (Fv D.host.F v)), ∃ g : GA D V, SuppAt e V g ∧ rho V π β g = x := by
  first | exact @GlobalTheory.SplitOnto.exists_suppAt_rho_eq | exact GlobalTheory.SplitOnto.exists_suppAt_rho_eq | (intros; apply GlobalTheory.SplitOnto.exists_suppAt_rho_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FinrankReductionRangeAddCorankStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_reduction_range_add_corank : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] (p : O), Irreducible p → ∀ (n j : ℕ) (a : GL (Fin n) K) (A : Matrix (Fin n) (Fin n) O), j ≤ n → Hk O p j a → A.map (algebraMap O K) = a.1 → Module.finrank (IsLocalRing.ResidueField O) (LinearMap.range (A.map (IsLocalRing.residue O)).mulVecLin) + j = n := by
  first | exact @GlobalTheory.SplitHecke.finrank_range_reduction | exact GlobalTheory.SplitHecke.finrank_range_reduction | (intros; apply GlobalTheory.SplitHecke.finrank_range_reduction <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeElementComponentMemStandardDoubleCosetStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeElement_component_mem_standardDoubleCoset : ∀ {D : D7} (e : AE D) (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v), IsSplitIdem D e → Chart e v π → ∀ (V : HSp D) (β : GL (Fin V.rank) (Fv D.host.F v)), Frame V e π β → ∀ (ϖ : D.host.E) (p : Ov D v) (k : ℕ) (α : GA D V), algebraMap (Ov D v) (Fv D.host.F v) p = π (incA D ϖ) → IsHeckeElt V e ϖ k α → Hk (Ov D v) p k (rho V π β α) := by
  first | exact @GlobalTheory.SplitHecke.HeckeComp.hk_of_isHeckeElt | exact GlobalTheory.SplitHecke.HeckeComp.hk_of_isHeckeElt | (intros; apply GlobalTheory.SplitHecke.HeckeComp.hk_of_isHeckeElt <;> assumption)
end

