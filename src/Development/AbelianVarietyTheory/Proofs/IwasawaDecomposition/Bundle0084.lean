import Mathlib
import Formalism.LocalToGlobal.Divisibility.DefGroup
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsLevel
import ReciprocityTheory.Automorphisms.SplitCoeAlgebraMap
import ReciprocityTheory.GaloisValuations.Global
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTameGenAtOfValuationSubring
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0003
import Formalism.LocalToGlobal.Columns.GenericUnipotentCharacter
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0193

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReductionCompletionBlockTriLowerBlockDet
section
open NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV

namespace GlobalTheory

theorem reduction_blockTri_detDD : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : ReciprocityTheory.Aut.SplitPlace L) (φ : s.v.adicCompletionIntegers (maximalRealSubfield L) →+* kP s.w) (n r : ℕ) (h : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) (g : GL (Fin n) (kP s.w)), (∀ x, φ x = 0 ↔ Valued.v (x : s.v.adicCompletion (maximalRealSubfield L)) < 1) → (∀ a b, ∃ hab : (h : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) a b ∈ s.v.adicCompletionIntegers (maximalRealSubfield L), (g : Matrix (Fin n) (Fin n) (kP s.w)) a b = φ ⟨_, hab⟩) → (g ∈ blockTri (blk2 r) ↔ ∀ a b : Fin n, r ≤ a.val → b.val < r → Valued.v ((h : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) a b) < 1) ∧ (g ∈ blockTri (blk2 r) → ∃ hd : NG.detDD s r h ∈ s.v.adicCompletionIntegers (maximalRealSubfield L), ((dBlk (blk2 r) 1 g : (kP s.w)ˣ) : kP s.w) = φ ⟨_, hd⟩) := by
  intro L _ _ _ s φ n r h g hφ hg
  have key : ∀ a b, (g : Matrix (Fin n) (Fin n) (kP s.w)) a b = 0 ↔
      Valued.v ((h : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) a b) < 1 := by
    intro a b
    obtain ⟨hab, e⟩ := hg a b
    rw [e, hφ]
  refine ⟨?_, ?_⟩
  · rw [mem_blockTri]
    constructor
    · intro H a b ha hb
      rw [← key]
      apply H
      simp [blk2, hb, Nat.not_lt.mpr ha]
    · intro H i j hij
      rw [key]
      unfold blk2 at hij
      by_cases hj : j.val < r
      · by_cases hi : i.val < r
        · simp [hj, hi] at hij
        · exact H i j (Nat.not_lt.mp hi) hj
      · by_cases hi : i.val < r <;> simp [hj, hi] at hij
  · intro hT
    let M : Matrix {x : Fin n // r ≤ x.val} {x : Fin n // r ≤ x.val} (s.v.adicCompletionIntegers (maximalRealSubfield L)) :=
      fun a b => ⟨(h : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) a.1 b.1, (hg a.1 b.1).1⟩
    have hdet : NG.detDD s r h = (s.v.adicCompletionIntegers (maximalRealSubfield L)).subtype M.det := by
      rw [RingHom.map_det]
      rfl
    refine ⟨hdet ▸ (M.det).2, ?_⟩
    have e1 : (⟨NG.detDD s r h, hdet ▸ (M.det).2⟩ : s.v.adicCompletionIntegers (maximalRealSubfield L)) = M.det :=
      Subtype.ext hdet
    rw [e1, RingHom.map_det, diag_block_det_val 1 hT]
    let e : {a : Fin n // blk2 r a = 1} ≃ {x : Fin n // r ≤ x.val} :=
      Equiv.subtypeEquivRight (fun a => by
        unfold blk2
        split_ifs with h'
        · exact ⟨fun h0 => absurd h0 (by decide), fun h0 => absurd h' (Nat.not_lt.mpr h0)⟩
        · exact ⟨fun _ => Nat.not_lt.mp h', fun _ => rfl⟩)
    rw [← Matrix.det_submatrix_equiv_self e]
    congr 1
    ext a b
    simp only [Matrix.submatrix_apply, Matrix.map_apply, M]
    exact (hg (e a).1 (e b).1).2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootEqOfClose
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.TameTau

theorem root_eq_of_close {Ω : Type*} [Field Ω] (A : ValuationSubring Ω) (m : ℕ) {ζ ζ' : Ω}
    (h : ζ ^ m = 1) (h' : ζ' ^ m = 1) (hm : ¬ A.valuation (m : Ω) < 1)
    (hc : A.valuation (ζ - ζ') < 1) : ζ = ζ' := by
  first
  | exact @_root_.GlobalTheory.PowEqOneValuation.eq_of_pow_eq_one_of_valuation_sub_lt_one
  | exact _root_.GlobalTheory.PowEqOneValuation.eq_of_pow_eq_one_of_valuation_sub_lt_one
  | (apply _root_.GlobalTheory.PowEqOneValuation.eq_of_pow_eq_one_of_valuation_sub_lt_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.PowEqOneValuation.eq_of_pow_eq_one_of_valuation_sub_lt_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PowEqOneValuation.eq_of_pow_eq_one_of_valuation_sub_lt_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PowEqOneValuation.eq_of_pow_eq_one_of_valuation_sub_lt_one ..)

theorem ine_fix_root {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {A : ValuationSubring Ω}
    {σ : G E Ω} (hσ : σ ∈ Ine (F := E) A) (m : ℕ) (hm : ¬ A.valuation (m : Ω) < 1) {ζ : Ω} (hζ : ζ ^ m = 1) :
    σ ζ = ζ := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (by simp)
  refine root_eq_of_close A m (by rw [← map_pow, hζ, map_one]) hζ hm ?_
  exact hσ.2 ζ (valuation_eq_one_of_pow_eq_one A hm0 hζ).le

theorem quot_mul {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {A : ValuationSubring Ω}
    {σ τ : G E Ω} (hσ : σ ∈ Ine (F := E) A) (m : ℕ) (hm : ¬ A.valuation (m : Ω) < 1) {π : Ω} (hπ : π ≠ 0)
    {e : E} (he : π ^ m = algebraMap E Ω e) :
    (σ * τ) π / π = (σ π / π) * (τ π / π) := by
  have hτ : (τ π / π) ^ m = 1 := by
    rw [div_pow, ← map_pow, he, AlgEquiv.commutes, ← he, div_self (pow_ne_zero _ hπ)]
  have hfix := ine_fix_root hσ m hm hτ
  have e1 : τ π = (τ π / π) * π := by field_simp
  have e2 : (σ * τ) π = σ (τ π / π) * σ π := by
    rw [AlgEquiv.mul_apply, ← map_mul, div_mul_cancel₀ _ hπ]
  rw [e2, hfix]
  field_simp

end GlobalTheory.TameTau
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SecondBlockDetEqBlockDetOfSumPartitions
section
open NumberField IsDedekindDomain

namespace GlobalTheory

theorem blkOf_eq_coarse {n r t : ℕ} (hn : n = r + t) :
    (Formalism.L2.DIV.blkOf r t : Fin n → ℕ) = fun a => Formalism.L2.Col.coarse r [t] a.val := by
  funext a
  have ha := a.isLt
  by_cases h : a.val < r
  · rw [Formalism.L2.Col.coarse_of_lt h]; simp [Formalism.L2.DIV.blkOf, h]
  · rw [Formalism.L2.Col.coarse_of_le (Nat.not_lt.mp h)]
    have h2 : a.val - r < t := by omega
    simp [Formalism.L2.DIV.blkOf, h, Formalism.L2.Col.blkIdx, h2, Nat.div_eq_of_lt h2]

theorem twoBlocks_eq_coarse_of_add {n r t : ℕ} (hn : n = r + t) :
    (Formalism.L2.DIV.blk2 r : Fin n → ℕ) = fun a => Formalism.L2.Col.coarse r [t] a.val := by
  funext a
  have ha := a.isLt
  by_cases h : a.val < r
  · rw [Formalism.L2.Col.coarse_of_lt h]; simp [Formalism.L2.DIV.blk2, h]
  · rw [Formalism.L2.Col.coarse_of_le (Nat.not_lt.mp h)]
    have h2 : a.val - r < t := by omega
    simp [Formalism.L2.DIV.blk2, h, Formalism.L2.Col.blkIdx, h2]

theorem lowerBlockDet_coarse_partition_eq_blockDet_upperTri {κ : Type} [CommRing κ] {n r t : ℕ} (g : GL (Fin n) κ)
    (hg : g ∈ Formalism.L2.Col.blockUT n κ r [t]) :
    Formalism.L2.DIV.dBlk (fun a : Fin n => Formalism.L2.Col.coarse r [t] a.val) 1 g =
      Formalism.L2.Col.blkDet n κ (Formalism.L2.Col.coarse r [t]) 1 ⟨g, hg⟩ := by
  have hg' : g ∈ Formalism.L2.DIV.blockTri (fun a : Fin n => Formalism.L2.Col.coarse r [t] a.val) := hg
  apply Units.ext
  rw [Formalism.L2.DIV.diag_block_det_val 1 hg', Formalism.L2.Col.blkDet_val]
  rfl

theorem secondBlockDet_eq_blockDet_of_sum_partitions : ∀ {κ : Type} [CommRing κ] {n r t : ℕ}, n = r + t → ∀ (g : GL (Fin n) κ) (hg : g ∈ Formalism.L2.Col.blockUT n κ r [t]),
    Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf r t) 1 g = Formalism.L2.Col.blkDet n κ (Formalism.L2.Col.coarse r [t]) 1 ⟨g, hg⟩ ∧
      Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blk2 r) 1 g = Formalism.L2.Col.blkDet n κ (Formalism.L2.Col.coarse r [t]) 1 ⟨g, hg⟩ := by
  intro κ _ n r t hn g hg
  refine ⟨?_, ?_⟩
  · rw [blkOf_eq_coarse hn]; exact lowerBlockDet_coarse_partition_eq_blockDet_upperTri g hg
  · rw [twoBlocks_eq_coarse_of_add hn]; exact lowerBlockDet_coarse_partition_eq_blockDet_upperTri g hg

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopBlockEqOneIffMemColHK
section
open NumberField IsDedekindDomain

namespace GlobalTheory

theorem topBlock_eq_one_iff_mem_colHK : ∀ {κ : Type} [CommRing κ] {n r t : ℕ}, n = r + t → ∀ (hr : r ≤ n) (g : GL (Fin n) κ),
    g ∈ Formalism.L2.Col.blockUT n κ r [t] → (Formalism.L2.DIV.upperLeftBlock hr g = 1 ↔ g ∈ Formalism.L2.Col.HK n κ r [t]) := by
  intro κ _ n r t _ hr g hg
  have hb : g ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 (n := n) r) := by
    refine Formalism.L2.DIV.mem_blockTri.2 fun i j hij => ?_
    have hji : j.val < r ∧ ¬ i.val < r := by
      unfold Formalism.L2.DIV.blk2 at hij
      by_cases hj : j.val < r <;> by_cases hi : i.val < r <;> simp [hj, hi] at hij ⊢
    refine hg (show Formalism.L2.Col.coarse r [t] j.val < Formalism.L2.Col.coarse r [t] i.val from ?_)
    rw [Formalism.L2.Col.coarse_of_lt hji.1, Formalism.L2.Col.coarse_of_le (Nat.not_lt.mp hji.2)]
    exact Nat.succ_pos _
  rw [Formalism.L2.Col.mem_HK, Units.ext_iff, Formalism.L2.DIV.upper_block_val_submatrix hr hb, Units.val_one]
  constructor
  · intro h
    refine ⟨hg, fun i j hi hj => ?_⟩
    have h1 := congrFun (congrFun h ⟨i.val, hi⟩) ⟨j.val, hj⟩
    simp only [Matrix.submatrix_apply, Matrix.one_apply, Fin.mk.injEq] at h1
    rw [Matrix.one_apply]
    simp only [Fin.ext_iff]
    exact h1
  · rintro ⟨-, h⟩
    ext i j
    rw [Matrix.submatrix_apply, h _ _ i.2 j.2]
    simp [Matrix.one_apply]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuationApplyOfWild
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module GlobalTheory.WeilDeligne

namespace GlobalTheory.TameCharUnique
open scoped Pointwise

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]

open NumberField IsDedekindDomain Polynomial Module in
open scoped Pointwise in
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] in

theorem _root_.GlobalTheory.TameCharUnique.mem_Ine_of_wild {A : ValuationSubring Ω} {σ : _root_.Formalism.ConjugateSelfDual.G E Ω}
    (hσ : ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) : σ ∈ _root_.ReciprocityTheory.Gal.Ine (F := E) A := by
  have hval : ∀ y : Ω, A.valuation (σ y) = A.valuation y := by
    intro y
    rcases eq_or_ne y 0 with rfl | hy
    · simp
    · have h1 : A.valuation (σ y / y) = 1 := by
        have := A.valuation.map_one_add_of_lt (hσ y hy)
        rwa [add_sub_cancel] at this
      have h2 : σ y = σ y / y * y := (div_mul_cancel₀ _ hy).symm
      rw [h2, map_mul, h1, one_mul]
  rw [_root_.ReciprocityTheory.Gal.mem_Ine]
  unfold _root_.Formalism.ConjugateSelfDual.Inertia
  refine ⟨?_, fun x hx => ?_⟩
  · change (σ : Gal(Ω/E)) • A = A
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← A.valuation_le_one_iff,
      ← A.valuation_le_one_iff, AlgEquiv.smul_def]
    have hx := hval (σ⁻¹ x)
    rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply] at hx
    rw [← hx]
  · rcases eq_or_ne x 0 with rfl | hx0
    · simp
    · have hsplit : σ x - x = (σ x / x - 1) * x := by
        rw [sub_mul, div_mul_cancel₀ _ hx0, one_mul]
      rw [hsplit, map_mul]
      calc A.valuation (σ x / x - 1) * A.valuation x ≤ A.valuation (σ x / x - 1) :=
            mul_le_of_le_one_right' hx
        _ < 1 := hσ x hx0

variable [IsAlgClosure E Ω]

open NumberField IsDedekindDomain Polynomial Module in
open scoped Pointwise in
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] in
variable [IsAlgClosure E Ω] in

theorem _root_.GlobalTheory.TameCharUnique.mem_of_tameGen {A : ValuationSubring Ω} {γ : _root_.Formalism.ConjugateSelfDual.G E Ω}
    (hγ : _root_.Formalism.BasicNotions.TameGenAt A γ)
    (S : Subgroup (_root_.ReciprocityTheory.Gal.Ine (F := E) A)) (hS : IsClosed (S : Set (_root_.ReciprocityTheory.Gal.Ine (F := E) A)))
    (h1 : (⟨γ, hγ.1⟩ : _root_.ReciprocityTheory.Gal.Ine (F := E) A) ∈ S)
    (h2 : ∀ σ : _root_.ReciprocityTheory.Gal.Ine (F := E) A, (∀ y : Ω, y ≠ 0 → A.valuation (σ.1 y / y - 1) < 1) → σ ∈ S)
    (σ : _root_.ReciprocityTheory.Gal.Ine (F := E) A) : σ ∈ S := by
  obtain ⟨C, hC, hCS⟩ := (Topology.IsInducing.subtypeVal.isClosed_iff).mp hS
  have hmapC : ((S.map (_root_.ReciprocityTheory.Gal.Ine (F := E) A).subtype : Subgroup (_root_.Formalism.ConjugateSelfDual.G E Ω)) :
      Set (_root_.Formalism.ConjugateSelfDual.G E Ω)) ⊆ C := by
    rintro _ ⟨τ, hτ, rfl⟩
    exact (Set.ext_iff.mp hCS τ).mpr hτ
  have hle : Subgroup.closure (insert γ {τ : _root_.Formalism.ConjugateSelfDual.G E Ω |
      ∀ y : Ω, y ≠ 0 → A.valuation (τ y / y - 1) < 1}) ≤ S.map (_root_.ReciprocityTheory.Gal.Ine (F := E) A).subtype := by
    rw [Subgroup.closure_le]
    rintro τ (rfl | hτ)
    · exact ⟨_, h1, rfl⟩
    · exact ⟨⟨τ, _root_.GlobalTheory.TameCharUnique.mem_Ine_of_wild hτ⟩, h2 _ hτ, rfl⟩
  have hσC : (σ : _root_.Formalism.ConjugateSelfDual.G E Ω) ∈ C :=
    closure_minimal ((SetLike.coe_subset_coe.mpr hle).trans hmapC) hC (hγ.2 σ.2)
  exact (Set.ext_iff.mp hCS σ).mp hσC

open NumberField IsDedekindDomain Polynomial Module in
open scoped Pointwise in
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] in
variable [IsAlgClosure E Ω] in
private lemma exists_pow_fixes_finiteDimensional (K : IntermediateField E Ω)
    [FiniteDimensional E K] (τ : Gal(Ω/E)) : ∃ m : ℕ, 0 < m ∧ ∀ x ∈ K, (τ ^ m) x = x := by
  obtain ⟨i, j, hij, heq⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun n : ℕ => ((τ ^ n : Gal(Ω/E)).toAlgHom.comp K.val : K →ₐ[E] Ω))
  have hfix : ∀ a b : ℕ, a < b → (∀ x ∈ K, (τ ^ a) x = (τ ^ b) x) →
      ∃ m : ℕ, 0 < m ∧ ∀ x ∈ K, (τ ^ m) x = x := by
    intro a b hab hx
    refine ⟨b - a, Nat.sub_pos_of_lt hab, fun x hxK => ?_⟩
    apply (τ ^ a).injective
    rw [← AlgEquiv.mul_apply, ← pow_add, Nat.add_sub_cancel' hab.le]
    exact (hx x hxK).symm
  have hij' : ∀ x ∈ K, (τ ^ i) x = (τ ^ j) x := fun x hx => by
    simpa using DFunLike.congr_fun heq ⟨x, hx⟩
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · exact hfix i j h hij'
  · exact hfix j i h fun x hx => (hij' x hx).symm

open NumberField IsDedekindDomain Polynomial Module in
open scoped Pointwise in
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] in
variable [IsAlgClosure E Ω] in

theorem _root_.GlobalTheory.TameCharUnique.eq_zero_of_wild {A : ValuationSubring Ω}
    {w : HeightOneSpectrum (𝓞 E)} (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w)
    {l : ℕ} [Fact l.Prime] (hlw : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal)
    (t : _root_.ReciprocityTheory.Gal.Ine (F := E) A →* Multiplicative ℤ_[l]) (ht : Continuous t)
    (σ : _root_.ReciprocityTheory.Gal.Ine (F := E) A)
    (hσ : ∀ y : Ω, y ≠ 0 → A.valuation (σ.1 y / y - 1) < 1) : (t σ).toAdd = 0 := by
  have hl1 : l ≠ 1 := (Fact.out : l.Prime).ne_one
  rw [← norm_eq_zero]
  refine le_antisymm (le_of_forall_pos_lt_add fun ε hε => ?_) (norm_nonneg _)
  rw [zero_add]
  have hUo : IsOpen (t ⁻¹' {x : Multiplicative ℤ_[l] | ‖x.toAdd‖ < ε}) :=
    (isOpen_lt (continuous_norm.comp continuous_toAdd) continuous_const).preimage ht
  obtain ⟨V, hVo, hVU⟩ := (Topology.IsInducing.subtypeVal.isOpen_iff).mp hUo
  have h1V : (1 : Gal(Ω/E)) ∈ V := by
    have h1U : (1 : _root_.ReciprocityTheory.Gal.Ine (F := E) A) ∈ t ⁻¹' {x : Multiplicative ℤ_[l] | ‖x.toAdd‖ < ε} := by
      simp [hε]
    rw [← hVU] at h1U
    exact h1U
  obtain ⟨K, hK, hKV⟩ := (krullTopology_mem_nhds_one_iff E Ω V).mp (hVo.mem_nhds h1V)
  obtain ⟨m, hm0, hmK⟩ := exists_pow_fixes_finiteDimensional K σ.1
  obtain ⟨e, m', hlm', hm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm0.ne' l hl1
  have hτ := _root_.GlobalTheory.WildInertiaChar.wild_pow A σ.1 hσ m'
  have hfix : (σ ^ m' : _root_.ReciprocityTheory.Gal.Ine (F := E) A).1 ∈ K.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    rw [Subgroup.coe_pow]
    refine _root_.GlobalTheory.WildInertiaChar.fixed_of_pow_fixed A _ hτ (l ^ e) (_root_.ReciprocityTheory.Gal.not_valuation_lt_one_of_isPlaceOver hlw h e) x ?_
    rw [← pow_mul, mul_comm, ← hm]
    exact hmK x hx
  have hmem : σ ^ m' ∈ t ⁻¹' {x : Multiplicative ℤ_[l] | ‖x.toAdd‖ < ε} := by
    rw [← hVU]
    exact hKV hfix
  have hnorm : ‖(t (σ ^ m')).toAdd‖ < ε := hmem
  rwa [map_pow, toAdd_pow, nsmul_eq_mul, norm_mul,
    PadicInt.norm_natCast_eq_one_iff.mpr ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hlm'),
    one_mul] at hnorm

open NumberField IsDedekindDomain Polynomial Module in
open scoped Pointwise in
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] in
variable [IsAlgClosure E Ω] in

theorem _root_.GlobalTheory.TameCharUnique.exists_eq_mul : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w) (l : ℕ) [Fact l.Prime], ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ (t t' : _root_.ReciprocityTheory.Gal.Ine (F := E) A →* Multiplicative ℤ_[l]), Continuous t → Continuous t' → Function.Surjective t' → ∃ c : ℤ_[l], ∀ σ, (t σ).toAdd = c * (t' σ).toAdd := by
  intro E Ω _ _ _ _ _ A w h l _ hlw t t' ht ht' hsurj
  obtain ⟨γ, hγ⟩ := _root_.GlobalTheory.TameInertiaGen.exists_tameGenAt_of_valuationSubring (E := E) A
  have hwild : ∀ s : _root_.ReciprocityTheory.Gal.Ine (F := E) A →* Multiplicative ℤ_[l], Continuous s →
      ∀ σ : _root_.ReciprocityTheory.Gal.Ine (F := E) A, (∀ y : Ω, y ≠ 0 → A.valuation (σ.1 y / y - 1) < 1) →
        s σ = 1 := by
    intro s hs σ hσ
    rw [← toAdd_eq_zero]
    exact _root_.GlobalTheory.TameCharUnique.eq_zero_of_wild h hlw s hs σ hσ
  have hb : IsUnit (t' ⟨γ, hγ.1⟩).toAdd := by
    by_contra hb
    let S : Subgroup (_root_.ReciprocityTheory.Gal.Ine (F := E) A) :=
      { carrier := {σ | ‖(t' σ).toAdd‖ ≤ (l : ℝ) ^ (-1 : ℤ)}
        mul_mem' := fun {a b} ha hb => by
          simp only [Set.mem_setOf_eq, map_mul, toAdd_mul] at *
          exact (PadicInt.nonarchimedean _ _).trans (max_le ha hb)
        one_mem' := by simp
        inv_mem' := fun {a} ha => by simpa using ha }
    have hS : IsClosed (S : Set (_root_.ReciprocityTheory.Gal.Ine (F := E) A)) :=
      isClosed_le (continuous_norm.comp (continuous_toAdd.comp ht')) continuous_const
    have hγS : (⟨γ, hγ.1⟩ : _root_.ReciprocityTheory.Gal.Ine (F := E) A) ∈ S := by
      show ‖(t' ⟨γ, hγ.1⟩).toAdd‖ ≤ (l : ℝ) ^ (-1 : ℤ)
      rw [PadicInt.norm_le_pow_iff_norm_lt_pow_add_one]
      rw [PadicInt.isUnit_iff] at hb
      norm_num
      exact lt_of_le_of_ne (PadicInt.norm_le_one _) hb
    have hall : ∀ σ, σ ∈ S := fun σ =>
      _root_.GlobalTheory.TameCharUnique.mem_of_tameGen hγ S hS hγS
        (fun τ hτ => by
          show ‖(t' τ).toAdd‖ ≤ (l : ℝ) ^ (-1 : ℤ)
          rw [hwild t' ht' τ hτ]
          simp) σ
    obtain ⟨σ, hσ⟩ := hsurj (Multiplicative.ofAdd 1)
    have h1 : ‖(t' σ).toAdd‖ ≤ (l : ℝ) ^ (-1 : ℤ) := hall σ
    rw [hσ, toAdd_ofAdd, norm_one, zpow_neg_one] at h1
    have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
    exact absurd h1 (not_le.mpr (inv_lt_one_of_one_lt₀ hl))
  refine ⟨(t ⟨γ, hγ.1⟩).toAdd * ↑hb.unit⁻¹, fun σ => ?_⟩
  let f : _root_.ReciprocityTheory.Gal.Ine (F := E) A →* Multiplicative ℤ_[l] :=
    (AddMonoidHom.toMultiplicative
      (AddMonoidHom.mulLeft ((t ⟨γ, hγ.1⟩).toAdd * ↑hb.unit⁻¹))).comp t'
  have hf : Continuous f := by
    show Continuous fun τ => Multiplicative.ofAdd
      ((t ⟨γ, hγ.1⟩).toAdd * ↑hb.unit⁻¹ * (t' τ).toAdd)
    exact continuous_ofAdd.comp (continuous_const.mul (continuous_toAdd.comp ht'))
  have hγmem : (⟨γ, hγ.1⟩ : _root_.ReciprocityTheory.Gal.Ine (F := E) A) ∈ MonoidHom.eqLocus t f := by
    show t ⟨γ, hγ.1⟩ = f ⟨γ, hγ.1⟩
    apply Multiplicative.toAdd.injective
    show (t ⟨γ, hγ.1⟩).toAdd = (t ⟨γ, hγ.1⟩).toAdd * ↑hb.unit⁻¹ * (t' ⟨γ, hγ.1⟩).toAdd
    rw [mul_assoc, IsUnit.val_inv_mul, mul_one]
  have hwmem : ∀ τ : _root_.ReciprocityTheory.Gal.Ine (F := E) A,
      (∀ y : Ω, y ≠ 0 → A.valuation (τ.1 y / y - 1) < 1) → τ ∈ MonoidHom.eqLocus t f := by
    intro τ hτ
    show t τ = f τ
    simp [f, hwild t ht τ hτ, hwild t' ht' τ hτ]
  have hmem := _root_.GlobalTheory.TameCharUnique.mem_of_tameGen hγ (MonoidHom.eqLocus t f)
    (isClosed_eq ht hf) hγmem hwmem σ
  exact congrArg Multiplicative.toAdd hmem

end GlobalTheory.TameCharUnique
end

