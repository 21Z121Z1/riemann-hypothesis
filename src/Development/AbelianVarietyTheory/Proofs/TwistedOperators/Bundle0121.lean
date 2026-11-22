import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0119
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0112
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowerKTypesPTensorStableUnderK
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0092
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0120
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0044
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0060
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0059
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ValTwoBlockParahoricInfTorusConjBlockwiseStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0071

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubleCoverUpqKsetGeneratedByExpStatement
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubleCoverUpq_Kset_generated_by_exp : ∀ (p q : ℕ), 1 ≤ p + q → ∀ (T : GrpData p q), ∀ k ∈ T.Kset, k ∈ Subgroup.closure (T.expt '' {Y | Y ∈ upq p q ∧ IsKC Y}) := by
  first | exact @GlobalTheory.CoverKGen.kset_gen | exact GlobalTheory.CoverKGen.kset_gen | (intros; apply GlobalTheory.CoverKGen.kset_gen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockOnePlaceIsoDirectSumPartitionsStatement
section
open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockOnePlace_iso_directSum_partitions : ∀ (a b : ℕ) (α β : ℤ), Iso (Representation.directSum fun i : GlobalTheory.GLDuality.Part (min a b) => Representation.tprod ((twist (detU a ^ α) ((irr a (GlobalTheory.GLDuality.pad a i)).comp (conjU a))).comp (MonoidHom.fst (U a) (U b))) ((twist (detU b ^ β) (irr b (GlobalTheory.GLDuality.pad b i))).comp (MonoidHom.snd (U a) (U b)))) (fockOne a b α β) := by
  first | exact @GlobalTheory.OneFunctional.iso_directSum_fockOne | exact GlobalTheory.OneFunctional.iso_directSum_fockOne | (intros; apply GlobalTheory.OneFunctional.iso_directSum_fockOne <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowerKTypesPTensorStableUnderKStatement
section
open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowerKTypes_pTensor_stable_under_K : ∀ (V W : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (Λ : Fin n → ℝ) (u : V) (j : W →ₗᵢ[ℂ] V) (τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (w : W), LowData ε E Λ u j → IsTau ε Λ τ w → TauTie ε E j τ → ∀ G : Fin n × Fin n → W, arr1 j G ∈ Vminus ε E Λ u → ∀ k ∈ Kset ε, ∃ G' : Fin n × Fin n → W, arr1 j G' ∈ Vminus ε E Λ u ∧ ∑ p, ⟪τ k w, G p⟫_ℂ • (k⁻¹ * thE ε p * k) = ∑ p, ⟪w, G' p⟫_ℂ • thE ε p := by
  first | exact @GlobalTheory.SphJet.vminus_stable_under_K | exact GlobalTheory.SphJet.vminus_stable_under_K | (intros; apply GlobalTheory.SphJet.vminus_stable_under_K <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OuterTensorFockOnePlaceIsoUnitaryFockStatement
section
open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.outerTensor_fockOnePlace_iso_unitaryFock : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (a b : ℕ) (α β : ι → ℤ), Iso (outer₂ fun τ => fockOne a b (α τ) (β τ)) (fock a b α β) := by
  first | exact @GlobalTheory.OneFunctional.FockTensor.outer₂_fockOne_iso | exact GlobalTheory.OneFunctional.FockTensor.outer₂_fockOne_iso | (intros; apply GlobalTheory.OneFunctional.FockTensor.outer₂_fockOne_iso <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairKEquivariantOfLieAlgebraCompatStatement
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_kEquivariant_of_lieAlgebra_compat : ∀ (p q : ℕ) (T : GrpData p q), (∀ k ∈ T.Kset, k ∈ Subgroup.closure (T.expt '' {Y | Y ∈ upq p q ∧ IsKC Y})) → ∀ (π₁ π₂ : URep T) (E : Type) [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E] (a : Mat p q → E →ₗ[ℂ] E) (j₁ : E →ₗ[ℂ] π₁.H) (j₂ : E →ₗ[ℂ] π₂.H), (∀ Y ∈ upq p q, IsKC Y → ∀ w, HasDerivAt (fun t : ℝ => π₁.π (T.expt (t • Y)) (j₁ w)) (j₁ (a Y w)) 0 ∧ HasDerivAt (fun t : ℝ => π₂.π (T.expt (t • Y)) (j₂ w)) (j₂ (a Y w)) 0) → (∀ k ∈ T.Kset, ∀ w : E, ∃ w' : E, π₁.π k (j₁ w) = j₁ w' ∧ π₂.π k (j₂ w) = j₂ w') := by
  first | exact @GlobalTheory.RealPar.pair_kEquivariant_of_lie | exact GlobalTheory.RealPar.pair_kEquivariant_of_lie | (intros; apply GlobalTheory.RealPar.pair_kEquivariant_of_lie <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexConjParahoric
section
noncomputable section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition

namespace GlobalTheory.ParahoricConjugateOpen

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isOpen_conj_inf {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (H : Subgroup G)
    (hH : IsOpen (H : Set G)) (g : G) :
    IsOpen ((H.map (MulAut.conj g).toMonoidHom ⊓ H : Subgroup G) : Set G) := by
  rw [Subgroup.coe_inf]
  refine IsOpen.inter ?_ hH
  have : ((H.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) = (fun x => g⁻¹ * x * g) ⁻¹' (H : Set G) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [mul_assoc] using hy
    · intro hx
      exact ⟨_, hx, by simp [mul_assoc]⟩
  rw [this]
  exact hH.preimage (by fun_prop)

theorem isOpen_KO (n : Type) [Fintype n] [DecidableEq n] : IsOpen (KO k n : Set (GL n k)) :=
  Subgroup.isOpen_mono StepData.KOne_le_KO StepData.isOpen_KOne

theorem isOpen_parahoric (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] :
    IsOpen (parahoric k A D : Set (GL (A ⊕ D) k)) := by
  refine Subgroup.isOpen_mono (H₁ := KOne k (A ⊕ D)) (fun g hg => ?_) StepData.isOpen_KOne
  refine mem_parahoric.2 ⟨StepData.KOne_le_KO hg, fun i j => ?_⟩
  simpa using StepData.mem_KOne.1 hg (.inr i) (.inl j)

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem torusElt_zero (n : Type) [Fintype n] [DecidableEq n] (ϖ : kˣ) :
    torusElt k n ϖ (fun _ => 0) = 1 := by
  refine Units.ext ?_
  rw [val_torusElt]
  simp

theorem conj_one_inf {G : Type} [Group G] (H : Subgroup G) :
    (H.map (MulAut.conj (1 : G)).toMonoidHom ⊓ H : Subgroup G) = H := by
  have : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by ext x; simp
  rw [this, Subgroup.map_id, inf_idem]

theorem vol_conj_inf [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ϖ : kˣ)
    (hϖ : valuation k (ϖ : k) = uniformizer k)
    (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (e : D → ℤ) :
    (volM ν (A ⊕ D) (A ⊕ D) (Units.val ''
      (((parahoric k A D).map (MulAut.conj (mtor (A := A) ϖ e)).toMonoidHom ⊓ parahoric k A D :
        Subgroup (GL (A ⊕ D) k)) : Set (GL (A ⊕ D) k)))).toReal =
      (volM ν A A (Units.val '' (KO k A : Set (GL A k)))).toReal *
        (ν (𝒪[k] : Set k)).toReal ^ (2 * (Fintype.card A * Fintype.card D)) *
        (resCard k : ℝ) ^ (-((Fintype.card A : ℤ) * (Fintype.card D + sumAbs e))) *
        (volM ν D D (Units.val '' (((KO k D).map (MulAut.conj (torusElt k D ϖ e)).toMonoidHom ⊓ KO k D :
          Subgroup (GL D k)) : Set (GL D k)))).toReal := by
  have hq : (0 : ℝ) < resCard k := Nat.cast_pos.2 Nat.card_pos
  have h1 := GlobalTheory.T.matrixEntrywiseProductMeasure_uniformizer_power_box k ν ϖ hϖ A D (fun _ j => max 0 (-e j))
  have h2 := GlobalTheory.T.matrixEntrywiseProductMeasure_uniformizer_power_box k ν ϖ hϖ D A (fun i _ => 1 + max 0 (e i))
  rw [GlobalTheory.T.val_twoBlockParahoric_inf_torusConj_blockwise k ϖ hϖ A D e, GlobalTheory.T.volM_blocks_eq_mul, h1, h2]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal (zpow_pos hq _).le]
  have hs : -((Fintype.card A : ℤ) * (Fintype.card D + sumAbs e)) =
      (-∑ _i : A, ∑ j : D, max 0 (-e j)) + (-∑ i : D, ∑ _j : A, (1 + max 0 (e i))) := by
    have : sumAbs e = ∑ j : D, max 0 (-e j) + ∑ j : D, max 0 (e j) := by
      rw [sumAbs, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rcases le_total 0 (e j) with h | h
      · rw [abs_of_nonneg h, max_eq_left (by omega), max_eq_right h]; ring
      · rw [abs_of_nonpos h, max_eq_right (by omega), max_eq_left h]; ring
    rw [this, Finset.sum_comm (s := (Finset.univ : Finset D))]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.sum_add_distrib]
    ring
  rw [hs, zpow_add₀ hq.ne', mul_comm (Fintype.card D) (Fintype.card A)]
  ring

theorem relIndex_conj_parahoric (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ϖ : kˣ) (hϖ : valuation k (ϖ : k) = uniformizer k)
    (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (e : D → ℤ) :
    ((((parahoric k A D).map (MulAut.conj (mtor (A := A) ϖ e)).toMonoidHom).relIndex (parahoric k A D) : ℕ) : ℝ) =
      (resCard k : ℝ) ^ ((Fintype.card A : ℤ) * sumAbs e) *
        ((((KO k D).map (MulAut.conj (torusElt k D ϖ e)).toMonoidHom).relIndex (KO k D) : ℕ) : ℝ) := by
  borelize k
  let ν : Measure k := Measure.addHaar
  have hq : (0 : ℝ) < resCard k := Nat.cast_pos.2 Nat.card_pos
  obtain ⟨hp, hJ⟩ := GlobalTheory.T.relIndex_mul_matrixVolume_open_subgroup_integralGL k ν (A ⊕ D) _ (parahoric k A D) inf_le_right
    (fun g hg => (mem_parahoric.1 hg).1) (isOpen_conj_inf _ (isOpen_parahoric A D) (mtor (A := A) ϖ e))
  obtain ⟨-, hK⟩ := GlobalTheory.T.relIndex_mul_matrixVolume_open_subgroup_integralGL k ν D _ (KO k D) inf_le_right le_rfl
    (isOpen_conj_inf _ (isOpen_KO D) (torusElt k D ϖ e))
  rw [Subgroup.inf_relIndex_right] at hJ hK
  have h0 := vol_conj_inf ν ϖ hϖ A D (fun _ => 0)
  have hm : mtor (A := A) ϖ (fun _ : D => 0) = 1 := by
    rw [← torusElt_zero (A ⊕ D) ϖ, mtor]
    congr 1
    funext x
    cases x <;> rfl
  rw [hm, torusElt_zero, conj_one_inf, conj_one_inf] at h0
  refine mul_right_cancel₀ hp.ne' ?_
  rw [hJ, h0, ← hK, vol_conj_inf ν ϖ hϖ A D e]
  have hs : sumAbs (fun _ : D => (0 : ℤ)) = 0 := by simp [sumAbs]
  have hz : (resCard k : ℝ) ^ (-((Fintype.card A : ℤ) * (Fintype.card D + sumAbs (fun _ : D => (0 : ℤ))))) =
      (resCard k : ℝ) ^ ((Fintype.card A : ℤ) * sumAbs e) *
        (resCard k : ℝ) ^ (-((Fintype.card A : ℤ) * (Fintype.card D + sumAbs e))) := by
    rw [← zpow_add₀ hq.ne', hs]
    congr 1
    ring
  rw [hz]
  ring

end GlobalTheory.ParahoricConjugateOpen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SupportParahoricBiTransformingDoubleCosets
section
noncomputable section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection
  GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

namespace GlobalTheory.ChainStepSupp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem _root_.GlobalTheory.ChainStepSupp.det_lower_ne_zero {A D : Type} [Fintype A] [DecidableEq A]
    [Fintype D] [DecidableEq D]
    {j : GL (A ⊕ D) k} (hj : j ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.parahoric k A D) : j.1.toBlocks₂₂.det ≠ 0 :=
  (_root_.GlobalTheory.ParahoricLowerBlock.lower_block_tame k A D 1 (fun _ _ => rfl) j hj).1

variable (k) in

def reGL {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (e : m ≃ n) : GL m k ≃* GL n k :=
  Units.mapEquiv (Matrix.reindexAlgEquiv k k e).toMulEquiv

theorem val_reGL {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (e : m ≃ n) (g : GL m k) :
    (reGL k e g).1 = reindex e e g.1 := rfl

open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem _root_.GlobalTheory.ChainStepSupp.reGL_mem_KO {m n : Type} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (e : m ≃ n)
    {g : GL m k} (hg : g ∈ _root_.GlobalTheory.SplitWeil.KO k m) :
    _root_.GlobalTheory.ChainStepSupp.reGL k e g ∈ _root_.GlobalTheory.SplitWeil.KO k n := by
  rw [_root_.GlobalTheory.SplitFlip.mem_KO_iff] at hg ⊢
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · simpa [_root_.GlobalTheory.ChainStepSupp.val_reGL, Matrix.reindex_apply] using hg.1 (e.symm i) (e.symm j)
  · rw [← map_inv]
    simpa [_root_.GlobalTheory.ChainStepSupp.val_reGL, Matrix.reindex_apply] using hg.2 (e.symm i) (e.symm j)

open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem _root_.GlobalTheory.ChainStepSupp.reGL_torusElt {m n : Type} [Fintype m]
    [DecidableEq m] [Fintype n] [DecidableEq n] (e : m ≃ n)
    (ϖ : kˣ) (f : m → ℤ) :
    _root_.GlobalTheory.ChainStepSupp.reGL k e (_root_.GlobalTheory.GLDoubling.torusElt k m ϖ f) =
      _root_.GlobalTheory.GLDoubling.torusElt k n ϖ (f ∘ e.symm) := by
  ext i j
  simp [_root_.GlobalTheory.ChainStepSupp.val_reGL, _root_.GlobalTheory.GLDoubling.val_torusElt, Matrix.reindex_apply,
    Matrix.diagonal_apply]

open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem _root_.GlobalTheory.ChainStepSupp.reGL_reGL_symm {m n : Type} [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] (e : m ≃ n)
    (g : GL n k) : _root_.GlobalTheory.ChainStepSupp.reGL k e (_root_.GlobalTheory.ChainStepSupp.reGL k e.symm g) = g := by
  ext i j
  simp [_root_.GlobalTheory.ChainStepSupp.val_reGL, Matrix.reindex_apply]

open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem _root_.GlobalTheory.ChainStepSupp.emb₂_mem_parahoric {A D : Type} [Fintype A] [DecidableEq A]
    [Fintype D] [DecidableEq D]
    {x : GL A k} {y : GL D k} (hx : x ∈ _root_.GlobalTheory.SplitWeil.KO k A)
    (hy : y ∈ _root_.GlobalTheory.SplitWeil.KO k D) :
    _root_.GlobalTheory.SmGL.emb₂ k (Equiv.refl (A ⊕ D)) (x, y) ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.parahoric k A D := by
  rw [_root_.GlobalTheory.SplitFlip.mem_KO_iff] at hx hy
  rw [_root_.GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.mem_parahoric, _root_.GlobalTheory.SplitFlip.mem_KO_iff]
  refine ⟨⟨fun i j => ?_, fun i j => ?_⟩, fun i j => ?_⟩
  · rcases i with i | i <;> rcases j with j | j <;>
      simp [_root_.GlobalTheory.SmGL.val_emb₂, hx.1, hy.1]
  · have hx₂ := hx.2
    have hy₂ := hy.2
    simp only [Matrix.coe_units_inv] at hx₂ hy₂
    rw [← map_inv, Prod.inv_mk]
    rcases i with i | i <;> rcases j with j | j <;>
      simp [_root_.GlobalTheory.SmGL.val_emb₂, hx₂, hy₂]
  · simp [_root_.GlobalTheory.SmGL.val_emb₂]

open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem _root_.GlobalTheory.ChainStepSupp.emb₂_one_torusElt {A D : Type} [Fintype A] [DecidableEq A]
    [Fintype D] [DecidableEq D] (ϖ : kˣ)
    (f : D → ℤ) :
    _root_.GlobalTheory.SmGL.emb₂ k (Equiv.refl (A ⊕ D)) (1, _root_.GlobalTheory.GLDoubling.torusElt k D ϖ f) =
      (_root_.GlobalTheory.ZonalCellDecomposition.mtor ϖ f : GL (A ⊕ D) k) := by
  have h : (_root_.GlobalTheory.ZonalCellDecomposition.mtor ϖ f : GL (A ⊕ D) k) =
      _root_.GlobalTheory.GLDoubling.torusElt k (A ⊕ D) ϖ (0 ⊕ᵥ f) := rfl
  rw [h]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [_root_.GlobalTheory.SmGL.val_emb₂, _root_.GlobalTheory.GLDoubling.val_torusElt, Matrix.diagonal_apply,
      Matrix.one_apply]

open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem _root_.GlobalTheory.ChainStepSupp.support_dcell : ∀ (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ϖ : kˣ),
    valuation k (ϖ : k) = uniformizer k →
  ∀ (r l t : ℕ) (ξ : kˣ →* ℂˣ), _root_.GlobalTheory.SplitWeil.IsTame ξ → ¬ _root_.GlobalTheory.SplitWeil.IsUnram ξ →
  ∀ φ : GL (Fin r ⊕ _root_.GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.Blocks l t) k → ℂ, _root_.GlobalTheory.ZonalCellDecomposition.IsBiType ξ φ →
    (∀ x y, φ (_root_.GlobalTheory.SmGL.emb₂ k (Equiv.refl (Fin r ⊕ _root_.GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.Blocks l t)) (x, y)) ≠ 0 →
      x ∈ _root_.GlobalTheory.SplitWeil.KO k (Fin r)) →
    ∀ g, φ g ≠ 0 → ∃ e : Fin (l * t) → ℤ, Antitone e ∧
      g ∈ _root_.GlobalTheory.ZonalCellDecomposition.dcell ϖ (e ∘ (_root_.GlobalTheory.ZonalCellDecomposition.blkEquiv l t).symm) := by
  intro k _ _ _ _ ϖ hϖ r l t ξ hT hU φ hφ hL g hg
  obtain ⟨x, y, j, hj, j', hj', rfl⟩ :=
    _root_.GlobalTheory.ParHeckeSupp.support_levi k (Fin r) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.Blocks l t) ξ hT hU φ hφ
      g hg
  have hne : φ (_root_.GlobalTheory.SmGL.emb₂ k (Equiv.refl _) (x, y)) ≠ 0 := by
    intro h0
    apply hg
    have hd := _root_.GlobalTheory.ChainStepSupp.det_lower_ne_zero hj
    have hd' := _root_.GlobalTheory.ChainStepSupp.det_lower_ne_zero hj'
    rw [mul_assoc, (hφ j hj (Units.mk0 _ hd) rfl _).1, (hφ j' hj' (Units.mk0 _ hd') rfl _).2, h0,
      mul_zero, mul_zero]
  have hx := hL x y hne
  set E := _root_.GlobalTheory.ZonalCellDecomposition.blkEquiv l t
  obtain ⟨⟨e, he⟩, hy⟩ := Set.mem_iUnion.1 ((Set.eq_univ_iff_forall.1
    (_root_.GlobalTheory.GLDoubling.iUnion_cell (N := l * t) hϖ)) (_root_.GlobalTheory.ChainStepSupp.reGL k E.symm y))
  unfold _root_.GlobalTheory.GLDoubling.cell at hy
  rw [DoubleCoset.mem_doubleCoset] at hy
  obtain ⟨κ₁, hκ₁, κ₂, hκ₂, hyeq⟩ := hy
  refine ⟨e, he, ?_⟩
  unfold _root_.GlobalTheory.ZonalCellDecomposition.dcell
  rw [DoubleCoset.mem_doubleCoset]
  have hy' : y = _root_.GlobalTheory.ChainStepSupp.reGL k E κ₁ *
      _root_.GlobalTheory.GLDoubling.torusElt k _ ϖ (e ∘ E.symm) * _root_.GlobalTheory.ChainStepSupp.reGL k E κ₂ := by
    rw [← _root_.GlobalTheory.ChainStepSupp.reGL_torusElt, ← map_mul, ← map_mul, ← hyeq]
    exact (_root_.GlobalTheory.ChainStepSupp.reGL_reGL_symm E y).symm
  refine ⟨j * _root_.GlobalTheory.SmGL.emb₂ k (Equiv.refl _) (x, _root_.GlobalTheory.ChainStepSupp.reGL k E κ₁),
    (_root_.GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.parahoric k _ _).mul_mem hj
      (_root_.GlobalTheory.ChainStepSupp.emb₂_mem_parahoric hx
        (_root_.GlobalTheory.ChainStepSupp.reGL_mem_KO E hκ₁)),
    _root_.GlobalTheory.SmGL.emb₂ k (Equiv.refl _) (1, _root_.GlobalTheory.ChainStepSupp.reGL k E κ₂) * j',
    (_root_.GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.parahoric k _ _).mul_mem
      (_root_.GlobalTheory.ChainStepSupp.emb₂_mem_parahoric (Subgroup.one_mem _)
        (_root_.GlobalTheory.ChainStepSupp.reGL_mem_KO E hκ₂)) hj', ?_⟩
  rw [← _root_.GlobalTheory.ChainStepSupp.emb₂_one_torusElt, hy']
  have hprod : ((x, _root_.GlobalTheory.ChainStepSupp.reGL k E κ₁ *
      _root_.GlobalTheory.GLDoubling.torusElt k _ ϖ (e ∘ E.symm) * _root_.GlobalTheory.ChainStepSupp.reGL k E κ₂) :
        GL (Fin r) k × GL (_root_.GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.Blocks l t) k) =
      (x, _root_.GlobalTheory.ChainStepSupp.reGL k E κ₁) * (1, _root_.GlobalTheory.GLDoubling.torusElt k _ ϖ (e ∘ E.symm)) *
        (1, _root_.GlobalTheory.ChainStepSupp.reGL k E κ₂) := by
    simp [Prod.mk_mul_mk]
  rw [hprod, map_mul, map_mul]
  simp only [mul_assoc]

end GlobalTheory.ChainStepSupp
end
end

