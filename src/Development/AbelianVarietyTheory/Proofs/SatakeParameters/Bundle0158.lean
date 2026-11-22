import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0925
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1043
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0149
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0142
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0152
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeisenbergTranslateFixedIntegralUnitary
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0125
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0148
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0153
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FdOfCharts
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.Bundle0003
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.InvarianceRepresentativesTrivial
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NatCastMemOfPlace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0154
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertPlaceHeckeDoubleCosetsInverseRepsLabel
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.Columns.HeckeSp
import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodFormsBaseLevelIffGoodProjection
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3

theorem goodForms_baseLevel : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Core R F → (∀ χ ∈ A.X, IsAbsIrrChar χ) → ∀ i (x : (R.HW i (sg0 D A)).H), (R.HW i _).e x ∈ R.Wat i (sg0 D A) (R.levL F false (sg0 D A)) ↔ eH R i x = x ∧ ∀ p : F.P0, R.gW i (sg0 D A) p x = sg0 D A ((F.ψ0⁻¹ p : D.what₂.LLˣ) : D.what₂.LL) • x := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC _ i x
  have hW := hC.models.HW
  have hg := hC.models.gW
  have hl := GlobalTheory.GalLift.Transl.lifts R i hC.lev
  have hx : (R.HW i (sg0 D A)).e x ∈ R.Wall i (sg0 D A) := (hW i _).2.1.le (LinearMap.mem_range_self _ x)
  have hm := (GlobalTheory.MultMem.mem_mult_iff ..).1 hx
  have hT := GlobalTheory.GalLift.Transl.hasType R i hW (sg0 D A) x
  have hsum : (∑ g, RealDat.eC (A := A) (sg0 D A) g • R.gW i (sg0 D A) g x) = eH R i x := by
    simp [eH, LinearMap.sum_apply]
  have hproj : eH R i x = x ↔ ∀ v, R.eWf i (sg0 D A) ((R.HW i (sg0 D A)).e x v) = (R.HW i (sg0 D A)).e x v := by
    constructor
    · intro h v
      rw [GlobalTheory.GalLift.Transl.proj R i hg, hsum, h]
    · intro h
      apply (hW i _).1
      ext v : 1
      rw [← h v, GlobalTheory.GalLift.Transl.proj R i hg, hsum]
  unfold RealDat.Wat
  rw [mem_goodPart, GlobalTheory.MultMem.mem_mult_iff, hproj]
  have hmem : ∀ p : F.P0, R.eG p ∈ (R.levL F false (sg0 D A)).H := fun p => by
    show R.eG.symm (R.eG p) ∈ F.P0
    rw [MulEquiv.symm_apply_apply]; exact p.2
  have hchi : ∀ p : F.P0, (((R.levL F false (sg0 D A)).chi ⟨R.eG p, hmem p⟩ : ℂˣ) : ℂ) =
      sg0 D A ((F.ψ0⁻¹ p : D.what₂.LLˣ) : D.what₂.LL) := fun p => by
    show sg0 D A ((F.ψ0⁻¹ ⟨R.eG.symm (R.eG p), _⟩ : D.what₂.LLˣ) : D.what₂.LL) = _
    congr 4
    exact R.eG.symm_apply_apply _
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h2, fun p => ?_⟩
    apply (hW i _).1
    rw [hg, map_smul]
    ext v h
    have h3 := GlobalTheory.LevelRows.levelType_eigenfunction_of_liftable_element (V := Wc D i) (β := R.βW i) (L := R.datWp i R.triv)
      (P := R.levL F false (sg0 D A)) (F := (R.HW i (sg0 D A)).e x v) (fun κ hκ h => h1.lev v κ hκ h) ⟨R.eG p, hmem p⟩ (hl _)
    exact (congrFun h3 h).trans (congrArg (· * (R.HW i (sg0 D A)).e x v h) (hchi p))
  · rintro ⟨h2, h⟩
    refine ⟨⟨hm.aut, hm.cusp, fun v => ?_, hm.equiv, hm.cont⟩, h2⟩
    have hP : IsPLevel (Wc D i) (R.βW i) (R.datWp i R.triv) (R.levL F false (sg0 D A)) ((R.HW i (sg0 D A)).e x v) := by
      refine ⟨hT v, fun p => ?_⟩
      have hp : R.eG.symm p.1 ∈ F.P0 := p.2
      have h4 := congrArg (fun z => (R.HW i (sg0 D A)).e z v) (h ⟨R.eG.symm p.1, hp⟩)
      simp only [hg _ _ _ x, map_smul] at h4
      have h5 : R.eG (R.eG.symm p.1) = p.1 := R.eG.apply_symm_apply p.1
      rw [h5] at h4
      exact h4
    exact fun κ hκ y => hP.hasType κ hκ y

end GlobalTheory.Hk3

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GramClassEqOfSigmaHermitianFormBounds
section
open Matrix

noncomputable section

namespace GlobalTheory.Hk3.GramConv

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem hform_add_left' (σ : L →+* L) {n : ℕ} (J : Matrix (Fin n) (Fin n) L) (u u' w : Fin n → L) :
    Formalism.UG.hform σ J (u + u') w = Formalism.UG.hform σ J u w + Formalism.UG.hform σ J u' w := by
  simp only [Formalism.UG.hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem hform_add_right' (σ : L →+* L) {n : ℕ} (J : Matrix (Fin n) (Fin n) L) (u w w' : Fin n → L) :
    Formalism.UG.hform σ J u (w + w') = Formalism.UG.hform σ J u w + Formalism.UG.hform σ J u w' := by
  simp only [Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hform_smul_right' (σ : L →+* L) {n : ℕ} (J : Matrix (Fin n) (Fin n) L) (c : L) (u w : Fin n → L) :
    Formalism.UG.hform σ J u (c • w) = c * Formalism.UG.hform σ J u w := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hform_smul_left' (σ : L →+* L) (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (J : Matrix (Fin n) (Fin n) L) (c : L)
    (u w : Fin n → L) : Formalism.UG.hform σ J (σ c • u) w = c * Formalism.UG.hform σ J u w := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, hσ, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hform_sub_mat (σ : L →+* L) {n : ℕ} (J J' : Matrix (Fin n) (Fin n) L) (u w : Fin n → L) :
    Formalism.UG.hform σ (J - J') u w = Formalism.UG.hform σ J u w - Formalism.UG.hform σ J' u w := by
  simp only [Formalism.UG.hform, Matrix.sub_apply, mul_sub, sub_mul, Finset.sum_sub_distrib]

theorem hform_eq_dot (σ : L →+* L) {n : ℕ} (J : Matrix (Fin n) (Fin n) L) (u w : Fin n → L) :
    Formalism.UG.hform σ J u w = (fun i => σ (u i)) ⬝ᵥ (J *ᵥ w) := by
  simp only [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hform_mulVec_mulVec (σ : L →+* L) {n r : ℕ} (J : Matrix (Fin n) (Fin n) L) (B : Matrix (Fin n) (Fin r) L)
    (α β : Fin r → L) :
    Formalism.UG.hform σ J (B *ᵥ α) (B *ᵥ β) = Formalism.UG.hform σ (Formalism.UG.cT σ B * J * B) α β := by
  have hs : (fun i => σ ((B *ᵥ α) i)) = (fun k => σ (α k)) ᵥ* Formalism.UG.cT σ B := by
    ext i
    simp only [Matrix.mulVec, Matrix.vecMul, dotProduct, Formalism.UG.cT, map_sum, map_mul, Matrix.transpose_apply,
      Matrix.map_apply]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [hform_eq_dot, hform_eq_dot, hs, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.mul_assoc]

theorem mulVec_int' {a b : ℕ} {A : Matrix (Fin a) (Fin b) L} (hA : ∀ i j, A i j ∈ Formalism.UG.intL L) {w : Fin b → L}
    (hw : ∀ j, w j ∈ Formalism.UG.intL L) (i : Fin a) : (A *ᵥ w) i ∈ Formalism.UG.intL L := by
  simp only [Matrix.mulVec, dotProduct]
  exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hA i j) (hw j)

theorem hform_int' (σ : L →+* L) (hv : ∀ x, Valued.v (σ x) = Valued.v x) {n : ℕ} {J : Matrix (Fin n) (Fin n) L}
    (hJ : ∀ i j, J i j ∈ Formalism.UG.intL L) {u w : Fin n → L} (hu : ∀ i, u i ∈ Formalism.UG.intL L)
    (hw : ∀ i, w i ∈ Formalism.UG.intL L) : Formalism.UG.hform σ J u w ∈ Formalism.UG.intL L := by
  have hsu : ∀ i, σ (u i) ∈ Formalism.UG.intL L := fun i => by
    show Valued.v (σ (u i)) ≤ 1
    rw [hv]; exact hu i
  exact Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ =>
    Subring.mul_mem _ (Subring.mul_mem _ (hsu i) (hJ i j)) (hw j)

theorem gramEq_of_gram_bounds : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L), (∀ x, σ (σ x) = x) → (∀ x, Valued.v (σ x) = Valued.v x) → ϖ ∈ Formalism.UG.intL L →
  ∀ (n n' r : ℕ) (JT : GL (Fin n') L) (a : GL (Fin n) L) (x y : Matrix (Fin n') (Fin n) L)
    (M : Matrix (Fin n) (Fin r) L) (e : Fin r → ℕ),
  (∀ i j, (JT : Matrix (Fin n') (Fin n') L) i j ∈ Formalism.UG.intL L) →
  (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
  (∀ v : Fin n → L, (∀ i, v i ∈ Formalism.UG.intL L) →
    ((∃ u : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) ∧ v = (a : Matrix (Fin n) (Fin n) L) *ᵥ u) ↔ ∀ i, (x *ᵥ v) i ∈ Formalism.UG.intL L)) → (∀ i j, (x * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L) → (∀ i j, (y * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L) →
  (∀ i k, M i k ∈ Formalism.UG.intL L) → (∀ i k, (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * M) i k * ϖ ^ e k ∈ Formalism.UG.intL L) → (∀ m : Fin n → L, (∀ i, m i ∈ Formalism.UG.intL L) → ∃ α : Fin r → L, (∀ k, α k ∈ Formalism.UG.intL L) ∧
      ∀ i, (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ (m - M *ᵥ α)) i ∈ Formalism.UG.intL L) → (∀ β : Fin r → L, (∀ k, β k ∈ Formalism.UG.intL L) → (∀ i, (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ (M *ᵥ β)) i ∈ Formalism.UG.intL L) →
      ∀ k, Valued.v (β k) ≤ Valued.v ϖ ^ e k) →
  (∀ j k, ((Formalism.UG.cT σ (y * M) * (JT : Matrix (Fin n') (Fin n') L) * (y * M)) - (Formalism.UG.cT σ (x * M) * (JT : Matrix (Fin n') (Fin n') L) * (x * M))) j k * ϖ ^ max (e j) (e k) ∈ Formalism.UG.intL L) →
  GlobalTheory.Hk3.HoweG.GramEq σ JT x y := by
  intro L _ _ ϖ σ hσ hv hϖ n n' r JT a x y M e hJ hJh hiff hxa hya hM hAM hdec hbd hG
  intro m m' hm hm' c hc hxm hxm'
  have toV : ∀ t : L, t ∈ Formalism.UG.intL L → Valued.v t ≤ 1 := fun t h => h
  have ofV : ∀ t : L, Valued.v t ≤ 1 → t ∈ Formalism.UG.intL L := fun t h => h
  set A : Matrix (Fin n) (Fin n) L := (a : Matrix (Fin n) (Fin n) L) with hA
  set Ai : Matrix (Fin n) (Fin n) L := ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hAi
  set J : Matrix (Fin n') (Fin n') L := (JT : Matrix (Fin n') (Fin n') L) with hJdef
  have hAAi : A * Ai = 1 := by rw [hA, hAi]; exact a.mul_inv
  have hAiA : Ai * A = 1 := by rw [hA, hAi]; exact a.inv_mul

  have key : ∀ μ : Fin n → L, (∀ i, μ i ∈ Formalism.UG.intL L) → (∀ i, (x *ᵥ (c • μ)) i ∈ Formalism.UG.intL L) →
      ∃ α : Fin r → L, (∀ k, α k ∈ Formalism.UG.intL L) ∧ (∀ i, (Ai *ᵥ (μ - M *ᵥ α)) i ∈ Formalism.UG.intL L) ∧
        (∀ i, (Ai *ᵥ (M *ᵥ (c • α))) i ∈ Formalism.UG.intL L) ∧ ∀ k, Valued.v (c * α k) ≤ Valued.v ϖ ^ e k := by
    intro μ hμ hxμ
    obtain ⟨α, hα, hν⟩ := hdec μ hμ
    have hcμ : ∀ i, (c • μ) i ∈ Formalism.UG.intL L := fun i => Subring.mul_mem _ hc (hμ i)
    obtain ⟨u, hu, hcu⟩ := (hiff (c • μ) hcμ).2 hxμ
    have heq : Ai *ᵥ (M *ᵥ (c • α)) = u - c • (Ai *ᵥ (μ - M *ᵥ α)) := by
      have h1 : M *ᵥ (c • α) = c • μ - c • (μ - M *ᵥ α) := by
        rw [Matrix.mulVec_smul, smul_sub, sub_sub_cancel]
      rw [h1, Matrix.mulVec_sub, hcu, Matrix.mulVec_mulVec, hAiA, Matrix.one_mulVec, Matrix.mulVec_smul]
    have hint : ∀ i, (Ai *ᵥ (M *ᵥ (c • α))) i ∈ Formalism.UG.intL L := by
      intro i
      rw [heq, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      exact Subring.sub_mem _ (hu i) (Subring.mul_mem _ hc (hν i))
    have hcα : ∀ k, (c • α) k ∈ Formalism.UG.intL L := fun k => Subring.mul_mem _ hc (hα k)
    refine ⟨α, hα, hν, hint, fun k => ?_⟩
    have := hbd (c • α) hcα hint k
    simpa only [Pi.smul_apply, smul_eq_mul] using this
  obtain ⟨α, hα, hν, hcαA, hbdα⟩ := key m hm hxm
  obtain ⟨α', hα', hν', hcα'A, hbdα'⟩ := key m' hm' hxm'

  have hσcα : ∀ i, (Ai *ᵥ (M *ᵥ (σ c • α))) i ∈ Formalism.UG.intL L := by
    intro i
    rw [Matrix.mulVec_mulVec]
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
    refine Subring.sum_mem _ fun k _ => ofV _ ?_
    calc Valued.v ((Ai * M) i k * (σ c * α k)) = Valued.v ((Ai * M) i k) * Valued.v (c * α k) := by
          rw [map_mul, map_mul, map_mul, hv]
      _ ≤ Valued.v ((Ai * M) i k) * Valued.v ϖ ^ e k := mul_le_mul' le_rfl (hbdα k)
      _ = Valued.v ((Ai * M) i k * ϖ ^ e k) := by rw [map_mul, map_pow]
      _ ≤ 1 := toV _ (hAM i k)

  have hz : ∀ z : Matrix (Fin n') (Fin n) L, (∀ i j, (z * A) i j ∈ Formalism.UG.intL L) →
      c * Formalism.UG.hform σ J (z *ᵥ m) (z *ᵥ m') - c * Formalism.UG.hform σ J (z *ᵥ (M *ᵥ α)) (z *ᵥ (M *ᵥ α'))
        ∈ Formalism.UG.intL L := by
    intro z hzA
    have hzw : ∀ w : Fin n → L, (∀ i, (Ai *ᵥ w) i ∈ Formalism.UG.intL L) → ∀ i, (z *ᵥ w) i ∈ Formalism.UG.intL L := by
      intro w hw
      have : z *ᵥ w = (z * A) *ᵥ (Ai *ᵥ w) := by
        rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, hAAi, Matrix.mul_one]
      rw [this]; exact mulVec_int' hzA hw
    have e1 : z *ᵥ m = z *ᵥ (M *ᵥ α) + z *ᵥ (m - M *ᵥ α) := by
      rw [← Matrix.mulVec_add, add_sub_cancel]
    have e2 : z *ᵥ m' = z *ᵥ (M *ᵥ α') + z *ᵥ (m' - M *ᵥ α') := by
      rw [← Matrix.mulVec_add, add_sub_cancel]
    have s1 : σ c • (z *ᵥ (M *ᵥ α)) = z *ᵥ (M *ᵥ (σ c • α)) := by
      rw [Matrix.mulVec_smul, Matrix.mulVec_smul]
    have s2 : c • (z *ᵥ (M *ᵥ α')) = z *ᵥ (M *ᵥ (c • α')) := by
      rw [Matrix.mulVec_smul, Matrix.mulVec_smul]
    have hexp : c * Formalism.UG.hform σ J (z *ᵥ m) (z *ᵥ m') - c * Formalism.UG.hform σ J (z *ᵥ (M *ᵥ α)) (z *ᵥ (M *ᵥ α')) =
        Formalism.UG.hform σ J (σ c • (z *ᵥ (M *ᵥ α))) (z *ᵥ (m' - M *ᵥ α')) +
        Formalism.UG.hform σ J (z *ᵥ (m - M *ᵥ α)) (c • (z *ᵥ (M *ᵥ α'))) +
        c * Formalism.UG.hform σ J (z *ᵥ (m - M *ᵥ α)) (z *ᵥ (m' - M *ᵥ α')) := by
      rw [hform_smul_left' σ hσ, hform_smul_right', e1, e2, hform_add_left', hform_add_right', hform_add_right']
      ring
    rw [hexp, s1, s2]
    have hJi : ∀ i j, J i j ∈ Formalism.UG.intL L := hJ
    refine Subring.add_mem _ (Subring.add_mem _ ?_ ?_) (Subring.mul_mem _ hc ?_)
    · exact hform_int' σ hv hJi (hzw _ hσcα) (hzw _ hν')
    · exact hform_int' σ hv hJi (hzw _ hν) (hzw _ hcα'A)
    · exact hform_int' σ hv hJi (hzw _ hν) (hzw _ hν')

  have hmain : c * (Formalism.UG.hform σ J (y *ᵥ (M *ᵥ α)) (y *ᵥ (M *ᵥ α')) -
      Formalism.UG.hform σ J (x *ᵥ (M *ᵥ α)) (x *ᵥ (M *ᵥ α'))) ∈ Formalism.UG.intL L := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      hform_mulVec_mulVec, hform_mulVec_mulVec, ← hform_sub_mat, ← hform_smul_right']
    set D := Formalism.UG.cT σ (y * M) * J * (y * M) - Formalism.UG.cT σ (x * M) * J * (x * M) with hD
    refine Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ => ofV _ ?_
    have h1 : Valued.v (α i) * Valued.v (c * α' j) ≤ Valued.v ϖ ^ max (e i) (e j) := by
      rcases le_total (e i) (e j) with h | h
      · rw [max_eq_right h]
        calc Valued.v (α i) * Valued.v (c * α' j) ≤ 1 * Valued.v ϖ ^ e j := mul_le_mul' (toV _ (hα i)) (hbdα' j)
          _ = _ := one_mul _
      · rw [max_eq_left h]
        calc Valued.v (α i) * Valued.v (c * α' j) = Valued.v (c * α i) * Valued.v (α' j) := by
              rw [map_mul, map_mul, mul_left_comm, ← mul_assoc]
          _ ≤ Valued.v ϖ ^ e i * 1 := mul_le_mul' (hbdα i) (toV _ (hα' j))
          _ = _ := mul_one _
    calc Valued.v (σ (α i) * D i j * (c • α') j) = (Valued.v (α i) * Valued.v (c * α' j)) * Valued.v (D i j) := by
          rw [Pi.smul_apply, smul_eq_mul, map_mul, map_mul, hv, mul_right_comm]
      _ ≤ Valued.v ϖ ^ max (e i) (e j) * Valued.v (D i j) := mul_le_mul' h1 le_rfl
      _ = Valued.v (D i j * ϖ ^ max (e i) (e j)) := by rw [map_mul, map_pow, mul_comm]
      _ ≤ 1 := toV _ (hG i j)
  have hfin : c * (Formalism.UG.hform σ J (y *ᵥ m) (y *ᵥ m') - Formalism.UG.hform σ J (x *ᵥ m) (x *ᵥ m')) =
      (c * Formalism.UG.hform σ J (y *ᵥ m) (y *ᵥ m') - c * Formalism.UG.hform σ J (y *ᵥ (M *ᵥ α)) (y *ᵥ (M *ᵥ α'))) -
      (c * Formalism.UG.hform σ J (x *ᵥ m) (x *ᵥ m') - c * Formalism.UG.hform σ J (x *ᵥ (M *ᵥ α)) (x *ᵥ (M *ᵥ α'))) +
      c * (Formalism.UG.hform σ J (y *ᵥ (M *ᵥ α)) (y *ᵥ (M *ᵥ α')) -
        Formalism.UG.hform σ J (x *ᵥ (M *ᵥ α)) (x *ᵥ (M *ᵥ α'))) := by ring
  rw [hfin]
  exact Subring.add_mem _ (Subring.sub_mem _ (hz y hya) (hz x hxa)) hmain

end GlobalTheory.Hk3.GramConv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GramHermitianSkewTraceSigmaFixed
section
open Matrix

namespace GlobalTheory

theorem gram_hermitian_and_trace_fixed :
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (δ : L), (∀ x, σ (σ x) = x) → σ δ = -δ →
  ∀ (n' r : ℕ) (JT : GL (Fin n') L) (z : Matrix (Fin n') (Fin r) L) (Γ : Matrix (Fin r) (Fin r) L),
  (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
  (∀ k j, σ (Γ k j) = - Γ j k) →
  (∀ j k, σ ((Formalism.UG.cT σ z * (JT : Matrix (Fin n') (Fin n') L) * z) j k) = (Formalism.UG.cT σ z * (JT : Matrix (Fin n') (Fin n') L) * z) k j) ∧
  σ (δ * Matrix.trace (Γ * (Formalism.UG.cT σ z * (JT : Matrix (Fin n') (Fin n') L) * z))) =
    δ * Matrix.trace (Γ * (Formalism.UG.cT σ z * (JT : Matrix (Fin n') (Fin n') L) * z)) := by
  intro L _ _ σ δ hσ hδ n' r JT z Γ hJ hΓ
  have h1 : ∀ j k, σ ((Formalism.UG.cT σ z * (JT : Matrix (Fin n') (Fin n') L) * z) j k) =
      (Formalism.UG.cT σ z * (JT : Matrix (Fin n') (Fin n') L) * z) k j := by
    intro j k
    simp only [Formalism.UG.cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum,
      map_mul, hσ, hJ, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  refine ⟨h1, ?_⟩
  generalize Formalism.UG.cT σ z * (JT : Matrix (Fin n') (Fin n') L) * z = G at h1 ⊢
  have h2 : σ (Matrix.trace (Γ * G)) = - Matrix.trace (Γ * G) := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, map_sum, map_mul, hΓ, h1,
      ← Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [map_mul, hδ, h2]
  ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeisenbergTranslateFixedIntegralUnitaryStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergTranslate_fixed_integralUnitary : ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L)
    (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ) (M : Type) [AddCommGroup M] [Module ℂ M]
    (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M)
    (ω : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M),
    GlobalTheory.Hk3.LocPair ϖ σ q δ JS JT ψ ρ ω → ∀ s : M, GlobalTheory.Hk3.LocVac ρ s → ∀ x : Matrix (Fin n') (Fin n) L,
    (∃ w : M, w ≠ 0 ∧ (∀ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L),
        (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) → ω (1, h) w = w) ∧
      w ∈ Submodule.span ℂ {v : M | ∃ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) ∧
          v = ρ (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x) s}) →
    ρ x s ≠ 0 ∧ ∀ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
      (∀ i j, ((((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x - x) i j ∈ Formalism.UG.intL L)) →
      ρ (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x) s = ρ x s := by
  first | exact @GlobalTheory.Hk3.class_fixed_phase | exact GlobalTheory.Hk3.class_fixed_phase | (intros; apply GlobalTheory.Hk3.class_fixed_phase <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HermitianFormIntegralPreimageLatticeStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianForm_integral_preimage_lattice : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L),
    (∀ z, σ (σ z) = z) → (∀ z, Valued.v (σ z) = Valued.v z) →
    JS ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) → JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JS : Matrix (Fin n) (Fin n) L) i j) = (JS : Matrix (Fin n) (Fin n) L) j i) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    ∀ x : Matrix (Fin n') (Fin n) L, (∀ i j, (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose (x.map σ)) i j ∈ Formalism.UG.intL L) →
    ∀ (u u' : Fin n → L) (w w' : Fin n' → L), (∀ i, u i ∈ Formalism.UG.intL L) → (∀ i, (x *ᵥ u) i ∈ Formalism.UG.intL L) →
      (∀ i, w i ∈ Formalism.UG.intL L) → (∀ i, u' i ∈ Formalism.UG.intL L) → (∀ i, (x *ᵥ u') i ∈ Formalism.UG.intL L) →
      (∀ i, w' i ∈ Formalism.UG.intL L) →
      Formalism.UG.hform σ (JS : Matrix (Fin n) (Fin n) L) (u + GlobalTheory.Hk3.HoweG.adj σ JS JT x *ᵥ w)
        (u' + GlobalTheory.Hk3.HoweG.adj σ JS JT x *ᵥ w') ∈ Formalism.UG.intL L := by
  first | exact @GlobalTheory.Hk3.HoweG.GramA.hform_integral | exact GlobalTheory.Hk3.HoweG.GramA.hform_integral | (intros; apply GlobalTheory.Hk3.HoweG.GramA.hform_integral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HomLatticeVolumeCompletionSplitPlace
section
noncomputable section

namespace GlobalTheory.VolAt

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Matrix

theorem latAt_lattice {p : ℕ} [Fact p.Prime] (X : Sys p) (v : X.Pl) (j : ℕ) (L : (X.Pj j).Tup)
    (hL : (X.Pj j).IsLatTup L) :
    ∃ g : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v), IsUnit g.det ∧
      X.latAt v j L = colSpan (X.G.P.W v) g ∧ len X v j L = -ordP (X.G.P.W v) p g.det := by
  have hS := X.G.P.setting v
  haveI := hS.frac_alt
  cases j with
  | zero =>
    have h0 : IsLattice (X.G.P.W v) (X.latAt v 0 L) := hL v
    obtain ⟨g, hg, hL'⟩ := h0
    refine ⟨g, hg, hL', ?_⟩
    change lenLat (X.G.P.W v) p (X.latAt v 0 L) = _
    rw [hL']
    exact lenLat_colSpan hS.p_unif g hg
  | succ j =>
    have h0 : IsLattice (X.G.P.W v) (X.latAt v (j + 1) L) := hL v
    obtain ⟨g, hg, hL'⟩ := h0
    refine ⟨g, hg, hL', ?_⟩
    change lenLat (X.G.P.W v) p (X.latAt v (j + 1) L) = _
    rw [hL']
    exact lenLat_colSpan hS.p_unif g hg

theorem Pj_m_succ {p : ℕ} [Fact p.Prime] (X : Sys p) (j : ℕ) : (X.Pj j).m + 1 = NN X.G.P.m X.t j := by
  cases j with
  | zero => simp [NN, Sys.Pj, Fills.Pj]
  | succ j =>
    simp only [NN, Sys.Pj, Fills.Pj, Places.withWt, Sys.t]
    ring

theorem homLat_conj {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq] {k k' : ℕ}
    (M g : Matrix (Fin k) (Fin k) Qq) (M' g' : Matrix (Fin k') (Fin k') Qq) (hM' : IsUnit M'.det)
    (z : Matrix (Fin k') (Fin k) Qq) :
    z ∈ homLat W (colSpan W (M * g)) (colSpan W (M' * g')) ↔
      ∀ y ∈ colSpan W g, (M'⁻¹ * z * M) *ᵥ y ∈ colSpan W g' := by
  rw [← colSpan_mul, ← colSpan_mul, mem_homLat]
  have hinv : M'⁻¹ * M' = 1 := Matrix.nonsing_inv_mul M' hM'
  have hinv' : M' * M'⁻¹ = 1 := Matrix.mul_nonsing_inv M' hM'
  constructor
  · intro h y hy
    obtain ⟨u, hu, hu'⟩ := h (M *ᵥ y) (Submodule.mem_map_of_mem hy)
    have e : (M'⁻¹ * z * M) *ᵥ y = u := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      have : z *ᵥ (M *ᵥ y) = M' *ᵥ u := hu'.symm
      rw [this, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
    rw [e]
    exact hu
  · rintro h _ ⟨y, hy, rfl⟩
    have e : z *ᵥ ((M.mulVecLin.restrictScalars W) y) = M' *ᵥ ((M'⁻¹ * z * M) *ᵥ y) := by
      change z *ᵥ (M *ᵥ y) = _
      simp only [Matrix.mulVec_mulVec]
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hinv', Matrix.one_mul]
    rw [e]
    exact Submodule.mem_map_of_mem (h y hy)

theorem vol_main : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (X : Sys p) (v : X.Pl) (j : ℕ) (ρ : D.host.E →+* X.G.P.Qq v) (P : HeightOneSpectrum (𝓞 D.host.E)), Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (1 : Submodule (𝓞 D.host.E) D.host.E) → (∀ x : 𝓞 D.host.E, ∃ y : X.G.P.W v, ρ x = algebraMap _ _ y ∧ (x ∈ P.asIdeal ↔ (p : X.G.P.W v) ∣ y)) → (∀ (y : X.G.P.W v) (n : ℕ), ∃ (x : 𝓞 D.host.E) (z : X.G.P.W v), ρ x = algebraMap _ _ (y + (p : X.G.P.W v) ^ n * z)) → ∃ φ : GL3Theta.EP D P ≃+* X.G.P.Qq v, (∀ x : D.host.E, φ (algebraMap _ _ x) = ρ x) ∧ ∀ (M : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)) (M' : Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj (j + 1)).m + 1)) (X.G.P.Qq v)), IsUnit M.det → IsUnit M'.det → ∀ (N : (X.Pj j).Tup → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E)) (N' : (X.Pj (j + 1)).Tup → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E)) (S : Set ((X.Pj j).Tup × (X.Pj (j + 1)).Tup)), (∀ q ∈ S, (X.Pj j).IsLatTup q.1 ∧ (X.Pj (j + 1)).IsLatTup q.2 ∧ TaylorLogMetric.admitted D _ _ (N q.1) (N' q.2) ∧ Submodule.span (X.G.P.W v) ((fun x k => ρ (x k)) '' (N q.1 : Set (Fin ((X.Pj j).m + 1) → D.host.E))) = (X.latAt v j q.1).map ((M.mulVecLin).restrictScalars (X.G.P.W v)) ∧ Submodule.span (X.G.P.W v) ((fun x k => ρ (x k)) '' (N' q.2 : Set (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))) = (X.latAt v (j + 1) q.2).map ((M'.mulVecLin).restrictScalars (X.G.P.W v))) → ∀ q ∈ S, (∀ y, y ∈ GL3Theta.YP D P (N q.1) (N' q.2) ↔ X.ind v j q.1 q.2 (M'⁻¹ * y.map φ * M) = 1) ∧ ∀ q₀ ∈ S, GL3Theta.volP (GL3Theta.YP D P (N q₀.1) (N' q₀.2)) (GL3Theta.YP D P (N q.1) (N' q.2)) = (p : ℝ) ^ ((X.G.P.n' v : ℤ) * (volE X v j q.1 q.2 - volE X v j q₀.1 q₀.2)) := by
  intro D p _ X v j ρ P hA h1 h2
  have hS := X.G.P.setting v
  haveI := hS.frac_alt
  obtain ⟨φ, hφ, hop, hnb⟩ := GlobalTheory.T.numberField_completion_ringEquiv_of_dense_unramified P p hS.p_unif hS.eq_sum_herm_smul_frame_of_inW ρ h1 h2
  refine ⟨φ, hφ, ?_⟩
  intro M M' hM hM' N N' S hSq
  have key : ∀ q ∈ S, ∃ (g : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v))
      (g' : Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj (j + 1)).m + 1)) (X.G.P.Qq v)),
      IsUnit (M * g).det ∧ IsUnit (M' * g').det ∧
      (∀ y, y ∈ GL3Theta.YP D P (N q.1) (N' q.2) ↔ y.map φ ∈ homLat (X.G.P.W v) (colSpan (X.G.P.W v) (M * g))
        (colSpan (X.G.P.W v) (M' * g'))) ∧
      (∀ z, X.ind v j q.1 q.2 (M'⁻¹ * z * M) = 1 ↔ z ∈ homLat (X.G.P.W v) (colSpan (X.G.P.W v) (M * g))
        (colSpan (X.G.P.W v) (M' * g'))) ∧
      ordP (X.G.P.W v) p (M * g).det = ordP (X.G.P.W v) p M.det - len X v j q.1 ∧
      ordP (X.G.P.W v) p (M' * g').det = ordP (X.G.P.W v) p M'.det - len X v (j + 1) q.2 := by
    intro q hq
    obtain ⟨hL, hL', hAdm, hsp, hsp'⟩ := hSq q hq
    obtain ⟨g, hg, hgL, hlen⟩ := latAt_lattice X v j q.1 hL
    obtain ⟨g', hg', hgL', hlen'⟩ := latAt_lattice X v (j + 1) q.2 hL'
    have hMg : IsUnit (M * g).det := by rw [Matrix.det_mul]; exact hM.mul hg
    have hMg' : IsUnit (M' * g').det := by rw [Matrix.det_mul]; exact hM'.mul hg'
    have hNa : Submodule.span (X.G.P.W v) ((fun x k => ρ (x k)) '' (N q.1 : Set (Fin ((X.Pj j).m + 1) → D.host.E))) =
        colSpan (X.G.P.W v) (M * g) := by rw [hsp, hgL, colSpan_mul]
    have hNb : Submodule.span (X.G.P.W v) ((fun x k => ρ (x k)) '' (N' q.2 : Set (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))) =
        colSpan (X.G.P.W v) (M' * g') := by rw [hsp', hgL', colSpan_mul]
    obtain ⟨-, -, ⟨hFG, hspan, -⟩, ⟨hFG', hspan', -⟩⟩ := hAdm
    refine ⟨g, g', hMg, hMg', fun y => ?_, fun z => ?_, ?_, ?_⟩
    · exact GlobalTheory.T.mem_closure_iff_map_mem_matrixHomLattice_completion P p hS.p_unif ρ h2 φ hφ hop hnb (TaylorLogMetric.YYl D (N q.1) (N' q.2)) _ _ hMg hMg'
        (GlobalTheory.T.ideal_mul_hom_map_mem_matrixHomLattice D P p hS.p_unif ρ hA h1 _ _ _ _ hNa hNb)
        (GlobalTheory.T.matrixHomLattice_le_span_ideal_hom_image D P p hS.p_unif ρ hA h1 _ _ hFG hFG' hspan hspan' _ _ hMg hMg' hNa hNb) y
    · rw [homLat_conj M g M' g' hM' z, ← hgL, ← hgL']
      unfold Sys.ind
      split_ifs with h
      · exact iff_of_true rfl h
      · exact iff_of_false (by norm_num) h
    · rw [Matrix.det_mul, ordP_mul hS.p_unif hM.ne_zero hg.ne_zero, hlen]
      ring
    · rw [Matrix.det_mul, ordP_mul hS.p_unif hM'.ne_zero hg'.ne_zero, hlen']
      ring
  intro q hq
  obtain ⟨g, g', hMg, hMg', hY, hind, ho, ho'⟩ := key q hq
  refine ⟨fun y => (hY y).trans (hind _).symm, fun q₀ hq₀ => ?_⟩
  obtain ⟨g₀, g₀', hMg₀, hMg₀', hY₀, -, ho₀, ho₀'⟩ := key q₀ hq₀
  let e : Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj j).m + 1)) (GL3Theta.EP D P) →+
      Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v) :=
    φ.toAddEquiv.toAddMonoidHom.mapMatrix
  have he : Function.Surjective e := fun z => ⟨z.map φ.symm, by ext i l; simp [e]⟩
  have hYc : ∀ (A : Submodule (X.G.P.W v) _), (∀ y, y ∈ GL3Theta.YP D P (N q.1) (N' q.2) ↔ y.map φ ∈ A) →
      GL3Theta.YP D P (N q.1) (N' q.2) = A.toAddSubgroup.comap e := fun A h => by
    ext y; exact h y
  have hYc₀ : ∀ (A : Submodule (X.G.P.W v) _), (∀ y, y ∈ GL3Theta.YP D P (N q₀.1) (N' q₀.2) ↔ y.map φ ∈ A) →
      GL3Theta.YP D P (N q₀.1) (N' q₀.2) = A.toAddSubgroup.comap e := fun A h => by
    ext y; exact h y
  have hrel : ∀ A B : AddSubgroup (Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)),
      ((A.comap e).addSubgroupOf (B.comap e)).index = A.relIndex B := fun A B => by
    change (A.comap e).relIndex (B.comap e) = _
    rw [AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective he]
  unfold GL3Theta.volP
  rw [hYc _ hY, hYc₀ _ hY₀, hrel, hrel,
    GlobalTheory.T.relIndex_matrixHomLattice_ratio_eq_residue_pow p (X.G.P.n' v) hS.p_unif hS.res_card _ _ _ _ hMg₀ hMg hMg₀' hMg', ho, ho', ho₀, ho₀']
  congr 1
  unfold volE
  rw [← Pj_m_succ X j, ← Pj_m_succ X (j + 1)]
  push_cast
  ring

end GlobalTheory.VolAt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertPlaceHeckeDoubleCosetsInverseRepsLabelStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inert_place_hecke_double_cosets_inverse_reps_label : ∀ {D : D7} (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (e : Formalism.L2.Theta.AE D), IsPrimeIdem P e e → (∃ x : 𝓞 D.host.F, ∃ y : 𝓞 D.host.E, (y : D.host.E) = algebraMap D.host.F D.host.E (x : D.host.F) ∧ y ∈ P.asIdeal ∧ y ∉ P.asIdeal ^ 2) → ∀ g, SuppF V e g → (∃ a b, a ∈ KsphC V ∅ ∧ SuppF V e a ∧ b ∈ KsphC V ∅ ∧ SuppF V e b ∧ g⁻¹ = a * g * b) ∧ (∃ R : Finset (GA D V), (∀ γ ∈ R, SuppF V e γ) ∧ IsCosetRep V {k | k ∈ KsphC V ∅ ∧ SuppF V e k} g R) ∧ ∀ (ϖ ϖ' : 𝓞 D.host.E) d g', ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → ϖ' ∈ P.asIdeal → ϖ' ∉ P.asIdeal ^ 2 → d.Pairwise (fun a b => b ≤ a) → SuppF V e g' → DivAt V e (ϖ : D.host.E) d g → DivAt V e (ϖ' : D.host.E) d g' → ∃ a b, a ∈ KsphC V ∅ ∧ SuppF V e a ∧ b ∈ KsphC V ∅ ∧ SuppF V e b ∧ g' = a * g * b := by
  first | exact @GlobalTheory.InertDoubleCoset.inert_double_cosets | exact GlobalTheory.InertDoubleCoset.inert_double_cosets | (intros; apply GlobalTheory.InertDoubleCoset.inert_double_cosets <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralAwayFromMovedLocalDatumStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralAwayFrom_moved_localDatum : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), (∀ j, ∃ e, Formalism.L2.Col.IsMu0 t.Ch t.seam.σ₀ e j (t.glob.mu0 j)) → (∀ (j : Fin D.R.m) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 t.X.E)), (∀ i, ((t.Pr.g i : ℕ) : 𝓞 t.X.E) ∉ v.asIdeal) → t.seam.σ₀ (t.Ch.muVal j v : t.X.K) = (((t.glob.mu0 j).val v : ℂˣ) : ℂ)) → ∀ u μ, (∀ k, D.host.g k ∉ Y.Qp μ) → ∀ (i : ℕ), i < D.R.m → ∀ (P : rowSG t.Pr t.sel (t.tup μ)) (hal : AutY t.X D.R i) (h : AutY t.X D.R (i + 1)), (P.1 ∈ t.Pr.vGs → hal ∈ stabL t.X.E _ (lamYat (Pr := t.Pr) i P.1) ∧ h ∈ stabL t.X.E _ (lamYat (Pr := t.Pr) (i + 1) P.1)) → ∀ x, IntOff (t.O u μ).S (t.seam.σ₀ (omPhi t.Ch t.sel (t.tup μ) (t.cst μ) i P hal h x)) := by
  first | exact @GlobalTheory.OmPhiInt.intOff_omPhi | exact GlobalTheory.OmPhiInt.intOff_omPhi | (intros; apply GlobalTheory.OmPhiInt.intOff_omPhi <;> assumption)
end

