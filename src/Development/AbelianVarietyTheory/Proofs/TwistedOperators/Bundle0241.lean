import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0216
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0055
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0025
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0220
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0072
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0222
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0129

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexHalfActionSplitPlaceFrames
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.SplitHecke GlobalTheory.LFun.ConjPlace GlobalTheory.AdelicU GlobalTheory.LFun.SplitTie

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.SplitIdx

open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting in

theorem relIndex_half_act : ∀ (D : D7) (S T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.SplitProj D v) (ε : AE D), GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.IsIdemOf φ ε → ∀ (BS : GL (Fin S.rank) (Fv D.host.F v)) (BT : GL (Fin T.rank) (Fv D.host.F v)), GlobalTheory.SplitHecke.Frame S ε (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdA φ) BS → GlobalTheory.SplitHecke.Frame T ε (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdA φ) BT → ∀ g : GA D T, (GlobalTheory.SplitIdx.halfLat S T ε).relIndex ((GlobalTheory.SplitIdx.halfLat S T ε).map (GlobalTheory.SplitIdx.actL S T g)) = (GlobalTheory.SplitIdx.intMat D.host.F v T.rank S.rank).relIndex ((GlobalTheory.SplitIdx.intMat D.host.F v T.rank S.rank).map (GlobalTheory.SplitIdx.mulL (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.grpCo φ T BT g).1)) := by
  intro D S T v φ ε hε BS BT hS hT g
  have hch := (GlobalTheory.SplitProjChart.chart_rdA D v φ ε hε).1
  obtain ⟨c, hc0, hc⟩ := GlobalTheory.SplitHomLattice.mem_latO_iff_intM ε v (rdA φ) hε.1 hch S T BS BT hS hT
  have hL : ∀ V : HSp D, ((frameLat V : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) : Set (Fin V.rank → D.host.E)) = L0c D V := by
    intro V
    ext x
    show V.frame.equivFun.symm x ∈ V.L0 ↔ _
    rw [Module.Basis.equivFun_symm_apply]
    rfl
  set Hf := GlobalTheory.PlaceModel.half S T ε with hHf
  set P := (grpCo φ T BT g).1 with hP
  let Ψ : WO S T →+ Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v) :=
    AddMonoidHom.mk' (fun u => c • ((BT⁻¹).1 * u.map (rdA φ) * BS.1)) (fun x y => by
      simp only [Matrix.map_add _ (map_add _), Matrix.mul_add, Matrix.add_mul, smul_add])
  have hΨ : ∀ u, Ψ u = c • ((BT⁻¹).1 * u.map (rdA φ) * BS.1) := fun _ => rfl
  have hmemH : ∀ u ∈ Hf, (u ∈ halfLat S T ε ↔ Ψ u ∈ intMat D.host.F v T.rank S.rank) := by
    intro u hu
    have hu' : IsHalf ε u := (GlobalTheory.PlaceModel.isHalf_iff S T).2 hu
    rw [halfLat, AddSubgroup.mem_inf, hL S, hL T, hΨ]
    constructor
    · rintro ⟨h, -⟩ i j
      exact GlobalTheory.SplitHecke.isInt_Ov.1 ((hc u hu').1 h i j)
    · intro h
      exact ⟨(hc u hu').2 fun i j => GlobalTheory.SplitHecke.isInt_Ov.2 (h i j), hu⟩
  have hmt1 : Formalism.L2.Theta.mt S (1 : GA D S)⁻¹ = 1 := by
    rw [inv_one]; unfold Formalism.L2.Theta.mt; rw [map_one]; rfl
  have hA : ∀ u, Ψ (actL S T g u) = P * Ψ u := by
    intro u
    change Ψ (actO S T 1 g u) = _
    rw [actO, hmt1, Matrix.mul_one, hΨ, hΨ, hP, grpCo, Matrix.mul_smul]
    congr 1
    rw [Matrix.map_mul]
    simp only [Units.val_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc BT.1, Units.mul_inv, Matrix.one_mul]
    rfl
  have hAHf : ∀ u ∈ Hf, actL S T g u ∈ Hf := by
    intro u hu
    have hu' := (GlobalTheory.PlaceModel.isHalf_iff S T).2 hu
    refine (GlobalTheory.PlaceModel.isHalf_iff S T).1 fun i j => ?_
    show ε * actO S T 1 g u i j = actO S T 1 g u i j
    rw [actO, hmt1, Matrix.mul_one, Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    exact (mul_left_comm ε _ _).trans (congrArg (Formalism.L2.Theta.mt T g i k * ·) (hu' k j))
  let f : Hf →+ Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v) := Ψ.comp Hf.subtype
  have hbij := GlobalTheory.PlaceCoord.bijOn_map (S := S) (T := T) hch hε.1.1 hε.2.2
  have hf_inj : Function.Injective f := by
    intro x y hxy
    have hxy' : Ψ x = Ψ y := hxy
    rw [hΨ, hΨ] at hxy'
    have h1 : (BT⁻¹).1 * (x : WO S T).map (rdA φ) * BS.1 = (BT⁻¹).1 * (y : WO S T).map (rdA φ) * BS.1 :=
      smul_right_injective (Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v)) hc0 hxy'
    have h2 := congrArg (fun M => BT.1 * M * (BS⁻¹).1) h1
    simp only [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul] at h2
    simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one] at h2
    exact Subtype.ext (hbij.injOn ((GlobalTheory.PlaceModel.isHalf_iff S T).2 x.2) ((GlobalTheory.PlaceModel.isHalf_iff S T).2 y.2) h2)
  have hf_surj : Function.Surjective f := by
    intro y
    obtain ⟨t, ht, ht'⟩ := GlobalTheory.PlaceCoord.exists_half hch hε.1.1 hε.2.2 (c⁻¹ • (BT.1 * y * (BS⁻¹).1))
    refine ⟨⟨t, (GlobalTheory.PlaceModel.isHalf_iff S T).1 ht⟩, ?_⟩
    change Ψ t = y
    rw [hΨ, ht', Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_inv_cancel₀ hc0, one_smul]
    simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  have hH : halfLat S T ε ≤ Hf := inf_le_right
  have hK : (halfLat S T ε).map (actL S T g) ≤ Hf := by
    rintro _ ⟨u, hu, rfl⟩
    exact hAHf u (hH hu)
  have e1 : ((halfLat S T ε).addSubgroupOf Hf).map f = intMat D.host.F v T.rank S.rank := by
    ext y
    rw [AddSubgroup.mem_map]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact (hmemH w w.2).1 (AddSubgroup.mem_addSubgroupOf.1 hw)
    · intro hy
      obtain ⟨w, hw⟩ := hf_surj y
      refine ⟨w, AddSubgroup.mem_addSubgroupOf.2 ((hmemH w w.2).2 ?_), hw⟩
      exact hw ▸ hy
  have e2 : (((halfLat S T ε).map (actL S T g)).addSubgroupOf Hf).map f =
      (intMat D.host.F v T.rank S.rank).map (mulL P) := by
    ext y
    rw [AddSubgroup.mem_map, AddSubgroup.mem_map]
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨u, hu, hw⟩ := AddSubgroup.mem_map.1 (AddSubgroup.mem_addSubgroupOf.1 hw)
      refine ⟨Ψ u, (hmemH u (hH hu)).1 hu, ?_⟩
      change P * Ψ u = Ψ (w : WO S T)
      rw [← hw, hA]
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨w, hw⟩ := hf_surj z
      have hz' : Ψ w ∈ intMat D.host.F v T.rank S.rank := hw ▸ hz
      refine ⟨⟨actL S T g w, hAHf w w.2⟩, AddSubgroup.mem_addSubgroupOf.2 ⟨w, (hmemH w w.2).2 hz', rfl⟩, ?_⟩
      change Ψ (actL S T g w) = mulL P z
      rw [hA w, ← hw]
      rfl
  rw [← AddSubgroup.relIndex_addSubgroupOf hK, ← AddSubgroup.relIndex_map_map_of_injective _ _ hf_inj, e1, e2]

end GlobalTheory.SplitIdx

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexIntegralMatricesCartanDoubleCoset
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.SplitHecke GlobalTheory.LFun.ConjPlace GlobalTheory.AdelicU GlobalTheory.LFun.SplitTie

noncomputable section

namespace GlobalTheory.SplitIdx.LocIndex

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {m n : ℕ}

private theorem mulL_apply' {K : Type} [CommRing K] {a b : ℕ} (P : Matrix (Fin a) (Fin a) K)
    (y : Matrix (Fin a) (Fin b) K) : GlobalTheory.SplitIdx.mulL (n := b) P y = P * y := rfl

private theorem mem_intMat_iff' (y : Matrix (Fin m) (Fin n) (v.adicCompletion F)) :
    y ∈ GlobalTheory.SplitIdx.intMat F v m n ↔ ∀ i j, y i j ∈ v.adicCompletionIntegers F := Iff.rfl

theorem mulL_mul (A B : Matrix (Fin m) (Fin m) (v.adicCompletion F)) :
    GlobalTheory.SplitIdx.mulL (n := n) (A * B) = (GlobalTheory.SplitIdx.mulL (n := n) A).comp (GlobalTheory.SplitIdx.mulL B) :=
  AddMonoidHom.ext fun y => by
    rw [AddMonoidHom.comp_apply, mulL_apply', mulL_apply', mulL_apply', Matrix.mul_assoc]

theorem mulL_mem {P : Matrix (Fin m) (Fin m) (v.adicCompletion F)}
    (hP : ∀ i j, P i j ∈ v.adicCompletionIntegers F) {y : Matrix (Fin m) (Fin n) (v.adicCompletion F)}
    (hy : y ∈ GlobalTheory.SplitIdx.intMat F v m n) : GlobalTheory.SplitIdx.mulL P y ∈ GlobalTheory.SplitIdx.intMat F v m n := by
  refine (mem_intMat_iff' v _).2 fun i j => ?_
  rw [mulL_apply', Matrix.mul_apply]
  exact sum_mem fun k _ => mul_mem (hP i k) ((mem_intMat_iff' v _).1 hy k j)

private theorem entries_mem_integers_of_mem_KGL {k : GL (Fin m) (v.adicCompletion F)} (hk : k ∈ KGL v m) :
    (∀ i j, k.1 i j ∈ v.adicCompletionIntegers F) ∧ (∀ i j, (k⁻¹).1 i j ∈ v.adicCompletionIntegers F) :=
  (GlobalTheory.LatHecke.mem_GLint_iff_entry _ _).1 hk

theorem mulL_mem_iff {k : GL (Fin m) (v.adicCompletion F)} (hk : k ∈ KGL v m)
    (y : Matrix (Fin m) (Fin n) (v.adicCompletion F)) :
    GlobalTheory.SplitIdx.mulL k.1 y ∈ GlobalTheory.SplitIdx.intMat F v m n ↔ y ∈ GlobalTheory.SplitIdx.intMat F v m n := by
  refine ⟨fun h => ?_, fun h => mulL_mem v (entries_mem_integers_of_mem_KGL v hk).1 h⟩
  have e : y = GlobalTheory.SplitIdx.mulL (k⁻¹).1 (GlobalTheory.SplitIdx.mulL (n := n) k.1 y) := by
    rw [mulL_apply', mulL_apply', ← Matrix.mul_assoc, k.inv_mul, Matrix.one_mul]
  rw [e]
  exact mulL_mem v (entries_mem_integers_of_mem_KGL v hk).2 h

theorem map_mulL {k : GL (Fin m) (v.adicCompletion F)} (hk : k ∈ KGL v m) :
    (GlobalTheory.SplitIdx.intMat F v m n).map (GlobalTheory.SplitIdx.mulL k.1) = GlobalTheory.SplitIdx.intMat F v m n := by
  ext y
  rw [AddSubgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact mulL_mem v (entries_mem_integers_of_mem_KGL v hk).1 hx
  · intro hy
    refine ⟨GlobalTheory.SplitIdx.mulL (k⁻¹).1 y, mulL_mem v (entries_mem_integers_of_mem_KGL v hk).2 hy, ?_⟩
    rw [mulL_apply', mulL_apply', ← Matrix.mul_assoc, k.mul_inv, Matrix.one_mul]

theorem comap_mulL {k : GL (Fin m) (v.adicCompletion F)} (hk : k ∈ KGL v m)
    (P : Matrix (Fin m) (Fin m) (v.adicCompletion F)) :
    (GlobalTheory.SplitIdx.intMat F v m n).comap (GlobalTheory.SplitIdx.mulL (k.1 * P)) =
      (GlobalTheory.SplitIdx.intMat F v m n).comap (GlobalTheory.SplitIdx.mulL P) := by
  ext y
  rw [AddSubgroup.mem_comap, AddSubgroup.mem_comap, mulL_mul, AddMonoidHom.comp_apply, mulL_mem_iff v hk]

theorem zpow_mul_mem_iff {ϖ : v.adicCompletion F} (hϖ : IsUnifV F v ϖ) (hϖO : ϖ ∈ v.adicCompletionIntegers F)
    (d : ℤ) (x : v.adicCompletionIntegers F) :
    ϖ ^ d * (x : v.adicCompletion F) ∈ v.adicCompletionIntegers F ↔
      x ∈ Ideal.span {(⟨ϖ, hϖO⟩ : v.adicCompletionIntegers F) ^ (max (-d) 0).toNat} := by
  have hv : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hϖ
  have hne : ϖ ≠ 0 := fun h => by
    rw [h, map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  have ht : Valued.v (((⟨ϖ, hϖO⟩ : v.adicCompletionIntegers F) ^ (max (-d) 0).toNat : v.adicCompletionIntegers F) : v.adicCompletion F) ≠ 0 := by
    rw [SubmonoidClass.coe_pow, map_pow]
    exact pow_ne_zero _ ((Valuation.ne_zero_iff _).2 hne)
  rw [GlobalTheory.CNorm.mem_span_singleton_adicCompletionIntegers v ht, SubmonoidClass.coe_pow, map_pow]
  change Valued.v (ϖ ^ d * (x : v.adicCompletion F)) ≤ 1 ↔ _
  rw [map_mul, map_zpow₀, hv]
  have hx1 : Valued.v (x : v.adicCompletion F) ≤ 1 := x.2
  by_cases hx : (x : v.adicCompletion F) = 0
  · rw [hx, map_zero]
    simp
  · have hx0 : Valued.v (x : v.adicCompletion F) ≠ 0 := (Valuation.ne_zero_iff _).2 hx
    rw [← WithZero.exp_log hx0] at hx1 ⊢
    rw [← WithZero.exp_zsmul, ← WithZero.exp_nsmul, ← WithZero.exp_add, ← WithZero.exp_zero,
      WithZero.exp_le_exp, WithZero.exp_le_exp] at *
    simp only [smul_eq_mul, nsmul_eq_mul] at *
    omega

theorem card_quot_pow {ϖ : v.adicCompletion F} (hϖ : IsUnifV F v ϖ) (hϖO : ϖ ∈ v.adicCompletionIntegers F)
    (e : ℕ) :
    Nat.card (v.adicCompletionIntegers F ⧸ Ideal.span {(⟨ϖ, hϖO⟩ : v.adicCompletionIntegers F) ^ e}) =
      qV F v ^ e := by
  have hv : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hϖ
  refine (GlobalTheory.CNorm.isAdicComplete_and_card_quotient_adicCompletionIntegers F v).2 _ e ?_
  rw [SubmonoidClass.coe_pow, map_pow, hv, ← WithZero.exp_nsmul]
  congr 1
  simp

end GlobalTheory.SplitIdx.LocIndex

namespace GlobalTheory.SplitIdx.LocIndex

theorem toNat_sum {m : ℕ} (d : Fin m → ℤ) :
    (∑ i, max (-d i) 0).toNat = ∑ i, (max (-d i) 0).toNat := by
  have h : ∀ i, 0 ≤ max (-d i) 0 := fun i => le_max_right _ _
  apply @Nat.cast_injective ℤ
  rw [Int.toNat_of_nonneg (Finset.sum_nonneg fun i _ => h i), Nat.cast_sum]
  exact Finset.sum_congr rfl fun i _ => (Int.toNat_of_nonneg (h i)).symm

theorem relIndex_intMat : ∀ {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (m n : ℕ) (ϖ : v.adicCompletion F), IsUnifV F v ϖ → ∀ (d : Fin m → ℤ) (t : GL (Fin m) (v.adicCompletion F)), t.1 = Matrix.diagonal (fun i => ϖ ^ d i) → ∀ k₁ ∈ KGL v m, ∀ k₂ ∈ KGL v m, (GlobalTheory.SplitIdx.intMat F v m n).relIndex ((GlobalTheory.SplitIdx.intMat F v m n).map (GlobalTheory.SplitIdx.mulL (n := n) (k₁ * t * k₂).1)) = qV F v ^ (n * (∑ i, max (-d i) 0).toNat) := by
  intro F _ _ v m n ϖ hϖ d t ht k₁ hk₁ k₂ hk₂
  have hv : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hϖ
  have hϖO : ϖ ∈ v.adicCompletionIntegers F := by
    change Valued.v ϖ ≤ 1
    rw [hv, ← WithZero.exp_zero, WithZero.exp_le_exp]
    norm_num
  rw [← AddSubgroup.relIndex_comap, Units.val_mul, Units.val_mul, Matrix.mul_assoc, comap_mulL v hk₁,
    mulL_mul, ← AddSubgroup.comap_comap, AddSubgroup.relIndex_comap, map_mulL v hk₂, ht]
  let ψ : GlobalTheory.SplitIdx.intMat F v m n →+
      ((i : Fin m) → Fin n → v.adicCompletionIntegers F ⧸ Ideal.span {(⟨ϖ, hϖO⟩ : v.adicCompletionIntegers F) ^ (max (-d i) 0).toNat}) :=
    { toFun := fun y i j => Ideal.Quotient.mk _ ⟨y.1 i j, (mem_intMat_iff' v y.1).1 y.2 i j⟩
      map_zero' := by
        funext i j
        exact map_zero (Ideal.Quotient.mk (Ideal.span {(⟨ϖ, hϖO⟩ : v.adicCompletionIntegers F) ^ (max (-d i) 0).toNat}))
      map_add' := fun y z => by
        funext i j
        exact map_add (Ideal.Quotient.mk (Ideal.span {(⟨ϖ, hϖO⟩ : v.adicCompletionIntegers F) ^ (max (-d i) 0).toNat}))
          ⟨y.1 i j, (mem_intMat_iff' v y.1).1 y.2 i j⟩ ⟨z.1 i j, (mem_intMat_iff' v z.1).1 z.2 i j⟩ }
  have hψ : ∀ (y : GlobalTheory.SplitIdx.intMat F v m n) i j, ψ y i j =
      Ideal.Quotient.mk (Ideal.span {(⟨ϖ, hϖO⟩ : v.adicCompletionIntegers F) ^ (max (-d i) 0).toNat}) ⟨y.1 i j, (mem_intMat_iff' v y.1).1 y.2 i j⟩ :=
    fun _ _ _ => rfl
  have hker : ψ.ker = (AddSubgroup.comap (GlobalTheory.SplitIdx.mulL (n := n) (Matrix.diagonal fun i => ϖ ^ d i))
      (GlobalTheory.SplitIdx.intMat F v m n)).addSubgroupOf (GlobalTheory.SplitIdx.intMat F v m n) := by
    ext y
    rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_comap, mem_intMat_iff',
      mulL_apply']
    simp only [Matrix.diagonal_mul]
    constructor
    · intro h i j
      have h1 : ψ y i j = 0 := congrFun (congrFun h i) j
      rw [hψ, Ideal.Quotient.eq_zero_iff_mem] at h1
      exact (zpow_mul_mem_iff v hϖ hϖO (d i) ⟨y.1 i j, (mem_intMat_iff' v y.1).1 y.2 i j⟩).2 h1
    · intro h
      funext i j
      show ψ y i j = 0
      rw [hψ, Ideal.Quotient.eq_zero_iff_mem]
      exact (zpow_mul_mem_iff v hϖ hϖO (d i) ⟨y.1 i j, (mem_intMat_iff' v y.1).1 y.2 i j⟩).1 (h i j)
  have hsurj : Function.Surjective ψ := by
    intro z
    choose w hw using fun i j => Ideal.Quotient.mk_surjective (z i j)
    refine ⟨⟨fun i j => (w i j : v.adicCompletion F), (mem_intMat_iff' v _).2 fun i j => (w i j).2⟩, ?_⟩
    funext i j
    rw [hψ]
    exact hw i j
  rw [AddSubgroup.relIndex, ← hker, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hsurj,
    AddSubgroup.card_top, Nat.card_pi]
  simp only [Nat.card_pi, card_quot_pow v hϖ hϖO, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← pow_mul, Finset.prod_pow_eq_pow_sum]
  congr 1
  rw [toNat_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

end GlobalTheory.SplitIdx.LocIndex
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceAdjointMatrixIsCoordinateEquivariant
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceTensor.AdjCoord

variable {D : D7} {v : FinPl D}

def conjProj (φ : SplitProj D v) : SplitProj D v :=
  φ.comp (Algebra.TensorProduct.map (AlgHom.id (Fv D.host.F v) (Fv D.host.F v)) D.sp.cm.sig)

theorem rdA_conjProj (φ : SplitProj D v) (a : AE D) : rdA (conjProj φ) a = rdA φ (cA D a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp only [_root_.map_zero]
  | tmul x y =>
    simp only [rdA, conjProj, RingHom.comp_apply, cA, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, GlobalTheory.AdelicU.compFin,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  | add x y hx hy => simp only [_root_.map_add, hx, hy]

theorem isIdemOf_conjProj {φ : SplitProj D v} {e : AE D} (he : IsIdemOf φ e) : IsIdemOf (conjProj φ) (cA D e) := by
  have hcc : ∀ x : AE D, cA D (cA D x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp only [_root_.map_zero]
    | tmul a y =>
      simp only [cA, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
        AlgHom.id_apply]
      congr 1
      exact star_star y
    | add x y hx hy => simp only [_root_.map_add, hx, hy]
  refine ⟨GlobalTheory.SplitScalar.isSplitIdem_conj he.1, ?_, ?_⟩
  · rw [hcc, add_comm]; exact he.2.1
  · rw [rdA_conjProj, hcc]; exact he.2.2

def trHomeo {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {m n : ℕ}
    (A A' : Matrix (Fin n) (Fin n) K) (B B' : Matrix (Fin m) (Fin m) K) (hA : A' * A = 1) (hB : B * B' = 1) :
    Matrix (Fin m) (Fin n) K ≃ₜ Matrix (Fin n) (Fin m) K where
  toFun y := A * yᵀ * B
  invFun z := (A' * z * B')ᵀ
  left_inv y := by
    have : A' * (A * yᵀ * B) * B' = (A' * A) * yᵀ * (B * B') := by simp only [Matrix.mul_assoc]
    simp only [this, hA, hB, Matrix.one_mul, Matrix.mul_one, Matrix.transpose_transpose]
  right_inv z := by
    have : A * (A' * z * B') * B = (A * A') * z * (B' * B) := by simp only [Matrix.mul_assoc]
    simp only [Matrix.transpose_transpose, this, mul_eq_one_comm.1 hA, mul_eq_one_comm.1 hB, Matrix.one_mul,
      Matrix.mul_one]
  continuous_toFun := (continuous_const.matrix_mul continuous_id.matrix_transpose).matrix_mul continuous_const
  continuous_invFun := ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).matrix_transpose

theorem isCoord_comp {S T : HSp D} {m n : ℕ} {a : AE D} {Λ : AddSubgroup (WO S T)}
    {κ : WO S T → Matrix (Fin m) (Fin n) (Fv D.host.F v)} (h : IsCoord a Λ κ)
    (A A' : Matrix (Fin n) (Fin n) (Fv D.host.F v)) (B B' : Matrix (Fin m) (Fin m) (Fv D.host.F v))
    (hA : A' * A = 1) (hB : B * B' = 1) : IsCoord a Λ (fun t => A * (κ t)ᵀ * B) := by
  have e : (fun t => A * (κ t)ᵀ * B) = ⇑(trHomeo A A' B B' hA hB) ∘ κ := rfl
  refine ⟨fun x y => ?_, ?_, ?_, ?_⟩
  · simp only [h.1 x y, Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul]
  · rw [e]; exact (Set.bijOn_univ.2 (trHomeo A A' B B' hA hB).bijective).comp h.2.1
  · rw [e, Set.image_comp]; exact (trHomeo A A' B B' hA hB).isOpenMap _ h.2.2.1
  · rw [e, Set.image_comp]; exact h.2.2.2.image (trHomeo A A' B B' hA hB).continuous

theorem gram_inv_mul (V : HSp D) : (V.gram⁻¹).map (incA D) * V.gram.map (incA D) = 1 := by
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (GlobalTheory.LatVac.gram_det_isUnit V)]
  exact Matrix.map_one _ (_root_.map_zero _) (_root_.map_one _)

theorem adj_mul {A : Type} [CommRing A] (σ : A →+* A) {a b : ℕ} (G G' k k' : Matrix (Fin a) (Fin a) A)
    (H m m' : Matrix (Fin b) (Fin b) A) (x : Matrix (Fin b) (Fin a) A) (h1 : G' * G = 1)
    (hk : Formalism.UG.cT σ k * G * k = G) (hm : Formalism.UG.cT σ m * H * m = H) (hk' : k * k' = 1) (hm' : m * m' = 1) :
    G' * Formalism.UG.cT σ (m * x * k) * H = k' * (G' * Formalism.UG.cT σ x * H) * m' := by
  have hG : G * G' = 1 := mul_eq_one_comm.1 h1
  have s1 : Formalism.UG.cT σ k * G = G * k' := calc
    Formalism.UG.cT σ k * G = Formalism.UG.cT σ k * G * (k * k') := by rw [hk', Matrix.mul_one]
    _ = (Formalism.UG.cT σ k * G * k) * k' := by simp only [Matrix.mul_assoc]
    _ = G * k' := by rw [hk]
  have e1 : G' * Formalism.UG.cT σ k = k' * G' := calc
    G' * Formalism.UG.cT σ k = G' * (Formalism.UG.cT σ k * (G * G')) := by rw [hG, Matrix.mul_one]
    _ = G' * ((Formalism.UG.cT σ k * G) * G') := by simp only [Matrix.mul_assoc]
    _ = (G' * G) * k' * G' := by rw [s1]; simp only [Matrix.mul_assoc]
    _ = k' * G' := by rw [h1, Matrix.one_mul]
  have e2 : Formalism.UG.cT σ m * H = H * m' := calc
    Formalism.UG.cT σ m * H = Formalism.UG.cT σ m * H * (m * m') := by rw [hm', Matrix.mul_one]
    _ = (Formalism.UG.cT σ m * H * m) * m' := by simp only [Matrix.mul_assoc]
    _ = H * m' := by rw [hm]
  unfold Formalism.UG.cT at *
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul]
  calc G' * ((k.map σ)ᵀ * ((x.map σ)ᵀ * (m.map σ)ᵀ)) * H
      = (G' * (k.map σ)ᵀ) * (x.map σ)ᵀ * ((m.map σ)ᵀ * H) := by simp only [Matrix.mul_assoc]
    _ = k' * (G' * (x.map σ)ᵀ * H) * m' := by rw [e1, e2]; simp only [Matrix.mul_assoc]

theorem map_mul_conj {A K : Type} [CommRing A] [CommRing K] (π : A →+* K) {a b : ℕ} (P : GL (Fin a) K) (Q : GL (Fin b) K)
    (k : Matrix (Fin a) (Fin a) A) (m : Matrix (Fin b) (Fin b) A) (X Y : Matrix (Fin a) (Fin b) A) (h : Y = k * X * m) :
    (P⁻¹).val * Y.map π * Q.val =
      ((P⁻¹).val * k.map π * P.val) * ((P⁻¹).val * X.map π * Q.val) * ((Q⁻¹).val * m.map π * Q.val) := by
  subst h
  simp only [Matrix.map_mul, Matrix.mul_assoc, Units.mul_inv_cancel_left]
  first
  | rw [Units.mul_inv_cancel_left]
  | rw [← Matrix.mul_assoc (P : Matrix (Fin a) (Fin a) K), Units.mul_inv, Matrix.one_mul]

theorem mt_mul_mt_inv (V : HSp D) (g : GA D V) : Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V g⁻¹ = 1 := by
  unfold Formalism.L2.Theta.mt
  rw [← Units.val_mul, ← _root_.map_mul, _root_.mul_inv_cancel, _root_.map_one, Units.val_one]

theorem grpCo_val (φ : SplitProj D v) (V : HSp D) (B : GL (Fin V.rank) (Fv D.host.F v)) (g : GA D V) :
    (grpCo φ V B g).val = (B⁻¹).val * (Formalism.L2.Theta.mt V g).map (rdA φ) * B.val := rfl

theorem grpCo_inv (φ : SplitProj D v) (V : HSp D) (B : GL (Fin V.rank) (Fv D.host.F v)) (g : GA D V) :
    (grpCo φ V B g)⁻¹ = grpCo φ V B g⁻¹ := by
  simp only [grpCo, _root_.mul_inv_rev, _root_.inv_inv, _root_.map_inv, _root_.mul_assoc]

theorem adjCo_actO (φ : SplitProj D v) (S T : HSp D) (BS : GL (Fin S.rank) (Fv D.host.F v))
    (BT : GL (Fin T.rank) (Fv D.host.F v)) (g : GA D S) (h : GA D T) (t : WO S T) :
    adjCo φ S T BS BT (actO S T g⁻¹ h⁻¹ t) = ((grpCo φ S BS g)⁻¹).val * adjCo φ S T BS BT t * (grpCo φ T BT h).val := by
  have hm' : Formalism.L2.Theta.mt T h⁻¹ * Formalism.L2.Theta.mt T h = 1 := by
    simpa only [_root_.inv_inv] using mt_mul_mt_inv T h⁻¹
  have key := adj_mul (cA D) (S.gram.map (incA D)) ((S.gram⁻¹).map (incA D)) (Formalism.L2.Theta.mt S g)
    (Formalism.L2.Theta.mt S g⁻¹) (T.gram.map (incA D)) (Formalism.L2.Theta.mt T h⁻¹) (Formalism.L2.Theta.mt T h)
    (t : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (gram_inv_mul S) (by exact g.2) (by exact h⁻¹.2)
    (mt_mul_mt_inv S g) hm'
  unfold Formalism.UG.cT at key
  have hact : (actO S T g⁻¹ h⁻¹ t : Matrix (Fin T.rank) (Fin S.rank) (AE D)) =
      Formalism.L2.Theta.mt T h⁻¹ * t * Formalism.L2.Theta.mt S g := by
    first
    | rfl
    | (simp only [actO, _root_.inv_inv]; done)
    | simp [actO]
  unfold adjCo
  rw [hact, key, map_mul_conj (rdA φ) BS BT (Formalism.L2.Theta.mt S g⁻¹) (Formalism.L2.Theta.mt T h) _ _ rfl, grpCo_inv,
    grpCo_val, grpCo_val]

end GlobalTheory.PlaceTensor.AdjCoord

namespace GlobalTheory.PlaceTensor

open AdjCoord

theorem adjCo_isCoord : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (v : FinPl D) (φ : SplitProj D v) (e : AE D), IsIdemOf φ e → ∀ (BS : GL (Fin S.rank) (Fv D.host.F v)) (BT : GL (Fin T.rank) (Fv D.host.F v)), IsCoord (cA D e) (latO S T ΛS ΛT fun _ => True) (adjCo φ S T BS BT) ∧ ∀ (g : GA D S) (h : GA D T) (t : WO S T), adjCo φ S T BS BT (actO S T g⁻¹ h⁻¹ t) = ((grpCo φ S BS g)⁻¹).val * adjCo φ S T BS BT t * (grpCo φ T BT h).val := by
  intro D S T ΛS ΛT hS hT v φ e he BS BT
  refine ⟨?_, fun g h t => adjCo_actO φ S T BS BT g h t⟩
  have hc := (GlobalTheory.T.splitPlace_matrix_coordinate_on_half D S T ΛS ΛT hS hT v (conjProj φ) (cA D e) (isIdemOf_conjProj he) 1 1).1
  have h1 : ((S.gram⁻¹).map (incA D)).map (rdA φ) * (S.gram.map (incA D)).map (rdA φ) = 1 := by
    rw [← Matrix.map_mul, gram_inv_mul, Matrix.map_one _ (_root_.map_zero _) (_root_.map_one _)]
  have h2 : ((T.gram⁻¹).map (incA D)).map (rdA φ) * (T.gram.map (incA D)).map (rdA φ) = 1 := by
    rw [← Matrix.map_mul, gram_inv_mul, Matrix.map_one _ (_root_.map_zero _) (_root_.map_one _)]
  have hA : ((S.gram.map (incA D)).map (rdA φ) * BS.val) * ((BS⁻¹).val * ((S.gram⁻¹).map (incA D)).map (rdA φ)) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc BS.val, Units.mul_inv, Matrix.one_mul]
    exact mul_eq_one_comm.1 h1
  have hB : ((T.gram.map (incA D)).map (rdA φ) * BT.val) * ((BT⁻¹).val * ((T.gram⁻¹).map (incA D)).map (rdA φ)) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc BT.val, Units.mul_inv, Matrix.one_mul]
    exact mul_eq_one_comm.1 h2
  convert isCoord_comp hc _ _ _ _ hA hB using 1
  funext t
  have ht : (((t : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (cA D))ᵀ).map (rdA φ) =
      ((t : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (rdA (conjProj φ)))ᵀ := by
    ext i j
    simp only [Matrix.map_apply, Matrix.transpose_apply, rdA_conjProj]
  simp only [adjCo, mapCo, Matrix.map_mul, ht, _root_.inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one,
    Matrix.mul_assoc]

end GlobalTheory.PlaceTensor

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SuppAtUnitaryGroupLocalToAdelicEmbedding
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.SplitHecke GlobalTheory.LFun.ConjPlace GlobalTheory.AdelicU GlobalTheory.LFun.SplitTie

noncomputable section

namespace GlobalTheory.SuppAtPlace

theorem suppAt_embV : ∀ (D : D7) (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)), w.under (𝓞 D.host.F) = v → ∀ ε : AE D, Formalism.L2.NTheta.IsIdemAt ε w → ∀ g : Gv V v, SuppAt ε V (embV V v g) := by
  intro D V v w h ε he g
  have hP : IsPrimeIdem w ε (ε + cA D ε) := Or.inl ⟨he, rfl⟩
  exact (Supp.suppF_iff_of_isPrimeIdem V hP h _).2 ⟨g, rfl⟩

end GlobalTheory.SuppAtPlace
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionVacuumEqResidueDetCharOfFrameStabilizeStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.StepLaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilAction_vacuum_eq_residueDetChar_of_frameStabilizer : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (θ : InfFam D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (e : AE D) (P : Finset (Pl D.host.E)) (cS cT : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (f : WO S T → ℂ), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → S.SigOK → T.SigOK → (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → IsSelfDualC S ΛS → IsSelfDualC T ΛT → IsFrame βS ΛS → IsFrame βT ΛT → IsIdemSum e P → TameOn χS e P cS → TameOn χT e P cT → (∀ v ε, NonSplitAt D v ε → UnramAt ε χS → UnramAt ε χT → FixesVacAt ψ S T ΛS ΛT om v ε) → IsVacO ψ θ S T sS sT ΛS ΛT f → ∀ g ∈ GfC S, ∀ h ∈ GfC T, finE S g ∈ St βS → finE T h ∈ St βT → om (g, h) f = vacScal βS βT P cS cT g h • f := by
  first | exact @GlobalTheory.VacLaw.vac_law | exact GlobalTheory.VacLaw.vac_law | (intros; apply GlobalTheory.VacLaw.vac_law <;> assumption)
end

