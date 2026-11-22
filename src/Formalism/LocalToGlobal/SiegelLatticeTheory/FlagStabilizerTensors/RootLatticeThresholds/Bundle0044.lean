import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0043
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0024
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.UnipotentInLevelSubgroup
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0029
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0044
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0040
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.SubMemOfIndQ
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0031
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.XLeSpanEXLam

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsEtAlg
section
noncomputable section

open MonoidAlgebra MeasureTheory

namespace Formalism.L2.SG.Pf.AllRowsEtAlg

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.SG.HidaSetting Formalism.L2.SG.AllRowsOf Formalism.L2.SG.Pf.AllRowsGA
  Formalism.L2.SG.Pf.AllRowsFin Formalism.L2.SG.Pf.AllRowsRhoX Formalism.L2.SG.Pf.AllRowsES Formalism.L2.SG.Pf.unitaryCongruence

variable {D : D7} {X : HidaSetting D} (hS : Function.Surjective (rhoX X))
include hS

def Ehat : MonoidAlgebra ℂ (G0g D.nd) := MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm (hat hS X.B.e))

theorem Ehat_coeff (γ : G0g D.nd) : (Ehat hS).coeff γ = hat hS X.B.e γ := by
  simp [Ehat, MonoidAlgebra.coeff_ofCoeff]

theorem Ehat_idem : Ehat hS * Ehat hS = Ehat hS := by
  apply MonoidAlgebra.ext
  ext γ
  rw [coeff_mul_fin]
  simp only [Ehat_coeff hS]
  exact hat_e_idem hS γ

theorem hat_inv {f : X.B.I.Gf → ℂ} (hf : BiInv X f) (hsa : ∀ x, f x⁻¹ = star (f x)) (γ : G0g D.nd) :
    hat hS f γ⁻¹ = star (hat hS f γ) := by
  have h1 : f ((sec hS γ⁻¹ : KSub X.B.I) : X.B.I.Gf) = f (((sec hS γ)⁻¹ : KSub X.B.I) : X.B.I.Gf) := by
    rw [val_hat hS hf, val_hat hS hf, rho_sec, map_inv, rho_sec]
  have hcoe : (((sec hS γ)⁻¹ : KSub X.B.I) : X.B.I.Gf) = ((sec hS γ : KSub X.B.I) : X.B.I.Gf)⁻¹ := rfl
  unfold hat
  rw [h1, hcoe, hsa, star_mul', Complex.star_def, Complex.conj_ofReal]

theorem Ehat_selfadj : conjA (Ehat hS) = Ehat hS := by
  apply MonoidAlgebra.ext
  ext γ
  rw [conjA_coeff, Ehat_coeff hS, Ehat_coeff hS, hat_inv hS (biInv_e X) X.B.e_adm.2.2.1 γ, star_star]

theorem hat_eT' (S : Set (Tup2 D)) (γ : G0g D.nd) : hat hS (eT X S) γ = (Ehat hS * ES S).coeff γ := by
  rw [hat_eT hS S γ, coeff_mul_fin]
  simp only [Ehat_coeff hS]

theorem prod_idem (S : Set (Tup2 D)) : (Ehat hS * ES S) * (Ehat hS * ES S) = Ehat hS * ES S := by
  rw [mul_assoc, ES_central S (Ehat hS * ES S), mul_assoc, ← mul_assoc (Ehat hS) (Ehat hS), Ehat_idem hS,
    ES_idem]

theorem prod_selfadj (S : Set (Tup2 D)) : conjA (Ehat hS * ES S) = Ehat hS * ES S := by
  rw [conjA_mul, ES_selfadj, Ehat_selfadj hS, ES_central]

theorem eT_idem (S : Set (Tup2 D)) : X.B.I.convF X.B.μf (eT X S) (eT X S) = eT X S := by
  apply hat_inj hS (biInv_conv hS (biInv_eT X S) (biInv_eT X S)) (biInv_eT X S)
  intro γ
  rw [conv_hat hS (biInv_eT X S) (biInv_eT X S) γ]
  simp only [hat_eT' hS S]
  rw [← coeff_mul_fin, prod_idem hS S]

theorem eT_inv (S : Set (Tup2 D)) (x : X.B.I.Gf) : eT X S x⁻¹ = star (eT X S x) := by
  by_cases hx : x ∈ X.B.I.Kset
  · have key : eT X S x = hat hS (eT X S) (rhoX X ⟨x, hx⟩) / (V X : ℂ) := val_hat hS (biInv_eT X S) ⟨x, hx⟩
    have k1 : eT X S x⁻¹ = hat hS (eT X S) (rhoX X ⟨x, hx⟩)⁻¹ / (V X : ℂ) := by
      have := val_hat hS (biInv_eT X S) (⟨x, hx⟩ : KSub X.B.I)⁻¹
      rwa [map_inv] at this
    have hc : ∀ γ, (Ehat hS * ES S).coeff γ⁻¹ = star ((Ehat hS * ES S).coeff γ) := by
      intro γ
      conv_lhs => rw [← prod_selfadj hS S]
      rw [conjA_coeff, inv_inv]
    rw [k1, key, hat_eT' hS S, hat_eT' hS S, hc, star_div₀, Complex.star_def, Complex.conj_ofReal]
  · have hx' : x⁻¹ ∉ X.B.I.Kset := fun h => hx (by simpa using K_inv X.B.I h)
    rw [eT_of_not_mem X S hx, eT_of_not_mem X S hx', star_zero]

section Pos

open scoped ComplexOrder

omit hS in

theorem posType_of (I : AutInst) (μ : Measure I.Gf) [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ]
    {f : I.Gf → ℂ} (hc : Continuous f) {C : Set I.Gf} (hC : IsCompact C) (hCo : IsOpen C)
    (hsupp : ∀ x, f x ≠ 0 → x ∈ C) (hconv : I.convF μ f f = f) (hsa : ∀ x, f x⁻¹ = star (f x)) :
    I.IsPosType f := by
  intro m x c
  have hsub : ∀ i j, f ((x i)⁻¹ * x j) = ∫ z, star (f (z⁻¹ * x i)) * f (z⁻¹ * x j) ∂μ := by
    intro i j
    conv_lhs => rw [← hconv]
    have := integral_mul_left_eq_self (μ := μ) (fun y => f y * f (y⁻¹ * ((x i)⁻¹ * x j))) (x i)⁻¹
    show ∫ y, f y * f (y⁻¹ * ((x i)⁻¹ * x j)) ∂μ = _
    rw [← this]
    congr 1
    funext z
    rw [← hsa (z⁻¹ * x i)]
    congr 1 <;> congr 1 <;> group
  have hint : ∀ i j, Integrable (fun z => star (f (z⁻¹ * x i)) * f (z⁻¹ * x j)) μ := by
    intro i j
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact ((hc.comp (continuous_inv.mul continuous_const)).star).mul
        (hc.comp (continuous_inv.mul continuous_const))
    · refine HasCompactSupport.intro
        (IsCompact.image (f := fun y : I.Gf => x j * y⁻¹) hC (continuous_const.mul continuous_inv)) ?_
      intro z hz
      have h0 : f (z⁻¹ * x j) = 0 := by
        by_contra h
        apply hz
        exact ⟨z⁻¹ * x j, hsupp _ h, by group⟩
      rw [h0, mul_zero]
  have hF : ∀ z, ((Complex.normSq (∑ j, c j * f (z⁻¹ * x j)) : ℝ) : ℂ) =
      ∑ i, ∑ j, star (c i) * c j * (star (f (z⁻¹ * x i)) * f (z⁻¹ * x j)) := by
    intro z
    rw [Complex.normSq_eq_conj_mul_self, ← Complex.star_def, star_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [star_mul']
    ring
  have key : ∫ z, ((Complex.normSq (∑ j, c j * f (z⁻¹ * x j)) : ℝ) : ℂ) ∂μ =
      ∑ i, ∑ j, star (c i) * c j * f ((x i)⁻¹ * x j) := by
    simp_rw [hF]
    rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => (hint i j).const_mul _))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finset_sum _ (fun j _ => (hint i j).const_mul _)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul, hsub]
  rw [← key, integral_complex_ofReal]
  exact Complex.zero_le_real.2 (integral_nonneg fun z => Complex.normSq_nonneg _)

end Pos

theorem eT_pos (S : Set (Tup2 D)) : X.B.I.IsPosType (eT X S) := by
  exact posType_of X.B.I X.B.μf (isLocallyConstant_eT X S).continuous (PI.WAU.Cpt.isCompact_Kset X.B.I)
    (PI.WAU.kset_open X.B.I) (fun x hx => by_contra fun h => hx (eT_of_not_mem X S h)) (eT_idem hS S)
    (eT_inv hS S)

theorem etAlg_of (S : Set (Tup2 D)) : EtAlg X S :=
  ⟨eT_idem hS S, eT_inv hS S, eT_pos hS S⟩

end Formalism.L2.SG.Pf.AllRowsEtAlg
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmpFibreConstHolds
section
noncomputable section

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full

namespace Formalism.L2.SG.Pf.FibreCounting

theorem AmpFibreConst_holds {D : D7} {X : HidaSetting D} (Y : Full X) : Formalism.L2.SG.LoopTieOf.AmpFibreConst Y :=
  ampFibreConst_of Formalism.L2.SG.Pf.ratPt_holds Formalism.L2.SG.Closed.ChiTrivialC_holds Y

end Formalism.L2.SG.Pf.FibreCounting
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ContinuousCw
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Matrix Topology

namespace Formalism.L2.S.L6.UnitaryStandardVectors

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.Carrier.JointQuot

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def Cw (w : Point D.host.E (D.R.rS + 1)) (c : FreeE w → ℂ) : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ :=
  Matrix.of fun i j => if i = j then 1 else if h : i < j ∧ blkOf w.1 i.1 = blkOf w.1 j.1 then c ⟨(i, j), h⟩ else 0

theorem isUB_Cw (w : Point D.host.E (D.R.rS + 1)) (c : FreeE w → ℂ) : IsUB (blkW w) (Cw w c) := by
  refine ⟨fun i => by simp [Cw], fun i j hij => ?_⟩
  simp only [Cw, Matrix.of_apply] at hij
  split_ifs at hij with h1 h2
  · subst h1; exact ⟨le_rfl, rfl⟩
  · exact ⟨h2.1.le, h2.2⟩
  · exact absurd rfl hij

theorem continuous_Cw (w : Point D.host.E (D.R.rS + 1)) : Continuous fun c : FreeE w → ℂ => Cw w c := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [Cw, Matrix.of_apply]
  split_ifs with h1 h2
  · exact continuous_const
  · exact continuous_apply _
  · exact continuous_const

theorem Cw_apply_free (w : Point D.host.E (D.R.rS + 1)) (c : FreeE w → ℂ) (p : FreeE w) :
    Cw w c p.1.1 p.1.2 = c p := by
  simp only [Cw, Matrix.of_apply]
  rw [if_neg (ne_of_lt p.2.1), dif_pos p.2]
  rfl

theorem inv_eq_adj {m : ℕ} {blk : Fin m → ℕ} {C : Matrix (Fin m) (Fin m) ℂ} (hC : IsUB blk C) : C⁻¹ = C.adjugate := by
  rw [Matrix.inv_def, hC.det_eq_one, Ring.inverse_one, one_smul]

theorem span_frm_le (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (w : D.what₂.Word) (v : InfinitePlace X.B.I.F) (k : ℕ)
    (hk : k ≤ D.R.rS) :
    Submodule.span ℂ (frm X w D.host.rdE v '' {a | a.1 < k}) ≤
      spanLt (fun a => rv X.B.I v (X.eR a)) k := by
  rw [Submodule.span_le]
  rintro _ ⟨a, ha, rfl⟩
  have ha' : a.1 < D.R.rS := lt_of_lt_of_le ha hk
  obtain ⟨b, rfl⟩ : ∃ b : Fin D.R.rS, a = b.castSucc := ⟨⟨a.1, ha'⟩, Fin.ext rfl⟩
  simp only [frm, famSc, fam_castSucc, SetLike.mem_coe]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, ?_, rfl⟩)
  simpa using ha

theorem frm_castSucc (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (w : D.what₂.Word) (v : InfinitePlace X.B.I.F) (b : Fin D.R.rS) :
    frm X w D.host.rdE v b.castSucc = (((D.host.rdE : ℂ) ^ (D.R.rS - b.1))⁻¹) • rv X.B.I v (X.eR b) := by
  simp only [frm, famSc, fam_castSucc, Fin.val_castSucc]

theorem frm_last (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (w : D.what₂.Word) (v : InfinitePlace X.B.I.F) :
    frm X w D.host.rdE v (Fin.last D.R.rS) = rv X.B.I v (X.zR w) := by
  simp only [frm, famSc, fam_last, Fin.val_last, Nat.sub_self, pow_zero, inv_one, one_smul]

theorem comb_mem (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (w : D.what₂.Word) (v : InfinitePlace X.B.I.F)
    {blk : Fin (D.R.rS + 1) → ℕ} {A : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ} (hA : IsUB blk A)
    (a' : Fin (D.R.rS + 1)) :
    ∑ a'', (A - 1) a'' a' • frm X w D.host.rdE v a'' ∈ Submodule.span ℂ (frm X w D.host.rdE v '' {a | a.1 < a'.1}) := by
  refine Submodule.sum_mem _ fun a'' _ => ?_
  by_cases h : (A - 1) a'' a' = 0
  · rw [h, zero_smul]; exact Submodule.zero_mem _
  · have hne : a'' ≠ a' := by intro he; subst he; apply h; simp [hA.1]
    have hA0 : A a'' a' ≠ 0 := by intro h0; apply h; simp [h0, Matrix.one_apply, hne]
    have hlt : a'' < a' := lt_of_le_of_ne (hA.2 _ _ hA0).1 hne
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a'', hlt, rfl⟩)

end Formalism.L2.S.L6.UnitaryStandardVectors
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.FibreCountEqHolds
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.PackageTie2

namespace Formalism.L2.SG.Pf.FibreEq

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} {Y : Formalism.L2.SG.Full.Full X} {u u' : D.what₂.Word}

theorem partner (hN : Formalism.L2.SG.PoincareInHH.Cut.NeatKu X u' Y.hK) (hIR : Formalism.L2.SG.Pf.SatGramRep.IotaRepC)
    {l₁ l₂ s₁ : TT Y u u'} (hrow : rowOf Y.TR (Y.cs u) (Y.cs u') l₁ = rowOf Y.TR (Y.cs u) (Y.cs u') l₂)
    (h : l₁.toTerm = s₁.toTerm) :
    ∃ s₂ : TT Y u u', s₂.toTerm = l₂.toTerm ∧
      rowOf Y.TR (Y.cs u) (Y.cs u') s₁ = rowOf Y.TR (Y.cs u) (Y.cs u') s₂ := by
  obtain ⟨γ, rfl⟩ := Formalism.L2.SG.Pf.KernelOfEmbedding.fib_gam hN h
  refine ⟨Formalism.L2.SG.Pf.KernelOfEmbedding.act Y ⟨l₁.lam', l₁.mem'⟩ γ l₂, Formalism.L2.SG.Pf.KernelOfEmbedding.toTerm_act _ _ _, ?_⟩
  have hl := Formalism.L2.SG.Pf.KernelOfEmbedding.lam_eq_of_row hrow
  have i1 := Formalism.L2.SG.Pf.KernelOfEmbedding.iota_act hIR ⟨l₁.lam', l₁.mem'⟩ γ l₁ rfl
  have i2 := Formalism.L2.SG.Pf.KernelOfEmbedding.iota_act hIR ⟨l₁.lam', l₁.mem'⟩ γ l₂ hl.2.symm
  have hι : iotaOf Y.TR (Y.cs u) (Y.cs u') l₁ = iotaOf Y.TR (Y.cs u) (Y.cs u') l₂ :=
    congrArg (fun r => r.2.2) hrow
  unfold rowOf
  simp only [Prod.mk.injEq, Subtype.mk.injEq]
  exact ⟨hl.1, hl.2, by rw [i1, i2, hι]⟩

theorem fibreCountEq_of (hF : FinX Y) (hN : ∀ u' : D.what₂.Word, Formalism.L2.SG.PoincareInHH.Cut.NeatKu X u' Y.hK)
    (hIR : Formalism.L2.SG.Pf.SatGramRep.IotaRepC) (hRF : Formalism.L2.SG.Pf.FibreCounting.RowFree Y) :
    Formalism.L2.SG.Pf.KernelOfEmbedding.FibreCountEq hF := by
  intro u u' q
  let _ := hF.fibFT q.1.1
  let _ := hF.fibFT q.1.2
  obtain ⟨l₁, l₂, hrow⟩ := q.2
  have hinner : ∀ r₁ : fib Y q.1.1,
      ∑ r₂ : fib Y q.1.2, (if Formalism.L2.SG.Pf.KernelOfEmbedding.row Y r₁.1 = Formalism.L2.SG.Pf.KernelOfEmbedding.row Y r₂.1 then
        Formalism.MainNotions.S.wRow D (X.Fu u') r₁.1.lam' else 0) = Formalism.MainNotions.S.wRow D (X.Fu u') r₁.1.lam' := by
    intro r₁
    obtain ⟨s₂, hs₂t, hs₂r⟩ := partner (hN u') hIR hrow (l₁.2.trans r₁.2.symm)
    have hs₂ : s₂.toTerm = q.1.2 := hs₂t.trans l₂.2
    refine (Finset.sum_eq_single (s := (Finset.univ : Finset (fib Y q.1.2))) (show fib Y q.1.2 from ⟨s₂, hs₂⟩)
      (fun b _ hb => ?_) (fun hb => absurd (Finset.mem_univ _) hb)).trans (if_pos hs₂r)
    refine if_neg (fun hrb => hb (Subtype.ext ?_))
    exact hRF u u' b.1 s₂ (b.2.trans hs₂.symm) (hrb.symm.trans hs₂r)
  have hlam : ∀ r₁ : fib Y q.1.1, r₁.1.lam' = l₁.1.lam' := fun r₁ =>
    Formalism.L2.SG.Pf.FibreCounting.lam'_eq (r₁.2.trans l₁.2.symm)
  have hsum : ∑ r₁ : fib Y q.1.1, ∑ r₂ : fib Y q.1.2, (if Formalism.L2.SG.Pf.KernelOfEmbedding.row Y r₁.1 = Formalism.L2.SG.Pf.KernelOfEmbedding.row Y r₂.1
      then Formalism.MainNotions.S.wRow D (X.Fu u') r₁.1.lam' else 0) =
      (Fintype.card (fib Y q.1.1) : ℝ) * Formalism.MainNotions.S.wRow D (X.Fu u') l₁.1.lam' := by
    rw [Finset.sum_congr rfl (fun r₁ _ => (hinner r₁).trans (by rw [hlam r₁])), Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
  rw [Fintype.sum_prod_type]
  refine hsum.trans ?_
  obtain ⟨f, hf⟩ := Formalism.L2.SG.Pf.FibreCounting.fib_bij (hN u') l₁.1
  have hcard : Fintype.card (fib Y q.1.1) = Nat.card ↥(autLz D (X.Fu u') l₁.1.lam') := by
    rw [← Nat.card_eq_fintype_card]
    have e1 : fib Y q.1.1 ≃ {s : TT Y u u' // s.toTerm = l₁.1.toTerm} :=
      Equiv.subtypeEquivRight (fun s => by rw [l₁.2])
    exact (Nat.card_congr e1).trans (Nat.card_congr (Equiv.ofBijective f hf))
  have hpos : 0 < Fintype.card (fib Y q.1.1) := Fintype.card_pos_iff.2 ⟨l₁⟩
  unfold Formalism.MainNotions.S.wRow
  rw [← hcard]
  exact mul_inv_cancel₀ (Nat.cast_ne_zero.2 hpos.ne')

theorem fibreCountEq_of' (hF : FinX Y) (hIR : Formalism.L2.SG.Pf.SatGramRep.IotaRepC) (hRF : Formalism.L2.SG.Pf.FibreCounting.RowFree Y) :
    Formalism.L2.SG.Pf.KernelOfEmbedding.FibreCountEq hF :=
  fibreCountEq_of hF (fun u' => Formalism.L2.SG.Closed.NeatKu_holds X u' Y.hK) hIR hRF

theorem FibreCountEq_holds (hF : FinX Y) : Formalism.L2.SG.Pf.KernelOfEmbedding.FibreCountEq hF :=
  fibreCountEq_of' hF Formalism.L2.SG.Pf.iotaRepC_holds
    (Formalism.L2.SG.Pf.Act.rowFree_of (fun u' => Formalism.L2.SG.Closed.NeatKu_holds X u' Y.hK) Formalism.L2.SG.Pf.iotaRepC_holds)

end Formalism.L2.SG.Pf.FibreEq
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.FibreCountHolds
section
noncomputable section

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full

namespace Formalism.L2.SG.Pf.FibreCounting

theorem FibreCount_holds {D : D7} {X : HidaSetting D} (Y : Full X) : Formalism.L2.SG.LoopTieOf.FibreCount Y :=
  fibreCount_of (Formalism.L2.SG.Pf.Act.rowFree_of (fun u' => Formalism.L2.SG.Closed.NeatKu_holds X u' Y.hK)
    Formalism.L2.SG.Pf.iotaRepC_holds)

end Formalism.L2.SG.Pf.FibreCounting
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.IotaKerHolds
section
namespace Formalism.L2.SG.Pf.KernelOfEmbedding

theorem IotaKer_holds : Formalism.L2.SG.Pf.FinXP.IotaKer := by
  intro D X Y u u' s₁ s₂ t₁ t₂ n₁ n₂ m₁ m₂ c₁ c₂
  exact iotaKer_core (Formalism.L2.SG.Closed.NeatKu_holds X u' Y.hK) Formalism.L2.SG.Pf.iotaRepC_holds s₁ s₂ t₁ t₂ n₁ n₂ m₁ m₂ c₁ c₂

end Formalism.L2.SG.Pf.KernelOfEmbedding
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.KppCharC
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.KppChar

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.RowDictPf Formalism.L2.SG.Pf.AllRowsRedKerA
  Formalism.L2.SG.Pf.AllRowsRedKer Formalism.L2.SG.Pf.KppRedW Formalism.L2.SG.Pf.RedBasicsPf

variable {D : D7} (X : HidaSetting D)

theorem Wq_of_congW_zero {I : AutInst} {w : HeightOneSpectrum (𝓞 I.E)} {p : ℕ} (hp : p.Prime)
    (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p) {t : I.E ⊗[I.F] Af I.F} (h : CongW (w := w) p t 0) : t ∈ Wq I w := by
  obtain ⟨c, hc, ht⟩ := h
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hc
  obtain ⟨q, rfl⟩ := hc
  have : ((((p : ℤ) * q : ℤ)) : I.E ⊗[I.F] Af I.F) ∈ Wq I w := by
    push_cast
    exact Wq_mul' (natCast_Wq hp hcard) (intCast_mem _ q)
  have := add_mem ht this
  simpa using this

theorem psi_sum {ι : Type*} (s : Finset ι) (f : ι → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) :
    X.psiEf (divN X.B.I X.B.g (∑ i ∈ s, f i)) = ∏ i ∈ s, X.psiEf (divN X.B.I X.B.g (f i)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, Finset.prod_empty]
    unfold divN; rw [mul_zero]; exact X.psiEf_int 0 (zero_mem _)
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, divN_add, X.psiEf_add, ih]

theorem congW_iE {I : AutInst} {w : HeightOneSpectrum (𝓞 I.E)} {p : ℕ} {a : 𝓞 I.E} {m : ℤ}
    (h : a - (m : 𝓞 I.E) ∈ w.asIdeal) : CongW (w := w) p (iE I a) (m : ZMod p) := by
  refine ⟨m, rfl, ?_⟩
  have := iE_mem (I := I) h
  simpa [iE] using this

variable (ε : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), 𝓞 X.B.I.E)

theorem chi_split (hε1 : ∀ kv, ε kv - 1 ∈ (wK X kv).asIdeal)
    (hεP : ∀ kv (P : HeightOneSpectrum (𝓞 X.B.I.E)), ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ P.asIdeal → P ≠ wK X kv →
      ε kv ∈ P.asIdeal)
    (hε : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ε kv ∈ Ideal.span {((D.host.g (1 - kv.1) : ℕ) : 𝓞 X.B.I.E)})
    (hn : 0 < X.B.I.n) {C : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} (hC : C ∈ IntAf X.B.I.F X.B.I.E)
    (t1 t2 : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1))
    (h1 : ∀ kv, CongW (w := wK X kv) (D.host.g kv.1) C (t1 kv))
    (h2 : ∀ kv, CongW (w := wc X.B.I (wK X kv)) (D.host.g kv.1) C (t2 kv)) :
    X.psiEf (divN X.B.I X.B.g C) = ∏ kv, psiK X (ε kv) (hε kv) (t1 kv + t2 kv) := by
  classical
  set T : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F := ∑ kv, (iE X.B.I (ε kv) * (((t1 kv).val : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) +
    iE X.B.I (sigO X.B.I (ε kv)) * (((t2 kv).val : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) with hT
  have hTint : T ∈ IntAf X.B.I.F X.B.I.E :=
    sum_mem fun kv _ => add_mem (mul_mem (iE_int _ _) (natCast_mem _ _)) (mul_mem (iE_int _ _) (natCast_mem _ _))

  have hgP : ∀ kv, ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ (wK X kv).asIdeal := fun kv => level_mem_wB' X kv
  have hgPc : ∀ kv, ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ (wc X.B.I (wK X kv)).asIdeal :=
    fun kv => natCast_mem_wc X.B.I (level_mem_wB' X kv)
  have hΔ : ∀ P : HeightOneSpectrum (𝓞 X.B.I.E), ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ P.asIdeal → C - T ∈ Wq X.B.I P := by
    intro P hP
    obtain ⟨kv0, hP0 | hP0⟩ := over_g X P hP
    · subst hP0
      have hp := D.host.g_prime kv0.1
      have : NeZero (D.host.g kv0.1) := ⟨hp.ne_zero⟩
      have hTc : CongW (w := wK X kv0) (D.host.g kv0.1) T (t1 kv0) := by
        have h3 : CongW (w := wK X kv0) (D.host.g kv0.1) T
            (∑ kv, ((if kv = kv0 then 1 else 0) * (((t1 kv).val : ℕ) : ZMod (D.host.g kv0.1)) +
              0 * (((t2 kv).val : ℕ) : ZMod (D.host.g kv0.1)))) := by
          refine congW_sum _ fun kv _ => congW_add ?_ ?_
          · refine congW_mul (natCast_mem _ _) ?_ (congW_natCast _)
            by_cases hk : kv = kv0
            · subst hk
              rw [if_pos rfl]
              have := congW_iE (p := D.host.g kv.1) (m := 1) (by simpa using hε1 kv)
              simpa using this
            · rw [if_neg hk]
              have := congW_iE (p := D.host.g kv0.1) (m := 0)
                (by simpa using hεP kv (wK X kv0) (hgP kv0) (wK_ne X (Ne.symm hk)))
              simpa using this
          · refine congW_mul (natCast_mem _ _) ?_ (congW_natCast _)
            have hm : ε kv ∈ (wc X.B.I (wK X kv0)).asIdeal := hεP kv _ (hgPc kv0) (wK_ne_wc X kv kv0).symm
            rw [mem_wc] at hm
            have := congW_iE (p := D.host.g kv0.1) (m := 0) (by simpa using hm)
            simpa using this
        convert h3 using 1
        simp [Finset.sum_ite_eq']
      have := congW_sub (h1 kv0) hTc
      rw [sub_self] at this
      exact Wq_of_congW_zero hp (card_wK X kv0) this
    · subst hP0
      have hp := D.host.g_prime kv0.1
      have : NeZero (D.host.g kv0.1) := ⟨hp.ne_zero⟩
      have hTc : CongW (w := wc X.B.I (wK X kv0)) (D.host.g kv0.1) T (t2 kv0) := by
        have h3 : CongW (w := wc X.B.I (wK X kv0)) (D.host.g kv0.1) T
            (∑ kv, (0 * (((t1 kv).val : ℕ) : ZMod (D.host.g kv0.1)) +
              (if kv = kv0 then 1 else 0) * (((t2 kv).val : ℕ) : ZMod (D.host.g kv0.1)))) := by
          refine congW_sum _ fun kv _ => congW_add ?_ ?_
          · refine congW_mul (natCast_mem _ _) ?_ (congW_natCast _)
            have hm : ε kv ∈ (wc X.B.I (wK X kv0)).asIdeal := hεP kv _ (hgPc kv0) (wK_ne_wc X kv kv0).symm
            have := congW_iE (p := D.host.g kv0.1) (m := 0) (by simpa using hm)
            simpa using this
          · refine congW_mul (natCast_mem _ _) ?_ (congW_natCast _)
            by_cases hk : kv = kv0
            · subst hk
              rw [if_pos rfl]
              have hm : sigO X.B.I (ε kv) - 1 ∈ (wc X.B.I (wK X kv)).asIdeal := by
                rw [mem_wc, map_sub, sigO_sigO, map_one]; exact hε1 kv
              have := congW_iE (p := D.host.g kv.1) (m := 1) (by simpa using hm)
              simpa using this
            · rw [if_neg hk]
              have hm : sigO X.B.I (ε kv) ∈ (wc X.B.I (wK X kv0)).asIdeal := by
                rw [mem_wc, sigO_sigO]; exact hεP kv (wK X kv0) (hgP kv0) (wK_ne X (Ne.symm hk))
              have := congW_iE (p := D.host.g kv0.1) (m := 0) (by simpa using hm)
              simpa using this
        convert h3 using 1
        simp [Finset.sum_ite_eq']
      have := congW_sub (h2 kv0) hTc
      rw [sub_self] at this
      exact Wq_of_congW_zero hp (card_wKc X kv0) this

  obtain ⟨a, r', hr', hr⟩ := PIW.AdelClassFin.dual_dense X.B.I.F X.B.I.E X.B.g (g_pos X) (C - T) (sub_mem hC hTint)
  have ha : ∀ P : HeightOneSpectrum (𝓞 X.B.I.E), ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ P.asIdeal → a ∈ P.asIdeal := by
    intro P hP
    have hgW : (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ∈ Wq X.B.I P := by
      have := iE_mem (I := X.B.I) hP; simpa [iE] using this
    have hiE : iE X.B.I a ∈ Wq X.B.I P := by
      have := sub_mem (hΔ P hP) (Wq_mul' hgW hr')
      rw [hr] at this
      simpa [iE] using this
    obtain ⟨kv0, hP0 | hP0⟩ := over_g X P hP
    · subst hP0; exact int_of_Wq (D.host.g_prime kv0.1) (card_wK X kv0) hn hiE
    · subst hP0; exact int_of_Wq (D.host.g_prime kv0.1) (card_wKc X kv0) hn hiE
  obtain ⟨c, hc⟩ := mem_g_of_all X ha
  have hCT : C = T + (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (iE X.B.I c + r') := by
    have : C - T = (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (iE X.B.I c + r') := by
      rw [hr, hc]; simp [iE]; ring
    rw [← this]; ring
  rw [hCT, psi_modg X _ (add_mem (iE_int _ c) hr'), hT, psi_sum]
  refine Finset.prod_congr rfl fun kv _ => ?_
  rw [divN_add, X.psiEf_add, psi_sig, AddChar.map_add_eq_mul, psiK_apply, psiK_apply]

end Formalism.L2.SG.Pf.KppChar
end
end

