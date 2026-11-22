import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.Bundle0004
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.AlgebraMapIntMemIntAd
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.Bundle0003

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.EqOneOfUniLevi
section
noncomputable section

namespace PI.IwaMeasEx.LP

open Matrix Formalism.L2.S.S7.WittLeviSubgroups PI.IwaMeasEx.PD

section Gen

variable {R : Type} [CommRing R] {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (e : ι ≃ Fin n) (lev : ι → ℕ)
  (Fm Fi : Matrix (Fin n) (Fin n) R)

def wc (X : Matrix (Fin n) (Fin n) R) : Matrix ι ι R := (Fi * X * Fm).submatrix e e

def uw (A : Matrix ι ι R) : Matrix (Fin n) (Fin n) R := Fm * A.submatrix e.symm e.symm * Fi

variable {Fm Fi}

theorem wc_mul (hFm : Fm * Fi = 1) (X Y : Matrix (Fin n) (Fin n) R) :
    wc e Fm Fi (X * Y) = wc e Fm Fi X * wc e Fm Fi Y := by
  unfold wc
  rw [submatrix_mul_equiv, show Fi * X * Fm * (Fi * Y * Fm) = Fi * X * (Fm * Fi) * Y * Fm by
    simp only [Matrix.mul_assoc], hFm, Matrix.mul_one]
  simp only [Matrix.mul_assoc]

theorem uw_mul (hFi : Fi * Fm = 1) (A B : Matrix ι ι R) :
    uw e Fm Fi (A * B) = uw e Fm Fi A * uw e Fm Fi B := by
  unfold uw
  rw [(submatrix_mul_equiv A B e.symm e.symm e.symm).symm,
    show Fm * A.submatrix e.symm e.symm * Fi * (Fm * B.submatrix e.symm e.symm * Fi) =
      Fm * A.submatrix e.symm e.symm * (Fi * Fm) * B.submatrix e.symm e.symm * Fi by simp only [Matrix.mul_assoc],
    hFi, Matrix.mul_one]
  simp only [Matrix.mul_assoc]

theorem wc_one (hFi : Fi * Fm = 1) : wc e Fm Fi (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  unfold wc
  rw [Matrix.mul_one, hFi, submatrix_one_equiv]

theorem uw_one (hFm : Fm * Fi = 1) : uw e Fm Fi (1 : Matrix ι ι R) = 1 := by
  unfold uw
  rw [submatrix_one_equiv, Matrix.mul_one, hFm]

theorem blo_of_par (hFi : Fi * Fm = 1) {g : GL (Fin n) R} (hg : g ∈ parGL (cols e Fm) lev) :
    BLo lev (wc e Fm Fi (g : Matrix (Fin n) (Fin n) R)) := by
  intro s r hl
  have h1 : g ∈ Formalism.UG.stabGL (stepLo (cols e Fm) lev (lev r + 1)) := Subgroup.mem_iInf.1 hg (lev r + 1)
  exact entry_zero hFi {t | lev t < lev r + 1} h1 s r (by simp only [Set.mem_ofPred_eq]; omega)
    (by simp only [Set.mem_ofPred_eq]; omega)

end Gen

section Form

variable {R : Type} [CommRing R] {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (e : ι ≃ Fin n) (lev : ι → ℕ)
  {Fm Fi : Matrix (Fin n) (Fin n) R}

def ALev (a : ℕ) (W : Matrix ι ι R) : Prop := ∀ q r, W q r ≠ 0 → lev q + lev r = 2 * a

theorem cT_apply (σ : R →+* R) {m p : Type} (M : Matrix m p R) (i : p) (j : m) :
    Formalism.UG.cT σ M i j = σ (M j i) := rfl

theorem cT_submatrix (σ : R →+* R) {m p m' p' : Type} (M : Matrix m p R) (f : m' → m) (g : p' → p) :
    Formalism.UG.cT σ (M.submatrix f g) = (Formalism.UG.cT σ M).submatrix g f := by
  ext i j; rfl

theorem tripleS (σ : R →+* R) (A W : Matrix ι ι R) (p q : ι) :
    (Formalism.UG.cT σ A * W * A) p q = ∑ t, ∑ r, σ (A r p) * W r t * A t q := by
  simp only [Matrix.mul_apply, cT_apply, Finset.sum_mul]

theorem bd_unitaryS (σ : R →+* R) {a : ℕ} {W T : Matrix ι ι R} (hA : ALev lev a W) (hT : BLo lev T)
    (hU : Formalism.UG.cT σ T * W * T = W) : Formalism.UG.cT σ (bd lev T) * W * bd lev T = W := by
  ext p q
  rw [tripleS]
  by_cases hpq : lev p + lev q = 2 * a
  · conv_rhs => rw [← hU, tripleS]
    refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun r _ => ?_
    by_cases hW : W r t = 0
    · rw [hW, mul_zero, zero_mul, mul_zero, zero_mul]
    have hl := hA r t hW
    simp only [bd]
    by_cases h1 : lev r = lev p
    · rw [if_pos h1, if_pos (show lev t = lev q by omega)]
    · rw [if_neg h1, map_zero, zero_mul, zero_mul]
      rcases Nat.lt_or_ge (lev p) (lev r) with h2 | h2
      · rw [hT r p h2, map_zero, zero_mul, zero_mul]
      · rw [hT t q (by omega), mul_zero]
  · have hW : W p q = 0 := by
      by_contra h; exact hpq (hA p q h)
    rw [hW]
    refine Finset.sum_eq_zero fun t _ => Finset.sum_eq_zero fun r _ => ?_
    simp only [bd]
    by_cases h1 : lev r = lev p
    · by_cases h2 : lev t = lev q
      · have hW' : W r t = 0 := by
          by_contra h; have := hA r t h; omega
        rw [hW', mul_zero, zero_mul]
      · rw [if_neg h2, mul_zero]
    · rw [if_neg h1, map_zero, zero_mul, zero_mul]

theorem wc_unitary (σ : R →+* R) (Jx : Matrix (Fin n) (Fin n) R) (hFm : Fm * Fi = 1) {W : Matrix ι ι R}
    (hW : (Formalism.UG.cT σ Fm * Jx * Fm).submatrix e e = W) (X : Matrix (Fin n) (Fin n) R)
    (hX : Formalism.UG.cT σ X * Jx * X = Jx) : Formalism.UG.cT σ (wc e Fm Fi X) * W * wc e Fm Fi X = W := by
  subst hW
  unfold wc
  rw [cT_submatrix, submatrix_mul_equiv, submatrix_mul_equiv]
  congr 1
  have e1 : Formalism.UG.cT σ Fi * Formalism.UG.cT σ Fm = 1 := by rw [← Formalism.UG.cT_mul, hFm, Formalism.UG.cT_one]
  calc Formalism.UG.cT σ (Fi * X * Fm) * (Formalism.UG.cT σ Fm * Jx * Fm) * (Fi * X * Fm)
      = Formalism.UG.cT σ Fm * Formalism.UG.cT σ X * (Formalism.UG.cT σ Fi * Formalism.UG.cT σ Fm) * Jx * (Fm * Fi) * X * Fm := by
        simp only [Formalism.UG.cT_mul, Matrix.mul_assoc]
    _ = Formalism.UG.cT σ Fm * (Formalism.UG.cT σ X * Jx * X) * Fm := by
        rw [e1, hFm]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = _ := by rw [hX]

theorem uw_unitary (σ : R →+* R) (Jx : Matrix (Fin n) (Fin n) R) (hFm : Fm * Fi = 1) {W : Matrix ι ι R}
    (hW : (Formalism.UG.cT σ Fm * Jx * Fm).submatrix e e = W) (A : Matrix ι ι R) (hA : Formalism.UG.cT σ A * W * A = W) :
    Formalism.UG.cT σ (uw e Fm Fi A) * Jx * uw e Fm Fi A = Jx := by
  have e1 : Formalism.UG.cT σ Fi * Formalism.UG.cT σ Fm = 1 := by rw [← Formalism.UG.cT_mul, hFm, Formalism.UG.cT_one]
  have hG : Formalism.UG.cT σ Fm * Jx * Fm = W.submatrix e.symm e.symm := by
    rw [← hW, submatrix_submatrix, Equiv.self_comp_symm, submatrix_id_id]
  have hA' : Formalism.UG.cT σ (A.submatrix e.symm e.symm) * W.submatrix e.symm e.symm * A.submatrix e.symm e.symm =
      W.submatrix e.symm e.symm := by
    rw [cT_submatrix, submatrix_mul_equiv, submatrix_mul_equiv, hA]
  unfold uw
  calc Formalism.UG.cT σ (Fm * A.submatrix e.symm e.symm * Fi) * Jx * (Fm * A.submatrix e.symm e.symm * Fi)
      = Formalism.UG.cT σ Fi * (Formalism.UG.cT σ (A.submatrix e.symm e.symm) * (Formalism.UG.cT σ Fm * Jx * Fm) *
          A.submatrix e.symm e.symm) * Fi := by simp only [Formalism.UG.cT_mul, Matrix.mul_assoc]
    _ = Formalism.UG.cT σ Fi * Formalism.UG.cT σ Fm * Jx * (Fm * Fi) := by
        rw [hG, hA', ← hG]; simp only [Matrix.mul_assoc]
    _ = Jx := by rw [e1, hFm, Matrix.one_mul, Matrix.mul_one]

theorem wc_mul_inv (hFm : Fm * Fi = 1) (hFi : Fi * Fm = 1) (g : GL (Fin n) R) :
    wc e Fm Fi (g : Matrix (Fin n) (Fin n) R) * wc e Fm Fi ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = 1 := by
  rw [← wc_mul e hFm, ← Units.val_mul, mul_inv_cancel, Units.val_one, wc_one e hFi]

theorem wc_inv_mul (hFm : Fm * Fi = 1) (hFi : Fi * Fm = 1) (g : GL (Fin n) R) :
    wc e Fm Fi ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) * wc e Fm Fi (g : Matrix (Fin n) (Fin n) R) = 1 := by
  rw [← wc_mul e hFm, ← Units.val_mul, inv_mul_cancel, Units.val_one, wc_one e hFi]

def levGL (hFm : Fm * Fi = 1) (hFi : Fi * Fm = 1) (g : GL (Fin n) R) (hg : g ∈ parGL (cols e Fm) lev) :
    GL (Fin n) R :=
  ⟨uw e Fm Fi (bd lev (wc e Fm Fi (g : Matrix (Fin n) (Fin n) R))),
    uw e Fm Fi (bd lev (wc e Fm Fi ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R))),
    by rw [← uw_mul e hFi, bd_mul lev (blo_of_par e lev hFi hg) (blo_of_par e lev hFi ((parGL _ lev).inv_mem hg))
      (wc_mul_inv e hFm hFi g), uw_one e hFm],
    by rw [← uw_mul e hFi, bd_mul lev (blo_of_par e lev hFi ((parGL _ lev).inv_mem hg)) (blo_of_par e lev hFi hg)
      (wc_inv_mul e hFm hFi g), uw_one e hFm]⟩

variable (hFm : Fm * Fi = 1) (hFi : Fi * Fm = 1) {g : GL (Fin n) R} (hg : g ∈ parGL (cols e Fm) lev)

theorem levGL_unitary (σ : R →+* R) (Jx : Matrix (Fin n) (Fin n) R) {a : ℕ} {W : Matrix ι ι R}
    (hW : (Formalism.UG.cT σ Fm * Jx * Fm).submatrix e e = W) (hA : ALev lev a W) (hgU : g ∈ Formalism.UG.UJ σ Jx) :
    levGL e lev hFm hFi g hg ∈ Formalism.UG.UJ σ Jx :=
  uw_unitary e σ Jx hFm hW _ (bd_unitaryS lev σ hA (blo_of_par e lev hFi hg) (wc_unitary e σ Jx hFm hW _ hgU))

end Form

end PI.IwaMeasEx.LP

end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.LeviSizesMeasurable
section
noncomputable section

namespace PI.IwaMeasEx.Nrm

open Matrix NumberField Topology Filter MeasureTheory Formalism.MainNotions.S Formalism.MainNotions.LeviCoordinates Formalism.L2.S.S7.DensDefs
  Formalism.L2.S.S7.WittLeviSubgroups Formalism.L2.S.S7.PositiveOrthantChangeOfVariables Formalism.L2.S.S7.GLOne
open scoped TensorProduct nonZeroDivisors

section Top

variable (I : AutInst)

attribute [local instance] AfT.tAf

theorem topRing : IsTopologicalRing (AEf I) := AfT.isTopologicalRing_tAf I

theorem t2 : T2Space (AEf I) := AfT.t2Space_finite_adeles_ext I

attribute [local instance] topRing t2

def mAf : MeasurableSpace (AEf I) := borel (AEf I)

attribute [local instance] mAf

theorem borel_mAf : BorelSpace (AEf I) := ⟨rfl⟩

attribute [local instance] borel_mAf

theorem isOpen_IntAf : IsOpen ((IntAf I.F I.E : Subring (AEf I)) : Set (AEf I)) := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [(AfT.hasBasis_nhds_tAf I x).mem_iff]
  refine ⟨0, trivial, fun y hy => ?_⟩
  change y - x ∈ AfT.bsub I (0 + 1) at hy
  obtain ⟨z, hz, he⟩ := (AfT.mem_bsub I).1 hy
  have e : y = x + (y - x) := by ring
  show y ∈ IntAf I.F I.E
  rw [e, ← he]
  exact add_mem hx (mul_mem (natCast_mem _ _) hz)

theorem continuous_inclR :
    Continuous (Algebra.TensorProduct.includeRight (R := I.F) (A := I.E) (B := Af I.F) : Af I.F → AEf I) := by
  apply continuous_of_continuousAt_zero
  rw [ContinuousAt, map_zero]
  refine (AfT.hasBasis_nhds_zero_tAf I).tendsto_right_iff.2 fun k _ => ?_
  have hk : ((k + 1 : ℕ) : I.F) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
  have hU : IsOpen {a : Af I.F | algebraMap I.F (Af I.F) (((k + 1 : ℕ) : I.F)⁻¹) * a ∈ Wau.Ohat I.F} :=
    Wau.isOpen_Ohat.preimage (continuous_const.mul continuous_id)
  have h0 : (0 : Af I.F) ∈ {a : Af I.F | algebraMap I.F (Af I.F) (((k + 1 : ℕ) : I.F)⁻¹) * a ∈ Wau.Ohat I.F} := by
    show _ * 0 ∈ Wau.Ohat I.F
    rw [mul_zero]
    exact Wau.ohat_zero
  filter_upwards [hU.mem_nhds h0] with a ha
  show Algebra.TensorProduct.includeRight a ∈ AfT.bsub I (k + 1)
  refine (AfT.mem_bsub I).2 ⟨Algebra.TensorProduct.includeRight
    (algebraMap I.F (Af I.F) (((k + 1 : ℕ) : I.F)⁻¹) * a), AfT.includeRight_mem_IntAf I ha, ?_⟩
  rw [← map_natCast (Algebra.TensorProduct.includeRight (R := I.F) (A := I.E) (B := Af I.F)), ← map_mul, ← mul_assoc,
    ← map_natCast (algebraMap I.F (Af I.F)), ← map_mul, mul_inv_cancel₀ hk, map_one, one_mul]

theorem continuous_embC {ι : Type} [Fintype ι] (b : Module.Basis ι I.F I.E) :
    Continuous (fun c : ι → Af I.F => (∑ j, b j ⊗ₜ[I.F] c j : AEf I)) := by
  refine continuous_finset_sum _ fun j _ => ?_
  have e : (fun c : ι → Af I.F => (b j ⊗ₜ[I.F] c j : AEf I)) =
      fun c => iE I (b j) * Algebra.TensorProduct.includeRight (c j) := by
    funext c
    show b j ⊗ₜ[I.F] c j = (b j ⊗ₜ[I.F] (1 : Af I.F)) * ((1 : I.E) ⊗ₜ[I.F] c j)
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [e]
  exact continuous_const.mul ((continuous_inclR I).comp (continuous_apply j))

theorem isCompact_IntAf : IsCompact ((IntAf I.F I.E : Subring (AEf I)) : Set (AEf I)) := by
  let b := Module.finBasis I.F I.E
  obtain ⟨D, hD, hDb⟩ := AfT.exists_denom I b
  have hK : IsCompact ((fun c => (∑ j, b j ⊗ₜ[I.F] c j : AEf I)) '' Set.univ.pi fun _ => Wau.Cpt.Bx I D) :=
    (isCompact_univ_pi fun _ => Wau.Cpt.isCompact_Bx I D).image (continuous_embC I b)
  have hcl : IsClosed ((IntAf I.F I.E : Subring (AEf I)) : Set (AEf I)) :=
    AddSubgroup.isClosed_of_isOpen (IntAf I.F I.E).toAddSubgroup (isOpen_IntAf I)
  refine hK.of_isClosed_subset hcl fun x hx => ?_
  refine ⟨fun j => AfT.crd I b j x, fun j _ => Wau.Cpt.mem_Bx I (by omega) ?_, (AfT.sum_crd I b x).symm⟩
  rw [nsmul_eq_mul]
  exact AfT.crd_mem I b hDb (AfT.IntAf_le_sumsInt I hx) j

def Bs (𝔞 : FractionalIdeal (𝓞 I.E)⁰ I.E) : Set (AEf I) :=
  {x | ∃ b ∈ (𝔞 : Submodule (𝓞 I.E) I.E), ∃ N : ℕ, 1 ≤ N ∧ (N : I.E) ∈ (𝔞 : Submodule (𝓞 I.E) I.E) ∧
    ∃ z ∈ IntAf I.F I.E, x = iE I b + iE I N * z}

def Sa (𝔞 : FractionalIdeal (𝓞 I.E)⁰ I.E) : Set (AEf I) :=
  Bs I 𝔞 ∩ ⋂ 𝔟 : {𝔟 : FractionalIdeal (𝓞 I.E)⁰ I.E // 𝔟 ≠ 0 ∧ 𝔟 < 𝔞}, (Bs I 𝔟.1)ᶜ

open Classical in

def hq (u : AEf I) : ℚ := if h : IsUnit u then (FractionalIdeal.absNorm (FI I h.unit))⁻¹ else 0

end Top

attribute [local instance] AfT.tAf topRing t2 mAf borel_mAf

end PI.IwaMeasEx.Nrm

end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.RelIndexUH
section
noncomputable section

namespace PI.IwaMeasEx.MFI

open NumberField
open scoped TensorProduct nonZeroDivisors Pointwise
open Formalism.MainNotions.S Formalism.L2.S.S7.GLOne PI.IwaMeasEx.Nrm

variable (I : AutInst)

def oH : AddSubgroup (AEf I) := (IntAf I.F I.E).toAddSubgroup

def uH (u : AEf I) : AddSubgroup (AEf I) := (oH I).map (AddMonoidHom.mulLeft u)

theorem mem_uH_iff (u : (AEf I)ˣ) (x : AEf I) :
    x ∈ uH I u ↔ ((u⁻¹ : (AEf I)ˣ) : AEf I) * x ∈ IntAf I.F I.E := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [AddMonoidHom.coe_mulLeft, ← mul_assoc, Units.inv_mul, one_mul]
    exact hy
  · intro hx
    refine ⟨_, hx, ?_⟩
    rw [AddMonoidHom.coe_mulLeft, ← mul_assoc, Units.mul_inv, one_mul]

def aI (u : (AEf I)ˣ) : Ideal (𝓞 I.E) := Submodule.comap (Algebra.linearMap (𝓞 I.E) I.E) (cid I u)

theorem map_aI (u : (AEf I)ˣ) (hu : (u : AEf I) ∈ IntAf I.F I.E) :
    Submodule.map (Algebra.linearMap (𝓞 I.E) I.E) (aI I u) = cid I u := by
  apply le_antisymm
  · exact Submodule.map_comap_le _ _
  · intro e he
    have h : iE I e ∈ IntAf I.F I.E := by
      have e1 : iE I e = (u : AEf I) * (((u⁻¹ : (AEf I)ˣ) : AEf I) * iE I e) := by
        rw [← mul_assoc, Units.mul_inv, one_mul]
      rw [e1]
      exact mul_mem hu he
    obtain ⟨o, rfl⟩ := mem_intOE _ h
    exact ⟨o, he, rfl⟩

theorem absNorm_FI (u : (AEf I)ˣ) (hu : (u : AEf I) ∈ IntAf I.F I.E) :
    FractionalIdeal.absNorm (FI I u) = (Ideal.absNorm (aI I u) : ℚ) := by
  rw [FractionalIdeal.absNorm_eq' 1 (aI I u) (by
    simp only [coe_FI, map_aI I u hu]
    exact one_smul _ _)]
  simp

theorem relIndex_uH (u : (AEf I)ˣ) (hu : (u : AEf I) ∈ IntAf I.F I.E) :
    ((uH I (u : AEf I)).relIndex (oH I) : ℝ) = (nrmF I u)⁻¹ := by
  set S := (uH I (u : AEf I)).addSubgroupOf (oH I) with hS
  let ι : 𝓞 I.E →+ oH I :=
    { toFun := fun o => ⟨iE I (algebraMap (𝓞 I.E) I.E o), inclE_mem (RingHom.mem_range_self _ o)⟩
      map_zero' := by ext; simp
      map_add' := fun a b => by ext; simp }
  let ψ : 𝓞 I.E →+ (oH I ⧸ S) := (QuotientAddGroup.mk' S).comp ι
  have hmem : ∀ o : 𝓞 I.E, ψ o = 0 ↔ o ∈ aI I u := by
    intro o
    show (QuotientAddGroup.mk' S) (ι o) = 0 ↔ _
    rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
    show iE I (algebraMap (𝓞 I.E) I.E o) ∈ uH I (u : AEf I) ↔ _
    rw [mem_uH_iff]
    rfl
  have hsurj : Function.Surjective ψ := by
    intro q
    obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientAddGroup.mk'_surjective S q
    obtain ⟨N, hN, hNc, -⟩ := mem_uO I u
    obtain ⟨a, ⟨o, rfl⟩, z, hz, hxe⟩ := IntAf_approx N hN x hx
    refine ⟨o, ?_⟩
    show (QuotientAddGroup.mk' S) (ι o) = (QuotientAddGroup.mk' S) ⟨x, hx⟩
    rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq]
    show -(iE I (algebraMap (𝓞 I.E) I.E o)) + x ∈ uH I (u : AEf I)
    rw [mem_uH_iff]
    have e1 : -(iE I (algebraMap (𝓞 I.E) I.E o)) + x = iE I (N : I.E) * z := by
      rw [hxe, map_natCast]
      change -(iE I (algebraMap (𝓞 I.E) I.E o)) + (iE I (algebraMap (𝓞 I.E) I.E o) + (N : AEf I) * z) = _
      ring
    rw [e1, ← mul_assoc]
    exact mul_mem hNc hz
  have hker : ψ.ker = (aI I u).toAddSubgroup := by
    ext o
    rw [AddMonoidHom.mem_ker, hmem]
    rfl
  have h1 : (uH I (u : AEf I)).relIndex (oH I) = Nat.card (oH I ⧸ S) := rfl
  have h2 : ψ.ker.index = Nat.card (oH I ⧸ S) := by
    rw [AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hsurj, AddSubgroup.card_top]
  have h3 : Ideal.absNorm (aI I u) = (aI I u).toAddSubgroup.index := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rfl
  rw [h1, ← h2, hker, ← h3, nrmF_eq, absNorm_FI I u hu, inv_inv]
  simp

end PI.IwaMeasEx.MFI

end
end

