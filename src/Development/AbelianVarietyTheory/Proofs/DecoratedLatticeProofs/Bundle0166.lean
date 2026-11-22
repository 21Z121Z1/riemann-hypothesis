import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0159
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0002
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0007
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0162
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
import Formalism.LocalToGlobal.Columns.ChainTw

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSphericalVacuaToDoubledLatticeVacuum
section
noncomputable section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause resL resR)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.VacBox

variable {D : D7}

theorem gram_dbl_inv (A : HSp D) : (dblSp A).gram⁻¹ = blkMat finSumFinEquiv A.gram⁻¹ (-A.gram⁻¹) :=
  Matrix.inv_eq_left_inv (by
    rw [gram_hdbl, dblGram, blkMat_mul, neg_mul_neg, Matrix.nonsing_inv_mul _ (isHermND_gram A).2.isUnit, blkMat_one])

theorem hO_dbl (A B : HSp D) (x y : WO (dblSp A) B) :
    hO (dblSp A) B x y = hO A B (resL A B x) (resL A B y) - hO A B (resR A B x) (resR A B y) := by
  simp only [hO]
  rw [gram_dbl_inv]
  simp only [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type, resL, resR, Matrix.of_apply,
    blkMat, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.neg_apply, map_zero,
    map_neg, zero_mul, Finset.sum_const_zero, add_zero, zero_add, neg_mul, Finset.sum_neg_distrib, sub_eq_add_neg]

theorem hO_neg_neg (A B : HSp D) (x y : WO A B) : hO A B (-x) (-y) = hO A B x y := by
  simp only [hO, Matrix.neg_apply, map_neg, mul_neg, neg_mul, neg_neg]

theorem symplOH_dbl (A B : HSp D) (x y : WO (dblSp A) B) :
    symplOH (dblSp A) B x y = symplOH A B (resL A B x) (resL A B y) - symplOH A B (resR A B x) (resR A B y) := by
  simp only [symplOH, symplO, hO_dbl, mul_sub, map_sub]

theorem symplOH_neg_neg (A B : HSp D) (x y : WO A B) : symplOH A B (-x) (-y) = symplOH A B x y := by
  simp only [symplOH, symplO, hO_neg_neg]

theorem resL_add (A B : HSp D) (x y : WO (dblSp A) B) : resL A B (x + y) = resL A B x + resL A B y :=
  Matrix.ext fun _ _ => rfl

theorem resR_add (A B : HSp D) (x y : WO (dblSp A) B) : resR A B (x + y) = resR A B x + resR A B y :=
  Matrix.ext fun _ _ => rfl

def resLHom (A B : HSp D) : WO (dblSp A) B →+ WO A B where
  toFun := resL A B
  map_zero' := Matrix.ext fun _ _ => rfl
  map_add' := resL_add A B

def resRHom (A B : HSp D) : WO (dblSp A) B →+ WO A B where
  toFun := resR A B
  map_zero' := Matrix.ext fun _ _ => rfl
  map_add' := resR_add A B

theorem conj_psi_eq {ψ : AddChar (AF D.host.F) ℂ} (hψ : ∀ x, ‖ψ x‖ = 1) (z : AF D.host.F) :
    conj (ψ z) = ψ (-z) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_def, Complex.normSq_eq_norm_sq, hψ, one_pow, inv_one, Complex.ofReal_one,
    mul_one]

theorem heisO_delta {ψ : AddChar (AF D.host.F) ℂ} (hψ : ∀ x, ‖ψ x‖ = 1) (A B : HSp D) (w₀ : WO (dblSp A) B)
    (f₁ f₂ : WO A B → ℂ) :
    heisO ψ (dblSp A) B w₀ (delta A B f₁ f₂) =
      delta A B (heisO ψ A B (resL A B w₀) f₁) (heisO ψ A B (-resR A B w₀) f₂) := by
  funext x
  simp only [heisO, GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.delta, resL_add, resR_add, map_mul, conj_psi_eq hψ, symplOH_dbl, symplOH_neg_neg, neg_add]
  rw [sub_eq_add_neg, AddChar.map_add_eq_mul]
  ring

theorem sum_dbl_gram_inl (A : HSp D) (s : Fin (dblSp A).rank → D.host.E) (j : Fin A.rank) :
    ∑ k, star (s k) * (dblSp A).gram k (finSumFinEquiv (Sum.inl j)) =
      ∑ k, star ((fun k => s (finSumFinEquiv (Sum.inl k))) k) * A.gram k j := by
  rw [gram_hdbl]
  simp only [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type, dblGram, blkMat, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, mul_zero,
    Finset.sum_const_zero, add_zero]

theorem sum_dbl_gram_inr (A : HSp D) (s : Fin (dblSp A).rank → D.host.E) (j : Fin A.rank) :
    ∑ k, star (s k) * (dblSp A).gram k (finSumFinEquiv (Sum.inr j)) =
      ∑ k, star ((-fun k => s (finSumFinEquiv (Sum.inr k))) k) * A.gram k j := by
  rw [gram_hdbl]
  simp only [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type, dblGram, blkMat, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, mul_zero,
    Finset.sum_const_zero, zero_add, Matrix.neg_apply, Pi.neg_apply, star_neg, mul_neg, neg_mul]

theorem res_mem_latO {A B : HSp D} {LA : Lat A} {LB : Lat B} {P : FinPl D → Prop} {u : WO (dblSp A) B}
    (hu : u ∈ latO (dblSp A) B (sumLat finSumFinEquiv LA LA : Lat (dblSp A)) LB P) :
    resL A B u ∈ latO A B LA LB P ∧ resR A B u ∈ latO A B LA LB P := by
  have key : latO (dblSp A) B (sumLat finSumFinEquiv LA LA : Lat (dblSp A)) LB P ≤
      (latO A B LA LB P).comap (resLHom A B) ⊓ (latO A B LA LB P).comap (resRHom A B) := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro w ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
    refine ⟨AddSubgroup.subset_closure
      ⟨α, hα, hP, a, ha, fun k => s (finSumFinEquiv (Sum.inl k)), hs.1, t, ht, ?_⟩,
      AddSubgroup.subset_closure
      ⟨α, hα, hP, a, ha, -fun k => s (finSumFinEquiv (Sum.inr k)), neg_mem hs.2, t, ht, ?_⟩⟩
    · ext i j
      simp only [resLHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, resL, Matrix.of_apply]
      exact congrArg (fun z => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t i * z)) (sum_dbl_gram_inl A s j)
    · ext i j
      simp only [resRHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, resR, Matrix.of_apply]
      exact congrArg (fun z => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t i * z)) (sum_dbl_gram_inr A s j)
  exact key hu

theorem latO_mono_at {A B : HSp D} (LA : Lat A) (LB : Lat B) {Sf : Finset (FinPl D)} {v : FinPl D} (hv : v ∉ Sf) :
    latO A B LA LB (fun u => u = v) ≤ latO A B LA LB (fun u => u ∉ Sf) := by
  refine AddSubgroup.closure_mono ?_
  rintro w ⟨α, hα, hP, rest⟩
  refine ⟨α, hα, fun v' hv' => hP v' fun h => hv' (h ▸ hv), rest⟩

theorem pair_dbl (A : HSp D) (x y : Fin (dblSp A).rank → D.host.E) :
    ∑ i, ∑ j, star (x i) * (dblSp A).gram i j * y j =
      (∑ i, ∑ j, star (x (finSumFinEquiv (Sum.inl i))) * A.gram i j * y (finSumFinEquiv (Sum.inl j))) -
      ∑ i, ∑ j, star (x (finSumFinEquiv (Sum.inr i))) * A.gram i j * y (finSumFinEquiv (Sum.inr j)) := by
  rw [gram_hdbl]
  simp only [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type, dblGram, blkMat, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.neg_apply, mul_zero, zero_mul, Finset.sum_const_zero,
    add_zero, zero_add, mul_neg, neg_mul, Finset.sum_neg_distrib, sub_eq_add_neg]

theorem selfDual_sumLat {A : HSp D} {L : Lat A} (hL : IsSelfDualC A L) :
    IsSelfDualC (dblSp A) (sumLat finSumFinEquiv L L) := by
  haveI := hL.1
  refine ⟨isLattice_sumLat L L, fun y => ⟨fun hy x hx => ?_, fun H => ?_⟩⟩
  · obtain ⟨b₁, hb₁⟩ := (hL.2 (fun i => y (finSumFinEquiv (Sum.inl i)))).1 hy.1
      (fun i => x (finSumFinEquiv (Sum.inl i))) hx.1
    obtain ⟨b₂, hb₂⟩ := (hL.2 (fun i => y (finSumFinEquiv (Sum.inr i)))).1 hy.2
      (fun i => x (finSumFinEquiv (Sum.inr i))) hx.2
    refine ⟨b₁ - b₂, ?_⟩
    rw [pair_dbl]
    push_cast
    linear_combination hb₁ - hb₂
  · refine ⟨(hL.2 _).2 fun x hx => ?_, (hL.2 _).2 fun x hx => ?_⟩
    · obtain ⟨b, hb⟩ := H (pairVec finSumFinEquiv x 0) ((pairVec_mem_sumLat _).2 ⟨hx, zero_mem _⟩)
      rw [pair_dbl] at hb
      simp only [pairVec_inl, pairVec_inr, Pi.zero_apply, star_zero, zero_mul, Finset.sum_const_zero, sub_zero] at hb
      refine ⟨b, ?_⟩
      show (b : D.host.E) = ∑ i, ∑ j, star (x i) * A.gram i j * y (finSumFinEquiv (Sum.inl j))
      exact hb
    · obtain ⟨b, hb⟩ := H (pairVec finSumFinEquiv 0 x) ((pairVec_mem_sumLat _).2 ⟨zero_mem _, hx⟩)
      rw [pair_dbl] at hb
      simp only [pairVec_inl, pairVec_inr, Pi.zero_apply, star_zero, zero_mul, Finset.sum_const_zero, zero_sub] at hb
      refine ⟨-b, ?_⟩
      show ((-b : 𝓞 D.host.E) : D.host.E) = ∑ i, ∑ j, star (x i) * A.gram i j * y (finSumFinEquiv (Sum.inr j))
      push_cast
      linear_combination -hb

theorem doubling_isLatVac : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (LA : Lat A) (LB : Lat B), IsStdChar D ψ (-1) → IsSelfDualC A LA → IsSelfDualC (dblSp A) (sumLat finSumFinEquiv LA LA) ∧ ∀ (Sf : Finset (FinPl D)) (Φ₁ Φ₂ : WO A B → ℂ), IsSphOff ψ A B LA LB Sf Φ₁ → IsSphOff ψ A B LA LB Sf Φ₂ → ∀ v ∉ Sf, IsLatVac (heisO ψ (dblSp A) B) (latO (dblSp A) B (sumLat finSumFinEquiv LA LA : Lat (dblSp A)) LB fun u => u = v) (delta A B Φ₁ Φ₂) := by
  intro D ψ A B LA LB hψ hLA
  have hn : ∀ x, ‖ψ x‖ = 1 := hψ.1.2.1
  refine ⟨selfDual_sumLat hLA, ?_⟩
  intro Sf Φ₁ Φ₂ h₁ h₂ v hv
  have mono := latO_mono_at LA LB hv
  refine ⟨fun u hu => ?_, fun e he u hu hh => ?_⟩
  · obtain ⟨hL, hR⟩ := res_mem_latO hu
    have eL : resL A B (2 • u) = 2 • resL A B u := by rw [two_nsmul, two_nsmul, resL_add]
    have eR : -resR A B (2 • u) = 2 • (-resR A B u) := by
      rw [two_nsmul, two_nsmul, resR_add, neg_add]
    rw [heisO_delta hn, eL, eR, h₁.1 _ (mono hL), h₂.1 _ (neg_mem (mono hR))]
  · obtain ⟨hL, hR⟩ := res_mem_latO hu
    have hhL : IsHalf e (resL A B u) := fun i j => hh i (finSumFinEquiv (Sum.inl j))
    have hhR : IsHalf e (-resR A B u) := fun i j => by
      show e * -(u i (finSumFinEquiv (Sum.inr j))) = -(u i (finSumFinEquiv (Sum.inr j)))
      rw [mul_neg, hh]
    rw [heisO_delta hn, h₁.2 e he _ (mono hL) hhL, h₂.2 e he _ (neg_mem (mono hR)) hhR]

end GlobalTheory.Core.Rk.VacBox
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqOfPsiE
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1600000

namespace GlobalTheory.FirstVec

theorem first_col {K : Type} [CommRing K] {σ : ℕ} (T S : Matrix (Fin (σ + 1)) (Fin (σ + 1)) K) (h : S * T = 1)
    (hl : T (Fin.last σ) (Fin.last σ) = 1) (hu : ∀ j j' : Fin (σ + 1), j'.1 = j.1 + 1 → ∀ a b, b ≤ a → T a j * S j' b = 0)
    (hs : ∀ j j' : Fin (σ + 1), j'.1 = j.1 + 1 → (∑ a : Fin (σ + 1), ∑ b : Fin (σ + 1),
      if b.1 = a.1 + 1 then T a j * S j' b else 0) = 1) : ∀ a, T a 0 = if a = 0 then 1 else 0 := by
  have key : ∀ j j' : Fin (σ + 1), j'.1 = j.1 + 1 → (∀ b, j' < b → T b j' = 0) → ∀ a, j ≤ a →
      T a j = if a = j then T j j * S j' j' * T j' j' else 0 := fun j j' e H a ha => by
    have e1 : T a j = ∑ b, T a j * S j' b * T b j' := by
      have := congrFun (congrFun h j') j'
      rw [Matrix.mul_apply, Matrix.one_apply_eq] at this
      simp only [mul_assoc, ← Finset.mul_sum, this, mul_one]
    rw [e1, Finset.sum_eq_single j']
    · split_ifs with h1
      · rw [h1]
      · rw [hu j j' e a j' (by rw [Fin.le_def] at *; have := mt Fin.ext h1; omega), zero_mul]
    · intro b _ hb
      rcases lt_or_gt_of_ne hb with h1 | h1
      · rw [hu j j' e a b (by rw [Fin.le_def, Fin.lt_def] at *; omega), zero_mul]
      · rw [H b h1, mul_zero]
    · exact fun h => absurd (Finset.mem_univ _) h
  have tri : ∀ j : Fin (σ + 1), ∀ b, j < b → T b j = 0 := fun j => by
    induction j using Fin.reverseInduction with
    | last => exact fun b hb => absurd (Fin.le_last b) (not_le.2 hb)
    | cast j ih => exact fun b hb => by rw [key j.castSucc j.succ rfl ih b hb.le, if_neg hb.ne']
  have triS : S.BlockTriangular id := by
    letI := invertibleOfLeftInverse T S h
    rw [← Matrix.inv_eq_left_inv h]
    exact Matrix.blockTriangular_inv_of_blockTriangular fun a b hab => tri b a hab
  have diag : ∀ j : Fin (σ + 1), T j j = 1 := fun j => by
    induction j using Fin.reverseInduction with
    | last => exact hl
    | cast j ih =>
      have h1 := hs j.castSucc j.succ rfl
      rw [Finset.sum_eq_single j.castSucc, Finset.sum_eq_single j.succ, if_pos (show j.succ.1 = j.castSucc.1 + 1 from rfl)] at h1
      · rw [key j.castSucc j.succ rfl (tri _) _ le_rfl, if_pos rfl, h1, ih, one_mul]
      · exact fun b _ hb => if_neg fun e => hb (Fin.ext e)
      · exact fun h => absurd (Finset.mem_univ _) h
      · intro a _ ha
        refine Finset.sum_eq_zero fun b _ => ?_
        split_ifs with e
        · rcases lt_or_gt_of_ne ha with h2 | h2
          · rw [show S j.succ b = 0 from triS (show b < j.succ by
              rw [Fin.lt_def] at h2 ⊢; simp only [Fin.val_castSucc, Fin.val_succ] at h2 e ⊢; omega), mul_zero]
          · rw [tri _ a h2, zero_mul]
        · rfl
      · exact fun h => absurd (Finset.mem_univ _) h
  intro a
  split_ifs with e
  · rw [e, diag]
  · exact tri 0 a (Fin.pos_iff_ne_zero.2 e)

variable {D : D7} {S S₀ S₀' : HSp D}

theorem eq_of_psiE {ψ : AddChar (AF D.host.F) ℂ} (hψ : ∃ s : AE D, psiE ψ s ≠ 1) {s s' : D.host.E}
    (h : ∀ t : AE D, psiE ψ (t * incA D s) = psiE ψ (t * incA D s')) : s = s' := by
  by_contra hne
  obtain ⟨y, hy⟩ := hψ
  have h0 : s - s' ≠ 0 := sub_ne_zero.2 hne
  have h1 := h (y * incA D (s - s')⁻¹)
  have e : y * incA D (s - s')⁻¹ * incA D s = y + y * incA D (s - s')⁻¹ * incA D s' := by
    have : incA D (s - s')⁻¹ * (incA D s - incA D s') = 1 := by rw [← map_sub, ← map_mul, inv_mul_cancel₀ h0, map_one]
    linear_combination y * this
  rw [e, psiE_add] at h1
  have h2 : psiE ψ (y * incA D (s - s')⁻¹ * incA D s') * psiE ψ (-(y * incA D (s - s')⁻¹ * incA D s')) = 1 := by
    rw [← psiE_add, add_neg_cancel, psiE_zero]
  exact hy (mul_right_cancel₀ (left_ne_zero_of_mul_eq_one h2) (h1.trans (one_mul _).symm))

section

variable {ρ : ℕ} (d : HypDec S S₀ ρ) (d' : HypDec S S₀' ρ) {z : Fin S₀.rank → D.host.E} {z' : Fin S₀'.rank → D.host.E}

theorem exists_b (hz' : z' ≠ 0) (i : Fin ρ) (t : AE D) : ∃ b : Mx D ρ S₀'.rank, b *ᵥ ratV z' = Pi.single i t := by
  obtain ⟨k, hk⟩ := Function.ne_iff.1 hz'
  refine ⟨Matrix.single i k (t * incA D (z' k)⁻¹), ?_⟩
  rw [Matrix.single_mulVec]
  change Function.update (0 : Fin ρ → AE D) i (t * incA D (z' k)⁻¹ * incA D (z' k)) = _
  rw [mul_assoc, ← map_mul, inv_mul_cancel₀ hk, map_one, mul_one]
  rfl

theorem coefX_eq (hz : d.i₀ *ᵥ z = d'.i₀ *ᵥ z') (n : GA D S) :
    coefX d z n = d.pX *ᵥ (mt S n *ᵥ (d'.j0 *ᵥ ratV z')) := by
  have e : d.j0 *ᵥ ratV z = d'.j0 *ᵥ ratV z' := (ratV_mulVec _ _).symm.trans ((congrArg ratV hz).trans (ratV_mulVec _ _))
  rw [coefX, ← mulVec_mulVec, ← mulVec_mulVec, e]

theorem coefX_nB' (hz : d.i₀ *ᵥ z = d'.i₀ *ᵥ z') (b : Mx D ρ S₀'.rank) :
    coefX d z (d'.nB b) = (d.pX ⬝ d'.jX) *ᵥ (b *ᵥ ratV z') := by
  have e0 : d.pX *ᵥ (d'.j0 *ᵥ ratV z') = 0 := by
    have := coefX_eq d d' hz 1
    rw [GlobalTheory.MixModel.mt_one, one_mulVec, coefX, GlobalTheory.MixModel.mt_one, Matrix.one_mul, d.pX_j0, zero_mulVec] at this
    exact this.symm
  rw [coefX_eq d d' hz, mulVec_mulVec _ (mt S _), d'.nB_j0, add_mulVec, mulVec_add, e0, zero_add]
  simp only [mulVec_mulVec, Matrix.mul_assoc]

theorem e_eq (hz : d.i₀ *ᵥ z = d'.i₀ *ᵥ z') (hz' : z' ≠ 0) (hN : ∀ n ∈ flagN d', n ∈ flagN d) : d'.e = d.e * (d.qX * d'.e) := by
  apply rat_injective
  rw [rat_mul, rat_mul]
  change d'.jX = d.jX ⬝ (d.pX ⬝ d'.jX)
  ext k i : 2
  obtain ⟨b, hb⟩ := exists_b hz' i 1
  have e : d.j0 *ᵥ ratV z = d'.j0 *ᵥ ratV z' := (ratV_mulVec _ _).symm.trans ((congrArg ratV hz).trans (ratV_mulVec _ _))
  obtain ⟨u, -, b₁, c, hn⟩ := Decomp.flag_decomp d (hN _ (d'.nB_mem_NFlag b))
  have h1 : mt S (d'.nB b) *ᵥ (d.j0 *ᵥ ratV z) = d.j0 *ᵥ ratV z + d.jX *ᵥ ((u.1 ⬝ b₁) *ᵥ ratV z) := by
    rw [hn, mulVec_mulVec, Decomp.flag_unipotent_product_anisotropic_action, add_mulVec, mulVec_mulVec]
  have h2 : mt S (d'.nB b) *ᵥ (d.j0 *ᵥ ratV z) = d.j0 *ᵥ ratV z + d'.jX *ᵥ Pi.single i 1 := by
    rw [e, mulVec_mulVec, d'.nB_j0, add_mulVec, ← mulVec_mulVec, hb]
  have h3 := add_left_cancel (h2.symm.trans h1)
  have h4 : (d.jX ⬝ (d.pX ⬝ d'.jX)) *ᵥ Pi.single i 1 = d'.jX *ᵥ Pi.single i 1 := by
    rw [← mulVec_mulVec, ← mulVec_mulVec, h3, mulVec_mulVec _ d.pX, d.pX_jX, one_mulVec]
  have := congrFun h4 k
  simp only [mulVec_single_one] at this
  exact this.symm

end

theorem first_eq {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {ρ : ℕ} (d : HypDec S S₀ ρ) (d' : HypDec S S₀' ρ)
    {z : Fin S₀.rank → D.host.E} {z' : Fin S₀'.rank → D.host.E} (hz : d.i₀ *ᵥ z = d'.i₀ *ᵥ z') (hz0 : z ≠ 0) (hz' : z' ≠ 0)
    (hN : ∀ n, n ∈ flagN d ↔ n ∈ flagN d') (hc : ∀ n ∈ flagN d, psiBes ψ d 1 z n = psiBes ψ d' 1 z' n)
    (r : Fin ρ) (hr : r.1 = 0) (k : Fin S.rank) : d'.e k r = d.e k r := by
  obtain _ | σ := ρ
  · exact r.elim0
  obtain rfl : r = 0 := Fin.ext hr
  have hne := GlobalTheory.Unf.CutChar.exists_psiE_ne_one D ψ hψ
  have e1 := e_eq d d' hz hz' fun n => (hN n).2
  have e2 := e_eq d' d hz.symm hz0 fun n => (hN n).1
  have q1 : d'.qX * d'.e = 1 := d'.e'e
  have hT : (rat (d.qX * d'.e) : Mx D _ _) = d.pX ⬝ d'.jX := rat_mul _ _
  generalize d.qX * d'.e = T at e1 hT
  generalize hS : d'.qX * d.e = S' at e2
  have hST : S' * T = 1 := by rw [← hS, Matrix.mul_assoc, ← e1, q1]
  have hX : d.jX = d'.jX ⬝ rat S' := (congrArg rat e2).trans (rat_mul _ _)
  have hTS : (rat T : Mx D _ _) ⬝ rat S' = 1 := by rw [← rat_mul, mul_eq_one_comm.1 hST, rat_one]
  have hell : ∀ y : Fin (σ + 1) → AE D, ell D (σ + 1) ⬝ᵥ y = y (Fin.last σ) := fun y => by
    rw [dotProduct, Finset.sum_eq_single (Fin.last σ)]
    · simp [ell]
    · intro b _ hb
      rw [ell, if_neg fun e => hb (Fin.ext (by simpa using e)), zero_mul]
    · exact fun h => absurd (Finset.mem_univ _) h
  have hA : ∀ (j j' : Fin (σ + 1)) (t : AE D), j'.1 = j.1 + 1 → ∃ u ∈ UX D (σ + 1), u.1 = 1 + Matrix.single j j' t ∧
      blockX d (d'.levi u) = 1 + Matrix.of fun a b => t * incA D (T a j * S' j' b) := fun j j' t e => by
    obtain ⟨u, hu, hu1⟩ := Decomp.exists_unit (D := D) (T := Matrix.single j j' t) fun a b hab =>
      Matrix.single_apply_of_ne _ _ _ _ _ (by rintro ⟨rfl, rfl⟩; rw [Fin.le_def] at hab; omega)
    refine ⟨u, hu, hu1, ?_⟩
    rw [blockX, hX, ← Matrix.mul_assoc (mt S _), d'.levi_jX, hu1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← hT,
      Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hTS]
    congr 1
    ext a b : 2
    rw [Matrix.mul_apply, Finset.sum_eq_single j', Matrix.mul_single_apply_same, Matrix.of_apply, map_mul]
    · change incA D (T a j) * t * incA D (S' j' b) = _
      ring
    · intro c _ hc
      rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hc, zero_mul]
    · exact fun h => absurd (Finset.mem_univ _) h
  have H := first_col T S' hST ?_ ?_ ?_
  · rw [e1, Matrix.mul_apply]
    simp only [H, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · refine eq_of_psiE hne fun t => ?_
    obtain ⟨b, hb⟩ := exists_b hz' (Fin.last σ) t
    have h1 := hc _ ((hN _).2 (d'.nB_mem_NFlag b))
    have h2 : blockX d (d'.nB b) = 1 := by
      rw [blockX, hX, ← Matrix.mul_assoc (mt S _), d'.nB_jX, ← hX, d.pX_jX]
    rw [psiBes_nB, psiBes, simpleSum, h2, upSum_one, zero_add, coefX_nB' d d' hz, hb, hell, hell, ← hT, mulVec_single] at h1
    simp only [map_one, one_mul, Pi.single_eq_same, mul_one] at h1 ⊢
    rw [mul_comm t]
    exact h1
  · intro j j' e a b hab
    obtain ⟨u, hu, -, h2⟩ := hA j j' 1 e
    obtain ⟨u₁, hu₁, b₁, c, hn⟩ := Decomp.flag_decomp d ((hN _).2 (d'.levi_mem_NFlag hu))
    rw [blockX, hn, Decomp.mt_flag_jX, ← Matrix.mul_assoc, d.pX_jX, Matrix.one_mul] at h2
    have h3 := congrFun (congrFun h2 a) b
    rw [Matrix.add_apply, Matrix.of_apply, one_mul] at h3
    have h4 : u₁.1 a b = (1 : Mx D (σ + 1) (σ + 1)) a b := by
      rcases eq_or_lt_of_le hab with rfl | h
      · rw [(hu₁ b b).2, Matrix.one_apply_eq]
      · rw [(hu₁ a b).1 h, Matrix.one_apply_ne h.ne']
    rw [h4, left_eq_add] at h3
    exact incA_injective (h3.trans (map_zero _).symm)
  · intro j j' e
    refine eq_of_psiE hne fun t => ?_
    obtain ⟨u, hu, h1, h2⟩ := hA j j' t e
    have h3 := hc _ ((hN _).2 (d'.levi_mem_NFlag hu))
    have h4 : coefX d z (d'.levi u) = 0 := by
      have := coefX_nB' d d' hz 0
      rw [zero_mulVec, mulVec_zero, coefX_eq d d' hz, d'.nB_zero, GlobalTheory.MixModel.mt_one, one_mulVec] at this
      rw [coefX_eq d d' hz, mulVec_mulVec _ (mt S _), d'.wittDecomp_levi_inclAnisotropic, this]
    have hadd : ∀ M : Mx D (σ + 1) (σ + 1), upSum (1 + M) = upSum M := fun M =>
      Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by
        split_ifs with h
        · rw [Matrix.add_apply, Matrix.one_apply_ne (by rintro rfl; omega), zero_add]
        · rfl
    have h5 : upSum (Matrix.single j j' t : Mx D (σ + 1) (σ + 1)) = t := by
      rw [upSum, Finset.sum_eq_single j, Finset.sum_eq_single j', if_pos e, Matrix.single_apply_same]
      · exact fun b _ hb => if_neg fun e' => hb (Fin.ext (e'.trans e.symm))
      · exact fun h => absurd (Finset.mem_univ _) h
      · exact fun a _ ha => Finset.sum_eq_zero fun b _ => by
          rw [Matrix.single_apply_of_row_ne ha.symm, ite_self]
      · exact fun h => absurd (Finset.mem_univ _) h
    rw [psiBes_levi, psiUni, h1, hadd, h5, psiBes, simpleSum, h2, h4, hadd, dotProduct_zero, add_zero, map_one, one_mul] at h3
    rw [map_one, mul_one, ← h3]
    congr 1
    simp only [upSum, map_sum, Finset.mul_sum, Matrix.of_apply]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by split_ifs <;> simp

end GlobalTheory.FirstVec

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCommonLevelCompactTranslatesThetaFunction
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.Level

theorem mt_mul' {D : D7} (V : HSp D) (g h : GA D V) :
    Formalism.L2.Theta.mt V (g * h) = Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V h := by
  unfold Formalism.L2.Theta.mt; rw [map_mul]; rfl

theorem mt_one' {D : D7} (V : HSp D) : Formalism.L2.Theta.mt V 1 = 1 := by
  unfold Formalism.L2.Theta.mt; rw [map_one]; rfl

theorem continuous_mt' {D : D7} (V : HSp D) : Continuous (Formalism.L2.Theta.mt V) :=
  Units.continuous_val.comp continuous_subtype_val

theorem actO_mul_mt {D : D7} (S T : HSp D) (k : GA D S) (u : WO S T) :
    actO S T k 1 (HMul.hMul (u : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (Formalism.L2.Theta.mt S k)) = u := by
  unfold actO
  rw [mt_one', Matrix.one_mul, Matrix.mul_assoc, ← mt_mul', mul_inv_cancel, mt_one', Matrix.mul_one]

theorem exists_common_level : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : WRep S T), IsWeilDatumO ψ S T χS χT om → ∀ K : Set (GA D S), IsCompact K → ∀ f, IsThetaFunO ψ S T f → ∃ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) ∧ ∀ k ∈ K, ∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ S T u (om (k, 1) f) = om (k, 1) f := by
  intro D ψ S T χS χT om hW K hK f hf
  obtain ⟨U₀, hU₀, hUf⟩ := hf.level
  let U : AddSubgroup (WO S T) :=
    { carrier := {u | ∀ k ∈ K,
        (HMul.hMul (u : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (Formalism.L2.Theta.mt S k) : WO S T) ∈ U₀}
      add_mem' := fun {a b} ha hb k hk => by
        have := U₀.add_mem (ha k hk) (hb k hk)
        rwa [← Matrix.add_mul] at this
      zero_mem' := fun k _ => by
        rw [Matrix.zero_mul]; exact U₀.zero_mem
      neg_mem' := fun {a} ha k hk => by
        have := U₀.neg_mem (ha k hk)
        rwa [← Matrix.neg_mul] at this }
  refine ⟨U, U.isOpen_of_mem_nhds (g := 0) ?_, fun k hk u hu h0 => ?_⟩
  · refine hK.eventually_forall_of_forall_eventually (x₀ := (0 : WO S T)) (P := fun u k =>
      (HMul.hMul (u : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (Formalism.L2.Theta.mt S k) : WO S T) ∈ U₀) fun k _ => ?_
    have hc : Continuous fun p : WO S T × GA D S =>
        (HMul.hMul (p.1 : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (Formalism.L2.Theta.mt S p.2) : WO S T) :=
      continuous_fst.matrix_mul ((continuous_mt' S).comp continuous_snd)
    refine (hU₀.preimage hc).mem_nhds ?_
    show (HMul.hMul (0 : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (Formalism.L2.Theta.mt S k) : WO S T) ∈ U₀
    rw [Matrix.zero_mul]; exact U₀.zero_mem
  · have h1 := hUf _ (hu k hk) (by rw [Matrix.map_mul, h0]; simp)
    have h2 := hW.om_heis k 1 (HMul.hMul (u : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (Formalism.L2.Theta.mt S k)) f hf
    rw [h1, actO_mul_mt] at h2
    exact h2.symm

end GlobalTheory.Core.Rk.Level
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilDatumHermitianSpaceDoubled
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk

theorem exists_doubled_weilDatum : GlobalTheory.Published.WeilRepresentationUnitaryPair → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (om : WRep A B), IsWeilDatumO ψ A B χA χB om → ∃ omh : WRep (dblSp A) B, IsWeilDatumO ψ (dblSp A) B 1 χB omh := by
  intro H D ψ A B χA χB om h
  have h0 : ResEta D 1 0 := by
    have h1 := resEta_parity (m := 0) (resEta_mul h.resS (resEta_inv h.resS)) (by omega)
    rwa [show χA * χA⁻¹ = 1 from mul_inv_cancel χA] at h1
  have h2 : IsHeckeChar D 1 := ⟨continuous_const, fun _ => rfl⟩
  exact H D ψ (dblSp A) B 1 χB h.1 h2 h.3 (resEta_parity h0 (by change 0 % 2 = (A.rank + A.rank) % 2; omega)) h.resT

end GlobalTheory.Core.Rk
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatFamilyZetaConvergenceHolomorphyStatement
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatFamilyZeta_convergence_holomorphy : GlobalTheory.IndefiniteRowSideFullHecke.FlatZetaIntegral.FlatZetaHolomorphic := by
  first | exact @GlobalTheory.FlatFamily.flatZetaHolomorphic | exact GlobalTheory.FlatFamily.flatZetaHolomorphic | (intros; apply GlobalTheory.FlatFamily.flatZetaHolomorphic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalVolumeAgreesRowSubgroupUnitaryStatement
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_volume_agrees_row_subgroup_unitary : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → VolAgree (R := R) sel mu cst σ₀ P ι s W ν := by
  first | exact @GlobalTheory.VolBridge.vol_agree | exact GlobalTheory.VolBridge.vol_agree | (intros; apply GlobalTheory.VolBridge.vol_agree <;> assumption)
end

