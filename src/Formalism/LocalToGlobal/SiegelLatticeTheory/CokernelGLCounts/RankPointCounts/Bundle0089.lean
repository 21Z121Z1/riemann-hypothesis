import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdECut
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0015
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.EntInSandwich
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.GlobalConditionOfLocalAgreement
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalModelPeriodLattices
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ZsVolShape
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0086

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdEApproxAt
section
noncomputable section

open IsDedekindDomain NumberField ValuativeRel Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.StabShape

namespace Formalism.L2.SG.Pf.ProdEApprox

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section At

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))

def ellP (p : PlF D) : (D.s.atP p).Fp := ((Loc.resChar p : ℕ) : (D.s.atP p).Fp)

theorem ellP_ne (p : PlF D) : ellP p ≠ 0 := by
  have := (D.s.atP p).char0
  have hp := (D.s.atP p).ellPrime.out
  exact Nat.cast_ne_zero.2 hp.ne_zero

theorem ellP_mem (p : PlF D) : ellP p ∈ 𝒪[(D.s.atP p).Fp] := natCast_mem _ _

variable {M δ}

theorem latS_R {p : PlF D} (hA : Agree δ M p) {x : (D.s.atP p).Ep} (hx : x ∈ latS (D.s.atP p) (ellP p)) :
    x ∈ (M p).R := by
  obtain ⟨y, hy, rfl⟩ := mem_latS.1 hx
  obtain ⟨-, -, -, hO, -, hsp⟩ := hA
  show _ ∈ (⟨(M p).L, (M p).split, (M p).mu⟩ : Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep).R
  rcases hM : (M p).split with _ | g
  · show _ ∈ (M p).L.O
    rw [hO]
    exact (D.s.atP p).O.mul_mem (alg_mem_O (ellP_mem p)) hy
  · rcases hR : (D.s.atP p).split with _ | sg
    · simp [hM, hR] at hsp
    · have hsp' : g.e = sg.e ∧ g.q = sg.q := by simpa [hM, hR] using hsp
      rw [Formalism.MainNotions.LocalModelPeriodLattices.mem_R_split]
      have hy' := (Formalism.MainNotions.BridgeLemma.O_split (D.s.atP p) sg y).1 hy
      have hq : ((g.q : 𝒪[(D.s.atP p).Fp]) : (D.s.atP p).Fp) = ellP p := by rw [hsp'.2]; exact sg.q_eq
      have he : g.e (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (ellP p) * y) =
          (ellP p * (sg.e y).1, ellP p * (sg.e y).2) := by
        rw [map_mul, AlgEquiv.commutes, hsp'.1]; rfl
      rw [he]
      refine ⟨Subring.mul_mem _ (ellP_mem p) hy'.1, Subring.mul_mem _ (ellP_mem p) hy'.2,
        (sg.e y).1 - (sg.e y).2, Subring.sub_mem _ hy'.1 hy'.2, ?_⟩
      rw [hq]; ring

variable (M δ)

theorem ptMat_mono : ptMat w = mono (Formalism.L2.SG.Pf.fσ w) (fun a => Formalism.L2.SG.Pf.pv w.1 a) := by
  ext a b
  rw [Formalism.L2.SG.Pf.ptMat_fσ]
  rfl

theorem exists_unit_monomial_stable_of_Y0 {p : PlF D} (hA : Agree δ M p) :
    ∃ N Ni : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep, N * Ni = 1 ∧ Ni * N = 1 ∧
      (∃ ν : Fin (D.R.rS + 1) → (D.s.atP p).Ep, (∀ a, IsUnit (ν a)) ∧ N = mono (Formalism.L2.SG.Pf.fσ w) ν) ∧
      ∀ l ρ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep, IsLoUni l → IsUpUni ρ →
        l * ProdE.Y0 M δ u u' w p * ρ = ProdE.Y0 M δ u u' w p → l * N * ρ = N := by
  set σ := Formalism.L2.SG.Pf.fσ w
  have hσ : ∀ a, σ (σ a) = a := Formalism.L2.SG.Pf.fσ_fσ w
  obtain ⟨ν, hν, κ, hY⟩ := zzp_mono δ M u u' hA hσ (fun a => (-1) ^ (D.R.rS - (σ a).val) * Formalism.L2.SG.Pf.pv w.1 a)
    (fun a => mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) (Formalism.L2.SG.Pf.pv_ne' w a))
  have hY0 : ProdE.Y0 M δ u u' w p = mono σ ν - Matrix.single (Fin.last D.R.rS) (Fin.last D.R.rS) κ := by
    rw [← hY]
    unfold ProdE.Y0
    rw [ptMat_mono, zhatOM_mono]
  refine ⟨mono σ ν, mono σ (fun a => Ring.inverse (ν (σ a))), ?_, ?_, ⟨ν, hν, rfl⟩, ?_⟩
  · ext i j
    rw [mono_mul]
    simp only [mono, Matrix.of_apply, Matrix.one_apply, hσ]
    split_ifs with h1 h2 h2
    · exact Ring.mul_inverse_cancel _ (hν i)
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · simp
  · ext i j
    rw [mul_mono hσ]
    simp only [mono, Matrix.of_apply, hσ, Matrix.one_apply]
    by_cases h : σ j = σ i
    · have hij : i = j := by rw [← hσ i, ← h, hσ]
      subst hij
      simp only [if_true]
      exact Ring.inverse_mul_cancel _ (hν _)
    · have hij : i ≠ j := fun e => h (by rw [e])
      rw [if_neg h, if_neg hij, zero_mul]
  · intro l ρ hl hρ h
    rw [hY0] at h
    exact fix_of_fix hl hρ κ h

end At

end Formalism.L2.SG.Pf.ProdEApprox
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdEOf
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.StabShape

namespace Formalism.L2.SG.Pf.ProdE

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))

theorem bOf_unique (a : Formalism.L2.SG.PairVal.GLR D) (b : Formalism.L2.SG.PairVal.MatR D)
    (hW : (a : Formalism.L2.SG.PairVal.MatR D) * ptMat w * b = ptMat w) : VolPinAsm.bOf w a = b := by
  have hWu := Formalism.L2.SG.Pf.StabilizerIndexVolumes.ptMat_isUnit (K := D.host.E) w
  unfold VolPinAsm.bOf
  have h1 : (((a⁻¹ : Formalism.L2.SG.PairVal.GLR D)) : Formalism.L2.SG.PairVal.MatR D) * (a : Formalism.L2.SG.PairVal.MatR D) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  calc (ptMat w)⁻¹ * (((a⁻¹ : Formalism.L2.SG.PairVal.GLR D)) : Formalism.L2.SG.PairVal.MatR D) * ptMat w
      = (ptMat w)⁻¹ * (((a⁻¹ : Formalism.L2.SG.PairVal.GLR D)) : Formalism.L2.SG.PairVal.MatR D) *
          ((a : Formalism.L2.SG.PairVal.MatR D) * ptMat w * b) := by rw [hW]
    _ = (ptMat w)⁻¹ * ((((a⁻¹ : Formalism.L2.SG.PairVal.GLR D)) : Formalism.L2.SG.PairVal.MatR D) * (a : Formalism.L2.SG.PairVal.MatR D)) *
          ptMat w * b := by simp only [Matrix.mul_assoc]
    _ = b := by rw [h1, Matrix.mul_one, Matrix.nonsing_inv_mul _ hWu, Matrix.one_mul]

theorem mem_stabInt_glob (hA : ∀ p, Agree δ M p) (g : VolPinAsm.StG w) :
    ((g : Formalism.L2.SG.PairVal.GLR D) ∈ Formalism.L2.SG.PairVal.stabInt D u u' δ M w) ↔
      ∀ p, πP M δ u u' w (hA p) g ∈ AP M δ u u' w p := by
  have hset : ∀ a : VolPinAsm.StG w, (a : Formalism.L2.SG.PairVal.GLR D) ∈ Formalism.L2.SG.PairVal.stabIntSet D u u' δ M w ↔
      ∀ p, πP M δ u u' w (hA p) a ∈ AP M δ u u' w p := by
    intro a
    obtain ⟨ha, hb, hW⟩ := bOf_spec w a
    rw [mem_stabIntSet_iff δ M u u' hA w]
    refine ⟨fun h p => ?_, fun hp => ⟨ha, _, hb, hW, hp⟩⟩
    obtain ⟨-, b, -, hW', hp⟩ := h
    have e := bOf_unique w (a : Formalism.L2.SG.PairVal.GLR D) b hW'
    rw [← e] at hp
    exact hp p
  constructor
  · intro hg

    set K : Subgroup (Formalism.L2.SG.PairVal.GLR D) :=
      (Formalism.L2.SG.Pf.ProdE.glob (fun p => πP M δ u u' w (hA p)) (fun p => AP M δ u u' w p)).map
        (VolPinAsm.StG w).subtype with hK
    have hle : Formalism.L2.SG.PairVal.stabInt D u u' δ M w ≤ K := by
      unfold Formalism.L2.SG.PairVal.stabInt
      rw [Subgroup.closure_le]
      intro a ha
      have haSt : a ∈ VolPinAsm.StG w := by
        obtain ⟨h1, b, hb, hW, -⟩ := ha
        exact ⟨h1, b, hb, hW⟩
      refine ⟨⟨a, haSt⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, Formalism.L2.SG.Pf.ProdE.mem_glob]
      exact (hset ⟨a, haSt⟩).1 ha
    obtain ⟨g', hg', e⟩ := hle hg
    have : g' = g := Subtype.ext e
    rw [this, SetLike.mem_coe, Formalism.L2.SG.Pf.ProdE.mem_glob] at hg'
    exact hg'
  · intro hp
    exact Subgroup.subset_closure ((hset g).2 hp)

theorem lOf_conj {p : PlF D} (hA : Agree δ M p) (L U g b : Formalism.L2.SG.PairVal.MatR D) :
    lOf δ M p (L * g * L⁻¹) (U⁻¹ * b * U) = lOf δ M p L U * lOf δ M p g b * lOf δ M p L⁻¹ U⁻¹ := by
  rw [Matrix.mul_assoc L g, lOf_mul δ M hA L U (g * L⁻¹) (U⁻¹ * b), lOf_mul δ M hA g b L⁻¹ U⁻¹, Matrix.mul_assoc]

theorem ρOf_conj {p : PlF D} (hA : Agree δ M p) (L U g b : Formalism.L2.SG.PairVal.MatR D) :
    ρOf δ M p (L * g * L⁻¹) (U⁻¹ * b * U) = ρOf δ M p L⁻¹ U⁻¹ * ρOf δ M p g b * ρOf δ M p L U := by
  rw [Matrix.mul_assoc L g, ρOf_mul δ M hA L U (g * L⁻¹) (U⁻¹ * b), ρOf_mul δ M hA g b L⁻¹ U⁻¹]

theorem mem_CZ_glob (hA : ∀ p, Agree δ M p) (L U : Formalism.L2.SG.PairVal.MatR D) (hL : IsLoUni L) (hU : IsUpUni U)
    (Zh : Formalism.L2.SG.PairVal.MatR D) (hZ : ZhatOM Zh = L * ptMat w * U) (g : VolPinAsm.StG w) :
    ((g : Formalism.L2.SG.PairVal.GLR D) ∈ Formalism.L2.SG.Pf.ZsVolCut.CZ M δ u u' Zh L) ↔
      ∀ p, πP M δ u u' w (hA p) g ∈ CPL M δ u u' w (hA p) L U hL hU := by
  have hLi := ZsVolGrp.isLoUni_inv hL
  have hUi := ZsVolGrp.isUpUni_inv hU
  have hLdet : IsUnit L.det := by rw [ZsVolGrp.det_lo (fun a => (hL a a).2 rfl) (fun a b h => (hL a b).1 h)]; exact isUnit_one
  rw [ZsVolGrp.mem_CZ M δ u u' Zh L hLdet]
  obtain ⟨ha, hb, hW⟩ := bOf_spec w g
  set gm : Formalism.L2.SG.PairVal.MatR D := ((g : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) with hgm
  set b := VolPinAsm.bOf w (g : Formalism.L2.SG.PairVal.GLR D) with hb'
  have hmemC : ∀ p, πP M δ u u' w (hA p) g ∈ CPL M δ u u' w (hA p) L U hL hU ↔
      Formalism.MainNotions.S.TieN.IntLow (M p) (lOf δ M p (L * gm * L⁻¹) (U⁻¹ * b * U)) ∧
        Formalism.MainNotions.S.TieN.IntUp (M p) (ρOf δ M p (L * gm * L⁻¹) (U⁻¹ * b * U)) := by
    intro p
    rw [lOf_conj M δ (hA p), ρOf_conj M δ (hA p)]
    rfl
  simp only [hmemC]
  constructor
  · rintro ⟨a', ha'eq, ha'lo, b', hb'up, hZ', hloc⟩ p
    have ea' : ((a' : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) = L * gm * L⁻¹ := by
      have h := ha'eq
      rw [← hgm] at h
      rw [h]
      calc ((a' : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D)
          = (L * L⁻¹) * (a' : Formalism.L2.SG.PairVal.MatR D) * (L * L⁻¹) := by rw [hLi.2.2]; simp
        _ = L * (L⁻¹ * (a' : Formalism.L2.SG.PairVal.MatR D) * L) * L⁻¹ := by simp only [Matrix.mul_assoc]
    have eb' : b' = U⁻¹ * b * U := by
      have h1 : gm * ptMat w * (U * b' * U⁻¹) = ptMat w := by
        have := hZ'
        rw [hZ, ea'] at this
        have h2 : L⁻¹ * (L * gm * L⁻¹ * (L * ptMat w * U) * b') * U⁻¹ = L⁻¹ * (L * ptMat w * U) * U⁻¹ := by rw [this]
        calc gm * ptMat w * (U * b' * U⁻¹) = (L⁻¹ * L) * gm * (L⁻¹ * L) * ptMat w * U * b' * U⁻¹ := by
              rw [hLi.2.1]; simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
          _ = L⁻¹ * (L * gm * L⁻¹ * (L * ptMat w * U) * b') * U⁻¹ := by simp only [Matrix.mul_assoc]
          _ = L⁻¹ * (L * ptMat w * U) * U⁻¹ := h2
          _ = (L⁻¹ * L) * ptMat w * (U * U⁻¹) := by simp only [Matrix.mul_assoc]
          _ = ptMat w := by rw [hLi.2.1, hUi.2.2, Matrix.one_mul, Matrix.mul_one]
      have e := bOf_unique w (g : Formalism.L2.SG.PairVal.GLR D) _ h1
      rw [← hb'] at e
      rw [e]
      calc b' = (U⁻¹ * U) * b' * (U⁻¹ * U) := by rw [hUi.2.1]; simp
        _ = U⁻¹ * (U * b' * U⁻¹) * U := by simp only [Matrix.mul_assoc]
    obtain ⟨l, ρ, hl, hρ, hZl⟩ := hloc p
    obtain ⟨el, eρ⟩ := uniq δ M u u' (hA p) _ b' ha'lo hb'up l ρ (fun i => hl.1 i) (fun i => hρ.1 i) hZl
    rw [← ea', ← eb', ← el, ← eρ]
    exact ⟨hl, hρ⟩
  · intro hp
    set a'm := L * gm * L⁻¹ with ha'm
    have ha'lo : IsLoUni a'm := ZsVolGrp.isLoUni_mul (ZsVolGrp.isLoUni_mul hL ha) hLi.1
    have hb'up : IsUpUni (U⁻¹ * b * U) := ZsVolGrp.isUpUni_mul (ZsVolGrp.isUpUni_mul hUi.1 hb) hU
    have hginv : ((((g : Formalism.L2.SG.PairVal.GLR D))⁻¹ : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) * gm = 1 := by
      rw [hgm, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hginv' : gm * ((((g : Formalism.L2.SG.PairVal.GLR D))⁻¹ : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) = 1 := by
      rw [hgm, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    let a' : Formalism.L2.SG.PairVal.GLR D :=
      ⟨a'm, L * ((((g : Formalism.L2.SG.PairVal.GLR D))⁻¹ : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) * L⁻¹,
        by
          calc a'm * (L * ((((g : Formalism.L2.SG.PairVal.GLR D))⁻¹ : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) * L⁻¹)
              = L * gm * (L⁻¹ * L) * ((((g : Formalism.L2.SG.PairVal.GLR D))⁻¹ : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) * L⁻¹ := by
                simp only [ha'm, Matrix.mul_assoc]
            _ = 1 := by rw [hLi.2.1, Matrix.mul_one, Matrix.mul_assoc L, hginv', Matrix.mul_one, hLi.2.2],
        by
          calc (L * ((((g : Formalism.L2.SG.PairVal.GLR D))⁻¹ : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) * L⁻¹) * a'm
              = L * ((((g : Formalism.L2.SG.PairVal.GLR D))⁻¹ : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) * (L⁻¹ * L) * gm * L⁻¹ := by
                simp only [ha'm, Matrix.mul_assoc]
            _ = 1 := by rw [hLi.2.1, Matrix.mul_one, Matrix.mul_assoc L, hginv, Matrix.mul_one, hLi.2.2]⟩
    refine ⟨a', ?_, ha'lo, U⁻¹ * b * U, hb'up, ?_, fun p => ⟨_, _, (hp p).1, (hp p).2,
      move δ M u u' (hA p) a'm (U⁻¹ * b * U) ha'lo hb'up⟩⟩
    · show gm = L⁻¹ * a'm * L
      calc gm = (L⁻¹ * L) * gm * (L⁻¹ * L) := by rw [hLi.2.1]; simp
        _ = L⁻¹ * a'm * L := by simp only [ha'm, Matrix.mul_assoc]
    · show a'm * ZhatOM Zh * (U⁻¹ * b * U) = ZhatOM Zh
      rw [hZ]
      calc a'm * (L * ptMat w * U) * (U⁻¹ * b * U) = L * gm * (L⁻¹ * L) * ptMat w * (U * U⁻¹) * b * U := by
            simp only [ha'm, Matrix.mul_assoc]
        _ = L * (gm * ptMat w * b) * U := by
            rw [hLi.2.1, hUi.2.2, Matrix.mul_one, Matrix.mul_one]; simp only [Matrix.mul_assoc]
        _ = L * ptMat w * U := by rw [hW]

theorem idxRatio_self {G : Type} [Group G] (A : Subgroup G) : Formalism.L2.SG.Pf.IndexCocycleOrbits.IdxRatio A A = 1 := by
  unfold Formalism.L2.SG.Pf.IndexCocycleOrbits.IdxRatio; simp [Subgroup.relIndex_self]

theorem idxRatio_subgroupOf {G : Type} [Group G] (A B K : Subgroup G) (hA : A ≤ K) (hB : B ≤ K) :
    Formalism.L2.SG.Pf.IndexCocycleOrbits.IdxRatio (A.subgroupOf K) (B.subgroupOf K) = Formalism.L2.SG.Pf.IndexCocycleOrbits.IdxRatio A B := by
  unfold Formalism.L2.SG.Pf.IndexCocycleOrbits.IdxRatio
  rw [Subgroup.relIndex_subgroupOf hA, Subgroup.relIndex_subgroupOf hB]

theorem cz_le (L U : Formalism.L2.SG.PairVal.MatR D) (hL : IsLoUni L) (hU : IsUpUni U)
    (Zh : Formalism.L2.SG.PairVal.MatR D) (hZ : ZhatOM Zh = L * ptMat w * U) :
    Formalism.L2.SG.Pf.ZsVolCut.CZ M δ u u' Zh L ≤ VolPinAsm.StG w := by
  have hLi := ZsVolGrp.isLoUni_inv hL
  have hUi := ZsVolGrp.isUpUni_inv hU
  have hLdet : IsUnit L.det := by rw [ZsVolGrp.det_lo (fun a => (hL a a).2 rfl) (fun a b h => (hL a b).1 h)]; exact isUnit_one
  intro a ha
  rw [ZsVolGrp.mem_CZ M δ u u' Zh L hLdet] at ha
  obtain ⟨a', ha'eq, ha'lo, b', hb'up, hZ', -⟩ := ha
  refine ⟨?_, U * b' * U⁻¹, ZsVolGrp.isUpUni_mul (ZsVolGrp.isUpUni_mul hU hb'up) hUi.1, ?_⟩
  · rw [ha'eq]; exact ZsVolGrp.isLoUni_mul (ZsVolGrp.isLoUni_mul hLi.1 ha'lo) hL
  · rw [ha'eq]
    rw [hZ] at hZ'
    calc L⁻¹ * (a' : Formalism.L2.SG.PairVal.MatR D) * L * ptMat w * (U * b' * U⁻¹)
        = L⁻¹ * ((a' : Formalism.L2.SG.PairVal.MatR D) * (L * ptMat w * U) * b') * U⁻¹ := by simp only [Matrix.mul_assoc]
      _ = L⁻¹ * (L * ptMat w * U) * U⁻¹ := by rw [hZ']
      _ = (L⁻¹ * L) * ptMat w * (U * U⁻¹) := by simp only [Matrix.mul_assoc]
      _ = ptMat w := by rw [hLi.2.1, hUi.2.2, Matrix.one_mul, Matrix.mul_one]

variable (F0 : FlagG (VS D) D.R.rS (Formalism.L2.SG.CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

theorem prodE_of (hap : ApproxC M δ u u' F0 what₂) (hloc : LocIdxC M δ u u' F0 what₂) :
    Formalism.L2.SG.Pf.ZsVolCut.ProdE M δ u u' F0 what₂ (Formalism.L2.SG.Pf.ZsVolCut.CZ M δ u u') := by
  intro γ w F' L U hE
  obtain ⟨S, hS, hfin, happrox⟩ := hap γ w F' L U hE
  have hA := hE.1
  have hL : IsLoUni L := hE.2.2.2.2.2.2.2.1
  have hU : IsUpUni U := hE.2.2.2.2.2.2.2.2.1
  have hZ : ZhatOM (ZhatL (lf D F0) F') = L * ptMat w * U := hE.2.2.2.2.2.2.2.2.2
  have hset : Formalism.L2.SG.PairVal.stabIntSet D u u' δ M w ⊆ Formalism.L2.SG.Pf.StabilizerIndexVolumes.StSet (ptMat w) := by
    intro a ha
    obtain ⟨h1, b, hb, hW, -⟩ := ha
    exact ⟨h1, b, hb, hW⟩
  have hAle : Formalism.L2.SG.PairVal.stabInt D u u' δ M w ≤ VolPinAsm.StG w := fun x hx =>
    Formalism.L2.SG.Pf.StabilizerIndexVolumes.closure_subset_StSet Formalism.L2.SG.Pf.StabilizerIndexVolumes.stClosed _ _ hset hx
  have hCle := cz_le M δ u u' w L U hL hU _ hZ
  rw [← idxRatio_subgroupOf _ _ _ hAle hCle]
  have e1 : (Formalism.L2.SG.PairVal.stabInt D u u' δ M w).subgroupOf (VolPinAsm.StG w) =
      Formalism.L2.SG.Pf.ProdE.glob (fun p => πP M δ u u' w (hA p)) (fun p => AP M δ u u' w p) := by
    ext g
    rw [Subgroup.mem_subgroupOf, Formalism.L2.SG.Pf.ProdE.mem_glob]
    exact mem_stabInt_glob M δ u u' w hA g
  have e2 : (Formalism.L2.SG.Pf.ZsVolCut.CZ M δ u u' (ZhatL (lf D F0) F') L).subgroupOf (VolPinAsm.StG w) =
      Formalism.L2.SG.Pf.ProdE.glob (fun p => πP M δ u u' w (hA p)) (fun p => CPL M δ u u' w (hA p) L U hL hU) := by
    ext g
    rw [Subgroup.mem_subgroupOf, Formalism.L2.SG.Pf.ProdE.mem_glob]
    exact mem_CZ_glob M δ u u' w hA L U hL hU _ hZ g
  rw [e1, e2, Formalism.L2.SG.Pf.ProdE.idxRatio_glob _ _ _ S hS (fun p => (hfin p).1) (fun p => (hfin p).2) happrox]
  have hl := fun p => hloc γ w F' L U hE p
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := S)]
  · exact Finset.prod_congr rfl fun p _ => hl p
  · intro p hp
    by_contra hpS
    apply hp
    show Formalism.L2.SG.LsDatumB.wtL M δ (D.mem u).A.T (D.mem u').A.T p w
      (Formalism.L2.SG.CntLocal.ZZP (M := M) δ u u' p (ZhatL (lf D F0) F') * Formalism.L2.SG.LsDatumB.sgnP p) = 1
    rw [← hl p, hS p hpS, idxRatio_self]

end Formalism.L2.SG.Pf.ProdE
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ZsVolIn
section
noncomputable section

namespace Formalism.L2.SG.Pf.ZsVolIn

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.PairVal
  Formalism.L2.SG.Pf.ZsVolCut Formalism.L2.SG.Pf.ZsVolGrp Formalism.L2.SG.Pf.ZsVolShape Matrix
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word)
  (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

def FrameShapeP : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (L U : MatR D), HypE M δ u u' F0 what₂ γ w F' L U →
    ∀ s ∈ NLam γ.lam (lf D F0) ∩ NLam γ.lam F', ∀ uu uu' : MatR D, IsUpUni uu → IsUpUni uu' →
      (∀ b, s (F0.fvec b) = ∑ c, uu c b • F0.fvec c) → (∀ b, s (F'.fl.fvec b) = ∑ c, uu' c b • F'.fl.fvec c) →
        Formalism.L2.SG.Pf.StabIntSh.EntryShape D uu.conjTranspose
          (Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS * uu' * Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS)

theorem stabInCZ_of (hF : FrameShapeP M δ u u' F0 what₂) : Formalism.L2.SG.Pf.ZsVolOrb.StabInCZ M δ u u' F0 what₂ := by
  intro γ w F' L U hH
  obtain ⟨hA, hT, hR, hP, hE, hN⟩ := hH
  obtain ⟨_, _, hL, hU, hZ⟩ := hN
  have hT0 : ((Tu D u : ℕ) : D.host.E) ≠ 0 := by exact_mod_cast hP.1.pos.ne'
  have hLd : IsUnit L.det := by rw [Formalism.L2.SG.Pf.StabilizerIndexVolumes.lo_det hL]; exact isUnit_one
  refine (Subgroup.closure_le _).2 ?_
  rintro a ⟨s, ⟨hsF, hsF'⟩, uu, huu, ha⟩
  have hsF0 := hsF
  have hsF'0 := hsF'
  obtain ⟨⟨hiso, _⟩, hf1, hf2⟩ := hsF
  obtain ⟨⟨_, _⟩, hg1, hg2⟩ := hsF'
  obtain ⟨uu0, huu0, hu0⟩ := Formalism.L2.SG.Pf.StabilizerIndexVolumes.tri_exists F0 s hf1 hf2
  obtain ⟨uu', huu', hu'⟩ := Formalism.L2.SG.Pf.StabilizerIndexVolumes.tri_exists F'.fl s hg1 hg2
  have heq : uu = uu0 :=
    Formalism.L2.SG.Pf.StabilizerIndexVolumes.coef_unique (Formalism.L2.SG.Pf.StabilizerIndexVolumes.frame_indep F0 hT0) (fun b => s (F0.fvec b)) uu uu0 huu hu0
  subst heq
  have hZc := Formalism.L2.SG.Pf.StabilizerIndexVolumes.zhat_conj F0 F'.fl s hiso uu uu' hu0 hu'
  have hdet : IsUnit uu.conjTranspose.det := by
    rw [Formalism.L2.SG.Pf.StabilizerIndexVolumes.lo_det (Formalism.L2.SG.Pf.StabilizerIndexVolumes.lo_conjT huu0)]; exact isUnit_one
  let a' : GLR D := Matrix.nonsingInvUnit uu.conjTranspose hdet
  have ha' : (a' : MatR D) = uu.conjTranspose := rfl
  have hshape := hF γ w F' L U ⟨hA, hT, hR, hP, hE, ⟨‹_›, ‹_›, hL, hU, hZ⟩⟩ s ⟨hsF0, hsF'0⟩ uu uu' huu0 huu' hu0 hu'
  have hmem : a ∈ stZSet M δ u u' (ZhatL (lf D F0) F') L := by
    refine (mem_stZSet_iff M δ u u' hA _ L a).2 ⟨a', by rw [ha', ha], by rw [ha']; exact Formalism.L2.SG.Pf.StabilizerIndexVolumes.lo_conjT huu0,
      Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS * uu' * Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS, Formalism.L2.SG.Pf.StabilizerIndexVolumes.up_sgn huu', ?_, by rw [ha']; exact hshape⟩
    rw [ha', Formalism.L2.SG.Pf.StabilizerIndexVolumes.zhatOM_eq]
    show uu.conjTranspose * (Zhat F0 F'.fl * Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS) *
      (Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS * uu' * Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS) = Zhat F0 F'.fl * Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS
    rw [show uu.conjTranspose * (Zhat F0 F'.fl * Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS) *
        (Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS * uu' * Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS) =
      uu.conjTranspose * Zhat F0 F'.fl * (Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS * Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS) * uu' *
        Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS by simp only [Matrix.mul_assoc],
      Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM_sq, Matrix.mul_one, ← hZc]
  exact (mem_CZ M δ u u' _ L hLd a).2 hmem

end Formalism.L2.SG.Pf.ZsVolIn

end
end

