import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StepVectorLiftPairFlagLevelRealizedChain
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainCompositeLiftIntertwinesFiniteGroupActions
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodProjectorSmallestSpaceForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0008
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemCutQGrp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0441
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0452
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0470
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0468
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0469
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0473
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0471
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0027
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CongruenceLevelEqDepthSucc
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0128

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepLevLift
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
noncomputable section

namespace GlobalTheory.Mem.R3.DTheta.StepLevLift

theorem stepLev_lift : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Pins R F cG → Holds R F → ∀ (b : Bool) (t : T) (k : ℕ), k + 1 < D.R.m → ∀ κ ∈ levS (Yc D k) (R.βY k) (R.datYt t k (R.toRealDat.levR F.lv2 b)), ∃ κ' ∈ levS (Yc D (k + 1)) (R.βY (k + 1)) (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b)), R.ωY t k (κ, κ') (R.vY t k) = (levChi (Yc D k) (R.βY k) (R.datYt t k (R.toRealDat.levR F.lv2 b)) κ * (levChi (Yc D (k + 1)) (R.βY (k + 1)) (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b)) κ')⁻¹) • R.vY t k := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG hP hH b t k hk κ hκ
  have hL := hP.char.base.lev
  have hk' : k < D.R.m := Nat.lt_of_succ_lt hk
  obtain ⟨hκ1, hκ2⟩ := hκ
  set g0 : G0 R.Pg D.R.r := rTup (R.βY k) (R.datYt t k R.triv) (finE (Yc D k) κ) with hg0
  have hl : IsLevelLift (Yc D k) (R.βY k) (R.datYt t k R.triv) g0 κ := ⟨hκ1, hκ2.1, rfl⟩
  obtain ⟨κ', hl'⟩ := GlobalTheory.ChainLiftEquiv.liftsExist_chain R.toRealDat hL t (k + 1) hk g0
  have hlaw := GlobalTheory.StepVecLaw.stepVec_lifts R.toRealDat hL hP.char.base.models.inf hP.char.base.chain.ωY
    hP.char.base.chain.vY t k hk g0 κ κ' hl hl'
  have hmem : rTup (R.βY (k + 1)) (R.datYt t (k + 1) R.triv) (finE (Yc D (k + 1)) κ') ∈
      (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b)).P.H := by
    rw [hl'.2.2]; exact hκ2.2
  refine ⟨κ', ⟨hl'.1, hl'.2.1, hmem⟩, ?_⟩
  have e1 := levFn_withP (V := Yc D k) (β := R.βY k) (L := R.datYt t k (R.toRealDat.levR F.lv2 b))
    (R.datYt t k (R.toRealDat.levR F.lv2 b)).P (finE (Yc D k) κ)
  have e2 := levFn_withP (V := Yc D (k + 1)) (β := R.βY (k + 1)) (L := R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b))
    (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b)).P (finE (Yc D (k + 1)) κ')
  have x1 : ext1 (R.datYt t k (R.toRealDat.levR F.lv2 b)).P.H (R.datYt t k (R.toRealDat.levR F.lv2 b)).P.chi
      (rTup (R.βY k) (R.datYt t k (R.toRealDat.levR F.lv2 b)) (finE (Yc D k) κ)) =
      ext1 (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b)).P.H (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b)).P.chi
      (rTup (R.βY (k + 1)) (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b)) (finE (Yc D (k + 1)) κ')) := by
    have : rTup (R.βY (k + 1)) (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b)) (finE (Yc D (k + 1)) κ') = g0 := hl'.2.2
    rw [this]
    rfl
  unfold levChi
  change R.ωY t k (κ, κ') (R.vY t k) = (((Formalism.L2.DIV.levFn (R.βY k) (withP (R.datYt t k (R.toRealDat.levR F.lv2 b)) (R.datYt t k (R.toRealDat.levR F.lv2 b)).P) (finE (Yc D k) κ) : ℂˣ) : ℂ) * ((Formalism.L2.DIV.levFn (R.βY (k + 1)) (withP (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b)) (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b)).P) (finE (Yc D (k + 1)) κ') : ℂˣ) : ℂ)⁻¹) • R.vY t k
  rw [e1, e2, x1]
  unfold levChi at hlaw
  change ((Formalism.L2.DIV.levFn (R.βY k) (flagL (R.datYt t k (R.toRealDat.levR F.lv2 b))) (finE (Yc D k) κ) : ℂˣ) : ℂ)⁻¹ • R.ωY t k (κ, κ') (R.vY t k) = ((Formalism.L2.DIV.levFn (R.βY (k + 1)) (flagL (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b))) (finE (Yc D (k + 1)) κ') : ℂˣ) : ℂ)⁻¹ • R.vY t k at hlaw
  set c := ext1 (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b)).P.H (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b)).P.chi
      (rTup (R.βY (k + 1)) (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b)) (finE (Yc D (k + 1)) κ'))
  set a := Formalism.L2.DIV.levFn (R.βY k) (flagL (R.datYt t k (R.toRealDat.levR F.lv2 b))) (finE (Yc D k) κ)
  set a' := Formalism.L2.DIV.levFn (R.βY (k + 1)) (flagL (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b))) (finE (Yc D (k + 1)) κ')
  have ha : ((a : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hc : ((c : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have h3 : R.ωY t k (κ, κ') (R.vY t k) = (((a : ℂˣ) : ℂ) * ((a' : ℂˣ) : ℂ)⁻¹) • R.vY t k := by
    rw [mul_smul, ← hlaw, smul_inv_smul₀ ha]
  rw [h3, Units.val_mul, Units.val_mul]
  congr 1
  field_simp

end GlobalTheory.Mem.R3.DTheta.StepLevLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepPointDeterminedByLatticeInvariants
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.ChEx

open Classical in

theorem ptDet_cqOf : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
    {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ},
    (∀ P ∈ QE sel (mu : Chr X.F X.E X.K), P ∉ Pr.vGs) → (∀ w ∈ Pr.vGs, ((Formalism.L2.Col.qOf w : ℕ) : 𝓞 X.E) ∉ w.asIdeal ^ 2) →
    GlobalTheory.Mem.Col2.ChEx.PtDet (GlobalTheory.Mem.Col2.ChEx.cqOf (R := R) (cst := cst) (u := u) (j := j) : PtAt R sel mu cst u j → _) := by
  intro X Pr R sel S mu cst u j hQ hq r r' hfr hb hc
  suffices h2 : r.1.2 = r'.1.2 from Subtype.ext (Prod.ext hfr h2)
  have hd : r.1.1.deco = r'.1.1.deco := congrArg DecoF.deco hfr
  by_cases hj : j + 1 = R.m
  · obtain ⟨y, hy, eY⟩ := (show PtAt R sel mu cst u j from r).mem_ybSet hj
    obtain ⟨y', hy', eY'⟩ := (show PtAt R sel mu cst u j from r').mem_ybSet hj
    have eN : r'.1.1.deco.1.N = r.1.1.deco.1.N := by rw [hd]
    rw [eN] at hy' eY'
    have hyin : y ∈ r.1.2 := by rw [eY, mem_coset, sub_self]; exact zero_mem _
    rw [eY, eY']
    apply coset_eq
    refine (mem_locLat _ _ _ _).2 fun P => ?_
    by_cases hG : P.1 ∈ Pr.vGs
    · rw [if_pos hG, zpow_zero, inv_one, one_smul]
      have hm : r.1.1.deco.1.be ⟨P.1, hG⟩ (((Formalism.L2.Col.qOf P.1 : ℕ) : X.E) • y) ∈ bar r ⟨P.1, hG⟩ := ⟨y, hyin, rfl⟩
      rw [hb] at hm
      obtain ⟨z, hz, ez⟩ := hm
      rw [← hd] at ez
      rw [eY'] at hz
      have hz' := (mem_locLat _ _ _ _).1 (mem_coset.1 hz) P
      rw [if_pos hG, zpow_zero, inv_one, one_smul] at hz'
      have h1 := (mem_locLat _ _ _ _).1 hy P
      have h2 := (mem_locLat _ _ _ _).1 hy' P
      rw [if_pos hG, _root_.zpow_neg_one, inv_inv] at h1 h2
      exact sub_mem_of_be_eq r.1.1.deco.2 ⟨P.1, hG⟩ (hq _ hG) h1 h2 hz' ez
    · rw [if_neg hG, zpow_natCast]
      have hPQ : P.1 ∈ QE sel (mu : Chr X.F X.E X.K) := (Finset.mem_union.mp P.2).resolve_left hG
      have hfrP : frsF sel mu r.1.1 P = r.1.1.fr ⟨P.1, hPQ⟩ := by
        unfold frsF
        rw [dif_neg hG]
      have hc1 : (r.1.1.fr ⟨P.1, hPQ⟩).symm y ∈ cqOf r ⟨P.1, hPQ⟩ := ⟨y, hyin, by
        show ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then 0 else cst.M))⁻¹ • (_ - (frsF sel mu r.1.1 P).symm y) ∈ _
        rw [hfrP, sub_self, smul_zero]
        exact zero_mem _⟩
      rw [hc] at hc1
      obtain ⟨y0, hy0, hmem⟩ := hc1
      change ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then 0 else cst.M))⁻¹ • (_ - (frsF sel mu r'.1.1 P).symm y0) ∈ _ at hmem
      rw [if_neg hG, ← hfr, hfrP] at hmem
      have hA := (r.1.1.2 ⟨P.1, hPQ⟩ _).2 hmem
      change r.1.1.fr ⟨P.1, hPQ⟩ _ ∈ _ at hA
      rw [map_smul, map_sub, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at hA
      rw [eY'] at hy0
      have hB := (mem_locLat _ _ _ _).1 (mem_coset.1 hy0) P
      rw [if_neg hG, zpow_natCast] at hB
      have := add_mem hA hB
      rwa [← smul_add, sub_add_sub_cancel] at this
  · have h1 := r.2
    have h1' := r'.2
    rw [ysAt_ys_of_ne sel mu cst hj] at h1 h1'
    exact h1.trans h1'.symm

end GlobalTheory.Mem.Col2.ChEx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymmetricCharResidueConjEqWeightedUnipotentSum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.SymChar.ResBar

variable {D : D7}

theorem unip_inv_sup {κ : Type} [CommRing κ] {r : ℕ} {N : GL (Fin r) κ} (hN : N ∈ unip κ r) (i j : Fin r)
    (hij : j.val = i.val + 1) :
    ((N⁻¹ : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ) i j = -(N : Matrix (Fin r) (Fin r) κ) i j := by
  have hi := Subgroup.inv_mem _ hN
  have h := unip_mul_entry hi hN (i := i) (j := j) (show i.val < j.val by omega) (fun l h1 h2 => by
    exfalso
    have : i.val < l.val := h1
    have : l.val < j.val := h2
    omega)
  rw [inv_mul_cancel, Units.val_one, Matrix.one_apply_ne (by intro e; rw [e] at hij; omega)] at h
  linear_combination -h

abbrev QW (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) : Type :=
  (X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) ⧸ (wInt X w).toAddSubgroup

abbrev mkW (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) :
    (X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) →+ QW X w :=
  QuotientAddGroup.mk' _

theorem mkW_eq {X : HidaSetting D} {w : HeightOneSpectrum (𝓞 D.host.E)}
    {a b : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F} (h : a - b ∈ wInt X w) : mkW X w a = mkW X w b := by
  show (QuotientAddGroup.mk a : QW X w) = QuotientAddGroup.mk b
  rw [QuotientAddGroup.eq_iff_sub_mem]
  exact h

theorem mkW_zero {X : HidaSetting D} {w : HeightOneSpectrum (𝓞 D.host.E)}
    {a : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F} (h : a ∈ wInt X w) : mkW X w a = 0 := by
  rw [← map_zero (mkW X w)]
  exact mkW_eq (by rw [sub_zero]; exact h)

theorem phi_exists (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) (g : ℕ) [NeZero g]
    (hg : ((g : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) ∈ wInt X w) :
    ∃ φ : ZMod g →+ QW X w, ∀ t : ZMod g, φ t = t.val • mkW X w 1 := by
  refine ⟨ZMod.lift g ⟨zmultiplesHom _ (mkW X w 1), ?_⟩, fun t => ?_⟩
  · rw [zmultiplesHom_apply, natCast_zsmul, ← map_nsmul, nsmul_one]
    exact mkW_zero hg
  · conv_lhs => rw [← ZMod.natCast_zmod_val t]
    have e : ((t.val : ℕ) : ZMod g) = ((t.val : ℤ) : ZMod g) := by simp
    rw [e, ZMod.lift_coe, zmultiplesHom_apply, natCast_zsmul]

theorem modW_of {X : HidaSetting D} {w : HeightOneSpectrum (𝓞 D.host.E)} {g : ℕ}
    {φ : ZMod g →+ QW X w} (hφ : ∀ t : ZMod g, φ t = t.val • mkW X w 1)
    {c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F} {t : ZMod g} (h : mkW X w c = φ t) : ModW X w c t := by
  unfold ModW
  rw [hφ, ← map_nsmul, nsmul_one] at h
  show (c - ((t.val : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F)) ∈ (wInt X w).toAddSubgroup
  rw [← QuotientAddGroup.eq_iff_sub_mem]
  exact h

theorem read (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) {g : ℕ} {u : Fin D.R.r → VA X.B.I}
    {x : X.B.I.Gf} {M : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod g)} (hM : GlobalTheory.Mem.SymFrame.IsMatIn X w u x M)
    {v : VA X.B.I} (hv : v ∈ X.B.I.Lf) (p q : Fin D.R.r) (c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F)
    (hG : ∀ j, hA X.B.I v (u j) - (if j = q then c else 0) ∈ wInt X w) :
    mkW X w (hA X.B.I v (X.B.I.fmat x *ᵥ u p)) = (M q p).val • mkW X w c := by
  classical
  rw [mkW_eq (hA_isMatIn X w hM hv p), map_sum]
  have e : ∀ j, mkW X w ((((M j p).val : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) * hA X.B.I v (u j)) =
      if j = q then (M q p).val • mkW X w c else 0 := by
    intro j
    rw [← nsmul_eq_mul, map_nsmul, mkW_eq (hG j)]
    split_ifs with hj
    · rw [hj]
    · rw [map_zero, smul_zero]
  simp only [e, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem r_eq (D : D7) : D.R.r = 2 * D.R.rS + D.R.k + 1 := by
  obtain ⟨t, ht⟩ := D.R.m_even
  have h2 := D.R.two_le_m
  unfold Formalism.BasicNotions.Ranks.r Formalism.BasicNotions.Ranks.rS
  omega

theorem symVec_mem (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) (j : Fin D.R.r) :
    GlobalTheory.Mem.SymFrame.symVec X w j ∈ X.B.I.Lf := by
  unfold GlobalTheory.Mem.SymFrame.symVec GlobalTheory.SeeConjRead.flagV GlobalTheory.Mem.SymFrame.epsW
  split_ifs
  · exact (X.vectorsInLattice.1 _).1
  · exact (X.vectorsInLattice.2.2 _).1
  · exact (X.vectorsInLattice.2.2 _).2
  · exact X.vectorsInLattice.2.1
  · exact (X.vectorsInLattice.1 _).2
  · exact zero_mem _

theorem symmetricOrderFrameModPlace_last_block (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) (a : Fin D.R.rS) (p : Fin D.R.r)
    (hp : p.val = 2 * D.R.rS + D.R.k - a.val) : GlobalTheory.Mem.SymFrame.symVec X w p = X.f0 a := by
  have hr := r_eq D
  unfold GlobalTheory.Mem.SymFrame.symVec GlobalTheory.SeeConjRead.flagV
  rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_pos (by omega)]
  congr 1
  ext
  simp only
  omega

theorem symVec_bwd (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) (hE : ¬ GlobalTheory.Mem.SymFrame.EwAt X w)
    (i : Fin D.R.k) (p : Fin D.R.r) (hp : p.val = D.R.rS + D.R.k - 1 - i.val) :
    GlobalTheory.Mem.SymFrame.symVec X w p = X.bwd i := by
  unfold GlobalTheory.Mem.SymFrame.symVec GlobalTheory.SeeConjRead.flagV GlobalTheory.Mem.SymFrame.epsW
  rw [if_neg hE, dif_neg (by omega), dif_pos (by omega)]
  congr 1
  ext
  simp only [Fin.val_rev]
  omega

theorem ite_val {r : ℕ} {R : Type} [Zero R] (j q : Fin r) (n : ℕ) (hq : q.val = n) (c : R) :
    (if j.val = n then c else 0) = (if j = q then c else 0) := by
  by_cases h : j = q
  · subst h; simp [hq]
  · have : j.val ≠ n := fun e => h (Fin.ext (by omega))
    simp [h, this]

theorem resBar : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal) → ∀ (kv : Σ k : Fin 2, D.nd.PlG k), ∀ k ∈ X.B.I.Kset, ∀ N : GL (Fin D.R.r) (ZMod (D.host.g kv.1)), GlobalTheory.Mem.SymFrame.IsMatIn X (D.naut.plGw kv.1 kv.2) (GlobalTheory.Mem.SymFrame.symVec X (D.naut.plGw kv.1 kv.2)) k (N : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) → N ∈ unipSym (ZMod (D.host.g kv.1)) D.R.r D.R.rS D.R.k → GlobalTheory.Mem.SymChar.ModW X (D.naut.plGw kv.1 kv.2) (sigA X.B.I (GlobalTheory.Mem.SymChar.argS X k)) (∑ i, ∑ j, if symEdge D.R.rS D.R.k i j then ((GlobalTheory.Mem.SymChar.wtB D.R.rS D.R.k (GlobalTheory.Mem.SymChar.side X (D.naut.plGw kv.1 kv.2)) i j : ℤ) : ZMod (D.host.g kv.1)) * (N : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) i j else 0) := by
  intro D X h hι hg kv k hk N hN hNu
  classical
  have hgw := hg kv
  set w := D.naut.plGw kv.1 kv.2 with hw
  haveI : NeZero (D.host.g kv.1) := ⟨(D.host.g_prime kv.1).ne_zero⟩
  have hgA : (((D.host.g kv.1 : ℕ)) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) ∈ wInt X w := by
    refine Submodule.subset_span ⟨((D.host.g kv.1 : ℕ) : 𝓞 X.B.I.E), ⟨_, hgw, ?_⟩, ?_⟩
    · simp
    · simp
  obtain ⟨φ, hφ⟩ := phi_exists X w _ hgA
  have hr := r_eq D
  set u := GlobalTheory.Mem.SymFrame.symVec X w with hu_def
  have hu : ∀ i, u i ∈ X.B.I.Lf := symVec_mem X w
  have hNi := GlobalTheory.T.isMatrixModPlaceInFamily_inv D X kv hgw u hu k hk N hN
  have hU : N ∈ unip _ _ := unipCol_le _ _ _ hNu
  rw [GlobalTheory.T.symEdge_conjWeighted_sum_eq_flag_and_unipotent_pairs _ _ _ hr]
  apply modW_of hφ
  simp only [argS, map_add, map_sum]
  congr 1
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Formalism.L2.SG.Pf.unitaryCongruence.hA_symm]
    have e := GlobalTheory.St.G.FrameClose.hA_move k⁻¹ (nxt X.e0 X.z0 a) (X.f0 a)
    rw [inv_inv] at e
    rw [← e, ← symmetricOrderFrameModPlace_last_block X w a ⟨2 * D.R.rS + D.R.k - a.val, by omega⟩ rfl]
    by_cases ha : a.val + 1 < D.R.rS
    · rw [dif_pos ha]
      have hn : nxt X.e0 X.z0 a = X.e0 ⟨a.val + 1, ha⟩ := by unfold nxt; rw [dif_pos ha]
      rw [hn, read X w hNi (X.vectorsInLattice.1 _).1 _ ⟨2 * D.R.rS + D.R.k - a.val - 1, by omega⟩ 1 (fun j => by
        rw [← ite_val j _ (2 * D.R.rS + D.R.k - (a.val + 1)) (by simp only; omega)]
        exact GlobalTheory.T.hermitian_e0_symmetric_frame D X kv hgw ⟨a.val + 1, ha⟩ j), ← hφ, unip_inv_sup hU _ _ (by simp only; omega)]
    · rw [dif_neg ha]
      have hn : nxt X.e0 X.z0 a = X.z0 := by unfold nxt; rw [dif_neg ha]
      have hp : (⟨2 * D.R.rS + D.R.k - a.val, by omega⟩ : Fin D.R.r) = ⟨D.R.rS + D.R.k + 1, by omega⟩ :=
        Fin.ext (by simp only; omega)
      rw [hn, hp, read X w hNi X.vectorsInLattice.2.1 _ ⟨D.R.rS + D.R.k, by omega⟩ (-1) (fun j => by
        rw [← ite_val j _ (D.R.rS + D.R.k) rfl]
        exact GlobalTheory.T.hermitian_z0_symmetric_frame D X kv hgw j), map_neg, smul_neg, ← hφ, ← map_neg, unip_inv_sup hU _ _ (by simp only),
        neg_neg]
  · by_cases hE : GlobalTheory.Mem.SymFrame.EwAt X w
    · have hs : side X w = true := by simp [side, hE]
      rw [hs, if_pos rfl, map_zero]
      refine Finset.sum_eq_zero fun i _ => ?_
      by_cases hi : i.val + 1 < D.R.k
      · rw [dif_pos hi]
        apply mkW_zero
        rw [← Formalism.L2.SG.Pf.unitaryCongruence.hA_symm]
        have hb : X.bwd i ∈ wLf X w := by
          have h1 := hE (X.bwd i) (X.vectorsInLattice.2.2 i).2
          have e : (1 - X.ew) • X.bwd i = X.bwd i := by
            conv_lhs => rw [X.bwd_w i]
            rw [smul_smul, sub_mul, one_mul, X.ew_orth, sub_zero, ← X.bwd_w i]
          rwa [e] at h1
        exact hA_mem_wInt X w (Formalism.L2.SG.Pf.unitaryCongruence.K_mv X.B.I hk (X.vectorsInLattice.2.2 _).1) hb
      · rw [dif_neg hi, map_zero, map_zero]
    · have hs : side X w = false := by simp [side, hE]
      have hew := GlobalTheory.T.conj_idempotent_sub_one_mem_placeIdeal D X h hι kv hgw hE
      rw [hs, if_neg (by simp), map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hi : i.val + 1 < D.R.k
      · rw [dif_pos hi, dif_pos hi]
        rw [← Formalism.L2.SG.Pf.unitaryCongruence.hA_symm]
        have e := GlobalTheory.St.G.FrameClose.hA_move k⁻¹ (X.bw ⟨i.val + 1, hi⟩) (X.bwd i)
        rw [inv_inv] at e
        rw [← e, ← symVec_bwd X w hE i ⟨D.R.rS + D.R.k - 1 - i.val, by omega⟩ rfl,
          read X w hNi (X.vectorsInLattice.2.2 _).1 _ ⟨D.R.rS + D.R.k - 2 - i.val, by omega⟩ 1 (fun j => by
            rw [← ite_val j _ (D.R.rS + D.R.k - 1 - (i.val + 1)) (by simp only; omega)]
            exact GlobalTheory.T.hermitianForm_middle_symmetricFrame_not_oneAt D X kv hgw hE hew ⟨i.val + 1, hi⟩ j), ← hφ, unip_inv_sup hU _ _ (by simp only; omega)]
      · rw [dif_neg hi, dif_neg hi, map_zero, map_zero, map_zero]

end GlobalTheory.Mem.SymChar.ResBar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistPrimeRowTypeTopRestrictionMulLevelCharEqOne
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.TopRowsQ

open GlobalTheory.TopStep GlobalTheory.Mem.Col2 GlobalTheory.TopLaw

theorem redV_eq_of_cong {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {P : HeightOneSpectrum (𝓞 E)} {c : ℕ}
    (hc : 0 < c) {a b : Sp E n} (hb : b ∈ stdAt E n P) (h : (((qOf P : ℕ) : E) ^ c)⁻¹ • (a - b) ∈ stdAt E n P) :
    a ∈ stdAt E n P ∧ redV P a = redV P b := by
  have hq := qOf_ne_zero (P := P)
  have h1 : ∀ i, IntAt P ((((qOf P : ℕ) : E) ^ c)⁻¹ * (a i - b i)) := fun i => mem_stdAt.1 h i
  have h2 : ∀ i, IntAt P (a i - b i) := fun i => by
    have h3 := (intAt_pow (intAt_nat (P := P) (qOf P)) c).mul (h1 i)
    convert h3 using 1
    field_simp
  have ha : ∀ i, IntAt P (a i) := fun i => by
    have h3 := (h2 i).add (mem_stdAt.1 hb i)
    convert h3 using 1
    ring
  refine ⟨mem_stdAt.2 ha, funext fun i => ?_⟩
  have h4 : redP P (a i - b i) = 0 := by
    apply redP_eq_zero_of_div
    have h3 := (intAt_pow (intAt_nat (P := P) (qOf P)) (c - 1)).mul (h1 i)
    convert h3 using 1
    obtain ⟨c, rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    simp only [Nat.add_sub_cancel, pow_succ]
    field_simp
  rw [reduction_sub (ha i) (mem_stdAt.1 hb i), sub_eq_zero] at h4
  exact h4

theorem lamQB_mul_levCong : ∀ {X : Fields} {R : Ranks} (ξ : Chr X.F X.E X.K) (Q : Finset (HeightOneSpectrum (𝓞 X.E))) (P : Q) (c M : ℕ), 1 ≤ M →
    ∀ (k : Formalism.L2.Col.GLint X.E (R.N R.m) P.1) (hk : k ∈ (levCong (N_m_succ R) P.1 c (rowTyQ R ξ Q P)).H)
    (g : Sp X.E (R.N R.m) ≃ₗ[X.E] Sp X.E (R.N R.m)) (g'' : Sp X.E ((R.N R.m - 1) + 0) ≃ₗ[X.E] Sp X.E ((R.N R.m - 1) + 0)),
    g'' ∈ LocE.JQ P.1 (qOf P.1) R.r (R.N R.m - 1) 0 →
    prXpG X.E (R.N R.m) ∘ₗ g.toLinearMap = g''.toLinearMap ∘ₗ prXpG X.E (R.N R.m) →
    CongE P.1 (2 * M) g (k⁻¹).1 →
    LocE.lamQB (resChar ξ P.1) R.r (R.N R.m - 1) g''.toLinearMap *
      (((levCong (N_m_succ R) P.1 c (rowTyQ R ξ Q P)).lam ⟨k, hk⟩ : X.Kˣ) : X.K) = 1 := by
  intro X R ξ Q P c M hM k hk g g'' hJ hpr hC
  have hN := N_m_succ R
  obtain ⟨j, hj, hb⟩ := (mem_levCong (N_m_succ R) c _ k).1 hk
  rw [levCong_lam (N_m_succ R) c _ hk hj hb, levRed_lam]
  have ek : redGL _ P.1 k = diagEmb _ (by omega : R.N R.m - 1 ≤ R.N R.m) (redGL _ P.1 j) := by
    have e := redGL_of_prinCong c.succ_pos hb
    rw [map_mul, map_inv, inv_mul_eq_one, redGL_extI] at e
    exact e.symm
  let g2 : Formalism.L2.Col.GLint X.E (R.N R.m - 1) P.1 := ⟨g'', hJ.1⟩
  have hred : redGL _ P.1 g2 = (redGL _ P.1 j)⁻¹ := by
    refine redGL_eq g2 fun x hx => ?_
    let v : Sp X.E (R.N R.m) := fun l => if h : l.1 < R.N R.m - 1 then x ⟨l.1, h⟩ else 0
    have hv : v ∈ stdAt X.E (R.N R.m) P.1 := mem_stdAt.2 fun l => by
      by_cases h : l.1 < R.N R.m - 1
      · simp only [v, dif_pos h]; exact mem_stdAt.1 hx _
      · simp only [v, dif_neg h]; simpa using intAt_nat (P := P.1) 0
    have hpv : prXpG X.E (R.N R.m) v = x := by
      funext i
      show v _ = x i
      simp only [v, dif_pos (show i.1 < R.N R.m - 1 from i.2)]
      rfl
    have hxg : g'' x = prXpG X.E (R.N R.m) (g v) := by
      have := LinearMap.congr_fun hpr v
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hpv] at this
      exact this.symm
    obtain ⟨-, e1⟩ := redV_eq_of_cong (by omega : 0 < 2 * M) (glint_mem k⁻¹ hv) (hC v hv)
    have e2 := redV_redGL k⁻¹ hv
    rw [map_inv, ek, ← map_inv, diagEmb_val] at e2
    funext i
    have e3 := congrFun e1 (Br.iC hN i)
    rw [e2, (diagMat_mulVec hN _ _).1] at e3
    show redP P.1 (g'' x i) = _
    rw [hxg]
    refine e3.trans ?_
    congr 1
    funext l
    show redP P.1 (v (Br.iC hN l)) = redP P.1 (x l)
    simp only [v, Br.iC, dif_pos l.2]
  have hH : redGL _ P.1 g2 ∈ HQ (𝓞 X.E ⧸ P.1.asIdeal) (R.N R.m - 1) R.r (R.m * R.t) := hred ▸ inv_mem hj
  have hl := lamQB_eq_red (resChar ξ P.1) (rank_X'_eq R) g2 hH
  rw [show (g''.toLinearMap : HomE X.E _ _) = g2.1.toLinearMap from rfl, hl]
  have e4 : lamQ (resChar ξ P.1) _ R.r (R.m * R.t) ⟨redGL _ P.1 g2, hH⟩ =
      (lamQ (resChar ξ P.1) _ R.r (R.m * R.t) ⟨redGL _ P.1 j, hj⟩)⁻¹ := by
    rw [← map_inv]
    exact congrArg _ (Subtype.ext hred)
  rw [← Units.val_mul, e4]
  show (((_ : X.Kˣ)⁻¹)⁻¹ * (lamQP ξ P.1 (R.N R.m - 1) R.r (R.m * R.t) ⟨redGL _ P.1 j, hj⟩)⁻¹ : X.Kˣ).1 = 1
  rw [inv_inv, lamQP, mul_inv_cancel, Units.val_one]

end GlobalTheory.TopRowsQ
end
end

