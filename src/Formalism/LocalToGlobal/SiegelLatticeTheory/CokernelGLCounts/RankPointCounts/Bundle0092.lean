import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0081
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0090
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFrameIota
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0091
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdBetaS
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0043
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.MSTypP

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarLprClose
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem lprPart_holds : LprPart Zd u u' F0 what₂ :=
  LprEx.lprPart_of_iota Zd Formalism.L2.SG.Pf.iotaStep_holds

theorem fStarC_of_beta (hC : CtxP u u' F0 what₂) (hRat : BetaRat Zd u u' F0 what₂) (hInt : BetaInt Zd u u' F0 what₂) :
    FStarC Zd u u' F0 what₂ :=
  fStarC_of_leaves' Zd hC (lprPart_holds Zd) hRat hInt

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FrameEntry
section
noncomputable section

namespace Formalism.L2.SG.Pf.ZsVolLat

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7}

theorem sum_fvec {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (w : Fin (D.R.rS + 1) → D.host.E) :
    ∑ c, w c • F0.fvec c = ∑ a : Fin D.R.rS, w (Fin.castSucc a) • F0.e a + w (Fin.last _) • F0.z := by
  rw [Fin.sum_univ_castSucc]
  simp [FlagG.fvec, Fin.snoc_castSucc, Fin.snoc_last]

theorem frame_entry {T : D.host.E} (F : LFlag (VS D) D.R.rS T) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (hX : XLam Λ F = XS D F.fl) (hz : F.fl.z ∈ Λ) (s : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hs : ∀ v ∈ Λ, s v ∈ Λ)
    (uu : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) (huu : IsUpUni uu)
    (hfr : ∀ b, s (F.fl.fvec b) = ∑ c, uu c b • F.fl.fvec c) (c b : Fin (D.R.rS + 1)) (hcb : c < b) :
    uu c b ∈ ddS D ^ (-((((b : ℕ) - (c : ℕ) : ℕ)) : ℤ)) := by
  have hne := Formalism.L2.SG.Pf.StabIntSh.lg_ddS_ne (D := D)
  have hXS_le : XS D F.fl ≤ Λ := by rw [← hX]; exact inf_le_left
  have hXmem : ∀ y : Fin D.R.rS → D.host.E, (∑ a, y a • F.fl.e a) ∈ Λ → (∑ a, y a • F.fl.e a) ∈ XS D F.fl := by
    intro y hy
    rw [← hX]
    refine Submodule.mem_inf.2 ⟨hy, ?_⟩
    show (∑ a, y a • F.fl.e a) ∈ F.fl.X
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  have hc : (c : ℕ) < D.R.rS := lt_of_lt_of_le hcb (Nat.lt_succ_iff.1 b.2)
  obtain ⟨a, rfl⟩ : ∃ a : Fin D.R.rS, c = Fin.castSucc a := ⟨⟨c, hc⟩, rfl⟩
  induction b using Fin.lastCases with
  | last =>
    have hv : s F.fl.z - F.fl.z = ∑ a', uu (Fin.castSucc a') (Fin.last _) • F.fl.e a' := by
      have h := hfr (Fin.last _)
      rw [sum_fvec] at h
      simp only [FlagG.fvec, Fin.snoc_last] at h
      rw [h, (huu _ _).2 rfl, one_smul, add_sub_cancel_right]
    have hmem : s F.fl.z - F.fl.z ∈ XS D F.fl := by
      rw [hv]
      apply hXmem
      rw [← hv]
      exact Λ.sub_mem (hs _ hz) hz
    have h := coef_XS F.fl hmem _ hv a
    have e : (-((((Fin.last D.R.rS : Fin (D.R.rS + 1)) : ℕ) - ((Fin.castSucc a : Fin (D.R.rS + 1)) : ℕ) : ℕ)) : ℤ) =
        -((D.R.rS : ℤ) - ((a : ℕ) : ℤ)) := by
      simp only [Fin.val_last, Fin.val_castSucc]
      rw [Nat.cast_sub a.2.le]
    rw [e]
    exact h
  | cast b' =>
    have hab : (a : ℕ) < b' := hcb
    have key : ∀ x ∈ ddS D ^ (-((D.R.rS : ℤ) - ((b' : ℕ) : ℤ))),
        x * uu (Fin.castSucc a) (Fin.castSucc b') ∈ ddS D ^ (-((D.R.rS : ℤ) - ((a : ℕ) : ℤ))) := by
      intro x hx
      have hgen : x • F.fl.e b' ∈ XS D F.fl := Submodule.subset_span ⟨b', x, hx, rfl⟩
      have hv : s (x • F.fl.e b') = ∑ a', (x * uu (Fin.castSucc a') (Fin.castSucc b')) • F.fl.e a' := by
        have h := hfr (Fin.castSucc b')
        rw [sum_fvec] at h
        simp only [FlagG.fvec, Fin.snoc_castSucc] at h
        rw [LinearEquiv.map_smul, h, (huu _ _).1 (Fin.castSucc_lt_last b'), zero_smul, add_zero, Finset.smul_sum]
        refine Finset.sum_congr rfl fun a' _ => ?_
        rw [smul_smul]
      have hmem : s (x • F.fl.e b') ∈ XS D F.fl := by
        rw [hv]
        apply hXmem
        rw [← hv]
        exact hs _ (hXS_le hgen)
      exact coef_XS F.fl hmem _ hv a
    have h := mem_of_mul (ddS D) hne _ _ _ key
    have e : (-((((Fin.castSucc b' : Fin (D.R.rS + 1)) : ℕ) - ((Fin.castSucc a : Fin (D.R.rS + 1)) : ℕ) : ℕ)) : ℤ) =
        -((D.R.rS : ℤ) - ((a : ℕ) : ℤ)) - -((D.R.rS : ℤ) - ((b' : ℕ) : ℤ)) := by
      simp only [Fin.val_castSucc]
      rw [Nat.cast_sub hab.le]
      ring
    rw [e]
    exact h

end Formalism.L2.SG.Pf.ZsVolLat

end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IdxRatioConjOfUnimod
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.StabShape Formalism.L2.SG.Pf.ProdE
  Formalism.L2.SG.Pf.ProdEP2Core Formalism.L2.SG.Pf.IndexCocycleOrbits

namespace Formalism.L2.SG.Pf.ProdEP2Cut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem idxRatio_conj_of_unimod {G : Type} [Group G] (A B : Subgroup G) (s : G) (hBA : B ≤ A) (hf : B.relIndex A ≠ 0)
    (hU : IdxRatio A (cj s A) = 1) : IdxRatio A (cj s B) = (B.relIndex A : ℝ) := by
  rw [idxCocycle G A (cj s B) (cj s A) (cj_le hBA) (by rw [relIndex_cj]; exact hf), hU, relIndex_cj, mul_one]

theorem unimod_of_sub {G : Type} [Group G] (A B' : Subgroup G) (s : G) (hAB' : A ≤ B') (hs : s ∈ B')
    (hf : A.relIndex B' ≠ 0) : IdxRatio A (cj s A) = 1 := by
  have h := idxRatio_conj_sub A A B' s le_rfl hAB' hs hf
  rw [h, Subgroup.relIndex_self, Nat.cast_one]

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word) {p : PlF D}

def UnimodAt (w : Point D.host.E (D.R.rS + 1)) : Prop :=
  ∀ s ∈ StP M δ u u' w p, IdxRatio (Ag M δ u u' (p := p) w) (cj s (Ag M δ u u' (p := p) w)) = 1

theorem unimod_of_over (w : Point D.host.E (D.R.rS + 1)) (h : OverAt M δ u u' (p := p) w) : UnimodAt M δ u u' (p := p) w := by
  intro s hs
  obtain ⟨B', hAB', hsB', hf⟩ := h s hs
  exact unimod_of_sub _ B' s hAB' hsB' hf

theorem locIdx_at' (w : Point D.host.E (D.R.rS + 1)) (hA : Agree δ M p) (L U : Formalism.L2.SG.PairVal.MatR D)
    (hL : IsLoUni L) (hU : IsUpUni U) (v : ℝ) (hN : CountAt M δ u u' w hA L U hL hU v)
    (hO : UnimodAt M δ u u' (p := p) w) :
    IdxRatio (AP M δ u u' w p) (CPL M δ u u' w hA L U hL hU) = v := by
  rw [idxRatio_map]
  obtain ⟨N, π, hR, hHN, hg, hBA, hfA, hv⟩ := hN
  have hC := cShape M δ u u' hA L U hL hU w
  have hCS : cj (g0 M δ hA L U hL hU) (KP M p ⊓ StabX p (XP M δ u u' w L U)) ≤ StP M δ u u' w p := by
    rw [← hC]
    rintro _ ⟨x, _, rfl⟩
    exact x.2
  show IdxRatio (Ag M δ u u' w) (Cg M δ u u' w hA L U hL hU) = v
  rw [hC, cj_eq_cj_img hR hHN hg hCS, idxRatio_conj_of_unimod _ _ _ hBA hfA (hO _ (hR.mem _ hg)), hv]

variable (F0 : FlagG (VS D) D.R.rS (Formalism.L2.SG.CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

def StepsU : Prop :=
  ∀ (γ : Formalism.L2.SG.TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (L U : Formalism.L2.SG.PairVal.MatR D)
    (hE : Formalism.L2.SG.Pf.ZsVolCut.HypE M δ u u' F0 what₂ γ w F' L U) (p : PlF D),
    CountAt M δ u u' w (hE.1 p) L U hE.2.2.2.2.2.2.2.1 hE.2.2.2.2.2.2.2.2.1
      (Formalism.L2.SG.LsDatumB.wtL M δ (D.mem u).A.T (D.mem u').A.T p w
        (Formalism.L2.SG.CntLocal.ZZP (M := M) δ u u' p (ZhatL (lf D F0) F') * Formalism.L2.SG.LsDatumB.sgnP p)) ∧
    UnimodAt M δ u u' (p := p) w

theorem locIdxC_of_count (h : StepsU M δ u u' F0 what₂) : LocIdxC M δ u u' F0 what₂ := by
  intro γ w F' L U hE p
  obtain ⟨hN, hO⟩ := h γ w F' L U hE p
  exact locIdx_at' M δ u u' w _ L U _ _ _ hN hO

end Formalism.L2.SG.Pf.ProdEP2Cut
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LmatUp
section
noncomputable section

open scoped Classical Matrix
open ValuativeRel

namespace Formalism.L2.SG.Pf.FibQ

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups PI.PairValDefs PI.NRCW IsDedekindDomain
  Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section ModeG3

variable {D : D7} (Z : LocDat D) (p : PlF D) (g : Formalism.MainNotions.S.Loc.SplitG (Z.M p).L)

theorem lmat_up {l ρ : Formalism.L2.SG.LsDatumB.MatP D p} (hl0 : ∀ a b, a < b → l a b = 0) (hl1 : ∀ a, l a a = 1)
    (hρ0 : ∀ a b, b < a → ρ a b = 0) (hρ1 : ∀ a, ρ a a = 1) :
    (∀ a b, b < a → lmat Z p g ρ l a b = 0) ∧ ∀ a, lmat Z p g ρ l a a = 1 := by
  refine ⟨fun a b h => ?_, fun a => ?_⟩
  · simp only [lmat, Matrix.of_apply, hρ0 a b h, hl0 b a h, map_zero, Prod.fst_zero, Prod.snd_zero]
    rw [show ((0 : (D.s.atP p).Fp), (0 : (D.s.atP p).Fp)) = 0 from rfl, map_zero]
  · simp only [lmat, Matrix.of_apply, hl1 a, hρ1 a, map_one, Prod.fst_one, Prod.snd_one]
    rw [show ((1 : (D.s.atP p).Fp), (1 : (D.s.atP p).Fp)) = 1 from rfl, map_one]

theorem modeG (hs : (Z.M p).split = some g) (u u' : D.what₂.Word)
    (N M Z₁ Z₂ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E)
    (hNU : ∀ a b, b < a → N a b = 0) (hNd : ∀ a, N a a = 1) (hMU : ∀ a b, b < a → M a b = 0)
    (hMd : ∀ a, M a a = 1)
    (hNb : ∀ c b, c < b → ∀ x ∈ aaF D b, x * N c b ∈ aaF D c)
    (hMb : ∀ c b, c < b → ∀ x ∈ aaF D b, x * M c b ∈ aaF D c) (hrel : Nᴴ * Z₂ = Z₁ * M)
    (hcong : Cq Z p g (locU Z p N * locU Z p M - 1)) :
    ∃ l ρ, Formalism.MainNotions.S.TieN.IntLow (Z.M p) l ∧ Formalism.MainNotions.S.TieN.IntUp (Z.M p) ρ ∧
      Formalism.L2.SG.CntLocal.ZZP (M := Z.M) Z.δ u u' p Z₂ * Formalism.L2.SG.LsDatumB.sgnP p =
        l * (Formalism.L2.SG.CntLocal.ZZP (M := Z.M) Z.δ u u' p Z₁ * Formalism.L2.SG.LsDatumB.sgnP p) * ρ := by
  obtain ⟨hN1, hN0, hNO⟩ := locU_int Z p N hNU hNd hNb
  obtain ⟨hM1, hM0, hMO⟩ := locU_int Z p M hMU hMd hMb
  set Nl := locU Z p N with hNl
  set Ml := locU Z p M with hMl
  set K := (Nl.map (Z.M p).L.cj)ᵀ with hKdef
  have hK0 : ∀ a b, a < b → K a b = 0 := fun a b h => by
    simp only [hKdef, Matrix.transpose_apply, Matrix.map_apply, hN0 b a h, map_zero]
  have hK1 : ∀ a, K a a = 1 := fun a => by
    simp only [hKdef, Matrix.transpose_apply, Matrix.map_apply, hN1 a, map_one]
  have hKO : IntM Z p K := fun i j => PI.LocCntLat.GC.cj_mem_O _ (hNO j i)
  have hKdet : K.det = 1 := det_lower p hK0 hK1
  have hKu : IsUnit K.det := by rw [hKdet]; exact isUnit_one
  have hNdet : Nl.det = 1 := det_upper p hN0 hN1
  have hNu : IsUnit Nl.det := by rw [hNdet]; exact isUnit_one
  have hl0O : IntM Z p K⁻¹ := Formalism.L2.SG.Pf.LocOrbCut.inv_int (Z.M p).L.O K hKO hKdet
  have hNiO : IntM Z p Nl⁻¹ := Formalism.L2.SG.Pf.LocOrbCut.inv_int (Z.M p).L.O Nl hNO hNdet
  have hl0low : (∀ a b, a < b → K⁻¹ a b = 0) ∧ ∀ a, K⁻¹ a a = 1 := by
    have h := Formalism.L2.SG.TermLoc.inv_unitri Kᵀ (fun a b h => by rw [Matrix.transpose_apply]; exact hK0 b a h)
      (fun a => by rw [Matrix.transpose_apply]; exact hK1 a)
    rw [← Matrix.transpose_nonsing_inv] at h
    exact ⟨fun a b hab => by have := h.1 b a hab; rwa [Matrix.transpose_apply] at this,
      fun a => by have := h.2 a; rwa [Matrix.transpose_apply] at this⟩
  have hK := key_rel Z p N M Z₁ Z₂ hrel
  have hY : Formalism.L2.SG.CntLocal.ZhatLoc Z.M Z.δ p Z₂ =
      K⁻¹ * Formalism.L2.SG.CntLocal.ZhatLoc Z.M Z.δ p Z₁ * Ml := by
    rw [Matrix.mul_assoc, ← hK, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul K hKu, Matrix.one_mul]

  set Cm : Formalism.L2.SG.LsDatumB.MatP D p := Matrix.of fun a b =>
    if a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS then
      g.e.symm (-(((D.mem u).A.T : ℕ) : (D.s.atP p).Fp) / (g.q : (D.s.atP p).Fp),
        (((D.mem u').A.T : ℕ) : (D.s.atP p).Fp) / (g.q : (D.s.atP p).Fp)) else 0 with hCm
  have hZZ : ∀ X, Formalism.L2.SG.CntLocal.ZZP (M := Z.M) Z.δ u u' p X =
      emap Z p g (Formalism.L2.SG.CntLocal.ZhatLoc Z.M Z.δ p X) - Cm := by
    intro X
    ext a b
    simp only [Formalism.L2.SG.CntLocal.ZZP, Formalism.MainNotions.S.Loc.HermSp.ZZplusOf, hs, emap, hCm, Matrix.sub_apply,
      Matrix.of_apply]
  obtain ⟨hL0, hL1⟩ := lmat_low Z p g hl0low.1 hl0low.2 hM0 hM1
  obtain ⟨hR0, hR1⟩ := lmat_up Z p g hl0low.1 hl0low.2 hM0 hM1
  have hcorner := corner_fix p hL0 hL1 hR0 hR1 (C := Cm) (fun a b h => by
    simp only [hCm, Matrix.of_apply]; rw [if_neg h])
  have hmain : Formalism.L2.SG.CntLocal.ZZP (M := Z.M) Z.δ u u' p Z₂ =
      lmat Z p g K⁻¹ Ml * Formalism.L2.SG.CntLocal.ZZP (M := Z.M) Z.δ u u' p Z₁ * lmat Z p g Ml K⁻¹ := by
    rw [hZZ, hZZ, hY, emap_mul, Matrix.mul_sub, Matrix.sub_mul, hcorner]

  have hKc : K.map (Z.M p).L.cj = Nlᵀ := by
    ext i j
    simp [hKdef, (Z.M p).L.cj_cj]
  have hA : Cq Z p g (Ml - ((K⁻¹).map (Z.M p).L.cj)ᵀ) := by
    have e1 : ((K⁻¹).map (Z.M p).L.cj)ᵀ = Nl⁻¹ := by
      rw [map_cj_inv Z p K hKu, hKc, Matrix.transpose_nonsing_inv, Matrix.transpose_transpose]
    have e2 : Ml - Nl⁻¹ = Nl⁻¹ * (Nl * Ml - 1) := by
      rw [Matrix.mul_sub, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul Nl hNu, Matrix.one_mul, Matrix.mul_one]
    rw [e1, e2]
    exact cq_mul_left Z p g hNiO hcong
  have hB : Cq Z p g (K⁻¹ - (Ml.map (Z.M p).L.cj)ᵀ) := by
    have e1 : Ml * Nl - 1 = Nl⁻¹ * (Nl * Ml - 1) * Nl := by
      rw [Matrix.mul_sub, Matrix.sub_mul, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul Nl hNu, Matrix.one_mul,
        Matrix.mul_one, Matrix.nonsing_inv_mul Nl hNu]
    have h1 : Cq Z p g (Ml * Nl - 1) := by
      rw [e1]; exact cq_mul_right Z p g (cq_mul_left Z p g hNiO hcong) hNO
    have e2 : ((Ml * Nl - 1).map (Z.M p).L.cj)ᵀ = K * (Ml.map (Z.M p).L.cj)ᵀ - 1 := by
      have m1 : (Ml * Nl - 1).map (Z.M p).L.cj = (Ml * Nl).map (Z.M p).L.cj - 1 := by
        ext i j
        rw [Matrix.map_apply, Matrix.sub_apply, Matrix.sub_apply, Matrix.map_apply, map_sub]
        congr 1
        simp only [Matrix.one_apply]
        split_ifs <;> simp
      rw [m1, map_cj_mul, Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul, hKdef]
    have e3 : K⁻¹ - (Ml.map (Z.M p).L.cj)ᵀ = -(K⁻¹ * ((Ml * Nl - 1).map (Z.M p).L.cj)ᵀ) := by
      rw [e2, Matrix.mul_sub, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul K hKu, Matrix.one_mul, Matrix.mul_one,
        neg_sub]
    rw [e3]
    exact cq_neg Z p g (cq_mul_left Z p g hl0O (cq_transpose Z p g (cq_map_cj Z p g h1)))
  have hLint : Formalism.MainNotions.S.TieN.IntLow (Z.M p) (lmat Z p g K⁻¹ Ml) := by
    refine ⟨hL1, hL0, fun a b => ?_⟩
    obtain ⟨o, ho, he⟩ := hB a b
    exact lmat_mem_R Z p g hs (hl0O a b) (hMO b a) ⟨o, ho, by
      rw [← he]; simp [Matrix.sub_apply, Matrix.transpose_apply, Matrix.map_apply]⟩
  have hRint : Formalism.MainNotions.S.TieN.IntUp (Z.M p) (lmat Z p g Ml K⁻¹) := by
    refine ⟨hR1, hR0, fun a b => ?_⟩
    obtain ⟨o, ho, he⟩ := hA a b
    exact lmat_mem_R Z p g hs (hMO a b) (hl0O b a) ⟨o, ho, by
      rw [← he]; simp [Matrix.sub_apply, Matrix.transpose_apply, Matrix.map_apply]⟩
  refine ⟨lmat Z p g K⁻¹ Ml, Formalism.L2.SG.LsDatumB.sgnP p * lmat Z p g Ml K⁻¹ * Formalism.L2.SG.LsDatumB.sgnP p,
    hLint, sgn_conj_intUp Z p hRint, ?_⟩
  rw [hmain]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Formalism.L2.SG.LsDatumB.sgnP p) (Formalism.L2.SG.LsDatumB.sgnP p), permSign_mul_self₂, Matrix.one_mul]

end ModeG3

end Formalism.L2.SG.Pf.FibQ
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocalOrthogonalHolds
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Saturated Formalism.L2.SG.Pf.ScalarFramePf

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open BwdCut BwdBetaCut BwdNP BetaI

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

set_option maxHeartbeats 1000000 in

theorem localOrthogonal_holds : PartialIsometryExtension Zd u u' F0 what₂ := by
  intro γ Z F'₂ φ φ' Λ₂ hB β₀ hβ₀ hfr hW0 hOm p w hw hm hm₂
  have hStar := hB.2.2.1
  have hT2 := hStar.2.1 p
  have hId := hT2.2.2.2.1

  have hwW := OrthogonalLocalComplement.baseChange_mem_W0 Zd p γ hw
  obtain ⟨w₂, hw₂, hs1, hs2⟩ := hId.2.2.1 (baseChange₂ D p w) hwW

  have hzrep : (repF γ).zt = (repF γ).fl.z := hB.2.2.2.2.2.2.1.1.2
  have hwHp : w ∈ Hp γ.lam (lf D F0) (repF γ) := by
    have hle := BwdBetaS.UUE_le_span γ.lam (lf D F0) (repF γ) rfl hzrep
    have hspan : Submodule.span D.host.E (Set.range (Sum.elim (lf D F0).fl.fvec (repF γ).fl.fvec)) =
        F0.Xplus ⊔ (repF γ).fl.Xplus := by
      rw [Set.Sum.elim_range, Submodule.span_union, SpanOmPf.Xplus_eq, SpanOmPf.Xplus_eq]
    rw [hspan] at hle
    show w ∈ orth (VS D) (UUE γ.lam (lf D F0) (repF γ))
    rw [PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth] at hw ⊢
    exact fun x hx => hw x (hle hx)
  obtain ⟨w₂g, hw₂g, hd1, hd2⟩ := hW0 w hwHp

  have hu := OrthogonalLocalComplement.hu_all Zd p
  have hwperp : baseChange₂ D p w ∈ (locH Zd p).perp ((locH Zd p).X (tLoc Zd p γ).f) :=
    baseChange_mem_perp_sup Zd p γ ((PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).2 fun x hx =>
      (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).1 hw x
        (Submodule.mem_sup_left (le_sup_left (a := F0.X) (b := Submodule.span D.host.E {F0.z}) hx)))
  have hw₂perp : w₂ ∈ (locH Zd p).perp ((locH Zd p).X (tLoc Zd p γ).f) := LsDatumA.mem_perp_isotropicSpan_of_mem_framePerp _ hw₂
  have hdiff1 : baseChange₂ D p w - w₂ ∈ (locH Zd p).X (tLoc Zd p γ).f := by
    have h := hs1 ⟨baseChange₂ D p w, hwperp⟩ ⟨w₂, hw₂perp⟩ rfl rfl
    have h1 : (φ p) ((locH Zd p).mkW (tLoc Zd p γ).f ⟨baseChange₂ D p w, hwperp⟩) =
        (locH Zd p).mkW (tLoc Zd p γ).f ⟨w₂, hw₂perp⟩ := by
      have := h
      simp only [one_smul] at this
      exact this
    have e' : ∀ x, (φ p) x = x := fun x => by rw [hStar.2.2 p]; rfl
    exact LsDatumA.sub_mem_X_of_mkW_eq _ ((e' _).symm.trans h1)
  have hdiff2 : baseChange₂ D p w - baseChange₂ D p w₂g ∈ (locH Zd p).X (tLoc Zd p γ).f := by
    rw [← map_sub]
    exact bcP_X Zd p γ hu hd1
  have hdX : w₂ - baseChange₂ D p w₂g ∈ (locH Zd p).X (tLoc Zd p γ).f := by
    have := Submodule.sub_mem _ hdiff2 hdiff1
    rwa [sub_sub_sub_cancel_left] at this
  have hd0 : ∀ a, (locH Zd p).h (w₂ - baseChange₂ D p w₂g) (locF' Zd p F'₂ a) = 0 := by
    intro a
    have h1 : (locH Zd p).h w₂ (locF' Zd p F'₂ a) = 0 :=
      hw₂ _ (Submodule.mem_sup_right (Submodule.subset_span ⟨a, rfl⟩))
    have h2 : (locH Zd p).h (baseChange₂ D p w₂g) (locF' Zd p F'₂ a) = 0 := by
      rw [h_eq, locF'_eq, LocFacts.localForm_smul_right, ← h_eq, localForm_baseChange,
        (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).1 hw₂g _ (OrthogonalLocalComplement.frame_mem_UUE hB.2.2.2.1.1 (lf D F0) F'₂ a),
        map_zero, mul_zero]
    rw [OmL.h_sub_left, h1, h2, sub_zero]
  have hgen := (hB.2.2.2.1.2 p).1
  have hdet : IsUnit ((locH Zd p).Zhat (locF' Zd p F'₂) (tLoc Zd p γ).f).det := by
    have h := hgen.1.2.2.2.1
    rw [OmL.dl_last] at h
    rw [LsDatumA.Zhat_swap, Matrix.det_transpose, ← RingHom.map_det]
    exact h.map _
  have hd : w₂ - baseChange₂ D p w₂g = 0 :=
    OmL.uniq_loc (locH Zd p) (locF' Zd p F'₂) (tLoc Zd p γ).f hdet
      (le_trans (Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨i.castSucc, rfl⟩)) le_rfl hdX) hd0
  have hw₂eq : w₂ = baseChange₂ D p w₂g := sub_eq_zero.1 hd

  have hw₂perp' : w₂ ∈ (locH Zd p).perp ((locH Zd p).X (locF' Zd p F'₂)) := LsDatumA.mem_perp_isotropicSpan_of_mem_framePerp' _ hw₂
  have h := hs2 ⟨baseChange₂ D p w, hm⟩ ⟨w₂, hw₂perp'⟩ rfl rfl
  have h' : (φ' p) ((locH Zd p).mkW (tLoc Zd p γ).f' ⟨baseChange₂ D p w, hm⟩) =
      (locH Zd p).mkW (locF' Zd p F'₂) ⟨w₂, hw₂perp'⟩ := by
    have := h
    simp only [one_smul] at this
    exact this
  rw [h']
  apply Submodule.Quotient.eq _ |>.2
  show w₂ - baseChange₂ D p (β₀ w) ∈ (locH Zd p).X (locF' Zd p F'₂)
  rw [hw₂eq, ← map_sub, show w₂g - β₀ w = -(β₀ w - w₂g) by abel, map_neg]
  exact Submodule.neg_mem _ (bcP_X' Zd p F'₂ hd2)

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXFrameVol
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.LocVol

namespace Formalism.L2.SG.Pf.MassDataX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem three_dvd_cubic (r : ℕ) : 3 ∣ (r + 1) * (8 * r ^ 2 + 10 * r + 3) := by

  obtain ⟨k, hk | hk | hk⟩ : ∃ k, r = 3 * k ∨ r = 3 * k + 1 ∨ r = 3 * k + 2 := ⟨r / 3, by omega⟩
  · subst hk
    exact ⟨(3 * k + 1) * (6 * k + 1) * (4 * k + 1), by ring⟩
  · subst hk
    exact ⟨(3 * k + 2) * (2 * k + 1) * (12 * k + 7), by ring⟩
  · subst hk
    exact ⟨(k + 1) * (8 * (3 * k + 2) ^ 2 + 10 * (3 * k + 2) + 3), by ring⟩

variable {D : D7} (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (Y : Full X) (u u' : D.what₂.Word)
  (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) (sd C Th : ℝ)
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
  (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
  (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)

theorem frameVolAt_of (hψ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF X.B.I.F ψ) (hstd : IsStdChar ψ) (hP : ProdConv X u u' ψ) :
    Formalism.L2.SG.NGAnalytic.MassDataLemmas.FrameVolAt X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq := by
  have hMS := Formalism.L2.S.Pv.MSTypP.lemmaMSStd_holds X u u' ψ hψ hstd hP
  have hZZ : 0 < (locOf X u u' ψ).volZZ := hP.2.2.2.2.2.2.1
  unfold Formalism.L2.SG.NGAnalytic.MassDataLemmas.FrameVolAt
  show ((locOf X u u' ψ).localVolumeArchimedean * ∏ p, (locOf X u u' ψ).localVolumeAtPlace p) / (locOf X u u' ψ).volZZ = _
  unfold Formalism.L2.SG.Pf.Carrier.EnergyConst.LemmaMS at hMS
  rw [hMS, mul_div_assoc, div_self hZZ.ne', mul_one]
  have hv : 2 * D.host.v = D.host.rdE := by unfold Formalism.BasicNotions.Host.v; ring
  have he : (((D.R.f * (D.R.rS + 1) * (8 * D.R.rS ^ 2 + 10 * D.R.rS + 3) : ℕ) : ℝ) / 3) =
      ((D.R.f * Formalism.L2.SG.Pf.Carrier.EnergyConst.e1 D : ℕ) : ℝ) := by
    unfold Formalism.L2.SG.Pf.Carrier.EnergyConst.e1
    obtain ⟨c, hc⟩ := three_dvd_cubic D.R.rS
    rw [mul_assoc, hc, Nat.mul_div_cancel_left _ (by norm_num : 0 < 3)]
    push_cast
    ring
  have hg : (X.B.g : ℝ) = ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ) := by rw [X.g_eq]; simp [Formalism.MainNotions.S.Lat.gS]
  rw [hv, he, Real.rpow_natCast, hg, mul_assoc D.R.f]

end Formalism.L2.SG.Pf.MassDataX
end
end

