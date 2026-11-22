import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0049
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RepresentationIndependence.FrameOKMap
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0048
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0037
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0039
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0041
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0042
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0050
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NOfibAlg
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0044
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0043
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NOfibLatF
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0047

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.CntIso
section
open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 2000000 in
open PI.RepsIndep.Tr in
theorem ci_EZ_map {D : Formalism.BasicNotions.D7} {β : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hβ : β ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    {T T' : D.host.E} {F0 : FlagG (VS D) D.R.rS T} {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    {Z : MatZ D} {F' : LFlag (VS D) D.R.rS T'} (h : F' ∈ EZ T' F0 Λ Z) :
    mapL β hβ F' ∈ EZ T' (mapF β hβ F0) (Formalism.HermitianLatticesTheory.gmap β Λ) Z := by
  have hlf : lf D (mapF β hβ F0) = mapL β hβ (lf D F0) := lflag_ext rfl rfl
  unfold EZ at h ⊢
  rw [Set.mem_setOf_eq] at h ⊢
  rw [hlf]
  obtain ⟨⟨hL, ⟨ξ, hξ⟩, hG⟩, hA, hGen, hF, hZ⟩ := h
  have hG' : Gval (mapL β hβ (lf D F0)) (mapL β hβ F') ≠ 0 := by
    show Formalism.MainNotions.S.Gflag (mapF β hβ F0) (mapF β hβ F'.fl) ≠ 0
    simp only [Formalism.MainNotions.S.Gflag, Formalism.MainNotions.S.Dl, Zhat_mapF hβ]
    exact hG
  have hZ' : ZhatL (mapL β hβ (lf D F0)) (mapL β hβ F') = Z := by
    show Formalism.MainNotions.S.Zhat (mapF β hβ F0) (mapF β hβ F'.fl) = Z
    rw [Zhat_mapF hβ]
    exact hZ
  exact ⟨⟨IsLift_map hβ hL, ⟨ξ, AdmWit_map hβ hξ⟩, hG'⟩, AdmWit_map hβ hA, IsGeneric_map hβ hGen,
    FrameOK_map hβ hF, hZ'⟩

set_option maxHeartbeats 2000000 in
open PI.RepsIndep.Tr in
theorem ci_rel_map {D : Formalism.BasicNotions.D7} {β : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hβ : β ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    {T T' : D.host.E} {F0 : FlagG (VS D) D.R.rS T} {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    {F' F'' : LFlag (VS D) D.R.rS T'} (h : NilradicalFlagMoved F0 Λ F' F'') :
    NilradicalFlagMoved (mapF β hβ F0) (Formalism.HermitianLatticesTheory.gmap β Λ) (mapL β hβ F') (mapL β hβ F'') := by
  have hlf : lf D (mapF β hβ F0) = mapL β hβ (lf D F0) := lflag_ext rfl rfl
  obtain ⟨n, ⟨hnL, hne, hnz⟩, h1, h2⟩ := h
  have hN : conj β n ∈ NLam (Formalism.HermitianLatticesTheory.gmap β Λ) (lf D (mapF β hβ F0)) := by
    rw [hlf]; exact NLam_conj hβ hnL
  refine ⟨conj β n, ⟨hN, fun a => ?_, ?_⟩, fun a => ?_, ?_⟩
  · show β (n (β.symm (β (F0.e a)))) = β (F0.e a)
    rw [LinearEquiv.symm_apply_apply, hne]
  · show β (n (β.symm (β F0.z))) = β F0.z
    rw [LinearEquiv.symm_apply_apply, hnz]
  · show β (n (β.symm (β (F'.fl.e a)))) = β (F''.fl.e a)
    rw [LinearEquiv.symm_apply_apply, h1]
  · show β (n (β.symm (β F'.fl.z))) = β F''.fl.z
    rw [LinearEquiv.symm_apply_apply, h2]

open PI.RepsIndep.Tr in
theorem ci_mapF_symm {D : Formalism.BasicNotions.D7} {β : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hβ : β ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) : mapF β.symm (iso_symm hβ) (mapF β hβ F0) = F0 :=
  flag_ext (funext fun a => LinearEquiv.symm_apply_apply β (F0.e a)) (LinearEquiv.symm_apply_apply β F0.z)

open PI.RepsIndep.Tr in
theorem counting_iso_inverse : CntIsoInv := by
  intro D β hβ T T' F0 Λ Z
  have hβ' := iso_symm hβ
  have hΛ : Formalism.HermitianLatticesTheory.gmap β.symm (Formalism.HermitianLatticesTheory.gmap β Λ) = Λ := gmap_symm_gmap β Λ
  have hF : Formalism.L2.SG.Saturated.mapFlag β hβ F0 = mapF β hβ F0 := flag_ext rfl rfl
  rw [hF]
  show Formalism.MainNotions.S.Cnt.cntCl (EZ T' (mapF β hβ F0) (Formalism.HermitianLatticesTheory.gmap β Λ) Z) (NilradicalFlagMoved (mapF β hβ F0) (Formalism.HermitianLatticesTheory.gmap β Λ)) =
    Formalism.MainNotions.S.Cnt.cntCl (EZ T' F0 Λ Z) (NilradicalFlagMoved F0 Λ)
  refine cntCl_equiv (mapL β hβ) (mapL β.symm hβ') (mapL_symm hβ) (mapL_symm' hβ hβ') _ _ _ _
    (fun F' => ⟨fun h => ?_, fun h => ci_EZ_map hβ h⟩) (fun F' F'' => ⟨fun h => ?_, fun h => ci_rel_map hβ h⟩)
  · have e := ci_EZ_map hβ' h
    rw [mapL_symm hβ, ci_mapF_symm hβ, hΛ] at e
    exact e
  · have e := ci_rel_map hβ' h
    rw [mapL_symm hβ, mapL_symm hβ, ci_mapF_symm hβ, hΛ] at e
    exact e

end Formalism.L2.SG.Pf.Cnt
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FormulaCHolds
section
namespace Formalism.L2.SG.Pf.Cnt

theorem densAll_of_leaves (hF : DualityBasisChange.FrameBasisL) (hη : EtaLocD) : DensAll :=
  densAll_of' local_self_dual_holds (DualityBasisChange.gaPlusDiag_of hF jordan_decomposition_holds)
    (DualityBasisChange.notIntDens_of_steps local_self_dual_holds hF DualityBasisChange.locGlobIntE) (densProdVal_of hη)

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem formulaC_holds_of (hF : DualityBasisChange.FrameBasisL) (hη : EtaLocD) (hI : CntIsoInv) : Formalism.L2.SG.PoincareAmplitudeLowerBounds.FormulaC :=
  formulaC_of local_self_dual_holds (DualityBasisChange.gaPlusDiag_of hF jordan_decomposition_holds)
    (DualityBasisChange.notIntDens_of_steps local_self_dual_holds hF DualityBasisChange.locGlobIntE) (densProdVal_of hη)
    (densMultInt_of local_self_dual_holds (DualityBasisChange.gaPlusDiag_of hF jordan_decomposition_holds) (densProdVal_of hη))
    (orbitFiniteR_of hI) lattice_exists_holds

end Formalism.L2.SG.Pf.Cnt
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NOfibAsm
section
namespace Formalism.L2.SG.Pf.NcReal.JX.NOf

theorem nofibLat_of_rest (hL : DictLat) (hE : DictEx) (hF : FibQ) (hO : FibOnto) : NOfibLat := by
  have hR : NOratC := by first | exact @noratC_holds | exact @noratC_proved | exact @noratC | exact @nOratC_holds | exact @noratC_of | exact @NOratC_holds
  have hG : DictGram := by first | exact @dictGram_holds | exact @dictGram_proved | exact @dictGram | exact @DictGram_holds | exact @dictGram_of
  have hP : DictPlace := by first | exact @dictionary_place_holds | exact @dictPlace_holds | exact @dictPlace_proved | exact @dictPlace | exact @DictPlace_holds | exact @dictPlace_of
  exact @nofibLat_of hR hG hL hE hP hF hO

theorem nofib_of_rest (hL : DictLat) (hE : DictEx) (hF : FibQ) (hO : FibOnto) : NOfib := @Formalism.L2.SG.Pf.NcReal.JX.nofib_of (@nofibLat_of_rest hL hE hF hO)

theorem nOfib_of_dict_fib (hB : DictLatB) (hF : FibQ) (hO : FibOnto) : NOfib := by
  have hLF : DictLatF := by first | exact @dictLatF_proof | exact @dictLatF_holds | exact @dictLatF_proved | exact @dictLatF | exact @DictLatF_holds | exact @dictLatF_of
  have hL : DictLat := @dictLat_of hLF hB
  have hE : DictEx := @Ex.dictEx_holds
  exact @nofib_of_rest hL hE hF hO

theorem nofib_of_fib (hF : FibQ) (hO : FibOnto) : NOfib := by
  have hB : DictLatB := by first | exact @dictLatB_proof | exact @dictLatB_holds | exact @dictLatB_proved | exact @dictLatB | exact @DictLatB_holds | exact @dictLatB_of
  exact @nOfib_of_dict_fib hB hF hO

theorem nofib_of_fibQ (hF : FibQ) : NOfib := by
  have hO : FibOnto := by first | exact @fibOnto_proof | exact @fibOnto_holds | exact @fibOnto_proved | exact @fibOnto | exact @FibOnto_holds | exact @fibOnto_of
  exact @nofib_of_fib hF hO

end Formalism.L2.SG.Pf.NcReal.JX.NOf
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ThetaIntMem
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Matrix

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.S Formalism.L2.SG.Pf.NcReal.JX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem theta_int_mem {I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E} {x : D.host.E} (hx : x ∈ I) :
    x * theta D ∈ I := by
  unfold theta
  split_ifs with h
  · obtain ⟨hint, -⟩ := h.choose_spec
    have hmem : (⟨h.choose, hint⟩ : 𝓞 D.host.E) • x ∈ (I : Submodule (𝓞 D.host.E) D.host.E) :=
      Submodule.smul_mem _ _ hx
    rwa [Algebra.smul_def, mul_comm] at hmem
  · rw [mul_zero]
    exact (I : Submodule (𝓞 D.host.E) D.host.E).zero_mem

theorem inW_sub {X : HidaSetting D} {x y : (VS D).V} (hx : InW X x) (hy : InW X y) : InW X (x - y) := by
  intro c
  obtain ⟨h1, h2⟩ := hx c
  obtain ⟨h3, h4⟩ := hy c
  exact ⟨by rw [map_sub, h1, h3, sub_zero], by rw [map_sub, h2, h4, sub_zero]⟩

theorem xblk {X : HidaSetting D} (u : D.what₂.Word) (X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E)
    (xs : Fin D.R.rS → (VS D).V) (M : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E)
    (p : Formalism.L2.SG.Pf.LsNc5.LtPair D.R.rS) :
    blkQ X u X0 xs M (Sum.inl (Sum.inl p)) - tauQ X u (Sum.inl (Sum.inl p)) (blkQ X u X0 xs M) =
      embV X (X0 p.1.1 p.1.2) := by
  simp only [blkQ, tauQ]
  first | exact sub_zero _ | rfl | simp

theorem rblk {X : HidaSetting D} (u : D.what₂.Word) (X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E)
    (xs : Fin D.R.rS → (VS D).V) (M : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (b : Fin D.R.rS) :
    blkQ X u X0 xs M (Sum.inl (Sum.inr b)) - tauQ X u (Sum.inl (Sum.inr b)) (blkQ X u X0 xs M) =
      rowV X u (xs b) := by
  simp only [blkQ, tauQ]
  first | exact sub_zero _ | rfl | simp

theorem fibQ_holds : FibQ := by
  intro D X u X0 xs M hok
  have hup := hok.1
  have hd := hok.2.1
  have hW := hok.2.2.1
  constructor
  · intro h

    have hX : ∀ b a : Fin D.R.rS, b < a → X0 b a ∈ iQ D b a := by
      intro b a hba
      have h1 := h (Sum.inl (Sum.inl ⟨(b, a), hba⟩))
      rw [xblk] at h1
      simp only [cLat] at h1
      obtain ⟨t, ht, hte⟩ := (CovB.mem_closure_embV X _ _).1 h1
      have : t = X0 b a := CovB.embVHom_injective X hte
      rw [← this]; exact ht

    have hR : ∀ b, xs b ∈ aaLb X b := by
      intro b
      have h1 := h (Sum.inl (Sum.inr b))
      rw [rblk] at h1
      simp only [cLat] at h1
      obtain ⟨y, hy, hye⟩ := (mem_cl_row X u b _).1 h1
      have hz : rowV X u (xs b - y) = 0 := by rw [rowV_sub, hye, sub_self]
      have := rowV_inj X u _ (inW_sub (hW b) (aaLb_inW X hy)) hz
      rw [sub_eq_zero] at this
      rw [this]; exact hy
    have hG := Gp_mem X X0 xs hup hd hX hR
    refine ⟨hX, hR, ?_⟩

    have hMu : ∀ b a : Fin D.R.rS, b < a → M b a ∈ iP D b a := by
      intro b a hba
      have h1 := h (Sum.inr (Sum.inl ⟨(b, a), hba⟩))
      rw [kblk X u hok] at h1
      simp only [cLat] at h1
      obtain ⟨t, ht, hte⟩ := (CovB.mem_closure_embV X _ _).1 h1
      have : t = M b a := CovB.embVHom_injective X hte
      rw [← this]; exact ht
    intro b a
    rcases lt_trichotomy b a with hba | hba | hba
    · exact hMu b a hba
    · subst hba
      have h1 := h (Sum.inr (Sum.inr b))
      rw [imblk X u hok] at h1
      obtain ⟨t, ht, htc, hte⟩ := (mem_cl_im X u b _).1 h1
      have hteq : t = xiA X0 xs M b := im_inj X htc (xiA_conj X hok b) fun v => congrFun hte v
      have hxi : xiA X0 xs M b ∈ iP D b b := by rw [← hteq]; exact ht
      have e : M b b = xiA X0 xs M b - Gp D X0 xs b b * theta D := by unfold xiA; ring
      rw [e]
      exact Submodule.sub_mem _ hxi (theta_int_mem (hG b b))
    · have e := entry_rel X hok b a
      have e2 : M b a = -Gp D X0 xs b a - star (M a b) := by rw [← e]; ring
      rw [e2]
      refine Submodule.sub_mem _ (Submodule.neg_mem _ (hG b a)) ?_
      have hab : M a b ∈ iP D b a := by rw [iP_comm]; exact hMu a b hba
      exact star_mem_iP hab
  · rintro ⟨hX, hR, hM⟩
    have hG := Gp_mem X X0 xs hup hd hX hR
    intro p
    rcases p with ((p | b) | (p | a))
    · rw [xblk]
      simp only [cLat]
      exact (CovB.mem_closure_embV X _ _).2 ⟨X0 p.1.1 p.1.2, hX _ _ p.2, rfl⟩
    · rw [rblk]
      simp only [cLat]
      exact (mem_cl_row X u b _).2 ⟨xs b, hR b, rfl⟩
    · rw [kblk X u hok]
      simp only [cLat]
      exact (CovB.mem_closure_embV X _ _).2 ⟨M p.1.1 p.1.2, hM _ _, rfl⟩
    · rw [imblk X u hok]
      refine (mem_cl_im X u a _).2 ⟨xiA X0 xs M a, ?_, xiA_conj X hok a, rfl⟩
      exact Submodule.add_mem _ (hM a a) (theta_int_mem (hG a a))

end Formalism.L2.SG.Pf.NcReal.JX.NOf
end
end

