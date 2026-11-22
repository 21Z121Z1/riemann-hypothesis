import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0065
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0058
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarOmLocPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0051
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0045
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0009
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqClass
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0049
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0066
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0026
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0067

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBetaRat
section
noncomputable section

open scoped Classical
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Saturated
  Formalism.L2.SG.Pf.ScalarFramePf

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

open BwdCut BwdBetaCut OmP BwdBetaS

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

variable (u u' F0 what₂)

set_option maxHeartbeats 1000000 in

theorem betaRat_holds : BetaRat Zd u u' F0 what₂ := by
  intro γ Z F'₂ φ φ' Λ₂ hB
  obtain ⟨hC, hCtx, hS, -, -, hTH, hPD, hGv⟩ := hB
  obtain ⟨hZd, hZ₁d', hx'⟩ := starMinors_holds u u' F0 what₂ γ Z hCtx
  have hZ : ZhatL (lf D F0) F'₂ = Z := hS.1
  have hrow := hC.2.1.1 γ.lam γ.mem
  have hΛ : Submodule.IsLattice D.host.E γ.lam := hrow.2.1.1
  have hLlf : IsLift γ.lam (lf D F0) := hrow.2.1.2.2.1
  have hLrep : IsLift γ.lam (repF γ) := hPD.1
  set f := frame (lf D F0) with hf
  set g := frame (repF γ) with hg
  set F₂ := F'₂.fl with hF₂
  set Z₁ := starZh f g with hZ₁
  have hlm : ∀ l, leadMinorE Z₁ l = leadMinorE (starZh f (starFrame γ)) l := fun l => (star_frame_lead_minor γ l).symm
  have hZ₁d : Z₁.det ≠ 0 := by
    rw [← FsLA.leadMinorE_full, hlm, FsLA.leadMinorE_full]; exact hZ₁d'
  have hx : leadMinorE Z₁ D.R.rS * Z.det = leadMinorE Z D.R.rS * Z₁.det := by
    rw [hlm, ← FsLA.leadMinorE_full Z₁, hlm, FsLA.leadMinorE_full]; exact hx'
  have hfF : f = F0.fvec := rfl
  have hZe : ∀ a b, (VS D).hT (f a) (F₂.fvec b) = Z a b := fun a b => by rw [← hZ]; rfl
  have hg2 : FsLA.gram (VS D) f F₂.fvec = Zᴴ := by
    refine Matrix.ext fun i j => ?_
    simp only [FsLA.gram, Matrix.conjTranspose_apply]
    rw [← hZe, ← (LinearMap.isSymm_def.1 (VS D).herm) (f j) (F₂.fvec i), starRingEnd_apply]
  have h1g : ∀ a b, (a ≠ Fin.last D.R.rS ∨ b ≠ Fin.last D.R.rS) → (VS D).hT (g a) (g b) = 0 :=
    fun a b h => FsLA.gram_fvec_zero (repF γ).fl a b h
  have h2g : (VS D).hT (g (Fin.last D.R.rS)) (g (Fin.last D.R.rS)) = -((Tu D u' : ℕ) : D.host.E) :=
    FsLA.gram_fvec_last (repF γ).fl
  have h1f : ∀ a b, (a ≠ Fin.last D.R.rS ∨ b ≠ Fin.last D.R.rS) → (VS D).hT (f a) (f b) = 0 :=
    fun a b h => FsLA.gram_fvec_zero F0 a b h
  have h2f : (VS D).hT (f (Fin.last D.R.rS)) (f (Fin.last D.R.rS)) = -CntLocal.Tn u := FsLA.gram_fvec_last F0
  have hdZ1h : Z₁ᴴ.det ≠ 0 := by rw [Matrix.det_conjTranspose]; exact star_ne_zero.2 hZ₁d
  have hdg2 : (FsLA.gram (VS D) f F₂.fvec).det ≠ 0 := by
    rw [hg2, Matrix.det_conjTranspose]; exact star_ne_zero.2 hZd
  have hx2 : leadMinorE (FsLA.gram (VS D) f F₂.fvec) D.R.rS * Z₁ᴴ.det =
      leadMinorE Z₁ᴴ D.R.rS * (FsLA.gram (VS D) f F₂.fvec).det := by
    rw [hg2, FsLA.lm_conjTranspose, FsLA.lm_conjTranspose, Matrix.det_conjTranspose, Matrix.det_conjTranspose,
      ← star_mul', ← star_mul', mul_comm (leadMinorE Z D.R.rS), hx, mul_comm]
  obtain ⟨F₃, hZ3, hom3, hsp3⟩ := FsLA.frame_la F₂ f h1f h2f Z₁ᴴ hdZ1h hdg2 hx2
  set h := F₃.fvec with hh
  set uu := Sum.elim f g with huu
  set uu' := Sum.elim h F₂.fvec with huu'
  set ww := Sum.elim f F₂.fvec with hww
  have hZ3e : ∀ a b, (VS D).hT (F₂.fvec a) (h b) = Z₁ᴴ a b := fun a b => congrFun (congrFun hZ3 a) b
  have k1 : ∀ a b, (VS D).hT (h a) (h b) = (VS D).hT (f a) (f b) := by
    intro a b
    by_cases hab : a ≠ Fin.last D.R.rS ∨ b ≠ Fin.last D.R.rS
    · exact (FsLA.gram_fvec_zero F₃ a b hab).trans (FsLA.gram_fvec_zero F0 a b hab).symm
    · push_neg at hab
      rw [hab.1, hab.2]
      exact (FsLA.gram_fvec_last F₃).trans (FsLA.gram_fvec_last F0).symm
  have k2 : ∀ a b, (VS D).hT (h a) (F₂.fvec b) = (VS D).hT (f a) (g b) := by
    intro a b
    rw [← (LinearMap.isSymm_def.1 (VS D).herm) (F₂.fvec b) (h a), hZ3e, starRingEnd_apply,
      Matrix.conjTranspose_apply, star_star]
    rfl
  have k3 : ∀ a b, (VS D).hT (F₂.fvec a) (h b) = (VS D).hT (g a) (f b) := by
    intro a b
    rw [hZ3e, Matrix.conjTranspose_apply, ← starRingEnd_apply]
    exact (LinearMap.isSymm_def.1 (VS D).herm) (f b) (g a)
  have k4 : ∀ a b, (VS D).hT (F₂.fvec a) (F₂.fvec b) = (VS D).hT (g a) (g b) := by
    intro a b
    by_cases hab : a ≠ Fin.last D.R.rS ∨ b ≠ Fin.last D.R.rS
    · exact (FsLA.gram_fvec_zero F₂ a b hab).trans (h1g a b hab).symm
    · push_neg at hab
      rw [hab.1, hab.2]
      exact (FsLA.gram_fvec_last F₂).trans h2g.symm
  have hGr : FsLA.gram (VS D) uu' uu' = FsLA.gram (VS D) uu uu := by
    refine Matrix.ext fun i j => ?_
    rcases i with a | a <;> rcases j with b | b
    · exact k1 a b
    · exact k2 a b
    · exact k3 a b
    · exact k4 a b
  have hGg : (FsLA.gram (VS D) g F0.fvec).det * star (FsLA.gram (VS D) g F0.fvec).det -
      CntLocal.Tn u * ((Tu D u' : ℕ) : D.host.E) *
        (leadMinorE (FsLA.gram (VS D) g F0.fvec) D.R.rS * star (leadMinorE (FsLA.gram (VS D) g F0.fvec) D.R.rS))
        ≠ 0 := by
    rw [← FsLA.leadMinorE_full]; exact hGv
  have hdet : (FsLA.gram (VS D) uu uu).det ≠ 0 := FsLA.gram_pair_det F0 g h1g h2g hZ₁d hGg
  have hGZ : Gflag F0 F₂ ≠ 0 := hTH.1.2.2
  have hGg₂ : (FsLA.gram (VS D) F₂.fvec F0.fvec).det * star (FsLA.gram (VS D) F₂.fvec F0.fvec).det -
      CntLocal.Tn u * ((Tu D u' : ℕ) : D.host.E) *
        (leadMinorE (FsLA.gram (VS D) F₂.fvec F0.fvec) D.R.rS *
          star (leadMinorE (FsLA.gram (VS D) F₂.fvec F0.fvec) D.R.rS)) ≠ 0 := by
    rw [← FsLA.leadMinorE_full]; exact hGZ
  have hdetZ : (Zhat F0 F₂).det ≠ 0 := by
    have e : Zhat F0 F₂ = Z := hZ
    rw [e]; exact hZd
  have hdetw : (FsLA.gram (VS D) ww ww).det ≠ 0 :=
    FsLA.gram_pair_det F0 F₂.fvec (fun a b hab => FsLA.gram_fvec_zero F₂ a b hab) (FsLA.gram_fvec_last F₂)
      hdetZ hGg₂
  have hsp : ∀ i, uu' i ∈ Submodule.span D.host.E (Set.range ww) := by
    have hsub : Set.range (Sum.elim F₂.fvec f) ⊆ Submodule.span D.host.E (Set.range ww) := by
      rintro _ ⟨k, rfl⟩
      rcases k with b | a
      · exact Submodule.subset_span ⟨Sum.inr b, rfl⟩
      · exact Submodule.subset_span ⟨Sum.inl a, rfl⟩
    intro i
    rcases i with a | b
    · exact Submodule.span_le.2 hsub (hsp3 a)
    · exact Submodule.subset_span ⟨Sum.inr b, rfl⟩

  have hdetγ : (Zhat F0 (repF γ).fl).det ≠ 0 := hZ₁d
  obtain ⟨Ω₂, hΩ₂⟩ := exists_om F0 F₂ hdetZ
  obtain ⟨Ωγ, hΩγ⟩ := exists_om F0 (repF γ).fl hdetγ
  have hΩd : Ω₂ - Ωγ ∈ Xsp (lf D F0) :=
    omega_local_holds Zd u u' F0 what₂ hC.2.1 γ Z hCtx F'₂ φ φ' hS hdetγ hZd Ω₂ Ωγ hΩ₂ hΩγ

  have hXq : ∀ y, (∀ k, (VS D).hT (uu k) y = 0) → FsLA.lin ww (FsLA.pc ww y) ∈ F0.X := by
    intro y hy
    have hrem := fun z hz => (FsLA.hT_span_rem ww hdetw y z hz).1
    have hyU : ∀ z ∈ Submodule.span D.host.E (Set.range uu), (VS D).hT z y = 0 :=
      NMoveP.spanL (VS D) uu y hy
    refine BRat.key_X F0 F₂ hdetZ hΩ₂ hGZ (FsLA.lin_sub ww _) (fun a => ?_) ?_
    · have e := hrem (f a) (Submodule.subset_span ⟨Sum.inl a, rfl⟩)
      rw [map_sub, sub_eq_zero] at e
      rw [← e]
      exact hy (Sum.inl a)
    · have e := hrem Ω₂ (Submodule.span_mono (Set.range_comp_subset_range Sum.inr ww) hΩ₂.1)
      rw [map_sub, sub_eq_zero] at e
      rw [← e]
      have e2 : Ω₂ = Ωγ + (Ω₂ - Ωγ) := by abel
      rw [e2, map_add, LinearMap.add_apply]
      have h1 : (VS D).hT Ωγ y = 0 :=
        hyU _ (Submodule.span_mono (Set.range_comp_subset_range Sum.inr uu) hΩγ.1)
      have hXu : ∀ x ∈ Xsp (lf D F0), x ∈ Submodule.span D.host.E (Set.range uu) := by
        intro x hx
        refine Submodule.span_le.2 ?_ hx
        rintro _ ⟨i, rfl⟩
        exact Submodule.subset_span ⟨Sum.inl i.castSucc, by simp [huu, hf, frame, FlagG.fvec]⟩
      rw [h1, hyU _ (hXu _ hΩd), add_zero]
  have hkey : ∀ y y', (∀ k, (VS D).hT (uu k) y = 0) → (∀ k, (VS D).hT (uu k) y' = 0) →
      (VS D).hT (FsLA.lin ww (FsLA.pc ww y)) (FsLA.lin ww (FsLA.pc ww y')) = 0 :=
    fun y y' hy hy' => NMoveP.hT_X_X F0 (hXq y hy) (hXq y' hy')
  obtain ⟨β, hiso, hβu, hβy⟩ := BRat.isometry_extension_two uu uu' ww hGr hdet hdetw hsp hkey
  refine ⟨β, hiso, fun b => hβu (Sum.inr b), fun w0 hw0 => ?_, ?_⟩
  ·
    have hw0u : ∀ k, (VS D).hT (uu k) w0 = 0 := fun k =>
      (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).1 hw0 _
        (PI.PairCorankPos.W.frame_mem_UUE γ.lam hΛ (lf D F0) (repF γ) hLlf hLrep k)
    refine ⟨β w0, ?_, ?_, by rw [sub_self]; exact zero_mem _⟩
    · refine (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).2 fun x hx => ?_
      have hxw : x ∈ Submodule.span D.host.E (Set.range ww) :=
        UUE_le_span Λ₂ (lf D F0) (liftF F'₂) rfl rfl hx
      rw [hβy w0 hw0u]
      exact (FsLA.hT_span_rem ww hdetw w0 x hxw).1
    · rw [hβy w0 hw0u, sub_sub_cancel]
      exact hXq w0 hw0u
  ·
    have homf : FsLA.om (VS D) F₂.fvec f = starOmL f (frame F'₂) := by
      rw [FsLA.om, hg2, ← Matrix.adjugate_conjTranspose]
      simp only [starOmL, Matrix.conjTranspose_apply]
      rw [← hZ]
      rfl
    have homh : FsLA.om (VS D) F₂.fvec h = β (starOmL f g) := by
      simp only [FsLA.om, starOmL, map_sum, map_smul]
      have e : FsLA.gram (VS D) h F₂.fvec = Z₁ᴴ := hZ3
      rw [e]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Matrix.adjugate_conjTranspose, Matrix.conjTranspose_apply]
      congr 1
      exact (hβu (Sum.inl a)).symm
    have e1 : Z₁ᴴ.det = star Z₁.det := Matrix.det_conjTranspose _
    have e2 : (FsLA.gram (VS D) f F₂.fvec).det = star Z.det := by rw [hg2, Matrix.det_conjTranspose]
    rw [e1, e2, homf, homh] at hom3
    have hD1 : GDl (frame (lf D F0)) (frame (repF γ)) (D.R.rS + 1) = Z₁.det := by rw [GDl_top']; rfl
    have hD2 : GDl (frame (lf D F0)) (frame (liftF F'₂)) (D.R.rS + 1) = Z.det := by
      rw [GDl_top']; rw [← hZ]; rfl
    have hO1 : Gom (frame (lf D F0)) (frame (repF γ)) = starOmL f g := rfl
    have hO2 : Gom (frame (lf D F0)) (frame (liftF F'₂)) = starOmL f (frame F'₂) := rfl
    unfold OmB
    rw [hD1, hD2, hO1, hO2]
    have := (Xsp (liftF F'₂)).neg_mem hom3
    rw [neg_sub] at this
    exact this

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarCohPfF
section
noncomputable section

open ValuativeRel

namespace Formalism.MainNotions.S.Loc.HermSp.CohU

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V}

theorem gdet_ne_of_ratio {r : ℕ} {f f₁ f₂ : Fin (r + 1) → V} {T T' : F} (h1G : H.Gdet f f₁ T T' ≠ 0)
    (h2u : IsUnit (H.Dl f f₂ (r + 1)))
    (hrat : H.Dl f f₁ r * H.Dl f f₂ (r + 1) = H.Dl f f₂ r * H.Dl f f₁ (r + 1)) : H.Gdet f f₂ T T' ≠ 0 := by
  intro h0
  apply h1G
  have hr' := congrArg M.L.cj hrat
  simp only [map_mul] at hr'
  have key : H.normE (H.Dl f f₁ (r + 1)) * H.Gdet f f₂ T T' =
      H.normE (H.Dl f f₂ (r + 1)) * H.Gdet f f₁ T T' := by
    unfold HermSp.Gdet HermSp.normE
    linear_combination (algebraMap F E (T * T') * (M.L.cj (H.Dl f f₁ r) * M.L.cj (H.Dl f f₂ (r + 1)))) * hrat +
      (algebraMap F E (T * T') * H.Dl f f₂ r * H.Dl f f₁ (r + 1)) * hr'
  rw [h0, mul_zero] at key
  have hu : IsUnit (H.normE (H.Dl f f₂ (r + 1))) := h2u.mul (h2u.map M.L.cj)
  exact (hu.mul_right_eq_zero).1 key.symm

end Formalism.MainNotions.S.Loc.HermSp.CohU

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open CohCut

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem gdl_full (x y : Fin (D.R.rS + 1) → (VS D).V) :
    Formalism.L2.SG.Pf.ScalarFramePf.GDl x y (D.R.rS + 1) = (Formalism.L2.SG.Pf.ScalarFramePf.GZ x y).det := by
  unfold Formalism.L2.SG.Pf.ScalarFramePf.GDl
  rw [dif_pos le_rfl]
  have hc : (Fin.castLE (le_refl (D.R.rS + 1)) : Fin (D.R.rS + 1) → Fin (D.R.rS + 1)) = id :=
    funext fun i => Fin.ext rfl
  rw [hc, Matrix.submatrix_id_id]

theorem local_discriminant_unit_of_det (p : PlF D) (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D)
    (F'₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (hZ : ZhatL (lf D F0) F'₂ = Z) (hdet : Z.det ≠ 0) :
    IsUnit ((locH Zd p).Dl (tLoc Zd p γ).f (locF' Zd p F'₂) (D.R.rS + 1)) := by
  have e : (locH Zd p).Dl (tLoc Zd p γ).f (locF' Zd p F'₂) (D.R.rS + 1) =
      (∏ i : Fin (D.R.rS + 1), (Zd.M p).L.cj (sgnP D p (Fin.castLE le_rfl i) * frFac Zd.δ p (Fin.castLE le_rfl i))) *
        (∏ i : Fin (D.R.rS + 1), (sgnP' D p (Fin.castLE le_rfl i) * frFac Zd.δ p (Fin.castLE le_rfl i))) *
        (D.s.atP p).ιE (Formalism.L2.SG.Pf.ScalarFramePf.GDl (frame (lf D F0)) (frame F'₂) (D.R.rS + 1)) :=
    Formalism.L2.SG.Pf.ScalarFramePf.dl_loc (Z := Zd) (p := p) (frame (lf D F0)) (frame F'₂)
      (fun a => sgnP D p a * frFac Zd.δ p a) (fun b => sgnP' D p b * frFac Zd.δ p b) (D.R.rS + 1) le_rfl
  rw [e]
  have hGZ : Formalism.L2.SG.Pf.ScalarFramePf.GZ (frame (lf D F0)) (frame F'₂) = Z := by
    rw [← hZ]; ext a b; rfl
  have hne : Formalism.L2.SG.Pf.ScalarFramePf.GDl (frame (lf D F0)) (frame F'₂) (D.R.rS + 1) ≠ 0 := by
    rw [gdl_full, hGZ]; exact hdet
  refine IsUnit.mul (IsUnit.mul ?_ ?_) (Formalism.L2.SG.Pf.BBTie.bt_iota_unit p hne)
  · exact Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one
      (fun i _ => (Formalism.L2.SG.Pf.ScalarFramePf.isUnit_sF Zd p _).map (Zd.M p).L.cj)
  · exact Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one
      (fun i _ => Formalism.L2.SG.Pf.ScalarFramePf.isUnit_sF' Zd p _)

theorem cohDG_holds : CohDG Zd u u' F0 what₂ := by
  intro _ γ Z F'₂ φ' hH
  refine Set.finite_empty.subset fun p hp => ?_
  have hdet : Z.det ≠ 0 := (starMinors_holds u u' F0 what₂ γ Z hH.1).1
  have hu := local_discriminant_unit_of_det Zd p γ Z F'₂ hH.2.1 hdet
  have T1 := hH.2.2.2 p
  exact absurd ⟨hu, Formalism.MainNotions.S.Loc.HermSp.CohU.gdet_ne_of_ratio T1.1.1.2.2.2.2.1 hu T1.2.2.2.1.2.2.2.2.2⟩ hp

theorem star_coherence_of_good (hLp : CohLp Zd u u' F0 what₂) (hGood : CohGood Zd u u' F0 what₂) :
    CtxP u u' F0 what₂ → StarCoh Zd u u' F0 what₂ :=
  star_coherence_of_three Zd (cohDG_holds Zd) hLp hGood

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqClassHolds
section
noncomputable section

open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc
  Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqClass

namespace Formalism.L2.SG.Pf

theorem liftIotaEqC_holds : LiftIotaEqC :=
  fun _ _ Y u _ s₁ s₂ _ _ _ _ hr =>
    Formalism.L2.SG.Pf.iotaDict_fwd Y s₁ s₂ (lam_eq Y u hr) (lam'_eq Y u hr) (congrArg (fun r => r.2.2) hr)

theorem stepClassG_holds : StepClassG := stepClassG_of_liftIota liftIotaEqC_holds

end Formalism.L2.SG.Pf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqLoc
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.Pf.MainEqCut
  Formalism.L2.SG.Pf.MainEqAna

namespace Formalism.L2.SG.Pf.MainEqLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def LocalInputLeG {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (X : PB.Terms τ Rw I H H₁) {E : Type} [Field E] {r : ℕ}
    {Cl Nu : Type} (N : PN.NGData τ E r Cl Nu) (C1 C0 : ℕ) (AAre : ℝ) : Prop :=
  ∀ γ, PN.IsPt X N γ → ∀ S : Finset (Cl × Nu), ∃ L : PN.LocalNG Cl Nu, L.Basic ∧ ZAt L C1 r ∧
    L.MassRatioAt C0 r ∧ L.Unfold ∧ (∀ x ∈ S, N.a2 x.1 γ x.2 = weightedGenericAmplitudeSq L x.1 x.2) ∧ N.Hh γ = L.Htot ∧
    0 < L.ngenTot ∧ L.ngenTot ≤ AAre * 2 * N.Hh γ ^ PN.eN r * N.n γ

theorem localInputG_of_le {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (X : PB.Terms τ Rw I H H₁) {E : Type} [Field E] {r : ℕ}
    {Cl Nu : Type} (N : PN.NGData τ E r Cl Nu) (C1 C0 : ℕ) (AAre : ℝ) (h : LocalInputLeG X N C1 C0 AAre)
    (hng : ∀ γ, N.ngen γ = AAre * 2 * N.Hh γ ^ PN.eN r * N.n γ) : LocalInputG X N C1 C0 := by
  intro γ hγ S
  obtain ⟨L, hB, hZ, hM, hU, ha, hH, hpos, hle⟩ := h γ hγ S
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = AAre * 2 * N.Hh γ ^ PN.eN r * N.n γ / L.ngenTot := ⟨_, rfl⟩
  have hc1 : 1 ≤ c := by
    rw [hc, le_div_iff₀ hpos, one_mul]
    exact hle
  have hV0 : 0 ≤ L.V0 := hB.2.2.2.2.2.1
  refine ⟨{ L with V0 := L.V0 * c }, ?_, hZ, hM, ?_, ?_, hH, ?_⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hB
    unfold Formalism.FourierDecayAlt.PN.LocalNG.Basic
    exact ⟨h1, h2, h3, h4, h5, mul_nonneg h6 (by linarith), h7⟩
  · intro d S' hS'
    have h0 := hU d S' hS'
    have hw : 0 ≤ L.V0 * ∏ p, L.wt p (d p) :=
      mul_nonneg hV0 (Finset.prod_nonneg fun p _ => hB.1 p (d p))
    calc ∑ x ∈ S', L.rw x.1 ≤ L.V0 * ∏ p, L.wt p (d p) := h0
      _ ≤ L.V0 * c * ∏ p, L.wt p (d p) := by nlinarith
  · intro x hx
    rw [ha x hx]
    first
      | rfl
      | (unfold Formalism.L2.SG.Pf.MainEqCut.weightedGenericAmplitudeSq Formalism.L2.SG.Pf.MainEqCut.ampGen; rfl)
      | (cases hd : L.dat x.1 x.2 <;> simp [Formalism.L2.SG.Pf.MainEqCut.weightedGenericAmplitudeSq, Formalism.L2.SG.Pf.MainEqCut.ampGen, hd])
  · show N.ngen γ = L.V0 * c * ∏ p, L.ngen p
    rw [hng γ]
    have e : L.ngenTot = L.V0 * ∏ p, L.ngen p := rfl
    have hne : L.ngenTot ≠ 0 := hpos.ne'
    rw [show L.V0 * c * ∏ p, L.ngen p = L.ngenTot * c by rw [e]; ring, hc, mul_div_assoc',
      mul_div_cancel_left₀ _ hne]

def StepLocPinnedG : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C1 C0n : ℕ, ∃ CSt : ℝ, 0 ≤ CSt ∧ ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u →
      ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
        (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ), MassDataTie X hb X0 ψ →
      ∀ (sd C Th : ℝ) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
        (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))
        (vR : Formalism.L2.SG.TermDef.Term D u u F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u F0 what₂)
        (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (Irat Ire : ℝ),
        MassDataAdmissible X Y u u (bkU X hb Y u u X0 ψ sd C Th vR Q i0 i0' νq) Irat Ire →
      ∀ ν, Pinned X u u ν →
      ∃ s : X.B.I.Ginf → NNReal,
        (∀ γ, Formalism.L2.SG.RealObj.RegX X u u γ → s γ = 1) ∧ (∀ γ, 0 < s γ) ∧
        (∀ γ, (s γ : ℝ) ^ 2 ≤ large₂.sc.b ^ (CSt * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 * D.R.f)) ∧
        LocalInputLeG (genT (Y.tO u u)) (NOfG Y u (sc s ν) ν (fun _ => 0)) C1 C0n
          (PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f * (bkU X hb Y u u X0 ψ sd C Th vR Q i0 i0' νq).AA)

end Formalism.L2.SG.Pf.MainEqLoc

namespace Formalism.L2.SG.Pf

open Formalism.L2.SG.Pf.MainEqLoc

theorem stepLocGenPinnedG_of_loc (h : StepLocPinnedG) : StepLocGenPinnedG := by
  intro Cg cb Cw cT CT C0
  obtain ⟨C1, C0n, CSt, hCSt, C'₀, Cl₀, H⟩ := h Cg cb Cw cT CT C0
  refine ⟨C1, C0n, CSt, hCSt, C'₀, Cl₀, ?_⟩
  intro C' Cl hC' hCl D large₂ X Y u hctx hb X0 ψ hbt sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hok ν hpin
  obtain ⟨s, hs1, hs2, hs3, hloc⟩ :=
    H C' Cl hC' hCl D large₂ X Y u hctx hb X0 ψ hbt sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hok ν hpin
  let AAre : ℝ := PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f * (bkU X hb Y u u X0 ψ sd C Th vR Q i0 i0' νq).AA
  let N0 := NOfG Y u (sc s ν) ν (fun _ => 0)
  let ng : PN.Pts D.host.E D.R.rS → ℝ := fun γ => AAre * 2 * N0.Hh γ ^ PN.eN D.R.rS * N0.n γ
  refine ⟨s, ng, 2, hs1, hs2, hs3, by norm_num, le_refl _, ?_, ?_⟩
  · exact localInputG_of_le _ _ C1 C0n AAre hloc (fun γ => rfl)
  · intro γ _
    refine ⟨?_, le_refl _⟩
    change 0 ≤ Formalism.L2.SG.RowsConc.nPt _ _ _ γ
    unfold Formalism.L2.SG.RowsConc.nPt
    apply Finset.prod_nonneg
    intro w _
    apply mul_nonneg
    · exact pow_nonneg (mul_nonneg (inv_nonneg.2 (Even.pow_nonneg (Even.mul_right (even_two_mul _) _) _))
        (w.1.nonneg _)) _
    · apply Finset.prod_nonneg
      intro a _
      exact Even.pow_nonneg (Even.mul_right (even_two_mul _) _) _

end Formalism.L2.SG.Pf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqVanish
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.Pf.MainEqAna

namespace Formalism.L2.SG.Pf.MainEqVanish

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def FormGC : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u →
      ∀ ν, Pinned X u u ν → ∀ t ∈ (Y.tO u u).genSet, (Y.tO u u).vec t ≠ 0 →
        (∃ w : Point D.host.E (D.R.rS + 1), toPts w = ptPN t ∧ ∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u w g) ∧
        ∀ w : Point D.host.E (D.R.rS + 1), toPts w = ptPN t → (∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u w g) →
          ∃ (c : ℂ) (A : X.Vpi u →L[ℂ] X.Vpi u) (B : X.Vpi u →L[ℂ] X.Vpi u),
            OOt t = c • A.comp ((haveI := FiniteDimensional.complete ℂ (X.Vpi u)
              OO (ν (Formalism.L2.SG.RealObj.gamW X u u w)) Set.univ (X.Wu u) (X.Wu u)
                (Formalism.L2.SG.RealObj.gamW X u u w)).comp B)

theorem stepTermVanishG_of_form (h : FormGC) : StepTermVanishG := by
  intro Cg cb Cw cT CT C0
  obtain ⟨a₀, b₀, h2⟩ := h Cg cb Cw cT CT C0
  refine ⟨a₀, b₀, fun C' Cl e1 e2 D large₂ X Y u hc ν hν t ht hJ => ?_⟩
  by_contra hv
  obtain ⟨⟨w, hw, hrep⟩, hform⟩ := h2 C' Cl e1 e2 D large₂ X Y u hc ν hν t ht hv
  have hex : ∃ w' : Point D.host.E (D.R.rS + 1), toPts w' = ptPN t ∧ ∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u w' g :=
    ⟨w, hw, hrep⟩
  unfold J2of at hJ
  rw [dif_pos hex] at hJ
  have hJw : Jw Y u u ν hex.choose = 0 :=
    Formalism.L2.SG.NGVanish.hsEmb_eq_zero _ (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hJ))
  obtain ⟨c, A, B, hO⟩ := hform hex.choose hex.choose_spec.1 hex.choose_spec.2
  have key : ∀ (k χ c : ℂ) (A : X.Vpi u →L[ℂ] X.Vpi u) (Z : X.Vpi u →L[ℂ] X.Vpi u)
      (B : X.Vpi u →L[ℂ] X.Vpi u), k • Z = 0 → k • (χ • (c • A.comp (Z.comp B))) = 0 := by
    intro k χ c A Z B hZ
    have hy : ∀ y, k • Z y = 0 := fun y => by simpa using congrArg (fun T => T y) hZ
    ext x
    simp only [smul_apply, ContinuousLinearMap.comp_apply, zero_apply]
    rw [smul_comm k χ, smul_comm k c, ← map_smul A k, hy]
    simp
  have hamp : ampN (Y.cs u) (Y.cs u) (Y.FN u) (Y.FN u) t = 0 := by
    unfold ampN
    rw [hO]
    unfold Jw at hJw
    exact key _ _ _ _ _ _ hJw
  apply hv
  show vec (Y.cs u) (Y.cs u) (Y.FN u) (Y.FN u) t = 0
  unfold vec
  rw [hamp]
  simp
  rfl

end Formalism.L2.SG.Pf.MainEqVanish
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NmlIntHolds
section
namespace Formalism.L2.SG.NGCut.NormalIntegrality

theorem NmlInt_holds : Formalism.L2.SG.NGCut.NormalVectorPairings.NmlInt :=
  nmlInt_of fun _ _ Y _ _ t0 t h0 h hR hG hT hT' =>
    ⟨(Formalism.L2.SG.NGCut.NormalVectorPairings.line_occ Y t0 t h0 h hR hG hT hT').1.1,
      (Formalism.L2.SG.NGCut.NormalVectorPairings.line_occ Y t0 t h0 h hR hG hT hT').2.1⟩

end Formalism.L2.SG.NGCut.NormalIntegrality
end

