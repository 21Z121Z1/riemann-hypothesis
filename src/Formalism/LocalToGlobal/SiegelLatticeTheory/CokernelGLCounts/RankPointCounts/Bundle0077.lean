import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0074
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataConc
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0051
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.UnipotentInLevelSubgroup

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBetaIB
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

variable (u u' F0 what₂)

def LsetB : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D) (F'₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
    (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂))
    (Λ₂ : Submodule (𝓞 D.host.E) (VS D).V), BHyp Zd u u' F0 what₂ γ Z F'₂ φ φ' Λ₂ →
    ∀ β₀ : (VS D).V ≃ₗ[D.host.E] (VS D).V, β₀ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT →
      (∀ b, β₀ (frame (repF γ) b) = frame (liftF F'₂) b) →
      W0₂ γ.lam Λ₂ (lf D F0) (repF γ) (liftF F'₂) β₀ → OmB (lf D F0) (repF γ) (liftF F'₂) β₀ →
      ∀ (p : PlF D) (m : (VS D).V), m ∈ γ.lam → m ∈ orth (VS D) (Xsp (repF γ)) →
        ∃ x ∈ lattice₂ D Zd.M p Λ₂, baseChange₂ D p (β₀ m) - x ∈ (locH Zd p).X (locF' Zd p F'₂)

def IotaB : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D) (F'₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
    (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂))
    (Λ₂ : Submodule (𝓞 D.host.E) (VS D).V), BHyp Zd u u' F0 what₂ γ Z F'₂ φ φ' Λ₂ →
    ∀ β₀ : (VS D).V ≃ₗ[D.host.E] (VS D).V, β₀ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT →
      (∀ b, β₀ (frame (repF γ) b) = frame (liftF F'₂) b) →
      W0₂ γ.lam Λ₂ (lf D F0) (repF γ) (liftF F'₂) β₀ → OmB (lf D F0) (repF γ) (liftF F'₂) β₀ →
      ∀ v : (VS D).V ≃ₗ[D.host.E] (VS D).V, v ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT →
        (∀ b, v (frame (liftF F'₂) b) = frame (liftF F'₂) b) →
        (∀ y ∈ orth (VS D) (Xsp (liftF F'₂)), v y - y ∈ Xsp (liftF F'₂)) →
        Formalism.HermitianLatticesTheory.gmap (v * β₀) γ.lam = Λ₂ → IotaC₂ γ.lam Λ₂ (lf D F0) (repF γ) (liftF F'₂) (v * β₀)

variable {u u' F0 what₂}

namespace BetaI

theorem isLattice_gmap' (g : (VS D).V ≃ₗ[D.host.E] (VS D).V) {L : Submodule (𝓞 D.host.E) (VS D).V}
    (hL : Submodule.IsLattice D.host.E L) : Submodule.IsLattice D.host.E (Formalism.HermitianLatticesTheory.gmap g L) := by
  refine ⟨hL.fg.map _, ?_⟩
  have e : ((Formalism.HermitianLatticesTheory.gmap g L : Submodule (𝓞 D.host.E) (VS D).V) : Set (VS D).V) =
      (g : (VS D).V →ₗ[D.host.E] (VS D).V) '' (L : Set (VS D).V) := rfl
  rw [e, Submodule.span_image, hL.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
  exact g.surjective

theorem sd_gmap (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hβ : β ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hSD : BwdNA.SD (VS D) Λ) : BwdNA.SD (VS D) (Formalism.HermitianLatticesTheory.gmap β Λ) := by
  intro x
  rw [Formalism.L2.SG.Saturated.mem_gmap_iff]
  constructor
  · intro hx y hy
    rw [Formalism.L2.SG.Saturated.mem_gmap_iff] at hy
    have h1 := (hSD _).1 hx _ hy
    have e := hβ (β.symm y) (β.symm x)
    simp only [LinearEquiv.apply_symm_apply] at e
    rwa [e]
  · intro h
    refine (hSD _).2 fun y hy => ?_
    have h1 := h (β y) (by rw [Formalism.L2.SG.Saturated.mem_gmap_iff]; simpa using hy)
    have e := hβ y (β.symm x)
    simp only [LinearEquiv.apply_symm_apply] at e
    rwa [e] at h1

end BetaI

theorem betaInt_of (hLs : LsetB Zd u u' F0 what₂) (hIo : IotaB Zd u u' F0 what₂) : BetaInt Zd u u' F0 what₂ := by
  intro γ Z F'₂ φ φ' Λ₂ hB β₀ hiso hfr hW hO
  have hB0 := hB
  obtain ⟨hC, -, hS, hΛ₂, -, hT, hPD, -⟩ := hB
  obtain ⟨hΛ₂lat, hloc₂⟩ := hΛ₂
  obtain ⟨-, hT2, -⟩ := hS
  have hrow := hC.2.1.1 γ.lam γ.mem
  have hΛlat : Submodule.IsLattice D.host.E γ.lam := hrow.2.1.1
  have hSDl : ∀ p, (locH Zd p).IsSelfDual (lattice₂ D Zd.M p γ.lam) := fun p => (hT2 p).1.1.1
  have hSDl₂ : ∀ p, (locH Zd p).IsSelfDual (lattice₂ D Zd.M p Λ₂) := fun p => (hloc₂ p).1.1.1
  have hpr₂ : ∀ p, (locH Zd p).Prim (lattice₂ D Zd.M p Λ₂) (locF' Zd p F'₂) := fun p => (hloc₂ p).1.1.2.2.1.1
  have hSD := sd_of_loc Zd hΛlat hSDl
  have hSD₂ := sd_of_loc Zd hΛ₂lat hSDl₂
  have hXiso : ∀ x ∈ Xsp (liftF F'₂), ∀ y ∈ Xsp (liftF F'₂), (VS D).hT x y = 0 :=
    fun x hx y hy => NMoveP.hT_X_X F'₂.fl hx hy
  have hzX : F'₂.fl.z ∈ orth (VS D) (Xsp (liftF F'₂)) := (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).2 fun x hx => by
    rw [BwdNA.hsw (VS D) F'₂.fl.z x]
    have h := NMoveP.hT_f_X F'₂.fl (Fin.last D.R.rS) hx
    rw [NMoveP.fvecL] at h
    rw [h, star_zero]
  have hznot : F'₂.fl.z ∉ Xsp (liftF F'₂) := by
    intro h
    have h0 := (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).1 hzX F'₂.fl.z h
    rw [F'₂.fl.z_norm, neg_eq_zero] at h0
    exact (D.mem u').A.T_prime.ne_zero (Nat.cast_eq_zero.1 h0)
  have hXo := BwdNA.X_le_orth (VS D) (Xsp (liftF F'₂)) hXiso
  have hXX : ∀ {w : (VS D).V}, w ∈ orth (VS D) (orth (VS D) (Xsp (liftF F'₂))) → w ∈ Xsp (liftF F'₂) :=
    fun {w} hw => BwdNA.mem_of_orth_orth (VS D) _ fun v hv => by
      rw [BwdNA.hsw (VS D) v w, (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).1 hw v hv, star_zero]
  have hXX' : ∀ {w : (VS D).V}, w ∈ orth (VS D) (orth (VS D) (Xsp (repF γ))) → w ∈ Xsp (repF γ) :=
    fun {w} hw => BwdNA.mem_of_orth_orth (VS D) _ fun v hv => by
      rw [BwdNA.hsw (VS D) v w, (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).1 hw v hv, star_zero]
  have hXmap : (Xsp (repF γ)).map (β₀ : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp (liftF F'₂) :=
    BwdBetaCut.Xsp_of_frame β₀ _ _ hfr
  have hsymmX : ∀ x ∈ Xsp (liftF F'₂), β₀.symm x ∈ Xsp (repF γ) := fun x hx => by
    rw [← hXmap] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    simpa using hy
  have hmapX : ∀ x ∈ Xsp (repF γ), β₀ x ∈ Xsp (liftF F'₂) := fun x hx => by
    rw [← hXmap]; exact Submodule.mem_map_of_mem hx

  have hΛ₁lat := BetaI.isLattice_gmap' β₀ hΛlat
  have hSD₁ := BetaI.sd_gmap β₀ hiso hSD

  have he : ∀ a, β₀ ((repF γ).fl.e a) = F'₂.fl.e a := BwdBetaCut.e_of_frame β₀ (repF γ) (liftF F'₂) hfr
  have hXS : Formalism.HermitianLatticesTheory.gmap β₀ (XS D (repF γ).fl) = XS D F'₂.fl := by
    unfold Formalism.HermitianLatticesTheory.gmap XS
    rw [Submodule.map_span]
    congr 1
    ext y
    constructor
    · rintro ⟨w, ⟨a, x, hx, rfl⟩, rfl⟩
      exact ⟨a, x, hx, by simp [he]⟩
    · rintro ⟨a, x, hx, rfl⟩
      exact ⟨x • (repF γ).fl.e a, ⟨a, x, hx, rfl⟩, by simp [he]⟩
  have hFO₂ : XLam Λ₂ (liftF F'₂) = XS D F'₂.fl := hT.2.2.2.2
  have hFO : XLam γ.lam (repF γ) = XS D (repF γ).fl := hPD.2.2.2
  have hXm : ∀ x ∈ Xsp (liftF F'₂), x ∈ Λ₂ ↔ x ∈ Formalism.HermitianLatticesTheory.gmap β₀ γ.lam := fun x hx => by
    have h1 : x ∈ Λ₂ ↔ x ∈ XLam Λ₂ (liftF F'₂) :=
      ⟨fun h => Submodule.mem_inf.2 ⟨h, hx⟩, fun h => (Submodule.mem_inf.1 h).1⟩
    have h2 : x ∈ Formalism.HermitianLatticesTheory.gmap β₀ γ.lam ↔ β₀.symm x ∈ XLam γ.lam (repF γ) := by
      rw [Formalism.L2.SG.Saturated.mem_gmap_iff]
      exact ⟨fun h => Submodule.mem_inf.2 ⟨h, hsymmX x hx⟩, fun h => (Submodule.mem_inf.1 h).1⟩
    rw [h1, h2, hFO₂, hFO, ← hXS, Formalism.L2.SG.Saturated.mem_gmap_iff]

  have hzβ : β₀ (repF γ).fl.z = F'₂.fl.z := by
    have := hfr (Fin.last _)
    rwa [BwdBetaCut.fvec_last', BwdBetaCut.fvec_last'] at this
  have hz₁ : F'₂.fl.z ∈ Formalism.HermitianLatticesTheory.gmap β₀ γ.lam := by
    rw [Formalism.L2.SG.Saturated.mem_gmap_iff, ← hzβ, LinearEquiv.symm_apply_apply]
    exact hPD.1.1
  have hz₂ : F'₂.fl.z ∈ Λ₂ := hT.1.1.1

  have hL : ∀ x ∈ Λ₂, x ∈ orth (VS D) (Xsp (liftF F'₂)) →
      ∃ y ∈ Formalism.HermitianLatticesTheory.gmap β₀ γ.lam, y - x ∈ Xsp (liftF F'₂) := fun x hx hxo => by
    obtain ⟨w, hw, hxw⟩ := BwdNA.dual_sum (VS D) γ.lam hΛlat hSD (orth (VS D) (Xsp (repF γ))) (β₀.symm x)
      (fun m hm hmo => by
        have e := hiso m (β₀.symm x)
        rw [LinearEquiv.apply_symm_apply] at e
        rw [← e]
        refine int_of_loc Zd fun p => ?_
        rw [← localForm_baseChange]
        obtain ⟨x₁, hx₁, hd⟩ := hLs γ Z F'₂ φ φ' Λ₂ hB0 β₀ hiso hfr hW hO p m hm hmo
        have e2 : baseChange₂ D p (β₀ m) = x₁ + (baseChange₂ D p (β₀ m) - x₁) := by abel
        rw [e2, Formalism.L2.SG.Pf.ScalarFramePf.h_add_right (locH Zd p),
          (show (locH Zd p).h (baseChange₂ D p x) (baseChange₂ D p (β₀ m) - x₁) = 0 from baseChangeAt_perp' Zd p F'₂ hxo _ hd), add_zero]
        exact ((hSDl₂ p).2.2 (baseChange₂ D p x)).1 (baseChange_mem_localLattice Zd hx p) x₁ hx₁)
    refine ⟨β₀ w, (Formalism.L2.SG.Saturated.mem_gmap_iff _ _ _).2 (by simpa using hw), ?_⟩
    have h2 := hmapX _ (hXX' hxw)
    have e : β₀ w - x = -(β₀ (β₀.symm x - w)) := by
      rw [map_sub, LinearEquiv.apply_symm_apply]; abel
    rw [e]
    exact (Xsp (liftF F'₂)).neg_mem h2
  have hL' : ∀ y ∈ Formalism.HermitianLatticesTheory.gmap β₀ γ.lam, y ∈ orth (VS D) (Xsp (liftF F'₂)) →
      ∃ x ∈ Λ₂, x ∈ orth (VS D) (Xsp (liftF F'₂)) ∧ y - x ∈ Xsp (liftF F'₂) := fun y hy hyo => by
    rw [Formalism.L2.SG.Saturated.mem_gmap_iff] at hy
    have hmo : β₀.symm y ∈ orth (VS D) (Xsp (repF γ)) := (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).2 fun x hx => by
      have e := hiso x (β₀.symm y)
      rw [LinearEquiv.apply_symm_apply] at e
      rw [← e]
      exact (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).1 hyo _ (hmapX x hx)
    obtain ⟨w, hw, hyw⟩ := BwdNA.dual_sum (VS D) Λ₂ hΛ₂lat hSD₂ (orth (VS D) (Xsp (liftF F'₂))) y
      (fun m₂ hm₂ hm₂o => by
        refine int_of_loc Zd fun p => ?_
        rw [← localForm_baseChange]
        obtain ⟨x₁, hx₁, hd⟩ := hLs γ Z F'₂ φ φ' Λ₂ hB0 β₀ hiso hfr hW hO p _ hy hmo
        rw [LinearEquiv.apply_symm_apply] at hd
        have e2 : baseChange₂ D p y = x₁ + (baseChange₂ D p y - x₁) := by abel
        rw [e2, (locH Zd p).h_add_left]
        have h0 : (locH Zd p).h (baseChange₂ D p y - x₁) (baseChange₂ D p m₂) = 0 := by
          rw [(locH Zd p).h_herm, (show (locH Zd p).h (baseChange₂ D p m₂) (baseChange₂ D p y - x₁) = 0 from
            baseChangeAt_perp' Zd p F'₂ hm₂o _ hd), map_zero]
        rw [h0, add_zero]
        exact ((hSDl₂ p).2.2 x₁).1 hx₁ (baseChange₂ D p m₂) (baseChange_mem_localLattice Zd hm₂ p))
    have hX1 := hXX hyw
    refine ⟨w, hw, ?_, hX1⟩
    have e : w = y - (y - w) := by abel
    rw [e]
    exact (orth (VS D) (Xsp (liftF F'₂))).sub_mem hyo (hXo hX1)
  have hy := exists_yG Zd F'₂ hΛ₂lat hSD₂ hpr₂ hznot
  have htr : ∃ c : D.host.E, IsIntegral ℤ c ∧ c + star c = 1 := by
    obtain ⟨c, hc⟩ := D.host.exists_trace_one
    refine ⟨(c : D.host.E), RingOfIntegers.isIntegral_coe c, ?_⟩
    rw [Formalism.BasicNotions.Examples₂.star_eq_conj (H := D.host)]
    exact hc
  obtain ⟨n, hniso, hnX, hnz, hno, himg⟩ := BwdNA.main (VS D) (Xsp (liftF F'₂)) hXiso F'₂.fl.z hzX
    (Formalism.HermitianLatticesTheory.gmap β₀ γ.lam) Λ₂ hΛ₁lat hΛ₂lat hSD₁ hSD₂ hXm hz₁ hz₂ hL hL' hy htr
  have hnI : n ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := hniso
  have hvI : n.symm ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := (Formalism.HermitianLatticesTheory.isom (VS D).hT).inv_mem hnI
  have hvf : ∀ b, n.symm (frame (liftF F'₂) b) = frame (liftF F'₂) b := by
    intro b
    rw [LinearEquiv.symm_apply_eq]
    refine Fin.lastCases ?_ (fun i => ?_) b
    · rw [BwdBetaCut.fvec_last']; exact hnz.symm
    · rw [BwdBetaCut.fvec_cs']; exact (hnX _ (Submodule.subset_span ⟨i, rfl⟩)).symm
  have hvX : ∀ y ∈ orth (VS D) (Xsp (liftF F'₂)), n.symm y - y ∈ Xsp (liftF F'₂) := by
    intro y hy
    have hy'o : n.symm y ∈ orth (VS D) (Xsp (liftF F'₂)) := (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).2 fun x hx => by
      have e := hniso x (n.symm y)
      rw [hnX x hx, LinearEquiv.apply_symm_apply] at e
      rw [← e]
      exact (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).1 hy x hx
    have h1 := hno _ hy'o
    rw [LinearEquiv.apply_symm_apply] at h1
    have e : n.symm y - y = -(y - n.symm y) := by abel
    rw [e]
    exact (Xsp (liftF F'₂)).neg_mem h1
  have hgm : Formalism.HermitianLatticesTheory.gmap (n.symm * β₀) γ.lam = Λ₂ := by
    ext x
    rw [Formalism.L2.SG.Saturated.mem_gmap_iff]
    have e : (n.symm * β₀).symm x = β₀.symm (n x) := by
      rw [LinearEquiv.symm_apply_eq]
      show x = n.symm (β₀ (β₀.symm (n x)))
      simp
    rw [e, ← Formalism.L2.SG.Saturated.mem_gmap_iff]
    constructor
    · intro h
      have h' : n x ∈ (n : (VS D).V → (VS D).V) '' (Λ₂ : Set (VS D).V) := by rw [himg]; exact h
      obtain ⟨y, hy, hyx⟩ := h'
      rw [← n.injective hyx]
      exact hy
    · intro h
      have h' : n x ∈ (n : (VS D).V → (VS D).V) '' (Λ₂ : Set (VS D).V) := ⟨x, h, rfl⟩
      rw [himg] at h'
      exact h'
  exact ⟨n.symm, hvI, hvf, hvX, hgm, hIo γ Z F'₂ φ φ' Λ₂ hB0 β₀ hiso hfr hW hO n.symm hvI hvf hvX hgm⟩

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataPos
section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.MassDataPos

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets
  Formalism.L2.SG.MassDataConc MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem glkC_pos (k g : ℕ) (hg : g.Prime) : 0 < glkC k g := by
  haveI : NeZero g := ⟨hg.ne_zero⟩
  unfold glkC
  exact Nat.card_pos

theorem ukC_pos (k g : ℕ) (hg : g.Prime) : 0 < ukC k g := by
  haveI : NeZero g := ⟨hg.ne_zero⟩
  unfold ukC
  exact Nat.card_pos

theorem ggC_pos (r k g : ℕ) (hg : g.Prime) : 0 < ggC r k g := by
  haveI : NeZero g := ⟨hg.ne_zero⟩
  unfold ggC
  exact Nat.card_pos

theorem nnC_pos (r k g : ℕ) (hg : g.Prime) : 0 < nnC r k g := by
  haveI : NeZero g := ⟨hg.ne_zero⟩
  unfold nnC
  rw [Nat.card_pos_iff]
  refine ⟨⟨⟨1, ?_⟩⟩, inferInstance⟩
  unfold Formalism.FourierDecayAlt.S3.IsN
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (simp only [Formalism.DoubleCosetMeasures.IsUpUni, Formalism.FourierDecayAlt.S3.b11, Formalism.FourierDecayAlt.S3.b33, Formalism.FourierDecayAlt.S3.b22, Formalism.FourierDecayAlt.S3.b21, Formalism.FourierDecayAlt.S3.b31, Formalism.FourierDecayAlt.S3.b32]
       exact ⟨fun i j hij => by simp [Matrix.one_apply, (show j < i from hij).ne'], fun a => by simp [Matrix.one_apply]⟩)
    | (simp [Formalism.FourierDecayAlt.S3.b11, Formalism.FourierDecayAlt.S3.b33, Formalism.FourierDecayAlt.S3.b22, Formalism.FourierDecayAlt.S3.b21, Formalism.FourierDecayAlt.S3.b31, Formalism.FourierDecayAlt.S3.b32, Matrix.one_apply]; done)
    | (ext i j; simp [Formalism.FourierDecayAlt.S3.b11, Formalism.FourierDecayAlt.S3.b33, Formalism.FourierDecayAlt.S3.b22, Formalism.FourierDecayAlt.S3.b21, Formalism.FourierDecayAlt.S3.b31, Formalism.FourierDecayAlt.S3.b32, Matrix.one_apply]; done)

section Main

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
  (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
  (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
  {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (T : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (sd C Th : ℝ)
  {F0 : FlagG (VS D) D.R.rS ((Lat.Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}
  (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
  (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)

abbrev bk : Formalism.FourierDecayAlt.S3.MassData (TypX X) := bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq

def MassDataPosC : Prop := (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).Pos

def LocHaarPosC : Prop :=
  (∀ p, 0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μKp p ∧
    0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μKnatp p ∧
    0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μKppp p ∧
    0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μSp p ∧
    0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μSp' p ∧
    0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μSppp p ∧
    0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μSppp' p) ∧
  0 < (X.measG.μGf (Formalism.L2.SG.Sub.Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)))).toReal ∧
  0 < ((X.measW u).μSf (Subtype.val ⁻¹' (Formalism.L2.SG.Sub.Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) :
      Set (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.B.I.F) X.B.I.cm.sig X.B.I.J)))).toReal ∧
  0 < ((X.measW u').μSf (Subtype.val ⁻¹' (Formalism.L2.SG.Sub.Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) :
      Set (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.B.I.F) X.B.I.cm.sig X.B.I.J)))).toReal ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μH ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μH' ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μHpp ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μHpp' ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μN ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μN'

def CovolPosC : Prop :=
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volG ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volHa ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volHa' ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volNa ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volNa' ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volB

def QuotVolPosC : Prop :=
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volH ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volH' ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volN ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volN'

def RecPosC : Prop :=
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).deg ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).dimπ ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).dimπ' ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).ρ0 ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).ρ0' ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).d ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).d'

theorem gOf_prime (p : TypX X) : (gOf p).Prime := by
  unfold gOf
  split_ifs
  · exact D.host.g_prime 0
  · exact D.host.g_prime 1

theorem massDataPosC_of (hL : LocHaarPosC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq)
    (hCv : CovolPosC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq)
    (hQv : QuotVolPosC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq)
    (hR : RecPosC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq)
    (hP : Formalism.L2.SG.LocVol.ProdConv X u u' ψ) (hCoo : 0 < Formalism.L2.SG.RealObj.DisintegrationConstant X u u' 1)
    (hκ : 0 < Formalism.L2.SG.MassDataConc.kapN D) (hsd : 0 ≤ sd) (hC : 0 ≤ C) (hTh : 0 < Th) :
    MassDataPosC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq := by
  obtain ⟨hv, -, -, -, hUo, -, hZZ, hPP, -, hal, -⟩ := hP
  obtain ⟨hloc, hGf, hSf, hSf', hH, hH', hHpp, hHpp', hN, hN'⟩ := hL
  obtain ⟨hG, hHa, hHa', hNa, hNa', hB⟩ := hCv
  obtain ⟨hvH, hvH', hvN, hvN'⟩ := hQv
  obtain ⟨hdeg, hdp, hdp', hr0, hr0', hd, hd'⟩ := hR
  set B := bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq with hBdef
  have hMp : ∀ p, 0 < B.Mp p := fun p => (hv p.1).1 p.2
  have hU00p : ∀ p, 0 < B.localVolumeAtPlace p := fun p => (hv p.1).2.1
  have hKo : 0 < B.μKo := div_pos hGf (Finset.prod_pos fun p _ => (hloc p).1)
  have hSo : 0 < B.μSo := div_pos hSf (Finset.prod_pos fun p _ => (hloc p).2.2.2.1)
  have hSo' : 0 < B.μSo' := div_pos hSf' (Finset.prod_pos fun p _ => (hloc p).2.2.2.2.1)
  have hU00o : 0 < B.localVolumeArchimedean := hUo
  have hMo : 0 < B.Mo := div_pos (mul_pos hU00o (pow_pos hKo 2)) (mul_pos hSo hSo')
  have hZ : 0 < B.volZZ := hZZ
  have hPPp : 0 < B.volPP := by
    show 0 < ∏ l : Fin (D.R.rS + 1), ∏' v : Formalism.L2.SG.LocVol.PlX X, Formalism.L2.SG.LocVol.PPX X u u' ψ l v
    exact Finset.prod_pos fun l _ => (hPP l).2
  have hAl : 0 < B.al := mul_pos (Finset.prod_pos fun p _ => (hv p.1).2.2.2.2) hal
  have hCo : 0 < B.Coo := mul_pos hκ hCoo
  have hMM : 0 < B.MM := mul_pos hMo (Finset.prod_pos fun p _ => hMp p)
  have hμK : 0 < B.μK := mul_pos hKo (Finset.prod_pos fun p _ => (hloc p).1)
  have hAA : 0 < B.AA := div_pos (mul_pos (mul_pos hB hCo) (div_pos hMM hZ)) hμK
  have hn0c : 0 < B.n0c := div_pos hAA hr0
  have hgp : ∀ p, 0 < B.g p := fun p => by
    show (0 : ℝ) < ((gOf p : ℕ) : ℝ)
    exact_mod_cast (gOf_prime X p).pos
  have hglk : ∀ p, 0 < B.glk p := fun p => by
    show (0 : ℝ) < ((glkC D.R.k (gOf p) : ℕ) : ℝ)
    exact_mod_cast glkC_pos _ _ (gOf_prime X p)
  have huk : ∀ p, 0 < B.uk p := fun p => by
    show (0 : ℝ) < ((ukC D.R.k (gOf p) : ℕ) : ℝ)
    exact_mod_cast ukC_pos _ _ (gOf_prime X p)
  have hnn : ∀ p, 0 < B.nn p := fun p => by
    show (0 : ℝ) < ((nnC D.R.rS D.R.k (gOf p) : ℕ) : ℝ)
    exact_mod_cast nnC_pos _ _ _ (gOf_prime X p)
  have hgg : ∀ p, 0 < B.gg p := fun p => by
    show (0 : ℝ) < ((ggC D.R.rS D.R.k (gOf p) : ℕ) : ℝ)
    exact_mod_cast ggC_pos _ _ _ (gOf_prime X p)
  have hδ : 0 ≤ B.δ := by
    show 0 ≤ C * ((D.R.rS : ℝ) + 1) * (C / Th) ^ (Fintype.card (NumberField.InfinitePlace X.B.I.F))
    exact mul_nonneg (mul_nonneg hC (by positivity)) (pow_nonneg (div_nonneg hC hTh.le) _)
  unfold MassDataPosC Formalism.FourierDecayAlt.S3.MassData.Pos
  exact ⟨fun p => ⟨hgp p, hglk p, huk p, hnn p, hgg p, (hloc p).1, (hloc p).2.1, (hloc p).2.2.1, (hloc p).2.2.2.1,
      (hloc p).2.2.2.2.1, (hloc p).2.2.2.2.2.1, (hloc p).2.2.2.2.2.2, hMp p, hU00p p⟩,
    hKo, hSo, hSo', hMo, hU00o, hH, hH', hHpp, hHpp', hN, hN', hZ, hPPp, hAl, hG, hHa, hHa', hNa, hNa', hB, hvH, hvH',
    hvN, hvN', hCo, hdeg, hdp, hdp', hr0, hr0', hd, hd', hn0c, hsd, hδ⟩

end Main

theorem cooOf_pos {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word) : 0 < Formalism.L2.SG.RealObj.DisintegrationConstant X u u' 1 := by
  have h := Formalism.L2.SG.RealObj.InfCut.ProductExactness.haar_disintegration_real_holds D X u u' 1 one_pos
  have h' : ∃ C, 0 < C ∧ Formalism.L2.SG.RealObj.Disint X u u' 1 C := h
  unfold Formalism.L2.SG.RealObj.DisintegrationConstant
  rw [dif_pos h']
  exact h'.choose_spec.1

theorem quotVolPosC_of {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (Y : Formalism.L2.SG.Full.Full X)
    (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
    {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (T : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (sd C Th : ℝ)
    {F0 : FlagG (VS D) D.R.rS ((Lat.Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}
    (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (hK2 : X.LevelSubgroupNormalized) (hV : 0 < X.volK2) :
    QuotVolPosC X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq := by
  obtain ⟨hN, hH⟩ := Formalism.L2.SG.Closed.VolPosC_holds D X Y u hK2
  obtain ⟨hN', hH'⟩ := Formalism.L2.SG.Closed.VolPosC_holds D X Y u' hK2
  refine ⟨hH, hH', ?_, ?_⟩
  · show 0 < ((X.muN u) (Y.FN u)).toReal
    exact pos_of_mul_pos_right hN hV.le
  · show 0 < ((X.muN u') (Y.FN u')).toReal
    exact pos_of_mul_pos_right hN' hV.le

end Formalism.L2.SG.Pf.MassDataPos
end
end

