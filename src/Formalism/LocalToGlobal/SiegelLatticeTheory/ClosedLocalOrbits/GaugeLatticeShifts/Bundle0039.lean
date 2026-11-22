import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0037
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0010
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0012
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.DoubleCosetSingleUnfolding
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.FormHermitianPositive
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0014
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0017
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGramActLChi
section
noncomputable section

open scoped Classical
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.NormCut Formalism.L2.SG.PoincareInHH.PoincareSetting

namespace Formalism.L2.SG.Pf.SatGramActL

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def ChiNBiAll : Prop := ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D), ChiNBi X

namespace ChiLeft

theorem kBB_mem {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (Y : Full X) (u u' : D.what₂.Word)
    {Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : Λ ∈ Y.what₂ u) (hΛ' : Λ' ∈ Y.what₂ u')
    (p : GCar X u u' (X.Fu u) (X.Fu u') Λ Λ') : kBB Y u u' Λ Λ' p.1.1 ∈ X.B.I.Kset := by
  obtain ⟨hRL, -, hmap, -⟩ := p.2
  have hRL' : RatLink X p.1.1 p.1.2 := hRL
  have hmap' : Formalism.HermitianLatticesTheory.gmap p.1.2 Λ' = Λ := hmap
  have hb0 := (Y.cs u).base_lam Λ hΛ
  have hb1 := (Y.cs u').base_lam Λ' hΛ'
  have key : (((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u)⁻¹ *
      (p.1.1.2 * (((Y.cs u').h ((Y.cs u').base Λ') : X.B.I.Gf) * X.xu u')) ∈ X.B.I.Kset := by
    refine LatDictK.dict_K X _ _ {y | y ∈ Λ} (fun y => ?_) (fun y => ?_)
    · show y ∈ Λ ↔ _
      conv_lhs => rw [← hb0]
      exact (Y.cs u).lat_eq _ y
    · show y ∈ Λ ↔ _
      have e1 : y ∈ Λ ↔ p.1.2.symm y ∈ Λ' := by
        constructor
        · intro hy
          rw [← hmap'] at hy
          obtain ⟨z, hz, hzy⟩ := hy
          have : p.1.2.symm y = z := by rw [← hzy]; simp
          rw [this]; exact hz
        · intro h
          rw [← hmap']
          exact ⟨p.1.2.symm y, h, by simp⟩
      have hlat : ∀ w, w ∈ Λ' ↔ X.B.I.fmat (((Y.cs u').h ((Y.cs u').base Λ') : X.B.I.Gf) * X.xu u')⁻¹ *ᵥ
          incl X.B.I (X.crd w) ∈ X.B.I.Lf := fun w => by
        have := (Y.cs u').lat_eq ((Y.cs u').base Λ') w
        rw [hb1] at this
        exact this
      rw [e1, hlat, show (p.1.1.2 * (((Y.cs u').h ((Y.cs u').base Λ') : X.B.I.Gf) * X.xu u'))⁻¹ =
          (((Y.cs u').h ((Y.cs u').base Λ') : X.B.I.Gf) * X.xu u')⁻¹ * p.1.1.2⁻¹ from _root_.mul_inv_rev _ _,
        LatDictK.fmatK_mul, ← Matrix.mulVec_mulVec, LatDictK.ratLink_incl_inv X hRL']
  have e : kBB Y u u' Λ Λ' p.1.1 = (((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u)⁻¹ *
      (p.1.1.2 * (((Y.cs u').h ((Y.cs u').base Λ') : X.B.I.Gf) * X.xu u')) := by
    simp only [kBB, kOf, mul_assoc]
  rw [e]
  exact key

theorem kB_inv_fix {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {w : D.what₂.Word}
    {rs : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (c : ColSys X w rs) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (γ : Gam X w) (hk : kB c Λ γ ∈ X.B.I.Kset) :
    ∀ a, CongG X (X.B.I.fmat (kB c Λ γ)⁻¹ *ᵥ X.f0 a) (X.f0 a) := by
  have e : (((iotaF X w γ * c.h (c.base Λ) : Hfin X w) : X.B.I.Gf) * X.xu w)⁻¹ *
      ((c.h (c.base Λ) : X.B.I.Gf) * X.xu w) = (kB c Λ γ)⁻¹ := by
    unfold kB
    push_cast
    group
  have hK : (((iotaF X w γ * c.h (c.base Λ) : Hfin X w) : X.B.I.Gf) * X.xu w)⁻¹ *
      ((c.h (c.base Λ) : X.B.I.Gf) * X.xu w) ∈ X.B.I.Kset := by
    rw [e]; exact mem_Kset_inv X hk
  have h := (column_fixed_holds X w (iotaF X w γ * c.h (c.base Λ)) (c.h (c.base Λ)) hK).1
  rw [e] at h
  exact h

theorem one_fix {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (w : D.what₂.Word) (h1 : (1 : X.B.I.Gf) ∈ X.B.I.Kset) :
    ∀ a, CongG X (X.B.I.fmat (1 : X.B.I.Gf) *ᵥ nxt X.e0 X.z0 a) (nxt X.e0 X.z0 a) := by
  have hK : (((1 : Hfin X w) : X.B.I.Gf) * X.xu w)⁻¹ * (((1 : Hfin X w) : X.B.I.Gf) * X.xu w) ∈ X.B.I.Kset := by
    rw [inv_mul_cancel]; exact h1
  have h := (column_fixed_holds X w 1 1 hK).2
  simpa only [inv_mul_cancel] using h

end ChiLeft

theorem chiNLeft_holds (hB : ChiNBiAll) : ChiNLeft := by
  intro D X Y u u' Λ Λ' hΛ hΛ' γ hk p
  have hκ := ChiLeft.kBB_mem Y u u' hΛ hΛ' p
  have h1 : (1 : X.B.I.Gf) ∈ X.B.I.Kset := by
    have h := mem_Kset_mul X hk (mem_Kset_inv X hk)
    rwa [mul_inv_cancel] at h
  have h := hB D X (kBB Y u u' Λ Λ' p.1.1) (kB (Y.cs u) Λ γ) 1 hκ hk h1
    (ChiLeft.kB_inv_fix (Y.cs u) Λ γ hk) (ChiLeft.one_fix u h1)
  rwa [mul_one] at h

end Formalism.L2.SG.Pf.SatGramActL
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabCoverPfSteps
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PoincareInHH.Cut Formalism.L2.SG.TermOp Formalism.L2.SG.TermOp.KExpCut
  Formalism.L2.SG.Full Formalism.L2.SG.Pf.Slab
open Matrix

namespace Formalism.L2.SG.Pf.SlabCoverPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def GFInfInj : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (s : X.B.I.GA), s ∈ Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I → s.1 = 1 → s = 1

def NStrongApprox : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (ρ : (Y.cs u).Cl) (n : X.B.I.Gf),
    X.LevelSubgroupNormalized → n ∈ X.NfinU u → ∃ ν ∈ Srat X u,
      (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)⁻¹ * (ν.2 * n) * (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u) ∈ X.K2

def NDense : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (n : X.B.I.Gf), n ∈ X.NfinU u →
    ∀ U : Set X.B.I.Gf, IsOpen U → n ∈ U →
      ∃ ν ∈ Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I, ν.1 ∈ X.NinfU u ∧ ν.2 ∈ X.NfinU u ∧ ν.2 ∈ U

def NLift : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (ρ : (Y.cs u).Cl) (t : X.B.I.Ginf),
    t ∈ NOcol (X.Fu u) (Y.cs u) ρ → ∃ s ∈ Srat X u, s.1 = t ∧
      (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)⁻¹ * s.2 * (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u) ∈ X.K2

def NRatLam : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (ρ : (Y.cs u).Cl) (ν : X.B.I.GA),
    X.LevelSubgroupNormalized → ν ∈ Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I → ν.1 ∈ X.NinfU u → ν.2 ∈ X.NfinU u →
    (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)⁻¹ * ν.2 * (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u) ∈ X.K2 →
    ν.1 ∈ NOcol (X.Fu u) (Y.cs u) ρ

def RatLeviC : Prop := ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), RatLevi X u

def PsiDdC : Prop := ∀ (D : D7) (X : HidaSetting D), PsiDd X

theorem hfin_sfin {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (h : Hfin X u) :
    (h : X.B.I.Gf) ∈ SfinU X u := by
  rw [Formalism.L2.SG.PoincareInHH.Cut.sfin_iff]
  refine ⟨?_, ?_⟩
  · intro a
    have e := h.2 (X.eR a) (by simp [fixSet])
    try beta_reduce
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, e, sub_self]
    exact Submodule.zero_mem _
  · have e := h.2 (X.zR u) (by simp [fixSet])
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, e, sub_self]
    exact Submodule.zero_mem _

theorem gam_srat {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (γ : X.B.I.GA) (hγ : γ ∈ Gam X u) :
    γ ∈ Srat X u := by
  obtain ⟨h1, h2⟩ := hγ
  obtain ⟨h21, h22⟩ := h2
  refine ⟨h1, Subgroup.subset_closure ⟨?_, hfin_sfin X u ⟨γ.2, h22⟩⟩⟩
  rw [Formalism.L2.SG.PoincareInHH.Cut.sinf_iff]
  intro v
  refine ⟨?_, ?_⟩
  · intro a
    have e := h21 v (X.eR a) (by simp [fixSet])
    try beta_reduce
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, e, sub_self]
    exact Submodule.zero_mem _
  · have e := h21 v (X.zR u) (by simp [fixSet])
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, e, sub_self]
    exact Submodule.zero_mem _

theorem iotaF_coe {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (γ : Gam X u) :
    ((iotaF X u γ : Hfin X u) : X.B.I.Gf) = (γ : X.B.I.GA).2 := rfl

end Formalism.L2.SG.Pf.SlabCoverPf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabMajPtPfSupp
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.Full

namespace Formalism.L2.SG.Pf.SlabMajPt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem term_supp {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (Y : Full X) (u u' : D.what₂.Word)
    (t : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')) :
    ∃ (h : Hfin X u') (κ : X.B.I.Gf), κ ∈ X.K2 ∧
      t.pt.2⁻¹ * Formalism.L2.SG.Pf.Slab.aB Y u t.lam = (h : X.B.I.Gf) * X.xu u' * κ := by
  have hTF := Full.frameTie (X := X) u u'
  have hKk := Formalism.L2.SG.Closed.TermK_holds (F0 := X.Fu u) (F0' := X.Fu u') (Y.cs u) (Y.cs u') t
  have hNk := Formalism.L2.SG.Closed.AdmN_holds (Y.cs u) (Y.cs u') hTF t
  have hGk := Formalism.L2.SG.Closed.AdmPar_holds (Y.cs u) (Y.cs u') hTF t
  obtain ⟨h, hc, -, hlev⟩ := Formalism.L2.SG.Pf.NormSteps.levi_onto_reduction Y.TR (Y.cs u')
    ⟨t.lam', t.mem'⟩
    (levi Y.TR (kOf X u u' ((Y.cs u).h ((Y.cs u).base t.lam) : X.B.I.Gf)
      ((Y.cs u').h ((Y.cs u').base t.lam') : X.B.I.Gf) t.pt))⁻¹
  have hNc := Formalism.L2.SG.NormCut.ncong_colDiff u' _ _ hc
  have hGc := Formalism.L2.SG.NormCut.good_of_ncong X hc hNc
  have hKkc := Formalism.L2.SG.Pf.unitaryCongruence.K_mul X.B.I hKk hc
  have hNkc := Formalism.L2.SG.NormCut.ncong_mul X hKk hNk hNc
  have hGkc := Formalism.L2.SG.NormCut.good_mul X hGk hGc
  have hlevkc := Formalism.L2.SG.NormCut.levi_mul Y.TR hGk hGc
  rw [hlev, mul_inv_cancel] at hlevkc
  have hK2 := Formalism.L2.SG.NormCut.mem_level_of_unitriangular Y.TR hGkc hNkc (fun v => by
    rw [hlevkc, Pi.one_apply]
    exact Formalism.L2.SG.GGMirabolic.isUni_one)
  refine ⟨h, _, Y.hK.2.2.1 _ hK2, ?_⟩
  simp only [Formalism.L2.SG.Pf.Slab.aB, kOf, Formalism.L2.SG.Pf.NormSteps.colDS]
  group

end Formalism.L2.SG.Pf.SlabMajPt
end
end

