import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0019
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0430
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0233
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0215
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0001
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0035
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0390
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0408
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0428
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0024
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.StepLocGenPinnedGP
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0072

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LowerBlockDoubleCosetOperatorKeepsLevelCharacter
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LowerBlockHecke

theorem sum_translate {G : Type} [Group G] (J : Subgroup G) (g₀ : G) (R : Finset G) (hRJ : ∀ y ∈ R, y ∈ J)
    (hR : ∀ j ∈ J, ∃! j', j' ∈ R ∧ (j' * g₀)⁻¹ * (j * g₀) ∈ J) (χ : G → ℂ)
    (hmul : ∀ a ∈ J, ∀ b ∈ J, χ (a * b) = χ a * χ b) (hne : ∀ a ∈ J, χ a ≠ 0)
    (hconj : ∀ m ∈ J, g₀⁻¹ * m * g₀ ∈ J → χ (g₀⁻¹ * m * g₀) = χ m)
    (Φ : G → ℂ) (hΦ : ∀ x, ∀ k ∈ J, Φ (x * k) = χ k * Φ x) {y₀ : G} (hy₀ : y₀ ∈ J) :
    ∑ y ∈ R, (χ y)⁻¹ * Φ (y₀ * y * g₀) = χ y₀ * ∑ y ∈ R, (χ y)⁻¹ * Φ (y * g₀) := by
  classical
  let s : G → G → G := fun a y => if h : a * y ∈ J then (hR _ h).exists.choose else y
  have hs : ∀ a ∈ J, ∀ y ∈ R, s a y ∈ R ∧ (s a y * g₀)⁻¹ * (a * y * g₀) ∈ J := by
    intro a ha y hy
    have h : a * y ∈ J := J.mul_mem ha (hRJ y hy)
    have e : s a y = (hR _ h).exists.choose := dif_pos h
    rw [e]
    exact (hR _ h).exists.choose_spec
  have huniq : ∀ a ∈ J, ∀ y ∈ R, ∀ z ∈ R, (z * g₀)⁻¹ * (a * y * g₀) ∈ J → s a y = z := by
    intro a ha y hy z hz hzJ
    exact (hR _ (J.mul_mem ha (hRJ y hy))).unique (hs a ha y hy) ⟨hz, hzJ⟩
  have hinv : ∀ y ∈ R, s y₀⁻¹ (s y₀ y) = y := by
    intro y hy
    obtain ⟨hm, hK⟩ := hs y₀ hy₀ y hy
    apply huniq _ (J.inv_mem hy₀) _ hm _ hy
    have e : (y * g₀)⁻¹ * (y₀⁻¹ * s y₀ y * g₀) = ((s y₀ y * g₀)⁻¹ * (y₀ * y * g₀))⁻¹ := by group
    rw [e]
    exact J.inv_mem hK
  have hinv' : ∀ y ∈ R, s y₀ (s y₀⁻¹ y) = y := by
    intro y hy
    obtain ⟨hm, hK⟩ := hs y₀⁻¹ (J.inv_mem hy₀) y hy
    apply huniq _ hy₀ _ hm _ hy
    have e : (y * g₀)⁻¹ * (y₀ * s y₀⁻¹ y * g₀) = ((s y₀⁻¹ y * g₀)⁻¹ * (y₀⁻¹ * y * g₀))⁻¹ := by group
    rw [e]
    exact J.inv_mem hK
  rw [Finset.mul_sum]
  refine Finset.sum_nbij' (s y₀) (s y₀⁻¹) (fun y hy => (hs y₀ hy₀ y hy).1)
    (fun y hy => (hs _ (J.inv_mem hy₀) y hy).1) hinv hinv' ?_
  intro y hy
  obtain ⟨hm, hK⟩ := hs y₀ hy₀ y hy
  set y' := s y₀ y
  set k := (y' * g₀)⁻¹ * (y₀ * y * g₀)
  have hyJ := hRJ y hy
  have hy'J := hRJ y' hm
  have hmJ : y'⁻¹ * (y₀ * y) ∈ J := J.mul_mem (J.inv_mem hy'J) (J.mul_mem hy₀ hyJ)
  have ek : k = g₀⁻¹ * (y'⁻¹ * (y₀ * y)) * g₀ := by simp only [k]; group
  have hχk : χ k = χ (y'⁻¹ * (y₀ * y)) := by rw [ek]; exact hconj _ hmJ (ek ▸ hK)
  have e1 : y₀ * y * g₀ = y' * g₀ * k := by simp only [k]; group
  have e2 : χ y₀ * χ y = χ y' * χ (y'⁻¹ * (y₀ * y)) := by
    rw [← hmul _ hy₀ _ hyJ, ← hmul _ hy'J _ hmJ, mul_inv_cancel_left]
  rw [e1, hΦ _ _ hK, hχk]
  have hy0 := hne y hyJ
  have hy'0 := hne y' hy'J
  have e3 : χ (y'⁻¹ * (y₀ * y)) = χ y₀ * χ y * (χ y')⁻¹ := by
    rw [e2, mul_comm (χ y'), mul_assoc, mul_inv_cancel₀ hy'0, mul_one]
  rw [e3]
  field_simp

end GlobalTheory.LowerBlockHecke

namespace GlobalTheory.LowerBlockHecke

open ValuativeRel GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.ZonalCellDecomposition

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]

theorem det_lower_ne {j : GL (A ⊕ D) k} (hj : j ∈ parahoric k A D) : j.1.toBlocks₂₂.det ≠ 0 := by
  obtain ⟨h, hh, rfl⟩ := hj
  intro h0
  have e1 : (GeneralLinearGroup.map (n := A ⊕ D) (algebraMap 𝒪[k] k) h).1.toBlocks₂₂ =
      (algebraMap 𝒪[k] k).mapMatrix h.1.toBlocks₂₂ := rfl
  rw [e1, ← RingHom.map_det] at h0
  have h1 : h.1.toBlocks₂₂.det = 0 := Subtype.ext h0
  set u := GeneralLinearGroup.map (n := A ⊕ D) (IsLocalRing.residue 𝒪[k]) h with hu
  have h21 : u.1.toBlocks₂₁ = 0 := by
    ext i j
    exact hh (i := .inr i) (j := .inl j) (show false < true by decide)
  have h22 : u.1.toBlocks₂₂.det = 0 := by
    have : u.1.toBlocks₂₂ = (IsLocalRing.residue 𝒪[k]).mapMatrix h.1.toBlocks₂₂ := rfl
    rw [this, ← RingHom.map_det, h1, map_zero]
  have := u.det_ne_zero
  rw [← fromBlocks_toBlocks u.1, h21, det_fromBlocks_zero₂₁, h22, mul_zero] at this
  exact this rfl

theorem det_lower_conj_mtor (ϖ : kˣ) (e : D → ℤ) (m : GL (A ⊕ D) k) :
    ((mtor ϖ e)⁻¹ * m * mtor ϖ e : GL (A ⊕ D) k).1.toBlocks₂₂.det = m.1.toBlocks₂₂.det := by
  set c : A ⊕ D → kˣ := fun i => ϖ ^ (Sum.elim (0 : A → ℤ) e i) with hc
  have ht : mtor (A := A) ϖ e = diagT k (A ⊕ D) c := rfl
  have hti : (mtor (A := A) ϖ e)⁻¹ = diagT k (A ⊕ D) c⁻¹ := by rw [ht, map_inv]
  have hb : ((mtor ϖ e)⁻¹ * m * mtor ϖ e : GL (A ⊕ D) k).1.toBlocks₂₂ =
      diagonal (fun i => ((c (.inr i))⁻¹ : kˣ) : D → k) * m.1.toBlocks₂₂ * diagonal (fun i => (c (.inr i) : k)) := by
    rw [hti, ht, Units.val_mul, Units.val_mul, val_diagT, val_diagT]
    ext i j
    simp only [toBlocks₂₂, of_apply, diagonal_mul, mul_diagonal, Pi.inv_apply]
  rw [hb, det_mul, det_mul, det_diagonal, det_diagonal, mul_comm, ← mul_assoc, ← Finset.prod_mul_distrib]
  simp

end GlobalTheory.LowerBlockHecke

namespace GlobalTheory.LowerBlockHecke

open GlobalTheory.ZonalCellDecomposition

set_option maxHeartbeats 2000000 in

theorem hecke_level : ∀ D : D7, ForStageQ D fun c w j s => ∀ PP ∈ w.Q, ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v), IsProjAt φ PP → ∀ (ξl : (Fv D.host.F v)ˣ →* ℂˣ), LiftsChar φ PP ξl (w.ξ PP) → ∀ ι, IsChart s j φ ι → ∀ (ϖ : (Fv D.host.F v)ˣ) (e : Blocks j D.R.t → ℤ) (R : Finset (GL (Fin D.R.r ⊕ Blocks j D.R.t) (Fv D.host.F v))) (d : GL (Fin D.R.r ⊕ Blocks j D.R.t) (Fv D.host.F v) → (Fv D.host.F v)ˣ), GlobalTheory.ParHecke.IsReps (GlobalTheory.ZonalCellDecomposition.mtor ϖ e) R d → ∀ F : GA D s.V → ℂ, (∀ κ ∈ Lev.levG s.V s.β s.L, ∀ g, F (g * κ) = Lev.levChi s.V s.β s.L κ * F g) → ∀ κ ∈ Lev.levG s.V s.β s.L, ∀ g, ∑ y ∈ R, ((ξl (d y) : ℂˣ) : ℂ) * F (g * κ * ι (y * GlobalTheory.ZonalCellDecomposition.mtor ϖ e)) = Lev.levChi s.V s.β s.L κ * ∑ y ∈ R, ((ξl (d y) : ℂˣ) : ℂ) * F (g * ι (y * GlobalTheory.ZonalCellDecomposition.mtor ϖ e)) := by
  intro D c w hw j hj s hs PP hPP v φ hφ ξl hξ ι hι ϖ e R d hR F hF κ hκ g
  obtain ⟨-, -, -, -, hch⟩ := GlobalTheory.T.splitPlaceChart_parahoric_level_stabiliser_height D c w hw j hj s hs PP hPP v φ hφ
  obtain ⟨⟨eq, hemb, -⟩, hlev, hchi⟩ := hch ι hι
  have hchi' := hchi ξl hξ
  set J := parahoric (Fv D.host.F v) (Fin D.R.r) (Blocks j D.R.t) with hJ
  set g₀ : GL (Fin D.R.r ⊕ Blocks j D.R.t) (Fv D.host.F v) := mtor ϖ e with hg₀
  set χ : GL (Fin D.R.r ⊕ Blocks j D.R.t) (Fv D.host.F v) → ℂ := fun x => Lev.levChi s.V s.β s.L (ι x) with hχ

  set k0 := gAt s.V (.inl v) κ with hk0def
  have hk0 : k0 ∈ Lev.levG s.V s.β s.L := by
    obtain ⟨hr, hL, hfl⟩ := hs
    have hfr : Formalism.L2.DIV.IsFrame s.β s.Λ := hfl.frame
    have hP : s.L.P.H = ⊥ := by rw [hL]; rfl
    obtain ⟨-, hS, hl⟩ := (LevLoc.mem_lev_iff s.V.gram s.β s.L hP _).1 hκ.2
    have hkS := LevLoc.finE_gAt_mem_St hfr κ v ((GlobalTheory.T.finitePart_mem_frameStabilizer_iff_local_stabilizer D s.V s.β s.Λ hfr κ).1 hS v)
    refine ⟨GlobalTheory.ChainOnto.LevelFacts.emb_mem_GfC s.V v _, ?_⟩
    refine (LevLoc.mem_lev_iff s.V.gram s.β s.L hP _).2 ⟨GlobalTheory.LevSplit.finE_mem_UA s.V _, hkS, fun PP' => ?_⟩
    by_cases e' : PP'.under (𝓞 D.host.F) = v
    · subst e'
      rw [← LevLoc.red_local hfr κ hS PP']
      exact hl PP'
    · rw [GlobalTheory.T.latticeReduction_eq_one_of_local_component_one D s.V s.β _ PP' hkS (GlobalTheory.AdelicU.proj_emb_ne _ _ e' _)]
      exact LevLoc.locOK_one _ _
  set y₀ := eq.symm (GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v κ) with hy₀def
  have hy0 : ι y₀ = k0 := by
    rw [hemb, hy₀def, eq.apply_symm_apply]
    rfl
  have hy0J : y₀ ∈ J := (hlev y₀).1 (hy0 ▸ hk0)
  set κ' := k0⁻¹ * κ with hκ'def
  have hκ' : κ' ∈ Lev.levG s.V s.β s.L := mul_mem (inv_mem hk0) hκ
  have hκeq : κ = k0 * κ' := by rw [hκ'def, mul_inv_cancel_left]
  have hpκ' : GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v κ' = 1 := by
    rw [hκ'def, map_mul, map_inv]
    show (GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v
      (GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v (GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v κ)))⁻¹ *
        GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v κ = 1
    rw [GlobalTheory.AdelicU.proj_emb_self, inv_mul_cancel]
  have hcomm : ∀ x, ι x * κ' = κ' * ι x := fun x => by
    rw [hemb]
    exact (GlobalTheory.AdelicU.commute_emb D.sp.cm.sig s.V.gram (eq x) hpκ').eq

  have hmul : ∀ a ∈ J, ∀ b ∈ J, χ (a * b) = χ a * χ b := fun a ha b hb => by
    simp only [hχ, map_mul]
    exact GlobalTheory.ChainOnto.LevelFacts.levChi_mul ((hlev a).2 ha) ((hlev b).2 hb)
  have hne : ∀ a ∈ J, χ a ≠ 0 := fun a ha => by
    simp only [hχ]
    rw [hchi' a ha (Units.mk0 _ (det_lower_ne ha)) rfl]
    exact Units.ne_zero _
  have hconj : ∀ m ∈ J, g₀⁻¹ * m * g₀ ∈ J → χ (g₀⁻¹ * m * g₀) = χ m := fun m hm hm' => by
    simp only [hχ]
    rw [hchi' _ hm' (Units.mk0 _ (det_lower_ne hm')) rfl, hchi' m hm (Units.mk0 _ (det_lower_ne hm)) rfl]
    have : Units.mk0 _ (det_lower_ne hm') = Units.mk0 _ (det_lower_ne hm) :=
      Units.ext (det_lower_conj_mtor ϖ e m)
    rw [this]
  have hΦ : ∀ x, ∀ k ∈ J, F (g * ι (x * k)) = χ k * F (g * ι x) := fun x k hk => by
    rw [map_mul, ← mul_assoc]
    exact hF _ ((hlev k).2 hk) _
  have hxi : ∀ y ∈ R, ((ξl (d y) : ℂˣ) : ℂ) = (χ y)⁻¹ := fun y hy => by
    simp only [hχ]
    rw [hchi' y (hR.1 y hy).1 (d y) (hR.1 y hy).2]
    simp
  have hterm : ∀ y, F (g * κ * ι (y * g₀)) = Lev.levChi s.V s.β s.L κ' * F (g * ι (y₀ * y * g₀)) := fun y => by
    have e1 : g * κ * ι (y * g₀) = g * ι (y₀ * y * g₀) * κ' := by
      rw [hκeq, mul_assoc y₀ y g₀, map_mul ι y₀, hy0]
      simp only [mul_assoc]
      rw [hcomm]
    rw [e1, hF κ' hκ']
  have key := sum_translate J g₀ R (fun y hy => (hR.1 y hy).1) hR.2 χ hmul hne hconj (fun x => F (g * ι x)) hΦ hy0J
  calc ∑ y ∈ R, ((ξl (d y) : ℂˣ) : ℂ) * F (g * κ * ι (y * g₀))
      = Lev.levChi s.V s.β s.L κ' * ∑ y ∈ R, (χ y)⁻¹ * F (g * ι (y₀ * y * g₀)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun y hy => ?_
        rw [hxi y hy, hterm y]
        ring
    _ = Lev.levChi s.V s.β s.L κ' * (χ y₀ * ∑ y ∈ R, (χ y)⁻¹ * F (g * ι (y * g₀))) := by rw [key]
    _ = Lev.levChi s.V s.β s.L κ * ∑ y ∈ R, ((ξl (d y) : ℂˣ) : ℂ) * F (g * ι (y * g₀)) := by
        have h1 : Lev.levChi s.V s.β s.L κ = χ y₀ * Lev.levChi s.V s.β s.L κ' := by
          rw [hκeq, GlobalTheory.ChainOnto.LevelFacts.levChi_mul hk0 hκ']
          simp only [hχ, hy0]
        have h2 : ∑ y ∈ R, ((ξl (d y) : ℂˣ) : ℂ) * F (g * ι (y * g₀)) = ∑ y ∈ R, (χ y)⁻¹ * F (g * ι (y * g₀)) :=
          Finset.sum_congr rfl fun y hy => by rw [hxi y hy]
        rw [h1, h2]
        ring

end GlobalTheory.LowerBlockHecke

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemOfRhoLt
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LevZeroUniq
open GlobalTheory.SplitWeil GlobalTheory.StepData

variable {D : D7} {c : Comm D} {v : VCom c} {PP : Formalism.L2.DIV.Pl D.host.E}

def rho (G : GLoc v) : 𝓞 D.host.E →+* G.k := (G.q.pr.comp (incA D)).comp (algebraMap (𝓞 D.host.E) D.host.E)

theorem rho_apply (G : GLoc v) (z : 𝓞 D.host.E) : rho G z = (ofSplit G.q).pr (z : D.host.E) := rfl

theorem rho_lt (G : GLoc v) (hid : Formalism.L2.NTheta.IsIdemAt G.q.e PP) {z : 𝓞 D.host.E} (hz : z ∈ PP.asIdeal) :
    valuation G.k (rho G z) < 1 := by
  by_cases h0 : z = 0
  · subst h0; simp
  have h0' : rho G z ≠ 0 := (map_ne_zero (G.q.pr.comp (incA D))).2 (RingOfIntegers.coe_ne_zero_iff.2 h0)
  have h1 := (hid.2 z h0).1 hz
  rw [← G.q.sec_pr, ← G.q.int_iff] at h1
  change (G.q.pr.comp (incA D)) _ ∉ _ at h1
  rw [map_inv₀, Valuation.mem_integer_iff, map_inv₀, not_le] at h1
  exact (one_lt_inv₀ (zero_lt_iff.2 ((map_ne_zero _).2 h0'))).1 h1

theorem mem_of_rho_lt (G : GLoc v) (hid : Formalism.L2.NTheta.IsIdemAt G.q.e PP) {z : 𝓞 D.host.E}
    (hz : valuation G.k (rho G z) < 1) : z ∈ PP.asIdeal := by
  by_cases h0 : z = 0
  · subst h0; exact zero_mem _
  have h0' : rho G z ≠ 0 := (map_ne_zero (G.q.pr.comp (incA D))).2 (RingOfIntegers.coe_ne_zero_iff.2 h0)
  refine (hid.2 z h0).2 ?_
  rw [← G.q.sec_pr, ← G.q.int_iff]
  change (G.q.pr.comp (incA D)) _ ∉ _
  rw [map_inv₀, Valuation.mem_integer_iff, map_inv₀, not_le]
  exact (one_lt_inv₀ (zero_lt_iff.2 ((map_ne_zero _).2 h0'))).2 hz

def out (y : Formalism.L2.DIV.kP PP) : 𝓞 D.host.E := Function.surjInv (Ideal.Quotient.mk_surjective (I := PP.asIdeal)) y

theorem mk_out (y : Formalism.L2.DIV.kP PP) : Ideal.Quotient.mk PP.asIdeal (out y) = y :=
  Function.surjInv_eq (Ideal.Quotient.mk_surjective (I := PP.asIdeal)) y

theorem rho_sub_lt (G : GLoc v) (hid : Formalism.L2.NTheta.IsIdemAt G.q.e PP) {y : Formalism.L2.DIV.kP PP} {z : 𝓞 D.host.E}
    (hz : Ideal.Quotient.mk PP.asIdeal z = y) : valuation G.k (rho G (out y) - rho G z) < 1 := by
  rw [← map_sub]
  refine rho_lt G hid (Ideal.Quotient.eq.1 ?_)
  rw [mk_out, hz]

def pos (G : GLoc v) : Fin D.R.k ⊕ Fin (G.s + 1) ≃ Fin D.R.r :=
  finSumFinEquiv.trans (finCongr (by have := G.hs; unfold Ranks.r; omega))

theorem pos_val (G : GLoc v) (a : Fin D.R.k ⊕ Fin (G.s + 1)) : (pos G a).val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ a := by
  rcases a with a | a <;> rfl

def lift (G : GLoc v) (g : Matrix (Fin D.R.r) (Fin D.R.r) (Formalism.L2.DIV.kP PP)) :
    Matrix (Fin D.R.k ⊕ Fin (G.s + 1)) (Fin D.R.k ⊕ Fin (G.s + 1)) G.k :=
  fun a b => rho G (out (g (pos G a) (pos G b)))

theorem lift_one (G : GLoc v) (hid : Formalism.L2.NTheta.IsIdemAt G.q.e PP) :
    MaxM (lift G (1 : Matrix (Fin D.R.r) (Fin D.R.r) (Formalism.L2.DIV.kP PP)) - 1) := by
  intro a b
  have e : (lift G (1 : Matrix (Fin D.R.r) (Fin D.R.r) (Formalism.L2.DIV.kP PP)) - 1) a b =
      rho G (out ((1 : Matrix (Fin D.R.r) (Fin D.R.r) (Formalism.L2.DIV.kP PP)) (pos G a) (pos G b))) -
      rho G (if a = b then 1 else 0) := by
    simp only [Matrix.sub_apply, lift, Matrix.one_apply]
    split_ifs <;> simp
  rw [e]
  refine rho_sub_lt G hid ?_
  simp only [Matrix.one_apply, (pos G).injective.eq_iff]
  split_ifs <;> simp

theorem red_iff (G : GLoc v) (hid : Formalism.L2.NTheta.IsIdemAt G.q.e PP) (x : G.S.P.J) (g : GL (Fin D.R.r) (Formalism.L2.DIV.kP PP)) :
    GlobalTheory.LevZero.Red G PP x g ↔ MaxM ((x : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val - lift G g.val) := by
  constructor
  · intro h a b
    have := h a b (pos G a) (pos G b) (pos_val G a) (pos_val G b) _ (mk_out _)
    simpa only [Matrix.sub_apply, lift, rho_apply] using this
  · intro h a b a' b' ha hb z hz
    obtain rfl : a' = pos G a := Fin.ext (ha.trans (pos_val G a).symm)
    obtain rfl : b' = pos G b := Fin.ext (hb.trans (pos_val G b).symm)
    have e : (x : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val a b - (ofSplit G.q).pr (z : D.host.E) =
        ((x : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val - lift G g.val) a b + (rho G (out (g.val (pos G a) (pos G b))) - rho G z) := by
      simp only [Matrix.sub_apply, lift, rho_apply]; ring
    rw [e]
    exact Valuation.map_add_lt _ (h a b) (rho_sub_lt G hid hz)

theorem intM_J (G : GLoc v) (x : G.S.P.J) : IntM (x : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val ∧
    IntM ((x : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k)⁻¹).val :=
  mem_KO.1 (G.S.P.le_KO x.2)

theorem red_one (G : GLoc v) (hid : Formalism.L2.NTheta.IsIdemAt G.q.e PP) : GlobalTheory.LevZero.Red G PP 1 1 := by
  rw [red_iff G hid]
  have := (lift_one G hid).neg
  simpa using this

theorem red_uniq (G : GLoc v) (hid : Formalism.L2.NTheta.IsIdemAt G.q.e PP) {x x' : G.S.P.J} {g g' : GL (Fin D.R.r) (Formalism.L2.DIV.kP PP)}
    (hx : GlobalTheory.LevZero.Red G PP x g) (hx' : GlobalTheory.LevZero.Red G PP x' g')
    (hk : x.1⁻¹ * x'.1 ∈ KOne G.k (Fin D.R.k ⊕ Fin (G.s + 1))) : g = g' := by
  rw [red_iff G hid] at hx hx'
  set X := (x : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k) with hX
  set X' := (x' : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k) with hX'
  have h1 : MaxM ((X⁻¹ * X').val - 1) := mem_KOne.1 hk
  have h2 : MaxM (lift G g'.val - lift G g.val) := by
    have e : lift G g'.val - lift G g.val =
        (X.val - lift G g.val) + -(X'.val - lift G g'.val) + X.val * ((X⁻¹ * X').val - 1) := by
      rw [Matrix.mul_sub, Units.val_mul, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul,
        Matrix.mul_one]
      abel
    rw [e]
    exact (hx.add hx'.neg).add ((intM_J G x).1.mul_maxM h1)
  refine Units.ext (Matrix.ext fun a' b' => ?_)
  obtain ⟨a, rfl⟩ := (pos G).surjective a'
  obtain ⟨b, rfl⟩ := (pos G).surjective b'
  have h3 : valuation G.k (rho G (out (g'.val (pos G a) (pos G b)) - out (g.val (pos G a) (pos G b)))) < 1 := by
    rw [map_sub]; simpa only [Matrix.sub_apply, lift] using h2 a b
  have h4 := Ideal.Quotient.eq.2 (mem_of_rho_lt G hid h3)
  rw [mk_out, mk_out] at h4
  exact h4.symm

end GlobalTheory.LevZeroUniq

theorem GlobalTheory.LevZeroUniq.main : ∀ {D : D7} {c : Comm D} {v : VCom c} (G : GLoc v) (PP : Formalism.L2.DIV.Pl D.host.E), Formalism.L2.NTheta.IsIdemAt G.q.e PP → GlobalTheory.LevZero.Red G PP 1 1 ∧ ∀ (x x' : G.S.P.J) (g g' : GL (Fin D.R.r) (kP PP)), GlobalTheory.LevZero.Red G PP x g → GlobalTheory.LevZero.Red G PP x' g' → x.1⁻¹ * x'.1 ∈ GlobalTheory.SplitWeil.KOne G.k (Fin D.R.k ⊕ Fin (G.s + 1)) → g = g' := by
  intro D c v G PP hid
  exact ⟨GlobalTheory.LevZeroUniq.red_one G hid, fun x x' g g' hx hx' hk => GlobalTheory.LevZeroUniq.red_uniq G hid hx hx' hk⟩

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MulMulDivCancelLeft
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.LevZero

theorem sum_fin_two_mul_add_one {M : Type*} [AddCommMonoid M] {ρ n : ℕ} (hn : n = 2 * ρ + 1) (f : Fin n → M)
    (a b : Fin ρ → M) (m : M) (ha : ∀ (i : Fin ρ) (j : Fin n), j.1 = i.1 → f j = a i) (hm : ∀ j : Fin n, j.1 = ρ → f j = m)
    (hb : ∀ (i : Fin ρ) (j : Fin n), j.1 + i.1 = 2 * ρ → f j = b i) :
    ∑ j, f j = ∑ i, a i + m + ∑ i, b i := by
  subst hn
  have e : ρ + (1 + ρ) = 2 * ρ + 1 := by omega
  rw [← Fin.sum_congr' f e, Fin.sum_univ_add, Fin.sum_univ_add, Fin.sum_univ_one, add_assoc]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => ha i _ (by simp)
  · congr 1
    · exact hm _ (by simp)
    · rw [← Equiv.sum_comp Fin.revPerm b]
      refine Finset.sum_congr rfl fun i _ => hb _ _ ?_
      simp [Fin.val_rev]
      omega

theorem mul_div_mem_integer_iff {k : Type} [Field k] [ValuativeRel k] {c : k} (hc : valuation k c = 1) (w z : k) :
    w * (z / c) ∈ 𝒪[k] ↔ w * z ∈ 𝒪[k] := by
  rw [Valuation.mem_integer_iff, Valuation.mem_integer_iff, map_mul, map_mul, map_div₀, hc, div_one]

theorem mul_mul_div_cancel_left' {k : Type} [Field k] {c : k} (hc : c ≠ 0) (P X : k) : c * P * (X / c) = P * X := by
  field_simp

theorem wShape_of_besFrame_loc : ∀ {D : D7} {c : Comm D} {v : VCom c} (G : GLoc v) (ρ : ℕ) (h0 : 0 + 2 * ρ + 2 = D.R.m) (L : GlobalTheory.FinPl.Lat (c.V 0)), (∀ y : XIx (Fin D.R.k) (Fin D.R.t) 0 ⊕ Fin (G.s + 1) → G.k, (fun r => G.q.sec (((G.FY 0 (G.s + 1) (zero_add _)).β *ᵥ y) r)) ∈ GlobalTheory.FinPl.latV (c.V 0) L (· = G.q.v) ↔ (∀ z, y (Sum.inl z) ∈ 𝒪[G.k]) ∧ ∀ i : Fin (G.s + 1), ((((G.S.ϖ : G.kˣ) : G.k) ^ (i.1 + 1))⁻¹ * y (Sum.inr i)) ∈ 𝒪[G.k]) → GlobalTheory.Core.Mi.LatMatch.WShape G.q (c.bes 0 ρ h0).d (c.bes 0 ρ h0).o (c.bes 0 ρ h0).ζ L (fun i => (((G.S.ϖ : G.kˣ) : G.k) ^ (i.1 + 1))⁻¹) (fun i => (((G.S.ϖ : G.kˣ) : G.k) ^ (2 * ρ - i.1 + 1))⁻¹) ((((G.S.ϖ : G.kˣ) : G.k) ^ (ρ + 1))⁻¹) 1 (c.x 0).L := by
  intro D c v G ρ h0 L hL
  obtain ⟨hc, hA, he, hz, he'⟩ := G.bes 0 ρ h0 (G.s + 1) (zero_add _)
  intro x x' t y
  have hsc : valuation G.k (G.sc 0) = 1 := G.sc_unit 0
  have hxi : valuation G.k (GlobalTheory.LocMod.ofSplit G.q).xi = 1 := GlobalTheory.MiTop.GluedLine.valuation_xi_zero_eq_one G.q G.unit
  have hhz : valuation G.k ((GlobalTheory.LocMod.ofSplit G.q).hz (c.B 0 ρ h0)) = 1 := G.hz_unit 0 ρ h0
  set cE : Fin ρ → G.k := fun i => G.sc 0 * (GlobalTheory.LocMod.ofSplit G.q).xi ^ (ρ - i.1) with hcE
  set cE' : Fin ρ → G.k := fun i => G.sc 0 * (-(GlobalTheory.LocMod.ofSplit G.q).hz (c.B 0 ρ h0) / (GlobalTheory.LocMod.ofSplit G.q).xi) *
    (-1 / (GlobalTheory.LocMod.ofSplit G.q).xi) ^ (ρ - 1 - i.1) with hcE'
  have vE : ∀ i, valuation G.k (cE i) = 1 := fun i => by simp [cE, map_pow, hsc, hxi]
  have vE' : ∀ i, valuation G.k (cE' i) = 1 := fun i => by
    simp [cE', map_pow, map_div₀, Valuation.map_neg, hsc, hxi, hhz]
  have nz : ∀ {c : G.k}, valuation G.k c = 1 → c ≠ 0 := fun h h0 => by simp [h0] at h
  have he2 : ∀ (i : Fin ρ) (j : Fin (G.s + 1)), j.1 = i.1 → ∀ r, (G.FY 0 (G.s + 1) (zero_add _)).β r (Sum.inr j) =
      cE i * G.q.pr (incA D ((c.bes 0 ρ h0).d.e r i)) := he
  have hz2 : ∀ (j : Fin (G.s + 1)), j.1 = ρ → ∀ r, (G.FY 0 (G.s + 1) (zero_add _)).β r (Sum.inr j) =
      G.sc 0 * G.q.pr (incA D (((c.bes 0 ρ h0).d.i₀ *ᵥ vecB (c.bes 0 ρ h0).o (c.bes 0 ρ h0).ζ) r)) := hz
  have he'2 : ∀ (i : Fin ρ) (j : Fin (G.s + 1)), j.1 + i.1 = 2 * ρ → ∀ r, (G.FY 0 (G.s + 1) (zero_add _)).β r (Sum.inr j) =
      cE' i * G.q.pr (incA D ((c.bes 0 ρ h0).d.e' r i)) := he'
  have hA2 : ∀ r a, (G.FY 0 (G.s + 1) (zero_add _)).β r (Sum.inl a) =
      (atW G.q ((c.bes 0 ρ h0).d.i₀ * (c.bes 0 ρ h0).o.iA) * (G.FX 0 (by omega)).β) r a := hA
  let Yr : Fin (G.s + 1) → G.k := fun j => if h : j.1 < ρ then x ⟨j.1, h⟩ / cE ⟨j.1, h⟩ else if j.1 = ρ then t / G.sc 0
      else if h' : 2 * ρ - j.1 < ρ then x' ⟨2 * ρ - j.1, h'⟩ / cE' ⟨2 * ρ - j.1, h'⟩ else 0
  let Y : StepData.XIx (Fin D.R.k) (Fin D.R.t) 0 ⊕ Fin (G.s + 1) → G.k := Sum.elim ((G.FX 0 (by omega)).γ *ᵥ y) Yr
  have YrE : ∀ (i : Fin ρ) (j : Fin (G.s + 1)), j.1 = i.1 → Yr j = x i / cE i := by
    intro i j hj
    have h : j.1 < ρ := hj ▸ i.2
    have : (⟨j.1, h⟩ : Fin ρ) = i := Fin.ext hj
    simp only [Yr, dif_pos h, this]
  have YrZ : ∀ (j : Fin (G.s + 1)), j.1 = ρ → Yr j = t / G.sc 0 := by
    intro j hj
    simp only [Yr, dif_neg (show ¬ j.1 < ρ by omega), if_pos hj]
  have YrE' : ∀ (i : Fin ρ) (j : Fin (G.s + 1)), j.1 + i.1 = 2 * ρ → Yr j = x' i / cE' i := by
    intro i j hj
    have h : 2 * ρ - j.1 < ρ := by omega
    have : (⟨2 * ρ - j.1, h⟩ : Fin ρ) = i := Fin.ext (by simp; omega)
    simp only [Yr, dif_neg (show ¬ j.1 < ρ by omega), if_neg (show ¬ j.1 = ρ by omega), dif_pos h, this]
  have hlat : (∀ a, Y (Sum.inl a) ∈ 𝒪[G.k]) ↔ (fun r => G.q.sec (y r)) ∈ GlobalTheory.FinPl.latV (c.X 0) (c.x 0).L (· = G.q.v) := by
    have h := G.latX 0 (by omega) ((G.FX 0 (by omega)).γ *ᵥ y)
    rw [Matrix.mulVec_mulVec, (G.FX 0 (by omega)).βγ, Matrix.one_mulVec] at h
    exact h
  refine Iff.trans (Eq.to_iff ?_) ((hL Y).trans ?_)
  · congr 1
    funext r
    congr 1
    symm
    rw [Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
    simp only [Y, Sum.elim_inl, Sum.elim_inr]
    have h1 : ∑ a, (G.FY 0 (G.s + 1) (zero_add _)).β r (Sum.inl a) * ((G.FX 0 (by omega)).γ *ᵥ y) a =
        (atW G.q ((c.bes 0 ρ h0).d.i₀ * (c.bes 0 ρ h0).o.iA) *ᵥ y) r := by
      calc _ = ((atW G.q ((c.bes 0 ρ h0).d.i₀ * (c.bes 0 ρ h0).o.iA) * (G.FX 0 (by omega)).β) *ᵥ
            ((G.FX 0 (by omega)).γ *ᵥ y)) r := by simp only [hA2]; rfl
        _ = _ := by rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, (G.FX 0 (by omega)).βγ, Matrix.mul_one]
    have h2 := sum_fin_two_mul_add_one hc (fun j => (G.FY 0 (G.s + 1) (zero_add _)).β r (Sum.inr j) * Yr j)
      (fun i => G.q.pr (incA D ((c.bes 0 ρ h0).d.e r i)) * x i) (fun i => G.q.pr (incA D ((c.bes 0 ρ h0).d.e' r i)) * x' i)
      (G.q.pr (incA D (((c.bes 0 ρ h0).d.i₀ *ᵥ vecB (c.bes 0 ρ h0).o (c.bes 0 ρ h0).ζ) r)) * t)
      (fun i j hj => by beta_reduce; rw [he2 i j hj r, YrE i j hj, mul_mul_div_cancel_left' (nz (vE i))])
      (fun j hj => by beta_reduce; rw [hz2 j hj r, YrZ j hj, mul_mul_div_cancel_left' (nz hsc)])
      (fun i j hj => by beta_reduce; rw [he'2 i j hj r, YrE' i j hj, mul_mul_div_cancel_left' (nz (vE' i))])
    rw [h1, h2]
    have hm : ∀ V : HSp D, Formalism.L2.Theta.mt V 1 = 1 := fun V => rfl
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hm, Matrix.map_one _ (map_zero G.q.pr) (map_one G.q.pr),
      Matrix.one_mulVec]
    simp only [Matrix.mulVec, dotProduct, atW, Matrix.map_apply]
    ring
  · have hinr : (∀ j : Fin (G.s + 1), (((G.S.ϖ : G.kˣ) : G.k) ^ (j.1 + 1))⁻¹ * Yr j ∈ 𝒪[G.k]) ↔
        (∀ a : Fin ρ, (((G.S.ϖ : G.kˣ) : G.k) ^ (a.1 + 1))⁻¹ * x a ∈ 𝒪[G.k]) ∧
        (∀ a : Fin ρ, (((G.S.ϖ : G.kˣ) : G.k) ^ (2 * ρ - a.1 + 1))⁻¹ * x' a ∈ 𝒪[G.k]) ∧
        (((G.S.ϖ : G.kˣ) : G.k) ^ (ρ + 1))⁻¹ * t ∈ 𝒪[G.k] := by
      constructor
      · intro h
        refine ⟨fun a => ?_, fun a => ?_, ?_⟩
        · have := h ⟨a.1, by omega⟩
          rwa [YrE a _ rfl, mul_div_mem_integer_iff (vE a)] at this
        · have := h ⟨2 * ρ - a.1, by omega⟩
          rwa [YrE' a _ (by simp only; omega), mul_div_mem_integer_iff (vE' a)] at this
        · have := h ⟨ρ, by omega⟩
          rwa [YrZ _ rfl, mul_div_mem_integer_iff hsc] at this
      · rintro ⟨h1, h2, h3⟩ j
        rcases lt_trichotomy j.1 ρ with hj | hj | hj
        · rw [YrE ⟨j.1, hj⟩ j rfl, mul_div_mem_integer_iff (vE _)]
          exact h1 ⟨j.1, hj⟩
        · rw [YrZ j hj, mul_div_mem_integer_iff hsc, hj]
          exact h3
        · have hi : 2 * ρ - j.1 < ρ := by omega
          rw [YrE' ⟨2 * ρ - j.1, hi⟩ j (by simp only; omega), mul_div_mem_integer_iff (vE' _)]
          have h4 := h2 ⟨2 * ρ - j.1, hi⟩
          have h5 : 2 * ρ - (2 * ρ - j.1) = j.1 := by omega
          simp only [h5] at h4
          exact h4
    constructor
    · rintro ⟨hl, hr⟩
      obtain ⟨a, b, c⟩ := hinr.1 hr
      exact ⟨a, b, c, hlat.1 hl⟩
    · rintro ⟨a, b, c, l⟩
      exact ⟨hlat.2 l, hinr.2 ⟨a, b, c⟩⟩

end GlobalTheory.LevZero

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormalCountLineIntegralitySeparationStatement
section
open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna Formalism.L2.SG.Pf.MainEqLoc Formalism.L2.SG.Pf.MainEqFam GlobalTheory.SnFam GlobalTheory.Core.One
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalCount_line_integrality_separation : Formalism.L2.SG.NGCut.NormalVectorPairings.NmlLine ∧ Formalism.L2.SG.NGCut.NormalVectorPairings.NmlInt ∧ Formalism.L2.SG.NGCut.NormalVectorPairings.NmlSep := by
  first | exact @GlobalTheory.Core.One.normalCountSteps | exact GlobalTheory.Core.One.normalCountSteps | (intros; apply GlobalTheory.Core.One.normalCountSteps <;> assumption)
end

