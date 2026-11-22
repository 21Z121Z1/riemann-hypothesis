import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.DataInst
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DensFrame
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0417
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0374
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0416
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0344
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0379
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0363
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0302
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitalIntegralsTermsOneDoubleCoset
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0046
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0261
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0194
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SameRowDoubleCosetInnerDataOneRationalClass

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GluedUnimodularLatticeIffLocalCompletions
section
noncomputable section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GenMass.GlueLoc

open Formalism.L2.SG.Pf Formalism.L2.SG.Pf.Cnt

variable {D : D7} (Z : LocDat D)

def locSp : Formalism.L2.SG.CntLocal.LocSp D Z.M where
  V := Vp D
  H := locH Z
  rank := finrank_Vp
  bc := baseChange₂ D
  bc_smul := baseChange_smul₂
  bc_span := span_baseChange_eq_top
  bc_form p := baseChangeAt_form Z.M p (Z.hcj p)

theorem eq_of_latP {A B : LV D} (hA : A.FG) (hB : B.FG) (h : ∀ p, lattice₂ D Z.M p A = lattice₂ D Z.M p B) : A = B := by
  apply eq_of_locP
  intro P
  exact (locEqC_holds D Z (P.under (𝓞 D.host.F)) A B hA hB).1 (h _) P rfl

theorem mem_of_bcP {Λ : LV D} (hΛ : Λ.FG) {x : (VS D).V} (h : ∀ p, baseChange₂ D p x ∈ lattice₂ D Z.M p Λ) : x ∈ Λ := by
  have e : Λ ⊔ Submodule.span (𝓞 D.host.E) {x} = Λ := by
    refine eq_of_latP Z (hΛ.sup (Submodule.fg_span_singleton x)) hΛ fun p => ?_
    rw [BBTie.latP_sup, BBTie.latP_span, sup_eq_left, Submodule.span_le]
    rintro _ ⟨y, rfl, rfl⟩
    exact h p
  rw [← e]
  exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)

theorem mem_dual_iff (Λ : LV D) (x : (VS D).V) :
    x ∈ Formalism.HermitianLatticesTheory.dual (VS D).hT Λ ↔ ∀ y ∈ Λ, (VS D).hT y x ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
  simp [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf]

theorem unimod_of_loc {Λ : LV D} (hΛ : Λ.FG) (hloc : ∀ p, (locH Z p).IsSelfDual (lattice₂ D Z.M p Λ)) :
    Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ := by
  have hf : ∀ p x y, (locH Z p).h (baseChange₂ D p x) (baseChange₂ D p y) = (D.s.atP p).ιE ((VS D).hT y x) :=
    fun p x y => baseChangeAt_form Z.M p (Z.hcj p) x y
  ext x
  rw [mem_dual_iff]
  constructor
  · intro h
    refine mem_of_bcP Z hΛ fun p => ((hloc p).2.2 _).2 fun w hw => ?_
    change LocFacts₂ Z.M p (baseChange₂ D p x) w ∈ _
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨y, hy, rfl⟩ := hw
      change (locH Z p).h _ _ ∈ _
      rw [hf]
      obtain ⟨o, ho⟩ := Submodule.mem_one.1 (h y hy)
      rw [← ho]
      exact BBTie.bt_iota_int Z p o
    | zero => rw [LocFacts.localForm_zero_right]; exact zero_mem _
    | add a b _ _ ha hb => rw [LocFacts.localForm_add_right]; exact add_mem ha hb
    | smul o w _ hw =>
      change LocFacts₂ Z.M p (baseChange₂ D p x) ((o : (D.s.atP p).Ep) • w) ∈ _
      rw [LocFacts.localForm_smul_right]
      exact mul_mem (LocFacts.lf_cjM_mem Z p _ o.2) hw
  · intro hx y hy
    refine DualityBasisChange.locGlobIntE D _ fun p => ?_
    rw [← hf, ← (Z.agree p).2.2.2.1]
    exact ((hloc p).2.2 (baseChange₂ D p x)).1 (Submodule.subset_span ⟨x, hx, rfl⟩) (baseChange₂ D p y)
      (Submodule.subset_span ⟨y, hy, rfl⟩)

variable (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) {T T' : D.host.E}
  (G : LFlag (VS D) D.R.rS T) (G' : LFlag (VS D) D.R.rS T')

theorem mmfam_eq (p : PlF D) (Λ : Submodule (Z.M p).L.O (Vp D p)) :
    (locH Z p).MMfam (tm FP G G' p Λ) = DualityBasisChange.locFam (locSp Z) Z.δ p G.fl G' := by
  funext b
  unfold Loc.HermSp.MMfam
  cases hs : (Z.M p).split with
  | none =>
    rw [DualityBasisChange.locFam_none (locSp Z) p G.fl G' hs]
    rcases b with a | a <;> rfl
  | some g =>
    rcases b with a | a
    · rw [DualityBasisChange.locFam_some_inl (locSp Z) p G.fl G' hs]; rfl
    · rw [DualityBasisChange.locFam_some_inr (locSp Z) p G.fl G' hs]; rfl

theorem span_mmfam (p : PlF D) (Λ : Submodule (Z.M p).L.O (Vp D p)) :
    Submodule.span (Z.M p).L.O (Set.range ((locH Z p).MMfam (tm FP G G' p Λ))) =
      lattice₂ D Z.M p (MMof D G.fl G') := by
  rw [mmfam_eq]
  exact DualityBasisChange.span_locFam Z.agree (locSp Z) p G.fl G'

theorem mmof_latIn : IsLatIn (UPair D G.fl G') (MMof D G.fl G') := by
  rw [R3.MMof_eq]; exact R3.BB_latIn D G.fl G'

theorem spanE_mmfam (p : PlF D) (Λ : Submodule (Z.M p).L.O (Vp D p)) :
    Submodule.span (D.s.atP p).Ep (Set.range ((locH Z p).MMfam (tm FP G G' p Λ))) =
      Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (UPair D G.fl G' : Set (VS D).V)) := by
  rw [← BBTie.bt_spanEp_spanO Z p, span_mmfam, lattice₂, BBTie.bt_spanEp_spanO Z p, ← (mmof_latIn G G').2,
    BBTie.bt_spanEp_spanE]

theorem glue_iff_local : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (u u' : D.what₂.Word) (G : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (G' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)), LinearIndependent D.host.E (Sum.elim (frame G) (frame G')) → ∀ Λ : LV D, Λ ∈ Formalism.L2.SG.Pf.Cnt.GlueSet (VS D).hT (Formalism.L2.SG.Pf.Cnt.UPair D G.fl G') (Formalism.L2.SG.Pf.Cnt.MMof D G.fl G') ↔ Submodule.IsLattice D.host.E Λ ∧ ∀ p, (locH Z p).IsSelfDual (lattice₂ D Z.M p Λ) ∧ (∀ i, (locH Z p).MMfam (tm FP G G' p (lattice₂ D Z.M p Λ)) i ∈ lattice₂ D Z.M p Λ) ∧ ¬ LocNG.BBne (H := locH Z p) (tm FP G G' p (lattice₂ D Z.M p Λ)) := by
  intro D Z FP u u' G G' _ Λ
  constructor
  · rintro ⟨hL, hU, hM⟩
    refine ⟨hL, fun p => ?_⟩
    have hle : lattice₂ D Z.M p (MMof D G.fl G') ≤ lattice₂ D Z.M p Λ :=
      BBTie.latP_mono Z p (hM ▸ inf_le_left)
    refine ⟨BBTie.bt_selfDual Z (locUnimodC_holds D Z) p Λ hL hU, fun i => hle ?_, ?_⟩
    · rw [← span_mmfam Z FP G G' p (lattice₂ D Z.M p Λ)]
      exact Submodule.subset_span ⟨i, rfl⟩
    · rw [BBTie.bt_bbne_iff Z p (locSatC_holds D Z) (tm FP G G' p (lattice₂ D Z.M p Λ)) Λ
        (MMof D G.fl G') (UPair D G.fl G') hL.fg rfl
        (span_mmfam Z FP G G' p _) (spanE_mmfam Z FP G G' p _) hle, not_not]
      exact congrArg _ hM
  · rintro ⟨hL, h⟩
    refine ⟨hL, unimod_of_loc Z hL.fg fun p => (h p).1, ?_⟩
    refine eq_of_latP Z (Submodule.FG.of_le hL.fg inf_le_left) (mmof_latIn G G').1 fun p => ?_
    have hle : lattice₂ D Z.M p (MMof D G.fl G') ≤ lattice₂ D Z.M p Λ := by
      rw [← span_mmfam Z FP G G' p (lattice₂ D Z.M p Λ), Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact (h p).2.1 i
    have h3 := (h p).2.2
    rw [BBTie.bt_bbne_iff Z p (locSatC_holds D Z) (tm FP G G' p (lattice₂ D Z.M p Λ)) Λ
        (MMof D G.fl G') (UPair D G.fl G') hL.fg rfl
      (span_mmfam Z FP G G' p _) (spanE_mmfam Z FP G G' p _) hle, not_not] at h3
    exact h3

end GlobalTheory.GenMass.GlueLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemRootsPointMatrixIffSameBlock
section
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RootsBijection

open Formalism.L2.SG.RealObj in
theorem fwd {K : Type*} [Zero K] : ∀ (bs : List (K × ℕ)) (i j a b : ℕ), Formalism.MainNotions.S.ptEntry bs i a ≠ 0 →
    Formalism.MainNotions.S.ptEntry bs j b ≠ 0 → a < b → j < i → blkOf bs a = blkOf bs b
  | [], _, _, _, _, h, _, _, _ => by simp [Formalism.MainNotions.S.ptEntry] at h
  | (t, s) :: bs, i, j, a, b, h1, h2, hab, hji => by
    rw [Formalism.MainNotions.S.ptEntry] at h1 h2
    by_cases ha : a < s
    · by_cases hb : b < s
      · simp [blkOf, ha, hb]
      · exfalso
        rw [if_neg (show ¬ (j < s ∧ b < s) by omega)] at h2
        by_cases hj : s ≤ j
        · rw [if_neg (show ¬ (s ≤ i ∧ s ≤ a) by omega)] at h1
          by_cases hi : i < s
          · omega
          · rw [if_neg (show ¬ (i < s ∧ a < s) by omega)] at h1; exact h1 rfl
        · rw [if_neg (show ¬ (s ≤ j ∧ s ≤ b) by omega)] at h2; exact h2 rfl
    · have hb : ¬ b < s := by omega
      rw [if_neg (show ¬ (i < s ∧ a < s) by omega)] at h1
      rw [if_neg (show ¬ (j < s ∧ b < s) by omega)] at h2
      by_cases hi : s ≤ i
      · by_cases hj : s ≤ j
        · rw [if_pos ⟨hi, by omega⟩] at h1
          rw [if_pos ⟨hj, by omega⟩] at h2
          have := fwd bs (i - s) (j - s) (a - s) (b - s) h1 h2 (by omega) (by omega)
          simp [blkOf, ha, hb, this]
        · rw [if_neg (show ¬ (s ≤ j ∧ s ≤ b) by omega)] at h2; exact absurd rfl h2
      · rw [if_neg (show ¬ (s ≤ i ∧ s ≤ a) by omega)] at h1; exact absurd rfl h1

open Formalism.L2.SG.RealObj in
theorem bwd {K : Type*} [Zero K] : ∀ (bs : List (K × ℕ)), (∀ p ∈ bs, p.1 ≠ 0) → ∀ (a b : ℕ), a < b →
    b < (bs.map Prod.snd).sum → blkOf bs a = blkOf bs b →
    ∃ i j, j < i ∧ i < (bs.map Prod.snd).sum ∧ Formalism.MainNotions.S.ptEntry bs i a ≠ 0 ∧ Formalism.MainNotions.S.ptEntry bs j b ≠ 0
  | [], _, _, _, _, hb, _ => by simp at hb
  | (t, s) :: bs, hnz, a, b, hab, hbs, hbl => by
    have ht : t ≠ 0 := hnz (t, s) (by simp)
    simp only [List.map_cons, List.sum_cons] at hbs ⊢
    by_cases ha : a < s
    · have hb : b < s := by
        by_contra hb
        simp [blkOf, ha, hb] at hbl
      refine ⟨s - 1 - a, s - 1 - b, by omega, by omega, ?_, ?_⟩
      · rw [Formalism.MainNotions.S.ptEntry, if_pos ⟨by omega, ha⟩, if_pos (by omega)]; exact ht
      · rw [Formalism.MainNotions.S.ptEntry, if_pos ⟨by omega, hb⟩, if_pos (by omega)]; exact ht
    · have hb : ¬ b < s := by omega
      have hbl' : blkOf bs (a - s) = blkOf bs (b - s) := by
        simpa [blkOf, ha, hb] using hbl
      obtain ⟨i, j, hji, his, hi, hj⟩ := bwd bs (fun p hp => hnz p (by simp [hp])) (a - s) (b - s) (by omega)
        (by omega) hbl'
      refine ⟨i + s, j + s, by omega, by omega, ?_, ?_⟩
      · rw [Formalism.MainNotions.S.ptEntry, if_neg (by omega), if_pos ⟨by omega, by omega⟩]; simpa using hi
      · rw [Formalism.MainNotions.S.ptEntry, if_neg (by omega), if_pos ⟨by omega, by omega⟩]; simpa using hj

end GlobalTheory.RootsBijection

theorem GlobalTheory.roots_ptMat_iff : ∀ (K : Type) [Field K] (n : ℕ) (w : Point K n) (a b : Fin n),
    (a, b) ∈ GlobalTheory.LoopV.roots (ptMat w) ↔ a < b ∧ Formalism.L2.SG.RealObj.blkOf w.1 a.1 = Formalism.L2.SG.RealObj.blkOf w.1 b.1 := by
  intro K _ n w a b
  unfold GlobalTheory.LoopV.roots
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  simp only [ptMat]
  constructor
  · rintro ⟨hab, i, j, hji, hi, hj⟩
    exact ⟨hab, GlobalTheory.RootsBijection.fwd w.1 i.1 j.1 a.1 b.1 hi hj hab hji⟩
  · rintro ⟨hab, hbl⟩
    obtain ⟨i, j, hji, hin, hi, hj⟩ := GlobalTheory.RootsBijection.bwd w.1 (fun p hp => (w.2.1 p hp).1) a.1 b.1 hab
      (by rw [w.2.2]; exact b.2) hbl
    rw [w.2.2] at hin
    exact ⟨hab, ⟨i, hin⟩, ⟨j, by omega⟩, hji, hi, hj⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitCountRowsDoubleCosetsInnerDatumClass
section
noncomputable section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OrbitCount

theorem relIndex_prod_prod {G G' : Type} [Group G] [Group G'] (H K : Subgroup G) (H' K' : Subgroup G') :
    (H.prod H').relIndex (K.prod K') = H.relIndex K * H'.relIndex K' := by
  unfold Subgroup.relIndex
  rw [← Subgroup.index_prod,
    ← Subgroup.index_comap_of_surjective ((H.subgroupOf K).prod (H'.subgroupOf K'))
      (f := (Subgroup.prodEquiv K K').toMonoidHom) (Subgroup.prodEquiv K K').surjective]
  congr 1

theorem card_image_eq_relIndex {Γ α : Type} [Group Γ] (P B : Subgroup Γ) (f : Γ → α)
    (hf : ∀ p ∈ P, ∀ q ∈ P, f p = f q ↔ p⁻¹ * q ∈ B) :
    Nat.card (f '' (P : Set Γ)) = B.relIndex P := by
  unfold Subgroup.relIndex Subgroup.index
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (Quotient.lift (s := QuotientGroup.leftRel (B.subgroupOf P))
      (fun p : P => (⟨f p, p, p.2, rfl⟩ : f '' (P : Set Γ))) ?_) ⟨?_, ?_⟩)
  · intro a b h
    have h' := QuotientGroup.leftRel_apply.mp h
    apply Subtype.ext
    exact (hf a a.2 b b.2).2 (by simpa [Subgroup.mem_subgroupOf] using h')
  · intro x y hxy
    induction x using Quotient.inductionOn with | h a => ?_
    induction y using Quotient.inductionOn with | h b => ?_
    apply Quotient.sound
    apply QuotientGroup.leftRel_apply.mpr
    have := congrArg Subtype.val hxy
    simp only [Quotient.lift_mk] at this
    simpa [Subgroup.mem_subgroupOf] using (hf a a.2 b b.2).1 this
  · rintro ⟨_, p, hp, rfl⟩
    exact ⟨Quotient.mk _ ⟨p, hp⟩, rfl⟩

theorem lrel_refl {D : D7} {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') (Λ : LV D) :
    LRel F F' Λ Λ := by
  refine ⟨1, ⟨(Formalism.HermitianLatticesTheory.isom (VS D).hT).one_mem, fun a => rfl, fun a => rfl⟩, ?_⟩
  congr 1
  simp [Formalism.HermitianLatticesTheory.gmap]

end GlobalTheory.OrbitCount

namespace GlobalTheory.OrbitCount

theorem orbit_count : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (t₀ : TauC Y u u') (Λ₀ : LV D), TG F F' t₀ Λ₀ → ∀ K, K = {κ | ∃ (t : TauC Y u u') (Λ₁ : LV D), TG F F' t Λ₁ ∧ LRel F F' Λ₀ Λ₁ ∧ key t = κ} → K.Finite ∧ (∀ κ ∈ K, ∃ t : TauC Y u u', TG F F' t Λ₀ ∧ key t = κ) ∧ (∀ (t : TauC Y u u') (Λ₁ : LV D), TG F F' t Λ₁ → LRel F F' Λ₀ Λ₁ → wt t = wt t₀) ∧ (K.encard : ℝ≥0∞) * ENNReal.ofReal (wt t₀ ^ 2) = (((stabL F F' Λ₀).encard : ℝ≥0∞))⁻¹ := by
  intro D X Y u u' F F' w hw hG t₀ Λ₀ h₀ K hK
  obtain ⟨A, N, hA, hN, hNA, hNn, hiA, hcA⟩ := GlobalTheory.T.rowLattice_automorphisms_eq_adapted_mod_unipotent D X Y u u' t₀.lam t₀.mem
  obtain ⟨A', N', hA', hN', hNA', hNn', hiA', hcA'⟩ := GlobalTheory.T.rowLattice_automorphisms_eq_adapted_mod_unipotent D X Y u' u t₀.lam' t₀.mem'
  obtain ⟨B, hB, hNB, hBiff⟩ := GlobalTheory.T.exists_subgroup_unitriangular_pairs_keeping_doubleCoset D X Y u u' t₀
  have hS := GlobalTheory.T.card_stabilizer_innerDatum_rowDoubleCoset D X Y u u' F F' w hw hG t₀ Λ₀ h₀ B N N' hB hN hN'
  have mA : ∀ a, a ∈ A ↔ a ∈ Aut0 (lf D (X.Fu u)) t₀.lam := fun a => SetLike.mem_coe.symm.trans (Set.ext_iff.mp hA a)
  have mA' : ∀ a, a ∈ A' ↔ a ∈ Aut0 (lf D (X.Fu u')) t₀.lam' := fun a => SetLike.mem_coe.symm.trans (Set.ext_iff.mp hA' a)
  have mN : ∀ a, a ∈ N ↔ a ∈ NLam t₀.lam (lf D (X.Fu u)) := fun a => SetLike.mem_coe.symm.trans (Set.ext_iff.mp hN a)
  have mN' : ∀ a, a ∈ N' ↔ a ∈ NLam t₀.lam' (lf D (X.Fu u')) := fun a => SetLike.mem_coe.symm.trans (Set.ext_iff.mp hN' a)
  set P : Subgroup (GV D × GV D) := A.prod A' with hP
  have htr : ∀ p : GV D × GV D, ∃ s : TauC Y u u', p ∈ P → (s.lam = t₀.lam ∧ s.lam' = t₀.lam' ∧
      ∃ n ∈ NLam t₀.lam (lf D (X.Fu u)), ∃ n' ∈ NLam t₀.lam' (lf D (X.Fu u')), s.lin = n * (p.1 * t₀.lin * p.2⁻¹) * n') := by
    intro p
    by_cases hp : p ∈ P
    · obtain ⟨s, h1, h2, n, hn, n', hn', h3⟩ := GlobalTheory.T.exists_term_translate_by_adapted_lattice_automorphisms D X Y u u' t₀ p.1 ((mA _).1 hp.1) p.2 ((mA' _).1 hp.2)
      exact ⟨s, fun _ => ⟨h1, h2, n, hn, n', hn', h3⟩⟩
    · exact ⟨t₀, fun h => absurd h hp⟩
  choose s hs using htr
  have hTG : ∀ p ∈ P, TG F F' (s p) Λ₀ := by
    intro p hp
    obtain ⟨h1, -, n, hn, n', hn', h3⟩ := hs p hp
    exact GlobalTheory.T.baseFrameLattice_invariant_under_adapted_translate D X Y u u' F F' t₀ (s p) Λ₀ p.1 p.2 n n' h₀ ((mA _).1 hp.1) ((mA' _).1 hp.2) hn hn' h1 h3

  have hfib : ∀ p ∈ P, ∀ q ∈ P, key (s p) = key (s q) ↔ p⁻¹ * q ∈ B := by
    intro p hp q hq
    obtain ⟨hp1, hp2, n, hn, n', hn', hpl⟩ := hs p hp
    obtain ⟨hq1, hq2, m, hm, m', hm', hql⟩ := hs q hq
    rw [GlobalTheory.T.term_row_double_coset_eq_iff_isometries D X Y u u' (s p) (s q), hp1, hq1, hp2, hq2]
    simp only [true_and]
    have ep : (s p).lin = (n * p.1) * t₀.lin * (n'⁻¹ * p.2)⁻¹ := by rw [hpl]; group
    have eq : (s q).lin = (m * q.1) * t₀.lin * (m'⁻¹ * q.2)⁻¹ := by rw [hql]; group
    have hnA : n ∈ A := hNA ((mN n).2 hn)
    have hmA : m ∈ A := hNA ((mN m).2 hm)
    have hnA' : n'⁻¹ ∈ A' := A'.inv_mem (hNA' ((mN' n').2 hn'))
    have hmA' : m'⁻¹ ∈ A' := A'.inv_mem (hNA' ((mN' m').2 hm'))
    rw [ep, eq, hBiff (n * p.1) ((mA _).1 (A.mul_mem hnA hp.1)) (m * q.1) ((mA _).1 (A.mul_mem hmA hq.1))
      (n'⁻¹ * p.2) ((mA' _).1 (A'.mul_mem hnA' hp.2)) (m'⁻¹ * q.2) ((mA' _).1 (A'.mul_mem hmA' hq.2))]
    have hx : p.1⁻¹ * (n⁻¹ * m) * p.1⁻¹⁻¹ ∈ N :=
      hNn _ (A.inv_mem hp.1) _ (N.mul_mem (N.inv_mem ((mN n).2 hn)) ((mN m).2 hm))
    have hx' : p.2⁻¹ * (n' * m'⁻¹) * p.2⁻¹⁻¹ ∈ N' :=
      hNn' _ (A'.inv_mem hp.2) _ (N'.mul_mem ((mN' n').2 hn') (N'.inv_mem ((mN' m').2 hm')))
    have hmB : (p.1⁻¹ * (n⁻¹ * m) * p.1⁻¹⁻¹, p.2⁻¹ * (n' * m'⁻¹) * p.2⁻¹⁻¹) ∈ B :=
      hNB _ ((mN _).1 hx) _ ((mN' _).1 hx')
    have heq : ((n * p.1)⁻¹ * (m * q.1), (n'⁻¹ * p.2)⁻¹ * (m'⁻¹ * q.2)) =
        (p.1⁻¹ * (n⁻¹ * m) * p.1⁻¹⁻¹, p.2⁻¹ * (n' * m'⁻¹) * p.2⁻¹⁻¹) * (p⁻¹ * q) := by
      ext <;> simp only [Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv] <;> group
    rw [heq, B.mul_mem_cancel_left hmB]

  have hKim : K = (fun p => key (s p)) '' (P : Set (GV D × GV D)) := by
    rw [hK]
    ext κ
    constructor
    · rintro ⟨t, Λ₁, ht, hrel, rfl⟩
      obtain ⟨a, ha, a', ha', hkey⟩ := GlobalTheory.T.matching_translate_same_row_double_coset D X Y u u' F F' w hw hG t₀ t Λ₀ Λ₁ h₀ ht hrel
      have hp : (a, a') ∈ P := ⟨(mA a).2 ha, (mA' a').2 ha'⟩
      obtain ⟨h1, h2, n, hn, n', hn', h3⟩ := hs (a, a') hp
      exact ⟨(a, a'), hp, hkey (s (a, a')) h1 h2 ⟨n, hn, n', hn', h3⟩⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨s p, Λ₀, hTG p hp, lrel_refl F F' Λ₀, rfl⟩
  have hcardK : Nat.card K = B.relIndex P := by
    rw [hKim]; exact card_image_eq_relIndex P B _ hfib
  have hBP : B ≤ P := fun b hb => ⟨(mA _).2 ((hB b).1 hb).1, (mA' _).2 ((hB b).1 hb).2.1⟩
  have hNNB : N.prod N' ≤ B := fun b hb => by
    have := hNB b.1 ((mN _).1 hb.1) b.2 ((mN' _).1 hb.2)
    simpa using this
  have hprod : (N.prod N').relIndex B * B.relIndex P = Nat.card (autLz D (X.Fu u) t₀.lam) * Nat.card (autLz D (X.Fu u') t₀.lam') := by
    rw [Subgroup.relIndex_mul_relIndex _ _ _ hNNB hBP, hP, relIndex_prod_prod, hiA, hiA']
  set k := B.relIndex P with hk
  set m := (N.prod N').relIndex B with hm
  set c := Nat.card (autLz D (X.Fu u) t₀.lam) with hc
  set c' := Nat.card (autLz D (X.Fu u') t₀.lam') with hc'
  have hmk : 0 < m * k := by rw [hprod]; exact Nat.mul_pos hcA hcA'
  have hk0 : 0 < k := Nat.pos_of_mul_pos_left hmk
  have hm0 : 0 < m := Nat.pos_of_mul_pos_right hmk
  have hKfin : K.Finite := by
    have : 0 < Nat.card K := hcardK ▸ hk0
    exact Set.finite_coe_iff.mp (Nat.card_pos_iff.mp this).2
  have hSfin : (stabL F F' Λ₀).Finite := by
    have : 0 < Nat.card (stabL F F' Λ₀) := hS ▸ hm0
    exact Set.finite_coe_iff.mp (Nat.card_pos_iff.mp this).2
  have hKenc : K.encard = (k : ℕ∞) := by
    rw [← hKfin.cast_ncard_eq, ← Nat.card_coe_set_eq, hcardK]
  have hSenc : (stabL F F' Λ₀).encard = (m : ℕ∞) := by
    rw [← hSfin.cast_ncard_eq, ← Nat.card_coe_set_eq, hS]
  have hwt : ∀ (t : TauC Y u u'), t.lam = t₀.lam → t.lam' = t₀.lam' → wt t = wt t₀ := by
    intro t h1 h2
    simp only [wt, h1, h2]
  refine ⟨hKfin, ?_, ?_, ?_⟩
  · intro κ hκ
    rw [hKim] at hκ
    obtain ⟨p, hp, rfl⟩ := hκ
    exact ⟨s p, hTG p hp, rfl⟩
  · intro t Λ₁ ht hrel
    obtain ⟨h1, h2, -⟩ := GlobalTheory.T.terms_same_rational_inner_class_are_translates D X Y u u' F F' w hw hG t₀ t Λ₀ Λ₁ h₀ ht hrel
    exact hwt t h1 h2
  · have hw2 : wt t₀ ^ 2 = (c : ℝ)⁻¹ * (c' : ℝ)⁻¹ := by
      simp only [wt]
      rw [Real.sq_sqrt (by unfold wRow; positivity)]
      rfl
    rw [hKenc, hSenc, hw2, ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_inv_of_pos (by exact_mod_cast hcA), ENNReal.ofReal_inv_of_pos (by exact_mod_cast hcA'),
      ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
    have hcc : ((c : ℝ≥0∞))⁻¹ * ((c' : ℝ≥0∞))⁻¹ = ((m : ℝ≥0∞))⁻¹ * ((k : ℝ≥0∞))⁻¹ := by
      rw [← ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _)),
        ← ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _))]
      congr 1
      exact_mod_cast hprod.symm
    simp only [ENat.toENNReal_coe]
    rw [hcc, mul_comm, mul_assoc, ENNReal.inv_mul_cancel (by exact_mod_cast hk0.ne') (ENNReal.natCast_ne_top _), mul_one]

end GlobalTheory.OrbitCount
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitalIntegralsTermsOneDoubleCosetStatement
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbital_integrals_terms_one_doubleCoset : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → ∀ ν, Formalism.L2.SG.RealObj.NuQPin X u u' ν → ∀ t₀ : TauC Y u u', t₀.relevant → t₀.G ≠ 0 → ∀ w, w = Formalism.L2.SG.PairVal.ptOf t₀.toTerm → (∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u' w g) ∧ ∃ T : X.Vpi u' →L[ℂ] X.Vpi u, ‖Formalism.L2.SG.PackageTie.hsEmb T‖ = ‖Formalism.L2.SG.PackageTie.hsEmb (haveI := FiniteDimensional.complete ℂ (X.Vpi u); OO (ν (Formalism.L2.SG.RealObj.gamW X u u' w)) Set.univ (X.Wu u) (X.Wu u') (Formalism.L2.SG.RealObj.gamW X u u' w))‖ ∧ ∀ (t : TauC Y u u') (n m : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (xn xm : X.B.I.GA), n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧ t.lin = n⁻¹ * t₀.lin * m → RatLink X xn n → RatLink X xm m → ∃ (μR : Measure X.B.I.Ginf) (K : Set X.B.I.Ginf), Formalism.L2.SG.VolPin.IsPinnedR t w μR ∧ (MeasurableSet K ∧ ∀ y ∈ Formalism.L2.SG.TermOp.Vanish.Rset t, ∃! s, s ∈ ROinf t ∧ s * y ∈ K) ∧ OOt t = (((μR K).toReal : ℂ) * ((X.psiInfU u xn.1)⁻¹ * X.psiInfU u' xm.1)) • T := by
  first | exact @GlobalTheory.CosetOrbital.coset_orbital_form | exact GlobalTheory.CosetOrbital.coset_orbital_form | (intros; apply GlobalTheory.CosetOrbital.coset_orbital_form <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RMeasExAll
section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LocWSOf Formalism.L2.SG.LoopTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RMeasAll

theorem rMeasEx_all : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (sOf hF)) (C : Choice X 1) (u u' : D.what₂.Word), (∀ τ, GoodW D τ u u' 1 (locW C u u' τ)) → RMeasEx hI C u u' := by
  intro D X Y hF hI C u u' hW t hG hr τ
  obtain ⟨_, _, h3, h4, h5, h6, h7, _⟩ := hW τ
  have hTu : 0 < Formalism.MainNotions.S.Tr D u := Nat.cast_pos.2 (D.mem u).A.T_prime.pos
  have hTu' : 0 < Formalism.MainNotions.S.Tr D u' := Nat.cast_pos.2 (D.mem u').A.T_prime.pos
  obtain ⟨p, hp⟩ := Formalism.L2.SG.LoopTerm.relPtEx_holds hI C u u' t hG hr τ
  exact GlobalTheory.Amp.RootQuot.exists_rMeas D (locW C u u' τ) _ p h3 h4 (by rw [h5]; exact hTu) (by rw [h6]; exact hTu') h7 hp

end GlobalTheory.RMeasAll
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RatCoordConjEqStCoord
section
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LoopVol

private theorem hJ_smul_right_flag_measures {n : ℕ} (ε : Fin n → Bool) (c : ℂ) (x y : Fin n → ℂ) :
    Formalism.L2.SG.HidaSetting.hJ ε x (c • y) = c * Formalism.L2.SG.HidaSetting.hJ ε x y := by
  unfold Formalism.L2.SG.HidaSetting.hJ
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem ratCoord_conj_eq_stCoord : ∀ (D : D7) (X : HidaSetting D) (u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) (γ s y : X.B.I.Ginf) (τ : D.what₂.Tau) (q : GlobalTheory.LoopV.roots (ptMat w)) (p : Formalism.L2.SG.RealObj.FreeE w), p.1 = q.1 → GlobalTheory.LoopVol.ratCoord X u' w γ s (s * y * s⁻¹) τ q = ((D.host.rdE : ℂ) ^ (q.1.2.1 - q.1.1.1))⁻¹ * Formalism.L2.SG.RealObj.stCoord X u' w γ y (X.pl.symm τ) p := by
  intro D X u' w γ s y τ q p hpq
  obtain ⟨pq, hp⟩ := p
  obtain ⟨qq, hq⟩ := q
  simp only at hpq
  subst hpq

  have hconj : s⁻¹ * (s * y * s⁻¹) * s = y := by group
  have hab : pq.1.val < pq.2.val := hp.1
  have hbr : pq.2.val ≤ D.R.rS := Nat.lt_succ_iff.mp pq.2.isLt
  have hrd : (D.host.rdE : ℂ) ≠ 0 := by
    have h1 := GlobalTheory.RealPlaces.one_le_rdE D
    exact Complex.ofReal_ne_zero.mpr (by linarith)
  unfold GlobalTheory.LoopVol.ratCoord Formalism.L2.SG.RealObj.stCoord
  rw [hconj]
  unfold Formalism.L2.SG.RealObj.frm Formalism.L2.SG.RealObj.famSc
  simp only [Complex.ofReal_one, one_pow, inv_one, one_smul, Matrix.mulVec_smul, hJ_smul_right_flag_measures]

  have hsplit : D.R.rS - pq.1.val = (pq.2.val - pq.1.val) + (D.R.rS - pq.2.val) := by omega
  rw [hsplit, pow_add]
  field_simp

end GlobalTheory.LoopVol
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SameRowDoubleCosetInnerDataOneRationalClassStatement
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.same_row_doubleCoset_inner_data_one_rational_class : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (t t' : TauC Y u u') (Λ₁ Λ₂ : LV D), TG F F' t Λ₁ → TG F F' t' Λ₂ → key t = key t' → LRel F F' Λ₁ Λ₂ := by
  first | exact @GlobalTheory.KeyRel.same_key_lrel | exact GlobalTheory.KeyRel.same_key_lrel | (intros; apply GlobalTheory.KeyRel.same_key_lrel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermsAtPointOfRelevantTermRelevantFiniteStatement
section
open Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermOp NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.terms_at_point_of_relevant_term_relevant_finite : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ t₀ : TauC Y u u', t₀.G ≠ 0 → t₀.relevant → ∃ w : Point D.host.E (D.R.rS + 1), toPts w = ptPN t₀ ∧ (∀ t : TauC Y u u', ptPN t = ptPN t₀ → t.relevant ∧ Gval (lf D (X.Fu u)) (Quot.out t.toTerm.cls).1 ≠ 0 ∧ IsInCell (ZhatOM (ZhatL (lf D (X.Fu u)) (Quot.out t.toTerm.cls).1)) w) ∧ (GTerm.toTerm '' {t : TauC Y u u' | ptPN t = ptPN t₀}).Finite := by
  first | exact @GlobalTheory.LocOver.terms_at_point_of_relevant | exact GlobalTheory.LocOver.terms_at_point_of_relevant | (intros; apply GlobalTheory.LocOver.terms_at_point_of_relevant <;> assumption)
end

