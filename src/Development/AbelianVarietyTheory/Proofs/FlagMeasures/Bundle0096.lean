import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairCommonUnipotentStabiliserSummary
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormGeometrySummary
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0040
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0061
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0092
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0091
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0078
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0080
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0064
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0088
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0084
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Cint
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0086
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0058
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesStabilizerActsOnTerms
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairCommonUnipotentStabiliserSummaryStatement
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermFramePairCommonUnipotentStabiliser_summary : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), (∀ s : V ≃ₗ[K] V, s ∈ N.R ↔ N.F.InN (s : V →ₗ[K] V) ∧ N.F'.InN (s : V →ₗ[K] V)) ∧ (∀ s ∈ N.R, ∀ y ∈ uPerp N.F N.F', s y - y ∈ II N.F N.F') ∧ (∀ s ∈ N.R, ∀ t ∈ N.R1, s * t * s⁻¹ ∈ N.R1) ∧ (∀ s ∈ N.R, ∀ t ∈ N.ZI, s * t * s⁻¹ ∈ N.ZI) ∧ ∀ s ∈ N.R, ((s : V →ₗ[K] V) - 1) ^ (2 * r + 1) = 0 := by
  first | exact @GlobalTheory.UnipStab.common_unipotent_stabiliser | exact GlobalTheory.UnipStab.common_unipotent_stabiliser | (intros; apply GlobalTheory.UnipStab.common_unipotent_stabiliser <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormGeometrySummaryStatement
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermFramePairNormalForm_geometry_summary : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), NFFull N.F N.F' N.j N.j_le N.c ∧ IsLift N.F N.F' N.Wt ∧ IsCompl N.Wt N.Pi ∧ Module.finrank K N.Wt + 2 * r + 1 = Module.finrank K V ∧ N.Wn = N.Wt ⊔ Submodule.span K {N.F.z} ∧ uPerp N.F N.F' = N.Wn ⊔ II N.F N.F' ∧ wSp N.F N.F' = N.Wt ⊔ II N.F N.F' ∧ wSp N.F' N.F = wSp N.F N.F' ∧ GlobalTheory.Mass.PD (GlobalTheory.Mass.hRes H.B.flip N.Wt) ∧ 1 ≤ N.T ∧ N.nD N.j ≠ 0 ∧ N.Pi = V0 N.F N.F' ⊔ N.Ist := by
  first | exact @GlobalTheory.DegCnt.NF.geometry | exact GlobalTheory.DegCnt.NF.geometry | (intros; apply GlobalTheory.DegCnt.NF.geometry <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetInFamilyMovedOfNotLeak
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.OffLeak

theorem ncard_image_eq_of_iff {α β γ : Type*} (B : Set α) (f : α → β) (g : α → γ)
    (h : ∀ a ∈ B, ∀ b ∈ B, f a = f b ↔ g a = g b) : (f '' B).ncard = (g '' B).ncard := by
  classical
  refine Set.ncard_congr (fun c hc => g (Classical.choose ((Set.mem_image f B c).1 hc))) ?_ ?_ ?_
  · intro c hc
    exact ⟨_, (Classical.choose_spec ((Set.mem_image f B c).1 hc)).1, rfl⟩
  · intro c c' hc hc' hgg
    have e₁ := Classical.choose_spec ((Set.mem_image f B c).1 hc)
    have e₂ := Classical.choose_spec ((Set.mem_image f B c').1 hc')
    exact e₁.2.symm.trans (((h _ e₁.1 _ e₂.1).2 hgg).trans e₂.2)
  · rintro _ ⟨a, ha, rfl⟩
    have hfa : f a ∈ f '' B := ⟨a, ha, rfl⟩
    refine ⟨f a, hfa, ?_⟩
    have e := Classical.choose_spec ((Set.mem_image f B (f a)).1 hfa)
    exact (h _ e.1 _ ha).1 e.2

theorem coset_eq_iff {R V : Type*} [Ring R] [AddCommGroup V] [Module R V] (M : Submodule R V) (a b : V) :
    ({x | x - a ∈ M} : Set V) = {x | x - b ∈ M} ↔ a - b ∈ M := by
  constructor
  · intro h
    have ha : a ∈ ({x | x - a ∈ M} : Set V) := by simp
    rw [h] at ha
    exact ha
  · intro h
    ext x
    constructor
    · intro hx
      have hxb : (x - a) + (a - b) ∈ M := M.add_mem hx h
      have e : (x - a) + (a - b) = x - b := by abel
      rw [e] at hxb
      exact hxb
    · intro hx
      have hxa : (x - b) - (a - b) ∈ M := M.sub_mem hx h
      have e : (x - b) - (a - b) = x - a := by abel
      rw [e] at hxa
      exact hxa

theorem relIndex_eq_of_reps {R V : Type*} [Ring R] [AddCommGroup V] [Module R V] (M T B : Submodule R V)
    (hM : M ≤ T) (hB : B ≤ T) (h : ∀ y ∈ T, ∃ y₀ ∈ B, y - y₀ ∈ M) :
    M.toAddSubgroup.relIndex T.toAddSubgroup =
      (M.toAddSubgroup ⊓ B.toAddSubgroup).relIndex B.toAddSubgroup := by
  have hT : T.toAddSubgroup = B.toAddSubgroup ⊔ M.toAddSubgroup := by
    apply le_antisymm
    · intro y hy
      obtain ⟨y₀, hy₀, hm⟩ := h y hy
      have hs : y₀ + (y - y₀) ∈ B.toAddSubgroup ⊔ M.toAddSubgroup :=
        AddSubgroup.add_mem_sup hy₀ hm
      have e : y₀ + (y - y₀) = y := by abel
      rw [e] at hs
      exact hs
    · exact sup_le (fun x hx => hB hx) (fun x hx => hM hx)
  rw [hT, AddSubgroup.relIndex_sup_right, AddSubgroup.inf_relIndex_right]

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem spanTo_mono {L : LocE F E} {r k : ℕ} (S : Frames L r k) (g : Fin (r + 1) → S.V) {a b : ℕ}
    (h : a ≤ b) : S.spanTo g a ≤ S.spanTo g b := by
  unfold Frames.spanTo
  apply Submodule.span_mono
  rintro _ ⟨i, hi, rfl⟩
  exact ⟨i, lt_of_lt_of_le hi h, rfl⟩

theorem th_ne_zero {L : LocE F E} {r k : ℕ} (S : Frames L r k) : S.th ≠ 0 := by
  unfold Frames.th
  split_ifs
  · intro h0
    apply S.ϖ_irr.ne_zero
    exact Subtype.ext h0
  · exact one_ne_zero
set_option maxHeartbeats 1000000 in

theorem inFF_moved_of_not_leak : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → ∀ x x' u s, S.IsMove (j + 1) d Λ x x' u s → (∃ y ∈ Λ, y ∈ S.W0 ∧ S.h u y = 1) → ∀ Λ₁ : Submodule L.O S.V, (Λ₁ : Set S.V) = S.moved Λ x u s → S.InFF β (j + 1) βJ d Λ₁ := by
  intro F _ _ _ _ _ E _ _ _ L r k S j β βJ d Λ hT hF x x' u s hMv hleak Λ₁ hΛ₁
  obtain ⟨hT₁, hY⟩ := GlobalTheory.T.hermitianMove_preserves_frameLattice_levels L r k S j β βJ d Λ hT hF x x' u s hMv Λ₁ hΛ₁
  have h78 := GlobalTheory.T.hermitianDefectClass_mem_trace_firstFrameSpan L r k S j β βJ d Λ hT hF x x' u s hMv hleak Λ₁ hΛ₁
  have h64 := GlobalTheory.T.termLevel_zero_and_bounded_representatives L r k S d Λ hT
  have h64₁ := GlobalTheory.T.termLevel_zero_and_bounded_representatives L r k S d Λ₁ hT₁
  have hMs : S.M d Λ ≤ S.sat Λ := (GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT).2.2.1
  have hMs₁ : S.M d Λ₁ ≤ S.sat Λ₁ := (GlobalTheory.HL.TermBasic.term_basic L r k S d Λ₁ hT₁).2.2.1
  unfold Frames.InFF at hF ⊢
  obtain ⟨hTB, hbe, hle, ⟨z, hz, hzJ⟩, hn⟩ := hF
  unfold Frames.TypeBe at hTB
  obtain ⟨Y, hYdef⟩ : ∃ Y : Submodule E S.V, Y = S.spanTo S.f (↑j + 1) ⊔ S.spanTo S.f' (↑j + 1) :=
    ⟨_, rfl⟩
  have hYmem : ∀ y, y ∈ Y ↔ y ∈ S.spanTo S.f (↑j + 1) ⊔ S.spanTo S.f' (↑j + 1) := by
    intro y
    rw [hYdef]
  have hjr : (j : ℕ) + 1 ≤ r := j.isLt
  have hjr' : (j : ℕ) + 1 ≤ r + 1 := by omega
  have hYME : Y ≤ S.ME := by
    rw [hYdef]
    exact sup_le_sup (spanTo_mono S S.f hjr') (spanTo_mono S S.f' hjr')
  have hYX : Y ≤ S.X ⊔ S.X' := by
    rw [hYdef]
    exact sup_le_sup (spanTo_mono S S.f hjr) (spanTo_mono S S.f' hjr)
  have hYY : ∀ y ∈ Y, (y ∈ Λ → y ∈ Λ₁) ∧ (y ∈ S.M d Λ₁ ↔ y ∈ S.M d Λ) ∧
      S.lev (S.fr d Λ₁) (S.fr' d Λ₁) y = S.lev (S.fr d Λ) (S.fr' d Λ) y :=
    fun y hy => hY y ((hYmem y).1 hy)
  have memSat : ∀ (Λ' : Submodule L.O S.V) (y : S.V), y ∈ S.sat Λ' ↔ y ∈ Λ' ∧ y ∈ S.ME := by
    intro Λ' y
    unfold Frames.sat
    simp [Submodule.mem_inf]
  obtain ⟨B₀, hB₀⟩ : ∃ B₀ : Submodule L.O S.V, ∀ y, y ∈ B₀ ↔ y ∈ Λ ∧ y ∈ Y :=
    ⟨Λ ⊓ Y.restrictScalars L.O, fun y => by simp [Submodule.mem_inf]⟩
  have hB₀Y : ∀ y ∈ B₀, y ∈ Y := fun y hy => ((hB₀ y).1 hy).2
  have hB₀sat : ∀ y ∈ B₀, y ∈ S.sat Λ := fun y hy =>
    (memSat Λ y).2 ⟨((hB₀ y).1 hy).1, hYME (hB₀Y y hy)⟩
  have hB₀Λ₁ : ∀ y ∈ B₀, y ∈ Λ₁ := fun y hy => (hYY y (hB₀Y y hy)).1 ((hB₀ y).1 hy).1
  have hB₀sat₁ : ∀ y ∈ B₀, y ∈ S.sat Λ₁ := fun y hy =>
    (memSat Λ₁ y).2 ⟨hB₀Λ₁ y hy, hYME (hB₀Y y hy)⟩
  have hMiff : ∀ y ∈ B₀, (y ∈ S.M d Λ₁ ↔ y ∈ S.M d Λ) := fun y hy => (hYY y (hB₀Y y hy)).2.1
  have hlev : ∀ y ∈ B₀, S.levC d Λ₁ y = S.levC d Λ y := by
    intro y hy
    unfold Frames.levC
    exact (hYY _ (Y.smul_mem _ (hB₀Y y hy))).2.2

  have rep : ∀ y ∈ S.sat Λ, ∃ y₁ ∈ B₀, y - y₁ ∈ S.M d Λ := by
    intro y hy
    obtain ⟨y₁, hy₁Y, hm⟩ := (h64.2.1 y hy (↑j + 1)).1 (hle y hy)
    have hs : y - (y - y₁) ∈ S.sat Λ := (S.sat Λ).sub_mem hy (hMs hm)
    have e : y - (y - y₁) = y₁ := by abel
    rw [e] at hs
    exact ⟨y₁, (hB₀ y₁).2 ⟨((memSat Λ y₁).1 hs).1, (hYmem y₁).2 hy₁Y⟩, hm⟩

  have rep₁ : ∀ y ∈ S.sat Λ₁, ∃ y₀ ∈ B₀, y - y₀ ∈ S.M d Λ₁ := by
    intro y hy
    obtain ⟨y₀, h1, h2, h3⟩ := h78 y hy
    exact ⟨y₀, (hB₀ y₀).2 ⟨h1, (hYmem y₀).2 h2⟩, h3⟩

  have hinv : ∀ (Λ' : Submodule L.O S.V), S.IsTerm d Λ' → ∀ y ∈ S.sat Λ', ∀ y₁,
      y - y₁ ∈ S.M d Λ' → S.levC d Λ' y₁ = S.levC d Λ' y := by
    intro Λ' hT' y hy y₁ hm
    have hm' : -(y - y₁) ∈ S.M d Λ' := (S.M d Λ').neg_mem hm
    have e₁ : -(y - y₁) = y₁ - y := by abel
    rw [e₁] at hm'
    have hc := (GlobalTheory.T.termLevel_zero_and_bounded_representatives L r k S d Λ' hT').2.2.1 y hy (y₁ - y) hm'
    have e₂ : y + (y₁ - y) = y₁ := by abel
    rw [e₂] at hc
    exact hc

  have hbe₁ : S.be d Λ₁ = S.be d Λ := by
    unfold Frames.be
    rw [relIndex_eq_of_reps (S.M d Λ₁) (S.sat Λ₁) B₀ hMs₁ (fun y hy => hB₀sat₁ y hy) rep₁,
      relIndex_eq_of_reps (S.M d Λ) (S.sat Λ) B₀ hMs (fun y hy => hB₀sat y hy) rep]
    congr 1
    ext y
    simp only [AddSubgroup.mem_inf, Submodule.mem_toAddSubgroup]
    exact ⟨fun h => ⟨(hMiff y h.2).1 h.1, h.2⟩, fun h => ⟨(hMiff y h.2).2 h.1, h.2⟩⟩

  have hth : S.th ≠ 0 := th_ne_zero S
  have hInTh : ∀ w : S.V, algebraMap F E S.th⁻¹ • w ∈ (B₀ : Set S.V) → S.InTh Λ w := by
    intro w hw
    refine ⟨_, ((hB₀ _).1 hw).1, ?_⟩
    rw [smul_smul, ← map_mul, mul_inv_cancel₀ hth, map_one, one_smul]
  have hnotBB : ¬ S.BBzero d Λ₁ := by
    intro hbb
    apply hTB.1
    unfold Frames.BBzero at hbb ⊢
    refine le_antisymm hMs ?_
    intro y hy
    obtain ⟨y₁, hy₁, hm⟩ := rep y hy
    have h1 : y₁ ∈ S.M d Λ₁ := by
      rw [hbb]
      exact hB₀sat₁ y₁ hy₁
    have h2 : (y - y₁) + y₁ ∈ S.M d Λ := (S.M d Λ).add_mem hm ((hMiff y₁ hy₁).1 h1)
    have e : (y - y₁) + y₁ = y := by abel
    rw [e] at h2
    exact h2
  have hTB₁ : S.TypeBe d Λ₁ :=
    GlobalTheory.T.pairing_second_type_test_on_representatives L r k S d Λ₁ hT₁ hnotBB (B₀ : Set S.V)
      (fun y hy => ⟨hB₀Λ₁ y hy, hYX (hB₀Y y hy)⟩) rep₁
      (fun x₁ hx₁ x₁' hx₁' x₂ hx₂ x₂' hx₂' h1 h2 =>
        hTB.2.2 x₁ hx₁ x₁' hx₁' x₂ hx₂ x₂' hx₂' (hInTh _ h1) (hInTh _ h2))

  have hle₁ : ∀ y ∈ S.sat Λ₁, S.levC d Λ₁ y ≤ ↑j + 1 := by
    intro y hy
    obtain ⟨y₀, hy₀, hm⟩ := rep₁ y hy
    have hy0 : y₀ ∈ S.spanTo S.f (↑j + 1) ⊔ S.spanTo S.f' (↑j + 1) := (hYmem y₀).1 (hB₀Y y₀ hy₀)
    have key := (h64₁.2.1 y hy (↑j + 1)).2
    have ex : ∃ y₁ ∈ S.spanTo S.f (↑j + 1) ⊔ S.spanTo S.f' (↑j + 1), y - y₁ ∈ S.M d Λ₁ :=
      ⟨y₀, hy0, hm⟩
    exact key ex
  have hex₁ : ∃ y ∈ S.sat Λ₁, S.levC d Λ₁ y = ↑j + 1 := by
    obtain ⟨y₁, hy₁, hm⟩ := rep z hz
    refine ⟨y₁, hB₀sat₁ y₁ hy₁, ?_⟩
    rw [hlev y₁ hy₁, hinv Λ hT z hz y₁ hm, hzJ]

  have hset : ∀ (Λ' : Submodule L.O S.V), S.IsTerm d Λ' → (∀ y ∈ B₀, y ∈ S.sat Λ') →
      (∀ y ∈ S.sat Λ', ∃ y₀ ∈ B₀, y - y₀ ∈ S.M d Λ') →
      {C : Set S.V | ∃ y ∈ S.sat Λ', S.levC d Λ' y = ↑j + 1 ∧ C = {x | x - y ∈ S.M d Λ'}} =
        (fun y => {x | x - y ∈ S.M d Λ'}) '' {y | y ∈ B₀ ∧ S.levC d Λ' y = ↑j + 1} := by
    intro Λ' hT' hBs hrep
    ext C
    constructor
    · rintro ⟨y, hy, hyJ, rfl⟩
      obtain ⟨y₀, hy₀, hm⟩ := hrep y hy
      refine ⟨y₀, ⟨hy₀, (hinv Λ' hT' y hy y₀ hm).trans hyJ⟩, ?_⟩
      have hm' : -(y - y₀) ∈ S.M d Λ' := (S.M d Λ').neg_mem hm
      have e : -(y - y₀) = y₀ - y := by abel
      rw [e] at hm'
      exact (coset_eq_iff (S.M d Λ') y₀ y).2 hm'
    · rintro ⟨y, ⟨hy, hyJ⟩, rfl⟩
      exact ⟨y, hBs y hy, hyJ, rfl⟩
  have hn₁ : S.nLev d Λ₁ (↑j + 1) = βJ := by
    rw [← hn]
    unfold Frames.nLev
    rw [hset Λ₁ hT₁ hB₀sat₁ rep₁, hset Λ hT hB₀sat rep]
    have hBB : {y | y ∈ B₀ ∧ S.levC d Λ₁ y = ↑j + 1} = {y | y ∈ B₀ ∧ S.levC d Λ y = ↑j + 1} := by
      ext y
      exact ⟨fun h => ⟨h.1, (hlev y h.1).symm.trans h.2⟩, fun h => ⟨h.1, (hlev y h.1).trans h.2⟩⟩
    rw [hBB]
    apply ncard_image_eq_of_iff
    intro a ha b hb
    have hab : a - b ∈ Y := Y.sub_mem (hB₀Y a ha.1) (hB₀Y b hb.1)
    exact (coset_eq_iff (S.M d Λ₁) a b).trans ((hYY _ hab).2.1.trans (coset_eq_iff (S.M d Λ) a b).symm)
  exact ⟨hTB₁, hbe₁.trans hbe, hle₁, hex₁, hn₁⟩

end GlobalTheory.HL.OffLeak
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetMassLeAndFinite
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.MassGlue

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ}

omit [IsNonarchimedeanLocalField F] [CharZero F] in

theorem sumCls_le (S : Frames L r k) (φ : Set S.FrP → ℝ≥0∞) (c : ℝ≥0∞) (h : ∀ C, φ C ≤ c) :
    S.sumCls φ ≤ (S.sumCls fun _ => 1) * c := by
  unfold Frames.sumCls
  rw [← ENNReal.tsum_mul_right]
  refine ENNReal.tsum_le_tsum fun o => ?_
  split_ifs
  · rw [mul_one]
    gcongr
    exact h _
  · simp

theorem mass_le (S : Frames L r k) (d : S.Datum) (j : ℕ) :
    (S.mass d fun Λ => S.cardI d Λ = j) ≤
      ENNReal.ofReal (S.Hp ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * (j : ℝ) ^ (k - 1)) := by
  by_cases hex : ∃ Λ, S.IsTerm d Λ
  · obtain ⟨Λ₀, h₀⟩ := hex
    have hH : 1 ≤ S.Hp := (GlobalTheory.T.term_exponents_nonneg_and_defect_group_bound L r k S d Λ₀ h₀).2.2.2.2.1
    rw [GlobalTheory.T.hermitianMass_eq_sum_frameClasses L r k S d _ (fun h hh Λ hT hP => by
      rw [(GlobalTheory.T.hermitianFrames_stabilizer_acts_on_terms L r k S d Λ hT h hh).2.2.2.2.2.2.1]; exact hP)]
    refine (sumCls_le S _ _ fun C => GlobalTheory.T.hermitianTermCount_frameClass_le L r k S d C j).trans ?_
    refine (mul_le_mul_left (GlobalTheory.T.hermitianFrameClasses_total_weight_le L r k S ⟨d, Λ₀, h₀⟩) _).trans ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← mul_assoc, ← pow_add]
    refine mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hH ?_) (by positivity)
    omega
  · have : (S.mass d fun Λ => S.cardI d Λ = j) = 0 := by
      unfold Frames.mass
      refine ENNReal.tsum_eq_zero.2 fun o => if_neg fun h => hex ⟨_, h.1⟩
    rw [this]
    exact zero_le

theorem finite_fibre (S : Frames L r k) (d : S.Datum) (C : Set S.FrP) :
    {Λ | S.IsTerm d Λ ∧ S.Fr d Λ = C}.Finite := by
  have h1 : ∀ j : ℕ, {Λ | S.IsTerm d Λ ∧ S.cardI d Λ = j ∧ S.Fr d Λ = C}.Finite := fun j => by
    have h := (GlobalTheory.T.hermitianTermCount_frameClass_le L r k S d C j).trans_lt ENNReal.ofReal_lt_top
    unfold Frames.nT at h
    rw [← Set.encard_lt_top_iff]
    by_contra hc
    rw [not_lt, top_le_iff] at hc
    rw [hc] at h
    simp at h
  refine ((Set.finite_Iic S.a.toNat).biUnion fun i _ =>
    (Set.finite_Iic (S.q ^ i)).biUnion fun j _ => h1 j).subset ?_
  rintro Λ ⟨hT, hC⟩
  obtain ⟨i, hi, hb⟩ := (GlobalTheory.T.term_exponents_nonneg_and_defect_group_bound L r k S d Λ hT).2.2.2.2.2.1
  have h2 := (GlobalTheory.T.gluingImage_card_pow_le_defectGroup_card L r k S d Λ hT).2.1
  simp only [Set.mem_iUnion, Set.mem_Iic, Set.mem_setOf_eq]
  exact ⟨i, by omega, S.cardI d Λ, hb ▸ h2, hT, rfl, hC⟩

theorem finite_cls (S : Frames L r k) (h : ∃ d Λ, S.IsTerm d Λ) :
    {o : MulAction.orbitRel.Quotient S.St (Set S.FrP) | S.IsIntCls o.out}.Finite := by
  have h1 := ((GlobalTheory.T.hermitianFrameClasses_total_weight_le L r k S h).trans_lt ENNReal.ofReal_lt_top).ne
  unfold Frames.sumCls at h1
  refine (ENNReal.finite_const_le_of_tsum_ne_top h1 (ε := 1) one_ne_zero).subset fun o ho => ?_
  have ho' : S.IsIntCls o.out := ho
  simp only [Set.mem_setOf_eq, if_pos ho', mul_one]
  exact ENNReal.one_le_ofReal.2 ((GlobalTheory.T.commonStabilizer_stabilizers_commensurable_volume L r k S).2 _ ho'.1).2.2.1

theorem finite_orbits (S : Frames L r k) (d : S.Datum) :
    {o : MulAction.orbitRel.Quotient S.St (Submodule L.O S.V) | S.IsTerm d o.out}.Finite := by
  by_cases hex : ∃ Λ, S.IsTerm d Λ
  · obtain ⟨Λ₀, h₀⟩ := hex
    refine (((finite_cls S ⟨d, Λ₀, h₀⟩).biUnion fun o _ => finite_fibre S d o.out).image
      (fun Λ => (Quotient.mk _ Λ : MulAction.orbitRel.Quotient S.St (Submodule L.O S.V)))).subset ?_
    intro o ho
    have hT : S.IsTerm d o.out := ho
    let o' : MulAction.orbitRel.Quotient S.St (Set S.FrP) := Quotient.mk _ (S.Fr d o.out)
    obtain ⟨h, hh⟩ : o'.out ∈ MulAction.orbit S.St (S.Fr d o.out) :=
      MulAction.orbitRel_apply.1 (Quotient.mk_out (s := MulAction.orbitRel S.St (Set S.FrP)) _)
    have hA := GlobalTheory.T.hermitianFrames_stabilizer_acts_on_terms L r k S d _ hT h.1 h.2
    have hF : S.Fr d (h.1 • o.out) = o'.out := hA.2.2.2.2.1.trans hh
    refine ⟨h.1 • o.out, ?_, ?_⟩
    · simp only [Set.mem_iUnion, Set.mem_setOf_eq]
      exact ⟨o', hF ▸ (GlobalTheory.HL.TermBasic.term_basic L r k S d _ hA.1).2.2.2.2.2.2.1, hA.1, hF⟩
    · refine Eq.trans ?_ (Quotient.out_eq o)
      exact Quotient.sound (MulAction.orbitRel_apply.2 ⟨h, rfl⟩)
  · refine Set.finite_empty.subset fun o ho => hex ⟨_, ho⟩

end GlobalTheory.HL.MassGlue

theorem GlobalTheory.HL.MassGlue.mass_le_and_finite : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 1 ≤ k → ∀ d : S.Datum, (∀ j : ℕ, (S.mass d fun Λ => S.cardI d Λ = j) ≤ ENNReal.ofReal (S.Hp ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * (j : ℝ) ^ (k - 1))) ∧ {o : MulAction.orbitRel.Quotient S.St (Submodule L.O S.V) | S.IsTerm d o.out}.Finite := by
  intro F _ _ _ _ _ E _ _ _ L r k S _ d
  exact ⟨GlobalTheory.HL.MassGlue.mass_le S d, GlobalTheory.HL.MassGlue.finite_orbits S d⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesReferenceSubgroupsRelIndexEqStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianFrames_reference_subgroups_relIndex_eq : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → ∀ Λ', S.IsTerm d Λ' → S.InFF β (j + 1) βJ d Λ' → (S.refA (j + 1) Λ).relIndex (S.refA (j + 1) Λ') = (S.refA (j + 1) Λ').relIndex (S.refA (j + 1) Λ) ∧ (S.refA (j + 1) Λ).relIndex (S.refA (j + 1) Λ') ≠ 0 := by
  first | exact @GlobalTheory.RefVol.main | exact GlobalTheory.RefVol.main | (intros; apply GlobalTheory.RefVol.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianGenusMassEqOrbitStabilizerMassStatement
section
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianGenusMass_eq_orbitStabilizerMass : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → ∀ L : Submodule (𝓞 K) V, Submodule.IsLattice K L → ENNReal.ofReal (mass h L) = orbMass (isom h) (genus h L) ∧ 0 < mass h L ∧ Stable (isom h) (genus h L) ∧ (∀ M : Submodule (𝓞 K) V, Submodule.IsLattice K M → Finite (MulAction.stabilizer (isom h) M)) ∧ ∀ (s : Finset (Submodule (𝓞 K) V)) (N : Submodule (𝓞 K) V → ℝ≥0∞), Formalism.ThetaLiftIndependence.IsClassReps h L s → (∀ (g : isom h) M, N (g • M) = N M) → ∑ M ∈ s, ENNReal.ofReal ((Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℝ))⁻¹ * N M = orbSum (isom h) (genus h L) N := by
  first | exact @GlobalTheory.Mass.GenusOrb.main | exact GlobalTheory.Mass.GenusOrb.main | (intros; apply GlobalTheory.Mass.GenusOrb.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLocalSumsEqConstMulCoordinateSums
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.CoordSq

open scoped Pointwise ENNReal Classical in
open ValuativeRel in
open scoped Pointwise ENNReal Classical in

theorem _root_.GlobalTheory.HL.CoordSq.sums_eq : ∀ {F : Type} [Field F] [ValuativeRel F]
    [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : _root_.Formalism.MainNotions.S.Loc.Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : _root_.Formalism.MainNotions.S.Loc.HermSp M V) (r k : ℕ)
    (P : _root_.Formalism.MainNotions.S.LocNG.FPair H r), ∀ (S : _root_.GlobalTheory.HL.Frames M.L r k) (c : _root_.GlobalTheory.HL.Coord P S),
    ∀ (R : _root_.Formalism.MainNotions.S.LocNG.Reps P) (d0 : _root_.Formalism.MainNotions.S.LocNG.Datum P), ∃ κ : ℝ, 0 ≤ κ ∧
      _root_.Formalism.MainNotions.S.LocNG.sumSq R d0 (_root_.Formalism.MainNotions.S.LocNG.BBne (H := H))
        = ENNReal.ofReal κ * S.ampSq (fun d Λ => ¬ S.BBzero d Λ) ∧
      _root_.Formalism.MainNotions.S.LocNG.sumSq R d0 (fun t => ¬ _root_.Formalism.MainNotions.S.LocNG.BBne (H := H) t)
        = ENNReal.ofReal κ * S.ampSq S.BBzero ∧
      _root_.Formalism.MainNotions.S.LocNG.sumSq R d0 (fun _ => True) = ENNReal.ofReal κ * S.ampSq (fun _ _ => True) ∧
      _root_.Formalism.MainNotions.S.LocNG.nn R d0 = ENNReal.ofReal κ * S.nn := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P S c R d0
  haveI := hM.loc
  haveI := hM.char0
  obtain ⟨κ, hκ, hsum⟩ := _root_.GlobalTheory.HL.CoordSum.tsum_reps_eq M hM H r k P S c R d0
  have hamp := _root_.GlobalTheory.HL.CoordAmp.amp_mass_eq M hM H r k P S c R
  have hvanA : ∀ (δ : S.Datum) (Q : Submodule M.L.O S.V → Prop),
      (¬ ∃ Λ, S.IsTerm δ Λ) → S.amp δ Q = 0 := by
    intro δ Q hδ
    unfold _root_.GlobalTheory.HL.Frames.amp
    refine (tsum_congr fun o => ?_).trans tsum_zero
    rw [if_neg fun h => hδ ⟨_, h.1⟩]
  have hvanM : ∀ (δ : S.Datum) (Q : Submodule M.L.O S.V → Prop),
      (¬ ∃ Λ, S.IsTerm δ Λ) → S.mass δ Q = 0 := by
    intro δ Q hδ
    unfold _root_.GlobalTheory.HL.Frames.mass
    refine (tsum_congr fun o => ?_).trans tsum_zero
    rw [if_neg fun h => hδ ⟨_, h.1⟩]
  have hinv : ∀ h ∈ S.H0, ∀ (δ : S.Datum) (Q : S.Datum → Submodule M.L.O S.V → Prop),
      (∀ δ', ∀ s ∈ S.St, ∀ Λ, S.IsTerm δ' Λ → Q δ' Λ → Q δ' (s • Λ)) →
      (∀ δ' Λ, S.IsTerm δ' Λ → (Q δ' Λ ↔ Q (h • δ') (h • Λ))) →
      S.amp (h • δ) (Q (h • δ)) = S.amp δ (Q δ) ∧
        S.mass (h • δ) (Q (h • δ)) = S.mass δ (Q δ) :=
    fun h hh δ Q h1 h2 => _root_.GlobalTheory.InvH.amp_mass_smul M.L r k S h hh δ (Q δ)
      (Q (h • δ)) (fun s hs Λ hΛ => h1 δ s hs Λ hΛ) (fun Λ hΛ => h2 δ Λ hΛ)
  have hBBst : ∀ δ', ∀ s ∈ S.St, ∀ Λ, S.IsTerm δ' Λ →
      (S.BBzero δ' (s • Λ) ↔ S.BBzero δ' Λ) :=
    fun δ' s hs Λ hΛ =>
      (_root_.GlobalTheory.FrameAct.stabiliser_acts_on_terms M.L r k S δ' Λ hΛ s hs).2.2.2.2.2.2.2.1
  have hBBh : ∀ h ∈ S.H0, ∀ δ' Λ, S.IsTerm δ' Λ →
      (S.BBzero δ' Λ ↔ S.BBzero (h • δ') (h • Λ)) := by
    intro h hh δ' Λ hΛ
    obtain ⟨-, -, -, hM', hsat, -⟩ :=
      _root_.GlobalTheory.HL.ComplAct.main M.L r k S δ' Λ hΛ h hh
    unfold _root_.GlobalTheory.HL.Frames.BBzero
    rw [hM', hsat]
  have hsq : ∀ z : ℂ, ((‖z‖₊ : ℝ≥0∞) ^ 2) = ENNReal.ofReal (‖z‖ ^ 2) := fun z => by
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
    rfl
  have hA : ∀ (p : _root_.Formalism.MainNotions.S.Loc.Term V M r → Prop) (Q : S.Datum → Submodule M.L.O S.V → Prop),
      (∀ d, _root_.Formalism.MainNotions.S.LocNG.amp R d p
        = S.amp (c.dat d) (Q (c.dat d))) →
      (∀ δ', ∀ s ∈ S.St, ∀ Λ, S.IsTerm δ' Λ → Q δ' Λ → Q δ' (s • Λ)) →
      (∀ h ∈ S.H0, ∀ δ' Λ, S.IsTerm δ' Λ → (Q δ' Λ ↔ Q (h • δ') (h • Λ))) →
      _root_.Formalism.MainNotions.S.LocNG.sumSq R d0 p = ENNReal.ofReal κ * S.ampSq Q := by
    intro p Q hpQ h1 h2
    unfold _root_.Formalism.MainNotions.S.LocNG.sumSq _root_.GlobalTheory.HL.Frames.ampSq
    rw [← hsum (fun δ => ENNReal.ofReal (‖S.amp δ (Q δ)‖ ^ 2))
      (fun h hh δ => by rw [(hinv h hh δ Q h1 (h2 h hh)).1])
      (fun δ hδ => by rw [hvanA δ _ hδ, norm_zero]; simp)]
    refine tsum_congr fun d => ?_
    rw [hpQ, hsq]
  refine ⟨κ, hκ, ?_, ?_, ?_, ?_⟩
  · exact hA _ (fun δ Λ => ¬ S.BBzero δ Λ) (fun d => (hamp d).1)
      (fun δ' s hs Λ hΛ hq => by rwa [hBBst δ' s hs Λ hΛ])
      (fun h hh δ' Λ hΛ => not_congr (hBBh h hh δ' Λ hΛ))
  · exact hA _ S.BBzero (fun d => (hamp d).2.1)
      (fun δ' s hs Λ hΛ hq => (hBBst δ' s hs Λ hΛ).2 hq)
      (fun h hh δ' Λ hΛ => hBBh h hh δ' Λ hΛ)
  · exact hA _ (fun _ _ => True) (fun d => (hamp d).2.2.1)
      (fun _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ => Iff.rfl)
  · unfold _root_.Formalism.MainNotions.S.LocNG.nn _root_.GlobalTheory.HL.Frames.nn
    rw [← hsum (fun δ => S.mass δ (fun _ => True))
      (fun h hh δ => (hinv h hh δ (fun _ _ => True) (fun _ _ _ _ _ _ => trivial)
        (fun _ _ _ => Iff.rfl)).2)
      (fun δ hδ => hvanM δ _ hδ)]
    refine tsum_congr fun d => ?_
    rw [(hamp d).2.2.2]

end GlobalTheory.HL.CoordSq
end

