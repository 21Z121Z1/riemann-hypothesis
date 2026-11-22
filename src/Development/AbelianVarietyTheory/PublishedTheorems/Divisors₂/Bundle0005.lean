import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0299
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LogResolutionProjectiveLine
import Development.AbelianVarietyTheory.Definitions.Divisors.XiMulNu
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqZeroOfCobOneEqZero

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

namespace GlobalTheory

inductive IsSmoothBlowupSeq {S Y : Scheme.{0}} (f : Y ⟶ S) (B : Set Y) : ∀ {Y' : Scheme.{0}}, (Y' ⟶ Y) → Prop

  | id : IsSmoothBlowupSeq f B (𝟙 Y)

  | step {Y₁ Y₂ : Scheme.{0}} {s : Y₁ ⟶ Y} (J : Y₁.IdealSheafData) (π : Y₂ ⟶ Y₁) :
      IsSmoothBlowupSeq f B s → Smooth (J.subschemeι ≫ s ≫ f) → (J.support : Set Y₁) ⊆ s ⁻¹' B →
      FinalTheorems.Blowup π J → IsSmoothBlowupSeq f B (π ≫ s)

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace in

theorem _root_.GlobalTheory.IsSmoothBlowupSeq.mono {S Y Y' : Scheme.{0}} {f : Y ⟶ S} {B B' : Set Y} {s : Y' ⟶ Y}
    (h : _root_.GlobalTheory.IsSmoothBlowupSeq f B s) (hB : B ⊆ B') : _root_.GlobalTheory.IsSmoothBlowupSeq f B' s := by
  induction h with
  | id => exact .id
  | step J π _ hsm hsupp hbl ih =>
    exact .step J π ih hsm (hsupp.trans (Set.preimage_mono hB)) hbl

theorem IsSmoothBlowupSeq.single {S Y Y' : Scheme.{0}} {f : Y ⟶ S} {B : Set Y} (J : Y.IdealSheafData) (π : Y' ⟶ Y)
    (h₁ : Smooth (J.subschemeι ≫ f)) (h₂ : (J.support : Set Y) ⊆ B) (h₃ : FinalTheorems.Blowup π J) :
    IsSmoothBlowupSeq f B π := by
  simpa using IsSmoothBlowupSeq.step (f := f) (B := B) J π .id (by simpa using h₁) (by simpa using h₂) h₃

namespace Principalise

theorem effCartier_top (X : Scheme.{0}) : FinalTheorems.EffCartier (⊤ : X.IdealSheafData) := fun x => by
  obtain ⟨_, ⟨U, hU, rfl⟩, hx, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  exact ⟨⟨U, hU⟩, 1, hx, one_mem _, by simp⟩

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace in

theorem _root_.GlobalTheory.Principalise.effCartier_comap_of_disjoint {W X : Scheme.{0}} (g : W ⟶ X) (J : X.IdealSheafData)
    (h : ∀ w, g w ∉ J.support) : _root_.ReciprocityTheory.AnForm.R.FinalTheorems.EffCartier (J.comap g) := by
  have htop : J.comap g = ⊤ := by
    rw [← Scheme.IdealSheafData.support_eq_bot_iff, Scheme.IdealSheafData.support_comap]
    ext w
    simpa using h w
  intro w
  obtain ⟨_, ⟨V, hV, rfl⟩, hwV, -⟩ :=
    W.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ w) isOpen_univ
  refine ⟨⟨V, hV⟩, 1, hwV, one_mem _, ?_⟩
  rw [htop, Ideal.span_singleton_one]
  simp [Scheme.IdealSheafData.ideal_top]

theorem blowup_id {X : Scheme.{0}} {J : X.IdealSheafData} (h : FinalTheorems.EffCartier J) : FinalTheorems.Blowup (𝟙 X) J :=
  ⟨by rwa [Scheme.IdealSheafData.comap_id], fun _ g _ => ⟨g, Category.comp_id g, fun _ e => by simpa using e⟩⟩

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace in

theorem _root_.GlobalTheory.Principalise.isIso_restrict_of_blowup {X X' : Scheme.{0}} {π : X' ⟶ X}
    {J : X.IdealSheafData} (h : _root_.ReciprocityTheory.AnForm.R.FinalTheorems.Blowup π J)
    (U : X.Opens) (hU : ∀ x ∈ U, x ∉ J.support) : IsIso (π ∣_ U) := by
  have hcart : ∀ (W : Scheme.{0}) (k : W ⟶ U.toScheme), _root_.ReciprocityTheory.AnForm.R.FinalTheorems.EffCartier (J.comap (k ≫ U.ι)) := by
    intro W k
    refine _root_.GlobalTheory.Principalise.effCartier_comap_of_disjoint _ J fun w => hU _ ?_
    rw [Scheme.Hom.comp_apply]
    have hmem : U.ι (k w) ∈ Set.range U.ι := ⟨_, rfl⟩
    rwa [Scheme.Opens.range_ι] at hmem
  have hσ' := hcart U.toScheme (𝟙 _)
  rw [Category.id_comp] at hσ'
  obtain ⟨σ, hσ, -⟩ := h.2 U.toScheme U.ι hσ'
  have hsnd : IsIso (pullback.snd π U.ι) := by
    refine ⟨⟨pullback.lift σ (𝟙 _) (by rw [hσ, Category.id_comp]), ?_,
      pullback.lift_snd _ _ _⟩⟩
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, Category.id_comp]
      have hg := hcart _ (pullback.snd π U.ι)
      rw [← pullback.condition] at hg
      exact (h.2 _ _ hg).unique (by rw [Category.assoc, hσ, pullback.condition]) rfl
    · simp only [Category.assoc, pullback.lift_snd, Category.comp_id, Category.id_comp]
  rw [morphismRestrict]
  infer_instance

end Principalise

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace in

theorem _root_.GlobalTheory.IsSmoothBlowupSeq.isIso_restrict {S Y Y' : Scheme.{0}} {f : Y ⟶ S}
    {B : Set Y} {s : Y' ⟶ Y}
    (h : _root_.GlobalTheory.IsSmoothBlowupSeq f B s) (U : Y.Opens) (hU : ∀ y ∈ U, y ∉ B) : IsIso (s ∣_ U) := by
  induction h with
  | id => infer_instance
  | @step Y₁ Y₂ s J π hs hsm hsupp hbl ih =>
    rw [morphismRestrict_comp]
    have : IsIso (π ∣_ s ⁻¹ᵁ U) :=
      _root_.GlobalTheory.Principalise.isIso_restrict_of_blowup hbl _ fun x hx hxJ => hU _ hx (hsupp hxJ)
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ this ih

namespace Principalise

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace in

theorem _root_.GlobalTheory.Principalise.nonempty_compl_support {Y : Scheme.{0}} [IsIntegral Y] {I : Y.IdealSheafData} (hI : I ≠ ⊥) :
    (I.support.compl : Set Y).Nonempty := by
  by_contra hne
  apply hI
  rw [← Scheme.IdealSheafData.support_eq_top_iff]
  ext x
  simp only [Set.not_nonempty_iff_eq_empty] at hne
  have : x ∉ (I.support.compl : Set Y) := by simp [hne]
  simpa using this

end Principalise

namespace Published

def Principalisation : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (d : ℕ) (Y : Scheme.{0}) (f : Y ⟶ Sp k),
    IsIntegral Y → SmoothOfRelativeDimension d f → IsProjOver f →
    ∀ I : Y.IdealSheafData, I ≠ ⊥ →
      ∃ (Y' : Scheme.{0}) (s : Y' ⟶ Y),
        IsIntegral Y' ∧ SmoothOfRelativeDimension d (s ≫ f) ∧ IsProjOver (s ≫ f) ∧
        IsSmoothBlowupSeq f (I.support : Set Y) s ∧ IsIso (s ∣_ I.support.compl) ∧
        FinalTheorems.EffCartier (I.comap s) ∧ FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal (I.comap s).support)

end Published

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PointDimensionLtProjectiveLine
section
namespace GlobalTheory

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions GlobalTheory.LogResInt Filter Topology

noncomputable section

namespace AnDim

variable {d : ℕ} {X : Type} [TopologicalSpace X]

def singularLocus (A : FinHolAtlas d X) (T : Set X) : Set X :=
  T \ ⋃ n, regularLocus A T n

def analyticDim (A : FinHolAtlas d X) (T : Set X) : WithBot ℕ∞ :=
  ⨆ (n : ℕ) (_ : (regularLocus A T n).Nonempty), (n : WithBot ℕ∞)

end AnDim

namespace Published

open AnDim

def AnalyticSetDimension : Prop :=
  ∀ (d : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas d X),
    (∀ T : Set X, A.IsAnalyticSubset T →
      A.IsAnalyticSubset (singularLocus A T) ∧
        (T.Nonempty → analyticDim A (singularLocus A T) < analyticDim A T)) ∧
    (∀ (Z : Set X) (n : ℕ), IsIrreducibleAnalytic A Z → (regularLocus A Z n).Nonempty →
      analyticDim A Z = n) ∧
    (∀ C S : Set X, IsIrreducibleAnalytic A C → A.IsAnalyticSubset S → ¬ C ⊆ S →
      analyticDim A (C ∩ S) < analyticDim A C) ∧
    (∀ T : Set X, A.IsAnalyticSubset T →
      {C | IsIrreducibleComponent A T C}.Finite ∧ T = ⋃₀ {C | IsIrreducibleComponent A T C})

end Published

namespace AnDim

variable {d : ℕ} {X : Type} [TopologicalSpace X]

theorem le_analyticDim {A : FinHolAtlas d X} {T : Set X} {n : ℕ}
    (h : (regularLocus A T n).Nonempty) : (n : WithBot ℕ∞) ≤ analyticDim A T :=
  le_iSup₂ (f := fun (n : ℕ) (_ : (regularLocus A T n).Nonempty) => (n : WithBot ℕ∞)) n h

theorem le_analyticDim_iff {A : FinHolAtlas d X} {T : Set X} {k : ℕ} :
    (k : WithBot ℕ∞) ≤ analyticDim A T ↔ ∃ n, k ≤ n ∧ (regularLocus A T n).Nonempty := by
  refine ⟨fun h => ?_, fun ⟨n, hk, hn⟩ => le_trans (by exact_mod_cast hk) (le_analyticDim hn)⟩
  by_contra hcon
  push_neg at hcon
  have hlt : ∀ n, (regularLocus A T n).Nonempty → n < k := fun n hn =>
    lt_of_not_ge fun hk => hn.ne_empty (hcon n hk)
  cases k with
  | zero =>
    have : analyticDim A T ≤ ⊥ := iSup₂_le fun n hn => absurd (hlt n hn) (Nat.not_lt_zero n)
    exact absurd (h.trans this) (by simp)
  | succ k =>
    have : analyticDim A T ≤ (k : WithBot ℕ∞) :=
      iSup₂_le fun n hn => by exact_mod_cast Nat.lt_succ_iff.1 (hlt n hn)
    have h2 : k + 1 ≤ k := by exact_mod_cast h.trans this
    omega

theorem analyticDim_le (A : FinHolAtlas d X) (T : Set X) : analyticDim A T ≤ (d : WithBot ℕ∞) :=
  iSup₂_le fun n ⟨_, _, _, hψ, _⟩ => by exact_mod_cast hψ.1

theorem analyticDim_empty (A : FinHolAtlas d X) : analyticDim A ∅ = ⊥ :=
  le_bot_iff.1 (iSup₂_le fun _ ⟨_, hx⟩ => absurd hx.1 (Set.notMem_empty _))

theorem analyticDim_univ [Nonempty X] (A : FinHolAtlas d X) : analyticDim A Set.univ = d :=
  le_antisymm (analyticDim_le A _)
    (le_analyticDim (by rw [regularLocus_univ]; exact Set.univ_nonempty))

theorem singularLocus_univ (A : FinHolAtlas d X) : singularLocus A Set.univ = ∅ :=
  Set.diff_eq_empty.2 fun x _ => Set.mem_iUnion.2 ⟨d, by rw [regularLocus_univ]; trivial⟩

theorem injective_fderiv_of_comp {a b c : ℕ} {F : (Fin a → ℂ) → Fin b → ℂ}
    {G : (Fin b → ℂ) → Fin c → ℂ} {H : (Fin a → ℂ) → Fin c → ℂ} {z : Fin a → ℂ}
    (hF : DifferentiableAt ℂ F z) (hG : DifferentiableAt ℂ G (F z)) (h : G ∘ F =ᶠ[𝓝 z] H)
    (hH : Function.Injective (fderiv ℂ H z)) : Function.Injective (fderiv ℂ F z) := by
  rw [← h.fderiv_eq, fderiv_comp z hG hF] at hH
  exact Function.Injective.of_comp (f := fderiv ℂ G (F z)) hH

def padL (k d : ℕ) : (Fin k → ℂ) →L[ℂ] (Fin d → ℂ) :=
  ContinuousLinearMap.pi fun i => if h : (i : ℕ) < k then ContinuousLinearMap.proj ⟨i, h⟩ else 0

theorem padL_apply_of_le {k d : ℕ} (z : Fin k → ℂ) {i : Fin d} (h : k ≤ (i : ℕ)) :
    padL k d z i = 0 := by
  simp [padL, not_lt.2 h]

theorem padL_injective {k d : ℕ} (h : k ≤ d) : Function.Injective (padL k d) := by
  intro z w hzw
  funext i
  simpa [padL] using congrFun hzw (Fin.castLE h i)

theorem hasHoloImm_of_regularLocus {A : FinHolAtlas d X} {T : Set X} {n k : ℕ} (hk : k ≤ n)
    (h : (regularLocus A T n).Nonempty) : HasHoloImm A T k := by
  obtain ⟨x, hxT, ψ, ⟨hnd, hψ, hT⟩, hx⟩ := h
  obtain ⟨j, hj⟩ := A.cover x
  have hp : ∀ i : Fin d, n ≤ (i : ℕ) → ψ x i = 0 := (hT.le ⟨hxT, hx⟩).2
  set a : (Fin k → ℂ) → Fin d → ℂ := fun z => ψ x + padL k d z with ha
  have han : ∀ z, AnalyticAt ℂ a z := fun z => analyticAt_const.add ((padL k d).analyticAt z)
  have hac : Continuous a := continuous_const.add (padL k d).continuous
  have hV : IsOpen (ψ.target ∩ ψ.symm ⁻¹' (A.chart j).source) :=
    ψ.symm.isOpen_inter_preimage (A.chart j).open_source
  have hF : ∀ z ∈ a ⁻¹' (ψ.target ∩ ψ.symm ⁻¹' (A.chart j).source),
      AnalyticAt ℂ (A.chart j ∘ ψ.symm ∘ a) z := fun z hz =>
    ((hψ j).2 (a z) hz).comp (han z)
  refine ⟨a ⁻¹' (ψ.target ∩ ψ.symm ⁻¹' (A.chart j).source), ψ.symm ∘ a, j, hV.preimage hac,
    ⟨0, ?_⟩, fun z hz => ⟨?_, hz.2⟩, hF, fun z hz => ?_⟩
  · simp [ha, ψ.map_source hx, ψ.left_inv hx, hj]
  · refine (hT.ge ⟨ψ.map_target hz.1, fun i hi => ?_⟩).1
    rw [ψ.right_inv hz.1]
    simp [ha, hp i hi, padL_apply_of_le z (hk.trans hi)]
  · refine injective_fderiv_of_comp (G := ψ ∘ (A.chart j).symm) (H := a) (hF z hz).differentiableAt
      ((hψ j).1 _ ⟨(A.chart j).map_source hz.2, ?_⟩).differentiableAt ?_ ?_
    · simpa [(A.chart j).left_inv hz.2] using ψ.map_target hz.1
    · filter_upwards [(hV.preimage hac).mem_nhds hz] with w hw
      simp [(A.chart j).left_inv hw.2, ψ.right_inv hw.1]
    · have : fderiv ℂ a z = padL k d := ((padL k d).hasFDerivAt.const_add (ψ x)).fderiv
      rw [this]
      exact padL_injective (hk.trans hnd)

theorem le_of_mem_regularLocus {A : FinHolAtlas d X} {T : Set X} {n k : ℕ}
    {U : Set (Fin k → ℂ)} {g : (Fin k → ℂ) → X} {j : Fin A.n} (hU : IsOpen U)
    (hmaps : Set.MapsTo g U (T ∩ (A.chart j).source)) (han : AnalyticOnNhd ℂ (A.chart j ∘ g) U)
    {z : Fin k → ℂ} (hz : z ∈ U) (hinj : Function.Injective (fderiv ℂ (A.chart j ∘ g) z))
    (hreg : g z ∈ regularLocus A T n) : k ≤ n := by
  obtain ⟨-, ψ, ⟨hnd, hψ, hT⟩, hx⟩ := hreg
  have hj := (hmaps hz).2
  have hV : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' ψ.source) :=
    (A.chart j).symm.isOpen_inter_preimage ψ.open_source
  have hzV : (A.chart j ∘ g) z ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' ψ.source :=
    ⟨(A.chart j).map_source hj, by simpa [(A.chart j).left_inv hj] using hx⟩
  have hev : ∀ᶠ w in 𝓝 z, w ∈ U ∧ g w ∈ ψ.source := by
    filter_upwards [hU.mem_nhds hz, (han z hz).continuousAt.preimage_mem_nhds (hV.mem_nhds hzV)]
      with w hw hw'
    exact ⟨hw, by simpa [(A.chart j).left_inv (hmaps hw).2] using hw'.2⟩
  have hH : AnalyticAt ℂ (ψ ∘ g) z := by
    refine (((hψ j).1 _ hzV).comp (han z hz)).congr ?_
    filter_upwards [hev] with w hw
    simp [(A.chart j).left_inv (hmaps hw.1).2]
  have hHinj : Function.Injective (fderiv ℂ (ψ ∘ g) z) := by
    refine injective_fderiv_of_comp (G := A.chart j ∘ ψ.symm) hH.differentiableAt
      ((hψ j).2 _ ⟨ψ.map_source hx, by simpa [ψ.left_inv hx] using hj⟩).differentiableAt ?_ hinj
    filter_upwards [hev] with w hw
    simp [ψ.left_inv hw.2]
  have hzero : ∀ (v : Fin k → ℂ) (i : Fin d), n ≤ (i : ℕ) → fderiv ℂ (ψ ∘ g) z v i = 0 := by
    intro v i hi
    have h1 : (fun w => (ψ ∘ g) w i) =ᶠ[𝓝 z] fun _ => 0 := by
      filter_upwards [hev] with w hw
      exact (hT.le ⟨(hmaps hw.1).1, hw.2⟩).2 i hi
    have h2 := h1.fderiv_eq (𝕜 := ℂ)
    rw [fderiv_pi (differentiableAt_pi.1 hH.differentiableAt)]
    simp only [ContinuousLinearMap.pi_apply]
    rw [h2]
    simp
  let M : (Fin k → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
    (LinearMap.funLeft ℂ ℂ (Fin.castLE hnd)).comp (fderiv ℂ (ψ ∘ g) z).toLinearMap
  have hM : Function.Injective M := by
    intro v w hvw
    refine hHinj (funext fun i => ?_)
    by_cases hi : (i : ℕ) < n
    · exact congrFun hvw ⟨i, hi⟩
    · rw [hzero v i (not_lt.1 hi), hzero w i (not_lt.1 hi)]
  simpa using LinearMap.finrank_le_finrank_of_injective hM

theorem hasHoloImm_iff (h : Published.AnalyticSetDimension) [CompactSpace X] [T2Space X]
    {A : FinHolAtlas d X} {T : Set X} (hT : A.IsAnalyticSubset T) {k : ℕ} :
    HasHoloImm A T k ↔ (k : WithBot ℕ∞) ≤ analyticDim A T := by
  refine ⟨fun hk => ?_, fun hk => ?_⟩
  · induction hm : analyticDim A T using WellFoundedLT.induction generalizing T with
    | ind m ih =>
      subst hm
      obtain ⟨U, g, j, hU, hne, hmaps, han, hinj⟩ := hk
      by_cases hreg : ∃ z ∈ U, ∃ n, g z ∈ regularLocus A T n
      · obtain ⟨z, hz, n, hn⟩ := hreg
        exact le_analyticDim_iff.2
          ⟨n, le_of_mem_regularLocus hU hmaps han hz (hinj z hz) hn, _, hn⟩
      · push_neg at hreg
        obtain ⟨hs, hlt⟩ := (h d X A).1 T hT
        obtain ⟨z, hz⟩ := hne
        have hlt' := hlt ⟨g z, (hmaps hz).1⟩
        refine (ih _ hlt' hs ⟨U, g, j, hU, ⟨z, hz⟩, fun w hw => ⟨⟨(hmaps hw).1, ?_⟩, (hmaps hw).2⟩,
          han, hinj⟩ rfl).trans hlt'.le
        simpa using hreg w hw
  · obtain ⟨n, hkn, hn⟩ := le_analyticDim_iff.1 hk
    exact hasHoloImm_of_regularLocus hkn hn

theorem immersedPieces (h : Published.AnalyticSetDimension) (d : ℕ) (X : Type) [TopologicalSpace X]
    [CompactSpace X] [T2Space X] (A : FinHolAtlas d X) :
    (∀ (Z : Set X) (n : ℕ), IsIrreducibleAnalytic A Z → (regularLocus A Z n).Nonempty →
      ¬ HasHoloImm A Z (n + 1)) ∧
    (∀ (C S : Set X) (k : ℕ), IsIrreducibleAnalytic A C → A.IsAnalyticSubset S → ¬ C ⊆ S →
      HasHoloImm A (C ∩ S) k → HasHoloImm A C (k + 1)) ∧
    (∀ S : Set X, A.IsAnalyticSubset S →
      {C | IsIrreducibleComponent A S C}.Finite ∧ S = ⋃₀ {C | IsIrreducibleComponent A S C}) := by
  obtain ⟨-, h2, h3, h4⟩ := h d X A
  refine ⟨fun Z n hZ hn hc => ?_, fun C S k hC hS hCS hk => ?_, h4⟩
  · have h5 := (hasHoloImm_iff h hZ.1).1 hc
    rw [h2 Z n hZ hn] at h5
    have : n + 1 ≤ n := by exact_mod_cast h5
    omega
  · have h5 := ((hasHoloImm_iff h (isAnalyticSubset_inter hC.1 hS)).1 hk).trans_lt (h3 C S hC hS hCS)
    obtain ⟨n, hn, hlt⟩ : ∃ n : ℕ, (regularLocus A C n).Nonempty ∧ (k : WithBot ℕ∞) < n := by
      obtain ⟨n, hn⟩ := lt_iSup_iff.1 h5
      obtain ⟨hn', hn⟩ := lt_iSup_iff.1 hn
      exact ⟨n, hn', hn⟩
    exact hasHoloImm_of_regularLocus (by exact_mod_cast hlt) hn

theorem analyticDim_singleton_le (A : FinHolAtlas d X) (x : X) : analyticDim A {x} ≤ 0 := by
  refine iSup₂_le fun n hn => ?_
  obtain ⟨U, g, j, hU, ⟨z, hz⟩, hmaps, -, hinj⟩ := hasHoloImm_of_regularLocus le_rfl hn
  have h1 : (A.chart j ∘ g) =ᶠ[𝓝 z] fun _ => A.chart j x := by
    filter_upwards [hU.mem_nhds hz] with w hw
    rw [Function.comp_apply, (hmaps hw).1]
  have h2 := hinj z hz
  rw [h1.fderiv_eq, fderiv_fun_const] at h2
  cases n with
  | zero => simp
  | succ n =>
    have := congrFun (h2 (a₁ := 0) (a₂ := 1) rfl) 0
    simp at this

theorem point_dimension_lt_projective_line (x : OnePoint ℂ) :
    analyticDim p1 (Set.univ ∩ {x}) < analyticDim p1 Set.univ := by
  rw [Set.univ_inter, analyticDim_univ]
  exact (analyticDim_singleton_le p1 x).trans_lt (by exact_mod_cast Nat.zero_lt_one)

theorem projective_line_dimension : IsIrreducibleAnalytic p1 Set.univ ∧ analyticDim p1 Set.univ = 1 ∧
    analyticDim p1 (singularLocus p1 Set.univ) < analyticDim p1 Set.univ := by
  refine ⟨AnLogRes.isIrreducibleAnalytic_univ p1, by simpa using analyticDim_univ p1, ?_⟩
  rw [singularLocus_univ, analyticDim_empty, analyticDim_univ]
  exact WithBot.bot_lt_coe _

end AnDim

end

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonneAt
section
noncomputable section

open CategoryTheory WittVector Ideal

namespace GlobalTheory.Published

open GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta

def PrismaticDieudonneAt {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (span {(p : O)}) O] {ε : PreTilt O p} (hε : IsPrimitiveSystem ε) : Prop :=
  ∃ (M : PDivGroup p O → ModuleCat.{0} (Ainf p O))
    (map : ∀ G H : PDivGroup p O, (G ⟶ H) →+ (M H →ₗ[Ainf p O] M G))
    (φ : ∀ G, M G →ₛₗ[(frobenius : Ainf p O →+* Ainf p O)] M G)
    (lie : ∀ G, M G →ₛₗ[fontaineTheta O p] G.dual.Lie)
    (dR : ∀ G, M G →ₛₗ[fontaineTheta O p] G.RigExt),
    (∀ G, Module.Free (Ainf p O) (M G) ∧ Module.Finite (Ainf p O) (M G) ∧
      Module.finrank (Ainf p O) (M G) = G.height ∧
      Function.Injective (φ G) ∧ (∀ m, ∃ n, φ G n = frobenius (xi ε) • m) ∧
      Module.Projective O G.dual.Lie ∧ Function.Surjective (lie G) ∧
      (∀ m, lie G m = 0 ↔ ∃ n, φ G m = frobenius (xi ε) • n) ∧
      Function.Surjective (dR G) ∧ (∀ m, dR G m = 0 ↔ ∃ n, m = xi ε • n) ∧
      map G G (𝟙 G) = LinearMap.id) ∧
    (∀ (G H K : PDivGroup p O) (f : G ⟶ H) (g : H ⟶ K),
      map G K (f ≫ g) = map G H f ∘ₗ map H K g) ∧
    (∀ (G H : PDivGroup p O) (f : G ⟶ H) (m : M H),
      map G H f (φ H m) = φ G (map G H f m) ∧
      lie G (map G H f m) = lieMap H.dual G.dual (dualHom G H f) (lie H m) ∧
      dR G (map G H f m) = rigExtMap f (dR H m)) ∧
    (∀ G H : PDivGroup p O, Function.Injective (map G H) ∧
      ∀ u : M H →ₗ[Ainf p O] M G, (∀ m, u (φ H m) = φ G (u m)) → ∃ f, map G H f = u) ∧
    ∃ (l : M (PDivGroup.mu p O)) (e : M (const p O)),
      Function.Bijective (LinearMap.toSpanSingleton (Ainf p O) _ l) ∧
      Function.Bijective (LinearMap.toSpanSingleton (Ainf p O) _ e) ∧
      φ _ l = frobenius (xi ε) • l ∧ φ _ e = e ∧
      map _ _ (epsHom (zeta ε) hε.zeta_zero (zeta_succ_pow ε)) l = Sandwich.mu ε • e

def PrismaticDieudonne : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (C : Type) [NontriviallyNormedField C] [NormedAlgebra ℚ_[p] C]
    [CompleteSpace C] [IsAlgClosed C] (O : Type) [CommRing O] [Algebra O C],
    IsIntegers O C →
    ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]
      (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), PrismaticDieudonneAt hε

end GlobalTheory.Published
end
end

