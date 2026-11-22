import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0002
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsAdmissibleSplittingCharPairMulTwist
import Formalism.HermitianCurvature.HermitianCurvatureProofs.StarStartConjugationIdentity
import Formalism.RealPlaceAnalysis.Bundle0004
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0057
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0026
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrameStartConstantsNormalFormEmptyWord
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF.StartForm

theorem prod_mul_prod_eq_one {A : Type} [Ring A] : ∀ (n : ℕ) (f g : Fin n → A),
    (∀ i j, Commute (f i) (g j)) → (∀ i, f i * g i = 1) → (List.ofFn f).prod * (List.ofFn g).prod = 1
  | 0, _, _, _, _ => by simp
  | n + 1, f, g, hc, h1 => by
    have ih := prod_mul_prod_eq_one n (fun i => f i.succ) (fun i => g i.succ) (fun i j => hc _ _) (fun i => h1 _)
    have hcm : Commute (List.ofFn fun i : Fin n => f i.succ).prod (g 0) := by
      refine Commute.list_prod_left _ _ fun x hx => ?_
      obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hx
      exact hc _ _
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, mul_assoc, ← mul_assoc _ (g 0), hcm.eq,
      mul_assoc, ih, mul_one, h1]

variable {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ}

theorem comm_of_closure (L : LevelData A r) {x y : A} (hx : x ∈ Submonoid.closure L.fns)
    (hy : y ∈ Submonoid.closure L.fns) : Commute x y := by
  induction hx using Submonoid.closure_induction with
  | mem x hx =>
    induction hy using Submonoid.closure_induction with
    | mem y hy => exact L.fns_comm x hx y hy
    | one => exact Commute.one_right _
    | mul a b _ _ ha hb => exact ha.mul_right hb
  | one => exact Commute.one_left _
  | mul a b _ _ ha hb => exact ha.mul_left hb

theorem prod_mem (L : LevelData A r) (f : Fin r → A) (hf : ∀ i, f i ∈ L.fns) :
    (List.ofFn f).prod ∈ Submonoid.closure L.fns := by
  refine Submonoid.list_prod_mem _ fun x hx => ?_
  obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hx
  exact Submonoid.subset_closure (hf i)

theorem phase (L : LevelData A r) : L.ζb * L.ζi * L.GGi * (L.D * L.Dbi) * (L.Drb * L.Dri) = L.GGi := by
  have mc : ∀ i, L.c i ∈ L.fns := fun i => by simp [LevelData.fns]
  have mci : ∀ i, L.ci i ∈ L.fns := fun i => by simp [LevelData.fns]
  have mcb : ∀ i, L.cb i ∈ L.fns := fun i => by simp [LevelData.fns]
  have mcbi : ∀ i, L.cbi i ∈ L.fns := fun i => by simp [LevelData.fns]
  have h1 : L.Dr * L.Dri = 1 :=
    prod_mul_prod_eq_one r _ _ (fun i j => L.fns_comm _ (mc i) _ (mci j)) L.c_ci
  have h2 : L.Drbi * L.Drb = 1 :=
    prod_mul_prod_eq_one r _ _ (fun i j => L.fns_comm _ (mcbi i) _ (mcb j)) L.cbi_cb
  have mDr : L.Dr ∈ Submonoid.closure L.fns := prod_mem L _ mc
  have mζ : L.ζ ∈ Submonoid.closure L.fns := Submonoid.subset_closure (by simp [LevelData.fns])
  have mζi : L.ζi ∈ Submonoid.closure L.fns := Submonoid.subset_closure (by simp [LevelData.fns])
  have mζb : L.ζb ∈ Submonoid.closure L.fns := Submonoid.subset_closure (by simp [LevelData.fns])
  have mζbi : L.ζbi ∈ Submonoid.closure L.fns := Submonoid.subset_closure (by simp [LevelData.fns])
  have mGGi : L.GGi ∈ Submonoid.closure L.fns := Submonoid.subset_closure (by simp [LevelData.fns])
  have e1 : L.D * L.Dbi * (L.Drb * L.Dri) = L.ζ * L.ζbi := by
    calc L.D * L.Dbi * (L.Drb * L.Dri) = L.Dr * (L.ζ * L.ζbi) * (L.Drbi * L.Drb) * L.Dri := by
          simp only [LevelData.D, LevelData.Dbi, mul_assoc]
      _ = L.ζ * L.ζbi := by
          rw [h2, mul_one, (comm_of_closure L mDr (mul_mem mζ mζbi)).eq, mul_assoc, h1, mul_one]
  rw [mul_assoc _ (L.D * L.Dbi), e1, (comm_of_closure L (mul_mem mζb mζi) mGGi).eq]
  calc L.GGi * (L.ζb * L.ζi) * (L.ζ * L.ζbi) = L.GGi * (L.ζb * (L.ζi * L.ζ) * L.ζbi) := by simp only [mul_assoc]
    _ = L.GGi := by rw [L.ζi_ζ, mul_one, L.ζb_ζbi, mul_one]

end GlobalTheory.HatNF.StartForm

namespace GlobalTheory.HatNF

open StartForm

open MeasureTheory in
private lemma prod_ofFn_mul_prod_ofFn_eq_one {A : Type} [Ring A] :
    ∀ {n : ℕ} (f g : Fin n → A), (∀ i, f i * g i = 1) → (∀ i j, Commute (f i) (g j)) →
      (List.ofFn f).prod * (List.ofFn g).prod = 1
  | 0, _, _, _, _ => by simp
  | n + 1, f, g, h, hc => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons]
    have hrest : (List.ofFn fun i : Fin n => f i.succ).prod *
        (List.ofFn fun i : Fin n => g i.succ).prod = 1 :=
      prod_ofFn_mul_prod_ofFn_eq_one _ _ (fun i => h i.succ) (fun i j => hc i.succ j.succ)
    have hcomm : Commute (List.ofFn fun i : Fin n => f i.succ).prod (g 0) := by
      refine Commute.list_prod_left _ _ ?_
      intro b hb
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hb
      exact hc i.succ 0
    calc f 0 * (List.ofFn fun i : Fin n => f i.succ).prod *
          (g 0 * (List.ofFn fun i : Fin n => g i.succ).prod)
        = f 0 * ((List.ofFn fun i : Fin n => f i.succ).prod * g 0) *
            (List.ofFn fun i : Fin n => g i.succ).prod := by simp only [mul_assoc]
      _ = f 0 * g 0 * ((List.ofFn fun i : Fin n => f i.succ).prod *
            (List.ofFn fun i : Fin n => g i.succ).prod) := by rw [hcomm.eq]; simp only [mul_assoc]
      _ = 1 := by rw [h 0, hrest, one_mul]

open MeasureTheory in
private lemma levelConstants_commute {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ} (L : _root_.Formalism.FourierDecayAlt.R.LevelData A r)
    {x y : A}
    (hx : x ∈ Set.range L.c ∪ Set.range L.ci ∪ Set.range L.cb ∪ Set.range L.cbi ∪
      {L.ζ, L.ζi, L.ζb, L.ζbi, L.GG, L.GGi})
    (hy : y ∈ Set.range L.c ∪ Set.range L.ci ∪ Set.range L.cb ∪ Set.range L.cbi ∪
      {L.ζ, L.ζi, L.ζb, L.ζbi, L.GG, L.GGi}) : Commute x y :=
  L.fns_comm x hx y hy

open MeasureTheory in
private lemma commute_prod_ofFn {A : Type} [Ring A] {n : ℕ} (a : A) (f : Fin n → A)
    (h : ∀ i, Commute a (f i)) : Commute a (List.ofFn f).prod := by
  refine Commute.list_prod_right _ _ ?_
  intro b hb
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hb
  exact h i

open MeasureTheory in

theorem _root_.GlobalTheory.HatNF.start_normalForm : ∀ (P : _root_.Formalism.FourierDecayAlt.M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : _root_.Formalism.FourierDecayAlt.Q.NFData P A), _root_.GlobalTheory.HatNF.HatHyp d → ∀ (L : _root_.Formalism.FourierDecayAlt.R.LevelData A P.r) (st : _root_.Formalism.FourierDecayAlt.Fr.Start A) (s : ℂ), _root_.GlobalTheory.HatNF.Comparison₂ d L st s → (∀ x ∈ _root_.Formalism.FourierDecayAlt.TL.kAlg st, x ∈ Set.range d.κ) ∧ ∀ Y ∈ st.inv, ∃ E ∈ _root_.GlobalTheory.HatNF.nfSpan d ∅ 0 0 0, L.l0 Y + L.ζb * L.ζi * L.GGi * st.ee Y = d.L.l0 Y + d.L.ζb * d.L.ζi * d.L.GGi * E := by
  intro P A _ _ _ _ d hHyp L st s hTie
  obtain ⟨hA, hSame, hs, hQ, hinv⟩ := hTie
  obtain ⟨-, -, hRel, -⟩ := hHyp
  obtain ⟨-, hκfns, -⟩ := hRel
  obtain ⟨-, -, -, -, -, -, -, hζi, hζb, -, hGG, hGGi, -⟩ := hSame
  have hst := hA.start
  have hs0 : s ≠ 0 := by rcases hs with rfl | rfl <;> norm_num

  have hκ : ∀ (f : _root_.Formalism.FourierDecayAlt.M.Ty P → ℂ) (g : A), g ∈ ({d.L.ζ, d.L.ζi, d.L.ζb, d.L.ζbi, d.L.GG, d.L.GGi} : Set A) →
      Commute (d.κ f) g := by
    intro f g hg
    exact hκfns f g (Or.inl (by unfold _root_.Formalism.FourierDecayAlt.R.LevelData.fns; exact Or.inr hg))

  have hx : ∀ Y, st.x Y = s • d.x Y := by
    intro Y
    have h11 := congrFun (congrFun (hQ Y) 1) 1
    rw [hst.tau Y, hGG] at h11
    simp only [Matrix.smul_apply, _root_.Formalism.FourierDecayAlt.Q.NFData.QQ] at h11
    simp at h11
    calc st.x Y = d.L.GGi * (d.L.GG * st.x Y) := by rw [← mul_assoc, d.L.GGi_GG, one_mul]
      _ = s • d.x Y := by rw [h11, mul_smul_comm, ← mul_assoc, d.L.GGi_GG, one_mul]

  have hxinv : ∀ Y ∈ st.inv, d.x Y * d.κ (fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹) = 1 ∧
      d.κ (fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹) * d.x Y = 1 := by
    intro Y hY
    rw [hinv] at hY
    unfold _root_.Formalism.FourierDecayAlt.Q.NFData.x
    rw [← map_mul, ← map_mul, ← map_one d.κ]
    constructor
    · congr 1; funext ρ; exact mul_inv_cancel₀ (hY ρ)
    · congr 1; funext ρ; exact inv_mul_cancel₀ (hY ρ)
  refine ⟨?_, ?_⟩
  · intro a ha
    have hle : _root_.Formalism.FourierDecayAlt.TL.kAlg st ≤ d.κ.range := by
      unfold _root_.Formalism.FourierDecayAlt.TL.kAlg
      refine Algebra.adjoin_le ?_
      rintro b (⟨Y, -, rfl⟩ | ⟨Y, hY, -, rfl⟩)
      · rw [hx Y]
        unfold _root_.Formalism.FourierDecayAlt.Q.NFData.x
        exact ⟨s • fun ρ => _root_.Formalism.FourierDecayAlt.M.xC P ρ Y, by simp [map_smul]⟩
      · have hxi : st.xi Y = s⁻¹ • d.κ (fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹) := by
          have hright : st.x Y * (s⁻¹ • d.κ (fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹)) = 1 := by
            rw [hx Y, smul_mul_smul_comm, mul_inv_cancel₀ hs0, (hxinv Y hY).1, one_smul]
          calc st.xi Y = st.xi Y * (st.x Y * (s⁻¹ • d.κ (fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹))) := by
                rw [hright, mul_one]
            _ = s⁻¹ • d.κ (fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹) := by
                rw [← mul_assoc, (hst.x_xi Y hY).2, one_mul]
        rw [hxi]
        exact ⟨s⁻¹ • fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹, by simp [map_smul]⟩
    rw [← AlgHom.coe_range]
    exact hle ha
  · intro Y hY
    obtain ⟨hXXi, hXiX⟩ := hxinv Y hY
    have h10 := congrFun (congrFun (hQ Y) 1) 0
    rw [hst.low Y hY, hx Y, hGG, hζb, hζi, hGGi] at h10
    simp only [Matrix.smul_apply, _root_.Formalism.FourierDecayAlt.Q.NFData.QQ] at h10
    simp at h10
    rw [← smul_add] at h10
    have h10' : d.L.GG * d.x Y * (L.l0 Y + d.L.ζb * d.L.ζi * d.L.GGi * st.ee Y) =
        d.L.GG * d.x Y * d.L.l0 Y + d.weightedSumBis Y := by
      have h := congrArg (fun a => s⁻¹ • a) h10
      simpa only [smul_smul, inv_mul_cancel₀ hs0, one_smul] using h
    have hcancel : ∀ a : A, d.κ (fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹) * (d.L.GGi * (d.L.GG * d.x Y * a)) = a := by
      intro a
      simp only [← mul_assoc]
      rw [mul_assoc _ d.L.GGi d.L.GG, d.L.GGi_GG, mul_one, hXiX, one_mul]
    have key : L.l0 Y + d.L.ζb * d.L.ζi * d.L.GGi * st.ee Y =
        d.L.l0 Y + d.κ (fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹) * (d.L.GGi * d.weightedSumBis Y) := by
      have h : d.κ (fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹) * (d.L.GGi * (d.L.GG * d.x Y *
          (L.l0 Y + d.L.ζb * d.L.ζi * d.L.GGi * st.ee Y))) =
          d.κ (fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹) * (d.L.GGi * (d.L.GG * d.x Y * d.L.l0 Y + d.weightedSumBis Y)) := by
        rw [h10']
      rw [hcancel, mul_add, mul_add, hcancel] at h
      exact h
    have hmem : ∀ b ∈ _root_.GlobalTheory.HatNF.bmon d, b ∈ _root_.GlobalTheory.HatNF.nfSpan d ∅ 0 0 0 := by
      intro b hb
      unfold _root_.GlobalTheory.HatNF.nfSpan
      exact Submodule.subset_span ⟨b, hb, [], rfl, by simp, by simp⟩
    have hgen : ∀ b ∈ _root_.GlobalTheory.HatNF.bset d, b ∈ _root_.GlobalTheory.HatNF.bmon d := by
      intro b hb
      unfold _root_.GlobalTheory.HatNF.bmon
      exact Submonoid.subset_closure hb
    have hκgen : ∀ f : _root_.Formalism.FourierDecayAlt.M.Ty P → ℂ, d.κ f ∈ _root_.GlobalTheory.HatNF.bmon d := fun f =>
      hgen _ (by unfold _root_.GlobalTheory.HatNF.bset; exact Or.inl (Or.inl (Or.inr ⟨f, rfl⟩)))
    have hDgen : d.L.D * d.L.Dbi ∈ _root_.GlobalTheory.HatNF.bmon d :=
      hgen _ (by unfold _root_.GlobalTheory.HatNF.bset; exact Or.inl (Or.inl (Or.inl (by simp))))
    have hPgen : ∀ l ∈ Finset.Icc 1 (P.k - 1), d.L.Drb * d.L.Dri * d.SS l ∈ _root_.GlobalTheory.HatNF.bmon d := by
      intro l hl
      refine hgen _ ?_
      unfold _root_.GlobalTheory.HatNF.bset
      refine Or.inl (Or.inr ⟨l, by simpa using hl, ?_⟩)
      unfold _root_.GlobalTheory.HatNF.ssn
      rfl
    have hDD : ∀ l, d.L.D * d.L.Dbi * (d.L.Drb * d.L.Dri * d.SS l) = d.L.ζ * (d.L.ζbi * d.SS l) := by
      intro l
      have hcb : (List.ofFn d.L.cbi).prod * (List.ofFn d.L.cb).prod = 1 :=
        prod_ofFn_mul_prod_ofFn_eq_one _ _ d.L.cbi_cb
          (fun i j => levelConstants_commute d.L (by simp) (by simp))
      have hc : (List.ofFn d.L.c).prod * (List.ofFn d.L.ci).prod = 1 :=
        prod_ofFn_mul_prod_ofFn_eq_one _ _ d.L.c_ci
          (fun i j => levelConstants_commute d.L (by simp) (by simp))
      have hζci : Commute d.L.ζ (List.ofFn d.L.ci).prod :=
        commute_prod_ofFn _ _ (fun i => levelConstants_commute d.L (by simp) (by simp))
      have hζbici : Commute d.L.ζbi (List.ofFn d.L.ci).prod :=
        commute_prod_ofFn _ _ (fun i => levelConstants_commute d.L (by simp) (by simp))
      unfold _root_.Formalism.FourierDecayAlt.R.LevelData.D _root_.Formalism.FourierDecayAlt.R.LevelData.Dbi _root_.Formalism.FourierDecayAlt.R.LevelData.Drb _root_.Formalism.FourierDecayAlt.R.LevelData.Dri _root_.Formalism.FourierDecayAlt.R.LevelData.Dr _root_.Formalism.FourierDecayAlt.R.LevelData.Drbi
      simp only [mul_assoc]
      rw [← mul_assoc (List.ofFn d.L.cbi).prod, hcb, one_mul, ← hζbici.symm.left_comm,
        ← hζci.symm.left_comm, ← mul_assoc, hc, one_mul]
    have hGGiζ : Commute d.L.GGi d.L.ζ := levelConstants_commute d.L (by simp) (by simp)
    have hGGiζbi : Commute d.L.GGi d.L.ζbi := levelConstants_commute d.L (by simp) (by simp)
    have hXiζ : Commute (d.κ (fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹)) d.L.ζ := hκ _ _ (by simp)
    have hXiζbi : Commute (d.κ (fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹)) d.L.ζbi := hκ _ _ (by simp)
    have hXiGGi : Commute (d.κ (fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹)) d.L.GGi := hκ _ _ (by simp)
    refine ⟨d.L.ζ * (d.L.ζbi * (d.κ (fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹) * d.weightedSumBis Y)), ?_, ?_⟩
    · have hS : d.weightedSumBis Y = ∑ l ∈ Finset.Icc 1 (P.k - 1), d.SS l * d.κ (fun ρ => _root_.Formalism.FourierDecayAlt.M.xEx P {l} ρ Y) := rfl
      rw [hS, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      refine Submodule.sum_mem _ (fun l hl => hmem _ ?_)
      have heq : d.L.ζ * (d.L.ζbi * (d.κ (fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹) *
          (d.SS l * d.κ (fun ρ => _root_.Formalism.FourierDecayAlt.M.xEx P {l} ρ Y)))) =
          d.κ (fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹) * (d.L.D * d.L.Dbi) * (d.L.Drb * d.L.Dri * d.SS l) *
            d.κ (fun ρ => _root_.Formalism.FourierDecayAlt.M.xEx P {l} ρ Y) := by
        rw [mul_assoc (d.κ _) (d.L.D * d.L.Dbi), hDD, ← hXiζbi.left_comm, ← hXiζ.left_comm]
        simp only [mul_assoc]
      rw [heq]
      exact mul_mem (mul_mem (mul_mem (hκgen _) hDgen) (hPgen l hl)) (hκgen _)
    · rw [hζb, hζi, hGGi, key]
      congr 1
      simp only [mul_assoc]
      rw [hGGiζ.left_comm, hGGiζbi.left_comm, ← mul_assoc d.L.ζi, d.L.ζi_ζ, one_mul,
        ← mul_assoc d.L.ζb, d.L.ζb_ζbi, one_mul, hXiGGi.left_comm]

end GlobalTheory.HatNF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MinusHatsPassGenerators
section
namespace GlobalTheory.HatNF.GenMinus

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
open Formalism.FourierDecayAlt.R.LevelData Formalism.FourierDecayAlt.P.RuleGD Formalism.FourierDecayAlt.P.MAx3.H Formalism.FourierDecayAlt.P.MAx3.K

noncomputable section

variable {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] {P : M.Par}

omit [Algebra ℂ A] [StarModule ℂ A] in
theorem star_listProd (l : List A) : star l.prod = (l.map star).reverse.prod := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.prod_cons, star_mul, ih, List.prod_append]

omit [StarModule ℂ A] in
theorem mem_span (d : Q.NFData P A) {b X : A} (hb : b ∈ bmon d) (hX : X ∈ hats d.L) :
    b * X ∈ nfSpan d (hats d.L) 0 0 1 := by
  unfold nfSpan
  refine Submodule.subset_span ⟨b, hb, [X], rfl, ?_⟩
  simp [hX]

omit [StarModule ℂ A] in
theorem kap_comm (d : Q.NFData P A) (h : HatHyp d) (f : M.Ty P → ℂ) (y : ℂ) :
    Commute (d.κ f) (d.L.Ahatv y) ∧ Commute (d.κ f) (d.L.R0v y) := by
  obtain ⟨-, -, hR, -, -, -, hk⟩ := h
  have hf : ∀ g ∈ d.L.fns, Commute (d.κ f) g := fun g hg => hR.2.1 f g (Or.inl hg)
  have hn : Commute (d.κ f) d.L.nabs := hR.2.1 f _ (Or.inr (by simp))
  have hpb : ∀ l, Commute (d.κ f) (d.L.pb l) := fun l => hk f _ (by simp [TL.siteOps])
  obtain ⟨hA, hB⟩ := Formalism.FourierDecayAlt.P.MAx3.Q.comm_Tvprod d.L (d.κ f) hpb (fun l => hf _ (m_cb d.L l))
    (fun l => hf _ (m_cbi d.L l)) y
  have hA' : Commute (d.κ f) (d.L.Avr y) := hA
  have hB' : Commute (d.κ f) (d.L.Bvr y) := hB
  have hDr : Commute (d.κ f) d.L.Dr := Commute.list_prod_right _ _ fun x hx => by
    obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hx; exact hf _ (m_c d.L l)
  have hDrb : Commute (d.κ f) d.L.Drb := Commute.list_prod_right _ _ fun x hx => by
    obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hx; exact hf _ (m_cb d.L l)
  have hm : Commute (d.κ f) (d.L.m0 y) :=
    hn.neg_right.sub_right ((Algebra.commutes _ _).symm |> fun h : Commute (d.κ f) (algebraMap ℂ A (y - 1/2)) =>
      h.mul_right ((hf _ (m_ζ d.L)).mul_right (hf _ (m_GGi d.L))))
  exact ⟨hDrb.mul_right hA', (hDr.mul_right (hf _ (m_GG d.L))).mul_right ((hm.mul_right hA').add_right hB')⟩

omit [StarModule ℂ A] in
theorem ss_rule (d : Q.NFData P A) (h : HatHyp d) (i : ℕ) (hi : i ∈ Finset.Icc 1 (P.k - 1)) (Y : ℂ) :
    d.L.Ahatv Y * ssn d i = ssn d i * d.L.Ahatv (Y - 1) ∧ d.L.R0v Y * ssn d i = ssn d i * d.L.R0v (Y - 1) := by
  obtain ⟨-, -, hR, -⟩ := h
  obtain ⟨h1, h2⟩ := hR.2.2.2.2.1 i hi
  have hc := hR.2.2.1 i
  have h := Formalism.FourierDecayAlt.P.intertwinerConjugation _ P.r d.L (d.SS i) 0 (fun x hx => (hc x (Or.inl (Or.inl hx))).symm)
    (fun l => (hc _ (Or.inl (Or.inr ⟨l, rfl⟩))).symm) (fun l => (hc _ (Or.inr ⟨l, rfl⟩)).symm) h1 h2
    (fun x _ => by simp) (fun l => by simp) (fun l => by simp) (by simp) (by simp) Y
  exact ⟨h.2.2.1, h.2.2.2.1⟩

theorem sss_rule (d : Q.NFData P A) (h : HatHyp d) (i : ℕ) (hi : i ∈ Finset.Icc 1 (P.k - 1)) (Y : ℂ) :
    d.L.Ahatv Y * star (ssn d i) = star (ssn d i) * d.L.Ahatv (Y + 1) ∧
      d.L.R0v Y * star (ssn d i) = star (ssn d i) * d.L.R0v (Y + 1) := by
  obtain ⟨-, hS, hR, sp, sc, sci, -⟩ := h
  obtain ⟨h1, h2⟩ := hR.2.2.2.2.1 i hi
  have hc := hR.2.2.1 i
  obtain ⟨sz, szb, szi, szbi, sg, sgi⟩ := Formalism.FourierDecayAlt.P.TLA.M2.star_fns d.L hS
  have sn : star d.L.nab = d.L.nabs := hS.2.1
  have sns : star d.L.nabs = d.L.nab := by rw [← sn, star_star]
  have scb : ∀ l, star (d.L.cb l) = d.L.c l := fun l => by rw [← sc, star_star]
  have scbi : ∀ l, star (d.L.cbi l) = d.L.ci l := fun l => by rw [← sci, star_star]
  have spb : ∀ l, star (d.L.pb l) = -d.L.p l := fun l => by
    rw [← star_star (d.L.p l), sp, star_neg, neg_neg]
  have sf : ∀ x ∈ d.L.fns, star x ∈ d.L.fns := by
    intro x hx
    simp only [LevelData.fns, Set.mem_union, Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with ((((⟨l, rfl⟩ | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | (rfl | rfl | rfl | rfl | rfl | rfl))
    · rw [sc]; exact m_cb d.L l
    · rw [sci]; exact m_cbi d.L l
    · rw [scb]; exact m_c d.L l
    · rw [scbi]; exact m_ci d.L l
    · rw [sz]; exact m_ζb d.L
    · rw [szi]; exact m_ζbi d.L
    · rw [szb]; exact m_ζ d.L
    · rw [szbi]; exact m_ζi d.L
    · rw [sg]; exact m_GG d.L
    · rw [sgi]; exact m_GGi d.L
  have hf : ∀ x ∈ d.L.fns, Commute (star (d.SS i)) x := fun x hx => by
    have := (hc _ (Or.inl (Or.inl (sf x hx)))).star_star
    rwa [star_star] at this
  have hp : ∀ l, Commute (star (d.SS i)) (d.L.p l) := fun l => by
    have := (hc _ (Or.inr ⟨l, rfl⟩)).star_star
    rw [spb] at this
    exact Commute.neg_right_iff.1 this
  have hpb : ∀ l, Commute (star (d.SS i)) (d.L.pb l) := fun l => by
    have := (hc _ (Or.inl (Or.inr ⟨l, rfl⟩))).star_star
    rw [sp] at this
    exact Commute.neg_right_iff.1 this
  have c1 : star (d.SS i) * (d.L.GGi * d.L.ζb) = d.L.ζb * d.L.GGi * star (d.SS i) := by
    rw [((hf _ (m_GGi d.L)).mul_right (hf _ (m_ζb d.L))).eq, d.L.fns_comm _ (m_GGi d.L) _ (m_ζb d.L)]
  have c2 : star (d.SS i) * (d.L.GGi * d.L.ζ) = d.L.ζ * d.L.GGi * star (d.SS i) := by
    rw [((hf _ (m_GGi d.L)).mul_right (hf _ (m_ζ d.L))).eq, d.L.fns_comm _ (m_GGi d.L) _ (m_ζ d.L)]
  have k1 : d.L.nab * star (d.SS i) = star (d.SS i) * d.L.nab + d.L.ζb * d.L.GGi * star (d.SS i) := by
    have := congrArg star h2
    rw [star_mul, star_sub, star_mul, star_mul, star_mul, sns, sz, sgi] at this
    rw [← c1, this]; abel
  have k2 : d.L.nabs * star (d.SS i) = star (d.SS i) * d.L.nabs + d.L.ζ * d.L.GGi * star (d.SS i) := by
    have := congrArg star h1
    rw [star_mul, star_sub, star_mul, star_mul, star_mul, sn, szb, sgi] at this
    rw [← c2, this]; abel
  have sDrb : star d.L.Drb = d.L.Dr := by
    unfold LevelData.Drb LevelData.Dr
    rw [star_listProd, List.map_ofFn]
    have : (star ∘ d.L.cb) = d.L.c := funext scb
    rw [this, rev_prod d.L]
    intro x hx; obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hx; exact memF d.L (m_c d.L l)
  have sDri : star d.L.Dri = d.L.Drbi := by
    unfold LevelData.Dri LevelData.Drbi
    rw [star_listProd, List.map_ofFn]
    have : (star ∘ d.L.ci) = d.L.cbi := funext sci
    rw [this, rev_prod d.L]
    intro x hx; obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hx; exact memF d.L (m_cbi d.L l)
  have e : star (ssn d i) = star (d.SS i) * (d.L.Dr * d.L.Drbi) := by
    rw [ssn, star_mul, star_mul, sDrb, sDri, cl_comm d.L (memDrbi d.L) (memDr d.L)]
  have h := Formalism.FourierDecayAlt.P.intertwinerConjugation _ P.r d.L 0 (star (d.SS i)) (fun x _ => by simp) (fun l => by simp)
    (fun l => by simp) (by simp) (by simp) (fun x hx => (hf x hx).symm) (fun l => (hp l).symm)
    (fun l => (hpb l).symm) k1 k2 Y
  rw [e]
  exact ⟨h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩

end

theorem minus_hats_pass_generators :
    ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d →
      ∀ b ∈ bset d, ∀ y : ℂ,
        d.L.Ahatv y * b ∈ nfSpan d (hats d.L) 0 0 1 ∧ d.L.R0v y * b ∈ nfSpan d (hats d.L) 0 0 1 := by
  intro P A _ _ _ _ d h b hb y
  have gen : ∀ {x}, x ∈ bset d → x ∈ bmon d := fun h => Submonoid.subset_closure h
  have mDD : d.L.D * d.L.Dbi ∈ bmon d := gen (Or.inl (Or.inl (Or.inl (by simp))))
  have mDbD : d.L.Db * d.L.Di ∈ bmon d := gen (Or.inl (Or.inl (Or.inl (by simp))))
  have mζi : d.L.ζi ∈ bmon d := gen (Or.inl (Or.inl (Or.inl (by simp))))
  have mζbi : d.L.ζbi ∈ bmon d := gen (Or.inl (Or.inl (Or.inl (by simp))))
  have hdrv : d.L.Dr * d.L.Dbi ∈ bmon d := by
    rw [drv_eq]; exact Submonoid.mul_mem _ mDD mζi
  have sA : ∀ {x}, x ∈ bmon d → ∀ y, x * d.L.Ahatv y ∈ nfSpan d (hats d.L) 0 0 1 := fun hx y =>
    mem_span d hx (Or.inl (Or.inr ⟨y, rfl⟩))
  have sR : ∀ {x}, x ∈ bmon d → ∀ y, x * d.L.R0v y ∈ nfSpan d (hats d.L) 0 0 1 := fun hx y =>
    mem_span d hx (Or.inr ⟨y, rfl⟩)
  have hInv := Formalism.FourierDecayAlt.P.inverseCommutators _ P.r d.L y
  have hb' := gen hb
  rcases hb with (((hb | ⟨f, rfl⟩) | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩)
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · rw [← hInv.2.2.2.2.2.1, ← hInv.2.2.2.2.2.2.1]
      exact ⟨sA hb' _, sR hb' _⟩
    · rw [← hInv.2.2.1, vgen_ζbi_R]
      refine ⟨sA hb' _, Submodule.add_mem _ (sR hb' _) ?_⟩
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ (sA mDD _))
        (Submodule.smul_mem _ _ (sA (Submonoid.mul_mem _ (Submonoid.mul_mem _ mζi mζbi) mDD) _))
    · rw [vgen_DD_A, vgen_DD_R]
      exact ⟨sA hb' _, Submodule.add_mem _ (sR hb' _) (Submodule.smul_mem _ _ (sA (Submonoid.mul_mem _ mDD hdrv) _))⟩
    · rw [vgen_DbD_A, vgen_DbD_R]
      exact ⟨sA hb' _, Submodule.add_mem _ (sR hb' _) (Submodule.smul_mem _ _ (sA (Submonoid.mul_mem _ mDbD hdrv) _))⟩
  · rw [← (kap_comm d h f y).1.eq, ← (kap_comm d h f y).2.eq]
    exact ⟨sA hb' _, sR hb' _⟩
  · have := ss_rule d h i (Finset.mem_Icc.2 (Set.mem_Icc.1 hi)) y
    rw [this.1, this.2]
    exact ⟨sA hb' _, sR hb' _⟩
  · have := sss_rule d h i (Finset.mem_Icc.2 (Set.mem_Icc.1 hi)) y
    simp only [] at hb' ⊢
    rw [this.1, this.2]
    exact ⟨sA hb' _, sR hb' _⟩

end GlobalTheory.HatNF.GenMinus
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SplitCasimirStdEigenvalue
section
open Formalism.REAL

namespace GlobalTheory

theorem splitCasimirStd_eigenvalue : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (Et : Fin (n + 1) → Fin (n + 1) → Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (Om : Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (m : Fin (n + 1) → ℂ), GlRel E → (∀ a b x y, inner ℂ (E a b x) y = inner ℂ x (E b a y)) → (∀ w v, qdet E w v = (∏ j, (w + m j)) • v) → (∀ a b y c, Et a b y c = E a b (y c) + if c = a then y b else 0) → (∀ y b, Om y b = ∑ c, E c b (y c)) → ∀ (lam : ℂ) (x : (PiLp 2 (fun _ : Fin (n + 1) => V))), x ≠ 0 → Om x = lam • x → ∃ j, lam = m j + 0 := by
  intro V _ _ _ n E Et Om m hE hadj hq hEt hOm lam x hx hlam
  obtain ⟨K, hK, -⟩ := GlobalTheory.T.capelli_comatrix_last_row_inverts_casimir V n E Om m hE hq hOm
  obtain ⟨-, -, -, hc⟩ := tensorStd_rel_adjoint_splitCasimir V n E Et Om hE hadj hEt hOm
  by_contra hne
  have hprod : (∏ j, (-lam + m j)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun j _ h => hne ⟨j, ?_⟩
    linear_combination -h
  have hlast : ∀ y, Om y = lam • y → y (Fin.last n) = 0 := by
    intro y hy
    have h := hK (-lam) y
    rw [hy, sub_zero, neg_smul, neg_add_cancel, map_zero] at h
    exact (smul_eq_zero.1 h.symm).resolve_left hprod
  apply hx
  refine PiLp.ext fun c => ?_
  have h1 : Om (Et (Fin.last n) c x) = lam • Et (Fin.last n) c x := by
    have h := LinearMap.congr_fun (hc (Fin.last n) c) x
    simp only [Module.End.mul_apply] at h
    rw [h, hlam, map_smul]
  have h2 := hlast _ h1
  rw [hEt, hlast x hlam] at h2
  simpa using h2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TopNum
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.TopNum

theorem hsq_le (r : ℕ) (T b C : ℝ) (hC : 0 ≤ C) (hb : 2 ≤ b)
    (hT : T ≤ b ^ (C * ((2 * r + 2 : ℕ) : ℝ))) :
    Hsq r T b ≤ b ^ ((C + 10) * ((2 * r + 2 : ℕ) : ℝ)) := by
  have hb0 : 0 < b := by linarith
  have hb1 : 1 ≤ b := by linarith
  have h1 : (1 : ℝ) ≤ b ^ (C * ((2 * r + 2 : ℕ) : ℝ)) :=
    Real.one_le_rpow hb1 (mul_nonneg hC (Nat.cast_nonneg _))
  have h2 : max 1 T ≤ b ^ (C * ((2 * r + 2 : ℕ) : ℝ)) := max_le h1 hT
  have h3 : (C + 10) * ((2 * r + 2 : ℕ) : ℝ)
      = C * ((2 * r + 2 : ℕ) : ℝ) + ((20 * (r + 1) : ℕ) : ℝ) := by
    push_cast; ring
  rw [h3, Real.rpow_add hb0, Real.rpow_natCast]
  unfold Hsq
  exact mul_le_mul_of_nonneg_right h2 (pow_nonneg hb0.le _)

theorem top_num : ∀ (r : ℕ) (T T' b C : ℝ), 0 ≤ C → 2 ≤ b → T ≤ b ^ (C * ((2 * r + 2 : ℕ) : ℝ)) → T' ≤ b ^ (C * ((2 * r + 2 : ℕ) : ℝ)) → Real.sqrt (Hsq r T b * Hsq r T' b) ≤ b ^ ((C + 10) * ((2 * r + 2 : ℕ) : ℝ)) := by
  intro r T T' b C hC hb hT hT'
  have hb0 : 0 < b := by linarith
  have h1 := hsq_le r T b C hC hb hT
  have h2 := hsq_le r T' b C hC hb hT'
  have hp : 0 ≤ b ^ ((C + 10) * ((2 * r + 2 : ℕ) : ℝ)) := Real.rpow_nonneg hb0.le _
  have h0 : 0 ≤ Hsq r T' b := by
    unfold Hsq
    exact mul_nonneg (le_trans zero_le_one (le_max_left _ _)) (pow_nonneg hb0.le _)
  rw [Real.sqrt_le_left hp, sq]
  exact mul_le_mul h1 h2 h0 hp

end GlobalTheory.TopNum
end

