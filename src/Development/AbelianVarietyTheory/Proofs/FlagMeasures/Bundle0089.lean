import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0040
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermInvariantsIndependentOfWitnesses
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0075
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0084
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0031
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0061
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0051
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0080
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0044
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0057
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0050
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0086
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0049
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0082
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0064
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesStabilizerActsOnTerms
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0074
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0085
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimitiveTuplesHermitianGramCosetContent

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianMovePreservesFrameLatticeLevels
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.MoveSame
open GlobalTheory.HL.Eichler

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem transfer {V : Type} [AddCommGroup V] [Module E V] {m : ℕ} {g g' h h' : Fin m → V}
    (hli : LinearIndependent E (Sum.elim g g')) {y : V} {al al' : Fin m → E}
    (e1 : y = ∑ i, al i • g i + ∑ i, al' i • g' i) (e2 : y = ∑ i, al i • h i + ∑ i, al' i • h' i)
    (P : (Fin m → E) → (Fin m → E) → Prop)
    (H : ∃ be be' : Fin m → E, y = ∑ i, be i • g i + ∑ i, be' i • g' i ∧ P be be') :
    ∃ be be' : Fin m → E, y = ∑ i, be i • h i + ∑ i, be' i • h' i ∧ P be be' := by
  obtain ⟨be, be', e3, hP⟩ := H
  have h0 := Fintype.linearIndependent_iff.1 hli (Sum.elim (al - be) (al' - be')) (by
    have := e1.symm.trans e3
    simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.sub_apply, sub_smul,
      Finset.sum_sub_distrib]
    rw [sub_add_sub_comm, this, sub_self])
  have a1 : al = be := funext fun i => sub_eq_zero.1 (h0 (Sum.inl i))
  have a2 : al' = be' := funext fun i => sub_eq_zero.1 (h0 (Sum.inr i))
  subst a1 a2
  exact ⟨_, _, e2, hP⟩

theorem mem_Mof (g g' : Fin (r + 1) → S.V) (y : S.V) :
    y ∈ S.Mof g g' ↔ ∃ al al' : Fin (r + 1) → E, y = ∑ i, al i • g i + ∑ i, al' i • g' i ∧
      ∀ i, algebraMap F E S.th * al' i ∈ L.O ∧ al i + al' i ∈ L.O := by
  have ht := WitIndep.th_mul S
  constructor
  · intro hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      rcases hx with ⟨b, rfl⟩ | ⟨b, rfl⟩
      · refine ⟨Pi.single b 1, 0, by simp [Pi.single_apply], fun i => ⟨by simp, ?_⟩⟩
        by_cases h : i = b
        · subst h; simp
        · simp [h]
      · refine ⟨Pi.single b (-algebraMap F E S.th⁻¹), Pi.single b (algebraMap F E S.th⁻¹), ?_,
          fun i => ?_⟩
        · simp only [Pi.single_apply, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
            if_true, smul_sub, neg_smul]
          abel
        · by_cases h : i = b
          · subst h
            simp only [Pi.single_eq_same, neg_add_cancel, mul_comm (algebraMap F E S.th), ht]
            exact ⟨L.O.one_mem, L.O.zero_mem⟩
          · simp [h]
    | zero => exact ⟨0, 0, by simp, fun i => by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, a', rfl, ha⟩ := hx
      obtain ⟨b, b', rfl, hb⟩ := hy
      refine ⟨a + b, a' + b', ?_, fun i => ⟨?_, ?_⟩⟩
      · simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]; abel
      · simpa [mul_add] using L.O.add_mem (ha i).1 (hb i).1
      · have := L.O.add_mem (ha i).2 (hb i).2
        rw [add_add_add_comm] at this
        exact this
    | smul c x _ hx =>
      obtain ⟨a, a', rfl, ha⟩ := hx
      refine ⟨fun i => c * a i, fun i => c * a' i, ?_, fun i => ⟨?_, ?_⟩⟩
      · rw [Subring.smul_def]
        simp only [smul_add, Finset.smul_sum, smul_smul]
      · have := L.O.mul_mem c.2 (ha i).1
        rw [mul_left_comm] at this
        exact this
      · have := L.O.mul_mem c.2 (ha i).2
        rw [mul_add] at this
        exact this
  · rintro ⟨al, al', rfl, h⟩
    rw [← Finset.sum_add_distrib]
    refine Submodule.sum_mem _ fun i _ => ?_
    have e : al i • g i + al' i • g' i = (al i + al' i) • g i +
        (algebraMap F E S.th * al' i) • (algebraMap F E S.th⁻¹ • (g' i - g i)) := by
      rw [smul_smul, mul_right_comm, mul_comm (algebraMap F E S.th), ht, one_mul, add_smul, smul_sub]
      abel
    rw [e]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ (⟨_, (h i).2⟩ : L.O) (Submodule.subset_span (Or.inl ⟨i, rfl⟩)))
      (Submodule.smul_mem _ (⟨_, (h i).1⟩ : L.O) (Submodule.subset_span (Or.inr ⟨i, rfl⟩)))

theorem exists_coef_map {g : Fin (r + 1) → S.V}
    (hg : ∀ a (j : Fin r), hf L S.Hm (g a) (g j.castSucc) = 0) {n : S.GLV} (hn : n ∈ S.Nof g)
    {J : ℕ} {y : S.V} (hy : y ∈ S.spanTo g J) :
    ∃ c : Fin (r + 1) → E, (∀ i : Fin (r + 1), ¬ (i : ℕ) < J → c i = 0) ∧ y = ∑ i, c i • n (g i) := by
  obtain ⟨c, hc, e⟩ := StdLat.exists_coef g _ (TermBasic.map_mem hg ((S.Nof g).inv_mem hn) J hy)
  refine ⟨c, hc, ?_⟩
  have e2 : n (n⁻¹ y) = y := n.apply_symm_apply y
  rw [← e2, e]
  simp only [map_sum, map_smul]

theorem iso_span {g : Fin (r + 1) → S.V}
    (hg : ∀ a (j : Fin r), hf L S.Hm (g a) (g j.castSucc) = 0) {J : ℕ} {v : S.V}
    (hv : v ∈ S.spanTo g J) : v ∈ perp L S.Hm (S.spanTo g r) := by
  refine (Submodule.span_le.2 ?_ : S.spanTo g J ≤ _) hv
  rintro _ ⟨i, -, rfl⟩
  rw [SetLike.mem_coe, Frames.spanTo, StdLat.image_lt, StdLat.mem_perp_span]
  exact hg _

variable [IsNonarchimedeanLocalField F] [CharZero F]

theorem indep {n n' : S.GLV} (hn : n ∈ S.N) (hn' : n' ∈ S.N') :
    LinearIndependent E (Sum.elim (fun b => n (S.f b)) (fun b => n' (S.f' b))) := by
  have hg : ∀ a (j : Fin r), hf L S.Hm (S.f a) (S.f j.castSucc) = 0 := fun a j => by
    simp [S.gram, Fin.castSucc_ne_last]
  have hg' : ∀ a (j : Fin r), hf L S.Hm (S.f' a) (S.f' j.castSucc) = 0 := fun a j => by
    simp [S.gram', Fin.castSucc_ne_last]
  obtain ⟨hli, -⟩ := FrameBasic.main L r k S
  obtain ⟨l1, l2, l3⟩ := linearIndependent_sum.1 hli
  refine LinearIndependent.sum_type (l1.map' n.toLinearMap (LinearEquiv.ker _))
    (l2.map' n'.toLinearMap (LinearEquiv.ker _)) (l3.mono ?_ ?_)
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨b, rfl⟩
    have := TermBasic.map_mem hg hn (r + 1) (TermBasic.self_mem S S.f b.2)
    rw [TermBasic.spanTo_top] at this
    exact this
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨b, rfl⟩
    have := TermBasic.map_mem hg' hn' (r + 1) (TermBasic.self_mem S S.f' b.2)
    rw [TermBasic.spanTo_top] at this
    exact this

end

theorem move_same : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → ∀ x x' u s, S.IsMove (j + 1) d Λ x x' u s → ∀ Λ₁ : Submodule L.O S.V, (Λ₁ : Set S.V) = S.moved Λ x u s → S.IsTerm d Λ₁ ∧ ∀ y ∈ (S.spanTo S.f (j + 1) ⊔ S.spanTo S.f' (j + 1)), (y ∈ Λ → y ∈ Λ₁) ∧ (y ∈ S.M d Λ₁ ↔ y ∈ S.M d Λ) ∧ S.lev (S.fr d Λ₁) (S.fr' d Λ₁) y = S.lev (S.fr d Λ) (S.fr' d Λ) y := by
  intro F _ _ _ _ _ E _ _ _ L r k S j β βJ d Λ hT hF x x' u s hM Λ₁ hΛ₁
  obtain ⟨n₀, hn₀, n₀', hn₀', n'', hn'', -, e0i, e0', e'', emv, hW₁⟩ :=
    GlobalTheory.T.move_lattice_isTerm_same_datum_with_witnesses L r k S j β βJ d Λ hT hF x x' u s hM
  obtain ⟨hsx, -, -, -, -, -, -, -, -, hxX, hxX'⟩ :=
    GlobalTheory.T.hermitianDoubleCosetFrames_datum_move_properties L r k S j β βJ d Λ hT hF x x' u s hM
  have eΛ : n₀⁻¹ • Λ = Λ₁ := SetLike.coe_injective (emv.trans hΛ₁.symm)
  rw [eΛ] at hW₁
  obtain ⟨-, hW, -, -, -, hli, -⟩ := TermBasic.term_basic L r k S d Λ hT
  obtain ⟨-, eM, -, eL, -⟩ := WitIndep.witness_independence L r k S d Λ₁ _ _ hW₁
  have hli₁ := indep S hW₁.2.2.1 hW₁.2.2.2.1
  have hg : ∀ a (j : Fin r), hf L S.Hm (S.f a) (S.f j.castSucc) = 0 := fun a j => by
    simp [S.gram, Fin.castSucc_ne_last]
  have hg' : ∀ a (j : Fin r), hf L S.Hm (S.f' a) (S.f' j.castSucc) = 0 := fun a j => by
    simp [S.gram', Fin.castSucc_ne_last]
  obtain ⟨-, -, hb, -, huΛ, hu, -, -⟩ := hM
  have hH := S.herm.1
  have hyu : ∀ y ∈ S.spanTo S.f (j + 1) ⊔ S.spanTo S.f' (j + 1), hf L S.Hm y u = 0 := fun y hy => by
    rw [← hf_cj L hH, hu y hy, map_zero]
  have hJ : (j : ℕ) + 1 ≤ r := j.2
  have hn := hW.2.2.1
  have hn' := hW.2.2.2.1
  have f1 : ∀ i : Fin (r + 1), (i : ℕ) < j + 1 → (n₀⁻¹ * (S.wit d Λ).1) (S.f i) = S.fr d Λ i := by
    intro i hi
    have hm : S.fr d Λ i ∈ S.spanTo S.f (j + 1) :=
      TermBasic.map_mem hg hn _ (TermBasic.self_mem S S.f hi)
    show n₀⁻¹ (S.fr d Λ i) = _
    rw [e0i, eich, hf_neg_r, hyu _ (Submodule.mem_sup_left hm), iso_span S hg hm x hxX]
    simp
  have f2 : ∀ i : Fin (r + 1), (i : ℕ) < j + 1 →
      (n'' * n₀' * (S.wit d Λ).2) (S.f' i) = S.fr' d Λ i := by
    intro i hi
    have hm : S.fr' d Λ i ∈ S.spanTo S.f' (j + 1) :=
      TermBasic.map_mem hg' hn' _ (TermBasic.self_mem S S.f' hi)
    show n'' (n₀' (S.fr' d Λ i)) = _
    rw [e0', eich, hyu _ (Submodule.mem_sup_right hm), iso_span S hg' hm x' hxX']
    simp only [zero_smul, add_zero, sub_zero]
    exact e'' _ (iso_span S hg' hm)
  refine ⟨⟨(_, _), hW₁⟩, fun y hy => ?_⟩
  have hyu0 := hyu y hy
  obtain ⟨v, hv, v', hv', rfl⟩ := Submodule.mem_sup.1 hy
  obtain ⟨c, hc, ec⟩ := exists_coef_map S hg hn hv
  obtain ⟨c', hc', ec'⟩ := exists_coef_map S hg' hn' hv'
  have e1 : v + v' = ∑ i, c i • S.fr d Λ i + ∑ i, c' i • S.fr' d Λ i := by
    rw [ec, ec']; rfl
  have e2 : v + v' = ∑ i, c i • (n₀⁻¹ * (S.wit d Λ).1) (S.f i) +
      ∑ i, c' i • (n'' * n₀' * (S.wit d Λ).2) (S.f' i) := by
    rw [e1]
    congr 1 <;> refine Finset.sum_congr rfl fun i _ => ?_
    · by_cases hi : (i : ℕ) < j + 1
      · rw [f1 i hi]
      · rw [hc i hi, zero_smul, zero_smul]
    · by_cases hi : (i : ℕ) < j + 1
      · rw [f2 i hi]
      · rw [hc' i hi, zero_smul, zero_smul]
  refine ⟨fun hyΛ => ?_, ?_, ?_⟩
  · have hvX : v ∈ S.X := TermBasic.spanTo_mono S S.f hJ hv
    have hvX' : v' ∈ S.X' := TermBasic.spanTo_mono S S.f' hJ hv'
    obtain ⟨a, ha, ea⟩ := hF.1.2.2 x hxX x' hxX' _ (S.X.smul_mem (algebraMap F E S.th) hvX) _
      (S.X'.smul_mem (algebraMap F E S.th) hvX') hb ⟨_, hyΛ, (smul_add _ _ _).symm⟩
    rw [Frames.h, hf_smul_r, AlgEquiv.commutes] at ea
    have ea2 : hf L S.Hm x v' = a := by
      have := congrArg (algebraMap F E S.th⁻¹ * ·) ea
      simpa only [← mul_assoc, WitIndep.th_mul S, one_mul] using this
    have ea3 : hf L S.Hm (v + v') x = L.cj a := by
      rw [hf_add_l, iso_span S hg hv x hxX, zero_add, ← ea2, hf_cj L hH]
    rw [← SetLike.mem_coe, hΛ₁]
    show eich L S.Hm x u s (v + v') ∈ Λ
    rw [eich, hyu0, ea3, zero_smul, add_zero]
    exact Λ.sub_mem hyΛ (Λ.smul_mem (⟨_, UnramOrder.cj_mem L ha⟩ : L.O) (Λ.add_mem huΛ hsx))
  · rw [eM, Frames.M, mem_Mof, mem_Mof]
    exact ⟨transfer hli₁ e2 e1 _, transfer hli e1 e2 _⟩
  · rw [eL, Frames.lev, Frames.lev]
    congr 1
    ext t
    exact ⟨transfer hli₁ e2 e1 _, transfer hli e1 e2 _⟩

end GlobalTheory.HL.MoveSame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianTermCountFrameClassLe
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.TermCount

theorem encard_le_mul {α β : Type} (s : Set α) (f : α → β) (t : Set β) (A B : ℝ≥0∞)
    (hf : ∀ a ∈ s, f a ∈ t) (ht : (t.encard : ℝ≥0∞) ≤ A)
    (hB : ∀ b ∈ t, (({a | a ∈ s ∧ f a = b} : Set α).encard : ℝ≥0∞) ≤ B) :
    (s.encard : ℝ≥0∞) ≤ A * B := by
  have h1 : s ⊆ ⋃ b : t, {a | a ∈ s ∧ f a = b.1} := by
    intro a ha
    exact Set.mem_iUnion.2 ⟨⟨f a, hf a ha⟩, ha, rfl⟩
  calc (s.encard : ℝ≥0∞) = ∑' _ : s, (1 : ℝ≥0∞) := (ENNReal.tsum_set_one s).symm
    _ ≤ ∑' _ : (⋃ b : t, {a | a ∈ s ∧ f a = b.1} : Set α), (1 : ℝ≥0∞) :=
        ENNReal.tsum_mono_subtype (fun _ => (1 : ℝ≥0∞)) h1
    _ ≤ ∑' b : t, ∑' _ : ({a | a ∈ s ∧ f a = b.1} : Set α), (1 : ℝ≥0∞) :=
        ENNReal.tsum_iUnion_le_tsum (fun _ => (1 : ℝ≥0∞)) _
    _ ≤ ∑' _ : t, B := by
        refine ENNReal.tsum_le_tsum fun b => ?_
        rw [ENNReal.tsum_set_one]
        exact hB b.1 b.2
    _ = (t.encard : ℝ≥0∞) * B := ENNReal.tsum_set_const t B
    _ ≤ A * B := by gcongr

theorem nT_cardI_le {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
    (L : LocE F E) (r k : ℕ) (S : Frames L r k) (d : S.Datum) (C : Set S.FrP) (j : ℕ) :
    (S.nT d C fun Λ => S.cardI d Λ = j) ≤ ENNReal.ofReal (S.Hp ^ (12 * (r + 1)) * (j : ℝ) ^ (k - 1)) := by
  unfold Frames.nT
  set s : Set (Submodule L.O S.V) := {Λ | S.IsTerm d Λ ∧ S.cardI d Λ = j ∧ S.Fr d Λ = C} with hs
  rcases s.eq_empty_or_nonempty with he | ⟨Λ₁, hΛ₁, -, hC₁⟩
  · simp [he]
  obtain ⟨ha, -, -, hq, hH1, -⟩ := GlobalTheory.T.term_exponents_nonneg_and_defect_group_bound L r k S d Λ₁ hΛ₁
  have hcls : S.IsCls C := hC₁ ▸ (GlobalTheory.HL.TermBasic.term_basic L r k S d Λ₁ hΛ₁).2.2.2.2.2.2.1.1
  have hp : (S.fr d Λ₁, S.fr' d Λ₁) ∈ C :=
    hC₁ ▸ (GlobalTheory.HL.FrameClass.frame_classes L r k S (S.fr d Λ₁) (S.fr' d Λ₁)).1
  have hM : ∀ Λ ∈ s, S.Mof (S.fr d Λ₁) (S.fr' d Λ₁) ≤ S.sat Λ := by
    rintro Λ ⟨hΛ, -, hC⟩
    have h1 := ((GlobalTheory.HL.FrameClass.frame_classes L r k S (S.fr d Λ) (S.fr' d Λ)).2.1
      (S.fr d Λ₁, S.fr' d Λ₁) (by
        have : S.frameCls (S.fr d Λ) (S.fr' d Λ) = C := hC
        rw [this]; exact hp)).2
    simp only at h1
    rw [h1]
    exact (GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hΛ).2.2.1
  have hmain : (s.encard : ℝ≥0∞) ≤ (S.q : ℝ≥0∞) ^ (2 * S.a.toNat * (2 * r + 2)) *
      (((S.q : ℝ≥0∞) ^ (S.a.toNat * (2 * r + 2)) * (j : ℝ≥0∞) ^ (k - 1)) *
        (S.q : ℝ≥0∞) ^ (2 * S.a.toNat * (2 * r + 2))) := by
    refine encard_le_mul s S.sat _ _ _ ?_ (GlobalTheory.T.lattice_count_bound_frames L r k S C hcls _ hp ha) ?_
    · intro Λ hΛ
      refine ⟨hM Λ hΛ, fun x hx => hx.2, fun x hx y hy => ?_⟩
      exact ((GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hΛ.1).1.2 y).2 hy.1 x hx.1
    · intro Mh hMh
      refine encard_le_mul _ (fun Λ : Submodule L.O S.V => Λ ⊓ S.W0.restrictScalars L.O) _ _ _ ?_
        (GlobalTheory.T.encard_gluingHom_kernels_le L r k S d C Mh j) ?_
      · rintro Λ ⟨⟨h1, h2, h3⟩, h4⟩
        exact ⟨Λ, ⟨h1, h3, h4, h2⟩, rfl⟩
      · intro Λ₀ _
        refine le_trans ?_ (GlobalTheory.T.encard_selfDual_sat_inf_W0_le_q_pow L r k S C hcls _ hp Mh Λ₀ hMh.1)
        refine ENat.toENNReal_le.2 (Set.encard_le_encard ?_)
        rintro Λ ⟨⟨⟨h1, -, -⟩, h4⟩, h5⟩
        exact ⟨(GlobalTheory.HL.TermBasic.term_basic L r k S d Λ h1).1, h4, h5⟩
  refine hmain.trans ?_
  have hq' : (S.q : ℝ) ^ S.a.toNat ≤ S.Hp := by
    have : S.a = (S.a.toNat : ℤ) := (Int.toNat_of_nonneg ha).symm
    rw [this, zpow_natCast] at hq
    exact hq
  have hreal : ((S.q : ℝ) ^ S.a.toNat) ^ (10 * (r + 1)) * (j : ℝ) ^ (k - 1) ≤
      S.Hp ^ (12 * (r + 1)) * (j : ℝ) ^ (k - 1) := by
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    calc ((S.q : ℝ) ^ S.a.toNat) ^ (10 * (r + 1)) ≤ S.Hp ^ (10 * (r + 1)) :=
          pow_le_pow_left₀ (by positivity) hq' _
      _ ≤ S.Hp ^ (12 * (r + 1)) := pow_le_pow_right₀ hH1 (by omega)
  refine le_trans (le_of_eq ?_) (ENNReal.ofReal_le_ofReal hreal)
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
  ring

end GlobalTheory.HL.TermCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianTermStabilizerCommensurable
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.LocComm

theorem stab_commensurable : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → ∀ (d : LocNG.Datum P) (τ : Term V M r), LocNG.IsTermOver P d τ → P.UW0 ⊓ LocNG.Aut τ.abelian₂ ≤ LocNG.Datum.Stab d ∧ (P.UW0 ⊓ LocNG.Aut τ.abelian₂).relIndex (LocNG.Datum.Stab d) ≠ 0 ∧ ∀ (d' : LocNG.Datum P) (τ' : Term V M r), LocNG.IsTermOver P d' τ' → (LocNG.Datum.Stab d).relIndex (LocNG.Datum.Stab d') ≠ 0 := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P hk hrel d τ hτ
  haveI := hM.loc
  haveI := hM.char0
  obtain ⟨S, ⟨c⟩⟩ := GlobalTheory.HL.CoordExist.exists_coord M hM H r k P hk hrel
  obtain ⟨hUW, -, -, -, hAut, -⟩ := GlobalTheory.T.framePairCoordinates_transport_unitary_mass M hM H r k P S c
  obtain ⟨-, -, -, hStab, -⟩ := GlobalTheory.T.hermitianFramePairCoordinates_transport_innerData M hM H r k P S c
  obtain ⟨hTC, -, -⟩ := GlobalTheory.T.isTerm_and_om_eq_of_coord_isTermOver M hM H r k P S c
  have key : ∀ (d : LocNG.Datum P) (τ : Term V M r), LocNG.IsTermOver P d τ →
      S.IsTerm (c.dat d) (c.lat τ.abelian₂) := fun d τ h => (hTC d τ h).1
  have eA : ∀ Λ, P.UW0 ⊓ LocNG.Aut Λ =
      (S.H0 ⊓ MulAction.stabilizer S.GLV (c.lat Λ)).comap c.grp.toMonoidHom := by
    intro Λ
    ext g
    simp only [Subgroup.mem_inf, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom]
    rw [hUW, hAut]
  have eS : ∀ d : LocNG.Datum P, LocNG.Datum.Stab d =
      (S.H0 ⊓ MulAction.stabilizer S.GLV (c.dat d)).comap c.grp.toMonoidHom := by
    intro d
    ext g
    rw [Subgroup.mem_comap, hStab]
    rfl
  have rel : ∀ A B : Subgroup S.GLV,
      (A.comap c.grp.toMonoidHom).relIndex (B.comap c.grp.toMonoidHom) = A.relIndex B := by
    intro A B
    rw [Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective c.grp.surjective]
  have fixd : ∀ (d : LocNG.Datum P) (τ : Term V M r), LocNG.IsTermOver P d τ →
      S.H0 ⊓ MulAction.stabilizer S.GLV (c.lat τ.abelian₂) ≤ S.H0 ⊓ MulAction.stabilizer S.GLV (c.dat d) := by
    intro d τ h x hx
    obtain ⟨hx0, hxs⟩ := Subgroup.mem_inf.mp hx
    have ht := key d τ h
    have h1 := (GlobalTheory.T.hermitianFrames_complementUnitary_acts_on_terms M.L r k S _ _ ht x hx0).1
    rw [MulAction.mem_stabilizer_iff.mp hxs] at h1
    have h2 := (GlobalTheory.T.hermitian_double_coset_term_basic_facts M.L r k S _ _ ht).2.2.2.2.2.2.2 _ h1
    exact Subgroup.mem_inf.mpr ⟨hx0, MulAction.mem_stabilizer_iff.mpr h2⟩
  have volH := GlobalTheory.T.stabilizer_commensurable_invVolume_smul_complement M.L r k S
  have cLam : ∀ (d : LocNG.Datum P) (τ : Term V M r), LocNG.IsTermOver P d τ →
      S.complementReferenceCompactSubgroup.Commensurable (S.H0 ⊓ MulAction.stabilizer S.GLV (c.lat τ.abelian₂)) := by
    intro d τ h
    have := volH.1 _ (GlobalTheory.T.hermitian_double_coset_term_basic_facts M.L r k S _ _ (key d τ h)).1.1
    exact ⟨this.1, this.2.1⟩
  have cDat : ∀ (d : LocNG.Datum P) (τ : Term V M r), LocNG.IsTermOver P d τ →
      S.complementReferenceCompactSubgroup.Commensurable (S.H0 ⊓ MulAction.stabilizer S.GLV (c.dat d)) := by
    intro d τ h
    exact volH.2 _ _ (key d τ h)
  refine ⟨?_, ?_, ?_⟩
  · rw [eA, eS]
    exact Subgroup.comap_mono (fixd d τ hτ)
  · rw [eA, eS, rel]
    exact ((cLam d τ hτ).symm.trans (cDat d τ hτ)).1
  · intro d' τ' hτ'
    rw [eS, eS, rel]
    exact ((cDat d τ hτ).symm.trans (cDat d' τ' hτ')).1

end GlobalTheory.HL.LocComm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassOrbitClass
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.MassOrbit

theorem mass_orbit_class {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
    (L : LocE F E) (r k : ℕ) (S : Frames L r k) (d₁ : S.Datum) (Λ₁ : Submodule L.O S.V)
    (h₁ : S.IsTerm d₁ Λ₁) (d : S.Datum) :
    (S.mass d fun Λ => S.BBzero d Λ ∧ ∃ s ∈ S.St, S.Fr d Λ = s • S.Fr d₁ Λ₁) =
      ENNReal.ofReal (S.wC (S.Fr d₁ Λ₁)) * S.nT d (S.Fr d₁ Λ₁) fun Λ => S.BBzero d Λ := by
  have act := @GlobalTheory.FrameAct.stabiliser_acts_on_terms F _ _ _ _ _ E _ _ _ L r k S
  have trm := @GlobalTheory.HL.TermBasic.term_basic F _ _ _ _ _ E _ _ _ L r k S
  have vol := (@GlobalTheory.HL.volSt F _ _ _ _ _ E _ _ _ L r k S).2
  have hT : ∀ d Λ, S.IsTerm d Λ → ∀ h ∈ S.St, S.IsTerm d (h • Λ) := fun d Λ H h hh => (act d Λ H h hh).1
  have hF : ∀ d Λ, S.IsTerm d Λ → ∀ h ∈ S.St, S.Fr d (h • Λ) = h • S.Fr d Λ :=
    fun d Λ H h hh => (act d Λ H h hh).2.2.2.2.1
  have hB : ∀ d Λ, S.IsTerm d Λ → ∀ h ∈ S.St, (S.BBzero d (h • Λ) ↔ S.BBzero d Λ) :=
    fun d Λ H h hh => (act d Λ H h hh).2.2.2.2.2.2.2.1
  have hI : ∀ d Λ, S.IsTerm d Λ → S.IsIntCls (S.Fr d Λ) := fun d Λ H => (trm d Λ H).2.2.2.2.2.2.1
  rw [GlobalTheory.HL.mass_eq_sumCls L r k S d _ (by
    rintro h hh Λ H ⟨hb, s, hs, e⟩
    refine ⟨(hB d Λ H h hh).2 hb, h * s, S.St.mul_mem hh hs, ?_⟩
    rw [hF d Λ H h hh, e, mul_smul])]
  set C₁ := S.Fr d₁ Λ₁ with hC
  unfold Frames.sumCls
  rw [tsum_eq_single (Quotient.mk (MulAction.orbitRel S.St (Set S.FrP)) C₁)]
  · have hrel : (MulAction.orbitRel S.St (Set S.FrP))
        (Quotient.mk (MulAction.orbitRel S.St (Set S.FrP)) C₁).out C₁ := Quotient.mk_out C₁
    obtain ⟨⟨h, hh⟩, e⟩ := MulAction.orbitRel_apply.1 hrel
    have e' : (Quotient.mk (MulAction.orbitRel S.St (Set S.FrP)) C₁).out = h • C₁ := e.symm
    have hint : S.IsIntCls (h • C₁) := by
      rw [hC, ← hF d₁ Λ₁ h₁ h hh]
      exact hI _ _ (hT _ _ h₁ h hh)
    change (if S.IsIntCls (Quotient.mk (MulAction.orbitRel S.St (Set S.FrP)) C₁).out then
      ENNReal.ofReal (S.wC (Quotient.mk (MulAction.orbitRel S.St (Set S.FrP)) C₁).out) *
        S.nT d (Quotient.mk (MulAction.orbitRel S.St (Set S.FrP)) C₁).out _ else 0) = _
    rw [e', if_pos hint, (vol C₁ (hI _ _ h₁).1).2.2.2 h hh]
    congr 1
    unfold Frames.nT
    congr 1
    have hset : {Λ : Submodule L.O S.V | S.IsTerm d Λ ∧
        (S.BBzero d Λ ∧ ∃ s ∈ S.St, S.Fr d Λ = s • C₁) ∧ S.Fr d Λ = h • C₁} =
        (fun Λ : Submodule L.O S.V => h • Λ) '' {Λ | S.IsTerm d Λ ∧ S.BBzero d Λ ∧ S.Fr d Λ = C₁} := by
      ext Λ
      constructor
      · rintro ⟨H, ⟨hb, -⟩, e⟩
        have hi := S.St.inv_mem hh
        refine ⟨h⁻¹ • Λ, ⟨hT _ _ H _ hi, (hB _ _ H _ hi).2 hb, ?_⟩, smul_inv_smul h Λ⟩
        rw [hF _ _ H _ hi, e, inv_smul_smul]
      · rintro ⟨Λ', ⟨H, hb, e⟩, rfl⟩
        have e2 : S.Fr d (h • Λ') = h • C₁ := by rw [hF _ _ H _ hh, e]
        exact ⟨hT _ _ H _ hh, ⟨(hB _ _ H _ hh).2 hb, h, hh, e2⟩, e2⟩
    rw [hset]
    exact (MulAction.injective h).encard_image _
  · intro o ho
    have h0 : S.nT d o.out (fun Λ => S.BBzero d Λ ∧ ∃ s ∈ S.St, S.Fr d Λ = s • C₁) = 0 := by
      unfold Frames.nT
      have : {Λ : Submodule L.O S.V | S.IsTerm d Λ ∧
        (S.BBzero d Λ ∧ ∃ s ∈ S.St, S.Fr d Λ = s • C₁) ∧ S.Fr d Λ = o.out} = ∅ := by
        ext Λ
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨-, ⟨-, s, hs, e⟩, e2⟩
        apply ho
        rw [← Quotient.out_eq o]
        apply Quotient.sound
        exact MulAction.orbitRel_apply.2 ⟨⟨s, hs⟩, by rw [← e2, e]; rfl⟩
      rw [this]
      simp
    simp only [h0, mul_zero, ite_self]

end GlobalTheory.HL.MassOrbit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimitiveTuplesHermitianGramCosetContentStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitiveTuples_hermitianGram_coset_content : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ Λs, IsSD L Hm Λs → ∀ m : ℕ, 2 * m + 3 ≤ n → ∀ B : Set (Matrix (Fin m) (Fin m) E), (∀ X ∈ B, X ∈ hermLat L m) → IsCO (hermLat L m) B → IsCO (tupLat L Λs m) {z : Fin m → Fin n → E | IsPrimT L Hm Λs z ∧ gramT L Hm z ∈ B} ∧ cont (hermLat L m) B ≤ 2 * cont (tupLat L Λs m) {z : Fin m → Fin n → E | IsPrimT L Hm Λs z ∧ gramT L Hm z ∈ B} ∧ cont (tupLat L Λs m) {z : Fin m → Fin n → E | IsPrimT L Hm Λs z ∧ gramT L Hm z ∈ B} ≤ 2 * cont (hermLat L m) B := by
  first | exact @GlobalTheory.HL.PrimVol.cont_primitive_tuples | exact GlobalTheory.HL.PrimVol.cont_primitive_tuples | (intros; apply GlobalTheory.HL.PrimVol.cont_primitive_tuples <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryComplementMovesHermitianTermsStatement
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryComplement_moves_hermitianTerms : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → ∀ (f f' : Fin (r + 1) → V), (∃ n ∈ P.A.N, f = fun b => n (P.A.f b)) → (∃ n' ∈ P.B.N, f' = fun b => n' (P.B.f b)) → ∀ g ∈ P.UW0, ∀ d d' : LocNG.Datum P, LocNG.Datum.Moves g d d' → (∀ b, g (f b) = f b ∧ g (f' b) = f' b) ∧ LocNG.img g '' {Λ | LocNG.IsTermOver P d (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r) ∧ ¬ LocNG.BBne (H := H) (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r)} = {Λ | LocNG.IsTermOver P d' (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r) ∧ ¬ LocNG.BBne (H := H) (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r)} := by
  first | exact @GlobalTheory.HL.ComplMove.main | exact GlobalTheory.HL.ComplMove.main | (intros; apply GlobalTheory.HL.ComplMove.main <;> assumption)
end

