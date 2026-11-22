import Formalism.LocalToGlobal.CharacterGerms.RowTieUpFBrS
import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.Bundle0001
import Formalism.LocalToGlobal.CharacterGerms.TripleSubstSecondCoordinate

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTieUpFBrEF
section
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace UpFBr

theorem echelon {C : Type} [Field C] (vm : Valuation C NNReal) (n : ℕ) :
    ∀ (k : ℕ) (M : Submodule C (Fin n → C)), Module.finrank C M = k →
    ∃ (s : ℕ) (J : Fin s → Fin n) (B : Fin s → Fin n → C), (∀ i, B i ∈ M) ∧ (∀ i x, vm (B i x) ≤ 1) ∧
      (∀ i i', B i (J i') = if i = i' then 1 else 0) ∧ ∀ v ∈ M, v = ∑ i, v (J i) • B i := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro M hM
  by_cases h0 : ∃ v ∈ M, v ≠ 0
  swap
  · push_neg at h0
    refine ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
      fun v hv => ?_⟩
    simp [h0 v hv]
  obtain ⟨v, hvM, hv0⟩ := h0
  obtain ⟨x₀, hx₀⟩ := Function.ne_iff.1 hv0
  obtain ⟨j, -, hjmax⟩ := (Finset.univ : Finset (Fin n)).exists_max_image (fun x => vm (v x))
    ⟨x₀, Finset.mem_univ _⟩
  have hvj : v j ≠ 0 := by
    intro h
    have h1 : vm (v x₀) ≤ vm (v j) := hjmax x₀ (Finset.mem_univ _)
    rw [h, map_zero] at h1
    exact hx₀ ((Valuation.zero_iff vm).1 (le_antisymm h1 zero_le'))

  set v₀ : Fin n → C := (v j)⁻¹ • v with hv₀
  have hv₀j : v₀ j = 1 := by simp [hv₀, hvj]
  have hv₀M : v₀ ∈ M := M.smul_mem _ hvM
  have hv₀le : ∀ x, vm (v₀ x) ≤ 1 := by
    intro x
    have hpos : 0 < vm (v j) := pos_iff_ne_zero.2 ((Valuation.ne_zero_iff vm).2 hvj)
    simp only [hv₀, Pi.smul_apply, smul_eq_mul, map_mul, map_inv₀]
    rw [inv_mul_le_iff₀ hpos, mul_one]
    exact hjmax x (Finset.mem_univ _)
  set M' : Submodule C (Fin n → C) := M ⊓ LinearMap.ker (LinearMap.proj j) with hM'
  have hlt : M' < M := by
    refine lt_of_le_of_ne inf_le_left fun h => ?_
    have h1 : v₀ ∈ M' := h ▸ hv₀M
    have h2 : v₀ j = 0 := (Submodule.mem_inf.1 h1).2
    rw [hv₀j] at h2
    exact one_ne_zero h2
  have hfr : Module.finrank C M' < k := hM ▸ Submodule.finrank_lt_finrank_of_lt hlt
  obtain ⟨s, J', B', hB'M, hB'le, hB'δ, hB'span⟩ := ih _ hfr M' rfl
  have hB'j : ∀ i, B' i j = 0 := fun i => (Submodule.mem_inf.1 (hB'M i)).2
  have hB'M0 : ∀ i, B' i ∈ M := fun i => (Submodule.mem_inf.1 (hB'M i)).1
  set b : Fin n → C := v₀ - ∑ i, v₀ (J' i) • B' i with hb
  have hbM : b ∈ M := M.sub_mem hv₀M (M.sum_mem fun i _ => M.smul_mem _ (hB'M0 i))
  have hbj : b j = 1 := by simp [hb, Finset.sum_apply, hB'j, hv₀j]
  have hbJ : ∀ i', b (J' i') = 0 := by
    intro i'
    simp [hb, Finset.sum_apply, hB'δ]
  have hble : ∀ x, vm (b x) ≤ 1 := by
    intro x
    simp only [hb, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Valuation.map_sub_le _ (hv₀le x) (Valuation.map_sum_le _ fun i _ => ?_)
    rw [map_mul]
    exact mul_le_one' (hv₀le _) (hB'le i x)
  refine ⟨s + 1, (Fin.cons j J' : Fin (s + 1) → Fin n), (Fin.cons b B' : Fin (s + 1) → Fin n → C),
    ?_, ?_, ?_, ?_⟩
  · intro i
    induction i using Fin.cases with
    | zero => simpa using hbM
    | succ i => simpa using hB'M0 i
  · intro i x
    induction i using Fin.cases with
    | zero => simpa using hble x
    | succ i => simpa using hB'le i x
  · intro i i'
    induction i using Fin.cases with
    | zero =>
      induction i' using Fin.cases with
      | zero => simp [hbj]
      | succ i' => simp only [Fin.cons_zero, Fin.cons_succ, hbJ]; rw [if_neg (Fin.succ_ne_zero i').symm]
    | succ i =>
      induction i' using Fin.cases with
      | zero => simp only [Fin.cons_zero, Fin.cons_succ, hB'j]; rw [if_neg (Fin.succ_ne_zero i)]
      | succ i' => simp [hB'δ, Fin.succ_inj]
  · intro w hw
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    have hw' : w - w j • b ∈ M' := by
      refine Submodule.mem_inf.2 ⟨M.sub_mem hw (M.smul_mem _ hbM), ?_⟩
      simp [LinearMap.mem_ker, hbj]
    have h1 := hB'span _ hw'
    have e : ∀ i, (w - w j • b) (J' i) = w (J' i) := by
      intro i
      simp [hbJ]
    simp only [e] at h1
    rw [← h1]
    abel

theorem eigFreeSt_holds : EigFreeSt := by
  intro C _ vm R _ _ hI n ι L χ
  set f := algebraMap R C
  let M : Submodule C (Fin n → C) :=
    { carrier := {w | ∀ a, ((L a).map f).mulVec w = f (χ a) • w}
      add_mem' := by
        intro w w' hw hw' a
        simp only [Set.mem_setOf_eq] at hw hw' ⊢
        rw [Matrix.mulVec_add, hw a, hw' a, smul_add]
      zero_mem' := by
        intro a
        simp
      smul_mem' := by
        intro c w hw a
        simp only [Set.mem_setOf_eq] at hw ⊢
        rw [Matrix.mulVec_smul, hw a, smul_comm] }
  obtain ⟨s, J, B, hBM, hBle, hBδ, hspan⟩ := echelon vm n _ M rfl
  have hlift : ∀ i x, ∃ r : R, f r = B i x := fun i x => hI.exists_of_le_one (hBle i x)
  choose W hW using hlift
  have hfW : ∀ i, f ∘ W i = B i := fun i => funext (hW i)
  have hmap : ∀ (A : Matrix (Fin n) (Fin n) R) (v : Fin n → R), f ∘ (A.mulVec v) = (A.map f).mulVec (f ∘ v) := by
    intro A v
    funext x
    simp [Matrix.mulVec, dotProduct, map_sum]
  have hinj : Function.Injective f := hI.hom_inj
  have hinjv : ∀ v w : Fin n → R, f ∘ v = f ∘ w → v = w :=
    fun v w h => funext fun x => hinj (congrFun h x)
  refine ⟨s, W, fun i a => ?_, fun v hv => ?_⟩
  · apply hinjv
    rw [hmap, hfW, hBM i a]
    funext x
    simp [hW]
  · have hvM : f ∘ v ∈ M := by
      intro a
      rw [← hmap, hv a]
      funext x
      simp
    refine ⟨fun i => v (J i), ?_, ?_⟩
    · apply hinjv
      have h1 := hspan _ hvM
      funext x
      have hx := congrFun h1 x
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply] at hx ⊢
      rw [map_sum]
      simp only [map_mul, hW]
      exact hx.symm
    · intro c hc
      funext i
      have h1 := congrFun hc (J i)
      apply hinj
      rw [← h1]
      simp [Finset.sum_apply, map_sum, hW, hBδ]

end UpFBr

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTieUpFBrPlB
section
set_option autoImplicit false

noncomputable section

namespace Formalism.L2.FormalSeriesBounds

namespace UpFBr

open ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs

theorem placeSt_of_X (h : Pl.PlaceCriterionOfIdempotent) : PlaceSt := by
  intro l _ OE _ _ _ _ _ R _ _ _ _ _ hl hd d _ em h1 h2 h3
  obtain ⟨e, he1, he2, he3, iN, t, jj, hj, ht, b, hb⟩ := h l OE R hl hd d em h1 h2 h3
  exact ⟨⟨e, he1, he2, he3⟩, iN, t, jj, hj, ht, b, hb⟩

end UpFBr

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.ValuationEqPairOfBiadditiveCross
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]

namespace VP

theorem Aterm_eq (Y : FBChart C V O dd) (π : Orb → Fin 2 → Fin dd → PS C 1 dd)
    (hπ0 : ∀ o g i, MvPowerSeries.constantCoeff (π o g i) = 0) (s s' : Orb × Fin 2) :
    Aterm Y π s s' = mvExp ((Y.k : C) • hAt Y (π s.1 s.2) (actAt Y Y.w0 (π s'.1 s'.2))) := by
  unfold Aterm
  rw [eval_two_points_eq_subst _ _ _ rfl, compose_one_action_eq_actAt]
  exact expS_eq _ (cc_smul _ (cc_hAt Y (hπ0 _ _) (cc_actAt Y _ (hπ0 _ _))))

theorem hRow_eq (Y : FBChart C V O dd) {J : Fin 2 → Type} [∀ g, Fintype (J g)] (q : PairData Y d J) :
    (Y.raw q).hRow = (Y.k : C) • hAt Y ((Y.raw q).expPt 0) ((Y.raw q).expPt 1) := by
  unfold RawChart.hRow hAt
  congr 2
  funext x
  obtain ⟨g, i⟩ := x
  fin_cases g <;> rfl

end VP

theorem pair_holds (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o)) : PairSt Y p := by
  intro _ π hπ o
  have hX := hπ.cc o 0
  have hZ := hπ.cc o 1
  have hwX := VP.cc_actAt Y Y.w0 hX
  have hwZ := VP.cc_actAt Y Y.w0 hZ
  have hbZ := VP.cc_actAt Y (star Y.w0) hZ
  have hid := VP.pair_id Y hX hZ
  set W : PS C 1 dd := MvPowerSeries.subst (VP.P2 (VP.actAt Y Y.w0 (π o 0)) (π o 1)) Y.B.sy *
    MvPowerSeries.subst (VP.P2 (π o 0) (π o 1)) (Y.B.ad Y.w0) *
    MvPowerSeries.subst (VP.P3 (π o 0) (VP.actAt Y Y.w0 (π o 1)) (VP.actAt Y (star Y.w0) (π o 1))) Y.B.ph2 with hW
  have hWi : IntS V W :=
    ((IntS.subst (VP.constantCoeff_pair_substitution hwX hZ) (VP.integral_pair_substitution (VP.int_actAt Y _ hX (hπ.int o 0)) (hπ.int o 1)) Y.intSy).mul
      (IntS.subst (VP.constantCoeff_pair_substitution hX hZ) (VP.integral_pair_substitution (hπ.int o 0) (hπ.int o 1)) (Y.intAd _))).mul
      (IntS.subst (VP.constantCoeff_triple_substitution hX hwZ hbZ) (VP.integral_triple_substitution (hπ.int o 0) (VP.int_actAt Y _ hZ (hπ.int o 1))
        (VP.int_actAt Y _ hZ (hπ.int o 1))) Y.intPh2)
  have hW1 : MvPowerSeries.constantCoeff W = 1 := by rw [← hid, VP.cc_mvExp']
  refine ⟨W ^ Y.k, ⟨hWi.pow _, by rw [map_pow, hW1, one_pow, V.v.map_one]⟩, ?_⟩
  have c1 := VP.cc_hAt Y hX hwZ
  have c2 := VP.cc_hAt Y hZ hwX
  have c3 := VP.cc_hAt Y hX hZ
  have hprod : Aterm Y π (o, 0) (o, 1) * Aterm Y π (o, 1) (o, 0) =
      W ^ Y.k * mvExp ((Y.k : C) • VP.hAt Y (π o 0) (π o 1)) := by
    rw [VP.Aterm_eq Y π hπ.cc, VP.Aterm_eq Y π hπ.cc, ← VP.exp_add (VP.cc_smul _ c1) (VP.cc_smul _ c2), ← hid,
      ← VP.exp_nsmul (by rw [map_sub, map_add, c1, c2, c3]; simp),
      ← VP.exp_add (VP.cc_smul _ (by rw [map_sub, map_add, c1, c2, c3]; simp)) (VP.cc_smul _ c3)]
    congr 1
    rw [← smul_add, ← smul_add]
    congr 1
    ring
  have hE : ∀ g i, MvPowerSeries.constantCoeff ((Y.raw (p o)).expPt g i) = 0 := fun g i => by
    rw [← VP.cc_toAllS o, ← hπ.pull o g i]
    exact (VP.cc_subst_eq (VP.cc_pull1Pt Y p) _).trans (hπ.cc o g i)
  have hpull : pull1 Y p (mvExp ((Y.k : C) • VP.hAt Y (π o 0) (π o 1))) = toAllS o (mvExp (Y.raw (p o)).hRow) := by
    unfold pull1 toAllS
    rw [VP.subst_exp (VP.cc_pull1Pt Y p) (VP.cc_smul _ c3), VP.subst_smul (VP.cc_pull1Pt Y p),
      VP.hAt_subst Y (VP.cc_pull1Pt Y p) hX hZ, VP.hRow_eq,
      VP.subst_exp (fun _ => VP.cc_X _) (VP.cc_smul _ (VP.cc_hAt Y (hE 0) (hE 1))),
      VP.subst_smul (fun _ => VP.cc_X _), VP.hAt_subst Y (fun _ => VP.cc_X _) (hE 0) (hE 1)]
    congr 3
    · funext i; exact hπ.pull o 0 i
    · funext i; exact hπ.pull o 1 i
  rw [← VP.pullback_one_var_mul, hprod, VP.pullback_one_var_mul, hpull]

theorem valuation_eq_pair_of_biadditive_cross (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o)) (H : ∀ o, (Y.raw (p o)).Hyps V)
    (Ls : LetSys C dd) (n : ℕ) (hP : ProjPullSt Y p) (hT : ∀ o, RawChart.TCoordSt (H o).cartH)
    (h1 : BiaddSt Y p) (h2 : CrossSt Y p) : ValEqPSt Y p H Ls n :=
  valuation_eq_pair_of_pairing Y p H Ls n hP hT h1 h2 (pair_holds Y p)

end Formalism.L2.FormalSeriesBounds
end
end

