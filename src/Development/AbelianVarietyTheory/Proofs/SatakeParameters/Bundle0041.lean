import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0006
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0025
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0026
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightRegularOfExt

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsobaricDiscreteSelfDualMultOneOfIsobaricSumMult
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.SpehRigid

def seg {C : Type} (p : C × ℕ) : Multiset (C × ℤ) :=
  (Multiset.range p.2).map fun a : ℕ => (p.1, (p.2 : ℤ) - 1 - 2 * (a : ℤ))

theorem seg_nodup {C : Type} (p : C × ℕ) : (seg p).Nodup := by
  refine (Multiset.nodup_range _).map ?_
  intro a b h
  have := congrArg Prod.snd h
  simp only at this
  omega

theorem mem_seg {C : Type} (p : C × ℕ) (c : C) (e : ℤ) :
    (c, e) ∈ seg p ↔ p.1 = c ∧ ∃ a : ℕ, a < p.2 ∧ (p.2 : ℤ) - 1 - 2 * (a : ℤ) = e := by
  simp only [seg, Multiset.mem_map, Multiset.mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨a, ha, h1, h2⟩
    exact ⟨h1, a, ha, h2⟩
  · rintro ⟨h1, a, ha, h2⟩
    exact ⟨a, ha, h1, h2⟩

theorem count_seg {C : Type} [DecidableEq C] (p : C × ℕ) (c : C) (d : ℕ) (hd : 1 ≤ d) :
    (seg p).count (c, (d : ℤ) - 1) = (seg p).count (c, (d : ℤ) + 1) + if (c, d) = p then 1 else 0 := by
  rw [Multiset.count_eq_of_nodup (seg_nodup p), Multiset.count_eq_of_nodup (seg_nodup p)]
  obtain ⟨c', d'⟩ := p
  have e1 : (c, (d : ℤ) - 1) ∈ seg (c', d') ↔ c' = c ∧ d ≤ d' ∧ (d' + d) % 2 = 0 := by
    rw [mem_seg]
    refine and_congr_right fun _ => ⟨?_, fun h => ⟨(d' - d) / 2, ?_, ?_⟩⟩
    · rintro ⟨a, h1, h2⟩
      simp only at h1 h2
      omega
    · simp only; omega
    · simp only; omega
  have e2 : (c, (d : ℤ) + 1) ∈ seg (c', d') ↔ c' = c ∧ d + 2 ≤ d' ∧ (d' + d) % 2 = 0 := by
    rw [mem_seg]
    refine and_congr_right fun _ => ⟨?_, fun h => ⟨(d' - d - 2) / 2, ?_, ?_⟩⟩
    · rintro ⟨a, h1, h2⟩
      simp only at h1 h2
      omega
    · simp only; omega
    · simp only; omega
  simp only [e1, e2, Prod.mk.injEq]
  by_cases hc : c' = c
  · subst hc
    simp only [true_and]
    split_ifs <;> omega
  · simp [hc, Ne.symm hc]

theorem count_bind_seg {C : Type} [DecidableEq C] (P : Multiset (C × ℕ)) (c : C) (d : ℕ) (hd : 1 ≤ d) :
    (P.bind seg).count (c, (d : ℤ) - 1) = (P.bind seg).count (c, (d : ℤ) + 1) + P.count (c, d) := by
  induction P using Multiset.induction_on with
  | empty => simp
  | cons p P ih =>
    rw [Multiset.cons_bind, Multiset.count_add, Multiset.count_add, ih, count_seg p c d hd, Multiset.count_cons]
    omega

theorem eq_of_bind_seg {C : Type} (P P' : Multiset (C × ℕ)) (h : ∀ p ∈ P, 1 ≤ p.2) (h' : ∀ p ∈ P', 1 ≤ p.2)
    (e : P.bind seg = P'.bind seg) : P = P' := by
  classical
  ext ⟨c, d⟩
  by_cases hd : 1 ≤ d
  · have h1 := count_bind_seg P c d hd
    have h2 := count_bind_seg P' c d hd
    rw [e] at h1
    omega
  · rw [Multiset.count_eq_zero_of_notMem fun hm => hd (h _ hm),
      Multiset.count_eq_zero_of_notMem fun hm => hd (h' _ hm)]

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

def flat (p : Formalism.BasicNotions.Part A.CG) : List ((Σ a : ℕ, A.CG a) × ℝ) :=
  (List.range p.d).map fun k : ℕ => (⟨p.a, p.π⟩, ((p.d : ℝ) - 1) / 2 - (k : ℝ))

theorem twSum_append (L L' : List ((Σ a : ℕ, A.CG a) × ℝ)) (w : PlE H) :
    GlobalTheory.RowTie.twSum N A (L ++ L') w = A.lpSum (GlobalTheory.RowTie.twSum N A L w) (GlobalTheory.RowTie.twSum N A L' w) := by
  unfold GlobalTheory.RowTie.twSum
  induction L with
  | nil => rw [List.nil_append, List.foldr_nil, A.lpSum_comm, A.lpSum_zero]
  | cons p L ih => rw [List.cons_append, List.foldr_cons, List.foldr_cons, ih, A.lpSum_assoc]

theorem spehLoc_eq (p : Formalism.BasicNotions.Part A.CG) (w : PlE H) :
    spehLoc N A p w = GlobalTheory.RowTie.twSum N A (flat N A p) w := by
  unfold spehLoc GlobalTheory.RowTie.twSum flat
  have hl : (List.range p.d >>= fun a : ℕ => (pure (a : ℝ) : List ℝ)) = (List.range p.d).map (fun a : ℕ => (a : ℝ)) := by
    simp [List.map_eq_flatMap]
  rw [hl, List.foldr_map, List.foldr_map]

theorem isoLoc_eq (P : List (Formalism.BasicNotions.Part A.CG)) (w : PlE H) :
    isoLoc N A P w = GlobalTheory.RowTie.twSum N A (P.flatMap (flat N A)) w := by
  induction P with
  | nil => rfl
  | cons p P ih => rw [List.flatMap_cons, twSum_append, ← ih, ← spehLoc_eq]; rfl

def toPair (p : Formalism.BasicNotions.Part A.CG) : (Σ a : ℕ, A.CG a) × ℕ := (⟨p.a, p.π⟩, p.d)

theorem toPair_injective : Function.Injective (toPair N A) :=
  Function.LeftInverse.injective (g := fun q => ⟨q.1.1, q.1.2, q.2⟩) fun _ => rfl

theorem coe_flatMap (P : List (Formalism.BasicNotions.Part A.CG)) :
    Multiset.ofList (P.flatMap (flat N A)) =
      ((Multiset.ofList (P.map (toPair N A))).bind seg).map fun q => (q.1, (q.2 : ℝ) / 2) := by
  induction P with
  | nil => simp
  | cons p P ih =>
    rw [List.flatMap_cons, ← Multiset.coe_add, ih, List.map_cons, ← Multiset.cons_coe, Multiset.cons_bind,
      Multiset.map_add]
    congr 1
    unfold seg flat toPair
    rw [Multiset.map_map, ← Multiset.map_coe]
    refine Multiset.map_congr rfl fun a _ => ?_
    simp only [Function.comp_apply]
    congr 1
    push_cast
    ring

theorem isobaricDiscreteSelfDualMultOne_of_isobaricSumMultOne : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N),
    GlobalTheory.RowTie.IsobaricRigid N A → GlobalTheory.RowCopy.IsobaricDiscreteSelfDualStrongMultiplicityOne N A := by
  intro R H what₂ N A hR Pa Pa' h h' he
  have hpos : ∀ P : List (Formalism.BasicNotions.Part A.CG), (∀ p ∈ P, 1 ≤ p.a ∧ 1 ≤ p.d ∧ A.csd p.π) →
      ∀ q ∈ P.flatMap (flat N A), 1 ≤ q.1.1 := by
    intro P hP q hq
    obtain ⟨p, hp, hq⟩ := List.mem_flatMap.1 hq
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hq
    exact (hP p hp).1
  have hd : ∀ P : List (Formalism.BasicNotions.Part A.CG), (∀ p ∈ P, 1 ≤ p.a ∧ 1 ≤ p.d ∧ A.csd p.π) →
      ∀ q ∈ Multiset.ofList (P.map (toPair N A)), 1 ≤ q.2 := by
    intro P hP q hq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 (Multiset.mem_coe.1 hq)
    exact (hP p hp).2.1
  have h1 := hR _ _ (hpos Pa h) (hpos Pa' h') (by simpa only [isoLoc_eq] using he)
  have h2 := Multiset.coe_eq_coe.2 h1
  rw [coe_flatMap, coe_flatMap] at h2
  have hinj : Function.Injective fun q : (Σ a : ℕ, A.CG a) × ℤ => (q.1, (q.2 : ℝ) / 2) := by
    intro q q' e
    have e1 := congrArg Prod.fst e
    have e2 := congrArg Prod.snd e
    simp only at e1 e2
    refine Prod.ext e1 ?_
    have : (q.2 : ℝ) = q'.2 := by linarith
    exact_mod_cast this
  have h3 := eq_of_bind_seg _ _ (hd Pa h) (hd Pa' h') (Multiset.map_injective hinj h2)
  rw [← Multiset.map_coe, ← Multiset.map_coe] at h3
  exact Multiset.coe_eq_coe.1 (Multiset.map_injective (toPair_injective N A) h3)

end GlobalTheory.SpehRigid
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalParameterLawsOfWeilDeligneIdentification
section
namespace GlobalTheory.RowLaws

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.WeilDeligne GlobalTheory.ThetaExh GlobalTheory.RowTie

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}

theorem tie_unit (T : WDTie N A) (w : PlE H) :
    (T.e w (A.lpUnr w {1})).unr ∧ (T.e w (A.lpUnr w {1})).lpDim = 1 ∧
      (T.e w (A.lpUnr w {1})).frobEig = {1} := by
  obtain ⟨h1, h2, h3⟩ := A.lpUnr_spec w {1} (by simp)
  refine ⟨(T.unr w _).1 h1, ?_, ?_⟩
  · rw [T.dim, h3]; rfl
  · rw [← T.frobEig w _ h1, h2]

theorem paramLaws_of_tie (T : WDTie N A) : ParamLaws N A := by
  intro w
  refine ⟨fun a b χ h => (T.e w).injective ?_, fun χ h => (T.e w).injective ?_,
    fun a χ s h => (T.e w).injective ?_, fun a b χ h hab => ?_, fun a b c h => (T.e w).injective ?_⟩
  · rw [T.char _ _ _ h, T.sum, T.sum, T.char _ _ _ h, T.char _ _ _ h]
    exact (GlobalTheory.T.lp_char_compatibilities _ _ _ _ _ _ _ _ 0).1
  · rw [T.char _ _ _ h, T.zero]
    exact (GlobalTheory.T.lp_char_compatibilities _ _ _ _ _ (WD.lpZero _) (WD.lpZero _) _ 0).2.2.2.2.1
  · rw [T.char _ _ _ h, T.tw, T.tw, T.char _ _ _ h]
    exact (GlobalTheory.T.lp_char_compatibilities _ _ _ _ _ _ (WD.lpZero _) _ s).2.1
  · apply (T.e w).injective
    have hχ : (T.e w χ).lpDim = 1 := by rw [T.dim, h]
    have := congrArg (T.e w) hab
    rw [T.char _ _ _ h, T.char _ _ _ h] at this
    exact GlobalTheory.T.weilDeligneParameter_tensor_oneDim_injective _ _ _ _ _ _ _ _ hχ this
  · have := congrArg (T.e w) h
    rw [T.sum, T.sum] at this
    exact GlobalTheory.T.directSum_cancel_right _ _ _ _ _ _ _ _ this

theorem cancel_of_tie (T : WDTie N A) : Cancel N A := fun w a b c h => (paramLaws_of_tie T w).2.2.2.2 a b c h

theorem charLaws_of_tie (T : WDTie N A) : CharLaws N A := by
  intro w a b χ χ' s h1 h2
  have h3 : A.lpDim (A.lpTw χ s) = 1 := by rw [A.lpDim_tw, h1]
  have h4 : A.lpDim (A.lpChar χ χ') = 1 := by rw [A.lpDim_char _ _ h2, h1]
  have h5 : A.lpDim (A.lpUnr w {1}) = 1 := (A.lpUnr_spec w {1} (by simp)).2.2
  refine ⟨(T.e w).injective ?_, (T.e w).injective ?_, (T.e w).injective ?_, (T.e w).injective ?_,
    (T.e w).injective ?_⟩
  · rw [T.char _ _ _ h1, T.sum, T.sum, T.char _ _ _ h1, T.char _ _ _ h1]
    exact (GlobalTheory.T.lp_char_compatibilities _ _ _ _ _ _ _ _ 0).1
  · rw [T.char _ _ _ h1, T.tw, T.tw, T.char _ _ _ h1]
    exact (GlobalTheory.T.lp_char_compatibilities _ _ _ _ _ _ (WD.lpZero _) _ s).2.1
  · rw [T.char _ _ _ h3, T.tw, T.tw, T.char _ _ _ h1]
    exact (GlobalTheory.T.lp_char_compatibilities _ _ _ _ _ _ (WD.lpZero _) _ s).2.2.1
  · rw [T.char _ _ _ h2, T.char _ _ _ h1, T.char _ _ _ h4, T.char _ _ _ h2]
    exact (GlobalTheory.T.lp_char_compatibilities _ _ _ _ _ _ _ _ 0).2.2.2.1
  · rw [T.char _ _ _ h5]
    obtain ⟨u1, u2, u3⟩ := tie_unit T w
    exact (GlobalTheory.T.lp_char_compatibilities _ _ _ _ _ (T.e w a) (WD.lpZero _) _ 0).2.2.2.2.2 u1 u2 u3

end GlobalTheory.RowLaws

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain in

theorem GlobalTheory.RowLaws.main : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N),
    GlobalTheory.RowTie.WDTie N A → GlobalTheory.ThetaExh.ParamLaws N A ∧ GlobalTheory.RowTie.CharLaws N A ∧ GlobalTheory.RowTie.Cancel N A :=
  fun _ _ _ _ _ T => ⟨GlobalTheory.RowLaws.paramLaws_of_tie T, GlobalTheory.RowLaws.charLaws_of_tie T, GlobalTheory.RowLaws.cancel_of_tie T⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PowFinrankEqZeroOfIsNilpotent
section
noncomputable section

open Module Polynomial
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain
open GlobalTheory.WeilDeligne

namespace GlobalTheory.LocalInv

theorem pow_finrank_eq_zero_of_isNilpotent {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] {N : End ℂ V} (hN : IsNilpotent N) : N ^ finrank ℂ V = 0 := by
  obtain ⟨m, hm⟩ := hN
  have h := Module.End.ker_pow_le_ker_pow_finrank N m
  rw [hm, LinearMap.ker_zero] at h
  exact LinearMap.ker_eq_top.mp (top_le_iff.mp h)

theorem norm_le_of_isPurePair {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {q : ℝ} (hq : 1 < q) {f N : End ℂ V} (hN : IsNilpotent N) (hp : IsPurePair q f N) {α : ℂ}
    (hα : f.HasEigenvalue α) :
    q ^ (-(((finrank ℂ V : ℝ) - 1) / 2)) ≤ ‖α‖ ∧ ‖α‖ ≤ q ^ (((finrank ℂ V : ℝ) - 1) / 2) := by
  obtain ⟨v, hv⟩ := hα.exists_hasEigenvector
  have hmem : ∀ r : ℝ, ‖α‖ = r → v ∈ absSpace f r := fun r hr =>
    Submodule.mem_iSup_of_mem α (Submodule.mem_iSup_of_mem hr hv.1)

  obtain ⟨i, hi⟩ : ∃ i : ℤ, ‖α‖ = q ^ ((i : ℝ) / 2) := by
    by_contra hc
    push_neg at hc
    have hle : (⨆ i : ℤ, absSpace f (q ^ ((i : ℝ) / 2))) ≤ ⨆ (β : ℂ) (_ : β ≠ α), f.eigenspace β := by
      refine iSup_le fun i => iSup₂_le fun β hβ => le_iSup₂_of_le β (fun h => hc i (h ▸ hβ)) le_rfl
    rw [hp.1] at hle
    have hd := (f.eigenspaces_iSupIndep α)
    have hv0 : v ∈ (⨆ (β : ℂ) (_ : β ≠ α), f.eigenspace β) := hle Submodule.mem_top
    exact hv.2 ((Submodule.disjoint_def.mp hd) v hv.1 hv0)

  set j := i.natAbs with hj
  have hNj : N ^ j ≠ 0 := by
    intro h0
    rcases le_or_gt 0 i with h | h
    · have hij : (i : ℝ) = (j : ℝ) := by
        rw [hj, Nat.cast_natAbs, Int.cast_abs, abs_of_nonneg (by exact_mod_cast h)]
      obtain ⟨u, -, hu⟩ := (hp.2 j).surjOn (hmem _ (by rw [hi, hij]))
      rw [h0, LinearMap.zero_apply] at hu
      exact hv.2 hu.symm
    · have hij : (i : ℝ) / 2 = -(j : ℝ) / 2 := by
        rw [hj, Nat.cast_natAbs, Int.cast_abs, abs_of_neg (by exact_mod_cast h)]; ring
      have h1 := (hp.2 j).injOn (hmem _ (by rw [hi, hij])) (Submodule.zero_mem _)
        (by rw [h0]; simp)
      exact hv.2 h1
  have hjd : j + 1 ≤ finrank ℂ V := by
    by_contra hc
    exact hNj (pow_eq_zero_of_le (by omega) (pow_finrank_eq_zero_of_isNilpotent hN))
  have hjr : ((j : ℕ) : ℝ) ≤ (finrank ℂ V : ℝ) - 1 := by
    have : ((j + 1 : ℕ) : ℝ) ≤ (finrank ℂ V : ℝ) := by exact_mod_cast hjd
    push_cast at this; linarith
  have habs : |(i : ℝ)| = (j : ℝ) := by rw [hj, Nat.cast_natAbs, Int.cast_abs]
  have h1 : (i : ℝ) ≤ (finrank ℂ V : ℝ) - 1 := (le_abs_self _).trans (habs ▸ hjr)
  have h2 : -((finrank ℂ V : ℝ) - 1) ≤ (i : ℝ) := by
    have := neg_abs_le (i : ℝ); rw [habs] at this; linarith
  rw [hi]
  exact ⟨Real.rpow_le_rpow_of_exponent_le hq.le (by linarith),
    Real.rpow_le_rpow_of_exponent_le hq.le (by linarith)⟩

theorem temperedSizes_of_tie : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂)
    (A : NAut N) (T : GlobalTheory.RowTie.WDTie N A), GlobalTheory.LocalInv.TemperedSizes N A T.eig := by
  intro R H what₂ N A T w σ hσ a ha α hα
  have hm := mem_Weil_of_isFrob (N.plOm.2 w) hσ
  rw [← T.dim w a]
  rw [T.tempered w a] at ha
  change α ∈ ((T.e w a).inePol σ).roots at hα
  generalize T.e w a = x at ha hα ⊢
  induction x using WD.ind with
  | hP n b =>
    rw [WD.inePol_of_mem _ hm, WD.charPol_mk] at hα
    rw [WD.tempered_mk] at ha
    rw [WD.lpDim_mk]
    have hroot : IsRoot (b.ρ ⟨σ, hm⟩).charpoly α :=
      (mem_roots (LinearMap.charpoly_monic _).ne_zero).mp hα
    have hev : Module.End.HasEigenvalue (b.ρ ⟨σ, hm⟩) α :=
      (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mpr hroot
    have hq : (1 : ℝ) < ((normV w : ℕ) : ℝ) := by exact_mod_cast one_lt_normV w
    exact norm_le_of_isPurePair hq b.nilpotent (ha ⟨σ, hm⟩ (deg_eq_one_iff.mpr hσ)) hev

end GlobalTheory.LocalInv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RootsCharpolySmulMatrix
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.WeilDeligne
open scoped TensorProduct

namespace GlobalTheory.RowTie.EigTwist

theorem roots_charpoly_smul_matrix {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (u : ℂ) :
    (u • M).charpoly.roots = M.charpoly.roots.map (· * u) := by
  have hM := (IsAlgClosed.splits M.charpoly).eq_prod_roots_of_monic (Matrix.charpoly_monic M)
  have hc : Multiset.card M.charpoly.roots = Fintype.card ι := by
    rw [← (IsAlgClosed.splits M.charpoly).natDegree_eq_card_roots, Matrix.charpoly_natDegree_eq_dim]
  suffices (u • M).charpoly = ((M.charpoly.roots.map (· * u)).map fun α => X - C α).prod by
    rw [this, roots_multiset_prod_X_sub_C]
  rcases eq_or_ne u 0 with rfl | hu
  · simp [hc]
  · refine Polynomial.funext fun x => ?_
    have h1 := congrArg (eval (x / u)) hM
    rw [Matrix.eval_charpoly, eval_multiset_prod, Multiset.map_map] at h1
    have e : Matrix.scalar ι x - u • M = u • (Matrix.scalar ι (x / u) - M) := by
      ext a b
      by_cases hab : a = b
      · subst hab
        simp
        field_simp
      · simp [Matrix.diagonal_apply_ne _ hab]
    rw [Matrix.eval_charpoly, e, Matrix.det_smul, h1, eval_multiset_prod, Multiset.map_map,
      Multiset.map_map, ← hc, ← Multiset.prod_replicate, ← Multiset.map_const, ← Multiset.prod_map_mul]
    refine congrArg _ (Multiset.map_congr rfl fun α _ => ?_)
    simp
    field_simp

theorem roots_charpoly_smul {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) (u : ℂ) : (u • f).charpoly.roots = f.charpoly.roots.map (· * u) := by
  rw [← LinearMap.charpoly_toMatrix (u • f) (Module.finBasis ℂ V),
    ← LinearMap.charpoly_toMatrix f (Module.finBasis ℂ V), map_smul, roots_charpoly_smul_matrix]

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {B : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver B w}

theorem eig_lpTw (x : WD h) {φ : Weil h} (hφ : deg φ = 1) (s : ℝ) :
    (x.lpTw s).eig φ = (x.eig φ).map (· * ((normV w : ℕ) : ℂ) ^ ((s : ℝ) : ℂ)) := by
  induction x using WD.ind with
  | hP n a =>
    rw [WD.lpTw_mk, WD.eig_mk, WD.eig_mk, WDRep.tw_ρ, hφ, zpow_one, roots_charpoly_smul]

theorem eig_lpChar (x y : WD h) (φ : Weil h) (hy : y.lpDim = 1) (c : ℂ) (hc : y.eig φ = {c}) :
    (x.lpChar y).eig φ = (x.eig φ).map (· * c) := by
  induction x using WD.ind with
  | hP n a =>
  induction y using WD.ind with
  | hP m b =>
    rw [WD.lpDim_mk, Module.finrank_fin_fun] at hy
    subst hy
    rw [WD.eig_mk] at hc
    have hb : b.ρ φ = c • 1 := by
      have hp : (b.ρ φ).charpoly = X - C c := by
        rw [(IsAlgClosed.splits _).eq_prod_roots_of_monic (LinearMap.charpoly_monic _), hc]
        simp
      have h3 := LinearMap.aeval_self_charpoly (b.ρ φ)
      rw [hp, map_sub, aeval_X, aeval_C, sub_eq_zero, Algebra.algebraMap_eq_smul_one] at h3
      exact h3
    rw [WD.lpChar_mk, WD.eig_mk, WD.eig_mk, WDRep.tensor_ρ, hb]
    let e : (Fin n → ℂ) ⊗[ℂ] (Fin 1 → ℂ) ≃ₗ[ℂ] (Fin n → ℂ) :=
      (TensorProduct.congr (LinearEquiv.refl ℂ _) (LinearEquiv.funUnique (Fin 1) ℂ ℂ)).trans
        (TensorProduct.rid ℂ _)
    have he : e.conj (TensorProduct.map (a.ρ φ) (c • 1)) = c • a.ρ φ := by
      refine LinearMap.ext fun v => ?_
      obtain ⟨t, rfl⟩ := e.surjective v
      rw [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
      erw [LinearEquiv.symm_apply_apply]
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul x y => simp [e, smul_smul, mul_comm]
      | add x y hx hy => simp only [map_add, hx, hy]
    rw [← LinearEquiv.charpoly_conj e, he, roots_charpoly_smul]

end GlobalTheory.RowTie.EigTwist

open GlobalTheory.RowTie.EigTwist in

theorem GlobalTheory.RowTie.eigLaws_of_wdTie : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂)
    (A : NAut N) (T : GlobalTheory.RowTie.WDTie N A), GlobalTheory.LocalInv.EigLaws N A T.eig := by
  intro R H what₂ N A T w σ hσ
  have hW : σ ∈ Weil (N.plOm.2 w) := mem_Weil_of_isFrob _ hσ
  let φ : Weil (N.plOm.2 w) := ⟨σ, hW⟩
  have hφ : deg φ = 1 := deg_eq_one_iff.mpr hσ
  have key : ∀ a, T.eig w a σ = (T.e w a).eig φ := fun a => by
    rw [WDTie.eig, WD.inePol_of_mem _ hW]
    rfl
  refine ⟨fun a => ?_, fun a s => ?_, fun a χ c hχ hc => ?_⟩
  · rw [key, WD.card_eig, T.dim]
  · rw [key, key, T.tw, eig_lpTw _ hφ]
  · rw [key] at hc
    rw [key, key, T.char _ _ _ hχ, eig_lpChar _ _ _ (by rw [T.dim, hχ]) c hc]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitComponentsDeterminedByPointOfBaseChange
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.RowTie

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

theorem placesOver_finite_of_ne_zero (E : Type) [Field E] [NumberField E] (p : ℕ) (hp : p ≠ 0) :
    (placesOver E p).Finite := by
  have h0 : Ideal.span {((p : ℕ) : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp
  refine (Ideal.finite_factors h0).subset fun v hv => ?_
  show v.asIdeal ∣ _
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hv

theorem isoLoc_perm {Pa Pa' : List (Part A.CG)} (h : Pa.Perm Pa') (w : PlE H) :
    isoLoc N A Pa w = isoLoc N A Pa' w := by
  induction h with
  | nil => rfl
  | cons p _ ih =>
    simp only [isoLoc, List.foldr_cons] at ih ⊢
    rw [ih]
  | swap p q l =>
    simp only [isoLoc, List.foldr_cons]
    rw [← A.lpSum_assoc (spehLoc N A q w), A.lpSum_comm (spehLoc N A q w) (spehLoc N A p w), A.lpSum_assoc]
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem locV_eq_of_pt (i : N.Loc) {P P' : A.AV i} {x : N.X i} (hx : A.ptV i P = some x)
    (hx' : A.ptV i P' = some x) {w : PlE H} (hso : SplitOut N i w) (hg : ∀ k, w ∉ placesOver H.E (H.g k))
    (hd : w ∉ placesOver H.E (if N.l i = H.pde then H.pde' else H.pde)) :
    A.locV i P w = A.locV i P' w := by
  set c : ℝ := (1 - (R.nV : ℝ)) / 2
  have u : A.unr (A.lpTw (A.locV i P w) c) :=
    (A.unr_tw _ _).2 (A.locV_unr i P w hso.1 hso.2.2.2 hg hd)
  have u' : A.unr (A.lpTw (A.locV i P' w) c) :=
    (A.unr_tw _ _).2 (A.locV_unr i P' w hso.1 hso.2.2.2 hg hd)
  have h1 := congrArg Polynomial.roots ((A.pt_loc i P x hx w hso).symm.trans (A.pt_loc i P' x hx' w hso))
  rw [Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at h1
  have e : A.lpTw (A.locV i P w) c = A.lpTw (A.locV i P' w) c := by
    rw [A.unr_eq_lpUnr _ u, A.unr_eq_lpUnr _ u', h1]
  have back : ∀ a : A.LP w, A.lpTw (A.lpTw a c) (-c) = a := fun a => by
    rw [A.lpTw_add, add_neg_cancel, A.lpTw_zero]
  rw [← back (A.locV i P w), e, back]

theorem locOfPt_of_splitBC : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N)
    (i : N.Loc), GlobalTheory.RowTie.BCEx N A i → GlobalTheory.RowTie.SplitBC N A i → GlobalTheory.ThetaExh.LocOfPt N A i := by
  intro R H what₂ N A i hBC hS P P' x hx hx' w hw
  obtain ⟨Pa, hPa⟩ := hBC P
  obtain ⟨Pa', hPa'⟩ := hBC P'
  have hd0 : (if N.l i = H.pde then H.pde' else H.pde) ≠ 0 := by
    split_ifs
    exacts [H.pde'_prime.ne_zero, H.pde_prime.ne_zero]
  have hfin : (placesOver H.E (N.l i) ∪ (N.S i : Set (PlE H)) ∪ (N.Q i : Set (PlE H)) ∪
      placesOver H.E (H.g 0) ∪ placesOver H.E (H.g 1) ∪
      placesOver H.E (if N.l i = H.pde then H.pde' else H.pde)).Finite := by
    refine ((((( placesOver_finite_of_ne_zero _ _ (N.lPrime i).out.ne_zero).union (N.S i).finite_toSet).union
      (N.Q i).finite_toSet).union (placesOver_finite_of_ne_zero _ _ (H.g_prime 0).ne_zero)).union
      (placesOver_finite_of_ne_zero _ _ (H.g_prime 1).ne_zero)).union (placesOver_finite_of_ne_zero _ _ hd0)
  have hev : ∀ᶠ v in Filter.cofinite, IsSplitPl H v → A.locV i P v = A.locV i P' v := by
    rw [Filter.eventually_cofinite]
    refine hfin.subset fun v hv => ?_
    by_contra hn
    simp only [Set.mem_union, Finset.mem_coe, not_or] at hn
    obtain ⟨⟨⟨⟨⟨hl, hSv⟩, hQv⟩, hg0⟩, hg1⟩, hdv⟩ := hn
    refine hv fun hsp => locV_eq_of_pt N A i hx hx' ⟨hsp, hl, hSv, hQv⟩ ?_ hdv
    intro k
    fin_cases k
    exacts [hg0, hg1]
  have hperm := hS P P' hev Pa Pa' hPa hPa'
  rw [← hPa.2.2.2.1 w hw, ← hPa'.2.2.2.1 w hw]
  exact isoLoc_perm N A hperm w

end GlobalTheory.RowTie
end
end

