import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CellDef
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle0001
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle0002
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CellSchur
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CellGeo
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle0004
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.TraceConjMulEqHilbertSchmidt
import Formalism.SharpRestriction.CuspSpanNormBounds.ThresholdCubicInequalitySignPattern

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CellFin
section
noncomputable section
namespace Formalism.MainNotions.BridgeLemma
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.LatticeGluingRadicals NumberField Module

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem tie_trace {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : CMData F E) (x : E) : algebraMap F E (Algebra.trace F E x) = x + star x := by
  classical

  have hfix : ∀ c : F, star (algebraMap F E c) = algebraMap F E c :=
    fun c => (hc.fixed _).2 ⟨c, rfl⟩
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hc.deg2]; norm_num)
  let s : E ≃ₐ[F] E :=
    { toFun := star
      invFun := star
      left_inv := star_star
      right_inv := star_star
      map_mul' := fun a b => by rw [star_mul, mul_comm]
      map_add' := star_add
      commutes' := hfix }
  have hs1 : s ≠ 1 := by
    intro h
    have hbot : (⊥ : Subalgebra F E) = ⊤ := by
      refine eq_top_iff.2 fun a _ => ?_
      have ha : star a = a := DFunLike.congr_fun h a
      obtain ⟨c, hc'⟩ := RingHom.mem_range.1 ((hc.fixed a).1 ha)
      exact Algebra.mem_bot.2 ⟨c, hc'⟩
    have h1 : Module.finrank F E = 1 := Subalgebra.bot_eq_top_iff_finrank_eq_one.1 hbot
    rw [hc.deg2] at h1
    exact absurd h1 (by norm_num)
  have hle : Fintype.card (E ≃ₐ[F] E) ≤ Module.finrank F E := by
    first
      | exact AlgEquiv.card_le
      | exact (Fintype.card_congr (algEquivEquivAlgHom F E)).le.trans AlgHom.card_le
  have hpair : ({1, s} : Finset (E ≃ₐ[F] E)).card = 2 := Finset.card_pair (Ne.symm hs1)
  have hcard : Fintype.card (E ≃ₐ[F] E) = 2 := by
    have hge : ({1, s} : Finset (E ≃ₐ[F] E)).card ≤ Fintype.card (E ≃ₐ[F] E) :=
      Finset.card_le_univ _
    rw [hc.deg2] at hle
    omega
  haveI : IsGalois F E := by
    first
      | exact IsGalois.of_card_aut_eq_finrank F E (by rw [Nat.card_eq_fintype_card, hcard, hc.deg2])
      | exact IsGalois.of_card_aut_eq_finrank F E (by rw [hcard, hc.deg2])
  have huniv : (Finset.univ : Finset (E ≃ₐ[F] E)) = {1, s} := by
    symm
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_univ, hcard, hpair]
  first
    | rw [trace_eq_sum_automorphisms]
    | rw [Algebra.trace_eq_sum_automorphisms]
  rw [huniv, Finset.sum_pair (Ne.symm hs1)]
  try rfl

theorem tie_aniso (D : D7) (T : ℕ) (hT : 0 < T) (F : LFlag (hS D) D.R.rS (T : D.host.E)) (y : (hS D).V)
    (h1 : ∀ a, (hS D).hT (F.fl.fvec a) y = 0) (h2 : (hS D).hT y y = 0) : y ∈ F.fl.X := by
  by_contra hy
  obtain ⟨τ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
  have hmem : y ∈ orth (hS D) (Xplus F) := by
    rw [p_mem_orth]
    intro x hx
    have hle : Xplus F ≤ LinearMap.ker ((hS D).hT.flip y) := by
      refine sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
      · rintro _ ⟨a, rfl⟩
        have := h1 a.castSucc
        simpa [FlagG.fvec] using this
      · rintro _ rfl
        have := h1 (Fin.last _)
        simpa [FlagG.fvec] using this
    exact hle hx
  have hp := p_posX D T hT F τ y hmem hy
  unfold nrm at hp
  rw [h2, map_zero] at hp
  simp at hp

end Formalism.MainNotions.BridgeLemma
end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.ClauseAOfIdentityFlag
section
noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.LatticeGluingRadicals NumberField Module

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

theorem tie_Xa_mono (F : FlagG S r T) {a b : ℕ} (h : a ≤ b) : F.Xa a ≤ F.Xa b :=
  Submodule.span_mono (by rintro _ ⟨i, hi, rfl⟩; exact ⟨i, lt_of_lt_of_le hi h, rfl⟩)

theorem tie_e_mem_Xa (F : FlagG S r T) (a : Fin r) : F.e a ∈ F.Xa (a.val + 1) :=
  Submodule.subset_span ⟨a, Nat.lt_succ_self _, rfl⟩

theorem tie_Xa_eq (F : FlagG S r T) (F' : FlagG S r T') (h : ∀ a, F'.e a - F.e a ∈ F.Xa a.val) (j : ℕ) :
    F'.Xa j = F.Xa j := by
  have h1 : ∀ j, F'.Xa j ≤ F.Xa j := by
    intro j
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, ha, rfl⟩
    have h2 : F'.e a = (F'.e a - F.e a) + F.e a := by abel
    rw [h2]
    exact Submodule.add_mem _ (tie_Xa_mono F (le_of_lt ha) (h a)) (tie_Xa_mono F ha (tie_e_mem_Xa F a))
  refine le_antisymm (h1 j) ?_
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, ha, rfl⟩
    have h2 : F.e a = F'.e a - (F'.e a - F.e a) := by abel
    rw [h2]
    exact Submodule.sub_mem _ (tie_Xa_mono F' ha (tie_e_mem_Xa F' a))
      (tie_Xa_mono F' (le_of_lt ha) (ih a.val ha (h a)))

theorem tie_X_eq_Xa (F : FlagG S r T) : F.X = F.Xa r := by
  unfold FlagG.X FlagG.Xa
  congr 1
  ext x
  constructor
  · rintro ⟨a, rfl⟩; exact ⟨a, a.isLt, rfl⟩
  · rintro ⟨a, _, rfl⟩; exact ⟨a, rfl⟩

end Gen

section Rec

variable {D : D7}

theorem tie_inS_sameFlag (X : TermTie D) {u u' : D.what₂.Word} (t : D.s.Term u u') (h : D.s.inS t) :
    FrobeniusProjectedBounds.SameFlag (X.fl t) (X.fl' t) := by
  obtain ⟨h1, h2⟩ := (X.inS_iff t).1 h
  have hXa := tie_Xa_eq (X.fl t).fl (X.fl' t).fl h1
  refine ⟨hXa, ?_⟩
  have hX : (X.fl' t).fl.X = (X.fl t).fl.X := by rw [tie_X_eq_Xa, tie_X_eq_Xa, hXa]
  show (X.fl' t).fl.X ⊔ Submodule.span D.host.E {(X.fl' t).fl.z} =
    (X.fl t).fl.X ⊔ Submodule.span D.host.E {(X.fl t).fl.z}
  rw [hX]
  apply le_antisymm
  · refine sup_le le_sup_left (Submodule.span_le.2 ?_)
    rintro _ rfl
    have : (X.fl' t).fl.z = ((X.fl' t).fl.z - (X.fl t).fl.z) + (X.fl t).fl.z := by abel
    rw [this]
    exact Submodule.add_mem _ (Submodule.mem_sup_left h2)
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
  · refine sup_le le_sup_left (Submodule.span_le.2 ?_)
    rintro _ rfl
    have : (X.fl t).fl.z = (X.fl' t).fl.z - ((X.fl' t).fl.z - (X.fl t).fl.z) := by abel
    rw [this]
    exact Submodule.sub_mem _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
      (Submodule.mem_sup_left h2)

theorem clause_a_of_identity_flag (X : TermTie D) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ) (hI : UnitaryVolumeMass.cIdFlag D X) :
    FrobeniusProjectedBounds.IntegralityFromMetric D large₂ X C' Cl Cg cb Cu cT CT C0 := by
  rintro ⟨_, a8, a9⟩ hH u
  have hirr := a8 hH u u
  have hid := a9 hH u
  have c4 : ∀ t : D.s.Term u u, FrobeniusProjectedBounds.SameFlag (X.fl t) (X.fl' t) → D.s.relevant t → D.s.isId t :=
    fun t h => hI u t h
  have c3 : ∀ t : D.s.Term u u, D.s.inS t → D.s.relevant t → D.s.isId t :=
    fun t h => c4 t (tie_inS_sameFlag X t h)
  refine ⟨?_, fun t => tie_isId_inS X t, c3, c4, hirr, fun t => term_in_S_vanishes X t, ?_, S0ge1_of_tie X u u⟩
  ·
    let ι : {t : D.s.Term u u // D.s.isId t} → {t : D.s.Term u u // D.s.inS t} :=
      fun t => ⟨t.1, tie_isId_inS X t.1 t.2⟩
    have hinj : Function.Injective ι := fun a b h => Subtype.ext (congrArg (fun z => z.1) h)
    refine (hinj.hasSum_iff (f := fun t : {t : D.s.Term u u // D.s.inS t} => D.s.aTerm u u t.1) ?_).1 hid
    intro t ht
    apply hirr
    intro hr
    exact ht ⟨⟨t.1, c3 t.1 t.2 hr⟩, rfl⟩
  · unfold FrobeniusProjectedBounds.Kpp KOf
    rw [tsum_subtype, tsum_subtype]
    congr 1
    funext t
    classical
    by_cases hr : D.s.relevant t
    · have hiff : t ∈ {t : D.s.Term u u | D.s.relevant t ∧ D.s.Gterm t = 0 ∧ ¬ FrobeniusProjectedBounds.SameFlag (X.fl t) (X.fl' t)} ↔
          t ∈ {t : D.s.Term u u | D.s.Gterm t = 0 ∧ ¬ D.s.isId t} := by
        constructor
        · rintro ⟨_, hG, hS⟩
          exact ⟨hG, fun h => hS (tie_inS_sameFlag X t (tie_isId_inS X t h))⟩
        · rintro ⟨hG, hn⟩
          exact ⟨hr, hG, fun h => hn (c4 t h hr)⟩
      by_cases hm : t ∈ {t : D.s.Term u u | D.s.Gterm t = 0 ∧ ¬ D.s.isId t}
      · rw [Set.indicator_of_mem hm, Set.indicator_of_mem (hiff.2 hm)]
      · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem (fun h => hm (hiff.1 h))]
    · have h0 := hirr t hr
      simp only [Set.indicator_apply, h0, ite_self]

end Rec

end Formalism.MainNotions.BridgeLemma

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.DecayHypothesisOfLargeConstants
section
noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ComplexOrder
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

theorem one_le_hilbert_schmidt_of_mem {n : ℕ} (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ) (hg : Formalism.REAL.inUJ ε g) (a : Fin n) :
    1 ≤ Formalism.REAL.hs g := by
  have h := congrFun (congrFun hg a) a
  unfold Formalism.REAL.Jm at h
  rw [Matrix.mul_apply] at h
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.diagonal_apply_eq] at h
  let s : Fin n → ℝ := fun j => if ε j then 1 else -1
  have h' : ((∑ j, s j * ‖g j a‖ ^ 2 : ℝ) : ℂ) = ((s a : ℝ) : ℂ) := by
    have e2 : ((s a : ℝ) : ℂ) = if ε a = true then 1 else -1 := by
      show (((if ε a then 1 else -1 : ℝ)) : ℂ) = _
      split_ifs <;> simp
    rw [e2, ← h]
    push_cast
    apply Finset.sum_congr rfl
    intro j _
    rw [← Complex.conj_mul' (g j a)]
    show (((if ε j then 1 else -1 : ℝ)) : ℂ) * _ = _
    split_ifs <;> simp
  have h'' : ∑ j, s j * ‖g j a‖ ^ 2 = s a := by exact_mod_cast h'
  have hs1 : s a * s a = 1 := by
    show (if ε a then (1 : ℝ) else -1) * (if ε a then (1 : ℝ) else -1) = 1
    split_ifs <;> norm_num
  have hle : ∀ j, s a * s j ≤ 1 := by
    intro j
    show (if ε a then (1 : ℝ) else -1) * (if ε j then (1 : ℝ) else -1) ≤ 1
    split_ifs <;> norm_num
  calc (1 : ℝ) = s a * ∑ j, s j * ‖g j a‖ ^ 2 := by rw [h'', hs1]
    _ = ∑ j, (s a * s j) * ‖g j a‖ ^ 2 := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by ring)
    _ ≤ ∑ j, ‖g j a‖ ^ 2 := Finset.sum_le_sum (fun j _ => by nlinarith [hle j, sq_nonneg ‖g j a‖])
    _ ≤ Formalism.REAL.hs g := by
        unfold Formalism.REAL.hs
        exact Finset.sum_le_sum (fun i _ =>
          Finset.single_le_sum (f := fun j => ‖g i j‖ ^ 2) (fun j _ => by positivity) (Finset.mem_univ a))

theorem compact_to_unitary_hermitian (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool)
    (P g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hP : IsCayleyU k r ε P)
    (hg : g ∈ Formalism.REAL.Kset ε) :
    P⁻¹ * g * P ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) ∩
      (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set _) := by
  have a1 : P.conjTranspose * P = 1 := Matrix.mem_unitaryGroup_iff'.1 hP.2
  have a2 : P * P.conjTranspose = 1 := Matrix.mem_unitaryGroup_iff.1 hP.2
  have iP : P⁻¹ = P.conjTranspose := Matrix.inv_eq_left_inv a1
  have gJ : g.conjTranspose * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := (Formalism.REAL.maximal_compact_facts _ ε).1 g hg
  rw [iP]
  constructor
  · show (P.conjTranspose * g * P).conjTranspose * Formalism.QuantumDeterminants.Hpk k r * (P.conjTranspose * g * P) = Formalism.QuantumDeterminants.Hpk k r
    rw [← hP.1.2]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc P.conjTranspose * (g.conjTranspose * P) * (P.conjTranspose * Formalism.REAL.Jm ε * P) * (P.conjTranspose * g * P)
        = P.conjTranspose * (g.conjTranspose * ((P * P.conjTranspose) * Formalism.REAL.Jm ε * (P * P.conjTranspose)) * g) * P := by
          simp only [Matrix.mul_assoc]
      _ = P.conjTranspose * Formalism.REAL.Jm ε * P := by
          rw [a2, Matrix.one_mul, Matrix.mul_one, gJ, Matrix.mul_assoc]
  · have hs : P.conjTranspose ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ := by
      rw [← Matrix.star_eq_conjTranspose]; exact Unitary.star_mem hP.2
    exact mul_mem (mul_mem hs hg.1) hP.2

end Formalism.MainNotions.BridgeLemma

end
end

