import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1667
import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1699
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0976
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0155
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1702
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1681
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0287
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1693
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1613
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1637
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1703
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1704
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Formalism.PairingDivisors.StatementH

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGridBlockCongruenceOffTypePrimeDescription
section
namespace IwahoriGroupOffset
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.CompanionTheory.StepGroupOff

theorem symm_mem_KO_iff {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (e : a ≃ b) (g : GL b k) :
    (reGL e).symm g ∈ KO k a ↔ g ∈ KO k b := by
  rw [mem_KO, mem_KO, ← map_inv, reGL_symm_val, reGL_symm_val]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun i j => by simpa using h1 (e.symm i) (e.symm j), fun i j => by simpa using h2 (e.symm i) (e.symm j)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun i j => h1 _ _, fun i j => h2 _ _⟩

theorem twoBlock_gridIndex {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) (w : Pl D.host.E)
    (j : ℕ) (x : Ix (Fin D.R.r) (Fin D.R.t) j) :
    Formalism.L2.DIV.blk2 D.R.r (ixFin G t w j x) = Sum.elim (fun _ => 0) (fun _ => 1) x := by
  rcases x with a | ⟨c, b⟩
  · simp [Formalism.L2.DIV.blk2, (ixFin_val G t w j).1 a]
  · simp [Formalism.L2.DIV.blk2, (ixFin_val G t w j).2 c b]

theorem mem_map_stepGroup_iff : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) (w : Pl D.host.E), w ∉ L.Pg → ∀ (j : ℕ) (g : GL (Fin ((locGrid G t w).rank (0, j))) (Kw w)), g ∈ (stepGroup L t w j).map (reGL (ixFin G t w j)).toMonoidHom ↔ g ∈ KO (Kw w) (Fin ((locGrid G t w).rank (0, j))) ∧ (w ∈ L.Q t → ∀ a b, Formalism.L2.DIV.blk2 D.R.r b < Formalism.L2.DIV.blk2 D.R.r a → valuation (Kw w) (g.1 a b) < 1) := by
  intro D T L sc G t w hP j g
  rw [Subgroup.mem_map_equiv, stepGroup, if_neg hP]
  by_cases hQ : w ∈ L.Q t
  · rw [if_pos hQ]
    refine (mem_parahoric (k := Kw w) (r := Fin D.R.r) (s := Fin j × Fin D.R.t) (δ := 1) (hδ := fun _ _ => rfl)).trans ?_
    rw [symm_mem_KO_iff]
    refine and_congr_right fun _ => ?_
    constructor
    · intro h _ a b hab
      obtain ⟨x, rfl⟩ := (ixFin G t w j).surjective a
      obtain ⟨y, rfl⟩ := (ixFin G t w j).surjective b
      rw [twoBlock_gridIndex, twoBlock_gridIndex] at hab
      rcases x with x | x <;> rcases y with y | y
      · simp at hab
      · simp at hab
      · simpa [reGL_symm_val, Matrix.toBlocks₂₁] using h x y
      · simp at hab
    · intro h i l
      have := h hQ (ixFin G t w j (.inr i)) (ixFin G t w j (.inl l)) (by simp [twoBlock_gridIndex])
      simpa [reGL_symm_val, Matrix.toBlocks₂₁] using this
  · rw [if_neg hQ, symm_mem_KO_iff]
    exact ⟨fun h => ⟨h, fun h' => absurd h' hQ⟩, fun h => h.1⟩

end GlobalTheory.CompanionTheory.StepGroupOff

end
end

end IwahoriGroupOffset
section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

theorem _root_.GlobalTheory.Adopt.thetaGridBlockCongruence_offTypePrime_description : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) (w : Pl D.host.E), w ∉ L.Pg → ∀ (j : ℕ) (g : GL (Fin ((locGrid G t w).rank (0, j))) (Kw w)), g ∈ (stepGroup L t w j).map (reGL (ixFin G t w j)).toMonoidHom ↔ g ∈ KO (Kw w) (Fin ((locGrid G t w).rank (0, j))) ∧ (w ∈ L.Q t → ∀ a b, Formalism.L2.DIV.blk2 D.R.r b < Formalism.L2.DIV.blk2 D.R.r a → valuation (Kw w) (g.1 a b) < 1) := by
  first | exact @IwahoriGroupOffset.GlobalTheory.CompanionTheory.StepGroupOff.mem_map_stepGroup_iff | exact IwahoriGroupOffset.GlobalTheory.CompanionTheory.StepGroupOff.mem_map_stepGroup_iff | (intros; apply IwahoriGroupOffset.GlobalTheory.CompanionTheory.StepGroupOff.mem_map_stepGroup_iff <;> assumption)

end
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGridBlockCongruenceTypePrimeDescription
section
namespace IteratedIwahori
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.CompanionTheory.IterJ

section Gen
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] in

theorem intM_submatrix_iff (e : a ≃ b) (M : Matrix a a k) :
    GlobalTheory.StepData.IntM (M.submatrix e.symm e.symm) ↔ GlobalTheory.StepData.IntM M :=
  ⟨fun h i j => by simpa using h (e i) (e j), fun h _ _ => h _ _⟩

theorem reGL_mem_KO_iff (e : a ≃ b) (g : GL a k) : reGL e g ∈ KO k b ↔ g ∈ KO k a := by
  rw [GlobalTheory.StepData.mem_KO, GlobalTheory.StepData.mem_KO, ← map_inv, reGL_val, reGL_val,
    intM_submatrix_iff, intM_submatrix_iff]

omit [Fintype a] [Fintype b] [DecidableEq b] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem symm_sub_one_apply [Fintype a] [Fintype b] [DecidableEq b] (e : a ≃ b) (h : GL b k) (x y : a) :
    (((reGL e).symm h).val - 1) x y = (h.val - 1) (e x) (e y) := by
  simp [reGL_symm_val, Matrix.one_apply]

end Gen

section Iter
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {r t : Type*} [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t]

theorem blk_le {j : ℕ} (x : Ix r t j) : Ix.blk x ≤ j := by
  rcases x with x | ⟨c, s⟩
  · simp [Ix.blk]
  · simpa [Ix.blk] using c.2

theorem blk_ixSucc_inl {j : ℕ} (x : Ix r t j) : Ix.blk (ixSucc r t j (Sum.inl x)) = Ix.blk x := by
  rcases x with x | ⟨c, s⟩ <;> simp [Ix.blk, ixSucc]

theorem blk_ixSucc_inr {j : ℕ} (s : t) : Ix.blk (ixSucc r t j (Sum.inr s)) = j + 1 := by
  simp [Ix.blk, ixSucc]

theorem mem_iter_J (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) (j : ℕ) (h : GL (Ix r t j) k) :
    h ∈ ((TypeDatum.principal k r).iter t μ hμ j).J ↔ h ∈ KO k (Ix r t j) ∧
      (∀ a b, Ix.blk b < Ix.blk a → valuation k (h.val a b) < 1) ∧
      ∀ a b : r, valuation k ((h.val - 1) (Sum.inl a) (Sum.inl b)) < 1 := by
  induction j with
  | zero =>
    rw [TypeDatum.iter_zero]
    have hK : (reGL (ixZero r t)).symm h ∈ KO k r ↔ h ∈ KO k (Ix r t 0) := by
      rw [← reGL_mem_KO_iff (ixZero r t), MulEquiv.apply_symm_apply]
    have mem : h ∈ ((TypeDatum.principal k r).reindex (ixZero r t)).J ↔
      (reGL (ixZero r t)).symm h ∈ KOne k r := Iff.rfl
    rw [mem, GlobalTheory.StepData.mem_KOne]
    constructor
    · intro hh
      refine ⟨hK.1 (GlobalTheory.StepData.KOne_le_KO (GlobalTheory.StepData.mem_KOne.2 hh)), fun a b hab => ?_, fun a b => ?_⟩
      · rcases a with a | ⟨c, _⟩
        · simp [Ix.blk] at hab
        · exact c.elim0
      · have := hh a b
        rwa [symm_sub_one_apply] at this
    · rintro ⟨-, -, h3⟩ a b
      rw [symm_sub_one_apply]
      exact h3 a b
  | succ j ih =>
    rw [TypeDatum.iter_succ]
    have hK : (reGL (ixSucc r t j)).symm h ∈ KO k (Ix r t j ⊕ t) ↔ h ∈ KO k (Ix r t (j + 1)) := by
      rw [← reGL_mem_KO_iff (ixSucc r t j), MulEquiv.apply_symm_apply]
    have mem : h ∈ ((((TypeDatum.principal k r).iter t μ hμ j).step t (μ (j + 1)) (hμ _)).reindex (ixSucc r t j)).J ↔
      (reGL (ixSucc r t j)).symm h ∈ ((TypeDatum.principal k r).iter t μ hμ j).stepJ t := Iff.rfl
    have ent : ∀ x y, ((reGL (ixSucc r t j)).symm h).val x y = h.val (ixSucc r t j x) (ixSucc r t j y) := fun _ _ => rfl
    rw [mem, TypeDatum.mem_stepJ_iff]
    constructor
    · rintro ⟨h0, ⟨g, hg, eg⟩, hC⟩
      obtain ⟨-, g2, g3⟩ := (ih g).1 hg
      have eg' : ∀ x y, g.val x y = h.val (ixSucc r t j (Sum.inl x)) (ixSucc r t j (Sum.inl y)) := fun x y => by
        rw [eg]; rfl
      refine ⟨hK.1 h0, fun a b hab => ?_, fun a b => ?_⟩
      · obtain ⟨x, rfl⟩ := (ixSucc r t j).surjective a
        obtain ⟨y, rfl⟩ := (ixSucc r t j).surjective b
        rcases x with x | s <;> rcases y with y | s'
        · rw [blk_ixSucc_inl, blk_ixSucc_inl] at hab
          rw [← eg']
          exact g2 x y hab
        · rw [blk_ixSucc_inl, blk_ixSucc_inr] at hab
          have := blk_le x
          omega
        · have := hC s y
          rwa [toBlocks₂₁, Matrix.of_apply, ent] at this
        · rw [blk_ixSucc_inr, blk_ixSucc_inr] at hab
          omega
      · have := g3 a b
        have e1 : ∀ c : r, (Sum.inl c : Ix r t (j + 1)) = ixSucc r t j (Sum.inl (Sum.inl c)) := fun c => rfl
        rw [e1 a, e1 b, ← symm_sub_one_apply, Matrix.sub_apply, ent]
        rw [Matrix.sub_apply, eg'] at this
        simpa [Matrix.one_apply] using this
    · rintro ⟨h1, h2, h3⟩
      have h0 := hK.2 h1
      have hC : GlobalTheory.StepData.MaxM ((reGL (ixSucc r t j)).symm h).val.toBlocks₂₁ := fun s y => by
        rw [toBlocks₂₁, Matrix.of_apply, ent]
        refine h2 _ _ ?_
        rw [blk_ixSucc_inl, blk_ixSucc_inr]
        have := blk_le y
        omega
      obtain ⟨⟨g, hg, eg⟩, -⟩ := GlobalTheory.StepData.exists_diag_blocks h0 hC
      have eg' : ∀ x y, g.val x y = h.val (ixSucc r t j (Sum.inl x)) (ixSucc r t j (Sum.inl y)) := fun x y => by
        rw [eg]; rfl
      refine ⟨h0, ⟨g, (ih g).2 ⟨hg, fun a b hab => ?_, fun a b => ?_⟩, eg⟩, hC⟩
      · rw [eg']
        refine h2 _ _ ?_
        rwa [blk_ixSucc_inl, blk_ixSucc_inl]
      · have := h3 a b
        have e1 : ∀ c : r, (Sum.inl c : Ix r t (j + 1)) = ixSucc r t j (Sum.inl (Sum.inl c)) := fun c => rfl
        rw [e1 a, e1 b, ← symm_sub_one_apply, Matrix.sub_apply, ent] at this
        rw [Matrix.sub_apply, eg']
        simpa [Matrix.one_apply] using this

end Iter

theorem blkOf_ixFin {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) (w : Pl D.host.E) (j : ℕ)
    (x : Ix (Fin D.R.r) (Fin D.R.t) j) :
    Formalism.L2.DIV.blkOf D.R.r D.R.t (ixFin G t w j x) = Ix.blk x := by
  obtain ⟨h1, h2⟩ := ixFin_val G t w j
  rcases x with a | ⟨c, b⟩
  · simp [Formalism.L2.DIV.blkOf, h1, Ix.blk]
  · have hb := b.2
    have hpos : 0 < D.R.t := by omega
    have hdiv : (b.val + D.R.t * c.val) / D.R.t = c.val := by
      rw [Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hb, zero_add]
    simp [Formalism.L2.DIV.blkOf, h2, Ix.blk, hdiv]

theorem mem_stepGroup_map_iff : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) (w : Pl D.host.E), w ∈ L.Pg → ∀ (j : ℕ) (g : GL (Fin ((locGrid G t w).rank (0, j))) (Kw w)), g ∈ (stepGroup L t w j).map (reGL (ixFin G t w j)).toMonoidHom ↔ g ∈ KO (Kw w) (Fin ((locGrid G t w).rank (0, j))) ∧ (∀ a b, Formalism.L2.DIV.blkOf D.R.r D.R.t b < Formalism.L2.DIV.blkOf D.R.r D.R.t a → valuation (Kw w) (g.1 a b) < 1) ∧ ∀ a b : Fin ((locGrid G t w).rank (0, j)), a.val < D.R.r → b.val < D.R.r → valuation (Kw w) ((g.1 - 1) a b) < 1 := by
  intro D T L sc G t w hw j g
  have hmap : g ∈ (stepGroup L t w j).map (reGL (ixFin G t w j)).toMonoidHom ↔
      (reGL (ixFin G t w j)).symm g ∈ stepGroup L t w j := by
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro hx
      exact ⟨_, hx, by simp⟩
  have hK : (reGL (ixFin G t w j)).symm g ∈ KO (Kw w) (Ix (Fin D.R.r) (Fin D.R.t) j) ↔
      g ∈ KO (Kw w) (Fin ((locGrid G t w).rank (0, j))) := by
    rw [← reGL_mem_KO_iff (ixFin G t w j), MulEquiv.apply_symm_apply]
  rw [hmap, stepGroup, if_pos hw, mem_iter_J, hK]
  refine and_congr_right fun _ => and_congr ?_ ?_
  · constructor
    · intro h a b hab
      obtain ⟨x, rfl⟩ := (ixFin G t w j).surjective a
      obtain ⟨y, rfl⟩ := (ixFin G t w j).surjective b
      rw [blkOf_ixFin, blkOf_ixFin] at hab
      exact h x y hab
    · intro h x y hxy
      refine h _ _ ?_
      rwa [blkOf_ixFin, blkOf_ixFin]
  · obtain ⟨h1, -⟩ := ixFin_val G t w j
    constructor
    · intro h a b ha hb
      have e : ∀ (c : Fin ((locGrid G t w).rank (0, j))) (hc : c.val < D.R.r),
          ixFin G t w j (Sum.inl ⟨c.val, hc⟩) = c := fun c hc => Fin.ext (h1 _)
      have := h ⟨a.val, ha⟩ ⟨b.val, hb⟩
      rwa [symm_sub_one_apply, e, e] at this
    · intro h a b
      rw [symm_sub_one_apply]
      exact h _ _ (by rw [h1]; exact a.2) (by rw [h1]; exact b.2)

end GlobalTheory.CompanionTheory.IterJ

end
end

end IteratedIwahori
section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

theorem _root_.GlobalTheory.Adopt.thetaGridBlockCongruence_typePrime_description : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) (w : Pl D.host.E), w ∈ L.Pg → ∀ (j : ℕ) (g : GL (Fin ((locGrid G t w).rank (0, j))) (Kw w)), g ∈ (stepGroup L t w j).map (reGL (ixFin G t w j)).toMonoidHom ↔ g ∈ KO (Kw w) (Fin ((locGrid G t w).rank (0, j))) ∧ (∀ a b, Formalism.L2.DIV.blkOf D.R.r D.R.t b < Formalism.L2.DIV.blkOf D.R.r D.R.t a → valuation (Kw w) (g.1 a b) < 1) ∧ ∀ a b : Fin ((locGrid G t w).rank (0, j)), a.val < D.R.r → b.val < D.R.r → valuation (Kw w) ((g.1 - 1) a b) < 1 := by
  first | exact @IteratedIwahori.GlobalTheory.CompanionTheory.IterJ.mem_stepGroup_map_iff | exact IteratedIwahori.GlobalTheory.CompanionTheory.IterJ.mem_stepGroup_map_iff | (intros; apply IteratedIwahori.GlobalTheory.CompanionTheory.IterJ.mem_stepGroup_map_iff <;> assumption)

end
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGridSquareRankInequalities
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.Div.SquareRanks

theorem square_ranks : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (i j : Fin D.R.m),
    (spW₁ G i j).rank < (spW G i j).rank ∧ Even ((spW G i j).rank + (spW₁ G i j).rank) ∧
    2 * ((D.R.m - j - 1) / 2 + (D.R.m - j) / 2) + 1 < ((spW G i j).rank - (spW₁ G i j).rank) / 2 ∧
    2 * ((D.R.m - j - 1) / 2 + (D.R.m - j) / 2) + 1 < (spW₁ G i j).rank := by
  intro D T L sc G μ₀ hL i j
  have r : ∀ a b, a ≤ D.R.m → b ≤ D.R.m → (G.V (.grid a b)).rank = rankV D a b :=
    fun a b ha hb => (node_isV G hL (X := .grid a b) ⟨ha, hb⟩).rank
  have hi := i.2
  have hj := j.2
  have e1 : (spW G i j).rank = rankV D (i + 1) (j + 1) := r _ _ (by omega) (by omega)
  have e2 : (spW₁ G i j).rank = rankV D i j := r _ _ (by omega) (by omega)
  have e3 : rankV D (i + 1) (j + 1) = rankV D i j + D.R.t + sLen D := by simp only [rankV]; ring
  rw [e1, e2, e3]
  have h0 : D.R.r ≤ rankV D i j := by unfold rankV; omega
  have ht := D.R.t_odd
  have hk := D.R.k_even
  have hm := D.R.m_even
  have h3 := D.R.three_m_lt_t
  have h4 := D.R.m_add_three_le_k
  have h5 := D.R.two_le_m
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hs : sLen D = D.R.r + 6 := rfl
  obtain ⟨t', ht'⟩ := ht
  obtain ⟨k', hk'⟩ := hk
  obtain ⟨m', hm'⟩ := hm
  refine ⟨by omega, ?_, by omega, by omega⟩
  rw [Nat.even_iff]
  omega

end GlobalTheory.Div.SquareRanks
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPointMemStandardAndSkewLatticeOfEntriesMem
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)
open scoped nonZeroDivisors

namespace GlobalTheory.FunObj.SqNum

theorem pt_mem_of_entries_mem (D : D7) (δ : ℂ) (𝔪 : Ideal (𝓞 D.host.E)) {a d : ℕ}
    (w : Matrix (Fin d) (Fin a) D.host.E) (hw : ∀ i j, ∃ b ∈ 𝔪, w i j = (b : D.host.E)) :
    pt D (tor0 D ⊤ δ) δ w ∈ La0 D (tor0 D ⊤ δ) a d ∧
      pt D (tor0 D ⊤ δ) δ w ∈ La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d) := by
  have key : ∀ L' : Submodule (𝓞 D.host.E) (Fin d → D.host.E), (∀ x ∈ stdL D a, w.mulVec x ∈ L') →
      pt D (tor0 D ⊤ δ) δ w ∈ La D (tor0 D ⊤ δ) (stdL D a) L' := by
    intro L' hL'
    refine AddSubgroup.subset_closure ⟨δ, AddSubgroup.subset_closure ⟨1, trivial, by simp⟩, w, ?_, rfl⟩
    refine Submodule.subset_span ⟨1, ?_, w, Submodule.subset_span hL', (one_smul _ _).symm⟩
    refine FractionalIdeal.one_mem_inv_coe_ideal fun h => ?_
    have h2 := D.host.𝔟_spec.2
    rw [h, Ideal.smul_bot, sup_bot_eq] at h2
    exact bot_ne_top h2
  have hent : ∀ x ∈ stdL D a, ∀ i, w.mulVec x i ∈
      ((𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : Submodule (𝓞 D.host.E) D.host.E) := by
    intro x hx i
    show ∑ j, w i j * x j ∈ _
    refine Submodule.sum_mem _ fun j _ => ?_
    obtain ⟨b, hb, hbw⟩ := hw i j
    obtain ⟨y, hy⟩ := Submodule.mem_one.1 (hx j trivial)
    refine (FractionalIdeal.mem_coeIdeal _).2 ⟨b * y, 𝔪.mul_mem_right y hb, ?_⟩
    rw [hbw, ← hy, map_mul]
  refine ⟨key _ fun x hx i _ => ?_, key _ fun x hx i _ => ?_⟩
  · have := (FractionalIdeal.coe_le_coe.2 FractionalIdeal.coeIdeal_le_one) (hent x hx i)
    rw [FractionalIdeal.coe_one] at this
    exact this
  · by_cases h𝔪 : 𝔪 = ⊥
    · have := hent x hx i
      rw [h𝔪, FractionalIdeal.coeIdeal_bot] at this
      have h0 : w.mulVec x i = 0 := by simpa using this
      rw [h0]
      exact zero_mem _
    · have hne : ((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := by
        rw [Ne, FractionalIdeal.coeIdeal_eq_zero]
        intro h
        apply h𝔪
        have := congrArg (fun J : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • J) h
        simpa using this
      have hle : (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≤
          (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) /
            ((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
        rw [FractionalIdeal.le_div_iff_mul_le hne]
        first
        | exact mul_le_of_le_one_right' FractionalIdeal.coeIdeal_le_one
        | exact mul_le_of_le_one_right (zero_le _) FractionalIdeal.coeIdeal_le_one
        | exact (mul_le_mul_left FractionalIdeal.coeIdeal_le_one _).trans_eq (mul_one _)
        | exact (FractionalIdeal.mul_le_mul_left FractionalIdeal.coeIdeal_le_one _).trans_eq (mul_one _)
        | exact (mul_le_mul_of_nonneg_left FractionalIdeal.coeIdeal_le_one (zero_le _)).trans_eq (mul_one _)
      exact (FractionalIdeal.coe_le_coe.2 hle) (hent x hx i)

end GlobalTheory.FunObj.SqNum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformizerOfValuationRingFixedFieldInertia
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.InertiaFixedUniformizer

theorem valuation_uniformizer_lt_one {R K Ω : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] [Field Ω] [Algebra K Ω] (V : ValuationSubring Ω) (hV : IsAbove R K V.toSubring)
    {π : R} (hπ : Irreducible π) : V.valuation (algebraMap K Ω (algebraMap R K π)) < 1 := by
  have hπ0 : algebraMap R K π ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective R K)]
    exact hπ.ne_zero
  have hle : V.valuation (algebraMap K Ω (algebraMap R K π)) ≤ 1 := by
    rw [V.valuation_le_one_iff]
    have : algebraMap R K π ∈ (V.toSubring).comap (algebraMap K Ω) := by
      rw [hV]; exact ⟨π, rfl⟩
    exact this
  refine lt_of_le_of_ne hle fun h1 => hπ.not_isUnit ?_
  have hinv : (algebraMap R K π)⁻¹ ∈ (V.toSubring).comap (algebraMap K Ω) := by
    change algebraMap K Ω (algebraMap R K π)⁻¹ ∈ V
    rw [← V.valuation_le_one_iff, map_inv₀, map_inv₀, h1, inv_one]
  rw [hV] at hinv
  obtain ⟨u, hu⟩ := hinv
  refine IsUnit.of_mul_eq_one u (IsFractionRing.injective R K ?_)
  rw [map_mul, hu, mul_inv_cancel₀ hπ0, map_one]

theorem uniformizer_fixedField_inertia : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω]
    [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring → ∀ π : R, Irreducible π →
    V.valuation (algebraMap K Ω (algebraMap R K π)) < 1 ∧
      ∀ y : IntermediateField.fixedField (inertia K V), V.valuation (y : Ω) < 1 →
        ∃ z : IntermediateField.fixedField (inertia K V), (z : Ω) ∈ V ∧
          y = algebraMap K _ (algebraMap R K π) * z := by
  intro R K Ω _ _ _ _ _ _ _ _ _ _ V hV π hπ
  refine ⟨valuation_uniformizer_lt_one V hV hπ, fun y hy => ?_⟩
  have hπ0 : algebraMap R K π ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective R K)]
    exact hπ.ne_zero
  have hmem := GlobalTheory.FixInertUnram.div_uniformizer_mem R K Ω V hV π hπ (y : Ω) y.2
    ((ValuationSubring.mem_nonunits_iff _).2 hy)
  refine ⟨y / algebraMap K _ (algebraMap R K π), ?_, ?_⟩
  · simpa using hmem
  · rw [mul_div_cancel₀]
    exact (map_ne_zero _).2 hπ0

end GlobalTheory.InertiaFixedUniformizer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryHeckeCharEqOneOfTrivialOverSplitPlacesCmStatement
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
theorem _root_.GlobalTheory.T.unitaryHeckeChar_eq_one_of_trivial_over_split_places_cm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ ν : (AF F ⊗[F] E)ˣ →* Circle, IsHeckeCharF ν →
      (∀ e, IsSplitIdemF σ e → ∀ x : (AF F ⊗[F] E)ˣ, (e + cAF σ e) * ((x : AF F ⊗[F] E) - 1) = (x : AF F ⊗[F] E) - 1 →
        ν x = 1) → ∀ x, ν x = 1 := by
  first | exact @GlobalTheory.HeckeSplitBase.heckeChar_eq_one_of_split | exact GlobalTheory.HeckeSplitBase.heckeChar_eq_one_of_split | (intros; apply GlobalTheory.HeckeSplitBase.heckeChar_eq_one_of_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedEtaCharacterKillsFiniteIdeleNormStatement
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_eta_character_kills_finite_idele_norm : ∀ (D : D7) (χ : HChar D.host.E), Formalism.L2.Host.IsEtaT D.host χ → ∀ x : (AE D)ˣ, χ.1 (finIdl D (x * sgU D x)) = 1 := by
  first | exact @GlobalTheory.EtaTildeNorm.map_finIdl_norm | exact GlobalTheory.EtaTildeNorm.map_finIdl_norm | (intros; apply GlobalTheory.EtaTildeNorm.map_finIdl_norm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationMinpolyCoeffZeroGeOfPowMulIntegralStatement
section
open NumberField Polynomial IsDedekindDomain
open Formalism.DivisionValues (vw lw)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_minpoly_coeff_zero_ge_of_pow_mul_integral : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) (β : ℂ) (p : K[X]) (l N : ℕ), GlobalTheory.FunObj.SqNum.IsMinPol σ β p → l.Prime → GlobalTheory.CMVal.IntAt l ((l : ℂ) ^ (N : ℤ) * β) → ∀ w : Formalism.PairingDivisionLocalBalance.Pl K, (l : 𝓞 K) ∈ w.asIdeal → -(((N * p.natDegree : ℕ) : ℤ) * vw w (l : K)) ≤ vw w (p.coeff 0) := by
  first | exact @GlobalTheory.FunObj.SqNum.LowVal.vw_coeff_zero_ge | exact GlobalTheory.FunObj.SqNum.LowVal.vw_coeff_zero_ge | (intros; apply GlobalTheory.FunObj.SqNum.LowVal.vw_coeff_zero_ge <;> assumption)
end

