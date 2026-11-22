import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0397
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.NormalDecomposition.LiftHeckeOperators
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0505
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0959
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0312
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsOverVacuaDenseThetaFunctions
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeColumnsOffFiniteSet

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiVertexLatticeSplitsAlongWittAtPlace
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.AscFin.MonoJac

variable {D : D7}

open GlobalTheory.SeeSaw.SplitLat (colProj colProj_mulVec colMul_rat rat_mulVec_mem_latV mulVec_eq_sum_colMul)

theorem monoAt_of_proj {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (L : Lat S) (L₀ : Lat S₀)
    (hX : ∀ i : Fin ρ, ∀ x ∈ L, colProj d.qX d.e i *ᵥ x ∈ L)
    (hY : ∀ i : Fin ρ, ∀ x ∈ L, colProj d.qY d.e' i *ᵥ x ∈ L)
    (h0 : ∀ x ∈ L, d.q0 *ᵥ x ∈ L₀) (hi : ∀ x ∈ L₀, d.i₀ *ᵥ x ∈ L) (v : GlobalTheory.FinPl.Pl D) :
    MonoAt d L L₀ v := by
  intro y
  constructor
  · intro hy
    refine ⟨fun i => ?_, fun i => ?_, ?_⟩
    · change GlobalTheory.FinPl.colMul (rat d.e) i ((rat d.qX *ᵥ y) i) ∈ _
      rw [colMul_rat]
      exact rat_mulVec_mem_latV _ (hX i) _ hy
    · change GlobalTheory.FinPl.colMul (rat d.e') i ((rat d.qY *ᵥ y) i) ∈ _
      rw [colMul_rat]
      exact rat_mulVec_mem_latV _ (hY i) _ hy
    · exact rat_mulVec_mem_latV d.q0 h0 _ hy
  · rintro ⟨h1, h3, h2⟩
    have e : y = d.jX *ᵥ (d.pX *ᵥ y) + d.j0 *ᵥ (d.p0 *ᵥ y) + d.jY *ᵥ (d.pY *ᵥ y) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, ← Matrix.add_mulVec,
        d.sum_eq_one, Matrix.one_mulVec]
    rw [e, mulVec_eq_sum_colMul d.jX, mulVec_eq_sum_colMul d.jY]
    refine add_mem (add_mem (sum_mem fun i _ => h1 i) ?_) (sum_mem fun i _ => h3 i)
    exact rat_mulVec_mem_latV d.i₀ hi _ h2

open GlobalTheory.SeeSaw.SplitLat (colProj)

theorem sumLat_map {n k c : ℕ} {M : Matrix (Fin n) (Fin k) D.host.E} {Λ : Submodule (𝓞 D.host.E) (Fin k → D.host.E)}
    {a : Matrix (Fin n) (Fin c) D.host.E} {𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E}
    (N : Matrix (Fin n) (Fin n) D.host.E) (w : Fin c → D.host.E) (hM : N * M = 0) (ha : N * a = a * Matrix.diagonal w)
    (hw : ∀ p, w p = 0 ∨ w p = 1) : ∀ x ∈ sumLat M Λ a 𝔟, N *ᵥ x ∈ sumLat M Λ a 𝔟 := by
  rintro _ ⟨y, -, u, hu, rfl⟩
  refine ⟨0, Λ.zero_mem, Matrix.diagonal w *ᵥ u, fun p => ?_, ?_⟩
  · rw [Matrix.mulVec_diagonal]
    rcases hw p with h | h
    · rw [h, zero_mul]; exact (𝔟 p).zero_mem
    · rw [h, one_mul]; exact hu p
  · rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM, ha, ← Matrix.mulVec_mulVec,
      Matrix.zero_mulVec, Matrix.mulVec_zero, zero_add]

theorem sumLat_proj {n k c : ℕ} {M : Matrix (Fin n) (Fin k) D.host.E} {Λ : Submodule (𝓞 D.host.E) (Fin k → D.host.E)}
    {a : Matrix (Fin n) (Fin c) D.host.E} {𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E}
    (q : Matrix (Fin k) (Fin n) D.host.E) (hM : q * M = 1) (ha : q * a = 0) : ∀ x ∈ sumLat M Λ a 𝔟, q *ᵥ x ∈ Λ := by
  rintro _ ⟨y, hy, u, -, rfl⟩
  rwa [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM, ha, Matrix.one_mulVec, Matrix.zero_mulVec,
    add_zero]

theorem mem_sumLat_of {n k c : ℕ} {M : Matrix (Fin n) (Fin k) D.host.E} {Λ : Submodule (𝓞 D.host.E) (Fin k → D.host.E)}
    {a : Matrix (Fin n) (Fin c) D.host.E} {𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} {y : Fin k → D.host.E}
    (hy : y ∈ Λ) : M *ᵥ y ∈ sumLat M Λ a 𝔟 :=
  ⟨y, hy, 0, fun p => (𝔟 p).zero_mem, by rw [Matrix.mulVec_zero, add_zero]⟩

theorem colProj_mul {S : HSp D} {ρ m l : ℕ} (q : Matrix (Fin ρ) (Fin m) D.host.E) (f : Matrix (Fin S.rank) (Fin ρ) D.host.E)
    (i : Fin ρ) (N : Matrix (Fin m) (Fin l) D.host.E) : colProj (S := S) q f i * N = colProj (S := S) (q * N) f i := by
  ext k j
  simp only [colProj, Matrix.mul_apply, Matrix.of_apply, Finset.mul_sum, mul_assoc]

theorem colProj_zero {S : HSp D} {ρ m : ℕ} (f : Matrix (Fin S.rank) (Fin ρ) D.host.E) (i : Fin ρ) :
    colProj (S := S) (0 : Matrix (Fin ρ) (Fin m) D.host.E) f i = 0 := by
  ext k j
  simp [colProj]

section SlopeTestRemainingChoices

variable {A B : HSp D} {c ρ : ℕ}

def cfE (c : ℕ) : Matrix (Fin ρ) (Fin c) D.host.E := fun p q => if p.1 = q.1 then ((-D.host.xi0) ^ (p.1 + 1))⁻¹ else 0

def cfE' (c : ℕ) (s : Fin ρ → D.host.E) : Matrix (Fin ρ) (Fin c) D.host.E := fun p q => if q.1 + p.1 + 1 = c then (s p)⁻¹ else 0

theorem eq_idempotent_mul_add_of_mul_sub_eq {n : ℕ} (a : Matrix (Fin n) (Fin c) D.host.E) (hc : c = 2 * ρ) (h : ρ ≤ c) (s : Fin ρ → D.host.E)
    (hs : ∀ p, s p ≠ 0) :
    a = (colsOf a (Fin.castLE h) (fun p : Fin ρ => (-D.host.xi0) ^ (p.1 + 1)) : Matrix (Fin n) (Fin ρ) D.host.E) *
        (cfE c : Matrix (Fin ρ) (Fin c) D.host.E) +
      (colsOf a (fun p : Fin ρ => (Fin.castLE h p : Fin c).rev) s : Matrix (Fin n) (Fin ρ) D.host.E) *
        (cfE' c s : Matrix (Fin ρ) (Fin c) D.host.E) := by
  have hx : ∀ p : ℕ, ((-D.host.xi0) ^ (p + 1)) ≠ 0 := fun p => pow_ne_zero _ (neg_ne_zero.2 cmHost_imaginaryGenerator_ne_zero)
  refine Matrix.ext fun k q => ?_
  rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply]
  simp only [colsOf, cfE, cfE']
  by_cases hq : q.1 < ρ
  · rw [Finset.sum_eq_single ⟨q.1, hq⟩, Finset.sum_eq_zero]
    · rw [if_pos rfl, add_zero, show (Fin.castLE h ⟨q.1, hq⟩ : Fin c) = q from Fin.ext rfl, mul_comm,
        ← mul_assoc, inv_mul_cancel₀ (hx _), one_mul]
    · intro p _
      rw [if_neg (by omega), mul_zero]
    · intro p _ hp
      rw [if_neg (fun e => hp (Fin.ext e)), mul_zero]
    · intro hn; exact absurd (Finset.mem_univ _) hn
  · have hp' : c - 1 - q.1 < ρ := by have := q.2; omega
    rw [Finset.sum_eq_zero, Finset.sum_eq_single ⟨c - 1 - q.1, hp'⟩]
    · rw [if_pos (by have := q.2; simp only [Fin.val_mk]; omega), zero_add,
        show ((Fin.castLE h ⟨c - 1 - q.1, hp'⟩ : Fin c).rev) = q from Fin.ext (by simp [Fin.val_rev]; omega),
        mul_comm, ← mul_assoc, inv_mul_cancel₀ (hs _), one_mul]
    · intro p _ hp
      rw [if_neg (fun e => hp (Fin.ext (show p.1 = c - 1 - q.1 by omega))), mul_zero]
    · intro hn; exact absurd (Finset.mem_univ _) hn
    · intro p _
      rw [if_neg (by have := p.2; omega), mul_zero]

end SlopeTestRemainingChoices

open GlobalTheory.SeeSaw.SplitLat (colProj)

theorem auxiliaryLattice_splitsAlongWitt_at_place {A B : HSp D} {c ρ : ℕ} (t : HermitianOrthogonalExtensionData A B c (-1)) (d : HypDec B A ρ) (hc : c = 2 * ρ)
    (hh : IsAuxiliaryVectorWittDec t d) (hi : d.i₀ = frameMat B A t.ι) (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E))
    (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (v : GlobalTheory.FinPl.Pl D) : MonoAt d (t.lat Λ 𝔟) Λ v := by
  obtain ⟨h2, he, s, he'⟩ := hh
  have hρ : ρ ≤ c := by omega
  have hx : ∀ p : ℕ, ((-D.host.xi0) ^ (p + 1)) ≠ 0 := fun p => pow_ne_zero _ (neg_ne_zero.2 cmHost_imaginaryGenerator_ne_zero)
  have hs : ∀ p, s p ≠ 0 := by
    intro p hp
    have h1 := congrFun (congrFun d.e'e p) p
    rw [Matrix.one_apply_eq] at h1
    have hcol : ∀ k, d.e' k p = 0 := fun k => by rw [he']; simp [colsOf, hp]
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, hcol] at h1
  have ha := eq_idempotent_mul_add_of_mul_sub_eq t.a hc hρ s hs
  rw [← he, ← he'] at ha
  have hX : d.qX * t.a = cfE c := by
    rw [ha, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, GlobalTheory.SeeSaw.SplitLat.qX_e, GlobalTheory.SeeSaw.SplitLat.qX_e',
      Matrix.one_mul, Matrix.zero_mul, add_zero]
  have hY : d.qY * t.a = cfE' c s := by
    rw [ha, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, GlobalTheory.SeeSaw.SplitLat.qY_e, GlobalTheory.SeeSaw.SplitLat.qY_e',
      Matrix.one_mul, Matrix.zero_mul, zero_add]
  have h0 : d.q0 * t.a = 0 := by
    rw [ha, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, GlobalTheory.SeeSaw.SplitLat.wittDecomposition_coreProj_mul_e_eq_zero, GlobalTheory.SeeSaw.SplitLat.wittZeroProjection_mul_dualBasis_eq_zero,
      Matrix.zero_mul, Matrix.zero_mul, add_zero]
  refine monoAt_of_proj d _ _ (fun i => ?_) (fun i => ?_) ?_ ?_ v
  · refine sumLat_map _ (Pi.single (Fin.castLE hρ i) 1) ?_ ?_ ?_
    · rw [colProj_mul, ← hi, GlobalTheory.SeeSaw.SplitLat.qX_i₀, colProj_zero]
    · rw [colProj_mul, hX]
      refine Matrix.ext fun k q => ?_
      rw [Matrix.mul_diagonal, he]
      simp only [colProj, Matrix.of_apply, colsOf, cfE]
      by_cases hq : i.1 = q.1
      · have e : (Fin.castLE hρ i : Fin c) = q := Fin.ext hq
        subst e
        rw [if_pos hq, Pi.single_eq_same, mul_one, mul_comm ((-D.host.xi0) ^ _), mul_assoc, mul_inv_cancel₀ (hx _),
          mul_one]
      · have e : q ≠ (Fin.castLE hρ i : Fin c) := fun e => hq (by rw [e]; rfl)
        rw [if_neg hq, mul_zero, Pi.single_apply, if_neg e, mul_zero]
    · intro p
      rw [Pi.single_apply]
      split_ifs
      · exact Or.inr rfl
      · exact Or.inl rfl
  · refine sumLat_map _ (Pi.single (Fin.castLE hρ i : Fin c).rev 1) ?_ ?_ ?_
    · rw [colProj_mul, ← hi, GlobalTheory.SeeSaw.SplitLat.qY_i₀, colProj_zero]
    · rw [colProj_mul, hY]
      refine Matrix.ext fun k q => ?_
      rw [Matrix.mul_diagonal, he']
      simp only [colProj, Matrix.of_apply, colsOf, cfE']
      by_cases hq : q.1 + i.1 + 1 = c
      · have e : (Fin.castLE hρ i : Fin c).rev = q := Fin.ext (by simp [Fin.val_rev]; omega)
        subst e
        rw [if_pos hq, Pi.single_eq_same, mul_one, mul_comm (s i), mul_assoc, mul_inv_cancel₀ (hs _), mul_one]
      · have e : q ≠ (Fin.castLE hρ i : Fin c).rev := fun e => hq (by rw [e]; simp [Fin.val_rev]; omega)
        rw [if_neg hq, mul_zero, Pi.single_apply, if_neg e, mul_zero]
    · intro p
      rw [Pi.single_apply]
      split_ifs
      · exact Or.inr rfl
      · exact Or.inl rfl
  · exact sumLat_proj d.q0 (by rw [← hi]; exact GlobalTheory.SeeSaw.SplitLat.wittDecomposition_coreProj_mul_core_eq_one d) h0
  · intro x hx
    rw [hi]
    exact mem_sumLat_of hx

theorem monoAt_jac : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (F : Frames G), Std F →
    ∀ (ρ : ℕ) (h : 2 * ρ + 2 ≤ D.R.m) (v : GlobalTheory.FinPl.Pl D),
      MonoAt (F.dJ ρ h) (G.Λ (.grid (2 * ρ + 1) 0)) (G.Λ (.core (2 * ρ + 1))) v := by
  intro D T L sc G F hF ρ h v
  have H := auxiliaryLattice_splitsAlongWitt_at_place (G.colDec (2 * ρ + 1) (by omega) (by omega)) (F.dJ ρ h) (by omega) (hF.hJ ρ h) (hF.aJ ρ h)
    (G.Λ (.core (2 * ρ + 1))) (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1)) v
  rw [← G.sp.colLat (2 * ρ + 1) (by omega) (by omega)] at H
  exact H

end GlobalTheory.AscFin.MonoJac

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GivenOppositeGridPathsAndDeterminedByEdges
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FlipPaths

variable {T : Type}

theorem arrows_comp {X Y : Node} (p : Path T X Y) : ∀ {Z : Node} (q : Path T Y Z), (p.comp q).arrows = p.arrows ++ q.arrows
  | _, .nil => by simp [Path.comp, Path.arrows]
  | _, .snoc a q => by simp [Path.comp, Path.arrows, arrows_comp p q]

theorem rowPath_arrows (j : ℕ) : ∀ n, (rowPath T j n).arrows = (List.range n).map fun i => Arrow.right i j
  | 0 => by simp [rowPath, Path.arrows]
  | n + 1 => by simp [rowPath, Path.arrows, rowPath_arrows j n, List.range_succ]

theorem downPath_arrows (t : T) (i : ℕ) : ∀ n, (downPath t i n).arrows = (List.range n).reverse.map fun j => Arrow.down t i j
  | 0 => by simp [downPath, Path.arrows]
  | n + 1 => by simp [downPath, arrows_comp, Path.arrows, downPath_arrows t i n, List.range_succ]

theorem edgeOf_inj {m : ℕ} {t : T} {a b : Arrow T} (ha : GlobalTheory.FlipRun.IsGridArrow m t a) (hb : GlobalTheory.FlipRun.IsGridArrow m t b)
    (h : GlobalTheory.FlipRun.edgeOf a = GlobalTheory.FlipRun.edgeOf b) : a = b := by
  rcases ha with ⟨i, j, -, -, rfl⟩ | ⟨i, j, -, -, rfl⟩ <;> rcases hb with ⟨k, l, -, -, rfl⟩ | ⟨k, l, -, -, rfl⟩ <;>
    simp_all [GlobalTheory.FlipRun.edgeOf]

theorem map_edgeOf_inj {m : ℕ} {t : T} : ∀ (l₁ l₂ : List (Arrow T)), (∀ a ∈ l₁, GlobalTheory.FlipRun.IsGridArrow m t a) →
    (∀ a ∈ l₂, GlobalTheory.FlipRun.IsGridArrow m t a) → l₁.map GlobalTheory.FlipRun.edgeOf = l₂.map GlobalTheory.FlipRun.edgeOf → l₁ = l₂
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | a :: l₁, b :: l₂, h₁, h₂, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [edgeOf_inj (h₁ a (by simp)) (h₂ b (by simp)) h.1,
      map_edgeOf_inj l₁ l₂ (fun x hx => h₁ x (by simp [hx])) (fun x hx => h₂ x (by simp [hx])) h.2]

theorem gridArrowPath_heq_of_arrows_eq {X : Node} : ∀ {Y : Node} (p : Path T X Y) {Y' : Node} (q : Path T X Y'),
    p.arrows = q.arrows → HEq p q := by
  intro Y p
  induction p with
  | nil =>
    intro Y' q h
    cases q with
    | nil => rfl
    | snoc b q => simp [Path.arrows] at h
  | snoc a p ih =>
    intro Y' q h
    cases q with
    | nil => simp [Path.arrows] at h
    | snoc b q =>
      simp only [Path.arrows] at h
      obtain ⟨h1, h2⟩ := List.append_inj' h rfl
      simp only [List.cons.injEq, and_true] at h2
      subst h2
      have := eq_of_heq (ih q h1)
      subst this
      rfl

theorem eq_of_arrows {X Y : Node} (p q : Path T X Y) (h : p.arrows = q.arrows) : p = q :=
  eq_of_heq (gridArrowPath_heq_of_arrows_eq p q h)

theorem givenPath_arrows (t : T) (m : ℕ) : (givenPath t m).arrows =
    (List.range m).reverse.map (fun j => Arrow.down t 0 j) ++ (List.range m).map fun i => Arrow.right i 0 := by
  simp [givenPath, arrows_comp, rowPath_arrows, downPath_arrows]

theorem oppPath_arrows (t : T) (m : ℕ) : (oppPath t m).arrows =
    (List.range m).map (fun i => Arrow.right i m) ++ (List.range m).reverse.map fun j => Arrow.down t m j := by
  simp [oppPath, arrows_comp, rowPath_arrows, downPath_arrows]

theorem given_opp_paths : ∀ {T : Type} (m : ℕ) (t : T), (GlobalTheory.FlipRun.OnGrid m t (GlobalTheory.FunObj.givenPath t m) ∧ GlobalTheory.FlipRun.edges (GlobalTheory.FunObj.givenPath t m) = GlobalTheory.SplitFlip.givenPath m) ∧ (GlobalTheory.FlipRun.OnGrid m t (GlobalTheory.FunObj.oppPath t m) ∧ GlobalTheory.FlipRun.edges (GlobalTheory.FunObj.oppPath t m) = GlobalTheory.SplitFlip.oppositePath m) ∧ ∀ {X Y : Node} (p q : Path T X Y), GlobalTheory.FlipRun.OnGrid m t p → GlobalTheory.FlipRun.OnGrid m t q → GlobalTheory.FlipRun.edges p = GlobalTheory.FlipRun.edges q → p = q := by
  intro T m t
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · intro a ha
    rw [givenPath_arrows] at ha
    simp only [List.mem_append, List.mem_map, List.mem_reverse, List.mem_range] at ha
    rcases ha with ⟨j, hj, rfl⟩ | ⟨i, hi, rfl⟩
    · exact Or.inr ⟨0, j, Nat.zero_le _, hj, rfl⟩
    · exact Or.inl ⟨i, 0, hi, Nat.zero_le _, rfl⟩
  · simp [GlobalTheory.FlipRun.edges, givenPath_arrows, GlobalTheory.SplitFlip.givenPath, GlobalTheory.FlipRun.edgeOf, Function.comp_def]
  · intro a ha
    rw [oppPath_arrows] at ha
    simp only [List.mem_append, List.mem_map, List.mem_reverse, List.mem_range] at ha
    rcases ha with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩
    · exact Or.inl ⟨i, m, hi, le_rfl, rfl⟩
    · exact Or.inr ⟨m, j, le_rfl, hj, rfl⟩
  · simp [GlobalTheory.FlipRun.edges, oppPath_arrows, GlobalTheory.SplitFlip.oppositePath, GlobalTheory.FlipRun.edgeOf, Function.comp_def]
  · intro X Y p q hp hq h
    exact eq_of_arrows p q (map_edgeOf_inj _ _ hp hq h)

end GlobalTheory.FlipPaths
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodVOfGoodL
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows
open Formalism.IndefR.CxPass Formalism.IndefR.CxPass.LevelOperators

namespace GlobalTheory.GoodModelVec

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

set_option maxHeartbeats 4000000 in

theorem actL_coord (R : RealDat D A Ks) (hr : R.grp_red_L) (hj : R.models_jV) (i : Fin D.R.m) (hc : (R.cV i).Is) (t : T0)
    (g : G) (x : (A.fam.L i t).S.Forms) (ℓ : (R.cV i).W →ₗ[ℂ] ℂ) :
    actL (Vc D i) (R.βV i) (R.datVt i t) (R.eG g) (fun h => ℓ (R.extV i t (R.jV i t x) h)) =
      fun h => ℓ (R.extV i t (R.jV i t ((A.fam.L i t).r g x)) h) := by
  have hT := GlobalTheory.RationalFormsAction.isTranslate_act_V R hr hj i t g x
  have hk : ∃ κ, IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) (R.eG g) κ := by
    obtain ⟨κ, h1, -⟩ := GlobalTheory.LiftEquivariance.exists_adelic_lift hT
    exact ⟨κ, h1⟩
  funext h
  refine (GlobalTheory.SecLift.actL_apply hk _ h).trans ?_
  have hs := hk.choose_spec
  have e1 := finE_eq (Vc D i) hk.choose
  have hq : (finHom (Vc D i)).rangeRestrict hk.choose ∈ (levEnv (Vc D i) (R.βV i) (R.datVt i t)).Q := by
    show Formalism.UG.bc (swapAE D) (finHom (Vc D i) hk.choose) ∈ lev _ _ _ _
    rw [← e1]
    exact ⟨hs.2.1, Subgroup.mem_top _⟩
  have hl : GlobalTheory.IndefiniteRowSideFullHecke.TranslateRepresentations.LiftsTo (Vc D i) (R.βV i) (R.datVt i t) ⟨(finHom (Vc D i)).rangeRestrict hk.choose, hq⟩ (R.eG g) := by
    show rTup (R.βV i) (R.datVt i t) (Formalism.UG.bc (swapAE D) (finHom (Vc D i) hk.choose)) = R.eG g
    rw [← e1]; exact hs.2.2
  have hT2 : ∀ u, (R.HV i t).e ((R.jV i t) (((A.fam.L i t).r g) x)) u =
      ((((levEnv (Vc D i) (R.βV i) (R.datVt i t)).ch ⟨(finHom (Vc D i)).rangeRestrict hk.choose, hq⟩)⁻¹ : ℂˣ) : ℂ) •
        (R.HV i t).e ((R.jV i t) x) (u * (finHom (Vc D i)).rangeRestrict hk.choose) := hT.2 _ hl
  have h2 := GlobalTheory.SecLift.coord_translate (R.cV i) hc hs.1 _ hT2 ℓ h
  have ec := GlobalTheory.LiftEquivariance.ch_eq (V := Vc D i) (β := R.βV i) (L := R.datVt i t) ⟨(finHom (Vc D i)).rangeRestrict hk.choose, hq⟩
  have e2 : levFn (R.βV i) (flagL (R.datVt i t)) (Formalism.UG.bc (swapAE D) ((finHom (Vc D i)) hk.choose)) =
      levFn (R.βV i) (flagL (R.datVt i t)) (finE (Vc D i) hk.choose) := by rw [e1]
  have hc' : ((((levEnv (Vc D i) (R.βV i) (R.datVt i t)).ch ⟨(finHom (Vc D i)).rangeRestrict hk.choose, hq⟩ : ℂˣ)) : ℂ) =
      levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) hk.choose := congrArg Units.val (ec.trans e2)
  rw [Units.val_inv_eq_inv_val, hc'] at h2
  exact h2.symm

set_option maxHeartbeats 4000000 in

theorem goodV_of_fix (R : RealDat D A Ks) (hr : R.grp_red_L) (hj : R.models_jV) (i : Fin D.R.m) (hc : (R.cV i).Is)
    (x : (A.fam.L i A.μ0).S.Forms) (hx : opF (A.fam.L i A.μ0).r (idemOf A.X) x = x) :
    GlobalTheory.LiftRows.GoodV R i (R.jV i A.μ0 x) := by
  intro ℓ
  let Φ : (R.HV i A.μ0).H →ₗ[ℂ] (GA D (Vc D i) → ℂ) := ℓ.compLeft (GA D (Vc D i)) ∘ₗ R.extV i A.μ0
  have hΦ : ∀ y, Φ y = fun h => ℓ (R.extV i A.μ0 y h) := fun _ => rfl
  have key : ∀ g, Φ (R.jV i A.μ0 ((A.fam.L i A.μ0).r g x)) =
      actL (Vc D i) (R.βV i) (R.datVt i A.μ0) (R.eG g) (Φ (R.jV i A.μ0 x)) := fun g =>
    (actL_coord R hr hj i hc A.μ0 g x ℓ).symm
  have hs : ∀ a, RealDat.eC (A := A) (sg0 D A) a = D.what₂.embLL ((idemOf A.X).coeff a) := fun a => by
    show sg0 D A _ = _
    rw [sg0, sgAt_mk D.what₂.embLL R.hv0]
  have e1 : Φ (R.jV i A.μ0 (opF (A.fam.L i A.μ0).r (idemOf A.X) x)) =
      gaL (Vc D i) (R.βV i) (R.datVt i A.μ0) R.eG (RealDat.eC (A := A) (sg0 D A)) (Φ (R.jV i A.μ0 x)) := by
    simp only [opF, gaL, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, LinearMap.map_smulₛₗ, key, hs, RingHom.id_apply]
    rfl
  rw [← hΦ, ← e1, hx]

noncomputable def goodSub (R : RealDat D A Ks) (i : Fin D.R.m) : Submodule ℂ (R.HV i A.μ0).H :=
  ⨅ ℓ : (R.cV i).W →ₗ[ℂ] ℂ, LinearMap.ker
    (gaL (Vc D i) (R.βV i) (R.datVt i A.μ0) R.eG (RealDat.eC (A := A) (sg0 D A)) ∘ₗ (ℓ.compLeft (GA D (Vc D i)) ∘ₗ R.extV i A.μ0) -
      ℓ.compLeft (GA D (Vc D i)) ∘ₗ R.extV i A.μ0)

theorem mem_goodSub (R : RealDat D A Ks) (i : Fin D.R.m) (y : (R.HV i A.μ0).H) :
    y ∈ goodSub R i ↔ GlobalTheory.LiftRows.GoodV R i y := by
  simp only [goodSub, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
  rfl

end GlobalTheory.GoodModelVec

open GlobalTheory.GoodModelVec in
set_option maxHeartbeats 4000000 in

theorem GlobalTheory.goodV_of_goodL : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) → R.PGEquiv F → ∀ (j : Fin D.R.m) (y : (R.toCx3 F).FLC j A3.A.fam.μ0), y ∈ U2.goodL A3 (R.toCx3 F) F.P0 F.ψ0 F.P1 F.ψ1 j → GoodV R.toRealDat j (Tw.out (s := twAt D.what₂.embLL A3.A.v0) y) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hok hC _ _ _ j y hy
  have hM := hC.base.models
  have hr := hC.base.grp.red_L
  have hfix : ∀ x ∈ BlockGood.goodR (A3.fam3.F.L j A3.A.fam.μ0) (A3.fam3.F.lvlA F.P0 F.ψ0),
      opF (A3.A.fam.L j A3.A.fam.μ0).r (idemOf A3.A.X) x = x := by
    intro x hx
    rw [goodR_eq] at hx
    obtain ⟨z, rfl⟩ := hx
    have hid := opF_goodAt_idem (A3.A.fam.L j A3.A.fam.μ0).r A3.A.X hok.ok2.irr ⊥ 1
    rw [goodAt_bot] at hid
    show opF _ (idemOf A3.A.X) (opF _ (idemOf A3.A.X * lvlIdem F.P0 F.ψ0⁻¹) z) = opF _ (idemOf A3.A.X * lvlIdem F.P0 F.ψ0⁻¹) z
    rw [opF_mul, LinearMap.comp_apply]
    exact LinearMap.congr_fun hid _
  have hy' : y ∈ Submodule.span ℂ ((R.toCx3 F).jL j A3.A.fam.μ0 ''
      (BlockGood.goodR (A3.fam3.F.L j A3.A.fam.μ0) (A3.fam3.F.lvlA F.P0 F.ψ0) : Set _)) := hy
  rw [← mem_goodSub]
  clear hy
  induction hy' using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨x, hx, rfl⟩ := hz
    exact (mem_goodSub _ _ _).2 (goodV_of_fix R.toRealDat hr hM.jV j (hM.cV j) x (hfix x hx))
  | zero => exact Submodule.zero_mem _
  | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb
  | smul c a _ ha => exact Submodule.smul_mem _ (Links.cj (twAt D.what₂.embLL A3.A.v0) c) ha
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridDownArrowThetaFunctionFockDenseOfLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ArrowFockDense

open GlobalTheory.RealWeil GlobalTheory.Mem.Lift GlobalTheory.Size GlobalTheory.ChainFr GlobalTheory.FockCompare GlobalTheory.OrientedHeis GlobalTheory.FockDensity

theorem dense_level : ∀ (D : D7) (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ (t : T) i j, i ≤ D.R.m → j < D.R.m → ∀ (U : AddSubgroup (WO (G.V i j).V (G.V i (j + 1)).V)), IsOpen (U : Set (WO (G.V i j).V (G.V i (j + 1)).V)) → ∀ Φ ∈ GlobalTheory.Size.thetaLevel R.ψ (G.V i j).V (G.V i (j + 1)).V U, ∀ (μ : Measure (WO (G.V i j).V (G.V i (j + 1)).V)) (𝓕 : Set (WO (G.V i j).V (G.V i (j + 1)).V)), IsCovolOne (ratL (G.V i (j + 1)).V (G.V i j).V) μ 𝓕 → ∀ (d : ℕ) (ε : ℝ), 0 < ε → ∃ (n : ℕ) (fs : Fin n → (WO (G.V i j).V (G.V i (j + 1)).V → ℂ)) (ps : Fin n → PolF D (G.V i (j + 1)).V.rank (G.V i j).V.rank), (∀ l, GlobalTheory.Grid.IsFinVec R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (fs l)) ∧ (∑ l, GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (fs l) (ps l)) ∈ GlobalTheory.Size.thetaLevel R.ψ (G.V i j).V (G.V i (j + 1)).V U ∧ GlobalTheory.Size.sobO R.ψ R.θ μ 𝓕 d ((∑ l, GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (fs l) (ps l)) - Φ) < ENNReal.ofReal ε := by
  intro D G₀ _ _ Pl0 T A Ks _ _ _ R G hRB hG t i j hi hj U hU Φ hΦ μ 𝓕 hm d ε hε
  have hω : IsWeilDatumO R.ψ (G.V i j).V (G.V i (j + 1)).V _ _ (G.th t i j).ω :=
    (GlobalTheory.Grid.isWeil_false _ _ _ _ _ _).1 (hG.arrows.th t i j hi hj).weil
  have hψ : IsStdChar D R.ψ (-1) := hω.std
  have hθ : IsInfFam R.θ := hRB.inf
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨-, i2, i3, i4, i5, -⟩ := GlobalTheory.AdelicMatrixLattice.lattice D (G.V i (j + 1)).V (G.V i j).V
  haveI : BorelSpace (WO (G.V i j).V (G.V i (j + 1)).V) := ⟨rfl⟩
  haveI : IsFiniteMeasure (μ.restrict 𝓕) :=
    ⟨by rw [Measure.restrict_apply_univ, hm.2.2]; exact ENNReal.one_lt_top⟩
  have e0 : coeL R.ψ _ _ (toB hψ Φ hΦ.1) = Φ := coe_toB hψ Φ hΦ.1
  have hF : toB hψ Φ hΦ.1 ∈ (thetaLevel R.ψ (G.V i j).V (G.V i (j + 1)).V U).comap (coeL R.ψ _ _) := by
    rw [Submodule.mem_comap, e0]
    exact hΦ
  obtain ⟨g, h1, h2, h3⟩ := dense_vec h hψ (Fr.ofModel (G.V i j).M) (Fr.ofModel (G.V i (j + 1)).M) hU
    (toL2 _ _ (μ.restrict 𝓕))
    (fun v F => by
      rw [← enorm_sq_inj, ← lintegral_norm_sq_eq_toL2, ← lintegral_norm_sq_eq_toL2]
      exact lintegral_rhoB hψ μ 𝓕 hm.1 hm.2.1 _ F)
    (fun a : D.what₂.Tau × Fin (G.V i (j + 1)).V.rank × Fin (G.V i j).V.rank × Bool =>
      atPl a.1 (Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1))) d hF
    (ENNReal.ofReal_pos.2 hε)
  have e1 : ∀ F : BB R.ψ (G.V i j).V (G.V i (j + 1)).V,
      l2O μ 𝓕 (coeL R.ψ _ _ F) = ‖toL2 _ _ (μ.restrict 𝓕) F‖ₑ := fun F =>
    (eLpNorm_congr_ae (BoundedContinuousFunction.coeFn_toLp 2 (μ.restrict 𝓕) ℂ F.1)).symm.trans (Lp.enorm_def _).symm
  have e2 : Φ - coeL R.ψ _ _ g = coeL R.ψ _ _ (toB hψ Φ hΦ.1 - g) := by rw [LinearMap.map_sub, e0]
  have hS : sobO R.ψ R.θ μ 𝓕 d (Φ - coeL R.ψ _ _ g) < ENNReal.ofReal ε := by
    refine lt_of_eq_of_lt ?_ h3
    simp only [sobO, wordSum, e2, coe_word h hψ hU _ (sub_mem hF h2), e1]

  obtain ⟨n, c, gs, hgs⟩ := Submodule.mem_span_set'.1 (Submodule.mem_comap.1 h1)
  choose f₀ P hv hl hP using fun l => (gs l).2
  refine ⟨n, f₀, fun l => c l • P l, fun l => hv l, ?_, ?_⟩
  · have e3 : (∑ l, GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (f₀ l) (c l • P l)) = coeL R.ψ _ _ g := by
      rw [← hgs]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [hP l, map_smul]
      rfl
    rw [e3]
    exact h2
  · have e3 : (∑ l, GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (f₀ l) (c l • P l)) - Φ =
        (-1 : ℂ) • (Φ - coeL R.ψ _ _ g) := by
      rw [← hgs, neg_one_smul, neg_sub]
      congr 1
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [hP l, map_smul]
      rfl
    rw [e3, sobO_smul, enorm_neg, enorm_one, one_mul]
    exact hS

end GlobalTheory.ArrowFockDense
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeColumnsOffFiniteSetStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselLevel_columns_carry_latticeLines_offExceptional : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ v ∉ G.pl.S0, ColsAt (F.dB ρ h) (xZero (F.dJ ρ h)) (G.Λ (.grid (2 * ρ + 2) 0)) (G.Λ (.grid (2 * ρ + 1) 0)) v := by
  first | exact @GlobalTheory.StairCols.colsAt_xZero | exact GlobalTheory.StairCols.colsAt_xZero | (intros; apply GlobalTheory.StairCols.colsAt_xZero <;> assumption)
end

