import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabIntPfG
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.GlobalConditionOfLocalAgreement
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0056

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabIntPfQ
section
noncomputable section

open scoped Classical

open ValuativeRel NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef Formalism.L2.SG.PairVal Formalism.MainNotions.S.LocalSplitGroups

namespace Formalism.L2.SG.Pf.StabIntSh

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem gS_ne : ((gS D : ℕ) : D.host.E) ≠ 0 := by
  unfold gS; push_cast
  exact mul_ne_zero (by exact_mod_cast (D.host.g_prime 0).ne_zero) (by exact_mod_cast (D.host.g_prime 1).ne_zero)

theorem qdPow_mem_iff (k : ℕ) (w : D.host.E) : w ∈ qdPow D k ↔ w / ((gS D : ℕ) : D.host.E) ∈ ddPow D k := by
  unfold qdPow qq
  rw [FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.mem_singleton_mul]
  have h0 := gS_ne (D := D)
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [map_natCast, mul_div_cancel_left₀ _ h0]; exact hy
  · intro h
    refine ⟨_, h, ?_⟩
    rw [map_natCast, mul_div_cancel₀ _ h0]

theorem mem_span_mul_iff {K : Type*} [CommRing K] (O : Subring K) (t : K) (ht : IsUnit t) (S : Set K) (y : K) :
    y ∈ Submodule.span O ((fun s => t * s) '' S) ↔ Ring.inverse t * y ∈ Submodule.span O S := by
  have hinv : Ring.inverse t * t = 1 := Ring.inverse_mul_cancel t ht
  have fwd : ∀ (t' : K) (T : Set K) (x : K), x ∈ Submodule.span O T →
      t' * x ∈ Submodule.span O ((fun s => t' * s) '' T) := by
    intro t' T x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => rw [mul_zero]; exact zero_mem _
    | add x z _ _ hx hz => rw [mul_add]; exact add_mem hx hz
    | smul o x _ hx =>
      rw [Subring.smul_def, smul_eq_mul, mul_left_comm, ← smul_eq_mul, ← Subring.smul_def]
      exact Submodule.smul_mem _ o hx
  constructor
  · intro hy
    have := fwd (Ring.inverse t) _ y hy
    rwa [Set.image_image, show (fun s => Ring.inverse t * (t * s)) = id by
      funext s; rw [← mul_assoc, hinv, one_mul]; rfl, Set.image_id] at this
  · intro hy
    have := fwd t S _ hy
    rwa [← mul_assoc, Ring.mul_inverse_cancel t ht, one_mul] at this

variable (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (hA : ∀ q, Agree δ M q) (p : PlF D)

theorem ιgS_mul_inv : (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) * (D.s.atP p).ιE (((gS D : ℕ) : D.host.E)⁻¹) = 1 := by
  rw [← map_mul, mul_inv_cancel₀ gS_ne, map_one]

def uGS : (D.s.atP p).Epˣ :=
  ⟨(D.s.atP p).ιE ((gS D : ℕ) : D.host.E), (D.s.atP p).ιE (((gS D : ℕ) : D.host.E)⁻¹), ιgS_mul_inv p,
    by rw [mul_comm]; exact ιgS_mul_inv p⟩

theorem locMem_qd_iff (k : ℕ) (z : D.host.E) :
    LocMem D p (qdPow D k) z ↔ LocMem D p (ddPow D k) (z / ((gS D : ℕ) : D.host.E)) := by
  unfold LocMem
  set ι := (D.s.atP p).ιE
  have hu : IsUnit (ι ((gS D : ℕ) : D.host.E)) := (uGS p).isUnit
  have hset : ι '' (qdPow D k : Set D.host.E) =
      (fun s => ι ((gS D : ℕ) : D.host.E) * s) '' (ι '' (ddPow D k : Set D.host.E)) := by
    rw [Set.image_image]
    ext x
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨w / ((gS D : ℕ) : D.host.E), (qdPow_mem_iff k w).1 hw, ?_⟩
      show ι ((gS D : ℕ) : D.host.E) * ι (w / ((gS D : ℕ) : D.host.E)) = ι w
      rw [← map_mul, mul_div_cancel₀ _ gS_ne]
    · rintro ⟨y, hy, rfl⟩
      refine ⟨((gS D : ℕ) : D.host.E) * y, (qdPow_mem_iff k _).2 (by rwa [mul_div_cancel_left₀ _ gS_ne]), ?_⟩
      show ι (((gS D : ℕ) : D.host.E) * y) = ι ((gS D : ℕ) : D.host.E) * ι y
      rw [map_mul]
  rw [hset, mem_span_mul_iff _ _ hu]
  have hi : Ring.inverse (ι ((gS D : ℕ) : D.host.E)) = ι (((gS D : ℕ) : D.host.E)⁻¹) := by
    rw [show ι ((gS D : ℕ) : D.host.E) = ((uGS p : (D.s.atP p).Epˣ) : (D.s.atP p).Ep) from rfl, Ring.inverse_unit]
    rfl
  rw [hi, ← map_mul, div_eq_mul_inv, mul_comm z]

include hA in

theorem qLocG_of_data (g : Loc.SplitG (M p).L) (hs : (M p).split = some g) (k : ℕ) (hk : k ≤ D.R.rS)
    (z : D.host.E) :
    LocMem D p (qdPow D k) z ↔ ∃ o ∈ (D.s.atP p).O,
      cc δ p ^ k * (D.s.atP p).ιE z = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp) * o := by
  rw [locMem_qd_iff, locMem_iff δ M hA p hk]
  set ι := (D.s.atP p).ιE

  obtain ⟨sg, hsg, hq⟩ : ∃ sg, (D.s.atP p).split = some sg ∧ g.q = sg.q := by
    have h6 := (hA p).2.2.2.2.2
    cases hD : (D.s.atP p).split with
    | none => rw [hs, hD] at h6; exact h6.elim
    | some sg => rw [hs, hD] at h6; exact ⟨sg, rfl, h6.2⟩
  have hgp := Formalism.MainNotions.BridgeLemma.gpart_some p sg hsg

  have hgS : ι ((gS D : ℕ) : D.host.E) =
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp) * ι ((Formalism.MainNotions.BridgeLemma.oth p : ℕ) : D.host.E) := by
    rw [hq, sg.q_eq, ← Formalism.MainNotions.BridgeLemma.gpart_mul_oth p, hgp]
    simp only [Nat.cast_mul, map_mul, map_natCast]
  have huP : ι (uP p : D.host.E) * ι ((Formalism.MainNotions.BridgeLemma.oth p : ℕ) : D.host.E) = 1 := by
    rw [← map_mul, Formalism.MainNotions.BridgeLemma.unitAt_eq p]
    have h0 : ((Formalism.MainNotions.BridgeLemma.oth p : ℕ) : D.host.E) ≠ 0 := by
      exact_mod_cast Formalism.MainNotions.BridgeLemma.oth_ne_zero p
    push_cast
    rw [inv_mul_cancel₀ h0, map_one]
  have huO : ι (uP p : D.host.E) ∈ (D.s.atP p).O := LocFacts.unitPart_mem₂ p
  have hoO : ι ((Formalism.MainNotions.BridgeLemma.oth p : ℕ) : D.host.E) ∈ (D.s.atP p).O := by
    rw [map_natCast]; exact natCast_mem _ _
  have hz : ι z = ι (z / ((gS D : ℕ) : D.host.E)) * ι ((gS D : ℕ) : D.host.E) := by
    rw [← map_mul, div_mul_cancel₀ _ gS_ne]
  constructor
  · intro h
    refine ⟨ι ((Formalism.MainNotions.BridgeLemma.oth p : ℕ) : D.host.E) * (cc δ p ^ k * ι (z / ((gS D : ℕ) : D.host.E))),
      mul_mem hoO h, ?_⟩
    rw [hz, hgS]; ring
  · rintro ⟨o, ho, he⟩
    have : cc δ p ^ k * ι (z / ((gS D : ℕ) : D.host.E)) = o * ι (uP p : D.host.E) := by
      have h1 : cc δ p ^ k * ι (z / ((gS D : ℕ) : D.host.E)) * ι ((gS D : ℕ) : D.host.E) =
          o * ι (uP p : D.host.E) * ι ((gS D : ℕ) : D.host.E) := by
        rw [mul_assoc, ← hz, he, hgS]
        linear_combination (-(algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp) * o)) * huP
      have hu : IsUnit (ι ((gS D : ℕ) : D.host.E)) := (uGS p).isUnit
      exact hu.mul_right_cancel h1
    rw [this]; exact mul_mem ho huO

theorem qLocG : QLocG D := fun δ M hA p g hs k hk z => qLocG_of_data δ M hA p g hs k hk z

theorem locShapeG : LocShapeG D := locShapeG_of qLocG

end Formalism.L2.SG.Pf.StabIntSh
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.YvMemUUE
section
noncomputable section

open Module
open Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.BasicNotions Formalism.L2.SG.TermOp

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

theorem X_le_UUE (Λ : Submodule (NumberField.RingOfIntegers E) S.V) (hΛ : Submodule.IsLattice E Λ)
    (F : LFlag S r T) (F' : LFlag S r T') (hL : IsLift Λ F) (hL' : IsLift Λ F') : F.fl.X ≤ UUE Λ F F' := by
  exact (Formalism.MainNotions.LatticeGluingRadicals.a_X_le (Formalism.MainNotions.LatticeGluingRadicals.a_HU Λ hΛ F F' hL.2 hL'.2)).1

theorem X'_le_UUE (Λ : Submodule (NumberField.RingOfIntegers E) S.V) (hΛ : Submodule.IsLattice E Λ)
    (F : LFlag S r T) (F' : LFlag S r T') (hL : IsLift Λ F) (hL' : IsLift Λ F') : F'.fl.X ≤ UUE Λ F F' := by
  exact (Formalism.MainNotions.LatticeGluingRadicals.a_X_le (Formalism.MainNotions.LatticeGluingRadicals.a_HU Λ hΛ F F' hL.2 hL'.2)).2

theorem z_mem_UUE (Λ : Submodule (NumberField.RingOfIntegers E) S.V) (hΛ : Submodule.IsLattice E Λ)
    (F : LFlag S r T) (F' : LFlag S r T') (hL : IsLift Λ F) (hL' : IsLift Λ F') : F.fl.z ∈ UUE Λ F F' := by
  rw [← hL.2]
  exact Submodule.subset_span (Submodule.mem_sup_left (Submodule.mem_sup_left
    (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))))

theorem z'_mem_UUE (Λ : Submodule (NumberField.RingOfIntegers E) S.V) (hΛ : Submodule.IsLattice E Λ)
    (F : LFlag S r T) (F' : LFlag S r T') (hL : IsLift Λ F) (hL' : IsLift Λ F') : F'.fl.z ∈ UUE Λ F F' := by
  rw [← hL'.2]
  exact Submodule.subset_span (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))

theorem yv_mem_UUE (Λ : Submodule (NumberField.RingOfIntegers E) S.V) (hΛ : Submodule.IsLattice E Λ)
    (F : LFlag S r T) (F' : LFlag S r T') (hL : IsLift Λ F) (hL' : IsLift Λ F') :
    yv F.fl F'.fl ∈ UUE Λ F F' := by
  have hf : ∀ b, F'.fl.fvec b ∈ UUE Λ F F' := by
    intro b
    refine Fin.lastCases ?_ (fun i => ?_) b
    · rw [Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_last]
      exact z'_mem_UUE Λ hΛ F F' hL hL'
    · rw [Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_castSucc]
      exact X'_le_UUE Λ hΛ F F' hL hL' (Submodule.subset_span ⟨i, rfl⟩)
  unfold yv omp
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.sum_mem _ fun b _ =>
    Submodule.smul_mem _ _ (hf b))) (Submodule.smul_mem _ _ (z_mem_UUE Λ hΛ F F' hL hL'))

theorem hT_Hp_UUE (Λ : Submodule (NumberField.RingOfIntegers E) S.V) (F : LFlag S r T) (F' : LFlag S r T')
    {h v : S.V} (hh : h ∈ Hp Λ F F') (hv : v ∈ UUE Λ F F') : S.hT h v = 0 := by
  rw [hT_swap v h, Formalism.L2.SG.NGCut.CorankRelation.hT_eq_zero_of_mem_Hp Λ F F' hh hv, star_zero]

theorem hT_UUE_Hp (Λ : Submodule (NumberField.RingOfIntegers E) S.V) (F : LFlag S r T) (F' : LFlag S r T')
    {h v : S.V} (hh : h ∈ Hp Λ F F') (hv : v ∈ UUE Λ F F') : S.hT v h = 0 :=
  Formalism.L2.SG.NGCut.CorankRelation.hT_eq_zero_of_mem_Hp Λ F F' hh hv

theorem hT_X_yv (F : FlagG S r T) (F' : FlagG S r T') {x : S.V} (hx : x ∈ F.X) : S.hT x (yv F F') = 0 := by
  have hker : F.X ≤ LinearMap.ker (S.hT (yv F F')) := by
    rw [Formalism.MainNotions.S.FlagG.X, Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, hT_swap]
    have h := brS_yv_e (F := F) (F' := F') a
    rw [Formalism.MainNotions.S.brS] at h
    rw [h, star_zero]
  have h1 : S.hT (yv F F') x = 0 := hker hx
  rw [hT_swap, h1, star_zero]

theorem hT_z_yv (F : FlagG S r T) (F' : FlagG S r T') : S.hT F.z (yv F F') = 0 := by
  have h := pairing_yVector_z (F := F) (F' := F')
  rwa [Formalism.MainNotions.S.brS] at h

theorem UUE_symm (Λ : Submodule (NumberField.RingOfIntegers E) S.V) (F : LFlag S r T) (F' : LFlag S r T') :
    UUE Λ F' F = UUE Λ F F' := by
  unfold Formalism.MainNotions.S.Lat.UUE Formalism.MainNotions.S.Lat.UU
  congr 1
  ac_rfl

theorem Hp_symm (Λ : Submodule (NumberField.RingOfIntegers E) S.V) (F : LFlag S r T) (F' : LFlag S r T') :
    Hp Λ F' F = Hp Λ F F' := by
  unfold Formalism.MainNotions.S.Lat.Hp
  rw [UUE_symm]

theorem line_pair (k : ℕ) (hdim : finrank E S.V = k + 2 * r + 1) (Λ : Submodule (NumberField.RingOfIntegers E) S.V)
    (hΛ : Submodule.IsLattice E Λ) (Fl : LFlag S r T) (F1 F2 : LFlag S r T') (β : S.V ≃ₗ[E] S.V)
    (hL : IsLift Λ Fl) (hL1 : IsLift Λ F1) (hL2 : IsLift Λ F2) (hG1 : Gval Fl F1 ≠ 0) (hG12 : Gval Fl F2 = Gval Fl F1)
    (hT : T ≠ 0) (hTs : star T = T) (hTh : Th Λ Fl F1 F2 β = Hp Λ Fl F1) :
    yv Fl.fl F2.fl - (brS S (yv Fl.fl F2.fl) (yv Fl.fl F1.fl) / brS S (yv Fl.fl F1.fl) (yv Fl.fl F1.fl)) •
        yv Fl.fl F1.fl ∈ Fl.fl.X ∧
      (brS S (yv Fl.fl F2.fl) (yv Fl.fl F1.fl) / brS S (yv Fl.fl F1.fl) (yv Fl.fl F1.fl)) *
        star (brS S (yv Fl.fl F2.fl) (yv Fl.fl F1.fl) / brS S (yv Fl.fl F1.fl) (yv Fl.fl F1.fl)) = 1 := by
  set y1 := yv Fl.fl F1.fl with hy1
  set y2 := yv Fl.fl F2.fl with hy2
  set c := brS S y2 y1 / brS S y1 y1 with hc
  have hG1' : Formalism.MainNotions.S.Gflag Fl.fl F1.fl ≠ 0 := hG1
  have hb1 : brS S y1 y1 ≠ 0 := by
    rw [hy1, brS_yv_yv Fl.fl F1.fl hTs]
    exact mul_ne_zero hT hG1'
  have hb12 : brS S y2 y2 = brS S y1 y1 := by
    rw [hy1, hy2, brS_yv_yv Fl.fl F2.fl hTs, brS_yv_yv Fl.fl F1.fl hTs]
    exact congrArg (T * ·) hG12
  obtain ⟨hfin, hk1⟩ := Formalism.L2.SG.NGCut.CorankRelation.finrank_Hp k hdim Λ hΛ Fl F1 hL hL1 hG1

  have hy2H : ∀ h ∈ Hp Λ Fl F1, S.hT h y2 = 0 := by
    intro h hh
    rw [← hTh] at hh
    unfold Formalism.MainNotions.S.Lat.Th at hh
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hh
    rw [Formalism.L2.SG.NGCut.CorankRelation.mem_ThPairs] at hp
    obtain ⟨-, hp2, hpX, -⟩ := hp
    have e : p.1 = (p.1 - p.2) + p.2 := by abel
    simp only [LinearMap.fst_apply]
    rw [e, map_add, LinearMap.add_apply, hT_X_yv Fl.fl F2.fl hpX,
      hT_Hp_UUE Λ Fl F2 hp2 (yv_mem_UUE Λ hΛ Fl F2 hL hL2), add_zero]
  have hv : y2 - c • y1 ∈ Fl.fl.X := by
    refine Formalism.L2.SG.NGCut.NormalVectorPairings.line Fl.fl hT (Hp Λ Fl F1) ?_ ?_ ?_ ?_ ?_ hb1 ?_ ?_
    · intro x hx h hh
      exact hT_UUE_Hp Λ Fl F1 hh (X_le_UUE Λ hΛ Fl F1 hL hL1 hx)
    · intro h hh
      exact hT_UUE_Hp Λ Fl F1 hh (z_mem_UUE Λ hΛ Fl F1 hL hL1)
    · intro x hx hxH
      exact Formalism.L2.SG.NGCut.CorankRelation.Xsp_Hp_eq_zero Λ hΛ Fl F1 hL hL1 hG1 hx hxH
    · omega
    · rw [Formalism.L2.SG.NGCut.NormalVectorPairings.mem_Qsp]
      exact ⟨fun x hx => hT_X_yv Fl.fl F1.fl hx, hT_z_yv Fl.fl F1.fl,
        fun h hh => hT_Hp_UUE Λ Fl F1 hh (yv_mem_UUE Λ hΛ Fl F1 hL hL1)⟩
    · rw [Formalism.L2.SG.NGCut.NormalVectorPairings.mem_Qsp]
      refine ⟨fun x hx => ?_, ?_, fun h hh => ?_⟩
      · rw [map_sub, map_smul, hT_X_yv Fl.fl F2.fl hx, hT_X_yv Fl.fl F1.fl hx, smul_zero, sub_zero]
      · rw [map_sub, map_smul, hT_z_yv, hT_z_yv, smul_zero, sub_zero]
      · rw [map_sub, map_smul, hy2H h hh, hT_Hp_UUE Λ Fl F1 hh (yv_mem_UUE Λ hΛ Fl F1 hL hL1),
          smul_zero, sub_zero]
    · rw [sub_eq_add_neg, ← neg_smul, brS_add_left, brS_smul_left, hc]
      field_simp
      ring
  refine ⟨hv, ?_⟩

  set x := y2 - c • y1 with hx
  have hy2x : y2 = x + c • y1 := by
    rw [hx]
    abel
  have hxx : brS S x x = 0 := by
    rw [Formalism.MainNotions.S.brS]
    exact hT_X_X Fl.fl hv hv
  have hyx : brS S y1 x = 0 := by
    rw [Formalism.MainNotions.S.brS]
    exact hT_X_yv Fl.fl F1.fl hv
  have hxy : brS S x y1 = 0 := by
    rw [Formalism.MainNotions.S.brS, hT_swap, hT_X_yv Fl.fl F1.fl hv, star_zero]
  have hmod : brS S y2 y2 = c * star c * brS S y1 y1 := by
    rw [hy2x, brS_add_left, brS_add_right, brS_add_right, brS_smul_left, brS_smul_left,
      brS_smul_right, brS_smul_right, hxx, hxy, hyx]
    ring
  rw [hb12] at hmod
  have h1 : (1 : E) * brS S y1 y1 = c * star c * brS S y1 y1 := by rw [one_mul]; exact hmod
  exact (mul_right_cancel₀ hb1 h1).symm

end Formalism.L2.SG.NGCut.NormalVectorPairings
end
end

