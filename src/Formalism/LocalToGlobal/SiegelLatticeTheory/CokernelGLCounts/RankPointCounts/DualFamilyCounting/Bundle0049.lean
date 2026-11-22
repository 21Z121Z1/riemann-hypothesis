import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.CovolBRb
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.TrDetPfH
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0048
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ReImESymmAdd
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0045
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.TermTiesEmptyOfLargeIndex
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0019
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0018
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle0005
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle0017

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.CovolBRc
section
namespace Formalism.L2.SG.Pf.NcReal.JX.CovB

theorem trDetUnimod_holds : TrDetUnimod := TrD.trDetUnimod_of TrD.detHOne_holds

theorem rowBlockCovol_holds : RowBlockCovol := rowBlockCovol_of trDetUnimod_holds

theorem blockCovol_holds : BlockCovol := blockCovol_of rowBlockCovol_holds

end Formalism.L2.SG.Pf.NcReal.JX.CovB
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.InvMulOfUnitri
section
noncomputable section

open NumberField Formalism.BasicNotions Matrix
open scoped BigOperators

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf.Ex

open Formalism.L2.SG.HidaSetting Formalism.MainNotions.S Formalism.L2.SG.Pf.NcReal.JX.NOf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D)

theorem inv_mul_of_unitri {X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E}
    (h0 : ∀ b a : Fin D.R.rS, a < b → X0 b a = 0) (h1 : ∀ a, X0 a a = 1) : X0⁻¹ * X0 = 1 := by
  have hdet : X0.det = 1 := by
    rw [Matrix.det_of_upperTriangular (fun i j hij => h0 i j hij)]
    simp [h1]
  exact Matrix.nonsing_inv_mul X0 (by rw [hdet]; exact isUnit_one)

theorem inW_sub {x y : (VS D).V} (hx : InW X x) (hy : InW X y) : InW X (x - y) := by
  intro c
  rw [map_sub, map_sub, (hx c).1, (hy c).1, (hx c).2, (hy c).2, sub_self]
  exact ⟨rfl, rfl⟩

theorem h_pW_left (y : (VS D).V) {w : (VS D).V} (hw : InW X w) : (VS D).hT y w = (VS D).hT (pW X y) w := by
  conv_lhs => rw [decomp X y]
  rw [LinearMap.map_add₂, LinearMap.map_add₂, h_sum_left, h_sum_left]
  simp [(hw _).1, (hw _).2]

theorem dictEx_holds : DictEx := by
  intro D X u X0 xs M hD
  obtain ⟨h0, h1, hxs, hM⟩ := hD
  have hinv := inv_mul_of_unitri h0 h1
  set n := nEq X X0 xs M hinv hxs hM with hn
  have hnx : ∀ y, n y = nL X X0 xs M y := fun y => rfl
  have hFe : (X.Fu u).e = X.eX := X.Fu_e u
  refine ⟨n, ⟨fun x y => ?_, fun j x hx => ?_, fun x hx => ?_⟩, ?_, ?_, ?_⟩
  ·
    show (VS D).hT (n x) (n y) = (VS D).hT x y
    rw [hnx, hnx]
    exact nL_isom X X0 xs M hinv hxs hM x y
  ·
    show n x - x ∈ (X.Fu u).Xa j
    have hx' : x ∈ (X.Fu u).Xa (j + 1) := hx
    unfold FlagG.Xa at hx' ⊢
    rw [hFe] at hx' ⊢
    refine Submodule.span_induction (p := fun x _ => n x - x ∈ Submodule.span D.host.E (X.eX '' {i | i.1 < j}))
      ?_ ?_ ?_ ?_ hx'
    · rintro _ ⟨i, hi, rfl⟩
      rw [hnx, nL_e]
      unfold nE
      have e1 : ∑ b, X0 b i • X.eX b - X.eX i = ∑ b, (X0 b i - if b = i then 1 else 0) • X.eX b := by
        simp [sub_smul, Finset.sum_sub_distrib, ite_smul]
      rw [e1]
      refine Submodule.sum_mem _ fun b _ => ?_
      by_cases hb : (b : ℕ) < j
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, hb, rfl⟩)
      · have hbi : i ≤ b := by
          have : (i : ℕ) < j + 1 := hi
          exact Fin.le_def.2 (by omega)
        rcases hbi.lt_or_eq with hlt | heq
        · rw [h0 b i hlt, if_neg (ne_of_gt hlt), sub_zero, zero_smul]
          exact Submodule.zero_mem _
        · subst heq
          rw [h1, if_pos rfl, sub_self, zero_smul]
          exact Submodule.zero_mem _
    · simp
    · intro a b _ _ ha hb
      rw [map_add, add_sub_add_comm]
      exact Submodule.add_mem _ ha hb
    · intro c a _ ha
      rw [map_smul, ← smul_sub]
      exact Submodule.smul_mem _ _ ha
  ·
    show n x - x ∈ (X.Fu u).X
    have horth : ∀ c, (VS D).hT (X.eX c) x = 0 := by
      intro c
      have hxo : x ∈ Lat.orth (VS D) (X.Fu u).X := hx
      unfold Lat.orth at hxo
      have := (Submodule.mem_iInf _).1 hxo (X.eX c)
      rw [Submodule.mem_iInf] at this
      have hmem : X.eX c ∈ (X.Fu u).X := by
        unfold FlagG.X
        rw [hFe]
        exact Submodule.subset_span ⟨c, rfl⟩
      exact LinearMap.mem_ker.1 (this hmem)
    unfold FlagG.X
    rw [hFe]
    have hdec := decomp X x
    simp only [horth, zero_smul, Finset.sum_const_zero, add_zero] at hdec
    have e1 : n x - x = ∑ c, (VS D).hT (X.fY c) x • (nE X X0 c - X.eX c) +
        ∑ b, (VS D).hT (xs b) (pW X x) • X.eX b := by
      calc n x - x = (∑ c, (VS D).hT (X.fY c) x • nE X X0 c +
            (pW X x + ∑ b, (VS D).hT (xs b) (pW X x) • X.eX b)) -
            (∑ c, (VS D).hT (X.fY c) x • X.eX c + pW X x) := by
            rw [← hdec, hnx, nL_apply]
            simp only [horth, zero_smul, Finset.sum_const_zero, add_zero]
        _ = _ := by
            simp only [smul_sub, Finset.sum_sub_distrib]
            abel
    rw [e1]
    refine Submodule.add_mem _ (Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ ?_)
      (Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩))
    unfold nE
    exact Submodule.sub_mem _ (Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩))
      (Submodule.subset_span ⟨c, rfl⟩)
  ·
    funext b a
    show (VS D).hT (X.fY b) (n (X.eX a)) = X0 b a
    rw [hnx, nL_e]
    unfold nE
    rw [h_sum_right]
    simp [h_fe, Finset.sum_ite_eq]
  ·
    funext b
    set y := n.symm (X.fY b) with hy
    have hny : n y = X.fY b := n.apply_symm_apply _
    have hd : InW X (pW X y - xs b) := inW_sub X (inW_pW X y) (hxs b)
    have hw0 : ∀ w, InW X w → (VS D).hT (pW X y - xs b) w = 0 := by
      intro w hw
      rw [LinearMap.map_sub₂, ← h_pW_left X y hw]
      have : (VS D).hT y w = (VS D).hT (n y) (n w) := (nL_isom X X0 xs M hinv hxs hM y w).symm
      rw [this, hny, hnx, h_f_nLw X X0 xs M hxs hw, sub_self]
    show pW X y = xs b
    rw [← sub_eq_zero]
    refine (VS D).nondeg.1 _ fun v => ?_
    conv_lhs => rw [decomp X v]
    rw [map_add, map_add, h_sum_right, h_sum_right, hw0 _ (inW_pW X v)]
    simp [(inW_left X (inW_pW X y) _).1, (inW_left X (inW_pW X y) _).2, (inW_left X (hxs b) _).1,
      (inW_left X (hxs b) _).2]
  ·
    have hA : Aq X n = X0 * M := by
      funext b a
      show (VS D).hT (X.fY b) (n (X.fY a)) = (X0 * M) b a
      rw [hnx, nL_f, h_f_nF X X0 xs M hxs]
    show (Xq X n)⁻¹ * Aq X n = M
    have hXq : Xq X n = X0 := by
      funext b a
      show (VS D).hT (X.fY b) (n (X.eX a)) = X0 b a
      rw [hnx, nL_e]
      unfold nE
      rw [h_sum_right]
      simp [h_fe, Finset.sum_ite_eq]
    rw [hXq, hA, ← Matrix.mul_assoc, hinv, Matrix.one_mul]

end Formalism.L2.SG.Pf.NcReal.JX.NOf.Ex
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.MemClRow
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Matrix

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.S Formalism.L2.SG.Pf.NcReal.JX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem mem_cl_row (b : Fin D.R.rS) (x : InfinitePlace X.B.I.F → Fin (D.R.k + 1) → ℂ) :
    x ∈ cLat X u (Sum.inl (Sum.inr b)) ↔ ∃ y ∈ aaLb X b, rowV X u y = x := by
  let f : (VS D).V →+ (InfinitePlace X.B.I.F → Fin (D.R.k + 1) → ℂ) :=
    AddMonoidHom.mk' (rowV X u) (fun x y => rowV_add (X := X) (u := u) x y)
  let S : AddSubgroup (VS D).V := (Submodule.span (𝓞 D.host.E)
    {y | ∃ c ∈ (aaD D b : Set D.host.E), ∃ l ∈ X.Lb, y = c • l}).toAddSubgroup
  have hc : cLat X u (Sum.inl (Sum.inr b)) = S.map f := AddSubgroup.closure_eq (S.map f)
  have key : x ∈ cLat X u (Sum.inl (Sum.inr b)) ↔ x ∈ S.map f := by
    rw [hc]; exact Iff.rfl
  exact key.trans AddSubgroup.mem_map

def imSub (a : Fin D.R.rS) : AddSubgroup D.host.E where
  carrier := {t | t ∈ ((aaD D a * aaD D a : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Set D.host.E) ∧
    D.host.conj t = -t}
  add_mem' := fun {s t} hs ht => ⟨Submodule.add_mem _ hs.1 ht.1, by rw [map_add, hs.2, ht.2, neg_add]⟩
  zero_mem' := ⟨Submodule.zero_mem _, by rw [map_zero, neg_zero]⟩
  neg_mem' := fun {t} ht => ⟨Submodule.neg_mem _ ht.1, by rw [map_neg, ht.2]⟩

def imHom : D.host.E →+ (InfinitePlace X.B.I.F → ℝ) where
  toFun t := fun v => (embS D (X.pl v) t).im
  map_zero' := by funext v; simp
  map_add' s t := by funext v; simp

theorem mem_cl_im (a : Fin D.R.rS) (x : InfinitePlace X.B.I.F → ℝ) :
    x ∈ cLat X u (Sum.inr (Sum.inr a)) ↔
      ∃ t : D.host.E, t ∈ aaD D a * aaD D a ∧ D.host.conj t = -t ∧ (fun v => (embS D (X.pl v) t).im) = x := by
  have hc : cLat X u (Sum.inr (Sum.inr a)) = (imSub a).map (imHom X) :=
    AddSubgroup.closure_eq ((imSub a).map (imHom X))
  have key : x ∈ cLat X u (Sum.inr (Sum.inr a)) ↔ x ∈ (imSub a).map (imHom X) := by
    rw [hc]; exact Iff.rfl
  refine key.trans (AddSubgroup.mem_map.trans ?_)
  constructor
  · rintro ⟨t, ⟨h1, h2⟩, rfl⟩
    exact ⟨t, h1, h2, rfl⟩
  · rintro ⟨t, h1, h2, rfl⟩
    exact ⟨t, ⟨h1, h2⟩, rfl⟩

theorem im_inj {t t' : D.host.E} (ht : D.host.conj t = -t) (ht' : D.host.conj t' = -t')
    (h : ∀ v : InfinitePlace X.B.I.F, (embS D (X.pl v) t).im = (embS D (X.pl v) t').im) : t = t' := by
  obtain ⟨v⟩ := (inferInstance : Nonempty (InfinitePlace X.B.I.F))
  have hs : D.host.conj (t - t') = -(t - t') := by rw [map_sub, ht, ht']; ring
  have h1 := CovB.embS_conj (D := D) (X.pl v) (t - t')
  rw [hs, map_neg] at h1
  have him : (embS D (X.pl v) (t - t')).im = 0 := by rw [map_sub, Complex.sub_im, h v, sub_self]
  have hre : (embS D (X.pl v) (t - t')).re = 0 := by
    have h2 := congrArg Complex.re h1
    simp only [Complex.neg_re, Complex.conj_re] at h2
    linarith
  have h0 : embS D (X.pl v) (t - t') = 0 := Complex.ext hre him
  exact sub_eq_zero.mp ((map_eq_zero_iff _ (RingHom.injective _)).mp h0)

theorem aaLb_inW {b : Fin D.R.rS} {y : (VS D).V} (hy : y ∈ aaLb X b) : InW X y := by
  have hL : ∀ l ∈ X.Lb, InW X l := by
    intro l hl
    have hp := Alg.pW_inW (X := X) l
    have he : pW X l = l := by
      have h1 := Level.prV_Lb (X := X) l hl
      rw [Level.prV_apply] at h1
      simpa only [pW] using h1
    rwa [he] at hp
  simp only [aaLb, SetLike.mem_coe] at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, -, l, hl, rfl⟩ := hx
    intro d
    exact ⟨by rw [map_smul, ((hL l hl) d).1, smul_zero], by rw [map_smul, ((hL l hl) d).2, smul_zero]⟩
  | zero => intro d; exact ⟨map_zero _, map_zero _⟩
  | add x z _ _ hx hz =>
    intro d
    exact ⟨by rw [map_add, (hx d).1, (hz d).1, add_zero], by rw [map_add, (hx d).2, (hz d).2, add_zero]⟩
  | smul o x _ hx =>
    intro d
    refine ⟨?_, ?_⟩
    · rw [← algebraMap_smul D.host.E o x, map_smul, (hx d).1, smul_zero]
    · rw [← algebraMap_smul D.host.E o x, map_smul, (hx d).2, smul_zero]

end Formalism.L2.SG.Pf.NcReal.JX.NOf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NOfibOnto
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Matrix

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.S Formalism.L2.SG.Pf.NcReal.JX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Onto

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem hc_congr (x y : BV X) (hX : ∀ p, x (Sum.inl (Sum.inl p)) = y (Sum.inl (Sum.inl p)))
    (hR : ∀ b, x (Sum.inl (Sum.inr b)) = y (Sum.inl (Sum.inr b))) : Hc X u x = Hc X u y := by
  funext v
  have h1 : Xc X x v = Xc X y v := by
    ext b a
    simp only [Xc, hX]
  have h2 : Gc X u x v = Gc X u y v := by
    ext b c
    simp only [Gc, hR]
  simp only [Hc, h1, h2]

theorem aaLb_inW {b : Fin D.R.rS} {y : (VS D).V} (hy : y ∈ aaLb X b) : InW X y := by
  rw [aaLb, SetLike.mem_coe] at hy
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨c, -, l, hl, rfl⟩ := hz
    intro a
    obtain ⟨h1, h2⟩ := X.Lb_perp l hl a
    simp only [map_smul, h1, h2, smul_zero, and_self]
  | zero =>
    intro a
    simp only [map_zero, and_self]
  | add z w _ _ hz hw =>
    intro a
    simp only [map_add, (hz a).1, (hz a).2, (hw a).1, (hw a).2, add_zero, and_self]
  | smul r z _ hz =>
    intro a
    simp only [LinearMap.map_smul_of_tower, (hz a).1, (hz a).2, smul_zero, and_self]

theorem mem_cl_row (b : Fin D.R.rS) (z : InfinitePlace X.B.I.F → Fin (D.R.k + 1) → ℂ) :
    z ∈ AddSubgroup.closure (rowV X u '' aaLb X b) ↔ ∃ y ∈ aaLb X b, rowV X u y = z := by
  exact mem_closure_image (rowHom X u)
    (Submodule.span (𝓞 D.host.E) {y | ∃ c ∈ (aaD D b : Set D.host.E), ∃ l ∈ X.Lb, y = c • l}).toAddSubgroup z

def imH (a : Fin D.R.rS) : AddSubgroup D.host.E where
  carrier := {t | t ∈ ((aaD D a * aaD D a : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
      Set D.host.E) ∧ D.host.conj t = -t}
  zero_mem' := ⟨Submodule.zero_mem _, by simp⟩
  add_mem' := by
    rintro s t ⟨hs1, hs2⟩ ⟨ht1, ht2⟩
    exact ⟨Submodule.add_mem _ hs1 ht1, by rw [map_add, hs2, ht2, neg_add]⟩
  neg_mem' := by
    rintro s ⟨hs1, hs2⟩
    exact ⟨Submodule.neg_mem _ hs1, by rw [map_neg, hs2]⟩

def imHom : D.host.E →+ (InfinitePlace X.B.I.F → ℝ) where
  toFun t := fun v => (embS D (X.pl v) t).im
  map_zero' := by funext v; simp
  map_add' s t := by funext v; simp

theorem mem_cl_im (a : Fin D.R.rS) (z : InfinitePlace X.B.I.F → ℝ) :
    z ∈ cLat X u (Sum.inr (Sum.inr a)) ↔ ∃ t ∈ imH a, imHom X t = z := by
  exact mem_closure_image (imHom X) (imH a) z

end Onto

open Onto in

theorem fibOnto_holds : FibOnto := by
  intro D X u x hx
  have hA : ∀ p : LsNc5.LtPair D.R.rS, ∃ t ∈ aaD D p.1.1 * (aaD D p.1.2)⁻¹,
      embV X t = x (Sum.inl (Sum.inl p)) := by
    intro p
    have h := hx (Sum.inl (Sum.inl p))
    simp only [tauQ, sub_zero] at h
    exact (mem_cl_emb X _ _).1 h
  have hB : ∀ b : Fin D.R.rS, ∃ y ∈ aaLb X b, rowV X u y = x (Sum.inl (Sum.inr b)) := by
    intro b
    have h := hx (Sum.inl (Sum.inr b))
    simp only [tauQ, sub_zero] at h
    exact (mem_cl_row X u b _).1 h
  have hC : ∀ p : LsNc5.LtPair D.R.rS, ∃ s ∈ aaD D p.1.1 * aaD D p.1.2,
      embV X s = fun v => x (Sum.inr (Sum.inl p)) v - Hc X u x v p.1.1 p.1.2 / 2 :=
    fun p => (mem_cl_emb X _ _).1 (hx (Sum.inr (Sum.inl p)))
  have hD : ∀ a : Fin D.R.rS, ∃ t ∈ imH a, imHom X t =
      fun v => x (Sum.inr (Sum.inr a)) v - -((Hc X u x v a a).re * (embS D (X.pl v) (theta D)).im) :=
    fun a => (mem_cl_im X u a _).1 (hx (Sum.inr (Sum.inr a)))
  choose tA htA htA' using hA
  choose xs hxs hxs' using hB
  choose sC hsC hsC' using hC
  choose tD htD htD' using hD
  obtain ⟨X0, hX0⟩ : ∃ X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E,
      X0 = fun b a => if h : b < a then tA ⟨(b, a), h⟩ else if b = a then 1 else 0 := ⟨_, rfl⟩
  have hup : ∀ b a : Fin D.R.rS, a < b → X0 b a = 0 := by
    intro b a h
    simp [hX0, not_lt_of_gt h, ne_of_gt h]
  have hdg : ∀ a, X0 a a = 1 := by
    intro a
    simp [hX0]
  have hX0p : ∀ p : LsNc5.LtPair D.R.rS, X0 p.1.1 p.1.2 = tA p := by
    intro p
    simp [hX0, p.2]
  have hW : ∀ b, InW X (xs b) := fun b => aaLb_inW X (hxs b)
  have hGh : ∀ i j, star (Gp D X0 xs j i) = Gp D X0 xs i j := by
    intro i j
    have := congrFun (congrFun (Gp_herm X0 xs) i) j
    rwa [Matrix.conjTranspose_apply] at this
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E,
      M = fun b a => if h : b < a then sC ⟨(b, a), h⟩
        else if h' : a < b then -Gp D X0 xs b a - star (sC ⟨(a, b), h'⟩)
        else tD a - Gp D X0 xs a a * theta D := ⟨_, rfl⟩
  have hMlt : ∀ p : LsNc5.LtPair D.R.rS, M p.1.1 p.1.2 = sC p := by
    intro p
    simp [hM, p.2]
  have hMgt : ∀ p : LsNc5.LtPair D.R.rS,
      M p.1.2 p.1.1 = -Gp D X0 xs p.1.2 p.1.1 - star (sC p) := by
    intro p
    simp [hM, p.2, not_lt_of_gt p.2]
  have hMd : ∀ a, M a a = tD a - Gp D X0 xs a a * theta D := by
    intro a
    simp [hM]
  have hth : star (theta D) = 1 - theta D := by
    rw [Inh.tie_star]
    exact eq_sub_of_add_eq' (theta_spec D).2
  have hData : DataOK X X0 xs M := by
    refine ⟨hup, hdg, hW, ?_⟩
    ext i j
    simp only [Matrix.add_apply, Matrix.conjTranspose_apply, Matrix.neg_apply]
    rcases lt_trichotomy i j with h | rfl | h
    · rw [hMlt ⟨(i, j), h⟩, hMgt ⟨(i, j), h⟩, star_sub, star_neg, star_star, hGh]
      ring
    · obtain ⟨-, hc⟩ := htD i
      rw [hMd, star_sub, star_mul', Inh.tie_star D (tD i), hc, hth, hGh]
      ring
    · rw [hMlt ⟨(j, i), h⟩, hMgt ⟨(j, i), h⟩]
      ring
  have hXb : ∀ p, x (Sum.inl (Sum.inl p)) = blkQ X u X0 xs M (Sum.inl (Sum.inl p)) := by
    intro p
    show _ = embV X (X0 p.1.1 p.1.2)
    rw [hX0p]
    exact (htA' p).symm
  have hRb : ∀ b, x (Sum.inl (Sum.inr b)) = blkQ X u X0 xs M (Sum.inl (Sum.inr b)) := by
    intro b
    exact (hxs' b).symm
  have hHc : ∀ v, Hc X u x v = (Gp D X0 xs).map (embS D (X.pl v)) := by
    intro v
    rw [hc_congr X u x _ hXb hRb]
    exact Hc_blkQ X u X0 xs M hup hdg hW v
  refine ⟨X0, xs, M, hData, ?_⟩
  funext p
  rcases p with ((p | b) | (p | a))
  · exact (hXb p).symm
  · exact (hRb b).symm
  · funext v
    show (embS D (X.pl v) (M p.1.1 p.1.2) - star (embS D (X.pl v) (M p.1.2 p.1.1))) / 2 = _
    have hs := congrFun (hsC' p) v
    simp only [embV, hHc v, Matrix.map_apply] at hs
    have e1 : star (embS D (X.pl v) (M p.1.2 p.1.1)) =
        -embS D (X.pl v) (Gp D X0 xs p.1.1 p.1.2) - embS D (X.pl v) (sC p) := by
      rw [hMgt, ← emb_star X, star_sub, star_neg, star_star, hGh, map_sub, map_neg]
    rw [e1, hMlt]
    linear_combination hs
  · funext v
    show (embS D (X.pl v) (M a a)).im = _
    have hs := congrFun (htD' a) v
    simp only [imHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, hHc v, Matrix.map_apply] at hs
    have hr : (embS D (X.pl v) (Gp D X0 xs a a)).im = 0 := by
      have := congrArg (embS D (X.pl v)) (hGh a a)
      rw [emb_star X] at this
      exact Complex.conj_eq_iff_im.mp this
    rw [hMd, map_sub, map_mul, Complex.sub_im, Complex.mul_im, hr]
    linear_combination hs

end Formalism.L2.SG.Pf.NcReal.JX.NOf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.OrbitFinR
section
open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def CntIsoInv : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hβ : β ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) {T : D.host.E}
    (T' : D.host.E) (F0 : FlagG (VS D) D.R.rS T) (Λ : Submodule (𝓞 D.host.E) (VS D).V) (Z : MatZ D),
    cntE T' (Formalism.L2.SG.Saturated.mapFlag β hβ F0) (Formalism.HermitianLatticesTheory.gmap β Λ) Z = cntE T' F0 Λ Z

theorem orbitFiniteR_of (hI : CntIsoInv) : OrbitFiniteR := by
  intro D δ M hA L u u' hT F0 what₂ hR Z Λ hΛ
  have hT0 : (((D.mem u).A.T : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (D.mem u).A.T_prime.ne_zero
  obtain ⟨β, hβ, he, hz⟩ := Formalism.L2.SG.Pf.WittFlags.flag_witt hT0 rfl F0 (Formalism.MainNotions.S.Inh.tie_flag0 D u)
  have hR' := Formalism.L2.SG.Pf.WittFlags.RowRepsIso_holds D β hβ F0 what₂ hR
  have hF1e : (Formalism.L2.SG.Saturated.mapFlag β hβ F0).e = D.sp.hypE := by
    funext a
    show β (F0.e a) = _
    rw [he a]
    rfl
  have hF1z : (Formalism.L2.SG.Saturated.mapFlag β hβ F0).z = D.zmOf u := by
    show β F0.z = _
    rw [hz]
    rfl
  have hRO : RowsOf u (Formalism.L2.SG.Saturated.mapFlag β hβ F0) (what₂.image (Formalism.HermitianLatticesTheory.gmap β)) :=
    ⟨hF1e, hF1z, hR', ⟨_, Finset.mem_image_of_mem _ hΛ⟩⟩
  have h := PI.UnitaryGroupMassFormula.CntFormula.orbitFinite_of PI.UnitaryGroupMassFormula.CntFormula.unipotent_integral_isGroup PI.UnitaryGroupMassFormula.CntFormula.orbit_representatives
    D δ M hA L u u' hT _ _ hRO Z (Formalism.HermitianLatticesTheory.gmap β Λ) (Finset.mem_image_of_mem _ hΛ)
  rwa [hI D β hβ (Tn u') F0 Λ Z] at h

end Formalism.L2.SG.Pf.Cnt
end
end

