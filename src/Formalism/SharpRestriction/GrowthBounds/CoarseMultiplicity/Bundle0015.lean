import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.OtherEFree
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Bundle0014
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Bundle0011
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Bundle0003

-- bundled from Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.GTheta
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.G.GLWeightTheory Formalism.MainNotions.CovariantDegrees

theorem op_single_add {K σ : Type} [Field K] (a : σ) (b : ℕ) (f : σ →₀ ℕ) (ha : a ∉ f.support) (u : MvPolynomial σ K) :
    monomial (Finsupp.single a b + f) (1 : K) * divDer (Finsupp.single a b + f) u =
      cth a b (monomial f (1 : K) * divDer f u) := by
  classical
  ext μ
  rw [eig_one, coeff_cth, eig_one]
  have hd : Disjoint (Finsupp.single a b).support f.support := by
    refine Finset.disjoint_of_subset_left Finsupp.support_single_subset ?_
    rw [Finset.disjoint_singleton_left]
    exact ha
  rw [Finsupp.prod_add_index_of_disjoint hd, Finsupp.prod_single_index (by simp)]
  push_cast
  ring

section GlobalTheory

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero (KK O)] {N r : ℕ} [NeZero r]

theorem op_SSt (D7 : Formalism.BasicNotions.D7) {D : BlockData N} (hT : TieOK D) (ν : BVar N r D.T.t →₀ ℕ) :
    (∀ v ∈ ν.support, OddV D v) → ∀ (thr thr' : Fin D.T.q → WithTop ℤ),
    (∀ k, thr k + (((ν.sum fun _ n => n : ℕ) : ℤ) : WithTop ℤ) ≤ thr' k) →
    ∀ u ∈ SSt O r D thr, monomial ν (1 : KK O) * divDer ν u ∈ SSt O r D thr' := by
  classical
  induction ν using Finsupp.induction with
  | zero =>
    intro _ thr thr' hthr u hu
    rw [divDer_zero]
    have : (monomial (0 : BVar N r D.T.t →₀ ℕ) (1 : KK O)) = 1 := rfl
    rw [this, one_mul]
    exact SSt_mono D (fun k => by simpa using hthr k) hu
  | single_add a b f ha hb ih =>
    intro hv thr thr' hthr u hu
    rw [op_single_add a b f ha]
    have hsum : ((Finsupp.single a b + f).sum fun _ n => n) = b + f.sum fun _ n => n := by
      rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl]
    have hsupp : (Finsupp.single a b + f).support = insert a f.support := by
      rw [Finsupp.support_add_eq, Finsupp.support_single_ne_zero _ hb]
      · rfl
      · rw [Finsupp.support_single_ne_zero _ hb, Finset.disjoint_singleton_left]
        exact ha
    have h1 := ih (fun v hvf => hv v (by rw [hsupp]; exact Finset.mem_insert_of_mem hvf)) thr
      (fun k => thr k + (((f.sum fun _ n => n : ℕ) : ℤ) : WithTop ℤ)) (fun _ => le_rfl) u hu
    refine cth_SSt D7 hT b (fun k => ?_) a (hv a (by rw [hsupp]; exact Finset.mem_insert_self _ _)) h1
    refine le_trans (le_of_eq ?_) (hthr k)
    rw [hsum, add_assoc]
    push_cast
    rw [add_comm ((b : ℕ) : WithTop ℤ)]

end GlobalTheory

theorem tieOK_blockBase (p : ℕ) {r s : ℕ} (S : SegData s) (aTop : Fin s → ℕ) (aPlus : ℕ) (b : SegBlock s r) :
    TieOK (blockBase p S aTop aPlus b) where
  lt := by
    intro i
    have := (uTop S i).2
    show 2 * ((uTop S i : Fin s) : ℕ) + 1 < 2 * s + 1
    omega
  inj := by
    intro i i' h
    have h' : 2 * ((uTop S i : Fin s) : ℕ) = 2 * ((uTop S i' : Fin s) : ℕ) := h
    simp only [uTop] at h'
    exact Fin.ext (by omega)
  sep := by
    intro i i' h
    have h' : 2 * ((uTop S i : Fin s) : ℕ) + 1 = 2 * ((uTop S i' : Fin s) : ℕ) := h
    omega
  uW := by
    intro i
    have := (uTop S i).2
    constructor
    · show 2 * ((uTop S i : Fin s) : ℕ) ≠ 2 * s
      omega
    · show 2 * ((uTop S i : Fin s) : ℕ) + 1 ≠ 2 * s
      omega
  vecE := by
    intro i h
    show decide ((2 * ((uTop S i : Fin s) : ℕ) + 1) % 2 = 0) = false
    simp

theorem thr_shift (x : WithTop ℤ) (mm : ℝ) (n c4 : ℕ) (h : n ≤ c4) :
    x.map (fun y : ℤ => ⌊(y : ℝ) - mm⌋) + ((n : ℤ) : WithTop ℤ) ≤ x.map (fun y : ℤ => ⌊(y : ℝ) - (mm - (c4 : ℝ))⌋) := by
  cases x with
  | top => simp
  | coe y =>
    simp only [WithTop.map_coe]
    have e : (y : ℝ) - (mm - (c4 : ℝ)) = ((y : ℝ) - mm) + (c4 : ℝ) := by ring
    rw [e, Int.floor_add_natCast]
    have : ⌊(y : ℝ) - mm⌋ + (n : ℤ) ≤ ⌊(y : ℝ) - mm⌋ + (c4 : ℤ) := by omega
    exact_mod_cast this

theorem gThetaAt (D7 : Formalism.BasicNotions.D7) : GThetaAt := by
  intro C0 CE1 CE2 X _ O _ _ _ _ j b _ c T q hT mm u hu
  unfold gOp
  refine Submodule.sum_mem _ fun ν hν => Submodule.smul_mem _ _ ?_
  have hTie := tieOK_blockBase X.p (r := X.m) (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) b
  refine op_SSt (O := O) (r := X.m) D7 hTie ν ?_
    (fun k => (segmentCapacities X.p (X.seg C0 CE1 CE2 j) b k).map (fun y : ℤ => ⌊(y : ℝ) - mm⌋))
    (fun k => (segmentCapacities X.p (X.seg C0 CE1 CE2 j) b k).map (fun y : ℤ => ⌊(y : ℝ) - (mm - 4 * (c : ℝ))⌋)) ?_ u hu
  · intro v hv
    have h := (hT ν hν).2 v hv
    rcases v with ⟨a, c'⟩ | ⟨l, s⟩
    · have h' : (a : ℕ) < 2 * segS X.TT j := h
      constructor
      · intro e
        have := congrArg Fin.val e
        simp only [Fin.val_castSucc] at this
        have h2 : ((blockBase X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) b).uPos : ℕ) =
          2 * segS X.TT j := rfl
        omega
      · intro e
        have := congrArg Fin.val e
        simp only [Fin.val_last] at this
        omega
    · have h' : (l : ℕ) < (X.seg C0 CE1 CE2 j).t := h
      intro e
      have := congrArg Fin.val e
      have h2 : ((Fin.last (blockBase X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) b).T.t :
        Fin _) : ℕ) = (X.seg C0 CE1 CE2 j).t := rfl
      omega
  · intro k
    have := thr_shift (segmentCapacities X.p (X.seg C0 CE1 CE2 j) b k) mm (ν.sum fun _ n => n) (4 * c) (hT ν hν).1
    have e : (((4 * c : ℕ) : ℕ) : ℝ) = 4 * (c : ℝ) := by push_cast; ring
    rw [e] at this
    exact this

end Formalism.MainNotions.ColumnSystems.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Loc4ResOfLine
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.LemmaBAlt

def psiRes0 (X : Loc) [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [Algebra (WF X.p X.n') O] (w : O)
    (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')) (a : Fin (X.m + 1)) : O ⧸ Ideal.span {w} :=
  Ideal.Quotient.mk (Ideal.span {w}) (psiO X.p X.n' O 0 (g⁻¹ 0 a))

def ResPowAt : Prop :=
  ∀ (X : Loc) [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF X.p X.n') O] (S : UniformizedDVR X.p O), S.SqP → D1num X →
    ∀ (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')) (a : Fin (X.m + 1)),
      (∀ j : Fin (numSeg X.TT), psiRes X O S.w g j a = psiRes0 X O S.w g a ^ (X.p ^ (segStart X.TT j).val)) ∧
      psiRes0 X O S.w g a ^ (X.p ^ X.n') = psiRes0 X O S.w g a

def ResTelAt : Prop :=
  ∀ (X : Loc) (K : Type) [Field K] (y : K), D1num X → 2 ≤ numSeg X.TT → y ≠ 0 → y ^ (X.p ^ X.n') = y →
    ∏ j : Fin (numSeg X.TT), (y ^ (X.p ^ (segStart X.TT j).val)) ^ (X.p ^ segG X.TT j - 1) = 1

def ResLineAt : Prop :=
  ∀ (X : Loc) [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF X.p X.n') O] (S : UniformizedDVR X.p O), S.SqP → D1num X →
    ∀ (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')), IsGLW g →
      ratPlane X.p X.n' 1 g ≠ ratPlane X.p X.n' 1 1 → psiRes0 X O S.w g 0 ≠ 0 →
      ∃ c : Fin X.m, psiRes0 X O S.w g c.succ ≠ 0

theorem loc4Res_of (hP : ResPowAt) (hT : ResTelAt) (hL : ResLineAt) : LocalResidueBound := by
  intro X _ O _ _ _ _ S hS hD hseg j0 g hg hrat
  haveI : (Ideal.span {S.w}).IsMaximal := by
    rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer S.w).mp S.w_irr]
    exact IsLocalRing.maximalIdeal.isMaximal O
  letI : Field (O ⧸ Ideal.span {S.w}) := Ideal.Quotient.field _
  by_cases h0 : psiRes0 X O S.w g 0 = 0
  · left
    rw [(hP X O S hS hD g 0).1 j0, h0, zero_pow (pow_ne_zero _ (Fact.out : X.p.Prime).ne_zero)]
  · right
    obtain ⟨c, hc⟩ := hL X O S hS hD g hg hrat h0
    refine ⟨c, ?_⟩
    have e0 := (hP X O S hS hD g 0).1
    have ec := (hP X O S hS hD g c.succ).1
    simp only [e0, ec]
    exact (hT X _ _ hD hseg h0 (hP X O S hS hD g 0).2).trans
      (hT X _ _ hD hseg hc (hP X O S hS hD g c.succ).2).symm

theorem resPowAt : ResPowAt := by
  intro X _ O _ _ _ _ S hS hD g a
  have hf : 1 ≤ X.n' := by have := hD.2.2.1; omega
  have hF := frobCong (p := X.p) (f := X.n') hf
  have hp0 : Ideal.Quotient.mk (Ideal.span {S.w}) (X.p : O) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem, ← (show S.w ^ 2 = (X.p : O) from hS), pow_two]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have key : ∀ (s s' : ℤ), s ≤ s' → ∀ β : WF X.p X.n',
      Ideal.Quotient.mk (Ideal.span {S.w}) (algebraMap (WF X.p X.n') O (sigPow X.p X.n' s β)) ^ (X.p ^ (s' - s).toNat) =
        Ideal.Quotient.mk (Ideal.span {S.w}) (algebraMap (WF X.p X.n') O (sigPow X.p X.n' s' β)) := by
    intro s s' hs β
    obtain ⟨τ, hτ⟩ := hF s s' hs β
    have h1 := congrArg (fun z => Ideal.Quotient.mk (Ideal.span {S.w}) (algebraMap (WF X.p X.n') O z)) hτ
    simp only [map_sub, map_pow, map_mul, map_natCast, hp0, zero_mul] at h1
    exact sub_eq_zero.1 h1
  constructor
  · intro j
    have := key 0 ((segStart X.TT j).val : ℤ) (by positivity) (g⁻¹ 0 a)
    simp only [sub_zero, Int.toNat_natCast] at this
    exact this.symm
  · have := key 0 (X.n' : ℤ) (by positivity) (g⁻¹ 0 a)
    simp only [sub_zero, Int.toNat_natCast] at this
    unfold psiRes0
    have e : sigPow X.p X.n' (X.n' : ℤ) = sigPow X.p X.n' 0 := by
      rw [sigPow_mod' X.p X.n' (X.n' : ℤ), Int.emod_self]
    show Ideal.Quotient.mk (Ideal.span {S.w}) (algebraMap (WF X.p X.n') O (sigPow X.p X.n' 0 (g⁻¹ 0 a))) ^ (X.p ^ X.n') =
      Ideal.Quotient.mk (Ideal.span {S.w}) (algebraMap (WF X.p X.n') O (sigPow X.p X.n' 0 (g⁻¹ 0 a)))
    rw [this, e]

theorem resTelAt : ResTelAt := by
  intro X K _ y hD h2 hy hq
  have hn : 0 < X.n' := by have := hD.2.2.1; omega
  have hper : ∀ s, y ^ (X.p ^ (s + X.n')) = y ^ (X.p ^ s) := by
    intro s
    rw [pow_add, pow_mul, ← pow_mul, mul_comm, pow_mul, hq]
  have hmod : ∀ s, y ^ (X.p ^ s) = y ^ (X.p ^ (s % X.n')) := by
    intro s
    conv_lhs => rw [← Nat.mod_add_div s X.n']
    induction s / X.n' with
    | zero => simp
    | succ t ih =>
      rw [Nat.mul_succ, ← add_assoc, hper, ih]
  have hnext : ∀ j : Fin (numSeg X.TT), ((segStart X.TT j).val + segG X.TT j) % X.n' = (segNext X.TT j).val := by
    intro j
    obtain ⟨e1, _⟩ := segG_eq X.TT h2 j
    rw [e1]
    unfold cdist
    have h1 := (segStart X.TT j).isLt
    have h2' := (segNext X.TT j).isLt
    rw [Nat.add_mod_mod]
    have : (segStart X.TT j).val + ((segNext X.TT j).val + X.n' - (segStart X.TT j).val) = (segNext X.TT j).val + X.n' := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt h2']
  set A : Fin (numSeg X.TT) → K := fun j => y ^ (X.p ^ (segStart X.TT j).val) with hA
  have hA0 : ∀ j, A j ≠ 0 := fun j => pow_ne_zero _ hy
  have hP0 : (∏ j, A j) ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => hA0 j
  have hpow : ∀ j, A j ^ (X.p ^ segG X.TT j - 1) * A j = A (rot (numSeg X.TT) j) := by
    intro j
    have hge : 1 ≤ X.p ^ segG X.TT j := Nat.one_le_pow _ _ hD.1.pos
    rw [← pow_succ, Nat.sub_add_cancel hge]
    show (y ^ (X.p ^ (segStart X.TT j).val)) ^ (X.p ^ segG X.TT j) = y ^ (X.p ^ (segStart X.TT (rot _ j)).val)
    rw [← pow_mul, ← pow_add, hmod, hnext j, next_eq]
  have hprod : (∏ j, A j ^ (X.p ^ segG X.TT j - 1)) * ∏ j, A j = ∏ j, A j := by
    rw [← Finset.prod_mul_distrib, Finset.prod_congr rfl fun j _ => hpow j]
    exact (rot_bij (numSeg X.TT)).prod_comp A
  exact mul_right_cancel₀ hP0 (by rw [hprod, one_mul])

theorem loc4Res_of_line (hL : ResLineAt) : LocalResidueBound :=
  loc4Res_of resPowAt resTelAt hL

end Formalism.MainNotions.ColumnSystems.Pf
end
end

