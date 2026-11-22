import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0070
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.TauExists

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MemDdPowMulQd
section
noncomputable section

open scoped Classical

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.PairVal Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.PtCell Formalism.L2.SG.RealObj
  Formalism.L2.SG.Pf.BlockPermutation Formalism.L2.SG.Pf.StabIntSh

namespace Formalism.L2.SG.Pf.StabIntLat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem ddS_ne : ddS D ≠ 0 := by
  intro h
  apply shapeNZ.1 1
  unfold ddPow; rw [h]; simp

theorem ddPow_mul (i j : ℕ) : ddPow D i * ddPow D j = ddPow D (i + j) := by
  unfold ddPow
  rw [← zpow_add₀ ddS_ne]
  congr 1; push_cast; ring

theorem mem_ddPow_mul {i j : ℕ} {x y : D.host.E} (hx : x ∈ ddPow D i) (hy : y ∈ ddPow D j) :
    x * y ∈ ddPow D (i + j) := by
  rw [← ddPow_mul]; exact FractionalIdeal.mul_mem_mul hx hy

theorem mem_qdPow_mul {i j : ℕ} {x y : D.host.E} (hx : x ∈ qdPow D i) (hy : y ∈ ddPow D j) :
    x * y ∈ qdPow D (i + j) := by
  have := FractionalIdeal.mul_mem_mul hx hy
  unfold qdPow at this ⊢
  rwa [mul_assoc, ddPow_mul] at this

theorem mem_ddPow_mul_qd {i j : ℕ} {x y : D.host.E} (hx : x ∈ ddPow D i) (hy : y ∈ qdPow D j) :
    x * y ∈ qdPow D (i + j) := by
  rw [mul_comm, add_comm]; exact mem_qdPow_mul hy hx

theorem one_mem_ddPow0 : (1 : D.host.E) ∈ ddPow D 0 := by
  unfold ddPow; simp only [CharP.cast_eq_zero, neg_zero, zpow_zero]
  exact (FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩

theorem qd_le_dd (h : ℕ) {x : D.host.E} (hx : x ∈ qdPow D h) : x ∈ ddPow D h := by
  rw [qdPow_mem_iff] at hx
  have h2 : ((gS D : ℕ) : D.host.E) ∈ ddPow D 0 := by
    unfold ddPow; simp only [CharP.cast_eq_zero, neg_zero, zpow_zero]
    exact (FractionalIdeal.mem_one_iff _).2 ⟨(gS D : ℕ), map_natCast _ _⟩
  have := mem_ddPow_mul h2 hx
  rwa [zero_add, mul_div_cancel₀ _ gS_ne] at this

def GrD (M : MatR D) : Prop := ∀ a c : Fin (D.R.rS + 1), a ≤ c → M a c ∈ ddPow D (c.val - a.val)

theorem grD_inv {X : MatR D} (hX : UpU X) (hG : GrD X) : GrD X⁻¹ := by
  have hXi := upU_inv hX
  have hd : IsUnit X.det := by rw [upU_det hX]; exact isUnit_one
  have key : ∀ n : ℕ, ∀ a c : Fin (D.R.rS + 1), a ≤ c → c.val - a.val = n → X⁻¹ a c ∈ ddPow D n := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro a c hac hn
      rcases eq_or_lt_of_le hac with h | h
      · subst h; rw [(hXi a a).2 rfl]; simp only [Nat.sub_self] at hn; subst hn; exact one_mem_ddPow0
      ·
        have h1 := congrFun (congrFun (Matrix.mul_nonsing_inv X hd) a) c
        rw [Matrix.mul_apply, Matrix.one_apply_ne (ne_of_lt h), ← Finset.add_sum_erase _ _ (Finset.mem_univ a),
          (hX a a).2 rfl, one_mul] at h1
        have h2 : X⁻¹ a c = -∑ i ∈ Finset.univ.erase a, X a i * X⁻¹ i c := by
          rw [eq_neg_iff_add_eq_zero]; exact h1
        rw [h2]
        refine (ddPow D n : Submodule (𝓞 D.host.E) D.host.E).neg_mem (Submodule.sum_mem _ fun i hi => ?_)
        have hia : i ≠ a := Finset.ne_of_mem_erase hi
        by_cases hai : a < i
        · by_cases hic : i ≤ c
          · have hlt : c.val - i.val < n := by have : a.val < i.val := hai; omega
            have e : n = (i.val - a.val) + (c.val - i.val) := by have : a.val < i.val := hai; omega
            rw [e]
            exact mem_ddPow_mul (hG a i (le_of_lt hai)) (ih _ hlt i c hic rfl)
          · rw [(hXi i c).1 (lt_of_not_ge hic), mul_zero]; exact FractionalIdeal.zero_mem _
        · rw [(hX a i).1 (lt_of_le_of_ne (not_lt.1 hai) hia), zero_mul]; exact FractionalIdeal.zero_mem _
  intro a c hac
  exact key _ a c hac rfl

theorem inv_diff {X X' : MatR D} (hX : UpU X) (hX' : UpU X') {a c : Fin (D.R.rS + 1)} (hac : a < c)
    (hag : ∀ i j : Fin (D.R.rS + 1), i < j → j.val - i.val < c.val - a.val → X i j = X' i j) :
    X⁻¹ a c - X'⁻¹ a c = X' a c - X a c := by
  have hd : IsUnit X.det := by rw [upU_det hX]; exact isUnit_one
  have hd' : IsUnit X'.det := by rw [upU_det hX']; exact isUnit_one
  have hXi := upU_inv hX
  have hXi' := upU_inv hX'
  have hm : X⁻¹ - X'⁻¹ = X⁻¹ * (X' - X) * X'⁻¹ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.nonsing_inv_mul _ hd, Matrix.one_mul, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hd', Matrix.mul_one]
  have e := congrFun (congrFun hm a) c
  rw [Matrix.sub_apply] at e
  rw [e, Matrix.mul_apply, Finset.sum_eq_single c]
  · rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [(hXi a a).2 rfl, (hXi' c c).2 rfl, one_mul, mul_one, Matrix.sub_apply]
    · intro i _ hia
      by_cases hai : a < i
      · rw [Matrix.sub_apply]
        by_cases hic : i < c
        · rw [hag i c hic (by have : a.val < i.val := hai; have : i.val < c.val := hic; omega), sub_self, mul_zero]
        · rcases eq_or_lt_of_le (not_lt.1 hic) with h | h
          · rw [h, (hX' i i).2 rfl, (hX i i).2 rfl, sub_self, mul_zero]
          · rw [(hX' i c).1 h, (hX i c).1 h, sub_self, mul_zero]
      · rw [(hXi a i).1 (lt_of_le_of_ne (not_lt.1 hai) hia), zero_mul]
    · simp
  · intro j _ hjc
    by_cases hjc' : j < c
    · rw [Matrix.mul_apply]
      refine mul_eq_zero_of_left (Finset.sum_eq_zero fun i _ => ?_) _
      by_cases hai : a ≤ i
      · rw [Matrix.sub_apply]
        by_cases hij : i < j
        · rw [hag i j hij (by have : a.val ≤ i.val := hai; have : j.val < c.val := hjc'; omega), sub_self, mul_zero]
        · rcases eq_or_lt_of_le (not_lt.1 hij) with h | h
          · rw [h, (hX' i i).2 rfl, (hX i i).2 rfl, sub_self, mul_zero]
          · rw [(hX' i j).1 h, (hX i j).1 h, sub_self, mul_zero]
      · rw [(hXi a i).1 (lt_of_not_ge hai), zero_mul]
    · rw [(hXi' j c).1 (lt_of_le_of_ne (not_lt.1 hjc') (Ne.symm hjc)), mul_zero]
  · simp

variable (w : Point D.host.E (D.R.rS + 1))

theorem Xmat_upU (y : FreeE w → D.host.E) : UpU (Xmat w y) := by
  intro a c
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simp only [Xmat, ne_of_gt h, if_false]
    rw [dif_neg (fun h' => absurd h'.1 (not_lt.2 (le_of_lt h)))]
  · simp [Xmat, h]

theorem Xmat_blk (y : FreeE w → D.host.E) : IsBlockDiagonalMatrix w (Xmat w y) := by
  intro a c hne
  have hac : a ≠ c := fun e => hne (by rw [e])
  simp only [Xmat, hac, if_false]
  rw [dif_neg (fun h' => hne h'.2)]

theorem Xmat_q (y : FreeE w → D.host.E) (q : FreeE w) : Xmat w y q.1.1 q.1.2 = y q := by
  have hne : q.1.1 ≠ q.1.2 := ne_of_lt q.2.1
  simp only [Xmat, hne, if_false]
  rw [dif_pos q.2]
  rfl

theorem Xmat_grD (y : FreeE w → D.host.E) (hy : ∀ q, y q ∈ ddPow D (hgt w q)) : GrD (Xmat w y) := by
  intro a c hac
  rcases eq_or_lt_of_le hac with h | h
  · subst h; simp only [Xmat, if_true, Nat.sub_self]; exact one_mem_ddPow0
  · by_cases hb : blkOf w.1 a.val = blkOf w.1 c.val
    · have := Xmat_q w y ⟨(a, c), h, hb⟩
      simp only at this; rw [this]; exact hy ⟨(a, c), h, hb⟩
    · rw [Xmat_blk w y a c hb]; exact FractionalIdeal.zero_mem _

end Formalism.L2.SG.Pf.StabIntLat
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SymmMemOfMem
section
noncomputable section

open scoped Classical
open Module Matrix
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.TermOp

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Grp

variable {D : D7} {T : D.host.E} (F : LFlag (VS D) D.R.rS T)

theorem symm_mem_of_mem (s : (VS D).V ≃ₗ[D.host.E] (VS D).V) (U : Submodule D.host.E (VS D).V)
    (h : ∀ x ∈ U, s x ∈ U) : ∀ x ∈ U, s.symm x ∈ U := by
  intro x hx
  let f : U →ₗ[D.host.E] U :=
    (s : (VS D).V →ₗ[D.host.E] (VS D).V).restrict (p := U) (q := U) (fun y hy => h y hy)
  have hinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply s.injective
    exact congrArg Subtype.val hab
  obtain ⟨y, hy⟩ := (LinearMap.injective_iff_surjective.mp hinj) ⟨x, hx⟩
  have hyx : s y.1 = x := congrArg Subtype.val hy
  rw [← hyx, LinearEquiv.symm_apply_apply]
  exact y.2

theorem Xflag_mono (j : ℕ) : Xflag F j ≤ Xflag F (j + 1) := by
  exact Formalism.L2.SG.Pf.xflag_mono_td F (Nat.le_succ j)

theorem Xflag_le_X (j : ℕ) : Xflag F j ≤ Xsp F := by
  exact PI.DCRelEquiv.UnitaryGroupMassFormula.Xflag_le_X F j

theorem X_eq_Xflag : Xsp F = Xflag F D.R.rS := by
  exact (Formalism.L2.SG.Pf.xflag_r F).symm

theorem flag_pres {s : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hs : ∀ j, ∀ x ∈ Xflag F (j + 1), s x - x ∈ Xflag F j)
    (j : ℕ) : ∀ x ∈ Xflag F j, s x ∈ Xflag F j := by
  intro x hx
  cases j with
  | zero =>
    rw [Formalism.L2.SG.Pf.xflag_zero_td F, Submodule.mem_bot] at hx
    rw [hx, map_zero]
    exact Submodule.zero_mem _
  | succ j =>
    have h1 := Xflag_mono F j (hs j x hx)
    have h2 := Submodule.add_mem _ h1 hx
    rwa [sub_add_cancel] at h2

theorem flag_inv {s : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hs : ∀ j, ∀ x ∈ Xflag F (j + 1), s x - x ∈ Xflag F j) :
    ∀ j, ∀ x ∈ Xflag F (j + 1), s.symm x - x ∈ Xflag F j := by
  intro j x hx
  have hy : s.symm x ∈ Xflag F (j + 1) :=
    symm_mem_of_mem s (Xflag F (j + 1)) (flag_pres F hs (j + 1)) x hx
  have h1 := hs j (s.symm x) hy
  rw [LinearEquiv.apply_symm_apply] at h1
  have h2 := Submodule.neg_mem _ h1
  rwa [neg_sub] at h2

theorem flag_mul {s t : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hs : ∀ j, ∀ x ∈ Xflag F (j + 1), s x - x ∈ Xflag F j) (ht : ∀ j, ∀ x ∈ Xflag F (j + 1), t x - x ∈ Xflag F j) :
    ∀ j, ∀ x ∈ Xflag F (j + 1), (s * t) x - x ∈ Xflag F j := by
  intro j x hx
  have htx : t x ∈ Xflag F (j + 1) := flag_pres F ht (j + 1) x hx
  have h1 := Submodule.add_mem _ (hs j (t x) htx) (ht j x hx)
  show s (t x) - x ∈ Xflag F j
  rwa [sub_add_sub_cancel] at h1

theorem X_pres {s : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hs : ∀ j, ∀ x ∈ Xflag F (j + 1), s x - x ∈ Xflag F j) :
    ∀ x ∈ Xsp F, s x ∈ Xsp F := by
  intro x hx
  rw [X_eq_Xflag F] at hx ⊢
  exact flag_pres F hs _ x hx

theorem SRat_inv {s : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hs : s ∈ SRat F) : s.symm ∈ SRat F := by
  simp only [SRat, Set.mem_setOf_eq] at hs ⊢
  refine ⟨(Formalism.HermitianLatticesTheory.isom (VS D).hT).inv_mem hs.1, flag_inv F hs.2.1, ?_⟩
  have h1 := symm_mem_of_mem s (Xsp F) (X_pres F hs.2.1) _ hs.2.2
  have h2 := Submodule.neg_mem _ h1
  rw [map_sub, LinearEquiv.symm_apply_apply, neg_sub] at h2
  exact h2

theorem SRat_mul {s t : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hs : s ∈ SRat F) (ht : t ∈ SRat F) : s * t ∈ SRat F := by
  simp only [SRat, Set.mem_setOf_eq] at hs ht ⊢
  refine ⟨(Formalism.HermitianLatticesTheory.isom (VS D).hT).mul_mem hs.1 ht.1, flag_mul F hs.2.1 ht.2.1, ?_⟩
  have hw := ht.2.2
  have hsw := X_pres F hs.2.1 _ hw
  have key : (s * t) F.fl.z - F.fl.z = (s F.fl.z - F.fl.z) +
      (s (t F.fl.z - F.fl.z) - (t F.fl.z - F.fl.z)) + (t F.fl.z - F.fl.z) := by
    show s (t F.fl.z) - F.fl.z = _
    rw [map_sub]; abel
  rw [key]
  exact Submodule.add_mem _ (Submodule.add_mem _ hs.2.2 (Submodule.sub_mem _ hsw hw)) hw

theorem perp_pres {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hi : n ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (hX : ∀ x ∈ Xsp F, n.symm x ∈ Xsp F) : ∀ y ∈ orth (VS D) (Xsp F), n y ∈ orth (VS D) (Xsp F) := by
  have hi' : ∀ a b, (VS D).hT (n a) (n b) = (VS D).hT a b := hi
  intro y hy
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at hy ⊢
  intro x hx
  have h1 := hi' (n.symm x) y
  rw [LinearEquiv.apply_symm_apply] at h1
  rw [h1]
  exact hy _ (hX x hx)

theorem NRat_inv {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ NRat F) : n.symm ∈ NRat F := by
  simp only [NRat, Set.mem_setOf_eq] at hn ⊢
  have hX : ∀ x ∈ Xsp F, n.symm x ∈ Xsp F := symm_mem_of_mem n (Xsp F) (X_pres F hn.2.1)
  have hO := perp_pres F hn.1 hX
  refine ⟨(Formalism.HermitianLatticesTheory.isom (VS D).hT).inv_mem hn.1, flag_inv F hn.2.1, ?_⟩
  intro x hx
  have hy := symm_mem_of_mem n (orth (VS D) (Xsp F)) hO x hx
  have h2 := Submodule.neg_mem _ (hn.2.2 _ hy)
  rw [LinearEquiv.apply_symm_apply, neg_sub] at h2
  exact h2

theorem NRat_mul {n m : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ NRat F) (hm : m ∈ NRat F) : n * m ∈ NRat F := by
  simp only [NRat, Set.mem_setOf_eq] at hn hm ⊢
  refine ⟨(Formalism.HermitianLatticesTheory.isom (VS D).hT).mul_mem hn.1 hm.1, flag_mul F hn.2.1 hm.2.1, ?_⟩
  intro x hx
  have hw := hm.2.2 x hx
  have hnw := X_pres F hn.2.1 _ hw
  have key : (n * m) x - x = (n x - x) + (n (m x - x) - (m x - x)) + (m x - x) := by
    show n (m x) - x = _
    rw [map_sub]; abel
  rw [key]
  exact Submodule.add_mem _ (Submodule.add_mem _ (hn.2.2 x hx) (Submodule.sub_mem _ hnw hw)) hw

end Grp

end Formalism.L2.SG.NGCut.NormalVectorPairings
end
end

