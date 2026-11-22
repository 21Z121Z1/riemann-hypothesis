import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0043
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.AdmNPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0014
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.DictRing
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0038

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RegroupPfFrameCong
section
noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting

namespace Formalism.L2.SG.Pf.RegroupPf

open Formalism.L2.SG.NormCut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section FrameCongSec

theorem coef_of_inMod (I : Formalism.MainNotions.S.AutInst) (m : ℕ) {ι : Type} [Fintype ι] (v : ι → VA I) (S : Set ι) (x : VA I)
    (h : InMod I m (v '' S) x) :
    ∃ t : ι → I.E ⊗[I.F] Af I.F, (∀ i, t i ∈ IntAf I.F I.E) ∧ (∀ i, i ∉ S → t i = 0) ∧
      x - ∑ i, t i • v i ∈ mL I m := by
  obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.1 h
  obtain ⟨l, hl, rfl⟩ := (Finsupp.mem_span_image_iff_linearCombination _).1 hy
  refine ⟨fun i => (l i : I.E ⊗[I.F] Af I.F), fun i => (l i).2, fun i hi => ?_, ?_⟩
  · have h0 : l i = 0 := (Finsupp.mem_supported' _ _).1 hl i hi
    simp [h0]
  · have e : Finsupp.linearCombination (IntAf I.F I.E) v l = ∑ i, (l i : I.E ⊗[I.F] Af I.F) • v i := by
      rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype]
      · rfl
      · intro i; exact zero_smul _ _
    rw [e, add_sub_cancel_left]
    exact hw

variable {D : D7}

theorem frame_congruence_holds : FrameCongC := by
  intro D X Y u u' ρ ρ' γ σ hRL hκ
  obtain ⟨hE0, -, hZ0, -, -⟩ := frame_Lf X
  have hTF : FrameTie X u u' (X.Fu u) (X.Fu u') := Formalism.L2.SG.Full.Full.frameTie u u'
  set g1 : X.B.I.Gf := ((Y.cs u).h ρ : X.B.I.Gf) * X.xu u with hg1
  set g2 : X.B.I.Gf := ((Y.cs u').h ρ' : X.B.I.Gf) * X.xu u' with hg2
  have haC : aC (Y.cs u) ρ = g1 := rfl
  rw [haC]
  set κ := kOf X u u' ((Y.cs u).h ρ : X.B.I.Gf) ((Y.cs u').h ρ' : X.B.I.Gf) γ with hκd
  have hκ' : κ = g1⁻¹ * γ.2 * g2 := rfl
  obtain ⟨hκK, hcE, hcZ, -⟩ := hκ
  have hg0 : 0 < X.B.g := by
    rw [X.g_eq]; exact Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos
  set e0v : Fin (D.R.rS + 1) → VA X.B.I := Fin.snoc (α := fun _ => VA X.B.I) X.e0 X.z0 with he0v
  have he0vL : ∀ a, e0v a ∈ X.B.I.Lf := fun a => by
    refine Fin.lastCases ?_ (fun i => ?_) a
    · simp only [he0v, Fin.snoc_last]; exact hZ0
    · simp only [he0v, Fin.snoc_castSucc]; exact hE0 i

  have hcol : ∀ c : Fin (D.R.rS + 1), ∃ t : Fin (D.R.rS + 1) → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F,
      (∀ a, t a ∈ IntAf X.B.I.F X.B.I.E) ∧ t c = 1 ∧ (∀ a, c < a → t a = 0) ∧
      X.B.I.fmat κ *ᵥ e0v c - ∑ a, t a • e0v a ∈ mL X.B.I X.B.g := by
    intro c
    cases c using Fin.lastCases with
    | last =>
      have hZ' : InMod X.B.I X.B.g (X.e0 '' Set.univ) ((X.B.I.fmat κ - 1) *ᵥ X.z0) := by
        rw [Set.image_univ]; exact hcZ
      obtain ⟨τ, hτI, -, hτ⟩ := coef_of_inMod X.B.I X.B.g X.e0 Set.univ _ hZ'
      refine ⟨Fin.snoc (α := fun _ => X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) τ 1, fun a => ?_, ?_, fun a ha => ?_, ?_⟩
      · cases a using Fin.lastCases with
        | last => simp only [Fin.snoc_last]; exact one_mem _
        | cast j => simp only [Fin.snoc_castSucc]; exact hτI j
      · simp only [Fin.snoc_last]
      · exact absurd ha (not_lt.2 (Fin.le_last a))
      · have e : X.B.I.fmat κ *ᵥ e0v (Fin.last _) -
            ∑ a, (Fin.snoc (α := fun _ => X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) τ 1 a) • e0v a =
            (X.B.I.fmat κ - 1) *ᵥ X.z0 - ∑ j, τ j • X.e0 j := by
          simp only [Fin.sum_univ_castSucc, he0v, Fin.snoc_castSucc, Fin.snoc_last, one_smul, Matrix.sub_mulVec,
            Matrix.one_mulVec]
          abel
        rw [e]; exact hτ
    | cast b =>
      obtain ⟨τ, hτI, hτ0, hτ⟩ := coef_of_inMod X.B.I X.B.g X.e0 {j | j.1 < b.1} _ (hcE b)
      have hτb : τ b = 0 := hτ0 b (fun h => lt_irrefl (b : ℕ) h)
      refine ⟨Fin.snoc (α := fun _ => X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (fun j => τ j + if j = b then 1 else 0) 0,
        fun a => ?_, ?_, fun a ha => ?_, ?_⟩
      · cases a using Fin.lastCases with
        | last => simp only [Fin.snoc_last]; exact zero_mem _
        | cast j =>
          simp only [Fin.snoc_castSucc]
          refine add_mem (hτI j) ?_
          split_ifs
          · exact one_mem _
          · exact zero_mem _
      · simp [Fin.snoc_castSucc, hτb]
      · cases a using Fin.lastCases with
        | last => simp only [Fin.snoc_last]
        | cast j =>
          have hbj : b < j := Fin.castSucc_lt_castSucc_iff.1 ha
          have hj : τ j = 0 := hτ0 j (fun h => lt_asymm hbj h)
          have hjb : j ≠ b := fun h => by subst h; exact lt_irrefl _ hbj
          simp only [Fin.snoc_castSucc, hj, if_neg hjb, add_zero]
      · have e : X.B.I.fmat κ *ᵥ e0v (Fin.castSucc b) -
            ∑ a, (Fin.snoc (α := fun _ => X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)
              (fun j => τ j + if j = b then 1 else 0) 0 a) • e0v a =
            (X.B.I.fmat κ - 1) *ᵥ X.e0 b - ∑ j, τ j • X.e0 j := by
          simp only [Fin.sum_univ_castSucc, he0v, Fin.snoc_castSucc, Fin.snoc_last, zero_smul, add_zero, add_smul,
            Finset.sum_add_distrib, ite_smul, one_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true,
            Matrix.sub_mulVec, Matrix.one_mulVec]
          abel
        rw [e]; exact hτ
  choose t htI ht1 ht0 htm using hcol

  set s : D.host.E → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F :=
    fun x => Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (X.ιE.symm x) with hs
  have happ : ∀ c a, ∃ ξ : 𝓞 D.host.E, ∃ y ∈ IntAf X.B.I.F X.B.I.E,
      t c a = s (ξ : D.host.E) + (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * y := by
    intro c a
    obtain ⟨a', y, hy, he⟩ := PIW.AdelClassFin.dual_dense X.B.I.F X.B.I.E X.B.g hg0 (t c a) (htI c a)
    have hint : IsIntegral ℤ (X.ιE (a' : X.B.I.E)) := (a'.2 : IsIntegral ℤ (a' : X.B.I.E)).map X.ιE.toRingHom.toIntAlgHom
    refine ⟨⟨X.ιE (a' : X.B.I.E), hint⟩, y, hy, ?_⟩
    show t c a = Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (X.ιE.symm (X.ιE (a' : X.B.I.E))) + _
    rw [RingEquiv.symm_apply_apply]
    exact he
  choose ξ0 y0 hy0 hξ0 using happ
  set ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E) :=
    fun a c => if a < c then ξ0 c a else if a = c then 1 else 0 with hξd
  have hsI : ∀ a c, s (ξ a c : D.host.E) ∈ IntAf X.B.I.F X.B.I.E := fun a c => inclE_int X (ξ a c)
  have hrel : ∀ a c, ∃ y ∈ IntAf X.B.I.F X.B.I.E,
      t c a = s (ξ a c : D.host.E) + (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * y := by
    intro a c
    rcases lt_trichotomy a c with h | h | h
    · refine ⟨y0 c a, hy0 c a, ?_⟩
      simp only [hξd, if_pos h]
      exact hξ0 c a
    · subst h
      refine ⟨0, zero_mem _, ?_⟩
      simp only [hξd, lt_irrefl, if_false, if_pos rfl, ht1, mul_zero, add_zero, hs]
      simp
    · refine ⟨0, zero_mem _, ?_⟩
      have hna : ¬ a < c := not_lt.2 h.le
      have hne : a ≠ c := ne_of_gt h
      simp only [hξd, if_neg hna, if_neg hne, ht0 c a h, mul_zero, add_zero, hs]
      simp
  refine ⟨ξ, fun a b hab => ?_, fun a => ?_, fun b => ?_⟩
  · simp only [hξd, if_neg (not_lt.2 hab.le), if_neg (ne_of_gt hab)]
  · simp [hξd]

  set Yv : Fin (D.R.rS + 1) → VA X.B.I := fun a => X.B.I.fmat g1⁻¹ *ᵥ incl X.B.I (X.crd ((X.Fu u).fvec a)) with hY
  set Yv' : Fin (D.R.rS + 1) → VA X.B.I := fun c => X.B.I.fmat g2⁻¹ *ᵥ incl X.B.I (X.crd ((X.Fu u').fvec c))
    with hY'
  have fixE : ∀ (w : D.what₂.Word) (h : Formalism.L2.SG.PoincareInHH.PoincareSetting.Hfin X w) (a : Fin D.R.rS),
      X.B.I.fmat ((h : X.B.I.Gf) * X.xu w)⁻¹ *ᵥ incl X.B.I (X.crd (X.eX a)) = incl X.B.I (X.crd (X.eX a)) :=
    fun w h a => fixes_inv X (fixes_mul X (h.2 _ (Or.inl (Or.inl ⟨a, rfl⟩))) ((X.xu_fix w a).1))
  have fixZ : ∀ (w : D.what₂.Word) (h : Formalism.L2.SG.PoincareInHH.PoincareSetting.Hfin X w),
      X.B.I.fmat ((h : X.B.I.Gf) * X.xu w)⁻¹ *ᵥ incl X.B.I (X.crd (X.zu w)) =
        X.B.I.fmat (X.xu w)⁻¹ *ᵥ incl X.B.I (X.crd (X.zu w)) := by
    intro w h
    have hz : X.B.I.fmat (h : X.B.I.Gf)⁻¹ *ᵥ incl X.B.I (X.crd (X.zu w)) = incl X.B.I (X.crd (X.zu w)) :=
      fixes_inv X (h.2 _ (Or.inr rfl))
    rw [_root_.mul_inv_rev, fmat_mul, ← Matrix.mulVec_mulVec, hz]
  have hYa : ∀ a, InAt X.B.I X.B.g X.B.g (e0v a - Yv a) := by
    intro a
    refine Fin.lastCases ?_ (fun i => ?_) a
    · simp only [he0v, hY, Fin.snoc_last, FlagG.fvec, hTF.2.1, hg1, fixZ]
      have := InAt_neg X (X.xu_z u)
      rwa [neg_sub] at this
    · simp only [he0v, hY, Fin.snoc_castSucc, FlagG.fvec, hTF.1 i, hg1, fixE]
      exact (X.basisApprox i).1
  have hY'a : ∀ c, InAt X.B.I X.B.g X.B.g (e0v c - Yv' c) := by
    intro c
    refine Fin.lastCases ?_ (fun i => ?_) c
    · simp only [he0v, hY', Fin.snoc_last, FlagG.fvec, hTF.2.2.2, hg2, fixZ]
      have := InAt_neg X (X.xu_z u')
      rwa [neg_sub] at this
    · simp only [he0v, hY', Fin.snoc_castSucc, FlagG.fvec, hTF.2.2.1 i, hg2, fixE]
      exact (X.basisApprox i).1

  have e : X.B.I.fmat g1⁻¹ *ᵥ incl X.B.I (X.crd (σ (frame (lf D (X.Fu u')) b) -
      frameAct (frame (lf D (X.Fu u))) ξ b)) = X.B.I.fmat κ *ᵥ Yv' b - ∑ a, s (ξ a b : D.host.E) • Yv a := by
    simp only [frameAct, crd_sub', crd_sum', crd_smul', incl_sub', incl_sum', incl_smul', Matrix.mulVec_sub,
      mulVec_fsum, Matrix.mulVec_smul, ratLink_incl X hRL]
    congr 1
    simp only [hY', Matrix.mulVec_mulVec, hκ', ← fmat_mul]
    congr 2
    group
  rw [e]
  have split : X.B.I.fmat κ *ᵥ Yv' b - ∑ a, s (ξ a b : D.host.E) • Yv a =
      (X.B.I.fmat κ *ᵥ e0v b - ∑ a, t b a • e0v a) - X.B.I.fmat κ *ᵥ (e0v b - Yv' b) +
        ∑ a, (t b a - s (ξ a b : D.host.E)) • e0v a + ∑ a, s (ξ a b : D.host.E) • (e0v a - Yv a) := by
    simp only [Matrix.mulVec_sub, smul_sub, sub_smul, Finset.sum_sub_distrib]
    abel
  rw [split]
  have inAt_mL : ∀ w : VA X.B.I, w ∈ mL X.B.I X.B.g → InAt X.B.I X.B.g X.B.g w := fun w hw =>
    ⟨1, Nat.coprime_one_left _, by rw [Nat.cast_one, one_smul]; exact hw⟩
  refine InAt_add X (InAt_add X (InAt_sub X (inAt_mL _ (htm b)) (InAt_K X hκK (hY'a b)))
    (InAt_sum X _ _ fun a _ => inAt_mL _ ?_)) (InAt_sum X _ _ fun a _ => InAt_smul X (hsI a b) (hYa a))
  obtain ⟨y, hy, hty⟩ := hrel a b
  rw [hty, add_sub_cancel_left, mul_smul]
  have hyL : y • e0v a ∈ X.B.I.Lf := by
    have : y • e0v a = (⟨y, hy⟩ : IntAf X.B.I.F X.B.I.E) • e0v a := rfl
    rw [this]; exact Submodule.smul_mem _ _ (he0vL a)
  exact Formalism.L2.SG.Pf.unitaryCongruence.smul_mem_mL X.B.I hyL

end FrameCongSec

end Formalism.L2.SG.Pf.RegroupPf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RegroupPfStabFlag
section
noncomputable section

open scoped Classical ComplexConjugate ENNReal NNReal
open MeasureTheory

namespace Formalism.L2.SG.Pf.RegroupPf

open Formalism.L2.SG.FoldBound Formalism.L2.SG.PoincareSeriesSquareIntegrable NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp.KExpCut Formalism.L2.SG.Full

namespace StabFlagPf

open Matrix

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

def toVHom : (Fin X.B.I.n → X.B.I.E) →+ (VS D).V where
  toFun := Formalism.L2.SG.Pf.Level.toV X
  map_zero' := by simp [Formalism.L2.SG.Pf.Level.toV]
  map_add' := Formalism.L2.SG.Pf.Level.toV_add X

theorem toV_span {T : Set (Fin X.B.I.n → X.B.I.E)} {w : Fin X.B.I.n → X.B.I.E}
    (hw : w ∈ Submodule.span X.B.I.E T) :
    Formalism.L2.SG.Pf.Level.toV X w ∈ Submodule.span D.host.E (Formalism.L2.SG.Pf.Level.toV X '' T) :=
  Formalism.L2.SG.Pf.Vanish2.tr_span X.ιE.toRingHom (toVHom X) (fun c x => Formalism.L2.SG.Pf.Level.toV_smul X c x) hw

theorem flag_e {u' : D.what₂.Word} {s : X.B.I.GA} {σ : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hs : RatLink X s σ) (hS : s ∈ Srat X u') (a : Fin D.R.rS) :
    σ (X.eX a) - X.eX a ∈ Submodule.span D.host.E (X.eX '' {b | b.1 < a.1}) := by
  obtain ⟨M, -, -, h2, h3⟩ := hs
  obtain ⟨-, hsf⟩ := Formalism.L2.SG.PoincareInHH.Cut.sratComp_holds X u' _ hS
  obtain ⟨hfe, -⟩ := hsf
  have hf := hfe a
  have hG : ∀ y, X.B.I.fmat s.2 *ᵥ Formalism.L2.SG.Pf.Vanish2.inclHom X.B.I y =
      Formalism.L2.SG.Pf.Vanish2.inclHom X.B.I ((M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ y) := by
    intro y
    rw [Formalism.L2.SG.Pf.Vanish2.inclHom_apply, Formalism.L2.SG.Pf.Vanish2.inclHom_apply, h2]
    exact Formalism.L2.SG.Pf.Level.incl_mulVec X _ y
  have e := Formalism.L2.SG.Pf.Vanish2.tr_sub (Formalism.L2.SG.Pf.Vanish2.inclHom X.B.I) _ _ hG (X.eR a)
  rw [Formalism.L2.SG.Pf.Vanish2.inclHom_apply, Formalism.L2.SG.Pf.Vanish2.inclHom_apply] at e
  rw [e] at hf
  have hd := Formalism.L2.SG.Pf.Level.descend X _ _ hf
  have hm : ((M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) - 1) *ᵥ X.eR a = X.crd (σ (X.eX a) - X.eX a) :=
    Formalism.L2.SG.Pf.Vanish2.mcrd X h3 (X.eX a)
  rw [hm] at hd
  have ht := toV_span X hd
  rw [Formalism.L2.SG.Pf.Level.toV_crd, Set.image_image] at ht
  have e2 : (fun b => Formalism.L2.SG.Pf.Level.toV X (X.eR b)) = X.eX :=
    funext fun b => Formalism.L2.SG.Pf.Level.toV_crd X (X.eX b)
  rwa [e2] at ht

end StabFlagPf

theorem flag_stabilizer_holds : StabFlagC := by
  intro D X Y u u' _ s σ hs _ hS j x hx
  have e : ∀ k, Xflag (lf D (X.Fu u')) k = Submodule.span D.host.E (X.eX '' {i | i.1 < k}) := by
    intro k
    show Submodule.span D.host.E ((X.Fu u').e '' {i | i.1 < k}) = _
    rw [X.Fu_e]
  rw [e] at hx ⊢
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, ha, rfl⟩ := hy
    refine Submodule.span_mono ?_ (StabFlagPf.flag_e X hs hS a)
    rintro _ ⟨b, hb, rfl⟩
    exact ⟨b, lt_of_lt_of_le hb (Nat.lt_succ_iff.1 ha), rfl⟩
  | zero => simp
  | add y z _ _ hy hz =>
    rw [map_add, add_sub_add_comm]
    exact add_mem hy hz
  | smul c y _ hy =>
    rw [map_smul, ← smul_sub]
    exact Submodule.smul_mem _ _ hy

end Formalism.L2.SG.Pf.RegroupPf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabCountPf
section
noncomputable section

open scoped Classical ComplexConjugate ENNReal NNReal
open MeasureTheory

namespace Formalism.L2.SG.Pf.SlabCount

open Formalism.L2.SG.FoldBound Formalism.L2.SG.PoincareSeriesSquareIntegrable NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PoincareInHH.Cut Formalism.L2.SG.TermOp.KExpCut Formalism.L2.SG.Full
  Formalism.L2.SG.Pf.Slab

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Eq

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}
  {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem gterm_eq_of {t t' : GTerm X u u' F0 F0' what₂ rows'} (h1 : t.lam = t'.lam) (h2 : t.lam' = t'.lam')
    (n ν : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hn : n ∈ NLam t.lam (lf D F0)) (hν : ν ∈ NLam t.lam' (lf D F0'))
    (he : t'.lin = n * t.lin * ν) : t = t' := by
  obtain ⟨l, m, l', m', c⟩ := t
  obtain ⟨l2, m2, l2', m2', c2⟩ := t'
  dsimp only at h1 h2
  subst h1 h2
  have hc : c = c2 := by
    rw [← Quot.out_eq c, ← Quot.out_eq c2]
    exact Quot.sound ⟨n, hn, ν, hν, he⟩
  subst hc
  rfl

end Eq

theorem countC_of_leviFin (hL : LeviFinC) : CountC := by
  intro D X Y u u'
  obtain ⟨F, hF⟩ := hL D X Y u'
  refine ⟨((∑ Λ₁ ∈ Y.what₂ u', ∑ Λ₂ ∈ Y.what₂ u', (F Λ₁ Λ₂).card : ℕ) : ℝ≥0∞), ENNReal.natCast_ne_top _, ?_⟩
  intro T T' Λ hΛ E hE x
  have hWD : PhWellDef X u Y.hK := Formalism.L2.SG.Pf.phWellDef_holds X u
  have hWD' : PhWellDef X u' Y.hK := Formalism.L2.SG.Pf.phWellDef_holds X u'
  have hLI : PhLeftInv X u Y.hK :=
    phLeftInv_of X u Y.hK hWD (Formalism.L2.SG.Pf.ratLevi_holds X u) (Formalism.L2.SG.Pf.psiProd_holds X u)
  have hLI' : PhLeftInv X u' Y.hK :=
    phLeftInv_of X u' Y.hK hWD' (Formalism.L2.SG.Pf.ratLevi_holds X u') (Formalism.L2.SG.Pf.psiProd_holds X u')

  let I := Σ t : {t : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') // t.lam = Λ}, E t.1
  have hlift : ∀ i : I, ∃ (xm : X.B.I.GA) (nm : (VS D).V ≃ₗ[D.host.E] (VS D).V),
      RatLink X xm nm ∧ (i.2 : X.B.I.Ginf) = xm.1 ∧ nm ∈ NLam Λ (lf D (X.Fu u)) := by
    intro i
    have hm : (i.2 : X.B.I.Ginf) ∈ ROset X (X.Fu u) (X.Fu u) Λ Λ 1 := (hE i.1.1 i.1.2).1 i.2.2
    obtain ⟨xm, nm, h1, h2, h3, -⟩ := hm
    exact ⟨xm, nm, h1, h2, h3⟩
  choose xm nm hxm hmx hnm using hlift

  let g : I → X.B.I.GA := fun i => (i.1.1.pt)⁻¹ * xm i
  have hg : ∀ i : I, RatLink X (g i) ((i.1.1.lin)⁻¹ * nm i) := fun i =>
    Formalism.L2.SG.TermOp.Vanish.ratLink_mul X (Formalism.L2.SG.TermOp.Vanish.ratLink_inv X i.1.1.rep.2.1) (hxm i)
  have hgr : ∀ i : I, g i ∈ Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I := fun i => ratLink_mem X (hg i)
  have hdec : ∀ i : I, ∃ p : (Srat X u') × (Y.Dt u'), (p.1 : X.B.I.GA) * (p.2 : X.B.I.GA) = g i :=
    fun i => ((Y.reps u').2 (g i) (hgr i)).exists
  choose p hp using hdec
  let φ : I → Y.Dt u' := fun i => (p i).2
  let G : Y.Dt u' → ℝ≥0∞ := fun δ => ‖Ph X u' Y.hK T' ((δ : X.B.I.GA) * (x, aB Y u Λ))‖ₑ

  have hκ : ∀ i : I, (aB Y u Λ)⁻¹ * (xm i).2 * aB Y u Λ ∈ X.K2 := by
    intro i
    have hn : nm i ∈ NLam ((Y.cs u).lamOf ((Y.cs u).base Λ)) (lf D (X.Fu u)) := by
      rw [(Y.cs u).base_lam Λ hΛ]; exact hnm i
    exact (Formalism.L2.SG.Pf.nilradical_conj_level' D X Y u ((Y.cs u).base Λ) (xm i) (nm i) hn (hxm i)).1
  have e1 : ∀ i : I, ((i.2 : X.B.I.Ginf) * x, aB Y u Λ) = xm i * (x, (xm i).2⁻¹ * aB Y u Λ) := by
    intro i
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_mul]; rw [hmx i]
    · simp only [Prod.snd_mul]; group
  have e2 : ∀ i : I, ((x, aB Y u Λ) : X.B.I.GA) =
      (x, (xm i).2⁻¹ * aB Y u Λ) * (1, (aB Y u Λ)⁻¹ * (xm i).2 * aB Y u Λ) := by
    intro i
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_mul, mul_one]
    · simp only [Prod.snd_mul]; group
  have hA : ∀ i : I, ‖Ph X u Y.hK T ((i.2 : X.B.I.Ginf) * x, aB Y u Λ)‖ₑ = ‖Ph X u Y.hK T (x, aB Y u Λ)‖ₑ := by
    intro i
    rw [e1 i, hLI T _ (Formalism.L2.SG.Pf.RegroupPf.nlam_srat u Λ (hxm i) (hnm i))]
    conv_rhs => rw [e2 i]
    rw [enorm_ph_right Y.hK hWD T _ _ (hκ i)]
  have hB : ∀ i : I, ‖Ph X u' Y.hK T' (i.1.1.pt⁻¹ * ((i.2 : X.B.I.Ginf) * x, aB Y u Λ))‖ₑ = G (φ i) := by
    intro i
    show _ = ‖Ph X u' Y.hK T' (((p i).2 : X.B.I.GA) * (x, aB Y u Λ))‖ₑ
    rw [e1 i, ← mul_assoc, show i.1.1.pt⁻¹ * xm i = g i from rfl, ← hp i, mul_assoc,
      hLI' T' _ (p i).1.2]
    conv_rhs => rw [e2 i, ← mul_assoc]
    rw [enorm_ph_right Y.hK hWD' T' _ _ (hκ i)]

  have hfib : ∀ k : Y.Dt u', ∃ (S : Finset (Submodule (𝓞 D.host.E) (VS D).V × ((VS D).V ≃ₗ[D.host.E] (VS D).V)))
      (e : I → Submodule (𝓞 D.host.E) (VS D).V × ((VS D).V ≃ₗ[D.host.E] (VS D).V)),
      S.card ≤ ∑ Λ₁ ∈ Y.what₂ u', ∑ Λ₂ ∈ Y.what₂ u', (F Λ₁ Λ₂).card ∧
      ∀ i, φ i = k → e i ∈ S ∧ ∀ j, φ j = k → e i = e j → i = j := by
    intro k
    by_cases h0 : ∃ i0, φ i0 = k
    swap
    · exact ⟨∅, fun _ => (⊥, 1), by simp, fun i hi => absurd ⟨i, hi⟩ h0⟩
    obtain ⟨i0, hi0⟩ := h0
    let σ : I → (VS D).V ≃ₗ[D.host.E] (VS D).V := fun i =>
      ((i0.1.1.lin)⁻¹ * nm i0) * ((i.1.1.lin)⁻¹ * nm i)⁻¹
    let e : I → Submodule (𝓞 D.host.E) (VS D).V × ((VS D).V ≃ₗ[D.host.E] (VS D).V) := fun i =>
      (i.1.1.lam', if h : ∃ f ∈ F i0.1.1.lam' i.1.1.lam', f⁻¹ * σ i ∈ NLam i.1.1.lam' (lf D (X.Fu u'))
        then h.choose else 1)
    have hex : ∀ i, φ i = k →
        ∃ f ∈ F i0.1.1.lam' i.1.1.lam', f⁻¹ * σ i ∈ NLam i.1.1.lam' (lf D (X.Fu u')) := by
      intro i hi
      refine hF _ i0.1.1.mem' _ i.1.1.mem' (σ i) (g i0 * (g i)⁻¹)
        (Formalism.L2.SG.TermOp.Vanish.ratLink_mul X (hg i0) (Formalism.L2.SG.TermOp.Vanish.ratLink_inv X (hg i))) ?_ ?_ ?_
      · have h0 := i0.1.1.rep.2.2.1
        have h1 := i.1.1.rep.2.2.1
        exact (Formalism.HermitianLatticesTheory.isom (VS D).hT).mul_mem
          ((Formalism.HermitianLatticesTheory.isom (VS D).hT).mul_mem ((Formalism.HermitianLatticesTheory.isom (VS D).hT).inv_mem h0) (hnm i0).1.1)
          ((Formalism.HermitianLatticesTheory.isom (VS D).hT).inv_mem
            ((Formalism.HermitianLatticesTheory.isom (VS D).hT).mul_mem ((Formalism.HermitianLatticesTheory.isom (VS D).hT).inv_mem h1) (hnm i).1.1))
      · have hpe : ((p i0).2 : X.B.I.GA) = ((p i).2 : X.B.I.GA) :=
          congrArg Subtype.val (hi0.trans hi.symm)
        have hgg : g i0 * (g i)⁻¹ = ((p i0).1 : X.B.I.GA) * ((p i).1 : X.B.I.GA)⁻¹ := by
          rw [← hp i0, ← hp i, hpe]; group
        rw [hgg]
        exact (Srat X u').mul_mem (p i0).1.2 ((Srat X u').inv_mem (p i).1.2)
      · have hs : σ i = (i0.1.1.lin)⁻¹ * (nm i0 * ((nm i)⁻¹ * i.1.1.lin)) := by
          simp only [σ, mul_inv_rev, inv_inv, mul_assoc]
        have ht : Formalism.HermitianLatticesTheory.gmap i.1.1.lin i.1.1.lam' = Λ := i.1.1.rep.2.2.2.1.trans i.1.2
        have ht0 : Formalism.HermitianLatticesTheory.gmap i0.1.1.lin i0.1.1.lam' = Λ := i0.1.1.rep.2.2.2.1.trans i0.1.2
        rw [hs, Formalism.L2.SG.Pf.gmap_mul, Formalism.L2.SG.Pf.gmap_mul, Formalism.L2.SG.Pf.gmap_mul, ht,
          (Formalism.L2.SG.Pf.nlam_inv (hnm i)).1.2, (hnm i0).1.2]
        exact Formalism.L2.SG.Pf.gmap_inv ht0
    refine ⟨(Y.what₂ u').biUnion (fun Λ₂ => (F i0.1.1.lam' Λ₂).image (fun f => (Λ₂, f))), e, ?_, ?_⟩
    · calc ((Y.what₂ u').biUnion (fun Λ₂ => (F i0.1.1.lam' Λ₂).image (fun f => (Λ₂, f)))).card
          ≤ ∑ Λ₂ ∈ Y.what₂ u', ((F i0.1.1.lam' Λ₂).image (fun f => (Λ₂, f))).card := Finset.card_biUnion_le
        _ ≤ ∑ Λ₂ ∈ Y.what₂ u', (F i0.1.1.lam' Λ₂).card := Finset.sum_le_sum fun _ _ => Finset.card_image_le
        _ ≤ ∑ Λ₁ ∈ Y.what₂ u', ∑ Λ₂ ∈ Y.what₂ u', (F Λ₁ Λ₂).card :=
          Finset.single_le_sum (f := fun Λ₁ => ∑ Λ₂ ∈ Y.what₂ u', (F Λ₁ Λ₂).card) (fun _ _ => Nat.zero_le _)
            i0.1.1.mem'
    · intro i hi
      have hei : e i = (i.1.1.lam', (hex i hi).choose) := by
        simp only [e, dif_pos (hex i hi)]
      refine ⟨?_, ?_⟩
      · rw [hei]
        exact Finset.mem_biUnion.2 ⟨i.1.1.lam', i.1.1.mem', Finset.mem_image.2 ⟨_, (hex i hi).choose_spec.1, rfl⟩⟩
      intro j hj hij
      have hej : e j = (j.1.1.lam', (hex j hj).choose) := by
        simp only [e, dif_pos (hex j hj)]
      rw [hei, hej] at hij
      have hl' : i.1.1.lam' = j.1.1.lam' := congrArg Prod.fst hij
      have hf : (hex i hi).choose = (hex j hj).choose := congrArg Prod.snd hij
      have hνi := (hex i hi).choose_spec.2
      have hνj := (hex j hj).choose_spec.2
      rw [← hf, ← hl'] at hνj
      have hν : i.1.1.lin⁻¹ * nm i * ((nm j)⁻¹ * j.1.1.lin) ∈ NLam i.1.1.lam' (lf D (X.Fu u')) := by
        have := Formalism.L2.SG.Pf.nlam_mul (Formalism.L2.SG.Pf.nlam_inv hνi) hνj
        have hq : ((hex i hi).choose⁻¹ * σ i)⁻¹ * ((hex i hi).choose⁻¹ * σ j) =
            i.1.1.lin⁻¹ * nm i * ((nm j)⁻¹ * j.1.1.lin) := by
          simp only [σ]; group
        rwa [hq] at this
      obtain ⟨ti, mi⟩ := i
      obtain ⟨tj, mj⟩ := j
      have hnΛ : nm ⟨tj, mj⟩ * (nm ⟨ti, mi⟩)⁻¹ ∈ NLam ti.1.lam (lf D (X.Fu u)) := by
        rw [ti.2]; exact Formalism.L2.SG.Pf.nlam_mul (hnm _) (Formalism.L2.SG.Pf.nlam_inv (hnm _))
      have htt : ti = tj := Subtype.ext (gterm_eq_of (ti.2.trans tj.2.symm) hl' _ _ hnΛ hν (by group))
      subst htt

      have hr : ((xm ⟨ti, mi⟩ * (xm ⟨ti, mj⟩)⁻¹).1 : X.B.I.Ginf) ∈
          ROsub X (X.Fu u) (X.Fu u') ti.1.lam ti.1.lam' ti.1.lin := by
        refine ⟨xm ⟨ti, mi⟩ * (xm ⟨ti, mj⟩)⁻¹, nm ⟨ti, mi⟩ * (nm ⟨ti, mj⟩)⁻¹,
          Formalism.L2.SG.TermOp.Vanish.ratLink_mul X (hxm _) (Formalism.L2.SG.TermOp.Vanish.ratLink_inv X (hxm _)), rfl,
          ?_, ?_⟩
        · rw [ti.2]; exact Formalism.L2.SG.Pf.nlam_mul (hnm _) (Formalism.L2.SG.Pf.nlam_inv (hnm _))
        · convert hν using 1
          all_goals rfl
      have hT := hE ti.1 ti.2
      obtain ⟨q, -, hq⟩ := hT.2 (mi : X.B.I.Ginf) (hT.1 mi.2)
      have h1 := hq ⟨1, mi⟩ (one_mul _)
      have h2 := hq ⟨⟨_, hr⟩, mj⟩ (by
        show (xm ⟨ti, mi⟩ * (xm ⟨ti, mj⟩)⁻¹).1 * (mj : X.B.I.Ginf) = mi
        rw [Prod.fst_mul, Prod.fst_inv, hmx ⟨ti, mi⟩, hmx ⟨ti, mj⟩]
        group)
      have hm : mj = mi := congrArg Prod.snd (h2.trans h1.symm)
      rw [hm]

  have hsig : (∑' t : {t : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') // t.lam = Λ}, ∑' m : E t.1,
        ‖Ph X u Y.hK T ((m : X.B.I.Ginf) * x, aB Y u Λ)‖ₑ *
          ‖Ph X u' Y.hK T' (t.1.pt⁻¹ * ((m : X.B.I.Ginf) * x, aB Y u Λ))‖ₑ) =
      ∑' i : I, ‖Ph X u Y.hK T ((i.2 : X.B.I.Ginf) * x, aB Y u Λ)‖ₑ *
          ‖Ph X u' Y.hK T' (i.1.1.pt⁻¹ * ((i.2 : X.B.I.Ginf) * x, aB Y u Λ))‖ₑ :=
    (ENNReal.tsum_sigma' (fun i : I => ‖Ph X u Y.hK T ((i.2 : X.B.I.Ginf) * x, aB Y u Λ)‖ₑ *
          ‖Ph X u' Y.hK T' (i.1.1.pt⁻¹ * ((i.2 : X.B.I.Ginf) * x, aB Y u Λ))‖ₑ)).symm
  rw [hsig]
  calc ∑' i : I, ‖Ph X u Y.hK T ((i.2 : X.B.I.Ginf) * x, aB Y u Λ)‖ₑ *
          ‖Ph X u' Y.hK T' (i.1.1.pt⁻¹ * ((i.2 : X.B.I.Ginf) * x, aB Y u Λ))‖ₑ
      = ∑' i : I, ‖Ph X u Y.hK T (x, aB Y u Λ)‖ₑ * G (φ i) := tsum_congr fun i => by rw [hA i, hB i]
    _ = ‖Ph X u Y.hK T (x, aB Y u Λ)‖ₑ * ∑' i : I, G (φ i) := ENNReal.tsum_mul_left
    _ ≤ ‖Ph X u Y.hK T (x, aB Y u Λ)‖ₑ *
          (((∑ Λ₁ ∈ Y.what₂ u', ∑ Λ₂ ∈ Y.what₂ u', (F Λ₁ Λ₂).card : ℕ) : ℝ≥0∞) * ∑' δ : Y.Dt u', G δ) :=
        by gcongr; exact tsum_comp_le_of_fibre φ G _ hfib
    _ = _ := by rw [mul_left_comm]

end Formalism.L2.SG.Pf.SlabCount
end
end

