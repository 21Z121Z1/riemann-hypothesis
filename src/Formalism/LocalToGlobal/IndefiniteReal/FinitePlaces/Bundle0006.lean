import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IntegrableOnOfPeriodic
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0003
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0017
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0005
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0020
import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.ConjPurelyImaginaryGenerator
import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.RealPlaceImaginaryGeneratorReEqZero
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.ContinuousSplitInv

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.HeisSt
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField Matrix Topology
open scoped TensorProduct ComplexConjugate ContDiff

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem trace_fst_eq_zero (z : AE D) (hz : infPart D z = 0) :
    fstA D.host.F (Algebra.trace (AF D.host.F) (AE D) z) = 0 := by
  have hc : ∀ k, fstA D.host.F (Formalism.IndefR.PHeisFC.cE D.host.F D.host.E z k) = 0 := fun k => by
    show (Formalism.IndefR.PHeisFC.cE D.host.F D.host.E z k).1 = 0
    rw [← Formalism.IndefR.PHeisTh.repr_fst]
    have : Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) z = 0 := hz
    rw [this, map_zero]; rfl
  rw [← (Formalism.IndefR.PHeisFC.bA D.host.F D.host.E).sum_repr z, map_sum, map_sum]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [map_smul, smul_eq_mul, map_mul]
  have : (Formalism.IndefR.PHeisFC.bA D.host.F D.host.E).repr z k = Formalism.IndefR.PHeisFC.cE D.host.F D.host.E z k := rfl
  rw [this, hc, zero_mul]

theorem trace_snd_eq_zero (z : AE D) (hz : finPart D z = 0) :
    sndA D.host.F (Algebra.trace (AF D.host.F) (AE D) z) = 0 := by
  have hc : ∀ k, sndA D.host.F (Formalism.IndefR.PHeisFC.cE D.host.F D.host.E z k) = 0 := fun k => by
    show (Formalism.IndefR.PHeisFC.cE D.host.F D.host.E z k).2 = 0
    rw [← Formalism.IndefR.PHeisTh.repr_snd]
    have : Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) z = 0 := hz
    rw [this, map_zero]; rfl
  rw [← (Formalism.IndefR.PHeisFC.bA D.host.F D.host.E).sum_repr z, map_sum, map_sum]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [map_smul, smul_eq_mul, map_mul]
  have : (Formalism.IndefR.PHeisFC.bA D.host.F D.host.E).repr z k = Formalism.IndefR.PHeisFC.cE D.host.F D.host.E z k := rfl
  rw [this, hc, zero_mul]

variable (S T : HSp D)

set_option synthInstance.maxHeartbeats 400000 in
theorem infPart_hO (u w : MO S T) (hu : u.map (infPart D) = 0) : infPart D (hO S T u w) = 0 := by
  have h0 : ∀ d a, infPart D (u d a) = 0 := fun d a => congrFun (congrFun hu d) a
  unfold hO
  simp only [map_sum (infPart D), map_mul (infPart D), h0, mul_zero, Finset.sum_const_zero]

set_option synthInstance.maxHeartbeats 400000 in
theorem finPart_hO (u w : MO S T) (hu : u.map (finPart D) = 0) : finPart D (hO S T u w) = 0 := by
  have h0 : ∀ d a, finPart D (u d a) = 0 := fun d a => congrFun (congrFun hu d) a
  unfold hO
  simp only [map_sum (finPart D), map_mul (finPart D), h0, mul_zero, Finset.sum_const_zero]

set_option synthInstance.maxHeartbeats 200000 in
theorem symplO_fst_eq_zero (u w : MO S T) (hu : u.map (infPart D) = 0) : fstA D.host.F (symplO S T u w) = 0 := by
  unfold symplO
  refine trace_fst_eq_zero _ ?_
  rw [map_mul (infPart D), infPart_hO S T u w hu, mul_zero]

set_option synthInstance.maxHeartbeats 200000 in
theorem symplO_snd_eq_zero (u w : MO S T) (hu : u.map (finPart D) = 0) : sndA D.host.F (symplO S T u w) = 0 := by
  unfold symplO
  refine trace_snd_eq_zero _ ?_
  rw [map_mul (finPart D), finPart_hO S T u w hu, mul_zero]

theorem symplOH_snd_eq_zero (u w : MO S T) (hu : u.map (finPart D) = 0) : sndA D.host.F (symplOH S T u w) = 0 := by
  unfold symplOH
  rw [map_mul, symplO_snd_eq_zero S T u w hu, mul_zero]

def sndSympl (w : MO S T) : MO S T →+ Af D.host.F where
  toFun u := sndA D.host.F (symplO S T u w)
  map_zero' := by rw [symplO_zero_left, map_zero]
  map_add' u u' := by rw [symplO_add_left, map_add]

theorem heisStable : HeisStable D := by
  intro ψ hψ S T w f hf
  obtain ⟨G, hGo, -, hG⟩ := Formalism.IndefR.PHeisTh.psiOpen D.host.F ψ hψ.1
  obtain ⟨U, hUo, hU⟩ := hf.level
  let H : AddSubgroup (WO S T) := AddSubgroup.comap (sndSympl S T w) G
  have hHo : IsOpen (H : Set (WO S T)) :=
    hGo.preimage (continuous_snd.comp (cont_symplO_left S T w))
  refine ⟨fun γ z => ?_, ⟨U ⊓ H, ?_, fun u hu h0 => ?_⟩, cont_heis S T hψ hf w, fun k L hL hL0 x => ?_⟩
  ·
    unfold heisO
    rw [show ratW T S γ + z + w = ratW T S γ + (z + w) by abel, hf.quasi γ (z + w), ← mul_assoc,
      ← AddChar.map_add_eq_mul, ← mul_assoc, ← AddChar.map_add_eq_mul]
    have key : symplOH S T (ratW T S γ + z) w + -symplOH S T (ratW T S γ) (z + w) =
        -symplOH S T (ratW T S γ) z + symplOH S T z w := by
      rw [symplOH_add_left, symplOH_add_right]; ring
    rw [key]
  · rw [AddSubgroup.coe_inf]; exact hUo.inter hHo
  ·
    have hfu := hU u hu.1 h0
    have hc : ψ (symplO S T u w) = 1 := by
      have e : symplO S T u w = pairA D.host.F 0 (sndA D.host.F (symplO S T u w)) := by
        refine Prod.ext ?_ rfl
        exact symplO_fst_eq_zero S T u w h0
      rw [e]; exact hG _ hu.2
    funext z
    have k1 := congrFun hfu (z + w)
    unfold heisO at k1 ⊢
    have hfz : f (z + w + u) = ψ (-(symplOH S T (z + w) u)) * f (z + w) := by
      rw [AddChar.map_neg_eq_inv, ← k1]; field_simp [psi_ne hψ]
    rw [show z + u + w = z + w + u by abel, hfz, ← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul,
      ← AddChar.map_add_eq_mul]
    have key : symplOH S T z u + symplOH S T (z + u) w + -symplOH S T (z + w) u =
        symplOH S T z w + symplO S T u w := by
      rw [symplOH_add_left, symplOH_add_left, symplOH_swap S T u w, ← symplOH_two]; ring
    rw [key, AddChar.map_add_eq_mul, hc, mul_one]
  ·
    let s : (Fin k → ℝ) →+ Ainf D.host.F :=
      { toFun := fun t => fstA D.host.F (symplOH S T (L t) w)
        map_zero' := by simp only [map_zero]; unfold symplOH; rw [symplO_zero_left, mul_zero, map_zero]
        map_add' := fun t t' => by simp only [map_add]; rw [symplOH_add_left, map_add] }
    have hs : Continuous s := continuous_fst.comp ((cont_symplOH_left S T w).comp hL)
    have e : (fun t => heisO ψ S T w f (x + L t)) =
        fun t => ψ (symplOH S T x w) * ψ (pairA D.host.F (s t) 0) * f (x + w + L t) := by
      funext t
      unfold heisO
      have ep : symplOH S T (L t) w = pairA D.host.F (s t) 0 :=
        Prod.ext rfl (symplOH_snd_eq_zero S T (L t) w (hL0 t))
      rw [symplOH_add_left, AddChar.map_add_eq_mul, ep, show x + L t + w = x + w + L t by abel]
    rw [e]
    exact (contDiff_const.mul (Formalism.IndefR.PHeisTh.psiSmooth D ψ hψ k s hs)).mul (hf.smooth k L hL hL0 (x + w))

theorem svnSchurO_all_of_heis (hK : KernelId D) (h : HeisStable D) : SvNSchurOAll D :=
  svnSchurO_all_of hK h

theorem svnSchurO_all_of_char (hC : CharComplete D) : SvNSchurOAll D :=
  svnSchurO_all_of_heis (kernelId_of hC) heisStable

end Formalism.IndefR.Fin

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.LiftsCart
section
noncomputable section

namespace Formalism.IndefR.Fin.Lifts

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix Formalism.L2.Theta
open scoped ComplexOrder
open Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem posDef_of_sig {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) (h : Formalism.UG.HasSignature G n 0) : G.PosDef := by
  obtain ⟨e, P, hP⟩ := h
  have hJ : Formalism.UG.Jpq n 0 = 1 := by
    unfold Formalism.UG.Jpq
    rw [show (-1 : Matrix (Fin 0) (Fin 0) ℂ) = 1 by ext i; exact i.elim0, Matrix.fromBlocks_one]
  have hc : Formalism.UG.cT (starRingEnd ℂ) (P : Matrix (Fin n ⊕ Fin 0) (Fin n ⊕ Fin 0) ℂ) =
      star (P : Matrix (Fin n ⊕ Fin 0) (Fin n ⊕ Fin 0) ℂ) := by
    ext i j
    simp [Formalism.UG.cT, Matrix.star_apply]
  rw [hJ, hc] at hP
  have hU : IsUnit (P : Matrix (Fin n ⊕ Fin 0) (Fin n ⊕ Fin 0) ℂ) := P.isUnit
  have h1 : (G.reindex e e).PosDef := (Matrix.IsUnit.posDef_star_left_conjugate_iff hU).1 (hP ▸ Matrix.PosDef.one)
  have hG : G = (G.reindex e e).submatrix e e := by
    ext i j
    simp
  rw [hG]
  exact h1.submatrix e.injective

end Formalism.IndefR.Fin.Lifts

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end Formalism.IndefR.Fin

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.PlaceInst
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Matrix
open scoped TensorProduct

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D)

theorem isSBHalf_iff {e : AE D} {Λ : AddSubgroup (WO S T)} {Φ : WO S T → ℂ} :
    IsSBHalf e Λ Φ ↔ Four.IsSB Λ (halfSub S T e) Φ := by
  constructor
  · rintro ⟨hs, k, hk, hi, hl⟩
    exact ⟨hs, k, hk, fun u hu t => hi u (AddSubgroup.mem_inf.1 hu).1 (AddSubgroup.mem_inf.1 hu).2 t, hl⟩
  · rintro ⟨hs, k, hk, hi, hl⟩
    exact ⟨hs, k, hk, fun u hu hue t => hi u (AddSubgroup.mem_inf.2 ⟨hu, hue⟩) t, hl⟩

theorem finite_qt_of {H : AddSubgroup (WO S T)} {k : ℕ} (R : Finset (WO S T))
    (hR : ∀ u ∈ H, ∃ r ∈ R, ∃ v ∈ H, u = r + k • v) : Finite (Four.Qt k H) := by
  classical
  let R' : Finset (WO S T) := R.filter (· ∈ H)
  let f : R' → Four.Qt k H := fun r => QuotientAddGroup.mk ⟨r.1, (Finset.mem_filter.1 r.2).2⟩
  refine Finite.of_surjective f ?_
  intro q
  induction q using QuotientAddGroup.induction_on with
  | H u =>
    obtain ⟨r, hr, v, hv, huv⟩ := hR u u.2
    have hrH : r ∈ H := by
      have := H.sub_mem u.2 (H.nsmul_mem hv k)
      rwa [huv, add_sub_cancel_right] at this
    refine ⟨⟨r, Finset.mem_filter.2 ⟨hr, hrH⟩⟩, ?_⟩
    apply QuotientAddGroup.eq.2
    rw [AddSubgroup.mem_addSubgroupOf]
    refine Four.mem_smulSub.2 ⟨v, hv, ?_⟩
    simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg]
    rw [huv]
    abel

theorem nsmul_eq_zero_WO {k : ℕ} (hk : 0 < k) {t : WO S T} (h : k • t = 0) : t = 0 := by
  have hu : IsUnit (k : AE D) := by
    have e1 : (k : AE D) = algebraMap D.host.F (AE D) (k : D.host.F) := by simp
    rw [e1]
    exact (IsUnit.mk0 _ (Nat.cast_ne_zero.2 hk.ne')).map _
  ext i j
  have := congrFun (congrFun h i) j
  rw [Matrix.smul_apply, nsmul_eq_mul, Matrix.zero_apply] at this
  rw [Matrix.zero_apply]
  exact (hu.mul_right_eq_zero).1 this

open Classical in
theorem exists_placeModel (e₁ : AE D) (he : e₁ * cA D e₁ = 0) (Λ : AddSubgroup (WO S T)) (f₀ : WO S T → ℂ)
    (hLL : ∀ x ∈ Λ, IsHalf e₁ x → ∀ y ∈ Λ, IsHalf (cA D e₁) y → ψ (symplO S T x y) = 1)
    (hdY : ∀ y, IsHalf (cA D e₁) y → (∀ x ∈ Λ, IsHalf e₁ x → ψ (symplO S T x y) = 1) → y ∈ Λ)
    (hfX : ∀ k : ℕ, 0 < k → ∃ R : Finset (WO S T), ∀ u ∈ Λ, IsHalf e₁ u →
      ∃ r ∈ R, ∃ v ∈ Λ, IsHalf e₁ v ∧ u = r + k • v)
    (hfY : ∀ k : ℕ, 0 < k → ∃ R : Finset (WO S T), ∀ u ∈ Λ, IsHalf (cA D e₁) u →
      ∃ r ∈ R, ∃ v ∈ Λ, IsHalf (cA D e₁) v ∧ u = r + k • v)
    (hoX : ∀ x, IsHalf e₁ x → ∃ k : ℕ, 0 < k ∧ k • x ∈ Λ)
    (hoY : ∀ y, IsHalf (cA D e₁) y → ∃ k : ℕ, 0 < k ∧ k • y ∈ Λ)
    (hvX : ∀ u ∈ Λ, IsHalf e₁ u → heisO ψ S T u f₀ = f₀)
    (hvY : ∀ u ∈ Λ, IsHalf (cA D e₁) u → heisO ψ S T u f₀ = f₀) :
    ∃ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) e₁ Λ 1 f₀ Tm ∧
      ∀ Φ, IsSBHalf e₁ Λ Φ → Tm Φ = Four.tfun (heisL ψ S T) (fun t y => ψ (symplO S T t y)) Λ
        (halfSub S T e₁) (halfSub S T (cA D e₁)) f₀ Φ := by
  have mi := fun {x : WO S T} {H K : AddSubgroup (WO S T)} (h : x ∈ H ⊓ K) => AddSubgroup.mem_inf.1 h
  obtain ⟨Tm, hTe, htr, hmo, hva⟩ := Four.exists_model (ρ := heisL ψ S T) (χ := fun t y => ψ (symplO S T t y))
    (L := Λ) (X := halfSub S T e₁) (Y := halfSub S T (cA D e₁)) (f₀ := f₀)
    (hX := fun x hx x' hx' => heisL_add_half ψ S T he hx hx')
    (hY := fun y hy y' hy' => heisL_add_half ψ S T (cA_half_orth he) hy hy')
    (hXY := fun x _ y _ => heisL_comm ψ S T x y)
    (hχl := fun t t' y => by simp only [symplO_add_left, AddChar.map_add_eq_mul])
    (hχr := fun t y y' => by simp only [symplO_add_right, AddChar.map_add_eq_mul])
    (hχ0 := fun t y => psi_ne_zero ψ _)
    (hLL := fun x hx y hy => hLL x (mi hx).1 (mi hx).2 y (mi hy).1 (mi hy).2)
    (hdY := fun y hy h => hdY y hy fun x hx hxe => h x (AddSubgroup.mem_inf.2 ⟨hx, hxe⟩))
    (hfinX := fun k hk => by
      obtain ⟨R, hR⟩ := hfX k hk
      exact finite_qt_of S T R fun u hu => by
        obtain ⟨r, hr, v, hv, hve, huv⟩ := hR u (mi hu).1 (mi hu).2
        exact ⟨r, hr, v, AddSubgroup.mem_inf.2 ⟨hv, hve⟩, huv⟩)
    (hfinY := fun k hk => by
      obtain ⟨R, hR⟩ := hfY k hk
      exact finite_qt_of S T R fun u hu => by
        obtain ⟨r, hr, v, hv, hve, huv⟩ := hR u (mi hu).1 (mi hu).2
        exact ⟨r, hr, v, AddSubgroup.mem_inf.2 ⟨hv, hve⟩, huv⟩)
    (htf := fun k hk t h => nsmul_eq_zero_WO S T hk h)
    (hoX := fun x hx => hoX x hx) (hoY := fun y hy => hoY y hy)
    (hfX := fun u hu => hvX u (mi hu).1 (mi hu).2)
    (hfY := fun u hu => hvY u (mi hu).1 (mi hu).2)
  refine ⟨Tm, ⟨fun Φ hΦ x hx => ?_, fun Φ hΦ y hy => ?_, ?_⟩, fun Φ hΦ => hTe Φ ((isSBHalf_iff S T).1 hΦ)⟩
  · exact htr Φ ((isSBHalf_iff S T).1 hΦ) x hx
  · exact hmo Φ ((isSBHalf_iff S T).1 hΦ) y hy
  · rw [one_smul]
    exact hva

end Formalism.IndefR.Fin

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.TameAtOne
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def UnrOff (e : AE D) (χ : (AE D)ˣ →* Circle) : Prop :=
  ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → finPart D (x : AE D) ∈ intAE D →
    finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D → (e + cA D e) * (x : AE D) = e + cA D e → χ x = 1

def TameAt (e : AE D) (PP : Formalism.L2.DIV.Pl D.host.E) (χ : (AE D)ˣ →* Circle)
    (c : (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (k : ℤ) : Prop :=
  ∀ (x : (AE D)ˣ) (u : (↥(Formalism.L2.Herm.intAf D.host.F D.host.E))ˣ), (1 - e) * (x : AE D) = 1 - e →
    Datum.toEAf D (x : AE D) = ((u : ↥(Formalism.L2.Herm.intAf D.host.F D.host.E)) : Datum.EAf D) →
    ((χ x : Circle) : ℂ) = ((c (Units.map (Formalism.L2.DIV.resS D.host.F PP).toMonoidHom u) : ℂˣ) : ℂ) ^ k

def stepLev {n : ℕ} (LS : Formalism.L2.DIV.LevDat D.host.E ℂ n)
    (χj : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (m : ℕ) (hm : n ≤ m) :
    Formalism.L2.DIV.LevDat D.host.E ℂ m where
  r := LS.r
  hr := LS.hr.trans hm
  t := LS.t
  s := LS.s + 1
  Pg := LS.Pg
  Q := LS.Q
  P := LS.P
  cg := fun c => if c = LS.s + 1 then χj else LS.cg c
  xq := LS.xq

def thpLev (n r : ℕ) (hr : r ≤ n) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E))
    (μ ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) : Formalism.L2.DIV.LevDat D.host.E ℂ n where
  r := r
  hr := hr
  t := n - r
  s := 1
  Pg := Pg
  Q := Q
  P := Formalism.L2.DIV.LevelP.triv Pg r ℂ
  cg := fun _ => μ
  xq := ξ

open Classical in

def VecLawStep (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : Datum.InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (Datum.WO S T → ℂ))
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (pS pT : D.what₂.Tau → ℕ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D))
    (βT : GL (Fin T.rank) (Lev.EAf D)) (LS : Formalism.L2.DIV.LevDat D.host.E ℂ S.rank)
    (χj : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (Q : Finset (Formalism.L2.DIV.Pl D.host.E))
    (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (f₀ fF : Datum.WO S T → ℂ)
    (hST : S.rank ≤ T.rank),
    Datum.IsWeilDatumO ψ S T χS χT om → WeilFull.SphInertAtO ψ S T χS χT om →
    Datum.IsDatumStep ψ θ S T sS sT BS BT pS pT ΛS ΛT βS βT LS χj Q ξ f₀ fF →
    S.rank = LS.r + LS.s * LS.t → T.rank = S.rank + LS.t → Odd LS.t → LS.Q = Q → LS.xq = (fun PP => (ξ PP)⁻¹) →
    (∀ e, Datum.IsIdemSum e (LS.Pg ∪ Q) → UnrOff e χS ∧ UnrOff e χT) →
    (∀ PP ∈ LS.Pg, ∀ e, Formalism.L2.NTheta.IsIdemAt e PP → TameAt e PP χS (χj PP) (-1) ∧ TameAt e PP χT (χj PP) (-1)) →
    (∀ PP ∈ Q, ∀ e, Formalism.L2.NTheta.IsIdemAt e PP → TameAt e PP χS (ξ PP) 1 ∧ TameAt e PP χT (ξ PP) 1) →
    Datum.VecLaw om (Lev.levG S βS LS) (Lev.levChi S βS LS) (Lev.levG T βT (stepLev LS χj T.rank hST))
      (fun κ => (Lev.levChi T βT (stepLev LS χj T.rank hST) κ)⁻¹) fF

open Classical in

def VecLawThP (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : Datum.InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (Datum.WO S T → ℂ))
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (pS pT : D.what₂.Tau → ℕ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D))
    (βT : GL (Fin T.rank) (Lev.EAf D)) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E))
    (μ ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (f₀ fF : Datum.WO S T → ℂ)
    (hTS : T.rank < S.rank),
    Datum.IsWeilDatumO ψ S T χS χT om → WeilFull.SphInertAtO ψ S T χS χT om →
    Datum.IsDatumThP ψ θ S T sS sT BS BT pS pT ΛS ΛT βS βT Pg Q ξ f₀ fF → Odd (S.rank - T.rank) →
    (∀ e, Datum.IsIdemSum e (Pg ∪ Q) → UnrOff e χS ∧ UnrOff e χT) →
    (∀ PP ∈ Pg, ∀ e, Formalism.L2.NTheta.IsIdemAt e PP → TameAt e PP χS (μ PP) 1 ∧ TameAt e PP χT (μ PP) 1) →
    (∀ PP ∈ Q, ∀ e, Formalism.L2.NTheta.IsIdemAt e PP → TameAt e PP χS (ξ PP) 1 ∧ TameAt e PP χT (ξ PP) 1) →
    Datum.VecLaw om (Lev.levG S βS (thpLev S.rank T.rank hTS.le Pg Q μ ξ))
      (fun κ => (Lev.levChi S βS (thpLev S.rank T.rank hTS.le Pg Q μ ξ) κ)⁻¹)
      (Lev.levG T βT (Lev.datW T.rank Pg (Formalism.L2.DIV.LevelP.triv Pg T.rank ℂ) Lev.Frm.B)) (fun _ => 1) fF

open Classical in

def DiagLaw (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : Datum.InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (Datum.WO S T → ℂ))
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (pS pT : D.what₂.Tau → ℕ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D))
    (βT : GL (Fin T.rank) (Lev.EAf D)) (LS : Formalism.L2.DIV.LevDat D.host.E ℂ S.rank)
    (χj : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (Q : Finset (Formalism.L2.DIV.Pl D.host.E))
    (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (f₀ fF : Datum.WO S T → ℂ)
    (hST : S.rank ≤ T.rank),
    Datum.IsWeilDatumO ψ S T χS χT om → WeilFull.SphInertAtO ψ S T χS χT om →
    Datum.IsDatumStep ψ θ S T sS sT BS BT pS pT ΛS ΛT βS βT LS χj Q ξ f₀ fF →
    S.rank = LS.r + LS.s * LS.t → T.rank = S.rank + LS.t → Odd LS.t → LS.Q = Q → LS.xq = (fun PP => (ξ PP)⁻¹) →
    LS.P = Formalism.L2.DIV.LevelP.triv LS.Pg LS.r ℂ →
    (∀ e, Datum.IsIdemSum e (LS.Pg ∪ Q) → UnrOff e χS ∧ UnrOff e χT) →
    (∀ PP ∈ LS.Pg, ∀ e, Formalism.L2.NTheta.IsIdemAt e PP → TameAt e PP χS (χj PP) (-1) ∧ TameAt e PP χT (χj PP) (-1)) →
    (∀ PP ∈ Q, ∀ e, Formalism.L2.NTheta.IsIdemAt e PP → TameAt e PP χS (ξ PP) 1 ∧ TameAt e PP χT (ξ PP) 1) →
    ∀ κS ∈ Lev.levG S βS (Lev.flagL LS), ∀ κT ∈ Lev.levG T βT (Lev.flagL (stepLev LS χj T.rank hST)),
      Formalism.L2.DIV.rTup βS LS (Lev.finE S κS) = Formalism.L2.DIV.rTup βT (stepLev LS χj T.rank hST) (Lev.finE T κT) →
      om (κS, κT) fF = (Lev.levChi S βS (Lev.flagL LS) κS *
        (Lev.levChi T βT (Lev.flagL (stepLev LS χj T.rank hST)) κT)⁻¹) • fF

end Formalism.IndefR.Fin

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.ThetaFinsetSum
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem dRhoStable (D : D7) : DRhoStable D := by
  intro ψ θ hψ hθ S T τ z f hf
  exact (Formalism.IndefR.Fock.DRho.thetaDRho D ψ θ hψ hθ (Formalism.IndefR.Eqv.lineAtExists_holds D) S T τ z f hf).1

section Pt

variable {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

lemma theta_sub {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) :
    IsThetaFunO ψ S T (f - g) := by
  have := Formalism.IndefR.Fock.CCR.theta_add_smul hf hg (-1)
  simpa [sub_eq_add_neg] using this

lemma theta_finsetSum {ι : Type*} (s : Finset ι) (g : ι → WO S T → ℂ) (hg : ∀ i ∈ s, IsThetaFunO ψ S T (g i)) :
    IsThetaFunO ψ S T (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Formalism.IndefR.Fock.CCR.theta_zero ψ S T
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact Formalism.IndefR.Fock.CCR.theta_add (hg a (Finset.mem_insert_self a s))
      (ih fun i hi => hg i (Finset.mem_insert_of_mem hi))

lemma theta_opPow {ι : Type} (A : ι → (WO S T → ℂ) → (WO S T → ℂ))
    (hA : ∀ i g, IsThetaFunO ψ S T g → IsThetaFunO ψ S T (A i g)) (k : ι →₀ ℕ) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (opPow A k f) := by
  unfold opPow
  induction (Multiset.toList (Finsupp.toMultiset k)) with
  | nil => exact hf
  | cons i l ih => exact hA i _ ih

theorem ptStable (D : D7) : PtStable D := by
  intro ψ θ hψ hθ S T sS sT BS BT f P hf
  have hA : ∀ (i : FVar D T.rank S.rank) (g : WO S T → ℂ), IsThetaFunO ψ S T g →
      IsThetaFunO ψ S T (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT i g) := by
    intro i g hg
    unfold aPlusAll aPlus crea
    exact Formalism.IndefR.Fock.CCR.theta_smul
      (theta_sub (dRhoStable D ψ θ hψ hθ S T i.1 _ g hg)
        (Formalism.IndefR.Fock.CCR.theta_smul (dRhoStable D ψ θ hψ hθ S T i.1 _ g hg) _)) _
  unfold pureTensorO pureTensorL
  rw [Module.Basis.constr_apply, Finsupp.sum]
  exact theta_finsetSum _ _ fun k _ =>
    Formalism.IndefR.Fock.CCR.theta_smul (theta_opPow _ hA k hf) _

end Pt

end Formalism.IndefR.Fin
end
end

