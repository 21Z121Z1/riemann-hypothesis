import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0097
import Formalism.HermitianCurvature.HermitianCurvatureProofs.QuantumMinorExpansion
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0099
import Formalism.HermitianCurvature.Bundle0005
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0098
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0011
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0088
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGenTransferKPt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormalFormOrderZeroOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0081
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameEntries

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliVectorEquivariance
section
open Matrix Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.TL

open TLC in
theorem capelli_vector_equivariance : TL.CapVEquiv := by
  intro Wq _ _ _ k r z' π' B0 ν ν' h hk hz hT hπ hB0 hν hh hνν' w
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  obtain ⟨he, hez, hee⟩ := cap_vec hB0 hν
  set e := ∑ j, ν j • B0 j with hedef
  set g := h⁻¹ with hgdef
  have hg : g ∈ UWset (n + 1) r z' := LieBracketMultiplication.uw_inv hh
  have hgU : g ∈ UH (Hpk (n + 1) r) := hg.1
  have hgL : g ∈ Glev (n + 1) r (Fin.last r) := Qx8.uw_glev _ hg
  have hν' : C6.sq2 ν' = 1 := by
    have h1 : herm (Hpk (n + 1) r) (∑ j, ν' j • B0 j) (∑ j, ν' j • B0 j) = 1 := by
      rw [hνν', Qx2.herm_uh hgU, hee]
    rw [HermitianFormSums.herm_comb hB0] at h1
    have : ∀ a, ν' a * star (ν' a) = ((Complex.normSq (ν' a) : ℝ) : ℂ) := fun a => Complex.mul_conj (ν' a)
    simp only [this] at h1
    rw [← Complex.ofReal_sum] at h1
    exact_mod_cast h1
  obtain ⟨Bs, hBs⟩ := exists_frame_two n r z' e hz hT he hez hee
  set Bs' : Fin n → Fin (2 * r + (n + 1) + 1) → ℂ := fun a => g *ᵥ Bs a with hBs'def
  have hBs' : IsFrameOf (n + 1) r [z', ∑ j, ν' j • B0 j] Bs' := by
    refine ⟨fun a => Qx8.inWb_mulVec hgL (hBs.1 a), fun a b => ?_, fun a v hv => ?_⟩
    · rw [hBs'def, Qx2.herm_uh hgU]; exact hBs.2.1 a b
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl
      · have e1 := Qx2.herm_uh hgU (Bs a) v
        rw [hg.2.2] at e1
        rw [e1]; exact hBs.2.2 a _ (by simp)
      · rw [hνν', Qx2.herm_uh hgU]; exact hBs.2.2 a _ (by simp)
  have hF := capelli_vector_frame Wq (n + 1) r z' π' B0 Bs ν (by omega) hz hT hπ hB0 hν hBs w
  have hF' := capelli_vector_frame Wq (n + 1) r z' π' B0 Bs' ν' (by omega) hz hT hπ hB0 hν' hBs' w
  have hBs1 := HermitianFormSums.frame_sub hBs
  have hBs1' := HermitianFormSums.frame_sub hBs'
  have hq := (frame_general_linear Wq (n + 1) r n z' π' Bs hπ hBs1).2 w
  have hq' := (frame_general_linear Wq (n + 1) r n z' π' Bs' hπ hBs1').2 w
  have hgi : g⁻¹ = h := Matrix.nonsing_inv_nonsing_inv _ (WeylGroupFacts.isUnit_of_uh hh.1)
  have hgh : g * h = 1 := LeftDerivativeCurves.uh_inv_mul hh.1
  have hhg : h * g = 1 := LeftDerivativeCurves.uh_mul_inv hh.1
  have hUUi : (π' g).comp (π' h) = ContinuousLinearMap.id ℂ Wq := by
    rw [← hπ.1.2 _ hg _ hh, hgh, hπ.1.1]; rfl
  have hUiU : (π' h).comp (π' g) = ContinuousLinearMap.id ℂ Wq := by
    rw [← hπ.1.2 _ hh _ hg, hhg, hπ.1.1]; rfl
  set U : Module.End ℂ Wq := (π' g : Wq →ₗ[ℂ] Wq) with hU
  set Ui : Module.End ℂ Wq := (π' h : Wq →ₗ[ℂ] Wq) with hUi
  have hUUi' : U * Ui = 1 := by
    apply LinearMap.ext; intro v
    have := congrArg (fun T : Wq →L[ℂ] Wq => T v) hUUi
    simpa [hU, hUi] using this
  have hUiU' : Ui * U = 1 := by
    apply LinearMap.ext; intro v
    have := congrArg (fun T : Wq →L[ℂ] Wq => T v) hUiU
    simpa [hU, hUi] using this
  have hEB : ∀ a b, U * EB π' Bs a b * Ui = EB π' Bs' a b := by
    intro a b
    obtain ⟨hX1, hX2⟩ := QrD.frame_lie hBs1 a b
    obtain ⟨-, -, e1⟩ := differential_operator_adjoint Wq (n + 1) r z' π' hπ _ hX1 g hg
    obtain ⟨-, -, e2⟩ := differential_operator_adjoint Wq (n + 1) r z' π' hπ _ hX2 g hg
    obtain ⟨c1, c2⟩ := Qx8.hpart_conj Bs a b hgU
    unfold EB QrD.ecOp
    rw [c1, c2, e1, e2, hgi]
    apply LinearMap.ext; intro v
    simp [hU, hUi]
  let f : Module.End ℂ Wq →+* Module.End ℂ Wq :=
    { toFun := fun T => U * T * Ui
      map_one' := by simp only [mul_one, hUUi']
      map_mul' := fun S T => by
        show U * (S * T) * Ui = U * S * Ui * (U * T * Ui)
        calc U * (S * T) * Ui = U * S * (Ui * U) * T * Ui := by rw [hUiU']; noncomm_ring
          _ = U * S * Ui * (U * T * Ui) := by noncomm_ring
      map_zero' := by simp only [mul_zero, zero_mul]
      map_add' := fun S T => by noncomm_ring }
  have hf : ∀ v, f (algebraMap ℂ (Module.End ℂ Wq) v) = algebraMap ℂ (Module.End ℂ Wq) v := by
    intro v
    show U * algebraMap ℂ (Module.End ℂ Wq) v * Ui = _
    rw [← Algebra.commutes, mul_assoc, hUUi', mul_one]
  have hqd := QuantumMinorExpansion.map_qminor (EB π' Bs') f hf (EB π' Bs) (fun a b => hEB a b) id id w
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.comp_apply]
  rw [hF', hF, hq', hq]
  unfold qdet
  rw [← hqd]
  show U (qminor (EB π' Bs) id id w (Ui (π' h⁻¹ v))) = π' h⁻¹ (qminor (EB π' Bs) id id w v)
  have : Ui (π' h⁻¹ v) = v := by
    rw [← hgdef]
    have := congrArg (fun T : Wq →L[ℂ] Wq => T v) hUiU
    simpa [hUi] using this
  rw [this]
  rfl

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutBPEqWigMapsValueECas
section
open Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P.WigCas

open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Qr

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem cas_comm {A : Type*} [Ring A] {n : ℕ} {E : Fin n → Fin n → A} (hE : GlRel E) (c d : Fin n) :
    Cas E * E c d = E c d * Cas E := by
  have expand : Cas E * E c d - E c d * Cas E = ∑ a, ∑ b, (E a b * ((if a = c then E b d else 0) -
      (if d = b then E c a else 0)) + ((if b = c then E a d else 0) - (if d = a then E c b else 0)) * E b a) := by
    simp only [Cas, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    rw [← hE b a c d, ← hE a b c d]
    noncomm_ring
  have hT1 : ∑ a, ∑ b, E a b * (if a = c then E b d else 0) = ∑ b, E c b * E b d := by
    rw [Finset.sum_eq_single c (fun a _ ha => by simp [ha]) (by simp)]
    simp
  have hT4 : ∑ a, ∑ b, (if d = a then E c b else 0) * E b a = ∑ b, E c b * E b d := by
    rw [Finset.sum_eq_single d (fun a _ ha => by simp [Ne.symm ha]) (by simp)]
    simp
  have hT2 : ∑ a, ∑ b, E a b * (if d = b then E c a else 0) = ∑ a, E a d * E c a := by
    simp [mul_ite]
  have hT3 : ∑ a, ∑ b, (if b = c then E a d else 0) * E b a = ∑ a, E a d * E c a := by
    simp [ite_mul]
  rw [← sub_eq_zero, expand]
  simp only [mul_sub, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hT1, hT2, hT3, hT4]
  abel

def casV {n : ℕ} (ν : Fin n → ℂ) : ℂ := ∑ a, ν a ^ 2 + ∑ a, ∑ b, if a < b then ν a - ν b else 0

end Formalism.FourierDecayAlt.P.WigCas

end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTRTopAct
section
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

theorem top_action_on_gauge_holds : GTRTopAct := TopAct.gTRTopAct_of_cut quadratic_top_algebra_holds

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSLSliceSS
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

section closure

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq}

theorem sliceLoc_zero : SliceLoc P Bs 0 := by
  intro Φ Φ' c c' _ _ _ ζ _
  simp

theorem sliceLoc_add {T S : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} (hT : SliceLoc P Bs T)
    (hS : SliceLoc P Bs S) : SliceLoc P Bs (T + S) := by
  intro Φ Φ' c c' hc hc' h ζ hζ
  simp only [LinearMap.add_apply, Submodule.coe_add, Pi.add_apply]
  rw [hT Φ Φ' c c' hc hc' h ζ hζ, hS Φ Φ' c c' hc hc' h ζ hζ]

theorem sliceLoc_smul {T : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} (a : ℂ) (hT : SliceLoc P Bs T) :
    SliceLoc P Bs (a • T) := by
  intro Φ Φ' c c' hc hc' h ζ hζ
  simp only [LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply]
  rw [hT Φ Φ' c c' hc hc' h ζ hζ]

theorem sliceLoc_mul {T S : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} (hT : SliceLoc P Bs T)
    (hS : SliceLoc P Bs S) : SliceLoc P Bs (T * S) := by
  intro Φ Φ' c c' hc hc' h ζ hζ
  exact hT (S Φ) (S Φ') c c' hc hc' (hS Φ Φ' c c' hc hc' h) ζ hζ

theorem sliceLoc_sum {ι : Type} (s : Finset ι) (T : ι → Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))
    (hT : ∀ i ∈ s, SliceLoc P Bs (T i)) : SliceLoc P Bs (∑ i ∈ s, T i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    exact sliceLoc_zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact sliceLoc_add (hT i (Finset.mem_insert_self _ _)) (ih fun j hj => hT j (Finset.mem_insert_of_mem hj))

theorem sliceLoc_of_smul {T U : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} {a : ℂ} (ha : a ≠ 0)
    (hU : U = a • T) (h : SliceLoc P Bs U) : SliceLoc P Bs T := by
  have hTU : T = a⁻¹ • U := by rw [hU, smul_smul, inv_mul_cancel₀ ha, one_smul]
  rw [hTU]
  exact sliceLoc_smul _ h

end closure

open Formalism.FourierDecayAlt.P.NFx4.NO in
theorem second_shift_slice_operator : GTSSLSliceSS := by
  intro Wp Wq _ _ _ _ _ _ P Bs X d hH hT l hl
  have hP := hH.1.1
  have hRel := hH.2.2.2.2.2.1
  have hQQ := hH.2.2.2.2.2.2
  obtain ⟨Qr, hQ⟩ := gauge_kappa_pointwise_holds Wp Wq P Bs X d hH
  have hK : ∀ f : M.Ty P → ℂ, SliceLoc P Bs (d.κ f).1 := by
    intro f Φ Φ' c c' hc hc' h ζ hζ
    have e1 := hQ.2.2.2 f Φ ⟨(c, ζ), ⟨hc, hζ⟩⟩
    have e2 := hQ.2.2.2 f Φ' ⟨(c', ζ), ⟨hc', hζ⟩⟩
    simp only at e1 e2
    rw [e1, e2, h ζ hζ]
  have hPj : ∀ ρ, SliceLoc P Bs (Pj d ρ).1 := fun ρ => hK _
  have e10 : ∀ Y, X.t Y 1 0 = (d.QQ Y 1 0).1 := fun Y => by rw [← hQQ Y]; rfl
  have e01 : ∀ Y, X.t Y 0 1 = (d.QQ Y 0 1).1 := fun Y => by rw [← hQQ Y]; rfl
  refine ⟨?_, ?_⟩
  · have hdec : (d.SS l).1 = ∑ a, ∑ b, (Pj d a * d.SS l * Pj d b).1 := by
      have h := congrArg (fstA _) (decomp d (d.SS l))
      simp only [map_sum] at h
      exact h
    rw [hdec]
    refine sliceLoc_sum _ _ fun a _ => sliceLoc_sum _ _ fun b _ => ?_
    by_cases hUp : M.Up P l b a
    · set Y : ℂ := -(M.rho P b l : ℂ) with hY
      have hc0 : M.xEx P {l} b Y ≠ 0 := by
        unfold M.xEx
        refine Finset.prod_ne_zero_iff.2 fun i hi => ?_
        have hi' := Finset.mem_sdiff.1 hi
        have hne : M.rho P b i ≠ M.rho P b l :=
          rho_ne P hP b hi'.1 hl (fun e => hi'.2 (by simp [e]))
        intro h0
        apply hne
        have : ((M.rho P b i : ℝ) : ℂ) = ((M.rho P b l : ℝ) : ℂ) := by rw [hY] at h0; linear_combination h0
        exact_mod_cast this
      have hE : (Pj d a).1 * X.t Y 1 0 * (Pj d b).1 = M.xEx P {l} b Y • (Pj d a * d.SS l * Pj d b).1 := by
        have h := congrArg (fstA _) (B1 hRel hl hUp Y)
        rw [map_mul, map_mul, map_smul] at h
        rw [e10]
        exact h
      exact sliceLoc_of_smul hc0 hE (sliceLoc_mul (sliceLoc_mul (hPj a) (hT Y 1 0)) (hPj b))
    · rw [block_zero hRel hUp]
      exact sliceLoc_zero
  · have hdec : (star (d.SS l)).1 = ∑ a, ∑ b, (Pj d a * star (d.SS l) * Pj d b).1 := by
      have h := congrArg (fstA _) (decomp d (star (d.SS l)))
      simp only [map_sum] at h
      exact h
    rw [hdec]
    refine sliceLoc_sum _ _ fun a _ => sliceLoc_sum _ _ fun b _ => ?_
    by_cases hUp : M.Up P l a b
    · set Y : ℂ := -(M.rho P b l : ℂ) with hY
      have hc0 : M.xEx P {l} a Y ≠ 0 := by
        unfold M.xEx
        refine Finset.prod_ne_zero_iff.2 fun i hi => ?_
        have hi' := Finset.mem_sdiff.1 hi
        have hil : i ≠ l := fun e => hi'.2 (by simp [e])
        have hup := Formalism.FourierDecayAlt.P.Mx3.rhoUp P l a b hUp i hi'.1
        rw [if_neg hil, add_zero] at hup
        have hne : M.rho P b i ≠ M.rho P b l := rho_ne P hP b hi'.1 hl hil
        intro h0
        apply hne
        have : ((M.rho P b i : ℝ) : ℂ) = ((M.rho P b l : ℝ) : ℂ) := by
          rw [hY] at h0; rw [hup]; linear_combination h0
        exact_mod_cast this
      have hE : (Pj d a).1 * X.t Y 0 1 * (Pj d b).1 = M.xEx P {l} a Y • (Pj d a * star (d.SS l) * Pj d b).1 := by
        have h := congrArg (fstA _) (B4 hRel hl hUp Y)
        rw [map_mul, map_mul, map_smul] at h
        rw [e01]
        exact h
      exact sliceLoc_of_smul hc0 hE (sliceLoc_mul (sliceLoc_mul (hPj a) (hT Y 0 1)) (hPj b))
    · rw [star_block_zero hRel hUp]
      exact sliceLoc_zero

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreKLLieGrp
section
open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.QrD

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

namespace KLR

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

theorem exp_intertwine {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] [FiniteDimensional ℂ Wq] (A : Wq →L[ℂ] Wp) (D' : Wq →L[ℂ] Wq)
    (D : Wp →L[ℂ] Wp) (h : A.comp D' = D.comp A) :
    A.comp (NormedSpace.exp D') = (NormedSpace.exp D).comp A := by
  have : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  have : CompleteSpace Wq := FiniteDimensional.complete ℂ Wq
  have hp : ∀ n : ℕ, A.comp (D' ^ n) = (D ^ n).comp A := by
    intro n
    induction n with
    | zero => ext v; simp
    | succ n ih =>
      ext v
      have e1 := congrArg (fun T : Wq →L[ℂ] Wp => T (D' v)) ih
      have e2 := congrArg (fun T : Wq →L[ℂ] Wp => T v) h
      simp only [ContinuousLinearMap.comp_apply] at e1 e2 ⊢
      rw [pow_succ, pow_succ, ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, e1, e2]
  have h1 := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) D'
  have h2 := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) D
  have g1 := h1.map (ContinuousLinearMap.compL ℂ Wq Wq Wp A) (ContinuousLinearMap.continuous _)
  have g2 := h2.map ((ContinuousLinearMap.compL ℂ Wq Wp Wp).flip A) (ContinuousLinearMap.continuous _)
  have e : ((ContinuousLinearMap.compL ℂ Wq Wq Wp A) ∘ fun n : ℕ => ((n.factorial : ℂ)⁻¹) • D' ^ n) =
      (((ContinuousLinearMap.compL ℂ Wq Wp Wp).flip A) ∘ fun n : ℕ => ((n.factorial : ℂ)⁻¹) • D ^ n) := by
    funext n
    simp only [Function.comp_apply, ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp, hp]
  rw [e] at g1
  exact g1.unique g2

theorem exp_conj {g : Mx k r} (hg : IsUnit g.det) (X : Mx k r) :
    NormedSpace.exp (g * X * g⁻¹) = g * NormedSpace.exp X * g⁻¹ := by
  have h := HermitianFormRankFour.exp_semiconj (g * X * g⁻¹) X g (by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hg, Matrix.mul_one])
  calc NormedSpace.exp (g * X * g⁻¹) = NormedSpace.exp (g * X * g⁻¹) * g * g⁻¹ := by
        rw [Matrix.mul_assoc (NormedSpace.exp (g * X * g⁻¹)) g g⁻¹, Matrix.mul_nonsing_inv _ hg, Matrix.mul_one]
    _ = g * NormedSpace.exp X * g⁻¹ := by rw [h]

theorem pi_exp_frame {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
    {z : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (W →L[ℂ] W)} (hπ : Qr.IsRepW k r z π) {m : ℕ}
    {Bs : Fin m → Fin (2 * r + k + 1) → ℂ} (hB : IsFrameOf k r [z] Bs) (B : Matrix (Fin m) (Fin m) ℂ)
    (hBs : Bᴴ = -B) :
    InLieW k r z (∑ p : Fin m × Fin m, B p.1 p.2 • unitB (Hpk k r) Bs p.1 p.2) ∧
    π (NormedSpace.exp (∑ p : Fin m × Fin m, B p.1 p.2 • unitB (Hpk k r) Bs p.1 p.2)) =
      NormedSpace.exp (∑ p : Fin m × Fin m, B p.1 p.2 • ecOp π (unitB (Hpk k r) Bs p.1 p.2)) := by
  obtain ⟨X, hX⟩ : ∃ X, X = ∑ p : Fin m × Fin m, B p.1 p.2 • unitB (Hpk k r) Bs p.1 p.2 := ⟨_, rfl⟩
  rw [← hX]
  have hsk : Xᴴ * Hpk k r + Hpk k r * X = 0 := by
    rw [hX, ← KLG.sum_unitB]
    exact HermitianFormRankFour.skew_of Qx8.hpk_herm hBs
  have hs := HermitianFormSums.ec_sum elementary_lie_elements hπ Finset.univ (fun p : Fin m × Fin m => B p.1 p.2)
    (fun p => unitB (Hpk k r) Bs p.1 p.2) (fun p => frame_lie hB p.1 p.2) 0 (SkewHermitianParts.inGl_zero z)
  beta_reduce at hs
  rw [← hX] at hs
  have hL : InLieW k r z X := by
    have := hs.1.1
    rwa [SkewHermitianParts.hpart1_skew hsk] at this
  have he : ecOp π X = dOp π X := by
    unfold ecOp
    rw [SkewHermitianParts.hpart1_skew hsk, SkewHermitianParts.hpart2_skew hsk, SkewHermitianParts.dOp_zero, smul_zero, add_zero]
  refine ⟨hL, ?_⟩
  have h2 := representation_exp W k r z π hπ X hL 1
  simp only [Complex.ofReal_one, one_smul] at h2
  rw [h2, ← he, hs.2]

end KLR

open KLR in
theorem lie_group_realization : KLLieGrp := by
  intro Wp Wq _ _ _ _ _ _ k r z z' π π' hz hz' hT hT' hπ hπ' g hg hGG Fr hFr A hA h hh h' hh' hgh
  have hgu := hg.1
  have hgU : IsUnit g.det := WeylGroupFacts.isUnit_of_uh hgu
  have hhU : IsUnit h.det := WeylGroupFacts.isUnit_of_uh hh.1
  have cancel : ∀ M : Mx k r, IsUnit M.det → ∀ v, M⁻¹ *ᵥ (M *ᵥ v) = v := fun M hM v => by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hM, Matrix.one_mulVec]
  obtain ⟨y, hy⟩ : ∃ y, y = g⁻¹ *ᵥ z := ⟨_, rfl⟩
  rw [← hy] at hFr
  have hgy : g *ᵥ y = z := by rw [hy]; exact Qx8.inv_mulVec_uh hgu z
  have hginv : g⁻¹ ∈ Glev k r (Fin.last r) := FrameEntries.glev_inv hg
  have hyW : inWb k r y := by rw [hy]; exact Qx8.inWb_mulVec hginv hz
  have hyy : herm (Hpk k r) y y = -((Tz k r z : ℝ) : ℂ) := by
    rw [← Qx8.herm_self', ← hgy, Qx8.herm_UH hgu]
  have hζ : herm (Hpk k r) z' y = zetaL k r z z' (Fin.last r) g := by
    unfold zetaL
    rw [Qx8.fvec_last, Qx8.fvec_last, ← hgy, Qx8.herm_UH hgu]
  have hpos := Qx8.GGl_pos hz hz' hT hT' hg hGG
  have hG2 : 0 < Complex.normSq (herm (Hpk k r) y z') - Tz k r z * Tz k r z' := by
    rw [← Qx8.herm_conj, hζ]
    have hc : Complex.normSq (star (zetaL k r z z' (Fin.last r) g)) = Complex.normSq (zetaL k r z z' (Fin.last r) g) :=
      Complex.normSq_conj _
    rw [hc]
    exact hpos
  obtain ⟨e', s, c, hs, he', he'W, he'z, he'e⟩ := Qx8.orth_unit hyW hz' hT' hyy (Qx8.herm_self' z') hG2
  have hFz' : ∀ a, herm (Hpk k r) (Fr a) z' = 0 := fun a => hFr.2.2 a z' (by simp)
  have hFy : ∀ a, herm (Hpk k r) (Fr a) y = 0 := fun a => hFr.2.2 a y (by simp)
  have hFe : ∀ a, herm (Hpk k r) (Fr a) e' = 0 := by
    intro a
    rw [he', Qx8.herm_smul_right', Qx8.herm_add_right', Qx8.herm_smul_right', hFy, hFz']
    simp
  have hFr2 : IsFrameOf k r [z', e'] Fr := ⟨hFr.1, hFr.2.1, fun a v hv => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact hFz' a
    · exact hFe a⟩
  have hFz'1 : IsFrameOf k r [z'] Fr := ⟨hFr.1, hFr.2.1, fun a v hv => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    subst hv
    exact hFz' a⟩

  have e1 : h *ᵥ (g *ᵥ (h' *ᵥ y)) = h *ᵥ z := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hgh, hgy, hh.2.2]
  have e2 : g *ᵥ (h' *ᵥ y) = z := by
    rw [← cancel h hhU (g *ᵥ (h' *ᵥ y)), e1, cancel h hhU z]
  have hh'y : h' *ᵥ y = y := by
    calc h' *ᵥ y = g⁻¹ *ᵥ (g *ᵥ (h' *ᵥ y)) := (cancel g hgU _).symm
      _ = y := by rw [e2, hy]
  have hh'e : h' *ᵥ e' = e' := by
    rw [he', Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul, hh'y, hh'.2.2]

  obtain ⟨B, hBs, hBe⟩ := KLG.stab_exp hz' hT' he'W he'z he'e hFr2 hh' hh'e
  rw [KLG.sum_unitB] at hBe
  obtain ⟨-, hE'⟩ := pi_exp_frame hπ' hFz'1 B hBs
  have hgF : IsFrameOf k r [z] (fun a => g *ᵥ Fr a) := ⟨fun a => Qx8.inWb_mulVec hg (hFr.1 a), fun a b => by
    rw [Qx8.herm_UH hgu]; exact hFr.2.1 a b, fun a v hv => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    subst hv
    rw [← hgy, Qx8.herm_UH hgu]
    exact hFy a⟩
  obtain ⟨hL, hE⟩ := pi_exp_frame hπ hgF B hBs
  have hconj : g * h' * g⁻¹ = NormedSpace.exp
      (∑ p : Fin (k - 1) × Fin (k - 1), B p.1 p.2 • unitB (Hpk k r) (fun a => g *ᵥ Fr a) p.1 p.2) := by
    have hsum : (∑ p : Fin (k - 1) × Fin (k - 1), B p.1 p.2 • unitB (Hpk k r) (fun a => g *ᵥ Fr a) p.1 p.2) =
        g * (∑ p : Fin (k - 1) × Fin (k - 1), B p.1 p.2 • unitB (Hpk k r) Fr p.1 p.2) * g⁻¹ := by
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Matrix.mul_smul, Matrix.smul_mul, Qx8.unitB_conj Fr p.1 p.2 hgu]
    rw [hsum, ← hBe]
    exact (exp_conj hgU _).symm
  have hD : A.comp (∑ p : Fin (k - 1) × Fin (k - 1), B p.1 p.2 • ecOp π' (unitB (Hpk k r) Fr p.1 p.2)) =
      (∑ p : Fin (k - 1) × Fin (k - 1), B p.1 p.2 • ecOp π (unitB (Hpk k r) (fun a => g *ᵥ Fr a) p.1 p.2)).comp A := by
    ext v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      map_sum, map_smul]
    refine Finset.sum_congr rfl fun p _ => ?_
    congr 1
    exact hA p.1 p.2 v
  have hX := exp_intertwine A _ _ hD
  rw [← hE', ← hE, hBe, ← hconj] at hX
  have hmem : g * h' * g⁻¹ ∈ UWset k r z := by
    rw [hconj]
    have := exp_uw hL 1
    simpa using this
  have hone : h * (g * h' * g⁻¹) = 1 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hgh, Matrix.mul_nonsing_inv _ hgU]
  rw [hX, ← ContinuousLinearMap.comp_assoc, ← hπ.1.2 h hh _ hmem, hone, hπ.1.1]
  ext v
  simp

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepThConstS
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC

noncomputable section

def PolyRadialS : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    2 ≤ P.k → ∀ (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    ActHyp P Bs X d → ∀ l ∈ Finset.Icc 1 (P.k - 1), ∀ S, IsSSPt P Bs d l S →
    ∀ Pr, PRho.PRhoSpec P Bs.z Bs.π Pr →
    ∀ Bw Bw' : Fin P.k → Fin (2 * P.r + P.k + 1) → ℂ, Q.IsFrameOf P.k P.r [Bs.z] Bw → Q.IsFrameOf P.k P.r [Bs.z'] Bw' →
    ∀ π ρ : M.Ty P, M.Up P l π ρ → ∃ (n : ℕ) (q : Polynomial ℂ), ∀ ζ ∈ Gauge.GC.Ann P,
      ∀ Xf ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ,
        (Pr π (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp Xf = Xf →
        (((Complex.normSq ζ - P.TT : ℝ) : ℂ) ^ n) • (Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp (S ζ Xf) =
          q.eval ((Real.sqrt (Complex.normSq ζ - P.TT) : ℝ) : ℂ) • (Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp
            (tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)
              (SSn.nu0' P.k P.r Bs.z Bs.z' Bs.μsec ζ) (SSn.io0 P.k P.r Bs.z Bs.z' Bs.μsec ζ) Xf)

def ThConstOfCutS : Prop := PolyRadialS → ModConst → LineNonzero → PolyFinish → ThConst

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC
end

