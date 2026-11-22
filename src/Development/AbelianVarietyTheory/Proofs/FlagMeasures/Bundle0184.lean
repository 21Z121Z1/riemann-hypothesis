import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0178
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointLatticeIntersectionSelfDualProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointRationalEquivariance
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermExponentsNonnegAndDefectGroupBound
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0082
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0046
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0026
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0100
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0035
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0040
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermInvariantsIndependentOfWitnesses
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0080
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0064
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0061
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0173
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselOpNormPowerIntegralLtTopClosedSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0170
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0171
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CmEulerProductDiscrUnramified
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0002
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0172

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdjointMemAndExistsIntegralPoint
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.RadCov.RatElt

theorem hform_eq {E : Type} [CommRing E] [StarRing E] {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (x y : Fin n → E) : Formalism.UG.hform (starRingEnd E) J x y = star x ⬝ᵥ (J *ᵥ y) := by
  simp only [Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, starRingEnd_apply,
    mul_assoc]

theorem cT_eq {E : Type} [CommRing E] [StarRing E] {n : ℕ} (M : Matrix (Fin n) (Fin n) E) :
    Formalism.UG.cT (starRingEnd E) M = Mᴴ := by
  ext i j
  simp [Formalism.UG.cT, conjTranspose_apply, starRingEnd_apply]

theorem unitary_map {A B : Type} [CommRing A] [CommRing B] {n : ℕ} (σ : A →+* A) (τ : B →+* B)
    (f : A →+* B) (hf : ∀ e, τ (f e) = f (σ e)) (J g : Matrix (Fin n) (Fin n) A)
    (h : Formalism.UG.cT σ g * J * g = J) : Formalism.UG.cT τ (g.map f) * J.map f * g.map f = J.map f := by
  have hc : Formalism.UG.cT τ (g.map f) = (Formalism.UG.cT σ g).map f := by
    ext i j
    simp [Formalism.UG.cT, hf]
  rw [hc, ← Matrix.map_mul, ← Matrix.map_mul, h]

theorem exists_point (I : AutInst) (γ : GL (Fin I.n) I.E)
    (hγ : γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J) : ∃ a : I.GA,
      (∀ v, uMat (a.1 v) = (I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v) ∧
      I.fmat a.2 = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F)) := by
  have hUJ : Formalism.UG.cT (starRingEnd I.E) (γ : Matrix (Fin I.n) (Fin I.n) I.E) * I.J * γ = I.J := hγ
  have hγH : (γ : Matrix (Fin I.n) (Fin I.n) I.E)ᴴ * I.J * γ = I.J := by rwa [cT_eq] at hUJ
  let γA : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F)) :=
    Units.map (RingHom.mapMatrix (Formalism.UG.inclE (F := I.F) (Af I.F))).toMonoidHom γ
  have hγA : (γA : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) =
      (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F)) := rfl
  have hA : γA ∈ Formalism.UG.UPts I.cm.sig I.J (Af I.F) := by
    unfold Formalism.UG.UPts
    show Formalism.UG.cT (Formalism.UG.sigR I.cm.sig (Af I.F)) (γA : Matrix (Fin I.n) (Fin I.n) _) *
        I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) * γA = I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F))
    rw [hγA]
    exact unitary_map (starRingEnd I.E) _ _ (fun e => Formalism.UG.P.csDual_sig_incl I.cm.sig e) _ _ hUJ

  let Mu : ∀ v, (Matrix (Fin I.n) (Fin I.n) ℂ)ˣ := fun v =>
    (I.P_unit v).unit⁻¹ * Units.map (RingHom.mapMatrix (I.φ v)).toMonoidHom γ * (I.P_unit v).unit
  have hMu : ∀ v, (Mu v : Matrix (Fin I.n) (Fin I.n) ℂ) =
      (I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v := by
    intro v
    simp only [Mu, Units.val_mul, Matrix.coe_units_inv, IsUnit.unit_spec]
    rfl
  have hU : ∀ v, Mu v ∈ Formalism.REAL.UJ (I.ε v) := by
    intro v
    show Formalism.REAL.inUJ (I.ε v) (Mu v : Matrix (Fin I.n) (Fin I.n) ℂ)
    unfold Formalism.REAL.inUJ
    set Q := I.P v with hQdef
    set G := (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) with hGdef
    have hQ : Q * Q⁻¹ = 1 :=
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v))
    have hQH : Q⁻¹ᴴ * Qᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hQ, Matrix.conjTranspose_one]
    have hGH : Gᴴ = (γ : Matrix (Fin I.n) (Fin I.n) I.E)ᴴ.map (I.φ v) := by
      ext i j
      simp only [G, conjTranspose_apply, Matrix.map_apply]
      rw [I.cm.cmUnram.2.1 (I.φ v)]
      rfl
    have hGJG : Gᴴ * (I.J.map (I.φ v) * (G * Q)) = I.J.map (I.φ v) * Q := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hGH, hGdef, ← Matrix.map_mul, ← Matrix.map_mul, hγH]
    rw [hMu, ← I.P_spec v, ← hQdef, ← hGdef, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Q⁻¹ᴴ Qᴴ, hQH, Matrix.one_mul, ← Matrix.mul_assoc Q Q⁻¹, hQ, Matrix.one_mul, hGJG]
  exact ⟨⟨fun v => ⟨Mu v, hU v⟩, ⟨γA, hA⟩⟩, fun v => hMu v, hγA⟩

theorem adj_mem (I : AutInst) (x : I.GA) (T : Matrix (Fin I.n) (Fin I.n) I.E)
    (hT : ∀ y ∈ lamX I x, T *ᵥ y ∈ lamX I x) : ∀ y ∈ lamX I x, (I.J⁻¹ * Tᴴ * I.J) *ᵥ y ∈ lamX I x := by
  intro y hy
  obtain ⟨-, -, -, hdual, -⟩ := GlobalTheory.PointLattice.lamX_selfDual I x
  rw [hdual]
  intro z hz
  have hJ : I.J * I.J⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr I.J_det)
  have key : Formalism.UG.hform (starRingEnd I.E) I.J z ((I.J⁻¹ * Tᴴ * I.J) *ᵥ y) =
      Formalism.UG.hform (starRingEnd I.E) I.J (T *ᵥ z) y := by
    have hM : I.J * (I.J⁻¹ * Tᴴ * I.J) = Tᴴ * I.J := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hJ, Matrix.one_mul]
    rw [hform_eq, hform_eq, Matrix.mulVec_mulVec, hM, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      Matrix.star_mulVec]
  rw [key]
  exact (hdual y).1 hy _ (hT z hz)

private lemma inv_mul_map_inclE_of_mem_lf (I : AutInst) (xf : I.Gf) (δ : Matrix (Fin I.n) (Fin I.n) I.E)
    (hδ : ∀ y ∈ lamX I (1, xf), δ *ᵥ y ∈ lamX I (1, xf))
    (x : Fin I.n → (TensorProduct I.F I.E (Af I.F))) (hx : x ∈ I.Lf) :
    ((((xf : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F)))⁻¹ : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) * δ.map (Formalism.UG.inclE (F := I.F) (Af I.F)) * ((xf : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F)))) *ᵥ x ∈ I.Lf := by
  set g : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F)) := (xf : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) with hg
  have hL : I.Lf = Formalism.UG.latS (F := I.F) (Af I.F) (IntAf I.F I.E) I.L := by
    unfold AutInst.Lf lamAf Formalism.UG.latS
    rw [Set.image_eq_range]
    rfl
  have hfin : Module.Finite (𝓞 I.E) I.L := Module.Finite.iff_fg.mpr I.L_fg
  have hrec := Formalism.UG.P.span_recovery_of_integral_adelic_approx Formalism.UG.P.integral_adele_approximation_holds I.F I.E (Fin I.n) I.L hfin I.L_span g
  have hglob : Formalism.UG.CS.globLat g I.L = lamX I (1, xf) := (GlobalTheory.PointLattice.lamX_eq_globLat I (1, xf)).symm
  rw [hglob] at hrec

  have hspan : ∀ w ∈ Submodule.span (IntAf I.F I.E) ((fun y : Fin I.n → I.E => fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (y i)) ''
        (lamX I (1, xf) : Set (Fin I.n → I.E))),
      δ.map (Formalism.UG.inclE (F := I.F) (Af I.F)) *ᵥ w ∈ Submodule.span (IntAf I.F I.E) ((fun y : Fin I.n → I.E => fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (y i)) ''
        (lamX I (1, xf) : Set (Fin I.n → I.E))) := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨y, hy, rfl⟩ := hw
      apply Submodule.subset_span
      refine ⟨δ *ᵥ y, hδ y hy, ?_⟩
      funext i
      exact RingHom.map_mulVec _ _ _ _
    | zero => simp
    | add w₁ w₂ _ _ h₁ h₂ =>
      rw [Matrix.mulVec_add]
      exact add_mem h₁ h₂
    | smul s w _ h =>
      rw [Matrix.mulVec_smul]
      exact Submodule.smul_mem _ s h
  have hu := (hrec ((g : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) *ᵥ x)).2 (by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec, ← hL]
    exact hx)
  have h2 := (hrec _).1 (hspan _ hu)
  rw [← hL] at h2
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  exact h2

theorem adj_mem_and_exists_latGroup : ∀ (I : AutInst) (xf : I.Gf), (∀ T : Matrix (Fin I.n) (Fin I.n) I.E, (∀ y ∈ lamX I (1, xf), T *ᵥ y ∈ lamX I (1, xf)) → ∀ y ∈ lamX I (1, xf), (I.J⁻¹ * Tᴴ * I.J) *ᵥ y ∈ lamX I (1, xf)) ∧ ∀ γ : Matrix (Fin I.n) (Fin I.n) I.E, γᴴ * I.J * γ = I.J → (∀ y ∈ lamX I (1, xf), γ *ᵥ y ∈ lamX I (1, xf)) → ∃ g ∈ latGroup I xf, ∀ v, uMat (g v) = (I.P v)⁻¹ * γ.map (I.φ v) * I.P v := by
  intro I xf
  refine ⟨fun T hT => adj_mem I (1, xf) T hT, ?_⟩
  intro γ hγJ hγL
  have hdet : γ.det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det hγJ
    rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at h1
    exact I.J_det h1.symm
  let γu : GL (Fin I.n) I.E := Matrix.nonsingInvUnit γ (isUnit_iff_ne_zero.mpr hdet)
  have hγu : (γu : Matrix (Fin I.n) (Fin I.n) I.E) = γ := rfl
  have hmemUJ : γu ∈ Formalism.UG.UJ (starRingEnd I.E) I.J := by
    show Formalism.UG.cT (starRingEnd I.E) (γu : Matrix (Fin I.n) (Fin I.n) I.E) * I.J * γu = I.J
    rw [cT_eq, hγu]
    exact hγJ
  obtain ⟨a, ha1, ha2⟩ := exists_point I γu hmemUJ
  refine ⟨a.1, ⟨a, ⟨γu, hmemUJ, ha1, ha2⟩, rfl, ?_⟩, ha1⟩
  have hδγ : (I.J⁻¹ * γᴴ * I.J) * γ = 1 := by
    rw [show (I.J⁻¹ * γᴴ * I.J) * γ = I.J⁻¹ * (γᴴ * I.J * γ) by simp only [Matrix.mul_assoc], hγJ,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr I.J_det)]
  have hδγA : (I.J⁻¹ * γᴴ * I.J).map (Formalism.UG.inclE (F := I.F) (Af I.F)) * γ.map (Formalism.UG.inclE (F := I.F) (Af I.F)) = 1 := by
    rw [← Matrix.map_mul, hδγ]
    simp
  have ha2' : ((a.2 : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) = γ.map (Formalism.UG.inclE (F := I.F) (Af I.F)) := by
    rw [← hγu]
    exact ha2
  set g : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F)) := (xf : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) with hg
  have hmat : (((xf⁻¹ * a.2 * xf : I.Gf) : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) =
      ((g⁻¹ : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) * γ.map (Formalism.UG.inclE (F := I.F) (Af I.F)) * (g : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) := by
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv, Units.val_mul]
    rw [ha2']
  have hprod : (((g⁻¹ : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) * (I.J⁻¹ * γᴴ * I.J).map (Formalism.UG.inclE (F := I.F) (Af I.F)) * (g : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F)))) *
      (((g⁻¹ : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) * γ.map (Formalism.UG.inclE (F := I.F) (Af I.F)) * (g : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F)))) = 1 := by
    calc _ = ((g⁻¹ : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) * ((I.J⁻¹ * γᴴ * I.J).map (Formalism.UG.inclE (F := I.F) (Af I.F)) *
            ((g : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) * ((g⁻¹ : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F)))) * γ.map (Formalism.UG.inclE (F := I.F) (Af I.F))) * (g : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [Units.mul_inv, Matrix.mul_one, hδγA, Matrix.mul_one, Units.inv_mul]
  show ((xf⁻¹ * a.2 * xf : I.Gf) : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) ∈ Formalism.UG.stabGL I.Lf
  unfold Formalism.UG.stabGL
  intro x
  show x ∈ I.Lf ↔ (((xf⁻¹ * a.2 * xf : I.Gf) : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) *ᵥ x ∈ I.Lf
  rw [hmat]
  constructor
  · intro hx
    exact inv_mul_map_inclE_of_mem_lf I xf γ hγL x hx
  · intro hx
    have h1 := inv_mul_map_inclE_of_mem_lf I xf (I.J⁻¹ * γᴴ * I.J) (adj_mem I (1, xf) γ hγL) _ hx
    rwa [Matrix.mulVec_mulVec, hprod, Matrix.one_mulVec] at h1

end GlobalTheory.RadCov.RatElt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmpSqLeHeightMulMass
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.NoCancellation

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] {L : LocE F E}
  {r k : ℕ} (S : Frames L r k)

omit [IsNonarchimedeanLocalField F] [CharZero F] in

theorem mass_le_sum {ι : Type} (s : Finset ι) (d : S.Datum) (P : Submodule L.O S.V → Prop)
    (Q : ι → Submodule L.O S.V → Prop) (h : ∀ Λ, S.IsTerm d Λ → P Λ → ∃ i ∈ s, Q i Λ) :
    S.mass d P ≤ ∑ i ∈ s, S.mass d (Q i) := by
  unfold Frames.mass
  rw [← Summable.tsum_finsetSum (fun i _ => ENNReal.summable)]
  refine ENNReal.tsum_le_tsum fun o => ?_
  by_cases hP : S.IsTerm d o.out ∧ P o.out
  · obtain ⟨i, hi, hQ⟩ := h _ hP.1 hP.2
    rw [if_pos hP]
    refine le_trans ?_ (Finset.single_le_sum (f := fun i => if S.IsTerm d o.out ∧ Q i o.out then
      ENNReal.ofReal (S.mu o.out) else 0) (fun _ _ => zero_le) hi)
    exact (if_pos ⟨hP.1, hQ⟩).ge
  · rw [if_neg hP]
    exact zero_le

omit [IsNonarchimedeanLocalField F] [CharZero F] in

theorem mass_mono (d : S.Datum) (P Q : Submodule L.O S.V → Prop)
    (h : ∀ Λ, S.IsTerm d Λ → P Λ → Q Λ) : S.mass d P ≤ S.mass d Q := by
  simpa using mass_le_sum S {()} d P (fun _ => Q) (fun Λ h1 h2 => ⟨(), by simp, h Λ h1 h2⟩)

omit [IsNonarchimedeanLocalField F] [CharZero F] in

theorem sumData_mass_le (P : S.Datum → Submodule L.O S.V → Prop) :
    (S.sumData fun d => S.mass d (P d)) ≤ S.nn := by
  unfold Frames.nn Frames.sumData
  exact ENNReal.tsum_le_tsum fun o => mul_le_mul_right (mass_mono S _ _ _ fun _ _ _ => trivial) _

theorem ampSq_le_of_mass (hk : 1 ≤ k) (P : S.Datum → Submodule L.O S.V → Prop) (B : ℝ)
    (hB : ∀ d, S.mass d (P d) ≤ ENNReal.ofReal B) :
    S.ampSq P ≤ ENNReal.ofReal B * S.sumData fun d => S.mass d (P d) := by
  obtain ⟨h1, h2⟩ := GlobalTheory.HL.BasicIneq.basic_inequality L r k S hk
  simpa using h2 P B 1 zero_le_one hB (fun d => by simpa using h1 d (P d))

theorem ampSq_le_of_zero (hk : 1 ≤ k) (P : S.Datum → Submodule L.O S.V → Prop)
    (hP : ∀ d Λ, S.IsTerm d Λ → P d Λ → S.BBzero d Λ) :
    S.ampSq P ≤ ENNReal.ofReal (S.Hp ^ (39 * (r + 1) ^ 2)) * S.nn := by
  refine (ampSq_le_of_mass S hk P _ fun d => ?_).trans
    (mul_le_mul_right (sumData_mass_le S P) _)
  by_cases hT : ∃ Λ, S.IsTerm d Λ
  · obtain ⟨Λ₀, h₀⟩ := hT
    have hH : 1 ≤ S.Hp := (GlobalTheory.HL.Defect.exponents_and_defect L r k S d Λ₀ h₀).2.2.2.2.1
    have hq : 2 ≤ S.q := (GlobalTheory.UnramOrder.order_facts L S.ϖ S.ϖ_irr).2.2.2.2.2.2.1
    refine (mass_mono S d _ (fun Λ => S.cardI d Λ = 1) fun Λ h1 h2 => ?_).trans
      (((GlobalTheory.T.hermitianDoubleCoset_mass_le_and_finite L r k S hk d).1 1).trans (ENNReal.ofReal_le_ofReal ?_))
    · have hb := (GlobalTheory.HL.Defect.exponents_and_defect L r k S d Λ h1).2.2.2.2.2.2.1.1 (hP d Λ h1 h2)
      obtain ⟨⟨i, hi⟩, hle, -⟩ := GlobalTheory.HL.SmallImage.small_image L r k S d Λ h1
      have : 0 < S.q ^ i := by positivity
      omega
    · rw [Nat.cast_one, one_pow, mul_one]
      exact pow_le_pow_right₀ hH (by nlinarith)
  · refine (mass_le_sum S (∅ : Finset Unit) d _ (fun _ _ => True) fun Λ h1 _ =>
      (hT ⟨Λ, h1⟩).elim).trans ?_
    simp

theorem ampSq_defect_le (hk : 4 * r + 7 ≤ k) (hH : 0 ≤ S.Hp) (i : ℕ) :
    (S.ampSq fun d Λ => S.be d Λ = S.q ^ i) ≤
      ENNReal.ofReal ((i + 1) * S.Hp ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) *
        (4 * S.Hp ^ (4 * (r + 1)))) * S.nn := by
  have hk1 : 1 ≤ k := by omega
  have hq : 2 ≤ S.q := (GlobalTheory.UnramOrder.order_facts L S.ϖ S.ϖ_irr).2.2.2.2.2.2.1
  have hβ : 0 < S.q ^ i := by positivity
  have hβ' : (0 : ℝ) < ((S.q ^ i : ℕ) : ℝ) ^ (k - 1) := by positivity
  have hm : ∀ d, S.mass d (fun Λ => S.be d Λ = S.q ^ i) ≤ ENNReal.ofReal ((i + 1) *
      (S.Hp ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * ((S.q ^ i : ℕ) : ℝ) ^ (k - 1))) := by
    intro d
    refine (mass_le_sum S (Finset.range (i + 1)) d _ (fun j Λ => S.cardI d Λ = S.q ^ j)
      fun Λ h1 h2 => ?_).trans ?_
    · obtain ⟨⟨j, hj⟩, hle, -⟩ := GlobalTheory.HL.SmallImage.small_image L r k S d Λ h1
      refine ⟨j, Finset.mem_range.2 ?_, hj⟩
      rw [hj, h2] at hle
      have := (Nat.pow_le_pow_iff_right (by omega)).1 hle
      omega
    · refine (Finset.sum_le_card_nsmul _ _ (ENNReal.ofReal
        (S.Hp ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * ((S.q ^ i : ℕ) : ℝ) ^ (k - 1)))
        fun j hj => ?_).trans ?_
      · refine ((GlobalTheory.T.hermitianDoubleCoset_mass_le_and_finite L r k S hk1 d).1 _).trans (ENNReal.ofReal_le_ofReal ?_)
        have hji : S.q ^ j ≤ S.q ^ i :=
          Nat.pow_le_pow_right (by omega) (by have := Finset.mem_range.1 hj; omega)
        gcongr
      · rw [Finset.card_range, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ i + 1),
          ← ENNReal.ofReal_natCast, Nat.cast_succ]
  refine (ampSq_le_of_mass S hk1 _ _ hm).trans ?_
  refine (mul_le_mul_right (GlobalTheory.T.sumData_mass_be_eq_le L r k S hk _ hβ) _).trans (le_of_eq ?_)
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  field_simp

theorem ampSq_le_height_mul_mass : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → S.ampSq S.BBzero ≤ ENNReal.ofReal (S.Hp ^ (39 * (r + 1) ^ 2)) * S.nn ∧ (S.ampSq fun _ _ => True) ≤ ENNReal.ofReal (S.Hp ^ (39 * (r + 1) ^ 2)) * S.nn := by
  intro F _ _ _ _ _ E _ _ _ L r k S hk
  have hk1 : 1 ≤ k := by omega
  refine ⟨ampSq_le_of_zero S hk1 _ fun _ _ _ h => h, ?_⟩
  by_cases hz : ∀ d Λ, S.IsTerm d Λ → S.BBzero d Λ
  · exact ampSq_le_of_zero S hk1 _ fun d Λ h _ => hz d Λ h
  push_neg at hz
  obtain ⟨d₀, Λ₀, h₀, hn⟩ := hz
  obtain ⟨ha, -, -, hqa, hH, -, -, hqH, -⟩ := GlobalTheory.HL.Defect.exponents_and_defect L r k S d₀ Λ₀ h₀
  have hq : 2 ≤ S.q := (GlobalTheory.UnramOrder.order_facts L S.ϖ S.ϖ_irr).2.2.2.2.2.2.1
  have hq' : (2 : ℝ) ≤ S.q := by exact_mod_cast hq
  have h2 : (2 : ℝ) ≤ S.Hp := hq'.trans (hqH hn)
  obtain ⟨A, hA⟩ := Int.eq_ofNat_of_zero_le ha
  have hAH : (A : ℝ) + 1 ≤ S.Hp := by
    rw [hA, zpow_natCast] at hqa
    have h1 : A + 1 ≤ S.q ^ A := Nat.lt_pow_self (by omega)
    exact le_trans (by exact_mod_cast h1) hqa
  refine (GlobalTheory.AmpCS.ampSq_le_card_mul_sum L r k S hk1 (Finset.range (A + 1))
    (fun i d Λ => S.be d Λ = S.q ^ i) _ (fun d Λ h => ?_) (fun d Λ h i _ i' _ h1 h2 => ?_)).trans ?_
  · obtain ⟨i, hi, hb⟩ := (GlobalTheory.HL.Defect.exponents_and_defect L r k S d Λ h).2.2.2.2.2.1
    exact ⟨fun _ => ⟨i, Finset.mem_range.2 (by omega), hb⟩, fun _ => trivial⟩
  · exact Nat.pow_right_injective hq (h1.symm.trans h2)
  have hsum := Finset.sum_le_card_nsmul (Finset.range (A + 1))
    (fun i => S.ampSq fun d Λ => S.be d Λ = S.q ^ i)
    (ENNReal.ofReal (S.Hp * S.Hp ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) *
        (S.Hp ^ 2 * S.Hp ^ (4 * (r + 1)))) * S.nn) (fun i hi => by
      refine (ampSq_defect_le S hk (by linarith) i).trans
        (mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _)
      have hi' : (i : ℝ) ≤ A := by
        have := Finset.mem_range.1 hi
        exact_mod_cast (by omega : i ≤ A)
      have h4 : (4 : ℝ) ≤ S.Hp ^ 2 := by nlinarith
      have h5 : (i : ℝ) + 1 ≤ S.Hp := by linarith
      gcongr)
  refine (mul_le_mul_right hsum _).trans ?_
  have hc : ((A + 1 : ℕ) : ℝ≥0∞) ≤ ENNReal.ofReal S.Hp := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (by push_cast; exact hAH)
  rw [Finset.card_range, nsmul_eq_mul, ← mul_assoc, ← mul_assoc]
  refine mul_le_mul_left ?_ _
  refine (mul_le_mul_left (mul_le_mul' hc hc) _).trans ?_
  rw [← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have he : S.Hp * S.Hp * (S.Hp * S.Hp ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) *
      (S.Hp ^ 2 * S.Hp ^ (4 * (r + 1)))) = S.Hp ^ (9 * (r + 1) ^ 2 + 16 * (r + 1) + 5) := by
    ring
  rw [he]
  exact pow_le_pow_right₀ hH (by nlinarith)

end GlobalTheory.HL.NoCancellation
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeLeMassSecondTypeFamily
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.AmpCancel

theorem ofReal_tsum_ite {ι : Type} (p : ι → Prop) (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i)
    (hfin : {i | p i}.Finite) :
    ENNReal.ofReal (∑' i, if p i then f i else 0) =
      ∑' i, if p i then ENNReal.ofReal (f i) else 0 := by
  have hs : ∀ i, i ∉ hfin.toFinset → ¬ p i := fun i hi h => hi (hfin.mem_toFinset.2 h)
  have hs' : ∀ i ∈ hfin.toFinset, p i := fun i hi => hfin.mem_toFinset.1 hi
  rw [tsum_eq_sum (s := hfin.toFinset) (fun i hi => if_neg (hs i hi)),
    tsum_eq_sum (s := hfin.toFinset) (fun i hi => if_neg (hs i hi)),
    Finset.sum_congr rfl (fun i hi => if_pos (hs' i hi)),
    Finset.sum_congr rfl (fun i hi => if_pos (hs' i hi)),
    ENNReal.ofReal_sum_of_nonneg (fun i _ => hf i)]

theorem amp_le_mass {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E]
    [TopologicalSpace E] (L : LocE F E) (r k : ℕ) (S : Frames L r k) (hk : 4 * r + 7 ≤ k)
    (β J βJ : ℕ) (d : S.Datum) :
    ENNReal.ofReal (‖S.amp d (S.InFF β J βJ d)‖) ≤
      ENNReal.ofReal (7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3))) * S.mass d (S.InFF β J βJ d) := by
  have hk1 : 1 ≤ k := by omega
  have hc0 : 0 ≤ (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) := zpow_nonneg (Nat.cast_nonneg _) _
  have hvol : ∀ K : Subgroup S.GLV, 0 ≤ invVol S.K0 K := fun K =>
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  obtain ⟨P, hP⟩ : ∃ P : Submodule L.O S.V → Prop, P = fun Λ => S.IsTerm d Λ ∧ S.InFF β J βJ d Λ :=
    ⟨_, rfl⟩
  have hPiff : ∀ Λ, P Λ ↔ S.IsTerm d Λ ∧ S.InFF β J βJ d Λ := fun Λ => by rw [hP]
  have hPfin : {o : MulAction.orbitRel.Quotient S.St (Submodule L.O S.V) | P o.out}.Finite :=
    (GlobalTheory.T.hermitianDoubleCoset_mass_le_and_finite L r k S hk1 d).2.subset fun o ho => ((hPiff _).1 ho).1
  have hmass : S.mass d (S.InFF β J βJ d) = ENNReal.ofReal (∑' o : MulAction.orbitRel.Quotient S.St (Submodule L.O S.V),
      if P o.out then invVol S.K0 (S.St ⊓ MulAction.stabilizer S.GLV o.out) else 0) := by
    rw [ofReal_tsum_ite (ι := MulAction.orbitRel.Quotient S.St (Submodule L.O S.V)) (fun o => P o.out)
      (fun o => invVol S.K0 (S.St ⊓ MulAction.stabilizer S.GLV o.out)) (fun o => hvol _) hPfin]
    subst hP
    unfold Frames.mass Frames.mu
    exact tsum_congr fun o => by congr
  have hsum0 : 0 ≤ ∑' o : MulAction.orbitRel.Quotient S.St (Submodule L.O S.V),
      if P o.out then invVol S.K0 (S.St ⊓ MulAction.stabilizer S.GLV o.out) else 0 :=
    tsum_nonneg fun o => by split_ifs <;> simp [hvol]
  have hamp : S.amp d (S.InFF β J βJ d) = ∑' o : MulAction.orbitRel.Quotient S.St (Submodule L.O S.V),
      if P o.out then ((invVol S.K0 (S.St ⊓ MulAction.stabilizer S.GLV o.out) : ℝ) : ℂ) * S.om d o.out
      else 0 := by
    subst hP
    unfold Frames.amp Frames.mu
    exact tsum_congr fun o => by congr
  have key : ‖S.amp d (S.InFF β J βJ d)‖ ≤ 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) *
      ∑' o : MulAction.orbitRel.Quotient S.St (Submodule L.O S.V),
        if P o.out then invVol S.K0 (S.St ⊓ MulAction.stabilizer S.GLV o.out) else 0 := by
    by_cases hJ : 1 ≤ J ∧ J ≤ r
    · have hj : ((⟨J - 1, by omega⟩ : Fin r) : ℕ) + 1 = J := by simp only; omega
      obtain ⟨m, hm_inv, hm⟩ := GlobalTheory.T.exists_symm_invariant_kernel_hermitian_frames L r k S hk ⟨J - 1, by omega⟩ β βJ d P
        (fun Λ => by rw [hj]; exact hPiff Λ)
      have hK0 : S.K0 ≤ S.St := fun g hg => hg.1.1
      have bound := GlobalTheory.HL.norm_orbit_sum_le_of_symm_kernel S.St S.K0 P (S.om d) m
        (24 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3))) hK0
        (fun h hh x hx => by
          obtain ⟨hT, hI⟩ := (hPiff x).1 hx
          have T := GlobalTheory.T.hermitianFrames_stabilizer_acts_on_terms L r k S d x hT h hh
          have hlat := (GlobalTheory.HL.TermBasic.term_basic L r k S d x hT).1.1
          exact ⟨(hPiff _).2 ⟨T.1, (T.2.2.2.2.2.2.2.2.2.1 β J βJ).2 hI⟩, T.2.1,
            ((GlobalTheory.T.commonStabilizer_stabilizers_commensurable_volume L r k S).1 x hlat).2.2 h hh, fun y hy => hm_inv h hh x y hx hy⟩)
        (fun x hx => by
          have hb := GlobalTheory.HL.TermBasic.term_basic L r k S d x ((hPiff x).1 hx).1
          have A := (GlobalTheory.T.commonStabilizer_stabilizers_commensurable_volume L r k S).1 x hb.1.1
          have W := (GlobalTheory.HL.WitIndep.witness_independence L r k S d x _ _ hb.2.1).2.2.2.2
          obtain ⟨h1, h2, h3, h4⟩ := hm x hx
          exact ⟨A.1, A.2.1, W, h1, h2, h3, h4⟩)
        hPfin
      rw [hamp]
      have h2 : 2 * (24 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3))) ≤
          7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) := by linarith
      exact bound.trans (mul_le_mul_of_nonneg_right h2 hsum0)
    · have hempty : ∀ Λ, ¬ P Λ := by
        intro Λ hΛ
        obtain ⟨hT, hTB, -, hle, ⟨y, hy, hyJ⟩, -⟩ := (hPiff Λ).1 hΛ
        by_cases hJr : r < J
        · have := hTB.2.1 y hy
          omega
        · have hJ0 : J = 0 := by omega
          apply hTB.1
          refine le_antisymm (GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT).2.2.1 fun z hz => ?_
          refine ((GlobalTheory.T.term_exponents_nonneg_and_defect_group_bound L r k S d Λ hT).2.2.2.2.2.2.2.2.2.1 z hz).1 ?_
          have := hle z hz
          omega
      rw [hamp]
      simp [hempty]
  rw [hmass, ← ENNReal.ofReal_mul (by linarith)]
  exact ENNReal.ofReal_le_ofReal key

end GlobalTheory.HL.AmpCancel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselOpNormPowerIntegralLtTopClosedSubgroupStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselOpNormPowerIntegral_lt_top_closedSubgroup : ∀ (k r : ℕ) (S : Set (Mat k r)) (μ : Measure (Mt k r)) (A : ℝ), IsClosedSub k r S → IsHaarOn S μ → 2 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 < A → normInt μ A < ⊤ := by
  first | exact @GlobalTheory.SgGrowth.normInt_lt_top | exact GlobalTheory.SgGrowth.normInt_lt_top | (intros; apply GlobalTheory.SgGrowth.normInt_lt_top <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselRootDilationNormalizesContractsUnipotentStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselRootDilation_normalizes_contracts_unipotent : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), inWb k r z → (∀ τ : ℝ, 0 < τ → dil k r τ ∈ GG k r ∧ (∀ h ∈ UWset k r z, dil k r τ * h = h * dil k r τ) ∧ (∀ m ∈ Nset k r, dil k r τ * m * (dil k r τ)⁻¹ ∈ Nset k r ∧ (dil k r τ)⁻¹ * m * dil k r τ ∈ Nset k r)) ∧ (∀ τ : ℝ, 1 ≤ τ → ∀ m ∈ Nset k r, ∀ i j, ‖((dil k r τ)⁻¹ * m * dil k r τ - 1) i j‖ ≤ τ⁻¹ * ‖(m - 1) i j‖) := by
  first | exact @GlobalTheory.SgInf.Dilation.main | exact GlobalTheory.SgInf.Dilation.main | (intros; apply GlobalTheory.SgInf.Dilation.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardIsometriesFixingSubspaceDefiniteLatticesLeStatement
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_isometries_fixing_subspace_definite_lattices_le : MinkowskiBound → ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → GlobalTheory.Mass.PD H.B.flip → ∀ (U : Submodule K V) (L L' : Submodule (𝓞 K) V), Submodule.IsLattice K L → Submodule.IsLattice K L' → ((({η : V ≃ₗ[K] V | η ∈ isomGrp H ∧ imLat η L = L' ∧ ∀ y ∈ U, η y = y}).encard : ℕ∞) : ℝ≥0∞) ≤ ((4 * ((Module.finrank K V) - Module.finrank K U) * (Formalism.HermitianLatticesTheory.fDeg K) : ℕ) : ℝ≥0∞) ^ (4 * ((Module.finrank K V) - Module.finrank K U) * (Formalism.HermitianLatticesTheory.fDeg K)) := by
  first | exact @GlobalTheory.IsoCount.isoCnt | exact GlobalTheory.IsoCount.isoCnt | (intros; apply GlobalTheory.IsoCount.isoCnt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CmEulerProductDiscrUnramifiedStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_euler_product_discr_unramified : ∀ (I : AutInst) (M : ℕ), 2 ≤ M → HasProd (fun u : IsDedekindDomain.HeightOneSpectrum (𝓞 I.F) => 1 - GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.eta I.F I.E u ^ M * (GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.resCard I.F u ^ M)⁻¹) (Formalism.HermitianLatticesTheory.lValEta I.E M)⁻¹ ∧ |(discr I.F : ℝ)| = (2 * Formalism.HermitianLatticesTheory.vInv I.E) ^ I.f ∧ ∀ u, GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.UnramifiedPlace I.F I.E u := by
  first | exact @GlobalTheory.DensityEuler.euler_product_discr_unramified | exact GlobalTheory.DensityEuler.euler_product_discr_unramified | (intros; apply GlobalTheory.DensityEuler.euler_product_discr_unramified <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdaptedBasisChangeModelsStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adapted_basis_change_models : ∀ (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (Λ : ∀ i, Submodule (𝓞 I.E) (Fin (j i) → I.E)) (x₀ : I₀.Gf) (T T' : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E) (T₀ : Matrix (Fin I.n) (Fin I₀.n) I.E), (∀ i, 1 ≤ j i) → IsAdapted I I₀ e xf j S Λ x₀ T T' T₀ → ∀ (Λ' : ∀ i, Submodule (𝓞 I.E) (Fin (j i) → I.E)) (x₀' : I₀.Gf), (∀ i, ∃ γ : GL (Fin (j i)) I.E, ∀ y, (γ : Matrix (Fin (j i)) (Fin (j i)) I.E) *ᵥ y ∈ Λ' i ↔ y ∈ Λ i) → (∃ γ ∈ I₀.GFset, ∃ k ∈ I₀.Kset, γ.2 * x₀ = x₀' * k) → ∃ U U' U₀, IsAdapted I I₀ e xf j S Λ' x₀' U U' U₀ := by
  first | exact @GlobalTheory.AdaptedMove.adapted_move | exact GlobalTheory.AdaptedMove.adapted_move | (intros; apply GlobalTheory.AdaptedMove.adapted_move <;> assumption)
end

