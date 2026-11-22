import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0017

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.EssSquareIntegrableSegments
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL

namespace GlobalTheory.Published

def EssSquareIntegrableSegments : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    (δ : IrrGL k), 1 ≤ δ.1 →
    ((∃ (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ), IsSqIntCoeff (δ.tw χ hχ).rep) ↔ ∃ Δ : Segment k, IsLSeg Δ δ.rep)

namespace EssSquareIntegrableSegments

open MeasureTheory

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem subsingleton_adGL_one : Subsingleton (AdGL k 1) := by
  refine QuotientGroup.subsingleton_iff.2 (eq_top_iff.2 fun g _ => Subgroup.mem_center_iff.2 fun h => ?_)
  ext i j
  obtain rfl : i = 0 := Subsingleton.elim _ _
  obtain rfl : j = 0 := Subsingleton.elim _ _
  simp [Matrix.mul_apply, mul_comm]

theorem isSqIntCoeff_of_trivial {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin 1) k) V}
    (h : ∀ g v, π g v = v) : IsSqIntCoeff π := by
  intro _ _ μ hμ v l _
  have := subsingleton_adGL_one (k := k)
  have : IsFiniteMeasure μ := ⟨(Set.toFinite _).isCompact.measure_lt_top⟩
  exact ⟨fun _ => ‖l v‖, fun g => by rw [h], memLp_const _⟩

theorem both_sides_ofChar (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) :
    1 ≤ (IrrGL.ofChar χ hχ).1 ∧
      (∃ (ψ : kˣ →* ℂˣ) (hψ : IsSmoothChar ψ), IsSqIntCoeff ((IrrGL.ofChar χ hχ).tw ψ hψ).rep) ∧
        ∃ Δ : Segment k, IsLSeg Δ (IrrGL.ofChar χ hχ).rep := by
  have hi : IsSmoothChar χ⁻¹ := by
    have : χ⁻¹.ker = χ.ker := by ext; simp
    unfold IsSmoothChar; rw [this]; exact hχ
  refine ⟨le_rfl, ⟨χ⁻¹, hi, ?_⟩, _, (single_spec (IrrGL.isCusp_ofChar χ hχ)).2.1⟩
  have e : (IrrGL.ofChar χ hχ).tw χ⁻¹ hi = IrrGL.ofChar 1 isSmoothChar_one := by
    simp only [IrrGL.tw_ofChar, mul_inv_cancel]
  rw [e]
  refine @isSqIntCoeff_of_trivial k _ _ _ _ _ _ _ _ fun g v => ?_
  let φ := equivRep (IrrRep.det (k := k) (Fin 1) 1 isSmoothChar_one)
  obtain ⟨w, rfl⟩ := φ.toLinearEquiv.surjective v
  refine (φ.toIntertwiningMap.isIntertwining _ _ g w).symm.trans (congrArg φ ?_)
  show ((detChar (Fin 1) (1 : kˣ →* ℂˣ) g : ℂˣ) : ℂ) • w = w
  simp

end EssSquareIntegrableSegments

end GlobalTheory.Published
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
section
noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.ContraPair

namespace GlobalTheory.Published

def GelfandKazhdanDual : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ) (π : CuspSub E n), Paired π π invTOp

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.TemperedProductOfSquareIntegrable
section
noncomputable section
open MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace GlobalTheory.Published

def TemperedProductOfSquareIntegrable : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (N : ℕ), 1 ≤ N →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → π.IsIrreducible →
      (IsTemperedCoeff π ↔ ∃ (h : ℕ) (δ : Fin h → IrrGL k) (hd : ∑ i, (δ i).1 = N),
        (∀ i, 1 ≤ (δ i).1 ∧ IsSqIntCoeff (δ i).rep) ∧ Nonempty (π.Equiv (prodIrr δ hd)))

namespace TemperedProduct

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in

theorem coeffLp_of_equiv {N : ℕ} {p : ℝ} {π : Representation ℂ (GL (Fin N) k) V} {σ : Representation ℂ (GL (Fin N) k) W}
    (φ : π.Equiv σ) (h : CoeffLp p π) : CoeffLp p σ := by
  intro _ _ μ hμ w l hl
  have hφ : ∀ g v, φ.toLinearEquiv (π g v) = σ g (φ.toLinearEquiv v) := fun g v =>
    φ.toIntertwiningMap.isIntertwining _ _ g v
  have hs : {g : GL (Fin N) k | (l ∘ₗ φ.toLinearEquiv.toLinearMap) ∘ₗ π g = l ∘ₗ φ.toLinearEquiv.toLinearMap} =
      {g : GL (Fin N) k | l ∘ₗ σ g = l} := by
    ext g
    refine ⟨fun H => LinearMap.ext fun x => ?_, fun H => LinearMap.ext fun x => ?_⟩
    · have h1 : l (φ.toLinearEquiv (π g (φ.toLinearEquiv.symm x))) = l (φ.toLinearEquiv (φ.toLinearEquiv.symm x)) :=
        LinearMap.congr_fun H (φ.toLinearEquiv.symm x)
      rwa [hφ, LinearEquiv.apply_symm_apply] at h1
    · show l (φ.toLinearEquiv (π g x)) = l (φ.toLinearEquiv x)
      rw [hφ]
      exact LinearMap.congr_fun H _
  obtain ⟨F, hF, hF'⟩ := h μ hμ (φ.toLinearEquiv.symm w) (l ∘ₗ φ.toLinearEquiv.toLinearMap) (hs ▸ hl)
  refine ⟨F, fun g => ?_, hF'⟩
  rw [hF, LinearMap.comp_apply, LinearEquiv.coe_coe, hφ, LinearEquiv.apply_symm_apply]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem subsingleton_adGL_one : Subsingleton (AdGL k 1) := by
  refine ⟨fun a b => ?_⟩
  induction a using QuotientGroup.induction_on
  induction b using QuotientGroup.induction_on
  refine QuotientGroup.eq.2 (Subgroup.mem_center_iff.2 fun g => ?_)
  generalize (_⁻¹ * _ : GL (Fin 1) k) = c
  ext i j
  simp [Matrix.mul_apply, Subsingleton.elim i 0, Subsingleton.elim j 0, mul_comm]

theorem coeffLp_detRep_one_iff (p : ℝ) {χ : kˣ →* ℂˣ} (hχ : IsSmoothChar χ) :
    CoeffLp p (detRep (Fin 1) χ) ↔ ∀ x, ‖(χ x : ℂ)‖ = 1 := by
  haveI : Subsingleton (AdGL k 1) := subsingleton_adGL_one
  have key : ∀ g v, detRep (Fin 1) χ g v = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • v := fun _ _ => rfl
  constructor
  · intro h x
    borelize (AdGL k 1)
    have ho : IsOpen {g : GL (Fin 1) k | (LinearMap.id : Module.Dual ℂ ℂ) ∘ₗ detRep (Fin 1) χ g = LinearMap.id} := by
      convert (isSmooth_ofChar_iff _).2 (hχ.detChar (n := Fin 1)) 1 using 2
      ext g
      exact ⟨fun H => LinearMap.congr_fun H 1, fun H => LinearMap.ext_ring H⟩
    obtain ⟨F, hF, -⟩ := h Measure.haar inferInstance 1 LinearMap.id ho
    have h1 := hF (Matrix.GeneralLinearGroup.scalar (Fin 1) x)
    have h2 : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 1) x) = x := by
      ext; simp [Matrix.GeneralLinearGroup.scalar]
    rw [Subsingleton.elim (QuotientGroup.mk _ : AdGL k 1) (QuotientGroup.mk 1), hF, key, key, h2] at h1
    simpa using h1.symm
  · intro hu _ _ μ hμ v l _
    refine ⟨fun _ => ‖l v‖, fun g => ?_, memLp_const _⟩
    rw [key, map_smul, norm_smul, hu, one_mul]

theorem unitary_char {χ : kˣ →* ℂˣ} (hχ : IsSmoothChar χ) (hu : ∀ x, ‖(χ x : ℂ)‖ = 1) :
    IsSmooth (detRep (Fin 1) χ) ∧ (detRep (Fin 1) χ).IsIrreducible ∧ IsTemperedCoeff (detRep (Fin 1) χ) ∧
      ∃ (h : ℕ) (δ : Fin h → IrrGL k) (hd : ∑ i, (δ i).1 = 1),
        (∀ i, 1 ≤ (δ i).1 ∧ IsSqIntCoeff (δ i).rep) ∧ Nonempty ((detRep (Fin 1) χ).Equiv (prodIrr δ hd)) := by
  have hs : IsSmooth (detRep (Fin 1) χ) := (isSmooth_ofChar_iff _).2 hχ.detChar
  have hi : (detRep (Fin 1) χ).IsIrreducible := isIrreducible_ofChar _
  let x := IrrGL.of _ hs hi
  let φ : (detRep (Fin 1) χ).Equiv x.rep := IrrGL.equivOf _ _ _
  have hd : ∑ _ : Fin 1, x.1 = x.1 := by simp
  obtain ⟨ψ⟩ := nonempty_equiv_prodIrr_one x hd
  have ht : IsTemperedCoeff (detRep (Fin 1) χ) := by
    intro ε _
    exact @Iff.mpr _ _ (coeffLp_detRep_one_iff (2 + ε) hχ) hu
  have h2 : IsSqIntCoeff x.rep := by
    exact @coeffLp_of_equiv k _ _ _ _ _ _ _ _ 1 2 _ _ φ (@Iff.mpr _ _ (coeffLp_detRep_one_iff 2 hχ) hu)
  exact ⟨hs, hi, ht, 1, fun _ => x, hd,
    fun _ => ⟨le_rfl, h2⟩, ⟨φ.trans ψ⟩⟩

theorem not_tempered_char {χ : kˣ →* ℂˣ} (hχ : IsSmoothChar χ) (hu : ¬ ∀ x, ‖(χ x : ℂ)‖ = 1) :
    IsSmooth (detRep (Fin 1) χ) ∧ (detRep (Fin 1) χ).IsIrreducible ∧ ¬ IsTemperedCoeff (detRep (Fin 1) χ) :=
  ⟨(isSmooth_ofChar_iff _).2 hχ.detChar, isIrreducible_ofChar _,
    fun h => hu ((coeffLp_detRep_one_iff _ hχ).1 (h 1 one_pos))⟩

end TemperedProduct

end GlobalTheory.Published
end
end

