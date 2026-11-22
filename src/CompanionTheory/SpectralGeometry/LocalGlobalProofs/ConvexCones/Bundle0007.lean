import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.Bundle0003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarrierDimInvFunHostFixingAutInvariant
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0692
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone
import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0708
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0682
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.Bundle0004
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellOfQuotientCellRadicalPullback
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0700
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0718
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0699
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.Bundle0005
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0727
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0706
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0728
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0674

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.CarrierFunctionTwistedGaloisStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.CarDim GlobalTheory.CompanionTheory.Ar.Fan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.carrier_function_twisted_galois : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (w0 : O), CMOrd O bar → ∀ (ψ : InvFun O), IsTwG w0 ψ → IsTwG w0 (carFun bar ψ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.TwistedCarrierFunction.isTwG_carFun | exact GlobalTheory.CompanionTheory.Ar.Fan.TwistedCarrierFunction.isTwG_carFun | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.TwistedCarrierFunction.isTwG_carFun <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.CellFaceOfFaceCutStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.CarDim GlobalTheory.CompanionTheory.Ar.Fan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cell_face_of_face_cut : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (ψ : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X], IsPolyFanOn bar ψ X → Dominates bar X → ∀ (m m' : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsCell bar ψ γ → IsFaceCut γ s h → IsCell bar ψ (fun i => γ (s i)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.CellFaces.isCell_comp | exact GlobalTheory.CompanionTheory.Ar.Fan.CellFaces.isCell_comp | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.CellFaces.isCell_comp <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.CellFaceRestrictionStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cell_face_restriction : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (q : ℕ) (ψ : InvFun O), IsPolyFan bar q ψ → ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q → Dominates bar X → ∀ (m : ℕ) (v : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ v → ∀ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut v s h → IsCell bar ψ (fun j => v (s j)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.FaceCells.isCell_face_of_isFaceCut | exact GlobalTheory.CompanionTheory.Ar.Fan.FaceCells.isCell_face_of_isFaceCut | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.FaceCells.isCell_face_of_isFaceCut <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.CellOfQuotientCellStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.CarDim GlobalTheory.CompanionTheory.Ar.Fan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cell_of_quotient_cell : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (ψ : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], IsPolyFanOn bar ψ X → (∀ (m m' : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsCell bar ψ γ → IsFaceCut γ s h → IsCell bar ψ (fun i => γ (s i))) → ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → ∀ (m' : ℕ) (δ : Fin m' → LinearMap.BilinForm ℤ (X ⧸ (orad β : Submodule O X))), IsCell bar ψ δ → InRCone (fun i => pull (orad β : Submodule O X).mkQ (δ i)) β → ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ ∧ InRCone γ β ∧ genRank γ ≤ genRank δ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.QuotientCell.cell_of_quot_cell | exact GlobalTheory.CompanionTheory.Ar.Fan.QuotientCell.cell_of_quot_cell | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.QuotientCell.cell_of_quot_cell <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.CellOfQuotientRadicalConeStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.CarDim GlobalTheory.CompanionTheory.Ar.Fan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cell_of_quotient_radical_cone : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (ψ : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X], (∀ (m m' : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsCell bar ψ γ → IsFaceCut γ s h → IsCell bar ψ (fun i => γ (s i))) → ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ → InRCone γ β → ∃ (m' : ℕ) (δ : Fin m' → LinearMap.BilinForm ℤ (X ⧸ (orad β : Submodule O X))), IsCell bar ψ δ ∧ InRCone (fun i => pull (orad β : Submodule O X).mkQ (δ i)) β ∧ genRank δ ≤ genRank γ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.QuotientCellRadical.exists_cell_quot_orad_of_inRCone | exact GlobalTheory.CompanionTheory.Ar.Fan.QuotientCellRadical.exists_cell_quot_orad_of_inRCone | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.QuotientCellRadical.exists_cell_quot_orad_of_inRCone <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.EvalPullbackSemilinearSurjective
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.SemilinearPullbackEval

open GlobalTheory.PolFan.OrbMark

theorem eval_pull_semilinear_of_isTwG : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O]
    (bar : O → O) (w0 : O), CMOrd O bar → ∀ (φ : InvFun O), IsTwG w0 φ →
    ∀ {X Y : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] [AddCommGroup Y] [Module O Y] [Module.Finite O Y]
      (τ : O ≃+* O), τ w0 = w0 → ∀ (f : X →+ Y), Function.Surjective f → (∀ (a : O) (x : X), f (a • x) = τ a • f x) →
      ∀ B : Y → Y → ℝ, φ.eval X (fun x y => B (f x) (f y)) = φ.eval Y B := by
  intro O _ _ _ _ bar w0 _ φ hφ X Y _ _ _ _ _ _ τ hτ f hf hsl B
  obtain ⟨n, πX, hπX⟩ := Module.Finite.exists_fin' O X
  let g : (Fin n → O) →ₗ[O] Y :=
    { toFun := fun a => f (πX (twv τ.symm a))
      map_add' := fun a b => by
        show f (πX (twv τ.symm (a + b))) = f (πX (twv τ.symm a)) + f (πX (twv τ.symm b))
        have hadd : twv τ.symm (a + b) = twv τ.symm a + twv τ.symm b := by
          funext i
          simp [twv_apply]
        rw [hadd, map_add, map_add]
      map_smul' := fun c a => by
        show f (πX (twv τ.symm (c • a))) = c • f (πX (twv τ.symm a))
        rw [twv_smul, map_smul, hsl, RingEquiv.apply_symm_apply] }
  have hg_apply : ∀ a, g a = f (πX (twv τ.symm a)) := fun _ => rfl
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨x, rfl⟩ := hf y
    obtain ⟨a, rfl⟩ := hπX x
    exact ⟨twv τ a, by rw [hg_apply, twv_symm_twv]⟩
  have key : ∀ a : Fin n → O, g (fun i => τ (a i)) = f (πX a) := by
    intro a
    rw [hg_apply]
    congr 2
    funext i
    simp [twv_apply]
  rw [φ.eval_eq hπX, φ.eval_eq hg, ← hφ τ hτ n (fun a b => B (g a) (g b))]
  congr 1
  funext a b
  show B (f (πX a)) (f (πX b)) = B (g (fun i => τ (a i))) (g (fun i => τ (b i)))
  rw [key a, key b]

end GlobalTheory.CompanionTheory.Ar.Fan.SemilinearPullbackEval
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsBalancedFormsDominatingStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_balanced_forms_dominating : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] (ι : Type) [Finite ι] (a : ι → X) (m : ℕ) (u : Fin m → LinearMap.BilinForm ℤ X), (∀ i y z, u i y z = u i z y) → (∀ i y, 0 ≤ u i y y) → ∃ (s : ℕ) (γ : Fin s → LinearMap.BilinForm ℤ X), (∀ i, γ i ∈ balForms bar X) ∧ (∀ i y, 0 ≤ γ i y y) ∧ (∀ i, toReal (γ i) ∈ contact bar a) ∧ ∀ B ∈ contact bar a, B ∈ rcone u → B ∈ rcone γ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.contact_inter_rcone_spanned | exact GlobalTheory.CompanionTheory.Ar.Fan.contact_inter_rcone_spanned | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.contact_inter_rcone_spanned <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.FinitePosDefFormSublevelStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_pos_def_form_sublevel : ∀ (X : Type) [AddCommGroup X] [Module.Finite ℤ X] [Module.Free ℤ X] (β : LinearMap.BilinForm ℤ X), (∀ y z, β y z = β z y) → (∀ y, y ≠ 0 → 0 < β y y) → ∀ c : ℤ, {y : X | β y y ≤ c}.Finite := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.sublevel_finite | exact GlobalTheory.CompanionTheory.Ar.Fan.sublevel_finite | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.sublevel_finite <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.IntegerLatticeDominatesStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integer_lattice_dominates : ∀ (X : Type) [AddCommGroup X] [Module.Finite ℤ X] [Module.Free ℤ X], Dominates (id : ℤ → ℤ) X := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.dominates_int | exact GlobalTheory.CompanionTheory.Ar.Fan.dominates_int | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.dominates_int <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.MarkingValueGaloisInvariant
section
set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.TwistedForm

variable {O : Type} [CommRing O]

def twPi (σ : O ≃+* O) (n : ℕ) : (Fin n → O) ≃+ (Fin n → O) :=
  AddEquiv.piCongrRight fun _ => σ.toAddEquiv

@[simp] theorem twPi_apply (σ : O ≃+* O) (n : ℕ) (a : Fin n → O) : twPi σ n a = fun j => σ (a j) := rfl

def twForm (σ : O ≃+* O) (n : ℕ) :
    LinearMap.BilinForm ℤ (Fin n → O) ≃+ LinearMap.BilinForm ℤ (Fin n → O) where
  toFun β := β.compl₁₂ (twPi σ n).toIntLinearEquiv.toLinearMap (twPi σ n).toIntLinearEquiv.toLinearMap
  invFun β := β.compl₁₂ (twPi σ.symm n).toIntLinearEquiv.toLinearMap (twPi σ.symm n).toIntLinearEquiv.toLinearMap
  left_inv β := LinearMap.ext₂ fun a b => by simp
  right_inv β := LinearMap.ext₂ fun a b => by simp
  map_add' _ _ := LinearMap.ext₂ fun a b => by simp

@[simp] theorem twForm_apply (σ : O ≃+* O) (n : ℕ) (β : LinearMap.BilinForm ℤ (Fin n → O)) (a b : Fin n → O) :
    twForm σ n β a b = β (fun j => σ (a j)) (fun j => σ (b j)) := rfl

theorem twForm_mem_balForms {bar : O → O} (hb : CMOrd O bar) (σ : O ≃+* O) {n : ℕ}
    {β : LinearMap.BilinForm ℤ (Fin n → O)}
    (h : β ∈ balForms bar (Fin n → O)) : twForm σ n β ∈ balForms bar (Fin n → O) := by
  refine ⟨fun y z => by simp only [twForm_apply]; exact h.1 _ _, fun a y z => ?_⟩
  simp only [twForm_apply]
  have e1 : (fun j => σ ((a • y) j)) = σ a • fun j => σ (y j) := funext fun j => by simp
  have e2 : (fun j => σ ((bar a • z) j)) = bar (σ a) • fun j => σ (z j) := funext fun j => by
    simp [hb.comm]
  rw [e1, e2]
  exact h.2 _ _ _

theorem twForm_symm_twForm (σ : O ≃+* O) {n : ℕ} (β : LinearMap.BilinForm ℤ (Fin n → O)) :
    twForm σ.symm n (twForm σ n β) = β := LinearMap.ext₂ fun a b => by simp

theorem twForm_mem_balForms_iff {bar : O → O} (hb : CMOrd O bar) (σ : O ≃+* O) {n : ℕ}
    (β : LinearMap.BilinForm ℤ (Fin n → O)) :
    twForm σ n β ∈ balForms bar (Fin n → O) ↔ β ∈ balForms bar (Fin n → O) :=
  ⟨fun h => by simpa [twForm_symm_twForm] using twForm_mem_balForms hb σ.symm h, twForm_mem_balForms hb σ⟩

theorem evalZ_twForm {w0 : O} {φ : InvFun O} (hφ : IsTwG w0 φ) {σ : O ≃+* O} (hσ : σ w0 = w0)
    {n : ℕ} (β : LinearMap.BilinForm ℤ (Fin n → O)) : φ.evalZ (twForm σ n β) = φ.evalZ β := by
  unfold InvFun.evalZ
  rw [InvFun.eval_pi, InvFun.eval_pi]
  exact hφ σ hσ n fun a b => (β a b : ℝ)

theorem markVal_twist : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O)
    (w0 : O), CMOrd O bar → ∀ (ψ lab : InvFun O) (i : ℕ), IsTwG w0 ψ → IsTwG w0 lab →
    ∀ σ : O ≃+* O, σ w0 = w0 → ∀ (n : ℕ) (B : (Fin n → O) → (Fin n → O) → ℝ),
      markVal bar ψ lab i n (fun a b => B (fun j => σ (a j)) (fun j => σ (b j))) = markVal bar ψ lab i n B := by
  intro O _ _ _ _ bar w0 hb ψ lab i hψ hlab σ hσ n B
  classical
  unfold markVal
  by_cases h2 : ∃ β : LinearMap.BilinForm ℤ (Fin n → O), ∀ a b, B a b = β a b
  · have h1 : ∃ β : LinearMap.BilinForm ℤ (Fin n → O), ∀ a b, B (fun j => σ (a j)) (fun j => σ (b j)) = β a b :=
      ⟨twForm σ n h2.choose, fun a b => h2.choose_spec _ _⟩
    rw [dif_pos h1, dif_pos h2]
    have e : h1.choose = twForm σ n h2.choose := LinearMap.ext₂ fun a b => by
      have := (h1.choose_spec a b).symm.trans (h2.choose_spec _ _)
      exact_mod_cast this
    rw [e, isMarked_transport (T := (twPi σ n).toEquiv) (fun _ _ _ => rfl) (twForm_mem_balForms_iff hb σ)
      (evalZ_twForm hψ hσ) (evalZ_twForm hlab hσ)]
  · have h1 : ¬ ∃ β : LinearMap.BilinForm ℤ (Fin n → O), ∀ a b,
        B (fun j => σ (a j)) (fun j => σ (b j)) = β a b := fun ⟨β, hβ⟩ =>
      h2 ⟨twForm σ.symm n β, fun a b => by
        have := hβ (fun j => σ.symm (a j)) (fun j => σ.symm (b j))
        simpa using this⟩
    rw [dif_neg h1, dif_neg h2]

end GlobalTheory.CompanionTheory.Ar.Fan.TwistedForm
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.MaxMultiplicityLtTop
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Fan.MaxMultiplicityFinite

open GlobalTheory.PolFan.MultBound in

theorem maxMult_lt_top : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O),
    CMOrd O bar → ∀ (q : ℕ) (φ : InvFun O), IsPolyFan bar q φ → maxMult bar q φ < ⊤ := by
  intro O _ _ _ _ bar hCM q φ hφ
  obtain ⟨n, R, hR, hcls⟩ := hCM.classes q
  have hC := fun k : Fin n =>
    haveI := (hR k).1
    haveI := (hR k).2.1
    GlobalTheory.PolFan.MultBound.perModule (hφ (R k) (hR k).2.2) (GlobalTheory.T.balanced_nonneg_form_in_psd_cone O bar hCM (R k))
  choose C hC using hC
  refine lt_of_le_of_lt (b := ((Finset.univ.sup C : ℕ) : ℕ∞)) ?_ (ENat.coe_lt_top _)
  unfold maxMult
  refine iSup_le fun X => iSup_le fun _ => iSup_le fun _ => iSup_le fun _ => iSup_le fun _ =>
    iSup_le fun hq => iSup_le fun m => iSup_le fun δ => iSup_le fun h => iSup_le fun hli =>
      iSup_le fun hpr => ?_
  obtain ⟨k, ⟨e⟩⟩ := hcls X hq
  haveI := (hR k).1
  obtain ⟨h', hli', hpr', heq⟩ := GlobalTheory.PolFan.MultBound.transport e.symm h hli hpr
  have hle := (hC k m _ h' hli' hpr').trans (Finset.le_sup (f := C) (Finset.mem_univ k))
  rw [← heq]
  exact_mod_cast hle

end GlobalTheory.CompanionTheory.Ar.Fan.MaxMultiplicityFinite
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.MemConeOfModTwoLiftStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCell_vorFun_of_contact_subset_rcone : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (g : ℕ) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] (n : ℕ) (r : (Fin n → ℤ) →ₗ[ℤ] X) (a : (Fin n → ZMod (1 + 1)) → Fin n → ℤ), Function.Surjective r → (∀ y, redV 1 (a y) = y) → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), (∀ i, γ i ∈ balForms bar X) → (∀ i y, 0 ≤ γ i y y) → (∀ i, toReal (γ i) ∈ contact bar fun y => r (a y)) → (contact bar fun y => r (a y)) ⊆ rcone γ → IsCell bar (vorFun O g) γ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.isCell_vorFun_of_contact | exact GlobalTheory.CompanionTheory.Ar.Fan.isCell_vorFun_of_contact | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.isCell_vorFun_of_contact <;> assumption)
end

