import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0235
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0249
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0304
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0298
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0296
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0282
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0167
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0201
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0266
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0299
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0114
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicFiniteVolumeIntegralBound
section
open IsLocalRing Polynomial

namespace GlobalTheory.GenFibBaseChange

theorem exists_genFib_maps : ∀ (T O A A₁ R R₁ : Type) [CommRing T] [IsDomain T] [CommRing O] [Algebra T O]
    [CommRing A] [IsDomain A] [CommRing A₁] [IsDomain A₁] [CommRing R] [Algebra A R] [CommRing R₁] [Algebra A₁ R₁]
    (j : A →+* A₁) (i₁ : A₁ →+* T), Function.Injective j → Function.Injective i₁ →
    ∀ (jA : R →+* O) (jA₁ : R₁ →+* O) (γ : R →+* R₁)
      (ψA : GlobalTheory.LocAcyc.GenFib A R →+* GlobalTheory.LocAcyc.GenFib T O),
    jA₁.comp (algebraMap A₁ R₁) = (algebraMap T O).comp i₁ →
    γ.comp (algebraMap A R) = (algebraMap A₁ R₁).comp j →
    jA₁.comp γ = jA →
    ψA.comp (algebraMap R (GlobalTheory.LocAcyc.GenFib A R)) = (algebraMap O (GlobalTheory.LocAcyc.GenFib T O)).comp jA →
    ∃ (ψA₁ : GlobalTheory.LocAcyc.GenFib A₁ R₁ →+* GlobalTheory.LocAcyc.GenFib T O)
      (β : GlobalTheory.LocAcyc.GenFib A R →+* GlobalTheory.LocAcyc.GenFib A₁ R₁),
      ψA₁.comp (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁)) = (algebraMap O (GlobalTheory.LocAcyc.GenFib T O)).comp jA₁ ∧
      ψA₁.comp β = ψA ∧
      β.comp (algebraMap R (GlobalTheory.LocAcyc.GenFib A R)) = (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁)).comp γ := by
  intro T O A A₁ R R₁ _ _ _ _ _ _ _ _ _ _ _ _ j i₁ hj hi₁ jA jA₁ γ ψA h1 h2 h3 h4
  have hu1 : ∀ y : Algebra.algebraMapSubmonoid R₁ (nonZeroDivisors A₁),
      IsUnit (((algebraMap O (GlobalTheory.LocAcyc.GenFib T O)).comp jA₁) y) := by
    rintro ⟨y, a, ha, rfl⟩
    have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
    have hi : i₁ a ∈ nonZeroDivisors T := mem_nonZeroDivisors_of_ne_zero (fun h => ha0 (hi₁ (by simpa using h)))
    have e : jA₁ (algebraMap A₁ R₁ a) = algebraMap T O (i₁ a) := by
      simpa using congrArg (fun f => f a) h1
    simp only [RingHom.coe_comp, Function.comp_apply, e]
    exact IsLocalization.map_units (GlobalTheory.LocAcyc.GenFib T O)
      (⟨algebraMap T O (i₁ a), ⟨i₁ a, hi, rfl⟩⟩ : Algebra.algebraMapSubmonoid O (nonZeroDivisors T))
  have hu2 : ∀ y : Algebra.algebraMapSubmonoid R (nonZeroDivisors A),
      IsUnit (((algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁)).comp γ) y) := by
    rintro ⟨y, a, ha, rfl⟩
    have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
    have hi : j a ∈ nonZeroDivisors A₁ := mem_nonZeroDivisors_of_ne_zero (fun h => ha0 (hj (by simpa using h)))
    have e : γ (algebraMap A R a) = algebraMap A₁ R₁ (j a) := by
      simpa using congrArg (fun f => f a) h2
    simp only [RingHom.coe_comp, Function.comp_apply, e]
    exact IsLocalization.map_units (GlobalTheory.LocAcyc.GenFib A₁ R₁)
      (⟨algebraMap A₁ R₁ (j a), ⟨j a, hi, rfl⟩⟩ : Algebra.algebraMapSubmonoid R₁ (nonZeroDivisors A₁))
  let ψA₁ : GlobalTheory.LocAcyc.GenFib A₁ R₁ →+* GlobalTheory.LocAcyc.GenFib T O :=
    IsLocalization.lift (M := Algebra.algebraMapSubmonoid R₁ (nonZeroDivisors A₁)) hu1
  let β : GlobalTheory.LocAcyc.GenFib A R →+* GlobalTheory.LocAcyc.GenFib A₁ R₁ :=
    IsLocalization.lift (M := Algebra.algebraMapSubmonoid R (nonZeroDivisors A)) hu2
  have k1 : ψA₁.comp (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁)) =
      (algebraMap O (GlobalTheory.LocAcyc.GenFib T O)).comp jA₁ := IsLocalization.lift_comp hu1
  have k3 : β.comp (algebraMap R (GlobalTheory.LocAcyc.GenFib A R)) =
      (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁)).comp γ := IsLocalization.lift_comp hu2
  refine ⟨ψA₁, β, k1, ?_, k3⟩
  apply IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid R (nonZeroDivisors A))
  rw [RingHom.comp_assoc, k3, ← RingHom.comp_assoc, k1, RingHom.comp_assoc, h3, h4]

end GlobalTheory.GenFibBaseChange
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealMapEqSpanPowUniformizerDvrStatement
section
open AlgebraicGeometry CategoryTheory IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideal_map_eq_span_pow_uniformizer_dvr : ∀ (V W : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (f : V →+* W), Function.Injective f → ∀ (ϖ : V) (w : W) (e a : ℕ) (I : Ideal V), Irreducible ϖ → Irreducible w → Associated (f ϖ) (w ^ e) → I.map f = Ideal.span {w ^ a} → ∃ b : ℕ, e * b = a ∧ I = Ideal.span {ϖ ^ b} := by
  first | exact @GlobalTheory.ideal_map_eq_span_pow_uniformizer | exact GlobalTheory.ideal_map_eq_span_pow_uniformizer | (intros; apply GlobalTheory.ideal_map_eq_span_pow_uniformizer <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentMatrixLocalSplit
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory

theorem idempotent_matrix_split_of_isLocalRing (A : Type) [CommRing A] [IsLocalRing A] (h : ℕ)
    (X : Matrix (Fin h) (Fin h) A) : X * X = X → ∃ (n : ℕ) (i : Matrix (Fin h) (Fin n) A)
      (q : Matrix (Fin n) (Fin h) A), q * i = 1 ∧ i * q = X ∧ X.trace = n := by
  classical
  intro hX
  set f : (Fin h → A) →ₗ[A] (Fin h → A) := Matrix.toLin' X with hfdef
  have hff : ∀ v, f (f v) = f v := by
    intro v
    have : Matrix.toLin' (X * X) v = Matrix.toLin' X v := by rw [hX]
    simpa [Matrix.toLin'_mul, hfdef] using this
  set M := LinearMap.range f
  have hsplit : f.rangeRestrict ∘ₗ M.subtype = LinearMap.id := by
    ext ⟨w, hw⟩
    obtain ⟨v, rfl⟩ := hw
    simp [hff]
  haveI : Module.Projective A M := Module.Projective.of_split M.subtype f.rangeRestrict hsplit
  haveI : Module.Free A M := Module.free_of_flat_of_isLocalRing
  let b := Module.finBasis A M
  have hqi : LinearMap.toMatrix' (b.equivFun.toLinearMap ∘ₗ f.rangeRestrict) *
      LinearMap.toMatrix' (M.subtype ∘ₗ b.equivFun.symm.toLinearMap) = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    have : (b.equivFun.toLinearMap ∘ₗ f.rangeRestrict) ∘ₗ (M.subtype ∘ₗ b.equivFun.symm.toLinearMap)
        = LinearMap.id := by
      refine LinearMap.ext fun v => ?_
      have h1 : f.rangeRestrict (M.subtype (b.equivFun.symm v)) = b.equivFun.symm v :=
        LinearMap.congr_fun hsplit _
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, h1,
        LinearEquiv.apply_symm_apply, LinearMap.id_apply]
    rw [this, LinearMap.toMatrix'_id]
  have hiq : LinearMap.toMatrix' (M.subtype ∘ₗ b.equivFun.symm.toLinearMap) *
      LinearMap.toMatrix' (b.equivFun.toLinearMap ∘ₗ f.rangeRestrict) = X := by
    rw [← LinearMap.toMatrix'_comp]
    have : (M.subtype ∘ₗ b.equivFun.symm.toLinearMap) ∘ₗ (b.equivFun.toLinearMap ∘ₗ f.rangeRestrict)
        = f := by
      refine LinearMap.ext fun v => ?_
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.symm_apply_apply]
      rfl
    rw [this, hfdef, LinearMap.toMatrix'_toLin']
  refine ⟨Module.finrank A M, LinearMap.toMatrix' (M.subtype ∘ₗ b.equivFun.symm.toLinearMap),
    LinearMap.toMatrix' (b.equivFun.toLinearMap ∘ₗ f.rangeRestrict), hqi, hiq, ?_⟩
  rw [← hiq, Matrix.trace_mul_comm, hqi, Matrix.trace_one, Fintype.card_fin]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsSideFurther
section
namespace GlobalTheory.FourClauses

theorem len : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.StandardFunctorsFiniteLength :=
  fun h k _ _ _ _ _ _ _ => ⟨fun V _ _ π hs hl => (h k).2.1 _ _ _ _ V π hs hl, fun W _ _ ρ hs hl => (h k).2.2.1 _ _ _ _ W ρ hs hl⟩

end GlobalTheory.FourClauses
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InCellIffDetNeZero
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp

theorem inCell_iff_det_ne_zero : ∀ (F : Type) [Field F] [CharZero F] (E : Type) [Field E] [Algebra F E]
    (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (ν : Type) [Fintype ν] [DecidableEq ν] (g : UG c (stdJ ν E)),
    InCell c g ↔ ((mat c g).toBlocks₂₁).det ≠ 0 := by
  intro F _ _ E _ _ c δ hE ν _ _ g
  constructor
  · rintro ⟨p, hp, q, hq, rfl⟩
    have hdet : ∀ x : UG c (stdJ ν E), (mat c x).det ≠ 0 := fun x =>
      ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit (x : GL (ν ⊕ ν) E))).ne_zero
    have hp0 : mat c p = fromBlocks (mat c p).toBlocks₁₁ (mat c p).toBlocks₁₂ 0 (mat c p).toBlocks₂₂ := by
      rw [← (mem_sieg c).1 hp, fromBlocks_toBlocks]
    have hq0 : mat c q = fromBlocks (mat c q).toBlocks₁₁ (mat c q).toBlocks₁₂ 0 (mat c q).toBlocks₂₂ := by
      rw [← (mem_sieg c).1 hq, fromBlocks_toBlocks]
    have hpd := hdet p
    have hqd := hdet q
    rw [hp0, det_fromBlocks_zero₂₁] at hpd
    rw [hq0, det_fromBlocks_zero₂₁] at hqd
    change (mat c p * stdJ ν E * mat c q).toBlocks₂₁.det ≠ 0
    rw [hp0, hq0]
    simp only [stdJ, fromBlocks_multiply, toBlocks_fromBlocks₂₁]
    simp
    rw [det_neg, det_mul]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero))
      (mul_ne_zero (right_ne_zero_of_mul hpd) (left_ne_zero_of_mul hqd))
  · intro hC
    set A := (mat c g).toBlocks₁₁ with hA
    set B := (mat c g).toBlocks₁₂ with hB
    set C := (mat c g).toBlocks₂₁ with hCdef
    set D := (mat c g).toBlocks₂₂ with hD
    have hg0 : mat c g = fromBlocks A B C D := (fromBlocks_toBlocks _).symm
    have hrel : mat c g * stdJ ν E * ((mat c g).map c)ᵀ = stdJ ν E := (mem_UG_iff c _).mp g.2
    have hkey : C * (D.map c)ᵀ = D * (C.map c)ᵀ := by
      have h := congrArg Matrix.toBlocks₂₂ hrel
      rw [hg0] at h
      simp only [stdJ, fromBlocks_map, fromBlocks_transpose, fromBlocks_multiply, toBlocks_fromBlocks₂₂] at h
      simp at h
      exact (neg_add_eq_zero.1 h).symm
    have hCu : IsUnit C := (Matrix.isUnit_iff_isUnit_det C).2 (isUnit_iff_ne_zero.2 hC)
    have hCs : IsUnit (C.map c)ᵀ := by
      rw [Matrix.isUnit_iff_isUnit_det, det_transpose]
      exact (hCu.map (RingHom.mapMatrix (c : E →+* E))).map detMonoidHom
    have hCC : C * C⁻¹ = 1 := Matrix.mul_nonsing_inv C (isUnit_iff_ne_zero.2 hC)
    set v := C⁻¹ * D with hv
    have hvh : (v.map c)ᵀ = v := by
      apply hCu.mul_left_cancel
      apply hCs.mul_right_cancel
      have e1 : ((v.map c)ᵀ) * (C.map c)ᵀ = (D.map c)ᵀ := by
        rw [hv, Matrix.map_mul, transpose_mul, Matrix.mul_assoc, ← transpose_mul, ← Matrix.map_mul, hCC,
          Matrix.map_one _ (map_zero c) (map_one c), transpose_one, Matrix.mul_one]
      rw [Matrix.mul_assoc, e1, hkey, hv, ← Matrix.mul_assoc, hCC, Matrix.one_mul]
    let q := unip c v hvh
    have hq : q ∈ sieg c ν := by
      change (fromBlocks (1 : Matrix ν ν E) v 0 1).toBlocks₂₁ = 0
      rw [toBlocks_fromBlocks₂₁]
    refine ⟨g * q⁻¹ * (weyl c ν)⁻¹, ?_, q, hq, by group⟩
    rw [mem_sieg]
    change (mat c g * fromBlocks 1 (-v) 0 1 * -stdJ ν E).toBlocks₂₁ = 0
    rw [hg0]
    simp only [stdJ, fromBlocks_neg, fromBlocks_multiply, toBlocks_fromBlocks₂₁]
    simp
    rw [hv, ← Matrix.mul_assoc, hCC, Matrix.one_mul, neg_add_cancel]

end GlobalTheory.KSp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducedScalarIrreducible
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct

namespace GlobalTheory.RankFibre

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem indScal_lift_law (ν β : kˣ →* ℂˣ) (a b : ℕ) {f : GL (Fin (a + b)) k → ℂ} (hf : f ∈ indScal ν β a b) :
    (fun x => f x ⊗ₜ[ℂ] (1:ℂ)) ∈ indSpace (parab k (blocks a b))
      ((twist ((extTensor (detRep (Fin a) (ν * β)) (detRep (Fin b) β)).comp
        (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom) (deltaHalf k (Two (Fin a) (Fin b)))).comp
        (leviProj k (blocks a b))) := by
  intro p x
  have h := hf.2 p x
  apply (TensorProduct.lid ℂ ℂ).injective
  simp only [MonoidHom.coe_comp, Function.comp_apply, twist_apply, MonoidHom.coe_coe] at h ⊢
  rw [h]
  simp [parChar, detRep, ofChar_apply]
  ring

def indScalLift (ν β : kˣ →* ℂˣ) (a b : ℕ) {f : GL (Fin (a + b)) k → ℂ} (hf : f ∈ indScal ν β a b) :
    IndSp (two (stdSum (rfl : a + b = a + b)))
      ((extTensor (detRep (Fin a) (ν * β)) (detRep (Fin b) β)).comp
        (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom) :=
  ⟨⟨fun x => f x ⊗ₜ[ℂ] (1:ℂ), indScal_lift_law ν β a b hf⟩,
    mem_smoothPart_of_nhds (Filter.mem_of_superset ((show IsOpen {g : GL (Fin (a + b)) k | rightReg ℂ (GL (Fin (a + b)) k) ℂ g f = f} from hf.1).mem_nhds (by simp)) fun g hg => by
      have hg' : rightReg ℂ (GL (Fin (a + b)) k) ℂ g f = f := hg
      apply Subtype.ext
      funext x
      show f (x * g) ⊗ₜ[ℂ] (1:ℂ) = f x ⊗ₜ[ℂ] (1:ℂ)
      rw [show f (x * g) = f x from congrFun hg' x])⟩

theorem indScal_lift_apply (ν β : kˣ →* ℂˣ) (a b : ℕ) {f : GL (Fin (a + b)) k → ℂ} (hf : f ∈ indScal ν β a b)
    (x : GL (Fin (a + b)) k) : TensorProduct.lid ℂ ℂ ((indScalLift ν β a b hf).1.1 x) = f x := by
  simp [indScalLift]

def indScalVal (ν β : kˣ →* ℂˣ) (a b : ℕ) :
    IndSp (two (stdSum (rfl : a + b = a + b)))
      ((extTensor (detRep (Fin a) (ν * β)) (detRep (Fin b) β)).comp
        (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom) →ₗ[ℂ] (GL (Fin (a + b)) k → ℂ) where
  toFun F x := TensorProduct.lid ℂ ℂ (F.1.1 x)
  map_add' F G := by
    funext x
    show TensorProduct.lid ℂ ℂ (F.1.1 x + G.1.1 x) = _
    rw [map_add]
    rfl
  map_smul' c F := by
    funext x
    show TensorProduct.lid ℂ ℂ (c • F.1.1 x) = _
    rw [map_smul]
    rfl

theorem indScal_scal_lift (ν β : kˣ →* ℂˣ) (a b : ℕ) {f : GL (Fin (a + b)) k → ℂ} (hf : f ∈ indScal ν β a b) :
    indScalVal ν β a b (indScalLift ν β a b hf) = f :=
  funext (indScal_lift_apply ν β a b hf)

theorem indScal_irreducible : GlobalTheory.Published.BernsteinUnitaryProductIrreducible → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : ℕ) (ν β : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν → GlobalTheory.SmGL.IsUnitaryChar ν → GlobalTheory.SmGL.IsSmoothChar β → GlobalTheory.SmGL.IsUnitaryChar β → ∀ M : Submodule ℂ (GL (Fin (a + b)) k → ℂ), M ≤ GlobalTheory.RankFibre.indScal ν β a b → (∀ f ∈ M, ∀ h : GL (Fin (a + b)) k, (fun x => f (x * h)) ∈ M) → M = ⊥ ∨ GlobalTheory.RankFibre.indScal ν β a b ≤ M := by
  intro H k _ _ _ _ a b ν β hνs hνu hβs hβu M hM hinv
  have hs : IsSmoothChar (ν * β) := hνs.mul hβs
  have hu : IsUnitaryChar (ν * β) := fun g => by simp [hνu g, hβu g]
  have h₁ := GlobalTheory.Published.BernsteinUnitaryProductIrreducible.detRep_hyp a hs hu
  have h₂ := GlobalTheory.Published.BernsteinUnitaryProductIrreducible.detRep_hyp b hβs hβu
  have hirr := H k a b ℂ ℂ (detRep (Fin a) (ν * β)) (detRep (Fin b) β) h₁.1 h₁.2.1 h₁.2.2 h₂.1 h₂.2.1 h₂.2.2
  let S : Subrepresentation (prod₂ (detRep (Fin a) (ν * β)) (detRep (Fin b) β)) :=
    ⟨M.comap (indScalVal ν β a b), fun g F hF => hinv _ hF g⟩
  have hS : S.toSubmodule = M.comap (indScalVal ν β a b) := rfl
  have hmem : ∀ f (hf : f ∈ indScal ν β a b), f ∈ M ↔ indScalLift ν β a b hf ∈ S.toSubmodule := fun f hf => by
    rw [hS, Submodule.mem_comap, indScal_scal_lift]
  rcases hirr.eq_bot_or_eq_top S with h | h
  · left
    refine (Submodule.eq_bot_iff M).2 fun f hf => ?_
    have h' := (hmem f (hM hf)).1 hf
    rw [h] at h'
    have h0 : indScalLift ν β a b (hM hf) = 0 := (Submodule.mem_bot ℂ).1 h'
    rw [← indScal_scal_lift ν β a b (hM hf), h0, map_zero]
  · right
    intro f hf
    refine (hmem f hf).2 ?_
    rw [h]
    exact Submodule.mem_top

end GlobalTheory.RankFibre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfinitePlaceCompletionNhdsNEZeroNeBotStatement
section
open NumberField IsDedekindDomain GlobalTheory.QSA
open scoped Quaternion Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.infinitePlace_completion_nhdsNE_zero_neBot : ∀ (F : Type) [Field F] [NumberField F] (w : InfinitePlace F), (𝓝[≠] (0 : w.Completion)).NeBot := by
  first | exact @GlobalTheory.QSA.infinitePlace_completion_nhdsNE_neBot | exact GlobalTheory.QSA.infinitePlace_completion_nhdsNE_neBot | (intros; apply GlobalTheory.QSA.infinitePlace_completion_nhdsNE_neBot <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableHeckeTermDecayIntegrandStatement
section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.TermDecay
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_heckeTermDecayIntegrand : ∀ σ ∈ halfPlane, ∀ (a : ℤ) (b m : ℕ), 2 ≤ a + 2 * b → ∀ y : ℝ, y ≠ 0 →
    MeasureTheory.Integrable (qZ σ a b m y) := by
  first | exact @GlobalTheory.HeckeTwo.TermDecay.integrable_qZ | exact GlobalTheory.HeckeTwo.TermDecay.integrable_qZ | (intros; apply GlobalTheory.HeckeTwo.TermDecay.integrable_qZ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureOverGenericFibreHartogsStatement
section
open IsLocalRing Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralClosureOverGenericFibre_hartogs : ∀ (A R : Type) [CommRing A] [IsDomain A] [CommRing R] [Algebra A R] [IsNoetherianRing R],
    GlobalTheory.GoodEtale.Hart A R R →
    Function.Injective (algebraMap R (GlobalTheory.LocAcyc.GenFib A R)) →
    ∀ (D : Type) [CommRing D] [Algebra (GlobalTheory.LocAcyc.GenFib A R) D]
      (τ : D →ₗ[GlobalTheory.LocAcyc.GenFib A R] GlobalTheory.LocAcyc.GenFib A R),
      (∀ c ∈ GlobalTheory.KeyOriginNoeth.closure A R D, ∃ r : R, algebraMap R _ r = τ c) →
    ∀ (a₀ : A), a₀ ≠ 0 → ∀ (n : ℕ) (x y : Fin n → D),
      (∀ i, y i ∈ GlobalTheory.KeyOriginNoeth.closure A R D) →
      (∀ d : D, ∑ i, x i * algebraMap _ D (τ (y i * d)) =
        GlobalTheory.KeyOriginNoeth.baseHom A R D (algebraMap A R a₀) * d) →
    letI := GlobalTheory.KeyOriginNoeth.closureAlg A R D
    GlobalTheory.GoodEtale.Hart A R (GlobalTheory.KeyOriginNoeth.closure A R D) := by
  first | (exact @GlobalTheory.ClosureHartogs.closure_hart) | (exact GlobalTheory.ClosureHartogs.closure_hart) | (intros; apply GlobalTheory.ClosureHartogs.closure_hart  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFunctionalExtension
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory

theorem integral_form_extend_of_saturated : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type)
    [CommRing O] [Algebra O C] (X : Type) [AddCommGroup X] [Module C X] [Module O X]
    [IsScalarTower O C X] (L : Submodule O X) (S : Submodule C X) (f : X →ₗ[C] C), v.Integers O →
    L.FG → (∀ x ∈ L, x ∈ S → f x ∈ (algebraMap O C).range) →
    ∃ F : X →ₗ[C] C, (∀ x ∈ L, F x ∈ (algebraMap O C).range) ∧ ∀ x ∈ L, x ∈ S → F x = f x := by
  intro C _ v O _ _ X _ _ _ _ L S f hv hfg hf
  classical
  haveI : IsDomain O := hv.hom_inj.isDomain
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  haveI : IsFractionRing O C := hv.isFractionRing
  haveI : Module.Finite O L := Module.Finite.iff_fg.2 hfg
  let P : Submodule O L := (S.restrictScalars O).comap L.subtype
  let q : X →ₗ[O] X ⧸ S := (S.mkQ).restrictScalars O
  have hPq : P ≤ LinearMap.ker (q ∘ₗ L.subtype) := by
    intro x hx
    simp only [LinearMap.mem_ker, LinearMap.comp_apply]
    exact (Submodule.Quotient.mk_eq_zero S).2 hx
  let ι : (L ⧸ P) →ₗ[O] X ⧸ S := P.liftQ (q ∘ₗ L.subtype) hPq
  have hιker : LinearMap.ker ι = ⊥ := by
    apply Submodule.ker_liftQ_eq_bot
    intro x hx
    exact (Submodule.Quotient.mk_eq_zero S).1 hx
  have hιinj : Function.Injective ι := LinearMap.ker_eq_bot.1 hιker
  have hfree : Module.Free O (L ⧸ P) := by
    have : Module.Flat O (L ⧸ P) := by
      rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
      intro y hy
      rw [Submodule.mem_bot]
      obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff y).1 hy
      have ha0 : (a : O) ≠ 0 := nonZeroDivisors.ne_zero a.2
      have h1 : (a : O) • ι y = 0 := by rw [← map_smul, Submonoid.smul_def] at *; rw [ha, map_zero]
      rw [← algebraMap_smul C (a : O) (ι y)] at h1
      have h2 : ι y = 0 := (smul_eq_zero.1 h1).resolve_left (by simpa using ha0)
      exact hιinj (by rw [h2, map_zero])
    exact Module.free_of_flat_of_isLocalRing
  let b := Module.Free.chooseBasis O (L ⧸ P)
  have hliO : LinearIndependent O (ι ∘ b) := b.linearIndependent.map' ι hιker
  have hliC : LinearIndependent C (ι ∘ b) := (LinearIndependent.iff_fractionRing O C).1 hliO
  obtain ⟨s, hs⟩ := Module.projective_lifting_property P.mkQ (LinearMap.id) (Submodule.mkQ_surjective P)
  have hs' : ∀ y, P.mkQ (s y) = y := fun y => LinearMap.congr_fun hs y
  have key : ∀ y, S.mkQ ((s y : L) : X) = ι y := by
    intro y
    conv_rhs => rw [← hs' y]
    rfl
  let g0 := (Module.Basis.span hliC).constr C (fun i => f ((s (b i) : L) : X))
  obtain ⟨h, hh⟩ := LinearMap.exists_extend g0
  have hhb : ∀ i, h (ι (b i)) = f ((s (b i) : L) : X) := by
    intro i
    have e1 : (⟨ι (b i), Submodule.subset_span ⟨i, rfl⟩⟩ : Submodule.span C (Set.range (ι ∘ b))) =
        Module.Basis.span hliC i := by
      apply Subtype.ext; rw [Module.Basis.span_apply]; rfl
    have := LinearMap.congr_fun hh (Module.Basis.span hliC i)
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, g0, Module.Basis.constr_basis] at this
    rw [← this, ← e1]
  let F : X →ₗ[C] C := f - h ∘ₗ S.mkQ
  have hFS : ∀ x ∈ S, F x = f x := by
    intro x hx
    simp [F, (Submodule.Quotient.mk_eq_zero S).2 hx]
  refine ⟨F, ?_, fun x _ hx => hFS x hx⟩
  let G : (L ⧸ P) →ₗ[O] C := (F.restrictScalars O) ∘ₗ L.subtype ∘ₗ s
  have hG : G = 0 := by
    apply b.ext
    intro i
    simp only [G, F, LinearMap.comp_apply, LinearMap.restrictScalars_apply, LinearMap.sub_apply,
      Submodule.subtype_apply, LinearMap.zero_apply]
    rw [key, hhb, sub_self]
  intro x hx
  let xL : L := ⟨x, hx⟩
  let y := P.mkQ xL
  have hmem : ((xL - s y : L) : X) ∈ S := by
    have : P.mkQ (xL - s y) = 0 := by rw [map_sub, hs', sub_self]
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
    exact this
  have hsplit : x = ((xL - s y : L) : X) + ((s y : L) : X) := by simp [xL]
  have hGy : F ((s y : L) : X) = 0 := LinearMap.congr_fun hG y
  rw [hsplit, map_add, hGy, add_zero, hFS _ hmem]
  exact hf _ (Submodule.coe_mem _) hmem

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgClosedFractionRingAtPrimeOfEtaleStatement
section
open GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAlgClosed_fractionRing_atPrime_of_etale' : ∀ (T E : Type) [CommRing T] [IsDomain T] [CommRing E] [Algebra T E] [Algebra.Etale T E] (P : Ideal E) [P.IsPrime] [IsDomain (Localization.AtPrime P)], IsAlgClosed (FractionRing T) → IsAlgClosed (FractionRing (Localization.AtPrime P)) := by
  first | (exact @GlobalTheory.isAlgClosed_fractionRing_atPrime_of_etale) | (exact GlobalTheory.isAlgClosed_fractionRing_atPrime_of_etale) | (intros; apply GlobalTheory.isAlgClosed_fractionRing_atPrime_of_etale  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedOfLocalIdealPointPropertyStatement
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClosed_of_local_ideal_point_property : ∀ (S : Scheme.{0}) (P : ∀ (R' : Type) [CommRing R'], (Sp R' ⟶ S) → Prop),
  (∀ (R' : Type) [CommRing R'] (R'' : Type) [CommRing R''] (g : R' →+* R'') (x : Sp R' ⟶ S), P R' x → P R'' (spMap g ≫ x)) →
  (∀ (R' : Type) [CommRing R'] (x : Sp R' ⟶ S) (t : Finset R'), Ideal.span (t : Set R') = ⊤ →
     (∀ r ∈ t, P (Localization.Away r) (spMap (algebraMap R' (Localization.Away r)) ≫ x)) → P R' x) →
  (∀ z : S, ∃ (U : S.Opens) (hU : IsAffineOpen U), z ∈ U ∧ ∃ K : Ideal Γ(S, U),
     ∀ (R' : Type) [CommRing R'] (f : Γ(S, U) →+* R'), P R' (spMap f ≫ hU.fromSpec) ↔ K ≤ RingHom.ker f) →
  ∃ (Z : Scheme.{0}) (i : Z ⟶ S), IsClosedImmersion i ∧
    ∀ (R' : Type) [CommRing R'] (x : Sp R' ⟶ S), (∃ y : Sp R' ⟶ Z, y ≫ i = x) ↔ P R' x := by
  first | exact @GlobalTheory.PtClosed.closed_of_points | exact GlobalTheory.PtClosed.closed_of_points | (intros; apply GlobalTheory.PtClosed.closed_of_points <;> assumption)
end

