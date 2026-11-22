import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0393
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0279
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0171
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0146
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0270
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0132
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0544
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0437
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0543
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0546
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0536
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0493
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0507
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0517
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.Divisibility.Tuples
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0545
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianHaarIndependentOfOrthonormalFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstMeasurableSpaceRealSU
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulPMemSqCounitKer
section
open scoped TensorProduct

theorem GlobalTheory.PDivGroup.mulP_mem_sq_counit : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O], (p : O) ≠ 0 → ¬IsUnit (p : O) → (∀ a : O, ∃ b : O, b ^ p = a) → ∀ (G : GlobalTheory.PDivGroup p O) (n : ℕ) (b : G.A n), G.mulP n b ∈ RingHom.ker (Bialgebra.counitAlgHom O (G.A (n + 1))) ^ 2 → b ∈ RingHom.ker (Bialgebra.counitAlgHom O (G.A n)) ^ 2 := by
  intro p hp O _ _ _ hp0 hpu hroot G n b hb

  have hpk : ((p : ℕ) : IsLocalRing.ResidueField O) = 0 := by
    rw [← map_natCast (IsLocalRing.residue O), IsLocalRing.residue_eq_zero_iff]
    exact (IsLocalRing.mem_maximalIdeal _).2 hpu
  haveI : CharP (IsLocalRing.ResidueField O) p := (CharP.charP_iff_prime_eq_zero hp.out).2 hpk
  haveI : ExpChar (IsLocalRing.ResidueField O) p := ExpChar.prime hp.out
  haveI : PerfectRing (IsLocalRing.ResidueField O) p :=
    PerfectRing.ofSurjective _ p (fun y => by
      obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
      obtain ⟨c, hc⟩ := hroot a
      exact ⟨IsLocalRing.residue O c, by rw [frobenius_def, ← map_pow, hc]⟩)

  letI : Algebra (G.A n) (G.A (n + 1)) :=
    ((G.mulP n : G.A n →ₐ[O] G.A (n + 1)) : G.A n →+* G.A (n + 1)).toAlgebra
  haveI : IsScalarTower O (G.A n) (G.A (n + 1)) :=
    IsScalarTower.of_algebraMap_eq fun c => ((G.mulP n : G.A n →ₐ[O] G.A (n + 1)).commutes c).symm
  haveI : Module.Flat (G.A n) (G.A (n + 1)) := GlobalTheory.T.mulP_flat' p O G n
  have hε : ∀ b : G.A n, Bialgebra.counitAlgHom O (G.A (n + 1)) (algebraMap (G.A n) (G.A (n + 1)) b) =
      Bialgebra.counitAlgHom O (G.A n) b := fun b => by
    rw [Bialgebra.counitAlgHom_apply, Bialgebra.counitAlgHom_apply]
    exact CoalgHomClass.counit_comp_apply (G.mulP n) b
  have hker : (RingHom.ker (Bialgebra.counitAlgHom O (G.A (n + 1)))).comap (algebraMap (G.A n) (G.A (n + 1))) =
      RingHom.ker (Bialgebra.counitAlgHom O (G.A n)) := by
    ext b
    rw [Ideal.mem_comap, RingHom.mem_ker, RingHom.mem_ker, hε]

  obtain ⟨ρ, hρ⟩ : ∃ ρ : G.A (n + 1) →+* IsLocalRing.ResidueField O ⊗[O] G.A 1,
      ∀ a, ρ a = 1 ⊗ₜ G.resOne n a :=
    ⟨(Algebra.TensorProduct.includeRight : G.A 1 →ₐ[O] IsLocalRing.ResidueField O ⊗[O] G.A 1).toRingHom.comp
      ((G.resOne n : G.A (n + 1) →ₐ[O] G.A 1) : G.A (n + 1) →+* G.A 1), fun _ => rfl⟩
  have hπs : Function.Surjective (algebraMap O (IsLocalRing.ResidueField O)) := by
    rw [IsLocalRing.ResidueField.algebraMap_eq]; exact IsLocalRing.residue_surjective
  have hπk : RingHom.ker (algebraMap O (IsLocalRing.ResidueField O)) = IsLocalRing.maximalIdeal O := by
    rw [IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.ker_residue]
  have hfib := GlobalTheory.T.pDivGroup_mulP_unit_fiber_eq_level_one p O (IsLocalRing.ResidueField O) hπs G n
  have hρs : Function.Surjective ρ := fun h => by
    obtain ⟨a, ha⟩ := hfib.1 h
    exact ⟨a, by rw [hρ]; exact ha⟩
  have hkerρ : RingHom.ker ρ = (RingHom.ker ((algebraMap O (IsLocalRing.ResidueField O)).comp
      ((Bialgebra.counitAlgHom O (G.A (n + 1)) : G.A (n + 1) →+* O).comp (algebraMap (G.A n) (G.A (n + 1)))))).map
      (algebraMap (G.A n) (G.A (n + 1))) := by
    have hcomp : (algebraMap O (IsLocalRing.ResidueField O)).comp
        ((Bialgebra.counitAlgHom O (G.A (n + 1)) : G.A (n + 1) →+* O).comp (algebraMap (G.A n) (G.A (n + 1)))) =
        (algebraMap O (IsLocalRing.ResidueField O)).comp (Bialgebra.counitAlgHom O (G.A n) : G.A n →+* O) :=
      RingHom.ext fun b => by
        simp only [RingHom.comp_apply, RingHom.coe_coe]
        rw [hε]
    rw [hcomp]
    ext a
    rw [RingHom.mem_ker, hρ]
    exact hfib.2 a
  have hρalg : ∀ c : O, ρ (algebraMap O (G.A (n + 1)) c) =
      algebraMap (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O ⊗[O] G.A 1)
        (algebraMap O (IsLocalRing.ResidueField O) c) := fun c => by
    rw [hρ, AlgHomClass.commutes, ← IsScalarTower.algebraMap_apply]
    exact (Algebra.TensorProduct.includeRight.commutes c)
  have hεH : ∀ a, Bialgebra.counitAlgHom (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O ⊗[O] G.A 1) (ρ a) =
      algebraMap O (IsLocalRing.ResidueField O) (Bialgebra.counitAlgHom O (G.A (n + 1)) a) := fun a => by
    rw [hρ, Bialgebra.counitAlgHom_apply, Bialgebra.counitAlgHom_apply, TensorProduct.counit_tmul,
      CoalgHomClass.counit_comp_apply, Algebra.smul_def, mul_comm]
    simp

  have hlaws : (∀ a : IsLocalRing.ResidueField O ⊗[O] G.A 1, TensorProduct.lid (IsLocalRing.ResidueField O) _
      (LinearMap.rTensor _ (Bialgebra.counitAlgHom (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O ⊗[O] G.A 1)).toLinearMap
        (Bialgebra.comulAlgHom (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O ⊗[O] G.A 1) a)) = a) ∧
      (∀ a : IsLocalRing.ResidueField O ⊗[O] G.A 1, TensorProduct.rid (IsLocalRing.ResidueField O) _
      (LinearMap.lTensor _ (Bialgebra.counitAlgHom (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O ⊗[O] G.A 1)).toLinearMap
        (Bialgebra.comulAlgHom (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O ⊗[O] G.A 1) a)) = a) := by
    constructor
    · intro a
      rw [Bialgebra.comulAlgHom_apply]
      erw [Coalgebra.rTensor_counit_comul]
      simp
    · intro a
      rw [Bialgebra.comulAlgHom_apply]
      erw [Coalgebra.lTensor_counit_comul]
      simp
  obtain ⟨e, he1, hei, ε', Δ', hlaws', hnil⟩ := GlobalTheory.T.localFactor_at_augmentation_counital_comul _ _ _ _ hlaws
  have hpres := GlobalTheory.T.exists_square_presentation_of_counit_isNilpotent_ker p _ _ ε' Δ' hlaws' hnil

  obtain ⟨r, f₀, hf₀⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1
    (inferInstance : Algebra.FiniteType O (G.A (n + 1)))
  have hfa : f₀ = MvPolynomial.aeval (fun i => f₀ (MvPolynomial.X i)) :=
    MvPolynomial.algHom_ext fun i => by rw [MvPolynomial.aeval_X]
  have hmap : ∀ {τ : Type} (x : τ → G.A (n + 1)) (q : MvPolynomial τ O),
      MvPolynomial.aeval (fun j => ρ (x j)) (MvPolynomial.map (algebraMap O (IsLocalRing.ResidueField O)) q) =
        ρ (MvPolynomial.aeval x q) := by
    intro τ x q
    rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_map, MvPolynomial.eval₂_comp_left]
    congr 1
    exact RingHom.ext fun c => (hρalg c).symm
  have haH : Function.Surjective (MvPolynomial.aeval (fun i => ρ (f₀ (MvPolynomial.X i))) :
      MvPolynomial (Fin r) (IsLocalRing.ResidueField O) →ₐ[IsLocalRing.ResidueField O] _) := fun h => by
    obtain ⟨y, rfl⟩ := hρs h
    obtain ⟨q, rfl⟩ := hf₀ y
    exact ⟨_, (hmap (fun i => f₀ (MvPolynomial.X i)) q).trans (by rw [← hfa])⟩
  obtain ⟨s, y, g, hg0, hgker⟩ := GlobalTheory.T.exists_presentation_square_at_point_of_localFactor _ _ _ e he1 hei hpres r _ haH
  choose yt hyt using fun i => hρs (y i)
  obtain ⟨x, hxd⟩ : ∃ x : Fin s ⊕ Fin r → G.A (n + 1), x = Sum.elim yt (fun i => f₀ (MvPolynomial.X i)) := ⟨_, rfl⟩
  have hx : (fun j => ρ (x j)) = Sum.elim y (fun i => ρ (f₀ (MvPolynomial.X i))) := by
    funext j
    cases j <;> simp [hxd, hyt]
  have hxs : Function.Surjective (MvPolynomial.aeval x : MvPolynomial (Fin s ⊕ Fin r) (G.A n) →ₐ[G.A n] G.A (n + 1)) := by
    intro z
    obtain ⟨q, rfl⟩ := hf₀ z
    refine ⟨MvPolynomial.map (algebraMap O (G.A n)) (MvPolynomial.rename Sum.inr q), ?_⟩
    rw [MvPolynomial.aeval_map_algebraMap, MvPolynomial.aeval_rename, hfa, hxd]
    rfl
  haveI : Module.FinitePresentation O (G.A (n + 1)) := Module.finitePresentation_of_projective _ _
  haveI : Algebra.FinitePresentation O (G.A (n + 1)) := Algebra.FinitePresentation.of_finitePresentation _ _
  haveI : Algebra.FinitePresentation (G.A n) (G.A (n + 1)) :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation O _ _
  have hFG : (RingHom.ker (MvPolynomial.aeval x : MvPolynomial (Fin s ⊕ Fin r) (G.A n) →ₐ[G.A n] G.A (n + 1))).FG :=
    Algebra.FinitePresentation.ker_fG_of_surjective _ hxs
  obtain ⟨f, hf0, hfker⟩ := GlobalTheory.T.lift_square_presentation_of_flat_alt O (G.A n) (G.A (n + 1)) (IsLocalRing.ResidueField O) _ (Fin s ⊕ Fin r)
    (Bialgebra.counitAlgHom O (G.A (n + 1))) (algebraMap O (IsLocalRing.ResidueField O)) ρ
    (Bialgebra.counitAlgHom (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O ⊗[O] G.A 1)) x
    hπs hπk hρalg hεH hkerρ hxs hFG g (by rw [hx]; exact hg0) (by rw [hx]; exact hgker)
  have hpt : ∀ a ∈ RingHom.ker (Bialgebra.counitAlgHom O (G.A (n + 1))), (p : O) • a ∈
      RingHom.ker (Bialgebra.counitAlgHom O (G.A (n + 1))) ^ 2 ⊔
        ((RingHom.ker (Bialgebra.counitAlgHom O (G.A (n + 1)))).comap (algebraMap (G.A n) (G.A (n + 1)))).map
          (algebraMap (G.A n) (G.A (n + 1))) := by
    rw [hker]
    exact GlobalTheory.T.natCast_smul_mem_augIdealSq_sup_map_mulP p O G n
  have := GlobalTheory.T.cotangent_map_injective_of_square_presentation_at_point O (G.A n) (G.A (n + 1)) (Fin s ⊕ Fin r) (Bialgebra.counitAlgHom O (G.A (n + 1))) x f (p : O)
    hp0 hxs hf0 hfker hpt b hb
  rwa [hker] at this
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormTraceFormDetIndex
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

namespace GlobalTheory.LieIndex

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def skewSub (G : Matrix (Fin r) (Fin r) E) : Submodule (maximalRealSubfield E) (Matrix (Fin r) (Fin r) E) where
  carrier := {X | X.trace = 0 ∧ ∀ u w, herm G (X *ᵥ u) w + herm G u (X *ᵥ w) = 0}
  zero_mem' := ⟨by simp, by simp [herm, cc]⟩
  add_mem' {X Y} hX hY := by
    refine ⟨by rw [trace_add, hX.1, hY.1, add_zero], fun u w => ?_⟩
    have h1 := hX.2 u w
    have h2 := hY.2 u w
    simp only [herm, cc, add_mulVec, Pi.add_apply, map_add, add_mul, mul_add, Finset.sum_add_distrib] at h1 h2 ⊢
    linear_combination h1 + h2
  smul_mem' c X hX := by
    have hc : IsCMField.complexConj E (c : E) = c := IsCMField.complexConj_apply_eq_self E c
    have e : c • X = (c : E) • X := rfl
    refine ⟨by rw [e, trace_smul, hX.1, smul_zero], fun u w => ?_⟩
    have h1 := hX.2 u w
    rw [e]
    simp only [herm, cc, smul_mulVec, Pi.smul_apply, smul_eq_mul, map_mul, hc] at h1 ⊢
    have e1 : ∀ a b, ((c : E) * (X *ᵥ u) a) * G a b * (IsCMField.complexConj E) (w b) =
        (c : E) * ((X *ᵥ u) a * G a b * (IsCMField.complexConj E) (w b)) := fun a b => by ring
    have e2 : ∀ a b, u a * G a b * ((c : E) * (IsCMField.complexConj E) ((X *ᵥ w) b)) =
        (c : E) * (u a * G a b * (IsCMField.complexConj E) ((X *ᵥ w) b)) := fun a b => by ring
    simp only [e1, e2, ← Finset.mul_sum]
    rw [← mul_add, h1, mul_zero]

def trForm (G : Matrix (Fin r) (Fin r) E) (hG : ∀ a b, cc (G a b) = G b a) (hd : G.det ≠ 0) :
    LinearMap.BilinForm (maximalRealSubfield E) (skewSub G) :=
  LinearMap.mk₂ (maximalRealSubfield E)
    (fun X Y => ⟨(X.1 * Y.1).trace, GlobalTheory.T.trace_product_skew_hermitian_real E r G X.1 Y.1 hG hd X.2.2 Y.2.2⟩)
    (fun X₁ X₂ Y => Subtype.ext (by simp [add_mul, trace_add]))
    (fun c X Y => Subtype.ext (by simp [trace_smul]; rfl))
    (fun X Y₁ Y₂ => Subtype.ext (by simp [mul_add, trace_add]))
    (fun c X Y => Subtype.ext (by simp [trace_smul]; rfl))

theorem trForm_apply (G : Matrix (Fin r) (Fin r) E) (hG : ∀ a b, cc (G a b) = G b a) (hd : G.det ≠ 0)
    (X Y : skewSub G) : ((trForm G hG hd X Y : maximalRealSubfield E) : E) = (X.1 * Y.1).trace := rfl

theorem norm_algebraMap_real (d : maximalRealSubfield E) :
    Algebra.norm ℚ (algebraMap (maximalRealSubfield E) E d) = (Algebra.norm ℚ d) ^ 2 := by
  rw [← Algebra.norm_norm (R := ℚ) (S := maximalRealSubfield E), Algebra.norm_algebraMap,
    Algebra.IsQuadraticExtension.finrank_eq_two, map_pow]

theorem isIntegral_coe_iff (x : maximalRealSubfield E) : IsIntegral ℤ (x : E) ↔ IsIntegral ℤ x :=
  isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ (maximalRealSubfield E) E)
    (IsScalarTower.toAlgHom ℤ (maximalRealSubfield E) E).toRingHom.injective

theorem abs_norm_gram_eq_index : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (e : Fin (r ^ 2 - 1) → Matrix (Fin r) (Fin r) E), 2 ≤ r → SelfDualLat G Λ → (∀ i, e i ∈ lieLat G Λ) → LinearIndependent (maximalRealSubfield E) e → |((Algebra.norm ℚ (Matrix.of fun i j => Matrix.trace (e i * e j)).det : ℚ) : ℝ)| = (((lieLat G Λ).relIndex (AddSubgroup.closure {Y : Matrix (Fin r) (Fin r) E | Y.trace = 0 ∧ (∀ u w, herm G (Y *ᵥ u) w + herm G u (Y *ᵥ w) = 0) ∧ ∀ X ∈ lieLat G Λ, IsIntegral ℤ (Matrix.trace (X * Y))}) : ℝ) * ((Submodule.span (𝓞 (maximalRealSubfield E)) (Set.range e)).toAddSubgroup.relIndex (lieLat G Λ) : ℝ) ^ 2) ^ 2 := by
  intro E _ _ _ r G Λ e hr hΛ he hli
  obtain ⟨hG, hd, hfg, hsp, -⟩ := hΛ
  have heV : ∀ i, e i ∈ skewSub G := fun i => ⟨(he i).1, (he i).2.1⟩
  set v : Fin (r ^ 2 - 1) → skewSub G := fun i => ⟨e i, heV i⟩ with hv_def
  have hve : (skewSub G).subtype ∘ v = e := rfl
  have hvli : LinearIndependent (maximalRealSubfield E) v :=
    LinearIndependent.of_comp (skewSub G).subtype (by rw [hve]; exact hli)
  have hmapv : Submodule.map (skewSub G).subtype (Submodule.span (maximalRealSubfield E) (Set.range v)) =
      Submodule.span _ (Set.range e) := by
    rw [Submodule.map_span, ← Set.range_comp, hve]
  have hspan : ⊤ ≤ Submodule.span (maximalRealSubfield E) (Set.range v) := by
    rintro ⟨X, hX⟩ -
    have h := GlobalTheory.T.lie_basis_spans_unitary_lie E r G e hG hd heV hli X hX.1 hX.2
    rw [← hmapv] at h
    obtain ⟨y, hy, hyX⟩ := h
    have : y = ⟨X, hX⟩ := Subtype.ext hyX
    rwa [← this]
  set b := Module.Basis.mk hvli hspan with hb
  have hbv : ∀ i, b i = v i := fun i => Module.Basis.mk_apply hvli hspan i
  set B := trForm G hG hd with hB
  set f : skewSub G →+ Matrix (Fin r) (Fin r) E := (skewSub G).subtype.toAddMonoidHom with hf_def
  have hf : Function.Injective f := Subtype.val_injective
  set L' := (lieLat G Λ).comap f with hL'
  have hLrange : lieLat G Λ ≤ f.range := fun X hX => ⟨⟨X, hX.1, hX.2.1⟩, rfl⟩
  have hLmap : L'.map f = lieLat G Λ := AddSubgroup.map_comap_eq_self hLrange
  have hsymm : B.IsSymm := ⟨fun x y => Subtype.ext (by rw [hB, trForm_apply, trForm_apply]; exact Matrix.trace_mul_comm _ _)⟩
  have hsep : ∀ X : skewSub G, (∀ Y : skewSub G, B X Y = 0) → X = 0 := by
    intro X hX
    apply Subtype.ext
    refine GlobalTheory.T.eq_zero_of_trace_form_skew_hermitian E r G X.1 hG hd X.2.1 X.2.2 fun Y hY1 hY2 => ?_
    have := congrArg (fun z : maximalRealSubfield E => (z : E)) (hX ⟨Y, hY1, hY2⟩)
    simpa [hB, trForm_apply] using this
  have hnd : B.Nondegenerate := ⟨fun X hX => hsep X hX, fun Y hY => hsep Y fun X => by rw [hsymm.eq]; exact hY X⟩
  have hbL : ∀ i, b i ∈ L' := fun i => by rw [hbv]; exact he i
  have hsm : ∀ (a : 𝓞 (maximalRealSubfield E)) x, x ∈ L' → a • x ∈ L' := by
    intro a x hx
    refine ⟨(a • x).2.1, (a • x).2.2, fun y hy => ?_⟩
    have hc : IsIntegral ℤ (((a : maximalRealSubfield E) : E)) := (isIntegral_coe_iff _).2 a.isIntegral_coe
    have e1 : (f (a • x)) = (((a : maximalRealSubfield E) : E)) • x.1 := rfl
    rw [e1, smul_mulVec]
    have e2 : (((a : maximalRealSubfield E) : E)) • (x.1 *ᵥ y) = (⟨_, (mem_integralClosure_iff ℤ E).2 hc⟩ : 𝓞 E) • (x.1 *ᵥ y) := by
      rw [← algebraMap_smul E (⟨_, (mem_integralClosure_iff ℤ E).2 hc⟩ : 𝓞 E) (x.1 *ᵥ y)]; rfl
    rw [e2]
    exact Λ.smul_mem _ (hx.2.2 y hy)
  have hint : ∀ x ∈ L', ∀ y ∈ L', IsIntegral ℤ (B x y) := by
    intro x hx y hy
    rw [← isIntegral_coe_iff, hB, trForm_apply]
    refine GlobalTheory.T.trace_integral_of_preserved_lattice E r Λ _ hfg hsp fun z hz => ?_
    rw [← mulVec_mulVec]
    exact hx.2.2 _ (hy.2.2 z hz)
  have key := GlobalTheory.T.norm_gram_det_eq_index (maximalRealSubfield E) (skewSub G) (r ^ 2 - 1) b B L' hsymm hnd hbL hsm hint
  have hdet : (Matrix.of fun i j => Matrix.trace (e i * e j)).det =
      algebraMap (maximalRealSubfield E) E (Matrix.of fun i j => B (b i) (b j)).det := by
    rw [RingHom.map_det]
    congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, hbv]
    rfl
  have I1 : (lieLat G Λ).relIndex (AddSubgroup.closure {Y : Matrix (Fin r) (Fin r) E | Y.trace = 0 ∧
      (∀ u w, herm G (Y *ᵥ u) w + herm G u (Y *ᵥ w) = 0) ∧ ∀ X ∈ lieLat G Λ, IsIntegral ℤ (Matrix.trace (X * Y))}) =
      L'.relIndex (AddSubgroup.closure {y | ∀ x ∈ L', IsIntegral ℤ (B x y)}) := by
    rw [← AddSubgroup.relIndex_map_map_of_injective _ _ hf, hLmap, AddMonoidHom.map_closure]
    congr 2
    ext Y
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨⟨Y, h1, h2⟩, fun x hx => ?_, rfl⟩
      rw [← isIntegral_coe_iff, hB, trForm_apply]
      exact h3 _ hx
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2.1, y.2.2, fun X hX => ?_⟩
      have := hy ⟨X, hX.1, hX.2.1⟩ hX
      rw [← isIntegral_coe_iff, hB, trForm_apply] at this
      exact this
  have I2 : (Submodule.span (𝓞 (maximalRealSubfield E)) (Set.range e)).toAddSubgroup.relIndex (lieLat G Λ) =
      (Submodule.span (𝓞 (maximalRealSubfield E)) (Set.range b)).toAddSubgroup.relIndex L' := by
    rw [← AddSubgroup.relIndex_map_map_of_injective _ _ hf, hLmap]
    congr 1
    let g : skewSub G →ₗ[𝓞 (maximalRealSubfield E)] Matrix (Fin r) (Fin r) E :=
      { toFun := Subtype.val, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have hg : (Submodule.span (𝓞 (maximalRealSubfield E)) (Set.range b)).map g =
        Submodule.span (𝓞 (maximalRealSubfield E)) (Set.range e) := by
      rw [Submodule.map_span, ← Set.range_comp]
      congr 2
      funext i
      simp [g, hbv, v]
    rw [← hg, Submodule.map_toAddSubgroup]
    rfl
  rw [hdet, norm_algebraMap_real, I1, I2, ← key]
  push_cast
  rw [abs_pow, sq_abs]

end GlobalTheory.LieIndex
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitUnfoldIntegralPartitionOfUnityStatement
section
open NumberField MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbit_unfold_integral_partition_of_unity : ∀ (I : Type) [Fintype I] (U : Type) [Countable U] (t : U → I → ℝ) (p : (I → ℝ) → ℝ), Measurable p → (∀ y, 0 ≤ p y) → (∀ y, HasSum (fun u => p (y - t u)) 1) → ∀ g : (I → ℝ) → ℂ, Integrable g → HasSum (fun u => ∫ y, (p y : ℂ) * g (y + t u)) (∫ y, g y) ∧ HasSum (fun u => ∫ y, p y * ‖g (y + t u)‖) (∫ y, ‖g y‖) := by
  first | exact @GlobalTheory.OrbitUnfold.orbit_unfold | exact GlobalTheory.OrbitUnfold.orbit_unfold | (intros; apply GlobalTheory.OrbitUnfold.orbit_unfold <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupResidueFieldTateLevelSectionStatement
section
open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pDivGroup_residueField_tate_level_section : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] [IsLocalRing O], v.Integers O → ∀ G : PDivGroup p O, (∀ (n : ℕ) (c : G.A n →ₐ[O] IsLocalRing.ResidueField O), ∃ t : G.TateOver (IsLocalRing.ResidueField O), t.pt n = c) ∧ ∃ s : G.TateOver (IsLocalRing.ResidueField O) →ₗ[ℤ_[p]] G.Tate, (∀ t, G.tatePush (Algebra.ofId O (IsLocalRing.ResidueField O)) (s t) = t) ∧ ∀ (n : ℕ) (t t' : G.TateOver (IsLocalRing.ResidueField O)), t.pt n = t'.pt n → (s t).pt n = (s t').pt n := by
  first | exact @GlobalTheory.TateResidue.main | exact GlobalTheory.TateResidue.main | (intros; apply GlobalTheory.TateResidue.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PderivPderivCommFock
section
open Formalism.BasicNotions.TH MvPolynomial

namespace GlobalTheory

theorem pderiv_pderiv_comm_fock {σ : Type} (i j : σ) (P : MvPolynomial σ ℂ) :
    pderiv i (pderiv j P) = pderiv j (pderiv i P) := by
  classical
  have hc : ∀ (a b k : σ), pderiv a (pderiv b (X k : MvPolynomial σ ℂ)) = 0 := by
    intro a b k
    rw [pderiv_X, Pi.single_apply]
    split_ifs
    · exact pderiv_one
    · exact map_zero _
  refine MvPolynomial.induction_on (motive := fun P => pderiv i (pderiv j P) = pderiv j (pderiv i P)) P ?_ ?_ ?_
  · intro a
    simp
  · intro p q hp hq
    rw [map_add, map_add, map_add, map_add, hp, hq]
  · intro p k hp
    simp only [pderiv_mul, map_add, hc, mul_zero, add_zero]
    rw [hp]
    ring

theorem fock_letters_ccr (p q r s : ℕ) (l m : Ln p q r s) :
    (lowB l * raiB m - raiB m * lowB l = if l = m then (1 : Module.End ℂ (Pol p q r s)) else 0) ∧
      lowB l * lowB m = lowB m * lowB l ∧ raiB l * raiB m = raiB m * raiB l := by
  classical
  have hcomm : ∀ (i j : Ln p q r s) (P : Pol p q r s), pderiv i (pderiv j P) = pderiv j (pderiv i P) :=
    fun i j P => pderiv_pderiv_comm_fock i j P
  have hX : ∀ (i j : Ln p q r s), pderiv i (X j : Pol p q r s) = if j = i then 1 else 0 := by
    intro i j
    rw [pderiv_X, Pi.single_apply]
  have hne : ∀ l m : Ln p q r s, linePos l ≠ linePos m → l ≠ m := by
    rintro l m h rfl
    exact h rfl
  refine ⟨?_, ?_, ?_⟩
  · by_cases hlm : l = m
    · subst hlm
      rw [if_pos rfl]
      cases hl : linePos l <;> simp only [lowB, raiB, hl, Bool.false_eq_true, ↓reduceIte] <;>
        refine LinearMap.ext fun f => ?_ <;>
        simp [Module.End.mul_apply, hX]
    · rw [if_neg hlm]
      cases hl : linePos l <;> cases hm : linePos m <;>
        simp only [lowB, raiB, hl, hm, Bool.false_eq_true, ↓reduceIte] <;>
        refine LinearMap.ext fun f => ?_ <;>
        simp [Module.End.mul_apply, hX, hcomm, Ne.symm hlm, hlm] <;> ring
  · cases hl : linePos l <;> cases hm : linePos m <;>
      simp only [lowB, hl, hm, Bool.false_eq_true, ↓reduceIte] <;>
      refine LinearMap.ext fun f => ?_ <;>
      simp [Module.End.mul_apply, hX, hcomm] <;> (try ring_nf) <;> (try (intro h; subst h; exact absurd (hl.symm.trans hm) (by decide)))
  · cases hl : linePos l <;> cases hm : linePos m <;>
      simp only [raiB, hl, hm, Bool.false_eq_true, ↓reduceIte] <;>
      refine LinearMap.ext fun f => ?_ <;>
      simp [Module.End.mul_apply, hX, hcomm] <;> (try ring_nf) <;> (try (intro h; subst h; exact absurd (hl.symm.trans hm) (by decide)))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalIdeleIntegralIffUnit
section
open NumberField IsDedekindDomain Formalism.L2.DIV Formalism.UG

namespace GlobalTheory.RatIdInt

theorem mem_RInt_iff_isIntegral (L : Type) [Field L] [NumberField L] (x : L) :
    (x ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈ RInt ℚ L ↔ IsIntegral ℤ x := by
  obtain ⟨ι, h1, h2, -⟩ := GlobalTheory.AdeleBaseChange.exists_finiteAdele_baseChange_equiv ℚ L
  constructor
  · intro hx
    have hv := (h2 _).1 hx
    rw [h1] at hv
    have hr : x ∈ (algebraMap (𝓞 L) L).range := by
      apply HeightOneSpectrum.mem_integers_of_valuation_le_one
      intro P
      have := hv P
      rwa [FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at this
    obtain ⟨y, rfl⟩ := hr
    exact RingOfIntegers.isIntegral_coe y
  · intro hx
    apply Subring.subset_closure
    exact Or.inl ⟨⟨x, ⟨⟨x, hx⟩, rfl⟩⟩, rfl⟩

theorem ratId_mem_intU_iff : ∀ (L : Type) [Field L] [NumberField L] (a : Lˣ),
    ratId ℚ L a ∈ intU ℚ L ↔ IsIntegral ℤ (a : L) ∧ IsIntegral ℤ ((a⁻¹ : Lˣ) : L) := by
  intro L _ _ a
  rw [intU, Submonoid.mem_units_iff, ← map_inv]
  exact and_congr (mem_RInt_iff_isIntegral L (a : L)) (mem_RInt_iff_isIntegral L ((a⁻¹ : Lˣ) : L))

end GlobalTheory.RatIdInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProperLiftTraitOfGenericLiftStatement
section
open AlgebraicGeometry CategoryTheory IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.proper_lift_trait_of_generic_lift : ∀ {X Y : Scheme.{0}} (π : Y ⟶ X), IsProper π → ∀ (V V' : Type) [CommRing V] [IsDomain V] [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V'] (f : V →+* V') (fK : FractionRing V →+* FractionRing V'), (∀ a, fK (algebraMap V _ a) = algebraMap V' _ (f a)) → ∀ (ξ : Sp V ⟶ X) (y : Sp (FractionRing V') ⟶ Y), y ≫ π = spMap fK ≫ jK V ≫ ξ → ∃ ξ' : Sp V' ⟶ Y, ξ' ≫ π = spMap f ≫ ξ ∧ jK V' ≫ ξ' = y := by
  first | exact @GlobalTheory.proper_lift_trait | exact GlobalTheory.proper_lift_trait | (intros; apply GlobalTheory.proper_lift_trait <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackLAdicRationalCohomologyGaloisCoverInvariStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullbackLAdicRationalCohomology_galoisCover_invariants : ∀ (l : ℕ) [Fact l.Prime] {Y X : Scheme.{0}} (f : Y ⟶ X) [IsFinite f] [Etale f] [Surjective f] (G : Type) [Fintype G]
  (a : G → (Y ⟶ Y)) (ha : ∀ g, a g ≫ f = f),
  IsIso (Sigma.desc (fun g => pullback.lift (a g) (𝟙 Y) (by rw [ha g, Category.id_comp])) : ∐ (fun _ : G => Y) ⟶ pullback f f) → ∀ n i : ℤ, Function.Injective (pullHQ l (sch.map f) n i) ∧
  LinearMap.range (pullHQ l (sch.map f) n i) = ⨅ g, LinearMap.ker (pullHQ l (sch.map (a g)) n i - LinearMap.id) := by
  first | (exact @GlobalTheory.pullHQ_galoisCover_inv) | (exact GlobalTheory.pullHQ_galoisCover_inv) | (intros; apply GlobalTheory.pullHQ_galoisCover_inv  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularFormsIsBundleProjectiveCoverStatement
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regularForms_isBundle_projectiveCover : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ (p : ℕ) (W : Type) [AddCommGroup W] [Module K W] [Module F W] [Module k W] [IsScalarTower F K W] [IsScalarTower k F W] [IsScalarTower k K W] (e : W →ₗ[K] DR k K), Function.Injective e → LinearMap.range e = ⋀[K]^p Ω[K⁄k] → IsBundle k x fun I => (omB k K (rB k K x I) p).comap (e.restrictScalars k) := by
  first | (exact @GlobalTheory.PD.omB_isBundle) | (exact GlobalTheory.PD.omB_isBundle) | (intros; apply GlobalTheory.PD.omB_isBundle  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianHaarIndependentOfOrthonormalFrameStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.riemannianHaar_independent_of_orthonormal_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r p0 p1 : ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x y : Frame Ψ r), (∀ a b, cc (G a b) = G b a) → (∀ τ : Ψ, gram τ.1 G (mat x τ) = Matrix.diagonal fun a : Fin r => ((sgn p0 (a : ℕ) : ℝ) : ℂ)) → (∀ τ : Ψ, gram τ.1 G (mat y τ) = Matrix.diagonal fun a : Fin r => ((sgn p1 (a : ℕ) : ℝ) : ℂ)) → riemHaar Ψ G x = riemHaar Ψ G y := by
  first | exact @GlobalTheory.FrameIndep.riemHaar_frame_indep | exact GlobalTheory.FrameIndep.riemHaar_frame_indep | (intros; apply GlobalTheory.FrameIndep.riemHaar_frame_indep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLatticeRealCompletionStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.self_dual_lattice_real_completion : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (g0 : Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)), SelfDualLat G Λ → IsUA (IsCMField.complexConj E) G g0 → ∃ L : Submodule (𝓞 E) (Fin r → E), (L : Set (Fin r → E)) = latOf (maximalRealSubfield E) g0 (Λ : Set (Fin r → E)) ∧ (hat (maximalRealSubfield E) (L : Set (Fin r → E)) : Set (Fin r → RA (maximalRealSubfield E) E)) = g0.mulVec '' (hat (maximalRealSubfield E) (Λ : Set (Fin r → E)) : Set (Fin r → RA (maximalRealSubfield E) E)) ∧ SelfDualLat G L := by
  first | exact @GlobalTheory.UCls.selfDual_latOf_translate | exact GlobalTheory.UCls.selfDual_latOf_translate | (intros; apply GlobalTheory.UCls.selfDual_latOf_translate <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemidirectCosetPairingEqZeroOrTwistStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semidirect_coset_pairing_eq_zero_or_twist : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ), (Nat.card Γ).Prime → s ≠ 1 → ∀ χ χ' : G ⋊[φ] Γ → ℂ, IsIrrChar ℂ ℂ χ → IsIrrChar ℂ ℂ χ' → ∑ᶠ g, χ (inl g * inr s) * star (χ' (inl g * inr s)) = 0 ∨ ∃ η : G ⋊[φ] Γ →* ℂˣ, (∀ g, η (inl g) = 1) ∧ ∀ x, χ x = χ' x * (η x : ℂ) := by
  first | (exact @GlobalTheory.Shin.coset_pair_eq_zero_or_twist) | (exact GlobalTheory.Shin.coset_pair_eq_zero_or_twist) | (intros; apply GlobalTheory.Shin.coset_pair_eq_zero_or_twist <;> assumption)
end

