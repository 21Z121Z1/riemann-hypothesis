import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1173
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0026
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0150
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0971
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0235
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1174
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1175
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1177
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1181
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernIntegralTopIndependentOfSmoothWeight
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

namespace GlobalTheory.ChernMass

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {L : LB X}

theorem sub_pick_eq (φ ψ : Weight p σ L) {y : CxPts p σ} {i : L.ι} (hi : y ∈ ptsIn p σ (L.U i)) :
    ψ.φ (pick φ.isLB y) y - φ.φ (pick φ.isLB y) y = ψ.φ i y - φ.φ i y := by
  rw [ψ.trans _ i y (mem_pick φ.isLB y) hi, φ.trans _ i y (mem_pick φ.isLB y) hi]
  ring

theorem cInfAt_half_sub {φ ψ : Weight p σ L} (hφ : φ.IsCInf) (hψ : ψ.IsCInf) (x : CxPts p σ) :
    CInfAt (fun y => (ψ.φ (pick φ.isLB y) y - φ.φ (pick φ.isLB y) y) / 2) x := by
  have hx := mem_pick φ.isLB x
  refine (((hψ _ x hx).add (hφ _ x hx).neg).const_mul 2⁻¹).congr ?_
  filter_upwards [(isOpen_ptsIn _).mem_nhds hx] with z hz
  rw [sub_pick_eq φ ψ hz]
  ring

theorem mInt_one_eq {D : ℕ} [CompactSpace (CxPts p σ)] [T2Space (CxPts p σ)]
    {A : FinHolAtlas D (CxPts p σ)} (hA : IsAlgAtlas A) {φ ψ : Weight p σ L} (hφ : φ.IsCInf)
    (hψ : ψ.IsCInf) :
    mInt A (fun _ => φ.locPot) (fun _ => 1) = mInt A (fun _ => ψ.locPot) (fun _ => 1) := by
  have hP : IsPotential A φ.locPot :=
    ((Weight.isCInf_iff_isSmooth hA.anRead).1 hφ).isPotential hA
  have hu : A.Smooth fun y => (ψ.φ (pick φ.isLB y) y - φ.φ (pick φ.isLB y) y) / 2 :=
    (hA.smooth_iff hA.anRead).2 ((cInfAt_iff_smoothOn hA.anRead isOpen_univ).1
      fun y _ => cInfAt_half_sub hφ hψ y)
  rw [← massIndep A (fun _ => φ.locPot) (fun _ => _) (fun _ => hP) fun _ => hu]
  refine SameForm.mInt_eq (fun _ j y hy => hessCGerm _ _ _ ?_) _
  refine eventually_of_mem (((A.chart j).isOpen_inter_preimage_symm (isOpen_ptsIn _)).mem_nhds
    ⟨hy, mem_pick φ.isLB ((A.chart j).symm y)⟩) fun w hw => ?_
  change φ.φ _ _ / 2 + (_ - _) / 2 = ψ.φ (pick φ.isLB _) _ / 2
  rw [sub_pick_eq φ ψ hw.2]
  ring

theorem chernInt_one_eq : ∀ (Y : Var ℂ) (L : LB Y.X) (φ ψ : Weight Y.str (RingHom.id ℂ) L), φ.IsCInf → ψ.IsCInf → Weight.chernInt φ Y.dim Set.univ (fun _ => 1) = Weight.chernInt ψ Y.dim Set.univ (fun _ => 1) := fun Y L φ ψ hφ hψ => by
  obtain ⟨h₁, h₂, -, A, hA⟩ := GlobalTheory.T.complexPoints_smoothProjVariety_compact_manifold Y
  rw [(GlobalTheory.T.chernIntegral_one_eq_mongeAmpereIntegral Y L φ hφ).2 A hA, (GlobalTheory.T.chernIntegral_one_eq_mongeAmpereIntegral Y L ψ hψ).2 A hA]
  exact mInt_one_eq hA hφ hψ

end GlobalTheory.ChernMass
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommTensCastRSymmMap
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

noncomputable section

namespace GlobalTheory.ConjFrame

theorem comm_tensCastR_symm_map {E : Type} [Field E] [NumberField E] {F1 F2 : Subfield E} (h : F1 = F2)
    (σ : E →ₐ[F1] E) (τ : E →ₐ[F2] E) (hστ : ∀ x, σ x = τ x) (x : E ⊗[F2] FiniteAdeleRing (𝓞 F2) F2) :
    Algebra.TensorProduct.comm F1 (FiniteAdeleRing (𝓞 F1) F1) E
        ((GlobalTheory.StdFrame.tensCastR h).symm (Algebra.TensorProduct.map τ (AlgHom.id F2 (FiniteAdeleRing (𝓞 F2) F2)) x)) =
      Formalism.UG.sigR σ (FiniteAdeleRing (𝓞 F1) F1)
        (Algebra.TensorProduct.comm F1 (FiniteAdeleRing (𝓞 F1) F1) E ((GlobalTheory.StdFrame.tensCastR h).symm x)) := by
  subst h
  have hc : ∀ y, (GlobalTheory.StdFrame.tensCastR (rfl : F1 = F1)).symm y =
      (Algebra.TensorProduct.comm F1 (FiniteAdeleRing (𝓞 F1) F1) E).symm y := fun _ => rfl
  simp only [hc]
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [Formalism.UG.sigR, Algebra.TensorProduct.map_tmul, hστ]
  | add a b ha hb => simp only [map_add, ha, hb]

theorem swapAE_conjAL : ∀ {D : D7} (hF : D.host.F = maximalRealSubfield D.host.E) (x : ReciprocityTheory.Aut.AL D.host.E), Formalism.IndefR.Lev.swapAE D ((GlobalTheory.StdFrame.tensCastR hF).symm (ReciprocityTheory.Aut.conjAL D.host.E x)) = Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) (Formalism.IndefR.Lev.swapAE D ((GlobalTheory.StdFrame.tensCastR hF).symm x)) := by
  intro D hF x
  exact comm_tensCastR_symm_map hF D.sp.cm.sig ((IsCMField.complexConj D.host.E).toAlgHom) (fun _ => rfl) x

end GlobalTheory.ConjFrame

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjResultantOfEllPolys
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ResConj

theorem prod_product_mul (A B : Multiset ℂ) (f g : ℂ → ℂ) :
    ((A ×ˢ B).map fun ij => f ij.1 * g ij.2).prod =
      (A.map f).prod ^ Multiset.card B * (B.map g).prod ^ Multiset.card A := by
  induction A using Multiset.induction_on with
  | empty => simp
  | cons a A ih =>
    rw [Multiset.cons_product, Multiset.map_add, Multiset.prod_add, ih, Multiset.map_map]
    simp only [Function.comp_def, Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate,
      Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, mul_pow, pow_succ]
    ring

theorem conj_prod_sub (A B : Multiset ℂ) (hA : ∀ x ∈ A, ‖x‖ = 1) (hB : ∀ y ∈ B, ‖y‖ = 1) :
    (starRingEnd ℂ) (((A ×ˢ B).map fun ij => ij.1 - ij.2).prod) *
        (A.prod ^ Multiset.card B * B.prod ^ Multiset.card A) =
      (-1) ^ (Multiset.card A * Multiset.card B) * ((A ×ˢ B).map fun ij => ij.1 - ij.2).prod := by
  have h := prod_product_mul A B id id
  simp only [Multiset.map_id, id, Multiset.map_id'] at h
  rw [← h, map_multiset_prod, Multiset.map_map, ← Multiset.prod_map_mul]
  have hc : ∀ ij ∈ A ×ˢ B, ((starRingEnd ℂ) ∘ fun ij : ℂ × ℂ => ij.1 - ij.2) ij * (ij.1 * ij.2) =
      (-1) * (ij.1 - ij.2) := by
    intro ij hij
    rw [Multiset.mem_product] at hij
    have h1 := hA _ hij.1
    have h2 := hB _ hij.2
    have n1 : ij.1 ≠ 0 := by intro h0; rw [h0, norm_zero] at h1; exact zero_ne_one h1
    have n2 : ij.2 ≠ 0 := by intro h0; rw [h0, norm_zero] at h2; exact zero_ne_one h2
    have c1 : (starRingEnd ℂ) ij.1 = ij.1⁻¹ := by
      rw [Complex.inv_def, Complex.normSq_eq_norm_sq, h1]; simp
    have c2 : (starRingEnd ℂ) ij.2 = ij.2⁻¹ := by
      rw [Complex.inv_def, Complex.normSq_eq_norm_sq, h2]; simp
    simp only [Function.comp_apply, map_sub, c1, c2]
    field_simp
    ring
  rw [Multiset.map_congr rfl hc, Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate,
    Multiset.card_product]

theorem conj_resultant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (P₁ P₂ : E[X]),
    P₁ ∈ Ell E a → P₂ ∈ Ell E b → IsCMField.complexConj E (resultant P₁ P₂) *
      (((-1) ^ a * P₁.coeff 0) ^ b * ((-1) ^ b * P₂.coeff 0) ^ a) = (-1) ^ (a * b) * resultant P₁ P₂ := by
  intro E _ _ _ a b P₁ P₂ h₁ h₂
  obtain ⟨m₁, d₁, -, r₁⟩ := h₁
  obtain ⟨m₂, d₂, -, r₂⟩ := h₂
  let τ : E →+* ℂ := Classical.choice (inferInstance : Nonempty (E →+* ℂ))
  apply τ.injective
  have sA : (P₁.map τ).Splits := IsAlgClosed.splits _
  have sB : (P₂.map τ).Splits := IsAlgClosed.splits _
  have cA : Multiset.card (P₁.map τ).roots = a := by rw [← sA.natDegree_eq_card_roots, natDegree_map, d₁]
  have cB : Multiset.card (P₂.map τ).roots = b := by rw [← sB.natDegree_eq_card_roots, natDegree_map, d₂]
  have hres : τ (resultant P₁ P₂) =
      (((P₁.map τ).roots ×ˢ (P₂.map τ).roots).map fun ij => ij.1 - ij.2).prod := by
    rw [← resultant_eq_prod_roots_sub _ _ (m₁.map τ) (m₂.map τ) sA sB,
      ← resultant_map_map P₁ P₂ P₁.natDegree P₂.natDegree τ, natDegree_map, natDegree_map]
  have e₁ : τ ((-1) ^ a * P₁.coeff 0) = (P₁.map τ).roots.prod := by
    rw [map_mul, map_pow, map_neg, map_one, ← coeff_map, sA.coeff_zero_eq_prod_roots_of_monic (m₁.map τ),
      natDegree_map, d₁, ← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]
  have e₂ : τ ((-1) ^ b * P₂.coeff 0) = (P₂.map τ).roots.prod := by
    rw [map_mul, map_pow, map_neg, map_one, ← coeff_map, sB.coeff_zero_eq_prod_roots_of_monic (m₂.map τ),
      natDegree_map, d₂, ← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]
  have key := conj_prod_sub _ _ (r₁ τ) (r₂ τ)
  rw [cA, cB] at key
  rw [map_mul, map_mul, map_mul, map_pow, map_pow, e₁, e₂, IsCMField.complexEmbedding_complexConj, hres, key,
    map_pow, map_neg, map_one]

end GlobalTheory.ResConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjUnitaryOfSameHermitianMultiplicationModel
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical

namespace GlobalTheory.KapLat

theorem models_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E) (B : GlobalTheory.UnitLemma.InvAlg K) (u x : B.A) (n : ℕ) (γ γ' : GLw n w), IsModel w e B u x γ → IsModel w e B u x γ' → ∃ y ∈ UL n w, γ' = y⁻¹ * γ * y := by
  intro E _ _ _ w hw K e B u x n γ γ' hγ hγ'
  obtain ⟨ψ, hψl, hψu, hψh⟩ := hγ
  obtain ⟨ψ', hψ'l, hψ'u, hψ'h⟩ := hγ'
  let f : (Fin n → w.adicCompletion E) →ₗ[w.adicCompletion E] (Fin n → w.adicCompletion E) :=
    { toFun := fun v => ψ (ψ'.symm v)
      map_add' := by intro a b; simp
      map_smul' := by
        intro t v
        obtain ⟨c, rfl⟩ : ∃ c, e c = t := ⟨e.symm t, e.apply_symm_apply t⟩
        obtain ⟨a, rfl⟩ : ∃ a, ψ' a = v := ⟨ψ'.symm v, ψ'.apply_symm_apply v⟩
        simp only [RingHom.id_apply]
        rw [← hψ'l, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply, hψl] }
  let g : (Fin n → w.adicCompletion E) →ₗ[w.adicCompletion E] (Fin n → w.adicCompletion E) :=
    { toFun := fun v => ψ' (ψ.symm v)
      map_add' := by intro a b; simp
      map_smul' := by
        intro t v
        obtain ⟨c, rfl⟩ : ∃ c, e c = t := ⟨e.symm t, e.apply_symm_apply t⟩
        obtain ⟨a, rfl⟩ : ∃ a, ψ a = v := ⟨ψ.symm v, ψ.apply_symm_apply v⟩
        simp only [RingHom.id_apply]
        rw [← hψl, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply, hψ'l] }
  have hfg : f ∘ₗ g = LinearMap.id := LinearMap.ext fun v => by simp [f, g]
  have hgf : g ∘ₗ f = LinearMap.id := LinearMap.ext fun v => by simp [f, g]
  let y : GLw n w := ⟨LinearMap.toMatrix' f, LinearMap.toMatrix' g,
    by rw [← LinearMap.toMatrix'_comp, hfg, LinearMap.toMatrix'_id],
    by rw [← LinearMap.toMatrix'_comp, hgf, LinearMap.toMatrix'_id]⟩
  have hy : ∀ v, (y : Matrix (Fin n) (Fin n) (w.adicCompletion E)) *ᵥ v = f v := fun v =>
    LinearMap.toMatrix'_mulVec f v

  have hinv : ∀ v v', stdH w (f v) (f v') = stdH w v v' := by
    intro v v'
    obtain ⟨a, rfl⟩ : ∃ a, ψ' a = v := ⟨ψ'.symm v, ψ'.apply_symm_apply v⟩
    obtain ⟨b, rfl⟩ : ∃ b, ψ' b = v' := ⟨ψ'.symm v', ψ'.apply_symm_apply v'⟩
    simp only [f, LinearMap.coe_mk, AddHom.coe_mk, AddEquiv.symm_apply_apply]
    rw [hψh, hψ'h]
  refine ⟨y, ?_, ?_⟩
  · unfold UL
    rw [if_neg hw]
    change Formalism.UG.cT (cj w) (y : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * 1 *
      (y : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = 1
    set M : Matrix (Fin n) (Fin n) (w.adicCompletion E) := (y : Matrix (Fin n) (Fin n) (w.adicCompletion E)) with hM
    have key : Mᵀ * M.map (cj w) = 1 := by
      refine Matrix.ext fun i j => ?_
      have h1 := hinv (Pi.single i 1) (Pi.single j 1)
      rw [← hy, ← hy] at h1
      simp only [stdH, Matrix.mulVec_single_one] at h1
      have h2 : (if i = j then (1 : w.adicCompletion E) else 0) = ∑ k, M k i * cj w (M k j) := by
        simpa [Pi.single_apply, eq_comm] using h1
      rw [Matrix.mul_apply, Matrix.one_apply]
      simp only [Matrix.transpose_apply, Matrix.map_apply]
      exact h2.symm
    have key2 := congrArg Matrix.transpose key
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at key2
    rw [Matrix.mul_one]
    exact key2
  ·
    have hc : (y : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * γ'.val = γ.val * y := by
      apply Matrix.toLin'.injective
      apply LinearMap.ext
      intro v
      obtain ⟨a, rfl⟩ : ∃ a, ψ' a = v := ⟨ψ'.symm v, ψ'.apply_symm_apply v⟩
      simp only [Matrix.toLin'_apply]
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hψ'u, hy, hy]
      simp only [f, LinearMap.coe_mk, AddHom.coe_mk, AddEquiv.symm_apply_apply]
      rw [hψu]
    have hc' : y * γ' = γ * y := Units.ext hc
    rw [mul_assoc, ← hc', ← mul_assoc, inv_mul_cancel, one_mul]

end GlobalTheory.KapLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjZpowersEntriesValuedBoundedOfCompactClosure
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.PowBdd

variable {E : Type} [Field E] [NumberField E]

theorem isOpen_le_exp (w : Pl E) (m : ℤ) :
    IsOpen {y : w.adicCompletion E | Valued.v y ≤ WithZero.exp m} := by
  obtain ⟨c, hc⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective E w (WithZero.exp m)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero] at hc
    exact WithZero.exp_ne_zero hc.symm
  have : {y : w.adicCompletion E | Valued.v y ≤ WithZero.exp m} =
      {y | Valued.v.restrict y ≤ Valued.v.restrict c} := by
    ext y
    simp only [Set.mem_ofPred_eq, Valuation.restrict_le_iff, hc]
  rw [this]
  exact Valued.isOpen_closedBall _ (by simp [hc0])

theorem exists_bound_of_isCompact (w : Pl E) {C : Set (w.adicCompletion E)} (hC : IsCompact C) :
    ∃ B : WithZero (Multiplicative ℤ), ∀ x ∈ C, Valued.v x ≤ B := by
  obtain ⟨s, hs⟩ := hC.elim_finite_subcover (fun m : ℤ => {y : w.adicCompletion E | Valued.v y ≤ WithZero.exp m})
    (fun m => isOpen_le_exp w m) (by
      intro x _
      rw [Set.mem_iUnion]
      by_cases h0 : Valued.v x = 0
      · exact ⟨0, by simp [h0]⟩
      · exact ⟨WithZero.log (Valued.v x), by simp [WithZero.exp_log h0]⟩)
  refine ⟨s.sup fun m => WithZero.exp m, fun x hx => ?_⟩
  obtain ⟨m, hm, hxm⟩ := Set.mem_iUnion₂.1 (hs hx)
  exact hxm.trans (Finset.le_sup (f := fun m => WithZero.exp m) hm)

end GlobalTheory.PowBdd

open GlobalTheory.PowBdd in
theorem GlobalTheory.BCT.powers_entries_bdd : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (t g : UL n w),
    IsCompact (closure (Subgroup.zpowers t : Set (UL n w))) →
    ∃ B : WithZero (Multiplicative ℤ), ∀ (k : ℤ) (i j : Fin n),
      Valued.v ((((g⁻¹ * t ^ k * g : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ B := by
  intro E _ _ _ n w t g hc
  have hent : ∀ i j : Fin n, ∃ B : WithZero (Multiplicative ℤ), ∀ k : ℤ,
      Valued.v ((((g⁻¹ * t ^ k * g : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ B := by
    intro i j
    let f : UL n w → w.adicCompletion E := fun y =>
      (((g⁻¹ * y * g : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j
    have hf : Continuous f := by
      have h1 : Continuous fun y : UL n w => (g⁻¹ * y * g : UL n w) :=
        (continuous_const.mul continuous_id).mul continuous_const
      have h2 : Continuous fun y : UL n w => (((g⁻¹ * y * g : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) :=
        Units.continuous_val.comp (continuous_subtype_val.comp h1)
      exact (continuous_apply j).comp ((continuous_apply i).comp h2)
    obtain ⟨B, hB⟩ := exists_bound_of_isCompact w (hc.image hf)
    refine ⟨B, fun k => hB _ ⟨t ^ k, subset_closure (Subgroup.zpow_mem_zpowers t k), rfl⟩⟩
  choose B hB using hent
  refine ⟨Finset.univ.sup fun p : Fin n × Fin n => B p.1 p.2, fun k i j => ?_⟩
  exact (hB i j k).trans (Finset.le_sup (f := fun p : Fin n × Fin n => B p.1 p.2) (Finset.mem_univ (i, j)))
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtTransgressionTopCoeffComplexStatement
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuousAt_transgressionTopCoeffComplex : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] {ρ : V n → ℝ} {G₀ G₁ : V n → Matrix r r ℂ} {v : V n}, ContDiffAt ℝ 1 ρ v → MContDiffAt 2 G₀ v → IsUnit (G₀ v).det → MContDiffAt 2 G₁ v → IsUnit (G₁ v).det → ContinuousAt (corrC ρ G₀ G₁) v := by
  first | exact @GlobalTheory.GoodTop.continuousAt_corrC | exact GlobalTheory.GoodTop.continuousAt_corrC | (intros; apply GlobalTheory.GoodTop.continuousAt_corrC <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousHeisenbergOperatorBoundedThetaFunctionStatement
section
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_heisenbergOperatorBoundedThetaFunctions : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (nS nT : ℕ)
    (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ), ∀ f : BBF σ JS JT ξ₀ ψ, Continuous fun w => rhoBF σ JS JT ξ₀ ψ hψ w f := by
  first | exact @GlobalTheory.RealWeilF.continuous_rhoBF | exact GlobalTheory.RealWeilF.continuous_rhoBF | (intros; apply GlobalTheory.RealWeilF.continuous_rhoBF <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOneAddLowRankEmbeddingQuaternionMatrix
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.QSA GlobalTheory.PlaneSU
open scoped TensorProduct Quaternion

namespace GlobalTheory

theorem emb_qm_continuous : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (a b : F) (M : ℕ) (A : Matrix (Fin M) (Fin 2) (AF F ⊗[F] E)) (B : Matrix (Fin 2) (Fin M) (AF F ⊗[F] E)) (θ : AF F ⊗[F] E), Continuous fun x : DA F a b => emb A B (qm (algebraMap (AF F) (AF F ⊗[F] E)) θ x) := by
  intro F E _ _ _ _ a b M A B θ
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalAddGroup (AF F ⊗[F] E) := IsModuleTopology.topologicalAddGroup (AF F) _
  have hL : ∀ c : AF F ⊗[F] E, Continuous (fun y : AF F ⊗[F] E => c * y) := fun c =>
    IsModuleTopology.continuous_of_linearMap (LinearMap.mulLeft (AF F) c)
  have hR : ∀ c : AF F ⊗[F] E, Continuous (fun y : AF F ⊗[F] E => y * c) := fun c =>
    IsModuleTopology.continuous_of_linearMap (LinearMap.mulRight (AF F) c)
  have hι : Continuous (algebraMap (AF F) (AF F ⊗[F] E)) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (AF F) (AF F ⊗[F] E))
  have hc : ∀ i, Continuous fun x : DA F a b => coords x i := fun i =>
    (continuous_apply i).comp continuous_induced_dom
  have h0 : Continuous fun x : DA F a b => x.re := by simpa [coords] using hc 0
  have h1 : Continuous fun x : DA F a b => x.imI := by simpa [coords] using hc 1
  have h2 : Continuous fun x : DA F a b => x.imJ := by simpa [coords] using hc 2
  have h3 : Continuous fun x : DA F a b => x.imK := by simpa [coords] using hc 3
  have hq : ∀ k l, Continuous fun x : DA F a b => qm (algebraMap (AF F) (AF F ⊗[F] E)) θ x k l := by
    intro k l
    fin_cases k <;> fin_cases l <;> simp [qm]
    · exact (hι.comp h0).add ((hR θ).comp (hι.comp h1))
    · exact (hL _).comp ((hι.comp h2).add ((hR θ).comp (hι.comp h3)))
    · exact (hι.comp h2).sub ((hR θ).comp (hι.comp h3))
    · exact (hι.comp h0).sub ((hR θ).comp (hι.comp h1))
  apply continuous_matrix
  intro i j
  simp only [emb, Matrix.add_apply, Matrix.mul_apply, Matrix.sub_apply]
  refine continuous_const.add (continuous_finset_sum _ fun l _ => (hR _).comp
    (continuous_finset_sum _ fun k _ => (hL _).comp ((hq k l).sub continuous_const)))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousPlaceAt
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
open MeasureTheory

noncomputable section

namespace GlobalTheory.PlaceCoordsF

variable {F : Type} [Field F] [NumberField F]

def placeAt (v : HeightOneSpectrum (𝓞 F)) (x : Fv F v) : AF F := pairA F 0 (GlobalTheory.AdelicU.singleFin v x)

theorem placeAt_add (v : HeightOneSpectrum (𝓞 F)) (x y : Fv F v) :
    placeAt v (x + y) = placeAt v x + placeAt v y := by
  unfold placeAt pairA
  rw [map_add]
  exact Prod.ext (add_zero 0).symm rfl

theorem placeAt_injective (v : HeightOneSpectrum (𝓞 F)) : Function.Injective (placeAt v) := by
  intro x y h
  have h2 := congrArg (fun c : AF F => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v c.2) h
  simpa only [placeAt, pairA, GlobalTheory.AdelicU.evalV_singleFin_self] using h2

theorem continuous_placeAt (v : HeightOneSpectrum (𝓞 F)) : Continuous (placeAt v) := by
  unfold placeAt pairA
  exact continuous_const.prodMk (GlobalTheory.AdelicU.continuous_singleFin v)

theorem eq_placeAt_of_mul {v : HeightOneSpectrum (𝓞 F)} {α : Af F} (hα1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v α = 1)
    (hα0 : ∀ v', v' ≠ v → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v' α = 0) {c : AF F} (hc : pairA F 0 α * c = c) :
    c = placeAt v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v c.2) := by
  have h1 : c.1 = 0 := by
    have := congrArg Prod.fst hc
    rw [← this]
    exact zero_mul _
  have h2 : α * c.2 = c.2 := congrArg Prod.snd hc
  refine Prod.ext h1 ?_
  show c.2 = GlobalTheory.AdelicU.singleFin v _
  refine GlobalTheory.AdelicU.af_ext fun u => ?_
  by_cases hu : u = v
  · subst hu
    rw [GlobalTheory.AdelicU.evalV_singleFin_self]
  · rw [GlobalTheory.AdelicU.evalV_singleFin_ne hu, ← h2, map_mul, hα0 u hu, zero_mul]

end GlobalTheory.PlaceCoordsF

namespace GlobalTheory.PlaceCoordsF

theorem coords_at_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (ε : AF F), IsPlaceIdemF F v ε → ∀ nS nT : ℕ,
      ∃ (N : ℕ) (Φ : (Fin N → v.adicCompletion F) →+ WOF F E nS nT), Continuous Φ ∧ Function.Injective Φ ∧
        ∀ y : WOF F E nS nT, (∀ i j, algebraMap (AF F) (AEF F E) ε * y i j = y i j) → y ∈ Set.range Φ := by
  intro F E _ _ _ _ _ v ε hε nS nT
  obtain ⟨α, rfl, hα1, hα0⟩ := hε
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AEF F E) := ⟨rfl⟩
  haveI := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)
  let B : Module.Basis (Fin (Module.finrank F E)) (AF F) (AEF F E) :=
    Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)
  let e := Fintype.equivFin (Fin nT × Fin nS × Fin (Module.finrank F E))
  let f : (Fin (Fintype.card (Fin nT × Fin nS × Fin (Module.finrank F E))) → v.adicCompletion F) → WOF F E nS nT :=
    fun t i j => B.equivFun.symm (fun l => placeAt v (t (e (i, j, l))))
  have hadd : ∀ s t, f (s + t) = f s + f t := by
    intro s t
    funext i j
    show B.equivFun.symm _ = B.equivFun.symm _ + B.equivFun.symm _
    rw [← map_add]
    congr 1
    funext l
    exact placeAt_add v _ _
  let Φ := AddMonoidHom.mk' f hadd
  refine ⟨_, Φ, ?_, ?_, ?_⟩
  · have hB : Continuous B.equivFun.symm := IsModuleTopology.continuous_of_linearMap B.equivFun.symm.toLinearMap
    exact continuous_pi fun i => continuous_pi fun j =>
      hB.comp (continuous_pi fun l => (continuous_placeAt v).comp (continuous_apply _))
  · intro s t hst
    have key : ∀ i j l, s (e (i, j, l)) = t (e (i, j, l)) := by
      intro i j l
      have h1 : f s i j = f t i j := congrFun (congrFun hst i) j
      have h2 := congrFun (B.equivFun.symm.injective h1) l
      exact placeAt_injective v h2
    funext k
    have := key (e.symm k).1 (e.symm k).2.1 (e.symm k).2.2
    simpa only [Prod.mk.eta, Equiv.apply_symm_apply] using this
  · intro y hy
    have hc : ∀ i j l, B.equivFun (y i j) l =
        placeAt v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (B.equivFun (y i j) l).2) := by
      intro i j l
      refine eq_placeAt_of_mul hα1 hα0 ?_
      have h1 : pairA F 0 α • y i j = y i j := by rw [Algebra.smul_def]; exact hy i j
      have h2 := congrFun (congrArg B.equivFun h1) l
      rw [map_smul, Pi.smul_apply, smul_eq_mul] at h2
      exact h2
    refine ⟨fun k => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (B.equivFun (y (e.symm k).1 (e.symm k).2.1) (e.symm k).2.2).2, ?_⟩
    funext i j
    show B.equivFun.symm _ = y i j
    simp only [Equiv.symm_apply_apply]
    rw [← B.equivFun.symm_apply_apply (y i j)]
    congr 1
    funext l
    rw [B.equivFun.symm_apply_apply]
    exact (hc i j l).symm

end GlobalTheory.PlaceCoordsF
end
end

