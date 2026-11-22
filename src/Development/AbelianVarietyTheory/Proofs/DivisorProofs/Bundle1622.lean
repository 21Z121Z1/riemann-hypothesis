import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1607
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PairingMulFirstChern
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0025
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1564
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1088
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqGenericPoint
import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoGenResMapSmulHom
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1608
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1252
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1545
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1589
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1462
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1473
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1478
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeDegreeGrowthChowFormIntegrality
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1590
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1573
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0887
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1558
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousThetaTransformAdelicSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernAtTwoEq
section
set_option autoImplicit false

noncomputable section

open Set Matrix Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.HermFrame GlobalTheory.CxForm GlobalTheory.SecForm
open GlobalTheory.GoodMetric (coordVec)
open scoped ContDiff ComplexOrder

namespace GlobalTheory.SecForm.ChernTwo

variable {n : ℕ}

theorem sym_mul_swap (a b c d : Fin n) : sym (a, b) * sym (c, d) = -(sym (a, d) * sym (c, b)) := by
  apply Subtype.ext
  have h (u w : Fin n ⊕ Fin n → ℂ) : ExteriorAlgebra.ι ℂ u * ExteriorAlgebra.ι ℂ w =
      -(ExteriorAlgebra.ι ℂ w * ExteriorAlgebra.ι ℂ u) :=
    eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap u w)
  have h3 : dzb b * (dz c * dzb d) = -(dzb d * (dz c * dzb b)) := by
    have e1 : dzb b * dz c = -(dz c * dzb b) := h _ _
    have e2 : dzb b * dzb d = -(dzb d * dzb b) := h _ _
    have e3 : dz c * dzb d = -(dzb d * dz c) := h _ _
    rw [← mul_assoc, e1, neg_mul, mul_assoc, e2, mul_neg, ← mul_assoc, e3, neg_mul, neg_neg, mul_assoc]
  change dz a * dzb b * (dz c * dzb d) = -(dz a * dzb d * (dz c * dzb b))
  rw [mul_assoc, h3, mul_neg, mul_assoc]

def four (f : Fin n → Fin n → Fin n → Fin n → ℂ) : Ev n :=
  ∑ a, ∑ b, ∑ c, ∑ d, f a b c d • (sym (a, b) * sym (c, d))

theorem four_eq (f : Fin n → Fin n → Fin n → Fin n → ℂ) :
    four f = ∑ x : (Fin n × Fin n) × (Fin n × Fin n), f x.1.1 x.1.2 x.2.1 x.2.2 • (sym x.1 * sym x.2) := by
  simp only [four, Fintype.sum_prod_type]

theorem four_swap (f : Fin n → Fin n → Fin n → Fin n → ℂ) : four (fun a b c d => f c d a b) = four f := by
  rw [four_eq, four_eq]
  refine Fintype.sum_equiv (Equiv.prodComm _ _) _ _ fun x => ?_
  simp [mul_comm]

theorem four_swap' (f : Fin n → Fin n → Fin n → Fin n → ℂ) : four (fun a b c d => f a d c b) = -four f := by
  rw [four_eq, four_eq, ← Finset.sum_neg_distrib]
  refine Fintype.sum_equiv (⟨fun x => ((x.1.1, x.2.2), (x.2.1, x.1.2)), fun x => ((x.1.1, x.2.2), (x.2.1, x.1.2)),
    fun _ => rfl, fun _ => rfl⟩) _ _ ?_
  rintro ⟨⟨a, b⟩, c, d⟩
  simp only [Equiv.coe_fn_mk]
  rw [sym_mul_swap, smul_neg]

theorem four_add (f g : Fin n → Fin n → Fin n → Fin n → ℂ) :
    four (fun a b c d => f a b c d + g a b c d) = four f + four g := by
  simp only [four, add_smul, Finset.sum_add_distrib]

theorem four_sub (f g : Fin n → Fin n → Fin n → Fin n → ℂ) :
    four (fun a b c d => f a b c d - g a b c d) = four f - four g := by
  simp only [four, sub_smul, Finset.sum_sub_distrib]

theorem four_mul (t : ℂ) (f : Fin n → Fin n → Fin n → Fin n → ℂ) :
    four (fun a b c d => t * f a b c d) = t • four f := by
  simp only [four, mul_smul, Finset.smul_sum]

theorem four_wedge (α β : V n → V n → ℂ) :
    four (fun a b c d => wedge α β (coordVec a) (coordVec b) (coordVec c) (coordVec d)) =
      (4 : ℂ) • (ofValues α * ofValues β) := by
  set f : Fin n → Fin n → Fin n → Fin n → ℂ :=
    fun a b c d => α (coordVec a) (coordVec b) * β (coordVec c) (coordVec d) with hf
  have e0 : ofValues α * ofValues β = four f := by
    simp only [ofValues, four, Finset.sum_mul]
    simp only [Finset.mul_sum, smul_mul_smul_comm, hf]
  have e1 := four_swap f
  have e2 := four_swap' f
  have e3 := four_swap' fun a b c d => f c d a b
  have e : four (fun a b c d => wedge α β (coordVec a) (coordVec b) (coordVec c) (coordVec d)) =
      four f + four (fun a b c d => f c d a b) - four (fun a b c d => f a d c b) - four (fun a b c d => f c b a d) := by
    rw [← four_add, ← four_sub, ← four_sub]; rfl
  rw [e, e3, e1, e2, e0]
  module

theorem coeff_two {R : Type} [CommRing R] (F : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) R) :
    (Matrix.charpolyRev (-F)).coeff 2 =
      F (.inl 0) (.inl 0) * F (.inr 0) (.inr 0) - F (.inl 0) (.inr 0) * F (.inr 0) (.inl 0) := by
  rw [Matrix.charpolyRev, ← Matrix.det_submatrix_equiv_self (finSumFinEquiv (m := 1) (n := 1)).symm]
  have h0 : (finSumFinEquiv (m := 1) (n := 1)).symm (0 : Fin 2) = .inl 0 := rfl
  have h1 : (finSumFinEquiv (m := 1) (n := 1)).symm (1 : Fin 2) = .inr 0 := rfl
  rw [Matrix.det_fin_two]
  simp only [Matrix.submatrix_apply, h0, h1]
  have : ∀ p q : Fin 1 ⊕ Fin 1, (1 - (Polynomial.X : Polynomial R) • (-F).map Polynomial.C) p q =
      (if p = q then 1 else 0) + Polynomial.C (F p q) * Polynomial.X := by
    intro p q
    rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.neg_apply, Matrix.one_apply, map_neg, smul_eq_mul]
    ring
  simp only [this]
  have e : ∀ a b c d : R, ((1 + Polynomial.C a * Polynomial.X) * (1 + Polynomial.C d * Polynomial.X) -
      (0 + Polynomial.C b * Polynomial.X) * (0 + Polynomial.C c * Polynomial.X)) =
      1 + Polynomial.C (a + d) * Polynomial.X + Polynomial.C (a * d - b * c) * Polynomial.X ^ 2 := by
    intro a b c d
    simp only [map_add, map_sub, map_mul]; ring
  simp only [if_true, reduceCtorEq, if_false, e]
  simp [Polynomial.coeff_one, Polynomial.coeff_X, -map_add, -map_sub, -map_mul]

theorem aeval_curvPoly {r : Type} [Fintype r] [DecidableEq r] (G : V n → Matrix r r ℂ) (v : V n) (p q : r) :
    MvPolynomial.aeval sym (GlobalTheory.GoodMetric.curvPoly G v p q) = ofValues (fun ξ η => curv G v ξ η p q) := by
  simp [GlobalTheory.GoodMetric.curvPoly, ofValues, Algebra.smul_def]

end GlobalTheory.SecForm.ChernTwo

namespace GlobalTheory.SecForm

open ChernTwo

theorem chernAt_two_eq {n : ℕ} (G : V n → Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ) (v : V n) :
    chernAt G v 2 = ofValuesTwo (chernTwo G v) := by
  have hc : ∀ a b c d, chernTwo G v a b c d = kappa ^ 2 * curvMinor G v (.inl 0) (.inr 0) a b c d := by
    intro a b c d
    simp only [chernTwo, Fintype.sum_sum_type, Finset.univ_unique, Finset.sum_singleton, curvMinor_self,
      Fin.default_eq_zero, curvMinor_comm G v (.inr 0) (.inl 0)]
    ring
  have e : ofValuesTwo (chernTwo G v) = (1 / 4 : ℂ) • four fun a b c d =>
      kappa ^ 2 * curvMinor G v (.inl 0) (.inr 0) (coordVec a) (coordVec b) (coordVec c) (coordVec d) := by
    simp only [ofValuesTwo, four, hc]
  rw [e, four_mul]
  simp only [curvMinor]
  rw [four_sub, four_wedge, four_wedge, chernAt, GlobalTheory.GoodMetric.chernPoly, coeff_two, map_sub, map_mul, map_mul]
  simp only [aeval_curvPoly]
  module

end GlobalTheory.SecForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartSingleton
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ArchDimZero

theorem volume_univ_zero : (volume : Measure (ReciprocityTheory.L2DbarEstimates.V 0)) Set.univ = 1 := by
  have h := (stdOrthonormalBasis ℝ (ReciprocityTheory.L2DbarEstimates.V 0)).volume_parallelepiped
  rwa [Set.eq_univ_of_forall (s := parallelepiped _) fun v =>
    (Subsingleton.elim 0 v) ▸ ⟨0, by simp, by simp⟩] at h

variable {k : Type} [CommRing k] {Y : Scheme.{0}} [IsIntegral Y] {q : Y ⟶ Sp k}

theorem exists_chart (hq : IsArithVar q 0) {σ : k →+* ℂ} (y : CxPts q σ) :
    ∃ c : AlgChart q σ 0, y ∈ c.e.source := by
  obtain ⟨U, x, hU, hg, hx⟩ := GenericEtale.exists_etale_coords hq
  have hy : y ∈ ptsIn q σ U := by
    rw [mem_ptsIn, show y.1 (IsLocalRing.closedPoint ℂ) = genericPoint Y from
      TwistTop.under_eq_genericPoint hq y]
    exact hg
  obtain ⟨c, hc, -⟩ := AlgChart.exists_of_etale hU x hx hy
  exact ⟨c, hc⟩

theorem isProper (hq : IsArithVar q 0) : IsProper q := by
  obtain ⟨N, j, _, hj⟩ := hq.isProjOver
  have := isProper_str k N
  exact hj ▸ inferInstance

theorem chernPart_singleton (hq : IsArithVar q 0) (L : HermLB q) (σ : k →+* ℂ) (ε : ℤˣ)
    (y : CxPts q σ) : (L.φ σ).chernPart 0 ε {y} = ENNReal.ofReal (ε : ℤ) := by
  have := isProper hq
  obtain ⟨c, hc⟩ := exists_chart hq y
  rw [Weight.chernPart_apply (L.cInf σ) ε c (measurableSet_singleton y)
    (Set.singleton_subset_iff.2 hc)]
  have e : c.e '' {y} = Set.univ := Set.eq_univ_of_forall fun v => ⟨y, rfl, Subsingleton.elim _ _⟩
  simp [e, AlgChart.chernDens_zero, volume_univ_zero]

theorem finite_cxPts (hq : IsArithVar q 0) (σ : k →+* ℂ) : Finite (CxPts q σ) := by
  have := HtSelfInter.finite_ringHom hq
  obtain ⟨e⟩ := HtSelfInter.nonempty_equiv hq
  have : Finite (Σ σ : k →+* ℂ, CxPts q σ) := .of_equiv _ e.symm
  exact .of_injective _ (sigma_mk_injective (i := σ))

theorem chernInt_univ (hq : IsArithVar q 0) (L : HermLB q) (σ : k →+* ℂ) (f : CxPts q σ → ℝ) :
    (L.φ σ).chernInt 0 Set.univ f = ∑ᶠ y, f y := by
  have := isProper hq
  have := finite_cxPts hq σ
  let := Fintype.ofFinite (CxPts q σ)
  have h₁ : (L.φ σ).chernPart 0 1 = Measure.count := Measure.ext_iff_singleton.2 fun y => by
    rw [chernPart_singleton hq L σ 1 y, Measure.count_singleton]
    simp
  have h₂ : (L.φ σ).chernPart 0 (-1) = 0 := Measure.ext_iff_singleton.2 fun y => by
    rw [chernPart_singleton hq L σ (-1) y]
    simp
  rw [Weight.chernInt, h₁, h₂, Measure.restrict_univ, Measure.restrict_univ, integral_zero_measure,
    sub_zero, integral_fintype (Integrable.of_finite (μ := Measure.count) (f := f)), finsum_eq_sum_of_fintype]
  simp [Measure.real]

theorem main : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k), IsArithVar q 0 → ∀ (M N : HermLB q) (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r), N.archInt M 0 hr = ∑ᶠ σ : k →+* ℂ, ∑ᶠ y : CxPts q σ, logNorm (M.φ σ) r y := by
  intro k _ Y _ q hq M N r hr
  unfold HermLB.archInt
  refine finsum_congr fun σ => ?_
  have hS : offSupp q σ (M.div hr) = Set.univ := Set.eq_univ_of_forall fun y => mem_offSupp.2 fun h =>
    CartierDiv.genericPoint_notMem_supp _ (TwistTop.under_eq_genericPoint hq y ▸ h)
  rw [hS, chernInt_univ hq]

end GlobalTheory.ArchDimZero
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmpNaturality
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.VB

namespace GlobalTheory.LineQuot

variable {S T Y B : Scheme.{0}}

def cmp (g' : T ⟶ Y) (π : Y ⟶ B) {g : T ⟶ B} (w : g' ≫ π = g) :
    Scheme.Modules.pullback π ⋙ Scheme.Modules.pullback g' ≅ Scheme.Modules.pullback g :=
  Scheme.Modules.pullbackComp g' π ≪≫ Scheme.Modules.pullbackCongr w

theorem cmp_hom_app (g' : T ⟶ Y) (π : Y ⟶ B) {g : T ⟶ B} (w : g' ≫ π = g) (E : B.Modules) :
    (cmp g' π w).hom.app E =
      (Scheme.Modules.pullbackComp g' π).hom.app E ≫ (Scheme.Modules.pullbackCongr w).hom.app E := rfl

@[reassoc] theorem cmp_naturality (g' : T ⟶ Y) (π : Y ⟶ B) {g : T ⟶ B} (w : g' ≫ π = g) {E F : B.Modules} (u : E ⟶ F) :
    (Scheme.Modules.pullback g').map ((Scheme.Modules.pullback π).map u) ≫ (cmp g' π w).hom.app F =
      (cmp g' π w).hom.app E ≫ (Scheme.Modules.pullback g).map u :=
  (cmp g' π w).hom.naturality u

@[reassoc] theorem cmp_assoc (h : S ⟶ T) (g' : T ⟶ Y) (π : Y ⟶ B) {g : T ⟶ B} (w : g' ≫ π = g) {k : S ⟶ B}
    (w₂ : h ≫ g = k) {h' : S ⟶ Y} (w₁ : h ≫ g' = h') (w₃ : h' ≫ π = k) (E : B.Modules) :
    (Scheme.Modules.pullback h).map ((cmp g' π w).hom.app E) ≫ (cmp h g w₂).hom.app E =
      (cmp h g' w₁).hom.app ((Scheme.Modules.pullback π).obj E) ≫ (cmp h' π w₃).hom.app E := by
  subst w w₂ w₁
  have := NatTrans.congr_app (Scheme.Modules.pseudofunctor_associativity h g' π) E
  simp [cmp, Scheme.Modules.pullbackCongr] at this ⊢
  rw [← cancel_epi ((Scheme.Modules.pullbackComp h (g' ≫ π)).inv.app E ≫
      (Scheme.Modules.pullback h).map ((Scheme.Modules.pullbackComp g' π).inv.app E))]
  simp only [Category.assoc, reassoc_of% this, eqToHom_trans, eqToHom_refl]
  simp [← Functor.map_comp_assoc]

def IsLineQuot (π : Y ⟶ B) (E : B.Modules) {Q : Y.Modules} (p : (Scheme.Modules.pullback π).obj E ⟶ Q) : Prop :=
  IsVB Q 1 ∧ Epi p ∧ ∀ (T : Scheme.{0}) (g : T ⟶ B) (Q' : T.Modules) (p' : (Scheme.Modules.pullback g).obj E ⟶ Q'),
    IsVB Q' 1 → Epi p' → ∃! g' : T ⟶ Y, ∃ (w : g' ≫ π = g) (e : (Scheme.Modules.pullback g').obj Q ⟶ Q'),
      (Scheme.Modules.pullback g').map p ≫ e = (cmp g' π w).hom.app E ≫ p'

theorem isLineQuot_id {E : B.Modules} (hE : IsVB E 1) : IsLineQuot (𝟙 B) E (𝟙 _) :=
  ⟨hE.pullback _, inferInstance, fun _ g _ p' _ _ =>
    ⟨g, ⟨Category.comp_id g, (cmp g (𝟙 B) (Category.comp_id g)).hom.app E ≫ p', by simp⟩,
      fun _ ⟨w, _⟩ => (Category.comp_id _).symm.trans w⟩⟩

variable {R : Type} [CommRing R] {N : ℕ} {L Q : T.Modules}

def Rel (φ : T ⟶ PSpace R N) (s : Fin (N + 1) → (L ⟶ Q)) : Prop :=
  ∀ (i j : Fin (N + 1)) (W : T.Opens) (h : W ≤ φ ⁻¹ᵁ ProjSpace.chart R N i) (t : Γ(L, W)),
    (s j).app W t = ProjSpace.pullRatio φ W i h j • (s i).app W t

def Gen {ι : Type} (s : ι → (L ⟶ Q)) : Prop :=
  ∀ x : T, ∃ (j : ι) (W : T.Opens), x ∈ W ∧ ∀ V : T.Opens, V ≤ W → Function.Bijective ((s j).app V)

def JointEpi {ι : Type} (s : ι → (L ⟶ Q)) : Prop :=
  ∀ (Z : T.Modules) (a : Q ⟶ Z), (∀ j, s j ≫ a = 0) → a = 0

end GlobalTheory.LineQuot

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocompactStandardParabolicUnipotentRadicalWittFrStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cocompact_standardParabolicUnipotentRadical_wittFrame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
      ∀ S : Finset (Fin r), GlobalTheory.Cusp.Cocompact (ratPts σ J) (GlobalTheory.StdPar.unip σ J X S) := by
  first | exact @GlobalTheory.CuspCocpt.cocompact_unip | exact GlobalTheory.CuspCocpt.cocompact_unip | (intros; apply GlobalTheory.CuspCocpt.cocompact_unip <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeDegreeGrowthChowFormIntegralityStatement
section
open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Indef.Tree
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cone_degree_growth_chowForm_integrality : (∀ (K V Ω : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Field Ω] [Algebra K Ω] (ev : V →ₗ[K] Ω) (D a : ℕ), 1 ≤ a → ∀ δ : ℕ, IsImageDeg ev D δ → growth D (fun k => hilb ev (a * k)) = (a : ℝ≥0∞) ^ D * δ) ∧ (∀ (K V Ω : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Field Ω] [Algebra K Ω] (ev : V →ₗ[K] Ω) (D a : ℕ), 1 ≤ a → growth D (fun k => hilb ev (a * k)) ≠ 0 → growth D (fun k => hilb ev (a * k)) ≠ ⊤ → ∃ δ : ℕ, IsImageDeg ev D δ) ∧ (∀ (K V Ω : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Field Ω] [Algebra K Ω] (ev : V →ₗ[K] Ω) (D a : ℕ), 1 ≤ a → ∀ S : ℕ → Submodule K Ω, (∀ k, ∀ t ∈ S k, IsIntDeg ev (a * k) t ∧ IsRatio ev (a * k) t) → growth D (fun k => Cardinal.toENat (Module.rank K (S k))) ≤ growth D (fun k => hilb ev (a * k))) ∧ (∀ (K A : Type) [Field K] [CommRing A] [IsDomain A] [Algebra K A] [Algebra.FiniteType K A] (σ : K →+* ℂ) (n k : ℕ) (w : Fin n → A) (s : A) (C : ℝ), (∀ φ : A →+* ℂ, φ.comp (algebraMap K A) = σ → ‖φ s‖ ≤ C * (1 + ∑ i, ‖φ (w i)‖) ^ k) → IsIntegral (Algebra.adjoin K (Set.range w)) s) := by
  first | exact @GlobalTheory.ConeDeg.degree_growth_integral | exact GlobalTheory.ConeDeg.degree_growth_integral | (intros; apply GlobalTheory.ConeDeg.degree_growth_integral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffDerivHeisenbergCMRealLineThetaStatement
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contDiff_deriv_heisenbergCM_real_line_theta : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ f : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ, Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f → ∀ L : ℝ →+ Formalism.IndefR.DatumF.WOF F E nS nT, Continuous L → (∀ t, (L t).map (Formalism.IndefR.DatumF.finPartF F E) = 0) →
      ∀ (k : ℕ) (L' : (Fin k → ℝ) →+ Formalism.IndefR.DatumF.WOF F E nS nT), Continuous L' → (∀ t, (L' t).map (Formalism.IndefR.DatumF.finPartF F E) = 0) →
      ∀ w : Formalism.IndefR.DatumF.WOF F E nS nT, ContDiff ℝ ∞ fun x => deriv (fun t : ℝ => Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (L t) f (w + L' x)) 0 := by
  first | exact @GlobalTheory.ThetaLineSmoothF.contDiff_deriv_heisOF_line | exact GlobalTheory.ThetaLineSmoothF.contDiff_deriv_heisOF_line | (intros; apply GlobalTheory.ThetaLineSmoothF.contDiff_deriv_heisOF_line <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnChernFormOfGramMatrixAtCoefficientsStatement
section
open Set Matrix Filter Topology
open GlobalTheory.HermFrame GlobalTheory.CxForm
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec chernPoly curvPoly)
open scoped ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contDiffOn_chernFormOfGramMatrixAt_coefficients : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (H : V n → Matrix r r ℂ) (s : Set (V n)), IsOpen s → (∀ a b, ContDiffOn ℝ ∞ (fun v => H v a b) s) → (∀ v ∈ s, IsUnit (H v).det) → ∀ (j : ℕ) (S : Finset (Fin (n + n))), ContDiffOn ℝ ∞ (fun v => (bas n).repr (chernAt H v j : Alt n) S) s := by
  first | exact @GlobalTheory.ChernSmooth.contDiffOn_chernAt | exact GlobalTheory.ChernSmooth.contDiffOn_chernAt | (intros; apply GlobalTheory.ChernSmooth.contDiffOn_chernAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnDbarCoefficientsStatement
section
open Set Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)
open GlobalTheory.CxForm
open scoped ComplexConjugate ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contDiffOn_dbar_coefficients : ∀ {n : ℕ} {γ : V n → Alt n} {U : Set (V n)}, IsOpen U → (∀ S, ContDiffOn ℝ ∞ (fun v => (bas n).repr (γ v) S) U) → ∀ (T : Finset (Fin (n + n))), ContDiffOn ℝ ∞ (fun v => (bas n).repr (dbarAt γ v) T) U := by
  first | exact @GlobalTheory.CxForm.contDiffOn_repr_dbarAt | exact GlobalTheory.CxForm.contDiffOn_repr_dbarAt | (intros; apply GlobalTheory.CxForm.contDiffOn_repr_dbarAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnExtTrace
section
set_option autoImplicit false

noncomputable section

open Set Matrix Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.HermFrame GlobalTheory.CxForm GlobalTheory.SecForm
open GlobalTheory.GoodMetric (coordVec)
open scoped ContDiff ComplexOrder

namespace GlobalTheory.SecForm

theorem contDiffOn_extTrace : ∀ {n : ℕ} {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]
    {U : Set (V n)} {H : V n → Matrix (m ⊕ l) (m ⊕ l) ℂ}, IsPosFrame U H →
    ∀ ξ η : V n, ContDiffOn ℝ ∞ (fun v => extTrace H v ξ η) U := by
  intro n m l _ _ _ _ U H hH ξ η
  have hM : ∀ v ∈ U, MContDiffAt ∞ H v := fun v hv a b =>
    (hH.smooth a b).contDiffAt (hH.isOpen.mem_nhds hv)
  have hP : ∀ v ∈ U, ∀ᶠ x in 𝓝 v, (H x).PosDef := fun v hv =>
    Filter.eventually_of_mem (hH.isOpen.mem_nhds hv) hH.posDef
  have key : ∀ v ∈ U,
      ContDiffAt ℝ ∞ (fun x => kappa * (secondForm H x ξ * secondFormAdj H x η).trace) v := by
    intro v hv
    have hu : IsUnit (H v).det := (hH.posDef v hv).det_pos.ne'.isUnit
    have hs : IsUnit (subGram (H v)).det := (posDef_subGram (hH.posDef v hv)).det_pos.ne'.isUnit
    have hc : ∀ ζ, MContDiffAt ∞ (fun x => secondForm H x ζ) v := fun ζ => by
      show MContDiffAt ∞ (fun x => quotMap m l * conn H x ζ * incl m l) v
      exact ((mContDiffAt_const _).mul ((hM v hv).conn hu (j := ∞) (by simp) ζ)).mul
        (mContDiffAt_const _)
    have ha : MContDiffAt ∞ (fun x => secondFormAdj H x η) v := by
      show MContDiffAt ∞ (fun x => (subGram (H x))ᵀ⁻¹ * (secondForm H x η)ᴴ * (quotGram (H x))ᵀ) v
      exact (((hM v hv).subGram.transpose.inv (by rwa [det_transpose])).mul
        (hc η).conjTranspose).mul ((hM v hv).quotGram hs).transpose
    have hp := (hc ξ).mul ha
    simp only [Matrix.trace, Matrix.diag_apply]
    exact contDiffAt_const.mul (ContDiffAt.sum fun i _ => hp i i)
  intro v hv
  refine ((key v hv).congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [hH.isOpen.mem_nhds hv] with x hx
  exact extTrace_eq ((hM x hx).of_le (by simp)) (hP x hx) ξ η

end GlobalTheory.SecForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousMultilinearMapNormLeSumBasisValuesStatement
section
open IsDedekindDomain NumberField
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuousMultilinearMap_norm_le_sum_basis_values : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (ι : Type) [Fintype ι] (b : Module.Basis ι ℝ E) (j : ℕ),
    ∃ K : ℝ, 0 ≤ K ∧ ∀ M : ContinuousMultilinearMap ℝ (fun _ : Fin j => E) ℂ,
      ‖M‖ ≤ K * ∑ cs : Fin j → ι, ‖M (fun r => b (cs r))‖ := by
  first | exact @GlobalTheory.continuousMultilinear_norm_le_basis_sum | exact GlobalTheory.continuousMultilinear_norm_le_basis_sum | (intros; apply GlobalTheory.continuousMultilinear_norm_le_basis_sum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOfLieIntertwineL2Statement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_of_lie_intertwine_l2 : ∀ (l : Type) [Fintype l] (L' : (l ⊕ l → ℝ) ≃ₗ[ℝ] (l ⊕ l → ℝ))
    (A' : GlobalTheory.RealWeil.Sch l →ₗ[ℂ] GlobalTheory.RealWeil.Sch l) (C : ℝ≥0∞), C ≠ ⊤ →
    (∀ f, ∫⁻ x, ‖A' f x‖ₑ ^ 2 ≤ C * ∫⁻ x, ‖f x‖ₑ ^ 2) →
    (∀ w f, A' (GlobalTheory.RealWeil.dRho w f) = GlobalTheory.RealWeil.dRho (L' w) (A' f)) →
    Continuous A' := by
  first | exact @GlobalTheory.RealWeil.continuous_of_dRho_intertwine_of_L2_bound | exact GlobalTheory.RealWeil.continuous_of_dRho_intertwine_of_L2_bound | (intros; apply GlobalTheory.RealWeil.continuous_of_dRho_intertwine_of_L2_bound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousThetaTransformAdelicSchwartzStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_thetaTransform_adelicSchwartz : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
      (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
      ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
      ∀ (κ : Type) [Fintype κ]
        (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
        (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
          co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
        ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, Continuous (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ) := by
  first | exact @GlobalTheory.ThetaTrCont.continuous_thetaTr | exact GlobalTheory.ThetaTrCont.continuous_thetaTr | (intros; apply GlobalTheory.ThetaTrCont.continuous_thetaTr <;> assumption)
end

