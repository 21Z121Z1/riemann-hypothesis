import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1416
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0771
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1444
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1456
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1460
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1524
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1483
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0019
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1516
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1475
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1527
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1513
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1507
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1533
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1526
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteDimensionalSpaceAutomorphicSmoothing
section
noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology

namespace GlobalTheory.AutGrowth.SmoothFinite

section

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def stabL (φ : Sm E a) : Subgroup (GL (Fin a) (Af E)) where
  carrier := {k | finRep E a k φ = φ}
  mul_mem' {x y} hx hy := by
    simp only [Set.mem_ofPred_eq, map_mul, Module.End.mul_apply] at *
    rw [hy, hx]
  one_mem' := by simp
  inv_mem' {x} hx := by
    simp only [Set.mem_ofPred_eq] at *
    conv_lhs => rw [← hx]
    rw [← Module.End.mul_apply, ← map_mul]
    simp

theorem height_mul_le (c : GL (Fin a) (Cinf E)) : ∃ B : ℝ, 1 ≤ B ∧ ∀ y, height (y * c) ≤ B * height y := by
  refine ⟨1 + ‖rmul (toL c.val)‖ + ‖lmul (toL (c⁻¹).val)‖,
    by linarith [norm_nonneg (rmul (toL c.val)), norm_nonneg (lmul (toL (c⁻¹).val))], fun y => ?_⟩
  have h1 : toL (y * c).val = rmul (toL c.val) (toL y.val) := rfl
  have h2 : toL ((y * c)⁻¹).val = lmul (toL (c⁻¹).val) (toL (y⁻¹).val) := by
    rw [_root_.mul_inv_rev]; rfl
  have e1 := (rmul (toL c.val)).le_opNorm (toL y.val)
  have e2 := (lmul (toL (c⁻¹).val)).le_opNorm (toL (y⁻¹).val)
  have n1 := norm_nonneg (toL y.val)
  have n2 := norm_nonneg (toL (y⁻¹).val)
  have n3 := norm_nonneg (rmul (toL c.val))
  have n4 := norm_nonneg (lmul (toL (c⁻¹).val))
  unfold height
  rw [h1, h2]
  nlinarith

theorem growth_cptRep {φ : Sm E a} (hφ : φ.1 ∈ growth E a) (k : Kinf E a) : (cptRep E a k φ).1 ∈ growth E a := by
  intro g
  obtain ⟨C, N, hC⟩ := hφ g
  obtain ⟨B, hB, hB'⟩ := height_mul_le (Unitary.toUnits k : GL (Fin a) (Cinf E))
  have C0 : 0 ≤ C := by
    have := (norm_nonneg _).trans (hC 1)
    have hp : 0 < height (1 : GL (Fin a) (Cinf E)) ^ N :=
      pow_pos (by linarith [one_le_height (1 : GL (Fin a) (Cinf E))]) N
    exact nonneg_of_mul_nonneg_left this hp
  refine ⟨C * B ^ N, N, fun y => ?_⟩
  change ‖φ.1 (g * infGL E a y * infGL E a (Unitary.toUnits k))‖ ≤ _
  rw [mul_assoc, ← map_mul]
  refine (hC _).trans ?_
  rw [mul_assoc, ← mul_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith [one_le_height (y * Unitary.toUnits k)]) (hB' y) N) C0

theorem spanK_induction {φ : Sm E a} {p : Sm E a → Prop} (h0 : p 0) (hadd : ∀ x y, p x → p y → p (x + y))
    (hsmul : ∀ (c : ℂ) x, p x → p (c • x)) (hk : ∀ k, p (cptRep E a k φ)) {w : Sm E a}
    (hw : w ∈ spanK E a φ) : p w := by
  induction hw using Submodule.span_induction with
  | mem x hx => obtain ⟨k, rfl⟩ := hx; exact hk k
  | zero => exact h0
  | add x y _ _ hx hy => exact hadd x y hx hy
  | smul c x _ hx => exact hsmul c x hx

theorem fin_cpt_comm (k : GL (Fin a) (Af E)) (c : Kinf E a) :
    finRep E a k * cptRep E a c = cptRep E a c * finRep E a k := by
  change rt E a (finGL E a k) * rt E a (infGL E a (Unitary.toUnits c)) =
    rt E a (infGL E a (Unitary.toUnits c)) * rt E a (finGL E a k)
  rw [← map_mul, ← map_mul, infGL_comm]

variable {φ : Sm E a}

theorem growth_mem (hφ : IsAutForm φ) {w : Sm E a} (hw : w ∈ spanK E a φ) : w.1 ∈ growth E a :=
  spanK_induction (p := fun w : Sm E a => w.1 ∈ growth E a) (zero_mem _)
    (fun x y hx hy => by rw [Submodule.coe_add]; exact add_mem hx hy)
    (fun c x hx => by rw [Submodule.coe_smul]; exact Submodule.smul_mem _ c hx)
    (fun k => growth_cptRep (φ := φ) hφ.growth k) hw

theorem left_mem (hφ : IsAutForm φ) {w : Sm E a} (hw : w ∈ spanK E a φ) :
    ∀ γ g, w.1 (ratGL E a γ * g) = w.1 g :=
  spanK_induction (p := fun w : Sm E a => ∀ γ g, w.1 (ratGL E a γ * g) = w.1 g) (fun _ _ => rfl)
    (fun x y hx hy γ g => by simp [hx γ g, hy γ g])
    (fun c x hx γ g => by simp [hx γ g])
    (fun k γ g => by
      change φ.1 (ratGL E a γ * g * infGL E a (Unitary.toUnits k)) = φ.1 (g * infGL E a (Unitary.toUnits k))
      rw [mul_assoc, hφ.left]) hw

theorem fixed_mem {k : GL (Fin a) (Af E)} (hk : k ∈ stabL φ) {w : Sm E a} (hw : w ∈ spanK E a φ) :
    finRep E a k w = w :=
  spanK_induction (p := fun w : Sm E a => finRep E a k w = w) (map_zero _)
    (fun x y hx hy => by rw [map_add, hx, hy])
    (fun c x hx => by rw [map_smul, hx])
    (fun c => by
      have hk' : finRep E a k φ = φ := hk
      rw [← Module.End.mul_apply, fin_cpt_comm, Module.End.mul_apply, hk']) hw

theorem killed_mem {z : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a) (h0 : z φ = 0) {w : Sm E a}
    (hw : w ∈ spanK E a φ) : z w = 0 :=
  spanK_induction (p := fun w : Sm E a => z w = 0) (map_zero _)
    (fun x y hx hy => by rw [map_add, hx, hy, add_zero])
    (fun c x hx => by rw [map_smul, hx, smul_zero])
    (fun c => by
      rw [← Module.End.mul_apply, GlobalTheory.ZalgCpt.zalg_comm_cptRep E a c z hz, Module.End.mul_apply, h0, map_zero]) hw

variable (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] {α : Lie E a → ℂ}

theorem smoothing_add (hα : IsTest (invSet E a) α) (φ ψ : Sm E a) :
    smoothing ν α (φ + ψ).1 = smoothing ν α φ.1 + smoothing ν α ψ.1 := by
  funext x
  simp only [Pi.add_apply, smoothing]
  refine (integral_congr_ae (.of_forall fun y => ?_)).trans
    (integral_add (hα.integrable_mul ν isOpen_invSet (φ.2 x).continuousOn)
      (hα.integrable_mul ν isOpen_invSet (ψ.2 x).continuousOn))
  by_cases h : IsUnit (Matrix.of y) <;> simp [chart, h, mul_add]

theorem smoothing_smul (c : ℂ) (φ : Sm E a) :
    smoothing ν α (c • φ).1 = c • smoothing ν α φ.1 := by
  funext x
  simp only [Pi.smul_apply, smul_eq_mul, smoothing]
  refine (integral_congr_ae (.of_forall fun y => ?_)).trans (integral_const_mul c _)
  by_cases h : IsUnit (Matrix.of y) <;> simp [chart, h, mul_left_comm]

def smoothMap (hα : IsTest (invSet E a) α) (W : Submodule ℂ (Sm E a)) : W →ₗ[ℂ] Sm E a where
  toFun w := ⟨smoothing ν α w.1.1, GlobalTheory.T.realLieSmoothing_mem_smoothAdelicFunctions E a ν α hα w.1.1 w.1.2⟩
  map_add' w w' := Subtype.ext (smoothing_add ν hα w.1 w'.1)
  map_smul' c w := Subtype.ext (smoothing_smul ν c w.1)

theorem smoothMap_mem (hα : IsTest (invSet E a) α) (hK : KInv α) (hφ : IsAutForm φ) :
    smoothMap ν hα (spanK E a φ) ∈ mapsJ φ (stabL φ) := by
  refine ⟨⟨fun k w => ?_, fun w => ⟨?_, fun γ g => ?_, fun k hk => ?_⟩⟩, fun z hz h0 w => ?_⟩
  · apply Subtype.ext; funext g
    exact GlobalTheory.T.smoothing_right_translate_maxCompact E a ν α hK w.1.1 k g
  · intro l
    obtain ⟨β, hβ, e⟩ : ∃ β, IsTest (invSet E a) β ∧
        ((l.map (lie E a)).prod (smoothMap ν hα (spanK E a φ) w)).1 = smoothing ν β w.1.1 := by
      induction l with
      | nil => exact ⟨α, hα, rfl⟩
      | cons X l ih =>
        obtain ⟨β, hβ, e⟩ := ih
        refine ⟨dens X β, isTest_dens X hβ, funext fun g => ?_⟩
        rw [List.map_cons, List.prod_cons, Module.End.mul_apply, lie_apply, e]
        exact GlobalTheory.T.lieDerivative_realLieSmoothing_eq_density E a ν β hβ w.1.1 w.1.2 X g
    rw [e]
    exact GlobalTheory.T.realLieSmoothing_mem_slowlyIncreasing E a ν β hβ w.1.1 (growth_mem hφ w.2)
  · show smoothing ν α w.1.1 (ratGL E a γ * g) = smoothing ν α w.1.1 g
    have hl := left_mem hφ w.2
    simp only [smoothing, chart, mul_assoc, hl]
  · apply Subtype.ext; funext g
    show smoothing ν α w.1.1 (g * finGL E a k) = smoothing ν α w.1.1 g
    have hw : (fun x => w.1.1 (x * finGL E a k)) = w.1.1 := congrArg Subtype.val (fixed_mem hk w.2)
    simp only [smoothing]
    rw [← chart_rt_fin, hw]
  · show (z ⟨smoothing ν α w.1.1, GlobalTheory.T.realLieSmoothing_mem_smoothAdelicFunctions E a ν α hα w.1.1 w.1.2⟩) = 0
    apply Subtype.ext
    rw [GlobalTheory.T.centreEnvelopingAlgebra_commute_realLieSmoothing E a ν α hα w.1 _ z hz, killed_mem hz h0 w.2]
    funext g
    simp [smoothing, chart]

end

theorem exists_finite_space : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E]
    [IsTotallyComplex E] (a : ℕ) (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] (φ : Sm E a), IsAutForm φ →
    ∃ V : Submodule ℂ (Sm E a), FiniteDimensional ℂ V ∧ V ≤ tame E a ∧ ∀ α, IsTest (invSet E a) α → KInv α →
      ∃ h : smoothing ν α φ.1 ∈ Sm E a, (⟨smoothing ν α φ.1, h⟩ : Sm E a) ∈ V := by
  intro hP E _ _ _ a ν _ φ hφ
  let w0 : spanK E a φ := ⟨φ, self_mem_spanK φ⟩
  haveI := GlobalTheory.T.finiteDimensional_centreAnnihilatorCompatibleMaps hP E a φ hφ (stabL φ) hφ.level
  refine ⟨(mapsJ φ (stabL φ)).map (LinearMap.applyₗ w0), inferInstance, ?_, fun α hα hK =>
    ⟨GlobalTheory.T.realLieSmoothing_mem_smoothAdelicFunctions E a ν α hα φ.1 φ.2, smoothMap ν hα _, smoothMap_mem ν hα hK hφ, rfl⟩⟩
  rintro _ ⟨T, hT, rfl⟩
  exact (hT.1.2 w0).1

end GlobalTheory.AutGrowth.SmoothFinite
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFixedComplexPointOfFixedFieldPoint
section
open CategoryTheory NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical
open AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.FixedCx

open Cardinal

theorem mk_le_of_essFiniteType {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [Algebra.EssFiniteType R S] :
    #S ≤ max #R ℵ₀ := by
  have h1 : #S ≤ #(Algebra.EssFiniteType.subalgebra R S) :=
    IsLocalization.cardinalMk_le (Algebra.EssFiniteType.submonoid R S)
  have h2 := Algebra.cardinalMk_adjoin_le R ((Algebra.EssFiniteType.finset R S : Finset S) : Set S)
  have h3 : #(((Algebra.EssFiniteType.finset R S : Finset S) : Set S)) ≤ ℵ₀ :=
    (Cardinal.lt_aleph0_of_finite _).le
  refine h1.trans (h2.trans ?_)
  exact max_le (max_le (le_max_left _ _) (h3.trans (le_max_right _ _))) (le_max_right _ _)

theorem nonempty_ringHom_complex (K : Type) [Field K] [CharZero K] (h : #K ≤ 𝔠) : Nonempty (K →+* ℂ) := by
  have hP1 : #(MvPolynomial ℝ K) ≤ 𝔠 := MvPolynomial.cardinalMk_le_max.trans
    (max_le (max_le h (Cardinal.mk_real).le) Cardinal.aleph0_le_continuum)
  have hP2 : 𝔠 ≤ #(MvPolynomial ℝ K) := by
    rw [← Cardinal.mk_real]
    exact Cardinal.mk_le_of_injective (MvPolynomial.X_injective (σ := ℝ) (R := K))
  have hF : #(FractionRing (MvPolynomial ℝ K)) = 𝔠 := (FractionRing.cardinalMk (MvPolynomial ℝ K)).trans (le_antisymm hP1 hP2)
  haveI : CharZero (FractionRing (MvPolynomial ℝ K)) :=
    charZero_of_injective_ringHom (f := (algebraMap (MvPolynomial ℝ K) (FractionRing (MvPolynomial ℝ K))).comp MvPolynomial.C)
      ((IsFractionRing.injective (MvPolynomial ℝ K) (FractionRing (MvPolynomial ℝ K))).comp (MvPolynomial.C_injective ℝ K))
  haveI : CharZero (AlgebraicClosure (FractionRing (MvPolynomial ℝ K))) := charZero_of_injective_ringHom (algebraMap (FractionRing (MvPolynomial ℝ K)) (AlgebraicClosure (FractionRing (MvPolynomial ℝ K)))).injective
  have hΩ1 : #(AlgebraicClosure (FractionRing (MvPolynomial ℝ K))) ≤ 𝔠 := (Algebra.IsAlgebraic.cardinalMk_le_max (FractionRing (MvPolynomial ℝ K)) (AlgebraicClosure (FractionRing (MvPolynomial ℝ K)))).trans
    (max_le hF.le Cardinal.aleph0_le_continuum)
  have hΩ2 : 𝔠 ≤ #(AlgebraicClosure (FractionRing (MvPolynomial ℝ K))) := hF ▸ Cardinal.mk_le_of_injective (algebraMap (FractionRing (MvPolynomial ℝ K)) (AlgebraicClosure (FractionRing (MvPolynomial ℝ K)))).injective
  have hΩ : #(AlgebraicClosure (FractionRing (MvPolynomial ℝ K))) = #ℂ := (le_antisymm hΩ1 hΩ2).trans Cardinal.mk_complex.symm
  obtain ⟨e⟩ := IsAlgClosed.ringEquiv_of_equiv_of_charZero (K := AlgebraicClosure (FractionRing (MvPolynomial ℝ K))) (L := ℂ)
    (by rw [hΩ, Cardinal.mk_complex]; exact Cardinal.aleph0_lt_continuum) (Cardinal.eq.1 hΩ)
  exact ⟨e.toRingHom.comp ((algebraMap (FractionRing (MvPolynomial ℝ K)) (AlgebraicClosure (FractionRing (MvPolynomial ℝ K)))).comp ((algebraMap (MvPolynomial ℝ K) (FractionRing (MvPolynomial ℝ K))).comp MvPolynomial.C))⟩

theorem cancel_spec_field {K L : Type} [Field K] [Field L] (φ : L →+* K) {X : Scheme.{0}} (a b : Sp L ⟶ X)
    (h : spMap φ ≫ a = spMap φ ≫ b) : a = b := by
  obtain ⟨⟨p, α⟩, rfl⟩ := (Scheme.SpecToEquivOfField L X).symm.surjective a
  obtain ⟨⟨q, β⟩, rfl⟩ := (Scheme.SpecToEquivOfField L X).symm.surjective b
  simp only [Scheme.SpecToEquivOfField_symm_apply] at h ⊢
  rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp] at h
  obtain ⟨e, he⟩ := GlobalTheory.SS.residue_embedding_unique _ _ h
  subst e
  simp only [Scheme.residueFieldCongr_refl, Iso.refl_hom, Category.id_comp] at he
  have : α = β := by
    ext c
    exact φ.injective (congrArg (fun g => g.hom c) he)
  rw [this]

end GlobalTheory.FixedCx

open GlobalTheory.FixedCx Cardinal in

theorem GlobalTheory.FixedCx.exists_fixed_complex_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (k : Type) [Field k] (x : Sp k ⟶ Xo.X) (ρ : Xo.X ⟶ Xo.X), x ≫ ρ = x → ∃ x' : Sp ℂ ⟶ Xo.X, x' ≫ ρ = x' := by
  intro E _ _ _ H Dw l Xo k _ x ρ hx
  obtain ⟨⟨p, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField k Xo.X).symm.surjective x
  simp only [Scheme.SpecToEquivOfField_symm_apply] at hx
  have hι : Xo.X.fromSpecResidueField p ≫ ρ = Xo.X.fromSpecResidueField p :=
    cancel_spec_field φ.hom _ _ (by rw [Category.assoc] at hx; exact hx)
  haveI := Xo.smooth
  haveI := SmoothOfRelativeDimension.smooth Dw.dim Xo.s
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (Xo.X.fromSpecResidueField p ≫ Xo.s)
  have hess := GlobalTheory.SS.essFiniteType_residueField_of_locallyOfFiniteType Xo.s p ψ hψ
  letI : Algebra (KA l) (Xo.X.residueField p) := ψ.hom.toAlgebra
  haveI : Algebra.EssFiniteType (KA l) (Xo.X.residueField p) := hess
  haveI : CharZero (KA l) := charZero_of_injective_ringHom (algebraMap ℚ (KA l)).injective
  haveI : CharZero (Xo.X.residueField p) := charZero_of_injective_ringHom ψ.hom.injective
  have hK : #(KA l) ≤ 𝔠 := (Cardinal.mk_subtype_le _).trans Cardinal.mk_complex.le
  have hc : #(Xo.X.residueField p) ≤ 𝔠 :=
    mk_le_of_essFiniteType.trans (max_le hK Cardinal.aleph0_le_continuum)
  obtain ⟨j⟩ := nonempty_ringHom_complex (Xo.X.residueField p) hc
  exact ⟨Spec.map (CommRingCat.ofHom j) ≫ Xo.X.fromSpecResidueField p, by rw [Category.assoc, hι]⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsDualRiemannOf
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame
open GlobalTheory.Twist (resM)
open GlobalTheory.LieVB (omega unitSec dUnit)
open scoped ComplexOrder

namespace GlobalTheory.DualRiemannEx

theorem form_dualGram_smul {n : Type} [Fintype n] [DecidableEq n] {H : Matrix n n ℂ} (hH : H.PosDef)
    {t : ℝ} (ht : 0 < t) (u v : n → ℂ) :
    form (dualGram ((t : ℂ) • H)) u v = (t : ℂ)⁻¹ * form (dualGram H) u v := by
  have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have e : ((t : ℂ) • H)⁻¹ = (t : ℂ)⁻¹ • H⁻¹ :=
    inv_eq_right_inv (by
      rw [smul_mul_smul_comm, mul_inv_cancel₀ ht', mul_nonsing_inv _ hH.det_pos.ne'.isUnit, one_smul])
  rw [dualGram, dualGram, e, transpose_smul, form_smul]

theorem form_dualGram_conj {n : Type} [Fintype n] [DecidableEq n] (H : Matrix n n ℂ) (t : ℝ)
    (u v : n → ℂ) :
    form (dualGram ((t : ℂ) • H.map star)) (star u) (star v) =
      star (form (dualGram ((t : ℂ) • H)) u v) := by
  have e : (t : ℂ) • H.map star = ((t : ℂ) • H).map star := by
    ext a b
    simp
  rw [e, dualGram_map_star]
  simp [form_eq_sum]

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}

theorem top_le_of_mem {U : X.Opens} {y : CxPts p σ} (h : y ∈ ptsIn p σ U) : ⊤ ≤ y.1 ⁻¹ᵁ U := by
  intro z _
  rw [mem_ptsIn] at h
  rwa [Subsingleton.elim z (IsLocalRing.closedPoint ℂ)]

theorem exists_isUnit
    (hc₁ : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (P : PPAS X) (y : CxPts p σ) (d : P.RiemannData y.1) (c : Chart (LieVB.omega P.A) P.g), y ∈ ptsIn p σ c.U → ∃ C : Matrix (Fin P.g) (Fin P.g) ℂ, ∀ (U : X.Opens) (W : P.A.left.Opens) (hU : U ≤ LieVB.unitSec P.A ⁻¹ᵁ W) (f : Γ(P.A.left, W)), y ∈ ptsIn p σ U → d.cov W f = C.mulVec (c.crd p σ (LieVB.dUnit P.A hU f) y))
    (hc₂ : ∀ (S : Scheme.{0}) (P : PPAS S) (y : Sp ℂ ⟶ S) (d : P.RiemannData y), (∀ v : epsR ℂ ⟶ d.B, IsTangent v → ∃! w, d.u.IsDiff w v) ∧ (∀ w, ∃! v : epsR ℂ ⟶ d.B, IsTangent v ∧ d.u.IsDiff w v))
    (hc₃ : ∀ (S : Scheme.{0}) (P : PPAS S) (y : Sp ℂ ⟶ S) (d : P.RiemannData y), ((∀ v : epsR ℂ ⟶ d.B, IsTangent v → ∃! w, d.u.IsDiff w v) ∧ (∀ w, ∃! v : epsR ℂ ⟶ d.B, IsTangent v ∧ d.u.IsDiff w v)) → ∀ w : Fin P.g → ℂ, (∀ (W : P.A.left.Opens) (f : Γ(P.A.left, W)), ⊤ ≤ (y ≫ LieVB.unitSec P.A) ⁻¹ᵁ W → d.cov W f ⬝ᵥ w = 0) → w = 0)
    (P : PPAS X) (y : CxPts p σ) (d : P.RiemannData y.1)
    (c : Chart (omega P.A) P.g) (hc : y ∈ ptsIn p σ c.U) :
    ∃ C : Matrix (Fin P.g) (Fin P.g) ℂ, IsUnit C ∧ ∀ (U : X.Opens) (W : P.A.left.Opens)
      (hU : U ≤ unitSec P.A ⁻¹ᵁ W) (f : Γ(P.A.left, W)), y ∈ ptsIn p σ U →
        d.cov W f = C *ᵥ c.crd p σ (dUnit P.A hU f) y := by
  obtain ⟨C, hC⟩ := hc₁ k X p σ P y d c hc
  refine ⟨C, ?_, hC⟩
  rw [← vecMul_injective_iff_isUnit]
  intro u v e
  have e₀ : (u - v) ᵥ* C = 0 := by rw [sub_vecMul]; exact sub_eq_zero.2 e
  refine sub_eq_zero.1 (hc₃ X P y.1 d (hc₂ X P y.1 d) _ fun W f hW => ?_)
  have hy : y ∈ ptsIn p σ (unitSec P.A ⁻¹ᵁ W) := mem_ptsIn.2 (hW (show _ ∈ ⊤ from trivial))
  rw [hC _ W le_rfl f hy, dotProduct_comm, dotProduct_mulVec, e₀, zero_dotProduct]

end GlobalTheory.DualRiemannEx

namespace GlobalTheory
open GlobalTheory.DualRiemannEx

theorem PPAS.exists_isDualRiemann_of
    (hc₁ : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (P : PPAS X) (y : CxPts p σ) (d : P.RiemannData y.1) (c : Chart (LieVB.omega P.A) P.g), y ∈ ptsIn p σ c.U → ∃ C : Matrix (Fin P.g) (Fin P.g) ℂ, ∀ (U : X.Opens) (W : P.A.left.Opens) (hU : U ≤ LieVB.unitSec P.A ⁻¹ᵁ W) (f : Γ(P.A.left, W)), y ∈ ptsIn p σ U → d.cov W f = C.mulVec (c.crd p σ (LieVB.dUnit P.A hU f) y))
    (hc₂ : ∀ (S : Scheme.{0}) (P : PPAS S) (y : Sp ℂ ⟶ S) (d : P.RiemannData y), (∀ v : epsR ℂ ⟶ d.B, IsTangent v → ∃! w, d.u.IsDiff w v) ∧ (∀ w, ∃! v : epsR ℂ ⟶ d.B, IsTangent v ∧ d.u.IsDiff w v))
    (hc₃ : ∀ (S : Scheme.{0}) (P : PPAS S) (y : Sp ℂ ⟶ S) (d : P.RiemannData y), ((∀ v : epsR ℂ ⟶ d.B, IsTangent v → ∃! w, d.u.IsDiff w v) ∧ (∀ w, ∃! v : epsR ℂ ⟶ d.B, IsTangent v ∧ d.u.IsDiff w v)) → ∀ w : Fin P.g → ℂ, (∀ (W : P.A.left.Opens) (f : Γ(P.A.left, W)), ⊤ ≤ (y ≫ LieVB.unitSec P.A) ⁻¹ᵁ W → d.cov W f ⬝ᵥ w = 0) → w = 0)
    (hc₄ : ∀ (S : Scheme.{0}) (P : PPAS S) (y : Sp ℂ ⟶ S) (d : P.RiemannData y), ∃ d' : P.RiemannData (spMap (starRingEnd ℂ) ≫ y), d'.H = d.H.map star ∧ ∀ (W : P.A.left.Opens) (f : Γ(P.A.left, W)), ⊤ ≤ (y ≫ LieVB.unitSec P.A) ⁻¹ᵁ W → d'.cov W f = star (d.cov W f))
    (hex₀ : ∀ (S : Scheme.{0}) (P : PPAS S) (y : Sp ℂ ⟶ S), Nonempty (P.RiemannData y))
    (hind : ∀ (S : Scheme.{0}) (P : PPAS S) (y : Sp ℂ ⟶ S) (d d' : P.RiemannData y)
      (W : P.A.left.Opens) (f f' : Γ(P.A.left, W)), ⊤ ≤ (y ≫ LieVB.unitSec P.A) ⁻¹ᵁ W →
        HermFrame.form (HermFrame.dualGram d.H) (d.cov W f) (d.cov W f') =
          HermFrame.form (HermFrame.dualGram d'.H) (d'.cov W f) (d'.cov W f')) :
    ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (P : PPAS X) (t : ℝ), 0 < t →
    ∃ h : VMetric p (LieVB.omega P.A) P.g, P.IsDualRiemann t h := by
  intro k _ X p P t ht
  have hE := P.isVB_omega
  have hex : ∀ (σ : k →+* ℂ) (y : CxPts p σ), ∃ (d : P.RiemannData y.1)
      (C : Matrix (Fin P.g) (Fin P.g) ℂ), IsUnit C ∧ ∀ (U : X.Opens) (W : P.A.left.Opens)
      (hU : U ≤ unitSec P.A ⁻¹ᵁ W) (f : Γ(P.A.left, W)), y ∈ ptsIn p σ U →
        d.cov W f = C *ᵥ (hE.pick y).crd p σ (dUnit P.A hU f) y := fun σ y => by
    obtain ⟨d⟩ := hex₀ X P y.1
    obtain ⟨C, h₁, h₂⟩ := exists_isUnit hc₁ hc₂ hc₃ P y d (hE.pick y) (hE.mem_pick y)
    exact ⟨d, C, h₁, h₂⟩
  choose D C hCu hC using hex
  have htc : (0 : ℂ) < (t : ℂ) := by exact_mod_cast ht
  let m (σ : k →+* ℂ) : Met p σ (omega P.A) P.g :=
    Met.ofPt hE (fun y => hE.pick y) (fun y => hE.mem_pick y)
      (fun y => chg (C σ y) (dualGram ((t : ℂ) • (D σ y).H)))
      (fun y => posDef_chg (hCu σ y) (posDef_dualGram ((D σ y).posDef.smul htc)))
  have hindep (σ : k →+* ℂ) (y : CxPts p σ) (d d' : P.RiemannData y.1) (W : P.A.left.Opens)
      (f f' : Γ(P.A.left, W)) (hW : ⊤ ≤ (y.1 ≫ unitSec P.A) ⁻¹ᵁ W) :
      form (dualGram ((t : ℂ) • d.H)) (d.cov W f) (d.cov W f') =
        form (dualGram ((t : ℂ) • d'.H)) (d'.cov W f) (d'.cov W f') := by
    rw [form_dualGram_smul d.posDef ht, form_dualGram_smul d'.posDef ht,
      hind X P y.1 d d' W f f' hW]
  have hform (σ : k →+* ℂ) (y : CxPts p σ) (d : P.RiemannData y.1) (U : X.Opens)
      (W : P.A.left.Opens) (hU : U ≤ unitSec P.A ⁻¹ᵁ W) (f f' : Γ(P.A.left, W))
      (hy : y ∈ ptsIn p σ U) :
      (m σ).form (dUnit P.A hU f) (dUnit P.A hU f') y =
        form (dualGram ((t : ℂ) • d.H)) (d.cov W f) (d.cov W f') := by
    have hG : (m σ).G (hE.pick y) y = chg (C σ y) (dualGram ((t : ℂ) • (D σ y).H)) := by
      change chg ((hE.pick y).tr p σ (hE.pick y) y) _ = _
      rw [Chart.tr_self _ (hE.mem_pick y), chg_one]
    have hW : ⊤ ≤ (y.1 ≫ unitSec P.A) ⁻¹ᵁ W := fun z hz => hU (mem_ptsIn.1 hy) |> fun h => by
      rw [Subsingleton.elim z (IsLocalRing.closedPoint ℂ)]
      exact h
    rw [(m σ).form_eq (hE.pick y) (hE.mem_pick y) _ _ hy, hG, form_chg, ← hC σ y U W hU f hy,
      ← hC σ y U W hU f' hy]
    exact hindep σ y _ d W f f' hW
  have hconj (σ σ' : k →+* ℂ) : (m σ).IsConj (m σ') := Met.isConj_of_exists fun y y' e => by
    obtain ⟨d', hH, hcov⟩ : ∃ d' : P.RiemannData y'.1, d'.H = (D σ y).H.map star ∧
        ∀ (W : P.A.left.Opens) (f : Γ(P.A.left, W)), ⊤ ≤ (y.1 ≫ unitSec P.A) ⁻¹ᵁ W →
          d'.cov W f = star ((D σ y).cov W f) := by
      rw [e]
      exact hc₄ X P y.1 (D σ y)
    refine ⟨hE.pick y, hE.mem_pick y, Matrix.ext fun a b => ?_⟩
    have hc := hE.mem_pick y
    obtain ⟨U', W, hx, hle, cc⟩ := Conormal.exists_isChart
      (LieVB.sec_hom (MonObj.one (X := P.A))) (mem_ptsIn.1 hc)
    have hy : y ∈ ptsIn p σ U' := mem_ptsIn.2 hx
    have hy' : y' ∈ ptsIn p σ' U' := (mem_ptsIn_iff_of_conj e).2 hy
    choose f hf using fun a => cc.d_surjective (LieVB.sec_hom (MonObj.one (X := P.A)))
      (resM (omega P.A) hle ((hE.pick y).e a))
    have hW : ⊤ ≤ (y.1 ≫ unitSec P.A) ⁻¹ᵁ W := fun z hz => by
      rw [Subsingleton.elim z (IsLocalRing.closedPoint ℂ)]
      exact cc.le (mem_ptsIn.1 hy)
    have e₁ : (m σ).G (hE.pick y) y a b = form (dualGram ((t : ℂ) • (D σ y).H))
        ((D σ y).cov W (f a)) ((D σ y).cov W (f b)) := by
      rw [← (m σ).form_frame _ hc, ← Met.form_resM _ _ _ hle hy, ← hf a, ← hf b]
      exact hform σ y _ U' W cc.le _ _ hy
    have e₂ : (m σ').G (hE.pick y) y' a b = form (dualGram ((t : ℂ) • d'.H))
        (d'.cov W (f a)) (d'.cov W (f b)) := by
      rw [← (m σ').form_frame _ ((mem_ptsIn_iff_of_conj e).2 hc), ← Met.form_resM _ _ _ hle hy',
        ← hf a, ← hf b]
      exact hform σ' y' _ U' W cc.le _ _ hy'
    rw [e₂, map_apply, e₁, hH, hcov _ _ hW, hcov _ _ hW, form_dualGram_conj]
  exact ⟨⟨hE, m, hconj⟩, fun σ y => ⟨⟨D σ y⟩, fun d U W hU f f' hy => hform σ y d U W hU f f' hy⟩⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsWittFrameExtend
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.DescB.PlaneTwo GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.TwoPlaneWitt

open Matrix
open Formalism.UG (cT)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

omit [NumberField F] [NumberField E] in

theorem hE_smul_map {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (c s t : E)
    (x y : Fin n → E) : hE σ (c • J.map σ) (s • x) (t • y) = σ s * t * c * σ (form σ J x y) := by
  simp only [hE, form, dotProduct, mulVec, Finset.mul_sum, map_sum, map_mul, Function.comp_apply, hσ, Pi.smul_apply,
    smul_eq_mul, Matrix.smul_apply, Matrix.map_apply]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    show σ (s * x i) * (c * σ (J i j)) * (t * y j) = _
    rw [map_mul]; ring

omit [NumberField F] [NumberField E] in

theorem form_mulVec {σ : E →ₐ[F] E} {n m : ℕ} (J : Matrix (Fin n) (Fin n) E) (ι : Matrix (Fin n) (Fin m) E)
    (u v : Fin m → E) : form σ J (ι *ᵥ u) (ι *ᵥ v) = form σ (ιᵀ * J * ι.map σ) u v := by
  have e : (⇑σ ∘ (ι *ᵥ v)) = ι.map σ *ᵥ (⇑σ ∘ v) := funext fun i => by simp [mulVec, dotProduct, map_sum]
  show (ι *ᵥ u) ⬝ᵥ J *ᵥ (⇑σ ∘ (ι *ᵥ v)) = u ⬝ᵥ (ιᵀ * J * ι.map σ) *ᵥ (⇑σ ∘ v)
  rw [e, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec u, vecMul_transpose]

omit [NumberField F] [NumberField E] in

theorem form_swap {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hJ : ∀ i j, σ (J j i) = -J i j) (x y : Fin n → E) : form σ J x y = -σ (form σ J y x) := by
  simp only [form, dotProduct, mulVec, Finset.mul_sum, map_sum, map_mul, Function.comp_apply, hσ, hJ,
    ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end GlobalTheory.TwoPlaneWitt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsValEq
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar

noncomputable section

namespace GlobalTheory.ThK.SmoothLev

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def SmModUA (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (f : UA σ J → ℂ) : Prop :=
  ∀ c₀ : E, c₀ ≠ 0 → IsHermND σ (c₀ • J.map σ) → ∀ φ' : GAd σ (c₀ • J.map σ) → ℂ,
    (∀ (g : UA σ J) (g' : GAd σ (c₀ • J.map σ)), g.1 = g'.1 → φ' g' = f g) →
    GlobalTheory.SiegelSet.IsSmoothModerate σ (c₀ • J.map σ) φ'

theorem exists_val_eq (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (hσ : IsCMExt F E σ) {c₀ : E}
    (hc₀ : c₀ ≠ 0) (g' : GAd σ (c₀ • J.map σ)) : ∃ g : UA σ J, g.1 = g'.1 := by
  have := GlobalTheory.SiegelSet.ug_eq_hr (F := F) (J := J) (GlobalTheory.SiegelSet.sigma_sigma hσ) hc₀
  obtain ⟨x, hx⟩ := g'
  exact ⟨⟨x, (SetLike.ext_iff.1 this x).2 hx⟩, rfl⟩

end GlobalTheory.ThK.SmoothLev
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodMetricLocalTransgressionFormulaStatement
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodMetric_local_transgression_formula : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (S : Finset (Fin n)) (U K : Set (V n)) (G₀ G₁ : V n → Matrix r r ℂ) (ρ : V n → ℝ) (c : ℝ), IsOpen U → IsCompact K → K ⊆ U → (∀ v ∈ U, ∀ a ∈ S, ‖v a‖ ≤ 1 / 2) → (∀ v ∈ U, MContDiffAt ∞ G₀ v ∧ IsUnit (G₀ v).det) → (∀ v ∈ offHyp S U, MContDiffAt ∞ G₁ v ∧ IsUnit (G₁ v).det) → (∀ v ∈ offHyp S U, ∀ a i j, ‖conn G₁ v (coordVec a) i j‖ * poinWt S v a ≤ c) → (∀ v ∈ offHyp S U, ∀ a b i j, ‖curv G₁ v (coordVec a) (coordVec b) i j‖ * (poinWt S v a * poinWt S v b) ≤ c) → ContDiffOn ℝ ∞ ρ U → (∀ v ∈ U, v ∉ K → ρ v = 0) → (∫ v in offHyp S U, (ρ v : ℂ) * mixTop fun _ => curvAt G₁ v) - (∫ v in U, (ρ v : ℂ) * mixTop fun _ => curvAt G₀ v) = ∫ v in offHyp S U, corrC ρ G₀ G₁ v := by
  first | exact @GlobalTheory.GoodTop.integral_cutTop_sub | exact GlobalTheory.GoodTop.integral_cutTop_sub | (intros; apply GlobalTheory.GoodTop.integral_cutTop_sub <;> assumption)
end

