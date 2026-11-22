import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0944
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AnFibLift
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0168
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0958
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1261
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1539
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0995
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0991
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1012
import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1545
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1546
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1097
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GtActIffEqGtSmul
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0191
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaConstantEqSumThetaTermsOddMultiple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1547
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0026
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfM
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0038
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1530
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0769
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1550
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPushFrame
section
open AlgebraicGeometry CategoryTheory NumberField Matrix MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.FrameEquiv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000

namespace GlobalTheory.AnMove

open GlobalTheory.Dict.Lift
open scoped MonObj

theorem exists_push_frame {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {Y : Scheme.{0}} {L : LB Y}
    (hL : L.IsLB) (φ : Y ⟶ Y) (O : L.ι → L.ι → Y.Opens) (ω : ∀ i j, Γ(Y, O i j))
    (hO : ∀ i j (p : Sp ℂ ⟶ Y), ⊤ ≤ p ⁻¹ᵁ O i j ↔ (⊤ ≤ (p ≫ φ) ⁻¹ᵁ L.U i ∧ ⊤ ≤ p ⁻¹ᵁ L.U j))
    (hne : ∀ i j (p : Sp ℂ ⟶ Y), ⊤ ≤ p ⁻¹ᵁ O i j → valAt' p (O i j) (ω i j) ≠ 0)
    (hg : ∀ i j i' j' (p : Sp ℂ ⟶ Y), ⊤ ≤ p ⁻¹ᵁ O i j → ⊤ ≤ p ⁻¹ᵁ O i' j' →
      valAt' p (O i j) (ω i j) * valAt' p (L.U j ⊓ L.U j') (L.g j j').val =
        valAt' (p ≫ φ) (L.U i ⊓ L.U i') (L.g i i').val * valAt' p (O i' j') (ω i' j'))
    (e : V → (Sp ℂ ⟶ Y)) (hol : IsHolTo Set.univ e) (fr : L.ι → V → ℂ)
    (fr_hol : ∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ e z ⁻¹ᵁ L.U j})
    (fr_ne : ∀ j z, ⊤ ≤ e z ⁻¹ᵁ L.U j → fr j z ≠ 0)
    (fr_g : ∀ j j' z, ⊤ ≤ e z ⁻¹ᵁ (L.U j ⊓ L.U j') →
      fr j z = valAt' (e z) (L.U j ⊓ L.U j') (L.g j j').val * fr j' z) :
    ∃ fr' : L.ι → V → ℂ, (∀ i, DifferentiableOn ℂ (fr' i) {z | ⊤ ≤ (e z ≫ φ) ⁻¹ᵁ L.U i}) ∧
      (∀ i z, ⊤ ≤ (e z ≫ φ) ⁻¹ᵁ L.U i → fr' i z ≠ 0) ∧
      (∀ i i' z, ⊤ ≤ (e z ≫ φ) ⁻¹ᵁ (L.U i ⊓ L.U i') →
        fr' i z = valAt' (e z ≫ φ) (L.U i ⊓ L.U i') (L.g i i').val * fr' i' z) ∧
      ∀ i j z, ⊤ ≤ (e z ≫ φ) ⁻¹ᵁ L.U i → ⊤ ≤ e z ⁻¹ᵁ L.U j →
        fr' i z = valAt' (e z) (O i j) (ω i j) * fr j z := by
  choose ch hch using fun z => exists_chart (e z) L hL
  have key : ∀ i j z, ⊤ ≤ (e z ≫ φ) ⁻¹ᵁ L.U i → ⊤ ≤ e z ⁻¹ᵁ L.U j →
      valAt' (e z) (O i (ch z)) (ω i (ch z)) * fr (ch z) z = valAt' (e z) (O i j) (ω i j) * fr j z := by
    intro i j z hi hj
    have h1 := hg i (ch z) i j (e z) ((hO _ _ _).2 ⟨hi, hch z⟩) ((hO _ _ _).2 ⟨hi, hj⟩)
    rw [val_g_self _ L hL i hi, _root_.one_mul] at h1
    rw [fr_g (ch z) j z ((top_le_preimage_inf _ _ _).2 ⟨hch z, hj⟩), ← mul_assoc, h1]
  refine ⟨fun i z => valAt' (e z) (O i (ch z)) (ω i (ch z)) * fr (ch z) z, fun i z₀ hz₀ => ?_, fun i z hi => ?_,
    fun i i' z h => ?_, key⟩
  · have hN := hol (O i (ch z₀)) (ω i (ch z₀))
    have hm := hN.1.mem_nhds (x := z₀) ⟨trivial, (hO _ _ _).2 ⟨hz₀, hch z₀⟩⟩
    have d1 : DifferentiableAt ℂ (fr (ch z₀)) z₀ :=
      (fr_hol (ch z₀)).differentiableAt (Filter.mem_of_superset hm fun z hz => ((hO _ _ _).1 hz.2).2)
    have d2 : DifferentiableAt ℂ (fun z => valAt' (e z) (O i (ch z₀)) (ω i (ch z₀))) z₀ := hN.2.differentiableAt hm
    refine ((d2.mul d1).congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [hm] with z hz
    exact key i (ch z₀) z ((hO _ _ _).1 hz.2).1 ((hO _ _ _).1 hz.2).2
  · exact mul_ne_zero (hne _ _ _ ((hO _ _ _).2 ⟨hi, hch z⟩)) (fr_ne _ z (hch z))
  · obtain ⟨hi, hi'⟩ := (top_le_preimage_inf _ _ _).1 h
    have h1 := hg i (ch z) i' (ch z) (e z) ((hO _ _ _).2 ⟨hi, hch z⟩) ((hO _ _ _).2 ⟨hi', hch z⟩)
    rw [val_g_self _ L hL _ (hch z), _root_.mul_one] at h1
    simp only []
    rw [h1, mul_assoc]

theorem anFib_move : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y y' : FrPt Xo c ℂ) (A : AnFib X bas idx e x L y), IsSympl X bas → x ∈ X.dom → SelfD X L → ∀ gM gA : Dw.La →ₗ[𝓞 E] Dw.La, levR (gM, gA) y y' → ∃ A' : AnFib X bas idx e x L y', (∀ θ, A.Reads 1 y.s θ → A'.Reads 1 y'.s θ) ∧ ∀ mk : Dw.La →ₗ[𝓞 E] (Fin r → E), A.Marked mk → A'.Marked (mk ∘ₗ gM) := by
  intro E _ _ _ H Dw l Xo c inst r g X bas idx e x L y y' A hsym hx hL gM gA hR
  obtain ⟨σ, rfl⟩ : ∃ σ : c.F →+* ℂ, inst = σ.toAlgebra :=
    ⟨algebraMap c.F ℂ, Algebra.algebra_ext _ _ fun _ => rfl⟩
  letI : Algebra c.F ℂ := σ.toAlgebra
  obtain ⟨ρ, ν, -, ⟨-, heta, -⟩, hmv⟩ := hR
  obtain ⟨O, ω, hO, hne, hg, hrig, hs⟩ := GlobalTheory.MoveValues.frMove_values E H Dw l Xo c σ ρ ν y y' hmv
  obtain ⟨hb, hu, -⟩ := hmv
  obtain ⟨Φ, hΦ⟩ := exists_mulEquiv ν.cart y.x y'.x hb.symm
  let ex : (Fin g → ℂ) → (ptO Xo y'.x ⟶ Xo.univ.t.G) := fun z => Φ (A.ex z)
  have hex : ∀ z, (ex z).left = (A.ex z).left ≫ ν.φ := fun z => hΦ _
  have hexf : (fun z => (ex z).left) = fun z => (A.ex z).left ≫ ν.φ := funext hex
  obtain ⟨fr, fr_hol, fr_ne, fr_g, key⟩ := exists_push_frame Xo.univ.t.PP.isLB ν.φ O ω hO hne hg
    (fun z => (A.ex z).left) A.hol A.fr A.fr_hol A.fr_ne A.fr_g
  have hch : ∀ z, ∃ a, ⊤ ≤ (A.ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U a :=
    fun z => exists_chart _ _ Xo.univ.t.PP.isLB
  have hex0 : (A.ex 0).left = y.x ≫ eSec Xo.univ.t.G := by
    have h0 : A.ex 0 = 1 := by
      have := A.ex_add 0 0
      rw [add_zero] at this
      exact left_eq_mul.1 this
    rw [h0]
    exact one_left _
  let A' : AnFib X bas idx e x L y' :=
    { ex := ex
      ex_add := fun z z' => by simp only [ex, A.ex_add, map_mul]
      ex_onto := Φ.surjective.comp A.ex_onto
      ex_ker := fun z => by
        rw [← A.ex_ker]
        exact Φ.map_eq_one_iff
      ex_lin := fun a z => by
        apply Over.OverMorphism.ext
        rw [hex, A.ex_lin, Over.comp_left, Over.comp_left, Category.assoc, ν.act, ← Category.assoc, hex]
      hol := hexf ▸ ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_comp A.hol ν.φ
      der := fun ℓ => by
        rw [hexf, hu]
        exact FibreDeriv.isDerivAt0_comp (A.der ℓ) ν.φ
      fr := fr
      fr_hol := by simpa only [hex] using fr_hol
      fr_ne := by simpa only [hex] using fr_ne
      fr_g := by simpa only [hex] using fr_g
      fr_0 := fun i hi => by
        obtain ⟨j, hj⟩ := hch 0
        rw [hex] at hi
        rw [key i j 0 hi hj, A.fr_0 j hj, hb]
        exact (hrig i j y.x _ hex0 ((hO _ _ _).2 ⟨hi, hj⟩)).symm
      χ := A.χ
      χ_norm := A.χ_norm
      fr_per := fun v hv i z hi => by
        obtain ⟨j, hj⟩ := hch z
        rw [hex] at hi
        have hz : A.ex (z + pv X idx x v) = A.ex z := by
          rw [A.ex_add, (A.ex_ker _).2 ⟨v, hv, rfl⟩, _root_.mul_one]
        have h2 := key i j (z + pv X idx x v) (hz ▸ hi) (hz ▸ hj)
        simp only [hz] at h2
        rw [key i j z hi hj, h2, A.fr_per v hv j z hj]
        ring }
  refine ⟨A', fun θ hθ i z pt' hp1 hp2 hi => ?_, fun mk hmk a ha => ?_⟩
  · obtain ⟨j, hj⟩ := hch z
    have hi' : ⊤ ≤ ((A.ex z).left ≫ ν.φ) ⁻¹ᵁ Xo.univ.t.PP.L.U i := hex z ▸ hi
    let pt : Sp ℂ ⟶ Gx y.x := (CartesianMonoidalCategory.lift (𝟙 (Over.mk y.x)) (A.ex z)).left
    have hq1 : pt ≫ Formalism.L2.PjFree.gxFst y.x = (A.ex z).left :=
      congrArg (·.left) (CartesianMonoidalCategory.lift_snd (𝟙 (Over.mk y.x)) (A.ex z))
    have hq2 : pt ≫ Formalism.L2.PjFree.gxSnd y.x = 𝟙 _ :=
      congrArg (·.left) (CartesianMonoidalCategory.lift_fst (𝟙 (Over.mk y.x)) (A.ex z))
    have h1 := hθ j z pt hq1 hq2 hj
    have h2 := hs i j pt pt' _ hq1 hq2 (hp1.trans (hex z)) hp2 ((hO _ _ _).2 ⟨hi', hj⟩)
    refine h2.trans ((congrArg (_ * ·) h1).trans ?_)
    change _ = θ z * fr i z ^ (1 : ℤ)
    rw [zpow_one, zpow_one, key i j z hi' hj]
    ring
  · have ha' : gM a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La) := by
      have := Submodule.mem_map_of_mem (f := gM) ha
      rw [Submodule.map_smul''] at this
      exact Submodule.smul_mono le_rfl le_top this
    change _ = Φ (A.ex (pv X idx x (((l.M : E)⁻¹) • mk (gM a))))
    rw [← hmk _ ha']
    apply Over.OverMorphism.ext
    rw [hΦ, levPt, levPt, Over.comp_left, Over.comp_left, Category.assoc, heta, toUnit_left, toUnit_left, hb]
    exact Category.assoc _ _ _

end GlobalTheory.AnMove
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSphericalCuspFormWhittakerNeZero
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix
open scoped ContDiff

noncomputable section

namespace GlobalTheory.JSW.NzSph

theorem finite_bad (E : Type) [Field E] [NumberField E] (a : ℕ) (k : GL (Fin a) (Af E)) :
    {w : HeightOneSpectrum (𝓞 E) | GeneralLinearGroup.map (pLoc E w) k ∉ KGL w a}.Finite :=
  GlobalTheory.T.finiteAdelicGL_mem_integral_cofinite_places E a k

theorem exists_outside (E : Type) [Field E] [NumberField E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (k : GL (Fin a) (Af E)) : ∃ k' : GL (Fin a) (Af E),
      (∀ w ∉ S, GeneralLinearGroup.map (pLoc E w) k' = GeneralLinearGroup.map (pLoc E w) k) ∧
      ∀ w ∈ S, GeneralLinearGroup.map (pLoc E w) k' = 1 :=
  GlobalTheory.T.exists_finiteAdelicGL_agree_outside_trivial_on_finset E a S k

theorem local_decomp (E : Type) [Field E] [NumberField E] (a : ℕ) (w : HeightOneSpectrum (𝓞 E))
    (ϖ : (w.adicCompletion E)ˣ) (hϖ : IsUnifV E w (ϖ : w.adicCompletion E)) (g : GL (Fin a) (w.adicCompletion E)) :
    ∃ u ∈ GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin a), ∃ (N : ℕ) (l : Fin a → ℕ), ∃ k ∈ KGL w a,
      g = u * GlobalTheory.JSW.diagPow ϖ⁻¹ (fun _ => N) * GlobalTheory.JSW.diagPow ϖ l * k :=
  GlobalTheory.T.iwasawa_decomposition_adicCompletionGL_diagonalPowers E a w ϖ hϖ g

theorem act_fin_eq_of_outside (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (φ : Sm E a)
    (hφ : IsAutForm φ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (hS : ∀ w ∉ S, ∀ k ∈ KGL w a, act (.fin (locGL E a w k)) φ = φ) (k : GL (Fin a) (Af E))
    (hk : ∀ w ∉ S, GeneralLinearGroup.map (pLoc E w) k ∈ KGL w a)
    (hk1 : ∀ w ∈ S, GeneralLinearGroup.map (pLoc E w) k = 1) : act (.fin k) φ = φ :=
  GlobalTheory.T.smoothAutomorphicForm_fixed_of_locally_integral_fixed E a φ hφ S hS k hk hk1

end GlobalTheory.JSW.NzSph

namespace GlobalTheory.JSW.NzSph

open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.MultiplicityOne

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem map_pLoc_pFin (w : HeightOneSpectrum (𝓞 E)) (g : GA E a) :
    GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) g) =
      GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) g := by
  ext; rfl

theorem comp_finGL (v : HeightOneSpectrum (𝓞 E)) (h : GL (Fin a) (Af E)) :
    GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) (finGL E a h) = GeneralLinearGroup.map (pLoc E v) h := by
  rw [finGL, map_cornerGL_of_hom (sFin E) ((pLoc E v).comp (pFin E)) (pLoc E v) (fun x => rfl)]

theorem diagPow_const_comm {K : Type} [CommRing K] {n : ℕ} (c : Kˣ) (N : ℕ) (h : GL (Fin n) K) :
    GlobalTheory.JSW.diagPow c (fun _ : Fin n => N) * h = h * GlobalTheory.JSW.diagPow c (fun _ : Fin n => N) := by
  ext i j
  simp [GlobalTheory.JSW.diagPow, Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm]

variable [IsTotallyComplex E]

theorem whit_act_fin (φ : Sm E a) (k : GL (Fin a) (Af E)) (y : GA E a) :
    whit (act (.fin k) φ).1 y = whit φ.1 (y * finGL E a k) := by
  rw [whit_mul_right]; rfl

theorem act_fin_mul (k k' : GL (Fin a) (Af E)) (φ : Sm E a) :
    act (.fin (k * k')) φ = act (.fin k) (act (.fin k') φ) := by
  show finRep E a (k * k') φ = finRep E a k (finRep E a k' φ)
  rw [map_mul]; rfl

theorem exists_whittaker_ne_zero_induction_bad_places (S : Finset (HeightOneSpectrum (𝓞 E)))
    (hψ : ∀ w ∉ S, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, GlobalTheory.JSW.psiLoc w (x * y) = 1) ↔ x ∈ Ov E w)
    (π : CuspSub E a) (α : HeightOneSpectrum (𝓞 E) → Fin a → ℂˣ)
    (hα : ∀ w ∉ S, HasSatGL w (π.locRep w) (Finset.univ.val.map (α w))) (T : Finset (HeightOneSpectrum (𝓞 E))) :
    ∀ φ ∈ π.V, (∀ w ∉ S, ∀ k ∈ KGL w a, act (.fin (locGL E a w k)) φ = φ) → ∀ g : GA E a,
      (∀ w ∉ S, w ∉ T → GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) g ∈ KGL w a) → whit φ.1 g ≠ 0 →
      ∃ φ ∈ π.V, (∀ w ∉ S, ∀ k ∈ KGL w a, act (.fin (locGL E a w k)) φ = φ) ∧
        ∃ x ∈ GlobalTheory.JSW.supS E a S, whit φ.1 x ≠ 0 := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    intro φ hφV hφ g hg hW
    obtain ⟨k, hk1, hk2⟩ := exists_outside E a S (GeneralLinearGroup.map (pFin E) g)
    have hinv : act (.fin k) φ = φ := act_fin_eq_of_outside E a φ (π.cusp φ hφV).1 S hφ k
      (fun w hw => by rw [hk1 w hw, map_pLoc_pFin]; exact hg w hw (Finset.notMem_empty w)) hk2
    refine ⟨φ, hφV, hφ, g * (finGL E a k)⁻¹, fun w hw => ?_, ?_⟩
    · rw [map_mul, map_inv, comp_finGL, hk1 w hw, map_pLoc_pFin, mul_inv_cancel]
    · have e : g = g * (finGL E a k)⁻¹ * finGL E a k := by group
      rw [e, ← whit_act_fin, hinv] at hW
      exact hW
  | insert w T hwT ih =>
    intro φ hφV hφ g hg hW
    by_cases hwS : w ∈ S
    · refine ih φ hφV hφ g (fun v hv hvT => hg v hv ?_) hW
      rw [Finset.mem_insert, not_or]
      exact ⟨fun h => hv (h ▸ hwS), hvT⟩
    obtain ⟨ϖ0, hϖ0⟩ := exists_isUnifV (E := E) w
    have hne : ϖ0 ≠ 0 := fun h => by simp [IsUnifV, h] at hϖ0
    let ϖ : (w.adicCompletion E)ˣ := Units.mk0 ϖ0 hne
    have hϖ : IsUnifV E w (ϖ : w.adicCompletion E) := hϖ0
    let gw := GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) g
    obtain ⟨u, hu, N, l, k, hk, hdec⟩ := local_decomp E a w ϖ hϖ gw
    let z := GlobalTheory.JSW.diagPow ϖ⁻¹ (fun _ : Fin a => N)
    let d := GlobalTheory.JSW.diagPow ϖ l
    let F : GL (Fin a) (w.adicCompletion E) →* GA E a := (finGL E a).comp (locGL E a w)
    have hF : ∀ h, F h = finGL E a (locGL E a w h) := fun h => rfl
    let y := g * (F gw)⁻¹
    have hyw : GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) y = 1 := by
      show GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) (g * (finGL E a (locGL E a w gw))⁻¹) = 1
      rw [map_mul, map_inv, comp_finGL, pLoc_locGL]; exact mul_inv_cancel _
    have hyv : ∀ v, v ≠ w → GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) y =
        GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) g := by
      intro v hv
      show GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) (g * (finGL E a (locGL E a w gw))⁻¹) = _
      rw [map_mul, map_inv, comp_finGL, pLoc_locGL_of_ne hv, inv_one, mul_one]
    have hg' : g = y * F u * F z * F d * F k := by
      have : F gw = F u * F z * F d * F k := by
        rw [hdec, map_mul, map_mul, map_mul]
      calc g = y * F gw := by simp only [y]; group
        _ = _ := by rw [this]; simp only [mul_assoc]
    have hcont : Continuous φ.1 := (π.cusp _ hφV).1.continuous
    have hleft : AutomorphicForm.IsLeftInvariant φ.1 := fun γ x => by
      rw [show AdelicGLn.diagonal E a γ = ratGL E a γ from Units.ext (Matrix.ext fun _ _ => rfl)]
      exact (π.cusp _ hφV).1.left γ x

    have h1 : whit φ.1 (y * F u * F z * F d) ≠ 0 := by
      rw [hg', hF k, ← whit_act_fin, hφ w hwS k hk] at hW
      exact hW

    have h2 : whit φ.1 (y * F z * F d) ≠ 0 := by
      have e : y * F u * F z * F d = F u * (y * F z * F d) := by
        rw [hF u, commute_finGL_locGL w hyw u]; group
      rw [e, hF u, finGL_locGL_eq_uGL w hu, whit, whittaker_uGL_mul hcont hleft] at h1
      exact right_ne_zero_of_mul h1

    let φ₁ := act (.fin (locGL E a w z)) φ
    have hφ₁V : φ₁ ∈ π.V := π.stable _ φ hφV
    have hφ₁ : ∀ v ∉ S, ∀ k' ∈ KGL v a, act (.fin (locGL E a v k')) φ₁ = φ₁ := by
      intro v hv k' hk'
      have hc : locGL E a v k' * locGL E a w z = locGL E a w z * locGL E a v k' := by
        by_cases hvw : v = w
        · subst hvw; rw [← map_mul, ← map_mul, diagPow_const_comm]
        · exact (GlobalTheory.CuspRep.LocSph.comm_locGL v (locGL E a w z) (pLoc_locGL_of_ne hvw z) k').symm
      simp only [φ₁]
      rw [← act_fin_mul, hc, act_fin_mul, hφ v hv k' hk']
    have h3 : whit φ₁.1 (y * F d) ≠ 0 := by
      have e : y * F z * F d = y * F d * F z := by
        rw [mul_assoc y (F z), mul_assoc y (F d), ← map_mul, ← map_mul, diagPow_const_comm]
      rw [e, hF z, ← whit_act_fin] at h2
      exact h2
    have h4 : whit φ₁.1 y ≠ 0 := by
      have := GlobalTheory.JSW.whit_mul_locGL_diagPow E a π w (α w) (hψ w hwS) (hα w hwS) φ₁ hφ₁V (hφ₁ w hwS) y hyw ϖ hϖ l
      rw [hF d] at h3
      rw [this] at h3
      exact right_ne_zero_of_mul h3
    refine ih φ₁ hφ₁V hφ₁ y (fun v hv hvT => ?_) h4
    by_cases hvw : v = w
    · subst hvw; rw [hyw]; exact one_mem _
    · rw [hyv v hvw]
      exact hg v hv (by rw [Finset.mem_insert, not_or]; exact ⟨hvw, hvT⟩)

theorem exists_sph_whit_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))), (∀ w ∉ S, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, GlobalTheory.JSW.psiLoc w (x * y) = 1) ↔ x ∈ Ov E w) → ∀ (π : CuspSub E (m + 1)) (α : HeightOneSpectrum (𝓞 E) → Fin (m + 1) → ℂˣ), (∀ w ∉ S, HasSatGL w (π.locRep w) (Finset.univ.val.map (α w))) → ∃ φ ∈ π.V, (∀ w ∉ S, ∀ k ∈ KGL w (m + 1), act (.fin (locGL E (m + 1) w k)) φ = φ) ∧ ∃ x ∈ GlobalTheory.JSW.supS E (m + 1) S, GlobalTheory.JSW.whit φ.1 x ≠ 0 := by
  intro E _ _ _ m S hψ π α hα
  obtain ⟨φ₀, hφ₀V, hφ₀0, hφ₀K⟩ := GlobalTheory.T.exists_global_spherical_vector_of_satake_family E (m + 1) π S (fun w => Finset.univ.val.map (α w)) hα
  obtain ⟨g, hg⟩ : ∃ g, whit φ₀.1 g ≠ 0 := by
    by_contra h
    push_neg at h
    exact hφ₀0 (GlobalTheory.T.cusp_form_eq_zero_of_whittaker_vanishing E (m + 1) φ₀ (π.cusp φ₀ hφ₀V) h)
  have hfin := finite_bad E (m + 1) (GeneralLinearGroup.map (pFin E) g)
  refine exists_whittaker_ne_zero_induction_bad_places S hψ π α hα hfin.toFinset φ₀ hφ₀V hφ₀K g (fun w _ hwT => ?_) hg
  by_contra h
  refine hwT (hfin.mem_toFinset.2 ?_)
  show GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) g) ∉ KGL w (m + 1)
  rw [map_pLoc_pFin]; exact h

end GlobalTheory.JSW.NzSph
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTateModuleLevelComponentEqOfCardTorsion
section
set_option autoImplicit false

open GlobalTheory.HTLat

namespace GlobalTheory

theorem exists_pow_prime_root_of_card_torsion {M : Type} [CommGroup M] {l : ℕ} [Fact l.Prime]
    {c : ℕ} (hcard : ∀ k : ℕ, Nat.card {x : M // x ^ (l ^ k) = 1} = l ^ (c * k)) (k : ℕ) (y : M)
    (hy : y ^ (l ^ k) = 1) : ∃ z : M, z ^ (l ^ (k + 1)) = 1 ∧ z ^ l = y := by
  have hl : 0 < l := (Fact.out : l.Prime).pos
  let T : ℕ → Subgroup M := fun n => (powMonoidHom (l ^ n)).ker
  have hT : ∀ n, Nat.card (T n) = l ^ (c * n) := fun n => by
    rw [← hcard n]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by simp [T, MonoidHom.mem_ker])
  let φ : T (k + 1) →* M := (powMonoidHom l).comp (T (k + 1)).subtype
  have hker : Nat.card φ.ker = l ^ c := by
    rw [← mul_one c, ← hT 1]
    refine Nat.card_congr
      { toFun := fun y => ⟨y.1.1, ?_⟩
        invFun := fun z => ⟨⟨z.1, ?_⟩, ?_⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    · have := y.2
      simp only [T, φ, MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
        powMonoidHom_apply, Subgroup.coe_subtype] at this
      simpa [T, MonoidHom.mem_ker] using this
    · have hz : (z : M) ^ l = 1 := by simpa [T] using MonoidHom.mem_ker.1 z.2
      simp only [T, MonoidHom.mem_ker, powMonoidHom_apply]
      rw [pow_succ' l k, pow_mul, hz, one_pow]
    · have := z.2
      simpa [T, φ, MonoidHom.mem_ker] using this
  have hrange : Nat.card φ.range = l ^ (c * k) := by
    have h1 := Subgroup.card_mul_index φ.ker
    rw [Subgroup.index_ker, hker, hT (k + 1), mul_add, mul_one, pow_add, mul_comm] at h1
    exact Nat.eq_of_mul_eq_mul_right (pow_pos hl c) h1
  have hfin : Finite (T k) := Nat.finite_of_card_ne_zero (by rw [hT k]; exact (pow_pos hl _).ne')
  have hle : φ.range ≤ T k := by
    rintro _ ⟨z, rfl⟩
    have := z.2
    simp only [T, MonoidHom.mem_ker, powMonoidHom_apply] at this ⊢
    simp only [φ, MonoidHom.coe_comp, Function.comp_apply, powMonoidHom_apply,
      Subgroup.coe_subtype]
    rw [← pow_mul, ← pow_succ', this]
  have heq : φ.range = T k := Subgroup.eq_of_le_of_card_ge hle (by rw [hrange, hT k])
  have hyT : y ∈ T k := by simpa [T, MonoidHom.mem_ker] using hy
  rw [← heq] at hyT
  obtain ⟨z, hz⟩ := hyT
  exact ⟨z.1, MonoidHom.mem_ker.1 z.2, hz⟩

theorem exists_tate_lev_eq_of_card_torsion :
    ∀ (M : Type) [CommGroup M] (l : ℕ) [Fact l.Prime] (c : ℕ),
      (∀ k : ℕ, Nat.card {x : M // x ^ (l ^ k) = 1} = l ^ (c * k)) →
      ∀ (N : ℕ) (x : M), x ^ (l ^ N) = 1 → ∃ t : Tate l M, t.lev N = x := by
  intro M _ l _ c hcard N x hx
  have h := exists_pow_prime_root_of_card_torsion hcard
  choose r hr1 hr2 using h
  let g : (n : ℕ) → {y : M // y ^ (l ^ (N + n)) = 1} := fun n =>
    Nat.rec ⟨x, hx⟩ (fun n y => ⟨r (N + n) y.1 y.2, hr1 (N + n) y.1 y.2⟩) n
  have hg0 : (g 0).1 = x := rfl
  have hgs : ∀ n, (g (n + 1)).1 ^ l = (g n).1 := fun n => hr2 (N + n) (g n).1 (g n).2
  have hgk : ∀ n k, (g (n + k)).1 ^ (l ^ k) = (g n).1 := fun n k => by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', pow_mul]
      show ((g (n + k + 1)).1 ^ l) ^ (l ^ k) = _
      rw [hgs, ih]
  let s : ℕ → M := fun n => (g n).1 ^ (l ^ N)
  have hs : ∀ n, s n ^ l ^ n = 1 ∧ s (n + 1) ^ l = s n := fun n => by
    refine ⟨?_, ?_⟩
    · simp only [s]
      rw [← pow_mul, ← pow_add, (g n).2]
    · simp only [s]
      rw [← pow_mul, mul_comm, pow_mul, hgs]
  refine ⟨Tate.mk s hs, ?_⟩
  rw [Tate.lev_mk]
  simp only [s]
  have := hgk 0 N
  rw [zero_add] at this
  rw [this, hg0]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstOrderPointIffRingHomAffineOpenSectionsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.firstOrderPoint_iff_ringHom_affineOpen_sections : ∀ (B : Type) [CommRing B] (X : Scheme.{0}) (s : X ⟶ Sp B) (U : (Sp B).Opens) (V : X.Opens),
    IsAffineOpen U → IsAffineOpen V → ∀ (e : V ≤ s ⁻¹ᵁ U) (d : ℕ) (k : Type) [Field k] (x : Sp k ⟶ X),
    Set.range x.base ⊆ (V : Set X) → (∃ u : Sp (TrivSqZeroExt k (Fin d → k)) ⟶ X, spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom ≫ u = x ∧ u ≫ s = spMap (algebraMap k (TrivSqZeroExt k (Fin d → k))) ≫ x ≫ s ∧ ∀ v : Sp (DualNumber k) ⟶ X, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v = x → v ≫ s = spMap (algebraMap k (DualNumber k)) ≫ x ≫ s → ∃! c : (Fin d → k) →ₗ[k] k, v = spMap (TrivSqZeroExt.map c).toRingHom ≫ u) →
    ∃ (φ : Γ(X, V) →+* k) (ψ : Γ(X, V) →+* TrivSqZeroExt k (Fin d → k)),
      (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom.comp ψ = φ ∧
      ψ.comp (s.appLE U V e).hom = (algebraMap k (TrivSqZeroExt k (Fin d → k))).comp (φ.comp (s.appLE U V e).hom) ∧
      ∀ v : Γ(X, V) →+* DualNumber k, (TrivSqZeroExt.fstHom k k k).toRingHom.comp v = φ →
        v.comp (s.appLE U V e).hom = (algebraMap k (DualNumber k)).comp (φ.comp (s.appLE U V e).hom) →
        ∃! c : (Fin d → k) →ₗ[k] k, v = (TrivSqZeroExt.map c).toRingHom.comp ψ := by
  first | exact @GlobalTheory.SchRing.deformation_on_sections | exact GlobalTheory.SchRing.deformation_on_sections | (intros; apply GlobalTheory.SchRing.deformation_on_sections <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacuumLinePlacewiseSignaturesStatement
section
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fock_vacuum_line_placewise_signatures : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : InfinitePlace F → ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ) (Φ : TensD F P Q R S →ₗ[ℂ] SInf F κ), IsCMExt F E σ → IsStd ψ →
    FramedD τ JA JB a b A C → IsFockMapD ψ τ d A C Φ → ∀ (f₀ : SInf F κ) (ε : InfinitePlace F → ℤˣ),
    (∀ u u' : Matrix α β (AE F E), At (evI F) u → At (evI F) u' → ∀ c : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ,
      (∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ) →
      (∀ w, u'.map (piInf (τ w)) = A w * ((((ε w : ℤ) : ℂ) * Complex.I) • (Jm (P w) (Q w) * c w * Jm (R w) (S w))) * (C w)ᵀ) →
      ∀ f f' : SInf F κ, SD (fun t => d.rho ψ (realAd F t • u)) f₀ f → SD (fun t => d.rho ψ (realAd F t • u')) f₀ f' →
        f' = Complex.I • f) →
    ∃ z : ℂ, f₀ = z • Φ (PiTensorProduct.tprod ℂ fun _ => 1) := by
  first | exact @GlobalTheory.HoweD.vacLineD | exact GlobalTheory.HoweD.vacLineD | (intros; apply GlobalTheory.HoweD.vacLineD <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierCoefficientFamilyPullbackFractionFieldStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierCoefficient_familyPullback_fractionField : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (hG : GlobalFnsSt) (k : ℕ) (s : Fam D (FractionRing R) k) (g : GtPtF D (FractionRing R)) (w : Frm D (FractionRing R) k g.b) (w' : Frm D F k (GlobalTheory.TorusExt.gtExt D (algebraMap (FractionRing R) F) (RingHom.comp_id _) g).b), w.IsGen → w'.IsGen → (∀ z J, Good D.P.L z J → val w' (𝟙 _) z J = val w (spMap (algebraMap (FractionRing R) F)) z J) → ∀ χ : D.X, coef (GlobalTheory.FieldBaseChange.famPull D (FractionRing R) F hG k s) (GlobalTheory.TorusExt.gtExt D (algebraMap (FractionRing R) F) (RingHom.comp_id _) g) w' χ = algebraMap (FractionRing R) F (coef s g w χ) := by
  first | exact @GlobalTheory.Poinc.Tors.CoefPull.coef_famPull_frac | exact GlobalTheory.Poinc.Tors.CoefPull.coef_famPull_frac | (intros; apply GlobalTheory.Poinc.Tors.CoefPull.coef_famPull_frac <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantExtensionMeasurableContDiffOnChartStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariantExtension_measurable_contDiffOn_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r) (ρ R : ℝ) (η : V (nd X) → ℝ) (ψ : Frame X.Ψ r → ℝ), IsOrth X x → ρ < R → (∀ z : V (nd X), ‖z‖ ≤ R → z ∈ OmF X x) → ContDiff ℝ ∞ η → (∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r, ∀ z : V (nd X), ‖z‖ ≤ R → ψ (lact γ (rmul (cpt X x z) b)) = η z) → (∀ y, (¬ ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z : V (nd X), ‖z‖ ≤ ρ ∧ y = lact γ (rmul (cpt X x z) b)) → ψ y = 0) → (∀ y ∈ X.dom, (¬ ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z : V (nd X), ‖z‖ ≤ ρ ∧ y = lact γ (rmul (cpt X x z) b)) → ∀ᶠ y' in 𝓝 y, ¬ ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z : V (nd X), ‖z‖ ≤ ρ ∧ y' = lact γ (rmul (cpt X x z) b)) → Measurable ψ ∧ ContDiffOn ℝ ∞ (fun w => ψ (cpt X x w)) (OmF X x) := by
  first | exact @GlobalTheory.PeakWeightSmooth.measurable_and_contDiffOn | exact GlobalTheory.PeakWeightSmooth.measurable_and_contDiffOn | (intros; apply GlobalTheory.PeakWeightSmooth.measurable_and_contDiffOn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelStructureChangeFramedGeometricPointUniqueStatement
section
open CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LevPull
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelStructureChange_framedGeometricPoint_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → l.A = 1 → ∀ (lift : Gam Dw l → Dw.La →ₗ[𝓞 E] Dw.La), IsLift lift → ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] (y y' : FrPt Xo c k) (γ γ' : Gam Dw l), levR (lift γ, LinearMap.id) y y' → levR (lift γ', LinearMap.id) y y' → γ = γ' := by
  first | exact @GlobalTheory.LevelFree.move_unique | exact GlobalTheory.LevelFree.move_unique | (intros; apply GlobalTheory.LevelFree.move_unique <;> assumption)
end

