import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0538
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0518
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0539
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0493
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0507
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0517
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0536
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0460
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0339
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0542
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0526
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0540

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierCompCoordDilationByHalfExpStatement
section
open NumberField MeasureTheory
open scoped RealInnerProductSpace FourierTransform
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourier_comp_coordDilationByHalfExp : ∀ (I : Type) [Fintype I] (f : EuclideanSpace ℂ I → ℂ) (y : I → ℝ) (l : EuclideanSpace ℂ I), 𝓕 (fun w : EuclideanSpace ℂ I => f (WithLp.toLp 2 (GlobalTheory.HeckeTheta.dil y (WithLp.ofLp w)))) l = (Real.exp (-∑ i, y i) : ℂ) * 𝓕 f (WithLp.toLp 2 (GlobalTheory.HeckeTheta.dil (-y) (WithLp.ofLp l))) := by
  first | exact @GlobalTheory.HeckePoisson.Dilation.fourier_comp_dil | exact GlobalTheory.HeckePoisson.Dilation.fourier_comp_dil | (intros; apply GlobalTheory.HeckePoisson.Dilation.fourier_comp_dil <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierHarmonicMonomialMulGaussianComplexStatement
section
open NumberField MeasureTheory
open scoped RealInnerProductSpace FourierTransform
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourier_harmonicMonomial_mul_gaussian_complex : ∀ (k : ℤ) (l : ℂ), 𝓕 (fun w : ℂ => GlobalTheory.HeckeTheta.hmon k w * Complex.exp ((-2 * Real.pi * ‖w‖ ^ 2 : ℝ) : ℂ)) l = (1 / 2 : ℂ) * (-Complex.I) ^ k.natAbs * (GlobalTheory.HeckeTheta.hmon k (l / 2) * Complex.exp ((-2 * Real.pi * ‖l / 2‖ ^ 2 : ℝ) : ℂ)) := by
  first | exact @GlobalTheory.HeckeLemma.fourier_hmon_mul_gaussian | exact GlobalTheory.HeckeLemma.fourier_hmon_mul_gaussian | (intros; apply GlobalTheory.HeckeLemma.fourier_hmon_mul_gaussian <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierProdSingleCoordinateFunctionsStatement
section
open NumberField MeasureTheory
open scoped RealInnerProductSpace FourierTransform
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourier_prod_single_coordinate_functions : ∀ (I : Type) [Fintype I] (f : I → ℂ → ℂ), (∀ i, Integrable (f i)) → ∀ l : EuclideanSpace ℂ I, 𝓕 (fun w : EuclideanSpace ℂ I => ∏ i, f i (w i)) l = ∏ i, 𝓕 (f i) (l i) := by
  first | exact @GlobalTheory.fourier_prod_coord_complex | exact GlobalTheory.fourier_prod_coord_complex | (intros; apply GlobalTheory.fourier_prod_coord_complex <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GammaIntegralExpSubstitutionRealLineStatement
section
open NumberField MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gamma_integral_exp_substitution_real_line : ∀ (r : ℝ), 0 < r → ∀ w : ℂ, 0 < w.re → Integrable (fun t : ℝ => Complex.exp (w * t) * Complex.exp (-(2 * Real.pi * r * Real.exp t : ℝ))) ∧ ∫ t : ℝ, Complex.exp (w * t) * Complex.exp (-(2 * Real.pi * r * Real.exp t : ℝ)) = Complex.Gamma w * ((2 * Real.pi * r : ℝ) : ℂ) ^ (-w) := by
  first | exact @GlobalTheory.HeckeMellin.gamma_integral_exp_substitution | exact GlobalTheory.HeckeMellin.gamma_integral_exp_substitution | (intros; apply GlobalTheory.HeckeMellin.gamma_integral_exp_substitution <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussianHarmonicProductKernelContinuousBoundedStatement
section
open NumberField MeasureTheory
open scoped RealInnerProductSpace FourierTransform
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussianHarmonicProductKernel_continuous_bounded : ∀ (I : Type) [Fintype I] (n : I → ℤ), Continuous (fun w : EuclideanSpace ℂ I => GlobalTheory.HeckeTheta.gauss n (WithLp.ofLp w)) ∧ ∃ C : ℝ, ∀ w : EuclideanSpace ℂ I, ‖GlobalTheory.HeckeTheta.gauss n (WithLp.ofLp w)‖ ≤ C * Real.exp (-Real.pi * ‖w‖ ^ 2) := by
  first | exact @GlobalTheory.HeckeTheta.GaussBound.gauss_cont_bound | exact GlobalTheory.HeckeTheta.GaussBound.gauss_cont_bound | (intros; apply GlobalTheory.HeckeTheta.GaussBound.gauss_cont_bound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HZeroPullbackTwistBijective
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.ConnectedGlobalSections

variable {q : ℕ} [NeZero q] {i : ℤ}

theorem res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (y : Sec F U) :
    Sec.res (k ≫ g) y = Sec.res k (Sec.res g y) := by
  simp [Sec.res]

theorem res_nsmul {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (n : ℕ) (t : Sec F U) :
    Sec.res g (n • t) = n • Sec.res g t := map_nsmul ((F.obj.map g.op).hom) n t

theorem res_twGen {V U : Scheme.{0}} (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    Sec.res g (twGen i ζ) = twGen i (ζ.map g.appTop.hom) := (GlobalTheory.T.tateTwist_sections_locally_generated q i).2.2.2.1 V U g ζ

theorem prim_map_comp {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    (ζ.map g.appTop.hom).map k.appTop.hom = ζ.map (k ≫ g).appTop.hom := by
  apply Subtype.ext
  simp [Prim.map]
  rfl

theorem nsmul_eq_up {U : Scheme.{0}} (n : ℕ) (t : Sec (tw q i) U) : n • t = (ULift.up (n : ZMod q)) • t := by
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]
  rfl

theorem scalar_eq {U : Scheme.{0}} [Nonempty U] (ζ : Prim q Γ(U, ⊤)) (c d : ZMod q)
    (h : c.val • twGen i ζ = d.val • twGen i ζ) : c = d := by
  have h0 : (c - d).val • twGen i ζ = 0 := by
    rw [nsmul_eq_up, ZMod.natCast_zmod_val]
    rw [nsmul_eq_up, nsmul_eq_up, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at h
    have : (ULift.up (c - d) : ULift.{1} (ZMod q)) = ULift.up c - ULift.up d := rfl
    rw [this, sub_smul, h, sub_self]
  have hd := (GlobalTheory.T.tateTwist_sections_locally_generated q i).2.2.1 U ζ _ h0
  have hv : (c - d).val = 0 := Nat.eq_zero_of_dvd_of_lt hd (ZMod.val_lt _)
  exact sub_eq_zero.1 ((ZMod.val_eq_zero _).1 hv)

theorem q_nsmul {U : Scheme.{0}} (t : Sec (tw q i) U) (k : ℕ) : (q * k) • t = 0 := by
  rw [nsmul_eq_up]
  have : ((q * k : ℕ) : ZMod q) = 0 := by simp
  rw [this]
  exact zero_smul _ t

theorem sec_eq_nsmul (X : Scheme.{0}) [Nonempty X] (hX : ∀ s : Set X, IsClopen s → s = ∅ ∨ s = Set.univ)
    (ζ : Prim q Γ(X, ⊤)) (y : Sec (tw q i) X) : ∃ c : ℕ, y = c • twGen i ζ := by
  classical
  let P : ∀ V : Scheme.{0}, (V ⟶ X) → ℕ → Prop := fun V g c => Sec.res g y = c • twGen i (ζ.map g.appTop.hom)
  have hstab : ∀ c (V W : Scheme.{0}) (g : V ⟶ X) (k : W ⟶ V), P V g c → P W (k ≫ g) c := by
    intro c V W g k h
    simp only [P] at h ⊢
    rw [res_comp, h, res_nsmul, res_twGen, prim_map_comp]
  have hloc := (loc_iff_etale_affine_points X (fun V g => ∃ c, P V g c)
    (fun V W g k ⟨c, h⟩ => ⟨c, hstab c V W g k h⟩)).1 ((GlobalTheory.T.tateTwist_sections_locally_generated q i).2.1 X ζ y)
  let S : ZMod q → Set X := fun c =>
    {x | ∃ (V : Scheme.{0}) (g : V ⟶ X), IsAffine V ∧ Etale g ∧ x ∈ Set.range g ∧ P V g c.val}
  have hopen : ∀ c, IsOpen (S c) := by
    intro c
    rw [isOpen_iff_forall_mem_open]
    rintro x ⟨V, g, hV, hg, hx, hP⟩
    haveI := hg
    refine ⟨Set.range g, ?_, g.isOpenMap.isOpen_range, hx⟩
    rintro _ ⟨v, rfl⟩
    exact ⟨V, g, hV, hg, ⟨v, rfl⟩, hP⟩
  have hcov : ∀ x, ∃ c, x ∈ S c := by
    intro x
    obtain ⟨V, g, hV, hg, hx, n, hn⟩ := hloc x
    refine ⟨(n : ZMod q), V, g, hV, hg, hx, ?_⟩
    simp only [P] at hn ⊢
    rw [hn, nsmul_eq_up, nsmul_eq_up, ZMod.natCast_zmod_val]
  have hdisj : ∀ c d x, x ∈ S c → x ∈ S d → c = d := by
    rintro c d x ⟨V, g, -, -, ⟨v, rfl⟩, hP⟩ ⟨V', g', -, -, ⟨v', hv'⟩, hP'⟩
    obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := g) (g := g') v v' hv'.symm
    haveI : Nonempty ↥(Limits.pullback g g') := ⟨z⟩
    have h1 := hstab _ _ _ g (pullback.fst g g') hP
    have h2 := hstab _ _ _ g' (pullback.snd g g') hP'
    simp only [P] at h1 h2
    rw [pullback.condition] at h1
    exact scalar_eq _ c d (h1.symm.trans h2)
  obtain ⟨x0⟩ := ‹Nonempty X›
  obtain ⟨c0, hx0⟩ := hcov x0
  have hcompl : (S c0)ᶜ = ⋃ d ∈ ({c0}ᶜ : Set (ZMod q)), S d := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_singleton_iff, exists_prop]
    constructor
    · intro hx
      obtain ⟨d, hd⟩ := hcov x
      exact ⟨d, fun h => hx (h ▸ hd), hd⟩
    · rintro ⟨d, hd, hxd⟩ hx
      exact hd (hdisj d c0 x hxd hx)
  have hclopen : IsClopen (S c0) := by
    refine ⟨?_, hopen c0⟩
    rw [← isOpen_compl_iff, hcompl]
    exact isOpen_biUnion fun d _ => hopen d
  have huniv : S c0 = Set.univ := by
    rcases hX _ hclopen with h | h
    · rw [h] at hx0; exact absurd hx0 (Set.notMem_empty _)
    · exact h
  refine ⟨c0.val, (sec_ext_glue (ZMod q) (tw q i) X).1 _ _ ?_⟩
  refine (loc_iff_etale_affine_points X (fun _ g => Sec.res g y = Sec.res g (c0.val • twGen i ζ))
    (fun V W g k h => by rw [res_comp, res_comp, h])).2 ?_
  intro x
  obtain ⟨V, g, hV, hg, hx, hP⟩ : x ∈ S c0 := huniv ▸ Set.mem_univ x
  refine ⟨V, g, hV, hg, hx, ?_⟩
  rw [hP, res_nsmul, res_twGen]

end GlobalTheory.EtC.ConnectedGlobalSections

namespace GlobalTheory.EtC.ConnectedGlobalSections

theorem clopen_of_idem (B : Type) [CommRing B] (hB : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1)
    (s : Set (Spec (CommRingCat.of B))) (hs : IsClopen s) : s = ∅ ∨ s = Set.univ := by
  obtain ⟨e, he, h⟩ := PrimeSpectrum.isClopen_iff.1 (show IsClopen (X := PrimeSpectrum B) s from hs)
  rcases hB e he with rfl | rfl
  · left
    change (s : Set (PrimeSpectrum B)) = ∅
    rw [h]; simp <;> rfl
  · right
    change (s : Set (PrimeSpectrum B)) = Set.univ
    rw [h]; simp <;> rfl

end GlobalTheory.EtC.ConnectedGlobalSections

open GlobalTheory.EtC.ConnectedGlobalSections in

theorem GlobalTheory.EtC.h_zero_pull_bijective : ∀ (q : ℕ) [NeZero q] (A A' : Type) [CommRing A] [CommRing A'] (f : A →+* A'),
    IsUnit (q : A) → (∃ ζ : A, Polynomial.aeval ζ (Polynomial.cyclotomic q ℤ) = 0) → Nontrivial A' →
    (∀ e : A, IsIdempotentElem e → e = 0 ∨ e = 1) → (∀ e : A', IsIdempotentElem e → e = 0 ∨ e = 1) →
    ∀ i : ℤ, Function.Bijective (pull _ (spMap f) (tw q i) 0) := by
  intro q _ A A' _ _ f hq ⟨ζ0, hζ0⟩ hA' hidA hidA' i
  haveI : Nontrivial A := f.domain_nontrivial
  obtain ⟨-, e, he, -⟩ := GlobalTheory.T.etaleCohomology_negative_vanishing_degree_zero (ZMod q) (tw q i)
  let g : Spec (CommRingCat.of A') ⟶ Spec (CommRingCat.of A) := Spec.map (CommRingCat.ofHom f)
  haveI : Nonempty (Spec (CommRingCat.of A)) := inferInstance
  haveI : Nonempty (Spec (CommRingCat.of A')) := inferInstance
  let ζ : Prim q Γ(Spec (CommRingCat.of A), ⊤) :=
    Prim.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ⟨ζ0, hq, hζ0⟩
  have hres : Function.Bijective (Sec.res (F := tw q i) g) := by
    constructor
    · change Function.Injective ((tw q i).obj.map g.op).hom
      rw [injective_iff_map_eq_zero]
      intro y hy
      obtain ⟨c, rfl⟩ := sec_eq_nsmul _ (clopen_of_idem A hidA) ζ y
      have h0 : c • twGen i (ζ.map g.appTop.hom) = 0 := by
        rw [← res_twGen, ← res_nsmul]; exact hy
      obtain ⟨k, rfl⟩ := (GlobalTheory.T.tateTwist_sections_locally_generated q i).2.2.1 _ _ _ h0
      exact q_nsmul _ k
    · intro y
      obtain ⟨c, rfl⟩ := sec_eq_nsmul _ (clopen_of_idem A' hidA') (ζ.map g.appTop.hom) y
      exact ⟨c • twGen i ζ, by rw [res_nsmul, res_twGen]⟩
  have key : ∀ s, pull _ (spMap f) (tw q i) 0 (e _ s) = e _ (Sec.res g s) := fun s => he g s
  have hfun : ⇑(pull _ (spMap f) (tw q i) 0) = e _ ∘ Sec.res g ∘ (e _).symm := by
    funext x
    obtain ⟨s, rfl⟩ := (e _).surjective x
    simp [key]
  rw [hfun]
  exact (e _).bijective.comp (hres.comp (e _).symm.bijective)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasStrictFDerivAtDiagonalTorusZero
section
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.TorusFrame
open scoped ENNReal

namespace GlobalTheory.TorusFrame

theorem hasStrictFDerivAt_torus_zero (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ)) (x : Frame Ψ r) : HasStrictFDerivAt (fun θ : Ψ → Fin (r - 1) → ℝ => fun τ a b => (mat x τ * diagonal (fun c => Complex.exp (Complex.I * (angles (θ τ) c : ℂ))) * (mat x τ)⁻¹) a b) (torusDer x) 0 := by
  refine hasStrictFDerivAt_pi'' fun τ => hasStrictFDerivAt_pi'' fun a => hasStrictFDerivAt_pi'' fun b => ?_
  set A : Fin r → ((Ψ → Fin (r - 1) → ℝ) →L[ℝ] ℂ) := fun c =>
    Complex.ofRealCLM.comp ((ContinuousLinearMap.proj c).comp ((LinearMap.toContinuousLinearMap (anglesL r)).comp (ContinuousLinearMap.proj τ))) with hA
  have hAapp : ∀ c θ, A c θ = (angles (θ τ) c : ℂ) := fun c θ => rfl
  have hc : ∀ c : Fin r, HasStrictFDerivAt (fun θ : Ψ → Fin (r - 1) → ℝ => mat x τ a c * Complex.exp (Complex.I * (angles (θ τ) c : ℂ)) * (mat x τ)⁻¹ c b)
      (((mat x τ)⁻¹ c b) • (mat x τ a c • (Complex.exp (Complex.I * (angles ((0 : Ψ → Fin (r - 1) → ℝ) τ) c : ℂ)) • (Complex.I • A c)))) 0 := by
    intro c
    have h1 : HasStrictFDerivAt (fun θ : Ψ → Fin (r - 1) → ℝ => (angles (θ τ) c : ℂ)) (A c) 0 := (A c).hasStrictFDerivAt
    exact ((h1.const_mul Complex.I).cexp.const_mul (mat x τ a c)).mul_const ((mat x τ)⁻¹ c b)
  have hs := HasStrictFDerivAt.sum (u := Finset.univ) (fun c _ => hc c)
  refine (hs.congr_fderiv ?_).congr_of_eventuallyEq ?_
  · ext θ
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.proj_apply, torusDer_apply,
      ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, hAapp,
      angles_zero, Pi.zero_apply, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_smul, smul_eq_mul]
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  · refine Filter.Eventually.of_forall fun θ => ?_
    simp only [Finset.sum_apply]
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal]
end GlobalTheory.TorusFrame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasStrictFDerivAtMulCurvesMatrixGroupIdentityStatement
section
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasStrictFDerivAt_mul_curves_matrixGroup_identity : ∀ (ι : Type) [Fintype ι] (r : ℕ) (H : Subgroup (ι → GL (Fin r) ℂ)) (W₁ W₂ : Type) [NormedAddCommGroup W₁] [NormedSpace ℝ W₁] [NormedAddCommGroup W₂] [NormedSpace ℝ W₂] (σ : W₁ → H) (t : W₂ → H) (D₁ : W₁ →L[ℝ] (ι → Fin r → Fin r → ℂ)) (D₂ : W₂ →L[ℝ] (ι → Fin r → Fin r → ℂ)), σ 0 = 1 → t 0 = 1 → HasStrictFDerivAt (fun w => fun τ i j => ((((σ w : H) : ι → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) i j) D₁ 0 → HasStrictFDerivAt (fun w => fun τ i j => ((((t w : H) : ι → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) i j) D₂ 0 → HasStrictFDerivAt (fun w : W₁ × W₂ => fun τ i j => ((((σ w.1 * t w.2 : H) : ι → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) i j) (D₁.comp (ContinuousLinearMap.fst ℝ W₁ W₂) + D₂.comp (ContinuousLinearMap.snd ℝ W₁ W₂)) 0 := by
  first | exact @GlobalTheory.hasStrictFDerivAt_mul_curves_at_identity | exact GlobalTheory.hasStrictFDerivAt_mul_curves_at_identity | (intros; apply GlobalTheory.hasStrictFDerivAt_mul_curves_at_identity <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumIntegralThetaMellinInterchangeStatement
section
open NumberField MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_integral_theta_mellin_interchange : ∀ (I : Type) [Fintype I] (ι : Type) [Countable ι] (e : ι → I → ℂ) (a : ι → ℂ) (C : ℝ), (∀ j, ‖a j‖ ≤ C) → ∀ (n : I → ℤ) (s : ℂ) (p : (I → ℝ) → ℝ), Measurable p → (∀ y, 0 ≤ p y) → (∀ y, p y ≤ 1) → (∀ j, Integrable (GlobalTheory.HeckeMellin.term n s (e j))) → Summable (fun j => ∫ y, p y * ‖GlobalTheory.HeckeMellin.term n s (e j) y‖) → HasSum (fun j => a j * ∫ y, (p y : ℂ) * GlobalTheory.HeckeMellin.term n s (e j) y) (∫ y, (p y : ℂ) * GlobalTheory.HeckeTheta.theta e a n y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ))) := by
  first | exact @GlobalTheory.HeckeMellin.hasSum_integral_theta | exact GlobalTheory.HeckeMellin.hasSum_integral_theta | (intros; apply GlobalTheory.HeckeMellin.hasSum_integral_theta <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumIteratedComplexPartialDerivTermwiseStatement
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_iteratedComplexPartialDeriv_termwise : ∀ (I : Type) [Fintype I] [DecidableEq I] (Ξ : Type) (u : List I) (r : ℝ) (f : Ξ → (I → ℂ) → ℂ) (g : (I → ℂ) → ℂ) (M : Ξ → ℝ), 0 < r → Summable M → (∀ ξ, DifferentiableOn ℂ (f ξ) (Metric.ball 0 r)) → (∀ ξ, ∀ z ∈ Metric.ball (0 : I → ℂ) r, ‖f ξ z‖ ≤ M ξ) → (∀ z ∈ Metric.ball (0 : I → ℂ) r, HasSum (fun ξ ↦ f ξ z) (g z)) → HasSum (fun ξ ↦ iterD u (f ξ) 0) (iterD u g 0) := by
  first | exact @GlobalTheory.HilbFam.hasSum_iterD_termwise | exact GlobalTheory.HilbFam.hasSum_iterD_termwise | (intros; apply GlobalTheory.HilbFam.hasSum_iterD_termwise <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeIdealEuclideanLatticeIsZLatticeStatement
section
open NumberField MeasureTheory
open scoped RealInnerProductSpace FourierTransform
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeIdealEuclideanLattice_isZLattice : ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I] (φ : I → K →+* ℂ), GlobalTheory.CMVal.IsCMType φ → ∀ M : Ideal (𝓞 K), M ≠ ⊥ → ∃ _ : DiscreteTopology (GlobalTheory.HeckePoisson.lat φ M), IsZLattice ℝ (GlobalTheory.HeckePoisson.lat φ M) := by
  first | exact @GlobalTheory.HeckePoisson.lat_isZLattice | exact GlobalTheory.HeckePoisson.lat_isZLattice | (intros; apply GlobalTheory.HeckePoisson.lat_isZLattice <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeMellinGaussIntegrandUnitMulStatement
section
open NumberField MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeMellinGaussIntegrand_unit_mul : ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I] (φ : I → K →+* ℂ), GlobalTheory.CMVal.IsCMType φ → ∀ (n : I → ℤ) (s : ℂ) (u : (𝓞 K)ˣ) (α : K) (y : I → ℝ), GlobalTheory.HeckeMellin.term n s (GlobalTheory.HeckeTheta.emb φ (((u : 𝓞 K) : K) * α)) y = GlobalTheory.HeckeStrip.wt φ n ((u : 𝓞 K) : K) * GlobalTheory.HeckeMellin.term n s (GlobalTheory.HeckeTheta.emb φ α) (y + GlobalTheory.HeckeTheta.ulog φ u) := by
  first | exact @GlobalTheory.HeckeShift.term_unit_mul | exact GlobalTheory.HeckeShift.term_unit_mul | (intros; apply GlobalTheory.HeckeShift.term_unit_mul <;> assumption)
end

