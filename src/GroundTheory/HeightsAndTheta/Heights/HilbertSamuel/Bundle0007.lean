import Mathlib
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0006
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsCN

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.BergmanObjects
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ComplexConjugate ENNReal ContDiff

noncomputable section

variable {D : ℕ} {X : Type} [TopologicalSpace X]

structure HolLineBundle (A : FinHolAtlas D X) where

  g : Fin A.n → Fin A.n → X → ℂ
  holo : ∀ j k, A.HoloOn ((A.chart j).source ∩ (A.chart k).source) (g j k)
  ne_zero : ∀ j k, ∀ x ∈ (A.chart j).source ∩ (A.chart k).source, g j k x ≠ 0
  cocycle : ∀ j k l, ∀ x ∈ (A.chart j).source ∩ (A.chart k).source ∩ (A.chart l).source,
    g j l x = g j k x * g k l x

namespace HolLineBundle

variable {A : FinHolAtlas D X} (L : HolLineBundle A)

def sections (n : ℕ) : Submodule ℂ (Fin A.n → X → ℂ) where
  carrier := {f | (∀ j, A.HoloOn (A.chart j).source (f j)) ∧
    (∀ j k, ∀ x ∈ (A.chart j).source ∩ (A.chart k).source, f j x = L.g j k x ^ n * f k x) ∧
    ∀ j, ∀ x ∉ (A.chart j).source, f j x = 0}
  add_mem' := by
    rintro f f' ⟨hf, hc, hz⟩ ⟨hf', hc', hz'⟩
    refine ⟨fun j k => (hf j k).add (hf' j k), fun j k x hx => ?_, fun j x hx => ?_⟩
    · simp only [Pi.add_apply, hc j k x hx, hc' j k x hx]; ring
    · simp [hz j x hx, hz' j x hx]
  zero_mem' := by
    refine ⟨fun j k => ?_, fun j k x _ => by simp, fun j x _ => rfl⟩
    exact analyticOnNhd_const
  smul_mem' := by
    rintro c f ⟨hf, hc, hz⟩
    refine ⟨fun j k => analyticOnNhd_const.mul (hf j k), fun j k x hx => ?_, fun j x hx => ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul, hc j k x hx]; ring
    · simp [hz j x hx]

end HolLineBundle

structure Weight {A : FinHolAtlas D X} (L : HolLineBundle A) where

  φ : Fin A.n → X → ℝ
  smooth : ∀ j, A.SmoothOn (A.chart j).source (φ j)
  compat : ∀ j k, ∀ x ∈ (A.chart j).source ∩ (A.chart k).source,
    φ j x = φ k x + Real.log (‖L.g j k x‖ ^ 2)

namespace Weight

variable {A : FinHolAtlas D X} {L : HolLineBundle A}

def IsSemipositive (W : Weight L) : Prop :=
  ∀ j, ∀ y ∈ (A.chart j).target, ∀ w : Fin D → ℂ, 0 ≤ levi (W.φ j ∘ (A.chart j).symm) y w

def lerp (W₀ W₁ : Weight L) (t : ℝ) : Weight L where
  φ j x := W₀.φ j x + t * (W₁.φ j x - W₀.φ j x)
  smooth j k := (W₀.smooth j k).add (contDiffOn_const.mul ((W₁.smooth j k).sub (W₀.smooth j k)))
  compat j k x hx := by rw [W₀.compat j k x hx, W₁.compat j k x hx]; ring

def diff (W₁ W₀ : Weight L) (x : X) : ℝ :=
  W₁.φ (chartIdx A x) x - W₀.φ (chartIdx A x) x

theorem diff_eq (W₁ W₀ : Weight L) (j : Fin A.n) {x : X} (hx : x ∈ (A.chart j).source) :
    diff W₁ W₀ x = W₁.φ j x - W₀.φ j x := by
  have hi : x ∈ (A.chart (chartIdx A x)).source := Classical.choose_spec (A.cover x)
  rw [diff, W₁.compat (chartIdx A x) j x ⟨hi, hx⟩, W₀.compat (chartIdx A x) j x ⟨hi, hx⟩]
  ring

end Weight

structure SmoothVolume [MeasurableSpace X] (A : FinHolAtlas D X) where

  μ : Measure X
  isProb : IsProbabilityMeasure μ

  dens : Fin A.n → (Fin D → ℂ) → ℝ
  smooth : ∀ j, ContDiffOn ℝ ∞ (dens j) (A.chart j).target
  pos : ∀ j, ∀ y ∈ (A.chart j).target, 0 < dens j y
  chart_lintegral : ∀ j (g : X → ℝ≥0∞), Measurable g →
    ∫⁻ x in (A.chart j).source, g x ∂μ =
      ∫⁻ y in (A.chart j).target, g ((A.chart j).symm y) * ENNReal.ofReal (dens j y)

variable {A : FinHolAtlas D X} {L : HolLineBundle A}

def ptNormSq (W : Weight L) (n : ℕ) (s : Fin A.n → X → ℂ) (x : X) : ℝ :=
  ‖s (chartIdx A x) x‖ ^ 2 * Real.exp (-(n : ℝ) * W.φ (chartIdx A x) x)

variable [MeasurableSpace X]

def sectionL2NormSq (W : Weight L) (dV : SmoothVolume A) (n : ℕ) (s : Fin A.n → X → ℂ) : ℝ :=
  ∫ x, ptNormSq W n s x ∂dV.μ

def bergman (W : Weight L) (dV : SmoothVolume A) (V : Submodule ℂ (Fin A.n → X → ℂ)) (n : ℕ)
    (x : X) : ℝ :=
  ⨆ s : V, ptNormSq W n (s : Fin A.n → X → ℂ) x / sectionL2NormSq W dV n s

def chernTopDens (W : Weight L) (j : Fin A.n) (y : Fin D → ℂ) : ℝ :=
  (D.factorial : ℝ) * ((((1 / Real.pi : ℝ) : ℂ) • hessC (W.φ j ∘ (A.chart j).symm) y).det).re

def bergmanDens (W : Weight L) (dV : SmoothVolume A) (x : X) : ℝ :=
  chernTopDens W (chartIdx A x) (A.chart (chartIdx A x) x) /
    ((D.factorial : ℝ) * dV.dens (chartIdx A x) (A.chart (chartIdx A x) x))

def gram (W : Weight L) (dV : SmoothVolume A) (n : ℕ) {ι : Type*} (e : ι → Fin A.n → X → ℂ) :
    Matrix ι ι ℂ :=
  Matrix.of fun a b => ∫ x, e a (chartIdx A x) x * conj (e b (chartIdx A x) x) *
    ((Real.exp (-(n : ℝ) * W.φ (chartIdx A x) x) : ℝ) : ℂ) ∂dV.μ

def chiGram (W : Weight L) (dV : SmoothVolume A) (n : ℕ) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι → Fin A.n → X → ℂ) : ℝ :=
  -(1 / 2) * Real.log (gram W dV n e).det.re

end

noncomputable def gaussDiscMass (lam R : ℝ) : ℝ :=
  if lam = 0 then Real.pi * R ^ 2 else Real.pi * (1 - Real.exp (-lam * R ^ 2)) / lam

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.GenericComplexPoint
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Cardinal

noncomputable section

theorem exists_ringHom_complex_of_charZero (F : Type) [Field F] [CharZero F] (hF : #F ≤ 𝔠) :
    Nonempty (F →+* ℂ) := by
  let M := MvPolynomial ℂ F
  let E := FractionRing M
  let L := AlgebraicClosure E
  have : CharZero M := charZero_of_injective_algebraMap (R := F) (MvPolynomial.C_injective _ _)
  have : CharZero E := charZero_of_injective_algebraMap (R := M) (IsFractionRing.injective M E)
  have : CharZero L := charZero_of_injective_algebraMap (R := E) (algebraMap E L).injective
  have hM : #M ≤ 𝔠 := by
    refine MvPolynomial.cardinalMk_le_max.trans ?_
    rw [mk_complex]
    exact max_le (max_le hF le_rfl) aleph0_le_continuum
  have hE : #E = #M := Cardinal.mk_fractionRing M
  have hL : #L ≤ 𝔠 :=
    (Algebra.IsAlgebraic.cardinalMk_le_max E L).trans (max_le (hE ▸ hM) aleph0_le_continuum)
  have hinj : Function.Injective (fun c : ℂ => algebraMap E L (algebraMap M E (X c))) :=
    (algebraMap E L).injective.comp ((IsFractionRing.injective M E).comp MvPolynomial.X_injective)
  have hLc : #L = #ℂ :=
    le_antisymm (hL.trans_eq mk_complex.symm) (Cardinal.mk_le_of_injective hinj)
  obtain ⟨σ⟩ := IsAlgClosed.ringEquiv_of_equiv_of_charZero (K := L) (L := ℂ)
    (by rw [hLc, mk_complex]; exact aleph0_lt_continuum) (Cardinal.eq.1 hLc)
  exact ⟨σ.toRingHom.comp ((algebraMap E L).comp ((algebraMap M E).comp C))⟩

theorem exists_mcPts_not_mem_mcPts {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P J : Ideal (MRing ι)} {d : ℕ} (hP : IsArithVar P d) (hJ : ¬ J ≤ P) :
    ∃ z, z ∈ mcPts P ∧ z ∉ mcPts J := by
  obtain ⟨_, ⟨hprime, -, hrel⟩, hhor, -⟩ := hP
  obtain ⟨g, hgJ, hgP⟩ := SetLike.not_le_iff_exists.mp hJ
  have := hprime
  let Q := MRing ι ⧸ P
  let F := FractionRing Q
  have hQ : Function.Injective (algebraMap ℤ Q) := by
    have e : algebraMap ℤ Q = (Ideal.Quotient.mk P).comp C := RingHom.ext_int _ _
    rw [e, injective_iff_map_eq_zero]
    intro n hn
    have hn0 : (C n : MRing ι) ∈ P := Ideal.Quotient.eq_zero_iff_mem.mp hn
    have hn' : n ∈ P.comap (C : ℤ →+* MRing ι) := hn0
    rw [IsHorizontal] at hhor
    rw [hhor] at hn'
    exact (Ideal.mem_bot).mp hn'
  have : CharZero Q := charZero_of_injective_algebraMap hQ
  have : CharZero F := charZero_of_injective_algebraMap (R := Q) (IsFractionRing.injective Q F)
  have hcard : #F ≤ 𝔠 := by
    rw [Cardinal.mk_fractionRing]
    refine (Cardinal.mk_le_of_surjective (Ideal.Quotient.mk_surjective (I := P))).trans ?_
    refine MvPolynomial.cardinalMk_le_max.trans ?_
    exact max_le (max_le (mk_int.le.trans aleph0_le_continuum)
      (Cardinal.mk_le_aleph0.trans aleph0_le_continuum)) aleph0_le_continuum
  obtain ⟨ψ⟩ := exists_ringHom_complex_of_charZero F hcard
  let φ : MRing ι →+* ℂ := (ψ.comp (algebraMap Q F)).comp (Ideal.Quotient.mk P)
  have hker : ∀ f, φ f = 0 ↔ f ∈ P := by
    intro f
    have hi : Function.Injective (ψ.comp (algebraMap Q F)) :=
      ψ.injective.comp (IsFractionRing.injective Q F)
    rw [show φ f = (ψ.comp (algebraMap Q F)) (Ideal.Quotient.mk P f) from rfl,
      map_eq_zero_iff _ hi, Ideal.Quotient.eq_zero_iff_mem]
  let z : (Σ k, ι k) → ℂ := fun p => φ (X p)
  have hev : ∀ f : MRing ι, eval z (map (Int.castRingHom ℂ) f) = φ f := by
    intro f
    have h : (eval z).comp (map (Int.castRingHom ℂ)) = φ := by
      refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
      · exact RingHom.congr_fun
          (RingHom.ext_int (((eval z).comp (map (Int.castRingHom ℂ))).comp C) (φ.comp C)) r
      · simp [z]
    exact RingHom.congr_fun h f
  refine ⟨z, ⟨fun k => ?_, fun f hf => ?_⟩, fun hz => ?_⟩
  · obtain ⟨i, hi⟩ := hrel k
    exact ⟨i, fun h => hi ((hker _).mp h)⟩
  · rw [hev]
    exact (hker f).mpr hf
  · exact hgP ((hker g).mp (by rw [← hev]; exact hz.2 g hgJ))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PConjIntNum
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial NumbersDVR

noncomputable section

namespace ConjIntNum

variable {K : Type} [DecidableEq K] {ι : K → Type} {F : Type} [Field F]

theorem isWeightedHomogeneous_map {σ M : Type*} [AddCommMonoid M] (w : σ → M) (τ : F →+* F)
    {f : MvPolynomial σ F} {m : M} (hf : IsWeightedHomogeneous w f m) :
    IsWeightedHomogeneous w (MvPolynomial.map τ f) m := by
  intro d hd
  rw [coeff_map] at hd
  exact hf fun h => hd (by rw [h, map_zero])

def quotEquiv (τ : F ≃+* F) (J : Ideal (MRing ι F)) :
    (MRing ι F ⧸ J) ≃+* (MRing ι F ⧸ J.map (MvPolynomial.map (τ : F →+* F))) :=
  Ideal.quotientEquiv J _ (MvPolynomial.mapEquiv _ τ) (by
    congr 1)

omit [DecidableEq K] in
theorem quotEquiv_mk (τ : F ≃+* F) (J : Ideal (MRing ι F)) (f : MRing ι F) :
    quotEquiv τ J (Ideal.Quotient.mk J f) = Ideal.Quotient.mk _ (MvPolynomial.map (τ : F →+* F) f) :=
  rfl

theorem mem_gradedPiece_iff (τ : F ≃+* F) (J : Ideal (MRing ι F)) (m : K → ℕ) (x : MRing ι F ⧸ J) :
    quotEquiv τ J x ∈ gradedPiece (J.map (MvPolynomial.map (τ : F →+* F))) m ↔ x ∈ gradedPiece J m := by
  simp only [gradedPiece, Submodule.mem_map, mem_weightedHomogeneousSubmodule]
  constructor
  · rintro ⟨g, hg, hgx⟩
    refine ⟨MvPolynomial.map (τ.symm : F →+* F) g, isWeightedHomogeneous_map _ _ hg, ?_⟩
    have := congrArg (quotEquiv τ J).symm hgx
    rw [RingEquiv.symm_apply_apply] at this
    rw [← this]
    rfl
  · rintro ⟨f, hf, rfl⟩
    exact ⟨MvPolynomial.map (τ : F →+* F) f, isWeightedHomogeneous_map _ _ hf, rfl⟩

def pieceEquiv (τ : F ≃+* F) (J : Ideal (MRing ι F)) (m : K → ℕ) :
    gradedPiece J m ≃+ gradedPiece (J.map (MvPolynomial.map (τ : F →+* F))) m where
  toFun x := ⟨quotEquiv τ J x, (mem_gradedPiece_iff τ J m x).2 x.2⟩
  invFun y := ⟨(quotEquiv τ J).symm y,
    (mem_gradedPiece_iff τ J m _).1 (by rw [RingEquiv.apply_symm_apply]; exact y.2)⟩
  left_inv x := Subtype.ext (RingEquiv.symm_apply_apply _ _)
  right_inv y := Subtype.ext (RingEquiv.apply_symm_apply _ _)
  map_add' x y := Subtype.ext (map_add _ _ _)

omit [DecidableEq K] in

theorem quotEquiv_smul (τ : F ≃+* F) (J : Ideal (MRing ι F)) (c : F) (x : MRing ι F ⧸ J) :
    quotEquiv τ J (c • x) = τ c • quotEquiv τ J x := by
  have hs : ∀ (I : Ideal (MRing ι F)) (a : F) (g : MRing ι F),
      a • Ideal.Quotient.mk I g = Ideal.Quotient.mk I (C a * g) := fun I a g => by
    rw [← smul_eq_C_mul]
    exact (map_smul (Ideal.Quotient.mkₐ F I) a g).symm
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [hs, quotEquiv_mk, quotEquiv_mk, hs, map_mul, map_C]
  rfl

theorem finrank_gradedPiece (τ : F ≃+* F) (J : Ideal (MRing ι F)) (m : K → ℕ) :
    Module.finrank F (gradedPiece (J.map (MvPolynomial.map (τ : F →+* F))) m) =
      Module.finrank F (gradedPiece J m) := by
  have h := rank_eq_of_equiv_equiv (τ : F → F) (pieceEquiv τ J m) τ.bijective
    (fun c x => Subtype.ext (quotEquiv_smul τ J c x))
  simp only [Module.finrank, h]

theorem hilbFn_map (τ : F ≃+* F) (J : Ideal (MRing ι F)) :
    hilbFn (J.map (MvPolynomial.map (τ : F →+* F))) = hilbFn J := by
  funext m
  unfold hilbFn
  split_ifs
  · rw [finrank_gradedPiece]
  · rfl

theorem proof : ConjIntNum.Statement := by
  intro K _ ι F _ τ J n bs
  unfold NumbersDVR.intNum
  rw [hilbFn_map]

end ConjIntNum

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PHilbertModule
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

universe u v

theorem HilbertModule.proof (hMP : ModulesFromPrimes.Statement.{u, v})
    (hHP : HilbertPrime.Statement.{u}) : HilbertModule.Statement.{u, v} :=
  fun d => hMP d fun e _ => hHP e

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLeviCompHol
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

noncomputable section

theorem LeviCompHol.proof : LeviCompHol.Statement := by
  intro E F _ _ g φ x w hg hφ
  have hgev : ∀ᶠ y in 𝓝 x, AnalyticAt ℂ g y := hg.eventually_analyticAt
  have hfdg : ∀ᶠ y in 𝓝 x, fderiv ℝ g y = (fderiv ℂ g y).restrictScalars ℝ := by
    filter_upwards [hgev] with y hy
    exact hy.differentiableAt.fderiv_restrictScalars ℝ
  have hgC : ContDiffAt ℂ 2 g x := hg.contDiffAt
  have hgR : ContDiffAt ℝ 2 g x := hgC.restrict_scalars ℝ
  have hgd : DifferentiableAt ℝ g x := hgR.differentiableAt (by norm_num)
  have hd2 : DifferentiableAt ℝ (fderiv ℝ g) x :=
    (hgR.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hGw : ∀ v, fderiv ℝ g x v = fderiv ℂ g x v := fun v => by rw [hfdg.self_of_nhds]; rfl
  have hGI : ∀ v, fderiv ℝ g x (Complex.I • v) = Complex.I • fderiv ℝ g x v := fun v => by
    rw [hGw, hGw]; exact (fderiv ℂ g x).map_smul _ _

  have hG2I : ∀ u v, fderiv ℝ (fderiv ℝ g) x u (Complex.I • v) =
      Complex.I • fderiv ℝ (fderiv ℝ g) x u v := by
    intro u v
    have hA : HasFDerivAt (fun y => fderiv ℝ g y (Complex.I • v))
        ((ContinuousLinearMap.apply ℝ (F → ℂ) (Complex.I • v)).comp (fderiv ℝ (fderiv ℝ g) x)) x :=
      (ContinuousLinearMap.apply ℝ (F → ℂ) (Complex.I • v)).hasFDerivAt.comp x hd2.hasFDerivAt
    have hB : HasFDerivAt (fun y => Complex.I • fderiv ℝ g y v)
        (Complex.I • (ContinuousLinearMap.apply ℝ (F → ℂ) v).comp (fderiv ℝ (fderiv ℝ g) x)) x :=
      ((ContinuousLinearMap.apply ℝ (F → ℂ) v).hasFDerivAt.comp x hd2.hasFDerivAt).const_smul Complex.I
    have hAB : (fun y => Complex.I • fderiv ℝ g y v) =ᶠ[𝓝 x] fun y => fderiv ℝ g y (Complex.I • v) := by
      filter_upwards [hfdg] with y hy
      rw [hy]; exact ((fderiv ℂ g y).map_smul _ _).symm
    have h := congrArg (fun L => L u) ((hB.congr_of_eventuallyEq hAB.symm).unique hA)
    simpa using h.symm
  have hsymm : IsSymmSndFDerivAt ℝ g x := hgR.isSymmSndFDerivAt (by simp)
  have hG2II : fderiv ℝ (fderiv ℝ g) x (Complex.I • w) (Complex.I • w) =
      -fderiv ℝ (fderiv ℝ g) x w w := by
    rw [hG2I, hsymm (Complex.I • w) w, hG2I, smul_smul, Complex.I_mul_I, neg_one_smul]
  have hev : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2 φ (g y) :=
    hgd.continuousAt.tendsto.eventually (hφ.eventually (by simp))
  have hfd : fderiv ℝ (fun y => φ (g y)) =ᶠ[𝓝 x]
      fun y => (fderiv ℝ φ (g y)).comp (fderiv ℝ g y) := by
    filter_upwards [hev, hgev] with y hy hy'
    exact fderiv_comp y (hy.differentiableAt (by norm_num)) (hy'.differentiableAt.restrictScalars ℝ)
  have hdφ : DifferentiableAt ℝ (fderiv ℝ φ) (g x) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hc : HasFDerivAt (fun y => fderiv ℝ φ (g y))
      ((fderiv ℝ (fderiv ℝ φ) (g x)).comp (fderiv ℝ g x)) x :=
    hdφ.hasFDerivAt.comp x hgd.hasFDerivAt
  have hD := hc.clm_comp hd2.hasFDerivAt
  unfold leviForm
  rw [hfd.fderiv_eq, hD.fderiv]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply, hGI, hG2II, map_neg, hGw]
  ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLeviLogFlat
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

noncomputable section

variable {J : Type} [Fintype J]

theorem fderiv_fderiv_add_apply {f g : (J → ℂ) → ℝ} {z : J → ℂ} (hf : ContDiffAt ℝ 2 f z)
    (hg : ContDiffAt ℝ 2 g z) (v : J → ℂ) :
    fderiv ℝ (fderiv ℝ (fun y => f y + g y)) z v v =
      fderiv ℝ (fderiv ℝ f) z v v + fderiv ℝ (fderiv ℝ g) z v v := by
  have hf' : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) z) z :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hg' : HasFDerivAt (fderiv ℝ g) (fderiv ℝ (fderiv ℝ g) z) z :=
    ((hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hev : fderiv ℝ (fun y => f y + g y) =ᶠ[𝓝 z] fun y => fderiv ℝ f y + fderiv ℝ g y := by
    filter_upwards [hf.eventually (by simp), hg.eventually (by simp)] with y hy1 hy2
    exact ((hy1.differentiableAt (by norm_num)).hasFDerivAt.add
      (hy2.differentiableAt (by norm_num)).hasFDerivAt).fderiv
  have h2 : HasFDerivAt (fun y => fderiv ℝ f y + fderiv ℝ g y)
      (fderiv ℝ (fderiv ℝ f) z + fderiv ℝ (fderiv ℝ g) z) z := hf'.add hg'
  rw [hev.fderiv_eq, h2.fderiv]
  rfl

theorem fderiv_fderiv_log_apply {F : (J → ℂ) → ℝ} {z : J → ℂ} (hF : ContDiffAt ℝ 2 F z) (hpos : 0 < F z)
    (v : J → ℂ) :
    fderiv ℝ (fderiv ℝ (fun x => Real.log (F x))) z v v =
      fderiv ℝ (fderiv ℝ F) z v v / F z - (fderiv ℝ F z v) ^ 2 / F z ^ 2 := by
  have hpos' : ∀ᶠ y in 𝓝 z, 0 < F y := continuousAt_const.eventually_lt hF.continuousAt hpos
  have hev : fderiv ℝ (fun x => Real.log (F x)) =ᶠ[𝓝 z] fun y => (F y)⁻¹ • fderiv ℝ F y := by
    filter_upwards [hF.eventually (by simp), hpos'] with y hy hy'
    exact ((hy.differentiableAt (by norm_num)).hasFDerivAt.log hy'.ne').fderiv
  have hH : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) z) z :=
    ((hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hinv : HasFDerivAt (fun y => (F y)⁻¹)
      ((ContinuousLinearMap.toSpanSingleton ℝ (-(F z ^ 2)⁻¹)).comp (fderiv ℝ F z)) z :=
    (hasFDerivAt_inv hpos.ne').comp z (hF.differentiableAt (by norm_num)).hasFDerivAt
  have hP := hinv.fun_smul hH
  rw [hev.fderiv_eq, hP.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply]
  field_simp
  ring

theorem leviForm_log {F : (J → ℂ) → ℝ} {z : J → ℂ} (hF : ContDiffAt ℝ 2 F z) (hpos : 0 < F z) (w : J → ℂ) :
    leviForm (fun x => Real.log (F x)) z w =
      leviForm F z w / F z - ((fderiv ℝ F z w) ^ 2 + (fderiv ℝ F z (Complex.I • w)) ^ 2) / (4 * F z ^ 2) := by
  unfold leviForm
  rw [fderiv_fderiv_log_apply hF hpos, fderiv_fderiv_log_apply hF hpos]
  have : F z ≠ 0 := hpos.ne'
  field_simp
  ring

theorem LeviLogFlat.proof : LeviLogFlat.Statement := by
  intro J _ P u z w hP hu hpos hu0 hdw hdiw hlevi
  have hF : ContDiffAt ℝ 2 (fun x => P x + u x) z := hP.add hu
  have hFpos : 0 < P z + u z := by rw [hu0, add_zero]; exact hpos
  have hd : ∀ v, fderiv ℝ (fun x => P x + u x) z v = fderiv ℝ P z v + fderiv ℝ u z v := by
    intro v
    have h2 : HasFDerivAt (fun x => P x + u x) (fderiv ℝ P z + fderiv ℝ u z) z :=
      (hP.differentiableAt (by norm_num)).hasFDerivAt.add (hu.differentiableAt (by norm_num)).hasFDerivAt
    rw [h2.fderiv]
    rfl
  have hL : leviForm (fun x => P x + u x) z w = leviForm P z w + leviForm u z w := by
    unfold leviForm
    rw [fderiv_fderiv_add_apply hP hu, fderiv_fderiv_add_apply hP hu]
    ring
  rw [leviForm_log hF hFpos, leviForm_log hP hpos, hL, hlevi, hd, hd, hdw, hdiw, hu0]
  simp

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsComplexFormsOnPoints
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def ComplexFormsOnPoints.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)),
    P.IsPrime → IsRelevant P →
    ∀ F : MvPolynomial (Σ k, ι k) ℂ, (∀ z ∈ mcPts P, eval z F = 0) →
      F ∈ P.map (MvPolynomial.map (Int.castRingHom ℂ))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsDegLTGrowth
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open GroundTheory.Heights₂.Heights.NumbersDVR

def DegLTGrowth.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (n : ℕ) (g : (K → ℤ) → ℤ), DegLT g n →
    ∃ (a₀ : ℕ) (C : ℝ), ∀ a : K → ℕ, (∀ k, a₀ ≤ a k) →
      |(g (fun k => (a k : ℤ)) : ℝ)| ≤ C * ((∑ k, (a k : ℝ)) + 1) ^ ((n : ℝ) - 1)

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

