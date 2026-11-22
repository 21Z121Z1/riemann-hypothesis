import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2250
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0653
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1996
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedSectionExponentShift
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0035
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0036
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0185
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1607
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2284
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2225
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatVectorThreeStepsConjugatePlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2183
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2285
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2240
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2179
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2248
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentHaarRealSUOfMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianHaarIndependentOfOrthonormalFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1951
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0065
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0126
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.MuCardLeTwo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2261
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2191
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2286
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2292
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSectionFrameInvariance
section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

open Formalism.L2.LamCM GlobalTheory.Frames

noncomputable section

namespace GlobalTheory.FlatGL

theorem evalFr_update_line {K : Type} [Field K] {B : Type} [DecidableEq B] {m : B → ℕ}
    (G : MvPolynomial (FrVar m) K) (X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) K) (b : B)
    (A₀ D : Matrix (Fin (m b)) (Fin (m b)) K) :
    ∃ p : Polynomial K, ∀ x : K, evalFr G (Function.update X b (A₀ + x • D)) = p.eval x := by
  classical
  let α : ∀ b, Matrix (Fin (m b)) (Fin (m b)) K := Function.update X b A₀
  let β : ∀ b, Matrix (Fin (m b)) (Fin (m b)) K := Function.update (fun _ => 0) b D
  have hl : ∀ x : K, Function.update X b (A₀ + x • D) = fun b' => α b' + x • β b' := by
    intro x
    funext b'
    by_cases h : b' = b
    · subst h; simp [α, β]
    · simp [α, β, Function.update_of_ne h]
  refine ⟨MvPolynomial.aeval (fun v : FrVar m => Polynomial.C (α v.1 v.2.2 v.2.1) +
    Polynomial.C (β v.1 v.2.2 v.2.1) * Polynomial.X) G, fun x => ?_⟩
  have key : ∀ (a c : FrVar m → K) (P : MvPolynomial (FrVar m) K),
      MvPolynomial.eval (fun v => a v + x * c v) P =
        (MvPolynomial.aeval (fun v => Polynomial.C (a v) + Polynomial.C (c v) * Polynomial.X) P).eval x := by
    intro a c P
    induction P using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => rw [map_add, map_add, Polynomial.eval_add, hp, hq]
    | mul_X p v hp =>
      rw [map_mul, map_mul, Polynomial.eval_mul, hp]
      simp only [MvPolynomial.aeval_X, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X, MvPolynomial.eval_X]
      ring
  rw [hl, ← key]
  rfl

end GlobalTheory.FlatGL

namespace GlobalTheory.FlatGL

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def wr {K : Type} [Field K] (τ : Psi H) (δ : (E →+* ℂ) → K) : K :=
  δ τ.1 / ((∏ b, δ b) * δ (conjEmb τ.1))

def hfun (Dw : Datum H) {K : Type} [Field K] (τ : Psi H) (G : MvPolynomial (FrVar Dw.mult) K)
    (X : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K) : K :=
  wr τ (fun b => (X b).det) * evalFr G X

variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

section Fixed

open Classical

variable {k : Type} [Field k] [Algebra c.F k] (τ : Psi H) {f : Rul Xo c} (y₀ : FrPt Xo c k)
  (G : MvPolynomial (FrVar Dw.mult) k)

theorem hfun_eq
    (hGY : ∀ (y' : FrPt Xo c k) (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) k),
      (∀ b, (Y b).det ≠ 0) → FrChg (fun b => (Y b).transpose) 1 y₀ y' → (∏ b, (Y b).det) * evR Xo c f y' = evalFr G Y)
    (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) k) (hY : ∀ b, (Y b).det ≠ 0) (y' : FrPt Xo c k)
    (h : FrChg (fun b => (Y b).transpose) 1 y₀ y') :
    hfun Dw τ G Y = evR Xo c f y' * (Y τ.1).det / (Y (conjEmb τ.1)).det := by
  have hD : (∏ b, (Y b).det) ≠ 0 := Finset.prod_ne_zero_iff.2 fun b _ => hY b
  have h2 := hY (conjEmb τ.1)
  unfold hfun wr
  rw [← hGY y' Y hY h]
  field_simp

theorem hfun_upper (hf : f ∈ secZ Xo c (exOf Dw (flatWt Dw τ) 0))
    (hGY : ∀ (y' : FrPt Xo c k) (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) k),
      (∀ b, (Y b).det ≠ 0) → FrChg (fun b => (Y b).transpose) 1 y₀ y' → (∏ b, (Y b).det) * evR Xo c f y' = evalFr G Y)
    (X : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) k) (hX : ∀ b, (X b).det ≠ 0) (b : E →+* ℂ)
    (T : Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) k) (hT : T.det ≠ 0) (htri : T.BlockTriangular id) :
    hfun Dw τ G (Function.update X b (X b * T)) = hfun Dw τ G X := by
  classical
  let Tf : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) k := Function.update (fun _ => 1) b T
  have hTb : Tf b = T := Function.update_self ..
  have hTo : ∀ b', b' ≠ b → Tf b' = 1 := fun b' h => Function.update_of_ne h ..
  have hTtri : ∀ b', (Tf b').BlockTriangular id := by
    intro b'
    by_cases h : b' = b
    · subst h; rw [hTb]; exact htri
    · rw [hTo b' h]; exact Matrix.blockTriangular_one
  have hTd : ∀ b', (Tf b').det ≠ 0 := by
    intro b'
    by_cases h : b' = b
    · subst h; rw [hTb]; exact hT
    · rw [hTo b' h]; simp
  have hup : Function.update X b (X b * T) = fun b' => X b' * Tf b' := by
    funext b'
    by_cases h : b' = b
    · subst h; rw [hTb, Function.update_self]
    · rw [hTo b' h, Function.update_of_ne h, _root_.mul_one]
  obtain ⟨z₁, h₁, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c k y₀ (fun b => (X b).transpose) 1
    (fun b' => by rw [Matrix.det_transpose]; exact (hX b').isUnit)
  obtain ⟨z₂, h₂, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c k z₁ (fun b => (Tf b).transpose) 1
    (fun b' => by rw [Matrix.det_transpose]; exact (hTd b').isUnit)
  rw [Units.val_one] at h₁ h₂
  have h₃ := (GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c k y₀ z₁ z₂).2 _ _ _ _ h₁ h₂
  simp only [← Matrix.transpose_mul, _root_.mul_one] at h₃
  have hXT : ∀ b', (X b' * Tf b').det ≠ 0 := fun b' => by rw [Matrix.det_mul]; exact mul_ne_zero (hX b') (hTd b')
  have e₁ := hfun_eq τ y₀ G hGY X hX z₁ h₁
  have e₂ := hfun_eq τ y₀ G hGY (fun b' => X b' * Tf b') hXT z₂ h₃
  have e₃ := GlobalTheory.FlatFrameLaw.evR_flat_frChg τ hf (fun σ => (Tf σ).transpose) 1 z₁ z₂ h₂
    (fun σ i j hij => hTtri σ hij) (fun σ => by rw [Matrix.det_transpose]; exact (hTd σ).isUnit) one_ne_zero
  rw [hup, e₂, e₁, e₃]
  simp only [Matrix.det_transpose, Matrix.det_mul]
  have a1 := hTd τ.1
  have a2 := hTd (conjEmb τ.1)
  have a3 := hX (conjEmb τ.1)
  field_simp

theorem hfun_update_one [Infinite k] (hf : f ∈ secZ Xo c (exOf Dw (flatWt Dw τ) 0))
    (hGY : ∀ (y' : FrPt Xo c k) (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) k),
      (∀ b, (Y b).det ≠ 0) → FrChg (fun b => (Y b).transpose) 1 y₀ y' → (∏ b, (Y b).det) * evR Xo c f y' = evalFr G Y)
    (X : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) k) (hX : ∀ b, (X b).det ≠ 0) (b : E →+* ℂ) :
    hfun Dw τ G X = hfun Dw τ G (Function.update X b 1) := by
  have hψ : ∀ A : Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) k, A.det ≠ 0 →
      hfun Dw τ G (Function.update X b A) =
        wr τ (Function.update (fun b' => (X b').det) b A.det) * evalFr G (Function.update X b A) := by
    intro A _
    unfold hfun
    congr 2
    funext b'
    by_cases h : b' = b
    · subst h; simp
    · simp [Function.update_of_ne h]
  have hT : ∀ A T : Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) k, A.det ≠ 0 → T.det ≠ 0 → T.BlockTriangular id →
      hfun Dw τ G (Function.update X b (A * T)) = hfun Dw τ G (Function.update X b A) := by
    intro A T hA hT htri
    have hX' : ∀ b', (Function.update X b A b').det ≠ 0 := by
      intro b'
      by_cases h : b' = b
      · subst h; simpa using hA
      · rw [Function.update_of_ne h]; exact hX b'
    have := hfun_upper τ y₀ G hf hGY (Function.update X b A) hX' b T hT htri
    simpa [Function.update_idem, Function.update_self] using this
  have key := GlobalTheory.T.rightInvariant_GL_of_upperTriangular_rightInvariant (fun A => hfun Dw τ G (Function.update X b A))
    (fun A => evalFr G (Function.update X b A)) (fun d => wr τ (Function.update (fun b' => (X b').det) b d))
    (fun A₀ D => evalFr_update_line G X b A₀ D) hψ hT 1 (X b) (by simp) (hX b)
  simp only [_root_.one_mul, Function.update_eq_self] at key
  exact key

theorem hfun_eq_one [Infinite k] (hf : f ∈ secZ Xo c (exOf Dw (flatWt Dw τ) 0))
    (hGY : ∀ (y' : FrPt Xo c k) (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) k),
      (∀ b, (Y b).det ≠ 0) → FrChg (fun b => (Y b).transpose) 1 y₀ y' → (∏ b, (Y b).det) * evR Xo c f y' = evalFr G Y)
    (X : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) k) (hX : ∀ b, (X b).det ≠ 0) :
    hfun Dw τ G X = hfun Dw τ G (fun _ => 1) := by
  suffices h : ∀ s : Finset (E →+* ℂ), ∀ X : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) k,
      (∀ b, (X b).det ≠ 0) → (∀ b, b ∉ s → X b = 1) → hfun Dw τ G X = hfun Dw τ G (fun _ => 1) from
    h Finset.univ X hX fun b hb => absurd (Finset.mem_univ b) hb
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro X _ h1
    have : X = fun _ => 1 := funext fun b => h1 b (Finset.notMem_empty b)
    rw [this]
  | insert b s hb ih =>
    intro X hX h1
    rw [hfun_update_one τ y₀ G hf hGY X hX b]
    refine ih _ (fun b' => ?_) (fun b' hb' => ?_)
    · by_cases h : b' = b
      · subst h; simp
      · rw [Function.update_of_ne h]; exact hX b'
    · by_cases h : b' = b
      · subst h; simp
      · rw [Function.update_of_ne h]; exact h1 b' (by simp [h, hb'])

end Fixed

theorem evR_flat_chg : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} (τ : Psi H) {f : Rul Xo c}, f ∈ secZ Xo c (exOf Dw (flatWt Dw τ) 0) →
    ∀ {k : Type} [Field k] [Algebra c.F k] (z y : FrPt Xo c k), z.x = y.x →
    ∀ (g₁ : Matrix (Fin (Dw.mult τ.1)) (Fin (Dw.mult τ.1)) k)
      (g₂ : Matrix (Fin (Dw.mult (conjEmb τ.1))) (Fin (Dw.mult (conjEmb τ.1))) k),
      (∀ i, IsCombAt y.x (y.u τ.1) (g₁ i) (z.u τ.1 i)) →
      (∀ i, IsCombAt y.x (y.u (conjEmb τ.1)) (g₂ i) (z.u (conjEmb τ.1) i)) →
      evR Xo c f z * g₁.det = g₂.det * evR Xo c f y := by
  intro E _ _ _ H Dw l Xo c τ f hf k _ _ z y hx g₁ g₂ h₁ h₂
  classical
  have : CharZero k := charZero_of_injective_algebraMap (algebraMap c.F k).injective
  have : Infinite k := Infinite.of_injective (Nat.cast : ℕ → k) Nat.cast_injective
  obtain ⟨G, -, hG⟩ := GlobalTheory.FieldPolyZ.exists_isHomogeneous_secZ E H Dw l Xo c k y (exOf Dw (flatWt Dw τ) 0)
    (fun _ => 1) (fun b i => (exOf Dw (flatWt Dw τ) 0 (some ⟨b, i⟩) + 1).toNat)
    (GlobalTheory.FlatFrameLaw.exOf_flatWt_none τ) (fun b i => by
      have h0 : 0 ≤ exOf Dw (flatWt Dw τ) 0 (some ⟨b, i⟩) + 1 := by
        rw [GlobalTheory.FlatFrameLaw.exOf_flatWt_some]; split_ifs <;> norm_num
      rw [Int.toNat_of_nonneg h0]; simp) f hf
  have hGY : ∀ (y' : FrPt Xo c k) (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) k),
      (∀ b, (Y b).det ≠ 0) → FrChg (fun b => (Y b).transpose) 1 y y' →
        (∏ b, (Y b).det) * evR Xo c f y' = evalFr G Y := fun y' Y hY h => by
    have := hG y' Y 1 hY (by simpa using h)
    simpa using this
  obtain ⟨g, a, hg, hc⟩ := (GlobalTheory.Frames.frChg_exists_unique E H Dw l Xo c k y z).1 hx
  obtain ⟨w, hw, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c k y g 1 hg
  rw [Units.val_one] at hw
  have hwz : FrChg (fun _ => 1) (a : k) w z :=
    ((GlobalTheory.Frames.frChg_calculus E H Dw l Xo c k).1 g (fun _ => 1) 1 a y w z hw).2 (by simpa using hc)
  have e1 := GlobalTheory.FlatFrameLaw.evR_flat_frChg τ hf (fun _ => 1) (a : k) w z hwz
    (fun σ i j hij => Matrix.one_apply_ne hij.ne) (fun σ => by simp) a.ne_zero
  simp only [Matrix.det_one, inv_one, _root_.one_mul] at e1
  have hgt : ∀ b, ((g b).transpose).det ≠ 0 := fun b => by rw [Matrix.det_transpose]; exact (hg b).ne_zero
  have e2 := hfun_eq τ y G hGY (fun b => (g b).transpose) hgt w (by simpa using hw)
  have hr : FrChg (fun b => (1 : Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) k).transpose) 1 y y := by
    simpa using (GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c k y y y).1
  have e3 := hfun_eq τ y G hGY (fun _ => 1) (fun b => by simp) y hr
  have e4 := hfun_eq_one τ y G hf hGY (fun b => (g b).transpose) hgt
  have hg1 : g τ.1 = g₁ := funext fun i =>
    (y.basis τ.1 (z.u τ.1 i) (by rw [← hx]; exact z.tan τ.1 i) (z.eig τ.1 i)).unique (hc.2.1 τ.1 i) (h₁ i)
  have hg2 : g (conjEmb τ.1) = g₂ := funext fun i =>
    (y.basis (conjEmb τ.1) (z.u (conjEmb τ.1) i) (by rw [← hx]; exact z.tan (conjEmb τ.1) i)
      (z.eig (conjEmb τ.1) i)).unique (hc.2.1 (conjEmb τ.1) i) (h₂ i)
  rw [e2, e3] at e4
  simp only [Matrix.det_transpose, Matrix.det_one, div_one, _root_.mul_one] at e4
  rw [e1, ← hg1, ← hg2]
  have a2 := hgt (conjEmb τ.1)
  rw [Matrix.det_transpose] at a2
  field_simp at e4
  linear_combination e4

end GlobalTheory.FlatGL
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatToSpecFieldStatement
section
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_to_spec_field' : ∀ (K : Type) [Field K] (Z : Scheme.{0}) (f : Z ⟶ Sp K), Flat f := by
  first | exact @GlobalTheory.flat_to_spec_field | exact GlobalTheory.flat_to_spec_field | (intros; apply GlobalTheory.flat_to_spec_field <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatVectorThreeStepsConjugatePlacesStatement
section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.ExportSeries
open Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.ConjTwist (BaseOf UnitOff)
open GlobalTheory.FlatVecSum (princ)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
open GlobalTheory.BigOn.Exp.TupLe.Swap

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatVector_three_steps_conjugate_places : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m) (t : T0), VStd D i → ∀ (B : Base (Vc D i) (Wc D i)) (ψ : Twist D Circle), B.Good → BaseOf R i B → ψ.Good → B.admitted ψ.Q → R.xi t = B.de.chi * ψ.chi → idem (R.Q t) + cA D (idem (R.Q t)) = idem (B.de.Q ∪ ψ.Q) + cA D (idem (B.de.Q ∪ ψ.Q)) → ∃ (eg ea et : AE D) (fg hA : WO (Vc D i) (Wc D i) → ℂ), IsIdemSum eg R.Pg ∧ IsIdemSum ea (keepPart (R := R) t (B.de.Q ∪ ψ.Q)) ∧ IsIdemSum et (flipPart (R := R) t (B.de.Q ∪ ψ.Q)) ∧ GlobalTheory.BaseCmp.IsTypeVec R i eg fg ∧ ThAt R i ea fg (GlobalTheory.BaseCmp.flatDat R i (keepPart (R := R) t (B.de.Q ∪ ψ.Q)) (R.xiR t) ea) hA ∧ ThAt R i (cA D et) hA (GlobalTheory.BaseCmp.flatDat R i ((flipPart (R := R) t (B.de.Q ∪ ψ.Q)).image conjPl) (fun PP => B.de.locC PP * ψ.locC PP) (cA D et)) ((princ B).vecFlat ψ) := by
  first | exact @GlobalTheory.FlatThreeSteps.vecFlat_three_steps | exact GlobalTheory.FlatThreeSteps.vecFlat_three_steps | (intros; apply GlobalTheory.FlatThreeSteps.vecFlat_three_steps <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierJacobiExpansionFderivTermwiseStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierJacobiExpansion_fderiv_termwise : AllCD fun {N} {g'} {r} {g} {bX} d σ => ∀ S : Matrix (Fin r) (Fin r) ℂ, S.IsSymm → ((d.full σ S).map Complex.im).PosDef → (∀ χ, Differentiable ℂ (d.fj σ S χ)) ∧ ∀ Z W, (Summable fun χ => ‖fderiv ℂ (d.fj σ S χ) Z W‖) ∧ ∑' χ, fderiv ℂ (d.fj σ S χ) Z W = fderiv ℂ (thetaChar (d.full σ S) (d.aF σ) (d.bF σ)) Z W := by
  first | exact @GlobalTheory.MBLow.Cl.fj_expansion_fderiv | exact GlobalTheory.MBLow.Cl.fj_expansion_fderiv | (intros; apply GlobalTheory.MBLow.Cl.fj_expansion_fderiv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionsUnitDenominatorsReplaceGeneratorsStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
open Polynomial

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fractions_unitDenominators_replace_generators : ∀ (L : Type) [Field L] (ψ : ℂ →+* L) (V : ValuationSubring L) (P : L → Prop) (s₀ : Finset L), (∀ x ∈ s₀, ∃ b d : L, P b ∧ P d ∧ d ≠ 0 ∧ d⁻¹ ∈ V ∧ x = b / d) → (∀ s ∈ V, ∃ b ∈ Subring.closure (Set.range ψ ∪ ↑s₀), ∃ d ∈ Subring.closure (Set.range ψ ∪ ↑s₀), d ≠ 0 ∧ d⁻¹ ∈ V ∧ s = b / d) → ∃ t : Finset L, (∀ x ∈ t, P x) ∧ ∀ s ∈ V, ∃ b ∈ Subring.closure (Set.range ψ ∪ ↑t), ∃ d ∈ Subring.closure (Set.range ψ ∪ ↑t), d ≠ 0 ∧ d⁻¹ ∈ V ∧ s = b / d := by
  first | exact @GlobalTheory.fractions_unit_denominators_replace_generators | exact GlobalTheory.fractions_unit_denominators_replace_generators | (intros; apply GlobalTheory.fractions_unit_denominators_replace_generators <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameBallSubsetExpChartImageFrameBoxStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameBall_subset_expChart_image_frameBox : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (hG : G.det ≠ 0), (∀ τ, (mat x τ).det ≠ 0) → ∀ δ : ℝ, 0 < δ → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → frBall Ψ G x ε ⊆ GlobalTheory.SUVol.DensOne.chartExp Ψ G hG '' {X : realLie Ψ G | ‖X‖ < δ ∧ ∀ τ a b, ‖((mat x τ)⁻¹ * Matrix.of (X.1 τ) * mat x τ) a b‖ < 2 * ε} := by
  first | exact @GlobalTheory.CovTop.VolUp.BallCover.frBall_subset_chartExp_image | exact GlobalTheory.CovTop.VolUp.BallCover.frBall_subset_chartExp_image | (intros; apply GlobalTheory.CovTop.VolUp.BallCover.frBall_subset_chartExp_image <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameEqUnitSmulDForm
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogKSDiv

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.TopForm

theorem frame_eq_unit_smul_dForm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), ∀ [IsIntegral (X₀ TF.Y Z)] [SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z)] (x : X₀ TF.Y Z) (U' : (X₀ TF.Y Z).Opens) (ω : TopForm.FormsOn (s₀ TF.Y Z) Dw.dim U'), TopForm.IsFrame ω → ∀ hx : x ∈ U', letI := (GlobalTheory.LogKSDiv.stalkAlg TF Z x).toAlgebra; ∃ (g : Fin Dw.dim → (X₀ TF.Y Z).presheaf.stalk x) (bΩ : Module.Basis (Fin Dw.dim) ((X₀ TF.Y Z).presheaf.stalk x) Ω[(X₀ TF.Y Z).presheaf.stalk x⁄c.F]) (u : (X₀ TF.Y Z).presheaf.stalk x), (∀ i, bΩ i = KaehlerDifferential.D c.F ((X₀ TF.Y Z).presheaf.stalk x) (g i)) ∧ IsUnit u ∧ formOf U' (gen_mem hx) ω = algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField u • TopForm.dForm (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)) (fun i => algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField (g i)) := by
  intro E _ _ _ H Dw l Xo c TF Z _ _ x U' ω hω hx
  letI := (GlobalTheory.LogKSDiv.stalkAlg TF Z x).toAlgebra
  obtain ⟨U, y, b, hUU', hxU, hU, hb⟩ :=
    GlobalTheory.AdaptedFrame.exists_basis_dFun (s₀ TF.Y Z) Dw.dim hx
  have hy : IsFreeGen Γ(X₀ TF.Y Z, U) (dOn (s₀ TF.Y Z) y) := isFreeGen_dForm y b hb
  have hres : IsFrame (resForm hUU' ω) := hω.res hU hUU'
  obtain ⟨a, ha⟩ := hy.2 (resForm hUU' ω)
  have hau : IsUnit a := by
    have := hres.gen
    rw [← ha] at this
    exact hy.smul_iff.1 this
  have hgU : genericPoint (X₀ TF.Y Z) ∈ U := gen_mem hxU
  have hform : formOf U' (gen_mem hx) ω =
      fnOf U hgU a • dForm (constFn (s₀ TF.Y Z)) (fun i => fnOf U hgU (y i)) := by
    rw [← formOf_resForm hUU' hgU ω, ← ha, map_smulₛₗ]
    congr 1
    exact formMap_dForm _ _ _
  letI iΓ : Algebra c.F Γ(X₀ TF.Y Z, U) := (algX (s₀ TF.Y Z) U).toAlgebra
  letI iΓA : Algebra Γ(X₀ TF.Y Z, U) ((X₀ TF.Y Z).presheaf.stalk x) :=
    ((X₀ TF.Y Z).presheaf.germ U x hxU).hom.toAlgebra
  have hsc : algebraMap c.F ((X₀ TF.Y Z).presheaf.stalk x) =
      (algebraMap Γ(X₀ TF.Y Z, U) ((X₀ TF.Y Z).presheaf.stalk x)).comp
        (algebraMap c.F Γ(X₀ TF.Y Z, U)) := by
    ext t
    change ((X₀ TF.Y Z).presheaf.germ ⊤ x trivial).hom (algX (s₀ TF.Y Z) ⊤ t) =
      ((X₀ TF.Y Z).presheaf.germ U x hxU).hom (algX (s₀ TF.Y Z) U t)
    rw [← resG_comp_algX (s₀ TF.Y Z) (le_top : U ≤ ⊤), RingHom.comp_apply, germ_resG]
  haveI : IsScalarTower c.F Γ(X₀ TF.Y Z, U) ((X₀ TF.Y Z).presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_eq' hsc
  haveI : IsLocalization.AtPrime ((X₀ TF.Y Z).presheaf.stalk x) (hU.primeIdealOf ⟨x, hxU⟩).asIdeal :=
    hU.isLocalization_stalk ⟨x, hxU⟩
  haveI : Algebra.FormallyEtale Γ(X₀ TF.Y Z, U) ((X₀ TF.Y Z).presheaf.stalk x) :=
    .of_isLocalization (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
  have hbc := KaehlerDifferential.isBaseChange_of_formallyEtale c.F Γ(X₀ TF.Y Z, U)
    ((X₀ TF.Y Z).presheaf.stalk x)
  refine ⟨fun i => ((X₀ TF.Y Z).presheaf.germ U x hxU).hom (y i), hbc.basis b,
    ((X₀ TF.Y Z).presheaf.germ U x hxU).hom a, fun i => ?_, hau.map _, ?_⟩
  · rw [IsBaseChange.basis_apply, hb]
    exact KaehlerDifferential.map_D c.F c.F _ _ (y i)
  · rw [hform]
    simp only [algebraMap_germ]
end GlobalTheory.LogKSDiv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramePointTangentMatrices
section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

namespace GlobalTheory.FrameChangePair

theorem isCombAt_unique {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)} {a : Fin m → S}
    {w₁ w₂ : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (h₁ : IsCombAt x v a w₁) (h₂ : IsCombAt x v a w₂) :
    w₁ = w₂ := by
  obtain ⟨u₁, hu₁, hw₁⟩ := h₁
  obtain ⟨u₂, hu₂, hw₂⟩ := h₂
  have hu : u₁ = u₂ := funext fun i => Over.OverMorphism.ext ((hu₁ i).trans (hu₂ i).symm)
  rw [← hw₁, ← hw₂, hu]

theorem psi_ne_conjEmb {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (τ : Psi H) :
    τ.1 ≠ conjEmb τ.1 := by
  intro h
  have hτ : τ.1 (H.rt : E) = H.rt0 := τ.2
  have hc : (starRingEnd ℂ) H.rt0 = H.rt0 := by
    have := congrArg (fun σ : E →+* ℂ => σ (H.rt : E)) h
    simp only [conjEmb, RingHom.comp_apply, hτ] at this
    exact this.symm
  have h1 : (H.rt0.re : ℂ) ^ 2 = -(H.d : ℂ) := by rw [Complex.conj_eq_iff_re.1 hc]; exact H.sqrt_neg_disc_sq
  have h2 : H.rt0.re ^ 2 = -(H.d : ℝ) := by exact_mod_cast h1
  have h3 : (2 : ℝ) ≤ H.d := by exact_mod_cast H.d_prime.two_le
  nlinarith [sq_nonneg H.rt0.re]

theorem exists_frPt_comb_pair : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (L : Type) [CommRing L] [Algebra c.F L] (z₀ : FrPt Xo c L)
    (τ : Psi H) (g₁ : Matrix (Fin (Dw.mult τ.1)) (Fin (Dw.mult τ.1)) L)
    (g₂ : Matrix (Fin (Dw.mult (conjEmb τ.1))) (Fin (Dw.mult (conjEmb τ.1))) L)
    (v₁ : Fin (Dw.mult τ.1) → (Sp (DualNumber L) ⟶ Xo.univ.t.G.left))
    (v₂ : Fin (Dw.mult (conjEmb τ.1)) → (Sp (DualNumber L) ⟶ Xo.univ.t.G.left)),
    IsUnit g₁.det → IsUnit g₂.det → (∀ i, IsCombAt z₀.x (z₀.u τ.1) (g₁ i) (v₁ i)) →
    (∀ i, IsCombAt z₀.x (z₀.u (conjEmb τ.1)) (g₂ i) (v₂ i)) →
    ∃ z : FrPt Xo c L, z.x = z₀.x ∧ (∀ i, z.u τ.1 i = v₁ i) ∧ ∀ i, z.u (conjEmb τ.1) i = v₂ i := by
  classical
  intro E _ _ _ H Dw l Xo c L _ _ z₀ τ g₁ g₂ v₁ v₂ hg₁ hg₂ hv₁ hv₂
  have hne : τ.1 ≠ conjEmb τ.1 := psi_ne_conjEmb τ
  let G : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) L :=
    Function.update (Function.update (fun σ => (1 : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) L)) τ.1 g₁)
      (conjEmb τ.1) g₂
  have hG₂ : G (conjEmb τ.1) = g₂ := Function.update_self _ _ _
  have hG₁ : G τ.1 = g₁ := by
    dsimp only [G]
    rw [Function.update_of_ne hne, Function.update_self]
  have hdet : ∀ σ, IsUnit (G σ).det := by
    intro σ
    by_cases h1 : σ = conjEmb τ.1
    · subst h1; rw [hG₂]; exact hg₂
    · by_cases h2 : σ = τ.1
      · subst h2; rw [hG₁]; exact hg₁
      · dsimp only [G]
        rw [Function.update_of_ne h1, Function.update_of_ne h2, Matrix.det_one]
        exact isUnit_one
  obtain ⟨z, hz, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c L z₀ G 1 hdet
  obtain ⟨hx, hc, -⟩ := hz
  refine ⟨z, hx, fun i => ?_, fun i => ?_⟩
  · have h := hc τ.1 i
    rw [hG₁] at h
    exact isCombAt_unique h (hv₁ i)
  · have h := hc (conjEmb τ.1) i
    rw [hG₂] at h
    exact isCombAt_unique h (hv₂ i)

end GlobalTheory.FrameChangePair
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameVectorsEqEigenFrameMulInvertibleStatement
section
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv mkT tanM_ext tv_mem actR)
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameVectors_eq_eigenFrame_mul_invertible : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (p : Proj (RingHom.id c.F)) (A : Atlas Y p) (b : A.B) (S₀ : Type) [CommRing S₀] [Algebra c.F S₀] (P₀ : FrPt Xo c S₀), ⊤ ≤ (frX P₀ ≫ Y.j) ⁻¹ᵁ (A.k b).V → ∀ σ : E →+* ℂ, ∃ T : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S₀, IsUnit T.det ∧ ∀ (S' : Type) [CommRing S'] [Algebra c.F S'] (ψ : S₀ →ₐ[c.F] S') (P' : FrPt Xo c S'), FrMap ψ P₀ P' → ∀ (h' : ⊤ ≤ (frX P' ≫ Y.j) ⁻¹ᵁ (A.k b).V) (hM' : ⊤ ≤ (frX P' ≫ Y.j) ⁻¹ᵁ (A.k b).M.U) (j : Fin (Dw.mult σ)), frVec Y P' rfl σ j = vec (A.k b).M.toMChart _ hM' (fun r => ((((A.k b).u σ).map (ev _ _ h')) * T.map ψ) r j) := by
  first | exact @GlobalTheory.FlagMod.FieldFlag.frVec_eq_eigFrame_mul | exact GlobalTheory.FlagMod.FieldFlag.frVec_eq_eigFrame_mul | (intros; apply GlobalTheory.FlagMod.FieldFlag.frVec_eq_eigFrame_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryEqReflOfCongrModGeThreeStatement
section
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isometry_eq_refl_of_congr_mod_ge_three : ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (β : LinearMap.BilinForm ℤ X), (∀ x, x ≠ 0 → 0 < β x x) → ∀ (e : X ≃ₗ[ℤ] X), (∀ x y, β (e x) (e y) = β x y) → ∀ N : ℕ, 3 ≤ N → (∀ x, CongMod N (e x) x) → e = LinearEquiv.refl ℤ X := by
  first | exact @GlobalTheory.Poinc.eq_refl_of_isometry_congMod | exact GlobalTheory.Poinc.eq_refl_of_isometry_congMod | (intros; apply GlobalTheory.Poinc.eq_refl_of_isometry_congMod <;> assumption)
end

