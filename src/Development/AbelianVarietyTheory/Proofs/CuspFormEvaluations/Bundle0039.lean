import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0005
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0062
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0032
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0014
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0036
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ThetaFunctionTorusL2Norm
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
import Development.AbelianVarietyTheory.Definitions.ThetaValues.FlatMemLatIffStdLat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0007

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HarmonicSumTriangularFrameChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TriangularFrame

theorem basis_of_triangular {T : Type} [Fintype T] {r : T → ℕ} {S : Type} [CommRing S] {d : ℕ}
    (u : (Σ τ : T, Fin (r τ)) → Fin d → S) (cf : ∀ τ : T, Fin (r τ) → Fin (r τ) → S)
    (h0 : ∀ τ i j, i < j → cf τ i j = 0) (h1 : ∀ τ i, IsUnit (cf τ i i))
    (hb : ∀ v : Fin d → S, ∃! a : (Σ τ : T, Fin (r τ)) → S, ∀ j, ∑ ℓ, a ℓ * u ℓ j = v j) (v : Fin d → S) :
    ∃! a : (Σ τ : T, Fin (r τ)) → S, ∀ e, ∑ ℓ, a ℓ * (∑ j, cf ℓ.1 ℓ.2 j * u ⟨ℓ.1, j⟩ e) = v e := by
  classical
  have hdet : ∀ τ, IsUnit (Matrix.of (cf τ)).det := fun τ => by
    rw [Matrix.det_of_lowerTriangular (Matrix.of (cf τ)) (fun i j hij => h0 τ i j (by simpa using hij))]
    exact IsUnit.prod_iff.2 fun i _ => h1 τ i
  have key : ∀ (a : (Σ τ : T, Fin (r τ)) → S) e, ∑ ℓ, a ℓ * (∑ j, cf ℓ.1 ℓ.2 j * u ⟨ℓ.1, j⟩ e) =
      ∑ ℓ : (Σ τ : T, Fin (r τ)), Matrix.vecMul (fun i => a ⟨ℓ.1, i⟩) (Matrix.of (cf ℓ.1)) ℓ.2 * u ℓ e := by
    intro a e
    rw [Fintype.sum_sigma, Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun τ _ => ?_
    simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul]
    simp only [_root_.mul_assoc]
    exact Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
      (f := fun (i j : Fin (r τ)) => a ⟨τ, i⟩ * (cf τ i j * u ⟨τ, j⟩ e))
  simp only [key]
  obtain ⟨b, hb1, hb2⟩ := hb v
  have back : ∀ a : (Σ τ : T, Fin (r τ)) → S,
      (∀ e, ∑ ℓ : (Σ τ : T, Fin (r τ)), Matrix.vecMul (fun i => a ⟨ℓ.1, i⟩) (Matrix.of (cf ℓ.1)) ℓ.2 * u ℓ e = v e) →
      a = fun ℓ => Matrix.vecMul (fun i => b ⟨ℓ.1, i⟩) (Matrix.of (cf ℓ.1))⁻¹ ℓ.2 := by
    intro a ha
    have := hb2 _ ha
    subst this
    funext ℓ
    show _ = Matrix.vecMul (Matrix.vecMul (fun i => a ⟨ℓ.1, i⟩) (Matrix.of (cf ℓ.1))) _ _
    rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ (hdet _), Matrix.vecMul_one]
  refine ⟨fun ℓ => Matrix.vecMul (fun i => b ⟨ℓ.1, i⟩) (Matrix.of (cf ℓ.1))⁻¹ ℓ.2, fun e => ?_, back⟩
  rw [← hb1 e]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  congr 1
  show Matrix.vecMul (Matrix.vecMul (fun i => b ⟨ℓ.1, i⟩) (Matrix.of (cf ℓ.1))⁻¹) _ _ = _
  rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (hdet _), Matrix.vecMul_one]

theorem fst_comp_jetTan {S : Type} [CommRing S] {κ : Type} [DecidableEq κ] (ℓ : κ) :
    (TrivSqZeroExt.fstHom S S S).comp (jetTan ℓ : Jet S κ (0 + 1) →ₐ[S] DualNumber S) = jetAug := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  show TrivSqZeroExt.fst (MvPolynomial.aeval
    (fun i => if i = ℓ then (DualNumber.eps : DualNumber S) else 0) (MvPolynomial.X i : MvPolynomial κ S)) =
    MvPolynomial.aeval (fun _ => (0 : S)) (MvPolynomial.X i : MvPolynomial κ S)
  by_cases h : i = ℓ <;> simp [h]

theorem left_one {T : Scheme.{0}} {X : Over T} {M : Over T} [GrpObj M] : (1 : X ⟶ M).left = X.hom ≫ η[M].left := by
  show (toUnit X ≫ η[M]).left = _
  rw [Over.comp_left]
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem isTanAt_jetTan {S : Type} [CommRing S] (x0 : Sp S ⟶ Xo.X) {κ : Type} [DecidableEq κ]
    (x : overAt x0 (Jet S κ (0 + 1)) ⟶ Xo.univ.t.G)
    (hx : homAt x0 (jetAug : Jet S κ (0 + 1) →ₐ[S] S) ≫ x = 1) (ℓ : κ) :
    IsTanAt x0 (homAt x0 (jetTan ℓ : Jet S κ (0 + 1) →ₐ[S] DualNumber S) ≫ x).left := by
  refine ⟨Over.w _, ?_⟩
  have h1 := congrArg (fun f => f.left) hx
  simp only [Over.comp_left, left_one] at h1 ⊢
  have e : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫
      (homAt x0 (jetTan ℓ : Jet S κ (0 + 1) →ₐ[S] DualNumber S)).left =
      (homAt x0 (jetAug : Jet S κ (0 + 1) →ₐ[S] S)).left := by
    rw [← fst_comp_jetTan ℓ]
    exact (Spec.map_comp _ _).symm
  refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ x.left) e)).trans (h1.trans ?_)
  have e' : spMap (algebraMap S S) = 𝟙 _ := Spec.map_id _
  show (spMap (algebraMap S S) ≫ x0) ≫ _ = x0 ≫ _
  rw [e', Category.id_comp]

theorem eq_of_isPullSec_id {X : Scheme.{0}} (A : Over X) [GrpObj A] (L : LB A.left) (k : ℤ) (T : Over X)
    (F F' : LB.Sec (LPow A L k T)) (h : IsPullSec A L k (𝟙 T ▷ A) (whiskerRight_snd _ _) F F') : F' = F := by
  have key : ∀ (g : T ⊗ A ⟶ T ⊗ A) (hg : g ≫ snd T A = snd T A), g = 𝟙 _ → IsPullSec A L k g hg F F' → F' = F := by
    intro g hg e h
    subst e
    obtain ⟨f, hf⟩ := F
    obtain ⟨f', hf'⟩ := F'
    congr
    funext j
    refine (h j).trans ?_
    show ((T ⊗ A).left.presheaf.map (𝟙 _)).hom (f j) = f j
    rw [CategoryTheory.Functor.map_id]
    rfl
  exact key _ _ (MonoidalCategory.id_whiskerRight _ _) h

theorem sum_eq (hC : ChartIndepSt2) [StarRing (𝓞 E)] (nab : NabV Xo c) (hnab : IsNab Xo c nab)
    {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (ho u' h1 h2 h3 s' h4)
    (cf : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Fin (Dw.mult τ) → S)
    (h0 : ∀ τ i j, i < j → cf τ i j = 0) (hu : ∀ τ i, IsUnit (cf τ i i))
    (hcomb : ∀ τ i, IsCombAt y.x (y.u τ) (cf τ i) (u' τ i)) (n : ℕ) (a : (E →+* ℂ) × ℕ → ℕ)
    (P : MvPolynomial (LtN Dw n) c.F)
    (hP : P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) (k : ℕ)
    (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))) :
    ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) *
        ∏ b, nab (⟨y.x, ho, u', h1, h2, h3, s', h4⟩ : FrPt Xo c S) k (F b) (colOf m b) =
      (∏ ℓ : Lt1 Dw, cf ℓ.1 ℓ.2 ℓ.2 ^ a (ℓ.1, ℓ.2)) *
        ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab y k (F b) (colOf m b) := by
  letI : Algebra ℚ S := ((algebraMap c.F S).comp (algebraMap ℚ c.F)).toAlgebra
  set y' : FrPt Xo c S := ⟨y.x, ho, u', h1, h2, h3, s', h4⟩ with hy'
  obtain ⟨C, hex, hpin⟩ := hnab.2 S y
  obtain ⟨C', hex', hpin'⟩ := hnab.2 S y'
  choose f hf using fun b => hex k (F b)
  choose f' hf' using fun b => hex' k (F b)
  let uv : Lt1 Dw → Fin C.d → S := fun ℓ e => ∑ j, cf ℓ.1 ℓ.2 j * C.uvec ⟨ℓ.1, j⟩ e
  let D : ChartAt Xo c y' :=
    ⟨C.d, C.B, uv, C.x, C.e, C.wP, C.h,
      ⟨C.chart.zero, C.chart.trunc, C.chart.law, C.chart.act, fun ℓ => by
        have := GlobalTheory.TangentLinear.isCombAt_mulVec E H Dw l Xo S y.x _
          (fun j => isTanAt_jetTan y.x (C.x 1) (C.chart.zero 1) ((0 : Fin 1), j)) (y.u ℓ.1)
          (Matrix.of fun e j => C.uvec ⟨ℓ.1, j⟩ e) (cf ℓ.1 ℓ.2) (u' ℓ.1 ℓ.2)
          (fun i => C.chart.tan ⟨ℓ.1, i⟩) (hcomb ℓ.1 ℓ.2)
        have e : (Matrix.of fun e j => C.uvec ⟨ℓ.1, j⟩ e).mulVec (cf ℓ.1 ℓ.2) = uv ℓ := by
          funext e
          simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, uv]
          exact Finset.sum_congr rfl fun j _ => _root_.mul_comm _ _
        rw [e] at this
        exact this,
        basis_of_triangular C.uvec cf h0 hu C.chart.basis⟩,
      ⟨C.frame.gen, C.frame.ph1, C.frame.ph2, C.frame.sy, C.frame.ad⟩, C.prim, C.gauge, C.rig0⟩
  obtain ⟨N, hN, hNP, hsupp⟩ := GlobalTheory.exists_natCast_smul_mem_harmA E H Dw l c a n P hP
  have hI := hC E H Dw l Xo c hnab.1 S y' C' D k n F f' f hf' hf a _ hNP
  have hNu : IsUnit (algebraMap c.F S (N : c.F)) :=
    (IsUnit.mk0 (N : c.F) (Nat.cast_ne_zero.2 hN.ne')).map _
  have hsc : ∀ (C₀ : ChartAt Xo c y') (g : Fin n → MvPowerSeries (Fin 1 × Fin C₀.d) S),
      chartVal C₀ k g ((N : c.F) • P) = algebraMap c.F S (N : c.F) * chartVal C₀ k g P := by
    intro C₀ g
    simp only [chartVal, hsupp, MvPolynomial.coeff_smul, smul_eq_mul, map_mul, Finset.mul_sum, _root_.mul_assoc]
  rw [hsc, hsc] at hI
  have hI' := hNu.mul_left_cancel hI
  have e₁ : ∀ m, ∏ b, nab y k (F b) (colOf m b) =
      ∏ b, C.B.nabVal S C.h H.w0 k (f b) C.uvec (MvPolynomial.monomial (colOf m b) 1) := fun m =>
    Finset.prod_congr rfl fun b _ => hpin k (F b) (f b) (hf b) (colOf m b)
  have e₂ : ∀ m, ∏ b, nab y' k (F b) (colOf m b) =
      ∏ b, C'.B.nabVal S C'.h H.w0 k (f' b) C'.uvec (MvPolynomial.monomial (colOf m b) 1) := fun m =>
    Finset.prod_congr rfl fun b _ => hpin' k (F b) (f' b) (hf' b) (colOf m b)
  simp only [e₁]
  exact (Finset.sum_congr rfl fun m _ => congrArg _ (e₂ m)).trans <| hI'.trans (GlobalTheory.T.invariantOperator_value_triangular_change E H Dw l c S C.d C.B C.h C.gauge k n f C.uvec uv cf h0 (fun _ _ _ => rfl) hu a P hP)

theorem harmonic_sum_frBor : ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (S : Type) [CommRing S] [Algebra c.F S] (y y' : FrPt Xo c S) (t : Ix Dw → Sˣ), FrBor t y y' → ∀ (h : ptO Xo y'.x ⟶ ptO Xo y.x), h.left = 𝟙 _ → ∀ (n : ℕ), ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∀ (N : ℕ) (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))) (F' : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y'.x))), (∀ b, IsPullSec Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (h ▷ Xo.univ.t.G) (whiskerRight_snd _ _) (F b) (F' b)) → ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab y' ((N : ℤ) ^ 2) (F' b) (colOf m b) = (∏ ℓ : Lt1 Dw, ((t (some ℓ) : Sˣ) : S) ^ a (ℓ.1, ℓ.2)) * ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab y ((N : ℤ) ^ 2) (F b) (colOf m b) := by
  intro hC E _ _ _ H Dw l Xo c _ nab hnab S _ _ y y' t hb h hh n a P hP N
  obtain ⟨x', ho, u', h1, h2, h3, s', h4⟩ := y'
  obtain ⟨hx, hcf, -⟩ := hb
  dsimp only at hx
  subst hx
  choose cf hd h0 hcomb using hcf
  have e : h = 𝟙 _ := Over.OverMorphism.ext hh
  subst e
  have hk : ((N : ℤ) ^ 2) = ((N ^ 2 : ℕ) : ℤ) := (Nat.cast_pow N 2).symm
  generalize ((N : ℤ) ^ 2) = K at hk
  subst hk
  intro F F' hF
  have hFF : F' = F := funext fun b => eq_of_isPullSec_id _ _ _ _ _ _ (hF b)
  subst hFF
  have := sum_eq hC nab hnab y ho u' h1 h2 h3 s' h4 cf h0 (fun τ i => by rw [hd]; exact Units.isUnit _) hcomb
    n a P hP (N ^ 2) F'
  simp only [hd] at this
  exact this

end GlobalTheory.TriangularFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.L2OneEqIntegralFundamentalDomainDivVolume
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.ThetaPT

open MeasureTheory

theorem Hf_add_smul_left {κ : Type} [Fintype κ] (c : ℂ) (v w u : EuclideanSpace ℂ κ) :
    I2.Hf (v + c • w) u = I2.Hf v u + c * I2.Hf w u := by
  unfold I2.Hf
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

theorem Hf_neg_right {κ : Type} [Fintype κ] (v w : EuclideanSpace ℂ κ) :
    I2.Hf v (-w) = -I2.Hf v w := by
  unfold I2.Hf
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp

theorem Hf_neg_left {κ : Type} [Fintype κ] (v w : EuclideanSpace ℂ κ) :
    I2.Hf (-v) w = -I2.Hf v w := by
  unfold I2.Hf
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp

theorem cexp_pi_int (k : ℤ) : cexp (Real.pi * I * (k : ℂ)) = ((Real.cos (Real.pi * k) : ℝ) : ℂ) := by
  have h : (Real.pi : ℂ) * I * (k : ℂ) = ((Real.pi * k : ℝ) : ℂ) * I := by push_cast; ring
  have hs : Real.sin (Real.pi * k) = 0 := by rw [mul_comm]; exact Real.sin_int_mul_pi k
  rw [h, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, hs]
  simp

theorem l2_one_eq_integral_fundamentalDomain_div_volume {E : Type} [Field E] [NumberField E] {g : ℕ} (T : I2.PT E)
    (ψ : (Fin g → ℂ) ≃ₗ[ℂ] I2.Vsp T.dim) (θ : (Fin g → ℂ) → ℂ)
    (hs : (fun v : Fin 1 → I2.Vsp T.dim => θ (ψ.symm (v 0))) ∈ T.Sec 1 1)
    (A : AddSubgroup (Fin g → ℂ)) (hL : ∀ z, z ∈ A ↔ ψ z ∈ T.L) (Fd : Set (Fin g → ℂ))
    (hFd : IsAddFundamentalDomain A Fd volume) :
    T.l2 1 (fun v : Fin 1 → I2.Vsp T.dim => θ (ψ.symm (v 0))) =
      (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (I2.Hf (ψ z) (ψ z)).re)) / (volume Fd).toReal := by
  classical

  have hper : ∀ (a : A) (z : Fin g → ℂ),
      ‖θ (a +ᵥ z)‖ ^ 2 * Real.exp (-Real.pi * (I2.Hf (ψ (a +ᵥ z)) (ψ (a +ᵥ z))).re) =
        ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (I2.Hf (ψ z) (ψ z)).re) := by
    intro a z
    have ha : ψ a ∈ T.L := (hL a).1 a.2
    obtain ⟨-, hq⟩ := hs
    have h := hq (fun _ => ψ a) (fun _ => ha) (fun _ => ψ z)
    simp only [Pi.add_apply, I2.HC, Fin.sum_univ_one, Fin.prod_univ_one, pow_one, Nat.cast_one,
      _root_.one_mul, map_add, LinearEquiv.symm_apply_apply] at h
    have hε : ‖((T.eps (ψ a) : ℤ) : ℂ)‖ = 1 := by
      rcases T.eps_pm _ ha with h1 | h1 <;> simp [h1]
    have hv : (a +ᵥ z : Fin g → ℂ) = z + a := by
      change (a : Fin g → ℂ) + z = z + a
      exact add_comm _ _
    have hre : ((Real.pi : ℂ) * I2.Hf (ψ z) (ψ a) + (Real.pi : ℂ) * I2.Hf (ψ a) (ψ a) / 2).re =
        Real.pi * (I2.Hf (ψ z) (ψ a)).re + Real.pi * (I2.Hf (ψ a) (ψ a)).re / 2 := by
      simp [Complex.add_re, Complex.div_ofNat_re]
    rw [hv, h, map_add, GlobalTheory.EtaAn.ThetaTorus.Hf_add_re, norm_mul, norm_mul, hε, _root_.one_mul,
      Complex.norm_exp, hre, mul_pow, sq (Real.exp _), ← Real.exp_add,
      mul_comm (Real.exp _) (‖θ z‖ ^ 2), _root_.mul_assoc, ← Real.exp_add]
    congr 2
    ring

  let ψR : (Fin g → ℂ) ≃L[ℝ] I2.Vsp T.dim := (ψ.restrictScalars ℝ).toContinuousLinearEquiv
  have hψR : ∀ z, ψR z = ψ z := fun z => rfl
  let eR : (Fin g → ℂ) ≃L[ℝ] (Fin 1 → I2.Vsp T.dim) :=
    ψR.trans (ContinuousLinearEquiv.funUnique (Fin 1) ℝ (I2.Vsp T.dim)).symm
  have heR : ∀ z, eR z = fun _ => ψ z := fun z => rfl

  have hl2 : T.l2 1 (fun v : Fin 1 → I2.Vsp T.dim => θ (ψ.symm (v 0))) =
      ⨍ z in ψ ⁻¹' ZSpan.fundamentalDomain T.b,
        ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (I2.Hf (ψ z) (ψ z)).re) := by
    have hset : eR ⁻¹' T.fd 1 = ψ ⁻¹' ZSpan.fundamentalDomain T.b := by
      ext z
      simp [I2.PT.fd, heR]
    unfold I2.PT.l2
    rw [GlobalTheory.EtaAn.ThetaTorus.setAverage_equiv volume volume eR, hset]
    congr 1
    funext z
    simp [I2.PT.ptN2, I2.HC, heR]

  have hqmp : MeasureTheory.Measure.QuasiMeasurePreserving ψR volume volume :=
    ⟨ψR.continuous.measurable, MeasureTheory.Measure.absolutelyContinuous_isAddHaarMeasure _ _⟩

  have hfd0 : IsAddFundamentalDomain A (ψ ⁻¹' ZSpan.fundamentalDomain T.b) volume := by
    have h0 := ZSpan.isAddFundamentalDomain T.b (volume : Measure (I2.Vsp T.dim))
    refine h0.preimage_of_equiv hqmp
      (e := fun y => (⟨ψ.symm y, (hL _).2 (by simp only [LinearEquiv.apply_symm_apply]; exact y.2)⟩ : A)) ⟨?_, ?_⟩ ?_
    · intro y y' hyy
      have := congrArg Subtype.val hyy
      exact Subtype.ext (ψ.symm.injective this)
    · intro a
      refine ⟨⟨ψ a, (hL a).1 a.2⟩, ?_⟩
      ext1
      simp
    · intro y z
      change ψ (ψ.symm (y : I2.Vsp T.dim) + z) = (y : I2.Vsp T.dim) + ψ z
      simp
  have hcA : Countable A := by
    have : Countable (Submodule.span ℤ (Set.range T.b)) := inferInstance
    refine Function.Injective.countable
      (f := fun a : A => (⟨ψ a, (hL a).1 a.2⟩ : Submodule.span ℤ (Set.range T.b))) ?_
    intro a a' h
    exact Subtype.ext (ψ.injective (congrArg Subtype.val h))
  rw [hl2, MeasureTheory.setAverage_eq, MeasureTheory.measureReal_def, hfd0.measure_eq hFd,
    hfd0.setIntegral_eq hFd hper, smul_eq_mul, div_eq_inv_mul]

theorem theta_on_torus :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (w : 𝓞 E) (L : Lt E r) (x : Frame X.Ψ r) (t : ℝ) (T : I2.PT E) (ψ : (Fin g → ℂ) ≃ₗ[ℂ] I2.Vsp T.dim) (e : Fin g ≃ I2.Idx T.dim), IsSympl X bas → x ∈ X.dom → (w : E) + cc (w : E) = 1 → (T.r = r ∧ (∀ z z', I2.Hf (ψ z) (ψ z') = hx X bas idx x z z') ∧ (∀ ga, ga ∈ T.L ↔ ∃ u ∈ L, ga = ψ (pv X idx x u)) ∧ (∀ (a : 𝓞 E) u, ψ (pv X idx x ((a : E) • u)) = I2.act a (ψ (pv X idx x u))) ∧ (∀ ga ∈ T.L, (T.eps ga : ℝ) = Real.cos (Real.pi * (I2.Hf ga (I2.act w ga)).im)) ∧ (∀ j, (e j).1 = rowType X (idx j) ∧ ψ (Pi.single j 1) = ((Real.sqrt t : ℝ) : ℂ) • EuclideanSpace.single (e j) (1 : ℂ))) → (∀ θ : (Fin g → ℂ) → ℂ, IsTheta1 X bas idx (w : E) x L θ → (fun v : Fin 1 → I2.Vsp T.dim => θ (ψ.symm (v 0))) ∈ T.Sec 1 1 ∧ (MeanOne X bas idx x L θ → T.l2 1 (fun v : Fin 1 → I2.Vsp T.dim => θ (ψ.symm (v 0))) = 1)) ∧ (∀ (n k : ℕ) (th : Fin n → (Fin g → ℂ) → ℂ) (a z : Fin n → Fin g → ℂ), ∏ b, fock X bas idx x k (a b) (th b) (z b) = T.U k (fun b => -ψ (a b)) (fun v => ∏ b, th b (ψ.symm (v b))) (fun b => ψ (z b))) ∧ ∀ u ∈ L, eps1 X (w : E) u = (T.eps (ψ (pv X idx x u)) : ℂ) := by
  intro E _ _ _ r X g bas idx w L x t T ψ e hsy hxd hw hT
  obtain ⟨-, hH, hL, hact, heps, -⟩ := hT
  have hlaws := hx_laws E r X g bas idx 0 hsy ⟨0, rfl⟩ x hxd
  have hpvL : ∀ u ∈ L, ψ (pv X idx x u) ∈ T.L := fun u hu => (hL _).2 ⟨u, hu, rfl⟩

  have hsign : ∀ u ∈ L, eps1 X (w : E) u = (T.eps (ψ (pv X idx x u)) : ℂ) := by
    intro u hu
    have hmem := hpvL u hu
    obtain ⟨k, hk⟩ := T.integral _ _ hmem (T.stable w _ hmem)
    have him : (I2.Hf (ψ (pv X idx x u)) (I2.act w (ψ (pv X idx x u)))).im =
        (EF X u ((w : E) • u) : ℝ) := by
      rw [← hact, hH]
      exact hlaws.2.2.1 u _
    have hq : ((EF X u ((w : E) • u) : ℚ) : ℂ) = (k : ℂ) := by
      have h1 : ((EF X u ((w : E) • u) : ℚ) : ℝ) = (k : ℝ) := by rw [← him, hk]
      have h2 := congrArg (fun s : ℝ => (s : ℂ)) h1
      push_cast at h2
      exact h2
    have hs1 : ((T.eps (ψ (pv X idx x u)) : ℤ) : ℂ) = ((Real.cos (Real.pi * k) : ℝ) : ℂ) := by
      have h1 := heps _ hmem
      rw [hk] at h1
      rw [← h1]
      norm_cast
    unfold eps1
    rw [hq, cexp_pi_int, hs1]

  have hHadd : ∀ z a : Fin g → ℂ, hx X bas idx x (z + (1 / 2 : ℂ) • a) a =
      I2.Hf (ψ z) (ψ a) + I2.Hf (ψ a) (ψ a) / 2 := by
    intro z a
    rw [← hH, map_add, map_smul, Hf_add_smul_left]
    ring
  have hHadd' : ∀ z a : Fin g → ℂ, hx X bas idx x (z + (1 / 2 : ℂ) • a) a =
      hx X bas idx x z a + hx X bas idx x a a / 2 := by
    intro z a
    rw [hHadd, hH, hH]

  have hthper : ∀ θ, IsTheta1 X bas idx (w : E) x L θ → ∀ u ∈ L, ∀ z,
      θ (z + pv X idx x u) = (T.eps (ψ (pv X idx x u)) : ℂ) *
        cexp (Real.pi * I2.Hf (ψ z) (ψ (pv X idx x u)) +
          Real.pi * I2.Hf (ψ (pv X idx x u)) (ψ (pv X idx x u)) / 2) * θ z := by
    intro θ hθ u hu z
    obtain ⟨-, hθp⟩ := hθ
    have h := congrFun (hθp u hu) z
    simp only [Pi.smul_apply, smul_eq_mul, fock, hHadd, hsign u hu, Nat.cast_one, _root_.one_mul] at h
    set ε : ℂ := ((T.eps (ψ (pv X idx x u)) : ℤ) : ℂ) with hεdef
    set P := I2.Hf (ψ z) (ψ (pv X idx x u))
    set Q := I2.Hf (ψ (pv X idx x u)) (ψ (pv X idx x u))
    have hε : ε * ε = 1 := by
      rcases T.eps_pm _ (hpvL u hu) with h1 | h1 <;> simp [hεdef, h1]
    have hc : cexp (Real.pi * P + Real.pi * Q / 2) * cexp (-(Real.pi * (P + Q / 2))) = 1 := by
      rw [← Complex.exp_add, show (Real.pi : ℂ) * P + Real.pi * Q / 2 + -(Real.pi * (P + Q / 2)) = 0 by ring,
        Complex.exp_zero]
    rw [← h]
    linear_combination (-(cexp (Real.pi * P + Real.pi * Q / 2) * cexp (-(Real.pi * (P + Q / 2)))) *
      θ (z + pv X idx x u)) * hε - θ (z + pv X idx x u) * hc

  have hsec : ∀ θ, IsTheta1 X bas idx (w : E) x L θ →
      (fun v : Fin 1 → I2.Vsp T.dim => θ (ψ.symm (v 0))) ∈ T.Sec 1 1 := by
    intro θ hθ
    show Differentiable ℂ (fun v : Fin 1 → I2.Vsp T.dim => θ (ψ.symm (v 0))) ∧ _
    refine ⟨?_, ?_⟩
    · have hd : Differentiable ℂ (fun y : I2.Vsp T.dim => ψ.symm y) := by
        simpa using (LinearMap.toContinuousLinearMap
          (ψ.symm : I2.Vsp T.dim →ₗ[ℂ] (Fin g → ℂ))).differentiable
      obtain ⟨hθd, -⟩ := hθ
      exact hθd.comp (hd.comp (differentiable_apply 0))
    · intro gam hgam v
      obtain ⟨u, hu, hgu⟩ := (hL (gam 0)).1 (hgam 0)
      have h := hthper θ hθ u hu (ψ.symm (v 0))
      simp only [Pi.add_apply, I2.HC, Fin.sum_univ_one, Fin.prod_univ_one, pow_one, Nat.cast_one,
        _root_.one_mul, map_add]
      rw [hgu, LinearEquiv.symm_apply_apply, h, LinearEquiv.apply_symm_apply]
  refine ⟨fun θ hθ => ⟨hsec θ hθ, fun hM => ?_⟩, ?_, hsign⟩
  · obtain ⟨A, Fd, hA, hFd, hmean⟩ := hM
    have hAL : ∀ z, z ∈ A ↔ ψ z ∈ T.L := by
      intro z
      rw [hA z, hL]
      constructor
      · rintro ⟨v, hv, rfl⟩
        exact ⟨v, hv, rfl⟩
      · rintro ⟨v, hv, h⟩
        exact ⟨v, hv, ψ.injective h⟩
    rw [l2_one_eq_integral_fundamentalDomain_div_volume T ψ θ (hsec θ hθ) A hAL Fd hFd]
    simpa only [hH] using hmean
  · intro n k th a z
    simp only [fock, I2.PT.U, Pi.sub_apply, sub_neg_eq_add, map_add, LinearEquiv.symm_apply_apply]
    rw [Finset.prod_mul_distrib, ← Complex.exp_sum]
    congr 1
    congr 1
    simp only [I2.HC, Hf_neg_right, Hf_neg_left, neg_neg, hH, hHadd']
    rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring

end GlobalTheory.Dict.ThetaPT
end

