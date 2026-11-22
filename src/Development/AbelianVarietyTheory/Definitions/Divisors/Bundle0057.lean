import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0038
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0030
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.SlopeBoundSingleLiftOfDefinitions

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl
section
noncomputable section

namespace GlobalTheory.LevPull

open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def IntAt (Xo : Moduli Dw l) (c : Coeff l) (f : Rul Xo c) : Prop := ∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v f

def Pull (d : DeltaDat Xo c 0) (f : Rul Xo c) (g : Rul d.Xo₂ d.c₂) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra d.c₂.F k],
    (∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a) →
    ∀ (y₂ : FrPt d.Xo₂ d.c₂ k) (y : FrPt Xo c k), FrOver d y₂ y → evR d.Xo₂ d.c₂ g y₂ = evR Xo c f y

def FibConst (d : DeltaDat Xo c 0) (g : Rul d.Xo₂ d.c₂) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra d.c₂.F k],
    (∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a) →
    ∀ (y₂ y₂' : FrPt d.Xo₂ d.c₂ k) (y : FrPt Xo c k), FrOver d y₂ y → FrOver d y₂' y →
      evR d.Xo₂ d.c₂ g y₂ = evR d.Xo₂ d.c₂ g y₂'

theorem Pull.fibConst {d : DeltaDat Xo c 0} {f : Rul Xo c} {g : Rul d.Xo₂ d.c₂} (h : Pull d f g) : FibConst d g :=
  fun k _ _ _ _ hk y₂ y₂' y h₁ h₂ => (h k hk y₂ y h₁).trans (h k hk y₂' y h₂).symm

variable (Dw l) in

abbrev LaQ : Type := Dw.La ⧸ (l.Mb • ⊤ : Submodule (𝓞 E) Dw.La)

variable (Dw l) in

abbrev Gam : Type := LaQ Dw l ≃ₗ[𝓞 E] LaQ Dw l

def IsLift (lift : Gam Dw l → Dw.La →ₗ[𝓞 E] Dw.La) : Prop :=
  ∀ γ, (Submodule.mkQ _) ∘ₗ lift γ = γ.toLinearMap ∘ₗ Submodule.mkQ _

def CongMod (I : Ideal (𝓞 E)) (h h' : Dw.La →ₗ[𝓞 E] Dw.La) : Prop :=
  ∀ a, h a - h' a ∈ (I • ⊤ : Submodule (𝓞 E) Dw.La)

end GlobalTheory.LevPull
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.EigLatLe
section
noncomputable section

namespace GlobalTheory.DefPt

open CategoryTheory NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.Frames
  GlobalTheory.CompHt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical

section Point

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

abbrev Mats (Dw : Datum H) (S : Type) : Type := ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S

def part (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → ℕ := fun τ i => a (τ, i)

def Reads (Z : Comp Xo c) (y₀ : FrPt Xo c c.F) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (x : TIdx (part Dw a) → c.F) (f : Rul Xo c) :
    Prop :=
  f ∈ suppOn Z ∧ ∀ (S : Type) [CommRing S] [Algebra c.F S] (z y : FrPt Xo c S) (Y : Mats Dw S) (s : S),
    (∀ τ, IsUnit (Y τ).det) → IsUnit s → FrMap (Algebra.ofId c.F S) y₀ z → FrChg (fun τ => (Y τ)ᵀ) s z y →
      evR Xo c f y = s ^ n * tval (part Dw a) (fun I => algebraMap c.F S (x I)) Y

def LocFr (y₀ : FrPt Xo c c.F) (w : HeightOneSpectrum (𝓞 c.F)) (a : c.F) (B : Mats Dw c.F) : Prop :=
  a ≠ 0 ∧ (∀ τ, (B τ).det ≠ 0) ∧
    ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa w T.V io e → letI := io.toAlgebra
      ∀ y z : FrPt Xo c T.Fr, Integral T io y → FrMap (Algebra.ofId c.F T.Fr) y₀ z → y.x = z.x →
        ∃ (Y : Mats Dw T.V) (u : T.Vˣ), (∀ τ, IsUnit (Y τ).det) ∧
          FrChg (fun τ => ((B τ).map io * (Y τ).map (algebraMap T.V T.Fr))ᵀ) (io a * algebraMap T.V T.Fr u) z y

def ArchFr (y₀ : FrPt Xo c c.F) (σ : c.F →+* ℂ) (N : ℝ) (X : Mats Dw ℂ) : Prop :=
  0 < N ∧ (∀ τ, (X τ).det ≠ 0) ∧
    ∀ z y : FrPt Xo c (CAt σ), FrMap (Algebra.ofId c.F (CAt σ)) y₀ z → FrChg (S := CAt σ) (fun τ => (X τ)ᵀ) 1 z y →
      GlobalTheory.LamT.IsMetric y N fun _ => 1

structure PtData (Z : Comp Xo c) : Type where

  y₀ : FrPt Xo c c.F
  on : LiesOn Z y₀
  only : ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), LiesOn Z y → y.x = spMap (algebraMap c.F S) ≫ y₀.x

  a : HeightOneSpectrum (𝓞 c.F) → c.F

  B : HeightOneSpectrum (𝓞 c.F) → Mats Dw c.F
  loc : ∀ w, LocFr y₀ w (a w) (B w)
  fin : {w | ¬ (a w = 1 ∧ B w = 1)}.Finite

  N : (c.F →+* ℂ) → ℝ

  X : (c.F →+* ℂ) → Mats Dw ℂ
  arch : ∀ σ, ArchFr y₀ σ (N σ) (X σ)

namespace PtData

variable {Z : Comp Xo c} (P : PtData Z)

def degLie (τ : E →+* ℂ) : ℝ := detDeg (fun w => P.B w τ) fun σ => P.X σ τ

def degTh : ℝ := lineDeg (fun σ => (Real.sqrt (P.N σ))⁻¹) fun w => (vAdd w (P.a w) : ℝ)

def matA (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (w : HeightOneSpectrum (𝓞 c.F)) :
    Matrix (TIdx (part Dw a)) (TIdx (part Dw a)) c.F := fibA (part Dw a) (P.a w ^ n) (P.B w)

def matY (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (σ : c.F →+* ℂ) :
    Matrix (TIdx (part Dw a)) (TIdx (part Dw a)) ℂ := fibY (part Dw a) ((Real.sqrt (P.N σ))⁻¹ ^ n) (P.X σ)

end PtData

variable {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (ξ : ℝ)

def FibreAt (Z : Comp Xo c) (G : WTZ E) (s : ℝ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (_ : Nonempty ι) (L : Submodule (𝓞 c.F) (ι → c.F))
    (Y : (c.F →+* ℂ) → Matrix ι ι ℂ) (φ : (ι → c.F) →ₗ[c.F] Rul Xo c),
    Submodule.IsLattice c.F L ∧ (∀ σ, (Y σ).det ≠ 0) ∧ s ≤ slope_sq (matNorm Y) L / 2 ∧ Function.Injective φ ∧
    LinearMap.range φ = cuspOn U Z G ∧ (∀ x ∈ L, ∀ w, ∀ v ∈ valSet Xo c (algCls Xo c) w, 0 ≤ v (φ x)) ∧
    ∀ σ x, ∀ z ∈ framesOn (U (goodOf c σ)) Z, homN (U (goodOf c σ)) ξ G (φ x) z ≤ matNorm Y σ x

def defBound (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (c₁ : ℝ) : ℝ :=
  (∑ τ : Psi H, (((size (part Dw a τ.1) : ℝ) / Dw.p + (n : ℝ) / 2) * c₁ - Real.log (dim (part Dw a τ.1)) / 2)) +
    (n : ℝ) * ((Fintype.card (Psi H) : ℝ) * Dw.p) * (Real.log (2 * Real.pi) / 4 - GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd E / 2)

structure DefCase : Prop where
  q : Dw.q = 0
  p : 1 ≤ Dw.p
  good : ∀ p : ℕ, p.Prime → l.GoodAt p
  A : l.A = 1
  geo : FnAlgClosed Xo c
  unf : ∀ σ, GoodEmb c σ → IsUnf (U σ)
  xi : ∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = ξ

variable (Xo c) in

def FreePt {G : Type} [Group G] (lev : G → (Dw.La →ₗ[𝓞 E] Dw.La) × (Dw.La →ₗ[𝓞 E] Dw.La)) : Prop :=
  ∀ (g : G) (k : Type) [Field k] [Algebra c.F k] (y y' : FrPt Xo c k), levR (lev g) y y' → y'.x = y.x → g = 1

example (lev : Unit → (Dw.La →ₗ[𝓞 E] Dw.La) × (Dw.La →ₗ[𝓞 E] Dw.La)) :
    FreePt Xo c (G := Multiplicative Unit) lev := fun _ _ _ _ _ _ _ _ => rfl

end Point

section Eigen

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) {G : Type} [Group G]
  (lev : G → (Dw.La →ₗ[𝓞 D.host.E] Dw.La) × (Dw.La →ₗ[𝓞 D.host.E] Dw.La)) (χ : G →* (c.F)ˣ)

set_option synthInstance.maxHeartbeats 400000 in

def eigSub : Submodule c.F (Rul Xo c) :=
  ⨅ g : G, LinearMap.ker (actLev (Xo := Xo) c lev g - ((χ g : (c.F)ˣ) : c.F) • (LinearMap.id : Rul Xo c →ₗ[c.F] Rul Xo c))

def eigLat (W : WTZ D.host.E) : Submodule (𝓞 c.F) (cuspW Xo c U W) :=
  latW U W ⊓ ((eigSub lev χ).comap (cuspW Xo c U W).subtype).restrictScalars (𝓞 c.F)

theorem eigLat_le (W : WTZ D.host.E) : eigLat U lev χ W ≤ latW U W := inf_le_left

end Eigen

end GlobalTheory.DefPt

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DegCmp

open NumberField GlobalTheory.AllWt GlobalTheory.CompHt
open scoped ENNReal

section Generic

variable {K V Ω : Type} [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω]

def hilb (ev : V →ₗ[K] Ω) (τ : ℕ) : ℕ∞ :=
  Cardinal.toENat (Module.rank K (↥((LinearMap.range ev) ^ τ : Submodule K Ω)))

def coneAlg (ev : V →ₗ[K] Ω) : Subalgebra K (Polynomial Ω) :=
  Algebra.adjoin K (Set.range fun v => Polynomial.X * Polynomial.C (ev v))

def IsIntDeg (ev : V →ₗ[K] Ω) (τ : ℕ) (t : Ω) : Prop :=
  IsIntegral (coneAlg ev) (Polynomial.X ^ τ * Polynomial.C t : Polynomial Ω)

def IsRatio (ev : V →ₗ[K] Ω) (τ : ℕ) (t : Ω) : Prop :=
  ∃ (e : ℕ) (h : Ω), h ∈ ((LinearMap.range ev) ^ e : Submodule K Ω) ∧ h ≠ 0 ∧
    t * h ∈ ((LinearMap.range ev) ^ (τ + e) : Submodule K Ω)

example (ev : V →ₗ[K] Ω) (v : V) : IsRatio ev 1 (ev v) ∧ IsIntDeg ev 1 (ev v) := by
  refine ⟨⟨0, 1, by simp [Submodule.one_eq_span], one_ne_zero, by simp⟩, ?_⟩
  have h : Polynomial.X * Polynomial.C (ev v) ∈ coneAlg ev := Algebra.subset_adjoin ⟨v, rfl⟩
  rw [IsIntDeg, pow_one]
  exact isIntegral_algebraMap (R := coneAlg ev) (x := ⟨_, h⟩)

end Generic

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Indef.Tree

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ)

def UnfAll : Prop := ∀ σ, GoodEmb c σ → IsUnf (U σ)

def Proport : Prop :=
  ∀ (Z : Comp Xo c) (la : Weight Dw), (∀ τ, StrictAnti (la τ)) →
    growthOn U Z (wtOf Dw la 0) = ENNReal.ofReal (topDeg U Z la)

def EqVolume : Prop := ∀ Z Z' : Comp Xo c, vZero U Z = vZero U Z'

def RatioOn (Z : Comp Xo c) (G : WTZ E) : Prop :=
  ∀ (τ : ℕ), ∀ t ∈ cuspOn U Z (τ • G), IsRatio (genPoint Z (cuspOn U Z G)) τ (genVal Z t)

def BoundedBy (Z : Comp Xo c) (σ : c.F →+* ℂ) (G₁ : WTZ E) (t : Rul Xo c) (G : WTZ E) (τ : ℕ) : Prop :=
  ∃ (n : ℕ) (w : Fin n → cuspOn U Z G) (C : ℝ), ∀ z ∈ framesOn (U σ) Z,
    homN (U σ) x G₁ t z ^ 2 ≤ C * (∑ i, homN (U σ) x G (w i : Rul Xo c) z ^ 2) ^ τ

def Multiplier (Z : Comp Xo c) (G G' : WTZ E) : Prop :=
  ∃ (a : ℕ) (θ : Rul Xo c), 1 ≤ a ∧ θ ∈ secZ Xo c (exZ Dw (a • (G - G'))) ∧ genVal Z θ ≠ 0 ∧
    (∀ (k : ℕ), ∀ f ∈ cuspOn U Z ((a * k) • G'), θ ^ k * f ∈ cuspOn U Z ((a * k) • G)) ∧
    ∃ σ, GoodEmb c σ ∧ BoundedBy U x Z σ (a • (G - G')) θ G a

def DegTie {K : Type} [Field K] [NumberField K] [StarRing K] {P : SlopeBoundParameters} (F : SlopeBoundLiftData K P) (u : Weight Dw) : Prop :=
  (∃ e : F.ι → Comp Xo c, ∀ k, F.δc k = compDeg U (e k) (wtOf Dw u 0)) ∧
    (∃ Z : Comp Xo c, F.δ' = delPrime U Z u) ∧ F.ρ = rhoB Dw u

end GlobalTheory.DegCmp
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.NotIsChowFormIntLineZero
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHt.Test

open MvPolynomial NumberField IsDedekindDomain Module Filter GlobalTheory.ChowHt GlobalTheory.AllWt GlobalTheory.CompHt
open scoped ENNReal

set_option autoImplicit false in
open MvPolynomial NumberField IsDedekindDomain Module Filter in
open scoped ENNReal in

theorem _root_.GlobalTheory.CompHt.Test.imageDeg_zero {K V Ω : Type} [Field K] [AddCommGroup V] [Module K V]
    [Field Ω] [Algebra K Ω] (D : ℕ) :
    _root_.GlobalTheory.CompHt.imageDeg (0 : V →ₗ[K] Ω) D = 0 := by
  by_contra hne
  obtain ⟨N, b, f, hf⟩ := (_root_.GlobalTheory.CompHt.imageDeg_pos_iff _ D).1 (Nat.pos_of_ne_zero hne)
  obtain ⟨y, hy, hI⟩ := hf.exists_point
  apply hy
  funext i
  have hX : (X i : MvPolynomial (Fin N) K) ∈ _root_.GlobalTheory.CompHt.imageIdeal (0 : V →ₗ[K] Ω) b := by
    unfold _root_.GlobalTheory.CompHt.imageIdeal
    rw [_root_.GlobalTheory.CompHt.mem_coneIdeal_of_isHomogeneous _ (isHomogeneous_X K i)]
    simp
  simpa using hI _ hX

theorem not_isChowFormInt_line_zero {K : Type} [Field K] {δ : ℕ} {g : MvPolynomial (Fin (0 + 1) × Fin 2) K}
    (hf' : IsChowFormInt (⊥ : Ideal (MvPolynomial (Fin 2) K)) 0 δ g) : False := by
  refine hf'.ne_zero ?_
  apply MvPolynomial.map_injective (algebraMap K (AlgebraicClosure K)) (algebraMap K _).injective
  rw [map_zero]
  refine MvPolynomial.funext fun u => ?_
  rw [map_zero, eval_map, ← aeval_def, hf'.zero_iff]
  by_cases hu : u (0, 0) = 0
  · refine ⟨![1, 0], by simp, fun g hg => by rw [Ideal.mem_bot.1 hg, map_zero], fun i => ?_⟩
    fin_cases i
    simp [Fin.sum_univ_two, hu]
  · refine ⟨![u (0, 1), -u (0, 0)], by simp [hu], fun g hg => by rw [Ideal.mem_bot.1 hg, map_zero], fun i => ?_⟩
    fin_cases i
    simp [Fin.sum_univ_two, mul_comm]

theorem imageDeg_line_zero : imageDeg (stdPoint 2) 0 = 0 := by
  by_contra h
  obtain ⟨N, b, f, hf⟩ := (imageDeg_pos_iff _ 0).1 (Nat.pos_of_ne_zero h)
  have hf' := isChowFormInt_basis _ b (Pi.basisFun ℚ (Fin 2)) hf
  rw [imageIdeal_std] at hf'
  exact not_isChowFormInt_line_zero hf'

theorem countVol_two_pow {d a : ℕ} (ha : a ≠ 0) :
    countVol 1 d a (fun τ => ((2 ^ (τ ^ 2) : ℕ) : ℕ∞)) = ENNReal.ofReal (Real.log 2) / d := by
  rw [countVol, ← limsup_const (f := (atTop : Filter ℕ)) (ENNReal.ofReal (Real.log 2) / d)]
  refine limsup_congr ((eventually_ne_atTop 0).mono fun k hk => ?_)
  have h0 : ((a * k : ℕ) : ℝ≥0∞) ^ 2 ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (mul_ne_zero ha hk))
  have h1 : ((a * k : ℕ) : ℝ≥0∞) ^ 2 ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)
  rw [logCard_coe, Nat.cast_pow, Real.log_pow, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
    Nat.factorial_one, Nat.cast_one, one_mul, Nat.cast_pow, mul_comm _ (ENNReal.ofReal _),
    ENNReal.mul_div_mul_right _ _ h0 h1]
  norm_num

theorem volSlope_zero {δ : ℝ} : volSlope δ (fun _ => 0) = ⊥ := by
  rw [volSlope, EReal.eq_bot_iff_forall_lt]
  intro y
  refine (iInf_le _ (1 - y)).trans_lt ?_
  simp only [ENNReal.zero_div, EReal.coe_ennreal_zero, zero_sub, ← EReal.coe_neg, EReal.coe_lt_coe_iff]
  linarith

theorem dim_count (p q : ℕ) : p * q + p * (p - 1) / 2 + q * (q - 1) / 2 = (p + q) * (p + q - 1) / 2 := by
  rw [← Nat.choose_two_right, ← Nat.choose_two_right, ← Nat.choose_two_right, Nat.add_choose_eq]
  simp [Finset.Nat.antidiagonal_succ]
  ring

theorem isShortGen_std (N : ℕ) : IsShortGen (stdNorm N) (stdLat N) (Pi.basisFun ℚ (Fin N)) 1 := by
  refine ⟨fun x => ⟨fun hx => ?_, fun hx => ?_⟩, fun i σ => ?_, le_rfl⟩
  · induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span hy
    | zero => exact zero_mem _
    | add y z _ _ hy hz => exact add_mem hy hz
    | smul a y _ hy =>
      obtain ⟨n, rfl⟩ := Rat.ringOfIntegersEquiv.symm.surjective a
      have : Rat.ringOfIntegersEquiv.symm n = (n : 𝓞 ℚ) := eq_intCast _ n
      rw [this, Int.cast_smul_eq_zsmul]
      exact Submodule.smul_mem _ _ hy
  · exact Submodule.span_le_restrictScalars ℤ (𝓞 ℚ) _ hx
  · simp [stdNorm, Pi.single_apply, apply_ite]

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

theorem exps_stdWt (τ : Psi H) (i j : ℕ) (hi : i < Dw.p) (hj : j < Dw.q) :
    (wtOf Dw (stdWt (Psi H) (Dw.p + Dw.q)) 0).1 (τ.1, i) = (Dw.p + Dw.q : ℤ) - 1 - i ∧
      (wtOf Dw (stdWt (Psi H) (Dw.p + Dw.q)) 0).1 (conjEmb τ.1, j) = -(j : ℤ) := by
  rw [wtOf_big _ _ _ _ hi, wtOf_small _ _ _ _ hj]
  simp only [stdWt]
  omega

theorem exps_hodgeWt (τ : Psi H) (i j : ℕ) (hi : i < Dw.p) (hj : j < Dw.q) :
    (wtOf Dw (hodgeWt Dw) 0).1 (τ.1, i) = 0 ∧ (wtOf Dw (hodgeWt Dw) 0).1 (conjEmb τ.1, j) = 1 := by
  rw [wtOf_big _ _ _ _ hi, wtOf_small _ _ _ _ hj]
  simp [hodgeWt, barWt, hi]

variable (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)

theorem valL_vw_one_nonneg (G : WTZ E) (v : Rul Xo c → EReal) (h1 : depth_vw U G v ≠ ⊤) (h2 : depth_vw U G v ≠ ⊥)
    {w : cuspW Xo c U G} (hw : w ∈ latW U G) : 0 ≤ valL_vw U G 1 v w := by
  rw [valL_vw, Nat.cast_one, one_mul, EReal.sub_nonneg (Or.inr h1) (Or.inr h2)]
  exact iInf₂_le w hw

theorem valL_vw_base (G : WTZ E) (v : Rul Xo c → EReal) (h : depth_vw U G v = ⊤) (τ : ℕ) (t : Rul Xo c) :
    valL_vw U G (τ + 1) v t = ⊥ := by
  rw [valL_vw, h, EReal.mul_top_of_pos (by exact_mod_cast Nat.succ_pos τ), EReal.sub_top]

end GlobalTheory.CompHt.Test
end
end

