import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice

-- bundled from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AbsOfRange
section
noncomputable section
open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace ENNReal
namespace GlobalTheory.Amp.RangeModel

example : @HypZ = @Formalism.MainNotions.S.Cnt.Hyp0 := rfl
example : @MomIn = @Formalism.MainNotions.S.UnitaryVolumeMass.stMOM := rfl
example : @SchurSt = @Formalism.MainNotions.S.UnitaryVolumeMass.stSchur := rfl

theorem abs_of_range (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 A Cn C1 C : ℝ) (hn : 0 ≤ Cn)
    (h : ABSr D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 C) :
    Formalism.MainNotions.S.UnitaryVolumeMass.stABS D large₂ C' Cl Cg cb Cu cT CT C0 A C1 C ∧
      Formalism.MainNotions.S.UnitaryVolumeMass.stABSconv D large₂ C' Cl Cg cb Cu cT CT C0 A C1 := by
  have h0 : ∀ τ, l1dist (lamD D τ) (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 := fun τ => by
    simp only [l1dist, sub_self, abs_zero, Finset.sum_const_zero]; positivity
  constructor
  · intro τ w w' hT θ hθ W hW S hS _ γ p hp θ' hθ' ν hν hH hD
    exact (h hH.1 τ w w' hT θ hθ W hW _ (h0 τ) S hS γ p hp θ' hθ' ν hν hD).2
  · intro τ w w' hT θ hθ W hW S hS _ γ p hp θ' hθ' ν hν hH hD
    exact (h hH.1 τ w w' hT θ hθ W hW _ (h0 τ) S hS γ p hp θ' hθ' ν hν hD).1

theorem vand_pos {n : ℕ} {x : Fin n → ℝ} (h : StrictAnti x) : 0 < Formalism.MainNotions.S.vand x :=
  Finset.prod_pos fun _ _ => Finset.prod_pos fun _ hb => sub_pos.2 (h (Finset.mem_filter.1 hb).2)

theorem deg_eq (D : D7) (h : DegVand D) (W : LocW D.R.k D.R.rS) (l) (A₁ A₂ : LocS W)
    (h₁ : GoodS D l A₁) (h₂ : GoodS D l A₂) : A₂.deg = A₁.deg :=
  mul_right_cancel₀ (vand_pos h₁.1.1).ne' (h W l l A₁ A₂ h₁ h₂)

theorem deg_ratio (D : D7) (h : DegVand D) (W : LocW D.R.k D.R.rS) (l₁ l₂) (A₁ A₂ : LocS W)
    (h₁ : GoodS D l₁ A₁) (h₂ : GoodS D l₂ A₂) :
    A₂.deg / A₁.deg = Formalism.MainNotions.S.vand l₂ / Formalism.MainNotions.S.vand l₁ := by
  obtain ⟨P, -, hd, -⟩ := h₁.2.2.2.2.2.2.2.2.2.2
  rw [div_eq_div_iff hd.ne' (vand_pos h₁.1.1).ne', h W l₁ l₂ A₁ A₂ h₁ h₂, mul_comm]

theorem sizes_of (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ) (hb : D.host.rdE ≤ large₂.sc.b)
    (h : HypZ D large₂ C' Cl Cg cb Cu cT CT C0) : Sizes D large₂ Cl Cg CT := by
  obtain ⟨⟨-, -, hmf, hfk, -, -, -, -, -, -, -, hg1, hg1', hg2, hg2', -, -, -, hv, -, -, hgap, hT, hCl, hCl0⟩, -, -⟩ := h
  have hL : 1 < large₂.sc.L := Real.one_lt_rpow large₂.sc.one_lt_alt large₂.sc.eps_pos
  have hbe : Real.exp 1 < large₂.sc.b := Real.exp_lt_exp.2 hL
  have hb1 : 1 < large₂.sc.b := lt_trans (by simpa using Real.exp_lt_exp.2 (zero_lt_one (α := ℝ))) hbe
  have hm : D.R.m = 2 * D.R.rS + 2 := by
    have := D.R.two_le_m; obtain ⟨a, ha⟩ := D.R.m_even; unfold Ranks.rS; omega
  have hr : D.R.r = 2 * D.R.rS + D.R.k + 1 := by unfold Ranks.r; omega
  have hk : (1 : ℝ) ≤ D.R.k := by have := D.R.m_add_three_le_k; exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hkb : (1 : ℝ) ≤ D.R.k * large₂.sc.b := by nlinarith
  have h8 : (1 : ℝ) ≤ (D.R.k * large₂.sc.b) ^ 8 := one_le_pow₀ hkb
  have hrd : D.host.rdE = 2 * D.host.v := by unfold Host.v; ring
  have hgg : 1 ≤ gg D := by unfold gg; nlinarith
  have hu : ∀ w τ, StrictAnti (uS D w τ) := fun w τ => by
    have hk0 : D.R.k = (D.R.k - 1) + 1 := by have := D.R.m_add_three_le_k; omega
    have key : ∀ (i : ℕ) (hi : i + 1 < D.R.k), uS D w τ ⟨i + 1, hi⟩ < uS D w τ ⟨i, by omega⟩ := fun i hi => by
      have a := (D.hcW w τ).u_gt_v ⟨i, by omega⟩
      have b := (D.hcW w τ).v_gt_u ⟨i, by omega⟩
      unfold uS; exact_mod_cast b.trans a
    rintro ⟨a, ha⟩ ⟨c, hc⟩ hac
    have hac' : a < c := hac
    induction c, hac' using Nat.le_induction with
    | base => exact key a hc
    | succ c hc' ih => exact (key c hc).trans (ih (by omega) hc')
  refine ⟨hL, Real.log_exp _, hbe, hm, hr, D.what₂.card_Tau, hCl, hmf.trans hfk, hv, hrd, rfl, hrd ▸ hb, hgg, ?_, ?_, ?_,
    fun w => (hT w).2, fun w τ => ⟨vand_pos (hu w τ), ?_⟩, ?_⟩
  · rw [two_mul, Real.rpow_add (by linarith)]
    exact mul_le_mul hg1' hg2' (by linarith) (by linarith)
  · have : large₂.sc.b ^ (8 : ℝ) ≤ large₂.sc.b ^ Cg := by
      refine le_trans ?_ (hg1.trans hg1')
      rw [show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      exact pow_le_pow_left₀ (by linarith) (by nlinarith) 8
    exact (Real.rpow_le_rpow_left_iff hb1).1 this
  · refine le_trans ?_ (hg1.trans hg1')
    exact le_trans (by nlinarith) (le_self_pow₀ hkb (by norm_num))
  · have h1 : 0 < D.host.ka := div_pos Real.pi_pos (by linarith)
    have h2 : 0 < D.host.rdE := by linarith
    have h3 : 0 < gg D := by linarith
    have h4 : 0 < VV D τ := mul_pos (D.dsig_pos τ) (Finset.prod_pos fun i _ => by positivity)
    have h5 := vand_pos (hu w τ)
    unfold Tcrit; positivity
  · intro τ
    have hp : 0 ≤ Cl * D.R.k * (D.R.m : ℝ) ^ 4 := by positivity
    have key : ∀ (i : ℕ) (hi : i + 1 < 2 * D.R.rS + D.R.k + 1),
        Cl * D.R.k * (D.R.m : ℝ) ^ 4 < lamD D τ ⟨i, by omega⟩ - lamD D τ ⟨i + 1, hi⟩ := fun i hi => by
      have := hgap τ ⟨i, by omega⟩ (by simpa [hr] using hi)
      have h0 : (0 : ℝ) ≤ D.R.r * (D.R.m : ℝ) ^ 10 := by positivity
      exact lt_of_le_of_lt (le_add_of_nonneg_right h0) this
    rintro ⟨a, ha⟩ ⟨c, hc⟩ hac
    have hac' : a < c := hac
    induction c, hac' using Nat.le_induction with
    | base => exact key a hc
    | succ c hc' ih =>
      have := key c hc
      have := ih (by omega) hc'
      linarith

theorem theta_pos (D : D7) (τ w w') (θ : ℝ) (W : LocW D.R.k D.R.rS) (h : GoodW D τ w w' θ W) : 0 < θ := by
  by_contra hθ
  obtain ⟨-, -, -, -, -, -, hG, -, -, -, -, hN, hq, -⟩ := h
  have hv : 0 ≤ D.host.v := by unfold Host.v Host.rdE; positivity
  have h0 : kapN D θ = 0 := ENNReal.ofReal_eq_zero.2
    (mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg (by linarith) _) (not_lt.1 hθ))
  have hN0 : W.μN = 0 := by rw [hN, h0]; simp [haarLie]
  have := hq (fun _ => 1) measurable_const
  simp [muS, hN0] at this
  exact hG.2.1 this

end GlobalTheory.Amp.RangeModel
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc

namespace GlobalTheory.LocOver

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def Uni {K : Type} [Zero K] [One K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K) : Prop :=
  (∀ a b, b < a → A a b = 0) ∧ ∀ a, A a a = 1

def Chg {K W : Type} [Semiring K] [AddCommMonoid W] [Module K W] {n : ℕ} (f : Fin n → W)
    (A : Matrix (Fin n) (Fin n) K) (g : Fin n → W) : Prop :=
  ∀ b, g b = ∑ a, A a b • f a

def Tri (K : Type) {W : Type} [Semiring K] [AddCommMonoid W] [Module K W] {n : ℕ} (f g : Fin n → W) : Prop :=
  ∃ A : Matrix (Fin n) (Fin n) K, Uni A ∧ Chg f A g

section Loc

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {r : ℕ}

def move (g : V ≃ₗ[E] V) (t : Term V M r) : Term V M r where
  abelian₂ := img g t.abelian₂
  f b := g (t.f b)
  f' b := g (t.f' b)
  T := t.T
  T' := t.T'

def Over {H : HermSp M V} (P : FPair H r) (d : Datum P) (t : Term V M r) : Prop :=
  ∃ g : V ≃ₗ[E] V, IsUnitary H g ∧ ∃ d' : Datum P, Datum.Rel d d' ∧ IsTermOver P d' (move g t)

def NU (H : HermSp M V) (f : Fin (r + 1) → V) : Set (V ≃ₗ[E] V) :=
  {n | IsUnitary H n ∧
    (∀ a : Fin r, n (f a.castSucc) - f a.castSucc ∈
      Submodule.span E ((fun b : Fin r => f b.castSucc) '' {b | b < a})) ∧
    ∀ v ∈ H.perp (H.X f), n v - v ∈ H.X f}

def Cong (H : HermSp M V) (Λ : Submodule M.L.O V) (f f' : Fin (r + 1) → V) (x : V) : Prop :=
  ∃ a ∈ H.smulLat (algebraMap F E (theta M)) Λ, ∃ b ∈ Λ, ∃ c ∈ Λ, b ∈ H.X f ∧ c ∈ H.X f' ∧ x = a + b + c

end Loc

section Glob

variable {D : D7}

def scaled (Z : LocDat D) (p : PlF D) (f : Fin (D.R.rS + 1) → (VS D).V) : Fin (D.R.rS + 1) → Vp D p :=
  fun a => frFac Z.δ p a • baseChange₂ D p (f a)

def locU (Z : LocDat D) (p : PlF D) (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' : D.host.E}
    (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') (Tn T'n : ℕ) : Loc.Term (Vp D p) (Z.M p) D.R.rS where
  abelian₂ := lattice₂ D Z.M p Λ
  f a := frFac Z.δ p a • baseChange₂ D p (frame F a)
  f' b := frFac Z.δ p b • baseChange₂ D p (frameAct (frame F') (admXi D Λ F F')⁻¹ b)
  T := (Tn : (D.s.atP p).Fp)
  T' := (T'n : (D.s.atP p).Fp)

def AtBase (Z : LocDat D) (p : PlF D) {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T')
    (Tn T'n : ℕ) (P : LocNG.FPair (locH Z p) D.R.rS) : Prop :=
  P.A.f = scaled Z p (frame F) ∧ P.B.f = scaled Z p (frame F') ∧
    P.A.T = (Tn : (D.s.atP p).Fp) ∧ P.B.T = (T'n : (D.s.atP p).Fp)

def Ext (p : PlF D) (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) : Prop :=
  ∀ x, g (baseChange₂ D p x) = baseChange₂ D p (γ x)

end Glob

end GlobalTheory.LocOver
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SiegelMeanCc
section
open MeasureTheory NumberField Matrix Finset IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.GaussMean

open Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice

def OneVectorCc : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    SW1a1 F E σ M J ∧
    (3 ≤ M → ∀ (β : F), β ≠ 0 → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E)
      (Φ : (Fin 1 → Fin M → AF F ⊗[F] E) → ℂ) (Φi : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℂ)
      (Φf : (Fin 1 → Fin M → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) → ℂ)
      (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin 1 → Fin M → Fv F v ⊗[F] E) → ℂ),
      Continuous Φi → HasCompactSupport Φi →
      (∀ (N : ℕ) (e : (Fin 1 → Fin M → Ainf F ⊗[F] E) ≃+ (Fin N → ℝ)), Continuous e → Continuous e.symm →
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Φi ∘ e.symm)) →
      IsPureFin b Φf Φv → IsProdInfFin Φ Φi Φf →
      AllSome (IsCharAF F) fun ψ =>
      OnH F E σ M J fun μ 𝓕 =>
      OnSD F E σ M J ψ 1 (Ainf F) (Fv F) (fun s t => psiInf F ψ (s * t)) (fun v s t => psiV F ψ v (s * t))
        fun μi νi μv νv =>
        ∃ (Fi : Ainf F → ℂ) (Fl : ∀ v, Fv F v → ℂ),
          IsContDensityOn μi (fun X => qR (Ainf F) σ J (X 0)) id νi {c | IsUnit c} Φi Fi ∧
          (∀ v, IsContDensityOn (μv v) (fun X => qR (Fv F v) σ J (X 0)) id (νv v) {c | c ≠ 0} (Φv v) (Fl v)) ∧
          Multipliable (fun v => Fl v (algebraMap F (Fv F v) β)) ∧
          meanC μ 𝓕 (thSum F E σ M J Φ {x | hE σ J (x 0) (x 0) = algebraMap F E β}) =
            Fi (algebraMap F (Ainf F) β) * ∏' v, Fl v (algebraMap F (Fv F v) β))

def IsDens {n : ℕ} (ε : Fin n → Bool) (φ : (Fin n → ℂ) → ℝ) (D : ℝ → ℝ) : Prop :=
  ContinuousOn D {t | t ≠ 0} ∧ ∀ S : Set ℝ, IsCompact S → S ⊆ {t | t ≠ 0} →
    ∫ y in {y | qEps ε y ∈ S}, φ y = ∫ t in S, D t

def SiegelMeanCc : Prop :=
  ∀ (I : AutInst), 3 ≤ I.n → ∀ (s : Bool) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure]
    (fund : Set I.GA), I.IsFundDom (I.muA μf) fund →
    I.muA μf fund < ⊤ ∧
    ∀ (φ : InfinitePlace I.F → (Fin I.n → ℂ) → ℝ) (D : InfinitePlace I.F → ℝ → ℝ),
      (∀ v, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (φ v) ∧ HasCompactSupport (φ v) ∧ (∀ y, 0 ≤ φ v y) ∧
        IsDens (I.ε v) (φ v) (D v)) →
      ∫⁻ x in fund, (∑' y : {y : Fin I.n → I.E // y ∈ lamX I x ∧ star y ⬝ᵥ (I.J *ᵥ y) = sgn I.E s},
          ENNReal.ofReal (∏ v, φ v (((uMat (x.1 v))⁻¹ * (I.P v)⁻¹) *ᵥ fun i => I.φ v (y.1 i)))) ∂(I.muA μf) =
        I.muA μf fund * ENNReal.ofReal (meanConst I.E I.n * ∏ v, D v (sgn ℝ s))

end GlobalTheory.GaussMean
end
end

