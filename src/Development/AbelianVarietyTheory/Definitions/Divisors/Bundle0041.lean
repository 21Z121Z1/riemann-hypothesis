import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle0018
import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPowMod

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace ContDiff

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict

abbrev Mt (n : ℕ) : Type := Matrix (Fin n) (Fin n) ℂ

section Local

variable {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

def frDom (Hm : Mt n) (q : ℕ) : Set (Mt n) :=
  {x | x.det ≠ 0 ∧ ∀ i : Fin (n + 1),
    0 < ReciprocityTheory.ChartRestriction.G.FD.psgn q i * (ReciprocityTheory.ChartRestriction.G.FD.lminor (-(xᴴ * Hm * x)) i).re}

def UpT (b : Mt n) : Prop := b.det ≠ 0 ∧ ∀ a c : Fin n, c < a → b a c = 0

def OrthFr (Hm : Mt n) (q : ℕ) (x₀ : Mt n) : Prop :=
  q ≤ n ∧ x₀ᴴ * Hm * x₀ = diagonal fun a : Fin n => -((ReciprocityTheory.ChartRestriction.G.FD.sgn q (a : ℕ) : ℝ) : ℂ)

def UG (Hm : ι → Mt n) : Set (ι → Mt n) := {u | ∀ τ, u τ ∈ Formalism.QuantumDeterminants.UH (Hm τ)}

def frDoms (Hm : ι → Mt n) (q : ι → ℕ) : Set (ι → Fin n → Fin n → ℂ) := {x | ∀ τ, Matrix.of (x τ) ∈ frDom (Hm τ) (q τ)}

def HolSec (Hm : ι → Mt n) (q : ι → ℕ) (w : ι → Fin n → ℤ) (P : (ι → Fin n → Fin n → ℂ) → ℂ) : Prop :=
  DifferentiableOn ℂ P (frDoms Hm q) ∧
    ∀ x ∈ frDoms Hm q, ∀ b : ι → Mt n, (∀ τ, UpT (b τ)) →
      P (fun τ => (Matrix.of (x τ) * b τ : Mt n)) = (∏ τ, ∏ a, b τ a a ^ w τ a) * P x

def HolFn (Hm : ι → Mt n) (q : ι → ℕ) (x₀ : ι → Mt n) (w : ι → Fin n → ℤ) (f : (ι → Mt n) → ℂ) : Prop :=
  ∃ P, HolSec Hm q w P ∧ ∀ u ∈ UG Hm, f u = P fun τ => (u τ * x₀ τ : Mt n)

def lieH (Hm : Mt n) : Set (Mt n) := {X | Xᴴ * Hm + Hm * X = 0}

def SmFn (Hm : ι → Mt n) (f : (ι → Mt n) → ℂ) : Prop :=
  ∀ (k : ℕ) (τs : Fin k → ι) (Xs : Fin k → Mt n), (∀ i, Xs i ∈ lieH (Hm (τs i))) → ∀ u ∈ UG Hm,
    ContDiff ℝ ∞ fun t : Fin k → ℝ =>
      f (u * (List.ofFn fun i => (Pi.mulSingle (τs i) (NormedSpace.exp (t i • Xs i)) : ι → Mt n)).prod)

def der (τ : ι) (X : Mt n) (f : (ι → Mt n) → ℂ) (u : ι → Mt n) : ℂ :=
  deriv (fun t : ℝ => f (u * (Pi.mulSingle τ (NormedSpace.exp (t • X)) : ι → Mt n))) 0

def conjH (Hm Z : Mt n) : Mt n := -(Hm⁻¹ * Zᴴ * Hm)

def derC (Hm : ι → Mt n) (τ : ι) (Z : Mt n) (f : (ι → Mt n) → ℂ) (u : ι → Mt n) : ℂ :=
  der τ ((1 / 2 : ℂ) • (Z + conjH (Hm τ) Z)) f u + Complex.I * der τ ((1 / (2 * Complex.I)) • (Z - conjH (Hm τ) Z)) f u

def KilledFn (Hm : ι → Mt n) (x₀ : ι → Mt n) (w : ι → Fin n → ℤ) (f : (ι → Mt n) → ℂ) : Prop :=
  ∀ τ (a c : Fin n), a ≤ c → ∀ u ∈ UG Hm,
    derC Hm τ (x₀ τ * Matrix.single a c 1 * (x₀ τ)⁻¹) f u = if a = c then (w τ a : ℂ) * f u else 0

def torEl (x₀ : ι → Mt n) (s : ι → Fin n → ℝ) : ι → Mt n :=
  fun τ => x₀ τ * diagonal (fun a => Complex.exp ((s τ a : ℂ) * Complex.I)) * (x₀ τ)⁻¹

def torCh (w : ι → Fin n → ℤ) (s : ι → Fin n → ℝ) : ℂ := ∏ τ, ∏ a, Complex.exp ((s τ a : ℂ) * Complex.I) ^ w τ a

def dRepC {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (Hm : Mt n) (σ : Mt n → (H →L[ℂ] H)) (Z : Mt n) (v : H) : H :=
  dRep σ ((1 / 2 : ℂ) • (Z + conjH Hm Z)) v + Complex.I • dRep σ ((1 / (2 * Complex.I)) • (Z - conjH Hm Z)) v

def gelfRep {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (Hm : Mt n) (σ : Mt n → (H →L[ℂ] H)) (k : ℕ) (v : H) : H :=
  ∑ idx : Fin (k + 1) → Fin n,
    (List.ofFn fun a : Fin (k + 1) => dRepC Hm σ (Matrix.single (idx a) (idx (a + 1)) 1)).foldr (fun f acc => f acc) v

def InZe (Hm : Mt n) (e : Fin n → ℂ) (m : Mt n) : Prop :=
  ∃ s : ℝ, m = 1 + ((s : ℂ) * Complex.I) • vecMulVec e (star e ᵥ* Hm)

end Local

section Adelic

variable {D : D7}

def HolShape {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) : Prop :=
  ∀ τ, Formalism.QuantumDeterminants.IsHCParam (M.lam τ) ∧ ∃ p ≤ V.rank, ∀ a, M.ε τ a = decide ((a : ℕ) < p)

def WtIs {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ) : Prop :=
  ∀ τ c, (w τ c : ℝ) = extWt M τ (arr (nNeg (M.ε τ)) c)

open Classical in

def HolAd (θ : InfFam D) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ)
    (φ : GA D V → ℂ) : Prop :=
  ∀ g, ∃ f, HolFn (gramAt D V) (fun τ => nNeg (M.ε τ)) (x0Mat M) w f ∧
    ∀ u ∈ GinfC V, φ (g * u) = f fun τ => archM V (θ τ) u

def ZI (V : HSp D) (ξ : Fin V.rank → D.host.E) : Subgroup (GA D V) :=
  Subgroup.closure {g | ∃ a : AF D.host.F ⊗[D.host.F] D.host.E,
    ((matHom V g).1 - 1 : Matrix (Fin V.rank) (Fin V.rank) (AF D.host.F ⊗[D.host.F] D.host.E)) =
      a • (vecMulVec ξ ((fun i => (D.sp.cm.sig : D.host.E →+* D.host.E) (ξ i)) ᵥ* V.gram)).map (incA D)}

def IsoVec (V : HSp D) (ξ : Fin V.rank → D.host.E) : Prop :=
  ξ ≠ 0 ∧ (fun i => (D.sp.cm.sig : D.host.E →+* D.host.E) (ξ i)) ⬝ᵥ V.gram.mulVec ξ = 0

def ZCusp (V : HSp D) (φ : GA D V → ℂ) : Prop :=
  ∀ ξ, IsoVec V ξ → ∀ (μ : Measure (ZI V ξ)) (𝓕 : Set (ZI V ξ)), μ.IsHaarMeasure →
    IsFundamentalDomain ((GQ V).subgroupOf (ZI V ξ)) 𝓕 μ → ∀ g, ∫ z in 𝓕, φ ((z : GA D V) * g) ∂μ = 0

structure HolForm (θ : InfFam D) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ)
    (J : Set (GA D V)) (χ : GA D V → ℂ) (φ : GA D V → ℂ) : Prop where
  aut : IsAutFun V φ
  bdd : ∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C
  lev : ∀ k ∈ J, ∀ g, φ (g * k) = χ k * φ g
  hol : HolAd θ M w φ

structure FinPair (V : HSp D) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) : Prop where
  haar : μ.IsHaarMeasure
  right : μ.IsMulRightInvariant
  fd : IsFundamentalDomain (GQ V) 𝓕 μ
  fin : μ 𝓕 ≠ ⊤

def nuQ (V : HSp D) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) : Measure (AutQ V) := (μ.restrict 𝓕).map (autMk V)

def Repr (V : HSp D) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (F : Lp ℂ 2 (nuQ V μ 𝓕)) (ψ : GA D V → ℂ) : Prop :=
  ∀ᵐ x ∂μ, F (autMk V x) = ψ x

structure IsReg (V : HSp D) (μ : Measure (GA D V)) (𝓕 : Set (GA D V))
    (ρ : GA D V →* (Lp ℂ 2 (nuQ V μ 𝓕) →L[ℂ] Lp ℂ 2 (nuQ V μ 𝓕))) : Prop where
  val : ∀ g F, ∀ᵐ x ∂μ, ρ g F (autMk V x) = F (autMk V (x * g))
  iso : ∀ g F, ‖ρ g F‖ = ‖F‖
  cont : ∀ F, Continuous fun g => ρ g F

def IsSmoothVector' (θ : InfFam D) (V : HSp D) {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] (ρ : GA D V →* (K →L[ℂ] K))
    (F : K) : Prop :=
  ∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Mt V.rank), (∀ i, Xs i ∈ lieAt V (τs i)) →
    ContDiff ℝ ∞ fun t : Fin k → ℝ => ρ (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod F

def dL2 (θ : InfFam D) (V : HSp D) {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] (ρ : GA D V →* (K →L[ℂ] K))
    (p : D.what₂.Tau × Mt V.rank) (F : K) : K :=
  deriv (fun t : ℝ => ρ (oneP θ V p.1 p.2 t) F) 0

structure GoodDict (θ : InfFam D) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ)
    {r : ℕ} (hr : V.rank = r) {Comp : Type} (X : Comp → ReciprocityTheory.ChartRestriction.G.FD.Data D.host.E r)
    (la : ∀ k, ReciprocityTheory.ChartRestriction.G.FD.Wt (X k).Ψ r) (dict : GA D V → Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame (X k).Ψ r) (mu : GA D V → ℂ)
    (c : Comp → ℂ) (Kf : Subgroup (GA D V)) : Prop where
  inf : IsInfFam θ
  base : BaseFr M θ hr dict
  unif : ∃ th, (∀ k τ, IsInfEmb τ.1 (th k τ)) ∧ DictIsUnif V dict Kf th hr
  model : ∀ k, ModelW V hr (X k)
  muUnit : MuUnit V dict mu
  muCont : Continuous mu
  chi : ∀ k, ∀ γ ∈ (X k).Γ, (X k).χ (la k) γ = 1
  cNe : ∀ k, c k ≠ 0
  cBdd : ∃ C : ℝ, ∀ k, ‖c k‖ ≤ C
  fin : Finite Comp
  levFin : Kf ≤ GfC V
  levOpen : ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧ ∀ k ∈ U, k ∈ GfC V → k ∈ Kf
  muK : ∀ k ∈ Kf, mu k = 1
  wt : ∃ e : D.what₂.Tau → ℤ, (∀ u ∈ GinfC V, mu u = ∏ ρ, (archM V (θ ρ) u).det ^ e ρ) ∧
    ∀ k ρ (τ : (X k).Ψ), τ.1 = tauE D ρ → ∀ a : Fin V.rank, w ρ a = la k τ (Fin.cast hr a) + e ρ

end Adelic

end GlobalTheory.HolDict
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.MapInclKMemTwCentResOne
section
noncomputable section
open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix
open scoped TensorProduct Classical
namespace GlobalTheory.LKRes.Model
variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem sigKQ_inclK (r : ℕ) (a : K) : sigKQ p K r (inclK p K r a) = inclK p K r a := by
  change Algebra.TensorProduct.map (AlgHom.id ℚ_[p] K) (frobQ p r) (a ⊗ₜ[ℚ_[p]] (1 : Qr p r)) = a ⊗ₜ[ℚ_[p]] (1 : Qr p r)
  rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]

theorem sigKQ_inclQ (r : ℕ) (b : Qr p r) : sigKQ p K r (inclQ p K r b) = inclQ p K r (frobQ p r b) := by
  change Algebra.TensorProduct.map (AlgHom.id ℚ_[p] K) (frobQ p r) ((1 : K) ⊗ₜ[ℚ_[p]] b) = (1 : K) ⊗ₜ[ℚ_[p]] frobQ p r b
  rw [Algebra.TensorProduct.map_tmul, map_one]

theorem frobQ_norm (r : ℕ) (b : Qr p r) : ‖((frobQ p r b : Qr p r) : PadicAlgCl p)‖ = ‖(b : PadicAlgCl p)‖ :=
  norm_map_GK p (Q0 p) (frobK p (Q0 p)) b

theorem frobQ_intR (r : ℕ) (b : Qr p r) (hb : b ∈ GlobalTheory.LKLoc.intR p (Q0 p) r) :
    frobQ p r b ∈ GlobalTheory.LKLoc.intR p (Q0 p) r := by
  simp only [GlobalTheory.LKLoc.intR, Subring.mem_comap] at *
  have := (mem_Obar_iff (p := p)).1 hb
  exact (mem_Obar_iff (p := p)).2 (by
    show ‖((frobQ p r b : Qr p r) : PadicAlgCl p)‖ ≤ 1
    rw [frobQ_norm]; exact this)

theorem sigKQ_intKQ (r : ℕ) (x : KQ p K r) (hx : x ∈ intKQ p K r) : sigKQ p K r x ∈ intKQ p K r := by
  have : intKQ p K r ≤ (intKQ p K r).comap (sigKQ p K r).toRingHom := by
    refine (Subring.closure_le).2 ?_
    rintro _ (⟨a, rfl⟩ | ⟨b, rfl⟩)
    · simp only [SetLike.mem_coe, Subring.mem_comap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      rw [sigKQ_inclK]; exact Subring.subset_closure (Or.inl ⟨a, rfl⟩)
    · simp only [SetLike.mem_coe, Subring.mem_comap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      rw [sigKQ_inclQ]; exact Subring.subset_closure (Or.inr ⟨⟨_, frobQ_intR p r b.1 b.2⟩, rfl⟩)
  exact this hx

theorem sigRes_Kres (n r : ℕ) (g : GL (Fin n) (KQ p K r)) (hg : g ∈ Kres p K n r) :
    sigRes p K n r g ∈ Kres p K n r := by
  obtain ⟨h, rfl⟩ := hg
  refine ⟨GeneralLinearGroup.map ((sigKQ p K r).toRingHom.restrict (intKQ p K r) (intKQ p K r)
    (fun x hx => sigKQ_intKQ p K r x hx)) h, ?_⟩
  ext i j
  simp [sigRes, GeneralLinearGroup.map]

theorem nrmRes_one (n : ℕ) (δ : GL (Fin n) (KQ p K 1)) : nrmRes p K n 1 δ = δ := by
  simp [nrmRes]

example (n r : ℕ) : Nontrivial (KQ p K r) := by
  unfold KQ; infer_instance

def mulMap (r : ℕ) : KQ p K r →ₐ[ℚ_[p]] PadicAlgCl p :=
  Algebra.TensorProduct.productMap K.val (Qr p r).val

theorem mulMap_intKQ (r : ℕ) (x : KQ p K r) (hx : x ∈ intKQ p K r) : ‖mulMap p K r x‖ ≤ 1 := by
  have : intKQ p K r ≤ (Obar p).toSubring.comap (mulMap p K r).toRingHom := by
    refine (Subring.closure_le).2 ?_
    rintro _ (⟨a, rfl⟩ | ⟨b, rfl⟩)
    · simp only [SetLike.mem_coe, Subring.mem_comap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      change (mulMap p K r (a.1 ⊗ₜ[ℚ_[p]] (1 : Qr p r))) ∈ Obar p
      show (a.1 : PadicAlgCl p) * 1 ∈ Obar p
      rw [mul_one]; exact a.2
    · simp only [SetLike.mem_coe, Subring.mem_comap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      change (mulMap p K r ((1 : K) ⊗ₜ[ℚ_[p]] b.1)) ∈ Obar p
      show 1 * (b.1 : PadicAlgCl p) ∈ Obar p
      rw [one_mul]; exact b.2
  exact (mem_Obar_iff (p := p)).1 (this hx)

theorem inv_p_not_mem_intKQ (r : ℕ) : inclK p K r (p : K)⁻¹ ∉ intKQ p K r := by
  intro h
  have h1 := mulMap_intKQ p K r _ h
  have h2 : mulMap p K r (inclK p K r (p : K)⁻¹) = (p : PadicAlgCl p)⁻¹ := by
    show (((p : K)⁻¹ : K) : PadicAlgCl p) * 1 = _
    simp
  rw [h2, norm_inv] at h1
  have hp : ‖(p : PadicAlgCl p)‖ < 1 := by
    have h := Padic.norm_p_lt_one (p := p)
    rw [← PadicAlgCl.norm_extends] at h
    simpa using h
  have hp0 : 0 < ‖(p : PadicAlgCl p)‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  have := (one_lt_inv₀ hp0).2 hp
  linarith

theorem Kres_ne_top (r : ℕ) : Kres p K 1 r ≠ ⊤ := by
  intro h
  have hp : (p : K)⁻¹ ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  let g0 : GL (Fin 1) K := GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal fun _ => (p : K)⁻¹) (by simp [hp])
  let g : GL (Fin 1) (KQ p K r) := GeneralLinearGroup.map (inclK p K r).toRingHom g0
  have hg : g ∈ Kres p K 1 r := by rw [h]; trivial
  obtain ⟨k, hk⟩ := hg
  have e := congrArg (fun x : GL (Fin 1) (KQ p K r) => (x : Matrix (Fin 1) (Fin 1) (KQ p K r)) 0 0) hk
  simp only [g, g0, GeneralLinearGroup.map] at e
  apply inv_p_not_mem_intKQ p K r
  have : ((k : Matrix (Fin 1) (Fin 1) (intKQ p K r)) 0 0 : KQ p K r) ∈ intKQ p K r := SetLike.coe_mem _
  convert this using 1
  simp at e ⊢
  exact e.symm

theorem frobQ_congr (r : ℕ) (b : Qr p r) (hb : ‖(b : PadicAlgCl p)‖ ≤ 1) :
    ‖((frobQ p r b : Qr p r) : PadicAlgCl p) - (b : PadicAlgCl p) ^ p‖ < 1 := by
  have h := (isFrob_frobK (p := p) (K := Q0 p) inferInstance).isFrobOn r b b.2 hb
  rw [show qK p (Q0 p) = p from residue_cardinality_base_field] at h
  exact h

theorem exists_frobQ_ne {r : ℕ} (hr : 2 ≤ r) : ∃ b : Qr p r, b ≠ 0 ∧ frobQ p r b ≠ b := by
  by_contra hc
  push Not at hc
  have hK : FiniteDimensional ℚ_[p] (Q0 p) := inferInstance
  have h := (IsFrobOn.pow_fixes_iff p (Q0 p) hK (by omega : 0 < r) ((isFrob_frobK hK).isFrobOn r) 1).1 (by
    intro x hx
    rw [pow_one]
    by_cases h0 : (⟨x, hx⟩ : Qr p r) = 0
    · have : x = 0 := congrArg Subtype.val h0
      rw [this, map_zero]
    · exact congrArg Subtype.val (hc ⟨x, hx⟩ h0))
  have := Nat.le_of_dvd one_pos h
  omega

theorem inclQ_injective (r : ℕ) : Function.Injective (inclQ p K r) :=
  haveI : Nontrivial (KQ p K r) := by unfold KQ; infer_instance
  (inclQ p K r).toRingHom.injective

theorem twCentRes_one_ne_top {r : ℕ} (hr : 2 ≤ r) : twCentRes p K 1 r 1 ≠ ⊤ := by
  intro h
  obtain ⟨b, hb0, hb⟩ := exists_frobQ_ne p hr
  let g0 : GL (Fin 1) (Qr p r) := GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal fun _ => b) (by simp [hb0])
  let g : GL (Fin 1) (KQ p K r) := GeneralLinearGroup.map (inclQ p K r).toRingHom g0
  have hg : g ∈ twCentRes p K 1 r 1 := by rw [h]; trivial
  have e : g * 1 = 1 * sigRes p K 1 r g := hg
  rw [mul_one, one_mul] at e
  have e' := congrArg (fun x : GL (Fin 1) (KQ p K r) => (x : Matrix (Fin 1) (Fin 1) (KQ p K r)) 0 0) e
  have e'' : inclQ p K r b = sigKQ p K r (inclQ p K r b) := by
    simpa [g, g0, sigRes, GeneralLinearGroup.map] using e'
  rw [sigKQ_apply_inclQ] at e''
  exact hb (inclQ_injective p K r e'').symm

theorem map_inclK_mem_twCentRes_one (n r : ℕ) (g : GL (Fin n) K) :
    GeneralLinearGroup.map (inclK p K r).toRingHom g ∈ twCentRes p K n r 1 := by
  show _ * 1 = 1 * sigRes p K n r _
  rw [mul_one, one_mul]
  ext i j
  simp [sigRes, GeneralLinearGroup.map, sigKQ_apply_inclK]

theorem finrank_KQ {r : ℕ} (hr : 0 < r) : Module.finrank ℚ_[p] (KQ p K r) = Module.finrank ℚ_[p] K * r := by
  have h : Module.finrank ℚ_[p] (Qr p r) = r := by
    have := finrank_Kn p (Q0 p) inferInstance hr
    simpa using this
  have e : Module.finrank ℚ_[p] (K ⊗[ℚ_[p]] Qr p r) = Module.finrank ℚ_[p] K * Module.finrank ℚ_[p] (Qr p r) :=
    Module.finrank_tensorProduct
  rw [h] at e
  exact e

theorem TOResU_gl_one_of_le (γ : GL (Fin 1) (KQ p K 1)) (U : Subgroup (GL (Fin 1) (KQ p K 1)))
    (hU : U ≤ Kres p K 1 1) (φ : GL (Fin 1) (KQ p K 1) → ℂ) :
    TOResU p K 1 1 γ U φ = φ γ / (U.relIndex (Kres p K 1 1) : ℂ) := by
  haveI := normal_of_gl_one (Kres p K 1 1)
  have hT : GlobalTheory.BCT.twCent (sigRes p K 1 1) γ = ⊤ := by
    rw [sigRes_degree_one]
    refine eq_top_iff.2 fun g _ => ?_
    show g * γ = γ * g
    ext i j
    fin_cases i; fin_cases j
    simp [Matrix.mul_apply, mul_comm]
  obtain ⟨x, hx⟩ := orbSum_of_twCent_eq_top (sigRes p K 1 1) (Kres p K 1 1) γ hT
  rw [TOResU, GlobalTheory.LKLoc.twOrbU, hx, locPart_of_normal, hT, top_inf_eq, GlobalTheory.LKLoc.volRat,
    Subgroup.relIndex_eq_one.2 hU]
  push_cast
  ring

theorem TOHT_torus_degree_one (m : ℕ) (Kw : Fin m → IntermediateField ℚ_[p] (PadicAlgCl p))
    (γ : GHT p m 1 1 Kw) (φ : GHT p m 1 1 Kw → ℂ) : TOHT p m 1 1 Kw γ φ = φ γ := by
  have hc : ∀ {R : Type} [CommRing R] (a b : GL (Fin 1) R), a * b = b * a := fun a b => by
    ext i j
    fin_cases i; fin_cases j
    simp [Matrix.mul_apply, mul_comm]
  have hT : GlobalTheory.BCT.twCent (sigHT p m 1 1 Kw) γ = ⊤ := by
    refine eq_top_iff.2 fun g _ => ?_
    have hs : sigHT p m 1 1 Kw g = g := by
      refine Prod.ext ?_ (funext fun i => ?_)
      · show GlobalTheory.LKLoc.sig p (Q0 p) 1 1 g.1 = g.1
        refine Units.ext (Matrix.ext fun i j => ?_)
        exact DFunLike.congr_fun (frobQ_degree_one p) ((g.1 : Matrix (Fin 1) (Fin 1) (Qr p 1)) i j)
      · show sigRes p (Kw i) 1 1 (g.2 i) = g.2 i
        rw [sigRes_degree_one]; rfl
    show g * γ = γ * sigHT p m 1 1 Kw g
    rw [hs]
    exact Prod.ext (hc _ _) (funext fun i => hc _ _)
  rw [TOHT_gl_one, TOHTU, GlobalTheory.LKLoc.twOrbU]
  haveI : (KHT p m 1 1 Kw).Normal := ⟨fun k hk x =>
    ⟨(normal_of_gl_one _).conj_mem k.1 hk.1 x.1,
      fun i hi => (normal_of_gl_one (Kres p (Kw i) 1 1)).conj_mem (k.2 i) (hk.2 i hi) (x.2 i)⟩⟩
  obtain ⟨x, hx⟩ := orbSum_of_twCent_eq_top (sigHT p m 1 1 Kw) (KHT p m 1 1 Kw) γ hT
  rw [hx, locPart_of_normal, twCentHT, GlobalTheory.LKLoc.volRat_self]
  simp

theorem sigHT_KHT (m n r : ℕ) (Kw : Fin m → IntermediateField ℚ_[p] (PadicAlgCl p)) (g : GHT p m n r Kw)
    (hg : g ∈ KHT p m n r Kw) : sigHT p m n r Kw g ∈ KHT p m n r Kw := by
  refine ⟨?_, fun i hi => sigRes_Kres p (Kw i) n r _ (hg.2 i hi)⟩
  obtain ⟨h, e⟩ := hg.1
  refine ⟨GeneralLinearGroup.map ((frobQ p r).toRingHom.restrict (GlobalTheory.LKLoc.intR p (Q0 p) r)
    (GlobalTheory.LKLoc.intR p (Q0 p) r) (fun x hx => frobQ_intR p r x hx)) h, ?_⟩
  show _ = GlobalTheory.LKLoc.sig p (Q0 p) 1 r g.1
  rw [← e]
  ext i j
  rfl

example (m n r : ℕ) (Kw : Fin m → IntermediateField ℚ_[p] (PadicAlgCl p)) : TopologicalSpace (GHT p m n r Kw) :=
  inferInstance

theorem isTopologicalRing_KQ (hK : FiniteDimensional ℚ_[p] K) {r : ℕ} (hr : 0 < r) :
    IsTopologicalRing (KQ p K r) := by
  haveI : FiniteDimensional ℚ_[p] (Qr p r) := finiteDimensional_Kn p (Q0 p) inferInstance hr
  haveI : FiniteDimensional ℚ_[p] (KQ p K r) := inferInstanceAs (Module.Finite ℚ_[p] (K ⊗[ℚ_[p]] Qr p r))
  haveI : IsModuleTopology ℚ_[p] (KQ p K r) := ⟨rfl⟩
  exact IsModuleTopology.isTopologicalRing ℚ_[p] (KQ p K r)

example : Q0 p = ReciprocityTheory.DiscreteGroups.LocalClassField.Q0 p := rfl

end GlobalTheory.LKRes.Model
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.TransSec
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBX

def transl {S : Scheme.{0}} {A : Over S} [GrpObj A] (x : 𝟙_ (Over S) ⟶ A) : A.left ⟶ A.left := ((toUnit A ≫ x) * 𝟙 A).left

section Generic

variable {K : Type} [Field K] {P P₂ : PolAV (Sp K)} {n : ℕ}

def TransSec (x : 𝟙_ (Over (Sp K)) ⟶ P.A) (s s' : (lbPow P.L n).Sec) : Prop :=
  ∃ io : LB.Iso ((lbPow P.L n).pull (transl x)) (lbPow P.L n), io.IsGen ∧ SecMaps io (secPull s (transl x)) s'

def TransMap (x : 𝟙_ (Over (Sp K)) ⟶ P.A) {r : ℕ} (b : Fin r → (lbPow P.L n).Sec) (u : (Fin r → K) ≃ₗ[K] (Fin r → K)) : Prop :=
  ∃ io : LB.Iso ((lbPow P.L n).pull (transl x)) (lbPow P.L n), io.IsGen ∧
    ∀ c, SecMaps io (secPull (secComb P.A.hom c b) (transl x)) (secComb P.A.hom (u c) b)

def GenPull (a : P.A ⟶ P₂.A) (θ : (lbPow P₂.L 1).Sec) (e : (lbPow P.L n).Sec) : Prop :=
  ∃ ga : LB.Iso ((lbPow P₂.L 1).pull a.left) (lbPow P.L n), ga.IsGen ∧ SecMaps ga (secPull θ a.left) e

def Eig (a : P.A ⟶ P₂.A) (e₀ : (lbPow P.L n).Sec) {d : ℕ} (e : Fin d → (lbPow P.L n).Sec) : Prop :=
  ∃ z : Fin d → Tor P n, (Function.Injective fun i => (z i).1 ≫ a) ∧ (∀ t : Tor P n, ∃ i, t.1 ≫ a = (z i).1 ≫ a) ∧
    ∀ i, TransSec (z i).1 e₀ (e i)

def Chars (a : P.A ⟶ P₂.A) {d : ℕ} (e : Fin d → (lbPow P.L n).Sec) (χ : Fin d → (𝟙_ (Over (Sp K)) ⟶ P.A) → Kˣ) : Prop :=
  (∀ i h h', h ≫ a = 1 → h' ≫ a = 1 → χ i (h * h') = χ i h * χ i h') ∧
  (∀ i i', (∀ h, h ≫ a = 1 → χ i h = χ i' h) → i = i') ∧
  ∀ h, h ≫ a = 1 → (∃ io : LB.Iso ((lbPow P.L n).pull (transl h)) (lbPow P.L n), io.IsGen) ∧
    ∀ io : LB.Iso ((lbPow P.L n).pull (transl h)) (lbPow P.L n), io.IsGen → ∃ l : Kˣ, ∀ i,
      SecMaps io (secPull (e i) (transl h)) (secSmul P.A.hom ((l * χ i h : Kˣ) : K) (e i))

abbrev boxLB (P : PolAV (Sp K)) (n : ℕ) {k : ℕ} (pr : Fin k → (P₂.A ⟶ P.A)) : LB P₂.A.left :=
  LB.LinComb (lbPow P.L n) (K := Fin k) (fun u => (pr u).left) fun _ => 1

def IsBox {k : ℕ} {pr : Fin k → (P₂.A ⟶ P.A)} (ga : LB.Iso (boxLB P n pr) (lbPow P₂.L n)) (s : Fin k → (lbPow P.L n).Sec)
    (s' : (lbPow P₂.L n).Sec) : Prop :=
  ∃ t : (boxLB P n pr).Sec, (∀ j : Fin k → (lbPow P.L n).ι, t.f j =
    ∏ u, ((pr u).left.appLE _ _ (LB.wchart_le (lbPow P.L n) (fun u => (pr u).left) j u)).hom ((s u).f (j u))) ∧
    SecMaps ga t s'

end Generic

section Model

variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {P P₂ : PolAV (Sp K)} {N N₂ n : ℕ}

def PullsTo {m : TGrp R K P N} {m₂ : TGrp R K P₂ N₂} (B : TBun m n) (B₂ : TBun m₂ 1) (a' : m.AA ⟶ m₂.AA)
    (θ : (lbPow P₂.L 1).Sec) (e : (lbPow P.L n).Sec) : Prop :=
  ∃ ga : LB.Iso (B₂.M.L.pull a'.left) B.M.L, ga.IsGen ∧ ∃ (c : K) (t₂ : B₂.M.L.Sec) (t : B.M.L.Sec), c ≠ 0 ∧
    SecMaps B₂.w (secPull t₂ m₂.φ) (secSmul P₂.A.hom c θ) ∧ SecMaps ga (secPull t₂ a'.left) t ∧
    SecMaps B.w (secPull t m.φ) (secSmul P.A.hom c e)

def IsSub (m' : TGrp R K P N₂) (m : TGrp R K P N) (i : m'.AA ⟶ m.AA) : Prop :=
  IsMonHom i ∧ IsOpenImmersion i.left ∧ m'.φ ≫ i.left = m.φ ∧ Set.range (m'.j ≫ i).left = Set.range m.j.left

def IsGlued {G : Over (Sp R)} (φ₀ : P.A.left ⟶ G.left) (X : Over (Sp R)) (φ : P.A.left ⟶ X.left) (io : Tor P N → (G ⟶ X)) : Prop :=
  IsSeparated X.hom ∧ IsPullback φ P.A.hom X.hom (spMap (algebraMap R K)) ∧ (∀ x, IsOpenImmersion (io x).left) ∧
  (∀ z : X.left, ∃ x, z ∈ Set.range (io x).left) ∧ ∀ x, φ₀ ≫ (io x).left = transl x.1 ≫ φ

end Model

def LocMem {K : Type} [Field K] [NumberField K] {r : ℕ} (E : Submodule (𝓞 K) (Fin r → K))
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (x : Fin r → K) : Prop :=
  ∃ s : 𝓞 K, s ∉ v.asIdeal ∧ s • x ∈ E

def LocPrim (κ : GlobalTheory.KeyCl.Rule) : Prop :=
  ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [CharZero K] [Algebra R K]
    [IsFractionRing R K], Finite (IsLocalRing.ResidueField R) → ∀ (x : KeyIn K),
    (letI := x.P.isAb.comm; GlobalTheory.ZH.HypS x.P.A x.P.L) →
    ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (φ : x.P.A.left ⟶ G.left) (M : RigLB G)
      (w : LB.Iso (M.L.pull φ) (lbPow x.P.L (1 ^ 2))) (y : Fin x.P.g → (epsR R ⟶ G)),
      IsSemiAbelian G → IsGrpPullback x.P.A G (spMap (algebraMap R K)) φ → Nonempty (CubicalStr G M) → w.IsGen →
      GlobalTheory.MBLow.RigPow (algebraMap R K) w x.rig → IsLieBasis y → (∀ i, IsVecOver (algebraMap R K) φ (y i) (x.v i)) →
      ∀ s : (lbPow x.P.L (1 ^ 2)).Sec, (∀ (i : x.P.L.ι) (h : (lbPow x.P.L (1 ^ 2)).U (fun _ => i) ≤ x.P.L.U i),
        s.f (fun _ => i) = resG _ h (x.th.f i)) → (∃ t : M.L.Sec, SecMaps w (secPull t φ) s) →
      ∃ r : R, algebraMap R K r * (κ K x : K) = 1

end GlobalTheory.MBX

end
end

