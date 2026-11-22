import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
section
set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjTwist

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

def IsRoot1 (z : ℂ) : Prop := ∃ n : ℕ, 0 < n ∧ z ^ n = 1

def UnitOff (N : ℕ) (u : ℂ) : Prop :=
  u ≠ 0 ∧ ∃ n : ℕ, IsIntegral ℤ ((N : ℂ) ^ n * u) ∧ IsIntegral ℤ ((N : ℂ) ^ n * u⁻¹)

section Any

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

def ConjTup (τ : ℂ ≃+* ℂ) (t t' : T0) : Prop :=
  R.Q t' = R.Q t ∧ ∀ x, ((R.xi t' x : Circle) : ℂ) = τ ((R.xi t x : Circle) : ℂ)

open Classical in

def omegaFlat {a b : ℕ} (Q : Finset (Pl D.host.E)) (r : ℕ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (y : ∀ PP : Pl D.host.E, Matrix (Fin a) (Fin b) (kP PP)) : ℂ :=
  if h : ∀ PP ∈ Q, IsUnit (topL r (y PP)).det then ∏ PP ∈ Q.attach, ((ξ PP.1 (h PP.1 PP.2).unit : ℂˣ) : ℂ) else 0

open Classical in

def IsFlatVec (i : Fin D.R.m) (t : T0) (f : WO (Vc D i) (Wc D i) → ℂ) : Prop :=
  ∃ (eg eQ : AE D) (fg : WO (Vc D i) (Wc D i) → ℂ), IsIdemSum eg R.Pg ∧ IsIdemSum eQ (R.Q t) ∧
    IsThetaAt R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) (cA D eg)
      (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) 1 (R.vacP i)
      (fun x => if IsHalf (cA D eg) x ∧ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) then
        omegaK R.Pg (fun PP => redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x)) else 0) fg ∧
    IsThetaAt R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) eQ
      (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) 1 fg
      (fun x => if IsHalf eQ x ∧ IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) then
        omegaFlat (R.Q t) (Wc D i).rank (R.xiR t) (fun PP => redM PP (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) x)) else 0) f

def IsCentAt (i : Fin D.R.m) (Q : Finset (Pl D.host.E)) (z : GA D (Vc D i)) : Prop :=
  z ∈ Subgroup.center (GA D (Vc D i)) ∧ z ∈ GfC (Vc D i) ∧ ∃ e : AE D, IsIdemSum e Q ∧ SuppAt e (Vc D i) z

def ser (i : Fin D.R.m) (t : T0) (f : WO (Vc D i) (Wc D i) → ℂ) (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (h : GA D (Vc D i))
    (w : (R.cV i).W) (g : GA D (Wc D i)) : ℂ :=
  thetaKO (R.ωP i t) h g (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i)
    (onb (R.MW i (sg0 D A))) f (R.ioP i (PiTensorProduct.tprod ℂ u) w))

theorem ser_vP (i : Fin D.R.m) (t : T0) (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (h : GA D (Vc D i)) (w : (R.cV i).W)
    (g : GA D (Wc D i)) :
    ser R i t (R.vP i t) u h w g = thetaKO (R.ωP i t) h g (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ u) w)) := rfl

def ConjVec (i : Fin D.R.m) (τ : ℂ ≃+* ℂ) (x x' : VsV D i ℂ) : Prop :=
  (x' : Pol ℂ D.what₂.Tau (Vc D i).rank) = MvPolynomial.map (τ : ℂ →+* ℂ) (x : Pol ℂ D.what₂.Tau (Vc D i).rank)

def ExtC (i : Fin D.R.m) {K' : Type} [Field K'] (σ' : K' →+* ℂ) (c0 : VsV D i K' →ₛₗ[σ'] (R.cV i).W)
    (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W) : Prop :=
  ∀ (v : VsV D i K') (v' : VsV D i ℂ),
    (v' : Pol ℂ D.what₂.Tau (Vc D i).rank) = MvPolynomial.map σ' (v : Pol K' D.what₂.Tau (Vc D i).rank) → c v' = c0 v

def ConjForm (i : Fin D.R.m) (τ : ℂ ≃+* ℂ) (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W) (t t' : T0) (y : (R.HV i t).H)
    (y' : (R.HV i t').H) : Prop :=
  ∀ h : GA D (Vc D i), ∃ x x' : VsV D i ℂ, ConjVec i τ x x' ∧ (R.HV i t).e y (fin _ h) = c x ∧ (R.HV i t').e y' (fin _ h) = c x'

end Any

section Core

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)

structure FixBase (i : Fin D.R.m) (τ : ℂ ≃+* ℂ) : Prop where
  core : ∀ a : T.Q.c.F, τ (a : ℂ) = (a : ℂ)
  host : ∀ (φ : D.host.E →+* ℂ) (x : D.host.E), τ (φ x) = φ x
  curve : GlobalTheory.CompRat.FixesCurve T.Q.H τ 1
  split : ∀ P : Pl D.host.E, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal →
    τ ((((R.C.mu0 i * R.C.eta⁻¹).val P : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm P.asIdeal : ℝ) : ℝ) : ℂ)) =
      (((R.C.mu0 i * R.C.eta⁻¹).val P : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm P.asIdeal : ℝ) : ℝ) : ℂ)
  chi : ∀ PP ∈ R.Pg, ∀ x, τ ((R.chi ((i : ℕ) + 1) PP x : ℂˣ) : ℂ) = ((R.chi ((i : ℕ) + 1) PP x : ℂˣ) : ℂ)

variable {T R} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}

def Expands (O : OMDat T.toCore R i Tp tup) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (Φ : GA D (Wc D i) → ℂ) {n : ℕ} (a : Fin n → ℂ)
    (f : Fin n → T.toCore.cuspA ((i : ℕ) + 1) (wtA κ) κ.n) : Prop :=
  ∀ g, Φ g = ∑ k, a k * ((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) *
    O.phi (T.cE ((i : ℕ) + 1) O.s0) (f k : T.toCore.R ((i : ℕ) + 1)) g)

def ConjFun (O : OMDat T.toCore R i Tp tup) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (τ : ℂ ≃+* ℂ) (ζ : ℂ) (Φ Φ' : GA D (Wc D i) → ℂ) : Prop :=
  (∃ (n : ℕ) (a : Fin n → ℂ) (f : Fin n → T.toCore.cuspA ((i : ℕ) + 1) (wtA κ) κ.n), Expands O κ Φ a f) ∧
    ∀ (n : ℕ) (a : Fin n → ℂ) (f : Fin n → T.toCore.cuspA ((i : ℕ) + 1) (wtA κ) κ.n),
      Expands O κ Φ a f → Expands O κ Φ' (fun k => ζ * τ (a k)) f

def SameCover (O : OMDat T.toCore R i Tp tup) (a b : Tp) (e : O.Cl' a ≃ O.Cl' b) : Prop :=
  (∃ cx : Rul (O.dδ a).Xo₂ (O.dδ a).c₂, O.dδ b = { O.dδ a with cδ := cx }) ∧ HEq (O.U₂ b) (O.U₂ a) ∧ HEq (O.dict₂ b) (O.dict₂ a) ∧
    O.bad b = O.bad a ∧ O.vol b = O.vol a ∧
    ∀ k, O.Lh b (e k) = O.Lh a k ∧ O.La b (e k) = O.La a k ∧ O.Nc b (e k) = O.Nc a k ∧ O.gam b (e k) = O.gam a k

end Core

end GlobalTheory.ConjTwist
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntegrandPeriodic
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RawLift.Model

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} {χV χW : (AE D)ˣ →* Circle}
  {om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)}

theorem cA_inc (e : D.host.E) : cA D (incA D e) = incA D (star e) := by
  rfl

theorem hO_eq_trace (x y : WO V W) :
    hO V W x y = Matrix.trace ((V.gram⁻¹).map (incA D) * ((y.map (cA D))ᵀ * W.gram.map (incA D) * x)) := by
  simp only [hO, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply,
    Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  ring

theorem hO_ratMul (C : Matrix (Fin W.rank) (Fin W.rank) D.host.E) (u v : WO V W) :
    hO V W (ratMul C u) (ratMul C v) =
      Matrix.trace ((V.gram⁻¹).map (incA D) * ((v.map (cA D))ᵀ * (Cᴴ * W.gram * C).map (incA D) * u)) := by
  have h : (C.map (incA D)).map (cA D) = (Cᴴ.map (incA D))ᵀ := by
    ext i j; simp [Matrix.map_apply, cA_inc]
  rw [hO_eq_trace]
  unfold ratMul
  rw [Matrix.map_mul, h, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.map_mul, Matrix.map_mul]
  simp only [Matrix.mul_assoc]

theorem gram_eq {Y : Lag W} {C} (h : IsLagFrame W Y C) : C.1ᴴ * W.gram * C.1 = C.2ᴴ * W.gram * C.2 := by
  rw [Matrix.mul_assoc, Matrix.mul_assoc]
  funext j k
  have m : ∀ j, ((fun a => C.1 a j), (fun a => C.2 a j)) ∈ Y.1 := fun j => h ▸ Submodule.subset_span ⟨j, rfl⟩
  have := Y.2.2 _ (m j) _ (m k)
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply] at this
  simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply] using this

theorem ratMul_add (C : Matrix (Fin W.rank) (Fin W.rank) D.host.E) (γ) (u : WO V W) :
    ratMul C (ratW W V γ + u) = ratW W V (C * γ) + ratMul C u := by
  unfold ratMul ratW
  rw [Matrix.mul_add, Matrix.map_mul]

theorem integrand_periodic (hψ : ∀ x, ‖ψ x‖ = 1) {Y : Lag W} {C} (h : IsLagFrame W Y C) {f₁ f₂ : WO V W → ℂ}
    (h₁ : IsThetaFunO ψ V W f₁) (h₂ : IsThetaFunO ψ V W f₂) (γ) (u : WO V W) :
    f₁ (ratMul C.1 (ratW W V γ + u)) * star (f₂ (ratMul C.2 (ratW W V γ + u))) =
      f₁ (ratMul C.1 u) * star (f₂ (ratMul C.2 u)) := by
  have e : ∀ B : Matrix (Fin W.rank) (Fin W.rank) D.host.E, ratW W V (B * γ) = ratMul B (ratW W V γ) := fun B => by
    unfold ratMul ratW; rw [Matrix.map_mul]
  have s : symplOH V W (ratW W V (C.1 * γ)) (ratMul C.1 u) = symplOH V W (ratW W V (C.2 * γ)) (ratMul C.2 u) := by
    rw [e, e]; unfold symplOH symplO; rw [hO_ratMul, hO_ratMul, gram_eq h]
  rw [ratMul_add, ratMul_add, h₁.quasi, h₂.quasi, s, star_mul']
  set z := ψ (-(symplOH V W (ratW W V (C.2 * γ)) (ratMul C.2 u))) with hz
  have : z * star z = 1 := by
    have := Complex.mul_conj' z
    rw [hz, hψ] at this
    simpa using this
  calc _ = (z * star z) * (f₁ (ratMul C.1 u) * star (f₂ (ratMul C.2 u))) := by ring
    _ = _ := by rw [this, one_mul]

theorem swPair_rank_zero {νV 𝓗 νW 𝓖 μ 𝓕 fr} (hs : SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr) (h : W.rank = 0)
    (f₁ f₂ : WO V W → ℂ) :
    HasSum (fun Y : Lag W => ((νV 𝓗).toReal : ℂ) * lagTerm μ 𝓕 (fr Y) f₁ f₂)
      (∫ h in 𝓗, thetaKO om h 1 f₁ * star (thetaKO om h 1 f₂) ∂νV) := by
  haveI : IsEmpty (Fin W.rank) := by rw [h]; infer_instance
  haveI : Subsingleton (WO V W) := ⟨fun a b => by funext i; exact isEmptyElim i⟩
  haveI : Subsingleton (Lag W) := ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
  haveI : Unique (Lag W) := uniqueOfSubsingleton default
  have hμ : μ 𝓕 = 1 := hs.covol.2.2
  have hc : ∀ g : WO V W → ℂ, g = fun _ => g 0 := fun g => funext fun w => by rw [Subsingleton.elim w 0]
  have z : ∀ x y : WO V W, symplOH V W x y = 0 := fun x y => by simp [symplOH, symplO, hO]
  have one : IsThetaFunO ψ V W (fun _ => 1) :=
    ⟨fun γ w => by simp [z], ⟨⊤, isOpen_univ, fun u _ _ => by funext w; simp [heisO, z]⟩, continuous_const,
      fun _ _ _ _ _ => contDiff_const⟩
  have key : ∀ p, ∀ f : WO V W → ℂ, om p f 0 = f 0 * om p (fun _ => 1) 0 := fun p f => by
    have : f = f 0 • (fun _ => (1 : ℂ)) := by funext w; simp [Subsingleton.elim w 0]
    conv_lhs => rw [this, map_smul]
    simp
  have nm : ∀ p, om p (fun _ => 1) 0 * star (om p (fun _ => 1) 0) = 1 := fun p => by
    have u := hs.weil.om_unit μ 𝓕 hs.covol.1 hs.covol.2.1 p _ one
    rw [hc (om p fun _ => 1)] at u
    simp only [setLIntegral_const, hμ, mul_one, enorm_one, one_pow] at u
    have u2 : ‖om p (fun _ => 1) 0‖ ^ 2 = 1 := by
      have := congrArg ENNReal.toReal u
      rwa [ENNReal.toReal_pow, toReal_enorm, ENNReal.toReal_one] at this
    have := Complex.mul_conj' (om p (fun _ => 1) 0)
    rw [← Complex.ofReal_pow, u2] at this
    simpa using this
  have I : ∀ g, thetaKO om g 1 f₁ * star (thetaKO om g 1 f₂) = f₁ 0 * star (f₂ 0) := fun g => by
    unfold thetaKO
    rw [key _ f₁, key _ f₂, star_mul']
    calc _ = (om (g, 1) (fun _ => 1) 0 * star (om (g, 1) (fun _ => 1) 0)) * (f₁ 0 * star (f₂ 0)) := by ring
      _ = _ := by rw [nm, one_mul]
  have L : ∀ C, lagTerm μ 𝓕 C f₁ f₂ = f₁ 0 * star (f₂ 0) := fun C => by
    have : μ.real 𝓕 = 1 := by rw [Measure.real, hμ, ENNReal.toReal_one]
    unfold lagTerm
    simp only [Subsingleton.elim (ratMul _ _ : WO V W) 0]
    rw [setIntegral_const, this, one_smul]
  simp only [I, L, setIntegral_const]
  convert hasSum_unique (fun _ : Lag W => ((νV 𝓗).toReal : ℂ) * (f₁ 0 * star (f₂ 0))) using 1
  simp [Measure.real]

end GlobalTheory.RawLift.Model

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsHermPairSelf
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL

namespace GlobalTheory.ColumnForm

section Sets

variable (k : Type) [Field k]

def colSet (N m : ℕ) : Set (GL (Fin N) k) :=
  {u | ∀ i j : Fin N, (j ≤ i ∨ (j : ℕ) < m) → u.val i j = (1 : Matrix (Fin N) (Fin N) k) i j}

def cornerSet (N m : ℕ) : Set (GL (Fin N) k) :=
  {g | ∀ i j : Fin N, (m ≤ (i : ℕ) + 1 ∨ m ≤ (j : ℕ)) → g.val i j = (1 : Matrix (Fin N) (Fin N) k) i j}

variable {k}

def colSum {N : ℕ} (l : ℕ) (u : GL (Fin N) k) : k :=
  ∑ p : Fin N × Fin N with (p.2 : ℕ) = p.1 + 1 ∧ l ≤ (p.2 : ℕ), u.val p.1 p.2

def headScalar (a b : ℕ) (t : kˣ) : GL (Fin (a + b)) k :=
  emb₂ k (stdSum (rfl : a + b = a + b)) (Matrix.GeneralLinearGroup.scalar (Fin a) t, 1)

theorem one_mem (N m : ℕ) : (1 : GL (Fin N) k) ∈ colSet k N m ∧ (1 : GL (Fin N) k) ∈ cornerSet k N m :=
  ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩

end Sets

variable {k : Type} [Field k] {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] {N : ℕ}

def colKer (π : Representation ℂ (GL (Fin N) k) V) (ψ : AddChar k Circle) (m l : ℕ) : Submodule ℂ V :=
  Submodule.span ℂ {w | ∃ u ∈ colSet k N m, ∃ v, w = π u v - (ψ (colSum l u) : ℂ) • v}

def IsPosForm (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) : Prop :=
  (∀ v w, B w v = starRingEnd ℂ (B v w)) ∧ ∀ v, 0 ≤ (B v v).re

def IsHermPair {G : Type} [Group G] (π : Representation ℂ G V) (σ : Representation ℂ G W) : Prop :=
  ∃ C : V →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ, (∀ g v w, C (π g v) (σ g w) = C v w) ∧ (∀ v, (∀ w, C v w = 0) → v = 0) ∧
    ∀ w, (∀ v, C v w = 0) → w = 0

theorem isHermPair_self {G : Type} [Group G] {π : Representation ℂ G V} (h : IsUnitarisable π) : IsHermPair π π := by
  obtain ⟨B, -, h2, h3⟩ := h
  refine ⟨B, h3, fun v hv => ?_, fun v hv => ?_⟩ <;>
  · by_contra h0
    have := h2 v h0
    rw [hv v] at this
    simp at this

def IsAvg {X : Type} [AddCommGroup X] (u : Representation ℂ (Multiplicative X) V) (L : AddSubgroup X) (χ : L → ℂ)
    (E : Module.End ℂ V) : Prop :=
  (∀ (x : L) v, u (Multiplicative.ofAdd (x : X)) (E v) = χ x • E v) ∧
    (∀ (x : L) v, E (u (Multiplicative.ofAdd (x : X)) v) = χ x • E v) ∧
    ∀ v, v - E v ∈ Submodule.span ℂ {w | ∃ (x : L) (y : V), w = u (Multiplicative.ofAdd (x : X)) y - χ x • y}

theorem isAvg_bot {X : Type} [AddCommGroup X] (u : Representation ℂ (Multiplicative X) V) :
    IsAvg u ⊥ (fun _ => 1) 1 := by
  have h : ∀ (x : (⊥ : AddSubgroup X)) v, u (Multiplicative.ofAdd (x : X)) v = v := fun x v => by
    rw [AddSubgroup.mem_bot.1 x.2]; simp
  exact ⟨fun x v => by simp [h], fun x v => by simp [h], fun v => by simp⟩

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def HasColumnForm (π : Representation ℂ (GL (Fin N) k) V) (ψ : AddChar k Circle) (m : ℕ) : Prop :=
  ∃ B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ, IsPosForm B ∧ (∀ v, B v v = 0 ↔ v ∈ colKer π ψ m m) ∧
    ∀ g ∈ cornerSet k N m, ∀ v w, B (π g v) (π g w) =
      ((GlobalTheory.SplitWeil.nabs k (Matrix.GeneralLinearGroup.det g) ^ (N - m) : ℝ) : ℂ) * B v w

end GlobalTheory.ColumnForm

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsLevelProjLevelProj
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL
open scoped Topology

namespace GlobalTheory.LBC

section Groups

variable {k k' : Type} [Field k] [Field k'] [Algebra k k']

def galAct (s : k' ≃ₐ[k] k') (n : ℕ) : GL (Fin n) k' →* GL (Fin n) k' :=
  GeneralLinearGroup.map s.toAlgHom.toRingHom

@[simp] theorem galAct_apply (s : k' ≃ₐ[k] k') {n : ℕ} (g : GL (Fin n) k') (i j : Fin n) :
    (galAct s n g : Matrix (Fin n) (Fin n) k') i j = s ((g : Matrix (Fin n) (Fin n) k') i j) := rfl

@[simp] theorem galAct_one (n : ℕ) : galAct (1 : k' ≃ₐ[k] k') n = MonoidHom.id _ := by
  ext g i j; rfl

theorem galAct_mul (s t : k' ≃ₐ[k] k') (n : ℕ) : galAct (s * t) n = (galAct s n).comp (galAct t n) := by
  ext g i j; rfl

def incl (k' : Type) [Field k'] [Algebra k k'] (n : ℕ) : GL (Fin n) k →* GL (Fin n) k' :=
  GeneralLinearGroup.map (algebraMap k k')

@[simp] theorem incl_apply {n : ℕ} (γ : GL (Fin n) k) (i j : Fin n) :
    (incl k' n γ : Matrix (Fin n) (Fin n) k') i j = algebraMap k k' ((γ : Matrix (Fin n) (Fin n) k) i j) := rfl

@[simp] theorem galAct_incl (s : k' ≃ₐ[k] k') {n : ℕ} (γ : GL (Fin n) k) : galAct s n (incl k' n γ) = incl k' n γ := by
  ext i j; simp

variable (k) in

def norm (s : k' ≃ₐ[k] k') {n : ℕ} (g : GL (Fin n) k') : GL (Fin n) k' :=
  (List.ofFn fun j : Fin (Module.finrank k k') => galAct (s ^ (j : ℕ)) n g).prod

def IsStable (s : k' ≃ₐ[k] k') {n : ℕ} (K : Subgroup (GL (Fin n) k')) : Prop := K.map (galAct s n) = K

end Groups

section Traces

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

def IsLevelProj (π : Representation ℂ G V) (K : Subgroup G) (A : V →ₗ[ℂ] V)
    (T : fixed π K →ₗ[ℂ] fixed π K) : Prop :=
  ∀ v : fixed π K, ((T v : V) - A v) ∈ twKer π K 1

def HasLevelTrace (π : Representation ℂ G V) (K : Subgroup G) (A : V →ₗ[ℂ] V) (c : ℂ) : Prop :=
  FiniteDimensional ℂ (fixed π K) ∧ ∃ T, IsLevelProj π K A T ∧ LinearMap.trace ℂ _ T = c

theorem isLevelProj_id (π : Representation ℂ G V) (K : Subgroup G) :
    IsLevelProj π K LinearMap.id LinearMap.id := fun v => by simp

theorem hasLevelTrace_id (π : Representation ℂ G V) (K : Subgroup G) [FiniteDimensional ℂ (fixed π K)] :
    HasLevelTrace π K LinearMap.id (Module.finrank ℂ (fixed π K)) :=
  ⟨inferInstance, _, isLevelProj_id π K, LinearMap.trace_id ℂ _⟩

end Traces

section Unique

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {π : Representation ℂ G V} {K : Subgroup G}
  {A : V →ₗ[ℂ] V}

theorem IsLevelProj.unique (hd : Disjoint (fixed π K) (twKer π K 1)) {T T' : fixed π K →ₗ[ℂ] fixed π K}
    (hT : IsLevelProj π K A T) (hT' : IsLevelProj π K A T') : T = T' := by
  ext v
  have h1 : ((T v : V) - T' v) ∈ fixed π K := sub_mem (T v).2 (T' v).2
  have h2 : ((T v : V) - T' v) ∈ twKer π K 1 := by
    have := sub_mem (hT v) (hT' v)
    rwa [sub_sub_sub_cancel_right] at this
  exact sub_eq_zero.1 (Submodule.disjoint_def.1 hd _ h1 h2)

theorem HasLevelTrace.unique (hd : Disjoint (fixed π K) (twKer π K 1)) {c c' : ℂ} (h : HasLevelTrace π K A c)
    (h' : HasLevelTrace π K A c') : c = c' := by
  obtain ⟨_, T, hT, rfl⟩ := h
  obtain ⟨_, T', hT', rfl⟩ := h'
  rw [hT.unique hd hT']

def levelProj (hc : IsCompl (fixed π K) (twKer π K 1)) (A : V →ₗ[ℂ] V) : fixed π K →ₗ[ℂ] fixed π K :=
  Submodule.projectionOnto _ _ hc ∘ₗ A ∘ₗ (fixed π K).subtype

end Unique

section Lift

variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [Algebra k k']
  {n : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

variable (k) in

def IsTwInt (s : k' ≃ₐ[k] k') (P : Representation ℂ (GL (Fin n) k') W) (I : W →ₗ[ℂ] W) : Prop :=
  (∀ g, P (galAct s n g) ∘ₗ I = I ∘ₗ P g) ∧ 0 < Module.finrank k k' ∧ I ^ Module.finrank k k' = 1

theorem IsTwInt.isUnit {s : k' ≃ₐ[k] k'} {P : Representation ℂ (GL (Fin n) k') W} {I : W →ₗ[ℂ] W}
    (hI : IsTwInt k s P I) : IsUnit I :=
  IsUnit.of_pow_eq_one hI.2.2 hI.2.1.ne'

theorem IsTwInt.conj {s : k' ≃ₐ[k] k'} {P : Representation ℂ (GL (Fin n) k') W} {I : W →ₗ[ℂ] W}
    (hI : IsTwInt k s P I) (g : GL (Fin n) k') : P (galAct s n g) = I * P g * ((hI.isUnit.unit⁻¹ : (W →ₗ[ℂ] W)ˣ) : W →ₗ[ℂ] W) := by
  rw [Units.eq_mul_inv_iff_mul_eq, IsUnit.unit_spec]
  exact hI.1 g

theorem IsTwInt.mem_fixed {s : k' ≃ₐ[k] k'} {P : Representation ℂ (GL (Fin n) k') W} {I : W →ₗ[ℂ] W}
    (hI : IsTwInt k s P I) {K : Subgroup (GL (Fin n) k')} (hK : IsStable s K) {v : W} (hv : v ∈ fixed P K) :
    I v ∈ fixed P K := by
  intro x
  have hx : (x : GL (Fin n) k') ∈ K.map (galAct s n) := by rw [hK]; exact x.2
  obtain ⟨y, hy, e⟩ := Subgroup.mem_map.1 hx
  have h1 := LinearMap.congr_fun (hI.1 y) v
  simp only [LinearMap.comp_apply] at h1
  have h2 : P y v = v := by simpa using hv ⟨y, hy⟩
  simp only [MonoidHom.one_apply, Units.val_one, one_smul]
  rw [← e, h1, h2]

variable (k) in

def TwCharVal (s : k' ≃ₐ[k] k') (P : Representation ℂ (GL (Fin n) k') W) (I : W →ₗ[ℂ] W) (g' : GL (Fin n) k')
    (c : ℂ) : Prop :=
  ∃ U ∈ 𝓝 (1 : GL (Fin n) k'), ∀ K : Subgroup (GL (Fin n) k'), IsOpen (K : Set (GL (Fin n) k')) →
    IsCompact (K : Set (GL (Fin n) k')) → IsStable s K → (K : Set (GL (Fin n) k')) ⊆ U →
      HasLevelTrace P K (P g' ∘ₗ I) c

def CharVal (π : Representation ℂ (GL (Fin n) k) V) (γ : GL (Fin n) k) (c : ℂ) : Prop :=
  ∃ U ∈ 𝓝 (1 : GL (Fin n) k), ∀ K : Subgroup (GL (Fin n) k), IsOpen (K : Set (GL (Fin n) k)) →
    IsCompact (K : Set (GL (Fin n) k)) → (K : Set (GL (Fin n) k)) ⊆ U → HasLevelTrace π K (π γ) c

def IsLBC (s : k' ≃ₐ[k] k') (π : Representation ℂ (GL (Fin n) k) V) (P : Representation ℂ (GL (Fin n) k') W) :
    Prop :=
  IsSmooth π ∧ π.IsIrreducible ∧ IsSmooth P ∧ P.IsIrreducible ∧
  ∃ I : W →ₗ[ℂ] W, IsTwInt k s P I ∧
    ∀ g' : GL (Fin n) k', (norm k s g' : Matrix (Fin n) (Fin n) k').charpoly.Separable →
      ∀ γ : GL (Fin n) k, (γ : Matrix (Fin n) (Fin n) k).charpoly.map (algebraMap k k') =
          (norm k s g' : Matrix (Fin n) (Fin n) k').charpoly →
        ∃ c : ℂ, TwCharVal k s P I g' c ∧ CharVal π γ c

def IsLBCCl (s : k' ≃ₐ[k] k') (x : IrrGL k) (y : IrrGL k') : Prop :=
  ∃ (m : ℕ) (π : IrrRep (GL (Fin m) k)) (P : IrrRep (GL (Fin m) k')), x = ⟨m, π.cl⟩ ∧ y = ⟨m, P.cl⟩ ∧
    IsLBC s π.ρ P.ρ

theorem isTwInt_of_triv (s : k' ≃ₐ[k] k') (hd : 0 < Module.finrank k k') {P : Representation ℂ (GL (Fin n) k') ℂ}
    (hP : ∀ g, P g = LinearMap.id) : IsTwInt k s P LinearMap.id :=
  ⟨fun g => by rw [hP, hP], hd, one_pow _⟩

theorem hasLevelTrace_of_triv {G : Type} [Group G] {P : Representation ℂ G ℂ} (hP : ∀ g, P g = LinearMap.id)
    (K : Subgroup G) : HasLevelTrace P K LinearMap.id 1 := by
  have htop : fixed P K = ⊤ := by
    ext v; simp [fixed, eig, hP]
  have h1 : Module.finrank ℂ (fixed P K) = 1 := by
    rw [htop, finrank_top, Module.finrank_self]
  have := hasLevelTrace_id P K
  rwa [h1, Nat.cast_one] at this

theorem charVal_of_triv {P : Representation ℂ (GL (Fin n) k) ℂ} (hP : ∀ g, P g = LinearMap.id) (γ : GL (Fin n) k) :
    CharVal P γ 1 :=
  ⟨Set.univ, Filter.univ_mem, fun K _ _ _ => by rw [hP]; exact hasLevelTrace_of_triv hP K⟩

theorem twCharVal_of_triv (s : k' ≃ₐ[k] k') {P : Representation ℂ (GL (Fin n) k') ℂ} (hP : ∀ g, P g = LinearMap.id)
    (g' : GL (Fin n) k') : TwCharVal k s P LinearMap.id g' 1 :=
  ⟨Set.univ, Filter.univ_mem, fun K _ _ _ _ => by rw [hP]; exact hasLevelTrace_of_triv hP K⟩

theorem ofChar_one_apply {G : Type} [Group G] (g : G) : SmGL.ofChar (1 : G →* ℂˣ) g = LinearMap.id := by
  ext; simp [SmGL.ofChar]

theorem isLBC_one (s : k' ≃ₐ[k] k') (hd : 0 < Module.finrank k k') :
    IsLBC s (SmGL.ofChar (1 : GL (Fin n) k →* ℂˣ)) (SmGL.ofChar (1 : GL (Fin n) k' →* ℂˣ)) :=
  ⟨(isSmooth_ofChar_iff _).2 isSmoothChar_one, isIrreducible_ofChar _,
    (isSmooth_ofChar_iff _).2 isSmoothChar_one, isIrreducible_ofChar _, LinearMap.id,
    isTwInt_of_triv s hd ofChar_one_apply, fun g' _ γ _ =>
      ⟨1, twCharVal_of_triv s ofChar_one_apply g', charVal_of_triv ofChar_one_apply γ⟩⟩

end Lift

example {k k' : Type} [Field k] [Field k'] [Algebra k k'] {n : ℕ} (g : GL (Fin n) k') :
    norm k (1 : k' ≃ₐ[k] k') g = g ^ Module.finrank k k' := by
  simp [norm, one_pow, galAct_one, List.prod_ofFn, Finset.prod_const]

end GlobalTheory.LBC
end
end

