import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011

-- bundled from Development.AbelianVarietyTheory.BlockTheory.HeightDefect.CMCurveCharacterAction
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.LegendreCharacterCMCurves

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

def legChar (d : ℕ) [Fact d.Prime] : DirichletCharacter ℂ d :=
  (quadraticChar (ZMod d)).ringHomComp (Int.castRingHom ℂ)

def logPeriod (d : ℕ) [Fact d.Prime] : ℝ :=
  Real.eulerMascheroniConstant + Real.log (2 * Real.pi / Real.sqrt d) -
    (deriv (legChar d).LFunction 1 / (legChar d).LFunction 1).re

def IsConj {K : Type} [Field K] (a b : 𝓞 K) : Prop :=
  ∀ τ : K →+* ℂ, τ (b : K) = starRingEnd ℂ (τ (a : K))

section

variable {R : Type} [CommRing R]

def RosatiConj {K : Type} [Field K] (P : Out.PolAV (Sp R)) (act : OAct (𝓞 K) P.A) : Prop :=
  ∀ a b : 𝓞 K, IsConj a b →
    LBIso (cubeLB P.A ![fst P.A P.A ≫ act.act a, snd P.A P.A] P.L)
      (cubeLB P.A ![fst P.A P.A, snd P.A P.A ≫ act.act b] P.L)

def ActsThrough {O : Type} [CommRing O] (P : Out.PolAV (Sp R)) (act : OAct O P.A) (ρ : O →+* R)
    (v : epsR R ⟶ P.A) : Prop :=
  ∀ a, (v ≫ act.act a).left = spMap (epsScaleR (ρ a)) ≫ v.left

def IsLenSq (P : Out.PolAV (Sp R)) (v : epsR R ⟶ P.A) (s : R →+* ℂ) (x : ℝ) : Prop :=
  ∃ (A : Over (Sp ℂ)) (_ : GrpObj A) (φ : A.left ⟶ P.A.left) (u : HolUnif A (P.L.pull φ) 1)
    (Hm : Matrix (Fin 1) (Fin 1) ℂ) (χ : u.Λ → ℂ) (vs : epsR ℂ ⟶ A) (w : Fin 1 → ℂ),
    IsGrpPullback A P.A (spMap s) φ ∧ u.IsAH Hm χ ∧
    vs.left ≫ φ = spMap (Chart.dualMapR s) ≫ v.left ∧ u.IsDiff w vs ∧
    x = Real.pi * (hermForm Hm w w).re

def IsPrincipalAt {K : Type} [Field K] (d : ℕ) (τ : K →+* ℂ) (P : Out.PolAV (Sp R)) (act : OAct (𝓞 K) P.A)
    (s : R →+* ℂ) : Prop :=
  ∃ (A : Over (Sp ℂ)) (_ : GrpObj A) (φ : A.left ⟶ P.A.left) (u : HolUnif A (P.L.pull φ) 1) (χ : u.Λ → ℂ),
    IsGrpPullback A P.A (spMap s) φ ∧
    (∀ z : Fin 1 → ℂ, z ∈ u.Λ ↔ ∃ a : 𝓞 K, z 0 = τ (a : K)) ∧
    (∀ (a : 𝓞 K) (z : Fin 1 → ℂ), (u.ex (τ (a : K) • z)).left ≫ φ = (u.ex z).left ≫ φ ≫ (act.act a).left) ∧
    u.IsAH (Matrix.of fun _ _ => ((2 / Real.sqrt d : ℝ) : ℂ)) χ

end

def IsCMCurve {K : Type} [Field K] (d : ℕ) (τ : K →+* ℂ) (logOm : ℝ) (M : Type) [Field M] [NumberField M]
    (P : Out.PolAV (Sp (𝓞 M))) (act : OAct (𝓞 K) P.A) (ρ : 𝓞 K →+* 𝓞 M) (v : epsR (𝓞 M) ⟶ P.A) : Prop :=
  P.g = 1 ∧ RosatiConj P act ∧
  IsLieBasis (fun _ : Fin 1 => v) ∧ ActsThrough P act ρ v ∧
  (∃ σ₀ : M →+* ℂ, (∀ a : 𝓞 K, σ₀ ((ρ a : 𝓞 M) : M) = τ (a : K)) ∧
    IsPrincipalAt d τ P act (σ₀.comp (algebraMap (𝓞 M) M))) ∧
  ∃ len_sq : (M →+* ℂ) → ℝ, (∀ σ, 0 < len_sq σ) ∧
    (∀ σ x, IsLenSq P v (σ.comp (algebraMap (𝓞 M) M)) x ↔ x = len_sq σ) ∧
    (∑ σ, Real.log (len_sq σ)) / (Module.finrank ℚ M : ℝ) = -logOm

def CMCurveExists : Prop :=
  ∀ (d : ℕ) [Fact d.Prime], d % 16 = 7 →
    ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 →
    ∀ (rt : K), rt ^ 2 = -(d : K) →
    ∀ τ : K →+* ℂ, τ rt = Complex.I * (Real.sqrt d : ℝ) →
    ∃ (M : Type) (_ : Field M) (_ : NumberField M) (P : Out.PolAV (Sp (𝓞 M))) (act : OAct (𝓞 K) P.A)
      (ρ : 𝓞 K →+* 𝓞 M) (v : epsR (𝓞 M) ⟶ P.A), IsCMCurve d τ (logPeriod d) M P act ρ v

example (M : Type) [Field M] [NumberField M] : Fintype.card (M →+* ℂ) = Module.finrank ℚ M :=
  Embeddings.card M ℂ

end GlobalTheory.IndefiniteRowSideFullHecke.LegendreCharacterCMCurves
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.HeightDefect.CurveFormSign
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CurveFormSign

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def wVal (H : Host E) : ℂ := (1 + H.rt0) / 2

def rtSign (H : Host E) : ℤ := if 0 < H.rt0.im then 1 else -1

def wTyp (H : Host E) (ε : Bool) : 𝓞 E := if ε then H.w0 else H.bar H.w0

def pureVec {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty P)
    (ε : Bool) : Submodule (𝓞 E) D.La where
  carrier := {v | ∀ i, ¬ (ty i (H.rt : E) = H.rt0 ↔ ε = true) → P v i = 0}
  zero_mem' i _ := by simp
  add_mem' {a b} ha hb i hi := by simp [ha i hi, hb i hi]
  smul_mem' a v hv i hi := by rw [hP.1, hv i hi, mul_zero]

def PureSpan {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty P) : Prop :=
  ∀ v : D.La, ∃ n : ℕ, 0 < n ∧ n • v ∈ pureVec hP true ⊔ pureVec hP false

def curveForm (H : Host E) (a b : ℂ) : ℝ := (a * starRingEnd ℂ b).im / (Real.sqrt H.d / 2)

def InCurveLat (H : Host E) (z : ℂ) : Prop := ∃ m n : ℤ, z = m + n * wVal H

def IsCurveUnif (H : Host E) {k : Type} [Field k] [Algebra k ℂ] (C : Out.PolAV (Sp k)) (wC : C.A ⟶ C.A)
    (e : ℂ → (Over.mk (spMap (algebraMap k ℂ)) ⟶ C.A)) : Prop :=
  (∀ z z', e (z + z') = e z * e z') ∧ Function.Surjective e ∧ (∀ z, e z = 1 ↔ InCurveLat H z) ∧
    (∀ z, e (wVal H * z) = e z ≫ wC) ∧ IsHolTo Set.univ (fun z => (e z).left) ∧
    ∀ (n : ℕ) (a b : ℂ) (c : ℂˣ), 0 < n → InCurveLat H a → InCurveLat H b →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (curveForm H a b : ℂ) / n) →
      Out.WeilIs C.A C.L n (e ((n : ℂ)⁻¹ * a)) (e ((n : ℂ)⁻¹ * b)) (unitOn c)

def polCoeffOne (D : Datum H) (v : D.La) (ε' : Bool) (v' : D.La) : ℤ := -(rtSign H * D.EF v (wTyp H ε' • v'))

def polCoeffW (D : Datum H) (v v' : D.La) : ℤ := rtSign H * D.EF v v'

section Maps

variable {S X Y : Scheme.{0}} (C : Over S) (G : Over X) (f : Y ⟶ S) (x : Y ⟶ X)

abbrev MapOver : Type := Over.mk (pullback.snd C.hom f ≫ x) ⟶ G

variable {C G f x}

def MapOver.ev (φ : MapOver C G f x) {T : Scheme.{0}} (t : T ⟶ Y) (p : Over.mk (t ≫ f) ⟶ C) :
    Over.mk (t ≫ x) ⟶ G :=
  Over.homMk (pullback.lift p.left t (Over.w p) ≫ φ.left) (by
    have := Over.w φ
    simp only [Over.mk_left, Over.mk_hom, Functor.id_obj, Functor.const_obj_obj] at this ⊢
    rw [Category.assoc, this, pullback.lift_snd_assoc])

end Maps

section Clauses

variable {S X Y : Scheme.{0}} {C : Over S} [GrpObj C] {G : Over X} [GrpObj G] {f : Y ⟶ S} {x : Y ⟶ X}

def MapOver.IsHom (φ : MapOver C G f x) : Prop :=
  ∀ (T : Scheme.{0}) (t : T ⟶ Y) (p q : Over.mk (t ≫ f) ⟶ C), φ.ev t (p * q) = φ.ev t p * φ.ev t q

def MapOver.Intertwines (φ : MapOver C G f x) (a : C ⟶ C) (b : G ⟶ G) : Prop :=
  ∀ (T : Scheme.{0}) (t : T ⟶ Y) (p : Over.mk (t ≫ f) ⟶ C), φ.ev t (p ≫ a) = φ.ev t p ≫ b

def MapOver.PolIdentity (φ ψ : MapOver C G f x) (LC : LB C.left) (LG : LB G.left) (w : C ⟶ C) (m n : ℤ) : Prop :=
  ∀ (T : Scheme.{0}) (t : T ⟶ Y) (N : ℕ) (p q : Over.mk (t ≫ f) ⟶ C) (c : Γ(T, ⊤)ˣ), 0 < N → p ^ N = 1 → q ^ N = 1 →
    Out.WeilIs C LC N (T := Over.mk (t ≫ f)) (p ^ m * (p ≫ w) ^ n) q c →
    Out.WeilIs G LG N (T := Over.mk (t ≫ x)) (φ.ev t p) (ψ.ev t q) c

def GenerateFibres {J : Type} (φ : J → MapOver C G f x) : Prop :=
  ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ Y),
    Subgroup.closure {y : Over.mk (t ≫ x) ⟶ G | ∃ (j : J) (p : Over.mk (t ≫ f) ⟶ C), y = (φ j).ev t p} = ⊤

end Clauses

def IsSpread {D₀ : Datum H} {l : Level H} {Xo : Moduli D₀ l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (U : FamilyUnif Xo σ ty) (i : Fin U.n) {P : (U.Di i).La →+ (Fin g → ℂ)} (hP : IsPeriod (U.Di i) ty P)
    {k : Type} [Field k] [Algebra k ℂ] (C : Out.PolAV (Sp k)) (wC : C.A ⟶ C.A)
    (e : ℂ → (Over.mk (spMap (algebraMap k ℂ)) ⟶ C.A)) {Y : Scheme.{0}} (f : Y ⟶ Sp k) (s : Sp ℂ ⟶ Y) (x : Y ⟶ Xo.X)
    (φ : ∀ ε : Bool, pureVec hP ε → MapOver C.A Xo.univ.t.G f x) : Prop :=
  s ≫ x = U.u i P ∧
  (∀ (ε : Bool) (v : pureVec hP ε), (φ ε v).IsHom) ∧
  (∀ (ε : Bool) (v v' : pureVec hP ε), φ ε (v + v') = φ ε v * φ ε v') ∧
  (∀ (ε : Bool) (a : 𝓞 E) (v : pureVec hP ε), φ ε (a • v) = φ ε v ≫ Xo.univ.t.act.act a) ∧
  (∀ (ε : Bool) (v : pureVec hP ε), (φ ε v).Intertwines wC (Xo.univ.t.act.act (wTyp H ε))) ∧
  (∀ (ε ε' : Bool) (v : pureVec hP ε) (v' : pureVec hP ε'),
    (φ ε v).PolIdentity (φ ε' v') C.L Xo.univ.t.PP.L wC (polCoeffOne (U.Di i) v.1 ε' v'.1)
      (polCoeffW (U.Di i) v.1 v'.1)) ∧
  GenerateFibres (fun j : (Σ ε : Bool, pureVec hP ε) => φ j.1 j.2) ∧
  ∀ (ε : Bool) (v : pureVec hP ε) (z : ℂ) (p : Over.mk (s ≫ f) ⟶ C.A), p.left = (e z).left →
    ((φ ε v).ev s p).left = (U.ex i P (z • P v.1)).left

def CMPointSpread : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D₀ : Datum H) (l : Level H) (Xo : Moduli D₀ l)
    (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (U : FamilyUnif Xo σ ty) (i : Fin U.n)
    (P : (U.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (U.Di i) ty P), PureSpan hP →
    ∀ (k : Type) [Field k] [NumberField k] [Algebra k ℂ] (C : Out.PolAV (Sp k)) (wC : C.A ⟶ C.A)
      (e : ℂ → (Over.mk (spMap (algebraMap k ℂ)) ⟶ C.A)), C.g = 1 → IsMonHom wC → IsCurveUnif H C wC e →
      ∃ (R : Subalgebra k ℂ) (x : Sp R ⟶ Xo.X)
        (φ : ∀ ε : Bool, pureVec hP ε → MapOver C.A Xo.univ.t.G (spMap (algebraMap k R)) x),
        R.FG ∧ IsSpread U i hP C wC e (spMap (algebraMap k R)) (spMap (algebraMap R ℂ)) x φ

end GlobalTheory.IndefiniteRowSideFullHecke.CurveFormSign
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.HeightDefect.OrderValuation
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot36

open Formalism.L2.Pj Formalism.L2.PjFree NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) (c : Coeff l)

def trivialClassCondition (T : CDVR) (ι : c.F →+* T.Fr) (_y : IntFr Xo c T ι) : Prop := True

abbrev algVal (la : HeightOneSpectrum (𝓞 c.F)) : Set (Rul Xo c → EReal) := valSet Xo c (algCls Xo c) la

abbrev allVal (la : HeightOneSpectrum (𝓞 c.F)) : Set (Rul Xo c → EReal) := valSet Xo c (trivialClassCondition Xo c) la

def TrivOn (T : CDVR) (ι : c.F →+* T.Fr) : Prop := ∀ a : c.F, a ≠ 0 → vV T.V (ι a) = 0

def ordVal : Set (Rul Xo c → EReal) :=
  {o | ∃ (T : CDVR) (ι : c.F →+* T.Fr) (_ : TrivOn c T ι) (y : IntFr Xo c T ι),
    o = fun f => nval T.V 1 (evI y f)}

variable {Xo c}

def NoCommonZero {κ : Type} (w : κ → Rul Xo c) : Prop :=
  ∀ (L : Type) [Field L] [Algebra c.F L] (y : FrPt Xo c L),
    FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y → ∃ k, evR Xo c (w k) y ≠ 0

def NoCommonZeroAt (la : HeightOneSpectrum (𝓞 c.F)) {κ : Type} (w : κ → Rul Xo c) : Prop :=
  ∀ v ∈ algVal Xo c la, ∃ k, v (w k) ≠ ⊤

def LeastLe {R κ : Type} (w : κ → R) (ν : ℝ) (v : R → EReal) : Prop := ∃ k, v (w k) ≤ (ν : EReal)

def Comb {R κ : Type} (w : κ → R) (η : R) (ν c' : ℝ) (v : R → EReal) : Prop :=
  0 ≤ v η ∧ (v η ≠ ⊤ → ∃ k, v (w k) ≤ (ν : EReal) + (c' : EReal) * v η)

variable (Xo c) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)

def TransferInt : Prop :=
  ∀ (la : HeightOneSpectrum (𝓞 c.F)) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ F ∈ cusp Xo c U a n,
    (∀ v ∈ algVal Xo c la, 0 ≤ v F) → (∀ v ∈ allVal Xo c la, 0 ≤ v F) ∧ ∀ o ∈ ordVal Xo c, 0 ≤ o F

def TransferComb (nz : HeightOneSpectrum (𝓞 c.F) → ∀ {m : ℕ}, (Fin m → Rul Xo c) → Prop) : Prop :=
  ∀ (la : HeightOneSpectrum (𝓞 c.F)) (aL : (E →+* ℂ) × ℕ → ℕ) (nL : ℕ) (aE : (E →+* ℂ) × ℕ → ℕ) (nE : ℕ),
    Dom aL nL → Dom aE nE → ∀ (m : ℕ) (w : Fin m → Rul Xo c), (∀ k, w k ∈ cusp Xo c U aL nL) → nz la w →
    ∀ η ∈ cusp Xo c U aE nE, ∀ ν c' : ℝ, 0 ≤ c' →
      (∀ v ∈ algVal Xo c la, Comb w η ν c' v) →
        (∀ v ∈ allVal Xo c la, Comb w η ν c' v) ∧ ∀ o ∈ ordVal Xo c, Comb w η 0 c' o

def TransferLeast (nz : HeightOneSpectrum (𝓞 c.F) → ∀ {m : ℕ}, (Fin m → Rul Xo c) → Prop) : Prop :=
  ∀ (la : HeightOneSpectrum (𝓞 c.F)) (aL : (E →+* ℂ) × ℕ → ℕ) (nL : ℕ), Dom aL nL →
    ∀ (m : ℕ) (w : Fin m → Rul Xo c), (∀ k, w k ∈ cusp Xo c U aL nL) → nz la w → ∀ ν : ℝ,
      (∀ v ∈ algVal Xo c la, LeastLe w ν v) →
        (∀ v ∈ allVal Xo c la, LeastLe w ν v) ∧ ∀ o ∈ ordVal Xo c, LeastLe w 0 o

def Transfer : Prop :=
  TransferInt Xo c U ∧ TransferComb Xo c U (fun _ _ w => NoCommonZero w) ∧
    TransferLeast Xo c U (fun _ _ w => NoCommonZero w)

def TransferAt : Prop :=
  TransferInt Xo c U ∧ TransferComb Xo c U (fun la _ w => NoCommonZeroAt la w) ∧
    TransferLeast Xo c U (fun la _ w => NoCommonZeroAt la w)

variable {Xo c U}

theorem NoCommonZero.at {κ : Type} {w : κ → Rul Xo c} (h : NoCommonZero w) (la : HeightOneSpectrum (𝓞 c.F)) :
    NoCommonZeroAt la w := by
  rintro _ ⟨⟨q, T, ι, e, ho, y, hy, η, hη, rfl⟩, rfl⟩
  letI := ι.toAlgebra
  obtain ⟨k, hk⟩ := h T.Fr y.1 y.2.1
  refine ⟨k, ?_⟩
  show nval T.V e (evI y (w k)) ≠ ⊤
  have hk' : evI y (w k) ≠ 0 := hk
  rw [nval_of_ne hk']
  exact EReal.coe_ne_top _

theorem TransferAt.transfer (h : TransferAt Xo c U) : Transfer Xo c U :=
  ⟨h.1, fun la aL nL aE nE hL hE m w hw hz => h.2.1 la aL nL aE nE hL hE m w hw (hz.at la),
    fun la aL nL hL m w hw hz => h.2.2 la aL nL hL m w hw (hz.at la)⟩

theorem ordVal_smul {o : Rul Xo c → EReal} (ho : o ∈ ordVal Xo c) {a : c.F} (ha : a ≠ 0) (f : Rul Xo c) :
    o (a • f) = o f := by
  obtain ⟨T, ι, ht, y, rfl⟩ := ho
  show nval T.V 1 (evI y (a • f)) = nval T.V 1 (evI y f)
  rw [evI_smul]
  exact nval_mul_unit 1 ((map_ne_zero ι).2 ha) (ht a ha) _

end GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot36
end
end

