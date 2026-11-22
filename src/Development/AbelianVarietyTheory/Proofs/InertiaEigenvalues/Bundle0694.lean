import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BddGood
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfOfBasePins
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0038
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0037
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0681
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LabelUniqueOfIrreducible
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0671
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsInertTop
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SingleDatum

variable {D : D7} {H : Geo.Tor.Host D.host.E} {Dw : Datum H}

def IsHalfIdem (l : Geo.Tor.Level H) (e : AE D) : Prop :=
  ∃ P : Finset (Formalism.L2.DIV.Pl D.host.E), IsIdemSum e P ∧ ∀ PP, PP ∈ P ↔ l.Mb ≤ PP.asIdeal

def levPoint (V W : HSp D) (l : Geo.Tor.Level H) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)) (e : AE D)
    (q : Fin V.rank → LevQ Dw l) : WO V W :=
  Matrix.of fun a b => e * incA D (ι (cSep l • levRep (q b)) a / (l.M : D.host.E))

def transSum (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (l : Geo.Tor.Level H)
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)) (e : AE D) (f₀ : WO V W → ℂ) (w : (Fin V.rank → LevQ Dw l) → ℂ) :
    WO V W → ℂ :=
  ((Nat.card (Fin V.rank → LevQ Dw l) : ℂ))⁻¹ • ∑ᶠ q : Fin V.rank → LevQ Dw l, w q • heisO ψ V W (levPoint V W l ι e q) f₀

def VacPair (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle)
    (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ)
    (f₀ : WO V W → ℂ) : Prop :=
  IsPair ψ θ V W χV χW om ∧ V.rank ≠ 0 ∧ (ΛV : Set (Fin V.rank → D.host.E)) = L0c D V ∧
    (ΛW : Set (Fin W.rank → D.host.E)) = L0c D W ∧ IsSelfDualC V ΛV ∧ IsSelfDualC W ΛW ∧
    (ΛV : Set (Fin V.rank → D.host.E)) = (Formalism.L2.Pj.stdLat D.host.E V.rank : Set (Fin V.rank → D.host.E)) ∧
    (∀ τ, IsCartanInv (gramAt D W τ) (s τ)) ∧
    IsVacO ψ θ V W (fun _ => 1) s (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) f₀

def StdBase {V W : HSp D} (B : Base V W) : Prop :=
  V.gram = 1 ∧ V.SigOK ∧ (B.F.ΛS : Set (Fin V.rank → D.host.E)) = L0c D V ∧ (B.F.ΛT : Set (Fin W.rank → D.host.E)) = L0c D W ∧
    (B.F.ΛS : Set (Fin V.rank → D.host.E)) = (Formalism.L2.Pj.stdLat D.host.E V.rank : Set (Fin V.rank → D.host.E))

def Induces (W : HSp D) (l : Geo.Tor.Level H) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)) (u : GA D W)
    (g : Dw.La →ₗ[𝓞 D.host.E] Dw.La) : Prop :=
  u ∈ GfC W ∧ gLat W u = Formalism.L2.Pj.latHat W ∧ ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 D.host.E) Dw.La), ∃ w ∈ latGHat W 1,
    (finHom W u).1.mulVec (finVec W (ι a)) - finVec W (ι (g a)) = (l.M : ℕ) • w

def clsScal (χ : (AE D)ˣ →* Circle) (y : (AE D)ˣ) {n : ℕ} (Λ : GenLat D.host.E n) (r : ℕ) : ℂ :=
  ((χ y : Circle) : ℂ)⁻¹ * ((Real.sqrt ((((Λ.La ⊓ Formalism.L2.Pj.stdLat D.host.E n).toAddSubgroup.addSubgroupOf
    Λ.La.toAddSubgroup).index : ℝ) ^ r) : ℝ) : ℂ)⁻¹

variable (Dw) in

def IsLetters {m n : ℕ} (lt : LtN Dw n ≃ FVar D m n) : Prop :=
  ∀ ℓ, (lt ℓ).2.2 = ℓ.2.2 ∧ ((ℓ.1 = tauE D (lt ℓ).1 ∧ ((lt ℓ).2.1 : ℕ) = ℓ.2.1) ∨
    (ℓ.1 = conjEmb (tauE D (lt ℓ).1) ∧ ((lt ℓ).2.1 : ℕ) = Dw.p + ℓ.2.1))

variable (Dw) in

def WtIs {n : ℕ} (w : Weight D n) (a : (D.host.E →+* ℂ) × ℕ → ℕ) : Prop :=
  ∀ ρ, w.p ρ = Dw.p ∧ w.q ρ = Dw.q ∧ (∀ i < Dw.p, a (tauE D ρ, i) = w.ap ρ i) ∧
    ∀ i < Dw.q, a (conjEmb (tauE D ρ), i) = w.am ρ i

variable (Dw) in

def degA (a : (D.host.E →+* ℂ) × ℕ → ℕ) : ℕ := ∑ τ : D.host.E →+* ℂ, ∑ j : Fin (Dw.mult τ), a (τ, j)

variable {l : Geo.Tor.Level H} {Xo : Moduli Dw l}

def IsDict {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r) (W : HSp D) (hr : W.rank = r)
    (dict : GA D W → Σ k, Frame (U.X k).Ψ r) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) : Prop :=
  IsUnf U ∧ GlobalTheory.Member.IotaOK Dw W ι ∧ (∀ k, IsMod W hr (U.X k)) ∧ (∀ k, IsOrthogonalFrame (U.X k) x₀) ∧
    ∃ (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
      (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
      (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ)
      (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)),
      (∀ k τ, IsInfEmb τ.1 (th k τ)) ∧ DictLat U W hr dict ι e F ik φ th x₀

def FrameTie {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r) (W : HSp D) (hr : W.rank = r)
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (s BW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) : Prop :=
  ∀ k, IsInvOf W hr (U.X k) (fun τ => x₀ τ.1) s ∧
    ∀ hq : (U.X k).p0 + Dw.p = r, IsBasOf W hr (U.X k) hq (fun τ => x₀ τ.1) BW

def MarkedVal {c : Coeff l} {n : ℕ} (d : DeltaDat Xo c n) (θ : InfFam D) (W : HSp D) {r : ℕ} (hr : W.rank = r)
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (f : Rul d.Xo₂ d.c₂) (ν : GA D W → ℂ) : Prop :=
  ∀ (X : Data D.host.E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw)
    (k : GA D W) (mk : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E)), IsMod W hr X → X.p0 = Dw.q → IsSympl X bas →
    IdxIs c (inC c) X idx e → latR hr (latG W k) = X.Λ → IsMark d.l₂ X.Λ mk → MarkAd d.l₂ W hr ι k mk →
    letI : Algebra d.c₂.F ℂ := ((inC c).comp (d.eF.symm : d.c₂.F →+* c.F)).toAlgebra
    ∀ (y₂ : FrPt d.Xo₂ d.c₂ ℂ) (A₂ : AnFib X bas idx e (frMove θ W hr X k (fun τ => x₀ τ.1)) X.Λ y₂), A₂.Marked mk →
      evR d.Xo₂ d.c₂ f y₂ = ν k

def FibreMove {c : Coeff l} {n : ℕ} (d : DeltaDat Xo c n) (W : HSp D)
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)) {A : Type} (ν : GA D W → A) (cs : A → Rul d.Xo₂ d.c₂) : Prop :=
  ∀ (s : Sim Dw) (ρ : d.Xo₂.X ≅ d.Xo₂.X) (u : GA D W), d.Xo₂.LevAut s ρ → Induces W d.l₂ ι u (s.f d.l₂.M) →
    ∀ a a', (∀ h, ν (h * u) = a' ↔ ν h = a) →
      ∀ (K : Type) [Field K] [Algebra d.c₂.F K] (y y' : FrPt d.Xo₂ d.c₂ K),
        y'.x = CategoryTheory.CategoryStruct.comp y.x ρ.hom → evR d.Xo₂ d.c₂ (cs a') y' = evR d.Xo₂ d.c₂ (cs a) y

def IsThetaSum {c : Coeff l} {n : ℕ} (d : DeltaDat Xo c n) {T : Type} [Fintype T] (cs : T → Rul d.Xo₂ d.c₂)
    (w : T → (Fin n → LevQ Dw d.l₂) → c.F) (La : GenLat D.host.E n) (N : ℕ) (P : T → MvPolynomial (LtN Dw n) c.F)
    (f : Rul Xo c) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra d.c₂.F k],
    (∀ x : c.F, algebraMap d.c₂.F k (d.eF x) = algebraMap c.F k x) →
    ∀ (y : FrPt Xo c k) (y₂ : FrPt d.Xo₂ d.c₂ k), FrOver d y₂ y → ∃ v : T → k,
      (∀ t, thLaValAt d.Xo₂ d.c₂ d.nab₂ (fun q => d.eF (w t q)) La N
        (MvPolynomial.map (d.eF : c.F →+* d.c₂.F) (P t)) y₂ (v t)) ∧
      evR Xo c f y = ∑ t, evR d.Xo₂ d.c₂ (cs t) y₂ * v t

variable (l) in

def CoverFor (p : ℕ) (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) : Prop :=
  ∃ (pd : ℕ) (I : Ideal (𝓞 D.host.E)) (l₂ : Geo.Tor.Level H), GlobalTheory.CoverHalf.IsCoverLevel l pd I l₂ ∧ ¬ p ∣ pd ∧
    ∀ PP ∈ Q, I.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) ≤ PP.asIdeal ∧ (pd : 𝓞 D.host.E) ∈ PP.asIdeal

def UnramOver (F F₁ : IntermediateField ℚ ℂ) (p : ℕ) : Prop :=
  ∀ τ : ℂ ≃+* ℂ, (∀ x ∈ F, τ x = x) → (∀ x ∈ F₁, τ x ∈ F₁) ∧
    ∀ O : ValuationSubring ℂ, (p : ℂ) ∈ O.nonunits → (∀ x : ℂ, IsAlgebraic ℚ x → x ∈ O → τ x - x ∈ O.nonunits) →
      ∀ x ∈ F₁, τ x = x

def IsInert (A : ValuationSubring ℂ) (K : Subfield ℂ) : Prop :=
  ∀ τ : ℂ ≃+* ℂ, (∀ x ∈ K, τ x = x) → ∀ x : ℂ, IsAlgebraic ℚ x → x ∈ A → τ x - x ∈ A.nonunits

def intOf (A : ValuationSubring ℂ) (K : Subfield ℂ) : Subring ℂ := A.toSubring ⊓ K.toSubring

theorem mem_intOf {A : ValuationSubring ℂ} {K : Subfield ℂ} {x : ℂ} : x ∈ intOf A K ↔ x ∈ A ∧ x ∈ K := Iff.rfl

def PlaceOf (A : ValuationSubring ℂ) (F : IntermediateField ℚ ℂ) [NumberField F] (la : HeightOneSpectrum (𝓞 F)) : Prop :=
  ∀ x : F, la.valuation F x ≤ 1 ↔ (x : ℂ) ∈ A

def ValIn (t : Twist D Circle) (K : Subfield ℂ) : Prop :=
  (∃ m : ℕ, 0 < m ∧ ∀ x, t.chi x ^ m = 1) ∧ (∀ x, ((t.chi x : Circle) : ℂ) ∈ K) ∧
    ∀ PP ∈ t.Q, ∀ u, ((t.res PP u : Circle) : ℂ) ∈ K

def HeckeIn (χ : Formalism.L2.Host.HChar D.host.E) (b : ℕ) (K : Subfield ℂ) : Prop :=
  ∀ P : HeightOneSpectrum (𝓞 D.host.E), (b : 𝓞 D.host.E) ∉ P.asIdeal → GlobalTheory.IdemSupport.cP P ≠ P →
    ((χ.val P : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm P.asIdeal) : ℝ) : ℂ) ∈ K

def formLat (O : Subring ℂ) {c : Coeff l} (la : HeightOneSpectrum (𝓞 c.F)) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)
    (σ : c.F →+* ℂ) (W : HSp D) (dict : GA D W → Σ k, Frame ((U σ).X k).Ψ r) (mu : GA D W → ℂ) (cc : (U σ).Comp → ℂ)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Submodule O (GA D W → ℂ) :=
  Submodule.span O {φ | ∃ f ∈ GlobalTheory.GoodPts.supSet Xo c la (cusp Xo c U a n),
    φ = (lieFac Dw (xiR D) a : ℂ) • adel W dict (muPin W dict mu cc) (rdU (U σ) f)}

theorem isInert_top (A : ValuationSubring ℂ) : IsInert A ⊤ := fun τ h x _ _ => by
  rw [h x trivial, sub_self]
  exact zero_mem _

theorem IsInert.mono {A : ValuationSubring ℂ} {K K' : Subfield ℂ} (h : IsInert A K) (hK : K ≤ K') : IsInert A K' :=
  fun τ hτ => h τ fun x hx => hτ x (hK hx)

end GlobalTheory.SingleDatum

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIrreducibleSecondFactorOfIrreducibleProduct
section
open NumberField ReciprocityTheory.Gal Formalism.ConjugateSelfDual IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.CuspRep GlobalTheory.DefiniteBC

open Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SmGL.ProdIrr

theorem exists_mem_ind_apply_one {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup W] [Module ℂ W]
    (hG : ∀ N ∈ 𝓝 (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ ∀ g ∈ K, g ∈ N)
    (P : Subgroup G) (σ : Representation ℂ P W) (hσ : IsSmooth σ) (u : W) :
    ∃ f : smoothPart (ind P σ), f.1.1 1 = u ∧ ∀ g, f.1.1 g = 0 ∨ ∃ p, f.1.1 g = σ p u := by
  classical
  obtain ⟨N, hN, hNS⟩ := (mem_nhds_subtype _ _ _).1 ((hσ u).mem_nhds (show σ 1 u = u by simp))
  obtain ⟨K, hKo, hKN⟩ := hG N (by simpa using hN)
  have hfix : ∀ p : P, (p : G) ∈ K → σ p u = u := fun p hp => hNS (hKN _ hp)
  have wd : ∀ (p p' : P) (c c' : G), c ∈ K → c' ∈ K → (p : G) * c = p' * c' → σ p u = σ p' u := by
    intro p p' c c' hc hc' h
    have hm : ((p'⁻¹ * p : P) : G) ∈ K := by
      have : ((p'⁻¹ * p : P) : G) = c' * c⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h, mul_inv_cancel_right]
      rw [this]; exact mul_mem hc' (inv_mem hc)
    have h2 := hfix _ hm
    rw [map_mul, Module.End.mul_apply] at h2
    calc σ p u = σ p' (σ p'⁻¹ (σ p u)) := by
          rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
      _ = σ p' u := by rw [h2]
  let F : G → W := fun g => if h : ∃ p : P, ∃ c ∈ K, g = (p : G) * c then σ h.choose u else 0
  have hF : ∀ (p : P) (c : G), c ∈ K → F ((p : G) * c) = σ p u := by
    intro p c hc
    have h : ∃ p' : P, ∃ c' ∈ K, (p : G) * c = (p' : G) * c' := ⟨p, c, hc, rfl⟩
    simp only [F, dif_pos h]
    obtain ⟨c', hc', e⟩ := h.choose_spec
    exact wd _ _ _ _ hc' hc e.symm
  have hF0 : ∀ g, (¬ ∃ p : P, ∃ c ∈ K, g = (p : G) * c) → F g = 0 := fun g h => by
    simp only [F, dif_neg h]
  have hmem : F ∈ indSpace P σ := by
    intro h g
    by_cases hg : ∃ p : P, ∃ c ∈ K, g = (p : G) * c
    · obtain ⟨p, c, hc, rfl⟩ := hg
      rw [← mul_assoc, show (h : G) * p = ((h * p : P) : G) from rfl, hF _ _ hc, hF _ _ hc, map_mul,
        Module.End.mul_apply]
    · have : ¬ ∃ p : P, ∃ c ∈ K, (h : G) * g = (p : G) * c := by
        rintro ⟨p, c, hc, e⟩
        exact hg ⟨h⁻¹ * p, c, hc, by rw [Subgroup.coe_mul, mul_assoc, ← e]; simp⟩
      rw [hF0 _ hg, hF0 _ this, map_zero]
  refine ⟨⟨⟨F, hmem⟩, mem_smoothPart_of_nhds (Filter.mem_of_superset (hKo.mem_nhds K.one_mem) fun c hc => ?_)⟩,
    ?_, ?_⟩
  · apply Subtype.ext; funext x
    show F (x * c) = F x
    by_cases hx : ∃ p : P, ∃ c' ∈ K, x = (p : G) * c'
    · obtain ⟨p, c', hc', rfl⟩ := hx
      rw [mul_assoc, hF _ _ (mul_mem hc' hc), hF _ _ hc']
    · have : ¬ ∃ p : P, ∃ c' ∈ K, x * c = (p : G) * c' := by
        rintro ⟨p, c', hc', e⟩
        exact hx ⟨p, c' * c⁻¹, mul_mem hc' (inv_mem hc), by rw [← mul_assoc, ← e, mul_inv_cancel_right]⟩
      rw [hF0 _ hx, hF0 _ this]
  · show F 1 = u
    have := hF 1 1 K.one_mem
    simpa using this
  · intro g
    show F g = 0 ∨ ∃ p, F g = σ p u
    by_cases hg : ∃ p : P, ∃ c ∈ K, g = (p : G) * c
    · obtain ⟨p, c, hc, rfl⟩ := hg; exact Or.inr ⟨p, hF _ _ hc⟩
    · exact Or.inl (hF0 _ hg)

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
  [Fintype n] [DecidableEq n]

theorem continuous_leviProj (e : (Σ a, m a) ≃ n) : Continuous (leviProj k e) := by
  refine continuous_pi fun a => Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    simp only [Function.comp_def, leviProj_apply]
    exact (Units.continuous_val.comp continuous_subtype_val).matrix_elem _ _
  · have : (fun p : parab k e => (((leviProj k e p a)⁻¹ : GL (m a) k) : Matrix (m a) (m a) k)) =
        fun p => ((leviProj k e p⁻¹ a : GL (m a) k) : Matrix (m a) (m a) k) := by
      funext p; rw [map_inv]; rfl
    rw [this]
    refine continuous_matrix fun i j => ?_
    simp only [leviProj_apply]
    exact ((Units.continuous_val.comp continuous_subtype_val).comp continuous_inv).matrix_elem _ _

theorem exists_openSubgroup_GL :
    ∀ N ∈ 𝓝 (1 : GL n k), ∃ K : Subgroup (GL n k), IsOpen (K : Set (GL n k)) ∧ ∀ g ∈ K, g ∈ N := by
  intro N hN
  obtain ⟨γ, hγ, h⟩ := GlobalTheory.CentralExponent.exists_cong_subset hN
  exact ⟨_, GlobalTheory.CentralExponent.isOpen_cong γ hγ, h⟩

theorem exists_indSp_apply_one {W : Type} [AddCommGroup W] [Module ℂ W] (e : (Σ a, m a) ≃ n)
    (ρ : Representation ℂ (Levi k m) W) (hρ : IsSmooth ρ) (u : W) :
    ∃ f : IndSp e ρ, f.1.1 1 = u ∧ ∀ g, f.1.1 g = 0 ∨ ∃ l : Levi k m, ∃ c : ℂ, f.1.1 g = c • ρ l u := by
  obtain ⟨f, h1, h2⟩ := exists_mem_ind_apply_one exists_openSubgroup_GL (parab k e) _
    (isSmooth_comp (isSmooth_twist hρ (isSmoothChar_deltaHalf k)) _ (continuous_leviProj e)) u
  exact ⟨f, h1, fun g => (h2 g).imp id fun ⟨p, hp⟩ => ⟨leviProj k e p, _, hp⟩⟩

end Local

end GlobalTheory.SmGL.ProdIrr

namespace GlobalTheory.SmGL.ProdIrr

theorem isIrreducible_of_prod₂ : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (r t : ℕ) (V W U : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U]
    (σ₀ : Representation ℂ (GL (Fin r) k) V) (τ : Representation ℂ (GL (Fin t) k) W)
    (π : Representation ℂ (GL (Fin (r + t)) k) U),
    IsSmooth σ₀ → σ₀.IsIrreducible → IsSmooth τ → π.IsIrreducible → Nonempty (π.Equiv (prod₂ σ₀ τ)) →
      τ.IsIrreducible := by
  intro k _ _ _ _ r t V W U _ _ _ _ _ _ σ₀ τ π hσs hσi hτs hπi ⟨Φ⟩
  classical
  have hI : (prod₂ σ₀ τ).IsIrreducible := (MultiIrr.isIrreducible_iff_of_equiv Φ).1 hπi
  obtain ⟨hV, -⟩ := (isIrreducible_iff σ₀).1 hσi
  obtain ⟨hX, hIirr⟩ := (isIrreducible_iff _).1 hI
  obtain ⟨x₀, hx₀⟩ := exists_ne (0 : V)
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ V, φ x₀ ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx₀ ((Module.forall_dual_apply_eq_zero_iff ℂ x₀).1 h)
  let L : V ⊗[ℂ] W →ₗ[ℂ] W := (TensorProduct.lid ℂ W).toLinearMap ∘ₗ LinearMap.rTensor W φ
  have hL : ∀ x w, L (x ⊗ₜ w) = φ x • w := fun x w => by simp [L]
  let ρ' := (extTensor σ₀ τ).comp (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom
  have hρ' : IsSmooth ρ' := isSmooth_comp (isSmooth_extTensor hσs hτs) _
    (show Continuous fun g : Levi k (Two (Fin r) (Fin t)) => (g false, g true) from
      (continuous_apply false).prodMk (continuous_apply true))
  have hW : Nontrivial W := by
    by_contra hW
    rw [not_nontrivial_iff_subsingleton] at hW
    have h0 : ∀ z : V ⊗[ℂ] W, z = 0 := fun z => z.induction_on rfl
      (fun x w => by rw [Subsingleton.elim w 0, TensorProduct.tmul_zero])
      (fun a b ha hb => by rw [ha, hb, add_zero])
    obtain ⟨f₁, f₂, hne⟩ := hX
    exact hne (Subtype.ext (Subtype.ext (funext fun x => (h0 _).trans (h0 _).symm)))
  rw [isIrreducible_iff]
  refine ⟨hW, fun S hS => ?_⟩
  by_cases hS0 : S = ⊥
  · exact Or.inl hS0
  right
  obtain ⟨s, hsS, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS0
  let R : Submodule ℂ (V ⊗[ℂ] W) := LinearMap.range (LinearMap.lTensor V S.subtype)
  have hR : ∀ l, ∀ y ∈ R, ρ' l y ∈ R := by
    rintro l _ ⟨z, rfl⟩
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x w =>
      exact ⟨σ₀ ((leviTwo k (Fin r) (Fin t)).symm l).1 x ⊗ₜ
        ⟨τ ((leviTwo k (Fin r) (Fin t)).symm l).2 w, hS _ _ w.2⟩, by simp [ρ']⟩
    | add a b ha hb =>
      rw [map_add, map_add]; exact add_mem ha hb
  have hLR : ∀ y ∈ R, L y ∈ S := by
    rintro _ ⟨z, rfl⟩
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x w => rw [LinearMap.lTensor_tmul, hL]; exact S.smul_mem _ w.2
    | add a b ha hb => rw [map_add, map_add]; exact add_mem ha hb
  let Y : Submodule ℂ (IndSp (two (stdSum (rfl : r + t = r + t))) ρ') :=
    { carrier := {f | ∀ g, f.1.1 g ∈ R}
      add_mem' := fun ha hb g => add_mem (ha g) (hb g)
      zero_mem' := fun g => zero_mem R
      smul_mem' := fun c f hf g => R.smul_mem c (hf g) }
  have hYs : ∀ g, ∀ f ∈ Y, prod₂ σ₀ τ g f ∈ Y := fun g f hf x => hf (x * g)
  have hmemY : ∀ (u : V ⊗[ℂ] W), u ∈ R → ∃ f ∈ Y, f.1.1 1 = u := by
    intro u hu
    obtain ⟨f, h1, h2⟩ := exists_indSp_apply_one (two (stdSum (rfl : r + t = r + t))) ρ' hρ' u
    refine ⟨f, fun g => ?_, h1⟩
    rcases h2 g with h | ⟨l, c, h⟩
    · rw [h]; exact zero_mem R
    · rw [h]; exact R.smul_mem c (hR l u hu)
  have hYtop : Y = ⊤ := by
    refine (hIirr Y hYs).resolve_left fun hY => ?_
    obtain ⟨f, hf, h1⟩ := hmemY (x₀ ⊗ₜ s) ⟨x₀ ⊗ₜ ⟨s, hsS⟩, rfl⟩
    rw [hY, Submodule.mem_bot] at hf
    have : L (x₀ ⊗ₜ s) = 0 := by rw [← h1, hf]; rfl
    rw [hL] at this
    exact smul_ne_zero hφ hs0 this
  refine eq_top_iff.2 fun v _ => ?_
  obtain ⟨f, h1, -⟩ := exists_indSp_apply_one (two (stdSum (rfl : r + t = r + t))) ρ' hρ' (x₀ ⊗ₜ v)
  have hf : f ∈ Y := hYtop ▸ Submodule.mem_top
  have h2 := hLR _ (h1 ▸ hf 1)
  rw [hL] at h2
  exact (S.smul_mem_iff hφ).1 h2

end GlobalTheory.SmGL.ProdIrr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSqIntCoeffOfIsSquareIntegrable
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL MeasureTheory

namespace GlobalTheory.LocGL.SqIntBridge

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V : Type} [AddCommGroup V] [Module ℂ V] {N : ℕ} {π : Representation ℂ (GL (Fin N) k) V}

theorem exists_central_scalar (hs : IsSmooth π) (hi : π.IsIrreducible) (hu : IsUnitarisable π) {z : GL (Fin N) k}
    (hz : z ∈ Subgroup.center (GL (Fin N) k)) : ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ v, π z v = c • v := by
  obtain ⟨c, hc⟩ := schur_GL hs hi ⟨π z, fun g => by
    rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, ← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz g]⟩
  have hc' : ∀ v, π z v = c • v := hc
  refine ⟨c, ?_, hc'⟩
  obtain ⟨B, -, hp, hB⟩ := hu
  have := Model.nontrivial_of_isIrreducible hi
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have h0 : B v v ≠ 0 := fun e => by simpa [e] using hp v hv
  have h1 := congrArg norm (hB z v v)
  rw [hc'] at h1
  simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, norm_mul, RingHom.id_apply, RCLike.norm_conj] at h1
  have h2 : 0 < ‖B v v‖ := norm_pos_iff.2 h0
  have h3 : ‖c‖ * ‖c‖ = 1 := mul_right_cancel₀ h2.ne' (by rw [mul_assoc, h1, one_mul])
  nlinarith [norm_nonneg c]

theorem norm_coeff_out (hs : IsSmooth π) (hi : π.IsIrreducible) (hu : IsUnitarisable π) (v : V) (l : Module.Dual ℂ V)
    (g : GL (Fin N) k) : ‖l (π (QuotientGroup.mk g : AdGL k N).out v)‖ = ‖l (π g v)‖ := by
  obtain ⟨z, hz⟩ := QuotientGroup.mk_out_eq_mul (Subgroup.center (GL (Fin N) k)) g
  obtain ⟨c, h1, hc⟩ := exists_central_scalar hs hi hu z.2
  rw [hz, map_mul, Module.End.mul_apply, hc, map_smul, map_smul, norm_smul, h1, one_mul]

omit [ValuativeRel k] in

theorem isLocallyConstant_orbit [IsTopologicalRing k] (hs : IsSmooth π) (v : V) :
    IsLocallyConstant fun g : GL (Fin N) k => π g v := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun g => ?_
  refine Filter.mem_of_superset (((hs v).preimage (continuous_const_mul g⁻¹)).mem_nhds (by simp)) fun x hx => ?_
  have hx' : π (g⁻¹ * x) v = v := hx
  show π x v = π g v
  conv_rhs => rw [← hx', ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]

theorem isSqIntCoeff_of_isSquareIntegrable {δ : IrrGL k} (h : UnitaryDual.IsSquareIntegrable δ) :
    IsSqIntCoeff δ.rep := by
  obtain ⟨-, hu, ν, hν, H⟩ := h
  intro m hm μ hμ v l hl
  obtain rfl : m = _root_.borel _ := hm.measurable_eq
  letI : MeasurableSpace (AdGL k δ.1) := _root_.borel _
  have := secondCountableTopology_GL k (Fin δ.1)
  have hs := δ.2.rep.smooth
  have hF := norm_coeff_out hs δ.2.rep.irr hu v l
  have hl' : l ∈ smoothPart δ.rep.dual := hl.preimage continuous_inv
  refine ⟨fun q => ‖l (δ.rep q.out v)‖, hF, ?_, ?_⟩
  · refine Continuous.aestronglyMeasurable ((QuotientGroup.isQuotientMap_mk _).continuous_iff.2 ?_)
    rw [show (fun q : AdGL k δ.1 => ‖l (δ.rep q.out v)‖) ∘ QuotientGroup.mk = fun g => ‖l (δ.rep g v)‖ from funext hF]
    exact ((isLocallyConstant_orbit hs v).comp fun w => ‖l w‖).continuous
  · rw [show ENNReal.ofReal 2 = 2 by simp, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top,
      Measure.isMulLeftInvariant_eq_smul μ ν, lintegral_smul_measure]
    have h1 := H v l hl'
    simp only [enorm_norm, ENNReal.toReal_ofNat, ENNReal.rpow_two]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top h1

end GlobalTheory.LocGL.SqIntBridge

namespace GlobalTheory.Published

theorem squareIntegrableSegment_of_ess (h : EssSquareIntegrableSegments) : SquareIntegrableSegment := by
  intro k _ _ _ _ _ δ hδ
  refine (h k δ hδ.1).1 ⟨1, isSmoothChar_one, ?_⟩
  rw [IrrGL.tw_one]
  exact SqIntBridge.isSqIntCoeff_of_isSquareIntegrable hδ

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsStratifiedPhiModuleHomOfGaloisEquivariantStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isStratifiedPhiModuleHom_of_galois_equivariant : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d d' : ℕ) (S : Strat bk d) (S' : Strat bk d') (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (ρ' : ↥(GK K) → Matrix (Fin d') (Fin d') ℤ_[l]) (T : Matrix (Fin d) (Fin d) (WCb l)) (T' : Matrix (Fin d') (Fin d') (WCb l)), MReal S ρ T → MReal S' ρ' T' → ∀ f : Matrix (Fin d') (Fin d) ℤ_[l], (∀ g, f * ρ g = ρ' g * f) → ∀ Y : Matrix (Fin d') (Fin d) bk.S, T' * Y.map bk.evW = zW f * T → IsStratHom S S' Y := by
  first | exact @GlobalTheory.isStratHom_of_equivariant | exact GlobalTheory.isStratHom_of_equivariant | (intros; apply GlobalTheory.isStratHom_of_equivariant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LabelUniqueOfIrreducibleStatement
section
open GlobalTheory.GLq GlobalTheory.GLp Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.label_unique_of_irreducible : ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g), 5 ≤ g → Green → ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) ℚ_[g]) V), IsIrrRep π → ∀ f f', HasLab L π f → HasLab L π f' → f = f' := by
  first | exact @GlobalTheory.GLp.OneLabel.label_unique | exact GlobalTheory.GLp.OneLabel.label_unique | (intros; apply GlobalTheory.GLp.OneLabel.label_unique <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LagrangiansTransverseEqGraphsRationalUnitaryStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lagrangians_transverse_eq_graphs_rational_unitary : ∀ (D : D7) (W : HSp D), ∃ e : GQ W ≃ {Y : Lag W // Y.1.comap (LinearMap.inl D.host.E _ _) = ⊥},
    ∀ γ : GQ W, ∃ c : Matrix (Fin W.rank) (Fin W.rank) D.host.E, mt W (γ : GA D W) = c.map (incA D) ∧ IsLagFrame W (e γ).1 (1, c) := by
  first | exact @GlobalTheory.RawLift.Graphs.graphs | exact GlobalTheory.RawLift.Graphs.graphs | (intros; apply GlobalTheory.RawLift.Graphs.graphs <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LanglandsClassificationSupercuspidalSupportMultiStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.langlandsClassification_supercuspidalSupport_multisegment : ZelevinskyPolynomialRing → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (𝔪 : Multiset (Segment k)) (x : IrrGL k), IsL 𝔪 x.rep → HasSupport x.rep (msupp 𝔪) := by
  first | exact @GlobalTheory.LocGL.hasSupport_msupp_of_isL | exact GlobalTheory.LocGL.hasSupport_msupp_of_isL | (intros; apply GlobalTheory.LocGL.hasSupport_msupp_of_isL <;> assumption)
end

