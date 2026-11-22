import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006

-- bundled from Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.FourierColumnIndicator
section
open NumberField IsDedekindDomain MeasureTheory
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.FourierColumnIndicator

def Zmu (K : Type) [Field K] (g : ℕ) : Subalgebra ℤ K := Algebra.adjoin ℤ {ζ : K | ζ ^ (g * (g - 1)) = 1}

section Notions

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K]

def FnModAt (P : HeightOneSpectrum (𝓞 E)) {a b : ℕ} (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b))
    (Φ : HomE E a b → K) : Prop :=
  (∀ x, Φ x ≠ 0 → x ∈ homAt {P} N N') ∧
  (∀ x z, z ∈ homAt {P} N N' → Φ (x + (qOf P : E) • z) = Φ x) ∧
  ∀ x, Φ x ∈ Zmu K (qOf P)

abbrev FnMod (P : HeightOneSpectrum (𝓞 E)) {a b : ℕ} (Φ : HomE E a b → K) : Prop :=
  FnModAt P (stdLat E a) (stdLat E b) Φ

def ColFn (P : HeightOneSpectrum (𝓞 E)) {n : ℕ} (f : Sp E n → K) : Prop :=
  (∀ y, f y ≠ 0 → (qOf P : E) • y ∈ stdAt E n P) ∧
  (∀ y z, z ∈ stdAt E n P → f (y + z) = f y) ∧
  ∀ y, f y ∈ Zmu K (qOf P)

def InDual (P : HeightOneSpectrum (𝓞 E)) {n : ℕ} (ξ : Sp E n →ₗ[E] E) : Prop := ∀ y ∈ stdAt E n P, IntAt P (ξ y)

def DualFn (P : HeightOneSpectrum (𝓞 E)) {n : ℕ} (F : (Sp E n →ₗ[E] E) → K) : Prop :=
  (∀ ξ, F ξ ≠ 0 → InDual P ξ) ∧
  (∀ ξ ξ', InDual P ξ' → F (ξ + (qOf P : E) • ξ') = F ξ) ∧
  ∀ ξ, F ξ ∈ Zmu K (qOf P)

omit [StarRing E] in
open Classical in

theorem colFn_indicator (P : HeightOneSpectrum (𝓞 E)) {n : ℕ} (y₀ : Sp E n) (h₀ : (qOf P : E) • y₀ ∈ stdAt E n P) :
    ColFn P (fun y => if y - y₀ ∈ stdAt E n P then (1 : K) else 0) := by
  refine ⟨fun y hy => ?_, fun y z hz => ?_, fun y => ?_⟩
  · have h : y - y₀ ∈ stdAt E n P := by
      by_contra h
      exact hy (if_neg h)
    have h1 : (qOf P : E) • (y - y₀) ∈ stdAt E n P := by
      rw [Nat.cast_smul_eq_nsmul]
      exact nsmul_mem h _
    have h2 := add_mem h1 h₀
    rwa [← smul_add, sub_add_cancel] at h2
  · have h1 : y + z - y₀ = (y - y₀) + z := by abel
    simp only [h1, Submodule.add_mem_iff_left _ hz]
  · dsimp only
    split_ifs
    · exact one_mem _
    · exact zero_mem _

end Notions

section Padic

variable {g : ℕ} [Fact g.Prime] {n : ℕ}

def stdP (g : ℕ) [Fact g.Prime] (n : ℕ) : Set (Fin n → ℚ_[g]) := {y | ∀ i, ‖y i‖ ≤ 1}

def InDualP (ξ : (Fin n → ℚ_[g]) →ₗ[ℚ_[g]] ℚ_[g]) : Prop := ∀ y ∈ stdP g n, ‖ξ y‖ ≤ 1

def repP (t : Fin n → Fin g) : Fin n → ℚ_[g] := fun i => ((t i : ℕ) : ℚ_[g]) / (g : ℚ_[g])

def fourierP [MeasurableSpace (Fin n → ℚ_[g])] (μ : Measure (Fin n → ℚ_[g])) (ψ : AddChar ℚ_[g] ℂ)
    (f : (Fin n → ℚ_[g]) → ℂ) (ξ : (Fin n → ℚ_[g]) →ₗ[ℚ_[g]] ℚ_[g]) : ℂ :=
  ∫ y, f y * (starRingEnd ℂ) (ψ (ξ y)) ∂μ

end Padic

def FourierLattice : Prop :=
  ∀ (g : ℕ) [Fact g.Prime] (n : ℕ) [MeasurableSpace (Fin n → ℚ_[g])] [BorelSpace (Fin n → ℚ_[g])]
    (μ : Measure (Fin n → ℚ_[g])) [μ.IsAddHaarMeasure] (ψ : AddChar ℚ_[g] ℂ),
    (∀ a : ℚ_[g], ‖a‖ ≤ 1 → ψ a = 1) → (∃ a : ℚ_[g], ‖(g : ℚ_[g]) * a‖ ≤ 1 ∧ ψ a ≠ 1) →
    ∀ f : (Fin n → ℚ_[g]) → ℂ,
      (∀ y, f y ≠ 0 → (g : ℚ_[g]) • y ∈ stdP g n) → (∀ y z, z ∈ stdP g n → f (y + z) = f y) →
      (∀ ξ : (Fin n → ℚ_[g]) →ₗ[ℚ_[g]] ℚ_[g], Integrable (fun y => f y * (starRingEnd ℂ) (ψ (ξ y))) μ) ∧
      (∀ ξ, fourierP μ ψ f ξ ≠ 0 → InDualP ξ) ∧
      (∀ ξ ξ', InDualP ξ' → fourierP μ ψ f (ξ + (g : ℚ_[g]) • ξ') = fourierP μ ψ f ξ) ∧
      (∀ ξ, InDualP ξ → fourierP μ ψ f ξ =
        (μ.real (stdP g n) : ℂ) * ∑ t : Fin n → Fin g, f (repP t) * (starRingEnd ℂ) (ψ (ξ (repP t)))) ∧
      ((∀ y, f y ∈ Zmu ℂ g) → ∀ ξ, ∃ z ∈ Zmu ℂ g, fourierP μ ψ f ξ = (μ.real (stdP g n) : ℂ) * z)

section Chain

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))

def restrX {E : Type} [Field E] {n' c' n c : ℕ} (x : HomE E (n' + c') (n + c)) : HomE E n' n :=
  LinearMap.funLeft E E (Fin.castAdd c) ∘ₗ x ∘ₗ Loc.inX E n' c'

def colX {E : Type} [Field E] {n' c' n c : ℕ} (x : HomE E (n' + c') (n + c)) : Sp E n :=
  LinearMap.funLeft E E (Fin.castAdd c) (x (Loc.eN E (n' + c') n'))

def fhat {n : ℕ} (P : rowSG Pr sel mu) (f : Sp X.E n → X.K) (η : Sp X.E n →ₗ[X.E] X.E) : X.K :=
  ∑ y ∈ Fintype.piFinset fun _ : Fin n => LocE.valsQ X.E (qOf P.1) 1 0, f y * ftY sel mu cst P η y

def topDatum (m2 : ℕ) (P : rowSG Pr sel mu) (f : Sp X.E (R.N (m2 + 1)) → X.K) (x : HomE X.E (R.N (m2 + 1)) (R.N R.m)) : X.K :=
  PhiTop Ch mu cst.sharp m2 P.1 (prXp X.E R ∘ₗ x ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) *
    fhat sel mu cst P f (atNL X.E (R.N R.m) (R.N R.m - 1) ∘ₗ x)

def facPen {u : Pr.Word} (m2 : ℕ) (al : L.β m2) (p₀ : ChPt (R := R) sel mu u m2) (p : ChPt (R := R) sel mu u (m2 + 1))
    (Y : Set (Sp X.E (R.N (m2 + 1)))) (P : rowSG Pr sel mu) (x : HomE X.E (R.N m2) (R.N (m2 + 1))) : X.K :=
  PsiAt Ch sel mu cst m2 P (L.h m2 al P) (inFr (frsF sel mu p₀ P) (frsF sel mu p P) x) ((frsF sel mu p P).symm (repY Y))

def facTop {u : Pr.Word} (m2 : ℕ) (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1)))) (d : RowPt Pr R sel mu)
    (P : rowSG Pr sel mu) (x : HomE X.E (R.N (m2 + 1)) (R.N R.m)) : X.K :=
  PhiTop Ch mu cst.sharp m2 P.1 ((d.1.liftFr P).symm.toLinearMap ∘ₗ prXp X.E R ∘ₗ x ∘ₗ (frsF sel mu p P).toLinearMap ∘ₗ
      LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) *
    ftY sel mu cst P ((((Pr.piT u : 𝓞 X.E) : X.E)⁻¹ • atNL X.E (R.N R.m) (R.N R.m - 1)) ∘ₗ x ∘ₗ (frsF sel mu p P).toLinearMap)
      ((frsF sel mu p P).symm (repY Y))

def SplitAt (m2 : ℕ) (P : rowSG Pr sel mu) (hal : AutY X R m2) : Prop :=
  (∀ x, omPhi Ch sel mu cst m2 P hal 1 x = PsiAt Ch sel mu cst m2 P hal (restrX x) (colX x)) ∧
  ∃ (ι : Type) (_ : Fintype ι) (Ψ : ι → HomE X.E (R.N m2) (R.N (m2 + 1)) → X.K) (f : ι → Sp X.E (R.N (m2 + 1)) → X.K),
    (∀ a, FnMod P.1 (Ψ a)) ∧ (∀ a, ColFn P.1 (f a)) ∧
    ∀ x₀ y, PsiAt Ch sel mu cst m2 P hal x₀ y = ∑ a, Ψ a x₀ * f a y

end Chain

def ChainData : Prop :=
  ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S)
    (cst : LocCst X (rowSG Pr sel mu)) (m2 : ℕ), Pr.Ok → cst.Ok → R.m = m2 + 2 →
    ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs →
      (∀ hal ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) m2 P.1), SplitAt Ch sel mu cst m2 P hal) ∧
      (∀ f : Sp X.E (R.N (m2 + 1)) → X.K, ColFn P.1 f → DualFn P.1 (fhat sel mu cst P f)) ∧
      (∀ f : Sp X.E (R.N (m2 + 1)) → X.K, ColFn P.1 f → FnMod P.1 (topDatum Ch sel mu cst m2 P f)) ∧
      (∀ (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (al : L.β m2),
        L.h m2 al P ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) m2 P.1) →
        ∀ (u : Pr.Word) (p₀ : ChPt (R := R) sel mu u m2) (p : ChPt (R := R) sel mu u (m2 + 1)),
        ∀ Y ∈ ybSet sel mu cst p.deco.1.N,
          FnModAt P.1 p₀.deco.1.N p.deco.1.N (facPen Ch sel mu cst L m2 al p₀ p Y P)) ∧
      (∀ (u : Pr.Word) (p : ChPt (R := R) sel mu u (m2 + 1)) (d : RowPt Pr R sel mu),
        ∀ Y ∈ ybSet sel mu cst p.deco.1.N,
          FnModAt P.1 p.deco.1.N (tilQ sel mu u d).1.N (facTop Ch sel mu cst m2 p Y d P))

def LastTwoSteps : Prop := FourierLattice ∧ ChainData

end GlobalTheory.IndefiniteRowSideFullHecke.FourierColumnIndicator
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.LatticeFramesPrimeToLevel
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointHilbertLifts

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host Neutral.B1
open scoped Matrix

section Adelic

variable {R : Ranks} (H : Formalism.BasicNotions.Host R)

abbrev Ad : Type := FiniteAdeleRing (𝓞 H.E) H.E

def AdConj (x y : Ad H) : Prop :=
  (x, y) ∈ closure (Set.range fun a : H.E => (algebraMap H.E (Ad H) a, algebraMap H.E (Ad H) (H.conj a)))

def IsUnitaryAd {N : ℕ} (g : GL (Fin N) (Ad H)) : Prop :=
  ∀ a b, AdConj H ((g : Matrix (Fin N) (Fin N) (Ad H)) a b) (((g⁻¹ : GL (Fin N) (Ad H)) : Matrix (Fin N) (Fin N) (Ad H)) b a)

def IsHilbLift (x : Ideles H.E) (d : Ad H) : Prop :=
  IsFinIdele x ∧ ∃ xb : Ad H, AdConj H (x : AdeleRing (𝓞 H.E) H.E).2 xb ∧ (x : AdeleRing (𝓞 H.E) H.E).2 = d * xb

def IsTildeVal (μ χ : HChar H.E) (a n : ℤ) (d : Ad H) (z : ℂ) : Prop :=
  ∃ x : Ideles H.E, IsHilbLift H x d ∧ z = (((μ.1 x) ^ a * (χ.1 x) ^ n : ℂˣ) : ℂ)

def StabAt (l : ℕ) {N : ℕ} (M : Matrix (Fin N) (Fin N) (Ad H)) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 H.E), OverP H l v →
    (∀ a b, M a b v ∈ v.adicCompletionIntegers H.E) ∧ Valued.v (M.det v) = 1

def IsBasisAt (l : ℕ) {N : ℕ} (g : GL (Fin N) (Ad H)) (b : Matrix (Fin N) (Fin N) H.E) : Prop :=
  StabAt H l (((g⁻¹ : GL (Fin N) (Ad H)) : Matrix (Fin N) (Fin N) (Ad H)) * b.map (algebraMap H.E (Ad H)))

end Adelic

section abelian₂

variable {l : ℕ} [Fact l.Prime] (lam : (algebraicClosure ℚ ℂ) →+* ℂ_[l])

def IntAt (z : ℂ) : Prop := ∃ h : z ∈ algebraicClosure ℚ ℂ, ‖lam ⟨z, h⟩‖ ≤ 1

def UnitAt (z : ℂ) : Prop := ∃ h : z ∈ algebraicClosure ℚ ℂ, ‖lam ⟨z, h⟩‖ = 1

def IsLatFrame {R : Ranks} (H : Formalism.BasicNotions.Host R) (φ : H.E →+* ℂ) {N : ℕ} (g : GL (Fin N) (Ad H))
    (y : Matrix (Fin N) (Fin N) ℂ) : Prop :=
  ∃ (b : Matrix (Fin N) (Fin N) H.E) (k : Matrix (Fin N) (Fin N) ℂ),
    IsBasisAt H l g b ∧ (∀ a a', IntAt lam (k a a')) ∧ UnitAt lam k.det ∧ y = b.map φ * k

end abelian₂

def LamOver (D : D7) (w : D.what₂.places.Pl) [Fact (D.what₂.places.resChar w).Prime]
    (lam : (algebraicClosure ℚ ℂ) →+* ℂ_[D.what₂.places.resChar w]) : Prop :=
  ∀ x : D.what₂.LL, IntAt lam (D.what₂.embLL x) ↔ 0 ≤ D.what₂.places.val w x

abbrev Reps (D : D7) (u : D.what₂.Word) (μ : D.what₂.Tup) : Type :=
  ∀ i, (D.chTw u μ).cls i → GL (Fin (D.R.N i)) (Ad D.host)

abbrev Frames (D : D7) (u : D.what₂.Word) (μ : D.what₂.Tup) : Type :=
  ∀ i, (D.chTw u μ).Y i → D.what₂.Tau → Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) ℂ

def RepTie (D : D7) (u : D.what₂.Word) (μ : D.what₂.Tup) (g : Reps D u μ) : Prop :=
  ∀ i, i ≤ D.R.m → ∀ c, IsUnitaryAd D.host (g i c)

def RhoTie (D : D7) (C : CharFrame D) {nch : NChoice D} (Tp : TupTied D C nch) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (g : Reps D u μ) : Prop :=
  ∀ (i : ℕ) (hi : i < D.R.m),
    (∀ c, IsTildeVal D.host (Tp.tup μ ⟨i, hi⟩) C.chiPsi (-1) (-((D.R.N (i + 1) / 2 : ℕ) : ℤ))
      (g i c : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) (Ad D.host)).det ((D.chTw u μ).rhoDet i c)) ∧
    (∀ c', IsTildeVal D.host (Tp.tup μ ⟨i, hi⟩) C.chiPsi 1 ((D.R.N i / 2 : ℕ) : ℤ)
      (g (i + 1) c' : Matrix (Fin (D.R.N (i + 1))) (Fin (D.R.N (i + 1))) (Ad D.host)).det ((D.chTw u μ).rhoDet' i c'))

def FrameTie (D : D7) (u : D.what₂.Word) (μ : D.what₂.Tup) (fr : Frames D u μ) : Prop :=
  ∀ i, i ≤ D.R.m →
    Function.Injective (fr i) ∧ (∀ M, M ∈ Set.range (fr i) ↔ ∀ τ, (M τ).det ≠ 0) ∧
      ∀ y τ, (D.chTw u μ).de i y τ = (fr i y τ).det

def PrimeToLevels (D : D7) {C : CharFrame D} {nch : NChoice D} (Tp : TupTied D C nch) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (l : ℕ) : Prop :=
  l ≠ (D.mem u).A.T ∧ (∀ k, l ≠ D.host.g k) ∧ ∀ v, OverP D.host l v → (Tp.xi μ).UnrAt v

def eps (D : D7) (u : D.what₂.Word) (μ : D.what₂.Tup) (i : ℕ) (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1)) : ℂ :=
  (D.chTw u μ).rhoDet i c * (D.chTw u μ).rhoDet' i c'

def epsFr (D : D7) (u : D.what₂.Word) (μ : D.what₂.Tup) (i : ℕ) (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1))
    (y : (D.chTw u μ).Y i) (y' : (D.chTw u μ).Y (i + 1)) : ℂ :=
  eps D u μ i c c' * (∏ τ, (D.chTw u μ).de i y τ ^ (D.chTw u μ).sSharp i τ) *
    (∏ τ, (D.chTw u μ).de (i + 1) y' τ ^ (D.chTw u μ).sDiv i τ)⁻¹

def UnUnit_at (D : D7) (C : CharFrame D) (nch : NChoice D) (Tp : TupTied D C nch) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (g : Reps D u μ) (fr : Frames D u μ) : Prop :=
  RepTie D u μ g → RhoTie D C Tp u μ g → FrameTie D u μ fr →
  ∀ (w : D.what₂.places.Pl) [Fact (D.what₂.places.resChar w).Prime]
    (lam : (algebraicClosure ℚ ℂ) →+* ℂ_[D.what₂.places.resChar w]), LamOver D w lam →
    PrimeToLevels D Tp u μ (D.what₂.places.resChar w) →
    ∀ i, i < D.R.m → ∀ (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1))
      (y : (D.chTw u μ).Y i) (y' : (D.chTw u μ).Y (i + 1)),
      (∀ τ, IsLatFrame lam D.host (embTau D τ) (g i c) (fr i y τ)) →
      (∀ τ, IsLatFrame lam D.host (embTau D τ) (g (i + 1) c') (fr (i + 1) y' τ)) →
      UnitAt lam (epsFr D u μ i c c' y y')

def UnUnitBase_at (D : D7) (C : CharFrame D) (nch : NChoice D) (Tp : TupTied D C nch) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (g : Reps D u μ) : Prop :=
  RepTie D u μ g → RhoTie D C Tp u μ g →
  ∀ (w : D.what₂.places.Pl) [Fact (D.what₂.places.resChar w).Prime]
    (lam : (algebraicClosure ℚ ℂ) →+* ℂ_[D.what₂.places.resChar w]), LamOver D w lam →
    PrimeToLevels D Tp u μ (D.what₂.places.resChar w) →
    ∀ i, i < D.R.m → ∀ (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1)),
      StabAt D.host (D.what₂.places.resChar w)
        (((g i c)⁻¹ : GL (Fin (D.R.N i)) (Ad D.host)) : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) (Ad D.host)) →
      StabAt D.host (D.what₂.places.resChar w)
        (((g (i + 1) c')⁻¹ : GL (Fin (D.R.N (i + 1))) (Ad D.host)) :
          Matrix (Fin (D.R.N (i + 1))) (Fin (D.R.N (i + 1))) (Ad D.host)) →
      UnitAt lam (eps D u μ i c c')

end GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointHilbertLifts
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.UnfoldedLatticeData
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnfoldedLatticeData

open Formalism.L2.Col

section Local

variable (g : ℕ) [Fact g.Prime]

abbrev Aut (N : ℕ) : Type := (Fin N → ℚ_[g]) ≃ₗ[ℚ_[g]] (Fin N → ℚ_[g])

abbrev HomQ (a b : ℕ) : Type := (Fin a → ℚ_[g]) →ₗ[ℚ_[g]] (Fin b → ℚ_[g])

abbrev Lat (N : ℕ) : Type := Submodule ℤ_[g] (Fin N → ℚ_[g])

def diagLat (N : ℕ) (e : ℕ → ℕ) : Lat g N :=
  Submodule.span ℤ_[g]
    (Set.range fun l : Fin N => (g : ℚ_[g]) ^ e l.1 • (Pi.single l 1 : Fin N → ℚ_[g]))

def stdLat (N : ℕ) : Lat g N := diagLat g N fun _ => 0

def lamSt (n c : ℕ) : Lat g (n + c) := diagLat g (n + c) fun l => if l < n then 0 else l - n + 1

def lamBase (hyp : Bool) (n c : ℕ) : Lat g (n + c) := if hyp then stdLat g (n + c) else lamSt g n c

variable {g}

def img {N : ℕ} (h : Aut g N) (Λ : Lat g N) : Lat g N := Λ.map (h.toLinearMap.restrictScalars ℤ_[g])

def GLlat {N : ℕ} (Λ : Lat g N) : Subgroup (Aut g N) where
  carrier := {κ | ∀ v, κ v ∈ Λ ↔ v ∈ Λ}
  one_mem' := fun _ => Iff.rfl
  mul_mem' := fun {a b} ha hb v => (ha (b v)).trans (hb v)
  inv_mem' := fun {a} ha v => by
    have h := ha (a.symm v)
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm

def InG {N : ℕ} (Λ : Lat g N) (v : Fin N → ℚ_[g]) : Prop := ∃ u ∈ Λ, v = (g : ℚ_[g]) • u

def Into {a b : ℕ} (Λ' : Lat g a) (Λ : Lat g b) (x : HomQ g a b) : Prop := ∀ v ∈ Λ', x v ∈ Λ

def InjMod {a b : ℕ} (Λ' : Lat g a) (Λ : Lat g b) (x : HomQ g a b) : Prop :=
  ∀ v ∈ Λ', InG Λ (x v) → InG Λ' v

def PeriodG {a b : ℕ} {M : Type} (Λ' : Lat g a) (Λ : Lat g b) (F : HomQ g a b → M) : Prop :=
  ∀ x y, Into Λ' Λ y → F (x + (g : ℚ_[g]) • y) = F x

def IsMu (g : ℕ) (ζ : ℂ) : Prop := ζ ^ (g * (g - 1)) = 1

def ZMu (g : ℕ) : Subalgebra ℤ ℂ := Algebra.adjoin ℤ {ζ | IsMu g ζ}

def CondO (ψ : AddChar ℚ_[g] ℂ) : Prop :=
  (∀ u : ℤ_[g], ψ (u : ℚ_[g]) = 1) ∧ ∃ u : ℤ_[g], ψ ((u : ℚ_[g]) / (g : ℚ_[g])) ≠ 1

def Shape {a b : ℕ} (Λ' : Lat g a) (Λ₀ : Lat g b) (Φ : Loc.SF ℚ_[g] ℂ a b) : Prop :=
  (∀ x, Φ x ≠ 0 → Into Λ' Λ₀ x ∧ InjMod Λ' Λ₀ x ∧ IsMu g (Φ x)) ∧ PeriodG Λ' Λ₀ Φ

def IsLevel {N : ℕ} (Λ₀ : Lat g N) (J : Subgroup (Aut g N)) : Prop :=
  J ≤ GLlat Λ₀ ∧ ∀ κ ∈ GLlat Λ₀, (∀ v ∈ Λ₀, InG Λ₀ (κ v - v)) → κ ∈ J

def omg {a b : ℕ} (μ : ℚ_[g] →*₀ ℂ) (g₀ : Aut g a) (h : Aut g b) (Φ : Loc.SF ℚ_[g] ℂ a b) :
    Loc.SF ℚ_[g] ℂ a b :=
  Loc.om μ Padic.valuation ((Real.sqrt g : ℝ) : ℂ) g₀ h Φ

def PartialFourierTransformFinite {n' n c : ℕ} (ψ : AddChar ℚ_[g] ℂ) (A B : ℕ) (Φ : Loc.SF ℚ_[g] ℂ (n' + (c + 1)) (n + c)) :
    Loc.SF ℚ_[g] ℂ n' n :=
  Loc.E1 (fun t => ψ t) (LocE.valsQ ℚ_[g] g A B) (((g : ℂ) ^ B)⁻¹) Φ

def IsRationalUnitaryDeterminantMap {n' n c : ℕ} (ψ : AddChar ℚ_[g] ℂ) (Φ : Loc.SF ℚ_[g] ℂ (n' + (c + 1)) (n + c))
    (Ψ : Loc.SF ℚ_[g] ℂ n' n) : Prop :=
  ∃ A₀ B₀ : ℕ, ∀ A B, A₀ ≤ A → B₀ ≤ B → PartialFourierTransformFinite ψ A B Φ = Ψ

def GoodFlag {n c : ℕ} (Λ : Lat g (n + c)) : Prop :=
  (∀ s < c, ∀ z : ℚ_[g],
    (∃ v ∈ Λ, v ∈ Loc.Ufl ℚ_[g] n c (s + 1) ∧ Loc.atN v (n + s) = z) ↔
      ∃ u : ℤ_[g], z = (g : ℚ_[g]) ^ (s + 1) * u) ∧
  (g : ℚ_[g]) • Loc.eN ℚ_[g] (n + c) n ∈ Λ

def scal {a b : ℕ} (μ : ℚ_[g] →*₀ ℂ) (h' : Aut g a) (h : Aut g b) : ℂ :=
  μ (LinearEquiv.det h' : ℚ_[g]ˣ) * (μ (LinearEquiv.det h : ℚ_[g]ˣ))⁻¹ *
    ((Real.sqrt g : ℝ) : ℂ) ^ (Padic.valuation ((LinearEquiv.det h : ℚ_[g]ˣ) : ℚ_[g]) * (a : ℤ))

def volAt {n c : ℕ} (Λ : Lat g (n + c)) (C : Subgroup (Aut g (n + c))) : ℂ :=
  Loc.volN ℂ C (Loc.N1 ℚ_[g] n c ⊓ GLlat Λ)

end Local

def e₁ (n c : ℕ) : ℕ := ∑ i ∈ Finset.Icc 1 c, (i * n + i * (i - 1) / 2)

def dimN (n c : ℕ) : ℕ := c * (c - 1) / 2 + (c - 1) * n

def expS (n c : ℕ) : ℕ :=
  ∑ i ∈ Finset.Icc 1 c, ∑ i' ∈ Finset.Ico 1 i, (i - i') + n * ∑ i ∈ Finset.Icc 2 c, i

def expSup (n c : ℕ) : ℕ := ∑ i ∈ Finset.Icc 1 c, (n + i)

section Clauses

variable (g : ℕ) [Fact g.Prime] (hyp : Bool) (n' n c : ℕ)

def SupportClause : Prop :=
  ∀ (ψ : AddChar ℚ_[g] ℂ) (μ : ℚ_[g] →*₀ ℂ) (Φ : Loc.SF ℚ_[g] ℂ (n' + (c + 1)) (n + c))
    (h' : Aut g (n' + (c + 1))) (h : Aut g (n + c)),
    CondO ψ → Shape (lamSt g n' (c + 1)) (lamBase g hyp n c) Φ → h' ∈ GLlat (lamSt g n' (c + 1)) →
      (∀ x, omg μ h' h Φ x ≠ 0 → Into (lamSt g n' (c + 1)) (img h (lamBase g hyp n c)) x) ∧
      PeriodG (lamSt g n' (c + 1)) (img h (lamBase g hyp n c)) (omg μ h' h Φ) ∧
      (∃ Ψ, IsRationalUnitaryDeterminantMap ψ (omg μ h' h Φ) Ψ) ∧
      (¬ IsRationalUnitaryDeterminantMap ψ (omg μ h' h Φ) 0 →
        GoodFlag (img h (lamBase g hyp n c)) ∧
        (∃ ρ ∈ Loc.R1 ℚ_[g] n c, img ρ (lamSt g n c) = img h (lamBase g hyp n c)) ∧
        ∀ h₀ : Aut g (n + c), img h₀ (lamBase g hyp n c) = lamSt g n c →
          ∃ ρ ∈ Loc.R1 ℚ_[g] n c, ∃ κ ∈ GLlat (lamBase g hyp n c), h = ρ * h₀ * κ)

def ShapeClause : Prop :=
  (∀ h : Aut g (n + c), GoodFlag (img h (lamBase g hyp n c)) →
    ∃ ρ ∈ Loc.R1 ℚ_[g] n c, img ρ (lamSt g n c) = img h (lamBase g hyp n c)) ∧
  (∃ h₀ : Aut g (n + c), img h₀ (lamBase g hyp n c) = lamSt g n c) ∧
  ∀ h : Aut g (n + c), img h (lamBase g hyp n c) = lamSt g n c →
    Padic.valuation ((LinearEquiv.det h : ℚ_[g]ˣ) : ℚ_[g]) =
      if hyp then ((c * (c + 1) / 2 : ℕ) : ℤ) else 0

def EntryClause (m N : ℕ) : Prop :=
  ∀ (J : Subgroup (Aut g (n + c))) (h : Aut g (n + c)),
    IsLevel (lamBase g hyp n c) J → img h (lamBase g hyp n c) = lamSt g n c →
      ∃ e₂ : ℕ, e₂ ≤ dimN n c ∧
        (volAt (lamSt g n c) (Loc.Cbe J h))⁻¹ = (g : ℂ) ^ e₂ ∧
        6 * (e₁ n c + e₂) ≤ 3 * m ^ 2 * N + m ^ 3 + 6 * m ^ 2 + 6 * m * N ∧
        e₁ n c + e₂ ≤ 4 * m ^ 2 * N ∧
        e₁ n c + e₂ + m * (N + m) ≤ 4 * m ^ 2 * N ∧
        ∀ (ψ : AddChar ℚ_[g] ℂ) (μ : ℚ_[g] →*₀ ℂ) (Φ : Loc.SF ℚ_[g] ℂ (n' + (c + 1)) (n + c))
          (h' : Aut g (n' + (c + 1))),
          CondO ψ → Shape (lamSt g n' (c + 1)) (lamBase g hyp n c) Φ →
          h' ∈ GLlat (lamSt g n' (c + 1)) →
            (∃ (Ψ : Loc.SF ℚ_[g] ℂ n' n) (Ψ₀ : HomQ g n' n → ZMu g),
              IsRationalUnitaryDeterminantMap ψ (omg μ h' h Φ) Ψ ∧
              (∀ x, Ψ x = scal μ h' h * (g : ℂ) ^ e₁ n c * (Ψ₀ x : ℂ)) ∧
              (∀ x, (volAt (lamSt g n c) (Loc.Cbe J h))⁻¹ * Ψ x =
                scal μ h' h * (g : ℂ) ^ (e₁ n c + e₂) * (Ψ₀ x : ℂ)) ∧
              (∀ x, Ψ₀ x ≠ 0 → Into (stdLat g n') (stdLat g n) x ∧ InjMod (stdLat g n') (stdLat g n) x) ∧
              PeriodG (stdLat g n') (stdLat g n) Ψ₀ ∧
              (∀ x, ∃ s : Multiset ℂ, Multiset.card s ≤ g ^ expSup n c ∧ Multiset.card s ≤ g ^ (m * (N + m)) ∧
                (∀ ζ ∈ s, IsMu g ζ) ∧ s.sum = (Ψ₀ x : ℂ)) ∧
              ∀ (σ : ZMu g →+* ℂ) (x : HomQ g n' n),
                ‖σ (Ψ₀ x)‖ ≤ (g : ℝ) ^ expSup n c ∧ ‖σ (Ψ₀ x)‖ ≤ (g : ℝ) ^ (m * (N + m))) ∧
            (hyp = false → (∀ u : ℤ_[g]ˣ, μ ((u : ℤ_[g]) : ℚ_[g]) ^ (g - 1) = 1) →
              scal μ h' h ^ (g - 1) = 1)

def MeasureClause (m N : ℕ) : Prop :=
  volAt (stdLat g (n + c)) (GLlat (lamSt g n c)) = (g : ℂ) ^ expS n c ∧
  expS n c ≤ m ^ 3 + m ^ 2 * N ∧ dimN n c ≤ m ^ 2 + m * N ∧ e₁ n c = expS n c + n

end Clauses

def UnfoldedDatum : Prop :=
  ∀ (g : ℕ) [Fact g.Prime] (hyp : Bool) (m j c n' t n N : ℕ),
    2 ≤ m → m ≤ N → 1 ≤ j → j + 2 ≤ m → c + j + 1 = m → n = n' + t + 1 → n ≤ N →
      SupportClause g hyp n' n c ∧ ShapeClause g hyp n c ∧ EntryClause g hyp n' n c m N ∧
        MeasureClause g n c m N

example : e₁ 5 2 = 16 ∧ dimN 5 2 = 6 ∧ expS 5 2 = 11 ∧ expSup 5 2 = 13 := by decide

example {g : ℕ} [Fact g.Prime] {a : ℕ} (Λ : Lat g a) :
    Into Λ Λ LinearMap.id ∧ InjMod Λ Λ LinearMap.id := ⟨fun _ h => h, fun _ _ h => h⟩

end GlobalTheory.IndefiniteRowSideFullHecke.UnfoldedLatticeData
end
end

