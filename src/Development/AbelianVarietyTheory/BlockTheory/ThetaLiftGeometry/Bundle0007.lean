import Mathlib
import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
import Formalism.LocalRingCardinality.DataDIV
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
import Formalism.LocalRingCardinality.Bundle0005
import Formalism.LocalRingCardinality.DataKerI
import Formalism.LocalToGlobal.Divisibility.CoefMod

-- bundled from Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.BadPrimesPeriodBound
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker

@[reducible] def recFields (D : D7) : Fields where
  F := D.host.F
  E := D.host.E
  K := D.what₂.LL
  starE := D.host.cmStar
  Tau := D.what₂.Tau
  deTau := Classical.decEq _
  emb τ := D.embE.comp (D.host.sigmaOf (D.eTau τ : D.R.GG) : D.host.E →+* D.host.E)

@[reducible] def recPrimes {D : D7} (EX : ErrX D) : Primes (recFields D) where
  cond := D.host.QS * D.host.q * D.host.d
  g := D.host.g
  piG := EX.piG
  Word := D.what₂.Word
  deWord := Classical.decEq _
  T u := (D.mem u).A.T
  piT := EX.piT

def recWts {D : D7} (EX : ErrX D) : Wts (recFields D) (recPrimes EX).Word D.R where
  row τ := RowPar.of (D.hc τ)
  hc := D.hcW
  tops := topsOf D.host D.eTau

def recSeam (D : D7) : Seam D (recFields D) where
  iE := RingEquiv.refl _
  iT := Equiv.refl _
  σ₀ := D.what₂.embLL

def badS (D : D7) : Set ℕ :=
  hostS D.host.q D.host.d (D.host.g 0) (D.host.g 1)
    ((Set.range fun u : D.what₂.Word => (D.mem u).A.T) ∪ (D.host.small : Set ℕ))

theorem T_mem_badS (D : D7) (u : D.what₂.Word) : (D.mem u).A.T ∈ badS D := Or.inr (Or.inl ⟨u, rfl⟩)

theorem small_mem_badS (D : D7) (l : ℕ) (h : l ∈ D.host.small) : l ∈ badS D := Or.inr (Or.inr (Finset.mem_coe.2 h))

theorem g_mem_badS (D : D7) (i : Fin 2) : D.host.g i ∈ badS D := Or.inl (by fin_cases i <;> simp)

abbrev Twist (D : D7) : Type := Tup (recFields D).F (recFields D).E (recFields D).K (badS D)

def recGlob (D : D7) (mu0 : Fin D.R.m → Formalism.L2.Host.HChar D.host.E) : ChGlob (recFields D) D.R.m where
  σ₀ := D.what₂.embLL
  xi0 := D.host.xi0
  mu0 := mu0

def HostTie {D : D7} (EX : ErrX D) : Prop :=
  D.host.ccK = ⊤ ∧ GL3Theta.InducedCMType D ∧ GL3Theta.HostFieldConditions D ∧ (recFields D).AbelianUnramifiedExtensionConditions ∧ (recPrimes EX).Ok

def CharTie {D : D7} {EX : ErrX D} (Ch : Chars (recFields D) (recPrimes EX) D.R.m)
    (mu0 : Fin D.R.m → Formalism.L2.Host.HChar D.host.E) (eta : Formalism.L2.Host.HChar D.host.E)
    (sel : HeightOneSpectrum (𝓞 D.host.F) → HeightOneSpectrum (𝓞 D.host.E)) : Prop :=
  Ch.Ok ∧ Ch.Tied D.what₂.embLL (fun j τ => (D.hc τ).e j) mu0 eta ∧ Ch.WeilTied D.what₂.embLL D.host.xi0 ∧
    IsSel (recFields D) sel

def AnTie (D : D7) (δ : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) : Prop :=
  TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D D.host.ccK δ ∧ TaylorLogMetric.IsChi D χ ∧ IsDgen D cD

def SizeAt (D : D7) (i : Fin 2) : Prop :=
  2 * D.R.f * D.R.N D.R.m + 1 < D.host.g i ∧
    ∀ u : D.what₂.Word, ∀ j ∈ LiftErrorLocal.lifts D,
      2 * LiftErrorLocal.Dpi D u j + 2 < (D.host.g i : ℝ) ∧ LiftErrorLocal.Dpi D u j + (D.R.N D.R.m : ℝ) < (D.host.g i : ℝ)

def TwistTie {D : D7} (Dx : DivX D) (μ : D.what₂.Tup) (ξ : Twist D) : Prop :=
  ((Dx.Qp μ : Set ℕ) = QprimeN (ξ : Chr (recFields D).F (recFields D).E (recFields D).K)) ∧ (μ = D.what₂.mu0 → ξ = 1)

open Classical in

def JetsRatDeg {X : Fields} (A : Amb X) (a b : ℕ) (Sb : Finset (HeightOneSpectrum (𝓞 X.E))) (M : ℕ) (deg : X.Tau → ℤ) : Prop :=
  ∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (c : ℕ) (x : HomE X.E a b),
    InRange Sb M c N N' x → ∀ e : DVar X.Tau a b →₀ ℕ,
      (∀ τ, ((∑ k ∈ e.support.filter (fun k => k.1 = τ), e k : ℕ) : ℤ) = deg τ) →
      ∃ y : X.K, A.σ₀ y = (A.chiF a b N N')⁻¹ * jetC A.cD (A.thInd Sb N N' c x) e

section Ties

variable {D : D7} {EX : ErrX D} (Ch : Chars (recFields D) (recPrimes EX) D.R.m)
  (sel : HeightOneSpectrum (𝓞 D.host.F) → HeightOneSpectrum (𝓞 D.host.E))

def FieldTie (A : Amb (recFields D)) (ξ : Twist D) (cst : LocCst (recFields D) (rowSG (recPrimes EX) sel ξ))
    (u : D.what₂.Word) : Prop :=
  ∀ i < D.R.m, JetsRatDeg A (D.R.N i) (D.R.N (i + 1)) (Sall (Pr := recPrimes EX) sel ξ u)
    (cAof sel ξ cst * cBof sel ξ cst u) (fun τ => ∑ a, ((recWts EX).nuW u (i + 1) τ).w a)

def ColTie (u : D.what₂.Word) (eM : (D.div.Nu u).V ≃ₗ[D.what₂.LL] MramV (recWts EX) Ch u) : Prop :=
  ∀ x, x ∈ DV.MramL D u ↔ eM x ∈ Formalism.L2.Col.MramL (recWts EX) Ch u

def RowTie (μ : D.what₂.Tup) (ξ : Twist D)
    (jA : MtildeV (recWts EX) Ch sel ξ (rPsymF Ch) →ₛₗ[D.what₂.embLL] D.what₂.Amb μ) : Prop :=
  (∀ s : Finset (MtildeV (recWts EX) Ch sel ξ (rPsymF Ch)),
      LinearIndependent D.what₂.LL (fun x : s => (x : MtildeV (recWts EX) Ch sel ξ (rPsymF Ch))) →
      LinearIndependent ℂ (fun x : s => jA x)) ∧
    Submodule.span ℂ (Set.range jA) = ⊤ ∧
    (∀ v ∈ (D.what₂.Mtilde μ).gen, v ∈ Set.range jA) ∧
    ∀ x, x ∈ MtildeL (recWts EX) Ch sel ξ (rPsymF Ch) ↔ ∃ c : D.what₂.Amb μ → 𝓞 D.what₂.LL,
      jA x = ∑ v ∈ (D.what₂.Mtilde μ).gen, D.what₂.embLL ((c v : 𝓞 D.what₂.LL) : D.what₂.LL) • v

def PerTie (u : D.what₂.Word) (μ : D.what₂.Tup) (ξ : Twist D)
    (hP : (mtildeGSD (recWts EX) Ch sel ξ (rPsymF Ch)).Ok)
    (col : MfV (recWts EX) Ch u →ₗ[D.what₂.LL] (evGSD (recWts EX) Ch sel ξ (rPsymF Ch) u).EqFun)
    (eM : (D.div.Nu u).V ≃ₗ[D.what₂.LL] MramV (recWts EX) Ch u)
    (jA : MtildeV (recWts EX) Ch sel ξ (rPsymF Ch) →ₛₗ[D.what₂.embLL] D.what₂.Amb μ) : Prop :=
  ∀ φ x, D.what₂.perCol u μ (D.jN u φ) (jA x) =
    D.what₂.embLL (PtilE (recWts EX) Ch sel ξ (rPsymF Ch) hP u (col (eM φ : MfV (recWts EX) Ch u)) x)

def ChainTie (Dx : DivX D) (mu0 : Fin D.R.m → Formalism.L2.Host.HChar D.host.E) (A : Amb (recFields D))
    (u : D.what₂.Word) (μ : D.what₂.Tup) : Prop :=
  ∃ (ξ : Twist D) (cst : LocCst (recFields D) (rowSG (recPrimes EX) sel ξ))
    (I : ChIdx (recFields D) (recPrimes EX) D.R (QE sel (ξ : Chr (recFields D).F (recFields D).E (recFields D).K)))
    (hI : I.Ok Ch sel ξ cst (recGlob D mu0) (D.R.m - 2))
    (b : I.β (D.R.m - 2 + 1)) (hY : YbHyp (R := D.R) sel ξ cst I u (D.R.m - 2) b)
    (hK : KerEquivC (recWts EX) Ch sel ξ cst I A u (D.R.m - 2) b hY (rPsymF Ch))
    (hF : ∀ j, (chF (recWts EX) sel ξ I u j).Ok)
    (hP : (mtildeGSD (recWts EX) Ch sel ξ (rPsymF Ch)).Ok)
    (eM : (D.div.Nu u).V ≃ₗ[D.what₂.LL] MramV (recWts EX) Ch u)
    (jA : MtildeV (recWts EX) Ch sel ξ (rPsymF Ch) →ₛₗ[D.what₂.embLL] D.what₂.Amb μ),
    cst.sharp = true ∧ TwistTie Dx μ ξ ∧ FieldTie sel A ξ cst u ∧ ColTie Ch u eM ∧ RowTie Ch sel μ ξ jA ∧
      PerTie Ch sel u μ ξ hP (colMu (recWts EX) Ch sel ξ cst I A u (D.R.m - 2) b hY (rPsymF Ch) hK hF hI) eM jA

end Ties

def BoundAt {D : D7} (L : SizeData₂ D) (EX : ErrX D) (C1 : ℝ) (i : Fin 2) (w : LiftErrorLocal.Pl D) (u : D.what₂.Word)
    (μ : D.what₂.Tup) : Prop :=
  ∀ φ ∈ DV.MramL D u, ∀ F ∈ (D.what₂.Mtilde μ).carrier, ∃ y : D.what₂.LL,
    D.what₂.embLL y = D.what₂.perCol u μ (D.jN u φ) F ∧
      (y = 0 ∨ -(∑ j ∈ LiftErrorLocal.lifts D, vNN EX i u j w) - C1 * LiftErrorLocal.errC D L ≤ LiftErrorLocal.vG D w y)

def periodBound_at (D : D7) (L : SizeData₂ D) (EX : ErrX D) (Dx : DivX D)
    (Ch : Chars (recFields D) (recPrimes EX) D.R.m)
    (mu0 : Fin D.R.m → Formalism.L2.Host.HChar D.host.E) (eta : Formalism.L2.Host.HChar D.host.E)
    (sel : HeightOneSpectrum (𝓞 D.host.F) → HeightOneSpectrum (𝓞 D.host.E))
    {δ : ℂ} (B : Base D D.host.ccK δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (C1 : ℝ) : Prop :=
  HostTie EX → CharTie Ch mu0 eta sel → AnTie D δ χ cD →
    ∀ (i : Fin 2), SizeAt D i → ∀ w : LiftErrorLocal.Pl D, LiftErrorLocal.Over D i w →
      ∀ u : D.what₂.Word, D.what₂.places.resChar w ≠ (D.mem u).A.T →
        ∀ μ : D.what₂.Tup, D.host.g i ∉ Dx.Qp μ →
          ChainTie Ch sel Dx mu0 (ambOf (recSeam D) B χ cD) u μ → BoundAt L EX C1 i w u μ

theorem recSeam_emb (D : D7) (τ : D.what₂.Tau) (x : D.host.E) :
    (recSeam D).σ₀ ((recFields D).emb τ x) = TaylorLogMetric.embT D ((recSeam D).iT τ) ((recSeam D).iE x) := by
  have h := RingHom.congr_fun D.embE_φ₀ (D.host.sigmaOf (D.eTau τ : D.R.GG) x)
  exact h

theorem recWts_row {D : D7} (EX : ErrX D) (u : D.what₂.Word) (τ : D.what₂.Tau) :
    RowPar.of ((recWts EX).hc u τ) = (recWts EX).row τ := by
  show RowPar.of (D.hcW u τ) = RowPar.of (D.hc τ)
  simp only [RowPar.of, D.hcW_v, D.hcW_b, D.hcW_e]

end GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.ColumnAvoidanceConditions
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ColumnAvoidanceConditions

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV

@[reducible] def fieldsOf (D : D7) : Fields where
  F := D.host.F
  E := D.host.E
  K := D.what₂.LL
  starE := D.host.cmStar
  Tau := D.what₂.Tau
  deTau := Classical.decEq _
  emb τ := D.embE.comp (D.host.sigmaOf (D.eTau τ : D.R.GG) : D.host.E →+* D.host.E)

@[reducible] def primesOf (D : D7) (EX : ErrX D) : Primes (fieldsOf D) where
  cond := D.host.QS * D.host.q * D.host.d
  g := D.host.g
  piG := EX.piG
  Word := D.what₂.Word
  ftWord := D.wordFin
  deWord := Classical.decEq _
  T u := (D.mem u).A.T
  piT := EX.piT

def wtsOf (D : D7) (EX : ErrX D) : Wts (fieldsOf D) (primesOf D EX).Word D.R where
  row τ := RowPar.of (D.hc τ)
  hc := D.hcW
  tops := topsOf D.host D.eTau

def seamOf (D : D7) : Seam D (fieldsOf D) where
  iE := RingEquiv.refl _
  iT := Equiv.refl _
  σ₀ := D.what₂.embLL

def globOf (D : D7) (m0 : Fin D.R.m → Formalism.L2.Host.HChar D.host.E) : ChGlob (fieldsOf D) D.R.m where
  σ₀ := D.what₂.embLL
  xi0 := D.host.xi0
  mu0 := m0

example (D : D7) (τ : D.what₂.Tau) (x : D.host.E) : (fieldsOf D).emb τ x = tauLL D τ x := rfl

example (D : D7) (τ : D.what₂.Tau) (x : D.host.E) :
    (seamOf D).σ₀ ((fieldsOf D).emb τ x) = TaylorLogMetric.embT D ((seamOf D).iT τ) ((seamOf D).iE x) :=
  DFunLike.congr_fun D.embE_φ₀ _

section Ties

variable (D : D7) (Dx : DivX D) (EX : ErrX D) (Ch : Chars (fieldsOf D) (primesOf D EX) D.R.m)
  (m0 : Fin D.R.m → Formalism.L2.Host.HChar D.host.E)
  (sel : HeightOneSpectrum (𝓞 (fieldsOf D).F) → HeightOneSpectrum (𝓞 (fieldsOf D).E))

def HostTie : Prop := GL3Theta.InducedCMType D ∧ GL3Theta.HostFieldConditions D ∧ D.host.ccK = ⊤

def PrimeTie : Prop := (primesOf D EX).Ok ∧ (primesOf D EX).PiGCong

def CharTie : Prop :=
  Ch.Ok ∧ ∃ eta : Formalism.L2.Host.HChar D.host.E, Ch.Tied D.what₂.embLL (fun j τ => (D.hc τ).e j) m0 eta

def ThetaTie (δ : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) : Prop :=
  TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D ⊤ δ ∧ TaylorLogMetric.IsChi D χ ∧ IsDgen D cD

def RangeG (i : Fin 2) (u : D.what₂.Word) : Prop :=
  2 * D.R.f * D.R.N D.R.m + 1 < D.host.g i ∧
  (∀ j ∈ LiftErrorLocal.lifts D, 2 * LiftErrorLocal.Dpi D u j + 2 < (D.host.g i : ℝ)) ∧
  ∀ j, j ≤ D.R.m → ∀ τ, ((wtsOf D EX).lamTrue u j τ).spread < (D.host.g i : ℤ)

def AvoidTie (i : Fin 2) (u : D.what₂.Word) (S : Set ℕ) : Prop :=
  (∀ l ∈ D.host.small, l ∈ S) ∧ D.host.q ∈ S ∧ D.host.d ∈ S ∧ D.host.g (1 - i) ∈ S ∧ (D.mem u).A.T ∈ S

variable {S : Set ℕ} (ξ : Tup (fieldsOf D).F (fieldsOf D).E (fieldsOf D).K S)

def TupTie (μ : D.what₂.Tup) : Prop :=
  (μ = D.what₂.mu0 → ξ = 1) ∧
    (Dx.Qp μ : Set ℕ) = QprimeN (ξ : Chr (fieldsOf D).F (fieldsOf D).E (fieldsOf D).K)

def FieldTie (cst : LocCst (fieldsOf D) (rowSG (primesOf D EX) sel ξ)) (A : Amb (fieldsOf D)) (u : D.what₂.Word) : Prop :=
  letI := (fieldsOf D).starE
  ∀ s, s < D.R.m →
    ∀ (N : Submodule (𝓞 (fieldsOf D).E) (Sp (fieldsOf D).E (D.R.N s)))
      (N' : Submodule (𝓞 (fieldsOf D).E) (Sp (fieldsOf D).E (D.R.N (s + 1))))
      (x : HomE (fieldsOf D).E (D.R.N s) (D.R.N (s + 1))),
      InRange (Sall (Pr := primesOf D EX) sel ξ u) (cAof sel ξ cst * cBof sel ξ cst u) (cBof sel ξ cst u) N N' x →
      ∀ n : DVar (fieldsOf D).Tau (D.R.N s) (D.R.N (s + 1)) →₀ ℕ,
        (∀ τ, (∑ b, ∑ a, (n (τ, b, a) : ℤ)) = ∑ r, ((wtsOf D EX).nuW u (s + 1) τ).w r) →
        ∃ k : D.what₂.LL, A.σ₀ k = (A.chiF _ _ N N')⁻¹ *
          jetC A.cD (A.thInd (Sall (Pr := primesOf D EX) sel ξ u) N N' (cBof sel ξ cst u) x) n

def ColTie (u : D.what₂.Word) (κ : ((D.fm u).lat 0).V ≃ₗ[D.what₂.LL] MfV (wtsOf D EX) Ch u) : Prop :=
  (∀ x, x ∈ ((D.fm u).lat 0).L ↔ κ x ∈ MfL (wtsOf D EX) Ch u) ∧
    ∀ x, x ∈ (D.fm u).ramSub ↔ κ x ∈ MramV (wtsOf D EX) Ch u

def RowTie (μ : D.what₂.Tup)
    (ι : MtildeV (wtsOf D EX) Ch sel ξ (rPsymF Ch) →ₛₗ[D.what₂.embLL] D.what₂.Amb μ) : Prop :=
  (∀ (n : ℕ) (v : Fin n → MtildeV (wtsOf D EX) Ch sel ξ (rPsymF Ch)), LinearIndependent D.what₂.LL v →
    LinearIndependent ℂ (fun a => ι (v a))) ∧
  Submodule.span ℂ (Set.range ι) = ⊤ ∧
  (∀ x ∈ (D.what₂.Mtilde μ).gen, x ∈ Set.range ι) ∧
  ∀ F, F ∈ MtildeL (wtsOf D EX) Ch sel ξ (rPsymF Ch) ↔ ∃ c : D.what₂.Amb μ → 𝓞 D.what₂.LL,
    ι F = ∑ v ∈ (D.what₂.Mtilde μ).gen, D.what₂.embLL ((c v : 𝓞 D.what₂.LL) : D.what₂.LL) • v

def PerTie (u : D.what₂.Word) (μ : D.what₂.Tup) (hP : (mtildeGSD (wtsOf D EX) Ch sel ξ (rPsymF Ch)).Ok)
    (col : MfV (wtsOf D EX) Ch u →ₗ[D.what₂.LL] (evGSD (wtsOf D EX) Ch sel ξ (rPsymF Ch) u).EqFun)
    (κ : ((D.fm u).lat 0).V ≃ₗ[D.what₂.LL] MfV (wtsOf D EX) Ch u)
    (ι : MtildeV (wtsOf D EX) Ch sel ξ (rPsymF Ch) →ₛₗ[D.what₂.embLL] D.what₂.Amb μ) : Prop :=
  ∀ (φ : (D.div.Nu u).V) (F : MtildeV (wtsOf D EX) Ch sel ξ (rPsymF Ch)),
    D.what₂.perCol u μ (D.jN u φ) (ι F) =
      D.what₂.embLL (PtilE (wtsOf D EX) Ch sel ξ (rPsymF Ch) hP u (col (κ (D.nuIn u φ))) F)

def ChainTie (A : Amb (fieldsOf D)) (u : D.what₂.Word) (μ : D.what₂.Tup) : Prop :=
  ∃ (cst : LocCst (fieldsOf D) (rowSG (primesOf D EX) sel ξ))
    (Lx : ChIdx (fieldsOf D) (primesOf D EX) D.R (QE sel (ξ : Chr (fieldsOf D).F (fieldsOf D).E (fieldsOf D).K)))
    (m2 : ℕ) (b : Lx.β (m2 + 1)) (hY : YbHyp (R := D.R) sel ξ cst Lx u m2 b)
    (hL : Lx.Ok Ch sel ξ cst (globOf D m0) m2)
    (hF : ∀ j, (chF (wtsOf D EX) sel ξ Lx u j).Ok)
    (hK : KerEquivC (wtsOf D EX) Ch sel ξ cst Lx A u m2 b hY (rPsymF Ch))
    (hP : (mtildeGSD (wtsOf D EX) Ch sel ξ (rPsymF Ch)).Ok)
    (κ : ((D.fm u).lat 0).V ≃ₗ[D.what₂.LL] MfV (wtsOf D EX) Ch u)
    (ι : MtildeV (wtsOf D EX) Ch sel ξ (rPsymF Ch) →ₛₗ[D.what₂.embLL] D.what₂.Amb μ),
    cst.sharp = true ∧ FieldTie D EX sel ξ cst A u ∧ ColTie D EX Ch u κ ∧ RowTie D EX Ch sel ξ μ ι ∧
      PerTie D EX Ch sel ξ u μ hP (colMu (wtsOf D EX) Ch sel ξ cst Lx A u m2 b hY (rPsymF Ch) hK hF hL) κ ι

end Ties

def Bound (D : D7) (L : SizeData₂ D) (EX : ErrX D) (C1 : ℝ) (i : Fin 2) (w : LiftErrorLocal.Pl D) (u : D.what₂.Word) (μ : D.what₂.Tup) : Prop :=
  ∀ φ ∈ DV.MramL D u, ∀ F ∈ (D.what₂.Mtilde μ).carrier,
    ∃ y : D.what₂.LL, D.what₂.embLL y = D.what₂.perCol u μ (D.jN u φ) F ∧
      (y = 0 ∨ -(∑ j ∈ LiftErrorLocal.lifts D, vNN EX i u j w) - C1 * LiftErrorLocal.errC D L ≤ LiftErrorLocal.vG D w y)

def ColPeriodAt (D : D7) (Dx : DivX D) (L : SizeData₂ D) (EX : ErrX D)
    (Ch : Chars (fieldsOf D) (primesOf D EX) D.R.m) (m0 : Fin D.R.m → Formalism.L2.Host.HChar D.host.E)
    (sel : HeightOneSpectrum (𝓞 (fieldsOf D).F) → HeightOneSpectrum (𝓞 (fieldsOf D).E))
    (δ : ℂ) (B : Base D ⊤ δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (C1 : ℝ) : Prop :=
  HostTie D → PrimeTie D EX → CharTie D EX Ch m0 → IsSel (fieldsOf D) sel → ThetaTie D δ χ cD →
  ∀ (i : Fin 2) (w : LiftErrorLocal.Pl D), LiftErrorLocal.Over D i w → ∀ u : D.what₂.Word, D.what₂.places.resChar w ≠ (D.mem u).A.T →
    RangeG D EX i u →
    ∀ μ : D.what₂.Tup, D.host.g i ∉ Dx.Qp μ →
    ∀ (S : Set ℕ) (ξ : Tup (fieldsOf D).F (fieldsOf D).E (fieldsOf D).K S), AvoidTie D i u S → TupTie D Dx ξ μ →
      ChainTie D EX Ch m0 sel ξ (ambOf (seamOf D) B χ cD) u μ →
      Bound D L EX C1 i w u μ

example (D : D7) (L : SizeData₂ D) (EX : ErrX D) (C1 C2 : ℝ) (h : LiftErrorLocal.PropositionCLatticeBound D L EX C1 C2) (i : Fin 2) (w : LiftErrorLocal.Pl D)
    (hw : LiftErrorLocal.Over D i w) (u : D.what₂.Word) (hT : D.what₂.places.resChar w ≠ (D.mem u).A.T) (μ : D.what₂.Tup) :
    Bound D L EX C1 i w u μ := h.1 i w hw u hT μ

end GlobalTheory.IndefiniteRowSideFullHecke.ColumnAvoidanceConditions

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.KernelAwayPrimes
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.IntegralityWeylConditions

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta

def IntAt {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (a : ℂ) : Prop :=
  a ∈ Qbar ∧ ‖lamC lam a‖ ≤ 1

def WeylAt (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {N : ℕ} (wt : D.what₂.Tau → DomWeight N)
    (Q : MvPolynomial (FrV D N) ℂ) : Prop :=
  ∃ (n : ℕ) (a : Fin n → ℂ) (f : Fin n → D.what₂.Tau → MvPolynomial (Fin N × Fin N) ℤ),
    (∀ k, IntAt lam (a k)) ∧ (∀ k τ, f k τ ∈ delSq ℤ N (wt τ)) ∧
    Q = ∑ k, a k • Formalism.L2.DIV.ten (fun τ => MvPolynomial.map (Int.castRingHom ℂ) (f k τ))

variable {D : D7}

def lastTrue (Tw : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) (i : ℕ) (τ : D.what₂.Tau) : ℤ :=
  ((Tw.fm u μ).lam i τ).detShift - ((i * (D.R.t + 1) / 2 : ℕ) : ℤ)

def ValInt (Tw : TwForms D) {u : D.what₂.Word} {μ : D.what₂.Tup} (O : LiftObj D (D.chTw u μ)) {p : ℕ} [Fact p.Prime]
    (lam : Qbar →+* ℂ_[p]) (i : ℕ) (v : (D.chTw u μ).Y i → ℂ) : Prop :=
  ∃ Q : MvPolynomial (FrV D (D.R.N i)) ℂ, WeylAt D lam ((Tw.fm u μ).lam i) Q ∧
    ∀ y, v y = evFr D Q (O.frm i y) * ∏ τ, (O.frm i y τ).det ^ lastTrue Tw u μ i τ

def nn (X : ErrX D) (ig : Fin 2) (u : D.what₂.Word) (j : ℕ) : D.what₂.LL :=
  ∏ τ : D.what₂.Tau, tauPib X ig τ ^ ⌊nuAbs D u j τ⌋₊

def loss (X : ErrX D) (ig : Fin 2) (u : D.what₂.Word) (i : ℕ) : D.what₂.LL :=
  nn X ig u (i + 1) * (D.host.g ig : D.what₂.LL) ^ (D.R.f * D.R.N i * D.R.N (i + 1))

def FamTie (D : D7) (ig : Fin 2) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D) : Prop :=
  IsCurveIdeal D cc ∧ Nat.Coprime (Ideal.absNorm cc) (D.host.g ig) ∧ IsDiscriminantTwelfthRootOfIdealLattice D cc δ ∧
    vec22 D (tor0 D cc δ) e ∧ int22 D (tor0 D cc δ) e

def RepStd {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} (O : LiftObj D C) (g i : ℕ) : Prop :=
  letI := D.host.cmStar
  ∀ c : C.cls i, EqAt D g (O.lat i c).1 (O.L0 i).1

def StabTie {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} (O : LiftObj D C) (i : ℕ) : Prop :=
  letI := D.host.cmStar
  ∀ c : C.cls i, ∃ j : C.stab i c →* Matrix.unitaryGroup (Fin (D.R.N i)) D.host.E, Function.Injective j ∧
    ∀ γ, SDLat.smulLat ((j γ : Matrix.unitaryGroup (Fin (D.R.N i)) D.host.E) :
      Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E) (O.lat i c).1 = (O.lat i c).1

def awayPr (Dx : DivX D) (u : D.what₂.Word) (μ : D.what₂.Tup) (ig : Fin 2) : Finset ℕ :=
  insert (D.host.g (1 - ig)) (insert (D.mem u).A.T (Dx.Qp μ))

def IdemPi (X : ErrX D) (ig : Fin 2) (ε : 𝓞 D.host.K) : Prop :=
  (∃ a : 𝓞 D.host.E, ((ε : D.host.K) : D.host.E) - 1 = ((X.piG ig : 𝓞 D.host.E) : D.host.E) ^ 4 * (a : D.host.E)) ∧
  ∃ a : 𝓞 D.host.E, ((ε : D.host.K) : D.host.E) =
    D.host.conj ((X.piG ig : 𝓞 D.host.E) : D.host.E) ^ 4 * (a : D.host.E)

def IsKerG (X : ErrX D) (ig : Fin 2) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D) (S : Finset ℕ) {N N' : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (Θ : VC D N N' → ℂ) : Prop :=
  ∃ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (ε : 𝓞 D.host.K) (n : ℕ) (a : Fin n → ℂ)
    (t : Fin n → VC D N N') (Ψ : Fin n → LocallyConstant (Fin r → ℤ_[D.host.g ig]) ℂ),
    NNBasis D (tor0 D cc δ) δ (D.host.g ig) L L' b ∧ IdemPi X ig ε ∧
    (∀ k, a k ∈ Qbar) ∧
    (∀ k (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), p ∉ S → ‖lamC lam (a k)‖ ≤ 1) ∧
    (∀ k, ∃ m : ℕ, 0 < m ∧ (∀ q : ℕ, q.Prime → q ∣ m → q ∈ S) ∧ m • t k ∈ La D (tor0 D cc δ) L L') ∧
    (∀ k, FactorsMod 1 (Ψ k) ∧ ∀ x, IsIntegral ℤ (Ψ k x)) ∧
    Θ = fun z => ∑ k, a k * U D (tor0 D cc δ) (t k)
      (XiF D (tor0 D cc δ) δ (D.host.g ig) 1 ε b (Ψ k) (e N N' L L')) z

def KerGTie (Dx : DivX D) (X : ErrX D) (ig : Fin 2) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D)
    {u : D.what₂.Word} {μ : D.what₂.Tup} (O : LiftObj D (D.chTw u μ)) (i : ℕ) : Prop :=
  letI := D.host.cmStar
  ∀ c c', IsKerG X ig cc δ e (awayPr Dx u μ ig) (O.lat i c).1 (O.lat (i + 1) c').1 (O.Th i c c')

def LatTie {Dx : DivX D} {Tw : TwForms D} (E : KerEnt D Dx Tw) {u : D.what₂.Word} {μ : D.what₂.Tup}
    (O : LiftObj D (D.chTw u μ)) (w : D.what₂.places.Pl) (i : ℕ) : Prop :=
  ∀ x : ((Tw.fm u μ).lat i).V, x ∈ locW D.what₂.places w ((Tw.fm u μ).lat i).L ↔
    ∀ c, ValInt Tw O (E.lam w) i ((Tw.fm u μ).emb i x c)

def SizeG (Tw : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) (ig : Fin 2) (i : ℕ) : Prop :=
  LiftErrorLocal.Dpi D u (i + 1) < (D.host.g ig : ℝ) - 1 ∧
  2 * D.R.f * D.R.N i + 1 < D.host.g ig ∧
  (∀ τ, ((Tw.fm u μ).lam i τ).spread < (D.host.g ig : ℤ)) ∧
  ∀ τ, ((Tw.fm u μ).lam (i + 1) τ).spread < (D.host.g ig : ℤ)

def ValLoss {Dx : DivX D} {Tw : TwForms D} (E : KerEnt D Dx Tw) (X : ErrX D) {u : D.what₂.Word} {μ : D.what₂.Tup}
    (O : LiftObj D (D.chTw u μ)) (ig : Fin 2) (w : D.what₂.places.Pl) (i : ℕ) : Prop :=
  ∀ φ : (D.chTw u μ).cls i → (D.chTw u μ).Y i → ℂ, (∀ c, ValInt Tw O (E.lam w) i (φ c)) →
    ∀ c', ValInt Tw O (E.lam w) (i + 1) (D.what₂.embLL (loss X ig u i) • (D.chTw u μ).K i φ c')

def FormLoss (Tw : TwForms D) (X : ErrX D) (u : D.what₂.Word) (μ : D.what₂.Tup) (ig : Fin 2)
    (w : D.what₂.places.Pl) (i : ℕ) : Prop :=
  ∀ x ∈ locW D.what₂.places w ((Tw.fm u μ).lat i).L, ∀ y : ((Tw.fm u μ).lat (i + 1)).V,
    (Tw.fm u μ).emb (i + 1) y = (D.chTw u μ).K i ((Tw.fm u μ).emb i x) →
    loss X ig u i • y ∈ locW D.what₂.places w ((Tw.fm u μ).lat (i + 1)).L

def KernelEntryIdealCondition (D : D7) (Dx : DivX D) (Tw : TwForms D) (E : KerEnt D Dx Tw) (X : ErrX D)
    (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D) : Prop :=
  InducedCMType D → HostFieldConditions D → Pinned D →
  ∀ (ig : Fin 2), FamTie D ig cc δ e →
  ∀ (w : D.what₂.places.Pl), LiftErrorLocal.Over D ig w →
  ∀ (u : D.what₂.Word) (μ : D.what₂.Tup), D.host.g ig ≠ (D.mem u).A.T → D.host.g ig ∉ Dx.Qp μ →
  ∀ (O : LiftObj D (D.chTw u μ)), rhoThreeOf D (D.chTw u μ) O.mt →
  ∀ i, i < D.R.m → SizeG Tw u μ ig i →
    liftTie D (tor0 D cc δ) e O i → KerGTie Dx X ig cc δ e O i →
    RepStd O (D.host.g ig) i → RepStd O (D.host.g ig) (i + 1) → StabTie O i →
    ValLoss E X O ig w i ∧ (LatTie E O w i → LatTie E O w (i + 1) → FormLoss Tw X u μ ig w i)

theorem valInt_zero (Tw : TwForms D) {u : D.what₂.Word} {μ : D.what₂.Tup} (O : LiftObj D (D.chTw u μ)) {p : ℕ}
    [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (i : ℕ) : ValInt Tw O lam i 0 :=
  ⟨0, ⟨0, Fin.elim0, Fin.elim0, fun k => k.elim0, fun k => k.elim0, by simp⟩, fun y => by simp [evFr]⟩

theorem formLoss_of_valLoss {Dx : DivX D} {Tw : TwForms D} (E : KerEnt D Dx Tw) (X : ErrX D) {u : D.what₂.Word}
    {μ : D.what₂.Tup} (O : LiftObj D (D.chTw u μ)) (ig : Fin 2) (w : D.what₂.places.Pl) (i : ℕ)
    (h : ValLoss E X O ig w i) (h0 : LatTie E O w i) (h1 : LatTie E O w (i + 1)) : FormLoss Tw X u μ ig w i := by
  intro x hx y hy
  refine (h1 _).2 fun c' => ?_
  have := h _ ((h0 x).1 hx) c'
  rw [LinearMap.map_smulₛₗ, hy]
  exact this

theorem exp_le (D : D7) (i : ℕ) (hi : i < D.R.m) :
    D.R.f * D.R.N i * D.R.N (i + 1) ≤ D.R.f * D.R.N D.R.m * (D.R.N D.R.m + D.R.t) := by
  have h1 : D.R.N i ≤ D.R.N D.R.m := by
    unfold Ranks.N; exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hi.le) _
  have h2 : D.R.N (i + 1) ≤ D.R.N D.R.m + D.R.t := by
    unfold Ranks.N
    exact le_trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hi) _) (Nat.le_add_right _ _)
  exact Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) h2

end GlobalTheory.IndefiniteRowSideFullHecke.IntegralityWeylConditions

end
end

