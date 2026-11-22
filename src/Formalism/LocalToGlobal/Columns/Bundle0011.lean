import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Mathlib
import Formalism.LocalToGlobal.Columns.Bundle0008
import Formalism.PadicSubsetSums.StableGradedCounts.Bundle0004
import Formalism.PadicSubsetSums.StableGradedCounts.IRRPrimeRecipSum
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IrreducibleCharacterSeries.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IrreducibleCharacterSeries.Bundle0002
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IrreducibleCharacterSeries.BlockSum
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GreenLabelSurjective.Bundle0001
import Formalism.LocalToGlobal.Columns.Bundle0010
import Formalism.LocalToGlobal.Divisibility.LiftLatInst
import Formalism.LocalToGlobal.Columns.HeckeSp
import Formalism.LocalToGlobal.Columns.StdLatUnimodular
import Formalism.LocalToGlobal.Columns.Adelic
import Formalism.LocalToGlobal.Columns.ScaledRamifiedLattice
import Formalism.LogVandermondeBounds.Bundle0001
import Formalism.GradedWeylDivisibility.StatementD
import Formalism.HermitianLattices.Bundle0003
import Formalism.FlagUnipotentLattices.MemOfOrthogonalAnisotropic
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.LocalToGlobal.Columns.Bundle0005

-- bundled from Formalism.LocalToGlobal.Columns.ChainLawPhi
section
open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Col

section PhiLaw

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K]

def PhiGSLaw (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ)
    (k₀ rS r t j c' n' c n : ℕ) : Prop :=
  ∀ γ ∈ LocE.JGsym P q k₀ rS r t n c, ∀ κ ∈ LocE.JGsym P q k₀ rS r t n' c', ∀ x : HomE E (n' + c') (n + c),
    LocE.PhiGS q ψ₀ χ k₀ rS r t j c' n' c n (γ.toLinearMap ∘ₗ x ∘ₗ κ.toLinearMap) =
      LocE.lamGBS q ψ₀ χ k₀ r t j n c γ.toLinearMap * (LocE.unitV (χ (j - 1)) ((LinearEquiv.det γ : Eˣ) : E))⁻¹ *
        (LocE.lamGBS q ψ₀ χ k₀ r t (j - 1) n' c' κ.toLinearMap * (LocE.unitV (χ (j - 1)) ((LinearEquiv.det κ : Eˣ) : E))⁻¹) *
          LocE.PhiGS q ψ₀ χ k₀ rS r t j c' n' c n x

structure PhiGSLawHyp (P : HeightOneSpectrum (𝓞 E)) (q k₀ rS r t j c' n' c n : ℕ) : Prop where
  hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal
  hu : ((q : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2
  hj : 1 ≤ j
  hk' : k₀ ≤ n'
  hk : k₀ ≤ n
  hr : k₀ + rS < r
  ht : 0 < t
  hsrc : n' + c' = r + (j - 1) * t
  htgt : n + c = r + j * t

end PhiLaw

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.ChainOne
section
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section One

variable {X : Fields} {Pr : Primes X} {R : Ranks}

def oneIdx (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs) (Q : Finset (HeightOneSpectrum (𝓞 X.E))) (m2 : ℕ) : ChIdx X Pr R Q where
  β j := {_u : Unit // j ≤ m2 + 1}
  h _ _ _ := 1
  levG j _ := Λ j
  levQ j _ := LevQFam.top X.E X.K (R.N j) Q

variable (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs)

open Classical in

structure OneCosetSym (m2 : ℕ) : Prop where
  surj : ∀ i, i < m2 → ∀ hh : rowSG Pr sel mu → AutY X R (i + 1),
    (∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs → hh P ∈ stabL X.E _ (lamYat (Pr := Pr) (i + 1) P.1)) →
    (∀ P, FiniteSumNonzeroLargeDepth Ch sel mu cst i P 1 (hh P)) → ∀ P, SameDC (Pr := Pr) cst.sharp (i + 1) P.1 1 (hh P)
  grpG : ∀ j, j ≤ m2 + 1 → ∀ (w : {w // w ∈ Pr.vGs}) (hbar : GL (Fin (R.N j)) (𝓞 X.E ⧸ w.1.asIdeal)),
    hbar ∈ (Λ j w).H ↔ ∃ g ∈ prCat (Pr := Pr) cst.sharp j w.1 (1 : AutY X R j),
      ∀ x ∈ stdAt X.E (R.N j) w.1, redV w.1 (g x) = hbar.1.mulVec (redV w.1 x)
  chrG : ∀ j, j ≤ m2 + 1 → ∀ (w : {w // w ∈ Pr.vGs}) (hbar : ↥(Λ j w).H) (g : Sp X.E (R.N j) ≃ₗ[X.E] Sp X.E (R.N j)) (r : AutY X R j),
    r ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp j w.1) (1 : AutY X R j) →
    (∀ x, r (Loc.inX X.E (R.N j) (cOf R j) x) = Loc.inX X.E (R.N j) (cOf R j) (g x)) →
    (∀ x ∈ stdAt X.E (R.N j) w.1, redV w.1 (g x) = hbar.1.1.mulVec (redV w.1 x)) →
    (((Λ j w).lam hbar : X.Kˣ) : X.K) = chiInv Ch sel mu cst j ⟨w.1, Finset.mem_union_left _ w.2⟩ (1 : AutY X R j) r

def OneYbSym (m2 : ℕ) : Prop :=
  ∀ (P : rowSG Pr sel mu), P.1 ∈ Pr.vGs → ∀ (x₀ : HomE X.E (R.N m2) (R.N (m2 + 1))) (y' : Sp X.E (R.N (m2 + 1))),
    PsiAt Ch sel mu cst m2 P 1 x₀ y' ≠ 0 →
      ∀ l : Fin (R.N (m2 + 1)), IntAt P.1 ((qOf P.1 : X.E) * y' l) ∧ redP P.1 ((qOf P.1 : X.E) * y' l) = if l.1 = R.k then 1 else 0

def NonVanSym (m2 : ℕ) : Prop :=
  ∀ i, i < m2 → ∀ P : rowSG Pr sel mu, FiniteSumNonzeroLargeDepth Ch sel mu cst i P 1 1

variable {Ch sel mu cst Λ}

theorem oneIdx_clauses {m2 : ℕ} (h : OneCosetSym Ch sel mu cst Λ m2) (hn : NonVanSym Ch sel mu cst m2) :
    (∀ i, i < m2 → ∀ (b : (oneIdx Λ (QE sel (mu : Chr X.F X.E X.K)) m2).β (i + 1)) (P : rowSG Pr sel mu),
      ∃ al : (oneIdx Λ (QE sel (mu : Chr X.F X.E X.K)) m2).β i,
        FiniteSumNonzeroLargeDepth Ch sel mu cst i P ((oneIdx Λ (QE sel (mu : Chr X.F X.E X.K)) m2).h i al P) ((oneIdx Λ (QE sel (mu : Chr X.F X.E X.K)) m2).h (i + 1) b P)) ∧
    (∀ i, i < m2 → ∀ b b' : (oneIdx Λ (QE sel (mu : Chr X.F X.E X.K)) m2).β (i + 1), b = b') ∧
    (∀ i, i < m2 → ∀ hh : rowSG Pr sel mu → AutY X R (i + 1),
      (∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs → hh P ∈ stabL X.E _ (lamYat (Pr := Pr) (i + 1) P.1)) →
      (∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → (∀ x ∈ lamYat (Pr := Pr) (R := R) (i + 1) P.1, (hh P)⁻¹ x ∈ lamYat (Pr := Pr) (R := R) (i + 1) P.1 ∧ ((qOf P.1 : X.E) ^ (i + 1)) • (hh P) x ∈ lamYat (Pr := Pr) (R := R) (i + 1) P.1)) →
      (∀ P, ∃ al : (oneIdx Λ (QE sel (mu : Chr X.F X.E X.K)) m2).β i, FiniteSumNonzeroLargeDepth Ch sel mu cst i P ((oneIdx Λ (QE sel (mu : Chr X.F X.E X.K)) m2).h i al P) (hh P)) →
      ∃ b : (oneIdx Λ (QE sel (mu : Chr X.F X.E X.K)) m2).β (i + 1),
        ∀ P, SameDC (Pr := Pr) cst.sharp (i + 1) P.1 ((oneIdx Λ (QE sel (mu : Chr X.F X.E X.K)) m2).h (i + 1) b P) (hh P)) := by
  refine ⟨fun i hi b P => ⟨(⟨(), by omega⟩ : {_u : Unit // i ≤ m2 + 1}), hn i hi P⟩,
    fun i _ b b' => by cases b; cases b'; rfl,
    fun i hi hh hstab _ hE => ⟨(⟨(), by omega⟩ : {_u : Unit // i + 1 ≤ m2 + 1}), h.surj i hi hh hstab fun P => ?_⟩⟩
  obtain ⟨_, hP⟩ := hE P
  exact hP

end One

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.ExistsUnitOfPowEqOne
section
open Polynomial CategoryTheory NumberField

noncomputable section

namespace Formalism.L2.Col

def XgBrauerSplit : Prop :=
  ∀ (Γ : Type) [Group Γ] [Fintype Γ] (K : Type) [Field K] (σ : K →+* ℂ) (z : K),
    IsPrimitiveRoot z (Fintype.card Γ) →
    ∀ (n : ℕ) (ρ : Representation ℂ Γ (Fin n → ℂ)), ρ.IsIrreducible →
      ∃ (m : ℕ) (τ : Representation K Γ (Fin m → K))
        (τb : Representation (AlgebraicClosure K) Γ (Fin m → AlgebraicClosure K)),
        τb.IsIrreducible ∧
        (∀ t, LinearMap.toMatrix' (τb t) = (LinearMap.toMatrix' (τ t)).map (algebraMap K (AlgebraicClosure K))) ∧
        ∀ t, σ (τ.character t) = ρ.character t

def XgGreenExists : Prop :=
  ∀ (g : ℕ) [Fact g.Prime] (teich : Formalism.CyclotomicNorms.Fbar g →* ℂ) (ζ : ℕ → Formalism.CyclotomicNorms.Fbar g),
    (∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → teich x = teich y → x = y) → Formalism.L2.NT.IsGenSys ζ →
    ∀ d k : ℕ, 0 < d → (Formalism.L2.NT.labCusp ζ d k).natDegree = d →
      ∃ χ : GL (Fin d) (ZMod g) → ℂ, Formalism.L2.NT.IsCuspChar χ ∧ Formalism.L2.NT.GreenAt teich χ k

section Rep

variable {Γ : Type} [Group Γ] [Fintype Γ]

end Rep

section Series

variable {g : ℕ} [Fact g.Prime]

end Series

section Assemble

theorem residueField_equiv_zmod {X : Fields} (w : IsDedekindDomain.HeightOneSpectrum (𝓞 X.E)) (g : ℕ) [Fact g.Prime]
    (hw : Ideal.absNorm w.asIdeal = g) : Nonempty ((𝓞 X.E ⧸ w.asIdeal) ≃+* ZMod g) := by
  have hc : Nat.card (𝓞 X.E ⧸ w.asIdeal) = g := by
    rw [← hw, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have : Finite (𝓞 X.E ⧸ w.asIdeal) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; exact (Fact.out : g.Prime).ne_zero)
  letI : Fintype (𝓞 X.E ⧸ w.asIdeal) := Fintype.ofFinite _
  have hc' : Fintype.card (𝓞 X.E ⧸ w.asIdeal) = g := by rw [← Nat.card_eq_fintype_card, hc]
  have : CharP (𝓞 X.E ⧸ w.asIdeal) g := charP_of_card_eq_prime hc'
  exact ⟨(ZMod.ringEquiv _ hc').symm⟩

def generalLinearEquivOfRingEquiv {R S : Type} [CommRing R] [CommRing S] (r : ℕ) (e : R ≃+* S) : GL (Fin r) R ≃* GL (Fin r) S :=
  Units.mapEquiv (e.mapMatrix (m := Fin r)).toMulEquiv

def XgNonemp : Prop :=
  XgBrauerSplit → XgGreenExists →
  ∀ {X : Fields} (Pr : Primes X) {m : ℕ} (Ch : Chars X Pr m) (r : ℕ)
    [∀ i, Fact (Pr.g i).Prime] (σ : X.K →+* ℂ) (teich : ∀ i : Fin 2, Formalism.CyclotomicNorms.Fbar (Pr.g i) →* ℂ)
    (ζ : ∀ i : Fin 2, ℕ → Formalism.CyclotomicNorms.Fbar (Pr.g i)),
    XgNonempty Pr Ch r σ teich ζ

end Assemble

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.HeckeInertTr
section
noncomputable section

namespace Formalism.L2.Col

open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory Module

section NbFunI

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}
variable (K V : Type) [Field K] [AddCommGroup V] [Module K V]

def nbFunI (P : Ideal (𝓞 E)) (s : List ℕ) : (DecoSet E n ST SG → V) →ₗ[K] (DecoSet E n ST SG → V) where
  toFun ψ d := ∑ d₁ ∈ d.inertNb P s, ψ d₁
  map_add' ψ ψ' := by
    funext d
    simp only [Pi.add_apply, Finset.sum_add_distrib]
  map_smul' c ψ := by
    funext d
    simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]

end NbFunI

section Tr

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}

theorem trF_nbFunI {V : Type} [AddCommGroup V] [Module X.K V] (a : GLG X.E n SG) (P : Ideal (𝓞 X.E)) (s : List ℕ)
    (ψ : DecoSet X.E n ST SG → V) :
    trF X n ST SG V a (nbFunI X.K V P s ψ) = nbFunI X.K V P s (trF X n ST SG V a ψ) := by
  funext d
  show ∑ d₁ ∈ (((1 : UF X.E n), a⁻¹) • d).inertNb P s, ψ d₁ =
    ∑ d₁ ∈ d.inertNb P s, ψ (((1 : UF X.E n), a⁻¹) • d₁)
  exact DecoSet.sum_inertNb_smul P s _ d ψ

variable (C : CoefPk X n (DecoSet X.E n ST SG)) (Λ : LevFam X.E X.K n SG)

theorem heckeFamI_formPts_apply (S0 : Set (HeightOneSpectrum (𝓞 X.E))) (y : LevOffI ST SG S0 × List ℕ)
    (φ : (formGSD C Λ).EqFun) :
    ((heckeFamI (Formalism.L2.DIV.formPts C Λ) S0 y φ : (formGSD C Λ).EqFun) : DecoSet X.E n ST SG → C.V) =
      nbFunI X.K C.V y.1.1.asIdeal y.2 (φ : DecoSet X.E n ST SG → C.V) := by
  funext d
  show ((heckeI (Formalism.L2.DIV.formPts C Λ) y.1.1.asIdeal y.2).op φ : DecoSet X.E n ST SG → C.V) d =
    ∑ d₁ ∈ DecoSet.inertNb y.1.1.asIdeal y.2 d, (φ : DecoSet X.E n ST SG → C.V) d₁
  rw [heckeI_op_apply]
  simp [DecoPts.nbI, Formalism.L2.DIV.formPts]

theorem heckeFamI_comm_trRep {A : Type} [Group A] (ι : A →* GLG X.E n SG) (hι : ∀ a w, (Λ w).NormBy (ι a w))
    (S0 : Set (HeightOneSpectrum (𝓞 X.E))) (y : LevOffI ST SG S0 × List ℕ) (a : A) :
    Commute (trRep C Λ ι hι a) (heckeFamI (Formalism.L2.DIV.formPts C Λ) S0 y) := by
  show trRep C Λ ι hι a * heckeFamI (Formalism.L2.DIV.formPts C Λ) S0 y =
    heckeFamI (Formalism.L2.DIV.formPts C Λ) S0 y * trRep C Λ ι hι a
  apply LinearMap.ext
  intro φ
  apply Subtype.ext
  rw [Module.End.mul_apply, Module.End.mul_apply]
  show trF X n ST SG C.V (ι a)
      ((heckeFamI (Formalism.L2.DIV.formPts C Λ) S0 y φ : (formGSD C Λ).EqFun) : DecoSet X.E n ST SG → C.V) =
    ((heckeFamI (Formalism.L2.DIV.formPts C Λ) S0 y (trRep C Λ ι hι a φ) : (formGSD C Λ).EqFun) :
      DecoSet X.E n ST SG → C.V)
  rw [heckeFamI_formPts_apply, heckeFamI_formPts_apply, trF_nbFunI]
  rfl

end Tr

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.Inputs
section
noncomputable section

namespace Formalism.L2.Col

open Module Module.End Polynomial

section Link

variable {L Pl Pt : Type} [Field L]

def ZSubHasBlocks (n : ℕ) (q : Pl → ℕ) (t : ℕ) (bl : List (Pl → L)) (sys : Pt → Pl × ℕ → L) (Z : Set Pt) : Prop :=
  ∀ x ∈ Z, HasBlocks n q t bl (sys x)

theorem ZSubHasBlocks.mono {n : ℕ} {q : Pl → ℕ} {t : ℕ} {bl : List (Pl → L)} {sys : Pt → Pl × ℕ → L} {Z Z' : Set Pt}
    (h : ZSubHasBlocks n q t bl sys Z) (hZ : Z' ⊆ Z) : ZSubHasBlocks n q t bl sys Z' :=
  fun x hx => h x (hZ hx)

def heckeRenorm (n : ℕ) (q : Pl → ℕ) (a : Pl × ℕ → L) : Pl × ℕ → L :=
  fun y => (q y.1 : L) ^ (y.2 * (n - 1)) * a y

end Link

section Conc

open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))} {S : GSD K}

def ZSubHasBlocksC (c : DecoPts S E n ST SG) (S0 : Set (HeightOneSpectrum (𝓞 E))) (t : ℕ)
    (bl : List (LevOff ST SG S0 → K)) (Z : Set (hAlg K (heckeFam c S0) →ₐ[K] K)) : Prop :=
  ZSubHasBlocks n SplitOff.q t bl (fun ψ => sysOf ψ) Z

end Conc

section Genus

open NumberField Formalism.HermitianLatticesTheory Formalism.BasicNotions

def UnimodGenusLoc (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) : Prop :=
  IsCMUnram E → ∀ N : Submodule (𝓞 E) (Sp E n), Submodule.IsLattice E N → IsUnimodular (hStd E n) N →
    SameGenus (hStd E n) (stdLat E n) N

def UnimodGenusLocAll : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ), UnimodGenusLoc E n

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n]

def UnimodGenus : Prop :=
  ∀ N : Submodule (𝓞 E) (Sp E n), Submodule.IsLattice E N → Formalism.HermitianLatticesTheory.IsUnimodular (hStd E n) N →
    ∃ x ∈ UAd hc n, Formalism.UG.CS.globLat x (stdLat E n) = N

end Genus

section Counting

open NumberField Formalism.HermitianLatticesTheory Formalism.BasicNotions

abbrev MassRatioStd : Prop := Formalism.HermitianLatticesTheory.SiegelMassRatio

def wSeq {n : ℕ} (lam : DomWeight n) : ℕ → ℝ := fun i => if h : i < n then ((lam.w ⟨i, h⟩ : ℤ) : ℝ) - i else 0

def WeylDim {n : ℕ} (lam : DomWeight n) : Prop :=
  (Nat.card (Formalism.GradedWeylDivisibility.ssIdx n n lam.natW) : ℝ) = Formalism.LogVandermondeBounds.StandardLattice.dimVN (wSeq lam) n

end Counting

section Alcove

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV

abbrev NablaMemDeltaLocallyAtLargePrime : Prop := Formalism.BasicNotions.NablaMemDeltaLocallyAtLargePrime

def DeltaEqNablaLatticeLargePrime : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n)
    (w : HeightOneSpectrum (𝓞 K)), (∀ τ, (lam τ).spread < (prW w : ℤ)) →
    ∀ M : ι → Submodule (𝓞 K) (Fin n → K), (∀ τ, Submodule.IsLattice K (M τ)) →
      atW w (delK lam M) = atW w (nabK lam M)

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

def DeltaEqNablaAtWordPrime : Prop :=
  ∀ (u : Pr.Word) (j : ℕ), j ≤ R.m → ∀ w : HeightOneSpectrum (𝓞 X.K), prW w = Pr.T u →
    SwC W Ch u j w = SwNabC W Ch u j w ∧ ∀ P : {P // P ∈ Pr.vT u}, BvWC W Ch u j w P = BvNabWC W Ch u j w P

end Alcove

abbrev MinkowskiBound : Prop := Formalism.HermitianLatticeCounting.S6.MinkowskiBound

section FormalDegree

open MeasureTheory

def HCFormalDegreeCD : Prop :=
  ∀ (C : Formalism.BasicNotions.CDHaar) (n P Q : ℕ) (ε : Fin n → Bool) (e : Fin P ⊕ Fin Q ≃ Fin n),
    (∀ i, ε (e (Sum.inl i)) = true) → (∀ j, ε (e (Sum.inr j)) = false) →
    ∀ μ : Measure (Formalism.REAL.UJ ε),
      (∀ A : Set (Formalism.REAL.UJ ε), MeasurableSet A →
        μ A = C.cd P Q {g | ∃ a ∈ A, Formalism.MainNotions.S.umat a = Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g)}) →
    ∀ lam : Fin n → ℝ, Formalism.QuantumDeterminants.IsHCParam lam →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (w : H),
      Formalism.MainNotions.S.IsDS ε lam σ → w ≠ 0 → Formalism.MainNotions.S.fdegOf μ σ w = Formalism.QuantumDeterminants.fdegHC lam

end FormalDegree

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.TargetChF
section
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Gen

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}

theorem chfok_false (hQ : Q = ∅) (P : Q) : False := by
  obtain ⟨p, hp⟩ := P
  simp [hQ] at hp

def chfokLift (hQ : Q = ∅) (d : DecoSet X.E n ST SG) : DecoF X.E n ST SG Q :=
  ⟨(d, fun _ => 1), fun P _ => (chfok_false hQ P).elim⟩

theorem chfok_ext (hQ : Q = ∅) {p q : DecoF X.E n ST SG Q} (h : p.deco = q.deco) : p = q :=
  Subtype.ext (Prod.ext h (funext fun P => (chfok_false hQ P).elim))

theorem chfok_grp_one (hQ : Q = ∅) (Θ : LevQFam X.E X.K n Q) (c c' : ↥Θ.grp) : c = c' :=
  Subtype.ext (funext fun P => (chfok_false hQ P).elim)

theorem chfok_root (hQ : Q = ∅) (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) (g : FrmG Λ Θ) :
    ∃ m : ℕ, 0 < m ∧ (((Λ.chr g.2.1 * Θ.chr g.2.2 : X.Kˣ)) : X.K) ^ m = 1 := by
  have h1 : g.2.2 = 1 := chfok_grp_one hQ Θ _ _
  obtain ⟨m, hm, hpow⟩ := LevFam.chr_root Λ g.2.1
  refine ⟨m, hm, ?_⟩
  rw [h1, map_one, mul_one]
  exact hpow

theorem frmGSD_ok_of_empty (hX : X.Ok) (hQ : Q = ∅) (C : CoefPk X n (DecoSet X.E n ST SG)) (hC : C.Eqv)
    (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) : (frmGSD (C.pull DecoF.deco) Λ Θ).Ok where
  fin_orb := by
    obtain ⟨s, hs, hrep⟩ := DecoSet.finite_reps (ST := ST) (SG := SG) (n := n) (posStar_of_conj hX.conjE)
    have : Finite s := hs
    refine Finite.of_surjective (fun d : s => (frmGSD (C.pull DecoF.deco) Λ Θ).cls (chfokLift hQ d.1)) ?_
    intro c
    induction c using Quotient.inductionOn' with
    | h p =>
      obtain ⟨d0, hd0, g, hg⟩ := hrep (DecoF.deco p)
      refine ⟨⟨d0, hd0⟩, ?_⟩
      refine ((frmGSD (C.pull DecoF.deco) Λ Θ).cls_eq_iff (chfokLift hQ d0) p).mpr ⟨((g, 1, 1) : FrmG Λ Θ)⁻¹, ?_⟩
      have h1 : p = (((g, 1, 1) : FrmG Λ Θ) : (frmGSD (C.pull DecoF.deco) Λ Θ).G) •
          (chfokLift hQ d0 : (frmGSD (C.pull DecoF.deco) Λ Θ).D) := chfok_ext hQ hg
      rw [h1, inv_smul_smul]
  fin_stab := by
    intro p
    have := DecoSet.finite_stabilizer (posStar_of_conj hX.conjE) (DecoF.deco p : DecoSet X.E n ST SG)
    refine Finite.of_injective
      (fun a : MulAction.stabilizer (frmGSD (C.pull DecoF.deco) Λ Θ).G p =>
        (⟨(a.1.1, (a.1.2.1 : GLG X.E n SG)), congrArg DecoF.deco a.2⟩ :
          MulAction.stabilizer (UF X.E n × GLG X.E n SG) (DecoF.deco p : DecoSet X.E n ST SG))) ?_
    intro a b hab
    have h0 : ((a.1.1, (a.1.2.1 : GLG X.E n SG)) : UF X.E n × GLG X.E n SG) = (b.1.1, (b.1.2.1 : GLG X.E n SG)) :=
      congrArg Subtype.val hab
    exact Subtype.ext (Prod.ext (Prod.mk.inj h0).1
      (Prod.ext (Subtype.ext (Prod.mk.inj h0).2) (chfok_grp_one hQ Θ _ _)))
  nab_smul := by
    intro g d
    obtain ⟨m, hm, hc⟩ := chfok_root hQ Λ Θ g
    exact (hC.nab_smul (g.1, (g.2.1 : GLG X.E n SG)) (DecoF.deco d)).trans (map_root_smul _ _ hm hc).symm
  del_smul := by
    intro g d
    obtain ⟨m, hm, hc⟩ := chfok_root hQ Λ Θ g
    exact (hC.del_smul (g.1, (g.2.1 : GLG X.E n SG)) (DecoF.deco d)).trans (map_root_smul _ _ hm hc).symm
  inv := by
    intro g (x : C.V) (y : C.V)
    obtain ⟨m, hm, hc⟩ := chfok_root hQ Λ Θ g
    show C.pair ((((Λ.chr g.2.1 * Θ.chr g.2.2 : X.Kˣ)) : X.K) • C.rho g.1 x)
      ((((Λ.chr g.2.1 * Θ.chr g.2.2 : X.Kˣ)) : X.K) • C.rho g.1 y) = C.pair x y
    rw [LinearMap.map_smulₛₗ₂, map_smul, hC.inv, smul_smul]
    show (star (((Λ.chr g.2.1 * Θ.chr g.2.2 : X.Kˣ)) : X.K) * _) • _ = _
    rw [star_mul_root hX.conjK hm hc, one_smul]

end Gen

section Chain

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))

theorem chF_ok_of_QE (hX : X.Ok) (hQ : QE sel (mu : Chr X.F X.E X.K) = ∅) (u : Pr.Word) (j : ℕ) : (chF W sel mu L u j).Ok := by
  intro b
  exact frmGSD_ok_of_empty hX hQ _ (colVal_eqv W hX u j (Pr.vT u) Pr.vGs) (L.levG j b) (L.levQ j b)

end Chain

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.TwQThetaOpen
section
open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ}

def lqPrinc (P : HeightOneSpectrum (𝓞 E)) (N : ℕ) (g : Sp E n ≃ₗ[E] Sp E n) : Prop :=
  ∀ i j : Fin n, P.valuation E ((LinearMap.toMatrix' (g : Sp E n →ₗ[E] Sp E n) - 1) i j) ≤
    WithZero.coe (Multiplicative.ofAdd (-(N : ℤ)))

def ThetaOpen {Q : Finset (HeightOneSpectrum (𝓞 E))} (Θ : LevQFam E K n Q) : Prop :=
  ∀ P : Q, ∃ N : ℕ, 0 < N ∧ ∀ g : ↥(GLint E n P.1), lqPrinc P.1 N (g : Sp E n ≃ₗ[E] Sp E n) →
    ∃ h : g ∈ (Θ P).H, (Θ P).lam ⟨g, h⟩ = 1

theorem thetaOpen_top (Q : Finset (HeightOneSpectrum (𝓞 E))) : ThetaOpen (LevQFam.top E K n Q) := by
  intro P
  exact ⟨1, Nat.one_pos, fun g _ => ⟨Subgroup.mem_top _, rfl⟩⟩

end Formalism.L2.Col
end
end

