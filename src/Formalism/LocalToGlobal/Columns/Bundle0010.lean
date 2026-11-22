import Mathlib
import Formalism.LocalToGlobal.Columns.RhoEqOfSmulEq
import Formalism.LocalToGlobal.Columns.GSetLemmas
import Formalism.LocalToGlobal.Columns.ColForms
import Formalism.LocalToGlobal.Columns.Bundle0005
import Formalism.LocalToGlobal.Columns.ScaledRamifiedLattice
import Formalism.LocalToGlobal.Columns.RowForms
import Formalism.LocalToGlobal.Columns.RowFormsLemmas
import Formalism.LocalToGlobal.Divisibility.Frames
import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
import Formalism.LocalToGlobal.GlobalTheory.HLatOps
import Formalism.LocalToGlobal.Columns.UnipotentRightActionFunctionsW
import Formalism.LocalToGlobal.Columns.HeckeSpCount
import Formalism.LocalToGlobal.Columns.HeckeSp
import Formalism.LocalToGlobal.Columns.Bundle0001

-- bundled from Formalism.LocalToGlobal.Columns.ToHLat
section
open NumberField IsDedekindDomain Module
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.DivisionValues Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps

namespace GSD

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : GSD K)

def pairAt (v : InfinitePlace K) (x y : S.V) : ℂ :=
  ∑ i, ∑ j, starRingEnd ℂ (v.embedding (S.bV.repr x i)) * v.embedding (S.gramV i j) * v.embedding (S.bV.repr y j)

def ipAt (h : S.Ok) (v : InfinitePlace K) (φ ψ : S.D → S.V) : ℂ :=
  letI : Fintype S.Cl := h.fintypeCl
  ∑ c : S.Cl, (((S.toCSD h).wt c : ℕ) : ℂ)⁻¹ * S.pairAt v (φ (S.outSec.rep c)) (ψ (S.outSec.rep c))

abbrev hDim (h : S.Ok) : ℕ := (S.toCSD h).dim

def hB (h : S.Ok) : Basis (Fin (S.hDim h)) K S.EqFun := (S.toCSD h).basis.map (S.res h).symm

abbrev hGram (h : S.Ok) : Matrix (Fin (S.hDim h)) (Fin (S.hDim h)) K := (S.toCSD h).H

def PosH (h : S.Ok) : Prop := ∀ v : InfinitePlace K, ((S.hGram h).map v.embedding).PosDef

@[reducible] def toH (h : S.Ok) (L : Submodule (𝓞 K) S.EqFun) : HLat K where
  V := S.EqFun
  ι := Fin (S.hDim h)
  b := S.hB h
  X := stdFrame (S.hGram h)
  L := L

abbrev hCoord (h : S.Ok) : S.EqFun ≃ₗ[K] (Fin (S.hDim h) → K) := S.coordOf h S.outSec

def toHc (h : S.Ok) (L : Submodule (𝓞 K) S.EqFun) : HLat K :=
  toHLat (stdFrame (S.hGram h)) (L.map ((S.hCoord h).toLinearMap.restrictScalars (𝓞 K)))

def delHc (h : S.Ok) : HLat K := toHLat (stdFrame (S.hGram h)) (S.toCSD h).delLat

def nabHc (h : S.Ok) : HLat K := toHLat (stdFrame (S.hGram h)) (S.toCSD h).nabLat

def subZ (h : S.Ok) (U : Submodule K S.EqFun) : Submodule K (Fin (S.hDim h) → K) :=
  U.map (S.hCoord h).toLinearMap

def subEq (h : S.Ok) (U : Submodule K S.EqFun) : U ≃ₗ[K] S.subZ h U := (S.hCoord h).submoduleMap U

abbrev subD (h : S.Ok) (U : Submodule K S.EqFun) : ℕ := subDim (S.subZ h U)

def subB (h : S.Ok) (U : Submodule K S.EqFun) : Basis (Fin (S.subD h U)) K U :=
  (subBasis (S.subZ h U)).map (S.subEq h U).symm

def subMat (h : S.Ok) (U : Submodule K S.EqFun) : Matrix (Fin (S.hDim h)) (Fin (S.subD h U)) K :=
  subE (S.subZ h U)

@[reducible] def subH (h : S.Ok) (U : Submodule K S.EqFun) (L : Submodule (𝓞 K) U) : HLat K where
  V := U
  ι := Fin (S.subD h U)
  b := S.subB h U
  X := restrFrame (S.subMat h U) (S.hGram h)
  L := L

def subIncl (h : S.Ok) (U : Submodule K S.EqFun) (L : Submodule (𝓞 K) U) (L' : Submodule (𝓞 K) S.EqFun) :
    (S.subH h U L).V →ₗ[K] (S.toH h L').V := U.subtype

def isoMat (h : S.Ok) (U : Submodule K S.EqFun) (v : InfinitePlace K) :
    Matrix (Fin (S.hDim h)) (Fin (S.subD h U)) ℂ :=
  (stdFrame (S.hGram h) v)⁻¹ * (S.subMat h U).map v.embedding * restrFrame (S.subMat h U) (S.hGram h) v

end GSD

section Cols

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (hX : X.Ok)

@[reducible] def latH (u : Pr.Word) (j : ℕ) : HLat X.K :=
  (colGSD W Ch u j).toH (colOk W Ch hX u j) (ColL W Ch u j)

@[reducible] def latNabH (u : Pr.Word) (j : ℕ) : HLat X.K :=
  (colGSD W Ch u j).toH (colOk W Ch hX u j) (ColLnab W Ch u j)

@[reducible] def Mu0H (u : Pr.Word) : HLat X.K :=
  (colGSD W Ch u 0).toH (colOk W Ch hX u 0) (MfL W Ch u)

@[reducible] def MramH (u : Pr.Word) : HLat X.K :=
  (colGSD W Ch u 0).subH (colOk W Ch hX u 0) (MramV W Ch u) (MramL W Ch u)

def ramInclH (u : Pr.Word) : (MramH W Ch hX u).V →ₗ[X.K] (Mu0H W Ch hX u).V := ramIncl W Ch u

def VrC (u : Pr.Word) (v : InfinitePlace X.K) : Matrix (Mu0H W Ch hX u).ι (MramH W Ch hX u).ι ℂ :=
  (colGSD W Ch u 0).isoMat (colOk W Ch hX u 0) (MramV W Ch u) v

@[reducible] def NlamH (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) : HLat X.K :=
  withL (MramH W Ch hX u) (NlamG W Ch u w)

end Cols

section Rows

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (hX : X.Ok)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

@[reducible] def MtildeH (P : LevFam X.E X.K R.r Pr.vGs) : HLat X.K :=
  (mtildeGSD W Ch sel mu P).toH (mtildeOk W Ch sel mu hX P) (MtildeL W Ch sel mu P)

@[reducible] def MtH (P : LevFam X.E X.K R.r Pr.vGs) (j : ℕ) : HLat X.K :=
  (mtGSD W Ch sel mu P j).toH (mtOk W Ch sel mu hX P j) (MtL W Ch sel mu P j)

end Rows

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.WmLemmas
section
open NumberField IsDedekindDomain Module Polynomial

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Nb

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))} (V : Type) [AddCommGroup V] [Module X.K V]

theorem trF_nbFun (a : GLG X.E n SG) (P : Ideal (𝓞 X.E)) (i : ℕ) (ψ : DecoSet X.E n ST SG → V) :
    trF X n ST SG V a (nbFun X.K V P i ψ) = nbFun X.K V P i (trF X n ST SG V a ψ) := by
  funext d
  rw [trF_apply]
  show ∑ d₁ ∈ ((((1 : UF X.E n), a⁻¹) : UF X.E n × GLG X.E n SG) • d).heckeNb P i, ψ d₁ =
    ∑ d₁ ∈ d.heckeNb P i, ψ ((((1 : UF X.E n), a⁻¹) : UF X.E n × GLG X.E n SG) • d₁)
  set g : UF X.E n × GLG X.E n SG := ((1 : UF X.E n), a⁻¹)
  refine Finset.sum_nbij' (fun e => g⁻¹ • e) (fun e => g • e) ?_ ?_ ?_ ?_ ?_
  · intro e he
    have : g • (g⁻¹ • e) ∈ (g • d).heckeNb P i := by rwa [smul_inv_smul]
    exact (DecoSet.smul_mem_heckeNb_iff g).1 this
  · intro e he
    exact (DecoSet.smul_mem_heckeNb_iff g).2 he
  · intro e _
    exact smul_inv_smul g e
  · intro e _
    exact inv_smul_smul g e
  · intro e _
    rw [smul_inv_smul]

end Nb

section Poly

variable {L : Type} [Field L]

end Poly

section HV

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

end HV

section FromRel

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

end FromRel

section Inh

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {a b : ℕ} {SG : Finset (HeightOneSpectrum (𝓞 E))}
  {V V' : Type} [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']

def wmTh0 : WmTh E K a b SG K K := fun _ _ _ =>
  { toFun := fun Φ => Φ 0 • LinearMap.id
    map_add' := fun Φ Ψ => by simp [add_smul]
    map_smul' := fun c Φ => by simp [smul_smul] }

end Inh

section Fub

variable {K : Type} [Field K] [NumberField K] [StarRing K]

end Fub

section Rev

open Pointwise

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

def DecoSet.revSet (P : Ideal (𝓞 E)) (i : ℕ) (d₁ : DecoSet E n ST SG) : Set (DecoSet E n ST SG) :=
  {d | d₁ ∈ d.heckeSet P i}

open Classical in

def DecoSet.revNb (P : Ideal (𝓞 E)) (i : ℕ) (d₁ : DecoSet E n ST SG) : Finset (DecoSet E n ST SG) :=
  if h : (d₁.revSet P i).Finite then h.toFinset else ∅

end Rev

section PhiLem

open Pointwise

variable {E : Type} [Field E] [NumberField E] [StarRing E] {SG : Finset (HeightOneSpectrum (𝓞 E))}

variable {K : Type} [Field K] {a b : ℕ}

open Classical in

theorem WmSchw.insert {S : Finset (HeightOneSpectrum (𝓞 E))} {Φ : (Sp E a →ₗ[E] Sp E b) → K} (hΦ : WmSchw S Φ)
    (P : HeightOneSpectrum (𝓞 E)) (hP : P ∉ S) {N' : Submodule (𝓞 E) (Sp E a)} {N : Submodule (𝓞 E) (Sp E b)}
    (hN' : Submodule.IsLattice E N') (hN : Submodule.IsLattice E N) :
    WmSchw (insert P S) (fun x => open Classical in if wmIntAt P N' N x then Φ x else 0) := by
  classical
  obtain ⟨A', B', A, B, hl, hper, hsupp⟩ := hΦ
  refine ⟨fun Q => if Q = P then N' else A' Q, fun Q => if Q = P then N' else B' Q,
    fun Q => if Q = P then N else A Q, fun Q => if Q = P then N else B Q, ?_, ?_, ?_⟩
  · intro Q hQ
    by_cases e : Q = P
    · simp only [if_pos e]
      exact ⟨hN', hN, hN', hN⟩
    · simp only [if_neg e]
      exact hl Q ((Finset.mem_insert.1 hQ).resolve_left e)
  · intro x y hy
    have hyP : wmIntAt P N' N y := by simpa using hy P (Finset.mem_insert_self P S)
    have hyS : ∀ Q ∈ S, wmIntAt Q (A' Q) (A Q) y := by
      intro Q hQ
      have hne : Q ≠ P := fun e => hP (e ▸ hQ)
      simpa [hne] using hy Q (Finset.mem_insert_of_mem hQ)
    have hiff : wmIntAt P N' N (x + y) ↔ wmIntAt P N' N x := by
      constructor
      · intro h z hz
        have := Submodule.sub_mem _ (h z hz) (hyP z hz)
        simpa using this
      · intro h z hz
        rw [LinearMap.add_apply]
        exact Submodule.add_mem _ (h z hz) (hyP z hz)
    simp only [hiff, hper x y hyS]
  · intro x hx Q hQ
    by_cases hint : wmIntAt P N' N x
    · have hx' : Φ x ≠ 0 := by simpa [hint] using hx
      by_cases e : Q = P
      · simp only [if_pos e]
        exact e ▸ hint
      · simp only [if_neg e]
        exact hsupp x hx' Q ((Finset.mem_insert.1 hQ).resolve_left e)
    · exact absurd (by simp [hint]) hx

end PhiLem

section Gauss

variable {L : Type} [Field L]

end Gauss

section Count

variable (E : Type) [Field E] [NumberField E] [StarRing E]

open Classical in

def WmCount : Prop :=
  ∀ {a b : ℕ} {SG : Finset (HeightOneSpectrum (𝓞 E))} (P : HeightOneSpectrum (𝓞 E)), conjPrime₂ P ≠ P → P ∉ SG → conjPrime₂ P ∉ SG →
    ∀ (d' : DecoSet E a ∅ SG) (d₁ : DecoSet E b ∅ SG) (x : Sp E a →ₗ[E] Sp E b),
      ∃ ρ, ρ ≤ a ∧ ρ ≤ b ∧ ∀ i j,
        ((d₁.revNb P.asIdeal i).filter fun d => wmIntAt P d'.1.N d.1.N x).card =
          (if wmIntAt P d'.1.N d₁.1.N x then gaussBin (Nat.card (𝓞 E ⧸ P.asIdeal)) (b - ρ) i else 0) ∧
        ((d'.heckeNb P.asIdeal j).filter fun d'₁ => wmIntAt P d'₁.1.N d₁.1.N x).card =
          (if wmIntAt P d'.1.N d₁.1.N x then gaussBin (Nat.card (𝓞 E ⧸ P.asIdeal)) (a - ρ) j else 0)

end Count

section ClassRel

open Classical

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {a b : ℕ} {SG : Finset (HeightOneSpectrum (𝓞 E))}
  {V V' : Type} [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']

end ClassRel

section RelOf

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

def WmKerInv (th : ThM W Ch sel mu (rKg X Pr R)) : Prop :=
  ∀ (g : (mtKGSD W Ch sel mu R.m).G) (d : (mtKGSD W Ch sel mu R.m).D) (d' : (wmKGSD W sel mu).D) (x : (mtKGSD W Ch sel mu R.m).V),
    wmKer W Ch sel mu (rKg X Pr R) th (g • d) d' ((mtKGSD W Ch sel mu R.m).ρ g x) =
      wmKer W Ch sel mu (rKg X Pr R) th d d' x

end RelOf

section Main

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

end Main

end Formalism.L2.Col
end
end

