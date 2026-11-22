import Mathlib
import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions
import Formalism.LocalToGlobal.Columns.StdLatUnimodular
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsFinTyp
import Formalism.LocalToGlobal.GaloisLevelStructure.Bundle0001

-- bundled from Formalism.LocalToGlobal.Columns.CoefCol
section
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section GLmat

variable (E : Type) [Field E] (n : ℕ)

def toGLm : (Sp E n ≃ₗ[E] Sp E n) ≃* GL (Fin n) E :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv E (Sp E n)).symm.trans
    Matrix.GeneralLinearGroup.toLin.symm

def ufGL [StarRing E] : UF E n →* GL (Fin n) E := (toGLm E n).toMonoidHom.comp (UF E n).subtype

end GLmat

structure CoefPk (X : Fields) (n : ℕ) (D : Type) where

  lam : X.Tau → DomWeight n

  rho : UF X.E n →* Module.End X.K (VV X.K lam)

  pair : VV X.K lam →ₗ⋆[X.K] VV X.K lam →ₗ[X.K] X.K

  Nab : D → Submodule (𝓞 X.K) (VV X.K lam)

  Del : D → Submodule (𝓞 X.K) (VV X.K lam)

namespace CoefPk

variable {X : Fields} {n : ℕ} {D : Type} (C : CoefPk X n D)

abbrev V : Type := VV X.K C.lam

def bV : Basis (VVIdx C.lam) X.K C.V := bVV X.K C.lam

def pull {D' : Type} (e : D' → D) : CoefPk X n D' where
  lam := C.lam
  rho := C.rho
  pair := C.pair
  Nab d' := C.Nab (e d')
  Del d' := C.Del (e d')

end CoefPk

section Pk

variable (X : Fields) {n : ℕ}

def roundPk (lam : X.Tau → DomWeight n) {D : Type} (L : D → Submodule (𝓞 X.E) (Sp X.E n)) : CoefPk X n D where
  lam := lam
  rho := (rhoVr X.emb lam).comp (ufGL X.E n)
  pair := pairVr X.emb lam 1
  Nab d := nabAtr X.emb lam (L d)
  Del d := delAtr X.emb lam (L d)

def squarePk (lam : X.Tau → DomWeight n) {D : Type} (L : D → Submodule (𝓞 X.E) (Sp X.E n)) : CoefPk X n D where
  lam := lam
  rho := (rhoV X.emb lam).comp (ufGL X.E n)
  pair := pairV X.emb lam 1
  Nab d := nabAt X.emb lam (L d)
  Del d := delAt X.emb lam (L d)

end Pk

section DecoKer

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

def Deco.LshKer (d : Deco E n ST SG) (P : ST) : Submodule (𝓞 E) (Sp E n) :=
  Submodule.span (𝓞 E) {x | x ∈ d.Lsh ∧ d.f P x = 0}

end DecoKer

section Vals

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)

def colVal (u : Pr.Word) (j : ℕ) (ST SG : Finset (HeightOneSpectrum (𝓞 X.E))) :
    CoefPk X (R.N j) (DecoSet X.E (R.N j) ST SG) :=
  roundPk X (W.lamTrue u j) fun d => d.1.Lsh

def colNabL (u : Pr.Word) (j : ℕ) {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}
    (d : DecoSet X.E (R.N j) ST SG) : Submodule (𝓞 X.K) (VV X.K (W.lamTrue u j)) :=
  nabAtr X.emb (W.lamTrue u j) d.1.L

def rowVal (SG : Finset (HeightOneSpectrum (𝓞 X.E))) :
    CoefPk X (R.N R.m - 1) (DecoSet X.E (R.N R.m - 1) ∅ SG) :=
  squarePk X W.sgTrue fun d => d.1.N

def mtVal (j : ℕ) (SG : Finset (HeightOneSpectrum (𝓞 X.E))) :
    CoefPk X R.nV (DecoSet X.E R.nV ∅ SG) :=
  roundPk X (W.lamV j) fun d => d.1.N

def BvLat (u : Pr.Word) (j : ℕ) {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}
    (P : ST) (d : DecoSet X.E (R.N j) ST SG) : Submodule (𝓞 X.K) (VV X.K (W.lamTrue u j)) :=
  delAtr X.emb (W.lamTrue u j) (d.1.LshKer P)

def BvLatF (u : Pr.Word) (j : ℕ) {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}
    (τ₀ : X.Tau) (P : ST) (d : DecoSet X.E (R.N j) ST SG) : Submodule (𝓞 X.K) (VV X.K (W.lamTrue u j)) :=
  delK (W.lamTrue u j) fun τ => dualFr (tauLat X.emb τ (if τ = τ₀ then d.1.LshKer P else d.1.Lsh))

end Vals

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.MtRowRep
section
noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.BasicNotions

namespace Formalism.L2.Col

section Gen

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

def finTypSetoid (Occ : Set (NG.FinTyp L n)) : Setoid Occ where
  r π π' := π.1.Iso π'.1
  iseqv := ⟨fun π => NG.IsoRep.refl _, fun {π _} h => NG.IsoRep.symm π.1.stable h, fun h h' => NG.IsoRep.trans h h'⟩

abbrev FinTypCls (Occ : Set (NG.FinTyp L n)) : Type := Quotient (finTypSetoid Occ)

def finTypRep (Occ : Set (NG.FinTyp L n)) (c : FinTypCls Occ) : NG.FinTyp L n := (Quotient.out c).1

theorem finTypRep_mem (Occ : Set (NG.FinTyp L n)) (c : FinTypCls Occ) : finTypRep Occ c ∈ Occ := (Quotient.out c).2

theorem finTypRep_inj {Occ : Set (NG.FinTyp L n)} {c c' : FinTypCls Occ}
    (h : (finTypRep Occ c).Iso (finTypRep Occ c')) : c = c' := by
  rw [← Quotient.out_eq c, ← Quotient.out_eq c']
  exact Quotient.sound h

theorem finTypRep_mk_iso {Occ : Set (NG.FinTyp L n)} (π : Occ) :
    (finTypRep Occ (Quotient.mk (finTypSetoid Occ) π)).Iso π.1 :=
  Quotient.mk_out (s := finTypSetoid Occ) π

def constSp (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) : Submodule ℂ (GAf L n → ℂ) :=
  Submodule.span ℂ {fun _ => (1 : ℂ)}

theorem mem_constSp {f : GAf L n → ℂ} : f ∈ constSp L n ↔ ∃ a : ℂ, f = fun _ => a := by
  rw [constSp, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, by funext x; simp⟩
  · rintro ⟨a, rfl⟩
    exact ⟨a, by funext x; simp⟩

def finTypConst (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) : NG.FinTyp L n where
  S := constSp L n
  stable h f hf := by
    obtain ⟨a, rfl⟩ := mem_constSp.mp hf
    exact mem_constSp.mpr ⟨a, rfl⟩
  smooth f hf := by
    obtain ⟨a, rfl⟩ := mem_constSp.mp hf
    exact ⟨1, one_pos, fun _ _ => rfl⟩
  ne := by
    intro h
    have h1 : (fun _ => (1 : ℂ)) ∈ constSp L n := Submodule.subset_span rfl
    rw [h, Submodule.mem_bot] at h1
    have := congrFun h1 1
    simp at this
  irr S' hle _ := by
    by_cases hb : S' = ⊥
    · exact Or.inl hb
    · right
      obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
      obtain ⟨a, rfl⟩ := mem_constSp.mp (hle hf)
      have ha : a ≠ 0 := by
        rintro rfl
        exact hf0 rfl
      refine le_antisymm hle ?_
      rw [constSp, Submodule.span_le, Set.singleton_subset_iff]
      have e : (fun _ => (1 : ℂ)) = a⁻¹ • (fun _ : GAf L n => a) := by
        funext x
        simp [ha]
      rw [SetLike.mem_coe, e]
      exact S'.smul_mem _ hf

end Gen

end Formalism.L2.Col
end
end

