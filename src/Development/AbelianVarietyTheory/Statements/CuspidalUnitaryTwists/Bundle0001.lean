import Development.AbelianVarietyTheory.Definitions.Foundations.TupleConstantsNeZero
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.OneSquareLeaf.LeafOneSquareFree
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0013
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree

-- bundled from Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.OneSquareClosed
section
open NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw conjPl)
open Formalism.PairingDivisionLocalBalance (Pl wt)
open Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts

noncomputable section

namespace GlobalTheory.Square

def RatioIn : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (σ₀ : K →+* ℂ) (S : Sq K) (hd y : ℕ), S.OK hd y →
  ∀ (w : Pl K) (cw : ℂ) (zA zA' : K) (zT zTd : ℤ → K) (gT : ℤ → ℤ) (n0 : ℤ → ℝ) (er dl : ℝ) (T : Type) (S0 : Finset T)
    (cc qq : T → ℕ), (∀ v ∈ S0, 0 < qq v) → S.Twisted σ₀ w cw zA zA' zT zTd gT n0 er dl S0 cc qq →
    ∃ r : K, r ≠ 0 ∧ σ₀ r * S.base.c = cw

def OneSquareClosed : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (σ₀ : K →+* ℂ) (m : ℕ) (T : Type)
    (r0 : Fin m × Fin m → K) (rw : Pl K → Fin m × Fin m → K) (Se Sd : Finset ℕ) (dd hd yy : Fin m × Fin m → ℕ)
    (N : ℕ) (S0 : Finset T) (cc qq ee : T → ℕ) (zA zA' : Fin m × Fin m → K) (zT : Fin m × Fin m → ℤ → K)
    (zTd : Fin m × Fin m → Bool → ℤ → K) (gT : Fin m × Fin m → ℤ → Pl K → ℤ) (ch : Pl K → Bool)
    (N0 : Fin m × Fin m → ℤ → ℕ → ℝ) (dl : Pl K → ℝ)
    (S : Fin m × Fin m → Sq K) (cw : Pl K → Fin m × Fin m → ℂ),
    (∀ l ∈ Se, l.Prime) → (∀ ij, dd ij = 2 * hd ij) → (∀ ij, dd ij ≤ 2 * N) → (∀ ij, yy ij + 1 ≤ m) →
    (∀ q ∈ S0, cc q ≤ ee q) → (∀ q ∈ S0, 0 < qq q) → (∀ w, 0 ≤ dl w) →
    (∀ ij (s : ℤ), 1 ≤ s → s ≤ hd ij → ∀ l ∈ Sd, 0 ≤ N0 ij s l) →
    (∀ ij, (S ij).OK (hd ij) (yy ij)) →
    (∀ ij, σ₀ (r0 ij) * (S ij).base.c = (S ij).base.c) →
    (∀ w ij, σ₀ (rw w ij) * (S ij).base.c = cw w ij) →
    (∀ w ij, cw w ij = (S ij).base.c ∨
      (S ij).Twisted σ₀ w (cw w ij) (zA ij) (zA' ij) (zT ij) (zTd ij (ch w)) (fun s => gT ij s w)
        (fun s => wt Sd (N0 ij s) w) (wt Se (fun l => 1 / (l : ℝ) ^ 2) w) (dl w) S0 cc qq) →
    SquareCoefficientsCondition r0 rw Se Sd dd hd yy N S0 cc qq ee zA zA' zT zTd gT ch N0 dl

end GlobalTheory.Square
end
end

-- bundled from Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.SlopeE
section
open NumberField
open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.TestLat

def SlopeK : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (v₀ : InfinitePlace K), Formalism.DivisionValues.IsConjAt v₀ →
  ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (R : ℝ), 1 ≤ R → SpreadLe lam R →
  ∀ (G : ι → Matrix (Fin n) (Fin n) K), (∀ τ, IsDefGram (G τ)) →
  ∀ (C : Type) [Nonempty C] (M : C → ι → Submodule (𝓞 K) (Fin n → K)), (∀ c τ, IsSelfDualK (G τ) (M c τ)) →
  ∀ (N : ℕ) (e : Fin N ≃ C × VVIdx lam) (X : InfinitePlace K → Matrix (Fin N) (Fin N) ℂ),
    (IsMetric (sumGram lam e G) X →
      TestLatticeCondition N X (sumLat lam e fun c => nabK lam (M c)) (bound (Fintype.card ι) n R) ∧
      TestLatticeCondition N X (sumLat lam e fun c => delK lam (M c)) (bound (Fintype.card ι) n R)) ∧
    (IsMetric ((sumGram lam e G)⁻¹)ᵀ X →
      TestLatticeCondition N X (dualFr (sumLat lam e fun c => delK lam (M c))) (bound (Fintype.card ι) n R))

def SlopeE : Prop :=
  ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    (v₀ : InfinitePlace K), Formalism.DivisionValues.IsConjAt v₀ →
  ∀ (cE : E →+* E), (∀ (φ : E →+* ℂ) (x : E), φ (cE x) = starRingEnd ℂ (φ x)) →
  ∀ (ι : Type) [Fintype ι] (emb : ι → E →+* K), (∀ τ x, star (emb τ x) = emb τ (cE x)) →
  ∀ (n : ℕ) (lam : ι → DomWeight n) (R : ℝ), 1 ≤ R → SpreadLe lam R →
  ∀ (J : Matrix (Fin n) (Fin n) E), (∀ φ : E →+* ℂ, (J.map φ).PosDef) →
  ∀ (C : Type) [Nonempty C] (L : C → Submodule (𝓞 E) (Fin n → E)), (∀ c, IsSelfDualE cE J (L c)) →
  ∀ (N : ℕ) (e : Fin N ≃ C × VVIdx lam) (X : InfinitePlace K → Matrix (Fin N) (Fin N) ℂ),
    (IsMetric ((sumGram lam e (gramK emb J))⁻¹)ᵀ X →
      TestLatticeCondition N X (dualFr (sumLat lam e fun c => delAt emb lam (L c))) (bound (Fintype.card ι) n R)) ∧
    (IsMetric (sumGram lam e (gramK emb J)) X →
      TestLatticeCondition N X (sumLat lam e fun c => nabAt emb lam (L c)) (bound (Fintype.card ι) n R)) ∧
    (IsMetric ((sumGram lam e (gramKd emb J))⁻¹)ᵀ X →
      TestLatticeCondition N X (dualFr (sumLat lam e fun c => delAtr emb lam (L c))) (bound (Fintype.card ι) n R)) ∧
    (IsMetric (sumGram lam e (gramKd emb J)) X →
      TestLatticeCondition N X (sumLat lam e fun c => nabAtr emb lam (L c)) (bound (Fintype.card ι) n R))

end GlobalTheory.TestLat
end
end

