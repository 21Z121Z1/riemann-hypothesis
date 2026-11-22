import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Formalism.DoubleCosetMeasures.StatementV
import Formalism.RealPlaceAnalysis.Bundle0003
import Formalism.HermitianCurvature.StatementW
import Formalism.FormalDegreeBessel.Bundle0001
import Formalism.PadicSubsetSums.CentralIdempotents.EigenbasisOfDistinctRoots
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GGMirabolicBase

-- bundled from Formalism.PeriodIntegrals.LocLatEq
section
noncomputable section

open ValuativeRel IsDedekindDomain NumberField Formalism.MainNotions.S.Loc

namespace PI.LocLatEq

def bc {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)} (A : LocAt F E sig p) {n : ℕ} (x : Fin n → E) :
    Fin n → A.Ep :=
  fun i => A.ιE (x i)

def latL {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)} (A : LocAt F E sig p) {n : ℕ}
    (Λ : Submodule (𝓞 E) (Fin n → E)) : Submodule A.O (Fin n → A.Ep) :=
  Submodule.span A.O (bc A '' (Λ : Set (Fin n → E)))

def Stmt : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    Module.finrank F E = 2 → ∀ (sig : E →ₐ[F] E) (p : HeightOneSpectrum (𝓞 F)) (A : LocAt F E sig p) (n : ℕ)
    (Λ₁ Λ₂ : Submodule (𝓞 E) (Fin n → E)), Λ₁.FG → Λ₂.FG →
    (latL A Λ₁ = latL A Λ₂ ↔
      ∀ P : HeightOneSpectrum (𝓞 E), P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) = p.asIdeal →
        ∀ x : Fin n → E, (∃ s : 𝓞 E, s ∉ P.asIdeal ∧ s • x ∈ Λ₁) ↔ (∃ s : 𝓞 E, s ∉ P.asIdeal ∧ s • x ∈ Λ₂))

end PI.LocLatEq
end
end

-- bundled from Formalism.PeriodIntegrals.LocLatSat
section
noncomputable section

open ValuativeRel IsDedekindDomain NumberField Formalism.MainNotions.S.Loc

namespace PI.LocLatSat

def bc {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)} (A : LocAt F E sig p) {n : ℕ} (x : Fin n → E) :
    Fin n → A.Ep :=
  fun i => A.ιE (x i)

def latL {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)} (A : LocAt F E sig p) {n : ℕ}
    (Λ : Submodule (𝓞 E) (Fin n → E)) : Submodule A.O (Fin n → A.Ep) :=
  Submodule.span A.O (bc A '' (Λ : Set (Fin n → E)))

def Stmt : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (sig : E →ₐ[F] E) (p : HeightOneSpectrum (𝓞 F)) (A : LocAt F E sig p) (n : ℕ)
    (Λ : Submodule (𝓞 E) (Fin n → E)) (W : Submodule E (Fin n → E)), Λ.FG →
    (latL A (Λ ⊓ W.restrictScalars (𝓞 E)) : Set (Fin n → A.Ep)) =
      (latL A Λ : Set (Fin n → A.Ep)) ∩ Submodule.span A.Ep (bc A '' (W : Set (Fin n → E)))

end PI.LocLatSat
end
end

-- bundled from Formalism.PeriodIntegrals.LocProdFormula
section
noncomputable section

open NumberField IsDedekindDomain

namespace PI

def LocProdFormula : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], Module.finrank F E = 2 →
    ∀ (sig : E →ₐ[F] E) (atP : ∀ p : HeightOneSpectrum (𝓞 F), Formalism.MainNotions.S.Loc.LocAt F E sig p)
      (M : ∀ p : HeightOneSpectrum (𝓞 F), Formalism.MainNotions.S.Loc.Model (atP p).Fp (atP p).Ep), (∀ p, (M p).OK) →
      ∀ x : E, x ≠ 0 → ∏ᶠ p, (M p).modK ((atP p).ιE x) = (((|Algebra.norm ℚ x| : ℚ)) : ℝ)⁻¹

end PI
end
end

-- bundled from Formalism.PeriodIntegrals.ParahoricIdxZ
section
noncomputable section

open MeasureTheory Matrix ComplexConjugate Finset

namespace PI.ParahoricIdxZ

def qE (q : ℝ) (a c : ℕ) : ℝ := ∏ i ∈ Icc a c, (1 - q ^ (-(i : ℤ)))

def zetaProd (q : ℝ) (n : ℕ) : ℝ := (qE q 1 n)⁻¹

def blockCond {F : Type} [Field F] (O : Subring F) (ϖ : F) {a t : ℕ}
    (J' : Subgroup (GL (Fin a) F)) (A : GL (Fin (a + t)) F) : Prop :=
  let M : Matrix (Fin a ⊕ Fin t) (Fin a ⊕ Fin t) F :=
    Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm (A : Matrix (Fin (a + t)) (Fin (a + t)) F)
  (∃ k ∈ J', (k : Matrix (Fin a) (Fin a) F) = M.toBlocks₁₁) ∧
  (∀ i j, M.toBlocks₁₂ i j ∈ O) ∧
  M.toBlocks₂₁ ∈ Formalism.DoubleCosetMeasures.IIset O ϖ ∧
  (∃ D ∈ Formalism.DoubleCosetMeasures.GLint O t, (D : Matrix (Fin t) (Fin t) F) = M.toBlocks₂₂)

end PI.ParahoricIdxZ

namespace PI

open PI.ParahoricIdxZ in

def ParahoricIdxZ : Prop :=
  ∀ (F : Type) [Field F] [TopologicalSpace F] [IsTopologicalRing F] [T2Space F]
    [SecondCountableTopology F] [MeasurableSpace F] [BorelSpace F] (O : Subring F),
    IsOpen (O : Set F) → ∀ (ϖ : F) (hϖ : ϖ ∈ O), ϖ ≠ 0 → Formalism.DoubleCosetMeasures.IsLocalAt O ϖ →
    Finite (Formalism.DoubleCosetMeasures.kF O ϖ hϖ) → ∀ (a t : ℕ) (J' : Subgroup (GL (Fin a) F)),
    Formalism.DoubleCosetMeasures.congSub O ϖ a ≤ J' → J' ≤ Formalism.DoubleCosetMeasures.GLint O a → IsCompact (J' : Set (GL (Fin a) F)) →
    ∀ (ρ : J' →* ℂˣ), (∀ k, ‖((ρ k : ℂˣ) : ℂ)‖ = 1) →
    ∀ (χ : Fˣ →* ℂˣ) (nrm : AbsoluteValue F ℝ) (lam : J' →* ℂˣ),
    (∀ k : J', ((χ (Matrix.GeneralLinearGroup.det (k : GL (Fin a) F)) : ℂˣ) : ℂ) *
        (((nrm ((Matrix.GeneralLinearGroup.det (k : GL (Fin a) F) : Fˣ) : F)) ^
          (((a + t : ℕ) : ℝ) / 2) : ℝ) : ℂ) *
        ((ρ k : ℂˣ) : ℂ) * conj ((lam k : ℂˣ) : ℂ) = 1) →
    ∀ (c : GL (Fin a) F → ℂ), (∀ g : GL (Fin a) F, ∀ k : J', c (g * k) = ((lam k : ℂˣ) : ℂ) * c g) →
    c 1 = 1 →
    ∀ (μ : Measure (GL (Fin a) F)) [μ.IsMulLeftInvariant], μ (J' : Set (GL (Fin a) F)) = 1 →
    ∀ (ν₁ : Measure (Matrix (Fin a) (Fin a) F)) [ν₁.IsAddLeftInvariant] [SFinite ν₁],
    ν₁ (Formalism.DoubleCosetMeasures.intMat O a a) = 1 →
    ∀ (ν₂ : Measure (Matrix (Fin t) (Fin a) F)) [ν₂.IsAddLeftInvariant] [SFinite ν₂],
    ν₂ (Formalism.DoubleCosetMeasures.intMat O t a) = 1 →
    ∀ (J : Subgroup (GL (Fin (a + t)) F)), (∀ A, A ∈ J ↔ blockCond O ϖ J' A) →
    let q : ℝ := Nat.card (Formalism.DoubleCosetMeasures.kF O ϖ hϖ)
    ((J.subgroupOf (Formalism.DoubleCosetMeasures.GLint O (a + t))).index : ℂ) * ((zetaProd q (a + t) : ℝ) : ℂ) *
        Formalism.DoubleCosetMeasures.localZ μ ((ν₁.prod ν₂).map (fun p => Matrix.fromRows p.1 p.2)) χ nrm
          (Formalism.DoubleCosetMeasures.phiU O ϖ J' ρ) (Formalism.DoubleCosetMeasures.phiU O ϖ J' ρ) c =
      ((zetaProd q t : ℝ) : ℂ)

end PI
end
end

-- bundled from Formalism.PeriodIntegrals.PinHostLoc
section
noncomputable section

open scoped Classical

open IsDedekindDomain NumberField ValuativeRel MeasureTheory

namespace PI.PinHostLoc

def Target : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (sig : E →ₐ[F] E) (p : HeightOneSpectrum (𝓞 F)) (A : Formalism.MainNotions.S.Loc.LocAt F E sig p)
    (g : Fin 2 → ℕ), (∀ i, (g i).Prime) → g 0 ≠ g 1 →
    ∀ i : Fin 2, ((g i : ℕ) : 𝓞 F) ∈ p.asIdeal → ((g i : ℕ) : 𝓞 F) ∉ p.asIdeal ^ 2 →
      Irreducible ((Formalism.MainNotions.S.Loc.resChar p : ℕ) : 𝒪[A.Fp]) ∧
        ∃ u : 𝒪[A.Fp], IsUnit u ∧
          (u : A.Fp) = A.ιF (((g 0 : ℕ) : F) * ((g 1 : ℕ) : F) / ((g i : ℕ) : F))

end PI.PinHostLoc
end
end

-- bundled from Formalism.PeriodIntegrals.ProdFormulaE
section
noncomputable section

open IsDedekindDomain NumberField

namespace PI.ProdFormulaE

def ProdFormulaE : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (sig : E →ₐ[F] E) (_h2 : Module.finrank F E = 2)
    (L : ∀ p : HeightOneSpectrum (𝓞 F), Formalism.MainNotions.S.Loc.LocAt F E sig p),
  (∀ M : ∀ p, Formalism.MainNotions.S.Loc.Model (L p).Fp (L p).Ep, (∀ p, (M p).OK) →
    ∀ x : E, x ≠ 0 →
      (Function.mulSupport fun p => (M p).modK ((L p).ιE x)).Finite ∧
      ∏ᶠ p, (M p).modK ((L p).ιE x) = |((Algebra.norm ℚ x : ℚ) : ℝ)|⁻¹) ∧
  (∀ x : E,
    (Function.mulSupport fun p => (L p).psiE ((L p).ιE x)).Finite ∧
    ∏ᶠ p, (L p).psiE ((L p).ιE x) =
      Complex.exp (2 * Real.pi * Complex.I * (((Algebra.trace ℚ E x : ℚ) : ℂ))))

end PI.ProdFormulaE
end
end

-- bundled from Formalism.PeriodIntegrals.QmDefs
section
open Matrix Finset

noncomputable section

namespace PI

open Formalism.REAL

def skip1 {t : ℕ} (i : Fin t) (j : Fin (t - 1)) : Fin t :=
  if j.val < i.val then ⟨j.val, by have := j.isLt; omega⟩ else ⟨j.val + 1, by have := j.isLt; omega⟩

def skip2 {t : ℕ} (i i' : Fin t) (j : Fin (t - 2)) : Fin t :=
  if j.val < i.val then ⟨j.val, by have := j.isLt; omega⟩
  else if j.val + 1 < i'.val then ⟨j.val + 1, by have := j.isLt; omega⟩
  else ⟨j.val + 2, by have := j.isLt; omega⟩

def SkipSucc : Prop := ∀ (t : ℕ) (i : Fin (t + 1)) (j : Fin t), skip1 i j = i.succAbove j

def SkipSucc2 : Prop :=
  ∀ (t : ℕ) (i : Fin (t + 2)) (i' : Fin (t + 1)) (j : Fin t), i.val ≤ i'.val →
    skip2 i (i.succAbove i') j = i.succAbove (i'.succAbove j)

def qminorRow {A : Type*} [Ring A] [Algebra ℂ A] {n t : ℕ} (E : Fin n → Fin n → A)
    (a b : Fin t → Fin n) (u : ℂ) : A :=
  ∑ σ : Equiv.Perm (Fin t),
    ((Equiv.Perm.sign σ : ℤ) : A) *
      (List.ofFn fun k : Fin t => Tm E (u - (t : ℂ) + 1 + ((k : ℕ) : ℂ)) (a k) (b (σ k))).prod

def RowForm : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n t : ℕ) (E : Fin n → Fin n → A), GlRel E →
    ∀ (a b : Fin t → Fin n) (u : ℂ), qminor E a b u = qminorRow E a b u

def ExpFirstCol : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n t : ℕ) (E : Fin n → Fin n → A) (a b : Fin (t + 1) → Fin n) (u : ℂ),
    qminor E a b u = ∑ l : Fin (t + 1), (((-1 : ℤ) ^ (l : ℕ) : ℤ) : A) *
      (Tm E u (a l) (b 0) * qminor E (a ∘ l.succAbove) (b ∘ Fin.succ) (u - 1))

def ExpLastCol : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n t : ℕ) (E : Fin n → Fin n → A) (a b : Fin (t + 1) → Fin n) (u : ℂ),
    qminor E a b u = ∑ l : Fin (t + 1), (((-1 : ℤ) ^ (t + (l : ℕ)) : ℤ) : A) *
      (qminor E (a ∘ l.succAbove) (b ∘ Fin.castSucc) u * Tm E (u - (t : ℂ)) (a l) (b (Fin.last t)))

def ExpFirstRow : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n t : ℕ) (E : Fin n → Fin n → A), GlRel E →
    ∀ (a b : Fin (t + 1) → Fin n) (u : ℂ),
      qminor E a b u = ∑ l : Fin (t + 1), (((-1 : ℤ) ^ (l : ℕ) : ℤ) : A) *
        (Tm E (u - (t : ℂ)) (a 0) (b l) * qminor E (a ∘ Fin.succ) (b ∘ l.succAbove) u)

def ExpLastRow : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n t : ℕ) (E : Fin n → Fin n → A), GlRel E →
    ∀ (a b : Fin (t + 1) → Fin n) (u : ℂ),
      qminor E a b u = ∑ l : Fin (t + 1), (((-1 : ℤ) ^ (t + (l : ℕ)) : ℤ) : A) *
        (qminor E (a ∘ Fin.castSucc) (b ∘ l.succAbove) (u - 1) * Tm E u (a (Fin.last t)) (b l))

def MoveVec : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n t : ℕ) (E : Fin n → Fin n → A) (y : Fin n → A), GlRel E →
    (∀ a b c, E a b * y c - y c * E a b = if a = c then -y b else 0) → (∀ a b, y a * y b = y b * y a) →
    ∀ (a : Fin t → Fin n) (b : Fin (t + 1) → Fin n) (w : ℂ),
      ∑ j : Fin (t + 1), (((-1 : ℤ) ^ (j : ℕ) : ℤ) : A) * (y (b j) * qminor E a (b ∘ j.succAbove) w) =
        ∑ j : Fin (t + 1), (((-1 : ℤ) ^ (j : ℕ) : ℤ) : A) * (qminor E a (b ∘ j.succAbove) (w - 1) * y (b j))

def MoveCov : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n t : ℕ) (E : Fin n → Fin n → A) (η : Fin n → A), GlRel E →
    (∀ a b c, E a b * η c - η c * E a b = if b = c then η a else 0) → (∀ a b, η a * η b = η b * η a) →
    ∀ (a : Fin (t + 1) → Fin n) (b : Fin t → Fin n) (w : ℂ),
      ∑ i : Fin (t + 1), (((-1 : ℤ) ^ (i : ℕ) : ℤ) : A) * (η (a i) * qminor E (a ∘ i.succAbove) b (w - 1)) =
        ∑ i : Fin (t + 1), (((-1 : ℤ) ^ (i : ℕ) : ℤ) : A) * (qminor E (a ∘ i.succAbove) b w * η (a i))

def StarMinor : Prop :=
  ∀ (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (n t : ℕ) (E : Fin n → Fin n → A)
    (ε : Fin n → ℤˣ), GlRel E → (∀ a b, star (E a b) = (((ε a * ε b : ℤˣ) : ℤ) : A) * E b a) →
    ∀ (a b : Fin t → Fin n) (w : ℂ),
      star (qminor E a b w) = ((((∏ k, ε (a k)) * ∏ k, ε (b k) : ℤˣ) : ℤ) : A) * qminor E b a (star w)

def bE {n m : ℕ} (e : Fin n) (v : Fin m → Fin n) : Fin (m + 1) → Fin n := Fin.cons (α := fun _ => Fin n) e v

def bS {n m : ℕ} (v : Fin m → Fin n) (es : Fin n) : Fin (m + 1) → Fin n := Fin.snoc (α := fun _ => Fin n) v es

def sg2 {m : ℕ} (w w' : Fin m) : ℤ :=
  if w'.val < w.val then (-1) ^ (w.val + w'.val) else (-1) ^ (w.val + w'.val + 1)

def IsBorder {n m : ℕ} (e es : Fin n) (v : Fin m → Fin n) : Prop :=
  Function.Injective v ∧ e ≠ es ∧ (∀ j, v j ≠ e) ∧ ∀ j, v j ≠ es

def BorderE : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n m : ℕ) (E : Fin n → Fin n → A) (e es : Fin n) (v : Fin m → Fin n),
    GlRel E → IsBorder e es v → ∀ u : ℂ,
      qminor E (bE e v) (bE e v) u = Tm E u e e * qminor E v v (u - 1) -
        ∑ w : Fin m, ∑ x : Fin m, (((-1 : ℤ) ^ ((w : ℕ) + (x : ℕ)) : ℤ) : A) *
          (E (v w) e * qminor E (v ∘ skip1 w) (v ∘ skip1 x) (u - 2) * E e (v x))

def BorderS : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n m : ℕ) (E : Fin n → Fin n → A) (e es : Fin n) (v : Fin m → Fin n),
    GlRel E → IsBorder e es v → ∀ u : ℂ,
      qminor E (bS v es) (bS v es) u = qminor E v v u * Tm E (u - (m : ℂ)) es es -
        ∑ w : Fin m, ∑ x : Fin m, (((-1 : ℤ) ^ ((w : ℕ) + (x : ℕ)) : ℤ) : A) *
          (E es (v x) * qminor E (v ∘ skip1 w) (v ∘ skip1 x) u * E (v w) es)

def BorderFull : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n m : ℕ) (E : Fin n → Fin n → A) (e es : Fin n) (v : Fin m → Fin n),
    GlRel E → IsBorder e es v → ∀ u : ℂ,
      qminor E (bE e (bS v es)) (bE e (bS v es)) u =
        Tm E u e e * qminor E v v (u - 1) * Tm E (u - (m : ℂ) - 1) es es
        - (∑ w : Fin m, ∑ x : Fin m, (((-1 : ℤ) ^ ((w : ℕ) + (x : ℕ)) : ℤ) : A) *
            (E es (v x) * Tm E u e e * qminor E (v ∘ skip1 w) (v ∘ skip1 x) (u - 1) * E (v w) es))
        - (∑ w : Fin m, ∑ x : Fin m, (((-1 : ℤ) ^ ((w : ℕ) + (x : ℕ)) : ℤ) : A) *
            (E (v w) e * qminor E (v ∘ skip1 w) (v ∘ skip1 x) (u - 2) * Tm E (u - (m : ℂ) - 1) es es * E e (v x)))
        - (∑ w : Fin m, ∑ w' : Fin m, ∑ x : Fin m, ∑ x' : Fin m,
            if w ≠ w' ∧ x ≠ x' then ((sg2 w w' * sg2 x x' : ℤ) : A) *
              (E (v w) e * E es (v x) *
                qminor E (v ∘ skip2 (min w w') (max w w')) (v ∘ skip2 (min x x') (max x x')) (u - 2) *
                E e (v x') * E (v w') es)
            else 0)
        + (((-1 : ℤ) ^ (m + 1) : ℤ) : A) * (E es e * qminor E (bE e v) (bS v es) (u - 1))
        + ∑ w : Fin m, (((-1 : ℤ) ^ ((w : ℕ) + 1 + m) : ℤ) : A) *
            (E (v w) e * qminor E (Fin.snoc (α := fun _ => Fin n) (v ∘ skip1 w) es ∘ Fin.cast (by
                have := w.isLt; omega)) v (u - 1) * E e es)

end PI
end
end

-- bundled from Formalism.PeriodIntegrals.RTTIndependence
section
open Matrix Finset

noncomputable section

namespace PI

open Formalism Formalism.FourierDecayAlt

def RTTSandwich : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (QQ : ℂ → Matrix (Fin 2) (Fin 2) A) (p c ci p' c' ci' : A),
    YangianSpanCharacter.T.WeylRel p c ci → YangianSpanCharacter.T.WeylRel p' c' ci' →
    (∀ x ∈ ({p, c, ci} : Set A), ∀ y ∈ ({p', c', ci'} : Set A), x * y = y * x) →
    (∀ x ∈ ({p, c, ci, p', c', ci'} : Set A), ∀ Y a b, x * QQ Y a b = QQ Y a b * x) →
    ∀ Y Y' : ℂ,
      let C : ℂ → A := fun y => (YangianSpanCharacter.T.Tm y p' c' ci' * QQ y * YangianSpanCharacter.T.Tm y p c ci) 0 0
      let X : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A :=
        ((Y' - Y) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) - YangianSpanCharacter.T.Pf A) * YangianSpanCharacter.T.E1 (QQ Y') * YangianSpanCharacter.T.E2 (QQ Y) -
          YangianSpanCharacter.T.E2 (QQ Y) * YangianSpanCharacter.T.E1 (QQ Y') * ((Y' - Y) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) - YangianSpanCharacter.T.Pf A)
      algebraMap ℂ A (Y' - Y - 1) * (C Y' * C Y - C Y * C Y') =
        ((YangianSpanCharacter.T.T2 Y p' c' ci' * YangianSpanCharacter.T.T1 Y' p' c' ci') * X * (YangianSpanCharacter.T.T1 Y' p c ci * YangianSpanCharacter.T.T2 Y p c ci)) (0, 0) (0, 0)

def RTTIndependence : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (x : Fin 2 × Fin 2 → Fin 2 × Fin 2 → V) (Y Y' : ℂ), Y' ≠ Y + 1 →
    (∀ (c : ℂ), c ≠ 0 → ∀ (β : ℂ) (n : ℤ),
      ∑ A : Fin 2 × Fin 2, ∑ B : Fin 2 × Fin 2,
        ((if A = (0, 0) then (Y - β) * (Y' - β) else if A = (0, 1) then Y' - β else if A = (1, 0) then Y - β + 1 else 1) *
          (if B = (0, 0) then (Y' + (β + n)) * (Y + (β + n)) else if B = (0, 1) then Y' + (β + n) - 1
            else if B = (1, 0) then Y + (β + n) else 1) *
          (((‖c‖ : ℂ) ^ (2 * β)) * c ^ n * (c ^ ((B.1 : ℕ) + (B.2 : ℕ)))⁻¹ * (star c ^ ((A.1 : ℕ) + (A.2 : ℕ)))⁻¹)) • x A B = 0) →
    ∀ A B, x A B = 0

def QdetFromRTT : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (QQ : ℂ → Matrix (Fin 2) (Fin 2) A), W.IsRTT QQ → ∀ Y : ℂ, ∃ qh : A,
    (QQ (Y + 1))ᵀ * YangianSpanCharacter.T.J A * QQ Y = qh • YangianSpanCharacter.T.J A ∧ QQ Y * YangianSpanCharacter.T.J A * (QQ (Y + 1))ᵀ = qh • YangianSpanCharacter.T.J A ∧
    ∀ Y' a b, qh * QQ Y' a b = QQ Y' a b * qh

def LemmaD : Prop :=
  ∀ (A : Type) [CommRing A] [IsDomain A] (DD : ℕ → Set (A →+ A)), DD 0 = {0} →
    (∀ n, ∀ D ∈ DD (n + 1), ∀ a : A, ∃ D' ∈ DD n, ∀ b, D' b = D (a * b) - a * D b) →
    ∀ A' : AddSubgroup A, (∀ x ∈ A', ∀ y ∈ A', x * y ∈ A') →
    (∀ b : A, ∃ a₁ ∈ A', ∃ a₂ ∈ A', a₂ ≠ 0 ∧ a₂ * b = a₁) →
    ∀ n, ∀ D ∈ DD n, (∀ x ∈ A', D x = 0) → D = 0

end PI
end
end

-- bundled from Formalism.PeriodIntegrals.StabBig
section
open Matrix

noncomputable section

namespace PI

open Formalism.QuantumDeterminants

def RStab (k r : ℕ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :=
  {a | a ∈ Nset k r ∧ g⁻¹ * a * g ∈ Nset k r}

def StabBig : Prop :=
  ∀ (k r : ℕ) (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ),
    (∀ a, c a ≠ 0) → μᴴ * Hb k * μ = Hb k → RStab k r (bigCell k r c μ) = {1}

end PI
end
end

-- bundled from Formalism.PeriodIntegrals.StrongApproxE
section
noncomputable section

open IsDedekindDomain NumberField

namespace PI.StrongApproxE

def StrongApproxE : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (sig : E →ₐ[F] E) (_h2 : Module.finrank F E = 2)
    (L : ∀ p : HeightOneSpectrum (𝓞 F), Formalism.MainNotions.S.Loc.LocAt F E sig p)
    (U : ∀ p, AddSubgroup (L p).Ep), (∀ p, IsOpen (U p : Set (L p).Ep)) →
    {p | (U p : Set (L p).Ep) ≠ ((L p).O : Set (L p).Ep)}.Finite →
    ∀ x : ∀ p, (L p).Ep, {p | x p ∉ (L p).O}.Finite →
      ∃ t : E, ∀ p, (L p).ιE t - x p ∈ U p

end PI.StrongApproxE
end
end

-- bundled from Formalism.PeriodIntegrals.TrDualLoc
section
noncomputable section

open ValuativeRel IsDedekindDomain NumberField

namespace PI.TrDualLoc

def Stmt : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (p : HeightOneSpectrum (𝓞 K)) [Fact (Formalism.MainNotions.S.Loc.resChar p).Prime]
    (Fp : Type) [Field Fp] [ValuativeRel Fp] [TopologicalSpace Fp] [IsNonarchimedeanLocalField Fp]
    [Algebra ℚ_[Formalism.MainNotions.S.Loc.resChar p] Fp], Continuous (algebraMap ℚ_[Formalism.MainNotions.S.Loc.resChar p] Fp) →
    FiniteDimensional ℚ_[Formalism.MainNotions.S.Loc.resChar p] Fp → ∀ (ι : K →+* Fp), DenseRange ι →
    (∀ x y : K, (ι x ≤ᵥ ι y) ↔ p.valuation K x ≤ p.valuation K y) →
    ∀ t : K, (∀ a : 𝓞 K, ∃ n : ℤ, Algebra.trace ℚ K (t * a) = n) →
    ∀ c ∈ 𝒪[Fp], ‖Algebra.trace ℚ_[Formalism.MainNotions.S.Loc.resChar p] Fp (c * ι t)‖ ≤ 1

end PI.TrDualLoc
end
end

-- bundled from Formalism.PeriodIntegrals.WhitFunctDual
section
namespace PI

def WhitFunctDual : Prop :=
  Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.GelfandGraevMultOne → Formalism.L2.SG.GGMirabolic.GelfandGraevMultOne

end PI
end

