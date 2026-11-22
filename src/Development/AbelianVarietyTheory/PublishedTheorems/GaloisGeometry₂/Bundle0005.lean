import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsStrictlySemistableAlt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.CaraianiTempered
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.Published

def CaraianiTempered : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ), 2 ≤ n →
    ∀ π : CuspSub L n, π.IsCsd → GKCoh.IsCohomological π →
      ∀ (y : HeightOneSpectrum (𝓞 L)) (σ : SmIrr (GL (Fin n) (y.adicCompletion L))), π.IsLocComp y σ →
        LocGL.IsTemperedCoeff σ.ρ

end GlobalTheory.Published
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ClozelCohomologicalModel
section
noncomputable section

open NumberField GlobalTheory.CuspRep

namespace GlobalTheory.Published

def ClozelCohomological : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ π : CuspSub E a,
    (CG.mk π).IsRegAlg → GKCoh.IsCohomological π

end GlobalTheory.Published
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ClozelPurity
section
noncomputable section

open NumberField GlobalTheory.CuspRep

namespace GlobalTheory.Published

def ClozelPurity : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ π : CuspSub E a,
    (∀ τ, ∀ z ∈ (CG.mk π).infChar τ, ∃ n : ℤ, z = (n : ℂ) + ((a : ℂ) - 1) / 2) →
    ∃ w₀ : ℤ, ∀ τ : E →+* ℂ,
      (CG.mk π).infChar ((starRingEnd ℂ).comp τ) = ((CG.mk π).infChar τ).map fun z => (w₀ : ℂ) - z

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GaloisRepOfPolarizedPair
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp

namespace GlobalTheory.Published

def GaloisRepOfPolarizedPair : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a →
    ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)), (CG.mk π).IsRegAlg → GlobalTheory.ContraPair.PolarizedPair π χ →
      ∃ (r : G E Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (E →+* Qbar l) → Multiset ℤ), IsGalRepOf π χ ι r wt HT

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsStrictlySemistableBase
section
noncomputable section
open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.SemistableModel

def evalQ (O : Type) [CommRing O] (ϖ : O) :
    (MvPolynomial (Fin 1) O ⧸ Ideal.span {(∏ i ∈ Finset.univ.filter (fun i : Fin 1 => (i : ℕ) < 1), MvPolynomial.X i) -
      MvPolynomial.C ϖ}) →+* O :=
  Ideal.Quotient.lift _ (MvPolynomial.aeval (fun _ : Fin 1 => ϖ) : MvPolynomial (Fin 1) O →ₐ[O] O).toRingHom (by
    intro a ha
    rw [Ideal.mem_span_singleton] at ha
    obtain ⟨b, rfl⟩ := ha
    simp)

theorem evalQ_algebraMap (O : Type) [CommRing O] (ϖ : O) (o : O) :
    evalQ O ϖ (algebraMap O _ o) = o := by
  change evalQ O ϖ (Ideal.Quotient.mk _ (MvPolynomial.C o)) = o
  simp [evalQ]

theorem evalQ_bijective (O : Type) [CommRing O] (ϖ : O) : Function.Bijective (evalQ O ϖ) := by
  let I : Ideal (MvPolynomial (Fin 1) O) := Ideal.span {(∏ i ∈ Finset.univ.filter (fun i : Fin 1 => (i : ℕ) < 1), MvPolynomial.X i) -
      MvPolynomial.C ϖ}
  have key : (Ideal.Quotient.mkₐ O I) = (Algebra.ofId O _).comp (MvPolynomial.aeval fun _ : Fin 1 => ϖ) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i
    simp only [Ideal.Quotient.mkₐ_eq_mk, AlgHom.comp_apply, MvPolynomial.aeval_X, Algebra.ofId_apply]
    change _ = Ideal.Quotient.mk I (MvPolynomial.C ϖ)
    rw [Ideal.Quotient.eq]
    apply Ideal.subset_span
    simp [I]
  refine ⟨fun a b hab => ?_, fun o => ⟨algebraMap O _ o, evalQ_algebraMap O ϖ o⟩⟩
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  have ha := AlgHom.congr_fun key a
  have hb := AlgHom.congr_fun key b
  simp only [Ideal.Quotient.mkₐ_eq_mk, AlgHom.comp_apply, Algebra.ofId_apply] at ha hb
  change Ideal.Quotient.mk I a = Ideal.Quotient.mk I b
  rw [ha, hb]
  change (MvPolynomial.aeval fun _ : Fin 1 => ϖ) a = (MvPolynomial.aeval fun _ : Fin 1 => ϖ) b at hab
  rw [hab]

theorem isStrictlySemistable_base (O : Type) [CommRing O] (ϖ : O) :
    GlobalTheory.Et.IsStrictlySemistable ϖ (𝟙 (Spec (CommRingCat.of O))) := by
  intro x
  let T := ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ Scheme.Hom.appLE (𝟙 (Spec (CommRingCat.of O))) ⊤ ⊤ le_top)
  have hT : Function.Bijective T.hom := by
    have : IsIso T := by
      have h1 : Scheme.Hom.appLE (𝟙 (Spec (CommRingCat.of O))) ⊤ ⊤ le_top = 𝟙 _ := by
        simp [Scheme.Hom.appLE]
      simp only [T, h1, Category.comp_id]
      infer_instance
    exact ConcreteCategory.bijective_of_isIso T
  refine ⟨⊤, isAffineOpen_top _, trivial, 1, 1, le_rfl, le_rfl, T.hom.comp (evalQ O ϖ), ?_, ?_⟩
  · exact RingHom.Etale.of_bijective (hT.comp (evalQ_bijective O ϖ))
  · ext o
    simp [evalQ_algebraMap, T]

end GlobalTheory.SemistableModel
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.LocalGlobalAboveL
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.Published

def LocalGlobalAboveL : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 2 ≤ a →
    ∀ π : CuspSub E a, π.IsCsd → GKCoh.IsCohomological π →
    ∀ (r : G E Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (E →+* Qbar l) → Multiset ℤ),
      IsGalRepOf π (quadChar E ^ a) ι r wt HT →
    ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw),
      ∀ σ, π.IsLocComp w σ → ∀ rc, IsRec h rc →
        wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype) = rc (algNorm σ)

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.RegularAlgebraicPurity
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.Published

def RegularAlgebraicPurity : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ), 1 ≤ a → ∀ π : CuspSub E a, (CG.mk π).IsRegAlg →
    (∃ w₀ : ℤ, ∀ τ : E →+* ℂ,
      (CG.mk π).infChar ((starRingEnd ℂ).comp τ) = ((CG.mk π).infChar τ).map fun z => (w₀ : ℂ) - z) ∧
    GKCoh.IsCohomological π

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.WignerVanishingGL
section
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh

namespace GlobalTheory.WignerGL

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

def dualS (Ξ : AlgRep E a) (i j : Fin a) (x : Cinf E) : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ :=
  -(Ξ.dmat (toL (Matrix.single i j x)))ᵀ

def dualE (Ξ : AlgRep E a) (τ : E →+* ℂ) (i j : Fin a) : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ :=
  (1 / 2 : ℂ) • (dualS Ξ i j (atEmb τ 1) - Complex.I • dualS Ξ i j (atEmb τ Complex.I))

def HasDualInfChar (Ξ : AlgRep E a) (τ : E →+* ℂ) (m : Multiset ℂ) : Prop :=
  Multiset.card m = a ∧ ∀ u : ℂ, Formalism.REAL.qdet (dualE Ξ τ) (u + ((a : ℂ) - 1) / 2) =
    (m.map (u + ·)).prod • (1 : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ)

end GlobalTheory.WignerGL

namespace GlobalTheory.Published

def WignerVanishingGL : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (Ξ : AlgRep E a)
    (m m' : (E →+* ℂ) → Multiset ℂ), (∀ τ, π.HasInfChar τ (m τ)) → (∀ τ, WignerGL.HasDualInfChar Ξ τ (m' τ)) →
    m ≠ m' → ¬ IsCohFor π Ξ

end GlobalTheory.Published

end
end

