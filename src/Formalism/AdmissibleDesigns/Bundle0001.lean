import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0005
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.WildPro
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
import Formalism.LocalRingCardinality.SpanPowerMembership.Places

-- bundled from Formalism.AdmissibleDesigns.AdmG5OfAdm51AdmG5
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace Formalism.MainNotions.N.K.SplitLatticeDiagonal

section Conv

variable {K : Type} [Field K] (a b n : ℕ) (hn : n = a + b)

def splitL : (Fin n → K) ≃ₗ[K] ((Fin a → K) × (Fin b → K)) where
  toFun u := (fun j => u ⟨j, by omega⟩, fun j => u ⟨a + j, by omega⟩)
  invFun p := fun k => if h : (k : ℕ) < a then p.1 ⟨k, h⟩ else p.2 ⟨k - a, by omega⟩
  map_add' u v := by ext <;> simp
  map_smul' c u := by ext <;> simp
  left_inv u := by
    funext k
    by_cases h : (k : ℕ) < a
    · simp [h]
    · simp only [h, dite_false]
      congr 1
      exact Fin.ext (by simp; omega)
  right_inv p := by
    ext j
    · simp
    · simp

theorem splitL_diag (c : K) (u : Fin n → K) (k : Fin n) :
    (splitL a b n hn).symm ((splitL a b n hn u).1, c • (splitL a b n hn u).2) k =
      (if (k : ℕ) < a then 1 else c) * u k := by
  by_cases h : (k : ℕ) < a
  · show (if h' : (k : ℕ) < a then u ⟨k, by omega⟩ else c * u ⟨a + (k - a), by omega⟩) = _
    simp [h]
  · show (if h' : (k : ℕ) < a then u ⟨k, by omega⟩ else c * u ⟨a + (k - a), by omega⟩) = _
    simp only [h, dite_false, if_false]
    congr 2
    exact Fin.ext (by simp; omega)

end Conv

theorem admG5_of_adm51_admG5 {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (hπ : π ∈ D.nd.Z i)
    (h51 : LargeLevelLemmas.adm51 i r ρ π) (h5 : EmbeddingTypes.admG5 i r ρ π) : TruncatedSeriesCountingIdentities.admG5 i r := by
  classical
  obtain ⟨S, hS⟩ := h51 hπ
  have G := h5 hπ S hS
  intro w hw
  obtain ⟨hT, ha, hb, -⟩ := G w hw
  refine ⟨fun hc x => ?_, fun hk _ hT' => ?_⟩
  · obtain ⟨hprod, e, he⟩ := ha hc x
    refine ⟨fun γ hγ => by simpa [rO, chi1] using hprod γ hγ, ?_⟩
    let sp : (Fin D.R.nV → KK D.nd i) ≃ₗ[KK D.nd i] ((Fin D.R.r → KK D.nd i) × (Fin D.R.t → KK D.nd i)) :=
      splitL D.R.r D.R.t D.R.nV rfl
    let ψ : (Fin D.R.nV → KK D.nd i) ≃ₗ[KK D.nd i] (Fin D.R.nV → KK D.nd i) := e.trans sp.symm
    let Pm : GL (Fin D.R.nV) (KK D.nd i) :=
      ⟨LinearMap.toMatrix' (ψ.symm : (Fin D.R.nV → KK D.nd i) →ₗ[KK D.nd i] _),
        LinearMap.toMatrix' (ψ : (Fin D.R.nV → KK D.nd i) →ₗ[KK D.nd i] _),
        by rw [← LinearMap.toMatrix'_comp]; simp,
        by rw [← LinearMap.toMatrix'_comp]; simp⟩
    refine ⟨Pm, fun γ hγ => ?_⟩
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro u
    have hM : ((mapRep (algebraMap (D.nd.O i) (KK D.nd i)) (r x) γ : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) =
        mapM (toK D.nd i) (rO D.nd i r x) γ := rfl
    have h1 : ((Pm⁻¹ : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) =
        LinearMap.toMatrix' (ψ : (Fin D.R.nV → KK D.nd i) →ₗ[KK D.nd i] _) := rfl
    have h2 : ((Pm : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) =
        LinearMap.toMatrix' (ψ.symm : (Fin D.R.nV → KK D.nd i) →ₗ[KK D.nd i] _) := rfl
    rw [Units.val_mul, Units.val_mul, Matrix.toLin'_mul, Matrix.toLin'_mul, LinearMap.comp_apply,
      LinearMap.comp_apply, hM, h1, h2, Matrix.toLin'_toMatrix', Matrix.toLin'_toMatrix',
      Matrix.toLin'_apply, Matrix.toLin'_apply]
    have key' := he γ hγ (e.symm (sp u))
    rw [LinearEquiv.apply_symm_apply] at key'
    change sp.symm (e ((mapM (toK D.nd i) (rO D.nd i r x) γ).mulVec (e.symm (sp u)))) = _
    rw [key']
    funext k
    rw [Matrix.mulVec_diagonal]
    exact splitL_diag D.R.r D.R.t D.R.nV rfl _ u k
  · obtain ⟨P, hP, hU⟩ := hb hk
    refine ⟨P, hU, fun x γ hγ => ?_⟩
    simpa [rO, chi1, evT] using hP x γ hγ

end Formalism.MainNotions.N.K.SplitLatticeDiagonal

end
end

-- bundled from Formalism.AdmissibleDesigns.RestrictedSevenEightOfFull
section
noncomputable section

open Classical Formalism.BasicNotions

namespace Formalism.MainNotions.N.K.Rows

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions Formalism.MainNotions.N

variable (D : D7)

def AllDesignConditions : Prop :=
  ∀ i : D.nd.Loc, D.nd.l i ≠ D.host.g 0 → D.nd.l i ≠ D.host.g 1 →
    ∀ (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
      (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i)
      (lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ) (e' : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ),
      GoodR D.nd i r → TruncatedSeriesCountingIdentities.admitted i r ρ π dc lenRow e' cB → LargeLevelLemmas.adm51 i r ρ π

def SomeDesignCondition : Prop :=
  ∀ i : D.nd.Loc, D.nd.l i ≠ D.host.g 0 → D.nd.l i ≠ D.host.g 1 →
    ∀ (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
      (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i)
      (lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ) (e' : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ),
      TruncatedSeriesCountingIdentities.admitted i r ρ π dc lenRow e' cB → LargeLevelLemmas.adm51 i r ρ π

def UnrInAll : Prop :=
  ∀ (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)), w ∈ dc.col →
    Formalism.WeaklyAdmissibleFiltrations.Z1ur (1 : Representation ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1 (Br.G D.nbr i w hw)
              ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1) (Br.inert D.nbr i w hw) ≤
      Formalism.WeaklyAdmissibleFiltrations.finiteCocycles (Br.PD D.loc D.nbr i w hw)
        (1 : Representation ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1 (Br.G D.nbr i w hw) ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1)

def BKaAll : Prop := ∀ i : D.nd.Loc, LargeLevelLemmas.BlochKatoAnnihilators i

def FinAll : Prop := ∀ i : D.nd.Loc, LargeLevelLemmas.tateH1FinitenessAtPlacesOver i

def SelfGoodAll : Prop :=
  ∀ (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
    (TruncatedSeriesCountingIdentities.CoefExt.self i w hw).IsGood

def QPowAll : Prop :=
  ∀ i : D.nd.Loc, ∀ v ∈ D.nd.Q i, ∀ g ∈ Ine (F := D.host.E) (D.nd.plOm.1 v),
    ∃ n : ℕ, D.nd.chi i 1 g = D.nd.chi i 1 (D.nd.gam0 i v) ^ n

def Rows : Prop :=
  AllDesignConditions D ∧ UnrInAll D ∧ BKaAll D ∧ FinAll D

def MainBoundForDesign : Prop :=
  ∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i)
    (lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ) (e' : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ),
    GoodR D.nd i r → TruncatedSeriesCountingIdentities.admitted i r ρ π dc lenRow e' cB → TruncatedSeriesCountingIdentities.GlobalLatticeIndexTheorem i ρ π dc lenRow e' cB

def SecondMainBoundForDesign : Prop :=
  ∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i)
    (lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ) (e' : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ),
    GoodR D.nd i r → LargeLevelLemmas.admitted i r ρ π → LargeLevelLemmas.Conclusion1 i r ρ π dc lenRow e' cB

def PurityConditionsForDesign : Prop :=
  ∀ (ep : Bool) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i)
    (e' : ℕ) (c0 : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ),
    GoodR D.nd i r → EmbeddingTypes.admitted i r ρ π dc ep e' c0 cB → EmbeddingTypes.aux₃ i r ρ π dc ep e' c0 cB

end Formalism.MainNotions.N.K.Rows

end
end

