import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsFieldSubalgebraSelf
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AlgebraMapMemChartRingLine
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.BaseComap
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)

noncomputable def baseComap (F : Type) [Field F] {K : Type} {ι : K → Type} (k₀ : K) {N : ℕ} (e : ι k₀ ≃ Fin (N + 1))
    (W : Ideal (NumbersDVR.MRing ι F)) : Ideal (NumbersDVR.MRing (fun _ : Unit => Fin (N + 1)) F) :=
  W.comap (rename fun p : (Σ _ : Unit, Fin (N + 1)) => (⟨k₀, e.symm p.2⟩ : Σ k, ι k))

def ModelCurves.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1))
    (x : Fin (N + 1) → Ω), x = IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm → IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ →
      ∀ d : ℕ,
        (∀ W : Ideal (NumbersDVR.MRing ι F), NumbersDVR.IsMultiProjPrime W → mIdealOver F y ≤ W →
          relDim W = ((d : ℕ) : WithBot (WithTop ℤ)) →
            NumbersDVR.IsMultiProjPrime (baseComap F k₀ e W) ∧
              mIdealOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) ≤ baseComap F k₀ e W ∧
              relDim (baseComap F k₀ e W) = ((d : ℕ) : WithBot (WithTop ℤ))) ∧
        (∀ P : Ideal (NumbersDVR.MRing (fun _ : Unit => Fin (N + 1)) F), NumbersDVR.IsMultiProjPrime P →
          mIdealOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) ≤ P → relDim P = ((d : ℕ) : WithBot (WithTop ℤ)) →
            ∃ W : Ideal (NumbersDVR.MRing ι F), NumbersDVR.IsMultiProjPrime W ∧ mIdealOver F y ≤ W ∧
              relDim W = ((d : ℕ) : WithBot (WithTop ℤ)) ∧ baseComap F k₀ e W = P)

theorem ModelCurves.hyps (F : Type) [Field F] :
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F (IndefiniteRowSideFullHecke.Kleiman2.pnPt F 1) () ∧
      NumbersDVR.IsMultiProjPrime (mIdealOver F (IndefiniteRowSideFullHecke.Kleiman2.pnPt F 1)) ∧
      relDim (mIdealOver F (IndefiniteRowSideFullHecke.Kleiman2.pnPt F 1)) = ((1 : ℕ) : WithBot (WithTop ℤ)) ∧
      baseComap F () (Equiv.refl (Fin (1 + 1))) (mIdealOver F (IndefiniteRowSideFullHecke.Kleiman2.pnPt F 1)) = ⊥ := by
  refine ⟨IndefiniteRowSideFullHecke.Kleiman2.isModelWithBase_pnPt F 1, ?_, IndefiniteRowSideFullHecke.Kleiman2.relDim_pnPt F 1, ?_⟩
  · rw [IndefiniteRowSideFullHecke.Kleiman2.mIdealOver_pnPt]
    exact NumbersDVR.isMultiProjPrime_bot
  · rw [IndefiniteRowSideFullHecke.Kleiman2.mIdealOver_pnPt, baseComap]
    refine Ideal.comap_bot_of_injective _ (rename_injective _ ?_)
    rintro ⟨⟨⟩, i⟩ ⟨⟨⟩, j⟩ h
    simpa using h

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ConstVanishHypSegment
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (Cell faceSign)

open Classical in

def constD (K : Type*) [Fintype K] [LinearOrder K] (ι : K → Type*) [∀ k, LinearOrder (ι k)] (V : Type*)
    [AddCommGroup V] (n : ℕ) (f : Cell K ι n → V) : Cell K ι (n + 1) → V :=
  fun I => ∑ k, ∑ i ∈ I.1 k,
    if h : (∀ l, (Function.update I.1 k ((I.1 k).erase i) l).Nonempty) ∧
        ∑ l, ((Function.update I.1 k ((I.1 k).erase i) l).card - 1) = n then
      faceSign I.1 k i • f ⟨Function.update I.1 k ((I.1 k).erase i), h⟩
    else 0

def CechConstVanish.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, LinearOrder (ι k)] (V : Type) [AddCommGroup V]
    (G : ∀ k, Finset (ι k)) (z : Cell K ι 1 → V),
    (∀ I : Cell K ι 2, (∀ k, I.1 k ⊆ G k) → constD K ι V 1 z I = 0) →
    ∃ f : Cell K ι 0 → V, ∀ J : Cell K ι 1, (∀ k, J.1 k ⊆ G k) → constD K ι V 0 f J = z J

theorem constVanish_hyp_segment :
    ∀ I : Cell Unit (fun _ => Fin 2) 2, (∀ k, I.1 k ⊆ Finset.univ) →
      constD Unit (fun _ => Fin 2) ℤ 1 (fun _ => 1) I = 0 := by
  intro I _
  exfalso
  have h : (I.1 ()).card - 1 = 2 := by simpa using I.2.2
  have hc : (I.1 ()).card ≤ 2 := by simpa using Finset.card_le_univ (I.1 ())
  omega

example (h : CechConstVanish.Statement) :=
  h Unit (fun _ => Fin 2) ℤ (fun _ => Finset.univ) (fun _ => 1) constVanish_hyp_segment

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.HypsMore
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver)

def SecOverLocalization.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω) (β : K → ℤ)
    (S' : Type) [CommRing S'] [Algebra S S'] [Algebra S' Ω] [IsScalarTower S S' Ω]
    (M : Submonoid S) [IsLocalization M S'],
    secOver S' y β = Submodule.span S' (secOver S y β : Set Ω)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsBisAltTer
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver secOver secMOver)

def OneBlockPrime.Statement : Prop :=
  ∀ (F : Type) [Field F] (κ : Type) [Fintype κ] (Ω : Type) [Field Ω] [Algebra F Ω] (x' : κ → Ω),
    (∃ i, x' i ≠ 0) → NumbersDVR.IsMultiProjPrime (mIdealOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x'))

def OneBlockHilbFn.Statement : Prop :=
  ∀ (F : Type) [Field F] (κ : Type) [Fintype κ] (Ω : Type) [Field Ω] [Algebra F Ω] (x' : κ → Ω) (n : ℕ),
    NumbersDVR.hilbFn (mIdealOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x')) (fun _ => (n : ℤ)) =
      (Module.finrank F (secMOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') (fun _ => n)) : ℤ)

def ReindexDim.Statement : Prop :=
  ∀ (F : Type) [Field F] (κ : Type) [Fintype κ] (Ω : Type) [Field Ω] [Algebra F Ω] (x' : κ → Ω) (N : ℕ)
    (e : κ ≃ Fin (N + 1)),
    ringKrullDim (NumbersDVR.MRing (fun _ : Unit => κ) F ⧸ mIdealOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x')) =
      ringKrullDim (Kleiman.Poly F N ⧸ Kleiman.primeOf (S := F) (x' ∘ e.symm))

def ReindexPiece.Statement : Prop :=
  ∀ (F : Type) [Field F] (κ : Type) [Fintype κ] (Ω : Type) [Field Ω] [Algebra F Ω] (x' : κ → Ω) (N : ℕ)
    (e : κ ≃ Fin (N + 1)) (n : ℕ),
    secMOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') (fun _ => n) = (Kleiman.coordGraded F (x' ∘ e.symm)).piece (n : ℤ)

def ReindexSecs.Statement : Prop :=
  ∀ (F : Type) [Field F] (κ : Type) [Fintype κ] (Ω : Type) [Field Ω] [Algebra F Ω] (x' : κ → Ω) (N : ℕ)
    (e : κ ≃ Fin (N + 1)) (n : ℤ),
    secOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') (fun _ => n) = (Kleiman.twistSys F (x' ∘ e.symm) n).secs

section Inhabitants

open IndefiniteRowSideFullHecke.Kleiman2

variable (F : Type) [Field F]

end Inhabitants

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsExtraMore
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

def ModelTwistGenerated.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω) (k₀ : K),
    IsNoetherianRing S → IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase S y k₀ → ∀ β : K → ℤ,
      ∃ c₀ : ℤ, ∀ c : ℤ, c₀ ≤ c → IndefiniteRowSideFullHecke.Kleiman2.IsGenerated S y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsFurtherExtra
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)

def ModelDimEq.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1)),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ → ∀ d : ℕ,
      (Kleiman.IsSubvar (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)
          (Kleiman.primeOf (S := F) (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) d ↔
        relDim (mIdealOver F y) = ((d : ℕ) : WithBot (WithTop ℤ)))

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsLastTail
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver chartRingOver)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)

def PointChartField.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) (Ω : Type) [Field Ω] [Algebra F Ω]
    (y : (Σ k, ι k) → Ω),
    relDim (mIdealOver F y) = ((0 : ℕ) : WithBot (WithTop ℤ)) →
    ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → IsField (chartRingOver F y c)

example (F : Type) [Field F] (h : PointChartField.Statement) :=
  h F Unit (IndefiniteRowSideFullHecke.Kleiman2.pnIdx 0) (IndefiniteRowSideFullHecke.Kleiman2.pnField F 0) (IndefiniteRowSideFullHecke.Kleiman2.pnPt F 0)
    (IndefiniteRowSideFullHecke.Kleiman2.relDim_pnPt F 0) (fun _ => 0) (fun _ => IndefiniteRowSideFullHecke.Kleiman2.pnPt_ne_zero F 0 _)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsRestSide
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver chartRingOver secOver)
open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver IsMultiHomog)

def ResidueGen.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω)
    (K' : Type) [Field K'] [Algebra F K'] (y' : (Σ k, ι k) → K'),
    mIdealOver F y ≤ mIdealOver F y' →
    ∀ (R : Subalgebra F Ω) (σ : R →ₐ[F] K'),
      (∀ (f g : MRingOver F ι) (n : K → ℕ), IsMultiHomog f n → IsMultiHomog g n → aeval y' g ≠ 0 →
        ∃ h : aeval y f / aeval y g ∈ R, σ ⟨_, h⟩ = aeval y' f / aeval y' g) →
      (∀ d : ∀ k, ι k, (∀ k, y' ⟨k, d k⟩ ≠ 0) → ∀ z ∈ chartRingOver F y d,
        ∃ h : z ∈ R, σ ⟨z, h⟩ ∈ chartRingOver F y' d) →
    ∀ β : K → ℤ, IndefiniteRowSideFullHecke.Kleiman2.IsGenerated F y β → ∀ d₀ : ∀ k, ι k, (∀ k, y' ⟨k, d₀ k⟩ ≠ 0) →
      ∃ ρ : Ω → K',
        (∀ h ∈ secOver F y β, ∃ hh : h * ∏ k, y ⟨k, d₀ k⟩ ^ (-β k) ∈ R,
          σ ⟨_, hh⟩ = ρ h * ∏ k, y' ⟨k, d₀ k⟩ ^ (-β k)) ∧
        ∀ c : ∀ k, ι k, (∀ k, y' ⟨k, c k⟩ ≠ 0) →
          Submodule.span (chartRingOver F y' c) (ρ '' (secOver F y β : Set Ω)) =
            Submodule.span (chartRingOver F y' c) {(∏ k, y' ⟨k, c k⟩ ^ (-β k))⁻¹}

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsRestTail
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver chartRingOver)
open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver IsMultiHomog)

def ResidueMap.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω)
    (K' : Type) [Field K'] [Algebra F K'] (y' : (Σ k, ι k) → K'),
    mIdealOver F y ≤ mIdealOver F y' →
    ∃ (R : Subalgebra F Ω) (σ : R →ₐ[F] K'),
      (∀ (f g : MRingOver F ι) (n : K → ℕ), IsMultiHomog f n → IsMultiHomog g n → aeval y' g ≠ 0 →
        ∃ h : aeval y f / aeval y g ∈ R, σ ⟨_, h⟩ = aeval y' f / aeval y' g) ∧
      (∀ (k : K) (f g : MvPolynomial (ι k) F) (m : ℕ), f.IsHomogeneous m → g.IsHomogeneous m →
        aeval (IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k) g ≠ 0 →
        ∃ h : aeval (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k) f / aeval (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k) g ∈ R,
          σ ⟨_, h⟩ = aeval (IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k) f / aeval (IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k) g) ∧
      (∀ d : ∀ k, ι k, (∀ k, y' ⟨k, d k⟩ ≠ 0) → ∀ z ∈ chartRingOver F y d,
        ∃ h : z ∈ R, σ ⟨z, h⟩ ∈ chartRingOver F y' d)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsSideExtra
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver mIdealOver)

def SectionsPoly.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ →
      ∃ P : MvPolynomial K ℚ, FieldNumbers.EventuallyPoly (NumbersDVR.hilbFn (mIdealOver F y)) P ∧
        ∀ β : K → ℤ, ∀ᶠ c : ℕ in Filter.atTop,
          (Module.finrank F (secOver F y (β + (c : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀)) : ℚ) =
            eval (fun k => (((β + (c : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k : ℤ) : ℚ)) P

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsFieldChartRingOverPnPtZero
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver chartRingOver cechHc quotPart)

def CechPointVanish.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω),
    (∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → IsField (chartRingOver F y c)) →
    ∀ β : K → ℤ, Subsingleton (cechHc ι (quotPart F (mIdealOver F y)) β 1)

theorem isField_chartRingOver_pnPt_zero (F : Type) [Field F] (c : ∀ k, IndefiniteRowSideFullHecke.Kleiman2.pnIdx 0 k) :
    IsField (chartRingOver F (IndefiniteRowSideFullHecke.Kleiman2.pnPt F 0) c) := by
  have hbot : chartRingOver F (IndefiniteRowSideFullHecke.Kleiman2.pnPt F 0) c = ⊥ := by
    refine eq_bot_iff.mpr (Algebra.adjoin_le ?_)
    rintro _ ⟨⟨u, i⟩, rfl⟩
    have hi : c u = i := Fin.ext (by omega)
    simp only [hi]
    rw [div_self (IndefiniteRowSideFullHecke.Kleiman2.pnPt_ne_zero F 0 _)]
    exact one_mem _
  rw [hbot]
  exact (Algebra.botEquiv F (IndefiniteRowSideFullHecke.Kleiman2.pnField F 0)).toMulEquiv.isField (Field.toIsField F)

example (F : Type) [Field F] (h : CechPointVanish.Statement) :=
  h F Unit (IndefiniteRowSideFullHecke.Kleiman2.pnIdx 0) (IndefiniteRowSideFullHecke.Kleiman2.pnField F 0) (IndefiniteRowSideFullHecke.Kleiman2.pnPt F 0)
    (fun c _ => isField_chartRingOver_pnPt_zero F c) 0

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsStepDataDimZero
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver cechHc quotPart)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)

open IndefiniteRowSideFullHecke.Kleiman2 (pnIdx pnField pnPt) in

theorem isStepData_dimZero (F : Type) [Field F] :
    IndefiniteRowSideFullHecke.Kleiman2.IsStepData F (pnPt F 0) () 0 0 (1 / 2) 2 1 1 1 := by
  refine ⟨IndefiniteRowSideFullHecke.Kleiman2.isModelWithBase_pnPt F 0, IndefiniteRowSideFullHecke.Kleiman2.relDim_pnPt F 0, IndefiniteRowSideFullHecke.Kleiman2.isNef_zero F _,
    by norm_num, by norm_num, by norm_num, le_rfl, ?_, one_ne_zero⟩
  have e : IndefiniteRowSideFullHecke.Kleiman2.stepL () (0 : Unit → ℤ) 2 1 - ((1 : ℕ) : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg () = 0 := by
    funext k
    simp [IndefiniteRowSideFullHecke.Kleiman2.stepL, IndefiniteRowSideFullHecke.Kleiman2.baseDeg]
  rw [e]
  simp only [ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.secOver, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulRight_apply,
    Subalgebra.mem_toSubmodule]
  intro c _
  simp

def ClaimVanishDimZero.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (μ : K → ℤ)
    (r : ℚ) (a : ℕ) (m : ℤ) (c₁ : ℕ) (σ : Ω),
    IndefiniteRowSideFullHecke.Kleiman2.IsStepData F y k₀ 0 μ r a m c₁ σ →
    ∃ c₀ : ℕ, ∀ b c : ℕ, c₀ ≤ c →
      Subsingleton (cechHc ι (quotPart F (mIdealOver F y))
        (b • IndefiniteRowSideFullHecke.Kleiman2.stepL k₀ μ a m + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) 1)

example (F : Type) [Field F] (h : ClaimVanishDimZero.Statement) :=
  h F Unit (IndefiniteRowSideFullHecke.Kleiman2.pnIdx 0) (IndefiniteRowSideFullHecke.Kleiman2.pnField F 0) (IndefiniteRowSideFullHecke.Kleiman2.pnPt F 0) () 0 (1 / 2) 2 1 1 1
    (isStepData_dimZero F)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

