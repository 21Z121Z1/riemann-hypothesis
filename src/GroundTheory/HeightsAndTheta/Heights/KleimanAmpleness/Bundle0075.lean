import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0053
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ChartRingOverOneBlockEqChartRing
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0073
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Fintype
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0055
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0018
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0068
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0062
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PChartSecGen
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0052
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0010
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0054
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0057
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsAmpleBaseLocalizationEq

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsScalarMulMemChartRingOver
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver)

section GenericFibre

variable {S : Type} [CommRing S] {F : Type} [Field F] [Algebra S F] {Ω : Type} [Field Ω] [Algebra S Ω]
  [Algebra F Ω] [IsScalarTower S F Ω]

theorem exists_scalar_mul_mem_chartRingOver [IsDomain S] [IsFractionRing S F] {N : ℕ} (x : Fin (N + 1) → Ω)
    (c : Unit → Fin (N + 1)) {b : Ω} (hb : b ∈ chartRingOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) c) :
    ∃ s : S, algebraMap S Ω s ≠ 0 ∧ algebraMap S Ω s * b ∈ chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) c := by
  induction hb using Algebra.adjoin_induction with
  | mem u hu => exact ⟨1, by simp, by rw [map_one, one_mul]; exact Algebra.subset_adjoin hu⟩
  | algebraMap f =>
    obtain ⟨a, t, ht, rfl⟩ := IsFractionRing.div_surjective (A := S) f
    have ht' : algebraMap S F t ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors ht
    have hte : algebraMap S Ω t = algebraMap F Ω (algebraMap S F t) := IsScalarTower.algebraMap_apply S F Ω t
    have htΩ : algebraMap S Ω t ≠ 0 := by
      rw [hte]
      exact (map_ne_zero (algebraMap F Ω)).mpr ht'
    refine ⟨t, htΩ, ?_⟩
    have e : algebraMap S Ω t * algebraMap F Ω (algebraMap S F a / algebraMap S F t) = algebraMap S Ω a := by
      rw [map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
        mul_div_cancel₀ _ htΩ]
    rw [e]
    exact Subalgebra.algebraMap_mem _ a
  | add u v _ _ hu hv =>
    obtain ⟨s, hs, hsu⟩ := hu
    obtain ⟨t, ht, htv⟩ := hv
    refine ⟨s * t, by rw [map_mul]; exact mul_ne_zero hs ht, ?_⟩
    have e : algebraMap S Ω (s * t) * (u + v) =
        algebraMap S Ω t * (algebraMap S Ω s * u) + algebraMap S Ω s * (algebraMap S Ω t * v) := by
      rw [map_mul]; ring
    rw [e]
    exact add_mem (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ t) hsu)
      (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ s) htv)
  | mul u v _ _ hu hv =>
    obtain ⟨s, hs, hsu⟩ := hu
    obtain ⟨t, ht, htv⟩ := hv
    refine ⟨s * t, by rw [map_mul]; exact mul_ne_zero hs ht, ?_⟩
    have e : algebraMap S Ω (s * t) * (u * v) = (algebraMap S Ω s * u) * (algebraMap S Ω t * v) := by
      rw [map_mul]; ring
    rw [e]
    exact Subalgebra.mul_mem _ hsu htv

end GenericFibre

theorem GenericFibreScalars.full : GenericFibreScalars.Statement := by
  intro S _ _ F _ _ Ω _ _ _ _ _ N N' x x' _ _ _ hsame i hi b hb
  set C : Subalgebra F Ω := chartRingOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) (fun _ => i) with hCdef
  have hbC : b ∈ C := by
    refine mem_of_forall_mem_locIn C fun m hm => ?_
    have := hm.isPrime
    have hCm : ∀ u ∈ C, u ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn C m := fun u hu =>
      (mem_locIn (A := C) (p := m)).mpr ⟨⟨u, hu⟩, 1, one_not_mem_of_prime hm.isPrime, by simp⟩
    have hpt : IndefiniteRowSideFullHecke.Kleiman2.locIn C m ∈ IndefiniteRowSideFullHecke.Kleiman2.modelPts F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) :=
      ⟨fun _ => i, fun _ => hi, m, hm.isPrime, rfl⟩
    rw [← hsame] at hpt
    obtain ⟨c', hc', p', hp', hz⟩ := hpt
    have := hp'
    have hj : x' (c' ()) ≠ 0 := hc' ()
    have hbP := mem_pairRing_of_mem_domRing (S := S) hj hi hb
    clear hb
    induction hbP using Algebra.adjoin_induction with
    | mem u hu =>
      rcases hu with ⟨a, rfl⟩ | ⟨a, rfl⟩
      · rw [hz]
        have ha : x' a / x' (c' ()) ∈ chartRingOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') c' :=
          Algebra.subset_adjoin ⟨⟨(), a⟩, rfl⟩
        exact (mem_locIn (A := chartRingOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') c') (p := p')).mpr
          ⟨⟨_, ha⟩, 1, one_not_mem_of_prime hp', by simp⟩
      · exact hCm _ (Algebra.subset_adjoin ⟨⟨(), a⟩, rfl⟩)
    | algebraMap r =>
      rw [IsScalarTower.algebraMap_apply S F Ω]
      exact hCm _ (Subalgebra.algebraMap_mem _ _)
    | add u v _ _ hu hv => exact add_mem hu hv
    | mul u v _ _ hu hv => exact mul_mem hu hv
  obtain ⟨s, hs, hsb⟩ := exists_scalar_mul_mem_chartRingOver (S := S) x (fun _ => i) hbC
  rw [chartRingOver_oneBlock_eq_chartRing x (fun _ => i) hi] at hsb
  exact ⟨s, hs, hsb⟩

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsFurtherAlt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver mIdealOver cechHc quotPart)

def ModelCechTwist.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ)
    (e : ι k₀ ≃ Fin (N + 1)),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ → ∀ (β : K → ℤ)
      (Q : Kleiman.LineBundle F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)),
      (∀ c : ℤ, (Q.twist (Kleiman.twistSys F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) c)).secs =
          secOver F y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀)) →
      ∀ (p b : ℕ) (m c : ℤ) (i : ℕ),
        Nonempty ((((Kleiman.twistMul Q.toSubSystem p m).pow b).twist
            (Kleiman.twistSys F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) c)).H i ≃ₗ[F]
          cechHc ι (quotPart F (mIdealOver F y)) (b • IndefiniteRowSideFullHecke.Kleiman2.stepL k₀ β p m + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) i)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsFurtherBis
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver)

def ModelChangeNef.Statement : Prop :=
  ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω] (N : ℕ)
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (y : (Σ k, ι k) → Ω) (k₀ : K) (e : ι k₀ ≃ Fin (N + 1))
    (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (y' : (Σ k, ι' k) → Ω) (k₀' : K') (e' : ι' k₀' ≃ Fin (N + 1)),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ → IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y' k₀' →
    IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm = IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k₀' ∘ e'.symm →
    ∀ (β : K → ℤ) (β' : K' → ℤ),
      (∀ c : ℤ, secOver F y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) =
          secOver F y' (β' + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀')) →
      (IndefiniteRowSideFullHecke.Kleiman2.IsNef F y β ↔ IndefiniteRowSideFullHecke.Kleiman2.IsNef F y' β')

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsFurtherTail
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver mIdealOver)

def ModelMulSecs.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1)),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ → ∀ (β : K → ℤ)
      (Q : Kleiman.LineBundle F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)),
      (∀ c : ℤ, (Q.twist (Kleiman.twistSys F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) c)).secs =
          secOver F y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀)) →
      ∀ (p : ℕ) (j : ℤ), (Kleiman.twistMul Q.toSubSystem p j).secs =
        secOver F y (p • β + j • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsLastFurther
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver)

def TensorRealises.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1)),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ →
    ∀ (L L' : Kleiman.LineBundle F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) (β β' : K → ℤ),
      BundleRealises y k₀ L β → BundleRealises y k₀ L' β' → BundleRealises y k₀ (L.tensor L') (β + β')

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsSideBis
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

def RowLocCover.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ)
    (e : ι k₀ ≃ Fin (N + 1)),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ → ∀ (γ : K → ℤ)
      (J : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)),
      ∃ (m : ℕ) (f u : Fin m → Ω),
        (∀ l, f l ∈ Kleiman.chartRing F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) J) ∧
        (∀ l, u l ∈ Kleiman.chartRing F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) J) ∧
        ∑ l, u l * f l = 1 ∧
        ∀ l, ∃ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) ∧
          (∀ I : ∀ k, Finset (ι k), (∀ k, (I k).Nonempty) → ¬ CellMeets y I →
            cellLocSys (fun I => cellSec F y γ (baseCell k₀ e J.1 I)) (f l) I = ⊥) ∧
          (∀ I I' : ∀ k, Finset (ι k), (∀ k, (I k).Nonempty) → (∀ k, I k ⊆ I' k) → CellMeets y I' →
            cellLocSys (fun I => cellSec F y γ (baseCell k₀ e J.1 I)) (f l) I ≤
              cellLocSys (fun I => cellSec F y γ (baseCell k₀ e J.1 I)) (f l) I') ∧
          (∀ I : ∀ k, Finset (ι k), (∀ k, (I k).Nonempty) → ∀ k,
            cellLocSys (fun I => cellSec F y γ (baseCell k₀ e J.1 I)) (f l)
                (Function.update I k (insert (c k) (I k))) =
              cellLocSys (fun I => cellSec F y γ (baseCell k₀ e J.1 I)) (f l) I)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTail
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver GeneratesOver)

theorem ModelGenerated.proof : ModelGenerated.Statement := by
  classical
  intro F _ K _ _ ι _ Ω _ _ y k₀ hy β
  obtain ⟨i₀, -⟩ := hy.1 k₀
  have hcard : 0 < Fintype.card (ι k₀) := Fintype.card_pos_iff.mpr ⟨i₀⟩
  obtain ⟨N, hN⟩ : ∃ N, Fintype.card (ι k₀) = N + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hcard).symm⟩
  let e : ι k₀ ≃ Fin (N + 1) := (Fintype.equivFin _).trans (finCongr hN)
  set x := IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm with hx
  obtain ⟨Q, hQ⟩ := BundleOfDeg.full F K ι Ω y k₀ N e hy β
  obtain ⟨c₀, hc₀⟩ := Kleiman.Generated.full.{0, 0} F Ω N x Q
  refine ⟨c₀, fun c hc => ?_⟩
  set δ := β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀ with hδ
  set L := Q.tensor (Kleiman.twistBundle F x c) with hL
  have hLsys : L.toSubSystem = Q.toSubSystem.twist (Kleiman.twistSys F x c) := rfl
  have hgen : L.toSubSystem.Generated := by rw [hLsys]; exact hc₀ c hc
  have hsecs : L.toSubSystem.secs = secOver F y δ := by rw [hLsys, hQ c]

  have hgam : ∀ m : ℤ, L.toSubSystem.gam m = secOver F y (δ + m • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) := by
    intro m
    rw [Kleiman.SubSystem.gam, hLsys, Kleiman.SubSystem.twist_assoc, Kleiman.twistSys_twist_twistSys, hQ (c + m),
      hδ, add_smul, add_assoc]

  have hsub : ∀ I : Kleiman.Chart x, (L.sub I : Set Ω) = chartSecOver F y k₀ e δ I := by
    intro I
    ext t
    rw [SetLike.mem_coe, mem_sub_iff_gam]
    refine exists_congr fun n => ?_
    rw [hgam]

  have hfg : ∀ I : Kleiman.Chart x, ∃ G : Finset Ω, Submodule.span (Kleiman.chartRing F x I) (G : Set Ω) = L.sub I :=
    fun I => L.fg I
  choose G hG using hfg
  have hfin : ∀ (I : Kleiman.Chart x) (g : Ω), ∃ T : Finset Ω, (T : Set Ω) ⊆ L.toSubSystem.secs ∧
      (g ∈ L.sub I → g ∈ Submodule.span (Kleiman.chartRing F x I) (T : Set Ω)) := by
    intro I g
    by_cases hg : g ∈ L.sub I
    · rw [← hgen I] at hg
      obtain ⟨T, hT, hgT⟩ := Submodule.mem_span_finite_of_mem_span hg
      exact ⟨T, hT, fun _ => hgT⟩
    · exact ⟨∅, by simp, fun h => absurd h hg⟩
  choose T hTsec hTspan using hfin
  let U : Finset Ω := Finset.univ.biUnion fun I => (G I).biUnion fun g => T I g
  have hU : (U : Set Ω) ⊆ L.toSubSystem.secs := by
    intro s hs
    simp only [U, Finset.coe_biUnion, Finset.coe_univ, Set.mem_univ, Set.iUnion_true, Set.mem_iUnion,
      Finset.mem_coe] at hs
    obtain ⟨I, g, -, hs⟩ := hs
    exact hTsec I g hs
  have hspanU : ∀ I : Kleiman.Chart x, Submodule.span (Kleiman.chartRing F x I) (U : Set Ω) = L.sub I := by
    intro I
    apply le_antisymm
    · rw [← hgen I]
      exact Submodule.span_mono hU
    · rw [← hG I, Submodule.span_le]
      intro g hg
      have hgI : g ∈ L.sub I := by rw [← hG I]; exact Submodule.subset_span hg
      refine Submodule.span_mono ?_ (hTspan I g hgI)
      intro s hs
      simp only [U, Finset.coe_biUnion, Finset.coe_univ, Set.mem_univ, Set.iUnion_true, Set.mem_iUnion,
        Finset.mem_coe]
      exact ⟨I, g, hg, hs⟩
  let η : Fin U.card → Ω := fun j => (U.equivFin.symm j : Ω)
  have hrange : Set.range η = (U : Set Ω) := by
    ext s
    constructor
    · rintro ⟨j, rfl⟩
      exact (U.equivFin.symm j).2
    · intro hs
      exact ⟨U.equivFin ⟨s, hs⟩, by simp [η]⟩
  have hη : ∀ j, η j ∈ secOver F y δ := fun j => hsecs ▸ hU (hrange ▸ Set.mem_range_self j)
  refine ⟨U.card, η, hη, ?_⟩
  refine (ChartSecGen.full F K ι Ω y k₀ N e hy δ U.card η hη).mpr fun I => ?_
  rw [hrange, hspanU I, hsub I]

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTerTail
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver mIdealOver)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)

def CurveNumModel.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1))
    (x : Fin (N + 1) → Ω), x = IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm → IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ →
      ∀ (Q : Kleiman.LineBundle F x) (β : K → ℤ), BundleRealises y k₀ Q β →
      ∀ W : Ideal (NumbersDVR.MRing ι F), NumbersDVR.IsMultiProjPrime W → mIdealOver F y ≤ W →
        relDim W = ((1 : ℕ) : WithBot (WithTop ℤ)) →
        NumbersDVR.intNum F W ![β] =
          Kleiman.interNum (W.comap (rename fun a : Fin (N + 1) => (⟨k₀, e.symm a⟩ : Σ k, ι k))) ![Q.toSubSystem]

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PModelWithBaseLoc
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2 (locIn modelPts)

section Local

variable {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω]

theorem not_mem_of_inv_mem_locIn (A : Subalgebra S Ω) (p : Ideal A) (hp : p.IsPrime) (b : A)
    (hb0 : (b : Ω) ≠ 0) (hb : (b : Ω)⁻¹ ∈ locIn A p) : b ∉ p := by
  have := hp
  obtain ⟨a, s, hs, e⟩ := (mem_locIn_iff A p _).mp hb
  intro hbp
  have hs0 : (s : Ω) ≠ 0 := fun h => hs (by rw [show s = 0 from Subtype.ext h]; exact p.zero_mem)
  have : s = a * b := Subtype.ext (by
    push_cast
    field_simp at e
    linear_combination e)
  exact hs (this ▸ p.mul_mem_left a hbp)

end Local

section Loc

variable {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω]
  {S' : Type} [CommRing S'] [Algebra S S'] [Algebra S' Ω] [IsScalarTower S S' Ω]
  (M : Submonoid S) [IsLocalization M S']

theorem algebraMap_mem_units {m : S} (hm : m ∈ M) (A' : Subalgebra S' Ω) :
    algebraMap S Ω m ≠ 0 ∧ algebraMap S Ω m ∈ A' ∧ (algebraMap S Ω m)⁻¹ ∈ A' := by
  obtain ⟨u, hu⟩ := IsLocalization.map_units S' (⟨m, hm⟩ : M)
  have hu' : (u : S') = algebraMap S S' m := hu
  have e : algebraMap S Ω m = algebraMap S' Ω u := by
    rw [IsScalarTower.algebraMap_apply S S' Ω, ← hu']
  have h1 : algebraMap S' Ω u * algebraMap S' Ω ↑u⁻¹ = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have hne : algebraMap S Ω m ≠ 0 := fun h => by
    rw [e] at h; rw [h, zero_mul] at h1; exact zero_ne_one h1
  refine ⟨hne, e ▸ Subalgebra.algebraMap_mem _ _, ?_⟩
  rw [e, inv_eq_of_mul_eq_one_right h1]
  exact Subalgebra.algebraMap_mem _ _

theorem algebraMap_not_mem_prime {m : S} (hm : m ∈ M) (A' : Subalgebra S' Ω) (p' : Ideal A')
    (hp' : p'.IsPrime) : (⟨algebraMap S Ω m, (algebraMap_mem_units M hm A').2.1⟩ : A') ∉ p' := by
  intro h
  obtain ⟨hne, hmem, hinv⟩ := algebraMap_mem_units M hm A'
  have h' := p'.mul_mem_left (⟨_, hinv⟩ : A') h
  rw [show (⟨_, hinv⟩ : A') * ⟨_, hmem⟩ = 1 from Subtype.ext (by simp [inv_mul_cancel₀ hne])] at h'
  exact hp'.ne_top ((Ideal.eq_top_iff_one _).mpr h')

def inclHom (A : Subalgebra S Ω) (A' : Subalgebra S' Ω) (hle : ∀ a ∈ A, a ∈ A') : A →+* A' where
  toFun a := ⟨a, hle a a.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem locIn_comap_inclHom (A : Subalgebra S Ω) (A' : Subalgebra S' Ω) (hle : ∀ a ∈ A, a ∈ A')
    (hden : ∀ a ∈ A', ∃ m ∈ M, algebraMap S Ω m * a ∈ A) (p' : Ideal A') (hp' : p'.IsPrime) :
    locIn A' p' = locIn A (p'.comap (inclHom A A' hle)) := by
  apply le_antisymm
  · refine Subring.closure_le.mpr ?_
    rintro u ⟨a', b', hb', rfl⟩
    obtain ⟨m₁, hm₁, h₁⟩ := hden a' a'.2
    obtain ⟨m₂, hm₂, h₂⟩ := hden b' b'.2
    have n₁ := (algebraMap_mem_units M hm₁ A').1
    have n₂ := (algebraMap_mem_units M hm₂ A').1
    have nb : (b' : Ω) ≠ 0 := fun h => hb' (by rw [show b' = 0 from Subtype.ext h]; exact p'.zero_mem)
    refine Subring.subset_closure ⟨⟨_, mul_mem (Subalgebra.algebraMap_mem A m₂) h₁⟩,
      ⟨_, mul_mem (Subalgebra.algebraMap_mem A m₁) h₂⟩, ?_, ?_⟩
    · rw [Ideal.mem_comap]
      intro h
      have e : inclHom A A' hle ⟨_, mul_mem (Subalgebra.algebraMap_mem A m₁) h₂⟩ =
          ⟨algebraMap S Ω m₁, (algebraMap_mem_units M hm₁ A').2.1⟩ *
            (⟨algebraMap S Ω m₂, (algebraMap_mem_units M hm₂ A').2.1⟩ * b') := Subtype.ext rfl
      rw [e] at h
      rcases hp'.mem_or_mem h with h | h
      · exact algebraMap_not_mem_prime M hm₁ A' p' hp' h
      rcases hp'.mem_or_mem h with h | h
      · exact algebraMap_not_mem_prime M hm₂ A' p' hp' h
      · exact hb' h
    · show (a' : Ω) / b' = algebraMap S Ω m₂ * (algebraMap S Ω m₁ * a') /
        (algebraMap S Ω m₁ * (algebraMap S Ω m₂ * b'))
      field_simp
  · refine Subring.closure_le.mpr ?_
    rintro u ⟨a, b, hb, rfl⟩
    exact Subring.subset_closure ⟨inclHom A A' hle a, inclHom A A' hle b, hb, rfl⟩

theorem isLocalization_inclHom (A : Subalgebra S Ω) (A' : Subalgebra S' Ω) (hle : ∀ a ∈ A, a ∈ A')
    (hden : ∀ a ∈ A', ∃ m ∈ M, algebraMap S Ω m * a ∈ A) :
    letI := (inclHom A A' hle).toAlgebra
    IsLocalization (M.map (algebraMap S A)) A' := by
  let _ := (inclHom A A' hle).toAlgebra
  refine (isLocalization_iff _ _).mpr ⟨?_, ?_, ?_⟩
  · rintro ⟨_, m, hm, rfl⟩
    obtain ⟨hne, hmem, hinv⟩ := algebraMap_mem_units M hm A'
    refine IsUnit.of_mul_eq_one ⟨_, hinv⟩ (Subtype.ext ?_)
    show algebraMap S Ω m * (algebraMap S Ω m)⁻¹ = 1
    exact mul_inv_cancel₀ hne
  · intro z
    obtain ⟨m, hm, h⟩ := hden z z.2
    refine ⟨(⟨_, h⟩, ⟨algebraMap S A m, Submonoid.mem_map_of_mem _ hm⟩), Subtype.ext ?_⟩
    show (z : Ω) * algebraMap S Ω m = algebraMap S Ω m * z
    ring
  · intro x y hxy
    refine ⟨1, ?_⟩
    have h' : ((algebraMap A A' x : A') : Ω) = (algebraMap A A' y : A') := congrArg Subtype.val hxy
    rw [show x = y from Subtype.ext h']

variable {K : Type} {ι : K → Type}

theorem chartRingOver_le (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) :
    ∀ a ∈ chartRingOver S y c, a ∈ chartRingOver S' y c := by
  have hle : chartRingOver S y c ≤ (chartRingOver S' y c).restrictScalars S :=
    Algebra.adjoin_le fun x hx => (Algebra.subset_adjoin hx : x ∈ Algebra.adjoin S' _)
  exact fun a ha => hle ha

theorem modelPts_localization (y : (Σ k, ι k) → Ω) :
    modelPts S' y = {z | z ∈ modelPts S y ∧ ∀ m ∈ M, (algebraMap S Ω m)⁻¹ ∈ z} := by
  ext z
  have hden : ∀ c, ∀ a ∈ chartRingOver S' y c, ∃ m ∈ M, algebraMap S Ω m * a ∈ chartRingOver S y c :=
    fun c a ha => exists_mul_mem_adjoin_of_isLocalization (S' := S') M _ ha
  constructor
  · rintro ⟨c, hc, p', hp', rfl⟩
    refine ⟨⟨c, hc, p'.comap (inclHom _ _ (chartRingOver_le (S := S) (S' := S') y c)), by have := hp'; infer_instance,
      locIn_comap_inclHom M _ _ _ (hden c) p' hp'⟩, fun m hm => ?_⟩
    obtain ⟨hne, hmem, hinv⟩ := algebraMap_mem_units M hm (chartRingOver S' y c)
    exact Subring.subset_closure ⟨1, ⟨_, hmem⟩, algebraMap_not_mem_prime M hm _ p' hp', by simp⟩
  · rintro ⟨⟨c, hc, p, hp, rfl⟩, hM⟩
    let _ := (inclHom _ _ (chartRingOver_le (S := S) (S' := S') y c)).toAlgebra
    have := isLocalization_inclHom M _ _ (chartRingOver_le (S := S) (S' := S') y c) (hden c)
    have hd : Disjoint ((M.map (algebraMap S (chartRingOver S y c)) : Submonoid (chartRingOver S y c)) :
        Set (chartRingOver S y c)) (p : Set (chartRingOver S y c)) := by
      rw [Set.disjoint_left]
      rintro _ ⟨m, hm, rfl⟩ hmp
      exact not_mem_of_inv_mem_locIn _ p hp _ (algebraMap_mem_units M hm (chartRingOver S' y c)).1
        (hM m hm) hmp
    have hp' := IsLocalization.isPrime_of_isPrime_disjoint
      (M.map (algebraMap S (chartRingOver S y c))) (chartRingOver S' y c) p hp hd
    refine ⟨c, hc, _, hp', ?_⟩
    rw [locIn_comap_inclHom M _ _ _ (hden c) _ hp']
    congr 1
    exact (IsLocalization.under_map_of_isPrime_disjoint
      (M.map (algebraMap S (chartRingOver S y c))) (chartRingOver S' y c) hp hd).symm

end Loc

theorem ModelWithBaseLocalization.proof : ModelWithBaseLocalization.Statement := by
  intro S _ K ι Ω _ _ y k₀ S' _ _ _ _ M _ h
  refine ⟨h.1, ?_⟩
  have e : modelPts S y = modelPts S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀)) := h.2
  show modelPts S' y = modelPts S' (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀))
  rw [modelPts_localization M y, modelPts_localization M (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀)), e]

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end
end

