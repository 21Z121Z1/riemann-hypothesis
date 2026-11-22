import Mathlib
import Development.AbelianVarietyTheory.Definitions.UpperBounds.CountAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldBStatementHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0004
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0003
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0063
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0040
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0014
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FourierJacobiCoeffLinearBoundedSections
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.LintegralNormLtTop
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Imports

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FinrankDomainSpanLeBinomial
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares GlobalTheory.UpTie
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.UpTie

theorem exists_bddSec_of_mem_domSpan {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (la : Wt X.Ψ r) {g : Frame X.Ψ r → ℂ} (hg : g ∈ domSpan X (X.SS la)) :
    ∃ f, X.IsBddSec la f ∧ g = X.dom.indicator f := by
  obtain ⟨n, u, v, rfl⟩ := Submodule.mem_span_set'.1 hg
  choose f hf hv using fun i => (v i).2
  refine ⟨_, GlobalTheory.UpperModel.isBddSec_sum X (fun i => (hf i).1) u, ?_⟩
  funext x
  simp only [← hv, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hx : x ∈ X.dom <;> simp [hx]

theorem finrank_domSpan_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa), FiniteDimensional ℂ (domSpan X (X.SS (Xa.Fp + Xa.T • Xa.L))) ∧ Module.finrank ℂ (domSpan X (X.SS (Xa.Fp + Xa.T • Xa.L))) ≤ Fl.δ * (Xa.T + 2 * nd X + 6).choose (nd X) := by
  intro E _ _ _ r X Xa Fl
  have hr : Module.rank ℂ (domSpan X (X.SS (Xa.Fp + Xa.T • Xa.L))) ≤
      ((Fl.δ * (Xa.T + 2 * nd X + 6).choose (nd X) : ℕ) : Cardinal) := by
    refine rank_le fun s hs => ?_
    have hs' := (hs.map' _ (Submodule.ker_subtype _)).comp s.equivFin.symm s.equivFin.symm.injective
    choose f hf hfe using fun q : Fin s.card =>
      exists_bddSec_of_mem_domSpan X _ (s.equivFin.symm q).1.2
    refine GlobalTheory.UpperModel.upper E r X Xa Fl s.card f hf fun u hu => ?_
    funext q
    refine Fintype.linearIndependent_iff.1 hs' u ?_ q
    funext x
    simp only [Function.comp, Submodule.subtype_apply, hfe, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply]
    by_cases hx : x ∈ X.dom
    · simpa [hx] using hu x hx
    · simp [hx]
  exact ⟨Module.rank_lt_aleph0_iff.1 (hr.trans_lt (Cardinal.natCast_lt_aleph0)), Module.finrank_le_of_rank_le hr⟩

end GlobalTheory.UpTie
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.IndicatorMemSSAndDomSpan
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares GlobalTheory.UpTie
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.UpTie

theorem mem_domSpan_iff_of_closed {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (A : Set (Frame X.Ψ r → ℂ)) (h0 : 0 ∈ A) (hadd : ∀ P ∈ A, ∀ Q ∈ A, P + Q ∈ A)
    (hsmul : ∀ (a : ℂ), ∀ P ∈ A, a • P ∈ A) (hind : ∀ f ∈ A, X.dom.indicator f ∈ A) (g : Frame X.Ψ r → ℂ) :
    g ∈ domSpan X A ↔ g ∈ A ∧ ∀ x ∉ X.dom, g x = 0 := by
  constructor
  · intro hg
    unfold domSpan at hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨f, hf, rfl⟩ := hg
      exact ⟨hind f hf, fun x hx => Set.indicator_of_notMem hx _⟩
    | zero => exact ⟨h0, fun _ _ => rfl⟩
    | add P Q _ _ hP hQ =>
      exact ⟨hadd _ hP.1 _ hQ.1, fun x hx => by rw [Pi.add_apply, hP.2 x hx, hQ.2 x hx, add_zero]⟩
    | smul a P _ hP =>
      exact ⟨hsmul a _ hP.1, fun x hx => by rw [Pi.smul_apply, hP.2 x hx, smul_zero]⟩
  · rintro ⟨hg, hz⟩
    refine Submodule.subset_span ⟨g, hg, ?_⟩
    funext x
    by_cases hx : x ∈ X.dom
    · exact Set.indicator_of_mem hx _
    · exact (Set.indicator_of_notMem hx _).trans (hz x hx).symm

theorem indicator_mem_SS_and_domSpan : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (c : ℝ), (∀ f ∈ X.SS la, X.dom.indicator f ∈ X.SS la) ∧ (∀ f ∈ X.SSgt la c, X.dom.indicator f ∈ X.SSgt la c) ∧ (∀ g, g ∈ domSpan X (X.SS la) ↔ g ∈ X.SS la ∧ ∀ x ∉ X.dom, g x = 0) ∧ (∀ g, g ∈ domSpan X (X.SSgt la c) ↔ g ∈ X.SSgt la c ∧ ∀ x ∉ X.dom, g x = 0) := by
  intro E _ _ _ r X la c
  have h1 : ∀ f ∈ X.SS la, X.dom.indicator f ∈ X.SS la := fun f hf =>
    (GlobalTheory.DomCongr.bddSec_cusp_congr E r X la f _ (fun x hx => (Set.indicator_of_mem hx _).symm)).2 hf
  have h2 : ∀ f ∈ X.SSgt la c, X.dom.indicator f ∈ X.SSgt la c := by
    intro f hf
    refine ⟨h1 f hf.1, fun ξ hξ ν hν x hx => ?_⟩
    have e := GlobalTheory.fj_eq_sum_of_eqOn_dom E r X la 1 (fun _ => 1) (fun _ => f) (X.dom.indicator f)
      (fun _ => hf.1.1) (fun y hy => by simp [Set.indicator_of_mem hy]) ξ hξ ν x hx
    rw [e]
    simp [hf.2 ξ hξ ν hν x hx]
  obtain ⟨⟨a0, a1, a2⟩, -, ⟨b0, b1, b2⟩, -⟩ := siegelSpaceAlgebra_holds (E := E) r X la la c
  exact ⟨h1, h2, mem_domSpan_iff_of_closed X _ a0 a1 a2 h1, mem_domSpan_iff_of_closed X _ b0 b1 b2 h2⟩

end GlobalTheory.UpTie
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.JetInj
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares GlobalTheory.UpTie
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.UpTie

theorem jetInj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r)
    (Xa : ArchInM X) (Fl : FlatM X Xa), JetInj X Xa Fl := by
  intro E _ _ _ r X Xa Fl f hf hV
  have hb : X.IsBddSec (Xa.Fp + Xa.T • Xa.L) f := hf.1
  exact GlobalTheory.HighOrderVanishing.eq_zero E r X Xa Fl f hb
    (GlobalTheory.isBigO_of_vanS E r X Xa Fl _ f hb.1.1 hV)

end GlobalTheory.UpTie
end

