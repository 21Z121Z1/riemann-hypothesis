import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0023
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IsMulRightInvariantOfLattice
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.AlTiePl
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RowFrameCoherence
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0022
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocModel

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.HaarPushforward
section
noncomputable section

open MeasureTheory Topology NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.KappaOffDiagonal Formalism.L2.SG.TermOp.Vanish Formalism.L2.SG.CovariantRepresentation

namespace Formalism.L2.SG.HaarPushforward

section Core

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G]

theorem pushHaar (R : Subgroup G) (hR : IsClosed (R : Set G)) :
    ∃ ν : Measure G, SigmaFinite ν ∧ ν ≠ 0 ∧ ν (R : Set G)ᶜ = 0 ∧ (∀ K : Set G, IsCompact K → ν K < ⊤) ∧
      (∀ r ∈ R, ν.map (fun x => r * x) = ν) := by
  have hce : IsClosedEmbedding (Subtype.val : R → G) := hR.isClosedEmbedding_subtypeVal
  haveI : LocallyCompactSpace R := hce.locallyCompactSpace
  haveI : BorelSpace R := Subtype.borelSpace _
  haveI : SecondCountableTopology R := TopologicalSpace.Subtype.secondCountableTopology (R : Set G)
  let μ : Measure R := Measure.haar
  haveI : SigmaFinite μ := sigmaFinite_of_locallyFinite
  have hemb : MeasurableEmbedding (Subtype.val : R → G) := MeasurableEmbedding.subtype_coe hR.measurableSet
  refine ⟨μ.map Subtype.val, hemb.sigmaFinite_map, ?_, ?_, ?_, ?_⟩
  · intro h
    rw [Measure.map_eq_zero_iff hemb.measurable.aemeasurable] at h
    exact (NeZero.ne μ) h
  · rw [hemb.map_apply]
    have e : (Subtype.val ⁻¹' ((R : Set G)ᶜ) : Set R) = ∅ := by
      ext x
      exact ⟨fun hx => (hx x.2).elim, fun h => h.elim⟩
    rw [e, measure_empty]
  · intro K hK
    rw [hemb.map_apply]
    exact (hce.isCompact_preimage hK).measure_lt_top
  · intro r hr
    have hm : Measurable (fun x : G => r * x) := (continuous_const.mul continuous_id).measurable
    have hm' : Measurable (fun y : R => (⟨r, hr⟩ : R) * y) := (continuous_const.mul continuous_id).measurable
    rw [Measure.map_map hm hemb.measurable]
    have e : (fun x : G => r * x) ∘ Subtype.val = Subtype.val ∘ (fun y : R => (⟨r, hr⟩ : R) * y) := rfl
    rw [e, ← Measure.map_map hemb.measurable hm', map_mul_left_eq_self]

theorem pushHaar_inv (R Γ : Subgroup G) [Countable Γ] [DiscreteTopology Γ] (hR : IsClosed (R : Set G)) (hΓ : Γ ≤ R)
    (hcov : ∃ K : Set G, IsCompact K ∧ ∀ r ∈ R, ∃ s ∈ Γ, s * r ∈ K) :
    ∃ ν : Measure G, SigmaFinite ν ∧ ν ≠ 0 ∧ ν (R : Set G)ᶜ = 0 ∧ (∀ K : Set G, IsCompact K → ν K < ⊤) ∧
      (∀ r ∈ R, ν.map (fun x => r * x) = ν) ∧ ν.map (fun x => x⁻¹) = ν := by
  have hce : IsClosedEmbedding (Subtype.val : R → G) := hR.isClosedEmbedding_subtypeVal
  haveI : LocallyCompactSpace R := hce.locallyCompactSpace
  haveI : BorelSpace R := Subtype.borelSpace _
  haveI : SecondCountableTopology R := TopologicalSpace.Subtype.secondCountableTopology (R : Set G)
  let μ : Measure R := Measure.haar
  haveI : SigmaFinite μ := sigmaFinite_of_locallyFinite
  have hemb : MeasurableEmbedding (Subtype.val : R → G) := MeasurableEmbedding.subtype_coe hR.measurableSet
  let Γ' : Subgroup R := Γ.subgroupOf R
  let ι : Γ' → Γ := fun x => ⟨x.1.1, Subgroup.mem_subgroupOf.1 x.2⟩
  have hι : Function.Injective ι := by
    intro a b e
    simp only [ι, Subtype.mk.injEq] at e
    exact Subtype.ext (Subtype.ext e)
  haveI : Countable Γ' := hι.countable
  haveI : DiscreteTopology Γ' :=
    DiscreteTopology.of_continuous_injective
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _) hι
  obtain ⟨K, hK, hKc⟩ := hcov
  have hinv : μ.map (fun x => x⁻¹) = μ :=
    haar_map_inv_of_lattice μ Γ' (hce.isCompact_preimage hK) (fun x => by
      obtain ⟨s, hs, hsK⟩ := hKc x.1 x.2
      exact ⟨⟨s, hΓ hs⟩, Subgroup.mem_subgroupOf.2 hs, hsK⟩)
  refine ⟨μ.map Subtype.val, hemb.sigmaFinite_map, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    rw [Measure.map_eq_zero_iff hemb.measurable.aemeasurable] at h
    exact (NeZero.ne μ) h
  · rw [hemb.map_apply]
    have e : (Subtype.val ⁻¹' ((R : Set G)ᶜ) : Set R) = ∅ := by
      ext x
      exact ⟨fun hx => (hx x.2).elim, fun h => h.elim⟩
    rw [e, measure_empty]
  · intro K hK
    rw [hemb.map_apply]
    exact (hce.isCompact_preimage hK).measure_lt_top
  · intro r hr
    have hm : Measurable (fun x : G => r * x) := (continuous_const.mul continuous_id).measurable
    have hm' : Measurable (fun y : R => (⟨r, hr⟩ : R) * y) := (continuous_const.mul continuous_id).measurable
    rw [Measure.map_map hm hemb.measurable]
    have e : (fun x : G => r * x) ∘ Subtype.val = Subtype.val ∘ (fun y : R => (⟨r, hr⟩ : R) * y) := rfl
    rw [e, ← Measure.map_map hemb.measurable hm', map_mul_left_eq_self]
  · rw [Measure.map_map continuous_inv.measurable hemb.measurable]
    have e : (fun x : G => x⁻¹) ∘ Subtype.val = Subtype.val ∘ (fun y : R => y⁻¹) := rfl
    rw [e, ← Measure.map_map hemb.measurable continuous_inv.measurable, hinv]

end Core

variable {D : D7} {X : HidaSetting D} {u u' : D.what₂.Word}

def RConjModC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word)
    (t : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')), ∀ h ∈ pointwiseStabilizerInfinite X t.rep, ∀ ν : Measure X.B.I.Ginf,
    SigmaFinite ν → ν ≠ 0 → ν (Rset t)ᶜ = 0 → (∀ K : Set X.B.I.Ginf, IsCompact K → ν K < ⊤) →
      (∀ r ∈ Rset t, ν.map (fun x => r * x) = ν) → ν.map (fun x => x⁻¹) = ν → ν.map (fun x => h⁻¹ * x * h) = ν

theorem rHaarC_of (hN : NLamNinf) (hG : PsiInfChar) (h1 : RClosedC) (h2 : RODiscreteC) (h3 : RCocompactC)
    (hM : RConjModC) : RHaarC := by
  intro D X Y u u' t h hh
  have hΓR : ROsub X (X.Fu u) (X.Fu u') t.lam t.lam' t.lin ≤ Rsub hG t := by
    intro s hs
    have hs0 : s ∈ ROset X (X.Fu u) (X.Fu u') t.lam t.lam' t.lin := hs
    obtain ⟨z, n, hz, hzs, hn, hn'⟩ := hs0
    have hl : RatLink X (t.pt⁻¹ * z * t.pt) (t.lin⁻¹ * n * t.lin) :=
      ratLink_mul X (ratLink_mul X (ratLink_inv X t.rep.2.1) hz) t.rep.2.1
    have hs2 := hN D X u' t.lam' _ _ hl hn'
    rw [Prod.fst_mul, Prod.fst_mul, Prod.fst_inv, ← hzs] at hs2
    exact ⟨hzs ▸ hN D X u t.lam z n hz hn, hs2⟩
  haveI := ROsub_countable X (X.Fu u) (X.Fu u') t.lam t.lam' t.lin
  haveI := h2 D X Y u u' t
  obtain ⟨K, hK, hKc⟩ := h3 D X Y u u' t
  obtain ⟨ν, hs, h0, hc, hKf, hl, hi⟩ :=
    pushHaar_inv (Rsub hG t) (ROsub X (X.Fu u) (X.Fu u') t.lam t.lam' t.lin) (h1 D X Y u u' t) hΓR
      ⟨K, hK, fun r hr => hKc r hr⟩
  exact ⟨ν, hs, h0, hc, hKf, hl, hi, hM D X Y u u' t h hh ν hs h0 hc hKf hl hi⟩

end Formalism.L2.SG.HaarPushforward
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumBCut
section
noncomputable section

namespace Formalism.L2.SG.LsDatumB

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut MeasureTheory
open Classical ValuativeRel

section Cut

variable {D : Formalism.BasicNotions.D7}

def LocOrbSum (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (u u' : D.what₂.Word) : Prop :=
  ∀ w : Point D.host.E (D.R.rS + 1), Gpt (D.mem u).A.T (D.mem u').A.T w ≠ 0 →
  ∀ (p : PlF D) (τ : Option ((M p).Cls D.R.rS)),
    HasSum (fL M δ (D.mem u).A.T (D.mem u').A.T p w τ) (BBtop M δ (D.mem u).A.T (D.mem u').A.T p w τ) ∧
    Summable (fun O => ‖fL M δ (D.mem u).A.T (D.mem u').A.T p w τ O‖) ∧
    (τ ≠ none → HasSum (gL M δ (D.mem u).A.T (D.mem u').A.T p w τ)
      (BBtop M δ (D.mem u).A.T (D.mem u').A.T p w τ / Pf.autP M p τ) ∧
    Summable (fun O => ‖gL M δ (D.mem u).A.T (D.mem u').A.T p w τ O‖))

def LocUnram (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (u u' : D.what₂.Word) (θ0 : ∀ p, Option ((M p).Cls D.R.rS)) : Prop :=
  ∀ w : Point D.host.E (D.R.rS + 1), Gpt (D.mem u).A.T (D.mem u').A.T w ≠ 0 →
  ∃ S : Finset (PlF D), ∀ p ∉ S, Pf.autP M p (θ0 p) = 1 ∧
    ∀ (τ : Option ((M p).Cls D.R.rS)) (O : Set (MatP D p)),
      fL M δ (D.mem u).A.T (D.mem u').A.T p w τ O =
          (if O = x0L M δ (D.mem u).A.T (D.mem u').A.T p w ∧ τ = θ0 p then 1 else 0) ∧
      gL M δ (D.mem u).A.T (D.mem u').A.T p w τ O =
          (if O = x0L M δ (D.mem u).A.T (D.mem u').A.T p w ∧ τ = θ0 p then 1 else 0)

def ThRestricted (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) (θ0 : ∀ p, Option ((M p).Cls D.R.rS)) : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)), EligAt γ w → Pf.Restricted θ0 (thT M δ γ)

def ThSome (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)), EligAt γ w → ∀ p, thT M δ γ p ≠ none

def ScalKind (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : Prop :=
  ∀ (γ γ' : TermDef.Term D u u' F0 what₂) (w w' : Point D.host.E (D.R.rS + 1)), EligAt γ w → EligAt γ' w' →
    Corank.TermScal D γ γ' → kind w = kind w'

def EligFinite (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : Prop :=
  ∀ w : Point D.host.E (D.R.rS + 1), {γ : TermDef.Term D u u' F0 what₂ | EligAt γ w}.Finite

def AtPtG (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)), γ.atPt w →
    Gpt (D.mem u).A.T (D.mem u').A.T w ≠ 0

def PartnerTupleSum (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)), EligAt γ w →
  ∀ w' : Point D.host.E (D.R.rS + 1), Gpt (D.mem u).A.T (D.mem u').A.T w' ≠ 0 → kind w' = kind w →
    (∀ γ' : TermDef.Term D u u' F0 what₂, Corank.TermScal D γ γ' → EligAt γ' w' →
      {p | locT M δ γ' p ≠ x0L M δ (D.mem u).A.T (D.mem u').A.T p w'}.Finite) ∧
    ∀ x : Rst (fun p => x0L M δ (D.mem u).A.T (D.mem u').A.T p w'),
      HasSum (fun γ' : {γ' : TermDef.Term D u u' F0 what₂ //
          (Corank.TermScal D γ γ' ∧ EligAt γ' w') ∧ locT M δ γ' = x.1} =>
          PairVal.cAt (PairVal.vRdef D u u' F0 what₂ δ M) γ'.1 w')
        (∏ᶠ p, fL M δ (D.mem u).A.T (D.mem u').A.T p w' (thT M δ γ p) (x.1 p))

def FiberTupleSum (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (L : CntLocal.LocSp D M) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : Prop :=
  ∀ nc : ℝ, CntLocal.Formula δ L u u' F0 what₂ nc →
  ∀ ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp], (∀ p, Irreducible (ϖ p)) →
  ∀ w : Point D.host.E (D.R.rS + 1), Gpt (D.mem u).A.T (D.mem u').A.T w ≠ 0 →
  ∀ (γ₀ : TermDef.Term D u u' F0 what₂) (w₀ : Point D.host.E (D.R.rS + 1)), EligAt γ₀ w₀ → kind w = kind w₀ →
    (∀ γ : TermDef.Term D u u' F0 what₂, EligAt γ w →
      {p | locT M δ γ p ≠ x0L M δ (D.mem u).A.T (D.mem u').A.T p w}.Finite) ∧
    ∀ x : Rst (fun p => x0L M δ (D.mem u).A.T (D.mem u').A.T p w),
      HasSum (fun γ : {γ : TermDef.Term D u u' F0 what₂ //
          (EligAt γ w ∧ kind w = kind w₀ ∧ thT M δ γ = thT M δ γ₀) ∧ locT M δ γ = x.1} =>
          (PairVal.massTerm γ.1 : ℂ) * PairVal.cAt (PairVal.vRdef D u u' F0 what₂ δ M) γ.1 w)
        ((n0 nc (D.mem u).A.T (D.mem u').A.T w : ℂ) * (dnT M δ L ϖ γ₀ : ℂ) *
          ∏ᶠ p, gL M δ (D.mem u).A.T (D.mem u').A.T p w (thT M δ γ₀ p) (x.1 p))

def CoefProd (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)), EligAt γ w →
    PairVal.cAt (PairVal.vRdef D u u' F0 what₂ δ M) γ w =
      (∏ᶠ p, hL M δ (D.mem u).A.T (D.mem u').A.T p w (locT M δ γ p)) *
        ((PairVal.orbT D u u' F0 what₂ γ (zT γ)).ncard : ℂ)

def PartnerCount (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)), EligAt γ w →
  ∀ w' : Point D.host.E (D.R.rS + 1), Gpt (D.mem u).A.T (D.mem u').A.T w' ≠ 0 → kind w' = kind w →
    (∀ γ' : TermDef.Term D u u' F0 what₂, Corank.TermScal D γ γ' → EligAt γ' w' →
      {p | locT M δ γ' p ≠ x0L M δ (D.mem u).A.T (D.mem u').A.T p w'}.Finite) ∧
    ∀ x : Rst (fun p => x0L M δ (D.mem u).A.T (D.mem u').A.T p w'),
      HasSum (fun γ' : {γ' : TermDef.Term D u u' F0 what₂ //
          (Corank.TermScal D γ γ' ∧ EligAt γ' w') ∧ locT M δ γ' = x.1} =>
          ((PairVal.orbT D u u' F0 what₂ γ'.1 (zT γ'.1)).ncard : ℂ))
        (∏ᶠ p, kL M δ (D.mem u).A.T (D.mem u').A.T p w' (thT M δ γ p) (x.1 p))

def FiberCount (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (L : CntLocal.LocSp D M) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : Prop :=
  ∀ nc : ℝ, CntLocal.Formula δ L u u' F0 what₂ nc →
  ∀ ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp], (∀ p, Irreducible (ϖ p)) →
  ∀ w : Point D.host.E (D.R.rS + 1), Gpt (D.mem u).A.T (D.mem u').A.T w ≠ 0 →
  ∀ (γ₀ : TermDef.Term D u u' F0 what₂) (w₀ : Point D.host.E (D.R.rS + 1)), EligAt γ₀ w₀ → kind w = kind w₀ →
    (∀ γ : TermDef.Term D u u' F0 what₂, EligAt γ w →
      {p | locT M δ γ p ≠ x0L M δ (D.mem u).A.T (D.mem u').A.T p w}.Finite) ∧
    ∀ x : Rst (fun p => x0L M δ (D.mem u).A.T (D.mem u').A.T p w),
      HasSum (fun γ : {γ : TermDef.Term D u u' F0 what₂ //
          (EligAt γ w ∧ kind w = kind w₀ ∧ thT M δ γ = thT M δ γ₀) ∧ locT M δ γ = x.1} =>
          (PairVal.massTerm γ.1 : ℂ) * ((PairVal.orbT D u u' F0 what₂ γ.1 (zT γ.1)).ncard : ℂ))
        ((n0 nc (D.mem u).A.T (D.mem u').A.T w : ℂ) * (dnT M δ L ϖ γ₀ : ℂ) *
          ∏ᶠ p, eL M δ (D.mem u).A.T (D.mem u').A.T p w (thT M δ γ₀ p) (x.1 p))

def DnInDens (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)), EligAt γ w →
    ∃ Λ ∈ what₂, (CntLocal.EZ (CntLocal.Tn u') F0 Λ (zT γ)).Nonempty

def NormRepElig (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)), EligAt γ w →
    ∃ x : Point D.host.E (D.R.rS + 1) × LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E) × PairVal.MatR D ×
      PairVal.MatR D, PairVal.NormRep γ x.1 x.2.1 x.2.2.1 x.2.2.2

def CutAt (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (L : CntLocal.LocSp D M) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : Prop :=
  LocOrbSum M δ u u' ∧ ScalKind u u' F0 what₂ ∧
    CoefProd M δ u u' F0 what₂ ∧ PartnerCount M δ u u' F0 what₂ ∧ FiberCount M δ L u u' F0 what₂ ∧
    NormRepElig u u' F0 what₂ ∧ ThSome M δ u u' F0 what₂ ∧
    ∃ θ0 : ∀ p, Option ((M p).Cls D.R.rS), LocUnram M δ u u' θ0 ∧ ThRestricted M δ u u' F0 what₂ θ0

end Cut

end Formalism.L2.SG.LsDatumB
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGVanish
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic

namespace Formalism.L2.SG.NGVanish

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem hsEmb_eq_zero {Wq Wp : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] (A : Wq →L[ℂ] Wp)
    (h : Formalism.L2.SG.PackageTie.hsEmb A = 0) : A = 0 := by
  have hi : ∀ i, A (stdOrthonormalBasis ℂ Wq i) = 0 := by
    intro i
    have := congrArg (fun v : Formalism.L2.SG.PackageTie.HS Wq Wp => WithLp.ofLp v i) h
    simpa [Formalism.L2.SG.PackageTie.hsEmb] using this
  have hA : (A : Wq →ₗ[ℂ] Wp) = 0 :=
    (stdOrthonormalBasis ℂ Wq).toBasis.ext (fun i => by simpa using hi i)
  ext x
  simpa using congrArg (fun f : Wq →ₗ[ℂ] Wp => f x) hA

def FormNGC : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
      ∀ ν, Pinned X u u' ν → ∀ t ∈ (Y.tO u u').ngSet, (Y.tO u u').vec t ≠ 0 →
        (∃ w : Point D.host.E (D.R.rS + 1), toPts w = ptPN t ∧ ∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u' w g) ∧
        ∀ w : Point D.host.E (D.R.rS + 1), toPts w = ptPN t → (∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u' w g) →
          ∃ (c : ℂ) (A : X.Vpi u →L[ℂ] X.Vpi u) (B : X.Vpi u' →L[ℂ] X.Vpi u'),
            OOt t = c • A.comp ((haveI := FiniteDimensional.complete ℂ (X.Vpi u)
              OO (ν (Formalism.L2.SG.RealObj.gamW X u u' w)) Set.univ (X.Wu u) (X.Wu u')
                (Formalism.L2.SG.RealObj.gamW X u u' w)).comp B)

theorem stepTermVanish_of_form (h : FormNGC) : StepTermVanish := by
  intro Cg cb Cw cT CT C0
  obtain ⟨a₀, b₀, h2⟩ := h Cg cb Cw cT CT C0
  refine ⟨a₀, b₀, fun C' Cl e1 e2 D large₂ X Y u u' hc ν hν t ht hJ => ?_⟩
  by_contra hv
  obtain ⟨⟨w, hw, hrep⟩, hform⟩ := h2 C' Cl e1 e2 D large₂ X Y u u' hc ν hν t ht hv
  have hex : ∃ w' : Point D.host.E (D.R.rS + 1), toPts w' = ptPN t ∧ ∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u' w' g :=
    ⟨w, hw, hrep⟩
  unfold J2of at hJ
  rw [dif_pos hex] at hJ
  have hJw : Jw Y u u' ν hex.choose = 0 :=
    hsEmb_eq_zero _ (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hJ))
  obtain ⟨c, A, B, hO⟩ := hform hex.choose hex.choose_spec.1 hex.choose_spec.2
  have key : ∀ (k χ c : ℂ) (A : X.Vpi u →L[ℂ] X.Vpi u) (Z : X.Vpi u' →L[ℂ] X.Vpi u)
      (B : X.Vpi u' →L[ℂ] X.Vpi u'), k • Z = 0 → k • (χ • (c • A.comp (Z.comp B))) = 0 := by
    intro k χ c A Z B hZ
    have hy : ∀ y, k • Z y = 0 := fun y => by simpa using congrArg (fun T => T y) hZ
    ext x
    simp only [smul_apply, ContinuousLinearMap.comp_apply, zero_apply]
    rw [smul_comm k χ, smul_comm k c, ← map_smul A k, hy]
    simp
  have hamp : ampN (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') t = 0 := by
    unfold ampN
    rw [hO]
    unfold Jw at hJw
    exact key _ _ _ _ _ _ hJw
  apply hv
  show vec (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') t = 0
  unfold vec
  rw [hamp]
  simp
  rfl

def FormRelC : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
      ∀ ν, Pinned X u u' ν → ∀ t ∈ (Y.tO u u').ngSet ∪ (Y.tO u u').genSet, (Y.tO u u').vec t ≠ 0 →
        (∃ w : Point D.host.E (D.R.rS + 1), toPts w = ptPN t ∧ ∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u' w g) ∧
        ∀ w : Point D.host.E (D.R.rS + 1), toPts w = ptPN t → (∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u' w g) →
          ∃ (c : ℂ) (A : X.Vpi u →L[ℂ] X.Vpi u) (B : X.Vpi u' →L[ℂ] X.Vpi u'),
            OOt t = c • A.comp ((haveI := FiniteDimensional.complete ℂ (X.Vpi u)
              OO (ν (Formalism.L2.SG.RealObj.gamW X u u' w)) Set.univ (X.Wu u) (X.Wu u')
                (Formalism.L2.SG.RealObj.gamW X u u' w)).comp B)

theorem formNGC_of_rel (h : FormRelC) : FormNGC := by
  intro Cg cb Cw cT CT C0
  obtain ⟨a, b, hh⟩ := h Cg cb Cw cT CT C0
  exact ⟨a, b, fun C' Cl h1 h2 D large₂ X Y u u' hc ν hν t ht hv =>
    hh C' Cl h1 h2 D large₂ X Y u u' hc ν hν t (Set.mem_union_left _ ht) hv⟩

theorem stepTermVanish_of_rel (h : FormRelC) : StepTermVanish :=
  stepTermVanish_of_form (formNGC_of_rel h)

end Formalism.L2.SG.NGVanish
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SummableLogAlpD
section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.AlTie

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.DataInst

variable {D : D7} (X : HidaSetting D)

theorem alX_eq (hEta : EtaTie X) (u u' : D.what₂.Word) (v : HeightOneSpectrum (𝓞 X.B.I.F)) :
    alX X u u' v = alpD u u' (plEquiv X v) := by
  have haP : ∀ T : ℕ, aP (E := X.B.I.E) v D.R.k X.B.I.n T = aPD (plEquiv X v) T := by
    intro T
    unfold aP aPD
    have hI : Finset.Icc (if ((T : 𝓞 X.B.I.F) ∈ v.asIdeal) then D.R.k else D.R.k + 1) X.B.I.n =
        Finset.Icc (if ((T : 𝓞 D.host.F) ∈ (plEquiv X v).asIdeal) then D.R.k else D.R.k + 1) D.R.r := by
      rw [X.n_eq]
      by_cases hm : ((T : 𝓞 X.B.I.F) ∈ v.asIdeal)
      · rw [if_pos hm, if_pos ((natCast_mem_plEquiv X v T).2 hm)]
      · rw [if_neg hm, if_neg (fun h => hm ((natCast_mem_plEquiv X v T).1 h))]
    rw [hI]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hEta v, absNorm_plEquiv]
  unfold alX alpD Tw
  rw [haP, haP]
  by_cases h : TypAt X v
  · rw [if_pos h, if_pos ((typAt_iff X v).1 h)]
  · rw [if_neg h, if_neg (fun h' => h ((typAt_iff X v).2 h'))]

theorem summable_log_alpD (hk : 2 * D.R.rS + 2 + D.R.f + 5 ≤ D.R.k) (u u' : D.what₂.Word) :
    (∀ p, 0 < alpD u u' p) ∧ Summable fun p => Real.log (alpD u u' p) := by
  have hP := Formalism.L2.SG.Pf.placesOver_holds D
  have hα := Formalism.L2.SG.IntegralApproximation.AlpBound_holds D
  set s := D.R.k - 2 * D.R.rS - 2 with hs
  have hs2 : 2 ≤ s := by omega
  set a : PlF D → ℝ := fun p => (Formalism.L2.SG.DataCut.qP p ^ s)⁻¹ with ha
  have ha0 : ∀ p, 0 ≤ a p := fun p => inv_nonneg.2 (pow_nonneg (Formalism.L2.SG.DataCut.qP_nonneg p) _)
  have hsum : ∀ S : Finset (PlF D), ∑ p ∈ S, a p ≤ 3 * (D.R.f : ℝ) * ((2 : ℝ) ^ s)⁻¹ := by
    intro S
    exact Formalism.FourierDecayAlt.P.DensitySumsAndDomination.densSum (PlF D) S Formalism.L2.SG.DataCut.qP Loc.resChar D.R.f s hs2
      (fun p _ => ⟨(D.s.atP p).ellPrime.out, hP.1 p⟩)
      (fun m => hP.2 m _ (fun p hp => (Finset.mem_filter.1 hp).2))
  have haS : Summable a := summable_of_sum_le ha0 hsum
  have hαb := hα hk u u'
  have hal0 : ∀ p, 0 < alpD u u' p := fun p => lt_of_lt_of_le (Real.exp_pos _) (hαb p).1
  refine ⟨hal0, ?_⟩
  refine Summable.of_norm_bounded (g := fun p => 2 * a p) (haS.mul_left 2) (fun p => ?_)
  rw [Real.norm_eq_abs, abs_le]
  have h1 := Real.log_le_log (Real.exp_pos _) (hαb p).1
  have h2 := Real.log_le_log (hal0 p) (hαb p).2
  rw [Real.log_exp] at h1 h2
  have ha' : a p = (Formalism.L2.SG.DataCut.qP p ^ (D.R.k - 2 * D.R.rS - 2))⁻¹ := rfl
  constructor <;> linarith

theorem prod_split {β : Type} (f : β → ℝ) (s : Finset β) (hpos : ∀ v, 0 < f v)
    (hlog : Summable fun v => Real.log (f v)) :
    (∏ p : ↥s, f p.1) * ∏' v : {v // v ∉ s}, f v.1 = ∏' v, f v := by
  have hls : Summable (fun v : {v // v ∉ s} => Real.log (f v.1)) :=
    hlog.comp_injective (i := fun v : {v // v ∉ s} => v.1) Subtype.val_injective
  have hO : ∏' v : {v // v ∉ s}, f v.1 = Real.exp (∑' v : {v // v ∉ s}, Real.log (f v.1)) :=
    (Real.rexp_tsum_eq_tprod (f := fun v : {v // v ∉ s} => f v.1) (fun v => hpos v.1) hls).symm
  have hT : ∏ p : ↥s, f p.1 = Real.exp (∑ p : ↥s, Real.log (f p.1)) := by
    rw [Real.exp_sum]
    exact Finset.prod_congr rfl fun p _ => (Real.exp_log (hpos _)).symm
  have hsplit : ∑ p : ↥s, Real.log (f p.1) + ∑' v : {v // v ∉ s}, Real.log (f v.1) = ∑' v, Real.log (f v) := by
    rw [Finset.sum_coe_sort s (fun x => Real.log (f x))]
    exact hlog.sum_add_tsum_compl (s := s)
  rw [hO, hT, ← Real.exp_add, hsplit, Real.rexp_tsum_eq_tprod hpos hlog]

theorem locOf_al_eq (hEta : EtaTie X) (hk : 2 * D.R.rS + 2 + D.R.f + 5 ≤ D.R.k) (u u' : D.what₂.Word)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) :
    (locOf X u u' ψ).al = ∏' q, alpD u u' q := by
  obtain ⟨hpos, hlog⟩ := summable_log_alpD hk u u'
  have he : ∀ v, alX X u u' v = alpD u u' (plEquiv X v) := alX_eq X hEta u u'
  have hxpos : ∀ v, 0 < alX X u u' v := fun v => (he v).symm ▸ hpos _
  have hxlog : Summable fun v => Real.log (alX X u u' v) := by
    have h1 : Summable fun v => Real.log (alpD u u' (plEquiv X v)) := (plEquiv X).summable_iff.2 hlog
    exact h1.congr fun v => by rw [he v]
  have hS := prod_split (alX X u u') (Formalism.L2.SG.TypedSets.typSet X.B.I.F (D.host.g 0) (D.host.g 1)) hxpos hxlog
  have hR : ∏' v, alX X u u' v = ∏' q, alpD u u' q := by
    rw [tprod_congr he]
    exact (plEquiv X).tprod_eq (alpD u u')
  rw [← hR, ← hS]
  rfl

end Formalism.L2.SG.Pf.AlTie

namespace Formalism.L2.SG.Pf

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets
  Formalism.L2.SG.MassDataConc Formalism.L2.SG.MassDataForm Formalism.L2.SG.Pf.RowForm MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem AlTieC_of {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (Y : Formalism.L2.SG.Full.Full X)
    (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) (sd C Th : ℝ)
    (vR : Term D u u' (X.Fu u) (Y.what₂ u) → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' (X.Fu u) (Y.what₂ u))
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (hEta : AlTie.EtaTie X) (hk : 2 * D.R.rS + 2 + D.R.f + 5 ≤ D.R.k) :
    AlTieC X hb Y u u' X0 ψ sd C Th vR Q M δ i0 i0' νq := by
  unfold AlTieC
  exact AlTie.locOf_al_eq X hEta hk u u' ψ

theorem AlTieC_of_loc {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (Y : Formalism.L2.SG.Full.Full X)
    (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) (sd C Th : ℝ)
    (vR : Term D u u' (X.Fu u) (Y.what₂ u) → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' (X.Fu u) (Y.what₂ u))
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (hL : Formalism.L2.SG.Pf.LocCP.LocTied D) (hk : 2 * D.R.rS + 2 + D.R.f + 5 ≤ D.R.k) :
    AlTieC X hb Y u u' X0 ψ sd C Th vR Q M δ i0 i0' νq :=
  AlTieC_of X hb Y u u' X0 ψ sd C Th vR Q M δ i0 i0' νq (AlTie.etaTie_of X hL) hk

end Formalism.L2.SG.Pf
end
end

