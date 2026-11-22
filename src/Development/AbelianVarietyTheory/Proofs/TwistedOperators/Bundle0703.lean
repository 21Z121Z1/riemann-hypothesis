import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0691
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0356
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0376
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTrace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RepresentationAtEveryPlace
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0674
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0037
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0689
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0193
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0182
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0196
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0464
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0296
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0174
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0692
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0273
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0526
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0676

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealDictionaryPrintHypothesesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_dictionary_hypotheses : GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7) {n k : ℕ} (Xs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E n) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E k)
    (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Xs Ws) (ψ' : AddChar (AF D.host.F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Xs Ws)
    (τ : ∀ w : InfinitePlace D.host.F, GlobalTheory.AdelicU.EmbOver D.host.E w),
    GlobalTheory.RealDict.PublishedHyps D Xs Ws Mo ψ' χX χW om τ → Mo.IsGood ψ' →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Ws,
    ∀ (f f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin n × Fin k)) (r : (Fin n × Fin k → AF D.host.F) → ℂ),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) f r → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) f₁ r →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ →
      ∀ {d : ℕ} (G : Matrix (Fin n) (Fin n) D.host.E) (e : Fin k ≃ Fin d) (x : Matrix (Fin d) (Fin n) (AE D)),
        HasDerivAt (fun t : ℝ => GlobalTheory.TripleRead.thO Mo ψ' G e
            (om (1, γ (Multiplicative.ofAdd t)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) f r)) x)
          (GlobalTheory.TripleRead.thO Mo ψ' G e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) f₁ r) x) 0 := by
  first | exact @GlobalTheory.ThetaInterchange.hasDerivAt_thO | exact GlobalTheory.ThetaInterchange.hasDerivAt_thO | (intros; apply GlobalTheory.ThetaInterchange.hasDerivAt_thO <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RepresentationAtEveryPlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.representation_at_every_place : Big fun ch => ∀ s, RepAt ch s := by
  first | exact @GlobalTheory.RowRep.rep_at | exact GlobalTheory.RowRep.rep_at | (intros; apply GlobalTheory.RowRep.rep_at <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowDataLocalPureTensorsLargeDepthStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowData_localPureTensors_largeDepth : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T) (e : AE D), IsIdemSum e (locPl ch.G t) → ∀ (φ : (∀ w : locPl ch.G t, ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin ((locGrid ch.G t w.1).rank b.tgt)) (Fin ((locGrid ch.G t w.1).rank b.src)) (Kw w.1) → ℂ)) (fr : SchRow ch.G), (∀ i : Fin D.R.m, IsLocVec ch.W (.chi i D.R.m) e (ch.rm.vX i D.R.m) (fun y => if IsHalf e y then ∏ w : locPl ch.G t, φ w (.ex i D.R.m) (ch.S.B.coord t w.1 (X := (i, D.R.m)) (Y := (i + 1, D.R.m)) ⟨i.2.le, le_rfl⟩ ⟨i.2, le_rfl⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) (fr i)) → ∃ (dr : ∀ i : Fin D.R.m, FinDatum ch.G t (.chi i D.R.m)) (cr : ∀ i : Fin D.R.m, WO (ch.G.pS (.chi i D.R.m : Pair T)) (ch.G.pT (.chi i D.R.m : Pair T)) →₀ ℂ), (∀ i, (dr i).e = e ∧ IsCombOf ch.W (dr i) (cr i)) ∧ (∀ i, comb ch.W.ψ _ _ (cr i) (ch.rm.vX i D.R.m) = fr i) ∧ ∀ i y, IsHalf e y → (dr i).fn y = ∏ w : locPl ch.G t, φ w (.ex i D.R.m) (ch.S.B.coord t w.1 (X := (i, D.R.m)) (Y := (i + 1, D.R.m)) ⟨i.2.le, le_rfl⟩ ⟨i.2, le_rfl⟩ (y.map fun a => cpt w.1 (toEAf D a))) := by
  first | exact @GlobalTheory.RowSingle.rowData | exact GlobalTheory.RowSingle.rowData | (intros; apply GlobalTheory.RowSingle.rowData <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowPeriodSubgroupFinitePointsSemidirect
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped NNReal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.CellMass

noncomputable section

namespace GlobalTheory.RowGrpSemi

theorem finite_split {X Y : Type} [Group X] [TopologicalSpace X] [Group Y] [TopologicalSpace Y]
    (Xf : Subgroup X) (Yf : Subgroup Y) (N R K : Subgroup X) (s : Y →* X) (p : R → Y)
    (hR : R = N ⊔ s.range) (hconj : ∀ n ∈ N, ∀ h, s h * n * (s h)⁻¹ ∈ N) (hs : Continuous s) (hp : Continuous p)
    (hpn : ∀ n ∈ N, ∀ h (hm : n * s h ∈ R), p ⟨n * s h, hm⟩ = h) (hsf : ∀ y ∈ Yf, s y ∈ Xf)
    (hkey : ∀ n ∈ N, ∀ h, n * s h ∈ Xf → h ∈ Yf) (hK : K ≤ Xf) :
    ∃ (π : R.subgroupOf Xf →* Yf) (σ : Yf →* R.subgroupOf Xf),
      Continuous π ∧ Continuous σ ∧ (∀ y, π (σ y) = y) ∧ (∀ r, π r = 1 ↔ r.1 ∈ N.subgroupOf Xf) ∧
      ∀ b : Xf, {g : Yf | ∃ n ∈ N, (b.1)⁻¹ * (n * s g.1) * b.1 ∈ K} = π '' {r | b⁻¹ * r.1 * b ∈ K.subgroupOf Xf} := by

  have hnorm : s.range ≤ Subgroup.normalizer (N : Set X) := by
    rintro _ ⟨y, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro n
    refine ⟨fun hn => hconj n hn y, fun hn => ?_⟩
    have := hconj _ hn y⁻¹
    have e : s y⁻¹ * (s y * n * (s y)⁻¹) * (s y⁻¹)⁻¹ = n := by rw [map_inv]; group
    rwa [e] at this
  have hdec : ∀ x ∈ R, ∃ n ∈ N, ∃ h, x = n * s h := by
    intro x hx
    rw [hR, ← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left N s.range hnorm] at hx
    obtain ⟨n, hn, _, ⟨h, rfl⟩, e⟩ := hx
    exact ⟨n, hn, h, e.symm⟩
  have hmemR : ∀ n ∈ N, ∀ h, n * s h ∈ R := fun n hn h => by
    rw [hR]; exact mul_mem (Subgroup.mem_sup_left hn) (Subgroup.mem_sup_right ⟨h, rfl⟩)
  have hpeq : ∀ x y (hx : x ∈ R) (hy : y ∈ R), x = y → p ⟨x, hx⟩ = p ⟨y, hy⟩ := by
    rintro x _ hx hy rfl; rfl
  have hval : ∀ x (hx : x ∈ R), ∃ n ∈ N, x = n * s (p ⟨x, hx⟩) := by
    intro x hx
    obtain ⟨n, hn, h, rfl⟩ := hdec x hx
    exact ⟨n, hn, by rw [hpn n hn h hx]⟩
  have hpmul : ∀ x y (hx : x ∈ R) (hy : y ∈ R) (hxy : x * y ∈ R), p ⟨x * y, hxy⟩ = p ⟨x, hx⟩ * p ⟨y, hy⟩ := by
    intro x y hx hy hxy
    obtain ⟨n, hn, h, rfl⟩ := hdec x hx
    obtain ⟨n', hn', h', rfl⟩ := hdec y hy
    have e : n * s h * (n' * s h') = (n * (s h * n' * (s h)⁻¹)) * s (h * h') := by rw [map_mul]; group
    rw [hpeq _ _ hxy (hmemR _ (mul_mem hn (hconj n' hn' h)) _) e, hpn _ (mul_mem hn (hconj n' hn' h)),
      hpn n hn h, hpn n' hn' h']
  have hp1 : ∀ (h1 : (1 : X) ∈ R), p ⟨1, h1⟩ = 1 := by
    intro h1
    rw [hpeq 1 (1 * s 1) h1 (hmemR 1 N.one_mem 1) (by rw [map_one, one_mul]), hpn 1 N.one_mem 1]
  have hfin : ∀ x (hx : x ∈ R), x ∈ Xf → p ⟨x, hx⟩ ∈ Yf := by
    intro x hx hxf
    obtain ⟨n, hn, e⟩ := hval x hx
    exact hkey n hn _ (e ▸ hxf)
  have hRf : ∀ r : R.subgroupOf Xf, r.1.1 ∈ R := fun r => Subgroup.mem_subgroupOf.1 r.2
  let π : R.subgroupOf Xf →* Yf :=
    { toFun := fun r => ⟨p ⟨r.1.1, hRf r⟩, hfin _ _ r.1.2⟩
      map_one' := Subtype.ext (hp1 _)
      map_mul' := fun r r' => Subtype.ext (hpmul _ _ (hRf r) (hRf r') (hRf (r * r'))) }
  have hsR : ∀ y, s y ∈ R := fun y => by rw [hR]; exact Subgroup.mem_sup_right ⟨y, rfl⟩
  let σ : Yf →* R.subgroupOf Xf :=
    { toFun := fun y => ⟨⟨s y.1, hsf _ y.2⟩, Subgroup.mem_subgroupOf.2 (hsR _)⟩
      map_one' := Subtype.ext (Subtype.ext (map_one s))
      map_mul' := fun y y' => Subtype.ext (Subtype.ext (map_mul s _ _)) }
  have hπ : ∀ r, (π r).1 = p ⟨r.1.1, hRf r⟩ := fun r => rfl
  refine ⟨π, σ, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hp.comp ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)).subtype_mk _
  · exact ((hs.comp continuous_subtype_val).subtype_mk _).subtype_mk _
  · intro y
    apply Subtype.ext
    rw [hπ]
    exact (hpeq _ (1 * s y.1) _ (hmemR 1 N.one_mem _) (one_mul _).symm).trans (hpn 1 N.one_mem _ _)
  · intro r
    rw [Subgroup.mem_subgroupOf]
    constructor
    · intro h1
      have h1' : p ⟨r.1.1, hRf r⟩ = 1 := by rw [← hπ, h1]; rfl
      obtain ⟨n, hn, e⟩ := hval _ (hRf r)
      rw [h1', map_one, mul_one] at e
      exact e ▸ hn
    · intro hn
      apply Subtype.ext
      rw [hπ]
      exact (hpeq _ (r.1.1 * s 1) _ (hmemR _ hn 1) (by rw [map_one, mul_one])).trans (hpn _ hn 1 _)
  · intro b
    ext g
    constructor
    · rintro ⟨n, hn, hk⟩
      have hxf : n * s g.1 ∈ Xf := by
        have e : n * s g.1 = b.1 * ((b.1)⁻¹ * (n * s g.1) * b.1) * (b.1)⁻¹ := by group
        rw [e]
        exact mul_mem (mul_mem b.2 (hK hk)) (inv_mem b.2)
      refine ⟨⟨⟨n * s g.1, hxf⟩, Subgroup.mem_subgroupOf.2 (hmemR n hn _)⟩, ?_, ?_⟩
      · show ((b⁻¹ * ⟨n * s g.1, hxf⟩ * b : Xf) : X) ∈ K
        exact hk
      · apply Subtype.ext
        rw [hπ]
        exact hpn n hn _ _
    · rintro ⟨r, hr, rfl⟩
      obtain ⟨n, hn, e⟩ := hval _ (hRf r)
      refine ⟨n, hn, ?_⟩
      rw [hπ, ← e]
      exact hr

end GlobalTheory.RowGrpSemi

namespace GlobalTheory.RowGrpSemi

open GlobalTheory.Core.Mi

theorem key_jac {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {n : GA D S} (hn : n ∈ flagN d) (h : GA D S₀)
    (hf : n * d.emb0 h ∈ GfC S) : h ∈ GfC S₀ := by
  rw [CenAct.mem_GfC_iff] at hf ⊢
  have := GlobalTheory.LevNorm.finf_sand d.p0 _ d.j0 hf d.p0_j0
  rwa [GlobalTheory.JacProj.witt_anisotropic_block_flag_mul_embedded d hn h] at this

theorem jac_case {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (N R K : Subgroup (GA D S)) (s : GA D S₀ →* GA D S)
    (hN : N = flagN d) (hs : s = d.emb0) (hR : R = N ⊔ s.range) (hK : K ≤ GfC S) :
    ∃ (π : R.subgroupOf (GfC S) →* GfC S₀) (σ : GfC S₀ →* R.subgroupOf (GfC S)),
      Continuous π ∧ Continuous σ ∧ (∀ y, π (σ y) = y) ∧ (∀ r, π r = 1 ↔ r.1 ∈ N.subgroupOf (GfC S)) ∧
      ∀ b : GfC S, {g : GfC S₀ | ∃ n ∈ N, (b.1)⁻¹ * (n * s g.1) * b.1 ∈ K} =
        π '' {r | b⁻¹ * r.1 * b ∈ K.subgroupOf (GfC S)} := by
  subst hN hs hR
  exact finite_split (GfC S) (GfC S₀) (flagN d) _ K d.emb0 (GlobalTheory.JacProj.proj d) rfl
    (fun n hn h => GlobalTheory.MixPer.witt_anisotropic_group_normalizes_flag_unipotent D S S₀ ρ d n hn h) d.continuous_embed (GlobalTheory.JacProj.continuous_proj d)
    (fun n hn h _ => GlobalTheory.JacProj.proj_mul d h ⟨n, hn⟩) (fun y hy => CenAct.witt_embedding_mem_finite_unitary_points d hy)
    (fun n hn h hf => key_jac d hn h hf) hK

theorem bes_case {D : D7} {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) (N R K : Subgroup (GA D S))
    (s : GA D A →* GA D S) (hN : N = flagN d) (hs : s = embA d o) (hR : R = N ⊔ s.range) (hK : K ≤ GfC S) :
    ∃ (π : R.subgroupOf (GfC S) →* GfC A) (σ : GfC A →* R.subgroupOf (GfC S)),
      Continuous π ∧ Continuous σ ∧ (∀ y, π (σ y) = y) ∧ (∀ r, π r = 1 ↔ r.1 ∈ N.subgroupOf (GfC S)) ∧
      ∀ b : GfC S, {g : GfC A | ∃ n ∈ N, (b.1)⁻¹ * (n * s g.1) * b.1 ∈ K} =
        π '' {r | b⁻¹ * r.1 * b ∈ K.subgroupOf (GfC S)} := by
  subst hN hs hR
  obtain ⟨p, hp, hpn⟩ := GlobalTheory.BesProj.exists_continuous_proj D S S₀ A L ρ d o
  refine finite_split (GfC S) (GfC A) (flagN d) _ K (embA d o) p rfl (fun n hn h => ?_)
    (d.continuous_embed.comp (o.continuous_emb.comp (continuous_id.prodMk continuous_const))) hp (fun n hn h _ => hpn h ⟨n, hn⟩) (fun y hy => CenAct.embA_mem_GfC d o hy)
    (fun n hn h hf => ?_) hK
  · rw [embA_apply]
    exact GlobalTheory.MixPer.witt_anisotropic_group_normalizes_flag_unipotent D S S₀ ρ d n hn _
  · rw [embA_apply] at hf
    have h0 := key_jac d hn _ hf
    have h1 : embA d o h ∈ GfC S := by rw [embA_apply]; exact CenAct.witt_embedding_mem_finite_unitary_points d h0
    exact GlobalTheory.LevNorm.mem_GfC_of_embA d o h1

end GlobalTheory.RowGrpSemi

namespace GlobalTheory.CellMass

theorem rowGrp_finite_semidirect : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R), ∀ j ∈ idx D,
    IsClosed (((rowGrp ch.G j).subgroupOf (GfC _) : Subgroup (GfC (ch.G.V (.grid D.R.m j)))) : Set (GfC (ch.G.V (.grid D.R.m j)))) ∧
    IsClosed (((rowN ch.G j).subgroupOf (GfC _) : Subgroup (GfC (ch.G.V (.grid D.R.m j)))) : Set (GfC (ch.G.V (.grid D.R.m j)))) ∧
    (rowN ch.G j).subgroupOf (GfC _) ≤ (rowGrp ch.G j).subgroupOf (GfC (ch.G.V (.grid D.R.m j))) ∧
    IsOpen (((latGrp ch.G j).subgroupOf (GfC _) : Subgroup (GfC (ch.G.V (.grid D.R.m j)))) : Set (GfC (ch.G.V (.grid D.R.m j)))) ∧
    IsCompact (((latGrp ch.G j).subgroupOf (GfC _) : Subgroup (GfC (ch.G.V (.grid D.R.m j)))) : Set (GfC (ch.G.V (.grid D.R.m j)))) ∧
    ∃ (π : (rowGrp ch.G j).subgroupOf (GfC (ch.G.V (.grid D.R.m j))) →* GfC (ch.G.V (.top j)))
      (σ : GfC (ch.G.V (.top j)) →* (rowGrp ch.G j).subgroupOf (GfC (ch.G.V (.grid D.R.m j)))),
      Continuous π ∧ Continuous σ ∧ (∀ y, π (σ y) = y) ∧ (∀ r, π r = 1 ↔ r.1 ∈ (rowN ch.G j).subgroupOf (GfC _)) ∧
      ∀ b : GfC (ch.G.V (.grid D.R.m j)), prSet ch.G j b = π '' {r | b⁻¹ * r.1 * b ∈ (latGrp ch.G j).subgroupOf (GfC _)} := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch j hj
  have hj' := List.mem_range'_1.1 hj
  have sp := GlobalTheory.RowGrpSplit.grpAt_all ch j hj
  have hNfl : ∃ (S₀ : HSp D) (ρ : ℕ) (d : HypDec (ch.G.V (.grid D.R.m j)) S₀ ρ), rowN ch.G j = flagN d := by
    by_cases h1 : j + 2 * ((D.R.m - 1 - j) / 2) + 1 = D.R.m
    · exact ⟨_, _, _, by unfold rowN; rw [dif_pos h1]⟩
    · have h2 : j + 2 * ((D.R.m - 2 - j) / 2) + 2 = D.R.m := by omega
      exact ⟨_, _, _, by unfold rowN; rw [dif_neg h1, dif_pos h2]⟩
  have hNc : IsClosed ((rowN ch.G j : Subgroup (GA D (ch.G.V (.grid D.R.m j)))) : Set (GA D (ch.G.V (.grid D.R.m j)))) := by
    obtain ⟨S₀, ρ, d, e⟩ := hNfl
    rw [e]
    exact GlobalTheory.Mem.TrueRecord.isClosed_NFlag _ (isIsoSub_e d)
  refine ⟨?_, ?_, ?_, sp.opn, ?_, ?_⟩
  · rw [Subgroup.coe_subgroupOf]
    exact sp.clR.preimage continuous_subtype_val
  · rw [Subgroup.coe_subgroupOf]
    exact hNc.preimage continuous_subtype_val
  · intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    rw [rowGrp_eq]
    exact Subgroup.mem_sup_left hx
  · rw [Subgroup.coe_subgroupOf]
    exact sp.clB.isClosedEmbedding_subtypeVal.isCompact_preimage sp.cpt
  · by_cases h1 : j + 2 * ((D.R.m - 1 - j) / 2) + 1 = D.R.m
    · exact GlobalTheory.RowGrpSemi.jac_case (rowJac ch.G j (by omega) ((D.R.m - 1 - j) / 2) (by omega)) _ _ _ _
        (by unfold rowN; rw [dif_pos h1]) (by unfold rowEmb; rw [dif_pos h1]) (rowGrp_eq ch.G j) sp.le
    · have h2 : j + 2 * ((D.R.m - 2 - j) / 2) + 2 = D.R.m := by omega
      exact GlobalTheory.RowGrpSemi.bes_case (besDecAt ch.G j _ h2) (GlobalTheory.OrthSumExists.orthDecHsum D _ _) _ _ _ _
        (by unfold rowN; rw [dif_neg h1, dif_pos h2]) (by unfold rowEmb; rw [dif_neg h1, dif_pos h2]) (rowGrp_eq ch.G j) sp.le

end GlobalTheory.CellMass
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestMemFourierJacobiGroupOfSumFrameSymmetric
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open GlobalTheory.RootEx GlobalTheory.RowRep
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RowRepLoc
open GlobalTheory.LocGrp GlobalTheory.LocMod

private lemma lev_le_of_sum_elim_le {σ p' : ℕ} (hp : p' = σ ∨ p' = σ + 1) {n : Type} (r s : n ⊕ Fin (2 * σ))
    (h : (Sum.elim (fun _ => σ + 1) (fun j : Fin (2 * σ) => if j.val < σ then j.val + 1 else j.val + 2) : n ⊕ Fin (2 * σ) → ℕ) s ≤
      (Sum.elim (fun _ => σ + 1) (fun j : Fin (2 * σ) => if j.val < σ then j.val + 1 else j.val + 2) : n ⊕ Fin (2 * σ) → ℕ) r) :
    GlobalTheory.RootEx.lev p' s ≤ GlobalTheory.RootEx.lev p' r := by

  rcases hp with rfl | rfl <;> rcases r with r | r <;> rcases s with s | s <;>
    simp only [Sum.elim_inl, Sum.elim_inr, GlobalTheory.RootEx.lev] at h ⊢ <;> (try split_ifs at h) <;> omega

private lemma mul_apply_eq_of_mul_eq_of_col_eq {K : Type} [Field K] {m n n' : Type} [Fintype m] (M : Matrix m m K) (X : Matrix m n K)
    (Y : Matrix m n' K) (hX : M * X = X) (i : n) (j : n') (hc : ∀ t, X t i = Y t j) (r : m) : (M * Y) r j = Y r j := by

  have h := congrFun (congrFun hX r) i
  simp only [Matrix.mul_apply, hc] at h ⊢
  exact h

theorem mem_jac {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)
    {A B : HSp D} {σ : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B (2 * σ) ε)
    {b b' : Matrix (Fin A.rank) (Fin A.rank) k} (hb : b * b' = 1) (hb' : b' * b = 1) {u : Fin (2 * σ) → k}
    {Γ : Matrix (Fin A.rank ⊕ Fin (2 * σ)) (Fin B.rank) k} (h1 : Γ * sumCols d p.π b u = 1) (h2 : sumCols d p.π b u * Γ = 1)
    {g : GA D B} (hg : SuppAt p.e B g) {x : GL (Fin A.rank ⊕ Fin (2 * σ)) k}
    (e : x.val = Γ * ((mt B g).map p.π * sumCols d p.π b u)) (hx : x ∈ symR k (Fin A.rank) (2 * σ)) :
    g ∈ jacGrp (jacDec d rfl) := by
  classical
  have hS : ∀ r (j : Fin (2 * σ)), sumCols d p.π b u r (Sum.inr j) = p.π (incA D (d.a r j)) * u j := by
    intro r j
    simp only [sumCols, Matrix.fromCols_apply_inr, Matrix.mul_diagonal, Matrix.map_apply, RingHom.comp_apply]
  let F : Frame k B.rank (Fin A.rank ⊕ Fin (2 * σ)) := ⟨sumCols d p.π b u, Γ, h2, h1⟩
  let FA : Frame k A.rank (Fin A.rank) := ⟨b, b', hb, hb'⟩
  obtain ⟨φ, hφ⟩ := exists_hom p F
  have hgx : p.IsLoc F g x := by
    refine ⟨hg, ?_⟩
    show (mt B g).map p.π = sumCols d p.π b u * x.val * Γ
    rw [e]
    simp only [Matrix.mul_assoc]
    rw [h2, Matrix.mul_one, ← Matrix.mul_assoc, h2, Matrix.one_mul]
  rw [isLoc_unique p hgx (hφ x)]

  have hfix : ∀ g₀ : GA D A, (mt B ((jacDec d rfl).emb0 g₀)).map p.π * d.a.map (p.π.comp (incA D)) =
      d.a.map (p.π.comp (incA D)) := by
    intro g₀
    have hX := map_fix p (HypDec.wittDecomp_anisotropicEmbedding_inclX (d := jacDec d rfl) (g := g₀))
    have hY := map_fix p (HypDec.wittDecomp_anisotropicEmbedding_inclY (d := jacDec d rfl) (g := g₀))
    ext r j
    by_cases hj : j.val < σ
    · exact mul_apply_eq_of_mul_eq_of_col_eq _ _ _ hX ⟨j.val, hj⟩ j (fun t => rfl) r
    · refine mul_apply_eq_of_mul_eq_of_col_eq _ _ _ hY ⟨2 * σ - 1 - j.val, by omega⟩ j (fun t => ?_) r
      show p.π (incA D ((jacDec d rfl).e' t ⟨2 * σ - 1 - j.val, by omega⟩)) = p.π (incA D (d.a t j))
      dsimp only [jacDec, Matrix.submatrix_apply, id]
      congr 3
      apply Fin.ext
      simp
      omega
  have hN : ∀ p', (p' = σ ∨ p' = σ + 1) → GlobalTheory.RootEx.N k (Fin A.rank) (2 * σ) p' ≤ (jacGrp (jacDec d rfl)).comap φ := by
    intro p' hp'
    unfold GlobalTheory.RootEx.N
    rw [Subgroup.closure_le]
    intro q hq
    show φ q ∈ flagN (jacDec d rfl) ⊔ (jacDec d rfl).emb0.range
    refine Subgroup.mem_sup_left (flag_of_strict p (jacDec d rfl) FA F
      (Sum.elim (fun a => Sum.inl a) (Sum.elim (fun i : Fin σ => Sum.inr ⟨i.val, by omega⟩)
        (fun i : Fin σ => Sum.inr ⟨2 * σ - 1 - i.val, by omega⟩))) ?_
      (Sum.elim (fun _ => (1 : k)) (Sum.elim (fun i : Fin σ => u ⟨i.val, by omega⟩)
        (fun i : Fin σ => u ⟨2 * σ - 1 - i.val, by omega⟩))) ?_
      (Sum.elim (fun _ => σ + 1) (fun j : Fin (2 * σ) => if j.val < σ then j.val + 1 else j.val + 2)) ?_ (hφ q) ?_)
    · rintro (a | j)
      · exact ⟨Sum.inl a, rfl⟩
      · by_cases hj : j.val < σ
        · exact ⟨Sum.inr (Sum.inl ⟨j.val, hj⟩), rfl⟩
        · refine ⟨Sum.inr (Sum.inr ⟨2 * σ - 1 - j.val, by omega⟩), congrArg Sum.inr (Fin.ext ?_)⟩
          show 2 * σ - 1 - (2 * σ - 1 - j.val) = j.val
          omega
    · rintro r (a | i | i)
      · show sumCols d p.π b u r (Sum.inl a) = 1 * ((jacDec d rfl).j0.map p.π * b) r a
        rw [one_mul]
        rfl
      · show sumCols d p.π b u r (Sum.inr ⟨i.val, _⟩) = u ⟨i.val, _⟩ * ((jacDec d rfl).jX.map p.π) r i
        rw [hS, mul_comm]
        rfl
      · show sumCols d p.π b u r (Sum.inr ⟨2 * σ - 1 - i.val, _⟩) = u ⟨2 * σ - 1 - i.val, _⟩ * ((jacDec d rfl).jY.map p.π) r i
        rw [hS, mul_comm]
        show u ⟨2 * σ - 1 - i.val, _⟩ * p.π (incA D (d.a r ⟨2 * σ - 1 - i.val, _⟩)) =
          u ⟨2 * σ - 1 - i.val, _⟩ * p.π (incA D ((jacDec d rfl).e' r i))
        dsimp only [jacDec, Matrix.submatrix_apply, id]
        congr 4
        apply Fin.ext
        simp
        omega
    · rintro (a | i | i)
      · rfl
      · show (if i.val < σ then i.val + 1 else i.val + 2) = i.val + 1
        rw [if_pos i.isLt]
      · show (if 2 * σ - 1 - i.val < σ then 2 * σ - 1 - i.val + 1 else 2 * σ - 1 - i.val + 2) = 2 * σ - i.val + 1
        have := i.isLt
        rw [if_neg (by omega)]
        omega
    · intro r s hrs
      have hq' : GlobalTheory.RootEx.InN p' q := hq
      rw [Matrix.sub_apply, hq' r s (lev_le_of_sum_elim_le hp' r s hrs), sub_self]
  have hR : symR k (Fin A.rank) (2 * σ) ≤ (jacGrp (jacDec d rfl)).comap φ := by
    unfold symR symN
    rw [show (2 * σ + 1) / 2 = σ by omega, show 2 * σ / 2 + 1 = σ + 1 by omega]
    refine sup_le ?_ (sup_le (hN σ (Or.inl rfl)) (hN (σ + 1) (Or.inr rfl)))
    rintro _ ⟨g₀, rfl⟩
    obtain ⟨ψ, hψ⟩ := exists_hom p FA
    have hloc : p.IsLoc F ((jacDec d rfl).emb0 (ψ g₀)) (embX (2 * σ) g₀) := by
      refine ⟨suppAt_wittLeviEmbedding _ (hψ g₀).1, ?_⟩
      refine eq_embX F _ g₀ ((frameMat B A d.ι).map (p.π.comp (incA D)) * b) (fun r a => rfl) ?_ ?_
      · exact intertwine p (HypDec.wittDecomp_anisotropicEmbedding_inclAnisotropic (d := jacDec d rfl) (g := ψ g₀)) (hψ g₀)
      · intro j
        refine fix_col (hfix (ψ g₀)) (u j) j (fun r => ?_)
        show sumCols d p.π b u r (Sum.inr j) = u j * (d.a.map (p.π.comp (incA D))) r j
        rw [hS, mul_comm]
        rfl
    show φ (embX (2 * σ) g₀) ∈ flagN (jacDec d rfl) ⊔ (jacDec d rfl).emb0.range
    rw [isLoc_unique p (hφ _) hloc]
    exact Subgroup.mem_sup_right ⟨_, rfl⟩
  exact hR hx

end GlobalTheory.RowRepLoc

theorem GlobalTheory.RowRepLoc.mem_jacGrp_of_symR : ∀ {D : D7} {A B : HSp D} {c σ : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε) (h : c = 2 * σ), 1 ≤ σ → ∀ (w : Pl D.host.E) (β : GL (Fin A.rank) (Lev.EAf D)) (β' : GL (Fin B.rank) (Lev.EAf D)) (u : Fin c → Kw w), IsSumFrame d w β β' u → (∀ p, u p ≠ 0) → ∀ {a b : ℕ} (_ : a = A.rank) (hb : b = B.rank) (hab : a + c = b) (q : GlobalTheory.FinPl.SplitPt D (Kw w)), (∀ x, q.pr x = GlobalTheory.RowRep.piAt w x) → ∀ g : GA D B, SuppAt q.e B g → frameGL hab (inBasis hb β' w (Lev.finE B g)) ∈ symR (Kw w) (Fin a) c → g ∈ jacGrp (jacDec d h) := by
  intro D A B c σ ε d h _ w β β' u hF _ a b ha hb hab q hq g hg hx
  subst h ha hb
  obtain ⟨Γ, hΓ1, hΓ2, hΓ⟩ := frame_val d w hF
  have hπ : (GlobalTheory.LocMod.Place.ofSplitPt q).π = piAt w := RingHom.ext hq
  refine GlobalTheory.RowRepLoc.mem_jac (GlobalTheory.LocMod.Place.ofSplitPt q) d (b' := (GlobalTheory.StdFrames.loc w β)⁻¹.val)
    (Units.mul_inv _) (Units.inv_mul _) (u := u) (Γ := Γ) ?_ ?_ hg (x := frameGL hab (inBasis rfl β' w (Lev.finE B g))) ?_ hx
  · rw [hπ]; exact hΓ1
  · rw [hπ]; exact hΓ2
  · rw [hπ]; exact hΓ g

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawUnfoldingCompatibleStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seesaw_unfolding_compatible : GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf D.sp.cm.sig Γ.V Bs.emb, ∀ ΦD ∈ algD Γ.M Bs.ψ Bs.emb, om (k, 1) ΦD ∈ algD Γ.M Bs.ψ Bs.emb := by
  first | exact @GlobalTheory.SquareAgree.CompactStableD.kInf_stable_algD | exact GlobalTheory.SquareAgree.CompactStableD.kInf_stable_algD | (intros; apply GlobalTheory.SquareAgree.CompactStableD.kInf_stable_algD <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawUnfoldingSymmetryStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seesaw_unfolding_symmetry : GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Γ.V', ∀ f ∈ Γ.M'.Pol Bs.ψ Bs.emb, ∀ f₁ ∈ Γ.M'.Pol Bs.ψ Bs.emb, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (fun t => om' (γ (Multiplicative.ofAdd t), 1)) f f₁ → ∀ φ : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl D.host.F, ((Fin W₁.rank × Fin (W.rank + W₁.rank)) → Fv D.host.F w) → ℂ, (∀ w, φ w ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ w in Filter.cofinite, φ w = Γ.M'.vac w) → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₁ φ ∈ kerPD ψ θ A₁ B Bs Γ cB p' := by
  first | exact @GlobalTheory.SquareAgree.KerLie.lie_mem_kerPD | exact GlobalTheory.SquareAgree.KerLie.lie_mem_kerPD | (intros; apply GlobalTheory.SquareAgree.KerLie.lie_mem_kerPD <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaContractionLinearLeftLargeDepthStatement
section
open GlobalTheory.RowClaim GlobalTheory.ConnectionLinear
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaContraction_linear_left_largeDepth : Big fun ch => GlobalTheory.ConnectionLinear.ContrLin ch 0 := by
  first | exact @GlobalTheory.ConnectionLinear.contrLin_left | exact GlobalTheory.ConnectionLinear.contrLin_left | (intros; apply GlobalTheory.ConnectionLinear.contrLin_left <;> assumption)
end

