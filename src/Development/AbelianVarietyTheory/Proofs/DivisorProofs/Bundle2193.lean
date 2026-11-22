import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0229
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1932
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1978
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2143
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2177
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2157
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0092
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0078
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0038
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0041
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0061
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.Bundle0004
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0363
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2168
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1200
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleExternalTensorPowerGroupPower
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2182
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2169
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerPreservesSchwartzSpace
section
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory
open scoped Matrix ENNReal

namespace GlobalTheory.ModelTr

theorem extEquiv {V : Type} [AddCommGroup V] [Module ℂ V] (S : Submodule ℂ V) (e : V →ₗ[ℂ] V) (h : Set.BijOn e S S) :
    ∃ T : V ≃ₗ[ℂ] V, (∀ x ∈ S, T x = e x) ∧ ∀ x, x ∈ S ↔ T x ∈ S := by
  obtain ⟨Q, hQ⟩ := Submodule.exists_isCompl S
  let f : V →ₗ[ℂ] V := LinearMap.ofIsCompl hQ (e ∘ₗ S.subtype) Q.subtype
  have dec : ∀ x : V, ∃ s ∈ S, ∃ q ∈ Q, x = s + q := fun x => by
    have : x ∈ S ⊔ Q := by rw [hQ.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨s, hs, q, hq, rfl⟩ := Submodule.mem_sup.1 this
    exact ⟨s, hs, q, hq, rfl⟩
  have hf : ∀ s ∈ S, ∀ q ∈ Q, f (s + q) = e s + q := fun s hs q hq => by
    rw [map_add, LinearMap.ofIsCompl_apply_left hQ (⟨s, hs⟩ : S), LinearMap.ofIsCompl_apply_right hQ (⟨q, hq⟩ : Q)]
    rfl
  have hdisj : ∀ y ∈ S, y ∈ Q → y = 0 := fun y h1 h2 => by
    have := hQ.inf_eq_bot
    exact (Submodule.mem_bot ℂ).1 (this ▸ Submodule.mem_inf.2 ⟨h1, h2⟩)
  have hmem : ∀ x, x ∈ S ↔ f x ∈ S := by
    intro x
    obtain ⟨s, hs, q, hq, rfl⟩ := dec x
    rw [hf s hs q hq]
    constructor
    · intro hx
      have hq0 : q = 0 := hdisj q (by simpa using S.sub_mem hx hs) hq
      subst hq0
      simpa using h.mapsTo hs
    · intro hx
      have hq0 : q = 0 := hdisj q (by simpa using S.sub_mem hx (h.mapsTo hs)) hq
      subst hq0
      simpa using hs
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker] at hx
    have hxS : x ∈ S := (hmem x).2 (hx ▸ S.zero_mem)
    obtain ⟨s, hs, q, hq, rfl⟩ := dec x
    have hq0 : q = 0 := hdisj q (by simpa using S.sub_mem hxS hs) hq
    subst hq0
    rw [add_zero] at hx ⊢
    have h0 := hf s hs 0 Q.zero_mem
    rw [add_zero, add_zero] at h0
    rw [h0] at hx
    exact h.injOn hs S.zero_mem (by rw [hx, map_zero])
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨s', hs', q, hq, rfl⟩ := dec y
    obtain ⟨s, hs, rfl⟩ := h.surjOn hs'
    exact ⟨s + q, hf s hs q hq⟩
  refine ⟨LinearEquiv.ofBijective f ⟨hinj, hsurj⟩, fun x hx => ?_, hmem⟩
  show f x = e x
  have := hf x hx 0 Q.zero_mem
  rwa [add_zero, add_zero] at this

theorem adm_congr {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {l l' : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ}
    (h : ∀ Φ ∈ schA F κ, l Φ = l' Φ) : l ∈ (adeleClass F).adm κ ↔ l' ∈ (adeleClass F).adm κ := by
  have key : ∀ {l l' : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ}, (∀ Φ ∈ schA F κ, l Φ = l' Φ) →
      l ∈ (adeleClass F).adm κ → l' ∈ (adeleClass F).adm κ := by
    intro l l' h hl g hg
    obtain ⟨T, hT⟩ := hl g hg
    exact ⟨T, fun f => (h _ (Submodule.subset_span ⟨f, g, hg, rfl⟩)).symm.trans (hT f)⟩
  exact ⟨key h, key fun Φ hΦ => (h Φ hΦ).symm⟩

theorem exists_isWeil_trans : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ M₁ : Model σ X W, M₁.IsGood B.ψ → ∀ e : Fn F n d →ₗ[ℂ] Fn F n d, IsEv B M M₁ 1 1 ∅ e → Set.BijOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _) → ∃ om₁ : Rep σ X W, M₁.IsWeil B.ψ χX χW om₁ ∧ ∀ x, ∀ Φ ∈ schA F (Fin n × Fin d), e (om x Φ) = om₁ x (e Φ) := by
  intro hP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hpair M₁ hM₁ e hev hbij
  obtain ⟨T, hTe, hTs⟩ := extEquiv (schA F (Fin n × Fin d)) e hbij
  have h1 : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have h1' : incM F (1 : Matrix (Fin d) (Fin d) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have hgood : IsGoodInt (adeleClass F) B.ψ M.co M₁.co T := by
    refine ⟨hTs, fun w Φ hΦ => ?_, fun l => ?_, fun μ hμ => ?_⟩
    · have hm : M.co.rho B.ψ w Φ ∈ schA F (Fin n × Fin d) :=
        GlobalTheory.T.schroedinger_preserves_adelic_schwartz F B.ψ hpair.base.std _ (M.co.e w) Φ hΦ
      have := hev.Heisenberg₂ w Φ hΦ
      rw [h1, h1', Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one] at this
      rw [hTe _ hm, hTe _ hΦ, this]
    · refine (GlobalTheory.T.model_evaluation_bijective_schwartz hP F E σ B n d X W M χX χW om r s r' s' hpair M₁ hM₁ e hev hbij l).trans (adm_congr ?_)
      intro Φ hΦ
      simp [hTe Φ hΦ]
    · obtain ⟨c, hc⟩ := GlobalTheory.T.model_evaluation_preserves_admissible hP F E σ B n d X W M χX χW om r s r' s' hpair M₁ hM₁ e hev hbij μ hμ
      exact ⟨c, fun Φ hΦ => by rw [hTe Φ hΦ]; exact hc Φ hΦ⟩
  refine ⟨trRep T om, isUWeilPair_trRep hgood
    (GlobalTheory.T.model_evaluation_preserves_schwartz hP F E σ B n d X W M χX χW om r s r' s' hpair M₁ hM₁ e hev hbij T hTe)
    (GlobalTheory.T.model_evaluation_intertwines hP F E σ B n d X W M χX χW om r s r' s' hpair M₁ hM₁ e hev hbij T hTe) hpair.weil, fun x Φ hΦ => ?_⟩
  have hpres : om x Φ ∈ schA F (Fin n × Fin d) := hpair.weil.isUSplitting.pres x Φ hΦ
  rw [trRep_apply, ← hTe Φ hΦ, LinearEquiv.symm_apply_apply, hTe _ hpres]

end GlobalTheory.ModelTr

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfRestrictionsVanish
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
open MeasureTheory Formalism.L2.Theta Formalism.BasicNotions.TH ReciprocityTheory.ChartRestriction.G.FD Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped Topology TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IntWtRead

open Formalism.L2.Pj

theorem wtAllZ_of_borChart {K : Type} [Field K] {ι : Type} [Fintype ι]
    {pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type}
    {mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T], (S →ₐ[K] T) → pts S → pts T → Prop}
    {borR : ∀ {S : Type} [CommRing S] [Algebra K S], (ι → Sˣ) → pts S → pts S → Prop}
    (h : BorChart pts mapR borR) (e : ι → ℤ) {f : Rules pts} (hf : IsNatural pts mapR f)
    (hw : ∀ (p : TRing K) (t : ι → (p.R)ˣ) (y y' : pts p.R), borR t y y' →
      f p y' = ((∏ i, t i ^ e i : (p.R)ˣ) : p.R) * f p y)
    (S : Type) [CommRing S] [Algebra K S] (t : ι → Sˣ) (y y' : pts S) (hy : FromTest pts mapR y)
    (hy' : FromTest pts mapR y') (hb : borR t y y') :
    evalAt pts mapR f y' = ((∏ i, t i ^ e i : Sˣ) : S) * evalAt pts mapR f y := by
  unfold evalAt
  rw [dif_pos hy, dif_pos hy']
  apply eq_of_locM (K := K)
  intro m hm
  obtain ⟨A, u, c, c', B, uB, uB', tB, π, π', cB, hc, hc', hπ, hπ', hbB, e1, e2, e3⟩ := h S t y y' hb m
  rw [map_mul, chartAt_val hf hc' hy'.choose_spec.choose_spec.choose_spec,
    chartAt_val hf hc hy.choose_spec.choose_spec.choose_spec, ← e1, ← e2, AlgHom.comp_apply, AlgHom.comp_apply,
    ← hf A B π u uB hπ, ← hf A B π' u uB' hπ', hw B tB uB uB' hbB, map_mul]
  congr 1
  have hu : ∀ i, Units.map (cB : B.R →* Localization.AtPrime m) (tB i)
      = Units.map ((locM K m : S →ₐ[K] Localization.AtPrime m) : S →* Localization.AtPrime m) (t i) :=
    fun i => Units.ext (by simpa using e3 i)
  have h1 : cB ((∏ i, tB i ^ e i : (B.R)ˣ) : B.R) =
      ((Units.map (cB : B.R →* Localization.AtPrime m) (∏ i, tB i ^ e i) : (Localization.AtPrime m)ˣ) :
        Localization.AtPrime m) := rfl
  have h2 : locM K m ((∏ i, t i ^ e i : Sˣ) : S) =
      ((Units.map ((locM K m : S →ₐ[K] Localization.AtPrime m) : S →* Localization.AtPrime m)
        (∏ i, t i ^ e i) : (Localization.AtPrime m)ˣ) : Localization.AtPrime m) := rfl
  rw [h1, h2, map_prod, map_prod]
  simp only [map_zpow, hu]

end GlobalTheory.IntWtRead

namespace GlobalTheory.IntWtRead

open Formalism.L2.Pj

set_option maxHeartbeats 800000 in

theorem cuspW_eq_zero_of_reading : ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ σ : Y.d.c₂.F →+* ℂ, GoodEmb Y.d.c₂ σ → ∀ (G : WTZ D.host.E) (x : Y.V G), (∀ k, ∀ z ∈ ((Y.U σ).X k).dom, rdU (Y.U σ) (x : Rul Y.d.Xo₂ Y.d.c₂) k z = 0) → x = 0 := by
  intro D T j Y e o hY σ hσ G x h0
  have hS : Out.SecBaseChangeSt := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
  have hU := hY.unf σ hσ
  obtain ⟨-, hB, hW, -, -, -, -⟩ := GlobalTheory.T.framedModuli_algebraicLaws_chart_weight_integrality hS _ _ _ _ Y.d.Xo₂ Y.d.c₂
  have hall : AllTest Y.d.Xo₂ Y.d.c₂ := GlobalTheory.T.framedPoint_reduced_from_testRing hS _ _ _ _ Y.d.Xo₂ Y.d.c₂
  have hx : (x : Rul Y.d.Xo₂ Y.d.c₂) ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (exZ _ G) :=
    GlobalTheory.AllWt.cuspW_le_secZ G x.2
  apply Subtype.ext
  funext p y
  show (x : Rul Y.d.Xo₂ Y.d.c₂) p y = 0
  refine eq_zero_of_cpts σ p _ fun ψ => ?_
  obtain ⟨z, hz⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hS _ _ _ _ Y.d.Xo₂ Y.d.c₂ p.R (CAt σ) ψ y
  obtain ⟨k, x', t, ht⟩ := hU.2.2.1 z
  have hft : FromTest (K := Y.d.c₂.F) (fun S _ _ => FrPt Y.d.Xo₂ Y.d.c₂ S) (fun φ y z => FrMap φ y z) z :=
    ⟨p, ψ, y, hz⟩
  have hev : evR Y.d.Xo₂ Y.d.c₂ (x : Rul Y.d.Xo₂ Y.d.c₂) z = ψ ((x : Rul Y.d.Xo₂ Y.d.c₂) p y) := by
    unfold evR evalAt
    rw [dif_pos hft]
    exact hW _ hx.1 (CAt σ) _ p _ ψ _ y z hft.choose_spec.choose_spec.choose_spec hz
  haveI : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ)
  have hw := wtAllZ_of_borChart hB (exZ _ G) hx.1 hx.2 (CAt σ) t _ z (hall _ _) (hall _ _) ht
  have h1 := h0 k x'.1 x'.2
  have h2 : toC (evR Y.d.Xo₂ Y.d.c₂ (x : Rul Y.d.Xo₂ Y.d.c₂) ((Y.U σ).un k x')) = 0 := by
    rw [← h1]
    classical
    show _ = (if h : x'.1 ∈ ((Y.U σ).X k).dom then toC (evR Y.d.Xo₂ Y.d.c₂ (x : Rul Y.d.Xo₂ Y.d.c₂) ((Y.U σ).un k ⟨x'.1, h⟩)) else 0)
    rw [dif_pos x'.2]
  have h3 : evR Y.d.Xo₂ Y.d.c₂ (x : Rul Y.d.Xo₂ Y.d.c₂) ((Y.U σ).un k x') = 0 := h2
  rw [← hev]
  unfold evR
  rw [hw]
  unfold evR at h3
  rw [h3, mul_zero]

end GlobalTheory.IntWtRead
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundedUnitSumComponent
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.FlatUnitProd

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ)
  (Z : Comp Xo c)

def IsBddUnit (G : WTZ E) (s t : Rul Xo c) : Prop :=
  Even G.2 ∧ s ∈ GlobalTheory.AllWt.secZ Xo c (Formalism.L2.Pj.exZ Dw G) ∧ t ∈ GlobalTheory.AllWt.secZ Xo c (-Formalism.L2.Pj.exZ Dw G) ∧
    GlobalTheory.FlatLine.idem Z * s = s ∧ GlobalTheory.FlatLine.idem Z * t = t ∧ s * t = GlobalTheory.FlatLine.idem Z ∧
    (∀ σ, GoodEmb c σ → ∃ C : ℝ, ∀ z ∈ framesOn (U σ) Z,
      GlobalTheory.AllWt.homN (U σ) x G s z ≤ C ∧ GlobalTheory.AllWt.homN (U σ) x (-G) t z ≤ C) ∧
    ∃ m : ℕ, 0 < m ∧ ∀ la, ∀ v ∈ GlobalTheory.FlatLine.valOn Z la, 0 ≤ v ((m : c.F) • s) ∧ 0 ≤ v ((m : c.F) • t)

theorem exZ_zero' : Formalism.L2.Pj.exZ Dw (0 : WTZ E) = 0 := by
  funext i; cases i <;> rfl

theorem exZ_add_eq' (G G' : WTZ E) : Formalism.L2.Pj.exZ Dw (G + G') = Formalism.L2.Pj.exZ Dw G + Formalism.L2.Pj.exZ Dw G' :=
  funext fun i => exZ_add _ _ i

theorem exZ_neg_eq' (G : WTZ E) : Formalism.L2.Pj.exZ Dw (-G) = -Formalism.L2.Pj.exZ Dw G := by
  funext i; cases i <;> rfl

theorem homN_idem_le {σ : c.F →+* ℂ} (V : Unf Xo c σ r) {z} (hz : z ∈ framesOn V Z) :
    GlobalTheory.AllWt.homN V x 0 (GlobalTheory.FlatLine.idem Z) z ≤ 1 := by
  obtain ⟨hd, hl⟩ := hz
  rcases eq_or_ne (GlobalTheory.AllWt.homN V x 0 (GlobalTheory.FlatLine.idem Z) z) 0 with h | h
  · rw [h]; exact zero_le_one
  · rw [GlobalTheory.FlatLine.homN_idem V x hd hl (GlobalTheory.FlatLine.tested_of_homN_ne V x hd h)]

theorem isBddUnit_zero : IsBddUnit U x Z 0 (GlobalTheory.FlatLine.idem Z) (GlobalTheory.FlatLine.idem Z) := by
  have hm : GlobalTheory.FlatLine.idem Z ∈ GlobalTheory.AllWt.secZ Xo c (Formalism.L2.Pj.exZ Dw (0 : WTZ E)) := by
    rw [exZ_zero']; exact GlobalTheory.FlatLine.idem_mem_secZ Z
  refine ⟨by simp, hm, by rwa [exZ_zero', neg_zero, ← exZ_zero' (Dw := Dw)], GlobalTheory.FlatLine.idem_mul_idem Z,
    GlobalTheory.FlatLine.idem_mul_idem Z, GlobalTheory.FlatLine.idem_mul_idem Z, fun σ _ => ⟨1, fun z hz => ?_⟩, 1, one_pos,
    fun la v hv => ?_⟩
  · rw [neg_zero]; exact ⟨homN_idem_le x Z (U σ) hz, homN_idem_le x Z (U σ) hz⟩
  · rw [Nat.cast_one, one_smul, GlobalTheory.FlatLine.val_idem hv]; exact ⟨le_rfl, le_rfl⟩

variable {U x Z}

theorem IsBddUnit.mul {G G' : WTZ E} {s t s' t' : Rul Xo c} (h : IsBddUnit U x Z G s t)
    (h' : IsBddUnit U x Z G' s' t') : IsBddUnit U x Z (G + G') (s * s') (t * t') := by
  obtain ⟨hG, hs, ht, his, hit, hst, hb, m, hm, hv⟩ := h
  obtain ⟨hG', hs', ht', his', hit', hst', hb', m', hm', hv'⟩ := h'
  refine ⟨hG.add hG', ?_, ?_, by rw [← mul_assoc, his], by rw [← mul_assoc, hit], ?_,
    fun σ hσ => ?_, m * m', Nat.mul_pos hm hm', fun la v hw => ?_⟩
  · rw [exZ_add_eq']; exact GlobalTheory.AllWt.mul_mem_secZ hs hs'
  · rw [exZ_add_eq', neg_add]; exact GlobalTheory.AllWt.mul_mem_secZ ht ht'
  · rw [mul_mul_mul_comm, hst, hst', GlobalTheory.FlatLine.idem_mul_idem]
  · obtain ⟨C, hC⟩ := hb σ hσ
    obtain ⟨C', hC'⟩ := hb' σ hσ
    refine ⟨max C 0 * max C' 0, fun z hz => ⟨?_, ?_⟩⟩
    · rw [GlobalTheory.AllWt.homN_mul (U σ) x hG hG' s s' z hz.1]
      exact mul_le_mul ((hC z hz).1.trans (le_max_left _ _)) ((hC' z hz).1.trans (le_max_left _ _))
        (GlobalTheory.AllWt.homN_nonneg _ _ _ _ _) (le_max_right _ _)
    · rw [neg_add, GlobalTheory.AllWt.homN_mul (U σ) x (G := -G) (G' := -G') hG.neg hG'.neg t t' z hz.1]
      exact mul_le_mul ((hC z hz).2.trans (le_max_left _ _)) ((hC' z hz).2.trans (le_max_left _ _))
        (GlobalTheory.AllWt.homN_nonneg _ _ _ _ _) (le_max_right _ _)
  · have hV := GlobalTheory.FlatLine.isVal_valOn hw
    rw [Nat.cast_mul, ← smul_mul_smul_comm, ← smul_mul_smul_comm, hV.mul, hV.mul]
    exact ⟨add_nonneg (hv la v hw).1 (hv' la v hw).1, add_nonneg (hv la v hw).2 (hv' la v hw).2⟩

theorem IsBddUnit.swap {G : WTZ E} {s t : Rul Xo c} (h : IsBddUnit U x Z G s t) : IsBddUnit U x Z (-G) t s := by
  obtain ⟨hG, hs, ht, his, hit, hst, hb, m, hm, hv⟩ := h
  refine ⟨hG.neg, by rwa [exZ_neg_eq'], by rwa [exZ_neg_eq', neg_neg], hit, his,
    by rw [mul_comm, hst], fun σ hσ => ?_, m, hm, fun la v hw => (hv la v hw).symm⟩
  obtain ⟨C, hC⟩ := hb σ hσ
  exact ⟨C, fun z hz => ⟨(hC z hz).2, by rw [neg_neg]; exact (hC z hz).1⟩⟩

theorem exists_nsmul {G : WTZ E} {s t : Rul Xo c} (h : IsBddUnit U x Z G s t) (k : ℕ) :
    ∃ s' t' : Rul Xo c, IsBddUnit U x Z (k • G) s' t' := by
  induction k with
  | zero => exact ⟨_, _, by rw [zero_nsmul]; exact isBddUnit_zero U x Z⟩
  | succ k ih =>
    obtain ⟨s', t', h'⟩ := ih
    exact ⟨_, _, by rw [succ_nsmul]; exact h'.mul h⟩

theorem exists_zsmul {G : WTZ E} {s t : Rul Xo c} (h : IsBddUnit U x Z G s t) (n : ℤ) :
    ∃ s' t' : Rul Xo c, IsBddUnit U x Z (n • G) s' t' := by
  cases n with
  | ofNat k =>
    obtain ⟨s', t', h'⟩ := exists_nsmul h k
    exact ⟨s', t', by rw [Int.ofNat_eq_natCast, natCast_zsmul]; exact h'⟩
  | negSucc k =>
    obtain ⟨s', t', h'⟩ := exists_nsmul h (k + 1)
    exact ⟨t', s', by rw [negSucc_zsmul]; exact h'.swap⟩

theorem exists_sum {ι : Type} (G : ι → WTZ E) (hu : ∀ i, ∃ s t : Rul Xo c, IsBddUnit U x Z (G i) s t)
    (n : ι → ℤ) (S : Finset ι) : ∃ s t : Rul Xo c, IsBddUnit U x Z (∑ i ∈ S, n i • G i) s t := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨_, _, by rw [Finset.sum_empty]; exact isBddUnit_zero U x Z⟩
  | insert a S ha ih =>
    obtain ⟨s, t, h⟩ := ih
    obtain ⟨s₀, t₀, h₀⟩ := hu a
    obtain ⟨s₁, t₁, h₁⟩ := exists_zsmul h₀ (n a)
    exact ⟨_, _, by rw [Finset.sum_insert ha]; exact h₁.mul h⟩

end GlobalTheory.FlatUnitProd

open GlobalTheory.FlatUnitProd in

theorem GlobalTheory.FlatUnitProd.exists_unit_sum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (Z : Comp Xo c) (ι : Type) [Fintype ι] (G : ι → WTZ E), (∀ i, Even (G i).2) → (∀ i, ∃ s t : Rul Xo c, (s ∈ GlobalTheory.AllWt.secZ Xo c (Formalism.L2.Pj.exZ Dw (G i)) ∧ t ∈ GlobalTheory.AllWt.secZ Xo c (-Formalism.L2.Pj.exZ Dw (G i)) ∧ GlobalTheory.FlatLine.idem Z * s = s ∧ GlobalTheory.FlatLine.idem Z * t = t ∧ s * t = GlobalTheory.FlatLine.idem Z ∧ (∀ σ, GoodEmb c σ → ∃ C : ℝ, ∀ z ∈ framesOn (U σ) Z, GlobalTheory.AllWt.homN (U σ) (x) (G i) s z ≤ C ∧ GlobalTheory.AllWt.homN (U σ) (x) (-(G i)) t z ≤ C)) ∧ ∃ m : ℕ, 0 < m ∧ ∀ la, ∀ v ∈ GlobalTheory.FlatLine.valOn Z la, 0 ≤ v ((m : c.F) • s) ∧ 0 ≤ v ((m : c.F) • t)) → ∀ n : ι → ℤ, ∃ s t : Rul Xo c, (s ∈ GlobalTheory.AllWt.secZ Xo c (Formalism.L2.Pj.exZ Dw (∑ i, n i • G i)) ∧ t ∈ GlobalTheory.AllWt.secZ Xo c (-Formalism.L2.Pj.exZ Dw (∑ i, n i • G i)) ∧ GlobalTheory.FlatLine.idem Z * s = s ∧ GlobalTheory.FlatLine.idem Z * t = t ∧ s * t = GlobalTheory.FlatLine.idem Z ∧ (∀ σ, GoodEmb c σ → ∃ C : ℝ, ∀ z ∈ framesOn (U σ) Z, GlobalTheory.AllWt.homN (U σ) (x) (∑ i, n i • G i) s z ≤ C ∧ GlobalTheory.AllWt.homN (U σ) (x) (-(∑ i, n i • G i)) t z ≤ C)) ∧ ∃ m : ℕ, 0 < m ∧ ∀ la, ∀ v ∈ GlobalTheory.FlatLine.valOn Z la, 0 ≤ v ((m : c.F) • s) ∧ 0 ≤ v ((m : c.F) • t) := by
  intro E _ _ _ H Dw l Xo c r U x Z ι _ G hev hu n
  have hu' : ∀ i, ∃ s t : Rul Xo c, IsBddUnit U x Z (G i) s t := fun i => by
    obtain ⟨s, t, ⟨h1, h2, h3, h4, h5, h6⟩, m, hm, hv⟩ := hu i
    exact ⟨s, t, hev i, h1, h2, h3, h4, h5, h6, m, hm, hv⟩
  obtain ⟨s, t, -, h1, h2, h3, h4, h5, h6, m, hm, hv⟩ := exists_sum G hu' n Finset.univ
  exact ⟨s, t, ⟨h1, h2, h3, h4, h5, h6⟩, m, hm, hv⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedPointSpecializesInOpenOfFiniteTypeStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_closedPoint_specializes_in_open_of_finiteType : ∀ (k : Type) [Field k] (X : Scheme.{0}) (q : X ⟶ Sp k) [LocallyOfFiniteType q] (U : X.Opens) (y : X), y ∈ U → ∃ x : X, IsClosed ({x} : Set X) ∧ y ⤳ x ∧ x ∈ U := by
  first | exact @GlobalTheory.closedPoint_specializing_in_open | exact GlobalTheory.closedPoint_specializing_in_open | (intros; apply GlobalTheory.closedPoint_specializing_in_open <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComponentIntegralFramedPointLiesOn
section
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum

namespace GlobalTheory.IntFrComp

open AlgebraicGeometry

theorem exists_liesOn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), ∃ Z : Comp Xo c, (letI := io.toAlgebra; LiesOn Z y.1) := by
  intro E _ _ _ H Dw l Xo c T io y
  letI := io.toAlgebra
  let s₀ : Sp T.Fr := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum T.Fr)
  refine ⟨⟨irreducibleComponent (GlobalTheory.AllWt.ptF y.1 s₀), irreducibleComponent_mem_irreducibleComponents _⟩,
    fun s => ?_⟩
  obtain rfl : s = s₀ := Subsingleton.elim (α := PrimeSpectrum T.Fr) s s₀
  exact mem_irreducibleComponent

end GlobalTheory.IntFrComp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtendMulSimplePoleOfVanishing
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.LogCanonicalReflexive

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k}

theorem fun_ext_ger_of_dense [IsReduced Y] {O W : Y.Opens} (hO : Dense (O : Set Y)) {a b : Γ(Y, W)}
    (h : ∀ z (hz : z ∈ W), z ∈ O → ger z hz a = ger z hz b) : a = b := by
  refine sub_eq_zero.1 (eq_zero_of_basicOpen_eq_bot _ ?_)
  by_contra hne
  obtain ⟨z, hz, hzO⟩ := hO.inter_open_nonempty (Y.basicOpen (a - b)) (Y.basicOpen (a - b)).isOpen
    ((Opens.ne_bot_iff_nonempty _).1 hne)
  have hzW : z ∈ W := Y.basicOpen_le _ hz
  have hu : IsUnit (ger z hzW (a - b)) := (Y.mem_basicOpen _ z hzW).1 hz
  rw [map_sub, h z hzW hzO, sub_self] at hu
  exact not_isUnit_zero hu

theorem exists_extend_of_dense [IsReduced Y] {O : Y.Opens} (hO : Dense (O : Set Y)) {N : LB Y} (hN : N.IsLB)
    (f : H0 p N O) (h : ∀ y, ∃ (W : Y.Opens) (_ : y ∈ W) (i : N.ι) (hi : W ≤ N.U i) (w : Γ(Y, W)),
      ∀ z (hz : z ∈ W) (ho : z ∈ O), ger z hz w = H0.germ i z ho (hi hz) f) :
    ∃ G : H0 p N ⊤, H0.restr le_top G = f := by
  choose W hW c hc w hw using h
  obtain ⟨G, hG⟩ := H0.exists_of_germs (p := p) (O := ⊤) hN W c (fun _ => le_top) hc
    (fun y _ => ⟨y, hW y⟩) w fun y t t' hy hy' => by
      have e : resG Y (inf_le_left : W t ⊓ W t' ≤ W t) (w t) =
          resG Y (inf_le_inf (hc t) (hc t')) (N.g (c t) (c t')).val *
            resG Y (inf_le_right : W t ⊓ W t' ≤ W t') (w t') :=
        fun_ext_ger_of_dense hO fun z hz ho => by
          rw [map_mul, ger_resG, ger_resG, ger_resG, hw t z hz.1 ho, hw t' z hz.2 ho,
            H0.germ_change (c t) (c t') z ho _ (hc t' hz.2), val_tr N z (memInf (hc t hz.1) (hc t' hz.2))]
      have e' := congrArg (ger y (memInf hy hy')) e
      rw [map_mul, ger_resG, ger_resG, ger_resG] at e'
      rw [val_tr N y (memInf (hc t hy) (hc t' hy'))]
      exact e'
  refine ⟨G, H0.ext_germ fun y hy => ⟨c y, hc y (hW y), ?_⟩⟩
  rw [H0.germ_restr, ← hw y y (hW y) hy]
  exact hG y y (hW y)

theorem exists_extend_mul_of_simplePole : ∀ {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} [IsReduced Y] {O : Y.Opens}, Dense (O : Set Y) → ∀ {P B N : LB Y} (C : ProdChart P B N) (ω : H0 p P O), GlobalTheory.LogCanonicalReflexive.SimplePoleAlong O C ω → ∀ g : H0 p B ⊤, (∀ y, y ∉ O → ∀ i hi, H0.germ i y (memTop y) hi g ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y)) → ∃ G : H0 p N ⊤, H0.restr le_top G = C.mul ω (H0.restr le_top g) := by
  intro k _ Y p _ O hO P B N C ω hω g hg
  refine exists_extend_of_dense hO C.isLB₃ _ fun y => ?_
  by_cases hy : y ∈ O
  · obtain ⟨t, -, -, hc⟩ := C.cover y
    exact ⟨O ⊓ N.U (C.c t), ⟨hy, hc⟩, C.c t, inf_le_right, H0.loc _ _, fun z hz ho => rfl⟩
  obtain ⟨V, hyV, τ, ha, hb, hc, t, u, -, -, hdiv, htu⟩ := hω y hy
  let gl : Γ(Y, V) := resG Y (le_inf le_top hb) (g.loc (C.b τ))
  have hgl (z) (hz : z ∈ V) : ger z hz gl = H0.germ (C.b τ) z (memTop z) (hb hz) g := ger_resG _ _ _ _
  clear_value gl
  obtain ⟨h, hh⟩ := hdiv V le_rfl gl (fun z hz ho => hgl z hz ▸ hg z ho _ _) y hyV
  obtain ⟨W₁, hy₁, h₁, rfl⟩ := Y.presheaf.exists_germ_eq h
  have e : ger y (memInf hyV hy₁) (resG Y inf_le_left gl) =
      ger y (memInf hyV hy₁) (resG Y inf_le_left t * resG Y inf_le_right h₁) := by
    rw [map_mul, ger_resG, ger_resG, ger_resG]
    exact hh
  obtain ⟨W, hyW, i₁, i₂, e'⟩ := Y.presheaf.germ_eq y _ _ _ _ e
  have hWV : W ≤ V := i₁.le.trans inf_le_left
  have hW₁ : W ≤ W₁ := i₁.le.trans inf_le_right
  refine ⟨W, hyW, C.c τ, hWV.trans hc, resG Y hWV u * resG Y hW₁ h₁, fun z hz ho => ?_⟩
  have e₂ : ger z hz (resG Y i₁.le (resG Y inf_le_left gl)) =
      ger z hz (resG Y i₂.le (resG Y inf_le_left t * resG Y inf_le_right h₁)) := congrArg (ger z hz) e'
  rw [ger_resG, ger_resG, ger_resG, map_mul, ger_resG, ger_resG, hgl] at e₂
  rw [C.germ_mul _ _ τ z ho (ha (hWV hz)) (hb (hWV hz)), H0.germ_restr, map_mul, ger_resG, ger_resG,
    ← htu z (hWV hz) ho]
  refine Eq.trans ?_ (congrArg (_ * ·) e₂.symm)
  ring

end GlobalTheory.LogCanonicalReflexive
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameTangentVectorsOfIsGrpPullbackStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frame_tangentVectors_of_isGrpPullback : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {K : Type} [Field K] [Algebra c.F K] (y : FrPt Xo c K) {A : Over (Sp K)} [GrpObj A] {π : A.left ⟶ Xo.univ.t.G.left}, IsGrpPullback A Xo.univ.t.G y.x π → ∀ (a : OAct (𝓞 E) A), (∀ z, (a.act z).left ≫ π = π ≫ (Xo.univ.t.act.act z).left) → ∃ ub : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → (epsR K ⟶ A), (∀ σ k, (ub σ k).left ≫ π = y.u σ k) ∧ (∀ σ k, IsTangent (ub σ k)) ∧ (∀ σ k z, ub σ k ≫ a.act z = GlobalTheory.GrpTangent.epsScale (algebraMap c.F K (embK c σ z)) ≫ ub σ k) ∧ ∀ σ (w : epsR K ⟶ A), IsTangent w → (∀ z, w ≫ a.act z = GlobalTheory.GrpTangent.epsScale (algebraMap c.F K (embK c σ z)) ≫ w) → ∃ cf, IsLieComb cf (ub σ) w := by
  first | exact @GlobalTheory.KSExist.exists_frame_of_isGrpPullback | exact GlobalTheory.KSExist.exists_frame_of_isGrpPullback | (intros; apply GlobalTheory.KSExist.exists_frame_of_isGrpPullback <;> assumption)
end

