import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0144
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0125
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0494
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0497
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0434
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0002
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0216
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0264
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0462
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0189
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0325
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousIntegrand
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.Bundle0013
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.Bundle0012
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0189
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.AmbIsTrueOfAmbTrue
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldNormBaseTermTranslate
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.Unf

theorem mt_mem_GQ_rat' {D : D7} (V : HSp D) {γ : GA D V} (hγ : γ ∈ GQ V) :
    ∃ M : Matrix (Fin V.rank) (Fin V.rank) D.host.E, mt V γ = rat M := by
  simp only [GQ, HFinIn, HFin, Subgroup.mem_subgroupOf] at hγ
  obtain ⟨u, -, hu⟩ := hγ
  exact ⟨u.1, (congrArg Units.val hu).symm⟩

set_option maxHeartbeats 1000000 in

theorem unfold_norm_base_term_translate : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (χV χW : (AE D)ˣ →* Circle) (om : Om V W) (om' : Om V₀ W), IsWeilDatumO ψ V W χV χW om → IsWeilDatumO ψ V₀ W χV χW om' → ∀ (vS : VolM D W.rank ρ) (vN : VolN d) (vW : Vol W) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E), IsBase W x₀ → ∀ (G : GA D W → ℂ) (Φ : WO V W → ℂ), RapidDec W G → IsThetaFunO ψ V W Φ → ∀ (𝓐 : Set (flagN d)) (𝓑 : Set (GA D W)), IsFundamentalDomain ((GQ V ⊓ radX d).subgroupOf (flagN d)) 𝓐 vN.ν → IsFundamentalDomain (GQ W ⊓ Rgrp W (rat x₀) : Subgroup (GA D W)) 𝓑 vW.μ → ∀ g : GA D V, ∫⁻ p in 𝓐 ×ˢ 𝓑, ‖G p.2 * term ψ d W vS (om (p.1.1 * g, p.2) Φ) x₀‖ₑ ∂(vN.ν.prod vW.μ) = ∫⁻ p in vN.𝓝 ×ˢ vW.𝓕, ∑' y : Orb W x₀, ‖G p.2 * term ψ d W vS (om (p.1.1 * g, p.2) Φ) y.1‖ₑ ∂(vN.ν.prod vW.μ) := by
  intro D ψ V V₀ W ρ d χV χW om om' hω hω' vS vN vW x₀ hx G Φ hG hΦ 𝓐 𝓑 h𝓐 h𝓑 g
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  obtain ⟨c1, c2, c3, c4⟩ := GlobalTheory.Mem.TrueRecord.top_NFlag V (GlobalTheory.MixPer.isIsoSub_e d)
  obtain ⟨hN1, hN2, hN3⟩ := vN.unit
  haveI := vW.haar
  haveI : SFinite vN.ν := inferInstance
  haveI : SFinite vW.μ := inferInstance
  obtain ⟨act, y₀, hy₀, hrel, htrans, hstab1, hstab2⟩ := GlobalTheory.T.flagUnitaryOrbitAction_transitive_with_stabilizer D V V₀ W ρ d x₀ hx
  letI := act
  haveI : Countable D.host.E := (Module.finBasis ℚ D.host.E).equivFun.injective.countable
  haveI : Countable (Matrix (Fin W.rank) (Fin ρ) D.host.E) := inferInstanceAs (Countable (Fin _ → Fin _ → _))
  haveI hΓc : Countable ((NFlagQ V d.e).prod (GQ W)) := Function.Injective.countable
    (f := fun γ : (NFlagQ V d.e).prod (GQ W) => ((⟨γ.1.1, (Subgroup.mem_prod.1 γ.2).1⟩ : NFlagQ V d.e),
      (⟨γ.1.2, (Subgroup.mem_prod.1 γ.2).2⟩ : GQ W)))
    fun a b h => by
      simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
      exact Subtype.ext (Prod.ext h.1 h.2)
  haveI : Countable ((MulAction.stabilizer ((NFlagQ V d.e).prod (GQ W)) y₀).map (Subgroup.subtype _)) :=
    (Subgroup.inclusion_injective (Subgroup.map_subtype_le (MulAction.stabilizer ((NFlagQ V d.e).prod (GQ W)) y₀))).countable
  have hF : IsFundamentalDomain ((NFlagQ V d.e).prod (GQ W)) (vN.𝓝 ×ˢ vW.𝓕) (vN.ν.prod vW.μ) := by
    refine GlobalTheory.T.isFundamentalDomain_prod_of_kernel_image _ _ vN.ν vW.μ _ vN.𝓝 vW.𝓕 ?_ ?_
    · have hc : ((NFlagQ V d.e).prod (GQ W)).comap (MonoidHom.inl (flagN d) (GA D W)) = NFlagQ V d.e := by
        ext n
        simp only [Subgroup.mem_comap, MonoidHom.inl_apply, Subgroup.mem_prod, one_mem, and_true]
      rw [hc]; exact hN2
    · have hc : ((NFlagQ V d.e).prod (GQ W)).map (MonoidHom.snd (flagN d) (GA D W)) = GQ W := by
        ext h
        constructor
        · rintro ⟨p, hp, rfl⟩
          exact (Subgroup.mem_prod.1 hp).2
        · intro hh
          exact ⟨(1, h), Subgroup.mem_prod.2 ⟨one_mem _, hh⟩, rfl⟩
      rw [hc]; exact vW.fund
  have hG' : IsFundamentalDomain ((MulAction.stabilizer ((NFlagQ V d.e).prod (GQ W)) y₀).map (Subgroup.subtype _))
      (𝓐 ×ˢ 𝓑) (vN.ν.prod vW.μ) := by
    refine GlobalTheory.T.isFundamentalDomain_prod_of_kernel_image _ _ vN.ν vW.μ _ 𝓐 𝓑 ?_ ?_
    · rw [hstab1]; exact h𝓐
    · rw [hstab2]; exact h𝓑
  have hmeas : ∀ y : Orb W x₀, Measurable fun p : flagN d × GA D W =>
      G p.2 * term ψ d W vS (om (p.1.1 * g, p.2) Φ) y.1 := by
    intro y
    have t4 := (GlobalTheory.T.mixedThetaSeries_terms_laws_unipotent_rational D ψ V V₀ W ρ d χV χW om om' hω hω' vS Φ hΦ).2.2.2.1 y.1
    refine Continuous.measurable ?_
    refine (hG.2.1.comp continuous_snd).mul ?_
    exact t4.comp (((continuous_subtype_val.comp continuous_fst).mul continuous_const).prodMk continuous_snd)
  have hinv : ∀ (γ : (NFlagQ V d.e).prod (GQ W)) (y : Orb W x₀) (p : flagN d × GA D W),
      G ((γ : flagN d × GA D W) * p).2 *
        term ψ d W vS (om (((γ : flagN d × GA D W) * p).1.1 * g, ((γ : flagN d × GA D W) * p).2) Φ) (γ • y).1 =
      G p.2 * term ψ d W vS (om (p.1.1 * g, p.2) Φ) y.1 := by
    intro γ y p
    have hmem := Subgroup.mem_prod.1 γ.2
    have hq1 : ((γ.1.1 : flagN d) : GA D V) ∈ GQ V := hmem.1
    have hq2 : γ.1.2 ∈ GQ W := hmem.2
    obtain ⟨M, hM⟩ := mt_mem_GQ_rat' W hq2
    have hΨ := hω.om_pres (p.1.1 * g, p.2) Φ hΦ
    have hΨ' := hω.om_pres (1, γ.1.2) _ hΨ
    have key : term ψ d W vS (om ((γ.1.1 : GA D V) * p.1.1 * g, γ.1.2 * p.2) Φ) (γ • y).1 =
        term ψ d W vS (om (p.1.1 * g, p.2) Φ) y.1 := by
      have hsplit : ((γ.1.1 : GA D V) * p.1.1 * g, γ.1.2 * p.2) =
          (((γ.1.1 : GA D V), 1) * ((1 : GA D V), γ.1.2)) * (p.1.1 * g, p.2) := by
        ext <;> simp [mul_assoc]
      rw [hsplit, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
      have t2 := (GlobalTheory.T.mixedThetaSeries_terms_laws_unipotent_rational D ψ V V₀ W ρ d χV χW om om' hω hω' vS _ hΨ').2.1
      have t3 := (GlobalTheory.T.mixedThetaSeries_terms_laws_unipotent_rational D ψ V V₀ W ρ d χV χW om om' hω hω' vS _ hΨ).2.2.1
      have e1 : (rat (M * y.1) : Mx D W.rank ρ) = rat (γ • y).1 ⬝ blockX d (γ.1.1 : GA D V) := by
        rw [hrel γ y, hM, rat_mul]
      rw [t2 _ hq1 γ.1.1.2 (γ • y).1 (M * y.1) e1, t3 _ hq2 (M * y.1) y.1 (by rw [hM, rat_mul])]
    have hGG : G (γ.1.2 * p.2) = G p.2 := hG.1 _ hq2 p.2
    show G (γ.1.2 * p.2) *
        term ψ d W vS (om ((γ.1.1 : GA D V) * p.1.1 * g, γ.1.2 * p.2) Φ) (γ • y).1 = _
    exact congrArg₂ (· * ·) hGG key
  obtain ⟨hl, -⟩ := GlobalTheory.T.lintegral_unfold_sum_transitive_orbit (flagN d × GA D W) (vN.ν.prod vW.μ) ((NFlagQ V d.e).prod (GQ W)) (Orb W x₀) y₀ htrans
    (vN.𝓝 ×ˢ vW.𝓕) (𝓐 ×ˢ 𝓑) hF hG'
    (fun y p => G p.2 * term ψ d W vS (om (p.1.1 * g, p.2) Φ) y.1) hmeas hinv
  simp only [hy₀] at hl
  exact hl

end GlobalTheory.Unf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilChartScalarAction
section
open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RegSch

theorem pass_isWeilSch : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A T : HSp D) (χ : (AE D)ˣ →* Circle) (om : GA D (dblSp A) × GA D T →* Module.End ℂ (WO (dblSp A) T → ℂ)) (ν : Measure (WO A T)) (𝓨 : Set (WO A T)) (μ : D.host.E) (κ : GA D (dblSp A) ≃* GlobalTheory.StdUnn.G D A.rank) (omS : GlobalTheory.StdUnn.G D A.rank →* Module.End ℂ (schwartzA θ T.rank A.rank)), Pass ψ θ A T χ om ν 𝓨 μ κ omS → ∀ lam : D.host.F, algebraMap D.host.F D.host.E lam = -D.host.xi0 / μ → GlobalTheory.StdUnn.IsWeilSch (GlobalTheory.StdUnn.shift ψ lam) χ⁻¹ θ T ν omS := by
  intro D ψ θ A T χ om ν 𝓨 μ κ omS hP lam hlam
  exact
    { levi := GlobalTheory.StdUnn.transport_levi D ψ A T χ om hP.weil ν 𝓨 hP.cov θ hP.inf μ hP.skew κ hP.chart omS hP.trans lam hlam
      unip := GlobalTheory.StdUnn.Unip.transport_unip D ψ A T χ om hP.weil ν 𝓨 hP.cov θ hP.inf μ hP.skew κ hP.chart omS hP.trans lam hlam
      weyl := GlobalTheory.StdUnn.WeylStd.main D ψ A T χ om hP.weil ν 𝓨 hP.cov θ hP.inf μ hP.skew κ hP.chart omS hP.trans lam hlam }

end GlobalTheory.RegSch
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepRankZeroWittEmbeddingValueAtZero
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing MeasureTheory GlobalTheory.FinPl.VLast

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.VLast.Transport

section RankZero

variable {D : D7} {S S₀ : HSp D} (d : HypDec S S₀ 0)

theorem rz_gA : gA S = adj d.p0 ⬝ (gA S₀ ⬝ d.p0) := by
  rw [d.gA_eq, Subsingleton.elim d.pX 0, Subsingleton.elim d.pY 0]
  simp

theorem rz_j0p0 : d.j0 ⬝ d.p0 = 1 := by
  have := d.sum_eq_one
  rwa [Subsingleton.elim d.jX 0, Subsingleton.elim d.jY 0, Matrix.zero_mul, Matrix.zero_mul, zero_add, add_zero] at this

theorem unitaryMatrix_rankZeroWittEmbedding_eq (g : GA D S₀) : mt S (d.emb0 g) = d.j0 ⬝ mt S₀ g ⬝ d.p0 := by
  rw [d.unitaryMatrix_wittCoreEmbedding, Subsingleton.elim d.jX 0, Subsingleton.elim d.jY 0]
  simp

theorem rz_unit (g : GA D S) : adj (d.p0 ⬝ mt S g ⬝ d.j0) ⬝ (gA S₀ ⬝ (d.p0 ⬝ mt S g ⬝ d.j0)) = gA S₀ := by
  have key : ∀ X : Mx D S.rank S₀.rank, adj d.p0 ⬝ (gA S₀ ⬝ (d.p0 ⬝ X)) = gA S ⬝ X := fun X => by
    rw [rz_gA d, Matrix.mul_assoc, Matrix.mul_assoc]
  rw [adj_mul, adj_mul]
  simp only [Matrix.mul_assoc]
  rw [key, ← Matrix.mul_assoc (gA S), ← Matrix.mul_assoc (adj (mt S g)), mt_unitary]
  exact d.gram_00

def rzInv (g : GA D S) : GA D S₀ := ofMat S₀ (d.p0 ⬝ mt S g ⬝ d.j0) (rz_unit d g)

theorem mt_rzInv (g : GA D S) : mt S₀ (rzInv d g) = d.p0 ⬝ mt S g ⬝ d.j0 := mt_ofMat _ _ _

def rzEquiv : GA D S₀ ≃* GA D S where
  toFun := d.emb0
  invFun := rzInv d
  left_inv g := mt_injective S₀ (by
    rw [mt_rzInv, unitaryMatrix_rankZeroWittEmbedding_eq]
    simp only [Matrix.mul_assoc, d.p0_j0, Matrix.mul_one]
    rw [← Matrix.mul_assoc, d.p0_j0, Matrix.one_mul])
  right_inv g := mt_injective S (by
    rw [unitaryMatrix_rankZeroWittEmbedding_eq, mt_rzInv]
    simp only [Matrix.mul_assoc, rz_j0p0 d, Matrix.mul_one]
    rw [← Matrix.mul_assoc, rz_j0p0 d, Matrix.one_mul])
  map_mul' := map_mul d.emb0

theorem rzInv_continuous : Continuous (rzInv d) :=
  continuous_of_mt S₀ (by
    simp only [mt_rzInv]
    exact (continuous_const.matrix_mul (continuous_mt S)).matrix_mul continuous_const)

theorem rzInv_mem_GQ {g : GA D S} (hg : g ∈ GQ S) : rzInv d g ∈ GQ S₀ := by
  rw [mem_GQ_iff, mt_rzInv]
  exact ratMx_mul (ratMx_mul (rat_mem _) ((mem_GQ_iff S g).1 hg)) (rat_mem _)

end RankZero

theorem weilRep_rankZeroWittEmbedding_valueAtZero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S S₀ T : HSp D) (d : HypDec S S₀ 0) (χS χT : (AE D)ˣ →* Circle) (om : Om S T) (om₀ : Om S₀ T), IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S₀ T χS χT om₀ → ∀ f, IsThetaFunO ψ S T f → ∀ (g₀ : GA D S₀) (h : GA D T), om (d.emb0 g₀, h) f 0 = om₀ (g₀, h) (fun w => f (d.ext0 T w)) 0 := by
  intro D ψ S S₀ T d χS χT om om₀ hom hom₀ f hf g₀ h
  obtain ⟨μ, 𝓕, hμ⟩ := exists_isCovolOne (D := D) (m := T.rank) (n := 0)
  have hF := GlobalTheory.T.mixedModelFormulasWittSource_proof D ψ S S₀ T 0 d χS χT om om₀ hom hom₀ μ 𝓕 hμ
  have H1 := (hF (om (1, h) f) (hom.om_pres _ _ hf)).core g₀ 0
  have H2 := (hF f hf).target h 0
  rw [mixS_rankZero ψ S S₀ T d μ 𝓕 hμ, mixS_rankZero ψ S S₀ T d μ 𝓕 hμ] at H1
  rw [mixS_rankZero ψ S S₀ T d μ 𝓕 hμ, mixS_rankZero ψ S S₀ T d μ 𝓕 hμ] at H2
  rw [H2] at H1
  have e1 : ((d.emb0 g₀, h) : GA D S × GA D T) = (d.emb0 g₀, 1) * (1, h) := by simp
  have e2 : ((g₀, h) : GA D S₀ × GA D T) = (g₀, 1) * (1, h) := by simp
  have := congrFun H1 0
  simp only [map_zero] at this
  rw [e1, e2, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
  exact this

theorem om_flatBF_rankZero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (B : BesLev D 0) (J : JacLev D 0) (s : StepBF ψ B J) (Ψ : WO B.V J.W → ℂ), IsThetaFunO ψ B.V J.W Ψ → ∀ (h₀ : GA D B.A) (g₀ : GA D J.W₀), s.om (embA B.d B.o h₀, J.d.emb0 g₀) Ψ 0 = s.om₀ (B.o.emb (h₀, 1), g₀) (flatBF s Ψ) 0 := by
  intro D ψ B J s Ψ hΨ h₀ g₀
  have hflat : ∀ X, flatBF s X = evalBF s X := by
    intro X; funext w
    obtain ⟨-, 𝓤, -, h1⟩ := s.vU.unit
    haveI : Subsingleton (UX D 0) := ⟨fun a b => Subtype.ext (Units.ext (Subsingleton.elim _ _))⟩
    have hU : 𝓤 = Set.univ := by
      rcases Set.eq_empty_or_nonempty 𝓤 with he | ⟨x, hx⟩
      · rw [he, measure_empty] at h1; exact absurd h1 zero_ne_one
      · exact Set.eq_univ_of_forall fun y => Subsingleton.elim x y ▸ hx
    have huniv : s.vU.ν Set.univ = 1 := hU ▸ h1
    haveI : IsProbabilityMeasure s.vU.ν := ⟨huniv⟩
    have hc : ∀ u : UX D 0, flatFun ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (xZero J.d) (yZero B.V₀ 0 (vecB B.o B.ζ)) X w u = evalBF s X w := by
      intro u
      simp only [flatFun, evalBF, evalZero]
      rw [Subsingleton.elim (xZero J.d ⬝ u.1.1) (xZero J.d)]
      simp [psiUni, upSum, psiE]
    simp only [flatBF, flat, flatAt, hc, integral_const, probReal_univ, one_smul]
  have hd := GlobalTheory.T.weilDatum_descends_to_wittCore D
  have hm : GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.MixedModelFormulas D := ⟨GlobalTheory.T.mixedModelFormulasWittSource_proof D, GlobalTheory.T.mixedModelFormulas_wittTarget D⟩
  have hv := GlobalTheory.T.mixedCoordinates_of_thetaFunction_are_thetaFunctions D
  rw [hflat, GlobalTheory.Unf.EvalCont.om_evalBF s hd hm hv hΨ h₀ g₀]
  unfold evalBF evalZero evalAt
  rw [mixT_rankZero ψ _ _ _ J.d s.vT.μ s.vT.𝓕 s.vT.covol, mixS_rankZero ψ _ _ _ B.d s.vS.μ s.vS.𝓕 s.vS.covol]
  simp only [map_zero]

end GlobalTheory.FinPl.VLast.Transport

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.XiZeroEmbeddingValue
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk
open scoped TensorProduct Classical
namespace GlobalTheory.AdForm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem xi_zero_embedding_value (D : D7) (hc : D.host.ccK = ⊤) (τ : D.what₂.Tau) :
    tauE D τ D.host.xi0 = Complex.I * ((Real.sqrt D.host.d)⁻¹ : ℝ) := by
  have h1 : tauE D τ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℝ) :=
    ((Formalism.BasicNotions.factEmb D.R D.host).2 _).2 (D.eTau τ).2
  have hd : 0 < Real.sqrt D.host.d := Real.sqrt_pos.2 (Nat.cast_pos.2 D.host.hyp.2.1.pos)
  rw [Host.xi0, hc, Ideal.absNorm_top, map_div₀, map_mul, h1, map_natCast, map_neg, map_one]
  have : ((Real.sqrt D.host.d : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hd.ne'
  push_cast
  field_simp
  simp

theorem stdPair_world {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (hI : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (ψ : AddChar (AF (I.rec7 l Z).host.F) ℂ) (θ : InfFam (I.rec7 l Z)) (hψ : IsStdChar (I.rec7 l Z) ψ (-1)) (hθ : IsInfFam θ)
    (i : ℕ) : StdPair θ ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) I.A.δ I.A.sc ψ := by
  obtain ⟨hs, hX, -⟩ := hI.spaces
  have hg : ∀ j, ((I.rec7 l Z).sp.X j).gram = 1 := fun j => by
    have e : (I.rec7 l Z).sp.X j = Formalism.BasicNotions.Examples₂.posSpace hs (B.R.N j) := hX j
    rw [e]
    refine Matrix.ext fun a b => ?_
    refine (Formalism.BasicNotions.Examples₂.stdSpace_gram_apply hs (B.R.N j) (fun _ => false) (B.R.N j) 0 a b).trans ?_
    by_cases h : a = b
    · subst h
      rw [Matrix.one_apply_eq]
      exact (if_pos rfl).trans (by simp [Formalism.BasicNotions.Examples₂.sgn]; rfl)
    · rw [Matrix.one_apply_ne h]
      exact if_neg h
  have hr : ∀ j, ((I.rec7 l Z).sp.X j).rank = B.R.N j := fun j => by
    have e : (I.rec7 l Z).sp.X j = Formalism.BasicNotions.Examples₂.posSpace hs (B.R.N j) := hX j
    rw [e]; rfl
  have hev : ∀ j, Even (B.R.N j) := fun j =>
    B.R.k_even.add (Even.mul_left (B.R.t_odd.add_one) j)
  have hδ : I.J.δ ≠ 0 := I.J.δ_ne_zero
  have hd : 0 < Real.sqrt B.host.d := Real.sqrt_pos.2 (Nat.cast_pos.2 B.host.hyp.2.1.pos)
  refine ⟨hψ, hθ, hg _, hg _, (I.rec7 l Z).sp.X_sig _, (I.rec7 l Z).sp.X_sig _, ?_, B.ccK_top, hδ,
    xi_zero_embedding_value _ B.ccK_top, ?_⟩
  · rw [hr, hr]
    refine ⟨?_, ?_, hev _, hev _⟩
    · have := B.R.m_add_three_le_k; unfold Ranks.N; omega
    · unfold Ranks.N; nlinarith
  · have hA := Formalism.MainNotions.Ext.area_lamOf (I.rec7 l Z) ⊤ top_ne_bot I.J.δ hδ
    rw [Formalism.MainNotions.Ext.discr_K (I.rec7 l Z).host, Ideal.absNorm_top] at hA
    have hA' : Formalism.MainNotions.TaylorLogMetric.area (Th.lamOf B.host ⊤ I.J.δ) = ‖I.J.δ‖ ^ 2 * Real.sqrt B.host.d / 2 := by
      refine hA.trans ?_
      simp
      exact Or.inl rfl
    show (Formalism.MainNotions.TaylorLogMetric.area (Th.lamOf B.host ⊤ I.J.δ))⁻¹ * ‖I.J.δ‖ ^ 2 = 2 * (Real.sqrt B.host.d)⁻¹
    rw [hA']
    have : ‖I.J.δ‖ ≠ 0 := norm_ne_zero_iff.2 hδ
    field_simp

end GlobalTheory.AdForm
end
end

