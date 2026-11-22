import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0470
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0263
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0035
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0465
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0410
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PinnedLocalGroupsHaveLevel
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0469
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteOrderChartsMiddleSteps
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMemberStepCharts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartLastStepTwistBasePoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0287
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0069
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0181
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0372
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0448
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1393
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0358
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0287
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0270
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0201
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0028
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0481
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0479
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0443
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0459
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteFourierExpansionHalfSplitPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0368
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0071
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0073
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0084
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1151
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0355
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0125
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeCharacterEqAtDetRootsOfCongruent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0471
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0356

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqMulOfValLtOne
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocMod.SplitUnif

section General
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_eq_mul (v : HeightOneSpectrum (𝓞 F)) (T b : 𝓞 F) (h1 : T ∈ v.asIdeal) (h2 : T ∉ v.asIdeal ^ 2)
    (hb : b ∈ v.asIdeal) : ∃ c ∈ v.adicCompletionIntegers F,
      algebraMap F (v.adicCompletion F) (b : F) = algebraMap F (v.adicCompletion F) (T : F) * c := by
  have hT0 : T ≠ 0 := by rintro rfl; exact h2 (zero_mem _)
  have hle : v.intValuation b ≤ v.intValuation T := by
    have h3 := (v.intValuation_le_pow_iff_mem b 1).2 (by simpa using hb)
    refine h3.trans ?_
    by_contra h
    rw [not_le] at h
    apply h2
    rw [← v.intValuation_le_pow_iff_mem]
    have h0 : v.intValuation T ≠ 0 := v.intValuation_ne_zero _ hT0
    rw [← WithZero.exp_log h0] at h ⊢
    rw [WithZero.exp_lt_exp] at h
    rw [WithZero.exp_le_exp]
    omega
  have hTF : (T : F) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.2 hT0
  refine ⟨algebraMap F (v.adicCompletion F) ((b : F) / (T : F)), ?_, ?_⟩
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    have h := v.valuedAdicCompletion_eq_valuation' ((b : F) / (T : F))
    change Valued.v (((b : F) / (T : F) : F) : v.adicCompletion F) ≤ 1
    rw [h, map_div₀]
    have e1 : v.valuation F (b : F) = v.intValuation b := v.valuation_of_algebraMap b
    have e2 : v.valuation F (T : F) = v.intValuation T := v.valuation_of_algebraMap T
    rw [e1, e2]
    exact div_le_one_of_le₀ hle zero_le
  · rw [← map_mul, mul_div_cancel₀ _ hTF]

theorem incl_eq_mul [StarRing E] (hc : CMData F E) (v : HeightOneSpectrum (𝓞 F)) (P : Ideal (𝓞 E))
    (hv : ∀ b : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) b ∈ P → b ∈ v.asIdeal) (T : 𝓞 F) (t t' : 𝓞 E)
    (ht' : (t' : E) = star (t : E)) (htt : t * t' = algebraMap (𝓞 F) (𝓞 E) T) (hco : IsCoprime t t') (ht : t ∈ P)
    (h1 : T ∈ v.asIdeal) (h2 : T ∉ v.asIdeal ^ 2) (a : 𝓞 E) (ha : a ∈ P) :
    ∃ c ∈ intV E v, Formalism.UG.inclE (F := F) (v.adicCompletion F) (a : E) =
      Formalism.UG.inclE (F := F) (v.adicCompletion F) (t : E) * c := by
  have hO : ∀ r : 𝓞 E, Formalism.UG.inclE (F := F) (v.adicCompletion F) (r : E) ∈ intV E v := fun r =>
    Subring.subset_closure (Or.inl ⟨⟨(r : E), r, rfl⟩, rfl⟩)
  have hF : ∀ x : F, Formalism.UG.inclE (F := F) (v.adicCompletion F) (algebraMap F E x) =
      (1 : E) ⊗ₜ[F] algebraMap F (v.adicCompletion F) x := fun x => by
    change (algebraMap F E x) ⊗ₜ[F] (1 : v.adicCompletion F) = _
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one]
  let a' : 𝓞 E := ⟨star (a : E), (RingOfIntegers.isIntegral_coe a).map_of_comp_eq (RingHom.id ℤ) (starRingEnd E)
    (RingHom.ext_int _ _)⟩
  have ha' : (a' : E) = star (a : E) := rfl
  obtain ⟨b₀, hb₀⟩ := (hc.fixed ((t' * a + t * a' : 𝓞 E) : E)).1 (by
    change star ((t' : E) * (a : E) + (t : E) * star (a : E)) = (t' : E) * (a : E) + (t : E) * star (a : E)
    rw [ht', star_add, star_mul', star_mul', star_star, star_star, add_comm])
  have hint : IsIntegral ℤ b₀ := by
    rw [← isIntegral_algebraMap_iff (algebraMap F E).injective, hb₀]
    exact RingOfIntegers.isIntegral_coe _
  let b : 𝓞 F := ⟨b₀, hint⟩
  have hb : algebraMap (𝓞 F) (𝓞 E) b = t' * a + t * a' := RingOfIntegers.ext hb₀
  obtain ⟨c, hc1, hc2⟩ := exists_eq_mul v T b h1 h2
    (hv b (by rw [hb]; exact add_mem (P.mul_mem_left _ ha) (P.mul_mem_right _ ht)))
  have hcV : (1 : E) ⊗ₜ[F] c ∈ intV E v := Subring.subset_closure (Or.inr ⟨⟨c, hc1⟩, rfl⟩)
  obtain ⟨α, β, hαβ⟩ := hco
  set ι := Formalism.UG.inclE (F := F) (E := E) (v.adicCompletion F) with hι
  have e1 : ι t' * ι a + ι t * ι a' = ι t * ι t' * ((1 : E) ⊗ₜ[F] c) := by
    have l : ι t' * ι a + ι t * ι a' = ι (algebraMap F E (b : F)) := by
      rw [← map_mul ι, ← map_mul ι, ← map_add ι]
      exact congrArg ι hb₀.symm
    have r : ι t * ι t' = ι (algebraMap F E (T : F)) := by
      rw [← map_mul ι]
      exact congrArg (fun z : 𝓞 E => ι (z : E)) htt
    rw [l, r, hF, hF, hc2, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  have e2 : ι α * ι t + ι β * ι t' = 1 := by
    rw [← map_mul ι, ← map_mul ι, ← map_add ι, ← map_one ι]
    exact congrArg (fun z : 𝓞 E => ι (z : E)) hαβ
  refine ⟨ι α * ι a + ι β * (ι t' * ((1 : E) ⊗ₜ[F] c) - ι a'),
    add_mem (mul_mem (hO _) (hO _)) (mul_mem (hO _) (sub_mem (mul_mem (hO _) hcV) (hO _))), ?_⟩
  linear_combination (-(ι a)) * e2 + ι β * e1

end General

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem eq_mul_of_val_lt_one : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : GlobalTheory.FinPl.SplitPt D k) (P : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt p.e P → ∀ (T : ℕ) (t t' : 𝓞 D.host.E), (t' : D.host.E) = star (t : D.host.E) → t * t' = (T : 𝓞 D.host.E) → IsCoprime t t' → t ∈ P.asIdeal → (T : 𝓞 D.host.F) ∈ p.v.asIdeal → (T : 𝓞 D.host.F) ∉ p.v.asIdeal ^ 2 → ∀ y : AE D, Formalism.UG.prV (E := D.host.E) p.v (toEAf D y) ∈ Formalism.BasicNotions.intV D.host.E p.v → valuation k (p.pr y) < 1 → ∃ c ∈ Formalism.BasicNotions.intV D.host.E p.v, Formalism.UG.prV (E := D.host.E) p.v (toEAf D y) = Formalism.UG.inclE (F := D.host.F) (p.v.adicCompletion D.host.F) (t : D.host.E) * c := by
  intro D k _ _ _ _ p P hP T t t' ht' htt hco ht h1 h2 y hy hval
  obtain ⟨π₀, hπ₀, -, -, hres⟩ := GlobalTheory.LocMod.LevBack.exists_chart p hP
  have he : toEAf D p.e = Formalism.UG.P.afsplitEps D.host.E p.v * toEAf D p.e := by
    obtain ⟨ε, hε, hsum⟩ := p.above
    have hee : algebraMap (AF D.host.F) (AE D) ε * p.e = p.e := by
      rw [← hsum, add_mul, p.split.1, mul_comm (cA D p.e) p.e, p.split.2.1, add_zero]
    rw [← sub_eq_zero]
    refine Formalism.UG.P.afsplit_inj _ fun w => ?_
    rw [map_sub, map_mul]
    by_cases hw : w = p.v
    · subst hw; rw [Formalism.UG.P.afsplit_prV_eps, one_mul, sub_self]
    · rw [← hee, GlobalTheory.AdForm.ChiStd.prV_toEAf_idem_mul hε hw, mul_zero, sub_zero]
  have hpe : π₀ (toEAf D p.e) = 1 := by rw [hπ₀]; exact GlobalTheory.LocMod.LevBack.pr_e p
  have heps : π₀ (Formalism.UG.P.afsplitEps D.host.E p.v) = 1 := by
    have h3 := congrArg π₀ he
    rw [map_mul, hpe, mul_one] at h3
    exact h3.symm
  let s : Formalism.L2.Herm.intAf D.host.F D.host.E := ⟨_, Formalism.UG.P.afsplit_IE_int p.v _ hy⟩
  have hs : s ∈ Formalism.L2.DIV.idS D.host.F P.asIdeal := by
    rw [← Formalism.L2.DIV.resS_eq_zero_iff, hres]
    change valuation k (π₀ (Formalism.UG.P.afsplitIE p.v _)) < 1
    rw [Formalism.UG.P.afsplit_decomp, map_mul, heps, one_mul, hπ₀]
    exact hval
  have hv : ∀ b : 𝓞 D.host.F, algebraMap (𝓞 D.host.F) (𝓞 D.host.E) b ∈ P.asIdeal → b ∈ p.v.asIdeal := fun b hb => by
    rw [GlobalTheory.LocMod.LevelPlaces.splitPt_v_eq_under p hP]
    exact hb
  have key : ∀ z ∈ Formalism.L2.DIV.idS D.host.F P.asIdeal, ∃ c ∈ intV D.host.E p.v,
      Formalism.UG.prV (E := D.host.E) p.v (z : Formalism.L2.Herm.intAf D.host.F D.host.E) =
        Formalism.UG.inclE (F := D.host.F) (p.v.adicCompletion D.host.F) (t : D.host.E) * c := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      exact incl_eq_mul D.sp.cm p.v P.asIdeal hv (T : 𝓞 D.host.F) t t' ht' (by rw [htt, map_natCast]) hco ht h1 h2 a ha
    | zero => exact ⟨0, zero_mem _, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨c, hc, ea⟩ := ha
      obtain ⟨d, hd, eb⟩ := hb
      exact ⟨c + d, add_mem hc hd, by rw [Subring.coe_add, map_add, ea, eb, mul_add]⟩
    | smul r a _ ha =>
      obtain ⟨c, hc, ea⟩ := ha
      exact ⟨Formalism.UG.prV (E := D.host.E) p.v r * c, mul_mem (Formalism.UG.P.afsplit_prV_int p.v _ r.2) hc, by
        rw [smul_eq_mul, Subring.coe_mul, map_mul, ea, mul_left_comm]⟩
  obtain ⟨c, hc, e⟩ := key s hs
  refine ⟨c, hc, ?_⟩
  rw [← e]
  exact (Formalism.UG.P.afsplit_prV_IE p.v _).symm

end GlobalTheory.LocMod.SplitUnif
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIndexZeroLevelElementGivenReductionAtPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LevZeroPlace

section Helpers
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod.LevBack
open GlobalTheory.FinPl (SplitPt)
open Formalism.L2.NTheta (IsIdemAt)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (framePos)
open GlobalTheory.SymBridge (IsOrd zPos)
open GlobalTheory.AdelicLatMove (finEmb finEmb_mul)
open Formalism.L2.DIV (blockTri blkOf blk2 upperLeftBlock resS oToS idS kP frGL St redFn)

variable {D : D7} {c : Comm D} {v : VCom c}

theorem red_at {PP : Formalism.L2.DIV.Pl D.host.E} (G : GLoc v) {j n : ℕ} (hr : D.R.r ≤ n)
    {e : Ix (Fin D.R.k ⊕ Fin (G.s + 1)) (Fin D.R.t) j ≃ Fin n} (he : IsOrd zPos e) (π : Lev.EAf D →+* G.k)
    (h1 : ∀ a, π (toEAf D a) = G.q.pr a) (h3 : ∀ s : Formalism.L2.Herm.intAf D.host.F D.host.E, π s ∈ 𝒪[G.k])
    (h4 : ∀ s : Formalism.L2.Herm.intAf D.host.F D.host.E, resS D.host.F PP s = 0 ↔ valuation G.k (π s) < 1)
    (Y : GL (Fin n) (Formalism.L2.Herm.intAf D.host.F D.host.E))
    (hy : ∀ a b, ¬ FreeIx G.S.ρ a b → valuation G.k (π (Y.val (e a) (e b)) - (1 : Matrix _ _ G.k) a b) < 1) :
    Formalism.UG.bc (resS D.host.F PP) Y ∈ blockTri (blkOf D.R.r D.R.t) ∧
      ∃ x, GlobalTheory.LevZero.Red G PP x (upperLeftBlock hr (Formalism.UG.bc (resS D.host.F PP) Y)) := by
  haveI : Nontrivial (kP PP) := Ideal.Quotient.nontrivial_iff.2 PP.isPrime.ne_top
  have hs := G.hs
  obtain ⟨c1, x, c2⟩ := red_of_pattern G.S (by unfold Ranks.r; omega) hr he (resS D.host.F PP)
    (π.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) h3 h4 Y hy
  refine ⟨c1, x, fun a b a' b' ha hb z hz => ?_⟩
  have := c2 a b a' b' ha hb (oToS D.host.F D.host.E z) ((Formalism.L2.DIV.resS_oToS PP z).trans hz)
  rwa [show (π.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) (oToS D.host.F D.host.E z) =
    (ofSplit G.q).pr (z : D.host.E) from h1 (incA D (z : D.host.E))] at this

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

theorem lev_back {cm : GlobalTheory.ChainOnto.Com D} {st : StAt (c.V 0)} {b : GA D (c.V 0)} {G : cm.Pg → GLoc v}
    (hB : GlobalTheory.LevZero.Bot cm st b G) (PP : cm.Pg) (c' : ℕ) (hc : 0 + c' = (G PP).s + 1) (x : GA D (c.V 0))
    (xk : GL (XIx (Fin D.R.k) (Fin D.R.t) 0 ⊕ Fin c') (G PP).k)
    (hx : (ofSplit (G PP).q).IsLoc ((G PP).FY 0 c' hc) x xk)
    (hxk : xk ∈ (((G PP).S.T (Fin D.R.t)).lev 0 c' hc).J) :
    b⁻¹ * x * b ∈ levS (c.V 0) st.β st.L := by
  have hs := (G PP).hs
  have hst := hB.mem
  obtain ⟨hr, ξ, hL⟩ := hst.lev
  replace hL : st.L = _ := hL
  obtain ⟨a, ha⟩ := hB.com.split
  obtain ⟨e, he, hmv⟩ := (hB.loc PP).frame c' hc
  obtain ⟨π, h1, h2, h3, h4⟩ := exists_chart (G PP).q (hB.loc PP).idem
  let L := typeFrame (G PP).S.ϖ (stdOrd (Fin D.R.k) (Fin D.R.t) 0 c' hc)
  obtain ⟨hyK, hyP⟩ := (pattern_iter _ _ _ (G PP).S (Fin D.R.t) 0 (L.conj.symm xk)).1 hxk
  have hmap : ∀ M : Matrix (Fin (c.V 0).rank) (Fin (c.V 0).rank) (AE D),
      (M.map (toEAf D)).map π = M.map (G PP).q.pr := fun M => Matrix.ext fun _ _ => h1 _
  have hγ : GeneralLinearGroup.map π (st.β⁻¹ * Lev.finE (c.V 0) (b⁻¹ * x * b) * st.β) =
      reGL e (L.conj.symm xk) := by
    rw [← conj_frame ((G PP).FY 0 c' hc) L e (GeneralLinearGroup.map π (Lev.finE (c.V 0) b * st.β))
      (GeneralLinearGroup.map π (Lev.finE (c.V 0) x)) (L.conj.symm xk) ?_ ?_]
    · rw [MonoidHom.map_mul (Lev.finE (c.V 0)), MonoidHom.map_mul (Lev.finE (c.V 0)), MonoidHom.map_inv, conj_conj,
        MonoidHom.map_mul, MonoidHom.map_mul, MonoidHom.map_inv]
    · have hb : (st.β.val.map (finEmb D)).map (toEAf D) = st.β.val := Matrix.ext fun _ _ => toEAf_finEmb _
      refine Eq.trans ?_ (hmv _ hb)
      refine Eq.trans ?_ (hmap _)
      rw [Matrix.map_mul, hb]
      rfl
    · rw [MulEquiv.apply_symm_apply]
      exact (hmap _).trans hx.2
  obtain ⟨Y, hY, hYv, hY1⟩ := exists_int (G PP).q π h2 (c.V 0) hst.selfDual hst.frame (t := b) hx.1 (by
    rw [hγ, mem_KO, ← map_inv]
    rw [mem_KO] at hyK
    exact ⟨fun _ _ => hyK.1 _ _, fun _ _ => hyK.2 _ _⟩)
  have hall : ∀ PP' : cm.Pg, Formalism.UG.bc (resS D.host.F PP'.1) Y ∈ blockTri (blkOf D.R.r D.R.t) ∧
      ∃ x, GlobalTheory.LevZero.Red (G PP') PP'.1 x (upperLeftBlock hr (Formalism.UG.bc (resS D.host.F PP'.1) Y)) := fun PP' => by
    by_cases hne : PP' = PP
    · subst hne
      refine red_at (G PP') hr he π h1 h3 h4 Y fun a₁ b₁ hab => ?_
      have e1 : π (Y.val (e a₁) (e b₁)) = (L.conj.symm xk).val a₁ b₁ := by
        rw [hYv]
        refine (congrArg (fun g : GL _ _ => g.val (e a₁) (e b₁)) hγ).trans ?_
        simp only [reGL_val, submatrix_apply, Equiv.symm_apply_apply]
      rw [e1]
      exact hyP a₁ b₁ hab
    · have hs' := (G PP').hs
      obtain ⟨e', he', -⟩ := (hB.loc PP').frame c' (by omega)
      obtain ⟨π', k1, -, k3, k4⟩ := exists_chart (G PP').q (hB.loc PP').idem
      refine red_at (G PP') hr he' π' k1 k3 k4 Y fun a₁ b₁ _ => ?_
      have e1 := congrArg π' (hY1 (e' a₁) (e' b₁))
      rw [RingHom.map_mul, k1, pr_other (G PP).q (G PP').q ha PP.2 PP'.2 (fun h => hne (Subtype.ext h)) (hB.loc PP).idem
        (hB.loc PP').idem, zero_mul, RingHom.map_sub] at e1
      have e2 : π' ((1 : Matrix _ _ (Lev.EAf D)) (e' a₁) (e' b₁)) = (1 : Matrix _ _ (G PP').k) a₁ b₁ := by
        simp only [one_apply, e'.injective.eq_iff]
        split_ifs
        · exact π'.map_one
        · exact π'.map_zero
      rw [← e2, ← e1, Valuation.map_zero]
      exact zero_lt_one
  change _ ∈ Lev.levG _ _ st.L
  rw [hL]
  refine ⟨(GfC _).mul_mem ((GfC _).mul_mem ((GfC _).inv_mem hB.fin)
    (GlobalTheory.WeilProduct.mem_GfC_of_suppAt (G PP).q.split hx.1)) hB.fin, ?_⟩
  change Lev.finE (c.V 0) _ ∈ Formalism.L2.DIV.lev _ _ _ _
  refine ⟨Formalism.L2.DIV.mem_parLev.2 ⟨GlobalTheory.LevSplit.finE_mem_UA _ _, ⟨Y, hY⟩, fun PP' hPP' => ?_,
    fun _ h => absurd h (Finset.notMem_empty _)⟩, ?_⟩
  · rw [← hY, Formalism.L2.DIV.redFn_frGL]
    exact (hall ⟨PP', hPP'⟩).1
  · refine (hB.grp _).2 fun PP' => ?_
    change ∃ z, GlobalTheory.LevZero.Red (G PP') PP'.1 z (upperLeftBlock hr (redFn _ PP'.1 _))
    rw [← hY, Formalism.L2.DIV.redFn_frGL]
    exact (hall PP').2

theorem finE_mem_St {cm : GlobalTheory.ChainOnto.Com D} {st : StAt (c.V 0)} {b : GA D (c.V 0)} {G : cm.Pg → GLoc v}
    (hB : GlobalTheory.LevZero.Bot cm st b G) (g : GA D (c.V 0)) (hg : g ∈ levS (c.V 0) st.β st.L) :
    finE (c.V 0) g ∈ St st.β := by
  obtain ⟨hr', ξ, hL⟩ := hB.mem.lev
  replace hL : st.L = _ := hL
  have h1 : g ∈ GfC _ ∧ finE (c.V 0) g ∈ Formalism.L2.DIV.lev D.sp.cm (c.V 0).gram st.β st.L := hg
  rw [hL, Formalism.L2.DIV.mem_lev, Formalism.L2.DIV.mem_parLev] at h1
  exact h1.2.1.2.1

theorem red_of_congr (G : GLoc v) (PP : Formalism.L2.DIV.Pl D.host.E) (x x' : G.S.P.J) (g : GL (Fin D.R.r) (kP PP))
    (h : GlobalTheory.LevZero.Red G PP x' g)
    (hc : (x'.1 : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k)⁻¹ * x.1 ∈ GlobalTheory.SplitWeil.KOne G.k (Fin D.R.k ⊕ Fin (G.s + 1))) :
    GlobalTheory.LevZero.Red G PP x g := by
  intro a b a' b' ha hb z hz
  have h1 := h a b a' b' ha hb z hz
  have hI : GlobalTheory.StepData.IntM (x'.1 : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val :=
    GlobalTheory.StepData.intM_of_mem_KO (G.S.P.le_KO x'.2)
  have hM := hI.mul_maxM (GlobalTheory.StepData.mem_KOne.1 hc)
  have e : (x'.1 : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val *
      (((x'.1 : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k)⁻¹ * x.1 : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val - 1) =
      (x.1 : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val - (x'.1 : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val := by
    rw [Matrix.mul_sub, Units.val_mul, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.mul_one]
  rw [e] at hM
  have h2 := hM a b
  rw [Matrix.sub_apply] at h2
  have e2 : (x.1 : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val a b - (GlobalTheory.LocMod.ofSplit G.q).pr (z : D.host.E) =
      ((x.1 : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val a b - (x'.1 : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val a b) +
      ((x'.1 : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val a b - (GlobalTheory.LocMod.ofSplit G.q).pr (z : D.host.E)) := by ring
  rw [e2]
  exact (Valuation.map_add _ _ _).trans_lt (max_lt h2 h1)

end Helpers

end GlobalTheory.LevZeroPlace

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.LevZeroPlace.one_place : ∀ {D : D7} {c : Comm D} {v : VCom c} (cm : GlobalTheory.ChainOnto.Com D) (st : StAt (c.V 0)) (b : GA D (c.V 0)) (G : cm.Pg → GLoc v) (h0 : 0 + 2 * D.R.rS + 2 = D.R.m), GlobalTheory.LevZero.Bot cm st b G → ∀ Q : GA D (c.V 0) → Prop, (∀ k ∈ levS (c.V 0) st.β st.L, ∀ k' ∈ levS (c.V 0) st.β st.L, Q k → Q k' → Q (k * k')) → (∀ (PP : cm.Pg) (n : GA D (c.V 0)) (q : GL (XIx (Fin D.R.k) (Fin D.R.t) 0 ⊕ Fin ((G PP).s + 1)) (G PP).k), n ∈ flagN (c.bes 0 D.R.rS h0).d → q ∈ GlobalTheory.RootEx.N (G PP).k _ ((G PP).s + 1) (D.R.rS + 1) → (ofSplit (G PP).q).IsLoc ((G PP).FY 0 ((G PP).s + 1) (Nat.zero_add _)) n q → b⁻¹ * n * b ∈ levS (c.V 0) st.β st.L → Q (b⁻¹ * n * b)) → (∀ x ∈ GfC (c.X 0), b⁻¹ * embA (c.bes 0 D.R.rS h0).d (c.bes 0 D.R.rS h0).o x * b ∈ levS (c.V 0) st.β st.L → Q (b⁻¹ * embA (c.bes 0 D.R.rS h0).d (c.bes 0 D.R.rS h0).o x * b)) → ∀ (PP : cm.Pg) (x : (G PP).S.P.J), ∃ m ∈ levS (c.V 0) st.β st.L, Q m ∧ (∀ hr : D.R.r ≤ (c.V 0).rank, GlobalTheory.LevZero.Red (G PP) PP.1 x (upperLeftBlock hr (redFn st.β PP.1 (finE (c.V 0) m)))) ∧ ∀ PP' ∈ cm.Pg, PP' ≠ PP.1 → redFn st.β PP' (finE (c.V 0) m) = 1 := by
  intro D c v cm st b G h0 hB Q hmul hN hU PP x
  have hst : ∀ w ∈ levS (c.V 0) st.β st.L, finE (c.V 0) w ∈ St st.β := GlobalTheory.LevZeroPlace.finE_mem_St hB
  have hbes := (G PP).bes 0 D.R.rS h0 ((G PP).s + 1) (Nat.zero_add _)
  have hρ : (G PP).S.ρ = D.R.rS := by have := hbes.1; have := (G PP).S.odd; omega
  have hLev := GlobalTheory.LevZeroPlace.lev_back hB PP ((G PP).s + 1) (Nat.zero_add _)
  have hv : ∀ P : cm.Pg, (G P).q.v = IsDedekindDomain.HeightOneSpectrum.under (NumberField.RingOfIntegers D.host.F) P.1 :=
    fun P => (hB.loc P).under
  have horth : ∀ P P' : cm.Pg, P ≠ P' →
      ((G P).q.e + cA D (G P).q.e) * ((G P').q.e + cA D (G P').q.e) = 0 := by
    intro P P' hne
    obtain ⟨ε, hε, hsum⟩ := (G P).q.above
    obtain ⟨ε', hε', hsum'⟩ := (G P').q.above
    have hvv : (G P).q.v ≠ (G P').q.v := by
      rw [hv P, hv P']
      intro h
      exact hne (Subtype.ext (GlobalTheory.LevelPlaces.injOn_under D cm hB.com P.2 P'.2 h))
    rw [hsum, hsum', ← map_mul, GlobalTheory.SingleDatum.BasePair.placeIdem_mul_eq_zero hε' hε hvv, map_zero]
  have hoff : ∀ g : GA D (c.V 0), Formalism.L2.Theta.SuppAt (G PP).q.e (c.V 0) g → b⁻¹ * g * b ∈ levS (c.V 0) st.β st.L →
      ∀ PP' ∈ cm.Pg, PP' ≠ PP.1 → redFn st.β PP' (finE (c.V 0) (b⁻¹ * g * b)) = 1 :=
    fun g hg hl PP' hPP' hne => GlobalTheory.T.reduction_eq_one_of_supportedAt_orthogonal_splitPlace D (G ⟨PP', hPP'⟩).k (G ⟨PP', hPP'⟩).q PP' (hB.loc ⟨PP', hPP'⟩).idem (G PP).q.e
      (horth PP ⟨PP', hPP'⟩ fun h => hne (congrArg Subtype.val h).symm) _ _ _
      (GlobalTheory.PlaceMatch.suppAt_conj' hg _) (hst _ hl)
  obtain ⟨n, γ, hnN, hnJ, hγJ, hc⟩ := GlobalTheory.T.exists_N_embX_inv_mul_mem_KOne' (G PP).k (G PP).s D.R.k (G PP).S x.1 x.2
  obtain ⟨hup1, hup2⟩ := GlobalTheory.T.levelZeroUniformizerFrame_unipotent_and_embedGL (G PP).k (G PP).s D.R.k (G PP).S (Fin D.R.t)
  obtain ⟨hupN, -⟩ := hup1 ⟨n, hnJ⟩ hnN
  rw [hρ] at hupN
  obtain ⟨ν, hν⟩ := GlobalTheory.LocMod.Witness.exists_isLoc (GlobalTheory.LocMod.ofSplit (G PP).q)
    ((G PP).FY 0 ((G PP).s + 1) (Nat.zero_add _)) (GlobalTheory.LevZeroGen.upZero (G PP).S (Fin D.R.t) n)
  obtain ⟨η, hη⟩ := GlobalTheory.LocMod.Witness.exists_isLoc (GlobalTheory.LocMod.ofSplit (G PP).q) ((G PP).FX 0 (Nat.zero_le _))
    (GlobalTheory.StepData.reGL (GlobalTheory.LevZeroGen.xZero (Fin D.R.k) (Fin D.R.t)) γ)
  have hη' := GlobalTheory.T.besselFrame_embedding_localElement_eq_embedded_matrix D (G PP).k _ _ _ _ _ _ _ _ hbes η _ hη
  rw [← hup2] at hη'
  have hνl := hLev ν _ hν ((GlobalTheory.LevZeroGen.upZero_mem_lev _ _ _).2 hnJ)
  have hηl := hLev _ _ hη' ((GlobalTheory.LevZeroGen.upZero_mem_lev _ _ _).2 hγJ)
  have hQν := hN PP ν _ (GlobalTheory.LocFlag.mem_flagN D _ _ _ _ _ _ _ _ _ hbes ν _ hupN hν) hupN hν hνl
  have hQη := hU η (GlobalTheory.PlaceMatch.mem_GfC_of_suppAt' (G PP).q.split hη.1) hηl
  have hprod := GlobalTheory.LocGrp.isLoc_mul _ hν hη'
  rw [← map_mul] at hprod
  have e : b⁻¹ * ν * b * (b⁻¹ * embA (c.bes 0 D.R.rS h0).d (c.bes 0 D.R.rS h0).o η * b) =
      b⁻¹ * (ν * embA (c.bes 0 D.R.rS h0).d (c.bes 0 D.R.rS h0).o η) * b := by group
  have hl : b⁻¹ * (ν * embA (c.bes 0 D.R.rS h0).d (c.bes 0 D.R.rS h0).o η) * b ∈ levS (c.V 0) st.β st.L :=
    hLev _ _ hprod ((GlobalTheory.LevZeroGen.upZero_mem_lev _ _ _).2 (mul_mem hnJ hγJ))
  refine ⟨_, hl, e ▸ hmul _ hνl _ hηl hQν hQη, fun hr => ?_, hoff _ hprod.1 hl⟩
  exact GlobalTheory.LevZeroPlace.red_of_congr (G PP) PP.1 x ⟨_, mul_mem hnJ hγJ⟩ _
    (GlobalTheory.T.reducesToResidue_of_localLevelElement_movedBack (G PP) PP.1 b st.β (hB.loc PP) hB.fin hr _ ⟨_, mul_mem hnJ hγJ⟩ hprod (hst _ hl)) hc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsStepPointOfChartBasePoint
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

namespace GlobalTheory.KxPoint

theorem pointOf_base : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (u : B.Word) (a : I.ι) (i : ℕ), i ≤ B.R.m → ∀ {C : Type} (chOf : (I.stp u a i).Cl → C) (Lb : C → Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)) (U : C → Subgroup (TC.GA B (B.R.N i))) (chi : ∀ β, U β →* ℂˣ) (y : (I.stp u a i).Cl → TC.GA B (B.R.N i)) (st : ∀ c, (I.stp u a i).Stab c → GL (Fin (B.R.N i)) B.host.E) (k : C → TC.GA B (B.R.N i)), I.Reads u a i chOf Lb U chi y st k → ∀ β, (∃ q : Formalism.L2.Col.ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u i, TC.PtOf (k β) q) → (∀ P ∈ I.SQ, P ∉ I.Q a → (k β).1.map (adAt B.host.F P) = 1) → ∃ (b0 : Idx I.sel (I.tup a) (I.idx a) i) (p0 : PtAt B.R I.sel (I.tup a) (I.cst a) u i), TC.PtOf (k β) (extTo I.SQ p0.1.1) ∧ p0.1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N i) ∧ ∀ c, chOf c = β → c.1 = b0 ∧ cosetIn ((I.stp u a i).rep c) = cosetIn p0 := by
  intro B X I hI hP u a i hi C chOf Lb U chi y st k hR β hq hk
  have hPr : (B.primes X).Ok := (base_fields_primes_ok B X).2.1
  have hd := ChEx.q_disj I hI a
  obtain ⟨c₀, hc₀⟩ := hR.onto β
  obtain ⟨q, hqk⟩ := hq
  obtain ⟨p, hpk, hpN⟩ := hR.k_std β
  have hqN : q.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N i) := by
    rw [← hpN]
    exact GlobalTheory.BaseCosetPt.lat_eq_of_carries q.deco.2.lat p.deco.2.lat hqk.lat hpk.lat
  obtain ⟨r', hr'1, hr'2, hr'3⟩ := ChExM.exists_pt_inv hd ((I.stp u a i).rep c₀) q
  have hcos : cosetIn r' = cosetIn ((I.stp u a i).rep c₀) :=
    (ChExM.cosetIn_iff hd (MemChart.hqG hPr) _ _).2 ⟨hr'2, hr'3⟩
  refine ⟨c₀.1, r', ?_, ?_, ?_⟩
  · rw [hr'1]
    refine ⟨hqk.uni, hqk.lat, hqk.f, hqk.be, fun P i' j => ?_⟩
    rw [extTo_fr]
    by_cases hPQ : P.1 ∈ I.Q a
    · rw [ptFr_of_mem q (hd P.1 hPQ) hPQ]
      exact hqk.fr ⟨P.1, hPQ⟩ i' j
    · have hPG : P.1 ∉ (B.primes X).vGs := by
        obtain ⟨b, -, hb⟩ := Finset.mem_biUnion.1 P.2
        exact ChEx.q_disj I hI b P.1 hb
      have hfr : ptFr q P.1 = 1 := by
        unfold ptFr
        rw [dif_neg hPG, dif_neg hPQ, hqN]
        unfold GlobalTheory.Mem.Col2.latFr
        exact if_pos rfl
      have hkP := congrFun (congrFun (hk P.1 P.2 hPQ) i') j
      rw [hfr]
      simp only [Matrix.map_apply] at hkP
      rw [hkP]
      simp [Matrix.one_apply, Pi.single_apply, eq_comm]
  · rw [hr'1]; exact hqN
  · intro c hc
    obtain ⟨h1, h2⟩ := (hR.key c c₀).1 (hc.trans hc₀.symm)
    exact ⟨h1, h2.trans hcos.symm⟩

end GlobalTheory.KxPoint
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtraProjectionLevelCharacterStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extra_projection_level_character : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → ∀ t (F : LinearMap.range ((pk W).cX.toMap (pk W).prX ∘ₗ ((pk W).HX t).e)), F.1 ∈ CXP (pk W) (lvP W) t → ∀ κ ∈ levS (Yc D (D.R.m - 1)) ((pk W).βY (D.R.m - 1)) ((pk W).datYt t (D.R.m - 1) (lvP W)), ∀ φ x g, ((pk W).ioX t F).1 ((pk W).ItX φ x) (g * κ) = levChi (Yc D (D.R.m - 1)) ((pk W).βY (D.R.m - 1)) ((pk W).datYt t (D.R.m - 1) (lvP W)) κ * ((pk W).ioX t F).1 ((pk W).ItX φ x) g := by
  first | exact @GlobalTheory.StepLevelP.ioX_levChi | exact GlobalTheory.StepLevelP.ioX_levChi | (intros; apply GlobalTheory.StepLevelP.ioX_levChi <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteFourierExpansionHalfSplitPlacesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_fourier_expansion_half_split_places : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (c : ℕ), 0 < c → Odd c → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → LaFacts (tauE D) δ D.host.d sc (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' → (∃ ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E), IsSelfDualC S ΛS ∧ (ΛS : Set (Fin S.rank → D.host.E)) = latFr S hS N) → (∃ ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E), IsSelfDualC T ΛT ∧ (ΛT : Set (Fin T.rank → D.host.E)) = latFr T hT N') → ∀ (Φ : WO S T → ℂ) (Ξ : Formalism.L2.Col.HomE D.host.E a b → ℂ), IsSBHalf e (latO S T (latFr S hS N) (latFr T hT N') fun _ => True) Φ → (∀ γ, Φ (γ.map fun r => e * incA D r) = Ξ (toHom S T hS hT γ)) → (∀ x, Ξ x ≠ 0 → (c : D.host.E) • x ∈ Formalism.L2.Col.homAt SS N N') → (∀ x, ∀ y ∈ Formalism.L2.Col.homAt SS N N', Ξ (x + (c : D.host.E) • y) = Ξ x) → ∀ (SX SA SB : Finset (VV D.what₂.Tau a b)), Formalism.L2.Th1.H.IsReps (LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') (AC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c) SX → Formalism.L2.Th1.H.IsReps (BC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c) ((LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') ⊓ (AC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c)) SA → Formalism.L2.Th1.H.IsReps (LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') (BC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c) SB → ∀ (px py : VV D.what₂.Tau a b → Formalism.L2.Col.HomE D.host.E a b), (∀ x ∈ SX, px x ∈ halfAO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c ∧ embH (tauE D) δ (px x) = x) → (∀ y ∈ SB, py y ∈ halfBO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c ∧ embH (tauE D) δ (py y) = y) → ∀ t, Φ t = ∑ x ∈ SX, ∑ y ∈ SB, (((SA.card : ℂ))⁻¹ * ∑ s ∈ SA, onV (tauE D) δ Ξ (s - x) * (brk (HV sc) y s)⁻¹) * (ψ (symplO S T (t + ((LinearMap.toMatrix' (px x)).reindex (finCongr hT.symm) (finCongr hS.symm)).map fun r => e * incA D r) (((LinearMap.toMatrix' (py y)).reindex (finCongr hT.symm) (finCongr hS.symm)).map fun r => cA D e * incA D r)) * halfInd e (latO S T (latFr S hS N) (latFr T hT N') fun _ => True) (t + ((LinearMap.toMatrix' (px x)).reindex (finCongr hT.symm) (finCongr hS.symm)).map fun r => e * incA D r)) := by
  first | exact @GlobalTheory.AdForm.DatumFour.four_expand | exact GlobalTheory.AdForm.DatumFour.four_expand | (intros; apply GlobalTheory.AdForm.DatumFour.four_expand <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiLatticeSplitsAtNormalFramePlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierJacobiLattice_splits_at_normalFrame_place : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ {a : XGeo D} (y : YRat a) {βT : GL (Fin D.sp.X'.rank) (Lev.EAf D)} {PP : Pl D.host.E} (l : LocX a βT PP) (FY : FYFam l) (sc : ℕ → l.k), IsNormalFr l y FY sc → (∀ j, j ≤ D.R.m → (a.x j).Is) → ∀ (N : ∀ j, GlobalTheory.FinPl.Lat (Yc D j)) (M : ∀ j ρ (h : j + 2 * ρ + 2 = D.R.m), GlobalTheory.FinPl.Lat (y.bes j ρ h).V₀), (∀ j, j < D.R.m → IsSelfDualC (Yc D j) (N j)) → (∀ j c (hc : j + c = l.s + 1), IntIn l.q (Yc D j) (FY j c hc) (N j)) → (∀ j ρ h, IsSelfDualC (y.bes j ρ h).V₀ (M j ρ h)) → (∀ j ρ h (hj : j ≤ l.s + 1) (F₀ : Frame l.k ((y.bes j ρ h).lev (a.x j).vol).V₀.rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Unit)), (ofSplit l.q).IsCoreFrame ((y.bes j ρ h).lev (a.x j).vol) (sc j) (l.FX j hj) F₀ → IntIn l.q _ F₀ (M j ρ h)) → ∀ j ρ (h : j + 2 * ρ + 2 = D.R.m), GlobalTheory.FinPl.MonoAt ((y.jac j ρ h).lev (a.x (j + 1)).vol).d (N (j + 1)) (a.x (j + 1)).L (PP.under (𝓞 D.host.F)) := by
  first | exact @GlobalTheory.Fam.monoW_of_normalFrames | exact GlobalTheory.Fam.monoW_of_normalFrames | (intros; apply GlobalTheory.Fam.monoW_of_normalFrames <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeCharacterEqAtDetRootsOfCongruentStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeCharacter_eq_at_det_roots_of_congruent : ∀ (D : D7) (c : (AE D)ˣ →* Circle), IsHeckeChar D c → ∃ N₀ : ℕ, ∀ (V : HSp D) {n : ℕ} (hn : V.rank = n) (g w : GA D V), w ∈ GfC V → (∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (r s : Fin n), Valued.v (adAt D.host.F P (finM V hn w r s - (1 : Matrix (Fin n) (Fin n) (EF D)) r s)) ≤ WithZero.exp (-(N₀ : ℤ))) → ∀ x, IsDetRoot V g x → ∃ x₁, IsDetRoot V (g * w) x₁ ∧ c x₁ = c x := by
  first | exact @GlobalTheory.DetRootApprox.exists_root_same_value | exact GlobalTheory.DetRootApprox.exists_root_same_value | (intros; apply GlobalTheory.DetRootApprox.exists_root_same_value <;> assumption)
end

