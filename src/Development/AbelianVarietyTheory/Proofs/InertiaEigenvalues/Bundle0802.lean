import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0339
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0419
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0197
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0155
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftGoodProjectorIntertwinesMatchedHecke
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0021
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0798
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0168
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0797
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HeckePin
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsParamDefinite
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Hk3

namespace GlobalTheory.DownLift.Params

variable {D : D7}

theorem mem_bddAut_of_posDef {V : HSp D} (hs : V.SigOK) (hp : V.IsPosDef) {f : GA D V → ℂ} (hc : Continuous f)
    (hl : ∀ γ ∈ GQ V, ∀ g, f (γ * g) = f g) : f ∈ GlobalTheory.FinZeta.bddAut V := by
  have hpos : ∀ τ, (gramAt D V τ).PosDef := fun τ => by
    have := hs (tauE D τ)
    rw [hp] at this
    exact GlobalTheory.DefiniteQuotient.posDef_of_signature this
  obtain ⟨C, hC, hcov⟩ := GlobalTheory.DefiniteQuotient.exists_compact V hpos
  obtain ⟨b, hb⟩ := hC.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨hc, hl, b, fun g => ?_⟩
  obtain ⟨γ, hγ, c, hcC, rfl⟩ := hcov g
  rw [hl γ hγ]
  exact hb c hcC

theorem level_abs {Γ Gf W : Type} [Group Γ] [Group Gf] [NormedAddCommGroup W] [InnerProductSpace ℂ W] {ι : Γ →* Gf}
    {ρ : Γ →* Module.End ℂ W} {J : Subgroup Gf} {χ : J →* ℂˣ} {f : Gf → W} (hf : f ∈ Bridge.AdForms ι ρ J χ)
    {k : Gf} (hk : k ∈ J) (h : Gf) : f (h * k) = ((χ ⟨k, hk⟩ : ℂˣ) : ℂ) • f h := by
  have h3 := hf 1 h ⟨k, hk⟩
  rw [map_one, map_one, one_mul] at h3
  exact h3

theorem ext_level {V : HSp D} (c : CoefA V) (hc : c.Is) {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank}
    {f : Bridge.Gf V → c.W}
    (hf : f ∈ Bridge.AdForms (W := c.W) (Bridge.ratF V) (c.ρ.comp (GQ V).subtype) (levEnv V β L).J (levEnv V β L).χ)
    {k : GA D V} (hk : k ∈ levG V β (flag1L L)) (h : GA D V) :
    c.ext f (h * k) = levChi V β (flag1L L) k • c.ext f h := by
  have hJ : (finHom V).rangeRestrict k ∈ (levEnv V β L).J := hk.2
  exact (GlobalTheory.DefLiftHecke.ext_mul c hc f hk.1 h).trans ((congrArg (c.ρ h⁻¹) (level_abs hf hJ _)).trans (map_smul _ _ _))

theorem exists_coord_ne {V : HSp D} (c : CoefA V) {f : Bridge.Gf V → c.W} (h0 : f ≠ 0) :
    ∃ ℓ : c.W →ₗ[ℂ] ℂ, (fun h => ℓ (c.ext f h)) ≠ 0 := by
  obtain ⟨u, hu⟩ := Function.ne_iff.1 h0
  obtain ⟨g, rfl⟩ := (finHom V).rangeRestrict_surjective u
  have h1 : c.ext f g ≠ 0 := fun e => hu (by
    have e' : c.ρ g⁻¹ (f ((finHom V).rangeRestrict g)) = 0 := e
    have := congrArg (c.ρ g) e'
    rwa [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, map_zero] at this)
  refine ⟨innerₛₗ ℂ (c.ext f g), Function.ne_iff.2 ⟨g, fun e => h1 ?_⟩⟩
  exact inner_self_eq_zero.1 e

set_option maxHeartbeats 1000000 in

theorem exists_param_definite {V : HSp D} (hs : V.SigOK) (hp : V.IsPosDef) (c : CoefA V) (hc : c.Is)
    {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hβ : IsSDFrame V β Λ 1)
    {L : LevDat D.host.E ℂ V.rank} {S : Finset (HeightOneSpectrum (𝓞 D.host.F))}
    (hS : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP.under (𝓞 D.host.F) ∈ S) {f : Bridge.Gf V → c.W}
    (hf : f ∈ Bridge.AdForms (Bridge.ratF V) c.coef.ρ (levEnv V β L).J (levEnv V β L).χ) (h0 : f ≠ 0) (s : Sys D)
    (he : ∀ P d, P.under (𝓞 D.host.F) ∉ S → IsLab V P d → hkF V P (Finsupp.single d 1) f = s P d • f) :
    ∃ B, GlobalTheory.LFun.IsSysParamD D S V.rank s B := by
  obtain ⟨n, hB⟩ := hβ
  rw [one_pow] at hB
  obtain ⟨ℓ, hℓ⟩ := exists_coord_ne c h0
  have hsph := (GlobalTheory.FinZeta.LevelOff.level_offS D V β Λ (flag1L L) S hB hS).1
  have hbd : (fun h => ℓ (c.ext f h)) ∈ GlobalTheory.FinZeta.bddAut V :=
    mem_bddAut_of_posDef hs hp (ℓ.continuous_of_finiteDimensional.comp (GlobalTheory.ThetaIntegrand.ext_continuous c hc β L hf))
      fun γ hγ g => congrArg ℓ (GlobalTheory.ThetaIntegrand.ext_invariant c hf γ hγ g)
  have hlev : ∀ k ∈ (levG V β (flag1L L) : Set (GA D V)), ∀ g,
      (fun h => ℓ (c.ext f h)) (g * k) = levChi V β (flag1L L) k * (fun h => ℓ (c.ext f h)) g := fun k hk g =>
    (congrArg ℓ (ext_level c hc hf hk g)).trans (map_smul _ _ _)
  have heig : ∀ w d R, Hecke₂ V (levG V β (flag1L L) : Set (GA D V)) (levChi V β (flag1L L)) S w d R →
      heckeLin V R (fun h => ℓ (c.ext f h)) = s w d • fun h => ℓ (c.ext f h) := fun w d R hR => by
    have hw : w.under (𝓞 D.host.F) ∉ S := by
      obtain ⟨_, _, _, _, h, -⟩ := hR
      exact (GlobalTheory.GoodPrimes.offS_iff S w).1 h
    have h1 : ((1 : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := GlobalTheory.DefLiftHecke.one_pow_notMem w 0
    obtain ⟨hk, hop, -⟩ := GlobalTheory.LevOp.level_operators V β Λ 1 (flag1L L) hB w h1 fun PP hPP =>
      ⟨fun e => hw (e ▸ hS PP hPP), fun e => hw (GlobalTheory.LevelPlaces.under_eq_of_isConjPl e ▸ hS PP hPP)⟩
    have hR' : SphOp V w d R := ((hop S d R).1 hR).2
    have h2 := ((GlobalTheory.SphLabelOps.label_operators V w).1 d R hR').2 _ (GlobalTheory.PRep.rightReg ℂ (GA D V) ℂ)
      (fun h => ℓ (c.ext f h)) fun k hkk => funext fun g => by
        have := hlev k (hk k hkk).1 g
        rwa [(hk k hkk).2, one_mul] at this
    funext g
    have h3 := congrFun h2 g
    have h4 := GlobalTheory.DefLiftHecke.ext_hkF c hc w (Finsupp.single d 1) f g
    rw [he w d hw ⟨R, hR'⟩, map_smul, Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton,
      Finsupp.single_eq_same, one_smul] at h4
    rw [opOf, Finsupp.sum_single_index (by exact zero_smul _ _), one_smul, Finset.sum_apply, LinearMap.sum_apply,
      Finset.sum_apply] at h3
    have h5 := congrArg ℓ h4
    rw [map_sum, Pi.smul_apply, map_smul] at h5
    exact h3.trans h5.symm
  obtain ⟨B, hB', -⟩ := GlobalTheory.T.exists_satake_parameters_bounded_eigenfunction D V _ _ S hsph _ hbd hℓ hlev s heig
  exact ⟨B, (GlobalTheory.LFun.isParamFunV_iff_isSysParamD_of_level hsph hℓ hlev heig B).1 hB'⟩

theorem exists_param_part (hP : GlobalTheory.Published.CuspRapidDecay) {V : HSp D} {Sp : D.what₂.Tau → SPar} {θ : InfFam D}
    (hθ : IsInfFam θ) {M : DSModel V Sp}
    {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hβ : IsSDFrame V β Λ 1)
    {L : LevDat D.host.E ℂ V.rank} {S : Finset (HeightOneSpectrum (𝓞 D.host.F))}
    (hS : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP.under (𝓞 D.host.F) ∈ S) {s : Sys D}
    (h : partFull θ M (levS V β L) (levChi V β L) S s ≠ ⊥) :
    ∃ B, GlobalTheory.LFun.IsSysParamD D S V.rank s B ∧ ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) ∉ S →
      ∀ a ∈ B w, ‖(a : ℂ)‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ (((V.rank : ℝ) - 1) / 2) := by
  obtain ⟨n, hB⟩ := hβ
  rw [one_pow] at hB
  have hsph := (GlobalTheory.FinZeta.LevelOff.level_offS D V β Λ L S hB hS).1
  obtain ⟨U, hU, hU0⟩ := (Submodule.ne_bot_iff _).1 h
  obtain ⟨v, hv⟩ : ∃ v, U v ≠ 0 := by
    by_contra h
    push Not at h
    exact hU0 (MultilinearMap.ext h)
  obtain ⟨h1, h2⟩ := (mem_partFull θ M _ _ S s U).1 hU
  have h3 := (GlobalTheory.MultMem.mem_mult_iff ..).1 h1
  obtain ⟨B, hB', hb⟩ := GlobalTheory.T.exists_satake_parameters_bounded_eigenfunction D V _ _ S hsph (U v)
    ⟨(h3.aut v).cont, (h3.aut v).left, GlobalTheory.CuspDecay.bounded_of_cuspForm hP hθ (h3.aut v) (h3.cusp v)⟩ hv (h3.lev v) s
    fun P d R hR => h2 P d R hR v
  exact ⟨B, (GlobalTheory.LFun.isParamFunV_iff_of_mem_partFull hsph hU hv B).1 hB', fun w hw => (hb w hw).2⟩

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem under_mem_badPl (t : T) {PP : Pl D.host.E} (h : PP ∈ R.Pg ∨ PP ∈ R.Q t) :
    PP.under (𝓞 D.host.F) ∈ GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t := by
  classical
  exact Finset.mem_image.2 ⟨PP, Finset.mem_union.2 h, rfl⟩

theorem good_iff (t : T) (P : Pl D.host.E) : Good R t P ↔ P.under (𝓞 D.host.F) ∉ GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t := by
  classical
  constructor
  · intro h hm
    obtain ⟨PP, hPP, e⟩ := Finset.mem_image.1 hm
    obtain ⟨h1, h2⟩ := h PP (Finset.mem_union.1 hPP)
    rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq e.symm with h3 | h3
    · exact h1 h3.symm
    · exact h2 (GlobalTheory.GoodPrimes.isConjPl_iff.2 h3)
  · intro hw PP hPP
    exact ⟨fun e => hw (e ▸ under_mem_badPl R t hPP),
      fun e => hw (GlobalTheory.LevelPlaces.under_eq_of_isConjPl e ▸ under_mem_badPl R t hPP)⟩

theorem paramsV {F : Face D A} (hC : Core R F) (i : Fin D.R.m) (t : T) (h) (hh : IsOpsV R i t h) (s y)
    (hy : IsEigV R i t h s y) (h0 : y ≠ 0) :
    ∃ B, GlobalTheory.LFun.IsSysParamD D (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) (Vc D i).rank s B :=
  exists_param_definite (D.sp.V_sig _) (hC.models.vpos i) (R.cV i) (hC.models.cV i) (hC.lev.βV i) (L := R.datVt i t)
    (fun _ hPP => under_mem_badPl R t hPP) ((hC.models.HV i t).2.1.le (LinearMap.mem_range_self _ y))
    (fun e => h0 ((hC.models.HV i t).1 (e.trans (map_zero _).symm))) s fun P d hP hd =>
      (hh P ((good_iff R t P).2 hP) _ y).symm.trans
        ((congrArg (R.HV i t).e (hy P d ((good_iff R t P).2 hP) hd)).trans (map_smul _ _ _))

theorem paramsW (hP : GlobalTheory.Published.CuspRapidDecay) {F : Face D A} (hC : Core R F) (i : Fin D.R.m) (t : T) (c : Sys D)
    (hc : partW R i t c ≠ ⊥) : ∃ B', GlobalTheory.LFun.IsSysParamD D (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) D.R.r c B' ∧
    ∀ w, Good R t w → ∀ a ∈ B' w, ‖(a : ℂ)‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ (((D.R.r : ℝ) - 1) / 2) := by
  have rW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  obtain ⟨B, h1, h2⟩ := exists_param_part hP hC.models.inf (hC.lev.βW i) (L := R.datWp i R.triv)
    (fun PP hPP => under_mem_badPl R t (hPP.imp_right fun h => absurd h (Finset.notMem_empty _))) hc
  rw [rW] at h1 h2
  exact ⟨B, h1, fun w hw => h2 w ((good_iff R t w).1 hw)⟩

theorem paramsEx : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type)
    (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t, ParamsEx R i t :=
  fun hP _ _ _ _ _ _ _ _ _ _ _ R _ hG _ i t => ⟨paramsV R hG.core i t, paramsW R hP hG.core i t⟩

end GlobalTheory.DownLift.Params

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GammaOperatorSemisimpleOfConclusions
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

namespace GlobalTheory

section LetterAux

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem γD_letE_smul (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (g : W.Gam) (i : ZMod n)
    (x : W.DD T) : W.γD T g ((letE i : LetA O n) • x) = (letE i : LetA O n) • W.γD T g x := by
  rw [← algebraMap_smul W.EE (letE i : LetA O n) x, W.γD_smul, W.γE_ext, algebraMap_smul]
  congr 1
  funext j
  show W.γ₀ g ((letE i : LetA O n) j) = (letE i : LetA O n) j
  by_cases h : j = i
  · subst h; simp [letE]
  · simp [letE, Pi.single_eq_of_ne h]

theorem letE_mul_self (i : ZMod n) : (letE i : LetA O n) * letE i = letE i := by
  funext j
  by_cases h : j = i
  · subst h; simp [letE]
  · simp [letE, Pi.single_eq_of_ne h]

theorem sum_letE_eq_one [NeZero n] : ∑ i : ZMod n, (letE i : LetA O n) = 1 := by
  funext j
  simp [letE, Finset.sum_apply, Pi.single_apply]

theorem le_Mmax_of [NeZero n] (Mi : ZMod n → ℕ) (i : ZMod n) : Mi i ≤ Formalism.MainNotions.LiftingTheory.Mmax n Mi := by
  have h := Finset.le_sup (f := fun k : ℕ => Mi (k : ZMod n)) (Finset.mem_range.2 (ZMod.val_lt i))
  simp only [ZMod.natCast_zmod_val] at h
  exact h

theorem smul_letE_mem (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) (a : LetA O n)
    (x : W.DD T) (hx : a • x ∈ W.N T) : a • ((letE i : LetA O n) • x) ∈ W.N T := by
  rw [smul_smul, mul_comm, ← smul_smul]
  exact (W.N T).smul_mem _ hx

theorem letE_rec (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) (c : O)
    (y z : W.DD T) (h : W.π₀ • (y + c • z) = W.γD T W.gam z - z) :
    W.π₀ • ((letE i : LetA O n) • y + c • ((letE i : LetA O n) • z)) =
      W.γD T W.gam ((letE i : LetA O n) • z) - (letE i : LetA O n) • z := by
  rw [smul_comm c (letE i : LetA O n) z, ← smul_add, smul_smul, mul_comm W.π₀, ← smul_smul, h,
    smul_sub, γD_letE_smul]

theorem mem_N_of_letE [NeZero n] (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (x : W.DD T)
    (h : ∀ i : ZMod n, (letE i : LetA O n) • x ∈ W.N T) : x ∈ W.N T := by
  have e : x = ∑ i : ZMod n, (letE i : LetA O n) • x := by
    rw [← Finset.sum_smul, sum_letE_eq_one, one_smul]
  rw [e]
  exact Submodule.sum_mem _ (fun i _ => h i)

theorem mem_of_qp_pow_zero (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (x : W.DD T)
    (h : Formalism.MainNotions.LiftingTheory.qp W ^ 0 • x ∈ W.N T) : x ∈ W.N T := by
  rwa [pow_zero, one_smul] at h

end LetterAux

theorem dss_semisimple_of_used : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F), Formalism.MainNotions.DeltaInvariantLattices.DeltaInvariantNormBound D HW F Cm → Formalism.MainNotions.LiftingTheory.adm19 D HW F := by
  intro D HW F Cm hN l _ K s LL h
  have h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W ((HW l).W K s LL h) := hN.2.2.2.2.2.2.2.2.1 l K s LL h
  rw [Formalism.MainNotions.UnusedSlot35.DssRec.coreDss_iff_mem _ h9]
  intro hA T Mi hi hT hJ ug hug hv cO hc Y y₀ hy hΔ seq h0 hrec
  subst h0
  have hs : s = 1 := ((HW l).W_s K s LL h).symm.trans hA.2.1
  subst hs
  have hpl : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hCAl : Loc.CaseA K LL := by
    refine ⟨fun x hx => ?_, by rw [← hpl]; exact hA.2.2, h⟩
    obtain ⟨y, hy⟩ := hA.1.2 ⟨x, hx⟩
    have h2 := y.2.2
    have : ((y : ↥(K0 K)) : Om l) = x := congrArg Subtype.val hy
    rw [this] at h2
    exact h2
  haveI : FiniteDimensional ℚ_[l] ↥(K0 K) := ((D.loc l).PD K).finK₀
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  have hw1 : (D.loc l).v LL (algebraMap ↥(OL LL) ↥LL.1
      ((((HW l).W K 1 LL h).χΓ ((HW l).W K 1 LL h).gam : (↥(OL LL))ˣ) : ↥(OL LL)) - 1) = 1 := by
    have := ((HW l).W K 1 LL h).gam_gen
    rw [hA.2.1, Nat.cast_one] at this
    exact this
  have hug1 : ug ^ (l - 1) = (((HW l).W K 1 LL h).χΓ ((HW l).W K 1 LL h).gam) ^ (l - 1) := by
    have := hug
    rw [hpl] at this
    exact this
  have hug' : ug = ((HW l).W K 1 LL h).χΓ ((HW l).W K 1 LL h).gam :=
    GlobalTheory.units_eq_of_pow_pred_eq_of_val_one l (D.loc l) LL ug _ hug1 hv hw1
  have hc' : ∀ x : ℤ, ((l : ℕ) : ↥(OL LL)) * cO x = 1 - ((((((HW l).W K 1 LL h).χΓ
      ((HW l).W K 1 LL h).gam) ^ (-x) : (↥(OL LL))ˣ) : ↥(OL LL))) := by
    intro x
    have := hc x
    rw [hpl, hug'] at this
    exact this
  have hjx : ∀ (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ) (j : ℕ),
      Formalism.MainNotions.LiftingTheory.Over ((HW l).W K 1 LL h) τ i → IsJumpV ((D.loc l).PD K) T.ρ τ a → 0 < j → j ≤ Y →
      a + (j : ℤ) ∈ Formalism.MainNotions.LiftingTheory.xList ((HW l).W K 1 LL h) T (Formalism.MainNotions.LiftingTheory.Mmax _ Mi)
        (Formalism.MainNotions.LiftingTheory.Mmax _ hi) Y := by
    intro i τ a j hO hjump hj0 hjY
    have ha := hJ i τ hO a hjump
    have hM := le_Mmax_of Mi i
    have hH := le_Mmax_of hi i
    rw [Formalism.MainNotions.LiftingTheory.xList, Finset.mem_sort, Finset.mem_image]
    refine ⟨(a, (j : ℤ)), Finset.mem_product.2 ⟨?_, ?_⟩, rfl⟩
    · simp only [Formalism.MainNotions.LiftingTheory.jumpSet, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨?_, ?_⟩, τ, hjump⟩
      · have := ha.1; omega
      · have := ha.2; omega
    · rw [Finset.mem_Icc]; omega
  have hmem : ∀ i : ZMod (Module.finrank ℚ_[l] ↥(K0 K)),
      (letE i : LetA ↥(OL LL) _) • seq (Formalism.MainNotions.LiftingTheory.xList ((HW l).W K 1 LL h) T (Formalism.MainNotions.LiftingTheory.Mmax _ Mi)
        (Formalism.MainNotions.LiftingTheory.Mmax _ hi) Y).length ∈ ((HW l).W K 1 LL h).N T := by
    intro i
    have hDL : Formalism.MainNotions.CrystallineLiftingInputs.DL ((HW l).W K 1 LL h) T i ((letE i : LetA ↥(OL LL) _) • seq 0) := by
      refine ⟨by rw [smul_smul, letE_mul_self], fun δ hδ => ?_⟩
      rw [γD_letE_smul ((HW l).W K 1 LL h) T δ i (seq 0)]
      have e2 := hΔ δ hδ
      exact congrArg (fun z => (letE i : LetA ↥(OL LL) _) • z) e2
    have hYi : Formalism.MainNotions.LiftingTheory.qp ((HW l).W K 1 LL h) ^ Y • ((letE i : LetA ↥(OL LL) _) • seq 0) ∈
        ((HW l).W K 1 LL h).N T := by
      exact smul_letE_mem ((HW l).W K 1 LL h) T i _ (seq 0) hy
    have key := GlobalTheory.T.wachOperatorProduct_shift_mem_lattice D HW F Cm hN l K LL hCAl T hT i 0 Y cO hc' _
      (fun τ a j hO hjump hj hjY => hjx i τ a j hO hjump hj hjY)
      (fun k => (letE i : LetA ↥(OL LL) _) • seq k) hDL hYi
      (fun k hk => letE_rec ((HW l).W K 1 LL h) T i _ _ _ (hrec k hk))
    exact mem_of_qp_pow_zero ((HW l).W K 1 LL h) T _ key.2
  exact mem_N_of_letE ((HW l).W K 1 LL h) T _ hmem

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GammaSubOneDivUniformiserAtLetterOfConclusions
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

namespace GlobalTheory.AdmDssLet

open Formalism.MainNotions.LiftingTheory

section Gen

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem qp_isUnit (W : LocWach PD LL O v n) (hπu : IsUnit (algebraMap (LetA O n) W.EE W.π₀)) :
    IsUnit (algebraMap (LetA O n) W.EE (qp W)) := by
  have := W.EE_complete
  obtain ⟨u, hu⟩ := hπu
  have hj := (Ideal.mem_jacobson_bot.mp (IsAdicComplete.le_jacobson_bot _
    (Ideal.mem_span_singleton_self ((PD.p : ℕ) : W.EE)))) (↑u⁻¹ : W.EE)
  have e : algebraMap (LetA O n) W.EE (qp W) = (u : W.EE) * (((PD.p : ℕ) : W.EE) * ↑u⁻¹ + 1) := by
    rw [qp, map_add, ← hu, map_natCast]
    rw [mul_add, mul_one, mul_comm ((PD.p : ℕ) : W.EE), ← mul_assoc, Units.mul_inv, one_mul, add_comm]
  rw [e]
  exact u.isUnit.mul hj

theorem letE_mul_self (i : ZMod n) : (letE i : LetA O n) * letE i = letE i := by
  funext j
  by_cases hj : j = i
  · subst hj; simp [letE]
  · simp [letE, Pi.single_apply, hj]

theorem letter_of_qp_pow_mem (W : LocWach PD LL O v n)
    (hqu : IsUnit (algebraMap (LetA O n) W.EE (qp W))) (T : LocLat G Qp LL O) (i : ZMod n) (Y : ℕ)
    (y : W.DD T) (hy : qp W ^ Y • y ∈ W.Nl T i) :
    (letE i : LetA O n) • y = y ∧ qp W ^ Y • y ∈ W.N T := by
  obtain ⟨m, hm, hm'⟩ := Submodule.mem_map.1 hy
  have hm'' : (letE i : LetA O n) • m = qp W ^ Y • y := hm'
  have hqYu : IsUnit (algebraMap (LetA O n) W.EE (qp W ^ Y)) := by
    rw [map_pow]; exact hqu.pow _
  refine ⟨Formalism.MainNotions.UnusedSlot35.DssRec.smul_inj (E := W.EE) _ hqYu ?_, ?_⟩
  · rw [smul_smul, mul_comm, ← smul_smul, ← hm'', smul_smul, letE_mul_self]
  · rw [← hm'']; exact (W.N T).smul_mem _ hm

theorem mem_Nl_of (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) (a : LetA O n)
    (x : W.DD T) (hx : (letE i : LetA O n) • x = x) (hN : a • x ∈ W.N T) : a • x ∈ W.Nl T i := by
  refine Submodule.mem_map.2 ⟨_, hN, ?_⟩
  show (letE i : LetA O n) • (a • x) = a • x
  rw [smul_smul, mul_comm, ← smul_smul, hx]

theorem mem_xListL (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) (M h y' Y : ℕ)
    (τ : K →ₐ[Qp] LL) (a : ℤ) (j : ℕ) (hτ : Over W τ i) (ha : IsJumpV PD T.ρ τ a)
    (hwin : a ∈ Set.Icc (-(M : ℤ)) (h : ℤ)) (hj1 : y' < j) (hj2 : j ≤ Y) :
    a + (j : ℤ) ∈ Formalism.MainNotions.RamifiedCoefficientChains.xListL W T i M h y' Y := by
  unfold Formalism.MainNotions.RamifiedCoefficientChains.xListL
  rw [Finset.mem_sort, Finset.mem_image]
  refine ⟨(a, (j : ℤ)), ?_, rfl⟩
  rw [Finset.mem_product]
  refine ⟨?_, ?_⟩
  · classical
    unfold Formalism.MainNotions.RamifiedCoefficientChains.jumpSetL
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨hwin, τ, hτ, ha⟩
  · rw [Finset.mem_Icc]; constructor <;> push_cast <;> omega

end Gen

end GlobalTheory.AdmDssLet

namespace GlobalTheory

open GlobalTheory.AdmDssLet in

theorem adm18_of_N1used : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F), Formalism.MainNotions.DeltaInvariantLattices.DeltaInvariantNormBound D HW F Cm → Formalism.MainNotions.RamifiedCoefficientChains.adm18 D HW F := by
  intro D HW F Cm hN l _ K s LL h
  have h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W ((HW l).W K s LL h) := hN.2.2.2.2.2.2.2.2.1 l K s LL h
  rw [Formalism.MainNotions.UnusedSlot35.DssRec.dssLet_iff_mem _ h9]
  intro hA T Mi hi hT hJ ug hug hv cO hc i y' Y y₀ hyY hy hΔ seq h0 hrec
  have hs : s = 1 := ((HW l).W_s K s LL h).symm.trans hA.2.1
  subst hs
  have hpl : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hCAl : Loc.CaseA K LL := by
    refine ⟨fun x hx => ?_, by rw [← hpl]; exact hA.2.2, h⟩
    obtain ⟨y, hy⟩ := hA.1.2 ⟨x, hx⟩
    have h2 := y.2.2
    have : ((y : ↥(K0 K)) : Om l) = x := congrArg Subtype.val hy
    rw [this] at h2
    exact h2

  have hgen : (D.loc l).v LL (algebraMap ↥(OL LL) ↥LL.1
      ((((HW l).W K 1 LL h).χΓ ((HW l).W K 1 LL h).gam : (↥(OL LL))ˣ) : ↥(OL LL)) - 1) = 1 := by
    have h1 := ((HW l).W K 1 LL h).gam_gen
    have h2 : ((((HW l).W K 1 LL h).s : ℕ) : WithTop ℚ) = 1 := by rw [hA.2.1]; rfl
    exact h1.trans h2
  have hug2 : ug ^ (l - 1) = (((HW l).W K 1 LL h).χΓ ((HW l).W K 1 LL h).gam) ^ (l - 1) := by
    have e : ((D.loc l).PD K).p - 1 = l - 1 := congrArg (· - 1) hpl
    rw [← e]; exact hug
  have hug' : ug = ((HW l).W K 1 LL h).χΓ ((HW l).W K 1 LL h).gam :=
    GlobalTheory.units_eq_of_pow_pred_eq_of_val_one l (D.loc l) LL ug _ hug2 hv hgen
  subst hug'
  have hc' : ∀ x : ℤ, ((l : ℕ) : ↥(OL LL)) * cO x =
      1 - (((((HW l).W K 1 LL h).χΓ ((HW l).W K 1 LL h).gam) ^ (-x) : (↥(OL LL))ˣ) : ↥(OL LL)) := by
    intro x
    have e : ((((D.loc l).PD K).p : ℕ) : ↥(OL LL)) = ((l : ℕ) : ↥(OL LL)) := congrArg _ hpl
    rw [← e]; exact hc x

  have hqu := qp_isUnit _ (Formalism.MainNotions.UnusedSlot35.DssRec.π₀_unit _ h9 hA T hT)
  obtain ⟨hey, hN0⟩ := letter_of_qp_pow_mem _ hqu T i Y y₀ hy
  have hDL0 : Formalism.MainNotions.CrystallineLiftingInputs.DL ((HW l).W K 1 LL h) T i (seq 0) := by
    rw [h0]; exact ⟨hey, hΔ⟩
  rw [← h0] at hN0
  obtain ⟨hDL, hmem⟩ := GlobalTheory.T.wachOperatorProduct_shift_mem_lattice D HW F Cm hN l K LL hCAl T hT i y' Y cO hc'
    (Formalism.MainNotions.RamifiedCoefficientChains.xListL ((HW l).W K 1 LL h) T i (Mi i) (hi i) y' Y)
    (fun τ a j hτ ha hj1 hj2 => mem_xListL _ T i (Mi i) (hi i) y' Y τ a j hτ ha (hJ i τ hτ a ha) hj1 hj2)
    seq hDL0 hN0 hrec
  exact mem_Nl_of _ T i _ _ hDL.1 hmem

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharacterValueAtSplitPlaceDeterminant
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.Lev Formalism.L2.DIV Formalism.IndefR.Mult
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.HeckeDetValue

theorem chr_detAt : ∀ {D : D7} (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (Q : Finset (Pl D.host.E)) (V : HSp D) (P : Pl D.host.E) (k : ℕ) (α : GA D V) (z : (AE D)ˣ), ChrEq c χ → GlobalTheory.ExportSeries.UnramOutside c Q → GlobalTheory.ExportSeries.SplitSet Q → Bridge.SplitOff P (Q : Set (Pl D.host.E)) → IsHeckeAt V P k α → IsDetAt (idemAt P) V α z → ((c z : Circle) : ℂ) = ((χ.val P : ℂˣ) : ℂ) ^ k := by
  intro D c χ Q V P k α z hc hU hS hoff hα hz
  exact GlobalTheory.HeckeDetChar.chi_detAt hc hU hS hoff hα hz

end GlobalTheory.HeckeDetValue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLanglandsDataTransportLocalFieldIsoStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLanglandsData_transport_localFieldIso : ∀ (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [CharZero k'] (i : k ≃+* k'), Continuous i → ∀ (l : List (Segment k)) (l' : List (Segment k')) (x : IrrGL k) (x' : IrrGL k'), List.Forall₂ (fun (Δ : Segment k) (Δ' : Segment k') => RepRel i Δ.first Δ'.first ∧ Δ.len = Δ'.len) l l' → RepRel i x x' → IsL (l : Multiset (Segment k)) x.rep → IsL (l' : Multiset (Segment k')) x'.rep := by
  first | exact @GlobalTheory.LocLanglands.isL_transport | exact GlobalTheory.LocLanglands.isL_transport | (intros; apply GlobalTheory.LocLanglands.isL_transport <;> assumption)
end

