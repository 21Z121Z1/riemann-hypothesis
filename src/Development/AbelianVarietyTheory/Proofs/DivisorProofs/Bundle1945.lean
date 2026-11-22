import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1833
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1829
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1915
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0970
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0083
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0271
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0841
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0451
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0542
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1927
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1919
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1891
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1826
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0354
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1148
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1658
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1930

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroStandardThetaLineReadAdelic
section
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.VacRead

def posSig {D : D7} (S : HSp D) : HSp D := {S with sig := fun _ => (S.rank, 0)}

theorem hasSignature_one (n : ℕ) : Formalism.UG.HasSignature (1 : Matrix (Fin n) (Fin n) ℂ) n 0 := by
  refine ⟨(Equiv.sumEmpty (Fin n) (Fin 0)).symm, 1, ?_⟩
  ext i j
  rcases i with i | i
  · rcases j with j | j
    · simp [Formalism.UG.Jpq, Formalism.UG.cT, Matrix.one_apply]
    · exact j.elim0
  · exact i.elim0

theorem sigOK_posSig {D : D7} (S : HSp D) (h : S.gram = 1) : (posSig S).SigOK := by
  intro τ
  show Formalism.UG.HasSignature (S.gram.map τ) S.rank 0
  rw [h, Matrix.map_one _ (map_zero τ) (map_one τ)]
  exact hasSignature_one _

open scoped ComplexOrder in
theorem isCartanInv_one {D : D7} (S : HSp D) (h : S.gram = 1) (τ : D.what₂.Tau) : IsCartanInv (gramAt D S τ) 1 := by
  have : gramAt D S τ = 1 := by
    show (HSpace.gram S).map (tauE D τ) = 1
    rw [h, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [this]
  exact ⟨by simp, by simp, by simpa using (Matrix.PosDef.one : Matrix.PosDef (1 : Matrix (Fin S.rank) (Fin S.rank) ℂ))⟩

theorem vac_exists_gram_one {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (hψ : IsStdChar D ψ (-1))
    (hθ : IsInfFam θ) (S T : HSp D) (gS : S.gram = 1) (gT : T.gram = 1)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) :
    ∃ f : WO S T → ℂ, IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) ΛS ΛT f := by
  obtain ⟨f, hf⟩ := GlobalTheory.VacuumO.vacExists D ψ θ hψ hθ (posSig S) (posSig T) (fun _ => 1) (fun _ => 1)
    (sigOK_posSig S gS) (sigOK_posSig T gT) (isCartanInv_one S gS) (isCartanInv_one T gT) ΛS ΛT hS hT
  exact ⟨f, hf.1, ⟨hf.2.inf, ⟨hf.2.theta.quasi, hf.2.theta.level, hf.2.theta.cont, hf.2.theta.smooth⟩, hf.2.lat,
    hf.2.fock, hf.2.norm⟩⟩

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {r : D.host.E}

theorem Hf_div_scale (hc : Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ) (h : IsScale D cc r) {a d : ℕ} (z x : VC D a d) :
    Hf D (tor0 D D.host.ccK δ) (fun τ i j => z τ i j / embT D τ r) (fun τ i j => x τ i j / embT D τ r) =
      Hf D (tor0 D cc δ) z x := by
  have hr : r ≠ 0 := IsScale.ne_zero hc.1.1 h
  have hA := area_pos hc
  have hx := xiR_pos D
  have key : ∀ τ, Complex.normSq (embT D τ r) * area (lamOf D D.host.ccK δ) = area (lamOf D cc δ) := by
    intro τ
    have h1 := normSq_scale hc.1.1 h δ τ
    have h2 := normSq_scale D.host.ccK_ne_bot (isScale_one D) δ τ
    rw [map_one, mul_one] at h2
    rw [Complex.normSq_mul, h2] at h1
    have h3 : (2 * Formalism.L2.Pj.xiR D) * (Complex.normSq (embT D τ r) * area (lamOf D D.host.ccK δ)) =
        (2 * Formalism.L2.Pj.xiR D) * area (lamOf D cc δ) := by rw [← h1]; ring
    exact mul_left_cancel₀ (by positivity) h3
  have hL : ∀ c : Ideal (𝓞 D.host.K), (tor0 D c δ).abelian₂ = lamOf D c δ := fun _ => rfl
  rw [Formalism.MainNotions.TaylorLogMetric.Hf, Formalism.MainNotions.TaylorLogMetric.Hf, hL, hL, Finset.sum_div, Finset.sum_div]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.sum_div, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_div, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  have ht : embT D τ r ≠ 0 := (map_ne_zero _).2 hr
  have htc : starRingEnd ℂ (embT D τ r) ≠ 0 := (map_ne_zero _).2 ht
  have hK : (area (lamOf D D.host.ccK δ) : ℂ) ≠ 0 := by
    have : 0 < area (lamOf D D.host.ccK δ) := by
      have := key τ
      have h0 : 0 < Complex.normSq (embT D τ r) := Complex.normSq_pos.2 ht
      nlinarith
    exact_mod_cast this.ne'
  rw [← key τ, map_div₀]
  push_cast
  rw [← Complex.mul_conj]
  field_simp

theorem th_div_scale (hc : Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ) (h : IsScale D cc r) {a d : ℕ}
    {L Ls : GlobalTheory.InertSign.Lat D a} {L' Lt : GlobalTheory.InertSign.Lat D d}
    (hLa : ∀ x ∈ Formalism.MainNotions.TaylorLogMetric.La D (tor0 D cc δ) L L',
      (fun τ i j => x τ i j / embT D τ r) ∈ Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK δ) Ls Lt)
    {Φ : VC D a d → ℂ} (hΦ : Φ ∈ Th D (tor0 D D.host.ccK δ) Ls Lt) :
    (fun Y => Φ (fun τ i j => Y τ i j / embT D τ r)) ∈ Th D (tor0 D cc δ) L L' := by
  refine ⟨?_, ?_⟩
  · have hl : Differentiable ℂ (fun Y : VC D a d => (fun τ i j => Y τ i j / embT D τ r : VC D a d)) := by
      fun_prop
    exact hΦ.1.comp hl
  · intro x hx z
    have e1 := hΦ.2 _ (hLa x hx) (fun τ i j => z τ i j / embT D τ r)
    have hal : Formalism.MainNotions.TaylorLogMetric.al D (tor0 D cc δ) x =
        Formalism.MainNotions.TaylorLogMetric.al D (tor0 D D.host.ccK δ) (fun τ i j => x τ i j / embT D τ r) := by
      simp only [Formalism.MainNotions.TaylorLogMetric.al, Hf_div_scale hc h]
    have hadd : (fun τ i j => (z + x) τ i j / embT D τ r) =
        (fun τ i j => z τ i j / embT D τ r) + (fun τ i j => x τ i j / embT D τ r) := by
      funext τ i j
      simp [add_div]
    show _ = Φ fun τ i j => z τ i j / embT D τ r
    rw [← e1, hal]
    simp only [Formalism.MainNotions.TaylorLogMetric.U]
    rw [Hf_div_scale hc h, Hf_div_scale hc h, hadd]

end GlobalTheory.VacRead

namespace GlobalTheory.VacRead

theorem exists_vac_reads : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∃ e0 ∈ Th D (tor0 D cc δ) (stdL D a) (stdL D d), e0 ≠ 0 ∧ ∃ f₀, Reads ψ θ hS hT cc δ r e0 f₀ := by
  intro D ψ θ S T a d hS hT cc δ r hset
  subst hS hT
  obtain ⟨hψ, hθ, gS, gT, crv, sc⟩ := hset
  have hc : cc ≠ ⊥ := crv.1.1
  have hr : r ≠ 0 := IsScale.ne_zero hc sc
  have hδ : δ ≠ 0 := delta_ne_zero crv
  have hS1 : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (1 : GL (Fin S.rank) D.host.E).1 * S.gram *
      (1 : GL (Fin S.rank) D.host.E).1 = 1 := by
    rw [gS]; simp [Formalism.UG.cT]
  have hT1 : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (1 : GL (Fin T.rank) D.host.E).1 * T.gram *
      (1 : GL (Fin T.rank) D.host.E).1 = 1 := by
    rw [gT]; simp [Formalism.UG.cT]
  have hLs : Formalism.MainNotions.StandardLatticesGL3.SD D (lsB D cc r S.rank) := GlobalTheory.T.invDifferentLatticeProductHermitian_isSelfDual D cc r S.rank hc sc
  have hLt : Formalism.MainNotions.StandardLatticesGL3.SD D (stdL D T.rank) := GlobalTheory.MovedVacuum.sd_stdL D T.rank
  obtain ⟨ΛS, hΛS, hSd⟩ := GlobalTheory.MovedDict.isSelfDualC_inV S 1 hS1 _ hLs
  obtain ⟨ΛT, hΛT, hTd⟩ := GlobalTheory.MovedDict.isSelfDualC_inV T 1 hT1 _ hLt
  obtain ⟨f, hf⟩ := vac_exists_gram_one ψ θ hψ hθ S T gS gT ΛS ΛT hSd hTd
  rw [hΛS, hΛT] at hf
  obtain ⟨Φ, hΦd, hΦ⟩ := GlobalTheory.FockPos.vacuum_real_entire ψ θ S T 1 1 _ _ hS1 hT1 f hf
  have hth := theta_of_unit_vacuum ψ θ S T 1 1 hS1 hT1 δ hδ _ _ hLs hLt f hf Φ hΦd hΦ
  have hLa : ∀ x ∈ Formalism.MainNotions.TaylorLogMetric.La D (tor0 D cc δ) (stdL D S.rank) (stdL D T.rank),
      (fun τ i j => x τ i j / embT D τ r) ∈ Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK δ) (lsB D cc r S.rank) (stdL D T.rank) := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := GlobalTheory.ThetaLatImage.La_sub hx
    have h2 := GlobalTheory.ThetaLatImage.pt_mem_La (δ := δ) (GlobalTheory.T.inv_smul_mem_rationalHomLatticeScaled_of_normScale D cc r S.rank T.rank hc sc z hz) 1
    convert h2 using 1
    funext τ i j
    rw [one_smul, GlobalTheory.ThetaLatImage.pt_apply, GlobalTheory.ThetaLatImage.pt_apply]
    have ht : embT D τ r ≠ 0 := (map_ne_zero _).2 hr
    simp only [Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀]
    field_simp
  have hG := th_div_scale crv sc hLa hth
  have hback : ∀ Z : VC D S.rank T.rank,
      (δ⁻¹ • fun τ i j => (δ * embT D τ r * Z τ i j) / embT D τ r : VC D S.rank T.rank) = Z := by
    intro Z
    funext τ i j
    have ht : embT D τ r ≠ 0 := (map_ne_zero _).2 hr
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
  refine ⟨_, hG, ?_, f, (reads_iff crv sc _ f).2 ⟨hf.2.theta, fun w hw => ?_⟩⟩
  · intro h0
    apply GlobalTheory.StepMove.vacO_ne_zero hf
    refine GlobalTheory.TwistFactorCompare.theta_eq_zero_of_real hf.2.theta fun w hw => ?_
    rw [hΦ w hw]
    have e := congrFun h0 (fun τ i j => δ * embT D τ r * GlobalTheory.FockPos.zCo θ 1 1 w τ i j)
    simp only [Pi.zero_apply, hback] at e
    rw [e, mul_zero]
  · rw [hΦ w hw]
    simp only [hback]

end GlobalTheory.VacRead
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumVolShellInterTranslate
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
open GlobalTheory.PureMatch GlobalTheory.SquareFlipReach ValuativeRel

noncomputable section
namespace GlobalTheory.PureMatch.ShellVolume

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

open IsDedekindDomain NumberField MeasureTheory Matrix in
open scoped TensorProduct in
attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar _root_.GlobalTheory.LocalData.complRel
  _root_.GlobalTheory.LocalData.isLocalField _root_.GlobalTheory.FunObj.borelKw
  _root_.GlobalTheory.FunObj.borelSpaceKw in
attribute [local instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv in
open ValuativeRel in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem _root_.GlobalTheory.PureMatch.ShellVolume.isOpen_translate {a : ℕ} (u u' : GL (Fin a) k) :
    IsOpen {g : GL (Fin a) k | u * g * u' ∈ _root_.GlobalTheory.SplitWeil.KO k (Fin a)} :=
  _root_.GlobalTheory.SplitFlip.isOpen_KO.preimage
    ((continuous_const.mul continuous_id).mul continuous_const)

end GlobalTheory.PureMatch.ShellVolume

open IsDedekindDomain NumberField MeasureTheory Matrix in
open scoped TensorProduct in
attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar _root_.GlobalTheory.LocalData.complRel
  _root_.GlobalTheory.LocalData.isLocalField _root_.GlobalTheory.FunObj.borelKw
  _root_.GlobalTheory.FunObj.borelSpaceKw in
attribute [local instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv in
open ValuativeRel in

theorem _root_.GlobalTheory.PureMatch.ShellVolume.finsum_vol_shell_inter_translate : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (a : ℕ) (ϖ : kˣ) (u u' : GL (Fin a) k), _root_.GlobalTheory.SplitFlip.IsUnif ϖ →
    ∑ᶠ m : {m : Fin a → ℤ // Antitone m}, (_root_.GlobalTheory.SplitFlip.haarVol (_root_.GlobalTheory.SplitWeil.KO k (Fin a))).real (_root_.GlobalTheory.SplitFlip.shellSet ϖ m.1 ∩ {g | u * g * u' ∈ _root_.GlobalTheory.SplitWeil.KO k (Fin a)}) = 1 := by
  intro k _ _ _ _ _ _ a ϖ u u' hϖ
  have hv : valuation k ↑ϖ = uniformizer k := hϖ
  letI : MeasurableSpace (GL (Fin a) k) := Units.instMeasurableSpace
  set K := _root_.GlobalTheory.SplitWeil.KO k (Fin a) with hK
  set μ := _root_.GlobalTheory.SplitFlip.haarVol K with hμ
  haveI : μ.IsHaarMeasure := _root_.GlobalTheory.SplitFlip.isHaarMeasure_haarVol_KO
  haveI : μ.IsMulRightInvariant := _root_.GlobalTheory.SplitFlip.isMulRightInvariant_of_haar μ
  set S : Set (GL (Fin a) k) := {g | u * g * u' ∈ K} with hS
  have hshell : ∀ m : Fin a → ℤ,
      _root_.GlobalTheory.SplitFlip.shellSet ϖ m = _root_.GlobalTheory.GLDoubling.cell k (Fin a) ϖ m := by
    intro m
    unfold _root_.GlobalTheory.GLDoubling.cell _root_.GlobalTheory.SplitFlip.shellSet
    congr 1
    ext : 1
    rw [_root_.GlobalTheory.GLDoubling.val_torusElt, _root_.GlobalTheory.SplitFlip.diagGL_val]
    simp
  simp only [hshell]
  have hSopen : IsOpen S := _root_.GlobalTheory.PureMatch.ShellVolume.isOpen_translate u u'
  have hSeq : S = (fun x => u⁻¹ * x * u'⁻¹) '' (K : Set (GL (Fin a) k)) := by
    ext g
    constructor
    · intro hg
      exact ⟨u * g * u', hg, by group⟩
    · rintro ⟨x, hx, rfl⟩
      show u * (u⁻¹ * x * u'⁻¹) * u' ∈ K
      have hx' : u * (u⁻¹ * x * u'⁻¹) * u' = x := by group
      rw [hx']
      exact hx
  have hScpt : IsCompact S := by
    rw [hSeq]
    exact _root_.GlobalTheory.SplitFlip.isCompact_KO.image
      ((continuous_const.mul continuous_id).mul continuous_const)
  have hμS : μ S = 1 := by
    have : S = (fun g => u * g) ⁻¹' ((fun g => g * u') ⁻¹' (K : Set (GL (Fin a) k))) := by
      ext g; simp [hS, mul_assoc]
    rw [this, measure_preimage_mul, measure_preimage_mul_right]
    exact _root_.GlobalTheory.SplitFlip.haarVol_self _root_.GlobalTheory.SplitFlip.isOpen_KO le_rfl
  obtain ⟨t, ht⟩ := hScpt.elim_finite_subcover
    (fun e : {m : Fin a → ℤ // Antitone m} => _root_.GlobalTheory.GLDoubling.cell k (Fin a) ϖ e.1)
    (fun e => _root_.GlobalTheory.GLDoubling.isOpen_cell _ _)
    (by rw [_root_.GlobalTheory.GLDoubling.iUnion_cell hv]; exact Set.subset_univ _)
  have hdisj := _root_.GlobalTheory.GLDoubling.pairwise_disjoint_cell (k := k) (N := a) hv
  have hsupp : Function.support (fun e : {m : Fin a → ℤ // Antitone m} =>
      μ.real (_root_.GlobalTheory.GLDoubling.cell k (Fin a) ϖ e.1 ∩ S)) ⊆ ↑t := by
    intro e he
    by_contra het
    apply he
    have hempty : _root_.GlobalTheory.GLDoubling.cell k (Fin a) ϖ e.1 ∩ S = ∅ := by
      ext g
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
      intro hge hgS
      obtain ⟨i, hi, hgi⟩ := Set.mem_iUnion₂.mp (ht hgS)
      have hie : i ≠ e := fun h => het (h ▸ hi)
      exact Set.disjoint_left.mp (hdisj hie) hgi hge
    simp [hempty]
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  have hpd : (↑t : Set {m : Fin a → ℤ // Antitone m}).PairwiseDisjoint
      (fun e => _root_.GlobalTheory.GLDoubling.cell k (Fin a) ϖ e.1 ∩ S) := by
    intro i _ j _ hij
    exact (hdisj hij).mono Set.inter_subset_left Set.inter_subset_left
  have hmeas : ∀ i ∈ t, MeasurableSet (_root_.GlobalTheory.GLDoubling.cell k (Fin a) ϖ i.1 ∩ S) := fun i _ =>
    (_root_.GlobalTheory.GLDoubling.isOpen_cell _ _).measurableSet.inter hSopen.measurableSet
  have hfin : ∀ i ∈ t, μ (_root_.GlobalTheory.GLDoubling.cell k (Fin a) ϖ i.1 ∩ S) ≠ ⊤ := fun i _ =>
    ne_top_of_le_ne_top (by rw [hμS]; exact ENNReal.one_ne_top) (measure_mono Set.inter_subset_right)
  rw [← measureReal_biUnion_finset hpd hmeas hfin]
  have hU : (⋃ e ∈ t, _root_.GlobalTheory.GLDoubling.cell k (Fin a) ϖ e.1 ∩ S) = S := by
    apply Set.Subset.antisymm
    · exact Set.iUnion₂_subset fun _ _ => Set.inter_subset_right
    · intro g hg
      obtain ⟨i, hi, hgi⟩ := Set.mem_iUnion₂.mp (ht hg)
      exact Set.mem_iUnion₂.mpr ⟨i, hi, hgi, hg⟩
  rw [hU, measureReal_def, hμS, ENNReal.toReal_one]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockMinorPolZero
section
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormDictEx

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.NormDictEx.Jets

open Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.AdForm GlobalTheory.AdForm.VacRead GlobalTheory.FockCompare GlobalTheory.MixPer GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Core.Rk

variable {D : D7}

theorem xiN_differentiable (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (δ : ℂ) (sc : ℝ)
    (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (hgS : S.gram = 1) (hgT : T.gram = 1) (hδ : δ ≠ 0)
    (hsc : sc * ‖δ‖ ^ 2 = 2 * Formalism.L2.Pj.xiR D) (f : WO S T → ℂ) (hf1 : IsThetaFunO ψ S T f)
    (hf2 : ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 1) f) :
    Differentiable ℂ (xiN θ S T rfl rfl δ sc f) := by
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨hF, hann⟩ := GlobalTheory.VacUnique.Ann.vacuum_annihilation D θ σ hσ ψ hψ S T (fun _ => 1) (fun _ => 1) f
    hf1 hf2
  set F : RW T S → ℂ := fun z => f (iotaW σ T S z) with hFdef
  set r : ℝ := sc / 2 with hr
  let L : RW T S →L[ℂ] RW T S := (-δ⁻¹) • ContinuousLinearMap.id ℂ (RW T S)
  have hL : ∀ Z τ i j, L Z τ i j = -(δ⁻¹ * Z τ i j) := fun Z τ i j => by simp [L]
  set E : RW T S → ℂ := fun Z => Complex.exp ((Real.pi * r * ∑ τ, ∑ i, ∑ j, ‖Z τ i j‖ ^ 2 : ℝ) : ℂ) with hE
  have hxi : xiN θ S T rfl rfl δ sc f = fun Z => F (L Z) * E Z := by
    funext Z
    unfold xiN
    have hp : realPt θ (fun τ => Matrix.of fun i j => -(δ⁻¹ * Z τ (Fin.cast rfl i) (Fin.cast rfl j))) =
        iotaW σ T S (L Z) := by
      refine realPt_eq hθ _ _ (by funext i j; exact hσ.fin _) fun τ => ?_
      funext i j
      show θ τ (infPart D (σ fun τ' => L Z τ' i j)) = _
      rw [hσ.comp]
      simp [hL]
    rw [hp, mul_comm]
    congr 2
    show (Real.pi : ℂ) / 2 * ((sc : ℂ) * ∑ τ, ∑ i, ∑ j, Z τ i j * starRingEnd ℂ (Z τ i j)) = _
    simp_rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [hr]; push_cast; ring
  rw [hxi]
  have hdG : ∀ Z Y, fderiv ℝ (fun Z => F (L Z)) Z Y = fderiv ℝ F (L Z) (L Y) := fun Z Y => by
    have h : HasFDerivAt (fun Z => F (L Z)) ((fderiv ℝ F (L Z)).comp (L.restrictScalars ℝ)) Z :=
      (hF (L Z)).hasFDerivAt.comp Z (L.restrictScalars ℝ).hasFDerivAt
    rw [h.fderiv]; rfl
  refine GlobalTheory.FockPos.differentiable_mul_of_cr (fun Z => F (L Z)) E
    (fun Z Y => (2 * Real.pi * r * ∑ τ, ∑ i, ∑ j, Z τ i j * starRingEnd ℂ (Y τ i j) : ℂ))
    (hF.comp (L.restrictScalars ℝ).differentiable) (GlobalTheory.FockPos.gauss_cr r).1 (fun Z Y => ?_)
    (GlobalTheory.FockPos.gauss_cr r).2
  rw [hdG, hdG]
  have hj : GlobalTheory.VacUnique.jO S T (fun _ => 1) (fun _ => 1) (L Y) = L (Complex.I • Y) := by
    rw [L.map_smul]; funext τ; rw [GlobalTheory.VacUnique.jO_apply]
    change Complex.I • ((1 : Matrix (Fin T.rank) (Fin T.rank) ℂ) * Matrix.of (L Y τ) *
      (1 : Matrix (Fin S.rank) (Fin S.rank) ℂ)) = _
    rw [Matrix.one_mul, Matrix.mul_one]; rfl
  have h := hann (L Z) (L Y)
  rw [hj] at h
  have hdd : δ⁻¹ * starRingEnd ℂ δ⁻¹ = (((‖δ‖ ^ 2)⁻¹ : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_inv, Complex.normSq_eq_norm_sq]
  have hom : ∀ Y' : RW T S, GlobalTheory.VacUnique.omO S T (L Z) (L Y') =
      ∑ τ, 2 * (Complex.I * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * (((‖δ‖ ^ 2)⁻¹ : ℝ) : ℂ) *
        ∑ i, ∑ j, Z τ i j * starRingEnd ℂ (Y' τ i j)).re := by
    intro Y'
    rw [GlobalTheory.VacUnique.omO_apply]
    refine Finset.sum_congr rfl fun τ _ => ?_
    show 2 * (tauE D τ D.host.xi0 * GlobalTheory.VacUnique.hAt S T τ (L Z τ) (L Y' τ)).re = _
    rw [GlobalTheory.FockPos.xi_zero_eq_host τ]
    erw [hAt_one S T hgS hgT τ (L Z τ) (L Y' τ)]
    have hs : ∑ i, ∑ j, L Z τ i j * starRingEnd ℂ (L Y' τ i j) =
        (((‖δ‖ ^ 2)⁻¹ : ℝ) : ℂ) * ∑ i, ∑ j, Z τ i j * starRingEnd ℂ (Y' τ i j) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hL, hL, ← hdd]
      simp only [map_neg, map_mul]
      ring
    rw [hs]
    congr 2
    ring
  rw [hom, hom] at h
  have hs2 : ∀ τ, (∑ i, ∑ j, Z τ i j * starRingEnd ℂ ((Complex.I • Y) τ i j)) =
      -Complex.I * ∑ i, ∑ j, Z τ i j * starRingEnd ℂ (Y τ i j) := fun τ => by
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_I, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  simp only [hs2] at h
  have key := key_sum (Formalism.L2.Pj.xiR D) ((‖δ‖ ^ 2)⁻¹) fun τ => ∑ i, ∑ j, Z τ i j * starRingEnd ℂ (Y τ i j)
  have hrk : Formalism.L2.Pj.xiR D * (‖δ‖ ^ 2)⁻¹ = r :=
    scale_eq _ _ _ (pow_ne_zero 2 (norm_ne_zero_iff.2 hδ)) hsc
  rw [hrk] at key
  show _ = -((2 * Real.pi * r * ∑ τ, ∑ i, ∑ j, Z τ i j * starRingEnd ℂ (Y τ i j) : ℂ) * F (L Z))
  linear_combination h + Real.pi * Complex.I * F (L Z) * key +
    2 * Real.pi * r * (∑ τ, ∑ i, ∑ j, Z τ i j * starRingEnd ℂ (Y τ i j)) * F (L Z) * Complex.I_sq

theorem frAt_one {n : ℕ} : GlobalTheory.FockPos.frAt (1 : GL (Fin n) D.host.E) = fun _ => 1 := by
  funext τ
  simp [GlobalTheory.FockPos.frAt]

theorem eq_gauss_mul (θ : InfFam D) (hθ : IsInfFam θ) (S T : HSp D) (δ : ℂ) (sc : ℝ) (hδ : δ ≠ 0)
    (hsc : sc * ‖δ‖ ^ 2 = 2 * Formalism.L2.Pj.xiR D) (f : WO S T → ℂ) (w : WO S T) (hw : w.map (finPart D) = 0) :
    f w = GlobalTheory.FockPos.gaussO θ 1 1 w * xiN θ S T rfl rfl δ sc f ((-δ) • GlobalTheory.FockPos.zCo θ 1 1 w) := by
  have hz : ∀ τ, GlobalTheory.FockPos.zCo θ (1 : GL (Fin S.rank) D.host.E) (1 : GL (Fin T.rank) D.host.E) w τ = compAt θ τ w := by
    intro τ
    simp only [GlobalTheory.FockPos.zCo, frAt_one, inv_one, Matrix.one_mul, Matrix.mul_one]
    rfl
  set y := GlobalTheory.FockPos.zCo θ (1 : GL (Fin S.rank) D.host.E) (1 : GL (Fin T.rank) D.host.E) w with hy
  have hp : realPt θ (fun τ => Matrix.of fun i j => -(δ⁻¹ * ((-δ) • y) τ (Fin.cast rfl i) (Fin.cast rfl j))) = w := by
    refine realPt_eq hθ _ w hw fun τ => ?_
    funext i j
    rw [← hz τ]
    simp only [Matrix.of_apply, Fin.cast_eq_self, Pi.smul_apply, smul_eq_mul]
    field_simp
  unfold xiN
  rw [hp, GlobalTheory.FockPos.gaussO, ← hy, ← mul_assoc, ← Complex.exp_add]
  have hH : HV sc ((-δ) • y) ((-δ) • y) = (sc : ℂ) * (((‖δ‖ ^ 2 : ℝ) : ℂ) * ∑ τ, ∑ i, ∑ j, ((‖y τ i j‖ ^ 2 : ℝ) : ℂ)) := by
    show (sc : ℂ) * (∑ τ, ∑ i, ∑ j, ((-δ) • y) τ i j * starRingEnd ℂ (((-δ) • y) τ i j)) = _
    congr 1
    simp only [Finset.mul_sum, Pi.smul_apply, smul_eq_mul, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_mul, norm_neg]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    push_cast; ring
  have hc : (sc : ℂ) * ((‖δ‖ ^ 2 : ℝ) : ℂ) = 2 * (Formalism.L2.Pj.xiR D : ℂ) := by exact_mod_cast hsc
  have h0 : -((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ i, ∑ j, ((‖y τ i j‖ ^ 2 : ℝ) : ℂ) +
      (Real.pi : ℂ) / 2 * HV sc ((-δ) • y) ((-δ) • y) = 0 := by
    rw [hH, ← mul_assoc (sc : ℂ), hc, Complex.ofReal_mul]
    ring
  rw [h0, Complex.exp_zero, one_mul]

theorem apply_minorPol {a d : ℕ} {n : D.what₂.Tau → ℕ} (U : Tup D a d n)
    (l : MvPolynomial (Formalism.MainNotions.GL3Theta.Idx D a d) ℂ →ₗ[ℂ] ℂ) (p : ℂ) (G : Formalism.MainNotions.TaylorLogMetric.VC D a d → ℂ)
    (h : ∀ k : Formalism.MainNotions.GL3Theta.Idx D a d →₀ ℕ, l (MvPolynomial.monomial k 1) =
      p ^ (k.sum fun _ e => e) * Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) G) :
    l (minorPol D U) = p ^ (a * ∑ τ, n τ) * Formalism.MainNotions.GL3Theta.applyAt0 D (minorPol D U) G := by
  conv_lhs => rw [(minorPol D U).as_sum]
  rw [map_sum l, Formalism.MainNotions.GL3Theta.applyAt0, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α hα => ?_
  have hk := GlobalTheory.RotJets.card_of_mem_support U hα
  rw [Finsupp.card_toMultiset] at hk
  have e : (MvPolynomial.monomial α ((minorPol D U).coeff α) : MvPolynomial (Formalism.MainNotions.GL3Theta.Idx D a d) ℂ) =
      (minorPol D U).coeff α • MvPolynomial.monomial α 1 := by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  have hk' : (α.sum fun _ e => e) = a * ∑ τ, n τ := hk
  rw [e, map_smul, h, GlobalTheory.FockPos.applyAt0_monomial', hk', smul_eq_mul]
  ring

theorem fock_minorPol_zero : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B : HSp D) {a d : ℕ} (hA : A.rank = a) (hB : B.rank = d) (n : D.what₂.Tau → ℕ) (s : ℂ) (sc : ℝ), IsStdChar D ψ (-1) → IsInfFam θ → A.gram = 1 → B.gram = 1 → s ≠ 0 → (∀ τ, sc * ‖s‖ ^ 2 = 2 * ‖tauE D τ D.host.xi0‖) → ∃ c₁ : ℂ, c₁ ≠ 0 ∧ ∀ f : WO A B → ℂ, IsThetaFunO ψ A B f → (∀ τ, IsFockVacAt (heisO ψ A B) θ τ (cplxO 1 1) f) → ∀ T : Tup D a d n, pureTensorL (aPlusAll (heisO ψ A B) θ (fun _ => cplxO 1 1) (fun _ => 1) (fun _ => 1)) f (MvPolynomial.rename (fun k : Formalism.MainNotions.GL3Theta.Idx D a d => ((k.1, Fin.cast hB.symm k.2.1, Fin.cast hA.symm k.2.2) : FVar D B.rank A.rank)) (minorPol D T)) 0 = c₁ * Formalism.MainNotions.GL3Theta.applyAt0 D (minorPol D T) (GlobalTheory.AdForm.xiN θ A B hA hB s sc f) := by
  intro D ψ θ A B a d hA hB n s sc hψ hθ hgA hgB hs hsc
  subst hA hB
  obtain ⟨τ₀⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm (Classical.arbitrary _)⟩
  have hsc' : sc * ‖s‖ ^ 2 = 2 * Formalism.L2.Pj.xiR D := by
    rw [hsc τ₀, GlobalTheory.FockPos.norm_embedding_xi0_eq]
  have hx : 0 < Formalism.L2.Pj.xiR D := by
    unfold Formalism.L2.Pj.xiR
    exact norm_pos_iff.2 ((map_ne_zero _).2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D))
  set p : ℂ := (((Real.sqrt (2 * Real.pi * Formalism.L2.Pj.xiR D) : ℝ) : ℂ)⁻¹) * -s with hp
  have hp0 : p ≠ 0 := by
    refine mul_ne_zero (inv_ne_zero ?_) (neg_ne_zero.2 hs)
    exact_mod_cast (Real.sqrt_pos.2 (by positivity)).ne'
  have hon : ∀ {V : HSp D}, V.gram = 1 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (1 : GL (Fin V.rank) D.host.E).1 *
      V.gram * (1 : GL (Fin V.rank) D.host.E).1 = 1 := by
    intro V hV
    rw [hV]
    simp [Formalism.UG.cT]
  refine ⟨p ^ (A.rank * ∑ τ, n τ), pow_ne_zero _ hp0, fun f hf1 hf2 T => ?_⟩
  have hG := xiN_differentiable ψ θ A B s sc hψ hθ hgA hgB hs hsc' f hf1 hf2
  set G := xiN θ A B rfl rfl s sc f with hGdef
  have hΦ : Differentiable ℂ (fun z : Formalism.MainNotions.TaylorLogMetric.VC D A.rank B.rank => G ((-s) • z)) :=
    hG.comp (differentiable_id.const_smul (-s))
  have hid : (fun k : Formalism.MainNotions.GL3Theta.Idx D A.rank B.rank => ((k.1, Fin.cast (rfl : B.rank = B.rank).symm k.2.1,
      Fin.cast (rfl : A.rank = A.rank).symm k.2.2) : FVar D B.rank A.rank)) = id := by
    funext v; rfl
  rw [hid, MvPolynomial.rename_id, AlgHom.id_apply]
  refine apply_minorPol T ((LinearMap.proj (0 : WO A B)).comp
    (pureTensorO ψ θ A B (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) f)) p G fun k => ?_
  have h := GlobalTheory.FockPos.fock_monomial_zero_of_on ψ θ A B 1 1 hψ hθ (hon hgA) (hon hgB) f _ hΦ
    (fun w hw => eq_gauss_mul θ hθ A B s sc hs hsc' f w hw) k
  rw [frAt_one, frAt_one, GlobalTheory.FockPos.applyAt0_monomial', GlobalTheory.FockPos.taylor_comp_smul' D _ hG] at h
  rw [GlobalTheory.FockPos.applyAt0_monomial']
  refine h.trans ?_
  rw [hp, mul_pow]
  ring

end GlobalTheory.NormDictEx.Jets
end
end

