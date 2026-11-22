import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0279
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0199
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0289
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemOfForallAnnihilatorAnnihilatorFieldModInteger
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0288
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0293
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocPrimeVNormalised
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

namespace GlobalTheory.HWL.NormVal

section General

variable {K : Type*} [Field K]

theorem exists_coe (v : AddValuation K (WithTop ℚ)) {x : K} (hx : x ≠ 0) :
    ∃ r : ℚ, v x = (r : WithTop ℚ) := by
  have h : v x + v x⁻¹ = 0 := by rw [← v.map_mul, mul_inv_cancel₀ hx, v.map_one]
  have h' : v x ≠ ⊤ := by
    intro e
    rw [e, top_add] at h
    exact WithTop.top_ne_zero h
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp h'
  exact ⟨r, hr.symm⟩

end General

open GlobalTheory.Per.Val

open TensorProduct in
private lemma addValuation_pow_mul_pow_div_pow {F : Type*} [Field F]
    (u : AddValuation F (WithTop ℚ)) {π : F} (hu : u π = 1) {x : F} {t : ℚ} (hx : u x = t)
    (b M N : ℕ) : u (x ^ b * π ^ M / π ^ N) = ((b * t + M - N : ℚ) : WithTop ℚ) := by
  rw [AddValuation.map_div, AddValuation.map_mul, AddValuation.map_pow, AddValuation.map_pow,
    AddValuation.map_pow, hx, hu]
  norm_cast
  simp [nsmul_eq_mul]

open TensorProduct in
private lemma le_of_nonneg_imp_nonneg {F : Type*} [Field F] (v w : AddValuation F (WithTop ℚ)) {π : F}
    (hv : v π = 1) (hw : w π = 1) (h : ∀ y, 0 ≤ v y → 0 ≤ w y) {x : F} {t s : ℚ}
    (hvx : v x = t) (hwx : w x = s) : t ≤ s := by
  have hMN : ((t.num.toNat : ℕ) : ℚ) - ((-t.num).toNat : ℕ) = t.num := by
    exact_mod_cast Int.toNat_sub_toNat_neg t.num
  have hbt : (t.den : ℚ) * t = t.num := by rw [mul_comm]; exact Rat.mul_den_eq_num t
  have hy := h (x ^ t.den * π ^ (-t.num).toNat / π ^ t.num.toNat) (by
    rw [addValuation_pow_mul_pow_div_pow v hv hvx]
    exact_mod_cast (by linarith : (0 : ℚ) ≤ t.den * t + ((-t.num).toNat : ℕ) - (t.num.toNat : ℕ)))
  rw [addValuation_pow_mul_pow_div_pow w hw hwx] at hy
  have hy' : (0 : ℚ) ≤ t.den * s + ((-t.num).toNat : ℕ) - (t.num.toNat : ℕ) := by exact_mod_cast hy
  have hd : (0 : ℚ) < t.den := by exact_mod_cast t.den_pos
  nlinarith

open TensorProduct in
private lemma addValuation_eq_of_nonneg_iff {F : Type*} [Field F] (v w : AddValuation F (WithTop ℚ))
    {π : F} (hv : v π = 1) (hw : w π = 1) (h : ∀ y, 0 ≤ v y ↔ 0 ≤ w y) (x : F) : v x = w x := by
  by_cases hx : x = 0
  · subst hx; simp
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp (mt (AddValuation.top_iff v).mp hx)
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp (mt (AddValuation.top_iff w).mp hx)
  rw [← ht, ← hs]
  have h1 := le_of_nonneg_imp_nonneg v w hv hw (fun y => (h y).mp) ht.symm hs.symm
  have h2 := le_of_nonneg_imp_nonneg w v hw hv (fun y => (h y).mpr) hs.symm ht.symm
  exact congrArg _ (le_antisymm h1 h2)

open TensorProduct in

theorem _root_.GlobalTheory.HWL.NormVal.locPrime_v_normalised : ∀ (l : ℕ) [Fact l.Prime] (P : _root_.Formalism.BasicNotions.LocPrime l) (LL : _root_.Formalism.BasicNotions.Loc.FinExt l), (∀ (x : ↥LL.1) (q : ℚ), P.v LL x = (q : WithTop ℚ) ↔ ‖(x : _root_.Formalism.BasicNotions.Loc.Om l)‖ = (l : ℝ) ^ (-(q : ℝ))) ∧ (∀ (x : ↥LL.1) (q : ℚ), (q : WithTop ℚ) ≤ P.v LL x ↔ ‖(x : _root_.Formalism.BasicNotions.Loc.Om l)‖ ≤ (l : ℝ) ^ (-(q : ℝ))) ∧ ∀ x : ↥LL.1, x ∈ _root_.Formalism.BasicNotions.Loc.OL LL ↔ ‖(x : _root_.Formalism.BasicNotions.Loc.Om l)‖ ≤ 1 := by
  intro l _ P LL
  set w : AddValuation (↥LL.1) (WithTop ℚ) :=
    (_root_.GlobalTheory.Per.Val.vOm l).comap (algebraMap (↥LL.1) (_root_.Formalism.BasicNotions.Loc.Om l)) with hwdef
  have hwx : ∀ x : ↥LL.1, w x = _root_.GlobalTheory.Per.Val.vf (x : _root_.Formalism.BasicNotions.Loc.Om l) := fun x => rfl
  have hw : w (l : ↥LL.1) = 1 := by
    rw [hwx]
    have : ((l : ↥LL.1) : _root_.Formalism.BasicNotions.Loc.Om l) = (l : _root_.Formalism.BasicNotions.Loc.Om l) := by simp
    rw [this]
    exact _root_.GlobalTheory.Per.Val.vf_l
  have hnn : ∀ y : ↥LL.1, 0 ≤ P.v LL y ↔ 0 ≤ w y := by
    intro y
    rw [_root_.Formalism.BasicNotions.LocPrime.v_O, _root_.GlobalTheory.Per.Val.mem_OL_iff, hwx]
    have := _root_.GlobalTheory.Per.Val.le_vf_iff (y : _root_.Formalism.BasicNotions.Loc.Om l) 0
    simp only [Rat.cast_zero, neg_zero, Real.rpow_zero, WithTop.coe_zero] at this
    exact this.symm
  have key : ∀ x : ↥LL.1, P.v LL x = _root_.GlobalTheory.Per.Val.vf (x : _root_.Formalism.BasicNotions.Loc.Om l) := fun x =>
    (addValuation_eq_of_nonneg_iff (P.v LL) w (P.v_l LL) hw hnn x).trans (hwx x)
  refine ⟨fun x q => ?_, fun x q => ?_, fun x => _root_.GlobalTheory.Per.Val.mem_OL_iff LL x⟩
  · rw [key]; exact _root_.GlobalTheory.Per.Val.vf_eq_iff _ q
  · rw [key]; exact _root_.GlobalTheory.Per.Val.le_vf_iff _ q

end GlobalTheory.HWL.NormVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalCohomologySevenElementaryFacts
section
noncomputable section

open Formalism.NG Formalism.RepresentationBoundsCohomology.LOC Formalism.RepresentationBoundsCohomology.JT NumberField IsDedekindDomain ReciprocityTheory.Gal ReciprocityTheory.ChartRestriction.T2

namespace GlobalTheory.LocElem

theorem padicInt_coeff {p : ℕ} [Fact p.Prime] : PadicCoeff p ℤ_[p] := by
  refine ⟨inferInstance, inferInstance, inferInstance, ?_, ?_, ?_⟩
  · rw [isAdic_iff]
    have key : ∀ n : ℕ, ((IsLocalRing.maximalIdeal ℤ_[p] ^ n : Ideal ℤ_[p]) : Set ℤ_[p]) =
        Metric.closedBall 0 ((p : ℝ) ^ (-(n : ℤ))) := by
      intro n
      ext x
      rw [PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow, SetLike.mem_coe,
        ← PadicInt.norm_le_pow_iff_mem_span_pow, mem_closedBall_zero_iff]
    refine ⟨fun n => ?_, fun s hs => ?_⟩
    · rw [key]
      exact IsUltrametricDist.isOpen_closedBall _ (zpow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _).ne'
    · obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hs
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ (show (1:ℝ) < p by exact_mod_cast (Fact.out : p.Prime).one_lt))
      refine ⟨n, ?_⟩
      rw [key]
      intro x hx
      apply hball
      rw [mem_closedBall_zero_iff] at hx
      rw [mem_ball_zero_iff]
      refine lt_of_le_of_lt hx ?_
      rw [zpow_neg, zpow_natCast, ← inv_pow]
      exact hn
  · rw [PadicInt.maximalIdeal_eq_span_p]; exact Ideal.subset_span rfl
  · exact_mod_cast (Fact.out : p.Prime).ne_zero

theorem mulSub_open {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
    {M : Type} [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    (hM : IsFGTop O M) (hO : PadicCoeff p O) {a : O} (ha : a ≠ 0) :
    IsOpen ((mulSub a M : Submodule O M) : Set M) := by
  have := hO.compact
  have := hO.ring
  have := hM.t2
  have := hM.csmul
  obtain ⟨s, hs⟩ := hM.fg.fg_top

  let f : (s → O) →ₗ[O] M := Fintype.linearCombination O (fun i : s => (i : M))
  have hfc : Continuous f := by
    show Continuous fun v : s → O => ∑ i, v i • (i : M)
    exact continuous_finset_sum _ fun i _ => (continuous_apply i).smul continuous_const
  have hfs : Function.Surjective f := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, Subtype.range_coe_subtype,
      Finset.setOf_mem, hs]
  have hq : Topology.IsQuotientMap f :=
    (hfc.isClosedMap).isQuotientMap hfc hfs

  have haO : IsOpen ((Ideal.span {a} : Ideal O) : Set O) := by
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
    have e : (Ideal.span {(u : O) * ϖ ^ n} : Ideal O) = IsLocalRing.maximalIdeal O ^ n := by
      rw [Ideal.span_singleton_mul_left_unit u.isUnit, ← Ideal.span_singleton_pow,
        hϖ.maximalIdeal_eq]
    rw [e]
    exact (isAdic_iff.1 hO.adic).1 n
  have hopen : IsOpen ((((mulSub a M).comap f).toAddSubgroup : AddSubgroup (s → O)) : Set (s → O)) := by
    refine AddSubgroup.isOpen_mono (H₁ := (Submodule.pi Set.univ fun _ => (Ideal.span {a} : Ideal O)).toAddSubgroup) ?_ ?_
    · intro v hv
      have : ∀ i, ∃ w : O, a * w = v i := fun i => by
        obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 (hv i (Set.mem_univ i))
        exact ⟨w, by rw [mul_comm]; exact hw⟩
      choose w hw using this
      refine ⟨f w, ?_⟩
      show a • f w = f v
      rw [← map_smul]
      congr 1
      funext i
      exact hw i
    · show IsOpen (Set.univ.pi fun _ => ((Ideal.span {a} : Ideal O) : Set O))
      exact isOpen_set_pi Set.finite_univ fun _ _ => haO
  rw [← hq.isOpen_preimage]
  exact hopen

theorem contAction_quotient {O G V : Type} [CommRing O] [Group G] [TopologicalSpace G] [AddCommGroup V] [Module O V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] {ρ : Representation O G V} (h : ReciprocityTheory.Gal.ContAction ρ)
    (T : Submodule O V) (hT : StableUnder ρ T) : ReciprocityTheory.Gal.ContAction (ρ.quotient T hT) := by
  have hq : IsOpenQuotientMap (Prod.map (id : G → G) T.mkQ) :=
    IsOpenQuotientMap.id.prodMap (Submodule.isOpenQuotientMap_mkQ T)
  unfold ReciprocityTheory.Gal.ContAction
  rw [hq.isQuotientMap.continuous_iff]
  exact continuous_quot_mk.comp h

theorem cup_eq_zero_of_coboundary {O : Type} [CommRing O] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    {M T₂ P : Type} [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousConstSMul O M] [AddCommGroup T₂] [Module O T₂] [TopologicalSpace T₂]
    [IsTopologicalAddGroup T₂] [ContinuousConstSMul O T₂] [AddCommGroup P] [Module O P]
    [TopologicalSpace P] [IsTopologicalAddGroup P] [ContinuousConstSMul O P]
    (ρM : Representation O Γ M) (ρ₂ : Representation O Γ T₂) (ρP : Representation O Γ P)
    (b : M →ₗ[O] T₂ →ₗ[O] P) (hb : Continuous fun q : M × T₂ => b q.1 q.2)
    (hbe : ∀ g x y, b (ρM g x) (ρ₂ g y) = ρP g (b x y)) (h₂ : ReciprocityTheory.Gal.ContAction ρ₂)
    (x : Z1 ρM) (t : Z1 ρ₂) (c : Γ → P) (hc : Continuous c)
    (hcz : ∀ g h, b (ρM g (x.1 h)) (t.1 g) = ρP g (c h) - c (g * h) + c g) :
    cupProductH1H1 ρM ρ₂ ρP b hb hbe h₂ (Submodule.Quotient.mk x) (Submodule.Quotient.mk t) = 0 := by
  show (Submodule.Quotient.mk (cupCocycleZ1Z1 ρM ρ₂ ρP b hb hbe h₂ x t) : H2 ρP) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  refine (separated_dvr_second_cohomology_mem _ _).2 ⟨fun g => -(b (x.1 g) (t.1 g)) - c g, ((hb.comp (x.2.1.prodMk t.2.1)).neg).sub hc, ?_⟩
  funext q
  obtain ⟨g, h⟩ := q
  have e := hcz g h
  simp only [d1_apply, Submodule.coe_subtype, cupCocycleZ1Z1_apply, map_sub, map_neg, ← hbe, x.2.2 g h, t.2.2 g h, map_add,
    LinearMap.add_apply]
  have e' : ρP g (c h) = b (ρM g (x.1 h)) (t.1 g) + c (g * h) - c g := by rw [e]; abel
  rw [e']
  abel

theorem pr_eq_zero_of_coboundary {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    {VT VT' : Type}
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT]
    [ContinuousSMul O VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT']
    [ContinuousSMul O VT'] {G : Type} [Group G] [TopologicalSpace G] (D : LatData O G VT VT')
    (x : Z1 D.ρA) (t : Z1 D.ρTl') (c : G → KO O) (hc : Continuous c)
    (hcz : ∀ g k, pairKO D.bT D.T (D.ρA g (x.1 k)) (t.1 g) = ((D.ε g : Oˣ) : O) • c k - c (g * k) + c g) :
    D.pr (Submodule.Quotient.mk x) (Submodule.Quotient.mk t) = 0 := by
  show D.inv (cupProductH1H1 D.ρA D.ρTl' (twist D.ε (KO O)) (pairKO D.bT D.T) (pairKO_cont D.bT D.contbT D.T)
    D.pairKO_equiv (sub_contAction D.contT' _ D.stT') (Submodule.Quotient.mk x) (Submodule.Quotient.mk t)) = 0
  have h0 := cup_eq_zero_of_coboundary D.ρA D.ρTl' (twist D.ε (KO O)) (pairKO D.bT D.T) (pairKO_cont D.bT D.contbT D.T)
    D.pairKO_equiv (sub_contAction D.contT' _ D.stT') x t c hc (fun g k => hcz g k)
  exact (congrArg D.inv h0).trans (map_zero _)

theorem quotShape_of_equiv {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {X : Type} [AddCommGroup X]
    [Module O X] (Hc F Hc' F' : Submodule O X) (d : ℕ)
    (e : (Hc ⧸ F.comap Hc.subtype) ≃ₗ[O] (Hc' ⧸ F'.comap Hc'.subtype)) (h : QuotShape Hc F d) :
    QuotShape Hc' F' d := by
  obtain ⟨Cy, i1, i2, ι, π, hι, hex, c0, hc0⟩ := h
  refine ⟨Cy, i1, i2, e.toLinearMap ∘ₗ ι, π ∘ₗ e.symm.toLinearMap, e.injective.comp hι, ?_, c0, hc0⟩
  intro y
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, Set.mem_range]
  rw [hex (e.symm y)]
  constructor
  · rintro ⟨z, hz⟩; exact ⟨z, by rw [hz, LinearEquiv.apply_symm_apply]⟩
  · rintro ⟨z, hz⟩; exact ⟨z, by rw [← hz, LinearEquiv.symm_apply_apply]⟩

theorem mem_integers_iff_norm_le_one {l : ℕ} [Fact l.Prime] (LL : Formalism.BasicNotions.Loc.FinExt l) (x : ↥LL.1) :
    x ∈ Formalism.BasicNotions.Loc.OL LL ↔ ‖(x : Formalism.BasicNotions.Loc.Om l)‖ ≤ 1 :=
  GlobalTheory.EmbInj.mem_OL_iff LL x

theorem isOpen_integers {l : ℕ} [Fact l.Prime] (LL : Formalism.BasicNotions.Loc.FinExt l) :
    IsOpen (Set.range (algebraMap ↥(Formalism.BasicNotions.Loc.OL LL) ↥LL.1)) :=
  (GlobalTheory.LitGood.litGoodO l LL).2.2.2.2

theorem elem : ReciprocityTheory.ChartRestriction.T2.Elem where
  padicInt := padicInt_coeff
  mulSub := @fun _ _ _ _ _ _ _ _ _ _ _ hM hO _ ha => mulSub_open hM hO ha
  contQuot := fun h T hT => contAction_quotient h T hT
  swapCob := fun D x t c hc hcz => pr_eq_zero_of_coboundary D x t c hc hcz
  shapeEquiv := fun Hc F Hc' F' d e h => quotShape_of_equiv Hc F Hc' F' d e h
  memOL := fun LL x => mem_integers_iff_norm_le_one LL x
  openOL := fun LL => isOpen_integers LL

end GlobalTheory.LocElem
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalConditionAboveLCoeffMapFunctorial
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published

namespace GlobalTheory.SelFun

section General

variable {R : Type} [CommRing R] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
  {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
  {M' : Type} [AddCommGroup M'] [Module R M'] [TopologicalSpace M'] [IsTopologicalAddGroup M'] [ContinuousConstSMul R M']
  (rho : Representation R Γ M) (rho' : Representation R Γ M') (u : M →ₗ[R] M') (hu : Continuous u)
  (he : ∀ g m, u (rho g m) = rho' g (u m))

theorem selMaps_res_map {H : Type} [Group H] [TopologicalSpace H] (phi : H →* Γ) (hphi : Continuous phi) (x : H1 rho) :
    resH1 rho' phi hphi (mapH1 rho rho' u hu he x) =
      mapH1 (rho.comp phi) (rho'.comp phi) u hu (fun g m => he (phi g) m) (resH1 rho phi hphi x) := by
  induction x using Submodule.Quotient.induction_on with
  | H z => rfl

theorem selMaps_map_ur (J : Subgroup Γ) (x : H1 rho) (hx : x ∈ H1ur rho J) :
    mapH1 rho rho' u hu he x ∈ H1ur rho' J := by
  have h0 : resH1 rho J.subtype continuous_subtype_val x = 0 := hx
  exact (selMaps_res_map rho rho' u hu he J.subtype continuous_subtype_val x).trans
    ((congrArg _ h0).trans (map_zero _))

end General

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (bkP : BKPh X)
  (i : X.Tw) {r : ℕ} (ρ : GE N →* GL (Fin r) (X.O0 i)) {Λ : Type} [CommRing Λ] [Algebra (X.O0 i) Λ] (κ : GE N →* Λˣ)
  {B B' : Type} [AddCommGroup B] [Module Λ B] [TopologicalSpace B] [DiscreteTopology B]
  [AddCommGroup B'] [Module Λ B'] [TopologicalSpace B'] [DiscreteTopology B']

theorem localConditionAboveL_coeffMap_functorial (f : B →ₗ[Λ] B') (v : PlE D.host) (x : H1 ((repOn ρ κ B).comp (DecV N v).subtype))
    (hx : x ∈ bkOn bkP i ρ κ B v) : h1MapSubgroup ρ κ (DecV N v) f x ∈ bkOn bkP i ρ κ B' v := by
  unfold bkOn at hx ⊢
  split_ifs at hx ⊢ with hv
  · induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z, c, y, b, hc, hy, hz, rfl⟩ := hx
      refine Submodule.subset_span ⟨cocycles1MapOfEquivariant _ _ (f.compLeft (Fin r)) continuous_of_discreteTopology
        (fun g m => repOn_map ρ κ f g.1 m) z, c, y, f b, hc, hy, fun g a => ?_, rfl⟩
      change f ((z : ↥(DecV N v) → Fin r → B) g a) = _
      rw [hz, map_smul]
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx
  · rw [Submodule.mem_bot] at hx ⊢
    rw [hx, map_zero]

theorem selmerClass_coeffMap_mem_selmer (f : B →ₗ[Λ] B') (Q : Finset (PlE D.host)) (x : H1 (repOn ρ κ B))
    (hx : x ∈ selOn bkP i ρ κ B Q) : h1Map ρ κ f x ∈ selOn bkP i ρ κ B' Q := by
  refine (mem_Sel _ _ _ _ _).2 fun v => ?_
  have hv := (mem_Sel _ _ _ _ _).1 hx v
  refine (selMaps_res_map (repOn ρ κ B) (repOn ρ κ B') (f.compLeft (Fin r)) continuous_of_discreteTopology
    (repOn_map ρ κ f) (Dec (F := D.host.E) (N.plOm.1 v)).subtype continuous_subtype_val x) ▸ ?_
  unfold Formalism.GaloisCohomology.bkCond at hv ⊢
  split_ifs at hv ⊢ with h1 h2
  · exact localConditionAboveL_coeffMap_functorial bkP i ρ κ f v _ hv
  · exact Submodule.mem_top
  · exact selMaps_map_ur _ _ _ _ _ _ _ hv

theorem selMaps (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X)
    (i : X.Tw) (s : X.Sig i) (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [Algebra (X.O0 i) Λ] (κ : GE N →* Λˣ)
    (Q : Finset (PlE D.host)) : SelMaps bkP i s κ Q := by
  intro B B' _ _ _ _ _ _ _ _ f
  rintro _ ⟨x, hx, rfl⟩
  exact selmerClass_coeffMap_mem_selmer bkP i _ κ f Q x hx

end GlobalTheory.SelFun

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalDegreeSum
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published

namespace GlobalTheory.Proof.LocalDegreeSum

theorem sum_locDeg : ∀ (F : Type) [Field F] [NumberField F] (l : ℕ) [Fact l.Prime] [Fintype {v : HeightOneSpectrum (𝓞 F) // ((l : ℕ) : 𝓞 F) ∈ v.asIdeal}], ∑ v : {v : HeightOneSpectrum (𝓞 F) // ((l : ℕ) : 𝓞 F) ∈ v.asIdeal}, ReciprocityTheory.Gal.locDeg v.1 = Module.finrank ℚ F := by
  intro F _ _ l hl _
  classical

  set p : Ideal ℤ := Ideal.span {(l : ℤ)} with hp
  have hpmax : p.IsMaximal := Int.ideal_span_isMaximal_of_prime l
  have : p.IsPrime := hpmax.isPrime
  have hp0 : p ≠ 0 := by
    rw [hp, Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hl.out.ne_zero

  have key : ∀ v : HeightOneSpectrum (𝓞 F),
      ((l : ℕ) : 𝓞 F) ∈ v.asIdeal ↔ v.asIdeal ∣ Ideal.map (algebraMap ℤ (𝓞 F)) p := by
    intro v
    rw [Ideal.dvd_iff_le, hp, Ideal.map_span, Set.image_singleton,
      Ideal.span_singleton_le_iff_mem]
    simp

  let e := (Equiv.subtypeEquivRight key).trans (HeightOneSpectrum.equivPrimesOver (𝓞 F) hp0)
  rw [← NumberField.RingOfIntegers.rank, ← Ideal.sum_ramification_inertia_eq_finrank p (𝓞 F)]
  exact Fintype.sum_equiv e _ _ (fun v => by rfl)

end GlobalTheory.Proof.LocalDegreeSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemOfForallAnnihilatorAnnihilatorFieldModIntegerStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_of_forall_annihilator_annihilator_fieldModIntegers : ∀ (l : ℕ) [Fact l.Prime] (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (M N : Type) [AddCommGroup M] [Module O M] [AddCommGroup N] [Module O N] [Module.Finite O M] (β : M →ₗ[O] N →ₗ[O] (LL ⧸ LinearMap.range (Algebra.linearMap O LL))) (S : Submodule O N), (∀ c, (∀ d, β d c = 0) → c ∈ S) → ∀ c, (∀ d, (∀ s ∈ S, β d s = 0) → β d c = 0) → c ∈ S := by
  first | exact @GlobalTheory.mem_of_forall_annihilator_annihilator | exact GlobalTheory.mem_of_forall_annihilator_annihilator | (intros; apply GlobalTheory.mem_of_forall_annihilator_annihilator <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemPiPowEllOfNearPiStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_pi_pow_ell_of_nearPi : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (W : Wach P K LL) (E : EtSit P AI K s LL h W) (m : ℕ) (a : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))), NearPi AI LL s m (inclR LL (E.tie.io a)) → ∃ a1 a2 : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K)), a = letπ ^ m * a1 + (l : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) * a2 := by
  first | exact @GlobalTheory.Decompl.mem_pow_pi_of_nearPi | exact GlobalTheory.Decompl.mem_pow_pi_of_nearPi | (intros; apply GlobalTheory.Decompl.mem_pow_pi_of_nearPi <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NBasisLoc
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL

namespace GlobalTheory.NL

set_option maxHeartbeats 1600000 in

theorem N_basis_loc {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) (K : FinExt l) (s : ℕ)
    (LL : FinExt l) (h : Good K s LL) (T : Lt K LL) (hT : IsCrys (P.PD K) T.ρ) :
    Nonempty (Module.Basis (Fin (Module.finrank ↥(OL LL) ↥T.L.T)) (AA K LL) ↥((H.W K s LL h).N T)) := by
  obtain ⟨_, -, hl⟩ := GlobalTheory.FinExtIntegers.dvr_complete LL
  haveI := (P.PD K).finK₀
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  have hproj := H.W_proj K s LL h T
  generalize H.W K s LL h = W at hproj ⊢
  obtain ⟨hfree, hrk⟩ := W.DD_free T
  rw [← hrk]
  haveI : Module.Finite (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥(W.N T) :=
    Module.Finite.iff_fg.mpr (W.N_fg T)
  have hl0 : ((l : ℕ) : ↥(OL LL)) ≠ 0 := by
    intro h0
    have := congrArg (fun x : ↥(OL LL) => (x : ↥LL.1)) h0
    simp [(Fact.out : l.Prime).ne_zero] at this
  refine GlobalTheory.WachFree.basis_of_regular (ι := ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (O := ↥(OL LL))
    (N := ↥(W.N T)) (E := W.EE) (D := W.DD T) W.EE_inj (W.N T).subtype (W.N_base T hT)
    ((l : ℕ) : ↥(OL LL)) hl0 hl ?_ ?_
  · intro x y hxy
    have h1 : (letπ : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) • (x : W.DD T) =
        (letπ : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) • (y : W.DD T) :=
      congrArg Subtype.val hxy
    rw [← algebraMap_smul W.EE, ← algebraMap_smul W.EE letπ (y : W.DD T)] at h1
    exact Subtype.ext (W.EE_π.smul_left_cancel.mp h1)
  · intro x y hxy
    have e1 : zlA LL (Module.finrank ℚ_[l] ↥(K0 K)) (PowerSeries.C ((l : ℕ) : ℤ_[l])) =
        fun _ => PowerSeries.C ((l : ℕ) : ↥(OL LL)) := by
      funext i
      simp
    have e2 : zlA LL (Module.finrank ℚ_[l] ↥(K0 K)) PowerSeries.X = fun _ => PowerSeries.X := by
      funext i
      simp [zlA]
    exact GlobalTheory.HWL.mem_smul_of_projective_comp _ hproj ((l : ℕ) : ℤ_[l])
      (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero) e1 e2 x y hxy

theorem N_basis : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let _E := ((F l).E K s LL h).tie; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → Nonempty (Module.Basis (Fin (Module.finrank ↥(OL LL) ↥T.L.T)) (AA K LL) ↥(W.N T)) :=
  fun _ HW _ l _ K s LL h T hT => N_basis_loc (HW l) K s LL h T hT

end GlobalTheory.NL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NearPiSepCompleteStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nearPi_sep_complete_alt : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (LL : FinExt l) (s : ℕ), (∀ x : RW LL, (∀ m, NearPi AI LL s m x) → ∃ r, x = (l : RW LL) * r) ∧ ∀ (k : ℕ) (f : ℕ → RW LL), (∀ i, NearPi AI LL s (i + k) (f i)) → ∃ x, ∀ m, NearPi AI LL s (m + k) (x - ∑ i ∈ Finset.range m, f i) := by
  first | exact @GlobalTheory.Decompl.nearPi_sep_complete | exact GlobalTheory.Decompl.nearPi_sep_complete | (intros; apply GlobalTheory.Decompl.nearPi_sep_complete <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyClosureHomTiltFieldStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_closure_hom_tilt_field : ∀ (l : ℕ) [Fact l.Prime], Nonempty (AlgebraicClosure (ZMod l) →+* Per.Fl l) := by
  first | exact @GlobalTheory.Per.nonempty_algClosure_zmod_to_tilt | exact GlobalTheory.Per.nonempty_algClosure_zmod_to_tilt | (intros; apply GlobalTheory.Per.nonempty_algClosure_zmod_to_tilt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormGeomSumGaloisLeStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_sum_pow_apply_le_and_norm_pow_prime_sub_le : ∀ (l : ℕ) [Fact l.Prime] (σ : GQ l) (S : AddSubgroup (Om l)) (s : ℝ), 0 ≤ s → s ≤ 1 → (∀ x ∈ S, σ x ∈ S) → (∀ x ∈ S, ‖σ x - x‖ ≤ s * ‖x‖) → ∀ x ∈ S, ‖∑ i ∈ Finset.range l, (σ ^ i) x‖ ≤ max (s ^ (l - 1)) ‖((l : ℕ) : Om l)‖ * ‖x‖ ∧ ‖(σ ^ l) x - x‖ ≤ max (s ^ (l - 1)) ‖((l : ℕ) : Om l)‖ * s * ‖x‖ := by
  first | exact @GlobalTheory.MemLoc.norm_geom_sum_galois_le | exact GlobalTheory.MemLoc.norm_geom_sum_galois_le | (intros; apply GlobalTheory.MemLoc.norm_geom_sum_galois_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicIntAddFilClosedInDeRhamPeriodRingStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padicInt_add_fil_closed_in_deRhamPeriodRing : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (M : ℕ), 1 ≤ M → ∀ v : P.R.BdR, (∀ n : ℕ, ∃ z : ℤ_[l], qB P (z : ℚ_[l]) - v ∈ Lat AI M n) → NearZ P M v := by
  first | exact @GlobalTheory.ExpImage.nearZ_of_forall_Lat | exact GlobalTheory.ExpImage.nearZ_of_forall_Lat | (intros; apply GlobalTheory.ExpImage.nearZ_of_forall_Lat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicIntExistsPowSubNormLeOfExactLevelStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padicInt_exists_pow_sub_norm_le_of_exact_level' : ∀ (l : ℕ) [Fact l.Prime] (u v : ℤ_[l]) (m : ℕ), 1 ≤ m → ‖u - 1‖ = ‖((l : ℕ) : ℤ_[l])‖ ^ m → ‖v - 1‖ ≤ ‖((l : ℕ) : ℤ_[l])‖ ^ m → ∃ i : ℕ, ‖u ^ i - v‖ ≤ ‖((l : ℕ) : ℤ_[l])‖ ^ (m + 1) := by
  first | exact @GlobalTheory.padicInt_exists_pow_sub_norm_le_of_exact_level | exact GlobalTheory.padicInt_exists_pow_sub_norm_le_of_exact_level | (intros; apply GlobalTheory.padicInt_exists_pow_sub_norm_le_of_exact_level <;> assumption)
end

