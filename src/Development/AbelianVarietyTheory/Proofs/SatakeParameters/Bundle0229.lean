import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0172
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0174
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0219
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0186
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0223
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardKerSubspacesAndHeckePolyOfConvolution
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0162
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0184
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0224

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalThetaCorrespondenceInertPlaceOfHowe
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3.CorrInert

variable {D : D7}

theorem exists_idem_of_conj_eq (P : Pl D.host.E) (hP : conjPl P = P) : ∃ e, IsPrimeIdem P e e := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  obtain ⟨e, f, h⟩ := GlobalTheory.IdemSupport.exists_isPrimeIdem hΦ P
  have hc : P = GlobalTheory.IdemSupport.cP P := by
    refine (GlobalTheory.IdemSupport.isConjPl_iff P P).1 fun c hc => ⟨GlobalTheory.IdemSupport.cO D c, ?_, rfl⟩
    have h1 : GlobalTheory.IdemSupport.cO D c ∈ (conjPl P).asIdeal := Ideal.mem_map_of_mem _ hc
    rwa [hP] at h1
  rcases h with ⟨h, -⟩ | h
  · exfalso
    have hd := GlobalTheory.IdemSupport.delta_of_isIdemAt hΦ h
    have hd' := GlobalTheory.IdemSupport.delta_conj hΦ hd
    rw [← hc] at hd'
    have h2 := GlobalTheory.IdemSupport.ev_mul (Φ := Φ) e (cA D e) P
    rw [h.1.2.1, GlobalTheory.IdemSupport.ev_zero, hd.2.1, hd'.2.1, one_mul] at h2
    exact zero_ne_one h2
  · obtain ⟨rfl, h⟩ := h
    exact ⟨f, Or.inr ⟨rfl, h⟩⟩

theorem suppF_of_mem_rep (V : HSp D) {P : Pl D.host.E} {e f : AE D} (he : IsPrimeIdem P e f) {d : List ℤ}
    {γ : GA D V} (h : γ ∈ rep V P d) : SuppF V f γ := by
  unfold rep at h
  split_ifs at h with hl
  · obtain ⟨e', f', -, -, -, he', -, -, -, -, -, -, -, hs, -⟩ := hl.choose_spec
    obtain ⟨-, rfl⟩ :=
      ((GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V).2.2.1 P e f he).2.2.2.1 e' f' he'
    exact hs γ h
  · exact absurd h (Finset.notMem_empty _)

theorem exists_pullback {V : HSp D} {P : Pl D.host.E} {e f : AE D} (he : IsPrimeIdem P e f)
    {W : Type} [AddCommGroup W] [Module ℂ W] (π : GA D V →* Module.End ℂ W) {H : Type} (ι : H → GA D V)
    (hι : ∀ g, SuppF V f g → ∃ h, ι h = g) (c : List ℤ →₀ ℂ) :
    ∃ b : H →₀ ℂ, ∀ u, (b.sum fun h z => z • π (ι h) u) = opOf π P c u := by
  have hm : opOf π P c ∈ Submodule.span ℂ (Set.range fun h => π (ι h)) := by
    refine Submodule.sum_mem _ fun d _ => Submodule.smul_mem _ _ (Submodule.sum_mem _ fun γ hγ => ?_)
    obtain ⟨h, rfl⟩ := hι γ (suppF_of_mem_rep V he hγ)
    exact Submodule.subset_span ⟨h, rfl⟩
  obtain ⟨b, hb⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hm
  refine ⟨b, fun u => ?_⟩
  rw [← hb]
  simp only [Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply]

theorem half {S T : HSp D} {P : Pl D.host.E} {e f : AE D} (he : IsPrimeIdem P e f)
    {W : Type} [AddCommGroup W] [Module ℂ W] (πS : GA D S →* Module.End ℂ W) (πT : GA D T →* Module.End ℂ W)
    (comm : ∀ g h u, πS g (πT h u) = πT h (πS g u)) (Vac : W → Prop)
    (fixS : ∀ u, Vac u → ∀ k ∈ hyp S P, πS k u = u) (fixT : ∀ u, Vac u → ∀ k ∈ hyp T P, πT k u = u)
    {GS GT : Type} (ιS : GS → GA D S) (ιT : GT → GA D T) (hS : ∀ g, SuppF S f (ιS g))
    (hT : ∀ g, SuppF T f g → ∃ h, ιT h = g)
    (howe : ∀ bT : GT →₀ ℂ, (∀ u, Vac u → ∀ k ∈ hyp T P,
        πT k (bT.sum fun h z => z • πT (ιT h) u) = bT.sum fun h z => z • πT (ιT h) u) →
      ∃ bS : GS →₀ ℂ, ∀ u, Vac u → (bT.sum fun h z => z • πT (ιT h) u) = bS.sum fun g z => z • πS (ιS g) u)
    (cT : List ℤ →₀ ℂ) : ∃ cS, ∀ u, Vac u → opOf πS P cS u = opOf πT P cT u := by
  classical
  obtain ⟨bT, hb⟩ := exists_pullback he πT ιT hT cT
  obtain ⟨bS, hbS⟩ := howe bT fun u hu k hk => by
    rw [hb]
    exact (GlobalTheory.T.spherical_label_operators_on_hyperspecial_fixed_vectors T P).2.1 cT W πT u (fixT u hu) k hk
  obtain ⟨cS, hc⟩ := GlobalTheory.T.exists_sphericalCombination_of_fixed_localTranslates S P e f he (Finsupp.mapDomain ιS bS) fun g hg => by
    obtain ⟨g', -, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hg)
    exact hS g'
  refine ⟨cS, fun u hu => ?_⟩
  have e1 : ((Finsupp.mapDomain ιS bS).sum fun g z => z • πS g u) = bT.sum fun h z => z • πT (ιT h) u := by
    rw [hbS u hu]
    exact Finsupp.sum_mapDomain_index (h := fun g (z : ℂ) => z • πS g u) (fun _ => zero_smul _ _)
      (fun _ _ _ => add_smul _ _ _)
  rw [← hc W πS u (fixS u hu) fun k hk => ?_, e1, hb]
  rw [e1, Finsupp.sum, map_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [map_smul, comm, fixS u hu k hk]

theorem coe_sum_smul {W : Type} [AddCommGroup W] [Module ℂ W] {M : Submodule ℂ W} {H : Type} (b : H →₀ ℂ) (v : H → M) :
    ((b.sum fun h z => z • v h : M) : W) = b.sum fun h z => z • (v h : W) := by
  simp only [Finsupp.sum, Submodule.coe_sum, Submodule.coe_smul]

theorem sphCorr_of_inert : HoweUnram → ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (P : Pl D.host.E), IsWeilDatumO ψ S T χS χT om → conjPl P = P → VacFix ψ om P → SphCorr ψ om P := by
  intro hH D ψ S T χS χT om P hW hP hV
  obtain ⟨e, he⟩ := exists_idem_of_conj_eq P hP
  obtain ⟨ϖ, σ, q, δ, JS, JT, ψ', M, ρ, ω, ιS, ιT, hL, rS, rT, kS, kT, hω, hM, hvac⟩ :=
    GlobalTheory.T.exists_unramifiedLocalPair_of_inertWeilDatum ψ S T χS χT om P hW hP hV e he
  haveI : CharZero (P.adicCompletion D.host.E) := algebraRat.charZero _
  obtain ⟨h1, h2⟩ := GlobalTheory.T.howeUnramified_all_vacua hH _ ϖ σ q δ _ _ JS JT ψ' M ρ ω hL
  have oneS : (1 : GA D S) ∈ hyp S P := by
    rw [← map_one ιS, kS]; exact one_mem _
  have oneT : (1 : GA D T) ∈ hyp T P := by
    rw [← map_one ιT, kT]; exact one_mem _
  have comm : ∀ g h u, (om.comp (MonoidHom.inl _ _)) g ((om.comp (MonoidHom.inr _ _)) h u) =
      (om.comp (MonoidHom.inr _ _)) h ((om.comp (MonoidHom.inl _ _)) g u) := by
    intro g h u
    change (om (g, 1) * om (1, h)) u = (om (1, h) * om (g, 1)) u
    rw [← map_mul, ← map_mul, Prod.mk_mul_mk, Prod.mk_mul_mk, one_mul, mul_one, one_mul, mul_one]
  have fixS : ∀ u, IsVacAt ψ S T P u → ∀ k ∈ hyp S P, (om.comp (MonoidHom.inl _ _)) k u = u :=
    fun u hu k hk => hV u hu k hk 1 oneT
  have fixT : ∀ u, IsVacAt ψ S T P u → ∀ k ∈ hyp T P, (om.comp (MonoidHom.inr _ _)) k u = u :=
    fun u hu k hk => hV u hu 1 oneS k hk
  have ωS : ∀ g (m : M), ((ω (g, 1) m : M) : WO S T → ℂ) = (om.comp (MonoidHom.inl _ _)) (ιS g) m := by
    intro g m
    rw [hω, map_one]; rfl
  have ωT : ∀ h (m : M), ((ω (1, h) m : M) : WO S T → ℂ) = (om.comp (MonoidHom.inr _ _)) (ιT h) m := by
    intro g m
    rw [hω, map_one]; rfl
  refine ⟨hV, fun cT => ?_, fun cS => ?_⟩
  · refine half he _ _ comm (IsVacAt ψ S T P) fixS fixT ιS ιT (fun g => (rS _).1 ⟨g, rfl⟩)
      (fun g hg => (rT g).2 hg) (fun bT hb => ?_) cT
    obtain ⟨bS, hbS⟩ := h1 bT fun s hs k hk => by
      apply Subtype.ext
      rw [ωT, coe_sum_smul]
      simp only [ωT]
      exact hb s ((hvac s).1 hs) _ ((kT k).2 hk)
    refine ⟨bS, fun u hu => ?_⟩
    have := congrArg Subtype.val (hbS ⟨u, hM u hu⟩ ((hvac _).2 hu))
    rw [coe_sum_smul, coe_sum_smul] at this
    simpa only [ωS, ωT] using this
  · suffices h : ∃ cT, ∀ u, IsVacAt ψ S T P u →
        opOf (om.comp (MonoidHom.inr _ _)) P cT u = opOf (om.comp (MonoidHom.inl _ _)) P cS u from
      h.imp fun cT h u hu => (h u hu).symm
    refine half he _ _ (fun g h u => (comm h g u).symm) (IsVacAt ψ S T P) fixT fixS ιT ιS (fun g => (rT _).1 ⟨g, rfl⟩)
      (fun g hg => (rS g).2 hg) (fun bS hb => ?_) cS
    obtain ⟨bT, hbT⟩ := h2 bS fun s hs k hk => by
      apply Subtype.ext
      rw [ωS, coe_sum_smul]
      simp only [ωS]
      exact hb s ((hvac s).1 hs) _ ((kS k).2 hk)
    refine ⟨bT, fun u hu => ?_⟩
    have := congrArg Subtype.val (hbT ⟨u, hM u hu⟩ ((hvac _).2 hu))
    rw [coe_sum_smul, coe_sum_smul] at this
    simpa only [ωS, ωT] using this

end GlobalTheory.Hk3.CorrInert

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaChainLastStepIntertwinesMatchedHeckeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_chain_last_step_intertwines_matched_hecke : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Core R F → SchurAll R → ∀ t P, Good R t P → VacFix R.ψ (R.ωX t) P → ∀ cS cX, Match R.ψ (R.ωX t) P cS (dualC cX) → ∀ y y' : (R.HX t).H, (R.HX t).e y' = hkF D.sp.X' P cX ((R.HX t).e y) → ∀ v, (R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y')).1 v = hk _ P cS ((R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y)).1 v) := by
  first | exact @GlobalTheory.Hk3.StepX.stepX_hk | exact GlobalTheory.Hk3.StepX.stepX_hk | (intros; apply GlobalTheory.Hk3.StepX.stepX_hk <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaIntertwinesMatchedOperatorsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_intertwines_matched_operators : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Core R F → SchurAll R → (∀ χ ∈ A.X, IsAbsIrrChar χ) → ∀ SF, IsSF R SF → ∀ i t P, Good R t P → ∀ cV cW, MatchW R i t P cV cW → ∀ hV, IsOpsV R i t hV → (∀ h, IsOpsW R i h → ∀ y, R.thG i t (hV P cV y) = h P cW (R.thG i t y)) ∧ ∀ c, ∀ w ∈ Wcc R SF i c, hV P cV (LinearMap.adjoint (R.thG i t) w) = evC (Wc D i) P (c P) cW • LinearMap.adjoint (R.thG i t) w := by
  first | exact @GlobalTheory.SysW.matched_operators_theta_intertwine | exact GlobalTheory.SysW.matched_operators_theta_intertwine | (intros; apply GlobalTheory.SysW.matched_operators_theta_intertwine <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftTransferHeckePolySplitPrime
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaPrimeHecke

open Formalism.L2.Host Formalism.L2.Col

theorem locK_eq_val {L : Type} [Field L] [NumberField L] (χ : HChar L) (Q : HeightOneSpectrum (𝓞 L))
    (hu : χ.UnrAt Q) (k : Lˣ) (hk : Q.valuation L (k : L) = WithZero.exp (-1 : ℤ)) :
    χ.locK Q k = χ.val Q := by
  have h1 : Valued.v ((atFin Q k : (Q.adicCompletion L)ˣ) : Q.adicCompletion L) = WithZero.exp (-1 : ℤ) := by
    rw [← hk]
    exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' Q (k : L)
  have h2 : Valued.v ((atFin Q (unif Q) : (Q.adicCompletion L)ˣ) : Q.adicCompletion L) = WithZero.exp (-1 : ℤ) :=
    unif_spec Q
  have h3 : IsUnitAt Q (atFin Q k * (atFin Q (unif Q))⁻¹) := by
    show Valued.v _ = _
    rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, h1, h2, mul_inv_cancel₀ WithZero.exp_ne_zero]
  have h4 := hu _ h3
  rw [map_mul, map_inv, mul_inv_eq_one] at h4
  exact h4

theorem exists_unif {L : Type} [Field L] [NumberField L] (Q : HeightOneSpectrum (𝓞 L)) :
    ∃ ϖ : 𝓞 L, ϖ ∈ Q.asIdeal ∧ ϖ ∉ Q.asIdeal ^ 2 ∧ Q.valuation L (ϖ : L) = WithZero.exp (-1 : ℤ) := by
  obtain ⟨ϖ, h⟩ := Q.intValuation_exists_uniformizer
  refine ⟨ϖ, ?_, ?_, ?_⟩
  · rw [← Q.intValuation_lt_one_iff_mem, h, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  · rw [← Q.intValuation_le_pow_iff_mem, h, WithZero.exp_le_exp]; norm_num
  · rw [← h]; exact Q.valuation_of_algebraMap ϖ

theorem poly_id (q r t : ℕ) (u v : ℂ) (a : ℕ → ℂ) :
    heckePolyOf (r + t) q (fun k => ∑ j ∈ Finset.range (r + 1),
      (if j ≤ k then (q : ℂ) ^ ((r - j) * (k - j)) * (gaussBin q t (k - j) : ℂ) * u⁻¹ ^ k * v ^ j else 0) * a j) =
    (heckePolyOf r q a).comp (C (u⁻¹ * v) * X) * blockPoly (u⁻¹ * (q : ℂ) ^ r) q t := by
  have key := GlobalTheory.KerRangeCount.card_ker_and_heckePolyOf_conv.2 ℂ q r t (fun j => if j ≤ r then a j else 0) u⁻¹ (u⁻¹ * v)
    (fun j hj => if_neg (by omega))
  have h1 : heckePolyOf r q (fun j => if j ≤ r then a j else 0) = heckePolyOf r q a := by
    unfold heckePolyOf
    refine Finset.sum_congr rfl fun j hj => ?_
    simp only [if_pos (show j ≤ r by simpa [Nat.lt_succ_iff] using hj)]
  rw [h1] at key
  rw [← key]
  congr 1
  funext k
  simp only [ite_mul, mul_ite, zero_mul, mul_zero]
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  refine Finset.sum_congr (by ext j; simp [Nat.lt_succ_iff, and_comm]) fun j hj => ?_
  have hjk : j ≤ k := by simpa [Nat.lt_succ_iff] using (Finset.mem_filter.1 hj).1
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hjk
  rw [Nat.add_sub_cancel_left, pow_add, mul_pow]
  ring

variable {D : D7}

theorem not_isConjPl {P : Pl D.host.E} (h : conjPl P ≠ P) : ¬ Formalism.IndefR.Lev.IsConjPl P P := by
  intro hc
  apply h
  refine HeightOneSpectrum.ext ((conjPl P).isMaximal.eq_of_le P.isPrime.ne_top ?_)
  refine Ideal.map_le_iff_le_comap.2 fun c hcP => ?_
  obtain ⟨c', hc', he⟩ := hc c hcP
  have : Formalism.DivisionValues.cO D.host.E c = c' := RingOfIntegers.ext he.symm
  rw [Ideal.mem_comap, this]
  exact hc'

theorem unrPl_mul_inv {P : Pl D.host.E} {a b : (AE D)ˣ →* Circle} (ha : UnrPl P a) (hb : UnrPl P b) : UnrPl P (a * b⁻¹) := by
  intro e f h x h1 h2 h3
  rw [MonoidHom.mul_apply, MonoidHom.inv_apply, ha e f h x h1 h2 h3, hb e f h x h1 h2 h3, inv_one, mul_one]

theorem consts (μ η ηa q s : ℂ) (hμ : μ ≠ 0) (hη : η ≠ 0) (hs : s ≠ 0) (hq : s * s = q) (he : ηa = η * s⁻¹) (r t : ℕ)
    (hr : Odd r) (ht : Odd t) :
    (μ * η⁻¹ * s ^ r)⁻¹ * (μ * s ^ (r + t)) = ηa * q ^ ((t + 1) / 2) ∧
      (μ * η⁻¹ * s ^ r)⁻¹ * q ^ r = μ⁻¹ * ηa * q ^ ((r + 1) / 2) := by
  obtain ⟨a, rfl⟩ := hr
  obtain ⟨b, rfl⟩ := ht
  rw [show (2 * a + 1 + 1) / 2 = a + 1 by omega, show (2 * b + 1 + 1) / 2 = b + 1 by omega, he, ← hq]
  constructor
  · field_simp
    ring
  · field_simp
    ring

set_option maxHeartbeats 1600000 in

theorem transfer_and_heckePoly : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Core R F → SchurAll R → ∀ i t (P : A.ok t), ∃ z : ℕ → ℕ → ℂ, (∀ k, k ≤ (Vc D i).rank → MatchW R i t (R.pl P) (Finsupp.single (splitLab (Vc D i).rank k) 1) (splitC (Wc D i).rank (z k))) ∧ ∀ a : ℕ → ℂ, Formalism.L2.Col.heckePolyOf (Vc D i).rank (A.q P) (fun k => ∑ j ∈ Finset.range ((Wc D i).rank + 1), z k j * a j) = (Formalism.L2.Col.heckePolyOf (Wc D i).rank (A.q P) a).comp (C (D.what₂.embLL (A.etaVal P : D.what₂.LL) * (A.q P : ℂ) ^ ((D.R.t + 1) / 2)) * X) * ((A.fam.L i t).blockProd P).map D.what₂.embLL := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hc hS i t P
  obtain ⟨hQ0, hG, -, hF⟩ := GlobalTheory.T.theta_lift_levels_good_primes_properties R F hc.lev
  obtain ⟨hgood, hsplit, hq⟩ := hF hc.fam t P P.2
  obtain ⟨hunη, hunμ⟩ := GlobalTheory.T.splittingCharacters_unramified_offLevels R F hc.lev t _ hgood
  obtain ⟨gramR, c0R, c0L, tie⟩ := hc.fam.tie
  obtain ⟨-, hAr, hAt⟩ := tie.ranks
  have hP0 : (P : Pl0) ∈ A.ok A.μ0 := by
    have h := (tie.ok t P).1 P.2
    rw [tie.ok, hQ0]
    simp only [Finset.coe_empty, Set.union_empty]
    exact ⟨h.1, fun h' => h.2.1 (Or.inl h'), fun Q hQ => h.2.2 Q (Or.inl hQ)⟩
  obtain ⟨e, he⟩ := GlobalTheory.ParahoricLift.exists_isIdemAt (not_isConjPl hsplit)
  obtain ⟨ϖ, hϖ1, hϖ2, hϖ3⟩ := exists_unif (R.pl P)
  have hϖ0 : (ϖ : D.host.E) ≠ 0 := fun h => by
    rw [h, map_zero] at hϖ3
    exact WithZero.exp_ne_zero hϖ3.symm
  have hpl : Formalism.L2.JoinChr.IsPlIdem D e (R.pl P) := by
    obtain ⟨⟨h1, h2, v, ε, h3, h4⟩, h5⟩ := he
    exact ⟨h1, ⟨v, ε, h3, Or.inl ⟨h2, h4⟩⟩, h5⟩
  let x : (AE D)ˣ := Formalism.L2.JoinChr.locU hpl.1 (Units.mk0 _ hϖ0)
  have hx : (x : AE D) = Formalism.L2.JoinChr.locE D e (Units.mk0 _ hϖ0 : D.host.Eˣ) := rfl
  have hx' : (x : AE D) = e * incA D (ϖ : D.host.E) + (1 - e) := by
    rw [hx, Formalism.L2.JoinChr.locE, Units.val_mk0]
    ring
  have hun1 := hunμ ((i : ℕ) + 1) (Nat.le_add_left _ _) i.2
  obtain ⟨hfix, hM⟩ := GlobalTheory.T.thetaVacuum_heckeIdentity_splitPlace R.ψ _ _ _ _ _ (R.pl P) (hc.thP.ωP i t) hsplit hun1 (unrPl_mul_inv hun1 hunη)
  have hW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have hV : (Vc D i).rank = (Wc D i).rank + D.R.t := by
    rw [hW]
    exact D.sp.V_rank _ (Nat.le_add_left _ _) i.2
  have hM' := (hM e ϖ x D.R.t he hϖ1 hϖ2 hx').2 hV
  refine ⟨_, fun k hk => GlobalTheory.T.thetaLiftGoodProjector_intertwines_matchedHecke R F hc hS i t _ hgood hfix _ _ (hM' k hk), fun a => ?_⟩

  have hu0 : (R.C.mu0 i).UnrAt (R.pl P) := by
    refine (R.C.isMu0 i).unr _ fun k hk => (hG t _ hgood).1 ?_
    rw [Nat.cast_mul]
    fin_cases k
    · exact Ideal.mul_mem_right _ _ hk
    · exact Ideal.mul_mem_left _ _ hk
  have huξ : (R.xiH t).UnrAt (R.pl P) := by
    by_contra h
    rcases (hc.lev.Q_ram t _).1 h with h | ⟨PP, h1, h2⟩
    · exact (hgood _ (Or.inr h)).1 rfl
    · exact (hgood _ (Or.inr h1)).2 h2
  have hη : ((R.eta x : Circle) : ℂ) = (R.C.eta.val (R.pl P) : ℂˣ) := by
    rw [hc.lev.eta.2 _ e hpl _ x hx, locK_eq_val _ _ (R.C.isEta.unr _) _ hϖ3]
  have hμ : ((R.toLevCh.mu t ((i : ℕ) + 1) x : Circle) : ℂ) = D.what₂.embLL (A.muVal i t P : D.what₂.LL) := by
    rw [hc.fam.muVal i t P P.2, HChar.val_mul, Units.val_mul, ← locK_eq_val _ _ hu0 (Units.mk0 _ hϖ0) hϖ3,
      ← locK_eq_val _ _ huξ (Units.mk0 _ hϖ0) hϖ3, ← (hc.lev.mu0 i).2 _ e hpl _ x hx, ← (hc.lev.xi t).2 _ e hpl _ x hx,
      ← Circle.coe_mul]
    rfl
  have hN : (0 : ℝ) < (Ideal.absNorm (R.pl P).asIdeal : ℕ) :=
    Nat.cast_pos.2 (Nat.pos_of_ne_zero fun h => (R.pl P).ne_bot (Ideal.absNorm_eq_zero_iff.1 h))
  have hs0 : ((Real.sqrt (Ideal.absNorm (R.pl P).asIdeal : ℕ) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 hN).ne'
  have hss : ((Real.sqrt (Ideal.absNorm (R.pl P).asIdeal : ℕ) : ℝ) : ℂ) *
      ((Real.sqrt (Ideal.absNorm (R.pl P).asIdeal : ℕ) : ℝ) : ℂ) = (Ideal.absNorm (R.pl P).asIdeal : ℕ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hN.le, Complex.ofReal_natCast]
  have hηa : D.what₂.embLL (A.etaVal P : D.what₂.LL) =
      ((R.eta x : Circle) : ℂ) * ((Real.sqrt (Ideal.absNorm (R.pl P).asIdeal : ℕ) : ℝ) : ℂ)⁻¹ := by
    rw [hc.fam.etaVal P hP0, hη, etaAlg, HChar.valTw, Complex.cpow_neg, Real.sqrt_eq_rpow, Complex.ofReal_cpow hN.le,
      Complex.ofReal_natCast]
  have hr : Odd (Wc D i).rank := by
    rw [hW]
    obtain ⟨a, ha⟩ := D.R.k_even
    obtain ⟨b, hb⟩ := D.R.m_even
    have := D.R.two_le_m
    exact ⟨a + b - 1, by unfold Ranks.r; omega⟩
  obtain ⟨c1, c2⟩ := consts _ _ _ _ _ (Circle.coe_ne_zero (R.toLevCh.mu t ((i : ℕ) + 1) x)) (Circle.coe_ne_zero (R.eta x))
    hs0 hss hηa _ _ hr D.R.t_odd
  have hB : ((A.fam.L i t).blockProd P).map D.what₂.embLL =
      blockPoly (D.what₂.embLL (firstValA (A.muVal i t) A.etaVal A.q A.r P)) (A.q P) A.t := by
    rw [← map_blockPoly]
    simp [BlockDat.blockProd, FamIn.fam, liftDat]
  rw [hB, firstValA, map_mul D.what₂.embLL, map_mul D.what₂.embLL, Units.val_inv_eq_inv_val, map_inv₀, map_pow D.what₂.embLL, map_natCast D.what₂.embLL, ← hμ,
    hAr, hAt, hq, ← hW,
    ← c1, ← c2]
  simp only [Lift.chrTh, MonoidHom.mul_apply, MonoidHom.inv_apply, Circle.coe_mul, Circle.coe_inv]
  rw [hV]
  exact poly_id _ _ _ _ _ a

end GlobalTheory.ThetaPrimeHecke
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightCocharacterEqOfGoodPlacesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_cocharacter_eq_of_good_places : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Core R F → ∀ SF, IsSF R SF → ∀ i (c c' : Pl D.host.E → List ℤ → ℂ), Wcc R SF i c ≠ ⊥ → Wcc R SF i c' ≠ ⊥ → (∀ P, Good R A.μ0 P → conjPl P ≠ P → ∀ k, k ≤ (Wc D i).rank → c P (splitLab (Wc D i).rank k) = c' P (splitLab (Wc D i).rank k)) → (∀ P d, Good R A.μ0 P → conjPl P = P → IsLab (Wc D i) P d → c P d = c' P d) → Wcc R SF i c = Wcc R SF i c' := by
  first | exact @GlobalTheory.Hk3.LabDet.part_eq_of_labels | exact GlobalTheory.Hk3.LabDet.part_eq_of_labels | (intros; apply GlobalTheory.Hk3.LabDet.part_eq_of_labels <;> assumption)
end

