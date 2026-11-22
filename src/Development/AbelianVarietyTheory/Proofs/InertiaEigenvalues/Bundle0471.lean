import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0344
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0438
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0442
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0295
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0446
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0232
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0230
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0443
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitCoeffWittTiltRelation
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.ResidueUnitCoeff

theorem neZero_of_piSys {l : ℕ} [Fact l.Prime] {e : ℕ} (ϖ : PiSys l e) : NeZero e := by
  refine ⟨fun he => ?_⟩
  subst he
  have h := ϖ.seq_zero
  rw [pow_zero, eq_neg_iff_add_eq_zero, add_comm] at h
  exact Nat.cast_add_one_ne_zero l h

theorem exists_bound {l : ℕ} [Fact l.Prime] {O K : Type} [CommRing O] [Algebra ℤ_[l] O]
    [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ c : O, ‖algebraMap O K c‖ < 1 → ‖algebraMap O K c‖ ≤ ρ := by
  have : IsNoetherianRing O := isNoetherian_of_tower ℤ_[l] inferInstance
  let m : Ideal O :=
    { carrier := {c | ‖algebraMap O K c‖ < 1}
      add_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq, map_add] at *
        exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hx hy)
      zero_mem' := by simp
      smul_mem' := fun r x hx => by
        simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul, norm_mul] at *
        exact (mul_le_of_le_one_left (norm_nonneg _) (norm_algebraMap_le r)).trans_lt hx }
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian m : m.FG)
  refine ⟨(s.sup fun g => ‖algebraMap O K g‖₊ : NNReal), NNReal.coe_nonneg _, ?_, fun c hc => ?_⟩
  · have : s.sup (fun g => ‖algebraMap O K g‖₊) < 1 := by
      refine (Finset.sup_lt_iff zero_lt_one).2 fun g hg => ?_
      have : g ∈ m := hs ▸ Ideal.subset_span hg
      exact (by exact_mod_cast this : ‖algebraMap O K g‖ < 1)
    exact_mod_cast this
  · have key : ∀ c ∈ Submodule.span O (s : Set O),
        ‖algebraMap O K c‖ ≤ (s.sup fun g => ‖algebraMap O K g‖₊ : NNReal) := by
      intro c hc'
      induction hc' using Submodule.span_induction with
      | mem x hx =>
        exact_mod_cast Finset.le_sup (f := fun g => ‖algebraMap O K g‖₊) hx
      | zero => simp
      | add x y _ _ hx hy =>
        rw [map_add]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
      | smul r x _ hx =>
        rw [smul_eq_mul, map_mul, norm_mul]
        exact (mul_le_of_le_one_left (norm_nonneg _) (norm_algebraMap_le r)).trans hx
    exact key c (by rw [hs]; exact hc)

end GlobalTheory.ResidueUnitCoeff

namespace GlobalTheory.ResidueUnitCoeff

theorem norm_coeff_pow_le {K : Type} [NormedField K] [IsUltrametricDist K] {f : K⟦X⟧} {ρ : ℝ}
    (h0 : 0 ≤ ρ) (hf : ∀ n, ‖coeff n f‖ ≤ ρ) (m n : ℕ) : ‖coeff n (f ^ m)‖ ≤ ρ ^ m := by
  induction m generalizing n with
  | zero => rw [pow_zero, pow_zero, coeff_one]; split_ifs <;> simp
  | succ m ih =>
    rw [pow_succ, pow_succ]
    simpa using norm_coeff_mul_le (w := fun _ => 1) (fun _ => zero_le_one) (fun _ _ => by simp)
      (pow_nonneg h0 m) h0 (f := f ^ m) (g := f) (by simpa using ih) (by simpa using hf) n

theorem exists_norm_coeff_eq_one : ∀ {l : ℕ} [Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) {S : Type} [Fintype S] (y : S → ZMod a → A O K) (c : S → OW l O) (h : ∑ s, c s * inclO l O (ϖ.iTot t K (y s)) = 1) (τ : ZMod a), ∃ s k, ‖coeff k (y s τ : K⟦X⟧)‖ = 1 := by
  intro l _ a _ e O K _ _ _ _ _ _ _ _ _ t ϖ S _ y c h τ
  have := neZero_of_piSys ϖ
  by_contra hne
  push_neg at hne
  obtain ⟨ρ, hρ0, hρ1, hρ⟩ := exists_bound (l := l) (O := O) (K := K)
  have hco : ∀ s k, ‖coeff k (y s τ : K⟦X⟧)‖ ≤ ρ := fun s k => by
    obtain ⟨o, ho⟩ := (IsUnitBall.mem_range_iff (O := O) _).2 (mem_A.1 (y s τ).2 k)
    have h1 : ‖coeff k (y s τ : K⟦X⟧)‖ < 1 := lt_of_le_of_ne (mem_A.1 (y s τ).2 k) (hne s k)
    rw [← ho] at h1 ⊢
    exact hρ o h1
  have hl0 : (l : K) ≠ 0 := by
    rw [← map_natCast (algebraMap ℚ_[l] K)]
    exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have hlpos : 0 < ‖(l : K)‖ := norm_pos_iff.2 hl0
  obtain ⟨N0, hN0⟩ := exists_pow_lt_of_lt_one hlpos hρ1
  set N := N0 + 1 with hN
  have hρN : ρ ^ N ≤ ‖(l : K)‖ :=
    (pow_le_pow_of_le_one hρ0 hρ1.le (Nat.le_succ N0)).trans hN0.le
  have hzmem : ∀ s, C (l : K)⁻¹ * (y s τ : K⟦X⟧) ^ N ∈ A O K := fun s n => by
    rw [coeff_C_mul, norm_mul, norm_inv, inv_mul_le_iff₀ hlpos, mul_one]
    exact (norm_coeff_pow_le hρ0 (hco s) N n).trans hρN
  let z : S → A O K := fun s => ⟨_, hzmem s⟩
  have hz : ∀ s, y s τ ^ N = (l : A O K) * z s := fun s => Subtype.ext (by
    simp only [SubmonoidClass.coe_pow, MulMemClass.coe_mul, SubringClass.coe_natCast, z]
    rw [← map_natCast (C : K →+* K⟦X⟧), ← mul_assoc, ← map_mul, mul_inv_cancel₀ hl0, map_one, one_mul])
  let ε : ZMod a → A O K := Pi.single τ 1
  have hpow : ∀ s, (ε * y s) ^ N = (l : ZMod a → A O K) * Pi.single τ (z s) := fun s => by
    funext σ
    rcases eq_or_ne σ τ with rfl | hσ
    · simp [ε, hz]
    · simp [ε, hσ, hN]
  obtain ⟨Φ, hΦi, hΦ⟩ : ∃ Φ : (ZMod a → A O K) →ₐ[O] OW l O, Function.Injective Φ ∧
      ∀ s, inclO l O (ϖ.iTot t K (y s)) = Φ (y s) :=
    ⟨(inclO l O).comp (ϖ.iTot t K), inclO_injective.comp (ϖ.iTot_injective t K), fun _ => rfl⟩
  simp only [hΦ] at h
  have hidem : IsIdempotentElem (Φ ε) := by
    show Φ ε * Φ ε = Φ ε
    rw [← map_mul]
    congr 1
    simp only [ε, ← Pi.single_mul, one_mul]
  have hne0 : Φ ε ≠ 0 := fun h0 => by
    have h1 := congrFun (hΦi (h0.trans (map_zero Φ).symm)) τ
    simp [ε] at h1
  let I : Ideal (OW l O) := Ideal.span {((l : ℕ) : OW l O)}
  have hnil : ∀ s, IsNilpotent (Ideal.Quotient.mk I (Φ ε * Φ (y s))) := fun s => by
    refine ⟨N, ?_⟩
    rw [← map_pow, ← map_mul, ← map_pow, hpow, map_mul, map_natCast, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have hsum : Φ ε = ∑ s, c s * (Φ ε * Φ (y s)) := by
    calc Φ ε = Φ ε * ∑ s, c s * Φ (y s) := by rw [h, mul_one]
      _ = ∑ s, c s * (Φ ε * Φ (y s)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun s _ => by ring
  have hmk : Ideal.Quotient.mk I (Φ ε) = 0 := by
    refine IsIdempotentElem.eq_zero_of_isNilpotent ?_ ?_
    · show _ * _ = _
      rw [← map_mul, hidem.eq]
    · rw [hsum, map_sum]
      refine isNilpotent_sum fun s _ => ?_
      rw [map_mul]
      exact (Commute.all _ _).isNilpotent_mul_left (hnil s)
  obtain ⟨x, hx⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 hmk)
  have hdvd : ∀ n, Φ ε ∈ Ideal.span {((l : ℕ) : OW l O) ^ n} := fun n => by
    rw [Ideal.mem_span_singleton]
    cases n with
    | zero => exact one_dvd _
    | succ n =>
      rw [← hidem.pow_succ_eq n, ← hx, mul_pow]
      exact dvd_mul_left _ _
  have hcpl := GlobalTheory.HWL.TensorWitt.complete_tensor (Module.Free.chooseBasis ℤ_[l] O) ((l : ℕ) : WCb l)
  have e1 : (1 : O) ⊗ₜ[ℤ_[l]] ((l : ℕ) : WCb l) = ((l : ℕ) : OW l O) :=
    map_natCast (Algebra.TensorProduct.includeRight : WCb l →ₐ[ℤ_[l]] OW l O) l
  rw [e1] at hcpl
  exact hne0 (GlobalTheory.Per.AinfComplete.eq_zero_of_haus ((l : ℕ) : OW l O) (Φ ε) hdvd)

end GlobalTheory.ResidueUnitCoeff
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitOfSpan
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.TwistDR

theorem exists_unit_of_span {k F R : Type} [Field k] [Infinite k] [Field F] [CommRing R] [Algebra F R]
    [Module k R] [Module.Finite F R] (hk : ∀ (c : k) (x : R), ∃ r : R, c • x = r * x)
    (U : Submodule k R) (hU : Submodule.span F (U : Set R) = ⊤) : ∃ d ∈ U, IsUnit d := by
  classical
  haveI : IsArtinianRing R := IsArtinianRing.of_finite F R
  haveI : Fintype (MaximalSpectrum R) := Fintype.ofFinite _
  let S : MaximalSpectrum R → Submodule k U := fun m =>
    { carrier := {x | (x : R) ∈ m.asIdeal}
      add_mem' := fun ha hb => m.asIdeal.add_mem ha hb
      zero_mem' := m.asIdeal.zero_mem
      smul_mem' := fun c x hx => by
        obtain ⟨r, hr⟩ := hk c x
        change c • (x : R) ∈ m.asIdeal
        rw [hr]
        exact m.asIdeal.mul_mem_left r hx }
  have hS : ⊤ ∉ Finset.univ.image S := by
    intro h
    obtain ⟨m, -, hm⟩ := Finset.mem_image.1 h
    apply m.isMaximal.ne_top
    rw [Ideal.eq_top_iff_one]
    have h1 : Submodule.span F (U : Set R) ≤ m.asIdeal.restrictScalars F :=
      Submodule.span_le.2 fun x hx => (hm ▸ Submodule.mem_top : (⟨x, hx⟩ : U) ∈ S m)
    exact h1 (hU ▸ Submodule.mem_top)
  have h2 := Subspace.biUnion_ne_univ_of_top_notMem hS
  obtain ⟨x, hx⟩ := (Set.ne_univ_iff_exists_notMem _).1 h2
  refine ⟨x, x.2, ?_⟩
  by_contra hn
  obtain ⟨m, hm, hxm⟩ := exists_max_ideal_of_mem_nonunits hn
  apply hx
  exact Set.mem_biUnion (x := S ⟨m, hm⟩) (by simp) hxm

section Generic

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem mem_DdR (ρ : Representation LL G V) (x : V ⊗[Qp] BdR) :
    x ∈ DdR PD ρ ↔ ∀ g, actVdR PD ρ g x = x := by
  simp [DdR, sub_eq_zero]

def tw (χ : G → LL) (g : G) : BdR ⊗[Qp] LL →ₗ[Qp] BdR ⊗[Qp] LL :=
  TensorProduct.map (((PD.actdR g).toAlgHom.toLinearMap).restrictScalars Qp) (LinearMap.mulLeft Qp (χ g))

theorem tw_tmul (χ : G → LL) (g : G) (b : BdR) (c : LL) :
    tw PD χ g (b ⊗ₜ[Qp] c) = PD.actdR g b ⊗ₜ[Qp] (χ g * c) := rfl

theorem tw_smul (χ : G → LL) (g : G) (b : BdR) (w : BdR ⊗[Qp] LL) :
    tw PD χ g (b • w) = PD.actdR g b • tw PD χ g w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul c v => simp [tw_tmul, TensorProduct.smul_tmul']
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

def twInv (χ : G → LL) : Submodule K (BdR ⊗[Qp] LL) where
  carrier := {x | ∀ g, tw PD χ g x = x}
  add_mem' ha hb g := by rw [map_add, ha g, hb g]
  zero_mem' g := map_zero _
  smul_mem' c x hx g := by
    rw [← algebraMap_smul BdR c x, tw_smul, AlgEquiv.commutes, hx g]

theorem finrank_twInv [FiniteDimensional Qp LL] (ν : Representation LL G (Fin 1 → LL)) (χ : G → LL)
    (hν : ∀ g x, ν g x = χ g • x) (h : finrank LL ↥(DdR PD ν) = finrank Qp K * finrank LL (Fin 1 → LL)) :
    finrank K ↥(twInv PD χ) = finrank Qp LL := by
  haveI := PD.finK
  let e : (Fin 1 → LL) ⊗[Qp] BdR ≃ₗ[Qp] BdR ⊗[Qp] LL :=
    ((LinearEquiv.funUnique (Fin 1) Qp LL).rTensor BdR).trans (TensorProduct.comm Qp LL BdR)
  have he : ∀ g x, e (actVdR PD ν g x) = tw PD χ g (e x) := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [e, actVdR, tw_tmul, hν]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hm : ((DdR PD ν).restrictScalars Qp).map (e : _ →ₗ[Qp] _) = (twInv PD χ).restrictScalars Qp := by
    ext y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply, Submodule.restrictScalars_mem, mem_DdR]
    refine forall_congr' fun g => ?_
    rw [← he, e.injective.eq_iff]
  have h1 : finrank Qp ↥(twInv PD χ) = finrank Qp ↥(DdR PD ν) := by
    have := LinearEquiv.finrank_map_eq e ((DdR PD ν).restrictScalars Qp)
    rw [hm] at this
    exact this
  rw [← Module.finrank_mul_finrank Qp K ↥(twInv PD χ), ← Module.finrank_mul_finrank Qp LL ↥(DdR PD ν), h,
    finrank_fintype_fun_eq_card, Fintype.card_fin, mul_one, mul_comm (finrank Qp LL)] at h1
  exact Nat.eq_of_mul_eq_mul_left finrank_pos h1

theorem exists_unit [Infinite Qp] [FiniteDimensional Qp LL] (hB : IsField BdR) (χ : G → LL)
    (h : finrank K ↥(twInv PD χ) = finrank Qp LL) : ∃ d ∈ twInv PD χ, IsUnit d := by
  letI : Field BdR := hB.toField
  haveI : Infinite K := Infinite.of_injective _ (algebraMap Qp K).injective
  have hpos : 0 < finrank Qp LL := finrank_pos
  haveI : Module.Finite K ↥(twInv PD χ) := Module.finite_of_finrank_pos (h ▸ hpos)
  refine exists_unit_of_span (F := BdR) (fun c x => ⟨algebraMap K _ c, Algebra.smul_def c x⟩) _ ?_
  let v := Module.finBasisOfFinrankEq K _ h
  have h1 : LinearIndependent K fun i => (v i : BdR ⊗[Qp] LL) :=
    v.linearIndependent.map' (twInv PD χ).subtype (twInv PD χ).ker_subtype
  have h2 : LinearIndependent BdR fun i => (v i : BdR ⊗[Qp] LL) := by
    rw [linearIndependent_iff_finset_linearIndependent]
    intro s
    refine GlobalTheory.RegularRing.linearIndepOn_of_invariant (fun g b => PD.actdR g b)
      (fun g => (tw PD χ g).toAddMonoidHom) (tw_smul PD χ) ?_ _ (fun g i => (v i).2 g) s
      (h1.linearIndepOn _)
    intro b b' hb hg
    obtain ⟨c, hc⟩ := PD.invdR (b' / b) fun g => by
      have h3 : PD.actdR g b ≠ 0 := (map_ne_zero _).2 hb
      rw [map_div₀, div_eq_div_iff h3 hb]
      linear_combination hg g
    exact ⟨c, by rw [hc, div_mul_cancel₀ _ hb]⟩
  haveI : Nonempty (Fin (finrank Qp LL)) := ⟨⟨0, hpos⟩⟩
  rw [eq_top_iff, ← h2.span_eq_top_of_card_eq_finrank (by simp)]
  refine Submodule.span_mono ?_
  rintro _ ⟨i, rfl⟩
  exact (v i).2

variable (V) in

def mulR : BdR ⊗[Qp] LL →ₗ[Qp] (V ⊗[Qp] BdR →ₗ[LL] V ⊗[Qp] BdR) :=
  TensorProduct.lift (LinearMap.mk₂ Qp
    (fun b c => c • AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (LinearMap.mulLeft Qp b))
    (fun b b' c => by ext; simp [add_mul, tmul_add])
    (fun q b c => by ext; simp [smul_comm q c])
    (fun b c c' => add_smul _ _ _)
    (fun q b c => smul_assoc _ _ _))

theorem mulR_tmul (b : BdR) (c : LL) (v : V) (b' : BdR) :
    mulR V (b ⊗ₜ[Qp] c) (v ⊗ₜ[Qp] b') = (c • v) ⊗ₜ[Qp] (b * b') := by
  simp [mulR, smul_tmul']

theorem mulR_one (x : V ⊗[Qp] BdR) : mulR V (1 : BdR ⊗[Qp] LL) x = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => rw [Algebra.TensorProduct.one_def, mulR_tmul, one_smul, one_mul]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem mulR_mul (d d' : BdR ⊗[Qp] LL) (x : V ⊗[Qp] BdR) :
    mulR V (d * d') x = mulR V d (mulR V d' x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul v b =>
    induction d using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [add_mul, map_add, LinearMap.add_apply, hx, hy]
    | tmul b₁ c₁ =>
      induction d' using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [mul_add, map_add, LinearMap.add_apply, hx, hy]
      | tmul b₂ c₂ => simp only [Algebra.TensorProduct.tmul_mul_tmul, mulR_tmul, mul_smul, mul_assoc]

theorem act_mulR (ρ ρ' : Representation LL G V) (χ : G → LL) (hρ : ∀ g x, ρ' g x = χ g • ρ g x)
    (g : G) (d : BdR ⊗[Qp] LL) (x : V ⊗[Qp] BdR) :
    actVdR PD ρ' g (mulR V d x) = mulR V (tw PD χ g d) (actVdR PD ρ g x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul v b =>
    induction d using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
    | tmul b₁ c₁ => simp [mulR_tmul, tw_tmul, actVdR, hρ, mul_smul]

theorem finrank_DdR_twist [Infinite Qp] [FiniteDimensional Qp LL] (hB : IsField BdR)
    (ρ ρ' : Representation LL G V) (ν : Representation LL G (Fin 1 → LL)) (χ : G → LL)
    (hν : ∀ g x, ν g x = χ g • x) (hρ : ∀ g x, ρ' g x = χ g • ρ g x)
    (h : finrank LL ↥(DdR PD ν) = finrank Qp K * finrank LL (Fin 1 → LL)) :
    finrank LL ↥(DdR PD ρ') = finrank LL ↥(DdR PD ρ) := by
  obtain ⟨_, hd, d, rfl⟩ := exists_unit PD hB χ (finrank_twInv PD ν χ hν h)
  let e : V ⊗[Qp] BdR ≃ₗ[LL] V ⊗[Qp] BdR := LinearEquiv.ofLinear (mulR V d.1) (mulR V d⁻¹.1)
    (LinearMap.ext fun x => by
      rw [LinearMap.comp_apply, ← mulR_mul, Units.mul_inv, mulR_one, LinearMap.id_apply])
    (LinearMap.ext fun x => by
      rw [LinearMap.comp_apply, ← mulR_mul, Units.inv_mul, mulR_one, LinearMap.id_apply])
  have he : ∀ g x, actVdR PD ρ' g (e x) = e (actVdR PD ρ g x) := fun g x => by
    change actVdR PD ρ' g (mulR V d.1 x) = mulR V d.1 _
    rw [act_mulR PD ρ ρ' χ hρ, hd g]
  have hm : (DdR PD ρ).map (e : _ →ₗ[LL] _) = DdR PD ρ' := by
    ext y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply, mem_DdR, mem_DdR]
    refine forall_congr' fun g => ?_
    rw [he, e.injective.eq_iff]
  rw [← hm, LinearEquiv.finrank_map_eq]

end Generic

theorem isDR_twist_iff : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ ρ' : Representation ↥LL.1 ↥(GK K) V) (ν : Representation ↥LL.1 ↥(GK K) (Fin 1 → ↥LL.1)) (χ : ↥(GK K) → ↥LL.1), (∀ g x, ν g x = χ g • x) → (∀ g x, ρ' g x = χ g • ρ g x) → IsDR (P.PD K) ν → (IsDR (P.PD K) ρ ↔ IsDR (P.PD K) ρ') := by
  intro l _ P AI T K LL V _ _ _ _ _ ρ ρ' ν χ hν hρ h
  haveI := LL.2
  unfold IsDR
  rw [finrank_DdR_twist (P.PD K) (GlobalTheory.RegularRing.isField_of_tied T) ρ ρ' ν χ hν hρ h]

end GlobalTheory.TwistDR
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteInertiaImpliesPotSemistableProof
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem unrStep_holds : UnrStep := by
  intro l _ P AI T n _ _ K r ρ hρ hfin
  obtain ⟨K', hK, hI, hc⟩ := GlobalTheory.T.unramified_over_finExt_of_finite_inertia_image l n K r ρ hρ hfin
  let ι : ↥(GK K') →* ↥(GK K) := Subgroup.inclusion (GK_le hK)
  let ρ' : ↥(GK K') →* GL n ↥(MaximalUnramifiedExtension l) := ρ.comp ι
  have hι : Continuous ι := continuous_subtype_val.subtype_mk _
  have hρ' : IsRat r ρ' :=
    { pos := hρ.pos
      le := fun c hc => hK (hρ.le c hc)
      rat := fun g i j => hρ.rat (ι g) i j
      cont := fun i j => (hρ.cont i j).comp hι }
  obtain ⟨Q, hQ⟩ := GlobalTheory.T.exists_crystalline_period_unramified_rep l P AI T n K' r ρ' hρ' (fun g hg => hI g hg) (fun g i j => hc g i j)
  refine ⟨K', hK, Units.map (RingHom.mapMatrix (Polynomial.C : P.R.B →+* Bst P)).toMonoidHom Q, fun g => ?_⟩
  have h1 : ((Units.map (RingHom.mapMatrix (Polynomial.C : P.R.B →+* Bst P)).toMonoidHom Q : GL n (Bst P)) :
      Matrix n n (Bst P)) = (Q : Matrix n n P.R.B).map Polynomial.C := rfl
  have h2 : ((Q : Matrix n n P.R.B).map Polynomial.C).map (actSt P (g : GQ l)) =
      ((Q : Matrix n n P.R.B).map (P.actQ (g : GQ l))).map (Polynomial.C : P.R.B →+* Bst P) := by
    rw [Matrix.map_map, Matrix.map_map]
    congr 1
    funext b
    exact actSt_C P _ b
  have h3 : (ρ ⟨g, GK_le hK g.2⟩ : Matrix n n ↥(MaximalUnramifiedExtension l)).map (ks P) =
      ((ρ' g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B)).map (Polynomial.C : P.R.B →+* Bst P) := by
    rw [Matrix.map_map]
    rfl
  rw [h1, h2, h3, ← Matrix.map_mul, hQ g]

end GlobalTheory.PMon

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankMulMinpolyNatDegreeLeOfPowEqNeg
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

open IntermediateField in

theorem GlobalTheory.finrank_mul_minpoly_natDegree_le_of_pow_eq_neg : ∀ (l : ℕ) [Fact l.Prime] (F : IntermediateField ℚ_[l] (Om l)) (N : ℕ) (x : Om l), 0 < N → x ^ N = -(l : Om l) → F ≤ IntermediateField.adjoin ℚ_[l] {x} → Module.finrank ℚ_[l] F * (minpoly F x).natDegree ≤ N := by
  intro l _ F N x hN hx hF
  have hp : (Polynomial.X ^ N + Polynomial.C (l : ℚ_[l])).Monic :=
    Polynomial.monic_X_pow_add_C _ hN.ne'
  have hroot : Polynomial.aeval x (Polynomial.X ^ N + Polynomial.C (l : ℚ_[l])) = 0 := by simp [hx]
  have hint : IsIntegral ℚ_[l] x := ⟨_, hp, hroot⟩
  have hdeg : (minpoly ℚ_[l] x).natDegree ≤ N := by
    have h1 := minpoly.min ℚ_[l] x hp hroot
    rw [Polynomial.degree_X_pow_add_C hN] at h1
    exact Polynomial.natDegree_le_of_degree_le h1
  have hintF : IsIntegral F x := hint.tower_top
  have key := Module.finrank_mul_finrank ℚ_[l] F (F⟮x⟯)
  have hE : (F⟮x⟯).restrictScalars ℚ_[l] = ℚ_[l]⟮x⟯ := by
    rw [restrictScalars_adjoin]
    apply le_antisymm
    · rw [adjoin_le_iff]
      rintro y (hy | hy)
      · exact hF hy
      · rw [Set.mem_singleton_iff.mp hy]; exact mem_adjoin_simple_self _ _
    · exact adjoin.mono _ _ _ (Set.subset_union_right)
  have h2 : Module.finrank ℚ_[l] (F⟮x⟯) = Module.finrank ℚ_[l] (ℚ_[l]⟮x⟯) := by
    rw [← hE]; rfl
  rw [← adjoin.finrank hintF, key, h2, adjoin.finrank hint]
  exact hdeg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineBoundsCrystallineDeRhamAll
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.Per.FontaineAll

noncomputable def extRep {G : Type} [Group G] {LL : Type} [Field LL] (LL' : Type) [Field LL']
    [Algebra LL LL'] {V : Type} [AddCommGroup V] [Module LL V] (ρ : Representation LL G V) :
    Representation LL' G (LL' ⊗[LL] V) where
  toFun g := (ρ g).baseChange LL'
  map_one' := by rw [map_one]; exact LinearMap.baseChange_one LL V
  map_mul' g h := by rw [map_mul]; exact LinearMap.baseChange_mul _ _

theorem fontCore_of_tied (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (hT : LocTied l P AI) (K : FinExt l) : Formalism.MainNotions.LocalSituation.fontCore (P.PD K) := by
  intro LL _ _ _ O _ _ hO A
  haveI : FiniteDimensional ℚ_[l] LL := hO.2.1
  obtain ⟨LL', ⟨f⟩, -, -⟩ := GlobalTheory.T.exists_finExt_embedding_splitting' l K LL
  letI : Algebra LL ↥LL'.1 := f.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ_[l] LL ↥LL'.1 :=
    IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
  haveI : FiniteDimensional ℚ_[l] ↥LL'.1 := LL'.2
  haveI : FiniteDimensional LL ↥LL'.1 := Module.Finite.of_restrictScalars_finite ℚ_[l] LL ↥LL'.1
  obtain ⟨hV, -, ⟨hc, hcf⟩, ⟨hd, hdf⟩, -⟩ :=
    GlobalTheory.T.finrank_periodFunctor_coeff_baseChange (P.PD K) LL ↥LL'.1 A.V (↥LL'.1 ⊗[LL] A.V) A.ρ (extRep ↥LL'.1 A.ρ)
      (TensorProduct.mk LL ↥LL'.1 A.V 1) (TensorProduct.isBaseChange LL A.V ↥LL'.1)
      (fun g x => by simp [extRep])
  obtain ⟨h1, h2⟩ := GlobalTheory.Per.FontaineBound.fontaineLe_of_tied l P AI hT K LL'
  obtain ⟨h3, h4⟩ := GlobalTheory.Per.TiedDdR.ddR_finrank_le l P AI hT K LL' _ (extRep ↥LL'.1 A.ρ)
  refine ⟨⟨hcf.1 (h2 _ _), ?_⟩, ⟨hdf.1 h3, ?_⟩, fun hcr => ?_⟩
  · rw [← hc, ← hV]; exact h1 _ _
  · rw [← hd, ← hV]; exact h4
  · have h5 : IsCrys (P.PD K) (extRep ↥LL'.1 A.ρ) := by
      unfold IsCrys at hcr ⊢
      rw [hc, hV]; exact hcr
    have h6 := (GlobalTheory.Per.CrisDR.isDR_of_isCrys l P AI hT K LL' _ _ h5).1
    unfold IsDR at h6 ⊢
    rw [← hd, ← hV]; exact h6

theorem fontaine_bounds : ∀ D : D7, Formalism.MainNotions.LocalSituation.adm7 D :=
  fun D l _ K => fontCore_of_tied l (D.loc l) (D.locA l) (D.locT l) K

end GlobalTheory.Per.FontaineAll
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisRepsCuspidalStatement
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_reps_cuspidal : ∀ D : D7, SumRepresentations.adm2 D → GlobalTheory.BlockComplement.GaloisRepsCusp D := by
  first | exact @GlobalTheory.GaloisFromAdm.main | exact GlobalTheory.GaloisFromAdm.main | (intros; apply GlobalTheory.GaloisFromAdm.main <;> assumption)
end

