import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0052
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0048
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExtUHInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0135
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0142
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0140
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevQFiniteIndexAndRoot
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0132
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0258
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0229
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0239
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0250
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0257
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0014

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TemperedOfTemperedLpSum
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.WeilDeligne.PrimDecomp GlobalTheory.LocLanglands

namespace GlobalTheory.WeilDeligne.TemperedSummand

theorem map_pow_apply_of_comm {V V' : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup V']
    [Module ℂ V'] {N : Module.End ℂ V} {M : Module.End ℂ V'} (e : V →ₗ[ℂ] V')
    (hN : ∀ v, e (N v) = M (e v)) (i : ℕ) (v : V) : e ((N ^ i) v) = (M ^ i) (e v) := by
  induction i generalizing v with
  | zero => simp
  | succ i ih => rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, hN]

theorem isPurePair_of_retract {V V' : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup V']
    [Module ℂ V'] {q : ℝ} {f N : Module.End ℂ V} {g M : Module.End ℂ V'} (s : V' →ₗ[ℂ] V)
    (p : V →ₗ[ℂ] V') (hps : ∀ v, p (s v) = v) (hsf : ∀ v, s (g v) = f (s v))
    (hsN : ∀ v, s (M v) = N (s v)) (hpf : ∀ v, p (f v) = g (p v)) (hpN : ∀ v, p (N v) = M (p v))
    (hp : IsPurePair q f N) : IsPurePair q g M := by
  have hs : ∀ r v, v ∈ absSpace g r → s v ∈ absSpace f r :=
    fun r v hv => map_absSpace_le s hsf r ⟨v, hv, rfl⟩
  have hp' : ∀ r v, v ∈ absSpace f r → p v ∈ absSpace g r :=
    fun r v hv => map_absSpace_le p hpf r ⟨v, hv, rfl⟩
  have hr : LinearMap.range p = ⊤ := LinearMap.range_eq_top.mpr fun v => ⟨s v, hps v⟩
  refine ⟨?_, fun i => ⟨fun v hv => ?_, fun v hv v' hv' hvv => ?_, fun v hv => ?_⟩⟩
  · rw [eq_top_iff, ← hr, LinearMap.range_eq_map, ← hp.1, Submodule.map_iSup]
    exact iSup_mono fun i => map_absSpace_le p hpf _
  · have h1 := hp' _ _ ((hp.2 i).1 (hs _ v hv))
    rw [map_pow_apply_of_comm p hpN, hps] at h1
    exact h1
  · have h1 : s v = s v' := (hp.2 i).2.1 (hs _ v hv) (hs _ v' hv') (by
      rw [← map_pow_apply_of_comm s hsN, ← map_pow_apply_of_comm s hsN, hvv])
    rw [← hps v, h1, hps]
  · obtain ⟨u, hu, huv⟩ := (hp.2 i).2.2 (hs _ v hv)
    refine ⟨p u, hp' _ u hu, ?_⟩
    rw [← map_pow_apply_of_comm p hpN, huv, hps]

theorem tempered_of_tempered_lpSum : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω]
    [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E))
    (h : IsPlaceOver A w) (x y : WD h), (x.lpSum y).tempered → y.tempered := by
  intro E Ω _ _ _ _ _ A w h x y
  induction x using WD.ind with
  | hP m b =>
    induction y using WD.ind with
    | hP n c =>
      rw [WD.lpSum_mk, WD.tempered_mk, WD.tempered_mk]
      intro ht φ hφ
      exact isPurePair_of_retract (LinearMap.inr ℂ _ _) (LinearMap.snd ℂ _ _) (fun _ => rfl)
        (fun v => by simp) (fun v => by simp) (fun v => by simp) (fun v => by simp) (ht φ hφ)

end GlobalTheory.WeilDeligne.TemperedSummand
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TemperedTopWeightStrand
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.WeilDeligne.PrimDecomp GlobalTheory.LocLanglands

noncomputable section

open TensorProduct Module

namespace GlobalTheory.WeilDeligne.PrimDecomp

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
variable {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem N_mem_wtSpace (a : WDRep h V) {d : ℤ} {v : V} (hv : v ∈ wtSpace a d) :
    a.N v ∈ wtSpace a (d + 2) := by
  have hq : (1 : ℝ) < ((normV w : ℕ) : ℝ) := by exact_mod_cast one_lt_normV w
  have hq0 := zero_lt_one.trans hq
  suffices H : wtSpace a d ≤ Submodule.comap a.N (wtSpace a (d + 2)) from H hv
  refine iSup₂_le fun α hα v hv => Submodule.mem_iSup_of_mem _
    (Submodule.mem_iSup_of_mem ?_ (a.map_N_eigenspace deg_frob hv))
  rw [norm_mul, hα, Complex.norm_natCast, show (((d + 2 : ℤ) : ℝ) / 2) = 1 + (d : ℝ) / 2 by
    push_cast; ring, Real.rpow_add hq0, Real.rpow_one]

theorem iSupIndep_wtSpace (a : WDRep h V) : iSupIndep (wtSpace a) := by
  have hq : (1 : ℝ) < ((normV w : ℕ) : ℝ) := by exact_mod_cast one_lt_normV w
  have hq0 := zero_lt_one.trans hq
  refine iSupIndep_absSpace (r := fun i : ℤ => ((normV w : ℕ) : ℝ) ^ ((i : ℝ) / 2)) _
    fun i j hij => ?_
  simp only at hij
  rw [Real.rpow_right_inj hq0 hq.ne'] at hij
  exact_mod_cast (by linarith : (i : ℝ) = j)

theorem ρ_pow_N (a : WDRep h V) (σ : Weil h) (j : ℕ) (v : V) :
    a.ρ σ ((a.N ^ j) v) = (((normV w : ℕ) : ℂ) ^ deg σ) ^ j • (a.N ^ j) (a.ρ σ v) := by
  induction j generalizing v with
  | zero => simp
  | succ j ih =>
    simp only [pow_succ', End.mul_apply, a.comm_apply, ih, map_smul, smul_smul]

theorem spEig_mul_qPow (m : ℕ) (j : Fin (m + 1)) :
    (WDRep.spEig w (m + 1) j : ℂ) * (qPow w ((m : ℝ) / 2) : ℂ) = ((normV w : ℕ) : ℂ) ^ (j : ℕ) := by
  rw [WDRep.spEig, ← Units.val_mul, ← qPow_add,
    show (((j : ℕ) : ℝ) - (((m + 1 : ℕ) : ℝ) - 1) / 2 + (m : ℝ) / 2) = ((j : ℕ) : ℝ) by
      push_cast; ring, coe_qPow, Complex.ofReal_natCast, Complex.cpow_natCast]

end GlobalTheory.WeilDeligne.PrimDecomp

theorem GlobalTheory.WeilDeligne.PrimDecomp.mk_restrict_strand_eq : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (a : WDRep h V) (m : ℕ) (hS : ∀ σ, ∀ v ∈ wtSpace a (-(m : ℤ)), a.ρ σ v ∈ wtSpace a (-(m : ℤ))) (hB : IsSubWD a (strand a.N (wtSpace a (-(m : ℤ))) m)), a.Tempered → (∀ k : ℤ, (m : ℤ) < k → wtSpace a k = ⊥) → WD.mk (restrict a _ hB) = ((WD.mk (restrictρ a _ hS)).lpTw ((m : ℝ) / 2)).lpChar (WD.lpSp h (m + 1)) := by
  intro E Ω _ _ _ _ _ A w h V _ _ _ a m hS hB ht htop
  set U := wtSpace a (-(m : ℤ)) with hU
  have hpure := ht (frob h) deg_frob
  have hb : ∀ i : ℕ, Set.BijOn (a.N ^ i) (wtSpace a (-(i : ℤ))) (wtSpace a (i : ℤ)) := by
    intro i
    have := hpure.2 i
    simpa [wtSpace, neg_div] using this
  have hN2 : ∀ d, ∀ v ∈ wtSpace a d, a.N v ∈ wtSpace a (d + 2) := fun d v hv => N_mem_wtSpace a hv
  have hkill : ∀ u ∈ U, (a.N ^ (m + 1)) u = 0 := by
    intro u hu
    have := pow_mem_of_degree_two hN2 (m + 1) (e := (m : ℤ) + 2) (by push_cast; ring) hu
    rwa [htop _ (by omega), Submodule.mem_bot] at this
  let Φ : (Fin (m + 1) → U) →ₗ[ℂ] V :=
    ∑ j : Fin (m + 1), (a.N ^ (j : ℕ)) ∘ₗ U.subtype ∘ₗ LinearMap.proj j
  have hΦ : ∀ f, Φ f = ∑ j : Fin (m + 1), (a.N ^ (j : ℕ)) (f j : V) := by intro f; simp [Φ]
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro f hf
    rw [LinearMap.mem_ker, hΦ] at hf
    have hi : Function.Injective fun j : Fin (m + 1) => -(m : ℤ) + 2 * ((j : ℕ) : ℤ) := by
      intro i j hij
      simp only at hij
      exact Fin.ext (by omega)
    have hind := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).mp
      ((iSupIndep_wtSpace a).comp hi) Finset.univ (fun j => (a.N ^ (j : ℕ)) (f j : V))
      (fun j _ => pow_mem_of_degree_two hN2 j rfl (f j).2) hf
    funext j
    apply Subtype.ext
    exact eq_zero_of_pow_eq_zero hb (d := -(m : ℤ)) (m := j) (by omega) (f j).2
      (hind j (Finset.mem_univ _))
  have hrange : LinearMap.range Φ = strand a.N U m := by
    apply le_antisymm
    · rintro _ ⟨f, rfl⟩
      rw [hΦ]
      exact Submodule.sum_mem _ fun j _ => Submodule.mem_iSup_of_mem j ⟨f j, (f j).2, rfl⟩
    · refine iSup_le fun j => ?_
      rintro _ ⟨u, hu, rfl⟩
      refine ⟨Pi.single j ⟨u, hu⟩, ?_⟩
      rw [hΦ, Finset.sum_eq_single j (fun k _ hk => by simp [Pi.single_eq_of_ne hk]) (by simp)]
      simp
  let eT : U ⊗[ℂ] (Fin (m + 1) → ℂ) ≃ₗ[ℂ] strand a.N U m :=
    (TensorProduct.piScalarRight ℂ ℂ U (Fin (m + 1))).trans
      ((LinearEquiv.ofInjective Φ hinj).trans (LinearEquiv.ofEq _ _ hrange))
  have heT : ∀ (x : U) (c : Fin (m + 1) → ℂ),
      (eT (x ⊗ₜ c) : V) = ∑ j : Fin (m + 1), c j • (a.N ^ (j : ℕ)) (x : V) := by
    intro x c
    simp [eT, hΦ, TensorProduct.piScalarRightHom_tmul]
  rw [WD.lpTw_mk, WD.lpSp, WD.lpChar_mk]
  refine WD.sound (WDRep.Iso.symm ⟨eT, fun σ t => Subtype.ext ?_, fun t => Subtype.ext ?_⟩)
  · induction t using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, Submodule.coe_add, hx, hy]
    | tmul x c =>
      rw [WDRep.tensor_ρ, TensorProduct.map_tmul, heT, restrict_ρ_apply, heT, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [WDRep.sp_ρ, diagEnd_apply, WDRep.tw_ρ, LinearMap.smul_apply, Submodule.coe_smul,
        restrictρ_ρ_apply, map_smul, map_smul, ρ_pow_N, smul_smul, smul_smul]
      congr 1
      have key : (WDRep.spEig w (m + 1) j : ℂ) ^ deg σ * (qPow w ((m : ℝ) / 2) : ℂ) ^ deg σ =
          (((normV w : ℕ) : ℂ) ^ deg σ) ^ (j : ℕ) := by
        rw [← mul_zpow, spEig_mul_qPow, ← zpow_natCast, ← zpow_mul, ← zpow_natCast, ← zpow_mul,
          mul_comm]
      rw [← key, coe_qPow]
      ring
  · induction t using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, Submodule.coe_add, hx, hy]
    | tmul x c =>
      have hNs : ∀ (k : ℕ) (y : V), a.N ((a.N ^ k) y) = (a.N ^ (k + 1)) y := fun k y => by
        rw [pow_succ', End.mul_apply]
      rw [WDRep.tensor_N, LinearMap.add_apply, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
        WDRep.tw_N, restrictρ_N, LinearMap.zero_apply, zero_tmul, zero_add, heT,
        restrict_N_apply, heT, map_sum]
      simp only [map_smul, hNs, WDRep.sp_N]
      rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
      simp [shiftEnd_apply, hkill x x.2]
      exact Finset.sum_congr rfl fun i _ => rfl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TemperedWeightSpaceBound
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.WeilDeligne.PrimDecomp GlobalTheory.LocLanglands

namespace GlobalTheory.WeilDeligne.PrimDecomp

theorem IsPurePair.absSpace_neg_eq_bot_iff {V : Type*} [AddCommGroup V] [Module Complex V]
    {q : Real} {f N : Module.End Complex V} (hp : IsPurePair q f N) (n : Nat) :
    absSpace f (q ^ (-(n : Real) / 2)) = ⊥ ↔ absSpace f (q ^ ((n : Real) / 2)) = ⊥ := by
  constructor
  · intro h0
    rw [eq_bot_iff]
    intro v hv
    obtain ⟨u, hu, rfl⟩ := (hp.2 n).2.2 hv
    have : u = 0 := by
      have : u ∈ (⊥ : Submodule Complex V) := h0 ▸ hu
      simpa using this
    simp [this]
  · intro h0
    rw [eq_bot_iff]
    intro v hv
    have h1 : (N ^ n) v ∈ absSpace f (q ^ ((n : Real) / 2)) := (hp.2 n).1 hv
    rw [h0, Submodule.mem_bot] at h1
    have := (hp.2 n).2.1 hv (zero_mem _) (by simpa using h1)
    simp [this]

theorem exists_top_weight :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
      (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (V : Type)
      [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (a : WDRep h V), a.Tempered →
      Nontrivial V → ∃ m : ℕ, wtSpace a (-(m : ℤ)) ≠ ⊥ ∧ ∀ k : ℤ, (m : ℤ) < k → wtSpace a k = ⊥ := by
  intro E Ω _ _ _ _ _ A w h V _ _ _ a ha hV
  have hp := ha (frob h) deg_frob
  set q : ℝ := ((normV w : ℕ) : ℝ)
  have hw : ∀ k : ℤ, wtSpace a k = absSpace (a.ρ (frob h)) (q ^ ((k : ℝ) / 2)) := fun _ => rfl
  have hneg : ∀ n : ℕ, wtSpace a (-(n : ℤ)) = ⊥ ↔ wtSpace a (n : ℤ) = ⊥ := by
    intro n
    rw [hw, hw]
    push_cast
    exact IsPurePair.absSpace_neg_eq_bot_iff hp n
  set d := Module.finrank ℂ V
  have hbig : ∀ k : ℤ, (d : ℤ) ≤ |k| → wtSpace a k = ⊥ := fun k hk =>
    hp.absSpace_eq_bot_of_finrank_le a.nilpotent hk

  have hex : ∃ n : ℕ, wtSpace a (n : ℤ) ≠ ⊥ := by
    by_contra hc
    push_neg at hc
    have hall : ∀ i : ℤ, wtSpace a i = ⊥ := by
      intro i
      rcases le_total 0 i with hi | hi
      · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hi
        exact hc n
      · obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = -(n : ℤ) := ⟨(-i).toNat, by omega⟩
        exact (hneg n).2 (hc n)
    have htop := hp.1
    simp only [← hw, hall, iSup_bot] at htop
    exact bot_ne_top htop
  classical
  let P : ℕ → Prop := fun n => wtSpace a (n : ℤ) ≠ ⊥
  obtain ⟨n₀, hn₀⟩ := hex
  have hn₀d : n₀ ≤ d := by
    by_contra hc
    exact hn₀ (hbig _ (by rw [abs_of_nonneg (by positivity)]; omega))
  refine ⟨Nat.findGreatest P d, ?_, ?_⟩
  · rw [Ne, hneg]
    exact Nat.findGreatest_spec (P := P) hn₀d hn₀
  · intro k hk
    have hk0 : 0 ≤ k := le_trans (by positivity) hk.le
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk0
    have hn : Nat.findGreatest P d < n := by exact_mod_cast hk
    by_cases hnd : n ≤ d
    · have := Nat.findGreatest_is_greatest (P := P) hn hnd
      simpa [P] using this
    · exact hbig _ (by rw [abs_of_nonneg (by positivity)]; omega)

end GlobalTheory.WeilDeligne.PrimDecomp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnChainsSatisfyConditions
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2

theorem GStep.Ok.reRep {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} {S : GStep E K n} (h : S.Ok)
    (pref : ∀ b, S.D b → Prop) : (S.reRep pref).Ok :=
  ⟨h.fin_orb, h.fin_stab, h.unit, h.root, h.lsh_smul, h.lsh_lat, h.stab_inj⟩

theorem GStep.Free.reRep {E K : Type} [Field E] [NumberField E] [Field K] {n : ℕ} {S : GStep E K n} (h : S.Free)
    (pref : ∀ b, S.D b → Prop) : (S.reRep pref).Free := fun b g d hd => h b g d hd

namespace TC

variable {B : Base} {X : PreX B.toPre} {I : TC B X}

theorem _root_.GlobalTheory.Mem.Col2.ColIn.Ok.xi_unitary (h : I.Ok) (a : I.ι) : (I.xi a).IsUnitary := by
  have ht : IsOfFinOrder (I.tup a : Chr B.fields.F B.fields.E B.fields.K) :=
    (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (I.tup a).2).1).1).1).2
  obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.1 ht
  exact HChar.isUnitary_of_order hn ((h.xi_reads a).orderDvd hpow)

theorem _root_.GlobalTheory.Mem.Col2.ColIn.Ok.unrepresented_step_conditions (h : I.Ok) (u : B.Word) (a : I.ι) (i : ℕ) : (I.stp0 u a i).Ok := by
  have hX : B.fields.Ok := (base_fields_primes_ok B X).1
  have hPr : (B.primes X).Ok := (base_fields_primes_ok B X).2.1
  refine StepOk.stepY_ok _ _ _ _ hX _ _ ?_ ?_ ?_
  · rintro ⟨_ | b, hb⟩ P
    · exact topLev_finiteIndex I.Ch I.sel (I.tup a) (I.cst a) I.Ps i P
    · exact (LevFin.levQ_finiteIndex_and_root I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) I.glob (B.R.m - 2) hX hPr
        (h.idx_ok a) i (hb.1 rfl) b P).1
  · rintro ⟨_ | b, hb⟩ P g
    · obtain ⟨m, hm, hk⟩ := topLev_root I.Ch I.sel (I.tup a) (I.cst a) I.Ps i P
      exact ⟨m, hm, hk g⟩
    · exact (LevFin.levQ_finiteIndex_and_root I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) I.glob (B.R.m - 2) hX hPr
        (h.idx_ok a) i (hb.1 rfl) b P).2 g
  · exact fun N hN => (CosetFin.ysAt_finite_nonempty B.R I.sel (I.tup a) (I.cst a) i N hN).1

theorem _root_.GlobalTheory.Mem.Col2.ColIn.Ok.stp_ok (h : I.Ok) (u : B.Word) (a : I.ι) (i : ℕ) : (I.stp u a i).Ok := (h.unrepresented_step_conditions u a i).reRep _

theorem _root_.GlobalTheory.Mem.Col2.ColIn.Ok.stp_zero_free (h : I.Ok) (u : B.Word) (a : I.ι) : (I.stp u a 0).Free :=
  GStep.Free.reRep (stepAt_zero_free I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) (I.Tp a) u (base_fields_primes_ok B X).1
    (base_fields_primes_ok B X).2.1 (base_fields_primes_ok B X).2.2.2.2 (h.idx_ok a).zero_G) _

theorem _root_.GlobalTheory.Mem.Col2.ColIn.Ok.chIn_ok (h : I.Ok) (u : B.Word) (a : I.ι) : (I.chIn u a).Ok where
  step i := h.stp_ok u a i
  rho_norm i _ c := by
    show ‖((rhoAt I.SQ I.C (I.xi a) i _ : ℂˣ) : ℂ)‖ = 1
    exact norm_rhoAt I.SQ I.C (h.xi_unitary a) i _
  rho'_norm i _ c := by
    show ‖((rhoAt' I.SQ I.C (I.xi a) i _ : ℂˣ) : ℂ)‖ = 1
    exact norm_rhoAt' I.SQ I.C (h.xi_unitary a) i _
  DG_pos := DGam_pos (posStar_of_ok (base_fields_primes_ok B X).1) B.R
  dvd_DG i hi c := by
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · have hf := h.stp_zero_free u a
      haveI : Subsingleton ((I.stp u a 0).Stab c) :=
        ⟨fun x y => Subtype.ext ((hf c.1 x.1 _ x.2).trans (hf c.1 y.1 _ y.2).symm)⟩
      rw [Nat.card_unique]
      exact one_dvd _
    · exact stepY_dvd _ _ _ _ ((I.Tp a).pref u i) (base_fields_primes_ok B X).1 B.R (N_mem_gamRanks B.R hpos hi) c.1 ((I.stp u a i).rep c)

theorem _root_.GlobalTheory.Mem.Col2.ColIn.Ok.idx0 (h : I.Ok) (a : I.ι) : Nonempty (Idx I.sel (I.tup a) (I.idx a) 0) := by
  obtain ⟨b, -⟩ := (h.idx_ok a).zero_uniq
  exact ⟨⟨some b, by simp only [Option.isSome_some, true_iff]; exact lt_of_lt_of_le (by norm_num) B.R.two_le_m⟩⟩

theorem rep_L_lattice (u : B.Word) (a : I.ι) (i : ℕ) (c : (I.stp u a i).Cl) :
    Submodule.IsLattice B.fields.E ((I.stp u a i).rep c).1.1.deco.1.L :=
  ((I.stp u a i).rep c).1.1.deco.2.L_lattice

theorem ok_chains : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ u a, (I.chIn u a).Ok ∧ Nonempty (Idx I.sel (I.tup a) (I.idx a) 0) ∧ ∀ i c, Submodule.IsLattice B.fields.E ((I.stp u a i).rep c).1.1.deco.1.L :=
  fun _ h u a => ⟨h.chIn_ok u a, h.idx0 a, fun i c => rep_L_lattice u a i c⟩

end TC

end GlobalTheory.Mem.Col2

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.Crd

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def Ortho (S : Formalism.BasicNotions.HSpace E) : Prop :=
  (∀ a b, S.hT (S.frame a) (S.frame b) = if a = b then 1 else 0) ∧ S.L0 = Submodule.span (𝓞 E) (Set.range S.frame)

theorem ortho_pos (hstar : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x)) (N : ℕ) : Ortho (Examples₂.posSpace hstar N) :=
  ⟨fun a b => (Examples₂.stdSpace_gram_apply hstar N (fun _ => false) N 0 a b).trans (by simp [Examples₂.sgn]; rfl), rfl⟩

abbrev co (S : Formalism.BasicNotions.HSpace E) {n : ℕ} (h : S.rank = n) : S.V ≃ₗ[E] (Fin n → E) :=
  S.frame.equivFun.trans (LinearEquiv.funCongrLeft E E (finCongr h).symm)

theorem Ortho.isStd {S : Formalism.BasicNotions.HSpace E} (h : Ortho S) : Formalism.L2.Herm.IsStd S := ⟨S.frame, h.1, h.2⟩

theorem Ortho.gram {S : Formalism.BasicNotions.HSpace E} (h : Ortho S) {n : ℕ} (hn : S.rank = n) :
    S.gram.reindex (finCongr hn) (finCongr hn) = 1 := by
  subst hn
  ext a b
  simpa [HSpace.gram, Matrix.one_apply] using h.1 a b

theorem Ortho.mem_standardLattice_iff_integral_coords {S : Formalism.BasicNotions.HSpace E} (h : Ortho S) {n : ℕ} (hn : S.rank = n) (x : Fin n → E) :
    x ∈ S.L0.map (((co S hn : S.V ≃ₗ[E] (Fin n → E)) : S.V →ₗ[E] (Fin n → E)).restrictScalars (𝓞 E)) ↔
      ∀ j, x j ∈ (algebraMap (𝓞 E) E).range := by
  subst hn
  rw [h.2]
  constructor
  · rintro ⟨v, hv, rfl⟩ j
    have := (Module.Basis.mem_span_iff_repr_mem (𝓞 E) S.frame v).1 hv j
    simpa [co] using this
  · intro hx
    refine ⟨(co S rfl).symm x, (Module.Basis.mem_span_iff_repr_mem (𝓞 E) S.frame _).2 fun j => ?_, (co S rfl).apply_symm_apply x⟩
    have h2 : S.frame.repr ((co S rfl).symm x) j = x j :=
      congrFun ((co S rfl).apply_symm_apply x) j
    rw [h2]
    exact hx j

theorem map_symm_map {S : Formalism.BasicNotions.HSpace E} {n : ℕ} (e : S.V ≃ₗ[E] (Fin n → E)) (L : Submodule (𝓞 E) (Fin n → E)) :
    (L.map ((e.symm : (Fin n → E) →ₗ[E] S.V).restrictScalars (𝓞 E))).map
      ((e : S.V →ₗ[E] (Fin n → E)).restrictScalars (𝓞 E)) = L := by
  ext x
  simp

theorem incl_co {S S' : Formalism.BasicNotions.HSpace E} {n : ℕ} (hn : S.rank = n) (hn' : S'.rank = n - 1) (f : S'.V →ₗ[E] S.V)
    (hf : ∀ (a : Fin S'.rank) (b : Fin S.rank), (a : ℕ) = b → f (S'.frame a) = S.frame b) (x : Fin (n - 1) → E) (j : Fin n) :
    co S hn (f ((co S' hn').symm x)) j = if h : j.1 < n - 1 then x ⟨j.1, h⟩ else 0 := by
  subst hn
  have hs : (co S' hn').symm x = ∑ a : Fin (S.rank - 1), x a • S'.frame (finCongr hn'.symm a) := by
    rw [LinearEquiv.symm_apply_eq]
    funext k
    rw [map_sum, Finset.sum_apply, Finset.sum_eq_single k]
    · simp [co]
    · intro a _ ha
      have : ¬ (a : ℕ) = k := fun h => ha (Fin.ext h)
      simp [co, Finsupp.single_apply, Fin.ext_iff, this]
    · simp
  have hb : ∀ a : Fin (S.rank - 1), f (S'.frame (finCongr hn'.symm a)) = S.frame ⟨a.1, by omega⟩ := fun a => hf _ _ rfl
  rw [hs, map_sum, map_sum]
  simp only [map_smul, hb, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hc : ∀ a : Fin (S.rank - 1), co S rfl (S.frame ⟨a.1, by omega⟩) j = if a.1 = j.1 then 1 else 0 := by
    intro a
    simp [co, Fin.ext_iff]
  simp only [hc]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨j.1, h⟩]
    · simp
    · intro a _ ha
      rw [if_neg (fun h2 => ha (Fin.ext h2)), mul_zero]
    · simp
  · refine Finset.sum_eq_zero fun a _ => ?_
    rw [if_neg (fun h2 : a.1 = j.1 => h (h2 ▸ a.2)), mul_zero]

end Gen

end GlobalTheory.Mem.Col2.Crd

end

set_option maxHeartbeats 1600000 in

theorem GlobalTheory.Mem.Col2.TC.spaces_in_coordinates : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), Formalism.L2.Herm.StdTied (I.rec7 l Z) ∧ gramP (I.rec7 l Z) = 1 ∧ (∀ x j, iXc (I.rec7 l Z) x j = if h : j.1 < B.R.N B.R.m - 1 then x ⟨j.1, h⟩ else 0) ∧ ∀ i (hi : i ≤ B.R.m), gramN (I.rec7 l Z) i hi = 1 ∧ (∀ x, x ∈ selfDualLatticeCoords (I.rec7 l Z) i hi ↔ ∀ j, x j ∈ (algebraMap (𝓞 B.host.E) B.host.E).range) ∧ ∀ u a, (∀ c, latCrd (I.rec7 l Z) i hi (I.latAt u a i c) = ((I.stp u a i).rep c).1.1.deco.1.L) ∧ ∃ (eY : (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi), I.IdY l Z u a i hi eY ∧ ∀ τ z, (I.chain l u a).de i z τ = ((eY z).1 τ).det := by
  intro B X I hI hP l Z
  obtain ⟨hs, hX, hX', -⟩ := hI.spaces
  have oX : ∀ j, Crd.Ortho (B.sp.X j) := fun j => by rw [hX]; exact Crd.ortho_pos hs _
  have oX' : Crd.Ortho B.sp.X' := by rw [hX']; exact Crd.ortho_pos hs _
  refine ⟨⟨fun i _ => (oX i).isStd, oX'.isStd⟩, oX'.gram (rankP (I.rec7 l Z)), fun x j => ?_, fun i hi =>
    ⟨(oX i).gram (rankN (I.rec7 l Z) i hi), fun x => (oX i).mem_standardLattice_iff_integral_coords (rankN (I.rec7 l Z) i hi) x, fun u a => ⟨fun c => ?_, ?_⟩⟩⟩
  · exact Crd.incl_co (S := B.sp.X B.R.m) (S' := B.sp.X') (rankN (I.rec7 l Z) _ le_rfl) (rankP (I.rec7 l Z)) B.sp.iX' hP.iX x j
  · unfold TC.latAt
    rw [dif_pos hi]
    exact Crd.map_symm_map (S := B.sp.X i) (TC.crd B i hi) _
  · exact ⟨Equiv.refl _, fun _ => rfl, fun _ _ => rfl⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedPowerHigherCohomVanishingPullbackIffPushfStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedPowerHigherCohomVanishing_pullback_iff_pushforward : ∀ {X Y : Scheme.{0}} (g : Y ⟶ X) [IsAffineHom g] (A N : LB X), A.IsLB → N.IsLB → ∀ (G : Y.Modules) [G.IsQuasicoherent], (TwistConeVanishing (A.pull g) (N.pull g) G ↔ TwistConeVanishing A N ((Scheme.Modules.pushforward g).obj G)) := by
  first | exact @GlobalTheory.twistConeVanishing_pull_iff_pushforward | exact GlobalTheory.twistConeVanishing_pull_iff_pushforward | (intros; apply GlobalTheory.twistConeVanishing_pull_iff_pushforward <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedPowerVanishingInductionBySectionSqTensorStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedPowerVanishing_induction_by_section_sq_tensor : ∀ {Y : Scheme.{0}} (A N : LB Y), A.IsLB → N.IsLB → ∀ (r : ℕ), 1 ≤ r → ∀ (hM : (lbPow (tens (lbPow N 2) A) r).IsLB) (s : (lbPow (tens (lbPow N 2) A) r).Sec) (G : Y.Modules), (∃ j₁ : ℕ, ∀ j m : ℕ, j₁ ≤ j → m < 2 * r → ∀ p, 0 < p → Subsingleton (coh (twist G (tens (lbPow A j) (lbPow N m))) p)) → TwistConeVanishing A N (kernel (cutHom G hM s)) → TwistConeVanishing A N (cokernel (cutHom G hM s)) → TwistConeVanishing A N G := by
  first | exact @GlobalTheory.twistConeVanishing_of_cut | exact GlobalTheory.twistConeVanishing_of_cut | (intros; apply GlobalTheory.twistConeVanishing_of_cut <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VolumesAgreeAdelicOfTrueVolumeStatement
section
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.volumesAgreeAdelic_of_trueVolume : ∀ D : D7, letI := D.host.cmStar; (∀ W, D.vol W = trueVol D.sp.cm (Formalism.BasicNotions.TH.tauE D) D.cd W) → Formalism.L2.Theta.VolTieG D := by
  first | exact @GlobalTheory.Mem.Vol.volTieG_of_trueVol | exact GlobalTheory.Mem.Vol.volTieG_of_trueVol | (intros; apply GlobalTheory.Mem.Vol.volTieG_of_trueVol <;> assumption)
end

