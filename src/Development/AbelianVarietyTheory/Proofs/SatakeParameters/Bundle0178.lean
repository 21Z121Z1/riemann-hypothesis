import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0166
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0051
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0172
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0170
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0171
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0075
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0964
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalHeckeScalarLabelCompEqShiftDownSplit
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CentralShift

open Formalism.L2.NTheta GlobalTheory.SplitPlace GlobalTheory.DualSplitRel

variable {D : D7}

theorem split_of_primeIdem {P : Pl D.host.E} (hP : conjPl P ≠ P) {e f : AE D} (h : IsPrimeIdem P e f) :
    IsIdemAt e P ∧ f = e + cA D e := by
  rcases h with h | ⟨-, ⟨v, ε, -, rfl⟩, ht⟩
  · exact h
  · refine absurd (GlobalTheory.IdemSupport.eq_of_le (Ideal.map_le_iff_le_comap.2 fun x hx => ?_)) hP
    have h2 := GlobalTheory.IdemSupport.Comparison₂.conj (P := P) ht
    rw [GlobalTheory.IdemSupport.cA_algebraMap] at h2
    by_cases h0 : x = 0
    · rw [h0]; exact zero_mem _
    · exact (h2 x h0).2 ((ht x h0).1 hx)

theorem dual_shift (d : List ℤ) : dualLab ((dualLab (d.map fun x => x - 1)).map (· - 1)) = d := by
  simp [dualLab, List.map_reverse, List.map_map, Function.comp_def]

theorem shift {P : Pl D.host.E} (hP : conjPl P ≠ P) {V : HSp D} {d : List ℤ} {R : Finset (GA D V)} [DecidableEq (GA D V)]
    (hR : SphOp V P d R) : ∃ z : GA D V, (∀ γ ∈ R, γ * z = z * γ) ∧
      SphOp V P (splitLab V.rank V.rank) {z} ∧ SphOp V P (d.map fun x => x - 1) (R.image (· * z)) := by
  obtain ⟨e, f, ϖ, α, -, hpi, h1, h2, hd, -, -, hα, hD, hRs, hc⟩ := hR
  obtain ⟨he, rfl⟩ := split_of_primeIdem hP hpi
  have h0 : (ϖ : D.host.E) ≠ 0 := GlobalTheory.SphLabelOps.unif_ne_zero h2
  obtain ⟨z, hs, hzc, hz⟩ := exists_central he.1 V h0
  obtain ⟨K, hK⟩ := GlobalTheory.SphLabelOps.exists_hyp V P
  have hKl : locPart V (KsphC V ∅) e = (K : Set (GA D V)) := (hyp_eq_locPart he V).symm.trans hK
  have hKz : ∀ k ∈ locPart V (KsphC V ∅) e, k * z = z * k := fun k hk => hzc k hk.2
  have sh : ∀ {d : List ℤ} {g : GA D V} {R' : Finset (GA D V)}, SuppAt e V g → DivAt V e (ϖ : D.host.E) d g →
      (∀ γ ∈ R', SuppAt e V γ) → IsCosetRep V (locPart V (KsphC V ∅) e) g R' →
      (d.map (· - 1)).Pairwise (fun a b => b ≤ a) → SphOp V P (d.map (· - 1)) (R'.image (· * z)) := by
    intro d g R' sg dg sR hr hp
    obtain ⟨a, b⟩ := coset_mul hKz (fun γ hγ => (hr.1 γ hγ).2) hr.2
    have sup : ∀ γ ∈ R'.image (· * z), SuppAt e V γ := fun γ hγ => by
      obtain ⟨δ, hδ, rfl⟩ := Finset.mem_image.1 hγ
      exact suppAt_mul (sR δ hδ) hs
    exact sphOp_of he h1 h2 hp (suppAt_mul sg hs) (divAt_mul h0 hz dg) sup
      ⟨fun γ hγ => ⟨mem_GfC he.1 (sup γ hγ), a γ hγ⟩, b⟩
  have one : IsCosetRep V (locPart V (KsphC V ∅) e) 1 {1} := by
    have := coset_one K
    rw [← hKl] at this
    refine ⟨fun γ hγ => ⟨?_, this.1 γ hγ⟩, this.2⟩
    rw [Finset.mem_singleton.1 hγ]
    exact one_mem _
  have S0 := sh (GlobalTheory.SplitHecke.suppAt_one V)
    (GlobalTheory.SphLabelOps.divAt_one V he.1.1 (GlobalTheory.SphLabelOps.tie_of_isPrimeIdem (Or.inl ⟨he, rfl⟩)) (ϖ : D.host.E))
    (fun γ hγ => by rw [Finset.mem_singleton.1 hγ]; exact GlobalTheory.SplitHecke.suppAt_one V) one
    (by rw [label_shift_zero]; simp [splitLab, List.pairwise_append, List.pairwise_replicate])
  rw [label_shift_zero, Finset.image_singleton, one_mul] at S0
  refine ⟨z, fun γ hγ => hzc γ (hRs γ hγ), S0, sh hα hD hRs hc ?_⟩
  exact List.pairwise_map.2 (hd.imp fun h => by omega)

theorem isLab_of_shift {P : Pl D.host.E} (hP : conjPl P ≠ P) {V : HSp D} {d : List ℤ}
    (h : IsLab V P (d.map fun x => x - 1)) : IsLab V P d := by
  obtain ⟨R, e, f, ϖ, α, -, hpi, h1, h2, hd, -, -, hα, hD, -, -⟩ := h
  obtain ⟨he, rfl⟩ := split_of_primeIdem hP hpi
  have h0 : (ϖ : D.host.E) ≠ 0 := GlobalTheory.SphLabelOps.unif_ne_zero h2
  obtain ⟨z, hs, -, hz⟩ := exists_central he.1 V h0
  have D1 := (GlobalTheory.DivDual.divAt_inv_and_mul V e _ _ _ he.1.1 h0 hD).1
  have D2 := divAt_mul h0 hz D1
  have D3 := (GlobalTheory.DivDual.divAt_inv_and_mul V e _ _ _ he.1.1 h0 D2).1
  rw [dual_shift] at D3
  refine GlobalTheory.SphLabelOps.isLab_of_divAt hpi h1 h2 ?_ ?_ D3
  · exact (List.pairwise_map.1 hd).imp fun h => by omega
  · exact suppAt_inv (suppAt_mul (suppAt_inv hα) hs)

theorem central_shift : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E), conjPl P ≠ P → ∀ (d : List ℤ) (M : Type) [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (u : M), (∀ k ∈ hyp V P, π k u = u) → opOf π P (Finsupp.single (splitLab V.rank V.rank) 1) (opOf π P (Finsupp.single d 1) u) = opOf π P (Finsupp.single (d.map fun x => x - 1) 1) u := by
  classical
  intro D V P hP d M _ _ π u hu
  have c1 := (GlobalTheory.SphLabelOps.label_operators V P).1
  by_cases hl : IsLab V P d
  · obtain ⟨z, hzR, S0, S1⟩ := shift hP (GlobalTheory.SphLabelOps.sphOp_rep hl)
    have fw := (GlobalTheory.SphLabelOps.label_operators V P).2.1 (Finsupp.single d 1) M π u hu
    rw [← (c1 _ _ S0).2 M π _ fw, ← (c1 _ _ S1).2 M π u hu, Finset.sum_singleton, GlobalTheory.SphLabelOps.opOf_single,
      map_sum, Finset.sum_image (mul_left_injective z).injOn]
    refine Finset.sum_congr rfl fun γ hγ => ?_
    rw [hzR γ hγ, map_mul, Module.End.mul_apply]
  · have hl' : ¬ IsLab V P (d.map fun x => x - 1) := fun h => hl (isLab_of_shift hP h)
    have e0 : rep V P d = ∅ := by rw [Hk3.rep, dif_neg hl]
    have e1 : rep V P (d.map fun x => x - 1) = ∅ := by rw [Hk3.rep, dif_neg hl']
    rw [GlobalTheory.SphLabelOps.opOf_single π d, e0, Finset.sum_empty, map_zero, GlobalTheory.SphLabelOps.opOf_single, e1,
      Finset.sum_empty]

end GlobalTheory.CentralShift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TemperedRepTemperedParameter
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.LocLanglands
namespace TemperedRec

theorem tempered_lpSum : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (x y : WD h), x.tempered → y.tempered → (x.lpSum y).tempered := GlobalTheory.T.tempered_direct_sum

theorem tempered_lpChar_lpSp : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (x : WD h), x.mono0 → (∀ φ : Weil h, deg φ = 1 → ∀ α ∈ x.eig φ, ‖α‖ = 1) → ∀ l : ℕ, (x.lpChar (WD.lpSp h l)).tempered := GlobalTheory.T.tempered_special_of_unit_eigen

theorem norm_eig_eq_of_isIrrWD : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (x : WD h), IsIrrWD x → ∀ φ : Weil h, deg φ = 1 → ∀ α ∈ x.eig φ, ∀ β ∈ x.eig φ, ‖α‖ = ‖β‖ := GlobalTheory.T.irreducible_wd_eigen_equal_norm

theorem prod_eig_lpChar_lpSp : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (x : WD h) (l : ℕ) (σ : Weil h), ((x.lpChar (WD.lpSp h l)).eig σ).prod = ((x.eig σ).prod) ^ l := GlobalTheory.T.lp_character_eigen_product

theorem not_precedes_of_norm_eig : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (rc : IrrGL (w.adicCompletion E) → WD h), IsRec h rc → ∀ Δ Δ' : Segment (w.adicCompletion E), (∀ φ : Weil h, deg φ = 1 → ∀ α ∈ ((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).eig φ, ‖α‖ = 1) → (∀ φ : Weil h, deg φ = 1 → ∀ α ∈ ((rc Δ'.first).lpTw (((Δ'.len : ℝ) - 1) / 2)).eig φ, ‖α‖ = 1) → ¬ Δ.Precedes Δ' := GlobalTheory.T.segment_sum_tempered

theorem monodromy_zero_of_irreducible_weilDeligne : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (x : WD h), IsIrrWD x → x.mono0 := by
  intro E Ω _ _ _ _ _ A w h x ⟨n, a, hx, hirr⟩
  subst hx
  rw [WD.monodromyZero_ofWeilDeligneRepClass_iff]
  have hq : ((normV w : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (zero_lt_one.trans (one_lt_normV w)).ne'
  let S : Subrepresentation a.ρ := ⟨LinearMap.ker a.N, fun σ v hv => by
    have h1 := a.comm_apply σ v
    rw [LinearMap.mem_ker.1 hv, map_zero] at h1
    exact LinearMap.mem_ker.2 ((smul_eq_zero.1 h1.symm).resolve_left (zpow_ne_zero _ hq))⟩
  rcases hirr.eq_bot_or_eq_top S with hS | hS
  · exfalso
    have hinj : Function.Injective a.N := by
      rw [← LinearMap.ker_eq_bot]
      exact congrArg Subrepresentation.toSubmodule hS
    obtain ⟨m, hm⟩ := a.nilpotent
    have hinj' : Function.Injective (a.N ^ m) := by
      rw [Module.End.coe_pow]; exact hinj.iterate m
    rw [hm] at hinj'
    have := Model.nontrivial_of_isIrreducible hirr
    obtain ⟨v, hv⟩ := exists_ne (0 : Fin n → ℂ)
    exact hv (hinj' (a₁ := v) (a₂ := 0) (by simp))
  · refine LinearMap.ext fun v => ?_
    have : v ∈ S.toSubmodule := by rw [hS]; trivial
    exact LinearMap.mem_ker.1 this

theorem tempered_lpZero {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w) : (WD.lpZero h).tempered :=
  (WD.tempered_mk _).mpr ((WD.tempered_diag_iff _).mpr fun i => i.elim0)

theorem tempered_sumList {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} :
    ∀ l : List (WD h), (∀ y ∈ l, y.tempered) → (sumList l).tempered
  | [], _ => tempered_lpZero h
  | y :: l, H => tempered_lpSum E Ω A w h y (sumList l) (H y (by simp))
      (tempered_sumList l fun z hz => H z (by simp [hz]))

theorem norm_centralChar_eq_one {k : Type} [CommRing k] {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    [Nontrivial V] {π : Representation ℂ (GL (Fin n) k) V} {ω : kˣ →* ℂˣ} (hu : IsUnitarisable π)
    (hω : HasCentralChar π ω) (z : kˣ) : ‖(ω z : ℂ)‖ = 1 := by
  obtain ⟨B, -, hpos, hinv⟩ := hu
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have h1 := hinv (Matrix.GeneralLinearGroup.scalar (Fin n) z) v v
  rw [hω] at h1
  simp only [map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul] at h1
  have hB : B v v ≠ 0 := fun h0 => by have := hpos v hv; rw [h0] at this; simp at this
  have h2 : ((ω z : ℂ) * starRingEnd ℂ (ω z : ℂ)) * B v v = 1 * B v v := by linear_combination h1
  have h3 := mul_right_cancel₀ hB h2
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at h3
  have h4 : ‖(ω z : ℂ)‖ ^ 2 = 1 := by exact_mod_cast h3
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h4

theorem norm_eq_one_of_norm_prod {s : Multiset ℂ} (hp : ‖s.prod‖ = 1) (hs : ∀ α ∈ s, ∀ β ∈ s, ‖α‖ = ‖β‖) {α : ℂ}
    (hα : α ∈ s) : ‖α‖ = 1 := by
  have hmap : s.map (fun β => ‖β‖) = Multiset.replicate (Multiset.card s) ‖α‖ := by
    rw [Multiset.eq_replicate]
    refine ⟨by simp, fun r hr => ?_⟩
    obtain ⟨β, hβ, rfl⟩ := Multiset.mem_map.1 hr
    exact (hs α hα β hβ).symm
  have h1 : ‖s.prod‖ = (s.map (fun β => ‖β‖)).prod := map_multiset_prod (normHom : ℂ →*₀ ℝ) s
  rw [hmap, Multiset.prod_replicate, hp] at h1
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (Multiset.card_pos_iff_exists_mem.2 ⟨α, hα⟩).ne').1 h1.symm

theorem isCosocle_rep_cl {G : Type} [Group G] [TopologicalSpace G] (σ : IrrRep G) {V : Type} [AddCommGroup V]
    [Module ℂ V] {π : Representation ℂ G V} (e : σ.ρ.Equiv π) : IsCosocle σ.cl.rep.ρ π := by
  obtain ⟨f⟩ := σ.nonempty_equiv_rep
  exact (isCosocle_self σ.irr).of_equiv f.symm e

theorem norm_eig_segParam {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    {rc : IrrGL (w.adicCompletion E) → WD h} (hrc : IsRec h rc) (δ : IrrGL (w.adicCompletion E))
    (Δ : Segment (w.adicCompletion E)) (hΔ : IsLSeg Δ δ.rep) (hu : IsUnitarisable δ.rep) :
    ∀ φ : Weil h, deg φ = 1 → ∀ α ∈ ((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).eig φ, ‖α‖ = 1 := by
  obtain ⟨a, ha, ε, -, H⟩ := hrc
  intro φ hφ
  have hz : (rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2) = rc (Δ.first.nu ((((Δ.len : ℝ) - 1) / 2 : ℝ) : ℂ)) :=
    (H.nu_eq _ _).symm
  have hirr : IsIrrWD ((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)) := by
    rw [hz]; exact (H.cusp _).1 (Δ.isCusp_first.nu _)
  have hδ : rc δ = ((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).lpChar (WD.lpSp h Δ.len) := by
    have hL : IsL ((([Δ] : List (Segment (w.adicCompletion E))) : Multiset (Segment (w.adicCompletion E)))) δ.rep := by
      simpa using hΔ.isL
    rw [H.langlands [Δ] δ hL]
    exact WD.lpSum_zero _
  obtain ⟨ω, -, hω⟩ := exists_smooth_hasCentralChar δ.2.rep.smooth δ.2.rep.irr
  have : Nontrivial δ.2.rep.V := Model.nontrivial_of_isIrreducible δ.2.rep.irr
  have hc := H.central δ ω hω φ
  rw [hδ, prod_eig_lpChar_lpSp] at hc
  have hn : ‖((((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).eig φ).prod)‖ ^ Δ.len = 1 := by
    rw [← norm_pow, hc]; exact norm_centralChar_eq_one hu hω _
  have hp1 := (pow_eq_one_iff_of_nonneg (norm_nonneg _) Δ.len_pos.ne').1 hn
  intro α hα
  exact norm_eq_one_of_norm_prod hp1 (norm_eig_eq_of_isIrrWD E Ω A w h _ hirr φ hφ) hα

end TemperedRec

open TemperedRec in

theorem tempered_of_isTemperedGL : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (rc : IrrGL (w.adicCompletion E) → WD h), IsRec h rc → ∀ (n : ℕ) (σ : IrrRep (GL (Fin n) (w.adicCompletion E))), GlobalTheory.LocGL.IsTemperedGL σ.ρ → (rc (cls σ)).tempered := by
  intro E Ω _ _ _ _ _ A w h rc hrc n σ hσ
  have hrc' := hrc
  obtain ⟨a, ha, ε, -, H⟩ := hrc'
  obtain ⟨m, δ, hd, hδ, ⟨e⟩⟩ := hσ
  choose Δ hΔ using fun i => (hδ i).1
  have hunit := fun i => norm_eig_segParam hrc (δ i) (Δ i) (hΔ i) (hδ i).2
  have hL : IsL (((List.ofFn Δ : List (Segment (w.adicCompletion E)))) : Multiset (Segment (w.adicCompletion E)))
      (cls σ).rep := by
    refine ⟨m, δ, hd, ⟨Δ, ⟨?_, fun i j _ hp => not_precedes_of_norm_eig E Ω A w h rc hrc (Δ i) (Δ j) (hunit i) (hunit j) hp⟩, hΔ⟩, ?_⟩
    · exact Fin.univ_val_map Δ
    · exact isCosocle_rep_cl σ e
  rw [H.langlands _ _ hL]
  refine tempered_sumList _ fun y hy => ?_
  obtain ⟨Γ, hΓ, rfl⟩ := List.mem_map.1 hy
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hΓ
  have hz : (rc (Δ i).first).lpTw ((((Δ i).len : ℝ) - 1) / 2) = rc ((Δ i).first.nu (((((Δ i).len : ℝ) - 1) / 2 : ℝ) : ℂ)) :=
    (H.nu_eq _ _).symm
  have hirr : IsIrrWD ((rc (Δ i).first).lpTw ((((Δ i).len : ℝ) - 1) / 2)) := by
    rw [hz]; exact (H.cusp _).1 ((Δ i).isCusp_first.nu _)
  exact tempered_lpChar_lpSp E Ω A w h _ (monodromy_zero_of_irreducible_weilDeligne E Ω A w h _ hirr) (hunit i) _

end GlobalTheory.LocLanglands
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaIntegralVacuumIntertwinesSphericalHecke
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaIntHecke

theorem integral_move {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H]
    [BorelSpace H] {μ : Measure H} [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
    {Γ : Subgroup H} [Countable Γ] {𝓕 : Set H} (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (K : Set H) (x : H)
    (A A' : Finset H) (Kn F : H → ℂ) (hA : ∀ a ∈ A, ∃ k₁ ∈ K, ∃ k₂ ∈ K, a = k₁ * x * k₂)
    (hA' : ∀ a ∈ A', ∃ k₁ ∈ K, ∃ k₂ ∈ K, a = k₁ * x⁻¹ * k₂) (hcard : A'.card = A.card)
    (hFl : ∀ γ ∈ Γ, ∀ h, F (γ * h) = F h) (hFr : ∀ k ∈ K, ∀ h, F (h * k) = F h)
    (hKl : ∀ γ ∈ Γ, ∀ h, Kn (γ * h) = Kn h) (hKr : ∀ k ∈ K, ∀ h, Kn (h * k) = Kn h)
    (hx : IntegrableOn (fun h => Kn h * F (h * x)) 𝓕 μ) :
    IntegrableOn (fun h => Kn h * ∑ a ∈ A, F (h * a)) 𝓕 μ ∧
      IntegrableOn (fun h => (∑ a ∈ A', Kn (h * a)) * F h) 𝓕 μ ∧
      ∫ h in 𝓕, Kn h * ∑ a ∈ A, F (h * a) ∂μ = ∫ h in 𝓕, (∑ a ∈ A', Kn (h * a)) * F h ∂μ := by
  have hu : ∀ γ ∈ Γ, ∀ h, (fun h => Kn h * F (h * x)) (γ * h) = (fun h => Kn h * F (h * x)) h := by
    intro γ hγ h
    simp only [hKl γ hγ, mul_assoc, hFl γ hγ]
  have h1e : ∀ a ∈ A, ∃ y, (fun h => Kn h * F (h * a)) = fun h => (fun h => Kn h * F (h * x)) (h * y) := by
    intro a ha
    obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := hA a ha
    refine ⟨k₁, funext fun h => ?_⟩
    simp only
    rw [hKr k₁ hk₁, ← mul_assoc, hFr k₂ hk₂, ← mul_assoc]
  have h2e : ∀ a ∈ A', ∃ y, (fun h => Kn (h * a) * F h)
      = fun h => (fun h => Kn h * F (h * x)) (h * y) := by
    intro a ha
    obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := hA' a ha
    refine ⟨k₁ * x⁻¹, funext fun h => ?_⟩
    have : h * (k₁ * x⁻¹) * x = h * k₁ := by group
    simp only [this]
    rw [hFr k₁ hk₁, ← mul_assoc, hKr k₂ hk₂]
  have key : ∀ u : H → ℂ, (∃ y, u = fun h => (fun h => Kn h * F (h * x)) (h * y)) →
      IntegrableOn u 𝓕 μ ∧ ∫ h in 𝓕, u h ∂μ = ∫ h in 𝓕, Kn h * F (h * x) ∂μ := by
    rintro _ ⟨y, rfl⟩
    exact ⟨integrableOn_fundamentalDomain_mul_right h𝓕 y _ hu hx,
      setIntegral_fundamentalDomain_mul_right h𝓕 y _ hu⟩
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  refine ⟨integrable_finsetSum _ fun a ha => (key _ (h1e a ha)).1,
    integrable_finsetSum _ fun a ha => (key _ (h2e a ha)).1, ?_⟩
  rw [integral_finsetSum _ fun a ha => (key _ (h1e a ha)).1,
    integral_finsetSum _ fun a ha => (key _ (h2e a ha)).1,
    Finset.sum_congr rfl fun a ha => (key _ (h1e a ha)).2,
    Finset.sum_congr rfl fun a ha => (key _ (h2e a ha)).2, Finset.sum_const, Finset.sum_const, hcard]

variable {D : D7}

theorem exists_dual (V : HSp D) (P : Pl D.host.E) (d : List ℤ) (R : Finset (GA D V)) (h : SphOp V P d R) :
    ∃ α ∈ GfC V, ∃ R', SphOp V P (dualLab d) R' ∧ R'.card = R.card ∧
      (∀ γ ∈ R, ∃ k₁ ∈ hyp V P, ∃ k₂ ∈ hyp V P, γ = k₁ * α * k₂) ∧
      ∀ γ ∈ R', ∃ k₁ ∈ hyp V P, ∃ k₂ ∈ hyp V P, γ = k₁ * α⁻¹ * k₂ := by
  obtain ⟨e, f, ϖ, α, hS, hef, hϖ, hϖ2, hd, hJ, hχ, hα, hdiv, hR, hrep⟩ := h
  obtain ⟨he, v, hf⟩ := HeckeDual.idem_of_isPrimeIdem hef
  obtain ⟨a, rfl⟩ := (HeckeDual.suppF_iff V hf α).1 hα
  obtain ⟨δ, hδ, hσδ⟩ := HeckeDual.exists_skew D
  have := HeckeDual.isLattice_frameLat V
  have hK : ∀ g, g ∈ {k | k ∈ KsphC V ∅ ∧ SuppF V f k} ↔
      ∃ k ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram (GlobalTheory.AdelicU.frameLat V) v,
        GlobalTheory.AdelicU.emb D.sp.cm.sig V.gram v k = g := fun g => by
    constructor
    · rintro ⟨h3, h2⟩
      obtain ⟨k, rfl⟩ := (HeckeDual.suppF_iff V hf g).1 h2
      rw [GlobalTheory.AdelicU.KsphC_eq] at h3
      have h4 := (GlobalTheory.AdelicU.mem_levelOff.1 h3).2.2 v (Finset.notMem_empty v)
      rw [GlobalTheory.AdelicU.proj_emb_self] at h4
      exact ⟨k, h4, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      have h2 := (HeckeDual.suppF_iff V hf _).2 ⟨k, rfl⟩
      refine ⟨?_, h2⟩
      rw [GlobalTheory.AdelicU.KsphC_eq]
      exact GlobalTheory.AdelicU.emb_mem_levelOff (Finset.notMem_empty v) hk
  obtain ⟨R', h1, h2, h3⟩ := HeckeDual.exists_rep_inv
    (HeckeDual.modular_eq_one D.sp.cm.sig V.gram (fun x => star_star x) hδ hσδ
      ((GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm).2 V) v)
    (GlobalTheory.AdelicU.emb D.sp.cm.sig V.gram v) (GlobalTheory.AdelicU.emb_injective _ _ v) _
    (GlobalTheory.AdelicU.isOpen_stabLoc _ _ _ v) (GlobalTheory.AdelicU.isCompact_stabLoc _ _ _ v) _ hK a R
    (fun γ hγ => (hrep.1 γ hγ).2) hrep.2
  have hϖ0 : (ϖ : D.host.E) ≠ 0 := fun h => hϖ2 (by
    rw [show ϖ = 0 from RingOfIntegers.ext h]
    exact zero_mem _)
  have hh : ∀ (β γ : GA D V), (∃ k₁ ∈ {k | k ∈ KsphC V ∅ ∧ SuppF V f k}, ∃ k₂ ∈ {k | k ∈ KsphC V ∅ ∧ SuppF V f k},
      γ = k₁ * β * k₂) → ∃ k₁ ∈ hyp V P, ∃ k₂ ∈ hyp V P, γ = k₁ * β * k₂ := by
    rintro β γ ⟨k₁, g₁, k₂, g₂, rfl⟩
    exact ⟨k₁, ⟨g₁.1, e, f, hef, g₁.2⟩, k₂, ⟨g₂.1, e, f, hef, g₂.2⟩, rfl⟩
  refine ⟨_, GlobalTheory.AdelicU.mem_finPts.2 (GlobalTheory.AdelicU.projInf_emb _ _ v a), R',
    ⟨e, f, ϖ, _, hS, hef, hϖ, hϖ2, ?_, hJ, hχ, (HeckeDual.suppF_iff V hf _).2 (inv_mem ⟨a, rfl⟩),
    (GlobalTheory.DivDual.divAt_inv_and_mul V e _ d _ he hϖ0 hdiv).1,
    fun γ hγ => (HeckeDual.suppF_iff V hf _).2 (h1 γ hγ).1,
    fun γ hγ => ⟨?_, (h1 γ hγ).2⟩, h2⟩, h3, fun γ hγ => hh _ _ (hrep.1 γ hγ).2, fun γ hγ => hh _ _ (h1 γ hγ).2⟩
  · rw [dualLab, List.pairwise_reverse, List.pairwise_map]
    exact hd.imp fun h => neg_le_neg h
  · obtain ⟨x, rfl⟩ := (h1 γ hγ).1
    exact GlobalTheory.AdelicU.mem_finPts.2 (GlobalTheory.AdelicU.projInf_emb _ _ v x)

theorem opOf_single {V : HSp D} {M : Type} [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M)
    (P : Pl D.host.E) (d : List ℤ) : opOf π P (Finsupp.single d 1) = ∑ γ ∈ Hk3.rep V P d, π γ := by
  unfold opOf
  rw [Finsupp.sum_single_index (by exact zero_smul _ _), one_smul]

theorem opOf_dualC {V : HSp D} {M : Type} [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M)
    (P : Pl D.host.E) (c : List ℤ →₀ ℂ) :
    opOf π P (dualC c) = ∑ d ∈ c.support, c d • ∑ γ ∈ Hk3.rep V P (dualLab d), π γ := by
  unfold opOf dualC
  rw [Finsupp.sum_mapDomain_index (by exact fun _ => zero_smul _ _) (by exact fun _ _ _ => add_smul _ _ _)]
  rfl

theorem exists_dual_rep (V : HSp D) (P : Pl D.host.E) (d : List ℤ) :
    ∃ α ∈ GfC V, ∃ R' : Finset (GA D V), R'.card = (Hk3.rep V P d).card ∧
      (∀ γ ∈ Hk3.rep V P d, ∃ k₁ ∈ hyp V P, ∃ k₂ ∈ hyp V P, γ = k₁ * α * k₂) ∧
      (∀ γ ∈ R', ∃ k₁ ∈ hyp V P, ∃ k₂ ∈ hyp V P, γ = k₁ * α⁻¹ * k₂) ∧
      ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (u : M),
        (∀ k ∈ hyp V P, π k u = u) → ∑ γ ∈ R', π γ u = ∑ γ ∈ Hk3.rep V P (dualLab d), π γ u := by
  by_cases h : IsLab V P d
  · have hs : SphOp V P d (Hk3.rep V P d) := by
      unfold Hk3.rep
      rw [dif_pos h]
      exact h.choose_spec
    obtain ⟨α, hα, R', h1, h2, h3, h4⟩ := exists_dual V P d _ hs
    refine ⟨α, hα, R', h2, h3, h4, fun M _ _ π u hu => ?_⟩
    rw [((GlobalTheory.T.spherical_label_operators_on_hyperspecial_fixed_vectors V P).1 _ _ h1).2 M π u hu, opOf_single, LinearMap.sum_apply]
  · have h0 : Hk3.rep V P d = ∅ := dif_neg h
    have h1 : Hk3.rep V P (dualLab d) = ∅ := dif_neg fun h' => h (((GlobalTheory.T.spherical_label_operators_on_hyperspecial_fixed_vectors V P).2.2.2.1 d).1.2 h')
    exact ⟨1, one_mem _, ∅, by rw [h0], by simp [h0], by simp, fun M _ _ π u _ => by rw [h1]⟩

theorem hk_apply (V : HSp D) (P : Pl D.host.E) (c : List ℤ →₀ ℂ) (F : GA D V → ℂ) (g : GA D V) :
    hk V P c F g = ∑ d ∈ c.support, c d * ∑ γ ∈ Hk3.rep V P d, F (g * γ) := by
  unfold hk Finsupp.sum
  rw [LinearMap.sum_apply, Finset.sum_apply]
  rfl

theorem liftInt_hk : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (P : Pl D.host.E), IsWeilDatumO ψ S T χS χT om → ∀ (ν : Measure (GA D T)) (𝓕 : Set (GA D T)), ν.IsHaarMeasure → IsFundamentalDomain (GQ T) 𝓕 ν → VacFix ψ om P → ∀ cS cT, Match ψ om P cS (dualC cT) → ∀ f, IsVacAt ψ S T P f → ∀ Φ : GA D T → ℂ, (∀ γ ∈ GQ T, ∀ h, Φ (γ * h) = Φ h) → (∀ k ∈ hyp T P, ∀ h, Φ (h * k) = Φ h) → (∀ g, ∀ y ∈ GfC T, IntegrableOn (fun h => thetaKO om g h f * Φ (h * y)) 𝓕 ν) → Lift.liftInt ν 𝓕 (thetaKO om) f (hk T P cT Φ) = hk S P cS (Lift.liftInt ν 𝓕 (thetaKO om) f Φ) := by
  intro D ψ S T χS χT om P hW ν 𝓕 hν h𝓕 hfix cS cT hM f hf Φ hΦl hΦr hint
  have : IsTopologicalGroup (GA D T) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have : BorelSpace (GA D T) := ⟨rfl⟩
  have : Countable (GQ T) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig T.gram
  have : ν.IsMulRightInvariant := GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D T ν hν
  obtain ⟨hl, hr⟩ := GlobalTheory.thetaKO_rat_left_and_eigen_right ψ S T χS χT om hW f hf.1
  have hfT : ∀ k ∈ hyp T P, om (1, k) f = f := fun k hk => by
    obtain ⟨e, f', hef⟩ : ∃ e f', IsPrimeIdem P e f' := hk.2.imp fun _ h => h.imp fun _ h => h.1
    refine hfix f hf 1 ⟨⟨one_mem _, fun y => ?_, by simp⟩, e, f', hef, fun i j => ?_⟩ k hk
    · have : finMat D.sp.cm.sig S.gram (1 : GA D S) = 1 := by
        unfold finMat
        exact Matrix.map_one _ (map_zero _) (map_one _)
      rw [this, Matrix.one_mulVec]
    · have : Formalism.L2.Theta.mt S (1 : GA D S) = 1 := by simp [Formalism.L2.Theta.mt]
      rw [this, sub_self, Matrix.zero_apply, mul_zero]
  have hth : ∀ g h a b, thetaKO om (g * a) (h * b) f = om (g, h) (om (a, b) f) 0 := fun g h a b => by
    unfold thetaKO
    rw [show ((g * a, h * b) : GA D S × GA D T) = (g, h) * (a, b) from rfl, map_mul, Module.End.mul_apply]
  funext g
  have step : ∀ d, IntegrableOn (fun h => thetaKO om g h f * ∑ a ∈ Hk3.rep T P d, Φ (h * a)) 𝓕 ν ∧
      IntegrableOn (fun h => (∑ a ∈ Hk3.rep T P (dualLab d), thetaKO om g (h * a) f) * Φ h) 𝓕 ν ∧
      ∫ h in 𝓕, thetaKO om g h f * ∑ a ∈ Hk3.rep T P d, Φ (h * a) ∂ν =
        ∫ h in 𝓕, (∑ a ∈ Hk3.rep T P (dualLab d), thetaKO om g (h * a) f) * Φ h ∂ν := fun d => by
    obtain ⟨α, hα, R', h1, h2, h3, h4⟩ := exists_dual_rep T P d
    have h5 := h4 _ (om.comp (MonoidHom.inr _ _)) f hfT
    have h6 : ∀ h, ∑ a ∈ Hk3.rep T P (dualLab d), thetaKO om g (h * a) f = ∑ a ∈ R', thetaKO om g (h * a) f := fun h => by
      have h7 := congrArg (fun u => om (g, h) u 0) h5
      simp only [map_sum, Finset.sum_apply] at h7
      have h8 : ∀ a, thetaKO om g (h * a) f = om (g, h) (om (1, a) f) 0 := fun a => by rw [← hth, mul_one]
      simp only [h8]
      exact h7.symm
    simp only [h6]
    exact integral_move h𝓕 (hyp T P) α _ R' (fun h => thetaKO om g h f) Φ h2 h3 h1 hΦl hΦr
      (fun γ hγ h => by simpa only [one_mul] using hl 1 (one_mem _) γ hγ g h)
      (fun k hk h => by simpa only [one_mul, mul_one] using hr 1 k 1 (by rw [hfT k hk, one_smul]) g h)
      (hint g α hα)
  have hker : ∀ h, ∑ d ∈ cT.support, cT d * ∑ a ∈ Hk3.rep T P (dualLab d), thetaKO om g (h * a) f =
      ∑ d ∈ cS.support, cS d * ∑ a ∈ Hk3.rep S P d, thetaKO om (g * a) h f := fun h => by
    have h7 := congrArg (fun u => om (g, h) u 0) (hM f hf)
    rw [opOf_dualC] at h7
    simp only [opOf, Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul] at h7
    have h8 : ∀ a, thetaKO om g (h * a) f = om (g, h) (om (1, a) f) 0 := fun a => by rw [← hth, mul_one]
    have h9 : ∀ a, thetaKO om (g * a) h f = om (g, h) (om (a, 1) f) 0 := fun a => by rw [← hth, mul_one]
    simp only [h8, h9]
    exact h7.symm
  have hi1 : ∀ g, IntegrableOn (fun h => thetaKO om g h f * Φ h) 𝓕 ν := fun g => by
    simpa only [mul_one] using hint g 1 (one_mem _)
  rw [hk_apply]
  unfold Lift.liftInt
  calc ∫ h in 𝓕, thetaKO om g h f * hk T P cT Φ h ∂ν
      = ∫ h in 𝓕, ∑ d ∈ cT.support, cT d * (thetaKO om g h f * ∑ a ∈ Hk3.rep T P d, Φ (h * a)) ∂ν := by
        congr 1
        funext h
        rw [hk_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun d _ => mul_left_comm _ _ _
    _ = ∫ h in 𝓕, ∑ d ∈ cT.support, cT d * ((∑ a ∈ Hk3.rep T P (dualLab d), thetaKO om g (h * a) f) * Φ h) ∂ν := by
        rw [integral_finsetSum _ fun d _ => (step d).1.const_mul _,
          integral_finsetSum _ fun d _ => (step d).2.1.const_mul _]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [integral_const_mul, integral_const_mul, (step d).2.2]
    _ = ∫ h in 𝓕, ∑ d ∈ cS.support, cS d * ∑ a ∈ Hk3.rep S P d, thetaKO om (g * a) h f * Φ h ∂ν := by
        congr 1
        funext h
        simp only [← mul_assoc, ← Finset.sum_mul]
        rw [hker]
    _ = _ := by
        rw [integral_finsetSum _ fun d _ => (integrable_finsetSum _ fun a _ => hi1 (g * a)).const_mul _]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [integral_const_mul, integral_finsetSum _ fun a _ => hi1 (g * a)]

end GlobalTheory.ThetaIntHecke
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UpwardThetaLiftInjectiveOnCarriedPartStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.upward_theta_lift_injective_on_carried_part : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.PThmB → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → ∀ p c, R.Carries p c → ∀ w ∈ R.EEc c, w ≠ 0 → LinearMap.adjoint (R.Th A3.A.μ0) w ≠ 0 := by
  first | exact @GlobalTheory.thetaUp_injective_on_carried | exact GlobalTheory.thetaUp_injective_on_carried | (intros; apply GlobalTheory.thetaUp_injective_on_carried <;> assumption)
end

