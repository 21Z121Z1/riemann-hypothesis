import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.H2EquivOfTorsionCharacter
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0127
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0129
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0244
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ActQdRPeriodTEqCyclotomicBottom
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0123
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0246
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeAlgebraMapOC
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemRootsBarXSubC
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PadicIntGLSmulMemPrincipalCongruenceFixed
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeterminantLemmaDiscreteValuationRingQuotientLen
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0245
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0170
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0216
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0225
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0249

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousTwoCocycleMultipleOfFundamental
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.GenSpan

open GlobalTheory.TateTop ReciprocityTheory.Gal

variable {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G]

theorem gen_zmod {χ : G →* ℤ_[l]ˣ} {r : ℕ} {c : G × G → ℤ_[l]} (h : Gen χ r c) :
    (IsLocallyConstant (fun p => PadicInt.toZModPow r (c p)) ∧
      ∀ g k m, PadicInt.toZModPow r (χ g : ℤ_[l]) * PadicInt.toZModPow r (c (k, m))
        - PadicInt.toZModPow r (c (g * k, m)) + PadicInt.toZModPow r (c (g, k * m))
        - PadicInt.toZModPow r (c (g, k)) = 0) ∧
    (∀ z : G × G → ZMod (l ^ r), IsLocallyConstant z →
      (∀ g k m, PadicInt.toZModPow r (χ g : ℤ_[l]) * z (k, m) - z (g * k, m) + z (g, k * m)
        - z (g, k) = 0) →
      ∃ (x : ZMod (l ^ r)) (b : G → ZMod (l ^ r)), IsLocallyConstant b ∧ ∀ p,
        z p = PadicInt.toZModPow r (c p) * x +
          (PadicInt.toZModPow r (χ p.1 : ℤ_[l]) * b p.2 - b (p.1 * p.2) + b p.1)) ∧
    (∀ (x : ZMod (l ^ r)) (b : G → ZMod (l ^ r)), IsLocallyConstant b →
      (∀ p, PadicInt.toZModPow r (c p) * x =
          PadicInt.toZModPow r (χ p.1 : ℤ_[l]) * b p.2 - b (p.1 * p.2) + b p.1) → x = 0) := by
  have : NeZero (l ^ r) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  let : Module ℤ_[l] (ZMod (l ^ r)) := Module.compHom _ (PadicInt.toZModPow r)
  have hs : ∀ (a : ℤ_[l]) (m : ZMod (l ^ r)), a • m = PadicInt.toZModPow r a * m := fun _ _ => rfl
  have h0 : PadicInt.toZModPow r ((l : ℤ_[l]) ^ r) = 0 := (dvd_iff_toZModPow _).1 dvd_rfl
  have hM : ∀ m : ZMod (l ^ r), (l : ℤ_[l]) ^ r • m = 0 := fun m => by rw [hs, h0, zero_mul]
  obtain ⟨h1, h2, h3⟩ := h _ hM
  refine ⟨?_, fun z hz hz' => ?_, fun x b hb hx => h3 x b hb fun p => ?_⟩
  · obtain ⟨a1, a2⟩ := h1 1
    simp only [hs, mul_one] at a1 a2
    exact ⟨a1, a2⟩
  · obtain ⟨x, b, hb, e⟩ := h2 z ⟨hz, fun g k m => by simpa only [hs] using hz' g k m⟩
    exact ⟨x, b, hb, fun p => by simpa only [GlobalTheory.TateTop.cob, hs] using e p⟩
  · simpa only [GlobalTheory.TateTop.cob, hs] using hx p

open GlobalTheory.PadicH2Separated in

theorem span : ∀ (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (χ : G →* ℤ_[l]ˣ) (c : G × G → ℤ_[l]), Continuous (fun g => (χ g : ℤ_[l])) → (∀ r, GlobalTheory.TateTop.Gen χ r c) → (∀ r : ℕ, 0 < r → Finite (ReciprocityTheory.Gal.H1 (ReciprocityTheory.Gal.charRep ((Units.map (PadicInt.toZModPow r : ℤ_[l] →+* ZMod (l ^ r)).toMonoidHom).comp χ)))) → (Continuous (fun p => (c p : ℚ_[l])) ∧ ∀ g h k, ((χ g : ℤ_[l]) : ℚ_[l]) * (c (h, k) : ℚ_[l]) - (c (g * h, k) : ℚ_[l]) + (c (g, h * k) : ℚ_[l]) - (c (g, h) : ℚ_[l]) = 0) ∧ ∀ z : G × G → ℚ_[l], Continuous z → (∀ g h k, ((χ g : ℤ_[l]) : ℚ_[l]) * z (h, k) - z (g * h, k) + z (g, h * k) - z (g, h) = 0) → ∃ (x : ℚ_[l]) (f : G → ℚ_[l]), Continuous f ∧ ∀ g h, ((χ g : ℤ_[l]) : ℚ_[l]) * f h - f (g * h) + f g = z (g, h) - x * (c (g, h) : ℚ_[l]) := by
  intro l _ G _ _ _ _ χ c hχ hgen hfin
  have hl : l.Prime := Fact.out
  have hG := fun r => gen_zmod (hgen r)
  have hcc : Continuous c := continuous_of_reductions c fun s => (hG (s + 1)).1.1.continuous
  have hcoc : ∀ g h k, (χ g : ℤ_[l]) * c (h, k) - c (g * h, k) + c (g, h * k) - c (g, h) = 0 := by
    intro g h k
    rw [← PadicInt.ext_of_toZModPow]
    intro n
    simpa only [map_sub, map_add, map_mul, map_zero] using (hG n).1.2 g h k
  refine ⟨⟨continuous_subtype_val.comp hcc, fun g h k => ?_⟩, fun z hz hzc => ?_⟩
  · have e := congrArg (fun a : ℤ_[l] => (a : ℚ_[l])) (hcoc g h k)
    push_cast at e
    exact e
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hz.continuousOn
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt C (by exact_mod_cast hl.one_lt : (1 : ℝ) < l)
  have hnorm : ∀ p, ‖(l : ℚ_[l]) ^ m * z p‖ ≤ 1 := fun p => by
    rw [norm_mul, Padic.norm_p_pow, zpow_neg, zpow_natCast]
    have hp : (0 : ℝ) < (l : ℝ) ^ m := by have := hl.pos; positivity
    rw [inv_mul_le_iff₀ hp, mul_one]
    exact (hC p trivial).trans hm.le
  let w : G × G → ℤ_[l] := fun p => ⟨(l : ℚ_[l]) ^ m * z p, hnorm p⟩
  have hw : ∀ p, (w p : ℚ_[l]) = (l : ℚ_[l]) ^ m * z p := fun _ => rfl
  have hwc : Continuous w := (continuous_const.mul hz).subtype_mk _
  have hwcoc : ∀ g h k, (χ g : ℤ_[l]) * w (h, k) - w (g * h, k) + w (g, h * k) - w (g, h) = 0 := by
    intro g h k
    have e : (((χ g : ℤ_[l]) * w (h, k) - w (g * h, k) + w (g, h * k) - w (g, h) : ℤ_[l]) :
        ℚ_[l]) = 0 := by
      push_cast [hw]
      linear_combination (l : ℚ_[l]) ^ m * hzc g h k
    exact PadicInt.coe_eq_zero.1 e
  have hlev : ∀ r, ∃ (x : ZMod (l ^ r)) (b : G → ZMod (l ^ r)), IsLocallyConstant b ∧ ∀ p,
      PadicInt.toZModPow r (w p) = PadicInt.toZModPow r (c p) * x +
        (PadicInt.toZModPow r (χ p.1 : ℤ_[l]) * b p.2 - b (p.1 * p.2) + b p.1) := fun r =>
    (hG r).2.1 _ ((IsLocallyConstant.iff_continuous _).2 ((continuous_reduction r).comp hwc))
      fun g k m => by
        simpa only [map_sub, map_add, map_mul, map_zero] using
          congrArg (PadicInt.toZModPow r) (hwcoc g k m)
  choose X B hB hXB using hlev
  have hred : ∀ r, PadicInt.toZModPow r (((X r).val : ℕ) : ℤ_[l]) = X r := fun r => by
    have : NeZero (l ^ r) := ⟨pow_ne_zero _ hl.ne_zero⟩
    rw [map_natCast, ZMod.natCast_zmod_val]
  have hcomp : ∀ r, ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r)) (X (r + 1)) = X r := by
    intro r
    set ψ := ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))
    have hψ : ∀ a : ℤ_[l], ψ (PadicInt.toZModPow (r + 1) a) = PadicInt.toZModPow r a := fun a => by
      rw [ZMod.castHom_apply]
      exact PadicInt.cast_toZModPow r (r + 1) (Nat.le_succ r) a
    rw [← sub_eq_zero]
    refine (hG r).2.2 _ (fun g => B r g - ψ (B (r + 1) g)) ((hB r).sub ((hB (r + 1)).comp ψ))
      fun p => ?_
    have e1 : PadicInt.toZModPow r (w p) = PadicInt.toZModPow r (c p) * ψ (X (r + 1)) +
        (PadicInt.toZModPow r (χ p.1 : ℤ_[l]) * ψ (B (r + 1) p.2) - ψ (B (r + 1) (p.1 * p.2)) +
          ψ (B (r + 1) p.1)) := by
      have := congrArg ψ (hXB (r + 1) p)
      simpa only [map_add, map_sub, map_mul, hψ] using this
    have e2 := hXB r p
    show PadicInt.toZModPow r (c p) * (ψ (X (r + 1)) - X r) =
      PadicInt.toZModPow r (χ p.1 : ℤ_[l]) * (B r p.2 - ψ (B (r + 1) p.2)) -
        (B r (p.1 * p.2) - ψ (B (r + 1) (p.1 * p.2))) + (B r p.1 - ψ (B (r + 1) p.1))
    linear_combination e2 - e1
  obtain ⟨x, hx⟩ := exists_lim (fun r => (((X r).val : ℕ) : ℤ_[l])) fun r => by
    rw [dvd_iff_toZModPow, map_sub, hred, ← PadicInt.cast_toZModPow r (r + 1) (Nat.le_succ r),
      hred]
    exact sub_eq_zero.2 (hcomp r)
  have hxr : ∀ r, PadicInt.toZModPow r x = X r := fun r => by
    have := (dvd_iff_toZModPow _).1 (hx r)
    rwa [map_sub, hred, sub_eq_zero] at this
  have hcont : ContAction (charRep χ) := by
    show Continuous fun p : G × ℤ_[l] => charRep χ p.1 p.2
    simp only [charRep_apply]
    exact (hχ.comp continuous_fst).mul continuous_snd
  have hcompat : ∀ (r : ℕ) (g : G) (a : ℤ_[l]), PadicInt.toZModPow r (charRep χ g a) =
      charRep ((Units.map (PadicInt.toZModPow r : ℤ_[l] →+* ZMod (l ^ r)).toMonoidHom).comp χ) g
        (PadicInt.toZModPow r a) := fun r g a => by
    simp [charRep_apply]
  have hyZ : (fun p => w p - x * c p) ∈ Z2 (charRep χ) := by
    refine (mem_cocycles2 _ _).2 ⟨hwc.sub (continuous_const.mul hcc), fun g h k => ?_⟩
    simp only [charRep_apply]
    linear_combination hwcoc g h k - x * hcoc g h k
  have hyB : ∀ r, (fun p => PadicInt.toZModPow r (w p - x * c p)) ∈
      B2 (charRep ((Units.map (PadicInt.toZModPow r : ℤ_[l] →+* ZMod (l ^ r)).toMonoidHom).comp χ)) := by
    intro r
    refine (separated_dvr_second_cohomology_mem _ _).2 ⟨B r, (hB r).continuous, funext fun p => ?_⟩
    obtain ⟨g, h⟩ := p
    simp only [d1_apply, charRep_apply, MonoidHom.comp_apply, Units.coe_map, map_sub, map_mul, hxr]
    have e := hXB r (g, h)
    simp only at e
    simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
    linear_combination -e
  have hker : ∀ r : ℕ, ∃ w' ∈ Z2 (charRep χ), (fun p => w p - x * c p) - (l : ℤ_[l]) ^ r • w' ∈
      B2 (charRep χ) := fun r =>
    GlobalTheory.padicInt_two_cocycle_eq_pow_smul_of_reduction_coboundary l G (charRep χ) hcont r _
      (hcompat r) _ hyZ (hyB r)
  obtain ⟨f, hf, hfd⟩ := (separated_dvr_second_cohomology_mem _ _).1 (mem_coboundaries_of_forall_pow l G (charRep χ) _ hcompat hfin _ hyZ hker)
  have hl0 : (l : ℚ_[l]) ^ m ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hl.ne_zero)
  refine ⟨(x : ℚ_[l]) / (l : ℚ_[l]) ^ m, fun g => (f g : ℚ_[l]) / (l : ℚ_[l]) ^ m,
    (continuous_subtype_val.comp hf).div_const _, fun g h => ?_⟩
  have e := congrFun hfd (g, h)
  simp only [d1_apply, charRep_apply] at e
  have e' := congrArg (fun a : ℤ_[l] => (a : ℚ_[l])) e
  push_cast [hw] at e'
  field_simp
  linear_combination e'

end GlobalTheory.GenSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicTowerFixesEpsilonRootsResGammaTrivial
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

namespace GlobalTheory.Decompl

theorem resΓ_eq_one_of_chi {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K LL : FinExt l}
    (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K)))
    (g : ↥(GK K)) (h1 : P.χQ g = 1) : W.resΓ g = 1 := by
  apply W.χΓ_inj
  rw [map_one W.χΓ]
  apply Units.ext
  apply Subtype.ext
  have h3 := W.χΓ_res g
  rw [P.PD_χ, h1, Units.val_one, map_one] at h3
  exact h3

theorem hinf_fixes_εroot_and_resΓ_eq_one : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l),
    (∀ g ∈ Hinf K, ∀ j : ℕ, AI.actT g (AI.εroot j) = AI.εroot j) ∧
    ∀ (s : ℕ) (LL : FinExt l), Good K s LL → ∀ (W : Wach P K LL), ∀ g ∈ Hinf K,
      ∃ hg : g ∈ GK K, W.resΓ ⟨g, hg⟩ = 1 := by
  intro l _ P AI K
  have hχ : ∀ g ∈ Hinf K, P.χQ g = 1 := fun g hg =>
    ((GlobalTheory.Cyc.cyc_basic l P.χQ P.χQ_cyc).2.2 K g
      (IntermediateField.fixingSubgroup_antitone (show K0 K ≤ Kinf K from le_sup_left) hg)).2.1 hg
  refine ⟨fun g hg j => ?_, fun s LL hG W g hg => ?_⟩
  · have := GlobalTheory.ExpImage.actT_εroot_eq_pow l P AI g 1 (by simp [hχ g hg]) j
    rwa [pow_one] at this
  · have h1 : Ks K s ≤ Kinf K :=
      sup_le_sup_left (IntermediateField.adjoin.mono _ _ _
        fun (x : Om l) (hx : x ^ (l ^ s) = 1) => (⟨s, hx⟩ : ∃ j : ℕ, x ^ (l ^ j) = 1)) _
    have h2 : K.1 ≤ Ks K s := hG.2.2.1
    have hgK : g ∈ GK K := IntermediateField.fixingSubgroup_antitone (h2.trans h1) hg
    exact ⟨hgK, resΓ_eq_one_of_chi P W ⟨g, hgK⟩ (hχ g hg)⟩

end GlobalTheory.Decompl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamDieudonneSpansTensorDeRhamPeriods
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.Per.DeRhamSpan

open GlobalTheory.DeRhamCompare
open GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual (mulPeriod)

theorem span_of_invariant {G E M : Type} [CommRing E] (hE : IsField E) [AddCommGroup M]
    [Module E M] [Module.Finite E M] {n : ℕ} (hn : n = finrank E M)
    (σ : G → (E →+* E)) (ρ : G → (M →+ M))
    (hρ : ∀ g (e : E) (m : M), ρ g (e • m) = σ g e • ρ g m) (v : Fin n → M)
    (hv : ∀ g i, ρ g (v i) = v i)
    (hind : ∀ c : Fin n → E, (∀ g i, σ g (c i) = c i) → ∑ i, c i • v i = 0 → ∀ i, c i = 0)
    (y : M) : ∃ c : Fin n → E, ∑ i, c i • v i = y := by
  letI := hE.toField
  have h := GlobalTheory.Per.linearIndependent_of_invariant G E M (Fin n) σ ρ hρ v hv hind
  have h2 := h.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin]; exact hn)
  exact (Submodule.mem_span_range_iff_exists_fun E).1 (h2 ▸ Submodule.mem_top)

section General

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem finrank_DdRK [FiniteDimensional Qp LL] [FiniteDimensional LL V] (h : IsDR PD ρ) :
    FiniteDimensional K (DdRK PD ρ) ∧ finrank K (DdRK PD ρ) = finrank Qp V := by
  have := PD.finK
  have := finite_DdR PD ρ h
  have : FiniteDimensional Qp V := Module.Finite.trans LL V
  have : FiniteDimensional Qp (DdR PD ρ) := Module.Finite.trans LL _
  let ε : DdR PD ρ ≃ₗ[Qp] DdRK PD ρ :=
    { toFun := fun x => toK PD ρ x x.2
      invFun := fun y => ⟨(TensorProduct.comm Qp V BdR).symm y, y.2⟩
      map_add' := fun x y => Subtype.ext (by simp [toK])
      map_smul' := fun a x => Subtype.ext (by simp [toK])
      left_inv := fun x => Subtype.ext (by simp [toK])
      right_inv := fun x => Subtype.ext (by simp [toK]) }
  have : FiniteDimensional Qp (DdRK PD ρ) := ε.finiteDimensional
  refine ⟨Module.Finite.of_restrictScalars_finite Qp K _, ?_⟩
  have h1 := Module.finrank_mul_finrank Qp K (DdRK PD ρ)
  have h2 := Module.finrank_mul_finrank Qp LL (DdR PD ρ)
  have h3 := Module.finrank_mul_finrank Qp LL V
  rw [← ε.finrank_eq, ← h2, h, mul_left_comm, h3] at h1
  exact Nat.eq_of_mul_eq_mul_left finrank_pos h1

theorem span_of_isField [FiniteDimensional Qp LL] [FiniteDimensional LL V] (hF : IsField BdR)
    (h : IsDR PD ρ) (y : V ⊗[Qp] BdR) :
    ∃ (m : ℕ) (b : Fin m → BdR) (d : Fin m → V ⊗[Qp] BdR), (∀ i, d i ∈ DdR PD ρ) ∧
      y = ∑ i, mulPeriod (Qp := Qp) (LL := LL) (V := V) (b i) (d i) := by
  have : FiniteDimensional Qp V := Module.Finite.trans LL V
  have := hF.nontrivial
  obtain ⟨_, hr⟩ := finrank_DdRK PD ρ h
  let e := Module.finBasisOfFinrankEq K _ hr
  let σ : G → BdR ⊗[Qp] V →ₗ[Qp] BdR ⊗[Qp] V := fun g =>
    TensorProduct.map (((PD.actdR g).toAlgHom.toLinearMap).restrictScalars Qp) ((ρ g).restrictScalars Qp)
  have hσ : ∀ g (b : BdR) w, σ g (b • w) = PD.actdR g b • σ g w := by
    intro g b w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul c v => simp [σ, TensorProduct.smul_tmul']
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  have hc : ∀ g x, σ g (TensorProduct.comm Qp V BdR x) =
      TensorProduct.comm Qp V BdR (actVdR PD ρ g x) := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c v => simp [σ, actVdR]
    | add x y hx hy => simp only [map_add, hx, hy]
  obtain ⟨b, hb⟩ := span_of_invariant (M := BdR ⊗[Qp] V) hF (n := finrank Qp V)
    Module.finrank_baseChange.symm
    (fun g => (PD.actdR g : BdR →+* BdR)) (fun g => (σ g).toAddMonoidHom) hσ
    (fun k => (e k : BdR ⊗[Qp] V))
    (fun g k => by
      have h1 := hc g ((TensorProduct.comm Qp V BdR).symm (e k))
      rw [(mem_DdR PD ρ _).1 (e k).2 g, LinearEquiv.apply_symm_apply] at h1
      exact h1)
    (fun c hcg hsum k => by
      choose a ha using fun p => PD.invdR (c p) fun g => hcg g p
      have h1 : ∑ i, a i • e i = 0 := by
        apply Subtype.ext
        rw [Submodule.coe_zero, ← hsum]
        simp only [Submodule.coe_sum, Submodule.coe_smul, ← ha, algebraMap_smul]
      rw [← ha, Fintype.linearIndependent_iff.1 e.linearIndependent a h1 k, map_zero])
    (TensorProduct.comm Qp V BdR y)
  refine ⟨_, b, fun k => (TensorProduct.comm Qp V BdR).symm (e k), fun k => (e k).2, ?_⟩
  apply (TensorProduct.comm Qp V BdR).injective
  simp only [map_sum, comm_mp, LinearEquiv.apply_symm_apply, hb]

end General

theorem tied_deRham_span : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), IsDR (P.PD K) ρ → ∀ y : V ⊗[ℚ_[l]] P.R.BdR, ∃ (m : ℕ) (b : Fin m → P.R.BdR) (d : Fin m → V ⊗[ℚ_[l]] P.R.BdR), (∀ i, d i ∈ DdR (P.PD K) ρ) ∧ y = ∑ i, AlgebraTensorModule.map (LinearMap.id : V →ₗ[↥LL.1] V) (LinearMap.mulLeft ℚ_[l] (b i)) (d i) := by
  intro l _ P AI T K LL V _ _ _ _ _ ρ h y
  haveI := LL.2
  exact span_of_isField (P.PD K) ρ (GlobalTheory.Per.TiedField.tied_field l P AI T).1 h y

end GlobalTheory.Per.DeRhamSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecompletionFrameOfMatrixFormStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.decompletion_frame_of_matrix_form : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ) (K : FinExt l) (m d : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (D : Matrix (Fin d) (Fin d) (PadicComplex l)) (g : GQ l), IsActC act → IsGen χ K m g → (∀ i j, ContinuousOn (fun σ => M σ i j) (Gj K m)) → (∀ σ ∈ Gj K m, ∀ τ ∈ Gj K m, M (σ * τ) = M σ * M τ) → (∀ σ ∈ Gj K m, ∀ τ ∈ Gj K m, (M τ).map (act σ) = M τ) → (∀ i j, ‖D i j‖ ≤ 1) → (∃ X : Matrix (Fin d) (Fin d) (PadicComplex l), (∀ i j, ‖X i j‖ ≤ 1) ∧ D * X = (l : PadicComplex l) • (1 : Matrix (Fin d) (Fin d) (PadicComplex l))) → (∀ σ ∈ Gj K m, ∃ X : Matrix (Fin d) (Fin d) (PadicComplex l), (∀ i j, X i j ∈ intC (Ks K m)) ∧ M σ * D.map (act σ) = D * X) → (∀ σ ∈ Hinf K, M σ * D.map (act σ) = D) → (∃ X : Matrix (Fin d) (Fin d) (PadicComplex l), (∀ i j, ‖X i j‖ < rho1 l) ∧ M g * D.map (act g) - D = D * X) → ∃ U : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l), IsDec act χ K m M D U g := by
  first | exact @GlobalTheory.Cyc.Decomp.isDec_of_matrix | exact GlobalTheory.Cyc.Decomp.isDec_of_matrix | (intros; apply GlobalTheory.Cyc.Decomp.isDec_of_matrix <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DetCharacterIrreducibleLabel
section
noncomputable section

namespace GlobalTheory.GLq.LabelDet

open GlobalTheory.GLq GlobalTheory.GLp Formalism.MainNotions.ArithmeticCylinders Formalism.CyclotomicNorms Polynomial
open scoped Classical ComplexOrder

variable {g : ℕ} [hg : Fact g.Prime]

open Polynomial in
open scoped Classical ComplexOrder in
variable {g : ℕ} [hg : Fact g.Prime] in

theorem _root_.GlobalTheory.GLq.LabelDet.isIrr_hom {G : Type} [Group G] [Fintype G] (φ : G →* ℂˣ) :
    _root_.GlobalTheory.GLq.IsIrr (fun x : G => ((φ x : ℂˣ) : ℂ)) := by
  have hchar : ∀ x : G, (FDRep.of (_root_.GlobalTheory.GLp.Model.chRep φ)).character x = φ x := by
    intro x
    have : _root_.GlobalTheory.GLp.Model.chRep φ x = (φ x : ℂ) • LinearMap.id := by
      ext; simp [_root_.GlobalTheory.GLp.Model.chRep_apply]
    simp [FDRep.character, FDRep.of_ρ, this]
  refine ⟨FDRep.of (_root_.GlobalTheory.GLp.Model.chRep φ), ?_, hchar⟩
  rw [FDRep.simple_iff_char_is_norm_one]
  simp [hchar, Nat.card_eq_fintype_card]

theorem level_pos : 0 < g ^ 1 - 1 :=
  Nat.sub_pos_of_lt (Nat.one_lt_pow one_ne_zero hg.out.one_lt)

open Polynomial in
open scoped Classical ComplexOrder in
variable {g : ℕ} [hg : Fact g.Prime] in
theorem _root_.GlobalTheory.GLq.LabelDet.theta_gen_pow (L : _root_.GlobalTheory.GLq.LabelDatum g) {x : _root_.Formalism.CyclotomicNorms.Fbar g}
    (hx : x ^ (g ^ 1 - 1) = 1) (n : ℕ) :
    _root_.GlobalTheory.GLq.thetaOf L 1 x (L.gen 1 ^ n) =
      L.teich x ^ n :=
  _root_.GlobalTheory.GLq.Model.thetaOf_gen_pow L one_pos hx n

open Polynomial in
open scoped Classical ComplexOrder in
variable {g : ℕ} [hg : Fact g.Prime] in

theorem _root_.GlobalTheory.GLq.LabelDet.gen_one_mem (L : _root_.GlobalTheory.GLq.LabelDatum g) :
    ∃ u : (ZMod g)ˣ, algebraMap (ZMod g) (_root_.Formalism.CyclotomicNorms.Fbar g) u = L.gen 1 := by
  obtain ⟨u, hu, -⟩ := _root_.GlobalTheory.GLp.Model.exists_gen L
  exact ⟨u, hu⟩

open Polynomial in
open scoped Classical ComplexOrder in
variable {g : ℕ} [hg : Fact g.Prime] in

theorem _root_.GlobalTheory.GLq.LabelDet.det_inPar (a b : ℕ) (M : _root_.GlobalTheory.GLq.Mt g (a + b))
    (h : _root_.GlobalTheory.GLq.InPar a M) :
    M.det = (_root_.GlobalTheory.GLq.tl a M).det * (_root_.GlobalTheory.GLq.br a b M).det := by
  have key : M.submatrix finSumFinEquiv finSumFinEquiv = Matrix.fromBlocks (_root_.GlobalTheory.GLq.tl a M)
      (M.submatrix (Fin.castAdd b) (Fin.natAdd a)) 0 (_root_.GlobalTheory.GLq.br a b M) := by
    ext (i | i) (j | j)
    · show M (Fin.castAdd b i) (Fin.castAdd b j) = _root_.Formalism.MainNotions.ArithmeticCylinders.entN M i j
      have hi := i.isLt
      have hj := j.isLt
      unfold _root_.Formalism.MainNotions.ArithmeticCylinders.entN
      rw [dif_pos ⟨by omega, by omega⟩]
      rfl
    · simp
    · exact h _ _ (by simp) (by simp)
    · simp [_root_.GlobalTheory.GLq.br, _root_.Formalism.MainNotions.ArithmeticCylinders.entN, Fin.natAdd]
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv M, key, Matrix.det_fromBlocks_zero₂₁]

open Polynomial in
open scoped Classical ComplexOrder in
variable {g : ℕ} [hg : Fact g.Prime] in
theorem _root_.GlobalTheory.GLq.LabelDet.det_toG {n : ℕ} (M : _root_.GlobalTheory.GLq.Mt g n) (h : M.det ≠ 0) :
    ((Matrix.GeneralLinearGroup.det (_root_.GlobalTheory.GLq.toG M) : (ZMod g)ˣ) : ZMod g) = M.det := by
  unfold _root_.GlobalTheory.GLq.toG
  rw [dif_pos ((Matrix.isUnit_iff_isUnit_det M).mpr (isUnit_iff_ne_zero.mpr h))]
  simp [Matrix.GeneralLinearGroup.val_det_apply]

open Polynomial in
open scoped Classical ComplexOrder in
variable {g : ℕ} [hg : Fact g.Prime] in
theorem _root_.GlobalTheory.GLq.LabelDet.det_par (a b : ℕ) (p : _root_.GlobalTheory.GLq.Gn g (a + b))
    (h : _root_.GlobalTheory.GLq.InPar a (p : _root_.GlobalTheory.GLq.Mt g (a + b))) :
    Matrix.GeneralLinearGroup.det p =
      Matrix.GeneralLinearGroup.det (_root_.GlobalTheory.GLq.toG (_root_.GlobalTheory.GLq.tl a
        (p : _root_.GlobalTheory.GLq.Mt g (a + b)))) *
      Matrix.GeneralLinearGroup.det (_root_.GlobalTheory.GLq.toG (_root_.GlobalTheory.GLq.br a b
        (p : _root_.GlobalTheory.GLq.Mt g (a + b)))) := by
  have hdet := _root_.GlobalTheory.GLq.LabelDet.det_inPar a b _ h
  have hp := (Matrix.GeneralLinearGroup.det p).ne_zero
  rw [Matrix.GeneralLinearGroup.val_det_apply] at hp
  rw [hdet] at hp
  obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp hp
  apply Units.ext
  rw [Units.val_mul, _root_.GlobalTheory.GLq.LabelDet.det_toG _ h1, _root_.GlobalTheory.GLq.LabelDet.det_toG _ h2,
    Matrix.GeneralLinearGroup.val_det_apply, ← hdet]

open Polynomial in
open scoped Classical ComplexOrder in
variable {g : ℕ} [hg : Fact g.Prime] in
theorem _root_.GlobalTheory.GLq.LabelDet.toG_one {n : ℕ} : _root_.GlobalTheory.GLq.toG (1 : _root_.GlobalTheory.GLq.Mt g n) = 1 := by
  unfold _root_.GlobalTheory.GLq.toG
  rw [dif_pos isUnit_one]
  exact Units.ext (by simp)

theorem inPar_one (a n : ℕ) : InPar a (1 : Mt g n) := fun i j h1 h2 =>
  Matrix.one_apply_ne (by rintro rfl; omega)

theorem br_one (a b : ℕ) : br a b (1 : Mt g (a + b)) = 1 := by
  ext i j
  simp [br, entN, Matrix.one_apply, Fin.ext_iff]

theorem tl_one (a b : ℕ) : tl a (1 : Mt g (a + b)) = 1 := by
  ext i j
  have hi : (i : ℕ) < a + b := by omega
  have hj : (j : ℕ) < a + b := by omega
  simp [tl, entN, Matrix.one_apply, Fin.ext_iff, hi, hj]

def PosMul (χ : (ZMod g)ˣ →* ℂˣ) {n : ℕ} (F : Gn g n → ℂ) : Prop :=
  ∃ r : Gn g n → ℂ, (∀ x, 0 ≤ r x) ∧ 0 < r 1 ∧
    ∀ x, F x = r x * ((χ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ)

end GlobalTheory.GLq.LabelDet
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeterminantLemmaDiscreteValuationRingQuotientLenStatement
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.determinantLemma_discreteValuationRing_quotientLength_bound : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (A : Type) [Ring A] [Algebra O A] (J : Type) [Fintype J] (d : J → ℕ) (ψ : ∀ j, A →ₐ[O] Matrix (Fin (d j)) (Fin (d j)) O), (∀ j, Function.Surjective (ψ j)) → ∀ (g : ℕ) (Rel : Submodule A (Fin g → A)) (I : Ideal O), (∀ (n : ℕ) (θ : Fin n → Fin g → Fin g → A), (∀ k p, θ k p ∈ Rel) → ∀ m : Fin n →₀ ℕ, MvPolynomial.coeff m (∏ j, Matrix.det (Matrix.of fun (pa qb : Fin g × Fin (d j)) => ∑ k, (MvPolynomial.X k : MvPolynomial (Fin n) O) * MvPolynomial.C (ψ j (θ k pa.1 qb.1) pa.2 qb.2))) ∈ I) → Module.length O (O ⧸ I) ≤ ∑ j, Module.length O ↥(⨅ θ ∈ Rel, LinearMap.ker (∑ q : Fin g, (matKO (ψ j (θ q))).comp (LinearMap.proj q : (Fin g → KOG O (d j)) →ₗ[O] KOG O (d j)))) := by
  first | exact @GlobalTheory.DetGen.length_quot_le_sum_length | exact GlobalTheory.DetGen.length_quot_le_sum_length | (intros; apply GlobalTheory.DetGen.length_quot_le_sum_length <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleEmbeddingFrobeniusGaloisCompatStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleEmbedding_frobenius_galois_compat : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (W : Wach P K LL) (E : EtSit P AI K s LL h W), (∀ e, E.tie.ioE (W.φE e) = φRW LL (E.tie.ioE e)) ∧ (∀ g : ↥(GK K), W.resΓ g = 1 → ∀ e, AI.gRW LL (g : GQ l) (E.tie.ioE e) = E.tie.ioE e) ∧ E.tie.ioE (algebraMap (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) W.EE letπ) = piR AI LL s ∧ (∀ e, ∃ c : ℕ, NearPi AI LL s 0 (piR AI LL s ^ c * E.tie.ioE e)) := by
  first | exact @GlobalTheory.Decompl.ioE_compat | exact GlobalTheory.Decompl.ioE_compat | (intros; apply GlobalTheory.Decompl.ioE_compat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EveryGeneratorH2Twist
section
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.FunctorialityH2

namespace GlobalTheory.FunctorialityH2

theorem bijective_phi_quot_pow : ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O] {G : Type} [Group G] [TopologicalSpace G], Formalism.GaloisCohomology.LocalTateDualityK → FiniteDimensional ℚ_[p] K → PadicCoeff p O → ∀ (i : G ≃ₜ* GK p K) {ε : G →* Oˣ}, IsCyc p K (carry i ε) → ∀ z : H2 (twist ε O), Function.Bijective (fun a : O => a • z) → ∀ k : ℕ, Function.Bijective (phi ε z (O ⧸ IsLocalRing.maximalIdeal O ^ k)) := by
  intro p _ K O _ _ _ _ _ G _ _ hT hK hO i ε hε z hz k
  haveI : ContinuousMul G := ⟨by
    have h : (fun q : G × G => q.1 * q.2) = fun q => i.symm (i q.1 * i q.2) := by
      funext q; simp
    rw [h]
    exact i.symm.continuous.comp
      ((i.continuous.comp continuous_fst).mul (i.continuous.comp continuous_snd))⟩
  have hinj := GlobalTheory.T.phi_injective_quotient_H2 hO (GlobalTheory.T.continuous_cyclotomic_character_localGalois hO i hε) z hz k
  obtain ⟨_, hcard⟩ := GlobalTheory.T.finite_H2_twist_quotient_pow_and_card_le hT hK hO i hε k
  exact hinj.bijective_of_nat_card_le hcard

end GlobalTheory.FunctorialityH2
end

