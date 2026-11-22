import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeOfSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0037
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0252
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0247
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0250
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0243
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0236
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.T2SpaceLocalLatticeRepresentationSpace
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0235
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteClassesSubsetAdmissibleOfGoodO
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0249
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0248
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0007
import Formalism.PeriodIntegrals.ArtSch
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0002
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0005

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWachModuleGeneratorReduction
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct

namespace GlobalTheory.RedFun

theorem exists_extend_of_dense {A E F : Type} [CommRing A] [CommRing E] [CommRing F] (ι : A →+* E) (f : A →+* F)
    (π P : A) (hf : IsUnit (f π)) (hP : f P = 0)
    (hd : ∀ e : E, ∃ (a : A) (m : ℕ) (y : E), e * ι π ^ m = ι a + ι P * y)
    (hs : ∀ (a : A) (y : E), ι a = ι P * y → ∃ b, a = P * b) :
    ∃ g : E →+* F, (∀ a, g (ι a) = f a) := by
  first
  | exact @_root_.GlobalTheory.RelationExtension.exists_extension
  | exact _root_.GlobalTheory.RelationExtension.exists_extension
  | (apply _root_.GlobalTheory.RelationExtension.exists_extension <;> assumption)
  | (intros; apply _root_.GlobalTheory.RelationExtension.exists_extension <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RelationExtension.exists_extension <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RelationExtension.exists_extension ..)

theorem exists_letter_reduction : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n) {k : Type} [Field k] [Algebra O k] (lam : O), Function.Surjective (algebraMap O k) → (∀ x, algebraMap O k x = 0 ↔ lam ∣ x) → ((PD.p : ℕ) : k) = 0 → ∃ p : ZMod n → (W.EE →+* k⸨X⸩), (∀ i (a : LetA O n), p i (algebraMap (LetA O n) W.EE a) = ((PowerSeries.map (algebraMap O k) (a i) : k⟦X⟧) : k⸨X⸩)) ∧ (∀ i, Function.Surjective (p i)) ∧ ∀ i e, p i e = 0 → ∃ e', algebraMap (LetA O n) W.EE (letE i) * e = algebraMap O W.EE lam * e' := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL O _ _ _ _ _ v n W k _ _ lam hsurj hker hp
  let f : ZMod n → (LetA O n →+* k⸨X⸩) := fun i =>
    (algebraMap k⟦X⟧ k⸨X⸩).comp ((PowerSeries.map (algebraMap O k)).comp (Pi.evalRingHom (fun _ => O⟦X⟧) i))
  have hf : ∀ i (a : LetA O n), f i a = algebraMap k⟦X⟧ k⸨X⸩ (PowerSeries.map (algebraMap O k) (a i)) :=
    fun _ _ => rfl
  have hX : ∀ i, f i letπ = algebraMap k⟦X⟧ k⸨X⸩ PowerSeries.X := fun i => by
    rw [hf, letπ, PowerSeries.map_X]
  have hu : IsUnit (algebraMap k⟦X⟧ k⸨X⸩ PowerSeries.X) :=
    IsLocalization.map_units k⸨X⸩ (⟨PowerSeries.X, Submonoid.mem_powers _⟩ : Submonoid.powers (PowerSeries.X : k⟦X⟧))
  have hP : ∀ i, f i (PD.p : LetA O n) = 0 := fun i => by
    rw [map_natCast, ← map_natCast (algebraMap k k⸨X⸩), hp, map_zero]
  have hd : ∀ e : W.EE, ∃ (a : LetA O n) (m : ℕ) (y : W.EE), e * algebraMap (LetA O n) W.EE letπ ^ m =
      algebraMap (LetA O n) W.EE a + algebraMap (LetA O n) W.EE (PD.p : LetA O n) * y := by
    intro e
    obtain ⟨a, m, h⟩ := W.EE_dense e 1
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 h
    refine ⟨a, m, y, ?_⟩
    rw [map_pow, pow_one] at hy
    rw [map_natCast]
    linear_combination -hy
  have hs : ∀ (a : LetA O n) (y : W.EE), algebraMap (LetA O n) W.EE a =
      algebraMap (LetA O n) W.EE (PD.p : LetA O n) * y → ∃ b, a = (PD.p : LetA O n) * b := by
    intro a y h
    have := W.EE_sat a 1 (Ideal.mem_span_singleton'.2 ⟨y, by rw [h, map_natCast, pow_one, mul_comm]⟩)
    simpa using this
  choose p hpa using fun i => exists_extend_of_dense (algebraMap (LetA O n) W.EE) (f i) letπ (PD.p : LetA O n)
    (by rw [hX]; exact hu) (hP i) hd hs
  obtain ⟨u, hπ⟩ := W.EE_π.exists_right_inv
  refine ⟨p, fun i a => hpa i a, fun i c => ?_, fun i e he => ?_⟩
  · obtain ⟨⟨s, ⟨_, m, rfl⟩⟩, h⟩ := IsLocalization.surj (Submonoid.powers (PowerSeries.X : k⟦X⟧)) c
    obtain ⟨t, rfl⟩ := PowerSeries.map_surjective _ hsurj s
    refine ⟨algebraMap (LetA O n) W.EE (fun _ => t) * u ^ m, ?_⟩
    have h1 := congrArg (p i) hπ
    rw [map_mul, hpa, hX, map_one] at h1
    simp only [map_pow] at h
    rw [map_mul, hpa, hf, map_pow, ← h, mul_assoc, ← mul_pow, h1, one_pow, mul_one]
  · obtain ⟨a, m, y, h⟩ := hd e
    have h1 := congrArg (p i) h
    rw [map_mul, he, zero_mul, map_add, map_mul, hpa, hpa, hP, zero_mul, add_zero, hf] at h1
    have h2 : PowerSeries.map (algebraMap O k) (a i) = 0 :=
      (IsFractionRing.injective k⟦X⟧ k⸨X⸩) (by rw [map_zero]; exact h1.symm)
    have h3 : ∀ j, ∃ d, PowerSeries.coeff j (a i) = lam * d := fun j => (hker _).1 (by
      have := congrArg (PowerSeries.coeff j) h2
      simpa using this)
    choose d hd' using h3
    obtain ⟨c, hc⟩ := (hker (PD.p : O)).1 (by rw [map_natCast, hp])
    have h4 : letE i * a = algebraMap O (LetA O n) lam * (letE i * fun _ => PowerSeries.mk d) := by
      funext j
      by_cases hj : j = i
      · subst hj
        ext l
        simp [letE, hd']
      · simp [letE, hj]
    have h5 : (PD.p : LetA O n) = algebraMap O (LetA O n) lam * algebraMap O (LetA O n) c := by
      rw [← map_mul, ← hc, map_natCast]
    have h6 := congrArg (algebraMap (LetA O n) W.EE) h4
    rw [h5] at h
    simp only [map_mul] at h h6
    rw [IsScalarTower.algebraMap_apply O (LetA O n) W.EE]
    have h7 : algebraMap (LetA O n) W.EE letπ ^ m * u ^ m = 1 := by rw [← mul_pow, hπ, one_pow]
    refine ⟨(algebraMap (LetA O n) W.EE (letE i) * algebraMap (LetA O n) W.EE (fun _ => PowerSeries.mk d) +
      algebraMap (LetA O n) W.EE (letE i) * algebraMap (LetA O n) W.EE (algebraMap O (LetA O n) c) * y) * u ^ m, ?_⟩
    linear_combination (algebraMap (LetA O n) W.EE (letE i) * u ^ m) * h + u ^ m * h6 -
      (algebraMap (LetA O n) W.EE (letE i) * e) * h7

end GlobalTheory.RedFun
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteDimensionalKsOfGood
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
open scoped TensorProduct

namespace GlobalTheory.Cyc.CrysDeRham

variable {l : ℕ} [Fact l.Prime]

theorem finiteDimensional_Ks_of_good {K LL : FinExt l} {s : ℕ} (h : Good K s LL) :
    FiniteDimensional ℚ_[l] ↥(Ks K s) := by
  have hle : Ks K s ≤ LL.1 := fun x hx => h.2.2.2 (Ks K s).val ⟨x, hx⟩
  have := LL.2
  exact FiniteDimensional.of_injective (IntermediateField.inclusion hle).toLinearMap
    (IntermediateField.inclusion_injective hle)

theorem apply_mem_Ks (K : FinExt l) (s : ℕ) :
    ∀ g ∈ GK K, ∀ x ∈ Ks K s, g x ∈ Ks K s := by
  intro g hg
  have key : Ks K s ≤ (Ks K s).comap (g : Om l →ₐ[ℚ_[l]] Om l) := by
    refine sup_le ?_ ?_
    · intro x hx
      have h1 : g x = x := hg ⟨x, hx.1⟩
      change g x ∈ Ks K s
      rw [h1]
      exact (le_sup_left : K0 K ≤ Ks K s) hx
    · rw [IntermediateField.adjoin_le_iff]
      intro x hx
      change g x ∈ Ks K s
      apply (le_sup_right : _ ≤ Ks K s)
      apply IntermediateField.subset_adjoin
      have hx' : x ^ (l ^ s) = 1 := hx
      change (g x) ^ (l ^ s) = 1
      rw [← map_pow, hx', map_one]
  intro x hx
  exact key hx

noncomputable def restrictRep {K E LL : FinExt l} (hle : K.1 ≤ E.1)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) : GRep ↥(GK E) ℚ_[l] ↥LL.1 ↥(OL LL) where
  V := T.V
  modO := T.modO
  towO := T.towO
  ρ := T.ρ.comp (Subgroup.inclusion (GK_le hle))
  cont x := (T.cont x).comp (continuous_inclusion (GK_le hle))

theorem isDR_of_restrict (P : LocPrime l) {K E LL : FinExt l} (hle : K.1 ≤ E.1)
    (hs : ∀ g ∈ GK K, ∀ x ∈ E.1, g x ∈ E.1) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL))
    (h : IsDR (P.PD E) (restrictRep hle T).ρ) : IsDR (P.PD K) T.ρ :=
  GlobalTheory.T.isDeRham_of_restrict_galois_descent l P K E LL (GK_le hle) hle hs T.V T.ρ h

set_option maxHeartbeats 1600000 in

theorem isDR_of_isCrysOn : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc), adm7 D → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := sit D.loc HW l (D.locA l) K s LL h; ∀ (T : LocLat S.G S.Qp S.LL S.O), IsCrysOn S S.W.GKs T → IsDR S.PD T.ρ := by
  intro D HW hF l _ K s LL h S T hT
  let E : FinExt l := ⟨Ks K s, finiteDimensional_Ks_of_good h⟩
  have hle : K.1 ≤ E.1 := h.2.2.1
  have h1 := isCrys_Ks_of_finrank l (D.loc l) K s LL _ ((HW l).W K s LL h) ((HW l).W_s K s LL h)
    E rfl hle T hT
  have h2 := (hF l E ↥LL.1 ↥(OL LL) (GlobalTheory.LocalIntegers.goodO_integers l LL)
    (restrictRep hle T)).2.2 h1
  exact isDR_of_restrict (D.loc l) hle (apply_mem_Ks K s) T h2

end GlobalTheory.Cyc.CrysDeRham
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteFinrankOfLocalizes
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

set_option autoImplicit false

namespace GlobalTheory.H1Rank

theorem pow_smul_mem_lattice : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (x : A.V), ∃ n : ℕ, ((l : ℕ) : O) ^ n • x ∈ LA.T := by
  intro l _ K LL _ _ _ O _ _ hG A LA x
  obtain ⟨-, -, hmod, htop, hopen⟩ := hG
  haveI := hmod
  haveI := htop
  have hT : IsOpen (LA.T : Set A.V) := GlobalTheory.Cyc.isOpen_of_fg_of_span_eq_top hopen LA.T LA.fg LA.span
  haveI := IsModuleTopology.toContinuousSMul LL A.V
  have h1 : Filter.Tendsto (fun n : ℕ => (l : ℚ_[l]) ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one Padic.norm_p_lt_one
  have h2 : Filter.Tendsto (fun n : ℕ => algebraMap ℚ_[l] LL ((l : ℚ_[l]) ^ n) • x) Filter.atTop (nhds 0) := by
    have := ((GlobalTheory.GoodCoeff.continuous_algebraMap_padic (l := l) (LL := LL)).tendsto 0).comp h1
    rw [map_zero] at this
    simpa using this.smul_const x
  have h3 : ∀ n : ℕ, ((l : ℕ) : O) ^ n • x = algebraMap ℚ_[l] LL ((l : ℚ_[l]) ^ n) • x := by
    intro n
    rw [← algebraMap_smul LL, map_pow, map_pow, map_natCast, map_natCast]
  obtain ⟨n, hn⟩ := (h2.eventually (hT.mem_nhds LA.T.zero_mem)).exists
  exact ⟨n, by rw [h3]; exact hn⟩

end GlobalTheory.H1Rank

namespace GlobalTheory.H1Rank

theorem not_isUnit_l : ∀ (l : ℕ) [Fact l.Prime] (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ¬ IsUnit ((l : ℕ) : O) := by
  intro l _ LL _ _ _ O _ _ hG hu
  obtain ⟨u, hu⟩ := hu
  have hint := ((GlobalTheory.GoodCoeff.good_coeff_integers l LL O hG).1 (algebraMap O LL (↑u⁻¹ : O))).1 ⟨_, rfl⟩
  have hl0 : (l : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hx : algebraMap O LL (↑u⁻¹ : O) = algebraMap ℚ_[l] LL ((l : ℚ_[l])⁻¹) := by
    have h1 : algebraMap O LL (↑u⁻¹ : O) * algebraMap O LL (u : O) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    have h2 : algebraMap O LL (u : O) = algebraMap ℚ_[l] LL (l : ℚ_[l]) := by
      rw [hu, map_natCast, map_natCast]
    rw [h2] at h1
    calc algebraMap O LL (↑u⁻¹ : O)
        = algebraMap O LL (↑u⁻¹ : O) * (algebraMap ℚ_[l] LL (l : ℚ_[l]) * algebraMap ℚ_[l] LL ((l : ℚ_[l])⁻¹)) := by
          rw [← map_mul, mul_inv_cancel₀ hl0, map_one, mul_one]
      _ = algebraMap ℚ_[l] LL ((l : ℚ_[l])⁻¹) := by rw [← mul_assoc, h1, one_mul]
  rw [hx] at hint
  obtain ⟨p, hpm, hp⟩ := hint
  have hp' : Polynomial.eval₂ (algebraMap ℤ_[l] ℚ_[l]) ((l : ℚ_[l])⁻¹) p = 0 := by
    apply (algebraMap ℚ_[l] LL).injective
    rw [map_zero, Polynomial.hom_eval₂]
    exact hp
  have hI : IsIntegral ℤ_[l] ((l : ℚ_[l])⁻¹) := ⟨p, hpm, hp'⟩
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 hI
  have h1 : ‖(z : ℚ_[l])‖ ≤ 1 := PadicInt.norm_le_one z
  have h3 : algebraMap ℤ_[l] ℚ_[l] z = (z : ℚ_[l]) := rfl
  rw [← h3, hz, norm_inv, Padic.norm_p, inv_inv] at h1
  have : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  linarith
end GlobalTheory.H1Rank

namespace GlobalTheory.H1Rank

theorem finite_finrank_of_localizes : ∀ (O LL M N : Type) [CommRing O] [IsDomain O] [Field LL] [Algebra O LL] [IsFractionRing O LL] [AddCommGroup M] [Module O M] [Module.Finite O M] [AddCommGroup N] [Module LL N] [Module O N] [IsScalarTower O LL N] (f : M →ₗ[O] N) (t : O), t ≠ 0 → (∀ y : N, ∃ n : ℕ, ∃ x : M, f x = t ^ n • y) → (∀ x : M, f x = 0 → ∃ n : ℕ, t ^ n • x = 0) → Module.Finite LL N ∧ finrank LL N = finrank O M := by
  intro O LL M N _ _ _ _ _ _ _ _ _ _ _ _ f t ht hs hk
  have htn : ∀ n : ℕ, t ^ n ∈ nonZeroDivisors O := fun n => pow_mem (mem_nonZeroDivisors_of_ne_zero ht) n
  haveI : IsLocalizedModule (nonZeroDivisors O) f :=
    { map_units := by
        intro s
        rw [Module.End.isUnit_iff]
        have ha : algebraMap O LL (s : O) ≠ 0 :=
          (map_ne_zero_iff _ (IsFractionRing.injective O LL)).2 (nonZeroDivisors.ne_zero s.2)
        have he : ∀ y : N, (algebraMap O (Module.End O N) (s : O)) y = algebraMap O LL (s : O) • y := fun y => by
          rw [Module.algebraMap_end_apply, algebraMap_smul]
        refine ⟨fun y z h => ?_, fun y => ⟨(algebraMap O LL (s : O))⁻¹ • y, ?_⟩⟩
        · rw [he, he] at h
          exact smul_right_injective N ha h
        · rw [he, smul_smul, mul_inv_cancel₀ ha, one_smul]
      surj := by
        intro y
        obtain ⟨n, x, hx⟩ := hs y
        exact ⟨(x, ⟨t ^ n, htn n⟩), hx.symm⟩
      exists_of_eq := by
        intro x₁ x₂ h
        obtain ⟨n, hn⟩ := hk (x₁ - x₂) (by rw [map_sub, h, sub_self])
        exact ⟨⟨t ^ n, htn n⟩, by rw [Submonoid.smul_def]; rw [smul_sub, sub_eq_zero] at hn; exact hn⟩ }
  refine ⟨Module.Finite.of_isLocalizedModule (nonZeroDivisors O) (Rₚ := LL) f, ?_⟩
  rw [IsLocalization.finrank_eq LL (nonZeroDivisors O) le_rfl, IsLocalizedModule.finrank_eq (nonZeroDivisors O) f le_rfl]
end GlobalTheory.H1Rank

namespace GlobalTheory.H1Rank

theorem pow_smul_mem_B1T : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ), ∀ c ∈ latticeCocycles LA, c ∈ B1 A.ρ → ∃ n : ℕ, ((l : ℕ) : O) ^ n • c ∈ latticeCoboundaries LA := by
  intro l _ K LL _ _ _ O _ _ hG A LA c _ hc
  obtain ⟨x, rfl⟩ := hc
  obtain ⟨n, hn⟩ := pow_smul_mem_lattice l K LL O hG A LA x
  exact ⟨n, _, hn, by rw [LinearMap.map_smul_of_tower]; rfl⟩

theorem pow_smul_mem_Z1T : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ), ∀ c ∈ continuousCocycles A.ρ, ∃ n : ℕ, ((l : ℕ) : O) ^ n • c ∈ latticeCocycles LA := by
  intro l _ K LL _ _ _ O _ _ hG A LA c hc
  haveI : CompactSpace ↥(GK K) := by
    haveI := K.2
    exact isCompact_iff_compactSpace.1 (IntermediateField.fixingSubgroup_isClosed K.1).isCompact
  have hG' := hG
  obtain ⟨-, -, hmod, htop, hopen⟩ := hG'
  haveI := hmod
  haveI := htop
  have hT : IsOpen (LA.T : Set A.V) := GlobalTheory.Cyc.isOpen_of_fg_of_span_eq_top hopen LA.T LA.fg LA.span
  let U : ℕ → Set A.V := fun n => (fun v : A.V => ((l : ℕ) : O) ^ n • v) ⁻¹' (LA.T : Set A.V)
  have hUo : ∀ n, IsOpen (U n) := by
    intro n
    refine hT.preimage ?_
    have : (fun v : A.V => ((l : ℕ) : O) ^ n • v) = fun v : A.V => algebraMap O LL (((l : ℕ) : O) ^ n) • v :=
      funext fun v => (algebraMap_smul LL _ v).symm
    rw [this]
    exact continuous_const_smul _
  have hUm : Monotone U := by
    refine monotone_nat_of_le_succ fun n v hv => ?_
    show ((l : ℕ) : O) ^ (n + 1) • v ∈ LA.T
    rw [pow_succ', mul_smul]
    exact LA.T.smul_mem _ hv
  have hcov : Set.range c ⊆ ⋃ n, U n := fun v _ => Set.mem_iUnion.2 (pow_smul_mem_lattice l K LL O hG A LA v)
  obtain ⟨n, hn⟩ := (isCompact_range hc.1).elim_directed_cover U hUo hcov hUm.directed_le
  refine ⟨n, ⟨(continuousCocycles A.ρ).smul_of_tower_mem _ hc, fun g _ => hn ⟨g, rfl⟩⟩⟩

end GlobalTheory.H1Rank

namespace GlobalTheory.H1Rank
section
variable {l : ℕ} [Fact l.Prime] {K : FinExt l} {LL : Type} [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] {O : Type} [CommRing O] [Algebra O LL]
  {A : GRep ↥(GK K) ℚ_[l] LL O} (LA : Lattice (O := O) A.ρ)

def incl : ↥(latticeCocycles LA) →ₗ[O] ↥(continuousCocycles A.ρ) where
  toFun c := ⟨c, c.2.1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def toH1V : LatticeCohomology LA →ₗ[O] H1V A.ρ :=
  Submodule.liftQ ((latticeCoboundaries LA).comap (latticeCocycles LA).subtype)
    ((((B1 A.ρ).comap (continuousCocycles A.ρ).subtype).mkQ.restrictScalars O).comp (incl LA)) (by
      intro c hc
      obtain ⟨x, -, hx⟩ := hc
      simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars,
        Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply]
      exact ⟨x, hx⟩)

theorem toH1V_mk (c : ↥(latticeCocycles LA)) :
    toH1V LA (Submodule.Quotient.mk c) = Submodule.Quotient.mk (incl LA c) := rfl
end
end GlobalTheory.H1Rank
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixedOfFixedByDeltaGammaLifts
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct
open Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.HerrClass

namespace GlobalTheory.RedDense

variable {l : ℕ} [Fact l.Prime]

theorem norm_pow_pred_sub_one_le {χ : GQ l →* ℚ_[l]ˣ} (hχ : IsCyc χ) (g : GQ l) :
    ‖(χ g : ℚ_[l]) ^ (l - 1) - 1‖ ≤ (l : ℝ) ^ (-((1 : ℕ) : ℤ)) := by
  let u : ℤ_[l] := ⟨(χ g : ℚ_[l]), hχ.norm_le_one g⟩
  have hu : IsUnit u := PadicInt.isUnit_iff.2 (hχ.norm_eq_one g)
  have h3 : PadicInt.toZMod (u ^ (l - 1) - 1) = 0 := by
    rw [map_sub, map_pow, map_one, ZMod.pow_card_sub_one_eq_one (hu.map _).ne_zero, sub_self]
  have h4 : u ^ (l - 1) - 1 ∈ Ideal.span {(l : ℤ_[l]) ^ 1} := by
    rw [pow_one, ← PadicInt.maximalIdeal_eq_span_p, ← PadicInt.ker_toZMod]
    exact h3
  have h5 := (PadicInt.norm_le_pow_iff_mem_span_pow _ 1).2 h4
  rw [PadicInt.norm_def] at h5
  exact h5

theorem card_and_dense {P : LocPrime l} (AI : LocAinf l P) {K LL : FinExt l} {s : ℕ} (h2 : l ≠ 2)
    (hK : K.1 ≤ Ks K s)
    (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))) :
    ¬ l ∣ W.DelF.card ∧ ∀ γ : W.Gam, (W.χΓ γ : ↥(OL LL)) = 1 + (l : ↥(OL LL)) →
      ∀ U : Subgroup ↥(GK K), IsClosed (U : Set ↥(GK K)) →
        (∀ g, (W.resΓ g ∈ W.DelF ∨ W.resΓ g = γ) → g ∈ U) → ∀ g, g ∈ U := by
  have hl : l.Prime := Fact.out
  have hχ : IsCyc P.χQ := P.χQ_cyc
  have ha : IsActC AI.actC := ⟨AI.actC_ext, AI.actC_norm⟩
  obtain ⟨-, -, hG⟩ := cyc_basic l P.χQ hχ
  have hH0 : ∀ x ∈ Hinf K, x ∈ (K0 K).fixingSubgroup := fun x hx y =>
    hx ⟨y.1, (le_sup_left : K0 K ≤ Kinf K) y.2⟩
  have hH : Hinf K ≤ GK K := by
    intro x hx
    have h1 : x ∈ Gj K s := ((hG K x (hH0 x hx)).1 s).2 (by
      rw [(hG K x (hH0 x hx)).2.1 hx, Units.val_one, sub_self, norm_zero]
      positivity)
    exact fun y => h1 ⟨y.1, hK y.2⟩
  have hj : Lev l 1 := ⟨le_rfl, fun e => absurd e h2⟩
  have hN : ¬ l ∣ l - 1 := by
    have := hl.two_le
    exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  have hpow := norm_pow_pred_sub_one_le hχ
  have hN0 : l - 1 ≠ 0 := by have := hl.two_le; omega
  refine ⟨?_, fun γ hγ U hU hp g => ?_⟩
  · have htor : ∀ δ ∈ W.DelF, δ ^ (l - 1) = 1 := by
      intro δ hδ
      obtain ⟨g, rfl⟩ := W.resΓ_onto δ
      obtain ⟨k, hk, hk'⟩ := (W.DelF_def _).1 hδ
      rw [res_pow_eq_one_iff] at hk' ⊢
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_one]
      refine eq_one_of_pow hj (hpow g) hk.ne' ?_
      rw [← pow_mul, mul_comm, pow_mul, ← Units.val_pow_eq_pow_val, hk', Units.val_one, one_pow]
    have h1Δ : (1 : W.Gam) ∈ W.DelF := (mem_DelF_iff W _).2 (one_mem _)
    intro hdv
    haveI : Finite ↥(CommGroup.torsion W.Gam) := Nat.finite_of_card_ne_zero (by
      rw [card_torsion]; exact Finset.card_ne_zero.2 ⟨1, h1Δ⟩)
    rw [← card_torsion] at hdv
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' l hdv
    apply hN
    have h3 : orderOf x ∣ l - 1 :=
      orderOf_dvd_iff_pow_eq_one.2 (Subtype.ext (htor x ((mem_DelF_iff W _).2 x.2)))
    rwa [hx] at h3
  · have hmemΔ : ∀ g : ↥(GK K), P.χQ g ^ (l - 1) = 1 → W.resΓ g ∈ W.DelF := fun g hg =>
      (W.DelF_def _).2 ⟨l - 1, Nat.pos_of_ne_zero hN0, (res_pow_eq_one_iff W g _).2 hg⟩
    obtain ⟨γ', hγ'⟩ := W.resΓ_onto γ
    have hv : (P.χQ γ' : ℚ_[l]) = 1 + l := by
      apply (algebraMap ℚ_[l] ↥LL.1).injective
      rw [← chi_res W γ', hγ', hγ]
      simp
    have hn : ‖(P.χQ γ' : ℚ_[l]) - 1‖ = (l : ℝ) ^ (-((1 : ℕ) : ℤ)) := by
      rw [hv, add_sub_cancel_left, Padic.norm_p]
      simp
    refine mem_of_tors_gen ha hχ K hH hj hN hN (fun x _ => hpow x) (fun x _ hx => hx) U hU
      (fun x hx => hp x (Or.inl (hmemΔ x hx))) γ' (hp γ' (Or.inr hγ')) (fun x => ?_) g
    rw [norm_pow_sub_one hj hn.le hN, hn]
    exact hpow x

theorem exists_closed_stab {G Qp LL O k : Type} [Group G] [TopologicalSpace G] [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] [IsTopologicalRing LL] [Field k]
    [Algebra O k] (hO : IsOpen (Set.range (algebraMap O LL))) {c : O} (hc : algebraMap O LL c ≠ 0)
    (hk : algebraMap O k c = 0) (T : LocLat G Qp LL O) (A : Ob k G) (q : ↥T.L.T →ₗ[O] (Fin A.m → k))
    (hq : Onto T A q) (t : Fin A.m → k) :
    ∃ U : Subgroup G, IsClosed (U : Set G) ∧ ∀ g, g ∈ U ↔ A.ρ g t = t := by
  obtain ⟨x, rfl⟩ := hq.1 t
  have hlc : IsLocallyConstant fun g => q (latRep T.L g x) :=
    GlobalTheory.FiniteAdm.isLocallyConstant_comp hO T.L.T T.L.fg T.L.span hc q
      (fun y => by rw [← algebraMap_smul k, hk, zero_smul]) _ (T.cont x)
  let U : Subgroup G :=
    { carrier := {g | A.ρ g (q x) = q x}
      mul_mem' := fun {a b} ha hb => by
        change A.ρ a (q x) = q x at ha
        change A.ρ b (q x) = q x at hb
        change A.ρ (a * b) (q x) = q x
        rw [map_mul, Module.End.mul_apply, hb, ha]
      one_mem' := by simp
      inv_mem' := fun {a} ha => by
        change A.ρ a (q x) = q x at ha
        change A.ρ a⁻¹ (q x) = q x
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  refine ⟨U, ?_, fun g => Iff.rfl⟩
  have := hlc.isClosed_fiber (q x)
  simp only [hq.2] at this
  exact this

theorem fixed_of_fixed_lifts : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (H : LocHW l P) (S : TopSit P) (k : Type) [Field k] [Algebra S.O k] [CharP k l], S.IsRes k → (((S.W H).DelF.card : ℕ) : k) ≠ 0 ∧ ∀ γ : (S.W H).Gam, ((S.W H).χΓ γ : S.O) = 1 + (l : S.O) → ∀ (T : LocLat S.G ℚ_[l] ↥S.LL.1 S.O) (A : Ob k S.G) (q : ↥T.L.T →ₗ[S.O] (Fin A.m → k)), Onto T A q → ∀ t : Fin A.m → k, (∀ g, ((S.W H).resΓ g ∈ (S.W H).DelF ∨ (S.W H).resΓ g = γ) → A.ρ g t = t) → ∀ g, A.ρ g t = t := by
  intro l _ P AI H S k _ _ _ _
  have hl : l.Prime := Fact.out
  obtain ⟨h1, h2⟩ := card_and_dense AI S.hyp.1.2.1.2.1 S.hyp.1.2.1.2.2.2.2.1 (S.W H)
  refine ⟨fun h => h1 ((CharP.cast_eq_zero_iff k l _).1 h), fun γ hγ T A q hq t ht => ?_⟩
  haveI : IsTopologicalRing ↥S.LL.1 :=
    inferInstanceAs (IsTopologicalRing ↥S.LL.1.toSubalgebra.toSubring)
  obtain ⟨U, hU, hm⟩ := exists_closed_stab (c := (l : S.O)) (GlobalTheory.LocalIntegers.isOpen_integers l S.LL)
    (by rw [map_natCast]; exact Nat.cast_ne_zero.2 hl.ne_zero)
    (by rw [map_natCast, CharP.cast_eq_zero]) T A q hq t
  exact fun g => (hm g).1 (h2 γ hγ U hU (fun g hg => (hm g).2 (ht g hg)) g)

end GlobalTheory.RedDense
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlatOverProductPowerSeriesRingStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_over_product_power_series_ring : ∀ (O : Type) [CommRing O] [IsNoetherianRing O] (n : ℕ) [NeZero n] (E : Type) [CommRing E] [Algebra (LetA O n) E] (p : ℕ), IsUnit (algebraMap (LetA O n) E letπ) → IsAdicComplete (Ideal.span {(p : E)}) E → (∀ (x : E) (k : ℕ), ∃ (a : LetA O n) (m : ℕ), x * algebraMap (LetA O n) E (letπ ^ m) - algebraMap (LetA O n) E a ∈ Ideal.span {(p : E) ^ k}) → (∀ (a : LetA O n) (k : ℕ), algebraMap (LetA O n) E a ∈ Ideal.span {(p : E) ^ k} → ∃ b : LetA O n, a = (p : LetA O n) ^ k * b) → Module.Flat (LetA O n) E := by
  first | exact @GlobalTheory.FlatLocCompl.flat_letA | exact GlobalTheory.FlatLocCompl.flat_letA | (intros; apply GlobalTheory.FlatLocCompl.flat_letA <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrKIsometricAndOneSubSurjectiveStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_frK_eq_and_exists_sub_pow_smul_frK_eq : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l), (∀ c : ↥(K0 K), ‖((frK P K c : ↥(K0 K)) : Om l)‖ = ‖(c : Om l)‖) ∧ ∀ j : ℕ, 1 ≤ j → ∀ c : ↥(K0 K), ‖(c : Om l)‖ ≤ 1 → ∃ d : ↥(K0 K), ‖(d : Om l)‖ ≤ 1 ∧ d - (l : ↥(K0 K)) ^ j * frK P K d = c := by
  first | exact @GlobalTheory.ExpImage.frK_isometric_and_one_sub_surjective | exact GlobalTheory.ExpImage.frK_isometric_and_one_sub_surjective | (intros; apply GlobalTheory.ExpImage.frK_isometric_and_one_sub_surjective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusIntegralityTensorAinfCoefficientsStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_integrality_tensor_ainf_coefficients : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (p q : Type) [Fintype p] [Fintype q] (Z : Matrix p q (RW LL)) (S : Matrix p p (RA LL)) (S' : Matrix q q (RA LL)) (Y : Matrix p q (RA LL)), Z.map (φRW LL) = S.map (inclR LL) * Z * S'.map (inclR LL) + Y.map (inclR LL) → ∀ a b, Z a b ∈ Set.range (inclR LL) := by
  first | exact @GlobalTheory.FrobIntegralCoeff.frobenius_integrality_coeff | exact GlobalTheory.FrobIntegralCoeff.frobenius_integrality_coeff | (intros; apply GlobalTheory.FrobIntegralCoeff.frobenius_integrality_coeff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusSubOneSurjectiveWittTiltStatement
section
theorem _root_.GlobalTheory.T.frobenius_sub_one_surjective_witt_tilt : Formalism.MainNotions.ElementDenominator.ArtinSchreierWittOnto := fun l _ x =>
  PI.ArtSch.main_of witt_lift (tiltSurjectiveOfParts rootModP_holds tilt_divisibility smallSurjective) l x
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodCoefficientRingPadicIntegersFinExtStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodCoefficientRing_padicIntegers_finExt : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l), GoodO (Qp := ℚ_[l]) ↥LL.1 ↥(OL LL) := by
  first | exact @GlobalTheory.LocalIntegers.goodO_integers | exact GlobalTheory.LocalIntegers.goodO_integers | (intros; apply GlobalTheory.LocalIntegers.goodO_integers <;> assumption)
end

