import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0158
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0102
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0173
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0174
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdemOfIsPrimeIdem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1151
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0019
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BaseChangeIsomorphicFields
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0126
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0177
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0178
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0179
import Formalism.LocalToGlobal.InertKernelTheory.Bundle0004

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSphericalDoubleCosetLabelIffDecreasing
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LabChar

theorem conjPl_eq_cP {D : D7} (P : HeightOneSpectrum (𝓞 D.host.E)) : conjPl P = GlobalTheory.IdemSupport.cP P := by
  apply HeightOneSpectrum.ext
  show P.asIdeal.map (Formalism.DivisionValues.cO D.host.E) = P.asIdeal.comap (GlobalTheory.IdemSupport.cO D).toRingHom
  have h : Formalism.DivisionValues.cO D.host.E = GlobalTheory.IdemSupport.cO D := rfl
  rw [h]
  have inv : ∀ y, GlobalTheory.IdemSupport.cO D (GlobalTheory.IdemSupport.cO D y) = y := fun y => by
    apply RingOfIntegers.ext
    simp [GlobalTheory.IdemSupport.cO]
  ext x
  rw [Ideal.mem_map_of_equiv, Ideal.mem_comap]
  constructor
  · rintro ⟨y, hy, rfl⟩
    show GlobalTheory.IdemSupport.cO D (GlobalTheory.IdemSupport.cO D y) ∈ P.asIdeal
    rwa [inv]
  · intro hx
    exact ⟨_, hx, inv x⟩

theorem eq_of_fixed {D : D7} (V : HSp D) {P : HeightOneSpectrum (𝓞 D.host.E)} {e f : Formalism.L2.Theta.AE D}
    (h : IsPrimeIdem P e f) (hc : conjPl P = P) : f = e := by
  rcases id h with ⟨hs, rfl⟩ | ⟨rfl, -⟩
  · exfalso
    have H := GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V
    have hcc : Formalism.IndefR.Lev.IsConjPl P P := by
      rw [GlobalTheory.IdemSupport.isConjPl_iff, ← conjPl_eq_cP, hc]
    have hs' := H.2.2.2 P P e hs hcc
    have h' : IsPrimeIdem P (cA D e) (cA D e + cA D (cA D e)) := Or.inl ⟨hs', rfl⟩
    have hee := ((H.2.2.1 P e _ h).2.2.2.1 _ _ h').1
    obtain ⟨⟨h1, h2, -⟩, ht⟩ := hs
    have e0 : e = 0 := by
      rw [hee, h1] at h2
      exact h2
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
    have := (ht x hx0).1 hx
    apply this
    rw [e0, zero_mul, map_zero]
    exact zero_mem _
  · rfl

theorem fixed_of_tie {D : D7} {P : HeightOneSpectrum (𝓞 D.host.E)} {e : Formalism.L2.Theta.AE D}
    (h : IsPrimeIdem P e e) : conjPl P = P := by
  rcases h with ⟨hs, he⟩ | ⟨-, ⟨v, ε, -, rfl⟩, ht⟩
  · exfalso
    obtain ⟨⟨h1, h2, -⟩, ht⟩ := hs
    have hc : cA D e = 0 := by
      have := he
      nth_rewrite 1 [← add_zero e] at this
      exact (add_left_cancel this).symm
    have e0 : e = 0 := by
      have := congrArg (cA D) hc
      rwa [cA_cA, map_zero] at this
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
    apply (ht x hx0).1 hx
    rw [e0, zero_mul, map_zero]
    exact zero_mem _
  · have ht' := GlobalTheory.IdemSupport.Comparison₂.conj ht
    rw [GlobalTheory.IdemSupport.cA_algebraMap] at ht'
    rw [conjPl_eq_cP]
    apply HeightOneSpectrum.ext
    ext x
    by_cases hx : x = 0
    · subst hx; simp only [zero_mem]
    · rw [ht' x hx, ht x hx]

theorem lab_char (hU : ∀ {D : D7} (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (e f : Formalism.L2.Theta.AE D) (ϖ : 𝓞 D.host.E) (d d' : List ℤ) (g : GA D V), IsPrimeIdem P e f → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → d.Pairwise (fun a b => b ≤ a) → d'.Pairwise (fun a b => b ≤ a) → DivAt V e (ϖ : D.host.E) d g → DivAt V e (ϖ : D.host.E) d' g → d = d') (hS : ∀ {D : D7} (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (e : Formalism.L2.Theta.AE D) (ϖ : 𝓞 D.host.E) (d : List ℤ), Formalism.L2.NTheta.IsIdemAt e P → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → d.length = V.rank → ∃ g : GA D V, SuppF V (e + cA D e) g ∧ DivAt V e (ϖ : D.host.E) d g) (hI : ∀ {D : D7} (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (e : Formalism.L2.Theta.AE D) (x : 𝓞 D.host.F) (ϖ : 𝓞 D.host.E) (d : List ℤ), IsPrimeIdem P e e → (ϖ : D.host.E) = algebraMap D.host.F D.host.E (x : D.host.F) → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → d.length = V.rank → dualLab d = d → ∃ g : GA D V, SuppF V e g ∧ DivAt V e (ϖ : D.host.E) d g) : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E), ∀ d : List ℤ, IsLab V P d ↔ d.length = V.rank ∧ d.Pairwise (fun a b => b ≤ a) ∧ (conjPl P = P → dualLab d = d) := by
  intro D V P d
  have H := GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V
  constructor
  · rintro ⟨R, e, f, ϖ, α, -, h, h1, h2, hd, -, -, hα, hD, -, -⟩
    refine ⟨hD.1, hd, fun hc => ?_⟩
    obtain rfl := eq_of_fixed V h hc
    have he : f * f = f := (H.2.2.1 P f f h).1
    obtain ⟨⟨a, b, ha, -, hb, -, hinv⟩, -⟩ :=
      GlobalTheory.InertDoubleCoset.inert_double_cosets V P f h (GlobalTheory.SphLabelOps.exists_real_unif D P) α hα
    have hϖ0 := GlobalTheory.SphLabelOps.unif_ne_zero h2
    have hx := GlobalTheory.DivDual.divAt_inv_and_mul V f (ϖ : D.host.E) d α he hϖ0 hD
    have h3 := hx.2 a ha b hb
    rw [← hinv] at h3
    exact hU V P f f ϖ (dualLab d) d α⁻¹ h h1 h2 (GlobalTheory.SphLabelOps.dualLab_pairwise hd) hd hx.1 h3
  · rintro ⟨hl, hd, hs⟩
    obtain ⟨e, f, h⟩ := H.2.1 P
    obtain ⟨x, y, hy, h1, h2⟩ := GlobalTheory.SphLabelOps.exists_real_unif D P
    by_cases hc : conjPl P = P
    · obtain rfl := eq_of_fixed V h hc
      obtain ⟨g, hg, hD⟩ := hI V P f x y d h hy h1 h2 hl (hs hc)
      exact GlobalTheory.SphLabelOps.isLab_of_divAt h h1 h2 hd hg hD
    · rcases id h with ⟨hi, rfl⟩ | ⟨rfl, -⟩
      · obtain ⟨g, hg, hD⟩ := hS V P e y d hi h1 h2 hl
        exact GlobalTheory.SphLabelOps.isLab_of_divAt h h1 h2 hd hg hD
      · exact absurd (fixed_of_tie h) hc

theorem labels_char : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E), ∀ d : List ℤ, IsLab V P d ↔ d.length = V.rank ∧ d.Pairwise (fun a b => b ≤ a) ∧ (conjPl P = P → dualLab d = d) :=
  lab_char GlobalTheory.T.elementaryDivisorsAtPrime_unique GlobalTheory.T.exists_unitary_elementaryDivisors_splitPrime GlobalTheory.T.exists_unitary_elementaryDivisors_inertPrime

end GlobalTheory.LabChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelOperatorsAtPrimeOffLevelDatum
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevOp

variable {D : D7} {V : HSp D} {P : Pl D.host.E}

theorem mem_hyp {e f : Formalism.L2.Theta.AE D} (hP : IsPrimeIdem P e f) {k : GA D V} :
    k ∈ hyp V P ↔ k ∈ KsphC V ∅ ∧ SuppF V f k := by
  refine ⟨fun ⟨h, e', f', h', hs⟩ => ⟨h, ?_⟩, fun h => ⟨h.1, e, f, hP, h.2⟩⟩
  obtain ⟨-, rfl⟩ := ((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.2.1 P e f hP).2.2.2.1 e' f' h'
  exact hs

theorem comm_of_supp {e f : Formalism.L2.Theta.AE D} (hP : IsPrimeIdem P e f) {a b : GA D V} (ha : SuppF V f a)
    (hb : SuppF V (1 - f) b) : Commute a b :=
  have h1 := (GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.2.1 P e f hP
  ((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).1 f h1.1 h1.2.1).2.2 (1 - f) a b (by rw [mul_sub, mul_one, h1.1, sub_self]) ha hb

theorem full_iff {e f : Formalism.L2.Theta.AE D} (hP : IsPrimeIdem P e f) {J : Set (GA D V)} {χ : GA D V → ℂ}
    (hJ : ∀ g, SuppF V f g → (g ∈ J ↔ g ∈ KsphC V ∅)) (hχ : ∀ g ∈ J, SuppF V f g → χ g = 1)
    (SF : Finset (HeightOneSpectrum (𝓞 D.host.F))) (d : List ℤ) (B : Finset (GA D V)) :
    Hecke₂ V J χ SF P d B ↔ OffS D SF P ∧ SphOp V P d B := by
  have hK : {k | k ∈ J ∧ SuppF V f k} = {k | k ∈ KsphC V ∅ ∧ SuppF V f k} :=
    Set.ext fun k => and_congr_left fun hk => hJ k hk
  constructor
  · rintro ⟨e', f', ϖ, α, hS, hP', h1, h2, hd, -, -, hα, hD, hR, hc⟩
    obtain ⟨rfl, rfl⟩ := ((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.2.1 P e f hP).2.2.2.1 e' f' hP'
    exact ⟨hS, _, _, ϖ, α, fun v hv => absurd hv (Finset.notMem_empty v), hP, h1, h2, hd, fun _ _ => Iff.rfl,
      fun _ _ _ => rfl, hα, hD, hR, hK ▸ hc⟩
  · rintro ⟨hS, e', f', ϖ, α, -, hP', h1, h2, hd, -, -, hα, hD, hR, hc⟩
    obtain ⟨rfl, rfl⟩ := ((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.2.1 P e f hP).2.2.2.1 e' f' hP'
    exact ⟨_, _, ϖ, α, hS, hP, h1, h2, hd, hJ, hχ, hα, hD, hR, hK ▸ hc⟩

theorem offS_empty : OffS D ∅ P := fun v hv => absurd hv (Finset.notMem_empty v)

theorem rep_cases (d : List ℤ) : GlobalTheory.Hk3.rep V P d = ∅ ∨ SphOp V P d (GlobalTheory.Hk3.rep V P d) := by
  unfold GlobalTheory.Hk3.rep
  split_ifs with h
  · exact Or.inr h.choose_spec
  · exact Or.inl rfl

theorem heckeLin_translate {e f : Formalism.L2.Theta.AE D} (hP : IsPrimeIdem P e f) {J : Subgroup (GA D V)}
    (hJ : ∀ g, SuppF V f g → (g ∈ J ↔ g ∈ KsphC V ∅)) {d : List ℤ} {R : Finset (GA D V)} (hR : SphOp V P d R)
    {F : GA D V → ℂ} (hF : ∀ k ∈ hyp V P, ∀ h, F (h * k) = F h) {k₁ k₂ : GA D V} (hk₁ : k₁ ∈ J)
    (s₁ : SuppF V f k₁) (s₂ : SuppF V (1 - f) k₂) (h : GA D V) :
    heckeLin V R F (h * (k₁ * k₂)) = heckeLin V R (fun x => F (x * (k₁ * k₂))) h := by
  obtain ⟨L, hL⟩ := GlobalTheory.HeckeKeep.exists_loc V f
  have hJ' : ∀ g, SuppF V f g → (g ∈ ((J ⊓ L : Subgroup (GA D V)) : Set (GA D V)) ↔ g ∈ KsphC V ∅) := fun g hg =>
    ⟨fun h => (hJ g hg).1 h.1, fun h => ⟨(hJ g hg).2 h, (hL g).2 hg⟩⟩
  have hop := (full_iff hP (χ := fun _ => 1) hJ' (fun _ _ _ => rfl) ∅ d R).2 ⟨offS_empty, hR⟩
  have hsupp : ∀ γ ∈ R, SuppF V f γ := by
    obtain ⟨e', f', ϖ, α, -, hP', -, -, -, -, -, -, -, hR, -⟩ := hR
    obtain ⟨-, rfl⟩ := ((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.2.1 P e f hP).2.2.2.1 e' f' hP'
    exact hR
  have key := GlobalTheory.SphericalOps.level_heckeLin (J := J ⊓ L) (F := fun x => F (x * k₂)) (fun _ _ _ _ => (one_mul _).symm)
    (fun e' f' _ hP' k hk => by
      obtain ⟨-, rfl⟩ := ((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.2.1 P e f hP).2.2.2.1 e' f' hP'
      exact ⟨k, hk, 1, one_mem _, (hL k).1 hk.2, GlobalTheory.HeckeKeep.suppF_one _, (mul_one k).symm⟩) hop
    (fun k hk g => by
      have s := (hL k).1 hk.2
      show F (g * k * k₂) = 1 * F (g * k₂)
      rw [one_mul, mul_assoc, (comm_of_supp hP s s₂).eq, ← mul_assoc,
        hF k ((mem_hyp hP).2 ⟨(hJ k s).1 hk.1, s⟩)]) k₁ ⟨hk₁, (hL _).2 s₁⟩ h
  rw [one_mul, heckeLin_apply, heckeLin_apply] at key
  rw [heckeLin_apply, heckeLin_apply]
  refine Eq.trans (Finset.sum_congr rfl fun a ha => ?_) (key.trans (Finset.sum_congr rfl fun a _ => ?_))
  · rw [← mul_assoc, mul_assoc _ k₂, ← (comm_of_supp hP (hsupp a ha) s₂).eq, ← mul_assoc]
  · show _ = F (h * a * (k₁ * k₂))
    rw [(comm_of_supp hP s₁ s₂).eq, ← mul_assoc, hF k₁ ((mem_hyp hP).2 ⟨(hJ _ s₁).1 hk₁, s₁⟩)]

theorem hk_apply (c : List ℤ →₀ ℂ) (F : GA D V → ℂ) (h : GA D V) :
    hk V P c F h = ∑ d ∈ c.support, c d * heckeLin V (GlobalTheory.Hk3.rep V P d) F h := by
  unfold hk Finsupp.sum
  rw [LinearMap.sum_apply, Finset.sum_apply]
  rfl

theorem hk_translate {e f : Formalism.L2.Theta.AE D} (hP : IsPrimeIdem P e f) {J : Subgroup (GA D V)}
    (hJ : ∀ g, SuppF V f g → (g ∈ J ↔ g ∈ KsphC V ∅)) (c : List ℤ →₀ ℂ)
    {F : GA D V → ℂ} (hF : ∀ k ∈ hyp V P, ∀ h, F (h * k) = F h) {k₁ k₂ : GA D V} (hk₁ : k₁ ∈ J)
    (s₁ : SuppF V f k₁) (s₂ : SuppF V (1 - f) k₂) (h : GA D V) :
    hk V P c F (h * (k₁ * k₂)) = hk V P c (fun x => F (x * (k₁ * k₂))) h := by
  rw [hk_apply, hk_apply]
  refine Finset.sum_congr rfl fun d _ => ?_
  congr 1
  rcases rep_cases (V := V) (P := P) d with h0 | h0
  · rw [h0, heckeLin_apply, heckeLin_apply, Finset.sum_empty, Finset.sum_empty]
  · exact heckeLin_translate hP hJ h0 hF hk₁ s₁ s₂ h

theorem postOn_hk {S : D.what₂.Tau → SPar} (M : DSModel V S) (c : List ℤ →₀ ℂ) (U : MMap M) :
    postOn M (hk V P c) U = ∑ d ∈ c.support, c d • heckeOn M (GlobalTheory.Hk3.rep V P d) U := by
  ext v g
  rw [postOn_apply, hk_apply, MultilinearMap.sum_apply, Finset.sum_apply]
  rfl

theorem level_operators : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ) (L : LevDat D.host.E ℂ V.rank), IsBaseFrame V β Λ N → ∀ P : Pl D.host.E, ((N : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal → (∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P) → (∀ k ∈ hyp V P, k ∈ levG V β L ∧ levChi V β L k = 1) ∧ (∀ SF d B, Hecke₂ V (levS V β L) (levChi V β L) SF P d B ↔ OffS D SF P ∧ SphOp V P d B) ∧ (∀ c Φ, HasType V β L Φ → HasType V β L (hk V P c Φ)) ∧ (∀ c (g0 : G0 L.Pg L.r) Φ, (∀ k ∈ hyp V P, ∀ h, Φ (h * k) = Φ h) → actG0 V β L g0 (hk V P c Φ) = hk V P c (actG0 V β L g0 Φ)) ∧ ∀ (S : D.what₂.Tau → SPar) (θ : InfFam D) (M : DSModel V S) c, IsInfFam θ → ∀ U ∈ Mult θ M (levS V β L) (levChi V β L), postOn M (hk V P c) U ∈ Mult θ M (levS V β L) (levChi V β L) := by
  intro D V β Λ N L hB P hN hPP
  obtain ⟨e, f, hP⟩ := (GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.1 P
  obtain ⟨hJ, hχ, hs⟩ := (GlobalTheory.LevSplit.lev_split V β Λ N L hB).2 P e f hP hN hPP
  obtain ⟨hJ', -, hs'⟩ := (GlobalTheory.LevSplit.lev_split V β Λ N (flagL L) hB).2 P e f hP hN hPP
  have h1 : ∀ k ∈ hyp V P, k ∈ levG V β L ∧ levChi V β L k = 1 := fun k hk => by
    obtain ⟨a, b⟩ := (mem_hyp hP).1 hk
    exact ⟨(hJ k b).2 a, hχ k ((hJ k b).2 a) b⟩
  have hinv : ∀ Φ, HasType V β L Φ → ∀ k ∈ hyp V P, ∀ h, Φ (h * k) = Φ h := fun Φ hΦ k hk h => by
    rw [hΦ k (h1 k hk).1, (h1 k hk).2, one_mul]
  refine ⟨h1, full_iff hP hJ hχ, fun c Φ hΦ κ hκ h => ?_, fun c g0 Φ hΦ => ?_, fun S θ M c hθ U hU => ?_⟩
  · obtain ⟨k₁, hk₁, k₂, -, s₁, s₂, rfl⟩ := hs κ hκ
    have e1 : (fun x => Φ (x * (k₁ * k₂))) = levChi V β L (k₁ * k₂) • Φ := funext fun x => hΦ _ hκ x
    rw [hk_translate hP hJ c (hinv Φ hΦ) hk₁ s₁ s₂, e1, LinearMap.map_smul]
    rfl
  · unfold actG0
    split_ifs with hex
    · have hl := hex.choose_spec
      generalize hex.choose = κ at hl ⊢
      have hκ : κ ∈ levG V β (flagL L) := ⟨hl.1, hl.2.1, Subgroup.mem_top _⟩
      obtain ⟨k₁, hk₁, k₂, -, s₁, s₂, rfl⟩ := hs' κ hκ
      have e1 : (fun x => (levChi V β (flagL L) (k₁ * k₂))⁻¹ * Φ (x * (k₁ * k₂))) =
        (levChi V β (flagL L) (k₁ * k₂))⁻¹ • fun x => Φ (x * (k₁ * k₂)) := rfl
      rw [e1, LinearMap.map_smul]
      funext h
      rw [hk_translate hP hJ' c hΦ hk₁ s₁ s₂]
      rfl
    · rw [LinearMap.map_zero]
  · rw [postOn_hk]
    refine sum_mem fun d _ => Submodule.smul_mem _ _ ?_
    rcases rep_cases (V := V) (P := P) d with h0 | h0
    · have : heckeOn M (GlobalTheory.Hk3.rep V P d) U = 0 := by
        ext v g
        rw [h0, heckeOn, postOn_apply, heckeLin_apply, Finset.sum_empty]
        rfl
      rw [this]
      exact zero_mem _
    · have hop := (full_iff hP (J := levS V β L) hJ hχ ∅ d _).2 ⟨offS_empty, h0⟩
      rw [GlobalTheory.MultMem.mem_mult_iff] at hU ⊢
      refine GlobalTheory.SphericalOps.isMultMap_heckeOn hU (fun k hk => ?_) fun v κ hκ h => ?_
      · obtain ⟨_, _, _, _, -, -, -, -, -, -, -, -, -, -, hc⟩ := hop
        exact (hc.1 k hk).1
      · obtain ⟨k₁, hk₁, k₂, -, s₁, s₂, rfl⟩ := hs κ hκ
        have e1 : (fun x => U v (x * (k₁ * k₂))) = levChi V β L (k₁ * k₂) • U v := funext fun x => hU.lev v _ hκ x
        rw [heckeLin_translate hP hJ h0 (hinv _ (hU.lev v)) hk₁ s₁ s₂, e1, LinearMap.map_smul]
        rfl

end GlobalTheory.LevOp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LtOneOfContinuous
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open Filter Topology Matrix GlobalTheory.IsoPull

namespace GlobalTheory.DegOneLift

section Val

variable {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M]

theorem tendsto_pow {v : HeightOneSpectrum (𝓞 K)} (x : v.adicCompletion K) (h : Valued.v x < 1) :
    Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0) := by
  rw [(Valued.hasBasis_nhds_zero _ _).tendsto_right_iff]
  intro γ _
  have hne : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 := by simp
  obtain ⟨n, hn⟩ := exists_pow_lt₀ h (Units.mk0 _ hne)
  filter_upwards [eventually_ge_atTop n] with m hm
  rw [Valuation.restrict_lt_iff_lt_embedding, map_pow]
  exact lt_of_le_of_lt (pow_le_pow_right_of_le_one' h.le hm) hn

theorem lt_one_of_continuous {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 M)}
    (s : v.adicCompletion K →+* w.adicCompletion M) (hs : Continuous s) {z : v.adicCompletion K}
    (hz : Valued.v z < 1) : Valued.v (s z) < 1 := by
  have h1 : Tendsto (fun n : ℕ => s z ^ n) atTop (𝓝 0) := by
    have := (hs.tendsto 0).comp (tendsto_pow z hz)
    simpa [Function.comp_def, map_pow] using this
  have hU : {y : w.adicCompletion M | Valued.v y < 1} ∈ 𝓝 (0 : w.adicCompletion M) :=
    Valued.mem_nhds_zero.2 ⟨1, fun y hy => by simpa using hy⟩
  obtain ⟨N, hN⟩ := (h1.eventually hU).exists
  by_contra hc
  rw [not_lt] at hc
  have hN' : Valued.v (s z ^ N) < 1 := hN
  rw [map_pow] at hN'
  exact absurd hN' (not_lt.2 (one_le_pow₀ hc))

theorem mem_iff_lt_one (v : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) :
    x ∈ v.asIdeal ↔ Valued.v (algebraMap K (v.adicCompletion K) (x : K)) < 1 := by
  have h : Valued.v (algebraMap K (v.adicCompletion K) (x : K)) = v.valuation K (algebraMap (𝓞 K) K x) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _
  rw [h, HeightOneSpectrum.valuation_lt_one_iff_mem]

theorem over_of_continuous (e : K ≃+* M) {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 M)}
    (i : v.adicCompletion K →+* w.adicCompletion M) (hi : Continuous i)
    (he : ∀ x : K, i (algebraMap K _ x) = algebraMap M _ (e x)) : Over e v w := by
  have h1 : v.asIdeal ≤ (src e w).asIdeal := by
    intro x hx
    rw [ringEquivPlaceCorrespondence_placeUnder e w x, mem_iff_lt_one]
    rw [mem_iff_lt_one] at hx
    have := lt_one_of_continuous i hi hx
    rw [he] at this
    exact this
  have h2 : v = src e w := HeightOneSpectrum.ext (v.isMaximal.eq_of_le (src e w).isPrime.ne_top h1)
  rw [h2]
  exact ringEquivPlaceCorrespondence_placeUnder e w

theorem normV_eq_absNorm (v : HeightOneSpectrum (𝓞 K)) : normV v = Ideal.absNorm v.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rfl

theorem two_le_normV (v : HeightOneSpectrum (𝓞 K)) : 2 ≤ normV v := by
  rw [normV_eq_absNorm]
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := fun h => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
  omega

end Val

end GlobalTheory.DegOneLift

namespace GlobalTheory.DegOneLift

section Rep

variable {K M : Type} [Field K] [NumberField K] [IsTotallyComplex K] [Field M] [NumberField M] [IsTotallyComplex M]
  {a : ℕ}

theorem pull_pull (e : K ≃+* M) (φ : Sm K a) : pull a e (pull a e.symm φ) = φ :=
  Subtype.ext <| funext fun g => congrArg φ.1 (mapA_symm e g)

theorem pullSub_pullSub (e : K ≃+* M) (π : CuspSub K a) : pullSub e (pullSub e.symm π) = π := by
  refine CuspSub.ext ?_
  change (π.V.map (pull a e.symm).toLinearMap).map (pull a e).toLinearMap = π.V
  rw [← Submodule.map_comp]
  convert Submodule.map_id π.V
  refine LinearMap.ext fun φ => ?_
  exact pull_pull e φ

def SmIrr.comap {G H : Type} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H] (σ : SmIrr H)
    (f : G →* H) (hf : Continuous f) (hs : Function.Surjective f) : SmIrr G where
  V := σ.V
  ρ := σ.ρ.comp f
  smooth x := (σ.smooth x).preimage hf
  irred := by
    obtain ⟨h0, h⟩ := (GlobalTheory.CuspRep.isIrreducible_iff _).1 σ.irred
    refine (GlobalTheory.CuspRep.isIrreducible_iff _).2 ⟨h0, fun W hW => h W fun g x hx => ?_⟩
    obtain ⟨g, rfl⟩ := hs g
    exact hW g x hx

theorem locRep_pullSub (e : K ≃+* M) {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 M)} (hO : Over e v w)
    (π : CuspSub K a) (g : GL (Fin a) (v.adicCompletion K)) (x : π.V) :
    (pullSub e.symm π).locRep w (GeneralLinearGroup.map (cLoc hO) g) ((pull a e.symm).submoduleMap π.V x) =
      (pull a e.symm).submoduleMap π.V (π.locRep v g x) := by
  apply Subtype.ext
  refine Eq.trans ?_ (pull_act e.symm (.fin (locGL K a v g)) x.1).symm
  change _ = act (.fin (GeneralLinearGroup.map (cFin e) (locGL K a v g))) (pull a e.symm x.1)
  rw [cFin_locGL hO]
  rfl

end Rep

theorem isLift : ∀ (K M : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field M] [NumberField M] [IsTotallyComplex M] [Algebra K M], Module.finrank K M = 1 → ∀ (a : ℕ) (π : CuspSub K a), ∃ P : CuspSub M a, GlobalTheory.GalCut.IsLift π P := by
  intro K M _ _ _ _ _ _ _ h1 a π
  let e : K ≃+* M := RingEquiv.ofBijective (algebraMap K M) (Algebra.finrank_eq_one_iff_bijective_algebraMap.1 h1)
  have he : ∀ x, e x = algebraMap K M x := fun _ => rfl
  refine ⟨pullSub e.symm π, ?_, ?_, ?_⟩
  · intro w f B hf hB
    have hO : Over e.symm w (w.under (𝓞 K)) := fun x => by
      rw [HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap]
      have : algebraMap (𝓞 K) (𝓞 M) (RingOfIntegers.mapRingEquiv e.symm x) = x := by
        apply RingOfIntegers.ext
        change algebraMap K M (e.symm (x : M)) = x
        rw [← he]
        exact e.apply_symm_apply _
      rw [this]
    have hq : normV w = normV (w.under (𝓞 K)) := by
      rw [normV_eq_absNorm, normV_eq_absNorm]
      exact (qV_eq hO).symm
    have h2 := two_le_normV (w.under (𝓞 K))
    have hf1 : f = 1 := Nat.pow_right_injective h2 (by
      change normV (w.under (𝓞 K)) ^ f = normV (w.under (𝓞 K)) ^ 1
      rw [pow_one, ← hf, hq])
    subst hf1
    simp only [pow_one, Multiset.map_id']
    exact hasSat_pullSub e.symm hO hB
  · intro τ
    have hτ : (τ.comp e.toRingHom).comp e.symm.toRingHom = τ := by
      ext x
      simp
    have key : ∀ m, (CG.mk π).HasInfChar (τ.comp (algebraMap K M)) m ↔
        (CG.mk (pullSub e.symm π)).HasInfChar τ m := by
      intro m
      constructor
      · intro h
        exact hasInfChar_pullSub e.symm (π := π) (σ := τ) h
      · intro h
        have h3 : (pullSub e (pullSub e.symm π)).HasInfChar (τ.comp e.toRingHom) m :=
          hasInfChar_pullSub e (σ := τ.comp e.toRingHom) (by rw [hτ]; exact h)
        rw [pullSub_pullSub] at h3
        exact h3
    by_cases h : ∃ m, (CG.mk π).HasInfChar (τ.comp (algebraMap K M)) m
    · obtain ⟨m, hm⟩ := h
      rw [((key m).1 hm).infChar_eq, hm.infChar_eq]
    · have h' : ¬ ∃ m, (CG.mk (pullSub e.symm π)).HasInfChar τ m := fun ⟨m, hm⟩ => h ⟨m, (key m).2 hm⟩
      unfold CG.infChar
      rw [dif_neg h, dif_neg h']
  · intro v w i hi hie σ σ' hσ hσ'
    have hO : Over e v w := over_of_continuous e i.toRingHom hi fun x => hie x
    have hiL : ∀ y, i y = cLoc hO y := fun y => congrFun
      ((HeightOneSpectrum.denseRange_algebraMap (K := K) v).equalizer hi (continuous_cLoc hO)
        (funext fun x => (hie x).trans (cLoc_algebraMap hO x).symm)) y
    have hsurj : Function.Surjective (GeneralLinearGroup.map (n := Fin a) (cLoc hO)) := fun g =>
      ⟨GeneralLinearGroup.map (locEquiv hO).symm.toRingHom g, Units.ext (Matrix.ext fun _ _ =>
        (locEquiv hO).apply_symm_apply _)⟩
    let σ'' := SmIrr.comap σ' (GeneralLinearGroup.map (n := Fin a) (cLoc hO))
      (continuous_mapGL _ (continuous_cLoc hO)) hsurj
    let T := (pull a e.symm).submoduleMap π.V
    have h'' : π.IsLocComp v σ'' := by
      obtain ⟨f, h0, hf⟩ := hσ'
      refine ⟨T.symm.toLinearMap ∘ₗ f, fun hz => h0 (LinearMap.ext fun x => T.symm.injective ?_), fun g x => ?_⟩
      · exact (LinearMap.congr_fun hz x).trans (map_zero T.symm).symm
      · have e1 := hf (GeneralLinearGroup.map (cLoc hO) g) x
        have e2 : (pullSub e.symm π).locRep w (GeneralLinearGroup.map (cLoc hO) g) (T (T.symm (f x))) =
            T (π.locRep v g (T.symm (f x))) := locRep_pullSub e hO π g (T.symm (f x))
        have e3 : (pullSub e.symm π).locRep w (GeneralLinearGroup.map (cLoc hO) g) (f x) =
            T (π.locRep v g (T.symm (f x))) := by
          refine Eq.trans ?_ e2
          exact congrArg _ (T.apply_symm_apply (f x)).symm
        exact (congrArg T.symm (e1.trans e3)).trans (T.symm_apply_apply _)
    obtain ⟨E⟩ := GlobalTheory.CuspRep.LocUniq.isLocComp_unique π v σ σ'' hσ h''
    refine ⟨E.toLinearEquiv, fun g x => ?_⟩
    have hg : GeneralLinearGroup.map i.toRingHom g = GeneralLinearGroup.map (cLoc hO) g :=
      Units.ext (Matrix.ext fun _ _ => hiL _)
    rw [hg]
    exact LinearMap.congr_fun (E.isIntertwining' g) x

end GlobalTheory.DegOneLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SemisimpleConjOfTraceEqualStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semisimple_conj_of_trace_equal : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (a : ℕ) (r r' : G E Ω →* GL (Fin a) (Qbar l)), Continuous r → Continuous r' → IsSSRep r → IsSSRep r' → (∀ (w : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (σ : Weil h), (r (σ : G E Ω)).val.trace = (r' (σ : G E Ω)).val.trace) → ∃ p : GL (Fin a) (Qbar l), ∀ g, r' g = p * r g * p⁻¹ := by
  first | exact @GlobalTheory.TraceConjWeil.main | exact GlobalTheory.TraceConjWeil.main | (intros; apply GlobalTheory.TraceConjWeil.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TemperedRepTemperedParameterStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tempered_rep_tempered_parameter : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (rc : IrrGL (w.adicCompletion E) → WD h), IsRec h rc → ∀ (n : ℕ) (σ : IrrRep (GL (Fin n) (w.adicCompletion E))), GlobalTheory.LocGL.IsTemperedGL σ.ρ → (rc (cls σ)).tempered := by
  first | exact @GlobalTheory.LocLanglands.tempered_of_isTemperedGL | exact GlobalTheory.LocLanglands.tempered_of_isTemperedGL | (intros; apply GlobalTheory.LocLanglands.tempered_of_isTemperedGL <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaUnitFunctionShortModelIntegralStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaUnitFunction_shortModel_integral : Formalism.L2.KerInert.BeCob.ThetaTie := by
  first | exact @GlobalTheory.ShortModelTheta.thetaTie_holds | exact GlobalTheory.ShortModelTheta.thetaTie_holds | (intros; apply GlobalTheory.ShortModelTheta.thetaTie_holds <;> assumption)
end

