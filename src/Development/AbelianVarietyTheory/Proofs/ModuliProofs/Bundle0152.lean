import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0133
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0137
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaCosetNonvanishingOfHasTh
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0058
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0138
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MvPolynomialEqZeroOfEventually
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
import Development.AbelianVarietyTheory.Statements.HeckeInFamilies.GenericMemChart
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0026
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0039
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0004

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPrePullbackPrincipalRingChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.SiegelRingChange

variable {h k : ℕ} {B B' : Type} [CommRing B] [CommRing B'] {ζ : B} {ζ' : B'} {S : Scheme.{0}}

theorem spMap_comp' {R₁ R₂ R₃ : Type} [CommRing R₁] [CommRing R₂] [CommRing R₃] (a : R₁ →+* R₂) (b : R₂ →+* R₃) :
    spMap (b.comp a) = spMap b ≫ spMap a := by
  simp only [spMap, ← Spec.map_comp]
  rfl

theorem exists_spMap {R₁ R₂ : Type} [CommRing R₁] [CommRing R₂] (x : Sp R₂ ⟶ Sp R₁) :
    ∃ a : R₁ →+* R₂, spMap a = x := by
  obtain ⟨a, ha⟩ := Spec.map_surjective x
  exact ⟨a.hom, ha⟩

theorem spMap_inj {R₁ R₂ : Type} [CommRing R₁] [CommRing R₂] {a b : R₁ →+* R₂} (e : spMap a = spMap b) : a = b := by
  have := Spec.map_injective e
  exact congrArg CommRingCat.Hom.hom this

def down (j : B →+* B') (hj : j ζ = ζ') {s' : S ⟶ Sp B'} (c : SiegPre h k ζ' s') : SiegPre h k ζ (s' ≫ spMap j) :=
  { A := c.A, ab := c.ab, P := c.P, isLB := c.isLB, rig₁ := c.rig₁, rig₂ := c.rig₂, symm := c.symm
    lev := c.lev, lev_add := c.lev_add, lev_tors := c.lev_tors
    geom := fun K _ _ x β z hx hz => by
      obtain ⟨β', hβ'⟩ := exists_spMap (x ≫ s')
      have e : β'.comp j = β := by
        apply spMap_inj
        rw [spMap_comp', hβ', Category.assoc, hx]
      refine c.geom K x β' z hβ'.symm ?_
      rw [hz, ← e, ← hj]; rfl }

def up (j : B →+* B') (hj : j ζ = ζ') {s' : S ⟶ Sp B'} (c : SiegPre h k ζ (s' ≫ spMap j)) : SiegPre h k ζ' s' :=
  { A := c.A, ab := c.ab, P := c.P, isLB := c.isLB, rig₁ := c.rig₁, rig₂ := c.rig₂, symm := c.symm
    lev := c.lev, lev_add := c.lev_add, lev_tors := c.lev_tors
    geom := fun K _ _ x β z hx hz => by
      refine c.geom K x (β.comp j) z ?_ ?_
      · rw [spMap_comp', ← hx, Category.assoc]
      · rw [hz, ← hj]; rfl }

theorem siegPre_pull_ringChange : ∀ (h k : ℕ) (B B' : Type) [CommRing B] [CommRing B'] (ζ : B) (ζ' : B') (j : B →+* B') (S S' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (f : S' ⟶ S), j ζ = ζ' → f ≫ s = s' ≫ spMap j → (∀ c : SiegPre h k ζ s, ∃ c' : SiegPre h k ζ' s', SiegPB c' c f) ∧ (∀ (c : SiegPre h k ζ s) (c' : SiegPre h k ζ' s'), SiegPB c' c f → c.Principal → c'.Principal) ∧ ∀ c' : SiegPre h k ζ' s', ∃ c₀ : SiegPre h k ζ (s' ≫ spMap j), SiegPB c' c₀ (𝟙 _) ∧ SiegPB c₀ c' (𝟙 _) := by
  intro h k B B' _ _ ζ ζ' j S S' s s' f hj hf
  refine ⟨fun c => ?_, fun c c' hc hp => ?_, fun c' => ?_⟩
  · obtain ⟨c₀, h₀⟩ := (GlobalTheory.T.siegelObject_pullback_exists_and_principal h k B ζ S S' s _ f c hf).1
    exact ⟨up j hj c₀, h₀⟩
  · exact (GlobalTheory.T.siegelObject_pullback_exists_and_principal h k B ζ S S' s _ f c hf).2 (down j hj c') hc hp
  · have e := (GlobalTheory.T.siegelPullback_id_comp_cancel h k B' B' B' ζ' ζ' ζ' S' S' S' s' s' s' c' c' c' (𝟙 _) (𝟙 _)).1
    exact ⟨down j hj c', e, e⟩

end GlobalTheory.SiegelRingChange
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaCosetNonvanishingOfHasThStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaCosetNonvanishing_of_hasTh : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (n : ℕ) (R : Type) [CommRing R] (x : Sp R ⟶ S) (v : Ix g (N' ^ 2) → R) (q : Ideal R), 2 ≤ n → n ∣ N' → t.HasTh x v → q.IsPrime → Coset n N' v q := by
  first | exact @GlobalTheory.coset_of_hasTh | exact GlobalTheory.coset_of_hasTh | (intros; apply GlobalTheory.coset_of_hasTh <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaIdealPrimeAvoidingVariable
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.ZM

namespace GlobalTheory.ThetaPrime

theorem eval₂_smul_of_isHomogeneous {o K I : Type} [CommRing o] [CommRing K] (β : o →+* K)
    (v : I → K) (c : K) {F : MvPolynomial I o} {n : ℕ} (hF : F.IsHomogeneous n) :
    MvPolynomial.eval₂ β (c • v) F = c ^ n * MvPolynomial.eval₂ β v F := by
  classical
  rw [MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have h1 : ∑ i ∈ m.support, m i = n := by
    have := hF (MvPolynomial.mem_support_iff.1 hm)
    rw [← this, Finsupp.weight_apply, Finsupp.sum]
    simp
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, h1]
  ring

theorem exists_homogenisation {o I D : Type} [CommRing o] (a₀ : I) (a : D → I)
    (G : MvPolynomial D o) : ∃ (n : ℕ) (H : MvPolynomial I o),
      ∀ (K : Type) [Field K] (β : o →+* K) (v : I → K), v a₀ ≠ 0 →
        MvPolynomial.eval₂ β v H = v a₀ ^ n * MvPolynomial.eval₂ β (fun i => v (a i) / v a₀) G := by
  induction G using MvPolynomial.induction_on with
  | C c => exact ⟨0, MvPolynomial.C c, fun K _ β v _ => by simp⟩
  | add p q hp hq =>
    obtain ⟨n, H, hH⟩ := hp
    obtain ⟨m, H', hH'⟩ := hq
    refine ⟨n + m, MvPolynomial.X a₀ ^ m * H + MvPolynomial.X a₀ ^ n * H', fun K _ β v hv => ?_⟩
    simp only [MvPolynomial.eval₂_add, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_pow,
      MvPolynomial.eval₂_X, hH K β v hv, hH' K β v hv]
    ring
  | mul_X p i hp =>
    obtain ⟨n, H, hH⟩ := hp
    refine ⟨n + 1, H * MvPolynomial.X (a i), fun K _ β v hv => ?_⟩
    simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, hH K β v hv]
    field_simp
    ring

noncomputable def coneIdeal {o I Z : Type} [CommRing o] (em : o →+* ℂ) (B : Set Z) (θ : Z → I → ℂ) :
    Ideal (MvPolynomial I o) :=
  ⨅ (z : Z) (_ : z ∈ B) (c : ℂ) (_ : c ≠ 0), RingHom.ker (MvPolynomial.eval₂Hom em (c • θ z))

theorem mem_coneIdeal {o I Z : Type} [CommRing o] {em : o →+* ℂ} {B : Set Z} {θ : Z → I → ℂ}
    {F : MvPolynomial I o} : F ∈ coneIdeal em B θ ↔
      ∀ z ∈ B, ∀ c : ℂ, c ≠ 0 → MvPolynomial.eval₂ em (c • θ z) F = 0 := by
  simp [coneIdeal, Ideal.mem_iInf, RingHom.mem_ker]

theorem coneIdeal_isPrime {o I : Type} [CommRing o] [Countable o] [Countable I] (em : o →+* ℂ)
    {d : ℕ} {B : Set (Fin d → ℂ)} (θ : (Fin d → ℂ) → I → ℂ) (ho : IsOpen B)
    (hc : IsPreconnected B) (hn : B.Nonempty) (hd : ∀ a, DifferentiableOn ℂ (fun z => θ z a) B) :
    (coneIdeal em B θ).IsPrime := by
  obtain ⟨z, hz, c, hc0, h⟩ :=
    GlobalTheory.exists_veryGeneral_point_of_holomorphic_family o em I d B θ ho hc hn hd
  have : coneIdeal em B θ = RingHom.ker (MvPolynomial.eval₂Hom em (c • θ z)) := by
    ext F
    rw [mem_coneIdeal, RingHom.mem_ker, MvPolynomial.coe_eval₂Hom]
    exact ⟨fun hF => hF z hz c hc0, h F⟩
  rw [this]
  exact RingHom.ker_isPrime _

theorem exists_ratios {o I : Type} [CommRing o] [Finite I] (em : o →+* ℂ)
    (hem : Function.Injective em) {d : ℕ} {B : Set (Fin d → ℂ)} (θ : (Fin d → ℂ) → I → ℂ)
    (ho : IsOpen B) (hd : ∀ a, DifferentiableOn ℂ (fun z => θ z a) B)
    (hf : ∀ z ∈ B, {z' ∈ B | ∃ c : ℂ, θ z' = c • θ z}.Countable) (a₁ : I)
    (h₁ : MvPolynomial.X a₁ ∉ coneIdeal em B θ) :
    ∃ (a₀ : I) (a : Fin d → I), MvPolynomial.X a₀ ∉ coneIdeal em B θ ∧
      ∀ (K : Type) [Field K] (β : o →+* K) (v : I → K),
        RingHom.ker (MvPolynomial.eval₂Hom β v) = coneIdeal em B θ →
        ∀ G : MvPolynomial (Fin d) o, MvPolynomial.eval₂ β (fun i => v (a i) / v a₀) G = 0 →
          G = 0 := by
  rw [mem_coneIdeal] at h₁
  push Not at h₁
  obtain ⟨z₁, hz₁, c₁, -, h₁⟩ := h₁
  have h₁' : θ z₁ a₁ ≠ 0 := by
    intro h
    apply h₁
    simp [h]
  have hcont : ContinuousAt (fun z => θ z a₁) z₁ :=
    (hd a₁).continuousOn.continuousAt (ho.mem_nhds hz₁)
  have hU : {z | z ∈ B ∧ θ z a₁ ≠ 0} ∈ nhds z₁ :=
    Filter.inter_mem (ho.mem_nhds hz₁) (hcont.eventually_ne h₁')
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hU
  have hsub : Metric.ball z₁ ε ⊆ B := fun z hz => (hball hz).1
  obtain ⟨a₀, a, ⟨z₀, hz₀, h₀⟩, hind⟩ := GlobalTheory.CountableFibres.exists_independent_ratios d I
    (Metric.ball z₁ ε) θ Metric.isOpen_ball (convex_ball z₁ ε).isPreconnected
    ⟨z₁, Metric.mem_ball_self hε⟩ (fun a => (hd a).mono hsub)
    (fun z hz => ⟨fun h => (hball hz).2 (by rw [h]; rfl),
      Set.Countable.mono (fun z' hz' => And.intro (hsub hz'.1) hz'.2) (hf z (hsub hz))⟩)
  have hX : MvPolynomial.X a₀ ∉ coneIdeal em B θ := by
    intro h
    have := mem_coneIdeal.1 h z₀ (hsub hz₀) 1 one_ne_zero
    simp [h₀] at this
  refine ⟨a₀, a, hX, fun K _ β v hv G hG => ?_⟩
  have hv₀ : v a₀ ≠ 0 := by
    intro h
    apply hX
    rw [← hv, RingHom.mem_ker]
    simp [h]
  obtain ⟨n, H, hH⟩ := exists_homogenisation a₀ a G
  have hHP : H ∈ coneIdeal em B θ := by
    rw [← hv, RingHom.mem_ker, MvPolynomial.coe_eval₂Hom, hH K β v hv₀, hG, mul_zero]
  have hmap : MvPolynomial.map em G = 0 := by
    refine hind _ fun z hz hz0 => ?_
    have := mem_coneIdeal.1 hHP z (hsub hz) 1 one_ne_zero
    rw [one_smul, hH ℂ em _ hz0] at this
    rw [MvPolynomial.eval_map]
    exact (mul_eq_zero.1 this).resolve_left (pow_ne_zero _ hz0)
  exact MvPolynomial.map_injective em hem (by rw [hmap, map_zero])

theorem countable_of_finiteType (o : Type) [CommRing o] (h : Algebra.FiniteType ℤ o) :
    Countable o := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 h
  have : Countable (MvPolynomial (Fin n) ℤ) := by
    rw [← Cardinal.mk_le_aleph0_iff]
    exact MvPolynomial.cardinalMk_le_max.trans (by simp)
  exact hf.countable

theorem span_range_eq_top {K I : Type} [Field K] {v : I → K} (hv : v ≠ 0) :
    Ideal.span (Set.range v) = ⊤ := by
  obtain ⟨a, ha⟩ := Function.ne_iff.1 hv
  exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨a, rfl⟩) (IsUnit.mk0 _ ha)

theorem exists_prime_independent_ratios : Out.Laws → Out.Laws2 → ∀ (g N' : ℕ) (J : Type) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ) (w w' : J) (o : Type) [CommRing o] (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (C : TObj g (N' ^ 2) J b (spMap em) → Prop) (d : ℕ), ArBase em → GoodClass em C Mat κ w w' d → ∀ (p : Ideal (MvPolynomial (Ix g (N' ^ 2)) o)) (a₁ : Ix g (N' ^ 2)), N' ≠ 0 → p.IsPrime → thIdeal em C ≤ p → MvPolynomial.X a₁ ∉ p → ∃ (P : Ideal (MvPolynomial (Ix g (N' ^ 2)) o)) (a₀ : Ix g (N' ^ 2)) (a : Fin d → Ix g (N' ^ 2)), P.IsPrime ∧ thIdeal em C ≤ P ∧ P ≤ p ∧ MvPolynomial.X a₀ ∉ P ∧ ∀ (K : Type) [Field K] (β : o →+* K) (v : Ix g (N' ^ 2) → K), RingHom.ker (MvPolynomial.eval₂Hom β v) = P → ∀ G : MvPolynomial (Fin d) o, MvPolynomial.eval₂ β (fun i => v (a i) / v a₀) G = 0 → G = 0 := by
  intro hL hL2 g N' J Mat κ w w' o _ b em C d hAr hG p a₁ hN hp hle hX
  obtain ⟨-, hft, hem⟩ := hAr
  have : Countable o := countable_of_finiteType o hft
  have : NeZero (N' ^ 2) := ⟨pow_ne_zero _ hN⟩
  obtain ⟨r, B, θ, hfam, hcov⟩ := hG.fam
  have hmem : ∀ F, F ∈ thIdeal em C ↔ ∀ t v, C t → t.HasTh (𝟙 _) v →
      MvPolynomial.eval₂ em v F = 0 := by
    intro F
    simp [thIdeal, Ideal.mem_iInf, RingHom.mem_ker]
  have hinf : (Finset.univ : Finset (Fin r)).inf (fun i => coneIdeal em (B i) (θ i)) ≤ p := by
    refine le_trans (fun F hF => ?_) hle
    rw [hmem]
    intro t v ht hv
    obtain ⟨i, z, hz, hθ⟩ := hcov t ht
    have hFi : F ∈ coneIdeal em (B i) (θ i) :=
      (Finset.inf_le (f := fun i => coneIdeal em (B i) (θ i)) (Finset.mem_univ i)) hF
    have key : ∃ c : ℂ, c ≠ 0 ∧ v = c • θ i z := by
      by_cases h0 : θ i z = 0
      · refine ⟨1, one_ne_zero, ?_⟩
        by_contra hne
        rw [h0, smul_zero] at hne
        obtain ⟨u, hu⟩ := GlobalTheory.hasTh_unique_unit hL hL2 o g N' J b _ _ t ℂ _ v (θ i z) hv hθ
          (span_range_eq_top hne)
        apply hne
        funext a
        have := hu a
        rw [h0] at this
        simpa using this
      · obtain ⟨u, hu⟩ := GlobalTheory.hasTh_unique_unit hL hL2 o g N' J b _ _ t ℂ _ (θ i z) v hθ hv
          (span_range_eq_top h0)
        exact ⟨u, u.ne_zero, funext hu⟩
    obtain ⟨c, hc, rfl⟩ := key
    exact mem_coneIdeal.1 hFi z hz c hc
  obtain ⟨i, -, hi⟩ := hp.inf_le'.1 hinf
  obtain ⟨ho, hc, hd, hz⟩ := hfam i
  have hX' : MvPolynomial.X a₁ ∉ coneIdeal em (B i) (θ i) := fun h => hX (hi h)
  have hn : (B i).Nonempty := by
    by_contra hne
    apply hX'
    rw [mem_coneIdeal]
    intro z hz
    exact absurd ⟨z, hz⟩ hne
  obtain ⟨a₀, a, h₀, hind⟩ := exists_ratios em hem (θ i) ho hd (fun z hz' => (hz z hz').2) a₁ hX'
  refine ⟨_, a₀, a, coneIdeal_isPrime em (θ i) ho hc hn hd, fun F hF => ?_, hi, h₀, hind⟩
  rw [mem_coneIdeal]
  intro z hz' c _
  obtain ⟨t, ht, hθ⟩ := (hz z hz').1
  have hcomp := (GlobalTheory.ZM.ThIdeal.thIdeal_radical_homogeneous_torsionFree o g N' J b em C hem).2.1 F hF
  rw [← MvPolynomial.sum_homogeneousComponent F, MvPolynomial.eval₂_sum]
  refine Finset.sum_eq_zero fun e _ => ?_
  rw [eval₂_smul_of_isHomogeneous em _ c (MvPolynomial.homogeneousComponent_isHomogeneous e F),
    (hmem _).1 (hcomp e) t _ ht hθ, mul_zero]

end GlobalTheory.ThetaPrime
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionSectionExtendsAbLocus
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory

theorem exists_section_of_pow_eq_one {T V : Scheme.{0}} [IsLocallyNoetherian T] (hT : Geo.Tor.IsNormalScheme T)
    (j : V ⟶ T) [IsPreimmersion j] [Flat j] [IsDominant j] [QuasiCompact j]
    (G : Over T) [GrpObj G] [IsCommMonObj G] [IsProper G.hom] (n : ℕ) (hn : IsUnit (n : Γ(T, ⊤)))
    (P : Over T) (x : P ⟶ G) (hx : x ^ n = 1) (k : V ⟶ P.left) (hk : k ≫ P.hom = j) :
    ∃ σ : T ⟶ G.left, σ ≫ G.hom = 𝟙 T ∧ j ≫ σ = k ≫ x.left := by
  have hw : (Out.mulA G n).left ≫ G.hom = G.hom := Over.w _
  have h₁ : FormallyUnramified (Out.mulA G n).left := formallyUnramified_mulA T G n hn
  have h₂ : IsProper ((Out.mulA G n).left ≫ G.hom) := by rw [hw]; infer_instance
  have h₃ : IsProper (Out.mulA G n).left := IsProper.of_comp _ G.hom
  have h₄ : LocallyQuasiFinite (Out.mulA G n).left := by
    refine ⟨fun {U} hU {W} hW e => ?_⟩
    have a₁ := (Out.mulA G n).left.formallyUnramified_appLE hU hW e
    have a₂ := (Out.mulA G n).left.finiteType_appLE hU hW e
    algebraize [((Out.mulA G n).left.appLE U W e).hom]
    exact inferInstanceAs (Algebra.QuasiFinite _ _)
  have h₅ : IsFinite (Out.mulA G n).left := .of_isProper_of_locallyQuasiFinite _
  have e₁ : x ≫ Out.mulA G n = toUnit P ≫ η[G] := by
    rw [Out.mulA, MonObj.comp_pow, Category.comp_id, hx, Hom.one_def]
  have e₂ : x.left ≫ (Out.mulA G n).left = P.hom ≫ (η[G]).left := by
    rw [← Over.comp_left, e₁]; simp
  obtain ⟨σ, ⟨a, b⟩, -⟩ := existsUnique_lift_of_densePart T V G.left G.left j hT ‹_› ‹_› ‹_› ‹_›
    (Out.mulA G n).left (η[G]).left (k ≫ x.left) inferInstance
    (by rw [Category.assoc, e₂, ← hk, Category.assoc])
  refine ⟨σ, ?_, a⟩
  rw [← hw, reassoc_of% b]
  exact Over.w η[G]

theorem torsion_section_extends_abLocus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), IsDedFrac β → AbOpen Y.t.G → ∃ U : Y.X.Opens, (U : Set Y.X) = abLocus Y.t.G ∧ ∀ (σ : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G) (n : ℕ), IsUnit (n : O) → σ ^ n = 1 → Y.Extends U σ := by
  intro E _ _ _ H D l Xo c O _ β Y ⟨⟨_, hD⟩, _, hF⟩ ⟨U, hU, hP⟩
  refine ⟨U, hU, fun σ n hn hσ => ?_⟩
  letI : Algebra O c.F := β.toAlgebra
  obtain ⟨hN, -, -, j₁, j₂, j₃, j₄⟩ := genericPart_dense_proOpen O c.F Y.X (Xo.XF c) Y.s Y.jQ Y.flat Y.proj
    Y.jQ_open Y.jQ_dense
  replace j₁ : IsPreimmersion Y.j := j₁
  replace j₂ : Flat Y.j := j₂
  replace j₃ : IsDominant Y.j := j₃
  replace j₄ : QuasiCompact Y.j := j₄
  have hr : Set.range Y.j ⊆ Set.range U.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι, hU]
    have : Y.jQ x ∈ pullback.fst Y.s (spMap β) ⁻¹' abLocus Y.t.G := by
      rw [Y.ab_gen]; exact ⟨_, rfl⟩
    exact this
  let j : Xo.XF c ⟶ U.toScheme := IsOpenImmersion.lift U.ι Y.j hr
  have hj : j ≫ U.ι = Y.j := IsOpenImmersion.lift_fac _ _ _
  have sq : IsPullback (𝟙 _) j Y.j U.ι := IsPullback.of_horiz_isIso_mono ⟨by simp [hj]⟩
  have k₁ : IsPreimmersion j := MorphismProperty.of_isPullback (P := @IsPreimmersion) sq j₁
  have k₂ : Flat j := MorphismProperty.of_isPullback (P := @Flat) sq j₂
  have k₄ : QuasiCompact j := MorphismProperty.of_isPullback (P := @QuasiCompact) sq j₄
  have k₃ : IsDominant j := by
    constructor
    have hd := Dense.preimage j₃.denseRange U.ι.isOpenEmbedding.isOpenMap
    refine hd.mono ?_
    rintro y ⟨x, hx⟩
    refine ⟨x, U.ι.isOpenEmbedding.injective ?_⟩
    rw [← hx, ← hj]; rfl
  have hT : Geo.Tor.IsNormalScheme U.toScheme := fun x => by
    obtain ⟨_, _⟩ := Y.normal (U.ι x)
    let e := (asIso (U.ι.stalkMap x)).commRingCatIsoToRingEquiv
    exact ⟨e.symm.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e⟩
  have hn' : IsUnit (n : Γ(U.toScheme, ⊤)) := by
    simpa using hn.map ((U.ι ≫ Y.s).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom)
  let G : Over U.toScheme := (Over.pullback U.ι).obj Y.t.G
  have hG : IsProper G.hom := by
    have : IsProper ((pullbackRestrictIsoRestrict Y.t.G.hom U).inv ≫ pullback.snd Y.t.G.hom U.ι) := hP
    exact (MorphismProperty.cancel_left_of_respectsIso @IsProper _ _).mp this
  have gp := isGrpPullback_pullback Y.t.G U.ι
  have hc := Y.m.cart
  let ψ : Y.oF.t.G.left ⟶ G.left := gp.1.lift Y.m.φ (Y.oF.t.G.hom ≫ j)
    (by rw [Category.assoc, hj]; exact hc.1.w)
  have hψ : ψ ≫ pullback.fst Y.t.G.hom U.ι = Y.m.φ := gp.1.lift_fst _ _ _
  have gq : IsGrpPullback Y.oF.t.G G j ψ :=
    gp.cancel (by rw [hψ, hj]; exact hc) (gp.1.lift_snd _ _ _)
  obtain ⟨s, hs₁, hs₂⟩ := exists_section_of_pow_eq_one hT j G n hn' _ (pushHom gq _ σ)
    (by rw [← map_pow, hσ, map_one]) (𝟙 _) ((Category.id_comp _).trans (Category.id_comp _))
  refine ⟨s ≫ pullback.fst Y.t.G.hom U.ι, ?_, fun j' hj' => ?_⟩
  · rw [Category.assoc, gp.1.w, reassoc_of% hs₁]
  · obtain rfl : j' = j := by rw [← cancel_mono U.ι, hj, hj']
    rw [reassoc_of% hs₂, ← hψ]
    exact Category.assoc _ _ _

end GlobalTheory
end

