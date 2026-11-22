import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0004
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0002
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0011
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0042
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0077
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0018
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0078
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import Formalism.LocalToGlobal.ProjectiveLattices.RulInst
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0071
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HodgeIPIffHodgeFormConj
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimeDivisorsOfOmegaBundle
section
open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)

namespace GlobalTheory.CompanionTheory.Ar.TieOfOrigin

theorem sum_fundOnRoot {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} {G : Type} [AddCommGroup G]
    (f : Ψ × Fin N → G) (a : Ψ × Fin N) :
    ∑ r, fundOnRoot a r • f r = -∑ k ∈ Finset.Iic a.2, f (a.1, k) := by
  rw [Fintype.sum_prod_type, Finset.sum_eq_single a.1]
  · rw [← Finset.sum_neg_distrib, ← Finset.sum_subset (Finset.subset_univ (Finset.Iic a.2))]
    · refine Finset.sum_congr rfl fun k hk => ?_
      simp [fundOnRoot, Finset.mem_Iic.mp hk]
    · intro k _ hk
      have hk' : ¬ k ≤ a.2 := fun h => hk (Finset.mem_Iic.mpr h)
      simp [fundOnRoot, hk']
  · intro τ _ hτ
    simp [fundOnRoot, hτ]
  · simp

theorem log_combLine {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {J : Type} [Fintype J]
    (ℓ : J → HermLine ι) (n : J → ℤ) (z : (Σ k, ι k) → ℂ) (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    Real.log ((Top.combLine ℓ n).h z) = ∑ j, n j • Real.log ((ℓ j).h z) := by
  show Real.log (∏ j, (ℓ j).h z ^ n j) = _
  rw [Real.log_prod fun j _ => (zpow_pos ((ℓ j).pos z hz) _).ne']
  simp [Real.log_zpow]

theorem sum_rootOnFund {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} (f g : Ψ × Fin N → ℝ)
    (h : ∀ a, g a = -∑ k ∈ Finset.Iic a.2, f (a.1, k)) (r : Ψ × Fin N) :
    ∑ a, rootOnFund r a • g a = f r := by
  have h1 : ∀ a, g a = ∑ r', fundOnRoot a r' • f r' := fun a => by rw [h, sum_fundOnRoot]
  simp only [h1, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, (rootOnFund_mul_fundOnRoot_inverse Ψ N r _).1]
  simp

end GlobalTheory.CompanionTheory.Ar.TieOfOrigin

open GlobalTheory.CompanionTheory.Ar.TieOfOrigin in
theorem GlobalTheory.CompanionTheory.Ar.hodgeTie_of_rootOrigin : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (RM : Top.RootModel (CMType H) (D.p + D.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (Or : RootOrigin Y S RM Fx), Or.𝔐.OmVB → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ NumberField.discr E → p ∈ S) → AlgOver (Or.Re.comap some) → ∃ T : HodgeTie Y S (Module.finrank ℚ c.F) RM, T.A = Or.𝔐 := by
  intro E _ _ _ H D l Xo c O _ β Y S RM Sys Fx Or hvb hdiscr halg
  refine ⟨{ A := Or.𝔐, Fl := Or.Fl, e := Or.e, roots := Or.lines, sing := Or.sing, sing_deg := Or.sing_deg
            hodge := Or.hodge, Sy := Sys.comap some, Re := Or.Re.comap some, alg := halg
            ref_deg := ?_, sing_eq := ?_, line_eq := ?_, δ_eq := Or.δ_eq, discr := hdiscr
            ht_vb := fun p hp s => (hvb p hp).2 s }, rfl⟩
  · rintro ⟨τ, i⟩
    refine (Or.fund_deg τ i).trans ?_
    refine Eq.trans ?_ (@sum_fundOnRoot _ _ (_) _ _ _ (fun r => (Or.sing r).a) (τ, i)).symm
    simp only [Or.sing_deg]
  · rintro ⟨τ, i⟩ x hx
    have hz := (Or.Re.R.mem x x (Or.Re.R.mem_U x)).1
    refine (log_combLine _ _ _ hz).trans ?_
    refine (@sum_fundOnRoot _ _ (_) _ _ _ (fun r => Real.log ((Or.sing r).h (Or.Re.R.lift x x))) (τ, i)).trans ?_
    exact (Or.fund_sing τ i x hx).symm
  · have h0 : 0 < Sys.t₀ := (Sys.reg none).1
    filter_upwards [Ioc_mem_nhdsGT h0] with t ht r z hz
    refine Real.log_injOn_pos ((RM.x t r).pos z hz.1) (HermLine.pos _ z hz.1) ?_
    refine Eq.trans ?_ (log_combLine _ _ _ hz.1).symm
    exact (@sum_rootOnFund _ _ (_) _ (fun r => Real.log ((RM.x t r).h z))
      (fun a => Real.log ((Or.Re.line (some a) t).h z))
      (fun a => Or.fund_reg a.1 a.2 t ht.1 ht.2 z hz) r).symm
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularRingDeterminesComponentStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_ring_determines_component : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (o : Type) [CommRing o] [Algebra o Ω] (κ : Type) (x : κ → Ω), CoordTie o ξ x → ∀ p q : Cpt ξ, regAt ξ p = regAt ξ q → p = q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncBase.eq_of_regAt_eq_of_coordTie | exact GlobalTheory.CompanionTheory.Ar.SncBase.eq_of_regAt_eq_of_coordTie | (intros; apply GlobalTheory.CompanionTheory.Ar.SncBase.eq_of_regAt_eq_of_coordTie <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularRingsEqualImagesEqualStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_rings_equal_images_equal : ∀ (P X₁ X₂ : Scheme.{0}) (Ω : Type) [Field Ω] (ξ₀ : Sp Ω ⟶ P) (ξ₁ : Sp Ω ⟶ X₁) (ξ₂ : Sp Ω ⟶ X₂) (f₁ : X₁ ⟶ P) (f₂ : X₂ ⟶ P) (o : Type) [CommRing o] [Algebra o Ω] (κ : Type) (u : κ → Ω), CoordTie o ξ₀ u → IsCptGen ξ₁ → IsCptGen ξ₂ → ξ₁ ≫ f₁ = ξ₀ → ξ₂ ≫ f₂ = ξ₀ → ∀ (p₁ : Cpt ξ₁) (p₂ : Cpt ξ₂), regAt ξ₁ p₁ = regAt ξ₂ p₂ → f₁ p₁.1 = f₂ p₂.1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncBase.image_eq_of_regAt_eq | exact GlobalTheory.CompanionTheory.Ar.SncBase.image_eq_of_regAt_eq | (intros; apply GlobalTheory.CompanionTheory.Ar.SncBase.image_eq_of_regAt_eq <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SmoothAdjoinInverse
section
namespace GlobalTheory.CompanionTheory.Ar.SncBase.Mdl

theorem isLocalizationAway_invAdj {Ω : Type} [Field Ω] [Algebra ℚ Ω] {A : Subalgebra ℚ Ω} {g : Ω}
    (hg : g ∈ A) (h0 : g ≠ 0) :
    letI : Algebra A (invAdj A g) := (Subalgebra.inclusion (le_invAdj A g)).toRingHom.toAlgebra
    IsLocalization.Away (⟨g, hg⟩ : A) (invAdj A g) := by
  letI : Algebra A (invAdj A g) := (Subalgebra.inclusion (le_invAdj A g)).toRingHom.toAlgebra
  have hmap : ∀ a : A, ((algebraMap A (invAdj A g) a : invAdj A g) : Ω) = a := fun _ => rfl
  refine IsLocalization.Away.mk (⟨g, hg⟩ : A) ?_ ?_ ?_
  · refine IsUnit.of_mul_eq_one (⟨g⁻¹, inv_mem_invAdj A g⟩ : invAdj A g) (Subtype.ext ?_)
    simp [hmap, h0]
  · intro s
    obtain ⟨k, hk⟩ := exists_mul_pow_mem hg h0 s.2
    refine ⟨k, ⟨_, hk⟩, Subtype.ext ?_⟩
    simp [hmap]
  · intro a b hab
    have hab' : a = b := Subtype.ext (by simpa [hmap] using congrArg Subtype.val hab)
    exact ⟨0, by rw [hab']⟩

theorem smooth_invAdj : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (A : Subalgebra ℚ Ω) (g : Ω), g ∈ A → g ≠ 0 →
    Algebra.Smooth ℚ A → Algebra.Smooth ℚ (invAdj A g) := by
  intro Ω _ _ A g hg h0 hA
  letI : Algebra A (invAdj A g) := (Subalgebra.inclusion (le_invAdj A g)).toRingHom.toAlgebra
  haveI : IsScalarTower ℚ A (invAdj A g) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsLocalization.Away (⟨g, hg⟩ : A) (invAdj A g) := isLocalizationAway_invAdj hg h0
  haveI : Algebra.Smooth A (invAdj A g) := Algebra.Smooth.of_isLocalization_Away (⟨g, hg⟩ : A)
  exact Algebra.Smooth.comp ℚ A (invAdj A g)

end GlobalTheory.CompanionTheory.Ar.SncBase.Mdl
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SmoothOpenImmersionRangeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_open_immersion_range : ∀ (A B T : Scheme.{0}) (j : A ⟶ B) [IsOpenImmersion j] (g : B ⟶ T) (n : ℕ), SmoothOfRelativeDimension n (j ≫ g) → SmoothOfRelativeDimension n (j.opensRange.ι ≫ g) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncBase.smoothOfRelativeDimension_opensRange_ι_comp | exact GlobalTheory.CompanionTheory.Ar.SncBase.smoothOfRelativeDimension_opensRange_ι_comp | (intros; apply GlobalTheory.CompanionTheory.Ar.SncBase.smoothOfRelativeDimension_opensRange_ι_comp <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SmoothSchemeStalksDomainsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_scheme_stalks_domains : ∀ (K : Type) [Field K] (e : ℕ) (X : Scheme.{0}) (g : X ⟶ Sp K), SmoothOfRelativeDimension e g → ∀ x : X, IsDomain (X.presheaf.stalk x) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncBase.isDomain_stalk_of_smoothOfRelativeDimension_field | exact GlobalTheory.CompanionTheory.Ar.SncBase.isDomain_stalk_of_smoothOfRelativeDimension_field | (intros; apply GlobalTheory.CompanionTheory.Ar.SncBase.isDomain_stalk_of_smoothOfRelativeDimension_field <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncModelFromLocalPatches
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SncBase.Mdl

section Core

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {N : ℕ}

theorem chartQ_ratEval_mem (x : Fin (N + 1) → Ω) (c : Fin (N + 1))
    (g : MRing (fun _ : Unit => Fin (N + 1))) : ratEval x c g ∈ chartQ x c := by
  induction g using MvPolynomial.induction_on with
  | C a => simpa using intCast_mem (chartQ x c) a
  | add a b ha hb => simpa using (chartQ x c).add_mem ha hb
  | mul_X a i ha =>
    have hi : x i.2 / x c ∈ chartQ x c := Algebra.subset_adjoin ⟨i.2, rfl⟩
    simpa using (chartQ x c).mul_mem ha hi

theorem adjoin_insert_eq_invAdj (R : Set Ω) (h : Ω) :
    Algebra.adjoin ℚ (insert h⁻¹ R) = invAdj (Algebra.adjoin ℚ R) h := by
  apply le_antisymm
  · exact Algebra.adjoin_mono (Set.insert_subset_insert Algebra.subset_adjoin)
  · refine Algebra.adjoin_le (Set.insert_subset (Algebra.subset_adjoin (Set.mem_insert _ _)) ?_)
    exact fun _ hs => Algebra.adjoin_mono (Set.subset_insert _ _) hs

theorem exists_sum_eq_one_of_span_eq_top {R : Type} [CommRing R] (T : Set R) (hT : Ideal.span T = ⊤) :
    ∃ (m : ℕ) (f a : Fin m → R), (∀ l, f l ∈ T) ∧ ∑ l, a l * f l = 1 := by
  classical
  have h1 : (1 : R) ∈ Ideal.span T := hT ▸ Submodule.mem_top
  obtain ⟨w, hw, hs⟩ := Submodule.mem_span_set.1 h1
  let ε := w.support.equivFin
  refine ⟨w.support.card, fun l => (ε.symm l : R), fun l => w (ε.symm l), fun l => hw (ε.symm l).2, ?_⟩
  rw [← hs, Finsupp.sum, ← Finset.sum_coe_sort w.support (fun i => w i • i)]
  exact Equiv.sum_comp ε.symm (fun i : w.support => w i • (i : R))

theorem chart_cover_core {P : Type} (u : P → Ω → Prop) (hu0 : ∀ p h, u p h → h ≠ 0) (C B : Set P)
    (Pt Bd : Set (Subring Ω)) (x : Fin (N + 1) → Ω) (c : Fin (N + 1)) (e : ℕ)
    (bd : Ideal (MRing (fun _ : Unit => Fin (N + 1))))
    (h1 : ∀ p ∈ C, ∃ h ∈ chartQ x c, u p h ∧ ∃ (z : Fin e → invAdj (chartQ x c) h) (n : ℕ),
      IsSncPatch Pt Bd e (invAdj (chartQ x c) h) z n)
    (h2 : ∀ I : Ideal (chartQ x c), I.IsPrime → ∃ p ∈ C, ∀ s : chartQ x c, s ∉ I ↔ u p (s : Ω))
    (h3 : ∀ h, h ∈ chartQ x c → h ≠ 0 → ∀ q : Ideal (invAdj (chartQ x c) h), q.IsPrime →
      ∃ p ∈ C, (∀ s : invAdj (chartQ x c) h, s ∉ q ↔ u p (s : Ω)) ∧
        ∀ (z : Fin e → invAdj (chartQ x c) h) (n : ℕ), IsSncPatch Pt Bd e (invAdj (chartQ x c) h) z n →
          (p ∈ B ↔ ∃ i : Fin e, (i : ℕ) < n ∧ z i ∈ q))
    (h4 : ∀ p ∈ C, (p ∈ B ↔ ∀ g ∈ bd, ¬ u p (ratEval x c g))) :
    ∃ (m : ℕ) (f a : Fin m → Ω), (∀ l, f l ∈ chartQ x c) ∧ (∀ l, a l ∈ chartQ x c) ∧
      ∑ l, a l * f l = 1 ∧ ∀ l, f l ≠ 0 → ∀ S : Subalgebra ℚ Ω,
        S = Algebra.adjoin ℚ (insert (f l)⁻¹ (Set.range fun j => x j / x c)) →
        Algebra.Smooth ℚ S ∧ ∃ (z : Fin e → S) (n : ℕ), n ≤ e ∧
          LinearIndependent S (fun i => KaehlerDifferential.D ℚ S (z i)) ∧
          Submodule.span S (Set.range fun i => KaehlerDifferential.D ℚ S (z i)) = ⊤ ∧
          ∀ q : Ideal S, q.IsPrime →
            ((∀ g ∈ bd, ∀ s : S, (s : Ω) = ratEval x c g → s ∈ q) ↔
              ∃ i : Fin e, (i : ℕ) < n ∧ z i ∈ q) := by
  let T : Set (chartQ x c) := {t | (t : Ω) ≠ 0 ∧ ∃ (z : Fin e → invAdj (chartQ x c) (t : Ω)) (n : ℕ),
    IsSncPatch Pt Bd e (invAdj (chartQ x c) (t : Ω)) z n}
  have hT : Ideal.span T = ⊤ := by
    by_contra hne
    obtain ⟨I, hI, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨p, hp, hs⟩ := h2 I hI.isPrime
    obtain ⟨h, hh, hu, z, n, hz⟩ := h1 p hp
    have hmem : (⟨h, hh⟩ : chartQ x c) ∈ T := ⟨hu0 p h hu, z, n, hz⟩
    exact (hs ⟨h, hh⟩).2 hu (hle (Ideal.subset_span hmem))
  obtain ⟨m, f, a, hf, hsum⟩ := exists_sum_eq_one_of_span_eq_top T hT
  refine ⟨m, fun l => f l, fun l => a l, fun l => (f l).2, fun l => (a l).2, ?_, ?_⟩
  · have := congrArg (Subtype.val) hsum
    simpa using this
  · intro l hl S hS
    rw [adjoin_insert_eq_invAdj] at hS
    subst hS
    obtain ⟨-, z, n, hz⟩ := hf l
    refine ⟨hz.smooth, z, n, hz.le, hz.li, hz.span, fun q hq => ?_⟩
    obtain ⟨p, hp, hs, hb⟩ := h3 _ (f l).2 hl q hq
    rw [← hb z n hz, h4 p hp]
    constructor
    · intro H g hg hu
      exact (hs ⟨ratEval x c g, le_invAdj _ _ (chartQ_ratEval_mem x c g)⟩).2 hu (H g hg _ rfl)
    · intro H g hg s hsg
      by_contra hn
      exact H g hg (hsg ▸ (hs s).1 hn)

end Core

theorem range_ratios_unit {Ω : Type} [Field Ω] {N : ℕ} (x : Fin (N + 1) → Ω) (c : Unit → Fin (N + 1)) :
    (Set.range fun p : (Σ _ : Unit, Fin (N + 1)) => x p.2 / x (c p.1)) =
      Set.range fun j => x j / x (c ()) := by
  ext w
  constructor
  · rintro ⟨⟨_, j⟩, rfl⟩
    exact ⟨j, rfl⟩
  · rintro ⟨j, rfl⟩
    exact ⟨⟨(), j⟩, rfl⟩

theorem isSncModel_of_chart_patches : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (X : Scheme.{0}) (ξ : Sp Ω ⟶ X) (N : ℕ) (x : Fin (N + 1) → Ω) (e : ℕ) (B : Set (Cpt ξ)) (bd : Ideal (MRing (fun _ : Unit => Fin (N + 1)))), (∀ c (p : Cpt ξ), Char0 ξ p → InChart ξ x c p → ∃ h ∈ Mdl.chartQ x c, unitAt ξ p h ∧ ∃ (z : Fin e → Mdl.invAdj (Mdl.chartQ x c) h) (n : ℕ), IsSncPatch (Pts ξ) (regAt ξ '' B) e (Mdl.invAdj (Mdl.chartQ x c) h) z n) → (∀ c, x c ≠ 0 → ∀ I : Ideal (Mdl.chartQ x c), I.IsPrime → ∃ p : Cpt ξ, Char0 ξ p ∧ InChart ξ x c p ∧ ∀ s : Mdl.chartQ x c, s ∉ I ↔ unitAt ξ p (s : Ω)) → (∀ c h, x c ≠ 0 → h ∈ Mdl.chartQ x c → h ≠ 0 → ∀ q : Ideal (Mdl.invAdj (Mdl.chartQ x c) h), q.IsPrime → ∃ p : Cpt ξ, Char0 ξ p ∧ InChart ξ x c p ∧ (∀ s : Mdl.invAdj (Mdl.chartQ x c) h, s ∉ q ↔ unitAt ξ p (s : Ω)) ∧ ∀ (z : Fin e → Mdl.invAdj (Mdl.chartQ x c) h) (n : ℕ), IsSncPatch (Pts ξ) (regAt ξ '' B) e (Mdl.invAdj (Mdl.chartQ x c) h) z n → (p ∈ B ↔ ∃ i : Fin e, (i : ℕ) < n ∧ z i ∈ q)) → (∀ c (p : Cpt ξ), Char0 ξ p → InChart ξ x c p → (p ∈ B ↔ ∀ g ∈ bd, ¬ unitAt ξ p (Mdl.ratEval x c g))) → Cmp.IsSncModel (fun p : (Σ _ : Unit, Fin (N + 1)) => x p.2) e bd := by
  intro Ω _ _ X ξ N x e B bd h1 h2 h3 h4
  unfold Cmp.IsSncModel
  intro c hc
  have hx : x (c ()) ≠ 0 := hc ()
  have key := chart_cover_core (P := Cpt ξ) (fun p h => unitAt ξ p h) (fun p h hh => hh.1)
    {p | Char0 ξ p ∧ InChart ξ x (c ()) p} B (Pts ξ) (regAt ξ '' B) x (c ()) e bd
    (fun p hp => h1 _ p hp.1 hp.2)
    (fun I hI => by
      obtain ⟨p, a, b, d⟩ := h2 _ hx I hI
      exact ⟨p, ⟨a, b⟩, d⟩)
    (fun h hh h0 q hq => by
      obtain ⟨p, a, b, d, f⟩ := h3 _ h hx hh h0 q hq
      exact ⟨p, ⟨a, b⟩, d, f⟩)
    (fun p hp => h4 _ p hp.1 hp.2)
  beta_reduce
  rw [range_ratios_unit x c]
  exact key

end GlobalTheory.CompanionTheory.Ar.SncBase.Mdl
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncPatchBoundaryUnits
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SncBase.Mdl

theorem unitAt_finsetProd {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {p : Cpt ξ}
    {I : Type} (s : Finset I) (f : I → Ω) (hf : ∀ i ∈ s, unitAt ξ p (f i)) :
    unitAt ξ p (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using unitAt_one ξ p
  | insert i s hi ih =>
    rw [Finset.prod_insert hi]
    exact unitAt_mul (hf i (Finset.mem_insert_self i s))
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

theorem unitAt_of_finsetProd {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {p : Cpt ξ}
    {I : Type} (s : Finset I) (f : I → Ω) (hf : ∀ i ∈ s, f i ∈ regAt ξ p)
    (hu : unitAt ξ p (∏ i ∈ s, f i)) {i : I} (hi : i ∈ s) : unitAt ξ p (f i) := by
  classical
  rw [← Finset.mul_prod_erase s f hi] at hu
  exact unitAt_of_mul_left hu (hf i hi)
    (prod_mem fun j hj => hf j (Finset.mem_of_mem_erase hj))

theorem exists_chartQ_unit_sep (Ω : Type) [Field Ω] [CharZero Ω] (X : Scheme.{0}) (ξ : Sp Ω ⟶ X)
    (κ : Type) (x : κ → Ω) (c : κ) (B : Set (Cpt ξ)) (h : Ω) (e n : ℕ)
    (z : Fin e → Mdl.invAdj (Mdl.chartQ x c) h) (p : Cpt ξ) (_hξ : IsCptGen ξ)
    (hB : ∀ q ∈ B, Char0 ξ q) (hh : h ∈ Mdl.chartQ x c) (h0 : h ≠ 0)
    (hcl : ∀ q : Cpt ξ, Char0 ξ q → InChart ξ x c q → unitAt ξ q h →
      (q ∈ B ↔ ∃ i : Fin e, (i : ℕ) < n ∧ ¬ unitAt ξ q (z i : Ω)))
    (hp : Char0 ξ p) (hpc : InChart ξ x c p) (hph : unitAt ξ p h) (hpB : p ∉ B) :
    ∃ a ∈ Mdl.chartQ x c, unitAt ξ p a ∧ ∀ q ∈ B, InChart ξ x c q → ¬ unitAt ξ q a := by
  classical
  set S : Finset (Fin e) := Finset.univ.filter fun i => (i : ℕ) < n with hS
  set f : Fin e → Ω := fun i => (z i : Ω) with hf
  set ζ : Ω := ∏ i ∈ S, f i with hζ
  have hζm : ζ ∈ Mdl.invAdj (Mdl.chartQ x c) h :=
    Subalgebra.prod_mem _ fun i _ => (z i).2
  obtain ⟨m, hm⟩ := exists_mul_pow_mem hh h0 hζm
  refine ⟨ζ * h ^ m * h, (Mdl.chartQ x c).mul_mem hm hh, ?_, ?_⟩
  · have hz : ∀ i ∈ S, unitAt ξ p (f i) := by
      intro i hi
      by_contra hni
      exact hpB ((hcl p hp hpc hph).2 ⟨i, (Finset.mem_filter.1 hi).2, hni⟩)
    exact unitAt_mul (unitAt_mul (unitAt_finsetProd S f hz) (unitAt_pow hph m)) hph
  · intro q hq hqc hua
    have hq0 := hB q hq
    have hA : ∀ s ∈ Mdl.chartQ x c, s ∈ regAt ξ q := fun s hs => chartQ_le hq0 hqc hs
    by_cases hqh : unitAt ξ q h
    · obtain ⟨i, hin, hni⟩ := (hcl q hq0 hqc hqh).1 hq
      have hreg : ∀ j ∈ S, f j ∈ regAt ξ q := fun j _ => invAdj_le hq0 hA hqh (z j).2
      have hζr : ζ ∈ regAt ξ q := prod_mem hreg
      have hhm : h ^ m * h ∈ regAt ξ q := (regAt ξ q).mul_mem (pow_mem (hA h hh) m) (hA h hh)
      have hua' : unitAt ξ q (ζ * (h ^ m * h)) := by rwa [← _root_.mul_assoc]
      have hζu : unitAt ξ q ζ := unitAt_of_mul_left hua' hζr hhm
      exact hni (unitAt_of_finsetProd S f hreg hζu (Finset.mem_filter.2 ⟨Finset.mem_univ i, hin⟩))
    · exact hqh (unitAt_of_mul_right hua (hA _ hm) (hA h hh))

end GlobalTheory.CompanionTheory.Ar.SncBase.Mdl
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.StableEigenTangentsPullbackStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.LocFn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stable_eigen_tangents_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : Type) [CommRing T] (y : Sp T ⟶ Xo.XF c) (A : Type) [CommRing A] (x₀ : Sp A ⟶ Y.X) (κ : c.F →+* A) (θ : A →+* T) (σ : E →+* ℂ) (r : ℕ) (e : Fin r → (epsAt x₀ ⟶ Y.t.G)), spMap θ ≫ x₀ = y ≫ Y.j → StableEig Y.t x₀ κ σ e → ∃ V : Fin r → (epsAt (under y) ⟶ Xo.univ.t.G), (∀ i, Tied Y y (V i).left (spMap (Formalism.L2.Pj.dualMap θ) ≫ (e i).left)) ∧ IsEigFrame Xo.univ.t.act (under y) ((θ.comp κ).comp (tauIn c σ)) V := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LocFn.exists_eigFrame_univ | exact GlobalTheory.CompanionTheory.Ar.LocFn.exists_eigFrame_univ | (intros; apply GlobalTheory.CompanionTheory.Ar.LocFn.exists_eigFrame_univ <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TangentSpaceEquivHolUnifStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_space_equiv_hol_unif : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] (z : Spec (CommRingCat.of ℂ) ⟶ X) (V : Type) [AddCommGroup V] [Module ℂ V] (M : LieModel G z V) (A : Over (Sp ℂ)) [GrpObj A] (φ : A.left ⟶ G.left) (L : LB A.left) (g : ℕ) (u : HolUnif A L g), IsGrpPullback A G z φ → (∀ v, IsTangent v → ∃! w, u.IsDiff w v) → (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) → ∃ D : V ≃ₗ[ℂ] (Fin g → ℂ), ∀ v, ∃ x : epsR ℂ ⟶ A, IsTangent x ∧ x.left ≫ φ = (M.pt v).left ∧ u.IsDiff (D v) x := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HodgeLin.exists_linearEquiv | exact GlobalTheory.CompanionTheory.Ar.HodgeLin.exists_linearEquiv | (intros; apply GlobalTheory.CompanionTheory.Ar.HodgeLin.exists_linearEquiv <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TopLeOfClosedPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Sl.Reg

def sc {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Sp R) (U : X.Opens) : R →+* Γ(X, U) :=
  (f.appLE ⊤ U (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

theorem sc_apply {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Sp R) (U : X.Opens) (a : R) :
    sc f U a = constFn f U a := rfl

def valR {O : Type} [CommRing O] {X : Scheme.{0}} (a : Sp O ⟶ X) (U : X.Opens) (h : ⊤ ≤ a ⁻¹ᵁ U) : Γ(X, U) →+* O :=
  (Scheme.ΓSpecIso (CommRingCat.of O)).hom.hom.comp (a.appLE U ⊤ h).hom

theorem top_le_of_closedPoint {O : Type} [CommRing O] [IsLocalRing O] (V : (Sp O).Opens)
    (h : IsLocalRing.closedPoint O ∈ V) : ⊤ ≤ V := by
  intro x _
  have hs : (x : Sp O) ⤳ IsLocalRing.closedPoint O :=
    (PrimeSpectrum.le_iff_specializes _ _).mp (IsLocalRing.le_maximalIdeal (x : PrimeSpectrum O).2.ne_top)
  exact hs.mem_open V.2 h

theorem valR_isUnit_iff {O : Type} [CommRing O] [IsLocalRing O] {X : Scheme.{0}} (a : Sp O ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ a ⁻¹ᵁ U) (b : Γ(X, U)) :
    IsUnit (valR a U h b) ↔ a (IsLocalRing.closedPoint O) ∈ X.basicOpen b := by
  have e : (a.appLE U ⊤ h).hom b = (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom (valR a U h b) := by
    simp [valR]
  have e2 := Scheme.basicOpen_appLE a ⊤ U h b
  rw [e, basicOpen_eq_of_affine] at e2
  have : a (IsLocalRing.closedPoint O) ∈ X.basicOpen b ↔ IsLocalRing.closedPoint O ∈ a ⁻¹ᵁ X.basicOpen b := Iff.rfl
  rw [this]
  have e3 : (IsLocalRing.closedPoint O ∈ a ⁻¹ᵁ X.basicOpen b) ↔ (IsLocalRing.closedPoint O ∈ (PrimeSpectrum.basicOpen (valR a U h b))) := by
    rw [e2]; exact ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
  rw [e3]
  change _ ↔ (valR a U h b) ∉ IsLocalRing.maximalIdeal O
  simp [IsLocalRing.mem_maximalIdeal]

theorem valR_res {O : Type} [CommRing O] {X : Scheme.{0}} (a : Sp O ⟶ X) {U V : X.Opens} (hVU : V ≤ U)
    (h : ⊤ ≤ a ⁻¹ᵁ V) (h' : ⊤ ≤ a ⁻¹ᵁ U) (f : Γ(X, U)) :
    valR a V h ((X.presheaf.map (homOfLE hVU).op).hom f) = valR a U h' f := by
  simp only [valR, RingHom.comp_apply]
  congr 1
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

theorem valR_sc {O R : Type} [CommRing O] [CommRing R] {X : Scheme.{0}} (a : Sp O ⟶ X) (π : X ⟶ Sp R) (ρ : R →+* O)
    (hρ : a ≫ π = spMap ρ) (U : X.Opens) (h : ⊤ ≤ a ⁻¹ᵁ U) (r : R) : valR a U h (sc π U r) = ρ r := by
  have key : ∀ (g : Sp O ⟶ Sp R) (_ : g = spMap ρ) (e : ⊤ ≤ g ⁻¹ᵁ ⊤),
      (Scheme.ΓSpecIso (CommRingCat.of O)).hom.hom ((g.appLE ⊤ ⊤ e).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) = ρ r := by
    rintro _ rfl e
    have e1 : (spMap ρ).appLE ⊤ ⊤ e = (spMap ρ).appTop := Scheme.Hom.appLE_eq_app (f := spMap ρ) (U := ⊤)
    have e2 := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ρ)
    rw [e1]
    have e3 : ((spMap ρ).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) = (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom (ρ r) :=
      (congrArg (fun q => q.hom r) e2).symm
    rw [e3]
    simp
  have e1 := Scheme.Hom.appLE_comp_appLE a π ⊤ U ⊤ (fun _ _ => trivial) h
  rw [← key (a ≫ π) hρ (by simpa using fun _ _ => trivial)]
  simp only [valR, sc, RingHom.comp_apply]
  congr 1
  rw [← CommRingCat.comp_apply, e1]

end GlobalTheory.CompanionTheory.Ar.Sl.Reg
end
end

