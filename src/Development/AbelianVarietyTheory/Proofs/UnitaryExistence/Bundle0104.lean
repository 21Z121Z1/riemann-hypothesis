import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0012
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0015
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0078
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0090
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0041
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0026
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0017
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionFractionalIdealDivisibleEqZero
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0041
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0048
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0101
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0080
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0085
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0033
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0049
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0040
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0021
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0020
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0038
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0024
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0016
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0111
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.Bundle0001
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0042
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0028
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0031

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsComplexFrobeniusPoints
section
noncomputable section

namespace GlobalTheory.Frames

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

namespace ComplexTransfer

theorem epi_spMap_field {k Ω : Type} [Field k] [Field Ω] (σ : k →+* Ω) : Epi (spMap σ) := by
  letI := σ.toAlgebra
  haveI : Flat (spMap σ) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 inferInstance
  haveI : Surjective (spMap σ) := ⟨fun p => ⟨IsLocalRing.closedPoint Ω, Subsingleton.elim _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

theorem countable_of_finiteType (K A : Type) [CommRing K] [Countable K] [CommRing A] [Algebra K A]
    [h : Algebra.FiniteType K A] : Countable A := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 h
  haveI : Countable (MvPolynomial (Fin n) K) := by
    rw [← Cardinal.mk_le_aleph0_iff]
    refine (MvPolynomial.cardinalMk_le_max).trans ?_
    simp
  exact hf.countable

theorem exists_common_field {K : Type} [Field K] [Countable K] (σ : K →+* ℂ) {A B k : Type} [CommRing A] [Algebra K A]
    [CommRing B] [Algebra K B] [Countable A] [Countable B] [Field k] [Algebra K k]
    (φ : A →ₐ[K] k) (ψ : B →ₐ[K] k) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (ι : L →ₐ[K] k) (j : L →ₐ[K] CAt σ) (φL : A →ₐ[K] L)
      (ψL : B →ₐ[K] L), ι.comp φL = φ ∧ ι.comp ψL = ψ ∧ Function.Injective j := by
  let s : Set k := Set.range φ ∪ Set.range ψ
  have hs : s.Countable := (Set.countable_range _).union (Set.countable_range _)
  let L := IntermediateField.adjoin K s
  have hL : Countable L := by
    have := hs.to_subtype
    rw [← Cardinal.mk_le_aleph0_iff]
    refine (IntermediateField.cardinalMk_adjoin_le K s).trans ?_
    simp
  letI : Algebra K ℂ := σ.toAlgebra
  obtain ⟨j⟩ := GlobalTheory.nonempty_algHom_complex_of_countable K L
  refine ⟨L, inferInstance, inferInstance, L.val, j,
    φ.codRestrict L.toSubalgebra fun a => IntermediateField.subset_adjoin K s (Or.inl ⟨a, rfl⟩),
    ψ.codRestrict L.toSubalgebra fun a => IntermediateField.subset_adjoin K s (Or.inr ⟨a, rfl⟩), ?_, ?_, ?_⟩
  · ext a; rfl
  · ext a; rfl
  · exact j.toRingHom.injective

theorem evalAt_of_mapR {K : Type} [Field K]
    (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
    (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
      (S →ₐ[K] T) → pts S → pts T → Prop)
    (hW : EvalWD pts mapR) (f : Rules pts) (hf : IsNatural pts mapR f)
    {S : Type} [CommRing S] [Algebra K S] (p : TRing K) (φ : p.R →ₐ[K] S) (y : pts p.R) (z : pts S)
    (hz : mapR φ y z) : evalAt pts mapR f z = φ (f p y) := by
  have hT : FromTest pts mapR z := ⟨p, φ, y, hz⟩
  unfold evalAt
  rw [dif_pos hT]
  exact (hW f hf S p _ φ _ y _ z hz hT.choose_spec.choose_spec.choose_spec).symm

end ComplexTransfer

theorem exists_complex_framed_pair : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (k : Type) [Field k] [Algebra c.F k] (y y' : FrPt Xo c k), ∃ z z' : FrPt Xo c (CAt c.F.val.toRingHom), (∀ ρ : Xo.X ⟶ Xo.X, y'.x = y.x ≫ ρ → z'.x = z.x ≫ ρ) ∧ (∀ f ∈ sec Xo c 0 0, evR Xo c f y = 0 → evR Xo c f z = 0) ∧ ∀ f ∈ sec Xo c 0 0, ∀ a : c.F, evR Xo c f z' = algebraMap c.F (CAt c.F.val.toRingHom) a * evR Xo c f z → evR Xo c f y' = algebraMap c.F k a * evR Xo c f y := by
  intro E _ _ _ H Dw l Xo c k _ _ y y'
  have hS : Out.SecBaseChangeSt := GlobalTheory.firstFiveLaws.1.secBaseChange
  have hW : EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) :=
    evalWD_fr (frChartF_of (GlobalTheory.Frames.chartCoverF_of_secBaseChange hS E H Dw l Xo c))
  have hA : AllTest Xo c := GlobalTheory.Frames.allTest_of_secBaseChange hS E H Dw l Xo c
  obtain ⟨p, φ, y₀, hy⟩ := hA k y
  obtain ⟨q, ψ, y₁, hy'⟩ := hA k y'
  haveI := c.fin
  haveI : Countable c.F := ComplexTransfer.countable_of_finiteType ℚ c.F
  haveI : Countable p.R := ComplexTransfer.countable_of_finiteType c.F p.R
  haveI : Countable q.R := ComplexTransfer.countable_of_finiteType c.F q.R
  obtain ⟨L, _, _, ι, j, φL, ψL, hφ, hψ, hj⟩ :=
    ComplexTransfer.exists_common_field c.F.val.toRingHom φ ψ
  obtain ⟨z, hz⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hS E H Dw l Xo c _ _ (j.comp φL) y₀
  obtain ⟨z', hz'⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hS E H Dw l Xo c _ _ (j.comp ψL) y₁
  have hι : Function.Injective ι := ι.toRingHom.injective
  have ev : ∀ f ∈ sec Xo c 0 0, evR Xo c f y = ι (φL (f p y₀)) ∧ evR Xo c f y' = ι (ψL (f q y₁)) ∧
      evR Xo c f z = j (φL (f p y₀)) ∧ evR Xo c f z' = j (ψL (f q y₁)) := by
    intro f hf
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← AlgHom.comp_apply, hφ]
      exact ComplexTransfer.evalAt_of_mapR _ _ hW f hf.1 p φ y₀ y hy
    · rw [← AlgHom.comp_apply, hψ]
      exact ComplexTransfer.evalAt_of_mapR _ _ hW f hf.1 q ψ y₁ y' hy'
    · exact ComplexTransfer.evalAt_of_mapR _ _ hW f hf.1 p _ y₀ z hz
    · exact ComplexTransfer.evalAt_of_mapR _ _ hW f hf.1 q _ y₁ z' hz'
  refine ⟨z, z', ?_, ?_, ?_⟩
  · intro ρ h
    have e1 : y.x = spMap ι.toRingHom ≫ spMap φL.toRingHom ≫ y₀.x := by
      rw [← Category.assoc, ← Geo.Tor.spMap_comp, hy.1, ← hφ]; rfl
    have e2 : y'.x = spMap ι.toRingHom ≫ spMap ψL.toRingHom ≫ y₁.x := by
      rw [← Category.assoc, ← Geo.Tor.spMap_comp, hy'.1, ← hψ]; rfl
    have e3 : z.x = spMap j.toRingHom ≫ spMap φL.toRingHom ≫ y₀.x := by
      rw [← Category.assoc, ← Geo.Tor.spMap_comp, hz.1]; rfl
    have e4 : z'.x = spMap j.toRingHom ≫ spMap ψL.toRingHom ≫ y₁.x := by
      rw [← Category.assoc, ← Geo.Tor.spMap_comp, hz'.1]; rfl
    haveI := ComplexTransfer.epi_spMap_field ι.toRingHom
    rw [e1, e2, Category.assoc, cancel_epi] at h
    rw [e3, e4, h]
    simp only [Category.assoc]
  · intro f hf h
    obtain ⟨h1, -, h3, -⟩ := ev f hf
    rw [h1, map_eq_zero_iff ι hι] at h
    rw [h3, h, map_zero]
  · intro f hf a h
    obtain ⟨h1, h2, h3, h4⟩ := ev f hf
    rw [h3, h4, ← j.commutes, ← map_mul] at h
    rw [h1, h2, hj h, map_mul, ι.commutes]

end GlobalTheory.Frames
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFiniteAdelicElementMarkingComponent
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member

theorem onto_dom_nonempty {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) : ∃ x, x ∈ X.dom := by
  choose P hP hg using X.signature
  have hs : ∀ a : ℕ, sgn X.p0 a ≠ 0 := fun a => by unfold sgn; split_ifs <;> norm_num
  refine ⟨fun τ => P τ, fun τ => ⟨hP τ, fun i => ?_⟩⟩
  have e : dmin X.Gm (fun τ => P τ) τ i = ((psgn X.p0 i : ℝ) : ℂ) := by
    unfold dmin lminor
    rw [show gram τ.1 X.Gm (mat (fun τ => P τ) τ) = gram τ.1 X.Gm (P τ) from rfl, hg τ,
      Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal]
    unfold psgn
    push_cast
    exact Fin.prod_univ_eq_prod_range (fun a => ((sgn X.p0 a : ℝ) : ℂ)) (i : ℕ)
  rw [e, Complex.ofReal_re]
  have h0 : psgn X.p0 i ≠ 0 := Finset.prod_ne_zero_iff.2 fun a _ => hs a
  exact mul_self_pos.2 h0

theorem onto_adelic_of_tower (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (L Λ : Submodule (𝓞 E) (Fin n → E)) (hL : L.FG) (hLs : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    (hΛ : Λ.FG) (hΛs : Submodule.span E (Λ : Set (Fin n → E)) = ⊤)
    {A B : Type} [AddCommGroup A] [Module (𝓞 E) A] [AddCommGroup B] [Module (𝓞 E) B]
    (ι : A ≃ₗ[𝓞 E] L) (φ : B ≃ₗ[𝓞 E] Λ) (EA : A → A → ℤ) (EB : B → B → ℤ) (f : ℕ → A →ₗ[𝓞 E] B)
    (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (ξ : E) (J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
    (hJ : ∀ z : E, z ∈ J ↔ ∀ a : 𝓞 E, ∃ m : ℤ, Algebra.trace ℚ E (ξ * (a * z)) = m)
    (hA : ∀ x y, Algebra.trace ℚ E (ξ * ∑ a, ∑ b, (ι x : Fin n → E) a * G a b * c ((ι y : Fin n → E) b)) =
      -(EA x y : ℚ))
    (hB : ∀ x y, Algebra.trace ℚ E (ξ * ∑ a, ∑ b, (φ x : Fin n → E) a * G a b * c ((φ y : Fin n → E) b)) =
      -(EB x y : ℚ))
    (h1 : ∀ N m : ℕ, 0 < N → 0 < m → ∀ a, ∃ e, f (N * m) a = f N a + N • e)
    (h2 : ∀ N : ℕ, 0 < N → (∀ a, (∃ e, f N a = N • e) ↔ ∃ e, a = N • e) ∧ ∀ a', ∃ a e, a' = f N a + N • e)
    (h3 : ∀ N : ℕ, 0 < N → ∀ a a', (N : ℤ) ∣ EB (f N a) (f N a') - EA a a') :
    ∃ g : GL (Fin n) (GlobalTheory.AdLat.RA F E),
      (g : Matrix (Fin n) (Fin n) (GlobalTheory.AdLat.RA F E)).mulVec '' (GlobalTheory.AdLat.hat F (L : Set (Fin n → E))) =
        GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E)) ∧
      (∀ N : ℕ, 0 < N → ∀ a : A, ∃ w ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E)),
        (g : Matrix (Fin n) (Fin n) (GlobalTheory.AdLat.RA F E)) *ᵥ GlobalTheory.AdLat.fv F (ι a : Fin n → E) =
          GlobalTheory.AdLat.fv F (φ (f N a) : Fin n → E) + N • w) ∧
      ∀ x y, GlobalTheory.AdLat.hermA c G ((g : Matrix (Fin n) (Fin n) (GlobalTheory.AdLat.RA F E)) *ᵥ x)
        ((g : Matrix (Fin n) (Fin n) (GlobalTheory.AdLat.RA F E)) *ᵥ y) = GlobalTheory.AdLat.hermA c G x y := by
  let f' : ℕ → (L →ₗ[𝓞 E] Λ) := fun N => φ.toLinearMap ∘ₗ f N ∘ₗ ι.symm.toLinearMap
  have hf' : ∀ N a, f' N (ι a) = φ (f N a) := fun N a => by simp [f']
  have hlin : ∀ (s : 𝓞 E) (x y : Fin n → E), (s : E) * ∑ a, ∑ b, x a * G a b * c (y b) =
      ∑ a, ∑ b, (s • x) a * G a b * c (y b) := by
    intro s x y
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    change _ = ((s : E) * x a) * _ * _
    ring
  obtain ⟨g, hg1, hg2, hg3⟩ := GlobalTheory.AdLat.exists_adelic_matrix_of_tower F E n L Λ f' hL hLs hΛ hΛs
    (fun N m hN hm a => by
      obtain ⟨a, rfl⟩ := ι.surjective a
      obtain ⟨e, he⟩ := h1 N m hN hm a
      exact ⟨φ e, by rw [hf', hf', he, map_add, map_nsmul]⟩)
    (fun N hN => ⟨fun a => by
      obtain ⟨a, rfl⟩ := ι.surjective a
      rw [hf']
      constructor
      · rintro ⟨v, hv⟩
        obtain ⟨e, he⟩ := ((h2 N hN).1 a).1 ⟨φ.symm v, by rw [← map_nsmul, ← hv, LinearEquiv.symm_apply_apply]⟩
        exact ⟨ι e, by rw [he, map_nsmul]⟩
      · rintro ⟨v, hv⟩
        obtain ⟨e, he⟩ := ((h2 N hN).1 a).2 ⟨ι.symm v, by rw [← map_nsmul, ← hv, LinearEquiv.symm_apply_apply]⟩
        exact ⟨φ e, by rw [he, map_nsmul]⟩, fun a' => by
      obtain ⟨a', rfl⟩ := φ.surjective a'
      obtain ⟨a, e, he⟩ := (h2 N hN).2 a'
      exact ⟨ι a, φ e, by rw [hf', he, map_add, map_nsmul]⟩⟩)
  refine ⟨g, hg1, fun N hN a => by rw [← hf']; exact hg2 N hN (ι a), hg3 c G J ?_ ?_⟩
  · intro x hx y hy
    obtain ⟨x', hx'⟩ := φ.surjective ⟨x, hx⟩
    obtain ⟨y', hy'⟩ := φ.surjective ⟨y, hy⟩
    rw [hJ]
    intro s
    refine ⟨-EB (s • x') y', ?_⟩
    rw [hlin, Int.cast_neg, ← hB, map_smul, hx', hy']
    rfl
  · intro N hN x y
    obtain ⟨x, rfl⟩ := ι.surjective x
    obtain ⟨y, rfl⟩ := ι.surjective y
    have hN0 : (N : E) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    have hNq : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    rw [hf', hf']
    refine ⟨(N : E)⁻¹ * ((∑ a, ∑ b, (φ (f N x) : Fin n → E) a * G a b * c ((φ (f N y) : Fin n → E) b)) -
      ∑ a, ∑ b, (ι x : Fin n → E) a * G a b * c ((ι y : Fin n → E) b)), ?_, ?_⟩
    · rw [hJ]
      intro s
      obtain ⟨m, hm⟩ := h3 N hN (s • x) y
      refine ⟨-m, ?_⟩
      have e1 := hA (s • x) y
      have e2 := hB (f N (s • x)) (f N y)
      rw [map_smul, Submodule.coe_smul, ← hlin] at e1
      rw [show (φ (f N (s • x)) : Fin n → E) = s • (φ (f N x) : Fin n → E) by
        rw [map_smul, map_smul, Submodule.coe_smul], ← hlin] at e2
      have hm' : (EB (f N (s • x)) (f N y) : ℚ) - EA (s • x) y = N * m := by exact_mod_cast hm
      generalize (∑ a, ∑ b, (φ (f N x) : Fin n → E) a * G a b * c ((φ (f N y) : Fin n → E) b)) = u at e2 ⊢
      generalize (∑ a, ∑ b, (ι x : Fin n → E) a * G a b * c ((ι y : Fin n → E) b)) = v at e1 ⊢
      have e3 : ξ * ((s : E) * ((N : E)⁻¹ * (u - v))) = (N : ℚ)⁻¹ • (ξ * (s * u) - ξ * (s * v)) := by
        rw [Algebra.smul_def, map_inv₀, map_natCast]; ring
      rw [e3, map_smul, map_sub, e1, e2, smul_eq_mul]
      push_cast
      field_simp
      linear_combination -hm'
    · rw [nsmul_eq_mul, mul_inv_cancel_left₀ hN0, add_sub_cancel]

theorem onto_marking_sub (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n N : ℕ}
    {u v e : Fin n → E} {z w : Fin n → GlobalTheory.AdLat.RA F E} (h : u = v + N • e)
    (hz : z = GlobalTheory.AdLat.fv F u + N • w) : GlobalTheory.AdLat.fv F v - z = N • -(GlobalTheory.AdLat.fv F e + w) := by
  rw [hz, h, GlobalTheory.AdLat.cap_fv_add, GlobalTheory.AdLat.cap_fv_nsmul, smul_neg, smul_add]
  abel

theorem exists_finite_mark : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r), C.OK → ∀ k, ∃ h ∈ GfC V, C.Mark h k 1 := by
  intro D H Dw l Xo c σ V r C hC k
  obtain rfl : V.rank = r := C.hr
  have hneg := (GlobalTheory.T.exists_memberDictionaryContext_goodEmbedding D H Dw l Xo c σ V _ rfl C.ι hC.iota hC.pos hC.lA hC.good).2.1 C hC
  obtain ⟨Pf, -, -, hPf, -⟩ := GlobalTheory.exists_framePeriods D.host.E H Dw l Xo c σ C.g C.e C.F _ C.M hC.good hC.base hneg k
  obtain ⟨x, hx⟩ := onto_dom_nonempty (C.M.X k)
  obtain ⟨f, h1, h2, h3, h4⟩ := GlobalTheory.familyUnif_lattice_genus D.host.E H Dw l Xo _ C.g _ C.F k (Pf x) (hPf x hx)
  obtain ⟨-, hfv, -, -, -, hcc, -, -, -, hT, -⟩ := GlobalTheory.T.completedLattice_eq_adelicCompletion_and_gram D V
  obtain ⟨hL, hLs, -⟩ := GlobalTheory.T.adelicElementLattice_full_and_completion D V 1
  let ι : Dw.La ≃ₗ[𝓞 D.host.E] latG V 1 :=
    (LinearEquiv.ofInjective C.ι hC.iota.emb.1).trans (LinearEquiv.ofEq _ _ hC.iota.emb.2)
  have hι : ∀ a, (ι a : Fin V.rank → D.host.E) = C.ι a := fun a => rfl
  have hherm : ∀ x y : Fin V.rank → D.host.E, (∑ a, ∑ b, x a * V.gramᵀ a b * cF D (y b)) = -herm (-V.gramᵀ) x y := by
    intro x y
    simp only [herm, hcc, Matrix.neg_apply, mul_neg, neg_mul, Finset.sum_neg_distrib, neg_neg]
  have hGm : (C.M.X k).Gm = -V.gramᵀ := (hC.modelW k).1
  have hxi : (C.M.X k).ξ0 = -D.host.xi0 := (hC.modelW k).2
  obtain ⟨g, hg1, hg2, hg3⟩ := onto_adelic_of_tower D.host.F D.host.E V.rank (latG V 1) (C.M.X k).Λ hL hLs
    (C.M.X k).Λ_fg (C.M.X k).Λ_span ι (C.M.φ k) (fun a b => Dw.EF a b) (fun a b => (C.F.Di k).EF a b) f
    (cF D) V.gramᵀ D.host.xi0 _ (GlobalTheory.T.adelicUnitaryLattice_selfDual_traceForm D V 1 _ rfl).1
    (fun x y => by
      have halt : Dw.EF y x = -Dw.EF x y := by
        have := Dw.alt (x + y)
        simp only [map_add, LinearMap.add_apply, Dw.alt] at this
        linear_combination this
      rw [hherm, hι, hι, ← hT, ← hC.iota.isom, halt, Int.cast_neg])
    (fun x y => by
      rw [hherm, hC.base.ef k x y, hGm, hxi, neg_neg, mul_neg, map_neg])
    h1 h2 h3
  obtain ⟨h, hh, rfl⟩ := (GlobalTheory.T.adelicUnitary_eq_real_mul_finite_split D V).2.2.2.1 g hg3
  obtain ⟨-, -, hlat, hhat, -⟩ := GlobalTheory.T.adelicElementLattice_full_and_completion D V h
  have hcap := (GlobalTheory.AdLat.hat_rational_points_and_approx D.host.F D.host.E V.rank (C.M.X k).Λ (C.M.X k).Λ_fg
    (C.M.X k).Λ_span).1
  rw [hg1] at hhat
  refine ⟨h, hh, one_mem _, ?_, fun a ha => ?_⟩
  · rw [one_mul, hlat]
    ext v
    rw [SetLike.mem_coe, ← hcap, ← SetLike.mem_coe, ← hg1]
    constructor
    · intro hv
      exact ⟨v, hv, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact hv
  · rw [one_mul]
    obtain ⟨e, he⟩ := h4 a ha
    obtain ⟨w, hw, hw'⟩ := hg2 l.M (lt_of_lt_of_le (by norm_num) l.three_le) a
    refine ⟨-(GlobalTheory.AdLat.fv D.host.F (C.M.φ k e : Fin V.rank → D.host.E) + w), ?_, ?_⟩
    · have h0 := (hcap _).2 (C.M.φ k e).2
      have h5 := AddSubgroup.neg_mem _ (AddSubgroup.add_mem _ h0 hw)
      rw [← SetLike.mem_coe, ← hhat] at h5
      exact h5
    · rw [hfv, hfv, ← hι]
      change GlobalTheory.AdLat.fv D.host.F (C.M.φ k (C.F.t k a) : Fin V.rank → D.host.E) - _ = _
      have he' : (C.M.φ k (f l.M a) : Fin V.rank → D.host.E) =
          (C.M.φ k (C.F.t k a) : Fin V.rank → D.host.E) + l.M • (C.M.φ k e : Fin V.rank → D.host.E) := by
        rw [he, (C.M.φ k).map_add, map_nsmul (C.M.φ k)]
        rfl
      exact onto_marking_sub D.host.F he' hw'

end GlobalTheory.Member
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedUniformisationComponentsPeriodSpacesBiject
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.CompRat

namespace GlobalTheory.CompBij

open GlobalTheory.CompInj

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem ik_bijective : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), 1 ≤ r → GoodEmb c σ → IsUnf U → ∀ (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ), (∀ k a b, (((F.Di (ik k)).EF a b : ℤ) : ℚ) = Algebra.trace ℚ E (-(U.X k).ξ0 * herm (U.X k).Gm (φ k a : Fin r → E) (φ k b))) → (∀ k (x : (U.X k).dom), ∃ Pm : (F.Di (ik k)).La →+ (Fin g → ℂ), (∀ a j, Pm a j = perFr (U.X k) x.1 (φ k a : Fin r → E) (relab c σ (e j).1) (e j).2) ∧ IsPeriod (F.Di (ik k)) (fun j => relab c σ (e j).1) Pm ∧ (U.un k x).x = F.u (ik k) Pm ∧ ∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (F.ex (ik k) Pm z).left) (Pi.single (e.symm ⟨τ, i⟩) 1) ((U.un k x).u τ i)) → Function.Bijective ik := by
  intro E _ _ _ H D l Xo c σ r U h1 hσ hU g e F ik φ hEF hP
  obtain ⟨hr, hX, hcov, hfib, -⟩ := hU
  refine ⟨fun k k' hk => ?_, fun i => ?_⟩
  · obtain ⟨x, hx⟩ := dom_nonempty (U.X k)
    obtain ⟨x₀, hx₀⟩ := dom_nonempty (U.X k')
    obtain ⟨P, -, hper, hpt, hder⟩ := hP k ⟨x, hx⟩
    obtain ⟨P₀, hP₀, hper₀, -⟩ := hP k' ⟨x₀, hx₀⟩
    have hP' := fun y => (hP k' y).imp fun _ h => (⟨h.1, h.2.2.1, h.2.2.2⟩ : _ ∧ _ ∧ _)
    have hEF' := hEF k'
    generalize φ k' = ψ at hP₀ hP' hEF'
    clear hP hEF φ
    generalize ik k' = n at *
    subst hk
    obtain ⟨x', hx', hPx⟩ := exists_frame (c := c) (σ := σ) hσ h1 hr e (U.X k') (hX k').1 (hX k').2 _ (F.sig _).1
      (F.sig _).2 ψ hEF' x₀ hx₀ P₀ hP₀ hper₀ P hper
    obtain ⟨P', hP', hpt', hder'⟩ := hP' ⟨x', hx'⟩
    obtain rfl : P = P' := by
      ext a j
      exact (hPx a j).trans (hP' a j).symm
    have hbor := frBor_of_eq (U.un k ⟨x, hx⟩) (U.un k' ⟨x', hx'⟩) (hpt'.trans hpt.symm) fun τ i =>
      ((GlobalTheory.isDerivAt0_ex_isTanAt E H D l Xo _ g _ F _ P hper).2.1 _).unique (hder' τ i) (hder τ i)
    obtain ⟨γ, -, b, -, h⟩ := (hfib k k' _ _).1 hbor
    exact (congrArg Sigma.fst h).symm
  · have hty : IsTypeFn H (F.Di i).p (F.Di i).q (fun j => relab c σ (e j).1) := by
      rw [(F.sig i).1, (F.sig i).2]
      exact (GlobalTheory.Relab.relab_good E H l c σ hσ).2.2.2 D g e
    obtain ⟨-, P, hPi⟩ := GlobalTheory.PeriodExists.period_of_isTypeFn H (F.Di i) g _ hty
    let _ : Algebra c.F ℂ := σ.toAlgebra
    obtain ⟨y, hy⟩ := Formalism.L2.Pj.exists_frPt_local (Xo := Xo) (c := c) (L := ℂ)
      GlobalTheory.firstFiveLaws.2.1.secTwist (F.u i P) ((F.over_σ i P hPi).trans rfl)
    obtain ⟨k, x, t, hb⟩ := hcov y
    obtain ⟨Pm, -, hPm, hx, -⟩ := hP k x
    exact ⟨k, F.disj _ _ Pm P hPm hPi (hx.symm.trans (hb.1.symm.trans hy))⟩

end GlobalTheory.CompBij
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelMoveModuliUniqueUniversalTriple
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory

open Moduli.LevelAction in

theorem levMove_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (_c : Coeff l), ∀ (ρ ρ' : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (ν' : SABMap Xo.univ.t Xo.univ.t ρ') (gM gM' gA gA' : Dw.La →ₗ[𝓞 E] Dw.La), 1 ≤ Dw.p + Dw.q → (∀ a, gM a - gM' a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) → (∀ a, Dw.ModN l.A (gA a - gA' a)) → IsIso ρ → IsIso ρ' → IsLevMove ρ ν gM gA → IsLevMove ρ' ν' gM' gA' → (∃ g : Sim Dw, (∀ a, g.f l.M a - gM a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) ∧ (∀ a, Dw.ModN l.A (g.f l.A a - gA a)) ∧ (l.A : ℤ) ∣ g.ν l.A - 1) → ρ = ρ' ∧ ν.φ = ν'.φ := by
  intro E _ _ _ H Dw l Xo _ ρ ρ' ν ν' gM gM' gA gA' hpq hM hA _ _ ⟨hs, e, eA⟩ ⟨hs', e', eA'⟩ ⟨g, hgM, hgA, hν⟩
  have hred : IsReduced Xo.X := by
    have := Xo.smooth
    exact (isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _ Xo.s
      (SmoothOfRelativeDimension.smooth Dw.dim _)).1
  obtain ⟨o, m, a₁, b₁⟩ := exists_obj_twist_by_similitude SimAlg.sim_group E H Dw l _ _ _ _ Xo.univ g hpq hν
  obtain ⟨n, hn⟩ := exists_comp_sabMap m ν (Category.id_comp ρ)
  obtain ⟨n', hn'⟩ := exists_comp_sabMap m ν' (Category.id_comp ρ')
  have c₁ : ∀ a, (o.eta a).left ≫ n.φ = ρ ≫ (Xo.univ.eta a).left := fun a => by
    rw [hn, ← Category.assoc, a₁, eta_congr Xo.univ (hgM a), e]
  have c₂ : ∀ a, (o.etaA a).left ≫ n.φ = ρ ≫ (Xo.univ.etaA a).left := fun a => by
    rw [hn, ← Category.assoc, b₁, etaA_congr Xo.univ (hgA a), eA]
  have d₁ : ∀ a, (o.eta a).left ≫ n'.φ = ρ' ≫ (Xo.univ.eta a).left := fun a => by
    rw [hn', ← Category.assoc, a₁, eta_congr Xo.univ (hgM a), eta_congr Xo.univ (hM a), e']
  have d₂ : ∀ a, (o.etaA a).left ≫ n'.φ = ρ' ≫ (Xo.univ.etaA a).left := fun a => by
    rw [hn', ← Category.assoc, b₁, etaA_congr Xo.univ (hgA a), etaA_congr Xo.univ (hA a), eA']
  obtain rfl : ρ = ρ' := (Xo.rep _ Xo.s hred o).unique ⟨hs, ⟨⟨n, c₁, c₂⟩⟩⟩ ⟨hs', ⟨⟨n', d₁, d₂⟩⟩⟩
  refine ⟨rfl, ?_⟩
  have h := obj_rigid_closed firstFiveLaws.1 E H Dw l _ _ _ _ _ _ _ _ Xo.univ o ρ (Or.inl hred) n n'
    fun a => ⟨_, c₁ a, d₁ a⟩
  have : IsIso m.φ := m.cart.1.isIso_fst_of_isIso
  rw [hn, hn'] at h
  exact (cancel_epi m.φ).1 h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NormalisedFramedPointArithmeticGroupInvariantSig
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.FrameUnif

theorem wchar_ex_sign {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (Dw : Datum H) {S : Type} [CommRing S] (t : Ix Dw → Sˣ) (h0 : (t none : S) ^ 2 = 1)
    (h1 : ∀ p, t (some p) = 1) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (hn : Even n) : wchar (ex Dw a n) t = 1 := by
  obtain ⟨m, rfl⟩ := hn
  unfold wchar
  rw [Fintype.prod_option]
  simp only [h1, Units.val_one, one_pow, Finset.prod_const_one, mul_one]
  show (t none : S) ^ (m + m) = 1
  rw [← two_mul, pow_mul, h0, one_pow]

theorem normUn_gamma : Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (un : ∀ k, (M.X k).dom → FrPt Xo c (CAt σ)) (k : Fin F.n) (T : ThetaData e F M k), GoodEmb c σ → ModelBase M → NegXi M → IsNormUn T (un k) → ∀ γ ∈ (M.X k).Γ, ∀ (x : (M.X k).dom) (h : lact γ x.1 ∈ (M.X k).dom), ∃ t : Ix Dw → (CAt σ)ˣ, FrBor t (un k x) (un k ⟨_, h⟩) ∧ ∀ a n, Dom a n → toC (wchar (ex Dw a n) t) = 1 := by
  intro hS E _ _ _ H Dw l Xo c σ g e F r M un k T hσ hM hN hun γ hγ x h
  obtain ⟨gam, hgam, hP⟩ := GlobalTheory.per_gam E H Dw l Xo c σ g e F r M hσ hM hN k T.Pf T.per γ hγ
  obtain ⟨κ, hκ, hy⟩ := hun x
  obtain ⟨κ', hκ', hy'⟩ := hun ⟨_, h⟩
  have hb : T.co.symm x.1 ∈ T.co ⁻¹' (M.X k).dom := by
    show T.co (T.co.symm x.1) ∈ (M.X k).dom
    rw [T.co.apply_symm_apply]; exact x.2
  have hb' : T.co.symm (lact γ x.1) ∈ T.co ⁻¹' (M.X k).dom := by
    show T.co (T.co.symm (lact γ x.1)) ∈ (M.X k).dom
    rw [T.co.apply_symm_apply]; exact h
  obtain ⟨hx, hd, t₀, hsec, ht⟩ := GlobalTheory.T.thetaPoints_change_levelIsometry_linearMap hS E H Dw l Xo c σ g e F r M k T _ hb _ hb' κ κ' (un k x)
    (un k ⟨_, h⟩) gam 1 hy hy' hgam (fun a => by
      rw [T.co.apply_symm_apply, T.co.apply_symm_apply, Matrix.one_mulVec]; exact hP x.1 x.2 a)
  have hu : ∀ τ i, (un k ⟨_, h⟩).u τ i = (un k x).u τ i := fun τ i => by
    have h1 := hd τ i
    rw [inv_one, Matrix.one_mulVec] at h1
    exact ((GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ F k _ (T.isPer _ hb)).2.1 _).unique h1 (hy.2.1 τ i)
  have hC : (normConst (fun j => relab c σ (e j).1) (M.X k).ξ0 : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    refine (Real.sqrt_pos.2 (div_pos (by positivity) (Finset.prod_pos fun j _ => ?_))).ne'
    have : relab c σ (e j).1 (M.X k).ξ0 ≠ 0 := (map_ne_zero _).2 (M.X k).ξ0_ne
    positivity
  have ht2 : toC (t₀ : CAt σ) ^ 2 = 1 := by
    have d1 := (T.norm _ hb).1.ne_zero
    have d2 := (T.norm _ hb').1.ne_zero
    rw [hκ, hκ', Matrix.det_one, mul_one] at ht
    refine mul_right_cancel₀ (mul_ne_zero (mul_ne_zero hC d1) d2) ?_
    rw [ht]; ring
  refine ⟨fun i => i.elim t₀ fun _ => 1, ?_, fun a n hn => ?_⟩
  · refine (frBor_iff_frChg _ _ _).2 ⟨fun _ => 1, fun τ i j hij => Matrix.one_apply_ne hij.ne,
      fun τ i => Matrix.one_apply_eq i, hx, fun τ i => ?_, hsec⟩
    rw [hu]
    exact (GlobalTheory.T.frameChangeByMatrices_refl_and_comp E H Dw l Xo c (CAt σ) (un k x) (un k x) (un k x)).1.2.1 τ i
  · exact wchar_ex_sign Dw _ ht2 (fun _ => rfl) a n hn.2

end GlobalTheory.FrameUnif
end

