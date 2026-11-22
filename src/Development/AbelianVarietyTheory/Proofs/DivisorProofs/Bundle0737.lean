import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0203
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0235
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0719
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0136
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0040
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStrictHenselisationOfDirectedUnion
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0026
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0042
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0170
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0279
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0258
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0505
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0656
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0717
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTaylorExpansionOrderOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0022
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0413
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0721
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0716
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0727
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0709
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0729
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0686
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoWindowsOfMatrixCongrModTau
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalHomToStrictlyHenselianNormal
section
open IsLocalRing Polynomial

namespace GlobalTheory.NormalStrictHens

theorem exists_mem_finset {S : Type} [CommRing S] {ι : Type} [Preorder ι] [IsDirected ι (· ≤ ·)]
    [Nonempty ι] (R : ι → Subring S) (hmono : Monotone R) (hcov : ∀ x : S, ∃ i, x ∈ R i)
    (s : Finset S) : ∃ i, ∀ x ∈ s, x ∈ R i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨Classical.arbitrary ι, by simp⟩
  | insert x s _ ih =>
    obtain ⟨i, hi⟩ := ih
    obtain ⟨j, hj⟩ := hcov x
    obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
    refine ⟨k, fun y hy => ?_⟩
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact hmono hjk hj
    · exact hmono hik (hi y hy)

theorem isDomain_of_directed {S : Type} [CommRing S] [Nontrivial S] {ι : Type} [Preorder ι]
    [IsDirected ι (· ≤ ·)] [Nonempty ι] (R : ι → Subring S) (hmono : Monotone R)
    (hcov : ∀ x : S, ∃ i, x ∈ R i) (hdom : ∀ i, IsDomain (R i)) : IsDomain S := by
  classical
  haveI : NoZeroDivisors S := ⟨fun {x y} hxy => by
    obtain ⟨k, hk⟩ := exists_mem_finset R hmono hcov {x, y}
    haveI := hdom k
    have hx : x ∈ R k := hk x (by simp)
    have hy : y ∈ R k := hk y (by simp)
    have h : (⟨x, hx⟩ : R k) * ⟨y, hy⟩ = 0 := Subtype.ext hxy
    rcases mul_eq_zero.1 h with h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)⟩
  exact NoZeroDivisors.to_isDomain S

theorem isIntegrallyClosed_of_directed {S : Type} [CommRing S] [IsDomain S] {ι : Type} [Preorder ι]
    [IsDirected ι (· ≤ ·)] [Nonempty ι] (R : ι → Subring S) (hmono : Monotone R)
    (hcov : ∀ x : S, ∃ i, x ∈ R i) (hdom : ∀ i, IsDomain (R i))
    (hic : ∀ i, IsIntegrallyClosed (R i)) : IsIntegrallyClosed S := by
  classical
  rw [isIntegrallyClosed_iff (FractionRing S)]
  intro x hx
  obtain ⟨f, hfm, hf⟩ := hx
  obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors S) x
  obtain ⟨k, hk⟩ := exists_mem_finset R hmono hcov (insert a (insert (b : S) f.coeffs))
  haveI := hdom k
  haveI := hic k
  have ha : a ∈ R k := hk a (by simp)
  have hb : (b : S) ∈ R k := hk b (by simp)
  have hcf : (f.coeffs : Set S) ⊆ R k := fun c hc =>
    hk c (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hc))
  have hgm : (f.toSubring (R k) hcf).Monic := (monic_toSubring f (R k) hcf).2 hfm
  have hgf : (f.toSubring (R k) hcf).map (R k).subtype = f := map_toSubring f (R k) hcf
  have hinj : Function.Injective ((algebraMap S (FractionRing S)).comp (R k).subtype) :=
    (IsFractionRing.injective S (FractionRing S)).comp Subtype.val_injective
  let φ : FractionRing (R k) →+* FractionRing S := IsFractionRing.lift hinj
  have hφ : ∀ r : R k, φ (algebraMap (R k) (FractionRing (R k)) r) = algebraMap S (FractionRing S) r :=
    fun r => IsFractionRing.lift_algebraMap hinj r
  have hb0 : (⟨b, hb⟩ : R k) ∈ nonZeroDivisors (R k) := by
    rw [mem_nonZeroDivisors_iff_ne_zero]
    intro h
    exact nonZeroDivisors.coe_ne_zero b (congrArg Subtype.val h)
  have hφy : φ (IsLocalization.mk' (FractionRing (R k)) (⟨a, ha⟩ : R k) ⟨⟨b, hb⟩, hb0⟩) =
      IsLocalization.mk' (FractionRing S) a b := by
    rw [IsFractionRing.lift_mk', IsFractionRing.mk'_eq_div]
    rfl
  have hcomp : φ.comp (algebraMap (R k) (FractionRing (R k))) =
      (algebraMap S (FractionRing S)).comp (R k).subtype := by
    ext r
    exact hφ r
  have hy : IsIntegral (R k) (IsLocalization.mk' (FractionRing (R k)) (⟨a, ha⟩ : R k) ⟨⟨b, hb⟩, hb0⟩) := by
    refine ⟨f.toSubring (R k) hcf, hgm, ?_⟩
    apply φ.injective
    rw [map_zero, hom_eval₂, hφy, hcomp, ← eval₂_map, hgf]
    exact hf
  obtain ⟨c, hc⟩ := (isIntegrallyClosed_iff (FractionRing (R k))).1 inferInstance hy
  refine ⟨c, ?_⟩
  rw [← hφ, hc, hφy]

end GlobalTheory.NormalStrictHens

namespace GlobalTheory

open GlobalTheory.NormalStrictHens in

theorem exists_strictlyHenselian_normal_between : ∀ (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T],
    GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      (i : A →+* T), IsLocalHom i →
    ∃ (A' : Type) (_ : CommRing A') (_ : IsDomain A') (_ : HenselianLocalRing A')
      (_ : IsSepClosed (ResidueField A')) (_ : IsNoetherianRing A') (_ : IsIntegrallyClosed A')
      (ι : A →+* A') (α : A' →+* T), α.comp ι = i ∧ IsLocalHom α := by
  intro T _ _ _ hT A _ _ _ _ _ i hi
  haveI := hi
  obtain ⟨hThens, hTac, -⟩ :=
    GlobalTheory.AbsIntClosedLocal.henselian_isAlgClosed_pow_surj T ⟨inferInstance, hT⟩
  haveI := hThens
  haveI := hTac
  obtain ⟨S, _, _, _, hloc, hsc, -, hmax, -, ι, _, _, _, Si, hmono, hcov, hSi⟩ :=
    GlobalTheory.exists_strictHenselisation A (SeparableClosure (ResidueField A))
  haveI := hsc
  have hind : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap A S) :=
    GlobalTheory.StrictHensUnion.indEtale_of_directed_union A S ι Si hmono hcov fun k => by
      obtain ⟨B, _, _, _, q, _, ⟨e⟩⟩ := hSi k
      exact GlobalTheory.StrictHensUnion.indEtale_of_algEquiv e
        (GlobalTheory.StrictHensUnion.indEtale_localization_of_etale A B q.primeCompl)
  have hsh : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation (algebraMap A S) :=
    ⟨inferInstance, hsc, hloc, hind⟩
  haveI : IsNoetherianRing S := GlobalTheory.StalkNoeth.isNoetherianRing_of_indEt A S hind
  have hdi : ∀ k, IsDomain (Si k).toSubring ∧ IsIntegrallyClosed (Si k).toSubring := fun k => by
    obtain ⟨B, _, _, _, q, _, ⟨e⟩⟩ := hSi k
    obtain ⟨h1, h2⟩ := GlobalTheory.etale_localization_atPrime_isDomain_isIntegrallyClosed A B q
    let e' : Localization.AtPrime q ≃+* (Si k).toSubring :=
      e.toRingEquiv.trans
        { toFun := fun x => ⟨x.1, x.2⟩
          invFun := fun x => ⟨x.1, x.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          map_mul' := fun _ _ => rfl
          map_add' := fun _ _ => rfl }
    exact ⟨e'.symm.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e'⟩
  have hmono' : Monotone fun k => (Si k).toSubring := fun _ _ h => hmono h
  haveI : IsDomain S := isDomain_of_directed _ hmono' hcov fun k => (hdi k).1
  have hic : IsIntegrallyClosed S :=
    isIntegrallyClosed_of_directed _ hmono' hcov (fun k => (hdi k).1) fun k => (hdi k).2
  obtain ⟨α, hα⟩ :=
    GlobalTheory.NCyc.StrictLocLift.exists_ringHom_of_isStrictHenselisation (algebraMap A S) hsh i
  have hle : maximalIdeal S ≤ (maximalIdeal T).comap α := by
    rw [← hmax, Ideal.map_le_iff_le_comap, Ideal.comap_comap, hα]
    intro a ha
    exact map_nonunit i a ha
  refine ⟨S, inferInstance, inferInstance, inferInstance, hsc, inferInstance, hic,
    algebraMap A S, α, hα, ⟨fun s hs => ?_⟩⟩
  by_contra h
  exact (mem_maximalIdeal _).1 (hle ((mem_maximalIdeal s).2 h)) hs

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionLiftSmoothNilpotentThickening
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SecLift

theorem exists_section_lift : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → IsNilpotent (RingHom.ker π) →
    ∀ (X : Over (Sp R)) (X₀ : Over (Sp R₀)) (i : X₀.left ⟶ X.left), IsPullback i X₀.hom X.hom (spMap π) → Smooth X.hom →
    ∀ e₀ : Sp R₀ ⟶ X₀.left, e₀ ≫ X₀.hom = 𝟙 _ → ∃ e : Sp R ⟶ X.left, e ≫ X.hom = 𝟙 _ ∧ e₀ ≫ i = spMap π ≫ e := by
  refine GlobalTheory.T.smooth_section_lift_nilpotent_of_sqZero ?_
  intro R R₀ _ _ π hπ hsq X X₀ i hpb hsm e₀ he₀
  have hnil : IsNilpotent (RingHom.ker π) := ⟨2, by rw [hsq]; rfl⟩
  let g₀ := e₀ ≫ i
  have hg₀ : g₀ ≫ X.hom = spMap π := by
    simp only [g₀, Category.assoc]; rw [hpb.w, ← Category.assoc, he₀, Category.id_comp]
  let J : Set R := {h | ∃ V : X.left.Opens, IsAffineOpen V ∧ LiftIn π X g₀ h V}
  have hS2 := GlobalTheory.T.exists_smooth_section_lift_basicOpen_affine R R₀ π hπ hnil X hsm g₀ hg₀
  have hspan : Ideal.span J = ⊤ := by
    by_contra hne
    obtain ⟨N, hN, hJN⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨f, hf, hfJ⟩ := hS2 ⟨N, hN.isPrime⟩
    exact hf (hJN (Ideal.subset_span hfJ))
  obtain ⟨s, hsJ, hs⟩ := (Ideal.span_eq_top_iff_finite J).1 hspan
  have hV : ∀ k : s, ∃ V : X.left.Opens, IsAffineOpen V ∧ LiftIn π X g₀ k.1 V := fun k => hsJ k.2
  choose V hVa hVl using hV
  obtain ⟨e, he1, he2⟩ :=
    GlobalTheory.T.exists_global_lift_of_chartLocal_lifts_squareZero R R₀ π hπ hsq X hsm g₀ hg₀ s (fun k => k.1) (by simpa using hs) V hVa hVl
  exact ⟨e, he1, he2.symm⟩

end GlobalTheory.SecLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmallChartPairAlongLinearMapStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_small_chart_pair_along_linear_map : ∀ {I₁ : Type} [Fintype I₁] {g₁ : ℕ} {Λ₁ : Type} [AddCommGroup Λ₁] {F₁ : Fam I₁ g₁ Λ₁} {B₁ : Type} [CommRing B₁] {X₁ : Scheme.{0}} {s₁ : X₁ ⟶ Sp B₁} {σ₁ : B₁ →+* Hol F₁.V} {I₂ : Type} [Fintype I₂] {g₂ : ℕ} {Λ₂ : Type} [AddCommGroup Λ₂] {F₂ : Fam I₂ g₂ Λ₂} {B₂ : Type} [CommRing B₂] {X₂ : Scheme.{0}} {s₂ : X₂ ⟶ Sp B₂} {σ₂ : B₂ →+* Hol F₂.V} (u₁ : Unif F₁ s₁ σ₁) (u₂ : Unif F₂ s₂ σ₂) (b : (I₁ → ℂ) → I₂ → ℂ) (hb : AnalyticOnNhd ℂ b F₁.V) (hbV : ∀ z ∈ F₁.V, b z ∈ F₂.V) (M : (Fin g₁ → ℂ) →ₗ[ℂ] (Fin g₂ → ℂ)) (A : Λ₁ →+ Λ₂), (∀ l, ∀ z ∈ F₁.V, F₂.τ (A l) (b z) = M (F₁.τ l z)) → ∃ (K₁ : Charts F₁) (K₂ : Charts F₂) (κ : K₁.K → K₂.K), K₁.Rich ∧ (∀ k, ∃ U, IsAffineOpen U ∧ ∀ p ∈ K₁.W k, ⊤ ≤ u₁.E p ⁻¹ᵁ U) ∧ (∀ k, ∃ U, IsAffineOpen U ∧ ∀ p ∈ K₂.W k, ⊤ ≤ u₂.E p ⁻¹ᵁ U) ∧ (∀ k, ∀ p ∈ K₁.W k, ((b p.1, M p.2) : Tot I₂ g₂) ∈ K₂.W (κ k)) ∧ ∀ l k' k, K₁.le l k' k → K₂.le (A l) (κ k') (κ k) := by
  first | exact @GlobalTheory.AnPer.ChartPair.exists_pair | exact GlobalTheory.AnPer.ChartPair.exists_pair | (intros; apply GlobalTheory.AnPer.ChartPair.exists_pair <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothLogTwistInequalitiesStatement
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smooth_log_twist_inequalities : ∀ T : ℝ, 300 ≤ T → ∃ κ : ℝ → ℝ, ContDiff ℝ ∞ κ ∧ (∃ C : ℝ, ∀ x, x ≤ 0 → |κ x| ≤ C) ∧ (∀ x, x ≤ 0 → 0 ≤ deriv κ x ∧ deriv κ x ≤ 1 ∧ 0 < deriv (deriv κ) x ∧ deriv κ x ^ 2 ≤ deriv (deriv κ) x ∧ wT T x / 8 ≤ (1 - deriv κ x ^ 2 / deriv (deriv κ) x) * Real.exp (κ x)) ∧ (∀ x, -T - 1 ≤ x → x ≤ -T + 1 → Real.exp (κ x) / deriv (deriv κ) x ≤ 16 / 3 ∧ wT T x / 8 ≤ (1 - 5 * (deriv κ x ^ 2 / deriv (deriv κ) x)) * Real.exp (κ x)) := by
  first | exact @GlobalTheory.OTY.exists_log_twist | exact GlobalTheory.OTY.exists_log_twist | (intros; apply GlobalTheory.OTY.exists_log_twist <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareZeroMoveTensorHolomorphicStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_squareZero_move_tensor_holomorphic : ∀ {g : ℕ} {W₀ : Opens (Tot Empty g)} {R : Type} [CommRing R] [Algebra ℂ R] {C : Type} [CommRing C] (ψ : R ⊗[ℂ] Hol W₀ →+* C) (n : Fin g → C), (∀ a b, n a * n b = 0) → ∃ ψ' : R ⊗[ℂ] Hol W₀ →+* C, ∀ x, ψ' x = ψ x + ∑ a, ψ (LinearMap.lTensor R (dw a).toLinearMap x) * n a := by
  first | exact @GlobalTheory.SqZeroMove.sqZeroMove | exact GlobalTheory.SqZeroMove.sqZeroMove | (intros; apply GlobalTheory.SqZeroMove.sqZeroMove <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStrictlyHenselianIndEtaleOverPrime
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.StrictHensPrime

theorem exists_sh_indEt (A : Type) [CommRing A] (p : Ideal A) [p.IsPrime] :
    ∃ (O : Type) (_ : CommRing O) (_ : Algebra A O) (_ : IsLocalRing O), SH O ∧ IndEt A O ∧
      (IsLocalRing.maximalIdeal O).comap (algebraMap A O) = p := by
  classical
  obtain ⟨S, _, _, hH, hloc, hsep, -, -, -, ι, _, _, _, Si, hmono, hcov, hSi⟩ :=
    GlobalTheory.exists_strictHenselisation (Localization.AtPrime p)
      (SeparableClosure (IsLocalRing.ResidueField (Localization.AtPrime p)))
  let _ : Algebra A S := ((algebraMap (Localization.AtPrime p) S).comp
    (algebraMap A (Localization.AtPrime p))).toAlgebra
  have _ : IsScalarTower A (Localization.AtPrime p) S := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hI : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap (Localization.AtPrime p) S) := by
    refine GlobalTheory.StrictHensUnion.indEtale_of_directed_union _ S ι Si hmono hcov fun i => ?_
    obtain ⟨B, _, _, _, q, _, ⟨e⟩⟩ := hSi i
    exact GlobalTheory.StrictHensUnion.indEtale_of_algEquiv e
      (GlobalTheory.StrictHensUnion.indEtale_localization_of_etale _ B q.primeCompl)
  refine ⟨S, inferInstance, inferInstance, inferInstance, ⟨hH, hsep⟩, ?_, ?_⟩
  · exact IndEtaleAtPrime.indEt_of_indEt_atPrime A S p hI
  · rw [IsScalarTower.algebraMap_eq A (Localization.AtPrime p) S, ← Ideal.comap_comap,
      IsLocalRing.maximalIdeal_comap]
    exact Localization.AtPrime.under_maximalIdeal

end GlobalTheory.StrictHensPrime

end

example : ∀ (A : Type) [CommRing A] (p : Ideal A) [p.IsPrime], ∃ (O : Type) (_ : CommRing O) (_ : Algebra A O) (_ : IsLocalRing O), SH O ∧ IndEt A O ∧ (IsLocalRing.maximalIdeal O).comap (algebraMap A O) = p :=
  GlobalTheory.StrictHensPrime.exists_sh_indEt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTangentOfUniformisationJet
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AnPer

theorem exists_tangent_of_jet : ∀ {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g), A.left.IsSeparated → ∀ (W : Opens (Tot Empty g)) (x : Sp (Hol W) ⟶ A.left), (∀ (p : Tot Empty g) (hp : p ∈ W), spMap (Hol.ev p hp).toRingHom ≫ x = (u.ex p.2).left) → x ≫ A.hom = spMap (algebraMap ℂ (Hol W)) → (0 : Tot Empty g) ∈ W → ∀ (w : Fin g → ℂ) (ρ : Hol W →ₐ[ℂ] DualNumber ℂ), (∀ h, (ρ h).fst = h.fn 0 ∧ (ρ h).snd = fderiv ℂ h.fn 0 (0, w)) → ∃ v : epsR ℂ ⟶ A, v.left = spMap ρ.toRingHom ≫ x ∧ IsTangent v ∧ u.IsDiff w v := by
  intro A _ L g u hsep W x hx hxA h0 w ρ hρ
  have hw : (spMap ρ.toRingHom ≫ x) ≫ A.hom = spMap (algebraMap ℂ (DualNumber ℂ)) := by
    rw [Category.assoc, hxA, ← Cris.spMap_comp]
    congr 1
    exact RingHom.ext fun c ↦ ρ.commutes c
  have hfst : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ spMap ρ.toRingHom ≫ x = (u.ex 0).left := by
    have e : (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp ρ.toRingHom = (Hol.ev 0 h0).toRingHom :=
      RingHom.ext fun f ↦ (hρ f).1.trans (Hol.ev_apply 0 h0 f).symm
    rw [← Category.assoc, ← Cris.spMap_comp, e]
    exact hx 0 h0
  refine ⟨Over.homMk (spMap ρ.toRingHom ≫ x) hw, rfl, ?_, ?_⟩
  · change spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ spMap ρ.toRingHom ≫ x = _
    rw [hfst, (u.ker 0).2 u.Λ.zero_mem, Hom.one_def, toUnit_unit, Category.id_comp]
  · intro U h f
    change ⊤ ≤ (spMap ρ.toRingHom ≫ x) ⁻¹ᵁ U at h
    change (evalAt (spMap ρ.toRingHom ≫ x) U h f).snd = _
    have hU0 : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U := by
      rw [← hfst]
      exact fun q _ ↦ h (Set.mem_univ ((spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) q))
    let q₀ : Sp ℂ := (default : PrimeSpectrum ℂ)
    obtain ⟨U', hU', hq, hle⟩ := exists_isAffineOpen_mem_and_subset
      (x := (u.ex 0).left q₀) (U := U) (hU0 (Set.mem_univ q₀))
    have hU0' : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U' := fun q _ ↦ by
      have : q = q₀ := Subsingleton.elim (α := PrimeSpectrum ℂ) q q₀
      subst this
      exact hq
    let W' : Opens (Tot Empty g) :=
      W ⊓ ⟨{p | ⊤ ≤ (u.ex p.2).left ⁻¹ᵁ U'}, (u.hol U' 0).1.preimage continuous_snd⟩
    have h0' : (0 : Tot Empty g) ∈ W' := ⟨h0, hU0'⟩
    obtain ⟨x', hx'U, hx'⟩ := exists_pt_of_affine (fibUnif u) W' (fun _ _ ↦ trivial) U' hU' (fun p hp ↦ hp.2)
    let res : Hol W →ₐ[ℂ] Hol W' := Hol.comap id analyticOnNhd_id fun p hp ↦ hp.1
    have hres : ∀ (k : Hol W), ∀ p ∈ W', (res k).fn p = k.fn p := fun k p hp ↦ Hol.fn_comap _ _ _ k hp
    have hxx : spMap res.toRingHom ≫ x = x' := by
      refine point_hol_ext_of_isSeparated W' hsep _ _ fun p hp ↦ ?_
      have e : (Hol.ev p hp).toRingHom.comp res.toRingHom = (Hol.ev p hp.1).toRingHom :=
        RingHom.ext fun _ ↦ rfl
      rw [hx' p hp, ← Category.assoc, ← Cris.spMap_comp, e]
      exact hx p hp.1
    obtain ⟨ρ', hρ'⟩ := Hol.exists_jet_algHom W' 0 h0' ((0, w) : Tot Empty g)
    have hρρ : ρ'.toRingHom.comp res.toRingHom = ρ.toRingHom := RingHom.ext fun k ↦ by
      change ρ' (res k) = ρ k
      refine TrivSqZeroExt.ext ?_ ?_
      · rw [(hρ' _).1, (hρ _).1, hres k 0 h0']
      · rw [(hρ' _).2, (hρ _).2, Hol.fderiv_fn_congr _ (hres k) h0']
    have hv : spMap ρ.toRingHom ≫ x = spMap ρ'.toRingHom ≫ x' := by
      rw [← hρρ, Cris.spMap_comp, Category.assoc, hxx]
    have hx'U' : ⊤ ≤ x' ⁻¹ᵁ U := fun q hq ↦ hle (hx'U hq)
    obtain ⟨h', hev, -⟩ := GlobalTheory.EvalNat.evalAt_natural ρ'.toRingHom x' U hx'U'
    have e1 : evalAt (spMap ρ.toRingHom ≫ x) U h f = ρ' (evalAt x' U hx'U' f) := by
      refine Eq.trans ?_ (hev f)
      congr 2
    have e2 : ∀ p ∈ W', (evalAt x' U hx'U' f).fn p = valAt' (u.ex p.2).left U f := fun p hp ↦ by
      rw [(evalAt_fn_eq_valAt' W' x' U hx'U' f p hp).2, hx' p hp]
      rfl
    have hd : DifferentiableAt ℂ (fun z ↦ valAt' (u.ex z).left U f) 0 :=
      (u.hol U f).2.differentiableAt ((u.hol U f).1.mem_nhds hU0)
    rw [e1, (hρ' _).2, Hol.fderiv_fn_congr _ e2 h0']
    have hc : HasFDerivAt (fun p : Tot Empty g ↦ valAt' (u.ex p.2).left U f)
        ((fderiv ℂ (fun z ↦ valAt' (u.ex z).left U f) 0).comp (ContinuousLinearMap.snd ℂ _ _)) 0 :=
      HasFDerivAt.comp (0 : Tot Empty g) (g := fun z ↦ valAt' (u.ex z).left U f) (f := Prod.snd)
        hd.hasFDerivAt hasFDerivAt_snd
    rw [hc.fderiv]
    rfl

end GlobalTheory.AnPer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTaylorAlgHom
section
set_option autoImplicit false

noncomputable section

open Filter Topology TopologicalSpace TensorProduct GlobalTheory.AnPer

namespace GlobalTheory.TaylorHom

variable {I I₀ : Type} [Fintype I] [Fintype I₀] {g : ℕ} {W : Opens (Tot I g)} {W₀ : Opens (Tot I₀ g)}

theorem eventually_mem {w : Fin g → ℂ} (h : (((0 : I → ℂ), w) : Tot I g) ∈ W) :
    ∀ᶠ z in 𝓝 (0 : I → ℂ), ((z, w) : Tot I g) ∈ W := by
  have hc : Continuous fun z : I → ℂ ↦ ((z, w) : Tot I g) := by fun_prop
  exact hc.continuousAt.preimage_mem_nhds (W.isOpen.mem_nhds h)

theorem analyticAt_slice (h : Hol W) {w : Fin g → ℂ} (hw : (((0 : I → ℂ), w) : Tot I g) ∈ W) :
    AnalyticAt ℂ (fun z : I → ℂ ↦ h.fn (z, w)) 0 := by
  have hp : AnalyticAt ℂ (fun z : I → ℂ ↦ ((z, w) : Tot I g)) 0 :=
    analyticAt_id.prod analyticAt_const
  exact AnalyticAt.comp (g := h.fn) (f := fun z : I → ℂ ↦ ((z, w) : Tot I g)) (h.analytic _ hw) hp

def coef (hW : ∀ p ∈ W₀, (((0 : I → ℂ), p.2) : Tot I g) ∈ W) (k : ℕ) (v : Fin k → I → ℂ) (h : Hol W) : Hol W₀ :=
  Hol.mk (fun p ↦ iteratedFDeriv ℂ k (fun z ↦ h.fn (z, p.2)) 0 v) fun p hp ↦
    AnalyticAt.comp (g := fun w ↦ iteratedFDeriv ℂ k (fun z ↦ h.fn (z, w)) 0 v) (f := Prod.snd)
      (GlobalTheory.analyticAt_iteratedFDeriv_slice_and_fderiv h.fn p.2 k v (h.analytic _ (hW p hp))).1 analyticAt_snd

theorem fn_coef (hW : ∀ p ∈ W₀, (((0 : I → ℂ), p.2) : Tot I g) ∈ W) (k : ℕ) (v : Fin k → I → ℂ) (h : Hol W)
    {p : Tot I₀ g} (hp : p ∈ W₀) : (coef hW k v h).fn p = iteratedFDeriv ℂ k (fun z ↦ h.fn (z, p.2)) 0 v := by
  unfold coef
  exact Hol.fn_mk _ _ hp

theorem dw_coef (hW : ∀ p ∈ W₀, (((0 : I → ℂ), p.2) : Tot I g) ∈ W) (k : ℕ) (v : Fin k → I → ℂ) (h : Hol W)
    (a : Fin g) : dw a (coef hW k v h) = coef hW k v (dw a h) := by
  refine Hol.ext_fn fun p hp ↦ ?_
  have hH : AnalyticAt ℂ h.fn ((0 : I → ℂ), p.2) := h.analytic _ (hW p hp)
  obtain ⟨hG, hG'⟩ := GlobalTheory.analyticAt_iteratedFDeriv_slice_and_fderiv h.fn p.2 k v hH

  have hL : (dw a (coef hW k v h)).fn p =
      fderiv ℂ (fun w ↦ iteratedFDeriv ℂ k (fun z ↦ h.fn (z, w)) 0 v) p.2 (Pi.single a 1) := by
    rw [show dw a (coef hW k v h) =
        Hol.der ((0, Pi.single a 1) : Tot I₀ g) (coef hW k v h) from rfl, Hol.fn_der _ _ hp,
      Hol.fderiv_fn_congr (F := fun q : Tot I₀ g ↦ iteratedFDeriv ℂ k (fun z ↦ h.fn (z, q.2)) 0 v) _
        (fun q hq ↦ fn_coef hW k v h hq) hp]
    have hc := (hG.differentiableAt.hasFDerivAt.comp p (hasFDerivAt_snd (p := p))).fderiv
    rw [show (fun q : Tot I₀ g ↦ iteratedFDeriv ℂ k (fun z ↦ h.fn (z, q.2)) 0 v) =
        (fun w ↦ iteratedFDeriv ℂ k (fun z ↦ h.fn (z, w)) 0 v) ∘ Prod.snd from rfl, hc]
    rfl
  have hR : (coef hW k v (dw a h)).fn p =
      iteratedFDeriv ℂ k (fun z ↦ fderiv ℂ h.fn (z, p.2) (0, Pi.single a 1)) 0 v := by
    rw [fn_coef hW k v (dw a h) hp]
    have hev : (fun z : I → ℂ ↦ (dw a h).fn (z, p.2)) =ᶠ[𝓝 0]
        fun z ↦ fderiv ℂ h.fn (z, p.2) (0, Pi.single a 1) := by
      filter_upwards [eventually_mem (hW p hp)] with z hz
      exact Hol.fn_der _ _ hz
    exact congrFun (congrArg DFunLike.coe ((hev.iteratedFDeriv (𝕜 := ℂ) k).eq_of_nhds)) v
  rw [hL, hR]
  exact hG' _

variable [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D]

def poly (hW : ∀ p ∈ W₀, (((0 : I → ℂ), p.2) : Tot I g) ∈ W) (N : ℕ) (t : I → D) (h : Hol W) : D ⊗[ℂ] Hol W₀ :=
  ∑ k ∈ Finset.range (N + 1), ∑ s : Fin k → I,
    ((k.factorial : ℂ)⁻¹ • ∏ a, t (s a)) ⊗ₜ[ℂ] coef hW k (fun a ↦ Pi.single (s a) 1) h

theorem ev_poly (hW : ∀ p ∈ W₀, (((0 : I → ℂ), p.2) : Tot I g) ∈ W) (N : ℕ) (t : I → D) (h : Hol W)
    (p : Tot I₀ g) (hp : p ∈ W₀) :
    Algebra.TensorProduct.lift (AlgHom.id ℂ D) ((Algebra.ofId ℂ D).comp (Hol.ev p hp)) (fun _ _ ↦ Commute.all _ _)
      (poly hW N t h) = GlobalTheory.PeriodFamily.taylor N t fun z ↦ h.fn (z, p.2) := by
  simp only [poly, map_sum, Algebra.TensorProduct.lift_tmul, AlgHom.id_apply, AlgHom.comp_apply,
    Algebra.ofId_apply, Hol.ev_apply, fn_coef hW _ _ h hp, GlobalTheory.PeriodFamily.taylor]
  refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun s _ ↦ ?_
  rw [mul_comm, ← Algebra.smul_def, smul_smul, mul_comm]

theorem exists_taylor_algHom : ∀ {I I₀ : Type} [Fintype I] [DecidableEq I] [Fintype I₀] {g : ℕ} {D : Type} [CommRing D]
    [Algebra ℂ D] (N : ℕ) (t : I → D), (∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) →
    ∀ (W : Opens (Tot I g)) (W₀ : Opens (Tot I₀ g)), (∀ p ∈ W₀, (((0 : I → ℂ), p.2) : Tot I g) ∈ W) →
    ∃ Ta : Hol W →ₐ[ℂ] D ⊗[ℂ] Hol W₀, (∀ (h : Hol W) (p : Tot I₀ g) (hp : p ∈ W₀),
      Algebra.TensorProduct.lift (AlgHom.id ℂ D) ((Algebra.ofId ℂ D).comp (Hol.ev p hp)) (fun _ _ ↦ Commute.all _ _)
        (Ta h) = GlobalTheory.PeriodFamily.taylor N t fun z ↦ h.fn (z, p.2)) ∧
      ∀ a h, Ta (dw a h) = LinearMap.lTensor D (dw a).toLinearMap (Ta h) := by
  intro I I₀ _ _ _ g D _ _ N t ht W W₀ hW

  have slice_eq : ∀ {p : Tot I₀ g} (_ : p ∈ W₀) {F : (I → ℂ) → ℂ} (x : Hol W),
      (∀ z, ((z, p.2) : Tot I g) ∈ W → x.fn (z, p.2) = F z) →
      GlobalTheory.PeriodFamily.taylor N t (fun z ↦ x.fn (z, p.2)) = GlobalTheory.PeriodFamily.taylor N t F := by
    intro p hp F x hx
    apply GlobalTheory.PeriodFamily.taylor_congr_germ
    filter_upwards [eventually_mem (hW p hp)] with z hz
    exact hx z hz
  have hconst : ∀ c : ℂ, poly hW N t (algebraMap ℂ (Hol W) c) = algebraMap ℂ (D ⊗[ℂ] Hol W₀) c := by
    intro c
    apply GlobalTheory.tensor_hol_ext_of_values W₀ D
    intro p hp
    rw [ev_poly, AlgHom.commutes, slice_eq hp (F := fun _ ↦ c) _ fun z hz ↦ Hol.fn_algebraMap c hz,
      GlobalTheory.PeriodFamily.taylor_const_fun]
  have hadd : ∀ x y : Hol W, poly hW N t (x + y) = poly hW N t x + poly hW N t y := by
    intro x y
    apply GlobalTheory.tensor_hol_ext_of_values W₀ D
    intro p hp
    rw [map_add, ev_poly, ev_poly, ev_poly,
      slice_eq hp (F := fun z ↦ x.fn (z, p.2) + y.fn (z, p.2)) _ fun z hz ↦ Hol.fn_add x y hz,
      GlobalTheory.PeriodFamily.taylor_add_of_analyticAt N t _ _ (analyticAt_slice x (hW p hp))
        (analyticAt_slice y (hW p hp))]
  have hmul : ∀ x y : Hol W, poly hW N t (x * y) = poly hW N t x * poly hW N t y := by
    intro x y
    apply GlobalTheory.tensor_hol_ext_of_values W₀ D
    intro p hp
    rw [map_mul, ev_poly, ev_poly, ev_poly,
      slice_eq hp (F := fun z ↦ x.fn (z, p.2) * y.fn (z, p.2)) _ fun z hz ↦ Hol.fn_mul x y hz,
      GlobalTheory.PeriodFamily.taylor_mul_of_prod_eq_zero N t ht _ _ (analyticAt_slice x (hW p hp))
        (analyticAt_slice y (hW p hp))]
  refine ⟨{ toFun := poly hW N t
            map_one' := by simpa only [map_one] using hconst 1
            map_mul' := hmul
            map_zero' := by simpa only [map_zero] using hconst 0
            map_add' := hadd
            commutes' := hconst }, fun h p hp ↦ ev_poly hW N t h p hp, fun a h ↦ ?_⟩
  show poly hW N t (dw a h) = LinearMap.lTensor D (dw a).toLinearMap (poly hW N t h)
  simp only [poly, map_sum, LinearMap.lTensor_tmul]
  refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun s _ ↦ ?_
  rw [← dw_coef]
  rfl

end GlobalTheory.TaylorHom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoWindowsOfMatrixCongrModTauStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIso_windows_of_matrix_congr_mod_tau : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (d k : ℕ) (U U' : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B), IsUnit U → IsUnit U' → (∀ i j, F.τ ∣ U i j - U' i j) → IsNil F.θ F.σ (U * blk d k (p : F.B) 1) → ∃ X : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B, (∀ i j, F.τ ∣ X i j - (1 : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) i j) ∧ X * (U' * blk d k (p : F.B) 1) = U * blk d k (p : F.B) 1 * X.map F.σ := by
  first | exact @GlobalTheory.WindowIso.window_iso | exact GlobalTheory.WindowIso.window_iso | (intros; apply GlobalTheory.WindowIso.window_iso <;> assumption)
end

