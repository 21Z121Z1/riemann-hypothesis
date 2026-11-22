import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0032
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0021
import Development.WeilBound.CoreStatements.HodgeTatePoints.HasLenOfEquiv
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0001
import Mathlib
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0003
import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0031
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0022
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0025
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0015
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0050
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
import Development.WeilBound.CoreStatements.HodgeTatePoints.FrameExpandLoc
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.GeoNum
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle0006
import Development.WeilBound.CoreStatements.HodgeTatePoints.GfForms

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.EqOfPowMul
section
noncomputable section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace PositivityTheory.HtPt.Re

def splitEquiv {N N₁ N₂ : Type} [AddCommGroup N] [AddCommGroup N₁] [AddCommGroup N₂]
    (ι₁ : N₁ →+ N) (π₁ : N →+ N₁) (ι₂ : N₂ →+ N) (π₂ : N →+ N₂) (h11 : ∀ y, π₁ (ι₁ y) = y)
    (h22 : ∀ y, π₂ (ι₂ y) = y) (hsum : ∀ x, ι₁ (π₁ x) + ι₂ (π₂ x) = x) (h12 : ∀ y, π₁ (ι₂ y) = 0)
    (h21 : ∀ y, π₂ (ι₁ y) = 0) : N₁ × N₂ ≃+ N where
  toFun z := ι₁ z.1 + ι₂ z.2
  invFun x := (π₁ x, π₂ x)
  left_inv z := by simp [h11, h22, h12, h21]
  right_inv x := hsum x
  map_add' a b := by simp only [Prod.fst_add, Prod.snd_add, map_add]; abel

theorem ret_colen {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R]
    [Algebra R C] {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
    (AA : HopfOrder (C := C) R N) {N₁ : Type} [AddCommGroup N₁] [Fintype N₁] [DecidableEq N₁]
    {N₂ : Type} [AddCommGroup N₂] [Fintype N₂] [DecidableEq N₂]
    (ι₁ : N₁ →+ N) (π₁ : N →+ N₁) (ι₂ : N₂ →+ N) (π₂ : N →+ N₂) (h11 : ∀ y, π₁ (ι₁ y) = y)
    (h22 : ∀ y, π₂ (ι₂ y) = y) (hsum : ∀ x, ι₁ (π₁ x) + ι₂ (π₂ x) = x) (h12 : ∀ y, π₁ (ι₂ y) = 0)
    (h21 : ∀ y, π₂ (ι₁ y) = 0) (hs₁ : ∀ g ∈ AA.carrier, (fun x => g (ι₁ (π₁ x))) ∈ AA.carrier)
    (a b : NNReal)
    (ha : HasColen R v (AA.carrier.map (LinearMap.funLeft R C (ι₁ : N₁ → N))) a)
    (hb : HasColen R v (AA.carrier.map (LinearMap.funLeft R C (ι₂ : N₂ → N))) b) :
    HasColen R v AA.carrier (a ^ Fintype.card N₂ * b ^ Fintype.card N₁) := by
  let e := splitEquiv ι₁ π₁ ι₂ π₂ h11 h22 hsum h12 h21
  have e1 : (fun y : N₁ => e (y, 0)) = ι₁ := by
    funext y
    show ι₁ y + ι₂ 0 = ι₁ y
    simp
  have e2 : (fun y : N₂ => e (0, y)) = ι₂ := by
    funext y
    show ι₁ 0 + ι₂ y = ι₂ y
    simp
  have h := tn_char AA e (fun g hg => by
    convert hs₁ g hg using 3 with x
    exact congrFun e1 _)
  rw [e1, e2] at h
  have h2 := hasColen_tn ha hb
  rw [← h] at h2
  have h3 := hasColen_map v e.symm _ _ h2
  rwa [show AA.carrier.map (LinearMap.funLeft R C (e : N₁ × N₂ → N)) =
    AA.carrier.map (pbE (C := C) (R := R) e : (N → C) →ₗ[R] (N₁ × N₂ → C)) from rfl,
    map_pbE_symm] at h3

theorem eq_of_pow_mul {x₁ y₁ x₂ y₂ : NNReal} {m n : ℕ} (hm : m ≠ 0) (h₁ : x₁ ≤ y₁) (h₂ : x₂ ≤ y₂)
    (hy : y₂ ≠ 0) (h : x₁ ^ m * x₂ ^ n = y₁ ^ m * y₂ ^ n) : x₁ = y₁ := by
  refine le_antisymm h₁ (not_lt.1 fun hlt => ?_)
  have a : x₁ ^ m < y₁ ^ m := pow_lt_pow_left₀ hlt zero_le hm
  have b : x₂ ^ n ≤ y₂ ^ n := pow_le_pow_left₀ zero_le h₂ n
  have c : 0 < y₂ ^ n := pow_pos (pos_iff_ne_zero.2 hy) n
  exact absurd h (ne_of_lt (lt_of_le_of_lt (mul_le_mul_of_nonneg_left b zero_le)
    (mul_lt_mul_of_pos_right a c)))

theorem ret_tight : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], (∀ x : N, p • x = 0) → ∀ AA : HopfOrder (C := C) R N, ∀ (N' : Type) [AddCommGroup N'] [Fintype N'] [DecidableEq N'], ∀ (ι : N' →+ N) (π : N →+ N'), (∀ y, π (ι y) = y) → (∀ g ∈ AA.carrier, (fun x => g (ι (π x))) ∈ AA.carrier) → IsTight v p AA.carrier → IsTight v p (AA.carrier.map (LinearMap.funLeft R C (ι : N' → N))) := by
  intro p _ C _ _ _ v R _ _ hv hp N _ _ _ hN AA N' _ _ _ ι π hπ hst hT
  classical
  have hcnt := @PositivityTheory.HtPt.Ra.cnt
  have hlens := @PositivityTheory.HtPt.Rc.lens
  let ι₂ : π.ker →+ N := π.ker.subtype
  let π₂ : N →+ π.ker := (AddMonoidHom.id N - ι.comp π).codRestrict π.ker (fun x => by
    simp [AddMonoidHom.mem_ker, hπ])
  have hπ₂ : ∀ x, ι₂ (π₂ x) = x - ι (π x) := fun _ => rfl
  have h12 : ∀ y, π (ι₂ y) = 0 := fun y => y.2
  have h22 : ∀ y, π₂ (ι₂ y) = y := fun y => Subtype.ext (by
    show ι₂ (π₂ (ι₂ y)) = ι₂ y
    rw [hπ₂, h12]; simp)
  have h21 : ∀ y, π₂ (ι y) = 0 := fun y => Subtype.ext (by
    show ι₂ (π₂ (ι y)) = 0
    rw [hπ₂, hπ]; simp)
  have hsum : ∀ x, ι (π x) + ι₂ (π₂ x) = x := fun x => by rw [hπ₂]; simp
  have hs₂ : ∀ g ∈ AA.carrier, (fun x => g (ι₂ (π₂ x))) ∈ AA.carrier :=
    (stabadd C R N N AA AA (AddMonoidHom.id N) (ι.comp π) (fun g hg => hg) hst).2
  obtain ⟨⟨A₁, hA₁⟩, -⟩ := ret_hopf p C v R hv hp N AA N' ι π hπ hst
  obtain ⟨⟨A₂, hA₂⟩, -⟩ := ret_hopf p C v R hv hp N AA π.ker ι₂ π₂ h22 hs₂
  have hN₁ : ∀ y : N', p • y = 0 := fun y => by rw [← hπ y, ← map_nsmul, hN, map_zero]
  have hN₂ : ∀ y : π.ker, p • y = 0 := fun y => by rw [← h22 y, ← map_nsmul, hN, map_zero]
  obtain ⟨a₁, c₁, o₁, -, hc₁0, -, ha₁, hc₁, ho₁⟩ := hlens p C v R hv hp N' hN₁ A₁
  obtain ⟨a₂, c₂, o₂, -, hc₂0, ho₂0, ha₂, hc₂, ho₂⟩ := hlens p C v R hv hp π.ker hN₂ A₂
  have l₁ := (hcnt p C v R hv hp N' hN₁ A₁ _ _ ha₁ hc₁).1
  have l₂ := (hcnt p C v R hv hp π.ker hN₂ A₂ _ _ ha₂ hc₂).1
  have m₁ := u4 p C v R hv hp N' hN₁ A₁ _ _ hc₁ ho₁
  have m₂ := u4 p C v R hv hp π.ker hN₂ A₂ _ _ hc₂ ho₂
  rw [hA₁] at ha₁ hc₁ ho₁
  rw [hA₂] at ha₂ hc₂ ho₂
  obtain ⟨a, c, o, ha, hc, ho, ea, eo⟩ := hT
  obtain rfl := hasLen_unique hv ha
    (ret_af p C v R hv hp N AA N' π.ker ι π ι₂ π₂ hπ h22 hsum h12 h21 hst hs₂ _ _ ha₁ ha₂)
  obtain rfl := hasLen_unique hv ho
    (ret_om hv AA ι π ι₂ π₂ hπ h22 hsum h12 h21 hst hs₂ _ _ ho₁ ho₂)
  obtain rfl := hasColen_unique hv AA.lat hc
    (ret_colen AA ι π ι₂ π₂ hπ h22 hsum h12 h21 hst _ _ hc₁ hc₂)
  have hcard : Fintype.card N = Fintype.card N' * Fintype.card π.ker := by
    rw [← Fintype.card_prod]
    exact (Fintype.card_congr (splitEquiv ι π ι₂ π₂ hπ h22 hsum h12 h21).toEquiv).symm
  rw [hcard] at ea eo
  refine ⟨a₁, c₁, o₁, ha₁, hc₁, ho₁, ?_, ?_⟩
  · refine eq_of_pow_mul (m := Fintype.card π.ker) (n := Fintype.card N') Fintype.card_ne_zero
      l₁ l₂ (pow_ne_zero _ hc₂0) ?_
    calc _ = (a₁ * a₂) ^ (Fintype.card N' * Fintype.card π.ker * (p - 1)) := by ring
      _ = _ := by rw [ea]; ring
  · refine (eq_of_pow_mul (m := Fintype.card π.ker) (n := Fintype.card N') Fintype.card_ne_zero
      m₁ m₂ (pow_ne_zero _ ho₂0) ?_).symm
    calc _ = (c₁ ^ Fintype.card π.ker * c₂ ^ Fintype.card N') ^ 2 := by ring
      _ = _ := by rw [← eo]; ring

end PositivityTheory.HtPt.Re
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.FinrankDualEqOfProjective
section
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

noncomputable section

namespace PositivityTheory.HtPt.Ge

theorem finrank_dual_eq_of_projective (A K : Type) [CommRing A] [IsDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] (M : Type) [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Module.Projective A M] : finrank A (Module.Dual A M) = finrank A M := by
  classical
  haveI := Module.finitePresentation_of_projective A M
  let S := nonZeroDivisors A
  let F := Localization S
  let f := LocalizedModule.mkLinearMap S M
  let g := Algebra.linearMap A F
  have e1 : finrank A (Module.Dual A M) = finrank A (LocalizedModule S M →ₗ[F] F) :=
    (IsLocalizedModule.finrank_eq S (IsLocalizedModule.mapExtendScalars S f g F) le_rfl).symm
  rw [e1, ← IsLocalization.finrank_eq F S le_rfl, Subspace.dual_finrank_eq,
    IsLocalization.finrank_eq F S le_rfl, IsLocalizedModule.finrank_eq S f le_rfl]

theorem ringOfIntegers_mem_range (A K : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Field K]
    [Algebra A K] [IsFractionRing A K] {E : Type} [Field E] [NumberField E] (σ : E →+* K) (a : 𝓞 E) :
    σ (a : E) ∈ (algebraMap A K).range := by
  have h1 : IsIntegral ℤ (σ (a : E)) := (RingOfIntegers.isIntegral_coe a).map σ.toIntAlgHom
  have h2 : IsIntegral A (σ (a : E)) := h1.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
  exact ⟨y, hy⟩

def qLin {A K : Type} [CommRing A] [Field K] [Algebra A K] {E : Type} [Field E] [NumberField E]
    {c : E ≃+* E} {p R N : ℕ} {Ω : Type} [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω]
    (D : HTChart A K c p R N Ω) (σ : E →+* K) : (Fin N → A) →ₗ[A] Ω where
  toFun := D.q σ
  map_add' x y := by simp [HTChart.q, add_smul, Finset.sum_add_distrib]
  map_smul' a x := by simp [HTChart.q, Finset.smul_sum, mul_smul]

theorem chart_sequence : ChartSequence := by
  intro A K _ _ _ _ _ _ _ _ E _ _ c hc p R N _ Ω _ _ _ _ D κ m hκ htest hproj'
  have hκR : κ ∣ (p : A) ^ R := dvd_trans (dvd_mul_right κ _) hκ
  have h1 := PositivityTheory.HtPt.Gc.chart_ii A K E c hc p R N Ω D κ hκR hproj' htest
  refine ⟨h1, ?_⟩
  intro σ d d' hd hd' hP1 hP2
  have hinj : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  have hint : ∀ (σ : E →+* K) (a : 𝓞 E), σ (a : E) ∈ (algebraMap A K).range :=
    fun σ a => ringOfIntegers_mem_range A K σ a
  obtain ⟨⟨i, hi⟩, -, hr⟩ :=
    PositivityTheory.HtPt.Ga.dual_map A K hinj E c hc p R N Ω D κ σ d m hint hd hκ h1.2 hP2
  obtain ⟨-, -, hsurj⟩ := PositivityTheory.HtPt.Ga.q_surj A K hinj E c hc p R N Ω D κ σ m (hint σ) hκ h1.2
  have hcz := PositivityTheory.HtPt.Gd.chart_comp_zero A K E c hc p R N Ω D κ σ d d' m i hκ hd hd' h1.2
    hP1 hP2 htest hi
  refine ⟨i, hi, hr i hi, ?_, hsurj⟩
  intro x
  constructor
  · rintro ⟨y, hy, hxy⟩
    by_cases hu : IsUnit (p : A)
    · obtain ⟨u, hu⟩ := hu
      refine ⟨0, (↑u⁻¹ : A) ^ m • x, ?_⟩
      rw [map_zero, zero_add, smul_smul, ← mul_pow, ← hu, Units.mul_inv, one_pow, one_smul]
    · haveI : Module.Finite A (D.omHT σ) := Module.Finite.iff_fg.mpr (PositivityTheory.HtPt.Gd.omHT_fg D σ)
      haveI : Module.Finite A (D.omHT (σ.comp c.toRingHom)) :=
        Module.Finite.iff_fg.mpr (PositivityTheory.HtPt.Gd.omHT_fg D _)
      let q' : (Fin N → A) →ₗ[A] D.omHT σ :=
        (qLin D σ).codRestrict (D.omHT σ) (PositivityTheory.HtPt.Ga.q_mem D σ)
      have hrank : finrank A (Module.Dual A (D.omHT (σ.comp c.toRingHom))) +
          finrank A (D.omHT σ) = N := by
        rw [finrank_dual_eq_of_projective A K (D.omHT (σ.comp c.toRingHom)), add_comm]
        exact PositivityTheory.HtPt.Gb.chart_rank A K E c hc p R N Ω D κ σ d d' hu hκR hd hd' hP1 hP2 htest
      obtain ⟨rr, hrr⟩ := hr i hi
      obtain ⟨w, x', hx⟩ := PositivityTheory.HtPt.Gd.split_exact A
        (Module.Dual A (D.omHT (σ.comp c.toRingHom))) (D.omHT σ) N ((p : A) ^ m) i rr q' hrank hrr
        (fun z => by
          obtain ⟨x0, y', hy', h⟩ := hsurj z.1 z.2
          exact ⟨x0, ⟨y', hy'⟩, Subtype.ext h⟩)
        (fun w => by
          obtain ⟨y0, hy0, h0⟩ := hcz w
          exact ⟨⟨y0, hy0⟩, Subtype.ext h0⟩)
        x ⟨⟨y, hy⟩, Subtype.ext hxy⟩
      exact ⟨w, x', hx⟩
  · rintro ⟨w, x', rfl⟩
    obtain ⟨y0, hy0, h0⟩ := hcz w
    refine ⟨y0 + D.q σ x', (D.omHT σ).add_mem hy0 (PositivityTheory.HtPt.Ga.q_mem D σ x'), ?_⟩
    have hq : ∀ z, D.q σ z = qLin D σ z := fun _ => rfl
    rw [hq, map_add, map_smul, ← hq, ← hq, h0, smul_add]
    all_goals rfl

end PositivityTheory.HtPt.Ge
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.FlagbGeo
section
noncomputable section

namespace PositivityTheory.HtPt.Flagb

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem unitAt_of_isUnit (q : Cpt ξ) (u : X.presheaf.stalk q.1) (hu : IsUnit u) : unitAt ξ q (genMap ξ q u) := by
  obtain ⟨u, rfl⟩ := hu
  refine ⟨(u.isUnit.map _).ne_zero, ⟨_, rfl⟩, ⟨(u⁻¹ : _ˣ), map_units_inv _ u⟩⟩

def secMap (ξ : Spec (CommRingCat.of Ω) ⟶ X) (U : X.Opens) (hg : genPt ξ ∈ U) : Γ(X, U) →+* Ω :=
  (Scheme.stalkClosedPointTo ξ).hom.comp (X.presheaf.germ U (ξ (IsLocalRing.closedPoint Ω)) hg).hom

theorem genMap_germ (q : Cpt ξ) (U : X.Opens) (hq : q.1 ∈ U) (hg : genPt ξ ∈ U) (f : Γ(X, U)) :
    genMap ξ q ((X.presheaf.germ U q.1 hq).hom f) = secMap ξ U hg f := by
  obtain ⟨q, h⟩ := q
  have := X.presheaf.germ_stalkSpecializes_apply (x := ξ (IsLocalRing.closedPoint Ω)) hq h f
  exact congrArg (Scheme.stalkClosedPointTo ξ).hom this

theorem exists_point {κ : Type} {x : κ → Ω} (tie : CoordTie ℤ ξ x) (c : κ) (hc : x c ≠ 0) {o : Type} [CommRing o]
    [Algebra o Ω] (A : Subalgebra o Ω) (hA : ∀ j, x j / x c ∈ A) (m : Ideal A) [hm : m.IsPrime] :
    ∃ q : Cpt ξ, InChart ξ x c q ∧ (∀ z ∈ regAt ξ q, ∃ s ∉ m, ∃ a : A, (s : Ω) * z = a) ∧
      ∀ n : ℕ, (n : A) ∉ m → unitAt ξ q (n : Ω) := by
  obtain ⟨U, hU, hUm⟩ := tie.affine c hc
  have hreg : ∀ a : Ω, a ∈ regAt ξ ⟨genPt ξ, specializes_rfl⟩ := by
    intro a
    obtain ⟨s, hs⟩ := tie.gen.bij.2 a
    refine ⟨s, ?_⟩
    unfold genMap
    have : X.presheaf.stalkSpecializes (specializes_rfl : genPt ξ ⤳ genPt ξ) = 𝟙 _ :=
      X.presheaf.stalkSpecializes_refl _
    erw [this, Category.id_comp]
    exact hs
  have hg : genPt ξ ∈ U := (hUm _).2 ⟨specializes_rfl, hc, fun c' => hreg _⟩
  let ψ : Γ(X, U) →+* Ω := secMap ξ U hg
  have hψ : ∀ (q : Cpt ξ) (hq : q.1 ∈ U) (f : Γ(X, U)), genMap ξ q ((X.presheaf.germ U q.1 hq).hom f) = ψ f := by
    intro q hq f
    exact genMap_germ q U hq hg f
  have hψA : ∀ f, ψ f ∈ A := by
    intro f
    have h1 : ψ f ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c) :=
      (tie.ring c hc _).2 fun q hq => ⟨_, hψ q ((hUm _).2 ⟨q.2, hq⟩) f⟩
    have h2 : Algebra.adjoin ℤ (Set.range fun j => x j / x c) ≤ subalgebraOfSubring A.toSubring :=
      Algebra.adjoin_le (by rintro _ ⟨j, rfl⟩; exact hA j)
    exact h2 h1
  let ψA : Γ(X, U) →+* A := ψ.codRestrict A hψA
  let 𝔭 : PrimeSpectrum Γ(X, U) := ⟨m.comap ψA, inferInstance⟩
  have hq : hU.fromSpec 𝔭 ∈ U := by
    have : hU.fromSpec 𝔭 ∈ Set.range hU.fromSpec := ⟨_, rfl⟩
    rwa [hU.range_fromSpec] at this
  obtain ⟨hs, hin⟩ := (hUm _).1 hq
  letI : Algebra Γ(X, U) (X.presheaf.stalk (hU.fromSpec 𝔭)) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hU.fromSpec 𝔭, hq⟩
  have hloc : IsLocalization 𝔭.asIdeal.primeCompl (X.presheaf.stalk (hU.fromSpec 𝔭)) :=
    hU.isLocalization_stalk' 𝔭 hq
  have hal : ∀ f, genMap ξ ⟨_, hs⟩ (algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec 𝔭)) f) = ψ f :=
    fun f => hψ ⟨_, hs⟩ hq f
  refine ⟨⟨_, hs⟩, hin, ?_, fun n hn => ?_⟩
  · rintro _ ⟨z, rfl⟩
    obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj (S := X.presheaf.stalk (hU.fromSpec 𝔭)) 𝔭.asIdeal.primeCompl z
    refine ⟨ψA s, s.2, ψA a, ?_⟩
    have := congrArg (genMap ξ ⟨_, hs⟩) h
    rw [map_mul, hal, hal] at this
    exact (mul_comm _ _).trans this
  · have hn' : (n : Γ(X, U)) ∈ 𝔭.asIdeal.primeCompl := by
      show ψA n ∉ m
      rwa [map_natCast]
    have := unitAt_of_isUnit ⟨_, hs⟩ _ (IsLocalization.map_units (X.presheaf.stalk (hU.fromSpec 𝔭)) ⟨_, hn'⟩)
    rwa [hal, map_natCast] at this

theorem unitAt_nat (q : Cpt ξ) (n : ℕ) (hn : n ≠ 0) (h : ∀ r : ℕ, r.Prime → r ∣ n → unitAt ξ q (r : Ω)) :
    unitAt ξ q (n : Ω) := by
  induction n using induction_on_primes with
  | zero => exact absurd rfl hn
  | one => exact ⟨by simp, by simpa using one_mem _, by simpa using one_mem _⟩
  | prime_mul p a hp ih =>
    have h1 := h p hp (dvd_mul_right _ _)
    have h2 := ih (right_ne_zero_of_mul hn) fun r hr hd => h r hr (hd.mul_left _)
    rw [Nat.cast_mul]
    exact ⟨mul_ne_zero h1.1 h2.1, mul_mem h1.2.1 h2.2.1, by rw [mul_inv]; exact mul_mem h1.2.2 h2.2.2⟩

theorem lat_stable {G : Over X} [GrpObj G] {L : Type} [AddCommGroup L] [Module Ω L] (M : LieModel G ξ L)
    (f : G ⟶ G) [IsMonHom f] (T : L →ₗ[Ω] L) (hT : M.IsDiffOf f T) (q : Cpt ξ) (e : L) (he : e ∈ M.lat q) :
    T e ∈ M.lat q := by
  induction he using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, h1, h2⟩ := hx
    refine Submodule.subset_span ⟨v ≫ f, ?_, ?_⟩
    · unfold IsTanAt at h1 ⊢
      rw [Over.comp_left, ← Category.assoc, h1, ← Over.comp_left, MonObj.one_comp]
    · rw [hT x, Over.comp_left, Over.comp_left, h2]
      exact Category.assoc _ _ _
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx =>
    have : T (c • x) = c • T x := map_smul T (c : Ω) x
    rw [this]; exact Submodule.smul_mem _ c hx

end PositivityTheory.HtPt.Flagb
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.GeTriv
section
open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

namespace PositivityTheory.HtPt.Ge

theorem chartMon_ne_zero {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω}
    {s : ∀ k, J k} (hs : mseg y s ≠ 0) (a : K → ℤ) : chartMon y s a ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun k hk => zpow_ne_zero _ (Finset.prod_ne_zero_iff.1 hs k hk)

theorem trivflag_charts : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) [CharZero Ω] (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R m j k : ℕ) [Fact p.Prime] (V : Type) [AddCommGroup V] [Module Ω V] (Dc : ∀ s : {s : ∀ k, J k // mseg y s ≠ 0}, HTChart (chartRing o (mseg y) s.1) Ω c p R (j + k) V) (σ : E →+* Ω) (d : Ω) (dd : ∀ s : {s : ∀ k, J k // mseg y s ≠ 0}, chartRing o (mseg y) s.1) (i : ∀ s : {s : ∀ k, J k // mseg y s ≠ 0}, Module.Dual (chartRing o (mseg y) s.1) ((Dc s).omHT (σ.comp c.toRingHom)) →ₗ[chartRing o (mseg y) s.1] (Fin (j + k) → chartRing o (mseg y) s.1)) (bW : ∀ s : {s : ∀ k, J k // mseg y s ≠ 0}, Module.Basis (Fin j) (chartRing o (mseg y) s.1) (Module.Dual (chartRing o (mseg y) s.1) ((Dc s).omHT (σ.comp c.toRingHom)))) (bM : ∀ s : {s : ∀ k, J k // mseg y s ≠ 0}, Module.Basis (Fin k) (chartRing o (mseg y) s.1) ((Dc s).omHT σ)) (wW : Fin j → Module.Dual Ω V) (wM : Fin k → V) (b : Fin (j + k) → K → ℤ), (∀ s : {s : ∀ k, J k // mseg y s ≠ 0}, IsFractionRing (chartRing o (mseg y) s.1) Ω) → (∀ (s : {s : ∀ k, J k // mseg y s ≠ 0}) (σ' : E →+* Ω) (a : 𝓞 E), σ' (a : E) ∈ chartRing o (mseg y) s.1) → (∀ s, (dd s : Ω) = d ∧ GeneratesDiff σ (dd s)) → (∀ s t, (Dc s).ρΩ = (Dc t).ρΩ ∧ (Dc s).e = (Dc t).e) → (∀ (s t : {s : ∀ k, J k // mseg y s ≠ 0}) (σ' : E →+* Ω), ∀ x ∈ (Dc s).omHT σ', ∃ n : ℕ, (mseg y s.1 / mseg y t.1) ^ n • x ∈ (Dc t).omHT σ') → (∀ (s t : {s : ∀ k, J k // mseg y s ≠ 0}) (σ' : E →+* Ω) x, ∃ n : ℕ, ∃ z ∈ (Dc t).omHT σ', (mseg y s.1 / mseg y t.1) ^ n • eigProj (Dc t).ρΩ σ' ((Dc s).h x - (Dc t).h x) = ((p : Ω) ^ m) • z) → (∀ s, (Dc s).IsDualMap σ (dd s) m (i s) ∧ (Dc s).ExactMod σ m (i s) ∧ ∀ x, (Dc s).q σ x ∈ (Dc s).omHT σ) → m ≤ R → (∀ (s : {s : ∀ k, J k // mseg y s ≠ 0}) a, ∃ cf : Fin j → Ω, (∀ a', a < a' → cf a' = 0) ∧ cf a = chartMon y s.1 (b (Fin.castAdd k a)) ∧ ∀ z : (Dc s).omHT (σ.comp c.toRingHom), ((bW s a z : chartRing o (mseg y) s.1) : Ω) = ∑ a', cf a' * wW a' z) → (∀ (s : {s : ∀ k, J k // mseg y s ≠ 0}) a, ∃ cf : Fin k → Ω, (∀ a', a < a' → cf a' = 0) ∧ cf a = chartMon y s.1 (b (Fin.natAdd j a)) ∧ ((bM s a : (Dc s).omHT σ) : V) = ∑ a', cf a' • wM a') → Num.TrivFlagMod o ((p : o) ^ m) y (j + k) b := by
  intro o _ Ω _ _ K _ J _ y _ E _ _ c hc p R m j k _ V _ _ Dc σ d dd i bW bM wW wM b hfr hint hdd hρe hM hh hi hm
    hW hMb
  classical
  have hfe := fun s => frame_exists _ Ω Subtype.val_injective E c hc p R (j + k) V (Dc s) σ m j k (i s) (bW s) (bM s)
    finSumFinEquiv (hi s).2.2 (hi s).2.1
  choose g hg using fun s => (hfe s).1
  choose cf cf1 cf2 cf3 using hW
  have hϖ : algebraMap o Ω ((p : o) ^ m) = (p : Ω) ^ m := by simp
  refine ⟨fun s => if h : mseg y s ≠ 0 then
    ((g ⟨s, h⟩).map (fun a => (a : Ω))).submatrix id finSumFinEquiv.symm else 0, fun s hs => ?_,
    fun s t hs ht => ?_⟩
  · simp only [dif_pos hs]
    refine ⟨fun a a' => (g ⟨s, hs⟩ _ _).2, ?_⟩
    obtain ⟨h, r, e⟩ := (hfe ⟨s, hs⟩).2 _ (hg ⟨s, hs⟩)
    refine ⟨h, h.2, r, r.2, ?_⟩
    have := congrArg (chartRing o (mseg y) s).val e
    rw [map_mul, AlgHom.map_det] at this
    rw [hϖ, Matrix.submatrix_map]
    simpa using this
  · simp only [dif_pos hs, dif_pos ht, hϖ]
    haveI := hfr ⟨t, ht⟩
    have hu := div_mem_chartRing (o := o) (mseg y) t s
    have hu0 : mseg y s / mseg y t ≠ 0 := div_ne_zero hs ht
    have hAL : ∀ a ∈ chartRing o (mseg y) s, a ∈ loc _ _ hu := fun a ha =>
      exists_pow_mul_mem_chartRing (mseg y) s t hs ha
    obtain ⟨T, T1, T2, T3⟩ := tri wW (fun a => ∑ a', cf ⟨s, hs⟩ a a' • wW a') (fun a => ∑ a', cf ⟨t, ht⟩ a a' • wW a')
      (fun a => chartMon y s (b (Fin.castAdd k a))) (fun a => chartMon y t (b (Fin.castAdd k a)))
      (fun a => chartMon_ne_zero ht _) (fun a => ⟨_, cf1 _ a, cf2 _ a, rfl⟩) (fun a => ⟨_, cf1 _ a, cf2 _ a, rfl⟩)
    obtain ⟨S, S1, S2, S3⟩ := tri wM (fun a => (bM ⟨s, hs⟩ a : V)) (fun a => (bM ⟨t, ht⟩ a : V))
      (fun a => chartMon y s (b (Fin.natAdd j a))) (fun a => chartMon y t (b (Fin.natAdd j a)))
      (fun a => chartMon_ne_zero ht _) (hMb ⟨s, hs⟩) (hMb ⟨t, ht⟩)
    obtain ⟨X, Z, hU, hZ, e⟩ := overlap (hu := hu) hc hu0 hAL (Dc ⟨s, hs⟩) (Dc ⟨t, ht⟩) hm (hint ⟨t, ht⟩ σ)
      (dd ⟨s, hs⟩) (dd ⟨t, ht⟩) ((hdd _).1.trans (hdd _).1.symm) (hdd _).2 (hρe _ _).1 (hρe _ _).2
      (hM ⟨s, hs⟩ ⟨t, ht⟩ σ) (by rw [inv_div]; exact hM ⟨t, ht⟩ ⟨s, hs⟩ _) (hh ⟨s, hs⟩ ⟨t, ht⟩)
      (hi _).1 (hi _).1 (hi _).2.1 (hg _) (hg _) _ _
      (fun a z => by rw [cf3]; simp) (fun a z => by rw [cf3]; simp) T T3 S S3
    obtain ⟨n, ⟨h1, h2⟩, h3⟩ := (((Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun a' =>
      loc_ev (hU a a')).and (Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun a' =>
      loc_ev (hZ a a'))).and (Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun a' =>
      loc_ev (hAL _ (g ⟨s, hs⟩ a a').2))).exists
    refine ⟨n, (mseg y s / mseg y t) ^ n •
      (Matrix.fromBlocks T X 0 S).submatrix finSumFinEquiv.symm finSumFinEquiv.symm,
      (mseg y s / mseg y t) ^ n • Z.submatrix id finSumFinEquiv.symm, fun a a' => h1 _ _, fun a a' => h2 _ _,
      fun a a' h => ?_, fun a => ?_, fun a a' => h3 _ _, ?_⟩
    · rw [Matrix.smul_apply, Matrix.submatrix_apply]
      refine smul_eq_zero_of_right _ ?_
      induction a using Fin.addCases with
      | left a =>
        induction a' using Fin.addCases with
        | left a' => simpa using T1 a a' h
        | right a' =>
          have : j + (a' : ℕ) < a := h
          omega
      | right a =>
        induction a' using Fin.addCases with
        | left a' => simp
        | right a' => simpa using S1 a a' (by simpa using h)
    · rw [Matrix.smul_apply, Matrix.submatrix_apply, smul_eq_mul]
      congr 1
      induction a using Fin.addCases with
      | left a => simpa using T2 a
      | right a => simpa using S2 a
    · rw [Matrix.mul_smul, smul_comm, ← smul_add, Matrix.submatrix_mul_equiv, e]
      rfl

end PositivityTheory.HtPt.Ge
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.GeoNumNonnegOfRegular
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.Bridge.GeoNum (red red_surjective ker_red comap_map_eq quotEquiv)

namespace PositivityTheory.HtPt.Gf

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem geoNum_nonneg_of_regular (p : ℕ) [Fact p.Prime] {W : Ideal (MRing J)} (hW : IsMultiProjPrime W)
    (hp : (p : MRing J) ∈ W) (hdim : ringKrullDim (MRing J ⧸ W) = ((1 + Fintype.card K : ℕ) : WithBot ℕ∞))
    {f g : MRing J} {bf bg : K → ℕ} {a : K → ℤ} (hf : IsMultiHomog f bf) (hg : IsMultiHomog g bg)
    (ha : ∀ k, (bf k : ℤ) - bg k = a k) (hfW : f ∉ W) (hgW : g ∉ W)
    (hreg : ∀ t : ∀ k, J k, (∀ k, (X ⟨k, t k⟩ : MRing J) ∉ W) → ∃ (n : ℕ) (c : K → ℕ) (v : MRing J),
      ¬ p ∣ n ∧ n * mon t c * f - v * g ∈ W) : 0 ≤ geoNum 1 W (fun _ => a) := by
  classical
  have hC : (MvPolynomial.C (p : ℤ) : MRing J) ∈ W := by
    simpa [map_natCast] using hp
  have hker : RingHom.ker (red (ι := J) p) ≤ W := by
    rw [ker_red]
    exact (Ideal.span_le).2 (by simpa using hC)
  set P := Ideal.map (red (ι := J) p) W with hPdef
  have hcomap : Ideal.comap (red (ι := J) p) P = W := comap_map_eq p hker
  have hWp : W.IsPrime := hW.1
  have hPprime : P.IsPrime := Ideal.map_isPrime_of_surjective (red_surjective p) hker
  have hsupp : ∀ h : MRing J, ∀ b : K → ℕ, IsMultiHomog h b →
      GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog (red (ι := J) p h) b := by
    intro h b hh
    rw [GroundTheory.Heights₂.Heights.Bridge.isMultiHomog_iff]
    intro m hm k
    exact hh m (MvPolynomial.support_map_subset _ _ hm) k
  have hPhom : GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomogIdeal P := by
    rw [GroundTheory.Heights₂.Heights.Bridge.isMultiHomogIdeal_iff]
    obtain ⟨S, hS, rfl⟩ := hW.2.1
    refine ⟨(red (ι := J) p) '' S, ?_, ?_⟩
    · rintro _ ⟨h, hh, rfl⟩
      obtain ⟨b, hb⟩ := hS h hh
      exact ⟨b, (GroundTheory.Heights₂.Heights.Bridge.isMultiHomog_iff _ _).1 (hsupp h b hb)⟩
    · rw [hPdef, Ideal.map_span]
  have hPrel : GroundTheory.Heights₂.Heights.NumbersDVR.IsRelevant P := by
    rw [← GroundTheory.Heights₂.Heights.Bridge.GeoNum.isRelevant_comap_iff p P, hcomap]
    exact hW.2.2
  have hPm : GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiProjPrime P := ⟨hPprime, hPhom, hPrel⟩
  have hdimP : ringKrullDim (GroundTheory.Heights₂.Heights.NumbersDVR.MRing J (ZMod p) ⧸ P) =
      ((1 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    rw [← hdim, ← ringKrullDim_eq_of_ringEquiv (quotEquiv p P), hcomap]
  have hreg' : GroundTheory.Heights₂.Heights.Model.IsRegularSection P a (red (ι := J) p f) (red (ι := J) p g) := by
    refine ⟨⟨bf, bg, hsupp f bf hf, hsupp g bg hg, funext ha⟩, ?_, ?_, ?_⟩
    · intro hm
      exact hfW (by rw [← hcomap]; exact hm)
    · intro hm
      exact hgW (by rw [← hcomap]; exact hm)
    · intro W' hW' hPW'
      set W'' := Ideal.comap (red (ι := J) p) W'
      have hW'pr : W'.IsPrime := hW'.1
      have hW''pr : W''.IsPrime := Ideal.comap_isPrime _ _
      have hWW'' : W ≤ W'' := by
        rw [← hcomap]
        exact Ideal.comap_mono hPW'
      have hrel : IsRelevant W'' :=
        (GroundTheory.Heights₂.Heights.Bridge.GeoNum.isRelevant_comap_iff p W').2 hW'.relevant
      choose t ht using hrel
      obtain ⟨n, c, v, hn, hv⟩ := hreg t (fun k hk => ht k (hWW'' hk))
      refine ⟨red (ι := J) p ((n : MRing J) * mon t c), red (ι := J) p v, ?_, ?_⟩
      · intro hu
        have hu' : ((n : MRing J) * mon t c) ∈ W'' := hu
        rcases hW''pr.mem_or_mem hu' with h1 | h1
        · exact natCast_not_mem hW''pr.ne_top (hWW'' hp) hn h1
        · exact mon_not_mem hW''pr ht c h1
      · have := Ideal.mem_map_of_mem (red (ι := J) p) hv
        simpa [map_sub, map_mul] using this
  have key := GroundTheory.Heights₂.Heights.Model.SectionNef.proof K J (ZMod p) P hPm hdimP a
    (red (ι := J) p f) (red (ι := J) p g) hreg'
  rw [GroundTheory.Heights₂.Heights.Bridge.intNum_map_eq_geoNum p 1 W hW hC hdim] at key
  have hfun : (![a] : Fin 1 → K → ℤ) = fun _ => a := by
    funext i
    fin_cases i
    rfl
  rwa [hfun] at key

end PositivityTheory.HtPt.Gf
end

