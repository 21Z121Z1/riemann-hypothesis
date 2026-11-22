import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ThetaQuasiPeriods.ThetaQuasiPeriodStatement
import ReciprocityTheory.ThetaQuasiPeriods.Transl
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb

-- bundled from Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsEtaleCoordsVanishing
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

noncomputable section

namespace GlobalTheory.HolChart

theorem exists_etale_coords_vanishing {g : ℕ} {A : Type} [CommRing A] (c : ℂ →+* A)
    (hc : c.IsStandardSmoothOfRelativeDimension g) (e : A →+* ℂ) (he : ∀ a, e (c a) = a) :
    ∃ φ : MvPolynomial (Fin g) ℂ →+* A, φ.comp MvPolynomial.C = c ∧ φ.Etale ∧
      ∀ i, e (φ (MvPolynomial.X i)) = 0 := by
  obtain ⟨φ, h1, h2⟩ := hc.exists_etale_mvPolynomial
  let a : Fin g → ℂ := fun i => e (φ (MvPolynomial.X i))
  let T : MvPolynomial (Fin g) ℂ ≃ₐ[ℂ] MvPolynomial (Fin g) ℂ :=
    AlgEquiv.ofAlgHom (MvPolynomial.aeval fun i => MvPolynomial.X i - MvPolynomial.C (a i))
      (MvPolynomial.aeval fun i => MvPolynomial.X i + MvPolynomial.C (a i))
      (by ext i; simp) (by ext i; simp)
  have hC : ∀ x, φ (MvPolynomial.C x) = c x := fun x => by rw [← h1]; rfl
  refine ⟨φ.comp T.toRingEquiv.toRingHom, ?_, ?_, ?_⟩
  · ext x
    simp [T, hC]
  · exact RingHom.Etale.respectsIso.2 φ T.toRingEquiv h2
  · intro i
    simp [T, hC, he, a]

theorem derivation_eq_zero {g : ℕ} {A : Type} [CommRing A] (φ : MvPolynomial (Fin g) ℂ →+* A)
    (hφ : φ.Etale) (e : A →+* ℂ) (D : A →+ ℂ) (h0 : ∀ a, D (φ (MvPolynomial.C a)) = 0)
    (hm : ∀ f f', D (f * f') = e f * D f' + e f' * D f)
    (hX : ∀ i, D (φ (MvPolynomial.X i)) = 0) : D = 0 := by
  have h1 : D 1 = 0 := by simpa using h0 1
  have hP : ∀ p, D (φ p) = 0 := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a => exact h0 a
    | add p q hp hq => rw [map_add, map_add, hp, hq, add_zero]
    | mul_X p i hp => rw [map_mul, hm, hp, hX]; simp
  let F : A →+* DualNumber ℂ :=
    { toFun := fun f => TrivSqZeroExt.inl (e f) + TrivSqZeroExt.inr (D f)
      map_one' := by ext <;> simp [h1]
      map_mul' := fun f f' => by ext <;> simp [hm, mul_comm]
      map_zero' := by ext <;> simp
      map_add' := fun f f' => by ext <;> simp }
  let F₀ : A →+* DualNumber ℂ := (algebraMap ℂ (DualNumber ℂ)).comp e
  have hFF : ∀ p, F (φ p) = F₀ (φ p) := fun p => by
    ext <;> simp [F, F₀, hP, TrivSqZeroExt.algebraMap_eq_inl]
  let _ := φ.toAlgebra
  let _ : Algebra (MvPolynomial (Fin g) ℂ) (DualNumber ℂ) := (F₀.comp φ).toAlgebra
  have _ : Algebra.Etale (MvPolynomial (Fin g) ℂ) A := hφ
  let G : A →ₐ[MvPolynomial (Fin g) ℂ] DualNumber ℂ :=
    { F with commutes' := hFF }
  let G₀ : A →ₐ[MvPolynomial (Fin g) ℂ] DualNumber ℂ := { F₀ with commutes' := fun p => rfl }
  have hnil : IsNilpotent (RingHom.ker (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) := by
    refine ⟨2, ?_⟩
    rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
    intro x hx y hy
    rw [RingHom.mem_ker] at hx hy
    have hx' : x.fst = 0 := hx
    have hy' : y.fst = 0 := hy
    rw [Ideal.mem_bot]
    ext <;> simp [hx', hy']
  have hG : G = G₀ := Algebra.FormallyUnramified.ext' (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom hnil G G₀
    (fun x => by simp [G, G₀, F, F₀])
  ext f
  have := congrArg (fun H : A →ₐ[MvPolynomial (Fin g) ℂ] DualNumber ℂ => (H f).snd) hG
  simpa [G, G₀, F, F₀, TrivSqZeroExt.algebraMap_eq_inl] using this

theorem hol_of_affine
    (hval : (∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a)))
    {g : ℕ} {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {W : Set (Fin g → ℂ)} (hW : IsOpen W)
    (s : (Fin g → ℂ) → (Sp ℂ ⟶ X)) (hs : ∀ w ∈ W, ⊤ ≤ s w ⁻¹ᵁ U)
    (hd : ∀ a : Γ(X, U), DifferentiableOn ℂ (fun w => valAt' (s w) U a) W)
    (V : X.Opens) (f : Γ(X, V)) :
    IsOpen {w | w ∈ W ∧ ⊤ ≤ s w ⁻¹ᵁ V} ∧
      DifferentiableOn ℂ (fun w => valAt' (s w) V f) {w | w ∈ W ∧ ⊤ ≤ s w ⁻¹ᵁ V} := by
  have key : ∀ w₀ ∈ {w | w ∈ W ∧ ⊤ ≤ s w ⁻¹ᵁ V}, {w | w ∈ W ∧ ⊤ ≤ s w ⁻¹ᵁ V} ∈ 𝓝 w₀ ∧
      DifferentiableAt ℂ (fun w => valAt' (s w) V f) w₀ := by
    rintro w₀ ⟨hw₀, hV⟩
    obtain ⟨h, hhV, hh⟩ := hU.exists_basicOpen_le (V := V) ⟨_, ((hval X (s w₀)).1 V).1 hV⟩
      (((hval X (s w₀)).1 U).1 (hs w₀ hw₀))
    have hB₀ : ⊤ ≤ s w₀ ⁻¹ᵁ X.basicOpen h := ((hval X (s w₀)).1 _).2 hh
    have hne₀ : valAt' (s w₀) U h ≠ 0 := ((hval X (s w₀)).2.2.2.2.1 U h).1 hB₀
    have hWn : W ∈ 𝓝 w₀ := hW.mem_nhds hw₀
    have hda : ∀ a : Γ(X, U), DifferentiableAt ℂ (fun w => valAt' (s w) U a) w₀ := fun a =>
      (hd a w₀ hw₀).differentiableAt hWn
    have hN : ∀ᶠ w in 𝓝 w₀, w ∈ W ∧ valAt' (s w) U h ≠ 0 :=
      Filter.Eventually.and hWn ((hda h).continuousAt.eventually_ne hne₀)
    have _ := hU.isLocalization_basicOpen h
    obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj h (resG X hhV f)
    refine ⟨hN.mono fun w hw => ⟨hw.1, ?_⟩, ?_⟩
    · exact ((hval X (s w)).1 V).2
        (hhV (((hval X (s w)).1 _).1 (((hval X (s w)).2.2.2.2.1 U h).2 hw.2)))
    · have hq : DifferentiableAt ℂ (fun w => valAt' (s w) U a * (valAt' (s w) U h ^ n)⁻¹) w₀ :=
        (hda a).mul (((hda h).pow n).inv (pow_ne_zero n hne₀))
      refine DifferentiableAt.congr_of_eventuallyEq hq (hN.mono fun w hw => ?_)
      have hB : ⊤ ≤ s w ⁻¹ᵁ X.basicOpen h := ((hval X (s w)).2.2.2.2.1 U h).2 hw.2
      obtain ⟨ev, hev⟩ := (hval X (s w)).2.1 _ hB
      have r1 := (hval X (s w)).2.2.1 V _ hhV f hB
      have r2 := (hval X (s w)).2.2.1 U _ (X.basicOpen_le h) a hB
      have r3 := (hval X (s w)).2.2.1 U _ (X.basicOpen_le h) h hB
      have ha' : resG X hhV f * resG X (X.basicOpen_le h) h ^ n = resG X (X.basicOpen_le h) a := ha
      have := congrArg ev ha'
      rw [map_mul, map_pow, ← hev, ← hev, ← hev, r1, r2, r3] at this
      show valAt' (s w) V f = valAt' (s w) U a * (valAt' (s w) U h ^ n)⁻¹
      rw [← this, mul_inv_cancel_right₀ (pow_ne_zero n hw.2)]
  exact ⟨isOpen_iff_mem_nhds.2 fun w hw => (key w hw).1,
    fun w hw => (key w hw).2.differentiableWithinAt⟩

theorem exists_holomorphic_chart :
    (∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a)) → (∀ (X : Over (Sp ℂ)) (U : X.left.Opens), IsAffineOpen U → ∀ e : Γ(X.left, U) →+* ℂ, (∀ a, e (constFn X.hom U a) = a) → ∃! x : (𝟙_ (Over (Sp ℂ)) ⟶ X), ⊤ ≤ (x).left ⁻¹ᵁ U ∧ ∀ f, valAt' x.left U f = e f) → (∀ (g : ℕ) (A : Type) [CommRing A] [Algebra ℂ A] [Algebra (MvPolynomial (Fin g) ℂ) A] [IsScalarTower ℂ (MvPolynomial (Fin g) ℂ) A] [Algebra.Etale (MvPolynomial (Fin g) ℂ) A] (e : A →ₐ[ℂ] ℂ), (∀ i, e (algebraMap (MvPolynomial (Fin g) ℂ) A (MvPolynomial.X i)) = 0) → ∃ (W : Set (Fin g → ℂ)) (σ : (Fin g → ℂ) → (A →ₐ[ℂ] ℂ)) (n : ℕ) (f : Fin n → A) (ε : ℝ), IsOpen W ∧ 0 ∈ W ∧ σ 0 = e ∧ 0 < ε ∧ (∀ a, DifferentiableOn ℂ (fun w => σ w a) W) ∧ (∀ w ∈ W, ∀ i, σ w (algebraMap (MvPolynomial (Fin g) ℂ) A (MvPolynomial.X i)) = w i) ∧ ∀ x : A →ₐ[ℂ] ℂ, (∀ k, ‖x (f k) - e (f k)‖ < ε) → ∃ w ∈ W, x = σ w) → (∀ (X : Over (Sp ℂ)) (g : ℕ), SmoothOfRelativeDimension g X.hom → ∀ e : (𝟙_ (Over (Sp ℂ)) ⟶ X), ∃ (W : Set (Fin g → ℂ)) (σ : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ X)) (U : X.left.Opens) (t : Fin g → Γ(X.left, U)), IsOpen W ∧ 0 ∈ W ∧ σ 0 = e ∧ IsAffineOpen U ∧ (∀ (U : (X).left.Opens) (f : Γ((X).left, U)), IsOpen {w | w ∈ W ∧ ⊤ ≤ (σ w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' (σ w).left U f) {w | w ∈ W ∧ ⊤ ≤ (σ w).left ⁻¹ᵁ U}) ∧ (∀ w ∈ W, ⊤ ≤ (σ w).left ⁻¹ᵁ U ∧ ∀ i, valAt' (σ w).left U (t i) = w i) ∧ IsOpen[(TopologicalSpace.generateFrom {S : Set (𝟙_ (Over (Sp ℂ)) ⟶ X) | ∃ (U : X.left.Opens) (f : Γ(X.left, U)) (O : Set ℂ), IsOpen O ∧ S = {x | ⊤ ≤ (x).left ⁻¹ᵁ U ∧ valAt' x.left U f ∈ O}})] (σ '' W) ∧ (∀ D : Γ(X.left, U) →+ ℂ, (∀ a, D (constFn X.hom U a) = 0) → (∀ f f', D (f * f') = valAt' e.left U f * D f' + valAt' e.left U f' * D f) → (∀ i, D (t i) = 0) → D = 0)) := by
  intro hval haff hring X g hX e
  let e' : Sp ℂ ⟶ X.left := e.left
  obtain ⟨U₀, -, U, hU, hp, hle, hsm⟩ :=
    hX.exists_isStandardSmoothOfRelativeDimension (e' (default : PrimeSpectrum ℂ))
  have hU₀ : U₀ = ⊤ := by
    refine eq_top_iff.2 fun y _ => ?_
    have h1 : X.hom (e' (default : PrimeSpectrum ℂ)) ∈ U₀ := hle hp
    have h2 : y = X.hom (e' (default : PrimeSpectrum ℂ)) :=
      Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
    rw [h2]; exact h1
  subst hU₀
  let c : ℂ →+* Γ(X.left, U) :=
    (X.hom.appLE ⊤ U hle).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  have hcc : ∀ a, constFn X.hom U a = c a := fun a => rfl
  have hc : c.IsStandardSmoothOfRelativeDimension g :=
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 (X.hom.appLE ⊤ U hle).hom
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).symm.commRingCatIsoToRingEquiv hsm
  have hpts : ∀ x : 𝟙_ (Over (Sp ℂ)) ⟶ X, ⊤ ≤ x.left ⁻¹ᵁ U →
      ∃ ev : Γ(X.left, U) →+* ℂ, (∀ f, valAt' x.left U f = ev f) ∧ ∀ a, ev (c a) = a := by
    intro x hx
    obtain ⟨ev, hev⟩ := (hval X.left x.left).2.1 U hx
    refine ⟨ev, hev, fun a => ?_⟩
    rw [← hev, ← hcc]
    exact (hval X.left x.left).2.2.2.2.2 X.hom (Over.w x) U a hx
  have heU : ⊤ ≤ e.left ⁻¹ᵁ U := ((hval X.left e').1 U).2 hp
  obtain ⟨ev, hev, hevc⟩ := hpts e heU
  obtain ⟨φ, hφc, hφ, hφ0⟩ := exists_etale_coords_vanishing c hc ev hevc
  have hφc' : ∀ a, φ (MvPolynomial.C a) = c a := fun a => by rw [← hφc]; rfl
  let _ : Algebra ℂ Γ(X.left, U) := c.toAlgebra
  let _ : Algebra (MvPolynomial (Fin g) ℂ) Γ(X.left, U) := φ.toAlgebra
  have _ : IsScalarTower ℂ (MvPolynomial (Fin g) ℂ) Γ(X.left, U) :=
    IsScalarTower.of_algebraMap_eq' hφc.symm
  have _ : Algebra.Etale (MvPolynomial (Fin g) ℂ) Γ(X.left, U) := hφ
  let eA : Γ(X.left, U) →ₐ[ℂ] ℂ := { ev with commutes' := hevc }
  obtain ⟨W, σ, n, f, ε, hW, hW0, hσ0, hε, hσd, hσt, hσs⟩ := hring g Γ(X.left, U) eA hφ0
  have hex : ∀ x : Γ(X.left, U) →ₐ[ℂ] ℂ, ∃! y : (𝟙_ (Over (Sp ℂ)) ⟶ X),
      ⊤ ≤ y.left ⁻¹ᵁ U ∧ ∀ f, valAt' y.left U f = x f := fun x =>
    haff X U hU x.toRingHom (fun a => x.commutes a)
  choose pt hpt hptu using hex
  let W' : Set (Fin g → ℂ) := W ∩ ⋂ k, (W ∩ (fun w => σ w (f k)) ⁻¹' Metric.ball (eA (f k)) ε)
  have hW' : IsOpen W' := hW.inter (isOpen_iInter_of_finite fun k =>
    (hσd (f k)).continuousOn.isOpen_inter_preimage hW Metric.isOpen_ball)
  have hmem : ∀ w, w ∈ W' ↔ w ∈ W ∧ ∀ k, ‖σ w (f k) - eA (f k)‖ < ε := by
    intro w
    simp only [W', Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, Metric.mem_ball, dist_eq_norm]
    exact ⟨fun h => ⟨h.1, fun k => (h.2 k).2⟩, fun h => ⟨h.1, fun k => ⟨h.1, h.2 k⟩⟩⟩
  refine ⟨W', fun w => pt (σ w), U, fun i => φ (MvPolynomial.X i), hW', ?_, ?_, hU, ?_, ?_, ?_, ?_⟩
  · exact (hmem 0).2 ⟨hW0, fun k => by rw [hσ0, sub_self, norm_zero]; exact hε⟩
  · show pt (σ 0) = e
    rw [hσ0]
    exact (hptu eA e ⟨heU, hev⟩).symm
  · intro V a
    refine hol_of_affine hval hU hW' (fun w => (pt (σ w)).left) (fun w _ => (hpt (σ w)).1)
      (fun b => ?_) V a
    exact ((hσd b).mono Set.inter_subset_left).congr fun w _ => (hpt (σ w)).2 b
  · intro w hw
    exact ⟨(hpt (σ w)).1, fun i => ((hpt (σ w)).2 _).trans (hσt w hw.1 i)⟩
  · have himg : (fun w => pt (σ w)) '' W' =
        {x : 𝟙_ (Over (Sp ℂ)) ⟶ X | ⊤ ≤ x.left ⁻¹ᵁ U ∧ valAt' x.left U 0 ∈ (Set.univ : Set ℂ)} ∩
          ⋂ k, {x : 𝟙_ (Over (Sp ℂ)) ⟶ X | ⊤ ≤ x.left ⁻¹ᵁ U ∧
            valAt' x.left U (f k) ∈ Metric.ball (eA (f k)) ε} := by
      ext x
      simp only [Set.mem_image, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq, Set.mem_univ,
        and_true, Metric.mem_ball, dist_eq_norm]
      constructor
      · rintro ⟨w, hw, rfl⟩
        refine ⟨(hpt (σ w)).1, fun k => ⟨(hpt (σ w)).1, ?_⟩⟩
        rw [(hpt (σ w)).2]
        exact ((hmem w).1 hw).2 k
      · rintro ⟨hx, hk⟩
        obtain ⟨ex, hex, hexc⟩ := hpts x hx
        let xA : Γ(X.left, U) →ₐ[ℂ] ℂ := { ex with commutes' := hexc }
        have hk' : ∀ k, ‖xA (f k) - eA (f k)‖ < ε := fun k => by
          have := (hk k).2
          rw [hex] at this
          exact this
        obtain ⟨w, hw, hxw⟩ := hσs xA hk'
        refine ⟨w, (hmem w).2 ⟨hw, hxw ▸ hk'⟩, ?_⟩
        rw [← hxw]
        exact (hptu xA x ⟨hx, hex⟩).symm
    rw [himg]
    let _ := TopologicalSpace.generateFrom {S : Set (𝟙_ (Over (Sp ℂ)) ⟶ X) |
      ∃ (U : X.left.Opens) (f : Γ(X.left, U)) (O : Set ℂ), IsOpen O ∧
        S = {x | ⊤ ≤ (x).left ⁻¹ᵁ U ∧ valAt' x.left U f ∈ O}}
    refine IsOpen.inter ?_ (isOpen_iInter_of_finite fun k => ?_)
    · exact TopologicalSpace.isOpen_generateFrom_of_mem ⟨U, 0, Set.univ, isOpen_univ, rfl⟩
    · exact TopologicalSpace.isOpen_generateFrom_of_mem ⟨U, f k, _, Metric.isOpen_ball, rfl⟩
  · intro D h0 hm hX
    refine derivation_eq_zero φ hφ ev D (fun a => ?_) (fun a b => ?_) hX
    · rw [hφc', ← hcc]; exact h0 a
    · rw [← hev, ← hev]; exact hm a b

end GlobalTheory.HolChart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsIsGenTranslDiffComp
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem exists_isGen_linComb_of_pull {X Y Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (f : Z ⟶ Y) (c : LB.Gen ((LB.LinComb L φ ε).pull f))
    (hc : c.IsGen) : ∃ d : LB.Gen (LB.LinComb L (fun k => f ≫ φ k) ε), d.IsGen := by
  have hle : ∀ j : K → L.ι, LB.wchart L (fun k => f ≫ φ k) j ≤
      LB.wchart (LB.LinComb L φ ε) (K := PUnit) (fun _ => f) (fun _ => j) :=
    fun j _ hy => Set.mem_iInter.2 fun _ => LB.wchart_comp_le L f φ j hy
  refine ⟨⟨fun j => res (hle j) (LB.ts c (fun _ => j))⟩, ?_⟩
  refine (LB.isGen_iff L _).2 fun i j => ?_
  have key := congrArg (res (inf_le_inf (hle i) (hle j)))
    ((LB.isGen_iff (LB.LinComb L φ ε) c).1 hc (fun _ => i) (fun _ => j))
  have e := LB.lcg_pull (LB.LinComb L φ ε) f (fun _ => i) (fun _ => j)
  rw [LB.lcg_comp]
  refine (LB.res_res _ _ _).trans (((LB.res_res _ _ _).symm.trans key).trans
    ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ ?_)))
  · exact (congrArg _ e).trans (LB.res_res _ _ _)
  · exact (LB.res_res _ _ _).trans (LB.res_res _ _ _).symm

theorem exists_isGen_translDiff_comp {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left)
    {T T' : Over S} (x : T ⟶ A) (g : T' ⟶ T) (V : T.left.Opens)
    (hg : ∀ q, g.left q ∈ V)
    (c : LB.Gen ((Out.translDiff A L x).pull ((fst T A).left ⁻¹ᵁ V).ι)) (hc : c.IsGen) :
    ∃ d : LB.Gen (Out.translDiff A L (g ≫ x)), d.IsGen := by
  obtain ⟨d, hd⟩ := exists_isGen_linComb_of_pull L _ _ _ c hc
  have hr : Set.range (g ▷ A).left ⊆ Set.range ((fst T A).left ⁻¹ᵁ V).ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    change ((g ▷ A).left ≫ (fst T A).left) y ∈ V
    rw [← Over.comp_left, whiskerRight_fst, Over.comp_left]
    exact hg _
  have hl := IsOpenImmersion.lift_fac ((fst T A).left ⁻¹ᵁ V).ι (g ▷ A).left hr
  have h4 : ∃ w : LB.Gen (LB.LinComb L _ _), w.IsGen :=
    ⟨_, LB.isGen_pullGen L _ _ d hd (IsOpenImmersion.lift ((fst T A).left ⁻¹ᵁ V).ι (g ▷ A).left hr)⟩
  have h3 : (fun k : Fin 2 => IsOpenImmersion.lift ((fst T A).left ⁻¹ᵁ V).ι (g ▷ A).left hr ≫
      ((fst T A).left ⁻¹ᵁ V).ι ≫
        ![(lift (fst T A ≫ x) (snd T A) ≫ μ[A]).left, (snd T A).left] k) =
      ![(lift (fst T' A ≫ g ≫ x) (snd T' A) ≫ μ[A]).left, (snd T' A).left] := by
    funext k
    rw [← Category.assoc, hl]
    fin_cases k
    · change (g ▷ A ≫ lift (fst T A ≫ x) (snd T A) ≫ μ[A]).left =
        (lift (fst T' A ≫ g ≫ x) (snd T' A) ≫ μ[A]).left
      rw [comp_lift_assoc, whiskerRight_fst_assoc, whiskerRight_snd]
    · change (g ▷ A ≫ snd T A).left = (snd T' A).left
      rw [whiskerRight_snd]
  rw [h3] at h4
  exact h4

theorem kTriv_of_global : ∀ (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left), IsAbelianScheme A → L.IsLB →
    (∀ (R : Type) [CommRing R] [Algebra ℂ R], ∀ (x : Over.mk (spMap (algebraMap ℂ R)) ⟶ A),
      (∃ c : LB.Gen (Out.translDiff A L x), c.IsGen) → x = 1) → Out.KTriv A L := by
  intro A _ L _ _ H R _ t x hx
  have H' : ∀ (R' : CommRingCat.{0}) (t' : Spec R' ⟶ Sp ℂ) (y : Over.mk t' ⟶ A),
      (∃ c : LB.Gen (Out.translDiff A L y), c.IsGen) → y = 1 := by
    intro R' t'
    obtain ⟨φ, rfl⟩ := Spec.map_surjective t'
    let _ : Algebra ℂ R' := φ.hom.toAlgebra
    exact H R'
  change x = 1
  apply Over.OverMorphism.ext
  refine Scheme.hom_ext_of_forall _ _ fun p => ?_
  obtain ⟨V, hp, c, hc⟩ := hx p
  obtain ⟨U, hU, hpU, hUV⟩ := exists_isAffineOpen_mem_and_subset (U := V) (x := p) hp
  refine ⟨U, hpU, ?_⟩
  let g : Over.mk (hU.fromSpec ≫ t) ⟶ Over.mk t := Over.homMk hU.fromSpec rfl
  have h1 : g ≫ x = g ≫ 1 := by
    rw [MonObj.comp_one]
    exact H' _ _ _ (exists_isGen_translDiff_comp A L x g V
      (fun q => hUV (hU.range_fromSpec.le ⟨q, rfl⟩)) c hc)
  have h2 : hU.fromSpec ≫ x.left = hU.fromSpec ≫ (1 : Over.mk t ⟶ A).left :=
    congrArg (·.left) h1
  rw [IsAffineOpen.fromSpec, Category.assoc, Category.assoc, cancel_epi] at h2
  exact h2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsIsHomogeneousEvalOfMulMemSpan
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

namespace GlobalTheory

private theorem isWeightedHomogeneous_coeff_mul_rw1 {X ρ : Type} (b : ρ → X → ℂ) {k l : ℕ} {f g : X → ℂ}
    (hf : ∃ G : MvPolynomial ρ ℂ, G.IsHomogeneous k ∧
      ∀ z, f z = MvPolynomial.eval (fun c => b c z) G)
    (hg : ∃ G : MvPolynomial ρ ℂ, G.IsHomogeneous l ∧
      ∀ z, g z = MvPolynomial.eval (fun c => b c z) G) :
    ∃ G : MvPolynomial ρ ℂ, G.IsHomogeneous (k + l) ∧
      ∀ z, f z * g z = MvPolynomial.eval (fun c => b c z) G := by
  obtain ⟨G, hG, hfG⟩ := hf
  obtain ⟨H, hH, hgH⟩ := hg
  exact ⟨G * H, hG.mul hH, fun z => by rw [hfG, hgH, map_mul]⟩

private theorem exists_homogeneous_one_eval_of_mem_span {X ρ : Type} (b : ρ → X → ℂ) {f : X → ℂ}
    (hf : f ∈ Submodule.span ℂ (Set.range b)) :
    ∃ G : MvPolynomial ρ ℂ, G.IsHomogeneous 1 ∧
      ∀ z, f z = MvPolynomial.eval (fun c => b c z) G := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X (R := ℂ) i, fun z => by simp⟩
  | zero => exact ⟨0, MvPolynomial.isHomogeneous_zero _ _ _, fun z => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨G, hG, hxG⟩ := hx
    obtain ⟨H, hH, hyH⟩ := hy
    exact ⟨G + H, hG.add hH, fun z => by simp [hxG, hyH]⟩
  | smul c x _ hx =>
    obtain ⟨G, hG, hxG⟩ := hx
    have hCG := (MvPolynomial.isHomogeneous_C (σ := ρ) c).mul hG
    rw [zero_add] at hCG
    exact ⟨MvPolynomial.C c * G, hCG, fun z => by simp [hxG]⟩

private theorem exists_homogeneous_eval_of_even_degree_monomial {X σ ρ : Type} (a : σ → X → ℂ) (b : ρ → X → ℂ)
    (hab : ∀ i j, a i * a j ∈ Submodule.span ℂ (Set.range b)) :
    ∀ (k : ℕ) (m : σ →₀ ℕ), m.degree = 2 * k →
      ∃ G : MvPolynomial ρ ℂ, G.IsHomogeneous k ∧
        ∀ z, (m.prod fun c e => a c z ^ e) = MvPolynomial.eval (fun c => b c z) G := by
  intro k
  induction k with
  | zero =>
    intro m hm
    rw [mul_zero, Finsupp.degree_eq_zero_iff] at hm
    subst hm
    exact ⟨1, MvPolynomial.isHomogeneous_one _ _, fun z => by simp⟩
  | succ k ih =>
    intro m hm
    classical
    obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
      by_contra h
      push Not at h
      have h0 : m = 0 := by ext x; exact h x
      rw [h0, map_zero] at hm
      omega
    have hle₁ : Finsupp.single i 1 ≤ m := by
      rw [Finsupp.single_le_iff]; omega
    obtain ⟨m₁, rfl⟩ : ∃ m₁, m = m₁ + Finsupp.single i 1 :=
      ⟨_, (tsub_add_cancel_of_le hle₁).symm⟩
    rw [map_add, Finsupp.degree_single] at hm
    obtain ⟨j, hj⟩ : ∃ j, m₁ j ≠ 0 := by
      by_contra h
      push Not at h
      have h0 : m₁ = 0 := by ext x; exact h x
      rw [h0, map_zero] at hm
      omega
    have hle₂ : Finsupp.single j 1 ≤ m₁ := by
      rw [Finsupp.single_le_iff]; omega
    obtain ⟨m₂, rfl⟩ : ∃ m₂, m₁ = m₂ + Finsupp.single j 1 :=
      ⟨_, (tsub_add_cancel_of_le hle₂).symm⟩
    rw [map_add, Finsupp.degree_single] at hm
    have hdeg : m₂.degree = 2 * k := by omega
    obtain ⟨G, hG, hGz⟩ := isWeightedHomogeneous_coeff_mul_rw1 b (ih m₂ hdeg) (exists_homogeneous_one_eval_of_mem_span b (hab j i))
    refine ⟨G, hG, fun z => ?_⟩
    rw [← hGz z, Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
      Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
    simp only [Finsupp.prod_single_index, pow_zero, pow_one, Pi.mul_apply]
    ring

theorem exists_isHomogeneous_eval_of_mul_mem_span {X σ ρ : Type} (a : σ → X → ℂ) (b : ρ → X → ℂ)
    (hab : ∀ i j, a i * a j ∈ Submodule.span ℂ (Set.range b)) (d : ℕ) (F : MvPolynomial σ ℂ)
    (hF : F.IsHomogeneous (2 * d)) :
    ∃ G : MvPolynomial ρ ℂ, G.IsHomogeneous d ∧
      ∀ z, MvPolynomial.eval (fun c => a c z) F = MvPolynomial.eval (fun c => b c z) G := by
  classical
  have hP : ∀ s : Finset (σ →₀ ℕ), s ⊆ F.support → ∃ G : MvPolynomial ρ ℂ, G.IsHomogeneous d ∧
      ∀ z, (∑ m ∈ s, F.coeff m * m.prod fun c e => a c z ^ e) =
        MvPolynomial.eval (fun c => b c z) G := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact fun _ => ⟨0, MvPolynomial.isHomogeneous_zero _ _ _, fun z => by simp⟩
    | insert m s hms ih =>
      intro hsub
      obtain ⟨G, hG, hGz⟩ := ih (fun x hx => hsub (Finset.mem_insert_of_mem hx))
      have hm : m.degree = 2 * d := by
        rw [Finsupp.degree_eq_weight_one]
        exact hF (MvPolynomial.mem_support_iff.mp (hsub (Finset.mem_insert_self m s)))
      obtain ⟨H, hH, hHz⟩ := exists_homogeneous_eval_of_even_degree_monomial a b hab d m hm
      have hCH := (MvPolynomial.isHomogeneous_C (σ := ρ) (F.coeff m)).mul hH
      rw [zero_add] at hCH
      refine ⟨MvPolynomial.C (F.coeff m) * H + G, hCH.add hG, fun z => ?_⟩
      rw [Finset.sum_insert hms, hGz z, hHz z]
      simp
  obtain ⟨G, hG, hGz⟩ := hP F.support subset_rfl
  exact ⟨G, hG, fun z => by rw [MvPolynomial.eval_eq, ← hGz z]; rfl⟩

theorem theta_projectiveNormality_even :
    (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 1 ≤ N → (∀ c : Fin g → Fin N, (Differentiable ℂ (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) ∧ ∀ (n n' : Fin g → ℤ) z, (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) z)) ∧ LinearIndependent ℂ (fun (c : Fin g → Fin N) (z : Fin g → ℂ) => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ))) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 1 ≤ N → ∀ f : (Fin g → ℂ) → ℂ, (Differentiable ℂ f ∧ ∀ (n n' : Fin g → ℤ) z, f (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f z) → f ∈ Submodule.span ℂ (Set.range (fun (c : Fin g → Fin N) (z : Fin g → ℂ) => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)))) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∃ N : ℕ, 3 ≤ N ∧ ∀ (d : ℕ) (f : (Fin g → ℂ) → ℂ), (Differentiable ℂ f ∧ ∀ (n n' : Fin g → ℤ) z, f (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-((N * d : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f z) → ∃ F : MvPolynomial (Fin g → Fin N) ℂ, F.IsHomogeneous d ∧ ∀ z, f z = MvPolynomial.eval (fun c => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) F) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∃ N : ℕ, 3 ≤ N ∧ Even N ∧ (∀ (d : ℕ) (f : (Fin g → ℂ) → ℂ), (Differentiable ℂ f ∧ ∀ (n n' : Fin g → ℤ) z, f (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-((N * d : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f z) → ∃ F : MvPolynomial (Fin g → Fin N) ℂ, F.IsHomogeneous d ∧ ∀ z, f z = MvPolynomial.eval (fun c => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) F)) := by
  intro hA hB hC g τ hτ
  obtain ⟨N, hN3, hNC⟩ := hC g τ hτ
  refine ⟨2 * N, by omega, even_two_mul N, fun d f hf => ?_⟩
  obtain ⟨F, hF, hFz⟩ := hNC (2 * d) f
    ⟨hf.1, fun n n' z => by rw [show N * (2 * d) = 2 * N * d by ring]; exact hf.2 n n' z⟩
  have hA' := (hA g τ hτ N (by omega)).1
  have hab : ∀ i j : Fin g → Fin N,
      (fun z : Fin g → ℂ => theta (fun k => ((i k : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) *
        (fun z : Fin g → ℂ => theta (fun k => ((j k : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) ∈
      Submodule.span ℂ (Set.range (fun (c : Fin g → Fin (2 * N)) (z : Fin g → ℂ) =>
        theta (fun k => ((c k : ℕ) : ℝ) / ((2 * N : ℕ) : ℝ)) 0
          (((2 * N : ℕ) : ℂ) • z) (((2 * N : ℕ) : ℂ) • τ))) := by
    intro i j
    refine hB g τ hτ (2 * N) (by omega) _ ⟨(hA' i).1.mul (hA' j).1, fun n n' z => ?_⟩
    have h1 := (hA' i).2 n n' z
    have h2 := (hA' j).2 n n' z
    beta_reduce at h1 h2 ⊢
    rw [Pi.mul_apply, Pi.mul_apply, h1, h2,
      show ∀ x : ℂ, eC (-((2 * N : ℕ) : ℂ) * x) = eC (-(N : ℂ) * x) * eC (-(N : ℂ) * x) from
        fun x => by unfold eC; rw [← Complex.exp_add]; congr 1; push_cast; ring]
    ring
  obtain ⟨G, hG, hGz⟩ := exists_isHomogeneous_eval_of_mul_mem_span
    (fun (c : Fin g → Fin N) (z : Fin g → ℂ) =>
      theta (fun k => ((c k : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ))
    (fun (c : Fin g → Fin (2 * N)) (z : Fin g → ℂ) =>
      theta (fun k => ((c k : ℕ) : ℝ) / ((2 * N : ℕ) : ℝ)) 0
        (((2 * N : ℕ) : ℂ) • z) (((2 * N : ℕ) : ℂ) • τ))
    hab d F hF
  exact ⟨G, hG, fun z => (hFz z).trans (hGz z)⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsAHOfPolarisation
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

namespace GlobalTheory

def thetaZeroSec {X : Scheme.{0}} (L : LB X) : L.Sec where
  f _ := 0
  compat := by intros; simp

theorem valAt'_zero_fn {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (U : X.Opens) : valAt' x U 0 = 0 := by
  unfold valAt'
  split_ifs with h
  · simp [valAt]
  · rfl

theorem isAH_of_polarisation :
    (∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a)) → (∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → ∀ (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : Λ → ℂ) (Ef : LinearMap.BilinForm ℤ Λ) (θ : (Fin g → ℂ) → ℂ), Hm.IsHermitian → (∀ l, ‖χ l‖ = 1) → (∀ l m : Λ, (Ef l m : ℝ) = ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ))).im) → Function.Injective Ef → Differentiable ℂ θ → θ ≠ 0 → (∀ (l : Λ) z, θ (z + l) = (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) + Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))))) * θ z) → ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) → (∀ (P : Out.PolAV (Sp ℂ)) (n : ℕ), 1 ≤ n → ∃ s : Fin (n ^ P.g) → (lbPow P.L n).Sec, ∀ a : Fin (n ^ P.g) → ℂ, (∀ j, ∑ i, constFn P.A.hom _ (a i) * (s i).f j = 0) → a = 0) → (∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (Ef : LinearMap.BilinForm ℤ u.Λ), (Hm.IsHermitian ∧ (∀ l, ‖χ l‖ = 1) ∧ (∀ l m : u.Λ, (Ef l m : ℝ) = ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin P.g → ℂ))).im) ∧ ∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i → u.fr i z = (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))) + Real.pi / 2 * ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))))) * u.fr i (z + l)) → ∀ n : ℕ, (∀ s, ∃! θ, u.IsThetaFn Hm χ n θ ∧ u.IsFnPow n s θ) ∧ ∀ θ s s', u.IsFnPow n s θ → u.IsFnPow n s' θ → s = s') → (∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (Ef : LinearMap.BilinForm ℤ u.Λ), (Hm.IsHermitian ∧ (∀ l, ‖χ l‖ = 1) ∧ (∀ l m : u.Λ, (Ef l m : ℝ) = ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin P.g → ℂ))).im) ∧ ∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i → u.fr i z = (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))) + Real.pi / 2 * ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))))) * u.fr i (z + l)) → Function.Bijective Ef → u.IsAH Hm χ) := by
  intro _ hpos hsec hthe P u Hm χ Ef hAH hbij
  obtain ⟨hH, hχ, hE, hfr⟩ := hAH
  refine ⟨hH, ?_, hχ, hfr⟩

  obtain ⟨s, hs⟩ := hsec P 1 le_rfl
  have hone : ∀ i j : Fin (1 ^ P.g), i = j := fun i j =>
    Fin.ext (by
      have hi : (i : ℕ) < 1 := lt_of_lt_of_eq i.isLt (one_pow _)
      have hj : (j : ℕ) < 1 := lt_of_lt_of_eq j.isLt (one_pow _)
      omega)
  let i0 : Fin (1 ^ P.g) := ⟨0, by rw [one_pow]; exact Nat.one_pos⟩
  have hcorr := hthe P u Hm χ Ef ⟨hH, hχ, hE, hfr⟩ 1
  obtain ⟨θ, ⟨hθ, hfn⟩, -⟩ := hcorr.1 (s i0)

  have hθne : θ ≠ 0 := by
    rintro rfl
    have hz : u.IsFnPow 1 (thetaZeroSec (lbPow P.L 1)) 0 := by
      intro j z _
      rw [Pi.zero_apply, zero_mul]
      exact valAt'_zero_fn _ _
    have hs0 : s i0 = thetaZeroSec (lbPow P.L 1) := hcorr.2 0 _ _ hfn hz
    have hall : ∀ i, s i = thetaZeroSec (lbPow P.L 1) := fun i => by rw [hone i i0, hs0]
    have h1 := hs (fun _ => 1) (fun j => Finset.sum_eq_zero (fun i _ => by rw [hall i]; exact mul_zero _))
    exact absurd (congrFun h1 i0) (by simp)

  exact hpos P.g u.Λ u.discrete u.full Hm χ Ef θ hH hχ hE hbij.1 hθ.1 hθne
    (fun l z => by have h := hθ.2 l z; rw [pow_one] at h; exact h)

end GlobalTheory
end
end

