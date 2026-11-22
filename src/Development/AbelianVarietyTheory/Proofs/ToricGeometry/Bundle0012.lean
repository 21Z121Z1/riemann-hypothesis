import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed

-- bundled from Development.AbelianVarietyTheory.Proofs.ToricGeometry.CompactSpacePointsPolAV
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

noncomputable section

namespace GlobalTheory.PointsCompact

abbrev ValueRules : Prop :=
  ∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a)

abbrev AffinePoints : Prop :=
  ∀ (X : Over (Sp ℂ)) (U : X.left.Opens), IsAffineOpen U → ∀ e : Γ(X.left, U) →+* ℂ, (∀ a, e (constFn X.hom U a) = a) → ∃! x : (𝟙_ (Over (Sp ℂ)) ⟶ X), ⊤ ≤ (x).left ⁻¹ᵁ U ∧ ∀ f, valAt' x.left U f = e f

abbrev pointTopology (X : Over (Sp ℂ)) : TopologicalSpace (𝟙_ (Over (Sp ℂ)) ⟶ X) :=
  TopologicalSpace.generateFrom {S : Set (𝟙_ (Over (Sp ℂ)) ⟶ X) | ∃ (U : X.left.Opens) (f : Γ(X.left, U)) (O : Set ℂ), IsOpen O ∧ S = {x | ⊤ ≤ (x).left ⁻¹ᵁ U ∧ valAt' x.left U f ∈ O}}

theorem continuous_of_affine (h1 : ValueRules) (X : Over (Sp ℂ)) (U : X.left.Opens)
    (hU : IsAffineOpen U) {Z : Type} [TopologicalSpace Z] (σ : Z → (𝟙_ (Over (Sp ℂ)) ⟶ X))
    (hσ : ∀ w, ⊤ ≤ (σ w).left ⁻¹ᵁ U)
    (hc : ∀ f : Γ(X.left, U), Continuous fun w => valAt' (σ w).left U f) :
    @Continuous _ _ _ (pointTopology X) σ := by
  refine continuous_generateFrom_iff.2 ?_
  rintro S ⟨V, f, O, hO, rfl⟩
  rw [isOpen_iff_mem_nhds]
  rintro w ⟨hwV, hwO⟩
  have hpU : (σ w).left (default : PrimeSpectrum ℂ) ∈ U := ((h1 _ (σ w).left).1 U).1 (hσ w)
  have hpV : (σ w).left (default : PrimeSpectrum ℂ) ∈ V := ((h1 _ (σ w).left).1 V).1 hwV
  obtain ⟨g, hgV, hpg⟩ := hU.exists_basicOpen_le ⟨_, hpV⟩ hpU
  letI := (X.left.presheaf.map (homOfLE <| X.left.basicOpen_le g).op).hom.toAlgebra
  haveI := hU.isLocalization_basicOpen g
  obtain ⟨⟨a, _, ⟨n, rfl⟩⟩, ha⟩ := IsLocalization.surj (Submonoid.powers g) (resG X.left hgV f)
  simp only [RingHom.algebraMap_toAlgebra] at ha

  have key : ∀ q : Sp ℂ ⟶ X.left, ⊤ ≤ q ⁻¹ᵁ X.left.basicOpen g →
      valAt' q V f * valAt' q U g ^ n = valAt' q U a := by
    intro q hq
    have hqU : ⊤ ≤ q ⁻¹ᵁ U := ((h1 _ q).1 U).2 (X.left.basicOpen_le g (((h1 _ q).1 _).1 hq))
    obtain ⟨e, he⟩ := (h1 _ q).2.1 _ hq
    obtain ⟨e', he'⟩ := (h1 _ q).2.1 _ hqU
    have := congrArg e ha
    rw [map_mul] at this
    rw [← (h1 _ q).2.2.1 V _ hgV f hq, ← (h1 _ q).2.2.1 U _ (X.left.basicOpen_le g) a hq,
      he, he, he', ← map_pow, ← he', ← (h1 _ q).2.2.1 U _ (X.left.basicOpen_le g) _ hq, he]
    simpa using this
  set F : Z → ℂ := fun w => valAt' (σ w).left U a / valAt' (σ w).left U g ^ n with hF
  have hopen : IsOpen {w | valAt' (σ w).left U g ≠ 0} := isOpen_ne_fun (hc g) continuous_const
  have hFc : ContinuousOn F {w | valAt' (σ w).left U g ≠ 0} :=
    (hc a).continuousOn.div ((hc g).pow n).continuousOn (fun w hw => pow_ne_zero _ hw)
  refine Filter.mem_of_superset ((hFc.isOpen_inter_preimage hopen hO).mem_nhds ?_) ?_
  · have hq : ⊤ ≤ (σ w).left ⁻¹ᵁ X.left.basicOpen g := ((h1 _ (σ w).left).1 _).2 hpg
    have hne : valAt' (σ w).left U g ≠ 0 := ((h1 _ (σ w).left).2.2.2.2.1 U g).1 hq
    refine ⟨hne, ?_⟩
    show valAt' (σ w).left U a / valAt' (σ w).left U g ^ n ∈ O
    rw [← key _ hq, mul_div_cancel_right₀ _ (pow_ne_zero _ hne)]
    exact hwO
  · rintro w' ⟨hne, hw'⟩
    have hq : ⊤ ≤ (σ w').left ⁻¹ᵁ X.left.basicOpen g := ((h1 _ (σ w').left).2.2.2.2.1 U g).2 hne
    refine ⟨((h1 _ (σ w').left).1 V).2 (hgV (((h1 _ (σ w').left).1 _).1 hq)), ?_⟩
    have h' : valAt' (σ w').left U a / valAt' (σ w').left U g ^ n ∈ O := hw'
    rwa [← key _ hq, mul_div_cancel_right₀ _ (pow_ne_zero _ hne)] at h'

theorem exists_compact_of_affine (h1 : ValueRules) (h2 : AffinePoints) (X : Over (Sp ℂ))
    (U : X.left.Opens) (hU : IsAffineOpen U) {n : ℕ} (r : Fin n → Γ(X.left, U))
    (c : ℂ →+* Γ(X.left, U)) (hc : ∀ a, c a = constFn X.hom U a)
    (hs : Function.Surjective (MvPolynomial.eval₂Hom c r)) :
    ∃ C : Set (𝟙_ (Over (Sp ℂ)) ⟶ X), @IsCompact _ (pointTopology X) C ∧
      ∀ x : 𝟙_ (Over (Sp ℂ)) ⟶ X, ⊤ ≤ x.left ⁻¹ᵁ U → (∀ j, ‖valAt' x.left U (r j)‖ ≤ 1) → x ∈ C := by
  letI := pointTopology X
  have hXw : ∀ x : 𝟙_ (Over (Sp ℂ)) ⟶ X, x.left ≫ X.hom = 𝟙 _ := fun x => by
    simpa using Over.w x
  set K : Set (Fin n → ℂ) := {z | (∀ j, ‖z j‖ ≤ 1) ∧
    ∀ p ∈ RingHom.ker (MvPolynomial.eval₂Hom c r), MvPolynomial.eval z p = 0} with hK
  have hKc : IsCompact K := by
    refine (isCompact_closedBall (0 : Fin n → ℂ) 1).of_isClosed_subset ?_ ?_
    · have hKe : K = (⋂ j, {z : Fin n → ℂ | ‖z j‖ ≤ 1}) ∩
          ⋂ p ∈ RingHom.ker (MvPolynomial.eval₂Hom c r), {z | MvPolynomial.eval z p = 0} := by
        ext z
        simp [hK]
      rw [hKe]
      refine IsClosed.inter (isClosed_iInter fun j => ?_) (isClosed_biInter fun p _ => ?_)
      · exact isClosed_le (continuous_norm.comp (continuous_apply j)) continuous_const
      · exact isClosed_eq (MvPolynomial.continuous_eval p) continuous_const
    · intro z hz
      rw [Metric.mem_closedBall, dist_zero_right]
      exact (pi_norm_le_iff_of_nonneg zero_le_one).2 hz.1
  let e : K → (Γ(X.left, U) →+* ℂ) := fun z =>
    (MvPolynomial.eval₂Hom c r).liftOfSurjective hs ⟨MvPolynomial.eval z.1, fun p hp => z.2.2 p hp⟩
  have he : ∀ z : K, ∀ p, e z (MvPolynomial.eval₂Hom c r p) = MvPolynomial.eval z.1 p := fun z p =>
    RingHom.liftOfRightInverse_comp_apply _ _ _ _ _
  have hconst : ∀ z : K, ∀ a, e z (constFn X.hom U a) = a := fun z a => by
    rw [← hc, ← MvPolynomial.eval₂Hom_C c r a, he]
    simp
  have hex := fun z : K => (h2 X U hU (e z) (hconst z))
  choose σ hσ hσu using hex
  have hσc : Continuous σ := continuous_of_affine h1 X U hU σ (fun z => (hσ z).1) (fun f => by
    obtain ⟨p, rfl⟩ := hs f
    refine ((MvPolynomial.continuous_eval p).comp continuous_subtype_val).congr fun z => ?_
    rw [(hσ z).2, he]
    rfl)
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hKc
  refine ⟨Set.range σ, isCompact_range hσc, fun x hx hle => ?_⟩
  obtain ⟨ex, hex⟩ := (h1 _ x.left).2.1 U hx
  have hcomp : ex.comp (MvPolynomial.eval₂Hom c r) = MvPolynomial.eval (fun j => valAt' x.left U (r j)) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun j => ?_)
    · simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C, MvPolynomial.eval_C]
      rw [← hex, hc]
      exact (h1 _ x.left).2.2.2.2.2 X.hom (hXw x) U a hx
    · simp [hex]
  have hz : (fun j => valAt' x.left U (r j)) ∈ K := by
    refine ⟨hle, fun p hp => ?_⟩
    rw [← hcomp, RingHom.comp_apply, RingHom.mem_ker.1 hp, map_zero]
  refine ⟨⟨_, hz⟩, ?_⟩
  refine (hσu ⟨_, hz⟩ x ⟨hx, fun f => ?_⟩).symm
  obtain ⟨p, rfl⟩ := hs f
  rw [he, ← hcomp, RingHom.comp_apply, hex]

theorem continuous_comp (h1 : ValueRules) {X Y : Over (Sp ℂ)} (φ : X ⟶ Y) :
    @Continuous _ _ (pointTopology X) (pointTopology Y) (fun x => x ≫ φ) := by
  letI := pointTopology X
  refine continuous_generateFrom_iff.2 ?_
  rintro S ⟨U, f, O, hO, rfl⟩
  apply TopologicalSpace.isOpen_generateFrom_of_mem
  refine ⟨φ.left ⁻¹ᵁ U, (φ.left.app U).hom f, O, hO, ?_⟩
  ext x
  simp only [Set.mem_preimage, Set.mem_setOf_eq, Over.comp_left]
  rw [(h1 _ x.left).2.2.2.1 _ φ.left U f]
  exact Iff.rfl

theorem compact_of_sections (h1 : ValueRules) (h2 : AffinePoints) (X : Over (Sp ℂ))
    (L : LB X.left) {M : ℕ} (s : Fin (M + 1) → LB.Sec L)
    (hcov : ⨆ i, Out.nonzeroLocus (s i) = ⊤)
    (H : ∀ i, IsAffineOpen (Out.nonzeroLocus (s i)) ∧
      ∃ r : Fin (M + 1) → Γ(X.left, Out.nonzeroLocus (s i)),
        (∀ j k, resG X.left (inf_le_right : Out.nonzeroLocus (s i) ⊓ L.U k ≤ L.U k) ((s j).f k) =
          resG X.left (inf_le_left : Out.nonzeroLocus (s i) ⊓ L.U k ≤ _) (r j) *
          resG X.left (inf_le_right : Out.nonzeroLocus (s i) ⊓ L.U k ≤ L.U k) ((s i).f k)) ∧
        ∃ c : ℂ →+* Γ(X.left, Out.nonzeroLocus (s i)), (∀ a, c a = constFn X.hom _ a) ∧
          Function.Surjective (MvPolynomial.eval₂Hom c r)) :
    @CompactSpace _ (pointTopology X) := by
  letI := pointTopology X
  choose hA r hr c hc hsurj using H
  have hC := fun i => exists_compact_of_affine h1 h2 X _ (hA i) (r i) (c i) (hc i) (hsurj i)
  choose C hCc hCmem using hC
  refine ⟨(isCompact_iUnion hCc).of_isClosed_subset isClosed_univ fun x _ => ?_⟩
  have hx0 : x.left (default : PrimeSpectrum ℂ) ∈ (⨆ i, Out.nonzeroLocus (s i)) := by
    rw [hcov]; trivial
  unfold Out.nonzeroLocus at hx0
  simp only [TopologicalSpace.Opens.mem_iSup] at hx0
  obtain ⟨i, k, hik⟩ := hx0
  set a : Fin (M + 1) → ℂ := fun j => valAt' x.left (L.U k) ((s j).f k) with ha
  obtain ⟨i0, hi0⟩ := Finite.exists_max (fun j => ‖a j‖)
  have hai : a i ≠ 0 := ((h1 _ x.left).2.2.2.2.1 _ _).1 (((h1 _ x.left).1 _).2 hik)
  have hai0 : a i0 ≠ 0 := by
    intro h0
    have := hi0 i
    rw [h0, norm_zero] at this
    exact hai (norm_le_zero_iff.1 this)
  have hb0 : ⊤ ≤ x.left ⁻¹ᵁ X.left.basicOpen ((s i0).f k) := ((h1 _ x.left).2.2.2.2.1 _ _).2 hai0
  have hmem0 : x.left (default : PrimeSpectrum ℂ) ∈ X.left.basicOpen ((s i0).f k) := ((h1 _ x.left).1 _).1 hb0
  have hN : ⊤ ≤ x.left ⁻¹ᵁ Out.nonzeroLocus (s i0) := by
    refine ((h1 _ x.left).1 _).2 ?_
    unfold Out.nonzeroLocus
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hmem0⟩
  have hNk : ⊤ ≤ x.left ⁻¹ᵁ (Out.nonzeroLocus (s i0) ⊓ L.U k) :=
    ((h1 _ x.left).1 _).2 ⟨((h1 _ x.left).1 _).1 hN, X.left.basicOpen_le _ hmem0⟩
  refine Set.mem_iUnion.2 ⟨i0, hCmem i0 x hN fun j => ?_⟩
  have hrel : a j = valAt' x.left (Out.nonzeroLocus (s i0)) (r i0 j) * a i0 := by
    obtain ⟨e, he⟩ := (h1 _ x.left).2.1 _ hNk
    have := congrArg e (hr i0 j k)
    rw [map_mul, ← he, ← he, ← he, (h1 _ x.left).2.2.1 _ _ _ _ hNk, (h1 _ x.left).2.2.1 _ _ _ _ hNk,
      (h1 _ x.left).2.2.1 _ _ _ _ hNk] at this
    exact this
  have hle := hi0 j
  rw [hrel, norm_mul] at hle
  have hpos : 0 < ‖a i0‖ := norm_pos_iff.2 hai0
  nlinarith

theorem compactSpace_points_polAV : (∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a)) → (∀ (X : Over (Sp ℂ)) (U : X.left.Opens), IsAffineOpen U → ∀ e : Γ(X.left, U) →+* ℂ, (∀ a, e (constFn X.hom U a) = a) → ∃! x : (𝟙_ (Over (Sp ℂ)) ⟶ X), ⊤ ≤ (x).left ⁻¹ᵁ U ∧ ∀ f, valAt' x.left U f = e f) → (∀ P : Out.PolAV (Sp ℂ), @CompactSpace (𝟙_ (Over (Sp ℂ)) ⟶ P.A) (TopologicalSpace.generateFrom {S : Set (𝟙_ (Over (Sp ℂ)) ⟶ P.A) | ∃ (U : P.A.left.Opens) (f : Γ(P.A.left, U)) (O : Set ℂ), IsOpen O ∧ S = {x | ⊤ ≤ (x).left ⁻¹ᵁ U ∧ valAt' x.left U f ∈ O}})) := by
  intro h1 h2 P
  obtain ⟨A, grp, hab, g, hsm, L, hL, hrig, h9⟩ := P
  unfold Out.RelAmple at h9
  obtain ⟨N, hN, M, s, hcov, hh⟩ := h9 ⊤ (AlgebraicGeometry.isAffineOpen_top _)
  let X' : Over (Sp ℂ) := Over.mk ((A.hom ∣_ ⊤) ≫ (⊤ : (Sp ℂ).Opens).ι)
  haveI : IsIso (⊤ : (Sp ℂ).Opens).ι := by
    rw [← Scheme.topIso_hom]
    infer_instance
  have hψ : Function.Surjective (((⊤ : (Sp ℂ).Opens).ι.app ⊤).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) := by
    have s1 := (ConcreteCategory.bijective_of_isIso ((⊤ : (Sp ℂ).Opens).ι.app ⊤)).2
    have s2 := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv).2
    exact s1.comp s2
  have hC : @CompactSpace _ (pointTopology X') := by
    refine compact_of_sections h1 h2 X' (Out.powOver A hsm ⊤ N) s hcov fun i => ?_
    obtain ⟨ha, r, hr1, hr2⟩ := hh i
    refine ⟨ha, r, hr1, ((A.hom ∣_ ⊤).appLE ⊤ (Out.nonzeroLocus (s i)) ?_).hom.comp
      ((((⊤ : (Sp ℂ).Opens).ι.app ⊤).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom)), ?_, ?_⟩
    · exact le_top
    · intro a
      rfl
    · intro y
      obtain ⟨p, rfl⟩ := hr2 y
      obtain ⟨q, rfl⟩ := MvPolynomial.map_surjective _ hψ p
      refine ⟨q, ?_⟩
      rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.coe_eval₂Hom]
      exact (MvPolynomial.eval₂_map _ _ _ _).symm
  let φ : X' ⟶ A := Over.homMk (A.hom ⁻¹ᵁ ⊤).ι (morphismRestrict_ι _ _).symm
  letI := pointTopology X'
  letI := pointTopology A
  have hsurj : Function.Surjective (fun y : 𝟙_ (Over (Sp ℂ)) ⟶ X' => y ≫ φ) := by
    intro x
    have hr : Set.range x.left.base ⊆ Set.range (A.hom ⁻¹ᵁ ⊤).ι.base := by
      rw [Scheme.Opens.range_ι]
      intro y _
      trivial
    let y0 := IsOpenImmersion.lift (A.hom ⁻¹ᵁ ⊤).ι x.left hr
    have hy0 : y0 ≫ (A.hom ⁻¹ᵁ ⊤).ι = x.left := IsOpenImmersion.lift_fac _ _ _
    refine ⟨Over.homMk y0 ?_, ?_⟩
    · show y0 ≫ (A.hom ∣_ ⊤) ≫ (⊤ : (Sp ℂ).Opens).ι = _
      rw [morphismRestrict_ι, ← Category.assoc, hy0]
      exact Over.w x
    · ext1
      exact hy0
  exact hsurj.compactSpace (continuous_comp h1 φ)

end GlobalTheory.PointsCompact
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ToricGeometry.CubeTrivialisationOnUniformisingSpace
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

noncomputable section

namespace GlobalTheory.CubeValues

def ValueRules : Prop :=
  ∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a)

section Values

variable {X : Scheme.{0}} (x : Sp ℂ ⟶ X)

lemma le_preimage_inf (U V : X.Opens) :
    ⊤ ≤ x ⁻¹ᵁ (U ⊓ V) ↔ ⊤ ≤ x ⁻¹ᵁ U ∧ ⊤ ≤ x ⁻¹ᵁ V := by
  show ⊤ ≤ x ⁻¹ᵁ U ⊓ x ⁻¹ᵁ V ↔ _
  exact le_inf_iff

lemma val_unit_ne_zero (hv : ValueRules) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)ˣ) :
    valAt' x U f.val ≠ 0 := by
  obtain ⟨e, he⟩ := (hv X x).2.1 U h
  rw [he]
  exact (Units.map (e : Γ(X, U) →* ℂ) f).ne_zero

lemma val_unit_mul (hv : ValueRules) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (f f' : Γ(X, U)ˣ) :
    valAt' x U (f * f').val = valAt' x U f.val * valAt' x U f'.val := by
  obtain ⟨e, he⟩ := (hv X x).2.1 U h
  rw [he, he, he, Units.val_mul, map_mul]

lemma val_unit_prod_zpow (hv : ValueRules) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) {K : Type} [Fintype K]
    (f : K → Γ(X, U)ˣ) (ε : K → ℤ) :
    valAt' x U (∏ k, f k ^ ε k).val = ∏ k, valAt' x U (f k).val ^ ε k := by
  obtain ⟨e, he⟩ := (hv X x).2.1 U h
  have hm : ∀ w : Γ(X, U)ˣ, valAt' x U w.val = ((Units.map (e : Γ(X, U) →* ℂ) w : ℂˣ) : ℂ) :=
    fun w => he w.val
  calc valAt' x U (∏ k, f k ^ ε k).val = ((Units.map (e : Γ(X, U) →* ℂ) (∏ k, f k ^ ε k) : ℂˣ) : ℂ) := hm _
    _ = ∏ k, ((Units.map (e : Γ(X, U) →* ℂ) (f k) : ℂˣ) : ℂ) ^ ε k := by
      rw [map_prod, Units.coe_prod]
      simp only [map_zpow, Units.val_zpow_eq_zpow_val]
    _ = ∏ k, valAt' x U (f k).val ^ ε k := by simp only [hm]

lemma val_res (hv : ValueRules) {U V : X.Opens} (hVU : V ≤ U) (h : ⊤ ≤ x ⁻¹ᵁ V) (f : Γ(X, U)ˣ) :
    valAt' x V (res hVU f).val = valAt' x U f.val :=
  (hv X x).2.2.1 U V hVU f.val h

lemma val_pullU (hv : ValueRules) {Y : Scheme.{0}} (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)ˣ) :
    valAt' x (φ ⁻¹ᵁ U) (pullU φ U f).val = valAt' (x ≫ φ) U f.val :=
  (hv X x).2.2.2.1 Y φ U f.val

lemma le_preimage_wchart {Y : Scheme.{0}} (L : LB Y) {K : Type} [Fintype K] (φ : K → (X ⟶ Y))
    (j : K → L.ι) :
    ⊤ ≤ x ⁻¹ᵁ L.wchart φ j ↔ ∀ k, ⊤ ≤ (x ≫ φ k) ⁻¹ᵁ L.U (j k) := by
  have key : ∀ q : Sp ℂ, q ∈ x ⁻¹ᵁ L.wchart φ j ↔ ∀ k, q ∈ (x ≫ φ k) ⁻¹ᵁ L.U (j k) := by
    intro q
    show x q ∈ L.wchart φ j ↔ ∀ k, φ k (x q) ∈ L.U (j k)
    simp [LB.wchart]
  constructor
  · intro h k q _
    exact (key q).1 (h trivial) k
  · intro h q _
    exact (key q).2 (fun k => h k trivial)

lemma val_gen (hv : ValueRules) {L : LB X} (t : L.Gen) (ht : t.IsGen) (i j : L.ι)
    (hi : ⊤ ≤ x ⁻¹ᵁ L.U i) (hj : ⊤ ≤ x ⁻¹ᵁ L.U j) :
    valAt' x (L.U i) (t.s i).val =
      valAt' x (L.U i ⊓ L.U j) (L.g i j).val * valAt' x (L.U j) (t.s j).val := by
  have hij : ⊤ ≤ x ⁻¹ᵁ (L.U i ⊓ L.U j) := (le_preimage_inf x _ _).2 ⟨hi, hj⟩
  have e := congrArg (fun w : Γ(X, L.U i ⊓ L.U j)ˣ => valAt' x (L.U i ⊓ L.U j) w.val) (ht i j)
  rw [val_unit_mul x hv hij, val_res x hv _ hij, val_res x hv _ hij] at e
  exact e

lemma val_linComb (hv : ValueRules) {Y : Scheme.{0}} (L : LB Y) {K : Type} [Fintype K]
    (φ : K → (X ⟶ Y)) (ε : K → ℤ) (j j' : K → L.ι)
    (hj : ⊤ ≤ x ⁻¹ᵁ L.wchart φ j) (hj' : ⊤ ≤ x ⁻¹ᵁ L.wchart φ j') :
    valAt' x (L.wchart φ j ⊓ L.wchart φ j') ((L.LinComb φ ε).g j j').val =
      ∏ k, valAt' (x ≫ φ k) (L.U (j k) ⊓ L.U (j' k)) (L.g (j k) (j' k)).val ^ ε k := by
  have h2 : ⊤ ≤ x ⁻¹ᵁ (L.wchart φ j ⊓ L.wchart φ j') := (le_preimage_inf x _ _).2 ⟨hj, hj'⟩
  simp only [LB.LinComb]
  rw [val_unit_prod_zpow x hv h2]
  refine Finset.prod_congr rfl (fun k _ => ?_)
  congr 1
  refine (val_res x hv _ h2 _).trans ?_
  exact val_pullU x hv (φ k) (L.U (j k) ⊓ L.U (j' k)) (L.g (j k) (j' k))

lemma val_cocycle (hv : ValueRules) {L : LB X} (hL : L.IsLB) (i j k : L.ι)
    (hi : ⊤ ≤ x ⁻¹ᵁ L.U i) (hj : ⊤ ≤ x ⁻¹ᵁ L.U j) (hk : ⊤ ≤ x ⁻¹ᵁ L.U k) :
    valAt' x (L.U i ⊓ L.U j) (L.g i j).val * valAt' x (L.U j ⊓ L.U k) (L.g j k).val =
      valAt' x (L.U i ⊓ L.U k) (L.g i k).val := by
  obtain ⟨-, -, hc⟩ := hL
  have hij : ⊤ ≤ x ⁻¹ᵁ (L.U i ⊓ L.U j) := (le_preimage_inf x _ _).2 ⟨hi, hj⟩
  have hijk : ⊤ ≤ x ⁻¹ᵁ (L.U i ⊓ L.U j ⊓ L.U k) := (le_preimage_inf x _ _).2 ⟨hij, hk⟩
  have e := congrArg (fun w : Γ(X, L.U i ⊓ L.U j ⊓ L.U k)ˣ => valAt' x _ w.val) (hc i j k)
  rw [val_unit_mul x hv hijk, val_res x hv _ hijk, val_res x hv _ hijk, val_res x hv _ hijk] at e
  exact e

end Values

section Points

variable {A : Over (Sp ℂ)} [GrpObj A] {L₀ : LB A.left} {g : ℕ} (u : HolUnif A L₀ g)

lemma ex_zero : u.ex 0 = 1 := (u.ker 0).2 (zero_mem _)

lemma ex_add_period (z l : Fin g → ℂ) (hl : l ∈ u.Λ) : u.ex (z + l) = u.ex z := by
  rw [u.ex_add, (u.ker l).2 hl, _root_.mul_one]

lemma comp_foldr {T T' : Over (Sp ℂ)} (p : T' ⟶ T) {n : ℕ} (y : Fin n → (T ⟶ A)) (l : List (Fin n)) :
    p ≫ l.foldr (fun k acc => padd A (y k) acc) (pzero A T) = (l.map fun k => p ≫ y k).prod := by
  induction l with
  | nil =>
    simp only [List.foldr_nil, List.map_nil, List.prod_nil, pzero, Hom.one_def, comp_toUnit_assoc]
  | cons k l ih =>
    simp only [List.foldr_cons, List.map_cons, List.prod_cons, ← ih, padd, Hom.mul_def, comp_lift_assoc]

lemma ex_list_sum {κ : Type} (w : κ → Fin g → ℂ) (l : List κ) :
    u.ex (l.map w).sum = (l.map fun k => u.ex (w k)).prod := by
  induction l with
  | nil => simp only [List.map_nil, List.sum_nil, List.prod_nil, ex_zero]
  | cons k l ih => simp only [List.map_cons, List.sum_cons, List.prod_cons, u.ex_add, ih]

lemma comp_psum {T : Over (Sp ℂ)} (p : 𝟙_ (Over (Sp ℂ)) ⟶ T) {n : ℕ} (y : Fin n → (T ⟶ A))
    (w : Fin n → Fin g → ℂ) (h : ∀ k, p ≫ y k = u.ex (w k)) (I : Finset (Fin n)) :
    p ≫ psum A y I = u.ex (∑ a ∈ I, w a) := by
  have hs : ∑ a ∈ I, w a = (((List.finRange n).filter (fun a => decide (a ∈ I))).map w).sum := by
    rw [← List.sum_toFinset _ ((List.nodup_finRange n).filter _)]
    congr 1
    ext a
    simp
  rw [psum, comp_foldr, hs, ex_list_sum]
  exact congrArg List.prod (List.map_congr_left (fun k _ => h k))

def pt3 (x : Fin 3 → Fin g → ℂ) : 𝟙_ (Over (Sp ℂ)) ⟶ G3 A :=
  lift (u.ex (x 0)) (lift (u.ex (x 1)) (u.ex (x 2)))

lemma tripleProductPoint_comp_partialSum (x : Fin 3 → Fin g → ℂ) (I : Finset (Fin 3)) :
    (pt3 u x).left ≫ (psum A (x3 A) I).left = (u.ex (∑ a ∈ I, x a)).left := by
  rw [← Over.comp_left, comp_psum u (pt3 u x) (x3 A) x _ I]
  intro k
  fin_cases k <;> simp [pt3, x3]

lemma tripleProductPoint_add_period (x l : Fin 3 → Fin g → ℂ) (hl : ∀ a, l a ∈ u.Λ) :
    pt3 u (x + l) = pt3 u x := by
  simp only [pt3, Pi.add_apply, ex_add_period u _ _ (hl _)]

lemma hol_coord (a : Fin 3) (U : A.left.Opens) (f : Γ(A.left, U)) :
    IsOpen {w : Fin 3 → Fin g → ℂ | w ∈ (Set.univ : Set _) ∧ ⊤ ≤ (u.ex (w a)).left ⁻¹ᵁ U} ∧
      DifferentiableOn ℂ (fun w : Fin 3 → Fin g → ℂ => valAt' (u.ex (w a)).left U f)
        {w | w ∈ (Set.univ : Set _) ∧ ⊤ ≤ (u.ex (w a)).left ⁻¹ᵁ U} := by
  obtain ⟨ho, hd⟩ := u.hol U f
  have hset : {w : Fin 3 → Fin g → ℂ | w ∈ (Set.univ : Set _) ∧ ⊤ ≤ (u.ex (w a)).left ⁻¹ᵁ U} =
      (fun w : Fin 3 → Fin g → ℂ => w a) ⁻¹' {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ U} := by
    ext w; simp
  refine ⟨?_, ?_⟩
  · rw [hset]
    exact ho.preimage (continuous_apply a)
  · exact hd.comp (differentiable_apply a).differentiableOn (fun w hw => hw.2)

private theorem pt3_preimage_theta_whole_iff {A : Over (Sp ℂ)} [GrpObj A] {L₀ : LB A.left} {g : ℕ}
    (u : HolUnif A L₀ g) (L : LB A.left) (j : Finset (Fin 3) → L.ι) (x : Fin 3 → Fin g → ℂ) :
    ⊤ ≤ (pt3 u x).left ⁻¹ᵁ (Theta A L).U (fun I => j I.down) ↔
      ∀ I : Finset (Fin 3), ⊤ ≤ (u.ex (∑ a ∈ I, x a)).left ⁻¹ᵁ L.U (j I) := by
  show ⊤ ≤ (pt3 u x).left ⁻¹ᵁ
      L.wchart (fun I : ULift (Finset (Fin 3)) => (psum A (x3 A) I.down).left) (fun I => j I.down) ↔ _
  rw [le_preimage_wchart]
  simp only [tripleProductPoint_comp_partialSum]
  exact ⟨fun h I => h ⟨I⟩, fun h I => h I.down⟩

private theorem valAt_theta_transition_eq_prod_zpow (hv : ValueRules) {A : Over (Sp ℂ)} [GrpObj A] {L₀ : LB A.left}
    {g : ℕ} (u : HolUnif A L₀ g) (L : LB A.left) (j j' : Finset (Fin 3) → L.ι) (x : Fin 3 → Fin g → ℂ)
    (hj : ⊤ ≤ (pt3 u x).left ⁻¹ᵁ (Theta A L).U (fun I => j I.down))
    (hj' : ⊤ ≤ (pt3 u x).left ⁻¹ᵁ (Theta A L).U (fun I => j' I.down)) :
    valAt' (pt3 u x).left ((Theta A L).U (fun I => j I.down) ⊓ (Theta A L).U (fun I => j' I.down))
        ((Theta A L).g (fun I => j I.down) (fun I => j' I.down)).val =
      ∏ I : Finset (Fin 3), valAt' (u.ex (∑ a ∈ I, x a)).left (L.U (j I) ⊓ L.U (j' I))
        (L.g (j I) (j' I)).val ^ ((-1 : ℤ) ^ (3 - I.card)) := by
  have e := val_linComb (pt3 u x).left hv L
    (fun I : ULift (Finset (Fin 3)) => (psum A (x3 A) I.down).left)
    (fun I : ULift (Finset (Fin 3)) => (-1 : ℤ) ^ (3 - I.down.card)) (fun I => j I.down) (fun I => j' I.down) hj hj'
  simp only [tripleProductPoint_comp_partialSum] at e
  refine e.trans ?_
  exact Fintype.prod_equiv Equiv.ulift _ _ (fun _ => rfl)

end Points

end GlobalTheory.CubeValues

open GlobalTheory.CubeValues in

theorem GlobalTheory.cube_trivialisation_on_uniformising_space :
    (∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a)) → (∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (W : Set E) (X Y : Over (Sp ℂ)) (a : E → (𝟙_ (Over (Sp ℂ)) ⟶ X)) (b : E → (𝟙_ (Over (Sp ℂ)) ⟶ Y)), (∀ (U : (X).left.Opens) (f : Γ((X).left, U)), IsOpen {w | w ∈ W ∧ ⊤ ≤ (a w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' (a w).left U f) {w | w ∈ W ∧ ⊤ ≤ (a w).left ⁻¹ᵁ U}) → (∀ (U : (Y).left.Opens) (f : Γ((Y).left, U)), IsOpen {w | w ∈ W ∧ ⊤ ≤ (b w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' (b w).left U f) {w | w ∈ W ∧ ⊤ ≤ (b w).left ⁻¹ᵁ U}) → (∀ (U : (X ⊗ Y).left.Opens) (f : Γ((X ⊗ Y).left, U)), IsOpen {w | w ∈ W ∧ ⊤ ≤ ((fun w => lift (a w) (b w)) w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' ((fun w => lift (a w) (b w)) w).left U f) {w | w ∈ W ∧ ⊤ ≤ ((fun w => lift (a w) (b w)) w).left ⁻¹ᵁ U})) → (∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (L₀ L : LB A.left) (g : ℕ) (u : HolUnif A L₀ g), L.IsLB → ∀ t : LB.Gen (Theta A L), t.IsGen → ∀ (W : L.ι → Set (Fin g → ℂ)) (c : L.ι → L.ι → (Fin g → ℂ) → ℂ), W = (fun (i : L.ι) => {z : Fin g → ℂ | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i}) → c = (fun (i j : L.ι) (z : Fin g → ℂ) => valAt' (u.ex z).left (L.U i ⊓ L.U j) (L.g i j).val) → ((∀ i, IsOpen (W i)) ∧ (∀ z, ∃ i, z ∈ W i) ∧ (∀ i j, DifferentiableOn ℂ (c i j) (W i ∩ W j)) ∧ (∀ i j z, z ∈ W i → z ∈ W j → c i j z ≠ 0) ∧ (∀ i j k z, z ∈ W i → z ∈ W j → z ∈ W k → c i j z * c j k z = c i k z) ∧ (∀ i z, ∀ l ∈ u.Λ, z + l ∈ W i ↔ z ∈ W i) ∧ (∀ i j z, ∀ l ∈ u.Λ, c i j (z + l) = c i j z)) ∧ ∃ T : (Finset (Fin 3) → L.ι) → (Fin 3 → Fin g → ℂ) → ℂ, (∀ j, DifferentiableOn ℂ (T j) {x | (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I))}) ∧ (∀ j x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) → T j x ≠ 0) ∧ (∀ j j' x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) → (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j' I)) → T j x = (∏ I : Finset (Fin 3), c (j I) (j' I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card))) * T j' x) ∧ (∀ j x (l : Fin 3 → Fin g → ℂ), (∀ a, l a ∈ u.Λ) → T j (x + l) = T j x)) := by
  intro hv0 hlift A _ _ L₀ L g u hL t ht W c hW hc
  have hv : ValueRules := hv0
  subst hW hc
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro i
    exact (u.hol (L.U i) 0).1
  · intro z
    have hq : (u.ex z).left (default : PrimeSpectrum ℂ) ∈ ⨆ i, L.U i := by
      rw [hL.cover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hq
    exact ⟨i, ((hv _ (u.ex z).left).1 (L.U i)).2 hi⟩
  · intro i j
    have hset : ({z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i} ∩ {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U j}) =
        {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (L.U i ⊓ L.U j)} := by
      ext z
      exact (le_preimage_inf _ _ _).symm
    show DifferentiableOn ℂ (fun z => valAt' (u.ex z).left (L.U i ⊓ L.U j) (L.g i j).val)
      ({z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i} ∩ {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U j})
    rw [hset]
    exact (u.hol _ _).2
  · intro i j z hi hj
    exact val_unit_ne_zero _ hv ((le_preimage_inf _ _ _).2 ⟨hi, hj⟩) _
  · intro i j k z hi hj hk
    exact val_cocycle _ hv hL i j k hi hj hk
  · intro i z l hl
    show ⊤ ≤ (u.ex (z + l)).left ⁻¹ᵁ L.U i ↔ ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i
    rw [ex_add_period u z l hl]
  · intro i j z l hl
    show valAt' (u.ex (z + l)).left _ _ = valAt' (u.ex z).left _ _
    rw [ex_add_period u z l hl]
  · have hH := hlift (Fin 3 → Fin g → ℂ) Set.univ A (A ⊗ A) (fun w => u.ex (w 0))
      (fun w => lift (u.ex (w 1)) (u.ex (w 2))) (fun U f => hol_coord u 0 U f)
      (hlift (Fin 3 → Fin g → ℂ) Set.univ A A (fun w => u.ex (w 1)) (fun w => u.ex (w 2))
        (fun U f => hol_coord u 1 U f) (fun U f => hol_coord u 2 U f))
    refine ⟨fun j x => valAt' (pt3 u x).left ((Theta A L).U (fun I => j I.down)) (t.s (fun I => j I.down)).val,
      ?_, ?_, ?_, ?_⟩
    · intro j
      refine ((hH ((Theta A L).U (fun I => j I.down)) (t.s (fun I => j I.down)).val).2).mono ?_
      intro x hx
      exact ⟨trivial, (GlobalTheory.CubeValues.pt3_preimage_theta_whole_iff u L j x).2 hx⟩
    · intro j x hx
      exact val_unit_ne_zero _ hv ((GlobalTheory.CubeValues.pt3_preimage_theta_whole_iff u L j x).2 hx) _
    · intro j j' x hx hx'
      have hi := (GlobalTheory.CubeValues.pt3_preimage_theta_whole_iff u L j x).2 hx
      have hi' := (GlobalTheory.CubeValues.pt3_preimage_theta_whole_iff u L j' x).2 hx'
      have e := val_gen (pt3 u x).left hv t ht _ _ hi hi'
      rw [GlobalTheory.CubeValues.valAt_theta_transition_eq_prod_zpow hv u L j j' x hi hi'] at e
      exact e
    · intro j x l hl
      show valAt' (pt3 u (x + l)).left _ _ = valAt' (pt3 u x).left _ _
      rw [tripleProductPoint_add_period u x l hl]
end
end

