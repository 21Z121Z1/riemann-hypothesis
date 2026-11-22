import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0140
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0085
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0214
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0062
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0186
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0178
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaHolomorphic
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0187
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0102
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0059
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GeometricallyConnectedOfIsPullbackOfSurjective
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0019

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubicalWeilPairingEq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct

namespace GlobalTheory.FlatTors

theorem weilIs_of_cubWeil_of_proper {S S' : Scheme.{0}} (f : S' ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G]
    (hG : IsSemiAbelian G) (hpr : IsProper (pullback.snd G.hom f)) {L : RigLB G} (c : CubicalStr G L) (k : ℕ)
    (T : Over S') (x y : Over.mk (T.hom ≫ f) ⟶ G) (z : Γ(T.left, ⊤)ˣ) (h : GlobalTheory.UU.CubWeil c k x y z) :
    WeilIs G L.L (k : ℤ) x y z := by
  let G' : Over S' := (Over.pullback f).obj G
  have hp : IsGrpPullback G' G f (pullback.fst G.hom f) := isGrpPullback_pullback G f
  have hG' : IsSemiAbelian G' := IsSemiAbelian.pullback f G hG
  have := hG'.comm
  have hA : IsAbelianScheme G' := ⟨hG'.comm, hG'.smooth, hpr, hG'.geomConnected⟩
  obtain ⟨hL, hr, ⟨c', hc'⟩, -⟩ := CubePf.cubePull _ _ G G' (cubeMapOf hp) L c
  have hw : pullback.fst G.hom f ≫ G.hom = G'.hom ≫ f := pullback.condition
  let β := GlobalTheory.UU.toBaseHom (GlobalTheory.UU.toBase_mul_pullback G f) T
  have inj : Function.Injective β := fun a b e =>
    Over.OverMorphism.ext (hp.1.hom_ext (congrArg (fun z => z.left) e) ((Over.w a).trans (Over.w b).symm))
  have sur : Function.Surjective β := fun p =>
    ⟨Over.homMk (hp.1.lift p.left T.hom (Over.w p)) (hp.1.lift_snd _ _ _),
      Over.OverMorphism.ext (hp.1.lift_fst _ _ _)⟩
  obtain ⟨u, rfl⟩ := sur x
  obtain ⟨v, rfl⟩ := sur y
  have hu : u ^ k = 1 := inj (by rw [map_pow, map_one]; exact h.1)
  have hv : v ^ k = 1 := inj (by rw [map_pow, map_one]; exact h.2.1)
  obtain ⟨z', hz', -⟩ := GlobalTheory.UU.existsUnique_cubWeil c' hu hv
  have h₁ := GlobalTheory.UU.cubWeil_of_isPullCubical _ _ f G G' (cubeMapOf hp) hw (GlobalTheory.UU.toBase_mul_pullback G f) L _ c c' hc'
    k T u v z' hz'
  obtain rfl : z = z' := h.unique h₁
  have h₂ := (GlobalTheory.UU.cubWeil_iff_weilIs GlobalTheory.SemiRigid.globalFns hA hu hv z).1 hz'
  exact (GlobalTheory.weilIs_iff_of_isGrpPullback_comm _ _ G G' f _ L.L _ L.isLB hL hp
    ⟨GlobalTheory.UU.pullIso _ _, GlobalTheory.UU.pullIso_isGen L.isLB _⟩ T k u v (β u) (β v) z rfl rfl).1 h₂

end GlobalTheory.FlatTors
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsComplexCmAbelianObjectStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_complex_cm_abelian_object : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), 1 ≤ D.p + D.q → ∀ l : Level H, ∃ (b : Base l ℂ) (o : Obj D l b (𝟙 (Sp ℂ))), b.ρ = H.rt0 ∧ b.ζ = zeta l.A ∧ SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (D.p + D.q)) o.t.G.hom ∧ ∃ x : 𝟙_ (Over (Sp ℂ)) ⟶ o.t.G, x ≠ 1 := by
  first | exact @GlobalTheory.exists_obj_complex | exact GlobalTheory.exists_obj_complex | (intros; apply GlobalTheory.exists_obj_complex <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsEndomorphismsExtendNearGoodPrimeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_endomorphisms_extend_near_good_prime : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (β : o →+* R) (v : Ix g ((n ^ j) ^ 2) → R) (Z : Over (Sp R)) (M : LB Z.left) (th : Ix g ((n ^ j) ^ 2) → M.Sec) (sc : Ix g ((n ^ j) ^ 2) → (Out.baseOver (Sp R) ⟶ Z)) (q₀ : Ideal R) (i : Option J), Den b Mat κ β v q₀ → Fam b Mat κ β v (n ^ 2) M th sc → Smooth Z.hom → ∃ f : R, f ∉ q₀ ∧ ∀ (R' : Type) [CommRing R'] (ρ : R →+* R'), IsUnit (ρ f) → ∀ (Z' : Over (Sp R')) (π : Z'.left ⟶ Z.left), IsPullback π Z'.hom Z.hom (spMap ρ) → ∃ F : Z' ⟶ Z', EndOk b Mat κ β v (n ^ 2) M th sc ρ π i F := by
  first | exact @GlobalTheory.ZM.NearBuild.exists_endomorphism_near | exact GlobalTheory.ZM.NearBuild.exists_endomorphism_near | (intros; apply GlobalTheory.ZM.NearBuild.exists_endomorphism_near <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHolomorphicThetaConstants
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.ZM GlobalTheory.IndefiniteRowSideFullHecke.ThetaCosetLabels GlobalTheory.ThetaObjCompare
attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.TorusFamilyTheta

theorem matrix_eq_of_im {g : ℕ} {Hm Hm' : Matrix (Fin g) (Fin g) ℂ} {s : Set (Fin g → ℂ)}
    (hs : Submodule.span ℝ s = ⊤) (h : ∀ a ∈ s, ∀ c ∈ s, (hermForm Hm a c).im = (hermForm Hm' a c).im) :
    Hm = Hm' := by
  have k := HermAdjoint.adjoint_of_im (Hm - Hm') LinearMap.id 0 s hs fun a ha c hc => by
    have := h a ha c hc
    simp only [hermForm] at this
    simp [hermForm, Matrix.sub_mulVec, this]
  rw [← sub_eq_zero]
  ext i j
  simpa [hermForm, Pi.star_single] using k (Pi.single i 1) (Pi.single j 1)

theorem lattice_properties (P : Out.PolAV (Sp ℂ)) {La : Type} [AddCommGroup La] {Ef : LinearMap.BilinForm ℤ La}
    {χ : La → ℂ} {Q : La →+ (Fin P.g → ℂ)} (u : HolUnif P.A P.L P.g) {Hm : Matrix (Fin P.g) (Fin P.g) ℂ}
    {χ' : u.Λ → ℂ} (hQ : Function.Injective Q) (hΛ : ∀ z, z ∈ u.Λ ↔ ∃ l, z = Q l) (hA : u.IsAH Hm χ')
    (hχ : ∀ (l : La) (z : u.Λ), (z : Fin P.g → ℂ) = Q l → χ' z = χ l)
    (hE : ∀ l l', (hermForm Hm (Q l) (Q l')).im = (Ef l l' : ℝ)) :
    DiscreteTopology Q.range ∧ Submodule.span ℝ (Set.range Q) = ⊤ ∧ Function.Bijective Ef ∧
      (∀ x, χ x = 1 ∨ χ x = -1) ∧ ∀ x y, χ (x + y) = χ x * χ y * (-1) ^ Ef x y := by
  obtain ⟨E, hE', hb, h₁, h₂, -⟩ := AnyAppellHumbert.isAH_properties abelianSchemeLaws_all.1 abelianSchemeLaws_all.2
    (fun S P M hM => AbLaw.CubeAssembly.cube_gen S P M hM) thetaUnifAV_all P u Hm χ' hA
  have hr : Set.range Q = (u.Λ : Set (Fin P.g → ℂ)) := Set.ext fun z =>
    ⟨fun ⟨l, hl⟩ => (hΛ z).2 ⟨l, hl.symm⟩, fun hz => ((hΛ z).1 hz).imp fun _ => Eq.symm⟩
  let e : La ≃ₗ[ℤ] u.Λ := LinearEquiv.ofBijective
    (LinearMap.codRestrict u.Λ Q.toIntLinearMap fun l => (hΛ _).2 ⟨l, rfl⟩)
    ⟨fun x y h => hQ (congrArg Subtype.val h), fun z => ((hΛ z).1 z.2).imp fun _ h => Subtype.ext h.symm⟩
  have he : ∀ l, (e l : Fin P.g → ℂ) = Q l := fun _ => rfl
  have hEe : ∀ x y, E (e x) (e y) = Ef x y := fun x y => by
    apply Int.cast_injective (α := ℝ)
    rw [hE', he, he, hE]
  refine ⟨?_, hr ▸ u.full, ?_, fun x => hχ x _ (he x) ▸ h₁ (e x), fun x y => ?_⟩
  · have : DiscreteTopology (Set.range Q) := hr ▸ u.discrete
    exact this
  · have : ⇑Ef = e.dualMap ∘ E ∘ e := funext fun x => LinearMap.ext fun y => (hEe x y).symm
    rw [this]
    exact e.dualMap.bijective.comp (hb.comp e.bijective)
  · rw [← hχ _ _ (he (x + y)), ← hχ _ _ (he x), ← hχ _ _ (he y), map_add, h₂, hEe]

theorem exists_holomorphic_thetaConstants : ∀ (o : Type) [CommRing o] (g N' : ℕ) [NeZero N'] (J : Type) (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (Ef : LinearMap.BilinForm ℤ (Lat g)) (τ : J → (Lat g →ₗ[ℤ] Lat g)) (χ : Lat g → ℂ) (tl : Lab g (N' ^ 2) → Lat g) (d : ℕ) (U : Set (Fin d → ℂ)) (P : (Fin d → ℂ) → (Lat g →+ (Fin g → ℂ))), Odd N' → IsOpen U → (∀ l, DifferentiableOn ℂ (fun z => P z l) U) → (∀ z ∈ U, ∃ t : TObj g (N' ^ 2) J b (spMap em), IsTorusOf Ef χ tl τ (P z) (toTh t)) → ∃ θ : (Fin d → ℂ) → Ix g (N' ^ 2) → ℂ, (∀ a, DifferentiableOn ℂ (fun z => θ z a) U) ∧ ∀ z ∈ U, ∀ t : TObj g (N' ^ 2) J b (spMap em), IsTorusOf Ef χ tl τ (P z) (toTh t) → t.HasTh (𝟙 _) (θ z) := by
  intro o _ g N' _ J b em Ef τ χ tl d U P hN hU hP hex
  rcases U.eq_empty_or_nonempty with rfl | ⟨z₀, hz₀⟩
  · exact ⟨0, fun _ => differentiableOn_empty, fun _ h => absurd h (Set.notMem_empty _)⟩
  have hH : ∀ z, ∃ Hm : Matrix (Fin g) (Fin g) ℂ, z ∈ U → (Function.Injective (P z) ∧ DiscreteTopology (P z).range ∧
      Submodule.span ℝ (Set.range (P z)) = ⊤ ∧ Hm.IsHermitian ∧ (∀ w : Fin g → ℂ, w ≠ 0 → 0 < (hermForm Hm w w).re) ∧
      ∀ x y, (hermForm Hm (P z x) (P z y)).im = Ef x y) ∧ Function.Bijective Ef ∧
      (∀ x, χ x = 1 ∨ χ x = -1) ∧ ∀ x y, χ (x + y) = χ x * χ y * (-1) ^ Ef x y := fun z => by
    by_cases hz : z ∈ U
    · obtain ⟨t, u, Hm, χ', hi, hΛ, hA, hχ, hE, -⟩ := hex z hz
      obtain ⟨h₁, h₂, h₃⟩ := lattice_properties t.pol u hi hΛ hA hχ hE
      exact ⟨Hm, fun _ => ⟨⟨hi, h₁, h₂, hA.1, hA.2.1, hE⟩, h₃⟩⟩
    · exact ⟨0, fun h => absurd h hz⟩
  choose Hm hH using hH
  obtain ⟨-, hb, h₁, h₂⟩ := hH z₀ hz₀
  obtain ⟨θ, hθ, hhol⟩ := HolTheta.exists_theta_holomorphic (Lat g) Ef χ g d N' U P Hm hN.pos hb h₁ h₂ hU hP
    fun z hz => (hH z hz).1
  let lam : Fin (2 * g) → Lat g := fun i => tl ((labEquiv g _).symm (Pi.single i 1))
  let x : Ix g (N' ^ 2) → Lat g := fun a => ∑ i, ((a i).val : ℤ) • lam i
  refine ⟨fun z a => χ (x a) * (Complex.exp (-(Real.pi / 2 / (N' : ℂ) ^ 2) * hermForm (Hm z) (P z (x a)) (P z (x a))) *
    θ z ((N' : ℂ)⁻¹ • P z (x a))), fun a => (hhol (x a)).const_mul _, ?_⟩
  rintro z hz t ⟨u, Hm', χ', -, hΛ, hA, hχ, hE, hlev, -⟩
  obtain rfl : Hm z = Hm' := matrix_eq_of_im (hH z hz).1.2.2.1 (by
    rintro _ ⟨l, rfl⟩ _ ⟨l', rfl⟩
    rw [hE, (hH z hz).1.2.2.2.2.2])
  obtain ⟨hne, hdiff, hfe⟩ := hθ z hz
  let lam' : Fin (2 * g) → u.Λ := fun i => ⟨P z (lam i), (hΛ _).2 ⟨_, rfl⟩⟩
  have hth : u.IsThetaFn (Hm z) χ' 1 (θ z) := by
    refine ⟨hdiff, fun l w => ?_⟩
    obtain ⟨y, hy⟩ := (hΛ l).1 l.2
    rw [pow_one, hχ y l hy, hy, hfe]
  have key := ThetaClassical.hasTh_classical abelianSchemeLaws_all.1 abelianSchemeLaws_all.2 thetaUnifAV_all
    o g N' J b em t u (Hm z) χ' (θ z) lam' hN hA hth hne fun i => by
      have e := hlev ((labEquiv g _).symm (Pi.single i 1))
      rw [toTh_lev, lab_single, Nat.cast_pow] at e
      exact congrArg (fun f => f.left) e
  have hx : ∀ a : Ix g (N' ^ 2), ∑ i, ((a i).val : ℂ) • (lam' i : Fin g → ℂ) = P z (x a) := fun a => by
    simp only [x, lam', map_sum, map_zsmul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [natCast_zsmul, Nat.cast_smul_eq_nsmul]
  have hx' : ∀ a : Ix g (N' ^ 2), χ' (∑ i, ((a i).val : ℤ) • lam' i) = χ (x a) := fun a => by
    refine hχ _ _ ?_
    simp only [x, lam', map_sum, map_zsmul, AddSubmonoidClass.coe_finsetSum, SetLike.val_smul]
  simp only [hx, hx'] at key
  convert key using 2 with a
  exact (_root_.mul_assoc _ _ _).symm

end GlobalTheory.TorusFamilyTheta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHomOfEquivariant
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct

namespace GlobalTheory.GaloisPoints

theorem exists_factor_of_fixed {K L : Type} [Field K] [CharZero K] [Field L] [Algebra K L]
    (em : L →ₐ[K] AlgebraicClosure K) {Y : Scheme} (y : Sp (AlgebraicClosure K) ⟶ Y)
    (h : ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, (∀ a, σ (em a) = em a) →
      spMap σ.toAlgHom.toRingHom ≫ y = y) :
    ∃ z : Sp L ⟶ Y, spMap em.toRingHom ≫ z = y := by
  obtain ⟨⟨p, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField (AlgebraicClosure K) Y).symm.surjective y
  have hy : (Scheme.SpecToEquivOfField (AlgebraicClosure K) Y).symm ⟨p, φ⟩ =
      Spec.map φ ≫ Y.fromSpecResidueField p := rfl
  rw [hy] at h ⊢
  have hmem : ∀ b, φ.hom b ∈ em.fieldRange := by
    intro b
    rw [← InfiniteGalois.fixedField_fixingSubgroup em.fieldRange, IntermediateField.mem_fixedField_iff]
    intro σ hσ
    have h1 := h σ (fun a => (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ _ ⟨a, rfl⟩)
    rw [← Category.assoc, cancel_mono, ← Spec.map_comp, Spec.map_inj] at h1
    exact congrArg (fun ψ => ψ.hom b) h1
  let e : L ≃ₐ[K] em.fieldRange := AlgEquiv.ofInjectiveField em
  let ψ : Y.residueField p →+* L :=
    e.symm.toAlgHom.toRingHom.comp (φ.hom.codRestrict em.fieldRange hmem)
  refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ Y.fromSpecResidueField p, ?_⟩
  rw [← Category.assoc, ← Spec.map_comp]
  congr 2
  ext b
  have : ∀ c, em c = (e c : AlgebraicClosure K) := fun c => rfl
  show em (e.symm ⟨φ.hom b, hmem b⟩) = φ.hom b
  rw [this, e.apply_symm_apply]

theorem exists_sigma_iso {K : Type} [Field K] (X : Over (Sp K)) [IsFinite X.hom] [Etale X.hom] :
    ∃ (I : Type) (L : I → Type) (_ : ∀ i, Field (L i)) (_ : ∀ i, Algebra K (L i))
      (e : (∐ fun i => Sp (L i)) ≅ X.left), (∀ i, Algebra.IsAlgebraic K (L i)) ∧
      ∀ i, Sigma.ι (fun i => Sp (L i)) i ≫ e.hom ≫ X.hom = spMap (algebraMap K (L i)) := by
  haveI : IsAffine X.left := isAffine_of_isAffineHom X.hom
  let A : CommRingCat := Γ(X.left, ⊤)
  let φ : CommRingCat.of K ⟶ A := Spec.preimage (X.left.isoSpec.inv ≫ X.hom)
  have hφ : Spec.map φ = X.left.isoSpec.inv ≫ X.hom := Spec.map_preimage _
  have hE : Etale (Spec.map φ) := by rw [hφ]; infer_instance
  have hE' : φ.hom.Etale := (HasRingHomProperty.Spec_iff (P := @Etale)).1 hE
  letI : Algebra K A := φ.hom.toAlgebra
  haveI : Algebra.Etale K A := hE'
  obtain ⟨I, hI, L, iF, iA, e, hs⟩ := (Algebra.FormallyEtale.iff_exists_algEquiv_prod K A).1 inferInstance
  let e' : A ≅ CommRingCat.of (∀ i, L i) := e.toRingEquiv.toCommRingCatIso
  refine ⟨I, L, iF, iA, asIso (sigmaSpec fun i => CommRingCat.of (L i)) ≪≫
    asIso (Spec.map e'.hom) ≪≫ X.left.isoSpec.symm, fun i => inferInstance, fun i => ?_⟩
  simp only [Iso.trans_hom, asIso_hom, Iso.symm_hom, Category.assoc]
  rw [← hφ, ι_sigmaSpec_assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext a
  exact congrFun (e.commutes a) i

theorem exists_hom_of_equivariant : ∀ (K : Type) [Field K] [CharZero K] (X Y : Over (Sp K)), IsFinite X.hom → Etale X.hom → ∀ f : (Over.mk (spMap (algebraMap K (AlgebraicClosure K))) ⟶ X) → (Over.mk (spMap (algebraMap K (AlgebraicClosure K))) ⟶ Y), (∀ (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) x x', x'.left = spMap σ.toAlgHom.toRingHom ≫ x.left → (f x').left = spMap σ.toAlgHom.toRingHom ≫ (f x).left) → ∃ u : X ⟶ Y, ∀ x, x ≫ u = f x := by
  intro K _ _ X Y _ _ f hf
  obtain ⟨I, L, iF, iA, e, halg, he⟩ := exists_sigma_iso X
  let em : ∀ i, L i →ₐ[K] AlgebraicClosure K := fun i => IsAlgClosed.lift
  have hem : ∀ i (j : L i →ₐ[K] AlgebraicClosure K),
      spMap j.toRingHom ≫ spMap (algebraMap K (L i)) = spMap (algebraMap K (AlgebraicClosure K)) := by
    intro i j
    rw [← Spec.map_comp]
    congr 1
    ext a
    exact j.commutes a
  let x₀ : ∀ i, (Over.mk (spMap (algebraMap K (AlgebraicClosure K))) ⟶ X) := fun i =>
    Over.homMk (spMap (em i).toRingHom ≫ Sigma.ι (fun i => Sp (L i)) i ≫ e.hom) (by
      simp only [Category.assoc, he]
      exact hem i _)
  have hx₀ : ∀ i, (x₀ i).left = spMap (em i).toRingHom ≫ Sigma.ι (fun i => Sp (L i)) i ≫ e.hom :=
    fun i => rfl
  have hz : ∀ i, ∃ z : Sp (L i) ⟶ Y.left, spMap (em i).toRingHom ≫ z = (f (x₀ i)).left := by
    intro i
    refine exists_factor_of_fixed (em i) _ fun σ hσ => (hf σ (x₀ i) (x₀ i) ?_).symm
    rw [hx₀]
    erw [← Category.assoc (spMap σ.toAlgHom.toRingHom), ← Spec.map_comp]
    congr 2
    ext a
    exact (hσ a).symm
  choose z hz using hz
  have hzw : ∀ i, z i ≫ Y.hom = spMap (algebraMap K (L i)) := by
    intro i
    have h1 : spMap (em i).toRingHom ≫ z i ≫ Y.hom =
        spMap (em i).toRingHom ≫ spMap (algebraMap K (L i)) := by
      rw [← Category.assoc, hz, hem]
      exact Over.w (f (x₀ i))
    rw [← Spec.map_preimage (z i ≫ Y.hom)] at h1 ⊢
    rw [← Spec.map_comp, ← Spec.map_comp, Spec.map_inj] at h1
    congr 1
    ext a
    exact (em i).toRingHom.injective (congrArg (fun ψ => ψ.hom a) h1)
  refine ⟨Over.homMk (e.inv ≫ Sigma.desc z) ?_, fun x => ?_⟩
  · rw [Category.assoc, Iso.inv_comp_eq]
    refine Sigma.hom_ext _ _ fun i => ?_
    rw [Sigma.ι_desc_assoc]
    exact (hzw i).trans (he i).symm
  · let w : Sp (AlgebraicClosure K) ⟶ ∐ fun i => Sp (L i) := x.left ≫ e.inv
    obtain ⟨i, q, hq⟩ : ∃ (i : I) (q : Sp (L i)),
        Sigma.ι (fun i => Sp (L i)) i q = w (closedPoint (AlgebraicClosure K)) :=
      (sigmaOpenCover fun i => Sp (L i)).exists_eq _
    have hr : Set.range w ⊆ Set.range (Sigma.ι (fun i => Sp (L i)) i) := by
      rintro _ ⟨t, rfl⟩
      obtain rfl : t = closedPoint (AlgebraicClosure K) := Subsingleton.elim _ _
      exact ⟨q, hq⟩
    let v : Sp (AlgebraicClosure K) ⟶ Sp (L i) := IsOpenImmersion.lift _ w hr
    have hv : v ≫ Sigma.ι (fun i => Sp (L i)) i = w := IsOpenImmersion.lift_fac _ _ _
    have hv2 : v ≫ spMap (algebraMap K (L i)) = spMap (algebraMap K (AlgebraicClosure K)) := by
      rw [← he, ← Category.assoc, hv]
      simp only [w, Category.assoc, Iso.inv_hom_id_assoc]
      exact Over.w x
    obtain ⟨v', hv'⟩ := Spec.map_surjective v
    rw [← hv', ← Spec.map_comp, Spec.map_inj] at hv2
    let j : L i →ₐ[K] AlgebraicClosure K :=
      { v'.hom with commutes' := fun a => congrArg (fun ψ => ψ.hom a) hv2 }
    obtain ⟨σ, hσ⟩ : ∃ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, ∀ a, σ (em i a) = j a := by
      letI : Algebra (L i) (AlgebraicClosure K) := (em i).toRingHom.toAlgebra
      haveI : IsScalarTower K (L i) (AlgebraicClosure K) :=
        IsScalarTower.of_algebraMap_eq fun a => ((em i).commutes a).symm
      refine ⟨AlgEquiv.ofBijective (j.liftNormal (AlgebraicClosure K)) (AlgHom.normal_bijective K _ _ _), fun a => ?_⟩
      exact j.liftNormal_commutes (AlgebraicClosure K) a
    have hvσ : v = spMap σ.toAlgHom.toRingHom ≫ spMap (em i).toRingHom := by
      rw [← hv', ← Spec.map_comp]
      congr 1
      ext a
      exact (hσ a).symm
    have hx : x.left = spMap σ.toAlgHom.toRingHom ≫ (x₀ i).left := by
      rw [hx₀]
      erw [← Category.assoc, ← hvσ, ← Category.assoc, hv]
      simp [w]
    ext1
    rw [hf σ _ _ hx, ← hz]
    have h1 : w ≫ Sigma.desc z =
        spMap σ.toAlgHom.toRingHom ≫ spMap (em i).toRingHom ≫ z i := by
      rw [← hv, Category.assoc, Sigma.ι_desc, hvσ, Category.assoc]
    exact (Category.assoc _ _ _).symm.trans h1

end GlobalTheory.GaloisPoints
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsPullbackPow
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct

namespace GlobalTheory.ExtensionMul

section General

variable {S : Scheme.{0}} {T G B : Over S} [GrpObj T] [GrpObj G] [GrpObj B]

theorem exists_isPullback_pow [IsCommMonObj G] (i : T ⟶ G) (q : G ⟶ B) [IsMonHom i] [IsMonHom q]
    (hk : IsPullback i (toUnit _) q (η : 𝟙_ _ ⟶ B)) (N : ℕ)
    {P P' Q : Over S} {a : P ⟶ G} {b : P ⟶ B} (hP : IsPullback a b q ((𝟙 B) ^ N))
    {φ : G ⟶ P} (hφa : φ ≫ a = (𝟙 G) ^ N) (hφb : φ ≫ b = q)
    {p : P' ⟶ P} {y : P' ⟶ G} (hP' : IsPullback y p q b)
    {s : Q ⟶ P'} {r : Q ⟶ G} (hQ : IsPullback s r p φ) :
    ∃ (c : P' ⟶ T) (t : Q ⟶ T), IsPullback s t c ((𝟙 T) ^ N) := by
  have inj : ∀ {W : Over S} {x y : W ⟶ T}, x ≫ i = y ≫ i → x = y := fun h =>
    hk.hom_ext h (toUnit_unique _ _)
  have ex : ∀ {W : Over S} (x : W ⟶ G), x ≫ q = 1 → ∃ y : W ⟶ T, y ≫ i = x := fun x h =>
    ⟨hk.lift x (toUnit _) (by rw [h, Hom.one_def]), hk.lift_fst _ _ _⟩
  have hiq : i ≫ q = 1 := by rw [hk.w, Hom.one_def]
  obtain ⟨c, hc⟩ := ex ((p ≫ a) / y ^ N) (by
    rw [GrpObj.div_comp, Category.assoc, hP.w, MonObj.pow_comp, hP'.w, ← Category.assoc, MonObj.comp_pow,
      Category.comp_id, div_self'])
  have hsr : s ≫ y ≫ q = r ≫ q := by
    rw [hP'.w, ← Category.assoc, hQ.w, Category.assoc, hφb]
  have hsa : s ≫ p ≫ a = r ^ N := by
    rw [← Category.assoc, hQ.w, Category.assoc, hφa, MonObj.comp_pow, Category.comp_id]
  obtain ⟨t, ht⟩ := ex (r / (s ≫ y)) (by
    rw [GrpObj.div_comp, Category.assoc, hsr, div_self'])
  refine ⟨c, t, ⟨?_⟩, ⟨PullbackCone.isLimitAux' _ fun W => ?_⟩⟩
  · apply inj
    rw [MonObj.comp_pow, Category.comp_id, MonObj.pow_comp, ht, div_pow, Category.assoc, hc, GrpObj.comp_div, hsa,
      MonObj.comp_pow]
  · have hW : W.fst ≫ c = W.snd ^ N := by rw [W.condition, MonObj.comp_pow, Category.comp_id]
    have hl : W.fst ≫ p = ((W.snd ≫ i) * (W.fst ≫ y)) ≫ φ := by
      refine hP.hom_ext ?_ ?_
      · rw [Category.assoc, Category.assoc, hφa, MonObj.comp_pow, Category.comp_id, mul_pow,
          ← MonObj.pow_comp _ _ i, ← hW, Category.assoc, hc, GrpObj.comp_div, MonObj.comp_pow, div_mul_cancel]
      · rw [Category.assoc, Category.assoc, hφb, MonObj.mul_comp, Category.assoc, Category.assoc, hiq,
          MonObj.comp_one, _root_.one_mul, hP'.w]
    refine ⟨hQ.lift W.fst _ hl, hQ.lift_fst _ _ _, ?_, ?_⟩
    · apply inj
      change (_ ≫ t) ≫ i = _
      rw [Category.assoc, ht, GrpObj.comp_div, ← Category.assoc, hQ.lift_fst, hQ.lift_snd, mul_div_cancel_right]
    · intro (m : W.pt ⟶ Q) (h1 : m ≫ s = W.fst) (h2 : m ≫ t = W.snd)
      change m = _
      refine hQ.hom_ext (by rw [hQ.lift_fst, h1]) ?_
      rw [hQ.lift_snd, ← h1, ← h2, Category.assoc, Category.assoc, ht, GrpObj.comp_div, div_mul_cancel]

theorem of_pow_kernel (Pr : MorphismProperty Scheme.{0}) [Pr.IsStableUnderBaseChange]
    [Pr.DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact)]
    [IsCommMonObj G] (i : T ⟶ G) (q : G ⟶ B) [IsMonHom i] [IsMonHom q]
    [Surjective q.left] [Flat q.left] [QuasiCompact q.left]
    (hk : IsPullback i (toUnit _) q (η : 𝟙_ _ ⟶ B)) (N : ℕ)
    {P : Over S} {a : P ⟶ G} {b : P ⟶ B} (hP : IsPullback a b q ((𝟙 B) ^ N))
    {φ : G ⟶ P} (hφa : φ ≫ a = (𝟙 G) ^ N) (hφb : φ ≫ b = q) (h : Pr ((𝟙 T) ^ N : T ⟶ T).left) :
    Pr φ.left := by
  have hP' := IsPullback.of_hasPullback q b
  have hQ := IsPullback.of_hasPullback (pullback.snd q b) φ
  obtain ⟨c, t, H⟩ := exists_isPullback_pow i q hk N hP hφa hφb hP' hQ
  have hP'' := hP'.map (Over.forget S)
  refine MorphismProperty.of_isPullback_of_descendsAlong (P := Pr)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (hQ.map (Over.forget S)) ⟨⟨?_, ?_⟩, ?_⟩ ?_
  · exact MorphismProperty.of_isPullback (P := @Surjective) hP'' ‹_›
  · exact MorphismProperty.of_isPullback (P := @Flat) hP'' ‹_›
  · exact MorphismProperty.of_isPullback (P := @QuasiCompact) hP'' ‹_›
  · exact MorphismProperty.of_isPullback (P := Pr) (H.map (Over.forget S)).flip h

end General

theorem pow_of_isGt {S : Scheme.{0}} (E : SplitExt S) (G : Over S) [GrpObj G] [IsCommMonObj G] (hG : E.IsGt G)
    (N : ℕ) (hN : 1 ≤ N) (h1 : IsFinite ((𝟙 E.B) ^ N : E.B ⟶ E.B).left) (h2 : Flat ((𝟙 E.B) ^ N : E.B ⟶ E.B).left)
    (h3 : Surjective ((𝟙 E.B) ^ N : E.B ⟶ E.B).left) :
    IsFinite ((𝟙 G) ^ N : G ⟶ G).left ∧ Flat ((𝟙 G) ^ N : G ⟶ G).left ∧ Surjective ((𝟙 G) ^ N : G ⟶ G).left := by
  obtain ⟨D⟩ := hG
  have := D.q_hom
  have := D.i_hom
  have := D.q_flat
  have := D.q_surjective
  have := D.q_affine
  have := E.free
  have := E.finite
  have hN' : N ≠ 0 := by omega
  have hf : IsFinite (mulN (splitTorus S E.X) N).left := Diag.isFinite_mulN S E.X hN'
  have hl : Flat (mulN (splitTorus S E.X) N).left := Diag.flat_mulN S E.X hN'
  have hs : Surjective (mulN (splitTorus S E.X) N).left := Diag.surjective_mulN S E.X hN'
  rw [MulEtaleDvr.mulN_eq_pow] at hf hl hs
  have := flat_descendsAlong_fpqc
  have := isAffineHom_descendsAlong_fpqc.{0}
  have hP := IsPullback.of_hasPullback D.q ((𝟙 E.B) ^ N)
  have w : ((𝟙 G) ^ N) ≫ D.q = D.q ≫ ((𝟙 E.B) ^ N) := by
    rw [MonObj.pow_comp, MonObj.comp_pow, Category.id_comp, Category.comp_id]
  have ha := hP.lift_fst _ _ w
  have hb := hP.lift_snd _ _ w
  have a0 : Surjective (hP.lift _ _ w).left := of_pow_kernel @Surjective D.i D.q D.isKernel N hP ha hb hs
  have a1 : Flat (hP.lift _ _ w).left := of_pow_kernel @Flat D.i D.q D.isKernel N hP ha hb hl
  have a2 : IsAffineHom (hP.lift _ _ w).left :=
    of_pow_kernel @IsAffineHom D.i D.q D.isKernel N hP ha hb inferInstance
  have a3 : UniversallyClosed (hP.lift _ _ w).left :=
    of_pow_kernel @UniversallyClosed D.i D.q D.isKernel N hP ha hb inferInstance
  have a4 : LocallyOfFiniteType (hP.lift _ _ w).left :=
    of_pow_kernel @LocallyOfFiniteType D.i D.q D.isKernel N hP ha hb inferInstance
  have a5 : IsFinite (hP.lift _ _ w).left :=
    (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).mpr
      ⟨IsIntegralHom.iff_universallyClosed_and_isAffineHom.mpr ⟨a3, a2⟩, a4⟩
  have hP' := (hP.map (Over.forget S)).flip
  have b1 : IsFinite (pullback.fst D.q ((𝟙 E.B) ^ N)).left := MorphismProperty.of_isPullback (P := @IsFinite) hP' h1
  have b2 : Flat (pullback.fst D.q ((𝟙 E.B) ^ N)).left := MorphismProperty.of_isPullback (P := @Flat) hP' h2
  have b3 : Surjective (pullback.fst D.q ((𝟙 E.B) ^ N)).left :=
    MorphismProperty.of_isPullback (P := @Surjective) hP' h3
  rw [← ha, Over.comp_left]
  exact ⟨inferInstance, inferInstance, inferInstance⟩

theorem exists_represents_pow : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (D : DegPre R), ∃ (Gt : Over (Sp R)) (_ : GrpObj Gt) (_ : IsCommMonObj Gt) (Φ : ∀ T, (T ⟶ Gt) ≃ GtPt D T), GlobalTheory.TorusModel.Represents Φ ∧ Smooth Gt.hom ∧ IsSeparated Gt.hom ∧ ∀ k : ℕ, 1 ≤ k → IsFinite ((𝟙 Gt) ^ k : Gt ⟶ Gt).left ∧ Flat ((𝟙 Gt) ^ k : Gt ⟶ Gt).left ∧ Surjective ((𝟙 Gt) ^ k : Gt ⟶ Gt).left := by
  intro R _ _ _ D
  have hL := abelianSchemeLaws_all.1
  obtain ⟨H, _, _, hH⟩ := TorusModel.exists_isGt hL.globalFns (TorusModel.splitExt D)
  obtain ⟨Φ, hΦ⟩ := TorusModel.exists_points hL.globalFns hH
  refine ⟨H, inferInstance, inferInstance, Φ, hΦ,
    (UnitRigidity.smooth_geometricallyConnected_of_isGt _ H hH).1, ?_, fun k hk => ?_⟩
  · obtain ⟨d⟩ := hH
    have := d.q_affine
    have := (TorusModel.splitExt D).isAbelian.proper
    rw [← Over.w d.q]
    infer_instance
  · obtain ⟨h₁, h₂, h₃, -⟩ := hL.mulN _ D.P k hk
    exact pow_of_isGt _ H hH k hk h₁ h₂ h₃

end GlobalTheory.ExtensionMul
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaUniformisationComplexAbelianVarieties
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField in
open scoped CategoryTheory.Obj in

theorem _root_.GlobalTheory.thetaUnifAV_closed : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ThetaUnifAV := by
  have hLaws := _root_.GlobalTheory.allSixLaws.1
  exact _root_.GlobalTheory.thetaUnifAV_of_laws hLaws.cube hLaws.mulN hLaws.weil
    hLaws.weilNondeg hLaws.globalSectionsRank

end GlobalTheory
end

