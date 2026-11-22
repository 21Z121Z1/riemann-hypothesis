import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0008
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2317
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2364
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2345
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineEigenframeNearImage
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1241
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1246
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1636
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1233
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1247
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2347
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0055
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0051
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1333
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2344

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsReducedNormalModelGenericCorrespondence
section
noncomputable section

namespace GlobalTheory.UPel.HT.ES

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke

theorem isReduced_of_pReg_of_factor (p : ℕ) {Y₀ Y : Scheme.{0}} [IsReduced Y₀] (i : Y₀ ⟶ Y) [IsOpenImmersion i]
    (hp : ∀ (U : Y.Opens) (f : Γ(Y, U)), (p : Γ(Y, U)) * f = 0 → f = 0)
    (hfac : ∀ (S : Scheme.{0}) (f : S ⟶ Y), IsUnit ((p : ℕ) : Γ(S, ⊤)) → ∃ f₀ : S ⟶ Y₀, f₀ ≫ i = f) :
    IsReduced Y := by

  have haff : ∀ (V : Y.Opens), IsAffineOpen V → ∀ g : Γ(Y, V), IsNilpotent g → g = 0 := by
    intro V hV g hg
    let q : Γ(Y, V) := (p : Γ(Y, V))
    let O := Y.basicOpen q
    let ρ : Γ(Y, V) →+* Γ(Y, O) := (Y.presheaf.map (homOfLE (Y.basicOpen_le q)).op).hom
    letI : Algebra Γ(Y, V) Γ(Y, O) := ρ.toAlgebra
    haveI : IsLocalization.Away q Γ(Y, O) := hV.isLocalization_basicOpen q
    have hu : IsUnit ((p : ℕ) : Γ(O.toScheme, ⊤)) := by
      have h1 : IsUnit (algebraMap Γ(Y, V) Γ(Y, O) q) := IsLocalization.Away.algebraMap_isUnit q
      rw [map_natCast] at h1
      have := h1.map (O.topIso.inv.hom)
      rwa [map_natCast] at this
    obtain ⟨f₀, hf₀⟩ := hfac O.toScheme O.ι hu
    haveI : IsOpenImmersion (f₀ ≫ i) := hf₀ ▸ inferInstance
    haveI : IsOpenImmersion f₀ := IsOpenImmersion.of_comp f₀ i
    haveI : IsReduced O.toScheme := isReduced_of_isOpenImmersion f₀
    haveI : _root_.IsReduced Γ(Y, O) :=
      isReduced_of_injective (O.topIso.inv.hom) (O.topIso.commRingCatIsoToRingEquiv.symm.injective)
    have h0 : algebraMap Γ(Y, V) Γ(Y, O) g = 0 := (hg.map (algebraMap Γ(Y, V) Γ(Y, O))).eq_zero
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers q) _ g).1 h0
    have hk' : q ^ k * g = 0 := hk
    clear hk h0
    induction k with
    | zero => simpa using hk'
    | succ k ih => exact ih (hp V _ (by rw [pow_succ', _root_.mul_assoc] at hk'; exact hk'))
  refine ⟨fun U => ⟨fun f hf => ?_⟩⟩
  refine Y.sheaf.eq_of_locally_eq' (fun V : {V : Y.affineOpens // V.1 ≤ U} => V.1.1) U
    (fun V => homOfLE V.2) ?_ f 0 fun V => ?_
  · intro y hy
    obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVU⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hy U.isOpen
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨V, hV⟩, hVU⟩, hyV⟩
  · rw [map_zero]
    exact haff V.1.1 V.1.2 _ (hf.map _)

theorem isReduced_normalModel_of_generic : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (b : Base D R) (N : ℕ), (p : R) ∈ IsLocalRing.maximalIdeal R → ∀ (M : Model b N) (Y₀ : Scheme.{0}) (s₀ : Y₀ ⟶ M.X) (gs : Y₀ ⟶ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).toScheme), gs ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = s₀ → Etale gs → ∀ (Y : Scheme.{0}) (s : Y ⟶ M.X) (i : Y₀ ⟶ Y), IsOpenImmersion i → i ≫ s = s₀ → Flat (s ≫ M.s) → (∀ (S : Scheme.{0}) (f : S ⟶ Y), IsUnit ((p : ℕ) : Γ(S, ⊤)) → ∃ f₀ : S ⟶ Y₀, f₀ ≫ i = f) → IsReduced Y := by
  intro p _ D R _ _ _ _ b N _ M Y₀ s₀ gs hgs _ Y s i _ _ hfl hfac
  haveI := M.smooth
  haveI : Smooth M.s := SmoothOfRelativeDimension.smooth (D.a * (D.n - 1)) M.s
  haveI : IsReduced Y₀ := GlobalTheory.isReduced_of_smooth_of_isReduced (gs ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι ≫ M.s)
  have hR : ∀ a : R, (p : R) * a = 0 → a = 0 := fun a ha =>
    (mul_eq_zero.1 ha).resolve_left (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  haveI := hfl
  exact isReduced_of_pReg_of_factor p i (fun U f hf => pReg_of_flat (p := p) (s ≫ M.s) hR U f hf) hfac

end GlobalTheory.UPel.HT.ES
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularLocalRingQuotientOfDetDerivationUnit
section
open IsLocalRing TensorProduct

namespace GlobalTheory.JacobianDerivation

theorem isRegularLocalRing_quotient : ∀ (T : Type) [CommRing T] [IsRegularRing T] (h : ℕ) (f : Fin h → T)
    (D : Fin h → Derivation ℤ T T) (n : Ideal T) [n.IsPrime], (∀ j, f j ∈ n) →
    (Matrix.of fun i j => D i (f j)).det ∉ n →
    IsRegularLocalRing (Localization.AtPrime n ⧸
      (Ideal.span (Set.range f)).map (algebraMap T (Localization.AtPrime n))) := by
  intro T _ _ h f D n _ hf hdet
  classical
  let A := Localization.AtPrime n
  haveI : IsRegularLocalRing A := IsRegularRing.isRegularLocalRing_localization n
  let x : Fin h → A := fun j => algebraMap T A (f j)
  have hx : ∀ j, x j ∈ maximalIdeal A := fun j =>
    (IsLocalization.AtPrime.to_map_mem_maximal_iff A n (f j)).mpr (hf j)

  have hrow0 : ∀ a : Fin h → A, ∑ j, a j * x j ∈ maximalIdeal A ^ 2 →
      ∀ i, ∑ j, a j * algebraMap T A (D i (f j)) ∈ maximalIdeal A := by
    intro a ha i
    obtain ⟨D', hD'⟩ := @GlobalTheory.derivation_extend_localization_atPrime ℤ T A _ _ _ (Ring.toIntAlgebra T) _ (Ring.toIntAlgebra A)
      (@IsScalarTower.of_algebraMap_eq' ℤ T A _ _ _ (Ring.toIntAlgebra T) _ (Ring.toIntAlgebra A)
        (Subsingleton.elim _ _)) n _ _
      { toFun := fun t => algebraMap T A (D i t)
        map_add' := fun s t => by simp
        map_smul' := fun m t => by simp [Algebra.smul_def]
        map_one_eq_zero' := by simp
        leibniz' := fun s t => by simp [Algebra.smul_def] }
    letI : Algebra ℤ A := Ring.toIntAlgebra A
    have hsq : ∀ y ∈ maximalIdeal A ^ 2, D' y ∈ maximalIdeal A := by
      intro y hy
      rw [pow_two] at hy
      refine Submodule.mul_induction_on hy (fun a ha b hb => ?_) (fun y z hy hz => ?_)
      · rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
        exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ ha) (Ideal.mul_mem_right _ _ hb)
      · rw [map_add]; exact Ideal.add_mem _ hy hz
    have h1 := hsq _ ha
    rw [map_sum] at h1
    have h2 : ∀ j, D' (a j * x j) = a j * algebraMap T A (D i (f j)) + x j * D' (a j) := by
      intro j
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, hD']
      rfl
    simp_rw [h2, Finset.sum_add_distrib] at h1
    have h3 : ∑ j, x j * D' (a j) ∈ maximalIdeal A :=
      Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ (hx j)
    simpa using Ideal.sub_mem _ h1 h3
  have hind : ∀ a : Fin h → A, ∑ j, a j * x j ∈ maximalIdeal A ^ 2 → ∀ j, a j ∈ maximalIdeal A := by
    intro a ha
    have hrow := hrow0 a ha
    let φ : T →+* ResidueField A := (residue A).comp (algebraMap T A)
    let M : Matrix (Fin h) (Fin h) (ResidueField A) := φ.mapMatrix (Matrix.of fun i j => D i (f j))
    have hM : M.det ≠ 0 := by
      rw [← RingHom.map_det]
      intro h0
      have hu : IsUnit (algebraMap T A (Matrix.of fun i j => D i (f j)).det) :=
        (IsLocalization.AtPrime.isUnit_to_map_iff A n _).mpr hdet
      exact (residue_ne_zero_iff_isUnit _).mpr hu h0
    have hv : M.mulVec (fun j => residue A (a j)) = 0 := by
      funext i
      have := (residue_eq_zero_iff _).mpr (hrow i)
      rw [map_sum] at this
      simp only [Matrix.mulVec, dotProduct, M, RingHom.mapMatrix_apply, Matrix.map_apply,
        Matrix.of_apply, Pi.zero_apply, φ, RingHom.comp_apply]
      rw [← this]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, mul_comm]
    intro j
    have := congrFun (Matrix.eq_zero_of_mulVec_eq_zero hM hv) j
    exact (residue_eq_zero_iff _).mp this

  let τ : Fin h → maximalIdeal A := fun i => ⟨x i, hx i⟩
  have hτ : LinearIndependent (ResidueField A) (fun i => (maximalIdeal A).toCotangent (τ i)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    choose a ha using fun j => residue_surjective (g j)
    have h1 : (maximalIdeal A).toCotangent (∑ j, a j • τ j) = 0 := by
      rw [map_sum, ← hg]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, ← ha j]
      rfl
    rw [Ideal.toCotangent_eq_zero] at h1
    have h2 : ∑ j, a j * x j ∈ maximalIdeal A ^ 2 := by
      simpa [τ] using h1
    rw [← ha i]
    exact (residue_eq_zero_iff _).mpr (hind a h2 i)
  obtain ⟨J, _, t, hs, hd⟩ := GlobalTheory.RegularQuotient.exists_extend A τ hτ
  have hrange : (Set.range fun i => ((τ i : maximalIdeal A) : A)) = Set.range x := rfl
  rw [hrange] at hs
  obtain ⟨hreg, -⟩ := GlobalTheory.RegularQuotient.quot_regular A t x hs hd
  have hmap : (Ideal.span (Set.range f)).map (algebraMap T A) = Ideal.span (Set.range x) := by
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  show IsRegularLocalRing (A ⧸ (Ideal.span (Set.range f)).map (algebraMap T A))
  rw [hmap]
  exact hreg

end GlobalTheory.JacobianDerivation
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStandardSmoothLocalizationAwayJacobianDvd
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Pinch

theorem isStandardSmoothOfRelativeDimension_localizationAway_of_det_dvd
    (R ν σ : Type) [CommRing R] [Finite ν] [Fintype σ] [DecidableEq σ] (m : σ → ν)
    (hm : Function.Injective m) (F : σ → MvPolynomial ν R) (h : MvPolynomial ν R)
    (hdvd : (Matrix.of fun s t : σ ↦ MvPolynomial.pderiv (m s) (F t)).det ∣ h) :
    Algebra.IsStandardSmoothOfRelativeDimension (Nat.card ν - Nat.card σ) R
      (Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range F)) h)) := by
  classical
  set A := MvPolynomial ν R ⧸ Ideal.span (Set.range F)
  set T := Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range F)) h)
  let P := Algebra.PreSubmersivePresentation.naive (v := F) m hm
  let Q := Algebra.SubmersivePresentation.localizationAway T
    (Ideal.Quotient.mk (Ideal.span (Set.range F)) h)
  have hPjac : P.jacobian = Ideal.Quotient.mk (Ideal.span (Set.range F))
      (Matrix.of fun s t : σ ↦ MvPolynomial.pderiv (m s) (F t)).det := by
    rw [P.jacobian_eq_jacobiMatrix_det, Algebra.Generators.algebraMap_apply]
    have hM : P.jacobiMatrix = Matrix.of fun s t : σ ↦ MvPolynomial.pderiv (m s) (F t) := by
      ext i j
      simp [P]
    rw [hM]
    have : MvPolynomial.aeval P.val = Ideal.Quotient.mkₐ R (Ideal.span (Set.range F)) :=
      MvPolynomial.algHom_ext fun v => by simp [P]
    rw [this]
    rfl
  let P' : Algebra.SubmersivePresentation R T (Unit ⊕ ν) (Unit ⊕ σ) :=
    { __ := Q.toPreSubmersivePresentation.comp P
      jacobian_isUnit := by
        rw [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
          Algebra.smul_def]
        refine IsUnit.mul ?_ Q.jacobian_isUnit
        rw [hPjac]
        exact isUnit_of_dvd_unit (map_dvd _ (map_dvd _ hdvd))
          (IsLocalization.Away.algebraMap_isUnit _) }
  refine P'.isStandardSmoothOfRelativeDimension ?_
  change (Q.toPreSubmersivePresentation.comp P).dimension = _
  rw [Algebra.PreSubmersivePresentation.dimension_comp_eq_dimension_add_dimension]
  simp [Algebra.Presentation.dimension, P]

end GlobalTheory.Pinch
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaEq
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Obs

theorem isTheta_eq {R R₀ B B₀ B' : Type} [CommRing R] [CommRing R₀] [CommRing B] [Algebra R B] [CommRing B₀]
    [Algebra R₀ B₀] [CommRing B'] [Algebra R B'] {I : Ideal R} {p : B →+* B₀} (hp : Function.Surjective p)
    {α β : B →ₐ[R] B'} {θ₁ θ₂ : Ω[B₀⁄R₀] →+ B'} (h₁ : IsTheta I p α β θ₁) (h₂ : IsTheta I p α β θ₂) :
    θ₁ = θ₂ := by
  ext w
  have hw : w ∈ Submodule.span B₀ (Set.range (D R₀ B₀)) := by
    rw [span_range_derivation]; trivial
  refine Submodule.span_induction (p := fun z _ ↦ θ₁ z = θ₂ z) ?_ ?_ ?_ ?_ hw
  · rintro z ⟨y, rfl⟩
    obtain ⟨b, rfl⟩ := hp y
    rw [h₁.der, h₂.der]
  · rw [map_zero, map_zero]
  · intro y z _ _ hy hz; rw [map_add, map_add, hy, hz]
  · intro c z _ hz
    obtain ⟨b, rfl⟩ := hp c
    rw [h₁.smul, h₂.smul, hz]

theorem isSig_eq {R R₀ R₁ : Type} [CommRing R] [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] {I : Ideal R}
    {π : R →+* R₀} (α : Aug I π R₁) {B B₀ : Type} [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀]
    {p : B →+* B₀} (hp : Function.Surjective p) {σ σ' : R₁ ⊗[R₀] B₀ →+ B} (h : α.IsSig p σ) (h' : α.IsSig p σ') :
    σ = σ' := by
  ext x
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul y x =>
    obtain ⟨b, rfl⟩ := hp x
    rw [h, h']
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem isOb2_add : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (w w' : Glob1 F) (c c' : GlobalTheory.CatCoh.H2 (ext R₁ F)), L.IsOb2 α w c → L.IsOb2 α w' c' → L.IsOb2 α (w + w') (c + c') := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α C _ F L w w' c c' h h'
  obtain ⟨θ, σ, z, hθ, hσ, rfl, hz⟩ := h
  obtain ⟨θ', σ', z', hθ', hσ', rfl, hz'⟩ := h'
  refine ⟨θ, σ, z + z', hθ, hσ, (map_add _ _ _).symm, fun T T' T'' a b ↦ ?_⟩
  have eθ : θ T T' T'' a b = θ' T T' T'' a b := isTheta_eq (L.surj T) (hθ T T' T'' a b) (hθ' T T' T'' a b)
  have eσ : σ T'' = σ' T'' := isSig_eq α (L.surj T'') (hσ T'') (hσ' T'')
  obtain ⟨k₁, s₁⟩ := hz T T' T'' a b
  obtain ⟨k₂, s₂⟩ := hz' T T' T'' a b
  have ez : (z + z').1 T T' T'' a b = z.1 T T' T'' a b + z'.1 T T' T'' a b := rfl
  refine ⟨?_, ?_⟩
  · unfold Aug.KerQ at k₁ k₂ ⊢
    rw [ez, map_add, k₁, k₂, add_zero]
  · rw [ez, map_add, s₁, eσ, s₂, ← eθ]
    exact (map_add (θ T T' T'' a b) (w.1 T) (w'.1 T)).symm

end GlobalTheory.Obs
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetFrameEigenbasisBlockAtPoint
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole

namespace GlobalTheory.LogPole

attribute [local instance] Over.cartesianMonoidalCategory Over.braidedCategory

open MonObj in

theorem isUnit_det_of_isCombAtG_vecAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (k : TF.X.F.J) (S : Type) [CommRing S] (z : Sp S ⟶ Y₀ TF.X Z) (hU : ⊤ ≤ (z ≫ toBase TF Z) ⁻¹ᵁ U.1) (hk : ⊤ ≤ (z ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U k) (hx : (z ≫ inc₀ TF.X Z) ≫ TF.X.π = z ≫ toBase TF Z) (σ : E →+* ℂ) (C : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S), (∀ i : Fin (Dw.mult σ), IsCombAtG TF.Y.t (z ≫ toBase TF Z) (fun j => spMap (dualMap (ev (z ≫ toBase TF Z) U.1 hU)) ≫ v (e ⟨σ, j⟩)) (C i) (tv (TF.X.F.vecAt k (z ≫ inc₀ TF.X Z) hk hx σ i)).left) → IsUnit C.det := by
  intro E _ _ _ H Dw l Xo c TF Z U n e v hv k S _ z hU hk hx σ C hC
  have hxU : spMap (ev (z ≫ toBase TF Z) U.1 hU) ≫ LogKS.chart U = z ≫ toBase TF Z :=
    FlagMod.spMap_ev (z ≫ toBase TF Z) U.2 hU
  have htan : ∀ j, IsTanAtG TF.Y.t (z ≫ toBase TF Z)
      (spMap (dualMap (ev (z ≫ toBase TF Z) U.1 hU)) ≫ v (e ⟨σ, j⟩)) := fun j => by
    have := GlobalTheory.FactorDepth.isTanAtG_map TF.Y.t (ev (z ≫ toBase TF Z) U.1 hU) (hv.1 (e ⟨σ, j⟩))
    rwa [hxU] at this
  choose B hB using fun j => GlobalTheory.FlagEmb.EigSpread.exists_lf (htan j)
  have hsum : ∀ i, ∑ j, C i j • B j = TF.X.F.vecAt k (z ≫ inc₀ TF.X Z) hk hx σ i := fun i => by
    have h := hC i
    simp only [← hB] at h
    exact (GlobalTheory.FlagEmb.EigSpread.comb_lf B (C i) _).1 h
  obtain ⟨Wm, hW⟩ := TF.X.F.uAt_split k (z ≫ inc₀ TF.X Z) hk σ
  let ρ := (Matrix.mulVecLin Wm).comp
    (FlagMod.vec (TF.X.F.M k).toMChart (z ≫ toBase TF Z) (TF.X.F.inM hk hx)).symm.toLinearMap
  have hρ : ∀ i, ρ (TF.X.F.vecAt k (z ≫ inc₀ TF.X Z) hk hx σ i) = Pi.single i 1 := fun i => by
    funext l
    have h := congrFun (congrFun hW l) i
    rw [Matrix.mul_apply] at h
    simp only [ρ, FlagMod.Frames.vecAt, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
    rw [h, Matrix.one_apply, Pi.single_apply]
  let B' : Fin (Dw.mult σ) → ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM (z ≫ toBase TF Z) TF.Y.t.G := fun j => B j
  have hsum' : ∀ i, ∑ j, C i j • B' j = TF.X.F.vecAt k (z ≫ inc₀ TF.X Z) hk hx σ i := hsum
  let D : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S := Matrix.of fun j l => ρ (B' j) l
  have hCD : C * D = 1 := by
    ext i l
    have h : ρ (∑ j, C i j • B' j) = ρ (TF.X.F.vecAt k (z ≫ inc₀ TF.X Z) hk hx σ i) := congrArg ρ (hsum' i)
    rw [hρ, map_sum] at h
    have h2 := congrFun h l
    simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h2
    have h3 : (if i = l then (1 : S) else 0) = (Pi.single i (1 : S) : Fin (Dw.mult σ) → S) l := by
      rw [Pi.single_apply]
      exact if_congr eq_comm rfl rfl
    rw [Matrix.mul_apply, Matrix.one_apply, h3]
    exact h2
  exact IsUnit.of_mul_eq_one D.det (by rw [← Matrix.det_mul, hCD, Matrix.det_one])

end GlobalTheory.LogPole
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogTarget
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

noncomputable section

namespace GlobalTheory.UPel.HT.ES.CorrQF

def IsogTarget {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    (M : Model b N) (c : ℕ) {L : Type} [Field L] (ξ ζ : Sp L ⟶ M.X) : Prop :=
  ξ ≫ M.s = ζ ≫ M.s ∧ ∃ (o o' : Obj b N (ξ ≫ M.s)) (ψ : o.A ⟶ o'.A),
    Nonempty (ObjMap o M.univ ξ) ∧ Nonempty (ObjMap o' M.univ ζ) ∧ IsPIsog c o o' ψ

end GlobalTheory.UPel.HT.ES.CorrQF
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KawamataViehwegOfNadelVanishingPair
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh

namespace GlobalTheory.KVFromPair

theorem subsingleton_coh_twist (hN : GlobalTheory.Published.NefNumerics) (hV : GlobalTheory.Published.NadelVanishingPair)
    (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (X : Scheme.{0}) [IsIntegral X]
    (p : X ⟶ Sp k) (D : ℕ) [hs : SmoothOfRelativeDimension D p] (hp : IsProjOver p)
    (K : CanonLB p D) (N : LB X) (h₁ : letI := algebraΓOfHom p; IsNef k N)
    (h₂ : letI := algebraΓOfHom p; IsBig k N) (q : ℕ) (hq : 0 < q) :
    Subsingleton (coh (twist (GlobalTheory.structureModule X) (tens K.bundle N)) q) := by
  have hNl : N.IsLB := by
    letI := algebraΓOfHom p
    exact h₁.isLB
  obtain ⟨K₁, X₁, p₁, ψ, L₁, hc, hp₁, H, hL₁, e⟩ := GlobalTheory.T.projectiveLineBundle_descends_to_countable_subfield k X p hp N hNl
  have hsm : Smooth p := SmoothOfRelativeDimension.smooth D p
  have hg : GeometricallyConnected p := GlobalTheory.geometricallyConnected_of_isAlgClosed p
  obtain ⟨hs₁, hg₁⟩ := GlobalTheory.T.smoothOfRelDim_geomConnected_descend_fieldExtension K₁ k X₁ X p₁ p ψ H D inferInstance hs hg
  have hne : Nonempty X₁ := ⟨ψ (Classical.arbitrary X)⟩
  have hP := LB.isLB_pull hL₁ ψ
  have ec : cls N hNl = cls (L₁.pull ψ) hP := (cls_eq_iff _ _).2 e
  have n₁ := GlobalTheory.T.isNefLineBundle_of_baseChange_field K₁ k X₁ X p₁ p ψ H hp₁ L₁ hL₁ (by
    letI := algebraΓOfHom p
    exact h₁.of_cls_eq hP ec.symm)
  have b₁ := (GlobalTheory.T.isBigLineBundle_pullback_fieldExtension_iff K₁ k X₁ X p₁ p ψ H hp₁ hp
    ((GlobalTheory.HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth p D hs).trans
      (GlobalTheory.HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth p₁ D hs₁).symm) L₁ hL₁).1 (by
    letI := algebraΓOfHom p
    exact h₂.of_cls_eq hP ec.symm)
  let C : CanonLB p₁ D := CanonLB.all p₁ D
  have v₁ := GlobalTheory.T.kawamataViehweg_vanishing_complexEmbeddedField hN hV K₁ (GlobalTheory.KeyHouse.nonempty_ringHom_complex K₁) X₁ p₁ D hp₁ hg₁
    C L₁ n₁ b₁ q hq
  have hT := isLB_tens C.isLB hL₁
  have v := (GlobalTheory.T.subsingleton_lineBundleCohomology_projBaseChange_iff K₁ k X₁ X p₁ p ψ H hp₁ hp _ hT q).2 v₁
  have eK : cls K.bundle K.isLB = cls (C.bundle.pull ψ) (LB.isLB_pull C.isLB ψ) := by
    obtain ⟨w, hw, -⟩ := canonLB_baseChange K₁ k _ X₁ X p₁ p ψ D H C K
    exact (cls_eq_iff _ _).2 ⟨w, hw⟩
  obtain ⟨i⟩ := nonempty_twist_iso_of_cls_eq (GlobalTheory.structureModule X) (isLB_tens K.isLB hNl)
    (LB.isLB_pull hT ψ) (by
      rw [cls_tens K.isLB hNl, cls_pull hT, cls_tens C.isLB hL₁, map_add, eK, ec,
        cls_pull C.isLB, cls_pull hL₁])
  exact (cohOn.mapIso Γ(X, ⊤) ⊤ q i).toEquiv.subsingleton_congr.2 v

theorem kawamataViehweg_of_nadelVanishingPair :
    GlobalTheory.Published.NefNumerics → GlobalTheory.Published.NadelVanishingPair → GlobalTheory.Published.KawamataViehweg := by
  intro hN hV k _ _ _ X a _ D hs hp K N h₁ h₂ q hq
  have ha : a = algebraΓOfHom (strHom k X) := Algebra.algebra_ext _ _ (algebraMap_eq_strHom k X)
  have v := subsingleton_coh_twist hN hV k X (strHom k X) D hp K N (ha ▸ h₁) (ha ▸ h₂) q hq
  exact (cohOn.mapIso Γ(X, ⊤) ⊤ q (Twist.unitTwistIso _)).toEquiv.subsingleton_congr.1 v

end GlobalTheory.KVFromPair
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelActionIsPullbackProdMapTorsor
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer

namespace GlobalTheory.CharKer

variable {S : Scheme.{0}}

theorem comp_one_hom {X Y M : Over S} [GrpObj M] (u : Y ⟶ X) : u ≫ (1 : X ⟶ M) = 1 := by
  rw [Hom.one_def, Hom.one_def, ← Category.assoc, toUnit_unique (u ≫ toUnit X) (toUnit Y)]

theorem pmap_isPullback_actMap : ∀ (S : Scheme.{0}) (A A' N T : Over S) [GrpObj A] [GrpObj A'] [GrpObj N] (i : N ⟶ A) (q : A ⟶ A'), IsMonHom i → IsMonHom q → IsPullback i (toUnit N) q η[A'] → IsPullback (prMap A N T) (actMap i T) (pmap q T) (pmap q T) := by
  intro S A A' N T _ _ _ i q hi hq hker
  have hiq : i ≫ q = 1 := by rw [hker.w, Hom.one_def]
  have hpf : pmap q T ≫ fst A' T = fst A T ≫ q := by simp [pmap]
  have hps : pmap q T ≫ snd A' T = snd A T := by simp [pmap]
  have hc : prMap A N T ≫ pmap q T = actMap i T ≫ pmap q T := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, Category.assoc, hpf]
      simp only [prMap, actMap, lift_fst_assoc, mul_comp, Category.assoc, hiq]
      simp only [comp_one_hom, _root_.mul_one]
    · rw [Category.assoc, Category.assoc, hps]
      simp [prMap, actMap]
  have hfs : ∀ s : PullbackCone (pmap q T) (pmap q T), (s.fst ≫ fst A T) ≫ q = (s.snd ≫ fst A T) ≫ q := by
    intro s
    have h := congrArg (· ≫ fst A' T) s.condition
    simp only [Category.assoc, hpf] at h
    simpa only [Category.assoc] using h
  have hss : ∀ s : PullbackCone (pmap q T) (pmap q T), s.fst ≫ snd A T = s.snd ≫ snd A T := by
    intro s
    have h := congrArg (· ≫ snd A' T) s.condition
    simpa only [Category.assoc, hps] using h
  have hk : ∀ s : PullbackCone (pmap q T) (pmap q T),
      ((s.fst ≫ fst A T)⁻¹ * (s.snd ≫ fst A T)) ≫ q = toUnit s.pt ≫ η[A'] := by
    intro s
    rw [mul_comp, GrpObj.inv_comp, hfs s, _root_.inv_mul_cancel, Hom.one_def]
  refine ⟨⟨hc⟩, ⟨PullbackCone.IsLimit.mk hc
    (fun s => lift (s.fst ≫ fst A T)
      (lift (hker.lift ((s.fst ≫ fst A T)⁻¹ * (s.snd ≫ fst A T)) (toUnit _) (hk s)) (s.fst ≫ snd A T)))
    ?_ ?_ ?_⟩⟩
  · intro s
    apply CartesianMonoidalCategory.hom_ext <;> simp [prMap]
  · intro s
    apply CartesianMonoidalCategory.hom_ext
    · simp only [actMap, Category.assoc, lift_fst, comp_mul, lift_fst_assoc, lift_snd_assoc, hker.lift_fst]
      exact _root_.mul_inv_cancel_left _ _
    · simp [actMap, hss]
  · intro s m h1 h2
    have ha : m ≫ fst A (N ⊗ T) = s.fst ≫ fst A T := by rw [← h1]; simp [prMap]
    have ht : m ≫ snd A (N ⊗ T) ≫ snd N T = s.fst ≫ snd A T := by rw [← h1]; simp [prMap]
    have hb : m ≫ fst A (N ⊗ T) * m ≫ snd A (N ⊗ T) ≫ fst N T ≫ i = s.snd ≫ fst A T := by
      rw [← h2]; simp [actMap, comp_mul]
    apply CartesianMonoidalCategory.hom_ext
    · simpa using ha
    · apply CartesianMonoidalCategory.hom_ext
      · apply hker.hom_ext
        · simp only [Category.assoc, lift_snd_assoc, lift_fst_assoc, hker.lift_fst]
          rw [← ha]
          exact eq_inv_mul_of_mul_eq hb
        · exact toUnit_unique _ _
      · simpa using ht

end GlobalTheory.CharKer
end

