import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0174
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0136
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0019
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0114
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0114
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0034
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0176
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0124
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0175
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0138
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0152
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0155

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleExtendedPrincipalPolarisationDvr
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.ExtAmple

theorem lbIso_self {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) : LBIso L L := by
  refine ⟨⟨fun p => L.g p.1 p.2⟩, fun p q => unit_ext fun y hy => ?_⟩
  refine (gm_res _ y _ hy _).trans (Eq.symm ((map_mul _ _ _).trans ((congrArg₂ (· * ·)
    (gm_div L L (𝟙 X) y p q hy) (gm_res _ y _ hy _)).trans ?_)))
  have a := gm_cocycle hL (𝟙 X) y hy.1.1 hy.2.1 hy.2.2
  have b := gm_cocycle hL (𝟙 X) y hy.1.1 hy.1.2 hy.2.2
  show gm (𝟙 X) y _ (L.g p.1 q.1) * (gm (𝟙 X) y _ (L.g p.2 q.2))⁻¹ * gm (𝟙 X) y _ (L.g q.1 q.2) =
    gm (𝟙 X) y _ (L.g p.1 p.2)
  rw [mul_right_comm, a, ← b, mul_inv_cancel_right]

theorem relAmple_pullback_of_fac {S S₀ T : Scheme.{0}} [IsAffine S₀] {B : Over S} {A : Over S₀} {L : LB B.left}
    {L₀ : LB A.left} (hL : L.IsLB) (hL₀ : L₀.IsLB) {g : S₀ ⟶ S} {φ : A.left ⟶ B.left}
    (h : IsPullback φ A.hom B.hom g) (e : LBIso L₀ (L.pull φ)) (hA : RelAmple A L₀) (y : T ⟶ S₀) :
    RelAmple ((Over.pullback (y ≫ g)).obj B) (L.pull (pullback.fst B.hom (y ≫ g))) := by
  let ψ : pullback B.hom (y ≫ g) ⟶ A.left :=
    h.lift (pullback.fst B.hom (y ≫ g)) (pullback.snd B.hom (y ≫ g) ≫ y) (by rw [Category.assoc]; exact pullback.condition)
  have hψ : ψ ≫ φ = pullback.fst B.hom (y ≫ g) := h.lift_fst _ _ _
  have H : IsPullback ψ (pullback.snd B.hom (y ≫ g)) A.hom y := by
    refine IsPullback.of_right ?_ (h.lift_snd _ _ _) h
    rw [hψ]
    exact IsPullback.of_hasPullback _ _
  obtain ⟨w, hw⟩ : LBIso (L.pull (pullback.fst B.hom (y ≫ g))) (L₀.pull ψ) :=
    LBIso.chartPull
      (chartPullSame L (fun _ : PUnit => pullback.fst B.hom (y ≫ g)) (fun _ => φ) (fun _ => 1) ψ fun _ => hψ.symm)
      (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull L₀ _ _ rfl) (LBIso.symm e)
  exact relAmple_pull (A' := (Over.pullback (y ≫ g)).obj B) H hL₀ (pull_isLB hL _)
    ((isGen_iff w).1 hw) ⊤ (isAffineOpen_top _) (fun _ => trivial) hA

theorem fac_or_fac (V K k : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
    [IsFractionRing V K] [Field k] (f : V →+* k) :
    (∃ g : K →+* k, f = g.comp (algebraMap V K)) ∨
      ∃ g : IsLocalRing.ResidueField V →+* k, f = g.comp (IsLocalRing.residue V) := by
  by_cases hf : RingHom.ker f = ⊥
  · have hi : Function.Injective f := (RingHom.injective_iff_ker_eq_bot f).2 hf
    exact Or.inl ⟨IsFractionRing.lift hi, RingHom.ext fun x => (IsFractionRing.lift_algebraMap hi x).symm⟩
  · have hm : (RingHom.ker f).IsMaximal := (RingHom.ker_isPrime f).isMaximal hf
    have he := IsLocalRing.eq_maximalIdeal hm
    exact Or.inr ⟨Ideal.Quotient.lift _ f (fun a ha => by rw [← he] at ha; exact ha), RingHom.ext fun x => rfl⟩

theorem relAmple_extension : Laws → Laws2 → ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (P : PolAV (Sp K)) (B : Over (Sp V)) [GrpObj B] [IsCommMonObj B] (M : GlobalTheory.UU.CP B) (φ : P.A.left ⟶ B.left), IsAbelianScheme B → IsGrpPullback P.A B (spMap (algebraMap V K)) φ → LBIso P.L (M.L.L.pull φ) → IsAdicComplete (IsLocalRing.maximalIdeal V) V → RelAmple B M.L.L := by
  intro h₁ h₂ V K _ _ _ _ _ _ P B _ _ M φ hB hφ e hc
  refine GlobalTheory.T.cubical_bundle_relAmple_of_ample_fibres h₁ h₂ V hc B hB M fun k _ x => ?_
  obtain ⟨f, rfl⟩ := Spec.map_surjective x
  rcases fac_or_fac V K k f.hom with ⟨g, hg⟩ | ⟨g, hg⟩
  · have hx : Spec.map f = spMap g ≫ spMap (algebraMap V K) := by
      rw [← Spec.map_comp]; congr 1; exact CommRingCat.hom_ext hg
    rw [hx]
    exact relAmple_pullback_of_fac M.L.isLB P.isLB hφ.1 e P.ample _
  · have hx : Spec.map f = spMap g ≫ spMap (IsLocalRing.residue V) := by
      rw [← Spec.map_comp]; congr 1; exact CommRingCat.hom_ext hg
    rw [hx]
    exact relAmple_pullback_of_fac (A := (Over.pullback (spMap (IsLocalRing.residue V))).obj B) M.L.isLB
      (pull_isLB M.L.isLB _) (IsPullback.of_hasPullback _ _) (lbIso_self (pull_isLB M.L.isLB _))
      (GlobalTheory.T.relAmple_specialFibre_extended_principalPolarisation h₁ h₂ V K P B M φ hB hφ e hc) _

end GlobalTheory.ExtAmple
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfAmpleGeometricFibresAbelianScheme
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.FibreAmple

variable {S X T₁ T₂ X₁ X₂ : Scheme.{0}} {f : X ⟶ S} {M : LB X} {π₁ : X₁ ⟶ X} {f₁ : X₁ ⟶ T₁} {t₁ : T₁ ⟶ S}
  {π₂ : X₂ ⟶ X} {f₂ : X₂ ⟶ T₂} {t₂ : T₂ ⟶ S}

theorem exists_isPullback (h₁ : IsPullback π₁ f₁ f t₁) (h₂ : IsPullback π₂ f₂ f t₂) (u : T₂ ⟶ T₁)
    (hu : u ≫ t₁ = t₂) : ∃ φ : X₂ ⟶ X₁, π₂ = φ ≫ π₁ ∧ IsPullback φ f₂ f₁ u := by
  have w : π₂ ≫ f = (f₂ ≫ u) ≫ t₁ := by rw [Category.assoc, hu, h₂.w]
  refine ⟨h₁.lift _ _ w, (h₁.lift_fst _ _ _).symm, IsPullback.of_right ?_ (h₁.lift_snd _ _ _) h₁⟩
  rw [h₁.lift_fst, hu]
  exact h₂

theorem lbIso_pull_comp {φ : X₂ ⟶ X₁} (hφ : π₂ = φ ≫ π₁) {L₁ : LB X₁} (e : LBIso L₁ (M.pull π₁)) :
    LBIso (M.pull π₂) (L₁.pull φ) :=
  LBIso.chartPull (chartPullSame M (fun _ : PUnit => π₂) (fun _ => π₁) (fun _ => 1) φ fun _ => hφ)
    (Geo.Tor.chartPullPull L₁ φ φ rfl) e.symm

theorem lbIso_pull_pull (hM : M.IsLB) (φ : X₂ ⟶ X₁) (π₁ : X₁ ⟶ X) :
    LBIso ((M.pull π₁).pull φ) (M.pull (φ ≫ π₁)) :=
  (lbIso_pull_comp rfl (GlobalTheory.lbIso_refl (pull_isLB hM π₁))).symm

theorem relAmple_of_factor [IsProper f] (hM : M.IsLB) (h₁ : IsPullback π₁ f₁ f t₁) (h₂ : IsPullback π₂ f₂ f t₂)
    (u : T₂ ⟶ T₁) (hu : u ≫ t₁ = t₂) {L₁ : LB X₁} (hL₁ : L₁.IsLB) (e : LBIso L₁ (M.pull π₁))
    (hA : Out.RelAmple (Over.mk f₁) L₁) : Out.RelAmple (Over.mk f₂) (M.pull π₂) := by
  obtain ⟨φ, hφ, H⟩ := exists_isPullback h₁ h₂ u hu
  have hp : IsProper (Over.mk f₂).hom := MorphismProperty.of_isPullback (P := @IsProper) h₂ ‹_›
  refine AmpleLocal.relAmple_of_locally T₂ (Over.mk f₂) (M.pull π₂) (pull_isLB hM π₂)
    inferInstance inferInstance fun s => ?_
  obtain ⟨V, hV, hs, -⟩ := exists_isAffineOpen_mem_and_subset (X := T₁) (U := ⊤) (x := u s) trivial
  exact ⟨u ⁻¹ᵁ V, hs, PolPull.relAmple_restrict (G := Over.mk f₁) (G' := Over.mk f₂) H hL₁ (pull_isLB hM π₂)
    (lbIso_pull_comp hφ e) hA V hV⟩

theorem relAmple_of_fieldExtension [IsProper f] (hM : M.IsLB) {K₀ K : Type} [Field K₀] [Field K] (i : K₀ →+* K)
    {f₁ : X₁ ⟶ Sp K₀} {t₁ : Sp K₀ ⟶ S} {f₂ : X₂ ⟶ Sp K} (h₁ : IsPullback π₁ f₁ f t₁)
    (h₂ : IsPullback π₂ f₂ f (spMap i ≫ t₁)) {L₁ : LB X₁} (hL₁ : L₁.IsLB) (e : LBIso L₁ (M.pull π₁))
    (hA : Out.RelAmple (Over.mk f₂) (M.pull π₂)) : Out.RelAmple (Over.mk f₁) L₁ := by
  obtain ⟨φ, hφ, H⟩ := exists_isPullback h₁ h₂ _ rfl
  have : Subsingleton (Spec (CommRingCat.of K₀)) := inferInstanceAs (Subsingleton (PrimeSpectrum K₀))
  have : Nonempty (Spec (CommRingCat.of K)) := inferInstanceAs (Nonempty (PrimeSpectrum K))
  have : Flat (Out.specOf i) := inferInstance
  have : Surjective (Out.specOf i) := inferInstance
  have hp : IsProper f₁ := MorphismProperty.of_isPullback (P := @IsProper) h₁ ‹_›
  have : IsProper (Over.mk f₁).hom := hp
  have : IsProper f₂ := MorphismProperty.of_isPullback (P := @IsProper) h₂ ‹_›
  have : CompactSpace X₁ := QuasiCompact.compactSpace_of_compactSpace f₁
  have : QuasiSeparatedSpace X₁ := quasiSeparatedSpace_of_quasiSeparated f₁
  refine (relAmple_iff_isAmpleLB_of_isAffine (Over.mk f₁) hL₁).2 (AmpleDescent.isAmpleLB_of_pull i H hL₁ ?_)
  exact (isAmpleLB_of_relAmple_of_isAffine (Over.mk f₂) (pull_isLB hM π₂) hA).of_lbIso (LB.isLB_pull hL₁ φ)
    (lbIso_pull_comp hφ e).symm

theorem residueField_fraction {R : Type} [CommRing R] (p : Ideal R) [p.IsPrime] (y : p.ResidueField) :
    ∃ a b : R, algebraMap R p.ResidueField b ≠ 0 ∧
      y * algebraMap R p.ResidueField b = algebraMap R p.ResidueField a := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R ⧸ p) y
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  have hb' : algebraMap (R ⧸ p) p.ResidueField (Ideal.Quotient.mk p b) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  exact ⟨a, b, hb', div_mul_cancel₀ _ hb'⟩

theorem relAmple_of_geometricFibres : Out.Laws → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → (∀ (K : Type) [Field K] [IsAlgClosed K] (y : Sp K ⟶ S), Out.RelAmple (Over.mk (pullback.snd P.A.hom y)) (M.pull (pullback.fst P.A.hom y))) → Out.RelAmple P.A M := by
  intro _ S _ P M hM hfib
  have := P.isAb.proper
  have := P.isAb.smooth
  refine AmpleLocal.relAmple_of_locally S P.A M hM inferInstance inferInstance fun s => ?_
  obtain ⟨V, hV, hs, -⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := ⊤) (x := s) trivial
  have : IsNoetherianRing Γ(S, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  let t : Spec (CommRingCat.of Γ(S, V)) ⟶ S := hV.fromSpec
  obtain ⟨p, hp⟩ : s ∈ Set.range t := by rw [hV.range_fromSpec]; exact hs
  have hB := IsPullback.of_hasPullback P.A.hom t
  have hL := pull_isLB hM (pullback.fst P.A.hom t)
  have := p.isPrime
  let g := algebraMap Γ(S, V) p.asIdeal.ResidueField
  let i := algebraMap p.asIdeal.ResidueField (AlgebraicClosure p.asIdeal.ResidueField)
  obtain ⟨r, hr, hA⟩ := GlobalTheory.T.relAmple_near_fibre_flat_projective Γ(S, V) (Over.mk (pullback.snd P.A.hom t)) (M.pull (pullback.fst P.A.hom t))
    (inferInstanceAs (Flat (pullback.snd P.A.hom t)))
    (AmpleBaseChange.isProjBy_smooth_isProper_geometricallyIntegral S P.A P.L P.isAb P.isLB P.ample _ t _ _ _ hB).1
    hL _ g (residueField_fraction p.asIdeal)
    (relAmple_of_fieldExtension hM i
      ((IsPullback.of_hasPullback (pullback.snd P.A.hom t) (spMap g)).paste_horiz hB)
      (IsPullback.of_hasPullback P.A.hom _) (pull_isLB hL _) (lbIso_pull_pull hM _ _) (hfib _ _))
  let D : (Spec (CommRingCat.of Γ(S, V))).Opens := PrimeSpectrum.basicOpen r
  have hD : p ∈ D := fun h => hr (Ideal.algebraMap_residueField_eq_zero.2 h)
  have hrange : Set.range (t ''ᵁ D).ι ⊆ Set.range (D.ι ≫ t) := by
    rintro _ ⟨⟨_, x, hx, rfl⟩, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  refine ⟨t ''ᵁ D, ⟨p, hD, hp⟩, ?_⟩
  exact relAmple_of_factor hM ((IsPullback.of_hasPullback (pullback.snd P.A.hom t) D.ι).paste_horiz hB)
    (isPullback_morphismRestrict P.A.hom (t ''ᵁ D)).flip (IsOpenImmersion.lift (D.ι ≫ t) _ hrange)
    (IsOpenImmersion.lift_fac _ _ _) (pull_isLB hL _) (lbIso_pull_pull hM _ _) hA

end GlobalTheory.FibreAmple
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SeesawTrivialityOnDenseFibresProductAbelianStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seesaw_triviality_on_dense_fibres_product_abelian : Out.GlobalFnsSt → ∀ (k : Type) [Field k] [IsAlgClosed k] (A B : Over (Sp k)) [GrpObj A] [GrpObj B] (N : LB (A ⊗ B).left) (M : LB B.left), IsAbelianScheme A → IsAbelianScheme B → M.IsLB → Out.RelAmple B M → N.IsLB → (∃ t : (N.pull (lift (1 : B ⟶ A) (𝟙 B)).left).Gen, t.IsGen) → Dense (⋃ x ∈ {x : 𝟙_ (Over (Sp k)) ⟶ A | ∃ t : (N.pull (lift (toUnit B ≫ x) (𝟙 B)).left).Gen, t.IsGen}, Set.range x.left) → (∃ t : (N.pull (lift (𝟙 A) (1 : A ⟶ B)).left).Gen, t.IsGen) → ∃ t : N.Gen, t.IsGen := by
  first | exact @GlobalTheory.triv_of_triv_on_dense_fibres_prod_abelian | exact GlobalTheory.triv_of_triv_on_dense_fibres_prod_abelian | (intros; apply GlobalTheory.triv_of_triv_on_dense_fibres_prod_abelian <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TheoremOfCubePolAbelianSchemeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theorem_of_cube_polAbelianScheme : ∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen := by
  first | exact @GlobalTheory.Moduli.cube_of_isLB | exact GlobalTheory.Moduli.cube_of_isLB | (intros; apply GlobalTheory.Moduli.cube_of_isLB <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaConstantsSatisfyClosureEquationsOfDenseClas
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM

theorem eval₂_mul_eq_zero_of_complex {o K₀ K σ : Type} [CommRing o] [Field K₀] [CommRing K] (β : o →+* K₀)
    (i : K₀ →+* K) (j : K₀ →+* ℂ) (v : σ → K₀) (F : MvPolynomial σ o)
    (h : ∀ c : ℂ, c ≠ 0 → MvPolynomial.eval₂ (j.comp β) (fun a => c * j (v a)) F = 0) (u : K) :
    MvPolynomial.eval₂ (i.comp β) (fun a => u * i (v a)) F = 0 := by
  let P : Polynomial K₀ :=
    MvPolynomial.eval₂ (Polynomial.C.comp β) (fun a => Polynomial.X * Polynomial.C (v a)) F
  have key : ∀ {E : Type} [CommRing E] (k : K₀ →+* E) (c : E),
      Polynomial.eval₂RingHom k c P = MvPolynomial.eval₂ (k.comp β) (fun a => c * k (v a)) F := by
    intro E _ k c
    simp only [P]
    rw [MvPolynomial.hom_eval₂]
    congr 1
    · ext r
      simp
    · funext a
      rw [map_mul]
      simp
  have hP : P.map j = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot _ ((Set.finite_singleton (0 : ℂ)).infinite_compl.mono fun c hc => ?_)
    change (P.map j).eval c = 0
    rw [Polynomial.eval_map]
    exact (key j c).trans (h c hc)
  rw [Polynomial.map_eq_zero] at hP
  rw [← key, hP, map_zero]

theorem TObj.exists_hasTh_field (hL : Out.Laws) (hL2 : Out.Laws2) {o : Type} [CommRing o] {g N' : ℕ} {J : Type}
    {b : TBase o (N' ^ 2)} {K : Type} [Field K] {s : Sp K ⟶ Sp o} (t : TObj g (N' ^ 2) J b s) (hN : Odd N') :
    ∃ v : Ix g (N' ^ 2) → K, t.HasTh (𝟙 _) v := by
  obtain ⟨R, _, x, v, hx, ⟨p, hp⟩, hth⟩ := GlobalTheory.ThetaLocal.exists_hasTh hL hL2 o g N' J b _ s t hN
    (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K)
  have hr : Set.range (𝟙 (Sp K) : Sp K ⟶ Sp K) ⊆ Set.range x := by
    rintro q -
    exact ⟨p, Subsingleton.elim (α := PrimeSpectrum K) _ _⟩
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (IsOpenImmersion.lift x (𝟙 _) hr)
  have e : spMap φ.hom ≫ x = 𝟙 _ := by
    rw [← IsOpenImmersion.lift_fac x (𝟙 _) hr, ← hφ]
    rfl
  exact ⟨_, e ▸ GlobalTheory.T.hasThetaConstants_ring_baseChange hL2 o g N' J b _ s t R K φ.hom x v hth⟩

theorem eval₂_eq_zero_of_fromC (hL : Out.Laws) (hL2 : Out.Laws2) {o : Type} [CommRing o] {g n N' : ℕ} {J : Type}
    {b : TBase o (N' ^ 2)} {em : o →+* ℂ} {C : TObj g (N' ^ 2) J b (spMap em) → Prop} {S : Scheme.{0}}
    {s : S ⟶ Sp o} {t : TObj g (N' ^ 2) J b s} (h2 : 2 ≤ n) (hn : n ∣ N') (hN : Odd N') {K : Type} [Field K]
    {y : Sp K ⟶ S} (hy : FromC em C t y) (β : o →+* K) (hβ : y ≫ s = spMap β) {w : Ix g (N' ^ 2) → K}
    (hw : t.HasTh y w) {F : MvPolynomial (Ix g (N' ^ 2)) o} (hF : F ∈ thIdeal em C) :
    MvPolynomial.eval₂ β w F = 0 := by
  obtain ⟨K₀, _, β₀, i, j, t₀, tx, tc, hem, hs, m1, m2, m3, hC⟩ := hy
  have hβi : β = i.comp β₀ := by
    have e : Spec.map (CommRingCat.ofHom β) = Spec.map (CommRingCat.ofHom β₀ ≫ CommRingCat.ofHom i) := by
      rw [Spec.map_comp]
      exact hβ.symm.trans hs
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  have a1 : tx.HasTh (𝟙 _) w :=
    (GlobalTheory.hasTh_iff_of_tmap o g N' J b _ _ t _ _ tx y K (𝟙 _) w m1).2 (by rwa [Category.id_comp])
  have a2 : t₀.HasTh (spMap i) w := by
    have := (GlobalTheory.hasTh_iff_of_tmap o g N' J b _ _ t₀ _ _ tx (spMap i) K (𝟙 _) w m2).1 a1
    rwa [Category.id_comp] at this
  obtain ⟨v₀, hv₀⟩ := t₀.exists_hasTh_field hL hL2 hN
  have a3 : t₀.HasTh (spMap i) (fun a => i (v₀ a)) := by
    have := GlobalTheory.T.hasThetaConstants_ring_baseChange hL2 o g N' J b _ _ t₀ K₀ K i (𝟙 _) v₀ hv₀
    rwa [Category.comp_id] at this
  have hspan : Ideal.span (Set.range fun a => i (v₀ a)) = ⊤ := by
    obtain ⟨a, ha⟩ := GlobalTheory.T.thetaCosetNonvanishing_of_hasTh hL hL2 o g N' J b _ _ t₀ n K (spMap i) _ ⊥ h2 hn a3 Ideal.isPrime_bot 0
    rw [Ideal.mem_bot] at ha
    exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨_, rfl⟩) (Ne.isUnit ha)
  obtain ⟨u, hu⟩ := GlobalTheory.hasTh_unique_unit hL hL2 o g N' J b _ _ t₀ K (spMap i) _ w a3 a2 hspan
  have a4 : tc.HasTh (𝟙 _) (fun a => j (v₀ a)) := by
    refine (GlobalTheory.hasTh_iff_of_tmap o g N' J b _ _ t₀ _ _ tc (spMap j) ℂ (𝟙 _) _ m3).2 ?_
    have := GlobalTheory.T.hasThetaConstants_ring_baseChange hL2 o g N' J b _ _ t₀ K₀ ℂ j (𝟙 _) v₀ hv₀
    rw [Category.comp_id] at this
    rwa [Category.id_comp]
  rw [hβi, funext hu]
  refine eval₂_mul_eq_zero_of_complex β₀ i j v₀ F (fun c hc => ?_) u
  have hle : thIdeal em C ≤ RingHom.ker (MvPolynomial.eval₂Hom em (fun a => c * j (v₀ a))) :=
    iInf_le_of_le tc (iInf_le_of_le _ (iInf_le_of_le ⟨hC, a4.unit_mul c hc.isUnit⟩ le_rfl))
  rw [hem]
  exact hle hF

theorem inMM_of_dense_fromSet :
    Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g n N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (C : TObj g (N' ^ 2) J b (spMap em) → Prop) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (R : Type) [CommRing R] (β : o →+* R) (x : Sp R ⟶ S) (v : Ix g (N' ^ 2) → R), 2 ≤ n → n ∣ N' → Odd N' → IsReduced S → Dense (fromSet em C t) → IsOpenImmersion x → x ≫ s = spMap β → t.HasTh x v → InMM n N' (thIdeal em C) β v := by
  intro hL hL2 o _ g n N' J b em C S s t R _ β x v h2 hn hN hS hd hx hβ hth
  refine ⟨fun F hF => ?_, fun q hq => GlobalTheory.T.thetaCosetNonvanishing_of_hasTh hL hL2 o g N' J b S s t n R x v q h2 hn hth hq⟩
  have hR : IsReduced (Sp R) := isReduced_of_isOpenImmersion x
  have hR' : _root_.IsReduced R := (affine_isReduced_iff (CommRingCat.of R)).1 hR
  refine IsNilpotent.eq_zero ((PrimeSpectrum.basicOpen_eq_bot_iff _).1 ?_)
  by_contra hne
  have hd' : Dense (x ⁻¹' fromSet em C t) := hd.preimage x.isOpenEmbedding.isOpenMap
  obtain ⟨q, hq, K, _, y, ⟨p, hp⟩, hy⟩ := hd'.inter_open_nonempty
    (PrimeSpectrum.basicOpen (MvPolynomial.eval₂ β v F) : Set (PrimeSpectrum R))
    (PrimeSpectrum.basicOpen _).isOpen ((TopologicalSpace.Opens.ne_bot_iff_nonempty _).1 hne)
  have hr : Set.range y ⊆ Set.range x := by
    rintro _ ⟨p', rfl⟩
    exact ⟨q, by rw [← hp, Subsingleton.elim (α := PrimeSpectrum K) p p']⟩
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (IsOpenImmersion.lift x y hr)
  have e : spMap φ.hom ≫ x = y := by
    rw [← IsOpenImmersion.lift_fac x y hr, ← hφ]
    rfl
  have hq' : PrimeSpectrum.comap φ.hom p = q := by
    apply x.isOpenEmbedding.injective
    rw [← hp, ← e]
    rfl
  have hw : t.HasTh y (fun a => φ.hom (v a)) := e ▸ GlobalTheory.T.hasThetaConstants_ring_baseChange hL2 o g N' J b S s t R K φ.hom x v hth
  have hs : y ≫ s = spMap (φ.hom.comp β) := by
    rw [← e, Category.assoc, hβ, ← Spec.map_comp]
    rfl
  have h0 := eval₂_eq_zero_of_fromC hL hL2 h2 hn hN hy _ hs hw hF
  rw [← MvPolynomial.hom_eval₂] at h0
  apply hq
  rw [← hq']
  change φ.hom _ ∈ PrimeSpectrum.asIdeal p
  rw [h0]
  exact Ideal.zero_mem _

end GlobalTheory.ZM
end

