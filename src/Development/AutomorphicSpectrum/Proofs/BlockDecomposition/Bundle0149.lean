import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0141
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Cup1CoboundaryMemBoundaries
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0138
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0139
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0140
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.FormalAlgebraisation.GEClosedProj
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GelfandSpectralNormalisation.NormalisedInvariants.PTConclAt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0142

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CupVanishingAntisymmetricCross
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.WedgeOf

namespace GlobalTheory.CompanionTheory.WedgeOf

theorem cup_add_cup_swap {R : Type} [CommRing R] {C : Type} [Category.{0} C]
    (F : C ⥤ CommAlgCat.{0} R) (a b : H1 F) : cup F a b + cup F b a = 0 := by
  obtain ⟨a', rfl⟩ := H1.mk_surjective F a
  obtain ⟨b', rfl⟩ := H1.mk_surjective F b
  rw [cup_mk, cup_mk, ← map_add, H2.mk_eq_zero]
  refine ⟨-(fun T T' φ => a'.1 T T' φ * b'.1 T T' φ), ?_⟩
  funext T T' T'' φ ψ
  simp only [map_neg, Pi.neg_apply, d1_apply, Submodule.coe_add, Pi.add_apply, cupZ_apply, Z1.comp, map_mul]
  ring

theorem hopf_pull_lift_cup {R : Type} [CommRing R] {C : Type} [Category.{0} C]
    (F : C ⥤ CommAlgCat.{0} R) {D : Type} [Category.{0} D] (G : D ⥤ CommAlgCat.{0} R)
    (π : CoefMap (RingHom.id R) (box F) G) (m : CoefMap (RingHom.id R) F G)
    (hm : ∀ c, m.pull1 c = π.pull1 ((boxL F).pull1 c + (boxR F).pull1 c))
    (t : H1 F ⊗[R] H1 F) :
    m.pull2 (TensorProduct.lift (cup F) t) =
      π.pull2 ((boxL F).pull2 (TensorProduct.lift (cup F) t) +
        (boxR F).pull2 (TensorProduct.lift (cup F) t) +
        TensorProduct.lift (crossB F) (t - TensorProduct.comm R _ _ t)) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [TensorProduct.lift.tmul, CoefMap.pullCohomologyTwo_cup m a b, hm a, hm b, ← CoefMap.pullCohomologyTwo_cup π _ _]
    refine congrArg (fun x => π.pull2 x) ?_
    rw [CoefMap.pullCohomologyTwo_cup (boxL F) a b, CoefMap.pullCohomologyTwo_cup (boxR F) a b, TensorProduct.comm_tmul, map_sub,
      TensorProduct.lift.tmul, TensorProduct.lift.tmul, crossB_apply, crossB_apply]
    simp only [map_add, LinearMap.add_apply]
    have h := cup_add_cup_swap (box F) ((boxL F).pull1 b) ((boxR F).pull1 a)
    have h3 : cup (box F) ((boxR F).pull1 a) ((boxL F).pull1 b) =
        -cup (box F) ((boxL F).pull1 b) ((boxR F).pull1 a) :=
      eq_neg_iff_add_eq_zero.2 (by rw [add_comm]; exact h)
    rw [h3]
    abel
  | add x y hx hy =>
    simp only [map_add, map_sub, hx, hy]
    abel

theorem hopf_cross_antisymm : LowSt → ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C]
    (F : C ⥤ CommAlgCat.{0} R), Hopf F False → ∀ t : H1 F ⊗[R] H1 F,
    TensorProduct.lift (cup F) t = 0 →
      TensorProduct.lift (crossB F) (t - TensorProduct.comm R _ _ t) = 0 := by
  intro hLow R _ C _ F hH t ht
  obtain ⟨D, _, G, π, m, hq, hm, -⟩ := hH
  have h2 := hopf_pull_lift_cup F G π m hm t
  simp only [ht, map_zero, zero_add] at h2
  obtain ⟨-, hinj, -⟩ := hLow R (C × C) D (box F) G π hq
  apply hinj.1
  rw [map_zero]
  exact h2.symm

end GlobalTheory.CompanionTheory.WedgeOf
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegenerateFaceOfOneCocycleEqZero
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC

namespace GlobalTheory.CompanionTheory.HopfC

theorem pr_eq_zero_of_degenerate :
    ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) {m : ℕ} (x : Cn F 1)
      (_ : dn F 1 x = 0) (e : Fin (1 + 1) →o Fin (m + 1)) (_ : e 0 = e 1), pr F e x = 0 := by
  intro R _ C _ F m x hx e h01
  have key : ∀ i : Fin (1 + 1 + 1),
      GlobalTheory.CompanionTheory.HopfC.pr F ((GlobalTheory.CompanionTheory.HopfC.cst (1 + 1) (e 0)).comp (GlobalTheory.CompanionTheory.HopfC.dl i)) x =
        GlobalTheory.CompanionTheory.HopfC.pr F e x := by
    intro i
    refine GlobalTheory.CompanionTheory.HopfC.pr_congr (fun j => ?_) x
    show e 0 = e j
    fin_cases j
    · rfl
    · exact h01
  have h := congrArg (GlobalTheory.CompanionTheory.HopfC.pr F (GlobalTheory.CompanionTheory.HopfC.cst (1 + 1) (e 0))) hx
  rw [map_zero (GlobalTheory.CompanionTheory.HopfC.pr F (GlobalTheory.CompanionTheory.HopfC.cst (1 + 1) (e 0))),
    GlobalTheory.CompanionTheory.HopfC.dn_eq, map_sum] at h
  simp only [map_smul, map_zsmul, GlobalTheory.CompanionTheory.HopfC.pr_pr] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, key] at h
  norm_num at h
  exact h

end GlobalTheory.CompanionTheory.HopfC
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsLocalChartAtPrimeStatement
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_chart_at_prime : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (e : Sp R ⟶ X) (g : ℕ), e ≫ s = 𝟙 _ → SmoothOfRelativeDimension g s → ∀ p : PrimeSpectrum R, ∃ (r : R) (A C : Type) (_ : CommRing A) (_ : CommRing C) (_ : Algebra C A) (_ : Algebra A (Localization.Away r)) (j : Sp A ⟶ X) (k : Sp C ⟶ Sp R), r ∉ p.asIdeal ∧ IsOpenImmersion j ∧ Mono k ∧ j ≫ s = spMap (algebraMap C A) ≫ k ∧ spMap (algebraMap A (Localization.Away r)) ≫ j = spMap (algebraMap R (Localization.Away r)) ≫ e ∧ Module.Free A (KaehlerDifferential C A) ∧ Module.Finite A (KaehlerDifferential C A) ∧ Module.finrank A (KaehlerDifferential C A) = g := by
  first | exact @GlobalTheory.CompanionTheory.CotChart.exists_smooth_chart | exact GlobalTheory.CompanionTheory.CotChart.exists_smooth_chart | (intros; apply GlobalTheory.CompanionTheory.CotChart.exists_smooth_chart <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSmoothCoordinateCoverStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smooth_coordinate_cover : ∀ {O : Type} [CommRing O] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) [IsSeparated q] [QuasiCompact q],
    (Smooth q → Nonempty (Cov q)) ∧ ∀ d, SmoothOfRelativeDimension d q → ∃ U : Cov q, ∀ α, U.d α = d := by
  first | exact @GlobalTheory.CompanionTheory.CovEx.exists_cov | exact GlobalTheory.CompanionTheory.CovEx.exists_cov | (intros; apply GlobalTheory.CompanionTheory.CovEx.exists_cov <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExteriorSquareTransportAlongEquiv
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC

namespace GlobalTheory.CompanionTheory.HopfC

theorem wedge_transport {R : Type} [CommRing R] {V V' W W' : Type} [AddCommGroup V] [Module R V] [AddCommGroup V'] [Module R V'] [AddCommGroup W] [Module R W] [AddCommGroup W'] [Module R W'] (u : V ≃ₗ[R] V') (v : W ≃ₗ[R] W') (c : V →ₗ[R] V →ₗ[R] W) (c' : V' →ₗ[R] V' →ₗ[R] W') (h : ∀ a b, v (c a b) = c' (u a) (u b)) (e : ⋀[R]^2 V' ≃ₗ[R] W') (he : ∀ a b, e (exteriorPower.ιMulti R 2 ![a, b]) = c' a b) : ∃ e' : ⋀[R]^2 V ≃ₗ[R] W, ∀ a b, e' (exteriorPower.ιMulti R 2 ![a, b]) = c a b := by
  have h₁ : (u : V →ₗ[R] V') ∘ₗ (u.symm : V' →ₗ[R] V) = LinearMap.id :=
    LinearMap.ext fun x => by simp
  have h₂ : (u.symm : V' →ₗ[R] V) ∘ₗ (u : V →ₗ[R] V') = LinearMap.id :=
    LinearMap.ext fun x => by simp
  let A : ⋀[R]^2 V ≃ₗ[R] ⋀[R]^2 V' :=
    LinearEquiv.ofLinear (exteriorPower.map 2 (u : V →ₗ[R] V'))
      (exteriorPower.map 2 (u.symm : V' →ₗ[R] V))
      (by rw [← exteriorPower.map_comp, h₁, exteriorPower.map_id])
      (by rw [← exteriorPower.map_comp, h₂, exteriorPower.map_id])
  refine ⟨A.trans (e.trans v.symm), fun a b => ?_⟩
  have hu : (⇑(u : V →ₗ[R] V') ∘ ![a, b]) = ![u a, u b] := by
    funext i
    fin_cases i <;> rfl
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.ofLinear_apply,
    exteriorPower.map_apply_ιMulti, hu, he, ← h, LinearEquiv.symm_apply_apply]

end GlobalTheory.CompanionTheory.HopfC
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExteriorSquareVectorBundleRank
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.WedgeOf

namespace GlobalTheory.CompanionTheory.WedgeOf

theorem vb_exteriorPower_two : ∀ (R V : Type) [CommRing R] [AddCommGroup V] [Module R V] (g : ℕ),
    VB R V g → VB R (⋀[R]^2 V) (g.choose 2) := by
  intro R V _ _ _ g h
  obtain ⟨hf, hp, hr⟩ := h
  have hproj : Module.Projective R (⋀[R]^2 V) := by
    obtain ⟨s, hs⟩ := Module.projective_def'.1 hp
    haveI : Module.Free R (⋀[R]^2 (V →₀ R)) := exteriorPower.instFree R 2
    refine Module.Projective.of_split (exteriorPower.map 2 s)
      (exteriorPower.map 2 (Finsupp.linearCombination R id)) ?_
    rw [← exteriorPower.map_comp, hs, exteriorPower.map_id]
  refine ⟨inferInstance, hproj, fun p => ?_⟩
  have hb := LocalizedModule.isBaseChange p.asIdeal.primeCompl V
  have hb2 := GlobalTheory.TopForm.isBaseChange_exteriorPower hb 2
  let S := Localization.AtPrime p.asIdeal
  let M := LocalizedModule p.asIdeal.primeCompl V
  let q : PrimeSpectrum S := IsLocalRing.closedPoint S
  have hq : PrimeSpectrum.comap (algebraMap R S) q = p :=
    PrimeSpectrum.ext (Localization.AtPrime.comap_maximalIdeal (I := p.asIdeal))
  have h1 := Module.rankAtStalk_isBaseChange hb q
  have h2 := Module.rankAtStalk_isBaseChange hb2 q
  rw [hq] at h1 h2
  haveI : Module.Finite S M := Module.Finite.equiv hb.equiv
  haveI : Module.Flat S M := Module.Flat.of_linearEquiv hb.equiv.symm
  haveI : Module.Free S M := Module.free_of_flat_of_isLocalRing
  have h3 : Module.finrank S M = g := by
    rw [← hr p, ← h1, Module.rankAtStalk_eq_finrank_of_free]
    rfl
  rw [← h2, Module.rankAtStalk_eq_finrank_of_free]
  change Module.finrank S (⋀[S]^2 M) = _
  rw [exteriorPower.finrank_eq, h3]

end GlobalTheory.CompanionTheory.WedgeOf
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteFunctorCategoryOfMeetLattice
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC

namespace GlobalTheory.CompanionTheory.HopfC

theorem finite_chains_semilattice : ∀ {P : Type} [SemilatticeInf P] [Finite P] (p : ℕ),
    Finite (Fin (p + 1) ⥤ Pᵒᵖ) := by
  intro P _ _ p
  haveI : Finite Pᵒᵖ := Finite.of_equiv P Opposite.equivToOpposite
  refine Finite.of_injective (fun F : Fin (p + 1) ⥤ Pᵒᵖ => F.obj) ?_
  intro F G h
  exact CategoryTheory.Functor.ext (fun i => congrFun h i)
    (fun i j f => Quiver.Hom.unop_inj (Subsingleton.elim _ _))

end GlobalTheory.CompanionTheory.HopfC
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteModulesSerreClassStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_modules_serre_class : ∀ (R : Type) [CommRing R] [IsNoetherianRing R], ∃ 𝒮 : Serre.{1} R,
    ∀ (M : Type 1) [AddCommGroup M] [Module R M], 𝒮.P M ↔ Module.Finite R M := by
  first | exact @GlobalTheory.CompanionTheory.SerreFin.exists_serre_finite | exact GlobalTheory.CompanionTheory.SerreFin.exists_serre_finite | (intros; apply GlobalTheory.CompanionTheory.SerreFin.exists_serre_finite <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FirstCohomologyBaseChangeOfCochainEquivsStatement
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.first_cohomology_base_change_of_cochain_equivs : ∀ (R R' C : Type) [CommRing R] [CommRing R'] [Algebra R R'] [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) (F' : C ⥤ CommAlgCat.{0} R') (m : BC F F') (E₀ : R' ⊗[R] C0 F ≃ₗ[R'] C0 F') (E₁ : R' ⊗[R] C1 F ≃ₗ[R'] C1 F') (E₂ : R' ⊗[R] C2 F ≃ₗ[R'] C2 F'), (∀ c, E₁ (1 ⊗ₜ c) = fun T T' φ ↦ m.α T' (c T T' φ)) → (∀ x, E₁ ((d0 F).baseChange R' x) = d0 F' (E₀ x)) → (∀ x, E₂ ((d1 F).baseChange R' x) = d1 F' (E₁ x)) → (∀ x : R' ⊗[R] C1 F, (d1 F).lTensor R' x = 0 → ∃ (t : R' ⊗[R] Z1 F) (y : R' ⊗[R] C0 F), (Z1 F).subtype.lTensor R' t + (d0 F).lTensor R' y = x) → (∀ (t : R' ⊗[R] Z1 F) (y : R' ⊗[R] C0 F), (Z1 F).subtype.lTensor R' t = (d0 F).lTensor R' y → ∃ y' : R' ⊗[R] C0 F, ((d0 F).codRestrict (Z1 F) (commAlgFunctorCoboundaryZero_mem_cocyclesOne F)).lTensor R' y' = t) → ∃ e : R' ⊗[R] H1 F ≃ₗ[R'] H1 F', ∀ c, e (1 ⊗ₜ c) = m.coef.pull1 c := by
  first | exact @GlobalTheory.CompanionTheory.PerfectFirstCohomologyBaseChange.h1_baseChange | exact GlobalTheory.CompanionTheory.PerfectFirstCohomologyBaseChange.h1_baseChange | (intros; apply GlobalTheory.CompanionTheory.PerfectFirstCohomologyBaseChange.h1_baseChange <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FirstCohomologyInclusionTensorInjective
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.WedgeOf

section BaseChange

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
  (R' : Type) [CommRing R'] [Algebra R R']

@[reducible] def bcF : C ⥤ CommAlgCat.{0} R' where
  obj T := CommAlgCat.of R' (R' ⊗[R] F.obj T)
  map φ := CommAlgCat.ofHom (Algebra.TensorProduct.map (AlgHom.id R' R') (mp F φ))
  map_id T := CommAlgCat.hom_ext (Algebra.TensorProduct.ext' fun a b ↦
    congrArg (fun y ↦ a ⊗ₜ[R] y) (mp_id F T b))
  map_comp φ ψ := CommAlgCat.hom_ext (Algebra.TensorProduct.ext' fun a b ↦
    congrArg (fun y ↦ a ⊗ₜ[R] y) (mp_comp F φ ψ b))

def bcM : BC F (bcF F R') where
  α T := (Algebra.TensorProduct.includeRight : F.obj T →ₐ[R] R' ⊗[R] F.obj T).toRingHom
  naturality _ _ := rfl
  smul T r b := by
    change (1 : R') ⊗ₜ[R] (r • b) = algebraMap R R' r • ((1 : R') ⊗ₜ[R] b)
    rw [TensorProduct.tmul_smul, algebraMap_smul]
  bij T := ⟨LinearEquiv.refl _ _, fun _ ↦ rfl⟩

variable {R'} {M : Type} [AddCommGroup M] [Module R M] (j : M →ₗ[R] R')

def ev0 : M ⊗[R] C0 F →ₗ[R] ∀ T : C, R' ⊗[R] F.obj T :=
  LinearMap.pi fun T ↦ TensorProduct.map j (LinearMap.proj T)

def ev1 : M ⊗[R] C1 F →ₗ[R] ∀ (T T' : C) (_ : T ⟶ T'), R' ⊗[R] F.obj T' :=
  LinearMap.pi fun T ↦ LinearMap.pi fun T' ↦ LinearMap.pi fun φ ↦
    TensorProduct.map j ((LinearMap.proj φ) ∘ₗ (LinearMap.proj T') ∘ₗ (LinearMap.proj T))

theorem evaluation_zero_tmul (n : M) (g : C0 F) (T : C) : ev0 F j (n ⊗ₜ g) T = j n ⊗ₜ g T := rfl

theorem realTensorEvalAlgHom_tmul (n : M) (f : C1 F) {T T' : C} (φ : T ⟶ T') :
    ev1 F j (n ⊗ₜ f) T T' φ = j n ⊗ₜ f T T' φ := rfl

theorem evaluation_coboundary_zero_tensor (y : M ⊗[R] C0 F) :
    ev1 F j ((d0 F).lTensor M y) = d0 (bcF F R') (ev0 F j y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul n g =>
    funext T T' φ
    show ev1 F j (n ⊗ₜ d0 F g) T T' φ = ev0 F j (n ⊗ₜ g) T' - mp (bcF F R') φ (ev0 F j (n ⊗ₜ g) T)
    rw [realTensorEvalAlgHom_tmul, evaluation_zero_tmul, evaluation_zero_tmul, amitsur_d0_apply]
    show j n ⊗ₜ (g T' - mp F φ (g T)) =
      j n ⊗ₜ g T' - (Algebra.TensorProduct.map (AlgHom.id R' R') (mp F φ)) (j n ⊗ₜ g T)
    rw [Algebra.TensorProduct.map_tmul, TensorProduct.tmul_sub]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem exists_cocycle (e : R' ⊗[R] H1 F ≃ₗ[R'] H1 (bcF F R'))
    (he : ∀ c, e (1 ⊗ₜ c) = (bcM F R').coef.pull1 c) (t : M ⊗[R] Z1 F) :
    ∃ z : Z1 (bcF F R'), z.1 = ev1 F j ((Z1 F).subtype.lTensor M t) ∧
      H1.mk (bcF F R') z = e (j.rTensor (H1 F) ((H1.mk F).lTensor M t)) := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp, by simp⟩
  | tmul n c =>
    refine ⟨j n • (bcM F R').coef.pullbackOneCocycle c, ?_, ?_⟩
    · funext T T' φ
      show j n • ((1 : R') ⊗ₜ[R] (c.1 T T' φ)) = ev1 F j (n ⊗ₜ c.1) T T' φ
      rw [realTensorEvalAlgHom_tmul, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    · rw [map_smul, ← CoefMap.pullCohomologyOne_class]
      show j n • (bcM F R').coef.pull1 (H1.mk F c) = e (j n ⊗ₜ H1.mk F c)
      rw [← he, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
  | add x y hx hy =>
    obtain ⟨z1, h1, h1'⟩ := hx
    obtain ⟨z2, h2, h2'⟩ := hy
    refine ⟨z1 + z2, ?_, ?_⟩
    · simp only [Submodule.coe_add, h1, h2, map_add]
    · simp only [map_add, h1', h2']

theorem lTensor_iotaQ_injective_of_retract (h : H1CommutesBaseChange F) (p : R' →ₗ[R] M) (hp : p ∘ₗ j = LinearMap.id) :
    Function.Injective ((iotaQ F).lTensor M) := by
  obtain ⟨e, he⟩ := h R' (bcF F R') (bcM F R')
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨t, rfl⟩ := LinearMap.lTensor_surjective M (H1.mk_surjective F) x
  have hcomp : iotaQ F ∘ₗ H1.mk F = (LinearMap.range (d0 F)).mkQ ∘ₗ (Z1 F).subtype :=
    LinearMap.ext fun f => iotaQ_mk F f
  have hx' : ((LinearMap.range (d0 F)).mkQ).lTensor M ((Z1 F).subtype.lTensor M t) = 0 := by
    rw [← LinearMap.lTensor_comp_apply, ← hcomp, LinearMap.lTensor_comp_apply]
    exact hx
  obtain ⟨y, hy⟩ := (lTensor_exact M (LinearMap.exact_map_mkQ_range (d0 F))
    (Submodule.mkQ_surjective _) ((Z1 F).subtype.lTensor M t)).1 hx'
  obtain ⟨z, hz1, hz2⟩ := exists_cocycle F j e he t
  have hz0 : H1.mk (bcF F R') z = 0 := by
    apply iotaQ_injective (bcF F R')
    rw [iotaQ_mk, map_zero, Submodule.Quotient.mk_eq_zero, hz1, ← hy, evaluation_coboundary_zero_tensor]
    exact LinearMap.mem_range_self _ _
  have hx0 : j.rTensor (H1 F) ((H1.mk F).lTensor M t) = 0 := by
    rw [← e.map_eq_zero_iff, ← hz2, hz0]
  calc (H1.mk F).lTensor M t = (p ∘ₗ j).rTensor (H1 F) ((H1.mk F).lTensor M t) := by
        rw [hp, LinearMap.rTensor_id_apply]
    _ = p.rTensor (H1 F) (j.rTensor (H1 F) ((H1.mk F).lTensor M t)) := LinearMap.rTensor_comp_apply _ _ _ _
    _ = 0 := by rw [hx0, map_zero]

end BaseChange

theorem iotaQ_lTensor_injective (R : Type) [CommRing R] (C : Type) [Category.{0} C]
    (F : C ⥤ CommAlgCat.{0} R) (h : H1CommutesBaseChange F) (M : Type) [AddCommGroup M] [Module R M] :
    Function.Injective ((iotaQ F).lTensor M) := by
  letI : Module Rᵐᵒᵖ M := Module.compHom M ((RingHom.id R).fromOpposite fun _ _ => Commute.all _ _)
  haveI : IsCentralScalar R M := ⟨fun _ _ => rfl⟩
  exact lTensor_iotaQ_injective_of_retract F (TrivSqZeroExt.inrHom R M) h (TrivSqZeroExt.sndHom R M)
    (LinearMap.ext fun m => by simp)

end GlobalTheory.CompanionTheory.WedgeOf
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalMorphismUniquenessStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out PositivityTheory.FormalThickening
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formal_morphism_uniqueness : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R →
  ∀ (X Z : Over (Spec (CommRingCat.of R))), IsProper X.hom → IsSeparated Z.hom →
  ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (b : ∀ e, (Y e).left ⟶ X.left),
    (∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) →
  ∀ g g' : X ⟶ Z, (∀ e, b e ≫ g.left = b e ≫ g'.left) → g = g' := by
  first | exact @GlobalTheory.CompanionTheory.FormalUniq.eq_of_comp_thickenings_eq | exact GlobalTheory.CompanionTheory.FormalUniq.eq_of_comp_thickenings_eq | (intros; apply GlobalTheory.CompanionTheory.FormalUniq.eq_of_comp_thickenings_eq <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaloisGroupTransportIsomorphism
section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso

namespace GlobalTheory.CompanionTheory.PTIso

section GalConj

variable {F Ω F' Ω' : Type} [Field F] [Field Ω] [Algebra F Ω]
  [Field F'] [Field Ω'] [Algebra F' Ω']

def galConjFun (e : F ≃+* F') (E : Ω ≃+* Ω')
    (hE : ∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) (σ : Ω ≃ₐ[F] Ω) :
    Ω' ≃ₐ[F'] Ω' :=
  AlgEquiv.ofRingEquiv (f := E.symm.trans ((σ : Ω ≃+* Ω).trans E)) (fun y => by
    obtain ⟨x, rfl⟩ := e.surjective y
    have h1 : E.symm (algebraMap F' Ω' (e x)) = algebraMap F Ω x := by
      rw [← hE, RingEquiv.symm_apply_apply]
    simp [h1, hE])

theorem galConjFun_apply (e : F ≃+* F') (E : Ω ≃+* Ω')
    (hE : ∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) (σ : Ω ≃ₐ[F] Ω) (x : Ω) :
    galConjFun e E hE σ (E x) = E (σ x) := by
  simp [galConjFun]

def galConjHom (e : F ≃+* F') (E : Ω ≃+* Ω')
    (hE : ∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) :
    (Ω ≃ₐ[F] Ω) →* (Ω' ≃ₐ[F'] Ω') where
  toFun := galConjFun e E hE
  map_one' := by
    ext y
    obtain ⟨x, rfl⟩ := E.surjective y
    rw [galConjFun_apply]; rfl
  map_mul' σ τ := by
    ext y
    obtain ⟨x, rfl⟩ := E.surjective y
    show galConjFun e E hE (σ * τ) (E x) = galConjFun e E hE σ (galConjFun e E hE τ (E x))
    rw [galConjFun_apply e E hE τ, galConjFun_apply e E hE σ, galConjFun_apply e E hE (σ * τ),
      AlgEquiv.mul_apply]

theorem galConjHom_apply (e : F ≃+* F') (E : Ω ≃+* Ω')
    (hE : ∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) (σ : Ω ≃ₐ[F] Ω) (x : Ω) :
    galConjHom e E hE σ (E x) = E (σ x) :=
  galConjFun_apply e E hE σ x

theorem continuous_galConjHom [Algebra.IsAlgebraic F Ω]
    (e : F ≃+* F') (E : Ω ≃+* Ω')
    (hE : ∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) :
    Continuous (galConjHom e E hE) := by
  refine continuous_of_continuousAt_one _ ?_
  intro s hs
  rw [map_one, krullTopology_mem_nhds_one_iff] at hs
  obtain ⟨K', hK', hKs⟩ := hs
  let b := Module.finBasis F' K'
  let T : Set Ω := Set.range fun i => E.symm (b i : Ω')
  let L : IntermediateField F Ω := IntermediateField.adjoin F T
  have hL : FiniteDimensional F L :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  rw [Filter.mem_map, krullTopology_mem_nhds_one_iff]
  refine ⟨L, hL, fun σ hσ => hKs ?_⟩
  have hfix : ∀ i, galConjHom e E hE σ (b i : Ω') = (b i : Ω') := by
    intro i
    have hmem : E.symm (b i : Ω') ∈ L :=
      IntermediateField.subset_adjoin F T ⟨i, rfl⟩
    have h1 : σ (E.symm (b i : Ω')) = E.symm (b i : Ω') :=
      (IntermediateField.mem_fixingSubgroup_iff L σ).1 hσ _ hmem
    have h2 := galConjHom_apply e E hE σ (E.symm (b i : Ω'))
    rwa [h1, RingEquiv.apply_symm_apply] at h2
  have hlin : ((galConjHom e E hE σ).toAlgHom.comp K'.val).toLinearMap = K'.val.toLinearMap :=
    b.ext fun i => hfix i
  refine (IntermediateField.mem_fixingSubgroup_iff K' _).2 fun x hx => ?_
  exact congrArg (fun f : K' →ₗ[F'] Ω' => f ⟨x, hx⟩) hlin

end GalConj

theorem exists_galContinuousMulEquiv : ∀ (F Ω F' Ω' : Type) [Field F] [NumberField F] [Field Ω]
    [Algebra F Ω] [IsAlgClosure F Ω] [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω']
    [IsAlgClosure F' Ω'] (e : F ≃+* F') (E : Ω ≃+* Ω'),
    (∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) →
    ∃ Φ : G F Ω ≃ₜ* G F' Ω', ∀ (σ : G F Ω) (x : Ω), Φ σ (E x) = E (σ x) := by
  intro F Ω F' Ω' _ _ _ _ _ _ _ _ _ _ e E hE
  haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  haveI : Algebra.IsAlgebraic F' Ω' := IsAlgClosure.isAlgebraic
  have hE' : ∀ x : F', E.symm (algebraMap F' Ω' x) = algebraMap F Ω (e.symm x) := by
    intro x
    rw [RingEquiv.symm_apply_eq, hE, RingEquiv.apply_symm_apply]
  refine ⟨{ toFun := galConjHom e E hE
            invFun := galConjHom e.symm E.symm hE'
            left_inv := ?_
            right_inv := ?_
            map_mul' := map_mul _
            continuous_toFun := continuous_galConjHom e E hE
            continuous_invFun := continuous_galConjHom e.symm E.symm hE' },
    fun σ x => galConjHom_apply e E hE σ x⟩
  · intro σ
    ext x
    have h := galConjHom_apply e.symm E.symm hE' (galConjHom e E hE σ) (E x)
    rw [galConjHom_apply e E hE σ x, RingEquiv.symm_apply_apply,
      RingEquiv.symm_apply_apply] at h
    exact h
  · intro τ
    ext y
    have h := galConjHom_apply e E hE (galConjHom e.symm E.symm hE' τ) (E.symm y)
    rw [galConjHom_apply e.symm E.symm hE' τ y, RingEquiv.apply_symm_apply,
      RingEquiv.apply_symm_apply] at h
    exact h

end GlobalTheory.CompanionTheory.PTIso
end

