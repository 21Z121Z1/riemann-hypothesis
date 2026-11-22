import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0469
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0144
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0149
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0141
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0150
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0146
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Cup1CoboundaryMemBoundaries
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GelfandSpectralNormalisation.NormalisedInvariants.PTConclAt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0142
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StCocycle
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0148
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniqueConstantOfCompatibleFamily
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.Axis
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.Axis

theorem existsUnique_const_of_trivSqZeroExt (R : Type) [CommRing R] (C : Type) [Category.{0} C]
    (F : C ⥤ CommAlgCat.{0} R) (M : Type) [AddCommGroup M]
    [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M] (F' : C ⥤ CommAlgCat.{0} (TrivSqZeroExt R M)) (bc : BC F F') :
    Stein F' → ∀ z : ∀ T : C, M ⊗[R] F.obj T,
      (∀ (T T' : C) (φ : T ⟶ T'), z T' = (mp F φ).toLinearMap.lTensor M (z T)) →
      ∃! m : M, ∀ T, z T = m ⊗ₜ[R] (1 : F.obj T) := by
  intro hS z hz
  choose e he using bc.bij
  have hpure : ∀ (T : C) (r : TrivSqZeroExt R M) (b : F.obj T), e T (r ⊗ₜ[R] b) = r • bc.α T b := by
    intro T r b
    have h : (r ⊗ₜ[R] b : TrivSqZeroExt R M ⊗[R] F.obj T) = r • ((1 : TrivSqZeroExt R M) ⊗ₜ[R] b) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    rw [h, map_smul, he]
  have hnat : ∀ {T T' : C} (φ : T ⟶ T') (x : TrivSqZeroExt R M ⊗[R] F.obj T),
      e T' ((mp F φ).toLinearMap.lTensor _ x) = mp F' φ (e T x) := by
    intro T T' φ x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r b =>
      rw [LinearMap.lTensor_tmul, hpure, hpure, map_smul]
      exact congrArg (r • ·) (bc.naturality φ b)
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, map_add]
  let jj : ∀ T : C, M ⊗[R] F.obj T →ₗ[R] TrivSqZeroExt R M ⊗[R] F.obj T :=
    fun T ↦ (TrivSqZeroExt.inrHom R M).rTensor _
  have hsnd : ∀ (T : C) (x : M ⊗[R] F.obj T),
      (TrivSqZeroExt.sndHom R M).rTensor _ (jj T x) = x := by
    intro T x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [jj]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hcomm : ∀ {T T' : C} (φ : T ⟶ T') (x : M ⊗[R] F.obj T),
      jj T' ((mp F φ).toLinearMap.lTensor M x) = (mp F φ).toLinearMap.lTensor _ (jj T x) := by
    intro T T' φ x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [jj]
    | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
  have hconst : ∀ (T : C) (r : TrivSqZeroExt R M),
      algebraMap (TrivSqZeroExt R M) (F'.obj T) r = e T (r ⊗ₜ[R] (1 : F.obj T)) := by
    intro T r
    rw [hpure, map_one, Algebra.algebraMap_eq_smul_one]
  let w : C0 F' := fun T ↦ e T (jj T (z T))
  have hw : d0 F' w = 0 := by
    funext T T' φ
    rw [amitsur_d0_apply]
    simp only [w, Pi.zero_apply]
    rw [← hnat, ← hcomm, ← hz, sub_self]
  obtain ⟨r, hr⟩ := (hS.1 w).1 hw
  have hjjr : ∀ T : C, jj T (z T) = r ⊗ₜ[R] (1 : F.obj T) := by
    intro T
    apply (e T).injective
    rw [← hconst]
    exact (congrFun hr T).symm
  refine ⟨r.snd, fun T ↦ ?_, fun m₂ hm₂ ↦ ?_⟩
  · rw [← hsnd T (z T), hjjr T]
    simp
  · have h0 : algebraMap (TrivSqZeroExt R M) (C0 F') (TrivSqZeroExt.inr (m₂ - r.snd)) = 0 := by
      funext T
      have hd : (m₂ - r.snd) ⊗ₜ[R] (1 : F.obj T) = 0 := by
        have h1 : z T = r.snd ⊗ₜ[R] (1 : F.obj T) := by
          rw [← hsnd T (z T), hjjr T]
          simp
        rw [TensorProduct.sub_tmul, ← hm₂ T, ← h1, sub_self]
      have h2 : (TrivSqZeroExt.inr (m₂ - r.snd) : TrivSqZeroExt R M) ⊗ₜ[R] (1 : F.obj T) = 0 := by
        have : jj T ((m₂ - r.snd) ⊗ₜ[R] (1 : F.obj T)) =
            (TrivSqZeroExt.inr (m₂ - r.snd) : TrivSqZeroExt R M) ⊗ₜ[R] (1 : F.obj T) := by
          simp [jj]
        rw [← this, hd, map_zero]
      change algebraMap (TrivSqZeroExt R M) (F'.obj T) _ = 0
      rw [hconst, h2, map_zero]
    have h3 : (TrivSqZeroExt.inr (m₂ - r.snd) : TrivSqZeroExt R M) = 0 :=
      hS.2 (h0.trans (map_zero _).symm)
    have h4 := congrArg TrivSqZeroExt.snd h3
    simpa [sub_eq_zero] using h4

end GlobalTheory.CompanionTheory.Axis
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExteriorSquareVectorBundleRankStatement
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.WedgeOf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exterior_square_vector_bundle_rank : ∀ (R V : Type) [CommRing R] [AddCommGroup V] [Module R V] (g : ℕ), VB R V g → VB R (⋀[R]^2 V) (g.choose 2) := by
  first | exact @GlobalTheory.CompanionTheory.WedgeOf.vb_exteriorPower_two | exact GlobalTheory.CompanionTheory.WedgeOf.vb_exteriorPower_two | (intros; apply GlobalTheory.CompanionTheory.WedgeOf.vb_exteriorPower_two <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteChains
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.PerfN

theorem QIsoAt.transport {R A₀ A₁ A₂ B₀ B₁ B₂ B₀' B₁' B₂' : Type} [CommRing R] [AddCommGroup A₀] [AddCommGroup A₁]
    [AddCommGroup A₂] [AddCommGroup B₀] [AddCommGroup B₁] [AddCommGroup B₂] [AddCommGroup B₀'] [AddCommGroup B₁']
    [AddCommGroup B₂'] [Module R A₀] [Module R A₁] [Module R A₂] [Module R B₀] [Module R B₁] [Module R B₂]
    [Module R B₀'] [Module R B₁'] [Module R B₂'] {a₀ : A₀ →ₗ[R] A₁} {a₁ : A₁ →ₗ[R] A₂} {b₀ : B₀ →ₗ[R] B₁}
    {b₁ : B₁ →ₗ[R] B₂} {b₀' : B₀' →ₗ[R] B₁'} {b₁' : B₁' →ₗ[R] B₂'} {f : A₁ →ₗ[R] B₁}
    (v₀ : B₀ →ₗ[R] B₀') (v₁ : B₁ →ₗ[R] B₁') (v₂ : B₂ →ₗ[R] B₂')
    (s₀ : Function.Surjective v₀) (s₁ : Function.Bijective v₁) (s₂ : Function.Injective v₂)
    (c₀ : ∀ x, v₁ (b₀ x) = b₀' (v₀ x)) (c₁ : ∀ x, v₂ (b₁ x) = b₁' (v₁ x))
    (H : QIsoAt a₀ a₁ b₀ b₁ f) : QIsoAt a₀ a₁ b₀' b₁' (v₁ ∘ₗ f) := by
  refine ⟨fun x hx ⟨y, hy⟩ ↦ ?_, fun z hz ↦ ?_⟩
  · obtain ⟨y, rfl⟩ := s₀ y
    exact H.1 x hx ⟨y, s₁.1 (by rw [c₀, hy]; rfl)⟩
  · obtain ⟨z, rfl⟩ := s₁.2 z
    obtain ⟨x, y, hx, hy⟩ := H.2 z (s₂ (by rw [c₁, hz, map_zero]))
    refine ⟨x, v₀ y, hx, ?_⟩
    rw [← c₀, ← hy, map_sub]; rfl

theorem finite_chains (P : Type) [PartialOrder P] [Finite P] (n : ℕ) : Finite (Fin (n + 1) ⥤ Pᵒᵖ) := by
  have : Finite Pᵒᵖ := Finite.of_equiv P Opposite.equivToOpposite
  refine Finite.of_injective (fun (c : Fin (n + 1) ⥤ Pᵒᵖ) (i : Fin (n + 1)) ↦ c.obj i) fun c c' h ↦ ?_
  exact CategoryTheory.Functor.ext (fun i ↦ congrFun h i) (fun _ _ _ ↦ Subsingleton.elim _ _)

theorem flat_Cn {R : Type} [CommRing R] (P : Type) [PartialOrder P] [Finite P] (F : Pᵒᵖ ⥤ CommAlgCat.{0} R)
    (hF : ∀ T, Module.Flat R (F.obj T)) (n : ℕ) : Module.Flat R (Cn F n) := by
  have := finite_chains P n
  have := Fintype.ofFinite (Fin (n + 1) ⥤ Pᵒᵖ)
  classical
  exact Module.Flat.of_linearEquiv (DirectSum.linearEquivFunOnFintype R (Fin (n + 1) ⥤ Pᵒᵖ)
    (fun c ↦ F.obj (c.obj (Fin.last n)))).symm

theorem perfNoeth : CxSt → DictSt → PerfNoethSt := by
  intro hCx hD R _ P _ _ F hN hfl hf0 hfs
  obtain ⟨hd, -⟩ := hCx R Pᵒᵖ F
  obtain ⟨e₀, e₁, e₂, e₃, -, -, -, -, h0, h1, h2⟩ := hD R Pᵒᵖ F
  obtain ⟨e, h, B, i1, i2, i3, i4, i5⟩ := GlobalTheory.T.chain_homotopy_finite_projector P F
  have := fun n ↦ flat_Cn P F hfl n
  obtain ⟨Q, ψ, f1, f2, f3, f4⟩ := GlobalTheory.T.homotopy_projector_complex_bounded (fun n ↦ Cn F n) (dn F) hd e h B i1 i2 i3 i4 i5 hf0 hfs
  have g₀ : ∀ x, e₁ (dn F 0 x) = d0 F (e₀ x) := h0
  have g₁ : ∀ x, e₂ (dn F 1 x) = d1 F (e₁ x) := h1
  have g₂ : ∀ x, e₃ (dn F 2 x) = d2 F (e₂ x) := h2
  have k : ∀ n x, ψ (n + 1) ((Q.d n (n + 1)).hom x) = dn F n (ψ n x) := fun n x ↦
    LinearMap.congr_fun (f3 n) x
  have lt : ∀ {A B A' B' : Type} [AddCommGroup A] [AddCommGroup B] [AddCommGroup A'] [AddCommGroup B'] [Module R A]
      [Module R B] [Module R A'] [Module R B'] (M : ModuleCat.{0} R) (u : A ≃ₗ[R] A') (v : B ≃ₗ[R] B')
      (b : A →ₗ[R] B) (b' : A' →ₗ[R] B'), (∀ x, v (b x) = b' (u x)) →
      ∀ x, (v : B →ₗ[R] B').lTensor M (b.lTensor M x) = b'.lTensor M ((u : A →ₗ[R] A').lTensor M x) := by
    intro A B A' B' _ _ _ _ _ _ _ _ M u v b b' h x
    have : (v : B →ₗ[R] B') ∘ₗ b = b' ∘ₗ (u : A →ₗ[R] A') := LinearMap.ext h
    rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp, ← LinearMap.lTensor_comp, this]
  have bij : ∀ {A A' : Type} [AddCommGroup A] [AddCommGroup A'] [Module R A] [Module R A'] (M : ModuleCat.{0} R)
      (u : A ≃ₗ[R] A'), Function.Bijective ((u : A →ₗ[R] A').lTensor M) := fun M u ↦
    (u.lTensor M).bijective
  refine ⟨Q.X 0, Q.X 1, Q.X 2, Q.X 3, (Q.d 0 1).hom, (Q.d 1 2).hom, (Q.d 2 3).hom, (e₀ : _ →ₗ[R] _) ∘ₗ ψ 0,
    (e₁ : _ →ₗ[R] _) ∘ₗ ψ 1, (e₂ : _ →ₗ[R] _) ∘ₗ ψ 2, ⟨f1 0, f2 0⟩, ⟨f1 1, f2 1⟩, ⟨f1 2, f2 2⟩, ⟨f1 3, f2 3⟩,
    ?_, ?_, ?_, ?_, ⟨(e₃ : _ →ₗ[R] _) ∘ₗ ψ 3, ?_⟩, fun M ↦ ?_⟩
  · exact congrArg ModuleCat.Hom.hom (Q.d_comp_d 0 1 2)
  · exact congrArg ModuleCat.Hom.hom (Q.d_comp_d 1 2 3)
  · refine LinearMap.ext fun x ↦ ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, k]
    exact g₀ _
  · refine LinearMap.ext fun x ↦ ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [k 1]; exact g₁ _
  · refine LinearMap.ext fun x ↦ ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [k 2]; exact g₂ _
  · obtain ⟨q0, qs⟩ := f4 M
    rw [LinearMap.lTensor_comp, LinearMap.lTensor_comp, LinearMap.lTensor_comp]
    exact ⟨QIsoAt.transport LinearMap.id _ _ Function.surjective_id (bij M e₀) (bij M e₁).1
        (fun x ↦ by simp) (lt M e₀ e₁ _ _ g₀) q0,
      QIsoAt.transport _ _ _ (bij M e₀).2 (bij M e₁) (bij M e₂).1 (lt M e₀ e₁ _ _ g₀) (lt M e₁ e₂ _ _ g₁) (qs 0),
      QIsoAt.transport _ _ _ (bij M e₁).2 (bij M e₂) (bij M e₃).1 (lt M e₁ e₂ _ _ g₁) (lt M e₂ e₃ _ _ g₂) (qs 1)⟩

end GlobalTheory.CompanionTheory.PerfN
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteFunctorCategoryOfMeetLatticeStatement
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_functor_category_of_meet_lattice : ∀ {P : Type} [SemilatticeInf P] [Finite P] (p : ℕ), Finite (Fin (p + 1) ⥤ Pᵒᵖ) := by
  first | exact @GlobalTheory.CompanionTheory.HopfC.finite_chains_semilattice | exact GlobalTheory.CompanionTheory.HopfC.finite_chains_semilattice | (intros; apply GlobalTheory.CompanionTheory.HopfC.finite_chains_semilattice <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FirstCohomologyInclusionTensorInjectiveStatement
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.WedgeOf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.first_cohomology_inclusion_tensor_injective : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), H1CommutesBaseChange F → ∀ (M : Type) [AddCommGroup M] [Module R M], Function.Injective ((iotaQ F).lTensor M) := by
  first | exact @GlobalTheory.CompanionTheory.WedgeOf.iotaQ_lTensor_injective | exact GlobalTheory.CompanionTheory.WedgeOf.iotaQ_lTensor_injective | (intros; apply GlobalTheory.CompanionTheory.WedgeOf.iotaQ_lTensor_injective <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatCocycleTensorRepresentation
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.Axis
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.Axis

theorem rTensor_coords_bijective {R : Type} [CommRing R] {I : Type} [Finite I] {P : Type}
    [AddCommGroup P] [Module R P] (M : I → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    (e : P ≃ₗ[R] ∀ i, M i) (N : Type) [AddCommGroup N] [Module R N] :
    Function.Bijective (LinearMap.pi fun i =>
      ((LinearMap.proj i : (∀ i, M i) →ₗ[R] M i) ∘ₗ e.toLinearMap).rTensor N) := by
  classical
  cases nonempty_fintype I
  have hcomp : (LinearMap.pi fun i =>
      ((LinearMap.proj i : (∀ i, M i) →ₗ[R] M i) ∘ₗ e.toLinearMap).rTensor N) =
      (TensorProduct.piLeft (R := R) (N := N) (M := M)).toLinearMap ∘ₗ
        (LinearEquiv.rTensor N e).toLinearMap := by
    apply TensorProduct.ext'
    intro p n
    funext i
    simp
  rw [hcomp]
  exact ((LinearEquiv.rTensor N e).trans
    (TensorProduct.piLeft (R := R) (N := N) (M := M))).bijective

section Cochains

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

def oneCochainsPiArrowsEquiv : C1 F ≃ₗ[R] ∀ a : (Σ T : C, Σ T' : C, (T ⟶ T')), F.obj a.2.1 where
  toFun f a := f a.1 a.2.1 a.2.2
  invFun g T T' φ := g ⟨T, T', φ⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

def twoCochainsPiComposableEquiv : C2 F ≃ₗ[R]
    ∀ a : (Σ T : C, Σ T' : C, Σ T'' : C, (T ⟶ T') × (T' ⟶ T'')), F.obj a.2.2.1 where
  toFun f a := f a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2
  invFun g T T' T'' φ ψ := g ⟨T, T', T'', φ, ψ⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

def evC {T T' : C} (φ : T ⟶ T') : C1 F →ₗ[R] F.obj T' where
  toFun f := f T T' φ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem evaluation_comp_coboundary_one {T T' T'' : C} (φ : T ⟶ T') (ψ : T' ⟶ T'') :
    (LinearMap.proj (⟨T, T', T'', φ, ψ⟩ : Σ T : C, Σ T' : C, Σ T'' : C, (T ⟶ T') × (T' ⟶ T'')) :
        (∀ a : (Σ T : C, Σ T' : C, Σ T'' : C, (T ⟶ T') × (T' ⟶ T'')), F.obj a.2.2.1) →ₗ[R] _) ∘ₗ
      (twoCochainsPiComposableEquiv F).toLinearMap ∘ₗ d1 F =
    (mp F ψ).toLinearMap ∘ₗ evC F φ - evC F (φ ≫ ψ) + evC F ψ := by
  ext f
  rfl

end Cochains

theorem cocycle_of_flat (R : Type) [CommRing R] (C : Type) [Category.{0} C] [Finite C]
    [Quiver.IsThin C] (F : C ⥤ CommAlgCat.{0} R)
    (N : Type) [AddCommGroup N] [Module R N] [Module.Flat R N]
    (f : ∀ (T T' : C) (_ : T ⟶ T'), F.obj T' ⊗[R] N)
    (hf : ∀ (T T' T'' : C) (φ : T ⟶ T') (ψ : T' ⟶ T''),
      f T T'' (φ ≫ ψ) = (mp F ψ).toLinearMap.rTensor N (f T T' φ) + f T' T'' ψ) :
    ∃ t : Z1 F ⊗[R] N, ∀ (T T' : C) (φ : T ⟶ T'), (evZ F φ).rTensor N t = f T T' φ := by
  haveI : ∀ T T' : C, Finite (T ⟶ T') := fun _ _ => Finite.of_subsingleton
  have b1 := rTensor_coords_bijective (R := R) _ (oneCochainsPiArrowsEquiv F) N
  have b2 := rTensor_coords_bijective (R := R) _ (twoCochainsPiComposableEquiv F) N
  obtain ⟨v, hv⟩ := b1.2 (fun a => f a.1 a.2.1 a.2.2)
  have hv' : ∀ (T T' : C) (φ : T ⟶ T'), (evC F φ).rTensor N v = f T T' φ := fun T T' φ =>
    congrFun hv ⟨T, T', φ⟩
  have hw : (d1 F).rTensor N v = 0 := by
    apply b2.1
    rw [map_zero]
    funext ⟨T, T', T'', φ, ψ⟩
    have h := congrArg (fun g => LinearMap.rTensor N g v) (evaluation_comp_coboundary_one F φ ψ)
    simp only [LinearMap.rTensor_add, LinearMap.rTensor_sub, LinearMap.rTensor_comp,
      LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply, hv'] at h
    rw [hf T T' T'' φ ψ] at h
    simp only [LinearMap.pi_apply, Pi.zero_apply, LinearMap.rTensor_comp, LinearMap.comp_apply]
    rw [h]
    abel
  have hex : Function.Exact (Z1 F).subtype (d1 F) := fun x => by
    rw [← LinearMap.mem_ker, ← commAlgFunctorCocyclesOne_eq_ker]
    simp
  obtain ⟨t, ht⟩ := (Module.Flat.rTensor_exact N hex v).1 hw
  refine ⟨t, fun T T' φ => ?_⟩
  have : evZ F φ = evC F φ ∘ₗ (Z1 F).subtype := rfl
  rw [this, LinearMap.rTensor_comp, LinearMap.comp_apply, ht, hv']

end GlobalTheory.CompanionTheory.Axis
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaloisGroupTransportIsomorphismStatement
section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_group_transport_isomorphism : ∀ (F Ω F' Ω' : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω'] (e : F ≃+* F') (E : Ω ≃+* Ω'), (∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) → ∃ Φ : G F Ω ≃ₜ* G F' Ω', ∀ (σ : G F Ω) (x : Ω), Φ σ (E x) = E (σ x) := by
  first | exact @GlobalTheory.CompanionTheory.PTIso.exists_galContinuousMulEquiv | exact GlobalTheory.CompanionTheory.PTIso.exists_galContinuousMulEquiv | (intros; apply GlobalTheory.CompanionTheory.PTIso.exists_galContinuousMulEquiv <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormAction
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
noncomputable section
namespace GlobalTheory.CompanionTheory.GrForm

section Abstract

variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R}

def mulSq (a b : IdF A) (T : C) (y : A.obj T) : sqM a b T →ₗ[R] sqM a b T where
  toFun x := ⟨Ideal.Quotient.mk _ y * x.1, Ideal.mul_mem_left ((a.S T).map (Ideal.Quotient.mk (b.S T))) _ x.2⟩
  map_add' x x' := Subtype.ext (mul_add _ _ _)
  map_smul' c x := Subtype.ext (mul_smul_comm _ _ _)

def mulMor (a b c : IdF A) (y : ∀ T : C, A.obj T)
    (hy : ∀ {T T' : C} (φ : T ⟶ T'), y T' - (A.map φ).hom (y T) ∈ c.S T')
    (hc : ∀ (T : C) {v w : A.obj T}, v ∈ c.S T → w ∈ a.S T → v * w ∈ b.S T) :
    CH.Mor (sq a b) (sq a b) (RingHom.id R) where
  G := 𝟭 C
  τ T := mulSq a b T (y T)
  nat {T T'} φ x := by
    obtain ⟨x, hx⟩ := x
    obtain ⟨w, hw, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hx
    have key : ∀ w : A.obj T, w ∈ a.S T → Ideal.Quotient.mk (b.S T') (y T') * Ideal.Quotient.mk (b.S T') ((A.map φ).hom w) =
        Ideal.Quotient.mk (b.S T') ((A.map φ).hom (y T * w)) := by
      intro w hw
      rw [← map_mul, map_mul (A.map φ).hom, Ideal.Quotient.eq, ← sub_mul]
      exact hc _ (hy φ) (a.map_mem φ hw)
    exact Subtype.ext (key w hw)

end Abstract

variable {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}

theorem sub_mem_of_lift {W : X.Opens} {T T' : Thick (LL q)} (φ : T ⟶ T') (h : InU W T) (h' : InU W T') (f : Γ(X, W))
    (v : T.B) (v' : T'.B) (hv : Ideal.Quotient.mk T.J v = ev T h f) (hv' : Ideal.Quotient.mk T'.J v' = ev T' h' f) :
    v' - φ.φ v ∈ T'.J := by
  refine Ideal.Quotient.eq.1 ?_
  rw [hv', ev_nat φ h h', ← hv]
  rfl

theorem lft_mul_sub {W : X.Opens} (T : Thick (LL q)) (h : InU W T) (f g : Γ(X, W)) :
    lft W T f * lft W T g - lft W T (f * g) ∈ T.J := by
  refine Ideal.Quotient.eq.1 ?_
  rw [map_mul, lft_spec T h, lft_spec T h, lft_spec T h, map_mul]

theorem J_mul_sFil (P : ObjectProperty (Thick (LL q))) (r : ℕ) (T : P.FullSubcategory) {v w : (sP P).A.obj T}
    (hv : v ∈ (sP P).J.S T) (hw : w ∈ (sFil P r).S T) : v * w ∈ (sFil P ((r : ℤ) + 1)).S T := by
  have hF := GlobalTheory.CompanionTheory.DPFil.isFil_sFil P
  have h1 : v ∈ (sFil P 1).S T := by
    have e := hF.one T
    rw [e]
    exact hv
  have := hF.mul 1 r T (x := v) (y := w) h1 hw
  have e : (((1 + r : ℕ)) : ℤ) = (r : ℤ) + 1 := by push_cast; ring
  rwa [e] at this

def mulZ {W : X.Opens} (P : ObjectProperty (Thick (LL q))) (hP : ∀ T, P T → InU W T) (r : ℕ) (z : Γ(X, W)) :
    CH.Mor (sq (sFil P r) (sFil P ((r : ℤ) + 1))) (sq (sFil P r) (sFil P ((r : ℤ) + 1))) (RingHom.id O) :=
  mulMor (sFil P r) (sFil P ((r : ℤ) + 1)) (sP P).J (fun T => lft W T.obj z)
    (fun {T T'} φ => sub_mem_of_lift φ.hom (hP _ T.property) (hP _ T'.property) z _ _
      (lft_spec _ (hP _ T.property) z) (lft_spec _ (hP _ T'.property) z))
    (fun T _ _ hv hw => J_mul_sFil P r T hv hw)

theorem units_mul_relation_rearrange_commRing {S : Type} [CommRing S] (y w l l' : S) : y * (w * l) - w * l' = (y * l - l') * w := by ring

theorem stAct : StAct := by
  intro O _ X q W P hP r z
  refine ⟨((mulZ P hP r z).pull r).toAddMonoidHom, ?_⟩
  intro d t u hu x c hc
  obtain ⟨f, hf, rfl, hfs⟩ := hc
  refine ⟨(mulZ P hP r z).pullC r f, ?_, rfl, ?_⟩
  · rw [CH.Mor.d_pullC, hf, map_zero]
  · intro s
    have hF := GlobalTheory.CompanionTheory.DPFil.isFil_sFil P
    let uu : Fin d → ∀ T : P.FullSubcategory, (sP P).A.obj T := fun i T => u i T.obj
    have hl : ∀ i {T T' : P.FullSubcategory} (φ : T ⟶ T'), uu i T' - ((sP P).A.map φ).hom (uu i T) ∈ (sP P).J.S T' :=
      fun i {T T'} φ => sub_mem_of_lift φ.hom (hP _ T.property) (hP _ T'.property) (t i) _ _
        (hu i _ (hP _ T.property)) (hu i _ (hP _ T'.property))
    change Ideal.Quotient.mk _ (show (sP P).A.obj (s.obj (Fin.last r)) from lft W (s.obj (Fin.last r)).obj z) *
      (show sqM (sFil P r) (sFil P ((r : ℤ) + 1)) _ from f s).1 = _
    rw [hfs s, ← map_mul, Ideal.Quotient.eq, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Ideal.sum_mem _ fun I _ => ?_
    have hw := wz_mem hF uu hl I.1 s
    have hd := lft_mul_sub _ (hP _ (s.obj (Fin.last r)).property) z (x I)
    have := J_mul_sFil P r _ hd hw
    have e := units_mul_relation_rearrange_commRing (S := (sP P).A.obj (s.obj (Fin.last r)))
      (lft W (s.obj (Fin.last r)).obj z) (wz uu I.1 s) (lft W (s.obj (Fin.last r)).obj (x I))
      (lft W (s.obj (Fin.last r)).obj (z * x I))
    exact Eq.mpr (congrArg (fun v => v ∈ (sFil P ((r : ℤ) + 1)).S (s.obj (Fin.last r))) e) this

end GlobalTheory.CompanionTheory.GrForm
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormCover
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.GrForm.AffCover

theorem iInf_basicOpen {X : Scheme.{0}} {V : X.Opens} : ∀ (n : ℕ) (g : Fin (n + 1) → Γ(X, V)),
    (⨅ a, X.basicOpen (g a)) = X.basicOpen (∏ k, g k) := by
  intro n
  induction n with
  | zero =>
    intro g
    simp
  | succ n ih =>
    intro g
    rw [Fin.prod_univ_succ, Scheme.basicOpen_mul, ← ih (fun k => g k.succ)]
    exact le_antisymm (le_inf (iInf_le _ 0) (le_iInf fun a => iInf_le _ a.succ))
      (le_iInf fun a => Fin.cases inf_le_left (fun b => inf_le_right.trans (iInf_le _ b)) a)

theorem stCover : GlobalTheory.CompanionTheory.GrForm.StCover := by
  intro O _ X q _ V hV
  classical
  have loc : ∀ x : V, ∃ (f : Γ(X, V)) (d : ℕ), x.1 ∈ X.basicOpen f ∧ Nonempty (Coord q (X.basicOpen f) d) := by
    intro x
    have h : RingHom.Locally RingHom.IsStandardSmooth (q.appLE ⊤ V le_top).hom :=
      RingHom.smooth_iff_locally_isStandardSmooth.1 (q.smooth_appLE (isAffineOpen_top _) hV le_top)
    obtain ⟨f, hf, hst⟩ := GlobalTheory.CompanionTheory.CovEx.exists_basicOpen RingHom.IsStandardSmooth
      RingHom.isStandardSmooth_respectsIso q hV h x.2
    obtain ⟨n, g, hg, he⟩ := hst.exists_etale_mvPolynomial
    exact ⟨f, n, hf, GlobalTheory.CompanionTheory.CovEx.coord_basicOpen q hV f g hg he⟩
  choose f d hx hc using loc
  obtain ⟨t, ht⟩ := hV.isCompact.elim_finite_subcover (fun x : V => (X.basicOpen (f x) : Set X))
    (fun x => (X.basicOpen (f x)).2) (fun x hxV => Set.mem_iUnion.2 ⟨⟨x, hxV⟩, hx _⟩)
  refine ⟨t, inferInstance, fun a => X.basicOpen (f a.1), fun a => d a.1, fun a => (hc a.1).some, ?_, ?_⟩
  · refine le_antisymm (iSup_le fun a => X.basicOpen_le _) fun x hxV => ?_
    obtain ⟨y, hy⟩ := Set.mem_iUnion.1 (ht hxV)
    obtain ⟨hy, hxy⟩ := Set.mem_iUnion.1 hy
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨y, hy⟩, hxy⟩
  · intro n i
    have e : capO (fun a : t => X.basicOpen (f a.1)) i = X.basicOpen (∏ k, f (i k).1) :=
      iInf_basicOpen n (fun k => f (i k).1)
    rw [e]
    exact hV.basicOpen _

end GlobalTheory.CompanionTheory.GrForm.AffCover
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InertiaQuotientTransportStatement
section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_quotient_equiv_of_matching_places : ∀ (F Ω F' Ω' : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω'] (e : F ≃+* F') (E : Ω ≃+* Ω'), (∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) → ∀ (Φ : G F Ω ≃ₜ* G F' Ω'), (∀ (σ : G F Ω) (x : Ω), Φ σ (E x) = E (σ x)) → ∀ (eV : HeightOneSpectrum (𝓞 F) ≃ HeightOneSpectrum (𝓞 F')), (∀ (A : ValuationSubring Ω) (A' : ValuationSubring Ω'), (∀ x, E x ∈ A' ↔ x ∈ A) → ∀ v : HeightOneSpectrum (𝓞 F), IsPlaceOver A v ↔ IsPlaceOver A' (eV v)) → (∀ (A : ValuationSubring Ω) (A' : ValuationSubring Ω'), (∀ x, E x ∈ A' ↔ x ∈ A) → ∀ σ : G F Ω, σ ∈ Inertia (F := F) A ↔ Φ σ ∈ Inertia (F := F') A') → ∀ (T : Set (HeightOneSpectrum (𝓞 F))) (T' : Set (HeightOneSpectrum (𝓞 F'))), (∀ v, v ∈ T ↔ eV v ∈ T') → ∃ Ψ : GS Ω T ≃ₜ* GS Ω' T', ∀ σ : G F Ω, Ψ (toGS Ω T σ) = toGS Ω' T' (Φ σ) := by
  first | exact @GlobalTheory.CompanionTheory.PTIso.exists_gsIso | exact GlobalTheory.CompanionTheory.PTIso.exists_gsIso | (intros; apply GlobalTheory.CompanionTheory.PTIso.exists_gsIso <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeNatDividesLPow
section
open DividedPowers CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.LatticeUnit

theorem natCast_dvd_pow :
    ∀ {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ) (m : ℕ),
      Lat.Hyp f ξ l m → ∀ n : ℕ, n ≠ 0 →
        ∃ (k : ℕ) (u : Lat.A f ξ l M), (n : Lat.A f ξ l M) * u = (l : Lat.A f ξ l M) ^ k := by
  intro W B _ _ _ f ξ l M m h n hn
  obtain ⟨k, u, hu⟩ := h.unit n hn
  refine ⟨k, Lat.ofW f ξ l M u, ?_⟩
  rw [← map_natCast (Lat.ofW f ξ l M) n, ← map_mul, hu, map_pow, map_natCast]

end GlobalTheory.CompanionTheory.LatticeUnit
end

