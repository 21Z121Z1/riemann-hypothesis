import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0175
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0060
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0061
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0019
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0158
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0018
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverOfIsPullback
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentPointCmEigenFrame
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0068
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0141
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0172
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0178
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GermSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0090
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0176
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0109
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0026
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFamilyExponentialLocally
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsGenericWeilPairing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0007
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.ThreeLeLevel
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0014
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0054

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BlockExtensionArithVarStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_extension_arith_var : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (e : ℕ) (β : MRing ι) (b : K → ℕ), IsArithVar (mCoordIdeal y) (e + 1) → IsMultiHomog β b → β ∉ mCoordIdeal y → ∃ (K' : Type) (_ : Fintype K') (ι' : K' → Type) (_ : ∀ k, Fintype (ι' k)) (κ : K → K') (v : (Σ k, ι k) → Σ k, ι' k) (y' : (Σ k, ι' k) → Ω) (J : Ideal (MRing ι')) (R : AnLogRes (mCoordIdeal y') J e) (Amp : HermLine ι'), IsBlockMap κ v ∧ y' ∘ v = y ∧ blockFnField y' = blockFnField y ∧ IsArithVar (mCoordIdeal y') (e + 1) ∧ IsEmbedded R.A (mCoordIdeal y') R.U R.lift ∧ IsSmoothHerm Amp ∧ IsPotential R.A (potOf R Amp) ∧ IsPosPot R.A (potOf R Amp) ∧ ∀ z ∈ mcPts (mCoordIdeal y'), evC z (rename v β) = 0 → z ∈ mcPts J := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.Good.exists_good_model | exact GlobalTheory.CompanionTheory.Ar.Cmp.Good.exists_good_model | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.Good.exists_good_model <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderBaseChangeGeneric
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BT.BaseChangeOrder

theorem exists_smul_mem_of_separates {R R' T : Type} [CommRing R] [CommRing R'] [IsDomain R'] [Finite T]
    (φ : R →+* R') (A : Subalgebra R (T → R))
    (hsep : ∀ s t : T, s ≠ t → ∃ a ∈ A, φ (a s) ≠ φ (a t)) :
    ∃ d : R, φ d ≠ 0 ∧ ∀ f : T → R, d • f ∈ A := by
  classical
  cases nonempty_fintype T
  have h1 : ∀ t s : T, s ≠ t → ∃ b ∈ A, b s = 0 ∧ φ (b t) ≠ 0 := by
    intro t s hst
    obtain ⟨a, ha, hne⟩ := hsep s t hst
    refine ⟨a - algebraMap R _ (a s), A.sub_mem ha (A.algebraMap_mem _), by simp, ?_⟩
    simpa [sub_eq_zero, map_sub] using hne.symm
  have h2 : ∀ t, ∃ c ∈ A, (∀ s, s ≠ t → c s = 0) ∧ φ (c t) ≠ 0 := by
    intro t
    choose! b hbA hb0 hb1 using h1 t
    refine ⟨∏ s ∈ Finset.univ.erase t, b s,
      Subalgebra.prod_mem _ fun s hs => hbA s (Finset.ne_of_mem_erase hs), ?_, ?_⟩
    · intro s hs
      rw [Finset.prod_apply]
      exact Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hs, Finset.mem_univ _⟩) (hb0 s hs)
    · rw [Finset.prod_apply, map_prod]
      exact Finset.prod_ne_zero_iff.2 fun s hs => hb1 s (Finset.ne_of_mem_erase hs)
  choose c hcA hc0 hc1 using h2
  refine ⟨∏ t, c t t, by rw [map_prod]; exact Finset.prod_ne_zero_iff.2 fun t _ => hc1 t, fun f => ?_⟩
  have key : (∏ t, c t t) • f = ∑ t, (f t * ∏ u ∈ Finset.univ.erase t, c u u) • c t := by
    ext x
    simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
    rw [Finset.sum_eq_single x]
    · rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ x)]
      ring
    · intro t _ ht
      rw [hc0 t x ht.symm, mul_zero]
    · simp
  rw [key]
  exact Subalgebra.sum_mem _ fun t _ => Subalgebra.smul_mem _ (hcA t) _

variable {R : Type} [CommRing R] {T : Type} [CommGroup T]

theorem translate_mem {A : Subalgebra R (T → R)} (hA : IsHopfOrder A) (t : T) {f : T → R} (hf : f ∈ A) :
    (fun h => f (t * h)) ∈ A := by
  have key : ∀ g ∈ prodSpan A, (fun h => g (t, h)) ∈ A := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hg
      exact A.smul_mem hb (a t)
    | zero => exact A.zero_mem
    | add x y _ _ hx hy => exact A.add_mem hx hy
    | smul r x _ hx => exact A.smul_mem hx r
  exact key _ (hA.comul f hf)

def transl {A : Subalgebra R (T → R)} (hA : IsHopfOrder A) (s : T) : A →+* A where
  toFun f := ⟨fun h => (f : T → R) (s * h), translate_mem hA s f.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem transl_apply {A : Subalgebra R (T → R)} (hA : IsHopfOrder A) (s : T) (f : A) (h : T) :
    (transl hA s f : T → R) h = (f : T → R) (s * h) := rfl

variable [IsDomain R] {R' : Type} [CommRing R'] [IsDomain R'] [Algebra R R']

theorem pt_comp_emb {Γ : QFGroup R T} {Γ' : QFGroup R' T} {F : Γ'.G.left ⟶ Γ.G.left}
    (hbc : Γ'.IsBaseChange Γ (algebraMap R R') F) {A : Subalgebra R (T → R)}
    {j : Γ.G.left ⟶ Spec (CommRingCat.of A)} (hj : Γ.IsEmb A j) (t : T) :
    (Γ'.pt t).left ≫ F ≫ j = Spec.map (CommRingCat.ofHom
      ((algebraMap R' (FractionRing R')).comp ((algebraMap R R').comp
        ((Pi.evalRingHom (fun _ : T => R) t).comp A.val.toRingHom)))) := by
  obtain ⟨B, _, i, k, k', σ, hinj, h1, h2, -, h4, h5⟩ := hbc.pts
  have hρ := Spec.map_preimage (σ t ≫ j)
  set ρ := Spec.preimage (σ t ≫ j) with hρdef
  have e1 : ρ ≫ CommRingCat.ofHom k = CommRingCat.ofHom
      ((algebraMap R (FractionRing R)).comp ((Pi.evalRingHom (fun _ : T => R) t).comp A.val.toRingHom)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hρ, ← Category.assoc, h4, hj.pt]
  have e2 : ∀ a : A, ρ.hom a = i ((a : T → R) t) := by
    intro a
    apply hinj
    have := congrArg (fun g => g.hom a) e1
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at this
    rw [this, ← RingHom.comp_apply k i, h1]
    rfl
  rw [← Category.assoc, ← h5 t, Category.assoc, ← hρ, ← Spec.map_comp]
  congr 1
  ext a
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
  rw [e2, ← RingHom.comp_apply k' i, h2]
  rfl

theorem separates {Γ : QFGroup R T} {Γ' : QFGroup R' T} {F : Γ'.G.left ⟶ Γ.G.left}
    (hbc : Γ'.IsBaseChange Γ (algebraMap R R') F) {A : Subalgebra R (T → R)}
    {j : Γ.G.left ⟶ Spec (CommRingCat.of A)} (hj : Γ.IsEmb A j) [Mono j] (s t : T) (hst : s ≠ t) :
    ∃ a ∈ A, algebraMap R R' (a s) ≠ algebraMap R R' (a t) := by
  by_contra hcon
  push_neg at hcon
  apply hst
  have e : (Γ'.pt s).left ≫ F ≫ j = (Γ'.pt t).left ≫ F ≫ j := by
    rw [pt_comp_emb hbc hj, pt_comp_emb hbc hj]
    congr 2
    ext a
    simp only [RingHom.comp_apply]
    exact congrArg _ (hcon a.1 a.2)
  have e' : (Γ'.pt s).left ≫ F = (Γ'.pt t).left ≫ F := by
    rw [← cancel_mono j]
    simpa only [Category.assoc] using e
  have e'' : (Γ'.pt s).left = (Γ'.pt t).left := by
    apply hbc.cart.hom_ext e'
    rw [Over.w, Over.w]
  obtain ⟨x⟩ : Nonempty (Spec (CommRingCat.of (FractionRing R'))) := inferInstance
  exact Γ'.pt_inj s t x x (by rw [e''])

end GlobalTheory.CompanionTheory.Ar.BT.BaseChangeOrder

namespace GlobalTheory.CompanionTheory.Ar.BT.BaseChangeOrder

variable {R : Type} [CommRing R] {T : Type} [CommGroup T]
variable [IsDomain R] {R' : Type} [CommRing R'] [IsDomain R'] [Algebra R R']

theorem isPullback_spec {A : Subalgebra R (T → R)} {A' : Subalgebra R' (T → R')}
    (e : R' ⊗[R] A ≃ₐ[R'] A') :
    IsPullback (Spec.map (CommRingCat.ofHom (e.toRingEquiv.toRingHom.comp
        (Algebra.TensorProduct.includeRight.toRingHom : A →+* R' ⊗[R] A))))
      (Spec.map (CommRingCat.ofHom (algebraMap R' A')))
      (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (Spec.map (CommRingCat.ofHom (algebraMap R R'))) := by
  have P := CommRingCat.isPushout_tensorProduct R R' A
  have P' : IsPushout (CommRingCat.ofHom (algebraMap R R')) (CommRingCat.ofHom (algebraMap R A))
      (CommRingCat.ofHom (algebraMap R' A'))
      (CommRingCat.ofHom (e.toRingEquiv.toRingHom.comp
        (Algebra.TensorProduct.includeRight.toRingHom : A →+* R' ⊗[R] A))) := by
    refine P.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) e.toRingEquiv.toCommRingCatIso ?_ ?_ ?_ ?_
    · simp
    · simp
    · ext x t
      have h : e (x ⊗ₜ[R] 1) = algebraMap R' A' x := by
        rw [← e.commutes]
        rfl
      simpa using congrFun (congrArg (fun y : A' => (y : T → R')) h) t
    · ext x
      simp
  exact isPullback_SpecMap_of_isPushout _ _ _ _ P'.flip

theorem exists_emb {Γ : QFGroup R T} {Γ' : QFGroup R' T} {F : Γ'.G.left ⟶ Γ.G.left}
    (hbc : Γ'.IsBaseChange Γ (algebraMap R R') F) {A : Subalgebra R (T → R)} {A' : Subalgebra R' (T → R')}
    (hA : IsHopfOrder A) (hA' : IsHopfOrder A') (e : R' ⊗[R] A ≃ₐ[R'] A')
    (he : ∀ (a : A) (t : T), (e (1 ⊗ₜ a)).1 t = algebraMap R R' (a.1 t))
    {j : Γ.G.left ⟶ Spec (CommRingCat.of A)} (hj : Γ.IsEmb A j) (hopen : IsOpenImmersion j)
    (hcov : Γ.TranslatesCover A j ⊤) :
    ∃ j' : Γ'.G.left ⟶ Spec (CommRingCat.of A'), Γ'.IsEmb A' j' ∧ IsOpenImmersion j' ∧
      Γ'.TranslatesCover A' j' ⊤ := by
  have hsq := isPullback_spec e
  set ψ : A →+* A' := e.toRingEquiv.toRingHom.comp
    (Algebra.TensorProduct.includeRight.toRingHom : A →+* R' ⊗[R] A) with hψ
  have hψt : ∀ (a : A) (t : T), (ψ a : T → R') t = algebraMap R R' ((a : T → R) t) := fun a t => he a t
  have hw : (F ≫ j) ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      Γ'.G.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')) := by
    rw [Category.assoc, hj.isOver, hbc.cart.w]
  let j' : Γ'.G.left ⟶ Spec (CommRingCat.of A') := hsq.lift (F ≫ j) Γ'.G.hom hw
  have hj1 : j' ≫ Spec.map (CommRingCat.ofHom ψ) = F ≫ j := hsq.lift_fst _ _ _
  have hj2 : j' ≫ Spec.map (CommRingCat.ofHom (algebraMap R' A')) = Γ'.G.hom := hsq.lift_snd _ _ _
  have hl : IsPullback F j' j (Spec.map (CommRingCat.ofHom ψ)) := by
    refine IsPullback.of_bot ?_ hj1.symm hsq
    rw [hj2, hj.isOver]
    exact hbc.cart
  have hj'open : IsOpenImmersion j' := MorphismProperty.of_isPullback hl hopen
  have hemb : Γ'.IsEmb A' j' := by
    refine ⟨hj2, fun t => ?_⟩
    apply hsq.hom_ext
    · rw [Category.assoc, hj1, pt_comp_emb hbc hj, ← Spec.map_comp]
      congr 1
      ext a
      simp [hψt]
    · rw [Category.assoc, hj2, ← Spec.map_comp, Over.w]
      congr 1
  refine ⟨j', hemb, hj'open, fun P => ?_⟩
  obtain ⟨t, g₀, -, hg₀⟩ := hcov (PrimeSpectrum.comap ψ P)
  have hcomm : ∀ a : A, transl hA' t⁻¹ (ψ a) = ψ (transl hA t⁻¹ a) := by
    intro a
    ext h
    simp [hψt]
  let P' : PrimeSpectrum A' := PrimeSpectrum.comap (transl hA' t⁻¹) P
  have hP' : j g₀ = Spec.map (CommRingCat.ofHom ψ) P' := by
    apply PrimeSpectrum.ext
    ext a
    have h1 := hg₀ (transl hA t⁻¹ a) a (fun h => by simp)
    change a ∈ (j g₀).asIdeal ↔ transl hA' t⁻¹ (ψ a) ∈ P.asIdeal
    rw [← h1, hcomm]
    rfl
  obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := j) (g := Spec.map (CommRingCat.ofHom ψ)) g₀ P' hP'
  have hg' : j' (hl.isoPullback.inv z) = P' := by
    rw [← Scheme.Hom.comp_apply, hl.isoPullback_inv_snd, hz]
  refine ⟨t, hl.isoPullback.inv z, trivial, fun f f' hf => ?_⟩
  rw [hg']
  change _ ↔ transl hA' t⁻¹ f' ∈ P.asIdeal
  have : transl hA' t⁻¹ f' = f := by
    ext h
    simp [hf]
  rw [this]

end GlobalTheory.CompanionTheory.Ar.BT.BaseChangeOrder

theorem GlobalTheory.CompanionTheory.Ar.BT.btOrder_baseChange : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left), Γ'.IsBaseChange Γ (algebraMap R R') F → (∃ d : R, algebraMap R R' d ≠ 0 ∧ ∀ f : T → R, d • f ∈ Γ.btOrder ⊤) ∧ Γ'.btOrder ⊤ = extOrder (algebraMap R R') (Γ.btOrder ⊤) := by
  intro R _ _ _ _ T _ _ Γ R' _ _ _ Γ' F hbc
  have hH := GlobalTheory.T.btOrder_isHopfOrder_noetherian R T Γ
  obtain ⟨j, hj, -⟩ := GlobalTheory.T.existsUnique_btOrder_embedding R T Γ
  obtain ⟨hopen, hcov⟩ := GlobalTheory.T.btOrder_embedding_open_immersion R T Γ j hj
  have hd : ∃ d : R, algebraMap R R' d ≠ 0 ∧ ∀ f : T → R, d • f ∈ Γ.btOrder ⊤ :=
    BaseChangeOrder.exists_smul_mem_of_separates _ _ (BaseChangeOrder.separates hbc hj)
  refine ⟨hd, ?_⟩
  obtain ⟨hH', e, he⟩ := GlobalTheory.T.hopf_order_scalar_extension R T R' (Γ.btOrder ⊤) hH hd
  obtain ⟨j', hj', hopen', hcov'⟩ := BaseChangeOrder.exists_emb hbc hH hH' e he hj hopen hcov
  exact GlobalTheory.T.btOrder_eq_of_hopf_embedding R' T Γ' _ hH' j' hj' hopen' hcov'
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ClosedInProductProjective
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

namespace GlobalTheory.CompanionTheory.Ar.SncBase.Segre

theorem isProjOver_of_closed_product : ∀ (K : Type) [Field K] (M r : ℕ) (X' : Scheme.{0}) (j : X' ⟶ pullback (PSpace.str K M) (PSpace.str K r)), IsClosedImmersion j → IsProjOver (j ≫ pullback.fst _ _ ≫ PSpace.str K M) := by
  intro K _ M r X' j hj
  have := hj
  exact GlobalTheory.ProjSpace.isProjOver_comp_of_isClosedImmersion j
    (GlobalTheory.ProjSpace.isProjOver_pullback_str K M r)

end GlobalTheory.CompanionTheory.Ar.SncBase.Segre
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentPointCmEigenFrameStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat
open GlobalTheory.CompanionTheory.Ar.Flat.Rep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.component_point_cm_eigen_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ), (Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → τ (H.rt : E) = H.rt0 → ∀ (F : Type) [Field F] (βF : c.F →+* F) (y : Sp F ⟶ Xo.XF c), y ≫ pullback.snd _ _ = spMap βF → Set.range y ⊆ U → ∀ (h : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j)) (σ : E →+* ℂ) (n : ℕ) (b : Fin n → Z.V), (Z.eig σ).IsFrameAt b ⟨_, h⟩ → ∃ v : Vecs y n, IsValFam Z y b v ∧ IsEigFrame Xo.univ.t.act (under y) (βF.comp (tauIn c σ)) v := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.Rep.valFam_eigFrame | exact GlobalTheory.CompanionTheory.Ar.Flat.Rep.valFam_eigFrame | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.Rep.valFam_eigFrame <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentSpecializationFieldExt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat
open GlobalTheory.CompanionTheory.Ar.Flat.Rep

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Flat.Rep

theorem lieValAt_spMap {X : Scheme.{0}} {Ω : Type} [Field Ω] {G : Over X} [GrpObj G] {ξ : Sp Ω ⟶ X}
    {V : Type} [AddCommGroup V] [Module Ω V] (M : LieModel G ξ V) (hξ : IsCptGen ξ) {F F' : Type} [Field F]
    [Field F'] (f : F →+* F') {z : Sp F ⟶ X} {z' : Sp F' ⟶ X} (hz : spMap f ≫ z = z') {e : V}
    {w : epsAt z ⟶ G} {w' : epsAt z' ⟶ G} (hw : w'.left = spMap (dualMap f) ≫ w.left) (h : M.ValAt z e w) :
    M.ValAt z' e w' := by
  letI : Algebra F F' := f.toAlgebra
  subst hz
  obtain ⟨hc, v, hext, hw0⟩ := h
  have hbot : ∀ x : PrimeSpectrum F, x.asIdeal = ⊥ := fun x =>
    (Ideal.eq_bot_or_top _).resolve_right x.isPrime.ne_top
  have hp : (spMap f) (IsLocalRing.closedPoint F') = IsLocalRing.closedPoint F :=
    PrimeSpectrum.ext ((hbot _).trans (hbot _).symm)
  have hcen : GlobalTheory.CompanionTheory.Ar.centre (spMap f ≫ z) = GlobalTheory.CompanionTheory.Ar.centre z := by
    change z ((spMap f) (IsLocalRing.closedPoint F')) = z (IsLocalRing.closedPoint F)
    rw [hp]
  have hc' : GlobalTheory.CompanionTheory.Ar.genPt ξ ⤳ GlobalTheory.CompanionTheory.Ar.centre (spMap f ≫ z) := hcen ▸ hc
  exact GlobalTheory.CompanionTheory.Ar.LieFib.valAt_base M z hc hc' v hext w' w hw hw0

theorem isValFam_spMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (F F' : Type) [Field F] [Field F'] (f : F →+* F') (y : Sp F ⟶ Xo.XF c) (y' : Sp F' ⟶ Xo.XF c), y' = spMap f ≫ y → ∀ (n : ℕ) (b : Fin n → Z.V) (v : Vecs y n) (v' : Vecs y' n), (∀ i, (v' i).left = spMap (dualMap f) ≫ (v i).left) → IsValFam Z y b v → IsValFam Z y' b v' := by
  intro E _ _ _ H D l Xo c O _ β Y U Z F F' _ _ f y y' hy n b v v' hv' hv
  subst hy
  simp only [GlobalTheory.CompanionTheory.Ar.Flat.Rep.IsValFam] at hv ⊢
  intro i
  obtain ⟨u, hval, t, ht1, ht2, ht3⟩ := hv i
  have hzz : spMap f ≫ (y ≫ Y.j) = (spMap f ≫ y) ≫ Y.j := (Category.assoc _ _ _).symm
  refine ⟨GlobalTheory.CompanionTheory.Ar.LieTangent.epsBase f hzz ≫ u, ?_, ?_⟩
  · exact lieValAt_spMap Z.M Z.gen f hzz rfl hval
  · simp only [GlobalTheory.CompanionTheory.Ar.Flat.SameVec]
    refine ⟨spMap (GlobalTheory.CompanionTheory.Ar.dualMap f) ≫ t, ?_, ?_, ?_⟩
    · rw [Category.assoc, ht1]
      simp only [ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap]
      rw [← Category.assoc, GlobalTheory.CompanionTheory.Ar.LieTangent.spec_dual_alg, Category.assoc]
    · rw [Category.assoc, ht2, hv' i]
    · rw [Category.assoc, ht3]
      try rfl

end GlobalTheory.CompanionTheory.Ar.Flat.Rep
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentSpecializationLatticeBasisStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.component_specialization_lattice_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (K : Type) [Field K] (y : Sp K ⟶ Xo.XF c) (h₁ : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j))
    (ψ : regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩ →+* K) (g : ℕ) (ℓ : Fin g → Z.V) (ρK : 𝓞 E →+* Module.End K (Fin g → K)),
    (∀ a : regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩, ValAt (Z.ξ₀ ≫ Y.j) (y ≫ Y.j) (a : Z.Ω) (ψ a)) → Z.M.lat.IsFrameAt ℓ ⟨_, h₁⟩ → Tied ℓ ψ Z.ρ ρK →
    ∃ (MU : LieModel Xo.univ.t.G (under y) (Fin g → K)) (MY : LieModel Y.t.G (y ≫ Y.j) (Fin g → K)),
      (∀ e, SameVec Y y (MU.pt e) (MY.pt e)) ∧
      (∀ x : Fin g → regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩, Z.M.ValAt (y ≫ Y.j) (comb ℓ x) (MY.pt (fun i => ψ (x i)))) ∧
      MU.IsActOf Xo.univ.t.act.act ρK ∧ MY.IsActOf Y.t.act.act ρK := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.CPoint.tangent_coords | exact GlobalTheory.CompanionTheory.Ar.Flat.CPoint.tangent_coords | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.CPoint.tangent_coords <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordDegreeBoundOfFlagStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coord_degree_bound_of_flag : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) [Fintype K] (J : K → Type)
    [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom]
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (V : Lat ξ Li) (r : ℕ) (b₀ : Fin r → Li)
    (m : ℕ) (i : Fin r) (a : K → ℤ) (e₀ : Ω),
    CharZero Ω → (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → 0 < m →
    LinearIndependent Ω b₀ → Sandwich M V b₀ m → (V.gr b₀ i).IsDegOn Set.univ y a e₀ →
    ∀ (L : Type) [Field L] [NumberField L] (w : (Σ k, J k) → L) (z : Sp (𝓞 L) ⟶ X),
      CoordsAt ξ y (spMap (algebraMap (𝓞 L) L) ≫ z) w → ∀ (B : HermitianBundle.{0} L) (MB : LieModel G z B.carrier)
      (F : SatFlag B r), (∀ j : Fin (r + 1), IsSubFibre M (flagStep Ω b₀ j.val) z MB (F.F j)) →
      ∀ c₀ : (k : K) → J k, (∀ k, w ⟨k, c₀ k⟩ ≠ 0) →
      ∃ (f : Fin i → B.carrier) (ef : Fin i → Li) (s : B.carrier) (e : Li) (t : Ω) (u : L)
        (vf : Fin i → (epsAt (spMap (algebraMap (𝓞 L) L) ≫ z) ⟶ G)) (ve : epsAt (spMap (algebraMap (𝓞 L) L) ≫ z) ⟶ G),
        (∀ j, f j ∈ F.F i.castSucc) ∧ LinearIndependent (𝓞 L) f ∧ s ∈ F.F i.succ ∧ s ∉ F.F i.castSucc ∧
        (∀ j, ef j ∈ flagStep Ω b₀ i) ∧ e ∈ flagStep Ω b₀ (i + 1) ∧
        (∀ j, M.ValAt _ (ef j) (vf j) ∧ MB.Lifts (algebraMap (𝓞 L) L) (𝟙 G.left) (f j) (vf j)) ∧
        M.ValAt _ e ve ∧ MB.Lifts (algebraMap (𝓞 L) L) (𝟙 G.left) s ve ∧
        IsCls b₀ i e t ∧ ValAt ξ (spMap (algebraMap (𝓞 L) L) ≫ z) (t / gen y a e₀ c₀) u ∧ u ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RootHt.Pick.pick | exact GlobalTheory.CompanionTheory.Ar.RootHt.Pick.pick | (intros; apply GlobalTheory.CompanionTheory.Ar.RootHt.Pick.pick <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFamilyExponentialLocallyStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_family_exponential_locally : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (g n : ℕ) (M : LieModel G (𝟙 (Sp R)) (Fin g → R)) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ)), Smooth G.hom → IsHolPts B ψ → ∀ b₀ ∈ B, ∃ ε : ℝ, 0 < ε ∧ ball b₀ ε ⊆ B ∧ Nonempty (FamExp G M (ball b₀ ε) ψ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.exists_famExp_near | exact GlobalTheory.CompanionTheory.Ar.Flat.exists_famExp_near | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.exists_famExp_near <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsGenericWeilPairingStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generic_weil_pairing : Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (S X : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s) (t : SAB H X) (f : S ⟶ X) (_ : SABMap o.t t f) (Ω : Type) [Field Ω] [CharZero Ω] (ξ₀ : Sp Ω ⟶ S) (n : ℕ), 1 ≤ n → FullTorsion t.G (ξ₀ ≫ f) n → (∃ ζ : Ω, IsPrimitiveRoot ζ n) → ∃ e, GenWeil t.G t.PP.L (ξ₀ ≫ f) n e := by
  first | exact @GlobalTheory.CompanionTheory.Ar.WeilObj.genWeil_of_obj | exact GlobalTheory.CompanionTheory.Ar.WeilObj.genWeil_of_obj | (intros; apply GlobalTheory.CompanionTheory.Ar.WeilObj.genWeil_of_obj <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FibreLatticeBaseChangeConjStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_lattice_base_change_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X' : Scheme.{0}) (t : SAB H X) (t' : SAB H X') (f : X' ⟶ X) (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (R R' : RiemLat E g Λ) (z : Sp ℂ ⟶ X'), (Nonempty (SABMap t' t f) → (FibreLat t' z R ↔ FibreLat t (z ≫ f) R)) ∧ ((∀ x, R'.P x = star (R.P x)) → R'.Hm = R.Hm.map (starRingEnd ℂ) → (∀ a x, R'.B a x = star (R.B a (star x))) → FibreLat t' z R → FibreLat t' (spMap (starRingEnd ℂ) ≫ z) R') := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.FibreMove.fibreLat_move | exact GlobalTheory.CompanionTheory.Ar.Cusp.FibreMove.fibreLat_move | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.FibreMove.fibreLat_move <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FormalGermDimensionUnique
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.GermUniv

theorem germ_chart_universal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] [IsLocalRing S] (x : Sp S ⟶ X0) (d : ℕ) (g : GermAt t x d), (∀ (d₂ : ℕ) (_ : GermAt t x d₂), d = d₂) ∧ ∀ (J : Type) [Finite J] (m : ℕ) (y : overAt x (Jet S J m) ⟶ t.G), homAt x (jetAug : Jet S J m →ₐ[S] S) ≫ y = 1 → ∃! χ : Jet S (Fin 1 × Fin d) m →ₐ[S] Jet S J m, (∀ q, (jetAug : Jet S J m →ₐ[S] S) (χ (Ideal.Quotient.mk _ (MvPolynomial.X q))) = 0) ∧ y = homAt x χ ≫ g.x m :=
  PositivityTheory.HtPt.Cd.germ_univ

end GlobalTheory.CompanionTheory.Ar.GermUniv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FormalGermLieBasis
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.GermLie

theorem germ_lie : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x : Sp S ⟶ X0) (d : ℕ) (g : GermAt t x d) (V : Type) [AddCommGroup V] [Module S V] (M : GlobalTheory.CompanionTheory.Ar.LieModel t.G x V), ∃ e : V ≃ₗ[S] (Fin d → S), (∀ v, IsCombAtG t x g.tg (e v) (M.pt v).left) ∧ ∀ r : 𝓞 E →+* Module.End S V, M.IsActOf t.act.act r → ∀ a v, e (r a v) = (rho g.B a).mulVec (e v) :=
  PositivityTheory.HtPt.Cd.germ_lie

end GlobalTheory.CompanionTheory.Ar.GermLie
end

