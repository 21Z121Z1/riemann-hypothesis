import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompletionPointClosedPointMemOfSmooth
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocGenOfTrivial
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.OpensRangeChartYSupOpensRangeChartZ
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPushoutQuotientMap
section
namespace GlobalTheory.NilpotentLift

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry in

theorem _root_.GlobalTheory.NilpotentLift.isPushout_quotient_map {A : Type} [CommRing A] (J : Ideal A) {B : CommRingCat.{0}}
    (σ : CommRingCat.of A ⟶ B) :
    IsPushout σ (CommRingCat.ofHom (Ideal.Quotient.mk J))
      (CommRingCat.ofHom (Ideal.Quotient.mk (J.map σ.hom)))
      (CommRingCat.ofHom (Ideal.quotientMap (J.map σ.hom) σ.hom Ideal.le_comap_map)) := by
  refine IsPushout.of_isColimit' (CommSq.mk ?_) ?_
  · ext a
    simp [Ideal.quotientMap_mk]
  · have key : ∀ s : PushoutCocone σ (CommRingCat.ofHom (Ideal.Quotient.mk J)),
        J.map σ.hom ≤ RingHom.ker s.inl.hom := by
      intro s
      rw [Ideal.map_le_iff_le_comap]
      intro j hj
      have h := congrArg (fun φ => φ.hom j) s.condition
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
      simp [RingHom.mem_ker, h, Ideal.Quotient.eq_zero_iff_mem.mpr hj]
    refine PushoutCocone.IsColimit.mk _
      (fun s => CommRingCat.ofHom (Ideal.Quotient.lift _ s.inl.hom (fun a ha => key s ha)))
      (fun s => ?_) (fun s => ?_) (fun s m h₁ _ => ?_)
    · ext b
      exact Ideal.Quotient.lift_mk (J.map σ.hom) s.inl.hom (fun a ha => key s ha)
    · ext a
      have h := congrArg (fun φ => φ.hom a) s.condition
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
      exact (Ideal.Quotient.lift_mk (J.map σ.hom) s.inl.hom (fun a ha => key s ha)).trans h
    · ext b
      have h := congrArg (fun φ => φ.hom b) h₁
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
      exact h.trans (Ideal.Quotient.lift_mk (J.map σ.hom) s.inl.hom (fun a ha => key s ha)).symm

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry in

theorem _root_.GlobalTheory.NilpotentLift.main : ∀ (A : Type) [CommRing A] (J : Ideal A), IsNilpotent J →
    ∀ (G Y : Over (Spec (CommRingCat.of A))) [Smooth G.hom] [IsAffine Y.left]
      (f₀ : pullback Y.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) ⟶ G.left),
      f₀ ≫ G.hom = pullback.fst _ _ ≫ Y.hom →
      (∃ W : G.left.Opens, IsAffineOpen W ∧ f₀ ⁻¹ᵁ W = ⊤) →
      ∃ f : Y ⟶ G, pullback.fst _ _ ≫ f.left = f₀ := by
  intro A _ J hJ G Y _ _ f₀ hf₀ hW
  obtain ⟨W, hWaff, hWtop⟩ := hW
  set e := Y.left.isoSpec with he
  obtain ⟨σ, hσdef⟩ : ∃ σ : CommRingCat.of A ⟶ Γ(Y.left, ⊤),
      σ = (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ Y.hom.appTop := ⟨_, rfl⟩
  have hσ : e.hom ≫ Spec.map σ = Y.hom := by
    have h1 := Scheme.isoSpec_hom_naturality Y.hom
    rw [Scheme.isoSpec_Spec_hom] at h1
    rw [hσdef, Spec.map_comp, ← Category.assoc, he, h1, Category.assoc, ← Spec.map_comp, Iso.inv_hom_id,
      Spec.map_id, Category.comp_id]
  have hσ' : e.inv ≫ Y.hom = Spec.map σ := by
    rw [← hσ, Iso.inv_hom_id_assoc]
  have hPB := isPullback_SpecMap_of_isPushout _ _ _ _ (_root_.GlobalTheory.NilpotentLift.isPushout_quotient_map J σ)
  have hPB' : IsPullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J.map σ.hom))) ≫ e.inv)
      (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (J.map σ.hom) σ.hom Ideal.le_comap_map)))
      Y.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) :=
    IsPullback.of_iso hPB (Iso.refl _) e.symm (Iso.refl _) (Iso.refl _)
      (by rw [Iso.refl_hom, Category.id_comp, Iso.symm_hom])
      (by rw [Iso.refl_hom, Iso.refl_hom, Category.id_comp, Category.comp_id])
      (by rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, hσ'])
      (by rw [Iso.refl_hom, Iso.refl_hom, Category.id_comp, Category.comp_id])
  have hx₀ : (hPB'.isoPullback.hom ≫ f₀) ≫ G.hom =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J.map σ.hom))) ≫ Spec.map σ := by
    rw [Category.assoc, hf₀, IsPullback.isoPullback_hom_fst_assoc, Category.assoc, hσ']
  obtain ⟨x, hx, hxs⟩ := _root_.GlobalTheory.exists_lift_of_smooth_of_isAffineOpen G.hom
    (isAffineOpen_top (Spec (CommRingCat.of A))) hWaff le_top
    (CommRingCat.ofHom (Ideal.Quotient.mk (J.map σ.hom))) (Spec.map σ) (hPB'.isoPullback.hom ≫ f₀) hx₀
    (by simp)
    (by
      rintro _ ⟨y, rfl⟩
      have : hPB'.isoPullback.hom y ∈ f₀ ⁻¹ᵁ W := by rw [hWtop]; trivial
      simpa using this)
    (by
      intro R' A' _ _ _ _ _ _ π' hπ' φ
      have hsurj : Function.Surjective π' := by
        intro c
        obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective c
        exact ⟨b, (hπ' b).trans hb⟩
      have hnil : IsNilpotent (RingHom.ker π'.toRingHom) := by
        obtain ⟨n, hn⟩ := hJ
        refine ⟨n, eq_bot_iff.mpr ?_⟩
        have hle : RingHom.ker π'.toRingHom ≤ J.map σ.hom := fun b hb =>
          Ideal.Quotient.eq_zero_iff_mem.mp ((hπ' b).symm.trans hb)
        calc _ ≤ (J.map σ.hom) ^ n := Ideal.pow_right_mono hle n
          _ = ⊥ := by rw [← Ideal.map_pow, hn, Ideal.zero_eq_bot, Ideal.map_bot]
      exact ⟨_, Algebra.FormallySmooth.comp_liftOfSurjective φ π' hsurj hnil⟩)
  refine ⟨Over.homMk (e.hom ≫ x) (by rw [Category.assoc, hxs, hσ]), ?_⟩
  rw [← cancel_epi hPB'.isoPullback.hom]
  show hPB'.isoPullback.hom ≫ pullback.fst _ _ ≫ e.hom ≫ x = hPB'.isoPullback.hom ≫ f₀
  rw [IsPullback.isoPullback_hom_fst_assoc, Category.assoc, Iso.inv_hom_id_assoc, hx]

end GlobalTheory.NilpotentLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSmoothAtOfSmoothQuotientPow
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SmoothLimit

section Ring
open TensorProduct IsLocalRing

variable {V A S C : Type} [CommRing V] [CommRing A] [CommRing S] [CommRing C] [Algebra V A]
  [Algebra A S] [Algebra V S] [IsScalarTower V A S] [Algebra V C]

theorem flat_and_formallySmooth_tensor (M : Submonoid A) [IsLocalization M S]
    [Algebra.Smooth C (C ⊗[V] A)] :
    Module.Flat C (C ⊗[V] S) ∧ Algebra.FormallySmooth C (C ⊗[V] S) := by
  let φ : C ⊗[V] A →ₐ[C] C ⊗[V] S :=
    Algebra.TensorProduct.map (AlgHom.id C C) (IsScalarTower.toAlgHom V A S)
  letI := φ.toRingHom.toAlgebra
  haveI : IsScalarTower C (C ⊗[V] A) (C ⊗[V] S) :=
    IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  haveI := IsLocalization.tensorProduct_tensorProduct_right V C M S (by
    ext a; simp [RingHom.algebraMap_toAlgebra, φ])
  haveI : Module.Flat (C ⊗[V] A) (C ⊗[V] S) :=
    IsLocalization.flat _ (M.map (Algebra.TensorProduct.includeRight (R := V) (A := C)))
  haveI : Algebra.FormallySmooth (C ⊗[V] A) (C ⊗[V] S) :=
    .of_isLocalization (M.map (Algebra.TensorProduct.includeRight (R := V) (A := C)))
  exact ⟨.trans C (C ⊗[V] A) _, .comp C (C ⊗[V] A) _⟩

theorem isSmoothAt_of_smooth_quotient_pow [IsLocalRing V] [IsNoetherianRing V]
    [Algebra.FiniteType V A]
    (h : ∀ e : ℕ, Algebra.Smooth (V ⧸ maximalIdeal V ^ (e + 1))
      ((V ⧸ maximalIdeal V ^ (e + 1)) ⊗[V] A))
    (q : Ideal A) [q.IsPrime] (hq : q.comap (algebraMap V A) = maximalIdeal V) :
    Algebra.IsSmoothAt V q := by
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing V A
  haveI : Algebra.FinitePresentation V A := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  let S := Localization.AtPrime q
  have hle : (maximalIdeal V).map (algebraMap V S) ≤ maximalIdeal S := by
    rw [Ideal.map_le_iff_le_comap, IsScalarTower.algebraMap_eq V A S, ← Ideal.comap_comap,
      show (maximalIdeal S).comap (algebraMap A S) = q from
        Localization.AtPrime.under_maximalIdeal, hq]
  haveI : IsLocalHom (algebraMap V S) :=
    ((IsLocalRing.local_hom_TFAE (algebraMap V S)).out 2 0).mp hle
  haveI : Module.Flat V S := by
    refine LocalFlat.flat_of_relationsLift S (I := maximalIdeal V)
      (hle.trans (IsLocalRing.maximalIdeal_le_jacobson _)) fun n => ?_
    rcases n with _ | e
    · intro F _ _ f x _
      exact LocalFlat.range_lTensor_le LinearMap.id _ (by simp) ⟨x, by simp⟩
    · haveI := h e
      haveI := (flat_and_formallySmooth_tensor (V := V) (S := S)
        (C := V ⧸ maximalIdeal V ^ (e + 1)) q.primeCompl).1
      refine LocalFlat.relationsLift_of_flat (C := V ⧸ maximalIdeal V ^ (e + 1))
        Ideal.Quotient.mk_surjective Ideal.mk_ker
        (TensorProduct.mk V (V ⧸ maximalIdeal V ^ (e + 1)) S 1)
        (TensorProduct.mk_surjective _ _ _ Ideal.Quotient.mk_surjective) ?_
      exact LinearMap.ker_tensorProductMk _
  haveI : Algebra.Smooth (ResidueField V) (ResidueField V ⊗[V] A) := by
    haveI := h 0
    let C := V ⧸ maximalIdeal V ^ (0 + 1)
    letI : Algebra C (ResidueField V) :=
      (Ideal.Quotient.factor (S := maximalIdeal V ^ (0 + 1)) (T := maximalIdeal V)
        (by simp)).toAlgebra
    haveI : IsScalarTower V C (ResidueField V) := IsScalarTower.of_algebraMap_eq fun _ => rfl
    exact .of_equiv (Algebra.TensorProduct.cancelBaseChange V C (ResidueField V) (ResidueField V) A)
  haveI := (flat_and_formallySmooth_tensor (V := V) (S := S)
        (C := ResidueField V) q.primeCompl).2
  exact Algebra.FormallySmooth.of_formallySmooth_residueField_tensor (R := V) (S := S) (P := A)
    q.primeCompl

end Ring

theorem mem_smoothLocus {V : Type} [CommRing V] [IsLocalRing V] [IsNoetherianRing V]
    {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of V)) [LocallyOfFinitePresentation f]
    (h : ∀ e, Smooth (pullback.snd f (thick V (IsLocalRing.maximalIdeal V) e)))
    (x : X) (hx : f x = IsLocalRing.closedPoint V) : x ∈ f.smoothLocus := by
  wlog hX : ∃ S, X = Spec S generalizing f X
  · obtain ⟨i, y, rfl⟩ := X.affineCover.exists_eq x
    have H := this (X.affineCover.f i ≫ f) (fun e => by
      haveI := h e
      rw [← pullbackRightPullbackFstIso_inv_snd_snd]
      infer_instance) y (by simpa using hx) ⟨_, rfl⟩
    rwa [← Scheme.Hom.preimage_smoothLocus_eq] at H
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  letI := φ.hom.toAlgebra
  haveI : Algebra.FinitePresentation V S :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation) (φ := φ)).mp ‹_›
  have hs (e : ℕ) : Algebra.Smooth (V ⧸ IsLocalRing.maximalIdeal V ^ (e + 1))
      (TensorProduct V (V ⧸ IsLocalRing.maximalIdeal V ^ (e + 1)) S) := by
    have H := isPullback_SpecMap_of_isPushout _ _ _ _
      (CommRingCat.isPushout_tensorProduct V (V ⧸ IsLocalRing.maximalIdeal V ^ (e + 1)) S)
    have e1 := H.flip.isoPullback_hom_snd
    have h1 : Smooth (H.flip.isoPullback.hom ≫ pullback.snd _ _) := by
      haveI : Smooth (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap V S)))
        (Spec.map (CommRingCat.ofHom
          (algebraMap V (V ⧸ IsLocalRing.maximalIdeal V ^ (e + 1)))))) := h e
      infer_instance
    rw [e1, HasRingHomProperty.Spec_iff (P := @Smooth)] at h1
    exact RingHom.smooth_algebraMap.mp h1
  haveI : x.asIdeal.IsPrime := PrimeSpectrum.isPrime x
  haveI := isSmoothAt_of_smooth_quotient_pow hs x.asIdeal (congrArg PrimeSpectrum.asIdeal hx)
  obtain ⟨g, hg, hsm⟩ := Algebra.IsSmoothAt.exists_notMem_smooth V x.asIdeal
  let j : Spec (CommRingCat.of (Localization.Away g)) ⟶ Spec S :=
    Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g)))
  haveI : IsOpenImmersion j := IsOpenImmersion.of_isLocalization g
  haveI : Smooth (j ≫ Spec.map φ) := by
    rw [← Spec.map_comp, HasRingHomProperty.Spec_iff (P := @Smooth)]
    exact RingHom.smooth_algebraMap.mpr hsm
  obtain ⟨y, rfl⟩ : x ∈ Set.range (PrimeSpectrum.comap (algebraMap S (Localization.Away g))) := by
    rw [PrimeSpectrum.localization_away_comap_range _ g]
    exact hg
  have := (j ≫ Spec.map φ).smoothLocus_eq_top.ge (Set.mem_univ y)
  rwa [← Scheme.Hom.preimage_smoothLocus_eq] at this

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsNoetherianRing V] (B : Over (Spec (CommRingCat.of V))) [IsProper B.hom], (∀ e, Smooth (thickObj V (IsLocalRing.maximalIdeal V) e B).hom) → Smooth B.hom := by
  intro V _ _ _ _ B _ h
  haveI : LocallyOfFinitePresentation B.hom := inferInstance
  rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← top_le_iff]
  intro x _
  by_contra hx
  have hc : IsClosed (B.hom '' (B.hom.smoothLocus : Set B.left)ᶜ) :=
    B.hom.isClosedMap _ B.hom.smoothLocus.2.isClosed_compl
  obtain ⟨y, hy, hy'⟩ := (IsLocalRing.specializes_closedPoint (R := V) (B.hom x)).mem_closed hc ⟨x, hx, rfl⟩
  exact hy (mem_smoothLocus B.hom h y hy')

end GlobalTheory.SmoothLimit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.KTrivExternalTensorPowerLineBundle
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BoxKernel

open GlobalTheory.KerPow

variable {X X' Y B : Scheme.{0}} {L : LB X} {K J : Type} [Fintype K] [Fintype J]

theorem hasGen_flat (F : J → (X' ⟶ X)) {ψ : K → (Y ⟶ X')} {ε : K → ℤ}
    (H : HasGen (LB.LinComb L F (fun _ => 1)) ψ ε) :
    HasGen L (K := K × J) (fun q => ψ q.1 ≫ F q.2) (fun q => ε q.1) := by
  have le : ∀ (j : K × J → L.ι) (y : Y), y ∈ LB.wchart L (K := K × J) (fun q => ψ q.1 ≫ F q.2) j →
      y ∈ LB.wchart (LB.LinComb L F (fun _ => 1)) ψ (fun k i => j (k, i)) := fun j y hy =>
    Set.mem_iInter.2 fun k => Set.mem_iInter.2 fun i => Set.mem_iInter.1 hy (k, i)
  refine gen_transfer (M := LB.LinComb (LB.LinComb L F (fun _ => 1)) ψ ε)
    (M' := LB.LinComb L (K := K × J) (fun q => ψ q.1 ≫ F q.2) (fun q => ε q.1))
    (fun j k i => j (k, i)) (fun j y hy => le j y hy) (fun j j' y hj hj' => ?_) H
  refine (gm_linComb L (K := K × J) (fun q => ψ q.1 ≫ F q.2) (fun q => ε q.1) (𝟙 Y) y j j' hj hj').trans
    (Eq.trans ?_ (gm_linComb (LB.LinComb L F (fun _ => 1)) ψ ε (𝟙 Y) y _ _ (le j y hj) (le j' y hj')).symm)
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun k _ => ?_
  refine Eq.trans ?_ (congrArg (· ^ ε k) (gm_linComb L F (fun _ => 1) (𝟙 Y ≫ ψ k) y (fun i => j (k, i))
    (fun i => j' (k, i)) (Set.mem_iInter.1 (le j y hj) k) (Set.mem_iInter.1 (le j' y hj') k)).symm)
  simp only [zpow_one, Category.assoc, Finset.prod_zpow]

theorem gen_of_chart {M : LB Y} (hM : M.IsLB) (i₀ : M.ι) (h : ∀ y, y ∈ M.U i₀) : ∃ t : LB.Gen M, t.IsGen := by
  refine ⟨⟨fun i => res (le_inf le_rfl (fun y _ => h y) : M.U i ≤ M.U i ⊓ M.U i₀) (M.g i i₀)⟩, fun i j => ?_⟩
  have := LB.res_cocycle hM i j i₀ (W := M.U i ⊓ M.U j) le_rfl (le_inf inf_le_right fun y _ => h y)
    (le_inf inf_le_left fun y _ => h y)
  refine (LB.res_res _ _ _).trans (this.symm.trans (congrArg₂ (· * ·) ?_ (LB.res_res _ _ _).symm))
  exact unit_ext fun y hy => gm_res _ y _ hy _

theorem locGen_base (hL : L.IsLB) (π : Y ⟶ B) (b : K → (B ⟶ X)) (ε : K → ℤ) :
    LocGen L π (fun k => π ≫ b k) ε := by
  intro p
  choose j hj using fun k => exists_chart hL (b k p)
  refine ⟨LB.wchart L b j, Set.mem_iInter.2 hj, gen_of_chart (LB.isLB_linComb hL _ _) j fun y => ?_⟩
  exact Set.mem_iInter.2 fun k => Set.mem_iInter.1 y.2 k

theorem locGen_flat (F : J → (X' ⟶ X)) {π : Y ⟶ B} {ψ : K → (Y ⟶ X')} {ε : K → ℤ}
    (H : LocGen (LB.LinComb L F (fun _ => 1)) π ψ ε) :
    LocGen L (K := K × J) π (fun q => ψ q.1 ≫ F q.2) (fun q => ε q.1) := by
  intro p
  obtain ⟨V, hV, t⟩ := H p
  exact ⟨V, hV, (hasGen_flat F t).pull (𝟙 _) fun q => by rw [Category.id_comp, Category.assoc]⟩

end GlobalTheory.BoxKernel

namespace GlobalTheory

open KerPow BoxKernel in

theorem kTriv_boxLB : ∀ (S : Scheme.{0}) (G' G : Over S) [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G]
    (j : ℕ) (p : IsPowGrp G' G j) (L : LB G.left), L.IsLB → KTriv G L → KTriv G' (boxLB L p.pr) := by
  intro S G' G _ _ _ _ j p L hL hK R _ t x hx
  classical
  have H : LocGen (boxLB L p.pr) (K := Fin 2) (fst (Over.mk t) G').left
      ![(translPt G' x).left, (snd (Over.mk t) G').left] ![1, -1] := (locGen_iff _ _ _).1 hx
  clear hx
  generalize Over.mk t = T at x H
  refine p.lim.hom_ext fun ⟨i⟩ => ?_
  have := p.hom
  show x ≫ p.pr i = (1 : T ⟶ G') ≫ p.pr i
  rw [MonObj.one_comp]
  let u : G ⟶ G' := p.lim.lift (Fan.mk G fun i' => if i' = i then 𝟙 G else 1)
  have hu : ∀ i', u ≫ p.pr i' = if i' = i then 𝟙 G else 1 := fun i' => p.lim.fac _ ⟨i'⟩
  let a : Fin 2 → (T ⊗ G ⟶ G') := ![(fst T G ≫ x) * (snd T G ≫ u), snd T G ≫ u]
  have H₁ := H.baseChange (π' := (fst T G).left) (T ◁ u).left (𝟙 _)
    ((congrArg (fun q => q.left) (whiskerLeft_fst T u)).trans (Category.comp_id _).symm)
    (φ' := fun k => (a k).left) (fun k => by
      fin_cases k
      · refine congrArg (fun q => q.left) (show T ◁ u ≫ ((fst T G' ≫ x) * snd T G') = (fst T G ≫ x) * (snd T G ≫ u) from ?_)
        rw [MonObj.comp_mul, whiskerLeft_fst_assoc, whiskerLeft_snd]
      · exact congrArg (fun q => q.left) (whiskerLeft_snd T u))
  let b : Fin 2 × Fin j → (T ⟶ G) := fun q => ![x ≫ p.pr q.2, 1] q.1
  have H₂ := locGen_base hL (fst T G).left (fun q => (b q).left)
    (fun q => if q.2 = i then 0 else (![1, -1] : Fin 2 → ℤ) q.1)
  refine eq_one_of_locGen hK _ ((locGen_flat _ H₁).comb hL H₂ fun U _ h => ?_)
  have e₀ : ∀ k i', i' ≠ i → (a k).left ≫ (p.pr i').left = (fst T G).left ≫ (b (k, i')).left := fun k i' hi => by
    refine congrArg (fun q => q.left) (show a k ≫ p.pr i' = fst T G ≫ b (k, i') from ?_)
    fin_cases k
    · show ((fst T G ≫ x) * (snd T G ≫ u)) ≫ p.pr i' = fst T G ≫ x ≫ p.pr i'
      rw [MonObj.mul_comp, Category.assoc, Category.assoc, hu, if_neg hi, MonObj.comp_one, _root_.mul_one]
    · show (snd T G ≫ u) ≫ p.pr i' = fst T G ≫ 1
      rw [Category.assoc, hu, if_neg hi, MonObj.comp_one, MonObj.comp_one]
  have e₁ : ∀ k, (a k).left ≫ (p.pr i).left =
      (![(translPt G (x ≫ p.pr i)).left, (snd T G).left] : Fin 2 → _) k := fun k => by
    fin_cases k
    · refine congrArg (fun q => q.left)
        (show ((fst T G ≫ x) * (snd T G ≫ u)) ≫ p.pr i = (fst T G ≫ x ≫ p.pr i) * snd T G from ?_)
      rw [MonObj.mul_comp, Category.assoc, Category.assoc, hu, if_pos rfl, Category.comp_id]
    · refine congrArg (fun q => q.left) (show (snd T G ≫ u) ≫ p.pr i = snd T G from ?_)
      rw [Category.assoc, hu, if_pos rfl, Category.comp_id]
  rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Finset.prod_eq_single i (fun i' _ hi => ?_) (fun hi => (hi (Finset.mem_univ _)).elim)]
  · simp only [if_true, zpow_zero, inv_one, _root_.mul_one, e₁]
  · simp only [if_neg hi, e₀ k i' hi, mul_inv_cancel]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LiftMulHomPullbackFst
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SmoothLocusBaseChange

theorem lift_mul_pullback_fst {S S' : Scheme.{0}} (φ : S' ⟶ S) (G : Over S) [GrpObj G]
    {Z : Over S'} (x y : Z ⟶ (Over.pullback φ).obj G) {Z₀ : Over S} (i : Z₀.left ⟶ Z.left)
    (a b : Z₀ ⟶ G) (ha : a.left = i ≫ x.left ≫ pullback.fst _ _)
    (hb : b.left = i ≫ y.left ≫ pullback.fst _ _) :
    (lift a b ≫ μ[G]).left =
      i ≫ (lift x y ≫ μ[(Over.pullback φ).obj G]).left ≫ pullback.fst _ _ := by
  have key : (lift a b).left = i ≫ (lift x y).left ≫
      (Functor.LaxMonoidal.μ (Over.pullback φ) G G).left ≫ pullback.fst (G ⊗ G).hom φ := by
    apply pullback.hom_ext
    · have h1 : (lift a b).left ≫ pullback.fst _ _ = a.left := congrArg (·.left) (lift_fst a b)
      have h2 : (lift x y).left ≫ pullback.fst _ _ = x.left := congrArg (·.left) (lift_fst x y)
      refine (h1.trans ha).trans ?_
      rw [← h2]
      simp only [Category.assoc]
      erw [Over.μ_pullback_left_fst_fst]
    · have h1 : (lift a b).left ≫ pullback.snd _ _ = b.left := congrArg (·.left) (lift_snd a b)
      have h2 : (lift x y).left ≫ pullback.snd _ _ = y.left := congrArg (·.left) (lift_snd x y)
      refine (h1.trans hb).trans ?_
      rw [← h2]
      simp only [Category.assoc]
      erw [Over.μ_pullback_left_fst_snd]
  rw [Over.comp_left, key]
  simp only [Functor.obj.μ_def, Over.comp_left, Category.assoc, Over.pullback_map_left]
  erw [pullback.lift_fst]

theorem lift_mul_hom_pullback_fst {S S' : Scheme.{0}} (φ : S' ⟶ S) (G : Over S) [GrpObj G]
    {E : Over S'} [MonObj E] (q : E ⟶ (Over.pullback φ).obj G) [IsMonHom q]
    {Z : Over S'} (x y : Z ⟶ E) {Z₀ : Over S} (i : Z₀.left ⟶ Z.left)
    (a b : Z₀ ⟶ G) (ha : a.left = i ≫ x.left ≫ q.left ≫ pullback.fst _ _)
    (hb : b.left = i ≫ y.left ≫ q.left ≫ pullback.fst _ _) :
    (lift a b ≫ μ[G]).left =
      i ≫ (lift x y ≫ μ[E]).left ≫ q.left ≫ pullback.fst _ _ := by
  rw [lift_mul_pullback_fst φ G (x ≫ q) (y ≫ q) i a b (by simpa using ha) (by simpa using hb)]
  have : lift (x ≫ q) (y ≫ q) ≫ μ[(Over.pullback φ).obj G] = (lift x y ≫ μ[E]) ≫ q := by
    rw [Category.assoc, IsMonHom.mul_hom, lift_map_assoc]
  rw [this, Over.comp_left, Category.assoc]

open GlobalTheory.WeierstrassCurve in

theorem main : ∀ (R R' : Type) [CommRing R] [CommRing R'] [IsDomain R'] [IsNoetherianRing R'] (f : R →+* R') (W : WeierstrassCurve R) (U : (GlobalTheory.WeierstrassCurve.scheme W).Opens), (∀ (k : Type) [Field k] (ρ : R →+* k) (P : Fin 3 → k) (h : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) P), ⊤ ≤ GlobalTheory.WeierstrassCurve.ptHom W ρ P h ⁻¹ᵁ U ↔ (W.map ρ).toProjective.Nonsingular P) → Smooth (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W) → GeometricallyIntegral (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W) → ∀ [GrpObj (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W))], (∀ (k : Type) [Field k] (ρ : R →+* k) (x y : Over.mk (Spec.map (CommRingCat.ofHom ρ)) ⟶ (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W))) (P Q : Fin 3 → k) (hP : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) P) (hQ : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) Q), x.left ≫ U.ι = GlobalTheory.WeierstrassCurve.ptHom W ρ P hP → y.left ≫ U.ι = GlobalTheory.WeierstrassCurve.ptHom W ρ Q hQ → ∃ h : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) ((W.map ρ).toProjective.add P Q), (lift x y ≫ μ[(Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W))]).left ≫ U.ι = GlobalTheory.WeierstrassCurve.ptHom W ρ _ h) → ∃ (U' : (GlobalTheory.WeierstrassCurve.scheme (W.map f)).Opens) (_ : GrpObj (Over.mk (U'.ι ≫ GlobalTheory.WeierstrassCurve.toSpec (W.map f)))) (e : (Over.mk (U'.ι ≫ GlobalTheory.WeierstrassCurve.toSpec (W.map f))) ≅ (Over.pullback (Spec.map (CommRingCat.ofHom f))).obj (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W))), IsMonHom e.hom ∧ e.hom.left ≫ pullback.fst _ _ ≫ U.ι = U'.ι ≫ GlobalTheory.WeierstrassCurve.mapHom W f rfl ∧ (∀ (k : Type) [Field k] (ρ : R' →+* k) (P : Fin 3 → k) (h : GlobalTheory.WeierstrassCurve.IsUnimodularSol ((W.map f).map ρ) P), ⊤ ≤ GlobalTheory.WeierstrassCurve.ptHom (W.map f) ρ P h ⁻¹ᵁ U' ↔ ((W.map f).map ρ).toProjective.Nonsingular P) ∧ (∀ (k : Type) [Field k] (ρ : R' →+* k) (x y : Over.mk (Spec.map (CommRingCat.ofHom ρ)) ⟶ (Over.mk (U'.ι ≫ GlobalTheory.WeierstrassCurve.toSpec (W.map f)))) (P Q : Fin 3 → k) (hP : GlobalTheory.WeierstrassCurve.IsUnimodularSol ((W.map f).map ρ) P) (hQ : GlobalTheory.WeierstrassCurve.IsUnimodularSol ((W.map f).map ρ) Q), x.left ≫ U'.ι = GlobalTheory.WeierstrassCurve.ptHom (W.map f) ρ P hP → y.left ≫ U'.ι = GlobalTheory.WeierstrassCurve.ptHom (W.map f) ρ Q hQ → ∃ h : GlobalTheory.WeierstrassCurve.IsUnimodularSol ((W.map f).map ρ) (((W.map f).map ρ).toProjective.add P Q), (lift x y ≫ μ[(Over.mk (U'.ι ≫ GlobalTheory.WeierstrassCurve.toSpec (W.map f)))]).left ≫ U'.ι = GlobalTheory.WeierstrassCurve.ptHom (W.map f) ρ _ h) := by
  intro R R' _ _ _ _ f W U hU _ _ _ hmul
  let φ := Spec.map (CommRingCat.ofHom f)
  let U' : (scheme (W.map f)).Opens := mapHom W f rfl ⁻¹ᵁ U
  have hpb : IsPullback (mapHom W f rfl ∣_ U) (U'.ι ≫ toSpec (W.map f)) (U.ι ≫ toSpec W) φ :=
    (isPullback_morphismRestrict (mapHom W f rfl) U).paste_vert (isPullback_mapHom W f rfl)
  let e : Over.mk (U'.ι ≫ toSpec (W.map f)) ≅
      (Over.pullback φ).obj (Over.mk (U.ι ≫ toSpec W)) :=
    Over.isoMk hpb.isoPullback hpb.isoPullback_hom_snd
  have he : e.hom.left ≫ pullback.fst (U.ι ≫ toSpec W) φ = mapHom W f rfl ∣_ U :=
    hpb.isoPullback_hom_fst
  have he' : e.hom.left ≫ pullback.fst (U.ι ≫ toSpec W) φ ≫ U.ι = U'.ι ≫ mapHom W f rfl := by
    rw [← Category.assoc, he]
    exact morphismRestrict_ι _ _
  let : GrpObj (Over.mk (U'.ι ≫ toSpec (W.map f))) := GrpObj.ofIso e.symm
  have hinv : IsMonHom e.symm.hom := isMonHom_ofIso e.symm
  have hhom : IsMonHom e.hom := inferInstanceAs (IsMonHom e.symm.inv)
  refine ⟨U', inferInstance, e, hhom, he', ?_, ?_⟩
  · intro k _ ρ P h
    have := hU k (ρ.comp f) P (h.comp_of_map_eq rfl)
    rw [← ptHom_mapHom W f rfl ρ P h, Scheme.Hom.comp_preimage] at this
    exact this
  · intro k _ ρ x y P Q hP hQ hx hy
    have hw : ∀ z : Over.mk (Spec.map (CommRingCat.ofHom ρ)) ⟶
        Over.mk (U'.ι ≫ toSpec (W.map f)),
        (z.left ≫ e.hom.left ≫ pullback.fst (U.ι ≫ toSpec W) φ) ≫ U.ι ≫ toSpec W =
          Spec.map (CommRingCat.ofHom (ρ.comp f)) := by
      intro z
      have hz : z.left ≫ U'.ι ≫ toSpec (W.map f) = Spec.map (CommRingCat.ofHom ρ) := Over.w z
      rw [he, Category.assoc, hpb.w, ← Category.assoc]
      erw [hz]
      rw [CommRingCat.ofHom_comp, Spec.map_comp]
    have hι : ∀ z : Over.mk (Spec.map (CommRingCat.ofHom ρ)) ⟶
        Over.mk (U'.ι ≫ toSpec (W.map f)),
        (z.left ≫ e.hom.left ≫ pullback.fst (U.ι ≫ toSpec W) φ) ≫ U.ι =
          (z.left ≫ U'.ι) ≫ mapHom W f rfl := by
      intro z
      simp only [Category.assoc]
      erw [he']
    let a : Over.mk (Spec.map (CommRingCat.ofHom (ρ.comp f))) ⟶ Over.mk (U.ι ≫ toSpec W) :=
      Over.homMk _ (hw x)
    let b : Over.mk (Spec.map (CommRingCat.ofHom (ρ.comp f))) ⟶ Over.mk (U.ι ≫ toSpec W) :=
      Over.homMk _ (hw y)
    obtain ⟨h, hab⟩ := hmul k (ρ.comp f) a b P Q (hP.comp_of_map_eq rfl) (hQ.comp_of_map_eq rfl)
      ((hι x).trans (by rw [hx]; exact ptHom_mapHom W f rfl ρ P hP))
      ((hι y).trans (by rw [hy]; exact ptHom_mapHom W f rfl ρ Q hQ))
    refine ⟨h, ?_⟩
    have hl := lift_mul_hom_pullback_fst φ (Over.mk (U.ι ≫ toSpec W)) e.hom x y
      (Z₀ := Over.mk (Spec.map (CommRingCat.ofHom (ρ.comp f)))) (𝟙 _) a b
      (Category.id_comp _).symm (Category.id_comp _).symm
    apply (isPullback_mapHom W f rfl).hom_ext
    · refine (hι _).symm.trans ?_
      refine Eq.trans ?_ (hab.trans (ptHom_mapHom W f rfl ρ _ h).symm)
      rw [hl]
      erw [Category.id_comp]
      rfl
    · exact (Category.assoc _ _ _).trans ((Over.w
        (lift x y ≫ μ[Over.mk (U'.ι ≫ toSpec (W.map f))])).trans
        (ptHom_toSpec (W.map f) ρ _ h).symm)

end GlobalTheory.SmoothLocusBaseChange
end

