import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0482
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0311
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0594
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0869
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0481
import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0112
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0031
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.OmegaPullOmegaTraceOfSecTraceOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FormResFormPullFormPull

-- bundled from Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.EquivOfStalkwiseBaseChange
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

private def covE (S : Scheme.{0}) : MorphismProperty (S.Etale)ᵒᵖ := fun _ _ g => Surjective g.unop.left

private instance (S : Scheme.{0}) : (covE S).IsStableUnderComposition where
  comp_mem f g hf hg := by
    have hf' : Surjective f.unop.left := hf
    have hg' : Surjective g.unop.left := hg
    change Surjective (f ≫ g).unop.left
    have : (f ≫ g).unop.left = g.unop.left ≫ f.unop.left := rfl
    rw [this]
    infer_instance

private noncomputable def etHom {S : Scheme.{0}} (U : (S.Etale)ᵒᵖ) (V : Over S) (hV : Etale V.hom)
    (h : V ⟶ (Scheme.Etale.forget S).obj U.unop) :
    U ⟶ op (@Scheme.Etale.mk S _ V.hom hV) :=
  ((Scheme.Etale.forget S).preimage
    (X := @Scheme.Etale.mk S _ V.hom hV) (Y := U.unop) h).op

private theorem etHom_map {S : Scheme.{0}} (U : (S.Etale)ᵒᵖ) (V : Over S) (hV : Etale V.hom)
    (h : V ⟶ (Scheme.Etale.forget S).obj U.unop) :
    (Scheme.Etale.forget S).map (etHom U V hV h).unop = h :=
  (Scheme.Etale.forget S).map_preimage
    (X := @Scheme.Etale.mk S _ V.hom hV) (Y := U.unop) h

private theorem etHom_left {S : Scheme.{0}} (U : (S.Etale)ᵒᵖ) (V : Over S) (hV : Etale V.hom)
    (h : V ⟶ (Scheme.Etale.forget S).obj U.unop) : (etHom U V hV h).unop.left = h.left := by
  exact congrArg (fun k => k.left) (etHom_map U V hV h)

private theorem fst_iso (E : Spc) (S : Scheme.{0}) (p : E ⟶ sch.obj S) :
    IsIso (pullback.fst p (sch.map (Over.mk (𝟙 S)).hom)) := by
  have : IsIso (sch.map (Over.mk (𝟙 S)).hom) := by
    change IsIso (sch.map (𝟙 S))
    rw [sch.map_id]
    infer_instance
  infer_instance

theorem UpperTheory.Cb.equiv_of_stalkwise_base_change :
    ∀ (R : Type) [CommRing R] (F : Shv R) (S : Scheme.{0}) (E E' : Spc) (α : E ⟶ E') (p : E' ⟶ sch.obj S), Finitary F → QcqsOver (α ≫ p) → QcqsOver p → (∀ (O : Type) [CommRing O] (s : Spec (CommRingCat.of O) ⟶ S), IsStalk O s → Eqv R ((bcMap α p).app (Over.mk s)) F) → Eqv R α F := by
  intro R _ F S E E' α p hF hq hq' hst
  have key := GlobalTheory.T.etale_cohomology_equivalence_of_strictly_henselian_stalks R F S E E' α p hF hq hq' hst
  have basic := GlobalTheory.T.etaleCohomologyEquivalence_basic_properties R F
  let Φ : (S.Etale)ᵒᵖ ⥤ Spcᵒᵖ := (Scheme.Etale.forget S ⋙ bc (α ≫ p)).op
  let Φ' : (S.Etale)ᵒᵖ ⥤ Spcᵒᵖ := (Scheme.Etale.forget S ⋙ bc p).op
  let β : Φ' ⟶ Φ := NatTrans.op (Functor.whiskerLeft (Scheme.Etale.forget S) (bcMap α p))
  have hall : ∀ U, Eqv R (β.app U).unop F := by
    refine GlobalTheory.T.etaleSpace_descent_local_equivalence R F (S.Etale)ᵒᵖ (covE S) Φ Φ' β ?_ ?_ ?_
    · refine GlobalTheory.T.coveringsRefine_of_cechConerve_property (S.Etale)ᵒᵖ (covE S) _ ?_
      intro U V g hg
      exact ⟨GlobalTheory.T.smallEtale_cechNerve_resolution_of_surjective R S E (α ≫ p) U V g hg, GlobalTheory.T.smallEtale_cechNerve_resolution_of_surjective R S E' p U V g hg⟩
    · intro U n x
      obtain ⟨V, h, y, hV, hs, hy⟩ := (key ((Scheme.Etale.forget S).obj U.unop) U.unop.prop n).1 x
      refine ⟨op (@Scheme.Etale.mk S _ V.hom hV), etHom U V hV h, ?_, y, ?_⟩
      · change Surjective (etHom U V hV h).unop.left
        rw [etHom_left]
        exact hs
      · have hm : (Φ.map (etHom U V hV h)).unop = (bc (α ≫ p)).map h := by
          change (bc (α ≫ p)).map ((Scheme.Etale.forget S).map (etHom U V hV h).unop) = _
          rw [etHom_map]
          rfl
        rw [hm]
        exact hy
    · intro U n y hy
      obtain ⟨V, h, hV, hs, hz⟩ := (key ((Scheme.Etale.forget S).obj U.unop) U.unop.prop n).2 y hy
      refine ⟨op (@Scheme.Etale.mk S _ V.hom hV), etHom U V hV h, ?_, ?_⟩
      · change Surjective (etHom U V hV h).unop.left
        rw [etHom_left]
        exact hs
      · have hm : (Φ'.map (etHom U V hV h)).unop = (bc p).map h := by
          change (bc p).map ((Scheme.Etale.forget S).map (etHom U V hV h).unop) = _
          rw [etHom_map]
          rfl
        rw [hm]
        exact hz
  have hid : Eqv R ((bcMap α p).app (Over.mk (𝟙 S))) F :=
    hall (op (@Scheme.Etale.mk S S (𝟙 S) inferInstance))
  have i1 := fst_iso E S (α ≫ p)
  have i2 := fst_iso E' S p
  have hsq : (bcMap α p).app (Over.mk (𝟙 S)) ≫ pullback.fst p (sch.map (Over.mk (𝟙 S)).hom) =
      pullback.fst (α ≫ p) (sch.map (Over.mk (𝟙 S)).hom) ≫ α := by
    exact pullback.lift_fst _ _ _
  have e1 : Eqv R (pullback.fst (α ≫ p) (sch.map (Over.mk (𝟙 S)).hom)) F := basic.1 _ _ _ i1
  have e2 : Eqv R (pullback.fst p (sch.map (Over.mk (𝟙 S)).hom)) F := basic.1 _ _ _ i2
  have e3 := (basic.2.1 _ _ _ _ _).1 hid e2
  rw [hsq] at e3
  exact (basic.2.1 _ _ _ _ _).2.1 e1 e3
end

-- bundled from Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ExistsIntegralClopenDecompositionOfSmooth
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR KaehlerDifferential GlobalTheory.W1

theorem UpperTheory.Cb.exists_integral_clopen_decomposition_of_smooth :
    ∀ (Z : Scheme.{0}) (s : Z ⟶ Sp ℂ) (d : ℕ) [SmoothOfRelativeDimension d s] [CompactSpace Z], ∃ (J : Type) (_ : Fintype J) (V : J → Z.Opens), (∀ i j, i ≠ j → V i ⊓ V j = ⊥) ∧ iSup V = ⊤ ∧ ∀ j, IsIntegral (V j).toScheme := by
  first | exact @GlobalTheory.SmoothComponents.main | exact GlobalTheory.SmoothComponents.main
end

-- bundled from Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.HodgeTraceEqSumClopenDecomposition
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR KaehlerDifferential GlobalTheory.W1

namespace UpperTheory.TrSum

section Alg

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Module.Finite R M]
  [Module.Projective R M] [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Projective R N]

open TensorProduct in

private theorem projTrace_comm (u : M →ₗ[R] N) (v : N →ₗ[R] M) :
    projTrace R N (u ∘ₗ v) = projTrace R M (v ∘ₗ u) := by
  obtain ⟨t, rfl⟩ := (dualTensorHom_bijective (R := R) (M := M) (N := N)).2 u
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, LinearMap.add_comp, LinearMap.comp_add, ha, hb]
  | tmul ξ n =>
    have e1 : dualTensorHom R M N (ξ ⊗ₜ n) ∘ₗ v = (ξ ∘ₗ v).smulRight n := by ext; simp
    have e2 : v ∘ₗ dualTensorHom R M N (ξ ⊗ₜ n) = ξ.smulRight (v n) := by ext; simp
    rw [e1, e2, projTrace_smulRight, projTrace_smulRight]
    rfl

private theorem algTrace_eq_sum {ι : Type*} [Fintype ι] {B B' : Type*} {C : ι → Type*} [CommRing B]
    [CommRing B'] [Algebra B B'] [Module.Finite B B'] [Module.Projective B B']
    [∀ i, CommRing (C i)] [∀ i, Algebra B (C i)] [∀ i, Module.Finite B (C i)]
    [∀ i, Module.Projective B (C i)] (r : ∀ i, B' →ₐ[B] C i)
    (hr : Function.Bijective fun (x : B') i ↦ r i x) (b : B') :
    algTrace B B' b = ∑ i, algTrace B (C i) (r i b) := by
  classical
  let E : B' ≃ₗ[B] (∀ i, C i) :=
    LinearEquiv.ofBijective (LinearMap.pi fun i ↦ (r i).toLinearMap) hr
  have hE : ∀ x i, E x i = r i x := fun _ _ ↦ rfl
  let t : ∀ i, C i →ₗ[B] B' := fun i ↦ E.symm.toLinearMap ∘ₗ LinearMap.single B C i
  have h1 : ∀ i y, r i (t i y) = y := fun i y ↦ by
    have e : E (t i y) = Pi.single i y := E.apply_symm_apply _
    have := congrFun e i
    rwa [hE, Pi.single_eq_same] at this
  have h2 : ∀ x, ∑ i, t i (r i x) = x := fun x ↦ by
    apply E.injective
    rw [map_sum]
    have e : ∀ i, E (t i (r i x)) = Pi.single i (r i x) := fun i ↦ E.apply_symm_apply _
    simp only [e]
    rw [Finset.univ_sum_single]
    rfl
  have h3 : LinearMap.mul B B' b = ∑ i, t i ∘ₗ ((r i).toLinearMap ∘ₗ LinearMap.mul B B' b) := by
    ext x
    simp only [LinearMap.sum_apply, LinearMap.comp_apply]
    exact (h2 _).symm
  rw [algTrace_apply, h3, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [projTrace_comm, algTrace_apply]
  congr 1
  ext y
  simp [h1]

end Alg

private theorem res_pi_bijective {Y : Scheme.{0}} {M : Type} (A : Y.Opens) (D : M → Y.Opens)
    (hD : ∀ m, D m ≤ A) (hc : A ≤ iSup D) (hd : ∀ i j, i ≠ j → D i ⊓ D j = ⊥) :
    Function.Bijective fun (x : Γ(Y, A)) m ↦ Y.presheaf.map (homOfLE (hD m)).op x := by
  constructor
  · intro x y e
    exact TopCat.Sheaf.eq_of_locally_eq' Y.sheaf D A (fun m ↦ homOfLE (hD m)) hc x y
      fun m ↦ congrFun e m
  · intro y
    have hcomp : TopCat.Presheaf.IsCompatible Y.sheaf.1 D y := by
      intro i j
      by_cases hij : i = j
      · subst hij
        rfl
      · have : Subsingleton Γ(Y, D i ⊓ D j) := by
          rw [hd i j hij]
          infer_instance
        exact this.elim _ _
    obtain ⟨x, hx, -⟩ := TopCat.Sheaf.existsUnique_gluing' Y.sheaf D A
      (fun m ↦ homOfLE (hD m)) hc y hcomp
    exact ⟨x, funext hx⟩

section Geo

variable {k : Type} [CommRing k] {Z Y : Scheme.{0}}

private theorem secTrace_eq_sum {s : Z ⟶ Sp k} {s' : Y ⟶ Sp k} {c : Y ⟶ Z} [IsFinite c] [Etale c]
    {M : Type} [Fintype M] (W : M → Y.Opens) (hd : ∀ i j, i ≠ j → W i ⊓ W j = ⊥)
    (hc : iSup W = ⊤) [∀ m, IsFinite ((W m).ι ≫ c)] [∀ m, Etale ((W m).ι ≫ c)] {U : Z.Opens}
    (hU : IsAffineOpen U) (b' : Sec s' (c ⁻¹ᵁ U)) :
    secTrace s s' hU b' = ∑ m, secTrace (f := (W m).ι ≫ c) s ((W m).ι ≫ s') hU
      (appSec s' ((W m).ι ≫ s') (W m).ι (c ⁻¹ᵁ U) b') := by
  letI := secAlg s s' c U
  letI inst : ∀ m, Algebra (Sec s U) (Sec ((W m).ι ≫ s') (((W m).ι ≫ c) ⁻¹ᵁ U)) :=
    fun m ↦ secAlg s ((W m).ι ≫ s') ((W m).ι ≫ c) U
  haveI := sec_finite (s := s) (s' := s') (f := c) hU
  haveI := sec_etale (s := s) (s' := s') (f := c) hU
  haveI := projective_of_etale (Sec s U) (Sec s' (c ⁻¹ᵁ U))
  haveI : ∀ m, Module.Finite (Sec s U) (Sec ((W m).ι ≫ s') (((W m).ι ≫ c) ⁻¹ᵁ U)) :=
    fun m ↦ sec_finite (s := s) (s' := (W m).ι ≫ s') (f := (W m).ι ≫ c) hU
  haveI : ∀ m, Algebra.Etale (Sec s U) (Sec ((W m).ι ≫ s') (((W m).ι ≫ c) ⁻¹ᵁ U)) :=
    fun m ↦ sec_etale (s := s) (s' := (W m).ι ≫ s') (f := (W m).ι ≫ c) hU
  haveI : ∀ m, Module.Projective (Sec s U) (Sec ((W m).ι ≫ s') (((W m).ι ≫ c) ⁻¹ᵁ U)) :=
    fun m ↦ projective_of_etale _ _
  let r : ∀ m, Sec s' (c ⁻¹ᵁ U) →ₐ[Sec s U] Sec ((W m).ι ≫ s') (((W m).ι ≫ c) ⁻¹ᵁ U) := fun m ↦
    { appSec s' ((W m).ι ≫ s') (W m).ι (c ⁻¹ᵁ U) with
      commutes' := fun b ↦ by
        change (c.app U ≫ (W m).ι.app (c ⁻¹ᵁ U)).hom b = (((W m).ι ≫ c).app U).hom b
        rw [Scheme.Hom.comp_app]
        rfl }
  have hDeq : ∀ m, (W m).ι ''ᵁ ((W m).ι ⁻¹ᵁ (c ⁻¹ᵁ U)) = W m ⊓ c ⁻¹ᵁ U := fun m ↦ by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  have hD : ∀ m, (W m).ι ''ᵁ ((W m).ι ⁻¹ᵁ (c ⁻¹ᵁ U)) ≤ c ⁻¹ᵁ U := fun m ↦ by
    rw [hDeq]; exact inf_le_right
  have hcov : c ⁻¹ᵁ U ≤ ⨆ m, (W m).ι ''ᵁ ((W m).ι ⁻¹ᵁ (c ⁻¹ᵁ U)) := by
    simp only [hDeq]
    rw [← iSup_inf_eq, hc, top_inf_eq]
  have hdis : ∀ i j, i ≠ j → (W i).ι ''ᵁ ((W i).ι ⁻¹ᵁ (c ⁻¹ᵁ U)) ⊓
      (W j).ι ''ᵁ ((W j).ι ⁻¹ᵁ (c ⁻¹ᵁ U)) = ⊥ := fun i j hij ↦ by
    rw [hDeq, hDeq, eq_bot_iff, ← hd i j hij]
    exact inf_le_inf inf_le_left inf_le_left
  have hb := res_pi_bijective (c ⁻¹ᵁ U) _ hD hcov hdis
  have hr : Function.Bijective fun (x : Sec s' (c ⁻¹ᵁ U)) m ↦ r m x := by
    have e : (fun (x : Sec s' (c ⁻¹ᵁ U)) m ↦ r m x) =
        fun x m ↦ Y.presheaf.map (homOfLE (hD m)).op x := by
      funext x m
      change ((W m).ι.app (c ⁻¹ᵁ U)).hom x = _
      rw [Scheme.Opens.ι_app]
      rfl
    rw [e]
    exact hb
  exact algTrace_eq_sum r hr b'

private noncomputable def piece (s' : Y ⟶ Sp k) (c : Y ⟶ Z) (V : Y.Opens) (j : ℕ) :
    (Scheme.Modules.pushforward c).obj (Omega s' j) ⟶
      (Scheme.Modules.pushforward (V.ι ≫ c)).obj (Omega (V.ι ≫ s') j) :=
  (Scheme.Modules.pushforward c).map (omegaPull (f := V.ι) rfl j) ≫
    (Scheme.Modules.pushforwardComp V.ι c).hom.app _

private theorem piece_app_smul {s : Z ⟶ Sp k} {s' : Y ⟶ Sp k} {c : Y ⟶ Z} (h : c ≫ s = s')
    (V : Y.Opens) (hg : (V.ι ≫ c) ≫ s = V.ι ≫ s') (j : ℕ) (U : Z.Opens)
    (b' : Sec s' (c ⁻¹ᵁ U)) (x : OmU s U j) :
    (piece s' c V j).app U (toOm s' j (c ⁻¹ᵁ U) (b' • formPull h U j x)) =
      toOm (V.ι ≫ s') j ((V.ι ≫ c) ⁻¹ᵁ U)
        ((show Sec (V.ι ≫ s') ((V.ι ≫ c) ⁻¹ᵁ U) from appSec s' (V.ι ≫ s') V.ι (c ⁻¹ᵁ U) b') •
          formPull hg U j x) := by
  change (omegaPull (f := V.ι) (s' := V.ι ≫ s') rfl j).val.app (Opposite.op (c ⁻¹ᵁ U))
    ((toOmega s' j).app (Opposite.op (c ⁻¹ᵁ U)) (b' • formPull h U j x)) = _
  rw [omegaPull_toOmega, formPull_smul, formPull_formPull h rfl hg]
  rfl

private theorem sum_app {X : Scheme.{0}} {F G : X.Modules} {ι : Type} (t : Finset ι)
    (φ : ι → (F ⟶ G)) (U : X.Opens) (y : Γ(F, U)) :
    (∑ i ∈ t, φ i).app U y = ∑ i ∈ t, (φ i).app U y := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, Scheme.Modules.Hom.zero_app]
    rfl
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Scheme.Modules.Hom.add_app, ← ih]
    rfl

private theorem omegaTrace_eq_sum {s : Z ⟶ Sp k} {s' : Y ⟶ Sp k} {c : Y ⟶ Z} [IsFinite c] [Etale c]
    (h : c ≫ s = s') {M : Type} [Fintype M] (W : M → Y.Opens) (hd : ∀ i j, i ≠ j → W i ⊓ W j = ⊥)
    (hc : iSup W = ⊤) [∀ m, IsFinite ((W m).ι ≫ c)] [∀ m, Etale ((W m).ι ≫ c)]
    (hg : ∀ m, ((W m).ι ≫ c) ≫ s = (W m).ι ≫ s') (j : ℕ) :
    omegaTrace h j = ∑ m, piece s' c (W m) j ≫ omegaTrace (hg m) j := by
  refine (omegaTrace_ext h j _ fun U hU b' x ↦ ?_).symm
  refine (sum_app Finset.univ _ U _).trans ?_
  have e : ∀ m, (piece s' c (W m) j ≫ omegaTrace (hg m) j).app U
      (toOm s' j (c ⁻¹ᵁ U) (b' • formPull h U j x)) =
      toOm s j U (secTrace (f := (W m).ι ≫ c) s ((W m).ι ≫ s') hU
        (appSec s' ((W m).ι ≫ s') (W m).ι (c ⁻¹ᵁ U) b') • x) := fun m ↦ by
    rw [Scheme.Modules.Hom.comp_app]
    change (omegaTrace (hg m) j).app U ((piece s' c (W m) j).app U
      (toOm s' j (c ⁻¹ᵁ U) (b' • formPull h U j x))) = _
    rw [piece_app_smul h (W m) (hg m) j U]
    exact omegaTrace_toOm_smul_formPull (hg m) j hU _ x
  simp only [e]
  rw [secTrace_eq_sum W hd hc hU b', Finset.sum_smul, map_sum]

private theorem cohOn_map_sum {X : Scheme.{0}} (R : Type) [CommRing R] [Algebra R Γ(X, ⊤)]
    {F G : X.Modules} {ι : Type} (t : Finset ι) (φ : ι → (F ⟶ G)) (U : X.Opens) (n : ℕ) :
    cohOn.map R (∑ i ∈ t, φ i) U n = ∑ i ∈ t, cohOn.map R (φ i) U n := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using cohOn.map_zero_hom R F G U n
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, cohOn.map_add_hom, ih]

private theorem hodgeTrace_eq_sum {s : Z ⟶ Sp k} {s' : Y ⟶ Sp k} {c : Y ⟶ Z} [IsFinite c] [Etale c]
    (h : c ≫ s = s') {M : Type} [Fintype M] (W : M → Y.Opens) (hd : ∀ i j, i ≠ j → W i ⊓ W j = ⊥)
    (hc : iSup W = ⊤) [∀ m, IsFinite ((W m).ι ≫ c)] [∀ m, Etale ((W m).ι ≫ c)]
    (hg : ∀ m, ((W m).ι ≫ c) ≫ s = (W m).ι ≫ s') (a b : ℕ) (w : hodgeH s' a b) :
    hodgeTrace h a b w = ∑ m, hodgeTrace (f := (W m).ι ≫ c) (hg m) a b
      (hodgePull (f := (W m).ι) rfl a b w) := by
  letI := algΓ s
  letI := algΓ s'
  obtain ⟨y, rfl⟩ := (coh.pushforwardEquiv k (appTop_algebraMap h) (Omega s' a) b).surjective w
  have e1 : hodgeTrace h a b (coh.pushforwardEquiv k (appTop_algebraMap h) (Omega s' a) b y) =
      cohOn.map k (omegaTrace h a) ⊤ b y :=
    congrArg (cohOn.map k (omegaTrace h a) ⊤ b)
      ((coh.pushforwardEquiv k (appTop_algebraMap h) (Omega s' a) b).symm_apply_apply y)
  rw [e1, omegaTrace_eq_sum h W hd hc hg a, cohOn_map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  letI := algΓ ((W m).ι ≫ s')
  rw [cohOn.map_comp, LinearMap.comp_apply]
  change _ = cohOn.map k (omegaTrace (hg m) a) ⊤ b
    ((coh.pushforwardEquiv k (appTop_algebraMap (hg m)) (Omega ((W m).ι ≫ s') a) b).symm _)
  congr 1
  refine ((coh.pushforwardEquiv k (appTop_algebraMap (hg m))
    (Omega ((W m).ι ≫ s') a) b).eq_symm_apply).2 ?_
  have s1 := cohOn.pull_map (σ := RingHom.id k) (appTop_algebraMap (hg m))
    (𝟙 _) (piece s' c (W m) a) (le_refl (((W m).ι ≫ c) ⁻¹ᵁ ⊤)) (n := b) y
  have s2 := cohOn_pull_pull (appTop_algebraMap h)
    (appTop_algebraMap (f := (W m).ι) (s := s') rfl) (appTop_algebraMap (hg m))
    (𝟙 _) (omegaPull rfl a) (le_refl (c ⁻¹ᵁ ⊤)) (le_refl _) (le_refl _) b y
  refine Eq.trans (cohOn.pushforwardEquiv_apply k (appTop_algebraMap (hg m)) _ ⊤ b _) (s1.trans ?_)
  refine Eq.trans ?_ s2.symm
  rw [Category.comp_id, Category.id_comp]
  rfl

end Geo

end UpperTheory.TrSum

theorem UpperTheory.Cb.hodgeTrace_eq_sum_clopen_decomposition :
    ∀ (Z Y : Scheme.{0}) (s : Z ⟶ Sp ℂ) (s' : Y ⟶ Sp ℂ) (c : Y ⟶ Z) [IsFinite c] [Etale c] (h : c ≫ s = s') (M : Type) [Fintype M] (W : M → Y.Opens), (∀ i j, i ≠ j → W i ⊓ W j = ⊥) → iSup W = ⊤ → ∀ (hf : ∀ m, IsFinite ((W m).ι ≫ c)) (he : ∀ m, Etale ((W m).ι ≫ c)) (a b : ℕ) (w : hodgeH s' a b), hodgeTrace h a b w = ∑ m, (haveI := hf m; haveI := he m; hodgeTrace (f := (W m).ι ≫ c) (s' := (W m).ι ≫ s') (by rw [Category.assoc, h]) a b (hodgePull (f := (W m).ι) rfl a b w)) := by
  intro Z Y s s' c _ _ h M _ W hd hc hf he a b w
  haveI := hf
  haveI := he
  exact UpperTheory.TrSum.hodgeTrace_eq_sum h W hd hc _ a b w
end

