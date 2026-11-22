import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0001
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleCohomology.Product
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsMatrixForm
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0009
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.Bundle0001
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0011
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIndEtaleOfIsLocalization
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0006
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FinrankGroupCohomologyFunRep
section
noncomputable section

open CategoryTheory
open scoped Matrix

namespace GlobalTheory.BorelCoh

def matVecRep {H : Type} [Group H] {d : ℕ} (ξ : H →* Matrix (Fin d) (Fin d) ℂ) : Representation ℂ H (Fin d → ℂ) :=
  (Matrix.toLinAlgEquiv' : Matrix (Fin d) (Fin d) ℂ ≃ₐ[ℂ] Module.End ℂ (Fin d → ℂ)).toRingEquiv.toMonoidHom.comp ξ

theorem matVecRep_apply {H : Type} [Group H] {d : ℕ} (ξ : H →* Matrix (Fin d) (Fin d) ℂ) (h : H) (v : Fin d → ℂ) :
    matVecRep ξ h v = ξ h *ᵥ v := by
  simp [matVecRep, Matrix.toLinAlgEquiv'_apply]

namespace Shapiro

variable {Γ Y : Type} [Group Γ] [MulAction Γ Y] {d : ℕ} (ξ : Γ →* Matrix (Fin d) (Fin d) ℂ)

abbrev stabRep (y : Y) : Rep ℂ (MulAction.stabilizer Γ y) :=
  Rep.of (matVecRep (ξ.comp (MulAction.stabilizer Γ y).subtype))

theorem xi_mulVec_inv (g : Γ) (v : Fin d → ℂ) : ξ g *ᵥ (ξ g⁻¹ *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, ← map_mul, mul_inv_cancel, map_one, Matrix.one_mulVec]

def toCoindLin (y : Y) : (Y → Fin d → ℂ) →ₗ[ℂ]
    Representation.coindV (MulAction.stabilizer Γ y).subtype (stabRep ξ y).ρ where
  toFun f := ⟨fun h => ξ h *ᵥ f (h⁻¹ • y), fun s h => by
    have hs : (s : Γ)⁻¹ • y = y := by
      rw [inv_smul_eq_iff]; exact s.2.symm
    change ξ ((s : Γ) * h) *ᵥ f (((s : Γ) * h)⁻¹ • y) = matVecRep (ξ.comp (MulAction.stabilizer Γ y).subtype) s (ξ h *ᵥ f (h⁻¹ • y))
    rw [matVecRep_apply, mul_inv_rev, mul_smul, hs, map_mul, MonoidHom.comp_apply, Subgroup.coe_subtype,
      Matrix.mulVec_mulVec]⟩
  map_add' f f' := Subtype.ext (funext fun h => by simp [Matrix.mulVec_add])
  map_smul' c f := Subtype.ext (funext fun h => by simp [Matrix.mulVec_smul])

def toCoind (y : Y) : Rep.of (funRep Y ξ) ⟶ Rep.coind (MulAction.stabilizer Γ y).subtype (stabRep ξ y) :=
  Rep.ofHom
    { toLinearMap := toCoindLin ξ y
      isIntertwining' := fun γ => by
        ext f h i
        change (ξ h *ᵥ (ξ γ *ᵥ f (γ⁻¹ • h⁻¹ • y))) i = (ξ (h * γ) *ᵥ f ((h * γ)⁻¹ • y)) i
        rw [Matrix.mulVec_mulVec, ← map_mul, mul_inv_rev, mul_smul] }

theorem toCoind_pi_bijective {ι : Type} (y : ι → Y) (hcov : ∀ x : Y, ∃ j, ∃ g : Γ, g • y j = x)
    (hdis : ∀ i j (g : Γ), g • y i = y j → i = j) :
    Function.Bijective fun (f : Rep.of (funRep Y ξ)) (j : ι) => (toCoind ξ (y j)).hom f := by
  constructor
  · intro f f' hff
    funext x
    obtain ⟨j, g, rfl⟩ := hcov x
    have h1 := congrArg (fun F => F.1 g⁻¹) (congrFun hff j)
    change ξ g⁻¹ *ᵥ f (g⁻¹⁻¹ • y j) = ξ g⁻¹ *ᵥ f' (g⁻¹⁻¹ • y j) at h1
    rw [inv_inv] at h1
    rw [← xi_mulVec_inv ξ g (f (g • y j)), h1, xi_mulVec_inv]
  · intro F
    choose J G hJG using hcov
    refine ⟨fun x => ξ (G x) *ᵥ (F (J x)).1 (G x)⁻¹, funext fun j => Subtype.ext (funext fun h => ?_)⟩
    change ξ h *ᵥ (ξ (G (h⁻¹ • y j)) *ᵥ (F (J (h⁻¹ • y j))).1 (G (h⁻¹ • y j))⁻¹) = (F j).1 h
    have key : ∀ j' (g : Γ), g • y j' = h⁻¹ • y j → ξ h *ᵥ (ξ g *ᵥ (F j').1 g⁻¹) = (F j).1 h := by
      intro j' g hg
      have hst : (h * g) • y j' = y j := by rw [mul_smul, hg, smul_inv_smul]
      obtain rfl := hdis j' j (h * g) hst
      have hmem : h * g ∈ MulAction.stabilizer Γ (y j') := hst
      have hc := (F j').2 ⟨h * g, hmem⟩ g⁻¹
      change (F j').1 ((h * g) * g⁻¹) = matVecRep (ξ.comp (MulAction.stabilizer Γ (y j')).subtype) ⟨h * g, hmem⟩ ((F j').1 g⁻¹) at hc
      rw [mul_inv_cancel_right, matVecRep_apply, MonoidHom.comp_apply, Subgroup.coe_subtype] at hc
      rw [hc]
      change ξ h *ᵥ (ξ g *ᵥ _) = ξ (h * g) *ᵥ _
      rw [map_mul, Matrix.mulVec_mulVec]
    exact key _ _ (hJG _)

def cohEquiv {ι : Type} (y : ι → Y) (hcov : ∀ x : Y, ∃ j, ∃ g : Γ, g • y j = x)
    (hdis : ∀ i j (g : Γ), g • y i = y j → i = j) (q : ℕ) :
    groupCohomology (Rep.of (funRep Y ξ)) q ≃ₗ[ℂ]
      ∀ j, groupCohomology (Rep.of (matVecRep (ξ.comp (MulAction.stabilizer Γ (y j)).subtype))) q :=
  GroundTheory.ProfCoh.groupCohomologyPiEquiv (fun j => toCoind ξ (y j)) (toCoind_pi_bijective ξ y hcov hdis) q ≪≫ₗ
    LinearEquiv.piCongrRight fun j => (groupCohomology.coindIso (stabRep ξ (y j)) q).toLinearEquiv

end Shapiro

end GlobalTheory.BorelCoh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FreeOnCechNerveExactAt
section
open CategoryTheory Limits AlgebraicGeometry Opposite Abelian Simplicial GlobalTheory.Et
universe v u

noncomputable section

namespace GlobalTheory.Et.FreeCech

variable {U V : Scheme.{0}} (π : V ⟶ U) (W : Scheme.{0})

def Img : Type 1 := {t : ULift.{1} (W ⟶ U) // ∃ s : W ⟶ V, s ≫ π = t.down}

def toImg : ULift.{1} (W ⟶ V) ⟶ Img π W :=
  TypeCat.ofHom fun s => ⟨⟨s.down ≫ π⟩, s.down, rfl⟩

def split : SplitEpi (toImg π W) where
  section_ := TypeCat.ofHom fun t => ⟨t.2.choose⟩
  id := by
    ext t
    exact Subtype.ext (ULift.ext _ _ t.2.choose_spec)

abbrev Pow (k : ℕ) : Scheme.{0} := widePullback.{0} U (fun _ : Fin (k + 1) => V) (fun _ => π)

def ptCone (k : ℕ) : Cone (WidePullbackShape.wideCospan (Img π W)
    (fun _ : Fin (k + 1) => ULift.{1} (W ⟶ V)) (fun _ => toImg π W)) :=
  WidePullbackShape.mkCone (X := ULift.{1} (W ⟶ Pow π k))
    (TypeCat.ofHom fun x => (⟨⟨x.down ≫ WidePullback.base _⟩, x.down ≫ WidePullback.π _ 0, by simp⟩ : Img π W))
    (fun j => TypeCat.ofHom fun x => (⟨x.down ≫ WidePullback.π _ j⟩ : ULift.{1} (W ⟶ V)))
    (fun j => by
      ext x
      exact Subtype.ext (ULift.ext _ _
        (show (x.down ≫ WidePullback.π _ j) ≫ π = x.down ≫ WidePullback.base _ by simp)))

def ptConeIsLimit (k : ℕ) : IsLimit (ptCone π W k) where
  lift c := TypeCat.ofHom fun x => (⟨WidePullback.lift (c.π.app none x).1.down
    (fun j => (c.π.app (some j) x).down)
    (fun j => congrArg (fun t : Img π W => t.1.down)
      (types_congr_hom (c.w (WidePullbackShape.Hom.term j)) x))⟩ : ULift.{1} (W ⟶ Pow π k))
  fac c j := by
    ext x
    cases j with
    | none => exact Subtype.ext (ULift.ext _ _ (WidePullback.lift_base ..))
    | some j => exact ULift.ext _ _ (WidePullback.lift_π ..)
  uniq c m hm := by
    ext x
    apply ULift.ext
    apply WidePullback.hom_ext
    · intro j
      exact (congrArg ULift.down (types_congr_hom (hm (some j)) x)).trans
        (WidePullback.lift_π (fun _ => π) _ (fun j => (c.π.app (some j) x).down) _ j).symm
    · exact (congrArg (fun t : Img π W => t.1.down) (types_congr_hom (hm none) x)).trans
        (WidePullback.lift_base ..).symm

end GlobalTheory.Et.FreeCech

namespace GlobalTheory.Et.FreeCech

variable {U V : Scheme.{0}} (π : V ⟶ U) (W : Scheme.{0})

abbrev pts : Scheme.{0} ⥤ Type 1 := uliftYoneda.{1} ⋙ (evaluation Scheme.{0}ᵒᵖ (Type 1)).obj (op W)

def cechIso : (Arrow.mk π).cechNerve ⋙ pts W ≅ (Arrow.mk (toImg π W)).cechNerve :=
  NatIso.ofComponents (fun n => (ptConeIsLimit π W n.unop.len).conePointUniqueUpToIso (limit.isLimit _))
    (fun {n m} f => by
      apply WidePullback.hom_ext
      · intro j
        have h1 := (ptConeIsLimit π W m.unop.len).conePointUniqueUpToIso_hom_comp (limit.isLimit _) (some j)
        have h2 := (ptConeIsLimit π W n.unop.len).conePointUniqueUpToIso_hom_comp (limit.isLimit _)
          (some (f.unop.toOrderHom j))
        simp only [Category.assoc, Arrow.cechNerve_map, WidePullback.lift_π]
        erw [h1, h2]
        ext x
        apply ULift.ext
        show x.down ≫ ((Arrow.mk π).cechNerve.map f) ≫ WidePullback.π _ j = x.down ≫ WidePullback.π _ _
        exact congrArg (fun g => x.down ≫ g) (WidePullback.lift_π (fun _ => π) _ _ _ j)
      · have h1 := (ptConeIsLimit π W m.unop.len).conePointUniqueUpToIso_hom_comp (limit.isLimit _) none
        have h2 := (ptConeIsLimit π W n.unop.len).conePointUniqueUpToIso_hom_comp (limit.isLimit _) none
        simp only [Category.assoc, Arrow.cechNerve_map, WidePullback.lift_base]
        erw [h1, h2]
        ext x
        apply Subtype.ext
        apply ULift.ext
        show x.down ≫ ((Arrow.mk π).cechNerve.map f) ≫ WidePullback.base _ = x.down ≫ WidePullback.base _
        exact congrArg (fun g => x.down ≫ g) (WidePullback.lift_base (fun _ => π) _ _ _))

end GlobalTheory.Et.FreeCech

namespace GlobalTheory.Et.FreeCech

variable {U V : Scheme.{0}} (π : V ⟶ U) (W : Scheme.{0})

theorem exactAt_pts (R : Type) [CommRing R] (k : ℕ) :
    ((AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{1} (ULift.{1} R))).obj
      (((Arrow.mk π).cechNerve ⋙ pts W) ⋙ ModuleCat.free (ULift.{1} R))).ExactAt (k + 1) := by
  let ed := (Arrow.AugmentedCechNerve.extraDegeneracy (Arrow.mk (toImg π W)) (split π W)).map
    (ModuleCat.free (ULift.{1} R))
  let h := ed.homotopyEquiv
  haveI := h.quasiIso_hom
  have h1 := (exactAt_iff_of_quasiIsoAt h.hom (k + 1)).2 (ChainComplex.exactAt_succ_single_obj _ _)
  exact h1.of_iso ((AlgebraicTopology.alternatingFaceMapComplex _).mapIso
    (Functor.isoWhiskerRight (cechIso π W) _)).symm

end GlobalTheory.Et.FreeCech

namespace GlobalTheory.Et

theorem freeOn_cechNerve_exactAt {R : Type} [CommRing R] {U V : Scheme.{0}} (π : V ⟶ U) (n : ℕ) :
    ((AlgebraicTopology.alternatingFaceMapComplex (Shv R)).obj
      ((Arrow.mk π).cechNerve ⋙ freeOn R)).ExactAt (n + 1) := by
  let P := (Arrow.mk π).cechNerve ⋙ uliftYoneda.{1} ⋙
    (Functor.whiskeringRight _ _ _).obj (ModuleCat.free (ULift.{1} R))
  let K := (AlgebraicTopology.alternatingFaceMapComplex _).obj P
  have hK : K.ExactAt (n + 1) := by
    rw [HomologicalComplex.exactAt_iff, ShortComplex.exact_iff_isZero_homology]
    refine Functor.isZero _ fun W => ?_
    refine IsZero.of_iso ?_ ((K.sc (n + 1)).mapHomologyIso ((evaluation _ _).obj W)).symm
    rw [← ShortComplex.exact_iff_isZero_homology]
    have h := FreeCech.exactAt_pts π (unop W) R n
    have e := Functor.congr_obj (AlgebraicTopology.map_alternatingFaceMapComplex
      ((evaluation Scheme.{0}ᵒᵖ (ModuleCat.{1} (ULift.{1} R))).obj W)) P
    have h' : ((((evaluation Scheme.{0}ᵒᵖ (ModuleCat.{1} (ULift.{1} R))).obj W).mapHomologicalComplex _).obj
        K).ExactAt (n + 1) := by
      rw [show K = (AlgebraicTopology.alternatingFaceMapComplex _).obj P from rfl]
      erw [e]
      exact h
    exact h'
  have e := Functor.congr_obj (AlgebraicTopology.map_alternatingFaceMapComplex
    (presheafToSheaf (Scheme.proetaleTopology.{0}) (ModuleCat.{1} (ULift.{1} R)))) P
  have h2 := hK.map (presheafToSheaf (Scheme.proetaleTopology.{0}) (ModuleCat.{1} (ULift.{1} R)))
  change (((presheafToSheaf _ _).mapHomologicalComplex _).obj K).ExactAt (n + 1) at h2
  erw [e] at h2
  exact h2

end GlobalTheory.Et
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIndEtaleOverEtaleOfIsIndEtale
section
open scoped TensorProduct

namespace GlobalTheory.IndEtaleCancel

theorem isIndEtale_of_etale_of_isIndEtale : ∀ (A W O : Type) [CommRing A] [CommRing W]
    [CommRing O] [Algebra A W] [Algebra A O] [Algebra W O] [IsScalarTower A W O]
    [Algebra.Etale A W], GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap A O) →
      GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap W O) := by
  intro A W O _ _ _ _ _ _ _ _ h
  have hT : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap W (W ⊗[A] O)) :=
    GlobalTheory.isIndEtale_tensorProduct_left A O W h
  obtain ⟨t, ht1, ht2⟩ :=
    (Algebra.FormallyUnramified.iff_exists_tensorProduct (R := A) (S := W)).1 inferInstance
  let g : W →ₐ[A] O := IsScalarTower.toAlgHom A W O
  let μ : W ⊗[A] O →ₐ[W] O := Algebra.TensorProduct.lift (Algebra.ofId W O) (AlgHom.id A O)
    (fun _ _ => Commute.all _ _)
  have hμ : ∀ w o, μ (w ⊗ₜ o) = algebraMap W O w * o := fun w o => by simp [μ]
  let e : W ⊗[A] O := Algebra.TensorProduct.map (AlgHom.id A W) g t
  have he1 : ∀ s : W, ((1 : W) ⊗ₜ[A] (algebraMap W O s) - s ⊗ₜ[A] (1 : O)) * e = 0 := by
    intro s
    have := congrArg (Algebra.TensorProduct.map (AlgHom.id A W) g) (ht1 s)
    simpa [map_mul, map_sub, e, g] using this
  have hμe : μ e = 1 := by
    have H : (μ.restrictScalars A).comp (Algebra.TensorProduct.map (AlgHom.id A W) g) =
        g.comp (Algebra.TensorProduct.lmul' A) := by
      apply Algebra.TensorProduct.ext'
      intro a b
      simp [μ, g, Algebra.TensorProduct.lmul'_apply_tmul, IsScalarTower.algebraMap_apply A W O]
    have := DFunLike.congr_fun H t
    simp only [AlgHom.comp_apply, AlgHom.coe_restrictScalars'] at this
    rw [show μ e = _ from this, ht2, map_one]
  have hkey : ∀ x : W ⊗[A] O, e * x = e * ((1 : W) ⊗ₜ[A] μ x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul w o =>
      rw [hμ]
      have h1 : (w ⊗ₜ[A] o : W ⊗[A] O) = (w ⊗ₜ[A] (1 : O)) * ((1 : W) ⊗ₜ[A] o) := by simp
      have h2 : ((1 : W) ⊗ₜ[A] (algebraMap W O w * o) : W ⊗[A] O) =
          ((1 : W) ⊗ₜ[A] algebraMap W O w) * ((1 : W) ⊗ₜ[A] o) := by simp
      linear_combination e * h1 - e * h2 - ((1 : W) ⊗ₜ[A] o) * he1 w
    | add x y hx hy => rw [mul_add, hx, hy, map_add, TensorProduct.tmul_add, mul_add]
  have hidem : IsIdempotentElem e := by
    show e * e = e
    rw [hkey e, hμe, Algebra.TensorProduct.one_def.symm, mul_one]
  letI : Algebra (W ⊗[A] O) O := μ.toRingHom.toAlgebra
  have hmap : ∀ x, algebraMap (W ⊗[A] O) O x = μ x := fun _ => rfl
  haveI : IsScalarTower W (W ⊗[A] O) O :=
    IsScalarTower.of_algebraMap_eq (fun w => by rw [hmap, μ.commutes])
  haveI : IsLocalization.Away e O := by
    refine IsLocalization.away_of_isIdempotentElem_of_mul hidem (fun x y => ?_) ?_
    · rw [hmap, hmap]
      constructor
      · intro hxy; rw [hkey x, hkey y, hxy]
      · intro hxy
        have hx : μ (e * x) = μ x := by rw [map_mul, hμe, one_mul]
        have hy : μ (e * y) = μ y := by rw [map_mul, hμe, one_mul]
        rw [← hx, ← hy, hxy]
    · intro o
      exact ⟨(1 : W) ⊗ₜ o, by rw [hmap, hμ, map_one, one_mul]⟩
  exact GlobalTheory.IndEtaleLoc.isIndEtale_of_isLocalization W (W ⊗[A] O) O (Submonoid.powers e) hT

example : ∀ (A W O : Type) [CommRing A] [CommRing W] [CommRing O] [Algebra A W] [Algebra A O] [Algebra W O] [IsScalarTower A W O] [Algebra.Etale A W], GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap A O) → GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap W O) :=
  isIndEtale_of_etale_of_isIndEtale

end GlobalTheory.IndEtaleCancel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsNoetherianRingOfDirectedPureUnion
section
open IsLocalRing

namespace GlobalTheory.DirectedNoeth

variable {S : Type} [CommRing S] [IsLocalRing S]

theorem mem_of_forall_mem_sup_pow (T : Subring S) [IsNoetherianRing T]
    (hmax : ((maximalIdeal S).comap T.subtype).map T.subtype = maximalIdeal S)
    (hpure : ∀ J : Ideal T, (J.map T.subtype).comap T.subtype = J)
    (A : Ideal T) (x : T) (hx : ∀ n : ℕ, (x : S) ∈ A.map T.subtype ⊔ maximalIdeal S ^ n) :
    x ∈ A := by
  set m : Ideal T := (maximalIdeal S).comap T.subtype with hm
  have hjac : m ≤ Ideal.jacobson ⊥ := by
    intro y hy
    rw [Ideal.mem_jacobson_bot]
    intro z
    have hu : T.subtype (y * z + 1) ∉ maximalIdeal S := by
      intro h
      have h1 : T.subtype (y * z) ∈ maximalIdeal S := by
        rw [map_mul]; exact Ideal.mul_mem_right _ _ hy
      have h2 := Ideal.sub_mem _ h h1
      rw [map_add, add_sub_cancel_left, map_one] at h2
      exact (maximalIdeal.isMaximal S).ne_top ((Ideal.eq_top_iff_one _).mpr h2)
    have hunit : IsUnit (T.subtype (y * z + 1)) := by
      by_contra h
      exact hu ((mem_maximalIdeal _).mpr h)
    have h2 : Ideal.span {y * z + 1} = (⊤ : Ideal T) := by
      rw [← hpure (Ideal.span {y * z + 1}), Ideal.map_span, Set.image_singleton,
        Ideal.span_singleton_eq_top.mpr hunit, Ideal.comap_top]
    exact Ideal.span_singleton_eq_top.mp h2
  have hK := Ideal.iInf_pow_smul_eq_bot_of_le_jacobson (M := T ⧸ A) m hjac
  have hxn : ∀ n : ℕ, x ∈ A ⊔ m ^ n := by
    intro n
    have h := hx n
    rw [← hmax, ← Ideal.map_pow, ← Ideal.map_sup] at h
    rw [← hpure (A ⊔ m ^ n)]
    exact h
  have h0 : Ideal.Quotient.mk A x ∈ (⨅ i : ℕ, m ^ i • ⊤ : Submodule T (T ⧸ A)) := by
    rw [Submodule.mem_iInf]
    intro n
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp (hxn n)
    have : Ideal.Quotient.mk A x = b • (1 : T ⧸ A) := by
      rw [← hab, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr ha, zero_add, Algebra.smul_def,
        mul_one, Ideal.Quotient.algebraMap_eq]
    rw [this]
    exact Submodule.smul_mem_smul hb trivial
  rw [hK, Submodule.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at h0
  exact h0

theorem mem_sup_pow_of_algebraMap_mem (K : Ideal S) (x : S)
    (hx : algebraMap S (AdicCompletion (maximalIdeal S) S) x ∈
      K.map (algebraMap S (AdicCompletion (maximalIdeal S) S))) (n : ℕ) :
    x ∈ K ⊔ maximalIdeal S ^ n := by
  have h := Ideal.mem_map_of_mem (AdicCompletion.evalₐ (maximalIdeal S) n).toRingHom hx
  rw [Ideal.map_map] at h
  have hc : (AdicCompletion.evalₐ (maximalIdeal S) n).toRingHom.comp
      (algebraMap S (AdicCompletion (maximalIdeal S) S)) = Ideal.Quotient.mk _ := by
    ext y
    simp [AlgHom.commutes, Ideal.Quotient.algebraMap_eq]
  rw [hc] at h
  have h' : Ideal.Quotient.mk (maximalIdeal S ^ n) x ∈ K.map (Ideal.Quotient.mk _) := by
    have e : (AdicCompletion.evalₐ (maximalIdeal S) n).toRingHom
        (algebraMap S (AdicCompletion (maximalIdeal S) S) x) = Ideal.Quotient.mk _ x := by
      rw [← RingHom.comp_apply, hc]
    rw [← e]; exact h
  rw [Ideal.mem_quotient_iff_mem_sup] at h'
  exact h'

theorem isNoetherianRing_completion (hfg : (maximalIdeal S).FG) :
    IsNoetherianRing (AdicCompletion (maximalIdeal S) S) := by
  refine GlobalTheory.AdicNoeth.isNoetherianRing_of_isAdicComplete _
    ((maximalIdeal S).map (algebraMap S (AdicCompletion (maximalIdeal S) S))) (hfg.map _)
    (AdicCompletion.isAdicComplete_self _ hfg) ?_
  rw [← AdicCompletion.ker_evalOneₐ_eq_map _ hfg]
  letI := Ideal.Quotient.field (maximalIdeal S)
  haveI : IsNoetherianRing (S ⧸ maximalIdeal S) := inferInstance
  exact isNoetherianRing_of_ringEquiv _
    (RingHom.quotientKerEquivOfSurjective (f := (AdicCompletion.evalOneₐ (maximalIdeal S)).toRingHom)
      (AdicCompletion.evalOneₐ_surjective _)).symm

end GlobalTheory.DirectedNoeth

namespace GlobalTheory

open GlobalTheory.DirectedNoeth in

theorem isNoetherianRing_of_directed_pure_union : ∀ (S : Type) [CommRing S] [IsLocalRing S] (ι : Type)
    [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] (R : ι → Subring S), Monotone R →
    (∀ x : S, ∃ i, x ∈ R i) → (∀ i, IsNoetherianRing (R i)) →
    (∀ i, ((maximalIdeal S).comap (R i).subtype).map (R i).subtype = maximalIdeal S) →
    (∀ i (J : Ideal (R i)), (J.map (R i).subtype).comap (R i).subtype = J) → IsNoetherianRing S := by
  intro S _ _ ι _ _ _ R hmono hcov hnoeth hmax hpure
  obtain ⟨i₁⟩ := ‹Nonempty ι›
  have hfg : (maximalIdeal S).FG := by
    haveI := hnoeth i₁
    rw [← hmax i₁]
    exact (Ideal.fg_of_isNoetherianRing _).map _
  haveI := isNoetherianRing_completion hfg
  set f := algebraMap S (AdicCompletion (maximalIdeal S) S) with hf
  refine ⟨fun (I : Ideal S) => ?_⟩
  let E : ι → Ideal S := fun i => (I.comap (R i).subtype).map (R i).subtype
  have hEI : ∀ i, E i ≤ I := fun i => Ideal.map_comap_le
  have hEmono : Monotone E := by
    intro i j hij
    rw [Ideal.map_le_iff_le_comap]
    intro y hy
    have hyj : (y : S) ∈ R j := hmono hij y.2
    have : (⟨y, hyj⟩ : R j) ∈ I.comap (R j).subtype := hy
    exact Ideal.mem_map_of_mem (R j).subtype this
  obtain ⟨_, ⟨i₀, rfl⟩, hmaxl⟩ := set_has_maximal_iff_noetherian.mpr
    (inferInstance : IsNoetherian (AdicCompletion (maximalIdeal S) S) (AdicCompletion (maximalIdeal S) S))
    (Set.range fun i => (E i).map f) (Set.range_nonempty _)
  have hfg0 : (E i₀).FG := by
    haveI := hnoeth i₀
    exact (Ideal.fg_of_isNoetherianRing _).map _
  suffices hle : I ≤ E i₀ by rw [le_antisymm hle (hEI i₀)]; exact hfg0
  intro x hx
  obtain ⟨k, hk⟩ := hcov x
  obtain ⟨j, hkj, hij⟩ := directed_of (· ≤ ·) k i₀
  have hxj : x ∈ R j := hmono hkj hk
  have hEj : (E j).map f = (E i₀).map f := by
    by_contra hne
    exact hmaxl _ ⟨j, rfl⟩ (lt_of_le_of_ne (Ideal.map_mono (hEmono hij)) (Ne.symm hne))
  have hfx : f x ∈ (E i₀).map f := by
    rw [← hEj]
    apply Ideal.mem_map_of_mem
    exact Ideal.mem_map_of_mem (R j).subtype (show (⟨x, hxj⟩ : R j) ∈ I.comap (R j).subtype from hx)
  have hij' : R i₀ ≤ R j := hmono hij
  let A : Ideal (R j) := (I.comap (R i₀).subtype).map (Subring.inclusion hij')
  have hA : A.map (R j).subtype = E i₀ := by
    simp only [A, E, Ideal.map_map]
    rfl
  have hxA : (⟨x, hxj⟩ : R j) ∈ A := by
    haveI := hnoeth j
    apply mem_of_forall_mem_sup_pow (R j) (hmax j) (hpure j) A
    intro n
    rw [hA]
    exact mem_sup_pow_of_algebraMap_mem (E i₀) x hfx n
  have := Ideal.mem_map_of_mem (R j).subtype hxA
  rwa [hA] at this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OpOfAevalExists
section
open GlobalTheory.Cong

noncomputable section

namespace GlobalTheory.Cong.OpPoly

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)

def opHom (v : V) : (G →₀ ℂ) →+ V :=
  Finsupp.liftAddHom fun g => (smulAddHom ℂ V).flip (ρ g v)

theorem opHom_apply (v : V) (F : G →₀ ℂ) : opHom ρ v F = opOf ρ F v := by
  rw [opHom, Finsupp.liftAddHom_apply, opOf]
  exact Finsupp.sum_congr fun g _ => rfl

theorem opOf_single (g : G) (c : ℂ) (v : V) : opOf ρ (Finsupp.single g c) v = c • ρ g v := by
  simp [opOf, Finsupp.sum_single_index]

theorem opOf_add (F F' : G →₀ ℂ) (v : V) : opOf ρ (F + F') v = opOf ρ F v + opOf ρ F' v := by
  simp only [← opHom_apply, map_add]

theorem opOf_smul (F : G →₀ ℂ) (c : ℂ) (v : V) : opOf ρ F (c • v) = c • opOf ρ F v := by
  simp [opOf, Finsupp.smul_sum, smul_comm c]

def conv (F f : G →₀ ℂ) : G →₀ ℂ :=
  F.sum fun g a => f.sum fun h b => Finsupp.single (g * h) (a * b)

theorem opOf_conv (F f : G →₀ ℂ) (v : V) : opOf ρ (conv F f) v = opOf ρ F (opOf ρ f v) := by
  rw [← opHom_apply]
  simp only [conv, Finsupp.sum, map_sum, opHom_apply, opOf_single]
  simp only [opOf, Finsupp.sum, map_sum, map_smul, Finset.smul_sum, mul_smul, map_mul, Module.End.mul_apply]

end GlobalTheory.Cong.OpPoly
end
end

