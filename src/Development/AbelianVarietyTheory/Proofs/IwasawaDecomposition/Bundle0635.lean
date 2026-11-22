import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0610
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0168
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0619
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.UnifMetricScalar
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0009
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0020
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HasSumPolyDerivMulProdAddMatrix
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0015
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0055
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0140
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0492
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.LiftLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0617
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1123
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2153
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LUnifOfRhoGeoEquivAll
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0024
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0565
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0602
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0599
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0620
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0621
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodFrameLimitsOfOrbit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedIUnionCell
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)

noncomputable section

namespace GlobalTheory.GrCl

section CellsInP

open MvPolynomial
open GlobalTheory.ProjSpace (grading spMap_pt pt_str_assoc pt_baseChange pt_eq_pt_iff span_range_comp_eq_top exists_mem_chart
  pt_preimage_basicOpen isPullback_baseChange baseChange mem_spOpen)
open GlobalTheory.SplitCells (lin lin_hom)

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R S : Type} [CommRing R] [CommRing S] {N : ℕ} {ρ : R →+* S} {J : Type} {ξ : J → Fin (N + 1) → S}
  {ℓ : J → Fin (N + 1) → R}

theorem eval₂_lin' (a : Fin (N + 1) → R) (w : Fin (N + 1) → S) : eval₂ ρ w (lin a) = ∑ q, ρ (a q) * w q := by
  simp [lin, eval₂_sum]

theorem cell_immersion (hc : Cells ρ ξ ℓ) (j : J) (hv) :
    IsImmersion (pt ρ (ξ j) hv) ∧ ∃ T : Set (PSpace R N), IsClosed T ∧
      Set.range (pt ρ (ξ j) hv) = T ∩ (Proj.basicOpen (grading R N) (lin (ℓ j)) : Set (PSpace R N)) := by
  have h1 : eval₂Hom ρ (ξ j) (lin (ℓ j)) = 1 := by rw [coe_eval₂Hom, eval₂_lin', hc.one]
  have hu : IsUnit (eval₂Hom ρ (ξ j) (lin (ℓ j))) := h1 ▸ isUnit_one
  have hm : lin (ℓ j) ∈ grading R N 1 := lin_hom _
  have e : pt ρ (ξ j) hv = _ := ProjPoint.ofHom_eq_awayι _ _ _ one_pos hm hu
  have hs : Function.Surjective (ProjPoint.awayLift (grading R N) (eval₂Hom ρ (ξ j)) _ hu) := by
    intro p
    obtain ⟨F, rfl⟩ := hc.gen j p
    change _ ∈ (ProjPoint.awayLift (grading R N) (eval₂Hom ρ (ξ j)) _ hu).range
    induction F using MvPolynomial.induction_on with
    | C a =>
      have := ProjPoint.awayLift_mk_mul (grading R N) _ hu hm 0 (C a) (isHomogeneous_C _ a)
      rw [pow_zero, mul_one] at this
      exact ⟨_, this⟩
    | add F G hF hG => rw [map_add]; exact add_mem hF hG
    | mul_X F k hF =>
      rw [map_mul]
      refine mul_mem hF ?_
      have := ProjPoint.awayLift_mk_mul (grading R N) _ hu hm 1 (X k) (isHomogeneous_X R k)
      rw [h1, one_pow, mul_one] at this
      exact ⟨_, this⟩
  have hcl : IsClosedImmersion (Spec.map (CommRingCat.ofHom (ProjPoint.awayLift (grading R N) _ _ hu))) :=
    IsClosedImmersion.spec_of_surjective _ hs
  refine ⟨by rw [e]; infer_instance, ?_⟩
  obtain ⟨T, hT, hT'⟩ := (Proj.awayι (grading R N) _ hm one_pos).isOpenEmbedding.isInducing.isClosed_iff.1
    (Spec.map (CommRingCat.ofHom (ProjPoint.awayLift (grading R N) _ _ hu))).isClosedEmbedding.isClosed_range
  refine ⟨T, hT, ?_⟩
  have hr : Set.range (Proj.awayι (grading R N) _ hm one_pos) = Proj.basicOpen (grading R N) (lin (ℓ j)) :=
    congrArg (fun U : (PSpace R N).Opens => (U : Set (PSpace R N))) (Proj.opensRange_awayι _ _ hm one_pos)
  rw [e, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, ← hT', Set.image_preimage_eq_inter_range, hr]

theorem cell_overlap (hc : Cells ρ ξ ℓ) (hv : ∀ j, Ideal.span (Set.range (ξ j)) = ⊤) {j j' : J} {x : PSpace R N}
    (hx : x ∈ Set.range (pt ρ (ξ j') (hv j'))) (h : x ∈ Proj.basicOpen (grading R N) (lin (ℓ j))) :
    x ∈ Set.range (pt ρ (ξ j) (hv j)) := by
  obtain ⟨y, rfl⟩ := hx
  have hy : y.asIdeal.IsPrime := y.isPrime
  let K : Type := y.asIdeal.ResidueField
  let ψ' : S →+* K := algebraMap S K
  have h2 : eval₂ ρ (ξ j') (lin (ℓ j)) ∉ y.asIdeal := by
    rw [← mem_spOpen, ← pt_preimage_basicOpen ρ (ξ j') (hv j') one_pos (lin_hom _)]
    exact h
  have h3 : ∑ q, ψ' (ρ (ℓ j q)) * ψ' (ξ j' q) ≠ 0 := by
    intro h0
    apply h2
    rw [eval₂_lin', ← Ideal.algebraMap_residueField_eq_zero, map_sum]
    simpa only [map_mul] using h0
  obtain ⟨ψ, u, hb, hu⟩ := hc.ovl K j j' ψ' h3
  let z : Sp K := IsLocalRing.closedPoint K
  have hz : spMap ψ' z = y := by
    refine PrimeSpectrum.ext ?_
    change Ideal.comap ψ' (IsLocalRing.maximalIdeal K) = y.asIdeal
    rw [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot]
    exact Ideal.ker_algebraMap_residueField _
  have e : spMap ψ ≫ pt ρ (ξ j) (hv j) = spMap ψ' ≫ pt ρ (ξ j') (hv j') := by
    rw [spMap_pt, spMap_pt, hb]
    exact (pt_eq_pt_iff _ _ _).2 ⟨u, hu⟩
  refine ⟨spMap ψ z, ?_⟩
  rw [← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply, hz]

theorem isClosed_iUnion_cell (hc : Cells ρ ξ ℓ) (hv : ∀ j, Ideal.span (Set.range (ξ j)) = ⊤) :
    IsClosed (⋃ j, Set.range (pt ρ (ξ j) (hv j))) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro y hy
  by_cases h : ∃ j, y ∈ Proj.basicOpen (grading R N) (lin (ℓ j))
  · obtain ⟨j, hj⟩ := h
    obtain ⟨T, hT, e⟩ := (cell_immersion hc j (hv j)).2
    have hyT : y ∉ T := fun h' => hy (Set.mem_iUnion.2 ⟨j, e ▸ ⟨h', hj⟩⟩)
    refine Filter.mem_of_superset
      ((hT.isOpen_compl.inter (Proj.basicOpen (grading R N) (lin (ℓ j))).isOpen).mem_nhds ⟨hyT, hj⟩) ?_
    rintro z ⟨h1, h2⟩ hz
    obtain ⟨j', hz⟩ := Set.mem_iUnion.1 hz
    have := cell_overlap hc hv hz h2
    rw [e] at this
    exact h1 this.1
  · push_neg at h
    obtain ⟨q, hq⟩ := exists_mem_chart R N y
    obtain ⟨T, _, jj, a, ha⟩ := hc.lin q
    let F : MvPolynomial (Fin (N + 1)) R := X q - ∑ t, C (a t) * lin (ℓ (jj t))
    have hF : F.IsHomogeneous 1 := by
      refine (isHomogeneous_X R q).sub (IsHomogeneous.sum _ _ _ fun t _ => ?_)
      simpa using (isHomogeneous_C _ (a t)).mul (lin_hom (ℓ (jj t)))
    have hyF : y ∈ Proj.basicOpen (grading R N) F := by
      intro hmem
      refine hq ?_
      have h4 : ∑ t, C (a t) * lin (ℓ (jj t)) ∈ y.asHomogeneousIdeal :=
        sum_mem fun t _ => Ideal.mul_mem_left _ _ (not_not.1 (h (jj t)))
      have := add_mem hmem h4
      simpa [F] using this
    refine Filter.mem_of_superset ((Proj.basicOpen (grading R N) F).isOpen.mem_nhds hyF) ?_
    intro z hz hz'
    obtain ⟨j', w, rfl⟩ := Set.mem_iUnion.1 hz'
    have h5 : w ∈ pt ρ (ξ j') (hv j') ⁻¹ᵁ Proj.basicOpen (grading R N) F := hz
    rw [pt_preimage_basicOpen ρ (ξ j') (hv j') one_pos hF, mem_spOpen] at h5
    refine h5 ?_
    have h6 : eval₂ ρ (ξ j') F = 0 := by
      simp only [F, eval₂_sub, eval₂_X, eval₂_sum, eval₂_mul, eval₂_C, eval₂_lin']
      rw [ha j']
      simp
    rw [h6]
    exact zero_mem _

theorem cells_immersed : ∀ (O : Type) [CommRing O] (Z P : Scheme.{0}) (s : Z ⟶ Sp O) (N : ℕ) (p₁ : P ⟶ Z) (p₂ : P ⟶ PSpace O N), IsPullback p₁ p₂ s (PSpace.str O N) → ∀ (R S : Type) [CommRing R] [CommRing S] (χ : Sp R ⟶ Z) (g : O →+* R) (ρ : R →+* S) (J : Type) (ξ : J → Fin (N + 1) → S) (ℓ : J → Fin (N + 1) → R) (i : J → (Sp S ⟶ P)), IsOpenImmersion χ → χ ≫ s = spMap g → Cells ρ ξ ℓ → (∀ j, i j ≫ p₁ = spMap ρ ≫ χ) → (∀ j, ∃ hv, i j ≫ p₂ = pt (ρ.comp g) (ξ j) hv) → (∀ j, IsImmersion (i j)) ∧ (∀ j, ∃ U : P.Opens, Set.range (i j) = (⋃ j', Set.range (i j')) ∩ (U : Set P)) ∧ ∃ T : Set P, IsClosed T ∧ ⋃ j, Set.range (i j) = T ∩ p₁ ⁻¹' Set.range χ := by
  intro O _ Z P s N p₁ p₂ hP R S _ _ χ g ρ J ξ ℓ i hχ hg hc hi₁ hi₂
  have hb := isPullback_baseChange N g
  rw [← hg] at hb
  let e : PSpace R N ⟶ P := hP.flip.lift (baseChange N g) (PSpace.str R N ≫ χ) (by rw [hb.w, Category.assoc])
  have he : IsPullback e (PSpace.str R N) p₁ χ := hb.of_right' hP.flip
  have he₂ : e ≫ p₂ = baseChange N g := hP.flip.lift_fst _ _ _
  have heo : IsOpenImmersion e := MorphismProperty.of_isPullback he.flip hχ
  have hr : Set.range e = p₁ ⁻¹' Set.range χ := by
    rw [← Scheme.Pullback.range_fst, ← he.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp]
    exact he.isoPullback.hom.surjective.range_comp _
  choose hv hi₂ using hi₂
  have hj : ∀ j, i j = pt ρ (ξ j) (hv j) ≫ e := fun j =>
    hP.hom_ext (by rw [hi₁, Category.assoc, he.w, pt_str_assoc]) (by rw [hi₂, Category.assoc, he₂, pt_baseChange])
  have hm : ∀ j, Set.range (i j) = e '' Set.range (pt ρ (ξ j) (hv j)) := fun j => by
    rw [hj, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  have hinj := e.isOpenEmbedding.injective
  refine ⟨fun j => ?_, fun j => ⟨e ''ᵁ Proj.basicOpen (grading R N) (lin (ℓ j)), Set.ext fun x => ?_⟩,
    (e '' (⋃ j, Set.range (pt ρ (ξ j) (hv j)))ᶜ)ᶜ,
    (e.isOpenEmbedding.isOpenMap _ (isClosed_iUnion_cell hc hv).isOpen_compl).isClosed_compl,
    Set.ext fun x => ?_⟩
  · have := (cell_immersion hc j (hv j)).1
    rw [hj]
    infer_instance
  · simp only [Set.mem_inter_iff, Set.mem_iUnion, hm]
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨T, -, eT⟩ := (cell_immersion hc j (hv j)).2
      have hy₂ := hy
      rw [eT] at hy₂
      exact ⟨⟨j, y, hy, rfl⟩, y, hy₂.2, rfl⟩
    · rintro ⟨⟨j', y, hy, rfl⟩, y', hy', e'⟩
      obtain rfl := hinj e'
      exact ⟨y', cell_overlap hc hv hy hy', rfl⟩
  · simp only [Set.mem_inter_iff, Set.mem_iUnion, hm, ← hr]
    constructor
    · rintro ⟨j, y, hy, rfl⟩
      refine ⟨?_, y, rfl⟩
      rintro ⟨y', hy', e'⟩
      obtain rfl := hinj e'
      exact hy' (Set.mem_iUnion.2 ⟨j, hy⟩)
    · rintro ⟨hx, y, rfl⟩
      by_contra hn
      refine hx ⟨y, fun hy => hn ?_, rfl⟩
      obtain ⟨j, hy⟩ := Set.mem_iUnion.1 hy
      exact ⟨j, y, hy, rfl⟩

end CellsInP

end GlobalTheory.GrCl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KeySectionEqConstMulThetaFunctionFibre
section
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FibreKeyTheta

variable {X : Scheme.{0}}

theorem toStk_valAt' (x : Sp ℂ ⟶ X) (U : X.Opens) (z : Sp ℂ) (h : x z ∈ U) (a : Γ(X, U)) :
    toStk z (valAt' x U a) = gs x z U a := by
  rw [valAt', dif_pos ((top_le_iff_mem x U z).2 h), valAt, gs_eq x z U h]
  show ((Sp ℂ).presheaf.germ ⊤ z trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
    ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom _)) = _
  rw [Iso.hom_inv_id_apply]
  exact TopCat.Presheaf.germ_res_apply (Sp ℂ).presheaf (homOfLE ((top_le_iff_mem x U z).2 h)) z trivial _

theorem cst_id (z : Sp ℂ) (a : ℂ) : cst (𝟙 (Sp ℂ)) z a = toStk z a := by
  rw [cst, gs_eq (𝟙 (Sp ℂ)) z ⊤ trivial]
  rfl

def isoSymm {A B : LB X} (w : LB.Iso A B) : LB.Iso B A :=
  ⟨fun p => (res (fun _ hy => ⟨hy.2, hy.1⟩ : A.U p.1 ⊓ B.U p.2 ≤ B.U p.2 ⊓ A.U p.1) (w.s (p.2, p.1)))⁻¹⟩

theorem isoSymm_isGen {A B : LB X} (w : LB.Iso A B) (hw : w.IsGen) : (isoSymm w).IsGen := by
  have le : ∀ p : A.ι × B.ι, A.U p.1 ⊓ B.U p.2 ≤ B.U p.2 ⊓ A.U p.1 := fun p y hy => ⟨hy.2, hy.1⟩
  intro p q
  refine unit_ext fun y hy => ?_
  have hm : (𝟙 X : X ⟶ X) y ∈ B.U p.2 ⊓ A.U p.1 ⊓ (B.U q.2 ⊓ A.U q.1) := ⟨le p hy.1, le q hy.2⟩
  have e := congrArg (gm (𝟙 X) y (B.U p.2 ⊓ A.U p.1 ⊓ (B.U q.2 ⊓ A.U q.1))) (hw (p.2, p.1) (q.2, q.1))
  have e' := (gm_res _ y _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_div A B (𝟙 X) y (p.2, p.1) (q.2, q.1) hm) (gm_res _ y _ hm _))))
  have v : ∀ p : A.ι × B.ι, y ∈ A.U p.1 ⊓ B.U p.2 → gm (𝟙 X) y (A.U p.1 ⊓ B.U p.2) (res (le p) (w.s (p.2, p.1)))⁻¹ =
      (gm (𝟙 X) y (B.U p.2 ⊓ A.U p.1) (w.s (p.2, p.1)))⁻¹ := fun p hp =>
    (map_inv _ _).trans (congrArg (·⁻¹) (gm_res _ y _ hp _))
  refine ((gm_res _ y _ hy _).trans ((v p hy.1).trans (congrArg (·⁻¹) e'))).trans (Eq.symm ?_)
  refine ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_div B A (𝟙 X) y p q hy)
    ((gm_res _ y _ hy _).trans (v q hy.2)))).trans ?_
  rw [mul_inv, mul_inv, inv_inv, mul_comm (gm (𝟙 X) y _ (A.g p.1 q.1))]
  rfl

end GlobalTheory.FibreKeyTheta

open GlobalTheory.FibreKeyTheta in

theorem GlobalTheory.FibreKeyTheta.th_isFn_const_mul : ∀ (x : KeyIn ℂ) (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left) (y : Sp ℂ ⟶ S) (Φ : x.P.A.left ⟶ G.left) (g : ℕ) (u : HolUnif x.P.A x.P.L g) (w : LB.Iso (L.pull Φ) x.P.L) (θ : (Fin g → ℂ) → ℂ) (fr : L.ι → (Fin g → ℂ) → ℂ) (s : (L.pull (pullback.fst G.hom y)).Sec), L.IsLB → IsPullback Φ x.P.A.hom G.hom y → w.IsGen → (∃ z, θ z ≠ 0) → (∀ j z, ⊤ ≤ ((u.ex z).left ≫ Φ) ⁻¹ᵁ L.U j → fr j z ≠ 0) → (∀ k j z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (x.P.L.U k ⊓ (L.pull Φ).U j) → u.fr k z = valAt' (u.ex z).left (x.P.L.U k ⊓ (L.pull Φ).U j) (w.s (k, j)).val * fr (j PUnit.unit) z) → (∀ j z (p : Sp ℂ ⟶ pullback G.hom y), p ≫ pullback.fst _ _ = (u.ex z).left ≫ Φ → p ≫ pullback.snd _ _ = 𝟙 _ → ⊤ ≤ ((u.ex z).left ≫ Φ) ⁻¹ᵁ L.U j → valAt' p ((L.pull (pullback.fst G.hom y)).U (fun _ => j)) (s.f (fun _ => j)) = θ z * fr j z) → ∃ c₀ : ℂ, u.IsFn x.th (fun z => c₀ * θ z) := by
  intro x S G _ L y Φ g u w θ fr s hL hΦ hw hθ hfr hu hs
  classical
  let km : x.P.A.left ⟶ pullback G.hom y := pullback.lift Φ x.P.A.hom hΦ.w
  have km1 : km ≫ pullback.fst G.hom y = Φ := pullback.lift_fst _ _ _
  have km2 : km ≫ pullback.snd G.hom y = x.P.A.hom := pullback.lift_snd _ _ _
  have le : ∀ j : L.ι, Φ ⁻¹ᵁ L.U j ≤ km ⁻¹ᵁ (L.pull (pullback.fst G.hom y)).U (fun _ => j) := fun j p hp =>
    mem_pull.2 ((congrArg (fun e => e p ∈ L.U j) km1).mpr hp)
  let σ : ∀ j : L.ι, Γ(x.P.A.left, Φ ⁻¹ᵁ L.U j) := fun j => (km.appLE _ _ (le j)).hom (s.f (fun _ => j))
  have hσv : ∀ {Z : Scheme.{0}} (r : Z ⟶ x.P.A.left) (z : Z) (j : L.ι), Φ (r z) ∈ L.U j →
      gs r z _ (σ j) = gs (r ≫ km) z _ (s.f (fun _ => j)) := fun r z j h =>
    gs_appLE km _ _ (le j) r z h _
  have hσ : ∀ (p : x.P.A.left) j j', Φ p ∈ L.U j → Φ p ∈ L.U j' →
      gs (𝟙 _) p _ (σ j) = (gm Φ p (L.U j ⊓ L.U j') (L.g j j')).val * gs (𝟙 _) p _ (σ j') := by
    intro p j j' h h'
    rw [hσv _ p j h, hσv _ p j' h', Category.id_comp]
    refine (sec_trans s km p (le j h) (le j' h')).trans ?_
    congr 2
    simp [trF, km1]
  have hwD : PGen (isoSymm w) := (isGen_iff _).1 (isoSymm_isGen w hw)
  obtain ⟨s', hs'⟩ := sec_down hwD hL x.P.isLB σ hσ
  have refl : LBIso x.P.L (x.P.L.pull (𝟙 _)) :=
    LBIso.chartPull (chartPullUnpull x.P.L _ rfl) (chartPullId _)
      (exists_iso_linComb (F := 𝟙 x.P.A.left) x.P.isLB (fun _ : PUnit => 𝟙 _) (fun _ => 1) fun _ _ _ => rfl)
  obtain ⟨a, ha, -⟩ := GlobalTheory.SectionBaseChange.generates GlobalTheory.allSixLaws.1.secBaseChange x.P (t := 𝟙 _) (φ := 𝟙 _)
    (IsPullback.of_horiz_isIso ⟨by simp⟩) x.P.isLB refl x.th x.th_ne s'
  obtain ⟨pt⟩ : Nonempty (Sp ℂ) := ⟨(⊥ : PrimeSpectrum ℂ)⟩
  have key : ∀ i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ x.P.L.U i →
      a * valAt' (u.ex z).left (x.P.L.U i) (x.th.f i) = θ z * u.fr i z := by
    intro i z hi
    have hri : (u.ex z).left pt ∈ x.P.L.U i := (top_le_iff_mem _ _ pt).1 hi
    obtain ⟨j, hj⟩ := exists_chart hL (Φ ((u.ex z).left pt))
    have hj' : ⊤ ≤ ((u.ex z).left ≫ Φ) ⁻¹ᵁ L.U j := (top_le_iff_mem _ _ pt).2 hj
    have hr0 : (u.ex z).left ≫ x.P.A.hom = 𝟙 _ := by simpa using Over.w (u.ex z)
    have hr1 : ((u.ex z).left ≫ km) ≫ pullback.snd G.hom y = 𝟙 _ := by rw [Category.assoc, km2, hr0]
    have e1 := hs j z ((u.ex z).left ≫ km) (by rw [Category.assoc, km1]) hr1 hj'
    have hm : (u.ex z).left pt ∈ x.P.L.U i ⊓ (L.pull Φ).U (fun _ => j) := ⟨hri, mem_pull.2 hj⟩
    have e2 := hu i (fun _ => j) z ((top_le_iff_mem _ _ pt).2 hm)
    have e3 := hs' (Sp ℂ) (u.ex z).left pt j i hj hri
    rw [hσv _ pt j hj, ← toStk_valAt' ((u.ex z).left ≫ km) _ pt (le j hj), e1, ha i, gs_mul _ pt _ hri, gs_constFn _ _ _ pt hri,
      hr0] at e3
    erw [cst_id] at e3
    rw [← toStk_valAt' _ _ pt hri] at e3
    have hm' : (u.ex z).left pt ∈ (L.pull Φ).U (fun _ => j) ⊓ x.P.L.U i := ⟨mem_pull.2 hj, hri⟩
    have gwv : gw (isoSymm w) (u.ex z).left pt j i =
        (gm (u.ex z).left pt (x.P.L.U i ⊓ (L.pull Φ).U (fun _ => j)) (w.s (i, fun _ => j)))⁻¹ :=
      (map_inv _ _).trans (congrArg (·⁻¹) (gm_res _ pt _ hm' _))
    rw [gwv, Units.eq_inv_mul_iff_mul_eq] at e3
    have e3' : toStk pt (valAt' (u.ex z).left (x.P.L.U i ⊓ (L.pull Φ).U (fun _ => j)) (w.s (i, fun _ => j)).val *
        (θ z * fr j z)) = toStk pt (a * valAt' (u.ex z).left (x.P.L.U i) (x.th.f i)) := by
      rw [map_mul, map_mul (toStk pt) a]
      erw [toStk_valAt' _ _ pt hm, gs_unit _ pt _ hm]
      exact e3
    have e4 := (toStk pt).injective e3'
    rw [e2, ← e4]
    ring
  obtain ⟨z0, hz0⟩ := hθ
  obtain ⟨i0, hi0⟩ := exists_chart x.P.isLB ((u.ex z0).left pt)
  have hi0' : ⊤ ≤ (u.ex z0).left ⁻¹ᵁ x.P.L.U i0 := (top_le_iff_mem _ _ pt).2 hi0
  have ha0 : a ≠ 0 := by
    intro h0
    have e := key i0 z0 hi0'
    rw [h0, zero_mul] at e
    exact mul_ne_zero hz0 (u.fr_ne i0 z0 hi0') e.symm
  refine ⟨a⁻¹, fun i z hi => ?_⟩
  have e := key i z hi
  show _ = a⁻¹ * θ z * u.fr i z
  rw [mul_assoc, ← e, ← mul_assoc, inv_mul_cancel₀ ha0, one_mul]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LUnifAtDat
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Top.Bl

open Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Mult

set_option maxHeartbeats 1000000 in

theorem lUnif_atDat : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Hk3.HoweUnram →
    GlobalTheory.Mem.Top.Bl.AtDat fun _ B f T w Z hX Wt z => z.R.toRealDat.LUnif := by
  intro _ _ _
  refine StepW.of_all fun K B f T w _ _ _ Z hX Wt z _ _ hEx hIn => ?_
  have hch := z.pins.char
  have hC : GlobalTheory.RealGeo.PreChar z.R.toRealDat :=
    ⟨hch.base.lev, hch.base.grp.red_R, hch.base.grp.red_L, hch.base.grp.record, hch.base.fam, hch.base.models,
      RealDat.chain_of_weak hch.base.chain hEx, RealDat.thP_of_weak hch.base.thP hEx⟩
  have hχ : z.R.toRealDat.grp_chiW := hch.base.grp.chiW
  have ht : TieIn z.core z.R.toRealDat z.geo.κ z.geo.v₀ :=
    ⟨z.geo.fw.laws, z.geo.fw.alg_eq, z.geo.fw.kap, z.geo.fw.hv₀, z.geo.fw.chiR, z.geo.fw.x0⟩
  have hp : z.core.pb = z.R.toRealDat.C.P.pb :=
    GlobalTheory.PinsFixHalf.pb_eq_of_pins z.core z.R.toRealDat z.geo.κ z.geo.v₀ z.geo.O hC.lev z.geo.fw.laws z.geo.pins
  have hx := GlobalTheory.T.exists_equivariant_unit_constants_goodEmbedding z.core z.R.toRealDat z.geo.κ z.geo.v₀ z.geo.O hC.lev ht hp z.geo.pins
  have hU := hIn.jUnif
  intro i σ
  exact ⟨(GlobalTheory.TiedUnif.indep_span_of_tie z.geo.fw hC.models.HW z.geo.bar hU i σ).1,
    (GlobalTheory.TiedUnif.indep_span_of_tie z.geo.fw hC.models.HW z.geo.bar hU i σ).2,
    GlobalTheory.TiedUnif.rhoIs_of_eqAt z.geo.fw hC.models.HW hC.models.gW hχ z.geo.bar z.geo.rhoGeo hU i σ
      (fun h hV => z.geo.equivAll i _ h hV (hx i _ h hV))
      fun h hV => z.geo.equivAll i _ (good_resC z.core h) hV (hx i _ (good_resC z.core h) hV)⟩

end GlobalTheory.Mem.Top.Bl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LintegralLeadingMinorFlagDensityPosDef
section
open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal

namespace GlobalTheory.FlagFibre.FlagInt

theorem isEmpty_low_one : IsEmpty (Low 1) :=
  ⟨fun s => by have h := s.2; rw [Subsingleton.elim s.1.1 s.1.2] at h; exact lt_irrefl _ h⟩

theorem isEmpty_low_zero : IsEmpty (Low 0) := ⟨fun s => s.1.1.elim0⟩

theorem volume_univ_of_isEmpty {ι : Type} [Fintype ι] [IsEmpty ι] : (volume : Measure (ι → ℂ)) Set.univ = 1 := by
  rw [volume_pi, Measure.pi_univ]; simp

theorem dens_one (A : Matrix (Fin 1) (Fin 1) ℂ) (y : Low 1 → ℂ) : dens A y = 1 := by
  simp only [dens, lminor, Fin.prod_univ_one]
  have : IsEmpty (Fin ((0 : Fin 1).castSucc : ℕ)) := ⟨fun x => x.elim0⟩
  rw [det_isEmpty]; simp

theorem re_facts {n : Type} [Fintype n] [DecidableEq n] {H : Matrix n n ℂ} (h : H.PosDef) :
    0 < H.det.re ∧ H.det = (H.det.re : ℂ) := by
  have := Complex.pos_iff.1 h.det_pos
  exact ⟨this.1, Complex.ext (by simp) (by simp [← this.2])⟩

theorem lintegral_dens : ∀ (m : ℕ) (A : Matrix (Fin m) (Fin m) ℂ), A.PosDef →
    ∫⁻ y : Low m → ℂ, ENNReal.ofReal (dens A y) = ENNReal.ofReal (A.det.re ^ (1 - (m : ℤ)) / flagConst m) := by
  intro m
  induction m with
  | zero =>
    intro A _
    have := isEmpty_low_zero
    simp [dens, flagConst, volume_univ_of_isEmpty]
  | succ p ih =>
    intro A hA
    have := isEmpty_low_one
    obtain ⟨e, he⟩ := exists_isBlockOrderedSumEquiv p 1
    have hA' : (reindex e e A).PosDef := hA.submatrix e.symm.injective
    have hd : (reindex e e A).det = A.det := det_reindex_self e A
    have hm : Measurable fun y : Low (p + 1) → ℂ => ENNReal.ofReal (dens A y) := (measurable_dens A).ennreal_ofReal
    have hm2 : Measurable fun w => ENNReal.ofReal (dens A (glue e w)) := hm.comp (continuous_glue e).measurable
    obtain ⟨hDpos, hD⟩ := re_facts hA
    have hf := flagConst_pos p
    have hc : 0 ≤ A.det.re ^ (1 - (p : ℤ)) / flagConst p := by positivity
    rw [← (GlobalTheory.T.measurePreserving_glueLowerUnitriangularBlocks _ _ _ e he).lintegral_comp hm, Measure.volume_eq_prod, lintegral_prod _ hm2.aemeasurable]
    have key : ∀ v : Fin p × Fin 1 → ℂ,
        ∫⁻ w : (Low 1 → ℂ) × (Low p → ℂ), ENNReal.ofReal (dens A (glue e (v, w))) =
        ENNReal.ofReal (A.det.re ^ (1 - (p : ℤ)) / flagConst p) *
          ENNReal.ofReal ((shear (reindex e e A) (toMat v)).toBlocks₂₂.det.re ^ (-((p + 1 : ℕ) : ℤ))) := by
      intro v
      have hS := posDef_shear hA' (toMat v)
      obtain ⟨-, h2, h3⟩ := posDef_blocks hS
      have hu := h2.det_pos.ne'.isUnit
      have hm3 : Measurable fun w : (Low 1 → ℂ) × (Low p → ℂ) => ENNReal.ofReal (dens A (glue e (v, w))) :=
        hm2.comp measurable_prodMk_left
      rw [Measure.volume_eq_prod, lintegral_prod _ hm3.aemeasurable]
      have hg := fun (y1 : Low 1 → ℂ) (y2 : Low p → ℂ) => GlobalTheory.T.leadingMinorFlagDensity_glueLowerUnitriangular _ _ _ e he A (v, y1, y2) hu
      simp only [dens_one, one_mul] at hg
      simp only [hg]
      have hdet := det_eq_mul_schur hu
      rw [det_shear, hd] at hdet
      obtain ⟨hp2, he2⟩ := re_facts h2
      obtain ⟨hp3, he3⟩ := re_facts h3
      have hI := ih _ h3
      set S := shear (reindex e e A) (toMat v)
      have hn : ‖S.toBlocks₂₂.det‖ = S.toBlocks₂₂.det.re := by
        conv_lhs => rw [he2, Complex.norm_real, Real.norm_of_nonneg hp2.le]
      have hre : A.det.re = S.toBlocks₂₂.det.re * (schur S).det.re := by
        rw [hdet]; conv_lhs => rw [he2, he3, ← Complex.ofReal_mul, Complex.ofReal_re]
      rw [lintegral_const, volume_univ_of_isEmpty, mul_one, hn]
      simp only [ENNReal.ofReal_mul (zpow_nonneg hp2.le _)]
      rw [lintegral_const_mul _ (measurable_dens _).ennreal_ofReal, hI, ← ENNReal.ofReal_mul (zpow_nonneg hp2.le _),
        ← ENNReal.ofReal_mul hc, hre, mul_zpow]
      congr 1
      have : S.toBlocks₂₂.det.re ^ (-(2 * p : ℤ)) =
          S.toBlocks₂₂.det.re ^ (1 - (p : ℤ)) * S.toBlocks₂₂.det.re ^ (-((p + 1 : ℕ) : ℤ)) := by
        rw [← zpow_add₀ hp2.ne']; congr 1; push_cast; ring
      rw [this]; ring
    simp only [key]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, GlobalTheory.T.hua_integral_positive_definite_quadric p 1 _ hA', ← ENNReal.ofReal_mul hc, hd,
      flagConst_add p 1]
    congr 1
    have h1 : flagConst 1 = 1 := by simp [flagConst]
    have : A.det.re ^ (1 - ((p + 1 : ℕ) : ℤ)) = A.det.re ^ (1 - (p : ℤ)) * A.det.re ^ (-((1 : ℕ) : ℤ)) := by
      rw [← zpow_add₀ hDpos.ne']; congr 1; push_cast; ring
    rw [this, h1]; ring

end GlobalTheory.FlagFibre.FlagInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSpanOfPluckerProportionalStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_span_of_plucker_proportional : ∀ (K : Type) [Field K] (M k : ℕ) (c c' : Fin k → Fin (M + 1) → K) (a : K), plk c' id ≠ 0 → plk c' id = a • plk c id → ∀ l, c' l ∈ Submodule.span K (Set.range c) := by
  first | exact @GlobalTheory.FlagEmb.mem_span_of_plk_eq_smul | exact GlobalTheory.FlagEmb.mem_span_of_plk_eq_smul | (intros; apply GlobalTheory.FlagEmb.mem_span_of_plk_eq_smul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NomePowerSeriesDvdOfSumBoundedStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nomePowerSeries_dvd_of_sum_bounded : ∀ (G H : PowerSeries ℂ) (T C : ℝ) (g h : ℂ → ℂ), H ≠ 0 → (∀ w : ℂ, T < w.im → SumsAt G w (g w) ∧ SumsAt H w (h w) ∧ (h w ≠ 0 → ‖g w‖ ≤ C * ‖h w‖)) → H ∣ G := by
  first | exact @GlobalTheory.powerSeries_dvd_of_sum_bounded | exact GlobalTheory.powerSeries_dvd_of_sum_bounded | (intros; apply GlobalTheory.powerSeries_dvd_of_sum_bounded <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodFrameLimitsOfOrbitStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_frame_limits_of_orbit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (X : Data E N) (T : ℝ) (M : ℕ) (γ : GL (Fin N) E) (x : ℂ → Frame X.Ψ N) (la : Wt X.Ψ N) (n : ℕ) (v : Fin n → Fin N → E) (Lp : Fin n → X.Ψ → Fin (N - X.p0) → ℂ) (Lm : Fin n → X.Ψ → Fin X.p0 → ℂ), IsOrbit X T M γ x → (∀ τ (j : Fin N), (X.p0 ≤ j → 0 ≤ la τ j) ∧ ((j : ℕ) < X.p0 → la τ j ≤ 0)) → ((∀ j (τ : X.Ψ) (i : Fin (N - X.p0)), Tendsto (fun w => perFr X (x w) (v j) τ.1 i) imTop (𝓝 (Lp j τ i))) ∧ (∀ j (τ : X.Ψ) (i : Fin X.p0), Tendsto (fun w => perFr X (x w) (v j) (conjEmb τ.1) i) imTop (𝓝 (Lm j τ i))) ∧ ∀ τ : X.Ψ, Submodule.span ℂ (Set.range fun j => Lp j τ) = ⊤ ∧ Submodule.span ℂ (Set.range fun j => Lm j τ) = ⊤) → ∃ (C : ℝ) (B : ℕ), ∀ᶠ w in imTop, 0 < X.nfac la (x w) ∧ (X.nfac la (x w))⁻¹ ≤ C * w.im ^ B := by
  first | exact @GlobalTheory.nfac_inv_le_pow_of_isOrbit | exact GlobalTheory.nfac_inv_le_pow_of_isOrbit | (intros; apply GlobalTheory.nfac_inv_le_pow_of_isOrbit <;> assumption)
end

