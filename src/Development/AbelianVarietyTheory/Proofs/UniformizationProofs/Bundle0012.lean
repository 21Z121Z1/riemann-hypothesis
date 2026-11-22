import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.OverHomEqIffForallIsAlgClosedAlgebra
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.OpensRangeChartYSupOpensRangeChartZ
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingStalkGeneric
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIsoOfIsClosedImmersionOfThickenings

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsNegOriginSmoothLocus
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory

namespace WeierstrassCurve

namespace SmoothNeg

open HomogeneousIdeal

attribute [local instance] MvPolynomial.gradedAlgebra

theorem equation_neg {A : Type*} [CommRing A] {V : WeierstrassCurve A} {P : Fin 3 → A}
    (h : V.toProjective.Equation P) : V.toProjective.Equation (V.toProjective.neg P) := by
  rw [WeierstrassCurve.Projective.equation_iff] at h ⊢
  simp only [WeierstrassCurve.Projective.neg, WeierstrassCurve.Projective.negY,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  linear_combination h

theorem span_le_span_neg {A : Type*} [CommRing A] (V : WeierstrassCurve A) (P : Fin 3 → A) :
    Ideal.span (Set.range P) ≤ Ideal.span (Set.range (V.toProjective.neg P)) := by
  have h0 : P 0 ∈ Ideal.span (Set.range (V.toProjective.neg P)) := Ideal.subset_span ⟨0, rfl⟩
  have h2 : P 2 ∈ Ideal.span (Set.range (V.toProjective.neg P)) := Ideal.subset_span ⟨2, rfl⟩
  have h1 : -P 1 - V.a₁ * P 0 - V.a₃ * P 2 ∈ Ideal.span (Set.range (V.toProjective.neg P)) :=
    Ideal.subset_span ⟨1, rfl⟩
  have h1' : P 1 ∈ Ideal.span (Set.range (V.toProjective.neg P)) := by
    have : P 1 = -((-P 1 - V.a₁ * P 0 - V.a₃ * P 2) + V.a₁ * P 0 + V.a₃ * P 2) := by ring
    rw [this]
    exact neg_mem (add_mem (add_mem h1 (Ideal.mul_mem_left _ _ h0)) (Ideal.mul_mem_left _ _ h2))
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  fin_cases i <;> assumption

theorem isUnimodularSol_neg {A : Type*} [CommRing A] {V : WeierstrassCurve A} {P : Fin 3 → A}
    (h : IsUnimodularSol V P) : IsUnimodularSol V (V.toProjective.neg P) :=
  ⟨equation_neg h.equation, top_le_iff.mp (h.span_eq_top.ge.trans (span_le_span_neg V P))⟩

variable {R : Type} [CommRing R] (W : WeierstrassCurve R)

def negCoord : Fin 3 → HomRing W := (W.map (algebraMap R (HomRing W))).toProjective.neg (coord W)

theorem negCoord_mem (i : Fin 3) : negCoord W i ∈ grading W 1 := by
  fin_cases i
  · exact coord_mem W 0
  · change -coord W 1 - algebraMap R _ W.a₁ * coord W 0 - algebraMap R _ W.a₃ * coord W 2 ∈ _
    rw [← Algebra.smul_def, ← Algebra.smul_def]
    exact sub_mem (sub_mem (neg_mem (coord_mem W 1)) (Submodule.smul_mem _ _ (coord_mem W 0)))
      (Submodule.smul_mem _ _ (coord_mem W 2))
  · exact coord_mem W 2

def negRingHom : HomRing W →+* HomRing W :=
  evalHom W (algebraMap R (HomRing W)) (negCoord W) (equation_neg (equation_coord W))

def negGraded : grading W →+*ᵍ grading W where
  toRingHom := negRingHom W
  map_mem := by
    rintro n _ ⟨p, hp, rfl⟩
    have hp' : p.IsHomogeneous n := hp
    change MvPolynomial.eval₂ (algebraMap R (HomRing W)) (negCoord W) p ∈ _
    rw [MvPolynomial.eval₂_eq]
    refine Submodule.sum_mem _ fun d hd => ?_
    rw [← Algebra.smul_def]
    refine Submodule.smul_mem _ _ ?_
    have := SetLike.prod_pow_mem_graded (grading W) (fun _ => 1) (negCoord W) (F := d.support) d
      (fun i _ => negCoord_mem W i)
    rw [hp'.degree_eq_sum_deg_support hd]
    simpa using this

theorem irrelevant_le_map_negGraded :
    irrelevant (grading W) ≤ (irrelevant (grading W)).map (negGraded W) := by
  rw [← toIdeal_le_toIdeal_iff, irrelevant_eq_span_coord]
  refine (span_le_span_neg (W.map (algebraMap R (HomRing W))) (coord W)).trans ?_
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  have : (W.map (algebraMap R (HomRing W))).toProjective.neg (coord W) i =
      negGraded W (coord W i) :=
    (evalHom_coord W (algebraMap R (HomRing W)) (negCoord W)
      (equation_neg (equation_coord W)) i).symm
  rw [this]
  exact Ideal.mem_map_of_mem (negGraded W) (mem_irrelevant_of_mem _ one_pos (coord_mem W i))

def negMap : scheme W ⟶ scheme W := Proj.map (negGraded W) (irrelevant_le_map_negGraded W)

@[reassoc]
theorem ptHom_negMap {A : Type} [CommRing A] (ρ : R →+* A) (P : Fin 3 → A)
    (hP : IsUnimodularSol (W.map ρ) P) :
    ptHom W ρ P hP ≫ negMap W = ptHom W ρ _ (isUnimodularSol_neg hP) := by
  refine (ProjPoint.ofHom_map (negGraded W) (irrelevant_le_map_negGraded W) _
    (map_irrelevant_evalHom W hP)).trans ?_
  have : (evalHom W ρ P hP.equation).comp (negGraded W).toRingHom =
      evalHom W ρ _ (isUnimodularSol_neg hP).equation := by
    refine homRing_hom_ext W (fun r => ?_) (fun i => ?_)
    · refine (congrArg (evalHom W ρ P hP.equation) (evalHom_algebraMap W _ (negCoord W)
        (equation_neg (equation_coord W)) r)).trans ?_
      rw [evalHom_algebraMap, evalHom_algebraMap]
    refine (congrArg (evalHom W ρ P hP.equation) (evalHom_coord W _ (negCoord W)
      (equation_neg (equation_coord W)) i)).trans ?_
    rw [evalHom_coord]
    fin_cases i
    · exact evalHom_coord W ρ P hP.equation 0
    · change evalHom W ρ P hP.equation
        (-coord W 1 - algebraMap R _ W.a₁ * coord W 0 - algebraMap R _ W.a₃ * coord W 2) =
        -P 1 - ρ W.a₁ * P 0 - ρ W.a₃ * P 2
      simp only [map_sub, map_neg, map_mul, evalHom_coord, evalHom_algebraMap]
    · exact evalHom_coord W ρ P hP.equation 2
  simp only [this]
  rfl

theorem negMap_toSpec : negMap W ≫ toSpec W = toSpec W := by
  apply scheme_hom_ext
  · rw [chartY, pt_eq_ptHom, ptHom_negMap_assoc, ptHom_toSpec, ptHom_toSpec]
  · rw [chartZ, pt_eq_ptHom, ptHom_negMap_assoc, ptHom_toSpec, ptHom_toSpec]

theorem range_subset_of_forall_field {T Y : Scheme.{0}} (f : T ⟶ Y) (U : Y.Opens)
    (h : ∀ (k : Type) [Field k] (x : Spec (.of k) ⟶ T), ⊤ ≤ (x ≫ f) ⁻¹ᵁ U) :
    Set.range f ⊆ Set.range U.ι := by
  rintro _ ⟨t, rfl⟩
  have := h (T.residueField t) (T.fromSpecResidueField t)
    (Set.mem_univ (IsLocalRing.closedPoint (T.residueField t)))
  rw [Scheme.Opens.range_ι]
  have e : (T.fromSpecResidueField t ≫ f) (IsLocalRing.closedPoint (T.residueField t)) = f t :=
    (Scheme.Hom.comp_apply _ _ _).trans (congrArg f (Scheme.fromSpecResidueField_apply t _))
  rw [← e]
  exact this

end SmoothNeg

open SmoothNeg in

theorem exists_neg_origin_smoothLocus :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (W : WeierstrassCurve R) (U : (GlobalTheory.WeierstrassCurve.scheme W).Opens), (∀ (k : Type) [Field k] (ρ : R →+* k) (P : Fin 3 → k) (h : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) P), ⊤ ≤ GlobalTheory.WeierstrassCurve.ptHom W ρ P h ⁻¹ᵁ U ↔ (W.map ρ).toProjective.Nonsingular P) → ∃ (neg : (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W)) ⟶ (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W))) (o : 𝟙_ _ ⟶ (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W))), o.left ≫ U.ι = GlobalTheory.WeierstrassCurve.zero W ∧ ∀ (k : Type) [Field k] (ρ : R →+* k) (x : Over.mk (Spec.map (CommRingCat.ofHom ρ)) ⟶ (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W))) (P : Fin 3 → k) (hP : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) P), x.left ≫ U.ι = GlobalTheory.WeierstrassCurve.ptHom W ρ P hP → ∃ h : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) ((W.map ρ).toProjective.neg P), (x ≫ neg).left ≫ U.ι = GlobalTheory.WeierstrassCurve.ptHom W ρ _ h := by
  intro R _ _ _ W U hU
  have hneg : Set.range (U.ι ≫ negMap W) ⊆ Set.range U.ι := by
    refine range_subset_of_forall_field _ U fun k _ x => ?_
    obtain ⟨ρ, hρ⟩ := Spec.map_surjective (x ≫ U.ι ≫ toSpec W)
    obtain ⟨P, hP, e⟩ := exists_eq_ptHom W ρ.hom (x ≫ U.ι) (by simpa using hρ.symm)
    have hns : (W.map ρ.hom).toProjective.Nonsingular P := by
      rw [← hU k ρ.hom P hP, ← e]
      intro y _
      simp
    rw [← Category.assoc, e, ptHom_negMap, hU]
    exact WeierstrassCurve.Projective.nonsingular_neg hns
  have hzero : Set.range (zero W) ⊆ Set.range U.ι := by
    refine range_subset_of_forall_field _ U fun k _ x => ?_
    obtain ⟨ρ, rfl⟩ := Spec.map_surjective x
    have := SpecMap_zero W ρ.hom
    rw [CommRingCat.ofHom_hom] at this
    rw [this, hU]
    exact WeierstrassCurve.Projective.nonsingular_zero
  refine ⟨Over.homMk (IsOpenImmersion.lift U.ι (U.ι ≫ negMap W) hneg) ?_,
    Over.homMk (IsOpenImmersion.lift U.ι (zero W) hzero) ?_, ?_, ?_⟩
  · change IsOpenImmersion.lift U.ι (U.ι ≫ negMap W) hneg ≫ U.ι ≫ toSpec W = U.ι ≫ toSpec W
    rw [IsOpenImmersion.lift_fac_assoc, Category.assoc, negMap_toSpec]
  · change IsOpenImmersion.lift U.ι (zero W) hzero ≫ U.ι ≫ toSpec W = 𝟙 _
    rw [IsOpenImmersion.lift_fac_assoc, zero_toSpec]
  · exact IsOpenImmersion.lift_fac _ _ _
  · intro k _ ρ x P hP e
    refine ⟨isUnimodularSol_neg hP, ?_⟩
    change (x.left ≫ IsOpenImmersion.lift U.ι (U.ι ≫ negMap W) hneg) ≫ U.ι = _
    rw [Category.assoc, IsOpenImmersion.lift_fac, ← ptHom_negMap W ρ P hP, ← e]
    exact (Category.assoc _ _ _).symm

end WeierstrassCurve

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsRankOneBundle
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RankBundle

variable {X : Scheme.{0}}

theorem gs_one (x : X) (U : X.Opens) (h : x ∈ U) : gs (𝟙 X) x U 1 = 1 := by
  rw [gs_eq (𝟙 X) x U h, map_one, map_one]

theorem mem_basicOpen_iff (x : X) (U : X.Opens) (h : x ∈ U) (a : Γ(X, U)) :
    x ∈ X.basicOpen a ↔ IsUnit (gs (𝟙 X) x U a) := by
  rw [gs_eq (𝟙 X) x U h]
  exact X.mem_basicOpen a x h

theorem sec_compat {N : LB X} (s : LB.Sec N) (x : X) {k k' : N.ι} (hk : x ∈ N.U k) (hk' : x ∈ N.U k') :
    gs (𝟙 X) x (N.U k) (s.f k) = (gm (𝟙 X) x (N.U k ⊓ N.U k') (N.g k k')).val * gs (𝟙 X) x (N.U k') (s.f k') := by
  have hm : x ∈ N.U k ⊓ N.U k' := ⟨hk, hk'⟩
  exact (gs_res (𝟙 X) x _ hm _).symm.trans ((congrArg (gs (𝟙 X) x _) (s.compat k k')).trans
    ((gs_mul (𝟙 X) x _ hm _ _).trans (congrArg₂ (· * ·) (gs_unit (𝟙 X) x _ hm _) (gs_res (𝟙 X) x _ hm _))))

theorem exists_ratio {U : X.Opens} (a b : Γ(X, U)) : ∃ r : Γ(X, X.basicOpen b), ∀ x ∈ X.basicOpen b,
    gs (𝟙 X) x (X.basicOpen b) r * gs (𝟙 X) x U b = gs (𝟙 X) x U a := by
  obtain ⟨u, hu⟩ : IsUnit ((X.presheaf.map (homOfLE (X.basicOpen_le b)).op).hom b) :=
    X.toRingedSpace.isUnit_res_basicOpen b
  refine ⟨(X.presheaf.map (homOfLE (X.basicOpen_le b)).op).hom a * (u⁻¹).val, fun x hx => ?_⟩
  rw [← gs_res (𝟙 X) x (X.basicOpen_le b) hx b, ← gs_res (𝟙 X) x (X.basicOpen_le b) hx a,
    ← gs_mul (𝟙 X) x _ hx, ← hu, _root_.mul_assoc, Units.inv_mul, _root_.mul_one]

theorem exists_rank_one_bundle : ∀ (X : Scheme.{0}) (N : LB X) (n m : ℕ) (w : Fin (n + 1) → Fin (m + 1) → LB.Sec N), N.IsLB → (⨆ i, ⨆ j, nonzeroLocus (w i j) = ⊤) → (∀ i i' j j' k, (w i j).f k * (w i' j').f k = (w i j').f k * (w i' j).f k) → ∃ (H' : LB X) (s' : Fin (n + 1) → LB.Sec H'), H'.IsLB ∧ (⨆ i, nonzeroLocus (s' i) = ⊤) ∧ ∀ (x : X) (c : H'.ι), x ∈ H'.U c → ∃ j, ∀ k, x ∈ N.U k → ∃ v : (X.presheaf.stalk x)ˣ, ∀ i, gs (𝟙 X) x (N.U k) ((w i j).f k) = v.val * gs (𝟙 X) x (H'.U c) ((s' i).f c) := by
  intro X N n m w hN hcov hr
  choose S hS using fun (l : Fin (n + 1)) (c : Fin (n + 1) × Fin (m + 1) × N.ι) =>
    exists_ratio ((w l c.2.1).f c.2.2) ((w c.1 c.2.1).f c.2.2)
  let U : Fin (n + 1) × Fin (m + 1) × N.ι → X.Opens := fun c => X.basicOpen ((w c.1 c.2.1).f c.2.2)
  have hle : ∀ c x, x ∈ U c → x ∈ N.U c.2.2 := fun c x hx => X.basicOpen_le _ hx
  have hu : ∀ c x, x ∈ U c → IsUnit (gs (𝟙 X) x (N.U c.2.2) ((w c.1 c.2.1).f c.2.2)) := fun c x hx =>
    (mem_basicOpen_iff x _ (hle c x hx) _).1 hx
  have one : ∀ c x, x ∈ U c → gs (𝟙 X) x (U c) (S c.1 c) = 1 := fun c x hx =>
    (hu c x hx).mul_right_cancel ((hS c.1 c x hx).trans (_root_.one_mul _).symm)
  have key : ∀ l c c' x, x ∈ U c → x ∈ U c' →
      gs (𝟙 X) x (U c) (S l c) = gs (𝟙 X) x (U c) (S c'.1 c) * gs (𝟙 X) x (U c') (S l c') := by
    intro l c c' x hx hx'
    have e₁ := hS l c x hx
    have e₂ := hS c'.1 c x hx
    have e₃ := hS l c' x hx'
    have e₄ := congrArg (gs (𝟙 X) x (N.U c.2.2)) (hr l c'.1 c.2.1 c'.2.1 c.2.2)
    rw [gs_mul (𝟙 X) x _ (hle c x hx), gs_mul (𝟙 X) x _ (hle c x hx),
      sec_compat (w c'.1 c'.2.1) x (hle c x hx) (hle c' x hx'),
      sec_compat (w l c'.2.1) x (hle c x hx) (hle c' x hx')] at e₄
    apply (((hu c x hx).mul (hu c' x hx')).mul
      (gm (𝟙 X) x (N.U c.2.2 ⊓ N.U c'.2.2) (N.g c.2.2 c'.2.2)).isUnit).mul_right_cancel
    rw [← e₁, ← e₂, ← e₃] at e₄
    exact Eq.trans (by ring) (e₄.trans (by ring))
  have hg : ∀ c c', IsUnit (rs X (inf_le_left : U c ⊓ U c' ≤ U c) (S c'.1 c)) := fun c c' =>
    IsUnit.of_mul_eq_one (rs X (inf_le_right : U c ⊓ U c' ≤ U c') (S c.1 c')) (fn_ext fun x hx => by
      rw [gs_mul (𝟙 X) x _ hx, gs_res (𝟙 X) x _ hx, gs_res (𝟙 X) x _ hx, ← key c.1 c c' x hx.1 hx.2,
        one c x hx.1, gs_one x _ hx])
  have gv : ∀ c c' x, x ∈ U c ⊓ U c' →
      (gm (𝟙 X) x (U c ⊓ U c') (hg c c').unit).val = gs (𝟙 X) x (U c) (S c'.1 c) := fun c c' x hx =>
    (gs_unit (𝟙 X) x _ hx _).symm.trans (gs_res (𝟙 X) x _ hx _)
  have ex : ∀ x : X, ∃ c, x ∈ U c := fun x => by
    have hx : x ∈ ⨆ i, ⨆ j, nonzeroLocus (w i j) := by rw [hcov]; trivial
    obtain ⟨i, hx⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    obtain ⟨j, hx⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    obtain ⟨k, hx⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    exact ⟨(i, j, k), hx⟩
  let H : LB X := ⟨Fin (n + 1) × Fin (m + 1) × N.ι, U, fun c c' => (hg c c').unit⟩
  let s : Fin (n + 1) → LB.Sec H := fun l => ⟨S l, fun c c' => fn_ext fun x hx =>
    (gs_res (𝟙 X) x _ hx _).trans ((key l c c' x hx.1 hx.2).trans ((gs_mul (𝟙 X) x _ hx _ _).trans
      (congrArg₂ (· * ·) (gs_res (𝟙 X) x _ hx _) (gs_res (𝟙 X) x _ hx _))).symm)⟩
  refine ⟨H, s, ⟨?_, fun c => unit_ext fun x hx => Units.ext ?_, fun a b c => unit_ext fun x hx => Units.ext ?_⟩, ?_, ?_⟩
  · exact top_unique fun x _ => TopologicalSpace.Opens.mem_iSup.2 (ex x)
  · rw [gm_res (𝟙 X) x _ hx, map_one, Units.val_one]
    exact (gv c c x ⟨hx, hx⟩).trans (one c x hx)
  · rw [map_mul, gm_res (𝟙 X) x _ hx, gm_res (𝟙 X) x _ hx, gm_res (𝟙 X) x _ hx, Units.val_mul]
    exact (congrArg₂ (· * ·) (gv a b x hx.1) (gv b c x ⟨hx.1.2, hx.2⟩)).trans
      ((key c.1 a b x hx.1.1 hx.1.2).symm.trans (gv a c x ⟨hx.1.1, hx.2⟩).symm)
  · refine top_unique fun x _ => ?_
    obtain ⟨c, hc⟩ := ex x
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨c.1, TopologicalSpace.Opens.mem_iSup.2 ⟨c, ?_⟩⟩
    exact (mem_basicOpen_iff x (U c) hc _).2 ((one c x hc).symm ▸ isUnit_one)
  · intro x c hc
    refine ⟨c.2.1, fun k hk => ⟨gm (𝟙 X) x (N.U k ⊓ N.U c.2.2) (N.g k c.2.2) * (hu c x hc).unit, fun l => ?_⟩⟩
    rw [sec_compat (w l c.2.1) x hk (hle c x hc), ← hS l c x hc, Units.val_mul, IsUnit.unit_spec, _root_.mul_assoc]
    exact congrArg _ (_root_.mul_comm _ _)

end GlobalTheory.RankBundle
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecGeneratesSpecialFibre
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory

namespace SpecialFibreGenerator

open TopologicalSpace Opposite

variable {X Y : Scheme.{0}}

theorem mem_basicOpen_of_chart {L : LB X} (s : L.Sec) {a b : L.ι} {x : X} (ha : x ∈ L.U a)
    (hb : x ∈ X.basicOpen (s.f b)) : x ∈ X.basicOpen (s.f a) := by
  have h := congrArg X.basicOpen (s.compat a b)
  rw [Scheme.basicOpen_mul, X.basicOpen_of_isUnit (Units.isUnit _)] at h
  have h₁ := X.basicOpen_res (s.f a) (homOfLE (inf_le_left : L.U a ⊓ L.U b ≤ L.U a)).op
  have h₂ := X.basicOpen_res (s.f b) (homOfLE (inf_le_right : L.U a ⊓ L.U b ≤ L.U b)).op
  have hab : x ∈ L.U a ⊓ L.U b := ⟨ha, X.basicOpen_le _ hb⟩
  exact (h₁.le (h.ge ⟨hab, h₂.ge ⟨hab, hb⟩⟩)).2

noncomputable def secAlong {L : LB X} (s : L.Sec) (φ : Y ⟶ X) :
    (LB.LinComb L (K := Fin 1) (fun _ ↦ φ) fun _ ↦ ((1 : ℕ) : ℤ)).Sec where
  f a := φ.appLE (L.U (a 0)) (LB.wchart L (fun _ ↦ φ) a) (LB.wchart_le L (fun _ ↦ φ) a 0) (s.f (a 0))
  compat a b := by
    have hle : LB.wchart L (fun _ : Fin 1 ↦ φ) a ⊓ LB.wchart L (fun _ : Fin 1 ↦ φ) b ≤
        φ ⁻¹ᵁ (L.U (a 0) ⊓ L.U (b 0)) :=
      inf_le_inf (LB.wchart_le L (fun _ ↦ φ) a 0) (LB.wchart_le L (fun _ ↦ φ) b 0)
    have h := congrArg (φ.appLE (L.U (a 0) ⊓ L.U (b 0)) _ hle) (s.compat (a 0) (b 0))
    rw [map_mul] at h
    have hg : ((LB.LinComb L (K := Fin 1) (fun _ ↦ φ) fun _ ↦ ((1 : ℕ) : ℤ)).g a b).val =
        φ.appLE (L.U (a 0) ⊓ L.U (b 0)) _ hle (L.g (a 0) (b 0)).val := by
      simp only [LB.LinComb, Fin.prod_univ_one, Nat.cast_one, zpow_one]
      rfl
    rw [hg]
    refine ((PrimeSection.res_appLE φ _ _ _).trans (PrimeSection.appLE_res φ _ _ _).symm).trans
      (h.trans (congrArg (_ * ·) ?_))
    exact (PrimeSection.appLE_res φ _ _ _).trans (PrimeSection.res_appLE φ _ _ _).symm

theorem mem_nonzeroLocus_secAlong {L : LB X} (s : L.Sec) (φ : Y ⟶ X) {y : Y} {a : L.ι}
    (h : φ y ∈ X.basicOpen (s.f a)) : y ∈ nonzeroLocus (secAlong s φ) := by
  refine Opens.mem_iSup.2 ⟨fun _ ↦ a, ?_⟩
  change y ∈ Y.basicOpen (φ.appLE _ _ _ _)
  rw [Scheme.basicOpen_appLE]
  exact ⟨Set.mem_iInter.2 fun _ ↦ X.basicOpen_le _ h, h⟩

theorem mem_basicOpen_of_isClosed [AlgebraicGeometry.IsIntegral X] {t : Γ(X, ⊤)} {ξ : X}
    (hξ : ∀ x : X, x ∉ X.basicOpen t ↔ ξ ⤳ x)
    (hp : ∀ U : X.Opens, IsAffineOpen U → ξ ∈ U →
      Prime (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t))
    {L : LB X} (s : L.Sec) {b : L.ι} (hb : ξ ∈ X.basicOpen (s.f b)) {Z : Set X} (hZ : IsClosed Z)
    (hZt : Z ⊆ X.basicOpen t)
    (hs : ∀ y ∈ X.basicOpen t, y ∉ Z → ∃ c, y ∈ X.basicOpen (s.f c))
    {x : X} (hx : x ∉ X.basicOpen t) {a : L.ι} (ha : x ∈ L.U a) : x ∈ X.basicOpen (s.f a) := by
  obtain ⟨W, hW, hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset
    (U := L.U a ⊓ ⟨Zᶜ, hZ.isOpen_compl⟩) (x := x) ⟨ha, fun h ↦ hx (hZt h)⟩
  have hWa : W ≤ L.U a := fun y hy ↦ (hWU hy).1
  have hξW : ξ ∈ W := ((hξ x).1 hx).mem_open W.isOpen hxW
  have : Nonempty W := ⟨⟨x, hxW⟩⟩
  have hpr := hp W hW hξW
  set p := X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op t with hpd
  set σ := X.presheaf.map (homOfLE hWa).op (s.f a) with hσd
  have hpb : X.basicOpen p = W ⊓ X.basicOpen t := X.basicOpen_res _ _
  have hσb : X.basicOpen σ = W ⊓ X.basicOpen (s.f a) := X.basicOpen_res _ _
  have hle : X.basicOpen p ≤ X.basicOpen σ := fun y hy ↦ by
    obtain ⟨h₁, h₂⟩ := hpb.le hy
    obtain ⟨c, hc⟩ := hs y h₂ (hWU h₁).2
    exact hσb.ge ⟨h₁, mem_basicOpen_of_chart s (hWa h₁) hc⟩
  have hrad : p ∈ (Ideal.span {σ}).radical := by
    rw [← PrimeSpectrum.basicOpen_le_basicOpen_iff]
    have := hW.fromSpec.preimage_mono hle
    rwa [hW.fromSpec_preimage_basicOpen, hW.fromSpec_preimage_basicOpen] at this
  obtain ⟨m, hm⟩ := hrad
  obtain ⟨i, -, hi⟩ := (dvd_prime_pow hpr m).1 (Ideal.mem_span_singleton.1 hm)
  obtain rfl | hi0 := eq_or_ne i 0
  · have hu : IsUnit σ := associated_one_iff_isUnit.1 (by simpa using hi)
    exact (hσb.le ((X.basicOpen_of_isUnit hu).ge hxW)).2
  · obtain ⟨q, hq⟩ := (dvd_pow_self p hi0).trans hi.symm.dvd
    have h₁ : ξ ∈ X.basicOpen σ := hσb.ge ⟨hξW, mem_basicOpen_of_chart s (hWa hξW) hb⟩
    rw [hq, Scheme.basicOpen_mul] at h₁
    exact absurd (hpb.le h₁.1).2 ((hξ ξ).2 specializes_rfl)

end SpecialFibreGenerator

open SpecialFibreGenerator TopologicalSpace in

theorem exists_sec_generates_specialFibre : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (N : LB G.left), N.IsLB → ∀ s : LB.Sec (N.pull (pullback.fst G.hom (jK V))), (∃ a, a ∈ nonzeroLocus s) → IsClosed ((pullback.fst G.hom (jK V)) '' {a | a ∉ nonzeroLocus s}) → ∃ θ : H0 N 1, ∀ x : G.left, G.hom x = IsLocalRing.closedPoint V → x ∈ nonzeroLocus θ := by
  intro V _ _ _ G _ _ hG N hN s ⟨a₀, ha₀⟩ hZ
  have := hG.smooth
  have := hG.geomConnected
  have := grpObj_geometricallyIntegral_of_smooth _ G
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hK := IsPullback.of_hasPullback G.hom (jK V)
  have hs := IsPullback.of_hasPullback G.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue V)))
  have := DvrModel.isIntegral_of_geometricallyIntegral hK
  have := DvrModel.isIntegral_of_geometricallyIntegral hs
  have := DvrModel.isOpenImmersion_generic hK
  have := DvrModel.isIntegral hK
  obtain ⟨n, ⟨σ, hσ, b, x₀, hx₀, hb⟩, -⟩ := DvrModel.existsUnique_zpow_mul_sec hK hs hϖ hN s (by
    obtain ⟨k, hk⟩ := Opens.mem_iSup.1 ha₀
    exact ⟨k, fun h ↦ by rw [h, Scheme.basicOpen_zero] at hk; exact hk⟩)
  have hξ := DvrModel.notMem_basicOpen_iff_specializes hϖ hs
  have hr := DvrModel.opensRange_generic hϖ hK
  refine ⟨secAlong σ (𝟙 _), fun x hx ↦ ?_⟩
  obtain ⟨a, ha⟩ := LB.mem_of_cover hN x
  refine mem_nonzeroLocus_secAlong σ (𝟙 _) (a := a) ?_
  refine mem_basicOpen_of_isClosed hξ (DvrModel.prime_res_generic hϖ hs) σ (b := b)
    (((hξ x₀).1 ((DvrModel.notMem_basicOpen_iff _ hϖ x₀).2 hx₀)).mem_open
      (Scheme.basicOpen _ _).isOpen hb) hZ ?_ (fun y hy hyZ ↦ ?_)
    ((DvrModel.notMem_basicOpen_iff _ hϖ x).2 hx) ha
  · rintro _ ⟨y, -, rfl⟩
    exact hr.le ⟨y, rfl⟩
  · obtain ⟨z, rfl⟩ := hr.ge hy
    have hz : z ∈ nonzeroLocus s := by_contra fun h ↦ hyZ ⟨z, h, rfl⟩
    obtain ⟨k, hk⟩ := Opens.mem_iSup.1 hz
    refine ⟨k ⟨⟩, ?_⟩
    have h0 : algebraMap V (FractionRing V) ϖ ^ n ≠ 0 :=
      zpow_ne_zero _ ((map_ne_zero_iff _ (IsFractionRing.injective V _)).2 hϖ.ne_zero)
    have h := congrArg (Scheme.basicOpen _) (hσ k)
    rw [Scheme.basicOpen_mul, Scheme.basicOpen_appLE,
      Scheme.basicOpen_of_isUnit _ (((h0.isUnit.map _).map _).map _)] at h
    exact (h.ge ⟨Scheme.basicOpen_le _ _ hk, hk⟩).2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsIsoOfIsClosedImmersion
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IsoLimit

open ThickeningClosed

theorem isIso_of_isClosedImmersion {V : Type} [CommRing V] [IsLocalRing V] [IsNoetherianRing V]
    {X Z : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of V)) [IsProper f] (j : Z ⟶ X)
    [IsClosedImmersion j]
    (h : ∀ n : ℕ, ∃ l : pullback f (thick V (IsLocalRing.maximalIdeal V) n) ⟶ Z,
      l ≫ j = pullback.fst f (thick V (IsLocalRing.maximalIdeal V) n)) : IsIso j := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have key : ∀ x, x ∈ zeroLocusOpen j.ker := by
    intro x
    by_contra hx
    have hc : IsClosed (f '' (zeroLocusOpen j.ker)ᶜ) :=
      f.isClosedMap _ (isOpen_zeroLocusOpen _).isClosed_compl
    obtain ⟨y, hy, hy'⟩ :=
      (IsLocalRing.specializes_closedPoint (R := V) (f x)).mem_closed hc ⟨x, hx, rfl⟩
    refine hy (mem_of_thickenings _ f j h y ?_)
    rw [hy']
    exact le_rfl
  rw [IsClosedImmersion.isIso_iff_ker_eq_bot]
  refine le_bot_iff.1 fun U a ha ↦ ?_
  change a = 0
  refine eq_zero_of_localization a fun J hJ ↦ ?_
  obtain ⟨s, hs, hsa⟩ := exists_mul_eq_zero_of_mem j.ker U ⟨J, hJ.isPrime⟩ (key _) ha
  exact (IsLocalization.map_eq_zero_iff J.primeCompl _ a).2 ⟨⟨s, hs⟩, hsa⟩

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsNoetherianRing V] (Γ₁ Y : Over (Spec (CommRingCat.of V))) (p : Γ₁ ⟶ Y) [IsProper Y.hom] [IsProper p.left], (∀ e, IsIso ((Over.pullback (thick V (IsLocalRing.maximalIdeal V) e)).map p)) → IsIso p := by
  intro V _ _ _ _ Γ₁ Y p _ _ h
  have hw : p.left ≫ Y.hom = Γ₁.hom := Over.w p
  let q (e : ℕ) : pullback Γ₁.hom (thick V (IsLocalRing.maximalIdeal V) e) ⟶
      pullback Y.hom (thick V (IsLocalRing.maximalIdeal V) e) :=
    ((Over.pullback (thick V (IsLocalRing.maximalIdeal V) e)).map p).left
  have hq (e : ℕ) : IsIso (q e) := by
    haveI := h e
    exact inferInstanceAs (IsIso ((Over.forget _).map
      ((Over.pullback (thick V (IsLocalRing.maximalIdeal V) e)).map p)))
  have q1 (e : ℕ) : q e ≫ pullback.fst _ _ = pullback.fst _ _ ≫ p.left := pullback.lift_fst _ _ _
  have q2 (e : ℕ) : q e ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
  have hd : IsIso (pullback.diagonal p.left) := by
    refine isIso_of_isClosedImmersion (pullback.fst p.left p.left ≫ p.left ≫ Y.hom) _ fun n ↦ ?_
    have c := pullback.condition (f := pullback.fst p.left p.left ≫ p.left ≫ Y.hom)
      (g := thick V (IsLocalRing.maximalIdeal V) n)
    have c' := pullback.condition (f := p.left) (g := p.left)
    set u := pullback.fst (pullback.fst p.left p.left ≫ p.left ≫ Y.hom)
      (thick V (IsLocalRing.maximalIdeal V) n)
    set v := pullback.snd (pullback.fst p.left p.left ≫ p.left ≫ Y.hom)
      (thick V (IsLocalRing.maximalIdeal V) n)
    have e : pullback.lift (f := Γ₁.hom) (u ≫ pullback.fst _ _) v
          (by rw [← c, ← hw, Category.assoc]) =
        pullback.lift (f := Γ₁.hom) (u ≫ pullback.snd _ _) v
          (by rw [← c, ← hw, Category.assoc, ← reassoc_of% c']) := by
      haveI := hq n
      rw [← cancel_mono (q n)]
      apply pullback.hom_ext
      · simp only [Category.assoc, q1, pullback.lift_fst_assoc, c']
      · simp only [Category.assoc, q2, pullback.lift_snd]
    have e' := congrArg (· ≫ pullback.fst _ _) e
    simp only [pullback.lift_fst] at e'
    refine ⟨u ≫ pullback.fst _ _, ?_⟩
    apply pullback.hom_ext
    · simp
    · simp [e']
  have hm : Mono p.left := (pullback.isIso_diagonal_iff p.left).1 hd
  have hc : IsClosedImmersion p.left :=
    (IsClosedImmersion.iff_isProper_and_mono p.left).2 ⟨‹_›, hm⟩
  have hi : IsIso p.left := by
    refine isIso_of_isClosedImmersion Y.hom _ fun n ↦ ?_
    haveI := hq n
    exact ⟨inv (q n) ≫ pullback.fst _ _, by rw [Category.assoc, ← q1, IsIso.inv_hom_id_assoc]⟩
  have : IsIso ((Over.forget _).map p) := hi
  exact isIso_of_reflects_iso p (Over.forget _)

end GlobalTheory.IsoLimit
end

