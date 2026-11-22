import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1425
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLocalFieldDataExists
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1793
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1057
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedFiniteMapsRestriction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1101
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2359
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2170
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2317
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreActionTrivialOfFixedPointResidueField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpObjPullG

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorSectionsEmbedFunctionFieldRegular
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
open TensorProduct

namespace GlobalTheory.Desc.BCChart

def ev {T : Scheme.{0}} {K : Type} [CommRing K] (f : Sp K ⟶ T) (O : T.Opens) (h : ⊤ ≤ f ⁻¹ᵁ O) (u : Γ(T, O)) : K :=
  (Scheme.ΓSpecIso (CommRingCat.of K)).hom ((f.appLE O ⊤ h).hom u)

theorem ev_comp {T T' : Scheme.{0}} {K : Type} [CommRing K] (s : Sp K ⟶ T') (g : T' ⟶ T) {O : T.Opens}
    {O' : T'.Opens} (e : O' ≤ g ⁻¹ᵁ O) (h : ⊤ ≤ s ⁻¹ᵁ O') {g' : Sp K ⟶ T} (hg : s ≫ g = g')
    (h' : ⊤ ≤ g' ⁻¹ᵁ O) (u : Γ(T, O)) : ev g' O h' u = ev s O' h ((g.appLE O O' e).hom u) := by
  subst hg
  unfold ev
  congr 1
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]

theorem appLE_top_top {A B : Scheme.{0}} (f : A ⟶ B) : f.appLE ⊤ ⊤ le_top = f.appTop := by
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  congr 1

theorem ev_spMap {T : Scheme.{0}} {A B : Type} [CommRing A] [CommRing B] (θ : A →+* B) (f : Sp A ⟶ T)
    (O : T.Opens) (h : ⊤ ≤ f ⁻¹ᵁ O) (h' : ⊤ ≤ (spMap θ ≫ f) ⁻¹ᵁ O) (u : Γ(T, O)) :
    ev (spMap θ ≫ f) O h' u = θ (ev f O h u) := by
  rw [ev_comp (spMap θ) f h le_top rfl]
  unfold ev
  rw [appLE_top_top, ← CommRingCat.comp_apply, Scheme.ΓSpecIso_naturality]
  rfl

theorem fromSpecStalk_top' {X : Scheme.{0}} (x : X) (U : X.Opens) (hx : x ∈ U) :
    ⊤ ≤ X.fromSpecStalk x ⁻¹ᵁ U := by
  intro z _
  have hz : X.fromSpecStalk x z ⤳ x := by
    have : X.fromSpecStalk x z ∈ Set.range (X.fromSpecStalk x) := ⟨z, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  exact hz.mem_open U.2 hx

theorem fromSpecStalk_appLE' {X : Scheme.{0}} (x : X) (U : X.Opens) (hx : x ∈ U) :
    (X.fromSpecStalk x).appLE U ⊤ (fromSpecStalk_top' x U hx) =
      X.presheaf.germ U x hx ≫ (Scheme.ΓSpecIso (X.presheaf.stalk x)).inv := by
  rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hx]
  simp only [Category.assoc, ← Functor.map_comp]
  have e : ((homOfLE le_top).op ≫ (homOfLE (fromSpecStalk_top' x U hx)).op :
      Opposite.op (⊤ : (Spec (X.presheaf.stalk x)).Opens) ⟶ Opposite.op ⊤) = 𝟙 _ := rfl
  rw [e, CategoryTheory.Functor.map_id, Category.comp_id]

theorem fnOf_eq_ev {X : Scheme.{0}} [IsIntegral X] (O : X.Opens) (hO : genericPoint X ∈ O) (u : Γ(X, O)) :
    fnOf O hO u = ev (gp X) O (fromSpecStalk_top' _ O hO) u := by
  unfold ev gp
  rw [fromSpecStalk_appLE' (genericPoint X) O hO, CommRingCat.comp_apply]
  change _ = (Scheme.ΓSpecIso (X.presheaf.stalk (genericPoint X))).hom _
  rw [Iso.inv_hom_id_apply]
  rfl

theorem exists_tensor_fnOf : ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] (ρ : R →+* R₁) (X Y V : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp R) (q : Y ⟶ Sp R₁) (i : V ⟶ Y) [IsOpenImmersion i] (φ : V ⟶ X) (θ : X.functionField →+* Y.functionField), IsPullback φ (i ≫ q) p (spMap ρ) → PFF i φ θ → ∀ (U : X.Opens), IsAffineOpen U → ∀ hg : genericPoint X ∈ U, letI := (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U).toAlgebra; letI := ρ.toAlgebra; ∃ β : Γ(X, U) ⊗[R] R₁ →+ Y.functionField, Function.Injective β ∧ (∀ b r, β (b ⊗ₜ[R] r) = θ (GlobalTheory.Cartier.fnOf U hg b) * GlobalTheory.Desc.cst q r) ∧ Set.range β = {v | ∀ z : V, φ z ∈ U → GlobalTheory.Cartier.RegAt (i z) v} := by
  intro R R₁ _ _ ρ X Y V _ _ p q i _ φ θ H hP U hU hg
  letI := (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U).toAlgebra
  letI := ρ.toAlgebra
  obtain ⟨l, hl1, hl2⟩ := hP
  let W : V.Opens := φ ⁻¹ᵁ U ⊓ (i ≫ q) ⁻¹ᵁ ⊤
  let O : Y.Opens := i ''ᵁ W
  have hmemW : ∀ z : V, z ∈ W ↔ φ z ∈ U := fun z => ⟨fun h => h.1, fun h => ⟨h, trivial⟩⟩
  have hmemO : ∀ y : Y, y ∈ O ↔ ∃ z : V, φ z ∈ U ∧ i z = y := by
    intro y
    constructor
    · rintro ⟨z, hz, rfl⟩; exact ⟨z, hz.1, rfl⟩
    · rintro ⟨z, hz, rfl⟩; exact ⟨z, (hmemW z).2 hz, rfl⟩
  let pt : Sp Y.functionField := IsLocalRing.closedPoint Y.functionField
  have hz1 : i (l pt) = genericPoint Y := by
    rw [← Scheme.Hom.comp_apply, hl1]
    exact Scheme.fromSpecStalk_closedPoint
  have hz2 : φ (l pt) = genericPoint X := by
    rw [← Scheme.Hom.comp_apply, hl2, Scheme.Hom.comp_apply]
    exact Scheme.fromSpecStalk_closedPoint (x := genericPoint X) ▸ congrArg _ (Subsingleton.elim _ _)
  have hO : genericPoint Y ∈ O := (hmemO _).2 ⟨l pt, hz2 ▸ hg, hz1⟩
  let e := ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.eTens p (i ≫ q) φ H U hU
  let j : Γ(V, W) →+* Γ(Y, O) := (i.appIso W).inv.hom
  have hj : ∀ s, j ((i.appIso W).hom.hom s) = s := fun s => Iso.hom_inv_id_apply _ _
  have hj' : ∀ s, (i.appIso W).hom.hom (j s) = s := fun s => Iso.inv_hom_id_apply _ _
  refine ⟨((fnOf O hO).comp (j.comp e.toRingHom)).toAddMonoidHom, ?_, ?_, ?_⟩
  · intro a b hab
    have h1 := congrArg (i.appIso W).hom.hom (fnOf_injective O hO hab)
    simp only [RingHom.comp_apply, hj'] at h1
    exact e.injective h1
  · intro b r
    have hlW : ⊤ ≤ l ⁻¹ᵁ W := by
      intro z _
      have hz : z = pt := Subsingleton.elim _ _
      subst hz
      exact (hmemW _).2 (hz2 ▸ hg)
    have hC : ∀ y : Γ(V, W), fnOf O hO (j y) = ev l W hlW y := by
      intro y
      rw [fnOf_eq_ev]
      refine (ev_comp l i (O := O) (O' := W) (i.preimage_image_eq W).ge hlW hl1 _ _).trans ?_
      congr 1
      rw [← CommRingCat.comp_apply, Scheme.Hom.appIso_inv_appLE]
      have : (homOfLE (le_refl W)).op = 𝟙 (Opposite.op W) := rfl
      erw [this, CategoryTheory.Functor.map_id]
      rfl
    have hX : ⊤ ≤ (spMap θ ≫ gp X) ⁻¹ᵁ U := fun z _ => fromSpecStalk_top' (genericPoint X) U hg (Set.mem_univ (spMap θ z))
    have hYq : ⊤ ≤ (gp Y ≫ q) ⁻¹ᵁ ⊤ := fun _ _ => trivial
    show fnOf O hO (j (e (b ⊗ₜ[R] r))) = _
    rw [ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.eTens_tmul, map_mul, map_mul, hC, hC]
    congr 1
    · rw [← ev_comp l φ inf_le_left hlW hl2 hX, ev_spMap θ (gp X) U (fromSpecStalk_top' _ U hg), ← fnOf_eq_ev]
    · unfold ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX cst
      rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, fnOf_eq_ev ⊤ trivial, ← appLE_top_top,
        ← ev_comp l (i ≫ q) le_top hlW (by rw [← Category.assoc, hl1]) hYq,
        ← ev_comp (gp Y) q le_top (fromSpecStalk_top' _ ⊤ trivial) rfl hYq]
  · ext v
    simp only [Set.mem_range, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨t, rfl⟩ z hz
      exact regAt_fnOf ((hmemO _).2 ⟨z, hz, rfl⟩) hO _
    · intro hv
      obtain ⟨s, hs⟩ := exists_fnOf_eq hO fun y hy => by
        obtain ⟨z, hz, rfl⟩ := (hmemO y).1 hy
        exact hv z hz
      refine ⟨e.symm ((i.appIso W).hom.hom s), ?_⟩
      show fnOf O hO (j (e (e.symm ((i.appIso W).hom.hom s)))) = v
      rw [RingEquiv.apply_symm_apply, hj, hs]

end GlobalTheory.Desc.BCChart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnimodularFrameInertPlace
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.InertFrameUnimod

theorem selfDual_scaled : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {d : ℕ} (W : Spc F E d) (r s : ℕ), W.IsSkew σ B r s →
  ∀ {v : Pl F} {w : HeightOneSpectrum (𝓞 E)}, Formalism.UG.IsInertAt F E v w →
  ∃ t : F, t ≠ 0 ∧ GlobalTheory.AdelicU.IsSelfDualAt σ (algebraMap F E t • W.Jᵀ) W.L v := by
  intro F E _ _ _ _ _ σ B d W r s hW v w hw
  obtain ⟨t, ht0, s₁, s₂, h1, h2, c1, c2⟩ := GlobalTheory.T.exists_baseField_generator_localDifferent_inertPlace hw
  exact ⟨t, ht0, GlobalTheory.T.skewHermitianLattice_selfDual_smul_transpose_inert σ B W r s hW hw t ht0 s₁ s₂ h1 h2 c1 c2⟩

theorem isConjAt_conjW {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {v : Pl F} {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w) :
    IsConjAt σ (under_eq_of_isInertAt hw) (GlobalTheory.InertBigCell.conjW σ hw) := fun y =>
  congrArg (fun z => toCompl (under_eq_of_isInertAt hw) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ z))
    ((InertChart.complEquiv hw (under_eq_of_isInertAt hw)).symm_apply_apply y)

theorem exists_frame_unimod : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {d : ℕ} (W : Spc F E d) (r s : ℕ), B.IsGood σ → W.IsSkew σ B r s →
  ∀ {v : Pl F} {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w),
  ∃ (b : GL (Fin d) (w.adicCompletion E)) (δ : w.adicCompletion E),
    (∀ u, u ∈ GlobalTheory.LFun.latAt w W.L ↔ GlobalTheory.InertBigCell.InLat (w.adicCompletionIntegers E) b u) ∧
    GlobalTheory.InertBigCell.conjW σ hw δ = δ ∧
    (∀ i j, (δ • ((b : Matrix (Fin d) (Fin d) (w.adicCompletion E))ᵀ * W.J.map (algebraMap E (w.adicCompletion E)) *
      (b : Matrix (Fin d) (Fin d) (w.adicCompletion E)).map (GlobalTheory.InertBigCell.conjW σ hw))) i j ∈ w.adicCompletionIntegers E) ∧
    (δ • ((b : Matrix (Fin d) (Fin d) (w.adicCompletion E))ᵀ * W.J.map (algebraMap E (w.adicCompletion E)) *
      (b : Matrix (Fin d) (Fin d) (w.adicCompletion E)).map (GlobalTheory.InertBigCell.conjW σ hw))).det ≠ 0 ∧
    (δ • ((b : Matrix (Fin d) (Fin d) (w.adicCompletion E))ᵀ * W.J.map (algebraMap E (w.adicCompletion E)) *
      (b : Matrix (Fin d) (Fin d) (w.adicCompletion E)).map (GlobalTheory.InertBigCell.conjW σ hw))).det⁻¹ ∈ w.adicCompletionIntegers E := by
  intro F E _ _ _ _ _ σ B d W r s _hB hW v w hw
  have hc := isConjAt_conjW σ hw
  obtain ⟨t, ht0, hsd⟩ := selfDual_scaled σ B W r s hW hw
  haveI := hW.lat
  obtain ⟨a, ha⟩ := InertChart.exists_isFrameAt (L := W.L) hw Submodule.IsLattice.fg Submodule.IsLattice.span_eq_top
  have hdet : (algebraMap F E t • W.Jᵀ).det ≠ 0 := by
    rw [Matrix.det_smul, Matrix.det_transpose]
    exact mul_ne_zero (pow_ne_zero _ ((map_ne_zero _).2 ht0)) (GlobalTheory.FinUniq.det_ne_zero_skew hW)
  obtain ⟨B0, hB0, eB0⟩ := InertChart.exists_gram hw hc hdet hsd ha
  obtain ⟨C, hC⟩ := hB0
  set δ : w.adicCompletion E := algebraMap E (w.adicCompletion E) (algebraMap F E t) with hδdef
  have hδ : GlobalTheory.InertBigCell.conjW σ hw δ = δ := by
    rw [hδdef, InertChart.conj_algebraMap hc, AlgHom.commutes]
  have key : δ • ((a : Matrix (Fin d) (Fin d) (w.adicCompletion E))ᵀ * W.J.map (algebraMap E (w.adicCompletion E)) *
      (a : Matrix (Fin d) (Fin d) (w.adicCompletion E)).map (GlobalTheory.InertBigCell.conjW σ hw)) =
      (B0 : Matrix (Fin d) (Fin d) (w.adicCompletion E))ᵀ := by
    rw [eB0, Matrix.transpose_mul, Matrix.transpose_mul]
    have e1 : ((algebraMap F E t • W.Jᵀ).map (algebraMap E (w.adicCompletion E)))ᵀ =
        δ • W.J.map (algebraMap E (w.adicCompletion E)) := by
      ext i j
      simp only [hδdef, Matrix.map_apply, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
    have e2 : (Formalism.UG.cT (GlobalTheory.InertBigCell.conjW σ hw) (a : Matrix (Fin d) (Fin d) (w.adicCompletion E)))ᵀ =
        (a : Matrix (Fin d) (Fin d) (w.adicCompletion E)).map (GlobalTheory.InertBigCell.conjW σ hw) := by
      simp [Formalism.UG.cT]
    rw [e1, e2, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
  have hBC : (B0 : Matrix (Fin d) (Fin d) (w.adicCompletion E)) =
      (C : Matrix (Fin d) (Fin d) (Formalism.UG.Ov E w)).map (Formalism.UG.Ov E w).subtype := by
    rw [← hC]; rfl
  have hdetB : (B0 : Matrix (Fin d) (Fin d) (w.adicCompletion E)).det =
      (Formalism.UG.Ov E w).subtype (C : Matrix (Fin d) (Fin d) (Formalism.UG.Ov E w)).det := by
    rw [hBC, ← RingHom.mapMatrix_apply, RingHom.map_det]
  have hCu : IsUnit (C : Matrix (Fin d) (Fin d) (Formalism.UG.Ov E w)).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 C.isUnit
  refine ⟨a, δ, fun u => ?_, hδ, fun i j => ?_, ?_, ?_⟩
  · have h1 := ha ((a⁻¹ : GL (Fin d) (w.adicCompletion E)).1 *ᵥ u)
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec] at h1
    exact h1.symm
  · rw [key, Matrix.transpose_apply, hBC, Matrix.map_apply]
    exact (C.1 j i).2
  · rw [key, Matrix.det_transpose, hdetB]
    intro h0
    exact hCu.ne_zero (Subtype.ext h0)
  · rw [key, Matrix.det_transpose, hdetB]
    obtain ⟨u, hu⟩ := hCu
    have : (Formalism.UG.Ov E w).subtype (C : Matrix (Fin d) (Fin d) (Formalism.UG.Ov E w)).det *
        (Formalism.UG.Ov E w).subtype (u⁻¹ : (Formalism.UG.Ov E w)ˣ) = 1 := by
      rw [← map_mul, ← hu, Units.mul_inv, map_one]
    rw [inv_eq_of_mul_eq_one_right this]
    exact (u⁻¹ : (Formalism.UG.Ov E w)ˣ).1.2

end GlobalTheory.InertFrameUnimod
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueBaseChangeVolumeForm
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

namespace AltBaseChange

section General

variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
  {X W : Type} [AddCommGroup X] [Module R X] [AddCommGroup W] [Module R W] [Module R' W]
  [IsScalarTower R R' W] {j : X →ₗ[R] W} (hj : IsBaseChange R' j) (n : ℕ)

def bc (g : X [⋀^Fin n]→ₗ[R] R) : W [⋀^Fin n]→ₗ[R'] R' :=
  exteriorPower.alternatingMapLinearEquiv.symm
    ((TopForm.isBaseChange_exteriorPower hj n).toDual
      (exteriorPower.alternatingMapLinearEquiv g))

theorem bc_apply (g : X [⋀^Fin n]→ₗ[R] R) (v : Fin n → X) :
    bc hj n g (fun i => j (v i)) = algebraMap R R' (g v) := by
  unfold bc
  rw [← exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, LinearEquiv.apply_symm_apply,
    ← exteriorPowerMapOver_ιMulti (B := R'), IsBaseChange.toDual_comp_apply,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]

include hj in
theorem ext_tuples {ω₁ ω₂ : W [⋀^Fin n]→ₗ[R'] R'}
    (h : ∀ v : Fin n → X, ω₁ (fun i => j (v i)) = ω₂ (fun i => j (v i))) : ω₁ = ω₂ := by
  apply exteriorPower.alternatingMapLinearEquiv.injective
  apply (TopForm.isBaseChange_exteriorPower hj n).algHom_ext
  intro x
  have key : ((exteriorPower.alternatingMapLinearEquiv ω₁).restrictScalars R).comp
        (exteriorPowerMapOver R' n j) =
      ((exteriorPower.alternatingMapLinearEquiv ω₂).restrictScalars R).comp
        (exteriorPowerMapOver R' n j) := by
    apply exteriorPower.linearMap_ext
    ext v
    simp [h]
  exact LinearMap.congr_fun key x

theorem bc_smul (r : R) (g : X [⋀^Fin n]→ₗ[R] R) :
    bc hj n (r • g) = algebraMap R R' r • bc hj n g :=
  ext_tuples hj n fun v => by simp [bc_apply]

theorem mem_span_bc_of_free [Module.Free R X] [Module.Finite R X]
    (ω : W [⋀^Fin n]→ₗ[R'] R') : ω ∈ Submodule.span R' (Set.range (bc hj n)) := by
  obtain ⟨L, rfl⟩ := exteriorPower.alternatingMapLinearEquiv.symm.surjective ω
  have hD := (TopForm.isBaseChange_exteriorPower hj n).dual
  induction L using hD.inductionOn with
  | zero => simp
  | tmul m =>
    refine Submodule.subset_span ⟨exteriorPower.alternatingMapLinearEquiv.symm m, ?_⟩
    simp [bc]
  | smul s L h => rw [map_smul]; exact Submodule.smul_mem _ _ h
  | add a b ha hb => rw [map_add]; exact add_mem ha hb

end General

end AltBaseChange

end GlobalTheory

namespace GlobalTheory

namespace AltBaseChange

section Projective

variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
  {M : Type} [AddCommGroup M] [Module R M] (n : ℕ)

theorem exists_smul_bc_eq [Module.Finite R M] [Module.Projective R M]
    (δ : M [⋀^Fin n]→ₗ[R] R) (hδ : Submodule.span R {δ} = ⊤)
    (ω : (R' ⊗[R] M) [⋀^Fin n]→ₗ[R'] R') :
    ω ∈ Submodule.span R' {bc (TensorProduct.isBaseChange R M R') n δ} := by
  obtain ⟨k, f, hf⟩ := Module.Finite.exists_fin' R M
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  have hF := TensorProduct.isBaseChange R (Fin k → R) R'
  have hM := TensorProduct.isBaseChange R M R'
  have hfs (x : R' ⊗[R] M) : f.baseChange R' (s.baseChange R' x) = x := by
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hs, LinearMap.baseChange_id,
      LinearMap.id_apply]
  let Φ : ((R' ⊗[R] (Fin k → R)) [⋀^Fin n]→ₗ[R'] R') →ₗ[R'] ((R' ⊗[R] M) [⋀^Fin n]→ₗ[R'] R') :=
    { toFun := fun t => t.compLinearMap (s.baseChange R')
      map_add' := fun _ _ => by ext; simp
      map_smul' := fun _ _ => by ext; simp }
  have hω : Φ (ω.compLinearMap (f.baseChange R')) = ω := by
    ext v
    simp [Φ, hfs]
  have hη := mem_span_bc_of_free hF n (ω.compLinearMap (f.baseChange R'))
  rw [← hω]
  have hmap := Submodule.mem_map_of_mem (f := Φ) hη
  rw [Submodule.map_span] at hmap
  refine Submodule.span_le.mpr ?_ hmap
  rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
  have hg : g.compLinearMap s ∈ Submodule.span R {δ} := hδ ▸ Submodule.mem_top
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hg
  have : Φ (bc hF n g) = algebraMap R R' r • bc hM n δ := by
    rw [← bc_smul, hr]
    refine ext_tuples hM n fun v => ?_
    simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk, AlternatingMap.compLinearMap_apply]
    rw [bc_apply hM n]
    have h1 : (fun i => s.baseChange R' (TensorProduct.mk R R' M 1 (v i))) =
        fun i => TensorProduct.mk R R' (Fin k → R) 1 (s (v i)) := by
      funext i
      simp
    rw [h1, bc_apply hF n]
    rfl
  rw [SetLike.mem_coe, this]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

end Projective

end AltBaseChange

end GlobalTheory

namespace GlobalTheory

namespace AltBaseChange

theorem exists_unique_baseChange_generator : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (M : Type) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] (N : Type) [AddCommGroup N] [Module R' N] (e : R' ⊗[R] M ≃ₗ[R'] N)
    (n : ℕ) (δ : M [⋀^Fin n]→ₗ[R] R), Submodule.span R {δ} = ⊤ →
    ∃! δ' : N [⋀^Fin n]→ₗ[R'] R', Submodule.span R' {δ'} = ⊤ ∧
      ∀ v : Fin n → M, δ' (fun i ↦ e (1 ⊗ₜ v i)) = algebraMap R R' (δ v) := by
  intro R R' _ _ _ M _ _ _ _ N _ _ e n δ hδ
  have hM := TensorProduct.isBaseChange R M R'
  let δ' : N [⋀^Fin n]→ₗ[R'] R' := (bc hM n δ).compLinearMap e.symm.toLinearMap
  have hval (v : Fin n → M) : δ' (fun i ↦ e (1 ⊗ₜ v i)) = algebraMap R R' (δ v) := by
    simp only [δ', AlternatingMap.compLinearMap_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]
    exact bc_apply hM n δ v
  refine ⟨δ', ⟨?_, hval⟩, ?_⟩
  · rw [Submodule.eq_top_iff']
    intro ω
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp
      (exists_smul_bc_eq n δ hδ (ω.compLinearMap e.toLinearMap))
    refine Submodule.mem_span_singleton.mpr ⟨a, ?_⟩
    ext x
    have := congrArg (fun t => t (fun i => e.symm (x i))) ha
    simpa [δ'] using this
  · rintro y ⟨-, hy⟩
    have key : y.compLinearMap e.toLinearMap = bc hM n δ := by
      refine ext_tuples hM n fun v => ?_
      simp only [AlternatingMap.compLinearMap_apply, LinearEquiv.coe_coe]
      rw [bc_apply hM n]
      exact hy v
    ext x
    have := congrArg (fun t => t (fun i => e.symm (x i))) key
    simpa [δ'] using this

end AltBaseChange

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitBasicOpenOfCoboundaryIdentity
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LBDescent
open TensorProduct

namespace GlobalTheory.LBDescent

theorem coboundary_unit_basicOpen : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) (V V₀ : Y.Opens)
    (h : pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀ ≤ pullback.snd f f ⁻¹ᵁ f ⁻¹ᵁ V₀)
    (hle : pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀ ≤ pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V) (c : Γ(pullback f f, pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V)ˣ)
    (r : Γ(Y, V₀)) (m s : Γ(X, f ⁻¹ᵁ V₀)) (n : ℕ),
    ((pullback.fst f f).app (f ⁻¹ᵁ V₀)).hom m * (res hle c).val = ((pullback.snd f f).appLE (f ⁻¹ᵁ V₀) _ h).hom m →
    m * s = (f.app V₀).hom r ^ n →
    ∃ u : Γ(X, f ⁻¹ᵁ Y.basicOpen r)ˣ, ∀ z : ↥(pullback f f), f (pullback.fst f f z) ∈ Y.basicOpen r →
      gm (pullback.fst f f) z _ u * gm (𝟙 _) z _ c = gm (pullback.snd f f) z _ u := by
  intro X Y f V V₀ h hle c r m s n hm hs
  have hD : Y.basicOpen r ≤ V₀ := Y.basicOpen_le r
  have hfD : f ⁻¹ᵁ Y.basicOpen r ≤ f ⁻¹ᵁ V₀ := fun x hx => hD hx
  have hB : f ⁻¹ᵁ Y.basicOpen r ≤ X.basicOpen ((f.app V₀).hom r) := (Scheme.preimage_basicOpen f r).le
  have hunitA : IsUnit ((X.presheaf.map (homOfLE hfD).op).hom ((f.app V₀).hom r)) := by
    have h1 : IsUnit ((X.presheaf.map (homOfLE (X.basicOpen_le ((f.app V₀).hom r))).op).hom ((f.app V₀).hom r)) :=
      RingedSpace.isUnit_res_basicOpen X.toRingedSpace _
    have h2 := h1.map (X.presheaf.map (homOfLE hB).op).hom
    rw [← CommRingCat.comp_apply, ← Functor.map_comp] at h2
    exact h2
  have hunit : IsUnit ((X.presheaf.map (homOfLE hfD).op).hom m) := by
    apply isUnit_of_mul_isUnit_left (y := (X.presheaf.map (homOfLE hfD).op).hom s)
    rw [← map_mul, hs, map_pow]
    exact hunitA.pow n
  refine ⟨hunit.unit, fun z hz => ?_⟩
  have e : f (pullback.snd f f z) = f (pullback.fst f f z) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
  have hz1 : pullback.fst f f z ∈ f ⁻¹ᵁ Y.basicOpen r := hz
  have hz2 : pullback.snd f f z ∈ f ⁻¹ᵁ Y.basicOpen r := by
    show f (pullback.snd f f z) ∈ Y.basicOpen r
    rw [e]; exact hz
  have hz0 : z ∈ pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀ := hD hz
  have hzV : z ∈ pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V := hle hz0
  apply Units.ext
  rw [Units.val_mul, gm_val _ z _ hz1, gm_val _ z _ hzV, gm_val _ z _ hz2, IsUnit.unit_spec]
  have k1 : ((pullback f f).presheaf.germ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ Y.basicOpen r) z hz1).hom
      (((pullback.fst f f).app (f ⁻¹ᵁ Y.basicOpen r)).hom ((X.presheaf.map (homOfLE hfD).op).hom m)) =
      ((pullback f f).presheaf.germ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) z hz0).hom
        (((pullback.fst f f).app (f ⁻¹ᵁ V₀)).hom m) := by
    have e1 := congrArg (fun q => q.hom m) ((pullback.fst f f).naturality (homOfLE hfD).op)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e1
    rw [e1]; exact TopCat.Presheaf.germ_res_apply _ _ _ _ _
  have hz0' : z ∈ pullback.snd f f ⁻¹ᵁ f ⁻¹ᵁ V₀ := h hz0
  have k2 : ((pullback f f).presheaf.germ (pullback.snd f f ⁻¹ᵁ f ⁻¹ᵁ Y.basicOpen r) z hz2).hom
      (((pullback.snd f f).app (f ⁻¹ᵁ Y.basicOpen r)).hom ((X.presheaf.map (homOfLE hfD).op).hom m)) =
      ((pullback f f).presheaf.germ (pullback.snd f f ⁻¹ᵁ f ⁻¹ᵁ V₀) z hz0').hom
        (((pullback.snd f f).app (f ⁻¹ᵁ V₀)).hom m) := by
    have e1 := congrArg (fun q => q.hom m) ((pullback.snd f f).naturality (homOfLE hfD).op)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e1
    rw [e1]; exact TopCat.Presheaf.germ_res_apply _ _ _ _ _
  have k4 : ((pullback f f).presheaf.germ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) z hz0).hom
      (((pullback.snd f f).appLE (f ⁻¹ᵁ V₀) _ h).hom m) =
      ((pullback f f).presheaf.germ (pullback.snd f f ⁻¹ᵁ f ⁻¹ᵁ V₀) z hz0').hom
        (((pullback.snd f f).app (f ⁻¹ᵁ V₀)).hom m) := by
    simp only [Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply]
    exact TopCat.Presheaf.germ_res_apply _ _ _ _ _
  have k3 : ((pullback f f).presheaf.germ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) z hz0).hom ((res hle c).val) =
      ((pullback f f).presheaf.germ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V) z hzV).hom c.val := by
    simp only [res, Units.coe_map, MonoidHom.coe_coe]
    exact TopCat.Presheaf.germ_res_apply _ _ _ _ _
  have hm' := congrArg ((pullback f f).presheaf.germ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) z hz0).hom hm
  rw [map_mul, k3, k4] at hm'
  rw [k1, k2, ← hm']
  congr 1

end GlobalTheory.LBDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreActionTrivialOfFixedPointResidueFieldStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_action_trivial_of_fixed_point_residue_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), 1 ≤ Dw.p + Dw.q → l.A = 1 → ∀ (I : Ideal (𝓞 E)) (g : ℕ), NeatPrime I g (Dw.p + Dw.q) → l.Mb ≤ I → ∀ (Γ : Type) [Group Γ] [Finite Γ] (ι : Γ →* LevelAut Dw l), (∀ γ, UnipAt I (ι γ)) → ∀ (X' : Scheme.{0}) [IsIntegral X'] (φ : X' ⟶ X₀ TF.Y Z) (ρ' : Γ →* Aut X'), GlobalTheory.IsNormalScheme X' → IsProjOver (φ ≫ s₀ TF.Y Z) → ∀ m : Γ → ((GlobalTheory.EqvAct.pullG TF Z φ).left ⟶ (GlobalTheory.EqvAct.pullG TF Z φ).left), GlobalTheory.EqvAct.IsEqvAct ρ' (GlobalTheory.EqvAct.pullG TF Z φ) (GlobalTheory.EqvAct.pullAct TF Z φ) m → GlobalTheory.EqvAct.TorsLevel I ι ρ' (GlobalTheory.EqvAct.pullG TF Z φ) (GlobalTheory.EqvAct.pullAct TF Z φ) m → ∀ γ (x : X'), X'.fromSpecResidueField x ≫ (ρ' γ).hom = X'.fromSpecResidueField x → ∀ (T : Scheme.{0}) (w : T ⟶ (GlobalTheory.EqvAct.pullG TF Z φ).left) (v : T ⟶ Spec (X'.residueField x)), w ≫ (GlobalTheory.EqvAct.pullG TF Z φ).hom = v ≫ X'.fromSpecResidueField x → w ≫ m γ = w := by
  first | exact @GlobalTheory.EqvFib.fibre_trivial_of_fixed | exact GlobalTheory.EqvFib.fibre_trivial_of_fixed | (intros; apply GlobalTheory.EqvFib.fibre_trivial_of_fixed <;> assumption)
end

