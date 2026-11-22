import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
import Development.WeilBound.CoreStatements.HodgeTatePoints.TwhopfSec
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0005
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0017
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0014
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0012

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.MhBase
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge

noncomputable section

namespace PositivityTheory.HtPt.Mh

section pb

variable {A B C : Type} [CommRing A] [CommRing B] [CommRing C] {X Y : Scheme.{0}}

def pb (j : X ⟶ Spec (CommRingCat.of A)) : A →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ j.appTop).hom

def val (x : Spec (CommRingCat.of B) ⟶ X) : Γ(X, ⊤) →+* B :=
  (x.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom).hom

theorem valAt_top (x : Spec (CommRingCat.of B) ⟶ X) (h : ⊤ ≤ x ⁻¹ᵁ ⊤) (s : Γ(X, ⊤)) : valAt x ⊤ h s = val x s := by
  simp only [valAt, val, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rfl

theorem pb_ext {j j' : X ⟶ Spec (CommRingCat.of A)} (h : ∀ a, pb j a = pb j' a) : j = j' := by
  apply ext_of_isAffine
  have e : (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ j.appTop =
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ j'.appTop := by
    ext a
    exact h a
  exact (cancel_epi _).1 e

theorem pb_comp (f : Y ⟶ X) (j : X ⟶ Spec (CommRingCat.of A)) (a : A) : pb (f ≫ j) a = f.appTop (pb j a) := by
  unfold pb
  rw [Scheme.Hom.comp_appTop]
  rfl

theorem val_comp (x : Spec (CommRingCat.of B) ⟶ Y) (f : Y ⟶ X) (s : Γ(X, ⊤)) :
    val (x ≫ f) s = val x (f.appTop s) := by
  unfold val
  rw [Scheme.Hom.comp_appTop]
  rfl

theorem pb_spec (j : X ⟶ Spec (CommRingCat.of B)) (ψ : A →+* B) (a : A) :
    pb (j ≫ Spec.map (CommRingCat.ofHom ψ)) a = pb j (ψ a) := by
  simp only [pb, Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

theorem val_pb_id (b : B) : val (𝟙 _) (pb (𝟙 (Spec (CommRingCat.of B))) b) = b := by
  simp [val, pb]

theorem val_pb_comp (x : Spec (CommRingCat.of B) ⟶ X) (j : X ⟶ Spec (CommRingCat.of A)) (a : A) :
    val x (pb j a) = val (𝟙 _) (pb (x ≫ j) a) := by
  rw [pb_comp, ← val_comp, Category.id_comp]

theorem val_pb {x : Spec (CommRingCat.of B) ⟶ X} {j : X ⟶ Spec (CommRingCat.of A)} {φ : A →+* B}
    (h : x ≫ j = Spec.map (CommRingCat.ofHom φ)) (a : A) : val x (pb j a) = φ a := by
  have e := pb_spec (𝟙 (Spec (CommRingCat.of B))) φ a
  rw [Category.id_comp] at e
  rw [val_pb_comp, h, e, val_pb_id]

theorem val_id_injective : Function.Injective (val (𝟙 (Spec (CommRingCat.of B)))) := by
  intro s t hst
  have e : (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (val (𝟙 _) s) =
      (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (val (𝟙 _) t) := by
    rw [hst]
  simpa [val] using e

theorem comp_eq_spec {x : Spec (CommRingCat.of B) ⟶ X} {j : X ⟶ Spec (CommRingCat.of A)} {φ : A →+* B}
    (h : ∀ a, val x (pb j a) = φ a) : x ≫ j = Spec.map (CommRingCat.ofHom φ) := by
  refine pb_ext fun a => val_id_injective ?_
  rw [← val_pb_comp, h, val_pb (Category.id_comp _)]

theorem exists_pb (φ : A →+* Γ(X, ⊤)) : ∃ j : X ⟶ Spec (CommRingCat.of A), ∀ a, pb j a = φ a := by
  refine ⟨(ΓSpec.adjunction.homEquiv X (Opposite.op (CommRingCat.of A))) (CommRingCat.ofHom φ).op,
    fun a => ?_⟩
  rw [pb, ΓSpecIso_inv_ΓSpec_adjunction_homEquiv]
  rfl

theorem spec_inj {φ ψ : A →+* B} (h : Spec.map (CommRingCat.ofHom φ) = Spec.map (CommRingCat.ofHom ψ)) : φ = ψ :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem spec_comp (φ : A →+* B) (ψ : B →+* C) :
    Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom φ) = Spec.map (CommRingCat.ofHom (ψ.comp φ)) := by
  rw [← Spec.map_comp]
  rfl

end pb

variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] [Finite T]

theorem sec_ext (Γ : QFGroup R T) {s s' : Γ(Γ.G.left, ⊤)} (h : ∀ t, val (Γ.pt t).left s = val (Γ.pt t).left s') :
    s = s' := by
  rw [← sub_eq_zero]
  refine Twhopf.sec_inj R T Γ ⊤ _ fun t ht => ?_
  rw [valAt_top, map_sub, h, sub_self]

theorem hom_ext_pt (Γ : QFGroup R T) {A : Type} [CommRing A] {j j' : Γ.G.left ⟶ Spec (CommRingCat.of A)}
    (h : ∀ t, (Γ.pt t).left ≫ j = (Γ.pt t).left ≫ j') : j = j' :=
  pb_ext fun a => sec_ext Γ fun t => by rw [val_pb_comp, h, ← val_pb_comp]

theorem mem_top_iff (Γ : QFGroup R T) (f : T → R) : f ∈ Γ.btOrder ⊤ ↔
    ∀ t, ∃ s : Γ(Γ.G.left, ⊤), ∀ h, val (Γ.pt h).left s = algebraMap R (FractionRing R) (f (t * h)) := by
  have hsub : ∀ {B : Type} [CommRing B] {X : Scheme} (x : Spec (CommRingCat.of B) ⟶ X) (U : X.Opens)
      (hx : ⊤ ≤ x ⁻¹ᵁ U) (a b : Γ(X, U)), valAt x U hx (a - b) = valAt x U hx a - valAt x U hx b := by
    intro B _ X x U hx a b
    simp only [valAt, map_sub]
  constructor
  · intro hf t
    rw [Twhopf.mem_order] at hf
    have hreg : ∀ g : Γ.G.left, ∃ U : Γ.G.left.Opens, g ∈ U ∧ ∃ s : Γ(Γ.G.left, U),
        ∀ (h : T) (hh : ⊤ ≤ (Γ.pt h).left ⁻¹ᵁ U),
          valAt (Γ.pt h).left U hh s = algebraMap R (FractionRing R) (f (t * h)) :=
      fun g => hf t g (by simp)
    choose U hgU s hs using hreg
    obtain ⟨g0, hglue, -⟩ := TopCat.Sheaf.existsUnique_gluing' Γ.G.left.sheaf U ⊤
      (fun g => homOfLE le_top) (fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hgU x⟩) s (by
        intro g g'
        rw [← sub_eq_zero]
        apply Twhopf.sec_inj R T Γ _ _
        intro h hh
        have h1 : ⊤ ≤ (Γ.pt h).left ⁻¹ᵁ U g :=
          (SubOrder.top_le_iff_mem _ _).2 fun z => ((SubOrder.top_le_iff_mem _ _).1 hh z).1
        have h2 : ⊤ ≤ (Γ.pt h).left ⁻¹ᵁ U g' :=
          (SubOrder.top_le_iff_mem _ _).2 fun z => ((SubOrder.top_le_iff_mem _ _).1 hh z).2
        refine (hsub _ _ hh _ _).trans ?_
        erw [Twhopf.valAt_restrict _ _ hh h1, Twhopf.valAt_restrict _ _ hh h2]
        rw [hs, hs, sub_self])
    refine ⟨g0, fun h => ?_⟩
    have htop : ⊤ ≤ (Γ.pt h).left ⁻¹ᵁ ⊤ := (SubOrder.top_le_iff_mem _ _).2 fun _ => trivial
    let z : Spec (CommRingCat.of (FractionRing R)) := IsLocalRing.closedPoint (FractionRing R)
    have hh : ⊤ ≤ (Γ.pt h).left ⁻¹ᵁ U ((Γ.pt h).left z) :=
      Twhopf.top_le_of_mem _ z (hgU _)
    refine (valAt_top _ htop g0).symm.trans ?_
    refine (Twhopf.valAt_restrict _ (homOfLE le_top) hh htop g0).symm.trans ?_
    erw [hglue ((Γ.pt h).left z)]
    exact hs _ h hh
  · intro hf
    rw [Twhopf.mem_order]
    intro t g _
    obtain ⟨s, hs⟩ := hf t
    unfold QFGroup.RegularAt
    exact ⟨⊤, by simp, s, fun h hh => by rw [valAt_top, hs]⟩

omit [Finite T] in
theorem val_const (Γ : QFGroup R T) (t : T) (r : R) :
    val (Γ.pt t).left (pb Γ.G.hom r) = algebraMap R (FractionRing R) r :=
  val_pb (Over.w (Γ.pt t)) r

omit [Finite T] in
theorem val_emb {Γ : QFGroup R T} {A : Subalgebra R (T → R)} {j : Γ.G.left ⟶ Spec (CommRingCat.of A)}
    (hj : Γ.IsEmb A j) (t : T) (a : A) :
    val (Γ.pt t).left (pb j a) = algebraMap R (FractionRing R) (a.1 t) :=
  val_pb (hj.pt t) a

theorem exists_emb (Γ : QFGroup R T) (A : Subalgebra R (T → R))
    (hA : ∀ a : A, ∃ s : Γ(Γ.G.left, ⊤), ∀ t, val (Γ.pt t).left s = algebraMap R (FractionRing R) (a.1 t)) :
    ∃! j : Γ.G.left ⟶ Spec (CommRingCat.of A), Γ.IsEmb A j := by
  choose s hs using hA
  let φ : A →+* Γ(Γ.G.left, ⊤) :=
    { toFun := s
      map_one' := sec_ext Γ fun t => by rw [hs, map_one]; simp
      map_mul' := fun a b => sec_ext Γ fun t => by rw [hs, map_mul, hs, hs]; simp
      map_zero' := sec_ext Γ fun t => by rw [hs, map_zero]; simp
      map_add' := fun a b => sec_ext Γ fun t => by rw [hs, map_add, hs, hs]; simp }
  obtain ⟨j, hj⟩ := exists_pb φ
  have hpt : ∀ t, (Γ.pt t).left ≫ j = Spec.map (CommRingCat.ofHom
      ((algebraMap R (FractionRing R)).comp
        ((Pi.evalRingHom (fun _ : T => R) t).comp A.val.toRingHom))) := by
    intro t
    apply comp_eq_spec
    intro a
    rw [hj]
    exact hs a t
  refine ⟨j, ⟨?_, hpt⟩, fun j' hj' => hom_ext_pt Γ fun t => by rw [hj'.pt, hpt]⟩
  apply hom_ext_pt Γ
  intro t
  rw [← Category.assoc, hpt, spec_comp, Over.w (Γ.pt t)]
  show _ = Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))
  congr 2

end PositivityTheory.HtPt.Mh
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.RedOmHTBc
section
noncomputable section

namespace PositivityTheory.HtPt.Gb

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

theorem red_omHT_bc : ∀ (A K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K] (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (D : HTChart A K c p R N Ω) (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O) [Algebra A O] (κ' : O) (V : Type) [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V] (Ω' : Type) [AddCommGroup Ω'] [Module C Ω'] [Module O Ω'] [IsScalarTower O C Ω'] (P : HTPoint C O c κ' N V Ω') (ι : D.om →ₛₗ[algebraMap A O] Ω') (hred : D.ReducesTo (algebraMap A O) P ι) (σ : E →+* K) (σ' : E →+* C) (d : A), (∀ (a : 𝓞 E) (a' : A), algebraMap A K a' = σ (a : E) → algebraMap O C (algebraMap A O a') = σ' (a : E)) → GeneratesDiff σ d → κ' ∣ (p : O) ^ R → Module.Projective A (D.omHT σ) → ∃ j : O ⊗[A] (D.omHT σ) →ₗ[O] Ω', Function.Injective j ∧ LinearMap.range j = P.omHT σ' ∧ (∀ (z : D.omHT σ) (y : D.om), (y : Ω) = d • (z : Ω) → algebraMap A O d • j (1 ⊗ₜ z) = ι y) ∧ Module.finrank A (D.omHT σ) = Module.finrank C (P.Ωsp σ') := by
  intro A K _ _ _ _ _ _ _ _ E _ _ c hc p R N _ Ω _ _ _ _ D C _ _ _ v O _ _ hv _ κ' V _ _ _ _
    Ω' _ _ _ _ P ι hred σ σ' d hφ hd hκ hproj
  have hAK : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  have : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)
  have := isFractionRing_of_integers hv
  have hσ : ∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap A K).range := fun a =>
    IsIntegrallyClosed.isIntegral_iff.1
      ((map_isIntegral_int σ (RingOfIntegers.isIntegral_coe a)).tower_top)
  obtain ⟨hd', h1, h2, h3, -⟩ := red_proj A K hAK E c hc p R N Ω D C v O hv κ' V Ω'
    (algebraMap A O) P ι hred σ σ' d hσ hφ hd hκ
  have hδ : algebraMap O C (algebraMap A O d) ≠ 0 :=
    (different_generator_dualInt O C E σ' _ hv.hom_inj
      (exists_diff_generator C v O hv E σ').1 hd').1
  obtain ⟨j₀, hj₀, -, hj₀'⟩ := bc_iso A K Ω D.om C v O hv Ω' P.om ι D.om_lat D.om_proj P.om_lat
    hred.span_eq hred.rank_eq
  have hfg : (D.omHT σ).FG := by
    have : IsNoetherian A D.om := isNoetherian_of_fg_of_noetherian _ D.om_lat.fg
    have h := (IsNoetherian.noetherian (D.om'.comap D.om.subtype)).map D.om.subtype
    rw [Submodule.map_comap_subtype, inf_eq_right.2 (om'_le_om D)] at h
    exact h.map _
  have : Module.Finite A (D.omHT σ) := Module.Finite.iff_fg.2 hfg
  let α : D.omHT σ →ₗ[A] D.om := LinearMap.codRestrict D.om (d • (D.omHT σ).subtype) (by
    rintro ⟨_, x, hx, rfl⟩
    exact h1 x (om'_le_om D hx))
  let β : D.om →ₗ[A] D.omHT σ := LinearMap.codRestrict (D.omHT σ)
    ((eigProj D.ρΩ σ).restrictScalars A ∘ₗ ((p : A) ^ R • D.om.subtype))
    (fun x => ⟨_, pow_smul_mem_om' D x.2, rfl⟩)
  have hβα : β ∘ₗ α = ((p : A) ^ R * d) • LinearMap.id := by
    ext z
    change eigProj D.ρΩ σ ((p : A) ^ R • d • (z : Ω)) = ((p : A) ^ R * d) • (z : Ω)
    rw [LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower,
      LatBasic.eigProj_of_mem (LatBasic.eigQuot_le_eigSp _ _ D.om' z.2), mul_smul]
  have hne : algebraMap A O ((p : A) ^ R * d) ≠ 0 := by
    intro h
    have h' := congrArg (algebraMap O C) h
    rw [map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast, map_zero] at h'
    exact mul_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)) hδ h'
  have hα : Function.Injective (α.baseChange O) := by
    have h : Function.Injective ((β.baseChange O) ∘ₗ (α.baseChange O)) := by
      rw [← LinearMap.baseChange_comp, hβα, LinearMap.baseChange_smul, LinearMap.baseChange_id]
      intro x y e
      change ((p : A) ^ R * d) • x = ((p : A) ^ R * d) • y at e
      rw [← algebraMap_smul O, ← algebraMap_smul O ((p : A) ^ R * d) y] at e
      exact smul_right_injective _ hne e
    exact Function.Injective.of_comp h
  obtain ⟨j₁, hj₁, hr₁⟩ := exists_lift (ι.comp α)
  have hj₁' : j₁ = j₀ ∘ₗ α.baseChange O := by
    refine LinearMap.ext fun t => ?_
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | tmul o z =>
      have : o ⊗ₜ[A] z = o • ((1 : O) ⊗ₜ[A] z) := by simp [TensorProduct.smul_tmul']
      rw [this, map_smul, map_smul, hj₁, LinearMap.comp_apply j₀, LinearMap.baseChange_tmul, hj₀']
      rfl
  let s : Ω' →ₗ[O] Ω' :=
    ((algebraMap O C (algebraMap A O d))⁻¹ • (LinearMap.id : Ω' →ₗ[C] Ω')).restrictScalars O
  have hs : ∀ w, algebraMap A O d • s w = w := fun w => by
    change algebraMap A O d • (algebraMap O C (algebraMap A O d))⁻¹ • w = w
    rw [← algebraMap_smul C, smul_smul, mul_inv_cancel₀ hδ, one_smul]
  have hinj : Function.Injective (s ∘ₗ j₁) := by
    have hs' : Function.Injective s := fun x y e => by rw [← hs x, e, hs]
    rw [hj₁']
    exact hs'.comp (hj₀.comp hα)
  have hrange : LinearMap.range (s ∘ₗ j₁) = P.omHT σ' := by
    have e : Set.range (ι.comp α) = ι '' {y : D.om | ∃ z ∈ D.omHT σ, (y : Ω) = d • z} := by
      ext w
      constructor
      · rintro ⟨z, rfl⟩
        exact ⟨α z, ⟨z, z.2, rfl⟩, rfl⟩
      · rintro ⟨y, ⟨z, hz, e⟩, rfl⟩
        exact ⟨⟨z, hz⟩, congrArg ι (Subtype.ext e.symm)⟩
    rw [LinearMap.range_comp, hr₁, e, h3, ← Submodule.map_comp]
    have : s ∘ₗ (algebraMap A O d • LinearMap.id) = LinearMap.id := by
      ext w
      change s (algebraMap A O d • w) = w
      rw [map_smul, hs]
    rw [this, Submodule.map_id]
  refine ⟨s ∘ₗ j₁, hinj, hrange, fun z y e => ?_, ?_⟩
  · rw [LinearMap.comp_apply, hs, hj₁]
    exact congrArg ι (Subtype.ext e.symm)
  · have hl := (pt_om_block C v O hv E c hc κ' N V Ω' P σ').2.2.1
    rw [← finrank_baseChange_flat (O := O), ← LinearMap.finrank_range_of_inj hinj, hrange,
      ← finrank_lattice _ hl]
    have e : (latIn (P.omHT σ') (P.Ωsp σ')).map ((P.Ωsp σ').subtype.restrictScalars O) =
        P.omHT σ' := by
      rw [LatBasic.map_latIn]
      exact inf_eq_left.2 (LatBasic.eigQuot_le_eigSp _ _ _)
    conv_lhs => rw [← e]
    exact (Submodule.equivMapOfInjective _ Subtype.val_injective _).finrank_eq.symm

theorem chart_rank : ∀ (A K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K] (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (D : HTChart A K c p R N Ω) (κ : A) (σ : E →+* K) (d d' : A), ¬ IsUnit (p : A) → κ ∣ (p : A) ^ R → GeneratesDiff σ d → GeneratesDiff (σ.comp c.toRingHom) d' → Module.Projective A (D.omHT σ) → Module.Projective A (D.omHT (σ.comp c.toRingHom)) → D.HasTestPoints κ → Module.finrank A (D.omHT σ) + Module.finrank A (D.omHT (σ.comp c.toRingHom)) = N := by
  intro A K _ _ _ _ _ _ _ _ E _ _ c hc p R N _ Ω _ _ _ _ D κ σ d d' hp hκ hd hd' hP hP' htest
  have hAK : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  have hp0 : (p : A) ≠ 0 := fun h => by
    have h' := congrArg (algebraMap A K) h
    rw [map_natCast, map_zero] at h'
    exact Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero h'
  obtain ⟨𝔮, h𝔮⟩ := Ideal.nonempty_minimalPrimes (I := Ideal.span {(p : A)})
    (by rwa [Ne, Ideal.span_singleton_eq_top])
  have hprime : 𝔮.IsPrime := h𝔮.1.1
  have hmem : (p : A) ∈ 𝔮 := h𝔮.1.2 (Ideal.mem_span_singleton_self _)
  have hht : 𝔮.height = 1 := by
    refine le_antisymm (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ h𝔮) ?_
    rw [Order.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff, IsDomain.minimalPrimes_eq_singleton_bot]
    rintro rfl
    exact hp0 hmem
  obtain ⟨C, O, _, _, _, _, _, v, φ, V, Ω', _, _, _, _, _, _, _, _, P, ι, hv, hφ, -, hred⟩ :=
    htest 𝔮 hprime hht hmem
  let _ : Algebra A O := φ.toAlgebra
  have hg : Function.Injective ((algebraMap O C).comp φ) := hv.hom_inj.comp hφ
  let ψ : K →+* C := IsFractionRing.lift hg
  have hψ : ∀ (τ : E →+* K) (a : 𝓞 E) (a' : A), algebraMap A K a' = τ (a : E) →
      algebraMap O C (algebraMap A O a') = (ψ.comp τ) (a : E) := fun τ a a' h => by
    rw [RingHom.comp_apply, ← h]
    exact (IsFractionRing.lift_algebraMap hg a').symm
  have hκ' : φ κ ∣ (p : O) ^ R := by
    have := map_dvd φ hκ
    rwa [map_pow, map_natCast] at this
  obtain ⟨_, -, -, -, e1⟩ := red_omHT_bc A K E c hc p R N Ω D C v O hv (φ κ) V Ω' P ι hred σ
    (ψ.comp σ) d (hψ σ) hd hκ' hP
  obtain ⟨_, -, -, -, e2⟩ := red_omHT_bc A K E c hc p R N Ω D C v O hv (φ κ) V Ω' P ι hred
    (σ.comp c.toRingHom) (ψ.comp (σ.comp c.toRingHom)) d' (hψ _) hd' hκ' hP'
  rw [e1, e2]
  exact finrank_Ω_add_Ω P hv hc (ψ.comp σ)

end PositivityTheory.HtPt.Gb
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.RfTors
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.HtPt.Rf

section
variable {R : Type} [CommRing R] {p : ℕ} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  {N : Type} [AddCommGroup N] {pt : N → (sp (R₀ := R) R ⟶ G)}

theorem pt_zero (hpt : IsTorsPts G p pt) : pt 0 = 1 := by
  have h := hpt.add 0 0
  rw [add_zero] at h
  exact (mul_eq_left.1 h.symm)

theorem pt_nsmul (hpt : IsTorsPts G p pt) (n : ℕ) (x : N) : pt (n • x) = pt x ^ n := by
  induction n with
  | zero => rw [zero_nsmul, pow_zero, pt_zero hpt]
  | succ n ih => rw [succ_nsmul, hpt.add, ih, pow_succ]

theorem exists_pts (T : TorsRep G p) (hpt : IsTorsPts G p pt) :
    ∃ φ : N → (T.A →ₐ[R] R), ∀ x, spMap (φ x) ≫ T.y = pt x := by
  choose φ hφ using fun x => (T.univ R (pt x) ((hpt.range _).2 ⟨x, rfl⟩)).exists
  exact ⟨φ, hφ⟩

omit [AddCommGroup N] in
theorem mem_torsFun {C : Type} [Field C] [Algebra R C] (T : TorsRep G p)
    {φ : N → (T.A →ₐ[R] R)} (hφ : ∀ x, spMap (φ x) ≫ T.y = pt x) (g : N → C) :
    g ∈ torsFun C T pt ↔ ∃ a : T.A, g = fun x => algebraMap R C (φ x a) := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, funext fun x => ha x _ (hφ x)⟩
  · rintro ⟨a, rfl⟩
    refine ⟨a, fun x ψ h => ?_⟩
    rw [tors_ext T (h.trans (hφ x).symm)]

omit [AddCommGroup N] in
theorem mem_vanIdeal (T : TorsRep G p) {φ : N → (T.A →ₐ[R] R)}
    (hφ : ∀ x, spMap (φ x) ≫ T.y = pt x) (K : Set N) (a : T.A) :
    a ∈ vanIdeal T pt K ↔ ∀ k ∈ K, φ k a = 0 := by
  constructor
  · exact fun h k hk => h k hk _ (hφ k)
  · intro h k hk ψ e
    rw [tors_ext T (e.trans (hφ k).symm)]
    exact h k hk

end

theorem tors_hopf : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], ∀ (T : TorsRep G p) (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N] (pt : N → (sp (R₀ := R) R ⟶ G)), IsTorsPts G p pt → (∃ AA : HopfOrder (C := C) R N, AA.carrier = torsFun C T pt) ∧ (∀ a : T.A, (∀ φ : T.A →ₐ[R] R, φ a = 0) → a = 0) ∧ (∀ x, ∃! φ : T.A →ₐ[R] R, spMap φ ≫ T.y = pt x) ∧ (∀ φ : T.A →ₐ[R] R, ∃ x, spMap φ ≫ T.y = pt x) ∧ ∀ x : N, p • x = 0 := by
  intro p _ C _ _ _ v R _ _ hv hp G _ _ T N _ _ _ pt hpt
  obtain ⟨Δ, ε, s, hΔ, -, -, h1, h2, h3, h4, h5⟩ := tors_alg R p G T
  obtain ⟨φ, hφ⟩ := exists_pts T hpt
  have hsurj : ∀ ψ : T.A →ₐ[R] R, ∃ x, spMap ψ ≫ T.y = pt x := fun ψ =>
    ((hpt.range _).1 (tors_pow T ψ)).imp fun _ h => h.symm
  have hbij : Function.Bijective φ :=
    ⟨fun x y h => hpt.inj (by rw [← hφ, ← hφ, h]),
      fun ψ => (hsurj ψ).imp fun x h => tors_ext T ((hφ x).trans h.symm)⟩
  let : Bialgebra R T.A := Bialgebra.ofAlgHom Δ ε h1 h2 h3
  let : HopfAlgebra R T.A := HopfAlgebra.ofAlgHom s h4 (by
    change AlgHom.comp _ Δ = AlgHom.comp _ ε
    rw [← h4]
    conv_lhs => rw [← h5, ← AlgHom.comp_assoc]
    congr 1
    ext <;> simp)
  have : Coalgebra.IsCocomm R T.A := ⟨congr(($h5).toLinearMap)⟩
  have := T.fin
  have := T.free
  obtain ⟨hsep, -, AA, hAA⟩ := hopfalg p C v R hv hp T.A N φ hbij (fun x y a => by
    have : φ (x + y) = (Algebra.TensorProduct.lift (φ x) (φ y) (fun _ _ => Commute.all _ _)).comp Δ := by
      apply tors_ext T
      rw [lift_comul T Δ hΔ, Algebra.TensorProduct.lift_comp_includeLeft,
        show (Algebra.TensorProduct.lift (φ x) (φ y) (fun _ _ => Commute.all _ _)).comp
          Algebra.TensorProduct.includeRight = φ y by ext; simp, hφ, hφ, hφ, hpt.add]
    rw [this]
    rfl)
  refine ⟨⟨AA, ?_⟩, fun a ha => hsep a fun x => ha _, fun x => ?_, hsurj, fun x => hpt.inj ?_⟩
  · ext g
    rw [hAA, mem_torsFun T hφ]
  · exact T.univ R (pt x) ((hpt.range _).2 ⟨x, rfl⟩)
  · rw [pt_nsmul hpt, pt_zero hpt]
    exact (hpt.range _).2 ⟨x, rfl⟩

end PositivityTheory.HtPt.Rf
end

