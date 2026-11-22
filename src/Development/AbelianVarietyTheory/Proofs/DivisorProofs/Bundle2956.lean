import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2843
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2865
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FlatSurjectiveKernel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2811
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2850
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2121
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2678
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0084
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkHomStalkMapEqFunctionFieldExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.ZH.RatModel

theorem stalkHom_stalkMap_algebraMap : ∀ (o₁ Ω₁ o₂ Ω₂ : Type) [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂] [Algebra Ω₁ Ω₂] (M₁ : RatModel o₁ Ω₁) (M₂ : RatModel o₂ Ω₂) (p : M₂.Z ⟶ M₁.Z), M₂.pt ≫ p = spMap (algebraMap Ω₁ Ω₂) ≫ M₁.pt → ∀ (z₂ : M₂.Z) (x : M₁.Z.presheaf.stalk (p z₂)), M₂.stalkHom z₂ ((p.stalkMap z₂).hom x) = algebraMap Ω₁ Ω₂ (M₁.stalkHom (p z₂) x) := by
  intro o₁ Ω₁ o₂ Ω₂ _ _ _ _ _ _ _ M₁ M₂ p hp z₂ x
  obtain ⟨U, hU, f, rfl⟩ := M₁.Z.presheaf.germ_exist x
  rw [Scheme.Hom.germ_stalkMap_apply, RatModel.stalkHom_germ, RatModel.stalkHom_germ (M := M₂) (show z₂ ∈ p ⁻¹ᵁ U from hU)]
  rw [GlobalTheory.Points.valF_eq_valR, GlobalTheory.Points.valF_eq_valR, ← GlobalTheory.Points.valR_comp, hp,
    GlobalTheory.Points.valR_spMap_comp _ _ _ (M₁.top_le_preimage_pt ⟨_, hU⟩)]

end GlobalTheory.ZH.RatModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureCohomologyFlatBaseChange
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem flat_cohomology_baseChange {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] [Module.Flat R R']
    {A B C H H' : Type} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
    [AddCommGroup H] [Module R H] [AddCommGroup H'] [Module R' H']
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) (hfg : ∀ a, g (f a) = 0)
    (θ : LinearMap.ker (g.baseChange R) →ₗ[R] H) (θ' : LinearMap.ker (g.baseChange R') →ₗ[R'] H')
    (hs : Function.Surjective θ) (hk : ∀ z, θ z = 0 ↔ z.1 ∈ LinearMap.range (f.baseChange R))
    (hs' : Function.Surjective θ') (hk' : ∀ z, θ' z = 0 ↔ z.1 ∈ LinearMap.range (f.baseChange R'))
    (p : H → H')
    (hp : ∀ z z', z'.1 = (Algebra.ofId R R').toLinearMap.rTensor B z.1 → θ' z' = p (θ z)) :
    ∃ e : R' ⊗[R] H ≃ₗ[R'] H', ∀ c, e (1 ⊗ₜ c) = p c := by
  let Z := LinearMap.ker g
  let f' : A →ₗ[R] Z := f.codRestrict Z hfg
  let i : Z →ₗ[R] LinearMap.ker (g.baseChange R) :=
    ((TensorProduct.mk R R B 1) ∘ₗ Z.subtype).codRestrict _ (fun z ↦ by
      have : g z.1 = 0 := z.2
      simp [this])
  have hi : ∀ z : Z, (i z).1 = (1 : R) ⊗ₜ[R] z.1 := fun z ↦ rfl
  have his : Function.Surjective i := by
    rintro ⟨x, hx⟩
    obtain ⟨b, rfl⟩ := (TensorProduct.lid R B).symm.surjective x
    have hb : g b = 0 := by
      have h1 : (1 : R) ⊗ₜ[R] g b = 0 := by simpa using hx
      have := congrArg (TensorProduct.lid R C) h1
      simpa using this
    exact ⟨⟨b, hb⟩, Subtype.ext (by simp [hi])⟩
  let τ : Z →ₗ[R] H := θ ∘ₗ i
  have hτs : Function.Surjective τ := hs.comp his
  have hex : Function.Exact f' τ := by
    intro z
    change θ (i z) = 0 ↔ _
    rw [hk, hi]
    constructor
    · rintro ⟨x, hx⟩
      obtain ⟨a, rfl⟩ := (TensorProduct.lid R A).symm.surjective x
      refine ⟨a, Subtype.ext ?_⟩
      have := congrArg (TensorProduct.lid R B) hx
      change f a = z.1
      simpa using this
    · rintro ⟨a, rfl⟩
      exact ⟨1 ⊗ₜ a, rfl⟩
  have hexZ : Function.Exact (Z.subtype.baseChange R') (g.baseChange R') :=
    Module.Flat.lTensor_exact R' (LinearMap.exact_subtype_ker_map g)
  have hinj : Function.Injective (Z.subtype.baseChange R') :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := R') Z.subtype Z.subtype_injective
  let j : R' ⊗[R] Z →ₗ[R'] LinearMap.ker (g.baseChange R') :=
    (Z.subtype.baseChange R').codRestrict _ (fun x ↦ hexZ.apply_apply_eq_zero x)
  have hjs : Function.Surjective j := by
    rintro ⟨x, hx⟩
    obtain ⟨y, rfl⟩ := (hexZ x).1 hx
    exact ⟨y, rfl⟩
  let a : R' ⊗[R] Z →ₗ[R'] R' ⊗[R] H := τ.baseChange R'
  let b : R' ⊗[R] Z →ₗ[R'] H' := θ' ∘ₗ j
  have has : Function.Surjective a := LinearMap.lTensor_surjective R' hτs
  have hbs : Function.Surjective b := hs'.comp hjs
  have hexa : Function.Exact (f'.baseChange R') a := lTensor_exact R' hex hτs
  have hcomp : ∀ y, Z.subtype.baseChange R' (f'.baseChange R' y) = f.baseChange R' y := by
    intro y
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
    rfl
  have hker : LinearMap.ker a = LinearMap.ker b := by
    ext x
    rw [LinearMap.mem_ker, LinearMap.mem_ker, hexa x]
    change _ ↔ θ' (j x) = 0
    rw [hk']
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, (hcomp y).symm⟩
    · rintro ⟨y, hy⟩
      exact ⟨y, hinj ((hcomp y).trans hy)⟩
  refine ⟨(a.quotKerEquivOfSurjective has).symm ≪≫ₗ Submodule.quotEquivOfEq _ _ hker ≪≫ₗ
    b.quotKerEquivOfSurjective hbs, fun c ↦ ?_⟩
  obtain ⟨z, rfl⟩ := hτs c
  have h1 : (a.quotKerEquivOfSurjective has).symm ((1 : R') ⊗ₜ[R] τ z) =
      Submodule.Quotient.mk ((1 : R') ⊗ₜ[R] z) := by
    rw [LinearEquiv.symm_apply_eq]
    rfl
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, h1]
  change θ' (j (1 ⊗ₜ z)) = p (θ (i z))
  apply hp
  rw [hi, LinearMap.rTensor_tmul]
  change (1 : R') ⊗ₜ[R] z.1 = (algebraMap R R' 1) ⊗ₜ[R] z.1
  rw [map_one]

theorem exists_fin_affine_cover {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) [QuasiCompact s] :
    ∃ (n : ℕ) (D : Fin n → X.Opens), (∀ i, IsAffineOpen (D i)) ∧ ⨆ i, D i = ⊤ := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  obtain ⟨S, hS, e⟩ := (isCompact_iff_finite_and_eq_biUnion_affineOpens (U := (⊤ : X.Opens))).1 isCompact_univ
  have := hS.fintype
  let q := (Fintype.equivFin S).symm
  refine ⟨_, fun i ↦ (q i).1.1, fun i ↦ (q i).1.2, ?_⟩
  rw [e]
  apply le_antisymm
  · exact iSup_le fun i ↦ le_iSup₂_of_le (q i).1 (q i).2 le_rfl
  · refine iSup₂_le fun U hU ↦ ?_
    obtain ⟨i, hi⟩ := q.surjective ⟨U, hU⟩
    exact le_iSup_of_le i (by simp only [hi]; exact le_rfl)

theorem flat_baseChange_HO : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] [Module.Flat R R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (φ : X' ⟶ X) (h : IsPullback φ s' s (spMap (algebraMap R R'))), IsSeparated s → QuasiCompact s → (∃ e : R' ⊗[R] HO1 s ≃ₗ[R'] HO1 s', ∀ c, e (1 ⊗ₜ c) = pullHO1 h.w c) ∧ ∃ e : R' ⊗[R] HO2 s ≃ₗ[R'] HO2 s', ∀ c, e (1 ⊗ₜ c) = pullHO2 h.w c := by
  intro R R' _ _ _ _ X X' s s' φ h hsep hqc
  obtain ⟨n, D, hD, hcov⟩ := exists_fin_affine_cover s
  obtain ⟨M⟩ := GlobalTheory.T.orderedCech_finiteAffineCover_models_structureSheafCohomology R X s (Fin n) D hsep hD hcov
  generalize GlobalTheory.AbLaw.cechLB s (LB.triv X) D = K at M
  have h0 : IsPullback (𝟙 X) s s (spMap (algebraMap R R)) := by
    have e : spMap (algebraMap R R) = 𝟙 _ := spMap_id R
    rw [e]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  have hdd : ∀ i j k a, (K.d j k).hom ((K.d i j).hom a) = 0 := by
    intro i j k a
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, K.d_comp_d]
    rfl
  obtain ⟨a1, a2, a3, a4⟩ := M.exact h0
  obtain ⟨b1, b2, b3, b4⟩ := M.exact h
  obtain ⟨c1, c2⟩ := M.nat h0 h (Algebra.ofId R R') φ h.w (Category.comp_id φ)
  exact ⟨flat_cohomology_baseChange _ _ (hdd 0 1 2) (M.θ1 h0) (M.θ1 h) a1 a2 b1 b2 _ c1,
    flat_cohomology_baseChange _ _ (hdd 1 2 3) (M.θ2 h0) (M.θ2 h) a3 a4 b3 b4 _ c2⟩

end GlobalTheory.AbCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureMapEqOfSameGenericImageModuli
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

theorem GlobalTheory.TInj.baseEq_of_sameImage : ∀ {o R V : Type} [CommRing o] [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] {X : Scheme.{0}} (sX : X ⟶ Sp o) (y : Sp (FractionRing R) ⟶ X) (b : o →+* R), y ≫ sX = jK R ≫ spMap b → ∀ (θ₁ θ₂ : R →+* V) (κ₁ κ₂ : Sp (FractionRing V) ⟶ Sp (FractionRing R)), κ₁ ≫ jK R = jK V ≫ spMap θ₁ → κ₂ ≫ jK R = jK V ≫ spMap θ₂ → κ₁ ≫ y = κ₂ ≫ y → θ₁.comp b = θ₂.comp b := by
  intro o R V _ _ _ _ _ X sX y b hy θ₁ θ₂ κ₁ κ₂ h₁ h₂ hκ
  have key : ∀ (θ : R →+* V) (κ : Sp (FractionRing V) ⟶ Sp (FractionRing R)), κ ≫ jK R = jK V ≫ spMap θ →
      jK V ≫ spMap (θ.comp b) = κ ≫ y ≫ sX := by
    intro θ κ h
    rw [hy, ← Category.assoc, h, Category.assoc]
    simp only [jK, spMap, ← Spec.map_comp]
    rfl
  have e : jK V ≫ spMap (θ₁.comp b) = jK V ≫ spMap (θ₂.comp b) := by
    rw [key θ₁ κ₁ h₁, key θ₂ κ₂ h₂, ← Category.assoc, hκ, Category.assoc]
  simp only [jK, spMap, ← Spec.map_comp] at e
  have e2 := congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  ext r
  have := congrArg (fun f => f r) e2
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at this
  exact IsFractionRing.injective V (FractionRing V) this
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubringEqTopOfWeightUnits
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

set_option maxHeartbeats 1000000 in

theorem subring_eq_top_of_weight_units : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (Y : Ext D) (i : splitTorus (Sp R) D.X ⟶ Y.H), IsMonHom i → IsPullback i (toUnit _) Y.q η[D.P.A] → ∀ {κ : Type} (bs : Module.Basis κ ℤ D.X) (V : D.P.A.left.Opens), IsAffineOpen V → ∀ (u : κ → Γ(Y.H.left, Y.q.left ⁻¹ᵁ V)ˣ), (∀ c, GlobalTheory.UU.IsWt i _ (u c).val (bs c)) → ∀ S : Subring Γ(Y.H.left, Y.q.left ⁻¹ᵁ V), (∀ c, (Y.q.left.app V).hom c ∈ S) → (∀ c, (u c).val ∈ S ∧ ((u c)⁻¹).val ∈ S) → S = ⊤ := by
  intro R _ _ D Y i hi hk κ bs V hV u hu S hS hSu
  obtain ⟨hsm, haff, hsurj⟩ := Y.q_props
  have hmon : IsMonHom Y.q := Y.isMonHom_q
  let m : Multiplicative D.X →* Γ(Y.H.left, Y.q.left ⁻¹ᵁ V)ˣ :=
    AddMonoidHom.toMultiplicativeLeft (bs.constr ℤ (fun k => Additive.ofMul (u k))).toAddMonoidHom
  have hm : ∀ k, m (Multiplicative.ofAdd (bs k)) = u k := fun k =>
    congrArg Additive.toMul (bs.constr_basis ℤ (fun k => Additive.ofMul (u k)) k)
  have key : ∀ χ : D.X, GlobalTheory.UU.IsWt i _ (m (Multiplicative.ofAdd χ)).val χ ∧
      (m (Multiplicative.ofAdd χ)).val ∈ S ∧ (m (Multiplicative.ofAdd χ))⁻¹.val ∈ S := by
    intro χ
    have hχ : χ ∈ AddSubgroup.closure (Set.range bs) := by
      rw [← Submodule.span_int_eq_addSubgroupClosure, bs.span_eq]; trivial
    refine AddSubgroup.closure_induction (p := fun x _ => GlobalTheory.UU.IsWt i _ (m (Multiplicative.ofAdd x)).val x ∧
      (m (Multiplicative.ofAdd x)).val ∈ S ∧ (m (Multiplicative.ofAdd x))⁻¹.val ∈ S) ?_ ?_ ?_ ?_ hχ
    · rintro _ ⟨k, rfl⟩
      rw [hm]; exact ⟨hu k, hSu k⟩
    · rw [ofAdd_zero, map_one]; exact ⟨GlobalTheory.UU.isWt_one, S.one_mem, by simpa using S.one_mem⟩
    · intro x y _ _ hx hy
      rw [ofAdd_add, map_mul]
      refine ⟨hx.1.mul hy.1, ?_, ?_⟩
      · rw [Units.val_mul]; exact S.mul_mem hx.2.1 hy.2.1
      · rw [mul_inv, Units.val_mul]; exact S.mul_mem hx.2.2 hy.2.2
    · intro x _ hx
      rw [ofAdd_neg, map_inv]
      exact ⟨hx.1.inv, hx.2.2, by rw [inv_inv]; exact hx.2.1⟩
  have hbij := (isAffineOpen_and_bijective_of_weight_units (Sp R) D.X Y.H D.P.A Y.q i hmon hi inferInstance
    hsurj inferInstance hk V hV m (fun χ => (key χ).1)).2
  refine (Subring.eq_top_iff' S).2 fun f => ?_
  obtain ⟨x, rfl⟩ := hbij.2 f
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => rw [map_zero]; exact S.zero_mem
  | add a b ha hb => rw [map_add]; exact S.add_mem ha hb
  | single χ c =>
    change AddMonoidAlgebra.liftNC _ _ _ ∈ S
    rw [AddMonoidAlgebra.liftNC_single]
    exact S.mul_mem (hS c) (key χ).2.1

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumFConstMul
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

namespace GlobalTheory.Poinc.Sep

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}

def TorChar {X₁ : Setup F W i} {z₁ : X₁.M.Z} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}
    {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
    {X : Type} [AddCommGroup X] {m : ℕ} {t : Fin m → V} {δ : Fin m → LinearMap.BilinForm ℤ X}
    (𝔪 : UMem X₁ z₁ act V ev X t δ) (τ : X₁.S.Gam) (χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ) : Prop :=
  χ ^ (X₁.S.r * X₁.S.N) = 1 ∧ ∀ g₀ : GtPtF 𝔪.D.toPre (FractionRing V), IsTor χ g₀ →
    ∃ (p : QkPt 𝔪.D.toPre (FractionRing V) (X₁.S.r * X₁.S.N)) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A),
      p.y = 0 ∧ p.g = g₀ ∧ QkToAkU 𝔪.U.toUnifPre (FractionRing V) (X₁.S.r * X₁.S.N) p x ∧
      x.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left

def TransExp {X₁ : Setup F W i} {z₁ : X₁.M.Z} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}
    {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
    {X : Type} [AddCommGroup X] {m : ℕ} {t : Fin m → V} {δ : Fin m → LinearMap.BilinForm ℤ X}
    (𝔪 : UMem X₁ z₁ act V ev X t δ) (x₀ a τ : X₁.S.Gam) (e : ℕ) : Prop :=
  ∀ χ, TorChar 𝔪 τ χ → ∀ (C : Type) (lab : C → X₁.S.Gam) (T : (Fin 8 → X) → C → V), 𝔪.Terms x₀ lab T →
    ∀ c, lab c = a → ∀ (C' : Type) (lab' : C' → X₁.S.Gam) (T' : (Fin 8 → X) → C' → V), 𝔪.Terms x₀ lab' T' →
    ∀ c', lab' c' = a + τ → ∀ mu : Fin 8 → X,
      ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) * algebraMap V (FractionRing V) (T mu c) =
        𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ e)) * algebraMap V (FractionRing V) (T' mu c')

theorem sumF_const_mul {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {K : Type} [Field K]
    [Algebra (FractionRing R) K] {Ix : Type} {x : Ix → K} {s : K} (c : K) (h : SumF I K x s) :
    SumF I K (fun j => c * x j) (c * s) := by
  letI : Module R K := Module.compHom K (algebraMap R (FractionRing R))
  obtain ⟨N, hN, hs, hx, hlim⟩ := h
  let f : K →ₗ[R] K :=
    { toFun := fun y => c * y
      map_add' := fun y z => mul_add c y z
      map_smul' := fun r y => by
        change c * ((algebraMap R (FractionRing R) r : FractionRing R) • y) = (algebraMap R (FractionRing R) r : FractionRing R) • (c * y)
        rw [Algebra.smul_def, Algebra.smul_def]; ring }
  refine ⟨N.map f, hN.map f, ⟨s, hs, rfl⟩, fun j => ⟨x j, hx j, rfl⟩, fun k => ?_⟩
  obtain ⟨S, hS⟩ := hlim k
  refine ⟨S, fun T hT => ?_⟩
  have := Submodule.mem_map_of_mem (f := f) (hS T hT)
  rw [Submodule.map_smul''] at this
  convert this using 1
  change c * s - ∑ j ∈ T, c * x j = c * (s - ∑ j ∈ T, x j)
  rw [mul_sub, Finset.mul_sum]

end GlobalTheory.Poinc.Sep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumIOfSumFMul
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

noncomputable section

namespace GlobalTheory.Poinc.TwistSum₂

theorem sumI_of_sumF_mul {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] [IsNoetherianRing V] {Ix : Type}
    (y : Ix → V) (v : V) (d : FractionRing V) (hd : d ≠ 0)
    (h : SumF (maximalIdeal V) (FractionRing V) (fun i => algebraMap V (FractionRing V) (y i) * d)
      (algebraMap V (FractionRing V) v * d)) :
    SumI (maximalIdeal V) y v := by
  classical
  have hsm : ∀ (r : V) (x : FractionRing V), r • x = algebraMap V (FractionRing V) r * x := Algebra.smul_def
  have hmod : (Module.compHom (FractionRing V) (algebraMap V (FractionRing V)) : Module V (FractionRing V)) =
      Algebra.toModule := Module.ext' _ _ fun r x => (Algebra.smul_def r x).symm
  unfold SumF at h
  rw [hmod] at h
  obtain ⟨N, hN, -, -, hS⟩ := h
  let P : Submodule V (FractionRing V) := N ⊔ Submodule.span V {d}
  haveI : Module.Finite V P := Module.Finite.iff_fg.mpr (hN.sup (Submodule.fg_span_singleton d))
  let L : Submodule V P := (Submodule.span V {d}).comap P.subtype
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul (maximalIdeal V) L
  refine ⟨⊤, Module.Finite.fg_top, Submodule.mem_top, fun _ => Submodule.mem_top, fun n => ?_⟩
  obtain ⟨S, hS⟩ := hS (n + k)
  refine ⟨S, fun T hT => ?_⟩
  set w : V := v - ∑ i ∈ T, y i with hw
  have e : algebraMap V (FractionRing V) w * d =
      algebraMap V (FractionRing V) v * d - ∑ i ∈ T, algebraMap V (FractionRing V) (y i) * d := by
    rw [hw, map_sub, map_sum, sub_mul, Finset.sum_mul]
  have h1 : algebraMap V (FractionRing V) w * d ∈ maximalIdeal V ^ (n + k) • N := e ▸ hS T hT
  have hwP : algebraMap V (FractionRing V) w * d ∈ P :=
    Submodule.mem_sup_right (by rw [← hsm]; exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self d))
  let p : P := ⟨_, hwP⟩
  have hp1 : p ∈ maximalIdeal V ^ (n + k) • (⊤ : Submodule V P) :=
    (Submodule.mem_smul_top_iff _ P p).2 (Submodule.smul_mono le_rfl le_sup_left h1)
  have hp2 : p ∈ L := by
    show algebraMap V (FractionRing V) w * d ∈ Submodule.span V {d}
    rw [← hsm]; exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self d)
  have hp3 : p ∈ maximalIdeal V ^ n • L := by
    have := (hk (n + k) (Nat.le_add_left _ _)).le ⟨hp1, hp2⟩
    rw [Nat.add_sub_cancel] at this
    exact Submodule.smul_mono le_rfl inf_le_right this
  have hp4 : algebraMap V (FractionRing V) w * d ∈ maximalIdeal V ^ n • Submodule.span V {d} := by
    have := Submodule.mem_map_of_mem (f := P.subtype) hp3
    rw [Submodule.map_smul''] at this
    exact Submodule.smul_mono le_rfl (Submodule.map_comap_le _ _) this
  obtain ⟨u, hu, hud⟩ := Submodule.mem_smul_span_singleton.1 hp4
  rw [hsm] at hud
  have hwu : w = u := IsFractionRing.injective V (FractionRing V) (mul_right_cancel₀ hd hud).symm
  rw [hwu]
  simpa using Submodule.smul_mem_smul hu (Submodule.mem_top : (1 : V) ∈ (⊤ : Submodule V V))

end GlobalTheory.Poinc.TwistSum₂

namespace GlobalTheory.Poinc.TwistSum₂

open GlobalTheory.Poinc.Sep

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}

theorem val_stalkHom (X₁ : Setup F W i) (z₁ : X₁.M.Z) {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V]
    (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) [IsLocalHom ev] (a : X₁.M.Z.presheaf.stalk z₁) :
    X₁.M.val (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (X₁.M.stalkHom z₁ a) =
      algebraMap V (FractionRing V) (ev a) := by
  have hc : (spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (closedPoint V) = z₁ := by
    refine (Scheme.Hom.comp_apply _ _ _).trans
      (Eq.trans (congrArg (X₁.M.Z.fromSpecStalk z₁) ?_) (Scheme.fromSpecStalk_closedPoint (x := z₁)))
    exact comap_closedPoint ev
  have h : (spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (closedPoint V) ⤳ z₁ := specializes_of_eq hc
  have e := RatModel.val_spMap_comp (algebraMap V (FractionRing V)) (spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) h
    (X₁.M.stalkEquiv z₁ a)
  rw [RatModel.coe_stalkEquiv] at e
  refine e.trans (congrArg _ ?_)
  have hψ : Spec.map (X₁.M.Z.presheaf.stalkSpecializes h ≫ Scheme.stalkClosedPointTo (spMap ev ≫ X₁.M.Z.fromSpecStalk z₁)) ≫
      X₁.M.Z.fromSpecStalk z₁ = spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ := by
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  have heq : spMap ev = Spec.map (X₁.M.Z.presheaf.stalkSpecializes h ≫
      Scheme.stalkClosedPointTo (spMap ev ≫ X₁.M.Z.fromSpecStalk z₁)) := by
    rw [← cancel_mono (X₁.M.Z.fromSpecStalk z₁), hψ]
  have hφψ := Spec.map_injective heq
  simp only [RatModel.valLoc, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    RingEquiv.symm_apply_apply]
  exact (congrArg (fun φ => φ.hom a) hφψ).symm

theorem twistSum_of_sumF : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (x₀ : X₁.S.Gam) (C : Type) (lab : C → X₁.S.Gam) (T : (Fin 8 → X) → C → V) (sg : ℤˣ) (c : C) (τ : X₁.S.Gam) (χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ) (e : ℕ), 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩ ≠ 0 → (∀ mu, ∃ a : X₁.S.Gam, 𝔪.YY a mu) → (∀ a mu, 𝔪.YY a mu → ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) = 𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (((sg : ℤˣ) : ℤ) • eStd X₁.S.g _ τ a).val)))) → SumF (maximalIdeal V) (FractionRing V) (fun mu : Fin 8 → X => ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) * (algebraMap V (FractionRing V) (T mu c) * 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩)) (𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ e)) * 𝔪.yK ⟨X₁.S.th (lab c + τ), X₁.S.th_mem (lab c + τ)⟩) → TwistSum X₁ z₁ act x₀ 𝔪 lab T sg c τ e := by
  intro g n F W Z i X₁ z₁ act V _ _ _ ev X _ m t δ 𝔪 x₀ C lab T sg c τ χ e hθ hY hχ hS
  intro zt h hzt hh wt hwt
  haveI : IsNoetherianRing V := 𝔪.cn.1
  haveI : IsLocalHom ev := 𝔪.loc
  have hc : (spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (closedPoint V) = z₁ := by
    refine (Scheme.Hom.comp_apply _ _ _).trans
      (Eq.trans (congrArg (X₁.M.Z.fromSpecStalk z₁) ?_) (Scheme.fromSpecStalk_closedPoint (x := z₁)))
    exact comap_closedPoint ev
  have hsp : ∀ w, (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) w ⤳
      (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (closedPoint (FractionRing V)) :=
    RatModel.specializes_of_range_eq (RatModel.range_eq_singleton (M := X₁.M) (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (IsLocalRing.closedPoint (FractionRing V)))
  have hgen : (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (closedPoint (FractionRing V)) ⤳ z₁ := by
    have h1 : (jK V) (closedPoint (FractionRing V)) ⤳ closedPoint V := IsLocalRing.specializes_closedPoint _
    have h2 := h1.map (spMap ev ≫ X₁.M.Z.fromSpecStalk z₁).continuous
    rw [hc] at h2
    exact h2
  have hO : ∀ s, X₁.M.stalkHom z₁ s ∈
      X₁.M.O ((jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (closedPoint (FractionRing V))) := fun s =>
    RatModel.O_le_of_specializes hgen (X₁.M.stalkEquiv z₁ s).2
  have hR : ∀ a ∈ X₁.S.R, a ∈ X₁.M.O ((jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (closedPoint (FractionRing V))) := 𝔪.reg
  have hyK : ∀ (a : X₁.Ω₁) (ha : a ∈ X₁.S.R), 𝔪.yK ⟨a, ha⟩ = X₁.M.val (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) a :=
    fun a ha => 𝔪.yK_eq ⟨a, ha⟩
  have hyA : ∀ b : X₁.o₁, 𝔪.yK (algebraMap X₁.o₁ X₁.S.R b) =
      X₁.M.val (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (algebraMap X₁.o₁ X₁.Ω₁ b) := fun b => by
    rw [𝔪.yK_eq, Subalgebra.coe_algebraMap]
  have hzt' : algebraMap V (FractionRing V) (ev zt) = 𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N))) := by
    rw [← val_stalkHom X₁ z₁ ev, hzt, hyA]
  have hth0 : X₁.S.th x₀ ≠ 0 := by
    intro h0
    apply hθ
    rw [hyK, h0, RatModel.val_zero]
  have hh' : algebraMap V (FractionRing V) (ev h) * 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩ =
      𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ e)) * 𝔪.yK ⟨X₁.S.th (lab c + τ), X₁.S.th_mem (lab c + τ)⟩ := by
    rw [← val_stalkHom X₁ z₁ ev, hyA, hyK, hyK, ← RatModel.val_mul hsp (hO h) (hR _ (X₁.S.th_mem x₀)),
      ← RatModel.val_mul hsp (hR _ (Subalgebra.algebraMap_mem _ _)) (hR _ (X₁.S.th_mem _)), hh,
      div_mul_cancel₀ _ hth0]
  have hterm : ∀ mu : Fin 8 → X, ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) *
      (algebraMap V (FractionRing V) (T mu c) * 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩) =
      algebraMap V (FractionRing V) (ev zt ^ (wt mu).val * T mu c) * 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩ := by
    intro mu
    obtain ⟨a, ha⟩ := hY mu
    rw [hχ a mu ha, ← hwt a mu ha, pow_mul, map_pow, map_pow, ← hzt', map_mul, map_pow]
    ring
  refine TwistSum₂.sumI_of_sumF_mul _ _ _ hθ ?_
  convert hS using 1
  · funext mu
    exact (hterm mu).symm

end GlobalTheory.Poinc.TwistSum₂
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumPointOfSize
section
open GlobalTheory.RefSum GlobalTheory.CovTop GlobalTheory.BigTop

namespace GlobalTheory.RefSum

theorem sumPt_of_size : Size → SumPt := fun h => GlobalTheory.T.sum_point_of_weight_numerical (GlobalTheory.T.weight_point_of_size h) (GlobalTheory.T.numerical_point_of_size h)

end GlobalTheory.RefSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveFunctionFieldModelHomOfProjective
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ProjModelSurj

theorem surjective_of_isProjOver (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (X M : RatModel o Ω) (f : M.Z ⟶ X.Z)
    (hf : X.IsHom M (AlgHom.id o Ω) f) (hM : IsProjOver M.s) : Function.Surjective f := by
  obtain ⟨N, i, hi, hs⟩ := hM
  haveI : IsProper (PSpace.str o N) := isProper_str o N
  haveI : IsProper M.s := hs ▸ inferInstance
  haveI : IsSeparated X.s := X.sep
  haveI : IsProper (f ≫ X.s) := by rw [hf.inducedModelMorphism_comp_structureMap]; infer_instance
  haveI : IsProper f := IsProper.of_comp f X.s
  have hcl : IsClosed (Set.range f) := f.isClosedMap.isClosed_range
  have hgen : genericPoint X.Z ∈ Set.range f := by
    have w : Sp Ω := IsLocalRing.closedPoint Ω
    refine ⟨M.pt w, ?_⟩
    have h : (M.pt ≫ f) w = (spMap (AlgHom.id o Ω).toRingHom ≫ X.pt) w := by rw [hf]
    simp only [Scheme.Hom.comp_apply] at h
    rw [h]
    exact X.pt_apply _
  intro x
  obtain ⟨y, hy⟩ := (genericPoint_specializes x).mem_closed hcl hgen
  exact ⟨y, hy⟩

end GlobalTheory.ProjModelSurj

example : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (X M : RatModel o Ω) (f : M.Z ⟶ X.Z),
    X.IsHom M (AlgHom.id o Ω) f → IsProjOver M.s → Function.Surjective f := GlobalTheory.ProjModelSurj.surjective_of_isProjOver
end

