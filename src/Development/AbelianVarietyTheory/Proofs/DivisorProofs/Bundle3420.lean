import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0506
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3391
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3397
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3410
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3396
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2629
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2640
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2614
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2844
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3058
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2875
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3398
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2559
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2502
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapInverseNatCast
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3409
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2728
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0829
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3386
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3277
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3314
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3399
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3404
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVectorFieldPullbackBaseChangeDerivation
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.FieldBC

theorem isField_mono {Z : Scheme.{0}} {W₀ W₁ : Z.Opens} {d : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)}
    (hd : IsField W₀ d) (h : W₁ ≤ W₀) : IsField W₁ d :=
  ⟨fun W hW => hd.1 W (hW.trans h), fun W hW => hd.2.1 W (hW.trans h),
    fun W W' h' hW => hd.2.2 W W' h' (hW.trans h)⟩

def derivOf {Z : Scheme.{0}} {W₀ : Z.Opens} {d : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)} (hd : IsField W₀ d)
    (V : Z.Opens) (hV : V ≤ W₀) : Derivation ℤ Γ(Z, V) Γ(Z, V) :=
  Derivation.mk' (AddMonoidHom.toIntLinearMap (AddMonoidHom.mk' (d V) (hd.1 V hV)))
    (fun a b => by simp [hd.2.1 V hV a b, smul_eq_mul])

theorem exists_field_of_deriv {Z : Scheme.{0}} (V : Z.Opens) (hV : IsAffineOpen V)
    (δ : Derivation ℤ Γ(Z, V) Γ(Z, V)) :
    ∃ e : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O), IsField V e ∧ ∀ a, e V a = δ a := by
  let σ : Γ(Z, V) →+* DualNumber Γ(Z, V) :=
    { toFun := fun a => TrivSqZeroExt.inl a + TrivSqZeroExt.inr (δ a)
      map_one' := by ext <;> simp
      map_mul' := fun a b => by
        ext
        · simp
        · simp [δ.leibniz, smul_eq_mul]; ring
      map_zero' := by ext <;> simp
      map_add' := fun a b => by ext <;> simp <;> ring }
  obtain ⟨d', hd', hd'v⟩ := GlobalTheory.SpecField.exists_isField Γ(Z, V) σ (fun a => by simp [σ])
  exact GlobalTheory.FieldTransport.exists_isField_transport Z V hV (fun a => δ a) d' hd'
    (fun a => by
      refine (hd'v a).trans ?_
      simp only [σ, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, TrivSqZeroExt.snd_add,
        TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
      rfl)

theorem sec_ext {Z : Scheme.{0}} (V : Z.Opens) (s t : Γ(Z, V))
    (h : ∀ x ∈ V, ∃ V' : Z.Opens, ∃ hV' : V' ≤ V, x ∈ V' ∧ resG Z hV' s = resG Z hV' t) : s = t := by
  refine TopCat.Presheaf.section_ext Z.sheaf V s t fun x hx => ?_
  obtain ⟨V', hV', hx', e⟩ := h x hx
  have := congrArg (Z.presheaf.germ V' x hx').hom e
  simp only [resG, TopCat.Presheaf.germ_res_apply] at this
  exact this

theorem appLE_res {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens) (V V' : X.Opens) (e : V ≤ f ⁻¹ᵁ U)
    (h : V' ≤ V) (r : Γ(Y, U)) :
    resG X h ((f.appLE U V e).hom r) = (f.appLE U V' (h.trans e)).hom r := by
  rw [resG, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

theorem res_appLE {X Y : Scheme.{0}} (f : X ⟶ Y) (U U' : Y.Opens) (V : X.Opens) (h : U' ≤ U)
    (e : V ≤ f ⁻¹ᵁ U') (r : Γ(Y, U)) :
    (f.appLE U' V e).hom (resG Y h r) = (f.appLE U V (e.trans (f.preimage_mono h))).hom r := by
  rw [resG, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

theorem deriv_eq_zero_of_closure {B : Type} [CommRing B] (Δ : Derivation ℤ B B) (S : Set B)
    (hS : Subring.closure S = ⊤) (h : ∀ x ∈ S, Δ x = 0) (x : B) : Δ x = 0 := by
  have hx : x ∈ Subring.closure S := hS ▸ Subring.mem_top x
  induction hx using Subring.closure_induction with
  | mem x hx => exact h x hx
  | zero => simp
  | one => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | neg x _ hx => simp [hx]
  | mul x y _ _ hx hy => simp [Derivation.leibniz, hx, hy]

theorem exists_field_pullback : ∀ (Z Z' X X' : Scheme.{0}) (p : Z ⟶ X) (p' : Z' ⟶ X') (φ : Z' ⟶ Z) (g : X' ⟶ X), IsPullback φ p' p g → ∀ (U : X.affineOpens) (U' : X'.affineOpens) (hU : U'.1 ≤ g ⁻¹ᵁ U.1) (D : Derivation ℤ Γ(X, U.1) Γ(X, U.1)) (D' : Derivation ℤ Γ(X', U'.1) Γ(X', U'.1)), (∀ r, D' ((g.appLE U.1 U'.1 hU).hom r) = (g.appLE U.1 U'.1 hU).hom (D r)) → ∀ (W : Z.Opens) (hW : W ≤ p ⁻¹ᵁ U.1) (d : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)), IsField W d → (∀ r, d W ((p.appLE U.1 W hW).hom r) = (p.appLE U.1 W hW).hom (D r)) → ∃ d' : ∀ O : Z'.Opens, Γ(Z', O) → Γ(Z', O), IsField (φ ⁻¹ᵁ W ⊓ p' ⁻¹ᵁ U'.1) d' ∧ (∀ (O' : Z'.Opens) (h' : O' ≤ p' ⁻¹ᵁ U'.1), O' ≤ φ ⁻¹ᵁ W → ∀ r, d' O' ((p'.appLE U'.1 O' h').hom r) = (p'.appLE U'.1 O' h').hom (D' r)) ∧ ∀ (O : Z.Opens) (O' : Z'.Opens) (h : O' ≤ φ ⁻¹ᵁ O), O ≤ W → O' ≤ p' ⁻¹ᵁ U'.1 → ∀ f, d' O' ((φ.appLE O O' h).hom f) = (φ.appLE O O' h).hom (d O f) := by
  intro Z Z' X X' p p' φ g hpb U U' hU D D' hD' W hW d hd hdD
  classical
  let A := {O : Z.affineOpens // O.1 ≤ W}
  have hOp : ∀ O : A, O.1.1 ≤ p ⁻¹ᵁ U.1 := fun O => O.2.trans hW
  let O' : A → Z'.Opens := fun O => φ ⁻¹ᵁ O.1.1 ⊓ p' ⁻¹ᵁ U'.1
  have hO'aff : ∀ O : A, IsAffineOpen (O' O) := fun O =>
    (GlobalTheory.T.fibreProduct_affineOpen_closure_legs_eq_top Z Z' X X' p p' φ g hpb U U' hU O.1 (hOp O)).1
  have hgen : ∀ O : A, Subring.closure (Set.range (φ.appLE O.1.1 (O' O) inf_le_left).hom ∪
      Set.range (p'.appLE U'.1 (O' O) inf_le_right).hom) = ⊤ := fun O =>
    (GlobalTheory.T.fibreProduct_affineOpen_closure_legs_eq_top Z Z' X X' p p' φ g hpb U U' hU O.1 (hOp O)).2
  let δ : ∀ O : A, Derivation ℤ Γ(Z, O.1.1) Γ(Z, O.1.1) := fun O => derivOf hd O.1.1 O.2
  have hδ : ∀ (O : A) r, δ O ((p.appLE U.1 O.1.1 (hOp O)).hom r) =
      (p.appLE U.1 O.1.1 (hOp O)).hom (D r) := by
    intro O r
    show d O.1.1 _ = _
    rw [← appLE_res p U.1 W O.1.1 hW O.2, hd.2.2 W O.1.1 O.2 le_rfl, hdD, appLE_res]
  choose δ' hδ'1 hδ'2 using fun O : A =>
    GlobalTheory.T.exists_derivation_fibreProduct_affine_compatible Z Z' X X' p p' φ g hpb U U' hU D D' hD' O.1 (hOp O) (δ O) (hδ O)
  choose e he1 he2 using fun O : A => exists_field_of_deriv (O' O) (hO'aff O) (δ' O)

  have hT : ∀ (O : A) (V : Z'.Opens) (hV : V ≤ O' O) (b : Γ(Z, O.1.1)),
      e O V ((φ.appLE O.1.1 V (hV.trans inf_le_left)).hom b) =
        (φ.appLE O.1.1 V (hV.trans inf_le_left)).hom (d O.1.1 b) := by
    intro O V hV b
    rw [← appLE_res φ O.1.1 (O' O) V inf_le_left hV, (he1 O).2.2 (O' O) V hV le_rfl, he2, hδ'2,
      appLE_res]
    rfl
  have hP : ∀ (O : A) (V : Z'.Opens) (hV : V ≤ O' O) (r : Γ(X', U'.1)),
      e O V ((p'.appLE U'.1 V (hV.trans inf_le_right)).hom r) =
        (p'.appLE U'.1 V (hV.trans inf_le_right)).hom (D' r) := by
    intro O V hV r
    rw [← appLE_res p' U'.1 (O' O) V inf_le_right hV, (he1 O).2.2 (O' O) V hV le_rfl, he2, hδ'1,
      appLE_res]

  let bas : (O : A) → Γ(Z, O.1.1) → A := fun O s =>
    ⟨⟨Z.basicOpen s, O.1.2.basicOpen s⟩, (Z.basicOpen_le s).trans O.2⟩
  have hKB : ∀ (O : A) (s : Γ(Z, O.1.1)) (V : Z'.Opens), V ≤ O' (bas O s) → ∀ f,
      e O V f = e (bas O s) V f := by
    intro O s
    have hle : O' (bas O s) ≤ O' O := inf_le_inf_right _ (φ.preimage_mono (Z.basicOpen_le s))
    refine GlobalTheory.T.vectorFields_eq_on_subopens_of_eq_affine Z' (O' (bas O s)) (hO'aff (bas O s)) (e O) (e (bas O s))
      (isField_mono (he1 O) hle) (he1 (bas O s)) ?_
    intro a
    rw [he2 (bas O s)]
    let Δ := derivOf (he1 O) (O' (bas O s)) hle - δ' (bas O s)
    have hΔ : ∀ x, Δ x = e O (O' (bas O s)) x - δ' (bas O s) x := fun x => rfl
    suffices key : ∀ x, Δ x = 0 by
      have := key a
      rwa [hΔ, sub_eq_zero] at this
    refine deriv_eq_zero_of_closure Δ _ (hgen (bas O s)) ?_
    rintro x (⟨c, rfl⟩ | ⟨r, rfl⟩)
    · let ψ := (φ.appLE (Z.basicOpen s) (O' (bas O s)) inf_le_left).hom
      have hres : ∀ b : Γ(Z, O.1.1), Δ (ψ (resG Z (Z.basicOpen_le s) b)) = 0 := by
        intro b
        rw [hΔ, sub_eq_zero]
        show e O (O' (bas O s)) ((φ.appLE (Z.basicOpen s) (O' (bas O s)) inf_le_left).hom
          (resG Z (Z.basicOpen_le s) b)) = δ' (bas O s) ((φ.appLE (Z.basicOpen s) (O' (bas O s)) inf_le_left).hom
          (resG Z (Z.basicOpen_le s) b))
        rw [hδ'2 (bas O s)]
        show _ = (φ.appLE (Z.basicOpen s) (O' (bas O s)) inf_le_left).hom (d (Z.basicOpen s) (resG Z (Z.basicOpen_le s) b))
        rw [res_appLE, hT O _ hle, hd.2.2 O.1.1 (Z.basicOpen s) (Z.basicOpen_le s) O.2, res_appLE]
      haveI := O.1.2.isLocalization_basicOpen s
      obtain ⟨⟨a₀, m⟩, hm⟩ := IsLocalization.surj (Submonoid.powers s) c
      change c * resG Z (Z.basicOpen_le s) m = resG Z (Z.basicOpen_le s) a₀ at hm
      have hunit : IsUnit (ψ (resG Z (Z.basicOpen_le s) m)) := by
        obtain ⟨n, hn⟩ := m.2
        rw [← hn, map_pow]
        exact ((RingedSpace.isUnit_res_basicOpen Z.toRingedSpace s).pow n).map ψ
      have h1 := congrArg (fun y => Δ (ψ y)) hm
      simp only [map_mul, Derivation.leibniz, hres, smul_zero, zero_add, smul_eq_mul, mul_zero] at h1
      exact (hunit.mul_right_eq_zero).1 h1
    · rw [hΔ, sub_eq_zero, hP O _ hle, hδ'1]
  have hcomp : ∀ (O₁ O₂ : A) (V : Z'.Opens), V ≤ O' O₁ → V ≤ O' O₂ → ∀ f, e O₁ V f = e O₂ V f := by
    intro O₁ O₂ V h1 h2 f
    apply sec_ext V
    intro x hx
    have hx1 : φ.base x ∈ O₁.1.1 ⊓ O₂.1.1 := ⟨(h1 hx).1, (h2 hx).1⟩
    obtain ⟨f₁, f₂, hf, hxf⟩ := exists_basicOpen_le_affine_inter O₁.1.2 O₂.1.2 _ hx1
    have hA : bas O₁ f₁ = bas O₂ f₂ := Subtype.ext (Subtype.ext hf)
    have hV1 : V ⊓ O' (bas O₁ f₁) ≤ O' (bas O₁ f₁) := inf_le_right
    have hV2 : V ⊓ O' (bas O₁ f₁) ≤ O' (bas O₂ f₂) := le_of_le_of_eq inf_le_right (congrArg O' hA)
    refine ⟨V ⊓ O' (bas O₁ f₁), inf_le_left, ⟨hx, hxf, (h1 hx).2⟩, ?_⟩
    rw [← (he1 O₁).2.2 V _ inf_le_left h1, ← (he1 O₂).2.2 V _ inf_le_left h2,
      hKB O₁ f₁ _ hV1, hKB O₂ f₂ _ hV2]
    exact congrArg (fun B => e B (V ⊓ O' (bas O₁ f₁)) (resG Z' inf_le_left f)) hA
  obtain ⟨d', hd'1, hd'2⟩ := GlobalTheory.T.exists_vectorField_glued_openCover Z' A O' e he1 hcomp
  have hcov : φ ⁻¹ᵁ W ⊓ p' ⁻¹ᵁ U'.1 ≤ ⨆ O : A, O' O := by
    intro x hx
    obtain ⟨O₀, hO₀, hx0, hle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp Z.isBasis_affineOpens
      (show φ.base x ∈ W from hx.1)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨O₀, hO₀⟩, hle⟩, hx0, hx.2⟩
  refine ⟨d', isField_mono hd'1 hcov, ?_, ?_⟩
  · intro V hV hVW r
    have hVc : V ≤ ⨆ O : A, O' O := (le_inf hVW hV).trans hcov
    apply sec_ext V
    intro x hx
    obtain ⟨O₀, hO₀, hx0, hle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp Z.isBasis_affineOpens
      (show φ.base x ∈ W from hVW hx)
    let B : A := ⟨⟨O₀, hO₀⟩, hle⟩
    refine ⟨V ⊓ O' B, inf_le_left, ⟨hx, hx0, hV hx⟩, ?_⟩
    rw [← hd'1.2.2 V _ inf_le_left hVc, appLE_res, appLE_res, hd'2 B _ inf_le_right,
      hP B _ inf_le_right]
  · intro O V h hOW hV f
    have hVc : V ≤ ⨆ O : A, O' O :=
      (le_inf (h.trans (φ.preimage_mono hOW)) hV).trans hcov
    apply sec_ext V
    intro x hx
    obtain ⟨O₀, hO₀, hx0, hle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp Z.isBasis_affineOpens
      (show φ.base x ∈ O from h hx)
    let B : A := ⟨⟨O₀, hO₀⟩, hle.trans hOW⟩
    refine ⟨V ⊓ O' B, inf_le_left, ⟨hx, hx0, hV hx⟩, ?_⟩
    rw [← hd'1.2.2 V _ inf_le_left hVc, appLE_res, appLE_res, hd'2 B _ inf_le_right,
      ← res_appLE φ O O₀ (V ⊓ O' B) hle (inf_le_right.trans inf_le_left) f,
      hT B _ inf_le_right, hd.2.2 O O₀ hle hOW, res_appLE]

end GlobalTheory.FieldBC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorPairingMumfordBundlePrincipalPolarisation
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem pairing_factor_mumford : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (_ : F.Alg) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (G₁ : Over (Sp R')) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (β : G₁.left ⟶ G.left) (β₂ : (G2 G₁).left ⟶ (G2 G).left) (A₁ : PolAV (Sp (FractionRing R'))) (gen₁ : (Over.pullback (jK R')).obj G₁ ≅ A₁.A), FinExt ρ ∧ IsGrpPullback G₁ G (spMap ρ) β ∧ Geo.Tor.IsSquare β β₂ ∧ IsMonHom gen₁.hom ∧ ExtLam G₁ (A₁.L.pull gen₁.hom.left) (((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left).pull β₂) := by
  intro R _ _ _ hR D D' F hA A' G' _ _ hG' U' oA oG hlin G _ _ hG inc pr hinc hpr hip hpi
  exact GlobalTheory.T.exists_finite_extension_mumford_bundle_polarisation R hR G
    (RetractGeneric.isAbelianScheme_generic R A' G' hG' U'.gen G hG inc pr hinc hpr hip) _
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.pull_isLB (ReciprocityTheory.ChartRestriction.G.Semi.LB.isLB_linComb U'.LG.isLB _ _) _)
    (FactorSym.main R hR D D' F hA A' G' hG' U' oA oG hlin G hG inc pr hinc hpr hip hpi)
    (factorPairing_add R hR D D' F A' G' hG' U' oA oG hlin G hG inc pr hinc hpr hip hpi)
    (factorPairing_diag_relAmple R hR D D' F hA A' G' hG' U' oA oG hlin G hG inc pr hinc hpr hip hpi)
    (pairing_kernel_trivial R hR D D' F hA A' G' hG' U' oA oG hlin G hG inc pr hinc hpr hip hpi)

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibrePullbackAffineFunctionEqQuotientConstStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_pullback_affineFunction_eq_quotientConst : ∀ (X Z : Scheme.{0}) (p : Z ⟶ X) (U : X.affineOpens) (m : Ideal Γ(X, U.1)) (A : Scheme.{0}) (q : A ⟶ Sp (Γ(X, U.1) ⧸ m)) (ι : A ⟶ Z), ι ≫ p = q ≫ spMap (Ideal.Quotient.mk m) ≫ chart U → ∀ (V : Z.Opens) (hV : V ≤ p ⁻¹ᵁ U.1) (V' : A.Opens) (hV' : V' ≤ ι ⁻¹ᵁ V) (r : Γ(X, U.1)), (ι.appLE V V' hV').hom ((p.appLE U.1 V hV).hom r) = (q.appLE ⊤ V' le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U.1) ⧸ m))).inv.hom (Ideal.Quotient.mk m r)) := by
  first | exact @GlobalTheory.fibre_restrict_scalar_compat | exact GlobalTheory.fibre_restrict_scalar_compat | (intros; apply GlobalTheory.fibre_restrict_scalar_compat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupCocycleCoboundaryModPrimeStatement
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalGroupCocycle_coboundary_mod_prime : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (κ : MvPowerSeries (Fin d ⊕ Fin d) O) (B : MvPowerSeries (Fin d) O) (y : G.A 1), constantCoeff κ = 0 → IsCoc c.μ κ → (∀ α, (p : O) ∣ coeff α (cob1 c.μ B - pull2 (nmul c.μ p) κ)) → c.ev 1 B = (p : O) • y → ∃ t : MvPowerSeries (Fin d) O, constantCoeff t = 0 ∧ ∀ α, (p : O) ∣ coeff α (κ - cob1 c.μ t) := by
  first | exact @GlobalTheory.CobModP.coboundary_mod_p | exact GlobalTheory.CobModP.coboundary_mod_p | (intros; apply GlobalTheory.CobModP.coboundary_mod_p <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisPermutesWeightPartsUpToRoots
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.GalPart

open GlobalTheory.UPoinc.USum

section General

open MonObj

variable {o Ω o' Ω' : Type} [CommRing o] [Field Ω] [Algebra o Ω] [CommRing o'] [Field Ω'] [Algebra o' Ω']
  {S : ThetaSys o Ω} {S' : ThetaSys o' Ω'} {ρ : S.Real} {ρ' : S'.Real} {lab : S.Gam → S'.Gam} {φ : Ω →+* Ω'}
  {P₀ : PolAV (Sp Ω')} {a : P₀.A.left ⟶ ρ.P.A.left} {a' : P₀.A.left ⟶ ρ'.P.A.left}

theorem exists_isGenLab_of (h₁ : IsGrpPullback P₀.A ρ.P.A (spMap (φ.comp S.R.val.toRingHom)) a)
    (h₂ : IsGrpPullback P₀.A ρ'.P.A (spMap S'.R.val.toRingHom) a') (l₁ : LBIso P₀.L (ρ.P.L.pull a))
    (l₂ : LBIso P₀.L (ρ'.P.L.pull a'))
    (hpt : ∀ x, ∃ w : Sp Ω' ⟶ P₀.A.left, w ≫ a = spMap (φ.comp S.R.val.toRingHom) ≫ (ρ.pt x).left ∧
      w ≫ a' = spMap S'.R.val.toRingHom ≫ (ρ'.pt (lab x)).left) :
    ∃ x, IsGenLab ρ ρ' lab φ P₀ a a' x ∧ ∀ b b', x (b + b') = x b * x b' := by
  obtain ⟨w, hw, hadd, -⟩ := GalAct.exists_generic_labels ρ' h₂
  obtain ⟨e, he⟩ := GalAct.exists_mulEquiv_points h₁ (𝟙 _) _ (Category.id_comp _)
  have := GalTrans.mono_val S'.R S'.frac
  have : Mono a' := (MorphismProperty.monomorphisms Scheme).of_isPullback h₂.1.flip (.infer_property _)
  refine ⟨fun b => e (w b), ⟨h₁, h₂, l₁, l₂, fun b => ⟨(w b).left, Over.w (w b), (he _).symm, hw b⟩,
    fun k => ?_⟩, fun b b' => by simp only [hadd, map_mul]⟩
  obtain ⟨v, hv, hv'⟩ := hpt k
  obtain rfl : v = (w (lab k)).left := (cancel_mono a').1 (hv'.trans (hw _).symm)
  exact Over.OverMorphism.ext ((he _).trans hv)

variable {x : S'.Gam → (genPt (φ.comp S.R.val.toRingHom) ⟶ ρ.P.A)}

theorem exists_conj_over (hx : IsGenLab ρ ρ' lab φ P₀ a a' x) (σ : Ω' →+* Ω') (hσ : Function.Surjective σ)
    (hφ : σ.comp φ = φ) : ∃ (g : S'.Gam ≃+ S'.Gam)
      (s : genPt (φ.comp S.R.val.toRingHom) ⟶ genPt (φ.comp S.R.val.toRingHom)) (t : P₀.A.left ⟶ P₀.A.left),
      s.left = spMap σ ∧ (∀ b, x (g b) = s ≫ x b) ∧ (∀ k, g (lab k) = lab k) ∧ t ≫ a = a ∧
      IsGrpPullback P₀.A P₀.A (spMap σ) t ∧ LBIso P₀.L (P₀.L.pull t) ∧
      ∀ y (w w' : Sp Ω' ⟶ P₀.A.left), w ≫ a' = spMap S'.R.val.toRingHom ≫ (ρ'.pt y).left →
        w' ≫ t = spMap σ ≫ w → w' ≫ a' = spMap S'.R.val.toRingHom ≫ (ρ'.pt (g y)).left := by
  obtain ⟨h₁, h₂, l₁, l₂, hw, hlab⟩ := hx
  have hs : spMap σ ≫ spMap (φ.comp S.R.val.toRingHom) = spMap (φ.comp S.R.val.toRingHom) :=
    GalTrans.sp_comp (by rw [← RingHom.comp_assoc, hφ])
  obtain ⟨t, ht₁, ht₂⟩ : ∃ t : P₀.A.left ⟶ P₀.A.left, t ≫ a = a ∧ t ≫ P₀.A.hom = P₀.A.hom ≫ spMap σ :=
    ⟨h₁.1.lift a (P₀.A.hom ≫ spMap σ) (by rw [Category.assoc, hs, h₁.1.w]), h₁.1.lift_fst _ _ _, h₁.1.lift_snd _ _ _⟩
  have ht : IsGrpPullback P₀.A P₀.A (spMap σ) t := h₁.cancel (h₁.congr hs.symm ht₁.symm) ht₂
  have lt : LBIso (P₀.L.pull t) (ρ.P.L.pull a) :=
    l₁.chartPull (Geo.Tor.chartPullPull P₀.L t t rfl)
      (chartPullSame ρ.P.L (fun _ => a) (fun _ => a) _ t fun _ => ht₁.symm)
  obtain ⟨g, hg, hg'⟩ := GalAct.exists_label_action ρ' h₂ σ hσ ht
  have := GalTrans.mono_val S'.R S'.frac
  have : Mono a' := (MorphismProperty.monomorphisms Scheme).of_isPullback h₂.1.flip (.infer_property _)
  refine ⟨g, Over.homMk (spMap σ) hs, t, rfl, fun b => Over.OverMorphism.ext ?_, fun k => ?_, ht₁, ht,
    LBIso.trans P₀.isLB (pull_isLB ρ.P.isLB _) (pull_isLB P₀.isLB _) l₁ lt.symm, hg⟩
  · obtain ⟨w, e₀, e₁, e₂⟩ := hw b
    obtain ⟨w', -, e₁', e₂'⟩ := hw (g b)
    have c : (spMap σ ≫ w) ≫ P₀.A.hom = 𝟙 _ ≫ spMap σ := by rw [Category.assoc, e₀]; simp
    have k := ht.1.lift_fst _ _ c
    obtain rfl : w' = ht.1.lift _ _ c := (cancel_mono a').1 (e₂'.trans (hg b w _ e₂ k).symm)
    rw [← e₁', ← ht₁, reassoc_of% k, e₁]
    rfl
  · obtain ⟨w, e₀, e₁, e₂⟩ := hw (lab k)
    refine hg' _ w e₂ (h₁.1.hom_ext ?_ ?_)
    · rw [Category.assoc, Category.assoc, ht₁, e₁, hlab]
      exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hs)).symm
    · rw [Category.assoc, Category.assoc, ht₂, reassoc_of% e₀, e₀, Category.comp_id]

open Classical in

theorem exists_root_conj [ArithBase o Ω] [ArithBase o' Ω'] (hx : IsGenLab ρ ρ' lab φ P₀ a a' x)
    (hadd : ∀ b b', x (b + b') = x b * x b') {m : ℕ} (hm : S'.N = m ^ 2) (H : AddSubgroup S'.Gam) (x₀ : S.Gam)
    (h₀ : S.th x₀ ≠ 0) (h₀' : S'.th (lab x₀) ≠ 0) {κ : S.Gam} {h : S'.Gam} (hh : h ∈ H) (e : m • h = lab κ) :
    ∃ ξ : Ω', (∃ k : ℕ, 0 < k ∧ ξ ^ k = 1) ∧ ∀ (σ : Ω' →+* Ω'), σ.comp φ = φ →
      ∀ (s : genPt (φ.comp S.R.val.toRingHom) ⟶ genPt (φ.comp S.R.val.toRingHom)), s.left = spMap σ →
      ∀ g : S'.Gam ≃+ S'.Gam, (∀ b, x (g b) = s ≫ x b) → (∀ k, g (lab k) = lab k) → (∀ y, g y ∈ H ↔ y ∈ H) →
      ∀ b, σ (ξ * (partV S' H ρ'.i₀ b h / S'.th (lab x₀))) = ξ * (partV S' H ρ'.i₀ (g b) h / S'.th (lab x₀)) := by
  have := Fintype.ofFinite (S'.perp H)
  choose V hV₁ using fun t : S'.perp H => TV.ex hx hadd hm t e
  have hV : ∀ h' ∈ H, m • h' = lab κ → ∀ t : S'.perp H, TV ρ x m t h' κ (V t) := fun h' hh' e' t => by
    have := (hV₁ t).transl hx hadd hm (k := h' - h) (by rw [smul_sub, e, e', sub_self]) (t.2 _ (sub_mem hh' hh))
    rwa [add_sub_cancel] at this
  have hφ₀ : φ (S.th x₀) ≠ 0 := (map_ne_zero φ).2 h₀
  obtain ⟨ξ, hξ, hc⟩ := GlobalTheory.T.twistedThetaValue_eq_root_mul_thetaOperatorValue ρ ρ' lab φ P₀ a a' x hx m hm κ x₀ h e
  have hf : ∀ b, ξ * (partV S' H ρ'.i₀ b h / S'.th (lab x₀)) =
      algebraMap o' Ω' (Ring.inverse (Nat.card (S'.perp H) : o')) *
        (∑ t : S'.perp H, algebraMap o' Ω' (S'.ζN ^ (-(wtChar S' _ b t)).val) * V t) / φ (S.th x₀) := fun b => by
    have hv : ∀ t : S'.perp H, V t =
        (ξ * φ (S.th x₀) / S'.th (lab x₀)) * ∑ j, algebraMap o' Ω' (S'.ρ t j ρ'.i₀) * S'.ev h j := fun t => by
      rw [div_mul_eq_mul_div, eq_div_iff h₀']
      exact hc t _ (hV₁ t)
    simp only [hv, partV_eq, mul_left_comm _ (ξ * φ (S.th x₀) / S'.th (lab x₀)), ← Finset.mul_sum]
    field_simp
  refine ⟨ξ, hξ, fun σ hφ s hs g hg hl hH b => ?_⟩
  have hw := hx.weil_conj σ s hs hg
  have h0 : ∀ y y', eStd S'.g _ y y' = 0 ↔ eStd S'.g _ (g y) (g y') = 0 := fun y y' => by
    rw [← zeta_pow_eq_one_iff, ← zeta_pow_eq_one_iff, ← hw, map_eq_one_iff σ σ.injective]
  have hT : ∀ t, t ∈ S'.perp H ↔ g t ∈ S'.perp H := fun t =>
    ⟨fun ht y hy => by
      obtain ⟨y, rfl⟩ := g.surjective y
      exact (h0 _ _).1 (ht y ((hH y).1 hy)), fun ht y hy => (h0 _ _).2 (ht _ ((hH y).2 hy))⟩
  let e' : S'.perp H ≃ S'.perp H := g.toEquiv.subtypeEquiv hT
  have hζ : ∀ t : S'.perp H, σ (algebraMap o' Ω' (S'.ζN ^ (-(wtChar S' _ b t)).val)) =
      algebraMap o' Ω' (S'.ζN ^ (-(wtChar S' _ (g b) (e' t))).val) := fun t => by
    have e₁ : σ (algebraMap o' Ω' (S'.ζN ^ (wtChar S' _ b t).val)) =
        algebraMap o' Ω' (S'.ζN ^ (wtChar S' _ (g b) (e' t)).val) := by
      refine (congrArg (fun q => σ (algebraMap o' Ω' q)) (zetaN_pow_cast _)).trans
        (Eq.trans ?_ (congrArg (algebraMap o' Ω') (zetaN_pow_cast _)).symm)
      rw [map_pow, map_pow, hw, ← map_pow]
      rfl
    have e₂ := congrArg (fun q => σ (algebraMap o' Ω' q)) (zetaN_neg_mul (wtChar S' _ b t))
    have e₃ := congrArg (algebraMap o' Ω') (zetaN_neg_mul (wtChar S' _ (g b) (e' t)))
    simp only [map_mul, map_one] at e₂ e₃
    rw [e₁] at e₂
    exact (eq_inv_of_mul_eq_one_left e₂).trans (eq_inv_of_mul_eq_one_left e₃).symm
  have hσV : ∀ t : S'.perp H, σ (V t) = V (e' t) := fun t =>
    ((hV₁ t).conj σ s hs g.toAddMonoidHom hg).unique ρ'
      (hV (g h) ((hH h).2 hh) (by rw [← map_nsmul, e, hl]) (e' t))
  rw [hf, hf, map_div₀, map_mul, map_inverse_natCast, map_sum,
    show σ (φ (S.th x₀)) = φ (S.th x₀) from RingHom.congr_fun hφ _,
    ← Equiv.sum_comp e' fun t => algebraMap o' Ω' (S'.ζN ^ (-(wtChar S' _ (g b) t)).val) * V t]
  simp only [map_mul, hζ, hσV]

end General

theorem exists_root_galois : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁) (z₁ : X₁.M.Z) (z₂ : D.X.M.Z), D.q z₂ = z₁ → ∃ U : X₁.S.HH X₁.M z₁ → D.X.Ω₁, (∀ κ, ∃ k : ℕ, 0 < k ∧ U κ ^ k = 1) ∧ ∀ σ : D.X.Ω₁ ≃ₐ[X₁.Ω₁] D.X.Ω₁, ∃ a : D.X.S.Gam ≃+ D.X.S.Gam, D.GalLab σ a ∧ (∀ x, a (D.lab x) = D.lab x) ∧ ((∀ x, a x ∈ D.X.S.HH D.X.M z₂ ↔ x ∈ D.X.S.HH D.X.M z₂) → ∀ b κ, σ (U κ * GSum.part D z₁ z₂ b κ) = U κ * GSum.part D z₁ z₂ (a b) κ) := by
  intro g n F W Z i X₁ hg hn hodd hi hE hT hP ε₁ hε₁ D z₁ z₂ hq
  obtain ⟨P₀, a₁, a₂, ε₀, h₁, h₂, l₁, l₂, hε, hpt⟩ := D.same
  obtain ⟨x, hx, hadd⟩ := exists_isGenLab_of h₁ h₂ l₁ l₂ hpt
  have hb : GSum.base X₁ z₁ ∈ X₁.S.supI X₁.M z₁ := by
    have hne : (X₁.S.supI X₁.M z₁).Nonempty := X₁.div z₁
    rw [GSum.base, dif_pos hne]
    exact hne.some_mem
  have hb' := GlobalTheory.T.thetaSetup_dividingLabel_persists_deeperLevel g n F W Z i X₁ hg hn hodd hi hE hT hP ε₁ hε₁ D z₁ _ hb z₂ hq
  have hl : ∀ κ : X₁.S.Gam, GSum.lift D z₂ κ ∈ D.X.S.HH D.X.M z₂ ∧ ∃ κ', D.m • GSum.lift D z₂ κ = D.lab κ' := fun κ => by
    by_cases h : ∃ h' ∈ D.X.S.HH D.X.M z₂, D.m • h' = D.lab κ
    · rw [GSum.lift, dif_pos h]
      exact ⟨h.choose_spec.1, κ, h.choose_spec.2⟩
    · rw [GSum.lift, dif_neg h]
      exact ⟨zero_mem _, 0, by rw [smul_zero, map_zero]⟩
  choose U hU hσU using fun κ : X₁.S.HH X₁.M z₁ =>
    exists_root_conj hx hadd D.sq (D.X.S.HH D.X.M z₂) _ hb.1 hb'.1 (hl κ).1 (hl κ).2.choose_spec
  refine ⟨U, hU, fun σ => ?_⟩
  have hφ : (σ : D.X.Ω₁ →+* D.X.Ω₁).comp (algebraMap X₁.Ω₁ D.X.Ω₁) = algebraMap X₁.Ω₁ D.X.Ω₁ :=
    RingHom.ext fun y => σ.commutes y
  obtain ⟨a, s, t, hs, ha, hlab, ht₁, ht, lt, hpt'⟩ := exists_conj_over hx (σ : D.X.Ω₁ →+* D.X.Ω₁) σ.surjective hφ
  refine ⟨a, ⟨P₀, a₂, t, ε₀, h₂, ht, l₂, lt, fun E => ⟨(hε E).2, ?_⟩, hpt'⟩, hlab, fun hH b κ => ?_⟩
  · have ht₂ := ht.1.w
    refine h₁.1.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, ht₁, (hε E).1, ← Category.assoc, ht₁]
    · rw [Category.assoc, Category.assoc, ht₂, Over.w (ε₀ E), ← Category.assoc, Over.w (ε₀ E), ht₂]
  · have key := hσU κ _ hφ s hs a ha hlab hH (D.m • b)
    rw [map_nsmul] at key
    exact key

end GlobalTheory.Poinc.GalPart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisTransportTorsionLabelsThetaSetup
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

theorem galTransport : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁) (σ : D.X.Ω₁ ≃ₐ[X₁.Ω₁] D.X.Ω₁) (s : D.X.M.Z ⟶ D.X.M.Z), D.X.M.pt ≫ s = spMap (σ : D.X.Ω₁ →+* D.X.Ω₁) ≫ D.X.M.pt → ∃ a : D.X.S.Gam ≃+ D.X.S.Gam, (∀ x, a (D.lab x) = D.lab x) ∧ ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (c : CTrait X₁ p z₁) (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y) (h' : (y ≫ s) ≫ D.q = c.y) (yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab D.X D.ε (D.lift c y h) yy → IsLab D.X D.ε (D.lift c (y ≫ s) h') (yy.comp a.toAddMonoidHom) := by
  intro g n F W Z i X₁ hg hn ho hi he ht hp ε₁ hd D σ s hs
  obtain ⟨a, hG, hfix⟩ := GlobalTheory.T.galois_automorphism_acts_on_deeper_level_labels g n F W Z i X₁ hg hn ho hi he ht hp ε₁ hd D σ
  exact ⟨a, hfix, fun p _ z₁ c y h h' yy hL =>
    GlobalTheory.T.thetaSetup_labelling_transport_galoisConjugate g n F W Z i X₁ hg hn ho hi he ht hp ε₁ hd D σ s hs a hG p z₁ c y h h' yy hL⟩

end GlobalTheory.Poinc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericStatementOfCanonicalExtensionStatement
section
open GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_statement_of_canonical_extension : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.CanonicalExtensionRankOne → GlobalTheory.Published.DeRhamCanonicalExtension → GenSt := by
  first | exact @GlobalTheory.FlatModel.genSt_of_hypotheses | exact GlobalTheory.FlatModel.genSt_of_hypotheses | (intros; apply GlobalTheory.FlatModel.genSt_of_hypotheses <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodChernWeil
section
namespace GlobalTheory.GoodMetric

theorem goodChernWeil : GlobalTheory.Published.GoodChernWeil :=
  goodChernWeil_of_goodTopChernForm GlobalTheory.T.goodMetric_topChernForm_integral_eq_smooth GlobalTheory.T.chernNumbers_eq_integral_chernForms_smoothMetric GlobalTheory.T.fullFlagBundle_pushForward_formula

end GlobalTheory.GoodMetric
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorsRelatedFourierTermImagesStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heatOperators_related_fourierTerm_images : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (dd : Fin n → Fld Y.H.left) (D : R → R), (∀ a, IsField ⊤ (dd a)) → ∀ (h h' : Heat Y.H Y.q.left Q.P.L dd D), IsBasic Y h → IsBasic Y h' → ∀ (k : ℕ) (α : Q.X) (C : R), (∀ (i : h.J) (i' : h'.J) (V : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ h.W i ⊓ h'.W i' → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V) f → op Y.H dd h.Θ h.u (h.d i) (h.p i) (h.p' i) k (Y.q.left ⁻¹ᵁ V) (pbT Y.q.left (Q.P.L.g (h.j i) (h'.j i')).val (Y.q.left ⁻¹ᵁ V) ^ k * f) = pbT Y.q.left (Q.P.L.g (h.j i) (h'.j i')).val (Y.q.left ⁻¹ᵁ V) ^ k * (op Y.H dd h'.Θ h'.u (h'.d i') (h'.p i') (h'.p' i') k (Y.q.left ⁻¹ᵁ V) f + constFn Y.H.hom _ C * f)) → ∀ (τ₁ τ₁' τ₂ τ₂'' : SecM Y.q.left Q.P.L k), (∀ (y : Y.H.left) J, Good Q.P.L y J → sval τ₁ (𝟙 Y.H.left) y J = sval τ₂ (𝟙 Y.H.left) y J) → (∀ (j : Q.P.L.ι) (V : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ Y.q.left ⁻¹ᵁ Q.P.L.U j → IsWt Y α (Y.q.left ⁻¹ᵁ V) (rsT (τ₂.f fun _ => j) (Y.q.left ⁻¹ᵁ V))) → h.Acts k τ₁ τ₁' → h'.Acts k τ₂ τ₂'' → ∀ (y : Y.H.left) J, Good Q.P.L y J → sval τ₁' (𝟙 Y.H.left) y J = sval τ₂'' (𝟙 Y.H.left) y J + gs (𝟙 _) y ⊤ (scal Y.H.hom C) * sval τ₂ (𝟙 Y.H.left) y J := by
  first | exact @GlobalTheory.HeatUniq.FourierChart.images_eq | exact GlobalTheory.HeatUniq.FourierChart.images_eq | (intros; apply GlobalTheory.HeatUniq.FourierChart.images_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedHeightPowEqDegreeLogCardFiniteFieldStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedHeight_pow_eq_degree_log_card_finiteField : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k), IsAmb p → ∀ (m : ℕ) T, IsMix p m T → ∀ (N : HermLB p) (d : ℕ), d ≤ m → ∀ (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] (κ : Type) [Field κ] [Finite κ] [Algebra κ Γ(Z, ⊤)], topologicalKrullDim Z = d → T d (fun _ => N) (i (genericPoint Z)) = topSelfIntersection κ (N.B.pull i) d * Real.log (Nat.card κ) := by
  first | exact @GlobalTheory.MixHtVert.mixHt_pow_eq_topSelf | exact GlobalTheory.MixHtVert.mixHt_pow_eq_topSelf | (intros; apply GlobalTheory.MixHtVert.mixHt_pow_eq_topSelf <;> assumption)
end

