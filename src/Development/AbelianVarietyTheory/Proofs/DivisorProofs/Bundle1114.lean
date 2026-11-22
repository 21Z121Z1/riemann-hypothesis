import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1084
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0019
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0004
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0921
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0887
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0910
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0129
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1072
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsMulCommutativeCentRealUJ
import Formalism.RealPlaceAnalysis.SmoothOnGVIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicAdelicFormOfBoundedSection
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreDimensionLe
section
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj

namespace GlobalTheory.GenFibreDim

section

attribute [local instance low] specializationOrder

theorem le_height_of_specializingMap {X Z : Type*} [TopologicalSpace X] [TopologicalSpace Z]
    [T0Space X] [T0Space Z] {f : X → Z} (hf : SpecializingMap f) (n : ℕ) :
    ∀ y : X, (n : ℕ∞) ≤ Order.height (f y) → (n : ℕ∞) ≤ Order.height y := by
  induction n with
  | zero => intro y _; simp
  | succ n ih =>
    intro y hy
    have hex : ∃ b < f y, (n : ℕ∞) ≤ Order.height b := by
      by_contra hne
      push_neg at hne
      have h1 : Order.height (f y) ≤ n := by
        rw [Order.height_eq_iSup_lt_height]
        exact iSup₂_le fun b hb => Order.add_one_le_of_lt (hne b hb)
      have h2 : ((n + 1 : ℕ) : ℕ∞) ≤ n := hy.trans h1
      have h3 : n + 1 ≤ n := by exact_mod_cast h2
      omega
    obtain ⟨b, hb, hnb⟩ := hex
    obtain ⟨y', hyy', rfl⟩ := hf hb.le
    have hlt : y' < y := lt_of_le_of_ne hyy' (fun h => hb.ne (by rw [h]))
    have h4 := Order.height_add_one_le hlt
    have h5 := ih y' hnb
    calc ((n + 1 : ℕ) : ℕ∞) = (n : ℕ∞) + 1 := by push_cast; rfl
      _ ≤ Order.height y' + 1 := by gcongr
      _ ≤ Order.height y := h4

theorem topologicalKrullDim_genericFibre_le : ∀ (B Y : Scheme.{0}) [IsIntegral B] (d e : ℕ),
    topologicalKrullDim B = (d : ℕ) → topologicalKrullDim Y ≤ (d + e : ℕ) →
    ∀ (f : Y ⟶ B) [UniversallyClosed f] (G : Scheme.{0}) (j : G ⟶ Y) (s : G ⟶ Sp B.functionField),
    IsPullback j s f (B.fromSpecStalk (genericPoint B)) → topologicalKrullDim G ≤ (e : ℕ) := by
  intro B Y _ d e hB hY f _ G j s h
  have hpre : IsPreimmersion j :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) h.flip inferInstance
  have hinj : Function.Injective j := (IsPreimmersion.isEmbedding j).injective
  have hm : StrictMono (j : G → Y) := fun a b hab =>
    lt_of_le_of_ne (Specializes.map hab.le j.continuous) (hinj.ne hab.ne)
  have hfj : ∀ x : G, f (j x) = genericPoint B := by
    intro x
    have e1 : f (j x) = (B.fromSpecStalk (genericPoint B)) (s x) := by
      rw [← Scheme.Hom.comp_apply, h.w, Scheme.Hom.comp_apply]
    have e2 : (B.fromSpecStalk (genericPoint B)) (s x) ⤳ genericPoint B := by
      have : (B.fromSpecStalk (genericPoint B)) (s x) ∈
          Set.range (B.fromSpecStalk (genericPoint B)) := ⟨_, rfl⟩
      rwa [Scheme.range_fromSpecStalk] at this
    rw [e1]
    exact (e2.antisymm (genericPoint_specializes _)).eq
  have eB : Order.krullDim B = (d : WithBot ℕ∞) := by
    rw [← hB]; exact (Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := B))).symm
  have eY : topologicalKrullDim Y = Order.krullDim Y :=
    Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := Y))
  have eG : topologicalKrullDim G = Order.krullDim G :=
    Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := G))

  have hη : (d : ℕ∞) ≤ Order.height (genericPoint B) := by
    rw [Order.krullDim_eq_iSup_height_of_nonempty] at eB
    have : (⨆ b : B, Order.height b) = (d : ℕ∞) := by exact_mod_cast eB
    rw [← this]
    exact iSup_le fun b => Order.height_mono (genericPoint_specializes b)
  have hsp : SpecializingMap f := f.isClosedMap.specializingMap
  rw [eG]
  rcases isEmpty_or_nonempty G with _ | _
  · simp [Order.krullDim_eq_bot]
  haveI : Nonempty Y := Nonempty.map j inferInstance
  rw [eY, Order.krullDim_eq_iSup_height_add_coheight_of_nonempty] at hY
  have hY' : (⨆ y : Y, Order.height y + Order.coheight y) ≤ ((d + e : ℕ) : ℕ∞) := by
    exact_mod_cast hY
  rw [Order.krullDim_eq_iSup_coheight_of_nonempty]
  have : (⨆ x : G, Order.coheight x) ≤ (e : ℕ∞) := by
    refine iSup_le fun x => ?_
    have h1 : (d : ℕ∞) ≤ Order.height (j x) :=
      le_height_of_specializingMap hsp d (j x) (by rw [hfj x]; exact hη)
    have h2 := Order.coheight_le_coheight_apply_of_strictMono _ hm x
    have h3 : Order.height (j x) + Order.coheight (j x) ≤ ((d + e : ℕ) : ℕ∞) :=
      (le_iSup (fun y : Y => Order.height y + Order.coheight y) (j x)).trans hY'
    have h4 : (d : ℕ∞) + Order.coheight x ≤ (d : ℕ∞) + (e : ℕ∞) := by
      push_cast at h3
      exact (add_le_add h1 h2).trans h3
    exact (WithTop.add_le_add_iff_left (ENat.coe_ne_top d)).1 h4
  exact_mod_cast this

end

end GlobalTheory.GenFibreDim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibrePreimmersionIntegral
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
  ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj

namespace GlobalTheory.GenericFibreGeom

theorem isIso_stalkMap_of_flat_of_isPreimmersion {X Y : Scheme.{0}} (j : X ⟶ Y) [IsPreimmersion j]
    [Flat j] (x : X) : IsIso (j.stalkMap x) := by
  have hs : SurjectiveOnStalks j := inferInstance
  refine (ConcreteCategory.isIso_iff_bijective _).mpr ⟨?_, j.stalkMap_surjective x⟩
  have hl : IsLocalHom (j.stalkMap x).hom := inferInstance
  have h := Flat.stalkMap j x
  algebraize [(j.stalkMap x).hom]
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (j x)) (X.presheaf.stalk x)) := hl
  have := Module.FaithfullyFlat.of_flat_of_isLocalHom
    (A := Y.presheaf.stalk (j x)) (B := X.presheaf.stalk x)
  exact FaithfulSMul.algebraMap_injective _ _

theorem setOf_specializes_genericPoint (B : Scheme.{0}) [IsIntegral B] :
    {y : B | y ⤳ genericPoint B} = {genericPoint B} := by
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  exact ⟨fun hy => (hy.antisymm ((genericPoint_spec B).specializes (Set.mem_univ y))).eq,
    fun hy => hy ▸ specializes_rfl⟩

theorem range_of_isPullback {P X Y Z : Scheme.{0}} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z}
    {g : Y ⟶ Z} (h : IsPullback fst snd f g) : Set.range fst = f ⁻¹' Set.range g := by
  rw [← Scheme.Pullback.range_fst f g]
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨h.isoPullback.hom x, by rw [← Scheme.Hom.comp_apply, h.isoPullback_hom_fst]⟩
  · rintro ⟨z, rfl⟩
    refine ⟨h.isoPullback.inv z, ?_⟩
    rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_fst]

theorem genericFibre_props : ∀ (B Y : Scheme.{0}) [IsIntegral B] (f : Y ⟶ B) (G : Scheme.{0}) (j : G ⟶ Y) (s : G ⟶ Sp B.functionField), IsPullback j s f (B.fromSpecStalk (genericPoint B)) → IsPreimmersion j ∧ Set.range j = f ⁻¹' {genericPoint B} ∧ (∀ x : G, IsIso (j.stalkMap x)) ∧ ∀ [IsIntegral Y], Nonempty G → ∃ _ : IsIntegral G, j (genericPoint G) = genericPoint Y := by
  intro B Y _ f G j s h
  have hι : Flat (B.fromSpecStalk (genericPoint B)) :=
    GlobalTheory.LocalRingGeneralisation.flat_fromSpecStalk B _
  have hj : IsPreimmersion j :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) h.flip inferInstance
  have hjf : Flat j := MorphismProperty.of_isPullback (P := @Flat) h.flip hι
  have hr : Set.range j = f ⁻¹' {genericPoint B} := by
    rw [range_of_isPullback h, Scheme.range_fromSpecStalk, setOf_specializes_genericPoint]
  have hiso : ∀ x : G, IsIso (j.stalkMap x) := fun x => isIso_stalkMap_of_flat_of_isPreimmersion j x
  refine ⟨hj, hr, hiso, ?_⟩
  intro _ hne
  obtain ⟨x₀⟩ := hne

  have hfx : f (j x₀) = genericPoint B := by
    have : j x₀ ∈ Set.range j := ⟨x₀, rfl⟩
    rw [hr] at this
    exact this
  have h1 : f (genericPoint Y) ⤳ genericPoint B := by
    rw [← hfx]
    exact ((genericPoint_spec Y).specializes (Set.mem_univ _)).map f.continuous
  have h2 : f (genericPoint Y) = genericPoint B :=
    (h1.antisymm ((genericPoint_spec B).specializes (Set.mem_univ _))).eq
  obtain ⟨ξ, hξ⟩ : genericPoint Y ∈ Set.range j := by rw [hr]; exact h2
  have hemb := IsPreimmersion.isEmbedding j
  have hgen : IsGenericPoint ξ (⊤ : Set G) := by
    rw [isGenericPoint_iff_specializes]
    intro x
    simp only [Set.top_eq_univ, Set.mem_univ, iff_true]
    rw [← hemb.isInducing.specializes_iff, hξ]
    exact (genericPoint_spec Y).specializes (Set.mem_univ _)
  have hirr : IrreducibleSpace G := (irreducibleSpace_def G).2 hgen.isIrreducible
  have hred : ∀ x : G, _root_.IsReduced (G.presheaf.stalk x) := fun x => by
    have := hiso x
    exact isReduced_of_injective (inv (j.stalkMap x)).hom
      (ConcreteCategory.bijective_of_isIso (inv (j.stalkMap x))).1
  have : AlgebraicGeometry.IsReduced G := isReduced_of_isReduced_stalk G
  have hint : IsIntegral G := isIntegral_of_irreducibleSpace_of_isReduced G
  refine ⟨hint, ?_⟩
  rw [← hξ]
  congr 1
  exact (genericPoint_spec G).eq hgen

end GlobalTheory.GenericFibreGeom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlActionQuadraticRelationModuloPiTensorAtFactor
section
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR.TensQuad

variable {T : Type} [Fintype T] [DecidableEq T] {V : T → Type} [∀ w, AddCommGroup (V w)] [∀ w, Module ℂ (V w)]

theorem atPl_tprod (w : T) (L : Module.End ℂ (V w)) (f : ∀ i, V i) :
    atPl w L (PiTensorProduct.tprod ℂ f) = PiTensorProduct.tprod ℂ (Function.update f w (L (f w))) := by
  rw [atPl, PiTensorProduct.map_tprod]
  congr 1
  funext i
  rcases eq_or_ne i w with rfl | h
  · simp
  · simp [Function.update_of_ne h]

noncomputable def atPlLin (w : T) : Module.End ℂ (V w) →ₗ[ℂ] Module.End ℂ (⨂[ℂ] i, V i) :=
  (PiTensorProduct.mapMultilinear ℂ V V).toLinearMap (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) w

theorem atPlLin_apply (w : T) (L : Module.End ℂ (V w)) : atPlLin w L = atPl w L := rfl

theorem atPl_mul (w : T) (L₁ L₂ : Module.End ℂ (V w)) : atPl w (L₁ * L₂) = atPl w L₁ * atPl w L₂ := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro f
  simp [atPl_tprod, Module.End.mul_apply]

theorem atPl_one (w : T) : atPl w (1 : Module.End ℂ (V w)) = 1 := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro f
  simp [atPl_tprod]

theorem qop_atPl {ι : Type} [Fintype ι] [DecidableEq ι] (w : T) (F : ι → ι → Module.End ℂ (V w)) (α β : ℂ) (i j : ι) :
    qop (fun a b => atPl w (F a b)) α β i j = atPl w (qop F α β i j) := by
  simp only [qop, ← atPlLin_apply, map_sub, map_sum, map_smul, apply_ite (atPlLin w), map_zero]
  simp only [atPlLin_apply, atPl_mul, atPl_one]

theorem mem_of_atPl (C : ∀ w, Submodule ℂ (V w)) (w : T) (L : Module.End ℂ (V w)) (hL : ∀ x, L x ∈ C w)
    (v : ⨂[ℂ] i, V i) : atPl w L v ∈ tensAny C := by
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    rw [map_smul, atPl_tprod]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ⟨w, by simpa using hL (f w)⟩, rfl⟩)
  | add x y hx hy =>
    rw [map_add]
    exact add_mem hx hy

end GlobalTheory.HoweR.TensQuad

open GlobalTheory.HoweR.TensQuad in
theorem GlobalTheory.HoweR.quadMod_actAt : ∀ (T : Type) [Fintype T] [DecidableEq T] (V : T → Type) [∀ w, AddCommGroup (V w)] [∀ w, Module ℂ (V w)], ∀ (C : ∀ w, Submodule ℂ (V w)) (w : T) (p q : ℕ) (a : Mat p q →ₗ[ℂ] Module.End ℂ (V w)) (α β α' β' : ℂ), QuadMod a α β α' β' (C w) ⊤ → QuadMod (actAt w a) α β α' β' (tensAny C) ⊤ := by
  intro T _ _ V _ _ C w p q a α β α' β' h i j v _
  have hu : units (actAt w a) = fun i j => atPl w (units a i j) := rfl
  have hn : negT (units (actAt w a)) = fun i j => atPl w (negT (units a) i j) := by
    funext i j
    simp only [negT, units, actAt_apply, ← atPlLin_apply, map_neg]
  refine ⟨?_, ?_⟩
  · rw [hu, qop_atPl]
    exact mem_of_atPl C w _ (fun x => (h i j x Submodule.mem_top).1) v
  · rw [hn, qop_atPl]
    exact mem_of_atPl C w _ (fun x => (h i j x Submodule.mem_top).2) v
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodPartFullEqKilled
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.CuspMult.CutFull

open GlobalTheory.CuspMult GlobalTheory.CuspMult.EqCut

theorem mem_killed_union {H X : Type} [Group H] [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ H X)
    (I I' : Set (MonoidAlgebra ℂ H)) (v : X) : v ∈ killed ρ (I ∪ I') ↔ v ∈ killed ρ I ∧ v ∈ killed ρ I' := by
  simp only [mem_killed, Set.mem_union, or_imp, forall_and]

theorem mem_partFull_iff {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}
    (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ)
    (SF : Finset (HeightOneSpectrum (𝓞 D.host.F))) (a : Pl D.host.E → List ℤ → ℂ) (T : MMap M) :
    T ∈ partFull θ M J χ SF a ↔ T ∈ Mult θ M J χ ∧ ∀ Q d R, Hecke₂ V J χ SF Q d R →
      ∀ v x, ∑ γ ∈ R, T v (x * γ) = a Q d * T v x := by
  unfold partFull
  simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero,
    MultilinearMap.ext_iff, funext_iff]
  rfl

theorem good_partFull_eq_killed : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) {G : Type} [Group G] [Fintype G] (eG : G ≃* G0 L.Pg L.r) (c : G → ℂ) (P : LevelP L.Pg L.r ℂ) (SF : Finset (HeightOneSpectrum (𝓞 D.host.F))) (a : Pl D.host.E → List ℤ → ℂ), L.s = 0 → L.Q = ∅ → LiftsExist V β L → goodPart θ M (levS V β (withP L P)) (levChi V β (withP L P)) (gaL V β L eG c) ⊓ partFull θ M (levS V β (withP L (LevelP.triv L.Pg L.r ℂ))) (levChi V β (withP L (LevelP.triv L.Pg L.r ℂ))) SF a = GlobalTheory.CuspMult.allMaps θ M ⊓ GlobalTheory.CuspMult.killed (GlobalTheory.CuspMult.finRep M) (GlobalTheory.CuspMult.eqSet V β L eG c P (∅ : Set Empty) Empty.elim Empty.elim Empty.elim ∪ {x | ∃ (Q : Pl D.host.E) (d : List ℤ) (B : Finset (GfC V)), Hecke₂ V (levS V β (withP L (LevelP.triv L.Pg L.r ℂ))) (levChi V β (withP L (LevelP.triv L.Pg L.r ℂ))) SF Q d (B.map ⟨Subtype.val, Subtype.val_injective⟩) ∧ x = ∑ γ ∈ B, MonoidAlgebra.single γ 1 - MonoidAlgebra.single 1 (a Q d)}) := by
  intro D V S θ M β L G _ _ eG c P SF a hs hQ hlift
  have h0 := good_hecke_eq_killed θ M β L eG c P (∅ : Set Empty) Empty.elim Empty.elim Empty.elim hs hQ hlift
  have h1 : ∀ T : MMap M, T ∈ goodPart θ M (levS V β (withP L P)) (levChi V β (withP L P)) (gaL V β L eG c) ↔
      T ∈ allMaps θ M ∧ T ∈ killed (finRep M) (eqSet V β L eG c P (∅ : Set Empty) Empty.elim Empty.elim Empty.elim) := by
    intro T
    rw [← Submodule.mem_inf, ← h0, Submodule.mem_inf, mem_hPart]
    exact ⟨fun h => ⟨h, fun p => p.elim⟩, fun h => h.1⟩
  ext T
  rw [Submodule.mem_inf, Submodule.mem_inf, mem_killed_union, ← and_assoc, ← h1, mem_partFull_iff]
  refine and_congr_right fun hg => ?_
  rw [mem_killed]
  constructor
  · rintro ⟨-, hh⟩ x ⟨Q, d, B, hB, rfl⟩
    refine (alg_sum M B (fun γ => γ) (fun _ => 1) _ T).2 fun v x => ?_
    have := hh Q d _ hB v x
    rw [Finset.sum_map] at this
    simp only [one_mul]
    exact this
  · intro hk
    have hm := (GlobalTheory.MultMem.mem_mult_iff D θ V S M _ _ T).1 hg.1
    refine ⟨(GlobalTheory.MultMem.mem_mult_iff D θ V S M _ _ T).2 ⟨hm.aut, hm.cusp, fun v k hkk x => ?_, hm.equiv, hm.cont⟩, ?_⟩
    · exact hasType_flag1 P (F := T v) (fun k hk h => hm.lev v k hk h) k hkk x
    · intro Q d R hR v x
      classical
      have hf : ∀ γ ∈ R, γ ∈ GfC V := by
        obtain ⟨e, f, ϖ, α, -, -, -, -, -, -, -, -, -, -, h⟩ := hR
        exact fun γ hγ => (h.1 γ hγ).1
      obtain ⟨B, rfl⟩ : ∃ B : Finset (GfC V), B.map ⟨Subtype.val, Subtype.val_injective⟩ = R :=
        ⟨R.subtype (· ∈ GfC V), Finset.subtype_map_of_mem hf⟩
      have := (alg_sum M B (fun γ => γ) (fun _ => 1) _ T).1 (hk _ ⟨Q, d, B, hR, rfl⟩) v x
      simp only [one_mul] at this
      rw [Finset.sum_map]
      exact this

end GlobalTheory.CuspMult.CutFull

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtHeisenbergOperatorThetaTransformRealLi
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical

noncomputable section

namespace GlobalTheory.ThetaDeriv

theorem decay_majorant {F : Type} [Field F] [NumberField F] {N : ℕ} (hF : IsTotallyReal F)
    {Φ : (Fin N → AF F) → ℂ} (hΦ : Decay Φ) (ω : Set (Fin N → AF F)) (hω : IsCompact ω) :
    ∃ C : ℝ, ∃ c : (Fin N → F) → ℝ, Summable c ∧ (∀ ξ, 0 ≤ c ξ) ∧
      ∀ ξ, ∀ y ∈ ω, ‖Φ (rat ξ + y)‖ ≤ C * c ξ := by
  obtain ⟨-, ⟨K, hK, hKz⟩, hdec⟩ := hΦ
  obtain ⟨k, hk⟩ := GlobalTheory.SumMaj.summable_majorant F N hF K hK
  obtain ⟨C, hC⟩ := hdec k
  have hC0 : 0 ≤ C :=
    le_trans (mul_nonneg (norm_nonneg _) (pow_nonneg (by linarith [GlobalTheory.SumMaj.sz_nonneg (0 : Fin N → AF F)]) k))
      (hC 0)
  obtain ⟨c, hcs, hc0, hcb⟩ := hk ω hω
  refine ⟨C, c, hcs, hc0, fun ξ y hy => ?_⟩
  by_cases hmem : fin (rat ξ + y) ∈ K
  · have h1 := hcb ξ y hy hmem
    have h2 := hC (rat ξ + y)
    calc ‖Φ (rat ξ + y)‖ = ‖Φ (rat ξ + y)‖ * 1 := (mul_one _).symm
      _ ≤ ‖Φ (rat ξ + y)‖ * (c ξ * (1 + sz (rat ξ + y)) ^ k) :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = c ξ * (‖Φ (rat ξ + y)‖ * (1 + sz (rat ξ + y)) ^ k) := by ring
      _ ≤ c ξ * C := mul_le_mul_of_nonneg_left h2 (hc0 ξ)
      _ = C * c ξ := mul_comm _ _
  · rw [hKz _ hmem, norm_zero]
    exact mul_nonneg hC0 (hc0 ξ)

variable {F : Type} [Field F] [NumberField F] {N : ℕ} [Invertible (2 : AF F)]

theorem schr_line_add (hF : IsTotallyReal F) (ψ : AddChar (AF F) ℂ) {M : ℝ →+ VA F N} (hM : IsRealLine M)
    (t h : ℝ) (Φ : (Fin N → AF F) → ℂ) :
    GlobalTheory.WeilM.schr ψ (M (t + h)) Φ = GlobalTheory.WeilM.schr ψ (M t) (GlobalTheory.WeilM.schr ψ (M h) Φ) := by
  rw [schr_schr, GlobalTheory.T.adelicSymplecticForm_realOneParamLine_eq_zero F N hF M hM t h, mul_zero, AddChar.map_zero_eq_one, one_smul, map_add]

theorem exists_deriv_schr (hF : IsTotallyReal F) (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ)
    {M : ℝ →+ VA F N} (hM : IsRealLine M) {Φ : (Fin N → AF F) → ℂ} (hΦ : Φ ∈ GlobalTheory.WeilM.schA F (Fin N)) :
    ∃ Φ' ∈ GlobalTheory.WeilM.schA F (Fin N), ∀ z, HasDerivAt (fun s : ℝ => GlobalTheory.WeilM.schr ψ (M s) Φ z) (Φ' z) 0 := by
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    obtain ⟨f', hf'⟩ := GlobalTheory.T.hasDerivAt_schrodingerLine_pureTensor_zero F N ψ hF hψ M hM f g hg
    exact ⟨_, Submodule.subset_span ⟨f', g, hg, rfl⟩, hf'⟩
  | zero =>
    refine ⟨0, zero_mem _, fun z => ?_⟩
    have e : (fun s : ℝ => GlobalTheory.WeilM.schr ψ (M s) (0 : (Fin N → AF F) → ℂ) z) = fun _ => 0 := by
      funext s; simp [GlobalTheory.WeilM.schr]
    rw [e]
    exact hasDerivAt_const 0 0
  | add Φ Ψ _ _ h1 h2 =>
    obtain ⟨Φ', h1m, h1d⟩ := h1
    obtain ⟨Ψ', h2m, h2d⟩ := h2
    refine ⟨Φ' + Ψ', add_mem h1m h2m, fun z => ?_⟩
    have e : (fun s : ℝ => GlobalTheory.WeilM.schr ψ (M s) (Φ + Ψ) z) =
        fun s => GlobalTheory.WeilM.schr ψ (M s) Φ z + GlobalTheory.WeilM.schr ψ (M s) Ψ z := by
      funext s; simp [GlobalTheory.WeilM.schr, mul_add]
    rw [e]
    exact (h1d z).add (h2d z)
  | smul c Φ _ h =>
    obtain ⟨Φ', hm, hd⟩ := h
    refine ⟨c • Φ', Submodule.smul_mem _ c hm, fun z => ?_⟩
    have e : (fun s : ℝ => GlobalTheory.WeilM.schr ψ (M s) (c • Φ) z) = fun s => c * GlobalTheory.WeilM.schr ψ (M s) Φ z := by
      funext s; simp [GlobalTheory.WeilM.schr]; ring
    rw [e]
    exact (hd z).const_mul c

theorem hasDerivAt_schr (hF : IsTotallyReal F) (ψ : AddChar (AF F) ℂ) {M : ℝ →+ VA F N} (hM : IsRealLine M)
    {Φ Φ' : (Fin N → AF F) → ℂ} (hd : ∀ z, HasDerivAt (fun s : ℝ => GlobalTheory.WeilM.schr ψ (M s) Φ z) (Φ' z) 0)
    (z : Fin N → AF F) (t : ℝ) :
    HasDerivAt (fun s : ℝ => GlobalTheory.WeilM.schr ψ (M s) Φ z) (GlobalTheory.WeilM.schr ψ (M t) Φ' z) t := by
  have h1 : HasDerivAt (fun h : ℝ => GlobalTheory.WeilM.schr ψ (M (t + h)) Φ z) (GlobalTheory.WeilM.schr ψ (M t) Φ' z) (t - t) := by
    have e : (fun h : ℝ => GlobalTheory.WeilM.schr ψ (M (t + h)) Φ z) = fun h =>
        ψ (z ⬝ᵥ (M t).2 + ⅟(2 : AF F) * ((M t).1 ⬝ᵥ (M t).2)) * GlobalTheory.WeilM.schr ψ (M h) Φ (z + (M t).1) := by
      funext h
      rw [schr_line_add hF ψ hM]
      rfl
    rw [e, sub_self]
    exact (hd (z + (M t).1)).const_mul _
  have h2 := h1.comp_sub_const t t
  simpa only [add_sub_cancel] using h2

end GlobalTheory.ThetaDeriv

open GlobalTheory.ThetaDeriv in

theorem GlobalTheory.ThetaTransform.hasDerivAt_heisV_line : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) [Invertible (2 : AF F)]
    (ψ : AddChar (AF F) ℂ), IsTotallyReal F → IsCharAF F ψ → ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin N),
    ∀ M : ℝ →+ VA F N, IsRealLine M → ∃ Φ' ∈ GlobalTheory.WeilM.schA F (Fin N),
      ∀ w, HasDerivAt (fun t : ℝ => heisV ψ (M t) (thV ψ Φ) w) (thV ψ Φ' w) 0 := by
  intro F _ _ N _ ψ hF hψ Φ hΦ M hM
  obtain ⟨Φ', hΦ'm, hΦ'd⟩ := exists_deriv_schr hF ψ hψ hM hΦ
  refine ⟨Φ', hΦ'm, fun w => ?_⟩
  have hnorm : ∀ x, ‖ψ x‖ = 1 := hψ.2.1
  have hM0 : M 0 = 0 := map_zero M
  set ω : Set (Fin N → AF F) := (fun s : ℝ => w.1 + (M s).1) '' Set.Icc (-1) 1 with hω
  have hωc : IsCompact ω := isCompact_Icc.image (continuous_const.add (continuous_fst.comp hM.1))
  obtain ⟨C, c, hcs, hc0, hcb⟩ := decay_majorant hF (GlobalTheory.T.adelicRapidDecay_of_mem_adelicSchwartzSpace F N Φ' hΦ'm) ω hωc
  obtain ⟨C₀, c₀, hcs₀, hc0₀, hcb₀⟩ := decay_majorant hF (GlobalTheory.T.adelicRapidDecay_of_mem_adelicSchwartzSpace F N Φ hΦ) {w.1} isCompact_singleton
  set ph : (Fin N → F) → ℂ := fun ξ => ψ (rat ξ ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) with hph
  have e : (fun t : ℝ => heisV ψ (M t) (thV ψ Φ) w) =
      fun t => ∑' ξ : Fin N → F, ph ξ * GlobalTheory.WeilM.schr ψ (M t) Φ (rat ξ + w.1) := by
    funext t
    rw [← thV_schr]
    rfl
  have hv : thV ψ Φ' w = ∑' ξ : Fin N → F, ph ξ * GlobalTheory.WeilM.schr ψ (M 0) Φ' (rat ξ + w.1) := by
    rw [hM0]
    refine tsum_congr fun ξ => ?_
    simp [ph, GlobalTheory.WeilM.schr]
    rfl
  rw [e, hv]
  have hmem : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  refine hasDerivAt_tsum_of_isPreconnected (hcs.mul_left C) isOpen_Ioo isPreconnected_Ioo
    (fun ξ t _ => (hasDerivAt_schr hF ψ hM hΦ'd (rat ξ + w.1) t).const_mul (ph ξ)) (fun ξ t ht => ?_) hmem ?_ hmem
  · have hy : w.1 + (M t).1 ∈ ω := ⟨t, ⟨ht.1.le, ht.2.le⟩, rfl⟩
    have := hcb ξ _ hy
    simp only [ph, GlobalTheory.WeilM.schr, norm_mul, hnorm, one_mul]
    simpa [add_assoc] using this
  · refine Summable.of_norm_bounded (hcs₀.mul_left C₀) fun ξ => ?_
    have := hcb₀ ξ w.1 rfl
    simpa [hM0, GlobalTheory.WeilM.schr, ph, norm_mul, hnorm] using this
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasOrbIntOfIsCompactCentConj
section
open MeasureTheory Matrix GlobalTheory.Orb
open Formalism.REAL (UJ KG toM toMK muK expG inG Jm Kset)
open scoped ContDiff

namespace GlobalTheory

theorem hasOrbInt_of_isCompact_cent_conj : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] [LocallyCompactSpace H] [T2Space H] (μ : Measure H) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (s : H), IsCompact (cent s : Set H) → ∀ (dt : Measure (cent s)) [dt.IsHaarMeasure] [dt.IsMulRightInvariant], IsProperOrbit (cent s) s → ∀ (y : H) (f : H → ℂ), Continuous f → HasCompactSupport f → HasOrbInt μ s dt f ((∫ x, f (x⁻¹ * (y⁻¹ * s * y) * x) ∂μ) / dt.real Set.univ) := by
  intro H _ _ _ _ _ _ _ _ μ _ _ s hT dt _ _ hP y f hf hc
  haveI : CompactSpace (cent s) := isCompact_iff_compactSpace.1 hT
  obtain ⟨C, hC, h0⟩ := hP _ hc
  have hcont : Continuous (conjFn s f) := hf.comp (by fun_prop)
  have hsupp : HasCompactSupport (conjFn s f) := by
    refine HasCompactSupport.intro' (hT.mul hC) (hT.mul hC).isClosed fun x hx => ?_
    by_contra hne
    obtain ⟨t, ht, htx⟩ := h0 x (subset_tsupport f hne)
    exact hx ⟨t⁻¹, (cent s).inv_mem ht, t * x, htx, by group⟩
  have hint : Integrable (conjFn s f) μ := hcont.integrable_of_hasCompactSupport hsupp
  have e : (∫ x, f (x⁻¹ * (y⁻¹ * s * y) * x) ∂μ) = ∫ x, f (x⁻¹ * s * x) ∂μ := by
    have := integral_mul_left_eq_self (μ := μ) (fun z => f (z⁻¹ * s * z)) y
    rw [← this]
    congr 1; ext x; congr 1; group
  rw [e]
  exact hasOrbInt_of_finite hint

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicAdelicFormOfBoundedSectionStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphicAdelicForm_of_boundedSection : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ) (r : ℕ) (hr : V.rank = r) (Comp : Type) (X : Comp → ReciprocityTheory.ChartRestriction.G.FD.Data D.host.E r) (la : ∀ k, ReciprocityTheory.ChartRestriction.G.FD.Wt (X k).Ψ r) (dict : GA D V → Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame (X k).Ψ r) (mu : GA D V → ℂ) (c : Comp → ℂ) (Kf : Subgroup (GA D V)), HolShape M → GoodDict θ M w hr X la dict mu c Kf → ∀ P : FDSec X, (∀ k, (X k).IsBddSec (la k) (P k)) → HolForm θ M w (Kf : Set (GA D V)) (fun _ => 1) (adel V dict (muPin V dict mu c) P) := by
  first | exact @GlobalTheory.HolDict.BackHol.holForm_adel | exact GlobalTheory.HolDict.BackHol.holForm_adel | (intros; apply GlobalTheory.HolDict.BackHol.holForm_adel <;> assumption)
end

