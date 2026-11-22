import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3529
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3531
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3557
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3561
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3553
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0078
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0393
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3554
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3315
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3341
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3355
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3337
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3401
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3560
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3481
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3334
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0008
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0838
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0788
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0785
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0577
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3494
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0759
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0789
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3562
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2761
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0597
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3555
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3556
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2436
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalFamilyBaseValueMemDescendedPoint
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon.BaseDescent

theorem ratHom_mem_of_isAlgClosed : ∀ (K : Type) [Field K] (k₀ : Subfield K), IsAlgClosed k₀ → ∀ (F : IntermediateField ℚ ℂ), FiniteDimensional ℚ F → ∀ (g : F →+* K) (x : F), g x ∈ k₀ := by
  intro K _ k₀ hk₀ F hF g x
  haveI : CharZero K := (RingHom.charZero_iff g.injective).mp inferInstance
  haveI : CharZero k₀ := (RingHom.charZero_iff k₀.subtype.injective).mpr inferInstance
  have h1 : IsAlgebraic ℚ x := Algebra.IsAlgebraic.isAlgebraic x
  have h2 : IsAlgebraic ℚ (g x) := by
    have := h1.algHom g.toRatAlgHom
    simpa using this
  have h3 : IsIntegral k₀ (g x) := (h2.extendScalars (algebraMap ℚ k₀).injective).isIntegral
  have hdeg := IsAlgClosed.degree_eq_one_of_irreducible k₀ (minpoly.irreducible h3)
  obtain ⟨y, hy⟩ := minpoly.mem_range_of_degree_eq_one k₀ (g x) hdeg
  rw [← hy]
  exact y.2

theorem pulledObj_descends : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) {V : Type} [CommRing V] [IsDomain V] (Q : DegPre V) [Module (𝓞 E) Q.X] (oQ : letI := H.starRing; Q.OAct (𝓞 E)) (iw : L.W →+* V) {I : Type} [Fintype I] (s : I → V) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : Q.X ≃ₗ[𝓞 E] L.D.X), DivFrom L Q oQ iw s ε e → ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (ev : V →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → ∀ (o' : LowObj D' c ((ev.comp iw).comp L.b)) (m₁ : ObjMap o' L.o (spMap (ev.comp iw))), (∃ (B₀ : Over (Sp k₀)) (_ : GrpObj B₀) (_ : IsCommMonObj B₀) (M₀ : LB B₀.left) (c₀ : Q.X → (Sp k₀ ⟶ B₀.left)) (B' : Over (Sp K)) (_ : GrpObj B') (π₁ : B'.left ⟶ Q.P.A.left) (π₀ : B'.left ⟶ B₀.left) (w : LB.Iso (Q.P.L.pull π₁) (M₀.pull π₀)) (c' : Q.X → (Sp K ⟶ B'.left)), IsAbelianScheme B₀ ∧ M₀.IsLB ∧ IsGrpPullback B' Q.P.A (spMap ev) π₁ ∧ IsGrpPullback B' B₀ (spMap k₀.subtype) π₀ ∧ w.IsGen ∧ ∀ a, c' a ≫ B'.hom = 𝟙 _ ∧ c' a ≫ π₁ = spMap ev ≫ (Q.c a).left ∧ c' a ≫ π₀ = spMap k₀.subtype ≫ c₀ a) → ∃ (B₀ : Over (Sp k₀)) (_ : GrpObj B₀) (_ : IsCommMonObj B₀) (M₀ : LB B₀.left) (π : o'.t.G.left ⟶ B₀.left), IsAbelianScheme B₀ ∧ M₀.IsLB ∧ IsGrpPullback o'.t.G B₀ (spMap k₀.subtype) π ∧ LBIso o'.t.PP.L (M₀.pull π) ∧ ∀ y : L.D.X, ∃ x : Sp K ⟶ o'.t.G.left, x ≫ o'.t.G.hom = 𝟙 _ ∧ x ≫ m₁.toSABMap.φ ≫ L.φB = spMap (ev.comp iw) ≫ (L.D.c y).left ∧ ∃ x₀ : Sp k₀ ⟶ B₀.left, x ≫ π = spMap k₀.subtype ≫ x₀ := by
  intro E _ _ _ H D' l c L V _ _ Q _ oQ iw I _ s ε e hDiv K _ _ _ ev k₀ hk₀ o' m₁ hB
  obtain ⟨B₀, _, _, M₀, c₀, B', _, π₁, π₀, w, c', hab, hM, h1, h0, hw, hc⟩ := hB
  obtain ⟨θ, hθ, hLθ, hrel⟩ := GlobalTheory.T.pulledLowerObject_group_identification L Q oQ iw s ε e hDiv K ev o' m₁ B' π₁ h1
  obtain ⟨hpb, hL, hpts⟩ := GlobalTheory.T.pulledLowerObject_descends_with_points_subfield L Q oQ iw s ε e hDiv K ev k₀ hk₀ o' m₁ B₀ M₀ c₀ B' π₁ π₀ w c' θ hab hM h1 h0 hw hc hθ hLθ hrel
  exact ⟨B₀, inferInstance, inferInstance, M₀, θ ≫ π₀, hab, hM, hpb, hL, fun y => by
    obtain ⟨x, hx1, hx2, x₀, hx₀⟩ := hpts y
    exact ⟨x, hx1, hx2, x₀, by rw [← Category.assoc] at hx₀ ⊢; simpa using hx₀⟩⟩

end GlobalTheory.UCanon.BaseDescent

theorem GlobalTheory.UCanon.base_value_mem_of_descended_point : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) {V : Type} [CommRing V] [IsDomain V] (Q : DegPre V) [Module (𝓞 E) Q.X] (oQ : letI := H.starRing; Q.OAct (𝓞 E)) (iw : L.W →+* V) {I : Type} [Fintype I] (s : I → V) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : Q.X ≃ₗ[𝓞 E] L.D.X), DivFrom L Q oQ iw s ε e → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∃ (B₀ : Over (Sp k₀)) (_ : GrpObj B₀) (_ : IsCommMonObj B₀) (M₀ : LB B₀.left) (c₀ : Q.X → (Sp k₀ ⟶ B₀.left)) (B' : Over (Sp K)) (_ : GrpObj B') (π₁ : B'.left ⟶ Q.P.A.left) (π₀ : B'.left ⟶ B₀.left) (w : LB.Iso (Q.P.L.pull π₁) (M₀.pull π₀)) (c' : Q.X → (Sp K ⟶ B'.left)), IsAbelianScheme B₀ ∧ M₀.IsLB ∧ IsGrpPullback B' Q.P.A (spMap ev) π₁ ∧ IsGrpPullback B' B₀ (spMap k₀.subtype) π₀ ∧ w.IsGen ∧ ∀ a, c' a ≫ B'.hom = 𝟙 _ ∧ c' a ≫ π₁ = spMap ev ≫ (Q.c a).left ∧ c' a ≫ π₀ = spMap k₀.subtype ≫ c₀ a) → ∀ a, ev (iw a) ∈ k₀ := by
  intro E _ _ _ H D' l c L V _ _ Q _ oQ iw I _ s ε e hDiv K _ _ ev k₀ hk₀ hB a
  let f : L.W →+* K := ev.comp iw
  have hF : ∀ x : c.F, (f.comp L.b) x ∈ k₀ := GlobalTheory.UCanon.BaseDescent.ratHom_mem_of_isAlgClosed K k₀ hk₀ c.F c.fin (f.comp L.b)
  haveI : CharZero K := (RingHom.charZero_iff (f.comp L.b).injective).mp inferInstance
  obtain ⟨o', ⟨m₁⟩⟩ := (GlobalTheory.T.shimuraObject_pullback_comp_cancel (D := D') (l := GlobalTheory.LowDat.lowLevel l)).1 (lowMap c L.b) L.o (spMap f)
    (lowMap c (f.comp L.b)) (by simp only [lowMap, spMap, ← Spec.map_comp]; rfl)
  obtain ⟨B₀, _, _, M₀, π, hab, hM, hpb, hL, hpts⟩ := GlobalTheory.UCanon.BaseDescent.pulledObj_descends L Q oQ iw s ε e hDiv K ev k₀ hk₀ o' m₁ hB
  choose x hx1 hx2 hx3 using hpts
  apply GlobalTheory.T.mem_subfield_of_forall_ringEquiv_fixed_of_isAlgClosed' K k₀ hk₀
  intro σ hσ
  obtain ⟨n, hn⟩ := GlobalTheory.T.exists_objMap_fixing_descended_points_subfield K k₀ hk₀ o' B₀ M₀ π hab hM hpb hL σ hσ
  have hcomp : ∀ g' : Sp K ⟶ Sp L.W, g' = spMap (σ : K →+* K) ≫ spMap f →
      ∃ k : ObjMap o' L.o g', k.toSABMap.φ = n.toSABMap.φ ≫ m₁.toSABMap.φ := by
    rintro g' rfl
    exact ((GlobalTheory.T.shimuraObject_pullback_comp_cancel (D := D') (l := GlobalTheory.LowDat.lowLevel l)).2 _ _ _ L.o o' o' (spMap f) (spMap (σ : K →+* K)) m₁).1 n
  obtain ⟨m₂, hm₂⟩ := hcomp (spMap ((σ : K →+* K).comp f)) (by simp only [spMap, ← Spec.map_comp]; rfl)
  have key := L.fineRed K f ((σ : K →+* K).comp f)
    (by ext y; simp only [RingHom.comp_apply]; exact (hσ _ (hF y)).symm) o' m₁ m₂ x hx2
    (fun y => by
      rw [hm₂, Category.assoc, ← Category.assoc (x y), hn (x y) (hx1 y) (hx3 y), Category.assoc, hx2 y]
      simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, f]) hx1
  have := congrArg (fun g : L.W →+* K => g a) key
  simpa [f] using this.symm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamToStructureH1SurjectiveStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.de_rham_to_structure_h1_surjective : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → Function.Surjective (toHO1 A.hom) := by
  first | exact @GlobalTheory.AbCoh.toHO1_surjective | exact GlobalTheory.AbCoh.toHO1_surjective | (intros; apply GlobalTheory.AbCoh.toHO1_surjective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamVectorExtensionIsoOfHodgeDeRham
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem deRhamVectorExtension_of_abelianHodgeDeRham :
    GlobalTheory.Published.AbelianHodgeDeRham → GlobalTheory.Published.DeRhamVectorExtension := by
  intro hHdR p _
  obtain ⟨e, hN, hF, hT, -⟩ := GlobalTheory.T.exists_canonical_deRham_rigidExtension_family hHdR p
  exact ⟨e, hN, hF, hT⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneColengthEqLogDegree
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.Dieu

theorem length_quot_range_map_eq_of_hasLogDeg : ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k]
    [CharP k p] [PerfectRing k p] (G H : PDivGroup p k) (q : G ⟶ H) (e : ℕ), IsIsog q → HasLogDeg q e →
    Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q)) = e := by
  intro p _ T k _ _ _ G H q e hq he
  obtain ⟨n, g, hqg, hgq⟩ := hq
  have hq' : IsIsog q := ⟨n, g, hqg, hgq⟩
  have hg : IsIsog g := ⟨n, q, hgq, hqg⟩
  obtain ⟨e', he', -⟩ := GlobalTheory.T.existsUnique_kernelOrder_pPowerDegree_isogeny p k H G g hg
  have hpG := ((GlobalTheory.T.pDivisibleGroup_isogeny_basic_properties p k G).1 n).2
  rw [← hqg] at hpG
  have hle : n * G.height ≤ e + e' := GlobalTheory.T.hasKernelOrderPPowerDegree_comp_le_add p k G H G q g e e' _ he he' hpG
  have h1 := GlobalTheory.T.kernelDegree_le_dieudonneColength p T k G H q e hq' he
  have h2 := GlobalTheory.T.kernelDegree_le_dieudonneColength p T k H G g e' hg he'
  obtain ⟨hinj, hfin1, -⟩ := GlobalTheory.T.isogenous_pDivGroup_finrank_omega_dual p T k G H q hq'
  obtain ⟨-, hfin2, -⟩ := GlobalTheory.T.isogenous_pDivGroup_finrank_omega_dual p T k H G g hg
  obtain ⟨hid, hcomp, -, -, -, -, -, hrank, -⟩ :=
    GlobalTheory.T.dieudonneFunctorBase_functor_properties p (fun _ _ _ => True) T.base k G H G trivial trivial trivial
  obtain ⟨-, -, -, -, hsmulG, -⟩ :=
    GlobalTheory.T.dieudonneFunctorBase_functor_properties p (fun _ _ _ => True) T.base k G G G trivial trivial trivial
  obtain ⟨hadd, hpow, -⟩ := GlobalTheory.T.witt_module_length_composition p k (T.M G) (T.M H) (T.M G)
  have hsum := hadd (T.map q) (T.map g) hinj
  have hcomp' : T.map q ∘ₗ T.map g = T.map (q ≫ g) := (hcomp q g).symm
  have hmul : ∀ a : T.M G, (T.map q ∘ₗ T.map g) a = p ^ n • a := by
    intro a
    rw [hcomp', hqg]
    show T.base.map trivial trivial ((p : ℤ_[p]) ^ n • 𝟙 G) a = p ^ n • a
    rw [hsmulG n (𝟙 G) a, hid]
    rfl
  have hn := hpow (T.base.free G trivial) (T.base.finite G trivial) n _ hmul
  rw [hn, hrank] at hsum
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.mp hfin1
  obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.mp hfin2
  rw [← ha] at h1 hsum ⊢
  rw [← hb] at h2 hsum
  norm_cast at h1 h2 hsum ⊢
  omega

end GlobalTheory.Dieu
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndIsogenyAlgebraFiniteFinrankLeStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.end_isogeny_algebra_finite_finrank_le : ∀ (K : Type) [Field K] (A : AbVar K), Module.Finite ℚ (End0 A) ∧ Module.finrank ℚ (End0 A) ≤ 4 * A.dim * A.dim := by
  first | (exact @GlobalTheory.AV.AbVar.end_isogeny_algebra_finrank_le) | (exact GlobalTheory.AV.AbVar.end_isogeny_algebra_finrank_le) | (intros; apply GlobalTheory.AV.AbVar.end_isogeny_algebra_finrank_le  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqPowSmulOfPDivGroupTorsionTowerMapStatement
section
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.AV GlobalTheory.AV.AbVar
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_pow_smul_of_pDivGroup_torsionTower_map : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] (A B : AbVar k) (G H : PDivGroup p k) (t : G.TorsionTower A.X) (t' : H.TorsionTower B.X) (f : A ⟶ B), (∀ (n : ℕ) (g : G ⟶ H), t.map t' f.hom = (p : ℤ_[p]) ^ n • g → ∃ f' : A ⟶ B, f = p ^ n • f') ∧ (t.map t' f.hom = 0 → f = 0) := by
  first | (exact @GlobalTheory.AV.AbVar.eq_pow_smul_of_torsionTower_map) | (exact GlobalTheory.AV.AbVar.eq_pow_smul_of_torsionTower_map) | (intros; apply GlobalTheory.AV.AbVar.eq_pow_smul_of_torsionTower_map  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdaptedQuasiLogBasisPDivGroupLieDual
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.QLogBasis

section Gen

variable {O E : Type} [CommRing O] [CommRing E] [Algebra O E] {d : ℕ}
  (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O)

theorem up_const (h : ∀ i, constantCoeff (μ i) = 0) (i : Fin d) :
    constantCoeff (up E μ i) = 0 := by
  simp only [up, constantCoeff_map, h, map_zero]

def cobL (h : ∀ i, constantCoeff (μ i) = 0) :
    MvPowerSeries (Fin d) E →ₗ[E] MvPowerSeries (Fin d ⊕ Fin d) E where
  toFun := cob1 (up E μ)
  map_add' := formalCoboundary_add (up_const μ h)
  map_smul' := formalCoboundary_smul (up_const μ h)

theorem cobL_apply (h : ∀ i, constantCoeff (μ i) = 0) (f : MvPowerSeries (Fin d) E) :
    cobL μ h f = cob1 (up E μ) f := rfl

variable {μ}

theorem in_top_add {σ : Type} {f g : MvPowerSeries σ E} (hf : In (⊤ : Ideal O) f)
    (hg : In (⊤ : Ideal O) g) : In (⊤ : Ideal O) (f + g) := fun α => by
  obtain ⟨a, -, ha⟩ := hf α
  obtain ⟨b, -, hb⟩ := hg α
  exact ⟨a + b, trivial, by rw [map_add, ha, hb, map_add]⟩

theorem in_top_sub {σ : Type} {f g : MvPowerSeries σ E} (hf : In (⊤ : Ideal O) f)
    (hg : In (⊤ : Ideal O) g) : In (⊤ : Ideal O) (f - g) := fun α => by
  obtain ⟨a, -, ha⟩ := hf α
  obtain ⟨b, -, hb⟩ := hg α
  exact ⟨a - b, trivial, by rw [map_sub, ha, hb, map_sub]⟩

theorem in_top_smul {σ : Type} {f : MvPowerSeries σ E} (a : O) (hf : In (⊤ : Ideal O) f) :
    In (⊤ : Ideal O) (algebraMap O E a • f) := fun α => by
  obtain ⟨b, -, hb⟩ := hf α
  exact ⟨a * b, trivial, by rw [map_smul, hb, smul_eq_mul, map_mul]⟩

theorem in_top_map {σ : Type} {f : MvPowerSeries σ E} (hf : In (⊤ : Ideal O) f) :
    ∃ s : MvPowerSeries σ O, f = map (algebraMap O E) s := by
  have hf' : ∀ α, ∃ b : O, coeff α f = algebraMap O E b := fun α => by
    obtain ⟨b, -, hb⟩ := hf α
    exact ⟨b, hb⟩
  choose s hs using hf'
  refine ⟨s, ?_⟩
  ext α
  exact (hs α).trans (coeff_map (algebraMap O E) α s).symm

theorem ql_zero (h : ∀ i, constantCoeff (μ i) = 0) : QL μ (⊤ : Ideal O) (0 : MvPowerSeries (Fin d) E) := by
  refine ⟨map_zero _, fun i => ⟨0, trivial, by simp [lin]⟩, fun α => ⟨0, trivial, ?_⟩⟩
  rw [← cobL_apply μ h, map_zero, map_zero, map_zero]

theorem ql_add_smul (h : ∀ i, constantCoeff (μ i) = 0) {f g : MvPowerSeries (Fin d) E}
    (hf : QL μ ⊤ f) (hg : QL μ ⊤ g) (a : O) : QL μ ⊤ (f + algebraMap O E a • g) := by
  refine ⟨?_, fun i => ?_, ?_⟩
  · have h1 := hf.1
    have h2 := hg.1
    rw [← coeff_zero_eq_constantCoeff_apply] at h1 h2 ⊢
    rw [map_add, map_smul, h1, h2, smul_zero, add_zero]
  · obtain ⟨a1, -, h1⟩ := hf.2.1 i
    obtain ⟨a2, -, h2⟩ := hg.2.1 i
    refine ⟨a1 + a * a2, trivial, ?_⟩
    simp only [lin] at h1 h2 ⊢
    rw [map_add, map_smul, h1, h2, smul_eq_mul, map_add, map_mul]
  · rw [← cobL_apply μ h, map_add, map_smul, cobL_apply, cobL_apply]
    exact in_top_add hf.2.2 (in_top_smul a hg.2.2)

theorem ql_comb (h : ∀ i, constantCoeff (μ i) = 0) {ι : Type} [Fintype ι]
    {e : ι → MvPowerSeries (Fin d) E} (he : ∀ i, QL μ ⊤ (e i)) (b : ι → O) :
    QL μ ⊤ (comb b e) := by
  classical
  unfold comb
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simpa using ql_zero h
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, add_comm]
    exact ql_add_smul h ih (he a) (b a)

theorem comb_sub {ι : Type} [Fintype ι] (e : ι → MvPowerSeries (Fin d) E) (b b' : ι → O) :
    comb (b - b') e = comb b e - comb b' e := by
  simp only [comb, Pi.sub_apply, map_sub, sub_smul, Finset.sum_sub_distrib]

end Gen

section Chart

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] (hv : v.Integers O)
  {G : PDivGroup p O} {d : ℕ} (c : QLog.Chart G d) {E : Type} [CommRing E] [Algebra O E]
  (hE : IsFrame p E (RingHom.id O))
include hv hE

theorem isLie_add {f g : MvPowerSeries (Fin d) E} {l l' : G.dual.Lie} (hf : QL c.μ ⊤ f)
    (hg : QL c.μ ⊤ g) (hl : c.IsLie f l) (hl' : c.IsLie g l') (a : O) :
    c.IsLie (f + algebraMap O E a • g) (l + a • l') :=
  (GlobalTheory.T.pDivGroup_dual_tangent_linear_kills_integral p C v O hv G d c E hE f g l l' a hl hl').1 hf hg

theorem isLie_int {f : MvPowerSeries (Fin d) E} {l : G.dual.Lie} (hl : c.IsLie f l)
    (hs : ∃ s : MvPowerSeries (Fin d) O, f = map (algebraMap O E) s) : l = 0 :=
  (GlobalTheory.T.pDivGroup_dual_tangent_linear_kills_integral p C v O hv G d c E hE f f l l 0 hl hl).2.1 hs

theorem isLie_log {f : MvPowerSeries (Fin d) E} {l : G.dual.Lie} (hl : c.IsLie f l)
    (h : cob1 (up E c.μ) f = 0) : l = 0 :=
  (GlobalTheory.T.pDivGroup_dual_tangent_linear_kills_integral p C v O hv G d c E hE f f l l 0 hl hl).2.2 h

theorem isLie_zero : c.IsLie (0 : MvPowerSeries (Fin d) E) 0 := by
  obtain ⟨l, hl, -⟩ := GlobalTheory.T.pDivGroup_dual_tangent_of_quasiLogarithm p C v O hv G d c E hE 0 (ql_zero c.isLaw.const)
  rwa [isLie_int hv c hE hl ⟨0, (map_zero _).symm⟩] at hl

theorem isLie_comb {ι : Type} [Fintype ι] {e : ι → MvPowerSeries (Fin d) E} {L : ι → G.dual.Lie}
    (he : ∀ i, QL c.μ ⊤ (e i)) (hL : ∀ i, c.IsLie (e i) (L i)) (b : ι → O) :
    c.IsLie (comb b e) (∑ i, b i • L i) := by
  classical
  have h0 := c.isLaw.const
  suffices ∀ s : Finset ι, QL c.μ ⊤ (∑ i ∈ s, algebraMap O E (b i) • e i) ∧
      c.IsLie (∑ i ∈ s, algebraMap O E (b i) • e i) (∑ i ∈ s, b i • L i) from
    (this Finset.univ).2
  intro s
  induction s using Finset.induction_on with
  | empty => simpa using ⟨ql_zero (E := E) h0, isLie_zero hv c hE⟩
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, add_comm, add_comm (b a • L a)]
    exact ⟨ql_add_smul h0 ih.1 (he a) (b a), isLie_add hv c hE ih.1 (he a) ih.2 (hL a) (b a)⟩

theorem exists_isLie (l : G.dual.Lie) : ∃ f : MvPowerSeries (Fin d) E, QL c.μ ⊤ f ∧ c.IsLie f l := by
  have h0 := c.isLaw.const
  let M : Submodule O G.dual.Lie :=
    { carrier := {l | ∃ f : MvPowerSeries (Fin d) E, QL c.μ ⊤ f ∧ c.IsLie f l}
      add_mem' := by
        rintro l1 l2 ⟨f1, hf1, hl1⟩ ⟨f2, hf2, hl2⟩
        refine ⟨f1 + algebraMap O E 1 • f2, ql_add_smul h0 hf1 hf2 1, ?_⟩
        have := isLie_add hv c hE hf1 hf2 hl1 hl2 1
        rwa [one_smul] at this
      zero_mem' := ⟨0, ql_zero (E := E) h0, isLie_zero hv c hE⟩
      smul_mem' := by
        rintro a l ⟨f, hf, hl⟩
        refine ⟨0 + algebraMap O E a • f, ql_add_smul h0 (ql_zero (E := E) h0) hf a, ?_⟩
        have := isLie_add hv c hE (ql_zero (E := E) h0) hf (isLie_zero hv c hE) hl a
        simpa only [zero_add] using this }
  have hom := GlobalTheory.PDiv.omega_finite_projective p C v O hv G.dual
  haveI := hom.1
  haveI := hom.2
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  have hp : Ideal.span {(p : O)} ≤ (⊥ : Ideal O).jacobson :=
    ((Ideal.span_singleton_le_iff_mem _).2 ((IsLocalRing.mem_maximalIdeal _).2
      (Fact.out : ¬IsUnit (p : O)))).trans (IsLocalRing.maximalIdeal_le_jacobson _)
  have htop : (⊤ : Submodule O G.dual.Lie) ≤ M := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hp fun x _ => ?_
    obtain ⟨f, l', l'', hf, hl', rfl⟩ := GlobalTheory.T.exists_quasiLogarithm_lie_add_p_smul p C v O hv G d c E hE x
    exact Submodule.add_mem_sup ⟨f, hf, hl'⟩
      (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top)
  exact htop Submodule.mem_top

end Chart

theorem adapted_basis : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (E : Type) [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∃ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) E) (lb : Module.Basis (Fin k) O G.dual.Lie), IsBasis c.μ e ∧ IsAdapted (RingHom.id O) c.μ e ∧ (∀ i, cob1 (up E c.μ) (e (Sum.inl i)) = 0) ∧ ∀ j, c.IsLie (e (Sum.inr j)) (lb j) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv G d c E _ _ hE
  have h0 := c.isLaw.const
  have hom := GlobalTheory.PDiv.omega_finite_projective p C v O hv G.dual
  haveI := hom.1
  haveI := hom.2
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  haveI : Module.Free O G.dual.omega := Module.free_of_flat_of_isLocalRing
  let lb := Module.finBasis O G.dual.Lie
  choose F hF using fun j => exists_isLie hv c hE (lb j)
  choose large₂ hLg using fun i : Fin d => GlobalTheory.T.exists_formalGroupLaw_log_with_linearPart p O E hE d c.μ c.isLaw (Pi.single i 1)
  have hlin : ∀ i, lin (large₂ i) = Pi.single i 1 := fun i => funext fun i' => by
    rw [(hLg i).2.1 i', Pi.single_apply, Pi.single_apply]
    split_ifs <;> simp
  let e : Fin d ⊕ Fin (Module.finrank O G.dual.Lie) → MvPowerSeries (Fin d) E := Sum.elim large₂ F
  have hQ : ∀ i, QL c.μ ⊤ (e i) := by
    rintro (i | j)
    · refine ⟨(hLg i).1, fun i' => ⟨_, trivial, (hLg i).2.1 i'⟩, fun α => ⟨0, trivial, ?_⟩⟩
      show coeff α (cob1 (up E c.μ) (large₂ i)) = _
      rw [(hLg i).2.2, map_zero, map_zero]
    · exact (hF j).1
  have hcob : ∀ i, cob1 (up E c.μ) (e (Sum.inl i)) = 0 := fun i => (hLg i).2.2
  have hlin' : ∀ i, lin (e (Sum.inl i)) = Pi.single i 1 := hlin
  have hlie : ∀ j, c.IsLie (e (Sum.inr j)) (lb j) := fun j => (hF j).2
  let L : Fin d ⊕ Fin (Module.finrank O G.dual.Lie) → G.dual.Lie := Sum.elim 0 lb
  have hL : ∀ i, c.IsLie (e i) (L i) := by
    rintro (i | j)
    · obtain ⟨l, hl, -⟩ := GlobalTheory.T.pDivGroup_dual_tangent_of_quasiLogarithm p C v O hv G d c E hE _ (hQ (Sum.inl i))
      rw [isLie_log hv c hE hl (hcob i)] at hl
      exact hl
    · exact hlie j
  have huniq : ∀ b : Fin d ⊕ Fin (Module.finrank O G.dual.Lie) → O, In (⊤ : Ideal O) (comb b e) → b = 0 := by
    intro b hb
    obtain ⟨s, hs⟩ := in_top_map hb
    have hl0 : ∑ i, b i • L i = 0 := isLie_int hv c hE (isLie_comb hv c hE hQ hL b) ⟨s, hs⟩
    have hr : ∀ j, b (Sum.inr j) = 0 := by
      have : ∑ j, b (Sum.inr j) • lb j = 0 := by simpa [Fintype.sum_sum_type, L] using hl0
      exact Fintype.linearIndependent_iff.1 lb.linearIndependent _ this
    have hc : cob1 (up E c.μ) (map (algebraMap O E) s) = 0 := by
      rw [← hs, ← cobL_apply c.μ h0]
      simp [comb, map_sum, map_smul, Fintype.sum_sum_type, cobL_apply, hcob, hr]
    have hs0 := GlobalTheory.T.pDivGroupChart_integral_additive_series_eq_zero p C v O hv G d c E hE s hc
    have hc0 : comb b e = 0 := by rw [hs, hs0, map_zero]
    have hl : ∀ i, b (Sum.inl i) = 0 := fun i => by
      have h1 := congrArg (coeff (Finsupp.single i 1)) hc0
      have hco : ∀ i', coeff (Finsupp.single i 1) (e (Sum.inl i')) = (Pi.single i' (1 : E) : Fin d → E) i :=
        fun i' => congrFun (hlin' i') i
      simp [comb, map_sum, Fintype.sum_sum_type, hr, hco, Pi.single_apply] at h1
      exact hE.inj (by rw [map_zero]; simpa [Algebra.smul_def] using h1)
    funext x
    cases x with
    | inl i => exact hl i
    | inr j => exact hr j
  refine ⟨Module.finrank O G.dual.Lie, e, lb, ⟨hQ, fun f hf => ?_⟩,
    fun i => ⟨fun α => ⟨0, (RingHom.mem_ker).2 (map_zero _), by rw [hcob i, map_zero, map_zero]⟩,
      hlin' i⟩, hcob, hlie⟩
  obtain ⟨b, hb⟩ := GlobalTheory.T.quasiLogarithm_generation_of_division_step_padic p O E hE d c.μ c.isLaw _ e hQ
    (GlobalTheory.T.quasiLogarithm_division_step_decomposition p C v O hv G d c E hE _ e lb hQ hcob hlin' hlie) f hf
  refine ⟨b, hb, fun b' hb' => ?_⟩
  have h1 : In (⊤ : Ideal O) (comb (b' - b) e) := by
    rw [comb_sub]
    have := in_top_sub hb hb'
    rwa [sub_sub_sub_cancel_left] at this
  exact sub_eq_zero.1 (huniq _ h1)

end GlobalTheory.QLogBasis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCarriedSectionNonzeroNearClosedFibreStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_carried_section_nonzero_near_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hB : Base R) (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R') (hF : FinExt ρ) (hG : IsGal ρ) (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (hS' : IsSemiAbelian G') (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left) (hS : IsSemiAbelian G) (hβ : IsGrpPullback G' G (spMap ρ) β) (hact : ∀ σ, a.act σ ≫ β = β), ∃ θ : U'.LG.L.Sec, (∀ (σ : Gal ρ) (h : IsPullDeg (Gal.hom σ) D'.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'), bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) = a.act σ → ∀ hP : IsPullUnif (Gal.hom σ) h bc U' U', PullOver hD h → SecCarried U'.LG.L θ _ (Classical.choose hP.lg)) ∧ ∃ O : G.left.Opens, (∃ g ∈ O, G.hom g = closedPoint R) ∧ ∀ g' : G'.left, β g' ∈ O → G.hom (β g') = closedPoint R → g' ∈ secNz θ := by
  first | exact @GlobalTheory.Mum.exists_carried_sec_nz_near_closed | exact GlobalTheory.Mum.exists_carried_sec_nz_near_closed | (intros; apply GlobalTheory.Mum.exists_carried_sec_nz_near_closed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCentredPureExtensionTowerMemberStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_centred_pure_extension_tower_member : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), GlobalTheory.GSep.IsAct X₁ act → ∀ (𝔗 : GlobalTheory.GSep.Tower X₁ act) (z₂ : 𝔗.X₂.M.Z), 𝔗.p z₂ = z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V), (∀ m : ℕ, m ≠ 0 → IsUnit (m : V)) → IsCN V → IsLocalHom ev → GlobalTheory.GSep.RegAt X₁ z₁ ev → ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (io : V →+* V') (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V'), IsCN V' ∧ Function.Injective io ∧ io.Finite ∧ IsLocalHom io ∧ (∀ J : Ideal V, (J.map io).comap io = J) ∧ 𝔗.Ext ev io ev₂ := by
  first | exact @GlobalTheory.GSep.exists_centred_ext_tower | exact GlobalTheory.GSep.exists_centred_ext_tower | (intros; apply GlobalTheory.GSep.exists_centred_ext_tower <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommutatorPairingValueHeckePointsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_commutatorPairing_value_heckePoints : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s), ∀ h₁ ∈ GlobalTheory.UPel.HT.Hecke.heckeSub o g N, ∀ h₂ ∈ GlobalTheory.UPel.HT.Hecke.heckeSub o g N, ∃ u : Γ((𝟙_ (Over S)).left, ⊤)ˣ, Out.WeilIs (G2 o.A) (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) 1 (lift h₁ 1 : 𝟙_ (Over S) ⟶ G2 o.A) (lift 1 h₂) u := by
  first | (exact @GlobalTheory.HeckeWeilLift.exists_weilIs_hecke) | (exact GlobalTheory.HeckeWeilLift.exists_weilIs_hecke) | (intros; apply GlobalTheory.HeckeWeilLift.exists_weilIs_hecke <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConnectionMatrixInvariantBasisStatement
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
theorem _root_.GlobalTheory.T.exists_connection_matrix_invariant_basis : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ D : Derivation ℤ R R,
  ∃ (Θ : Matrix (Fin n) (Fin n) R) (J : Type) (V : J → Dd.toPre.P.A.left.Opens) (j : J → Dd.toPre.P.L.ι) (d : J → Fld Y.H.left),
    Θᵀ = Θ ∧ ⨆ i, V i = ⊤ ∧ (∀ i, V i ≤ Dd.toPre.P.L.U (j i)) ∧ (∀ i, IsLift Y.H ⇑D (Y.q.left ⁻¹ᵁ V i) (d i)) ∧
    (∀ i (α : Dd.toPre.X) (V' : Dd.toPre.P.A.left.Opens), Y.q.left ⁻¹ᵁ V' ≤ Y.q.left ⁻¹ᵁ V i → ∀ f,
      IsWt Y α (Y.q.left ⁻¹ᵁ V') f → IsWt Y α (Y.q.left ⁻¹ᵁ V') (d i _ f)) ∧
    ∀ i i' (W : Y.H.left.Opens), W ≤ Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i' → ∀ f, d i W f - d i' W f =
      ∑ a, ∑ b, constFn Y.H.hom W (Θ a b) * dlg Y.H Y.q.left Dd.toPre.P.L (dd b) (j i) (j i') W * dd a W f := by
  first | exact @GlobalTheory.HeatInvLift.exists_invLift_symmKS | exact GlobalTheory.HeatInvLift.exists_invLift_symmKS | (intros; apply GlobalTheory.HeatInvLift.exists_invLift_symmKS <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteRepRosatiOrderActionsSiegelStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_rep_rosati_orderActions_siegel : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (h M : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Scheme.{0}) [IsLocallyNoetherian S] (s₁ : S ⟶ Sp B) (c : SiegPre h M ζ s₁), Out.RelAmple c.A c.diag → ∃ (H : Scheme.{0}) (πH : H ⟶ S) (AH : Over H) (_ : GrpObj AH) (_ : IsCommMonObj AH) (φH : AH.left ⟶ c.A.left) (φ₂H : (G2 AH).left ⟶ (G2 c.A).left) (actH : OActN D.O AH), IsFinite πH ∧ IsAbelianScheme AH ∧ IsGrpPullback AH c.A πH φH ∧ IsSquare φH φ₂H ∧ RosatiFor D actH (c.P.pull φ₂H) ∧ ∀ (T : Scheme.{0}) (g : T ⟶ S) (AT : Over T) [GrpObj AT] (φ : AT.left ⟶ c.A.left) (φ₂ : (G2 AT).left ⟶ (G2 c.A).left) (act : OActN D.O AT), IsGrpPullback AT c.A g φ → IsSquare φ φ₂ → RosatiFor D act (c.P.pull φ₂) → ∃! z : T ⟶ H, z ≫ πH = g ∧ ∃ ψ : AT.left ⟶ AH.left, IsGrpPullback AT AH z ψ ∧ ψ ≫ φH = φ ∧ ∀ a : D.O, (act.act a).left ≫ ψ = ψ ≫ (actH.act a).left := by
  first | (exact @GlobalTheory.UPel.HT.exists_finite_rep_oActN_rosati) | (exact GlobalTheory.UPel.HT.exists_finite_rep_oActN_rosati) | (intros; apply GlobalTheory.UPel.HT.exists_finite_rep_oActN_rosati  <;> assumption)
end

