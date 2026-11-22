import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0082
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0007
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ValRPullbackTwistingSheafTransition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3073
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3095
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2464
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2745
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricallyIntegralOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfInfLeInfRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2805
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2670
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2666
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2673
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2646
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2467
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2211
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0603
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsTwistBasisOffPrime
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0021
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0024
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitOfAssociated
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2773
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0256
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBoxGenOfSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0026
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2045
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3077
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3093
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0084
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorUniformisedGroupsBaseChange
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2554
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2643
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricCoordinatesO1FactorialPower
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMin.CrdSym

open GlobalTheory.Points GlobalTheory.ProjSpace

variable {k Ω : Type} [CommRing k] [Field Ω] [Algebra k Ω]

theorem div_mem_O {o : Type} [CommRing o] {M : RatModel k Ω} {n : ℕ} {h : M.Z ⟶ PSpace o n}
    {c : Fin (n + 1) → Ω} (hc : PCrd (M.pt ≫ h) c) {a : Fin (n + 1)} {z : M.Z}
    (hz : z ∈ h ⁻¹ᵁ ProjSpace.chart o n a) : c a ≠ 0 ∧ ∀ b, c b / c a ∈ M.O z := by
  have hW : ⊤ ≤ M.pt ⁻¹ᵁ (h ⁻¹ᵁ ProjSpace.chart o n a) := M.top_le_preimage_pt ⟨z, hz⟩
  obtain ⟨h0, hv⟩ := GlobalTheory.T.homogeneousCoords_in_standardChart_ratio o Ω n (M.pt ≫ h) c a hc (le_preimage_comp M.pt h le_rfl hW)
  refine ⟨h0, fun b => ?_⟩
  have e : valF M.pt (h ⁻¹ᵁ ProjSpace.chart o n a) (ProjSpace.pullRatio h _ a le_rfl b) = c b / c a :=
    (Points.valR_appLE M.pt h le_rfl hW _).trans (hv b)
  exact e ▸ M.valF_mem_O hz _

theorem valR_pullO1_g {L : Type} [Field L] {X : Scheme.{0}} {o : Type} [CommRing o] {r : ℕ} (y0 : Sp L ⟶ X)
    (π : X ⟶ PSpace o r) {t : Fin (r + 1) → L} (ht : PCrd (y0 ≫ π) t) (i j : PUnit → Fin (r + 1))
    (h : ⊤ ≤ y0 ⁻¹ᵁ (((ProjSpace.O1 o r).pull π).U i ⊓ ((ProjSpace.O1 o r).pull π).U j)) :
    valR y0 _ (((ProjSpace.O1 o r).pull π).g i j).val = t (j PUnit.unit) / t (i PUnit.unit) := by
  have h1 : ⊤ ≤ (y0 ≫ π) ⁻¹ᵁ (ProjSpace.chart o r (i PUnit.unit) ⊓ ProjSpace.chart o r (j PUnit.unit)) :=
    le_preimage_comp y0 π (inf_le_inf (LB.wchart_le (ProjSpace.O1 o r) (fun _ => π) i PUnit.unit)
      (LB.wchart_le (ProjSpace.O1 o r) (fun _ => π) j PUnit.unit)) h
  refine (TuplePoint.valR_linComb_g y0 (ProjSpace.O1 o r) π 1 i j h).trans ((zpow_one _).trans ?_)
  refine (valR_res (y0 ≫ π) inf_le_left h1 (ProjSpace.ratio o r (i PUnit.unit) (j PUnit.unit))).trans ?_
  exact (GlobalTheory.T.homogeneousCoords_in_standardChart_ratio o L r (y0 ≫ π) t _ ht (le_preimage_mono _ inf_le_left h1)).2 _

open Classical in

def unitOf (M : RatModel k Ω) (U : M.Z.Opens) (x : Ω) (hx : ∀ z ∈ U, x ≠ 0 ∧ x ∈ M.O z ∧ x⁻¹ ∈ M.O z) :
    Γ(M.Z, U)ˣ :=
  if hU : (U : Set M.Z).Nonempty then
    Units.map (M.sectionsEquiv U hU).symm.toMonoidHom
      ⟨⟨x, RatModel.mem_ringOn.2 fun z hz => (hx z hz).2.1⟩, ⟨x⁻¹, RatModel.mem_ringOn.2 fun z hz => (hx z hz).2.2⟩,
        Subtype.ext (mul_inv_cancel₀ (hx _ hU.some_mem).1), Subtype.ext (inv_mul_cancel₀ (hx _ hU.some_mem).1)⟩
  else 1

theorem valR_unitOf {M : RatModel k Ω} {U : M.Z.Opens} {x : Ω} {hx : ∀ z ∈ U, x ≠ 0 ∧ x ∈ M.O z ∧ x⁻¹ ∈ M.O z}
    (h : ⊤ ≤ M.pt ⁻¹ᵁ U) : valR M.pt U (unitOf M U x hx).val = x := by
  have hU : (U : Set M.Z).Nonempty := ⟨_, h (x := IsLocalRing.closedPoint Ω) trivial⟩
  rw [unitOf, dif_pos hU]
  have := M.coe_sectionsEquiv U hU ((M.sectionsEquiv U hU).symm ⟨x, RatModel.mem_ringOn.2 fun z hz => (hx z hz).2.1⟩)
  rw [RingEquiv.apply_symm_apply] at this
  exact this.symm

end GlobalTheory.UMin.CrdSym
end

namespace GlobalTheory.UMin.CrdSym
open GlobalTheory.Points GlobalTheory.ProjSpace

theorem lbIso_symTup : ∀ (k Ω o : Type) [CommRing k] [Field Ω] [Algebra k Ω] [CommRing o] (M : RatModel k Ω) (n : ℕ) (h : M.Z ⟶ PSpace k n) (g : M.Z ⟶ PSpace o n) (c : Fin (n + 1) → Ω), PCrd (M.pt ≫ h) c → PCrd (M.pt ≫ g) (symTup c) → LBIso ((ProjSpace.O1 o n).pull g) (lbPow ((ProjSpace.O1 k n).pull h) (n + 1).factorial) := by
  intro k Ω o _ _ _ _ M n h g c hc he
  set D := (n + 1).factorial
  set L := (ProjSpace.O1 o n).pull g
  set L' := lbPow ((ProjSpace.O1 k n).pull h) D
  have h2 : ∀ a : L'.ι, L'.U a ≤ ((ProjSpace.O1 k n).pull h).U (a PUnit.unit) := fun a =>
    LB.wchart_le ((ProjSpace.O1 k n).pull h) (fun _ => 𝟙 M.Z) a PUnit.unit
  have hL' : ∀ a : L'.ι, L'.U a ≤ h ⁻¹ᵁ ProjSpace.chart k n (a PUnit.unit PUnit.unit) := fun a =>
    (h2 a).trans (LB.wchart_le (ProjSpace.O1 k n) (fun _ => h) _ PUnit.unit)
  have hL : ∀ j : L.ι, L.U j ≤ g ⁻¹ᵁ ProjSpace.chart o n (j PUnit.unit) := fun j =>
    LB.wchart_le (ProjSpace.O1 o n) (fun _ => g) j PUnit.unit
  let x : L'.ι × L.ι → Ω := fun p => symTup c (p.2 PUnit.unit) / c (p.1 PUnit.unit PUnit.unit) ^ D
  have hx : ∀ p : L'.ι × L.ι, ∀ z ∈ (LB.div L' L).U p, x p ≠ 0 ∧ x p ∈ M.O z ∧ (x p)⁻¹ ∈ M.O z := by
    rintro ⟨a, j⟩ z ⟨hza, hzj⟩
    obtain ⟨h1, h3⟩ := div_mem_O hc (hL' a hza)
    obtain ⟨h4, h5⟩ := div_mem_O he (hL j hzj)
    exact GlobalTheory.T.thetaSymmetricFunctions_div_pow_factorial_isUnit k Ω (M.O z) (n + 1) c _ _ h1 h3 h4 h5
  have nzh : ∀ a : L'.ι, ⊤ ≤ M.pt ⁻¹ᵁ L'.U a → c (a PUnit.unit PUnit.unit) ≠ 0 := fun a ha =>
    (GlobalTheory.T.homogeneousCoords_in_standardChart_ratio k Ω n (M.pt ≫ h) c _ hc (le_preimage_comp M.pt h (hL' a) ha)).1
  have nzg : ∀ j : L.ι, ⊤ ≤ M.pt ⁻¹ᵁ L.U j → symTup c (j PUnit.unit) ≠ 0 := fun j hj =>
    (GlobalTheory.T.homogeneousCoords_in_standardChart_ratio o Ω n (M.pt ≫ g) (symTup c) _ he (le_preimage_comp M.pt g (hL j) hj)).1
  let w : LB.Iso L L' := ⟨fun p => unitOf M ((LB.div L' L).U p) (x p) (hx p)⟩
  refine ⟨w, ?_⟩
  rintro ⟨a, j⟩ ⟨a', j'⟩
  refine Units.ext (TuplePoint.ext_of_dense M.pt fun hW => ?_)
  have ha := le_preimage_mono M.pt inf_le_left hW
  have hb := le_preimage_mono M.pt inf_le_right hW
  have hk : ⊤ ≤ M.pt ⁻¹ᵁ (L'.U a ⊓ L'.U a') :=
    le_preimage_mono M.pt (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)) hW
  have hj : ⊤ ≤ M.pt ⁻¹ᵁ (L.U j ⊓ L.U j') :=
    le_preimage_mono M.pt (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)) hW
  have e1 := TuplePoint.valR_linComb_g M.pt ((ProjSpace.O1 k n).pull h) (𝟙 M.Z) D a a' hk
  rw [Category.comp_id, valR_pullO1_g M.pt h hc _ _ (le_preimage_mono M.pt (inf_le_inf (h2 a) (h2 a')) hk),
    zpow_natCast] at e1
  have e2 := valR_pullO1_g M.pt g he j j' hj
  have n1 := nzh a (le_preimage_mono M.pt inf_le_left ha)
  have n2 := nzh a' (le_preimage_mono M.pt inf_le_left hb)
  have n3 := nzg j (le_preimage_mono M.pt inf_le_right ha)
  have n4 := nzg j' (le_preimage_mono M.pt inf_le_right hb)
  refine (TuplePoint.valR_res_unit M.pt _ hW _).trans ((valR_unitOf (hx := hx (a, j)) ha).trans (Eq.symm ?_))
  refine (TuplePoint.valR_mul_unit M.pt hW _ _).trans ?_
  have eg : valR M.pt _ ((LB.div L' L).g (a, j) (a', j')).val =
      (c (a' PUnit.unit PUnit.unit) / c (a PUnit.unit PUnit.unit)) ^ D *
        (symTup c (j' PUnit.unit) / symTup c (j PUnit.unit))⁻¹ := by
    refine (TuplePoint.valR_mul_unit M.pt hW _ _).trans ?_
    exact congrArg₂ (· * ·) ((TuplePoint.valR_res_unit M.pt _ hW _).trans e1)
      ((TuplePoint.valR_inv_unit M.pt hW _).trans (congrArg (·⁻¹) ((TuplePoint.valR_res_unit M.pt _ hW _).trans e2)))
  rw [eg, TuplePoint.valR_res_unit M.pt _ hW, valR_unitOf (hx := hx (a', j')) hb]
  simp only [x]
  rw [div_pow]
  field_simp

end GlobalTheory.UMin.CrdSym
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricPrincipalPolarisationExtendsSemiAbelian
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.SymExtend

open GlobalTheory.CechPic

theorem stalkMap_comp_base {R : Type} [CommRing R] {G : Over (Sp R)} (f : G ⟶ G) (x : G.left) :
    (f.left.stalkMap x).hom.comp ((G.left.presheaf.germ ⊤ (f.left x) trivial).hom.comp ((G.hom.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)) =
      (G.left.presheaf.germ ⊤ x trivial).hom.comp ((G.hom.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) := by
  ext a
  have e := Scheme.Hom.germ_stalkMap_apply f.left ⊤ x trivial
    (G.hom.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
  refine e.trans ?_
  conv_rhs => rw [← Over.w f]
  rfl

theorem exists_open_unit_mul_sq (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hA : AdmBase R (maximalIdeal R))
    (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (L2 : LB G.left) (h2 : L2.IsLB) (h : L2.Sec)
    (Lθ : LB (pullback G.hom (jK R))) (hθ : Lθ.IsLB) (θ : Lθ.Sec) (hc : (∀ j i, ∃ w : Γ(pullback G.hom (jK R), pullback.fst G.hom (jK R) ⁻¹ᵁ L2.U j ⊓ Lθ.U i)ˣ, ((pullback G.hom (jK R)).presheaf.map (homOfLE inf_le_right).op).hom (θ.f i) ^ 2 = (w : Γ(pullback G.hom (jK R), pullback.fst G.hom (jK R) ⁻¹ᵁ L2.U j ⊓ Lθ.U i)) * ((pullback G.hom (jK R)).presheaf.map (homOfLE inf_le_left).op).hom (((pullback.fst G.hom (jK R)).app (L2.U j)).hom (h.f j)))) (hs : (∀ (x' : G.left) (k : L2.ι), ((𝟙 G) ^ 2 : G ⟶ G).left x' ∈ L2.U k → gs ((𝟙 G) ^ 2 : G ⟶ G).left x' (L2.U k) (h.f k) ≠ 0 ∧ ∃ (u : (G.left.presheaf.stalk x')ˣ) (g : G.left.presheaf.stalk x'), gs ((𝟙 G) ^ 2 : G ⟶ G).left x' (L2.U k) (h.f k) = u * g ^ 2))
    (x : G.left) (hx : G.hom x = closedPoint R) :
    ∃ V : G.left.Opens, x ∈ V ∧ ∃ a : Γ(G.left, V), a ≠ 0 ∧ ∀ j, ∃ u : Γ(G.left, V ⊓ L2.U j)ˣ, (G.left.presheaf.map (homOfLE inf_le_right).op).hom (h.f j) = (u : Γ(G.left, V ⊓ L2.U j)) * (G.left.presheaf.map (homOfLE inf_le_left).op).hom a ^ 2 := by
  have hfl := (GlobalTheory.SemiAbMulFlat.flat_and_locallyQuasiFinite_pow _ G hG 2 two_ne_zero).1
  have hsu := GlobalTheory.SemiAbSurj.surjective_pow _ G hG 2 two_ne_zero
  generalize ((𝟙 G) ^ 2 : G ⟶ G) = f at hs hfl hsu
  obtain ⟨x', rfl⟩ := f.left.surjective x
  have hx' : G.hom x' = closedPoint R := by
    rw [← hx, ← Scheme.Hom.comp_apply, Over.w f]
  obtain ⟨hD, hN, hIC⟩ := GlobalTheory.SquareNear.stalk_props R hA G hG (f.left x')
  obtain ⟨hD', hN', hIC'⟩ := GlobalTheory.SquareNear.stalk_props R hA G hG x'
  obtain ⟨k, hk⟩ := exists_chart h2 (f.left x')
  obtain ⟨hne, u, g, hug⟩ := hs x' k hk
  rw [gs_stalkMap _ _ _ hk, gs_eq (𝟙 G.left) (f.left x') _ hk] at hne hug
  let _ := (f.left.stalkMap x').hom.toAlgebra
  have : Module.Flat (G.left.presheaf.stalk (f.left x')) (G.left.presheaf.stalk x') := Flat.stalkMap f.left x'
  have : IsLocalHom (algebraMap (G.left.presheaf.stalk (f.left x')) (G.left.presheaf.stalk x')) :=
    inferInstanceAs (IsLocalHom (f.left.stalkMap x').hom)
  have : Module.FaithfullyFlat (G.left.presheaf.stalk (f.left x')) (G.left.presheaf.stalk x') :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hne₀ : (G.left.presheaf.germ (L2.U k) (f.left x') hk).hom (h.f k) ≠ 0 := fun e =>
    hne ((congrArg (f.left.stalkMap x').hom e).trans (map_zero _))
  have hsq : ∃ (u : (G.left.presheaf.stalk x')ˣ) (g : G.left.presheaf.stalk x'),
      algebraMap (G.left.presheaf.stalk (f.left x')) (G.left.presheaf.stalk x')
        ((G.left.presheaf.germ (L2.U k) (f.left x') hk).hom (h.f k)) = u * g ^ 2 := ⟨u, g, hug⟩
  have hinj := GlobalTheory.Mum.LocalInj.base_to_stalk_injective R hA G hG (f.left x')
  have hpr := GlobalTheory.Mum.ideal_map_stalk_isPrime_of_closedPoint R hA G hG (f.left x') hx
  have hpr' := GlobalTheory.Mum.ideal_map_stalk_isPrime_of_closedPoint R hA G hG x' hx'
  have hhor := GlobalTheory.SqHorizontal.horizontal R hA G hG L2 h Lθ hθ θ hc (f.left x') k hk
  rw [← stalkMap_comp_base f x'] at hpr'
  generalize ((G.left.presheaf.germ ⊤ (f.left x') trivial).hom.comp ((G.hom.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)) = σ at hinj hpr hpr' hhor
  have Hp : ∀ p : Ideal (G.left.presheaf.stalk (f.left x')), p.IsPrime → p.height = 1 →
      ∃ a b c : G.left.presheaf.stalk (f.left x'), b ∉ p ∧ c ∉ p ∧
        b * (G.left.presheaf.germ (L2.U k) (f.left x') hk).hom (h.f k) = c * a ^ 2 := by
    intro p hp h1
    by_cases hq : Ideal.comap σ p = ⊥
    · exact hhor p hp hq
    · have hqp : (Ideal.comap σ p).IsPrime := Ideal.comap_isPrime _ p
      have hP := hpr _ hqp
      have heq : Ideal.map σ (Ideal.comap σ p) = p := by
        by_contra hne'
        have hlt := lt_of_le_of_ne (Ideal.map_comap_le (f := σ) (K := p)) hne'
        have h1' : (Ideal.map σ (Ideal.comap σ p)).height < 1 :=
          (Ideal.height_strict_mono_of_isPrime hlt).trans_le h1.le
        rw [ENat.lt_one_iff_eq_zero, Ideal.height_eq_zero_iff_eq_bot] at h1'
        exact hq ((Ideal.map_eq_bot_iff_of_injective hinj).1 h1')
      refine GlobalTheory.T.exists_mul_eq_mul_sq_of_faithfullyFlat_height_one _ _ _ hne₀ hsq p hp h1 ?_
      have := hpr' _ hqp
      rwa [← Ideal.map_map, heq] at this
  obtain ⟨u₀, a, hua⟩ := isUnit_mul_sq_of_faithfullyFlat _ (G.left.presheaf.stalk x') _ hne₀ hsq Hp
  have ha : a ≠ 0 := by
    rintro rfl
    apply hne₀
    rw [hua]
    simp
  exact GlobalTheory.Mum.unit_mul_sq_spread G.left L2 h (f.left x') k hk u₀ a ha hua

theorem exists_unit_mul_of_sq_sec {X : Scheme.{0}} [IsIntegral X] [GlobalTheory.IsNormalScheme X] (W : X.Opens)
    {s t : Γ(X, W)} (c : Γ(X, W)ˣ) (ht : Nonempty W → t ≠ 0) (h : s ^ 2 = c * t ^ 2) :
    ∃ w : Γ(X, W)ˣ, s = w * t := by
  by_cases hW : Nonempty W
  · have ht := ht hW
    have h1 : t ∣ s := (IsIntegrallyClosed.pow_dvd_pow_iff two_ne_zero).1 ⟨c, by rw [h, mul_comm]⟩
    have h2 : s ∣ t := (IsIntegrallyClosed.pow_dvd_pow_iff two_ne_zero).1
      ⟨(c⁻¹ : Γ(X, W)ˣ), by rw [h, mul_right_comm, Units.mul_inv, _root_.one_mul]⟩
    obtain ⟨w, hw⟩ := associated_of_dvd_dvd h1 h2
    exact ⟨w, by rw [← hw, mul_comm]⟩
  · obtain rfl : W = ⊥ := by
      ext x
      simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun hx => hW ⟨⟨x, hx⟩⟩
    exact ⟨1, Subsingleton.elim _ _⟩

theorem res_ne_zero {X : Scheme.{0}} [IsIntegral X] {V W : X.Opens} (hW : W ≤ V) {a : Γ(X, V)} (ha : a ≠ 0)
    [Nonempty W] : (X.presheaf.map (homOfLE hW).op).hom a ≠ 0 := fun h0 =>
  ha (map_injective_of_isIntegral X (homOfLE hW) (h0.trans (map_zero _).symm))

theorem res_mem_nonZeroDivisors {X : Scheme.{0}} [IsIntegral X] {V W : X.Opens} (hW : W ≤ V) {a : Γ(X, V)}
    (ha : a ≠ 0) : (X.presheaf.map (homOfLE hW).op).hom a ∈ nonZeroDivisors Γ(X, W) := by
  by_cases hn : Nonempty W
  · exact mem_nonZeroDivisors_of_ne_zero (res_ne_zero hW ha)
  · obtain rfl : W = ⊥ := by
      ext x
      simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun hx => hn ⟨⟨x, hx⟩⟩
    rw [Subsingleton.elim ((X.presheaf.map (homOfLE hW).op).hom a) 1]
    exact Submonoid.one_mem _

theorem extends_near (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hA : AdmBase R (maximalIdeal R))
    (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (L2 : LB G.left) (h2 : L2.IsLB) (h : L2.Sec)
    (Lθ : LB (pullback G.hom (jK R))) (hθ : Lθ.IsLB) (θ : Lθ.Sec) (hc : (∀ j i, ∃ w : Γ(pullback G.hom (jK R), pullback.fst G.hom (jK R) ⁻¹ᵁ L2.U j ⊓ Lθ.U i)ˣ, ((pullback G.hom (jK R)).presheaf.map (homOfLE inf_le_right).op).hom (θ.f i) ^ 2 = (w : Γ(pullback G.hom (jK R), pullback.fst G.hom (jK R) ⁻¹ᵁ L2.U j ⊓ Lθ.U i)) * ((pullback G.hom (jK R)).presheaf.map (homOfLE inf_le_left).op).hom (((pullback.fst G.hom (jK R)).app (L2.U j)).hom (h.f j)))) (hs : (∀ (x' : G.left) (k : L2.ι), ((𝟙 G) ^ 2 : G ⟶ G).left x' ∈ L2.U k → gs ((𝟙 G) ^ 2 : G ⟶ G).left x' (L2.U k) (h.f k) ≠ 0 ∧ ∃ (u : (G.left.presheaf.stalk x')ˣ) (g : G.left.presheaf.stalk x'), gs ((𝟙 G) ^ 2 : G ⟶ G).left x' (L2.U k) (h.f k) = u * g ^ 2)) :
    ∃ (O : G.left.Opens) (N : LB O.toScheme), (∀ g : G.left, G.hom g = closedPoint R → g ∈ O) ∧ N.IsLB ∧
      LBIso (N.pull (pullback.fst O.ι (pullback.fst G.hom (jK R)))) (Lθ.pull (pullback.snd O.ι (pullback.fst G.hom (jK R)))) := by
  have hY := fun (x : {x : G.left // G.hom x = closedPoint R}) =>
    exists_open_unit_mul_sq R hA G hG L2 h2 h Lθ hθ θ hc hs x.1 x.2
  choose V hxV a ha hu using hY
  obtain ⟨hsq, hθa⟩ := GlobalTheory.SqGlue.main R hA G hG L2 h2 h _ θ hc _ V a ha hu
  haveI : IsIntegrallyClosed R := hA.2.2.1
  haveI : IsNoetherianRing R := hA.1
  haveI : Smooth G.hom := hG.smooth
  haveI : GeometricallyConnected G.hom := hG.geomConnected
  haveI : IsIntegral G.left := GlobalTheory.isIntegral_left_of_isSemiAbelian G
  haveI : GlobalTheory.IsNormalScheme G.left := GlobalTheory.isNormalScheme_of_smooth G.hom
  haveI : IsIntegral (pullback G.hom (jK R)) := GlobalTheory.isIntegral_pullback_of_smooth G.hom (jK R)
  haveI : GlobalTheory.IsNormalScheme (pullback G.hom (jK R)) := GlobalTheory.isNormalScheme_of_smooth (pullback.snd G.hom (jK R))
  have hgen : ∀ k, ((pullback.fst G.hom (jK R)).app (V k)).hom (a k) ≠ 0 := fun k h0 =>
    ha k (GlobalTheory.ExpInt.generic_app_injective G (V k) (h0.trans (map_zero _).symm))
  obtain ⟨O, N, hO, hN, hiso⟩ := GlobalTheory.LocalEqGlue.exists_lb_of_localEq G.left _ (pullback.fst G.hom (jK R)) Lθ θ _ V a
    (fun k W hW => res_mem_nonZeroDivisors hW (ha k)) (fun k W hW => res_mem_nonZeroDivisors hW (hgen k))
    (fun k l => by
      obtain ⟨c, hc⟩ := hsq k l
      exact exists_unit_mul_of_sq_sec _ c (fun _ => res_ne_zero _ (ha l)) hc)
    (fun k i => by
      obtain ⟨w, hw⟩ := hθa k i
      exact exists_unit_mul_of_sq_sec _ w (fun _ => res_ne_zero _ (hgen k)) hw)
  exact ⟨O, N, fun g hg => hO ⟨g, hg⟩ (hxV ⟨g, hg⟩), hN, hiso⟩

theorem exists_odd_sec {X : Scheme.{0}} [Nonempty X] {L : LB X} (hL : GlobalTheory.IsAmpleLB L) :
    ∃ (t : ℕ) (θ : (lbPow L (2 * t + 1)).Sec) (i : (lbPow L (2 * t + 1)).ι), θ.f i ≠ 0 := by
  obtain ⟨t, ht⟩ := Filter.eventually_atTop.1 (GlobalTheory.CutOutSections.eventually_isGenerated_lbPow hL)
  obtain ⟨θ, hθ⟩ := (ht (2 * t + 1) (by omega)).exists_mem (Classical.arbitrary X)
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hθ
  refine ⟨t, θ, i, fun e => ?_⟩
  rw [e, Scheme.basicOpen_zero] at hi
  exact hi

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ∀ PP : LB (G2 G).left, ExtLam G (A.L.pull gen.hom.left) PP → ∃ L₁ : LB G.left, L₁.IsLB ∧ LBIso (L₁.pull (pullback.fst G.hom (jK R))) (A.L.pull gen.hom.left) := by
  intro R _ _ _ hA G _ _ hG A gen hgen PP hext
  have hL : (A.L.pull gen.hom.left).IsLB := LB.isLB_pull A.isLB _
  have hP : (PP.pull (lift (𝟙 G) (𝟙 G) : G ⟶ G2 G).left).IsLB := LB.isLB_pull hext.1 _
  obtain ⟨h2c, φ, hφ, h4c⟩ := GlobalTheory.T.two_smul_polarisation_class_generic_diagonal_doubling R G A gen hgen PP hext _ _ hL hP rfl rfl
  haveI : Smooth G.hom := hG.smooth
  haveI : GeometricallyConnected G.hom := hG.geomConnected
  haveI : IsIntegral (pullback G.hom (jK R)) := GlobalTheory.isIntegral_pullback_of_smooth G.hom (jK R)
  haveI : IsIso gen.hom.left := inferInstanceAs (IsIso ((Over.forget _).map gen.hom))
  have hamp : GlobalTheory.IsAmpleLB (X := pullback G.hom (jK R)) (A.L.pull gen.hom.left) :=
    (GlobalTheory.isAmpleLB_of_relAmple_of_isAffine A.A A.isLB A.ample).pull_of_isAffineHom gen.hom.left
  have hK : Function.Surjective (pullback.snd G.hom (jK R)).appTop.hom := by
    have e : pullback.snd G.hom (jK R) = gen.hom.left ≫ A.A.hom := (Over.w gen.hom).symm
    haveI : IsIso gen.hom.left.appTop := inferInstanceAs (IsIso (gen.hom.left.app ⊤))
    rw [e, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp]
    exact (ConcreteCategory.bijective_of_isIso gen.hom.left.appTop).2.comp (GlobalTheory.ExpansionTotal.globalFns _ A.A A.isAb).2
  obtain ⟨t, θ, hθ⟩ := exists_odd_sec hamp
  generalize (PP.pull (lift (𝟙 G) (𝟙 G) : G ⟶ G2 G).left) = P at hP h2c
  have hLθ := GlobalTheory.isLB_lbPow hL (2 * t + 1)
  have hL2 := GlobalTheory.isLB_lbPow hP (2 * t + 1)
  have eθ := cls_lbPow hL (2 * t + 1) hLθ
  obtain ⟨h, hc, hs⟩ := exists_sec_sq_of_double R hA G hG hK _ hLθ θ hθ _ hL2
    (by rw [cls_lbPow hP, map_nsmul, ← h2c, smul_comm]; exact congrArg (2 • ·) eθ) φ hφ
    (by
      refine (congrArg (pull φ) eθ).trans (Eq.trans ?_ (congrArg (4 • ·) eθ).symm)
      rw [map_nsmul, smul_comm]
      exact congrArg ((2 * t + 1) • ·) h4c)
  obtain ⟨O, N, hO, hN, hiso⟩ := extends_near R hA G hG _ hL2 h _ hLθ θ hc hs
  obtain ⟨N', hN', eN'⟩ := cls_surj (cls N hN - t • pull O.ι (cls P hP))
  have e₁ := (cls_eq_iff (LB.isLB_pull hN _) (LB.isLB_pull hLθ _)).2 hiso
  rw [cls_pull hN, cls_pull hLθ] at e₁
  obtain ⟨L', hL', hI⟩ := GlobalTheory.Mum.lb_extends_of_extLam R hA G hG _ PP hL hext O hO N' hN'
    ((cls_eq_iff (LB.isLB_pull hN' _) (LB.isLB_pull hL _)).1 (by
      rw [cls_pull hN', eN', map_sub, e₁, map_nsmul, ← pull_comp, pullback.condition, pull_comp, ← h2c]
      refine Eq.trans ?_ (cls_pull hL _ _).symm
      refine (congrArg (fun z => pull (pullback.snd O.ι (pullback.fst G.hom (jK R))) z - _) eθ).trans ?_
      rw [map_nsmul, map_nsmul, smul_smul, add_smul, one_smul, mul_comm t 2, add_sub_cancel_left]))
  exact ⟨L', hL', hI.symm⟩

end GlobalTheory.SymExtend
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TMulOfBox
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif

namespace GlobalTheory.ProdUnif

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.SumDeg

theorem tMul_of_box : ∀ (R : Type) [CommRing R] [IsDomain R] (D D₁ D₂ : DegPre R) (p₁ : D.P.A ⟶ D₁.P.A) (p₂ : D.P.A ⟶ D₂.P.A) (q₁ : D.X →+ D₁.X) (q₂ : D.X →+ D₂.X), IsSumDeg D D₁ D₂ p₁ p₂ q₁ q₂ → ∀ (w : LB.Iso D.P.L (extLB D₁.P.L D₂.P.L p₁.left p₂.left)), IsBoxGen (φ := thφ D.P.A (x3 D.P.A)) (φ₁ := thφ D₁.P.A (x3 D₁.P.A)) (φ₂ := thφ D₂.P.A (x3 D₂.P.A)) (ε := thε) w (p₁ ⊗ₘ p₁ ⊗ₘ p₁).left (p₂ ⊗ₘ p₂ ⊗ₘ p₂).left D.cub.t D₁.cub.t D₂.cub.t → ∀ (T T₁ T₂ : Over (Sp R)) (P : T ⟶ D.P.A) (P₁ : T₁ ⟶ D₁.P.A) (P₂ : T₂ ⟶ D₂.P.A) (ρ₁ : T ⟶ T₁) (ρ₂ : T ⟶ T₂), P ≫ p₁ = ρ₁ ≫ P₁ → P ≫ p₂ = ρ₂ ≫ P₂ → ∀ (t : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (D.Oφ P χ) Oinvε)) (t₁ : ∀ χ : D₁.X, LB.Gen (LB.LinComb D₁.P.L (D₁.Oφ P₁ χ) Oinvε)) (t₂ : ∀ χ : D₂.X, LB.Gen (LB.LinComb D₂.P.L (D₂.Oφ P₂ χ) Oinvε)), (∀ x, IsBoxGen w ρ₁.left ρ₂.left (t x) (t₁ (q₁ x)) (t₂ (q₂ x))) → TMul D₁ P₁ t₁ → TMul D₂ P₂ t₂ → TMul D P t := by
  intro R _ _ D D₁ D₂ p₁ p₂ q₁ q₂ hS w hc T T₁ T₂ P P₁ P₂ ρ₁ ρ₂ e₁ e₂ t t₁ t₂ hb h₁ h₂ χ χ'
  haveI := hS.hom₁
  haveI := hS.hom₂
  refine corr_of_val D.P.isLB fun y J hJ => ?_
  obtain ⟨J₁, hJ₁⟩ := GlobalTheory.BoxFamily.exists_good_at D₁.P.isLB y
  obtain ⟨J₂, hJ₂⟩ := GlobalTheory.BoxFamily.exists_good_at D₂.P.isLB y
  have B : ∀ x, (om w y J₁ J₂ J (P * cP D T x).left)⁻¹ * om w y J₁ J₂ J (cP D T x).left * om w y J₁ J₂ J P.left *
      (om w y J₁ J₂ J (1 : T ⟶ D.P.A).left)⁻¹ * val (t x) (𝟙 T.left) y J =
      val (t₁ (q₁ x)) ρ₁.left y J₁ * val (t₂ (q₂ x)) ρ₂.left y J₂ := fun x => by
    have := hb x T.left (𝟙 T.left) y J₁ J₂ J hJ₁ hJ₂ hJ
    simp only [Category.id_comp] at this
    rwa [GlobalTheory.TorusCoordPull.prod_O D P x (om w y J₁ J₂ J)] at this
  have K₁ : (lift (cP D T χ) (lift (cP D T χ') P)).left ≫ (p₁ ⊗ₘ p₁ ⊗ₘ p₁).left =
      ρ₁.left ≫ (lift (cP D₁ T₁ (q₁ χ)) (lift (cP D₁ T₁ (q₁ χ')) P₁)).left := by
    rw [groupObj_lift3_comp_tensorCube_monHom, cPoint_pr hS.c_pr₁, cPoint_pr hS.c_pr₁, e₁, ← comp_cP D₁ ρ₁ (q₁ χ), ← comp_cP D₁ ρ₁ (q₁ χ'),
      ← comp_lift, ← comp_lift, Over.comp_left]
  have K₂ : (lift (cP D T χ) (lift (cP D T χ') P)).left ≫ (p₂ ⊗ₘ p₂ ⊗ₘ p₂).left =
      ρ₂.left ≫ (lift (cP D₂ T₂ (q₂ χ)) (lift (cP D₂ T₂ (q₂ χ')) P₂)).left := by
    rw [groupObj_lift3_comp_tensorCube_monHom, cPoint_pr hS.c_pr₂, cPoint_pr hS.c_pr₂, e₂, ← comp_cP D₂ ρ₂ (q₂ χ), ← comp_cP D₂ ρ₂ (q₂ χ'),
      ← comp_lift, ← comp_lift, Over.comp_left]
  have C0 := hc T.left (lift (cP D T χ) (lift (cP D T χ') P)).left y J₁ J₂ J hJ₁ hJ₂ hJ
  rw [K₁, K₂] at C0
  have pc := prod_cub (cP D T χ) (cP D T χ') P (om w y J₁ J₂ J)
  have C : (om w y J₁ J₂ J (cP D T χ * cP D T χ' * P).left * (om w y J₁ J₂ J (cP D T χ * cP D T χ').left)⁻¹ *
      (om w y J₁ J₂ J (cP D T χ * P).left)⁻¹ * (om w y J₁ J₂ J (cP D T χ' * P).left)⁻¹ *
      om w y J₁ J₂ J (cP D T χ).left * om w y J₁ J₂ J (cP D T χ').left * om w y J₁ J₂ J P.left *
      (om w y J₁ J₂ J (1 : T ⟶ D.P.A).left)⁻¹) * val D.cub.t (lift (cP D T χ) (lift (cP D T χ') P)).left y J =
      val D₁.cub.t (ρ₁.left ≫ (lift (cP D₁ T₁ (q₁ χ)) (lift (cP D₁ T₁ (q₁ χ')) P₁)).left) y J₁ *
      val D₂.cub.t (ρ₂.left ≫ (lift (cP D₂ T₂ (q₂ χ)) (lift (cP D₂ T₂ (q₂ χ')) P₂)).left) y J₂ := by
    rw [← pc]; exact C0
  have M₁ : val (t₁ (q₁ χ + q₁ χ')) ρ₁.left y J₁ *
      val D₁.cub.t (ρ₁.left ≫ (lift (cP D₁ T₁ (q₁ χ)) (lift (cP D₁ T₁ (q₁ χ')) P₁)).left) y J₁ =
      val (t₁ (q₁ χ)) ρ₁.left y J₁ * val (t₁ (q₁ χ')) ρ₁.left y J₁ := by
    have := (val_mul hJ₁ _ _ _).symm.trans ((val_corr hJ₁ (h₁ (q₁ χ) (q₁ χ')) ρ₁.left).trans (val_mul hJ₁ _ _ _))
    refine Eq.trans ?_ this
    exact congrArg₂ (· * ·) rfl (val_pull hJ₁ _ _ _).symm
  have M₂ : val (t₂ (q₂ χ + q₂ χ')) ρ₂.left y J₂ *
      val D₂.cub.t (ρ₂.left ≫ (lift (cP D₂ T₂ (q₂ χ)) (lift (cP D₂ T₂ (q₂ χ')) P₂)).left) y J₂ =
      val (t₂ (q₂ χ)) ρ₂.left y J₂ * val (t₂ (q₂ χ')) ρ₂.left y J₂ := by
    have := (val_mul hJ₂ _ _ _).symm.trans ((val_corr hJ₂ (h₂ (q₂ χ) (q₂ χ')) ρ₂.left).trans (val_mul hJ₂ _ _ _))
    refine Eq.trans ?_ this
    exact congrArg₂ (· * ·) rfl (val_pull hJ₂ _ _ _).symm
  have B0 := B (χ + χ')
  have Ba := B χ
  have Bb := B χ'
  rw [map_add, map_add, cPoint_add,
    show P * (cP D T χ * cP D T χ') = cP D T χ * cP D T χ' * P from mul_comm _ _] at B0
  rw [show P * cP D T χ = cP D T χ * P from mul_comm _ _] at Ba
  rw [show P * cP D T χ' = cP D T χ' * P from mul_comm _ _] at Bb
  refine ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl ((val_pull hJ _ _ _).trans
    (congrArg (fun r => val D.cub.t r y J) (Category.id_comp _))))).trans (Eq.trans ?_ (val_mul hJ _ _ _).symm)
  show val (t (χ + χ')) (𝟙 T.left) y J * val D.cub.t (lift (cP D T χ) (lift (cP D T χ') P)).left y J =
    val (t χ) (𝟙 T.left) y J * val (t χ') (𝟙 T.left) y J
  apply Additive.ofMul.injective
  have a0 := congrArg Additive.ofMul B0
  have a1 := congrArg Additive.ofMul Ba
  have a2 := congrArg Additive.ofMul Bb
  have a3 := congrArg Additive.ofMul C
  have a4 := congrArg Additive.ofMul M₁
  have a5 := congrArg Additive.ofMul M₂
  simp only [ofMul_mul, ofMul_inv] at a0 a1 a2 a3 a4 a5 ⊢
  linear_combination (norm := abel) a0 + a3 - a1 - a2 + a4 + a5

end GlobalTheory.ProdUnif
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TailWeightLineNef
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi)
open GlobalTheory.HSApp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NefStep

theorem isNef_tailWt : GlobalTheory.Published.SemiAbelianLieSeminegative → GlobalTheory.CovTop.Hypotheses₂ → GlobalTheory.Published.NefNumerics → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed Xo c → ∀ (τ : Psi H) (k : ℕ), Dw.p ≤ k → k + 1 < Dw.p + Dw.q → letI := algebraΓOfHom (str₀ TF.X Z); IsNef c.F (L₀ TF.X Z (GlobalTheory.NefWt.tailWt τ k)) := by
  intro h _ hN E _ _ _ H Dw l Xo c TF Z _ τ k hk _
  letI := algebraΓOfHom (str₀ TF.X Z)
  rw [L₀_tailWt TF.X Z τ k hk]
  have hq := FlagMod.mult_conj (Dw := Dw) τ
  exact isNef_pull_LL_stepEx TF.X.F h hN.1 c.F (inc₀ TF.X Z) _ (by omega)

end GlobalTheory.NefStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalBaseDataPullbackAlongMapStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tautological_base_data_pullback_along_map : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (θ : R →+* V) (iw : W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (Q : Data R) (e : Q.X ≃+ (Fin T.r → ℤ)) (Q' : Data V) (e' : Q'.X ≃+ (Fin T.r → ℤ)), (∀ i, θ (s i) ≠ 0) → DataFrom T iw s ε n Q e → DataFrom T (θ.comp iw) (fun i => θ (s i)) ε n Q' e' → PullData Q θ Q' (e'.trans e.symm) := by
  first | exact @GlobalTheory.PullFrom.pullData_of_dataFrom | exact GlobalTheory.PullFrom.pullData_of_dataFrom | (intros; apply GlobalTheory.PullFrom.pullData_of_dataFrom <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalLatticeIdentificationEqIdStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tautological_lattice_identification_eq_id : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) (ψ : InvFun ℤ) (m N n : ℕ) (ε : (Fin m ⊕ Fin N) → LinearMap.BilinForm ℤ (Fin T.r → ℤ)), 3 ≤ n → IsCone id ψ (fun k => ε (.inl k)) → (∀ x, x ≠ 0 → ∃ k, 0 < ε (.inl k) x x) → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D₁ D₂ : DegPre V) (ω₁ : W →+* V) (s₁ : (Fin m ⊕ Fin N) → V) (e₁ : D₁.X ≃+ (Fin T.r → ℤ)) (β₁ : D₁.P.A.left ⟶ T.B.left) (ββ₁ : (G2 D₁.P.A).left ⟶ (G2 T.B).left) (w₁ : LB.Iso (abelian₂ D₁.P.A D₁.P.L) ((abelian₂ T.B T.M.L).pull ββ₁)) (ω₂ : W →+* V) (s₂ : (Fin m ⊕ Fin N) → V) (e₂ : D₂.X ≃+ (Fin T.r → ℤ)) (β₂ : D₂.P.A.left ⟶ T.B.left) (ββ₂ : (G2 D₂.P.A).left ⟶ (G2 T.B).left) (w₂ : LB.Iso (abelian₂ D₂.P.A D₂.P.L) ((abelian₂ T.B T.M.L).pull ββ₂)) (b : D₁.P.A ⟶ D₂.P.A) (φ : D₁.X ≃+ D₂.X) (F : Type) [Field F] [Algebra (FractionRing V) F], D₁.TauBimult → D₂.TauBimult → From T ω₁ s₁ ε n D₁ e₁ β₁ ββ₁ w₁ → From T ω₂ s₂ ε n D₂ e₂ β₂ ββ₂ w₂ → (∀ k, s₁ (.inl k) ∈ maximalIdeal V ∧ s₁ (.inl k) ≠ 0) → (∀ k, IsUnit (s₁ (.inr k))) → (∀ k, s₂ (.inl k) ∈ maximalIdeal V ∧ s₂ (.inl k) ≠ 0) → (∀ k, IsUnit (s₂ (.inr k))) → Match D₁ D₂ b φ F → (∀ a : Fin T.r → ℤ, ∃ (p₁ : QkPt D₁ F n) (p₂ : QkPt D₂ F n), p₁.y = e₁.symm a ∧ TautPt T ω₁ s₁ ε n D₁ e₁ β₁ ββ₁ w₁ F a p₁.g ∧ p₂.y = e₂.symm a ∧ TautPt T ω₂ s₂ ε n D₂ e₂ β₂ ββ₂ w₂ F a p₂.g ∧ QImg b φ p₁ p₂) → ∀ y, e₂ (φ y) = e₁ y := by
  first | exact @GlobalTheory.TInj.lattice_iso_eq_of_tautPts | exact GlobalTheory.TInj.lattice_iso_eq_of_tautPts | (intros; apply GlobalTheory.TInj.lattice_iso_eq_of_tautPts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoIntegralLogAddInvStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_integral_log_add_inv_succ : ∀ (T : Type) [MeasurableSpace T] (μ : Measure T) [IsFiniteMeasure μ] (w : T → ℝ) (C : ℝ), Measurable w → (∀ x, 0 ≤ w x ∧ w x ≤ C) → (∀ᵐ x ∂μ, 0 < w x) → Integrable (fun x => Real.log (w x) / 2) μ → Tendsto (fun n : ℕ => ∫ x, Real.log (w x + 1 / ((n : ℝ) + 1)) ∂μ) atTop (𝓝 (2 * ∫ x, Real.log (w x) / 2 ∂μ)) := by
  first | exact @GlobalTheory.Mix.tendsto_integral_log_add_inv | exact GlobalTheory.Mix.tendsto_integral_log_add_inv | (intros; apply GlobalTheory.Mix.tendsto_integral_log_add_inv <;> assumption)
end

