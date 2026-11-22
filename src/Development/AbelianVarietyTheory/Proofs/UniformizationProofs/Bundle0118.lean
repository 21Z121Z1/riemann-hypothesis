import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ArcDataSpecialiseAtUniformiser
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0117
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0061
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0057
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0111
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0089
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0081
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0056
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0077
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0047
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ProportionalField
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ProportionalRaw
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FiniteOfNotLinearIndependent
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FinrankTotalDegreeImageGrowth
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0009
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0028
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GenericIsoAgreesOnCompletePoints
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0016
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0013
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety
import Development.AbelianVarietyTheory.Definitions.Uniformization.FinrankComplexReal
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0003
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0068
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0087
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0108
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0094
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0074

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ArcDataSpecialiseAtUniformiserStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arcData_specialise_at_uniformiser : Laws → Laws2 → DVR.TwistBaseChangeStatement → UnifBaseChangeSt → Laws5 → ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Geo.Tor.Host E) (Dm : Geo.Tor.Datum H) (l : Geo.Tor.Level H) (Xo : Geo.Tor.Moduli Dm l) (c : Geo.Tor.Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Geo.Tor.Model Xo c β) (V : Type) [CommRing V] [IsDomain V] [CharZero V] [IsDiscreteValuationRing V] (b : O →+* V) (ϖ : V) (a : Geo.Tor.ArcIn Dm l β V b), Irreducible ϖ → IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (ev : PowerSeries V →+* V), (∀ x, ev (PowerSeries.C x) = x) → ev PowerSeries.X = ϖ → ∀ χ : Geo.Tor.Sp (PowerSeries V) ⟶ Y.X, χ ≫ Y.s = Geo.Tor.spMap (PowerSeries.C (R := V)) ≫ Geo.Tor.spMap b → Set.range (jK V ≫ Geo.Tor.spMap ev ≫ χ) ⊆ Set.range Y.j → Y.HasArcData a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := V)) PowerSeries.X χ → Y.HasArcData a (Ideal.span {ϖ}) (RingHom.id V) ϖ (Geo.Tor.spMap ev ≫ χ) := by
  first | exact @GlobalTheory.hasArcData_specialise | exact GlobalTheory.hasArcData_specialise | (intros; apply GlobalTheory.hasArcData_specialise <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.DescendedBundleAmpleSpecialFibreStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.descended_bundle_ample_special_fibre : (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g n : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → (n : k) ≠ 0 → Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} = n ^ (2 * g)) → Laws → AllSet fun s => ∀ t : Tower s, RelAmple (t.l 0).Q.B (t.l 0).D.M.L.L := by
  first | exact @GlobalTheory.UU.AmpleZero.relAmple_zero | exact GlobalTheory.UU.AmpleZero.relAmple_zero | (intros; apply GlobalTheory.UU.AmpleZero.relAmple_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpansionComponentsProportionalShiftMultiple
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.UU.SchurComp

set_option maxHeartbeats 1000000 in

theorem components_proportional : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {_} {_} _ _ U => ∀ N : ℕ, 1 ≤ N → ∀ (α mu : D.X) (u : LB.Gen (LB.LinComb D.P.L (DegPre.deltaφ D (Kbar V) N α mu) (DegPre.deltaε N))), u.IsGen → U.Supp (Kbar V) N α → ∃ a : Kbar V, ∀ t s, U.ExpF (Kbar V) N t s → ∀ z J, Good D.P.L z J → sval (s (α + N • mu)) (𝟙 _) z J = gs (𝟙 _) z ⊤ (DegPre.constBF D (Kbar V) a ⊤) * (sval (s α) (DegPre.trF D (Kbar V) mu).left z J * (val u (𝟙 _) z J).val)) := by
  intro hL hL2 V _ _ _ hV D A G _ _ U N hN α mu u hu hS
  have := hV.1
  have := hV.2.2
  have hN0 : N ≠ 0 := by omega
  have hNF : (N : Kbar V) ≠ 0 := Nat.cast_ne_zero.2 hN0
  obtain ⟨Φ, e, hfr, hθ, hmul, hcomm, hnd⟩ :=
    GlobalTheory.ThetaRep.exists_projective_rep hL hL2 _ A (Kbar V) (jFK (R := V) (Kbar V)) N hNF
  obtain ⟨m, hm, hact, -⟩ := GlobalTheory.UU.Eqv.main hL hL2 V hV D A G U N hN
  obtain ⟨hw1, hw2, hw3⟩ := GlobalTheory.T.lineBundleSections_torusTorsion_weightSpaces hL hL2 V hV D A G U N hN
  have huniq := GlobalTheory.UU.ExpFUniq.main V hV D A G U (Kbar V) N
  choose xp hxp using GlobalTheory.UU.ExpTotal.expF_total hL hL2 V hV D A G U (Kbar V) N hN
  have hcA := (hL.mulN _ A N hN).2.2.2.2 (Kbar V) (jFK (R := V) (Kbar V)) hNF
  have hcH := (GlobalTheory.GtCount.card_gtTors hL hL2 V D (Kbar V) N hNF).1
  have hg : A.g = D.P.g + D.rank := GlobalTheory.UU.PreU.dim_eq V hV D A G U
  have hlinF := ExpLin.expF_linear V hV D A G U (Kbar V) N
  have hbas := exists_basis_twist_field hL hL2 V D (Kbar V) N hN
  clear * - hL hN0 hu hS Φ e hfr hθ hmul hcomm hnd m hm hact hw1 hw2 hw3 huniq xp hxp hcA hcH hg hlinF hbas
  have := A.isAb.comm
  let iso := (Scheme.ΓSpecIso (CommRingCat.of (Kbar V))).commRingCatIsoToRingEquiv
  let S : Subgroup (TFK (R := V) (Kbar V) ⟶ A.A) := (powMonoidHom N).ker
  have hcS : Nat.card S = N ^ (2 * A.g) := hcA
  have : Finite S := Nat.finite_of_card_ne_zero (hcS ▸ pow_ne_zero _ hN0)
  obtain ⟨x, hx⟩ : ∃ x : SecM A.A A.L N (TFK (R := V) (Kbar V)) → Raw D (Kbar V) N,
    ∀ v, U.ExpF (Kbar V) N (SecM.toSec A.A v) (x v) := ⟨_, fun v => hxp _⟩
  have hxe : ∀ t s, U.ExpF (Kbar V) N t s → x (SecM.ofSec A.A t) = s := fun t s h => (huniq _ _ _ _ (hx _) h).1 rfl
  have hsupp : ∀ β, U.Supp (Kbar V) N β ↔ ∃ v j, (x v β).f j ≠ 0 := fun β =>
    ⟨fun ⟨t, s, h, hj⟩ => ⟨SecM.ofSec A.A t, by rwa [hxe t s h]⟩, fun ⟨v, hv⟩ => ⟨_, _, hx v, hv⟩⟩
  refine (proportional_raw (D := D) (k := Γ((TFK (R := V) (Kbar V)).left, ⊤)) (A := S)
    (E := SecM A.A A.L N (TFK (R := V) (Kbar V))) hL.globalFns iso e Φ ?_ ?_ ?_ ?_ hN0 (fun g => ⟨m g, (hact g).1⟩)
    ?_ ?_ (n := N ^ D.P.g) ?_ x ?_ ?_ ?_ ?_ ?_ ?_ ?_ α mu u hu ((hsupp _).1 hS)).elim fun a ha => ?_
  · rw [hcS, mul_comm, pow_mul]; exact congrArg (· ^ 2) hfr
  · exact fun a b => hmul a b (a * b : S) rfl
  · exact fun a b => (hcomm a b).2
  · exact fun a h => Subtype.ext (hnd a h)
  · exact fun g g' h => hm (congrArg Subtype.val h)
  · rw [hcS, hcH, hg, ← pow_add]; exact le_of_eq (congrArg _ (by ring))
  · rw [← pow_add, add_comm, ← hg]; exact hfr.ge
  · intro c v v' β
    obtain ⟨c, rfl⟩ := iso.symm.surjective c
    choose s hs using fun β => exists_comb ((fst (TF (R := V) (Kbar V)) D.P.A).left.appTop.hom (iso.symm c))
      (x v β) (x v' β)
    have := hlinF _ _ (SecM.toSec A.A (iso.symm c • v + v' :)) _ _ s c (hx v) (hx v') (fun _ => rfl) hs
    rw [(huniq _ _ _ _ (hx _) this).1 rfl, iso.apply_symm_apply]
    exact hs β
  · exact fun v v' h => congrArg (SecM.ofSec A.A) ((huniq _ _ _ _ (hx v) (hx v')).2 h)
  · intro χ v
    obtain ⟨t', s', h, H⟩ := hw1 χ _ _ (hx v)
    exact ⟨SecM.ofSec A.A t', by rwa [hxe _ _ h]⟩
  · exact fun χ => (hw2 χ).imp fun ν h => (hsupp _).1 h
  · exact fun χ hχ v h h' => Subtype.ext (funext (hw3 χ ((hsupp _).2 hχ) _ _ (hx v) h h'))
  · exact fun β => (hbas β).imp fun b hb s => (hb s).exists
  · intro g
    obtain ⟨θ, hθ₁, hθ₂⟩ := hθ ⟨m g, (hact g).1⟩
    obtain ⟨w, hw, H⟩ := (hact g).2 θ hθ₁
    exact ⟨w, hw, fun v => H _ _ _ _ (hx _) (hx _) (hθ₂ v)⟩
  · refine ⟨a, fun t s h => ?_⟩
    rw [← hxe t s h]
    exact ha _

end GlobalTheory.UU.SchurComp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FiniteMonotoneGrowth
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.VeryAmpleGrowth

variable {K : Type} [Field K] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of K))

theorem top_add {M : LB X} (a b : SecOnR f M ⊤) (k : M.ι) :
    (SecOnR.topEquiv f M (a + b)).f k = (SecOnR.topEquiv f M a).f k + (SecOnR.topEquiv f M b).f k := by
  rw [SecOnR.topEquiv_f, SecOnR.topEquiv_f, SecOnR.topEquiv_f, SecOnR.coord_add, map_add]

theorem top_smul {M : LB X} (c : K) (a : SecOnR f M ⊤) (k : M.ι) :
    (SecOnR.topEquiv f M (c • a)).f k = cst f (M.U k) c * (SecOnR.topEquiv f M a).f k := by
  rw [SecOnR.topEquiv_f, SecOnR.topEquiv_f, SecOnR.coord_base_smul, map_mul, rs_cst]

theorem top_ext {M : LB X} {a b : SecOnR f M ⊤}
    (h : ∀ k, (SecOnR.topEquiv f M a).f k = (SecOnR.topEquiv f M b).f k) : a = b :=
  (SecOnR.topEquiv f M).injective (by
    generalize SecOnR.topEquiv f M a = x at h ⊢
    generalize SecOnR.topEquiv f M b = y at h ⊢
    obtain ⟨x, hx⟩ := x
    obtain ⟨y, hy⟩ := y
    obtain rfl : x = y := funext h
    rfl)

theorem top_zero {M : LB X} (k : M.ι) : (SecOnR.topEquiv f M 0).f k = 0 := by
  rw [SecOnR.topEquiv_f, SecOnR.coord_zero, map_zero]

def linTop {M : LB X} {V : Type} [AddCommGroup V] [Module K V] (φ : V → LB.Sec M)
    (hadd : ∀ a b k, (φ (a + b)).f k = (φ a).f k + (φ b).f k)
    (hsmul : ∀ (c : K) a k, (φ (c • a)).f k = cst f (M.U k) c * (φ a).f k) :
    V →ₗ[K] SecOnR f M ⊤ where
  toFun a := (SecOnR.topEquiv f M).symm (φ a)
  map_add' a b := top_ext f fun k => by
    simp only [top_add, LinearEquiv.apply_symm_apply, hadd]
  map_smul' c a := top_ext f fun k => by
    simp only [top_smul, LinearEquiv.apply_symm_apply, hsmul, RingHom.id_apply]

theorem top_linTop {M : LB X} {V : Type} [AddCommGroup V] [Module K V] (φ : V → LB.Sec M) (hadd hsmul)
    (a : V) : SecOnR.topEquiv f M (linTop f φ hadd hsmul a) = φ a :=
  (SecOnR.topEquiv f M).apply_symm_apply _

def mulPw {H : LB X} (s : LB.Sec H) (t : ℕ) (σ : LB.Sec (pw H t)) : LB.Sec (pw H (t + 1 : ℕ)) where
  f := fun k => s.f k * (show Γ(X, H.U k) from σ.f k)
  compat := fun k l => by
    have h₁ : rs X (inf_le_left : H.U k ⊓ H.U l ≤ H.U k) (s.f k) =
      (H.g k l).val * rs X (inf_le_right : H.U k ⊓ H.U l ≤ H.U l) (s.f l) := s.compat k l
    have h₂ : rs X (inf_le_left : H.U k ⊓ H.U l ≤ H.U k) (σ.f k) =
      (H.g k l ^ (t : ℤ)).val * rs X (inf_le_right : H.U k ⊓ H.U l ≤ H.U l) (σ.f l) := σ.compat k l
    change rs X (inf_le_left : H.U k ⊓ H.U l ≤ H.U k) (s.f k * (show Γ(X, H.U k) from σ.f k)) =
      (H.g k l ^ ((t + 1 : ℕ) : ℤ)).val *
        rs X (inf_le_right : H.U k ⊓ H.U l ≤ H.U l) (s.f l * (show Γ(X, H.U l) from σ.f l))
    rw [map_mul, map_mul, h₁, h₂, zpow_natCast, zpow_natCast, pow_succ, Units.val_mul]
    ring

def mulLin {H : LB X} (s : LB.Sec H) (t : ℕ) :
    SecOnR f (pw H t) ⊤ →ₗ[K] SecOnR f (pw H (t + 1 : ℕ)) ⊤ :=
  linTop f (fun a => mulPw s t (SecOnR.topEquiv f _ a))
    (fun a b k => (congrArg (fun y : Γ(X, H.U k) => s.f k * y) (top_add f a b k)).trans
      (mul_add (s.f k) (show Γ(X, H.U k) from (SecOnR.topEquiv f (pw H t) a).f k)
        (show Γ(X, H.U k) from (SecOnR.topEquiv f (pw H t) b).f k)))
    (fun c a k => (congrArg (fun y : Γ(X, H.U k) => s.f k * y) (top_smul f c a k)).trans
      (mul_left_comm _ _ _))

theorem top_mulLin {H : LB X} (s : LB.Sec H) (t : ℕ) (a : SecOnR f (pw H t) ⊤) :
    SecOnR.topEquiv f (pw H (t + 1 : ℕ)) (mulLin f s t a) = mulPw s t (SecOnR.topEquiv f (pw H t) a) :=
  top_linTop f _ _ _ a

theorem mulLin_injective [IsIntegral X] {H : LB X} (s : LB.Sec H) {x : X} (hx : x ∈ nonzeroLocus s) (t : ℕ) :
    Function.Injective (mulLin f s t) := by
  obtain ⟨k₀, hk₀⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  let W : X.Opens := X.basicOpen (s.f k₀)
  have hWU : W ≤ H.U k₀ := X.basicOpen_le _
  haveI : Nonempty W := ⟨⟨x, hk₀⟩⟩
  have hu : IsUnit (rs X hWU (s.f k₀)) := X.toRingedSpace.isUnit_res_basicOpen _
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro a ha
  have h : s.f k₀ * (show Γ(X, H.U k₀) from (SecOnR.topEquiv f (pw H t) a).f k₀) = 0 := by
    have e := top_mulLin f s t a
    rw [ha] at e
    exact (congrArg (fun σ : LB.Sec (pw H (t + 1 : ℕ)) => σ.f k₀) e).symm.trans
      (top_zero f (M := pw H (t + 1 : ℕ)) k₀)
  have h' := congrArg (rs X hWU) h
  rw [map_mul, map_zero, hu.mul_right_eq_zero] at h'
  exact top_ext f fun k =>
    (SecGrowth.sec_eq_zero (M := pw H t) (SecOnR.topEquiv f _ a) (k₀ := k₀) hWU h' k).trans
      (top_zero f k).symm

theorem finite_of_polynomial {H : LB X} {m : ℕ} (s : Fin (m + 1) → LB.Sec H) (t : ℕ)
    (h : ∀ σ : LB.Sec (pw H t), ∃ F : MvPolynomial (Fin (m + 1)) K, F.IsHomogeneous t ∧
      ∀ k : H.ι, σ.f k = MvPolynomial.eval₂Hom (cst f (H.U k)) (fun j => (s j).f k) F) :
    Module.Finite K (SecOnR f (pw H t) ⊤) := by
  haveI : Module.Finite K (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) K t) :=
    Submodule.finiteDimensional_of_le (S₂ := MvPolynomial.restrictTotalDegree (Fin (m + 1)) K t)
      fun F hF => (MvPolynomial.mem_restrictTotalDegree _ _ _).2
        (MvPolynomial.IsHomogeneous.totalDegree_le hF)
  refine Module.Finite.of_surjective
    (linTop f (V := MvPolynomial.homogeneousSubmodule (Fin (m + 1)) K t)
      (fun F => SecGrowth.polySec f s F.2)
      (fun a b k => map_add (MvPolynomial.eval₂Hom (cst f (H.U k)) (fun j => (s j).f k)) a.1 b.1)
      (fun c a k => ?_)) fun a => ?_
  · change MvPolynomial.eval₂Hom (cst f (H.U k)) (fun j => (s j).f k) (c • a.1) =
      cst f (H.U k) c * MvPolynomial.eval₂Hom (cst f (H.U k)) (fun j => (s j).f k) a.1
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval₂Hom_C]
  · obtain ⟨F, hF, hFa⟩ := h (SecOnR.topEquiv f _ a)
    refine ⟨⟨F, hF⟩, top_ext f fun k => ?_⟩
    exact (congrArg (fun σ : LB.Sec (pw H t) => σ.f k) (top_linTop f _ _ _ _)).trans (hFa k).symm

theorem finite_monotone_growth : ∀ (K : Type) [Field K] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of K)) (g : ℕ), SmoothOfRelativeDimension g f → ∀ (H : LB X) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → (∀ t : ℕ, Module.Finite K (SecOnR f (pw H t) ⊤)) ∧ (∀ t t' : ℕ, t ≤ t' → Module.finrank K (SecOnR (f) (pw H t) ⊤) ≤ Module.finrank K (SecOnR (f) (pw H t') ⊤)) ∧ ∃ c C : ℕ, 1 ≤ c ∧ ∀ t : ℕ, 1 ≤ t → t ^ g ≤ c * Module.finrank K (SecOnR (f) (pw H t) ⊤) ∧ Module.finrank K (SecOnR (f) (pw H t) ⊤) ≤ C * t ^ g := by
  intro K _ X _ f g hf H n s hH hs
  obtain ⟨t₀, ht₀⟩ := GlobalTheory.T.exists_homogeneousForm_eq_highPowerSection K X f H n s hH hs
  obtain ⟨x⟩ : Nonempty X := inferInstance
  have hx : x ∈ ⨆ i, nonzeroLocus (s i) := by rw [hs.1]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  have hinj := mulLin_injective f (s i) hi
  have hfin : ∀ t : ℕ, Module.Finite K (SecOnR f (pw H t) ⊤) := fun t => by
    have h : ∀ d t : ℕ, t₀ ≤ t + d → Module.Finite K (SecOnR f (pw H t) ⊤) := by
      intro d
      induction d with
      | zero => exact fun t ht => finite_of_polynomial f s t (ht₀ t ht)
      | succ d ih =>
        intro t ht
        haveI := ih (t + 1) (by omega)
        exact Module.Finite.of_injective _ (hinj t)
    exact h t₀ t (Nat.le_add_left _ _)
  refine ⟨hfin, fun t t' h => ?_, ?_⟩
  · exact monotone_nat_of_le_succ (f := fun t : ℕ => Module.finrank K (SecOnR f (pw H t) ⊤))
      (fun t => LinearMap.finrank_le_finrank_of_injective (hinj t)) h
  · exact SecGrowth.growth_of_veryAmpleBy f s hs g t₀ ht₀
      (fun B _ _ _ r => finrank_totalDegree_image_growth K B _ _ r)
      (trdeg_eq_of_smoothOfRelativeDimension K X f g hf)
      (fun t => SecOnR f (pw H t) ⊤) (fun t => SecOnR.topEquiv f _)
      (fun t a b k => top_add f a b k) (fun t c a k => top_smul f c a k)
      (fun t a ha => top_ext f fun k => (ha k).trans (top_zero f k).symm)
      (fun t σ => ⟨(SecOnR.topEquiv f _).symm σ, fun k => by rw [LinearEquiv.apply_symm_apply]⟩)

end GlobalTheory.VeryAmpleGrowth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GenericIsoAgreesOnCompletePointsStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.generic_iso_agrees_on_complete_points_alt : Laws → Laws2 → ∀ (R
    : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (I
    : Ideal R), AdmBase R I → I = IsLocalRing.maximalIdeal R → ∀ (D D' : DegData R I) (A A'
    : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of
    R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj
    G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ (U : Unif I D A G) (U' : Unif I D' A' G') (hD
    : IsPullDeg (RingHom.id R) D.toPre D'.toPre) (j
    : ∀ e : ℕ, thickObj R I e G' ≅ thickObj R I e G), (∀ e : ℕ, IsMonHom (j
    e).hom ∧ thickMap R I e G' ≫ (j (e + 1)).hom.left = (j e).hom.left ≫ thickMap R I e G ∧ (U'.gt
    e).pG.left ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) = (j
    e).hom.left ≫ (U.gt e).pG.left ∧ ∀ x : D'.toPre.X, (∀ κ : Fin 4, D'.toPre.Oφ (U'.gt
    e).pG x κ ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) = (j
    e).hom.left ≫ D.toPre.Oφ (U.gt e).pG (hD.xe x) κ) ∧ PMaps hD.w (D'.toPre.Oφ (U'.gt e).pG
    x) (D.toPre.Oφ (U.gt e).pG (hD.xe x)) Oinvε ((U'.gt e).t x) ((U.gt e).t (hD.xe x)) (j
    e).hom.left) → ∀ (ΦK : (Over.pullback (jK R)).obj G' ≅ (Over.pullback (jK R)).obj G) (wK
    : LB.Iso (U'.LG.L.pull (pullback.fst G'.hom (jK R))) (U.LG.L.pull (ΦK.hom.left ≫ pullback.fst
    G.hom (jK R)))), (wK.IsGen ∧ ∀ (k : ℕ), 1 ≤ k → ∀ (σ' : H0 U'.LG.L k) (σ : H0 U.LG.L k), (∀ (e
    : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G').left) (z : Z) (jM : D.toPre.P.L.ι) (jM'
    : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (hD.e.hom.left ≫ pullback.fst
    D.toPre.P.A.hom (specOf (RingHom.id R))) ((U'.gt e).pG.left (r z)) ∈ D.toPre.P.L.U jM → (U'.gt
    e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → (fstG I e G).left ((j e).hom.left (r
    z)) ∈ U.LG.L.U jL → (fstG I e G').left (r z) ∈ U'.LG.L.U jL' → (Geo.Tor.gw (U.w e) (r ≫ (j
    e).hom.left) z jM (fun _ => jL) ^ k).val * gs (r ≫ (j e).hom.left ≫ (fstG I e
    G).left) z (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => jL)) (σ.f
    (fun _ => jL)) = ((Geo.Tor.gw hD.w (r ≫ (U'.gt e).pG.left) z jM jM' * Geo.Tor.gw (U'.w e) r z
    jM' (fun _ => jL')) ^ k).val * gs (r ≫ (fstG I e G').left) z (LB.wchart U'.LG.L
    (fun _ : Fin 1 => 𝟙 G'.left) (fun _ => jL')) (σ'.f (fun _ => jL'))) → ∀ (Z : Scheme.{0}) (r
    : Z ⟶ ((Over.pullback (jK R)).obj G').left) (z : Z) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (r ≫
    ΦK.hom.left ≫ pullback.fst G.hom (jK R)) z ∈ U.LG.L.U jL → (r ≫ pullback.fst G'.hom (jK
    R)) z ∈ U'.LG.L.U jL' → gs (r ≫ ΦK.hom.left ≫ pullback.fst G.hom (jK R)) z (LB.wchart U.LG.L
    (fun _ : Fin 1 => 𝟙 G.left) (fun _ => jL)) (σ.f (fun _ => jL)) = (Geo.Tor.gw wK r z jL
    (fun _ => jL') ^ k).val * gs (r ≫ pullback.fst G'.hom (jK R)) z (LB.wchart U'.LG.L
    (fun _ : Fin 1 => 𝟙 G'.left) (fun _ => jL')) (σ'.f (fun _ => jL'))) → ∀ (B : Type) [CommRing
    B] [Algebra R B] (g' : Spec (CommRingCat.of B) ⟶ G'.left) (g : Spec (CommRingCat.of
    B) ⟶ G.left) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), IsAdicComplete (I.map (algebraMap R B)) B → (g'
    ≫ G'.hom = Spec.map (CommRingCat.ofHom (algebraMap R B)) ∧ g ≫ G.hom = Spec.map
    (CommRingCat.ofHom (algebraMap R B)) ∧ ⊤ ≤ g' ⁻¹ᵁ U'.LG.L.U jL' ∧ ⊤ ≤ g ⁻¹ᵁ U.LG.L.U jL ∧ ∀ (e
    : ℕ) (Z : Scheme.{0}) (ρ : Z ⟶ Spec (CommRingCat.of B)) (r : Z ⟶ (thickObj R I e
    G').left), r ≫ (fstG I e G').left = ρ ≫ g' → r ≫ (j e).hom.left ≫ (fstG I e
    G).left = ρ ≫ g) → ∃ v : Γ(Spec (CommRingCat.of B), ⊤)ˣ, (∀ (Z : Scheme.{0}) (ρ
    : Z ⟶ Spec (CommRingCat.of B)) (r : Z ⟶ ((Over.pullback (jK R)).obj
    G').left), r ≫ pullback.fst G'.hom (jK R) = ρ ≫ g' → r ≫ ΦK.hom.left ≫ pullback.fst G.hom (jK
    R) = ρ ≫ g ∧ ∀ z : Z, Geo.Tor.gw wK r z jL (fun _ => jL') = gm ρ z ⊤ v) ∧ ∀ (e : ℕ) (Z
    : Scheme.{0}) (ρ : Z ⟶ Spec (CommRingCat.of B)) (r : Z ⟶ (thickObj R I e G').left) (z : Z) (jM
    : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι), r ≫ (fstG I e G').left = ρ ≫ g' → (hD.e.hom.left ≫
    pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) ((U'.gt e).pG.left (r
    z)) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → (fstG I e G).left ((j
    e).hom.left (r z)) ∈ U.LG.L.U jL → (fstG I e G').left (r z) ∈ U'.LG.L.U jL' → Geo.Tor.gw hD.w (r
    ≫ (U'.gt e).pG.left) z jM jM' * Geo.Tor.gw (U'.w e) r z jM' (fun _ => jL') = Geo.Tor.gw (U.w
    e) (r ≫ (j e).hom.left) z jM (fun _ => jL) * gm ρ z ⊤ v := by
  first | exact @GlobalTheory.generic_iso_agrees_on_complete_points | exact GlobalTheory.generic_iso_agrees_on_complete_points | (intros; apply GlobalTheory.generic_iso_agrees_on_complete_points <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVarietyStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isProjectiveOverRingByCharts_abelian_variety : ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Spec (CommRingCat.of K))) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → IsProjBy B.hom := by
  first | exact @GlobalTheory.AbelianProjective.isProjBy_of_isAbelianScheme | exact GlobalTheory.AbelianProjective.isProjBy_of_isAbelianScheme | (intros; apply GlobalTheory.AbelianProjective.isProjBy_of_isAbelianScheme <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaSupportPairIffDegreeTwoSumDiff
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
namespace GlobalTheory.UU.SuppRel

theorem component_ne_zero_iff_mod_two (F : Type) [Field F] (X : Type) [AddCommGroup X] [Module.Finite ℤ X]
    (E : Type) [AddCommGroup E] [Module F E] (W : X → Type) [∀ a, AddCommGroup (W a)]
    [∀ a, Module F (W a)] (ex : ∀ a, E →ₗ[F] W a)
    (hsep : ∀ s, (∀ a, ex a s = 0) → s = 0)
    (hcut : ∀ (α : X) (s : E), ∃ s' : E, ∀ β,
      ((∃ mu, β = α + 2 • mu) → ex β s' = ex β s) ∧ ((¬ ∃ mu, β = α + 2 • mu) → ex β s' = 0))
    (hinj : ∀ α, ex α ≠ 0 → ∀ s, (∀ β, (¬ ∃ mu, β = α + 2 • mu) → ex β s = 0) → ex α s = 0 → s = 0)
    (w : TensorProduct F E E)
    (hfull : ∀ π : E →ₗ[F] E, TensorProduct.map π (LinearMap.id : E →ₗ[F] E) w = 0 → π = 0)
    (hoff : ∀ α β, (¬ ∃ a b, α = a + b ∧ β = a - b) → TensorProduct.map (ex α) (ex β) w = 0)
    (a b : X) :
    TensorProduct.map (ex (a + b)) (ex (a - b)) w ≠ 0 ↔ ex (a + b) ≠ 0 ∧ ex (a - b) ≠ 0 := by
  let H : AddSubgroup X := (nsmulAddMonoidHom 2 : X →+ X).range
  have hfg : AddGroup.FG X := Module.Finite.iff_addGroup_fg.mp inferInstance
  have hH : H.FiniteIndex := AddSubgroup.finiteIndex_range_nsmulAddMonoidHom_of_fg X two_ne_zero
  have hfin : Finite (X ⧸ H) := AddSubgroup.finite_quotient_of_finiteIndex
  have hcl : ∀ α β : X, (QuotientAddGroup.mk β : X ⧸ H) = QuotientAddGroup.mk α ↔ ∃ mu, β = α + 2 • mu := by
    intro α β
    rw [eq_comm, QuotientAddGroup.eq]
    constructor
    · rintro ⟨mu, h⟩
      exact ⟨mu, by rw [nsmulAddMonoidHom_apply] at h; rw [h]; abel⟩
    · rintro ⟨mu, h⟩
      exact ⟨mu, by rw [nsmulAddMonoidHom_apply, h]; abel⟩
  refine GlobalTheory.tensor_component_ne_zero_iff F X (X ⧸ H) QuotientAddGroup.mk E W ex hsep ?_ ?_ w hfull ?_ _ _ ?_
  · intro c s
    obtain ⟨α, rfl⟩ := QuotientAddGroup.mk_surjective c
    obtain ⟨s', hs'⟩ := hcut α s
    exact ⟨s', fun β => ⟨fun h => (hs' β).1 ((hcl α β).1 h), fun h => (hs' β).2 fun h' => h ((hcl α β).2 h')⟩⟩
  · intro α hα s hs h0
    exact hinj α hα s (fun β hβ => hs β fun h => hβ ((hcl α β).1 h)) h0
  · intro α β h
    refine hoff α β ?_
    rintro ⟨x, y, rfl, rfl⟩
    exact h ((hcl _ _).2 ⟨y, by rw [two_nsmul]; abel⟩)
  · exact (hcl _ _).2 ⟨b, by rw [two_nsmul]; abel⟩

theorem supp_rel : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ θ f, U.Theta θ f → ∀ a b : D.X, ((∃ j, (f a).f j ≠ 0) ∧ ∃ j, (f b).f j ≠ 0) ↔ (U.Supp (Kbar V) 2 (a + b) ∧ U.Supp (Kbar V) 2 (a - b))) := by
  intro hL hL2 V _ _ _ hV D A G _ _ U θ f hθ a b
  obtain ⟨hG, hB⟩ := GlobalTheory.UU.PullSec.pullEx V hV D A G U (Kbar V) (𝟙_ _) (toUnit _) 1
  obtain ⟨th, hth, -⟩ := hG θ
  obtain ⟨s₀, hs₀, -⟩ := hB f
  obtain ⟨r, n, t, t', s, s', hr, hexp, hA, hAB⟩ := GlobalTheory.T.additionFormula_algClosure_with_expansions hL hL2 V hV D A G U θ f hθ th s₀ hth hs₀
  obtain ⟨hth0, -, -⟩ := GlobalTheory.T.expF_of_theta_degree_one hL hL2 V hV D A G U θ f hθ th s₀ hth hs₀
  obtain ⟨ex, hex, huniq, hsep, hsupp⟩ := GlobalTheory.T.exists_linear_fourierJacobi_expansion_family hL hL2 V hV D A G U (Kbar V) 2 (by norm_num)
  obtain ⟨hcut, -, hinj⟩ := GlobalTheory.T.lineBundleSections_torusTorsion_weightSpaces hL hL2 V hV D A G U 2 (by norm_num)
  obtain ⟨hon, hoff⟩ := GlobalTheory.T.additionTensor_abelianPart_ne_zero_iff V D (Kbar V) s₀ r n s s' hr hAB
  have hcV : CharZero V := hV.2.2
  have hchar : CharZero (FractionRing V) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective V (FractionRing V))
  have h2 : (2 : Kbar V) ≠ 0 := two_ne_zero
  let u : Fin n → EA A (jFK (R := V) (Kbar V)) 2 := fun i => SecMod.mk _ (t i)
  let u' : Fin n → EA A (jFK (R := V) (Kbar V)) 2 := fun i => SecMod.mk _ (t' i)
  have hfull := GlobalTheory.T.additionTensor_full_left_support hL hL2 _ A (Kbar V) (jFK (R := V) (Kbar V)) h2 (SecMod.mk _ th) n u u' hA
    (fun h => by
      obtain ⟨j, hj⟩ := hth0
      exact hj ((SecMod.eq_zero_iff _).1 h j))
  have hmap : ∀ α β : D.X, TensorProduct.map (ex α) (ex β) (∑ i, TensorProduct.tmul (Kbar V) (u i) (u' i)) =
      ∑ i, TensorProduct.tmul (Kbar V) (SecMod.mk _ (s i α) : WB D (Kbar V) 2 α)
        (SecMod.mk _ (s' i β) : WB D (Kbar V) 2 β) := by
    intro α β
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [TensorProduct.map_tmul, huniq _ _ (hexp i).1 α, huniq _ _ (hexp i).2 β]
    rfl
  have key := component_ne_zero_iff_mod_two (Kbar V) D.X (EA A (jFK (R := V) (Kbar V)) 2)
    (fun α => WB D (Kbar V) 2 α) ex hsep ?_ ?_ _ hfull (fun α β h => (hmap α β).trans (hoff α β h)) a b
  · rw [hsupp, hsupp, ← key, hmap, hon, GlobalTheory.T.pullbackSectionFamily_ne_zero_iff V D (Kbar V) 1 f s₀ hs₀ a,
      GlobalTheory.T.pullbackSectionFamily_ne_zero_iff V D (Kbar V) 1 f s₀ hs₀ b]
  · intro α v
    obtain ⟨v', p, hp, hβ⟩ := hcut α _ _ (hex v)
    refine ⟨SecMod.mk _ v', fun β => ⟨fun h => ?_, fun h => ?_⟩⟩
    · rcases hβ β with h' | h'
      · exact (huniq _ _ hp β).symm.trans h'.2
      · exact absurd h h'.1
    · rcases hβ β with h' | h'
      · exact absurd h'.1 h
      · refine (SecMod.eq_zero_iff _).2 fun j => ?_
        rw [← huniq _ _ hp β]
        exact h'.2 j
  · intro α hα v hv h0
    exact (SecMod.eq_zero_iff _).2 (hinj α ((hsupp α).2 hα) _ _ (hex v)
      (fun β hβ => (SecMod.eq_zero_iff _).1 (hv β hβ)) ((SecMod.eq_zero_iff _).1 h0))

end GlobalTheory.UU.SuppRel
end

