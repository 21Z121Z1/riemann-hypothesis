import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0109
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsoOfSectionRingEquiv
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0019
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2665
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0016
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0139
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0024
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2641
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2615
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2616
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0078
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0393
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2614
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapGermFromSpec

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeightZeroSectionNonzeroAtOrigin
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.OriginSec

theorem isUnit_sval_iff' {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) :
    IsUnit (sval s r z J) ↔ r z ∈ nonzeroLocus s := by
  have key : ∀ (U : Y.Opens) (_ : r z ∈ U) (f : Γ(Y, U)), IsUnit (gs r z U f) ↔ IsUnit (gs (𝟙 Y) (r z) U f) :=
    fun U h f => by rw [gs_stalkMap r z U h, isUnit_map_iff]
  refine ⟨fun h => (mem_nonzeroLocus s _).2 ⟨_, hJ.mem φ r, (key _ (hJ.mem φ r) _).1 h⟩, fun h => ?_⟩
  obtain ⟨j, hj, hu⟩ := (mem_nonzeroLocus s _).1 h
  rw [sval, sec_trans s r z (hJ.mem φ r) hj]
  exact (Units.isUnit _).mul ((key _ hj _).2 hu)

theorem c_zero {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) : D.c 0 = η[D.P.A] := by
  have h := D.c_add 0 0
  simp only [add_zero, padd] at h
  rw [← Hom.mul_def] at h
  have : D.c 0 = 1 := by simpa using h
  rw [this, Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]

theorem formEq_zero {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (k : ℕ) :
    FormEq (K := Fin 1) (fun _ => 𝟙 D.P.A.left) (fun _ => (k : ℤ)) (D.famφB 0) (DegPre.famε k) := by
  have e1 : (padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ η[D.P.A])).left = 𝟙 D.P.A.left := by
    rw [padd, ← Hom.mul_def, ← Hom.one_def, _root_.mul_one]; rfl
  intro U _ h
  rw [Fin.prod_univ_four, Fin.prod_univ_one]
  simp only [DegPre.famφB, DegPre.famε, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, c_zero, e1]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow]
  module

end GlobalTheory.Mum.OriginSec

open GlobalTheory.Mum.OriginSec GlobalTheory.SecRingIso in

theorem GlobalTheory.Mum.exists_secB_zero_nonzero_origin : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)), ∃ k₀ : ℕ, ∀ k ≥ k₀, ∃ b : D.toPre.SecB k 0, eSec D.toPre.P.A (closedPoint R) ∈ nonzeroLocus b := by
  intro R _ _ _ _ D
  have : IsProper D.toPre.P.A.hom := D.toPre.P.isAb.proper
  obtain ⟨n, hn, a, b, ha, hb⟩ := GlobalTheory.exists_sec_succ_of_relAmple R D.toPre.P.A D.toPre.P.L D.toPre.P.isLB
    D.toPre.P.ample (eSec D.toPre.P.A (closedPoint R))
  let Q : ℕ → Prop := fun m => ∃ d : H0 D.toPre.P.L m, eSec D.toPre.P.A (closedPoint R) ∈ nonzeroLocus d
  have hQ : ∀ m m', Q m → Q m' → Q (m + m') := fun m m' ⟨d, hd⟩ ⟨d', hd'⟩ => by
    obtain ⟨e, he⟩ := exists_mul d d'
    exact ⟨e, mem_mul he hd hd'⟩
  have hij : ∀ i j : ℕ, Q (n * (i + 1) + (n + 1) * j) := by
    intro i j
    induction j with
    | zero =>
      induction i with
      | zero => simpa using (⟨a, ha⟩ : Q n)
      | succ i ih =>
        have := hQ _ _ ih ⟨a, ha⟩
        rwa [show n * (i + 1 + 1) + (n + 1) * 0 = n * (i + 1) + (n + 1) * 0 + n by ring]
    | succ j ih =>
      have := hQ _ _ ih ⟨b, hb⟩
      rwa [show n * (i + 1) + (n + 1) * (j + 1) = n * (i + 1) + (n + 1) * j + (n + 1) by ring]
  refine ⟨n * (n + 1), fun k hk => ?_⟩
  obtain ⟨d, hd⟩ : Q k := by
    have hk' : n * (k / n) + k % n = k := Nat.div_add_mod k n
    have hr : k % n < n := Nat.mod_lt _ hn
    have hq : n + 1 ≤ k / n := (Nat.le_div_iff_mul_le hn).2 (by rw [mul_comm]; exact hk)
    obtain ⟨t, ht⟩ : ∃ t, k / n = k % n + 1 + t := ⟨k / n - k % n - 1, by omega⟩
    have e : k = n * (t + 1) + (n + 1) * (k % n) := by
      conv_lhs => rw [← hk', ht]
      ring
    rw [e]
    exact hij _ _
  obtain ⟨b', hb'⟩ := exists_sec D.toPre.P.isLB (formEq_zero D.toPre k) d
  refine ⟨b', ?_⟩
  obtain ⟨J, hJ⟩ : ∃ J, Good D.toPre.P.L (eSec D.toPre.P.A (closedPoint R)) J :=
    ⟨fun χ => (exists_chart D.toPre.P.isLB (χ (eSec D.toPre.P.A (closedPoint R)))).choose,
      fun χ => (exists_chart D.toPre.P.isLB (χ (eSec D.toPre.P.A (closedPoint R)))).choose_spec⟩
  have h1 := (isUnit_sval_iff' d (𝟙 _) _ hJ).2 hd
  rw [← hb' _ (𝟙 _) _ J hJ] at h1
  exact (isUnit_sval_iff' b' (𝟙 _) _ hJ).1 h1
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeightZeroSectionNotVanishingClosedFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1 ReciprocityTheory.ChartRestriction.G.H1.SquareUnits ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic

noncomputable section

namespace GlobalTheory.Mum.SecBZeroBpf

theorem unitAt_pow {S : Scheme.{0}} [IsLocallyNoetherian S] (hL : Laws) (P : PolAV S) {K : Type} [Field K]
    [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S) (x : Over.mk t ⟶ P.A) (m : ℕ) :
    UnitAt P.L ![(translPt P.A (1 : Over.mk t ⟶ P.A)).left, (snd (Over.mk t) P.A).left] ![1, (m : ℤ) + 1]
      ((ptSecT P.A x).left (IsLocalRing.closedPoint K)) := by
  have := P.isAb.smooth
  have := P.isAb.geomConnected
  have : GeometricallyIntegral P.A.hom := GlobalTheory.geometricallyIntegral_of_smooth _
  have : AlgebraicGeometry.IsIntegral (Over.mk t ⊗ P.A).left :=
    GeometricallyIntegral.geometrically_isIntegral t _ _ (IsPullback.of_hasPullback t P.A.hom).flip
  have : Subsingleton (Over.mk t).left := ⟨spec_pt_eq (k := K)⟩
  have : Nontrivial Γ((Over.mk t).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  have h1 := GlobalTheory.ThetaRep.finrank_secM hL.secBaseChange P (n := 1) le_rfl t
  rw [one_pow] at h1
  have : Nontrivial (SecM P.A P.L (1 : ℕ) (Over.mk t)) := Module.nontrivial_of_finrank_pos (h1 ▸ Nat.one_pos)
  obtain ⟨f, hf⟩ := exists_ne (0 : SecM P.A P.L (1 : ℕ) (Over.mk t))
  let θ : LB.Sec (LPow P.A P.L 1 (Over.mk t)) := SecM.toSec P.A f
  obtain ⟨k, hk⟩ : ∃ k, θ.f k ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf (Subtype.ext (funext h))
  have hD : (((Over.mk t ⊗ P.A).left.basicOpen (θ.f k) : (Over.mk t ⊗ P.A).left.Opens) :
      Set (Over.mk t ⊗ P.A).left).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro h
    exact hk ((basicOpen_eq_bot_iff _).1 (SetLike.coe_injective h))
  let p : (Over.mk t).left := IsLocalRing.closedPoint K
  let y := (ptSecT P.A x).left p
  have good : ∀ a : Over.mk t ⟶ P.A, (ptSecT P.A (a * x)).left p ∈ (Over.mk t ⊗ P.A).left.basicOpen (θ.f k) →
      UnitAt P.L (K := Fin 1) (fun _ => (translPt P.A a).left) (fun _ => 1) y := fun a ha =>
    GlobalTheory.NoBasePoint.unitAt_transl P.isLB θ k a y (by
      rw [← GlobalTheory.NoBasePoint.ptSecT_translT] at ha
      exact ha)
  have step : ∀ (m : ℤ) (b a : Over.mk t ⟶ P.A),
      UnitAt P.L ![(translPt P.A b).left, (snd (Over.mk t) P.A).left] ![1, m] y →
      UnitAt P.L (K := Fin 1) (fun _ => (translPt P.A a).left) (fun _ => 1) y →
      UnitAt P.L ![(translPt P.A (b * a)).left, (snd (Over.mk t) P.A).left] ![1, m + 1] y := by
    intro m b a hb ha
    obtain ⟨V, hV, c, hc⟩ := hL.square S P (Over.mk t) b a p
    refine UnitAt.congr P.isLB (formEq_of_add fun U _ hh => ?_)
      ((hb.mul ha).mul (GlobalTheory.NoBasePoint.unitAt_of_local P.isLB _ _ p V hV c hc y))
    simp [Fin.sum_univ_succ]
    module
  have main : ∀ (m : ℕ) (b : Over.mk t ⟶ P.A),
      UnitAt P.L ![(translPt P.A b).left, (snd (Over.mk t) P.A).left] ![1, (m : ℤ) + 1] y := by
    intro m
    induction m with
    | zero =>
      intro b
      obtain ⟨a, h₁, h₂⟩ := GlobalTheory.NoBasePoint.exists_two_points t _ hD x (b * x)
      have := step 0 a (a⁻¹ * b) (UnitAt.congr P.isLB (formEq_of_add fun U _ hh => by simp) (good a (h₁ p)))
        (good _ (by rw [_root_.mul_assoc]; exact h₂ p))
      rwa [mul_inv_cancel_left] at this
    | succ m ih =>
      intro b
      obtain ⟨a, h₁, -⟩ := GlobalTheory.NoBasePoint.exists_two_points t _ hD x x
      have := step _ _ a (ih (b * a⁻¹)) (good a (h₁ p))
      rwa [inv_mul_cancel_right] at this
  exact main m 1

theorem mem_basicOpen_of_isUnit {Y Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (U : Y.Opens) (hz : r z ∈ U) (a : Γ(Y, U))
    (h : IsUnit (gs r z U a)) : r z ∈ Y.basicOpen a := by
  rw [gs_eq r z U hz] at h
  exact (SetLike.ext_iff.1 (Scheme.preimage_basicOpen r a) z).2 ((Z.mem_basicOpen _ z hz).2 h)

theorem c_zero {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) : D.c 0 = η[D.P.A] := by
  have h := D.c_add 0 0
  rw [add_zero] at h
  have h' : D.c 0 * D.c 0 = D.c 0 := h.symm
  rw [mul_eq_left] at h'
  rw [h']
  show toUnit _ ≫ η[D.P.A] = η[D.P.A]
  rw [toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]

theorem _root_.GlobalTheory.Mum.exists_secB_zero_mem_basicOpen : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R →
    ∀ (D : DegData R (maximalIdeal R)) (k : ℕ), 2 ≤ k → ∀ x : D.toPre.P.A.left,
      D.toPre.P.A.hom x = closedPoint R →
      ∃ (σ : D.toPre.SecB k 0) (j : Fin 4 → D.toPre.P.L.ι), x ∈ D.toPre.P.A.left.basicOpen (σ.f j) := by
  intro R _ _ _ hB D k hk x hx
  haveI : IsNoetherianRing R := hB.1.1
  have hL : Laws := GlobalTheory.abelianSchemeLaws_all.1
  have hTW : DVR.TwistBCSpanStatement := DVR.twistBCSpan_of GlobalTheory.twistBaseChange
  let P := D.toPre.P
  let K := AlgebraicClosure (P.A.left.residueField x)
  let u : Spec (CommRingCat.of K) ⟶ P.A.left :=
    Spec.map (CommRingCat.ofHom (algebraMap (P.A.left.residueField x) K)) ≫ P.A.left.fromSpecResidueField x
  have hu : ∀ q, u q = x := fun q => (Scheme.Hom.comp_apply _ _ q).trans (Scheme.fromSpecResidueField_apply x _)
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (u ≫ P.A.hom)
  let f : R →+* K := φ.hom
  have hφ' : Spec.map (CommRingCat.ofHom f) = u ≫ P.A.hom := hφ
  have e2 : (u ≫ P.A.hom) (closedPoint K) = closedPoint R :=
    (Scheme.Hom.comp_apply _ _ _).trans ((congrArg _ (hu _)).trans hx)
  have e : (Spec.map (CommRingCat.ofHom f)) (closedPoint K) = closedPoint R := by rw [hφ']; exact e2
  have e3 : Ideal.comap f (maximalIdeal K) = maximalIdeal R := congrArg PrimeSpectrum.asIdeal e
  have hf : IsLocalHom f := ⟨fun a ha => by
    by_contra hna
    have h1 : a ∈ maximalIdeal R := (mem_maximalIdeal a).2 hna
    rw [← e3] at h1
    exact (mem_maximalIdeal _).1 h1 ha⟩
  let T : Over (Spec (CommRingCat.of R)) := Over.mk (Spec.map (CommRingCat.ofHom f))
  let xb : T ⟶ P.A := Over.homMk u hφ'.symm
  let y := (ptSecT P.A xb).left (closedPoint K)
  have hy : (snd T P.A).left y = x := by
    have e4 : ptSecT P.A xb ≫ snd T P.A = xb := lift_snd _ _
    have e5 := congrArg (fun q => q.left (closedPoint K)) e4
    simp only [Over.comp_left, Scheme.Hom.comp_apply] at e5
    exact e5.trans (hu _)
  have c0 := c_zero D.toPre
  have a0 : (snd T P.A).left ≫ D.toPre.famφB 0 0 = (snd T P.A).left := Category.comp_id _
  have a1 : (snd T P.A).left ≫ D.toPre.famφB 0 1 = (translPt P.A (1 : T ⟶ P.A)).left := by
    show (snd T P.A ≫ padd D.toPre.P.A (𝟙 D.toPre.P.A) (toUnit _ ≫ D.toPre.c 0)).left = _
    congr 1
    have e1 : snd T P.A ≫ padd D.toPre.P.A (𝟙 D.toPre.P.A) (toUnit _ ≫ D.toPre.c 0) =
        snd T P.A * (toUnit _ ≫ D.toPre.c 0) := by
      refine (MonObj.comp_mul (snd T P.A) (𝟙 _) (toUnit _ ≫ D.toPre.c 0)).trans ?_
      rw [Category.comp_id, ← Category.assoc, comp_toUnit]
    rw [e1, mul_comm, GlobalTheory.NoBasePoint.translPt_eq, c0, MonObj.comp_one]
    rfl
  have a2 : (snd T P.A).left ≫ D.toPre.famφB 0 2 = (T ⊗ P.A).hom ≫ (η[P.A]).left := by
    show (snd T P.A ≫ toUnit _ ≫ D.toPre.c 0).left = _
    rw [← Category.assoc, comp_toUnit, Over.comp_left, Over.toUnit_left, c0]
  have a3 : (snd T P.A).left ≫ D.toPre.famφB 0 3 = (T ⊗ P.A).hom ≫ (η[P.A]).left := by
    show (snd T P.A ≫ toUnit _ ≫ η[D.toPre.P.A]).left = _
    rw [← Category.assoc, comp_toUnit, Over.comp_left, Over.toUnit_left]
  obtain ⟨σ, hσ⟩ : UnitAt P.L (fun i => (snd T P.A).left ≫ D.toPre.famφB 0 i) (DegPre.famε k) y := by
    refine UnitAt.congr P.isLB (formEq_of_add fun U _ hh => ?_)
      (unitAt_pow hL P (Spec.map (CommRingCat.ofHom f)) xb (k - 2))
    rw [Fin.sum_univ_four, a0, a1, a2, a3, Fin.sum_univ_two]
    have hk' : ((k - 2 : ℕ) : ℤ) + 1 = (k : ℤ) - 1 := by omega
    simp only [DegPre.famε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, hk']
    abel
  obtain ⟨m, c', β, hβ⟩ := hTW R D.toPre k (by omega) 0 K f hf σ
  choose J hJ using fun ψ : (T ⊗ P.A).left ⟶ P.A.left => exists_chart P.isLB (ψ y)
  have hJ' : Good P.L y J := hJ
  have e6 := SectionScalarValuation.sval_lin (fun l => (fst T P.A).left.appTop.hom (c' l))
      (fun l => SectionArithmetic.pullSec (β l) (snd T P.A).left) (fun j => hβ j) (𝟙 _) y hJ'
  obtain ⟨i, -, hi⟩ := IsLocalRing.exists_of_isUnit_sum ((congrArg IsUnit e6).mp (hσ J hJ'))
  have hi' := isUnit_of_mul_isUnit_right hi
  rw [SectionArithmetic.sval_pullSec _ _ (𝟙 _) y hJ', Category.id_comp] at hi'
  rw [← hy]
  exact ⟨β i, _, mem_basicOpen_of_isUnit _ y _ (hJ'.mem _ _) _ hi'⟩

end GlobalTheory.Mum.SecBZeroBpf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpansionScalarArbitraryOfMembersZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Mum.ZeroFam

theorem gs_zero' {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) : gs f y U 0 = 0 := by
  unfold gs; split_ifs <;> simp

theorem sval_eq_zero {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (hs : ∀ j, s.f j = 0) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) :
    sval s r z J = 0 := by
  unfold sval; exact (congrArg (gs r z _) (hs _)).trans (gs_zero' _ _ _)

theorem secB_zero_of_pullB {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'}
    {D : DegPre R} {D' : DegPre R'} (hD : IsPullDeg φ D D') {k : ℕ} (x : D'.X) (b : D.SecB k (hD.xe x))
    (b' : D'.SecB k x) (hb : ∀ j, b.f j = 0) (h : PullB hD x b b') : ∀ q, b'.f q = 0 := by
  intro q
  refine fn_ext fun y hy => ?_
  choose p hp using fun κ => exists_chart D.P.isLB
    ((hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) ((D'.famφB x) κ y))
  have e := h _ (𝟙 _) y p q (fun κ => hp κ) (fun κ => Set.mem_iInter.1 hy κ)
  rw [show b.f p = 0 from hb _] at e
  have e2 := e.symm.trans (gs_zero' _ _ _)
  exact ((Units.mul_right_eq_zero _).1 e2).trans (gs_zero' _ _ _).symm

end GlobalTheory.Mum.ZeroFam

namespace GlobalTheory.Mum.ZeroFam

open GlobalTheory.ExpInt

theorem section_eq_zero_of_expansion_zero_family {W : Type} [CommRing W] [IsDomain W] {I : Ideal W} {D : DegData W I}
    {A : PolAV (Sp (FractionRing W))} {G : Over (Sp W)} [GrpObj G] [IsCommMonObj G] (U : Unif I D A G) {k : ℕ}
    (hk : 1 ≤ k) (σ : H0 U.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α) (hf : ∀ α j, (f α).f j = 0)
    (hE : ∀ e, U.ExpandsAt e k σ f) : ∀ j, σ.f j = 0 := by
  have := U.smooth
  have : Flat G.hom := inferInstance
  have ex : ∀ (φ' : Fin 1 → (pullback G.hom (jK W) ⟶ G.left))
      (_ : φ' = fun _ => pullback.fst G.hom (jK W) ≫ 𝟙 G.left),
      ∃ s' : LB.Sec (LB.LinComb U.LG.L φ' (fun _ => (k : ℤ))), ∀ z J, Good U.LG.L z J →
        sval s' (𝟙 _) z J = sval σ (pullback.fst G.hom (jK W)) z J := by
    rintro _ rfl
    exact ⟨pullSec _ _ _ σ _, fun z J hJ => (SectionScalarValuation.sval_pullSec _ _ σ _ (𝟙 _) z hJ).trans (by rw [Category.id_comp])⟩
  obtain ⟨s₀, hs₀⟩ := ex (fun _ => pullback.fst G.hom (jK W)) (funext fun _ => (Category.comp_id _).symm)
  have h1 : scal (pullback.snd G.hom (jK W) ≫ jK W) (1 : W) = 1 := by unfold scal; rw [map_one, map_one]
  have h1' : scal (DegPre.BF D.toPre (FractionRing W)).hom (1 : W) = 1 := by unfold scal; rw [map_one, map_one]
  have hF : ∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing W) α) (DegPre.famε k)
      ((0 : Fam D.toPre (FractionRing W) k).s α) (D.toPre.famφB α) (DegPre.famε k) (f α)
      (DegPre.prB D.toPre (FractionRing W)).left (scal (DegPre.BF D.toPre (FractionRing W)).hom 1) := fun α => by
    rw [h1']
    exact SectionScalarValuation.secScal_of_sval D.toPre.P.isLB fun y J _ =>
      (sval_eq_zero _ (hf α) _ y J).trans (sval_eq_zero _ (fun _ => rfl) _ y J).symm
  have hE₀ : ∀ e, U.ExpandsAt e k (SecOps.secZero : H0 U.LG.L k) f := fun e => by
    refine ⟨∅, fun α _ j => by rw [show (f α).f j = 0 from hf α j, map_zero], fun p j₁ jf jt _ _ => ?_⟩
    simp only [Finset.attach_empty, Finset.sum_empty]
    erw [show (SecOps.secZero : H0 U.LG.L k).f j₁ = 0 from rfl, map_zero, map_zero, mul_zero]
  have hEs₀ : U.Expands k s₀ 0 := ⟨1, one_ne_zero, σ, f, by
    rw [h1]
    exact SectionScalarValuation.secScal_of_sval U.LG.isLB fun y J hJ => by rw [Category.id_comp]; exact (hs₀ y J hJ).symm, hF, hE⟩
  have hEz : U.Expands k SecOps.secZero 0 := ⟨1, one_ne_zero, SecOps.secZero, f, by
    rw [h1]
    exact SectionScalarValuation.secScal_of_sval U.LG.isLB fun y J _ =>
      (sval_eq_zero _ (fun _ => rfl) _ y J).trans (sval_eq_zero _ (fun _ => rfl) _ y J).symm, hF, hE₀⟩
  have e₀ : s₀ = SecOps.secZero := ((U.expand k hk).2 0).unique hEs₀ hEz
  have hm := secIsMul_of_generic G U.LG.isLB k SecOps.secZero σ SecOps.secZero 1
    (SectionScalarValuation.secScal_of_sval U.LG.isLB fun y J _ =>
      (sval_eq_zero _ (fun _ => rfl) _ y J).trans (sval_eq_zero _ (fun _ => rfl) _ y J).symm)
    (by
      rw [h1]
      exact SectionScalarValuation.secScal_of_sval U.LG.isLB fun y J hJ => by rw [Category.id_comp, ← hs₀ y J hJ, e₀])
  intro j
  rw [hm j]
  exact mul_zero _

end GlobalTheory.Mum.ZeroFam

namespace GlobalTheory.Mum.ZeroFam

theorem exp_of_members_zero : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (k : ℕ), 1 ≤ k → ∀ (s : SecK C.P.L.L C.α k) (F : IntFam (maximalIdeal R) D.toPre k), (∀ α j, (F.f α).f j = 0) → ∀ a b : W, T.Exp a b s F → ∀ b' : W, T.Exp a b' s F := by
  intro R _ _ _ _ D C W _ _ _ T k hk s F hF a b hExp b'
  obtain ⟨σ, ⟨σ', f', hC, hP, hE⟩, hs⟩ := hExp
  have hf' : ∀ x q, (f' x).f q = 0 := fun x => secB_zero_of_pullB T.hD x _ (f' x) (hF _) (hP x)
  have hσ' := section_eq_zero_of_expansion_zero_family T.U hk σ' f' hf' hE
  refine ⟨σ, ⟨σ', f', fun Z r z J J' hJ hJ' => ?_, hP, hE⟩, hs⟩
  rw [hC Z r z J J' hJ hJ', sval_eq_zero _ hσ', mul_zero, mul_zero]

end GlobalTheory.Mum.ZeroFam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtLIPreimageMono
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem extLI_preimage_le {X X' Y : Scheme.{0}} (a : Y ⟶ X') (f : X' ⟶ X) (α : Y ⟶ X) (e : a ≫ f = α)
    (W : X.Opens) : a ⁻¹ᵁ (f ⁻¹ᵁ W) ≤ α ⁻¹ᵁ W := by
  intro y hy
  show α y ∈ W
  rw [← e, Scheme.Hom.comp_apply]
  exact hy

theorem extLI_le_chart {X X' Y : Scheme.{0}} (L : LB X) (f : X' ⟶ X) (a : Y ⟶ X') (α : Y ⟶ X) (e : a ≫ f = α)
    (W : X'.Opens) (j : L.ι) (hW : W ≤ f ⁻¹ᵁ L.U j) :
    a ⁻¹ᵁ W ≤ LB.wchart L (K := Fin 1) (fun _ => α) (fun _ => j) :=
  fun _ hy => Set.mem_iInter.2 fun _ => extLI_preimage_le a f α e (L.U j) (hW hy)

theorem extLI_le_wchart {X X' Y : Scheme.{0}} (L : LB X) (f : X' ⟶ X) (a : Y ⟶ X') (α : Y ⟶ X) (e : a ≫ f = α)
    (j : Fin 1 → L.ι) :
    a ⁻¹ᵁ LB.wchart L (K := Fin 1) (fun _ => f) j ≤ LB.wchart L (K := Fin 1) (fun _ => α) j :=
  fun _ hy => Set.mem_iInter.2 fun k => extLI_preimage_le a f α e (L.U (j k)) (Set.mem_iInter.1 hy k)

theorem extLI_preimage_mono {X Y : Scheme.{0}} (a : Y ⟶ X) {V V' : X.Opens} (hV : V ≤ V') : a ⁻¹ᵁ V ≤ a ⁻¹ᵁ V' :=
  fun _ hz => hV hz

theorem extLI_res_res {Y : Scheme.{0}} {U V W : Y.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (h3 : W ≤ U) (x : Γ(Y, U)) :
    (Y.presheaf.map (homOfLE h2).op).hom ((Y.presheaf.map (homOfLE h1).op).hom x) =
      (Y.presheaf.map (homOfLE h3).op).hom x := by
  change (Y.presheaf.map (homOfLE h1).op ≫ Y.presheaf.map (homOfLE h2).op).hom x = _
  rw [← Functor.map_comp]
  rfl

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendsToSemiAbelianOfLocalGroupsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extendsToSemiAbelian_of_local_groups : ∀ (σ : Setup) (E : Emb σ), σ.Common → (∀ x : Sp σ.R, ∃ g : σ.R, g ∉ x.asIdeal ∧ ∃ (H : Over (Sp (Localization.Away g))) (_ : GrpObj H) (h : H.left ⟶ E.P), E.LocGrp g H h ∧ Set.range h = E.U ∩ E.p ⁻¹' {z : Sp σ.R | g ∉ z.asIdeal}) → HasExt (awayMap σ.f) σ.A := by
  first | exact @GlobalTheory.Desc.Emb.hasExt_of_locGrp | exact GlobalTheory.Desc.Emb.hasExt_of_locGrp | (intros; apply GlobalTheory.Desc.Emb.hasExt_of_locGrp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamilyPulledBackNearPointOfEtaleCoordinatesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.family_pulled_back_near_point_of_etale_coordinates : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S X : Scheme.{0}) (π : S ⟶ Sp R) (U : Over (Sp R)) (a : X ⟶ U.left) (b : X ⟶ S) (g : ℕ) (τ : U.left ⟶ 𝔸(Fin g; Sp R)) (c : X ⟶ pullback (𝔸(Fin g; Sp R) ↘ Sp R) π), IsProper π → Surjective π → Function.Bijective π.appTop.hom → LocallyOfFiniteType U.hom → IsSeparated U.hom → IsProper a → (∀ V : U.left.Opens, Function.Bijective (a.app V).hom) → τ ≫ (𝔸(Fin g; Sp R) ↘ Sp R) = U.hom → c ≫ pullback.fst _ _ = a ≫ τ → c ≫ pullback.snd _ _ = b → Etale c → ∀ x : U.left, IsClosed ({x} : Set U.left) → U.hom x = closedPoint R → (∀ (Ω : Type) [Field Ω] (p p' : Sp Ω ⟶ X), Set.range (p ≫ a) = {x} → p ≫ a = p' ≫ a → p ≫ b = p' ≫ b → p = p') → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ξ : Sp Ω ⟶ U.left) (s : Sp Ω ⟶ S), Set.range ξ = {x} → ξ ≫ U.hom = s ≫ π → ∃ p : Sp Ω ⟶ X, p ≫ a = ξ ∧ p ≫ b = s) → ∀ V : U.left.Opens, x ∈ V → Etale (V.ι ≫ τ) → ∃ V : U.left.Opens, x ∈ V ∧ Etale (V.ι ≫ τ) ∧ IsPullback (a ∣_ V) ((a ⁻¹ᵁ V).ι ≫ b) (V.ι ≫ U.hom) π := by
  first | exact @GlobalTheory.Mum.EtalePull.main | exact GlobalTheory.Mum.EtalePull.main | (intros; apply GlobalTheory.Mum.EtalePull.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FfDescentPairs
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem ff_descent_pairs : ∀ (R : Type) [CommRing R] (D D' : Type) [CommRing D] [Algebra R D]
    [CommRing D'] [Algebra R D'] (ψ : D →ₐ[R] D'), (ψ : D →+* D').FaithfullyFlat → ∀ a : D',
    (∀ (E : Type) [CommRing E] [Algebra R E] (α β : D' →ₐ[R] E), α.comp ψ = β.comp ψ → α a = β a) →
      ∃! e : D, ψ e = a := by
  intro R _ D D' _ _ _ _ ψ hψ a h
  letI : Algebra D D' := (ψ : D →+* D').toAlgebra
  haveI : Module.FaithfullyFlat D D' := hψ
  haveI : IsScalarTower R D D' := IsScalarTower.of_algebraMap_eq (fun r => (ψ.commutes r).symm)
  have hinj : Function.Injective (algebraMap D D') := FaithfulSMul.algebraMap_injective D D'
  let α : D' →ₐ[R] D' ⊗[D] D' := Algebra.TensorProduct.includeLeft
  let β : D' →ₐ[R] D' ⊗[D] D' := (Algebra.TensorProduct.includeRight).restrictScalars R
  have hαβ : α.comp ψ = β.comp ψ := by
    ext x
    show ψ x ⊗ₜ[D] (1 : D') = (1 : D') ⊗ₜ[D] ψ x
    have : ψ x = algebraMap D D' x := rfl
    rw [this, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  have hab : a ⊗ₜ[D] (1 : D') = (1 : D') ⊗ₜ[D] a := h _ α β hαβ
  obtain ⟨e, he⟩ := GlobalTheory.ff_descent_elem D D' a hab
  exact ⟨e, he, fun e' he' => hinj (he'.trans he.symm)⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreDatumBaseChangeToCoarserPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibreDatum_baseChange_to_coarserPoint : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (g : ℕ) (L : RigLB G) (δ : LB S)
    (σ : (CechPic.tens L.L (δ.pull G.hom)).Sec) (i : δ.ι) (R R' K : Type) [CommRing R]
    [CommRing R'] [CommRing K] (ξ : Sp R ⟶ S) (r : R →+* R') (ξ' : Sp R' ⟶ S) (f : R' →+* K)
    (t : (KeyVals.bL L ξ).L.Sec) (y : Fin g → (epsR R ⟶ KeyVals.bG G ξ)) (t' : (KeyVals.bL L ξ').L.Sec)
    (y' : Fin g → (epsR R' ⟶ KeyVals.bG G ξ')) (x : KeyIn K) (hg : x.P.g = g),
    spMap r ≫ ξ = ξ' → ⊤ ≤ ξ ⁻¹ᵁ δ.U i → KeyVals.IsLocSec σ i ξ t → KeyVals.IsLocSec σ i ξ' t' →
    (∀ F : DualNumber R →+* DualNumber R', (∀ a, F (algebraMap R _ a) = algebraMap R' _ (r a)) →
      F DualNumber.eps = DualNumber.eps → ∀ j, (y' j).left ≫ pullback.fst G.hom ξ' = spMap F ≫ (y j).left ≫ pullback.fst G.hom ξ) →
    KeyOn f x (KeyVals.bG G ξ') (KeyVals.bL L ξ') t' (fun j => y' (j.cast hg)) →
    KeyOn (f.comp r) x (KeyVals.bG G ξ) (KeyVals.bL L ξ) t (fun j => y (j.cast hg)) := by
  first | exact @GlobalTheory.KeyValsTrans.keyOn_trans | exact GlobalTheory.KeyValsTrans.keyOn_trans | (intros; apply GlobalTheory.KeyValsTrans.keyOn_trans <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreEtaleRestrictOpenStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_etale_restrict_open_alt : ∀ (T X Z T' X' Z' S : Scheme.{0}) (p : X ⟶ T) (q : Z ⟶ T) (h : X ⟶ Z) (hh : h ≫ q = p) (p' : X' ⟶ T') (q' : Z' ⟶ T') (h' : X' ⟶ Z') (hh' : h' ≫ q' = p') (iT : T' ⟶ T) (iX : X' ⟶ X) (iZ : Z' ⟶ Z) [IsOpenImmersion iT] [IsOpenImmersion iX] [IsOpenImmersion iZ] (sZ : iZ ≫ q = q' ≫ iT) (sh : iX ≫ h = h' ≫ iZ) (x : S ⟶ T) (x' : S ⟶ T') (sx : x' ≫ iT = x) (W : (pullback p x).Opens) (w : ↥(pullback p x)) (hw : w ∈ W) (hz : pullback.fst p x w ∈ Set.range iX), Etale (W.ι ≫ pullback.map p x q x h (𝟙 _) (𝟙 _) (by simp [hh]) (by simp)) → ∃ (W' : (pullback p' x').Opens) (w' : ↥(pullback p' x')), w' ∈ W' ∧ iX (pullback.fst p' x' w') = pullback.fst p x w ∧ Etale (W'.ι ≫ pullback.map p' x' q' x' h' (𝟙 _) (𝟙 _) (by simp [hh']) (by simp)) := by
  first | exact @GlobalTheory.fibre_etale_restrict_open | exact GlobalTheory.fibre_etale_restrict_open | (intros; apply GlobalTheory.fibre_etale_restrict_open <;> assumption)
end

