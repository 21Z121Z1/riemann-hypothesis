import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2212
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2243
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2219
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0978
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2395
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2394
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2364
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2413
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftLeftFst
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2323

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPushforwardRegularIdeal
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Cartier.PullIdeal

open CartierDiv

theorem exists_pow_regularAt {Y : Scheme.{0}} [IsIntegral Y] (D : CartierDiv Y) {V : Y.Opens}
    (hV : IsCompact (V : Set Y)) (hηV : genericPoint Y ∈ V) (t : Γ(Y, V)) (F : Y.functionField)
    (hF : ∀ z ∈ Y.basicOpen t, D.RegularAt z F) :
    ∃ n : ℕ, ∀ z ∈ V, D.RegularAt z (fnOf V hηV t ^ n * F) := by
  by_cases ht : genericPoint Y ∈ Y.basicOpen t
  swap
  · refine ⟨1, fun z _ => ?_⟩
    have h0 : fnOf V hηV t = 0 := by
      by_contra h
      exact ht ((unitAt_fnOf_iff hηV hηV t).1 (unitAt_genericPoint h))
    rw [h0, pow_one, zero_mul]
    exact (D.vanishesAt_zero z).regularAt
  have loc : ∀ y : V, ∃ W : Y.Opens, y.1 ∈ W ∧ ∃ n : ℕ,
      ∀ z ∈ W, D.RegularAt z (fnOf V hηV t ^ n * F) := by
    intro y
    obtain ⟨V', hyV', g, hg⟩ := D.exists_isEqn_nhds y.1
    obtain ⟨W, hW, hyW, hWV⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens
      (show y.1 ∈ V ⊓ V' from ⟨y.2, hyV'⟩)
    have hWV1 : W ≤ V := hWV.trans inf_le_left
    set t' : Γ(Y, W) := Y.presheaf.map (homOfLE hWV1).op t
    have hB : Y.basicOpen t' = W ⊓ Y.basicOpen t := Y.basicOpen_res t _
    have hgen : genericPoint Y ∈ Y.basicOpen t' := hB ▸ memInf (gen_mem hyW) ht
    obtain ⟨b, hb⟩ := exists_fnOf_eq (f := F * (g : Y.functionField)) hgen fun z hz => by
      rw [hB] at hz
      exact (hg z (hWV hz.1).2).regularAt_iff.1 (hF z hz.2)
    obtain ⟨n, a, ha⟩ := exists_eq_pow_mul_of_isAffineOpen Y W hW t' b
    have key : fnOf W (gen_mem hyW) a = fnOf V hηV t ^ n * (F * (g : Y.functionField)) := by
      have e := congrArg (fnOf _ hgen) ha
      rw [map_mul, map_pow, hb] at e
      erw [SecPowLoc.fnOf_map, SecPowLoc.fnOf_map, SecPowLoc.fnOf_map] at e
      exact e
    refine ⟨W, hyW, n, fun z hz => (hg z (hWV hz).2).regularAt_iff.2 ?_⟩
    rw [mul_assoc, ← key]
    exact regAt_fnOf hz _ a
  choose W hyW n hn using loc
  obtain ⟨T, hT⟩ := hV.elim_finite_subcover (fun y : V => (W y : Set Y)) (fun y => (W y).isOpen)
    (fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, hyW _⟩)
  refine ⟨T.sup n, fun z hz => ?_⟩
  obtain ⟨y, hyT, hzy⟩ := Set.mem_iUnion₂.1 (hT hz)
  have hle : n y ≤ T.sup n := Finset.le_sup hyT
  have hr := regAt_fnOf hz hηV (t ^ (T.sup n - n y))
  rw [map_pow] at hr
  rw [← Nat.sub_add_cancel hle, pow_add, mul_assoc]
  exact (hn y z hzy).regAt_mul hr

theorem regAt_pull {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (s : Y ⟶ X) [IsDominant s]
    {U : X.Opens} {y : Y} (hy : s y ∈ U) (c : Γ(X, U)) :
    RegAt y (functionFieldMap s (fnOf U (gen_mem hy) c)) := by
  have hy' : y ∈ s ⁻¹ᵁ U := hy
  rw [← PullPres.fnOf_app s (gen_mem hy') c]
  exact regAt_fnOf hy' _ _

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (s : Y ⟶ X) [IsDominant s]
  (D : CartierDiv Y)

def pullIdeal (U : X.Opens) : Ideal Γ(X, U) where
  carrier := {f | ∀ (y : Y) (hy : s y ∈ U), D.RegularAt y (functionFieldMap s (fnOf U (gen_mem hy) f))}
  zero_mem' y hy := by rw [map_zero, map_zero]; exact (D.vanishesAt_zero y).regularAt
  add_mem' hf hg y hy := by rw [map_add, map_add]; exact (hf y hy).add (hg y hy)
  smul_mem' c f hf y hy := by
    rw [smul_eq_mul, map_mul, map_mul]
    exact (hf y hy).regAt_mul (regAt_pull s hy c)

def pullIdealSheaf [QuasiCompact s] : X.IdealSheafData where
  ideal U := pullIdeal s D U.1
  map_ideal_basicOpen U a := by
    show Ideal.map (X.presheaf.map (homOfLE (X.basicOpen_le a)).op).hom (pullIdeal s D U.1) =
      pullIdeal s D (X.basicOpen a)
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro f hf
      rw [Ideal.mem_comap]
      intro y hy
      have := hf y (X.basicOpen_le a hy)
      convert this using 3
      exact SecPowLoc.fnOf_map _ _ _
    · intro h hh
      by_cases hg : genericPoint X ∈ X.basicOpen a
      swap
      · have : h = 0 := fn_ext fun h' => (hg h').elim
        rw [this]; exact zero_mem _
      obtain ⟨n, b, hb⟩ := exists_eq_pow_mul_of_isAffineOpen X U.1 U.2 a h
      have hU0 : genericPoint X ∈ U.1 := X.basicOpen_le a hg
      have e' : fnOf U.1 hU0 b = fnOf U.1 hU0 a ^ n * fnOf _ hg h := by
        have := congrArg (fnOf _ hg) hb
        rw [map_mul, map_pow] at this
        erw [SecPowLoc.fnOf_map, SecPowLoc.fnOf_map] at this
        exact this
      obtain ⟨M, hM⟩ : ∃ M : ℕ, a ^ M * b ∈ pullIdeal s D U.1 := by
        by_cases hηV : genericPoint Y ∈ s ⁻¹ᵁ U.1
        · obtain ⟨M, hM⟩ := exists_pow_regularAt D (s.isCompact_preimage U.2.isCompact) hηV
            ((s.app U.1).hom a) (functionFieldMap s (fnOf U.1 hU0 b)) (fun z hz => by
              rw [← Scheme.preimage_basicOpen] at hz
              rw [e', map_mul, map_pow]
              have hr := regAt_pull s (U := U.1) (X.basicOpen_le a hz) (a ^ n)
              rw [map_pow, map_pow] at hr
              exact (hh z hz).regAt_mul hr)
          refine ⟨M, fun y hy => ?_⟩
          have := hM y hy
          rw [PullPres.fnOf_app] at this
          rw [map_mul, map_mul, map_pow, map_pow]
          exact this
        · exact ⟨0, fun y hy => (hηV (gen_mem (x := y) hy)).elim⟩
      have hu : IsUnit (X.presheaf.map (homOfLE (X.basicOpen_le a)).op a) :=
        X.toRingedSpace.isUnit_res_basicOpen a
      have hb' : X.presheaf.map (homOfLE (X.basicOpen_le a)).op (a ^ M * b) =
          h * (hu.unit : Γ(X, X.basicOpen a)) ^ (n + M) := by
        have hb2 : X.presheaf.map (homOfLE (X.basicOpen_le a)).op b =
            X.presheaf.map (homOfLE (X.basicOpen_le a)).op a ^ n * h := hb
        rw [map_mul, map_pow, hb2]
        rw [IsUnit.unit_spec, pow_add]
        ring
      have : h = X.presheaf.map (homOfLE (X.basicOpen_le a)).op (a ^ M * b) *
          ((hu.unit⁻¹ ^ (n + M) : (Γ(X, X.basicOpen a))ˣ) : Γ(X, X.basicOpen a)) := by
        rw [hb', mul_assoc, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← mul_pow, mul_inv_cancel,
          one_pow, Units.val_one, mul_one]
      rw [this]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hM)

theorem exists_idealSheaf : ∀ (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (s : Y ⟶ X) [IsDominant s]
    [QuasiCompact s] (D : CartierDiv Y), ∃ J : X.IdealSheafData, (∀ (U : X.affineOpens) (f : Γ(X, U.1)),
    f ∈ J.ideal U ↔ ∀ (y : Y) (hy : s y ∈ U.1), D.RegularAt y (functionFieldMap s (fnOf U.1 (gen_mem hy) f))) := by
  intro X Y _ _ s _ _ D
  exact ⟨pullIdealSheaf s D, fun _ _ => Iff.rfl⟩

end GlobalTheory.Cartier.PullIdeal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuotientNilCrystallineThickeningOfSubDPIde
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.PDA

namespace GlobalTheory.ThickQuot

section Ring

variable {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) {𝔟 : Ideal B}
  (h𝔟 : δ.IsSubDPIdeal 𝔟)
include h𝔟

theorem isSubDPIdeal_inf : δ.IsSubDPIdeal (𝔟 ⊓ J) := by
  rw [inf_eq_left.mpr h𝔟.isSubideal]; exact h𝔟

def qdp : DividedPowers (J.map (Ideal.Quotient.mk 𝔟)) :=
  DividedPowers.Quotient.dividedPowers δ (isSubDPIdeal_inf δ h𝔟)

theorem qdp_apply {n : ℕ} {a : B} (ha : a ∈ J) :
    (qdp δ h𝔟).dpow n (Ideal.Quotient.mk 𝔟 a) = Ideal.Quotient.mk 𝔟 (δ.dpow n a) :=
  DividedPowers.Quotient.dpow_apply δ (isSubDPIdeal_inf δ h𝔟) ha

theorem qdp_isDPMorphism : IsDPMorphism δ (qdp δ h𝔟) (Ideal.Quotient.mk 𝔟) :=
  DividedPowers.Quotient.isDPMorphism δ (isSubDPIdeal_inf δ h𝔟)

theorem lift_list (l : List (ℕ × (B ⧸ 𝔟))) (hl : ∀ p ∈ l, p.2 ∈ J.map (Ideal.Quotient.mk 𝔟)) :
    ∃ l' : List (ℕ × B), (∀ p ∈ l', p.2 ∈ J) ∧ l'.map Prod.fst = l.map Prod.fst ∧
      Ideal.Quotient.mk 𝔟 ((l'.map fun p ↦ δ.dpow p.1 p.2).prod) =
        (l.map fun p ↦ (qdp δ h𝔟).dpow p.1 p.2).prod := by
  induction l with
  | nil => exact ⟨[], by simp, rfl, by simp⟩
  | cons p l ih =>
    obtain ⟨l', h1, h2, h3⟩ := ih fun q hq ↦ hl q (List.mem_cons_of_mem _ hq)
    obtain ⟨a, ha, hpa⟩ :=
      (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 (hl p List.mem_cons_self)
    refine ⟨(p.1, a) :: l', ?_, ?_, ?_⟩
    · intro q hq
      rcases List.mem_cons.1 hq with rfl | hq
      · exact ha
      · exact h1 q hq
    · simp [h2]
    · simp only [List.map_cons, List.prod_cons, map_mul, h3]
      rw [← hpa, qdp_apply δ h𝔟 ha]

theorem isLev_qdp {n : ℕ} (hn : IsLev δ n) : IsLev (qdp δ h𝔟) n := by
  rw [isLev_iff_prod] at hn ⊢
  intro l hl hs
  obtain ⟨l', h1, h2, h3⟩ := lift_list δ h𝔟 l hl
  rw [← h3, hn l' h1 (h2 ▸ hs), map_zero]

theorem isDPNilpotent_quotient (hδ : IsNilDP δ) : IsNilDP (qdp δ h𝔟) := by
  rw [isDPNilpotent_iff_exists_isLevel] at hδ ⊢
  obtain ⟨n, hn⟩ := hδ
  exact ⟨n, isLev_qdp δ h𝔟 hn⟩

end Ring

section Thick

variable {R : Type} [CommRing R] {I : Ideal R} {κ : DividedPowers I} {X : Scheme.{0}} {t : X ⟶ Sp R}
  (T : Thick κ t) {𝔟 : Ideal T.B} (h𝔟 : T.δ.IsSubDPIdeal 𝔟)
include h𝔟

def quot : Thick κ t where
  B := T.B ⧸ 𝔟
  J := T.J.map (Ideal.Quotient.mk 𝔟)
  δ := qdp T.δ h𝔟
  nil := isDPNilpotent_quotient T.δ h𝔟 T.nil
  dp := by
    have : algebraMap R (T.B ⧸ 𝔟) = (Ideal.Quotient.mk 𝔟).comp (algebraMap R T.B) := rfl
    rw [this]
    exact (qdp_isDPMorphism T.δ h𝔟).comp _ T.dp
  B₀ := T.B₀
  π := Ideal.Quotient.lift 𝔟 T.π fun a ha ↦ (T.ker a).2 (h𝔟.isSubideal ha)
  surj := Ideal.Quotient.lift_surjective_of_surjective _ _ T.surj
  ker b := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [Ideal.Quotient.lift_mk, T.ker, Ideal.mem_quotient_iff_mem h𝔟.isSubideal]
  x := T.x
  w := by
    convert T.w using 2
    exact RingHom.ext fun _ ↦ rfl

def proj : T ⟶ quot T h𝔟 where
  φ := Ideal.Quotient.mkₐ R 𝔟
  φ₀ := RingHom.id T.B₀
  comm _ := rfl
  dp := qdp_isDPMorphism T.δ h𝔟
  pt := by
    show spMap (RingHom.id T.B₀) ≫ T.x = T.x
    rw [spMap_id, Category.id_comp]

def desc {S : Thick κ t} (a : T ⟶ S) (ha : ∀ b ∈ 𝔟, a.φ b = 0) : quot T h𝔟 ⟶ S where
  φ := Ideal.Quotient.liftₐ 𝔟 a.φ ha
  φ₀ := a.φ₀
  comm b := by
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective b
    exact a.comm c
  dp := by
    refine ⟨?_, fun {n} y hy ↦ ?_⟩
    · rw [Ideal.map_le_iff_le_comap]
      intro y hy
      obtain ⟨c, hc, rfl⟩ :=
        (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hy
      exact Thick.Hom.mem a hc
    · obtain ⟨c, hc, rfl⟩ :=
        (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hy
      have e1 : (quot T h𝔟).δ.dpow n (Ideal.Quotient.mk 𝔟 c) = Ideal.Quotient.mk 𝔟 (T.δ.dpow n c) :=
        qdp_apply T.δ h𝔟 hc
      rw [e1]
      exact a.dp.2 c hc
  pt := a.pt

end Thick

section Main

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

theorem exists_quotient : ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I) (X : Scheme.{0}) (t : X ⟶ Sp R) (T : Thick κ t) (𝔟 : Ideal T.B), T.δ.IsSubDPIdeal 𝔟 → ∃ (G : Thick κ t) (q : T ⟶ G), Function.Surjective q.φ ∧ (∀ b, q.φ b = 0 ↔ b ∈ 𝔟) ∧ G.J = T.J.map (q.φ : T.B →+* G.B) ∧ (∀ n, IsLev T.δ n → IsLev G.δ n) ∧ ∀ (S : Thick κ t) (a : T ⟶ S), (∀ b ∈ 𝔟, a.φ b = 0) → ∃! g : G ⟶ S, q ≫ g = a := by
  intro R _ I κ X t T 𝔟 h𝔟
  refine ⟨quot T h𝔟, proj T h𝔟, Ideal.Quotient.mkₐ_surjective R 𝔟, fun b ↦ Ideal.Quotient.eq_zero_iff_mem,
    rfl, fun n hn ↦ isLev_qdp T.δ h𝔟 hn, fun S a ha ↦
      ⟨desc T h𝔟 a ha, Thick.hom_ext fun _ ↦ rfl, fun g hg ↦ Thick.hom_ext fun b ↦ ?_⟩⟩
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective b
  exact congrArg (fun f : T ⟶ S ↦ f.φ c) hg

end Main

end GlobalTheory.ThickQuot
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalFunctionMapsOfCartierTwistSections
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Cartier

variable {Y : Scheme.{0}} [IsIntegral Y]

def chartEqn {D : CartierDiv Y} (i : (toLB D).ι) : Y.functionFieldˣ := (show EqnChart D from i).1.2

theorem gen_mem_chart {D : CartierDiv Y} (i : (toLB D).ι) : genericPoint Y ∈ (toLB D).U i :=
  (show EqnChart D from i).2.1

theorem isEqn_chartEqn {D : CartierDiv Y} (i : (toLB D).ι) {x : Y} (hx : x ∈ (toLB D).U i) :
    D.IsEqn x (chartEqn i) :=
  (show EqnChart D from i).2.2 x hx

theorem fnOf_g_chart {D : CartierDiv Y} (i j : (toLB D).ι) (h) :
    fnOf _ h ((toLB D).g i j).val = (chartEqn i : Y.functionField) / (chartEqn j : Y.functionField) :=
  fnOf_toLB_g i j h

def genChart (D : CartierDiv Y) : (toLB D).ι :=
  (exists_chart (isLB_toLB D) (genericPoint Y)).choose

def coordFn {D : CartierDiv Y} {W : Y.Opens}
    (a : sectionsOn (twist (GlobalTheory.structureModule Y) (toLB D)) W) (i : (toLB D).ι) :
    Γ(Y, W ⊓ (toLB D).U i) :=
  Twist.coord (sectionsOn.toΓ _ _ a) i

theorem coordFn_zero {D : CartierDiv Y} {W : Y.Opens} (i : (toLB D).ι) :
    coordFn (0 : sectionsOn (twist (GlobalTheory.structureModule Y) (toLB D)) W) i = 0 := rfl

theorem coordFn_add {D : CartierDiv Y} {W : Y.Opens}
    (a b : sectionsOn (twist (GlobalTheory.structureModule Y) (toLB D)) W) (i : (toLB D).ι) :
    coordFn (a + b) i = coordFn a i + coordFn b i := rfl

open Classical in

def ratOn (D : CartierDiv Y) (W : Y.Opens) :
    sectionsOn (twist (GlobalTheory.structureModule Y) (toLB D)) W →+ Y.functionField where
  toFun a := if h : genericPoint Y ∈ W then
      fnOf _ (memInf h (gen_mem_chart (genChart D))) (coordFn a (genChart D)) /
        (chartEqn (genChart D) : Y.functionField)
    else 0
  map_zero' := by
    split_ifs with h
    · rw [coordFn_zero, map_zero, zero_div]
    · rfl
  map_add' a b := by
    split_ifs with h
    · rw [coordFn_add, map_add, add_div]
    · rw [add_zero]

theorem ratOn_apply (D : CartierDiv Y) {W : Y.Opens} (h : genericPoint Y ∈ W)
    (a : sectionsOn (twist (GlobalTheory.structureModule Y) (toLB D)) W) :
    ratOn D W a = fnOf _ (memInf h (gen_mem_chart (genChart D))) (coordFn a (genChart D)) /
      (chartEqn (genChart D) : Y.functionField) :=
  dif_pos h

theorem ratOn_mul (D : CartierDiv Y) {W : Y.Opens} (h : genericPoint Y ∈ W)
    (a : sectionsOn (twist (GlobalTheory.structureModule Y) (toLB D)) W) (i : (toLB D).ι) :
    ratOn D W a * chartEqn i = fnOf _ (memInf h (gen_mem_chart i)) (coordFn a i) := by
  set j := genChart D
  have hij : genericPoint Y ∈ W ⊓ (toLB D).U i ⊓ (toLB D).U j :=
    memInf (memInf h (gen_mem_chart i)) (gen_mem_chart j)
  have e0 : resG Y (inf_le_left : W ⊓ (toLB D).U i ⊓ (toLB D).U j ≤ W ⊓ (toLB D).U i) (coordFn a i) =
      resG Y (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
          W ⊓ (toLB D).U i ⊓ (toLB D).U j ≤ (toLB D).U i ⊓ (toLB D).U j) ((toLB D).g i j).val *
        resG Y (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
          W ⊓ (toLB D).U i ⊓ (toLB D).U j ≤ W ⊓ (toLB D).U j) (coordFn a j) :=
    Twist.coord_rel (sectionsOn.toΓ _ _ a) i j _ _ _
  have e := congrArg (fnOf (W ⊓ (toLB D).U i ⊓ (toLB D).U j) hij) e0
  rw [map_mul, fnOf_resG, fnOf_resG, fnOf_resG, fnOf_g_chart] at e
  rw [ratOn_apply D h, e]
  have := (chartEqn j).ne_zero
  field_simp
  exact mul_comm _ _

end GlobalTheory.Cartier

namespace GlobalTheory.Cartier

variable {Y : Scheme.{0}} [IsIntegral Y]

theorem ratOn_regularAt (D : CartierDiv Y) {W : Y.Opens}
    (a : sectionsOn (twist (GlobalTheory.structureModule Y) (toLB D)) W) {y : Y} (hy : y ∈ W) :
    D.RegularAt y (ratOn D W a) := by
  obtain ⟨i, hi⟩ : ∃ i, y ∈ (toLB D).U i := exists_chart (isLB_toLB D) y
  refine ⟨chartEqn i, isEqn_chartEqn i hi, ?_⟩
  rw [ratOn_mul D (gen_mem hy) a i]
  exact regAt_fnOf (memInf hy hi) _ _

theorem exists_ratOn_eq (D : CartierDiv Y) {W : Y.Opens} (h : genericPoint Y ∈ W)
    {f : Y.functionField} (hf : ∀ y ∈ W, D.RegularAt y f) :
    ∃ a, ratOn D W a = f := by
  have key (i : (toLB D).ι) : ∃ b : Γ(Y, W ⊓ (toLB D).U i),
      fnOf _ (memInf h (gen_mem_chart i)) b = f * chartEqn i :=
    exists_fnOf_eq _ fun x hx => (isEqn_chartEqn i hx.2).regularAt_iff.1 (hf x hx.1)
  choose b hb using key
  have hmem : b ∈ Twist.secGroup (GlobalTheory.structureModule Y) (toLB D) W := fun i j =>
    fn_ext (U := W ⊓ (toLB D).U i ⊓ (toLB D).U j) fun hij => by
      show fnOf (W ⊓ (toLB D).U i ⊓ (toLB D).U j) hij
          (resG Y (inf_le_left : W ⊓ (toLB D).U i ⊓ (toLB D).U j ≤ W ⊓ (toLB D).U i) (b i)) =
        fnOf (W ⊓ (toLB D).U i ⊓ (toLB D).U j) hij
          (resG Y (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
              W ⊓ (toLB D).U i ⊓ (toLB D).U j ≤ (toLB D).U i ⊓ (toLB D).U j) ((toLB D).g i j).val *
            resG Y (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
              W ⊓ (toLB D).U i ⊓ (toLB D).U j ≤ W ⊓ (toLB D).U j) (b j))
      rw [map_mul, fnOf_resG, fnOf_resG, fnOf_resG, hb, hb, fnOf_g_chart]
      have := (chartEqn j).ne_zero
      field_simp
  refine ⟨(sectionsOn.toΓ _ _).symm (Twist.mkSec b hmem), ?_⟩
  have e := ratOn_mul D h ((sectionsOn.toΓ _ _).symm (Twist.mkSec b hmem)) (genChart D)
  exact mul_right_cancel₀ (chartEqn (genChart D)).ne_zero (e.trans (hb _))

theorem ratOn_res (D : CartierDiv Y) {W W' : Y.Opens} (hle : W' ≤ W)
    (a : sectionsOn (twist (GlobalTheory.structureModule Y) (toLB D)) W) (h : genericPoint Y ∈ W') :
    ratOn D W' (sectionsOn.res Γ(Y, ⊤) _ hle a) = ratOn D W a := by
  rw [ratOn_apply D h, ratOn_apply D (hle h)]
  have e : coordFn (sectionsOn.res Γ(Y, ⊤) _ hle a) (genChart D) =
      resG Y (inf_le_inf_right _ hle) (coordFn a (genChart D)) := rfl
  rw [e, fnOf_resG]

theorem exists_ratOn_twist : ∀ (Y : Scheme.{0}) [IsIntegral Y] (D : CartierDiv Y), ∃ ρ : ∀ W : Y.Opens, sectionsOn (twist (GlobalTheory.structureModule Y) (toLB D)) W →+ Y.functionField, (∀ (W : Y.Opens) (a), ∀ y ∈ W, D.RegularAt y (ρ W a)) ∧ (∀ (W : Y.Opens) (f : Y.functionField), genericPoint Y ∈ W → (∀ y ∈ W, D.RegularAt y f) → ∃ a, ρ W a = f) ∧ ∀ (W W' : Y.Opens) (h : W' ≤ W) (a), genericPoint Y ∈ W' → ρ W' (sectionsOn.res Γ(Y, ⊤) _ h a) = ρ W a :=
  fun Y _ D => ⟨ratOn D, fun _ a _ hy => ratOn_regularAt D a hy,
    fun _ _ h hf => exists_ratOn_eq D h hf, fun _ _ hle a h => ratOn_res D hle a h⟩

end GlobalTheory.Cartier
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealMultiplicationUniformizationStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_real_multiplication_uniformization : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (X : Obj F 𝔠 (Sp ℂ)), ∃ (L : LB X.A.left) (u : HolUnif X.A L (Module.finrank ℚ F)) (Fa : 𝓞 F →+* Module.End ℂ (Fin (Module.finrank ℚ F) → ℂ)), ∀ (a : 𝓞 F) (z : Fin (Module.finrank ℚ F) → ℂ), u.ex (Fa a z) = u.ex z ≫ X.rm.act a := by
  first | exact @GlobalTheory.RealMult.Obj.exists_holUnif_ringHom_lift | exact GlobalTheory.RealMult.Obj.exists_holUnif_ringHom_lift | (intros; apply GlobalTheory.RealMult.Obj.exists_holUnif_ringHom_lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRelationsLiftVanishingConductorStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_relations_lift_vanishing_conductor : (∀ (R R' ν : Type) [CommRing R] [CommRing R'] [Algebra R R'] (c : Ideal R), (∀ x ∈ c, ∀ r : R', ∃ y ∈ c, algebraMap R R' y = algebraMap R R' x * r) → ∀ G ∈ (c.map (algebraMap R R')).map (MvPolynomial.C : R' →+* MvPolynomial ν R'), ∃ H : MvPolynomial ν R, MvPolynomial.map (Ideal.Quotient.mk c) H = 0 ∧ MvPolynomial.map (algebraMap R R') H = G) → ∀ (R R' C' D E ν : Type) [CommRing R] [CommRing R'] [CommRing C'] [CommRing D] [CommRing E] [Algebra R R'] [Algebra R' C'] (c : Ideal R) [Algebra (R ⧸ c) D], (∀ x ∈ c, ∀ r : R', ∃ y ∈ c, algebraMap R R' y = algebraMap R R' x * r) → ∀ (π : C' →+* E) (ψ : D →+* E) (ζ : ν → D) (ξ : ν → C'), RingHom.ker π = c.map ((algebraMap R' C').comp (algebraMap R R')) → ψ.comp ((algebraMap (R ⧸ c) D).comp (Ideal.Quotient.mk c)) = (π.comp (algebraMap R' C')).comp (algebraMap R R') → (∀ s, π (ξ s) = ψ (ζ s)) → Function.Surjective (MvPolynomial.aeval ξ : MvPolynomial ν R' →ₐ[R'] C') → ∀ f : MvPolynomial ν (R ⧸ c), MvPolynomial.aeval ζ f = 0 → ∃ F : MvPolynomial ν R, MvPolynomial.map (Ideal.Quotient.mk c) F = f ∧ MvPolynomial.aeval ξ (MvPolynomial.map (algebraMap R R') F) = 0 := by
  first | exact @GlobalTheory.Pinch.relations_lift_vanishing | exact GlobalTheory.Pinch.relations_lift_vanishing | (intros; apply GlobalTheory.Pinch.relations_lift_vanishing <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRelativeFrobeniusGrpSchemeCharP
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.AbDual
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RelFrobGrp

open GlobalTheory.AbDual GlobalTheory.PDiv

variable {R R' : Type} [CommRing R] [CommRing R'] {A : Over (Sp R)} [GrpObj A] {A' : Over (Sp R')} [GrpObj A']
  {σ : R →+* R'} {φ : A'.left ⟶ A.left}

def down (m : GrpMor (dp0 R) (𝟙 _) A (dp0 R') (𝟙 _) A' σ (spMap σ) φ) {Y : Over (Sp R')} (x : Y ⟶ A') :
    Over.mk (Y.hom ≫ spMap σ) ⟶ A :=
  Over.homMk (x.left ≫ φ) (by simp [m.w])

theorem down_mul (m : GrpMor (dp0 R) (𝟙 _) A (dp0 R') (𝟙 _) A' σ (spMap σ) φ) {Y : Over (Sp R')} (x y : Y ⟶ A') :
    down m (x * y) = down m x * down m y :=
  Over.OverMorphism.ext (m.mul Y x y (down m x) (down m y) rfl rfl).symm

theorem main : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (hR : (p : R) = 0) (A A₁ : Over (Sp R)) [GrpObj A] [GrpObj A₁] (π : A₁.left ⟶ A.left), IsGrpPullback A₁ A (spMap (frobR p R hR)) π → ∃ F : A ⟶ A₁, IsMonHom F ∧ F.left ≫ π = GlobalTheory.VB.frob A.left p (cast_left p R hR A) := by
  intro p _ R _ hR A A₁ _ _ π hπ
  have mF := frobMor p R hR A (cast_left p R hR A)
  have mπ := grpMor_of_isGrpPullback hπ
  let F : A ⟶ A₁ := liftPt hπ A.hom _ mF.w
  have hF : F.left ≫ π = _ := liftPt_left hπ A.hom _ mF.w
  have dF : ∀ {Y : Over (Sp R)} (t : Y ⟶ A), down mπ (t ≫ F) = down mF t := fun t ↦
    Over.OverMorphism.ext ((Category.assoc _ _ _).trans (congrArg (t.left ≫ ·) hF))
  refine ⟨F, isMonHom_of_mul _ fun T x y ↦ pt_ext hπ ?_, hF⟩
  have e : down mπ ((x * y) ≫ F) = down mπ ((x ≫ F) * (y ≫ F)) := by rw [down_mul, dF, dF, dF, down_mul]
  exact congrArg (fun z ↦ z.left) e

end GlobalTheory.RelFrobGrp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingHomCyclotomicAwayToFieldPrimitiveRootStatement
section
open GlobalTheory.SiegelTor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ringHom_cyclotomicAway_to_field_primitiveRoot : ∀ (M : ℕ), M ≠ 0 → ∀ (K : Type) [Field K] (y : K), IsPrimitiveRoot y M → IsUnit (M : K) →
  ∃ β : cycAway M →+* K, β (zetaAway M) = y := by
  first | (exact @GlobalTheory.CycLift.exists_hom_to_field) | (exact GlobalTheory.CycLift.exists_hom_to_field) | (intros; apply GlobalTheory.CycLift.exists_hom_to_field  <;> assumption)
end

