import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0114
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3122
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3189
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3131
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3285
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3251
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3279
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3281
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2436
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1265
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3017
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3206
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3124
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3145
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3282
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3255
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3132
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3129
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3283
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumMultPullbackRationalSectionPushforward
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PushDiv

theorem hasDim_lt {X : Scheme.{0}} {x y : X} {d d' : ℕ} (hxy : y ⤳ x) (hne : x ≠ y)
    (hx : HasDim x d) (hy : HasDim y d') : d < d' := by
  have hsub : closure ({x} : Set X) ⊆ closure {y} := specializes_iff_closure_subset.1 hxy
  have hne' : closure ({x} : Set X) ≠ closure {y} := fun e =>
    hne (inseparable_iff_closure_eq.2 e).eq
  have h := topologicalKrullDim_add_one_le_of_ssubset X _ _ isClosed_closure
    isIrreducible_singleton.closure isIrreducible_singleton.closure (ssubset_of_subset_of_ne hsub hne')
  rw [show topologicalKrullDim (closure ({x} : Set X)) = d from hx,
    show topologicalKrullDim (closure ({y} : Set X)) = d' from hy] at h
  have h' : ((d + 1 : ℕ) : WithBot ℕ∞) ≤ (d' : WithBot ℕ∞) := by exact_mod_cast h
  have h'' : d + 1 ≤ d' := by exact_mod_cast h'
  omega

theorem mult_genericPoint {Z : Scheme.{0}} [IsIntegral Z] [IsLocallyNoetherian Z] (D : CartierDiv Z) :
    D.mult (genericPoint Z) = 0 := by
  rw [(D.isEqn_genericPoint 1).mult_eq]
  exact (unitAt_one _).ord_eq_zero

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
  (g : Y ⟶ X) (hη' : g (genericPoint Y) ⤳ genericPoint X) {B : LB X} (hB : B.IsLB)
  {r : B.ι → X.functionFieldˣ} (hr : IsRatSec B r)

theorem mult_pull_eq (w : Y) (i : B.ι) (hi : g w ∈ B.U i) :
    (divOfRatSec (LB.isLB_pull hB g) (MultPull.isRatSec_pull_map g hη' hr)).mult w =
      Scheme.ord (TrueGeo.SmallSec.fnMap g hη' (r i : X.functionField)) w :=
  by
  have hm : w ∈ (B.pull g).U (fun _ => i) := Set.mem_iInter.2 fun _ => hi
  have h := (presents_divOfRatSec (LB.isLB_pull hB g) (MultPull.isRatSec_pull_map g hη' hr)).isEqn
    (fun _ => i) w hm
  rw [h.mult_eq]
  rfl

theorem mult_eq_chart (z : X) (i : B.ι) (hi : z ∈ B.U i) :
    (divOfRatSec hB hr).mult z = Scheme.ord (r i : X.functionField) z :=
  ((presents_divOfRatSec hB hr).isEqn i z hi).mult_eq

theorem map_ne_genericPoint (w : Y)
    (hw : (divOfRatSec (LB.isLB_pull hB g) (MultPull.isRatSec_pull_map g hη' hr)).mult w ≠ 0) :
    g w ≠ genericPoint X := by
  intro e
  obtain ⟨i, hi⟩ := exists_chart hB (g w)
  apply hw
  rw [mult_pull_eq g hη' hB hr w i hi]
  exact (FrameGlue.Pull.unitAt_fnMap g hη' (e ▸ unitAt_genericPoint (r i).ne_zero)).ord_eq_zero

end GlobalTheory.PushDiv

namespace GlobalTheory.PushDiv

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
  (g : Y ⟶ X) (hη' : g (genericPoint Y) ⤳ genericPoint X) {B : LB X} (hB : B.IsLB)
  {r : B.ι → X.functionFieldˣ} (hr : IsRatSec B r)
  {k : Type} [CommRing k] {p : X ⟶ Sp k} {q : Y ⟶ Sp k}

theorem degree_ne_zero_and_coheight (hp : IsAmb p) (hq : IsAmb q) (hg : g ≫ p = q)
    (hη : g (genericPoint Y) = genericPoint X) (w : Y)
    (hw : (divOfRatSec (LB.isLB_pull hB g) (MultPull.isRatSec_pull_map g hη' hr)).mult w ≠ 0)
    (hd : g.residueDegree w ≠ 0) :
    g.residueDegree (genericPoint Y) ≠ 0 ∧ Order.coheight (g w) = 1 := by
  have hw1 := CartierDiv.coheight_eq_one_of_mult_ne_zero hw
  have hgw := map_ne_genericPoint g hη' hB hr w hw
  have hwY : w ≠ genericPoint Y := fun e => hw (e ▸ mult_genericPoint _)
  have AY := GlobalTheory.T.hasPointClosureDim_basic_projArithAmbient k Y q hq
  have AX := GlobalTheory.T.hasPointClosureDim_basic_projArithAmbient k X p hp
  obtain ⟨mY, hmY⟩ := AY.1
  obtain ⟨mX, hmX⟩ := AX.1
  obtain ⟨dY, -, hdY⟩ := hmY (genericPoint Y)
  obtain ⟨dw, -, hdw⟩ := hmY w
  have hlt : dw < dY := hasDim_lt (genericPoint_specializes w) hwY hdw hdY
  obtain ⟨e, rfl⟩ : ∃ e, dY = e + 1 := ⟨dY - 1, by omega⟩
  have hYdim : topologicalKrullDim Y = ((e + 1 : ℕ) : WithBot ℕ∞) := (AY.2.2.2.2.2 Y (e + 1)).1 hdY
  have hwe : HasDim w e := ((GlobalTheory.T.coheight_one_iff_pointClosure_dim_projArith k Y q hq e hYdim).1 w).1 hw1
  obtain ⟨dgw, -, hdgw⟩ := hmX (g w)
  obtain ⟨dX, -, hdX⟩ := hmX (genericPoint X)
  have h1 := GlobalTheory.T.pointClosureDim_le_and_residueDegree_ne_zero_iff k X Y p q hp hq g hg w e dgw hwe hdgw
  have hdX' : HasDim (g (genericPoint Y)) dX := by rw [hη]; exact hdX
  have h2 := GlobalTheory.T.pointClosureDim_le_and_residueDegree_ne_zero_iff k X Y p q hp hq g hg (genericPoint Y) (e + 1) dX hdY hdX'
  have h3 : dgw < dX := hasDim_lt (genericPoint_specializes (g w)) hgw hdgw hdX
  have he : e = dgw := h1.2.1 hd
  have hXe : dX = e + 1 := by omega
  refine ⟨h2.2.2 hXe.symm, ?_⟩
  have hXdim : topologicalKrullDim X = ((e + 1 : ℕ) : WithBot ℕ∞) :=
    (AX.2.2.2.2.2 X (e + 1)).1 (hXe ▸ hdX)
  exact ((GlobalTheory.T.coheight_one_iff_pointClosure_dim_projArith k X p hp e hXdim).1 (g w)).2 (he ▸ hdgw)

end GlobalTheory.PushDiv

namespace GlobalTheory.PushDiv

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
  (g : Y ⟶ X) (hη' : g (genericPoint Y) ⤳ genericPoint X) {B : LB X} (hB : B.IsLB)
  {r : B.ι → X.functionFieldˣ} (hr : IsRatSec B r)
  {k : Type} [CommRing k] {p : X ⟶ Sp k} {q : Y ⟶ Sp k}

open Classical in

theorem fiber_sum (hp : IsAmb p) (hq : IsAmb q) (hg : g ≫ p = q)
    (hη : g (genericPoint Y) = genericPoint X) [CompactSpace Y] (z : X) :
    ∑ w ∈ (CartierDiv.finite_support_mult
        (divOfRatSec (LB.isLB_pull hB g) (MultPull.isRatSec_pull_map g hη' hr))).toFinset with g w = z,
      (divOfRatSec (LB.isLB_pull hB g) (MultPull.isRatSec_pull_map g hη' hr)).mult w *
        (g.residueDegree w : ℤ) =
    (g.residueDegree (genericPoint Y) : ℤ) * (divOfRatSec hB hr).mult z := by
  by_cases h : g.residueDegree (genericPoint Y) ≠ 0 ∧ Order.coheight z = 1
  · obtain ⟨i, hi⟩ := exists_chart hB z
    have H := GlobalTheory.T.sum_schemeOrd_pullback_residueDegree_codimOne k X Y p q hp hq g hg hη h.1 z h.2 (r i : X.functionField) (r i).ne_zero
    have H2 : ∑ᶠ w ∈ g ⁻¹' {z},
        (divOfRatSec (LB.isLB_pull hB g) (MultPull.isRatSec_pull_map g hη' hr)).mult w *
          (g.residueDegree w : ℤ) =
        (g.residueDegree (genericPoint Y) : ℤ) * (divOfRatSec hB hr).mult z := by
      rw [mult_eq_chart hB hr z i hi, ← H]
      refine finsum_mem_congr rfl fun w hw => ?_
      have hw' : g w = z := hw
      rw [mult_pull_eq g hη' hB hr w i (by rw [hw']; exact hi)]
    rw [← H2]
    refine (finsum_mem_eq_sum_of_inter_support_eq _ ?_).symm
    ext w
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Finset.coe_filter,
      Set.Finite.mem_toFinset, Function.mem_support, Set.mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨⟨left_ne_zero_of_mul h2, h1⟩, h2⟩
    · rintro ⟨⟨-, h1⟩, h2⟩; exact ⟨h1, h2⟩
  · have hR : (g.residueDegree (genericPoint Y) : ℤ) * (divOfRatSec hB hr).mult z = 0 := by
      by_cases hδ : g.residueDegree (genericPoint Y) = 0
      · rw [hδ, Nat.cast_zero, zero_mul]
      · have hz : Order.coheight z ≠ 1 := fun hz => h ⟨hδ, hz⟩
        rw [show (divOfRatSec hB hr).mult z = 0 from
          by_contra fun h0 => hz (CartierDiv.coheight_eq_one_of_mult_ne_zero h0), mul_zero]
    rw [hR]
    refine Finset.sum_eq_zero fun w hw => ?_
    have hwz : g w = z := (Finset.mem_filter.1 hw).2
    by_contra hne
    have h1 := left_ne_zero_of_mul hne
    have h2 : g.residueDegree w ≠ 0 := fun h0 => hne (by rw [h0, Nat.cast_zero, mul_zero])
    obtain ⟨hδ, hc⟩ := degree_ne_zero_and_coheight g hη' hB hr hp hq hg hη w h1 h2
    exact h ⟨hδ, hwz ▸ hc⟩

end GlobalTheory.PushDiv

namespace GlobalTheory.PushDiv

theorem finsum_mult_pull : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k), IsAmb p → IsAmb q → ∀ (g : Y ⟶ X) (hg : g ≫ p = q) (hη : g (genericPoint Y) = genericPoint X), ∀ (B : LB X) (hB : B.IsLB) (r : B.ι → X.functionFieldˣ) (hr : IsRatSec B r) (φ : X → ℝ), ∑ᶠ w, ((divOfRatSec (LB.isLB_pull hB g) (MultPull.isRatSec_pull_map g (hη ▸ specializes_rfl : g (genericPoint Y) ⤳ genericPoint X) hr)).mult w : ℝ) * ((g.residueDegree w : ℝ) * φ (g w)) = (g.residueDegree (genericPoint Y) : ℝ) * ∑ᶠ z, ((divOfRatSec hB hr).mult z : ℝ) * φ z := by
  intro k _ X Y _ _ _ _ p q hp hq g hg hη B hB r hr φ
  classical
  haveI := hq.isNoetherian
  haveI := hp.isNoetherian
  set D' := divOfRatSec (LB.isLB_pull hB g) (MultPull.isRatSec_pull_map g
    (hη ▸ specializes_rfl : g (genericPoint Y) ⤳ genericPoint X) hr) with hD'
  set D := divOfRatSec hB hr with hD
  set S := D'.finite_support_mult.toFinset with hS
  set T := S.image g ∪ D.finite_support_mult.toFinset with hT
  have hL : ∑ᶠ w, (D'.mult w : ℝ) * ((g.residueDegree w : ℝ) * φ (g w)) =
      ∑ w ∈ S, (D'.mult w : ℝ) * ((g.residueDegree w : ℝ) * φ (g w)) := by
    apply finsum_eq_sum_of_support_subset
    intro w hw
    rw [hS, Set.Finite.coe_toFinset]
    exact fun h0 => hw (by simp only [h0, Int.cast_zero, zero_mul])
  have hR : ∑ᶠ z, (D.mult z : ℝ) * φ z = ∑ z ∈ T, (D.mult z : ℝ) * φ z := by
    apply finsum_eq_sum_of_support_subset
    intro z hz
    rw [hT, Finset.coe_union, Set.Finite.coe_toFinset]
    exact Or.inr fun h0 => hz (by simp only [h0, Int.cast_zero, zero_mul])
  rw [hL, hR, ← Finset.sum_fiberwise_of_maps_to (s := S) (t := T) (g := g)
    (fun w hw => Finset.mem_union_left _ (Finset.mem_image_of_mem g hw)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  have hF := fiber_sum g (hη ▸ specializes_rfl : g (genericPoint Y) ⤳ genericPoint X) hB hr hp hq hg hη z
  calc ∑ w ∈ S with g w = z, (D'.mult w : ℝ) * ((g.residueDegree w : ℝ) * φ (g w))
      = ((∑ w ∈ S with g w = z, D'.mult w * (g.residueDegree w : ℤ) : ℤ) : ℝ) * φ z := by
        rw [Int.cast_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun w hw => ?_
        rw [(Finset.mem_filter.1 hw).2]
        push_cast
        ring
    _ = (g.residueDegree (genericPoint Y) : ℝ) * ((D.mult z : ℝ) * φ z) := by
        rw [hF]
        push_cast
        ring

end GlobalTheory.PushDiv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionsEqSeriesInChart
section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz.Chart

theorem functions_are_series : ∀ (p : ℕ) (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k)
    (c : Chart G d), (∀ n f, G.res n (c.ev (n + 1) f) = c.ev n f) ∧
    (∀ n s, pullbackTwo (G.res n) (c.ev₂ (n + 1) s) = c.ev₂ n s) ∧
    ∀ b : ∀ n, G.A n, (∀ n, G.res n (b (n + 1)) = b n) → ∃! f, ∀ n, c.ev n f = b n := by
  intro p k _ d G c
  refine ⟨fun n f => ?_, fun n s => ?_, fun b hb => ?_⟩
  · exact (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin d) (G.A (n + 1))).2 (G.A n) (G.res n : G.A (n + 1) →ₐ[k] G.A n)
      (c.x (n + 1)) (c.nil (n + 1)) (c.x n) (c.nil n) (fun i => c.res n i) f
  · let g : G.A (n + 1) →ₐ[k] G.A n := G.res n
    have h := (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin d ⊕ Fin d) (G.A (n + 1) ⊗[k] G.A (n + 1))).2
      (G.A n ⊗[k] G.A n) (Algebra.TensorProduct.map g g)
      (c.x₂ (n + 1)) (c.nil₂ (n + 1)) (c.x₂ n) (c.nil₂ n) (fun i => by
        cases i with
        | inl i => simp [x₂, g, c.res n i]
        | inr i => simp [x₂, g, c.res n i]) s
    refine Eq.trans ?_ h
    rfl
  · exact GlobalTheory.T.existsUnique_powerSeries_of_compatible_system k (Fin d) G.A c.x c.nil (fun n => (G.res n : G.A (n + 1) →ₐ[k] G.A n))
      (fun n i => c.res n i) c.presents b hb

end GlobalTheory.Katz.Chart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricFunctionalChernIntegralStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometric_functional_chern_integral : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) (hX : IsRegVar p D) (ι : Type) [Fintype ι] (L : ι → HermLB p) (Ψ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ),
    IsGeoFun L D Ψ → ∀ G : MvPolynomial ι ℝ, G.IsHomogeneous D →
      Ψ G = ∑ᶠ σ : k →+* ℂ, (hX.atlas σ).integral (evalF (hX.atlas σ) (fun i => c1F hX σ (L i)) G) := by
  first | exact @GlobalTheory.LineForm.GeoInt.geoFun_eq_integral | exact GlobalTheory.LineForm.GeoInt.geoFun_eq_integral | (intros; apply GlobalTheory.LineForm.GeoInt.geoFun_eq_integral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieTateLociClosedSiegelPullbackStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_lie_tate_loci_closed_siegelPullback : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (h M : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Scheme.{0}) (s₁ : S ⟶ Sp B) (t : S ⟶ Sp R) (c : SiegPre h M ζ s₁) (e : ℕ), e.Coprime p → SiegKerBy c e → ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (πX : X ⟶ S) (AX : Over X) [GrpObj AX] [IsCommMonObj AX] (φX : AX.left ⟶ c.A.left) (φ₂X : (G2 AX).left ⟶ (G2 c.A).left) (actX : OActN D.O AX) (ηX : D.La → (𝟙_ (Over X) ⟶ AX)), IsGrpPullback AX c.A πX φX → IsSquare φX φ₂X → RosatiFor D actX (c.P.pull φ₂X) → EtaOK D N actX ηX → ∃ (Z : Scheme.{0}) (j : Z ⟶ X), IsClosedImmersion j ∧ ∀ (T : Scheme.{0}) (g : T ⟶ X), (∃ z : T ⟶ Z, z ≫ j = g) ↔ ((∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ T), x ≫ g ≫ πX ≫ t = spMap β → LieHer b actX β (x ≫ g)) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ T) (β : R →+* k), x ≫ g ≫ πX ≫ t = spMap β → GeomAt D N actX (c.P.pull φ₂X) ηX k (x ≫ g)) := by
  first | (exact @GlobalTheory.UPel.HT.lieGeom_locus_closed) | (exact GlobalTheory.UPel.HT.lieGeom_locus_closed) | (intros; apply GlobalTheory.UPel.HT.lieGeom_locus_closed  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeTraceVectorValuedEqFiniteKernelSumStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeTrace_vectorValued_eq_finite_kernelSum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → trOn (GlobalTheory.BCT.TrKer.vecM S lam K') (GlobalTheory.BCT.TrKer.hopM S lam K' f) = (((globLev S K').relIndex (globLev S (KL n)) : ℕ) : ℂ)⁻¹ * ∑ᶠ q : DoubleCoset.Quotient (ratFinU E n : Set (finU E n)) (globLev S K' : Set (finU E n)), ((Nat.card (ratFinU E n ⊓ (globLev S K').map (MulAut.conj (Quotient.out q)).toMonoidHom : Subgroup (finU E n)) : ℂ))⁻¹ * ∑ᶠ γ : UE E n, globFn S f ((Quotient.out q)⁻¹ * finPt γ * Quotient.out q) * LinearMap.trace ℂ _ (GlobalTheory.BCT.TrKer.wAt lam γ⁻¹) := by
  first | exact @GlobalTheory.BCT.TrKer.trOn_vecM_hopM | exact GlobalTheory.BCT.TrKer.trOn_vecM_hopM | (intros; apply GlobalTheory.BCT.TrKer.trOn_vecM_hopM <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightGenericPointNonnegAmpleSemiPositiveStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_genericPoint_nonneg_ample_semiPositive : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → 1 ≤ D → ∀ (C : HermLB p) (h : X → ℝ), IsAmpleLB C.B → C.SemiPos D → C.IsArithHeight h → (∀ z, z ≠ genericPoint X → 0 ≤ h z) → 0 ≤ h (genericPoint X) := by
  first | exact @GlobalTheory.HSNef.height_generic_nonneg_of_ample | exact GlobalTheory.HSNef.height_generic_nonneg_of_ample | (intros; apply GlobalTheory.HSNef.height_generic_nonneg_of_ample <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomDegreeIntegerCombinationIsHomogeneous
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.AV.AbVar.multilinear_quadratic_isHomogeneous' (P : Type*) [AddCommGroup P] (g n : ℕ)
    (M : MultilinearMap ℤ (fun _ : Fin g => P) ℤ) (a : Fin n → Fin n → P) :
    ∃ F : MvPolynomial (Fin n) ℤ, F.IsHomogeneous (2 * g) ∧
      ∀ m : Fin n → ℤ, MvPolynomial.eval m F = M (fun _ => ∑ i, ∑ j, (m i * m j) • a i j) := by
  let φ : (Fin n → Fin n → ℤ) →ₗ[ℤ] P :=
    { toFun := fun x => ∑ i, ∑ j, x i j • a i j
      map_add' := fun x y => by
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun r x => by
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply] }
  let e : Fin n → Fin n → (Fin n → Fin n → ℤ) := fun i j => Pi.single i (Pi.single j 1)
  have he : ∀ i j, φ (e i j) = a i j := by
    intro i j
    simp only [φ, e, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Finset.sum_eq_single i (fun k _ hk => by simp [Pi.single_apply, hk]) (by simp)]
    rw [Finset.sum_eq_single j (fun k _ hk => by simp [Pi.single_apply, hk]) (by simp)]
    simp
  obtain ⟨F, hF, hFe⟩ := GlobalTheory.multilinear_quadratic_isHomogeneous (Fin n → Fin n → ℤ) g n
    (M.compLinearMap (fun _ => φ)) e
  refine ⟨F, hF, fun m => ?_⟩
  rw [hFe m, MultilinearMap.compLinearMap_apply]
  congr 1
  funext _
  simp only [map_sum, map_zsmul, he]

theorem GlobalTheory.AV.AbVar.deg_isHomogeneousPoly : ∀ (K : Type) [Field K] (A B : AbVar K), A.dim = B.dim → ∀ (n : ℕ) (f : Fin n → (A ⟶ B)), ∃ F : MvPolynomial (Fin n) ℚ, F.IsHomogeneous (2 * A.dim) ∧ ∀ m : Fin n → ℤ, MvPolynomial.eval (fun i => (m i : ℚ)) F = (deg (∑ i, m i • f i) : ℚ) := by
  intro K _ A B hAB n f
  obtain ⟨c, hamp, hsym⟩ := GlobalTheory.AV.AbVar.exists_symm_ample K B
  obtain ⟨⟨M, hM⟩, -⟩ := GlobalTheory.T.intersection_number_multilinear_symm K A (Fin A.dim) (Fintype.card_fin _)
  set D : ℤ := inter B (fun _ : Fin A.dim => c) with hD
  have hDpos : 0 < D := GlobalTheory.T.abelianVariety_topSelfIntersection_ample_pos K B c hamp (Fin A.dim) (by rw [Fintype.card_fin, hAB])
  obtain ⟨F, hFh, hFe⟩ := GlobalTheory.AV.AbVar.multilinear_quadratic_isHomogeneous' (Pic A.X.left) A.dim n M
    (fun i j => AbVar.lam c (f i).hom (f j).hom)
  refine ⟨MvPolynomial.C ((1 : ℚ) / ((2 : ℚ) ^ A.dim * D)) * MvPolynomial.map (Int.castRingHom ℚ) F, ?_, ?_⟩
  · have := (MvPolynomial.isHomogeneous_C (Fin n) ((1 : ℚ) / ((2 : ℚ) ^ A.dim * D))).mul (hFh.map (Int.castRingHom ℚ))
    rwa [zero_add] at this
  · intro m
    have hq := GlobalTheory.T.two_smul_pullback_symmetric_class_integral_combination K A B c hsym n f m
    have hp := GlobalTheory.T.intersection_pullback_eq_degree_mul_intersection K A B (show A ⟶ B from ∑ i, m i • f i) hAB (Fin A.dim) (Fintype.card_fin _) (fun _ => c)
    have key : MvPolynomial.eval m F = 2 ^ A.dim * ((deg (show A ⟶ B from ∑ i, m i • f i) : ℤ) * D) := by
      rw [hFe m, ← hq, ← hp, ← hM]
      have := M.map_smul_univ (fun _ => (2 : ℤ)) (fun _ => CechPic.pull (Hom.hom (show A ⟶ B from ∑ i, m i • f i)).left c)
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at this
      rw [← this]
      congr 1
    rw [MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_map]
    have e2 : MvPolynomial.eval₂ (Int.castRingHom ℚ) (fun i => (m i : ℚ)) F = ((MvPolynomial.eval m F : ℤ) : ℚ) := by
      rw [MvPolynomial.eval, MvPolynomial.coe_eval₂Hom, ← eq_intCast (Int.castRingHom ℚ), MvPolynomial.eval₂_comp_left]
      rfl
    rw [e2, key]
    have hD0 : (D : ℚ) ≠ 0 := by exact_mod_cast hDpos.ne'
    push_cast
    field_simp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InductiveMixedHeightReciprocityTwoSections
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt

set_option autoImplicit false

theorem mixRecVal_cons_eq_resCyc_sub_resArch {k : Type} [CommRing k] {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] {q : Y ⟶ Sp k} (hA : IsAmb q) {e : ℕ} (hdim : topologicalKrullDim Y = (e + 1 + 1 : ℕ))
    {T : ∀ d : ℕ, (Fin d → HermLB q) → Y → ℝ} (hT : IsMix q (e + 1) T) (N : HermLB q) (L : Fin e → HermLB q)
    (t : N.B.Sec) {z : Y} (hz : Order.coheight z = 1) (hzt : z ∈ nonzeroLocus t) :
    T (e + 1) (Fin.cons N L) z = resCyc N.isLB t (T e L) z - resArch L N t z := by
  have hg : genericPoint (clo z) ∈ nonzeroLocus (secPull t (cloι z)) := by
    rw [GlobalTheory.nonzeroLocus_secPull]
    show cloι z (genericPoint (clo z)) ∈ nonzeroLocus t
    rw [cloι_genericPoint]
    exact hzt
  have hd : topologicalKrullDim (clo z) = ((e + 1 : ℕ) : WithBot ℕ∞) :=
    ((GlobalTheory.T.coheight_one_iff_pointClosure_dim_projArith k Y q hA (e + 1) hdim).2 z (genericPoint (clo z)) hz).1
  have h := hT.recur (clo z) (cloι z ≫ q) (cloι z) rfl e le_rfl hd N L (N.restr (cloι z))
    (fun a => (L a).restr (cloι z)) (HermLB.Isometric.refl _) (fun _ => HermLB.Isometric.refl _) _
    (isRatSec_ratOfSec _ hg)
  rw [cloι_genericPoint] at h
  rw [h, resCyc, resArch, dif_pos hg, dif_pos hg]
  rfl

end GlobalTheory.MixHt

namespace GlobalTheory.MixHt

theorem finite_support_mult_mul {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [CompactSpace Y]
    (D : CartierDiv Y) (g : Y → ℝ) : (Function.support fun z => (D.mult z : ℝ) * g z).Finite :=
  D.finite_support_mult.subset fun z hz => by
    simp only [Function.mem_support] at hz ⊢
    intro h
    simp [h] at hz

theorem recVal_cons_recip : ArchRecip → ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k), IsAmb q → ∀ e : ℕ, topologicalKrullDim Y = (e + 1 + 1 : ℕ) → ∀ T, IsMix q (e + 1) T → ∀ (M N : HermLB q) (L : Fin e → HermLB q) (s : M.B.Sec) (t : N.B.Sec) (hs : genericPoint Y ∈ nonzeroLocus s) (ht : genericPoint Y ∈ nonzeroLocus t), (∀ z : Y, Order.coheight z = 1 → z ∈ nonzeroLocus s ∨ z ∈ nonzeroLocus t) → recVal (T (e + 1) (Fin.cons N L)) (Fin.cons N L : Fin (e + 1) → HermLB q) M (isRatSec_ratOfSec s hs) = recVal (T (e + 1) (Fin.cons M L)) (Fin.cons M L : Fin (e + 1) → HermLB q) N (isRatSec_ratOfSec t ht) := by
  intro hAR k _ Y _ _ q hA e hdim T hT M N L s t hs ht hcov
  have : IsNoetherian Y := hA.isNoetherian
  have key (A B : HermLB q) (a : A.B.Sec) (b : B.B.Sec) (ha : genericPoint Y ∈ nonzeroLocus a)
      (hab : ∀ z : Y, Order.coheight z = 1 → z ∈ nonzeroLocus a ∨ z ∈ nonzeroLocus b) (z : Y) :
      ((divOfSec A.isLB a ha).mult z : ℝ) * T (e + 1) (Fin.cons B L) z =
        ((divOfSec A.isLB a ha).mult z : ℝ) * resCyc B.isLB b (T e L) z -
          ((divOfSec A.isLB a ha).mult z : ℝ) * resArch L B b z := by
    by_cases h0 : (divOfSec A.isLB a ha).mult z = 0
    · simp [h0]
    · have hz := CartierDiv.coheight_eq_one_of_mult_ne_zero h0
      have hza : z ∉ nonzeroLocus a := fun h =>
        (notMem_supp_divOfSec.2 h) (CartierDiv.mem_supp_of_mult_ne_zero h0)
      rw [mixRecVal_cons_eq_resCyc_sub_resArch hA hdim hT B L b hz ((hab z hz).resolve_left hza), mul_sub]
  have hL : recVal (T (e + 1) (Fin.cons N L)) (Fin.cons N L : Fin (e + 1) → HermLB q) M (isRatSec_ratOfSec s hs) =
      (∑ᶠ z, ((divOfSec M.isLB s hs).mult z : ℝ) * resCyc N.isLB t (T e L) z -
        ∑ᶠ z, ((divOfSec M.isLB s hs).mult z : ℝ) * resArch L N t z) -
        mixArch (Fin.cons N L : Fin (e + 1) → HermLB q) M (isRatSec_ratOfSec s hs) := by
    rw [recVal, finsum_congr (key M N s t hs hcov), finsum_sub_distrib (finite_support_mult_mul _ _)
      (finite_support_mult_mul _ _)]
  have hR : recVal (T (e + 1) (Fin.cons M L)) (Fin.cons M L : Fin (e + 1) → HermLB q) N (isRatSec_ratOfSec t ht) =
      (∑ᶠ z, ((divOfSec N.isLB t ht).mult z : ℝ) * resCyc M.isLB s (T e L) z -
        ∑ᶠ z, ((divOfSec N.isLB t ht).mult z : ℝ) * resArch L M s z) -
        mixArch (Fin.cons M L : Fin (e + 1) → HermLB q) N (isRatSec_ratOfSec t ht) := by
    rw [recVal, finsum_congr (key N M t s ht fun z hz => (hcov z hz).symm),
      finsum_sub_distrib (finite_support_mult_mul _ _) (finite_support_mult_mul _ _)]
  have hC := GlobalTheory.T.iteratedWeilDivisorSum_symm_no_common_divisor k Y q hA M.B N.B M.isLB N.isLB s t hs ht hcov (T e L)
  rw [hL, hR, hC]
  rcases GlobalTheory.T.projArithAmbient_vertical_or_arithmeticVariety k Y q hA (e + 1 + 1) hdim with ⟨l, _, _, hno⟩ | ⟨e', he', hav⟩
  · have z₀ := GlobalTheory.T.mixedArch_restricted_eq_zero_of_no_complexPoints k Y q hno
    rw [(z₀ (e + 1) (Fin.cons N L) M).1, (z₀ (e + 1) (Fin.cons M L) N).1]
    simp only [(z₀ e L N).2, (z₀ e L M).2, mul_zero, finsum_zero]
  · obtain rfl : e' = e + 1 := by omega
    have hA' := hAR k Y q e hav M N L s t hs ht hcov
    linarith

end GlobalTheory.MixHt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InductiveMixedHeightTensorAdditive
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt

theorem recVal_tens_cons : ArchInteg → ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k), IsAmb q → ∀ e : ℕ, topologicalKrullDim Y = (e + 1 + 1 : ℕ) → ∀ T, IsMix q (e + 1) T → ∀ (M : HermLB q) (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r) (A B : HermLB q) (L : Fin e → HermLB q), recVal (T (e + 1) (Fin.cons (A.tens B) L)) (Fin.cons (A.tens B) L : Fin (e + 1) → HermLB q) M hr = recVal (T (e + 1) (Fin.cons A L)) (Fin.cons A L : Fin (e + 1) → HermLB q) M hr + recVal (T (e + 1) (Fin.cons B L)) (Fin.cons B L : Fin (e + 1) → HermLB q) M hr := by
  intro hA k _ Y _ _ q hq e hdim T hT M r hr A B L
  have hN := hq.isNoetherian
  have hfin := (M.div hr).finite_support_mult
  have hm := (GlobalTheory.T.mixedArchIntegral_additive_and_diagonal hA k Y q hq M r hr).1 e hdim A B L
  have hsupp : ∀ (f : Y → ℝ), (Function.support fun z => ((M.div hr).mult z : ℝ) * f z).Finite := fun f =>
    hfin.subset fun z hz h => hz (by simp [h])
  unfold recVal
  rw [hm]
  have hsum : (∑ᶠ z, ((M.div hr).mult z : ℝ) * T (e + 1) (Fin.cons (A.tens B) L) z) =
      (∑ᶠ z, ((M.div hr).mult z : ℝ) * T (e + 1) (Fin.cons A L) z) +
        ∑ᶠ z, ((M.div hr).mult z : ℝ) * T (e + 1) (Fin.cons B L) z := by
    rw [← finsum_add_distrib (hsupp _) (hsupp _)]
    refine finsum_congr fun z => ?_
    by_cases h0 : (M.div hr).mult z = 0
    · simp [h0]
    · have hc := CartierDiv.coheight_eq_one_of_mult_ne_zero h0
      have hd := ((GlobalTheory.T.coheight_one_iff_pointClosure_dim_projArith k Y q hq (e + 1) hdim).1 z).1 hc
      rw [hT.add e A B L z le_rfl hd, mul_add]
  rw [hsum]
  ring

end GlobalTheory.MixHt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralEvalFormModRelationEqStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_evalForm_mod_relation_eq : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) (hX : IsRegVar p D) (E : X.Modules) (h : VMetric p E 2) (H : h.IsCInf) (fl : Vert.Flag E 2) (A : HermLB p) (σ : k →+* ℂ)
    (Z Z' : MvPolynomial (Fin 4) ℝ), (MvPolynomial.X 3 - MvPolynomial.X 1 * MvPolynomial.X 2 : MvPolynomial (Fin 4) ℝ) ∣ Z - Z' →
      (hX.atlas σ).integral (evalF (hX.atlas σ) (fam4 hX σ H fl A) Z) = (hX.atlas σ).integral (evalF (hX.atlas σ) (fam4 hX σ H fl A) Z') := by
  first | exact @GlobalTheory.FlagChernWeil.integral_evalForm_flag_family_eq | exact GlobalTheory.FlagChernWeil.integral_evalForm_flag_family_eq | (intros; apply GlobalTheory.FlagChernWeil.integral_evalForm_flag_family_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoOfProperIsIsoOnReductionsStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIso_of_proper_isIso_on_reductions : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), I ≤ Ideal.jacobson ⊥ → ∀ (T X : Scheme.{0}) (φ : T ⟶ X) (f : X ⟶ Spec (CommRingCat.of R)), IsProper φ → IsProper f → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (c : ∀ e, (Y e).left ⟶ T), (∀ e, IsPullback (c e) (Y e).hom (φ ≫ f) (thick R I e)) → (∀ e, IsPullback (c e ≫ φ) (Y e).hom f (thick R I e)) → IsIso φ := by
  first | exact @GlobalTheory.FormalAlg.isIso_of_isIso_reductions | exact GlobalTheory.FormalAlg.isIso_of_isIso_reductions | (intros; apply GlobalTheory.FormalAlg.isIso_of_isIso_reductions <;> assumption)
end

