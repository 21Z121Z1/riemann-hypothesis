import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3566
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3315
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3070
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3386
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3565
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3331
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3567
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2761
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3242
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupPullbackTripleProductMapLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2898
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3452
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3497
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3569
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3556
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3568
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyUWit
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneColengthEqLogDegreeStatement
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dieudonneColength_eq_log_degree : ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G H : PDivGroup p k) (q : G ⟶ H) (e : ℕ), IsIsog q → HasLogDeg q e → Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q)) = e := by
  first | exact @GlobalTheory.Dieu.length_quot_range_map_eq_of_hasLogDeg | exact GlobalTheory.Dieu.length_quot_range_map_eq_of_hasLogDeg | (intros; apply GlobalTheory.Dieu.length_quot_range_map_eq_of_hasLogDeg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndCharpolyTateDetDegreeTrace
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem linTrace_eq_neg_nextCoeff {F W : Type} [Field F] [AddCommGroup W] [Module F W]
    [FiniteDimensional F W] (g : Module.End F W) :
    LinearMap.trace F W g = -g.charpoly.nextCoeff := by
  classical
  let b := Module.finBasis F W
  rw [LinearMap.trace_eq_matrix_trace F b, Matrix.trace_eq_neg_charpoly_nextCoeff,
    LinearMap.charpoly_toMatrix]

theorem charpoly_map_vmap {K : Type} [Field K] (l : ℕ) [Fact l.Prime] (hl : (l : K) ≠ 0) (A : AbVar K)
    [Module.Finite ℚ_[l] (Vl l A)] (f : End A) :
    (charpoly f).map (algebraMap ℤ ℚ_[l]) = (vmap l (A := A) (B := A) f).charpoly := by
  obtain ⟨⟨hm, hd, hev⟩, -⟩ := GlobalTheory.T.abelianVarietyEndCharpoly_spec K A f
  have key := GlobalTheory.T.abelianVariety_degreePolynomial_map_eq_charpoly_rationalTate K l hl A f ((charpoly f).map (algebraMap ℤ ℚ)) (hm.map _)
    (by rw [Polynomial.natDegree_map_eq_of_injective (RingHom.injective_int (algebraMap ℤ ℚ)), hd])
    (fun n => by
      rw [Polynomial.eval_intCast_map, Int.cast_id, hev n]
      simp)
  rw [← key, Polynomial.map_map]
  congr 1

end GlobalTheory.AV.AbVar

namespace GlobalTheory.AV.AbVar

theorem charpoly_tate_det_trace : ∀ (K : Type) [Field K] (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 → ∀ (A : AbVar K) (f : End A), (∀ [Module.Finite ℚ_[l] (Vl l A)], (charpoly f).map (algebraMap ℤ ℚ_[l]) = (vmap l (A := A) (B := A) f).charpoly) ∧ (∀ [Module.Free ℤ_[l] (Tl l A)] [Module.Finite ℤ_[l] (Tl l A)], (charpoly f).map (algebraMap ℤ ℤ_[l]) = (tend l A f).charpoly) ∧ LinearMap.det (vmap l (A := A) (B := A) f) = (deg (A := A) (B := A) f : ℚ_[l]) ∧ LinearMap.trace ℚ_[l] _ (vmap l (A := A) (B := A) f) = (trace f : ℚ_[l]) := by
  intro K _ l _ hl A f
  refine ⟨fun {_} => charpoly_map_vmap l hl A f, fun {_ _} => ?_, ?_, ?_⟩
  · apply Polynomial.map_injective (algebraMap ℤ_[l] ℚ_[l]) (IsFractionRing.injective ℤ_[l] ℚ_[l])
    rw [Polynomial.map_map, ← LinearMap.charpoly_baseChange]
    have hc : (algebraMap ℤ_[l] ℚ_[l]).comp (algebraMap ℤ ℤ_[l]) = algebraMap ℤ ℚ_[l] := Subsingleton.elim _ _
    rw [hc]
    exact charpoly_map_vmap l hl A f
  · obtain ⟨-, -, -, hfin, hrk⟩ := tl_free_finrank K l hl A
    have hneg : vmap l (A := A) (B := A) f = (-1 : ℚ_[l]) • vmap l (A := A) (B := A) (-f) := by
      simp only [vmap, map_neg, LinearMap.baseChange_neg, neg_one_smul, neg_neg]
    have hev := (GlobalTheory.T.abelianVarietyEndCharpoly_spec K A (-f)).1.2.2 0
    rw [Int.cast_zero, zero_sub, neg_neg] at hev
    rw [hneg, LinearMap.det_smul, LinearMap.det_eq_sign_charpoly_coeff, ← charpoly_map_vmap l hl A (-f),
      Polynomial.coeff_map, Polynomial.coeff_zero_eq_eval_zero, hev, hrk, pow_mul, neg_one_sq, one_pow]
    simp
  · obtain ⟨-, -, -, hfin, -⟩ := tl_free_finrank K l hl A
    rw [linTrace_eq_neg_nextCoeff, ← charpoly_map_vmap l hl A f,
      Polynomial.nextCoeff_map (RingHom.injective_int (algebraMap ℤ ℚ_[l])), trace]
    simp

end GlobalTheory.AV.AbVar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdaptedQuasiLogBasisPDivGroupLieDualStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adapted_quasiLog_basis_pDivGroup_lieDual : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (E : Type) [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∃ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) E) (lb : Module.Basis (Fin k) O G.dual.Lie), IsBasis c.μ e ∧ IsAdapted (RingHom.id O) c.μ e ∧ (∀ i, cob1 (up E c.μ) (e (Sum.inl i)) = 0) ∧ ∀ j, c.IsLie (e (Sum.inr j)) (lb j) := by
  first | exact @GlobalTheory.QLogBasis.adapted_basis | exact GlobalTheory.QLogBasis.adapted_basis | (intros; apply GlobalTheory.QLogBasis.adapted_basis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApproximatingElementsNormalCoverUnitaryStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.USep
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_approximating_elements_normalCover_unitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), ∀ (φ : InvFun (𝓞 E)), IsPolFan H.bar (min Dw.p Dw.q) φ → ∀ (d : ℕ) (J : C.Z.IdealSheafData), (∀ x ∈ J.support, x ∉ Set.range C.i) → UValOn Xo c C.i φ J d → ∀ (S : Scheme.{0}) (π : S ⟶ pullback C.z (spMap C.b)), IsNormBl π (J.comap (pullback.fst C.z (spMap C.b))) → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Cm : GlobalTheory.UChart.MonoFam Xo c φ V), GlobalTheory.Mum.Base V → ∀ ξ : Sp V ⟶ S, Cm.y ≫ C.iF = jK V ≫ ξ ≫ π → ∀ (N₁ : ℕ) (M : Scheme.{0}) [IsIntegral M] (g : M ⟶ C.Z) (z₁ : M) (ζ : Sp (M.presheaf.stalk z₁) ⟶ pullback C.z (spMap C.b)) (Φ : VSys (H.bar : 𝓞 E → 𝓞 E) (min Dw.p Dw.q) !![(1 : ℤ)] N₁ (M.presheaf.stalk z₁)) (y : Φ.Y) (ρ : V →+* Φ.V y) (e : Φ.X y ≃ₗ[𝓞 E] Cm.P.D.toPre.X) (h : Fin (Φ.m y) ≃ Fin Cm.m) (U : M.Opens), (U : Set M).Nonempty → IsCov C g z₁ ζ → GlobalTheory.GSep.HasTraitsOn ζ Φ.pre U → IsMember ζ Φ Cm (ξ ≫ π) y ρ e h → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ p, (spMap ev ≫ ξ) p = ξ (closedPoint V)) → GlobalTheory.UChart.DefOver k₀ (spMap ev ≫ ξ) → ∀ ga : Fin (Φ.m y) → LinearMap.BilinForm ℤ (Φ.X y), (∀ k a b, ga k a b = Cm.δ (h k) (e a) (e b)) → ∃ ev₁ : Φ.V y →+* K, ev₁.comp ρ = ev ∧ GlobalTheory.Poinc.Sep.Elements Φ y φ (2 * d) ga ev₁ k₀ := by
  first | exact @GlobalTheory.USep.exists_elements_cover | exact GlobalTheory.USep.exists_elements_cover | (intros; apply GlobalTheory.USep.exists_elements_cover <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBalancedLatticeDataClosedPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_balanced_lattice_data_closedPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (M : RatModel X₁.o₁ X₁.Ω₁) (U₀ : M.Z.Opens) (EE : M.Lat X₁.S.J) (out : ZHOut X₁.ρ M U₀ EE), X₁.S.admitted M U₀ → X₁.S.IsEE M U₀ EE → ∀ x : M.Z, IsClosed ({x} : Set M.Z) → ∃ (X : Type) (_ : AddCommGroup X) (_ : Module (𝓞 E) X) (_ : Module.Finite (𝓞 E) X) (_ : Module.Projective (𝓞 E) X) (n : ℕ) (eb : X ≃ₗ[ℤ] (Fin n → ℤ)) (b₀ : LinearMap.BilinForm ℤ X) (μ : (Fin n → ZMod X₁.S.N) → X) (e : (Fin n → ZMod X₁.S.N) → X₁.Ω₁), Module.finrank (𝓞 E) X ≤ min Dw.p Dw.q ∧ b₀ ∈ balForms H.bar X ∧ (∀ y, y ≠ 0 → 0 < b₀ y y) ∧ (∀ cl i, ((eb (μ cl) i : ℤ) : ZMod X₁.S.N) = cl i) ∧ (∀ cl (α : X), (∀ i, ((eb α i : ℤ) : ZMod X₁.S.N) = cl i) → b₀ (μ cl) (μ cl) ≤ b₀ α α) ∧ (∀ cl, e cl ≠ 0 ∧ ∃ (T₀ : AddSubgroup X₁.S.Gam) (c' : T₀ →+ ZMod X₁.S.N) (κ : X₁.S.J × (T₀ → ZMod ((X₁.S.r * X₁.S.N) ^ 2))) (x₀ : X₁.S.Gam), X₁.S.IsoFree T₀ ∧ e cl = X₁.S.FF T₀ c' κ / X₁.S.th x₀) ∧ ∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ M.Z), (∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ ξ ∧ X₁.Lies (ξ₀ ≫ out.u₀) T.y) → ξ (IsLocalRing.closedPoint T.V) ⤳ x → ∃ π : X →ₗ[𝓞 E] T.P.D.toPre.X, Function.Surjective π ∧ (∀ cl (α : X), (∀ i, ((eb α i : ℤ) : ZMod X₁.S.N) = cl i) → T.be (π (μ cl)) (π (μ cl)) ≤ T.be (π α) (π α)) ∧ ∀ cl, UOrdEq M T ξ (e cl ^ (2 * X₁.S.N)) (T.be (π (μ cl)) (π (μ cl))).toNat := by
  first | exact @GlobalTheory.UPoinc.ClosedPt.exists_lattice_data | exact GlobalTheory.UPoinc.ClosedPt.exists_lattice_data | (intros; apply GlobalTheory.UPoinc.ClosedPt.exists_lattice_data <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCarriedFrameNearClosedFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem closed_spec {R : Type} [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] (hS : IsSemiAbelian G)
    (y : G.left) (hy : G.hom y = closedPoint R) :
    ∃ y₀ : G.left, y ⤳ y₀ ∧ IsClosed ({y₀} : Set G.left) ∧ G.hom y₀ = closedPoint R := by
  have : QuasiCompact G.hom := hS.quasiCompact
  have hc : CompactSpace G.left := by
    constructor
    have := QuasiCompact.isCompact_preimage (f := G.hom) Set.univ isOpen_univ isCompact_univ
    simpa using this
  obtain ⟨y₀, hy₀, hcl⟩ := (isClosed_closure (s := ({y} : Set G.left))).exists_closed_singleton ⟨y, subset_closure rfl⟩
  have hsp : y ⤳ y₀ := specializes_iff_mem_closure.2 hy₀
  refine ⟨y₀, hsp, hcl, ?_⟩
  have h1 : G.hom y ⤳ G.hom y₀ := hsp.map G.hom.continuous
  rw [hy] at h1
  have h2 := specializes_iff_mem_closure.1 h1
  exact (isClosed_singleton_closedPoint R).closure_subset h2

set_option maxHeartbeats 1000000 in

theorem FrameCarried.exists_near_closed_fibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hB : Base R) (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R') (hF : FinExt ρ) (hG : IsGal ρ) (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (hS' : IsSemiAbelian G') (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left) (hS : IsSemiAbelian G) (hβ : IsGrpPullback G' G (spMap ρ) β) (hact : ∀ σ, a.act σ ≫ β = β), ∀ y : G.left, G.hom y = closedPoint R → ∃ V : G.left.Opens, y ∈ V ∧ ∃ T : ∀ k : U'.LG.L.ι, Γ(G'.left, β ⁻¹ᵁ V ⊓ U'.LG.L.U k)ˣ, IsFrameOver U'.LG.L (β ⁻¹ᵁ V) T ∧ ∀ (σ : Gal ρ) (h : IsPullDeg (Gal.hom σ) D'.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'), bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) = a.act σ → ∀ hP : IsPullUnif (Gal.hom σ) h bc U' U', PullOver hD h → FrameCarried U'.LG.L (β ⁻¹ᵁ V) T _ (Classical.choose hP.lg) := by
  intro R _ _ _ hB R' _ _ _ ρ hF hG D D' hD A' G' _ _ hS' U' a G _ _ β hS hβ hact y hy
  obtain ⟨θ, hθ, O, hO, hnz⟩ := GlobalTheory.T.exists_carried_section_nonzero_near_closedFibre R hB R' ρ hF hG D D' hD A' G' hS' U' a G β hS hβ hact
  obtain ⟨y₀, hsp, hcl, hy₀c⟩ := closed_spec G hS y hy
  obtain ⟨V, hV, rest⟩ := GlobalTheory.T.exists_frame_near_closedFibre_point R hB R' ρ hF hG D D' hD A' G' hS' U' a G β hS hβ hact θ hθ O hO hnz y₀ hcl hy₀c
  exact ⟨V, hsp.mem_open V.isOpen hV, rest⟩

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCarriedSectionOffClosedFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

open CubeCarried

theorem exists_secOver_of_gen {X : Scheme.{0}} (L : LB X) (W : X.Opens) (g : W.toScheme ⟶ X) (hg : g = W.ι)
    (t : LB.Gen (L.pull g)) (ht : t.IsGen) :
    ∃ s : ∀ k, Γ(X, W ⊓ L.U k), IsSecOver L W s ∧
      (∀ (z : X) (k : L.ι), z ∈ W → z ∈ L.U k → IsUnit (gs (𝟙 X) z (W ⊓ L.U k) (s k))) ∧
      ∀ (f : X ⟶ X) (w : LB.Iso L (L.pull f)), W ≤ f ⁻¹ᵁ W →
        (∀ (Z : Scheme.{0}) (r r' : Z ⟶ W) (z : Z) (j k : L.ι), r' ≫ W.ι = (r ≫ W.ι) ≫ f →
          g (r' z) ∈ L.U j → g (r z) ∈ L.U k →
          gm r' z ((L.pull g).U (fun _ => j)) (t.s (fun _ => j)) =
            gw w (r ≫ g) z j k * gm r z ((L.pull g).U (fun _ => k)) (t.s (fun _ => k))) →
        SecCarriedOver L W s f w := by
  subst hg
  obtain ⟨s, hs⟩ := exists_sec_of_gen L W t
  have inj : ∀ z : W.toScheme, Function.Injective (W.ι.stalkMap z).hom := fun z =>
    (ConcreteCategory.bijective_of_isIso (W.ι.stalkMap z)).1
  have v : ∀ (z : W.toScheme) (k : L.ι), W.ι z ∈ L.U k →
      (W.ι.stalkMap z).hom (gs (𝟙 X) (W.ι z) (W ⊓ L.U k) (s k)) =
        (gm (𝟙 _) z ((L.pull W.ι).U (fun _ => k)) (t.s (fun _ => k))).val := fun z k hk => by
    rw [← gs_eq_map_gs W.ι z _ (show W.ι z ∈ W ⊓ L.U k from ⟨z.2, hk⟩), ← hs _ (𝟙 _) z k hk, Category.id_comp]
  refine ⟨s, fun z k k' hz hk hk' => ?_, fun z k hz hk => ?_, fun f w hf H z j k hz hfz hk hj => ?_⟩
  · obtain ⟨z, rfl⟩ : ∃ z' : W.toScheme, W.ι z' = z := ⟨⟨z, hz⟩, rfl⟩
    apply inj z
    rw [map_mul, v z k hk, v z k' hk', ← gm_val_map W.ι z (L.U k ⊓ L.U k') ⟨hk, hk'⟩, ← Units.val_mul]
    congr 1
    refine (gen_trans ht (𝟙 _) z (j := fun _ => k) (j' := fun _ => k') (mem_pull.2 hk) (mem_pull.2 hk')).trans ?_
    rw [trF, Fintype.prod_unique, zpow_one, Category.id_comp]
    rfl
  · obtain ⟨z, rfl⟩ : ∃ z' : W.toScheme, W.ι z' = z := ⟨⟨z, hz⟩, rfl⟩
    refine (isUnit_map_iff (W.ι.stalkMap z).hom _).1 ?_
    rw [v z k hk]
    exact Units.isUnit _
  · obtain ⟨z, rfl⟩ : ∃ z' : W.toScheme, W.ι z' = z := ⟨⟨z, hz⟩, rfl⟩
    apply inj z
    have hr : f.resLE W W hf ≫ W.ι = (𝟙 _ ≫ W.ι) ≫ f := by simp
    have hj' : W.ι (f.resLE W W hf z) ∈ L.U j := by
      rw [← Scheme.Hom.comp_apply, hr]; exact hj
    have e := congrArg Units.val (H _ (𝟙 _) (f.resLE W W hf) z j k hr hj' hk)
    rw [← hs _ _ z j hj', hr, Category.id_comp, Units.val_mul] at e
    rw [map_mul, v z k hk, ← CubeCarried.gs_comp W.ι f z (W ⊓ L.U j) ⟨hfz, hj⟩, e]
    exact congrArg₂ (· * ·) (gm_val_map W.ι z ((L.pull f).U (fun _ => j) ⊓ L.U k) ⟨mem_pull.2 hj, hk⟩ _) rfl

set_option maxHeartbeats 1000000 in

theorem exists_carried_sec_off_closed : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hB : Base R) (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R') (hF : FinExt ρ) (hG : IsGal ρ) (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (hS' : IsSemiAbelian G') (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left) (hS : IsSemiAbelian G) (hβ : IsGrpPullback G' G (spMap ρ) β) (hact : ∀ σ, a.act σ ≫ β = β), ∀ y : G.left, G.hom y ≠ closedPoint R → ∃ V : G.left.Opens, y ∈ V ∧ ∃ s : ∀ k : U'.LG.L.ι, Γ(G'.left, β ⁻¹ᵁ V ⊓ U'.LG.L.U k), IsSecOver U'.LG.L (β ⁻¹ᵁ V) s ∧ (∀ (z : G'.left) (k : U'.LG.L.ι), β z = y → z ∈ U'.LG.L.U k → IsUnit (gs (𝟙 G'.left) z (β ⁻¹ᵁ V ⊓ U'.LG.L.U k) (s k))) ∧ ∀ σ : Gal ρ, ∃ (h : IsPullDeg (Gal.hom σ) D'.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'), bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) = a.act σ ∧ ∃ hP : IsPullUnif (Gal.hom σ) h bc U' U', PullOver hD h ∧ SecCarriedOver U'.LG.L (β ⁻¹ᵁ V) s _ (Classical.choose hP.lg) := by
  intro R _ _ _ hB R' _ _ _ ρ hF hG D D' hD A' G' _ _ hS' U' a G _ _ β hS hβ hact y hy
  obtain ⟨θ, hθ, O, hO, hnz⟩ := GlobalTheory.T.exists_carried_section_nonzero_near_closedFibre R hB R' ρ hF hG D D' hD A' G' hS' U' a G β hS hβ hact
  have := hB.1.1
  have hfin : IsFinite (spMap ρ) := (IsFinite.SpecMap_iff _).2 hF.2.2
  have hβf : IsFinite β := MorphismProperty.of_isPullback (P := @IsFinite) hβ.1.flip hfin
  let O' : G.left.Opens := ⟨farSet β θ, isOpen_farSet β β.isClosedMap θ⟩
  have hO' : ∃ g ∈ O', G.hom g = closedPoint R := by
    obtain ⟨g, hg, hgc⟩ := hO
    refine ⟨g, fun g' hg' => ?_, hgc⟩
    subst hg'
    exact hnz g' hg hgc
  obtain ⟨p, q, c, h⟩ := OffClosed.exists_ten R hB.1.2.2.2 G hS O' hO' y hy
  let V : G.left.Opens := ⟨⋂ f ∈ {f | f ∈ cubeTen (𝟙 G) p q c}, ((f.left ⁻¹ᵁ O' : G.left.Opens) : Set G.left),
    (List.finite_toSet _).isOpen_biInter fun f _ => (f.left ⁻¹ᵁ O').isOpen⟩
  have hyV : y ∈ V := Set.mem_iInter₂.2 h
  refine ⟨V, hyV, ?_⟩
  obtain ⟨hl, hm⟩ := grpPullback_points_lift_mul_inv _ _ (spMap ρ) G G' β hβ G' G β hβ.1.w
  obtain ⟨a', ha⟩ := hl p
  obtain ⟨b', hb⟩ := hl q
  obtain ⟨c', hc⟩ := hl c
  have h1 : (𝟙 G' : G' ⟶ G').left ≫ β = β ≫ (𝟙 G : G ⟶ G).left := by simp
  have mul := fun u v u' v' hu hv => (hm u v u' v' hu hv).1
  have inv := fun u u' hu => (hm u u u' u' hu hu).2
  have hten : ∀ f' ∈ cubeTen (𝟙 G') a' b' c', ∃ f ∈ cubeTen (𝟙 G) p q c, f'.left ≫ β = β ≫ f.left := by
    intro f' hf
    simp only [cubeTen, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, by simp [cubeTen], mul _ _ _ _ h1 ha⟩
    · exact ⟨_, by simp [cubeTen], mul _ _ _ _ h1 (inv _ _ ha)⟩
    · exact ⟨_, by simp [cubeTen], ha⟩
    · exact ⟨_, by simp [cubeTen], inv _ _ ha⟩
    · exact ⟨_, by simp [cubeTen], mul _ _ _ _ h1 hb⟩
    · exact ⟨_, by simp [cubeTen], mul _ _ _ _ h1 hc⟩
    · exact ⟨_, by simp [cubeTen], mul _ _ _ _ h1 (inv _ _ (mul _ _ _ _ hb hc))⟩
    · exact ⟨_, by simp [cubeTen], hb⟩
    · exact ⟨_, by simp [cubeTen], hc⟩
    · exact ⟨_, by simp [cubeTen], inv _ _ (mul _ _ _ _ hb hc)⟩
  choose hd bc hbc hP hov using a.unif
  let F : Gal ρ → (G'.left ⟶ G'.left) := fun σ => (bc σ).hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ))
  have hFa : ∀ σ, F σ = a.act σ := hbc
  have hFc : ∀ σ, IsGrpPullback G' G' (spMap (Gal.hom σ)) (F σ) := fun σ => (hFa σ).symm ▸ a.cart σ
  have hFβ : ∀ σ, F σ ≫ β = β := fun σ => by rw [hFa, hact]
  let w : ∀ σ, LB.Iso U'.LG.L (U'.LG.L.pull (F σ)) := fun σ => Classical.choose (hP σ).lg
  have hw : ∀ σ, (w σ).IsGen := fun σ => (Classical.choose_spec (hP σ).lg).1
  have hrig : ∀ σ, PMaps (w σ) (K := PUnit) (fun _ => eSec G') (fun _ => eSec G') (fun _ => 1) U'.LG.rig U'.LG.rig
      (spMap (Gal.hom σ)) := fun σ => by
    obtain ⟨he, hr, -⟩ := (Classical.choose_spec (hP σ).lg).2
    exact (maps_iff (w σ) _ (fun _ => eSec G') _ U'.LG.rig U'.LG.rig (spMap (Gal.hom σ)) _
      (rigPull_le (F σ) (spMap (Gal.hom σ)) he U'.LG.L) (fun _ => rfl)).1 hr
  have comm : ∀ (u : G ⟶ G) (u' : G' ⟶ G'), u'.left ≫ β = β ≫ u.left → ∀ σ, u'.left ≫ F σ = F σ ≫ u'.left := by
    intro u u' hu σ
    have e₁ := hFβ σ
    have e₂ := (hFc σ).1.w
    generalize F σ = f at e₁ e₂ ⊢
    apply hβ.1.hom_ext
    · rw [Category.assoc, e₁, Category.assoc, hu, ← Category.assoc, e₁]
    · rw [Category.assoc, Category.assoc, Over.w, e₂, ← Category.assoc, Over.w]
  obtain ⟨t, ht, hcar⟩ := exists_gen_carried U'.cubG hFc w hrig
    (fun σ => pmaps_cub R' _ D' A' G' U'.toUnifPre (hFc σ) (w σ) (hw σ)) θ
    (fun σ => hθ σ (hd σ) (bc σ) (hbc σ) (hP σ) (hov σ)) G' F (fun σ => (hFc σ).1.w) (𝟙 G') a' b' c'
    (comm _ _ h1) (comm _ _ ha) (comm _ _ hb) (comm _ _ hc) (β ⁻¹ᵁ V) (by
      intro f' hf' g hg
      obtain ⟨f, hf, e⟩ := hten f' hf'
      have h2 : f.left (β g) ∈ farSet β θ := Set.mem_iInter₂.1 hg f hf
      refine h2 (f'.left g) ?_
      rw [← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply])
  obtain ⟨s, hs, hu, hcs⟩ := exists_secOver_of_gen U'.LG.L (β ⁻¹ᵁ V) _ (by simp) t ht
  refine ⟨s, hs, fun z k hz hk => hu z k (show β z ∈ V from hz ▸ hyV) hk, fun σ =>
    ⟨hd σ, bc σ, hbc σ, hP σ, hov σ, hcs (F σ) (w σ) (fun z hz => ?_) (hcar σ)⟩⟩
  show (F σ ≫ β) z ∈ V
  rw [hFβ]
  exact hz

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompatibleIsometriesCoisotropicKernels
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

namespace GlobalTheory.LowFilt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
  {X : Type} [AddCommGroup X] [Module (𝓞 E) X]

theorem nsmul_eq_nsmul_of_dvd {M : Type} [AddCommGroup M] {n m : ℕ} (h : n ∣ m) (e : M) : ∃ e', m • e = n • e' := by
  obtain ⟨k, rfl⟩ := h
  exact ⟨k • e, mul_smul n k e⟩

theorem Cois.comp_isometry {y : D.La →ₗ[𝓞 E] X} {n : ℕ} (hy : Cois D y n) (G : D.La ≃ₗ[𝓞 E] D.La)
    (hG : ∀ a b, D.EF (G a) (G b) = D.EF a b) : Cois D (y.comp G.toLinearMap) n := by
  refine ⟨fun x => ?_, fun a ha => ?_⟩
  · obtain ⟨a, e, he⟩ := hy.1 x
    exact ⟨G.symm a, e, by simpa using he⟩
  · have := hy.2 (G a) fun b hb => by
      have h1 := ha (G.symm b) (by simpa using hb)
      rwa [← hG a (G.symm b), G.apply_symm_apply] at h1
    exact this

theorem ker_iff_of_congr {f f' : D.La →ₗ[𝓞 E] X} {n : ℕ} (h : ∀ a, ∃ e, f' a = f a + n • e) (a : D.La) :
    (∃ e, f a = n • e) ↔ ∃ e, f' a = n • e := by
  obtain ⟨e₀, he₀⟩ := h a
  constructor
  · rintro ⟨e, he⟩
    exact ⟨e + e₀, by rw [he₀, he, smul_add]⟩
  · rintro ⟨e, he⟩
    exact ⟨e - e₀, by rw [smul_sub, ← he, he₀]; abel⟩

theorem KerIs.of_dvd {f : D.La →ₗ[𝓞 E] X} {Z : Submodule (𝓞 E) D.La} {n n' : ℕ} (hk : KerIs D f Z n')
    (hon : ∀ x, ∃ a e, f a = x + n' • e) (hd : n ∣ n') : KerIs D f Z n := by
  intro a
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨c, e', hc⟩ := hon x
    have h1 : ∃ e, f (a - n • c) = n' • e := ⟨-(n • e'), by
      rw [map_sub, map_nsmul, hx, hc, smul_add, smul_neg, smul_comm n' n e']; abel⟩
    obtain ⟨b, hb, e, he⟩ := (hk _).1 h1
    obtain ⟨e'', he''⟩ := nsmul_eq_nsmul_of_dvd hd e
    refine ⟨b, hb, c + e'', ?_⟩
    rw [sub_eq_iff_eq_add] at he
    rw [he, smul_add, ← he'']; abel
  · rintro ⟨b, hb, e, rfl⟩
    obtain ⟨e', he'⟩ := (hk b).2 ⟨b, hb, 0, by simp⟩
    obtain ⟨e'', he''⟩ := nsmul_eq_nsmul_of_dvd hd e'
    exact ⟨e'' + f e, by rw [map_add, map_nsmul, he', he'', smul_add]⟩

theorem exists_step [Module.Free ℤ X] [Module.Finite ℤ X] {Z FinalForm : Submodule (𝓞 E) D.La} (hop : IsOpp D Z FinalForm)
    (hrk : Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) X) (f : D.La →ₗ[𝓞 E] X) {n N' : ℕ} (hn : 0 < n)
    (hd : N' ∣ n) (hc : Cois D f n) (hk : KerIs D f Z N') :
    ∃ h : D.La ≃ₗ[𝓞 E] D.La, (∀ a b, D.EF (h a) (h b) = D.EF a b) ∧ (∀ a, ∃ e, h a = a + N' • e) ∧
      KerIs D (f.comp h.toLinearMap) Z n := by
  obtain ⟨Z'', hop'', hon⟩ := GlobalTheory.T.exists_opposite_transversal_isotropic D f n hn hc Z FinalForm hop hrk
  obtain ⟨h, hi, hN, hk'⟩ := GlobalTheory.T.exists_isometry_kernel_coisotropic_mod D f n N' hn hd hc Z Z'' hop'' hrk hk hon
  exact ⟨h, hi, hN, hk'⟩

def levelSeq (N j : ℕ) : ℕ := N * (j + 1).factorial

theorem levelSeq_pos {N : ℕ} (hN : 0 < N) (j : ℕ) : 0 < levelSeq N j := Nat.mul_pos hN (Nat.factorial_pos _)

theorem levelSeq_succ (N j : ℕ) : levelSeq N (j + 1) = levelSeq N j * (j + 2) := by
  unfold levelSeq; rw [Nat.factorial_succ (j + 1)]; ring

theorem levelSeq_dvd (N : ℕ) {i j : ℕ} (h : i ≤ j) : levelSeq N i ∣ levelSeq N j :=
  Nat.mul_dvd_mul_left N (Nat.factorial_dvd_factorial (by omega))

theorem dvd_levelSeq (N : ℕ) {n : ℕ} (hn : 0 < n) : n ∣ levelSeq N n :=
  Dvd.dvd.mul_left (Nat.dvd_factorial hn (Nat.le_succ n)) N

theorem levelSeq_zero (N : ℕ) : levelSeq N 0 = N := by simp [levelSeq]

def GoodAt (D : Datum H) (y : D.La →ₗ[𝓞 E] X) (Z : Submodule (𝓞 E) D.La) (N n : ℕ) (G : D.La ≃ₗ[𝓞 E] D.La) : Prop :=
  (∀ a b, D.EF (G a) (G b) = D.EF a b) ∧ (∀ a, ∃ e, G a = a + N • e) ∧ KerIs D (y.comp G.toLinearMap) Z n

def iterSeq {α : Type} (x₀ : α) (f : ℕ → α → α) (j : ℕ) : α := Nat.rec (motive := fun _ => α) x₀ f j

theorem exists_compatible_isometries : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (y : ℕ → D.La →ₗ[𝓞 E] X), (∀ n, 0 < n → Cois D (y n) n) →
    (∀ n m, 0 < n → 0 < m → ∀ a, ∃ e, y (n * m) a = y n a + n • e) →
    Module.finrank (𝓞 E) X ≤ min D.p D.q → ∀ N, 0 < N →
    ∃ Z : Submodule (𝓞 E) D.La, IsIsoSat D Z ∧ Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) X ∧
      ∃ g : ℕ → D.La ≃ₗ[𝓞 E] D.La, (∀ n a b, D.EF (g n a) (g n b) = D.EF a b) ∧
        (∀ n m, 0 < n → 0 < m → ∀ a, ∃ e, g (n * m) a = g n a + n • e) ∧ (∀ n a, ∃ e, g n a = a + N • e) ∧
        ∀ n, 0 < n → ∀ a, (∃ e, y n (g n a) = n • e) ↔ ∃ b ∈ perp D Z, ∃ e, a = b + n • e := by
  intro E _ _ _ H D X _ _ _ _ y hc hy hr N hN
  classical
  obtain ⟨Z₀, hZ₀, hrk₀⟩ := GlobalTheory.T.exists_isotropicSaturatedSubmodule_of_finrank_le D _ hr
  obtain ⟨Z₀', hop₀⟩ := GlobalTheory.T.exists_oppositeIsotropicPair D Z₀ hZ₀
  obtain ⟨Z₁', hop₁, hon₁⟩ := GlobalTheory.T.exists_opposite_transversal_isotropic D (y N) N hN (hc N hN) Z₀ Z₀' hop₀ hrk₀
  obtain ⟨g₀, hg₀, -, hk₀⟩ := GlobalTheory.T.exists_isometry_kernel_coisotropic_mod D (y N) N 1 hN (one_dvd N) (hc N hN) Z₀ Z₁' hop₁ hrk₀
    (fun a => ⟨fun _ => ⟨0, zero_mem _, a, by simp⟩, fun _ => ⟨y N a, by simp⟩⟩) hon₁
  set Z := Z₀.map (g₀ : D.La →ₗ[𝓞 E] D.La) with hZdef
  have memZ : ∀ x, x ∈ Z ↔ g₀.symm x ∈ Z₀ := fun x => Submodule.mem_map_equiv Z₀
  have memP : ∀ x, x ∈ perp D Z ↔ g₀.symm x ∈ perp D Z₀ := by
    intro x
    rw [mem_perp, mem_perp]
    constructor
    · intro hx z hz
      have := hx (g₀ z) ((memZ _).2 (by simpa using hz))
      rwa [← hg₀ (g₀.symm x) z, g₀.apply_symm_apply]
    · intro hx z hz
      have := hx _ ((memZ z).1 hz)
      rwa [← hg₀ (g₀.symm x) (g₀.symm z), g₀.apply_symm_apply, g₀.apply_symm_apply] at this
  have hZ : IsIsoSat D Z := by
    refine ⟨fun z hz => (memP z).2 (hZ₀.1 ((memZ z).1 hz)), fun n x hn hx => (memZ x).2 ?_⟩
    have := (memZ _).1 hx
    rw [map_nsmul] at this
    exact hZ₀.2 n _ hn this
  have hrk : Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) X := by
    rw [← hrk₀]; exact (g₀.submoduleMap Z₀).finrank_eq.symm
  obtain ⟨FinalForm, hop⟩ := GlobalTheory.T.exists_oppositeIsotropicPair D Z hZ
  have hbase : KerIs D (y N) Z N := by
    intro a
    have h1 := hk₀ (g₀.symm a)
    rw [g₀.apply_symm_apply] at h1
    rw [h1]
    constructor
    · rintro ⟨b, hb, e, he⟩
      refine ⟨g₀ b, (memP _).2 (by rwa [g₀.symm_apply_apply]), g₀ e, ?_⟩
      conv_lhs => rw [← g₀.apply_symm_apply a, he]
      rw [map_add, map_nsmul]
    · rintro ⟨b, hb, e, rfl⟩
      exact ⟨g₀.symm b, (memP b).1 hb, g₀.symm e, by rw [map_add, map_nsmul]⟩
  have hstep : ∀ j (G : D.La ≃ₗ[𝓞 E] D.La), GoodAt D (y (levelSeq N j)) Z N (levelSeq N j) G →
      ∃ G' : D.La ≃ₗ[𝓞 E] D.La, GoodAt D (y (levelSeq N (j + 1))) Z N (levelSeq N (j + 1)) G' ∧
        ∀ a, ∃ e, G' a = G a + levelSeq N j • e := by
    rintro j G ⟨hGi, hGN, hGk⟩
    have hcong : ∀ a, ∃ e, ((y (levelSeq N (j + 1))).comp G.toLinearMap) a =
        ((y (levelSeq N j)).comp G.toLinearMap) a + levelSeq N j • e := by
      intro a
      rw [levelSeq_succ]
      exact hy (levelSeq N j) (j + 2) (levelSeq_pos hN j) (by omega) (G a)
    have hk : KerIs D ((y (levelSeq N (j + 1))).comp G.toLinearMap) Z (levelSeq N j) := fun a =>
      (ker_iff_of_congr hcong a).symm.trans (hGk a)
    obtain ⟨h, hi, hN', hk'⟩ := exists_step hop hrk ((y (levelSeq N (j + 1))).comp G.toLinearMap)
      (levelSeq_pos hN (j + 1)) (levelSeq_dvd N (Nat.le_succ j)) ((hc _ (levelSeq_pos hN _)).comp_isometry G hGi) hk
    refine ⟨h.trans G, ⟨fun a b => ?_, fun a => ?_, fun a => hk' a⟩, fun a => ?_⟩
    · simp only [LinearEquiv.trans_apply]; rw [hGi, hi]
    · obtain ⟨e, he⟩ := hN' a
      obtain ⟨e₁, he₁⟩ := hGN a
      obtain ⟨e₂, he₂⟩ := nsmul_eq_nsmul_of_dvd (Dvd.intro _ rfl : N ∣ levelSeq N j) (G e)
      exact ⟨e₁ + e₂, by rw [LinearEquiv.trans_apply, he, map_add, map_nsmul, he₁, he₂, smul_add, add_assoc]⟩
    · obtain ⟨e, he⟩ := hN' a
      exact ⟨G e, by rw [LinearEquiv.trans_apply, he, map_add, map_nsmul]⟩
  choose! F hF hFc using hstep
  obtain ⟨S, hS0, hSs⟩ : ∃ S : ℕ → D.La ≃ₗ[𝓞 E] D.La, S 0 = LinearEquiv.refl _ _ ∧ ∀ j, S (j + 1) = F j (S j) :=
    ⟨iterSeq (LinearEquiv.refl _ _) F, rfl, fun _ => rfl⟩
  have hgood : ∀ j, GoodAt D (y (levelSeq N j)) Z N (levelSeq N j) (S j) := by
    intro j
    induction j with
    | zero =>
      rw [hS0, levelSeq_zero]
      exact ⟨fun _ _ => rfl, fun a => ⟨0, by simp⟩, fun a => hbase a⟩
    | succ j ih => rw [hSs]; exact hF j (S j) ih
  have hc1 : ∀ j a, ∃ e, S (j + 1) a = S j a + levelSeq N j • e := fun j a => by
    rw [hSs]; exact hFc j (S j) (hgood j) a
  have hck : ∀ i k a, ∃ e, S (i + k) a = S i a + levelSeq N i • e := by
    intro i k
    induction k with
    | zero => intro a; exact ⟨0, by simp⟩
    | succ k ih =>
      intro a
      obtain ⟨e, he⟩ := ih a
      obtain ⟨e₁, he₁⟩ := hc1 (i + k) a
      obtain ⟨e₂, he₂⟩ := nsmul_eq_nsmul_of_dvd (levelSeq_dvd N (Nat.le_add_right i k)) e₁
      exact ⟨e + e₂, by rw [← Nat.add_assoc, he₁, he, he₂, smul_add, add_assoc]⟩
  refine ⟨Z, hZ, hrk, S, fun n => (hgood n).1, fun n m hn hm a => ?_, fun n => (hgood n).2.1, fun n hn a => ?_⟩
  · have hle : n ≤ n * m := Nat.le_mul_of_pos_right n hm
    rw [← Nat.add_sub_of_le hle]
    obtain ⟨e, he⟩ := hck n (n * m - n) a
    obtain ⟨e', he'⟩ := nsmul_eq_nsmul_of_dvd (dvd_levelSeq N hn) e
    exact ⟨e', by rw [he, he']⟩
  · have hg := hgood n
    have hon := ((hc _ (levelSeq_pos hN n)).comp_isometry (S n) hg.1).1
    have hkn := hg.2.2.of_dvd hon (dvd_levelSeq N hn)
    obtain ⟨k, hk⟩ := dvd_levelSeq N hn
    have hkpos : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · rw [h0, mul_zero] at hk; exact absurd hk (levelSeq_pos hN n).ne'
      · exact h0
    have hcong : ∀ a, ∃ e, ((y (levelSeq N n)).comp (S n).toLinearMap) a =
        ((y n).comp (S n).toLinearMap) a + n • e := by
      intro a
      rw [hk]
      exact hy n k hn hkpos (S n a)
    exact (ker_iff_of_congr hcong a).trans (hkn a)

end GlobalTheory.LowFilt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLabelsUnitaryClassicalTraitStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_labels_unitaryClassicalTrait : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf), ∀ (X : USetup C) (wi : UWit X) (p : ℕ) [Fact p.Prime] (z : X.M.Z) (ct : UCTrait X p z), ∃ yy : X.S.Gam →+ ModN (X.S.r * X.S.N) ct.T.P.D.toPre.X, UIsLabW X wi ct yy := by
  first | exact @GlobalTheory.UPoinc.exists_uIsLabW | exact GlobalTheory.UPoinc.exists_uIsLabW | (intros; apply GlobalTheory.UPoinc.exists_uIsLabW <;> assumption)
end

