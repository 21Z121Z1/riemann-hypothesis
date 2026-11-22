import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0056
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0078
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2877
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2494
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3452
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3433
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3451
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3315
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3070
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3377
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CohomologyLogDerivativeAdjointEndomorphisms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3426
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3418
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3469
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTaylorExpansionOrderOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkDerField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3453
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0393
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3466
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2461
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2332
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2336
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.IsQProjOverOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2202
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3443
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2514
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0618
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3025
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2875
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3468
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2979
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3402
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0026
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEffCartierCompl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2263
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedPointNotMemAbelianLocusTautologicalBoundar
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ChartNotAb

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem subsingleton_of_closed_mem_abLocus {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {t : SAB H (Sp R)}
    (P : PELUnif (maximalIdeal R) t) (hc : (closedPoint R : Sp R) ∈ abLocus t.G) : Subsingleton P.D.toPre.X := by
  have hmax : (maximalIdeal R ^ (0 + 1)).IsMaximal := by
    rw [zero_add, pow_one]; infer_instance
  have hF : IsField (R ⧸ maximalIdeal R ^ (0 + 1)) := (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 hmax
  have hle : maximalIdeal R ^ (0 + 1) ≤ (closedPoint R).asIdeal := by
    rw [zero_add, pow_one]; exact le_rfl
  obtain ⟨q, hq⟩ : closedPoint R ∈ Set.range (PrimeSpectrum.comap
      (Ideal.Quotient.mk (maximalIdeal R ^ (0 + 1)))) := by
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
    exact hle
  let g := P.U.gt 0
  have m : Mono g.i := ⟨fun a b h => g.isKernel.hom_ext h (toUnit_unique _ _)⟩
  have hq' : thick R (maximalIdeal R) 0 q ∈ abLocus t.G := by
    rw [← hq] at hc; exact hc
  exact ArcNotAbelian.subsingleton_of_mem_abLocus t.G t.semi _ hF _ q hq' P.D.toPre.X g.i g.i_hom

end GlobalTheory.ChartNotAb

open GlobalTheory.ChartNotAb in

theorem GlobalTheory.UChart.closedPoint_not_mem_abLocus_of_isTaut : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)) (k : Type) [Field k] (m e : ℕ) (C : MonoFam Xo c φ (ChartRing k m e)), IsTaut C → 1 ≤ C.m → closedPoint (ChartRing k m e) ∉ abLocus C.t.G := by
  intro E _ _ _ H Dw l Xo c φ k _ m e C hT hm hc
  obtain ⟨-, -, -, -, -, ⟨N, s, ε, τ₀, -, hε, -, -⟩, -⟩ := hT
  have hs := subsingleton_of_closed_mem_abLocus C.P hc
  let i : Fin C.m := ⟨0, hm⟩
  apply ε.ne_zero (Sum.inl i)
  apply Subtype.ext
  rw [Submodule.coe_zero, hε i]
  ext x y
  rw [Subsingleton.elim x 0]
  simp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologousNegTorsorCocycleOfOrthogonal
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.PtExt.cohom_fv_neg_tanCoc_of_orthogonal : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (g : ℕ), IsAbelianScheme A → IsAbelianScheme B → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom → ∀ P : LB (A ⊗ B).left, P.IsLB → ∀ φ : HdR A →ₗ[R] HdR B →ₗ[R] R, AbDual.IsCorrForm (dp0 R) (𝟙 _) A B P φ → (∀ x ∈ Fil A, ∀ y ∈ Fil B, φ x y = 0) → ∀ (h' : HdR B) (v : epsR R ⟶ B), IsLieImage h' v → ∀ c : primDR A, (∀ h ∈ Fil A, φ h h' = h c) → ∀ f : Z1 (O (dp0 R) (A.hom ≫ 𝟙 _)), CatCoh.H1.mk _ f = c.1 → ∀ (j : ∀ (D : Type) [CommRing D] [Algebra R D], Pt A D → P.ι), IsChoice P j → Cohom (chartsA P) (fv f) (tanCoc P j v).neg := by
  intro H2' R _ A B _ _ g hA hB sA sB P hL φ hφ hO h' v hv c hc f hf j hj
  have hT : IsTangent v := hv.1
  obtain ⟨w, hw, hw0, hκ⟩ := GlobalTheory.T.exists_chernRepresentative_contraction_of_orthogonal H2' R A B g hA hB sA sB P hL φ hφ hO h' v hv c hc f hf
  obtain ⟨κ, hκc⟩ := (GlobalTheory.PtExt.ContrMor.exists_contr R A B v hT).2 w.1
  obtain ⟨k1, h1⟩ := hκ κ hκc
  obtain ⟨u, hu, k2, h2⟩ := GlobalTheory.T.chernClass_contraction_tangent_eq_torsorCocycle R A B P hL v hT j hj w hw hw0 κ hκc
  obtain ⟨k3, h3⟩ := GlobalTheory.T.eps_part_cocycle_coboundary_of_hodgeDeRham H2' R A B g hA hB sA sB P hL v hT u hu
  refine ⟨fun D _ _ x ↦ k1 D x - k2 D x - k3 D x, fun D _ _ D' _ _ ψ x hx ↦ ?_⟩
  have e1 := h1 D D' ψ x (sm_whole x)
  have e2 := h2 D D' ψ x hx
  have e3 := h3 D D' ψ x hx
  simp only [Fn1.add, Fn1.neg, Fn1.zero, map_sub] at e1 e2 e3 ⊢
  linear_combination e1 - e2 - e3
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColengthRangeMapGeStatement
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_quot_range_le_length_quot_range_map : ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G H : PDivGroup p k) (q : G ⟶ H), (Module.finrank k (G.omega ⧸ LinearMap.range (omegaMap G H q)) : ℕ∞) ≤ Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q)) ∧ (Module.finrank k (G.dual.Lie ⧸ LinearMap.range (lieMap H.dual G.dual (dualHom G H q))) : ℕ∞) ≤ Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q)) := by
  first | exact @GlobalTheory.Dieu.colength_range_map_ge | exact GlobalTheory.Dieu.colength_range_map_ge | (intros; apply GlobalTheory.Dieu.colength_range_map_ge <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectionClosedFibreOfPulledBackIso
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

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PotIso

open GlobalTheory.KS GlobalTheory.KS.AdjDlog

theorem constFn_mul_c {R : Type} [CommRing R] {Y : Scheme.{0}} (q : Y ⟶ Sp R) (W : Y.Opens) (a b : R) :
    constFn q W (a * b) = constFn q W a * constFn q W b := by
  simp only [constFn, map_mul]

theorem constFn_one_c {R : Type} [CommRing R] {Y : Scheme.{0}} (q : Y ⟶ Sp R) (W : Y.Opens) :
    constFn q W 1 = 1 := by
  simp only [constFn, map_one]

theorem constFn_zero_c {R : Type} [CommRing R] {Y : Scheme.{0}} (q : Y ⟶ Sp R) (W : Y.Opens) :
    constFn q W 0 = 0 := by
  simp only [constFn, map_zero]

theorem constFn_comp_spMap_c {R S : Type} [CommRing R] [CommRing S] {Y : Scheme.{0}} (q : Y ⟶ Sp S) (x : R →+* S)
    (W : Y.Opens) (t : R) : constFn (q ≫ spMap x) W t = constFn q W (x t) := by
  have e1 : (q ≫ spMap x).appLE ⊤ W le_top = (spMap x).appLE ⊤ ⊤ le_top ≫ q.appLE ⊤ W le_top :=
    (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  have h2 := congrArg (fun k => k.hom t) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom x))
  change ((q ≫ spMap x).appLE ⊤ W le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom t) =
    (q.appLE ⊤ W le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (x t))
  rw [e1, CommRingCat.comp_apply]
  congr 1
  simp only [CommRingCat.comp_apply] at h2
  exact h2.symm

theorem pull_g_val {X Y : Scheme.{0}} (L : LB X) (f : Y ⟶ X) (j j' : PUnit → L.ι) {O : Y.Opens}
    (h : O ≤ (L.pull f).U j ⊓ (L.pull f).U j') :
    (res h ((L.pull f).g j j')).val = pbT f (L.g (j PUnit.unit) (j' PUnit.unit)).val O := by
  have le : O ≤ f ⁻¹ᵁ (L.U (j PUnit.unit) ⊓ L.U (j' PUnit.unit)) :=
    le_inf ((h.trans inf_le_left).trans (LB.wchart_le L _ j PUnit.unit))
      ((h.trans inf_le_right).trans (LB.wchart_le L _ j' PUnit.unit))
  have e : res h ((L.pull f).g j j') = res le (pullU f _ (L.g (j PUnit.unit) (j' PUnit.unit))) := by
    show res h (∏ k : PUnit, _) = _
    erw [Fintype.prod_unique, zpow_one, res_res']
    rfl
  rw [e, val_res_pullU]

theorem isPullback_pr {k R : Type} [Field k] [CommRing R] (ρ : R →+* DualNumber k) {A B' A₀ : Scheme.{0}}
    (pA : A ⟶ Sp R) (pB : B' ⟶ Sp (DualNumber k)) (p₀ : A₀ ⟶ Sp k) (π₂ : B' ⟶ A) (m₀ : A₀ ⟶ A) (pr : B' ⟶ A₀)
    (h₂ : IsPullback π₂ pB pA (spMap (constHom ρ)))
    (hm : IsPullback m₀ p₀ pA (spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ)))
    (hpr : pr ≫ m₀ = π₂) (hprb : pr ≫ p₀ = pB ≫ spMap (algebraMap k (DualNumber k))) :
    IsPullback pr pB p₀ (spMap (algebraMap k (DualNumber k))) := by
  refine IsPullback.of_right ?_ hprb hm
  have e : spMap (constHom ρ) = spMap (algebraMap k (DualNumber k)) ≫
      spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ) := by
    rw [← Spec.map_comp]; rfl
  rw [hpr, ← e]; exact h₂

theorem conn_of_iso : ∀ (k : Type) [Field k] (R : Type) [CommRing R] (P : PolAV (Sp R)) (ρ : R →+* DualNumber k) (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ P.A.left), IsGrpPullback B' P.A (spMap ρ) π₁ → IsGrpPullback B' P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → ∀ (A₀ : Over (Sp k)) [GrpObj A₀] (m₀ : A₀.left ⟶ P.A.left), IsGrpPullback A₀ P.A (spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ)) m₀ → ∀ pr : B'.left ⟶ A₀.left, pr ≫ m₀ = π₂ → pr ≫ A₀.hom = B'.hom ≫ spMap (algebraMap k (DualNumber k)) → ∀ {J : Type} (V : J → P.A.left.Opens) (jj : J → P.L.ι), ⨆ i, V i = ⊤ → (∀ i, V i ≤ P.L.U (jj i)) → ∀ d : ∀ W : P.A.left.Opens, Γ(P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W), GlobalTheory.KS.LocDerK A₀.hom P.A.hom m₀ (fun r => (ρ r).snd) ⊤ d → (∀ (W : P.A.left.Opens) (f : Γ(P.A.left, W)), pbT π₁ f (π₂ ⁻¹ᵁ W) = pbT π₂ f (π₂ ⁻¹ᵁ W) + constFn B'.hom (π₂ ⁻¹ᵁ W) DualNumber.eps * pbT pr (d W f) (π₂ ⁻¹ᵁ W)) → ∀ w : LB.Iso (P.L.pull π₁) (P.L.pull π₂), w.IsGen → ∃ q : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i), GlobalTheory.HeatConn.IsConnK P.A P.L A₀ m₀ (fun r => (ρ r).snd) V jj d q := by
  intro k _ R _ P ρ B' _ π₁ π₂ h₁ h₂ hfib A₀ _ m₀ hm₀ pr hpr hprb J V jj hV hVU d hd hdB w hw
  obtain ⟨a, b, hab⟩ := GlobalTheory.T.two_pullback_isomorphism_unit_constant_plus_eps_function k R P ρ B' π₁ π₂ h₁ h₂ hfib A₀ m₀ hm₀ pr hpr hprb V jj hV hVU w hw
  have hpre : ∀ W : P.A.left.Opens, π₁ ⁻¹ᵁ W = π₂ ⁻¹ᵁ W := GlobalTheory.T.preimage_eq_of_agree_on_closedFibre_dualNumbers k P.A.left B'.left B'.hom π₁ π₂ hfib
  have hpb : IsPullback pr B'.hom A₀.hom (spMap (algebraMap k (DualNumber k))) :=
    GlobalTheory.PotIso.isPullback_pr ρ _ _ _ π₂ m₀ pr h₂.1 hm₀.1 hpr hprb
  have thick := GlobalTheory.T.existsUnique_add_eps_mul_on_dualNumber_thickening k A₀.left B'.left A₀.hom B'.hom pr hpb
  subst hpr
  refine ⟨fun i => constFn A₀.hom (m₀ ⁻¹ᵁ V i) ((a⁻¹ : kˣ) : k) * b i, hd, hV, hVU, fun i i' => ?_⟩
  have hW : V i ⊓ V i' ≤ P.L.U (jj i) ⊓ P.L.U (jj i') := inf_le_inf (hVU i) (hVU i')
  have hO₀ : m₀ ⁻¹ᵁ (V i ⊓ V i') ≤ m₀ ⁻¹ᵁ (P.L.U (jj i) ⊓ P.L.U (jj i')) := m₀.preimage_mono hW
  have hO : (pr ≫ m₀) ⁻¹ᵁ (V i ⊓ V i') ≤ pr ⁻¹ᵁ (m₀ ⁻¹ᵁ (V i ⊓ V i')) := le_rfl
  have hchart : ∀ l, (pr ≫ m₀) ⁻¹ᵁ V l ≤ (LB.div (P.L.pull (pr ≫ m₀)) (P.L.pull π₁)).U (fun _ => jj l, fun _ => jj l) := by
    intro l x hx
    refine ⟨Set.mem_iInter.2 fun _ => hVU l hx, Set.mem_iInter.2 fun _ => ?_⟩
    have : x ∈ π₁ ⁻¹ᵁ P.L.U (jj l) := by rw [hpre]; exact hVU l hx
    exact this
  have hM : (pr ≫ m₀) ⁻¹ᵁ (V i ⊓ V i') ≤ (P.L.pull (pr ≫ m₀)).U (fun _ => jj i) ⊓ (P.L.pull (pr ≫ m₀)).U (fun _ => jj i') :=
    fun x hx => ⟨(hchart i hx.1).1, (hchart i' hx.2).1⟩
  have hL : (pr ≫ m₀) ⁻¹ᵁ (V i ⊓ V i') ≤ (P.L.pull π₁).U (fun _ => jj i) ⊓ (P.L.pull π₁).U (fun _ => jj i') :=
    fun x hx => ⟨(hchart i hx.1).2, (hchart i' hx.2).2⟩
  have iso := iso_rel w hw (fun _ => jj i) (fun _ => jj i') (fun _ => jj i) (fun _ => jj i') hM hL
  rw [GlobalTheory.PotIso.pull_g_val, GlobalTheory.PotIso.pull_g_val] at iso
  have hs : ∀ l, V i ⊓ V i' ≤ V l → rsT (w.s (fun _ => jj l, fun _ => jj l)).val ((pr ≫ m₀) ⁻¹ᵁ (V i ⊓ V i')) =
      constFn B'.hom ((pr ≫ m₀) ⁻¹ᵁ (V i ⊓ V i')) (algebraMap k (DualNumber k) (a : k)) +
        constFn B'.hom ((pr ≫ m₀) ⁻¹ᵁ (V i ⊓ V i')) DualNumber.eps *
          pbT pr (rsT (b l) (m₀ ⁻¹ᵁ (V i ⊓ V i'))) ((pr ≫ m₀) ⁻¹ᵁ (V i ⊓ V i')) := by
    intro l hl
    have hl' : (pr ≫ m₀) ⁻¹ᵁ (V i ⊓ V i') ≤ (pr ≫ m₀) ⁻¹ᵁ V l := (pr ≫ m₀).preimage_mono hl
    rw [← rsT_rsT (hchart l) hl', hab l, rsT_add, rsT_mul, GlobalTheory.KS.rsT_constFn _ hl', GlobalTheory.KS.rsT_constFn _ hl',
      rsT_pbT pr (show (pr ≫ m₀) ⁻¹ᵁ V l ≤ pr ⁻¹ᵁ (m₀ ⁻¹ᵁ V l) from le_rfl) hl', pbT_rsT pr (m₀.preimage_mono hl) hO]
  have hA : constFn B'.hom ((pr ≫ m₀) ⁻¹ᵁ (V i ⊓ V i')) (algebraMap k (DualNumber k) (a : k)) =
      pbT pr (constFn A₀.hom (m₀ ⁻¹ᵁ (V i ⊓ V i')) (a : k)) ((pr ≫ m₀) ⁻¹ᵁ (V i ⊓ V i')) := by
    rw [GlobalTheory.KS.pbT_constFn A₀.hom pr hO, hprb, GlobalTheory.PotIso.constFn_comp_spMap_c]
  have hd' := hdB (V i ⊓ V i') (rsT (P.L.g (jj i) (jj i')).val (V i ⊓ V i'))
  rw [pbT_rsT π₁ hW (hpre _).ge, pbT_rsT (pr ≫ m₀) hW le_rfl, ← pbT_pbT pr m₀ hO₀ hO] at hd'
  rw [← pbT_pbT pr m₀ hO₀ hO, hd', hs i inf_le_left, hs i' inf_le_right, hA] at iso
  have hee : constFn B'.hom ((pr ≫ m₀) ⁻¹ᵁ (V i ⊓ V i')) DualNumber.eps *
      constFn B'.hom ((pr ≫ m₀) ⁻¹ᵁ (V i ⊓ V i')) DualNumber.eps = 0 := by
    rw [← GlobalTheory.PotIso.constFn_mul_c, DualNumber.eps_mul_eps, GlobalTheory.PotIso.constFn_zero_c]
  generalize d (V i ⊓ V i') (rsT (P.L.g (jj i) (jj i')).val (V i ⊓ V i')) = D at iso ⊢
  generalize pbT m₀ (P.L.g (jj i) (jj i')).val (m₀ ⁻¹ᵁ (V i ⊓ V i')) = g₀ at iso ⊢
  have key : constFn B'.hom ((pr ≫ m₀) ⁻¹ᵁ (V i ⊓ V i')) DualNumber.eps *
      pbT pr (constFn A₀.hom (m₀ ⁻¹ᵁ (V i ⊓ V i')) (a : k) * D) ((pr ≫ m₀) ⁻¹ᵁ (V i ⊓ V i')) =
      constFn B'.hom ((pr ≫ m₀) ⁻¹ᵁ (V i ⊓ V i')) DualNumber.eps *
      pbT pr (g₀ * (rsT (b i') (m₀ ⁻¹ᵁ (V i ⊓ V i')) - rsT (b i) (m₀ ⁻¹ᵁ (V i ⊓ V i'))))
        ((pr ≫ m₀) ⁻¹ᵁ (V i ⊓ V i')) := by
    rw [pbT_mul, pbT_mul, pbT_sub]
    linear_combination iso - (pbT pr (rsT (b i) (m₀ ⁻¹ᵁ (V i ⊓ V i'))) ((pr ≫ m₀) ⁻¹ᵁ (V i ⊓ V i')) *
      pbT pr D ((pr ≫ m₀) ⁻¹ᵁ (V i ⊓ V i'))) * hee
  obtain ⟨_, _, huniq⟩ := thick (m₀ ⁻¹ᵁ (V i ⊓ V i'))
    (constFn B'.hom (pr ⁻¹ᵁ (m₀ ⁻¹ᵁ (V i ⊓ V i'))) DualNumber.eps *
      pbT pr (constFn A₀.hom (m₀ ⁻¹ᵁ (V i ⊓ V i')) (a : k) * D) (pr ⁻¹ᵁ (m₀ ⁻¹ᵁ (V i ⊓ V i'))))
  have u₁ := huniq (0, constFn A₀.hom (m₀ ⁻¹ᵁ (V i ⊓ V i')) (a : k) * D) (by
    simp only [map_zero, zero_add, app_eq_pbT])
  have u₂ := huniq (0, g₀ * (rsT (b i') (m₀ ⁻¹ᵁ (V i ⊓ V i')) - rsT (b i) (m₀ ⁻¹ᵁ (V i ⊓ V i')))) (by
    simp only [map_zero, zero_add, app_eq_pbT]; exact key)
  have hX := congrArg Prod.snd (u₁.trans u₂.symm)
  simp only at hX
  have hc : constFn A₀.hom (m₀ ⁻¹ᵁ (V i ⊓ V i')) ((a⁻¹ : kˣ) : k) * constFn A₀.hom (m₀ ⁻¹ᵁ (V i ⊓ V i')) (a : k) = 1 := by
    rw [← GlobalTheory.PotIso.constFn_mul_c, Units.inv_mul, GlobalTheory.PotIso.constFn_one_c]
  show D = g₀ * (rsT (constFn A₀.hom (m₀ ⁻¹ᵁ V i') ((a⁻¹ : kˣ) : k) * b i') (m₀ ⁻¹ᵁ (V i ⊓ V i')) -
    rsT (constFn A₀.hom (m₀ ⁻¹ᵁ V i) ((a⁻¹ : kˣ) : k) * b i) (m₀ ⁻¹ᵁ (V i ⊓ V i')))
  rw [rsT_mul, rsT_mul, GlobalTheory.KS.rsT_constFn _ (m₀.preimage_mono inf_le_right),
    GlobalTheory.KS.rsT_constFn _ (m₀.preimage_mono inf_le_left)]
  linear_combination constFn A₀.hom (m₀ ⁻¹ᵁ (V i ⊓ V i')) ((a⁻¹ : kˣ) : k) * hX - D * hc

end GlobalTheory.PotIso
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCycleExtensionTaylorPeriodOfThickeningCoStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constantCycleExtension_taylorPeriod_of_thickeningComparison : GlobalTheory.AnPer.PTaylor := by
  first | exact @GlobalTheory.AnPer.pTaylor | exact GlobalTheory.AnPer.pTaylor | (intros; apply GlobalTheory.AnPer.pTaylor <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordinateLogDerivMinusPotentialsChartIndependenStatement
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
open GlobalTheory.HeatConn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coordinate_logDeriv_minus_potentials_chart_independent : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) {n : ℕ} {dd : Fin n → Fld Y.H.left} {D : R → R} (h : Heat Y.H Y.q.left Q.P.L dd D) {K : Type} [Field K] [CharZero K] (φ : R →+* K) (e : ℕ) (ν : R) (A₀ : Over (Sp K)) [GrpObj A₀] (m₀ : A₀.left ⟶ Q.P.A.left), IsFibre Y h φ e ν A₀ m₀ → ∀ (V : h.J → Q.P.A.left.Opens) (ed : ∀ W : Q.P.A.left.Opens, Γ(Q.P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)) (pb : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i)), IsConnK Q.P.A Q.P.L A₀ m₀ (fun r => φ (D r)) V h.j ed pb → IsDesc Y h ν m₀ V ed pb → Commutes Q m₀ ed → ∀ α : Q.X, ChartFree Y h ν m₀ V pb α := by
  first | exact @GlobalTheory.HeatConn.chartFree | exact GlobalTheory.HeatConn.chartFree | (intros; apply GlobalTheory.HeatConn.chartFree <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamToRigidifiedExtensionBijectivePNilpotentStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deRham_to_rigidified_extension_bijective_p_nilpotent : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (p : ℕ) [Fact p.Prime]  (R : Type) [CommRing R], IsNilpotent (p : R) → ∀ (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (G : PDivGroup p R) (t : G.TorsionTower A) (L : primDR A →ₗ[R] G.RigExt), (∀ c, IsCan t c (L c)) → Function.Bijective L := by
  first | exact @GlobalTheory.PtExt.bijective_of_isCan_of_isNilpotent_of_hodgeDeRham | exact GlobalTheory.PtExt.bijective_of_isCan_of_isNilpotent_of_hodgeDeRham | (intros; apply GlobalTheory.PtExt.bijective_of_isCan_of_isNilpotent_of_hodgeDeRham <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescSt
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc GlobalTheory.SiegJoin

namespace GlobalTheory.SiegDescent

theorem exists_chart {o : Type} [CommRing o] {ζ : o} {g n : ℕ} {F : SFam g n ζ} {S : Scheme.{0}} {s : S ⟶ Sp o}
    {j : F.X ⟶ S} [IsOpenImmersion j] {φ : InvFun ℤ} {BD : EffCartierData S} {d : ℕ} {x : S}
    (h : GlobalTheory.PolDeg.PreChart F s j φ BD d x) :
    ∃ C : Chart j F.univ.A x, ∀ p : Sp C.R, p ∈ abLocus C.G ↔ C.ξ p ∈ Set.range j := by
  obtain ⟨R, _, _, _, b, ξ, m, t, Q, δ, a, G₁, _, y, α₁, ⟨hc, h0, -, hx, het, hun⟩, ⟨-, -, hr⟩, ⟨hs, hab, hy, hgen⟩, -⟩ := h
  exact ⟨{ R := R, complete := hc, charZero := h0, ξ := ξ, centre := hx, etc := het, unr := hun, G := G₁, semi := hs,
           y := y, hy := hy, α := α₁, gen := hgen }, fun p => (hab p).trans (hr p).symm⟩

theorem descSt : GlobalTheory.SiegJoin.DescSt := by
  intro g _ φ n hn _ F Z z i OZ d S π j _ BD _ hB _ hC
  obtain ⟨J, -, -, -, ⟨hN, -⟩, hP, hD, -⟩ := hB
  have hn0 : n ≠ 0 := by omega
  haveI : IsDedekindDomain (cycAway n) := (arBase_cycAway n hn0).1
  haveI : IsProper (π ≫ z) := GlobalTheory.SchemeWords.isProper_of_isProjOver hP
  haveI : IsNoetherianRing (CommRingCat.of (cycAway n)) := inferInstanceAs (IsNoetherianRing (cycAway n))
  haveI : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian (π ≫ z)
  haveI : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace (π ≫ z)
  haveI : AlgebraicGeometry.IsNoetherian S := {}
  have hj : IsDominant j := ⟨hD⟩
  have hd : SmoothOfRelativeDimension g F.univ.A.hom :=
    GlobalTheory.SiegSharpCover.smoothDim F.univ (by omega) (cycBase hn0).ζ.isUnit (isUnit_natCast hn0)
  obtain ⟨G, _, e, hG, he, hπ⟩ := GlobalTheory.T.semiAbelian_descent_from_complete_regular_charts F.X S ((GlobalTheory.isNormalScheme_iff_pred S).1 hN) j hj F.univ.A F.univ.ab F.univ.diag (pull_isLB F.univ.isLB _)
    F.princ.1 fun x => ⟨(exists_chart (hC x)).choose⟩
  obtain ⟨h₁, h₂⟩ := GlobalTheory.T.descended_group_abelianLocus_and_relDim F.X S j hj F.univ.A G e g F.univ.ab hd hG he fun x => by
    obtain ⟨C, hab⟩ := exists_chart (hC x)
    obtain ⟨p, hp, -⟩ := hπ x C
    exact ⟨C.R, inferInstance, inferInstance, C.ξ, C.G, inferInstance, p, C.centre, hp, hab⟩
  exact ⟨G, inferInstance, e, hG, h₂, he, h₁⟩

end GlobalTheory.SiegDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedBundleHodgeClassStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.descended_bundle_hodge_class : Hypotheses2 → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), 1 ≤ Dw.p → 1 ≤ Dw.q → FnAlgClosed Xo c → ∀ (δ : LB (X₀ TF.Y Z)) (hδ : δ.IsLB), CechPic.pull (π₀ TF.X Z) (cls δ hδ) = cls (L₀ TF.X Z (hodgeWt Dw)) (isLB_L₀ TF.X Z _) → letI := algebraΓOfHom (s₀ TF.Y Z); IsBig c.F δ := by
  first | exact @GlobalTheory.HodgeBig.isBig_hodgeLine | exact GlobalTheory.HodgeBig.isBig_hodgeLine | (intros; apply GlobalTheory.HodgeBig.isBig_hodgeLine <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalRestrictionRelAmpleLocusOpenStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diagonal_restriction_relAmple_locus_open : ∀ (S' : Scheme.{0}) [IsLocallyNoetherian S'] (G : Over S') [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), IsAbelianScheme G → P.IsLB → ∃ U : S'.Opens, (∀ V : S'.Opens, V ≤ U → Out.RelAmple ((Over.pullback V.ι).obj G) ((P.pull (Pdiv.PullbackComparison.pφ₂ V.ι G)).pull (lift (𝟙 ((Over.pullback V.ι).obj G)) (𝟙 ((Over.pullback V.ι).obj G))).left)) ∧ ∀ (T : Scheme.{0}) (g : T ⟶ S') (A' : Over T) [GrpObj A'] (φ : A'.left ⟶ G.left) (φ₂ : (G2 A').left ⟶ (G2 G).left) (P' : LB (G2 A').left), IsGrpPullback A' G g φ → IsSquare φ φ₂ → P'.IsLB → LBIso P' (P.pull φ₂) → Out.RelAmple A' (P'.pull (lift (𝟙 A') (𝟙 A')).left) → Set.range g.base ⊆ (U : Set S') := by
  first | (exact @GlobalTheory.DiagAmpleLocus.diag_relAmple_locus) | (exact GlobalTheory.DiagAmpleLocus.diag_relAmple_locus) | (intros; apply GlobalTheory.DiagAmpleLocus.diag_relAmple_locus  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberUnitTranslateEqIdFieldPoints
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.InfTranslPts

theorem factor_fst {S K : Type} [CommRing S] [Field K] (w : Sp K ⟶ Sp (DualNumber S)) :
    w = (w ≫ spMap (algebraMap S (DualNumber S))) ≫ spMap (TrivSqZeroExt.fstHom S S S).toRingHom := by
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective w
  have hε : ψ.hom (DualNumber.eps : DualNumber S) = 0 := by
    have h : ψ.hom (DualNumber.eps : DualNumber S) * ψ.hom (DualNumber.eps : DualNumber S) = 0 := by
      rw [← map_mul, DualNumber.eps_mul_eps, map_zero]
    exact mul_self_eq_zero.1 h
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  refine RingHom.ext fun x => ?_
  change ψ.hom x = ψ.hom (algebraMap S (DualNumber S) x.fst)
  have hx : x = algebraMap S (DualNumber S) x.fst + algebraMap S (DualNumber S) x.snd * DualNumber.eps := by
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  conv_lhs => rw [hx]
  rw [map_add, map_mul, hε, mul_zero, add_zero]

theorem transl_field_point {X : Scheme.{0}} (G : Over X) [GrpObj G] {S : Type} [CommRing S] (x0 : Sp S ⟶ X)
    (P : tEpsG x0 ⟶ G)
    (hP : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ P.left = (1 : Over.mk x0 ⟶ G).left)
    {K : Type} [Field K] (z : Sp K ⟶ (tEpsG x0 ⊗ G).left) :
    z ≫ (lift (fst (tEpsG x0) G ≫ P) (snd (tEpsG x0) G) ≫ μ[G]).left = z ≫ (snd (tEpsG x0) G).left := by
  let zz : Over.mk (z ≫ (tEpsG x0 ⊗ G).hom) ⟶ tEpsG x0 ⊗ G := Over.homMk z rfl
  let p : tEpsG x0 ⟶ Over.mk x0 := Over.homMk (spMap (algebraMap S (DualNumber S))) rfl
  have h1 : GlobalTheory.VertSpanZero.redOver x0 ≫ P = 1 := Over.OverMorphism.ext hP
  have h2 : zz ≫ fst (tEpsG x0) G = (zz ≫ fst (tEpsG x0) G ≫ p) ≫ GlobalTheory.VertSpanZero.redOver x0 := by
    apply Over.OverMorphism.ext
    have := factor_fst (S := S) (K := K) (z ≫ (fst (tEpsG x0) G).left)
    exact this
  have h3 : zz ≫ fst (tEpsG x0) G ≫ P = 1 := by
    rw [← Category.assoc, h2, Category.assoc, h1, MonObj.comp_one]
  have h4 : zz ≫ ((fst (tEpsG x0) G ≫ P) * snd (tEpsG x0) G) = zz ≫ snd (tEpsG x0) G := by
    rw [MonObj.comp_mul, h3, _root_.one_mul]
  exact congrArg (fun q => q.left) h4

theorem transl_points : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (S : Type) [CommRing S] (x0 : Sp S ⟶ X) (P : tEpsG x0 ⟶ t.G), spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ P.left = (1 : Over.mk x0 ⟶ t.G).left → ∀ y : (tEpsG x0 ⊗ t.G).left, ∃ (K : Type) (_ : Field K) (z : Sp K ⟶ (tEpsG x0 ⊗ t.G).left), y ∈ Set.range z.base ∧ z ≫ (lift (fst (tEpsG x0) t.G ≫ P) (snd (tEpsG x0) t.G) ≫ μ[t.G]).left = z ≫ (snd (tEpsG x0) t.G).left := by
  intro E _ _ _ H X t S _ x0 P hP y
  refine ⟨(tEpsG x0 ⊗ t.G).left.residueField y, inferInstance,
    (tEpsG x0 ⊗ t.G).left.fromSpecResidueField y, ?_, transl_field_point t.G x0 P hP _⟩
  exact ⟨IsLocalRing.closedPoint _, Scheme.fromSpecResidueField_apply y _⟩

end GlobalTheory.InfTranslPts
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqualVolumeDeepLevel
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

namespace GlobalTheory.CompEqVol

theorem eqVolume_good : Hypotheses2 → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → EqVolume Y.U := by
  intro hP2 hS hKS hSA D T hT j hp hq hf hj Y e o hY
  have hr : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by omega
  obtain ⟨M, hs, hb, hk, hc⟩ := hKS.exists_model_charts hS hr Y.d.Xo₂ Y.d.c₂
  obtain ⟨TF, hTF⟩ := GlobalTheory.CompProport.exists_torFlag_charts hr M hs hb hk hc
  have hσ : GoodEmb Y.d.c₂ Y.d.c₂.F.val.toRingHom := rfl
  obtain ⟨-, q, -, hv⟩ := GlobalTheory.CompProport.vZero_eq_covol (GlobalTheory.T.stronger_published_hypotheses_imply hP2) hP2.q7 hSA hY hf TF hTF hσ
  have hg0 : ∀ p : ℕ, p.Prime → T.Q.l.GoodAt p :=
    Formalism.L2.Pj.goodAt_of_two_primes hT.pins.2.1.1 (D.host.g_prime 0) (D.host.g_prime 1) D.host.g_ne
  have hg : ∀ p : ℕ, p.Prime → Y.d.l₂.GoodAt p := GlobalTheory.LawsDeep.goodAt_of_mul _ _ _ hY.lev.1.2.1 hg0
  have hcov := GlobalTheory.T.complexUniformisation_components_covolume_eq _ _ _ _ _ _ _ _ (Formalism.L2.PjFree.Unf.ofPj (Y.U Y.d.c₂.F.val.toRingHom)) hσ
    ((Formalism.L2.PjFree.isUnf_ofPj _).2 (hY.unf _ hσ)) hg hp hq
  intro Z Z'
  obtain ⟨k, rfl⟩ := q.surjective Z
  obtain ⟨k', rfl⟩ := q.surjective Z'
  rw [hv, hv]
  exact congrArg (fun x => x * _ / _) (hcov k k')

end GlobalTheory.CompEqVol
end

