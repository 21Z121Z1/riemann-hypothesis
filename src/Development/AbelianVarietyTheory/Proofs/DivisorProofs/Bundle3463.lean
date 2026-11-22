import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3443
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2514
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0618
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2643
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3448
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2590
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2675
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2973
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0044
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3384
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3438
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3444
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3381
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSymmOfKsCoc
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0101
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0140
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0176
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfForallField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudTorusWeightZeroInvariantFieldCoeffs
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0044
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3441
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3436
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3445
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0692
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0848
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0765
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3431

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerKilledOn
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.KerKilledLocus

def KerKilledOn (d : ℕ) {S' : Scheme.{0}} (G : Over S') [GrpObj G] [IsCommMonObj G]
    (P : LB (G2 G).left) (V : S'.Opens) : Prop :=
  ∀ (T : Over V.toScheme) (x : T ⟶ (Over.pullback V.ι).obj G),
    (∃ s : ((P.pull (Pdiv.PullbackComparison.pφ₂ V.ι G)).pull
        (lift (snd ((Over.pullback V.ι).obj G) T ≫ x) (fst ((Over.pullback V.ι).obj G) T)).left).Gen,
        s.IsGen) → x ^ d = 1

end GlobalTheory.KerKilledLocus
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyFormulaEvenDegenerationGlobalOfLocalUnits
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.KeyEvenGlue

theorem lbPow_U' {S : Scheme.{0}} (M : LB S) (n : ℕ) (j : (lbPow M n).ι) : (lbPow M n).U j = M.U (j PUnit.unit) := by
  ext x
  simp only [lbPow, LB.LinComb, LB.wchart]
  simp
  exact ⟨fun h => h _, fun h i => h⟩

theorem germ_lbPow_g' {S : Scheme.{0}} (M : LB S) (n : ℕ) (j j' : (lbPow M n).ι) (x : S)
    (h : x ∈ (lbPow M n).U j ⊓ (lbPow M n).U j') (h' : x ∈ M.U (j PUnit.unit) ⊓ M.U (j' PUnit.unit)) :
    S.presheaf.germ _ x h ((lbPow M n).g j j' : Γ(S, (lbPow M n).U j ⊓ (lbPow M n).U j')) =
      S.presheaf.germ _ x h' (M.g (j PUnit.unit) (j' PUnit.unit) : Γ(S, M.U (j PUnit.unit) ⊓ M.U (j' PUnit.unit))) ^ n := by
  simp only [lbPow, LB.LinComb, Fintype.prod_unique, zpow_natCast, Units.val_pow_eq_pow_val, map_pow]
  congr 1
  simp [res, pullU]
  erw [map_pow]
  congr 1
  erw [Units.coe_map, Units.coe_map]
  exact TopCat.Presheaf.germ_res_apply _ _ _ _ _

theorem keyGlob_of_keyLoc : ∀ κ : Rule, Homog (fun _ => 1) κ → Funct κ → KeyLoc κ → KeyGlob := by
  intro κ hH hF hL S s G _ _ g L δ σ hg hS hN hs h0 hsa hsm hne hop hsym hδ hpol hunif hnz
  haveI := hS
  obtain ⟨f, hloc, hcomp⟩ := GlobalTheory.T.thetaKeyValues_detOmega_delta_local_units κ hH hF hL S s G g L δ σ hg hN hs h0 hsa hsm hne hop hsym hδ hpol hunif hnz
  refine GlobalTheory.T.lineBundleIso_of_compatible_rational_local_units S (lbPow δ 8) (lbPow (SiegelTor.hodge G g) 4) (fun p => f (p.1 PUnit.unit) (p.2 PUnit.unit)) ?_ ?_
  · rintro ⟨c, i⟩ x hx
    rw [lbPow_U', lbPow_U'] at hx
    obtain ⟨V, hV, hxV, u, hu⟩ := hloc _ _ x hx
    exact ⟨V, by rw [lbPow_U', lbPow_U']; exact hV, hxV, u, hu⟩
  · rintro ⟨c, i⟩ ⟨c', i'⟩ h1 h2
    have h1' : genericPoint S ∈ (VB.det (LieVB.omega G) g).U (c PUnit.unit) ⊓ (VB.det (LieVB.omega G) g).U (c' PUnit.unit) := by
      rw [lbPow_U', lbPow_U'] at h1; exact h1
    have h2' : genericPoint S ∈ δ.U (i PUnit.unit) ⊓ δ.U (i' PUnit.unit) := by
      rw [lbPow_U', lbPow_U'] at h2; exact h2
    dsimp only
    rw [germ_lbPow_g' δ 8 i i' _ h2 h2', germ_lbPow_g' _ 4 c c' _ h1 h1']
    exact hcomp _ _ _ _ h1' h2'

end GlobalTheory.KeyEvenGlue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KltOfKltRestrict
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

theorem GlobalTheory.FieldPair.klt_of_klt_restrict : GlobalTheory.Published.Principalisation →
  ∀ {L K : Type} [Field L] [Field K] (cL : ℂ →+* L) (cK : ℂ →+* K) (n : ℕ) (T : Subring L) (hT : IsLocModel cL T)
    (ψ : T →+* K) (f : T) (w : Fin n → T) (θ : T →₀ ℚ),
  IsIntegrallyClosed T → (∀ a, ψ ⟨cL a, hT.const_mem a⟩ = cK a) →
  RingHom.ker ψ = Ideal.span {f} → f ≠ 0 → IsLocModel cK ψ.range → TrBasis cK (fun i => ψ (w i)) →
  (∀ g ∈ θ.support, ψ g ≠ 0) →
  EffAt cL (n + 1) T (dForm cL (Fin.cons (f : L) (fun i => (w i : L)) : Fin (n + 1) → L))
    (Finsupp.mapDomain (fun g : T => (g : L)) θ) →
  Klt cK n ψ.range (dForm cK (fun i => ψ (w i))) (Finsupp.mapDomain ψ θ) →
  Klt cL (n + 1) T (dForm cL (Fin.cons (f : L) (fun i => (w i : L)) : Fin (n + 1) → L))
    (Finsupp.mapDomain (fun g : T => (g : L)) θ) := by
  classical
  intro hP L K _ _ cL cK n T hT ψ f w θ hic hconst hker hf0 hRng hTr hsupp hEff hKlt
  obtain ⟨S, hS, ψS, hsurj, hcK, hcomp, hirr⟩ :=
    GlobalTheory.T.exists_dvrPlace_of_prime_element_of_normal_localModel cL cK n T hT ψ f hic hconst hker hf0 hRng

  let ι : T → S.ring := fun t => ⟨t, hS.1 t t.2⟩
  have hw : (fun i => ψS (ι (w i))) = fun i => ψ (w i) := funext fun i => hcomp (w i)
  have hTr' : TrBasis cK (fun i => ψS (ι (w i))) := by rw [hw]; exact hTr
  obtain ⟨hTrL, hform, hord, hord0⟩ :=
    GlobalTheory.T.transcendenceBasis_uniformiser_cons_residual_lifts cL cK n S ψS (ι f) (fun i => ι (w i)) hsurj hcK hirr hTr'
  have hmapS : Finsupp.mapDomain ψS (Finsupp.mapDomain ι θ) = Finsupp.mapDomain ψ θ := by
    rw [← Finsupp.mapDomain_comp]
    congr 1
    funext t
    exact hcomp t
  have hmapL : Finsupp.mapDomain (fun g : S.ring => (g : L)) (Finsupp.mapDomain ι θ) =
      Finsupp.mapDomain (fun g : T => (g : L)) θ := by
    rw [← Finsupp.mapDomain_comp]
    rfl
  have hsuppS : ∀ g ∈ (Finsupp.mapDomain ι θ).support, ψS g ≠ 0 := by
    intro g hg
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hg)
    intro h
    exact hsupp t ht ((hcomp t).symm.trans h)
  have hrange : ∀ a ∈ ψ.range, ∃ t : T, ψS ⟨t, hS.1 t t.2⟩ = a := by
    rintro a ⟨t, rfl⟩
    exact ⟨t, hcomp t⟩
  have hKlt' : Klt cK n ψ.range (dForm cK (fun i => ψS (ι (w i))))
      (Finsupp.mapDomain ψS (Finsupp.mapDomain ι θ)) := by
    rw [hw, hmapS]
    exact hKlt
  have hadj := GlobalTheory.T.adjunctionKlt_of_klt_along_residue_subring cL cK n T S hS.1 ψS (ι f) (fun i => ι (w i))
    (Finsupp.mapDomain ι θ) ψ.range hsurj hcK hirr hTr' hsuppS hrange hKlt'
  have hadj' : AdjKlt cL (n + 1) T S
      (dForm cL (Fin.cons (f : L) (fun i => (w i : L)) : Fin (n + 1) → L))
      (Finsupp.mapDomain (fun g : T => (g : L)) θ + Finsupp.single (f : L) 1) := by
    rw [← hmapL]
    exact hadj
  have hTrL' : TrBasis cL (Fin.cons (f : L) (fun i => (w i : L)) : Fin (n + 1) → L) := hTrL
  have hform' : S.formOrd (dForm cL (Fin.cons (f : L) (fun i => (w i : L)) : Fin (n + 1) → L)) = 0 :=
    hform
  have hord' : S.ord (f : L) = 1 := hord
  have hfL : (f : L) ≠ 0 := fun h => hf0 (Subtype.ext h)

  have hq : S.ordQ (Finsupp.mapDomain (fun g : T => (g : L)) θ) = 0 := by
    rw [Place.ordQ, Finsupp.linearCombination_mapDomain, Finsupp.linearCombination_apply]
    unfold Finsupp.sum
    refine Finset.sum_eq_zero fun t ht => ?_
    have h0 : S.ord (t : L) = 0 :=
      hord0 (ι t) (fun h => hsupp t ht ((hcomp t).symm.trans h))
    simp [Function.comp, h0]
  have hdisc : S.disc (dForm cL (Fin.cons (f : L) (fun i => (w i : L)) : Fin (n + 1) → L))
      (Finsupp.mapDomain (fun g : T => (g : L)) θ) = 0 := by
    rw [Place.disc, hform', hq]
    simp
  exact GlobalTheory.T.klt_of_adjunctionKlt_localModel hP cL (n + 1) T _ _ (f : L) S hT hic hTrL' f.2 hfL hS hord' hdisc hEff hadj'
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerDescentOfTorusInvariantLifts
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

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatDescend

open GlobalTheory.KS

theorem alg_sum {Γ₀ R : Type} [CommRing Γ₀] [CommRing R] {g n : ℕ} (κ : R →+* Γ₀) (P : Matrix (Fin g) (Fin n) R)
    (C : Matrix (Fin n) (Fin n) R) (X Z : Fin g → Γ₀) :
    ∑ a, ∑ b, κ (C a b) * (∑ c', κ (P c' b) * X c') * ∑ c, κ (P c a) * Z c =
      ∑ c, ∑ c', κ ((P * C * Pᵀ) c c') * X c' * Z c := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  calc ∑ a, ∑ b, ∑ c, ∑ c', κ (C a b) * (κ (P c' b) * X c') * (κ (P c a) * Z c)
      = ∑ b, ∑ a, ∑ c, ∑ c', κ (C a b) * (κ (P c' b) * X c') * (κ (P c a) * Z c) := Finset.sum_comm
    _ = ∑ b, ∑ c, ∑ c', ∑ a, κ (C a b) * (κ (P c' b) * X c') * (κ (P c a) * Z c) :=
        Finset.sum_congr rfl fun b _ => Finset.sum_comm.trans (Finset.sum_congr rfl fun c _ => Finset.sum_comm)
    _ = ∑ c, ∑ c', ∑ b, ∑ a, κ (C a b) * (κ (P c' b) * X c') * (κ (P c a) * Z c) :=
        Finset.sum_comm.trans (Finset.sum_congr rfl fun c _ => Finset.sum_comm)
    _ = _ := by
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun c' _ => Finset.sum_congr rfl fun b _ =>
          Finset.sum_congr rfl fun a _ => ?_
        ring

theorem pbT_id' {X : Scheme.{0}} {U : X.Opens} (s : Γ(X, U)) {O : X.Opens} (h : O ≤ U) : pbT (𝟙 X) s O = rsT s O := by
  rw [pbT_of_le (𝟙 X) (show O ≤ (𝟙 X) ⁻¹ᵁ U from h), rsT_of_le h]
  rfl

theorem valR_pbT {A : Type} [CommRing A] {X Z : Scheme.{0}} (x : Sp A ⟶ Z) (q : Z ⟶ X) (V : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ (q ⁻¹ᵁ V)) (f : Γ(X, V)) :
    valR x (q ⁻¹ᵁ V) (pbT q f (q ⁻¹ᵁ V)) = valR (x ≫ q) V f := by
  rw [GlobalTheory.Heat.WtAlg.valR_eq' x _ h, GlobalTheory.KS.pbT_of_le q le_rfl, GlobalTheory.Heat.WtAlg.valR_eq' (x ≫ q) V h]
  rw [← Scheme.Hom.appLE_comp_appLE x q V (q ⁻¹ᵁ V) ⊤ le_rfl h]
  rfl

theorem isWt_pbT {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
    {oa : Q.OAct O} (Y : Ray oa) (V : Q.P.A.left.Opens) (f : Γ(Q.P.A.left, V)) :
    IsWt Y 0 _ (pbT Y.q.left f (Y.q.left ⁻¹ᵁ V)) := by
  intro S _ φ x x' c a a' ha ha' hV hV' hq hc
  rw [GlobalTheory.Heat.WtAlg.c_zero x x' c hc, Units.val_one, _root_.one_mul, valR_pbT _ _ _ hV', valR_pbT _ _ _ hV]
  subst ha ha'
  have e : x'.left ≫ Y.q.left = x.left ≫ Y.q.left := by
    rw [← Over.comp_left, ← Over.comp_left, hq]
  rw [e]

section General

variable {R : Type} [CommRing R] {G B : Over (Sp R)} (q : G ⟶ B)

theorem exists_lift (hinj : ∀ (O : B.left.Opens) (f f' : Γ(B.left, O)),
      pbT q.left f (q.left ⁻¹ᵁ O) = pbT q.left f' (q.left ⁻¹ᵁ O) → f = f')
    (D : R → R) (V : B.left.Opens) (d : Fld G.left) (hd : IsLift G D (q.left ⁻¹ᵁ V) d)
    (hdesc : ∀ O, O ≤ V → ∀ f : Γ(B.left, O), ∃ f' : Γ(B.left, O),
      pbT q.left f' (q.left ⁻¹ᵁ O) = d _ (pbT q.left f (q.left ⁻¹ᵁ O))) :
    ∃ dB : Fld B.left, IsLift B D V dB ∧ ∀ O, O ≤ V → ∀ f : Γ(B.left, O),
      pbT q.left (dB O f) (q.left ⁻¹ᵁ O) = d _ (pbT q.left f (q.left ⁻¹ᵁ O)) := by
  classical
  have hq : q.left ≫ B.hom = G.hom := Over.w q
  let dB : Fld B.left := fun O f => if h : O ≤ V then (hdesc O h f).choose else 0
  have hB : ∀ O, O ≤ V → ∀ f : Γ(B.left, O),
      pbT q.left (dB O f) (q.left ⁻¹ᵁ O) = d _ (pbT q.left f (q.left ⁻¹ᵁ O)) := by
    intro O h f
    simp only [dB, dif_pos h]
    exact (hdesc O h f).choose_spec
  obtain ⟨⟨h1, h2, h3⟩, h4⟩ := hd
  refine ⟨dB, ⟨⟨fun O h f f' => hinj O _ _ ?_, fun O h f f' => hinj O _ _ ?_, fun O O' h' h f => hinj O' _ _ ?_⟩,
    fun O h r => hinj O _ _ ?_⟩, hB⟩
  · rw [pbT_add, hB O h, hB O h, hB O h, pbT_add, h1 _ (q.left.preimage_mono h)]
  · rw [pbT_add, pbT_mul, pbT_mul, hB O h, hB O h, hB O h, pbT_mul, h2 _ (q.left.preimage_mono h)]
  · have hp : q.left ⁻¹ᵁ O' ≤ q.left ⁻¹ᵁ O := q.left.preimage_mono h'
    rw [hB O' (h'.trans h), ← rsT_of_le h', ← rsT_of_le h', pbT_rsT _ h' le_rfl, pbT_rsT _ h' le_rfl,
      ← rsT_pbT q.left le_rfl hp, ← rsT_pbT q.left le_rfl hp (dB O f), hB O h, rsT_of_le hp, rsT_of_le hp]
    exact h3 _ _ hp (q.left.preimage_mono h) _
  · rw [hB O h, pbT_constFn _ _ le_rfl, pbT_constFn _ _ le_rfl, hq, h4 _ (q.left.preimage_mono h)]

theorem dlg_pull {g : ℕ} (L : LB B.left) (δ : Fld G.left) (e : Fin g → Fld B.left) (he : ∀ c, IsField ⊤ (e c))
    (p : Fin g → R) (hδ : ∀ (V : B.left.Opens) (W : G.left.Opens), W ≤ q.left ⁻¹ᵁ V → ∀ f : Γ(B.left, V),
      δ W (pbT q.left f W) = ∑ c, constFn G.hom W (p c) * pbT q.left (e c V f) W)
    (i i' : L.ι) (O : B.left.Opens) (h : O ≤ L.U i ⊓ L.U i') :
    dlg G q.left L δ i i' (q.left ⁻¹ᵁ O) =
      ∑ c, constFn G.hom _ (p c) * pbT q.left (dlg B (𝟙 _) L (e c) i i' O) (q.left ⁻¹ᵁ O) := by
  unfold dlg
  rw [← pbT_rsT q.left h le_rfl, hδ O _ le_rfl, Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [pbT_mul, pbT_id' _ h, pbT_id' _ h, pbT_rsT q.left h le_rfl, _root_.mul_assoc]

end General

theorem ksRel_of_invLifts : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (g : ℕ) (w : Module.Basis (Fin g) R (TanM (𝟙 (Sp R)) Dd.toPre.P.A)) (e : Fin g → Fld Dd.toPre.P.A.left) (P : Matrix (Fin g) (Fin n) R), (∀ c, IsInv Dd.toPre.P.A (w c) (e c)) → (∀ b (V : Dd.toPre.P.A.left.Opens) (W : Y.H.left.Opens), W ≤ Y.q.left ⁻¹ᵁ V → ∀ f : Γ(Dd.toPre.P.A.left, V), dd b W (pbT Y.q.left f W) = ∑ c, constFn Y.H.hom W (P c b) * pbT Y.q.left (e c V f) W) → ∀ (D : Derivation ℤ R R) (J : Type) (V : J → Dd.toPre.P.A.left.Opens) (j : J → Dd.toPre.P.L.ι) (d : J → Fld Y.H.left), ⨆ i, V i = ⊤ → (∀ i, V i ≤ Dd.toPre.P.L.U (j i)) → (∀ i, IsLift Y.H ⇑D (Y.q.left ⁻¹ᵁ V i) (d i)) → (∀ i, (∀ (α : Dd.toPre.X) (V' : Dd.toPre.P.A.left.Opens), Y.q.left ⁻¹ᵁ V' ≤ Y.q.left ⁻¹ᵁ V i → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V') f → IsWt Y α (Y.q.left ⁻¹ᵁ V') (d i _ f))) → ∀ C : Matrix (Fin n) (Fin n) R, (∀ i i' (W : Y.H.left.Opens), W ≤ Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i' → ∀ f, d i W f - d i' W f = ∑ a, ∑ b, constFn Y.H.hom W (C a b) * dlg Y.H Y.q.left Dd.toPre.P.L (dd b) (j i) (j i') W * dd a W f) → KSRel Dd.toPre.P.A (𝟙 Dd.toPre.P.A.left) Dd.toPre.P.L e ⇑D (P * C * Pᵀ) := by
  intro R _ _ _ _ _ _ Dd O _ _ _ oa Y n v dd _ g w e P he hP D J V j d hcov hle hlift hwt C hC
  have hA := GlobalTheory.T.existsUnique_pullback_of_raynaudTorusWeight_zero R Dd.toPre O oa Y
  have hinj : ∀ (U : Dd.toPre.P.A.left.Opens) (f f' : Γ(Dd.toPre.P.A.left, U)),
      pbT Y.q.left f (Y.q.left ⁻¹ᵁ U) = pbT Y.q.left f' (Y.q.left ⁻¹ᵁ U) → f = f' := fun U f f' h =>
    (hA U _ (isWt_pbT Y U f')).unique h rfl
  choose dB hB hB' using fun i => exists_lift Y.q hinj D (V i) (d i) (hlift i) fun U hU f =>
    (hA U _ (hwt i 0 U (Y.q.left.preimage_mono hU) _ (isWt_pbT Y U f))).exists
  refine ⟨J, V, j, dB, hcov, hle, hB, fun i i' U hU f => hinj U _ _ ?_⟩
  have hq : Y.q.left ≫ Dd.toPre.P.A.hom = Y.H.hom := Over.w Y.q
  have hL : U ≤ Dd.toPre.P.L.U (j i) ⊓ Dd.toPre.P.L.U (j i') := hU.trans (inf_le_inf (hle i) (hle i'))
  rw [pbT_sub, hB' i U (hU.trans inf_le_left), hB' i' U (hU.trans inf_le_right),
    hC i i' _ (Y.q.left.preimage_mono hU)]
  simp only [fun b => dlg_pull Y.q Dd.toPre.P.L (dd b) e (fun c => (he c).1) (fun c => P c b) (hP b) _ _ U hL,
    fun a => hP a U _ le_rfl f, pbT_sum, pbT_mul, pbT_constFn _ Y.q.left (O₀ := U) le_rfl, hq]
  exact alg_sum ((Y.H.hom.appLE ⊤ _ (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) P C _ _

end GlobalTheory.HeatDescend
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerMatrixUniqueOverChartAbelianLocusStatement
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
theorem _root_.GlobalTheory.T.kodairaSpencer_matrix_unique_over_chart_abelian_locus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → ∀ (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Sp (ChartRing k m d), ⊤)) ⟶ t.G.left)), (∀ i, IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) (v i)) → (∀ w, IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) w → ∃! cf : Fin n → Γ(Sp (ChartRing k m d), ⊤), IsCombAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) v cf w) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (Θ Θ' : Matrix (Fin n) (Fin n) Γ(Sp (ChartRing k m d), ⊤)), IsKS t ((Sp (ChartRing k m d)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i))) (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens) v (fun r => (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom r))) Θ → IsKS t ((Sp (ChartRing k m d)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i))) (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens) v (fun r => (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom r))) Θ' → Θ = Θ' := by
  first | exact @GlobalTheory.ChartKSUniq.isKS_unique_chart | exact GlobalTheory.ChartKSUniq.isKS_unique_chart | (intros; apply GlobalTheory.ChartKSUniq.isKS_unique_chart <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerMatrixZeroDerivationEqZeroStatement
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kodairaSpencer_matrix_zero_derivation_eq_zero : ∀ (K : Type) [Field K] [CharZero K] (P₀ : Out.PolAV (Sp K)) (n : ℕ) (v : Module.Basis (Fin n) K (TanM (𝟙 (Sp K)) P₀.A)) (dd : Fin n → Fld P₀.A.left), (∀ a, IsInv P₀.A (v a) (dd a)) → ∀ M : Matrix (Fin n) (Fin n) K, KSRel P₀.A (𝟙 P₀.A.left) P₀.L dd (fun _ => 0) M → M = 0 := by
  first | exact @GlobalTheory.KSZeroDer.main | exact GlobalTheory.KSZeroDer.main | (intros; apply GlobalTheory.KSZeroDer.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerRelationMatrixSymmetricLocalDomain
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
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.KSRelSymm

theorem fieldCompat : ∀ {R : Type} [CommRing R] {K : Type} [Field K] (x₀ : R →+* K) {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {A : Over (Sp K)} [GrpObj A] [IsCommMonObj A] (m : A.left ⟶ G.left), IsGrpPullback A G (spMap x₀) m → ∀ (w : TanM (𝟙 (Sp R)) G) (e : Fld G.left), IsInv G w e → ∀ (v : epsR K ⟶ A), IsTangent v → v.left ≫ m = spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR x₀) ≫ (tv w).left → ∀ (dd : ∀ O : A.left.Opens, Γ(A.left, O) → Γ(A.left, O)), GlobalTheory.KS.IsInvDer v dd → ∀ (O : G.left.Opens) (f : Γ(G.left, O)), dd (m ⁻¹ᵁ O) ((m.app O).hom f) = pbT m (e O f) (m ⁻¹ᵁ O) := @GlobalTheory.Heat.FieldCompat.invField_baseChange

theorem cechData : ∀ {R : Type} [CommRing R] {K : Type} [Field K] (x₀ : R →+* K) (P : Out.PolAV (Sp R)) {A : Over (Sp K)} [GrpObj A] (m : A.left ⟶ P.A.left), m ≫ P.A.hom = A.hom ≫ spMap x₀ → ∀ {g : ℕ} (e : Fin g → Fld P.A.left) (dd : Fin g → ∀ O : A.left.Opens, Γ(A.left, O) → Γ(A.left, O)), (∀ a, IsField ⊤ (e a)) → (∀ a (O : P.A.left.Opens) (f : Γ(P.A.left, O)), dd a (m ⁻¹ᵁ O) ((m.app O).hom f) = pbT m (e a O f) (m ⁻¹ᵁ O)) → ∀ (D : Derivation ℤ R R) (M : Matrix (Fin g) (Fin g) R), KSRel P.A (𝟙 P.A.left) P.L e ⇑D M → ∃ L : LB P.A.left, Finite L.ι ∧ L.IsLB ∧ (∀ i, IsAffineOpen (L.U i)) ∧ LBIso P.L L ∧ ∃ d : L.ι → ∀ O : P.A.left.Opens, Γ(P.A.left, O) → Γ(A.left, m ⁻¹ᵁ O), ∀ φ, GlobalTheory.KS.IsDlog m L dd φ → GlobalTheory.KS.KSCoc A.hom P.A.hom m (fun r => x₀ (D r)) L.U dd d (fun a => GlobalTheory.KS.lc A.hom (fun b => -x₀ (M a b)) φ) := @GlobalTheory.KSCechData.exists_ksCoc_of_ksRel

theorem ksRel_symm : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (P : Out.PolAV (Sp R)) (g : ℕ) (w : Module.Basis (Fin g) R (TanM (𝟙 (Sp R)) P.A)) (e : Fin g → Fld P.A.left), (∀ c, IsInv P.A (w c) (e c)) → ∀ (D : Derivation ℤ R R) (M : Matrix (Fin g) (Fin g) R), KSRel P.A (𝟙 P.A.left) P.L e ⇑D M → Mᵀ = M := by
  intro R _ _ _ _ _ _ P g w e he D M hKS
  let K := FractionRing R
  let x₀ : R →+* K := algebraMap R K
  let P₀ : Out.PolAV (Sp K) := GlobalTheory.StrictPull.polPull P (spMap x₀)
  let m : P₀.A.left ⟶ P.A.left := pullback.fst P.A.hom (spMap x₀)
  have hm : IsGrpPullback P₀.A P.A (spMap x₀) m := isGrpPullback_pullback P.A (spMap x₀)
  have := P.isAb.comm
  have := P₀.isAb.comm
  have hs : Smooth P.A.hom := P.isAb.smooth
  obtain ⟨u, hu, hul⟩ := GlobalTheory.Heat.CoeffWt.exists_isLieBasis w
  obtain ⟨v, hv, hvl⟩ := GlobalTheory.exists_isLieBasis_baseChange R K x₀ P.A P₀.A m hm hs g u hu
  choose dd hdd using fun a => (GlobalTheory.KS.InvField.main K P₀.A (v a) (hv.1 a)).1
  have hcomp : ∀ a (O : P.A.left.Opens) (f : Γ(P.A.left, O)), dd a (m ⁻¹ᵁ O) ((m.app O).hom f) = pbT m (e a O f) (m ⁻¹ᵁ O) :=
    fun a => fieldCompat x₀ m hm (w a) (e a) (he a) (v a) (hv.1 a) (by rw [hvl, hul]) (dd a) (hdd a)
  obtain ⟨L, hfin, hL, haff, hPL, d, hd⟩ := cechData x₀ P m hm.1.w e dd (fun a => (he a).1) hcomp D M hKS
  have hI : LBIso P₀.L (L.pull m) :=
    LBIso.trans P₀.isLB (pull_isLB P.isLB m) (pull_isLB hL m) (GlobalTheory.PolBaseChange.lbIso_refl P₀.isLB)
      (hPL.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ _ _ rfl) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ _ _ rfl))
  obtain ⟨⟨φ, hφ⟩, hφ'⟩ := GlobalTheory.KS.DlogPol.dlog_independent K P₀ g v dd hv hdd _ m L hL hI
  obtain ⟨Θ', hsy, hΘ'⟩ := GlobalTheory.KS.Sym.exists_symm_of_ksCoc GlobalTheory.allSixLaws.1 GlobalTheory.allSixLaws.2.1
    GlobalTheory.Moduli.cube_of_isLB K P₀ g v dd hv hdd R x₀ P m L _ d _ φ hm hL haff hI (hd φ hφ) hφ
  have e1 : Θ' = -M.map x₀ := by
    rw [eq_comm, ← sub_eq_zero]
    funext b
    refine (hφ' φ hφ).2 _ ?_
    rw [GlobalTheory.LogKSBal.lc_sub]
    exact hΘ' b
  have h1 : (M.map x₀)ᵀ = M.map x₀ := by
    have h : Θ'ᵀ = Θ' := hsy
    rwa [e1, Matrix.transpose_neg, neg_inj] at h
  ext a b
  have := congrFun (congrFun h1 a) b
  simp only [Matrix.transpose_apply, Matrix.map_apply] at this
  exact IsFractionRing.injective R K this

end GlobalTheory.KSRelSymm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerRelationZeroDerivationOfShiftedStatement
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kodairaSpencer_relation_zero_derivation_of_shifted : ∀ (K : Type) [Field K] [CharZero K] (P₀ : Out.PolAV (Sp K)) (n : ℕ) (v : Module.Basis (Fin n) K (TanM (𝟙 (Sp K)) P₀.A)) (dd : Fin n → Fld P₀.A.left), (∀ a, IsInv P₀.A (v a) (dd a)) → ∀ (F : Type) [Field F] (ψ : K →+* F) (ξ : Sp F ⟶ P₀.A.left), ξ ≫ P₀.A.hom = spMap ψ → (∀ O (f : Γ(P₀.A.left, O)), ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O f = 0 → f = 0) → ∀ (δ : Fin n → Derivation ℤ F F), (∀ a O f, ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O (dd a O f) = δ a (valR ξ O f)) → ∀ (j₀ : P₀.L.ι), ⊤ ≤ ξ ⁻¹ᵁ P₀.L.U j₀ → ∀ (δ₀ : Derivation ℤ F F) (lam : Matrix (Fin n) (Fin n) K), lamᵀ = lam → (∀ r, δ₀ (ψ r) = 0) → ∀ (k : ℕ), 1 ≤ k → ∀ (I : Type) (s : I → SecM (𝟙 P₀.A.left) P₀.L k), ⨆ i, Out.nonzeroLocus (s i) = ⊤ → (∀ i, IsAffineOpen (Out.nonzeroLocus (s i))) → (∀ i, ⊤ ≤ ξ ⁻¹ᵁ Out.nonzeroLocus (s i)) → (∀ i, (∀ f : Γ(P₀.A.left, (Out.nonzeroLocus (s i))), ∃ f' : Γ(P₀.A.left, (Out.nonzeroLocus (s i))), valR ξ _ f' = (k : F) * δ₀ (valR ξ _ f) - ∑ a, ∑ e, ψ (lam a e) * (δ a (valR ξ _ ((s i).f fun _ => j₀)) / valR ξ _ ((s i).f fun _ => j₀)) * δ e (valR ξ _ f))) → KSRel P₀.A (𝟙 P₀.A.left) P₀.L dd (fun _ => 0) lam := by
  first | exact @GlobalTheory.Heat.ZeroKS.ksRel_zero | exact GlobalTheory.Heat.ZeroKS.ksRel_zero | (intros; apply GlobalTheory.Heat.ZeroKS.ksRel_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeastIntCombinationMinimiserCellUnitaryStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.least_intCombination_minimiserCell_unitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (φ : InvFun (𝓞 E)), IsPolFan H.bar q φ → ∀ (N : ℕ) [NeZero N], 3 ≤ N → Odd N → ∃ (B ι : ℕ) (𝓛 : ∀ n : ℕ, Finset (Finset ((Fin n → ZMod N) → ℤ))), 1 ≤ ι ∧ ∀ (n : ℕ) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ (eb : X ≃ₗ[ℤ] (Fin n → ℤ)), n < B ∧ ∀ (b : LinearMap.BilinForm ℤ X), b ∈ balForms H.bar X → (∀ y, y ≠ 0 → 0 < b y y) → ∀ μ : (Fin n → ZMod N) → X, (∀ cl i, ((eb (μ cl) i : ℤ) : ZMod N) = cl i) → (∀ cl (α : X), (∀ i, ((eb α i : ℤ) : ZMod N) = cl i) → b (μ cl) (μ cl) ≤ b α α) → ∃ L ∈ 𝓛 n, ∀ b' : LinearMap.BilinForm ℤ X, b' ∈ balForms H.bar X → (∀ y, 0 ≤ b' y y) → (∀ cl (α : X), (∀ i, ((eb α i : ℤ) : ZMod N) = cl i) → b' (μ cl) (μ cl) ≤ b' α α) → (∀ ν ∈ L, (ι : ℝ) * φ.evalZ b' ≤ ∑ cl, (ν cl : ℝ) * b' (μ cl) (μ cl)) ∧ ∃ ν ∈ L, (ι : ℝ) * φ.evalZ b' = ∑ cl, (ν cl : ℝ) * b' (μ cl) (μ cl) := by
  first | exact @GlobalTheory.UPoinc.finite_types_unitary | exact GlobalTheory.UPoinc.finite_types_unitary | (intros; apply GlobalTheory.UPoinc.finite_types_unitary <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelSectionsFormulasOfIdempotentImagePullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.ZRelLevs

theorem zrel_levs : ∀ (h h' M : ℕ) (O : Type) [Ring O] (e : O) (jl : (Fin h ⊕ Fin h → ℤ) →+ (Fin h' ⊕ Fin h' → ℤ)) (n : ℕ) (o : Fin n → O) (κ : Fin n → (Fin h' ⊕ Fin h' → ℤ) →+ (Fin h ⊕ Fin h → ℤ)) (S' T : Scheme.{0}) (t : S' ⟶ Sp (cycAway M)) (z : SiegPre h' M (zetaAway M) t) (act : O → (z.A ⟶ z.A)) (g : T ⟶ S') (c' : SiegPre h M (zetaAway M) (g ≫ t)) (w' : SiegPre h' M (zetaAway M) (g ≫ t)) (actw' : O → (w'.A ⟶ w'.A)), ActPB w' actw' z act g → ZRel e jl o κ c' w' actw' → (∀ a, g ≫ (z.lev (jl a) ≫ act e).left = g ≫ (z.lev (jl a)).left) ∧ ∀ a, g ≫ (z.lev a).left = g ≫ ((List.ofFn fun k => z.lev (jl (κ k a)) ≫ act (o k)).prod).left := by
  intro h h' M O _ e jl n o κ S' T t z act g c' w' actw' hpb hz
  obtain ⟨φ, φ₂, hφ, -, -, hl, ha⟩ := hpb
  obtain ⟨inc, pr, -, -, hip, hpi, -, hc, hw⟩ := hz
  have key : ∀ b (oo : O), (w'.lev b ≫ actw' oo).left ≫ φ = g ≫ (z.lev b ≫ act oo).left := by
    intro b oo
    rw [Over.comp_left, Over.comp_left, Category.assoc, ha, ← Category.assoc, hl, Category.assoc]
  refine ⟨fun a => ?_, fun a => ?_⟩
  · rw [← key, ← hl]
    congr 2
    rw [← hc, Category.assoc, ← hpi, ← Category.assoc inc, hip, Category.id_comp]
  · rw [← hl, hw a]
    have e1 : ((List.ofFn fun k => c'.lev (κ k a) ≫ inc ≫ actw' (o k)).prod).left ≫ φ =
        (pushHom hφ (𝟙_ (Over T)) (List.ofFn fun k => c'.lev (κ k a) ≫ inc ≫ actw' (o k)).prod).left := rfl
    rw [e1, map_list_prod, List.map_ofFn]
    have e2 : g ≫ ((List.ofFn fun k => z.lev (jl (κ k a)) ≫ act (o k)).prod).left =
        (toUnit (Over.mk ((𝟙_ (Over T)).hom ≫ g)) ≫
          (List.ofFn fun k => z.lev (jl (κ k a)) ≫ act (o k)).prod).left := by
      rw [Over.comp_left, Over.toUnit_left]
      rfl
    rw [e2, GlobalTheory.comp_list_prod_ofFn]
    congr 3
    funext k
    apply Over.OverMorphism.ext
    show (c'.lev (κ k a) ≫ inc ≫ actw' (o k)).left ≫ φ = _
    rw [← Category.assoc, hc, key]
    simp only [Over.comp_left, Over.toUnit_left, Over.mk_hom]
    rfl

end GlobalTheory.ZRelLevs
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieSurjModP
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.QLog

theorem lie_surj_mod_p : ∀ (p : ℕ) [Fact p.Prime] (O E : Type) [CommRing O] [CommRing E] [Algebra O E],
    IsFrame p E (RingHom.id O) → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d),
    ∀ l : G.dual.Lie, ∃ (f : MvPowerSeries (Fin d) E) (l' l'' : G.dual.Lie),
      QL c.μ ⊤ f ∧ c.IsLie f l' ∧ l = l' + (p : O) • l'' := by
  intro p _ O E _ _ _ hF G d c l
  obtain ⟨b, z, hbz, hl⟩ := GlobalTheory.T.dual_lie_exists_additive_eval_mod_prime_pow p O G l 1
  rw [pow_one] at hbz
  obtain ⟨f, s, y, hf, hs, hy⟩ := GlobalTheory.T.additive_mod_prime_eq_quasiLogarithm_defect p O E hF G d c b z hbz
  obtain ⟨l', hl', -⟩ := GlobalTheory.T.existsUnique_isLie_of_isFrame_of_QL p O E hF G d c f hf
  have hdiv : ∀ w : G.dual.omega, (p : O) ∣ (l - l') w := by
    intro w
    obtain ⟨φ, hφ⟩ := AugCot.d_surjective _ (w.1 1)
    have h1 := hl w φ hφ
    have h2 := hl'.2 1 w φ s hφ (by rw [pow_one]; exact hs)
    rw [pow_one] at h1 h2
    rw [hy, map_add, map_smul, smul_eq_mul] at h2
    have h3 : (p : O) ∣ l' w - φ b := by
      have := dvd_add h2 (dvd_mul_right (p : O) (φ y))
      rwa [show l' w - (φ b + (p : O) * φ y) + (p : O) * φ y = l' w - φ b by ring] at this
    have := dvd_sub h1 h3
    rwa [show l w - φ b - (l' w - φ b) = (l - l') w by simp] at this
  obtain ⟨l'', hl''⟩ := GlobalTheory.T.dual_eq_smul_of_forall_dvd' O G.dual.omega (p : O) (fun x hx => hF.sat x hx) (l - l') hdiv
  exact ⟨f, l', l'', hf, hl', by rw [← hl'']; abel⟩

end GlobalTheory.QLog
end

