import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2908
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2306
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2654
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2650
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1167
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1241
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1224
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1247
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1230
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1266
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1338
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2898
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2611
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0075
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0081
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2625
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2885
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2434
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2811
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TxFrameTranslate
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0031
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0567
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2838
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0046
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2944
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2764
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2843
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2909
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0084
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalTatePairsUnitaryTypeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_tate_pairs_unitaryType : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dm : Datum H) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F), Function.Injective β → ∀ (T : Formalism.L2.Pj.CDVR) (b : O →+* T.V), Function.Injective b → ∀ (D : DegData T.V (maximalIdeal T.V)) [Module (𝓞 E) D.toPre.X] (o : letI := H.starRing; D.toPre.OAct (𝓞 E)), PelOK Dm D.toPre o → (∀ k : ℕ, k ∣ l.M' → ∀ q : QkPt D.toPre (AlgebraicClosure (FractionRing T.V)) k, ∃ p : QkPt D.toPre (FractionRing T.V) k, QkExt (algebraMap (FractionRing T.V) (AlgebraicClosure (FractionRing T.V))) p q) → ∃ (pA : Dm.La → QkPt D.toPre (FractionRing T.V) l.A) (pM : Dm.La → QkPt D.toPre (FractionRing T.V) l.M), ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing T.V) F] (z : O), ((β z : c.F) : ℂ) = zeta l.A → ∃ I : (letI := H.starRing; TateIsoQ Dm D.toPre o F), (I.ζ l.A : F) = algebraMap (FractionRing T.V) F (algebraMap T.V _ (b z)) ∧ (∀ a q, QkExt (algebraMap _ F) (pA a) q → QkPt.Equiv D.toPre F q (I.ev l.A a)) ∧ ∀ a q, QkExt (algebraMap _ F) (pM a) q → QkPt.Equiv D.toPre F q (I.ev l.M a) := by
  first | exact @GlobalTheory.TraitTate.exists_tate | exact GlobalTheory.TraitTate.exists_tate | (intros; apply GlobalTheory.TraitTate.exists_tate <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRegularLocalModelGraphOfPlace
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct

set_option autoImplicit false

theorem GlobalTheory.GraphLocal.exists_locModel_graph : ∀ {K κ κ' L : Type} [Field K] [Field κ] [Field κ'] [Field L] [Algebra ℂ K] [Algebra ℂ κ] [Algebra ℂ κ'] [Algebra ℂ L]
    [Algebra (K ⊗[ℂ] κ') L] [IsScalarTower ℂ (K ⊗[ℂ] κ') L] [IsFractionRing (K ⊗[ℂ] κ') L]
    (n k k' : ℕ) (x : Fin n → K) (τ' : Fin k' → κ') (R : Subring K) (π : R →+* κ) (ρ : κ →ₐ[ℂ] κ'),
  TrBasis (algebraMap ℂ K) x → TrBasis (algebraMap ℂ κ') τ' → (∃ O' : Subring κ', IsLocModel (algebraMap ℂ κ') O') → (∃ z : Fin k → κ, TrBasis (algebraMap ℂ κ) z) →
  (∀ a (h : algebraMap ℂ K a ∈ R), π ⟨algebraMap ℂ K a, h⟩ = algebraMap ℂ κ a) →
  (∀ a, algebraMap ℂ K a ∈ R) →
  (∀ f : κ, ∃ a b : R, π b ≠ 0 ∧ f * π b = π a) →
  ∀ (E : Place (algebraMap ℂ K)), E.Contains R → (∀ r : R, (r : K) ≠ 0 → (π r = 0 ↔ 0 < E.ord r)) →
  ∃ (Q : Subring L) (hQ : IsLocModel (algebraMap ℂ L) Q), letI := hQ.isLocalRing; ∃ z : Fin (k + 1) → Q,
    IsLocalRing.maximalIdeal Q = Ideal.span (Set.range z) ∧ ringKrullDim Q = k + 1 ∧
    (∀ e ∈ E.ring, algebraMap (K ⊗[ℂ] κ') L (e ⊗ₜ 1) ∈ Q) ∧
    (∀ g : K, g ≠ 0 → ∃ q : Q, IsUnit q ∧ algebraMap (K ⊗[ℂ] κ') L (g ⊗ₜ 1) = q * (z 0 : L) ^ E.ord g) ∧
    (∀ b : κ', b ≠ 0 → ∃ q : Q, IsUnit q ∧ (q : L) = algebraMap (K ⊗[ℂ] κ') L (1 ⊗ₜ b)) ∧
    (∀ (l : ℕ) (a : Fin l → R) (b : Fin l → κ'), ∑ i, ρ (π (a i)) * b i ≠ 0 →
      ∃ q : Q, IsUnit q ∧ (q : L) = (fun (l : ℕ) (a : Fin l → R) (b : Fin l → κ') => ∑ i, algebraMap (K ⊗[ℂ] κ') L ((a i : K) ⊗ₜ b i)) l a b) ∧
    (∀ (M l : ℕ) (a : Fin l → R) (b : Fin l → κ'), ∑ i, π (a i) ⊗ₜ[ℂ] b i ∈ (RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ'))) ^ M →
      ∃ q : Q, (q : L) = (fun (l : ℕ) (a : Fin l → R) (b : Fin l → κ') => ∑ i, algebraMap (K ⊗[ℂ] κ') L ((a i : K) ⊗ₜ b i)) l a b ∧ q ∈ IsLocalRing.maximalIdeal Q ^ M ⊔ Ideal.span {z 0}) ∧
    ∃ (y : Fin (k' + n) → Q) (q : Q), IsFreeGen Q (dForm ((algebraMap ℂ L).codRestrict Q hQ.const_mem) y) ∧ IsUnit q ∧
      dForm (algebraMap ℂ L) (Fin.append (fun i => algebraMap (K ⊗[ℂ] κ') L (1 ⊗ₜ τ' i))
        (fun i => algebraMap (K ⊗[ℂ] κ') L (x i ⊗ₜ 1))) =
        ((q : L) * (z 0 : L) ^ E.formOrd (dForm (algebraMap ℂ K) x)) • dForm (algebraMap ℂ L) (fun i => (y i : L)) := by
  intro K κ κ' L _ _ _ _ _ _ _ _ _ _ _ n k k' x τ' R π ρ hx hτ hO' hz hcompat hC hfrac E hER hcentre
  have hinj : Function.Injective (algebraMap (K ⊗[ℂ] κ') L) := IsFractionRing.injective _ _
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible E.ring
  obtain ⟨zR, hzR⟩ := GlobalTheory.T.exists_trBasis_in_image_of_fractionField k R π hfrac hz
  obtain ⟨𝔭, h𝔭⟩ := Ideal.nonempty_minimalPrimes (GlobalTheory.T.placeGraphIdealTensor_ne_top (κ' := κ') R π ρ E hcompat hC hfrac hER hcentre)
  haveI : 𝔭.IsPrime := h𝔭.1.1
  have hle : graphIdeal E R π ρ ≤ 𝔭 := h𝔭.1.2
  have hQ : IsLocModel (algebraMap ℂ L) (locAt (L := L) 𝔭) := GlobalTheory.T.isLocalRingOfVarietyPoint_localization_placeTensor E 𝔭 hO'
  letI := hQ.isLocalRing
  have hmax := GlobalTheory.T.graphIdeal_localization_maximalIdeal_eq_span (L := L) k R π ρ E hER t zR 𝔭 hO' hcompat hC hfrac hcentre ht hzR h𝔭
  have hdim := GlobalTheory.T.ringKrullDim_localization_graphIdeal_minimalPrime (L := L) k R π ρ E 𝔭 hO' hcompat hC hfrac hER hcentre hz h𝔭
  have hz0 : ((toQ (L := L) 𝔭 (gens E R π ρ hER t zR 0) : locAt (L := L) 𝔭) : L) =
      algebraMap (K ⊗[ℂ] κ') L ((t : K) ⊗ₜ 1) := by
    simp [gens]
  refine ⟨locAt (L := L) 𝔭, hQ, fun i => toQ 𝔭 (gens E R π ρ hER t zR i), hmax, hdim, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e he
    exact (toQ (L := L) 𝔭 ⟨e ⊗ₜ 1, tmul_mem (A := placeAlg E) he 1⟩).2
  · intro g hg
    rw [hz0]
    exact GlobalTheory.T.exists_isUnit_mul_zpow_uniformiser_tmul E 𝔭 t hinj ht g hg
  · intro b hb
    refine ⟨toQ 𝔭 ⟨1 ⊗ₜ b, tmul_mem (one_mem (placeAlg E)) b⟩, isUnit_toQ 𝔭 hinj ?_, rfl⟩
    intro h
    apply one_notMem 𝔭
    have h2 := 𝔭.mul_mem_right ⟨(1 : K) ⊗ₜ b⁻¹, tmul_mem (one_mem (placeAlg E)) b⁻¹⟩ h
    convert h2 using 1
    apply Subtype.ext
    simp [Algebra.TensorProduct.tmul_mul_tmul, mul_inv_cancel₀ hb, Algebra.TensorProduct.one_def]
  · intro l a b hs
    have hw : ∑ i, (a i : K) ⊗ₜ[ℂ] b i ∈ tens (κ' := κ') (placeAlg E) :=
      Subalgebra.sum_mem _ fun i _ => tmul_mem (hER _ (a i).2) (b i)
    refine ⟨toQ 𝔭 ⟨_, hw⟩, isUnit_toQ 𝔭 hinj (GlobalTheory.T.sum_tmul_notMem_prime_of_graph_image_ne_zero R π ρ E 𝔭 hle hER l a b ⟨_, hw⟩ rfl hs), ?_⟩
    simp [map_sum]
  · intro M l a b hJ
    have hw : ∑ i, (a i : K) ⊗ₜ[ℂ] b i ∈ tens (κ' := κ') (placeAlg E) :=
      Subalgebra.sum_mem _ fun i _ => tmul_mem (hER _ (a i).2) (b i)
    refine ⟨toQ 𝔭 ⟨_, hw⟩, by simp [map_sum], ?_⟩
    have h1 := GlobalTheory.T.graphJets_mem_pow_sup_uniformiser R π ρ E 𝔭 t hle ht hcompat hC hfrac hER hcentre M l a b ⟨_, hw⟩ rfl hJ
    have h2 := Ideal.mem_map_of_mem (toQ (L := L) 𝔭) h1
    rw [Ideal.map_sup, Ideal.map_pow, Ideal.map_span, Set.image_singleton] at h2
    have h3 : Ideal.map (toQ (L := L) 𝔭) 𝔭 ^ M ⊔ Ideal.span {toQ (L := L) 𝔭 ⟨(t : K) ⊗ₜ 1, tmul_mem t.2 1⟩} ≤
        IsLocalRing.maximalIdeal (locAt (L := L) 𝔭) ^ M ⊔
          Ideal.span {toQ (L := L) 𝔭 (gens E R π ρ hER t zR 0)} :=
      sup_le_sup (Ideal.pow_right_mono (map_le_maximalIdeal 𝔭 hinj) M) le_rfl
    exact h3 h2
  · obtain ⟨y, q, hy, hq, e⟩ := GlobalTheory.T.exists_freeGenerator_topForms_tensorLocalization_order n k' x τ' E 𝔭 t hQ.const_mem hx hτ hO' ht
    refine ⟨y, q, hy, hq, ?_⟩
    rw [hz0]
    exact e
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRescaleIsPullDeg
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.PreLift

open GlobalTheory.ArcPull GlobalTheory.ArcQ

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

theorem exists_rescale_isPullDeg {i : R →+* R'} (D : DegPre R) (D' : DegPre R')
    {W : (Sp R).Opens} (ψW : PsiOn D W) (g : (TK R').left ⟶ (TW W).left) (hg : g ≫ W.ι = jK R' ≫ specOf i)
    {Φ : D'.P.A.left ⟶ D.P.A.left} (gp : IsGrpPullback D'.P.A D.P.A (spMap i) Φ)
    (w : LB.Iso D'.P.L (D.P.L.pull Φ)) (hw : PGen w)
    (hr : PMaps w (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => eSec D.P.A) (fun _ => 1) D'.rig D.rig (spMap i))
    (xe : D'.X ≃+ D.X) (hc : ∀ x, (D'.c x).left ≫ Φ = spMap i ≫ (D.c (xe x)).left) :
    ∃ (κ : D'.X → (FractionRing R')ˣ) (hD : IsPullDeg i D (GlobalTheory.PolDeg.rescale D' κ)), hD.W = W := by
  obtain ⟨e, e_hom, he⟩ := grpPullback_iso gp (isGrpPullback_pullback D.P.A (specOf i))
  subst he
  have hE : eSec D'.P.A ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) = specOf i ≫ eSec D.P.A :=
    (cubeMapOf gp).e_comm
  have hx : ∀ x, g ≫ (toUnit (TW W) ≫ D.c (xe x)).left =
      D'.xK x ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) := fun x => by
    show g ≫ W.ι ≫ (D.c (xe x)).left = (jK R' ≫ (D'.c x).left) ≫ _
    rw [Category.assoc, hc, ← Category.assoc, hg, Category.assoc]
  choose b hb vb using fun x => exists_gen D.P.isLB (K' := PUnit)
    (φ' := fun _ => D'.xK x ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i)) (ε' := fun _ => -1)
    (fun U _ h => Finset.prod_congr rfl fun _ _ => congrArg (fun q => h q ^ (-1 : ℤ)) (hx x))
    (LB.pullGen D.P.L _ _ (ψW.psi (xe x)) g) (DVR.pullGen_isGen _ _ _ _ (ψW.psi_gen _) g)
  choose psi hpsi vpsi using fun x => DegPull.exists_down_val hw D.P.isLB D'.P.isLB (K := PUnit)
    (φ' := fun _ => D'.xK x) (ε := fun _ => -1) (fun _ => rfl) (b x) (hb x)
  choose u hu using GlobalTheory.FieldPull.exists_psi_ratio D' psi hpsi
  refine ⟨fun x => (u x)⁻¹, ?_⟩
  have eψ : ∀ x, psi x = (GlobalTheory.PolDeg.rescale D' fun x => (u x)⁻¹).psi x := fun x =>
    GlobalTheory.TorusExt.gen_ext_val D'.P.isLB (hpsi x) ((GlobalTheory.PolDeg.rescale D' fun x => (u x)⁻¹).psi_gen x)
      fun y J' hJ' => by
        refine Eq.trans ?_ (GlobalTheory.UU.val_scaleGen _ _ _ hJ').symm
        have h1 : unitOn (u x)⁻¹ * unitOn (u x) = 1 := (map_mul _ _ _).symm.trans
          ((congrArg unitOn (inv_mul_cancel (u x))).trans (map_one _))
        rw [hu x y J' hJ', GlobalTheory.TauTwist.unitAt_apply, ← _root_.mul_assoc, ← map_mul]
        erw [h1]
        rw [map_one, _root_.one_mul]
  have key : ∀ x, GeneratorPullback.MapsAt D.P.L D'.P.L (J := PUnit)
      (fun _ => e.hom.left ≫ pullback.fst D.P.A.hom (specOf i)) w (D'.xK x) (-1) (psi x) (b x) := fun x jN jL => by
    refine unit_ext fun y hy => ?_
    have v := vpsi x _ (𝟙 _) y jN (fun _ => jL) (GeneratorPullback.mapsAt_le_b _ _ _ _ jN jL hy) (GeneratorPullback.mapsAt_le_a _ _ _ _ jN jL hy)
    refine (gm_res _ y _ hy _).trans (v.trans (Eq.symm ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_
      (gm_res _ y _ hy _)))))
    rw [pw, Fintype.prod_unique]
    exact (map_zpow _ _ _).trans (congrArg (· ^ (-1 : ℤ)) (gm_pull (𝟙 _) _ y _ hy _))
  refine ⟨⟨e, e_hom, w, (isGen_iff w).2 hw, hE, ?_, xe, hc, W, ψW, g, hg, fun x => ⟨b x, eψ x ▸ key x,
      corr_of_val D.P.isLB fun y J hJ => vb x _ _ y J hJ⟩⟩, rfl⟩
  exact (maps_iff w _ (fun _ => eSec D.P.A) _ D'.rig D.rig (specOf i) _
    (rigPull_le (G' := D'.P.A) (G := D.P.A) _ (specOf i) hE D.P.L) (fun _ => rfl)).2 hr

end GlobalTheory.PreLift

namespace GlobalTheory.PreLift

theorem exists_lift_c (R₁ R : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] [IsNoetherianRing R₁] [CommRing R]
    [IsDomain R] [IsLocalRing R] (hR₁ : IsAdicComplete (maximalIdeal R₁) R₁) (π : R₁ →+* R)
    (hπ : Function.Surjective π) (D : DegPre R) (P : PolAV (Sp R₁)) (i : D.P.A.left ⟶ P.A.left)
    (gp : IsGrpPullback D.P.A P.A (spMap π) i) :
    ∃ c : D.X → (𝟙_ (Over (Sp R₁)) ⟶ P.A), (∀ a b, c (a + b) = padd P.A (c a) (c b)) ∧
      ∀ x, (D.c x).left ≫ i = spMap π ≫ (c x).left := by
  letI := P.isAb.comm
  haveI := P.smoothDim
  have hsm : Smooth P.A.hom := SmoothOfRelativeDimension.smooth P.g P.A.hom
  have hx₀ : ∀ x, ((D.c x).left ≫ i) ≫ P.A.hom = spMap π := fun x => by
    rw [Category.assoc, gp.1.w, ← Category.assoc, Over.w]
    exact Category.id_comp _
  choose s hs₁ hs₂ using fun x => GlobalTheory.T.hensel_smooth_section_lift R₁ R hR₁ π hπ P.A hsm _ (hx₀ x)
  let sec : D.X → (𝟙_ (Over (Sp R₁)) ⟶ P.A) := fun x => Over.homMk (s x) (hs₁ x)
  let bs := Module.Free.chooseBasis ℤ D.X
  let f : D.X →ₗ[ℤ] Additive (𝟙_ (Over (Sp R₁)) ⟶ P.A) := bs.constr ℤ fun j => Additive.ofMul (sec (bs j))
  refine ⟨fun x => (f x).toMul, fun a b => ?_, ?_⟩
  · show Additive.toMul (f (a + b)) = _
    rw [map_add]; rfl
  let T := 𝟙_ (Over (Sp R))
  let q : Over.mk (T.hom ≫ spMap π) ⟶ 𝟙_ (Over (Sp R₁)) := Over.homMk (spMap π) (by
    show spMap π ≫ 𝟙 _ = 𝟙 _ ≫ spMap π
    rw [Category.comp_id, Category.id_comp])
  let h₁ : D.X → (Over.mk (T.hom ≫ spMap π) ⟶ P.A) := fun x =>
    Over.homMk ((D.c x).left ≫ i) ((hx₀ x).trans (Category.id_comp _).symm)
  let F₁ : D.X →+ Additive (Over.mk (T.hom ≫ spMap π) ⟶ P.A) :=
    AddMonoidHom.mk' (fun x => Additive.ofMul (h₁ x)) fun a b => by
      show h₁ (a + b) = h₁ a * h₁ b
      refine Over.OverMorphism.ext ?_
      rw [gp.2 T (D.c a) (D.c b) _ _ rfl rfl]
      show (D.c (a + b)).left ≫ i = _
      rw [D.c_add]
      rfl
  let F₂ : D.X →+ Additive (Over.mk (T.hom ≫ spMap π) ⟶ P.A) :=
    AddMonoidHom.mk' (fun x => Additive.ofMul (q ≫ (f x).toMul)) fun a b => by
      show q ≫ Additive.toMul (f (a + b)) = (q ≫ Additive.toMul (f a)) * (q ≫ Additive.toMul (f b))
      rw [map_add, toMul_add, MonObj.comp_mul]
  have hF : F₁ = F₂ := by
    refine AddMonoidHom.toIntLinearMap_injective (bs.ext fun j => ?_)
    show Additive.ofMul (h₁ (bs j)) = Additive.ofMul (q ≫ Additive.toMul (f (bs j)))
    have e : f (bs j) = Additive.ofMul (sec (bs j)) := bs.constr_basis ℤ _ j
    rw [e]
    refine congrArg Additive.ofMul (Over.OverMorphism.ext ?_)
    exact (hs₂ (bs j)).symm
  intro x
  have := congrArg (fun φ => (Additive.toMul (φ x)).left) hF
  exact this

end GlobalTheory.PreLift

namespace GlobalTheory.PreLift

open GlobalTheory.ArcPull GlobalTheory.ArcQ

theorem prelift : ∀ (R₁ R : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] [IsNoetherianRing R₁] [CommRing R] [IsDomain R] [IsLocalRing R], IsAdicComplete (maximalIdeal R₁) R₁ → ∀ π : R₁ →+* R, Function.Surjective π → ∀ (D : DegPre R) (P : PolAV (Sp R₁)) (i : D.P.A.left ⟶ P.A.left), IsGrpPullback D.P.A P.A (spMap π) i → LBIso D.P.L (P.L.pull i) → ∃ (D₁ : DegPre R₁) (κ : D.X → (FractionRing R)ˣ) (h : IsPullDeg π D₁ (GlobalTheory.PolDeg.rescale D κ)), h.W = ⊤ ∧ D₁.PsiEven ∧ D₁.TauBimult := by
  intro R₁ R _ _ _ _ _ _ _ hR₁ π hπ D P i gp hL
  obtain ⟨rig, hrig⟩ := P.rigid
  obtain ⟨cub⟩ := (GlobalTheory.T.all_six_abelian_scheme_laws_hold.1.cube _ P ⟨P.L, rig, P.isLB, hrig⟩ rfl).1
  obtain ⟨sym, hsym, hsr⟩ := GlobalTheory.SelfUnif.exists_sym P
  obtain ⟨c, cadd, hc⟩ := exists_lift_c R₁ R hR₁ π hπ D P i gp
  choose psi hpsi using fun x : D.X => GlobalTheory.SS.HtForm.gen_field _
    (DVR.linComb_isLB P.L P.isLB (K := PUnit) (fun _ => ptK (c x)) (fun _ => -1))
  let E : DegPre R₁ :=
    { P := P, rig := rig, rig_gen := hrig, cub := cub, sym := sym, sym_gen := hsym, sym_rig := hsr, X := D.X,
      c := c, c_add := cadd, psi := psi, psi_gen := hpsi }
  obtain ⟨g, hev, htb, ⟨ψW⟩⟩ := GlobalTheory.T.degeneration_rescale_even_bimult_exists R₁ E
  obtain ⟨w₀, hw₀⟩ := hL
  have he : eSec D.P.A ≫ i = spMap π ≫ eSec P.A := (cubeMapOf gp).e_comm
  have hσ : eSec D.P.A ≫ D.P.A.hom = 𝟙 _ := Over.w η[D.P.A]
  obtain ⟨w, hw, hr⟩ := GlobalTheory.UnifPreCompare.exists_rigidified P.isLB D.P.isLB D.P.A.hom (eSec D.P.A) hσ w₀ hw₀
    D.rig D.rig_gen (φ := eSec P.A) rig hrig (spMap π) he
  let gg : (TK R).left ⟶ (TW (⊤ : (Sp R₁).Opens)).left := (jK R ≫ specOf π) ≫ (Sp R₁).topIso.inv
  have hg : gg ≫ (⊤ : (Sp R₁).Opens).ι = jK R ≫ specOf π := by
    rw [Category.assoc, ← Scheme.topIso_hom, Iso.inv_hom_id, Category.comp_id]
  obtain ⟨κ, hD, hW⟩ := exists_rescale_isPullDeg (i := π) (GlobalTheory.PolDeg.rescale E g) D ψW gg hg (Φ := i) gp w
    ((isGen_iff w).1 hw) hr (AddEquiv.refl _) hc
  exact ⟨GlobalTheory.PolDeg.rescale E g, κ, hD, hW, hev, htb⟩

end GlobalTheory.PreLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRetractionDifferentialsInvariantOneFormsAfStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_retraction_differentials_invariantOneForms_affine : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ U : AffOp A.left, ∃ r : Ω[Sec A.hom U.unop.1⁄R] →ₗ[Sec A.hom U.unop.1] (Sec A.hom U.unop.1 ⊗[R] GlobalTheory.InvForm.InvForm A), ∀ w : GlobalTheory.InvForm.InvForm A, r (evForm A.hom U w.1) = 1 ⊗ₜ w := by
  first | exact @GlobalTheory.InvFormRetract.retract | exact GlobalTheory.InvFormRetract.retract | (intros; apply GlobalTheory.InvFormRetract.retract <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRigidificationMatchingFramesTorsionFramesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rigidification_matchingFrames_torsionFrames : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ), ∀ (x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)) (fr : ∀ a, FrAt (x a)), (∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) → (∀ a, (fr a).IsGen ∧ ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' → Geo.Tor.gw 𝔪.wl (x a).left z (J ((x a).left ≫ 𝔪.φ)) (J' (x a).left) * val (fr a) (𝟙 _) z J' = val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J) → ∃ ρA : LB.Gen (𝔪.A.L.pull (eSec 𝔪.A.A)), ρA.IsGen ∧ ∀ a, IsTorsFrame 𝔪.A ρA (X₁.S.r * X₁.S.N) (x a) (fr a) := by
  first | exact @GlobalTheory.Poinc.IntTerm.exists_rig_torsFrame_of_match | exact GlobalTheory.Poinc.IntTerm.exists_rig_torsFrame_of_match | (intros; apply GlobalTheory.Poinc.IntTerm.exists_rig_torsFrame_of_match <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRigidifiedTranslatedBundleIsoPsiZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumCmp.Norm

section General

variable {X X' S : Scheme.{0}} {L : LB X} {L' : LB X'}

theorem exists_iso (hL : L.IsLB) (hL' : L'.IsLB) (p : X' ⟶ S) (e' : S ⟶ X') (he : e' ≫ p = 𝟙 S) (Φ : X' ⟶ X)
    (e : S ⟶ X) (ρ' : LB.Gen (L'.pull e')) (hρ' : ρ'.IsGen) (ρ : LB.Gen (L.pull e)) (hρ : ρ.IsGen)
    (w₀ : LB.Iso L' (L.pull Φ)) (hw₀ : w₀.IsGen) :
    ∃ w : LB.Iso L' (LB.LinComb L ![Φ, p ≫ e' ≫ Φ, p ≫ e] twε), w.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ S) (z : Z) (j : Fin 3 → L.ι) (q : L'.ι),
        e' (r z) ∈ LB.wchart L ![Φ, p ≫ e' ≫ Φ, p ≫ e] j → e' (r z) ∈ L'.U q →
        gv w (r ≫ e') z j q = gm ((r ≫ e') ≫ Φ) z (L.U (j 0) ⊓ L.U (j 1)) (L.g (j 0) (j 1)) *
          gm r z (LB.wchart L (fun _ : PUnit => e) (fun _ => j 2)) (ρ.s (fun _ => j 2)) *
          (gm r z (LB.wchart L' (fun _ : PUnit => e') (fun _ => q)) (ρ'.s (fun _ => q)))⁻¹ := by
  have hw := (isGen_iff w₀).1 hw₀
  obtain ⟨u, hu, vu⟩ := exists_up hw hL hL' (K := PUnit) (φ' := fun _ => e') (ε := fun _ => 1) ρ' hρ'
  have l₀ : ∀ (j : Fin 3 → L.ι) (q : L'.ι), LB.wchart L ![Φ, p ≫ e' ≫ Φ, p ≫ e] j ⊓ L'.U q ≤
      (L.pull Φ).U (fun _ => j 0) ⊓ L'.U q := fun j q x hx => ⟨mem_pull.2 (Set.mem_iInter.1 hx.1 0), hx.2⟩
  have l₁ : ∀ (j : Fin 3 → L.ι) (q : L'.ι), LB.wchart L ![Φ, p ≫ e' ≫ Φ, p ≫ e] j ⊓ L'.U q ≤
      p ⁻¹ᵁ LB.wchart L (fun _ : PUnit => e' ≫ Φ) (fun _ => j 1) := fun j q x hx =>
    Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hx.1 1
  have l₂ : ∀ (j : Fin 3 → L.ι) (q : L'.ι), LB.wchart L ![Φ, p ≫ e' ≫ Φ, p ≫ e] j ⊓ L'.U q ≤
      p ⁻¹ᵁ LB.wchart L (fun _ : PUnit => e) (fun _ => j 2) := fun j q x hx =>
    Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hx.1 2
  let w : LB.Iso L' (LB.LinComb L ![Φ, p ≫ e' ≫ Φ, p ≫ e] twε) :=
    ⟨fun c => res (l₀ c.1 c.2) (w₀.s (fun _ => c.1 0, c.2)) *
      (res (l₁ c.1 c.2) (pullU p _ (u.s (fun _ => c.1 1))))⁻¹ * res (l₂ c.1 c.2) (pullU p _ (ρ.s (fun _ => c.1 2)))⟩
  have vw : ∀ (Z : Scheme.{0}) (f : Z ⟶ X') (z : Z) (j : Fin 3 → L.ι) (q : L'.ι),
      f z ∈ LB.wchart L ![Φ, p ≫ e' ≫ Φ, p ≫ e] j ⊓ L'.U q →
      gm f z (LB.wchart L ![Φ, p ≫ e' ≫ Φ, p ≫ e] j ⊓ L'.U q) (w.s (j, q)) = gw w₀ f z (j 0) q *
        (gm (f ≫ p) z (LB.wchart L (fun _ : PUnit => e' ≫ Φ) (fun _ => j 1)) (u.s (fun _ => j 1)))⁻¹ *
        gm (f ≫ p) z (LB.wchart L (fun _ : PUnit => e) (fun _ => j 2)) (ρ.s (fun _ => j 2)) := fun Z f z j q hz =>
    (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res f z (l₀ j q) hz _)
      ((map_inv _ _).trans (congrArg (·⁻¹) ((gm_res f z (l₁ j q) hz _).trans (gm_pull f p z _ (l₁ j q hz) _))))))
      ((gm_res f z (l₂ j q) hz _).trans (gm_pull f p z _ (l₂ j q hz) _)))
  refine ⟨w, ?_, fun Z r z j q hj hq => ?_⟩
  · rintro ⟨j, q⟩ ⟨j', q'⟩
    refine unit_ext fun x hx => ?_
    refine ((gm_res (𝟙 X') x _ hx _).trans (vw _ _ x j q hx.1)).trans (Eq.symm ((map_mul _ _ _).trans
      ((congrArg₂ (· * ·) ((gm_div L' _ (𝟙 X') x (j, q) (j', q') hx).trans
        (congrArg (· * _) (gm_linComb L _ twε (𝟙 X') x j j' hx.1.1 hx.2.1)))
        ((gm_res (𝟙 X') x _ hx _).trans (vw _ _ x j' q' hx.2))).trans ?_)))
    rw [hw _ (𝟙 X') x (j 0) (j' 0) q q' (Set.mem_iInter.1 hx.1.1 0) (Set.mem_iInter.1 hx.2.1 0) hx.1.2 hx.2.2,
      gen_trans hu (𝟙 X' ≫ p) x (l₁ j q hx.1) (l₁ j' q' hx.2), gen_trans hρ (𝟙 X' ≫ p) x (l₂ j q hx.1) (l₂ j' q' hx.2),
      Fin.prod_univ_three]
    simp only [trF, Fintype.prod_unique, twε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, zpow_one,
      zpow_neg, Category.assoc]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · have hp : (r ≫ e') ≫ p = r := by rw [Category.assoc, he, Category.comp_id]
    have hz : p (e' (r z)) = r z := congrArg (fun g => g z) hp
    have m₀ : Φ (e' (r z)) ∈ L.U (j 0) := Set.mem_iInter.1 hj 0
    have m₁ : Φ (e' (r z)) ∈ L.U (j 1) := by
      have : Φ (e' (p (e' (r z)))) ∈ L.U (j 1) := Set.mem_iInter.1 hj 1
      rwa [hz] at this
    refine (vw Z (r ≫ e') z j q ⟨hj, hq⟩).trans ?_
    rw [hp, vu Z r z (fun _ => j 1) (fun _ => q) (Set.mem_iInter.2 fun _ => m₁) (Set.mem_iInter.2 fun _ => hq),
      pw, Fintype.prod_unique, zpow_one, hw Z (r ≫ e') z (j 0) (j 1) q q m₀ m₁ hq hq, gm_self hL' (r ≫ e') z hq]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, inv_one, ofMul_one]
    abel

theorem exists_iso_maps (hL : L.IsLB) (hL' : L'.IsLB) (p : X' ⟶ S) (e' : S ⟶ X') (he : e' ≫ p = 𝟙 S) (Φ : X' ⟶ X)
    (b e : S ⟶ X) (hb : e' ≫ Φ = b) (ρ' : LB.Gen (L'.pull e')) (hρ' : ρ'.IsGen) (ρ : LB.Gen (L.pull e)) (hρ : ρ.IsGen)
    (w₀ : LB.Iso L' (L.pull Φ)) (hw₀ : w₀.IsGen) {Y : Scheme.{0}} (r : Y ⟶ S) (x : Y ⟶ X') (hx : x = r ≫ e')
    (a : LB.Gen (LB.LinComb L' (K := PUnit) (fun _ => x) (fun _ => -1)))
    (ha : ∀ (y : Y) (q : L'.ι), e' (r y) ∈ L'.U q →
      gm (𝟙 Y) y (LB.wchart L' (fun _ : PUnit => x) (fun _ => q)) (a.s (fun _ => q)) =
        (gm r y (LB.wchart L' (fun _ : PUnit => e') (fun _ => q)) (ρ'.s (fun _ => q)))⁻¹) :
    ∃ w : LB.Iso L' (LB.LinComb L ![Φ, p ≫ b, p ≫ e] twε), w.IsGen ∧
      ∃ t : LB.Gen (LB.LinComb L (fun i => x ≫ (![Φ, p ≫ b, p ≫ e] : Fin 3 → (X' ⟶ X)) i) (fun i => -1 * twε i)),
        MapsAtExp L L' ![Φ, p ≫ b, p ≫ e] twε w x (-1) a t ∧
        ∀ y J, Good L y J → val t (𝟙 Y) y J = (val ρ r y J)⁻¹ := by
  subst hb hx
  obtain ⟨w, hw, vw⟩ := exists_iso hL hL' p e' he Φ e ρ' hρ' ρ hρ w₀ hw₀
  have hp : (r ≫ e') ≫ p = r := by rw [Category.assoc, he, Category.comp_id]
  have hz : ∀ z, p (e' (r z)) = r z := fun z => congrArg (fun g => g z) hp
  have l₁ : ∀ j : Fin 3 → L.ι,
      LB.wchart L (fun i => (r ≫ e') ≫ (![Φ, p ≫ e' ≫ Φ, p ≫ e] : Fin 3 → (X' ⟶ X)) i) j ≤
        ((r ≫ e') ≫ Φ) ⁻¹ᵁ (L.U (j 0) ⊓ L.U (j 1)) := fun j y hy => ⟨Set.mem_iInter.1 hy 0, by
    have : Φ (e' (p (e' (r y)))) ∈ L.U (j 1) := Set.mem_iInter.1 hy 1
    rw [hz] at this
    exact this⟩
  have l₂ : ∀ j : Fin 3 → L.ι,
      LB.wchart L (fun i => (r ≫ e') ≫ (![Φ, p ≫ e' ≫ Φ, p ≫ e] : Fin 3 → (X' ⟶ X)) i) j ≤
        r ⁻¹ᵁ LB.wchart L (fun _ : PUnit => e) (fun _ => j 2) := fun j y hy => Set.mem_iInter.2 fun _ => by
    have : e (p (e' (r y))) ∈ L.U (j 2) := Set.mem_iInter.1 hy 2
    rw [hz] at this
    exact this
  let t : LB.Gen (LB.LinComb L (fun i => (r ≫ e') ≫ (![Φ, p ≫ e' ≫ Φ, p ≫ e] : Fin 3 → (X' ⟶ X)) i)
      (fun i => -1 * twε i)) :=
    ⟨fun j => (res (l₁ j) (pullU ((r ≫ e') ≫ Φ) (L.U (j 0) ⊓ L.U (j 1)) (L.g (j 0) (j 1))) * res (l₂ j) (pullU r _ (ρ.s (fun _ => j 2))))⁻¹⟩
  have vt : ∀ (y : Y) (j : Fin 3 → L.ι),
      y ∈ LB.wchart L (fun i => (r ≫ e') ≫ (![Φ, p ≫ e' ≫ Φ, p ≫ e] : Fin 3 → (X' ⟶ X)) i) j →
      gm (𝟙 Y) y (LB.wchart L (fun i => (r ≫ e') ≫ (![Φ, p ≫ e' ≫ Φ, p ≫ e] : Fin 3 → (X' ⟶ X)) i) j) (t.s j) =
        (gm ((r ≫ e') ≫ Φ) y (L.U (j 0) ⊓ L.U (j 1)) (L.g (j 0) (j 1)) *
          gm r y (LB.wchart L (fun _ : PUnit => e) (fun _ => j 2)) (ρ.s (fun _ => j 2)))⁻¹ := fun y j hy =>
    (map_inv _ _).trans (congrArg (·⁻¹) ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      ((gm_res (𝟙 Y) y (l₁ j) hy _).trans ((gm_pull (𝟙 Y) ((r ≫ e') ≫ Φ) y (L.U (j 0) ⊓ L.U (j 1)) (l₁ j hy) _).trans (by rw [Category.id_comp])))
      ((gm_res (𝟙 Y) y (l₂ j) hy _).trans ((gm_pull (𝟙 Y) r y _ (l₂ j hy) _).trans (by rw [Category.id_comp]))))))
  refine ⟨w, hw, t, fun j q => unit_ext fun y hy => ?_, fun y J hJ => ?_⟩
  · refine ((gm_res (𝟙 Y) y _ hy _).trans (vt y j (mapsAtExp_le_b L L' _ twε _ j q hy))).trans
      (Eq.symm ((map_mul _ _ _).trans ((congrArg₂ (· * ·) ((map_zpow _ _ _).trans (congrArg (· ^ (-1 : ℤ))
        ((gm_pull (𝟙 Y) (r ≫ e') y _ hy _).trans ((congrArg (fun f => gv w f y j q) (Category.id_comp _)).trans
          (vw Y r y j q hy.1 hy.2))))) ((gm_res (𝟙 Y) y _ hy _).trans (ha y q hy.2))).trans ?_)))
    rw [zpow_neg, zpow_one, ← mul_inv, inv_mul_cancel_right]
  · have e₁ : (r ≫ e') ≫ p ≫ e' ≫ Φ = (r ≫ e') ≫ Φ := by rw [← Category.assoc, hp, Category.assoc]
    have e₂ : (r ≫ e') ≫ p ≫ e = r ≫ e := by rw [← Category.assoc, hp]
    rw [val_of t (𝟙 Y) y J ![J ((r ≫ e') ≫ Φ), J ((r ≫ e') ≫ Φ), J (r ≫ e)] (fun k => by
      rw [Category.id_comp]
      fin_cases k
      exacts [rfl, congrArg J e₁, congrArg J e₂])]
    refine (vt y _ (Set.mem_iInter.2 fun k => ?_)).trans ?_
    · fin_cases k
      · exact hJ ((r ≫ e') ≫ Φ)
      · show ((r ≫ e') ≫ p ≫ e' ≫ Φ) y ∈ L.U (J ((r ≫ e') ≫ Φ))
        rw [e₁]; exact hJ _
      · show ((r ≫ e') ≫ p ≫ e) y ∈ L.U (J (r ≫ e))
        rw [e₂]; exact hJ _
    · exact congrArg (·⁻¹) ((congrArg (· * _) (gm_self hL ((r ≫ e') ≫ Φ) y (hJ _))).trans (_root_.one_mul _))

end General

theorem exists_rigidified : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D₂ : DegData R I) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))) (β : D₂.toPre.P.A ⟶ D.toPre.P.A), IsMonHom β → ∀ w₀ : LB.Iso D₂.toPre.P.L (D.toPre.P.L.pull (padd D.toPre.P.A β (toUnit D₂.toPre.P.A ≫ g.b)).left), w₀.IsGen → ∃ w : LB.Iso D₂.toPre.P.L (LB.LinComb D.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β g.b) GlobalTheory.MumCmp.twε), w.IsGen ∧ ∃ t : LB.Gen (LB.LinComb D.toPre.P.L (fun i => D₂.toPre.xK 0 ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β g.b i) (fun i => -1 * GlobalTheory.MumCmp.twε i)), GlobalTheory.MumCmp.MapsAtExp D.toPre.P.L D₂.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β g.b) GlobalTheory.MumCmp.twε w (D₂.toPre.xK 0) (-1) (D₂.toPre.psi 0) t ∧ LB.Gen.Corr D.toPre.P.L _ _ _ _ t (LB.mulGen D.toPre.P.L _ _ _ _ (D.toPre.psi 0) (LB.pullGen D.toPre.P.L _ _ (g.s 0) (toUnit (TK R)).left)) := by
  intro R _ _ I D D₂ g β hβ w₀ hw₀
  have hb : eSec D₂.toPre.P.A ≫ (padd D.toPre.P.A β (toUnit D₂.toPre.P.A ≫ g.b)).left = g.b.left := by
    rw [eSec, ← Over.comp_left]
    congr 1
    show η[D₂.toPre.P.A] ≫ (β * (toUnit D₂.toPre.P.A ≫ g.b)) = g.b
    have h₁ : η[D₂.toPre.P.A] ≫ β = 1 := by rw [IsMonHom.one_hom, Hom.one_def, toUnit_unit, Category.id_comp]
    have h₂ : η[D₂.toPre.P.A] ≫ toUnit D₂.toPre.P.A = 𝟙 _ := toUnit_unique _ _
    rw [MonObj.comp_mul, h₁, ← Category.assoc, h₂, Category.id_comp, _root_.one_mul]
  have he : eSec D₂.toPre.P.A ≫ (toUnit D₂.toPre.P.A).left = 𝟙 _ := by
    rw [eSec, ← Over.comp_left, toUnit_unique (η[D₂.toPre.P.A] ≫ toUnit D₂.toPre.P.A) (𝟙 _)]
    rfl
  obtain ⟨w, hw, t, h₁, h₂⟩ := exists_iso_maps D.toPre.P.isLB D₂.toPre.P.isLB (toUnit D₂.toPre.P.A).left
    (eSec D₂.toPre.P.A) he _ g.b.left (eSec D.toPre.P.A) hb D₂.toPre.rig D₂.toPre.rig_gen D.toPre.rig D.toPre.rig_gen
    w₀ hw₀ (jK R) (D₂.toPre.xK 0) (Uniq.xK_zero D₂.toPre) (D₂.toPre.psi 0)
    (fun y q hq => Uniq.gm_psi_zero D₂.tau_bimult 0 rfl y q hq)
  refine ⟨w, hw, t, h₁, corr_of_val D.toPre.P.isLB fun y J hJ => (h₂ y J hJ).trans ?_⟩
  refine Eq.symm ((val_mul hJ _ _ _).trans ?_)
  rw [PsiZero.val_psi_zero D.tau_bimult hJ, val_pull hJ, val_corr hJ g.s_zero, val_one, _root_.mul_one]

end GlobalTheory.MumCmp.Norm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRigidifiedValueAtOriginStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rigidifiedValueAtOrigin : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (k : ℕ) (α : D.X) (b : D.SecB k α), ∃ v : R, OrigVal D b v := by
  first | exact @GlobalTheory.Mum.exists_origVal | exact GlobalTheory.Mum.exists_origVal | (intros; apply GlobalTheory.Mum.exists_origVal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionNonzeroUniformisedModelDvrStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Ex.OneGen
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_nonzero_uniformised_model_dvr : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [CharZero W], IsAdicComplete (IsLocalRing.maximalIdeal W) W → ∀ (D : DegData W (IsLocalRing.maximalIdeal W)) (A : PolAV (Sp (FractionRing W))) (G : Over (Sp W)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (IsLocalRing.maximalIdeal W) D A G), ∃ σ : SecAt G U.LG.L (𝟙 (Sp W)), NZ G U.LG.L (𝟙 (Sp W)) σ := by
  first | exact @GlobalTheory.UMin.ModelNZ.exists_sec_nz | exact GlobalTheory.UMin.ModelNZ.exists_sec_nz | (intros; apply GlobalTheory.UMin.ModelNZ.exists_sec_nz <;> assumption)
end

