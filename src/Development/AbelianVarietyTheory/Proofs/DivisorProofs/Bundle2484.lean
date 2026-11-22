import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2364
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2417
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2256
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2396
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2339
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2313
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2337
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2381
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2438
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2371
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0208
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGen
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsExpandsAtOfIntegral
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0155
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0103
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1500
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2398
import Development.AbelianVarietyTheory.Definitions.Divisors.OrdGeOfForall
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalUnitGeneratorOfLineBundleLocalSection
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.Pinch

theorem gm_id_val_germ {X : Scheme.{0}} (x : X) (U : X.Opens) (h : x ∈ U) (a : Γ(X, U)ˣ) :
    (gm (𝟙 X) x U a).val = (X.presheaf.germ U x h).hom a.val := by
  rw [gm_val (𝟙 X) x U h]
  rfl

theorem isUnit_res_basicOpen' {X : Scheme.{0}} {D : X.Opens} (e : Γ(X, D)) :
    IsUnit ((X.presheaf.map (homOfLE (X.basicOpen_le e)).op).hom e) :=
  X.toRingedSpace.isUnit_res_basicOpen e

def basicUnit {X : Scheme.{0}} {D : X.Opens} (e : Γ(X, D)) : Γ(X, X.basicOpen e)ˣ :=
  (isUnit_res_basicOpen' e).unit

theorem gm_basicUnit_val {X : Scheme.{0}} {D : X.Opens} (e : Γ(X, D)) (x : X) (hx : x ∈ X.basicOpen e) :
    (gm (𝟙 X) x _ (basicUnit e)).val = (X.presheaf.germ D x (X.basicOpen_le e hx)).hom e := by
  rw [gm_id_val_germ x _ hx]
  show (X.presheaf.germ (X.basicOpen e) x hx).hom ((X.presheaf.map (homOfLE (X.basicOpen_le e)).op).hom e) = _
  exact TopCat.Presheaf.germ_res_apply X.presheaf _ x hx e

theorem exists_locGen_of_secFam : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (J : Type) (D : J → X.Opens) (k : J → L.ι) (hD : ∀ j, D j ≤ L.U (k j)) (e : ∀ j, Γ(X, D j)), GlobalTheory.Pinch.IsSecFam L D k hD e → ∃ (V : X.Opens) (a : ∀ i, Γ(X, V ⊓ L.U i)ˣ), (∀ j (x : X) (h : x ∈ D j), IsUnit ((X.presheaf.germ (D j) x h).hom (e j)) → x ∈ V) ∧ GlobalTheory.Pinch.LocGen L V a := by
  intro X L hL J D k hD e he
  let B : J → X.Opens := fun j => X.basicOpen (e j)
  have hB : ∀ j, B j ≤ D j := fun j => X.basicOpen_le (e j)
  let V : X.Opens := ⨆ j, B j
  have hBV : ∀ j, B j ≤ V := fun j => le_iSup B j

  have ge : ∀ j j' (z : X) (hz : z ∈ B j) (hz' : z ∈ B j'),
      gm (𝟙 X) z (B j) (basicUnit (e j)) =
        gm (𝟙 X) z (L.U (k j) ⊓ L.U (k j')) (L.g (k j) (k j')) * gm (𝟙 X) z (B j') (basicUnit (e j')) := by
    intro j j' z hz hz'
    apply Units.ext
    rw [Units.val_mul, gm_basicUnit_val _ z hz, gm_basicUnit_val _ z hz',
      gm_id_val_germ z (L.U (k j) ⊓ L.U (k j')) ⟨hD j (hB j hz), hD j' (hB j' hz')⟩]
    exact he j j' z (hB j hz) (hB j' hz')
  let W : L.ι → J → X.Opens := fun i j => B j ⊓ L.U i
  have hWV : ∀ i j, W i j ≤ V ⊓ L.U i := fun i j => inf_le_inf_right _ (hBV j)
  have hWg : ∀ i j, W i j ≤ L.U i ⊓ L.U (k j) := fun i j z hz => ⟨hz.2, hD j (hB j hz.1)⟩
  have hWB : ∀ i j, W i j ≤ B j := fun i j => inf_le_left
  let u : ∀ i j, Γ(X, W i j)ˣ := fun i j => res (hWg i j) (L.g i (k j)) * res (hWB i j) (basicUnit (e j))
  have gu : ∀ i j (z : X) (hz : z ∈ W i j), gm (𝟙 X) z (W i j) (u i j) =
      gm (𝟙 X) z (L.U i ⊓ L.U (k j)) (L.g i (k j)) * gm (𝟙 X) z (B j) (basicUnit (e j)) := by
    intro i j z hz
    simp only [u, map_mul]
    rw [gm_res _ z (hWg i j) hz, gm_res _ z (hWB i j) hz]
  have key : ∀ i j j' (z : X), z ∈ L.U i → z ∈ B j → z ∈ B j' →
      gm (𝟙 X) z (L.U i ⊓ L.U (k j)) (L.g i (k j)) * gm (𝟙 X) z (B j) (basicUnit (e j)) =
      gm (𝟙 X) z (L.U i ⊓ L.U (k j')) (L.g i (k j')) * gm (𝟙 X) z (B j') (basicUnit (e j')) := by
    intro i j j' z hi hj hj'
    rw [ge j j' z hj hj', ← _root_.mul_assoc, gm_cocycle hL (𝟙 X) z hi (hD j (hB j hj)) (hD j' (hB j' hj'))]
  have glued : ∀ i, ∃ s : Γ(X, V ⊓ L.U i)ˣ, ∀ j, res (hWV i j) s = u i j := by
    intro i
    refine glue_unit (V ⊓ L.U i) (W i) (hWV i) (fun z hz => ?_) (u i) (fun j j' z hz => ?_)
    · obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hz.1
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, hj, hz.2⟩
    · rw [gu i j z hz.1, gu i j' z hz.2]
      exact key i j j' z hz.1.2 hz.1.1 hz.2.1
  choose a ha using glued
  refine ⟨V, a, fun j x hx hu => hBV j ((Scheme.mem_basicOpen X (e j) x hx).2 hu), ?_⟩
  intro y i i' hy hi hi'
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
  have ga : ∀ i (hi : y ∈ L.U i), gm (𝟙 X) y (V ⊓ L.U i) (a i) =
      gm (𝟙 X) y (L.U i ⊓ L.U (k j)) (L.g i (k j)) * gm (𝟙 X) y (B j) (basicUnit (e j)) := by
    intro i hi
    rw [← gm_res _ y (hWV i j) ⟨hj, hi⟩, ha i j]
    exact gu i j y ⟨hj, hi⟩
  rw [ga i hi, ga i' hi', ← _root_.mul_assoc, gm_cocycle hL (𝟙 X) y hi hi' (hD j (hB j hj))]

end GlobalTheory.Pinch
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogKodairaSpencerGenericEigenFrame
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

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LogKSDiv.GenKSProof

theorem embK_conj_bar' {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {l : Level H} (c : Coeff l) (τ : E →+* ℂ) (x : 𝓞 E) :
    embK c ((starRingEnd ℂ).comp τ) (H.bar x) = embK c τ x := by
  apply Subtype.ext
  show ((starRingEnd ℂ).comp τ) ((H.bar x : 𝓞 E) : E) = τ (x : E)
  rw [RingHom.comp_apply, H.bar_eq, IsCMField.complexEmbedding_complexConj, Complex.conj_conj]

theorem embK_bar' {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {l : Level H} (c : Coeff l) (τ : E →+* ℂ) (x : 𝓞 E) :
    embK c τ (H.bar x) = embK c ((starRingEnd ℂ).comp τ) x := by
  apply Subtype.ext
  show τ ((H.bar x : 𝓞 E) : E) = ((starRingEnd ℂ).comp τ) (x : E)
  rw [RingHom.comp_apply, H.bar_eq, IsCMField.complexEmbedding_complexConj]

theorem card_pairIx {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) : Fintype.card (GlobalTheory.LogKSDiv.PairIx H Dw) = Dw.dim := by
  have h := FlagTan.isHalf_psiSet H
  have hc : Fintype.card {τ : E →+* ℂ // τ (H.rt : E) = H.rt0} = Module.finrank ℚ E / 2 := by
    rw [← h.card, FlagTan.psiSet, Fintype.card_subtype]
  have hm : ∀ τ : {τ : E →+* ℂ // τ (H.rt : E) = H.rt0},
      Dw.mult τ.1 * Dw.mult ((starRingEnd ℂ).comp τ.1) = Dw.p * Dw.q := fun τ => by
    rcases FlagTan.mult_conj (Dw := Dw) τ.1 with ⟨a, b⟩ | ⟨a, b⟩
    · rw [a, show (starRingEnd ℂ).comp τ.1 = conjEmb τ.1 from rfl, b]
    · rw [a, show (starRingEnd ℂ).comp τ.1 = conjEmb τ.1 from rfl, b, mul_comm]
  simp only [Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin, hm, Finset.sum_const, Finset.card_univ, hc,
    smul_eq_mul, Datum.dim, mul_assoc]

theorem symPair_mem_balanced {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (c : Coeff l) (R : Type) [CommRing R] (κ : c.F → R) (n : ℕ)
    (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (P : GlobalTheory.LogKSDiv.PairIx H Dw) :
    GlobalTheory.LogKSDiv.symPair (R := R) e P ∈
      LogKS.balanced H.bar (fun a => Matrix.diagonal fun j => κ (embK c (e.symm j).1 a)) := by
  refine (LogKS.mem_balanced_diagonal H.bar (fun j a => κ (embK c (e.symm j).1 a)) _).2 ⟨?_, fun a i k => ?_⟩
  · ext a b
    simp only [Matrix.transpose_apply, GlobalTheory.LogKSDiv.symPair, Matrix.of_apply]
    rw [add_comm]
    congr 1 <;> congr 1 <;> exact propext and_comm
  · simp only [GlobalTheory.LogKSDiv.symPair, Matrix.of_apply]
    by_cases h1 : i = e ⟨P.1.1, P.2.1⟩ ∧ k = e ⟨(starRingEnd ℂ).comp P.1.1, P.2.2⟩
    · obtain ⟨rfl, rfl⟩ := h1
      simp only [Equiv.symm_apply_apply, embK_conj_bar', sub_self, zero_mul]
    by_cases h2 : i = e ⟨(starRingEnd ℂ).comp P.1.1, P.2.2⟩ ∧ k = e ⟨P.1.1, P.2.1⟩
    · obtain ⟨rfl, rfl⟩ := h2
      simp only [Equiv.symm_apply_apply, embK_bar', sub_self, zero_mul]
    · rw [if_neg h1, if_neg h2, add_zero, mul_zero]

theorem exists_ext (k R K : Type) [CommRing k] [CommRing R] [Field K] (ρ : R →+* K) (α : k →+* K) (κ : k → R)
    (hfr : letI := ρ.toAlgebra; IsFractionRing R K) (hκ : ∀ a, ρ (κ a) = α a) (d : Derivation ℤ R R)
    (hd : ∀ a, d (κ a) = 0) :
    ∃ D : (letI := α.toAlgebra; Derivation k K K), ∀ r, D (ρ r) = ρ (d r) := by
  letI := ρ.toAlgebra
  obtain ⟨δ, hδ, hδρ⟩ := Formalism.L2.Pj.GenericSectionMinimum.IsDer.ofLoc (A := R) (B := K) (nonZeroDivisors R) (fun r => ρ (d r))
    (fun x y => by rw [map_add, map_add]) (fun x y => by
      rw [Derivation.leibniz, map_add, smul_eq_mul, smul_eq_mul, map_mul, map_mul]; rfl)
  have hα : ∀ a, δ (α a) = 0 := fun a => by
    rw [← hκ a]
    exact (hδρ (κ a)).trans (by rw [hd, map_zero])
  letI := α.toAlgebra
  have hs : ∀ (a : k) (x : K), δ (a • x) = a • δ x := fun a x => by
    show δ (α a * x) = α a * δ x
    rw [hδ.mul, hα, mul_zero, add_zero]
  let D0 : K →ₗ[k] K := { toFun := δ, map_add' := hδ.add, map_smul' := hs }
  exact ⟨{ toLinearMap := D0, map_one_eq_zero' := hδ.der_one, leibniz' := (fun x y => hδ.mul x y) },
    fun r => hδρ r⟩

theorem exists_genKS : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), 1 ≤ Dw.p + Dw.q → FnAlgClosed Xo c → ∀ [IsIntegral (X₀ TF.Y Z)] [SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z)], ∀ (φ₀ : c.F →+* (X₀ TF.Y Z).functionField) (f₀ : GlobalTheory.ShFam.EigFrame TF.Y φ₀ ((show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) ≫ (barComp TF.Y Z).ι)), (show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) ≫ s₀ TF.Y Z = spMap φ₀ → ∃ D : Fin Dw.dim → GlobalTheory.LogKSDiv.GenDer TF Z, GlobalTheory.LogKSDiv.GenKS TF Z f₀.v D := by
  intro E _ _ _ H Dw l Xo c TF Z _ _ _ _ φ₀ f₀ hφ₀
  obtain ⟨U, hU, ρ, n, e, v, hch, htan, huq, hf, heig⟩ := GlobalTheory.T.exists_spread_genericEigenFrame_affineOpen E H Dw l Xo c TF Z φ₀ f₀ hφ₀
  obtain ⟨hfr, hconst⟩ := GlobalTheory.T.genericGerm_functionField_isFractionRing_affineChart E H Dw l Xo c TF Z U hU ρ hch
  obtain ⟨e', he'⟩ := TF.logKS U n v _ htan huq heig
  let ε : Fin Dw.dim ≃ GlobalTheory.LogKSDiv.PairIx H Dw := (Fintype.equivFinOfCardEq (card_pairIx H Dw)).symm
  let Dl : Fin Dw.dim → LogKS.logDer TF.Y.s (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U :=
    fun j => e'.symm ⟨GlobalTheory.LogKSDiv.symPair e (ε j), symPair_mem_balanced H Dw l c _ _ n e (ε j)⟩
  have hD := fun j => exists_ext c.F Γ(TF.Y.X, U.1) (X₀ TF.Y Z).functionField ρ (GlobalTheory.Cartier.constFn (s₀ TF.Y Z))
    (constFn TF.Y.s U.1) hfr hconst (Dl j).1 (Dl j).2.1
  choose D hD using hD
  refine ⟨D, U, hU, ρ, n, e, v, ε, Dl, hch, htan, huq, fun τ i => hf τ i, fun j => ?_, hD⟩
  refine (he' (Dl j) _).2 ?_
  simp only [Dl, LinearEquiv.apply_symm_apply]

end GlobalTheory.LogKSDiv.GenKSProof
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogVectorFieldTopFormPairingRegularAtPoint
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

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogKSDiv

open IsLocalRing

theorem isUnit_det_of_span_eq_top (k A : Type) [CommRing k] [CommRing A] [Algebra k A] {N : ℕ} (g : Fin N → A)
    (bΩ : Module.Basis (Fin N) A Ω[A⁄k]) (hg : ∀ i, bΩ i = KaehlerDifferential.D k A (g i))
    (δ : Fin N → Derivation k A A) (hδ : Submodule.span A (Set.range δ) = ⊤) :
    IsUnit (Matrix.of fun i j => δ j (g i)).det := by
  classical
  have h : ∀ i, ∃ a : Fin N → A, ∑ j, a j • δ j = KaehlerDifferential.linearMapEquivDerivation k A (bΩ.coord i) :=
    fun i => (Submodule.mem_span_range_iff_exists_fun A).1 (hδ ▸ Submodule.mem_top)
  choose a ha using h
  have hm : (Matrix.of fun i j => δ j (g i)) * (Matrix.of fun j i => a i j) = 1 := by
    ext l i
    have h1 := congrArg (fun d : Derivation k A A => d (g l)) (ha i)
    simp only [KaehlerDifferential.linearMapEquivDerivation_apply_apply, ← hg] at h1
    rw [Matrix.mul_apply, Matrix.one_apply]
    have h2 : (∑ j, a i j • δ j) (g l) = ∑ j, a i j * δ j (g l) := by
      have := map_sum (Derivation.coeFnAddMonoidHom (R := k) (A := A) (M := A)) (fun j => a i j • δ j) Finset.univ
      have h3 := congrFun this (g l)
      rw [Finset.sum_apply] at h3
      exact h3
    rw [h2] at h1
    simp only [Matrix.of_apply, mul_comm (δ _ _)]
    rw [h1]
    simp [Finsupp.single_apply]
  exact Matrix.isUnit_det_of_right_inverse hm

theorem det_mem_maximalIdeal (k A : Type) [CommRing k] [CommRing A] [IsLocalRing A] [Algebra k A] {N : ℕ}
    (g : Fin N → A) (bΩ : Module.Basis (Fin N) A Ω[A⁄k]) (hg : ∀ i, bΩ i = KaehlerDifferential.D k A (g i))
    (δ : Fin N → Derivation k A A) (t : A) (ht : t ∈ maximalIdeal A)
    (hd : KaehlerDifferential.D k A t ∉ (maximalIdeal A) • (⊤ : Submodule A Ω[A⁄k]))
    (hδ : ∀ j, δ j t ∈ Ideal.span {t}) : (Matrix.of fun i j => δ j (g i)).det ∈ maximalIdeal A := by
  classical
  set c : Fin N → A := fun i => bΩ.repr (KaehlerDifferential.D k A t) i with hc
  have hsum : KaehlerDifferential.D k A t = ∑ i, c i • bΩ i := (bΩ.sum_repr _).symm
  have hne : (fun i => residue A (c i)) ≠ 0 := by
    intro h0
    apply hd
    rw [hsum]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul ?_ Submodule.mem_top
    exact (residue_eq_zero_iff _).1 (congrFun h0 i)
  rw [← residue_eq_zero_iff, RingHom.map_det]
  refine Matrix.exists_vecMul_eq_zero_iff.1 ⟨_, hne, ?_⟩
  funext j
  have h1 : δ j t = ∑ i, c i * δ j (g i) := by
    rw [← (δ j).liftKaehlerDifferential_comp_D t, hsum, map_sum]
    simp [hg]
  have h2 : residue A (δ j t) = 0 :=
    (residue_eq_zero_iff _).2 ((Ideal.span_singleton_le_iff_mem _).2 ht (hδ j))
  rw [h1, map_sum] at h2
  simpa [Matrix.vecMul, dotProduct] using h2

theorem derivation_mem_span_of_prod {k A : Type} [CommRing k] [CommRing A] [IsRegularLocalRing A] [Algebra k A] {n : ℕ}
    (f : Fin n → A) (hf : ReciprocityTheory.AnForm.R.FinalTheorems.Rsp A n f) (J : Finset (Fin n)) {j : Fin n} (hj : j ∈ J)
    (δ : Derivation k A A) (hδ : δ (∏ i ∈ J, f i) ∈ Ideal.span {∏ i ∈ J, f i}) : δ (f j) ∈ Ideal.span {f j} := by
  classical
  have hD : IsDomain A := ReciprocityTheory.AnForm.R.isDomain_of_isRegularLocalRing
  have hp := ReciprocityTheory.AnForm.R.prime_of_regular_params f hf.1 hf.2
  rw [Ideal.mem_span_singleton] at hδ ⊢
  rw [← Finset.mul_prod_erase J f hj, Derivation.leibniz, smul_eq_mul, smul_eq_mul] at hδ
  have h1 : f j ∣ (∏ i ∈ J.erase j, f i) * δ (f j) :=
    (dvd_add_right (dvd_mul_right _ _)).1 ((dvd_mul_right _ _).trans hδ)
  refine ((hp j).dvd_or_dvd h1).resolve_left fun h2 => ?_
  obtain ⟨i, hi, h3⟩ := (hp j).exists_mem_finset_dvd h2
  exact (ReciprocityTheory.AnForm.R.regular_params_spec f hf.1 hf.2).2 j i (Finset.ne_of_mem_erase hi).symm
    ((hp j).associated_of_dvd (hp i) h3)

theorem D_notMem_smul_top {k A : Type} [CommRing k] [CommRing A] [IsLocalRing A] [Algebra k A]
    [Algebra.FormallySmooth k (ResidueField A)] {t : A} (ht : t ∈ maximalIdeal A) (ht2 : t ∉ maximalIdeal A ^ 2) :
    KaehlerDifferential.D k A t ∉ (maximalIdeal A) • (⊤ : Submodule A Ω[A⁄k]) := by
  intro hm
  have h := GlobalTheory.AdaptedFrame.linearIndependent_tmul_D (k := k) (fun _ : Unit => t) (fun _ => ht)
    (linearIndependent_unique_iff.2 (by
      intro h0
      exact ht2 ((Ideal.toCotangent_eq_zero _ _).1 h0)))
  refine h.ne_zero () ?_
  generalize KaehlerDifferential.D k A t = w at hm
  refine Submodule.smul_induction_on hm (fun r hr w _ => ?_) (fun x y hx hy => ?_)
  · rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one, ResidueField.algebraMap_eq,
      (residue_eq_zero_iff _).2 hr, TensorProduct.zero_tmul]
  · rw [TensorProduct.tmul_add, hx, hy, add_zero]

theorem derivation_mem_map {k R A : Type} [CommRing k] [CommRing R] [CommRing A] [Algebra k A] (φ : R →+* A)
    (I : Ideal R) (d : R → R) (hd : ∀ r ∈ I, d r ∈ I) (δ : Derivation k A A) (hδ : ∀ r, δ (φ r) = φ (d r))
    {a : A} (ha : a ∈ I.map φ) : δ a ∈ I.map φ := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨r, hr, rfl⟩ := hx
    rw [hδ]
    exact Ideal.mem_map_of_mem _ (hd r hr)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x hx0 hx =>
    rw [smul_eq_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact add_mem (Ideal.mul_mem_left _ _ hx) (Ideal.mul_mem_right _ _ hx0)

theorem exists_boundary_param : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), ∀ [IsIntegral (X₀ TF.Y Z)] [SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z)] (x : X₀ TF.Y Z) (U : TF.Y.X.affineOpens), ∀ (hx : (barComp TF.Y Z).ι x ∈ U.1) (b : Module.Basis (Fin Dw.dim) Γ(TF.Y.X, U.1) (LogKS.logDer TF.Y.s (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U)), letI := (GlobalTheory.LogKSDiv.stalkAlg TF Z x).toAlgebra; ∀ δ : Fin Dw.dim → Derivation c.F ((X₀ TF.Y Z).presheaf.stalk x) ((X₀ TF.Y Z).presheaf.stalk x), (∀ j r, δ j (GlobalTheory.LogKSDiv.stalkHom TF Z x U hx r) = GlobalTheory.LogKSDiv.stalkHom TF Z x U hx ((b j).1 r)) → x ∉ (j₀ TF.Y Z).opensRange → ∃ t ∈ IsLocalRing.maximalIdeal ((X₀ TF.Y Z).presheaf.stalk x), KaehlerDifferential.D c.F ((X₀ TF.Y Z).presheaf.stalk x) t ∉ (IsLocalRing.maximalIdeal ((X₀ TF.Y Z).presheaf.stalk x)) • (⊤ : Submodule ((X₀ TF.Y Z).presheaf.stalk x) Ω[(X₀ TF.Y Z).presheaf.stalk x⁄c.F]) ∧ ∀ j, δ j t ∈ Ideal.span {t} := by
  intro E _ _ _ H Dw l Xo c TF Z _ _ x U hx b δ hδ hn
  letI := (GlobalTheory.LogKSDiv.stalkAlg TF Z x).toAlgebra
  obtain ⟨hreg, n, f, J, hf, ⟨j, hj⟩, hI⟩ := GlobalTheory.T.boundary_componentStalk_regular_boundaryIdeal_prod_params E H Dw l Xo c TF Z x U hx hn
  have hm : f j ∈ maximalIdeal ((X₀ TF.Y Z).presheaf.stalk x) := hf.1 ▸ Ideal.subset_span ⟨j, rfl⟩
  refine ⟨f j, hm, ?_, fun i => ?_⟩
  · obtain ⟨V, hV, hxV, -⟩ := Opens.isBasis_iff_nbhd.1 (X₀ TF.Y Z).isBasis_affineOpens (show x ∈ (⊤ : (X₀ TF.Y Z).Opens) from trivial)
    haveI := GlobalTheory.AdaptedFrame.formallySmooth_residueField (s₀ TF.Y Z) (n := Dw.dim) hV x hxV (by
      ext t
      change ((X₀ TF.Y Z).presheaf.germ ⊤ x trivial).hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX (s₀ TF.Y Z) ⊤ t) =
        ((X₀ TF.Y Z).presheaf.germ V x hxV).hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX (s₀ TF.Y Z) V t)
      rw [← GlobalTheory.TopForm.resG_comp_algX (s₀ TF.Y Z) (le_top : V ≤ ⊤), RingHom.comp_apply, germ_resG])
    exact D_notMem_smul_top hm ((ReciprocityTheory.AnForm.R.regular_params_spec f hf.1 hf.2).1 j)
  · refine derivation_mem_span_of_prod f hf J hj (δ i) ?_
    rw [← hI]
    refine derivation_mem_map _ _ (b i).1 (b i).2.2 (δ i) (hδ i) ?_
    rw [hI]
    exact Ideal.subset_span rfl

theorem local_topPair : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), ∀ [IsIntegral (X₀ TF.Y Z)] [SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z)] (x : X₀ TF.Y Z) (U : TF.Y.X.affineOpens), U.1 ≤ barComp TF.Y Z → (barComp TF.Y Z).ι x ∈ U.1 → ∀ (ρ : Γ(TF.Y.X, U.1) →+* (X₀ TF.Y Z).functionField), spMap ρ ≫ LogKS.chart U = GlobalTheory.LogKSDiv.genPt TF Z ≫ (barComp TF.Y Z).ι → ∀ (b : Module.Basis (Fin Dw.dim) Γ(TF.Y.X, U.1) (LogKS.logDer TF.Y.s (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U)) (D : Fin Dw.dim → GlobalTheory.LogKSDiv.GenDer TF Z), (letI := (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)).toAlgebra; ∀ j r, (show Derivation c.F (X₀ TF.Y Z).functionField (X₀ TF.Y Z).functionField from D j) (ρ r) = ρ ((b j).1 r)) → ∀ (U' : (X₀ TF.Y Z).Opens) (ω : TopForm.FormsOn (s₀ TF.Y Z) Dw.dim U'), TopForm.IsFrame ω → ∀ hx : x ∈ U', RegAt x (GlobalTheory.LogKSDiv.topPair (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)) D (formOf U' (gen_mem hx) ω)) ∧ (UnitAt x (GlobalTheory.LogKSDiv.topPair (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)) D (formOf U' (gen_mem hx) ω)) ↔ x ∈ (j₀ TF.Y Z).opensRange) := by
  intro E _ _ _ H Dw l Xo c TF Z _ _ x U hU hxU ρ hρ b D hD U' ω hω hx
  have h1 := chartRestr_eq_germ E H Dw l Xo c TF Z x U hU hxU ρ hρ
  obtain ⟨δ, hδK, hδR⟩ := GlobalTheory.T.exists_componentStalkDerivation_of_functionField_extension E H Dw l Xo c TF Z x U hU hxU ρ h1 (fun j => (b j).1) D hD
  obtain ⟨g, bΩ, u, hg, hu, hform⟩ := frame_eq_unit_smul_dForm E H Dw l Xo c TF Z x U' ω hω hx
  letI := (stalkAlg TF Z x).toAlgebra
  have key : topPair (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)) D (formOf U' (gen_mem hx) ω) =
      algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField
        (u * (Matrix.of fun i j => δ j (g i)).det) := by
    rw [hform, LinearMap.map_smul, topPair_dForm, smul_eq_mul, map_mul, RingHom.map_det]
    congr 2
    ext i j
    exact hδK j (g i)
  refine ⟨⟨_, key.symm⟩, fun hU' => ?_, fun hr => ?_⟩
  · by_contra hn
    obtain ⟨t, htm, htd, htδ⟩ := exists_boundary_param E H Dw l Xo c TF Z x U hxU b δ hδR hn
    have hz := det_mem_maximalIdeal c.F _ g bΩ hg δ t htm htd htδ
    refine (zeroAt_iff.1 ⟨_, Ideal.mul_mem_left _ u hz, key.symm⟩).2 hU'
  · have hs := GlobalTheory.T.span_logDer_germs' E H Dw l Xo c TF Z x U hU hxU b δ hδR hr
    exact ⟨_, hu.mul (isUnit_det_of_span_eq_top c.F _ g bΩ hg δ hs), key.symm⟩

end GlobalTheory.LogKSDiv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLtBinomialBoundOfMulPowLt
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair

namespace GlobalTheory

theorem elementary_binom_bound : ∀ (c k : ℕ) (h d : ℚ), 1 ≤ k → 0 < h → (c : ℚ) * (k : ℚ) ^ k < h ^ k * d →
  ∃ q : ℚ, q < d ∧ ∀ l₀ : ℕ, ∃ l M : ℕ, l₀ ≤ l ∧ 1 ≤ M ∧ (k : ℚ) * l < h * M ∧ h < l ∧
    ((c * (M + k - 1).choose k : ℕ) : ℚ) < q * (l : ℚ) ^ k / k.factorial := by
  intro c k h d hk hh hcd
  have hhk : 0 < h ^ k := pow_pos hh k
  set a : ℚ := (c : ℚ) * ((k : ℚ) / h) ^ k with ha
  have had : a < d := by
    rw [ha, div_pow, ← mul_div_assoc, div_lt_iff₀ hhk]; linarith
  refine ⟨(a + d) / 2, by linarith, ?_⟩
  intro l₀
  have hlim : Tendsto (fun l : ℕ => (c : ℚ) * ((k : ℚ) / h + (k : ℚ) / (l : ℚ)) ^ k) atTop
      (nhds ((c : ℚ) * ((k : ℚ) / h + 0) ^ k)) :=
    ((tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat (k : ℚ))).pow k).const_mul _
  rw [add_zero] at hlim
  have hev1 : ∀ᶠ l : ℕ in atTop, (c : ℚ) * ((k : ℚ) / h + (k : ℚ) / (l : ℚ)) ^ k < (a + d) / 2 :=
    hlim.eventually (gt_mem_nhds (by rw [← ha]; linarith))
  have hev2 : ∀ᶠ l : ℕ in atTop, h < (l : ℚ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop h)
  obtain ⟨l, hl1, hl2, hl0⟩ := (hev1.and (hev2.and (eventually_ge_atTop l₀))).exists
  have hlpos : (0 : ℚ) < l := lt_trans hh hl2
  set x : ℚ := (k : ℚ) * l / h with hx
  have hx0 : 0 ≤ x := by positivity
  refine ⟨l, ⌊x⌋₊ + 1, hl0, by omega, ?_, hl2, ?_⟩
  · have := Nat.lt_floor_add_one x
    push_cast
    rw [hx, div_lt_iff₀ hh] at this
    linarith
  · have hfl : ((⌊x⌋₊ : ℕ) : ℚ) ≤ x := Nat.floor_le hx0
    have hcast : (((⌊x⌋₊ + 1 + k - 1 : ℕ)) : ℚ) = (⌊x⌋₊ : ℚ) + k := by
      have : ⌊x⌋₊ + 1 + k - 1 = ⌊x⌋₊ + k := by omega
      rw [this]; push_cast; ring
    have hch : (((⌊x⌋₊ + 1 + k - 1).choose k : ℕ) : ℚ) ≤ (((⌊x⌋₊ + 1 + k - 1 : ℕ)) : ℚ) ^ k / k.factorial :=
      Nat.choose_le_pow_div k _
    have hfact : (0 : ℚ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
    have hbase : (((⌊x⌋₊ + 1 + k - 1 : ℕ)) : ℚ) ≤ (l : ℚ) * ((k : ℚ) / h + (k : ℚ) / (l : ℚ)) := by
      rw [hcast, mul_add, hx]
      have e1 : (l : ℚ) * ((k : ℚ) / h) = (k : ℚ) * l / h := by ring
      have e2 : (l : ℚ) * ((k : ℚ) / l) = k := by field_simp
      rw [e1, e2]; linarith [hfl]
    have hpow : (((⌊x⌋₊ + 1 + k - 1 : ℕ)) : ℚ) ^ k ≤ ((l : ℚ) * ((k : ℚ) / h + (k : ℚ) / (l : ℚ))) ^ k :=
      pow_le_pow_left₀ (by positivity) hbase k
    have hlk : (0 : ℚ) < (l : ℚ) ^ k := pow_pos hlpos k
    push_cast
    calc (c : ℚ) * (((⌊x⌋₊ + 1 + k - 1).choose k : ℕ) : ℚ)
        ≤ (c : ℚ) * ((((⌊x⌋₊ + 1 + k - 1 : ℕ)) : ℚ) ^ k / k.factorial) :=
          mul_le_mul_of_nonneg_left hch (by positivity)
      _ ≤ (c : ℚ) * (((l : ℚ) * ((k : ℚ) / h + (k : ℚ) / (l : ℚ))) ^ k / k.factorial) := by
          gcongr
      _ = ((c : ℚ) * ((k : ℚ) / h + (k : ℚ) / (l : ℚ)) ^ k) * (l : ℚ) ^ k / k.factorial := by
          rw [mul_pow]; ring
      _ < (a + d) / 2 * (l : ℚ) ^ k / k.factorial := by
          apply div_lt_div_of_pos_right _ hfact
          exact mul_lt_mul_of_pos_right hl1 hlk

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemNonzeroLocusOfWeightZeroExpansion
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.PreUTheta

theorem exists_mem_nonzeroLocus : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : GlobalTheory.UU.PreU (maximalIdeal R) D A G) (τ : U.SecGT (𝟙_ _) 1) (g : ∀ α, GlobalTheory.UU.SecBT D (𝟙_ _) 1 α), U.ExpT (𝟙_ _) 1 τ g → GlobalTheory.PsiRing.FibNZ (𝟙_ _ ⊗ D.P.A).hom (g 0) → (∀ α, α ≠ 0 → ∃ a ∈ maximalIdeal R, ∃ h : GlobalTheory.UU.SecBT D (𝟙_ _) 1 α, ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul (𝟙_ _ ⊗ D.P.A).hom a (g α) h) → ∃ θ : LB.Sec U.P.L.L, ∃ x ∈ nonzeroLocus θ, G.hom x = closedPoint R := by
  intro R _ _ _ D A G _ _ U τ g hE hnz hmul
  obtain ⟨z₀, hz₀, hn₀⟩ := hnz (closedPoint R)
  have hx : D.P.A.hom ((snd (𝟙_ (Over (Sp R))) D.P.A).left z₀) = closedPoint R :=
    (congrArg (fun q => q z₀) (Over.w (snd (𝟙_ (Over (Sp R))) D.P.A))).trans hz₀
  obtain ⟨y', hy'⟩ := GlobalTheory.ThetaUnit.exists_thick_pt le_rfl 0 D.P.A _ hx
  obtain ⟨y, rfl⟩ := (U.gt 0).q_surj.surj y'
  have hpG : (U.gt 0).pG.left y = (snd (𝟙_ (Over (Sp R))) D.P.A).left z₀ := hy'
  let rG : (thickObj R (maximalIdeal R) 0 G).left ⟶ (𝟙_ (Over (Sp R)) ⊗ G).left :=
    (lift (toUnit _) (fstG (maximalIdeal R) 0 G)).left
  let rB : (thickObj R (maximalIdeal R) 0 G).left ⟶ (𝟙_ (Over (Sp R)) ⊗ D.P.A).left :=
    (lift (toUnit _) (U.gt 0).pG).left
  have h₁ : rG ≫ (snd _ G).left = (fstG (maximalIdeal R) 0 G).left := by
    rw [← Over.comp_left, lift_snd]
  have h₂ : rB ≫ (snd _ D.P.A).left = (U.gt 0).pG.left := by
    rw [← Over.comp_left, lift_snd]
  have h₃ : rB ≫ (fst _ D.P.A).left = rG ≫ (fst _ G).left := by
    rw [← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst]
  have hinj : ∀ a b : (𝟙_ (Over (Sp R)) ⊗ D.P.A).left,
      (snd (𝟙_ (Over (Sp R))) D.P.A).left a = (snd (𝟙_ (Over (Sp R))) D.P.A).left b → a = b := by
    intro a b hab
    have e := GlobalTheory.PsiExpansion.snd_lift_unit D.P.A
    have key : ∀ c, (lift (toUnit D.P.A) (𝟙 D.P.A)).left ((snd (𝟙_ (Over (Sp R))) D.P.A).left c) = c :=
      fun c => by rw [← Scheme.Hom.comp_apply, e]; rfl
    rw [← key a, ← key b, hab]
  have hrB : rB y = z₀ := hinj _ _ ((congrArg (fun q => q y) h₂).trans hpG)
  obtain ⟨J, hJ⟩ := GlobalTheory.ConstFam.exists_good' D.P.isLB y
  obtain ⟨JG, hJG⟩ := GlobalTheory.ConstFam.exists_good' U.P.L.isLB y
  obtain ⟨s, hs⟩ := hE 0
  obtain ⟨H₁, H₂⟩ := hs _ (𝟙 _) rG rB (by rw [Category.id_comp]; exact h₁) (by rw [Category.id_comp]; exact h₂) h₃
    y JG J hJG hJ
  have hu : IsUnit (sval (g 0) rB y J) :=
    (GlobalTheory.Ex.OneGen.isUnit_sval_iff (g 0) rB y hJ).2 (by rw [hrB]; exact hn₀)
  have hc' : rB ≫ (𝟙_ (Over (Sp R)) ⊗ D.P.A).hom =
      (thickObj R (maximalIdeal R) 0 G).hom ≫ spMap (Ideal.Quotient.mk (maximalIdeal R ^ (0 + 1))) :=
    Over.w (lift (toUnit _) (U.gt 0).pG)
  rw [Finset.sum_eq_single 0 (fun α _ hα => by
    obtain ⟨a, ha, h, hh⟩ := hmul α hα
    rw [GlobalTheory.IndivisibleSection.sval_of_secIsMul hh _ y hJ, hc', cst_comp,
      Ideal.Quotient.eq_zero_iff_mem.2 (by simpa using ha), GlobalTheory.GermDiv.cst_zero, zero_mul, zero_mul])
    (fun h => absurd (H₁ 0 h) hu.ne_zero)] at H₂
  have hτ : IsUnit (sval τ rG y JG) :=
    isUnit_of_mul_isUnit_right (H₂ ▸ hu.mul (Units.isUnit _))
  obtain ⟨σ, hσ⟩ := GlobalTheory.PsiExpansion.exists_sameG U.P.L.isLB τ
  rw [hσ _ rG y JG hJG, h₁] at hτ
  have hm := (GlobalTheory.Ex.OneGen.isUnit_sval_iff σ _ y hJG).1 hτ
  refine ⟨ReciprocityTheory.ChartRestriction.G.DVR.secOfH0 σ, _, GlobalTheory.ThetaClosed.nonzeroLocus_firstPower_section_subset σ hm, ?_⟩
  have hc : (fstG (maximalIdeal R) 0 G).left ≫ G.hom = (U.gt 0).pG.left ≫ D.P.A.hom :=
    (Over.w (fstG (maximalIdeal R) 0 G)).trans (Over.w (U.gt 0).pG).symm
  exact (congrArg (fun q => q y) hc).trans ((congrArg D.P.A.hom hpG).trans hx)

end GlobalTheory.PreUTheta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSupportingFormGapOffSmoothConeStatement
section
open AlgebraicGeometry CategoryTheory IsLocalRing ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_supportingForm_gap_off_smoothCone : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (φ : InvFun O) (d : ℕ) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] [Module.Free ℤ X] [Module.Finite ℤ X], IsPolFanOn bar φ X → ∀ (r m : ℕ) (γ : Fin r → LinearMap.BilinForm ℤ X) (a : Fin m → X), IsCone bar φ γ → Supports bar φ d γ a → ∀ lam : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ, (∀ j, 0 ≤ lam (γ j)) → ∀ K : ℤ, ∃ D₀ : ℕ, ∀ D, D₀ ≤ D → (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → (D * d : ℝ) * φ.evalZ β ≤ (D * ∑ i, β (a i) (a i) + lam β : ℤ)) ∧ ∀ (ρ : LinearMap.BilinForm ℤ X), IsCone bar φ ![ρ] → (∀ j, ρ ≠ γ j) → (D * d : ℝ) * φ.evalZ ρ + K ≤ (D * ∑ i, ρ (a i) (a i) + lam ρ : ℤ) := by
  first | exact @GlobalTheory.Poinc.Gap.exists_gap | exact GlobalTheory.Poinc.Gap.exists_gap | (intros; apply GlobalTheory.Poinc.Gap.exists_gap <;> assumption)
end

