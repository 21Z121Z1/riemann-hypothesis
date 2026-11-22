import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0655
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0673
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0643
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0674
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0661
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackModelArcPeriod
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0188
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPsiCoordOfIsPsiCoord
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0946
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0627
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0634
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0667
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0677
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0664
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0617
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0619
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0665
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0659
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousLatticeVectorsAlongArc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0651
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0622
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0638
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0666
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0652

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DicksonExistsFiniteSubfamilyBelow
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory

theorem dickson_finite_below_every {ι : Type} (n : ℕ) (f : ι → Fin n → ℕ) :
    ∃ F : Finset ι, ∀ i, ∃ j ∈ F, f j ≤ f i := by
  classical
  set s : Set (Fin n → ℕ) := Set.range f
  have hpwo : s.IsPWO := Set.isPWO_of_wellQuasiOrderedLE s
  set m : Set (Fin n → ℕ) := {x | Minimal (· ∈ s) x}
  have hm : m.Finite := (setOf_minimal_antichain (· ∈ s)).finite_of_partiallyWellOrderedOn
    (hpwo.mono (fun x hx => hx.prop))
  have hpre : ∀ x ∈ m, ∃ j, f j = x := fun x hx => hx.prop
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨∅, fun i => isEmptyElim i⟩
  choose! g hg using hpre
  refine ⟨hm.toFinset.image g, fun i => ?_⟩
  obtain ⟨x, hxi, hx⟩ := hpwo.exists_le_minimal (Set.mem_range_self i)
  exact ⟨g x, Finset.mem_image_of_mem g (hm.mem_toFinset.mpr hx), by rw [hg x hx]; exact hxi⟩

example : ∀ {ι : Type} (n : ℕ) (f : ι → Fin n → ℕ), ∃ F : Finset ι, ∀ i, ∃ j ∈ F, f j ≤ f i := @dickson_finite_below_every

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DvrPointBoundaryCompatible
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

open GlobalTheory.TraitChartForm in

theorem GlobalTheory.TraitBlowForm.main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (X Z : GMod Xo c) (π : Z.X ⟶ X.X), Z.j ≫ π = X.j → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (ξ : Sp R ⟶ X.X) (tR : SAB H (Sp R)) (_ : SABMap tR X.t ξ) (PR : PELUnif (maximalIdeal R) tR), IsCN R → PR.TorsionIso → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ¬ (∀ p : ℕ, p.Prime → IsUnit (p : W)) → ∀ ϖ : W, Irreducible ϖ → ∀ (χ : Sp W ⟶ Z.X) (t : SAB H (Sp W)) (_ : SABMap t Z.t χ) (P : PELUnif (maximalIdeal W) t), Set.range (jK W ≫ χ) ⊆ Set.range Z.j → ∀ be : LinearMap.BilinForm ℤ P.D.toPre.X, IsMonomial P.D.toPre ![ϖ] ![be] → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V → ∀ (f : W →+* V) (ψ : R →+* V), Function.Injective f → IsLocalHom f → IsLocalHom ψ → Irreducible (f ϖ) → spMap f ≫ χ ≫ π = spMap ψ ≫ ξ → Set.range (jK V ≫ spMap ψ ≫ ξ) ⊆ Set.range X.j → ∃ ε : PR.D.toPre.X ≃ₗ[𝓞 E] P.D.toPre.X, ∀ y, ∃ (r : R) (n : ℕ), PsiCoord PR.D.toPre y r ∧ be (ε y) (ε y) = 2 * n ∧ Associated (ψ r) (f ϖ ^ n) := by
  intro E _ _ _ H D l Xo c X Z π hπ R _ _ _ ξ tR mR PR hCN hTor W _ _ _ hW _ ϖ hϖ χ t mt P hr be hmon V _ _ _ hV f ψ
    hfi hfl hψl _ hc hrV
  have hV' : CDvr V := hV
  obtain ⟨hWd, hWc, hW0⟩ := hW
  obtain ⟨hVd, hVc, hV0⟩ := hV
  obtain ⟨hRN, hRI, hRA, hR0⟩ := hCN
  obtain ⟨L₁, L₂, L₃, L₄, L₅⟩ := GlobalTheory.firstFiveLaws

  obtain ⟨tV, ⟨mV⟩⟩ := GlobalTheory.TraitOrder.exists_pull (spMap f) t
  obtain ⟨tRV, ⟨mRV⟩⟩ := GlobalTheory.TraitOrder.exists_pull (spMap ψ) tR
  obtain ⟨n₀⟩ := GlobalTheory.TraitOrder.comp rfl mt mV
  obtain ⟨n₂⟩ := GlobalTheory.TraitOrder.comp rfl mR mRV
  have j : Function.Injective ((algebraMap V (FractionRing V)).comp f) := (IsFractionRing.injective V _).comp hfi
  let g : FractionRing W →+* FractionRing V := IsFractionRing.lift j
  have eg : jK V ≫ spMap f = spMap g ≫ jK W :=
    (GlobalTheory.Ex.UnifModel.spMap_comp fun _ => rfl).trans
      (GlobalTheory.Ex.UnifModel.spMap_comp (IsFractionRing.lift_algebraMap j)).symm
  obtain ⟨yW, hyW⟩ := GlobalTheory.TraitRank.exists_generic_of_range Z W χ hr
  have hZy : jK V ≫ (spMap f ≫ χ) = (spMap g ≫ yW) ≫ Z.j := by
    rw [Category.assoc, hyW, ← Category.assoc (spMap g), ← eg, Category.assoc]
  have hXy : jK V ≫ (spMap f ≫ χ ≫ π) = (spMap g ≫ yW) ≫ X.j := by
    rw [← hπ, ← Category.assoc (spMap g ≫ yW), ← hZy]
    simp only [Category.assoc]
  obtain ⟨n₁⟩ := GlobalTheory.ArcOrder.exists_sabMap_of_generic X Z hV' (spMap g ≫ yW) (spMap f ≫ χ ≫ π) (spMap f ≫ χ)
    hXy hZy n₀
  obtain ⟨k₁⟩ := GlobalTheory.TraitOrder.cancel (show 𝟙 _ ≫ (spMap f ≫ χ ≫ π) = spMap ψ ≫ ξ by rw [Category.id_comp, hc])
    n₁ n₂

  have hpV : PolAt tV (jK V) := GlobalTheory.DatUniq.polAt_pull mV (GlobalTheory.DatUniq.polAt_of_unif P) (jK V) (spMap g) eg.symm
  have hpRV : PolAt tRV (jK V) :=
    GlobalTheory.DatUniq.polAt_pull k₁ hpV (jK V) (𝟙 _) (by rw [Category.id_comp, Category.comp_id])
  obtain ⟨B, -, gen, hg, hw, -⟩ := GlobalTheory.LN.exists_polAV_of_polAt L₁ L₂ E H V tV hpV
  obtain ⟨BR, -, genR, hgR, hwR, -⟩ := GlobalTheory.LN.exists_polAV_of_polAt L₁ L₂ E H V tRV hpRV

  have hχgen : χ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum W) ∈ abLocus Z.t.G := by
    let p : Sp (FractionRing W) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing W))
    obtain ⟨w, hw⟩ := hr ⟨p, rfl⟩
    rw [← jK_apply_eq_bot W p, ← Scheme.Hom.comp_apply, ← hw]
    exact j_mem_abLocus Z w
  have hfbot : spMap f (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum V) = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum W) := by
    rw [← ker_eq_spMap_bot]
    exact PrimeSpectrum.ext ((RingHom.injective_iff_ker_eq_bot f).1 hfi)

  have hlocW : ∀ a ∈ maximalIdeal W, f a ∈ maximalIdeal V := fun a ha =>
    (mem_maximalIdeal _).2 fun h => (mem_maximalIdeal _).1 ha (isUnit_of_map_unit f a h)
  let Ww : Set (Sp W) := abLocus t.G ∩ {p | ϖ ∉ p.asIdeal}
  have hWo : IsOpen Ww :=
    (GlobalTheory.AbLocusOpen.isOpen_abLocus_local t.G t.semi).inter (PrimeSpectrum.isOpen_basicOpen (a := ϖ))
  have hkerW : (⟨RingHom.ker f, RingHom.ker_isPrime f⟩ : PrimeSpectrum W) ∈ Ww := by
    rw [ker_eq_spMap_bot, hfbot]
    refine ⟨(abLocus_pullback abLocusOne Z.t.semi mt.cart.1 _).1 hχgen, fun h => hϖ.ne_zero ((Submodule.mem_bot W).1 h)⟩
  have hψW : ∀ y, PsiUnitOn P.D.toPre y Ww := fun y => hmon.psiUnitOn y fun p hp => by simpa using hp.2
  obtain ⟨PV, e₁, he₁⟩ := GlobalTheory.PelCoordPull.exists_pelUnif_psiCoord E H W V f t tV mV P Ww inferInstance inferInstance
    hWc inferInstance inferInstance hVc hlocW hWo Set.inter_subset_left hψW hkerW ⟨B, gen, hg, hw⟩

  have hlocR : ∀ a ∈ maximalIdeal R, ψ a ∈ maximalIdeal V := fun a ha =>
    (mem_maximalIdeal _).2 fun h => (mem_maximalIdeal _).1 ha (isUnit_of_map_unit ψ a h)
  have hRo : IsOpen (abLocus tR.G) := GlobalTheory.AbLocusOpen.isOpen_abLocus_local tR.G tR.semi
  have hAdm : admitted R (maximalIdeal R) := ⟨⟨hRN, inferInstance, hRI, hRA⟩, hRA, hR0, inferInstance,
    by letI := Ideal.Quotient.field (maximalIdeal R); infer_instance⟩
  have hψR : ∀ y, PsiUnitOn PR.D.toPre y (abLocus tR.G) :=
    GlobalTheory.psiUnitOn_abLocus_pel L₁ L₂ L₃ L₄ L₅ E H R (maximalIdeal R) hAdm tR PR hTor hRo
  have hkerR : (⟨RingHom.ker ψ, RingHom.ker_isPrime ψ⟩ : PrimeSpectrum R) ∈ abLocus tR.G := by
    rw [ker_eq_spMap_bot]
    refine (abLocus_pullback abLocusOne X.t.semi mR.cart.1 _).1 ?_
    let p : Sp (FractionRing V) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing V))
    obtain ⟨w, hw⟩ := hrV ⟨p, rfl⟩
    have key : ξ (spMap ψ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum V)) = (jK V ≫ spMap ψ ≫ ξ) p := by
      rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, jK_apply_eq_bot V p]
    rw [key, ← hw]
    exact j_mem_abLocus X w
  obtain ⟨PRV, e₂, he₂⟩ := GlobalTheory.PelCoordPull.exists_pelUnif_psiCoord E H R V ψ tR tRV mRV PR (abLocus tR.G) hRN hRI
    hRA inferInstance inferInstance hVc hlocR hRo subset_rfl hψR hkerR ⟨BR, genR, hgR, hwR⟩

  obtain ⟨e₃, he₃⟩ := GlobalTheory.SameCoord.exists_equiv_psiCoord E H V tV tRV k₁ PV PRV inferInstance inferInstance hVc
  refine ⟨(e₂.trans e₃.symm).trans e₁.symm, fun y => ?_⟩
  obtain ⟨r, hr⟩ := (GlobalTheory.PeriodFormCompare.exists_psiCoord_iff PR.D.toPre y).2
    (GlobalTheory.PeriodFormCompare.psiIn_top PR.D y)
  set x := ((e₂.trans e₃.symm).trans e₁.symm) y with hx
  have hx2 : e₃ (e₁ x) = e₂ y := by simp [hx]
  obtain ⟨u₀, nW, hnW, hcW⟩ := hmon x
  obtain ⟨u₁, h₁⟩ := he₁ x _ hcW
  obtain ⟨u₃, h₃⟩ := he₃ _ _ h₁
  obtain ⟨u₂, h₂⟩ := he₂ y r hr
  rw [hx2] at h₃
  obtain ⟨w, hw⟩ := GlobalTheory.PsiCoordLocal.exists_unit_of_coord h₃ h₂
  have key : ψ r = ((u₂⁻¹ * w * u₃ * u₁ * Units.map f.toMonoidHom u₀ : Vˣ) : V) * f ϖ ^ nW 0 := by
    have e := congrArg (fun z => ((u₂⁻¹ : Vˣ) : V) * z) hw
    simp only [Fin.prod_univ_one, Matrix.cons_val_zero, map_mul, map_pow] at e
    rw [← mul_assoc, Units.inv_mul, one_mul] at e
    rw [e]
    simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
    ring
  refine ⟨r, nW 0, hr, by simpa using hnW 0, ?_⟩
  exact Associated.symm (⟨_, by rw [key, mul_comm]⟩ : Associated (f ϖ ^ nW 0) (ψ r))
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenMetricFlagCompactification
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open scoped ComplexOrder

namespace GlobalTheory.ShFam.FlagCpt

theorem smoothOn_met_of_eigMet : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) [SmoothOfRelativeDimension Dw.dim (genStr Z)] (F : Type) [Field F] [NumberField F] (e : F ≃+* c.F) (Y : FlagCpt Z e) (σ : F →+* ℂ) (G : EigMet Z (embOf e σ)) (T : Set (CxPts (genStr Z) (embOf e σ))), IsOpen T → G.SmoothOn (manifold Z (embOf e σ)) T → ∀ n : Pad.Letter Dw → ℤ, IsOpen (Y.down ⁻¹' T : Set (Y.Y.pts σ)) ∧ (Y.met G n).SmoothOn (Y.down ⁻¹' T) := by
  intro E _ _ _ H Dw l Xo c O _ β Z _ F _ _ e Y σ G T hT hG n
  have hc : Continuous (Y.down (σ := σ)) := CxPts.continuous_of_comp (f := Y.π) (fun _ => rfl)
  have hS : IsOpen (Y.down ⁻¹' T : Set (Y.Y.pts σ)) := hT.preimage hc
  refine ⟨hS, ?_⟩
  have key : ∀ y : Y.Y.X, ∃ (U : Y.Y.X.Opens) (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Y.Y.Fnˣ), y ∈ U ∧
      (∀ y' ∈ U, ∀ τ i, (Y.gr τ i).IsEqn y' (t τ i)) ∧
      (Y.Y.an σ).SmoothOn (Y.down ⁻¹' T ∩ ptsIn Y.Y.str σ U) (fun q => Real.log ((Y.met G n).h (prodPow t n) q)) := by
    intro y
    obtain ⟨U, t, V, φ, Fr, A, hy, hφ, hUV, ht, hfr⟩ := GlobalTheory.T.exists_local_flag_coordinates E H Dw l Xo c O β Z F e Y σ y
    refine ⟨U, t, hy, ht, ?_⟩
    choose gf hre him hgf using fun (τ : E →+* ℂ) (a b : Fin (Dw.mult τ)) => hG V φ Fr τ a b hφ
    set S' : Set (Y.Y.pts σ) := Y.down ⁻¹' T ∩ ptsIn Y.Y.str σ U with hS'def
    have hS' : IsOpen S' := hS.inter (isOpen_ptsIn _)
    have hsub : S' ⊆ Y.down ⁻¹' (T ∩ ptsIn _ _ V.1) := fun q hq => ⟨hq.1, hUV q hq.2⟩
    let Mf : ∀ τ : E →+* ℂ, Y.Y.pts σ → Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ :=
      fun τ q => Matrix.of fun a b => gf τ a b (Y.down q)
    let Af : ∀ τ : E →+* ℂ, Y.Y.pts σ → Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ :=
      fun τ q => Matrix.of fun a b => ev Y.Y.str σ U (A τ a b) q
    have hM : ∀ τ a b, (Y.Y.an σ).SmoothOn S' (fun q => (Mf τ q a b).re) ∧ (Y.Y.an σ).SmoothOn S' (fun q => (Mf τ q a b).im) :=
      fun τ a b => ⟨((hre τ a b).comp_map (hT.inter (isOpen_ptsIn _)) (m := Y.down) (f := Y.π) (fun _ => rfl) (Y.Y.an σ)).mono hsub,
        ((him τ a b).comp_map (hT.inter (isOpen_ptsIn _)) (m := Y.down) (f := Y.π) (fun _ => rfl) (Y.Y.an σ)).mono hsub⟩
    have hA : ∀ τ a b, (Y.Y.an σ).HoloOn S' (fun q => Af τ q a b) :=
      fun τ a b => AnRead.holoOn_ev_of_subset _ (fun _ hq => hq.2)
    have hgram : ∀ q ∈ S', ∃ g : Y.FrameAt q, Y.Adapted q t g 1 ∧
        ∀ τ, G.gram (Y.down q) g τ = (Af τ q)ᴴ * Mf τ q * Af τ q := by
      intro q hq
      obtain ⟨hv, g, f, had, hmap, hco⟩ := hfr q hq.2
      refine ⟨g, had, fun τ => ?_⟩
      have e1 : f.co g τ = Af τ q := by
        rw [hco τ]; ext a b; simp [Af, ev_eq hq.2]
      have e2 : G.gram (Y.down q) f τ = Mf τ q := by
        ext a b; exact hgf τ a b (Y.down q) hq.1 hv f hmap
      rw [G.change _ f g τ, e1, e2]
    have hpos : ∀ τ, ∀ q ∈ S', ((Af τ q)ᴴ * Mf τ q * Af τ q).PosDef := fun τ q hq => by
      obtain ⟨g, -, hg⟩ := hgram q hq
      rw [← hg τ]; exact G.pos _ _ _
    have hsm : ∀ z : Letter Dw, (Y.Y.an σ).SmoothOn S' (fun q => Real.log (grSq ((Af z.1 q)ᴴ * Mf z.1 q * Af z.1 q) z.2)) :=
      fun z => GlobalTheory.T.log_gram_square_smooth _ S' _ (GlobalTheory.T.conjugate_hermitian_smooth _ S' hS' _ _ (hA z.1) (hM z.1)) (hpos z.1) z.2
    refine AnRead.SmoothOn.congr (f := fun q => ∑ z : Letter Dw, (n z : ℝ) * Real.log (grSq ((Af z.1 q)ᴴ * Mf z.1 q * Af z.1 q) z.2))
      (fun i => ContDiffOn.sum fun z _ => contDiffOn_const.mul (hsm z i)) fun q hq => ?_
    obtain ⟨g, had, hg⟩ := hgram q hq
    rw [FlagCpt.met_h G n had]
    simp only [prodPow, FlagCpt.genSq, hg, Pi.one_apply, _root_.one_zpow, Finset.prod_const_one, Units.val_one, norm_one, one_pow, div_one]
    rw [Real.log_prod (fun z _ => (zpow_pos (grSq_pos (hpos z.1 q hq) z.2) (n z)).ne')]
    exact Finset.sum_congr rfl fun z _ => Real.log_zpow _ _
  choose U t hy ht hs using key
  refine Var.Met.smoothOn_of_cover hS (fun q _ => by rw [FlagCpt.posSet_met]; exact Set.mem_univ q)
    (T := fun y => ptsIn Y.Y.str σ (U y)) (fun _ => isOpen_ptsIn _) (fun q => ⟨Var.base q, mem_ptsIn.2 (hy _)⟩)
    (e := fun y => prodPow (t y) n) (fun y q hq => FlagCpt.prodPow_mem n (fun τ i => ht y _ (mem_ptsIn.1 hq) τ i))
    fun y => ?_
  refine AnRead.SmoothOn.congr (f := fun q => -Real.log ((Y.met G n).h (prodPow (t y) n) q)) (fun i => (hs y i).neg) ?_
  exact fun q _ => rfl

end GlobalTheory.ShFam.FlagCpt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfToRealRel
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

noncomputable section

namespace GlobalTheory.PolFan

section ConeFacts

variable {X : Type} [AddCommGroup X]

theorem apply_eq_of_toReal_eq {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} {c : Fin m → ℝ}
    {β : LinearMap.BilinForm ℤ X} (h : toReal β = ∑ i, c i • toReal (γ i)) (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ) :
    (ℓ β : ℝ) = ∑ i, c i * ℓ (γ i) := by
  have h0 : ∑ i : Fin (m + 1), (Fin.cons (-1) c : Fin (m + 1) → ℝ) i •
      toReal ((LinearMap.id : LinearMap.BilinForm ℤ X →ₗ[ℤ] LinearMap.BilinForm ℤ X)
        ((Fin.cons β γ : Fin (m + 1) → LinearMap.BilinForm ℤ X) i)) = 0 := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, LinearMap.id_apply, neg_one_smul, ← h, neg_add_cancel]
  have key := sum_mul_eq_zero_of_sum_toReal (fun _ _ hab => hab) ℓ h0
  rw [Fin.sum_univ_succ] at key
  simp only [Fin.cons_zero, Fin.cons_succ] at key
  linarith

theorem InRCone.apply_nonneg {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} {β : LinearMap.BilinForm ℤ X}
    (h : InRCone γ β) (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ) (hℓ : ∀ i, 0 ≤ ℓ (γ i)) : 0 ≤ ℓ β := by
  obtain ⟨c, hc, hβ⟩ := h
  have e := apply_eq_of_toReal_eq hβ ℓ
  have hr : (0 : ℝ) ≤ ℓ β := by
    rw [e]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hc i) (by exact_mod_cast hℓ i)
  exact_mod_cast hr

theorem inRCone_trans {m n : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} {δ : Fin n → LinearMap.BilinForm ℤ X}
    (hδ : ∀ j, InRCone γ (δ j)) {β : LinearMap.BilinForm ℤ X} (hβ : InRCone δ β) : InRCone γ β := by
  choose a ha hδe using hδ
  obtain ⟨b, hb, hβe⟩ := hβ
  refine ⟨fun i => ∑ j, b j * a j i, fun i => Finset.sum_nonneg fun j _ => mul_nonneg (hb j) (ha j i), ?_⟩
  rw [hβe]
  simp only [hδe, Finset.smul_sum, smul_smul, Finset.sum_smul]
  exact Finset.sum_comm

theorem eq_zero_of_toReal_rel {a b : ℕ} {u : Fin a → LinearMap.BilinForm ℤ X} {v : Fin b → LinearMap.BilinForm ℤ X}
    (hind : ∀ (d : Fin b → ℤ) (c : Fin a → ℤ), ∑ j, c j • u j = ∑ k, d k • v k → c = 0)
    {r : Fin a → ℝ} {s : Fin b → ℝ} (h : ∑ j, r j • toReal (u j) = ∑ k, s k • toReal (v k)) : r = 0 := by

  have hpt : ∀ x y : X, ∑ j, r j * (u j x y : ℝ) = ∑ k, s k * (v k x y : ℝ) := by
    intro x y
    have hxy := congrArg (fun B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ => B x y) h
    simpa [LinearMap.sum_apply, toReal_apply] using hxy

  suffices hf : ∀ (f : Module.Dual ℚ ℝ) (j : Fin a), f (r j) = 0 by
    funext j
    exact (Module.forall_dual_apply_eq_zero_iff ℚ (r j)).mp fun f => hf f j
  intro f
  have e : ∀ (t : ℝ) (n : ℤ), f (t * n) = n * f t := by
    intro t n
    rw [mul_comm, ← zsmul_eq_mul, map_zsmul, zsmul_eq_mul]
  have hq : ∀ x y : X, ∑ j, ((u j x y : ℤ) : ℚ) * f (r j) = ∑ k, ((v k x y : ℤ) : ℚ) * f (s k) := by
    intro x y
    have hxy := congrArg f (hpt x y)
    rw [map_sum, map_sum] at hxy
    simpa only [e] using hxy

  let N : ℕ := (∏ j, (f (r j)).den) * ∏ k, (f (s k)).den
  have hN : (N : ℚ) ≠ 0 := by
    have : N ≠ 0 := mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun j _ => (f (r j)).den_nz)
      (Finset.prod_ne_zero_iff.mpr fun k _ => (f (s k)).den_nz)
    exact_mod_cast this
  have key : ∀ q : ℚ, q.den ∣ N → ((((N / q.den : ℕ) : ℤ) * q.num : ℤ) : ℚ) = N * q := by
    intro q hq'
    have hd : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
    rw [Int.cast_mul, Int.cast_natCast, Nat.cast_div hq' hd]
    rw [div_mul_eq_mul_div, mul_div_assoc, Rat.num_div_den]
  have hdr : ∀ j, (f (r j)).den ∣ N := fun j =>
    dvd_mul_of_dvd_left (Finset.dvd_prod_of_mem _ (Finset.mem_univ j)) _
  have hds : ∀ k, (f (s k)).den ∣ N := fun k =>
    dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ (Finset.mem_univ k)) _
  let c : Fin a → ℤ := fun j => ((N / (f (r j)).den : ℕ) : ℤ) * (f (r j)).num
  let d : Fin b → ℤ := fun k => ((N / (f (s k)).den : ℕ) : ℤ) * (f (s k)).num
  have hc : ∀ j, (c j : ℚ) = N * f (r j) := fun j => key _ (hdr j)
  have hd : ∀ k, (d k : ℚ) = N * f (s k) := fun k => key _ (hds k)
  have hrel : ∑ j, c j • u j = ∑ k, d k • v k := by
    ext x y
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    apply Int.cast_injective (α := ℚ)
    push_cast
    simp only [hc, hd]
    have := hq x y
    calc ∑ j, (N : ℚ) * f (r j) * (u j x y : ℚ) = N * ∑ j, ((u j x y : ℤ) : ℚ) * f (r j) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
      _ = N * ∑ k, ((v k x y : ℤ) : ℚ) * f (s k) := by rw [this]
      _ = ∑ k, (N : ℚ) * f (s k) * (v k x y : ℚ) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
  have h0 := hind d c hrel
  intro j
  have hcj : (c j : ℚ) = 0 := by rw [h0]; simp
  rw [hc j] at hcj
  have : (f (r j) : ℚ) = 0 := (mul_eq_zero.mp hcj).resolve_left hN
  exact_mod_cast this

end ConeFacts

section CellFacts

variable {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
  [Module.Finite O X]

theorem IsCell.reindex {m m' : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} (h : IsCell bar φ γ) (e : Fin m' ≃ Fin m) :
    IsCell bar φ fun i => γ (e i) := by
  obtain ⟨hmem, hnn, hlin, hstr⟩ := h
  refine ⟨fun i => hmem (e i), fun i y => hnn (e i) y, ?_, ?_⟩
  · intro c hc
    convert hlin (fun i => c (e.symm i)) (fun i => hc _) using 1
    · congr 1
      funext x y
      exact Fintype.sum_equiv e _ _ (fun i => by simp)
    · exact Fintype.sum_equiv e _ _ (fun i => by simp)
  · obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hstr
    refine ⟨N, ℓ, hN, fun i => h1 (e i), h2, ?_⟩
    intro β hβ hβn heq
    obtain ⟨k, c, hk, hkc⟩ := h3 β hβ hβn heq
    refine ⟨k, fun i => c (e i), hk, ?_⟩
    rw [hkc]
    exact (Fintype.sum_equiv e _ _ (fun _ => rfl)).symm

end CellFacts

example : InRCone (fun i : Fin 2 => (![mulForm, mulForm] : Fin 2 → LinearMap.BilinForm ℤ ℤ) (Equiv.swap 0 1 i))
    ((2 : ℤ) • mulForm) :=
  inRCone_trans (δ := ![mulForm]) (fun j => by
    fin_cases j
    exact ⟨![1, 0], fun i => by fin_cases i <;> norm_num, LinearMap.ext₂ fun a b => by simp [Fin.sum_univ_two]⟩)
    ⟨![2], fun i => by fin_cases i; norm_num, LinearMap.ext₂ fun a b => by simp⟩

end GlobalTheory.PolFan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EtaleCompletionOfDimOneNormal
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Cartier

namespace GlobalTheory.CdvrExt

theorem injective_of_flat_local {A R : Type} [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R]
    (φ : A →+* R) (hφ : φ.Flat) [IsLocalHom φ] : Function.Injective φ := by
  letI := φ.toAlgebra
  haveI : Module.Flat A R := hφ
  haveI : IsLocalHom (algebraMap A R) := ‹_›
  haveI := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := A) (B := R)
  rw [injective_iff_map_eq_zero]
  intro a ha
  have h := Ideal.comap_map_eq_self_of_faithfullyFlat (A := A) (B := R) ⊥
  rw [Ideal.map_bot] at h
  have : a ∈ Ideal.comap (algebraMap A R) ⊥ := by rw [Ideal.mem_comap, Ideal.mem_bot]; exact ha
  rw [h] at this
  simpa using this

theorem isLocalHom_of_map_maximalIdeal {A R : Type} [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R]
    (φ : A →+* R) (h : (maximalIdeal A).map φ = maximalIdeal R) : IsLocalHom φ := by
  refine ⟨fun a ha => ?_⟩
  by_contra hna
  have : φ a ∈ maximalIdeal R := h ▸ Ideal.mem_map_of_mem φ ((mem_maximalIdeal a).2 hna)
  exact (mem_maximalIdeal _).1 this ha

theorem isDVR_of_ringKrullDim_eq_one {A : Type} [CommRing A] [IsLocalRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] (hA : ringKrullDim A = 1) : IsDiscreteValuationRing A := by
  obtain ⟨hf, hrad⟩ := ringKrullDim_eq_one_iff_of_isLocalRing_isDomain.1 hA
  have key := (IsDiscreteValuationRing.TFAE A hf).out 0 3
  try simp only [List.length_cons, List.getElem_cons_succ, List.getElem_cons_zero] at key
  refine key.2 ⟨inferInstance, maximalIdeal A, ⟨?_, ?_⟩, ?_⟩
  · exact (isField_iff_maximalIdeal_eq).not.1 hf
  · exact (maximalIdeal.isMaximal A).isPrime
  · rintro P ⟨hP, hPp⟩
    obtain ⟨x, hxP, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
    refine le_antisymm (le_maximalIdeal hPp.ne_top) ?_
    refine (hrad x hx0).trans ?_
    rw [hPp.radical_le_iff, Ideal.span_singleton_le_iff_mem]
    exact hxP

theorem cdvr_of_isEtaleCompletion : ∀ {A R : Type} [CommRing A] [IsLocalRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] [CommRing R] [IsDomain R] [IsLocalRing R] (φ : A →+* R), ringKrullDim A = 1 →
    IsEtaleCompletion φ → IsCN R → CDvr R := by
  intro A R _ _ _ _ _ _ _ _ φ hA hφ hR
  obtain ⟨hfl, hm, -⟩ := hφ
  obtain ⟨hRn, -, hRc, hR0⟩ := hR
  haveI := hRn
  haveI := isLocalHom_of_map_maximalIdeal φ hm
  have hinj := injective_of_flat_local φ hfl
  haveI := isDVR_of_ringKrullDim_eq_one hA
  have hAf : ¬IsField A := (isField_iff_maximalIdeal_eq).not.2 (IsDiscreteValuationRing.not_a_field A)
  have keyA := (IsDiscreteValuationRing.TFAE A hAf).out 0 4
  try simp only [List.length_cons, List.getElem_cons_succ, List.getElem_cons_zero] at keyA
  obtain ⟨π, hπ⟩ := (keyA.1 inferInstance).principal
  have hπ0 : π ≠ 0 := by
    rintro rfl
    exact IsDiscreteValuationRing.not_a_field A (by rw [hπ]; simp)
  have hmR : maximalIdeal R = Ideal.span {φ π} := by
    rw [← hm, hπ]
    show Ideal.map φ (Ideal.span {π}) = _
    rw [Ideal.map_span, Set.image_singleton]
  have hnf : ¬IsField R := by
    rw [isField_iff_maximalIdeal_eq, hmR, Ideal.span_singleton_eq_bot]
    exact (map_ne_zero_iff φ hinj).2 hπ0
  refine ⟨?_, hRc, hR0⟩
  have keyR := (IsDiscreteValuationRing.TFAE R hnf).out 0 4
  try simp only [List.length_cons, List.getElem_cons_succ, List.getElem_cons_zero] at keyR
  exact keyR.2 ⟨⟨φ π, by rw [hmR]⟩⟩

end GlobalTheory.CdvrExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineDomainFrameHasDRStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.HTLine
open Formalism.MainNotions.DIV.Cons (intO SCF)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affine_domain_frame_hasDR : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Z : Mdl Y i₀), HasDR Z → ∀ z : Z.X, ∃ (U : Z.X.Opens) (hU : IsAffineOpen U) (_ : IsDomain Γ(Z.X, U)) (w : Vecs Dw (Y Z.i).t Γ(Z.X, U)) (g : ℕ) (e : Fin g → (Sp (DualNumber Γ(Z.X, U)) ⟶ (Y Z.i).t.G.left)) (β : ↥(Z.i.c.V W) →+* Γ(Z.X, U)) (y : Sp (FractionRing Γ(Z.X, U)) ⟶ (Xo Z.i.l).XF Z.i.c), z ∈ U ∧ IsIntegrallyClosed Γ(Z.X, U) ∧ Function.Injective β ∧ IntFrame Z hU w ∧ GlobalTheory.LineNorm.IsTanBasis (Y Z.i).t (R := Γ(Z.X, U)) (hU.fromSpec ≫ Z.π) e ∧ spMap (algebraMap Γ(Z.X, U) (FractionRing Γ(Z.X, U))) ≫ hU.fromSpec ≫ Z.π = y ≫ (Y Z.i).j := by
  first | exact @GlobalTheory.HTLine.exists_small_chart | exact GlobalTheory.HTLine.exists_small_chart | (intros; apply GlobalTheory.HTLine.exists_small_chart <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsArcFibreUniformisationThetaMultipleStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_arc_fibre_uniformisation_theta_multiple : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (V : ValuationSubring c.F) (Y : Model Xo c V.subtype) (a : ArcIn Dw l V.subtype ℂ (σ.comp V.subtype)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : GlobalTheory.ArcQ.Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) (th : a.D₀.P.L.Sec) (Θ : GlobalTheory.ArcQ.ThetaDat Ha th) (M : GChart Y), Formalism.L2.PjFree.GoodEmb c σ → IsTypeFn H Dw.p Dw.q ty → PushInvertible Y.t.G Y.t.PP.L → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (σ.comp V.subtype) → (∀ x : Sp (PowerSeries ℂ), PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) → ⊤ ≤ χ ⁻¹ᵁ M.U → ∃ T : ℝ, ∀ w : ℂ, T < w.im → ∀ yF : Sp ℂ ⟶ Xo.XF c, yF ≫ pullback.fst _ _ = Fu.u Ha.i (Ha.Pw w) → yF ≫ pullback.snd _ _ = spMap σ → ∀ (hz : ⊤ ≤ (yF ≫ Y.j) ⁻¹ᵁ M.U) (x : KeyIn ℂ) (φ : x.P.A.left ⟶ Y.t.G.left), GlobalTheory.ArcNormal.KeyAtVia M (yF ≫ Y.j) hz x φ → ∃ (_ : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (c₀ : ℂ), u.IsRig x.rig ∧ GlobalTheory.ArcNormal.ArcFib Y σ Fu Ha.i (Ha.Pw w) x φ u ∧ u.Λ = (Ha.Pw w).range.toIntSubmodule ∧ u.IsFn x.th (fun z => c₀ * thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec z)) := by
  first | exact @GlobalTheory.ArcNormal.exists_unif_of_arc | exact GlobalTheory.ArcNormal.exists_unif_of_arc | (intros; apply GlobalTheory.ArcNormal.exists_unif_of_arc <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsComplexPointDerivationSeparatingParamsCharStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_complexPointDerivation_separating_params_charZero : ∀ (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (n : ℕ) (σ : k →+* ℂ), SmoothOfRelativeDimension n p → ∀ (x₀ : CxPts p σ) (U : Y.affineOpens) (hy : x₀.1 (IsLocalRing.closedPoint ℂ) ∈ U.1) (m : ℕ) (f : Fin m → Γ(Y, U.1)), ReciprocityTheory.AnForm.R.FinalTheorems.Rsp (Y.presheaf.stalk (x₀.1 (IsLocalRing.closedPoint ℂ))) m (fun i => Y.presheaf.germ U.1 _ hy (f i)) → ∀ l : Fin m → ℂ, l ≠ 0 → ∃ δ : Γ(Y, U.1) →+ ℂ, (∀ a : k, δ (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U.1 a) = 0) ∧ (∀ g h : Γ(Y, U.1), δ (g * h) = CxPts.ev p σ U.1 g x₀ * δ h + CxPts.ev p σ U.1 h x₀ * δ g) ∧ ∑ i, l i * δ (f i) ≠ 0 := by
  first | exact @GlobalTheory.PtDerivSep.exists_ptDer_sep | exact GlobalTheory.PtDerivSep.exists_ptDer_sep | (intros; apply GlobalTheory.PtDerivSep.exists_ptDer_sep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousLatticeVectorsAlongArcStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
open scoped CategoryTheory.MonObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuous_lattice_vectors_along_arc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (A : Type) [CommRing A] (φ : c.F →+* A) (x : Sp A ⟶ gen Z) (fr : EigFrame Z φ (x ≫ genι Z)) (ψ : ℂ → (A →+* ℂ)) (r : ℝ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)), IsArc Z σ φ x ψ r → ∃ (ρ : ℝ) (n : ℕ) (lam : Fin n → ℂ → (Fin g → ℂ)), 0 < ρ ∧ ρ ≤ r ∧ (∀ j, ContinuousOn (lam j) (Metric.ball 0 ρ)) ∧ Submodule.span ℂ (Set.range fun j => lam j 0) = ⊤ ∧ ∀ u ∈ Metric.ball (0 : ℂ) ρ, ∀ ex : (Fin g → ℂ) → (Over.mk (spMap (ψ u) ≫ x ≫ genι Z) ⟶ Z.t.G), (∀ z w, ex (z + w) = ex z * ex w) → IsHolTo Set.univ (fun z => (show Sp ℂ ⟶ Z.t.G.left from (ex z).left)) → (∀ j, IsDerivAt0 (fun z => (ex z).left) (Pi.single j 1) (spMap (dualMap (ψ u)) ≫ fr.v (e j).1 (e j).2)) → ∀ j, ex (lam j u) = 1 := by
  first | exact @GlobalTheory.ShFam.BdArc.exists_lattice_sections | exact GlobalTheory.ShFam.BdArc.exists_lattice_sections | (intros; apply GlobalTheory.ShFam.BdArc.exists_lattice_sections <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDvrLiftThroughEtaleChartStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dvr_lift_through_etale_chart : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} (Y : Model Xo c (RingHom.id c.F)) {k : Type} [Field k] {m e : ℕ} (ξ : Sp (ChartRing k m e) ⟶ gen Y), IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ (χ : Sp W ⟶ Y.X), χ (closedPoint W) = genι Y (ξ (closedPoint _)) → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (f : W →+* V) (ψ : ChartRing k m e →+* V), CDvr V ∧ Function.Injective f ∧ IsLocalHom f ∧ IsLocalHom ψ ∧ spMap f ≫ χ = spMap ψ ≫ ξ ≫ genι Y := by
  first | exact @GlobalTheory.ChartLift.exists_lift_to_chart | exact GlobalTheory.ChartLift.exists_lift_to_chart | (intros; apply GlobalTheory.ChartLift.exists_lift_to_chart <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFinsetSquaresConeOfCompactPosDefStatement
section
open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_squares_cone_of_compact_posDef : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (𝒦 : Set (Matrix ι ι ℝ)), IsCompact 𝒦 → (∀ P ∈ 𝒦, P.PosDef) → ∃ S : Finset (ι → ℤ), ∀ P ∈ 𝒦, ∃ c : (ι → ℤ) → ℝ, (∀ l, 0 ≤ c l) ∧ P = ∑ l ∈ S, c l • vecMulVec (fun i => (l i : ℝ)) (fun i => (l i : ℝ)) := by
  first | exact @GlobalTheory.ConeSq.exists_finset_cone | exact GlobalTheory.ConeSq.exists_finset_cone | (intros; apply GlobalTheory.ConeSq.exists_finset_cone <;> assumption)
end

