import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0580
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0632
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0568
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0592
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1139
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0009
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRadNMulLevM
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0112
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.SegmentDerivatives.CuspPairSubGeneric
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0643
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0512
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.ArchBaseChangeOfHyp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1231
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0716
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0126
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import GroundTheory.AutomorphicForms.Bundle0021
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0625
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0590
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarFundamentalDomainOrthogonalSum
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0641
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0626
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.GaugeTopology.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0634
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0627
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrregularProjectionImageNull
section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit segre fibre IsGoodProj IsSheet HermLine IsSmoothHerm sheetDensity maDensity ptsIntegral ptsIntegralAt pot)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat)

noncomputable section

namespace GlobalTheory.CompanionTheory.MixZ.ArchEq

open GlobalTheory.CompanionTheory.MPDict.SmoothRep (rt mem_mchart ev_rt)

variable {m : ℕ} {n : Fin (m + 1) → ℕ} {D : ℕ}

def ratioVec {X : Scheme.{0}} (i : X ⟶ MP ℤ m n) (p : ∀ k, Bk n k) (y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) :
    (Σ k, Bk n k) → ℂ :=
  fun q => ev (i ≫ mpStr ℤ m n) σ₀ (i ⁻¹ᵁ mchart p) ((i.appLE (mchart p) (i ⁻¹ᵁ mchart p) le_rfl).hom (rt p q)) y

theorem mem_ptsIn_of_over {X : Scheme.{0}} (i : X ⟶ MP ℤ m n) {p : ∀ k, Bk n k}
    {y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀} {z : (Σ k, Bk n k) → ℂ} (H : Over i y z) (hp : ∀ k, z ⟨k, p k⟩ ≠ 0) :
    y ∈ ptsIn (i ≫ mpStr ℤ m n) σ₀ (i ⁻¹ᵁ mchart p) :=
  (mem_ptsIn_preimage (f := i) (m := PtsOver.map i rfl _) fun _ => rfl).2 (mem_mchart H hp)

theorem ratioVec_apply {X : Scheme.{0}} (i : X ⟶ MP ℤ m n) {p : ∀ k, Bk n k}
    {y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀} {z : (Σ k, Bk n k) → ℂ} (H : Over i y z) (hp : ∀ k, z ⟨k, p k⟩ ≠ 0)
    (q : Σ k, Bk n k) : ratioVec i p y q = z q / z ⟨q.1, p q.1⟩ :=
  (CxPts.ev_appLE_of_comp (r := i) (m := PtsOver.map i rfl _) (fun _ => rfl) le_rfl _
    (mem_ptsIn_of_over i H hp)).trans (ev_rt H hp q)

theorem sameOrbit_ratioVec {X : Scheme.{0}} (i : X ⟶ MP ℤ m n) {p : ∀ k, Bk n k}
    {y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀} {z : (Σ k, Bk n k) → ℂ} (H : Over i y z) (hp : ∀ k, z ⟨k, p k⟩ ≠ 0) :
    SameOrbit z (ratioVec i p y) := by
  refine ⟨fun k => z ⟨k, p k⟩, hp, funext fun q => ?_⟩
  rw [ratioVec_apply i H hp q, mul_div_cancel₀ _ (hp q.1)]

theorem over_liftOf {X : Scheme.{0}} [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i]
    (y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) : Over i y (liftOf i y) := by
  obtain ⟨z, -, hz⟩ := GlobalTheory.T.complex_point_lifts_to_multicone m n X i y
  have h : ∃ z, Over i y z := ⟨z, hz⟩
  rw [liftOf, dif_pos h]
  exact h.choose_spec

theorem differentiableAt_projCoord {X : Scheme.{0}} [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i]
    (Ψ : LinProj n D) (c : GlobalTheory.AlgChart (i ≫ mpStr ℤ m n) σ₀ D) {y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀}
    (hy : y ∈ c.e.source) {z : (Σ k, Bk n k) → ℂ} (H : Over i y z) (h0 : Ψ (segre z) 0 ≠ 0) :
    DifferentiableAt ℂ (projCoord i Ψ ∘ c.finChart.symm) (c.finChart y) := by
  choose p hp using fun k => exists_block_ne_zero_of_isUnder H k
  have hyW := mem_ptsIn_of_over i H hp
  have hOo : IsOpen (c.finChart.target ∩ c.finChart.symm ⁻¹' ptsIn (i ≫ mpStr ℤ m n) σ₀ (i ⁻¹ᵁ mchart p)) :=
    c.finChart.isOpen_inter_preimage_symm (isOpen_ptsIn _)
  have hv : c.finChart y ∈ c.finChart.target ∩ c.finChart.symm ⁻¹' ptsIn (i ≫ mpStr ℤ m n) σ₀ (i ⁻¹ᵁ mchart p) :=
    ⟨c.finChart.map_source hy, by rwa [Set.mem_preimage, c.finChart.left_inv hy]⟩
  have hl : DifferentiableAt ℂ (fun v => ratioVec i p (c.finChart.symm v)) (c.finChart y) :=
    differentiableAt_pi.2 fun q =>
      (((c.analyticOnNhd_finChart_iff (isOpen_ptsIn _) _).2 (c.holo _ _)) _ hv).differentiableAt
  have hs := ReciprocityTheory.ChartRestriction.G.Geo.segre_differentiableAt hl
  let L := LinearMap.toContinuousLinearMap Ψ
  have hL : DifferentiableAt ℂ (fun v => L (segre (ratioVec i p (c.finChart.symm v)))) (c.finChart y) :=
    L.differentiableAt.comp _ hs
  have hc (a : Fin (D + 1)) := differentiableAt_pi.1 hL a
  have hne : Ψ (segre (ratioVec i p y)) 0 ≠ 0 := by
    obtain ⟨l, hl0, e⟩ := sameOrbit_ratioVec i H hp
    intro h
    apply h0
    rw [segre_orbit e, map_smul, Pi.smul_apply, h, smul_zero]
  have hne' : L (segre (ratioVec i p (c.finChart.symm (c.finChart y)))) 0 ≠ 0 := by
    rw [c.finChart.left_inv hy]
    exact hne
  have hev : (projCoord i Ψ ∘ c.finChart.symm) =ᶠ[nhds (c.finChart y)]
      fun v => ratios Ψ (ratioVec i p (c.finChart.symm v)) := by
    filter_upwards [hOo.mem_nhds hv, (hc 0).continuousAt.eventually_ne hne'] with v hvO hv0
    have H' := over_liftOf i (c.finChart.symm v)
    have hp' : ∀ k, liftOf i (c.finChart.symm v) ⟨k, p k⟩ ≠ 0 := fun k =>
      (H' k (p k)).1.1 (ptsIn_mono (mchart_le p k)
        ((mem_ptsIn_preimage (f := i) (m := PtsOver.map i rfl _) fun _ => rfl).1 hvO.2))
    exact ratios_eq_of_sameOrbit Ψ (sameOrbit_ratioVec i H' hp') hv0
  refine DifferentiableAt.congr_of_eventuallyEq (differentiableAt_pi.2 fun a => ?_) hev
  simp only [ratios, div_eq_mul_inv]
  exact (hc a.succ).mul ((hc 0).inv hne')

theorem volume_image_crit : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (X : Scheme.{0}) [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i] (D : ℕ)
    (Ψ : GlobalTheory.CompanionTheory.MixZ.ArchEq.LinProj n D) (c : GlobalTheory.AlgChart (i ≫ mpStr ℤ m n) σ₀ D),
    volume (GlobalTheory.CompanionTheory.MixZ.ArchEq.projCoord i Ψ '' {y | y ∈ c.e.source ∧
      (∃ z, GlobalTheory.CompanionTheory.MixZ.ArchEq.Over i y z ∧ Ψ (segre z) 0 ≠ 0) ∧ ¬ GlobalTheory.CompanionTheory.MixZ.ArchEq.IsRegAt i Ψ c y}) = 0 := by
  intro m n X _ i _ D Ψ c
  set A := {y | y ∈ c.e.source ∧ (∃ z, Over i y z ∧ Ψ (segre z) 0 ≠ 0) ∧ ¬ IsRegAt i Ψ c y} with hA
  have e : projCoord i Ψ '' A = (projCoord i Ψ ∘ c.finChart.symm) '' (c.finChart '' A) := by
    rw [Set.image_image]
    exact Set.image_congr fun y hy => by
      simp only [Function.comp_apply, c.finChart.left_inv (show y ∈ c.finChart.source from hy.1)]
  rw [e]
  refine addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume
    (f' := fun v => (fderiv ℂ (projCoord i Ψ ∘ c.finChart.symm) v).restrictScalars ℝ) ?_ ?_
  · rintro _ ⟨y, ⟨hy, ⟨z, hz, h0⟩, -⟩, rfl⟩
    exact ((differentiableAt_projCoord i Ψ c hy hz h0).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  · rintro _ ⟨y, ⟨-, -, hc⟩, rfl⟩
    have h0 := not_not.1 hc
    have hdet : ((fderiv ℂ (projCoord i Ψ ∘ c.finChart.symm) (c.finChart y)).restrictScalars ℝ).det =
        Algebra.norm ℝ (LinearMap.det (fderiv ℂ (projCoord i Ψ ∘ c.finChart.symm) (c.finChart y) :
          (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))) :=
      LinearMap.det_restrictScalars (f := (fderiv ℂ (projCoord i Ψ ∘ c.finChart.symm) (c.finChart y) :
        (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ)))
    rw [hdet, h0, Algebra.norm_complex_apply, map_zero]

end GlobalTheory.CompanionTheory.MixZ.ArchEq
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsClosedUnipotentRadicalStabilizer
section
noncomputable section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.CompanionTheory.QKAvg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.QKAvg

theorem isClosed_radN : ∀ (D : D7) (B W : HSp D) (t : ℕ) (d : HypDec B W t),
    IsClosed (radN d : Set (GlobalTheory.RegSW.stab d)) := by
  intro D B W t d
  have e : (radN d : Set (GlobalTheory.RegSW.stab d)) =
      (Subtype.val : GlobalTheory.RegSW.stab d → GA D B) ⁻¹' (GlobalTheory.MixPer.radX d : Set (GA D B)) := by
    ext q
    constructor
    · rintro ⟨c, b, h⟩
      exact (GlobalTheory.MixPer.Decomp.mem_radX_iff d).2 ⟨b, c, h.trans (d.nC_mul_nB b c)⟩
    · intro h
      obtain ⟨b, c, h⟩ := (GlobalTheory.MixPer.Decomp.mem_radX_iff d).1 h
      exact ⟨c, b, h.trans (d.nC_mul_nB b c).symm⟩
  rw [e]
  exact (GlobalTheory.JacMeas.isClosed_radX d).preimage continuous_subtype_val

end GlobalTheory.CompanionTheory.QKAvg
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsGenericOfInjective
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.JHMult Zc

namespace GlobalTheory.CompanionTheory.CuspStd

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def EmbW {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (G : Representation ℂ (GL (Fin N) k) V)
    (W : List (IrrGL k)) : Prop :=
  ∃ (h : ∑ a, (W.get a).1 = N) (f : G.IntertwiningMap (prodIrr W.get h)), Function.Injective f

def Good (W : List (IrrGL k)) : Prop := W.Pairwise fun u v => v ≠ u.nu 1

def prod₂MapR {r t : ℕ} {U X Y : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] (π₁ : Representation ℂ (GL (Fin r) k) U)
    {π₂ : Representation ℂ (GL (Fin t) k) X} {π₂' : Representation ℂ (GL (Fin t) k) Y}
    (f : π₂.IntertwiningMap π₂') : (prod₂ π₁ π₂).IntertwiningMap (prod₂ π₁ π₂') :=
  parIndMap _ (compMap (ρ := extTensor π₁ π₂) (σ := extTensor π₁ π₂')
    ⟨TensorProduct.map LinearMap.id f.toLinearMap, fun g => by
      ext u x
      exact congrArg (fun b => π₁ g.1 u ⊗ₜ[ℂ] b) (f.isIntertwining _ _ g.2 x)⟩ _)

def prod₂MapL {r t : ℕ} {U X Y : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] {π₁ : Representation ℂ (GL (Fin r) k) X}
    {π₁' : Representation ℂ (GL (Fin r) k) Y} (f : π₁.IntertwiningMap π₁')
    (π₂ : Representation ℂ (GL (Fin t) k) U) : (prod₂ π₁ π₂).IntertwiningMap (prod₂ π₁' π₂) :=
  parIndMap _ (compMap (ρ := extTensor π₁ π₂) (σ := extTensor π₁' π₂)
    ⟨TensorProduct.map f.toLinearMap LinearMap.id, fun g => by
      ext x u
      exact congrArg (fun b => b ⊗ₜ[ℂ] π₂ g.2 u) (f.isIntertwining _ _ g.1 x)⟩ _)

def HasNG {N : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (GL (Fin N) k) V) (π' : Representation ℂ (GL (Fin N) k) W) : Prop :=
  ∃ F : π.IntertwiningMap π', ¬ IsGeneric F.ker.toRepresentation

def KerNG (W W' : List (IrrGL k)) : Prop :=
  ∀ (N : ℕ) (h : ∑ a, (W.get a).1 = N) (h' : ∑ a, (W'.get a).1 = N), HasNG (prodIrr W.get h) (prodIrr W'.get h')

theorem prodIrr_congr {p q N : ℕ} (hpq : p = q) (x : Fin p → IrrGL k) (y : Fin q → IrrGL k)
    (hxy : ∀ i, x i = y (Fin.cast hpq i)) (hx : ∑ a, (x a).1 = N) (hy : ∑ a, (y a).1 = N) :
    Nonempty ((prodIrr x hx).Equiv (prodIrr y hy)) := by
  subst hpq
  obtain rfl : x = y := funext hxy
  exact ⟨.refl _⟩

theorem append_get {α : Type*} (A B : List α) (i : Fin (A.length + B.length)) :
    Fin.append A.get B.get i = (A ++ B).get (Fin.cast (List.length_append (as := A) (bs := B)).symm i) := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · rw [Fin.append_left]
    simp [List.getElem_append]
  · rw [Fin.append_right]
    simp [List.getElem_append]

theorem word_append_aux₁ (A B : List (IrrGL k)) {r t : ℕ} (hA : ∑ a, (A.get a).1 = r) (hB : ∑ a, (B.get a).1 = t)
    (h' : ∑ a, (Fin.append A.get B.get a).1 = r + t) :
    Nonempty ((prod₂ (prodIrr A.get hA) (prodIrr B.get hB)).Equiv (prodIrr (Fin.append A.get B.get) h')) :=
  GlobalTheory.T.product_irreducible_append_equiv k _ _ r t A.get B.get hA hB h'

theorem word_append_aux₂ (A B : List (IrrGL k)) {N : ℕ} (h : ∑ a, ((A ++ B).get a).1 = N)
    (h' : ∑ a, (Fin.append A.get B.get a).1 = N) :
    Nonempty ((prodIrr (Fin.append A.get B.get) h').Equiv (prodIrr (A ++ B).get h)) :=
  prodIrr_congr (List.length_append (as := A) (bs := B)).symm (Fin.append A.get B.get) (A ++ B).get
    (append_get A B) h' h

end GlobalTheory.CompanionTheory.CuspStd
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSubquotientIff
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.OnePart

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem hasSat_iff {π : CuspSub E n} {w : HeightOneSpectrum (𝓞 E)} {τ : SmIrr (GL (Fin n) (w.adicCompletion E))}
    (hτ : π.IsLocComp w τ) (B : Multiset ℂˣ) : (CG.mk π).HasSat w B ↔ GlobalTheory.LFun.HasSatGL w τ.ρ B := by
  refine ⟨fun h => ?_, fun h => GlobalTheory.HeightCounting.Blocks.hasSatGL_locRep hτ h⟩
  obtain ⟨α, hαB, hα⟩ := GlobalTheory.LFun.SphComp.hasSatake_of_isLocComp π h hτ
  rw [← hαB]
  exact GlobalTheory.LFun.SatBridge.hasSatGL_of_hasSatake E w n _ _ _ hα

theorem isSubquotient_iff {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {π : Representation ℂ G W} [ρ.IsIrreducible] [π.IsIrreducible] :
    GlobalTheory.SmGL.IsSubquotient π ρ ↔ Nonempty (π.Equiv ρ) := by
  constructor
  · intro h
    obtain ⟨e, he⟩ := GroundTheory.Automorphic.IsSubquotient.exists_bijective (π := π) (ρ := ρ) h
    exact ⟨GlobalTheory.LocGL.equivOfBijective e he⟩
  · rintro ⟨e⟩
    exact .of_surjective e.symm.toIntertwiningMap e.symm.toLinearEquiv.surjective

theorem oneRead : OneRead := by
  intro E _ _ _ n hn π D hD
  obtain ⟨c, N, h, V, σ, m, pos, disc, loc, inf⟩ := D
  obtain ⟨hc, hv⟩ := hD
  dsimp only at hc hv
  subst hc
  obtain ⟨e, he⟩ := hv 0
  obtain ⟨M, rfl⟩ : ∃ M, N = fun _ => M := ⟨N 0, funext fun i => by rw [Subsingleton.elim i 0]⟩
  have e' : M = n := e
  subst e'
  have he' : V 0 = π.V := he
  obtain ⟨s, rfl⟩ : ∃ s : ∀ w : HeightOneSpectrum (𝓞 E), SmIrr (GL (Fin M) (w.adicCompletion E)), σ = fun _ => s :=
    ⟨σ 0, funext fun i => by rw [Subsingleton.elim i 0]⟩
  have hl : ∀ w, π.IsLocComp w (s w) := fun w => ((cuspSub_iff π).2.1 w _).1 (he' ▸ loc 0 w)
  refine ⟨fun w B => ?_, fun w => ⟨_, hl w⟩, fun w τ hτ P => ?_⟩
  · rw [hasSat_iff (hl w)]
    constructor
    · intro hB
      exact ⟨fun _ => B, fun _ => ⟨hB.1, hB⟩, by simp⟩
    · rintro ⟨b, hb, rfl⟩
      simpa using (hb 0).2
  · obtain ⟨φ⟩ := GlobalTheory.LocGL.nonempty_equiv_multiProd_one (s w).smooth (GlobalTheory.SmGL.stdBlocks (fun _ : Fin 1 => M) h)
      fun a i => Fin.ext (by rw [GlobalTheory.SmGL.stdBlocks_val, Subsingleton.elim a 0]; simp)
    obtain ⟨u⟩ := LocUniq.isLocComp_unique π w _ _ (hl w) hτ
    have := (s w).irred
    have := P.irred
    have hφ : ∀ {X : Type} [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (GL (Fin M) (w.adicCompletion E)) X),
        GlobalTheory.SmGL.IsSubquotient ρ (s w).ρ → GlobalTheory.SmGL.IsSubquotient ρ (GlobalTheory.UnitaryBC.locProd h w fun _ => s w) := fun ρ hρ =>
      hρ.trans (.of_surjective φ.symm.toIntertwiningMap φ.symm.toLinearEquiv.surjective)
    constructor
    · intro hP
      have h1 : GlobalTheory.SmGL.IsSubquotient P.ρ (s w).ρ :=
        hP.trans (.of_surjective φ.toIntertwiningMap φ.toLinearEquiv.surjective)
      obtain ⟨e₁⟩ := isSubquotient_iff.1 h1
      exact ⟨e₁.trans u⟩
    · rintro ⟨e₁⟩
      exact hφ _ (isSubquotient_iff.2 ⟨e₁.trans u.symm⟩)

end GlobalTheory.CompanionTheory.OnePart

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsotropicFramesSumByOrbitStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf
open GlobalTheory.CompanionTheory.SW.ThetaStage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropic_frames_sum_by_orbit : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (n : ℕ) (rr : framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E) → UJ (σ : E →+* E) (hypOne J)), (∀ q, gact σ (rr q) q.1 = e0 E M) → ∀ f : (Fin (n + 1) → Fin (M + 2) → E) → ℝ≥0∞, ∑' X : framesE σ (hypOne J) (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) E), f X.1 = ∑' q : framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E), ∑' X : framesOne σ J n, f (gact σ (rr q)⁻¹ X.1) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf.tsum_framesOne | exact GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf.tsum_framesOne | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf.tsum_framesOne <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IteratedIntegralsFourFactors
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.ColumnSplitting

section Fub4Proof

variable {α β γ δ : Type} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]

theorem integral_prod_three (b : Measure β) (c : Measure γ) (a : Measure α) [SFinite a] [SFinite b] [SFinite c]
    (g : β × γ × α → ℂ) (hg : Integrable g (b.prod (c.prod a))) :
    ∫ q, g q ∂(b.prod (c.prod a)) = ∫ h, ∫ u, ∫ k, g (h, u, k) ∂a ∂c ∂b := by
  rw [integral_prod _ hg]
  refine integral_congr_ae ?_
  filter_upwards [hg.prod_right_ae] with h hh
  exact integral_prod _ hh

theorem integral_prod_four (e : Measure δ) (b : Measure β) (c : Measure γ) (a : Measure α)
    [SFinite a] [SFinite b] [SFinite c] [SFinite e]
    (g : δ × β × γ × α → ℂ) (hg : Integrable g (e.prod (b.prod (c.prod a)))) :
    ∫ q, g q ∂(e.prod (b.prod (c.prod a))) = ∫ y, ∫ h, ∫ u, ∫ k, g (y, h, u, k) ∂a ∂c ∂b ∂e := by
  rw [integral_prod _ hg]
  refine integral_congr_ae ?_
  filter_upwards [hg.prod_right_ae] with y hy
  exact integral_prod_three b c a _ hy

theorem lintegral_prod_four (e : Measure δ) (b : Measure β) (c : Measure γ) (a : Measure α)
    [SFinite a] [SFinite b] [SFinite c] [SFinite e]
    (g : δ × β × γ × α → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ q, g q ∂(e.prod (b.prod (c.prod a))) = ∫⁻ y, ∫⁻ h, ∫⁻ u, ∫⁻ k, g (y, h, u, k) ∂a ∂c ∂b ∂e := by
  rw [lintegral_prod _ hg.aemeasurable]
  refine lintegral_congr fun y => ?_
  have h1 : Measurable fun q : β × γ × α => g (y, q) := hg.comp measurable_prodMk_left
  rw [lintegral_prod _ h1.aemeasurable]
  refine lintegral_congr fun h => ?_
  have h2 : Measurable fun q : γ × α => g (y, h, q) := h1.comp measurable_prodMk_left
  exact lintegral_prod _ h2.aemeasurable

def swapFour (α β γ δ : Type) [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ] :
    (α × β × γ × δ) ≃ᵐ (δ × β × γ × α) where
  toFun p := (p.2.2.2, p.2.1, p.2.2.1, p.1)
  invFun p := (p.2.2.2, p.2.1, p.2.2.1, p.1)
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := by
    dsimp only [Equiv.coe_fn_mk]
    fun_prop
  measurable_invFun := by
    dsimp only [Equiv.coe_fn_symm_mk]
    fun_prop

theorem measurePreserving_swapFour (a : Measure α) (b : Measure β) (c : Measure γ) (e : Measure δ)
    [SFinite a] [SFinite b] [SFinite c] [SFinite e] :
    MeasurePreserving (swapFour α β γ δ) (a.prod (b.prod (c.prod e))) (e.prod (b.prod (c.prod a))) := by
  have p1 : MeasurePreserving (Prod.map id (MeasurableEquiv.prodAssoc (α := β) (β := γ) (γ := δ)).symm)
      (a.prod (b.prod (c.prod e))) (a.prod ((b.prod c).prod e)) :=
    (MeasurePreserving.id a).prod ((measurePreserving_prodAssoc b c e).symm _)
  have p2 : MeasurePreserving (MeasurableEquiv.prodAssoc (α := α) (β := β × γ) (γ := δ)).symm
      (a.prod ((b.prod c).prod e)) ((a.prod (b.prod c)).prod e) :=
    (measurePreserving_prodAssoc a (b.prod c) e).symm _
  have p3 : MeasurePreserving Prod.swap ((a.prod (b.prod c)).prod e) (e.prod (a.prod (b.prod c))) :=
    Measure.measurePreserving_swap
  have p4 : MeasurePreserving (Prod.map id Prod.swap) (e.prod (a.prod (b.prod c))) (e.prod ((b.prod c).prod a)) :=
    (MeasurePreserving.id e).prod Measure.measurePreserving_swap
  have p5 : MeasurePreserving (Prod.map id (MeasurableEquiv.prodAssoc (α := β) (β := γ) (γ := α)))
      (e.prod ((b.prod c).prod a)) (e.prod (b.prod (c.prod a))) :=
    (MeasurePreserving.id e).prod (measurePreserving_prodAssoc b c a)
  exact (((p5.comp p4).comp p3).comp p2).comp p1

end Fub4Proof

theorem iterated_integrals_four_factors_holds : Fub4 := by
  intro α β γ δ _ _ _ _ a b c e _ _ _ _
  have hm := measurePreserving_swapFour a b c e
  constructor
  · intro f hf
    let g : δ × β × γ × α → ℂ := fun q => f (q.2.2.2, q.2.1, q.2.2.1, q.1)
    have hfg : g ∘ swapFour α β γ δ = f := rfl
    have hg : Integrable g (e.prod (b.prod (c.prod a))) :=
      (hm.integrable_comp_emb (swapFour α β γ δ).measurableEmbedding).1 (by rwa [hfg])
    calc ∫ p, f p ∂(a.prod (b.prod (c.prod e)))
        = ∫ p, g (swapFour α β γ δ p) ∂(a.prod (b.prod (c.prod e))) := rfl
      _ = ∫ q, g q ∂(e.prod (b.prod (c.prod a))) :=
          hm.integral_comp (swapFour α β γ δ).measurableEmbedding g
      _ = _ := integral_prod_four e b c a g hg
  · intro f hf
    let g : δ × β × γ × α → ℝ≥0∞ := fun q => f (q.2.2.2, q.2.1, q.2.2.1, q.1)
    have hg : Measurable g := hf.comp (swapFour α β γ δ).symm.measurable
    calc ∫⁻ p, f p ∂(a.prod (b.prod (c.prod e)))
        = ∫⁻ p, g (swapFour α β γ δ p) ∂(a.prod (b.prod (c.prod e))) := rfl
      _ = ∫⁻ q, g q ∂(e.prod (b.prod (c.prod a))) := hm.lintegral_comp hg
      _ = _ := lintegral_prod_four e b c a g hg

end GlobalTheory.CompanionTheory.ColumnSplitting

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaCoordinatesBoundedRegionStatement
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwasawa_coordinates_bounded_region : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (x : F) (m n L : ℤ) (κ : GL (Fin 2) F) (R : ℝ) (t : Fˣ), κ ∈ GLnLocal.integralGL F 2 → R ≤ (residueCard F : ℝ) ^ L → (Ad3.uni2 x * Ad3.dg2 (unifUnit F ^ m) (unifUnit F ^ n) * κ)⁻¹ ∈ Ad3.LFS.om R t → m ≤ L ∧ n ≤ L ∧ (modulus x : ℝ) ≤ (residueCard F : ℝ) ^ (L - m) ∧ (modulus (t : F) : ℝ) * (residueCard F : ℝ) ^ (-n) ≤ (residueCard F : ℝ) ^ L := by
  first | exact @GlobalTheory.CompanionTheory.LFCoords.coords | exact GlobalTheory.CompanionTheory.LFCoords.coords | (intros; apply GlobalTheory.CompanionTheory.LFCoords.coords <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaDecompositionGlTwoHolds
section
noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel ENNReal

namespace GlobalTheory.CompanionTheory.GIntIw

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem exists_zpow_mul_ord_zero (a : Fˣ) :
    ∃ (m : ℤ) (e : Fˣ), ord (e : F) = 0 ∧ a = unifUnit F ^ m * e := by
  refine ⟨ord (a : F), (unifUnit F ^ ord (a : F))⁻¹ * a, ?_, by group⟩
  have h := ord_units_mul ((unifUnit F ^ ord (a : F))⁻¹) a
  rw [h, ord_units_inv, ord_unifUnit_zpow]
  simp

theorem diag_unit_mem_integral_gl_two {e f : Fˣ} (he : ord (e : F) = 0) (hf : ord (f : F) = 0) :
    Ad3.dg2 e f ∈ GLnLocal.integralGL F 2 := by
  rw [GLnLocal.mem_integralGL_iff]
  have h1 : (e : F) ∈ 𝒪[F] := GlobalTheory.CompanionTheory.RankinTorusVanishing.mem_of_ord_nonneg he.ge
  have h2 : (f : F) ∈ 𝒪[F] := GlobalTheory.CompanionTheory.RankinTorusVanishing.mem_of_ord_nonneg hf.ge
  have h3 : ((e⁻¹ : Fˣ) : F) ∈ 𝒪[F] :=
    GlobalTheory.CompanionTheory.RankinTorusVanishing.mem_of_ord_nonneg (by rw [ord_units_inv, he]; simp)
  have h4 : ((f⁻¹ : Fˣ) : F) ∈ 𝒪[F] :=
    GlobalTheory.CompanionTheory.RankinTorusVanishing.mem_of_ord_nonneg (by rw [ord_units_inv, hf]; simp)
  have h3' : (e : F)⁻¹ ∈ 𝒪[F] := by simpa using h3
  have h4' : (f : F)⁻¹ ∈ 𝒪[F] := by simpa using h4
  constructor <;> intro i j <;> fin_cases i <;> fin_cases j <;>
    simp [Ad3.dg2, h1, h2, h3', h4', zero_mem, one_mem]

theorem iwasawa_decomposition_gl_two :
    ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
      (g : GL (Fin 2) F), ∃ (x : F) (m n : ℤ), ∃ κ ∈ GLnLocal.integralGL F 2,
        g = Ad3.uni2 x * Ad3.dg2 (unifUnit F ^ m) (unifUnit F ^ n) * κ := by
  intro F _ _ _ _ g
  obtain ⟨x, a, d, k, hk, rfl⟩ := GlobalTheory.CompanionTheory.RankinTorusVanishing.exists_iwasawa2 g
  obtain ⟨m, e, he, rfl⟩ := exists_zpow_mul_ord_zero a
  obtain ⟨n, f, hf, rfl⟩ := exists_zpow_mul_ord_zero d
  refine ⟨x, m, n, Ad3.dg2 e f * k,
    (GLnLocal.integralGL F 2).mul_mem (diag_unit_mem_integral_gl_two he hf) hk, ?_⟩
  rw [← GlobalTheory.CompanionTheory.RankinTorusVanishing.diagonal_mul_diagonal_alt]
  simp only [mul_assoc]

end GlobalTheory.CompanionTheory.GIntIw
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaSumMeasureEstimateStatement
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwasawa_sum_measure_estimate : ∀ {X : Type} [MeasurableSpace X] (μ : Measure X) (q A τ : ℝ) (L : ℤ) (c T₁ T₂ : ℝ≥0∞) (S : ℤ → ℤ → Set X) (Φ : X → ℝ≥0∞), 1 < q → 0 ≤ A → 0 < τ → (∀ m n, MeasurableSet (S m n)) → (∀ m n, n ≤ L → μ (S m n) ≤ ENNReal.ofReal (q ^ (L - n)) * c) → (∑' m : ℤ, (if m ≤ L then ENNReal.ofReal (q ^ ((m : ℝ) / 4)) else 0)) ≤ T₁ → (∑' n : ℤ, (if τ * q ^ (-n) ≤ q ^ L then ENNReal.ofReal (q ^ (-(n : ℝ) / 4)) else 0)) ≤ T₂ → (∀ y, Φ y ≠ 0 → ∃ m n : ℤ, m ≤ L ∧ n ≤ L ∧ τ * q ^ (-n) ≤ q ^ L ∧ y ∈ S m n ∧ Φ y ≤ ENNReal.ofReal (A * q ^ (((n : ℝ) - m) / 4) * q ^ (((m : ℝ) + n) / 2))) → ∫⁻ y, Φ y ∂μ ≤ ENNReal.ofReal (A * q ^ L) * T₁ * T₂ * c := by
  first | exact @GlobalTheory.CompanionTheory.ShellSum.lintegral_le_of_shells | exact GlobalTheory.CompanionTheory.ShellSum.lintegral_le_of_shells | (intros; apply GlobalTheory.CompanionTheory.ShellSum.lintegral_le_of_shells <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelFunctionalEquationOfTwoVariableStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_functional_equation_of_two_variable : Ad3.R.A7 → Ad3.R.A8 := by
  first | exact @GlobalTheory.CompanionTheory.RSKernel.kernel_local_functional_equation | exact GlobalTheory.CompanionTheory.RSKernel.kernel_local_functional_equation | (intros; apply GlobalTheory.CompanionTheory.RSKernel.kernel_local_functional_equation <;> assumption)
end

