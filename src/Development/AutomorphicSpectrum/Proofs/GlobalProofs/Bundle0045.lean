import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0044
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.GlRelationsDerivativePreserved
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteSpectrumOfResidual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1281
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0177
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import ReciprocityTheory.Hypotheses.GalCoh
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.Transport
import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.Bundle0002
import GroundTheory.ProfiniteCohomology.RestrictedRamification.IsUnramifiedOutsideIffLeMaxUnramifiedOutside
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0011
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAffineOpenAndIsPushout
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0004

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdelicOpenNeighbourhoodProduct
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult MeasureTheory NumberField Matrix
open scoped TensorProduct Topology InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.CuspNbhd

open GlobalTheory.AdelicU

theorem real_mul_level_mem_nhds : ∀ (D : D7) (V : HSp D) (U : Subgroup (GA D V)), IsOpen (U : Set (GA D V)) → ∀ N ∈ 𝓝 (1 : GA D V), {g : GA D V | ∃ r k : GA D V, r ∈ GinfC V ∧ r ∈ N ∧ k ∈ U ∧ k ∈ GfC V ∧ g = r * k} ∈ 𝓝 (1 : GA D V) := by
  intro D V U hU N hN
  have hr : Continuous fun g : GA D V =>
      ofInf D.sp.cm.sig V.gram (projInf D.sp.cm.sig V.gram g) :=
    (continuous_ofInf _ _).comp (continuous_projInf _ _)
  have hk : Continuous fun g : GA D V =>
      ofFin D.sp.cm.sig V.gram (projFin D.sp.cm.sig V.gram g) :=
    (continuous_ofFin _ _).comp (continuous_projFin _ _)
  have h1 : ∀ᶠ g : GA D V in 𝓝 1, ofInf D.sp.cm.sig V.gram (projInf D.sp.cm.sig V.gram g) ∈ N := by
    have := hr.continuousAt (x := (1 : GA D V))
    simp only [ContinuousAt, map_one] at this
    exact this hN
  have h2 : ∀ᶠ g : GA D V in 𝓝 1, ofFin D.sp.cm.sig V.gram (projFin D.sp.cm.sig V.gram g) ∈ U := by
    have := hk.continuousAt (x := (1 : GA D V))
    simp only [ContinuousAt, map_one] at this
    exact this (hU.mem_nhds U.one_mem)
  filter_upwards [h1, h2] with g hg1 hg2
  exact ⟨_, _, mem_infPts.2 (by simp), hg1, hg2, mem_finPts.2 (by simp),
    (ofInf_projInf_mul_ofFin_projFin D.sp.cm.sig V.gram g).symm⟩

end GlobalTheory.CompanionTheory.CuspNbhd
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.BernsteinZelevinskyFinitenessStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bernstein_zelevinsky_finiteness : GlobalTheory.Published.BernsteinZelevinskyFiniteness := by
  first | exact @GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness | exact GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness | (intros; apply GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.GlRelationsDerivativePreservedStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gl_relations_triangular_annihilation : ∀ (W Q : Type) [AddCommGroup W] [Module ℂ W] [AddCommGroup Q] [Module ℂ Q] (c N : ℕ) (n : Fin c → ℕ) (h : ∑ i, n i = N)
    (Xf : Fin N → Fin N → Module.End ℂ W), Formalism.REAL.GlRel Xf → ∀ Wn : Submodule ℂ W, (∀ p q, ∀ F ∈ Wn, Xf p q F ∈ Wn) →
    ∀ L : W →ₗ[ℂ] Q, (∀ p q, GlobalTheory.SmGL.blk (GlobalTheory.SmGL.stdBlocks n h) p < GlobalTheory.SmGL.blk (GlobalTheory.SmGL.stdBlocks n h) q → ∀ F ∈ Wn, L (Xf p q F) = 0) →
    ∀ W₀ : Set W, W₀ ⊆ Wn → (∀ v : ℂ, ∃ s : ℂ, ∀ F ∈ W₀, Formalism.REAL.qdet Xf v F = s • F) →
    ∀ (i : Fin c) (w : ℂ), ∃ q : Polynomial ℂ, q.Monic ∧ ∀ F ∈ W₀,
      L (Polynomial.aeval (Formalism.REAL.qdet (fun p q : Fin (n i) => Xf (GlobalTheory.SmGL.stdBlocks n h ⟨i, p⟩) (GlobalTheory.SmGL.stdBlocks n h ⟨i, q⟩)) w) q F) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Dblock.CentreManyBlocks.monic_relations_along_block | exact GlobalTheory.CompanionTheory.Dblock.CentreManyBlocks.monic_relations_along_block | (intros; apply GlobalTheory.CompanionTheory.Dblock.CentreManyBlocks.monic_relations_along_block <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.HolomorphicGluingLocalFunctions
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts

noncomputable section

namespace GlobalTheory.CompanionTheory.Gaga

open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.ChartGlue

variable {X : Scheme.{0}} {s : X ⟶ Sp ℂ} {D : ℕ}

theorem valAt'_eq_ev (U : X.Opens) (f : Γ(X, U)) (y : CxPts s (RingHom.id ℂ)) :
    valAt' y.1 U f = ev s (RingHom.id ℂ) U f y := rfl

theorem comp_eq_id (y : CxPts s (RingHom.id ℂ)) : y.1 ≫ s = 𝟙 _ := by
  rw [y.2]
  simp [spMap]

theorem isHolTo_chart (c : AlgChart s (RingHom.id ℂ) D) (W : X.Opens)
    (ψ : (Fin D → ℂ) ≃L[ℂ] V D) :
    IsHolTo (ψ ⁻¹' (c.e.target ∩ c.e.symm ⁻¹' ptsIn s (RingHom.id ℂ) W))
      (fun b => (c.e.symm (ψ b)).1) := by
  intro U f
  have hset : ψ ⁻¹' (c.e.target ∩ c.e.symm ⁻¹' (ptsIn s (RingHom.id ℂ) W ∩ ptsIn s (RingHom.id ℂ) U)) =
      {b | b ∈ ψ ⁻¹' (c.e.target ∩ c.e.symm ⁻¹' ptsIn s (RingHom.id ℂ) W) ∧
        ⊤ ≤ (Opens.map (c.e.symm (ψ b)).1.base).obj U} := by
    ext b
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h1, h2⟩, h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h1, h2, h3⟩
  refine ⟨?_, ?_⟩
  · have ho := (c.e.isOpen_inter_preimage_symm
      ((isOpen_ptsIn (p := s) (σ := RingHom.id ℂ) W).inter (isOpen_ptsIn U))).preimage ψ.continuous
    rw [hset] at ho
    exact ho
  · have hd := ((c.holo U f).comp ψ.differentiableOn (fun b hb => hb)).mono
      (fun b (hb : b ∈ {b | b ∈ ψ ⁻¹' (c.e.target ∩ c.e.symm ⁻¹' ptsIn s (RingHom.id ℂ) W) ∧
        ⊤ ≤ (Opens.map (c.e.symm (ψ b)).1.base).obj U}) => (⟨hb.1.1, hb.2⟩ :
          ψ b ∈ c.e.target ∩ c.e.symm ⁻¹' ptsIn s (RingHom.id ℂ) U))
    refine hd.congr ?_
    intro b _
    exact valAt'_eq_ev U f _

theorem exists_mem_holSec : ∀ (X : Scheme.{0}) (s : X ⟶ Sp ℂ) (D : ℕ), SmoothOfRelativeDimension D s → ∀ (R : AnRead s (RingHom.id ℂ) D), ∀ (L : LB X), L.IsLB → ∀ h : L.ι → (Sp ℂ ⟶ X) → ℂ, (∀ (i : L.ι) (m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)), IsOpen B → IsHolTo B y → (∀ b ∈ B, y b ≫ s = 𝟙 _ ∧ ⊤ ≤ y b ⁻¹ᵁ L.U i) → DifferentiableOn ℂ (fun b => h i (y b)) B) → (∀ (i j : L.ι) (x : Sp ℂ ⟶ X), x ≫ s = 𝟙 _ → ⊤ ≤ x ⁻¹ᵁ (L.U i ⊓ L.U j) → h i x = valAt' x (L.U i ⊓ L.U j) (L.g i j).val * h j x) → ∃ σ ∈ R.holSec L, ∀ (i : L.ι), ∀ y ∈ ptsIn s (RingHom.id ℂ) (L.U i), σ i y = h i y.1 := by
  intro X s D _ R L _ h hhol hcoc
  classical
  obtain ⟨ψ⟩ : Nonempty ((Fin D → ℂ) ≃L[ℂ] V D) := ⟨(EuclideanSpace.equiv (Fin D) ℂ).symm⟩
  refine ⟨fun i y => if y ∈ ptsIn s (RingHom.id ℂ) (L.U i) then h i y.1 else 0, ?_, ?_⟩
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro i j y hi hj
      have hij : y ∈ ptsIn s (RingHom.id ℂ) (L.U i ⊓ L.U j) := mem_ptsIn_inf.2 ⟨hi, hj⟩
      simp only [if_pos hi, if_pos hj]
      rw [hcoc i j y.1 (comp_eq_id y) hij, valAt'_eq_ev]
      rfl
    · intro i y hy
      simp only [if_neg hy]
    · intro i k
      have hB : IsOpen (ψ ⁻¹' ((R.chart k).e.target ∩
          (R.chart k).e.symm ⁻¹' ptsIn s (RingHom.id ℂ) (L.U i))) :=
        ((R.chart k).e.isOpen_inter_preimage_symm (isOpen_ptsIn _)).preimage ψ.continuous
      have hd := hhol i D _ (fun b => ((R.chart k).e.symm (ψ b)).1) hB
        (isHolTo_chart (R.chart k) (L.U i) ψ) (fun b hb => ⟨comp_eq_id _, hb.2⟩)
      have hd2 := hd.comp ψ.symm.differentiableOn (fun v hv => by
        show ψ (ψ.symm v) ∈ (R.chart k).e.target ∩
          (R.chart k).e.symm ⁻¹' ptsIn s (RingHom.id ℂ) (L.U i)
        rw [ψ.apply_symm_apply]
        exact hv)
      refine hd2.congr ?_
      intro v hv
      have hv2 : (R.chart k).e.symm v ∈ ptsIn s (RingHom.id ℂ) (L.U i) := hv.2
      simp [Function.comp, hv2]
  · intro i y hy
    simp only [if_pos hy]

end GlobalTheory.CompanionTheory.Gaga
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.NSEqFixingSubgroup
section
noncomputable section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal Formalism.ConjugateSelfDual

namespace GlobalTheory.CompanionTheory.Hypotheses₂

theorem NS_eq_fixingSubgroup (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (S : Set (HeightOneSpectrum (𝓞 F))) :
    NS Ω S = (maxUnramifiedOutside F Ω S).fixingSubgroup :=
  le_antisymm (GlobalTheory.T.normal_subgroup_le_unramified_fixing F Ω S) (GlobalTheory.T.galois_unramified_outside_cohomology F Ω S)

theorem exists_gsEquiv (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (S : Set (HeightOneSpectrum (𝓞 F))) : Nonempty (GS Ω S ≃ₜ* galUnramifiedOutside F Ω S) := by
  have : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  let E := maxUnramifiedOutside F Ω S
  let φ : G F Ω →* Gal(E/F) := AlgEquiv.restrictNormalHom E
  have hφs : Function.Surjective φ := AlgEquiv.restrictNormalHom_surjective Ω
  have hker : φ.ker = NS Ω S := by
    rw [NS_eq_fixingSubgroup F Ω S]
    ext σ
    rw [MonoidHom.mem_ker, IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · intro h x hx
      have h1 := AlgEquiv.restrictNormal_commutes σ E (⟨x, hx⟩ : E)
      have h2 : σ.restrictNormal E = 1 := h
      rw [h2] at h1
      exact h1.symm
    · intro h
      apply AlgEquiv.ext
      intro x
      apply Subtype.ext
      exact (AlgEquiv.restrictNormal_commutes σ E x).trans (h x.1 x.2)
  have hφc : Continuous φ := InfiniteGalois.restrictNormalHom_continuous E
  let q : GS Ω S ≃* Gal(E/F) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans (QuotientGroup.quotientKerEquivOfSurjective φ hφs)
  have hq : Continuous q := continuous_coinduced_dom.2 hφc
  have : CompactSpace (G F Ω) := inferInstance
  have : CompactSpace (GS Ω S) := Quotient.compactSpace
  exact ⟨{ q with
    continuous_toFun := hq
    continuous_invFun := Continuous.continuous_symm_of_equiv_compact_to_t2 (f := q.toEquiv) hq }⟩

theorem globalFiniteness : ReciprocityTheory.Gal.GlobalFiniteness := by
  intro F Ω _ _ _ _ _ l hl r M _ _ _ _ _ S rhoS hr hS hc
  obtain ⟨e0⟩ := exists_gsEquiv F Ω (S : Set (HeightOneSpectrum (𝓞 F)))
  let e : galUnramifiedOutside F Ω (S : Set (HeightOneSpectrum (𝓞 F))) ≃ₜ* GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) :=
    e0.symm
  have hc' := ReciprocityTheory.Neutral.Bridge.contAction_comp e hc
  let rho' : Representation (ZMod (l ^ r)) (galUnramifiedOutside F Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M :=
    rhoS.comp (e : galUnramifiedOutside F Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* GS Ω (S : Set (HeightOneSpectrum (𝓞 F))))
  obtain ⟨A, _, eA, he⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.gcRep _ (ZMod (l ^ r)) M rho' hc'
  have hAf : Finite A.V := Finite.of_equiv _ eA.toEquiv
  have hn : ∀ a : A.V, (l ^ r) • a = 0 := by
    intro a
    obtain ⟨m, rfl⟩ := eA.surjective a
    rw [← map_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod (l ^ r)), ZMod.natCast_self, zero_smul, map_zero]
  obtain ⟨e1, -⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.gc1 _ (ZMod (l ^ r)) M rho' A eA he
  obtain ⟨e2, -⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.gc2 _ (ZMod (l ^ r)) M rho' A eA he
  have f1 := GlobalTheory.T.finite_H1_unramified_outside F Ω l r S hS A hAf hn
  have f2 := GlobalTheory.T.finite_H2_unramified_outside F Ω l r S hS A hAf hn
  have t1 := ReciprocityTheory.Neutral.Bridge.equivH1OfIso e rhoS rho' (fun _ _ => rfl)
  have t2 := ReciprocityTheory.Neutral.Bridge.equivH2OfIso e rhoS rho' (fun _ _ => rfl)
  refine ⟨?_, ?_, ?_, fun hl2 n hn3 => ?_⟩
  · exact Finite.of_injective (fun x : H0 rhoS => (x : M)) Subtype.val_injective
  · have : Finite (H1 rho') := Finite.of_equiv _ e1.symm.toEquiv
    exact Finite.of_equiv _ t1.toEquiv.symm
  · have : Finite (H2 rho') := Finite.of_equiv _ e2.symm.toEquiv
    exact Finite.of_equiv _ t2.toEquiv.symm
  · obtain ⟨en⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.gcn _ (ZMod (l ^ r)) M rho' A eA he n
    have := GlobalTheory.T.cohomological_dimension_two_unramified F Ω l r S hS hl2 A hAf hn n hn3
    have : Subsingleton (Hn rho' n) := en.toEquiv.subsingleton
    exact (ReciprocityTheory.Neutral.Bridge.isoHn e rhoS rho' (fun _ _ => rfl) n).toEquiv.subsingleton

end GlobalTheory.CompanionTheory.Hypotheses₂
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.RegularFunctionPolynomialGrowth
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts

open CategoryTheory.Limits ReciprocityTheory.ChartRestriction.G.DVR.FlatBC

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.Gaga

theorem mem_closure_of_isPushout {R A B C : CommRingCat.{0}} {f : R ⟶ A} {g : R ⟶ B} {i : A ⟶ C}
    {j : B ⟶ C} (h : IsPushout f g i j) (c : C) :
    c ∈ AddSubmonoid.closure {x : C | ∃ (a : A) (b : B), x = i a * j b} := by
  letI : Algebra R A := f.hom.toAlgebra
  letI : Algebra R B := g.hom.toAlgebra
  letI : Algebra A C := i.hom.toAlgebra
  letI : Algebra B C := j.hom.toAlgebra
  letI : Algebra R C := (f ≫ i).hom.toAlgebra
  haveI : IsScalarTower R A C := .of_algebraMap_eq fun r => rfl
  haveI : IsScalarTower R B C := .of_algebraMap_eq fun r => congr($(h.w) r)
  haveI : Algebra.IsPushout R B A C := CommRingCat.isPushout_iff_isPushout.mp h.flip
  obtain ⟨t, rfl⟩ := (Algebra.IsPushout.equiv R B A C).surjective c
  induction t with
  | zero => simp
  | tmul b a =>
    rw [Algebra.IsPushout.equiv_tmul]
    exact AddSubmonoid.subset_closure ⟨a, b, mul_comm _ _⟩
  | add x y hx hy =>
    rw [map_add]
    exact add_mem hx hy

theorem appLE_surjective {X Z : Scheme.{0}} (d : X ⟶ Z) [IsClosedImmersion d] {O : Z.Opens}
    (hO : IsAffineOpen O) {D : X.Opens} (hD : D = d ⁻¹ᵁ O) (e : D ≤ d ⁻¹ᵁ O) :
    Function.Surjective (d.appLE O D e) := by
  subst hD
  rw [← Scheme.Hom.app_eq_appLE]
  exact d.app_surjective O hO

theorem mem_closure_inf {S Y : Scheme.{0}} [IsAffine S] (p : Y ⟶ S) [IsSeparated p] {V W : Y.Opens}
    (hV : IsAffineOpen V) (hW : IsAffineOpen W) (g : Γ(Y, V ⊓ W)) :
    g ∈ AddSubmonoid.closure {x : Γ(Y, V ⊓ W) | ∃ (a : Γ(Y, V)) (b : Γ(Y, W)),
      x = resG Y inf_le_left a * resG Y inf_le_right b} := by
  have H := IsPullback.of_hasPullback p p
  obtain ⟨hO, po⟩ := Conormal.isAffineOpen_and_isPushout H (U := ⊤) (T₀ := W) (W := V)
    (isAffineOpen_top _) hW hV le_top le_top
  have d1 : pullback.diagonal p ≫ pullback.fst p p = 𝟙 Y := pullback.diagonal_fst p
  have d2 : pullback.diagonal p ≫ pullback.snd p p = 𝟙 Y := pullback.diagonal_snd p
  have hD : V ⊓ W = pullback.diagonal p ⁻¹ᵁ (pullback.fst p p ⁻¹ᵁ V ⊓ pullback.snd p p ⁻¹ᵁ W) := by
    rw [Scheme.Hom.preimage_inf, ← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, d1, d2]
    simp
  obtain ⟨c, rfl⟩ := appLE_surjective (pullback.diagonal p) hO hD hD.le g
  have hc := mem_closure_of_isPushout po c
  induction hc using AddSubmonoid.closure_induction with
  | zero => simp
  | mem x hx =>
    obtain ⟨a, b, rfl⟩ := hx
    rw [map_mul]
    refine AddSubmonoid.subset_closure ⟨a, b, ?_⟩
    have e₁ := Conormal.appLE_appLE d1 (U := V) (V := pullback.fst p p ⁻¹ᵁ V ⊓ pullback.snd p p ⁻¹ᵁ W)
      (W := V ⊓ W) inf_le_left hD.le (by simpa using inf_le_left) a
    have e₂ := Conormal.appLE_appLE d2 (U := W) (V := pullback.fst p p ⁻¹ᵁ V ⊓ pullback.snd p p ⁻¹ᵁ W)
      (W := V ⊓ W) inf_le_right hD.le (by simpa using inf_le_right) b
    rw [e₁, e₂]
    exact congrArg₂ (· * ·) (Conormal.id_appLE _ a) (Conormal.id_appLE _ b)
  | add x y _ _ hx hy =>
    rw [map_add]
    exact add_mem hx hy

variable {Y : Scheme.{0}} {p : Y ⟶ Sp ℂ}

def GensBdd (V W : Y.Opens) {n : ℕ} (u : Fin n → Γ(Y, V))
    (F : CxPts p (RingHom.id ℂ) → ℂ) : Prop :=
  ∃ (r m : ℕ) (w : Fin r → Γ(Y, W)), ∀ y ∈ ptsIn p (RingHom.id ℂ) (V ⊓ W),
    ‖F y‖ ≤ (∑ k, ‖ev p (RingHom.id ℂ) W (w k) y‖) *
      (1 + ∑ l, ‖ev p (RingHom.id ℂ) V (u l) y‖) ^ m

variable {V W : Y.Opens} {n : ℕ} {u : Fin n → Γ(Y, V)}

theorem GensBdd.add {F G : CxPts p (RingHom.id ℂ) → ℂ} (hF : GensBdd V W u F)
    (hG : GensBdd V W u G) : GensBdd V W u fun y => F y + G y := by
  obtain ⟨r₁, m₁, w₁, h₁⟩ := hF
  obtain ⟨r₂, m₂, w₂, h₂⟩ := hG
  refine ⟨r₁ + r₂, max m₁ m₂, Fin.append w₁ w₂, fun y hy => ?_⟩
  have hB : (1 : ℝ) ≤ 1 + ∑ l, ‖ev p (RingHom.id ℂ) V (u l) y‖ :=
    le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  have s₁ : 0 ≤ ∑ k, ‖ev p (RingHom.id ℂ) W (w₁ k) y‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have s₂ : 0 ≤ ∑ k, ‖ev p (RingHom.id ℂ) W (w₂ k) y‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  calc ‖F y + G y‖ ≤ ‖F y‖ + ‖G y‖ := norm_add_le _ _
    _ ≤ _ := add_le_add (h₁ y hy) (h₂ y hy)
    _ ≤ (∑ k, ‖ev p (RingHom.id ℂ) W (w₁ k) y‖) *
            (1 + ∑ l, ‖ev p (RingHom.id ℂ) V (u l) y‖) ^ max m₁ m₂ +
          (∑ k, ‖ev p (RingHom.id ℂ) W (w₂ k) y‖) *
            (1 + ∑ l, ‖ev p (RingHom.id ℂ) V (u l) y‖) ^ max m₁ m₂ :=
        add_le_add (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hB (le_max_left _ _)) s₁)
          (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hB (le_max_right _ _)) s₂)
    _ = _ := by ring

theorem gensBdd_eval₂ (f : MvPolynomial (Fin n) ℂ) (b : Γ(Y, W)) :
    GensBdd V W u fun y => ev p (RingHom.id ℂ) V (MvPolynomial.eval₂Hom (algX p V) u f) y *
      ev p (RingHom.id ℂ) W b y := by
  induction f using MvPolynomial.induction_on generalizing b with
  | C a =>
    refine ⟨1, 0, fun _ => algX p W a * b, fun y hy => ?_⟩
    have hy' := mem_ptsIn_inf.1 hy
    simp [ev_mul, ev_algX hy'.1, ev_algX hy'.2]
  | add f g hf hg =>
    simpa only [map_add, ev_add, add_mul] using (hf b).add (hg b)
  | mul_X f l hf =>
    obtain ⟨r, m, w, h⟩ := hf b
    refine ⟨r, m + 1, w, fun y hy => ?_⟩
    have hB : ‖ev p (RingHom.id ℂ) V (u l) y‖ ≤ 1 + ∑ l, ‖ev p (RingHom.id ℂ) V (u l) y‖ :=
      (Finset.single_le_sum (f := fun l => ‖ev p (RingHom.id ℂ) V (u l) y‖)
        (fun _ _ => norm_nonneg _) (Finset.mem_univ l)).trans (le_add_of_nonneg_left zero_le_one)
    have s : 0 ≤ (∑ k, ‖ev p (RingHom.id ℂ) W (w k) y‖) *
        (1 + ∑ l, ‖ev p (RingHom.id ℂ) V (u l) y‖) ^ m :=
      (norm_nonneg _).trans (h y hy)
    have e : ev p (RingHom.id ℂ) V (MvPolynomial.eval₂Hom (algX p V) u (f * MvPolynomial.X l)) y *
        ev p (RingHom.id ℂ) W b y =
        (ev p (RingHom.id ℂ) V (MvPolynomial.eval₂Hom (algX p V) u f) y *
          ev p (RingHom.id ℂ) W b y) * ev p (RingHom.id ℂ) V (u l) y := by
      rw [map_mul, MvPolynomial.eval₂Hom_X', ev_mul]
      ring
    beta_reduce
    rw [e, norm_mul, pow_succ, ← mul_assoc]
    exact mul_le_mul (h y hy) hB (norm_nonneg _) s

theorem exists_gens_bound : ∀ (Y : Scheme.{0}) (p : Y ⟶ Sp ℂ), IsSeparated p → LocallyOfFiniteType p → ∀ (V : Y.Opens), IsAffineOpen V → ∃ (n : ℕ) (u : Fin n → Γ(Y, V)), ∀ (W : Y.Opens), IsAffineOpen W → ∀ g : Γ(Y, V ⊓ W), ∃ (r m : ℕ) (w : Fin r → Γ(Y, W)), ∀ y ∈ ptsIn p (RingHom.id ℂ) (V ⊓ W), ‖ev p (RingHom.id ℂ) (V ⊓ W) g y‖ ≤ (∑ k, ‖ev p (RingHom.id ℂ) W (w k) y‖) * (1 + ∑ l, ‖ev p (RingHom.id ℂ) V (u l) y‖) ^ m := by
  intro Y p hs hl V hV
  have hc : (algX p V).FiniteType :=
    (HasRingHomProperty.appLE @LocallyOfFiniteType p inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ _).comp
      (RingHom.FiniteType.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv).2)
  letI : Algebra ℂ Γ(Y, V) := (algX p V).toAlgebra
  haveI : Algebra.FiniteType ℂ Γ(Y, V) := hc
  obtain ⟨n, φ, hφ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1
    (inferInstance : Algebra.FiniteType ℂ Γ(Y, V))
  have hφe (f : MvPolynomial (Fin n) ℂ) :
      φ f = MvPolynomial.eval₂Hom (algX p V) (fun l => φ (MvPolynomial.X l)) f := by
    conv_lhs => rw [MvPolynomial.aeval_unique φ]
    rfl
  refine ⟨n, fun l => φ (MvPolynomial.X l), fun W hW g => ?_⟩
  have key : GensBdd V W (p := p) (fun l => φ (MvPolynomial.X l))
      (ev p (RingHom.id ℂ) (V ⊓ W) g) := by
    induction mem_closure_inf p hV hW g using AddSubmonoid.closure_induction with
    | zero =>
      refine ⟨0, 0, Fin.elim0, fun y hy => ?_⟩
      simp [ev_eq hy]
    | mem x hx =>
      obtain ⟨a, b, rfl⟩ := hx
      obtain ⟨f, rfl⟩ := hφ a
      obtain ⟨r, m, w, h⟩ := gensBdd_eval₂ (V := V) (W := W) (p := p)
        (u := fun l => φ (MvPolynomial.X l)) f b
      refine ⟨r, m, w, fun y hy => ?_⟩
      have hy' := mem_ptsIn_inf.1 hy
      rw [ev_mul, ev_res _ hy, ev_res _ hy, hφe]
      exact h y hy
    | add x y _ _ hx hy =>
      have e : ev p (RingHom.id ℂ) (V ⊓ W) (x + y) =
          fun z => ev p (RingHom.id ℂ) (V ⊓ W) x z + ev p (RingHom.id ℂ) (V ⊓ W) y z :=
        funext fun z => ev_add x y z
      rw [e]
      exact hx.add hy
  exact key

end GlobalTheory.CompanionTheory.Gaga
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.SmoothSchemeDecomposeRelativeDimension
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts

namespace GlobalTheory.CompanionTheory.Gaga

theorem dim_eq_of_mem_inf {X Y : Scheme.{0}} (f : X ⟶ Y) {U V : X.Opens} {n m : ℕ}
    (hU : SmoothOfRelativeDimension n (U.ι ≫ f)) (hV : SmoothOfRelativeDimension m (V.ι ≫ f))
    {x : X} (hxU : x ∈ U) (hxV : x ∈ V) : n = m := by
  have e₁ : SmoothOfRelativeDimension (0 + n) ((U ⊓ V).ι ≫ f) := by
    rw [← Scheme.homOfLE_ι _ (inf_le_left : U ⊓ V ≤ U), Category.assoc]; infer_instance
  have e₂ : SmoothOfRelativeDimension (0 + m) ((U ⊓ V).ι ≫ f) := by
    rw [← Scheme.homOfLE_ι _ (inf_le_right : U ⊓ V ≤ V), Category.assoc]; infer_instance
  simpa using ReciprocityTheory.ChartRestriction.G.H1.dim_unique _ e₁ e₂ ⟨x, hxU, hxV⟩

theorem smoothOfRelativeDimension_iSup {X Y : Scheme.{0}} (f : X ⟶ Y) (D : ℕ) {ι : Type*}
    (U : ι → X.Opens) (hU : ∀ i, SmoothOfRelativeDimension D ((U i).ι ≫ f)) :
    SmoothOfRelativeDimension D ((⨆ i, U i).ι ≫ f) := by
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{0} D) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension.{0} D)
    (fun i => (⨆ i, U i).ι ⁻¹ᵁ U i) ?_ fun i => ?_
  · refine top_le_iff.1 fun x _ => ?_
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 x.2
    exact Opens.mem_iSup.2 ⟨i, hi⟩
  · let j := ((⨆ i, U i).ι ⁻¹ᵁ U i).ι ≫ (⨆ i, U i).ι
    have hr : Set.range j ⊆ Set.range (U i).ι := by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact y.2
    let k := IsOpenImmersion.lift (U i).ι j hr
    have hk : k ≫ (U i).ι = j := IsOpenImmersion.lift_fac _ _ _
    have : IsOpenImmersion (k ≫ (U i).ι) := by rw [hk]; infer_instance
    have : IsOpenImmersion k := IsOpenImmersion.of_comp k (U i).ι
    have e : ((⨆ i, U i).ι ⁻¹ᵁ U i).ι ≫ (⨆ i, U i).ι ≫ f = k ≫ (U i).ι ≫ f := by
      rw [← Category.assoc, ← Category.assoc, hk]
    rw [e]
    exact IsZariskiLocalAtSource.comp (P := @SmoothOfRelativeDimension.{0} D) (hU i) k

theorem exists_clopen_smoothOfRelativeDimension :
    ∀ (X : Scheme.{0}) (s : X ⟶ Sp ℂ), Smooth s → ∃ W : ℕ → X.Opens, (∀ D, IsClosed (W D : Set X)) ∧ (∀ D, SmoothOfRelativeDimension D ((W D).ι ≫ s)) ∧ (⨆ D, W D) = ⊤ ∧ Pairwise fun D D' => W D ⊓ W D' = ⊥ := by
  intro X s hs
  let W : ℕ → X.Opens := fun D => ⨆ U : {U : X.Opens // SmoothOfRelativeDimension D (U.ι ≫ s)}, U.1
  have hsm : ∀ D, SmoothOfRelativeDimension D ((W D).ι ≫ s) := fun D =>
    smoothOfRelativeDimension_iSup s D _ fun U => U.2
  have hcov : (⨆ D, W D) = ⊤ := by
    refine top_le_iff.1 fun x _ => ?_
    obtain ⟨n, U, hx, hU⟩ := ReciprocityTheory.ChartRestriction.G.H1.exists_dim s x
    exact Opens.mem_iSup.2 ⟨n, Opens.mem_iSup.2 ⟨⟨U, hU⟩, hx⟩⟩
  have hdis : Pairwise fun D D' => W D ⊓ W D' = ⊥ := by
    intro D D' hne
    refine le_bot_iff.1 fun x hx => ?_
    obtain ⟨U, hU⟩ := Opens.mem_iSup.1 hx.1
    obtain ⟨V, hV⟩ := Opens.mem_iSup.1 hx.2
    exact (hne (dim_eq_of_mem_inf s U.2 V.2 hU hV)).elim
  refine ⟨W, fun D => ?_, hsm, hcov, hdis⟩
  have hc : (W D : Set X)ᶜ = ((⨆ D' : {D' // D' ≠ D}, W D'.1 : X.Opens) : Set X) := by
    ext x
    constructor
    · intro hx
      have hx' : x ∈ (⨆ D, W D) := hcov ▸ trivial
      obtain ⟨D', hD'⟩ := Opens.mem_iSup.1 hx'
      refine Opens.mem_iSup.2 ⟨⟨D', fun e => hx (e ▸ hD')⟩, hD'⟩
    · intro hx hxD
      obtain ⟨D', hD'⟩ := Opens.mem_iSup.1 hx
      have := hdis D'.2
      have hm : x ∈ W D'.1 ⊓ W D := ⟨hD', hxD⟩
      rw [this] at hm
      exact hm
  rw [← isOpen_compl_iff, hc]
  exact Opens.isOpen _

end GlobalTheory.CompanionTheory.Gaga
end

