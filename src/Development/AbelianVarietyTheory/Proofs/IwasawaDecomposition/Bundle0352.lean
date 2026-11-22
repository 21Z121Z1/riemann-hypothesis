import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitsLiftSpec
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.LocalToGlobal.NumberFieldFamilies.HeckeStd0Of
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0340
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0259
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0011
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0303
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0339
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0313
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0337
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0019
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideMultiplicityFamily
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0046

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalLocalisationSpaceAll
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

namespace GlobalTheory.FinDimVProof

theorem finDimV_all : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (B : LocBase0 H what₂), FinDimV B := by
  intro R H what₂ B j w
  classical
  have hfin : (Formalism.L2.Fam.NPC.LatticeFinitenessFree.latJ (what₂ := what₂) j w).Finite :=
    Set.Finite.subset ((what₂.MtLat (what₂.muTw w) j).gen.finite_toSet.preimage
      ((Formalism.L2.Fam.NPC.LatticeFinitenessFree.jMt_injective (what₂.muTw w) j).injOn)) fun x hx => hx
  have hs := Formalism.L2.Fam.NPC.LatticeFinitenessFree.span_iV (B := B) j w
  exact Module.finite_def.2 ⟨(hfin.image (B.iV j w)).toFinset, by simpa using hs⟩

end GlobalTheory.FinDimVProof
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteInertHeckeSupportCosets
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial Formalism.UG GlobalTheory.SatInd

namespace GlobalTheory.SatInd.CosetFin

theorem finite_cosets {G H : Type} [Group G] [Group H] (φ : G →* H) (H' : Subgroup H) (K : Subgroup H')
    (U : Subgroup G) (p : G → Prop) (F : Set (H' ⧸ K)) (hF : F.Finite)
    (hp : ∀ x, p x → ∃ hx : φ x ∈ H', ((⟨φ x, hx⟩ : H') : H' ⧸ K) ∈ F)
    (hU : ∀ x y, p x → p y → ∀ hz : φ (x⁻¹ * y) ∈ H', (⟨φ (x⁻¹ * y), hz⟩ : H') ∈ K → x⁻¹ * y ∈ U) :
    Set.Finite {c : G ⧸ U | ∃ x : G, (x : G ⧸ U) = c ∧ p x} := by
  have hsub : {c : G ⧸ U | ∃ x : G, (x : G ⧸ U) = c ∧ p x} ⊆
      ⋃ d ∈ F, {c : G ⧸ U | ∃ x : G, (x : G ⧸ U) = c ∧ p x ∧
        ∃ hx : φ x ∈ H', ((⟨φ x, hx⟩ : H') : H' ⧸ K) = d} := by
    rintro c ⟨x, hc, hx⟩
    obtain ⟨h1, h2⟩ := hp x hx
    exact Set.mem_biUnion h2 ⟨x, hc, hx, h1, rfl⟩
  refine (hF.biUnion fun d _ => Set.Subsingleton.finite ?_).subset hsub
  rintro c ⟨x, rfl, hx, hx1, hx2⟩ c' ⟨y, rfl, hy, hy1, hy2⟩
  have hk := QuotientGroup.eq.1 (hx2.trans hy2.symm)
  have hz : φ (x⁻¹ * y) ∈ H' := by
    rw [map_mul, map_inv]; exact H'.mul_mem (H'.inv_mem hx1) hy1
  refine QuotientGroup.eq.2 (hU x y hx hy hz ?_)
  convert hk using 1
  apply Subtype.ext
  simp

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem trivOutside_mul {T : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))} {x y : GA L n}
    (hx : TrivOutside T x) (hy : TrivOutside T y) : TrivOutside T (x * y) := by
  intro w hw
  have : ((x * y).1 : Matrix (Fin n) (Fin n) (AL L)) =
      (x.1 : Matrix (Fin n) (Fin n) (AL L)) * (y.1 : Matrix (Fin n) (Fin n) (AL L)) := rfl
  rw [this, Matrix.map_mul, hx w hw, hy w hw, mul_one]

theorem trivOutside_inv {T : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))} {x : GA L n}
    (hx : TrivOutside T x) : TrivOutside T x⁻¹ := by
  intro w hw
  have h1 : (((x⁻¹ : GA L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
      (x.1 : Matrix (Fin n) (Fin n) (AL L)) = 1 := by
    rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]
    rfl
  have h2 := congrArg (fun M => M.map (compAt L w)) h1
  simp only [Matrix.map_mul, hx w hw, mul_one] at h2
  rw [h2, Matrix.map_one _ (map_zero _) (map_one _)]

variable {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} {w : HeightOneSpectrum (𝓞 L)}

def locHom (D : InertDatum L n v w) : GAf L n →* GL (Fin n) (w.adicCompletion L) :=
  MonoidHom.mk' D.loc fun x y => by
    simp only [InertDatum.loc, Subgroup.coe_mul, map_mul, mul_assoc, mul_inv_cancel_left]

theorem entries_int {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] {σ : K →+* K}
    {g : GU σ n} (hg : g ∈ KU σ n) (i j : Fin n) :
    ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j ∈ intL K := by
  obtain ⟨-, k, hk⟩ := hg
  have hk' : bc (n := Fin n) (intL K).subtype k = (g : GL (Fin n) K) := hk
  rw [← hk']
  exact ((k : Matrix (Fin n) (Fin n) (intL K)) i j).2

theorem finite_inert_support : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w), (∀ s : GU Dv.σw n, Set.Finite {c : GU Dv.σw n ⧸ KU Dv.σw n | ∃ a ∈ KU Dv.σw n, ((a * s : GU Dv.σw n) : GU Dv.σw n ⧸ KU Dv.σw n) = c}) → (∀ z : GAf L n, TrivOutside {v} z → (∀ i j, ((Dv.loc z : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) i j ∈ intL (w.adicCompletion L)) → z ∈ Umax L n) → ∀ (U : Subgroup (GAf L n)), (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) → ∀ h ∈ Hecke ℂ (KU Dv.σw n), Set.Finite {c : GAf L n ⧸ U | ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x ∧ Dv.hval h (Dv.loc x) ≠ 0} := by
  intro L _ _ _ n v w Dv hfin hint U hU h hh
  obtain ⟨-, S, hS⟩ := hh
  refine finite_cosets (locHom Dv) (GU Dv.σw n) (KU Dv.σw n) U
    (fun x => TrivOutside {v} x ∧ Dv.hval h (Dv.loc x) ≠ 0) _
    (S.finite_toSet.biUnion fun s _ => hfin s) ?_ ?_
  · rintro x ⟨-, hx⟩
    have hm : Dv.loc x ∈ GU Dv.σw n := by
      by_contra hm
      exact hx (dif_neg hm)
    have hne : h ⟨Dv.loc x, hm⟩ ≠ 0 := by
      intro h0
      exact hx ((dif_pos hm).trans h0)
    obtain ⟨s, hs, a, b, e⟩ := hS _ hne
    refine ⟨hm, Set.mem_biUnion hs ⟨a, a.2, ?_⟩⟩
    have e' : (⟨locHom Dv x, hm⟩ : GU Dv.σw n) = (a : GU Dv.σw n) * s * b := e
    rw [e']
    exact (QuotientGroup.mk_mul_of_mem _ b.2).symm
  · rintro x y ⟨hx, -⟩ ⟨hy, -⟩ hz hk
    have ht : TrivOutside {v} (x⁻¹ * y) := trivOutside_mul (trivOutside_inv hx) hy
    exact (hU _ ht).2 (hint _ ht fun i j => entries_int hk i j)

end GlobalTheory.SatInd.CosetFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankJointEigenspaceCoefficientFieldComplexStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_jointEigenspace_coefficientField_complex : ∀ (D : D7) (M : MtFam D) (B : NLocBase D M) (j : ℕ) (w : D.what₂.places.Pl) (μ : D.what₂.Tup) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m), μ = D.what₂.muTw w → ∀ (φ : FractionRing (B.Oc j w) →+* ℂ), (∀ x, φ (B.ec j w x) = D.what₂.embLL x) → ∀ (κ : PlE D.host → ℕ → FractionRing (B.Oc j w)) (E : Submodule ℂ (D.what₂.Mt μ j)), (∀ v k, GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k → ∃ (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), IsConjPl D.host v s.w ∧ IsUnif D.host.E s.v ϖ) → (∀ v k (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k → IsConjPl D.host v s.w → IsUnif D.host.E s.v ϖ → ∀ (c : ℂ) (f f' : GAf D.host.E D.R.nV → (M μ j h1 h2).wt.W), NG.tN (M μ j h1 h2).J s ϖ k (c • f + f') = c • NG.tN (M μ j h1 h2).J s ϖ k f + NG.tN (M μ j h1 h2).J s ϖ k f') → (∀ y, y ∈ E ↔ ∀ v k (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k → IsConjPl D.host v s.w → IsUnif D.host.E s.v ϖ → NG.tN (M μ j h1 h2).J s ϖ k ((M μ j h1 h2).real y) = φ (κ v k) • (M μ j h1 h2).real y) → Module.finrank (FractionRing (B.Oc j w)) ↥(⨅ (v : PlE D.host) (k : ℕ) (_ : GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k), Module.End.eigenspace (B.hK j w v k) (κ v k)) = Module.finrank ℂ E := by
  first | exact @GlobalTheory.PtLocalEig.eig_dim | exact GlobalTheory.PtLocalEig.eig_dim | (intros; apply GlobalTheory.PtLocalEig.eig_dim <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FullFlagBundleFunctionFieldMapDominatesLocalRing
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical

namespace GlobalTheory.FlagBundle.Dom

theorem mem_O_of_forall_dvr {F : Type} [Field F] (Y : Var F) (y : (ratOf Y).Z) (x : Y.Fn)
    (hx : ∀ V : ValuationSubring Y.Fn, IsDiscreteValuationRing V →
      LocalSubring.range (algebraMap ((ratOf Y).O y) Y.Fn) ≤ V.toLocalSubring → x ∈ V) :
    x ∈ (ratOf Y).O y := by
  haveI := (ratOf Y).lft
  haveI : IsLocallyNoetherian (ratOf Y).Z := LocallyOfFiniteType.isLocallyNoetherian (ratOf Y).s
  haveI : IsNoetherianRing ((ratOf Y).O y) :=
    isNoetherianRing_of_ringEquiv _ ((ratOf Y).stalkEquiv y)
  haveI : Algebra.EssFiniteType ((ratOf Y).O y) Y.Fn :=
    Algebra.EssFiniteType.of_isLocalization Y.Fn (nonZeroDivisors ((ratOf Y).O y))
  have hN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (ratOf Y).Z := fun z =>
    ⟨(Y.isNormalScheme).isDomain_stalk z, (Y.isNormalScheme).isIntegrallyClosed_stalk z⟩
  haveI := RatModel.isIntegrallyClosed_O hN y
  by_contra hn
  have hi : ¬ IsIntegral ((ratOf Y).O y) x := fun h => by
    obtain ⟨a, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
    exact hn a.2
  obtain ⟨V, h1, h2, h3⟩ := GlobalTheory.exists_discreteValuationSubring_dominating_notMem hi
  exact h3 (hx V h1 h2)

end GlobalTheory.FlagBundle.Dom

namespace GlobalTheory.FlagBundle.Dom

theorem exists_pt_of_le {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (z : M.Z)
    (V : ValuationSubring Ω) (hV : LocalSubring.range (algebraMap (M.O z) Ω) ≤ V.toLocalSubring) :
    ∃ v : Sp V ⟶ M.Z, v (IsLocalRing.closedPoint V) = z ∧ spMap (algebraMap V Ω) ≫ v = M.pt ∧
      ∃ σ : IsLocalRing.ResidueField (M.Z.presheaf.stalk z) →+* IsLocalRing.ResidueField V,
        spMap (IsLocalRing.residue V) ≫ v = spMap σ ≫ spMap (IsLocalRing.residue _) ≫ M.Z.fromSpecStalk z := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.localSubring_range_le_valuationSubring_iff _ V).1 hV
  let ι : M.O z →+* V := (algebraMap (M.O z) Ω).codRestrict V h1
  haveI hι : IsLocalHom ι := ⟨fun r hr => by
    by_contra hn
    obtain ⟨_, hm⟩ := (ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal).1 (h2 r hn)
    exact hm hr⟩
  let g : M.Z.presheaf.stalk z →+* V := ι.comp (M.stalkEquiv z).toRingHom
  haveI : IsLocalHom g := ⟨fun a ha =>
    (isUnit_map_iff (M.stalkEquiv z) a).1 (IsLocalHom.map_nonunit (f := ι) _ ha)⟩
  refine ⟨spMap g ≫ M.Z.fromSpecStalk z, ?_, ?_, IsLocalRing.ResidueField.map g, ?_⟩
  · show M.Z.fromSpecStalk z (spMap g (IsLocalRing.closedPoint V)) = z
    rw [show spMap g (IsLocalRing.closedPoint V) = IsLocalRing.closedPoint _ from IsLocalRing.comap_closedPoint g]
    exact Scheme.fromSpecStalk_closedPoint
  · have e : (algebraMap V Ω).comp g = M.stalkHom z := rfl
    have e2 : spMap (M.stalkHom z) = spMap (Scheme.stalkClosedPointTo (R := .of Ω) M.pt).hom ≫
        Spec.map (M.Z.presheaf.stalkSpecializes (M.pt_specializes (IsLocalRing.closedPoint Ω) z)) := by
      rw [RatModel.stalkHom]
      show Spec.map _ = _
      rw [CommRingCat.ofHom_hom, Spec.map_comp]
      rfl
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, e]
    change spMap (M.stalkHom z) ≫ _ = _
    rw [e2, Category.assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    exact spMap_stalkClosedPointTo M.pt
  · rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp, IsLocalRing.ResidueField.map_comp_residue]

end GlobalTheory.FlagBundle.Dom

namespace GlobalTheory.FlagBundle.Dom

variable {F : Type} [Field F] {ι : Type} {m : ι → ℕ} {X Y₁ Y₂ : Var F} {Eb : Fr (ratOf X) m 0}
  {S₁ : Fr (ratOf Y₁) m m} {φ₁ : X.Fn →ₐ[F] Y₁.Fn} {S₂ : Fr (ratOf Y₂) m m} {φ₂ : X.Fn →ₐ[F] Y₂.Fn}

theorem coBear_swap {K : Type} [Field K] {x x' : Sp K ⟶ X.X} {p₁ p₁' : Sp K ⟶ Y₁.X}
    {p₂ p₂' : Sp K ⟶ Y₂.X} (hx : x = x') (hp₁ : p₁ = p₁') (hp₂ : p₂ = p₂')
    (h : CoBear Eb S₁ φ₁ S₂ φ₂ x p₁ p₂) : CoBear Eb S₂ φ₂ S₁ φ₁ x' p₂' p₁' := by
  subst hx hp₁ hp₂
  obtain ⟨A, hA, g, hg, b₁, b₂⟩ := h
  exact ⟨A, hA, g, hg, b₂, b₁⟩

end GlobalTheory.FlagBundle.Dom

namespace GlobalTheory.FlagBundle

open GlobalTheory.FlagBundle.Dom in

theorem dominates_O (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y₁ Y₂ : Var F)
    (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn) (f₁ : Y₁.X ⟶ X.X)
    (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) (f₂ : Y₂.X ⟶ X.X) (h₁ : Reps Eb S₁ φ₁ f₁)
    (h₂ : Reps Eb S₂ φ₂ f₂) (ψ : Y₂.Fn →ₐ[F] Y₁.Fn) (hψ : ψ.comp φ₂ = φ₁)
    (hg : CoBear Eb S₁ φ₁ S₂ φ₂ ((ratOf Y₁).pt ≫ f₁) (ratOf Y₁).pt (spMap ψ.toRingHom ≫ (ratOf Y₂).pt))
    (y : Y₁.X) : ∃ y' : Y₂.X, ∀ a ∈ (ratOf Y₂).O y', ψ a ∈ (ratOf Y₁).O y := by
  let κ := IsLocalRing.ResidueField (Y₁.X.presheaf.stalk y)
  let py : Sp κ ⟶ Y₁.X := spMap (IsLocalRing.residue _) ≫ Y₁.X.fromSpecStalk y
  obtain ⟨A, hA, h, hh, hb⟩ := GlobalTheory.T.exists_pointCarriesFrameFlags_own_frame F ι m X Y₁ Eb S₁ φ₁ f₁ h₁ κ py
  obtain ⟨s, ⟨hs, hsb⟩, -⟩ := h₂.2.2 κ (py ≫ f₁) A hA h hh
  refine ⟨s (IsLocalRing.closedPoint κ), fun a ha => ?_⟩
  refine mem_O_of_forall_dvr Y₁ y (ψ a) fun V _ hV => ?_
  obtain ⟨v, -, hv1, σ, hv2⟩ := exists_pt_of_le (ratOf Y₁) y V hV
  haveI : IsProper (f₂ ≫ X.str) := by
    rw [show f₂ ≫ X.str = Y₂.str from h₂.1.inducedModelMorphism_comp_structureMap]
    infer_instance
  haveI : IsProper f₂ := IsProper.of_comp f₂ X.str
  have hψ' : spMap ψ.toRingHom ≫ spMap φ₂.toRingHom = spMap φ₁.toRingHom := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← hψ]
    rfl
  have hq : (spMap ψ.toRingHom ≫ (ratOf Y₂).pt) ≫ f₂ = spMap (algebraMap V Y₁.Fn) ≫ (v ≫ f₁) := by
    have e1 : (ratOf Y₂).pt ≫ f₂ = spMap φ₂.toRingHom ≫ (ratOf X).pt := h₂.1
    have e2 : (ratOf Y₁).pt ≫ f₁ = spMap φ₁.toRingHom ≫ (ratOf X).pt := h₁.1
    erw [Category.assoc, e1, ← Category.assoc, hψ', ← e2, ← Category.assoc, hv1]
  obtain ⟨ℓ, ⟨hℓ1, hℓ2⟩, -⟩ :=
    GlobalTheory.ModelPoints.existsUnique_extension f₂ (spMap ψ.toRingHom ≫ (ratOf Y₂).pt) (v ≫ f₁) hq
  have hinc := GlobalTheory.T.fullFlag_common_closedPoint_of_generic F ι m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ h₁ h₂ V Y₁.Fn v ℓ hℓ1.symm
    (by erw [hℓ2, ← Category.assoc, hv1]; exact hg)
  have hbc := GlobalTheory.T.pointsCarryCommonFlag_spectrumMap_field_ext F ι m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ h₁ h₂ κ (IsLocalRing.ResidueField V) σ
    (py ≫ f₁) py s ⟨A, hA, h, hh, hb, hsb⟩
  have hpv : spMap (IsLocalRing.residue V) ≫ v = spMap σ ≫ py := hv2
  have E1 : (spMap (IsLocalRing.residue V) ≫ ℓ) ≫ f₂ = (spMap σ ≫ py) ≫ f₁ :=
    (Category.assoc _ _ _).trans ((congrArg (spMap (IsLocalRing.residue V) ≫ ·) hℓ1).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ f₁) hpv)))
  have E2 : (spMap σ ≫ s) ≫ f₂ = (spMap σ ≫ py) ≫ f₁ :=
    (Category.assoc _ _ _).trans ((congrArg (spMap σ ≫ ·) hs).trans (Category.assoc _ _ _).symm)
  have E3 : spMap (IsLocalRing.residue V) ≫ v ≫ f₁ = (spMap (IsLocalRing.residue V) ≫ ℓ) ≫ f₂ :=
    (congrArg (spMap (IsLocalRing.residue V) ≫ ·) hℓ1.symm).trans (Category.assoc _ _ _).symm
  have E4 : spMap σ ≫ py ≫ f₁ = (spMap σ ≫ s) ≫ f₂ :=
    (congrArg (spMap σ ≫ ·) hs.symm).trans (Category.assoc _ _ _).symm
  have e : spMap (IsLocalRing.residue V) ≫ ℓ = spMap σ ≫ s :=
    GlobalTheory.T.eq_of_bear_common_fullFlag F ι m X Y₂ Y₁ Eb S₂ φ₂ f₂ S₁ φ₁ f₁ h₂ h₁ _ (spMap (IsLocalRing.residue V) ≫ ℓ)
      (spMap σ ≫ s) (spMap σ ≫ py) E1 E2 (coBear_swap E3 hpv rfl hinc) (coBear_swap E4 rfl rfl hbc)
  have hℓc : ℓ (IsLocalRing.closedPoint V) = s (IsLocalRing.closedPoint κ) := by
    have h3 : ℓ (spMap (IsLocalRing.residue V) (IsLocalRing.closedPoint (IsLocalRing.ResidueField V))) =
        s (spMap σ (IsLocalRing.closedPoint (IsLocalRing.ResidueField V))) :=
      congrArg (fun t : Sp (IsLocalRing.ResidueField V) ⟶ Y₂.X =>
        t (IsLocalRing.closedPoint (IsLocalRing.ResidueField V))) e
    have h4 : spMap (IsLocalRing.residue V) (IsLocalRing.closedPoint (IsLocalRing.ResidueField V)) =
        IsLocalRing.closedPoint V := IsLocalRing.comap_closedPoint (IsLocalRing.residue V)
    have h5 : spMap σ (IsLocalRing.closedPoint (IsLocalRing.ResidueField V)) = IsLocalRing.closedPoint κ :=
      Subsingleton.elim (α := PrimeSpectrum κ) _ _
    rw [h4, h5] at h3
    exact h3
  have hsp : ℓ (IsLocalRing.closedPoint V) ⤳ s (IsLocalRing.closedPoint κ) := hℓc ▸ specializes_rfl
  have k1 := RatModel.val_spMap_comp (M := ratOf Y₂) (algebraMap V Y₁.Fn) ℓ hsp ⟨a, ha⟩
  have k2 := RatModel.val_spMap_comp (M := ratOf Y₂) ψ.toRingHom (ratOf Y₂).pt
    ((ratOf Y₂).pt_specializes (IsLocalRing.closedPoint _) _) ⟨a, ha⟩
  have k4 := (RatModel.valLoc_eq_val (M := ratOf Y₂) (ratOf Y₂).pt
    ((ratOf Y₂).pt_specializes (IsLocalRing.closedPoint _) (s (IsLocalRing.closedPoint κ))) ⟨a, ha⟩).trans
    (RatModel.val_pt (M := ratOf Y₂) a)
  have k3 : ψ a = algebraMap V Y₁.Fn (RatModel.valLoc ℓ _ hsp ⟨a, ha⟩) := by
    calc ψ a = ψ.toRingHom (RatModel.valLoc (ratOf Y₂).pt _
          ((ratOf Y₂).pt_specializes (IsLocalRing.closedPoint _) (s (IsLocalRing.closedPoint κ))) ⟨a, ha⟩) :=
          (congrArg ψ.toRingHom k4).symm
      _ = (ratOf Y₂).val (spMap ψ.toRingHom ≫ (ratOf Y₂).pt) a := k2.symm
      _ = (ratOf Y₂).val (spMap (algebraMap V Y₁.Fn) ≫ ℓ) a :=
          congrArg (fun t : Sp Y₁.Fn ⟶ Y₂.X => (ratOf Y₂).val t a) hℓ2.symm
      _ = _ := k1
  rw [k3]
  exact (RatModel.valLoc ℓ _ hsp ⟨a, ha⟩).2

end GlobalTheory.FlagBundle
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FullFlagBundleMorphismBearsFlagsOfGeneric
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical

namespace GlobalTheory.FlagBundle

theorem coBear_comp_of_isHom : ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y₁ Y₂ : Var F) (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn) (f₁ : Y₁.X ⟶ X.X) (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) (f₂ : Y₂.X ⟶ X.X), Reps Eb S₁ φ₁ f₁ → Reps Eb S₂ φ₂ f₂ → ∀ ψ : Y₂.Fn →ₐ[F] Y₁.Fn, ψ.comp φ₂ = φ₁ → CoBear Eb S₁ φ₁ S₂ φ₂ ((ratOf Y₁).pt ≫ f₁) (ratOf Y₁).pt (spMap ψ.toRingHom ≫ (ratOf Y₂).pt) → ∀ g : Y₁.X ⟶ Y₂.X, (ratOf Y₂).IsHom (ratOf Y₁) ψ g → ∀ (K : Type) [Field K] (p : Sp K ⟶ Y₁.X), CoBear Eb S₁ φ₁ S₂ φ₂ (p ≫ f₁) p (p ≫ g) := by
  intro F _ ι _ m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ h₁ h₂ ψ hψ hgen g hg K _ p
  have hgf : g ≫ f₂ = f₁ := by
    have := h₂.1.comp hg
    rw [hψ] at this
    exact this.unique h₁.1

  let y : Y₁.X := p (IsLocalRing.closedPoint K)
  let R := Y₁.X.presheaf.stalk y
  let v₁ : Sp R ⟶ Y₁.X := Y₁.X.fromSpecStalk y
  have hpt : spMap (algebraMap R Y₁.Fn) ≫ v₁ = (ratOf Y₁).pt :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes y)
  have hinc := GlobalTheory.T.fullFlag_common_closedPoint_of_generic F ι m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ h₁ h₂ R Y₁.Fn v₁ (v₁ ≫ g)
    (by rw [Category.assoc, hgf]) (by
      have e1 : spMap (algebraMap R Y₁.Fn) ≫ v₁ ≫ f₁ = (ratOf Y₁).pt ≫ f₁ := by
        rw [← Category.assoc]; exact congrArg (· ≫ f₁) hpt
      have e2 : spMap (algebraMap R Y₁.Fn) ≫ v₁ ≫ g = spMap ψ.toRingHom ≫ (ratOf Y₂).pt := by
        rw [← Category.assoc, hpt]; exact hg
      rw [e1, hpt, e2]; exact hgen)

  let c := Scheme.stalkClosedPointTo (R := .of K) p
  let σ : IsLocalRing.ResidueField R →+* K := IsLocalRing.ResidueField.lift c.hom
  have hσ : σ.comp (IsLocalRing.residue R) = c.hom := IsLocalRing.ResidueField.lift_comp_residue c.hom
  have hp : spMap σ ≫ spMap (IsLocalRing.residue R) ≫ v₁ = p := by
    rw [← Category.assoc, ← spMap_comp, hσ]
    exact spMap_stalkClosedPointTo p
  have hbc := GlobalTheory.T.pointsCarryCommonFlag_spectrumMap_field_ext F ι m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ h₁ h₂ (IsLocalRing.ResidueField R) K σ _ _ _ hinc
  rw [← hp]
  simpa only [Category.assoc] using hbc

end GlobalTheory.FlagBundle
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FullFlagBundleMorphismBijectiveFieldPoints
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical

namespace GlobalTheory.FlagBundle

theorem CoBear₂ : ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y₁ Y₂ : Var F) (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn) (f₁ : Y₁.X ⟶ X.X) (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) (f₂ : Y₂.X ⟶ X.X), Reps Eb S₁ φ₁ f₁ → Reps Eb S₂ φ₂ f₂ → ∀ g : Y₁.X ⟶ Y₂.X, g ≫ f₂ = f₁ → (∀ (K : Type) [Field K] (p : Sp K ⟶ Y₁.X), CoBear Eb S₁ φ₁ S₂ φ₂ (p ≫ f₁) p (p ≫ g)) → ∀ (K : Type) [Field K], Function.Bijective (fun p : Sp K ⟶ Y₁.X => p ≫ g) := by
  intro F _ ι _ m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ hR₁ hR₂ g hg hco K _
  have hcomp : ∀ p : Sp K ⟶ Y₁.X, p ≫ f₁ = (p ≫ g) ≫ f₂ := by
    intro p; rw [Category.assoc, hg]
  constructor
  · intro p p' hpp'
    simp only at hpp'
    have h1 := hco K p
    have h2 := hco K p'
    rw [← hpp'] at h2
    exact GlobalTheory.T.eq_of_bear_common_fullFlag F ι m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ hR₁ hR₂ K p p' (p ≫ g) (hcomp p)
      (by rw [hcomp p', hpp']) h1 h2
  · intro w
    obtain ⟨A, hA, h, hh, hw⟩ := GlobalTheory.T.exists_pointCarriesFrameFlags_own_frame F ι m X Y₂ Eb S₂ φ₂ f₂ hR₂ K w
    obtain ⟨p, ⟨hpx, hpA⟩, -⟩ := hR₁.2.2 K (w ≫ f₂) A hA h hh
    obtain ⟨B, hB, h', -, hpB, hqB⟩ := hco K p
    have hA' : A ∈ Eb.S ((p ≫ f₁) (IsLocalRing.closedPoint K)) := by rw [hpx]; exact hA
    have hqA : Bears S₂ φ₂ A h (p ≫ g) :=
      GlobalTheory.T.pointCarriesFrameFlags_transfer_between_flag_bundles F ι m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ hR₁ hR₂ K p (p ≫ g) (hcomp p) A hA' B hB h h'
        hpA hpB hqB
    obtain ⟨q, -, hq⟩ := hR₂.2.2 K (w ≫ f₂) A hA h hh
    refine ⟨p, ?_⟩
    simp only
    rw [hq (p ≫ g) ⟨by rw [← hcomp p, hpx], hqA⟩, hq w ⟨rfl, hw⟩]

end GlobalTheory.FlagBundle
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FullFlagBundlePointAtGenericLiftImage
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical

set_option autoImplicit false

namespace GlobalTheory.FlagBundle

theorem exists_spMap_fromSpecResidueField {Z : Scheme.{0}} (y : Z) {K : Type} [Field K] (p : Sp K ⟶ Z)
    (hp : p (IsLocalRing.closedPoint K) = y) :
    ∃ σ : Z.residueField y →+* K, spMap σ ≫ Z.fromSpecResidueField y = p := by
  subst hp
  exact ⟨(Z.descResidueField (Scheme.stalkClosedPointTo p)).hom,
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K Z p⟩

theorem coBear_swap {F : Type} [Field F] {ι : Type} {m : ι → ℕ} {X Y₁ Y₂ : Var F} {Eb : Fr (ratOf X) m 0}
    {S₁ : Fr (ratOf Y₁) m m} {φ₁ : X.Fn →ₐ[F] Y₁.Fn} {S₂ : Fr (ratOf Y₂) m m} {φ₂ : X.Fn →ₐ[F] Y₂.Fn}
    {K : Type} [Field K] {x x' : Sp K ⟶ X.X} {p₁ : Sp K ⟶ Y₁.X} {p₂ : Sp K ⟶ Y₂.X}
    (h : CoBear Eb S₁ φ₁ S₂ φ₂ x p₁ p₂) (hx : x = x') : CoBear Eb S₂ φ₂ S₁ φ₁ x' p₂ p₁ := by
  subst hx
  obtain ⟨A, hA, g, hg, h₁, h₂⟩ := h
  exact ⟨A, hA, g, hg, h₂, h₁⟩

end GlobalTheory.FlagBundle

theorem GlobalTheory.FlagBundle.conclusion : ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y₁ Y₂ : Var F) (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn) (f₁ : Y₁.X ⟶ X.X) (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) (f₂ : Y₂.X ⟶ X.X), Reps Eb S₁ φ₁ f₁ → Reps Eb S₂ φ₂ f₂ → ∀ r : Sp Y₂.Fn ⟶ Y₁.X, r ≫ f₁ = (ratOf Y₂).pt ≫ f₂ → CoBear Eb S₁ φ₁ S₂ φ₂ (r ≫ f₁) r (ratOf Y₂).pt → ∀ (K : Type) [Field K] (p : Sp K ⟶ Y₁.X) (p' : Sp K ⟶ Y₂.X), p (IsLocalRing.closedPoint K) = r (IsLocalRing.closedPoint Y₂.Fn) → p ≫ f₁ = p' ≫ f₂ → CoBear Eb S₁ φ₁ S₂ φ₂ (p ≫ f₁) p p' → p' (IsLocalRing.closedPoint K) = genericPoint Y₂.X := by
  intro F _ ι _ m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ hR₁ hR₂ r hr hrc K _ p p' hp hpp' hc
  set y₁ := r (IsLocalRing.closedPoint Y₂.Fn)
  let c : Sp (Y₁.X.residueField y₁) ⟶ Y₁.X := Y₁.X.fromSpecResidueField y₁
  obtain ⟨τ, hτ⟩ := exists_spMap_fromSpecResidueField y₁ r rfl
  obtain ⟨σ, hσ⟩ := exists_spMap_fromSpecResidueField y₁ p hp
  obtain ⟨A, hA, g, hg, hb₁⟩ := GlobalTheory.T.exists_pointCarriesFrameFlags_own_frame F ι m X Y₁ Eb S₁ φ₁ f₁ hR₁ _ c
  obtain ⟨s, ⟨hs, hb₂⟩, -⟩ := hR₂.2.2 _ (c ≫ f₁) A hA g hg
  have hcs : CoBear Eb S₁ φ₁ S₂ φ₂ (c ≫ f₁) c s := ⟨A, hA, g, hg, hb₁, hb₂⟩
  have hτc := GlobalTheory.T.pointsCarryCommonFlag_spectrumMap_field_ext F ι m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ hR₁ hR₂ _ _ τ _ _ _ hcs
  have hσc := GlobalTheory.T.pointsCarryCommonFlag_spectrumMap_field_ext F ι m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ hR₁ hR₂ _ _ σ _ _ _ hcs
  have hτ' : spMap τ ≫ c = r := hτ
  have hσ' : spMap σ ≫ c = p := hσ
  rw [hτ'] at hτc
  rw [hσ'] at hσc
  have e₁ : (spMap τ ≫ s) ≫ f₂ = r ≫ f₁ := by rw [Category.assoc, hs, ← Category.assoc, hτ']
  have e₂ : (spMap σ ≫ s) ≫ f₂ = p ≫ f₁ := by rw [Category.assoc, hs, ← Category.assoc, hσ']
  have k₁ : spMap τ ≫ s = (ratOf Y₂).pt :=
    GlobalTheory.T.eq_of_bear_common_fullFlag F ι m X Y₂ Y₁ Eb S₂ φ₂ f₂ S₁ φ₁ f₁ hR₂ hR₁ _ _ _ r e₁ hr.symm
      (coBear_swap hτc (by rw [Category.assoc, hs])) (coBear_swap hrc hr)
  have k₂ : p' = spMap σ ≫ s :=
    GlobalTheory.T.eq_of_bear_common_fullFlag F ι m X Y₂ Y₁ Eb S₂ φ₂ f₂ S₁ φ₁ f₁ hR₂ hR₁ _ _ _ p hpp'.symm e₂
      (coBear_swap hc hpp') (coBear_swap hσc (by rw [Category.assoc, hs]))
  have hgen : s (IsLocalRing.closedPoint _) = genericPoint Y₂.X := by
    have e : (spMap τ ≫ s) (IsLocalRing.closedPoint Y₂.Fn) = s (IsLocalRing.closedPoint _) := by
      exact (Scheme.Hom.comp_apply _ _ _).trans
        (congrArg s (Subsingleton.elim (α := PrimeSpectrum (Y₁.X.residueField y₁)) _ _))
    rw [← e, k₁]
    exact Scheme.fromSpecStalk_closedPoint
  rw [k₂, ← hgen]
  exact (Scheme.Hom.comp_apply _ _ _).trans
    (congrArg s (Subsingleton.elim (α := PrimeSpectrum (Y₁.X.residueField y₁)) _ _))
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GalTiedWithLoc
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.FitGal

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem galTied_withLoc : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL), LpCmp hL → ∀ (D' : D7) (b : NBuilt hL D') (fr : OmFrame b.D), fr.jE = b.jE → (PhtOn b.A.wd fr fun _ _ _ _ => True) → (∀ x : b.D.LL0, star (x : b.D.what₂.LL) ∈ b.D.LL0) → (∀ j g, ∃ z : ℤ, eExp b.D j g = z) → (∀ v, v ∈ placesOver b.D.host.E b.D.host.pde ∨ v ∈ placesOver b.D.host.E b.D.host.pde' → IsSplitPl b.D.host v) → GlobalTheory.RowTie.ChebSplit b.D.nd → ∃ g : NGalTied (withLoc b.L), g.fr.jE = b.jE ∧ g.mt = mtL b.L b.M ∧ g.tup = b.tp.tup ∧ Nonempty (NormalizedDataCompatibility (withLoc b.L)) ∧ Nonempty (NormalizedLocalCompatibility (withLoc b.L) (mtL b.L b.M)) ∧ ∀ F : RowFrame (withLoc b.L), F.rep = b.rep → RowLocTied (withLoc b.L) g.lp F := by
  intro hL hLp D' b fr hfr hpht hstar hexp hsplit hcheb
  obtain ⟨Hk, hHk⟩ := GlobalTheory.FitHecke.heckeOpen_withLoc b.D b.cf b.jE b.A b.low b.Pq b.S b.hL b.eig b.θ b.Bs b.M b.C b.tp b.ch
    b.mt hstar hexp hsplit hcheb b.big b.L b.Sp b.Au
  let lp : LPTiedPlaceholder (withLoc b.L) := ⟨⟩
  let fr' : OmFrame (withLoc b.L) := { fr with }
  have au : AUTied (withLoc b.L) lp (mtL b.L b.M) Hk.av :=
    { Hk.au with
      emb := Hk.emb }
  let g : NGalTied (withLoc b.L) :=
    { fr := fr', lp := lp, mt := mtL b.L b.M, hecke := Hk.hecke, av := Hk.av, au := au
      rational := Hk.rational, tup := b.tp.tup, level := Hk.level }
  refine ⟨g, hfr, rfl, rfl, ⟨Hk.data⟩, ⟨Hk.cover⟩, ?_⟩
  intro F hF
  refine ⟨fun i σ v w hov Dv hα => ?_⟩
  · rw [hF] at hα ⊢
    obtain ⟨α, hS, he⟩ := b.row.2 σ v w hov Dv hα
    refine ⟨α, hS, ?_⟩
    show b.L.Y.satW i σ w = _
    rw [b.Au.satW i σ w]
    exact he

end GlobalTheory.FitGal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisFamilyConductorBoundStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_family_conductor_bound : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C) (hCS : ChoiceSide D cf M Bs.exp C tp) (hMI : MtInput D M tp.tup C.Q) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) (hE : ∀ j g, ∃ z : ℤ, eExp D j g = z) (hsp : ∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) (hCh : GlobalTheory.RowTie.ChebSplit D.nd) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T) (i : X.nd.Loc) (j : Fin D.R.m), j.1 + 1 = X.nd.j i → ∀ w, SplitOut X.nd i w → (tp.tup (X.nd.mu i) j * cf.eta⁻¹).UnrAt w := by
  first | exact @GlobalTheory.HeightCounting.tupEtaInv_unrAt_splitOut | exact GlobalTheory.HeightCounting.tupEtaInv_unrAt_splitOut | (intros; apply GlobalTheory.HeightCounting.tupEtaInv_unrAt_splitOut <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisFamilyCrystallineWeightsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_family_crystalline_weights : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C) (hCS : ChoiceSide D cf M Bs.exp C tp) (hMI : MtInput D M tp.tup C.Q) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) (hE : ∀ j g, ∃ z : ℤ, eExp D j g = z) (hsp : ∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) (hCh : GlobalTheory.RowTie.ChebSplit D.nd) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T) (i : X.nd.Loc), ∃ μ : D.naut.CG 1, D.naut.csd μ ∧ ∀ j : Fin D.R.m, j.1 + 1 = X.nd.j i → (A.chr.e1 μ).1 = tp.tup (X.nd.mu i) j := by
  first | exact @GlobalTheory.MuCLoc.exists_muC | exact GlobalTheory.MuCLoc.exists_muC | (intros; apply GlobalTheory.MuCLoc.exists_muC <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisFamilyDeterminantStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_family_determinant : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C) (hCS : ChoiceSide D cf M Bs.exp C tp) (hMI : MtInput D M tp.tup C.Q) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) (hE : ∀ j g, ∃ z : ℤ, eExp D j g = z) (hsp : ∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) (hCh : GlobalTheory.RowTie.ChebSplit D.nd) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T) (i : X.nd.Loc), ∃ κ : IsLocalRing.ResidueField (X.nd.O i) →+* Formalism.CyclotomicNorms.Fbar (X.nd.l i), ∀ y : X.nd.O i, ∃ h : (((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).toRingHom.comp (Sp.iq i)).comp (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)))) y ∈ A.pl.plB (X.nd.w i), fbCast (X.nd.w_l i) (D.what₂.places.resChar_prime (X.nd.w i)) (X.nd.lPrime i).out (A.pl.plκ (X.nd.w i) (IsLocalRing.residue (A.pl.plB (X.nd.w i)) ⟨_, h⟩)) = κ (IsLocalRing.residue (X.nd.O i) y) := by
  first | exact @GlobalTheory.ResidueLocPlace.exists_residueField_map | exact GlobalTheory.ResidueLocPlace.exists_residueField_map | (intros; apply GlobalTheory.ResidueLocPlace.exists_residueField_map <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisFamilyLocalConditionStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_family_local_condition : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C) (hCS : ChoiceSide D cf M Bs.exp C tp) (hMI : MtInput D M tp.tup C.Q) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) (hE : ∀ j g, ∃ z : ℤ, eExp D j g = z) (hsp : ∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) (hCh : GlobalTheory.RowTie.ChebSplit D.nd) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T) (i : X.nd.Loc) (V : Submodule ℂ (D.what₂.Mt (X.nd.mu i) (X.nd.j i))), V ≠ ⊥ → ∀ x x' : X.nd.X i, (∀ (w : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), SplitOut X.nd i w → IsConjPl D.host w s.w → IsUnif D.host.E s.v ϖ → 1 ≤ k → k ≤ D.R.nV → ∀ y ∈ V, NG.tN (mlX M X i).J s ϖ k ((mlX M X i).real y) = (((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).toRingHom.comp (Sp.iq i)).comp (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)))) ((X.nd.hT i w k : X.nd.X i → X.nd.O i) x) • (mlX M X i).real y) → (∀ (w : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), SplitOut X.nd i w → IsConjPl D.host w s.w → IsUnif D.host.E s.v ϖ → 1 ≤ k → k ≤ D.R.nV → ∀ y ∈ V, NG.tN (mlX M X i).J s ϖ k ((mlX M X i).real y) = (((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).toRingHom.comp (Sp.iq i)).comp (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)))) ((X.nd.hT i w k : X.nd.X i → X.nd.O i) x') • (mlX M X i).real y) → x = x' := by
  first | exact @GlobalTheory.HeckePointUniq.eq_of_eigen | exact GlobalTheory.HeckePointUniq.eq_of_eigen | (intros; apply GlobalTheory.HeckePointUniq.eq_of_eigen <;> assumption)
end

