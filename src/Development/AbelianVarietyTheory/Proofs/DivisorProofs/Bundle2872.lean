import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0143
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0033
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0014
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2761
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2865
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2827
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1176
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2555
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2446
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2813
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0084
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0196
import ReciprocityTheory.GeometryOfNumbers.PluriharmonicAnalysis.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2780
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0025
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2651
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2764
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1583
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1051
import Development.AbelianVarietyTheory.Definitions.Divisors.GenericPointAsIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1048
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2685
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2781
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2754

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointUniformisationEndomorphismLiesOverAdjoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.Mum.AdjEnd

theorem rosati_unique : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (f g g' : D.toPre.P.A ⟶ D.toPre.P.A), IsMonHom f → IsMonHom g → IsMonHom g' → RosatiAdj D.toPre.P.A D.toPre.P.L f g → RosatiAdj D.toPre.P.A D.toPre.P.L f g' → g = g' := GlobalTheory.T.rosatiAdjoint_unique_degenerationData

theorem keepsIota : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ E : EndU U.toUnifPre, E.aB = a → E.h = h' → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (y : D.toPre.X) (g g' : GtPtF D.toPre F), GtPtF.IsIota y g → E.Act g g' → GtPtF.IsIota (h y) g' := GlobalTheory.T.uniformisationEndomorphism_carries_periodPoint_balanced

theorem aB_h_eq (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hR : AdmBase R (maximalIdeal R))
    (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]
    (U : UnifPre (maximalIdeal R) D A G) (E : EndU U) (a : D.toPre.P.A ⟶ D.toPre.P.A) (h' : D.toPre.X →+ D.toPre.X)
    (ha : IsMonHom a) (hE : FormalEnd U a h' fun e => (Over.pullback (thick R (maximalIdeal R) e)).map E.aG) :
    E.aB = a ∧ E.h = h' := by
  have := E.homG
  have := E.homB
  have hu := fun e => gtCoord_end_torus_abelian GlobalTheory.firstFiveLaws R (maximalIdeal R) hR D.toPre e G (U.gt e)
    ((Over.pullback (thick R (maximalIdeal R) e)).map E.aG) inferInstance
  have hm : ∀ e, (Over.pullback (thick R (maximalIdeal R) e)).map E.aB =
      (Over.pullback (thick R (maximalIdeal R) e)).map a := fun e =>
    (hu e).2.unique ⟨inferInstance, (E.q_lin e)⟩ ⟨inferInstance, hE.2.2.1 e⟩
  have := D.toPre.P.isAb.proper
  haveI : IsNoetherianRing R := hR.1
  refine ⟨GlobalTheory.hom_eq_of_thickenings_of_isProper R (maximalIdeal R) (IsLocalRing.maximalIdeal_le_jacobson _)
    D.toPre.P.A D.toPre.P.A _ _ fun e => ?_, ?_⟩
  · have k := congrArg (fun m => m.left ≫ pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e)) (hm e)
    simp only [GlobalTheory.EndData.map_fst] at k
    exact k
  · obtain ⟨t, ht, hi⟩ := hE.2.2.2 0
    obtain ⟨t', ht', hi'⟩ := E.i_lin 0
    exact (hu 0).1.unique ⟨t', ht', hi'⟩ ⟨t, ht, hi⟩

theorem linEnd_of_adjoint : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ g g' : G ⟶ G, LinEnd U.toUnifPre a h' g → IsMonHom g' → LBIso (cubeLB G ![fst G G ≫ g, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ g'] U.LG.L) → LinEnd U.toUnifPre a' h g' := by
  intro R _ _ _ hB D A G _ _ hG U a a' h h' hD g g' hg hg' hL
  obtain ⟨hadm, hc⟩ := hB
  have hF := GlobalTheory.UT.functorial_of_unif R (maximalIdeal R) hadm D A G hG U
  have := U.gen_hom
  have := hg.1
  have ex : ∀ b : G ⟶ G, IsMonHom b → ∃ E : EndU U.toUnifPre, E.aG = b := fun b hb => by
    obtain ⟨E, e1, -⟩ := hF.1 b (U.gen.inv ≫ (Over.pullback (jK R)).map b ≫ U.gen.hom) hb inferInstance (by simp)
    exact ⟨E, e1⟩
  obtain ⟨E, rfl⟩ := ex g hg.1
  obtain ⟨E', rfl⟩ := ex g' hg'
  obtain ⟨⟨-, hRB, -, -⟩, hFp⟩ := hF.2 E E' hL
  obtain ⟨haB, hh⟩ := aB_h_eq R hadm D A G U.toUnifPre E a h' hD.1 hg.2
  have ha' : E'.aB = a' := rosati_unique R ⟨hadm, hc⟩ D a E'.aB a' hD.1 E'.homB hD.2.1 (haB ▸ hRB) hD.2.2.1
  have hh2 : E'.h = h := by
    ext y
    let F := AlgebraicClosure (FractionRing R)
    obtain ⟨g₀, hg₀⟩ := GlobalTheory.TorusExt.exists_iota (F := F) D.tau_bimult y
    obtain ⟨g₁, hg₁, -⟩ := ((hFp F).1 g₀)
    exact GlobalTheory.IotaInj.main GlobalTheory.firstFiveLaws R (maximalIdeal R) hadm D F _ _ g₁ ((hFp F).2.1 y g₀ g₁ hg₀ hg₁)
      (keepsIota R ⟨hadm, hc⟩ D A G hG U a a' h h' hD E haB hh F y g₀ g₁ hg₀ hg₁)
  have := E'.homG
  exact ⟨inferInstance, fun e => inferInstance, fun e => GlobalTheory.Mum.EndModel.thickMap_map _ e,
    fun e => ha' ▸ E'.q_lin e, fun e => hh2 ▸ E'.i_lin e⟩

end GlobalTheory.Mum.AdjEnd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjunctionKltOfKltAlongResidueSubring
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair

namespace GlobalTheory.FieldPair

theorem adjKlt_of_klt_restrict : ∀ {L K : Type} [Field L] [Field K] (cL : ℂ →+* L) (cK : ℂ →+* K) (n : ℕ) (T : Subring L) (S : Place cL) (hS : S.Contains T) (ψ : S.ring →+* K) (f : S.ring) (w : Fin n → S.ring) (θ : S.ring →₀ ℚ) (R : Subring K), Function.Surjective ψ → (∀ a, ψ (S.const a) = cK a) → Irreducible f → TrBasis cK (fun i => ψ (w i)) → (∀ g ∈ θ.support, ψ g ≠ 0) → (∀ a ∈ R, ∃ t : T, ψ ⟨t, hS t t.2⟩ = a) → Klt cK n R (dForm cK (fun i => ψ (w i))) (Finsupp.mapDomain ψ θ) → AdjKlt cL (n + 1) T S (dForm cL (Fin.cons (f : L) (fun i => (w i : L)) : Fin (n + 1) → L)) (Finsupp.mapDomain (fun g : S.ring => (g : L)) θ + Finsupp.single (f : L) 1) := by
  intro L K _ _ cL cK n T S hS ψ f w θ R hψ hc hf hw hθ hR hK
  refine ⟨?_, ?_, ?_⟩
  · have htr := (trBasis_uniformiser_cons cL cK n S ψ f w hψ hc hf hw).1
    have hfree := (formOrd_api cL (n + 1) _ htr).1
    exact fun h0 => one_ne_zero (hfree.1 (a₁ := 1) (a₂ := 0) (by simp [h0]))
  · have hf0 : (0 : L) ≠ (f : L) := fun h => hf.ne_zero (Subtype.ext h.symm)
    have hθ0 : θ 0 = 0 := by
      by_contra h
      exact hθ 0 (Finsupp.mem_support_iff.2 h) (map_zero ψ)
    have h1 : Finsupp.mapDomain (fun g : S.ring => (g : L)) θ ((0 : S.ring) : L) = θ 0 :=
      Finsupp.mapDomain_apply Subtype.val_injective θ 0
    rw [Finsupp.add_apply, Finsupp.single_eq_of_ne hf0, add_zero]
    exact h1.trans hθ0
  intro Q hQ t u E hTQ hspan hdim hSQ hEQ hSt hEu hP
  obtain ⟨F, hF, hdisc⟩ := GlobalTheory.AdjCodimTwo.disc_residue_eq cL cK n Q hQ t u S E ψ f w θ hspan hdim
    hSQ hEQ hSt hEu hψ hc hf hw hθ hP
  rw [← hdisc]
  apply hK.lt_disc
  intro a ha
  obtain ⟨x, hx⟩ := hR a ha
  exact (hF a).2 ⟨⟨x, hS x x.2⟩, hTQ x.2, hx⟩

end GlobalTheory.FieldPair
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineOpenLocalFactorization
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem affine_factor_basicOpen_affineOpen :
    ∀ (M : Scheme.{0}) (W : M.Opens) (hW : IsAffineOpen W) (R : Type) [CommRing R] (b : Sp R ⟶ M) (p : PrimeSpectrum R),
    b p ∈ W → ∃ (f : R) (g : Γ(M, W) →+* Localization.Away f), f ∉ p.asIdeal ∧
      spMap g ≫ hW.fromSpec = spMap (algebraMap R (Localization.Away f)) ≫ b := by
  intro M W hW R _ b p hp
  have hopen : IsOpen (X := PrimeSpectrum R) (b ⁻¹ᵁ W).carrier := (b ⁻¹ᵁ W).isOpen
  obtain ⟨_, ⟨f, rfl⟩, hpf, hsub⟩ :=
    (PrimeSpectrum.isTopologicalBasis_basic_opens (R := R)).exists_subset_of_mem_open
      (a := p) (show p ∈ (b ⁻¹ᵁ W).carrier from hp) hopen
  have H : Set.range (spMap (algebraMap R (Localization.Away f)) ≫ b) ⊆ Set.range hW.fromSpec := by
    rw [IsAffineOpen.range_fromSpec]
    rintro _ ⟨x, rfl⟩
    have hx : (spMap (algebraMap R (Localization.Away f))) x ∈ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) := by
      rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away f) f]
      exact ⟨x, rfl⟩
    exact hsub hx
  let h := IsOpenImmersion.lift hW.fromSpec _ H
  refine ⟨f, (Spec.preimage h).hom, hpf, ?_⟩
  have e : spMap (Spec.preimage h).hom = h := by
    simp [spMap, Spec.map_preimage]
  rw [e]
  exact IsOpenImmersion.lift_fac _ _ _

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineOpenRingIsDomainNoetherianIntegrallyClosed
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem affineOpen_ring_isDomain_noetherian_integrallyClosed (X : Scheme.{0}) (hX : IsIntegral X)
    (hN : Geo.Tor.IsNormalScheme X) (hL : IsLocallyNoetherian X) (U : X.affineOpens)
    (hU0 : (U : X.Opens) ≠ ⊥) :
    IsDomain Γ(X, U) ∧ IsNoetherianRing Γ(X, U) ∧ IsIntegrallyClosed Γ(X, U) := by
  have hne : Nonempty (U : X.Opens) := by
    obtain ⟨x, hx⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).mp hU0
    exact ⟨⟨x, hx⟩⟩
  haveI : IsDomain Γ(X, U) := IsIntegral.component_integral (U : X.Opens)
  haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U
  refine ⟨inferInstance, inferInstance, ?_⟩
  have hUa : IsAffineOpen (U : X.Opens) := U.2
  refine IsIntegrallyClosed.of_localization_maximal fun p _ hp => ?_
  have hy : hUa.fromSpec ⟨p, hp.isPrime⟩ ∈ (U : X.Opens) := hUa.range_fromSpec.le ⟨_, rfl⟩
  letI := X.presheaf.algebra_section_stalk ⟨_, hy⟩
  have hl := hUa.isLocalization_stalk' ⟨p, hp.isPrime⟩ hy
  haveI := (hN (hUa.fromSpec ⟨p, hp.isPrime⟩)).2
  exact IsIntegrallyClosed.of_equiv
    (@IsLocalization.algEquiv _ _ p.primeCompl _ _
      (X.presheaf.algebra_section_stalk ⟨_, hy⟩) hl (Localization.AtPrime p) _ _ _).toRingEquiv

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicPointLiftsFiniteType
section
open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory MonObj Matrix Topology
open Formalism.BasicNotions ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CubeFib GlobalTheory.LieMet GlobalTheory.LieHt GlobalTheory.LocM.Frm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh GlobalTheory.Toroidal GlobalTheory.HeightParts GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.BdFib
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CovLift

theorem exists_lift_of_locallyOfFiniteType : ∀ (V Y : Scheme.{0}) (π : V ⟶ Y), LocallyOfFiniteType π → ∀ (K : Type) [Field K] [IsAlgClosed K] (y : Sp K ⟶ Y) (u : V), π u = y (IsLocalRing.closedPoint K) → ∃ w : Sp K ⟶ V, w ≫ π = y := by
  intro V Y π hπ K _ _ y u hu
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := π) (g := y) u (IsLocalRing.closedPoint K) hu
  have : JacobsonSpace ↥(pullback π y : Scheme.{0}) := LocallyOfFiniteType.jacobsonSpace (pullback.snd π y)
  obtain ⟨c, -, hc'⟩ := nonempty_inter_closedPoints (X := ↥(pullback π y : Scheme.{0})) (Z := Set.univ) ⟨z, trivial⟩
    isOpen_univ.isLocallyClosed
  have hc : IsClosed {c} := hc'
  refine ⟨pointOfClosedPoint (pullback.snd π y) c hc ≫ pullback.fst π y, ?_⟩
  rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc]

end GlobalTheory.CovLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlternatingBinomialSumEqPolynomial
section
set_option autoImplicit false

noncomputable section

open MvPolynomial GlobalTheory.LineForm

namespace GlobalTheory.LineForm.PolyId

def tm (n j : ℕ) : MvPolynomial (Fin 2) ℝ := C ((-1) ^ j * ((n - j).choose j : ℝ)) * X 0 ^ (n - 2 * j) * X 1 ^ j

theorem tm_eq_zero (n j : ℕ) (h : n < j) : tm n j = 0 := by
  simp [tm, Nat.choose_eq_zero_of_lt (show n - j < j by omega)]

theorem hs_eq (n K : ℕ) (hK : n + 1 ≤ K) : hs n = ∑ j ∈ Finset.range K, tm n j := by
  unfold hs
  exact Finset.sum_subset (Finset.range_mono hK) (fun j hj hj' => by
    simp only [Finset.mem_range] at hj hj'; exact tm_eq_zero n j (by omega))

theorem pascal (n j : ℕ) : (n + 2 - (j + 1)).choose (j + 1) = (n - j).choose j + (n + 1 - (j + 1)).choose (j + 1) := by
  rcases le_or_gt j n with h | h
  · rw [show n + 2 - (j + 1) = (n - j) + 1 by omega, show n + 1 - (j + 1) = n - j by omega, Nat.choose_succ_succ']
  · rw [show n + 2 - (j + 1) = 0 by omega, show n - j = 0 by omega, show n + 1 - (j + 1) = 0 by omega,
      Nat.choose_eq_zero_of_lt (by omega : 0 < j + 1), Nat.choose_eq_zero_of_lt (by omega : 0 < j)]

theorem tm_rec (n j : ℕ) : tm (n + 2) (j + 1) = X 0 * tm (n + 1) (j + 1) - X 1 * tm n j := by
  have hb : C ((-1) ^ (j + 1) * ((n + 1 - (j + 1)).choose (j + 1) : ℝ)) * (X 0 : MvPolynomial (Fin 2) ℝ) ^ (n - 2 * j) =
      X 0 * (C ((-1) ^ (j + 1) * ((n + 1 - (j + 1)).choose (j + 1) : ℝ)) * X 0 ^ (n + 1 - 2 * (j + 1))) := by
    by_cases h : 2 * j + 1 ≤ n
    · rw [show n - 2 * j = (n + 1 - 2 * (j + 1)) + 1 by omega, pow_succ]; ring
    · rw [Nat.choose_eq_zero_of_lt (by omega : n + 1 - (j + 1) < j + 1)]; simp
  have hC : C ((-1) ^ (j + 1) * ((((n - j).choose j + (n + 1 - (j + 1)).choose (j + 1) : ℕ)) : ℝ)) =
      (C ((-1) ^ (j + 1) * ((n + 1 - (j + 1)).choose (j + 1) : ℝ)) - C ((-1) ^ j * ((n - j).choose j : ℝ)) :
        MvPolynomial (Fin 2) ℝ) := by
    rw [← C_sub]; congr 1; push_cast; ring
  simp only [tm]
  rw [pascal, show n + 2 - 2 * (j + 1) = n - 2 * j by omega, hC]
  linear_combination X 1 ^ (j + 1) * hb

theorem hs_rec (n : ℕ) : hs (n + 2) = X 0 * hs (n + 1) - X 1 * hs n := by
  rw [hs_eq (n + 2) (n + 2 + 1) le_rfl, hs_eq (n + 1) (n + 2 + 1) (by omega), hs_eq n (n + 2) (by omega),
    Finset.sum_range_succ', Finset.sum_range_succ' (fun j => tm (n + 1) j)]
  simp_rw [tm_rec]
  rw [Finset.sum_sub_distrib, mul_add, Finset.mul_sum, Finset.mul_sum]
  have h0 : tm (n + 2) 0 = X 0 * tm (n + 1) 0 := by simp [tm]; ring
  rw [h0]; ring

theorem eval_hs_mul (a b : ℝ) (n : ℕ) :
    (a - b) * eval ![a + b, a * b] (hs n) = a ^ (n + 1) - b ^ (n + 1) := by
  have key : ∀ n : ℕ, (a - b) * eval ![a + b, a * b] (hs n) = a ^ (n + 1) - b ^ (n + 1) ∧
      (a - b) * eval ![a + b, a * b] (hs (n + 1)) = a ^ (n + 2) - b ^ (n + 2) := by
    intro n
    induction n with
    | zero => constructor <;> simp [hs, Finset.sum_range_succ] <;> ring
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      rw [hs_rec]
      simp only [map_sub, map_mul, eval_X, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      linear_combination (a + b) * ih.2 - a * b * ih.1
  exact (key n).1

theorem integral_affine (a b : ℝ) (hab : a ≠ b) (n : ℕ) :
    ∫ t in (0:ℝ)..1, (t * a + (1 - t) * b) ^ n = (a ^ (n + 1) - b ^ (n + 1)) / (((n : ℝ) + 1) * (a - b)) := by
  have hd : a - b ≠ 0 := sub_ne_zero.mpr hab
  have e : (fun t : ℝ => (t * a + (1 - t) * b) ^ n) = fun t => (fun x : ℝ => x ^ n) ((a - b) * t + b) := by
    funext t; ring
  rw [e, intervalIntegral.integral_comp_mul_add (fun x : ℝ => x ^ n) hd, integral_pow]
  simp only [mul_zero, zero_add, mul_one, sub_add_cancel, smul_eq_mul]
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp

theorem beta_eq (j : ℕ) :
    ∫ t in (0:ℝ)..1, t ^ j * (1 - t) ^ j = (j.factorial * j.factorial : ℝ) / (2 * j + 1).factorial := by
  have h : ((j : ℝ) + j + 1) * ((j + j).choose j : ℝ) * ReciprocityTheory.GeometryOfNumbersTheory.betaNatInt j j = 1 := ReciprocityTheory.GeometryOfNumbersTheory.bI_closed j j
  have hc := Nat.choose_mul_factorial_mul_factorial (show j ≤ j + j by omega)
  rw [show j + j - j = j by omega] at hc
  have hc' : ((j + j).choose j : ℝ) * j.factorial * j.factorial = (j + j).factorial := by exact_mod_cast hc
  have hf : ((2 * j + 1).factorial : ℝ) = (2 * (j : ℝ) + 1) * (j + j).factorial := by
    rw [show 2 * j + 1 = (j + j) + 1 by omega, Nat.factorial_succ]; push_cast; ring
  have hpos : ((2 * j + 1).factorial : ℝ) ≠ 0 := by positivity
  rw [eq_div_iff hpos, hf]
  change ReciprocityTheory.GeometryOfNumbersTheory.betaNatInt j j * _ = _
  linear_combination (-(ReciprocityTheory.GeometryOfNumbersTheory.betaNatInt j j) * (2 * (j : ℝ) + 1)) * hc' + ((j.factorial : ℝ) * j.factorial) * h

theorem eval_lhs (a b : ℝ) (hab : a ≠ b) (m : ℕ) :
    eval ![a + b, a * b] (∑ j ∈ Finset.range (m + 1),
      C ((-1) ^ j * (m.choose j : ℝ) / (m + j + 1 : ℝ)) * X 0 ^ (m - j) * hs (m + j))
      = ∫ t in (0:ℝ)..1, (t * a + (1 - t) * b) ^ m * (a + b - (t * a + (1 - t) * b)) ^ m := by
  have hE : ∀ n : ℕ, eval ![a + b, a * b] (hs n) = ((n : ℝ) + 1) * ∫ t in (0:ℝ)..1, (t * a + (1 - t) * b) ^ n := by
    intro n
    rw [integral_affine a b hab n]
    have h := eval_hs_mul a b n
    have hd : a - b ≠ 0 := sub_ne_zero.mpr hab
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    linear_combination h
  have hI : ∀ t : ℝ, (t * a + (1 - t) * b) ^ m * (a + b - (t * a + (1 - t) * b)) ^ m =
      ∑ j ∈ Finset.range (m + 1), (-1) ^ j * (m.choose j : ℝ) * (a + b) ^ (m - j) * (t * a + (1 - t) * b) ^ (m + j) := by
    intro t
    rw [show a + b - (t * a + (1 - t) * b) = -(t * a + (1 - t) * b) + (a + b) by ring, add_pow (-(t * a + (1 - t) * b)) (a + b) m, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [neg_pow]; ring
  simp_rw [hI]
  rw [intervalIntegral.integral_finset_sum (fun j _ => by apply Continuous.intervalIntegrable; fun_prop)]
  simp only [map_sum, map_mul, eval_C, map_pow, eval_X, hE]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [intervalIntegral.integral_const_mul]
  simp only [Matrix.cons_val_zero]
  have hp : (m : ℝ) + j + 1 ≠ 0 := by positivity
  push_cast
  field_simp
  try ring

theorem eval_rhs (a b : ℝ) (m : ℕ) :
    ∫ t in (0:ℝ)..1, (t * a + (1 - t) * b) ^ m * (a + b - (t * a + (1 - t) * b)) ^ m = eval ![a + b, a * b] (pm m) := by
  have hI : ∀ t : ℝ, (t * a + (1 - t) * b) ^ m * (a + b - (t * a + (1 - t) * b)) ^ m =
      ∑ j ∈ Finset.range (m + 1), ((m.choose j : ℝ) * (a * b) ^ (m - j) * ((a + b) ^ 2 - 4 * (a * b)) ^ j) *
        (t ^ j * (1 - t) ^ j) := by
    intro t
    rw [← mul_pow, show (t * a + (1 - t) * b) * (a + b - (t * a + (1 - t) * b)) =
      t * (1 - t) * ((a + b) ^ 2 - 4 * (a * b)) + a * b by ring, add_pow]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_pow, mul_pow]
    ring
  simp_rw [hI]
  rw [intervalIntegral.integral_finset_sum (fun j _ => by apply Continuous.intervalIntegrable; fun_prop)]
  simp only [pm, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [intervalIntegral.integral_const_mul, beta_eq]
  simp
  ring

theorem eval_map_aeval (P : MvPolynomial (Fin 2) ℝ) (z : Fin 2 → ℂ) :
    eval z ((aeval ![X 0 + X 1, X 0 * X 1] P : MvPolynomial (Fin 2) ℝ).map (algebraMap ℝ ℂ)) =
      eval ![z 0 + z 1, z 0 * z 1] (P.map (algebraMap ℝ ℂ)) := by
  induction P using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp, aeval_X, map_X, eval_X]
    fin_cases i <;> simp

theorem eval_aeval_sym (P : MvPolynomial (Fin 2) ℝ) (x : Fin 2 → ℝ) :
    eval x (aeval ![X 0 + X 1, X 0 * X 1] P : MvPolynomial (Fin 2) ℝ) = eval ![x 0 + x 1, x 0 * x 1] P := by
  induction P using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp, aeval_X, eval_X]
    fin_cases i <;> simp

theorem eq_zero_of_symm_real (P : MvPolynomial (Fin 2) ℝ) (h : ∀ a b : ℝ, a ≠ b → eval ![a + b, a * b] P = 0) :
    P = 0 := by
  set Q : MvPolynomial (Fin 2) ℝ := aeval ![X 0 + X 1, X 0 * X 1] P with hQ
  have hQe : ∀ x : Fin 2 → ℝ, eval x Q = eval ![x 0 + x 1, x 0 * x 1] P := by
    intro x
    rw [hQ, eval_aeval_sym]
  have hXQ : (X 0 - X 1 : MvPolynomial (Fin 2) ℝ) * Q = 0 := by
    refine MvPolynomial.funext fun x => ?_
    rw [map_mul, map_zero, hQe]
    by_cases hx : x 0 = x 1
    · simp [hx]
    · simp [h _ _ hx]
  have hX : (X 0 - X 1 : MvPolynomial (Fin 2) ℝ) ≠ 0 := by
    intro h0
    have := congrArg (eval ![1, 0]) h0
    simp at this
  have hQ0 : Q = 0 := (mul_eq_zero.mp hXQ).resolve_left hX
  have hPm : P.map (algebraMap ℝ ℂ) = 0 := by
    refine GlobalTheory.FibLine.eq_zero_of_eval_symm _ fun a b => ?_
    have := eval_map_aeval P ![a, b]
    rw [← hQ, hQ0] at this
    simpa using this.symm
  exact MvPolynomial.map_injective _ (algebraMap ℝ ℂ).injective (by simpa using hPm)

end GlobalTheory.LineForm.PolyId

namespace GlobalTheory.LineForm

open PolyId in

theorem sum_choose_hs_eq_pm : ∀ m : ℕ, ∑ j ∈ Finset.range (m + 1),
    C ((-1) ^ j * (m.choose j : ℝ) / (m + j + 1 : ℝ)) * X 0 ^ (m - j) * hs (m + j) = pm m := by
  intro m
  rw [← sub_eq_zero]
  refine eq_zero_of_symm_real _ fun a b hab => ?_
  rw [map_sub, eval_lhs a b hab m, eval_rhs a b m, sub_self]

end GlobalTheory.LineForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithVarComplexPointsCompactStatement
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open GlobalTheory.Cartier GlobalTheory.CovTest.SwapLine
open ReciprocityTheory.AnForm.M GlobalTheory.ChernPoly
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arith_var_complex_points_compact : ∀ {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {D : ℕ}, IsArithVar p D →
    Finite (k →+* ℂ) ∧ ∀ σ : k →+* ℂ, CompactSpace (CxPts p σ) ∧ T2Space (CxPts p σ) ∧
      SecondCountableTopology (CxPts p σ) := by
  first | exact @GlobalTheory.IsArithVar.finite_emb_and_topology | exact GlobalTheory.IsArithVar.finite_emb_and_topology | (intros; apply GlobalTheory.IsArithVar.finite_emb_and_topology <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticHeightPolynomialInDegreesStatement
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open GlobalTheory.Cartier GlobalTheory.CovTest.SwapLine
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithmetic_height_polynomial_in_degrees : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (D : ℕ), IsArithVar p D →
    ∀ (Z : Scheme.{0}) (i : Z ⟶ Y) [IsClosedImmersion i] [IsIntegral Z] (ℓ : ℕ) [Fact ℓ.Prime]
    [Algebra (ZMod ℓ) Γ(Z, ⊤)] (e : ℕ), topologicalKrullDim Z = e → ∀ (ι : Type) [Fintype ι] (L : ι → HermLB p),
    ∃ T : MvPolynomial ι ℝ →ₗ[ℝ] ℝ, ∀ (n : ι → ℤ) (g : Y → ℝ), (comb L n).IsArithHeight g →
      g (i (genericPoint Z)) = T (lin (fun j => (n j : ℝ)) ^ e) := by
  first | exact @GlobalTheory.VertFun.exists_vertical_functional | exact GlobalTheory.VertFun.exists_vertical_functional | (intros; apply GlobalTheory.VertFun.exists_vertical_functional <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticVarietyDivisorDimensionStatement
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open GlobalTheory.Cartier GlobalTheory.CovTest.SwapLine
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithmetic_variety_divisor_dimension : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (D : ℕ), IsArithVar p D →
    ∀ (Z : Scheme.{0}) (i : Z ⟶ Y) [IsClosedImmersion i] [IsIntegral Z],
    Order.coheight (i (genericPoint Z)) = 1 → topologicalKrullDim Z = D := by
  first | exact @GlobalTheory.CodimOneDim.topologicalKrullDim_eq_of_coheight_eq_one | exact GlobalTheory.CodimOneDim.topologicalKrullDim_eq_of_coheight_eq_one | (intros; apply GlobalTheory.CodimOneDim.topologicalKrullDim_eq_of_coheight_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AuxiliarySetLAdicPlaceStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct

set_option autoImplicit false
noncomputable section
open scoped Classical
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.auxiliary_set_l_adic_place : GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.PolarisationModule → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (d : ℕ)
    (φ : I → E →+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ → ∀ (𝔣 : Ideal (OF E)), IsBaseCond 𝔣 →
    ∀ (l : ℕ) [Fact l.Prime] (Q : Finset (HeightOneSpectrum (OF E))), IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) →
    ∀ y : (Af E)ˣ, OneOver l y → ∀ (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (R : Subring ℂ) [IsDiscreteValuationRing R],
    GlobalTheory.LatModel.IsPlaceRing E l lam R → ∀ (j : FractionRing R →+* ℂ), (∀ x : R, j (algebraMap R (FractionRing R) x) = x) →
    ∀ (ξ : E) (e₀ : ℤˣ), ξ ∈ GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.polPos φ e₀ (GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.latMod (condQ 𝔣 Q) y) →
      GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.GenAt l (GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.polMod (GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.latMod (condQ 𝔣 Q) y)) ξ →
      ξ ≠ 0 ∧ ∀ σ : E →+* FractionRing R, GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (σ ξ) ≤ 0 := by
  first | exact @GlobalTheory.XiSize.xi_size | exact GlobalTheory.XiSize.xi_size | (intros; apply GlobalTheory.XiSize.xi_size <;> assumption)
end
end

