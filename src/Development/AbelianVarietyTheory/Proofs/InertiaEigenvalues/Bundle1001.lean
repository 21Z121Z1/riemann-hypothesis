import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0998
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0997
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameMatricesIntegralOfMemCompletedLattice
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0069
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0996
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0797
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0640
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0784
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0603
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EigenCompatibleOfBadSet
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0982
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0682
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0824
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0831
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0444
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0847
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0848
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0862
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0247
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRatScalarMulIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0856
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0977
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0981
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0947
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0980
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2130
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0013
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicCharacterFactorPrimitiveOnIdempotentSum
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
noncomputable section

namespace GlobalTheory.IdemCharLift

theorem exists_factor {M ι : Type} [AddCommGroup M] (k : ι → Type) [∀ i, AddCommGroup (k i)]
    (χ : AddChar M ℂ) (Q : Finset ι) (R : ∀ i, M →+ k i)
    (hker : ∀ m, (∀ i ∈ Q, R i m = 0) → χ m = 1)
    (hlift : ∀ Y : ∀ i, k i, ∃ m, ∀ i ∈ Q, R i m = Y i) :
    ∃ ψP : ∀ i, AddChar (k i) ℂ, ∀ m, χ m = ∏ i ∈ Q, ψP i (R i m) := by
  classical
  choose L hL using hlift
  have key : ∀ m m', (∀ i ∈ Q, R i m = R i m') → χ m = χ m' := by
    intro m m' h
    have h1 := hker (m - m') (fun i hi => by rw [map_sub, h i hi, sub_self])
    calc χ m = χ ((m - m') + m') := by rw [sub_add_cancel]
      _ = χ m' := by rw [AddChar.map_add_eq_mul, h1, one_mul]
  let ψP : ∀ i, AddChar (k i) ℂ := fun i =>
    { toFun := fun a => χ (L (Pi.single i a))
      map_zero_eq_one' := by
        rw [← AddChar.map_zero_eq_one χ]
        refine key _ _ fun j hj => ?_
        rw [hL _ j hj, map_zero, Pi.single_zero, Pi.zero_apply]
      map_add_eq_mul' := fun a b => by
        rw [← AddChar.map_add_eq_mul]
        refine key _ _ fun j hj => ?_
        rw [hL _ j hj, map_add, hL _ j hj, hL _ j hj, Pi.single_add, Pi.add_apply] }
  refine ⟨ψP, fun m => ?_⟩
  have hs : χ m = χ (∑ i ∈ Q, L (Pi.single i (R i m))) := by
    refine key _ _ fun j hj => ?_
    rw [map_sum, Finset.sum_congr rfl (fun i _ => hL (Pi.single i (R i m)) j hj),
      Finset.sum_eq_single j (fun i _ hij => Pi.single_eq_of_ne (Ne.symm hij) _) (fun h => absurd hj h),
      Pi.single_eq_same]
  have hprod : ∀ (s : Finset ι) (f : ι → M), χ (∑ i ∈ s, f i) = ∏ i ∈ s, χ (f i) := by
    intro s f
    refine Finset.induction_on s ?_ ?_
    · rw [Finset.sum_empty, Finset.prod_empty, AddChar.map_zero_eq_one]
    · intro a s ha ih
      rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]
  rw [hs, hprod]
  rfl

end GlobalTheory.IdemCharLift

namespace GlobalTheory.IdemCharLift

def supG (D : D7) (e : AE D) (ϖ : 𝓞 D.host.E) : AddSubgroup (AE D) where
  carrier := {Z | e * Z = Z ∧ toEAf D (incA D (ϖ : D.host.E) * Z) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E}
  zero_mem' := ⟨mul_zero e, by rw [mul_zero, RingHom.map_zero]; exact zero_mem _⟩
  add_mem' := fun {a b} ha hb => ⟨by rw [mul_add, ha.1, hb.1], by rw [mul_add, RingHom.map_add]; exact add_mem ha.2 hb.2⟩
  neg_mem' := fun {a} ha => ⟨by rw [mul_neg, ha.1], by rw [mul_neg, RingHom.map_neg]; exact neg_mem ha.2⟩

def resG (D : D7) (e : AE D) (ϖ : 𝓞 D.host.E) (PP : Pl D.host.E) : supG D e ϖ →+ kP PP where
  toFun m := resS D.host.F PP ⟨toEAf D (incA D (ϖ : D.host.E) * m), m.2.2⟩
  map_zero' := by
    rw [← map_zero (resS D.host.F PP)]
    exact congrArg _ (Subtype.ext (by simp))
  map_add' a b := by
    rw [← map_add (resS D.host.F PP)]
    exact congrArg _ (Subtype.ext (by simp [mul_add]))

def chiA (D : D7) (ψ : AddChar (AF D.host.F) ℂ) : AddChar (AE D) ℂ :=
  ψ.compAddMonoidHom ((Algebra.trace (AF D.host.F) (AE D)).toAddMonoidHom.comp (AddMonoidHom.mulLeft (incA D D.host.xi0)))

theorem toEAf_surj (D : D7) : Function.Surjective (toEAf D) := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, RingHom.map_zero _⟩
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, RingHom.map_add _ _ _⟩
  | tmul x a => exact ⟨pairA D.host.F 0 a ⊗ₜ[D.host.F] x, rfl⟩

end GlobalTheory.IdemCharLift

namespace GlobalTheory.IdemCharLift

theorem factor_prim : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (Q : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Q → ∀ ϖ : 𝓞 D.host.E, ϖ ≠ 0 → (∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) → (∀ Z : AE D, e * Z = Z → (toEAf D Z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔ ∀ Z' : AE D, e * Z' = Z' → toEAf D Z' ∈ Formalism.L2.Herm.intAf D.host.F D.host.E → ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * (Z * Z'))) = 1)) → ∃ ψP : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ, (∀ PP ∈ Q, (ψP PP).IsPrimitive) ∧ ∀ Z : AE D, e * Z = Z → ∀ h : toEAf D (incA D (ϖ : D.host.E) * Z) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * Z)) = ∏ PP ∈ Q.attach, ψP PP.1 (resS D.host.F PP.1 ⟨toEAf D (incA D (ϖ : D.host.E) * Z), h⟩) := by
  intro D ψ Q e he ϖ hϖ0 hϖ H
  have hee : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have heI : toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    GlobalTheory.LatHalfInt.toEAf_mem_of_finPart (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, hee]))
  obtain ⟨⟨es, hes, hsum⟩, hc⟩ := he
  have hc' : (∑ PP ∈ Q, es PP) * cA D (∑ PP ∈ Q, es PP) = 0 := hsum ▸ hc
  have hϖE : (ϖ : D.host.E) ≠ 0 := by exact_mod_cast hϖ0
  have hinv : incA D ((ϖ : D.host.E)⁻¹) * incA D (ϖ : D.host.E) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hϖE, map_one]
  have hdiv : ∀ m : supG D e ϖ, (toEAf D (m : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔
      ∀ PP ∈ Q, resG D e ϖ PP m = 0) := by
    intro m
    have h1 := GlobalTheory.T.idempotentSum_integral_div_uniformisers_iff_reduction_zero D Q es (fun _ => ϖ) hes hc' (fun PP hP => hϖ PP hP)
      (toEAf D (incA D (ϖ : D.host.E) * m)) m.2.2
      (by rw [← hsum, ← map_mul, ← mul_assoc, mul_comm e, mul_assoc, m.2.1])
    have h2 : toEAf D (∑ PP ∈ Q, es PP * incA D ((ϖ : D.host.E)⁻¹)) * toEAf D (incA D (ϖ : D.host.E) * m) =
        toEAf D m := by
      rw [← Finset.sum_mul, ← hsum, ← map_mul]
      congr 1
      calc e * incA D ((ϖ : D.host.E)⁻¹) * (incA D (ϖ : D.host.E) * m)
          = (incA D ((ϖ : D.host.E)⁻¹) * incA D (ϖ : D.host.E)) * (e * m) := by ring
        _ = m := by rw [hinv, one_mul, m.2.1]
    rw [h2] at h1
    exact h1
  have hker : ∀ m : supG D e ϖ, (∀ PP ∈ Q, resG D e ϖ PP m = 0) →
      ((chiA D ψ).compAddMonoidHom (supG D e ϖ).subtype) m = 1 := by
    intro m hm
    have h1 := (H m m.2.1).1 ((hdiv m).2 hm) e hee heI
    rw [mul_comm (m : AE D) e, m.2.1] at h1
    exact h1
  have hlift : ∀ Y : ∀ PP : Pl D.host.E, kP PP, ∃ m : supG D e ϖ, ∀ PP ∈ Q, resG D e ϖ PP m = Y PP := by
    intro Y
    obtain ⟨N, hN, hNe, hNY⟩ := GlobalTheory.T.exists_integral_lift_residues_idempotentSum D Q es hes hc' Y
    obtain ⟨w, hw⟩ := toEAf_surj D N
    have hm1 : e * (e * incA D ((ϖ : D.host.E)⁻¹) * w) = e * incA D ((ϖ : D.host.E)⁻¹) * w := by
      rw [← mul_assoc, ← mul_assoc, hee]
    have hm0 : incA D (ϖ : D.host.E) * (e * incA D ((ϖ : D.host.E)⁻¹) * w) = e * w := by
      calc incA D (ϖ : D.host.E) * (e * incA D ((ϖ : D.host.E)⁻¹) * w)
          = (incA D ((ϖ : D.host.E)⁻¹) * incA D (ϖ : D.host.E)) * (e * w) := by ring
        _ = e * w := by rw [hinv, one_mul]
    have hm2 : toEAf D (incA D (ϖ : D.host.E) * (e * incA D ((ϖ : D.host.E)⁻¹) * w)) = N := by
      rw [hm0, map_mul, hw, hsum]
      exact hNe
    refine ⟨⟨_, hm1, hm2 ▸ hN⟩, fun PP hP => ?_⟩
    rw [← hNY PP hP]
    show resS D.host.F PP ⟨_, _⟩ = resS D.host.F PP ⟨N, hN⟩
    exact congrArg _ (Subtype.ext hm2)
  obtain ⟨ψP, hψP⟩ := exists_factor (fun PP : Pl D.host.E => kP PP)
    ((chiA D ψ).compAddMonoidHom (supG D e ϖ).subtype) Q (resG D e ϖ) hker hlift
  refine ⟨ψP, fun PP hP => ?_, fun Z hZ h => ?_⟩
  · haveI := PP.isMaximal
    letI := Ideal.Quotient.field PP.asIdeal
    refine AddChar.IsPrimitive.of_ne_one fun h1 => ?_
    obtain ⟨m1, hm1⟩ := hlift (Pi.single PP 1)
    have hnI : toEAf D (m1 : AE D) ∉ Formalism.L2.Herm.intAf D.host.F D.host.E := fun hI => by
      have h3 := (hdiv m1).1 hI PP hP
      rw [hm1 PP hP, Pi.single_eq_same] at h3
      exact one_ne_zero h3
    obtain ⟨Z', hZ'e, hZ'I, hne⟩ : ∃ Z' : AE D, e * Z' = Z' ∧ toEAf D Z' ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧
        ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * ((m1 : AE D) * Z'))) ≠ 1 := by
      by_contra hcon
      push_neg at hcon
      exact hnI ((H m1 m1.2.1).2 hcon)
    let m2 : supG D e ϖ := ⟨(m1 : AE D) * Z', by rw [← mul_assoc, m1.2.1],
      by rw [← mul_assoc, map_mul]; exact mul_mem m1.2.2 hZ'I⟩
    have hres : ∀ QQ : Pl D.host.E, resG D e ϖ QQ m2 =
        resG D e ϖ QQ m1 * resS D.host.F QQ ⟨toEAf D Z', hZ'I⟩ := by
      intro QQ
      show resS D.host.F QQ ⟨_, _⟩ = resS D.host.F QQ ⟨_, _⟩ * resS D.host.F QQ ⟨_, _⟩
      rw [← map_mul]
      exact congrArg _ (Subtype.ext (by
        show toEAf D (incA D (ϖ : D.host.E) * ((m1 : AE D) * Z')) = toEAf D (incA D (ϖ : D.host.E) * m1) * toEAf D Z'
        rw [← map_mul, mul_assoc]))
    have h2 := hψP m2
    rw [Finset.prod_eq_single PP (fun QQ hQ hQP => by
        rw [hres, hm1 QQ hQ, Pi.single_eq_of_ne hQP, zero_mul, AddChar.map_zero_eq_one])
      (fun h => absurd hP h), h1, AddChar.one_apply] at h2
    exact hne h2
  · exact (hψP ⟨Z, hZ, h⟩).trans (Finset.prod_attach Q (fun PP => ψP PP (resG D e ϖ PP ⟨Z, hZ, h⟩))).symm

end GlobalTheory.IdemCharLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmDZOfLabelsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admDZ_of_labels : GlobalTheory.NRows.Hypotheses₂ → GlobalTheory.Published.DepthZeroInertia → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), (∀ i : D.nd.Loc, Nonempty (RowMod D P.rep (D.nd.j i))) → LabAll D P.T → GlobalTheory.HeightCounting.Up.CenLoc D P.M → GreenLab P.ty.grp → ChiTOk D P.cf → PairedCharacterCondition.RT.AdmDepthZeroTypes (D := D) := by
  first | exact @GlobalTheory.DepthZeroRow.main | exact GlobalTheory.DepthZeroRow.main | (intros; apply GlobalTheory.DepthZeroRow.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompAtEqOneOfTameAt
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain

noncomputable section
namespace GlobalTheory.AVGood

theorem compAt_eq_one_of_tameAt {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (χ : HChar L)
    (hχ : χ.TameAt s.w) (ξ : (s.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ) (hξ : NG.IsCompAt χ s ξ)
    (u : (s.v.adicCompletion (maximalRealSubfield L))ˣ)
    (hu : Valued.v ((u : s.v.adicCompletion (maximalRealSubfield L)) - 1) < 1) : ξ u = 1 := by
  obtain ⟨ξ', hξ', hv⟩ := GlobalTheory.T.tame_heckeCharacter_split_place_local_component L s χ hχ
  have e : ξ = ξ' := GlobalTheory.T.heckeCharacter_splitPlaceComponent_unique L χ s ξ ξ' hξ hξ'
  have hu1 : Valued.v (u : s.v.adicCompletion (maximalRealSubfield L)) = 1 := by
    have h := Valuation.map_one_add_of_lt (Valued.v : Valuation (s.v.adicCompletion (maximalRealSubfield L)) _) hu
    rwa [add_sub_cancel] at h
  rw [e, hv u 1 1 (by simp) hu1 (by simpa using hu), map_one]

theorem tameAtG_of_tameAt (D : D7) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E)
    (h : ∀ (i : D.nd.Loc) (j : Fin D.R.m) (k : Fin 2) (v : D.nd.PlG k), (tup (D.nd.mu i) j).TameAt (D.naut.plGw k v)) :
    TameAtG D tup := by
  intro i j k v s ξ hw hξ u hu
  exact compAt_eq_one_of_tameAt s _ (hw ▸ h i j k v) ξ hξ u hu

theorem tameAtG_of_tupTied (D : D7) (cf : CharFrame D) {C : NChoice D} (tp : TupTied D cf C) : TameAtG D tp.tup :=
  tameAtG_of_tameAt D tp.tup fun i j _ _ x hx hx' => by
    rw [TupTied.tup, HChar.loc_mul, (cf.isMu0 j).tame _ x hx hx', tp.xi_tame _ _ x hx hx', one_mul]
end GlobalTheory.AVGood
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DirichletSeriesExponentialSumConvergesStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW Filter Topology Formalism.UG GlobalTheory.RSNonvan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dirichlet_series_exponential_sum_converges : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a b : ℕ) (σ : CG E a) (σ' : CG E b), σ.IsUnitary → σ'.IsUnitary → ∀ T : Finset (HeightOneSpectrum (𝓞 E)), UnrOutside T σ → UnrOutside T σ' → ∀ x : ℝ, 1 < x → ∃ g : ℂ, HasSum (fun p : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} × ℕ => ((dcoef σ σ' p.1.1 p.2 : ℝ) : ℂ) * Complex.exp (-((dexp p.1.1 p.2 : ℝ) : ℂ) * (x : ℂ))) g ∧ (∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, lfac σ σ (x : ℂ) w.1) * (∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, lfac σ' σ' (x : ℂ) w.1) * (∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, lfac σ σ' (x : ℂ) w.1) * (∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, lfac σ' σ (x : ℂ) w.1) = Complex.exp g := by
  first
  | exact @GlobalTheory.RSNonvan.fourProd_eq_exp
  | exact GlobalTheory.RSNonvan.fourProd_eq_exp
  | (intros; apply GlobalTheory.RSNonvan.fourProd_eq_exp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EigenOccurrenceWithLocalData
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
namespace GlobalTheory.GalLoc.EigLoc

set_option maxHeartbeats 4000000 in

theorem parIn_loc {hL : GlobalTheory.Published.LocalLanglandsGL} {D' : D7} {cf' : CharFrame D'} {C' : NChoice D'}
    {tp' : TupTied D' cf' C'} (nt : NTrue hL D' cf' C' tp') (rep' : D'.what₂.FT → NG.FinTyp D'.host.E D'.R.r)
    (hrep : HEq nt.rep rep') :
    ∃ Rw : RowSide D', HEq Rw.locR nt.A.row.locR ∧ Nonempty (ParIn hL D' cf' rep' Rw) := by
  obtain ⟨⟨D, cf, jE, A, cg, au, rep, row, low, Pq, S, hk, eig, θ, Bs, M, C, tp, ch, mt, big, L, Sp, Au, ss, eq⟩, pack⟩ := nt
  subst eq
  obtain ⟨-, h2⟩ := Sigma.mk.inj_iff.mp pack
  obtain ⟨hcf, -⟩ := Sigma.mk.inj_iff.mp (eq_of_heq h2)
  subst hcf
  have hr : rep = rep' := eq_of_heq hrep
  subst hr
  let T : GlobalTheory.RowTie.WDTie (withLoc L).nd (withLoc L).naut := { A.wdT with }
  let Rw : RowSide (withLoc L) := { A.row with }
  refine ⟨Rw, HEq.rfl, ⟨{ T := T, lab := A.lab, chr := { A.chr with }, cg := { cg with }, A := { A.au with }, au := au, row := row }⟩⟩

set_option maxHeartbeats 4000000 in

theorem transport {hL : GlobalTheory.Published.LocalLanglandsGL} {D' : D7} {cf' : CharFrame D'} {C' : NChoice D'}
    {tp' : TupTied D' cf' C'} (nt : NTrue hL D' cf' C' tp') (Sb : Finset (PlE D'.host)) (hS0 : ∀ i, Sb ⊆ D'.ntw.S0 i)
    (e : ℕ → D'.what₂.FT → ℕ → PlE D'.host → ↥D'.LL0) (he : HEq nt.eig e)
    (S' : RatDat D'.ntw) (hS : HEq (ratL nt.L nt.S) S')
    (hL' : ∀ j, ℕ → PlE D'.host → Module.End D'.what₂.LL (S'.WL j)) (hh : HEq nt.hL hL')
    (θ' : ∀ kk : Fin 2, Multiplicative (ZMod (D'.host.g kk)) →* (↥D'.LL0)ˣ) (hθ : HEq nt.θ θ')
    (Rw0 : RowSide D') (hR0 : HEq Rw0.locR nt.A.row.locR)
    (hT : GlobalTheory.TwInputs.EigTrue D' cf' Rw0 Sb e) (hO : GlobalTheory.TwInputs.EigOcc D' S' θ' hL' Sb e) :
    ∃ Sb : Finset (PlE nt.D.host), (∀ i, Sb ⊆ (withLoc nt.L).ntw.S0 i) ∧
      (∀ Rw : RowSide (withLoc nt.L), HEq Rw.locR nt.A.row.locR →
        GlobalTheory.TwInputs.EigTrue (withLoc nt.L) (cfL nt.L nt.cf) Rw Sb nt.eig) ∧
      GlobalTheory.TwInputs.EigOcc (withLoc nt.L) ({ nt.S with } : RatDat (withLoc nt.L).ntw) nt.θ nt.hL Sb nt.eig := by
  obtain ⟨⟨D, cf, jE, A, cg, au, rep, row, low, Pq, S, hk, eig, θ, Bs, M, C, tp, ch, mt, big, L, Sp, Au, ss, eq⟩, pack⟩ := nt
  subst eq
  obtain ⟨-, h2⟩ := Sigma.mk.inj_iff.mp pack
  obtain ⟨hcf, -⟩ := Sigma.mk.inj_iff.mp (eq_of_heq h2)
  subst hcf
  have e1 : ratL L S = S' := eq_of_heq hS
  subst e1
  have e2 : hk = hL' := eq_of_heq hh
  subst e2
  have e3 : θ = θ' := eq_of_heq hθ
  subst e3
  have e4 : eig = e := eq_of_heq he
  subst e4
  refine ⟨Sb, hS0, fun Rw hRw => ?_, hO⟩
  have e5 : Rw.locR = Rw0.locR := (eq_of_heq hRw).trans (eq_of_heq hR0).symm
  unfold GlobalTheory.TwInputs.EigTrue at hT ⊢
  rw [e5]
  exact hT

end GlobalTheory.GalLoc.EigLoc

namespace GlobalTheory.GalLoc.EigLoc

set_option maxHeartbeats 4000000 in

theorem eig_at : PrN → SerN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AtMem hL fun _ _ _ _ w Z _ _ t nch n c =>
    ∃ Sb : Finset (PlE c.a.nt.D.host), (∀ i, Sb ⊆ (withLoc c.a.nt.L).ntw.S0 i) ∧ (∀ Rw : RowSide (withLoc c.a.nt.L), HEq Rw.locR c.a.nt.A.row.locR → GlobalTheory.TwInputs.EigTrue (withLoc c.a.nt.L) (cfL c.a.nt.L c.a.nt.cf) Rw Sb c.a.nt.eig) ∧ GlobalTheory.TwInputs.EigOcc (withLoc c.a.nt.L) ({ c.a.nt.S with } : RatDat (withLoc c.a.nt.L).ntw) c.a.nt.θ c.a.nt.hL Sb c.a.nt.eig := by
  intro hN hS hL
  have h2 : PrN → SerN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AtMem hL fun _ _ _ _ w Z _ _ t _ _ c =>
    ∀ Sb : Finset (PlE (w.D Z).host), (∀ i, Sb ⊆ (w.D Z).ntw.S0 i) → ∃ Sb' : Finset (PlE (w.D Z).host), Sb ⊆ Sb' ∧
      (∀ i, Sb' ⊆ (w.D Z).ntw.S0 i) ∧ GlobalTheory.TwInputs.Eig.Low (w.D Z) Sb' ∧
      GlobalTheory.HeightCounting.RatSide.HeckeRd t.r.z.R t.r.z.cG c.row.kKs c.row.hk Sb' c.row.hecke.hL := GlobalTheory.T.exists_enlarged_hecke_set
  have h3 : PrN → SerN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AtMem hL fun _ _ _ _ w Z _ _ t _ _ c =>
    ∃ θ : ∀ kk : Fin 2, Multiplicative (ZMod ((w.D Z).host.g kk)) →* (↥(w.D Z).LL0)ˣ, HEq θ c.a.nt.θ ∧
      GlobalTheory.HeightCounting.RatSide.LvlPsi t.r.z.R t.r.z.F t.r.z.cG θ := GlobalTheory.T.level_character_of_local_langlands
  refine GlobalTheory.GalLoc.atMem_imp (GlobalTheory.GalLoc.atMem_and (h2 hN hS hL) (h3 hN hS hL)) ?_
  intro K B f T w Z Wt p0 t nch n xd c hE H
  obtain ⟨H2, H3⟩ := H
  obtain ⟨e⟩ := hE
  have e' : NMore (D := (w.st Z).toD7) c.row t.r.z.geo xd := e
  obtain ⟨Sb, eg, hSb, heq, hAd⟩ := e'.eig
  obtain ⟨Sb', hsub, hS0, hlow, hrd⟩ := H2 Sb hSb
  obtain ⟨θ, hθ, hψ⟩ := H3
  obtain ⟨Rw0, hRw0, ⟨hpar⟩⟩ := parIn_loc c.a.nt _ c.row.rep_eq
  have hT := GlobalTheory.TwInputs.Eig.eigTrue hL t.r.Y t.r.z.pins.char.base.lev hpar.T Rw0 hpar.row hAd hsub hlow
  have hO := GlobalTheory.TwInputs.Eig.eigOcc t.r.Y t.r.z.pins.char.base.lev t.r.intersectionNumber_baseChange.prim.unif t.r.z.pins.char.base.models.HW
    t.r.z.good.2 hψ hAd hsub hlow hrd
  rw [t.r.z.lev.C] at hT
  exact transport c.a.nt Sb' hS0 eg heq _ c.row.S_eq _ c.row.hL_eq θ hθ.symm Rw0 hRw0 hT hO

end GlobalTheory.GalLoc.EigLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCentralFlipTranslateHalfPlacesThetaPair
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.LevelSeries

theorem exists_central_flip_step : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (m : ℕ), ∃ z : GA D V, z ∈ GfC V ∧ (∀ l : ℕ, (∀ PP ∈ T, ((l : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → OneAt V l z) ∧ ∀ eT : AE D, IsIdemSum eT T → Odd m → Nat.Coprime m (GlobalTheory.Tow.badN D) → (∀ PP ∈ T, ((m : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → ∃ x : (AE D)ˣ, IsFlipDet V eT m x ∧ ∀ (M u : ℕ) (e e' : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (O : Subring ℂ), M = m * u → (∀ PP ∈ T, ((u : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → IsIdemSum e P → T ⊆ P → IsIdemSum e' ((P \ T) ∪ T.image Formalism.L2.DIV.conjPl) → zeta M ∈ O → ∀ f ∈ trSp ψ V W ΛV ΛW f₀ e M O, ∃ F ∈ trSp ψ V W ΛV ΛW f₀ e' M O, om (z, 1) (flipScal χW V W T m x • F) = f := by
  intro D ψ θ V W χV χW om ΛV ΛW sW f₀ hV T m
  by_cases h : ∃ eT : AE D, IsIdemSum eT T ∧ m ≠ 0
  · obtain ⟨eT₀, h0, hm0⟩ := h
    obtain ⟨z, hzG, hzOne, hzmt⟩ := GlobalTheory.T.exists_central_conjugateFlipScalar_finiteAdelic D V T m eT₀ h0 hm0
    refine ⟨z, hzG, hzOne, ?_⟩
    intro eT heT hodd hcop hmT
    have h1 : eT₀ * eT = eT := GlobalTheory.Tow.idemSum_mul_of_subset heT h0 subset_rfl
    have h2 : eT * eT₀ = eT₀ := GlobalTheory.Tow.idemSum_mul_of_subset h0 heT subset_rfl
    have hEq : eT = eT₀ := by rw [← h1, mul_comm, h2]
    subst hEq
    have hidem : eT * eT = eT := GlobalTheory.Tow.idemSum_mul_of_subset heT heT subset_rfl
    have hinv : incA D ((m : D.host.E)⁻¹) * (m : AE D) = 1 := by
      rw [← map_natCast (incA D) m, ← map_mul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hm0), map_one]
    have hpq : incA D ((m : D.host.E)⁻¹) ^ V.rank * (m : AE D) ^ V.rank = 1 := by
      rw [← mul_pow, hinv, one_pow]
    have hunit : (eT * incA D ((m : D.host.E)⁻¹) ^ V.rank + (1 - eT)) * (eT * (m : AE D) ^ V.rank + (1 - eT)) = 1 := by
      linear_combination (eT * eT) * hpq + (2 - incA D ((m : D.host.E)⁻¹) ^ V.rank - (m : AE D) ^ V.rank) * hidem
    let x : (AE D)ˣ := Units.mkOfMulEqOne _ _ hunit
    have hx : IsFlipDet V eT m x := hunit
    refine ⟨x, hx, ?_⟩
    obtain ⟨lam, Y, hY, hYd, hYc, hom⟩ := GlobalTheory.T.centralFlip_vacuum_eq_multiple_of_translate_mean D ψ θ V W χV χW om ΛV ΛW sW f₀ hV T m eT z heT hodd hcop hmT hzG hzmt
    have hlam := GlobalTheory.T.movedVacuum_translateSum_flipScalar D ψ θ V W χV χW om ΛV ΛW sW f₀ hV T m eT z x lam Y heT hodd hcop hmT hzG hzmt hx hY hYd hYc hom
    subst hlam
    have hs : flipScal χW V W T m x ≠ 0 := by
      unfold flipScal
      refine mul_ne_zero (inv_ne_zero (Circle.coe_ne_zero _)) (inv_ne_zero ?_)
      rw [Complex.ofReal_ne_zero, Real.sqrt_ne_zero']
      exact Nat.cast_pos.2 (Nat.pos_of_ne_zero (flipIdx_ne_zero V W T hm0))
    intro M u e e' P O hM hu he hTP he' hz
    exact GlobalTheory.T.centralFlip_maps_halfTranslates_span D ψ θ V W χV χW om ΛV ΛW sW f₀ hV T m eT z _ Y heT hodd hcop hmT hzmt hs hY hom M u e e' P O hM hu he hTP
      (GlobalTheory.T.isIdemSum_conjugatePlaces_subset_eq_flip D e eT e' P T he heT hTP he') hz
  · refine ⟨1, (GfC V).one_mem, fun l _ => oneAt_one V l, ?_⟩
    intro eT heT hodd
    exact absurd ⟨eT, heT, (Nat.pos_of_ne_zero (by rintro rfl; exact (Nat.not_odd_zero hodd))).ne'⟩ h

end GlobalTheory.LevelSeries

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHalfUniformiserFrameMatrixPrescribedReduct
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.HalfFrameLift

theorem exists_half_redM_frMapO : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (Q : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Q → ∀ ϖ : 𝓞 D.host.E, ϖ ≠ 0 → ∀ y : ∀ PP : Pl D.host.E, Matrix (Fin T.rank) (Fin S.rank) (kP PP), ∃ u : WO S T, IsHalf e u ∧ IsIntM (frMapO S T βS βT (u.map fun w => incA D (ϖ : D.host.E) * w)) ∧ ∀ PP ∈ Q, redM PP (frMapO S T βS βT (u.map fun w => incA D (ϖ : D.host.E) * w)) = y PP := by
  intro D S T βS βT Q e he ϖ hϖ y
  have hee : e * e = e := GlobalTheory.PlaceVec.idemSum_mul_self he
  obtain ⟨⟨es, hes, hsum⟩, hc⟩ := he
  subst hsum
  choose N hN hNe hNr using fun (i : Fin T.rank) (j : Fin S.rank) =>
    GlobalTheory.T.exists_integral_lift_residues_idempotentSum D Q es hes hc (fun PP => y PP i j)
  set e := ∑ PP ∈ Q, es PP with he_def
  let z : Matrix (Fin T.rank) (Fin S.rank) (EAf D) := Matrix.of N
  let A : Matrix (Fin T.rank) (Fin S.rank) (EAf D) :=
    ((βT.val : Matrix (Fin T.rank) (Fin T.rank) (EAf D)) * z : Matrix (Fin T.rank) (Fin S.rank) (EAf D)) *
      ((βS⁻¹).val : Matrix (Fin S.rank) (Fin S.rank) (EAf D))
  choose w hw using fun (i : Fin T.rank) (j : Fin S.rank) =>
    GlobalTheory.AdjDatumNe.toEAf_surjective (D := D) (A i j)
  have hϖ' : (ϖ : D.host.E) ≠ 0 := by exact_mod_cast hϖ
  have hinv : incA D (ϖ : D.host.E) * incA D (ϖ : D.host.E)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hϖ', map_one]
  let u : WO S T := Matrix.of fun i j => e * incA D (ϖ : D.host.E)⁻¹ * w i j
  have key : frMapO S T βS βT (u.map fun v => incA D (ϖ : D.host.E) * v) = z := by
    have hmap : (u.map fun v => incA D (ϖ : D.host.E) * v).map (toEAf D) = toEAf D e • A := by
      ext i j
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, u, Matrix.of_apply]
      rw [← hw i j, ← map_mul]
      congr 1
      linear_combination (e * w i j) * hinv
    unfold frMapO
    rw [hmap, Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul, Matrix.mul_assoc, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, Matrix.mul_one]
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul, z, Matrix.of_apply]
    exact hNe i j
  refine ⟨u, fun i j => ?_, ?_, fun PP hPP => ?_⟩
  · show e * (e * incA D (ϖ : D.host.E)⁻¹ * w i j) = e * incA D (ϖ : D.host.E)⁻¹ * w i j
    rw [← mul_assoc, ← mul_assoc, hee]
  · rw [key]; exact fun i j => hN i j
  · rw [key]
    funext i j
    exact (dif_pos (hN i j)).trans (hNr i j PP hPP)

end GlobalTheory.HalfFrameLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsThetaSeriesRationalVectorNeZeroOfCuspFormsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.IndefR.Links IsDedekindDomain NumberField GlobalTheory.ExportSeries Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels GlobalTheory.ConjTwist
open Formalism.L2.Host (embLL0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaSeries_rational_vector_ne_zero_of_cuspForms : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T.Q.c.F) (F : Face D A3.A) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (O : ∀ j, OMDat T.toCore Rl.toRealDat j Unit (fun _ => A3.A.μ0)), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Hk3.Core Rl.toRealDat F → Nonempty (FWTie T Rl.toRealDat κ v₀) → IoExt Rl.toRealDat → ∀ (j : Fin D.R.m), OMPins T Rl.toRealDat κ v₀ O j → OneMapRow0 T Rl.toRealDat κ v₀ O j → T.toCore.cuspA ((j : ℕ) + 1) (wtA (κ j)) (κ j).n ≠ ⊥ → ∀ (c : VsV D j ℂ →ₗ[ℂ] (Rl.cV j).W), ExtC Rl.toRealDat j (inC (O j).c') (O j).c0' c → ∀ (u : ∀ ρ, lowT (Rl.MW j (sg0 D A3.A)) ρ), (∀ ρ, (u ρ : (Rl.MW j (sg0 D A3.A)).sm ρ) = v₀ j _ ρ) → ∃ (v : VsV D j D.what₂.LL) (x : VsV D j ℂ) (h : GA D (Vc D j)) (g : GA D (Wc D j)), (∀ m, ∃ q : ℚ, MvPolynomial.coeff m (v : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank) = (q : D.what₂.LL)) ∧ (x : Pol ℂ D.what₂.Tau (Vc D j).rank) = MvPolynomial.map D.what₂.embLL (v : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank) ∧ h ∈ GfC (Vc D j) ∧ ser Rl.toRealDat j A3.A.μ0 (Rl.vP j A3.A.μ0) u h (c x) g ≠ 0 := by
  first | exact @GlobalTheory.SeriesTie.RatNe.exists_ser_rat_ne | exact GlobalTheory.SeriesTie.RatNe.exists_ser_rat_ne | (intros; apply GlobalTheory.SeriesTie.RatNe.exists_ser_rat_ne <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodRowCuspParamStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_row_cusp_param : ∀ (D : D7) (Rw : RowSide D), ParLaws D → SphericalInertData.Conclusion1 D → SphericalInertData.HypEFK D → SphericalInertData.HypCM D → (∀ j, 1 ≤ j → j ≤ D.R.m → (D.sp.V j).IsDefinite) → LiftAll D Rw → (∀ σ, RowLoc D Rw σ) → GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.GoodRowCuspParam D Rw := by
  first | exact @GlobalTheory.ParAsm.goodRowCuspParam_of_lift | exact GlobalTheory.ParAsm.goodRowCuspParam_of_lift | (intros; apply GlobalTheory.ParAsm.goodRowCuspParam_of_lift <;> assumption)
end

