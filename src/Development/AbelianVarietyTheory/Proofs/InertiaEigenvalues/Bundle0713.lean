import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0704
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelSubgroupRestrictedProductOfLaws
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0700
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0706
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockVectorsKilledHeisenbergAverageIsotropic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0247
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0138
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0072
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0027
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TeichmullerInertiaLabelCondition
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0134
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0332
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0243
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0189
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0123
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0709
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0107
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0179
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0705

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFCrystalHomOfEquivariantEtaleMapAinfStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_FCrystalHom_of_equivariantEtaleMap_ainf : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (T : Type) [AddCommGroup T] [Module ℤ_[l] T] (ρ : ↥(GK K) → (T →ₗ[ℤ_[l]] T)) (T' : Type) [AddCommGroup T'] [Module ℤ_[l] T'] (ρ' : ↥(GK K) → (T' →ₗ[ℤ_[l]] T')) (M M' : FCrys l ↥(OL K)) (j : M.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] T)) (j' : M'.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] T')), Realises K M (ainfObj K) (ainfId K) T ρ j → Realises K M' (ainfObj K) (ainfId K) T' ρ' j' → ∀ f : T →ₗ[ℤ_[l]] T', (∀ g x, f (ρ g x) = ρ' g (f x)) → ∃ u : FHom M M', ∀ x, j' (u.u (ainfObj K) x) = f.lTensor (WCb l) (j x) := by
  first | exact @GlobalTheory.BSP.exists_fHom_of_equivariant | exact GlobalTheory.BSP.exists_fHom_of_equivariant | (intros; apply GlobalTheory.BSP.exists_fHom_of_equivariant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinsetDoubleCosetsConjMaxCompactStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_doubleCosets_conj_maxCompact : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (h : GAf L n), ∃ T : Finset (GAf L n), ∀ g : GAf L n, ∃ γ ∈ GQ L n, ∃ t ∈ T, ∃ κ ∈ (Umax L n ⊓ (Umax L n).map (MulAut.conj h).toMonoidHom), g = γ * t * κ := by
  first | exact @GlobalTheory.ClassFinConj.exists_finset_double_cosets_conj | exact GlobalTheory.ClassFinConj.exists_finset_double_cosets_conj | (intros; apply GlobalTheory.ClassFinConj.exists_finset_double_cosets_conj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHeckeRepresentativesRightTranslateIdentityStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_heckeRepresentatives_rightTranslate_identity : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m), TransLaws R i → ∀ (B : GfC (Wc D i) → ((R.HW i (sg0 D A)).H →L[ℂ] (R.HW i (sg0 D A)).H)), (∀ (γ : GfC (Wc D i)) x y, trPair R i (γ : GA D (Wc D i)) x y = ⟪x, B γ y⟫_ℂ) → (∀ v α, GlobalTheory.UpInj.cf (Wc D i) v α = α → ∃ C, GlobalTheory.UpInj.DCRep (GlobalTheory.UpInj.cf (Wc D i) v) (GlobalTheory.UpInj.KR R i) α C) ∧ (∀ v α C, GlobalTheory.UpInj.cf (Wc D i) v α = α → GlobalTheory.UpInj.DCRep (GlobalTheory.UpInj.cf (Wc D i) v) (GlobalTheory.UpInj.KR R i) α C → ∀ γ, ∑ δ ∈ C, B (γ * δ) = B γ * ∑ δ ∈ C, B δ) := by
  first | exact @GlobalTheory.UpInj.heckeReps | exact GlobalTheory.UpInj.heckeReps | (intros; apply GlobalTheory.UpInj.heckeReps <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIdempotentPlaceChartFiniteAdeles
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef

namespace GlobalTheory.DownLift.SplitCoef

variable {D : D7}

theorem toEAf_idem_mul_eq_zero {e : AE D} (he : IsSplitIdem D e) (a : AE D) :
    toEAf D (e * a) = 0 ↔ e * a = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h, map_zero]⟩
  apply GlobalTheory.SplitScalar.adele_ext
  · rw [map_mul, GlobalTheory.SplitScalar.infPart_splitIdem he, zero_mul, map_zero]
  · rw [map_zero]
    change (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E) (finPart D (e * a)) = 0 at h
    exact (map_eq_zero_iff _ (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).injective).1 h

theorem residue_eq_zero_iff_val_lt {v : HeightOneSpectrum (𝓞 D.host.F)} (o : GlobalTheory.SplitHecke.Ov D v) :
    IsLocalRing.residue (GlobalTheory.SplitHecke.Ov D v) o = 0 ↔ Valued.v (o : Fv D.host.F v) < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
  exact ⟨fun h => lt_of_le_of_ne o.2 h, fun h => h.ne⟩

set_option maxHeartbeats 1000000 in

theorem exists_levChart : ∀ (D : D7) (e : AE D) (PP : Pl D.host.E), Formalism.L2.NTheta.IsIdemAt e PP →
    ∃ (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : Formalism.IndefR.Lev.EAf D →+* Fv D.host.F v)
      (ι : kP PP ≃+* IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v)), LevChart e PP v φ ι := by
  intro D e PP he
  obtain ⟨v, π, hπ⟩ := GlobalTheory.SplitChart.exists_chart e he.1
  obtain ⟨φ, hφ, hres⟩ := GlobalTheory.ThetaSupport.exists_chart_levels he hπ
  obtain ⟨hi, hi1⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D e PP he
  have hπe : π e = 1 := by
    have h0 : π (1 - e) = 0 := (hπ.2.1 _).2 (by rw [mul_sub, mul_one, he.1.1, sub_self])
    rw [map_sub, map_one, sub_eq_zero] at h0
    exact h0.symm
  have hint_iff : ∀ a : AE D, toEAf D (e * a) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔
      π a ∈ v.adicCompletionIntegers D.host.F := by
    intro a
    rw [← GlobalTheory.SplitHecke.isInt_Ov, ← hπ.2.2.2 a]
    exact ⟨GlobalTheory.PlaceDatum.finPart_mem_of_toEAf, GlobalTheory.IdemRes.toEAf_mem_of_finPart⟩
  have hsurj : Function.Surjective φ := fun y => by
    obtain ⟨a, ha⟩ := hπ.1 y
    exact ⟨toEAf D a, by rw [hφ, ha]⟩
  have hint : ∀ s : Formalism.L2.Herm.intAf D.host.F D.host.E, φ s ∈ v.adicCompletionIntegers D.host.F := by
    intro s
    obtain ⟨a, ha⟩ := GlobalTheory.AdjDatumNe.toEAf_surjective (D := D) (s : Formalism.IndefR.Datum.EAf D)
    rw [← ha, hφ, ← hint_iff, map_mul, ha]
    exact mul_mem hi s.2
  let g : Formalism.L2.Herm.intAf D.host.F D.host.E →+* IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v) :=
    (IsLocalRing.residue (GlobalTheory.SplitHecke.Ov D v)).comp
      ((φ.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype).codRestrict (v.adicCompletionIntegers D.host.F) hint)
  have hg : ∀ s, g s = IsLocalRing.residue (GlobalTheory.SplitHecke.Ov D v) ⟨φ s, hint s⟩ := fun s => rfl
  have hrsurj : Function.Surjective (resS D.host.F PP) := fun q => by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
    exact ⟨_, resS_oToS PP x⟩
  have hker : RingHom.ker (resS D.host.F PP) ≤ RingHom.ker g := fun s hs => by
    rw [RingHom.mem_ker] at hs ⊢
    rw [hg, residue_eq_zero_iff_val_lt]
    exact hres s hs
  let ι₀ : kP PP →+* IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v) :=
    RingHom.liftOfRightInverse (resS D.host.F PP) (Function.surjInv hrsurj) (Function.rightInverse_surjInv hrsurj) ⟨g, hker⟩
  have hι₀ : ∀ s, ι₀ (resS D.host.F PP s) = g s := fun s =>
    RingHom.liftOfRightInverse_comp_apply _ _ _ _ s
  haveI := PP.isMaximal
  letI : Field (kP PP) := Ideal.Quotient.field PP.asIdeal
  have hbij : Function.Bijective ι₀ := by
    refine ⟨RingHom.injective ι₀, fun r => ?_⟩
    obtain ⟨o, rfl⟩ := IsLocalRing.residue_surjective r
    obtain ⟨z, hz⟩ := hsurj (o : Fv D.host.F v)
    obtain ⟨a, rfl⟩ := GlobalTheory.AdjDatumNe.toEAf_surjective (D := D) z
    have hm : toEAf D e * toEAf D a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
      rw [← map_mul, hint_iff, ← hφ, hz]
      exact o.2
    refine ⟨resS D.host.F PP ⟨_, hm⟩, ?_⟩
    rw [hι₀, hg]
    congr 1
    apply Subtype.ext
    show φ (toEAf D e * toEAf D a) = (o : Fv D.host.F v)
    rw [map_mul, hz, hφ e, hπe, one_mul]
  refine ⟨v, φ, RingEquiv.ofBijective ι₀ hbij, hsurj, fun z => ?_, fun z => ?_, fun s o ho => ?_⟩
  · obtain ⟨a, rfl⟩ := GlobalTheory.AdjDatumNe.toEAf_surjective (D := D) z
    rw [hφ, hπ.2.1, ← map_mul, toEAf_idem_mul_eq_zero he.1]
  · obtain ⟨a, rfl⟩ := GlobalTheory.AdjDatumNe.toEAf_surjective (D := D) z
    rw [← map_mul, hint_iff, hφ]
  · change ι₀ (resS D.host.F PP s) = _
    rw [hι₀, hg]
    congr 1
    exact Subtype.ext ho.symm

end GlobalTheory.DownLift.SplitCoef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIrrRepQuotientOfFiniteGen
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial MeasureTheory Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.DZero
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.DZero

theorem exists_irrRep_quotient_of_finite_gen : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), GlobalTheory.PRep.IsSmooth π → Nontrivial V → ∀ s : Finset V, Submodule.span ℂ (Set.range fun p : G × s => π p.1 (p.2 : V)) = ⊤ → ∃ (σ : IrrRep G) (p : V →ₗ[ℂ] σ.V), Function.Surjective p ∧ ∀ g v, p (π g v) = σ.ρ g (p v) := by
  intro G V _ _ _ _ _ π hπ hV s hs
  classical

  have htop : ∀ N : Submodule ℂ V, (∀ (g : G), ∀ v ∈ N, π g v ∈ N) →
      Submodule.span ℂ ((s : Set V)) ≤ N → N = ⊤ := by
    intro N hN hsN
    rw [eq_top_iff, ← hs, Submodule.span_le]
    rintro _ ⟨⟨g, v⟩, rfl⟩
    exact hN g _ (hsN (Submodule.subset_span v.2))
  let S : Set (Submodule ℂ V) := {N | (∀ (g : G), ∀ v ∈ N, π g v ∈ N) ∧ N ≠ ⊤}
  have hbot : (⊥ : Submodule ℂ V) ∈ S := ⟨fun g v hv => by
    rw [Submodule.mem_bot] at hv ⊢; rw [hv, map_zero], bot_ne_top⟩
  have hcomp := Submodule.finset_span_isCompactElement (R := ℂ) s
  obtain ⟨N, -, hmax⟩ := zorn_le_nonempty₀ S (fun c hcS hc y hy => by
    have hne : c.Nonempty := ⟨y, hy⟩
    have hd : DirectedOn (· ≤ ·) c := hc.directedOn
    refine ⟨sSup c, ⟨fun g v hv => ?_, fun htop' => ?_⟩, fun z hz => le_sSup hz⟩
    · obtain ⟨M, hM, hvM⟩ := (Submodule.mem_sSup_of_directed hne hd).1 hv
      exact le_sSup hM ((hcS hM).1 g v hvM)
    · obtain ⟨M, hM, hsM⟩ := (CompleteLattice.isCompactElement_iff_le_of_directed_sSup_le _ _).1 hcomp c hne hd
        (by rw [htop']; exact le_top)
      exact (hcS hM).2 (htop M (hcS hM).1 hsM)) ⊥ hbot
  obtain ⟨hNst, hNtop⟩ := hmax.prop
  let T : Subrepresentation π := ⟨N, fun g v hv => hNst g v hv⟩
  have hT : IsCoatom T := by
    refine ⟨fun h => hNtop (congrArg Subrepresentation.toSubmodule h), fun T' hT' => ?_⟩
    by_contra hne
    have hmem : T'.toSubmodule ∈ S := ⟨fun g v hv => T'.apply_mem_toSubmodule g hv,
      fun h => hne (Subrepresentation.toSubmodule_injective h)⟩
    have heq : T'.toSubmodule = N := le_antisymm (hmax.2 hmem hT'.le) hT'.le
    exact hT'.ne (Subrepresentation.toSubmodule_injective heq.symm)
  have hi := isIrreducible_subQuot hT.covBy_top
  let q : (⊤ : Subrepresentation π).toRepresentation.IntertwiningMap (subQuot ⊤ T) :=
    ⟨Submodule.mkQ _, fun _ => rfl⟩
  have hsm : IsSmooth (subQuot ⊤ T) :=
    IsSubquotient.isSmooth ⟨⊤, q, Submodule.Quotient.mk_surjective _⟩ hπ
  let σ : IrrRep G := ⟨_, subQuot ⊤ T, hsm, hi⟩
  let p : V →ₗ[ℂ] σ.V := (Submodule.mkQ _) ∘ₗ LinearMap.codRestrict (⊤ : Subrepresentation π).toSubmodule
    LinearMap.id (fun _ => trivial)
  refine ⟨σ, p, fun w => ?_, fun g v => rfl⟩
  obtain ⟨⟨v, -⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  exact ⟨v, rfl⟩

end GlobalTheory.DZero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRepsLatticeQuotientConjugateHalfOrthogonal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.DownLift.GenQuot

open GlobalTheory.PlaceModel

variable {D : D7} {S T : HSp D}

theorem symplO_nsmul_swap (k : ℕ) (x y : WO S T) : symplO S T (k • x) y = symplO S T x (k • y) := by
  induction k with
  | zero => simp only [zero_smul, symplO_zero_left, symplO_zero_right]
  | succ n ih => rw [succ_nsmul, succ_nsmul, symplO_add_left, symplO_add_right, ih]

theorem reps_orth : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsStdChar D ψ (-1) → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ a : AE D, a * a = a → infPart D a = 0 → ∀ k : ℕ, 0 < k → ∃ Y : Finset (WO S T), Y.Nonempty ∧ (∀ y ∈ Y, IsHalf (cA D a) y ∧ k • y ∈ latH S T ΛS ΛT) ∧ (∀ y', IsHalf (cA D a) y' → k • y' ∈ latH S T ΛS ΛT → ∃! y, y ∈ Y ∧ ∃ u ∈ latH S T ΛS ΛT, IsHalf (cA D a) u ∧ y' - y = k • u) ∧ ∀ x, IsHalf a x → k • x ∈ latH S T ΛS ΛT → ((∃ u ∈ latH S T ΛS ΛT, IsHalf a u ∧ x = k • u) → ∀ y ∈ Y, ψ (symplO S T x y) = 1) ∧ ((¬ ∃ u ∈ latH S T ΛS ΛT, IsHalf a u ∧ x = k • u) → ∑ y ∈ Y, ψ (symplO S T x y) = 0) := by
  intro D ψ S T hψ ΛS ΛT hS hT a ha hinf k hk
  classical
  have hdual : ∀ u : WO S T, u.map (infPart D) = 0 →
      (u ∈ latH S T ΛS ΛT ↔ ∀ u' ∈ latH S T ΛS ΛT, ψ (symplO S T u u') = 1) :=
    (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T _ _ hψ hS hT).1
  have hfin : ∀ m : ℕ, 0 < m → ∃ R : Set (WO S T), R.Finite ∧
      ∀ t ∈ latH S T ΛS ΛT, ∃ r ∈ R, ∃ u ∈ latH S T ΛS ΛT, t = r + m • u :=
    GlobalTheory.LatFinMod.latO_finite_mod D S T _ _ hS.1.fg hT.1.fg fun _ => True
  have hsm : ∀ {b : AE D}, b * b = b → ∀ u ∈ latH S T ΛS ΛT, b • u ∈ latH S T ΛS ΛT ⊓ half S T b :=
    fun {b} hb u hu =>
    ⟨GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ b
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, hb])) u hu,
      (mem_half S T).2 (by rw [smul_smul, hb])⟩
  generalize latH S T ΛS ΛT = Λ at *
  have hc : cA D a * cA D a = cA D a := by rw [← RingHom.map_mul, ha]
  generalize hcdef : cA D a = c at *
  have tf : Function.Injective fun t : WO S T => k • t := fun x y hxy => by
    rw [← inv_smul_nsmul S T hk x, ← inv_smul_nsmul S T hk y]
    exact congrArg _ hxy

  let M : AddSubgroup (WO S T) := half S T c ⊓ Λ.comap (nsmulAddMonoidHom k)
  let N : AddSubgroup (WO S T) := (Λ ⊓ half S T c).map (nsmulAddMonoidHom k)
  have hM : ∀ y, y ∈ M ↔ IsHalf c y ∧ k • y ∈ Λ := fun y => by
    rw [isHalf_iff]; rfl
  have hN : ∀ n, n ∈ N ↔ ∃ u ∈ Λ, IsHalf c u ∧ n = k • u := fun n => by
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u, hu.1, (isHalf_iff S T).2 hu.2, rfl⟩
    · rintro ⟨u, hu, hu', rfl⟩
      exact ⟨u, ⟨hu, (isHalf_iff S T).1 hu'⟩, rfl⟩
  let N' : AddSubgroup M := N.addSubgroupOf M
  have hq : ∀ y₁ y₂ : M, ((y₁ : M ⧸ N') = y₂ ↔ (y₂ : WO S T) - y₁ ∈ N) := fun y₁ y₂ => by
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
    simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg]
    rw [neg_add_eq_sub]

  obtain ⟨R2, hR2, hR2'⟩ := hfin (k * k) (Nat.mul_pos hk hk)
  have hP : ((fun t : WO S T => k • t) ⁻¹' ((fun r => c • r) '' R2)).Finite :=
    (hR2.image _).preimage tf.injOn
  have hcover : ∀ y : M, ∃ z : M, (z : WO S T) ∈ (fun t : WO S T => k • t) ⁻¹' ((fun r => c • r) '' R2) ∧
      (z : M ⧸ N') = y := by
    rintro ⟨y, hy⟩
    obtain ⟨hyc, hyk⟩ := (hM y).1 hy
    obtain ⟨r, hr, u, hu, hru⟩ := hR2' _ hyk
    have hcu := hsm hc u hu
    have hky : c • (k • y) = k • y := by
      rw [smul_comm]; exact congrArg (k • ·) ((mem_half S T).1 ((isHalf_iff S T).1 hyc))
    have hz : k • (y - k • (c • u)) = c • r := by
      rw [smul_sub, ← hky, hru, smul_add, mul_smul, smul_comm c k (k • u), smul_comm c k u]
      abel
    have hzM : y - k • (c • u) ∈ M := by
      refine (hM _).2 ⟨(isHalf_iff S T).2 ?_, ?_⟩
      · exact sub_mem ((isHalf_iff S T).1 hyc) (nsmul_mem hcu.2 k)
      · rw [smul_sub]
        exact sub_mem hyk (nsmul_mem (nsmul_mem hcu.1 k) k)
    refine ⟨⟨_, hzM⟩, ⟨r, hr, hz.symm⟩, (hq _ _).2 ?_⟩
    show y - (y - k • (c • u)) ∈ N
    rw [sub_sub_cancel]
    exact ⟨c • u, hcu, rfl⟩
  haveI hfinQ : Finite (M ⧸ N') := by
    let P' : Set M := {z | (z : WO S T) ∈ (fun t : WO S T => k • t) ⁻¹' ((fun r => c • r) '' R2)}
    have hP' : P'.Finite := hP.preimage Subtype.val_injective.injOn
    haveI := hP'.to_subtype
    refine Finite.of_surjective (fun z : P' => ((z : M) : M ⧸ N')) fun q => ?_
    induction q using QuotientAddGroup.induction_on with
    | H y =>
      obtain ⟨z, hz, hzy⟩ := hcover y
      exact ⟨⟨z, hz⟩, hzy⟩
  letI := Fintype.ofFinite (M ⧸ N')
  let rep : M ⧸ N' → WO S T := fun q => ((Quotient.out q : M) : WO S T)
  have hrepM : ∀ q, rep q ∈ M := fun q => (Quotient.out q : M).2
  have hrep : ∀ q, ((⟨rep q, hrepM q⟩ : M) : M ⧸ N') = q := fun q => QuotientAddGroup.out_eq' q
  have hrepinj : Function.Injective rep := fun q₁ q₂ h => by
    rw [← hrep q₁, ← hrep q₂]
    simp only [h]
  refine ⟨Finset.univ.image rep, ⟨rep 0, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hy
    exact (hM _).1 (hrepM q)
  · intro y' hy'c hy'k
    have hy'M : y' ∈ M := (hM y').2 ⟨hy'c, hy'k⟩
    refine ⟨rep (⟨y', hy'M⟩ : M), ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), (hN _).1 ?_⟩, ?_⟩
    · exact (hq _ _).1 (hrep _)
    · rintro y ⟨hyY, hyN⟩
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hyY
      have := (hq ⟨rep q, hrepM q⟩ ⟨y', hy'M⟩).2 ((hN _).2 hyN)
      rw [hrep] at this
      rw [this]
  intro x hx hkx
  have hxfin : ∀ {u : WO S T}, IsHalf a u → u.map (infPart D) = 0 := fun hu =>
    GlobalTheory.PlaceVec.half_infPart hinf ((isHalf_iff S T).1 hu)
  have hkxh : IsHalf a (k • x) := (isHalf_iff S T).2 (nsmul_mem ((isHalf_iff S T).1 hx) k)
  refine ⟨?_, fun hnot => ?_⟩
  · rintro ⟨u, hu, hua, rfl⟩ y hy
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hy
    rw [symplO_nsmul_swap]
    exact (hdual u (hxfin hua)).1 hu _ ((hM _).1 (hrepM q)).2
  ·
    have hconst : ∀ y₁ y₂ : M, (y₁ : M ⧸ N') = y₂ →
        ψ (symplO S T x (y₂ : WO S T)) = ψ (symplO S T x (y₁ : WO S T)) := fun y₁ y₂ h => by
      obtain ⟨u, hu, -, hu'⟩ := (hN _).1 ((hq _ _).1 h)
      have e : (y₂ : WO S T) = y₁ + k • u := by rw [← hu']; abel
      rw [e, symplO_add_right, AddChar.map_add_eq_mul, ← symplO_nsmul_swap,
        (hdual _ (hxfin hkxh)).1 hkx u hu, mul_one]

    obtain ⟨x', hx'h, hx'⟩ := half_div S T a k hk x ((isHalf_iff S T).1 hx)
    have hx'Λ : x' ∉ Λ := fun h => hnot ⟨x', h, (isHalf_iff S T).2 hx'h, hx'.symm⟩
    have hx'fin := hxfin ((isHalf_iff S T).2 hx'h)
    obtain ⟨l, hl, hψl⟩ : ∃ l ∈ Λ, ψ (symplO S T x' l) ≠ 1 := by
      by_contra hcon
      push_neg at hcon
      exact hx'Λ ((hdual x' hx'fin).2 hcon)
    have hl' := hsm hc l hl
    obtain ⟨y₀, hy₀h, hy₀⟩ := half_div S T c k hk _ hl'.2
    have hy₀M : y₀ ∈ M := (hM _).2 ⟨(isHalf_iff S T).2 hy₀h, hy₀ ▸ hl'.1⟩
    have hψ0 : ψ (symplO S T x y₀) ≠ 1 := by
      rw [← hx', symplO_nsmul_swap, hy₀, ← hcdef, ← symplO_smul, (mem_half S T).1 hx'h]
      exact hψl

    have hsum : ∑ y ∈ Finset.univ.image rep, ψ (symplO S T x y) = ∑ q : M ⧸ N', ψ (symplO S T x (rep q)) :=
      Finset.sum_image fun q₁ _ q₂ _ h => hrepinj h
    rw [hsum]
    have hshift : ∑ q : M ⧸ N', ψ (symplO S T x (rep q)) =
        (∑ q : M ⧸ N', ψ (symplO S T x (rep q))) * ψ (symplO S T x y₀) := by
      rw [Finset.sum_mul]
      refine (Fintype.sum_equiv (Equiv.addRight ((⟨y₀, hy₀M⟩ : M) : M ⧸ N')) _ _ fun q => ?_).symm
      rw [← AddChar.map_add_eq_mul, ← symplO_add_right]
      have := hconst (⟨rep q, hrepM q⟩ + ⟨y₀, hy₀M⟩) ⟨rep (q + ((⟨y₀, hy₀M⟩ : M) : M ⧸ N')), hrepM _⟩
        (by rw [hrep, QuotientAddGroup.mk_add, hrep])
      simpa using this.symm
    have h0 : (∑ q : M ⧸ N', ψ (symplO S T x (rep q))) * (ψ (symplO S T x y₀) - 1) = 0 := by
      rw [mul_sub, mul_one, ← hshift, sub_self]
    exact (mul_eq_zero.1 h0).resolve_right (sub_ne_zero.2 hψ0)

end GlobalTheory.DownLift.GenQuot

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsStandardAdelicAddChar
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

theorem sFin_sLoc_eq (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (y : w.adicCompletion E) :
    sFin E (sLoc E w y) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.pairA E 0 (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.singleV E w y) := by
  classical
  refine Prod.ext rfl ?_
  refine Subtype.ext (funext fun v => ?_)
  change (sLoc E w y) v = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.singleV E w y v
  by_cases h : v = w
  · subst h
    rw [GlobalTheory.StdDual.singleV_self]
    exact (Pi.single_eq_same v y : (Pi.single v y : ∀ u : HeightOneSpectrum (𝓞 E), u.adicCompletion E) v = y)
  · rw [GlobalTheory.StdDual.singleV_of_ne _ h]
    exact (Pi.single_eq_of_ne h y : (Pi.single w y : ∀ u : HeightOneSpectrum (𝓞 E), u.adicCompletion E) v = 0)

theorem exists_stdPsi : ∀ (E : Type) [Field E] [NumberField E], ∃ ψ : AddChar (Ad E) ℂ, StdPsi ψ := by
  intro E _ _
  obtain ⟨ψ, hψ, -⟩ := GlobalTheory.StdCharUnique.existsUnique_isStdChar E
  let L : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf E →+ ℂ :=
    AddMonoidHom.mk' (fun x => (GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.traceInf E x : ℂ)) fun a b => by
      rw [GlobalTheory.StdCharUnique.traceInf_add, Complex.ofReal_add]
  have hL : Continuous L := Complex.continuous_ofReal.comp (GlobalTheory.StdCharUnique.continuous_traceInf E)
  have hT : ∀ x : E, L (algebraMap E _ x) = ((Algebra.trace ℚ E x : ℚ) : ℂ) := fun x => by
    show ((GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.traceInf E (algebraMap E _ x) : ℝ) : ℂ) = _
    rw [GlobalTheory.StdCharUnique.traceInf_algebraMap, Complex.ofReal_ratCast]
  have hinf : ∀ x, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.psiInf E ψ x = Complex.exp (-(2 * Real.pi * Complex.I * L x)) := fun x => by
    rw [hψ.2, GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.stdInf]
    congr 1
    show _ * ((GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.traceInf E x : ℝ) : ℂ) = -(_ * ((GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.traceInf E x : ℝ) : ℂ))
    ring
  have hv : ∀ v, ∃ y, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.psiV E ψ v y ≠ 1 := fun v => by
    obtain ⟨y, hy⟩ := GlobalTheory.StdCharLocal.psiV_ne_one_of_trace (GlobalTheory.StdAdelicChar.isCharAF_inv hψ.1) (fun a => by
      rw [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.psiInf, AddChar.inv_apply', ← Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.psiInf, hinf, hT, ← Complex.exp_neg, neg_neg]) v
    refine ⟨y, fun h1 => hy ?_⟩
    rw [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.psiV] at h1 ⊢
    rw [AddChar.inv_apply', h1, inv_one]
  refine ⟨ψ, hψ.1.1, hψ.1.2.1, hψ.1.2.2.1, fun x h => GlobalTheory.RatAnnih.adele_rat hψ.1 hv L hL hT hinf x h, fun w => ?_⟩
  obtain ⟨y, hy⟩ := hv w
  refine ⟨y, ?_⟩
  rw [sFin_sLoc_eq]
  exact hy

end GlobalTheory.CuspGeneric

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSupportedAtSplitPlaceUnitaryMatrixEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl idem SplitProj IsIdemOf IsProjAt adjCo grpCo frCo)
open GlobalTheory.DownLift.GenSplit

noncomputable section

namespace GlobalTheory.DownLift.GenSplit

theorem exists_suppAt_grpCo_eq : ∀ (D : D7) (V : HSp D) (v : FinPl D) (φ : SplitProj D v) (e : Formalism.L2.Theta.AE D),
    IsIdemOf φ e → ∀ (B g : GL (Fin V.rank) (Fv D.host.F v)), ∃ h : GA D V, Formalism.L2.Theta.SuppAt e V h ∧ grpCo φ V B h = g := by
  intro D V v φ e he B g
  obtain ⟨h, hs, hr⟩ := GlobalTheory.SplitOnto.exists_suppAt_rho_eq e v (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdA φ) he.1
    (GlobalTheory.SplitProjChart.chart_rdA D v φ e he).1 V B g
  refine ⟨h, hs, ?_⟩
  rw [← hr]
  apply Units.ext
  rw [GlobalTheory.SplitHecke.rho_val]
  rfl

end GlobalTheory.DownLift.GenSplit

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTwLFullTeich
section
noncomputable section

namespace GlobalTheory.LamTie.TrueList

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.ToricRational
open GlobalTheory.HeckeGal GlobalTheory.GalChar GlobalTheory.HeightCounting

attribute [local instance 10000] GlobalTheory.GalChar.isTorsionFree_field

theorem exists_twL_full_teich (hA : GlobalTheory.Published.GlobalArtinReciprocity) (hR : RatioConj) (D : D7) (N : NData D.R D.host D.what₂)
    (hE : IsEmpty N.Loc) (T : TwR D.LL0 N) (Z : LamDat D) (hZ : Z.Ok)
    (art : Ideles D.host.E →* Gab D.host.E N.Om) (ha : IsGlobalArtin art)
    (κ : ∀ i, FractionRing (T.O0 i) →+* Qbar (T.l i)) (ι : ∀ i, Qbar (T.l i) ≃+* ℂ)
    (hκ : ∀ i (z : ℤ_[T.l i]), κ i (algebraMap (T.O0 i) _ (algebraMap ℤ_[T.l i] (T.O0 i) z)) =
      algebraMap ℚ_[T.l i] (Qbar (T.l i)) (z : ℚ_[T.l i]))
    (hι : ∀ i (x : D.LL0), ι i (κ i (T.emb0 i x)) = D.what₂.embLL (x : D.what₂.LL))
    (hμ : ∀ i j, (Z.C.mu0 j).ValuesIn 0 ((ι i).toRingHom.comp (κ i)))
    (hχ : ∀ i a, (Z.chi a).ValuesIn 0 ((ι i).toRingHom.comp (κ i)))
    (hδ : ∀ i, IsGal art (κ i) (ι i) (Z.C.delAt (T.l i)) 0 (T.delta i))
    (hS : ∀ i P, (below P).asIdeal ∣ cond0 D.host Z.w0 → P ∈ T.S0 i)
    (hT : Z.Teich) :
    ∃ (L : TwL T) (e : ∀ i, L.abelian₂ i ≃ Idx D.R),
      (∀ i lam, L.jL i lam = (e i lam).1.1 + 1 ∧ L.sideL i lam = (e i lam).2.2.2 ∧ L.s2 i lam = 2 * ((e i lam).2.2.1.1 : ℤ) ∧
        (∃ n r, IsGal art (κ i) (sideIso (ι i) (e i lam).2.2.2) (Z.lam0 (T.l i) (e i lam).1 (e i lam).2.1) n r ∧
          L.lamG i lam = (Units.map (algebraMap (T.O0 i) (T.O i)).toMonoidHom).comp r) ∧
        ∀ P, L.qs i lam P = ((Ideal.absNorm P.asIdeal : ℕ) : FractionRing (T.O i)) ^ (-((e i lam).2.2.1.1 : ℤ))) ∧
      ∀ F : TwF T, IsLamTieFull (T.ntw hE F L) Z :=
  exists_twL_full hA hR D N hE T Z hZ art ha κ ι hκ hι hμ hχ hδ hS fun a w hw => ⟨w, rfl, hT a w hw⟩

end GlobalTheory.LamTie.TrueList
end
end

