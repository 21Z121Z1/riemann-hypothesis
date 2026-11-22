import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0366
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0005
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0007
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0263
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumLocalCongruenceLengthEqRationalLength
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0360
import Formalism.SharpRestriction.LevelLetterCocycles.TWSet
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0205
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0011
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0034
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0332
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0230
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0351
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0365
import Formalism.AdmissibleDesigns.Bundle0001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0304
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0367

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StrictIndepPowOfRegularPairStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.strict_indep_pow_of_regular_pair : ∀ (S A : Type) [CommRing S] [CommRing A] (s : S →+* A) (p q : S) (ι : Type) (b : ι → A), (∀ x : A, s p * x = 0 → x = 0) → (∀ x : A, s p ∣ s q * x → s p ∣ x) → (∀ a : ι →₀ S, a.sum (fun i y => s y * b i) ∈ (Ideal.span {p} ⊔ Ideal.span {q}).map s → ∀ i, a i ∈ Ideal.span {p} ⊔ Ideal.span {q}) → ∀ n : ℕ, ∃ m : ℕ, ∀ a : ι →₀ S, a.sum (fun i y => s y * b i) ∈ ((Ideal.span {p} ⊔ Ideal.span {q}) ^ m).map s → ∀ i, a i ∈ (Ideal.span {p} ⊔ Ideal.span {q}) ^ n := by
  first | exact @GlobalTheory.BSP.strict_indep_pow | exact GlobalTheory.BSP.strict_indep_pow | (intros; apply GlobalTheory.BSP.strict_indep_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StructureUnramifiedAdjoinSqrtNegPrime
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.SqrtNegL

open Polynomial

theorem natDegree_minpoly_sqrt (l : ℕ) [Fact l.Prime] (F : IntermediateField ℚ_[l] (Om l)) (y : Om l)
    (hF : F ≤ MaximalUnramifiedExtension l) (hy : y ^ 2 = -(l : Om l)) (hyK : y ∉ MaximalUnramifiedExtension l) :
    (minpoly F y).natDegree = 2 := by
  have hint : IsIntegral F y := (Algebra.IsIntegral.isIntegral (R := ℚ_[l]) y).tower_top
  have hmon : (X ^ 2 + C ((l : ℕ) : F)).Monic :=
    (monic_X_pow 2).add_of_left (degree_C_le.trans_lt (by simp))
  have hdeg : (X ^ 2 + C ((l : ℕ) : F)).natDegree = 2 := by
    rw [natDegree_add_eq_left_of_natDegree_lt] <;> simp
  have hev : aeval y (X ^ 2 + C ((l : ℕ) : F)) = 0 := by
    simp [hy]
  have h1 : (minpoly F y).natDegree ≤ 2 :=
    hdeg ▸ natDegree_le_natDegree (minpoly.min F y hmon hev)
  have h2 : 0 < (minpoly F y).natDegree := minpoly.natDegree_pos hint
  have h3 : (minpoly F y).natDegree ≠ 1 := by
    intro h
    obtain ⟨a, ha⟩ := minpoly.natDegree_eq_one_iff.mp h
    apply hyK
    rw [← ha]
    exact hF a.2
  omega

theorem structure_sqrt_neg : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (K : FinExt l) (M : IntermediateField ℚ_[l] (Om l)) (y : Om l), M ≤ MaximalUnramifiedExtension l → y ^ 2 = -(l : Om l) → y ∉ MaximalUnramifiedExtension l → y ∈ IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ (l ^ 1) = 1} → K.1 = M ⊔ IntermediateField.adjoin ℚ_[l] {y} → K.1 = K0 K ⊔ IntermediateField.adjoin ℚ_[l] {y} ∧ K.1 ≤ Ks K 1 ∧ Module.finrank ↥(K0 K) ↥K.1 = 2 ∧ Module.finrank ℚ_[l] ↥(Ks K 1) = (l - 1) / 2 * Module.finrank ℚ_[l] ↥K.1 := by
  intro l _ hl2 K M y hM hy hyK hyz hK
  have hyK1 : y ∈ K.1 := hK ▸ (le_sup_right : IntermediateField.adjoin ℚ_[l] {y} ≤ _)
      (IntermediateField.mem_adjoin_simple_self _ _)
  have hMK0 : M ≤ K0 K := le_inf (hK ▸ le_sup_left) hM
  have hA : IntermediateField.adjoin ℚ_[l] {y} ≤ K.1 :=
    (IntermediateField.adjoin_simple_le_iff).2 hyK1
  have e1 : K.1 = K0 K ⊔ IntermediateField.adjoin ℚ_[l] {y} :=
    le_antisymm (hK.le.trans (sup_le_sup_right hMK0 _)) (sup_le inf_le_left hA)
  have e2 : K.1 ≤ Ks K 1 := by
    rw [e1]
    exact sup_le_sup_left ((IntermediateField.adjoin_simple_le_iff).2 hyz) _
  have hd := natDegree_minpoly_sqrt l (K0 K) y inf_le_right hy hyK
  have hf : Module.finrank ℚ_[l] ↥K.1 = Module.finrank ℚ_[l] ↥(K0 K) * 2 := by
    rw [← hd, ← GlobalTheory.HubLoc.finrank_sup_adjoin, ← e1]
  have hpos := GlobalTheory.HubLoc.finrank_maxUnramifiedSubfield_padicFinExt_pos K
  have := K.2
  have htow := Module.finrank_mul_finrank ℚ_[l] ↥(K0 K) ↥K.1
  have e3 : Module.finrank ↥(K0 K) ↥K.1 = 2 := by
    rw [hf] at htow
    exact Nat.eq_of_mul_eq_mul_left hpos htow
  refine ⟨e1, e2, e3, ?_⟩
  rw [GlobalTheory.HubLoc.finrank_Ks_eq l K 1 one_pos, hf]
  have hodd : Odd l := (Fact.out : l.Prime).odd_of_ne_two hl2
  have hev : 2 ∣ l - 1 := by
    obtain ⟨k, hk⟩ := hodd
    exact ⟨k, by omega⟩
  obtain ⟨k, hk⟩ := hev
  rw [hk]
  rw [Nat.sub_self, pow_zero, one_mul]
  rw [Nat.mul_div_cancel_left k two_pos]
  ring

end GlobalTheory.SqrtNegL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumLocalCongruenceLengthEqRationalLengthStatement
section
open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_localCongruenceLength_eq_rationalLength : ∀ (D : D7) (M : MtFam D) (T : NormalizedLocalCompatibility D M) (j : ℕ) (w : D.what₂.places.Pl), 1 ≤ j → j ≤ D.R.m → D.what₂.muAt w ≠ D.what₂.mu0 → HeckeStdTw T.B → LatStable T.B j w → ZRat D (D.what₂.muTw w) j → (∀ i ∈ D.nd.locs j w, SpecPr D i) → D.what₂.etaJ j w = etaRat D (D.what₂.muTw w) j w := by
  first | exact @GlobalTheory.EtaJoinSum.sum_etaLoc_eq_etaRat | exact GlobalTheory.EtaJoinSum.sum_etaLoc_eq_etaRat | (intros; apply GlobalTheory.EtaJoinSum.sum_etaLoc_eq_etaRat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SurjConj
section
noncomputable section

open GlobalTheory.LiftLeaf GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw Formalism.BasicNotions Formalism.MainNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.UnivCharIne

theorem surj_conj (D : D7) {B : Type} [CommGroup B] (χ : G D.host.E D.nd.Om →* B) (hA : AntiHom D.ntw.cc χ)
    {P P' : PlE D.host} (hPP : IsConjPl D.host P P')
    (hs : ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A P → ∀ b : B, ∃ σ ∈ Ine (F := D.host.E) A, χ σ = b)
    (A : ValuationSubring D.nd.Om) (hA' : IsPlaceOver A P') (b : B) : ∃ σ ∈ Ine (F := D.host.E) A, χ σ = b := by
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  have hst : ∀ x : D.host.E, IsCMField.complexConj D.host.E x = D.host.conj x :=
    Formalism.BasicNotions.bridge_star_holds D.R D.host
  obtain ⟨⟨j, hj⟩, -⟩ := D.ntw.cc_cm
  have hκ : ∀ x, D.host.conj (D.host.conj x) = x := fun x => by
    rw [← hst, ← hst, IsCMField.complexConj_apply_apply]
  have hc : ∀ x, D.ntw.cc (algebraMap D.host.E D.nd.Om x) =
      algebraMap D.host.E D.nd.Om (D.host.conj x) := fun x => by
    apply j.injective
    rw [hj, ← hst]
    exact (IsCMField.complexEmbedding_complexConj D.host.E
      (j.comp (algebraMap D.host.E D.nd.Om)) x).symm
  have hs' : ∀ x, D.ntw.cc.symm (algebraMap D.host.E D.nd.Om x) =
      algebraMap D.host.E D.nd.Om (D.host.conj x) := fun x => by
    rw [RingEquiv.symm_apply_eq, hc, hκ]
  have hinv : ∀ x, D.ntw.cc (D.ntw.cc x) = x := fun x => by
    apply j.injective
    rw [hj, hj]
    simp
  have hsymm : ∀ x, D.ntw.cc.symm x = D.ntw.cc x := fun x => by
    rw [RingEquiv.symm_apply_eq, hinv]
  have hP'P := GlobalTheory.GalChar.isConjPl_symm hPP
  have hpl : IsPlaceOver (A.comap D.ntw.cc.symm.toRingHom) P := fun y => by
    have hint : IsIntegral ℤ (D.host.conj (y : D.host.E)) := by
      rw [← hst]
      exact (RingOfIntegers.isIntegral_coe y).map
        ((IsCMField.complexConj D.host.E).toRingEquiv.toRingHom.toIntAlgHom)
    rw [GlobalTheory.AntiRam.valuation_comap_lt_one, hs', ← hP'P ⟨_, hint⟩ y (hκ _).symm]
    exact hA' ⟨_, hint⟩
  obtain ⟨σ, hσ, hσb⟩ := hs _ hpl b⁻¹
  obtain ⟨σ', h1, h2⟩ := GlobalTheory.AntiRam.exists_conj_mem_Ine D.ntw.cc (fun x => D.host.conj x) hc hκ _ σ hσ
  have eA : (A.comap D.ntw.cc.symm.toRingHom).comap D.ntw.cc.symm.toRingHom = A := by
    ext y
    show D.ntw.cc.symm (D.ntw.cc.symm y) ∈ A ↔ y ∈ A
    rw [hsymm, hsymm, hinv]
  refine ⟨σ', eA ▸ h2, ?_⟩
  rw [hA σ σ' h1, hσb, inv_inv]

theorem delU_ine : ∀ D : D7, GlobalTheory.UnivChar.IsUnivChar D.nexp → (∀ (i : D.ntw.Tw) (Q : Finset (PlE D.host)) (M : ℕ), Formalism.MainNotions.NAdm.AdmQ D.ntw i Q M → ∀ P (hP : P ∈ Q), (∀ A : ValuationSubring D.nd.Om, IsPlaceOver A P → Function.Surjective fun σ : Ine (F := D.host.E) A => Multiplicative.toAdd (D.nexp.delU i Q M σ) ⟨P, hP⟩) ∧ ∀ P' ∈ Q, P' ≠ P → ¬ IsConjPl D.host P P' → ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A P' → ∀ σ ∈ Ine (F := D.host.E) A, Multiplicative.toAdd (D.nexp.delU i Q M σ) ⟨P, hP⟩ = 0) := by
  intro D hU i Q M hQ P hP
  obtain ⟨-, hQ'⟩ := hQ
  have hcl : ∀ P ∈ Q, ∀ P', IsConjPl D.host P P' → P' ∈ Q := fun P hP P' h => by
    obtain ⟨⟨P'', hP'', h''⟩, -⟩ := hQ' P hP
    rwa [GlobalTheory.GalChar.isConjPl_unique h h'']
  obtain ⟨-, χ, h1, h2, h3, h4, h5⟩ := hQ' P hP
  have hsP : ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A P →
      ∀ b, ∃ σ ∈ Ine (F := D.host.E) A, χ σ = b := fun A hA b => by
    obtain ⟨σ, hσ⟩ := h5 A hA (Multiplicative.toAdd b)
    exact ⟨σ.1, σ.2, Multiplicative.toAdd.injective hσ⟩
  have hDel : GlobalTheory.GalChar.IsDel D.host D.ntw.cc (D.ntw.l i) M (GlobalTheory.GalChar.pair D.host P) χ := by
    refine ⟨h1, h2, h3, fun v hv => h4 v (fun e => hv (Or.inl e)) (fun e => hv (Or.inr e)), fun v hv A hA b => ?_⟩
    rcases hv with rfl | hv
    · exact hsP A hA b
    · exact surj_conj D χ h2 hv hsP A hA b
  have hD := GlobalTheory.GalChar.isDel_delOf D.host D.ntw.cc (D.ntw.l i) ⟨χ, hDel⟩
  have e : ∀ σ, Multiplicative.toAdd (D.nexp.delU i Q M σ) ⟨P, hP⟩ =
      Multiplicative.toAdd (GlobalTheory.GalChar.delOf D.host D.ntw.cc (D.ntw.l i) M (GlobalTheory.GalChar.pair D.host P) σ) := by
    intro σ
    rw [hU]
    exact (GlobalTheory.GalChar.universal_anticyclotomic_character_laws D.host D.ntw.cc (D.ntw.l i)).2.2.2.2.2.2.1 Q M hcl P hP σ
  refine ⟨fun A hA x => ?_, fun P' _ hne hnc A hA σ hσ => ?_⟩
  · obtain ⟨σ, hσ, hx⟩ := hD.2.2.2.2 P (Or.inl rfl) A hA (Multiplicative.ofAdd x)
    exact ⟨⟨σ, hσ⟩, by simp only [e, hx, toAdd_ofAdd]⟩
  · rw [e, hD.2.2.2.1 P' (by rintro (h | h); exacts [hne h, hnc h]) A hA σ hσ]
    rfl

end GlobalTheory.UnivCharIne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.T2SpaceCoefficientRing
section
noncomputable section

namespace GlobalTheory.ComplementCompare

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions.N ReciprocityTheory.Gal
open GlobalTheory.IndefiniteRowSideFullHecke

section General

variable {k Γ : Type} [Field k] [Group Γ]

theorem semisimple_congr {V W : Type} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    {ρ : Representation k Γ V} {σ : Representation k Γ W} (e : V ≃ₗ[k] W)
    (he : ∀ g v, e (ρ g v) = σ g (e v)) :
    ρ.IsSemisimpleRepresentation ↔ σ.IsSemisimpleRepresentation := by
  have he' : ∀ g w, e.symm (σ g w) = ρ g (e.symm w) := fun g w => by
    rw [LinearEquiv.symm_apply_eq, he, LinearEquiv.apply_symm_apply]
  let o : Subrepresentation ρ ≃o Subrepresentation σ :=
    { toFun := fun P => ⟨P.toSubmodule.comap e.symm.toLinearMap, fun g w hw => by
        change e.symm (σ g w) ∈ P.toSubmodule
        rw [he']
        exact P.apply_mem_toSubmodule g hw⟩
      invFun := fun Q => ⟨Q.toSubmodule.comap e.toLinearMap, fun g v hv => by
        change e (ρ g v) ∈ Q.toSubmodule
        rw [he]
        exact Q.apply_mem_toSubmodule g hv⟩
      left_inv := fun P => by ext v; simp
      right_inv := fun Q => by ext w; simp
      map_rel_iff' := by
        intro P Q
        constructor
        · intro h v hv
          have := @h (e v) (by
            change e.symm (e v) ∈ P.toSubmodule
            rw [e.symm_apply_apply]
            exact hv)
          change e.symm (e v) ∈ Q.toSubmodule at this
          rw [e.symm_apply_apply] at this
          exact this
        · intro h w hw
          exact @h (e.symm w) hw }
  exact OrderIso.complementedLattice_iff o

theorem isCompl_sub_iff {V : Type} [AddCommGroup V] [Module k V] {ρ : Representation k Γ V}
    (P Q : Subrepresentation ρ) : IsCompl P Q ↔ IsCompl P.toSubmodule Q.toSubmodule := by
  rw [isCompl_iff, isCompl_iff, disjoint_iff, disjoint_iff, codisjoint_iff, codisjoint_iff,
    ← Subrepresentation.toSubmodule_injective.eq_iff, ← Subrepresentation.toSubmodule_injective.eq_iff]
  rfl

theorem isSSRep_iff {a : ℕ} (ρ : Γ →* GL (Fin a) k) :
    IsSSRep ρ ↔ (glRep ρ).IsSemisimpleRepresentation := by
  constructor
  · intro h
    refine ⟨fun P => ?_⟩
    obtain ⟨W', h1, h2⟩ := h P.toSubmodule fun g v hv => P.apply_mem_toSubmodule g hv
    exact ⟨⟨W', fun g v hv => h1 g v hv⟩, (isCompl_sub_iff _ _).2 h2⟩
  · intro h W hW
    obtain ⟨Q, hQ⟩ := h.exists_isCompl ⟨W, fun g v hv => hW g v hv⟩
    exact ⟨Q.toSubmodule, fun g v hv => Q.apply_mem_toSubmodule g hv, (isCompl_sub_iff _ _).1 hQ⟩

variable {O : Type} [CommRing O] [IsDomain O]

theorem fracRep_eq {a : ℕ} (r : Γ →* GL (Fin a) O) :
    BlockRepresentationsSemisimple.fracRep r = RepresentationOverSumChar.repOver (FractionRing O) ((Units.coeHom _).comp r) := rfl

theorem sum_equivariant {a : ℕ} (ρ : Γ →* GL (Fin a) O) (χ : ℕ → (Γ →* Oˣ)) (t : ℕ) (g : Γ)
    (v : Fin a ⊕ Fin t → FractionRing O) :
    LinearEquiv.sumArrowLequivProdArrow (Fin a) (Fin t) (FractionRing O) (FractionRing O)
        (RepresentationOverSumChar.repOver (FractionRing O) (RepresentationOverSumChar.blockSum t ρ χ) g v) =
      BlockRepresentationsSemisimple.blockRep ρ χ t g
        (LinearEquiv.sumArrowLequivProdArrow (Fin a) (Fin t) (FractionRing O) (FractionRing O) v) := by
  rw [BlockRepresentationsSemisimple.blockRep_apply]
  have key : ∀ s : Fin a ⊕ Fin t, RepresentationOverSumChar.repOver (FractionRing O) (RepresentationOverSumChar.blockSum t ρ χ) g v s =
      ∑ s' : Fin a ⊕ Fin t, algebraMap O (FractionRing O)
        (Matrix.fromBlocks ((ρ g : GL (Fin a) O) : Matrix (Fin a) (Fin a) O) 0 0
          (Matrix.diagonal fun c : Fin t => ((χ (c.1 + 1) g : Oˣ) : O)) s s') * v s' := fun s => rfl
  refine Prod.ext (funext fun j => ?_) (funext fun c => ?_)
  · refine (key (Sum.inl j)).trans ?_
    simp [Fintype.sum_sum_type, Matrix.mulVec, dotProduct]
  · refine (key (Sum.inr c)).trans ?_
    simp [Fintype.sum_sum_type, Matrix.diagonal_apply, apply_ite]

theorem trace_repOver {n : Type} [Fintype n] [DecidableEq n] (M : Γ →* Matrix n n O) (g : Γ) :
    LinearMap.trace _ _ (RepresentationOverSumChar.repOver (FractionRing O) M g) =
      algebraMap O (FractionRing O) (M g).trace := by
  change LinearMap.trace _ _ (Matrix.toLin' ((M g).map (algebraMap O (FractionRing O)))) = _
  rw [Matrix.trace_toLin'_eq, AddMonoidHom.map_trace]

omit [IsDomain O] in
theorem trace_eq_of_charpoly_eq [Nontrivial O] {m n : Type} [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] (A : Matrix m m O) (B : Matrix n n O) (h : A.charpoly = B.charpoly) :
    A.trace = B.trace := by
  rw [Matrix.trace_eq_neg_charpoly_nextCoeff, Matrix.trace_eq_neg_charpoly_nextCoeff, h]

end General

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)

theorem ss_iff (i : N.Loc) (ρ : GE N →* GL (Fin R.r) (N.O i)) :
    BlockRepresentationsSemisimple.BlockSemisimple ρ (N.chi i) R.t ↔ RepresentationOverSumChar.IsSSSum N i ρ :=
  (semisimple_congr _ (sum_equivariant ρ (N.chi i) R.t)).symm

theorem isoBlock_iff (i : N.Loc) (r₀ : GE N →* GL (Fin R.nV) (N.O i)) (ρ : GE N →* GL (Fin R.r) (N.O i)) :
    BlockRepresentationsSemisimple.IsoBlock r₀ ρ (N.chi i) R.t ↔ RepresentationOverSumChar.SplitsAs N i r₀ ρ := by
  constructor
  · rintro ⟨e, he⟩
    refine ⟨e.trans (LinearEquiv.sumArrowLequivProdArrow _ _ _ _).symm, fun g u => ?_⟩
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.symm_apply_eq]
    refine (he g u).trans ?_
    refine Eq.trans ?_ (sum_equivariant ρ (N.chi i) R.t g _).symm
    rw [LinearEquiv.apply_symm_apply]
  · rintro ⟨e, he⟩
    refine ⟨e.trans (LinearEquiv.sumArrowLequivProdArrow _ _ _ _), fun g u => ?_⟩
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, fracRep_eq, he g u]
    exact sum_equivariant ρ (N.chi i) R.t g _

theorem isHeckeGalois_iff (i : N.Loc) (x : N.X i) (r : GE N →* GL (Fin R.nV) (N.O i)) :
    IsHeckeGalois N i x r ↔ RepresentationOverSumChar.IsRx N i x ((Units.coeHom _).comp r) :=
  and_congr Iff.rfl (and_congr (isSSRep_iff _) Iff.rfl)

theorem second_of_first (i : N.Loc) (π : N.X i) (r₀ : GE N →* GL (Fin R.nV) (N.O i))
    (ρ : GE N →* GL (Fin R.r) (N.O i)) (hr : IsHeckeGalois N i π r₀)
    (h : BlockRepresentationsSemisimple.IsComplement N i r₀ ρ) : RepresentationOverSumChar.IsComplement N i π ρ :=
  ⟨RepresentationOverSumChar.isRhoAt_of_splitsAs N i π r₀ ρ hr.2.2 ((isoBlock_iff N i r₀ ρ).1 h.rho),
    (ss_iff N i ρ).1 h.ss, h.cont⟩

theorem exists_conj_ne (H : Host R) : ∃ x y : 𝓞 H.E, (y : H.E) = H.conj (x : H.E) ∧ y - x ≠ 0 := by
  by_contra hc
  push Not at hc
  have h1 : ∀ x : 𝓞 H.E, H.conj (x : H.E) = x := fun x => by
    have := hc x ⟨H.conj x, (RingOfIntegers.isIntegral_coe x).map (H.conj.toAlgHom.restrictScalars ℤ)⟩ rfl
    exact congrArg (fun z : 𝓞 H.E => (z : H.E)) (sub_eq_zero.1 this)
  have h2 : ∀ z : H.E, H.conj z = z := fun z => by
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 H.E) z
    rw [map_div₀]
    exact congrArg₂ (· / ·) (h1 a) (h1 b)
  have := H.isCMField_hostE
  refine IsTotallyComplex.complexEmbedding_not_isReal H.φ₀ (ComplexEmbedding.isReal_iff.2 ?_)
  ext z
  exact (H.conjE_apply H.φ₀ z).symm.trans (congrArg H.φ₀ (h2 z))

theorem exists_int_sub_mem {E : Type} [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E))
    (hv : v.asIdeal.inertiaDeg ℤ = 1) (x : 𝓞 E) : ∃ n : ℤ, x - n ∈ v.asIdeal := by
  have := v.isPrime
  have : NeZero v.asIdeal := ⟨v.ne_bot⟩
  have hp := Nat.absNorm_under_prime v.asIdeal
  have h := Ideal.absNorm_pow_inertiaDeg (v.asIdeal.under ℤ) v.asIdeal
  rw [hv, pow_one] at h
  rw [h] at hp
  have : Fact (Ideal.absNorm v.asIdeal).Prime := ⟨hp⟩
  have hc : Nat.card (𝓞 E ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal := rfl
  have : Nontrivial (𝓞 E ⧸ v.asIdeal) := Ideal.Quotient.nontrivial_iff.2 v.isPrime.ne_top
  have hm := mem_zmultiples_of_prime_card hc (g := (1 : 𝓞 E ⧸ v.asIdeal)) (g' := Ideal.Quotient.mk _ x)
    one_ne_zero
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.1 hm
  refine ⟨n, Ideal.Quotient.eq.1 ?_⟩
  rw [← hn]
  simp

theorem eq_univ_of_frob (hC : GlobalTheory.TwSys.Cheb) (i : N.Loc) (s : Set (GE N)) (hs : IsClosed s)
    (h : ∀ w : PlE H, SplitOut N i w → ∀ (B : ValuationSubring N.Om) (σ : GE N),
      IsPlaceOver (F := H.E) B w → IsFrob (F := H.E) B (normV w) σ → σ ∈ s) (g : GE N) : g ∈ s := by
  classical
  by_contra hg
  have : IsGalois H.E N.Om := {}
  have hn : (fun u : GE N => u * g) ⁻¹' sᶜ ∈ nhds (1 : GE N) :=
    (hs.isOpen_compl.preimage (continuous_mul_const g)).mem_nhds (by simpa using hg)
  obtain ⟨L, hfd, hN, hL⟩ := (krullTopology_mem_nhds_one_iff_of_normal H.E N.Om _).1 hn
  have hgal : IsGalois H.E L := {}
  obtain ⟨x, y, hxy, hne⟩ := exists_conj_ne H
  have f1 : {v : PlE H | v.asIdeal ∣ Ideal.span {y - x}}.Finite :=
    Ideal.finite_factors (by simpa using hne)
  have f2 : {v : PlE H | v.asIdeal ∣ Ideal.span {((N.l i : ℕ) : 𝓞 H.E)}}.Finite :=
    Ideal.finite_factors (by simpa using (N.lPrime i).out.ne_zero)
  obtain ⟨v, hv, hf, -, B, hB, -, σ, hσ, hU⟩ := hC H.E N.Om L.fixingSubgroup L.fixingSubgroup_isOpen
    ((InfiniteGalois.normal_iff_isGalois L).2 hgal) g (f1.toFinset ∪ f2.toFinset ∪ N.S i ∪ N.Q i)
  simp only [Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_span_singleton,
    not_or] at hv
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hv
  obtain ⟨n, hx⟩ := exists_int_sub_mem v hf x
  have hsplit : IsSplitPl H v := by
    refine ⟨x - n, hx, fun z hz hzv => h1 ?_⟩
    have hz' : z = y - n := by
      apply RingOfIntegers.ext
      rw [hz]
      simp [hxy]
    have := v.asIdeal.sub_mem hzv hx
    rwa [hz', sub_sub_sub_cancel_right] at this
  have := hL hU
  simp only [Set.mem_preimage, inv_mul_cancel_right, Set.mem_compl_iff] at this
  exact this (h v ⟨hsplit, h2, h3, h4⟩ B σ hB hσ)

theorem t2Space_coefficientRing (i : N.Loc) : T2Space (N.O i) :=
  have := N.O_complete i
  (N.O_adic i).isHausdorff_iff.1 inferInstance

theorem isRx_unique (hC : GlobalTheory.TwSys.Cheb) (i : N.Loc) (x : N.X i) {m n : Type} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (M : GE N →* Matrix m m (N.O i)) (M' : GE N →* Matrix n n (N.O i))
    (h : RepresentationOverSumChar.IsRx N i x M) (h' : RepresentationOverSumChar.IsRx N i x M') :
    ∃ e : (m → KK N i) ≃ₗ[KK N i] (n → KK N i), ∀ g u,
      e (RepresentationOverSumChar.repOver (KK N i) M g u) = RepresentationOverSumChar.repOver (KK N i) M' g (e u) := by
  have := t2Space_coefficientRing N i
  have : CharZero what₂.LL := what₂.embLL.charZero
  have : CharZero (FractionRing (N.O i)) :=
    (N.embK i).charZero_iff (N.embK i).injective |>.1 inferInstance
  refine GlobalTheory.TraceIso.exists_equiv_of_trace_eq _ _ h.2.1 h'.2.1 fun g => ?_
  rw [trace_repOver, trace_repOver]
  congr 1
  refine eq_univ_of_frob N hC i {g | (M g).trace = (M' g).trace}
    (isClosed_eq h.1.matrix_trace h'.1.matrix_trace) (fun w hw B σ hB hσ => ?_) g
  exact trace_eq_of_charpoly_eq _ _ ((h.2.2 w hw B σ hB hσ).trans (h'.2.2 w hw B σ hB hσ).symm)

end GlobalTheory.ComplementCompare

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateDualityDegreeOneContinuousCocycles
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory

theorem tateDuality_degreeOne_cocycles : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l), ∀ (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDual1 (P.PD K) A.ρ A'.ρ m → ∃ β : ↥(continuousCocycles A.ρ) →ₗ[LL] ↥(continuousCocycles A'.ρ) →ₗ[LL] LL, (∀ a b, β a b = 0 ↔ CobL (P.PD K) (cupL A'.ρ m a.1 b.1)) ∧ (∀ a, (∀ b, β a b = 0) ↔ a.1 ∈ B1 A.ρ) ∧ ∀ b, (∀ a, β a b = 0) ↔ b.1 ∈ B1 A'.ρ := by
  intro hT l _ P K LL _ _ _ O _ _ hO A A' m hm
  obtain ⟨β, hβ⟩ := GlobalTheory.T.exists_rational_tatePairing_bilinear hT l P K LL O hO A A' m hm
  have hflip : IsDual1 (P.PD K) A'.ρ A.ρ m.flip :=
    ⟨fun g x y => hm.1 g y x, hm.2.2.1, hm.2.1, hm.2.2.2.symm⟩
  have hanti := GlobalTheory.T.cup_one_cocycles_anticomm_up_to_coboundary l P K LL O hO A A' m hm
  refine ⟨β, hβ, fun a => ⟨fun h => ?_, fun ha b => ?_⟩, fun b => ⟨fun h => ?_, fun hb a => ?_⟩⟩
  · refine GlobalTheory.T.cocycle_mem_coboundaries_of_tate_orthogonal hT l P K LL O hO A' A m.flip hflip a.1 a.2 (fun b hb => ?_)
    exact ((hanti a.1 a.2 b hb).1).1 ((hβ a ⟨b, hb⟩).1 (h ⟨b, hb⟩))
  · exact (hβ a b).2 ((hanti a.1 a.2 b.1 b.2).2 (Or.inl ha))
  · exact GlobalTheory.T.cocycle_mem_coboundaries_of_tate_orthogonal hT l P K LL O hO A A' m hm b.1 b.2
      (fun a ha => (hβ ⟨a, ha⟩ b).1 (h ⟨a, ha⟩))
  · exact (hβ a b).2 ((hanti a.1 a.2 b.1 b.2).2 (Or.inr hb))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateFinitenessAllOfLocalTateDualityStatement
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateFinitenessAll_of_localTateDuality : Formalism.GaloisCohomology.LocalTateDualityK → ∀ D : D7, Formalism.MainNotions.N.K.Rows.FinAll D := by
  first | exact @GlobalTheory.finAll_of_localTateDuality | exact GlobalTheory.finAll_of_localTateDuality | (intros; apply GlobalTheory.finAll_of_localTateDuality <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaAinfPeriodPowNeZero
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.ThetaPer

theorem thetaD_aDp_pow_ne_zero : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ →
    ∀ (n : ℕ), ((Per.θD l).comp (aDp l)) (τ ^ n) ≠ 0 := by
  intro l _ K bk τ hτ n
  obtain ⟨-, ε, η, hε, hφ⟩ := hτ
  have hinj : Function.Injective (WittVector.frobenius : Ainf l → Ainf l) := by
    intro x y h
    rw [WittVector.frobenius_eq_map_frobenius] at h
    exact WittVector.map_injective _ (frobeniusEquiv (OCb l) l).injective h
  have hpi : WittVector.frobenius (GlobalTheory.MemLoc.TiedUnif.piOne ε) = WittVector.teichmuller l ε - 1 := by
    rw [GlobalTheory.MemLoc.TiedUnif.piOne, map_sub, map_one, WittVector.frobenius_eq_map_frobenius]
    change WittVector.map (frobenius (OCb l) l) (WittVector.teichmuller l ((frobeniusEquiv (OCb l) l).symm ε)) - 1 = _
    rw [WittVector.map_teichmuller, frobenius_apply_frobeniusEquiv_symm]
  have hsurj : Function.Surjective (WittVector.frobenius : Ainf l → Ainf l) := by
    intro y
    obtain ⟨x, hx⟩ := WittVector.map_surjective _ (frobeniusEquiv (OCb l) l).surjective y
    exact ⟨x, by rw [WittVector.frobenius_eq_map_frobenius]; exact hx⟩
  obtain ⟨η₀, hη₀⟩ := hsurj (η : Ainf l)
  obtain ⟨η₁, hη₁⟩ := hsurj ((η⁻¹ : (Ainf l)ˣ) : Ainf l)
  have hu : η₀ * η₁ = 1 := hinj (by rw [map_mul, map_one, hη₀, hη₁, Units.mul_inv])
  have hτe : τ = η₀ * GlobalTheory.MemLoc.TiedUnif.piOne ε := hinj (by rw [hφ, map_mul, hη₀, hpi])
  set f := (Per.θD l).comp (aDp l)
  have hf0 : f η₀ ≠ 0 := by
    intro h
    have := congrArg f hu
    rw [map_mul, h, zero_mul, map_one] at this
    exact zero_ne_one this
  have hf1 : f (GlobalTheory.MemLoc.TiedUnif.piOne ε) ≠ 0 := GlobalTheory.MemLoc.TiedUnif.theta_piOne hε
  rw [map_pow, hτe, map_mul]
  exact pow_ne_zero _ (mul_ne_zero hf0 hf1)

end GlobalTheory.ThetaPer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TopologicalBasisBasicFactsStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topologicalBasis_basic_facts : ∀ (S A : Type) [CommRing S] [CommRing A] (s : S →+* A) (I : Ideal S) (ι : Type) (TB : TopBasis s I ι), IsHausdorff I S → (∀ x, (∀ i, TB.c i x = 0) → x = 0) ∧ Function.Injective s ∧ (∀ (L : Ideal S) (n : ℕ), I ^ n ≤ L → ∀ x, x ∈ L.map s ↔ ∀ i, TB.c i x ∈ L) ∧ (∀ z : ι → S, (∀ n : ℕ, {i | z i ∉ I ^ n}.Finite) → ∃ x, ∀ i, TB.c i x = z i) ∧ ∀ a ∈ nonZeroDivisors S, s a ∈ nonZeroDivisors A := by
  first | exact @GlobalTheory.BSP.TopBasis.basic_facts | exact GlobalTheory.BSP.TopBasis.basic_facts | (intros; apply GlobalTheory.BSP.TopBasis.basic_facts <;> assumption)
end

