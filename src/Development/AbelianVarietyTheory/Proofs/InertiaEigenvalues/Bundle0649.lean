import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.NHkRow
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0564
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0268
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0637
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoboundaryMemBlochKatoCocycles
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankH1fDeRham
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0642
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0502
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0503
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0640
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0641
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0534
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictJumps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0645
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachInclusionXQFrobenius

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodProjectorFormsIdempotent
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms NumberField Polynomial Formalism.IndefR.NX
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.GoodSS.Idem

def rhoTw {D : D7} (S : RatDat D.ntw) (j : ℕ) : G0g D.nd →* Module.End D.what₂.LL (S.WL j) where
  toFun g := ((((S.A j).chi (S.eG.symm g))⁻¹ : D.what₂.LLˣ) : D.what₂.LL) • (S.A j).ρ (S.eG.symm g)
  map_one' := by simp
  map_mul' x y := by
    simp only [map_mul, mul_inv, Units.val_mul]
    rw [smul_mul_smul_comm]

theorem goodProjW_idem : ∀ (D : D7) (S : RatDat D.ntw) (j : ℕ), D.ntw.Tw →
    goodProjW S j D.nexp.eLL0 * goodProjW S j D.nexp.eLL0 = goodProjW S j D.nexp.eLL0 := by
  intro D S j i
  set s := (D.nexp.eAlg i true).coeff.support with hs
  have hsupp : ∀ g, g ∉ s → D.nexp.eLL0 g = 0 := fun g hg => by
    have h0 : (D.nexp.eAlg i true).coeff g = 0 := Finsupp.notMem_support_iff.1 hg
    have hcoef : (D.nexp.eAlg i true).coeff g = readLL0 S i true (D.nexp.eLL0 g) := by
      rw [D.nexp.eAlg_def]; rfl
    rw [hcoef] at h0
    exact (map_eq_zero_iff _ (readLL0 S i true).injective).1 h0
  let rd : ↥D.LL0 →+* FractionRing (D.ntw.O i) := readLL0 S i true
  have hrd : Function.Injective rd := (readLL0 S i true).injective
  let eL : MonoidAlgebra ↥D.LL0 (G0g D.nd) :=
    MonoidAlgebra.ofCoeff (Finsupp.onFinset s D.nexp.eLL0 fun g hg => by
      by_contra h
      exact hg (hsupp g h))
  have heL : ∀ g, eL.coeff g = D.nexp.eLL0 g := fun g => by
    simp only [eL, MonoidAlgebra.coeff_ofCoeff, Finsupp.onFinset_apply]
  have hmap : MonoidAlgebra.mapRingHom (G0g D.nd) rd eL = D.nexp.eAlg i true := by
    apply MonoidAlgebra.ext
    apply Finsupp.ext
    intro g
    rw [MonoidAlgebra.coeff_mapRingHom, heL, D.nexp.eAlg_def]
    rfl
  have hinj : Function.Injective (MonoidAlgebra.mapRingHom (G0g D.nd) rd) := by
    intro x y hxy
    apply MonoidAlgebra.ext
    apply Finsupp.ext
    intro g
    apply hrd
    rw [← MonoidAlgebra.coeff_mapRingHom, ← MonoidAlgebra.coeff_mapRingHom, hxy]
  have hidem : eL * eL = eL := hinj (by rw [map_mul, hmap, D.nexp.eAlg_idem])
  let eLL := MonoidAlgebra.mapRingHom (G0g D.nd) (algebraMap ↥D.LL0 D.what₂.LL) eL
  have hP : goodProjW S j D.nexp.eLL0 =
      MonoidAlgebra.lift D.what₂.LL (Module.End D.what₂.LL (S.WL j)) (G0g D.nd) (rhoTw S j) eLL := by
    rw [MonoidAlgebra.lift_apply]
    unfold goodProjW
    rw [finsum_eq_sum_of_support_subset _ (s := s) fun g hg => by
      by_contra hgs
      exact hg (by simp only [hsupp g hgs, IntermediateField.coe_zero, zero_mul, zero_smul])]
    rw [Finsupp.sum_of_support_subset _ (s := s) (fun g hg => by
      by_contra hgs
      apply Finsupp.mem_support_iff.1 hg
      simp only [eLL, MonoidAlgebra.coeff_mapRingHom, heL, hsupp g hgs, map_zero]) (fun a b => b • rhoTw S j a) (fun _ _ => zero_smul _ _)]
    refine Finset.sum_congr rfl fun g _ => ?_
    simp only [eLL, MonoidAlgebra.coeff_mapRingHom, heL, rhoTw, MonoidHom.coe_mk, OneHom.coe_mk, mul_smul,
      Units.val_inv_eq_inv_val]
    rfl
  rw [hP, ← map_mul, ← map_mul, hidem]

end GlobalTheory.GoodSS.Idem
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GreenCuspidalCharsByRegularCharsProof
section
noncomputable section

open GlobalTheory.GLq GlobalTheory.Published Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GreenRegularCharactersInertiaEigenvalues

variable {g : ℕ} [Fact g.Prime]

theorem isPrimeLab_pos {e : ℕ} {P : (ZMod g)[X]} (h : IsPrimeLab e P) : 0 < e := by
  have := degree_pos_of_irreducible h.2.1
  rw [← h.2.2.2]
  exact natDegree_pos_iff_degree_pos.mpr this

theorem family (g : ℕ) [Fact g.Prime] (e : ℕ) (he : 0 < e) (K : Type) [Field K] [Algebra (ZMod g) K]
    (hK : Module.finrank (ZMod g) K = e) (τ : (Kˣ →* ℂˣ) → Gn g e → ℂ)
    (h1 : ∀ θ, IsRegularChar g e θ → IsCusp (τ θ))
    (h2 : ∀ θ θ', IsRegularChar g e θ → IsRegularChar g e θ' → (τ θ = τ θ' ↔ ∃ i < e, θ' = θ ^ g ^ i)) :
    ∃ L : (ZMod g)[X] → Gn g e → ℂ,
      (∀ P, IsPrimeLab e P → IsCusp (L P) ∧ ∃ θ, IsRegularChar g e θ ∧ L P = τ θ) ∧
      ∀ P P', IsPrimeLab e P → IsPrimeLab e P' → L P = L P' → P = P' := by
  obtain ⟨c, hc1, hc2⟩ := GlobalTheory.T.monicIrreducible_inject_regularCharacterOrbits g e he K hK
  refine ⟨fun P => τ (c P), fun P hP => ⟨h1 _ (hc1 P hP), c P, hc1 P hP, rfl⟩, ?_⟩
  intro P P' hP hP' h
  exact hc2 P P' hP hP' ((h2 _ _ (hc1 P hP) (hc1 P' hP')).mp h)

theorem factor_lab {f : (ZMod g)[X]} (h0 : f.coeff 0 ≠ 0) :
    ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors f, IsPrimeLab P.natDegree P := by
  intro P hP
  have hirr := UniqueFactorizationMonoid.irreducible_of_normalized_factor P hP
  have hmon : P.Monic := by
    rw [← UniqueFactorizationMonoid.normalize_normalized_factor P hP]
    exact monic_normalize hirr.ne_zero
  refine ⟨hmon, hirr, ?_, rfl⟩
  intro hc
  have : (X : (ZMod g)[X]) ∣ f :=
    (X_dvd_iff.mpr hc).trans (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP)
  exact h0 (X_dvd_iff.mp this)

theorem prod_factors {f : (ZMod g)[X]} (hf : f.Monic) (h0 : f.coeff 0 ≠ 0) :
    (UniqueFactorizationMonoid.normalizedFactors f).prod = f := by
  have hm : ((UniqueFactorizationMonoid.normalizedFactors f).prod).Monic := by
    have := monic_multiset_prod_of_monic (UniqueFactorizationMonoid.normalizedFactors f) id
      (fun P hP => (factor_lab h0 P hP).1)
    simpa using this
  exact eq_of_monic_of_associated hm hf (UniqueFactorizationMonoid.prod_normalizedFactors hf.ne_zero)

theorem count (d : ℕ) (hd : 0 < d) (Lf : ∀ e, (ZMod g)[X] → Gn g e → ℂ)
    (hc : ∀ e P, IsPrimeLab e P → IsCusp (Lf e P))
    (hi : ∀ e P P', IsPrimeLab e P → IsPrimeLab e P' → Lf e P = Lf e P' → P = P')
    (χ : Gn g d → ℂ) (hχ : IsCusp χ) (hne : ∀ P, IsPrimeLab d P → Lf d P ≠ χ) : False := by
  let s : Set (ZMod g)[X] := {P | IsPrimeLab P.natDegree P}
  let φ : (ZMod g)[X] → Pc g := fun P => ⟨P.natDegree, Lf P.natDegree P⟩
  have hinj : Set.InjOn φ s := by
    intro P hP P' hP' h
    have h1 : P.natDegree = P'.natDegree := congrArg Sigma.fst h
    have h2 : (⟨P'.natDegree, Lf P'.natDegree P'⟩ : Pc g) = ⟨P.natDegree, Lf P.natDegree P'⟩ := by rw [h1]
    have h3 : Lf P.natDegree P = Lf P.natDegree P' := sigma_mk_injective (h.trans h2)
    have hP'' : IsPrimeLab P.natDegree P' := by rw [h1]; exact hP'
    exact hi _ P P' hP hP'' h3
  let ψ : Pc g → (ZMod g)[X] := Function.invFunOn φ s
  have hleft : ∀ P ∈ s, ψ (φ P) = P := fun P hP => hinj.leftInvOn_invFunOn hP
  let T : Set (ZMod g)[X] := {f | f.Monic ∧ f.natDegree = d ∧ f.coeff 0 ≠ 0}
  obtain ⟨hcard, hfin⟩ := GlobalTheory.T.ncard_monic_natDegree_coeff_zero_ne_zero g d hd
  let F : (ZMod g)[X] → Multiset (Pc g) := fun f => (UniqueFactorizationMonoid.normalizedFactors f).map φ
  have hback : ∀ f ∈ T, (F f).map ψ = UniqueFactorizationMonoid.normalizedFactors f := by
    intro f hf
    simp only [F, Multiset.map_map]
    conv_rhs => rw [← Multiset.map_id (UniqueFactorizationMonoid.normalizedFactors f)]
    exact Multiset.map_congr rfl (fun P hP => hleft P (factor_lab hf.2.2 P hP))
  have hFinj : Set.InjOn F T := by
    intro f hf f' hf' h
    have := congrArg (fun M => (M.map ψ).prod) h
    simp only [hback f hf, hback f' hf'] at this
    rwa [prod_factors hf.1 hf.2.2, prod_factors hf'.1 hf'.2.2] at this
  have hnot : ({⟨d, χ⟩} : Multiset (Pc g)) ∉ hfin.toFinset.image F := by
    intro hmem
    obtain ⟨f, hf, hfe⟩ := Finset.mem_image.mp hmem
    rw [Set.Finite.mem_toFinset] at hf
    have hnf := hback f hf
    rw [hfe, Multiset.map_singleton] at hnf
    have hPmem : ψ ⟨d, χ⟩ ∈ UniqueFactorizationMonoid.normalizedFactors f := by
      rw [← hnf]; exact Multiset.mem_singleton_self _
    have hPl := factor_lab hf.2.2 _ hPmem
    have hφ : φ (ψ ⟨d, χ⟩) = ⟨d, χ⟩ := by
      have := hfe
      simp only [F] at this
      rw [← hnf, Multiset.map_singleton, Multiset.singleton_inj] at this
      exact this
    set P := ψ ⟨d, χ⟩ with hPdef
    have hdeg : P.natDegree = d := congrArg Sigma.fst hφ
    have h2 : (⟨d, Lf d P⟩ : Pc g) = ⟨P.natDegree, Lf P.natDegree P⟩ := by rw [hdeg]
    have h3 : Lf d P = χ := sigma_mk_injective (h2.trans hφ)
    have hPl' : IsPrimeLab d P := by rw [← hdeg]; exact hPl
    exact hne P hPl' h3
  let S : Finset (Multiset (Pc g)) := insert {⟨d, χ⟩} (hfin.toFinset.image F)
  have hS : ∀ M ∈ S, (M.map fun p => p.1).sum = d ∧ ∀ p ∈ M, IsCusp p.2 := by
    intro M hM
    rcases Finset.mem_insert.mp hM with rfl | hM
    · refine ⟨by simp, ?_⟩
      intro p hp
      rw [Multiset.mem_singleton] at hp
      subst hp
      exact hχ
    · obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hM
      rw [Set.Finite.mem_toFinset] at hf
      refine ⟨?_, ?_⟩
      · simp only [F, Multiset.map_map]
        have hdeg := natDegree_multiset_prod_of_monic (UniqueFactorizationMonoid.normalizedFactors f)
          (fun P hP => (factor_lab hf.2.2 P hP).1)
        rw [prod_factors hf.1 hf.2.2, hf.2.1] at hdeg
        rw [hdeg]
        rfl
      · intro p hp
        obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.mp hp
        exact hc _ P (factor_lab hf.2.2 P hP)
  have hle := GlobalTheory.T.card_cuspidal_multisets_total_degree_le g d hd S hS
  have hcardS : S.card = g ^ d - g ^ (d - 1) + 1 := by
    rw [Finset.card_insert_of_notMem hnot, Finset.card_image_of_injOn, ← hcard,
      Set.ncard_eq_toFinset_card T hfin]
    rw [Set.Finite.coe_toFinset]
    exact hFinj
  omega

end GlobalTheory.GreenRegularCharactersInertiaEigenvalues

open GlobalTheory.GreenRegularCharactersInertiaEigenvalues in

theorem GlobalTheory.greenRegularCharacters_holds : GreenRegularCharacters := by
  intro g _ d hd K _ _ hK
  obtain ⟨τ, hτ1, hτ2⟩ := GlobalTheory.T.exists_cuspidalCharacter_of_regularCharacter_GLn g d hd K hK
  refine ⟨τ, hτ1, hτ2, ?_⟩
  have hex : ∀ e, ∃ L : (ZMod g)[X] → Gn g e → ℂ,
      (∀ P, IsPrimeLab e P → IsCusp (L P)) ∧
      (∀ P P', IsPrimeLab e P → IsPrimeLab e P' → L P = L P' → P = P') ∧
      (∀ _ : e = d, ∀ P, IsPrimeLab e P → ∃ θ, IsRegularChar g d θ ∧ (⟨e, L P⟩ : Pc g) = ⟨d, τ θ⟩) := by
    intro e
    by_cases hed : e = d
    · subst hed
      obtain ⟨L, hL1, hL2⟩ := family g e hd K hK τ (fun θ hθ => (hτ1 θ hθ).1) hτ2
      refine ⟨L, fun P hP => (hL1 P hP).1, hL2, fun _ P hP => ?_⟩
      obtain ⟨θ, hθ, he⟩ := (hL1 P hP).2
      exact ⟨θ, hθ, by rw [he]⟩
    · by_cases he0 : e = 0
      · refine ⟨fun _ _ => 0, fun P hP => absurd (isPrimeLab_pos hP) (by omega),
          fun P _ hP _ _ => absurd (isPrimeLab_pos hP) (by omega), fun h => absurd h hed⟩
      · have hpos : 0 < e := Nat.pos_of_ne_zero he0
        obtain ⟨τ', hτ'1, hτ'2⟩ := GlobalTheory.T.exists_cuspidalCharacter_of_regularCharacter_GLn g e hpos (GaloisField g e) (GaloisField.finrank g he0)
        obtain ⟨L, hL1, hL2⟩ := family g e hpos (GaloisField g e) (GaloisField.finrank g he0) τ'
          (fun θ hθ => (hτ'1 θ hθ).1) hτ'2
        exact ⟨L, fun P hP => (hL1 P hP).1, hL2, fun h => absurd h hed⟩
  choose Lf hc hi hdd using hex
  intro χ hχ
  by_contra hno
  push_neg at hno
  refine count d hd Lf hc hi χ hχ ?_
  intro P hP heq
  obtain ⟨θ, hθ, hs⟩ := hdd d rfl P hP
  have : Lf d P = τ θ := sigma_mk_injective hs
  exact hno θ hθ (heq ▸ this)

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1fTSpanCardBound
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.H1fGeneratorsAlt

section Eval

variable {G V LL : Type} [Field LL] [AddCommGroup V] [Module LL V]

theorem exists_finset_eval (W : Submodule LL (G → V)) [Module.Finite LL ↥W] :
    ∃ s : Finset G, ∀ c ∈ W, (∀ g ∈ s, c g = 0) → c = 0 := by
  classical
  let Ks : Finset G → Submodule LL (G → V) := fun s =>
    W ⊓ ⨅ g ∈ s, LinearMap.ker (LinearMap.proj (R := LL) (φ := fun _ : G => V) g)
  have hmem : ∀ s c, c ∈ Ks s ↔ c ∈ W ∧ ∀ g ∈ s, c g = 0 := by
    intro s c
    simp [Ks, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker]
  obtain ⟨s, -, hs⟩ := (measure fun s => finrank LL ↥(Ks s)).wf.has_min Set.univ ⟨∅, trivial⟩
  refine ⟨s, fun c hc h0 => ?_⟩
  by_contra hne
  obtain ⟨g, hg⟩ : ∃ g, c g ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  have hlt : Ks (insert g s) < Ks s := by
    refine lt_of_le_of_ne (fun x hx => ?_) fun heq => ?_
    · rw [hmem] at hx ⊢
      exact ⟨hx.1, fun g' hg' => hx.2 g' (Finset.mem_insert_of_mem hg')⟩
    · have h1 : c ∈ Ks s := (hmem s c).2 ⟨hc, h0⟩
      rw [← heq, hmem] at h1
      exact hg (h1.2 g (Finset.mem_insert_self g s))
  haveI : Module.Finite LL ↥(Ks s) := Submodule.finiteDimensional_of_le inf_le_left
  exact hs (insert g s) trivial (Submodule.finrank_lt_finrank_of_lt hlt)

theorem fg_of_le_of_values {O : Type} [CommRing O] [IsNoetherianRing O] [Algebra O LL] [Module O V]
    [IsScalarTower O LL V] (W : Submodule LL (G → V)) [Module.Finite LL ↥W]
    (T : Submodule O V) (hT : T.FG) (N : Submodule O (G → V)) (hNW : N ≤ W.restrictScalars O)
    (hNT : ∀ c ∈ N, ∀ g, c g ∈ T) : N.FG := by
  classical
  obtain ⟨s, hs⟩ := exists_finset_eval W
  haveI : IsNoetherian O ↥T := isNoetherian_of_fg_of_noetherian T hT
  let φ : ↥N →ₗ[O] (↥s → ↥T) :=
    { toFun := fun c i => ⟨(c : G → V) i, hNT _ c.2 _⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hφ : Function.Injective φ := by
    intro c c' h
    apply Subtype.ext
    rw [← sub_eq_zero]
    refine hs _ (W.sub_mem (hNW c.2) (hNW c'.2)) fun g hg => ?_
    have := congrArg (fun f => ((f ⟨g, hg⟩ : ↥T) : V)) h
    simpa [φ, sub_eq_zero] using this
  haveI : IsNoetherian O ↥N := isNoetherian_of_injective φ hφ
  exact Module.Finite.iff_fg.1 inferInstance

end Eval

section Cohomology

open GlobalTheory.H1fGeneratorBoundAlt GlobalTheory.IndefiniteRowSideFullHecke.GaloisLatticeModuleActions

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {ρ : Representation LL G V}
    [TopologicalSpace G] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul LL V]
    {O : Type} [CommRing O] [Algebra O LL] [IsDomain O] [IsDiscreteValuationRing O]
    [IsFractionRing O LL] [Module O V] [IsScalarTower O LL V]

theorem finite_Z1f_of_H1fV [FiniteDimensional LL V] (hρ : ∀ x, Continuous fun g => ρ g x)
    [Module.Finite LL (FiniteCohomology PD ρ)] : Module.Finite LL ↥(finiteCocycles PD ρ) := by
  have hle : B1 ρ ≤ finiteCocycles PD ρ := by
    rintro _ ⟨x, rfl⟩
    exact coboundary_mem_blochKatoCocycles PD hρ x
  haveI : Module.Finite LL ↥(B1 ρ) := LinearMap.finiteDimensional_range _
  haveI : Module.Finite LL ↥((B1 ρ).comap (finiteCocycles PD ρ).subtype) :=
    Module.Finite.equiv (Submodule.comapSubtypeEquivOfLe hle).symm
  haveI : IsNoetherian LL ↥(finiteCocycles PD ρ) :=
    isNoetherian_of_range_eq_ker ((B1 ρ).comap (finiteCocycles PD ρ).subtype).subtype
      (Submodule.mkQ _) (by rw [Submodule.range_subtype, Submodule.ker_mkQ])
  infer_instance

theorem finite_Z1fT_of (L : Lattice (O := O) ρ) [Module.Finite LL ↥(finiteCocycles PD ρ)] :
    Module.Finite O ↥(latticeFiniteCocycles PD L) :=
  Module.Finite.iff_fg.2 (fg_of_le_of_values (finiteCocycles PD ρ) L.T L.fg (latticeFiniteCocycles PD L) inf_le_right
    fun _ hc g => hc.1.2 g (Set.mem_univ g))

theorem exists_generators_H1fT' [FiniteDimensional LL V] (L : Lattice (O := O) ρ)
    (hρ : ∀ x, Continuous fun g => ρ g x) [Module.Finite LL (FiniteCohomology PD ρ)]
    {ϖ : O} (hϖ : Irreducible ϖ) :
    ∃ m : ℕ, GeneratedByAtMost (latticeFiniteCohomology PD L) m ∧
      m + finrank LL ↥(H0V ρ) ≤ finrank LL (FiniteCohomology PD ρ) + h0ModResidueDim L ϖ := by
  classical
  haveI hI : (Ideal.span {ϖ}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hϖ
  letI : Field (O ⧸ Ideal.span {ϖ}) := Ideal.Quotient.field _
  haveI := L.free
  haveI : Module.Finite O ↥L.T := Module.Finite.iff_fg.2 L.fg
  haveI := finite_Z1f_of_H1fV PD hρ
  haveI := finite_Z1fT_of PD L
  haveI : Module.IsTorsionFree O LL := inferInstance
  haveI : Module.IsTorsionFree O V := Module.IsTorsionFree.trans LL
  haveI : Module.Free O ↥(latticeFiniteCocycles PD L) := inferInstance
  obtain ⟨m, z, hz, hm⟩ := exists_generators (Ideal.span {ϖ}) (cobT PD L hρ)
  refine ⟨m, ⟨Finset.univ.image fun i => classT PD L (z i), ?_, ?_⟩, ?_⟩
  · have := congrArg (Submodule.map (classT PD L)) hz
    rw [Submodule.map_sup, ← ker_classT, Submodule.map_top, range_classT,
      (Submodule.map_le_iff_le_comap.2 le_rfl : (LinearMap.ker (classT PD L)).map (classT PD L) ≤ ⊥).antisymm bot_le,
      sup_bot_eq, Submodule.map_span, ← Set.range_comp] at this
    rw [← this, Finset.coe_image, Finset.coe_univ, Set.image_univ]
    rfl
  · simpa using Finset.card_image_le (s := Finset.univ) (f := fun i => classT PD L (z i))
  · haveI := finite_latMod L (Ideal.span {ϖ})
    have h1 := Submodule.finrank_mono (ker_redMap_le PD L hρ (Ideal.span {ϖ}))
    have h2 := finrank_bloch_kato_cocycles PD hρ
    have h3 := finrank_lattice L
    have h4 : finrank O ↥(latticeFiniteCocycles PD L) ≤ finrank LL ↥(finiteCocycles PD ρ) :=
      finrank_le_of_injective (W := ↥(finiteCocycles PD ρ))
        { toFun := fun c => ⟨c, c.2.2⟩
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl } fun _ _ h =>
          Subtype.ext (congrArg (fun c : ↥(finiteCocycles PD ρ) => (c : G → V)) h)
    have h5 : finrank (O ⧸ Ideal.span {ϖ}) ↥(LinearMap.ker (redMap (Ideal.span {ϖ}) (cobT PD L hρ))) ≤
      h0ModResidueDim L ϖ := h1
    omega

end Cohomology

open GlobalTheory.H1fGeneratorBoundAlt GlobalTheory.IndefiniteRowSideFullHecke.GaloisLatticeModuleActions

theorem h1fT_generators : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ T : LocLat ↥(GK K) ℚ_[l] LL O, IsDR (P.PD K) T.ρ → ∃ s : Finset (LatticeCohomology T.L), Submodule.span O (s : Set (LatticeCohomology T.L)) = latticeFiniteCohomology (P.PD K) T.L ∧ s.card + finrank LL ↥(H0V T.ρ) ≤ finrank LL (FiniteCohomology (P.PD K) T.ρ) + finrank LL T.V := by
  intro l _ P AI hTied K LL _ _ _ O _ _ hO T hDR
  have hH1f := (GlobalTheory.SeqDim.h1f_finrank l P AI hTied K LL O hO (toGRep T) hDR).1
  obtain ⟨⟨hD, hDVR, hF⟩, -⟩ := hO
  haveI : IsTopologicalAddGroup T.V := IsModuleTopology.topologicalAddGroup LL T.V
  haveI : Module.Finite LL (FiniteCohomology (P.PD K) T.ρ) := hH1f
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨m, ⟨s, hs, hc⟩, hm⟩ := exists_generators_H1fT' (P.PD K) T.L T.cont hϖ
  have h5 := h0_mod_uniformizer_le_rank T.L hϖ
  have h3 := finrank_lattice T.L
  exact ⟨s, hs, by omega⟩

end GlobalTheory.H1fGeneratorsAlt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesWeightLeSquarefreeStatement
section
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harishChandraSeriesWeight_le_squarefree : ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g), 5 ≤ g → Green → ∀ (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ (N k s : ℕ), N = k + 2 * s + 1 → 1 ≤ k → ∀ f : (ZMod g)[X], f.Monic → f.natDegree = N → f.coeff 0 ≠ 0 → Squarefree f → wtC L (eJ g N k s ψ) f ≤ (1 + 1 / (g : ℝ)) ^ N * wtC L (eU g N ψ) f := by
  first | exact @GlobalTheory.GLq.UpperWeight.wtC_eJ_le | exact GlobalTheory.GLq.UpperWeight.wtC_eJ_le | (intros; apply GlobalTheory.GLq.UpperWeight.wtC_eJ_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralConnectionTaylorFormulaTameBreuilKisin
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.IntConnTaylor

theorem main : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T), IsBK (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) → ∃ C : Conn P, C.nabla = P.nabla ∧ Ident.Taylor (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) C := by
  intro hBS l _ a e _ _ ϖ LL _ _ hl2 ι _ _ P T I hBK
  obtain ⟨sh, φ₂, h1, h2, h3⟩ := GlobalTheory.T.exists_taylorShift_frobenius_twoVariable_compatible l (↥LL.1)
  obtain ⟨ε, hε0, hεφ, hεS⟩ := GlobalTheory.T.exists_integral_crystal_stratification_matrix hBS l a e ϖ LL hl2 ι P T I hBK sh φ₂ h1 h2 h3
  have hc := GlobalTheory.T.frobeniusStratification_coeff_eq_connection_pow (↥(OL LL)) (↥LL.1) l e a ι P sh φ₂ h1 h2 h3 ε hε0 hεφ
  have hphi : ∀ j, P.phi (bas j) ∈ P.MM := fun j =>
    P.ext_mono (fun _ h => A_le_S l e h) (P.phi_mem_L (P.bas_mem_M j))
  have hpow : ∀ (n : ℕ) (j : ι), (P.nabla ^ n) (P.phi (bas j)) ∈ P.MM := fun n j =>
    mem_tot.2 fun τ => P.mem_extc_iff.2 fun i => by rw [← hc τ n i j]; exact hεS τ i j n
  have hMM : ∀ m ∈ P.MM, P.nabla m ∈ P.MM := fun m hm =>
    P.nabla_mem_MM_of_basis (fun j => by simpa using hpow 1 j) hphi hm
  let C : Conn P := ⟨P.nabla, fun f v => P.nabla_smul_tot f v, hMM⟩
  have hS : ∀ (τ : ZMod a) (j : ι) (k : ℕ) (i : ι), (X : (↥LL.1)⟦X⟧) ^ k *
      (P.mxInv τ *ᵥ (P.nabla ^ k) (P.phi (bas j)) τ) i ∈ S (↥(OL LL)) (↥LL.1) e := fun τ j k i =>
    mul_mem (pow_mem (uIn (S (↥(OL LL)) (↥LL.1) e)).2 k)
      (P.mem_extc_iff.1 (mem_tot.1 (hpow k j) τ) i)
  exact ⟨C, rfl, GlobalTheory.T.galois_taylor_formula_breuilKisin_lattice l a e ϖ LL hl2 ι P _ _ C hS (GlobalTheory.T.galois_dividedTaylor_expansion_frobeniusBasis hBS l a e ϖ LL hl2 ι P T I hBK hS)⟩

end GlobalTheory.IntConnTaylor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvQPowNygaardExtComesFromBaseField
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.NL.CrystallineBase

noncomputable section

namespace GlobalTheory.NL.TransitionThirdCase

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem jD_Qpow (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime]
    (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (T : Lt K LL) (m : ℕ)
    (x : ((HW l).W K s LL h).DD T) :
    ((F l).E K s LL h).tie.jD T (((HW l).W K s LL h).Q ^ m • x) =
      (inclR LL ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (D.locA l).ξ)) ^ m • ((F l).E K s LL h).tie.jD T x := by
  have hQ := (GlobalTheory.NL.IoXQ.main D HW F l K s LL h).2.1
  rw [← algebraMap_smul ((HW l).W K s LL h).EE (((HW l).W K s LL h).Q ^ m) x,
    ((F l).E K s LL h).tie.jD_smul, ((F l).E K s LL h).tie.ioE_ext, map_pow, hQ, map_pow]

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem main : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (K' : FinExt l) (h' : Good K' s LL) (hle : K.1 ≤ K'.1), K0 K' = K0 K → ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (m : ℕ) (y' : ((HW l).W K' s LL h').DD (resLt (K := K) (K' := K') (LL := LL) hle T)), y' ∈ invN ((HW l).W K' s LL h') (resLt (K := K) (K' := K') (LL := LL) hle T) (((HW l).W K' s LL h').Q ^ m) → ∃ y ∈ invN ((HW l).W K s LL h) T (((HW l).W K s LL h).Q ^ m), ((F l).E K s LL h).tie.jD T y = toTW hle T (((F l).E K' s LL h').tie.jD (resLt (K := K) (K' := K') (LL := LL) hle T) y') := by
  intro D HW F l _ K s LL h K' h' hle hK0 T hT m y' hy'
  have hB := GlobalTheory.NL.BaseField.base_indep D HW F l K s LL h K' h' hle hK0
  have hB3 := hB.2.2 T (resLt (K := K) (K' := K') (LL := LL) hle T) (LinearEquiv.refl (↥(OL LL)) ↥T.L.T)
    (fun g t => rfl)
  have hid : (TensorProduct.map (LinearMap.id : RW LL →ₗ[↥(OL LL)] RW LL)
      (LinearEquiv.refl (↥(OL LL)) ↥T.L.T).toLinearMap) = LinearMap.id := TensorProduct.map_id
  have hR := hB3.1
  have hN := hB3.2 hT (restrict_crys D hle T hT)
  have hy1 : TensorProduct.map (LinearMap.id : RW LL →ₗ[↥(OL LL)] RW LL)
      (LinearEquiv.refl (↥(OL LL)) ↥T.L.T).toLinearMap
      (((F l).E K' s LL h').tie.jD (resLt (K := K) (K' := K') (LL := LL) hle T) y') ∈
      Set.range (((F l).E K s LL h).tie.jD T) := hR ▸ ⟨_, ⟨y', rfl⟩, rfl⟩
  have hy2 : TensorProduct.map (LinearMap.id : RW LL →ₗ[↥(OL LL)] RW LL)
      (LinearEquiv.refl (↥(OL LL)) ↥T.L.T).toLinearMap
      (((F l).E K' s LL h').tie.jD (resLt (K := K) (K' := K') (LL := LL) hle T)
      (((HW l).W K' s LL h').Q ^ m • y')) ∈
      ((F l).E K s LL h).tie.jD T '' (((HW l).W K s LL h).N T : Set (((HW l).W K s LL h).DD T)) :=
    hN ▸ ⟨_, ⟨_, hy', rfl⟩, rfl⟩
  have hm1 := LinearMap.congr_fun hid (((F l).E K' s LL h').tie.jD (resLt (K := K) (K' := K') (LL := LL) hle T) y')
  have hm2 := LinearMap.congr_fun hid (((F l).E K' s LL h').tie.jD (resLt (K := K) (K' := K') (LL := LL) hle T)
      (((HW l).W K' s LL h').Q ^ m • y'))
  refine hy1.elim fun y hy => hy2.elim fun z hz => ⟨y, ?_, hy.trans hm1⟩
  show ((HW l).W K s LL h).Q ^ m • y ∈ ((HW l).W K s LL h).N T
  have e : z = ((HW l).W K s LL h).Q ^ m • y := by
    apply ((F l).E K s LL h).tie.jD_inj T
    rw [hz.2, hm2, jD_Qpow, jD_Qpow, hy, hm1]
    rfl
  exact e ▸ hz.1

end GlobalTheory.NL.TransitionThirdCase
end
end

