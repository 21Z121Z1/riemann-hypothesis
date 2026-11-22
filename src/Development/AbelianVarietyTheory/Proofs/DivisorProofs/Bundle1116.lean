import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsFiniteProjectiveComplexQuasiIso
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ProjectiveOfIsLocallyConstantFinrankFiber
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0951
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0347
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0018
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0402
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1065
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsMulCommutativeCentRealUJ
import Formalism.RealPlaceAnalysis.SmoothOnGVIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0145
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0437
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1077
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DcOpCommOfCommute
import Formalism.UnipotentAdelicQuotients.ThmBInHecke
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1078
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1040
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1026
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1035
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1024

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomologyVanishingSpecializes
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

set_option autoImplicit false

attribute [local instance] RingHom.ker_isPrime PrimeSpectrum.isPrime

noncomputable section

namespace GlobalTheory.FibreVanishGen

theorem primeCompl_ker_le {R : Type} [CommRing R] {κ : Type} [Field κ] (g : R →+* κ) :
    (RingHom.ker g).primeCompl ≤ Submonoid.comap g (IsUnit.submonoid κ) := by
  intro r hr
  rw [Submonoid.mem_comap, IsUnit.mem_submonoid_iff]
  exact isUnit_iff_ne_zero.2 fun h => (Ideal.mem_primeCompl_iff.1 hr) (RingHom.mem_ker.2 h)

def liftRes {R : Type} [CommRing R] {κ : Type} [Field κ] (g : R →+* κ) :
    (RingHom.ker g).ResidueField →+* κ :=
  Ideal.ResidueField.lift (RingHom.ker g) g le_rfl (primeCompl_ker_le g)

theorem liftRes_comp {R : Type} [CommRing R] {κ : Type} [Field κ] (g : R →+* κ) :
    (liftRes g).comp (algebraMap R (RingHom.ker g).ResidueField) = g :=
  RingHom.ext fun r => Ideal.ResidueField.lift_algebraMap _ _ le_rfl (primeCompl_ker_le g) r

theorem subsingleton_homology_iff {R : Type} [CommRing R] (K : CochainComplex (ModuleCat.{0} R) ℕ)
    {κ : Type} [Field κ] (g : R →+* κ) (q : ℕ) :
    Subsingleton ((((ModuleCat.extendScalars.{0, 0, 0} g).mapHomologicalComplex _).obj K).homology q) ↔
    Subsingleton ((((ModuleCat.extendScalars.{0, 0, 0}
      (algebraMap R (RingHom.ker g).ResidueField)).mapHomologicalComplex _).obj K).homology q) := by
  set L := (RingHom.ker g).ResidueField
  set a := algebraMap R L
  letI : Algebra L κ := (liftRes g).toAlgebra
  let K' := ((ModuleCat.extendScalars.{0, 0, 0} a).mapHomologicalComplex (ComplexShape.up ℕ)).obj K
  obtain ⟨e⟩ := FieldChangeInter.nonempty_homology_equiv (R := L) κ K' q
  have e₁ : ModuleCat.extendScalars.{0, 0, 0} g ≅
      ModuleCat.extendScalars.{0, 0, 0} a ⋙ ModuleCat.extendScalars.{0, 0, 0} (algebraMap L κ) :=
    eqToIso (congrArg _ (liftRes_comp g).symm) ≪≫ ModuleCat.extendScalarsComp a (liftRes g)
  have e₂ : ((ModuleCat.extendScalars.{0, 0, 0} g).mapHomologicalComplex (ComplexShape.up ℕ)).obj K ≅
      ((ModuleCat.extendScalars.{0, 0, 0} (algebraMap L κ)).mapHomologicalComplex _).obj K' :=
    (NatIso.mapHomologicalComplex e₁ _).app K ≪≫
      ((Functor.mapHomologicalComplexCompIso (Iso.refl _) _).symm.app K)
  have e₃ := ((HomologicalComplex.homologyFunctor _ _ q).mapIso e₂).toLinearEquiv
  refine Iff.trans (e₃.toEquiv.trans e.toEquiv).subsingleton_congr ?_
  constructor
  · intro h
    by_contra hV
    rw [not_subsingleton_iff_nontrivial] at hV
    exact not_nontrivial_iff_subsingleton.2 h (Module.FaithfullyFlat.lTensor_nontrivial L κ _)
  · intro h
    infer_instance

theorem main : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (C : CochainComplex (ModuleCat.{0} R) ℕ) (n : ℕ), (∀ p, n < p → IsZero (C.X p)) → (∀ p, Module.Flat R (C.X p)) → (∀ p, Module.Finite R (C.homology p)) → ∀ (κ₁ κ₂ : Type) [Field κ₁] [Field κ₂] (g₁ : R →+* κ₁) (g₂ : R →+* κ₂), RingHom.ker g₂ ≤ RingHom.ker g₁ → ∀ q : ℕ, Subsingleton ((((ModuleCat.extendScalars.{0, 0, 0} g₁).mapHomologicalComplex _).obj C).homology q) → Subsingleton ((((ModuleCat.extendScalars.{0, 0, 0} g₂).mapHomologicalComplex _).obj C).homology q) := by
  intro R _ _ C n hn hflat hfin κ₁ κ₂ _ _ g₁ g₂ hle q h1
  obtain ⟨K, φ, hKn, hKfin, -, hKproj, -, -, hext⟩ :=
    exists_finite_projective_complex_quasiIso C n hn hflat hfin
  have tr : ∀ (κ : Type) [Field κ] (g : R →+* κ),
      Subsingleton ((((ModuleCat.extendScalars.{0, 0, 0} g).mapHomologicalComplex _).obj C).homology q) ↔
      Subsingleton ((((ModuleCat.extendScalars.{0, 0, 0} g).mapHomologicalComplex _).obj K).homology q) := by
    intro κ _ g
    letI := g.toAlgebra
    haveI := hext κ
    exact (asIso (HomologicalComplex.homologyMap
      (((ModuleCat.extendScalars.{0, 0, 0} (algebraMap R κ)).mapHomologicalComplex _).map φ) q)
      ).toLinearEquiv.toEquiv.subsingleton_congr.symm
  haveI := hKfin
  haveI := hKproj
  obtain ⟨hfinH, hsc, -⟩ := semicontinuity_finite_projective_complex K n hKn
  let P₁ : PrimeSpectrum R := ⟨RingHom.ker g₁, RingHom.ker_isPrime g₁⟩
  let P₂ : PrimeSpectrum R := ⟨RingHom.ker g₂, RingHom.ker_isPrime g₂⟩
  have h1' := (subsingleton_homology_iff K g₁ q).1 ((tr κ₁ g₁).1 h1)
  have hP₁ : Module.finrank P₁.asIdeal.ResidueField ((((ModuleCat.extendScalars
      (algebraMap R P₁.asIdeal.ResidueField)).mapHomologicalComplex _).obj K).homology q) < 1 := by
    rw [Module.finrank_zero_of_subsingleton]
    exact zero_lt_one
  have hsp : P₂ ⤳ P₁ := (PrimeSpectrum.le_iff_specializes P₂ P₁).1 hle
  have hP₂ := ((hsc q P₁ 1 hP₁).filter_mono (specializes_iff_nhds.1 hsp)).self_of_nhds
  haveI := hfinH q P₂
  have h2' : Subsingleton ((((ModuleCat.extendScalars
      (algebraMap R P₂.asIdeal.ResidueField)).mapHomologicalComplex _).obj K).homology q) :=
    Module.finrank_zero_iff.1 (Nat.lt_one_iff.1 hP₂)
  exact (tr κ₂ g₂).2 ((subsingleton_homology_iff K g₂ q).2 h2')

end GlobalTheory.FibreVanishGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomotopyInvQuotIInfKerRetractions
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory

theorem homotopyInv_quot_iInf_ker_retractions : ∀ (q : ℕ) [NeZero q] (D T E : Type) [CommRing D] [IsDomain D] [CommRing T] [IsDomain T] [Algebra D T] [Algebra.IsIntegral D T] [CommRing E] [Algebra D E] [Algebra.IsIntegral D E], IsUnit (q : D) → HInv q T → (∀ (E' : Type) [CommRing E'] [Algebra D E'] [Algebra.IsIntegral D E'] (s : D), s ≠ 0 → algebraMap D E' s = 0 → HInv q E') → ∀ (ι : T →ₐ[D] E) (X : Finset (E →ₐ[D] T)), (∀ χ ∈ X, χ.comp ι = AlgHom.id D T) → HInv q (E ⧸ ⨅ χ ∈ X, RingHom.ker χ) := by
  intro q _ D T E _ _ _ _ _ _ _ _ _ hq hT hlow ι X
  classical
  induction X using Finset.induction_on with
  | empty =>
    intro _
    apply GlobalTheory.T.etaleHomotopyInvariantTwists_of_subsingleton
    rw [Ideal.Quotient.subsingleton_iff]
    simp
  | @insert χ Y hχY ih =>
    intro hX
    have hχ : χ.comp ι = AlgHom.id D T := hX χ (Finset.mem_insert_self _ _)
    have ih' := ih (fun ψ hψ => hX ψ (Finset.mem_insert_of_mem hψ))
    have hχι : ∀ t, χ (ι t) = t := fun t => by
      simpa using DFunLike.congr_fun hχ t
    have hins : (⨅ ψ ∈ insert χ Y, RingHom.ker ψ) = RingHom.ker χ ⊓ ⨅ ψ ∈ Y, RingHom.ker ψ := by
      rw [Finset.iInf_insert]
    rw [hins]
    set P : Ideal E := RingHom.ker χ with hPdef
    set I : Ideal E := ⨅ ψ ∈ Y, RingHom.ker ψ with hIdef
    by_cases hIP : I ≤ P
    · rw [inf_eq_right.mpr hIP]; exact ih'
    · obtain ⟨y, hyI, hyP⟩ := Set.not_subset.mp hIP
      have hy0 : χ y ≠ 0 := fun h => hyP (RingHom.mem_ker.mpr h)
      have hint : IsIntegral D (χ y) := Algebra.IsIntegral.isIntegral _
      have hne := Ideal.comap_ne_bot_of_integral_mem hy0 (Ideal.mem_span_singleton_self (χ y)) hint
      obtain ⟨s, hsmem, hs0⟩ := Submodule.ne_bot_iff _ |>.mp hne
      rw [Ideal.mem_comap, Ideal.mem_span_singleton'] at hsmem
      obtain ⟨u, hu⟩ := hsmem
      have hsPI : algebraMap D E s ∈ P ⊔ I := by
        have h1 : algebraMap D E s - ι u * y ∈ P := by
          rw [hPdef, RingHom.mem_ker, map_sub, map_mul, AlgHom.commutes, hχι, hu, sub_self]
        have h2 : ι u * y ∈ I := Ideal.mul_mem_left _ _ hyI
        have : algebraMap D E s = (algebraMap D E s - ι u * y) + ι u * y := by ring
        rw [this]
        exact Ideal.add_mem _ (Ideal.mem_sup_left h1) (Ideal.mem_sup_right h2)
      set J : Ideal E := P ⊓ I with hJ
      have hJP : J ≤ P := inf_le_left
      have hJI : J ≤ I := inf_le_right
      apply GlobalTheory.T.etaleHomotopyInvariantTwists_of_closedCover q (E ⧸ J) (P.map (Ideal.Quotient.mk J)) (I.map (Ideal.Quotient.mk J))
      · intro x hx
        obtain ⟨e, rfl⟩ := Ideal.Quotient.mk_surjective x
        have h1 := (Ideal.mem_quotient_iff_mem hJP).mp hx.1
        have h2 := (Ideal.mem_quotient_iff_mem hJI).mp hx.2
        have : Ideal.Quotient.mk J e = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr ⟨h1, h2⟩
        rw [this]; exact zero_mem _
      · have := hq.map (algebraMap D (E ⧸ J))
        simpa using this
      · have hsurj : Function.Surjective χ := fun t => ⟨ι t, hχι t⟩
        have e1 := DoubleQuot.quotQuotEquivQuotOfLE hJP
        have e2 := (Ideal.quotientKerAlgEquivOfSurjective hsurj).toRingEquiv
        exact GlobalTheory.T.etaleHomotopyInvariantTwists_of_ringEquiv q T _ (e1.trans e2).symm hT
      · exact GlobalTheory.T.etaleHomotopyInvariantTwists_of_ringEquiv q _ _ (DoubleQuot.quotQuotEquivQuotOfLE hJI).symm ih'
      · apply hlow _ s hs0
        change Ideal.Quotient.mk _ (Ideal.Quotient.mk J (algebraMap D E s)) = 0
        rw [Ideal.Quotient.eq_zero_iff_mem, ← Ideal.map_sup]
        exact Ideal.mem_map_of_mem _ hsPI

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsLastSide
section
open MeasureTheory Matrix GlobalTheory.Orb
open Formalism.REAL (UJ KG toM toMK muK expG inG Jm Kset)
open scoped ContDiff

namespace GlobalTheory.PolyShapeFinite

theorem main : ∀ (n : ℕ) (ε : Fin n → Bool) (F : ℝ → ℝ) (P : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ), IsBiFinite (KG ε) (fun g : UJ ε => ((F (∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖(toM g) z.1.1 z.1.2‖ ^ 2) : ℝ) : ℂ) * MvPolynomial.eval (Sum.elim (fun z : Fin n × Fin n => (toM g) z.1 z.2) (fun z : Fin n × Fin n => star ((toM g) z.1 z.2))) P) := by
  intro n ε F P
  let r : UJ ε → ℝ := fun g => ∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖(toM g) z.1.1 z.1.2‖ ^ 2
  let ev : UJ ε → ((Fin n × Fin n) ⊕ (Fin n × Fin n)) → ℂ := fun g =>
    Sum.elim (fun z : Fin n × Fin n => (toM g) z.1 z.2) (fun z : Fin n × Fin n => star ((toM g) z.1 z.2))
  let L : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ →ₗ[ℂ] (UJ ε → ℂ) :=
    { toFun := fun Q g => ((F (r g) : ℝ) : ℂ) * MvPolynomial.eval (ev g) Q
      map_add' := fun Q Q' => by funext g; simp [mul_add]
      map_smul' := fun c Q => by funext g; simp [MvPolynomial.smul_eq_C_mul, mul_left_comm] }
  unfold IsBiFinite
  have hle : Submodule.span ℂ {φ : UJ ε → ℂ | ∃ k ∈ KG ε, ∃ k' ∈ KG ε, φ = fun g =>
      ((F (r (k * g * k')) : ℝ) : ℂ) * MvPolynomial.eval (ev (k * g * k')) P} ≤
      (MvPolynomial.restrictTotalDegree _ ℂ P.totalDegree).map L := by
    rw [Submodule.span_le]
    rintro φ ⟨k, hk, k', hk', rfl⟩
    obtain ⟨Q, hQ, hQe⟩ := GlobalTheory.T.exists_poly_entries_conj_left_right_mul n (toM k) (toM k') P
    refine ⟨Q, (MvPolynomial.mem_restrictTotalDegree _ _ _).2 hQ, ?_⟩
    funext g
    have h1 : r (k * g * k') = r g := (GlobalTheory.T.offDiagBlockNorm_mul_invariant n ε).2 ⟨k, hk⟩ ⟨k', hk'⟩ g
    have h2 : toM (k * g * k') = toM k * toM g * toM k' := rfl
    have h3 : MvPolynomial.eval (ev (k * g * k')) P = MvPolynomial.eval (ev g) Q := by
      simp only [ev, h2]; exact hQe (toM g)
    show ((F (r g) : ℝ) : ℂ) * MvPolynomial.eval (ev g) Q = _
    rw [h1, h3]
  exact Submodule.finiteDimensional_of_le hle

end GlobalTheory.PolyShapeFinite
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndefiniteUnitaryCharacterMaximalCompactDetPowStatement
section
open scoped Matrix
open Formalism.BasicNotions.TH
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.indefiniteUnitaryCharacter_maximalCompact_det_pow : ∀ (R S : ℕ) (χ : Mat R S → ℂ),
    (∀ g h : Mat R S, gᴴ * Jm R S * g = Jm R S → hᴴ * Jm R S * h = Jm R S → χ (g * h) = χ g * χ h) →
    ContinuousOn χ {g : Mat R S | gᴴ * Jm R S * g = Jm R S} →
    (∀ g : Mat R S, gᴴ * Jm R S * g = Jm R S → χ g ≠ 0) →
    ∃ x y : ℤ, ∀ (a : Matrix (Fin R) (Fin R) ℂ) (d : Matrix (Fin S) (Fin S) ℂ), aᴴ * a = 1 → dᴴ * d = 1 →
      χ (Matrix.fromBlocks a 0 0 d) = a.det ^ x * d.det ^ y := by
  first | exact @GlobalTheory.KChar.kchar | exact GlobalTheory.KChar.kchar | (intros; apply GlobalTheory.KChar.kchar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
section
noncomputable section

open MeasureTheory ValuativeRel Matrix Filter Topology
open GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model GlobalTheory.SplitFlip

namespace GlobalTheory.KSplit

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def IsSmU (χ : kˣ →* ℂˣ) : Prop := IsOpen (χ.ker : Set kˣ) ∧ ∀ x, ‖(χ x : ℂ)‖ = 1

theorem isSmU_one : IsSmU (1 : kˣ →* ℂˣ) := ⟨by simp, by simp⟩

variable (k) in

def intM (m n : Type) : Set (Matrix m n k) := {X | ∀ i j, X i j ∈ 𝒪[k]}

def IsEqv {n : ℕ} (ν : kˣ →* ℂˣ) (z : ℂ) (l : (Matrix (Fin n) (Fin n) k → ℂ) → ℂ) : Prop :=
  (∀ φ ∈ SB (Matrix (Fin n) (Fin n) k), ∀ φ' ∈ SB (Matrix (Fin n) (Fin n) k), l (φ + φ') = l φ + l φ') ∧
  (∀ c : ℂ, ∀ φ ∈ SB (Matrix (Fin n) (Fin n) k), l (c • φ) = c * l φ) ∧
  ∀ g₁ g₂ : GL (Fin n) k, ∀ φ ∈ SB (Matrix (Fin n) (Fin n) k),
    (ν (gdet g₁ * gdet g₂) : ℂ) * apow (gdet g₁ * gdet g₂) z * l (fun X => φ (g₁.val * X * g₂.val)) = l φ

example (n : ℕ) : IsEqv (n := n) (1 : kˣ →* ℂˣ) 0 (fun φ => φ 0) :=
  ⟨fun _ _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ => by simp⟩

def indSp (a a' : ℕ) (α β : kˣ →* ℂˣ) : Submodule ℂ (GL (Fin (a + a')) k → ℂ) where
  carrier := {f | (∀ (b : GL (Fin (a + a')) k) (A : GL (Fin a) k) (D : GL (Fin a') k) (N : Matrix (Fin a) (Fin a') k),
      b.val.submatrix finSumFinEquiv finSumFinEquiv = fromBlocks A.val N 0 D.val → ∀ h, f (b * h) =
        (α (gdet A) : ℂ) * β (gdet D) * apow (gdet A) ((a' : ℂ) / 2) * apow (gdet D) (-(a : ℂ) / 2) * f h) ∧
    ∀ᶠ u in 𝓝 (1 : GL (Fin (a + a')) k), ∀ h, f (h * u) = f h}
  add_mem' := by
    rintro f f' ⟨h1, h2⟩ ⟨h1', h2'⟩
    refine ⟨fun b A D N hb h => ?_, (h2.and h2').mono fun u hu h => ?_⟩
    · simp only [Pi.add_apply, h1 b A D N hb, h1' b A D N hb, mul_add]
    · simp only [Pi.add_apply, hu.1, hu.2]
  zero_mem' := ⟨fun _ _ _ _ _ _ => by simp, Eventually.of_forall fun _ _ => rfl⟩
  smul_mem' := by
    rintro c f ⟨h1, h2⟩
    refine ⟨fun b A D N hb h => ?_, h2.mono fun u hu h => ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul, h1 b A D N hb]; ring
    · simp only [Pi.smul_apply, hu]

def mapA {a : ℕ} (a' : ℕ) (l : (Matrix (Fin a) (Fin a) k → ℂ) → ℂ) (ν β : kˣ →* ℂˣ)
    (Φ : Matrix (Fin a) (Fin (a + a')) k → ℂ) (h : GL (Fin (a + a')) k) : ℂ :=
  l fun g => omA ν β 1 h Φ (g * X0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')))

def mapB (a : ℕ) {a' : ℕ} (l : (Matrix (Fin a') (Fin a') k → ℂ) → ℂ) (ν α : kˣ →* ℂˣ)
    (Ψ : Matrix (Fin a') (Fin (a + a')) k → ℂ) (h : GL (Fin (a + a')) k) : ℂ :=
  l fun g => omB ν α 1 h Ψ (g * Y0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')))

section Frames

variable {R S D : Type} [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S] [Fintype D] [DecidableEq D]

theorem restrict_mem_SB {P : Matrix R D k} {P' : Matrix D R k} (hP : P * P' = 1) {Φ : Matrix R D k → ℂ}
    (hΦ : Φ ∈ SB (Matrix R D k)) : (fun g : Matrix R R k => Φ (g * P)) ∈ SB (Matrix R R k) := by
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  have c1 : Continuous fun g : Matrix R R k => g * P := continuous_id.matrix_mul continuous_const
  have c2 : Continuous fun X : Matrix R D k => X * P' := continuous_id.matrix_mul continuous_const
  have e : IsClosedEmbedding fun g : Matrix R R k => g * P :=
    Function.LeftInverse.isClosedEmbedding (f := fun X : Matrix R D k => X * P')
      (fun g => by simp only [Matrix.mul_assoc, hP, Matrix.mul_one]) c2 c1
  exact ⟨hΦ.1.comp_continuous c1, hΦ.2.comp_isClosedEmbedding e⟩

omit [DecidableEq R] [DecidableEq D] in

theorem indicator_intM_mem_SB : (intM k R D).indicator (1 : Matrix R D k → ℂ) ∈ SB (Matrix R D k) := by
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  have hc : IsCompact (intM k R D) := isCompact_intMatrix
  have hK : IsClopen (intM k R D) := ⟨hc.isClosed, isOpen_intMatrix⟩
  exact ⟨(LocallyConstant.indicator (1 : LocallyConstant _ ℂ) hK).isLocallyConstant,
    HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _⟩

theorem exists_extend_SB {P : Matrix R D k} {Q : Matrix S D k} (hP : P * Pᵀ = 1) (hQ : P * Qᵀ = 0)
    (hPQ : Pᵀ * P + Qᵀ * Q = 1) {φ : Matrix R R k → ℂ} (hφ : φ ∈ SB (Matrix R R k)) :
    ∃ Φ ∈ SB (Matrix R D k), ∀ g, Φ (g * P) = φ g := by
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  have hI := indicator_intM_mem_SB (k := k) (R := R) (D := S)
  have c1 : Continuous fun X : Matrix R D k => X * Pᵀ := continuous_id.matrix_mul continuous_const
  have c2 : Continuous fun X : Matrix R D k => X * Qᵀ := continuous_id.matrix_mul continuous_const
  have c3 : Continuous fun x : Matrix R R k × Matrix R S k => x.1 * P + x.2 * Q :=
    (continuous_fst.matrix_mul continuous_const).add (continuous_snd.matrix_mul continuous_const)
  refine ⟨fun X => φ (X * Pᵀ) * (intM k R S).indicator 1 (X * Qᵀ),
    ⟨(hφ.1.comp_continuous c1).mul (hI.1.comp_continuous c2), ?_⟩, fun g => ?_⟩
  · refine HasCompactSupport.intro ((hφ.2.isCompact.prod hI.2.isCompact).image c3) fun X hX => ?_
    by_contra h
    obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 h
    refine hX ⟨(X * Pᵀ, X * Qᵀ), ⟨subset_tsupport _ h1, subset_tsupport _ h2⟩, ?_⟩
    simp only [Matrix.mul_assoc, ← Matrix.mul_add, hPQ, Matrix.mul_one]
  · simp only [Matrix.mul_assoc, hP, hQ, Matrix.mul_one, Matrix.mul_zero]
    rw [Set.indicator_of_mem (show (0 : Matrix R S k) ∈ intM k R S from fun _ _ => zero_mem _)]
    simp

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem frame_rel (σ : R ⊕ S ≃ D) : X0 k σ * (X0 k σ)ᵀ = 1 ∧ Y0 k σ * (Y0 k σ)ᵀ = 1 ∧ X0 k σ * (Y0 k σ)ᵀ = 0 ∧
    Y0 k σ * (X0 k σ)ᵀ = 0 ∧ (X0 k σ)ᵀ * X0 k σ + (Y0 k σ)ᵀ * Y0 k σ = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · ext i j; rw [frameMatrixFirstColumnBlock_mul_apply]; simp [X0, one_apply, eq_comm]
  · ext i j; rw [frameMatrixSecondColumnBlock_mul_apply]; simp [Y0, one_apply, eq_comm]
  · ext i j; simp [frameMatrixFirstColumnBlock_mul_apply, Y0]
  · ext i j; simp [frameMatrixSecondColumnBlock_mul_apply, X0]
  · ext i j
    obtain ⟨i | i, rfl⟩ := σ.surjective i <;> obtain ⟨j | j, rfl⟩ := σ.surjective j <;>
      simp [X0, Y0, Matrix.mul_apply, one_apply, eq_comm]

end Frames

variable {a a' : ℕ} {z : ℂ} {ν α β : kˣ →* ℂˣ}

theorem restrict_X0 {Φ : Matrix (Fin a) (Fin (a + a')) k → ℂ} (hΦ : Φ ∈ SB (Matrix (Fin a) (Fin (a + a')) k)) :
    (fun g : Matrix (Fin a) (Fin a) k => Φ (g * X0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')))) ∈ SB _ :=
  restrict_mem_SB (frame_rel _).1 hΦ

theorem restrict_Y0 {Ψ : Matrix (Fin a') (Fin (a + a')) k → ℂ} (hΨ : Ψ ∈ SB (Matrix (Fin a') (Fin (a + a')) k)) :
    (fun g : Matrix (Fin a') (Fin a') k => Ψ (g * Y0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')))) ∈ SB _ :=
  restrict_mem_SB (frame_rel _).2.1 hΨ

theorem mapA_omA_right (l : (Matrix (Fin a) (Fin a) k → ℂ) → ℂ) (Φ : Matrix (Fin a) (Fin (a + a')) k → ℂ)
    (x h : GL (Fin (a + a')) k) : mapA a' l ν β (omA ν β 1 x Φ) h = mapA a' l ν β Φ (h * x) := by
  unfold mapA
  rw [← omA_mul, one_mul]

theorem mapB_omB_right (l : (Matrix (Fin a') (Fin a') k → ℂ) → ℂ) (Ψ : Matrix (Fin a') (Fin (a + a')) k → ℂ)
    (x h : GL (Fin (a + a')) k) : mapB a l ν α (omB ν α 1 x Ψ) h = mapB a l ν α Ψ (h * x) := by
  unfold mapB
  rw [← omB_mul, one_mul]

end Local

section Adelic

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def locMat {v : Pl F} (t : E →ₐ[F] Fv F v) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (b : GL (Fin n) (Fv F v)) :
    UA σ J →* GL (Fin n) (Fv F v) where
  toFun g := b⁻¹ * Matrix.GeneralLinearGroup.map (piW t) g.1 * b
  map_one' := by simp
  map_mul' g h := by simp [mul_assoc]

theorem locMat_val {v : Pl F} (t : E →ₐ[F] Fv F v) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (b : GL (Fin n) (Fv F v))
    (g : UA σ J) : (locMat t b g).val = (b⁻¹).val * (mat g).map (piW t) * b.val := rfl

end Adelic

end GlobalTheory.KSplit

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlacesIffGoodPrimesFixedByConj
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.InertPlaces

theorem inert_places_iff : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → ∀ (t : T) (P : Pl D.host.E), (∃ Q ∈ A3.okI t, R.plI Q = P) ↔ (Good R.toRealDat t P ∧ conjPl P = P) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F h t P
  have hSb : (R.Sb : Set (Pl D.host.E)) = R.Pg := by rw [h.allPl]
  constructor
  · rintro ⟨Q, hQ, rfl⟩
    obtain ⟨hfix, hoff⟩ := (h.inert.tie.okI t Q).1 hQ
    rw [Formalism.DivisionValues.GluingInclusion.conjIdeal_eq] at hfix
    have hf : Formalism.DivisionValues.conjPl (R.plI Q) = R.plI Q := HeightOneSpectrum.ext hfix
    refine ⟨fun PP hPP => ⟨fun he => hoff ?_, fun hc => hoff ?_⟩, hf⟩
    · rcases hPP with hm | hm
      · exact Or.inl (by rw [hSb, ← he]; exact hm)
      · exact Or.inr (by rw [← he]; exact hm)
    · have e1 := GlobalTheory.SplitHeckeAdj.eq_conj_of_isConjPl hc
      have e2 : PP = R.plI Q := by
        rw [← Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl PP, ← e1, hf]
      rcases hPP with hm | hm
      · exact Or.inl (by rw [hSb, ← e2]; exact hm)
      · exact Or.inr (by rw [← e2]; exact hm)
  · rintro ⟨hg, hf⟩
    have hnS : P ∉ (R.Sb : Set (Pl D.host.E)) := by
      rw [hSb]; intro hm; exact (hg P (Or.inl hm)).1 rfl
    have hio : Formalism.IndefR.Bridge.InertOff P (R.Sb : Set (Pl D.host.E)) := by
      refine ⟨?_, hnS⟩
      rw [Formalism.DivisionValues.GluingInclusion.conjIdeal_eq, hf]
    obtain ⟨Q, hQ⟩ := h.inert.onto P hio
    refine ⟨Q, (h.inert.tie.okI t Q).2 ⟨?_, ?_⟩, hQ⟩
    · rw [hQ]; exact hio.1
    · rw [hQ]
      rintro (hm | hm)
      · exact hnS hm
      · exact (hg P (Or.inr hm)).1 rfl

end GlobalTheory.InertPlaces
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntAEMulMem
section
open scoped TensorProduct
open NumberField IsDedekindDomain

namespace GlobalTheory.IntegralAdeleProducts

theorem intAf_mul {F : Type} [Field F] [NumberField F] {a b : FiniteAdeleRing (𝓞 F) F}
    (ha : a ∈ HeckeCharacterZeroLocus.ThmBIn.intAf F) (hb : b ∈ HeckeCharacterZeroLocus.ThmBIn.intAf F) : a * b ∈ HeckeCharacterZeroLocus.ThmBIn.intAf F :=
  fun v => mul_mem (ha v) (hb v)

theorem intAE_mul_mem {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {s t : FiniteAdeleRing (𝓞 F) F ⊗[F] E}
    (hs : s ∈ HeckeCharacterZeroLocus.ThmBIn.intAE F E) (ht : t ∈ HeckeCharacterZeroLocus.ThmBIn.intAE F E) :
    s * t ∈ HeckeCharacterZeroLocus.ThmBIn.intAE F E := by
  unfold HeckeCharacterZeroLocus.ThmBIn.intAE at hs ht
  induction hs using AddSubgroup.closure_induction with
  | zero => rw [zero_mul]; exact zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | neg x _ hx => rw [neg_mul]; exact neg_mem hx
  | mem x hx =>
    obtain ⟨a, ha, p, rfl⟩ := hx
    induction ht using AddSubgroup.closure_induction with
    | zero => rw [mul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
    | neg x _ hx => rw [mul_neg]; exact neg_mem hx
    | mem y hy =>
      obtain ⟨b, hb, q, rfl⟩ := hy
      refine AddSubgroup.subset_closure ⟨a * b, intAf_mul ha hb, p * q, ?_⟩
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      rfl

end GlobalTheory.IntegralAdeleProducts
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralHolomorphicTypeFamilyHolomorphicTypeStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_holomorphicTypeFamily_holomorphicType : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (Hm : ι → Mt n) (q : ι → ℕ) (x₀ : ι → Mt n) (w : ι → Fin n → ℤ), (∀ τ, OrthFr (Hm τ) (q τ) (x₀ τ)) → ∀ (Ω : Type) [MeasurableSpace Ω] (ν : Measure Ω) [IsFiniteMeasure ν] (f : Ω → (ι → Mt n) → ℂ) (C : ℝ), (∀ o, HolFn Hm q x₀ w (f o)) → (∀ o, ∀ u ∈ UG Hm, ‖f o u‖ ≤ C) → (∀ u ∈ UG Hm, AEStronglyMeasurable (fun o => f o u) ν) → HolFn Hm q x₀ w fun u => ∫ o, f o u ∂ν := by
  first | exact @GlobalTheory.HolDict.holFn_integral | exact GlobalTheory.HolDict.holFn_integral | (intros; apply GlobalTheory.HolDict.holFn_integral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralLocalCenterFiniteMaximalIdealsStatement
section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralLocalCenter_finite_maximal_ideals : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : AwayP p) (h1 : IsIntV G v 1) (hm : ∀ y z : Qv v ⊗[ℚ] G.C, IsIntV G v y → IsIntV G v z → IsIntV G v (y * z)), Set.Finite {I : Ideal (intF G v h1 hm) | I.IsMaximal} := by
  first | (exact @GlobalTheory.OrbFinAf.intF_finite_maximal) | (exact GlobalTheory.OrbFinAf.intF_finite_maximal) | (intros; apply GlobalTheory.OrbFinAf.intF_finite_maximal  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEffectivePicClassAddIntegralStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isEffectivePicClass_add_integral : ∀ {X : Scheme.{0}} [IsIntegral X] (a b : GlobalTheory.CechPic.Pic X), GlobalTheory.EffBound.Eff a → GlobalTheory.EffBound.Eff b → GlobalTheory.EffBound.Eff (a + b) := by
  first | exact @GlobalTheory.EffBound.eff_add | exact GlobalTheory.EffBound.eff_add | (intros; apply GlobalTheory.EffBound.eff_add <;> assumption)
end

