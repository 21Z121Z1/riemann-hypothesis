import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0254
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1233
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1263
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1272
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1240
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1271
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1200
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1239
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1176
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0176
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1213
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1269
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0164
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1187
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0165
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0124
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0155
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1266
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0004
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1217
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0497
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0531
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0528
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0364
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0418

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantIntegralVanishesIwahori
section
open ValuativeRel Matrix MeasureTheory
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.LocLanglands GlobalTheory.GamMul DiscreteGroups.sglob.LConv
open scoped Pointwise

noncomputable section
namespace GlobalTheory.GamMul.UnitCell

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {m : ℕ}

theorem setOf_eq_mul (N K : Subgroup (GL (Fin m) k)) :
    {g : GL (Fin m) k | ∃ u ∈ N, ∃ c ∈ K, g = u * c} = (N : Set (GL (Fin m) k)) * (K : Set (GL (Fin m) k)) := by
  ext g
  simp only [Set.mem_setOf_eq, Set.mem_mul]
  exact ⟨fun ⟨u, hu, c, hc, e⟩ => ⟨u, hu, c, hc, e.symm⟩, fun ⟨u, hu, c, hc, e⟩ => ⟨u, hu, c, hc, e.symm⟩⟩

theorem isTestFun_unitCell :
    IsTestFun (Set.indicator {g : GL (Fin m) k | ∃ u ∈ unipB k (Fin m), ∃ c ∈ KO k (Fin m), g = u * c}
      (fun _ => (1 : ℂ))) := by
  rw [setOf_eq_mul]
  exact InvInt.isTestFun_indicator

theorem eq_zero_of_unitCell (I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ) (hI : IsInvIntegral I)
    (h0 : I (Set.indicator {g : GL (Fin m) k | ∃ u ∈ unipB k (Fin m), ∃ c ∈ KO k (Fin m), g = u * c}
      (fun _ => (1 : ℂ))) = 0) (f : GL (Fin m) k → ℂ) (hf : IsTestFun f) : I f = 0 := by
  have hB : IsOpen ((Subtype.val : (⊤ : Subgroup (GL (Fin m) k)) → GL (Fin m) k) ⁻¹'
      (KO k (Fin m) : Set (GL (Fin m) k))) :=
    SplitFlip.isOpen_KO.preimage continuous_subtype_val
  refine GlobalTheory.T.invariant_integral_unipotent_compact (GL (Fin m) k) (unipB k (Fin m)) ⊤ (KO k (Fin m)) {F | IsTestFun F} ?_ ?_ ?_
    le_top SplitFlip.isCompact_KO hB I ?_ ?_ h0 f hf
  · intro F
    simp only [Set.mem_setOf_eq, IsTestFun]
    refine and_congr Iff.rfl (and_congr Iff.rfl ⟨fun ⟨C, hC, hs⟩ => ⟨C, hC, fun _ _ => Subgroup.mem_top _, hs⟩,
      fun ⟨C, hC, _, hs⟩ => ⟨C, hC, hs⟩⟩)
  · intro K _ hKc hKo
    have hKo' : IsOpen (K : Set (GL (Fin m) k)) :=
      hKo.preimage (continuous_id.subtype_mk (p := fun g => g ∈ (⊤ : Subgroup (GL (Fin m) k))) fun g => Subgroup.mem_top g)
    rw [setOf_eq_mul]
    exact ⟨InvInt.isClosed_unipB.mul_right_of_isCompact hKc, hKo'.mul_left⟩
  · intro U hU
    obtain ⟨_, K, hKo, hKc, hKU, hKO, hnorm, -⟩ := GlobalTheory.T.exists_small_open_compact_normal k m m 0 (Nat.add_zero m) U hU
    exact ⟨K, hKO, hKc, hKo.preimage continuous_subtype_val, hKU, hnorm⟩
  · intro F _ F' _ c c'
    have : (fun g => c * F g + c' * F' g) = c • F + c' • F' := rfl
    rw [this, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  · intro F hF x _
    exact hI F hF x

theorem main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m : ℕ),
    IsTestFun (Set.indicator {g : GL (Fin m) k | ∃ u ∈ unipB k (Fin m), ∃ c ∈ KO k (Fin m), g = u * c}
      (fun _ => (1 : ℂ))) ∧
    (∀ (I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ), IsInvIntegral I →
      I (Set.indicator {g : GL (Fin m) k | ∃ u ∈ unipB k (Fin m), ∃ c ∈ KO k (Fin m), g = u * c}
        (fun _ => (1 : ℂ))) = 0 → ∀ f, IsTestFun f → I f = 0) ∧
    ∃ (I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ), IsInvIntegral I ∧
      I (Set.indicator {g : GL (Fin m) k | ∃ u ∈ unipB k (Fin m), ∃ c ∈ KO k (Fin m), g = u * c}
        (fun _ => (1 : ℂ))) = 1 := by
  intro k _ _ _ _ m
  refine ⟨isTestFun_unitCell, fun I hI h0 f hf => eq_zero_of_unitCell I hI h0 f hf, ?_⟩
  obtain ⟨I, f, hI, hf, hne⟩ := InvInt.exists_isInvIntegral k m
  set a := I (Set.indicator {g : GL (Fin m) k | ∃ u ∈ unipB k (Fin m), ∃ c ∈ KO k (Fin m), g = u * c}
    (fun _ => (1 : ℂ))) with ha
  have ha0 : a ≠ 0 := fun h => hne (eq_zero_of_unitCell I hI h f hf)
  refine ⟨a⁻¹ • I, fun F hF x => ?_, ?_⟩
  · simp only [LinearMap.smul_apply, hI F hF x]
  · rw [LinearMap.smul_apply, ← ha, smul_eq_mul, inv_mul_cancel₀ ha0]

end GlobalTheory.GamMul.UnitCell
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactClosureZpowersLeftMulGLIffIntegralStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompact_closure_zpowers_leftMulGL_iff_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (a : ℕ) (B : GlobalTheory.UnitLemma.InvAlg K) (b : Module.Basis (Fin a) K.E B.A) (t : B.Aˣ), IsCompact (closure (Subgroup.zpowers (GlobalTheory.TwOrbLat.mulGL e b t) : Set (GLw a w))) ↔ t ∈ GlobalTheory.UnitLemma.intUnits K.O B.A := by
  first | exact @GlobalTheory.TwOrbLat.isCompact_closure_zpowers_mulGL_iff | exact GlobalTheory.TwOrbLat.isCompact_closure_zpowers_mulGL_iff | (intros; apply GlobalTheory.TwOrbLat.isCompact_closure_zpowers_mulGL_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactClosureZpowersMulIntegralUnitStatement
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompact_closure_zpowers_mul_integralUnit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ) (b : Module.Basis (Fin m) K.E B.A) (a : B.Aˣ), a ∈ GlobalTheory.UnitLemma.intUnits K.O B.A → IsCompact (closure (Subgroup.zpowers (GlobalTheory.TwLat.mulU e b a) : Set (GLw m w))) := by
  first | exact @GlobalTheory.TwLat.isCompact_closure_zpowers_mulU | exact GlobalTheory.TwLat.isCompact_closure_zpowers_mulU | (intros; apply GlobalTheory.TwLat.isCompact_closure_zpowers_mulU <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFreeGenTopFormEtaleTowerTranscendenceBasis
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair

theorem IsEtTower.eval₂Hom_pderiv_eq_zero {K L : Type} [Field K] [Field L] {cK : ℂ →+* K} {cL : ℂ →+* L} {r : ℕ}
    {R : Subring K} {T : Subring L} {ι : R →+* T} {ψ : T →+* R} {τ : Fin r → T}
    (h : IsEtTower cK R cL T ι ψ τ) (P : MvPolynomial (Fin r) R) (i : Fin r)
    (hP : MvPolynomial.eval₂Hom ι τ P = 0) :
    MvPolynomial.eval₂Hom ι τ (MvPolynomial.pderiv i P) = 0 := by
  letI : Algebra R T := ι.toAlgebra
  letI : Algebra (MvPolynomial (Fin r) R) T := (MvPolynomial.eval₂Hom ι τ).toAlgebra
  haveI : IsScalarTower R (MvPolynomial (Fin r) R) T := IsScalarTower.of_algebraMap_eq' (by
    ext a; simp [RingHom.algebraMap_toAlgebra])
  haveI : Algebra.FormallyEtale (MvPolynomial (Fin r) R) T := h.etale
  let d : Derivation R (MvPolynomial (Fin r) R) T :=
    (Algebra.linearMap (MvPolynomial (Fin r) R) T).compDer (MvPolynomial.pderiv i)
  let f : Ω[MvPolynomial (Fin r) R⁄R] →ₗ[MvPolynomial (Fin r) R] T := d.liftKaehlerDifferential
  have hb := KaehlerDifferential.isBaseChange_of_formallyEtale R (MvPolynomial (Fin r) R) T
  let g : Ω[T⁄R] →ₗ[T] T := hb.lift f
  have key : g (KaehlerDifferential.D R T (algebraMap (MvPolynomial (Fin r) R) T P)) =
      algebraMap (MvPolynomial (Fin r) R) T (MvPolynomial.pderiv i P) := by
    rw [← KaehlerDifferential.map_D R R (MvPolynomial (Fin r) R) T]
    erw [hb.lift_eq]
    simp [f, d]
  have h0 : algebraMap (MvPolynomial (Fin r) R) T P = 0 := hP
  rw [h0, map_zero, map_zero] at key
  exact key.symm

theorem charZero_subring_of_complex {K : Type} [Field K] (cK : ℂ →+* K) (R : Subring K) :
    CharZero R := by
  haveI : CharZero K := charZero_of_injective_ringHom cK.injective
  exact ⟨fun a b h => by
    have := congrArg (fun t : R => (t : K)) h
    simpa using this⟩

theorem IsEtTower.eval₂Hom_injective {K L : Type} [Field K] [Field L] {cK : ℂ →+* K}
    {cL : ℂ →+* L} {r : ℕ} {R : Subring K} {T : Subring L} {ι : R →+* T} {ψ : T →+* R}
    {τ : Fin r → T} (h : IsEtTower cK R cL T ι ψ τ) :
    Function.Injective (MvPolynomial.eval₂Hom ι τ) := by
  haveI := charZero_subring_of_complex cK R
  have hI := GlobalTheory.T.mvPolynomial_ideal_eq_bot_of_pderiv_stable_no_constants r (RingHom.ker (MvPolynomial.eval₂Hom ι τ))
    (fun P hP i => h.eval₂Hom_pderiv_eq_zero P i hP)
    (fun a ha => by
      rw [RingHom.mem_ker, MvPolynomial.eval₂Hom_C] at ha
      simpa [h.retr] using congrArg ψ ha)
  exact (RingHom.injective_iff_ker_eq_bot _).2 hI

theorem isFreeGen_dForm_tower : ∀ {K L : Type} [Field K] [Field L] (cK : ℂ →+* K) (cL : ℂ →+* L)
    (n r : ℕ) (R : Subring K) (T : Subring L) (ι : R →+* T) (ψ : T →+* R) (τ : Fin r → T)
    (x : Fin n → R),
  IsEtTower cK R cL T ι ψ τ → TrBasis cK (fun i => (x i : K)) →
  IsFreeGen L (dForm cL (Fin.append (fun i => (τ i : L)) (fun i => (ι (x i) : L)))) := by
  intro K L _ _ cK cL n r R T ι ψ τ x h hx
  have hinj := h.eval₂Hom_injective
  letI := cL.toAlgebra
  have hind := GlobalTheory.T.algebraicIndependent_etaleTower_coordinates cK cL n r R T ι ψ τ x h hx hinj
  have halg : Algebra.IsAlgebraic
      (Algebra.adjoin ℂ (Set.range (Fin.append (fun i => (τ i : L)) (fun i => (ι (x i) : L))))) L := by
    refine ⟨fun z => GlobalTheory.T.isAlgebraic_of_isAlgebraic_over_algebraic_subring _ _ z ?_ (GlobalTheory.T.isAlgebraic_over_mvPolynomial_range_etaleTower cK cL r R T ι ψ τ h hinj z)⟩
    rintro b ⟨a, rfl⟩
    exact GlobalTheory.T.isAlgebraic_mvPolynomialEval_adjoin_etaleTowerCoords cK cL n r R T ι ψ τ x h hx a
  have htr : TrBasis cL (Fin.append (fun i => (τ i : L)) (fun i => (ι (x i) : L))) :=
    isTranscendenceBasis_iff_algebraicIndependent_isAlgebraic.2 ⟨hind, halg⟩
  exact isFreeGen_dForm_of_trBasis cL htr

end GlobalTheory.FieldPair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOrIsEmptyGenericMemberLinearSystem
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.GenericMember
open GlobalTheory.ThickeningDetermines (secIdeal)
open scoped TensorProduct

namespace GlobalTheory

theorem GenericMember.isIntegral_or_isEmpty_zeroScheme : ∀ (k : Type) [Field k] (N : ℕ) (X X' : Scheme.{0}) [IsIntegral X] [IsIntegral X'] (f : X ⟶ Sp k) (f' : X' ⟶ Sp (FractionRing (MvPolynomial (Fin N) k))) (π : X' ⟶ X), IsPullback π f' f (spMap (algebraMap k (FractionRing (MvPolynomial (Fin N) k)))) → ∀ (L : LB X) (hL : L.IsLB) (b : Fin N → L.Sec), ⨆ i, nonzeroLocus (b i) = ⊤ → ∃ t : (L.pull π).Sec, t ≠ 0 ∧ (IsIntegral (secIdeal (LB.isLB_pull hL π) t).subscheme ∨ IsEmpty (secIdeal (LB.isLB_pull hL π) t).subscheme) := by
  intro k _ N X X' _ _ f f' π hP L hL b hb

  have loc : ∀ x : X, ∃ (V : X.Opens) (c : L.ι) (hVc : V ≤ L.U c) (j : Fin N),
      IsAffineOpen V ∧ x ∈ V ∧ IsUnit (resG X hVc ((b j).f c)) := by
    intro x
    have hx : x ∈ (⨆ i, nonzeroLocus (b i)) := hb.ge (Set.mem_univ x)
    obtain ⟨j, hj⟩ := Opens.mem_iSup.1 hx
    obtain ⟨c, hc⟩ := Opens.mem_iSup.1 hj
    obtain ⟨V, hVa, hxV, hVle⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hc
    have hVc : V ≤ L.U c := hVle.trans (X.basicOpen_le _)
    refine ⟨V, c, hVc, j, hVa, hxV, ?_⟩
    have h1 := RingedSpace.isUnit_res_basicOpen X.toRingedSpace ((b j).f c)
    have h2 := h1.map (X.presheaf.map (homOfLE hVle).op).hom
    convert h2 using 1
    simp only [resG]
    erw [← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl
  choose V c hVc j hVa hxV hu using loc
  have hW : ∀ x, IsAffineOpen (π ⁻¹ᵁ V x) := fun x => (GlobalTheory.T.affine_base_change_over_field_extension k _ X X' f f' π hP (V x) (hVa x)).1
  have key : ∀ x, (genSec k N f' π L b).f (fun _ => c x) ≠ 0 ∧
      ((secIdeal (LB.isLB_pull hL π) (genSec k N f' π L b)).ideal ⟨π ⁻¹ᵁ V x, hW x⟩ = ⊤ ∨
        ((secIdeal (LB.isLB_pull hL π) (genSec k N f' π L b)).ideal ⟨π ⁻¹ᵁ V x, hW x⟩).IsPrime ∧
        ((secIdeal (LB.isLB_pull hL π) (genSec k N f' π L b)).ideal ⟨π ⁻¹ᵁ V x, hW x⟩).comap
          (π.app (V x)).hom = ⊥) := fun x => by
    obtain ⟨-, e, he1, he2⟩ := GlobalTheory.T.affine_base_change_over_field_extension k _ X X' f f' π hP (V x) (hVa x)
    exact GlobalTheory.T.genericMemberSection_ne_zero_isPrime_affineChart k N X X' f f' π L hL b (V x) ⟨x, hxV x⟩ (hW x) (c x) (hVc x) (j x) (hu x) e he1 he2
  refine ⟨genSec k N f' π L b, fun h0 => ?_, ?_⟩
  · obtain ⟨x⟩ := (inferInstance : Nonempty X)
    exact (key x).1 (by rw [h0]; rfl)
  · refine GlobalTheory.T.isIntegral_or_isEmpty_subscheme_of_prime_charts X' _ X (fun x => ⟨π ⁻¹ᵁ V x, hW x⟩) ?_ (fun x => ?_) (fun x y hx hy => ?_)
    · refine eq_top_iff.2 fun z _ => Opens.mem_iSup.2 ⟨π z, hxV (π z)⟩
    · rcases (key x).2 with h | h
      · exact Or.inl h
      · exact Or.inr h.1
    · rcases (key x).2 with h | h
      · exact absurd h hx.ne_top
      · have hg := GlobalTheory.T.fromSpec_comap_eq_bot_eq_genericPoint X X' π (V x) (hVa x) (hW x) _ hx h.2
        show π _ ∈ V y
        rw [hg]
        exact (genericPoint_spec X).mem_open_set_iff (V y).isOpen |>.2 ⟨y, trivial, hxV y⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLabelThetaLiftSpaceIffDualStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLabel_thetaLiftSpace_iff_dual : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) {s : ℕ}, Core R F → ∀ i P d, Good R A.μ0 P → (IsLab (Wc D i) P d ↔ IsLab (Yc D 0) P (dualLab d)) ∧ (IsLab (Wc D i) P d ↔ IsLab (Yc D 0) P d) := by
  first | exact @GlobalTheory.LabEq.isLab_W_iff | exact GlobalTheory.LabEq.isLab_W_iff | (intros; apply GlobalTheory.LabEq.isLab_W_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLevelBlockLevelsSplitPlaceStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.CtLevel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLevel_blockLevels_splitPlace : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b n : ℕ) (h : a + b = n) (w : Pl E)
    (N : Subgroup (GLw n w)) (μ : (w.adicCompletion E)ˣ →* ℂˣ), IsSplitAt w → IsOpen (N : Set (GLw n w)) →
    IsOpen {x | μ x = 1} →
    IsLevel (thL a w) (GlobalTheory.LFun.KGL w a) (lev₁ h w N μ) ∧ IsLevel (thL b w) (GlobalTheory.LFun.KGL w b) (lev₂ h w N μ) := by
  first | exact @GlobalTheory.BCT.CtLevel.isLevel_lev_split | exact GlobalTheory.BCT.CtLevel.isLevel_lev_split | (intros; apply GlobalTheory.BCT.CtLevel.isLevel_lev_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefOfSemiPosGeneratedBySmallSectionsStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isNef_of_semiPos_generated_by_smallSections : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (M : HermLB p) (n : ℕ) (s : Fin n → M.B.Sec), M.SemiPos D → (∀ i, s i ∈ M.smallSec) → (∀ x : X, ∃ i, x ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (s i)) → M.IsNef D := by
  first | exact @GlobalTheory.GenNef.isNef_of_gen_small | exact GlobalTheory.GenNef.isNef_of_gen_small | (intros; apply GlobalTheory.GenNef.isNef_of_gen_small <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicFlagStabilizerNotLowerWeight
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open scoped TensorProduct
open GlobalTheory.Mem.UnipCocompact
open Formalism.UG (cT cT_mul cT_one)

namespace GlobalTheory.UAut.NoLower

theorem abstract_no_lower {A : Type} [CommRing A] {n r : ℕ} (st : Matrix (Fin n) (Fin n) A →+ Matrix (Fin n) (Fin n) A)
    (u : Fin r → Matrix (Fin n) (Fin n) A) (X Y : Matrix (Fin n) (Fin r) A) (L T : Matrix (Fin r) (Fin n) A)
    (hu : ∀ j, u j = X * single j j (1 : A) * L) (hs : ∀ j, st (u j) = Y * single j j (1 : A) * T)
    (hLX : L * X = 1) (hTX : T * X = 0) (hTY : T * Y = 1) (d : Fin r → ℕ) (M : ℕ) (hd : ∀ j, d j < M)
    (x : Matrix (Fin n) (Fin n) A) (B C : Matrix (Fin r) (Fin r) A) (hB : ∀ i j, d j < d i → B i j = 0)
    (hC : ∀ i j, d i < d j → C i j = 0) (eB : x * X = X * B) (eC : T * x = C * T) :
    ∀ a b, wt d M a < wt d M b → fam st u a * x * fam st u b = 0 := by
  have e0 : fam st u none = 1 - (X * L + Y * T) := by
    simp only [fam, Option.elim, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, hs]
    simp only [hu, ← Matrix.sum_mul, ← Matrix.mul_sum, Matrix.sum_single_one, Matrix.mul_one]
  have e1 : ∀ j, fam st u (some (.inl j)) = X * single j j (1 : A) * L := hu
  have e2 : ∀ j, fam st u (some (.inr j)) = Y * single j j (1 : A) * T := hs
  have k0 : fam st u none * X = 0 := by
    rw [e0, Matrix.sub_mul, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, hLX, hTX]; simp
  have k1 : T * fam st u none = 0 := by
    rw [e0, Matrix.mul_sub, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hTY, hTX]; simp
  have l1 : ∀ (e : Matrix (Fin n) (Fin n) A) (j : Fin r), e * x * (X * single j j (1 : A) * L) =
      e * X * B * single j j (1 : A) * L := fun e j => by
    rw [Matrix.mul_assoc e X, ← eB]; simp only [Matrix.mul_assoc]
  have l2 : ∀ (e : Matrix (Fin n) (Fin n) A) (j : Fin r), (Y * single j j (1 : A) * T) * x * e =
      Y * single j j (1 : A) * C * (T * e) := fun e j => by
    rw [Matrix.mul_assoc _ T, eC]; simp only [Matrix.mul_assoc]
  have sm : ∀ (D : Matrix (Fin r) (Fin r) A) (i j : Fin r), D i j = 0 →
      single i i (1 : A) * D * single j j (1 : A) = 0 := fun D i j h => by
    rw [Matrix.single_mul_mul_single, h]; simp
  rintro (_ | i | i) (_ | j | j) hab
  · simp at hab
  · rw [e1, l1, k0]; simp
  · have := hd j; simp [wt] at hab; omega
  · have := hd i; simp [wt] at hab; omega
  · have h := sm B i j (hB i j (by simp [wt] at hab; omega))
    rw [e1, e1, l1, Matrix.mul_assoc _ L, hLX, Matrix.mul_one, Matrix.mul_assoc X, Matrix.mul_assoc X, h]; simp
  · have := hd i; have := hd j; simp [wt] at hab; omega
  · rw [e2, l2, k1]; simp
  · rw [e1, e2, l1, Matrix.mul_assoc _ T, hTX]; simp
  · have h := sm C i j (hC i j (by simp [wt] at hab; omega))
    rw [e2, e2, l2, ← Matrix.mul_assoc T, ← Matrix.mul_assoc T, hTY, Matrix.one_mul, ← Matrix.mul_assoc,
      Matrix.mul_assoc Y, Matrix.mul_assoc Y, h]; simp

theorem parFlag_no_lower : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E) (d : Fin r → ℕ) (M : ℕ), (∀ j, d j < M) → Formalism.UG.cT (σ : E →+* E) X * J * X = 0 → Formalism.UG.cT (σ : E →+* E) Y * J * Y = 0 → Formalism.UG.cT (σ : E →+* E) X * J * Y = 1 → ∀ p ∈ parFlag σ J X d, ∀ a b, wt d M a < wt d M b → fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J)) a * (matHom (AF F) σ J p).1 * fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J)) b = 0 := by
  intro F E _ _ _ _ _ σ hcm n J hJ r X Y d M hd hXX _ hXY p hp
  have hσ : ∀ x, σ (σ x) = x := sigma_sigma hcm
  have cc : ∀ {m q : Type} (A : Matrix m q E), cT (σ : E →+* E) (cT (σ : E →+* E) A) = A := fun A =>
    Matrix.ext fun i j => hσ _
  obtain ⟨⟨B, hB, eB⟩, B', hB', eB'⟩ := hp
  have eC := form_mul_of_mul_cols eB'
  rw [inv_inv] at eC
  have hLX : cT (σ : E →+* E) Y * J * X = 1 := by
    have := congrArg (cT (σ : E →+* E)) hXY
    rwa [cT_mul, cT_mul, cc, cT_form hJ, cT_one, ← Matrix.mul_assoc] at this
  refine abstract_no_lower _ _ (adMat F X) (adMat F Y) (adMat F (cT (σ : E →+* E) Y * J))
    (adMat F (cT (σ : E →+* E) X * J)) (fun j => idemA_eq _ _ j) (fun j => ?_) ?_ ?_ ?_ d M hd _ B _
    (fun i j h => hB h) (fun i j h => ?_) eB eC
  · have s : cT (σ : E →+* E) (single j j (1 : E) : Matrix (Fin r) (Fin r) E) = single j j 1 := by
      rw [cT, Matrix.map_single, Matrix.transpose_single, map_one]
    have e : J⁻¹ * cT (σ : E →+* E) (X * single j j (1 : E) * (cT (σ : E →+* E) Y * J)) * J =
        Y * single j j (1 : E) * (cT (σ : E →+* E) X * J) := by
      rw [cT_mul, cT_mul, cT_mul, cc, cT_form hJ, s, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
        Matrix.nonsing_inv_mul_cancel_left _ _ (det_isUnit hJ)]
      simp only [Matrix.mul_assoc]
    rw [idemA, adjA_map, e]
    exact idemA_eq Y _ j
  · rw [adMat, adMat, ← Matrix.map_mul, hLX, Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [adMat, adMat, ← Matrix.map_mul, hXX, Matrix.map_zero _ (map_zero _)]
  · rw [adMat, adMat, ← Matrix.map_mul, hXY, Matrix.map_one _ (map_zero _) (map_one _)]
  · show sigR (AF F) σ (B' j i) = 0
    rw [hB' h, map_zero]

end GlobalTheory.UAut.NoLower
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KltAtAddSmulOfLcAtStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kltAt_add_one_sub_smul_of_kltAt_of_lcAt : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Δ D : X → ℚ) (δ : ℚ) (x : X), IsQCart D → KltAt p n Δ x → LcAt p n (Δ + D) x → 0 < δ → δ ≤ 1 → KltAt p n (Δ + (1 - δ) • D) x := by
  first | exact @GlobalTheory.PairStep.kltAt_add_smul_of_lcAt | exact GlobalTheory.PairStep.kltAt_add_smul_of_lcAt | (intros; apply GlobalTheory.PairStep.kltAt_add_smul_of_lcAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KltAtLcAtOfLeCoeffStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kltAt_and_lcAt_antitone_coeff : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Γ B : X → ℚ) (a b : ℚ) (x : X), IsQCart B → a ≤ b → (KltAt p n (Γ + b • B) x → KltAt p n (Γ + a • B) x) ∧ (LcAt p n (Γ + b • B) x → LcAt p n (Γ + a • B) x) := by
  first | exact @GlobalTheory.PairStep.kltAt_lcAt_of_le_coeff | exact GlobalTheory.PairStep.kltAt_lcAt_of_le_coeff | (intros; apply GlobalTheory.PairStep.kltAt_lcAt_of_le_coeff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KudlaSplittingSplitUnitary
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory

theorem kudlaSplittingSplitUnitary : GlobalTheory.Published.KudlaSplittingSplitUnitary := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α ν _ _ _ _ Q hQ ψ hψ hψ1 hψne χ hχ hres
  letI : MeasurableSpace (Matrix α ν E) := borel _
  haveI : BorelSpace (Matrix α ν E) := ⟨rfl⟩
  obtain ⟨-, -, -, -, -, -, -, hmat⟩ := GlobalTheory.T.quadExt_topological_properties F E c δ hE
  obtain ⟨-, hG⟩ := hmat α ν
  haveI := hG.grp
  haveI := hG.t2
  haveI := hG.lc
  haveI := hG.sc
  obtain ⟨κ, ω, hKW⟩ := GlobalTheory.T.exists_weil_representation_split_unitary_schwartzBruhat F E c δ hE α ν Q hQ ψ hψ hψ1 hψne χ hχ hres (Measure.addHaar)
  refine ⟨ω, GlobalTheory.T.splitUnitaryWeilRepresentation_isSmooth F E c δ hE α ν Q hQ ψ hψ hψ1 hψne χ hχ hres _ κ ω hKW, ?_,
    GlobalTheory.T.weilRepresentation_intertwines_heisenberg F E c δ hE α ν Q hQ ψ hψ hψ1 hψne χ hχ hres _ κ ω hKW, ?_⟩
  · intro μ' hμ' g φ
    exact GlobalTheory.T.weil_representation_preserves_L2_space F E c δ hE α ν Q hQ ψ hψ hψ1 hψne χ hχ hres _ κ ω hKW μ' g φ
  · intro a φ x
    have hp : levi c hE.invol a ∈ sieg c ν := by
      rw [mem_sieg, mat, levi_val, toBlocks_fromBlocks₂₁]
    rw [hKW.par _ hp φ]
    have h0 : ∀ y : Matrix α ν E, pr c Q y 0 = 0 := fun y => by
      simp [pr, form, GlobalTheory.WeilM.hTens]
    obtain ⟨-, -, hsc, -⟩ := GlobalTheory.T.unitaryCharacterAbsScalar_basic_properties F E c δ hE (Fintype.card α) χ hres
    have hd := hsc (Matrix.GeneralLinearGroup.det a)
    rw [Matrix.GeneralLinearGroup.val_det_apply] at hd
    simp only [parFun, mat, levi_val, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, Matrix.mul_zero, h0,
      mul_zero, AddChar.map_zero_eq_one, one_mul, hd]

end GlobalTheory
end

