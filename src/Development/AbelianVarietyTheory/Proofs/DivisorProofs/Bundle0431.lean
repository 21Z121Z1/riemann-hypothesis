import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0065
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocalRingOfIdem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0062
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0163
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0134
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0096
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0408
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0296
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0341
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0359
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0342
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0339
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0419
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0356
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0388
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0412
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnramifiedEmbeddingOfInvolutionAlgebra
section
noncomputable section

namespace GlobalTheory.UnitLemma.UnrAny

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial IsLocalRing

theorem pow_eq_one_eq_of_residue {S : Type*} [CommRing S] [IsLocalRing S] {n : ℕ} (hn : IsUnit (n : S))
    {y₁ y₂ : S} (h₁ : y₁ ^ n = 1) (h₂ : y₂ ^ n = 1) (h : residue S y₁ = residue S y₂) : y₁ = y₂ := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hn
  have key : (∑ i ∈ Finset.range n, y₁ ^ i * y₂ ^ (n - 1 - i)) * (y₁ - y₂) = 0 := by
    rw [Commute.geom_sum₂_mul (Commute.all _ _), h₁, h₂, sub_self]
  have hr : residue S (∑ i ∈ Finset.range n, y₁ ^ i * y₂ ^ (n - 1 - i)) =
      (n : ResidueField S) * residue S y₂ ^ (n - 1) := by
    rw [map_sum]
    simp only [map_mul, map_pow, h]
    rw [Finset.sum_congr rfl (g := fun _ => residue S y₂ ^ (n - 1)), Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    intro i hi
    rw [← pow_add]
    congr 1
    have := Finset.mem_range.1 hi
    omega
  have hu : IsUnit (∑ i ∈ Finset.range n, y₁ ^ i * y₂ ^ (n - 1 - i)) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, hr]
    refine mul_ne_zero ?_ (pow_ne_zero _ ?_)
    · simpa using (hn.map (residue S)).ne_zero
    · intro h0
      have := congrArg (residue S) h₂
      rw [map_pow, h0, zero_pow hn0, map_one] at this
      exact zero_ne_one this
  have := (hu.mul_right_eq_zero).1 key
  exact sub_eq_zero.1 this

theorem card_sub_one_isUnit (S : Type*) [CommRing S] [IsLocalRing S] [Finite (ResidueField S)] :
    IsUnit ((Nat.card (ResidueField S) - 1 : ℕ) : S) := by
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_natCast, Nat.cast_sub Nat.card_pos, Nat.cast_one]
  haveI := Fintype.ofFinite (ResidueField S)
  rw [Nat.card_eq_fintype_card, FiniteField.cast_card_eq_zero]
  simp

theorem exists_unr_embedding_any : ∀ (K : UQ) (B : InvAlg K), B.g * B.σ B.g = 1 → B.P.Separable → IsIntegral K.O B.g → ∀ (hl : IsLocalRing (Algebra.adjoin K.O ({B.g} : Set B.A))) (d : ℕ), Nat.card (@IsLocalRing.ResidueField (Algebra.adjoin K.O ({B.g} : Set B.A)) _ hl) = K.q ^ (2 * d) → ∀ (K' : UQ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → (∃ z : K'.E, IsPrimitiveRoot z (K'.q ^ 2 - 1) ∧ @Algebra.adjoin K.E K'.E _ _ φ.toAlgebra {z} = ⊤) → ∃ (ψ : K'.E →+* B.A) (_ : ∀ e, ψ (φ e) = algebraMap K.E B.A e) (_ : ∀ e, B.σ (ψ e) = ψ (K'.c e)) (hO : ∀ y : K'.O, ψ (algebraMap K'.O K'.E y) ∈ Algebra.adjoin K.O ({B.g} : Set B.A)), ∃ s : K'.Oˣ, algebraMap K'.O K'.E s * K'.c (algebraMap K'.O K'.E s) = 1 ∧ @IsLocalRing.residue _ _ hl ⟨B.g, Algebra.self_mem_adjoin_singleton K.O B.g⟩ = @IsLocalRing.residue _ _ hl ⟨ψ (algebraMap K'.O K'.E s), hO s⟩ := by
  intro K B hu _ hi hl d hcard K' φ hU hz
  obtain ⟨z, hzp, hzadj⟩ := hz
  set R := Algebra.adjoin K.O ({B.g} : Set B.A) with hR
  have hq0 : K.q ≠ 0 := by
    intro h0
    have : 0 < Nat.card (ResidueField K.O) := Nat.card_pos
    rw [K.card_res, h0] at this
    simp at this
  have hq' : K'.q = K.q ^ d := hU.1
  set N := K'.q ^ 2 - 1 with hNdef
  have hcardR : Nat.card (ResidueField R) = K'.q ^ 2 := by rw [hcard, hq', ← pow_mul, mul_comm]
  have hd : d ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hq'
    rw [hq', one_pow] at hcardR
    have : Subsingleton (ResidueField R) := (Nat.card_eq_one_iff_unique.1 hcardR).1
    exact not_subsingleton (ResidueField R) this
  haveI : Finite (ResidueField R) := Nat.finite_of_card_ne_zero (by rw [hcardR, hq']; exact pow_ne_zero _ (pow_ne_zero _ hq0))

  haveI : Module.Finite K.O R := Algebra.finite_adjoin_simple_of_isIntegral hi
  haveI : HenselianLocalRing K.O := GlobalTheory.henselianLocalRing_of_henselianRing K.O
  haveI : HenselianLocalRing R := GlobalTheory.henselianLocalRing_of_finite K.O R
  have h1q : 1 < K'.q ^ 2 := by rw [← K'.card_res]; exact Finite.one_lt_card
  have hN : N ≠ 0 := by omega
  have hNR : IsUnit (N : R) := by
    have := card_sub_one_isUnit R
    rwa [hcardR] at this
  letI : Algebra K.E K'.E := φ.toAlgebra
  letI : Algebra K.O K'.E := (φ.comp (algebraMap K.O K.E)).toAlgebra
  haveI : IsScalarTower K.O K.E K'.E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : FaithfulSMul K.O K'.E := (faithfulSMul_iff_algebraMap_injective _ _).2
    (φ.injective.comp (IsFractionRing.injective K.O K.E))
  have hzN : z ^ N = 1 := hzp.pow_eq_one
  have hzint : IsIntegral K.O z :=
    ⟨_, monic_X_pow_sub_C (1 : K.O) hN, by rw [← aeval_def]; simp [hzN]⟩
  have hmdvd : minpoly K.O z ∣ X ^ N - C 1 := minpoly.isIntegrallyClosed_dvd hzint (by simp [hzN])
  obtain ⟨yR, hyR⟩ := GlobalTheory.T.exists_root_of_monic_dvd_X_pow_card_sub_one R ((minpoly K.O z).map (algebraMap K.O R))
    ((minpoly.monic hzint).map _)
    (by rw [(minpoly.monic hzint).natDegree_map]; exact (minpoly.natDegree_pos hzint).ne')
    (by
      rw [hcardR]
      have := Polynomial.map_dvd (algebraMap K.O R) hmdvd
      simpa using this)
  have hyN : yR ^ N = 1 := by
    obtain ⟨h, hh⟩ := hmdvd
    have := congrArg (fun p => (p.map (algebraMap K.O R)).eval yR) hh
    simp only [Polynomial.map_mul, eval_mul, hyR, zero_mul] at this
    simpa [sub_eq_zero] using this

  have hzE : IsIntegral K.E z := hzint.tower_top
  let pb := PowerBasis.ofAdjoinEqTop hzE hzadj
  have hgen : pb.gen = z := rfl
  have hy : aeval (yR : B.A) (minpoly K.E pb.gen) = 0 := by
    rw [hgen, minpoly.isIntegrallyClosed_eq_field_fractions' K.E hzint, aeval_map_algebraMap,
      ← Polynomial.aeval_subalgebra_coe, aeval_def, ← eval_map, hyR]
    rfl
  let ψ : K'.E →+* B.A := (pb.lift (yR : B.A) hy).toRingHom
  have hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e := fun e => (pb.lift (yR : B.A) hy).commutes e
  have hψz : ψ z = yR := pb.lift_gen _ hy
  haveI : Nontrivial B.A := nontrivial_of_ne (0 : B.A) 1 fun h => zero_ne_one (Subtype.ext h : (0 : R) = 1)
  have hψi : Function.Injective ψ := ψ.injective

  let τR : R →+* R := (B.σ : B.A →+* B.A).restrict R R fun x hx => Orbit.adjoin_stable B hu hi hx
  have hτR : ∀ x : R, (τR x : B.A) = B.σ x := fun x => rfl
  have hτ2 : ∀ x, τR (τR x) = x := fun x => Subtype.ext (B.σ_σ x)
  obtain ⟨a, b, hab, hres⟩ := K.c_res
  have hτa : τR (algebraMap K.O R a) = algebraMap K.O R b := by
    apply Subtype.ext
    rw [hτR]
    change B.σ (algebraMap K.O B.A a) = algebraMap K.O B.A b
    rw [IsScalarTower.algebraMap_apply K.O K.E B.A, B.σ_alg, hab, ← IsScalarTower.algebraMap_apply]
  have hne : residue R (τR (algebraMap K.O R a)) ≠ residue R (algebraMap K.O R a) := by
    rw [hτa]
    intro h
    have h2 : residue R (algebraMap K.O R (a - b)) = 0 := by rw [map_sub, map_sub, h, sub_self]
    rw [IsLocalRing.residue_eq_zero_iff] at h2
    have hu' : IsUnit (a - b) := by
      by_contra hc
      exact hres ((IsLocalRing.mem_maximalIdeal _).2 hc)
    exact (IsLocalRing.mem_maximalIdeal _).1 h2 (hu'.map _)
  obtain ⟨hfr1, hfr2⟩ := GlobalTheory.T.involution_residue_pow_and_roots_of_unity R K'.q hcardR τR hτ2 ⟨_, hne⟩
  choose τ' hτ' using K'.c_int
  have hinj' : Function.Injective (algebraMap K'.O K'.E) := IsFractionRing.injective _ _
  let cO : K'.O →+* K'.O :=
    { toFun := τ'
      map_one' := hinj' (by rw [← hτ']; simp)
      map_mul' := fun a b => hinj' (by simp [← hτ'])
      map_zero' := hinj' (by rw [← hτ']; simp)
      map_add' := fun a b => hinj' (by simp [← hτ']) }
  have hcO : ∀ x, algebraMap K'.O K'.E (cO x) = K'.c (algebraMap K'.O K'.E x) := fun x => (hτ' x).symm
  have hc2 : ∀ x, cO (cO x) = x := fun x => hinj' (by rw [hcO, hcO, K'.c_c])
  obtain ⟨a', b', hab', hres'⟩ := K'.c_res
  have hne' : residue K'.O (cO a') ≠ residue K'.O a' := by
    have : cO a' = b' := hinj' (by rw [hcO, hab'])
    rw [this]
    intro h
    apply hres'
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, h, sub_self]
  obtain ⟨-, hfc⟩ := GlobalTheory.T.involution_residue_pow_and_roots_of_unity K'.O K'.q K'.card_res cO hc2 ⟨_, hne'⟩
  obtain ⟨zO, hzO⟩ : ∃ zO : K'.O, algebraMap K'.O K'.E zO = z :=
    IsIntegrallyClosed.isIntegral_iff.1
      ⟨_, monic_X_pow_sub_C (1 : K'.O) hN, by rw [← aeval_def]; simp [hzN]⟩
  have hzON : zO ^ N = 1 := hinj' (by rw [map_pow, hzO, hzN, map_one])
  have hcz : K'.c z = z ^ K'.q := by
    rw [← hzO, ← hcO, hfc zO hzON, map_pow]
  have hσz : B.σ (ψ z) = ψ (K'.c z) := by
    rw [hψz, ← hτR, hfr2 yR hyN, hcz, map_pow, hψz]
    rfl
  have hσ : ∀ e, B.σ (ψ e) = ψ (K'.c e) := by
    intro e
    have he : e ∈ @Algebra.adjoin K.E K'.E _ _ φ.toAlgebra {z} := hzadj ▸ Algebra.mem_top
    induction he using Algebra.adjoin_induction with
    | mem x hx => rw [Set.mem_singleton_iff.1 hx]; exact hσz
    | algebraMap e =>
      change B.σ (ψ (φ e)) = ψ (K'.c (φ e))
      rw [← hU.2.1, hψ, hψ, B.σ_alg]
    | add x y _ _ hx hy => simp only [map_add, hx, hy]
    | mul x y _ _ hx hy => simp only [map_mul, hx, hy]

  have hO : ∀ y : K'.O, ψ (algebraMap K'.O K'.E y) ∈ R := by
    intro y
    have hadj := GlobalTheory.T.adjoin_primitiveRoot_eq_integers_unramifiedQuadratic K K' d φ hU hd z hzp hzadj _ (GlobalTheory.T.isIntegral_integers_unramifiedInvolutionExt K K' d φ hU hd y)
    generalize algebraMap K'.O K'.E y = x at hadj ⊢
    induction hadj using Algebra.adjoin_induction with
    | mem x hx => rw [Set.mem_singleton_iff.1 hx, hψz]; exact yR.2
    | algebraMap a =>
      change ψ (φ (algebraMap K.O K.E a)) ∈ R
      rw [hψ, ← IsScalarTower.algebraMap_apply]
      exact Subalgebra.algebraMap_mem _ _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  refine ⟨ψ, hψ, hσ, hO, ?_⟩
  haveI : NeZero N := ⟨hN⟩
  have hcoe : ∀ n : ℕ, ((yR ^ n : R) : B.A) = ψ (z ^ n) := fun n => by rw [map_pow, hψz]; rfl
  have hwp : IsPrimitiveRoot (residue R yR) N := by
    refine ⟨by rw [← map_pow, hyN, map_one], fun l hl => hzp.dvd_of_pow_eq_one l ?_⟩
    have h1 : yR ^ l = 1 := pow_eq_one_eq_of_residue hNR
      (by rw [← pow_mul, mul_comm, pow_mul, hyN, one_pow]) (one_pow N) (by rw [map_pow, hl, map_one])
    apply hψi
    rw [← hcoe, h1, map_one]
    rfl
  set gR : R := ⟨B.g, Algebra.self_mem_adjoin_singleton K.O B.g⟩ with hgR
  have hgu : gR * τR gR = 1 := Subtype.ext hu
  have hg0 : residue R gR ≠ 0 := (IsUnit.map (residue R) (⟨⟨gR, τR gR, hgu, by rw [mul_comm]; exact hgu⟩, rfl⟩ : IsUnit gR)).ne_zero
  have hgN : residue R gR ^ N = 1 := by
    haveI := Fintype.ofFinite (ResidueField R)
    have := FiniteField.pow_card_sub_one_eq_one _ hg0
    rwa [← Nat.card_eq_fintype_card, hcardR] at this
  obtain ⟨j, -, hj⟩ := hwp.eq_pow_of_pow_eq_one hgN
  let zOu : K'.Oˣ := Units.ofPowEqOne zO N hzON hN
  have hs : algebraMap K'.O K'.E ((zOu ^ j : K'.Oˣ) : K'.O) = z ^ j := by
    rw [Units.val_pow_eq_pow_val, map_pow, Units.val_ofPowEqOne, hzO]
  refine ⟨zOu ^ j, ?_, ?_⟩
  · set e := j + j * K'.q with he
    have hres : residue R (yR ^ e) = 1 := by
      rw [map_pow, he, pow_add, pow_mul, hj, ← hfr1 gR, ← map_mul, hgu, map_one]
    have hye : yR ^ e = 1 := pow_eq_one_eq_of_residue hNR
      (by rw [← pow_mul, mul_comm, pow_mul, hyN, one_pow]) (one_pow N) (by rw [hres, map_one])
    rw [hs, map_pow, hcz, ← pow_mul, ← pow_add, mul_comm K'.q j, ← he]
    apply hψi
    rw [← hcoe, hye, map_one]
    rfl
  · have : (⟨ψ (algebraMap K'.O K'.E ((zOu ^ j : K'.Oˣ) : K'.O)), hO _⟩ : R) = yR ^ j :=
      Subtype.ext (by
        change ψ (algebraMap K'.O K'.E ((zOu ^ j : K'.Oˣ) : K'.O)) = ((yR ^ j : R) : B.A)
        rw [hs, hcoe])
    rw [this, map_pow, hj]

end GlobalTheory.UnitLemma.UnrAny
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreZeroMemCoinvariantsStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_zero_mem_coinvariants : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (a b : ℕ) (ν β : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν → GlobalTheory.SmGL.IsSmoothChar β → ∀ Φ ∈ GlobalTheory.RankFibre.fullRankSB k a (a + b), GlobalTheory.RankFibre.fibre ν β a b Φ = 0 → Φ ∈ GlobalTheory.RankFibre.coinv ν β a (a + b) := by
  first | exact @GlobalTheory.RankFibreKer.fibre_ker | exact GlobalTheory.RankFibreKer.fibre_ker | (intros; apply GlobalTheory.RankFibreKer.fibre_ker <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitaryOfLocallyBijectiveFromFilteredFunctor
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.FinitaryOfLocBij

variable {R : Type} [CommRing R]

lemma etale_inr {A B C P : CommRingCat.{0}} {g : A ⟶ B} {f : A ⟶ C} {inl : B ⟶ P}
    {inr : C ⟶ P} (sq : IsPushout g f inl inr) (hg : g.hom.Etale) : inr.hom.Etale := by
  have : (RingHom.toMorphismProperty @RingHom.Etale).IsStableUnderCobaseChange :=
    RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.2 RingHom.Etale.isStableUnderBaseChange
  exact MorphismProperty.of_isPushout (P := RingHom.toMorphismProperty @RingHom.Etale) sq.flip hg

lemma cover_inr {ι : Type} {A C : CommRingCat.{0}} {B P : ι → CommRingCat.{0}}
    (g : ∀ i, A ⟶ B i) (f : A ⟶ C) (inl : ∀ i, B i ⟶ P i) (inr : ∀ i, C ⟶ P i)
    (sq : ∀ i, IsPushout (g i) f (inl i) (inr i))
    (hcov : ∀ p : Spec A, ∃ i v, Spec.map (g i) v = p) :
    ∀ p : Spec C, ∃ i v, Spec.map (inr i) v = p := by
  intro p
  obtain ⟨i, v, hv⟩ := hcov (Spec.map f p)
  obtain ⟨z, hz⟩ := GlobalTheory.EtaleCoverDescent.exists_point_of_isPushout (sq i).flip p v hv.symm
  exact ⟨i, z, hz⟩

lemma eta_map {M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)} {F : Shv R}
    (η : M ⟶ onRings F) {A B : CommRingCat.{0}} (f : A ⟶ B) (x : M.obj A) :
    ((onRings F).map f).hom ((η.app A).hom x) = (η.app B).hom ((M.map f).hom x) := by
  change (η.app A ≫ (onRings F).map f).hom x = (M.map f ≫ η.app B).hom x
  rw [η.naturality]

lemma map_comp_apply (N : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) {A B C : CommRingCat.{0}}
    (f : A ⟶ B) (g : B ⟶ C) (x : N.obj A) :
    (N.map (f ≫ g)).hom x = (N.map g).hom ((N.map f).hom x) := by
  rw [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

lemma isPushout_pushouts {C : Type*} [Category C] {A C₁ C₂ X B₁ B₂ P Q : C} {u₁ : A ⟶ C₁}
    {u₂ : A ⟶ C₂} {f : A ⟶ X} {i₁ : C₁ ⟶ B₁} {g₁ : X ⟶ B₁} {i₂ : C₂ ⟶ B₂} {g₂ : X ⟶ B₂}
    {p₁ : C₁ ⟶ P} {p₂ : C₂ ⟶ P} {q₁ : B₁ ⟶ Q} {q₂ : B₂ ⟶ Q} {w : P ⟶ Q}
    (h₁ : IsPushout u₁ f i₁ g₁) (h₂ : IsPushout u₂ f i₂ g₂) (hP : IsPushout u₁ u₂ p₁ p₂)
    (hQ : IsPushout g₁ g₂ q₁ q₂) (e₁ : p₁ ≫ w = i₁ ≫ q₁) (e₂ : p₂ ≫ w = i₂ ≫ q₂) :
    IsPushout (u₁ ≫ p₁) f w (g₁ ≫ q₁) := by
  have s : IsPushout u₂ (u₁ ≫ i₁) (p₂ ≫ w) q₁ := by
    rw [h₁.w, e₂]; exact h₂.paste_vert hQ.flip
  have t : IsPushout p₁ i₁ w q₁ := IsPushout.of_top s e₁ hP.flip
  exact h₁.paste_horiz t

lemma glue (F : Shv R) {ι : Type} {A : CommRingCat.{0}} {C : ι → CommRingCat.{0}}
    (e : ∀ i, A ⟶ C i) (he : ∀ i, (e i).hom.Etale)
    (hcov : ∀ p : Spec A, ∃ i v, Spec.map (e i) v = p) (s : ∀ i, (onRings F).obj (C i))
    (hs : ∀ a b, ((onRings F).map (pushout.inl (e a) (e b))).hom (s a) =
      ((onRings F).map (pushout.inr (e a) (e b))).hom (s b)) :
    ∃ y : (onRings F).obj A, ∀ i, ((onRings F).map (e i)).hom y = s i := by
  refine (GlobalTheory.EtC.sec_sep_glue_of_points R F (Spec A) ι (fun i => Spec (C i)) (fun i => Spec.map (e i))
    (fun i => (HasRingHomProperty.Spec_iff (P := @Etale)).mpr (he i)) hcov).2 s ?_
  intro a b
  have H := isPullback_SpecMap_pushout (e a) (e b)
  have h1 : pullback.fst (Spec.map (e a)) (Spec.map (e b)) =
      H.isoPullback.inv ≫ Spec.map (pushout.inl (e a) (e b)) := by simp
  have h2 : pullback.snd (Spec.map (e a)) (Spec.map (e b)) =
      H.isoPullback.inv ≫ Spec.map (pushout.inr (e a) (e b)) := by simp
  have := congrArg (fun z => (F.obj.map H.isoPullback.inv.op).hom z) (hs a b)
  simp only [Sec.res, h1, h2, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
  exact this

lemma sep (F : Shv R) {ι : Type} {A : CommRingCat.{0}} {C : ι → CommRingCat.{0}}
    (e : ∀ i, A ⟶ C i) (he : ∀ i, (e i).hom.Etale)
    (hcov : ∀ p : Spec A, ∃ i v, Spec.map (e i) v = p) (y z : (onRings F).obj A)
    (h : ∀ i, ((onRings F).map (e i)).hom y = ((onRings F).map (e i)).hom z) : y = z := by
  rw [← sub_eq_zero]
  refine (GlobalTheory.EtC.sec_sep_glue_of_points R F (Spec A) ι (fun i => Spec (C i)) (fun i => Spec.map (e i))
    (fun i => (HasRingHomProperty.Spec_iff (P := @Etale)).mpr (he i)) hcov).1 _ ?_
  intro i
  change ((onRings F).map (e i)).hom (y - z) = 0
  rw [map_sub, h i, sub_self]

end GlobalTheory.EtC.FinitaryOfLocBij

namespace GlobalTheory.EtC.FinitaryOfLocBij

variable {R : Type} [CommRing R]

lemma cocone_nat {C : Type} [Category C] {D' : C ⥤ CommRingCat.{0}} {B : CommRingCat.{0}}
    (ιB : D' ⟶ (Functor.const C).obj B) {K K' : C} (φ : K ⟶ K') :
    D'.map φ ≫ ιB.app K' = ιB.app K := by
  simpa using ιB.naturality φ

lemma po_stage {J : Type} [SmallCategory J] {D : J ⥤ CommRingCat.{0}} {j : J} {B' : CommRingCat.{0}}
    {g' : D.obj j ⟶ B'} {D' : Under j ⥤ CommRingCat.{0}} {u : Under.forget j ⋙ D ⟶ D'}
    {v : (Functor.const _).obj B' ⟶ D'} (hpo : ∀ k, IsPushout g' (D.map k.hom) (v.app k) (u.app k))
    {K K' : Under j} (φ : K ⟶ K') :
    IsPushout (u.app K) (D.map φ.right) (D'.map φ) (u.app K') := by
  have hv : v.app K ≫ D'.map φ = v.app K' := by simpa using (v.naturality φ).symm
  have e1 : D.map K.hom ≫ D.map φ.right = D.map K'.hom := by rw [← Functor.map_comp, Under.w φ]
  have s : IsPushout g' (D.map K.hom ≫ D.map φ.right) (v.app K ≫ D'.map φ) (u.app K') := by
    rw [e1, hv]; exact hpo K'
  exact IsPushout.of_top s (u.naturality φ).symm (hpo K)

lemma po_colim {J : Type} [SmallCategory J] {D : J ⥤ CommRingCat.{0}} {c : Cocone D} {j : J}
    {B' B : CommRingCat.{0}} {g' : D.obj j ⟶ B'} {h : B' ⟶ B} {g : c.pt ⟶ B}
    (hbig : IsPushout g' (c.ι.app j) h g) {D' : Under j ⥤ CommRingCat.{0}}
    {ιB : D' ⟶ (Functor.const _).obj B} {u : Under.forget j ⋙ D ⟶ D'}
    {v : (Functor.const _).obj B' ⟶ D'} (k : Under j)
    (hk : IsPushout g' (D.map k.hom) (v.app k) (u.app k) ∧ v.app k ≫ ιB.app k = h ∧
      u.app k ≫ ιB.app k = c.ι.app k.right ≫ g) :
    IsPushout (u.app k) (c.ι.app k.right) (ιB.app k) g := by
  have e1 : D.map k.hom ≫ c.ι.app k.right = c.ι.app j := c.w k.hom
  rw [← e1, ← hk.2.1] at hbig
  exact IsPushout.of_top hbig hk.2.2 hk.1

theorem surj (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) (F : Shv R) (η : M ⟶ onRings F)
    (hM : PreservesFilteredColimitsOfSize.{0, 0} M)
    (hloc : ∀ (A : CommRingCat.{0}) (x : (onRings F).obj A), ∃ (ι : Type) (_ : Finite ι) (B : ι → CommRingCat.{0}) (g : ∀ i, A ⟶ B i) (m : ∀ i, M.obj (B i)), (∀ i, (g i).hom.Etale) ∧ (∀ p : Spec A, ∃ i v, Spec.map (g i) v = p) ∧ ∀ i, (η.app (B i)).hom (m i) = ((onRings F).map (g i)).hom x)
    (hinj : ∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ (j : J) (y : (onRings F).obj (D.obj j)), ((onRings F).map (c.ι.app j)).hom y = 0 → ∃ (k : J) (f : j ⟶ k), ((onRings F).map (D.map f)).hom y = 0)
    (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D)
    (hc : IsColimit c) (x : (onRings F).obj c.pt) :
    ∃ (j : J) (y : (onRings F).obj (D.obj j)), ((onRings F).map (c.ι.app j)).hom y = x := by
  classical
  obtain ⟨ι, _, B, g, m, hg, hcov, hm⟩ := hloc _ x
  have hMel := (GlobalTheory.EtC.FilteredElements.preservesFilteredColimits_modules_iff_elements _ M).2.1 hM
  obtain ⟨j0⟩ := IsFiltered.nonempty (C := J)
  obtain ⟨j, -, B', g', h, hsq, hcov'⟩ :=
    GlobalTheory.EtaleCoverDescent.exists_etale_cover_model_of_isColimit J D c hc ι B g hg hcov j0
  choose D' ιB u v hcol hpush using fun i =>
    GlobalTheory.BaseChangeColim.exists_isColimit_pushout_under J D c hc j (B' i) (B i) (g' i) (h i) (g i)
      (hsq i).2
  have hlift : ∀ i, ∃ k : Under j, ∃ n : M.obj ((D' i).obj k), (M.map ((ιB i).app k)).hom n = m i :=
    fun i => (hMel (Under j) (D' i) _ (hcol i).some).1 (m i)
  choose k n hn using hlift
  letI := Fintype.ofFinite ι
  obtain ⟨K, hK⟩ := IsFiltered.sup_objs_exists (Finset.univ.image k)
  have e : ∀ i, k i ⟶ K := fun i => (hK (Finset.mem_image_of_mem _ (Finset.mem_univ i))).some
  let s : ∀ i, (onRings F).obj ((D' i).obj K) :=
    fun i => (η.app _).hom ((M.map ((D' i).map (e i))).hom (n i))
  have hs : ∀ i, ((onRings F).map ((ιB i).app K)).hom (s i) = ((onRings F).map (g i)).hom x := by
    intro i
    simp only [s]
    rw [eta_map, ← map_comp_apply, cocone_nat, hn]
    exact hm i
  let Kp : Under K.right → Under j := fun L => Under.mk (K.hom ≫ L.hom)
  let φ : ∀ L : Under K.right, K ⟶ Kp L := fun L => Under.homMk L.hom
  let s' : ∀ (L : Under K.right) i, (onRings F).obj ((D' i).obj (Kp L)) :=
    fun L i => ((onRings F).map ((D' i).map (φ L))).hom (s i)
  have hover : ∀ a b : ι, ∃ L0 : Under K.right, ∀ (L : Under K.right) (_ : L0 ⟶ L),
      ((onRings F).map (pushout.inl ((u a).app (Kp L)) ((u b).app (Kp L)))).hom (s' L a) =
      ((onRings F).map (pushout.inr ((u a).app (Kp L)) ((u b).app (Kp L)))).hom (s' L b) := by
    intro a b
    let w : pushout ((u a).app K) ((u b).app K) ⟶ pushout (g a) (g b) :=
      pushout.desc ((ιB a).app K ≫ pushout.inl (g a) (g b)) ((ιB b).app K ≫ pushout.inr (g a) (g b))
        (by
          have hua : ∀ i, (u i).app K ≫ (ιB i).app K = c.ι.app K.right ≫ g i := fun i => (hpush i K).2.2
          rw [reassoc_of% (hua a), reassoc_of% (hua b)]
          exact (Category.assoc _ _ _).trans ((c.ι.app K.right ≫= pushout.condition).trans
            (Category.assoc _ _ _).symm))
    let t : (onRings F).obj (pushout ((u a).app K) ((u b).app K)) :=
      ((onRings F).map (pushout.inl _ _)).hom (s a) - ((onRings F).map (pushout.inr _ _)).hom (s b)
    have ht : ((onRings F).map w).hom t = 0 := by
      simp only [t, map_sub, ← map_comp_apply, w, pushout.inl_desc, pushout.inr_desc]
      rw [map_comp_apply _ ((ιB a).app K), map_comp_apply _ ((ιB b).app K), hs, hs,
        ← map_comp_apply, ← map_comp_apply, pushout.condition, sub_self]
    have hPO : IsPushout ((u a).app K ≫ pushout.inl _ _) (c.ι.app K.right) w
        (g a ≫ pushout.inl (g a) (g b)) :=
      isPushout_pushouts (po_colim (hsq a).2 K (hpush a K)) (po_colim (hsq b).2 K (hpush b K))
        (IsPushout.of_hasPushout _ _) (IsPushout.of_hasPushout _ _) (pushout.inl_desc _ _ _)
        (pushout.inr_desc _ _ _)
    obtain ⟨D'', ι'', u'', v'', hcol'', hpush''⟩ :=
      GlobalTheory.BaseChangeColim.exists_isColimit_pushout_under J D c hc K.right _ _ _ w _ hPO
    let k0 : Under K.right := Under.mk (𝟙 _)
    have h0 : ((onRings F).map (ι''.app k0)).hom (((onRings F).map (v''.app k0)).hom t) = 0 := by
      rw [← map_comp_apply, (hpush'' k0).2.1, ht]
    obtain ⟨L0, f, hf⟩ := hinj (Under K.right) D'' _ hcol''.some k0 _ h0
    refine ⟨L0, fun L ψ => ?_⟩
    have hvL : ((onRings F).map (v''.app L)).hom t = 0 := by
      have e1 : v''.app k0 ≫ D''.map f ≫ D''.map ψ = v''.app L := by
        rw [← D''.map_comp]
        simpa using (v''.naturality (f ≫ ψ)).symm
      rw [← e1, map_comp_apply, map_comp_apply, hf, map_zero]
    let w' : pushout ((u a).app K) ((u b).app K) ⟶ pushout ((u a).app (Kp L)) ((u b).app (Kp L)) :=
      pushout.desc ((D' a).map (φ L) ≫ pushout.inl _ _) ((D' b).map (φ L) ≫ pushout.inr _ _)
        (by
          rw [← Category.assoc, ← Category.assoc, ← (u a).naturality, ← (u b).naturality]
          simp only [Category.assoc, pushout.condition])
    have hPO' : IsPushout ((u a).app K ≫ pushout.inl _ _) (D.map L.hom) w'
        ((u a).app (Kp L) ≫ pushout.inl _ _) :=
      isPushout_pushouts (po_stage (fun k => (hpush a k).1) (φ L))
        (po_stage (fun k => (hpush b k).1) (φ L))
        (IsPushout.of_hasPushout _ _) (IsPushout.of_hasPushout _ _) (pushout.inl_desc _ _ _)
        (pushout.inr_desc _ _ _)
    have hw' : v''.app L ≫ ((hpush'' L).1.isoIsPushout _ _ hPO').hom = w' :=
      IsPushout.inl_isoIsPushout_hom _ _ (hpush'' L).1 hPO'
    have hwt : ((onRings F).map w').hom t = 0 := by
      rw [← hw', map_comp_apply, hvL, map_zero]
    simp only [t, map_sub, sub_eq_zero, ← map_comp_apply, w', pushout.inl_desc,
      pushout.inr_desc] at hwt
    simpa only [s', ← map_comp_apply] using hwt
  choose L0 hL0 using hover
  obtain ⟨Lc, hLc⟩ := IsFiltered.sup_objs_exists (Finset.univ.image (fun p : ι × ι => L0 p.1 p.2))
  have ψ : ∀ a b, L0 a b ⟶ Lc := fun a b =>
    (hLc (Finset.mem_image_of_mem (fun p : ι × ι => L0 p.1 p.2) (Finset.mem_univ (a, b)))).some
  let e' : ∀ i, D.obj Lc.right ⟶ (D' i).obj (Kp Lc) := fun i => (u i).app (Kp Lc)
  obtain ⟨y, hy⟩ := glue F e'
    (fun i => etale_inr (hpush i (Kp Lc)).1 (hsq i).1)
    (cover_inr g' (D.map (Kp Lc).hom) (fun i => (v i).app (Kp Lc)) e'
      (fun i => (hpush i _).1) hcov')
    (s' Lc) (fun a b => hL0 a b Lc (ψ a b))
  refine ⟨Lc.right, y, ?_⟩
  apply sep F g hg hcov
  intro i
  have hu : e' i ≫ (ιB i).app (Kp Lc) = c.ι.app Lc.right ≫ g i := (hpush i _).2.2
  rw [← map_comp_apply, ← hu, map_comp_apply, hy i]
  simp only [s']
  rw [← map_comp_apply, cocone_nat, hs]

end GlobalTheory.EtC.FinitaryOfLocBij

namespace GlobalTheory.EtC.FinitaryOfLocBij

theorem finitary_of_locally_bijective : ∀ (R : Type) [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) (F : Shv R) (η : M ⟶ onRings F), PreservesFilteredColimitsOfSize.{0, 0} M → (∀ (A : CommRingCat.{0}) (x : (onRings F).obj A), ∃ (ι : Type) (_ : Finite ι) (B : ι → CommRingCat.{0}) (g : ∀ i, A ⟶ B i) (m : ∀ i, M.obj (B i)), (∀ i, (g i).hom.Etale) ∧ (∀ p : Spec A, ∃ i v, Spec.map (g i) v = p) ∧ ∀ i, (η.app (B i)).hom (m i) = ((onRings F).map (g i)).hom x) → (∀ (A : CommRingCat.{0}) (m : M.obj A), (η.app A).hom m = 0 → ∃ (ι : Type) (_ : Finite ι) (B : ι → CommRingCat.{0}) (g : ∀ i, A ⟶ B i), (∀ i, (g i).hom.Etale) ∧ (∀ p : Spec A, ∃ i v, Spec.map (g i) v = p) ∧ ∀ i, (M.map (g i)).hom m = 0) → Finitary F := by
  intro R _ M F η hM hloc hker
  have hinj := GlobalTheory.T.sheafSection_eq_zero_at_stage_of_filtered_colimit R M F η hM hloc hker
  show PreservesFilteredColimitsOfSize.{0, 0} (onRings F)
  refine (GlobalTheory.EtC.FilteredElements.preservesFilteredColimits_modules_iff_elements _ (onRings F)).2.2 ?_
  intro J _ _ D c hc
  exact ⟨surj M F η hM hloc hinj J D c hc, hinj J D c hc⟩

end GlobalTheory.EtC.FinitaryOfLocBij
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAlgebraStrictlyHenselianInductionStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteAlgebra_strictlyHenselian_induction : ∀ (A : Type) [CommRing A], SH A → ∀ (P : ∀ (T : Type) [CommRing T] [Algebra A T], Prop),
  (∀ (T T' : Type) [CommRing T] [CommRing T'] [Algebra A T] [Algebra A T'], (T ≃ₐ[A] T') → P T → P T') →
  (∀ (T : Type) [CommRing T] [Algebra A T], Subsingleton T → P T) →
  (∀ (T₁ T₂ : Type) [CommRing T₁] [CommRing T₂] [Algebra A T₁] [Algebra A T₂], Module.Finite A T₁ → Module.Finite A T₂ →
    P T₁ → P T₂ → P (T₁ × T₂)) →
  (∀ (T : Type) [CommRing T] [Algebra A T], Module.Finite A T → SH T → P T) →
  ∀ (T : Type) [CommRing T] [Algebra A T], Module.Finite A T → P T := by
  first | (exact @GlobalTheory.EtC.GmStep.FinSH.induction_principle) | (exact GlobalTheory.EtC.GmStep.FinSH.induction_principle) | (intros; apply GlobalTheory.EtC.GmStep.FinSH.induction_principle  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumOrderPlacesAboveEqFinrankMulStatement
section
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finsum_order_placesAbove_eq_finrank_mul : ∀ (k F E : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Field E] [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E] [FiniteDimensional F E], IsFF k F →
  ∀ ρ : Place k E → Place k F, IsRes ρ → (∀ s : Set (Place k F), s.Finite → (ρ ⁻¹' s).Finite) ∧ ∀ φ : Place k F → F, {v | ord v (φ v) ≠ 0}.Finite → ∑ᶠ p : Place k E, ord p (algebraMap F E (φ (ρ p))) = Module.finrank F E * ∑ᶠ v, ord v (φ v) := by
  first | exact @GlobalTheory.Nef.finsum_ord_pull_eq_finrank_mul | exact GlobalTheory.Nef.finsum_ord_pull_eq_finrank_mul | (intros; apply GlobalTheory.Nef.finsum_ord_pull_eq_finrank_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HerbrandQuotientEigenDetStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.herbrandQuotient_eigen_det : GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity.HerbrandDet := by
  first | exact @GlobalTheory.HerbrandAlg.herbrandDet | exact GlobalTheory.HerbrandAlg.herbrandDet | (intros; apply GlobalTheory.HerbrandAlg.herbrandDet <;> assumption)
end

