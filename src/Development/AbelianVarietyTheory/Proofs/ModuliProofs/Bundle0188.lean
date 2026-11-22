import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleLevelCoverOfPowEqOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelEqOfPowEqOfHasTh
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIdealOfLocally
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0109
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaCosetNonvanishingOfHasTh
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0124
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0043
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0046
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0180
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0003
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsIsoOfIsFiniteOfUniqueLiftOfClassicalPoints
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FiniteOfIsClosedOfFiniteInterClosedPoints
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0062
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0019
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0182
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0183
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0184

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSquareLevelWithGivenThetaPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.LevelTheta

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem spMap_id {A : Type} [CommRing A] : spMap (RingHom.id A) = 𝟙 _ := Spec.map_id _

theorem lbIso_pull_comp {X Y Z : Scheme.{0}} {L : LB X} {M : LB Y} {ψ : Y ⟶ X} (φ : Z ⟶ Y) {χ : Z ⟶ X}
    (H : LBIso M (L.pull ψ)) (e : χ = φ ≫ ψ) : LBIso (M.pull φ) (L.pull χ) :=
  H.chartPull (chartPullPull M φ φ rfl)
    (chartPullSame L (fun _ : PUnit => χ) (fun _ : PUnit => ψ) (fun _ => 1) φ (fun _ => e))

theorem pow_push {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (x' : Out.baseOver S' ⟶ G') (x : Out.baseOver S ⟶ G)
    (e : x'.left ≫ φ = f ≫ x.left) (m : ℕ) : (x' ^ m).left ≫ φ = f ≫ (x ^ m).left := by
  let U : Over.mk ((Out.baseOver S').hom ≫ f) ⟶ Out.baseOver S := Over.homMk f (by simp)
  have e₁ : pushHom h _ x' = preHom U x := Over.OverMorphism.ext e
  have e₂ : pushHom h _ (x' ^ m) = preHom U (x ^ m) := by rw [map_pow, map_pow, e₁]
  exact congrArg (fun z => z.left) e₂

variable {o : Type} [CommRing o] {g k : ℕ} {J : Type} {b : TBase o k}

def Above {S S' : Scheme.{0}} (P : Out.PolAV S) (act : J → (P.A ⟶ P.A)) (Q : Fin (2 * g) → (Out.baseOver S ⟶ P.A))
    (m : ℕ) {s' : S' ⟶ Sp o} (t : TObj g k J b s') (f : S' ⟶ S) (ψ : t.A.left ⟶ P.A.left) : Prop :=
  IsGrpPullback t.A P.A f ψ ∧ LBIso t.L (P.L.pull ψ) ∧ (∀ i, (t.act i).left ≫ ψ = ψ ≫ (act i).left) ∧
    ∀ i, (t.pt i ^ m).left ≫ ψ = f ≫ (Q i).left

theorem Above.comp {S S' S'' : Scheme.{0}} {P : Out.PolAV S} {act : J → (P.A ⟶ P.A)}
    {Q : Fin (2 * g) → (Out.baseOver S ⟶ P.A)} {m : ℕ} {s' : S' ⟶ Sp o} {s'' : S'' ⟶ Sp o} {t : TObj g k J b s'}
    {u : TObj g k J b s''} {f : S' ⟶ S} {ψ : t.A.left ⟶ P.A.left} (h : Above P act Q m t f ψ) {f' : S'' ⟶ S'}
    {φ : u.A.left ⟶ t.A.left} (h₁ : IsGrpPullback u.A t.A f' φ) (h₂ : LBIso u.L (t.L.pull φ))
    (h₃ : ∀ i, (u.pt i).left ≫ φ = f' ≫ (t.pt i).left) (h₄ : ∀ j, (u.act j).left ≫ φ = φ ≫ (t.act j).left) :
    Above P act Q m u (f' ≫ f) (φ ≫ ψ) := by
  refine ⟨h₁.comp h.1, LBIso.trans u.isLB (pull_isLB t.isLB _) (pull_isLB P.isLB _) h₂
    (lbIso_pull_comp φ h.2.1 rfl), fun i => ?_, fun i => ?_⟩
  · rw [← Category.assoc, h₄, Category.assoc, h.2.2.1, Category.assoc]
  · rw [← Category.assoc, pow_push h₁ _ _ (h₃ i), Category.assoc, h.2.2.2, Category.assoc]

theorem Above.compare {S S' : Scheme.{0}} {P : Out.PolAV S} {act : J → (P.A ⟶ P.A)}
    {Q : Fin (2 * g) → (Out.baseOver S ⟶ P.A)} {m : ℕ} {s' : S' ⟶ Sp o} {u u' : TObj g k J b s'}
    {f : S' ⟶ S} {ψ : u.A.left ⟶ P.A.left} {ψ' : u'.A.left ⟶ P.A.left} (h : Above P act Q m u f ψ)
    (h' : Above P act Q m u' f ψ') :
    ∃ χ : u'.A.left ⟶ u.A.left, χ ≫ ψ = ψ' ∧ IsGrpPullback u'.A u.A (𝟙 _) χ ∧ LBIso u'.L (u.L.pull χ) ∧
      (∀ i, (u'.pt i ^ m).left ≫ χ = (u.pt i ^ m).left) ∧ ∀ j, (u'.act j).left ≫ χ = χ ≫ (u.act j).left := by
  have hp := h.1.1
  let χ : u'.A.left ⟶ u.A.left := hp.lift ψ' u'.A.hom h'.1.1.w
  have e₁ : χ ≫ ψ = ψ' := hp.lift_fst _ _ _
  have e₂ : χ ≫ u.A.hom = u'.A.hom := hp.lift_snd _ _ _
  refine ⟨χ, e₁, h.1.cancel (h'.1.congr (Category.id_comp _).symm e₁.symm) (by rw [e₂, Category.comp_id]),
    LBIso.trans u'.isLB (pull_isLB P.isLB _) (pull_isLB u.isLB _) h'.2.1
      (lbIso_pull_comp χ h.2.1 e₁.symm).symm, fun i => ?_, fun j => ?_⟩
  · apply hp.hom_ext
    · rw [Category.assoc, e₁, h'.2.2.2, h.2.2.2]
    · rw [Category.assoc, e₂, Over.w, Over.w]
  · apply hp.hom_ext
    · rw [Category.assoc, e₁, h'.2.2.1, Category.assoc, h.2.2.1, ← Category.assoc, e₁]
    · rw [Category.assoc, e₂, Over.w, Category.assoc, Over.w, e₂]

theorem exists_level_with_theta_point : Out.Laws → Out.Laws2 → ∀ (g n j : ℕ) (J : Type), n.Prime → Odd n → 2 ≤ j → ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (β : o →+* R) (v : Ix g ((n ^ j) ^ 2) → R) (P : Out.PolAV (Sp R)) (act : J → (P.A ⟶ P.A)) (Q : Fin (2 * g) → (Out.baseOver (Sp R) ⟶ P.A)), (P.g = g ∧ (∀ i, IsMonHom (act i)) ∧ (∀ i, Q i ^ (n ^ j) = 1) ∧ (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp R) (y : Over.mk x ⟶ P.A), y ^ (n ^ j) = 1 → ∃! c : Ix g (n ^ j), Out.linComb (fun i => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver (Sp R)) ≫ Q i) (fun i => (c i).val) = y)) → VeryDense {q | ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)) (ψ : t'.A.left ⟶ P.A.left), RingHom.ker x = q ∧ t'.HasTh (𝟙 _) (fun a => x (v a)) ∧ (IsGrpPullback t'.A P.A (spMap x) ψ ∧ LBIso t'.L (P.L.pull ψ) ∧ (∀ i, (t'.act i).left ≫ ψ = ψ ≫ (act i).left) ∧ ∀ i, (t'.pt i ^ (n ^ j)).left ≫ ψ = (spMap x) ≫ (Q i).left)} → ∃ t : TObj g ((n ^ j) ^ 2) J b (spMap β), t.HasTh (𝟙 _) v ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)) (ψ : t'.A.left ⟶ P.A.left), t'.HasTh (𝟙 _) (fun a => x (v a)) → (IsGrpPullback t'.A P.A (spMap x) ψ ∧ LBIso t'.L (P.L.pull ψ) ∧ (∀ i, (t'.act i).left ≫ ψ = ψ ≫ (act i).left) ∧ ∀ i, (t'.pt i ^ (n ^ j)).left ≫ ψ = (spMap x) ≫ (Q i).left) → TMap t' t (spMap x) := by
  intro hL hL2 g n j J hn hodd hj o _ b R _ _ _ β v P act Q hP hdense
  have hn2 : 2 ≤ n := hn.two_le
  have hpos : 0 < n ^ j := pow_pos hn.pos j
  have hdvd : n ∣ n ^ j := dvd_pow_self n (by omega)
  have h3 : 3 ≤ n ^ j := by
    have h4 : 2 ^ 2 ≤ n ^ j := (Nat.pow_le_pow_left hn2 2).trans (Nat.pow_le_pow_right hn.pos hj)
    omega
  obtain ⟨R₁, _, _, t₁, ψ₁, hfin, het, hab, huniv⟩ := GlobalTheory.exists_finiteEtale_level_cover hL hL2 o g (n ^ j) J b R β P act Q hpos hP
  have hab' : Above P act Q (n ^ j) t₁ (spMap (algebraMap R R₁)) ψ₁ := hab
  have hspan : Ideal.span (Set.range v) = ⊤ := by
    by_contra hne
    obtain ⟨q, hq, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨p, ⟨K, _, _, x, t', ψ, hker, hth, -⟩, -, hqp, -⟩ :=
      hdense q 1 hq.isPrime (fun h => hq.ne_top ((Ideal.eq_top_iff_one _).2 h))
    obtain ⟨c, hc⟩ := GlobalTheory.coset_of_hasTh hL hL2 o g (n ^ j) J b _ _ t' n K (𝟙 _) _ ⊥ hn2 hdvd hth Ideal.isPrime_bot 0
    apply hc
    have : v (0 + (n ^ j / n) • c) ∈ RingHom.ker x := hker ▸ hqp (hle (Ideal.subset_span ⟨_, rfl⟩))
    exact this
  have hspan₁ : Ideal.span (Set.range fun a => algebraMap R R₁ (v a)) = ⊤ := by
    have := congrArg (Ideal.map (algebraMap R R₁)) hspan
    rwa [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at this
  obtain ⟨𝔞, h𝔞⟩ := GlobalTheory.ThetaClosed.exists_ideal_hasTh_iff hL hL2 o g (n ^ j) J b R₁ _ t₁ _ hodd.pow h3 hspan₁

  have hth : ∀ (R' : Type) [CommRing R'] (x : R →+* R') (y : R₁ →+* R') (s' : Sp R' ⟶ Sp o)
      (t' : TObj g ((n ^ j) ^ 2) J b s'), y.comp (algebraMap R R₁) = x → TMap t' t₁ (spMap y) →
      (t'.HasTh (𝟙 _) (fun a => x (v a)) ↔ ∀ r ∈ 𝔞, y r = 0) := by
    intro R' _ x y s' t' e hm
    subst e
    rw [GlobalTheory.hasTh_iff_of_tmap o g (n ^ j) J b _ _ t₁ _ _ t' _ R' _ _ hm, Category.id_comp]
    exact h𝔞 R' y

  have huniq : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (y y' : R₁ →+* K),
      y.comp (algebraMap R R₁) = x → y'.comp (algebraMap R R₁) = x → (∀ r ∈ 𝔞, y r = 0) → (∀ r ∈ 𝔞, y' r = 0) →
      y = y' := by
    intro K _ _ x y y' e e' k k'
    have d : spMap y ≫ spMap (algebraMap R R₁) = spMap x := by rw [spMap_comp, e]
    have d' : spMap y' ≫ spMap (algebraMap R R₁) = spMap x := by rw [spMap_comp, e']
    obtain ⟨u, hu⟩ := GlobalTheory.tObj_pull o g _ J b _ _ _ (spMap x ≫ spMap β) (spMap y) t₁ (by rw [← Category.assoc, d])
    obtain ⟨u', hu'⟩ := GlobalTheory.tObj_pull o g _ J b _ _ _ (spMap x ≫ spMap β) (spMap y') t₁ (by rw [← Category.assoc, d'])
    have T := (hth K x y _ u e hu).2 k
    have T' := (hth K x y' _ u' e' hu').2 k'
    obtain ⟨φ, a₁, a₂, a₃, a₄⟩ := id hu
    obtain ⟨φ', a₁', a₂', a₃', a₄'⟩ := id hu'
    have A := hab'.comp a₁ a₂ a₃ a₄
    have A' := hab'.comp a₁' a₂' a₃' a₄'
    rw [d] at A
    rw [d'] at A'
    obtain ⟨χ, c₀, c₁, c₂, c₃, c₄⟩ := A.compare A'
    have c₅ := GlobalTheory.level_eq_of_pow_eq_of_hasTh hL hL2 g n j J hn hodd hj o b K _ u u' χ _ c₁ c₂ c₃ T T'
    have hχ : TMap u' u (𝟙 _) := ⟨χ, c₁, c₂, fun i => by rw [c₅, Category.id_comp], c₄⟩
    have hm : TMap u' t₁ (spMap y) := by
      have := ((GlobalTheory.ZM.tmap_id_comp_cancel o g _ J b _ _ _ _ _ _ t₁ u u').2 _ _ hu).1 hχ
      rwa [Category.id_comp] at this
    refine (huniv K x u' (φ' ≫ ψ₁) A').unique ⟨e, fun i => ?_, hm⟩ ⟨e', fun i => ?_, hu'⟩
    · rw [← c₀, ← Category.assoc, c₅, ← Category.assoc, a₃, Category.assoc]
    · rw [← Category.assoc, a₃', Category.assoc]
  have hcomp : (Ideal.Quotient.mk 𝔞).comp (algebraMap R R₁) = algebraMap R (R₁ ⧸ 𝔞) := rfl
  have : Algebra.FormallyUnramified R (R₁ ⧸ 𝔞) :=
    Algebra.FormallyUnramified.of_surjective (Ideal.Quotient.mkₐ R 𝔞) Ideal.Quotient.mk_surjective
  have hbij : Function.Bijective (algebraMap R (R₁ ⧸ 𝔞)) := by
    refine GlobalTheory.algebraMap_bijective_of_unramified_of_unique_geometric_point R (R₁ ⧸ 𝔞) _ hdense ?_
    rintro q ⟨K, _, _, x, t', ψ, hker, T, A⟩
    obtain ⟨y, ⟨e, -, hm⟩, -⟩ := huniv K x t' ψ A
    have k := (hth K x y _ t' e hm).1 T
    refine ⟨K, inferInstance, inferInstance, x, hker, Ideal.Quotient.lift 𝔞 y k, ?_, fun z hz => ?_⟩
    · exact e
    · have := huniq K x (z.comp (Ideal.Quotient.mk 𝔞)) y hz e
        (fun r hr => by rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 hr, map_zero]) k
      exact Ideal.Quotient.ringHom_ext (this.trans (by ext r; rfl))
  let ε : R ≃+* R₁ ⧸ 𝔞 := RingEquiv.ofBijective _ hbij
  let ρ : R₁ →+* R := (ε.symm : R₁ ⧸ 𝔞 →+* R).comp (Ideal.Quotient.mk 𝔞)
  have hρ : ρ.comp (algebraMap R R₁) = RingHom.id R := RingHom.ext fun r => ε.symm_apply_apply r
  have hρ' : ∀ r, r - algebraMap R R₁ (ρ r) ∈ 𝔞 := fun r =>
    Ideal.Quotient.eq.1 (ε.apply_symm_apply (Ideal.Quotient.mk 𝔞 r)).symm
  obtain ⟨t, ht⟩ := GlobalTheory.tObj_pull o g _ J b _ _ _ (spMap β) (spMap ρ) t₁
    (by rw [← Category.assoc, spMap_comp, hρ, spMap_id, Category.id_comp])
  refine ⟨t, (hth R (RingHom.id R) ρ _ t hρ ht).2 fun r hr => ?_, fun K _ _ x t' ψ T A => ?_⟩
  · show ε.symm (Ideal.Quotient.mk 𝔞 r) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hr, map_zero]
  · obtain ⟨y, ⟨e, -, hm⟩, -⟩ := huniv K x t' ψ A
    have k := (hth K x y _ t' e hm).1 T
    have hy : x.comp ρ = y := RingHom.ext fun r => by
      have := k _ (hρ' r)
      rw [map_sub, sub_eq_zero] at this
      rw [this, ← e]; rfl
    refine ((GlobalTheory.ZM.tmap_id_comp_cancel o g _ J b _ _ _ _ _ _ t₁ t t').2 _ _ ht).2 ?_
    rwa [spMap_comp ρ x, hy]

end GlobalTheory.LevelTheta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueHomExtensionSemiAbelianNormal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory.HomExt

theorem mem_range_or_exists_dvr {W Z : Scheme.{0}} (i : W ⟶ Z) [IsPreimmersion i] [Flat i]
    [IsDominant i] [QuasiCompact i] [IsLocallyNoetherian Z] (z : Z) :
    z ∈ Set.range i ∨ ∃ (T : Type) (_ : CommRing T) (_ : IsDomain T)
      (_ : IsDiscreteValuationRing T) (a : Sp T ⟶ Z) (c : Sp (FractionRing T) ⟶ W),
      c ≫ i = spMap (algebraMap T (FractionRing T)) ≫ a ∧ a (IsLocalRing.closedPoint T) = z := by
  obtain ⟨ξ, hξ, hs⟩ := exists_mem_genericPoints_specializes z
  have hξ' := genericPoints_subset_range_of_isDominant i hξ
  by_cases hne : ξ = z
  · exact .inl (hne ▸ hξ')
  obtain ⟨O, _, _, -, a, h₀, h₁⟩ := exists_complete_discreteValuationRing_of_specializes hs hne
  obtain ⟨c, hc⟩ := exists_lift_of_range_subset i
    (spMap (algebraMap O (FractionRing O)) ≫ a) (by
      rintro _ ⟨t, rfl⟩
      have : spMap (algebraMap O (FractionRing O)) t = (⊥ : PrimeSpectrum O) := by
        apply PrimeSpectrum.ext
        change Ideal.comap (algebraMap O (FractionRing O)) t.asIdeal = ⊥
        rw [@Ideal.eq_bot_of_prime _ _ t.asIdeal t.isPrime]
        exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective _ _)
      rw [Scheme.Hom.comp_apply, this]
      exact h₀ ▸ hξ')
  exact .inr ⟨O, inferInstance, inferInstance, inferInstance, a, c, hc, h₁⟩

theorem finite_torsion_points {X : Scheme.{0}} {G : Over X} [GrpObj G] (hG : IsSemiAbelian G)
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ X) {n : ℕ} (hn : 0 < n) :
    Finite {x : Over.mk t ⟶ G // x ^ n = 1} := by
  have := GlobalTheory.finite_torsion_semiAbelian Ω _ (IsSemiAbelian.pullback t G hG) n hn
  let e := TorsionLift.ptsEquiv t G (𝟙_ (Over (Sp Ω))) t (Category.id_comp _)
  refine Finite.of_injective
    (β := {x : 𝟙_ (Over (Sp Ω)) ⟶ (Over.pullback t).obj G // x ^ n = 1})
    (fun x ↦ ⟨e.symm x.1, (map_pow e.symm x.1 n).symm.trans
      ((congrArg e.symm x.2).trans (map_one e.symm))⟩) fun a b h ↦ ?_
  exact Subtype.ext (e.symm.injective (congrArg Subtype.val h))

theorem locallyQuasiFinite_of_torsion {X : Scheme.{0}} (z : X ⟶ Sp ℤ) [LocallyOfFiniteType z]
    {G G' Γ : Over X} [GrpObj G] [GrpObj G'] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    (hG' : IsSemiAbelian G') (p : Γ ⟶ G) (q : Γ ⟶ G') [LocallyOfFiniteType p.left]
    (hext : ∀ {T : Scheme.{0}} (a b : T ⟶ Γ.left), a ≫ p.left = b ≫ p.left →
      a ≫ q.left = b ≫ q.left → a = b)
    (key : ∀ (k : Type) [Field k] (c : Sp k ⟶ Γ.left) (n : ℕ),
      c ≫ (p ^ n).left = c ≫ (1 : Γ ⟶ G).left → c ≫ (q ^ n).left = c ≫ (1 : Γ ⟶ G').left) :
    LocallyQuasiFinite p.left := by
  have : JacobsonSpace Γ.left := jacobsonSpace_of_locallyOfFiniteType_int (p.left ≫ G.hom ≫ z)
  have : JacobsonSpace G.left := jacobsonSpace_of_locallyOfFiniteType_int (G.hom ≫ z)
  refine locallyQuasiFinite_of_finite_fibres_closedPoints p.left fun w hw ↦ ?_
  have hσ : IsClosed ({p.left w} : Set G.left) := p.left.closePoints_subset_preimage_closedPoints hw
  generalize p.left w = σ at hσ
  have : Finite (G.left.residueField σ) :=
    (jacobson_closedPoints_tools_int G.left (G.hom ≫ z)).2.1 σ hσ
  let t₀ : Sp (G.left.residueField σ) ⟶ X := G.left.fromSpecResidueField σ ≫ G.hom
  have := SemiAbTorsion.finite_points_over z G (G.left.residueField σ) t₀
  let x₀ : Over.mk t₀ ⟶ G := Over.homMk (G.left.fromSpecResidueField σ) rfl
  have hn : 0 < Nat.card (Over.mk t₀ ⟶ G) := Nat.card_pos
  have hx₀ : x₀ ^ Nat.card (Over.mk t₀ ⟶ G) = 1 := pow_card_eq_one'
  generalize Nat.card (Over.mk t₀ ⟶ G) = n at hn hx₀
  let Ω := AlgebraicClosure (G.left.residueField σ)
  let r : Sp Ω ⟶ Sp (G.left.residueField σ) := spMap (algebraMap (G.left.residueField σ) Ω)
  let y : Sp Ω ⟶ G.left := r ≫ G.left.fromSpecResidueField σ
  have hy : σ ∈ Set.range y :=
    ⟨default, (Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply σ _)⟩
  let r' : Over.mk (y ≫ G.hom) ⟶ Over.mk t₀ := Over.homMk r (Category.assoc _ _ _).symm
  have := finite_torsion_points hG' (y ≫ G.hom) hn
  refine (finite_preimage_of_finite_lifts p.left y ?_).subset
    (Set.preimage_mono (Set.singleton_subset_iff.mpr hy))
  let l : {x : Sp Ω ⟶ Γ.left // x ≫ p.left = y} → (Over.mk (y ≫ G.hom) ⟶ Γ) := fun x ↦
    Over.homMk x.1 (by
      change x.1 ≫ Γ.hom = y ≫ G.hom
      rw [← Over.w p, ← Category.assoc, x.2])
  have hl (x) : (l x ≫ q) ^ n = 1 := by
    have e : l x ≫ p = r' ≫ x₀ := Over.OverMorphism.ext x.2
    have h₁ : l x ≫ p ^ n = l x ≫ (1 : Γ ⟶ G) := by
      rw [SemiAbTorsion.comp_pow_points, e, ← SemiAbTorsion.comp_pow_points, hx₀, MonObj.comp_one,
        MonObj.comp_one]
    have h₂ : l x ≫ q ^ n = l x ≫ (1 : Γ ⟶ G') :=
      Over.OverMorphism.ext (key Ω x.1 n (congrArg CommaMorphism.left h₁))
    rwa [SemiAbTorsion.comp_pow_points, MonObj.comp_one] at h₂
  refine Finite.of_injective (β := {x : Over.mk (y ≫ G.hom) ⟶ G' // x ^ n = 1})
    (fun x ↦ ⟨l x ≫ q, hl x⟩) fun a b h ↦ Subtype.ext (hext _ _ (a.2.trans b.2.symm) ?_)
  exact congrArg (fun u ↦ u.1.left) h

end GlobalTheory.HomExt

open GlobalTheory GlobalTheory.HomExt in

theorem GlobalTheory.existsUnique_hom_extension_semiAbelian_normal :
    (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (X U : Scheme.{0}) (j : U ⟶ X), (ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X ∧ ∃ z : X ⟶ Sp ℤ, LocallyOfFiniteType z ∧ Flat z) → IsPreimmersion j → Flat j → IsDominant j → QuasiCompact j → ∀ (G G' : Over X) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback j).obj G ⟶ (Over.pullback j).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback j).map F = f := by
  rintro H X U j ⟨hX, z, _, -⟩ _ _ _ _ G G' _ _ hG hG' f hf
  have := hG.smooth
  have := hG'.smooth
  have := hG.quasiCompact
  have := hG'.quasiCompact
  have := hG'.separated
  have : GlobalTheory.IsNormalScheme X := (GlobalTheory.isNormalScheme_iff X).mpr hX
  have : GlobalTheory.IsNormalScheme G.left := (GlobalTheory.isNormalScheme_iff _).mpr
    (forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth G.hom hX)
  have : IsSchemeTheoreticallyDominant j := IsSchemeTheoreticallyDominant.of_isDominant j
  let u : pullback G.hom j ⟶ G.left := pullback.fst G.hom j
  let φ : pullback G.hom j ⟶ G'.left := f.left ≫ pullback.fst G'.hom j
  have hw : f.left ≫ pullback.snd G'.hom j = pullback.snd G.hom j := Over.w f
  have huφ : u ≫ G.hom = φ ≫ G'.hom := by
    rw [Category.assoc, pullback.condition, pullback.condition, reassoc_of% hw]
  have : IsDominant u := isDominant_pullback_fst_of_isOpenMap j G.hom G.hom.isOpenMap
  have : IsPreimmersion u := inferInstanceAs (IsPreimmersion (pullback.fst G.hom j))
  have : Flat u := inferInstanceAs (Flat (pullback.fst G.hom j))
  have : QuasiCompact u := inferInstanceAs (QuasiCompact (pullback.fst G.hom j))
  have hus := isIso_stalkMap_of_flat_of_surjectiveOnStalks u
  have : GlobalTheory.IsNormalScheme (pullback G.hom j) := GlobalTheory.IsNormalScheme.of_isIso_stalkMap u
  let Γ := graphClosure G.hom G'.hom u φ huφ
  let p : Γ ⟶ G.left := graphClosure.fst G.hom G'.hom u φ huφ
  let q : Γ ⟶ G'.left := graphClosure.snd G.hom G'.hom u φ huφ
  let i : pullback G.hom j ⟶ Γ := graphClosure.incl G.hom G'.hom u φ huφ
  have hip : i ≫ p = u := graphClosure.incl_fst ..
  have hiq : i ≫ q = φ := graphClosure.incl_snd ..
  have hpq : p ≫ G.hom = q ≫ G'.hom := graphClosure.condition ..
  have hpb := graphClosure.isPullback_incl G.hom G'.hom u φ huφ
  have : IsPreimmersion i := MorphismProperty.of_isPullback hpb ‹IsPreimmersion u›
  have : Flat i := MorphismProperty.of_isPullback hpb ‹Flat u›
  have : QuasiCompact i := graphClosure.quasiCompact_incl ..
  have : IsSchemeTheoreticallyDominant i := graphClosure.schemeDominant_incl ..
  have : IsDominant i := inferInstance
  have : IsReduced Γ := graphClosure.isReduced ..
  have : LocallyOfFiniteType p := graphClosure.locallyOfFiniteType_fst ..
  have : QuasiCompact p := graphClosure.quasiCompact_fst ..
  have : IsSeparated p := graphClosure.isSeparated_fst ..
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian (G.hom ≫ z)
  have : IsLocallyNoetherian Γ := LocallyOfFiniteType.isLocallyNoetherian p
  have : Surjective p := by
    refine ⟨fun σ ↦ ?_⟩
    rcases mem_range_or_exists_dvr u σ with ⟨w, rfl⟩ | ⟨T, _, _, _, a, c, hc, rfl⟩
    · exact ⟨i w, by rw [← Scheme.Hom.comp_apply, hip]⟩
    obtain ⟨F, s, -, -, hs₂, hs⟩ := exists_hom_along_dvr H j hG hG' f T _ a c hc
    have := schemeTheoreticallyDominant_fractionField T (FractionRing T)
    have hF : F.left ≫ pullback.snd G'.hom (a ≫ G.hom) = pullback.snd G.hom (a ≫ G.hom) := Over.w F
    obtain ⟨l, ⟨hl, -⟩, -⟩ := graphClosure.existsUnique_lift G.hom G'.hom u φ huφ a
      (s ≫ F.left ≫ pullback.fst G'.hom (a ≫ G.hom))
      (by rw [Category.assoc, Category.assoc, pullback.condition, reassoc_of% hF, reassoc_of% hs₂])
      (spMap (algebraMap T (FractionRing T))) c hc.symm hs
    exact ⟨l (IsLocalRing.closedPoint T), by rw [← hl]; rfl⟩
  let Γ' : Over X := Over.mk (p ≫ G.hom)
  let p' : Γ' ⟶ G := Over.homMk p rfl
  let q' : Γ' ⟶ G' := Over.homMk q hpq.symm
  have : LocallyOfFiniteType p'.left := ‹LocallyOfFiniteType p›
  have : LocallyQuasiFinite p := by
    refine locallyQuasiFinite_of_torsion z hG' p' q'
      (fun a b ↦ graphClosure.hom_ext G.hom G'.hom u φ huφ) fun k _ x n hx ↦ ?_
    rcases mem_range_or_exists_dvr i (x default) with hw | ⟨T, _, _, _, a, c, hc, ha⟩
    · obtain ⟨c, rfl⟩ := exists_lift_of_range_subset i x (by
        rintro _ ⟨t, rfl⟩
        rwa [Subsingleton.elim t default])
      exact comp_pow_eq_one_of_pullback_hom j f p' q' _ c
        (by rw [Category.assoc]; exact congrArg (c ≫ ·) hip.symm)
        (by rw [Category.assoc]; exact congrArg (c ≫ ·) hiq.symm) n hx
    obtain ⟨F, s, _, hs₁, hs₂, hs⟩ := exists_hom_along_dvr H j hG hG' f T _ (a ≫ p) c
      (by rw [← reassoc_of% hc, hip])
    have := schemeTheoreticallyDominant_fractionField T (FractionRing T)
    have hF : F.left ≫ pullback.snd G'.hom ((a ≫ p) ≫ G.hom) =
      pullback.snd G.hom ((a ≫ p) ≫ G.hom) := Over.w F
    have hb : s ≫ F.left ≫ pullback.fst G'.hom ((a ≫ p) ≫ G.hom) = a ≫ q := by
      have := over_ext_of_schemeTheoreticallyDominant (Y := Over.mk ((a ≫ p) ≫ G.hom)) (X := G')
        (spMap (algebraMap T (FractionRing T)))
        (a := Over.homMk (s ≫ F.left ≫ pullback.fst G'.hom ((a ≫ p) ≫ G.hom)) (by
          change (s ≫ F.left ≫ pullback.fst G'.hom ((a ≫ p) ≫ G.hom)) ≫ G'.hom = (a ≫ p) ≫ G.hom
          rw [Category.assoc s, Category.assoc F.left, pullback.condition, reassoc_of% hF,
            reassoc_of% hs₂]))
        (b := Over.homMk (a ≫ q) (by
          change (a ≫ q) ≫ G'.hom = (a ≫ p) ≫ G.hom
          rw [Category.assoc, Category.assoc, hpq]))
        (hs.trans (by
          change _ = spMap (algebraMap T (FractionRing T)) ≫ a ≫ q
          rw [← reassoc_of% hc, hiq]))
      exact congrArg CommaMorphism.left this
    let r : Sp (IsLocalRing.ResidueField T) ⟶ Sp T := spMap (IsLocalRing.residue T)
    have hr : x default ∈ Set.range (r ≫ a) := by
      refine ⟨IsLocalRing.closedPoint _, ?_⟩
      exact (Scheme.Hom.comp_apply r a _).trans
        ((congrArg a (IsLocalRing.comap_closedPoint (IsLocalRing.residue T))).trans ha)
    rw [field_point_comp_eq_iff _ _ x _ ⟨default, rfl⟩,
      ← field_point_comp_eq_iff (Z := Γ'.left) _ _ (r ≫ a) _ hr] at hx ⊢
    exact comp_pow_eq_one_of_pullback_hom _ F p' q' (r ≫ a) (r ≫ s)
      (by rw [Category.assoc, hs₁, Category.assoc]; rfl)
      (by rw [Category.assoc, hb, Category.assoc]; rfl) n hx
  have : IsIso p := by
    have : IsPreimmersion (i ≫ p) := by rwa [hip]
    have : Flat (i ≫ p) := by rwa [hip]
    have : IsDominant (i ≫ p) := by rwa [hip]
    have : QuasiCompact (i ≫ p) := by rwa [hip]
    exact isIso_of_densePart i p
  obtain ⟨ψ, hψ, huψ⟩ := graphClosure.exists_extension_of_isIso_fst G.hom G'.hom u φ huφ
  let F : G ⟶ G' := Over.homMk ψ hψ.symm
  have hF : (Over.pullback j).map F = f := by
    ext1
    apply pullback.hom_ext
    · exact (pullback.lift_fst _ _ _).trans huψ
    · exact (Over.w _).trans hw.symm
  refine ⟨F, ⟨?_, hF⟩, fun F' hF' ↦ pullback_map_injective_of_flat j (hF'.2.trans hF.symm)⟩
  have : IsMonHom ((Over.pullback j).map F) := hF ▸ hf
  exact isMonHom_of_pullback_of_flat j F
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.KTrivNearGoodPrime
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild

namespace GlobalTheory.ZM.NearBuild

private theorem isGrpPullback_pullback_fst {S S' : Scheme.{0}} (G : Over S) [GrpObj G] (f : S' ⟶ S) :
    IsGrpPullback ((Over.pullback f).obj G) G f (pullback.fst G.hom f) := by
  refine ⟨IsPullback.of_hasPullback G.hom f, ?_⟩
  intro T x y x₀ y₀ hx hy
  have h := GlobalTheory.UU.toBase_mul_pullback G f T x y
  have ex : x₀ = Out.toBase (A := G) (A' := (Over.pullback f).obj G) (g := pullback.fst G.hom f) pullback.condition x := by
    ext
    simp [hx, Out.toBase]
  have ey : y₀ = Out.toBase (A := G) (A' := (Over.pullback f).obj G) (g := pullback.fst G.hom f) pullback.condition y := by
    ext
    simp [hy, Out.toBase]
  rw [ex, ey, ← h]
  simp [Out.toBase]

theorem kTriv_near_good_prime : ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ) (R : Type) [CommRing R] [IsNoetherianRing R] (β : o →+* R) (v : Ix g (N' ^ 2) → R) (A : Over (Sp R)) [GrpObj A] (L : LB A.left) (act : J → (A ⟶ A)) (Q : Fin (2 * g) → (Out.baseOver (Sp R) ⟶ A)) (q₀ : Ideal R), q₀ ∈ objPrimes b Mat κ β v → PolFam b Mat κ β v A L act Q → ∃ f : R, f ∉ q₀ ∧ Out.KTriv ((Over.pullback (spMap (loc f))).obj A) (L.pull (pullback.fst A.hom (spMap (loc f)))) := by
  intro o _ g N' J b Mat κ R _ _ β v A _ L act Q q₀ hq hP
  obtain ⟨K, _, _, x, s, t, hker, hgood⟩ := mem_objPrimes.1 hq
  obtain ⟨hab, -, hLB, -, -, hamp, -, hfib⟩ := hP
  obtain ⟨ψ, hψ, hiso⟩ := hfib K x s t hgood
  obtain ⟨e, he, hcomp⟩ := grpPullback_iso (isGrpPullback_pullback_fst A (spMap x)) hψ.1
  haveI := he
  have hLB' : (L.pull (pullback.fst A.hom (spMap x))).IsLB := pull_isLB hLB _
  have hLt : (t.L.pull e.hom.left).IsLB := pull_isLB t.isLB _
  have hψL : (L.pull ψ).IsLB := pull_isLB hLB ψ
  have hcls : LBIso (L.pull (pullback.fst A.hom (spMap x))) (t.L.pull e.hom.left) := by
    rw [← GlobalTheory.CechPic.cls_eq_iff hLB' hLt, GlobalTheory.CechPic.cls_pull hLB _ hLB', GlobalTheory.CechPic.cls_pull t.isLB _ hLt,
      ← hcomp, GlobalTheory.CechPic.pull_comp, ← GlobalTheory.CechPic.cls_pull hLB ψ hψL,
      ← (GlobalTheory.CechPic.cls_eq_iff t.isLB hψL).2 hiso]
  have hfibK := (amplePt (Sp K) K (𝟙 _) t.A _ e.hom.left (isGrpPullback_of_iso e) t.L _ t.isLB hLB' hcls
    t.ample t.ktriv).2
  obtain ⟨f, hf, hk⟩ := kTriv_away_of_kTriv_fibre globalFns_holds R A L K x hab hLB hamp hfibK
  refine ⟨f, fun h => hf ?_, hk⟩
  rw [← hker, RingHom.mem_ker] at h
  exact h

end GlobalTheory.ZM.NearBuild
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LambdaBundleAdjointOfWeilPairingAdjointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lambdaBundle_adjoint_of_weilPairing_adjoint : Out.Laws → ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (P : Out.PolAV (Sp k)) (a a' : P.A ⟶ P.A), IsMonHom a → IsMonHom a' → (∀ (n : ℕ) (x y : 𝟙_ (Over (Sp k)) ⟶ P.A) (c : Γ((𝟙_ (Over (Sp k))).left, ⊤)ˣ), 0 < n → x ^ n = 1 → y ^ n = 1 → Out.WeilIs P.A P.L n (x ≫ a) y c → Out.WeilIs P.A P.L n x (y ≫ a') c) → LBIso (cubeLB P.A ![fst P.A P.A ≫ a, snd P.A P.A] P.L) (cubeLB P.A ![fst P.A P.A, snd P.A P.A ≫ a'] P.L) := by
  first | exact @GlobalTheory.lbIso_cubeLB_of_pairing_adjoint | exact GlobalTheory.lbIso_cubeLB_of_pairing_adjoint | (intros; apply GlobalTheory.lbIso_cubeLB_of_pairing_adjoint <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LambdaBundleIsoOfPrimeToPWeilPairingsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lambdaBundleIso_of_primeToP_weilPairings : Out.Laws → ∀ (k : Type) [Field k] [IsAlgClosed k] (P P' : Out.PolAV (Sp k)) (α : P.A ⟶ P'.A) (p d : ℕ), IsMonHom α → p.Prime → CharZero k → (∀ (n : ℕ) (x y : 𝟙_ (Over (Sp k)) ⟶ P.A) (c : kˣ), 0 < n → n.Coprime p → x ^ n = 1 → y ^ n = 1 → Out.WeilIs P.A P.L n x y (unitOn c) → Out.WeilIs P'.A P'.L n (x ≫ α) (y ≫ α) (unitOn (c ^ d))) → LBIso (abelian₂ P.A (lbPow P.L d)) (abelian₂ P.A (P'.L.pull α.left)) := by
  first | exact @GlobalTheory.lam_iso_of_weil_pairings | exact GlobalTheory.lam_iso_of_weil_pairings | (intros; apply GlobalTheory.lam_iso_of_weil_pairings <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PolarizedAbelianAmpleExistsPositiveVolumeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarizedAbelian_ample_exists_positive_volume : Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (M : LB P.A.left), M.IsLB → Out.RelAmple P.A M → ∃ δ : ℝ, 0 < δ ∧ Vol P.A.hom M P.g δ := by
  first | exact @GlobalTheory.VolEx.exists_vol | exact GlobalTheory.VolEx.exists_vol | (intros; apply GlobalTheory.VolEx.exists_vol <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TangentVectorZeroOfObjectConstantAlongStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangentVector_zero_of_object_constant_along : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g n N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (I : Ideal (MvPolynomial (Ix g (N' ^ 2)) o)) (Y : MMPre n N' I) (u : TObj g (N' ^ 2) J b Y.s), Odd N' → (∀ (R : Type) [CommRing R] (x : Sp R ⟶ Y.MM) (v : Ix g (N' ^ 2) → R), u.HasTh x v ↔ SecCoord Y.de Y.th x v) → ∀ (K : Type) [Field K] (x : Sp (DualNumber K) ⟶ Y.MM) (t : TObj g (N' ^ 2) J b (x ≫ Y.s)), x ≫ Y.s = constPt x ≫ Y.s → TMap t u x → TMap t u (constPt x) → x = constPt x := by
  first | exact @GlobalTheory.ZM.tangent_eq_constPt_of_tMap | exact GlobalTheory.ZM.tangent_eq_constPt_of_tMap | (intros; apply GlobalTheory.ZM.tangent_eq_constPt_of_tMap <;> assumption)
end

