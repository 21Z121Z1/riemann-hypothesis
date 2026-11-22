import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0777
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0805
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0807
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0799
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0810
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0011
import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatSumThIndRegroup
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory

theorem latSum_tower_reps (E : Type) [Field E] [NumberField E] (W : Type) [AddCommGroup W] [Module (𝓞 E) W]
    (D G C B : Submodule (𝓞 E) W) (hBC : B ≤ C) (hCG : C ≤ G) (hGD : G ≤ D)
    (hfin : Finite (↥D ⧸ B.comap D.subtype)) :
    ∃ R : Finset W, (∀ x ∈ R, x ∈ G) ∧ R.card = Nat.card (↥G ⧸ C.comap G.subtype) ∧
      ∀ f : W → ℂ, (∀ x, f x ≠ 0 → x ∈ G) → (∀ x y, x - y ∈ B → f x = f y) →
        latSum D B f = ∑ x ∈ R, latSum C B fun y => f (x + y) := by
  classical
  have key : ∀ (P Q : Submodule (𝓞 E) W) (t u : ↥P),
      (Submodule.Quotient.mk t : ↥P ⧸ Q.comap P.subtype) = Submodule.Quotient.mk u ↔ (t : W) - u ∈ Q := by
    intro P Q t u
    rw [Submodule.Quotient.eq, Submodule.mem_comap]
    rfl
  set r : (↥G ⧸ C.comap G.subtype) → ↥G :=
    Function.surjInv (Submodule.Quotient.mk_surjective (C.comap G.subtype)) with hr
  set s : (↥C ⧸ B.comap C.subtype) → ↥C :=
    Function.surjInv (Submodule.Quotient.mk_surjective (B.comap C.subtype)) with hs
  set t : (↥D ⧸ B.comap D.subtype) → ↥D :=
    Function.surjInv (Submodule.Quotient.mk_surjective (B.comap D.subtype)) with ht
  have hr' : ∀ z, Submodule.Quotient.mk (r z) = z := fun z => Function.surjInv_eq _ z
  have hs' : ∀ z, Submodule.Quotient.mk (s z) = z := fun z => Function.surjInv_eq _ z
  have ht' : ∀ z, Submodule.Quotient.mk (t z) = z := fun z => Function.surjInv_eq _ z
  have hmem : ∀ p : (↥G ⧸ C.comap G.subtype) × (↥C ⧸ B.comap C.subtype), (r p.1 : W) + s p.2 ∈ D :=
    fun p => hGD (G.add_mem (r p.1).2 (hCG (s p.2).2))
  let φ : (↥G ⧸ C.comap G.subtype) × (↥C ⧸ B.comap C.subtype) → (↥D ⧸ B.comap D.subtype) :=
    fun p => Submodule.Quotient.mk ⟨_, hmem p⟩
  have hinj : Function.Injective φ := by
    rintro ⟨x, j⟩ ⟨x', j'⟩ h
    have h1 : (r x : W) + s j - (r x' + s j') ∈ B := (key D B _ _).1 h
    have h2 : x = x' := by
      rw [← hr' x, ← hr' x', key]
      have : (r x : W) - r x' = ((r x : W) + s j - (r x' + s j')) + (s j' - s j) := by abel
      rw [this]
      exact C.add_mem (hBC h1) (C.sub_mem (s j').2 (s j).2)
    subst h2
    have h3 : j = j' := by
      rw [← hs' j, ← hs' j', key]
      simpa using h1
    rw [h3]
  haveI hprod : Finite ((↥G ⧸ C.comap G.subtype) × (↥C ⧸ B.comap C.subtype)) := Finite.of_injective φ hinj
  haveI : Finite (↥G ⧸ C.comap G.subtype) := Finite.prod_left (↥C ⧸ B.comap C.subtype)
  haveI : Finite (↥C ⧸ B.comap C.subtype) := Finite.prod_right (↥G ⧸ C.comap G.subtype)
  letI := Fintype.ofFinite (↥G ⧸ C.comap G.subtype)
  letI := Fintype.ofFinite (↥C ⧸ B.comap C.subtype)
  letI := Fintype.ofFinite (↥D ⧸ B.comap D.subtype)
  have hrinj : Function.Injective fun z => (r z : W) := by
    intro z w h
    rw [← hr' z, ← hr' w, Subtype.ext h]
  refine ⟨Finset.univ.image fun z => (r z : W), ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨z, -, rfl⟩ := Finset.mem_image.1 hx
    exact (r z).2
  · rw [Finset.card_image_of_injective _ hrinj, Nat.card_eq_fintype_card, Finset.card_univ]
  · intro f hf0 hf
    rw [Finset.sum_image fun _ _ _ _ h => hrinj h]
    unfold latSum
    simp only [finsum_eq_sum_of_fintype]
    rw [← Fintype.sum_prod_type']
    symm
    refine Fintype.sum_of_injective φ hinj _ _ ?_ ?_
    · intro z hz
      by_contra hne
      have hG : (t z : W) ∈ G := hf0 _ hne
      apply hz
      have h1 : (r (Submodule.Quotient.mk ⟨_, hG⟩) : W) - t z ∈ C := (key G C _ ⟨_, hG⟩).1 (hr' _)
      have h1' : (t z : W) - r (Submodule.Quotient.mk ⟨_, hG⟩) ∈ C := by
        simpa using C.neg_mem h1
      have h2 : (s (Submodule.Quotient.mk ⟨_, h1'⟩) : W) - ((t z : W) - r (Submodule.Quotient.mk ⟨_, hG⟩)) ∈ B :=
        (key C B _ ⟨_, h1'⟩).1 (hs' _)
      refine ⟨(Submodule.Quotient.mk ⟨_, hG⟩, Submodule.Quotient.mk ⟨_, h1'⟩), ?_⟩
      refine Eq.trans ?_ (ht' z)
      refine (key D B _ _).2 ?_
      convert h2 using 1
      simp only
      abel
    · intro p
      apply hf
      exact (key D B ⟨_, hmem p⟩ _).1 (ht' _).symm

theorem thInd_congr_of_sub_mem {X : Fields} (A : Amb X) {a b : ℕ} (S : Finset (HeightOneSpectrum (𝓞 X.E)))
    (L : Submodule (𝓞 X.E) (Sp X.E a)) (L' : Submodule (𝓞 X.E) (Sp X.E b)) (c : ℕ) (x y : HomE X.E a b)
    (h : x - y ∈ mulLat c (homAt S L L')) : A.thInd S L L' c x = A.thInd S L L' c y := by
  have h1 : A.IsLift S L L' c x = A.IsLift S L L' c y := by
    funext s
    unfold Amb.IsLift
    congr 1
    apply propext
    constructor
    · intro hs
      simpa using Submodule.add_mem _ hs h
    · intro hs
      simpa using Submodule.sub_mem _ hs h
  unfold Amb.thInd Amb.liftW
  rw [h1]

theorem latSum_thInd_regroup : ∀ (X : Fields) (A : Amb X) (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E))) (L : Submodule (𝓞 X.E) (Sp X.E a)) (L' : Submodule (𝓞 X.E) (Sp X.E b)) (cA c c' : ℕ) (Ξ : HomE X.E a b → ℂ), A.IndAdd a b S (cA * (c * c')) → IsSdLat L → IsSdLat L' → 0 < cA → 0 < c → 0 < c' → (∀ x, Ξ x ≠ 0 → x ∈ homAt S L L') → (∀ x, ∀ y ∈ mulLat c (homAt S L L'), Ξ (x + y) = Ξ x) → ∃ R : Finset (HomE X.E a b), R.card ≤ c ^ (Module.finrank ℚ X.E * a * b) ∧ ∀ z, latSum (divLat cA (homAt S L L')) (mulLat (c * c') (homAt S L L')) (fun x => Ξ x * A.thInd S L L' (c * c') x z) = ∑ x ∈ R, Ξ x * A.thInd S L L' c x z := by
  intro X A a b S L L' cA c c' Ξ hadd hL hL' hcA hc hc' hsupp hinv
  have hdiv : ∀ (n : ℕ) x, x ∈ homAt S L L' → x ∈ divLat n (homAt S L L') := fun n x hx =>
    Submodule.smul_mem (homAt S L L') (n : 𝓞 X.E) hx
  have hone : ∀ x, x ∈ divLat 1 (homAt S L L') → x ∈ homAt S L L' := fun x hx => by
    simpa [divLat] using hx
  have hBC : mulLat (c * c') (homAt S L L') ≤ mulLat c (homAt S L L') := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨(c' : 𝓞 X.E) • x, Submodule.smul_mem _ _ hx, ?_⟩
    simp only [LinearMap.smul_apply, LinearMap.id_apply, Nat.cast_mul, mul_smul]
  have hCG : mulLat c (homAt S L L') ≤ divLat 1 (homAt S L L') := by
    rintro _ ⟨x, hx, rfl⟩
    exact hdiv 1 _ (Submodule.smul_mem (homAt S L L') (c : 𝓞 X.E) hx)
  have hfin := (GlobalTheory.SemilocalClasses.finite_card_classes X.E a b S L L' cA (c * c') hL.1 hL'.1 hcA (Nat.mul_pos hc hc')).1
  have hcard := (GlobalTheory.SemilocalClasses.finite_card_classes X.E a b S L L' 1 c hL.1 hL'.1 Nat.one_pos hc).2
  obtain ⟨R, hR, hRc, hsum⟩ := latSum_tower_reps X.E (HomE X.E a b) (divLat cA (homAt S L L'))
    (divLat 1 (homAt S L L')) (mulLat c (homAt S L L')) (mulLat (c * c') (homAt S L L')) hBC hCG
    (fun x hx => hdiv cA x (hone x hx)) hfin
  refine ⟨R, by rw [hRc]; simpa using hcard, fun z => ?_⟩
  rw [hsum]
  · refine Finset.sum_congr rfl fun x hx => ?_
    rw [hadd L L' c c' x hc hc' ⟨hL, hL', Nat.mul_pos hc hc', Dvd.intro_left _ rfl, hdiv _ x (hone x (hR x hx))⟩ z]
    unfold latSum
    rw [mul_finsum]
    exact finsum_congr fun q => by beta_reduce; rw [hinv x _ (Subtype.property _)]
  · intro x hx
    exact hdiv 1 x (hsupp x (left_ne_zero_of_mul hx))
  · intro x y hxy
    rw [thInd_congr_of_sub_mem A S L L' (c * c') x y hxy]
    have := hinv y _ (hBC hxy)
    rw [add_sub_cancel] at this
    rw [this]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCombinationInHodgeFiltration
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HodgeUnif

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ}

theorem isDiff_mul (hA : IsAbelianScheme A) (u : HolUnif A L g) {w w' : Fin g → ℂ} {v v' : epsR ℂ ⟶ A}
    (hv : IsTangent v) (hv' : IsTangent v') (h : u.IsDiff w v) (h' : u.IsDiff w' v') :
    u.IsDiff (w + w') (v * v') := by
  have := GlobalTheory.isDiff_sum_smul_of_isLieComb A hA L g 2 u ![v, v'] ![w, w'] ![1, 1] (v * v')
    (fun i => by fin_cases i <;> assumption) (fun i => by fin_cases i <;> assumption)
    ⟨![v, v'], fun i => by
      fin_cases i <;> (rw [← GlobalTheory.GrpTangent.epsScale_left]; simp [GlobalTheory.GrpTangent.epsScale_one]),
      by simp [List.ofFn_succ]⟩
  simpa [Fin.sum_univ_two] using this

theorem isDiff_smul (hA : IsAbelianScheme A) (u : HolUnif A L g) {w : Fin g → ℂ} {v : epsR ℂ ⟶ A}
    (hv : IsTangent v) (h : u.IsDiff w v) (r : ℂ) :
    u.IsDiff (r • w) (GlobalTheory.GrpTangent.epsScale r ≫ v) := by
  have := GlobalTheory.isDiff_sum_smul_of_isLieComb A hA L g 1 u ![v] ![w] ![r] (GlobalTheory.GrpTangent.epsScale r ≫ v)
    (fun i => by fin_cases i; assumption) (fun i => by fin_cases i; assumption)
    ⟨![GlobalTheory.GrpTangent.epsScale r ≫ v], fun i => by
      fin_cases i; simp [Over.comp_left, GlobalTheory.GrpTangent.epsScale_left], by simp⟩
  simpa using this

theorem exists_isLieImage_isDiff (hA : IsAbelianScheme A) (u : HolUnif A L g) (P : u.Λ →+ HdR A)
    (hP : ∀ x : u.Λ, ∃ v, IsLieImage (P x) v ∧ u.IsDiff x v) (c : u.Λ →₀ ℂ) :
    ∃ v, IsLieImage (c.sum fun x r ↦ r • P x) v ∧ u.IsDiff (c.sum fun x r ↦ r • (x : Fin g → ℂ)) v := by
  induction c using Finsupp.induction with
  | zero =>
    refine ⟨1, by simpa using isLieImage_one_iff.2 (zero_mem (Fil A)), ?_⟩
    simpa [Hom.one_def] using GlobalTheory.ArchMetricCompare.isDiff_zero u
  | single_add a b f _ _ ih =>
    obtain ⟨v, hv, hd⟩ := ih
    obtain ⟨v₀, hv₀, hd₀⟩ := hP a
    refine ⟨(GlobalTheory.GrpTangent.epsScale b ≫ v₀) * v, ?_, ?_⟩
    · rw [Finsupp.sum_add_index' (h := fun x r ↦ r • P x) (fun _ ↦ zero_smul ℂ _)
        (fun _ _ _ ↦ add_smul _ _ _), Finsupp.sum_single_index (h := fun x r ↦ r • P x) (zero_smul ℂ _)]
      exact (hv₀.smul b).add hv
    · rw [Finsupp.sum_add_index' (h := fun (x : u.Λ) (r : ℂ) ↦ r • (x : Fin g → ℂ)) (fun _ ↦ zero_smul ℂ _)
        (fun _ _ _ ↦ add_smul _ _ _),
        Finsupp.sum_single_index (h := fun (x : u.Λ) (r : ℂ) ↦ r • (x : Fin g → ℂ)) (zero_smul ℂ _)]
      exact isDiff_mul hA u (hv₀.smul b).1 hv.1 (isDiff_smul hA u hv₀.1 hd₀ b) hd

theorem sum_smul_mem_fil_iff :
    ∀ (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → ∀ (L : LB A.left) (g : ℕ) (u : HolUnif A L g)
    (P : u.Λ →+ HdR A), LieExact A → (∀ x : u.Λ, ∃ v, IsLieImage (P x) v ∧ u.IsDiff x v) →
    ∀ c : u.Λ →₀ ℂ, (c.sum fun x r ↦ r • P x) ∈ Fil A ↔ (c.sum fun x r ↦ r • (x : Fin g → ℂ)) = 0 := by
  intro A _ hA L g u P hE hP c
  obtain ⟨v, hv, hd⟩ := exists_isLieImage_isDiff hA u P hP c
  rw [← isLieImage_one_iff, GlobalTheory.ArchMetricCompare.isDiff_ne_iff u hv.1 hd, ← Hom.one_def]
  exact ⟨fun h ↦ (hE.1 _).unique hv h, fun e ↦ e ▸ hv⟩

end GlobalTheory.HodgeUnif
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeMovePreservingLocalParts
section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.ColumnNormCompare
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (recFields recPrimes recWts recSeam recGlob Twist)

namespace GlobalTheory.SemilocalBasis

def awayFrom {R : Type} [CommRing R] [IsDomain R] (SB : Finset (HeightOneSpectrum R)) :
    Submonoid R where
  carrier := {s | s ≠ 0 ∧ ∀ P ∈ SB, s ∉ P.asIdeal}
  one_mem' := ⟨one_ne_zero, fun P _ h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)⟩
  mul_mem' := fun {a b} ha hb => ⟨mul_ne_zero ha.1 hb.1, fun P hP h =>
    (P.isPrime.mem_or_mem h).elim (ha.2 P hP) (hb.2 P hP)⟩

theorem awayFrom_le {R : Type} [CommRing R] [IsDomain R] (SB : Finset (HeightOneSpectrum R)) :
    awayFrom SB ≤ nonZeroDivisors R := fun _ h => mem_nonZeroDivisors_of_ne_zero h.1

theorem isPrincipalIdealRing_awayFrom {R : Type} [CommRing R] [IsDedekindDomain R]
    (SB : Finset (HeightOneSpectrum R)) (A : Type) [CommRing A] [IsDomain A] [Algebra R A]
    [IsLocalization (awayFrom SB) A] : IsPrincipalIdealRing A := by
  classical
  haveI : IsDedekindDomain A := IsLocalization.isDedekindDomain R (awayFrom_le SB) A
  apply IsPrincipalIdealRing.of_finite_primes
  let T : Finset (Ideal R) := insert ⊥ (SB.image (·.asIdeal))
  have hT : ∀ Q ∈ T, Q.IsPrime := by
    intro Q hQ
    rcases Finset.mem_insert.1 hQ with rfl | hQ
    · exact Ideal.isPrime_bot
    · obtain ⟨P, _, rfl⟩ := Finset.mem_image.1 hQ
      exact P.isPrime
  have hinj : Function.Injective (fun I : Ideal A => I.comap (algebraMap R A)) := by
    intro I J h
    rw [← IsLocalization.map_comap (awayFrom SB) A I, ← IsLocalization.map_comap (awayFrom SB) A J]
    exact congrArg _ h
  refine ((T.finite_toSet).preimage hinj.injOn).subset ?_
  intro I hI
  have hI' : I.IsPrime := hI
  have hsub : ((I.comap (algebraMap R A) : Ideal R) : Set R) ⊆ ⋃ i ∈ (T : Set (Ideal R)), ((id i : Ideal R) : Set R) := by
    intro s hs
    by_contra hn
    simp only [Set.mem_iUnion, not_exists, id] at hn
    have hS : s ∈ awayFrom SB := by
      refine ⟨fun h0 => hn ⊥ (by simp [T]) (by simp [h0]), fun P hP h => hn P.asIdeal ?_ h⟩
      exact Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hP))
    exact hI'.ne_top (Ideal.eq_top_of_isUnit_mem _ hs (IsLocalization.map_units A ⟨s, hS⟩))
  obtain ⟨Q, hQ, hle⟩ := (Ideal.subset_union_prime (⊥ : Ideal R) ⊥ (fun i hi _ _ => hT i hi)).1 hsub
  show I.comap (algebraMap R A) ∈ (T : Set (Ideal R))
  by_cases h0 : I.comap (algebraMap R A) = ⊥
  · rw [h0]; simp [T]
  · have hmax : (I.comap (algebraMap R A)).IsMaximal :=
      Ring.DimensionLEOne.maximalOfPrime h0 (Ideal.comap_isPrime _ _)
    rw [hmax.eq_of_le (hT Q hQ).ne_top hle]
    exact hQ

theorem exists_basis {R : Type} [CommRing R] [IsDedekindDomain R] (K : Type) [Field K]
    [Algebra R K] [IsFractionRing R K] (n : ℕ) (SB : Finset (HeightOneSpectrum R))
    (N : Submodule R (Fin n → K)) (hN : Submodule.IsLattice K N) :
    ∃ v : Module.Basis (Fin n) K (Fin n → K), (∀ i, v i ∈ N) ∧
      ∀ x ∈ N, ∃ s ∈ awayFrom SB, s • x ∈ Submodule.span R (Set.range v) := by
  classical
  let A : Subalgebra R K := Localization.subalgebra K (awayFrom SB) (awayFrom_le SB)
  haveI : IsLocalization (awayFrom SB) A :=
    Localization.subalgebra.isLocalization_subalgebra K (awayFrom SB) (awayFrom_le SB)
  haveI : IsPrincipalIdealRing A := isPrincipalIdealRing_awayFrom SB A
  haveI : IsFractionRing A K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (awayFrom SB) A K

  have clear : ∀ (X : Set (Fin n → K)) (x : Fin n → K), x ∈ Submodule.span A X →
      ∃ s ∈ awayFrom SB, s • x ∈ Submodule.span R X := by
    intro X x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact ⟨1, one_mem _, by simpa using Submodule.subset_span hx⟩
    | zero => exact ⟨1, one_mem _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨s, hs, hsx⟩ := hx
      obtain ⟨t, ht, hty⟩ := hy
      refine ⟨s * t, mul_mem hs ht, ?_⟩
      rw [smul_add]
      refine add_mem ?_ ?_
      · rw [mul_comm, mul_smul]; exact Submodule.smul_mem _ _ hsx
      · rw [mul_smul]; exact Submodule.smul_mem _ _ hty
    | smul a x _ hx =>
      obtain ⟨s, hs, hsx⟩ := hx
      obtain ⟨⟨r, t⟩, hr⟩ := IsLocalization.surj (awayFrom SB) a
      refine ⟨s * t, mul_mem hs t.2, ?_⟩
      have : (t : R) • a • x = r • x := by
        rw [← algebraMap_smul A (t : R), ← mul_smul, mul_comm, hr, algebraMap_smul]
      rw [mul_smul, this, smul_comm]
      exact Submodule.smul_mem _ _ hsx
  let M : Submodule A (Fin n → K) := Submodule.span A (N : Set (Fin n → K))
  haveI hM : Submodule.IsLattice K M := by
    refine ⟨?_, ?_⟩
    · obtain ⟨X, hX⟩ := hN.fg
      refine ⟨X, ?_⟩
      simp only [M, ← hX]
      exact (Submodule.span_span_of_tower R A _).symm
    · simp only [M]
      rw [Submodule.span_span_of_tower]
      exact hN.span_eq_top
  haveI : Module.Free A M := Submodule.IsLattice.free K M
  haveI : Module.Finite A M := Module.Finite.iff_fg.2 hM.fg
  have hrk : Module.finrank A M = n := by
    simpa using Submodule.IsLattice.finrank_of_pi K M
  let b : Module.Basis (Fin n) A M := Module.finBasisOfFinrankEq A M hrk
  have hb : ∀ i, ∃ s ∈ awayFrom SB, s • (b i : Fin n → K) ∈ N := by
    intro i
    obtain ⟨s, hs, h⟩ := clear _ _ (b i).2
    exact ⟨s, hs, by simpa using h⟩
  choose s hs hsb using hb
  let b' : Module.Basis (Fin n) A M :=
    b.isUnitSMul (w := fun i => algebraMap R A (s i)) (fun i => IsLocalization.map_units A ⟨s i, hs i⟩)
  have hb' : ∀ i, (b' i : Fin n → K) = s i • (b i : Fin n → K) := by
    intro i
    simp only [b', Module.Basis.isUnitSMul_apply, Submodule.coe_smul, algebraMap_smul]
    try rfl
  refine ⟨b'.extendOfIsLattice K, fun i => ?_, fun x hx => ?_⟩
  · rw [Module.Basis.extendOfIsLattice_apply, hb']
    exact hsb i
  · apply clear
    have hxM : x ∈ M := Submodule.subset_span hx
    have h1 := b'.sum_repr ⟨x, hxM⟩
    have h2 : x = ∑ i, b'.repr ⟨x, hxM⟩ i • (b' i : Fin n → K) := by
      have := congrArg Subtype.val h1
      rw [AddSubmonoidClass.coe_finset_sum] at this
      exact this.symm
    rw [h2]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, ?_⟩)
    rw [Module.Basis.extendOfIsLattice_apply]

theorem mem_localization_iff {R : Type} [CommRing R] {W : Type} [AddCommGroup W] [Module R W]
    (p : Ideal R) [p.IsPrime] (L : Submodule R W) (x : W) :
    x ∈ Formalism.HermitianLatticesTheory.localization₂ p L ↔ ∃ s, s ∉ p ∧ s • x ∈ L := Iff.rfl

theorem stdLat_eq_span (E : Type) [Field E] (n : ℕ) :
    Formalism.L2.Col.stdLat E n = Submodule.span (𝓞 E) (Set.range (Pi.basisFun E (Fin n))) := by
  classical
  apply le_antisymm
  · intro x hx
    have hx' : ∀ i, ∃ r : 𝓞 E, algebraMap (𝓞 E) E r = x i := fun i =>
      Submodule.mem_one.1 (hx i (Set.mem_univ _))
    choose r hr using hx'
    have : x = ∑ i, r i • Pi.basisFun E (Fin n) i := by
      conv_lhs => rw [← (Pi.basisFun E (Fin n)).sum_repr x]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Pi.basisFun_repr, ← hr, algebraMap_smul]
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩ j _
    rw [Pi.basisFun_apply]
    by_cases h : j = i
    · subst h
      exact Submodule.mem_one.2 ⟨1, by simp⟩
    · exact Submodule.mem_one.2 ⟨0, by simp [h]⟩

theorem exists_equiv (E : Type) [Field E] [NumberField E] (n : ℕ)
    (SB : Finset (HeightOneSpectrum (𝓞 E))) (N : Submodule (𝓞 E) (Sp E n))
    (hN : Submodule.IsLattice E N) :
    ∃ γ : Sp E n ≃ₗ[E] Sp E n, (∀ x ∈ Formalism.L2.Col.stdLat E n, γ x ∈ N) ∧
      ∀ P ∈ SB, ∀ x, γ x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N ↔
        x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Formalism.L2.Col.stdLat E n) := by
  obtain ⟨v, hv, hgen⟩ := exists_basis E n SB N hN
  let γ : Sp E n ≃ₗ[E] Sp E n := (Pi.basisFun E (Fin n)).equiv v (Equiv.refl _)
  have key : ∀ x, x ∈ Formalism.L2.Col.stdLat E n ↔ γ x ∈ Submodule.span (𝓞 E) (Set.range v) := by
    intro x
    have hmap : (Formalism.L2.Col.stdLat E n).map ((γ.restrictScalars (𝓞 E)) : Sp E n →ₗ[𝓞 E] Sp E n)
        = Submodule.span (𝓞 E) (Set.range v) := by
      rw [stdLat_eq_span, Submodule.map_span, ← Set.range_comp]
      congr 2
      funext i
      exact (Pi.basisFun E (Fin n)).equiv_apply i v (Equiv.refl _)
    rw [← hmap]
    constructor
    · intro h
      exact ⟨x, h, rfl⟩
    · rintro ⟨y, hy, h⟩
      have : y = x := γ.injective h
      exact this ▸ hy
  have hle : Submodule.span (𝓞 E) (Set.range v) ≤ N := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hv i
  have hsm : ∀ (s : 𝓞 E) x, γ (s • x) = s • γ x := fun s x =>
    (γ.restrictScalars (𝓞 E)).map_smul s x
  refine ⟨γ, fun x hx => hle ((key x).1 hx), fun P hP x => ?_⟩
  rw [mem_localization_iff, mem_localization_iff]
  constructor
  · rintro ⟨s, hs, h⟩
    obtain ⟨t, ht, h'⟩ := hgen _ h
    refine ⟨t * s, fun hm => (P.isPrime.mem_or_mem hm).elim (ht.2 P hP) hs, ?_⟩
    rw [key, hsm, mul_smul]
    exact h'
  · rintro ⟨s, hs, h⟩
    refine ⟨s, hs, hle ?_⟩
    rw [← hsm]
    exact (key _).1 h

end GlobalTheory.SemilocalBasis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearNormalisationClosedSubscheme
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section

namespace GlobalTheory.HomFixUniv

theorem factors_quot_iff {P : Type} [CommRing P] (I : Ideal P) (T : Scheme.{0}) (g : T ⟶ Sp P) :
    (∃ w : T ⟶ Sp (P ⧸ I), w ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) = g) ↔
      ∀ x ∈ I, g.appTop ((Scheme.ΓSpecIso (CommRingCat.of P)).inv x) = 0 := by
  constructor
  · rintro ⟨w, rfl⟩ x hx
    have e : (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of P)).inv x) =
        (Scheme.ΓSpecIso (CommRingCat.of (P ⧸ I))).inv (Ideal.Quotient.mk I x) := by
      rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]; rfl
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, e,
      Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero, map_zero]
  · intro h
    let φ : CommRingCat.of P ⟶ Γ(T, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of P)).inv ≫ g.appTop
    let ψ : CommRingCat.of (P ⧸ I) ⟶ Γ(T, ⊤) :=
      CommRingCat.ofHom (Ideal.Quotient.lift I φ.hom (fun x hx => h x hx))
    refine ⟨T.toSpecΓ ≫ Spec.map ψ, ?_⟩
    have e : CommRingCat.ofHom (Ideal.Quotient.mk I) ≫ ψ = φ := by ext x; rfl
    rw [Category.assoc, ← Spec.map_comp, e]
    simp only [φ, Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv,
      Category.comp_id]

def normEq {Rg : Type} [CommRing Rg] {mA mB : ℕ} (α : Fin mA → Γ(Sp Rg, ⊤)) (β : Fin mB → Γ(Sp Rg, ⊤))
    (j : Fin mB) : MvPolynomial (Fin (mA * mB)) Rg :=
  MvPolynomial.C ((Scheme.ΓSpecIso (CommRingCat.of Rg)).hom (β j)) -
    ∑ i, MvPolynomial.X (finProdFinEquiv (i, j)) *
      MvPolynomial.C ((Scheme.ΓSpecIso (CommRingCat.of Rg)).hom (α i))

theorem appTop_affπ {Rg : Type} [CommRing Rg] {N : ℕ} (a : Γ(Sp Rg, ⊤)) :
    (affπ Rg N).appTop a = (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin N) Rg))).inv
      (MvPolynomial.C ((Scheme.ΓSpecIso (CommRingCat.of Rg)).hom a)) := by
  conv_lhs => rw [← (Scheme.ΓSpecIso (CommRingCat.of Rg)).hom_inv_id_apply a]
  rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]; rfl

theorem normal_iff {Rg : Type} [CommRing Rg] {mA mB : ℕ} (α : Fin mA → Γ(Sp Rg, ⊤)) (β : Fin mB → Γ(Sp Rg, ⊤))
    (T : Scheme.{0}) (g : T ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)) :
    Normal (g ≫ affπ Rg (mA * mB)) (matOf g) α β ↔
      ∀ j, g.appTop ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin (mA * mB)) Rg))).inv (normEq α β j)) = 0 := by
  refine forall_congr' fun j => ?_
  rw [normEq, map_sub, map_sub, sub_eq_zero, map_sum, map_sum]
  simp only [map_mul, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, appTop_affπ, matOf, coord]

end GlobalTheory.HomFixUniv

namespace GlobalTheory.HomFixUniv

theorem normal_closed : ∀ (Rg : Type) [CommRing Rg] (mA mB : ℕ) (α : Fin mA → Γ(Sp Rg, ⊤)) (β : Fin mB → Γ(Sp Rg, ⊤)), ∃ (Z : Scheme.{0}) (ιZ : Z ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)), IsClosedImmersion ιZ ∧ ∀ (T : Scheme.{0}) (g : T ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)), (GlobalTheory.HomFixUniv.Normal (g ≫ affπ Rg (mA * mB)) (matOf g) α β ↔ ∃ w : T ⟶ Z, w ≫ ιZ = g) := by
  intro Rg _ mA mB α β
  let I : Ideal (MvPolynomial (Fin (mA * mB)) Rg) := Ideal.span (Set.range (normEq α β))
  refine ⟨Sp (MvPolynomial (Fin (mA * mB)) Rg ⧸ I), Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)),
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective, fun T g => ?_⟩
  rw [factors_quot_iff, normal_iff]
  let φ : MvPolynomial (Fin (mA * mB)) Rg →+* Γ(T, ⊤) :=
    g.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin (mA * mB)) Rg))).inv.hom
  change (∀ j, φ (normEq α β j) = 0) ↔ ∀ x ∈ I, φ x = 0
  constructor
  · intro h x hx
    have hle : I ≤ RingHom.ker φ := by
      rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      exact h j
    exact hle hx
  · intro h j
    exact h _ (Ideal.subset_span ⟨j, rfl⟩)

end GlobalTheory.HomFixUniv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogarithmIntegersAdaptedBasisNoLieComponentsStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.logarithm_integers_adapted_basis_no_lie_components : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (k : ℕ) (e0 : Fin d ⊕ Fin k → MvPowerSeries (Fin d) C) (lb : Module.Basis (Fin k) O G.dual.Lie), IsBasis c.μ e0 → IsAdapted (RingHom.id O) c.μ e0 → (∀ j, c.IsLie (e0 (Sum.inr j)) (lb j)) → ∀ h : MvPowerSeries (Fin d) C, QL c.μ ⊤ h → cob1 (up C c.μ) h = 0 → ∀ a : Fin d ⊕ Fin k → O, In (⊤ : Ideal O) (h - comb a e0) → (∀ j, a (Sum.inr j) = 0) ∧ ∀ i, lin h i = algebraMap O C (a (Sum.inl i)) := by
  first | exact @GlobalTheory.QLog.RedO.main | exact GlobalTheory.QLog.RedO.main | (intros; apply GlobalTheory.QLog.RedO.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicityLinearCharacterEqCharacterSumStatement
section
open Formalism.L2.DIV NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplicity_linearCharacter_eq_characterSum : ∀ (K : Type) [Field K] [CharZero K] (G : Type) [Group G] [Fintype G] (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] (τ : Representation K G W) (H : Subgroup G) [Fintype H] (ψ : H →* Kˣ), (Formalism.IndefR.IndefiniteEpsilonOperator.nOf τ ⟨H, ψ⟩ : K) = (Nat.card H : K)⁻¹ * ∑ h : H, Formalism.IndefR.TransferLatticeStatement.charOf τ (h : G) * (((ψ h)⁻¹ : Kˣ) : K) := by
  first | exact @GlobalTheory.multiplicity_linearCharacter_eq_characterSum.nOf_eq_charSum | exact GlobalTheory.multiplicity_linearCharacter_eq_characterSum.nOf_eq_charSum | (intros; apply GlobalTheory.multiplicity_linearCharacter_eq_characterSum.nOf_eq_charSum <;> assumption)
end

