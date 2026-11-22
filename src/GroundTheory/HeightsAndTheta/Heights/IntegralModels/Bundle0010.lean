import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle0006
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle0007

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.PGlueBundles
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

variable {X : Scheme.{0}}

lemma mul_not_mem_prime_iff {P : Ideal ℤ} (hP : P.IsPrime) (a b : ℤ) :
    a * b ∉ P ↔ a ∉ P ∧ b ∉ P := by
  rw [hP.mul_mem_iff_mem_or_mem, not_or]

lemma invOpen_mul_eq_inf (f : X ⟶ SpecZ) (a b : ℤ) :
    invOpen f (a * b) = invOpen f a ⊓ invOpen f b := by
  ext x
  change a * b ∉ _ ↔ a ∉ _ ∧ b ∉ _
  exact mul_not_mem_prime_iff (PrimeSpectrum.isPrime _) a b

lemma invOpen_le_of_dvd' (f : X ⟶ SpecZ) {a b : ℤ} (h : a ∣ b) : invOpen f b ≤ invOpen f a := by
  obtain ⟨c, rfl⟩ := h
  exact invOpen_mul_le_left f a c

lemma not_dvd_prod_erase (S : Finset Nat.Primes) (p : Nat.Primes) :
    ¬ (p : ℕ) ∣ ∏ q ∈ S.erase p, (q : ℕ) := by
  intro h
  obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff p.2.prime _).1 h
  have : p = q := Subtype.ext ((Nat.prime_dvd_prime_iff_eq p.2 q.2).1 hpq)
  subst this
  exact Finset.notMem_erase _ _ hq

lemma primeProd_eq_cast (S : Finset Nat.Primes) :
    primeProd S = ((∏ q ∈ S, (q : ℕ) : ℕ) : ℤ) := by
  simp [primeProd]

theorem GlueBundles.localPiece (hSB : SpreadBundle.Statement) (hSI : SpreadIso.Statement)
    (hVR : VectorBundleRestrict.Statement) (f : X ⟶ SpecZ) [LocallyOfFiniteType f] [QuasiCompact f]
    (S : Finset Nat.Primes) (E₀ : (invOpen f (primeProd S) : Scheme.{0}).Modules)
    (hE₀ : IsVectorBundle E₀) (p : S) (Ep : (baseChange f (ZLoc p)).Modules) (hEp : IsVectorBundle Ep)
    (β : (Scheme.Modules.pullback (ratToLoc f p)).obj Ep ≅
      (Scheme.Modules.pullback (toInvOpen f ℚ (primeProd S)
        (isUnit_intCast_rat _ (primeProd_ne_zero S)))).obj E₀) :
    ∃ (n : ℕ) (hn : ¬ (((p : Nat.Primes) : ℕ) : ℤ) ∣ (n : ℤ)),
      (∀ q ∈ S, q ≠ (p : Nat.Primes) → ((q : ℕ) : ℤ) ∣ (n : ℤ)) ∧
      ∃ (F : (invOpen f n : Scheme.{0}).Modules), IsVectorBundle F ∧
      ∃ (ψ' : (Scheme.Modules.pullback (X.homOfLE
            (inf_le_left : invOpen f n ⊓ invOpen f (primeProd S) ≤ invOpen f n))).obj F ≅
          (Scheme.Modules.pullback (X.homOfLE
            (inf_le_right : invOpen f n ⊓ invOpen f (primeProd S) ≤ invOpen f (primeProd S)))).obj E₀)
        (δ : (Scheme.Modules.pullback (toInvOpen f (ZLoc p) n (isUnit_intCast_zLoc p n hn))).obj F ≅ Ep),
      ∀ (E : X.Modules) (e₀ : (Scheme.Modules.pullback (invOpen f (primeProd S)).ι).obj E ≅ E₀)
        (eU : (Scheme.Modules.pullback (invOpen f n).ι).obj E ≅ F),
        pullbackCompIso (X.homOfLE_ι (inf_le_right :
            invOpen f n ⊓ invOpen f (primeProd S) ≤ invOpen f (primeProd S))) e₀ =
          pullbackCompIso (X.homOfLE_ι (inf_le_left :
            invOpen f n ⊓ invOpen f (primeProd S) ≤ invOpen f n)) eU ≪≫ ψ' →
        pullbackCompIso (toInvOpen_ι f ℚ (primeProd S)
            (isUnit_intCast_rat _ (primeProd_ne_zero S))) e₀ =
          pullbackCompIso (ratToLoc_baseChangeMap f p)
            (pullbackCompIso (toInvOpen_ι f (ZLoc p) n (isUnit_intCast_zLoc p n hn)) eU ≪≫ δ) ≪≫ β := by
  classical
  obtain ⟨pp, hpS⟩ := p
  obtain ⟨m₀, hm₀pos, hpm₀, hspread⟩ := hSB X f pp Ep hEp
  set M : ℕ := ∏ q ∈ S, (q : ℕ) with hMdef
  set N : ℕ := m₀ * ∏ q ∈ S.erase pp, (q : ℕ) with hNdef
  have hpNnat : ¬ (pp : ℕ) ∣ N := fun h =>
    ((Nat.Prime.dvd_mul pp.2).1 h).elim hpm₀ (not_dvd_prod_erase S pp)
  have hpN : ¬ ((pp : ℕ) : ℤ) ∣ (N : ℤ) := by exact_mod_cast hpNnat
  obtain ⟨E', hE', ⟨σ⟩⟩ := hspread N (dvd_mul_right _ _) hpN
  have hMpos : 0 < M := Finset.prod_pos fun q _ => q.2.pos
  have hNpos : 0 < N := Nat.mul_pos hm₀pos (Finset.prod_pos fun q _ => q.2.pos)
  set a : ℕ := N * M with hadef
  have ha : 0 < a := Nat.mul_pos hNpos hMpos
  have hm : primeProd S = (M : ℤ) := primeProd_eq_cast S
  have haN : invOpen f (a : ℤ) ≤ invOpen f (N : ℤ) :=
    invOpen_le_of_dvd' f (by exact_mod_cast dvd_mul_right N M)
  have haM : invOpen f (a : ℤ) ≤ invOpen f (primeProd S) := by
    rw [hm]
    exact invOpen_le_of_dvd' f (by exact_mod_cast dvd_mul_left M N)
  have hFa : IsVectorBundle ((Scheme.Modules.pullback (X.homOfLE haN)).obj E') :=
    hVR _ _ (X.homOfLE haN) E' hE'
  have hGa : IsVectorBundle ((Scheme.Modules.pullback (X.homOfLE haM)).obj E₀) :=
    hVR _ _ (X.homOfLE haM) E₀ hE₀
  have uQa : IsUnit ((a : ℤ) : ℚ) := isUnit_intCast_rat a (by exact_mod_cast ha.ne')
  have uQm : IsUnit ((primeProd S : ℤ) : ℚ) := isUnit_intCast_rat _ (primeProd_ne_zero S)
  have uPN : IsUnit ((N : ℤ) : ZLoc pp) := isUnit_intCast_zLoc pp N hpN
  have uQN : IsUnit ((N : ℤ) : ℚ) := isUnit_intCast_rat N (by exact_mod_cast hNpos.ne')
  have e1 : toInvOpen f ℚ a uQa ≫ X.homOfLE haN = ratToLoc f pp ≫ toInvOpen f (ZLoc pp) N uPN := by
    rw [toInvOpen_homOfLE f ℚ uQa uQN haN, ← cancel_mono (invOpen f N).ι, Category.assoc,
      toInvOpen_ι, toInvOpen_ι, ratToLoc_baseChangeMap]
  have e2 : toInvOpen f ℚ a uQa ≫ X.homOfLE haM = toInvOpen f ℚ (primeProd S) uQm :=
    toInvOpen_homOfLE f ℚ uQa uQm haM
  obtain ⟨m', hm', ψ, hψ⟩ := hSI X f a ha _ _ hFa hGa
    ((pullbackCompIso e1 (Iso.refl ((Scheme.Modules.pullback (X.homOfLE haN)).obj E'))).symm ≪≫
      pullbackCompIso (rfl : ratToLoc f pp ≫ toInvOpen f (ZLoc pp) N uPN = _) σ ≪≫ β ≪≫
      pullbackCompIso e2 (Iso.refl ((Scheme.Modules.pullback (X.homOfLE haM)).obj E₀)))
  obtain ⟨k, m'', hpm'', hm'eq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm'.ne' (pp : ℕ) pp.2.one_lt.ne'
  set n : ℕ := N * m'' with hndef
  have hpn : ¬ ((pp : ℕ) : ℤ) ∣ (n : ℤ) := by
    have : ¬ (pp : ℕ) ∣ n := fun h => ((Nat.Prime.dvd_mul pp.2).1 h).elim hpNnat hpm''
    exact_mod_cast this
  have hqn : ∀ q ∈ S, q ≠ pp → ((q : ℕ) : ℤ) ∣ (n : ℤ) := by
    intro q hq hne
    have : (q : ℕ) ∣ n := Dvd.dvd.mul_right (Dvd.dvd.mul_left
      (Finset.dvd_prod_of_mem (fun r : Nat.Primes => (r : ℕ)) (Finset.mem_erase.2 ⟨hne, hq⟩)) _) _
    exact_mod_cast this
  have hUN : invOpen f (n : ℤ) ≤ invOpen f (N : ℤ) :=
    invOpen_le_of_dvd' f (by exact_mod_cast dvd_mul_right N m'')
  have hF : IsVectorBundle ((Scheme.Modules.pullback (X.homOfLE hUN)).obj E') :=
    hVR _ _ (X.homOfLE hUN) E' hE'
  have hWam : invOpen f n ⊓ invOpen f (primeProd S) ≤ invOpen f ((a : ℤ) * (m' : ℤ)) := by
    rintro x ⟨hxU, hxV⟩
    have hP := PrimeSpectrum.isPrime (f.base x)
    change (n : ℤ) ∉ (f.base x).asIdeal at hxU
    change primeProd S ∉ (f.base x).asIdeal at hxV
    change (a : ℤ) * (m' : ℤ) ∉ (f.base x).asIdeal
    rw [hm] at hxV
    rw [hndef, Nat.cast_mul, mul_not_mem_prime_iff hP] at hxU
    have hpP : ((pp : ℕ) : ℤ) ∉ (f.base x).asIdeal := fun h => hxV (by
      obtain ⟨c, hc⟩ : ((pp : ℕ) : ℤ) ∣ (M : ℤ) := by
        exact_mod_cast Finset.dvd_prod_of_mem (fun q : Nat.Primes => (q : ℕ)) hpS
      rw [hc]
      exact Ideal.mul_mem_right _ _ h)
    have hk : ((pp : ℕ) : ℤ) ^ k ∉ (f.base x).asIdeal := fun h => hpP (hP.mem_of_pow_mem k h)
    rw [hadef, hm'eq]
    push_cast
    rw [mul_not_mem_prime_iff hP, mul_not_mem_prime_iff hP, mul_not_mem_prime_iff hP]
    exact ⟨⟨hxU.1, hxV⟩, hk, hxU.2⟩
  have e7 : (X.homOfLE hWam ≫ X.homOfLE (invOpen_mul_le_left f a m')) ≫ X.homOfLE haN =
      X.homOfLE (inf_le_left : invOpen f n ⊓ invOpen f (primeProd S) ≤ invOpen f n) ≫
        X.homOfLE hUN := by
    simp only [Scheme.homOfLE_homOfLE]
  have e8 : (X.homOfLE hWam ≫ X.homOfLE (invOpen_mul_le_left f a m')) ≫ X.homOfLE haM =
      X.homOfLE (inf_le_right : invOpen f n ⊓ invOpen f (primeProd S) ≤ invOpen f (primeProd S)) := by
    simp only [Scheme.homOfLE_homOfLE]
  have uPn : IsUnit ((n : ℤ) : ZLoc pp) := isUnit_intCast_zLoc pp n hpn
  have h5 : toInvOpen f (ZLoc pp) n uPn ≫ X.homOfLE hUN = toInvOpen f (ZLoc pp) N uPN :=
    toInvOpen_homOfLE f _ uPn uPN hUN
  refine ⟨n, hpn, hqn, _, hF, starIso rfl e7 e8 ψ,
    (pullbackCompIso h5 (Iso.refl ((Scheme.Modules.pullback (X.homOfLE hUN)).obj E'))).symm ≪≫ σ, ?_⟩
  intro E e₀ eU hglue
  have hm''0 : m'' ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hm'eq
    omega
  have hnm : ((n : ℤ) * primeProd S : ℤ) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast (Nat.mul_pos hNpos
      (Nat.pos_of_ne_zero hm''0)).ne') (primeProd_ne_zero S)
  have hrange : Set.range (baseChangeMap f ℚ) ⊆
      Set.range (invOpen f n ⊓ invOpen f (primeProd S)).ι := by
    intro y hy
    have := range_baseChangeMap_subset f ℚ ((n : ℤ) * primeProd S) (isUnit_intCast_rat _ hnm) hy
    rw [Scheme.Opens.range_ι] at this ⊢
    rwa [invOpen_mul_eq_inf] at this
  have qW : IsOpenImmersion.lift _ _ hrange ≫ (invOpen f n ⊓ invOpen f (primeProd S)).ι =
      baseChangeMap f ℚ := IsOpenImmersion.lift_fac _ _ _
  have qV : IsOpenImmersion.lift _ _ hrange ≫ X.homOfLE (inf_le_right :
      invOpen f n ⊓ invOpen f (primeProd S) ≤ invOpen f (primeProd S)) =
      toInvOpen f ℚ (primeProd S) uQm := by
    rw [← cancel_mono (invOpen f (primeProd S)).ι, Category.assoc, Scheme.homOfLE_ι, qW, toInvOpen_ι]
  have qU : IsOpenImmersion.lift _ _ hrange ≫ X.homOfLE (inf_le_left :
      invOpen f n ⊓ invOpen f (primeProd S) ≤ invOpen f n) =
      ratToLoc f pp ≫ toInvOpen f (ZLoc pp) n uPn := by
    rw [← cancel_mono (invOpen f n).ι, Category.assoc, Scheme.homOfLE_ι, qW, Category.assoc,
      toInvOpen_ι, ratToLoc_baseChangeMap]
  have qt : IsOpenImmersion.lift _ _ hrange ≫ X.homOfLE hWam =
      toInvOpen f ℚ ((a : ℤ) * (m' : ℤ)) (isUnit_intCast_rat ((a : ℤ) * m') (by positivity)) := by
    rw [← cancel_mono (invOpen f ((a : ℤ) * (m' : ℤ))).ι, Category.assoc, Scheme.homOfLE_ι, qW,
      toInvOpen_ι]
  exact glue_compat_chase (X.homOfLE_ι _) (X.homOfLE_ι _) (toInvOpen_ι f ℚ _ _)
    (ratToLoc_baseChangeMap f pp) (toInvOpen_ι f (ZLoc pp) n uPn) h5 e1 e2
    (toInvOpen_homOfLE f ℚ _ _ _) rfl e7 e8 qV qU qt qW e₀ eU σ β ψ hψ hglue

theorem GlueBundles.proof (hSB : SpreadBundle.Statement) (hSI : SpreadIso.Statement)
    (hPC : PrimeOpensCover.Statement) (hGS : GlueModulesStar.Statement)
    (hVR : VectorBundleRestrict.Statement) (hVL : VectorBundleLocal.Statement) :
    GlueBundles.Statement := by
  classical
  intro X f _ _ S E₀ Ep hE₀ hEp β
  have key := fun p : S => GlueBundles.localPiece hSB hSI hVR f S E₀ hE₀ p (Ep p) (hEp p) (β p)
  choose n hn hqdiv F hF ψ' δ hcompat using key
  let mp : Nat.Primes → ℤ := fun q => if h : q ∈ S then (n ⟨q, h⟩ : ℤ) else 1
  have hmp : ∀ p : S, mp p = (n p : ℤ) := fun p => dif_pos p.2
  obtain ⟨hcover, hpair⟩ := hPC X f S mp
    (fun p hp => by rw [show mp p = (n ⟨p, hp⟩ : ℤ) from dif_pos hp]; exact hn ⟨p, hp⟩)
    (fun p hp q hq hqp => by
      rw [show mp p = (n ⟨p, hp⟩ : ℤ) from dif_pos hp]
      exact hqdiv ⟨p, hp⟩ q hq hqp)
  let U : S → X.Opens := fun p => invOpen f (n p)
  have hUsup : (⨆ q ∈ S, invOpen f (mp q)) = ⨆ p : S, U p := by
    rw [iSup_subtype']
    exact iSup_congr fun p => by rw [hmp]
  have hcov : invOpen f (primeProd S) ⊔ ⨆ p : S, U p = ⊤ := by
    rw [← hUsup]
    exact hcover
  have hpairU : ∀ i j : S, i ≠ j → U i ⊓ U j ≤ invOpen f (primeProd S) := by
    intro i j hij
    have := (hpair i i.2 j j.2 (fun h => hij (Subtype.ext h))).1
    rwa [hmp, hmp] at this
  obtain ⟨E, e₀, e, hglue⟩ := hGS X (invOpen f (primeProd S)) S U hcov hpairU E₀ F ψ'
  have hVB : IsVectorBundle E := by
    refine hVL X (Option S) (fun o => o.elim (invOpen f (primeProd S)) U) ?_ E ?_
    · rw [iSup_option]
      exact hcov
    · intro o
      cases o with
      | none => exact hE₀.of_iso e₀.symm
      | some p => exact (hF p).of_iso (e p).symm
  exact ⟨E, hVB, e₀, fun p => pullbackCompIso (toInvOpen_ι f (ZLoc p) (n p)
      (isUnit_intCast_zLoc p (n p) (hn p))) (e p) ≪≫ δ p,
    fun p => hcompat p E e₀ (e p) (hglue p)⟩

end

end GroundTheory.Heights₂.Heights.Model
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.PKrullAkizuki
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

namespace KrullAkizuki

theorem noetherian_and_dimensionLEOne
    {R : Type} [CommRing R] [IsDomain R]
    {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]
    {L : Type} [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra R L]
    [IsScalarTower R K L] (S : Subalgebra R L)
    (h : ∀ b : R, b ≠ 0 → IsFiniteLength R (S ⧸ Ideal.span {algebraMap R S b})) :
    IsNoetherianRing S ∧ Ring.DimensionLEOne S := by

  have hmeet : ∀ I : Ideal S, I ≠ ⊥ → ∃ b : R, b ≠ 0 ∧ algebraMap R S b ∈ I := by
    intro I hI
    obtain ⟨x, hxI, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    have halg : Algebra.IsAlgebraic R L :=
      (IsFractionRing.comap_isAlgebraic_iff (K := K)).mpr inferInstance
    have hx : IsAlgebraic R x :=
      Subalgebra.isAlgebraic_iff_isAlgebraic_val.mpr (halg.isAlgebraic _)
    obtain ⟨b, hb, hb0⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot (Ideal.comap_ne_bot_of_algebraic_mem hx0 hxI hx)
    exact ⟨b, hb0, hb⟩
  refine ⟨(isNoetherianRing_iff_ideal_fg S).mpr fun I => ?_, ⟨fun {P} hP0 hP => ?_⟩⟩
  · rcases eq_or_ne I ⊥ with rfl | hI
    · exact Submodule.fg_bot
    obtain ⟨b, hb0, hbI⟩ := hmeet I hI
    have : IsNoetherian R (S ⧸ Ideal.span {algebraMap R S b}) :=
      (isFiniteLength_iff_isNoetherian_isArtinian.mp (h b hb0)).1
    have : IsNoetherian S (S ⧸ Ideal.span {algebraMap R S b}) :=
      isNoetherian_of_tower R inferInstance
    refine Submodule.fg_of_fg_map_of_fg_inf_ker (Ideal.span {algebraMap R S b}).mkQ
      (IsNoetherian.noetherian _) ?_
    rw [Submodule.ker_mkQ, inf_eq_right.mpr ((Ideal.span_singleton_le_iff_mem I).mpr hbI)]
    exact Submodule.fg_span_singleton _
  · obtain ⟨b, hb0, hbP⟩ := hmeet P hP0
    have hle : Ideal.span {algebraMap R S b} ≤ P := (Ideal.span_singleton_le_iff_mem P).mpr hbP
    have hfl : IsFiniteLength R (S ⧸ P) :=
      (h b hb0).of_surjective (f := (Ideal.Quotient.factorₐ R hle).toLinearMap)
        (Ideal.Quotient.factor_surjective hle)
    have : IsArtinian R (S ⧸ P) := (isFiniteLength_iff_isNoetherian_isArtinian.mp hfl).2
    have : IsArtinianRing (S ⧸ P) := isArtinian_of_tower R inferInstance
    have : IsDomain (S ⧸ P) := Ideal.Quotient.isDomain P
    exact Ideal.Quotient.maximal_of_isField P (IsArtinianRing.isField_of_isDomain _)

theorem proof (h : KrullAkizukiQuotientLength.Statement) : KrullAkizuki.Statement := by
  refine ⟨fun R _ _ _ hR K _ _ _ L _ _ _ _ _ S => ?_, fun R _ _ _ hR K _ _ _ => ?_⟩
  · obtain ⟨h₁, h₂⟩ := noetherian_and_dimensionLEOne (K := K) S (h R hR K L S)
    refine ⟨h₁, ?_⟩
    have := (Ring.krullDimLE_iff (R := S) (n := 1)).mp inferInstance
    exact_mod_cast this
  · obtain ⟨h₁, h₂⟩ :=
      noetherian_and_dimensionLEOne (K := K) (L := K) (integralClosure R K) (h R hR K K _)
    have : IsIntegrallyClosed (integralClosure R K) :=
      integralClosure.isIntegrallyClosedOfFiniteExtension (R := R) K (L := K)
    exact { }

end KrullAkizuki

end GroundTheory.Heights₂.Heights.Model
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.PKrullAkizukiQuotientLength
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

theorem KrullAkizukiQuotientLength.proof (h : TorsionFreeQuotientLength.Statement) :
    KrullAkizukiQuotientLength.Statement := by
  intro R _ _ _ hdim K _ _ _ L _ _ _ _ _ S b hb

  have hinj : Function.Injective (algebraMap R S) := by
    intro x y hxy
    have h1 : algebraMap R L x = algebraMap R L y := by
      simpa using congrArg (fun s : S => (s : L)) hxy
    rw [IsScalarTower.algebraMap_apply R K L, IsScalarTower.algebraMap_apply R K L] at h1
    exact IsFractionRing.injective R K ((algebraMap K L).injective h1)
  have : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr hinj
  have : Module.IsTorsionFree R S := inferInstance

  have hrankL : Module.rank R L = Module.rank K L :=
    (IsLocalization.rank_eq K (nonZeroDivisors R) le_rfl).symm
  have hlt : Module.rank R S < Cardinal.aleph0 :=
    lt_of_le_of_lt (by rw [← hrankL]; exact Submodule.rank_le (Subalgebra.toSubmodule S))
      (Module.rank_lt_aleph0 K L)
  obtain ⟨r, hr⟩ := Cardinal.lt_aleph0.mp hlt

  have hdim0 : Ring.KrullDimLE 0 (R ⧸ Ideal.span {b}) := by
    rw [Ring.krullDimLE_iff]
    have h2 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hb)
    rw [hdim] at h2
    generalize ringKrullDim (R ⧸ Ideal.span {b}) = d at h2 ⊢
    cases d with
    | bot => exact bot_le
    | coe n =>
      have h3 : n + 1 ≤ 1 := by exact_mod_cast h2
      induction n using ENat.recTopCoe with
      | top => simp at h3
      | coe k =>
        have hk : k + 1 ≤ 1 := by exact_mod_cast h3
        obtain rfl : k = 0 := by omega
        simp
  have : IsArtinianRing (R ⧸ Ideal.span {b}) :=
    IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
  have hRlen : Module.length R (R ⧸ Ideal.span {b}) ≠ ⊤ := by
    rw [Module.length_ne_top_iff, isFiniteLength_iff_isNoetherian_isArtinian]
    exact ⟨inferInstance, isArtinian_of_surjective_algebraMap
      (Ideal.Quotient.mk_surjective (I := Ideal.span {b}))⟩

  have hle := h R hdim S r hr b hb
  have hfin : IsFiniteLength R (S ⧸ (Ideal.span {b} • ⊤ : Submodule R S)) :=
    Module.length_ne_top_iff.mp
      (ne_top_of_le_ne_top (WithTop.mul_ne_top (ENat.natCast_ne_top r) hRlen) hle)

  have heq : (Ideal.span {b} • ⊤ : Submodule R S) =
      (Ideal.span {algebraMap R S b}).restrictScalars R := by
    ext x
    simp only [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists,
      Submodule.mem_top, true_and, Submodule.restrictScalars_mem, Ideal.mem_span_singleton',
      Algebra.smul_def, mul_comm]
  rw [heq] at hfin
  exact hfin.of_surjective (f := (Submodule.Quotient.restrictScalarsEquiv R _).toLinearMap)
    (Submodule.Quotient.restrictScalarsEquiv R _).surjective

end GroundTheory.Heights₂.Heights.Model
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.PRatDenominators
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

namespace RatDenominators

theorem proof : RatDenominators.Statement := by
  intro X f U hU
  have : IsAffineHom (baseChangeMap f ℚ) := by
    set_option backward.isDefEq.respectTransparency.types false in
    exact MorphismProperty.pullback_fst _ _ inferInstance
  set g := baseChangeMap f ℚ with hg
  have hV : IsAffineOpen (g ⁻¹ᵁ U) := hU.preimage g
  intro b
  let φ : Γ(X, U) ⟶ Γ(baseChange f ℚ, g ⁻¹ᵁ U) := g.appLE U (g ⁻¹ᵁ U) le_rfl
  have hφ : g.app U = φ := Scheme.Hom.app_eq_appLE _
  let ιA : CommRingCat.of ℤ ⟶ Γ(X, U) := CommRingCat.ofHom (Int.castRingHom Γ(X, U))
  let h : CommRingCat.of ℤ ⟶ CommRingCat.of ℚ := CommRingCat.ofHom (Int.castRingHom ℚ)
  have hUf : hU.fromSpec ≫ f = Spec.map ιA := specZIsTerminal.hom_ext _ _

  have key := IsAffineOpen.SpecMap_appLE_fromSpec g hU hV le_rfl
  have Pgeo : IsPullback (Spec.map φ) (hV.fromSpec ≫ pullback.snd f (Spec.map h))
      (Spec.map ιA) (Spec.map h) := by
    have P := (isPullback_morphismRestrict g U).paste_vert (IsPullback.of_hasPullback f (Spec.map h))
    rw [← hUf]
    refine P.of_iso hV.isoSpec hU.isoSpec (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · rw [← cancel_mono hU.fromSpec, Category.assoc, Category.assoc, key, ← hU.isoSpec_inv_ι,
        ← hV.isoSpec_inv_ι]
      simp [morphismRestrict_ι]
    · rw [← hV.isoSpec_inv_ι]
      simp
    · rw [← hU.isoSpec_inv_ι]
      simp
    · simp

  let M : Submonoid Γ(X, U) := (nonZeroDivisors ℤ).map (Int.castRingHom Γ(X, U))
  let L := Localization M
  let fQ : ℚ →+* L := IsLocalization.map (M := nonZeroDivisors ℤ) (S := ℚ) L
    (Int.castRingHom Γ(X, U)) (T := M) (Submonoid.le_comap_map _)
  have H : fQ.comp (algebraMap ℤ ℚ) = (algebraMap Γ(X, U) L).comp (Int.castRingHom Γ(X, U)) :=
    IsLocalization.map_comp _
  have Palg := isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isLocalization (Int.castRingHom Γ(X, U)) fQ H (nonZeroDivisors ℤ))
  let e := Pgeo.isoIsPullback _ _ Palg
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective e.hom
  obtain ⟨χ, hχ⟩ := Spec.map_surjective e.inv
  have hcomp : CommRingCat.ofHom (algebraMap Γ(X, U) L) ≫ ψ = φ := by
    apply Spec.map_injective
    rw [Spec.map_comp, hψ]
    exact IsPullback.isoIsPullback_hom_fst _ _ Pgeo Palg
  have hχψ : χ ≫ ψ = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, hψ, hχ, Iso.hom_inv_id, Spec.map_id]
  have hφa : ∀ a, φ a = ψ (algebraMap Γ(X, U) L a) := fun a => by rw [← hcomp]; rfl
  have hψa : ∀ b, ψ (χ b) = b := fun b => by
    rw [← CommRingCat.comp_apply, hχψ]; rfl

  obtain ⟨⟨a, m⟩, ham⟩ := IsLocalization.surj M (χ b)
  obtain ⟨n, hn, hnm⟩ := Submonoid.mem_map.mp m.2
  have hn0 : n ≠ 0 := nonZeroDivisors.ne_zero hn
  have hb : b * (n : Γ(baseChange f ℚ, g ⁻¹ᵁ U)) = φ a := by
    have := congrArg ψ ham
    rw [map_mul, hψa, ← hφa, ← hφa, ← hnm] at this
    simpa using this
  refine ⟨n.natAbs, Int.natAbs_pos.mpr hn0, ?_⟩
  rw [hφ, nsmul_eq_mul]
  rcases Int.natAbs_eq n with hn' | hn'
  · refine ⟨a, ?_⟩
    rw [← hb, mul_comm, hn']
    simp
  · refine ⟨-a, ?_⟩
    rw [map_neg, ← hb, mul_comm, hn']
    simp

end RatDenominators

end

end GroundTheory.Heights₂.Heights.Model
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.PVectorBundleLocal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

universe u

theorem IsBasisOn.image_of_restrict {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (M : X.Modules) {W : Y.Opens} {n : ℕ} {s : Fin n → Γ(M.restrict f, W)}
    (hs : IsBasisOn (M.restrict f) W s) :
    IsBasisOn M (f ''ᵁ W) (fun i => (M.restrictAppIso f W).hom (s i)) := by
  intro V h
  obtain ⟨V', rfl⟩ : ∃ V' : Y.Opens, f ''ᵁ V' = V :=
    ⟨f ⁻¹ᵁ V, by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right]
      exact h.trans (f.image_le_opensRange W)⟩
  have hV' : V' ≤ W := by
    rw [← f.preimage_image_eq V', ← f.preimage_image_eq W]
    exact f.preimage_mono h
  have key : (fun r : Fin n → Γ(X, f ''ᵁ V') =>
      ∑ i, r i • (M.presheaf.map (homOfLE h).op).hom ((M.restrictAppIso f W).hom (s i))) =
      (fun r' : Fin n → Γ(Y, V') =>
        ∑ i, r' i • ((M.restrict f).presheaf.map (homOfLE hV').op).hom (s i)) ∘
        (fun r i => (f.appIso V').hom.hom (r i)) := by
    funext r
    simp only [Function.comp_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    change _ = ((f.appIso V').inv.hom ((f.appIso V').hom.hom (r i)) : Γ(X, f ''ᵁ V')) •
      (M.presheaf.map (homOfLE h).op).hom ((M.restrictAppIso f W).hom (s i))
    rw [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]
  rw [key]
  refine (hs V' hV').comp ?_
  exact (Equiv.piCongrRight fun _ => (f.appIso V').commRingCatIsoToRingEquiv.toEquiv).bijective

theorem VectorBundleLocal.proof : VectorBundleLocal.Statement := by
  intro X ι U hU E hE x
  have hx : x ∈ ⨆ i, U i := by rw [hU]; trivial
  obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp hx
  have hR : IsVectorBundle (E.restrict (U i).ι) :=
    (hE i).of_iso ((Scheme.Modules.restrictFunctorIsoPullback (U i).ι).app E).symm
  obtain ⟨W, hWa, hyW, n, s, hs⟩ := hR ⟨x, hxi⟩
  exact ⟨(U i).ι ''ᵁ W, hWa.image_of_isOpenImmersion (U i).ι, ⟨⟨x, hxi⟩, hyW, rfl⟩, n, _,
    hs.image_of_restrict (U i).ι E⟩

end

end GroundTheory.Heights₂.Heights.Model
end

