import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1054
import Formalism.PieriBlockIdeals.Bundle0004
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.Divisibility.RowLat
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1052
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0727
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0620
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0765
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0769
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0516
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSpanTprodOfCommuteAtEachPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1055
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubbundleFrameExists
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
open GlobalTheory.QCoh (freeModule)
open GlobalTheory.Twist (resM)

namespace GlobalTheory.VB

open GlobalTheory.QCoh (appLinear appLinear_apply)
open GlobalTheory.Twist (app_resM)

theorem sum_castLE_eq {M : Type*} [AddCommMonoid M] {N l : ℕ} (hl : l ≤ N) (g : Fin N → M)
    (hg : ∀ j : Fin N, l ≤ (j : ℕ) → g j = 0) :
    ∑ k : Fin l, g (Fin.castLE hl k) = ∑ j, g j :=
  Fintype.sum_of_injective (Fin.castLE hl) (Fin.castLE_injective hl) _ _
    (fun j hj => hg j (by
      by_contra h
      exact hj ⟨⟨j, by omega⟩, rfl⟩)) fun _ => rfl

theorem exists_isFrame_sub_of_vanishing {X : Scheme.{0}} {F : X.Modules} {U : X.Opens} {N : ℕ}
    (P : VB.Sub F) (c : Fin N → Γ(F, U)) (hc : VB.IsFrame c) (l : ℕ) (hl : l ≤ N)
    (hP : ∀ (V : X.Opens) (h : V ≤ U) (a : Fin N → Γ(X, V)),
      (∑ j, a j • resM F h (c j)) ∈ P.sec V ↔ ∀ j : Fin N, l ≤ (j : ℕ) → a j = 0) :
    ∃ e : Fin l → Γ(P.toMod, U), VB.IsFrame e := by
  classical

  have hmem (k : Fin l) : c (Fin.castLE hl k) ∈ P.sec U := by
    have := (hP U le_rfl (Pi.single (Fin.castLE hl k) 1)).2 fun j hj => by
      rw [Pi.single_apply, if_neg]
      rintro rfl
      simp at hj
      omega
    simpa [Pi.single_apply, Finset.sum_ite_eq'] using this
  let e : Fin l → Γ(P.toMod, U) := fun k => P.mkSec _ (hmem k)

  have hincl (V : X.Opens) (h : V ≤ U) (b : Fin l → Γ(X, V)) :
      P.incl.app V (Fintype.linearCombination Γ(X, V) (fun k => resM P.toMod h (e k)) b) =
        ∑ k, b k • resM F h (c (Fin.castLE hl k)) := by
    rw [Fintype.linearCombination_apply, ← appLinear_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, appLinear_apply, app_resM]
    rfl

  let ext (V : X.Opens) (b : Fin l → Γ(X, V)) : Fin N → Γ(X, V) :=
    fun j => if hj : (j : ℕ) < l then b ⟨j, hj⟩ else 0
  have hext0 (V : X.Opens) (b : Fin l → Γ(X, V)) (j : Fin N) (hj : l ≤ (j : ℕ)) : ext V b j = 0 :=
    dif_neg (by omega)
  have hextk (V : X.Opens) (b : Fin l → Γ(X, V)) (k : Fin l) : ext V b (Fin.castLE hl k) = b k :=
    dif_pos k.2
  have hsum (V : X.Opens) (h : V ≤ U) (a : Fin N → Γ(X, V))
      (ha : ∀ j : Fin N, l ≤ (j : ℕ) → a j = 0) :
      ∑ k : Fin l, a (Fin.castLE hl k) • resM F h (c (Fin.castLE hl k)) =
        ∑ j, a j • resM F h (c j) :=
    sum_castLE_eq hl (fun j => a j • resM F h (c j)) fun j hj => by rw [ha j hj, zero_smul]
  refine ⟨e, fun V h => ⟨fun b b' hbb => ?_, fun s => ?_⟩⟩
  · have h1 := congrArg (P.incl.app V) hbb
    rw [hincl, hincl] at h1
    have h2 : Fintype.linearCombination Γ(X, V) (fun j => resM F h (c j)) (ext V b) =
        Fintype.linearCombination Γ(X, V) (fun j => resM F h (c j)) (ext V b') := by
      rw [Fintype.linearCombination_apply, Fintype.linearCombination_apply,
        ← hsum V h _ (hext0 V b), ← hsum V h _ (hext0 V b')]
      simpa only [hextk] using h1
    funext k
    rw [← hextk V b k, ← hextk V b' k, (hc V h).1 h2]
  · obtain ⟨a, ha⟩ := (hc V h).2 (P.incl.app V s)
    rw [Fintype.linearCombination_apply] at ha
    have hz := (hP V h a).1 (ha ▸ P.incl_app_mem s)
    refine ⟨fun k => a (Fin.castLE hl k), P.incl_app_injective V ?_⟩
    rw [hincl, hsum V h a hz, ha]

end GlobalTheory.VB
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubbundleFrameMembership
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
open GlobalTheory.QCoh (freeModule)
open GlobalTheory.Twist (resM)

namespace GlobalTheory.VB

theorem sum_smul_frame_mem_ofStalks_iff : ∀ {X : Scheme.{0}} {F : X.Modules} {U : X.Opens} {N : ℕ} (c : Fin N → Γ(F, U)), VB.IsFrame c → ∀ (S : ∀ x : X, Submodule (X.presheaf.stalk x) (F.presheaf.stalk x :)) (l : ℕ), (∀ (y : X) (hy : y ∈ U), S y = Submodule.span _ {v | ∃ j : Fin N, (j : ℕ) < l ∧ v = F.presheaf.germ U y hy (c j)}) → ∀ {V : X.Opens} (h : V ≤ U) (a : Fin N → Γ(X, V)), (∑ j, a j • resM F h (c j)) ∈ (VB.Sub.ofStalks S).sec V ↔ ∀ j : Fin N, l ≤ (j : ℕ) → a j = 0 := by
  intro X F U N c hc S l hS V h a
  have hg : ∀ (y : X) (hy : y ∈ V), F.presheaf.germ V y hy (∑ j, a j • resM F h (c j)) =
      ∑ j, X.presheaf.germ V y hy (a j) • hc.stalkBasis y (h hy) j := by
    intro y hy
    simp only [map_sum, QCoh.germ_smul, Twist.germ_resM, IsFrame.stalkBasis_apply]
  have hset : ∀ (y : X) (hy : y ∈ U),
      {v | ∃ j : Fin N, (j : ℕ) < l ∧ v = F.presheaf.germ U y hy (c j)} =
        hc.stalkBasis y hy '' {j : Fin N | (j : ℕ) < l} := by
    intro y hy
    ext v
    simp only [Set.mem_setOf_eq, Set.mem_image, IsFrame.stalkBasis_apply]
    exact ⟨fun ⟨j, h1, h2⟩ => ⟨j, h1, h2.symm⟩, fun ⟨j, h1, h2⟩ => ⟨j, h1, h2.symm⟩⟩
  change (∀ (y : X) (hy : y ∈ V), F.presheaf.germ V y hy (∑ j, a j • resM F h (c j)) ∈ S y) ↔ _
  constructor
  · intro H j hj
    refine TopCat.Presheaf.section_ext X.sheaf V _ _ fun y hy => ?_
    have H1 := H y hy
    rw [hg y hy, hS y (h hy), hset y (h hy), Module.Basis.mem_span_image] at H1
    have h0 : (hc.stalkBasis y (h hy)).repr
        (∑ j, X.presheaf.germ V y hy (a j) • hc.stalkBasis y (h hy) j) j = 0 := by
      by_contra hne
      have := H1 (Finset.mem_coe.2 (Finsupp.mem_support_iff.2 hne))
      exact absurd this (not_lt.2 hj)
    rw [congrFun ((hc.stalkBasis y (h hy)).repr_sum_self _) j] at h0
    exact h0.trans (map_zero (X.presheaf.germ V y hy).hom).symm
  · intro H y hy
    rw [hg y hy, hS y (h hy), hset y (h hy)]
    refine Submodule.sum_mem _ fun j _ => ?_
    by_cases hj : (j : ℕ) < l
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)
    · rw [H j (not_lt.1 hj), map_zero, zero_smul]
      exact Submodule.zero_mem _

end GlobalTheory.VB
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumExactExponentsSmulMemLocalizedCoeffLatticeStatement
section
open NumberField IsDedekindDomain Formalism.L2.DIV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_exactExponents_smul_mem_localizedCoeffLattice : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [StarRing K] (ι : Type) [Fintype ι] (n : ℕ) (emb : ι → E →+* K) (lam : ι → Formalism.BasicNotions.DomWeight n) (L : Submodule (𝓞 E) (Fin n → E)), Submodule.IsLattice E L → ∀ (w : HeightOneSpectrum (𝓞 K)), ∀ x ∈ nabAtr emb lam L, (((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 K) ^ (∑ τ, Formalism.CohomologicalDescent.LA.exZ n n le_rfl (lam τ).natW (Formalism.EigenvalueLevelCeiling.plc w))) • x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (delAtr emb lam L) := by
  first | exact @GlobalTheory.OntoExponentsLat.exZ_sum_smul_mem_locP_delAtr | exact GlobalTheory.OntoExponentsLat.exZ_sum_smul_mem_locP_delAtr | (intros; apply GlobalTheory.OntoExponentsLat.exZ_sum_smul_mem_locP_delAtr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistAcyclicSpectrumPolynomialOfIsAlgClosed
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem acyc_polynomial_of_isAlgClosed : ∀ (q : ℕ) [NeZero q] (K : Type) [Field K] [IsAlgClosed K],
    IsUnit (q : K) → Acyc q (sp (Polynomial K)) := by
  intro q _ K _ _ hq n i hn
  have hqA : IsUnit (q : Polynomial K) := by
    simpa using hq.map (Polynomial.C : K →+* Polynomial K)
  by_cases h2 : 2 ≤ n
  · exact GlobalTheory.T.smooth_affine_curve_etale_cohomologicalDimension_le_one q K (Polynomial K) hq n i h2
  · have hn1 : n = 1 := by omega
    subst hn1
    have hζ : ∃ ζ : Polynomial K, Polynomial.aeval ζ (Polynomial.cyclotomic q ℤ) = 0 := by
      have hdeg : (Polynomial.cyclotomic q K).degree ≠ 0 := by
        rw [Polynomial.degree_cyclotomic]
        have := Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne q))
        exact_mod_cast this.ne'
      obtain ⟨z, hz⟩ := IsAlgClosed.exists_root _ hdeg
      refine ⟨Polynomial.C z, ?_⟩
      have hz' : Polynomial.aeval z (Polynomial.cyclotomic q ℤ) = 0 := by
        rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
        exact hz
      have hC : Polynomial.C z = algebraMap K (Polynomial K) z := rfl
      rw [hC, Polynomial.aeval_algebraMap_apply, hz', map_zero]
    obtain ⟨e⟩ := GlobalTheory.T.tateTwistCohomology_spec_twist_independent q (Polynomial K) hqA hζ 1 i 1
    have hs : Subsingleton (Ht q (sp (Polynomial K)) 1 1) := by
      refine GlobalTheory.T.kummer_etale_vanishing q (Polynomial K) hqA ?_ ?_
      · intro u
        obtain ⟨r, hr, hru⟩ := Polynomial.isUnit_iff.1 u.isUnit
        obtain ⟨v, hv⟩ := IsAlgClosed.exists_pow_nat_eq r (Nat.pos_of_ne_zero (NeZero.ne q))
        have hv0 : v ≠ 0 := by
          rintro rfl
          rw [zero_pow (NeZero.ne q)] at hv
          exact hr.ne_zero hv.symm
        refine ⟨Units.map (Polynomial.C : K →+* Polynomial K).toMonoidHom (Units.mk0 v hv0), ?_⟩
        ext
        simp [← hru, ← hv]
      · intro c _
        exact Subsingleton.elim _ _
    exact e.toEquiv.subsingleton

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCohomologyLaurentPolynomialOfIsAlgClose
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.LaurentUnits
open LaurentPolynomial Polynomial

variable (K : Type) [Field K]

theorem isDomain : IsDomain (LaurentPolynomial K) :=
  IsLocalization.isDomain_of_le_nonZeroDivisors (M := Submonoid.powers (X : K[X])) _
    (powers_le_nonZeroDivisors_of_noZeroDivisors X_ne_zero)

theorem isPrincipalIdealRing : IsPrincipalIdealRing (LaurentPolynomial K) := by
  refine ⟨fun P => ?_⟩
  obtain ⟨g, hg⟩ := (IsPrincipalIdealRing.principal (P.comap (algebraMap K[X] (LaurentPolynomial K))))
  refine ⟨algebraMap K[X] (LaurentPolynomial K) g, ?_⟩
  rw [← IsLocalization.map_comap (Submonoid.powers (X : K[X])) (LaurentPolynomial K) P, Ideal.under_def, hg,
    Ideal.submodule_span_eq, Ideal.map_span, Set.image_singleton, Ideal.submodule_span_eq]

theorem units_eq (u : (LaurentPolynomial K)ˣ) :
    ∃ (c : K) (m : ℤ), (u : LaurentPolynomial K) = LaurentPolynomial.C c * T m := by
  obtain ⟨n, p, hp⟩ := exists_T_pow (u : LaurentPolynomial K)
  obtain ⟨n', r, hr⟩ := exists_T_pow ((u⁻¹ : (LaurentPolynomial K)ˣ) : LaurentPolynomial K)
  have hpr : p * r = X ^ (n + n') := by
    apply Polynomial.toLaurent_injective
    rw [map_mul, hp, hr, Polynomial.toLaurent_X_pow]
    have : (u : LaurentPolynomial K) * T n * (((u⁻¹ : (LaurentPolynomial K)ˣ) : LaurentPolynomial K) * T n')
        = T n * T n' := by
      rw [mul_mul_mul_comm, Units.mul_inv, one_mul]
    rw [this, ← T_add]; push_cast; rfl
  obtain ⟨i, -, hi⟩ := (dvd_prime_pow Polynomial.prime_X (n + n')).1 ⟨r, hpr.symm⟩
  obtain ⟨v, hv⟩ := hi.symm
  obtain ⟨c, -, hc⟩ := Polynomial.isUnit_iff.1 v.isUnit
  refine ⟨c, (i : ℤ) - n, ?_⟩
  have h1 : (u : LaurentPolynomial K) * T n = LaurentPolynomial.C c * T i := by
    rw [← hp, ← hv, ← hc, map_mul, Polynomial.toLaurent_X_pow, Polynomial.toLaurent_C, mul_comm]
  calc (u : LaurentPolynomial K) = (u : LaurentPolynomial K) * T n * T (-(n : ℤ)) := by
        rw [mul_assoc, ← T_add, add_neg_cancel, T_zero, mul_one]
    _ = LaurentPolynomial.C c * T ((i : ℤ) - n) := by rw [h1, mul_assoc, ← T_add, sub_eq_add_neg]

theorem pic_subsingleton : Subsingleton (CommRing.Pic (LaurentPolynomial K)) := by
  haveI := isDomain K
  haveI := isPrincipalIdealRing K
  haveI := UniqueFactorizationMonoid.toGCDMonoid (LaurentPolynomial K)
  infer_instance

theorem isDedekindDomain : IsDedekindDomain (LaurentPolynomial K) := by
  haveI := isDomain K
  haveI := isPrincipalIdealRing K
  infer_instance

theorem laurent_monomial_exponent_eq {a b : ℤ} {c : K} (h : (T a : LaurentPolynomial K) = LaurentPolynomial.C c * T b) : a = b := by
  have hc : c ≠ 0 := by
    rintro rfl
    simp only [map_zero, zero_mul] at h
    exact (isUnit_T (R := K) a).ne_zero h
  have h2 := congrArg LaurentPolynomial.degree h
  rw [degree_T, degree_C_mul_T _ _ hc] at h2
  exact WithBot.coe_inj.1 h2

theorem val_T_unit_zpow (m : ℤ) :
    ((((isUnit_T 1).unit : (LaurentPolynomial K)ˣ) ^ m : (LaurentPolynomial K)ˣ) : LaurentPolynomial K) = T m := by
  induction m using Int.induction_on with
  | zero => simp
  | succ i ih => rw [zpow_add_one, Units.val_mul, ih, IsUnit.unit_spec, ← T_add]
  | pred i ih =>
    rw [zpow_sub_one, Units.val_mul, ih]
    have : ((((isUnit_T 1).unit)⁻¹ : (LaurentPolynomial K)ˣ) : LaurentPolynomial K) = T (-1) := by
      apply Units.inv_eq_of_mul_eq_one_right
      rw [IsUnit.unit_spec, ← T_add]; simp
    rw [this, ← T_add]; ring_nf

end GlobalTheory.LaurentUnits

namespace GlobalTheory.GmAlgClosed
open LaurentPolynomial GlobalTheory.LaurentUnits

variable (q : ℕ) [NeZero q] (K : Type) [Field K]

noncomputable abbrev gEq : Γ(Spec (CommRingCat.of (LaurentPolynomial K)), ⊤) ≃+* LaurentPolynomial K :=
  (Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial K))).commRingCatIsoToRingEquiv

theorem isUnit_q_L (hq : IsUnit (q : K)) : IsUnit (q : LaurentPolynomial K) := by
  simpa using hq.map (algebraMap K (LaurentPolynomial K))

theorem isUnit_q_Γ (hq : IsUnit (q : LaurentPolynomial K)) :
    IsUnit (q : Γ(Spec (CommRingCat.of (LaurentPolynomial K)), ⊤)) := by
  simpa using hq.map (gEq K).symm.toRingHom

noncomputable def kumL (hq : IsUnit (q : LaurentPolynomial K)) :
    (LaurentPolynomial K)ˣ →* Multiplicative (Ht q (sp (LaurentPolynomial K)) 1 1) where
  toFun u := Multiplicative.ofAdd (kum q (Units.map (gEq K).symm.toRingHom.toMonoidHom u))
  map_one' := by
    have h := ((a6add_holds q).2 (1 : (Γ(Spec (CommRingCat.of (LaurentPolynomial K)), ⊤))ˣ) 1
      (isUnit_q_Γ q K hq)).1
    rw [mul_one] at h
    rw [map_one, ofAdd_eq_one]
    exact add_left_cancel (b := kum q _) (c := 0) (by rw [add_zero]; exact h.symm)
  map_mul' u v := by
    rw [map_mul, ((a6add_holds q).2 _ _ (isUnit_q_Γ q K hq)).1, ofAdd_add]

theorem kumL_pow_q (hq : IsUnit (q : LaurentPolynomial K)) (u : (LaurentPolynomial K)ˣ) :
    kumL q K hq (u ^ q) = 1 := by
  show Multiplicative.ofAdd (kum q _) = 1
  rw [map_pow, ((a6add_holds q).2 _ 1 (isUnit_q_Γ q K hq)).2, ofAdd_zero]

noncomputable abbrev tau : (LaurentPolynomial K)ˣ := (isUnit_T 1).unit

theorem zsmul_q (hq : IsUnit (q : LaurentPolynomial K)) :
    zmultiplesHom _ (Multiplicative.toAdd (kumL q K hq (tau K))) (q : ℤ) = 0 := by
  rw [zmultiplesHom_apply, natCast_zsmul, ← toAdd_pow, ← map_pow, kumL_pow_q, toAdd_one]

noncomputable def fL (hq : IsUnit (q : LaurentPolynomial K)) : ZMod q →+ Ht q (sp (LaurentPolynomial K)) 1 1 :=
  ZMod.lift q ⟨zmultiplesHom _ (Multiplicative.toAdd (kumL q K hq (tau K))), zsmul_q q K hq⟩

theorem fL_intCast (hq : IsUnit (q : LaurentPolynomial K)) (m : ℤ) :
    fL q K hq (m : ZMod q) = Multiplicative.toAdd (kumL q K hq (tau K ^ m)) := by
  rw [fL, ZMod.lift_coe]
  show zmultiplesHom _ _ m = _
  rw [zmultiplesHom_apply, map_zpow, toAdd_zpow]

variable [IsAlgClosed K]

theorem fL_surjective (hq : IsUnit (q : LaurentPolynomial K)) : Function.Surjective (fL q K hq) := by
  intro x
  obtain ⟨u', hu'⟩ := GlobalTheory.T.exists_unit_kummer_eq_of_picard_torsionFree q (LaurentPolynomial K) hq
    (fun c _ => @Subsingleton.elim _ (pic_subsingleton K) _ _) x
  set u : (LaurentPolynomial K)ˣ := Units.map (gEq K).toRingHom.toMonoidHom u'
  have hu : Units.map (gEq K).symm.toRingHom.toMonoidHom u = u' := by ext; simp [u]
  obtain ⟨c, m, hcm⟩ := units_eq K u
  have hc : c ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_mul] at hcm
    exact u.ne_zero hcm
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq c (Nat.pos_of_ne_zero (NeZero.ne q))
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hc (by rw [← hd, zero_pow (NeZero.ne q)])
  set w : (LaurentPolynomial K)ˣ := Units.map (LaurentPolynomial.C : K →+* LaurentPolynomial K).toMonoidHom (Units.mk0 d hd0)
  have huw : u = w ^ q * tau K ^ m := by
    ext
    rw [Units.val_mul, Units.val_pow_eq_pow_val, val_T_unit_zpow, hcm, ← hd, map_pow]
    rfl
  refine ⟨(m : ZMod q), ?_⟩
  rw [fL_intCast, ← hu', ← hu]
  show _ = Multiplicative.toAdd (kumL q K hq u)
  rw [huw, map_mul, kumL_pow_q, one_mul]

theorem fL_injective (hq : IsUnit (q : LaurentPolynomial K)) : Function.Injective (fL q K hq) := by
  refine (injective_iff_map_eq_zero _).2 fun z hz => ?_
  have hz' : fL q K hq ((z.val : ℤ) : ZMod q) = 0 := by
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]; exact hz
  rw [fL_intCast, zpow_natCast] at hz'
  obtain ⟨v, hv⟩ := GlobalTheory.T.eq_pow_of_kummerClassOfUnit_eq_zero q (LaurentPolynomial K) hq _ hz'
  have hv' : tau K ^ z.val = (Units.map (gEq K).toRingHom.toMonoidHom v) ^ q := by
    have := congrArg (Units.map (gEq K).toRingHom.toMonoidHom) hv
    rw [← map_pow, ← this]; ext; simp
  obtain ⟨c, k, hck⟩ := units_eq K (Units.map (gEq K).toRingHom.toMonoidHom v)
  have hT : (T (z.val : ℤ) : LaurentPolynomial K) = LaurentPolynomial.C (c ^ q) * T ((q : ℤ) * k) := by
    have := congrArg (fun w : (LaurentPolynomial K)ˣ => (w : LaurentPolynomial K)) hv'
    simp only [Units.val_pow_eq_pow_val, hck, IsUnit.unit_spec, T_pow, mul_one, mul_pow, map_pow] at this
    rw [map_pow]; exact this
  have he := laurent_monomial_exponent_eq K hT
  have hlt : ((z.val : ℕ) : ℤ) < q := by exact_mod_cast ZMod.val_lt z
  have hq0 : (0 : ℤ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have h0 : ((z.val : ℕ) : ℤ) = 0 := by
    rcases le_or_gt k 0 with hk | hk
    · nlinarith
    · nlinarith
  exact (ZMod.val_eq_zero z).1 (by exact_mod_cast h0)

theorem exists_root_L (hq : IsUnit (q : K)) :
    ∃ ζ : LaurentPolynomial K, Polynomial.aeval ζ (Polynomial.cyclotomic q ℤ) = 0 := by
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic q K) (by
    rw [Polynomial.degree_cyclotomic]
    exact_mod_cast (Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne q))).ne')
  refine ⟨algebraMap K _ ζ, ?_⟩
  rw [Polynomial.aeval_algebraMap_apply, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map,
    Polynomial.map_cyclotomic, hζ.eq_zero, map_zero]

end GlobalTheory.GmAlgClosed

theorem GlobalTheory.EtC.gm_algClosed_cohomology : ∀ (q : ℕ) [NeZero q] (K : Type) [Field K] [IsAlgClosed K], IsUnit (q : K) →
    ∀ n i : ℤ, (2 ≤ n → Subsingleton (Ht q (sp (LaurentPolynomial K)) n i)) ∧
      Nonempty (Ht q (sp (LaurentPolynomial K)) 1 i ≃+ ZMod q) := by
  intro q _ K _ _ hq n i
  haveI := GlobalTheory.LaurentUnits.isDedekindDomain K
  refine ⟨fun hn => GlobalTheory.T.smooth_affine_curve_etale_cohomologicalDimension_le_one q K (LaurentPolynomial K) hq n i hn, ?_⟩
  have hqL := GlobalTheory.GmAlgClosed.isUnit_q_L q K hq
  obtain ⟨e1⟩ := GlobalTheory.T.tateTwistCohomology_spec_twist_independent q (LaurentPolynomial K) hqL (GlobalTheory.GmAlgClosed.exists_root_L q K hq) 1 i 1
  exact ⟨e1.trans (AddEquiv.ofBijective _
    ⟨GlobalTheory.GmAlgClosed.fL_injective q K hqL, GlobalTheory.GmAlgClosed.fL_surjective q K hqL⟩).symm⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorPlaceActionInjective
section
open scoped TensorProduct

namespace GlobalTheory.FactorKernel

variable {ι : Type} [Fintype ι] [hd : DecidableEq ι] {V : Type} [AddCommGroup V] [Module ℂ V]

noncomputable def contrML (w₀ : ι) (μ : ι → Module.Dual ℂ V) : MultilinearMap ℂ (fun _ : ι => V) V where
  toFun x := (∏ i ∈ Finset.univ.erase w₀, μ i (x i)) • x w₀
  map_update_add' := by
    intro inst x i a b
    obtain rfl : inst = hd := Subsingleton.elim _ _
    by_cases h : i = w₀
    · subst h
      have e : ∀ c, ∏ k ∈ Finset.univ.erase i, μ k (Function.update x i c k) =
          ∏ k ∈ Finset.univ.erase i, μ k (x k) := fun c =>
        Finset.prod_congr rfl fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
      simp only [e, Function.update_self, smul_add]
    · have hi : i ∈ Finset.univ.erase w₀ := Finset.mem_erase.2 ⟨h, Finset.mem_univ _⟩
      have e : ∀ c, ∏ k ∈ Finset.univ.erase w₀, μ k (Function.update x i c k) =
          μ i c * ∏ k ∈ (Finset.univ.erase w₀).erase i, μ k (x k) := fun c => by
        rw [← Finset.mul_prod_erase _ _ hi, Function.update_self]
        congr 1
        exact Finset.prod_congr rfl fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
      simp only [e, Function.update_of_ne (Ne.symm h), map_add, add_mul, add_smul]
  map_update_smul' := by
    intro inst x i c a
    obtain rfl : inst = hd := Subsingleton.elim _ _
    by_cases h : i = w₀
    · subst h
      have e : ∀ c, ∏ k ∈ Finset.univ.erase i, μ k (Function.update x i c k) =
          ∏ k ∈ Finset.univ.erase i, μ k (x k) := fun c =>
        Finset.prod_congr rfl fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
      simp only [e, Function.update_self, smul_comm c]
    · have hi : i ∈ Finset.univ.erase w₀ := Finset.mem_erase.2 ⟨h, Finset.mem_univ _⟩
      have e : ∀ c, ∏ k ∈ Finset.univ.erase w₀, μ k (Function.update x i c k) =
          μ i c * ∏ k ∈ (Finset.univ.erase w₀).erase i, μ k (x k) := fun c => by
        rw [← Finset.mul_prod_erase _ _ hi, Function.update_self]
        congr 1
        exact Finset.prod_congr rfl fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
      simp only [e, Function.update_of_ne (Ne.symm h), map_smul, smul_eq_mul, mul_assoc, smul_smul]

noncomputable def contr (w₀ : ι) (μ : ι → Module.Dual ℂ V) : (⨂[ℂ] _ : ι, V) →ₗ[ℂ] V :=
  PiTensorProduct.lift (contrML w₀ μ)

theorem contr_tprod (w₀ : ι) (μ : ι → Module.Dual ℂ V) (x : ι → V) :
    contr w₀ μ (PiTensorProduct.tprod ℂ x) = (∏ i ∈ Finset.univ.erase w₀, μ i (x i)) • x w₀ := by
  rw [contr, PiTensorProduct.lift.tprod]; rfl

theorem dual_contr (w₀ : ι) (μ : ι → Module.Dual ℂ V) (ν : Module.Dual ℂ V) (T : ⨂[ℂ] _ : ι, V) :
    ν (contr w₀ μ T) =
      PiTensorProduct.dualDistrib (PiTensorProduct.tprod ℂ (Function.update μ w₀ ν)) T := by
  induction T using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    rw [map_smul, map_smul, map_smul, contr_tprod, PiTensorProduct.dualDistrib_apply, map_smul,
      ← Finset.mul_prod_erase _ _ (Finset.mem_univ w₀), Function.update_self, smul_eq_mul, smul_eq_mul, smul_eq_mul]
    congr 1
    rw [mul_comm]
    congr 1
    exact Finset.prod_congr rfl fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add]

theorem contr_atPl (w₀ : ι) (μ : ι → Module.Dual ℂ V) (L : Module.End ℂ V) (T : ⨂[ℂ] _ : ι, V) :
    contr w₀ μ (GlobalTheory.RealLift.atPl (V := fun _ : ι => V) w₀ L T) = L (contr w₀ μ T) := by
  induction T using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    rw [map_smul, map_smul, map_smul, GlobalTheory.RealLift.atPl, PiTensorProduct.map_tprod, contr_tprod, contr_tprod,
      map_smul, Function.update_self, L.map_smul]
    congr 2
    exact Finset.prod_congr rfl fun k hk => by
      simp [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  | add a b ha hb => simp only [map_add, ha, hb]

theorem atPl_noCommonKernel : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (V : Type) [AddCommGroup V] [Module ℂ V] (J : Type)
    (L : J → Module.End ℂ V) (w₀ : ι), (∀ v : V, (∀ j, L j v = 0) → v = 0) →
    ∀ T : ⨂[ℂ] _ : ι, V, (∀ j, GlobalTheory.RealLift.atPl (V := fun _ : ι => V) w₀ (L j) T = 0) → T = 0 := by
  intro ι _ _ V _ _ J L w₀ hL T hT
  apply GlobalTheory.PiTensorCommute.eq_zero_of_forall_dualDistrib (M := fun _ : ι => V)
  intro f
  have hv : contr w₀ f T = 0 := hL _ fun j => by rw [← contr_atPl, hT j, map_zero]
  have h := dual_contr w₀ f (f w₀) T
  rw [hv, map_zero, Function.update_eq_self] at h
  exact h.symm

end GlobalTheory.FactorKernel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPairCharactersAtLevelStatement
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_pair_characters_at_level : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.Char F → ∀ (i : Fin D.R.m) (t : T0), VStd D i → IsPair R.ψ R.θ (Vc D i) (Wc D i) (Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).1 (Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).2 (R.ωP i t) ∧ (Vc D i).rank ≠ 0 ∧ (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E)) = L0c D (Vc D i) ∧ (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) = L0c D (Wc D i) ∧ IsSelfDualC (Vc D i) (R.ΛV i) ∧ IsSelfDualC (Wc D i) (R.ΛW i) ∧ (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E)) = (Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank : Set (Fin (Vc D i).rank → D.host.E)) := by
  first | exact @GlobalTheory.AdTh.RecPair.isPair_record | exact GlobalTheory.AdTh.RecPair.isPair_record | (intros; apply GlobalTheory.AdTh.RecPair.isPair_record <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaVectorFockVacuumStatement
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_vector_fock_vacuum : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.Char F → ∀ (i : Fin D.R.m) (t : T0), VStd D i → IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t) ∧ (∀ τ, IsFockVacAt (heisO R.ψ (Vc D i) (Wc D i)) R.θ τ (cplxO 1 (cart (R.MW i (sg0 D A)) τ)) (R.vP i t)) ∧ (∀ τ, IsCartanInv (gramAt D (Wc D i) τ) (cart (R.MW i (sg0 D A)) τ)) ∧ (∀ τ, IsCartanInv (gramAt D (Vc D i) τ) 1) ∧ ∀ τ, IsONBasis (gramAt D (Wc D i) τ) (cart (R.MW i (sg0 D A)) τ) (onb (R.MW i (sg0 D A)) τ) ((Wc D i).sig (tauE D τ)).1 := by
  first | exact @GlobalTheory.AdTh.VecFock.vec_fock | exact GlobalTheory.AdTh.VecFock.vec_fock | (intros; apply GlobalTheory.AdTh.VecFock.vec_fock <;> assumption)
end

