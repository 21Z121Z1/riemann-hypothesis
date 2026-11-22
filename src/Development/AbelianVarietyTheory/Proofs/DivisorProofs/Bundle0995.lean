import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsAlgebraicIndependentGenericPoint
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjPointIdealMemProjComponentsOfIsProjPureDim
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFormDegreeLeHilbertDegreeEvalNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0522
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0966
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0958
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0127
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0008
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0903
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabEqStabilizer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0967
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerEqCentralizer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0308
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0295
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0936
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0968

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FieldDegreeLeChowFormDegreeAlgebraicPoint
section
set_option autoImplicit false

noncomputable section

open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt

namespace GlobalTheory.CompHt.PointLow

set_option autoImplicit false in
open MvPolynomial in
private lemma natDegree_aeval_le_totalDegree_of_natDegree_le_one {R S σ : Type} [CommRing R] [CommRing S] [Algebra R S]
    (p : MvPolynomial σ R) (s : σ → Polynomial S) (hs : ∀ i, (s i).natDegree ≤ 1) :
    (MvPolynomial.aeval s p).natDegree ≤ p.totalDegree := by
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun d hd => ?_
  rw [MvPolynomial.aeval_monomial]
  refine Polynomial.natDegree_mul_le.trans ?_
  have h0 : (algebraMap R (Polynomial S) (p.coeff d)).natDegree = 0 := by
    rw [Polynomial.algebraMap_apply]; exact Polynomial.natDegree_C _
  rw [h0, zero_add, Finsupp.prod]
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  refine le_trans ?_ (MvPolynomial.le_totalDegree hd)
  refine Finset.sum_le_sum fun i _ => ?_
  refine Polynomial.natDegree_pow_le.trans ?_
  simpa using Nat.mul_le_mul_left (d i) (hs i)

set_option autoImplicit false in
open MvPolynomial in

theorem _root_.GlobalTheory.CompHt.PointLow.finrank_le_of_isChowFormInt : ∀ (K : Type) [Field K] [CharZero K] (N δ : ℕ) (y : Fin N → AlgebraicClosure K)
    (j : Fin N) (f : MvPolynomial (Fin (0 + 1) × Fin N) K), y j = 1 → _root_.GlobalTheory.ChowHt.IsChowFormInt (_root_.GlobalTheory.CompHt.coneIdeal K y) 0 δ f →
    Module.finrank K (IntermediateField.adjoin K (Set.range y)) ≤ δ := by
  intro K _ _ N δ y j f hyj hf
  classical
  set E := IntermediateField.adjoin K (Set.range y) with hE
  haveI : FiniteDimensional K E :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  rw [← AlgHom.card K E (AlgebraicClosure K)]
  let yE : Fin N → E := fun k => ⟨y k, IntermediateField.subset_adjoin K _ ⟨k, rfl⟩⟩
  let pt : (E →ₐ[K] AlgebraicClosure K) → Fin N → AlgebraicClosure K := fun σ k => σ (yE k)
  have hpj : ∀ σ, pt σ j = 1 := by
    intro σ
    have : yE j = 1 := Subtype.ext hyj
    simp only [pt, this, map_one]
  have hzero : ∀ σ, ∀ g ∈ _root_.GlobalTheory.CompHt.coneIdeal K y, MvPolynomial.aeval (pt σ) g = 0 := by
    intro σ g hg
    have hy := _root_.GlobalTheory.CompHt.aeval_eq_zero_of_mem_coneIdeal hg
    have hE0 : MvPolynomial.aeval yE g = 0 := by
      apply Subtype.ext
      have := MvPolynomial.comp_aeval_apply yE E.val g
      show E.val (MvPolynomial.aeval yE g) = E.val 0
      rw [this, map_zero]
      exact hy
    have := MvPolynomial.comp_aeval_apply yE σ g
    rw [hE0, map_zero] at this
    exact this.symm
  have hinj : Function.Injective pt := by
    intro σ τ h
    refine IntermediateField.adjoin_algHom_ext K fun x hx => ?_
    obtain ⟨k, rfl⟩ := hx
    exact congrFun h k
  set fΩ := MvPolynomial.map (algebraMap K (AlgebraicClosure K)) f with hfΩ
  have hfΩ0 : fΩ ≠ 0 := by
    intro h
    exact hf.ne_zero (MvPolynomial.map_injective _ (algebraMap K (AlgebraicClosure K)).injective
      (by rw [← hfΩ, h, map_zero]))
  let lin : (E →ₐ[K] AlgebraicClosure K) → (E →ₐ[K] AlgebraicClosure K) →
      MvPolynomial (Fin (0 + 1) × Fin N) (AlgebraicClosure K) :=
    fun σ τ => ∑ k, X (0, k) * C (pt σ k - pt τ k)
  have hlin_eval : ∀ σ τ (a : Fin (0 + 1) × Fin N → AlgebraicClosure K),
      eval a (lin σ τ) = ∑ k, a (0, k) * pt σ k - ∑ k, a (0, k) * pt τ k := by
    intro σ τ a
    simp only [lin, map_sum, eval_mul, eval_X, eval_C, ← Finset.sum_sub_distrib, mul_sub]
  set pairs := Finset.univ.filter fun st : (E →ₐ[K] AlgebraicClosure K) × (E →ₐ[K] AlgebraicClosure K) =>
    st.1 ≠ st.2 with hpairs
  set Q := fΩ * ∏ st ∈ pairs, lin st.1 st.2 with hQ
  have hQ0 : Q ≠ 0 := by
    refine mul_ne_zero hfΩ0 (Finset.prod_ne_zero_iff.mpr fun st hst => ?_)
    have hne : st.1 ≠ st.2 := (Finset.mem_filter.mp hst).2
    have hpne : pt st.1 ≠ pt st.2 := fun h => hne (hinj h)
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hpne
    intro h0
    have := congrArg (eval (Pi.single (0, k) 1)) h0
    rw [hlin_eval, map_zero] at this
    simp only [Pi.single_apply, Prod.mk.injEq, true_and, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
    exact hk (sub_eq_zero.mp this)
  obtain ⟨a, ha⟩ : ∃ a, eval a Q ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hQ0 (MvPolynomial.funext fun x => by rw [hcon x, map_zero])
  have hfa : eval a fΩ ≠ 0 := fun h => ha (by rw [hQ, eval_mul, h, zero_mul])
  let c : (E →ₐ[K] AlgebraicClosure K) → AlgebraicClosure K := fun σ => ∑ k, a (0, k) * pt σ k
  have hdist : Function.Injective c := by
    intro σ τ h
    by_contra hne
    apply ha
    rw [hQ, eval_mul, map_prod]
    refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (i := (σ, τ))
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩) ?_)
    rw [hlin_eval]
    exact sub_eq_zero.mpr h
  let s : Fin (0 + 1) × Fin N → Polynomial (AlgebraicClosure K) :=
    fun ik => Polynomial.C (a ik) + if ik.2 = j then Polynomial.X else 0
  set g := MvPolynomial.aeval s f with hg
  have heval : ∀ t, g.eval t = MvPolynomial.aeval (fun ik => a ik + if ik.2 = j then t else 0) f := by
    intro t
    have := MvPolynomial.comp_aeval_apply s
      ((Polynomial.aeval t).restrictScalars K : Polynomial (AlgebraicClosure K) →ₐ[K] AlgebraicClosure K) f
    rw [hg, ← Polynomial.coe_aeval_eq_eval, show (Polynomial.aeval t) (MvPolynomial.aeval s f) =
      ((Polynomial.aeval t).restrictScalars K : Polynomial (AlgebraicClosure K) →ₐ[K] AlgebraicClosure K)
        (MvPolynomial.aeval s f) from rfl, this]
    refine congrArg (fun v => MvPolynomial.aeval v f) (funext fun ik => ?_)
    simp only [s]
    split_ifs <;> simp
  have hg0 : g ≠ 0 := by
    intro h
    have := heval 0
    rw [h, Polynomial.eval_zero] at this
    have h2 : (fun ik : Fin (0 + 1) × Fin N => a ik + if ik.2 = j then (0 : AlgebraicClosure K) else 0) = a := by
      funext ik; split_ifs <;> simp
    rw [h2] at this
    apply hfa
    rw [hfΩ, MvPolynomial.eval_map, ← MvPolynomial.aeval_def]
    exact this.symm
  have hroot : ∀ σ, g.eval (-c σ) = 0 := by
    intro σ
    rw [heval]
    refine (hf.zero_iff _).mpr
      ⟨pt σ, fun h => by simpa [hpj σ] using congrFun h j, hzero σ, fun i => ?_⟩
    obtain rfl : i = 0 := Fin.ext (Nat.lt_one_iff.mp i.isLt)
    simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, hpj σ, mul_one]
    simp [c]
  have hcard : Fintype.card (E →ₐ[K] AlgebraicClosure K) ≤ g.roots.toFinset.card := by
    rw [← Finset.card_univ]
    refine Finset.card_le_card_of_injOn (fun σ => -c σ) (fun σ _ => ?_) ?_
    · simp only [Finset.mem_coe, Multiset.mem_toFinset]
      rw [Polynomial.mem_roots hg0]
      exact hroot σ
    · intro σ _ τ _ h
      exact hdist (neg_injective h)
  have hhom := ((_root_.GlobalTheory.ChowHt.isMultiHomogeneous_iff_block.mp
    hf.homog).isHomogeneous)
  have htot : f.totalDegree = δ := by
    rw [hhom.totalDegree hf.ne_zero]
    simp
  calc Fintype.card (E →ₐ[K] AlgebraicClosure K) ≤ g.roots.toFinset.card := hcard
    _ ≤ Multiset.card g.roots := Multiset.toFinset_card_le _
    _ ≤ g.natDegree := Polynomial.card_roots' g
    _ ≤ f.totalDegree := natDegree_aeval_le_totalDegree_of_natDegree_le_one f s fun ik => by
        simp only [s]
        split_ifs
        · exact (Polynomial.natDegree_add_le _ _).trans (by simp)
        · simp
    _ = δ := htot

end GlobalTheory.CompHt.PointLow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdelicGLMemIntegralCofinitePlacesStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteAdelicGL_mem_integral_cofinite_places : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (k : GL (Fin a) (Af E)), {w : HeightOneSpectrum (𝓞 E) | GeneralLinearGroup.map (pLoc E w) k ∉ KGL w a}.Finite := by
  first | exact @GlobalTheory.GLFinPlaces.gl_mem_int_cofinite | exact GlobalTheory.GLFinPlaces.gl_mem_int_cofinite | (intros; apply GlobalTheory.GLFinPlaces.gl_mem_int_cofinite <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePadicIntegersQuotPrimePowOfFiniteDim
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKLoc.IntFin

theorem finite_intK_quot_pow : ∀ (p : ℕ) [Fact p.Prime] (L : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] L] (m : ℕ),
    Finite (GlobalTheory.LKLoc.intK p L ⧸ Ideal.span {(p : GlobalTheory.LKLoc.intK p L) ^ m}) := by
  intro p _ L hL m
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have h := ReciprocityTheory.DiscreteGroups.LocalClassField.Euler.card_OK_quot_natCast p L hL (pow_ne_zero m hp)
  have hf : Finite (ReciprocityTheory.DiscreteGroups.LocalClassField.OK p L ⧸ Ideal.span {((p ^ m : ℕ) : ReciprocityTheory.DiscreteGroups.LocalClassField.OK p L)}) :=
    Nat.finite_of_card_ne_zero (by rw [h]; positivity)
  push_cast at hf
  exact hf

end GlobalTheory.LKLoc.IntFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePadicTensorUnramifiedIntegersQuotPrimePow
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.TenFin

theorem finite_quot_of_gen {R A B : Type} [CommRing R] [CommRing A] [CommRing B] (I : Ideal R)
    (f : A →+* R) (g : B →+* R) (J₁ : Ideal A) (J₂ : Ideal B) (h₁ : J₁.map f ≤ I) (h₂ : J₂.map g ≤ I)
    [Finite (A ⧸ J₁)] [Finite (B ⧸ J₂)] (hgen : Subring.closure (Set.range f ∪ Set.range g) = ⊤)
    (n : ℕ) (hn : n ≠ 0) (hI : (n : R) ∈ I) : Finite (R ⧸ I) := by
  let π := Ideal.Quotient.mk I
  let fa : A ⧸ J₁ →+* R ⧸ I := Ideal.Quotient.lift J₁ (π.comp f) (fun a ha =>
    Ideal.Quotient.eq_zero_iff_mem.2 (h₁ (Ideal.mem_map_of_mem f ha)))
  let gb : B ⧸ J₂ →+* R ⧸ I := Ideal.Quotient.lift J₂ (π.comp g) (fun a ha =>
    Ideal.Quotient.eq_zero_iff_mem.2 (h₂ (Ideal.mem_map_of_mem g ha)))
  have hfa : ∀ a, π (f a) = fa (Ideal.Quotient.mk J₁ a) := fun a => rfl
  have hgb : ∀ b, π (g b) = gb (Ideal.Quotient.mk J₂ b) := fun b => rfl
  let S : Set (R ⧸ I) := Set.image2 (· * ·) (Set.range fa) (Set.range gb)
  have hS : S.Finite := (Set.finite_range fa).image2 _ (Set.finite_range gb)
  let M : Submonoid (R ⧸ I) :=
    { carrier := S
      one_mem' := ⟨1, ⟨1, map_one _⟩, 1, ⟨1, map_one _⟩, one_mul 1⟩
      mul_mem' := by
        rintro _ _ ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, rfl⟩ ⟨_, ⟨a', rfl⟩, _, ⟨b', rfl⟩, rfl⟩
        refine ⟨fa (a * a'), ⟨_, rfl⟩, gb (b * b'), ⟨_, rfl⟩, ?_⟩
        simp only [map_mul]; ring }
  have hsub : π '' (Set.range f ∪ Set.range g) ⊆ (M : Set (R ⧸ I)) := by
    rintro _ ⟨_, ⟨a, rfl⟩ | ⟨b, rfl⟩, rfl⟩
    · exact ⟨fa (Ideal.Quotient.mk J₁ a), ⟨_, rfl⟩, 1, ⟨1, map_one _⟩, (mul_one _).trans (hfa a).symm⟩
    · exact ⟨1, ⟨1, map_one _⟩, gb (Ideal.Quotient.mk J₂ b), ⟨_, rfl⟩, (one_mul _).trans (hgb b).symm⟩
  have htop : AddSubgroup.closure S = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ Subring.closure (π '' (Set.range f ∪ Set.range g)) := by
      rw [← RingHom.map_closure, hgen, ← RingHom.range_eq_map]
      exact Ideal.Quotient.mk_surjective x
    rw [Subring.mem_closure_iff] at hx
    refine AddSubgroup.closure_mono ?_ hx
    exact Submonoid.closure_le.2 hsub
  haveI : AddGroup.FG (R ⧸ I) := ⟨⟨hS.toFinset, by rw [Set.Finite.coe_toFinset]; exact htop⟩⟩
  refine AddCommGroup.finite_of_fg_torsion _ fun x => ?_
  refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨n, Nat.pos_of_ne_zero hn, ?_⟩
  rw [nsmul_eq_mul]
  have : (n : R ⧸ I) = 0 := by
    rw [← map_natCast π]; exact Ideal.Quotient.eq_zero_iff_mem.2 hI
  rw [this, zero_mul]

theorem finite_intKQ_quot : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r m : ℕ),
    Finite (GlobalTheory.LKLoc.intK p K ⧸ Ideal.span {(p : GlobalTheory.LKLoc.intK p K) ^ m}) →
    Finite (GlobalTheory.LKLoc.intK p (Qr p r) ⧸ Ideal.span {(p : GlobalTheory.LKLoc.intK p (Qr p r)) ^ m}) →
    Finite (intKQ p K r ⧸ Ideal.span {(p : intKQ p K r) ^ m}) := by
  intro p _ K r m hA hB
  let f : GlobalTheory.LKLoc.intK p K →+* intKQ p K r :=
    ((inclK p K r).toRingHom.comp (GlobalTheory.LKLoc.intK p K).subtype).codRestrict (intKQ p K r)
      (fun a => Subring.subset_closure (Or.inl ⟨a, rfl⟩))
  let g : GlobalTheory.LKLoc.intK p (Qr p r) →+* intKQ p K r :=
    ((inclQ p K r).toRingHom.comp (GlobalTheory.LKLoc.intK p (Qr p r)).subtype).codRestrict (intKQ p K r)
      (fun b => Subring.subset_closure (Or.inr ⟨⟨b.1, b.2⟩, rfl⟩))
  have hgen : Subring.closure (Set.range f ∪ Set.range g) = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨x, hx⟩ -
    induction hx using Subring.closure_induction with
    | mem y hy =>
      rcases hy with ⟨a, rfl⟩ | ⟨b, rfl⟩
      · exact Subring.subset_closure (Or.inl ⟨a, rfl⟩)
      · exact Subring.subset_closure (Or.inr ⟨⟨b.1, b.2⟩, rfl⟩)
    | zero => exact zero_mem _
    | one => exact one_mem _
    | add y z _ _ h1 h2 => exact add_mem h1 h2
    | neg y _ h => exact neg_mem h
    | mul y z _ _ h1 h2 => exact mul_mem h1 h2
  refine finite_quot_of_gen (J₁ := Ideal.span {(p : GlobalTheory.LKLoc.intK p K) ^ m})
    (J₂ := Ideal.span {(p : GlobalTheory.LKLoc.intK p (Qr p r)) ^ m}) _ f g ?_ ?_ hgen (p ^ m) (pow_ne_zero _ (Fact.out : p.Prime).ne_zero) ?_
  · rw [Ideal.map_span, Set.image_singleton, map_pow, map_natCast]
  · rw [Ideal.map_span, Set.image_singleton, map_pow, map_natCast]
  · rw [Nat.cast_pow]; exact Ideal.subset_span rfl

end GlobalTheory.TenFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankJointEigenspaceAddConjEqMulStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieType
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_jointEigenspace_add_conj_eq_mul : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (D' : PLat D.O D.inv) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (Q : D'.La →+ (Fin D.g → ℂ)), IsPeriod D' ρ Q → ∀ τ : D.F →+* ℂ, Module.finrank ℂ (eigSp (ρ.comp (algebraMap (𝓞 D.F) D.O)) τ) + Module.finrank ℂ (eigSp (ρ.comp (algebraMap (𝓞 D.F) D.O)) ((starRingEnd ℂ).comp τ)) = D.m * D.n := by
  first | exact @GlobalTheory.UPel.HT.LieType.finrank_eigSp_add_conj_eq | exact GlobalTheory.UPel.HT.LieType.finrank_eigSp_add_conj_eq | (intros; apply GlobalTheory.UPel.HT.LieType.finrank_eigSp_add_conj_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumDoubleCosetEqFinsumOrbit
section
open GlobalTheory.LKCount

namespace GlobalTheory.LKCount

variable {Γ G : Type} [Group Γ] [Group G]

noncomputable def doubleCosetToOrbit (ι : Γ →* G) (H : Subgroup Γ) (K : Subgroup G) :
    DoubleCoset.Quotient ((H.map ι : Subgroup G) : Set G) (K : Set G) →
      MulAction.orbitRel.Quotient H (LeftCosets ι K) :=
  Quotient.lift (fun x => (Quotient.mk (MulAction.orbitRel H (LeftCosets ι K)) (LeftCosets.mk ι K x))) (by
    intro a b hab
    obtain ⟨_, ⟨h, hh, rfl⟩, k, hk, rfl⟩ := DoubleCoset.rel_iff.1 hab
    refine (Quotient.sound ?_).symm
    refine ⟨⟨h, hh⟩, ?_⟩
    show LeftCosets.mk ι K (ι h * a) = LeftCosets.mk ι K (ι h * a * k)
    rw [LeftCosets.mk_eq_mk]
    convert hk using 1
    group)

theorem doubleCosetToOrbit_mk (ι : Γ →* G) (H : Subgroup Γ) (K : Subgroup G) (x : G) :
    doubleCosetToOrbit ι H K (DoubleCoset.mk _ _ x) =
      Quotient.mk (MulAction.orbitRel H (LeftCosets ι K)) (LeftCosets.mk ι K x) := rfl

theorem doubleCosetToOrbit_bijective (ι : Γ →* G) (H : Subgroup Γ) (K : Subgroup G) :
    Function.Bijective (doubleCosetToOrbit ι H K) := by
  constructor
  · intro p q hpq
    rw [← DoubleCoset.out_eq' _ _ p, ← DoubleCoset.out_eq' _ _ q] at hpq ⊢
    rw [doubleCosetToOrbit_mk, doubleCosetToOrbit_mk] at hpq
    obtain ⟨h, hh⟩ := Quotient.exact hpq
    have hh' : LeftCosets.mk ι K (ι (h : Γ) * q.out) = LeftCosets.mk ι K p.out := hh
    rw [LeftCosets.mk_eq_mk] at hh'
    refine ((DoubleCoset.eq _ _ _ _).2 ⟨ι h, Subgroup.mem_map_of_mem ι h.2, _, hh', ?_⟩).symm
    group
  · intro o
    induction o using Quotient.inductionOn with
    | h y =>
      refine ⟨DoubleCoset.mk _ _ (LeftCosets.rep ι K y), ?_⟩
      rw [doubleCosetToOrbit_mk, LeftCosets.mk_rep]

theorem finsum_doubleCoset_eq_finsum_orbit {Γ G : Type} [Group Γ] [Group G] (ι : Γ →* G) (H : Subgroup Γ)
    (K : Subgroup G) (g : LeftCosets ι K → ℂ) (hg : ∀ h ∈ H, ∀ y : LeftCosets ι K, g (h • y) = g y) :
    ∑ᶠ q : DoubleCoset.Quotient ((H.map ι : Subgroup G) : Set G) (K : Set G), g (LeftCosets.mk ι K (Quotient.out q)) =
      ∑ᶠ o : MulAction.orbitRel.Quotient H (LeftCosets ι K), g (Quotient.out o) := by
  let e := Equiv.ofBijective _ (doubleCosetToOrbit_bijective ι H K)
  rw [← finsum_comp_equiv e]
  refine finsum_congr fun q => ?_
  have hq : e q = Quotient.mk (MulAction.orbitRel H (LeftCosets ι K)) (LeftCosets.mk ι K q.out) := by
    show doubleCosetToOrbit ι H K q = _
    conv_lhs => rw [← DoubleCoset.out_eq' _ _ q]
    rfl
  rw [hq]
  obtain ⟨h, hh⟩ := Quotient.exact (Quotient.out_eq
    (Quotient.mk (MulAction.orbitRel H (LeftCosets ι K)) (LeftCosets.mk ι K q.out)))
  rw [← hh]
  exact (hg h h.2 _).symm

end GlobalTheory.LKCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumDoubleCosetFoldIntermediateSubgroupStatement
section
open GlobalTheory.LKCount
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finsum_doubleCoset_fold_intermediate_subgroup : ∀ {G : Type} [Group G] (Γ' T K : Subgroup G) (F : G → ℂ), Γ' ≤ T → (∀ t ∈ T, ∀ x, ∀ k ∈ K, F (t * x * k) = F x) → (∀ x : G, ((Γ' ⊓ K.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G).Finite) → {q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G) | F (Quotient.out q) ≠ 0}.Finite → ∑ᶠ q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G), ((Nat.card (Γ' ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom : Subgroup G) : ℕ) : ℂ)⁻¹ * F (Quotient.out q) = ∑ᶠ y : DoubleCoset.Quotient (T : Set G) (K : Set G), ((massC Γ' T (T ⊓ K.map (MulAut.conj (Quotient.out y)).toMonoidHom) : ℚ) : ℂ) * F (Quotient.out y) := by
  first | exact @GlobalTheory.finsum_fold_intermediate | exact GlobalTheory.finsum_fold_intermediate | (intros; apply GlobalTheory.finsum_fold_intermediate <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumOrbitsEqFinsumConjClasses
section
open GlobalTheory.LKCount GlobalTheory.OrbitUnfold

namespace GlobalTheory.OrbitUnfold

theorem finsum_orbits_eq_finsum_conjClasses : ∀ {Γ Y : Type} [Group Γ] [MulAction Γ Y] (F : Y → Γ → ℂ), (∀ (η : Γ) (y : Y) (γ : Γ), F (η • y) (η * γ * η⁻¹) = F y γ) → (∀ y : Y, (MulAction.stabilizer Γ y : Set Γ).Finite) → (∀ y : Y, (Function.support (F y)).Finite) → {o : MulAction.orbitRel.Quotient Γ Y | ∃ γ, F (Quotient.out o) γ ≠ 0}.Finite → ∑ᶠ o : MulAction.orbitRel.Quotient Γ Y, ((Nat.card (MulAction.stabilizer Γ (Quotient.out o)) : ℕ) : ℂ)⁻¹ * ∑ᶠ γ : Γ, F (Quotient.out o) γ = ∑ᶠ c : ConjClasses Γ, ∑ᶠ o : MulAction.orbitRel.Quotient (Subgroup.centralizer {Quotient.out c}) Y, ((Nat.card (MulAction.stabilizer Γ (Quotient.out o) ⊓ Subgroup.centralizer {Quotient.out c} : Subgroup Γ) : ℕ) : ℂ)⁻¹ * F (Quotient.out o) (Quotient.out c) := by
  intro Γ Y _ _ F hF hst hs ho
  rw [GlobalTheory.T.weightedOrbitSum_eq_pairOrbitSum F hF hst hs ho, GlobalTheory.T.finsum_conjClasses_centralizer_orbits_eq_pairOrbits F hF hst hs ho]

end GlobalTheory.OrbitUnfold
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FischerPairingAdjointLowerBlockStatement
section
open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fischer_pairing_adjoint_lower_block : ∀ (P Q S : ℕ) (h : Q ≤ S) (k' : ℕ) (b b' : Fin Q) (G : Mdl P Q) (f : Pol P Q 0 S), GlobalTheory.DefLift.BilFischer.pair (fockAct1 P Q 0 S (Eab (Sum.inr b) (Sum.inr b')) f) (embS P Q S h k' G) = GlobalTheory.DefLift.BilFischer.pair f (embS P Q S h k' (opS P Q S k' (Sum.inr b) (Sum.inr b') G)) := by
  first | exact @GlobalTheory.CharPair.SecondBlockS.pair_fockAct1_inr_inr_embS | exact GlobalTheory.CharPair.SecondBlockS.pair_fockAct1_inr_inr_embS | (intros; apply GlobalTheory.CharPair.SecondBlockS.pair_fockAct1_inr_inr_embS <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FischerPairingAdjointMixedLowerStatement
section
open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fischer_pairing_adjoint_mixed_lower : ∀ (P Q S : ℕ) (h : Q ≤ S) (k' : ℕ) (a : Fin P) (b : Fin Q) (G : Mdl P Q) (f : Pol P Q 0 S), GlobalTheory.DefLift.BilFischer.pair (fockAct1 P Q 0 S (Eab (Sum.inr b) (Sum.inl a)) f) (embS P Q S h k' G) = GlobalTheory.DefLift.BilFischer.pair f (embS P Q S h k' (opS P Q S k' (Sum.inr b) (Sum.inl a) G)) := by
  first | exact @GlobalTheory.CharPair.fockAct1_Eab_inr_inl_embS_pair | exact GlobalTheory.CharPair.fockAct1_Eab_inr_inl_embS_pair | (intros; apply GlobalTheory.CharPair.fockAct1_Eab_inr_inl_embS_pair <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FischerPairingAdjointMixedUpperStatement
section
open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fischer_pairing_adjoint_mixed_upper : ∀ (P Q S : ℕ) (h : Q ≤ S) (k' : ℕ) (a : Fin P) (b : Fin Q) (G : Mdl P Q) (f : Pol P Q 0 S), GlobalTheory.DefLift.BilFischer.pair (fockAct1 P Q 0 S (Eab (Sum.inl a) (Sum.inr b)) f) (embS P Q S h k' G) = GlobalTheory.DefLift.BilFischer.pair f (embS P Q S h k' (opS P Q S k' (Sum.inl a) (Sum.inr b) G)) := by
  first | exact @GlobalTheory.CharPair.pair_fockAct1_embS_up | exact GlobalTheory.CharPair.pair_fockAct1_embS_up | (intros; apply GlobalTheory.CharPair.pair_fockAct1_embS_up <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FischerPairingAdjointUpperBlockStatement
section
open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fischer_pairing_adjoint_upper_block : ∀ (P Q S : ℕ) (h : Q ≤ S) (k' : ℕ) (a a' : Fin P) (G : Mdl P Q) (f : Pol P Q 0 S), GlobalTheory.DefLift.BilFischer.pair (fockAct1 P Q 0 S (Eab (Sum.inl a) (Sum.inl a')) f) (embS P Q S h k' G) = GlobalTheory.DefLift.BilFischer.pair f (embS P Q S h k' (opS P Q S k' (Sum.inl a) (Sum.inl a') G)) := by
  first | exact @GlobalTheory.CharPair.ActSFirstBlock.pair_act_first_block | exact GlobalTheory.CharPair.ActSFirstBlock.pair_act_first_block | (intros; apply GlobalTheory.CharPair.ActSFirstBlock.pair_act_first_block <;> assumption)
end

