import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0383
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0438
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0359
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0395
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0400
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0439
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuationTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0415
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0426
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0416
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0417
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0440
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0401
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0407
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0414
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0410
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrPreservesHomology
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0369
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0430
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0429
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0252
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0277
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0371
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0328

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiGPairingEqChGPairing
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory

theorem psiG_pairing_eq_chG_pairing : ∀ (F : Type) [Field F] [Finite F], ∀ (S : F[X] → ℂ) (n : ℕ)
    (Y : GL (Fin n) F → ℂ), IsChar ℂ ℂ Y → HFree Y →
    ∑ᶠ x, psiG S n x * star (Y x) = ∑ᶠ x, chG S n x * star (Y x) := by
  intro F _ _ S n Y hY hF
  have hfin : Finite (GL (Fin n) F) := inferInstance
  have hfs : ∀ f : GL (Fin n) F → ℂ, (Function.support f).Finite := fun f => Set.toFinite _
  have hz : ∀ a ∈ Finset.range n,
      ∑ᶠ x, hc a (n - a) (psiG S a) (fun _ => 1) n x * star (Y x) = 0 := by
    intro a ha
    have ha' : a < n := Finset.mem_range.mp ha
    exact GlobalTheory.T.harishChandraInductionGL_trivial_orthogonal_hyperplaneFixer F a (n - a) n (by omega) (by omega) (psiG S a) Y hY hF
  have hrec : ∀ x, psiG S n x * star (Y x) = chG S n x * star (Y x)
      - ∑ a ∈ Finset.range n, hc a (n - a) (psiG S a) (fun _ => 1) n x * star (Y x) := by
    intro x
    rw [GlobalTheory.T.primitiveFunctionCharpolyGL_harishChandra_recursion F S n x, sub_mul, Finset.sum_mul]
  simp_rw [hrec]
  rw [finsum_sub_distrib (hfs _) (hfs _), finsum_sum_comm (Finset.range n) _ (fun a _ => hfs _),
    Finset.sum_eq_zero hz, sub_zero]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackProjBundleFormulaMapOfFactorStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_projBundleFormulaMap_of_factor : DivisorNaturality → ∀ (q : ℕ) [NeZero q] {E B P : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) (L : B ⟶ ofCat (glCat 1)) (θ : P ⟶ pullback V (PGL.pr N)) (f : P ⟶ E) (g : P ⟶ B), Inv q B → Inv q (pullback V (PGL.pr N)) → θ ≫ pullback.fst _ _ = f → θ ≫ pullback.snd _ _ ≫ PGL.line N = g ≫ L → ∀ (n i : ℤ) (a : ∀ j : Fin N, Ht q E (n - 2 * (j : ℕ)) (i - (j : ℕ))), pull _ θ _ _ (pbfMap q V n i a) = ∑ j : Fin N, ((cup q (pull _ f _ _ (a j)) (pull _ g _ _ (cpow q (c1 q L) j))).cast (by ring) (by ring) : Ht q P n i) := by
  first | (exact @GlobalTheory.EtC.PbfNatl.pull_pbfMap_of_factor) | (exact GlobalTheory.EtC.PbfNatl.pull_pbfMap_of_factor) | (intros; apply GlobalTheory.EtC.PbfNatl.pull_pbfMap_of_factor  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiIsoHypercohomologyBijectiveStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasiIso_hypercohomology_bijective : GlobalTheory.EtC.A1 := by
  first | (exact @GlobalTheory.EtC.quasiIso_hypercohomology_bijective') | (exact GlobalTheory.EtC.quasiIso_hypercohomology_bijective') | (intros; apply GlobalTheory.EtC.quasiIso_hypercohomology_bijective'  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RebasedTypicalCurvesIsBasisStatement
section
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.DepthStages
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rebased_typical_curves_isBasis : ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ),
    p.Prime → v (p : C) = 1 → ∀ (d h : ℕ) (ty : Fin d → ZMod h) (G : LogFGL v d)
      (γ : Fin d → Fin d → PowerSeries C) (X : Matrix (Fin d) (Fin d) C),
      IsBasis G p ty γ → (∀ a b, IsIntV v (X a b)) → v X.det = 0 →
      (∀ a b, X a b ≠ 0 → ty b = ty a) →
      IsBasis G p ty (rebase G X γ) ∧
        (∀ a, tangent (rebase G X γ a) = ∑ b, X a b • tangent (γ b)) ∧
        ∀ a n, G.lc p (rebase G X γ a) n = ∑ b, X a b ^ (p ^ n) • G.lc p (γ b) n := by
  first | exact @GlobalTheory.DepthStages.RebaseBasis.rebase_isBasis | exact GlobalTheory.DepthStages.RebaseBasis.rebase_isBasis | (intros; apply GlobalTheory.DepthStages.RebaseBasis.rebase_isBasis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReductionToSiegelDomain
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC.ArtCoh

theorem ht_subsingleton_of_ringEquiv (q : ℕ) {R S : Type} [CommRing R] [CommRing S] (e : R ≃+* S) (n i : ℤ)
    [h : Subsingleton (Ht q (sp R) n i)] : Subsingleton (Ht q (sp S) n i) := by
  have hid : spMap (e : R →+* S) ≫ spMap (e.symm : S →+* R) = 𝟙 (sp S) := by
    rw [← Functor.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (e : R →+* S).comp (e.symm : S →+* R) = RingHom.id S := by ext x; simp
    rw [this]
    simp
  constructor
  intro x y
  have hx : pull _ (spMap (e : R →+* S)) _ _ (pull _ (spMap (e.symm : S →+* R)) _ _ x) = x := by
    rw [← pull_comp, hid, pull_id]
  have hy : pull _ (spMap (e : R →+* S)) _ _ (pull _ (spMap (e.symm : S →+* R)) _ _ y) = y := by
    rw [← pull_comp, hid, pull_id]
  rw [← hx, ← hy, Subsingleton.elim (pull _ (spMap (e.symm : S →+* R)) _ _ x)
    (pull _ (spMap (e.symm : S →+* R)) _ _ y)]

theorem ht_subsingleton_prod (q : ℕ) (A B : Type) [CommRing A] [CommRing B] (n i : ℤ)
    [Subsingleton (Ht q (sp A) n i)] [Subsingleton (Ht q (sp B) n i)] : Subsingleton (Ht q (sp (A × B)) n i) := by
  constructor
  intro x y
  exact (GlobalTheory.EtC.ProdCoh.ht_prod_bijective q A B n i).1 (Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _))

theorem ht_subsingleton_of_subsingleton (q : ℕ) (Z : Type) [CommRing Z] [Subsingleton Z] (n i : ℤ) :
    Subsingleton (Ht q (sp Z) n i) := by
  have hfs : RingHom.fst Z Z = RingHom.snd Z Z := by ext x; exact Subsingleton.elim _ _
  constructor
  intro a b
  obtain ⟨x, hx⟩ := (GlobalTheory.EtC.ProdCoh.ht_prod_bijective q Z Z n i).2 (a, b)
  have h1 := congrArg Prod.fst hx
  have h2 := congrArg Prod.snd hx
  simp only at h1 h2
  rw [hfs] at h1
  rw [← h1, ← h2]

theorem ht_subsingleton_pi (q : ℕ) (n i : ℤ) (ι : Type) [Finite ι] : ∀ (R : ι → Type) [∀ j, CommRing (R j)],
    (∀ j, Subsingleton (Ht q (sp (R j)) n i)) → Subsingleton (Ht q (sp (∀ j, R j)) n i) := by
  induction ι using Finite.induction_empty_option with
  | of_equiv e ih =>
    intro R _ hR
    have := ih (fun a => R (e a)) (fun a => hR (e a))
    exact ht_subsingleton_of_ringEquiv q (RingEquiv.piCongrLeft R e) n i
  | h_empty =>
    intro R _ _
    exact ht_subsingleton_of_subsingleton q _ n i
  | h_option ih =>
    intro R _ hR
    have h1 := hR none
    have h2 := ih (fun a => R (some a)) (fun a => hR (some a))
    have := ht_subsingleton_prod q (R none) (∀ a, R (some a)) n i
    exact ht_subsingleton_of_ringEquiv q (RingEquiv.piOptionEquivProd (R := R)).symm n i

theorem ht_subsingleton_artinian : ∀ (q : ℕ) (K : Type) [CommRing K] [IsArtinianRing K] [IsReduced K] (n i : ℤ),
    (∀ M : MaximalSpectrum K, Subsingleton (Ht q (sp (K ⧸ M.asIdeal)) n i)) → Subsingleton (Ht q (sp K) n i) := by
  intro q K _ _ _ n i h
  have := ht_subsingleton_pi q n i (MaximalSpectrum K) (fun M => K ⧸ M.asIdeal) h
  exact ht_subsingleton_of_ringEquiv q (IsArtinianRing.equivPi K).toRingEquiv.symm n i

end GlobalTheory.EtC.ArtCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularTopFormPoleOrderHeightOnePrime
section
set_option autoImplicit false

noncomputable section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.PD

theorem omB_top_coeff_iff_pole : ∀ (k F K : Type) [Field k] [CharZero k] [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] [FiniteDimensional F K] (d : ℕ) (u : Fin d → F), AlgebraicIndependent k u → ∀ (A : Subalgebra k F) [IsFractionRing A F], A = Algebra.adjoin k (Set.range u) → ∀ (B : Subalgebra k K), B = (integralClosure A K).restrictScalars k → Algebra.Smooth k B → ∀ τ : DR k K →ₗ[K] K, τ (ExteriorAlgebra.ιMulti K d fun j => D k K (algebraMap F K (u j))) = 1 → ∀ (Q : Ideal B), Q.IsPrime → Q.height = 1 → ∀ (t : A) (s : B) (e : ℕ), Irreducible t → 1 ≤ e → s ∈ Q → (∀ y ∈ Q, ∃ c r : B, r ∉ Q ∧ r * y = c * s) → (∃ a r : B, a ∉ Q ∧ r ∉ Q ∧ (r : K) * algebraMap F K t = a * s ^ e) → ∀ z : K, (∃ r : B, r ∉ Q ∧ ∃ y ∈ omB k K B d, τ y = r * z) ↔ ∃ c r : B, r ∉ Q ∧ (r : K) * s ^ (e - 1) * z = c := by
  intro k F K _ _ _ _ _ _ _ _ _ d u hu A _ hA B hB _ τ hτ Q hQ hQh t s e ht he hsQ hQs hts z
  obtain ⟨a₀, r₀, ha₀, hr₀, hrt⟩ := hts
  have htQ : ∀ b : B, (b : K) = algebraMap F K t → b ∈ Q := by
    intro b hb
    have h1 : r₀ * b = a₀ * s ^ e := Subtype.ext (by push_cast; rw [hb]; exact hrt)
    have h2 : r₀ * b ∈ Q := h1 ▸ Q.mul_mem_left _ (Q.pow_mem_of_mem hsQ e (by omega))
    exact (hQ.mem_or_mem h2).resolve_left hr₀
  have hcomap := GlobalTheory.T.mem_heightOne_prime_integralClosure_iff_dvd_irreducible k F K d u hu A hA B hB Q hQ hQh t ht htQ
  obtain ⟨htp, m, rfl, y, hy⟩ := GlobalTheory.T.polynomial_ring_irreducible_prime_reduction k F d u hu A hA t ht
  have hAft : Algebra.FiniteType k A := by
    subst hA
    classical
    exact (Subalgebra.fg_iff_finiteType _).1 ⟨Finset.univ.image u, by simp⟩
  have ht0 : t ≠ 0 := ht.ne_zero
  have hP : (Ideal.span {t}).IsPrime := (Ideal.span_singleton_prime ht0).2 htp
  have genA := GlobalTheory.T.exists_not_mem_smul_D_eq_sum k F K A (Ideal.span {t}) hP t (Ideal.mem_span_singleton_self t) ht0
    (fun y hy => by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
      exact ⟨c, 1, (Ideal.ne_top_iff_one _).1 hP.ne_top, by ring⟩) m y hy

  have memB : ∀ a : A, algebraMap F K (a : F) ∈ B := fun a => by
    rw [hB]; exact (Subalgebra.mem_restrictScalars k).2 ((integralClosure A K).algebraMap_mem a)
  let ιB : A → B := fun a => ⟨algebraMap F K (a : F), memB a⟩
  have hιQ : ∀ a : A, ιB a ∈ Q ↔ a ∈ Ideal.span {t} := fun a => by
    rw [Ideal.mem_span_singleton]; exact hcomap a (ιB a) rfl
  set du : DR k K := ExteriorAlgebra.ιMulti K (m + 1) fun j => D k K (algebraMap F K (u j)) with hdu
  have hdu0 : du ≠ 0 := fun h => by rw [h, map_zero] at hτ; exact zero_ne_one hτ
  set gA : Fin (m + 1) → Ω[K⁄k] := Fin.cons (D k K (algebraMap F K (t : F))) (fun j => D k K (algebraMap F K (y j : F))) with hgA
  obtain ⟨rA, hrA, aA, hA1⟩ := GlobalTheory.T.exterior_wedge_eq_of_localized_span A K Ω[K⁄k] (Ideal.span {t}).primeCompl (m + 1) gA (fun j => D k K (algebraMap F K (u j))) (fun i => by
    obtain ⟨r, hr, c, hc⟩ := genA ⟨u i, hA ▸ Algebra.subset_adjoin (Set.mem_range_self i)⟩
    exact ⟨r, hr, c, hc⟩)
  obtain ⟨r', hr', c', hA2⟩ := GlobalTheory.T.exterior_wedge_eq_of_localized_span A K Ω[K⁄k] (Ideal.span {t}).primeCompl (m + 1) (fun j => D k K (algebraMap F K (u j))) gA (fun i => by
    have key : ∀ v : A, ∃ c : Fin (m + 1) → A, D k K (algebraMap F K (v : F)) = ∑ l, algebraMap A K (c l) • D k K (algebraMap F K (u l)) := by
      intro v
      obtain ⟨c, hc, hc'⟩ := GlobalTheory.T.exists_D_eq_sum_smul_D_of_mem_adjoin k F K (m + 1) u (v : F) (hA ▸ v.2)
      exact ⟨fun j => ⟨c j, hA ▸ hc j⟩, hc'⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · obtain ⟨c, hc⟩ := key t
      exact ⟨1, Submonoid.one_mem _, c, by rw [map_one, one_smul]; exact hc⟩
    · obtain ⟨c, hc⟩ := key (y j)
      exact ⟨1, Submonoid.one_mem _, c, by rw [map_one, one_smul]; exact hc⟩)
  have hAeq : rA * r' = aA * c' := by
    apply FaithfulSMul.algebraMap_injective A K
    have h3 : (algebraMap A K (rA * r')) • du = (algebraMap A K (aA * c')) • du := by
      rw [map_mul, map_mul, mul_comm, mul_smul, hA1, smul_comm, hA2, smul_smul, mul_comm]
    exact smul_left_injective K hdu0 h3
  have haA : aA ∉ Ideal.span {t} := fun h => by
    have : rA * r' ∈ Ideal.span {t} := hAeq ▸ Ideal.mul_mem_right _ _ h
    rcases hP.mem_or_mem this with h4 | h4
    · exact hrA h4
    · exact hr' h4

  let y' : Fin m → B := fun j => ιB (y j)
  have hy' := GlobalTheory.T.isTranscendenceBasis_quotient_integralClosure' k F K A B hB Q hQ t hcomap m y hy y' (fun j => rfl)
  haveI := GlobalTheory.T.integralClosure_finiteType_over_adjoin k F K (m + 1) u hu A hA B hB
  have hs0 : s ≠ 0 := by
    rintro rfl
    have h5 : (r₀ : K) * algebraMap F K t = 0 := by rw [hrt]; simp [zero_pow (by omega : e ≠ 0)]
    rcases mul_eq_zero.1 h5 with h6 | h6
    · exact hr₀ (by rw [show r₀ = 0 from Subtype.ext h6]; exact Q.zero_mem)
    · exact ht0 (by
        have : (t : F) = 0 := (map_eq_zero_iff _ (algebraMap F K).injective).1 h6
        exact Subtype.ext this)
  have genB := GlobalTheory.T.exists_not_mem_smul_D_eq_sum k K K B Q hQ s hsQ hs0 hQs m y' hy'
  simp only [Algebra.algebraMap_self_apply] at genB
  obtain ⟨N, Dn, hN, hDn, hND⟩ := GlobalTheory.T.differential_relation_local_ring_bound k K B Q hQ s m (fun j => (y' j : K)) (algebraMap F K t) e he hsQ genB ⟨a₀, r₀, ha₀, hr₀, hrt⟩
  set ω : DR k K := ExteriorAlgebra.ιMulti K (m + 1) (Fin.cons (D k K (s : K)) (fun j => D k K (y' j : K)) : Fin (m + 1) → Ω[K⁄k]) with hω
  let Dt : B := Dn * ιB rA
  let Nt : B := N * ιB aA
  have hDt : Dt ∉ Q := fun h => (hQ.mem_or_mem h).elim hDn (fun h' => hrA ((hιQ rA).1 h'))
  have hNt : Nt ∉ Q := fun h => (hQ.mem_or_mem h).elim hN (fun h' => haA ((hιQ aA).1 h'))
  have hmain : (Dt : K) • du = ((Nt : K) * (s : K) ^ (e - 1)) • ω := by
    have h7 : (Dn : K) • ExteriorAlgebra.ιMulti K (m + 1) gA = ((N : K) * (s : K) ^ (e - 1)) • ω := hND
    have hA1' : (algebraMap F K (rA : F)) • du = (algebraMap F K (aA : F)) • ExteriorAlgebra.ιMulti K (m + 1) gA := hA1
    show ((Dn : K) * algebraMap F K (rA : F)) • du = ((N : K) * algebraMap F K (aA : F) * (s : K) ^ (e - 1)) • ω
    rw [mul_smul, hA1', smul_comm, h7, smul_smul]
    congr 1
    ring
  have hkey : (Dt : K) = (Nt : K) * (s : K) ^ (e - 1) * τ ω := by
    have := congrArg τ hmain
    rw [map_smul, map_smul, hτ, smul_eq_mul, smul_eq_mul, mul_one] at this
    rw [this]
  have hv0 : (Fin.cons (D k K (s : K)) (fun j => D k K (y' j : K)) : Fin (m + 1) → Ω[K⁄k]) = fun j => D k K ((Fin.cons (s : K) (fun j => (y' j : K)) : Fin (m + 1) → K) j) := by
    funext j; exact Fin.cases rfl (fun j => rfl) j
  have hωmem : ∀ b : B, (b : K) • ω ∈ omB k K B (m + 1) := fun b => by
    refine Submodule.subset_span ⟨b, b.2, Fin.cons (s : K) (fun j => (y' j : K)), fun j => Fin.cases s.2 (fun j => (y' j).2) j, ?_⟩
    rw [hω, hv0]
  have P : ∀ yy ∈ omB k K B (m + 1), ∃ c ρ : B, ρ ∉ Q ∧ (ρ : K) * (s : K) ^ (e - 1) * τ yy = c := by
      intro yy hyy
      unfold omB at hyy
      induction hyy using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨b, hb, v, hv, rfl⟩ := hx
        obtain ⟨ρ, hρ, β, hβ⟩ := GlobalTheory.T.exterior_wedge_eq_of_localized_span B K Ω[K⁄k] Q.primeCompl (m + 1) (Fin.cons (D k K (s : K)) (fun j => D k K (y' j : K))) (fun j => D k K (v j)) (fun i => genB ⟨v i, hv i⟩)
        have hβ' : (ρ : K) • ExteriorAlgebra.ιMulti K (m + 1) (fun j => D k K (v j)) = (β : K) • ω := hβ
        have h8 := congrArg τ hβ'
        rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul] at h8
        refine ⟨⟨b, hb⟩ * β * Dt, ρ * Nt, fun h => (hQ.mem_or_mem h).elim hρ hNt, ?_⟩
        rw [map_smul, smul_eq_mul]
        push_cast
        rw [hkey]
        linear_combination ((b : K) * (Nt : K) * (s : K) ^ (e - 1)) * h8
      | zero => exact ⟨0, 1, (Ideal.ne_top_iff_one _).1 hQ.ne_top, by simp⟩
      | add x w _ _ hx hw =>
        obtain ⟨c1, ρ1, h1, e1⟩ := hx
        obtain ⟨c2, ρ2, h2, e2⟩ := hw
        refine ⟨ρ2 * c1 + ρ1 * c2, ρ1 * ρ2, fun h => (hQ.mem_or_mem h).elim h1 h2, ?_⟩
        rw [map_add]; push_cast
        linear_combination (ρ2 : K) * e1 + (ρ1 : K) * e2
      | smul a x _ hx =>
        obtain ⟨c, ρ, h1, e1⟩ := hx
        refine ⟨algebraMap k B a * c, ρ, h1, ?_⟩
        rw [τ.map_smul_of_tower, Algebra.smul_def]
        push_cast
        rw [← e1]
        ring
  constructor
  · rintro ⟨r, hr, yy, hyy, hτy⟩
    obtain ⟨c, ρ, hρ, hc⟩ := P yy hyy
    refine ⟨c, ρ * r, fun h => (hQ.mem_or_mem h).elim hρ hr, ?_⟩
    rw [← hc, hτy]; push_cast; ring
  · rintro ⟨c, r, hr, hc⟩
    refine ⟨Dt * r, fun h => (hQ.mem_or_mem h).elim hDt hr, ((c * Nt : B) : K) • ω, hωmem _, ?_⟩
    rw [map_smul, smul_eq_mul]
    push_cast
    rw [hkey]
    linear_combination (-((Nt : K) * τ ω)) * hc

end GlobalTheory.PD
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictScalarsResolutionMapAugmentationSpec
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

section
variable {R S : Type} [CommRing R] [CommRing S]

def rcxSemi (φ : R →+* S) {K : Cx S} {J : Cx R} (m : (rcx φ).obj K ⟶ J) : SemiMap K J where
  app U s := ((m.f s).hom.app (op U)).hom.toAddMonoidHom
  nat g s a := (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom ((m.f s).hom.naturality g.op)) a).symm
  comm U s t a := by
    have h := congrArg (fun k => ((k.hom.app (op U)).hom a)) (m.comm s t)
    refine Eq.trans ?_ (h.trans ?_) <;> rfl

theorem rcxSemi_app (φ : R →+* S) {K : Cx S} {J : Cx R} (m : (rcx φ).obj K ⟶ J) (U : Scheme.{0}) (s : ℤ)
    (a : Sec (K.X s) U) : (rcxSemi φ m).app U s a = Sec.map (m.f s) (show Sec ((restr φ).obj (K.X s)) U from a) := rfl

end

theorem restrMap_exists : ∀ (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (F : Shv S), ∃ ρ : SemiMap (res S F) (res R ((restr φ).obj F)),
    ∀ (U : Scheme.{0}) (a : Sec F U),
      ρ.app U 0 (Sec.map (resι S F) a) = Sec.map (resι R ((restr φ).obj F)) (show Sec ((restr φ).obj F) U from a) := by
  intro R S _ _ φ F
  obtain ⟨hKI, -, hGE, -, hι, -⟩ := GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties R ((restr φ).obj F)
  obtain ⟨-, -, -, hq, hιS, -⟩ := GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties S F
  have := rAug_quasiIso φ (resAug F)
  obtain ⟨m, hm⟩ := (GlobalTheory.T.extend_chainMap_along_quasiIso_kInjective R ((restr φ).obj F) ((rcx φ).obj (res S F)) (res R ((restr φ).obj F))
    (rAug φ (resAug F))).1 (resAug ((restr φ).obj F))
  refine ⟨rcxSemi φ m, fun U a => ?_⟩
  rw [rcxSemi_app]
  have h1 : Sec.map (resι S F) a = Sec.map ((resAug F).f 0) (Sec.map (sglι F) a) := by
    rw [← hιS]; rfl
  have h2 := rAug_f_zero φ (resAug F) U a
  have h3 : Sec.map (resι R ((restr φ).obj F)) (show Sec ((restr φ).obj F) U from a) =
      Sec.map (((rAug φ (resAug F)) ≫ m).f 0) (Sec.map (sglι ((restr φ).obj F)) (show Sec ((restr φ).obj F) U from a)) := by
    rw [hm, ← hι]; rfl
  rw [h3, h1, ← h2]
  rfl

theorem restrMap_spec' : ∀ (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (F : Shv S) (U : Scheme.{0}) (a : Sec F U), (restrMap φ F).app U 0 (Sec.map (resι S F) a) = Sec.map (resι R ((restr φ).obj F)) (show Sec ((restr φ).obj F) U from a) := by
  intro R S _ _ φ F U a
  exact pick_spec (restrMap_exists R S φ F) U a

end GlobalTheory.EtC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootExtractionLemmaSheaf
section
namespace GlobalTheory.RootTrick

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

theorem root_statement : RootStatement := by
  intro C _ _ _ v p hp hv d h m ty i G γ hγ hty n j _hn V _ _ La hdim
  obtain ⟨x, hxi, hxd, hxk⟩ := GlobalTheory.T.exists_integral_unimodular_matrix_for_depth C v V (p ^ n) (pow_pos hp.pos n) j m
    (fun u => La (G.lc p (γ u) n)) hdim
  refine ⟨x, hxi, hxd, ?_⟩
  have h6 := fun w => pt6' C v p hp hv d m G γ (x w) hγ (hxi w)
  dsimp only at h6 ⊢
  refine ⟨fun w => (h6 w).2.1, fun w => ⟨(h6 w).2.2.2 (fun u => (hty u).1), fun k a hk => ?_⟩,
    fun w hw => ?_⟩
  · rw [(h6 w).2.2.1 k]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, (hty _).2 k a hk, mul_zero,
      Finset.sum_const_zero]
  · rw [(h6 w).2.2.1 n, map_sum]
    simp only [map_smul]
    exact hxk w hw

end GlobalTheory.RootTrick
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootTrickFinsetCurvesBlockInverseStatement
section
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.DepthStages
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_trick_finset_curves_block_inverse : RootStatement → ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ),
    p.Prime → v (p : C) = 1 → ∀ (d h : ℕ) (ty : Fin d → ZMod h) (i : ZMod h) (G : LogFGL v d)
      (γ : Fin d → Fin d → PowerSeries C) (S : Finset (Fin d)),
      (∀ a ∈ S, IsCurve v (γ a)) → (∀ a ∈ S, G.IsOfType p ty i (γ a)) → ∀ (n j : ℕ), 1 ≤ n →
      ∀ (V : Type) [AddCommGroup V] [Module C V] (La : (Fin d → C) →ₗ[C] V),
        Module.finrank C (Submodule.span C
          ((fun a => La (G.lc p (γ a) n)) '' (S : Set (Fin d)))) ≤ j →
        ∃ (x y : Matrix (Fin d) (Fin d) C) (D : Finset (Fin d)), D ⊆ S ∧ D.card ≤ j ∧
          (∀ a b, IsIntV v (x a b)) ∧ (∀ a b, IsIntV v (y a b)) ∧
          (∀ a b, x a b ≠ 0 → a ∈ S ∧ b ∈ S) ∧ (∀ a b, y a b ≠ 0 → a ∈ S ∧ b ∈ S) ∧
          (∀ a c, a ∈ S → c ∈ S → ∑ b, x a b * y b c = if a = c then 1 else 0) ∧
          ∀ a ∈ S, a ∉ D → La (∑ b, x a b ^ (p ^ n) • G.lc p (γ b) n) = 0 := by
  first | exact @GlobalTheory.RootFin.root_fin | exact GlobalTheory.RootFin.root_fin | (intros; apply GlobalTheory.RootFin.root_fin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootsReverseProd
section
noncomputable section

open Polynomial CategoryTheory

namespace GlobalTheory.DualLabel

theorem roots_reverse_prod {K : Type} [Field K] (s : Multiset K) (hs : (0 : K) ∉ s) :
    ((s.map fun x => X - C x).prod.reverse).roots = s.map (·⁻¹) := by
  induction s using Multiset.induction_on with
  | empty => simp [reverse]
  | cons a s ih =>
    rw [Multiset.mem_cons, not_or] at hs
    have ha : a ≠ 0 := fun h => hs.1 h.symm
    have hX : (X : K[X]).reverse = 1 := by simp [reverse]
    have e : (X - C a : K[X]).reverse = C (-a) * (X - C a⁻¹) := by
      rw [sub_eq_add_neg, ← C_neg, reverse_add_C, natDegree_X, hX, mul_sub, ← C_mul, neg_mul,
        mul_inv_cancel₀ ha]
      simp [add_comm]
    have hm : (s.map fun x => X - C x).prod ≠ 0 :=
      (monic_multiset_prod_of_monic _ _ fun x _ => monic_X_sub_C x).ne_zero
    rw [Multiset.map_cons, Multiset.prod_cons, reverse_mul_of_domain, e, roots_mul, roots_C_mul _ (neg_ne_zero.2 ha),
      roots_X_sub_C, ih hs.2, Multiset.map_cons, Multiset.singleton_add]
    exact mul_ne_zero (mul_ne_zero (C_ne_zero.2 (neg_ne_zero.2 ha)) (X_sub_C_ne_zero _))
      (by rwa [Ne, reverse_eq_zero])

theorem monic_normRev {K : Type} [Field K] {f : K[X]} (h0 : f.coeff 0 ≠ 0) :
    (C (f.coeff 0)⁻¹ * f.reverse).Monic := by
  rw [Monic, leadingCoeff_mul, leadingCoeff_C, reverse_leadingCoeff, trailingCoeff_eq_coeff_zero h0,
    inv_mul_cancel₀ h0]

theorem rootsBar_normRev {K : Type} [Field K] {f : K[X]} (hm : f.Monic) (h0 : f.coeff 0 ≠ 0) :
    Formalism.IrreducibleCountingLemmas.TYPES.rootsBar K (C (f.coeff 0)⁻¹ * f.reverse) =
      (Formalism.IrreducibleCountingLemmas.TYPES.rootsBar K f).map (·⁻¹) := by
  have hz : (0 : AlgebraicClosure K) ∉ Formalism.IrreducibleCountingLemmas.TYPES.rootsBar K f := fun h => by
    rw [Formalism.IrreducibleCountingLemmas.TYPES.rootsBar, mem_roots (hm.map _).ne_zero, IsRoot, ← coeff_zero_eq_eval_zero,
      coeff_map] at h
    exact h0 ((map_eq_zero _).1 h)
  have e : f.reverse.map (algebraMap K (AlgebraicClosure K)) = (f.map (algebraMap K (AlgebraicClosure K))).reverse := by
    rw [reverse, reverse, reflect_map, natDegree_map]
  have hf := (IsAlgClosed.splits (f.map (algebraMap K (AlgebraicClosure K)))).eq_prod_roots_of_monic (hm.map _)
  rw [Formalism.IrreducibleCountingLemmas.TYPES.rootsBar, Polynomial.map_mul, map_C, roots_C_mul _ (by simpa using h0), e, hf]
  exact roots_reverse_prod _ hz

theorem eq_of_rootsBar_eq {K : Type} [Field K] {f g : K[X]} (hf : f.Monic) (hg : g.Monic)
    (h : Formalism.IrreducibleCountingLemmas.TYPES.rootsBar K f = Formalism.IrreducibleCountingLemmas.TYPES.rootsBar K g) : f = g := by
  apply map_injective (algebraMap K (AlgebraicClosure K)) (algebraMap K (AlgebraicClosure K)).injective
  rw [(IsAlgClosed.splits (f.map (algebraMap K (AlgebraicClosure K)))).eq_prod_roots_of_monic (hf.map _),
    (IsAlgClosed.splits (g.map (algebraMap K (AlgebraicClosure K)))).eq_prod_roots_of_monic (hg.map _)]
  exact congrArg (fun s => (s.map fun a => X - C a).prod) h

theorem lab_dual : ∀ {K : Type} [Field K] [Fintype K] [DecidableEq K] {C : Formalism.IrreducibleCountingLemmas.TYPES.LabelConv K}
    (O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap K C), Formalism.IrreducibleCountingLemmas.TYPES.LabelMapEquivariant O →
    ∀ (d : ℕ) (τ τ' : FDRep ℂ (GL (Fin d) K)), 1 ≤ d → Simple τ → Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal K τ → Simple τ' →
    Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal K τ' →
    (∀ γ : GL (Fin d) K, LinearMap.trace ℂ τ'.V (τ'.ρ γ) = LinearMap.trace ℂ τ.V (τ.ρ γ⁻¹)) →
    O.lab d τ' = Polynomial.C ((O.lab d τ).coeff 0)⁻¹ * (O.lab d τ).reverse := by
  intro K _ _ _ C O hO d τ τ' hd hs hc hs' hc' htr
  have h := hO.2 d τ τ' hd hs hc hs' hc' htr
  obtain ⟨hm, hi, hX, -⟩ := O.lab_spec d τ hd hs hc
  have h0 := Formalism.L2.NT.coeff_zero_ne_of_monic_irr hm hi hX
  refine eq_of_rootsBar_eq (O.lab_spec d τ' hd hs' hc').1 (monic_normRev h0) ?_
  rw [h, rootsBar_normRev hm h0]

end GlobalTheory.DualLabel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SandwichDatumEigenMultiplicity
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

theorem eig_decomp_T_H : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (GlobalTheory.Sandwich.root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ] (N h : ℕ), h = Module.finrank ℤ_[p] Λ * N → ∀ (D : Datum ε h Λ), (iSupIndep (fun σ : Λ →+* O => eig C (actT D) σ) ∧ (⨆ σ : Λ →+* O, eig C (actT D) σ) = ⊤ ∧ ∀ τ : Λ →+* O, Module.finrank C (eig C (actT D) τ) = N) ∧ (iSupIndep (fun σ : Λ →+* O => eig C (actH D) σ) ∧ (⨆ σ : Λ →+* O, eig C (actH D) σ) = ⊤ ∧ ∀ τ : Λ →+* O, Module.finrank C (eig C (actH D) τ) = N) := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε Λ _ _ _ _ _ _ N h hh D
  obtain ⟨⟨ρT, hρT⟩, ⟨ρH, hρH⟩⟩ := GlobalTheory.T.sandwich_datum_actions_ring_homs p O ε Λ h D
  have hT : ∀ a, (ρT a).trace = (N : O) * padicToO p O (Algebra.trace ℤ_[p] Λ a) := by
    intro a
    rw [congrFun hρT a, (GlobalTheory.T.sandwich_datum_trace_eq p C v O hv ε hε Λ h D a).2, GlobalTheory.T.rep_trace_eq_mul_algebra_trace p Λ N h hh D.ρT a,
      map_mul, map_natCast]
  have hH : ∀ a, (ρH a).trace = (N : O) * padicToO p O (Algebra.trace ℤ_[p] Λ a) := by
    intro a
    rw [congrFun hρH a, (GlobalTheory.T.sandwich_datum_trace_eq p C v O hv ε hε Λ h D a).1,
      (GlobalTheory.T.sandwich_datum_trace_eq p C v O hv ε hε Λ h D a).2, GlobalTheory.T.rep_trace_eq_mul_algebra_trace p Λ N h hh D.ρT a,
      map_mul, map_natCast]
  rw [← hρT, ← hρH]
  exact ⟨⟨GlobalTheory.T.eigenspaces_of_ring_homs_independent C O Λ h ρT hv.hom_inj, GlobalTheory.T.dvr_rep_eigenspaces_span_top p C v O hv Λ h ρT,
      GlobalTheory.T.rep_trace_eq_mul_algebra_trace_dvr p C v O hv Λ N h ρT hT⟩,
    ⟨GlobalTheory.T.eigenspaces_of_ring_homs_independent C O Λ h ρH hv.hom_inj, GlobalTheory.T.dvr_rep_eigenspaces_span_top p C v O hv Λ h ρH,
      GlobalTheory.T.rep_trace_eq_mul_algebra_trace_dvr p C v O hv Λ N h ρH hH⟩⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsComplexExactEtaleLocallyOfNoClassesStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sectionsComplex_exact_etaleLocally_of_no_classes : ∀ (R : Type) [CommRing R] (M : Cx R) (U : Scheme.{0}), (∀ n, Subsingleton (CohomologyClass ((chains R).obj (sch.obj U)) M n)) → ∀ (n : ℤ) (b : Sec (M.X n) U), Sec.map (M.d n (n + 1)) b = 0 → Loc U fun V g => ∃ a : Sec (M.X (n - 1)) V, Sec.map (M.d (n - 1) n) a = Sec.res g b := by
  first | (exact @GlobalTheory.EtC.sch_loc_exact) | (exact GlobalTheory.EtC.sch_loc_exact) | (intros; apply GlobalTheory.EtC.sch_loc_exact <;> assumption)
end

