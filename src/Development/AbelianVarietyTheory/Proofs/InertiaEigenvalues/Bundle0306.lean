import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualLatticeSetting
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0284
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0194
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0293
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0205
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RootEqOfNormLt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0256
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0278
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FundamentalMapSurjective
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.H2EquivOfTorsionCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0260
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0127
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorMemCocyclesPowQuot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachFunctorFullyFaithful
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelmerIffSelmerMatrixAtPrimes
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.IndefiniteRowSideFullHecke.ResidualLatticeSetting

namespace GlobalTheory.SelMatrixCompare

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N)

theorem l_mem_maximalIdeal (i : X.Tw) : ((X.l i : ℕ) : X.O0 i) ∈ IsLocalRing.maximalIdeal (X.O0 i) := by
  intro h
  have h2 := h.map (algebraMap (X.O0 i) (X.O i))
  rw [map_natCast] at h2
  exact X.O_l i h2

theorem l_mem_maxLam (i : X.Tw) (M : ℕ) (ι : Type) : ((X.l i : ℕ) : abelian₂ X i M ι) ∈ maxLam X i M ι := by
  have h := Ideal.mem_map_of_mem (algebraMap (X.O0 i) (abelian₂ X i M ι)) (l_mem_maximalIdeal X i)
  rw [map_natCast] at h
  exact Ideal.mem_sup_left h

theorem maxLam_le (i : X.Tw) (M : ℕ) (ι : Type) [Fintype ι] (m : Ideal (abelian₂ X i M ι)) [hm : m.IsMaximal] :
    maxLam X i M ι ≤ m := by
  classical
  have hp : (X.l i).Prime := (X.lPrime i).out
  have : NeZero (X.l i ^ M) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have h0 : (IsLocalRing.maximalIdeal (X.O0 i)).map (algebraMap (X.O0 i) (abelian₂ X i M ι)) ≤ m := by
    rw [Ideal.map_le_iff_le_comap]
    have : (m.comap (algebraMap (X.O0 i) (abelian₂ X i M ι))).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal m
    exact (IsLocalRing.eq_maximalIdeal this).ge
  refine sup_le h0 ?_
  rw [Ideal.span_le]
  rintro _ ⟨q, rfl⟩
  have hl : ((X.l i : ℕ) : abelian₂ X i M ι) ∈ m := by
    have h := Ideal.mem_map_of_mem (algebraMap (X.O0 i) (abelian₂ X i M ι)) (l_mem_maximalIdeal X i)
    rw [map_natCast] at h
    exact h0 h
  have : Nontrivial (abelian₂ X i M ι ⧸ m) := Ideal.Quotient.nontrivial_iff.2 hm.ne_top
  have : CharP (abelian₂ X i M ι ⧸ m) (X.l i) := by
    refine (CharP.charP_iff_prime_eq_zero hp).2 ?_
    rw [← map_natCast (Ideal.Quotient.mk m)]
    exact Ideal.Quotient.eq_zero_iff_mem.2 hl
  have hg : (Multiplicative.ofAdd (Pi.single q 1) : Del X i M ι) ^ (X.l i ^ M) = 1 := by
    apply Multiplicative.toAdd.injective
    funext j
    simp only [toAdd_pow, toAdd_ofAdd, Pi.smul_apply, toAdd_one, Pi.zero_apply]
    rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  refine hm.isPrime.mem_of_pow_mem (X.l i ^ M) ?_
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_pow]
  simp only [toLam, MvPolynomial.aeval_X, map_sub, map_one]
  rw [sub_pow_char_pow, ← map_pow, ← map_pow]
  rw [one_pow, sub_eq_zero]
  convert map_one (Ideal.Quotient.mk m) using 2
  convert map_one (MonoidAlgebra.of (X.O0 i) (Del X i M ι)) using 2

theorem exists_const (i : X.Tw) (M : ℕ) (ι : Type) [Fintype ι] (x : abelian₂ X i M ι) :
    ∃ c : X.O0 i, x - algebraMap (X.O0 i) (abelian₂ X i M ι) c ∈ maxLam X i M ι := by
  obtain ⟨F, rfl⟩ := toLam_surjective X i M ι x
  induction F using MvPolynomial.induction_on with
  | C a => exact ⟨a, by rw [MvPolynomial.algHom_C, sub_self]; exact zero_mem _⟩
  | add p q hp hq =>
    obtain ⟨a, ha⟩ := hp
    obtain ⟨b, hb⟩ := hq
    refine ⟨a + b, ?_⟩
    have := add_mem ha hb
    rw [map_add, map_add]
    convert this using 1
    ring
  | mul_X p q _ =>
    refine ⟨0, ?_⟩
    rw [map_zero, sub_zero, map_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_sup_right (Ideal.subset_span ⟨q, rfl⟩))

theorem mem_maxLam_iff (i : X.Tw) (M : ℕ) (ι : Type) [Fintype ι] (x : abelian₂ X i M ι) :
    x ∈ maxLam X i M ι ↔ ¬ IsUnit x := by
  refine ⟨fun hx hu => maxLam_ne_top X i M ι (Ideal.eq_top_of_isUnit_mem _ hx hu), fun hx => ?_⟩
  obtain ⟨m, hm, hxm⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.2 hx)
  obtain ⟨c, hc⟩ := exists_const X i M ι x
  have h1 : algebraMap (X.O0 i) (abelian₂ X i M ι) c ∈ m := by
    have := sub_mem hxm (maxLam_le X i M ι m hc)
    rwa [sub_sub_cancel] at this
  have h2 : c ∈ IsLocalRing.maximalIdeal (X.O0 i) := fun hu =>
    hm.ne_top (Ideal.eq_top_of_isUnit_mem _ h1 (hu.map _))
  have h3 : algebraMap (X.O0 i) (abelian₂ X i M ι) c ∈ maxLam X i M ι :=
    Ideal.mem_sup_left (Ideal.mem_map_of_mem _ h2)
  have := add_mem hc h3
  rwa [sub_add_cancel] at this

theorem maxLam_isMaximal (i : X.Tw) (M : ℕ) (ι : Type) [Fintype ι] : (maxLam X i M ι).IsMaximal := by
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ (maxLam_ne_top X i M ι)
  have : maxLam X i M ι = m := le_antisymm hle fun x hx =>
    (mem_maxLam_iff X i M ι x).2 fun hu => hm.ne_top (Ideal.eq_top_of_isUnit_mem _ hx hu)
  rwa [this]

theorem length_resLam (i : X.Tw) (M : ℕ) (ι : Type) [Fintype ι] :
    Module.length (abelian₂ X i M ι) (ResLam X i M ι) = 1 := by
  have : IsSimpleModule (abelian₂ X i M ι) (abelian₂ X i M ι ⧸ maxLam X i M ι) :=
    isSimpleModule_iff_isCoatom.2 (maxLam_isMaximal X i M ι).out
  exact Module.length_eq_one (abelian₂ X i M ι) (abelian₂ X i M ι ⧸ maxLam X i M ι)

theorem smul_resLam (i : X.Tw) (M : ℕ) (ι : Type) (x : abelian₂ X i M ι) (hx : x ∈ maxLam X i M ι) (b : ResLam X i M ι) :
    x • b = 0 := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective (maxLam X i M ι) b
  exact (Submodule.Quotient.mk_eq_zero _).2 (Ideal.mul_mem_right y _ hx)

variable {X} (bkP : BKPh X)

theorem length_sel_of_computes (i : X.Tw) (s : X.Sig i) (M : ℕ) {ι : Type} [Fintype ι]
    (d : ι → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) (Q : Finset (PlE D.host)) (a : ℕ)
    (Φ : Matrix (Fin a) (Fin a) (abelian₂ X i M ι)) (h : Computes bkP i s M d Q Φ) (hΦ : ∀ x y, Φ x y ∈ maxLam X i M ι) :
    Module.length (abelian₂ X i M ι) ↥(selOn bkP i (Tgl i s) (delInv i M d) (ResLam X i M ι) Q) = (a : ℕ∞) := by
  obtain ⟨e, -⟩ := h
  have hB : ∀ b : ResLam X i M ι, ∃ n : ℕ, (X.l i ^ n) • b = 0 := fun b =>
    ⟨1, by rw [pow_one, ← Nat.cast_smul_eq_nsmul (abelian₂ X i M ι)]; exact smul_resLam X i M ι _ (l_mem_maxLam X i M ι) b⟩
  have hk : LinearMap.ker (matAct (M := ResLam X i M ι) Φ) = ⊤ := by
    rw [eq_top_iff]
    intro v _
    rw [LinearMap.mem_ker]
    funext x
    change ∑ y, Φ x y • v y = 0
    exact Finset.sum_eq_zero fun y _ => smul_resLam X i M ι _ (hΦ x y) (v y)
  rw [← (e (ResLam X i M ι) hB).length_eq, (LinearEquiv.ofTop _ hk).length_eq, Module.length_pi_of_fintype]
  simp [length_resLam]

theorem isSelMatrix_iff (i : X.Tw) (s : X.Sig i) (M : ℕ) {ι : Type} [Fintype ι]
    (d : ι → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) (Q : Finset (PlE D.host)) (a : ℕ)
    (Φ : Matrix (Fin a) (Fin a) (abelian₂ X i M ι)) :
    IsSelMatrix bkP i s M d Q a Φ ↔ Computes bkP i s M d Q Φ ∧ ∀ b c, ¬ IsUnit (Φ b c) :=
  ⟨fun h => ⟨h.1, fun b c => (mem_maxLam_iff X i M ι _).1 (h.2.2 b c)⟩, fun h =>
    have h2 : ∀ b c, Φ b c ∈ maxLam X i M ι := fun b c => (mem_maxLam_iff X i M ι _).2 (h.2 b c)
    ⟨h.1, length_sel_of_computes bkP i s M d Q a Φ h.1 h2, h2⟩⟩

theorem galHyp_iff (i : X.Tw) (s : X.Sig i) :
    GalHyp bkP i s ↔ TripleHyp bkP i s ∧ True ∧ 100 ≤ D.R.r :=
  ⟨fun h => ⟨⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.2.1, le_trans (by norm_num) h.2.2.2.2.2.2⟩,
      h.2.2.2.2.1, h.2.2.2.2.2.2⟩,
    fun h => ⟨h.1.1, h.1.2.1, h.1.2.2.1, h.1.2.2.2.1, h.2.1, h.1.2.2.2.2.1, h.2.2⟩⟩

theorem selmer_iff_selmer_matrix_at_primes : ThmS bkP ↔ SelmerMatrixChosenPrimes bkP := by
  constructor
  · intro h i s hG M hM A ι _ P d Q hA hQ
    obtain ⟨a, Φ, hΦ⟩ := h i s hG M ι P d Q hM hA.empty hQ
    exact ⟨a, Φ, (isSelMatrix_iff bkP i s M d Q a Φ).2 hΦ⟩
  · intro h i s hG M ι _ P d Q hM hA hQ
    obtain ⟨a, Φ, hΦ⟩ := h i s hG M hM ∅ ι P d Q hA hQ
    exact ⟨a, Φ, (isSelMatrix_iff bkP i s M d Q a Φ).1 hΦ⟩

theorem selMatrix_iff : SelMatrix bkP ↔
    ∀ (i : X.Tw) (s : X.Sig i), TripleHyp bkP i s → ∀ (M : ℕ) (ι : Type) [Fintype ι] (P : ι → PlE D.host) d
      (Q : Finset (PlE D.host)), HidaSetting X i M P Q d →
      ∃ (a : ℕ) (Φ : Matrix (Fin a) (Fin a) (abelian₂ X i M ι)), Computes bkP i s M d Q Φ ∧ ∀ b c, ¬ IsUnit (Φ b c) := by
  constructor
  · intro h i s hG M ι _ P d Q hS
    obtain ⟨a, Φ, hΦ⟩ := h i s hG M ι P Q d hS
    exact ⟨a, Φ, (isSelMatrix_iff bkP i s M d Q a Φ).1 hΦ⟩
  · intro h i s hG M ι _ P Q d hS
    obtain ⟨a, Φ, hΦ⟩ := h i s hG M ι P d Q hS
    exact ⟨a, Φ, (isSelMatrix_iff bkP i s M d Q a Φ).2 hΦ⟩

theorem thmS_of_selMatrix (h : SelMatrix bkP) : ThmS bkP :=
  (selmer_iff_selmer_matrix_at_primes bkP).2 (selmerMatrixAuxiliaryPrimes_of_selMatrix bkP h)

theorem compare : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X),
    (ThmS bkP ↔ SelmerMatrixChosenPrimes bkP) ∧ (SelMatrix bkP → ThmS bkP) ∧
      ∀ (i : X.Tw) (s : X.Sig i) (M : ℕ) (ι : Type) [Fintype ι] (d : ι → (GE N →* Multiplicative (ZMod (X.l i ^ M))))
        (Q : Finset (PlE D.host)) (a : ℕ) (Φ : Matrix (Fin a) (Fin a) (abelian₂ X i M ι)),
        IsSelMatrix bkP i s M d Q a Φ ↔ Computes bkP i s M d Q Φ ∧ ∀ b c, ¬ IsUnit (Φ b c) :=
  fun _ _ _ bkP => ⟨selmer_iff_selmer_matrix_at_primes bkP, thmS_of_selMatrix bkP,
    fun i s M _ _ d Q a Φ => isSelMatrix_iff bkP i s M d Q a Φ⟩

end GlobalTheory.SelMatrixCompare

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SmallTracesDvdSpanImage
section
open Formalism.MainNotions.N GlobalTheory.Cong GlobalTheory.PsChar

namespace GlobalTheory.SmallTrace

theorem exists_ball_sub_image {l : ℕ} [Fact l.Prime] {ι F : Type} [Fintype ι]
    [NormedAddCommGroup F] [NormedSpace ℚ_[l] F] (S : (ι → ℚ_[l]) →ₗ[ℚ_[l]] F) :
    ∃ ε > 0, ∀ w ∈ LinearMap.range S, ‖w‖ < ε → ∃ x : ι → ℚ_[l], ‖x‖ < 1 ∧ S x = w := by
  have hS' : Function.Surjective S.rangeRestrict := LinearMap.surjective_rangeRestrict S
  have ho : IsOpenMap S.rangeRestrict := LinearMap.isOpenMap_of_finiteDimensional _ hS'
  have hU : IsOpen (S.rangeRestrict '' Metric.ball 0 1) := ho _ Metric.isOpen_ball
  have h0 : (0 : LinearMap.range S) ∈ S.rangeRestrict '' Metric.ball 0 1 := ⟨0, by simp, by simp⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU 0 h0
  refine ⟨ε, hε, fun w hw hwε => ?_⟩
  have hmem : (⟨w, hw⟩ : LinearMap.range S) ∈ Metric.ball 0 ε := by
    rw [Metric.mem_ball, dist_zero_right]; exact hwε
  obtain ⟨x, hx, hxw⟩ := hball hmem
  refine ⟨x, by simpa using hx, ?_⟩
  have := congrArg Subtype.val hxw
  simpa using this

variable {l : ℕ} [Fact l.Prime] {Γ : Type} [Group Γ] {a : ℕ}

noncomputable def matOf (r : Γ →* GL (Fin a) (PadicAlgCl l)) (f : Γ →₀ ℤ_[l]) :
    Matrix (Fin a) (Fin a) (PadicAlgCl l) :=
  f.sum fun h c => ((algebraMap ℚ_[l] (PadicAlgCl l)) (c : ℚ_[l])) •
    ((r h : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l))

theorem matOf_eq_lc (r : Γ →* GL (Fin a) (PadicAlgCl l)) (t : Finset Γ) (f : Γ →₀ ℤ_[l])
    (hf : f.support ⊆ t) :
    matOf r f = Fintype.linearCombination ℚ_[l]
      (fun i : t => ((r i : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l)))
      (fun i => (f i : ℚ_[l])) := by
  rw [Fintype.linearCombination_apply, matOf, Finsupp.sum_of_support_subset f hf _ (by simp)]
  rw [← Finset.sum_coe_sort t]
  simp [algebraMap_smul]

theorem exists_matOf_eq (r : Γ →* GL (Fin a) (PadicAlgCl l)) (t : Finset Γ) (y : t → ℤ_[l]) :
    ∃ f' : Γ →₀ ℤ_[l], matOf r f' = Fintype.linearCombination ℚ_[l]
      (fun i : t => ((r i : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l)))
      (fun i => (y i : ℚ_[l])) := by
  classical
  let f' : Γ →₀ ℤ_[l] := Finsupp.onFinset t (fun g => if h : g ∈ t then y ⟨g, h⟩ else 0)
    (by intro g hg; by_contra h; simp [h] at hg)
  refine ⟨f', ?_⟩
  rw [matOf_eq_lc r t f' (Finsupp.support_onFinset_subset)]
  congr 1
  funext i
  simp [f', Finsupp.onFinset_apply, i.2]

end GlobalTheory.SmallTrace

namespace GlobalTheory.SmallTrace
variable {l : ℕ} [Fact l.Prime] {Γ : Type} [Group Γ] {a : ℕ}

theorem matOf_single (r : Γ →* GL (Fin a) (PadicAlgCl l)) (g : Γ) :
    matOf r (Finsupp.single g 1) =
      ((r g : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l)) := by
  rw [matOf, Finsupp.sum_single_index (by simp)]
  simp

theorem matOf_mem_span (r : Γ →* GL (Fin a) (PadicAlgCl l)) (f : Γ →₀ ℤ_[l]) :
    matOf r f ∈ Submodule.span (PadicAlgCl l) (Set.range fun g =>
      ((r g : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l))) := by
  rw [matOf]
  exact Submodule.sum_mem _ fun h _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨h, rfl⟩)

theorem trace_zero_of_finset (r : Γ →* GL (Fin a) (PadicAlgCl l)) (t : Finset Γ)
    (ht : ∀ f : Γ →₀ ℤ_[l], ∃ f' : Γ →₀ ℤ_[l], f'.support ⊆ t ∧ matOf r f = matOf r f')
    (D : Matrix (Fin a) (Fin a) (PadicAlgCl l))
    (hD : ∀ i : t, (D * ((r i : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l))).trace = 0)
    (g : Γ) : (D * ((r g : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l))).trace = 0 := by
  obtain ⟨f', hf't, hf'⟩ := ht (Finsupp.single g 1)
  rw [matOf_single, matOf_eq_lc r t f' hf't, Fintype.linearCombination_apply] at hf'
  rw [hf', Matrix.mul_sum, Matrix.trace_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Matrix.mul_smul, Matrix.trace_smul, hD i, smul_zero]

end GlobalTheory.SmallTrace

namespace GlobalTheory.SmallTrace
variable {l : ℕ} [Fact l.Prime] {Γ : Type} [Group Γ] {a : ℕ}

theorem finiteRing_sq_sub_mul_sq_eq_of_card [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    (r : Γ →* GL (Fin a) (PadicAlgCl l)) (hr : Continuous r) (hss : IsSSRep r) :
    ∃ c : ℕ, ∀ (n : ℕ) (f : Γ →₀ ℤ_[l]),
      (∀ g, ‖(matOf r f * ((r g : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l))).trace‖
        ≤ ((l : ℝ)⁻¹) ^ (n + c)) →
      ∃ f' : Γ →₀ ℤ_[l], matOf r f = ((l : PadicAlgCl l) ^ n) • matOf r f' := by
  obtain ⟨t, ht⟩ := GlobalTheory.T.zlSpan_image_continuous_rep_finite l Γ a r hr
  have ht' : ∀ f : Γ →₀ ℤ_[l], ∃ f' : Γ →₀ ℤ_[l], f'.support ⊆ t ∧ matOf r f = matOf r f' := ht
  let v : t → Matrix (Fin a) (Fin a) (PadicAlgCl l) := fun i =>
    ((r i : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l))
  let Φ : Matrix (Fin a) (Fin a) (PadicAlgCl l) →ₗ[ℚ_[l]] (t → PadicAlgCl l) :=
    { toFun := fun M i => (M * v i).trace
      map_add' := by intro M N; funext i; simp [Matrix.add_mul, Matrix.trace_add]
      map_smul' := by intro c M; funext i; simp [Matrix.smul_mul, Matrix.trace_smul] }
  let S : (t → ℚ_[l]) →ₗ[ℚ_[l]] (t → PadicAlgCl l) := Φ ∘ₗ Fintype.linearCombination ℚ_[l] v
  obtain ⟨ε, hε, hball⟩ := exists_ball_sub_image S
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  obtain ⟨c, hc⟩ : ∃ c : ℕ, ((l : ℝ)⁻¹) ^ c < ε :=
    exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ hl1)
  refine ⟨c, fun n f hf => ?_⟩
  obtain ⟨f0, hf0t, hf0⟩ := ht' f
  set x0 : t → ℚ_[l] := fun i => (f0 i : ℚ_[l]) with hx0
  have hMf : matOf r f = Fintype.linearCombination ℚ_[l] v x0 := by
    rw [hf0]; exact matOf_eq_lc r t f0 hf0t
  have hΦf : ‖Φ (matOf r f)‖ ≤ ((l : ℝ)⁻¹) ^ (n + c) :=
    (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => hf i
  set q : ℚ_[l] := ((l : ℚ_[l]) ^ n)⁻¹ with hq
  have hlQ : (l : ℚ_[l]) ^ n ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : l.Prime).ne_zero)
  have hqn : ‖q‖ = (l : ℝ) ^ n := by
    rw [hq, norm_inv, norm_pow, Padic.norm_p, inv_pow, inv_inv]
  set w : t → PadicAlgCl l := q • Φ (matOf r f) with hw
  have hwS : w = S (q • x0) := by
    rw [hw, map_smul, hMf]; rfl
  have hwε : ‖w‖ < ε := by
    rw [hw, norm_smul, hqn]
    calc (l : ℝ) ^ n * ‖Φ (matOf r f)‖ ≤ (l : ℝ) ^ n * ((l : ℝ)⁻¹) ^ (n + c) :=
          mul_le_mul_of_nonneg_left hΦf (by positivity)
      _ = ((l : ℝ)⁻¹) ^ c := by
          rw [pow_add, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hl0.ne', one_pow, one_mul]
      _ < ε := hc
  obtain ⟨y, hy1, hy⟩ := hball w ⟨_, hwS.symm⟩ hwε
  have hyi : ∀ i, ‖y i‖ ≤ 1 := fun i => (norm_le_pi_norm y i).trans hy1.le
  let yz : t → ℤ_[l] := fun i => ⟨y i, hyi i⟩
  obtain ⟨f', hf'⟩ := exists_matOf_eq r t yz
  refine ⟨f', ?_⟩
  have hlK : ((l : PadicAlgCl l) ^ n) = algebraMap ℚ_[l] (PadicAlgCl l) ((l : ℚ_[l]) ^ n) := by simp
  rw [← sub_eq_zero]
  apply GlobalTheory.T.eq_zero_of_trace_mul_eq_zero_semisimple_rep (PadicAlgCl l) Γ a r hss
  · exact Submodule.sub_mem _ (matOf_mem_span r f)
      (Submodule.smul_mem _ _ (matOf_mem_span r f'))
  · apply trace_zero_of_finset r t ht'
    intro i
    have hy' : Fintype.linearCombination ℚ_[l] v (fun i => (yz i : ℚ_[l])) = Fintype.linearCombination ℚ_[l] v y := rfl
    have key : Φ (matOf r f - ((l : PadicAlgCl l) ^ n) • matOf r f') = 0 := by
      rw [hf', hy', hlK, algebraMap_smul, map_sub, map_smul]
      have : Φ (Fintype.linearCombination ℚ_[l] v y) = w := hy
      rw [this, hw, smul_smul, hq, mul_inv_cancel₀ hlQ, one_smul, sub_self]
    exact congrFun key i

end GlobalTheory.SmallTrace

theorem GlobalTheory.smallTrace_dvd_span : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (a : ℕ) (r : Γ →* GL (Fin a) (PadicAlgCl l)), Continuous r → IsSSRep r → ∃ c : ℕ, ∀ (n : ℕ) (f : Γ →₀ ℤ_[l]), (∀ g, ‖((f.sum fun h c => ((algebraMap ℚ_[l] (PadicAlgCl l)) (c : ℚ_[l])) • ((r h : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l))) * ((r g : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l))).trace‖ ≤ ((l : ℝ)⁻¹) ^ (n + c)) → ∃ f' : Γ →₀ ℤ_[l], (f.sum fun h c => ((algebraMap ℚ_[l] (PadicAlgCl l)) (c : ℚ_[l])) • ((r h : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l))) = ((l : PadicAlgCl l) ^ n) • (f'.sum fun h c => ((algebraMap ℚ_[l] (PadicAlgCl l)) (c : ℚ_[l])) • ((r h : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l))) := by
  intro l _ Γ _ _ _ _ a r hr hss
  exact GlobalTheory.SmallTrace.finiteRing_sq_sub_mul_sq_eq_of_card r hr hss
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltInvariantApproxByEpsilonRootsClosure
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.FlatInvariants

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P)

theorem root_pow (j : ℕ) : AI.εroot j ^ l ^ j = AI.ε := by
  induction j with
  | zero => simp [LocAinf.εroot]
  | succ j ih =>
    rw [pow_succ', pow_mul, LocAinf.εroot, Function.iterate_succ_apply', frobeniusEquiv_symm_pow_p]
    exact ih

theorem root_sub_dvd (j : ℕ) : AI.εroot j - 1 ∣ AI.ε - 1 := by
  rw [← root_pow AI j]
  exact sub_one_dvd_pow_sub_one _ _

theorem exists_pow_mul_integral (s : ℕ) (y : Cb l) : ∃ k, ∀ k' ≥ k, ∃ z : OCb l,
    algebraMap (OCb l) (Cb l) ((AI.εroot s - 1) ^ k') * y = algebraMap (OCb l) (Cb l) z := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := OCb l) y
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨k, hk⟩ : ∃ k, b ∣ (AI.εroot s - 1) ^ k := by
    by_contra h
    exact hb0 ((GlobalTheory.TiltComplete.tilt_separated_complete l P AI s).1 b fun m =>
      (ValuationRing.dvd_total _ _).resolve_right fun h' => h ⟨m, h'⟩)
  refine ⟨k, fun k' hk' => ?_⟩
  obtain ⟨d, hd⟩ := hk.trans (pow_dvd_pow _ hk')
  have : algebraMap (OCb l) (Cb l) b ≠ 0 := fun h =>
    hb0 (IsFractionRing.injective (OCb l) (Cb l) (h.trans (map_zero _).symm))
  refine ⟨d * a, ?_⟩
  rw [hd, map_mul, map_mul]
  field_simp

theorem flat_invariant_approx : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (w : Cb l), (∀ g ∈ Hinf K, autCb l (AI.actT g) w = w) → ∀ m : ℕ, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∃ u ∈ Subring.closure (Set.range AI.εroot ∪ {xb | ∃ c : Om l, c ∈ K0 K ∧ ∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧ c ^ m = 1 ∧ IsTiltOf c m xb}), ∃ v : OCb l, algebraMap (OCb l) (Cb l) ((AI.εroot s - 1) ^ N) * w = algebraMap (OCb l) (Cb l) (u + (AI.εroot s - 1) ^ (N + m) * v) := by
  intro l _ P AI K s w hw m
  obtain ⟨k, hk⟩ := exists_pow_mul_integral AI s w
  refine ⟨k, fun N hN => ?_⟩
  obtain ⟨z, hz⟩ := hk N hN
  have hfix : ∀ g ∈ Hinf K, AI.actT g z = z := fun g hg => by
    apply IsFractionRing.injective (OCb l) (Cb l)
    rw [← autCb_alg, ← hz, map_mul, hw g hg, autCb_alg, map_pow (AI.actT g), map_sub (AI.actT g), map_one (AI.actT g),
      (GlobalTheory.T.cyclotomicTower_fixes_epsilonRoots_resGamma_trivial l P AI K).1 g hg s]
  obtain ⟨u, hu, hd⟩ := GlobalTheory.TiltInvariants.invariant_approx l P AI K z hfix (N + m)
  obtain ⟨v, hv⟩ := (pow_dvd_pow_of_dvd (root_sub_dvd AI s) (N + m)).trans hd
  exact ⟨u, hu, v, by rw [hz, ← hv, add_sub_cancel]⟩

end GlobalTheory.FlatInvariants
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltUntiltToComplexPAdicBasicLaws
section
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSer.Laws

variable (l : ℕ) [Fact l.Prime]

theorem untilt_zero : (0 : Fl l).untilt = 0 :=
  Perfection.teichmuller_zero

theorem sh_laws : ∀ (l : ℕ) [Fact l.Prime], sh (1 : Fl l) = 1 ∧ sh (0 : Fl l) = 0 ∧
    (∀ x y : Fl l, sh (x * y) = sh x * sh y) ∧ (∀ (x : Fl l) (n : ℕ), sh (x ^ n) = sh x ^ n) ∧
    (∀ x : Fl l, ‖sh x‖ ≤ 1) ∧ (∀ c : ℂ_[l], ‖c‖ ≤ 1 → ∃ x : Fl l, sh x = c) ∧
    (∀ x y : Fl l, ‖sh (x + y) - sh x - sh y‖ ≤ ‖(l : ℂ_[l])‖) ∧ (∀ x : Fl l, ‖sh (-x)‖ = ‖sh x‖) := by
  intro l _
  have hmul : ∀ x y : Fl l, sh (x * y) = sh x * sh y := fun x y => by
    simp only [sh, map_mul]; rfl
  have hpow : ∀ (x : Fl l) (n : ℕ), sh (x ^ n) = sh x ^ n := fun x n => by
    simp only [sh, map_pow]; norm_cast
  refine ⟨by simp [sh], by simp [sh, untilt_zero], hmul, hpow, fun x => (GlobalTheory.RingBasics.mem_OC _).1 (x.untilt).2,
    fun c hc => ?_, fun x y => ?_, fun x => ?_⟩
  · obtain ⟨x, hx⟩ := GlobalTheory.MemLoc.FundOnto.untilt_surjective l ⟨c, (GlobalTheory.RingBasics.mem_OC c).2 hc⟩
    exact ⟨x, by simp [sh, hx]⟩
  · have hm : (x + y).untilt - x.untilt - y.untilt ∈ Ideal.span {(l : OC l)} := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_sub, PreTilt.mk_untilt_eq_coeff_zero,
        PreTilt.mk_untilt_eq_coeff_zero, PreTilt.mk_untilt_eq_coeff_zero, map_add]
      ring
    have := (GlobalTheory.RingBasics.mem_span_pow_OC 1 _).1 (by rw [pow_one]; exact hm)
    simpa [sh] using this
  · have h2 : sh (-x) ^ 2 = sh x ^ 2 := by rw [← hpow, ← hpow, neg_sq]
    have h3 : ‖sh (-x)‖ ^ 2 = ‖sh x‖ ^ 2 := by rw [← norm_pow, ← norm_pow, h2]
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h3

end GlobalTheory.PSer.Laws
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TmPowDvd
section
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSer

theorem tm_pow_dvd : ∀ (l : ℕ) [Fact l.Prime] (x : Fl l), ‖sh x‖ ≤ ‖(l : ℂ_[l])‖ →
    (l : Acris l) ∣ algebraMap (Ainf l) (Acris l) (tm x) ^ l := by
  intro l _ x hx
  have hmem : x.untilt ∈ (Ideal.span {(l : OC l)}) ^ 1 := by
    rw [GlobalTheory.RingBasics.mem_span_pow_OC, pow_one]
    exact hx
  rw [pow_one] at hmem
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hmem
  obtain ⟨z, hz⟩ := GlobalTheory.MemLoc.FundOnto.untilt_surjective l c
  have hk := GlobalTheory.MemLoc.FundOnto.dvd_pow_of_ker l (tm x - (l : Ainf l) * tm z) (by
    rw [map_sub, map_mul, map_natCast, GlobalTheory.MemLoc.FundOnto.theta_tm,
      GlobalTheory.MemLoc.FundOnto.theta_tm, hz, ← hc, mul_comm, sub_self])
  rw [map_sub, map_mul, map_natCast] at hk
  generalize algebraMap (Ainf l) (Acris l) (tm x) = X at hk ⊢
  generalize algebraMap (Ainf l) (Acris l) (tm z) = Z at hk
  have h1 : ((l : ℕ) : Acris l) ∣ X - (X - (l : Acris l) * Z) := ⟨Z, by ring⟩
  have h2 := h1.trans (sub_dvd_pow_sub_pow _ _ l)
  have := dvd_add h2 hk
  simpa using this

end GlobalTheory.PSer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwoCocycleMemCoboundariesOfModUniformizerPowStatement
section
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.LocDualInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twoCocycle_mem_coboundaries_of_mod_uniformizer_pow : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O] {G : Type} [Group G] [TopologicalSpace G] (ε : G →* Oˣ) (ϖ : O), (∀ n : ℕ, IsOpen ((powSub (M := O) ϖ n : Submodule O O) : Set O)) → (∀ U ∈ nhds (0 : O), ∃ n : ℕ, ((powSub (M := O) ϖ n : Submodule O O) : Set O) ⊆ U) → (∀ n : ℕ, (Z1 (quotRep (twist ε O) ϖ n) : Set (G → O ⧸ powSub (M := O) ϖ n)).Finite) → ∀ (w : G × G → O), w ∈ Z2 (twist ε O) → (∀ n : ℕ, ∃ b : G → O ⧸ powSub (M := O) ϖ n, Continuous b ∧ ∀ g h : G, d1 (quotRep (twist ε O) ϖ n) b (g, h) = Submodule.Quotient.mk (w (g, h))) → w ∈ B2 (twist ε O) := by
  first | exact @GlobalTheory.PadicH2SeparatedDVR.separated_dvr_second_cohomology_mem | exact GlobalTheory.PadicH2SeparatedDVR.separated_dvr_second_cohomology_mem | (intros; apply GlobalTheory.PadicH2SeparatedDVR.separated_dvr_second_cohomology_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachFunctorFullyFaithfulStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachFunctor_fullyFaithful : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ (T T' : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (f : W.DD T →ₗ[W.EE] W.DD T'), (∀ x, f (W.φD T x) = W.φD T' (f x)) → (∀ g x, f (W.γD T g x) = W.γD T' g (f x)) → ∃! F : LatHom T.L T'.L, ∀ x, W.map F x = f x := by
  first | exact @GlobalTheory.FontaineFullyFaithful.main | exact GlobalTheory.FontaineFullyFaithful.main | (intros; apply GlobalTheory.FontaineFullyFaithful.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachHypothesisCrystallineLatticesStatement
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachHypothesis_crystallineLattices : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), DeltaInvariantLattices.UsedLocalConclusion D HW F Cm → DeltaInvariantLattices.ConclusionE D HW F → CrysOnCond D HW F → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), EmbeddingTypeJumps.WachHypothesisLocal (LocalSituation.sit D.loc HW l (D.locA l) K s LL h) ((F l).E K s LL h).tie := by
  first | exact @GlobalTheory.WachHyp.hypW_crystalline | exact GlobalTheory.WachHyp.hypW_crystalline | (intros; apply GlobalTheory.WachHyp.hypW_crystalline <;> assumption)
end

