import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0518
import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocE
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitOfClosure
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0252
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0006
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0495
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousAlgebraMapPadicInt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0358
import Development.AutomorphicArithmetic.CyclotomicBounds.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0502
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisPrescribedUnramifiedKummer
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0008
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0481
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0503
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0504
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0480

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsStableComplActK
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual GlobalTheory.Pass.LocDual.OneX

namespace GlobalTheory.BlockSum

section General

variable {K : Type} [Field K] {Γ : Type}

def StableUnder {V : Type} [AddCommGroup V] [Module K V] (f : Γ → V →ₗ[K] V)
    (S : Submodule K V) : Prop :=
  ∀ γ, ∀ v ∈ S, f γ v ∈ S

def HasRelCompl {V : Type} [AddCommGroup V] [Module K V] (f : Γ → V →ₗ[K] V)
    (Y : Submodule K V) : Prop :=
  ∀ W : Submodule K V, StableUnder f W → W ≤ Y →
    ∃ C : Submodule K V, StableUnder f C ∧ C ≤ Y ∧ W ⊓ C = ⊥ ∧ W ⊔ C = Y

variable {V : Type} [AddCommGroup V] [Module K V] {f : Γ → V →ₗ[K] V}

theorem hasRelCompl_sup {X U : Submodule K V} (hXs : StableUnder f X) (hUs : StableUnder f U)
    (hX : HasRelCompl f X) (hU : HasRelCompl f U) : HasRelCompl f (X ⊔ U) := by
  first
  | exact @_root_.GlobalTheory.ComplementedSup.complemented_sup
  | exact _root_.GlobalTheory.ComplementedSup.complemented_sup
  | (apply _root_.GlobalTheory.ComplementedSup.complemented_sup <;> assumption)
  | (intros; apply _root_.GlobalTheory.ComplementedSup.complemented_sup <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ComplementedSup.complemented_sup <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ComplementedSup.complemented_sup ..)

end General

section Blocks

variable {K : Type} [Field K] {Γ : Type} {ι : Type} [DecidableEq ι]
  {n : Type} [Fintype n] [DecidableEq n]

def blockAct (ρ : Γ → ι → Matrix n n K) (γ : Γ) : (ι → n → K) →ₗ[K] (ι → n → K) :=
  LinearMap.pi (fun b => (Matrix.mulVecLin (ρ γ b)).comp (LinearMap.proj b))

theorem blockAct_apply (ρ : Γ → ι → Matrix n n K) (γ : Γ) (v : ι → n → K) (b : ι) :
    blockAct ρ γ v b = (ρ γ b).mulVec (v b) := rfl

def blockSub (s : Set ι) : Submodule K (ι → n → K) where
  carrier := {v | ∀ b, b ∉ s → v b = 0}
  add_mem' := by
    intro v w hv hw b hb
    simp [hv b hb, hw b hb]
  zero_mem' := by
    intro b _
    rfl
  smul_mem' := by
    intro c v hv b hb
    simp [hv b hb]

theorem blockSub_stable (ρ : Γ → ι → Matrix n n K) (s : Set ι) :
    StableUnder (blockAct ρ) (blockSub s : Submodule K (ι → n → K)) := by
  intro γ v hv b hb
  rw [blockAct_apply, hv b hb, Matrix.mulVec_zero]

theorem blockSub_mono {s t : Set ι} (h : s ⊆ t) :
    (blockSub s : Submodule K (ι → n → K)) ≤ blockSub t :=
  fun _ hv b hb => hv b (fun hs => hb (h hs))

theorem blockSub_empty : (blockSub (∅ : Set ι) : Submodule K (ι → n → K)) = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  rw [Submodule.mem_bot]
  funext b
  exact hv b (Set.notMem_empty b)

theorem blockSub_univ : (blockSub (Set.univ : Set ι) : Submodule K (ι → n → K)) = ⊤ := by
  rw [eq_top_iff]
  intro v _ b hb
  exact absurd (Set.mem_univ b) hb

theorem blockSub_insert (b : ι) (s : Set ι) :
    (blockSub (insert b s) : Submodule K (ι → n → K)) = blockSub s ⊔ blockSub {b} := by
  apply le_antisymm
  · intro v hv
    refine Submodule.mem_sup.mpr ⟨Function.update v b 0, ?_, Pi.single b (v b), ?_, ?_⟩
    · intro c hc
      by_cases h : c = b
      · subst h; simp
      · rw [Function.update_of_ne h]
        exact hv c (by simp [h, hc])
    · intro c hc
      have h : c ≠ b := by simpa using hc
      simp [h]
    · funext c
      by_cases h : c = b
      · subst h; simp
      · simp [h]
  · exact sup_le (blockSub_mono (Set.subset_insert _ _))
      (blockSub_mono (Set.singleton_subset_iff.mpr (Set.mem_insert _ _)))

def BlockHasCompl (ρ : Γ → ι → Matrix n n K) (b : ι) : Prop :=
  ∀ S : Submodule K (n → K), (∀ γ, ∀ y ∈ S, (ρ γ b).mulVec y ∈ S) →
    ∃ D : Submodule K (n → K), (∀ γ, ∀ y ∈ D, (ρ γ b).mulVec y ∈ D) ∧ IsCompl S D

theorem hasRelCompl_single (ρ : Γ → ι → Matrix n n K) (b : ι) (hb : BlockHasCompl ρ b) :
    HasRelCompl (blockAct ρ) (blockSub ({b} : Set ι) : Submodule K (ι → n → K)) := by
  intro W hW hWY
  obtain ⟨D', hD's, hc⟩ := hb (W.map (LinearMap.proj b)) (by
    rintro γ _ ⟨v, hv, rfl⟩
    exact ⟨blockAct ρ γ v, hW γ v hv, rfl⟩)
  have hDle : D'.map (LinearMap.single K (fun _ : ι => n → K) b) ≤ blockSub {b} := by
    rintro _ ⟨y, _, rfl⟩ c hc
    have h : c ≠ b := by simpa using hc
    simp [h]
  refine ⟨D'.map (LinearMap.single K (fun _ : ι => n → K) b), ?_, hDle, ?_, ?_⟩
  · rintro γ _ ⟨y, hy, rfl⟩
    refine ⟨(ρ γ b).mulVec y, hD's γ y hy, ?_⟩
    funext c
    rw [blockAct_apply]
    by_cases h : c = b
    · subst h; simp
    · simp [h]
  · rw [eq_bot_iff]
    intro v hv
    obtain ⟨hvW, hvD⟩ := Submodule.mem_inf.mp hv
    obtain ⟨y, hy, rfl⟩ := hvD
    have hy0 : y = 0 := by
      have hm : y ∈ W.map (LinearMap.proj b) ⊓ D' :=
        Submodule.mem_inf.mpr ⟨⟨_, hvW, by simp⟩, hy⟩
      rw [hc.inf_eq_bot] at hm
      exact (Submodule.mem_bot K).mp hm
    subst hy0
    simp
  · apply le_antisymm (sup_le hWY hDle)
    intro u hu
    have hub : u b ∈ W.map (LinearMap.proj b) ⊔ D' := by
      rw [hc.sup_eq_top]; trivial
    obtain ⟨s', ⟨v, hv, rfl⟩, d', hd', hsum⟩ := Submodule.mem_sup.mp hub
    refine Submodule.mem_sup.mpr ⟨v, hv, Pi.single b d', ⟨d', hd', by simp⟩, ?_⟩
    funext c
    by_cases h : c = b
    · subst h
      simpa using hsum
    · have h1 : u c = 0 := hu c (by simpa using h)
      have h2 : v c = 0 := hWY hv c (by simpa using h)
      simp [h, h1, h2]

theorem hasRelCompl_finset (ρ : Γ → ι → Matrix n n K) (hblk : ∀ b, BlockHasCompl ρ b)
    (s : Finset ι) :
    HasRelCompl (blockAct ρ) (blockSub (s : Set ι) : Submodule K (ι → n → K)) := by
  refine Finset.induction_on s ?_ ?_
  · intro W _ hWY
    rw [Finset.coe_empty, blockSub_empty] at hWY ⊢
    refine ⟨⊥, fun γ v hv => ?_, le_rfl, inf_bot_eq _, ?_⟩
    · rw [(Submodule.mem_bot K).mp hv, map_zero]; exact Submodule.zero_mem _
    · rw [sup_bot_eq]; exact le_antisymm hWY bot_le
  · intro b s _ ih
    rw [Finset.coe_insert, blockSub_insert]
    exact hasRelCompl_sup (blockSub_stable ρ _) (blockSub_stable ρ _) ih
      (hasRelCompl_single ρ b (hblk b))

theorem exists_stable_compl [Fintype ι] (ρ : Γ → ι → Matrix n n K)
    (hblk : ∀ b, BlockHasCompl ρ b) (W : Submodule K (ι → n → K))
    (hW : StableUnder (blockAct ρ) W) :
    ∃ C : Submodule K (ι → n → K), StableUnder (blockAct ρ) C ∧ IsCompl W C := by
  have h := hasRelCompl_finset ρ hblk Finset.univ W hW
    (by rw [Finset.coe_univ, blockSub_univ]; exact le_top)
  rw [Finset.coe_univ, blockSub_univ] at h
  obtain ⟨C, hCs, _, h1, h2⟩ := h
  exact ⟨C, hCs, ⟨disjoint_iff.mpr h1, codisjoint_iff.mpr h2⟩⟩

end Blocks

end GlobalTheory.BlockSum

namespace GlobalTheory.BlockSum

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem exists_stable_compl_actK : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (Xs : Set (D.nd.X i)), GoodR D.nd i r → ∀ {a : ℕ} (x : Fin a → ↥Xs)
    (W : Submodule (KK D.nd i) (Fin a → Fin D.R.nV → KK D.nd i)),
    (∀ γ : GE D.nd, ∀ v ∈ W, actK i r Xs x γ v ∈ W) →
    ∃ C : Submodule (KK D.nd i) (Fin a → Fin D.R.nV → KK D.nd i),
    (∀ γ : GE D.nd, ∀ v ∈ C, actK i r Xs x γ v ∈ C) ∧ IsCompl W C := by
  intro D i r Xs hG a x W hW
  let ρ : GE D.nd → Fin a → Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i) :=
    fun γ b => (mapM (toK D.nd i) (rTwO D.nd i r ↑(x b))) γ
  have hact : ∀ γ v, actK i r Xs x γ v = blockAct ρ γ v := fun γ v => rfl
  have hblk : ∀ b, BlockHasCompl ρ b := by
    intro b
    have hss := (hG ↑(x b)).2.1
    set c : GE D.nd → KK D.nd i :=
      fun γ => toK D.nd i ((((chiU D.nd i 1)⁻¹ γ : (D.nd.O i)ˣ)) : D.nd.O i) with hcdef
    have hrel : ∀ γ, ρ γ b = c γ • (↑(mapRep (algebraMap (D.nd.O i) (Kf D.nd i)) (r ↑(x b)) γ) :
        Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) := by
      intro γ
      ext j k
      simp [ρ, c, mapM, rTwO, twistM, mapRep, rO]
    have hc0 : ∀ γ, c γ ≠ 0 := fun γ =>
      ((((chiU D.nd i 1)⁻¹ γ : (D.nd.O i)ˣ)).isUnit.map (toK D.nd i)).ne_zero
    intro S hS
    obtain ⟨D', hD', hcompl⟩ := hss S (by
      intro g y hy
      have h := hS g y hy
      rw [hrel, Matrix.smul_mulVec] at h
      have h2 := S.smul_mem (c g)⁻¹ h
      rwa [smul_smul, inv_mul_cancel₀ (hc0 g), one_smul] at h2)
    refine ⟨D', fun g y hy => ?_, hcompl⟩
    rw [hrel, Matrix.smul_mulVec]
    exact D'.smul_mem _ (hD' g y hy)
  obtain ⟨C, hCs, hc⟩ := exists_stable_compl ρ hblk W (fun γ v hv => by
    rw [← hact]; exact hW γ v hv)
  exact ⟨C, fun γ v hv => by rw [hact]; exact hCs γ v hv, hc⟩

end GlobalTheory.BlockSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWildInertiaGeneratingCyclotomicValue
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

noncomputable section

namespace GlobalTheory.WildCycGen

def ex {l : ℕ} (hl : l.Prime) (k : ℕ) : ℕ :=
  (Nat.chineseRemainder (Nat.Coprime.pow_left (k + 1)
    (Nat.coprime_ordCompl hl (Nat.factorial_ne_zero k))) 1 0).1

theorem ex_modEq {l : ℕ} (hl : l.Prime) (k : ℕ) : ex hl k ≡ 1 [MOD l ^ (k + 1)] :=
  (Nat.chineseRemainder (Nat.Coprime.pow_left (k + 1)
    (Nat.coprime_ordCompl hl (Nat.factorial_ne_zero k))) 1 0).2.1

theorem ex_dvd {l : ℕ} (hl : l.Prime) (k : ℕ) :
    (k.factorial / l ^ (k.factorial).factorization l) ∣ ex hl k :=
  Nat.modEq_zero_iff_dvd.1 (Nat.chineseRemainder (Nat.Coprime.pow_left (k + 1)
    (Nat.coprime_ordCompl hl (Nat.factorial_ne_zero k))) 1 0).2.2

theorem pow_ex {Q : Type*} [Group Q] {l : ℕ} (hl : l.Prime) (x : Q) {d : ℕ} (hd : 0 < d)
    (hx : x ^ d = 1) :
    (∀ k, d ≤ k → x ^ ex hl k = x ^ ex hl d) ∧ x ^ (ex hl d * l ^ d.factorization l) = 1 := by
  set a := d.factorization l
  set d' := d / l ^ a
  have hdd : l ^ a * d' = d := Nat.ordProj_mul_ordCompl_eq_self d l
  have hco : (l ^ a).Coprime d' := Nat.Coprime.pow_left a (Nat.coprime_ordCompl hl hd.ne')
  have hla : l ^ a ≤ d := Nat.le_of_dvd hd (Nat.ordProj_dvd d l)
  have ha : a < l ^ a := Nat.lt_pow_self hl.one_lt
  have hdvd : ∀ k, d ≤ k → d' ∣ ex hl k := fun k hk =>
    (Nat.ordCompl_dvd_ordCompl_of_dvd (Nat.dvd_factorial hd hk) l).trans (ex_dvd hl k)
  have hmod1 : ∀ k, d ≤ k → ex hl k ≡ 1 [MOD l ^ a] := fun k hk =>
    Nat.ModEq.of_dvd (Nat.pow_dvd_pow l (by omega)) (ex_modEq hl k)
  have hord : orderOf x ∣ d := orderOf_dvd_of_pow_eq_one hx
  refine ⟨fun k hk => ?_, ?_⟩
  · rw [pow_eq_pow_iff_modEq]
    refine Nat.ModEq.of_dvd hord ?_
    have h := (Nat.modEq_and_modEq_iff_modEq_mul hco).1 ⟨(hmod1 k hk).trans (hmod1 d le_rfl).symm,
      (Nat.modEq_zero_iff_dvd.2 (hdvd k hk)).trans (Nat.modEq_zero_iff_dvd.2 (hdvd d le_rfl)).symm⟩
    rwa [hdd] at h
  · obtain ⟨t, ht⟩ := hdvd d le_rfl
    have e : ex hl d * l ^ a = d * t := by rw [ht, ← hdd]; ring
    rw [e, pow_mul, hx, one_pow]

theorem exists_proL {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    {l : ℕ} (hl : l.Prime) (σ : G) : ∃ g0 : G,
    (∀ C : Set G, IsClosed C → (∀ k, σ ^ ex hl k ∈ C) → g0 ∈ C) ∧
    ∀ N : Subgroup G, N.Normal → IsOpen (N : Set G) → ∃ a : ℕ, g0 ^ (l ^ a) ∈ N := by
  obtain ⟨g0, -, hg0⟩ := isCompact_univ.exists_clusterPt
    (f := Filter.map (fun k => σ ^ ex hl k) Filter.atTop) (by simp)
  have hmem : ∀ C : Set G, IsClosed C → (∀ᶠ k in Filter.atTop, σ ^ ex hl k ∈ C) → g0 ∈ C := by
    intro C hC hev
    have h := hg0.mem_closure_of_mem (s := C) hev
    rwa [hC.closure_eq] at h
  refine ⟨g0, fun C hC h => hmem C hC (Filter.Eventually.of_forall h), fun N hN hNo => ?_⟩
  have hfin := Subgroup.quotient_finite_of_isOpen N hNo
  have hd : 0 < N.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hx : ((σ : G ⧸ N)) ^ N.index = 1 := by
    rw [← QuotientGroup.mk_pow]
    exact (QuotientGroup.eq_one_iff _).2 (N.pow_index_mem σ)
  obtain ⟨h1, h2⟩ := pow_ex hl (σ : G ⧸ N) hd hx
  have hC : IsClosed {τ : G | τ⁻¹ * σ ^ ex hl N.index ∈ N} :=
    (N.isClosed_of_isOpen hNo).preimage (by fun_prop)
  have hg : g0⁻¹ * σ ^ ex hl N.index ∈ N := by
    refine hmem _ hC ?_
    rw [Filter.eventually_atTop]
    refine ⟨N.index, fun k hk => ?_⟩
    show (σ ^ ex hl k)⁻¹ * σ ^ ex hl N.index ∈ N
    rw [← QuotientGroup.eq, QuotientGroup.mk_pow, QuotientGroup.mk_pow]
    exact h1 k hk
  refine ⟨N.index.factorization l, ?_⟩
  have hq : (g0 : G ⧸ N) = (σ : G ⧸ N) ^ ex hl N.index := by
    rw [QuotientGroup.eq.2 hg, QuotientGroup.mk_pow]
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hq, ← pow_mul, h2]

end GlobalTheory.WildCycGen

namespace GlobalTheory.WildCycGen

theorem wild_of_pow {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {l : ℕ} (hl : l.Prime) (hA : A.valuation (l : Ω) < 1)
    {σ : G E Ω} (hσ : σ ∈ Ine (F := E) A) {y : Ω} (hy : y ≠ 0) {n : ℕ} (hn : (σ ^ (l ^ n)) y = y) :
    A.valuation (σ y / y - 1) < 1 := by
  have hdec : σ ∈ Dec (F := E) A := hσ.1
  have hvs : ∀ (j : ℕ) (z : Ω), A.valuation ((σ ^ j) z) = A.valuation z := fun j z =>
    GlobalTheory.PrimeToInertia.valuation_apply_eq (pow_mem hdec j) z
  set x := σ y / y with hx
  have hy0 : A.valuation y ≠ 0 := by simpa using hy
  have hx1 : A.valuation x = 1 := by
    rw [hx, map_div₀, show σ y = (σ ^ 1) y by rw [pow_one], hvs 1 y, div_self hy0]
  have hxy : σ y = x * y := by rw [hx]; field_simp
  have hprod : ∀ k : ℕ, (σ ^ k) y = (∏ j ∈ Finset.range k, (σ ^ j) x) * y := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, AlgEquiv.mul_apply, hxy, map_mul, ih, Finset.prod_range_succ]
      ring
  have hj : ∀ j : ℕ, A.valuation ((σ ^ j) x - x) < 1 := fun j => (pow_mem hσ j).2 x hx1.le
  have hpk : ∀ k : ℕ, A.valuation ((∏ j ∈ Finset.range k, (σ ^ j) x) - x ^ k) < 1 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.prod_range_succ, pow_succ]
      have e : (∏ j ∈ Finset.range k, (σ ^ j) x) * (σ ^ k) x - x ^ k * x =
          ((∏ j ∈ Finset.range k, (σ ^ j) x) - x ^ k) * (σ ^ k) x + x ^ k * ((σ ^ k) x - x) := by ring
      rw [e]
      refine Valuation.map_add_lt _ ?_ ?_
      · rw [map_mul, hvs k x, hx1, mul_one]; exact ih
      · rw [map_mul, map_pow, hx1, one_pow, one_mul]; exact hj k
  have hP : (∏ j ∈ Finset.range (l ^ n), (σ ^ j) x) = 1 := by
    have h := hprod (l ^ n)
    rw [hn] at h
    exact mul_right_cancel₀ hy (h.symm.trans (one_mul y).symm)
  have hxN : A.valuation (x ^ (l ^ n) - 1) < 1 := by
    have h := hpk (l ^ n)
    rw [hP, ← Valuation.map_neg, neg_sub] at h
    exact h

  have hxA : x ∈ A := (A.valuation_le_one_iff x).1 hx1.le
  set xa : A := ⟨x, hxA⟩
  haveI : Fact l.Prime := ⟨hl⟩
  have hlm : ((l : A) : Ω) = (l : Ω) := by simp
  have hl0 : ((l : ℕ) : IsLocalRing.ResidueField A) = 0 := by
    rw [← map_natCast (IsLocalRing.residue A), IsLocalRing.residue_eq_zero_iff,
      ValuationSubring.valuation_lt_one_iff, hlm]
    exact hA
  haveI : CharP (IsLocalRing.ResidueField A) l := (CharP.charP_iff_prime_eq_zero hl).2 hl0
  have h1 : IsLocalRing.residue A (xa ^ (l ^ n) - 1) = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
    simpa [xa] using hxN
  have h2 : IsLocalRing.residue A (xa - 1) = 0 := by
    rw [map_sub, map_pow, map_one] at h1
    have h3 : (IsLocalRing.residue A xa - 1) ^ (l ^ n) = 0 := by
      rw [sub_pow_char_pow, one_pow, h1]
    rw [map_sub, map_one]
    exact pow_eq_zero_iff (pow_ne_zero _ hl.ne_zero) |>.1 h3
  rw [IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff] at h2
  simpa [xa] using h2

end GlobalTheory.WildCycGen

namespace GlobalTheory.WildCycGen

theorem one_add_pow_sub_mem {l : ℕ} [Fact l.Prime] {s c : ℕ} (hs : 1 ≤ s) (hc : c % l = 1) :
    (1 + (l : ℤ_[l]) ^ s) ^ c - (1 + (l : ℤ_[l]) ^ s) ∈ Ideal.span {(l : ℤ_[l]) ^ (s + 1)} := by
  rw [← PadicInt.ker_toZModPow, RingHom.mem_ker]
  simp only [map_sub, map_pow, map_add, map_one, map_natCast]
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  set X : ZMod (l ^ (s' + 1 + 1)) := (l : ZMod (l ^ (s' + 1 + 1))) ^ (s' + 1) with hX
  have hlx : (l : ZMod (l ^ (s' + 1 + 1))) * X = 0 := by
    rw [hX, ← pow_succ', ← Nat.cast_pow, ZMod.natCast_self]
  have hX2 : X * X = 0 := by
    have e : X * X = ((l : ZMod (l ^ (s' + 1 + 1))) * X) * (l : ZMod (l ^ (s' + 1 + 1))) ^ s' := by
      rw [hX]; ring
    rw [e, hlx, zero_mul]
  have hpow : ∀ m : ℕ, (1 + X) ^ m = 1 + (m : ZMod (l ^ (s' + 1 + 1))) * X := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ (1 + X) m, ih]
      push_cast
      linear_combination (m : ZMod (l ^ (s' + 1 + 1))) * hX2
  rw [hpow]
  have hc' : c = l * (c / l) + 1 := by have := Nat.div_add_mod c l; omega
  rw [hc']
  push_cast
  linear_combination ((c / l : ℕ) : ZMod (l ^ (s' + 1 + 1))) * hlx

theorem ex_mod {l : ℕ} (hl : l.Prime) (k : ℕ) : ex hl k % l = 1 := by
  have h := Nat.ModEq.of_dvd (dvd_pow_self l (Nat.succ_ne_zero k)) (ex_modEq hl k)
  rw [Nat.ModEq, Nat.mod_eq_of_lt hl.one_lt] at h
  exact h

theorem main : ∀ (D : D7) (i : D.nd.Loc) (k : Fin 2), D.nd.l i = D.host.g k → ∃ g0 : GE D.nd, (∃ w ∈ placesOver D.host.E (D.nd.l i), g0 ∈ Ine (F := D.host.E) (D.nd.plOm.1 w)) ∧ (∃ u : ℤ_[D.nd.l i]ˣ, ((cycZ (F := D.host.E) (Ω := D.nd.Om) (D.nd.l i) g0 : ℤ_[D.nd.l i]ˣ) : ℤ_[D.nd.l i]) = 1 + (D.nd.l i : ℤ_[D.nd.l i]) ^ D.nd.s0 i * (u : ℤ_[D.nd.l i])) ∧ ∀ w ∈ placesOver D.host.E (D.nd.l i), g0 ∈ Ine (F := D.host.E) (D.nd.plOm.1 w) → g0 ∈ wildSet D.nd (D.nd.plOm.1 w) := by
  intro D i k hk
  have hl : (D.nd.l i).Prime := Fact.out

  obtain ⟨w, hw⟩ : (placesOver D.host.E (D.nd.l i)).Nonempty := by
    refine Set.nonempty_of_ncard_ne_zero ?_
    rw [(GlobalTheory.TypeDegOne.degree_one D i k hk).1]
    have h5 : D.R.f = 2 * D.R.ord := rfl
    rw [h5]
    positivity
  obtain ⟨σ, hσI, hσc⟩ := GlobalTheory.PtCore.EpsAll.exists_generator (GlobalTheory.EpsInertia.epsAll D i) w hw
  obtain ⟨g0, hC, hP⟩ := exists_proL hl σ
  have hs : 1 ≤ D.nd.s0 i := by
    exact UpperTheory.KStar.S0.one_le_localLevel D.nd i
  refine ⟨g0, ⟨w, hw, hC _ (isClosed_Ine (F := D.host.E) (D.nd.plOm.1 w)) fun k => pow_mem hσI _⟩, ?_, ?_⟩
  ·
    set L : ℤ_[D.nd.l i] := (D.nd.l i : ℤ_[D.nd.l i])
    have hcont : Continuous fun τ : GE D.nd =>
        ‖((cycZ (F := D.host.E) (Ω := D.nd.Om) (D.nd.l i) τ : ℤ_[D.nd.l i]ˣ) : ℤ_[D.nd.l i]) -
          (1 + L ^ D.nd.s0 i)‖ :=
      continuous_norm.comp ((Units.continuous_val.comp (continuous_cycZ _ _ (D.nd.l i))).sub continuous_const)
    have hg := hC _ (isClosed_le hcont continuous_const) fun k => by
      show ‖((cycZ (F := D.host.E) (Ω := D.nd.Om) (D.nd.l i) (σ ^ ex hl k) : ℤ_[D.nd.l i]ˣ) : ℤ_[D.nd.l i]) -
          (1 + L ^ D.nd.s0 i)‖ ≤ ((D.nd.l i : ℝ)) ^ (-((D.nd.s0 i + 1 : ℕ) : ℤ))
      rw [PadicInt.norm_le_pow_iff_mem_span_pow, map_pow, Units.val_pow_eq_pow_val, hσc]
      exact one_add_pow_sub_mem hs (ex_mod hl k)
    rw [Set.mem_setOf_eq, PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton'] at hg
    obtain ⟨t, ht⟩ := hg
    have hu : IsUnit (1 + L * t) := by
      rw [← sub_neg_eq_add]
      refine IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ fun h => ?_
      exact PadicInt.irreducible_p.not_isUnit (isUnit_of_mul_isUnit_left ((IsUnit.neg_iff _).1 h))
    refine ⟨hu.unit, ?_⟩
    rw [IsUnit.unit_spec]
    linear_combination (-1 : ℤ_[D.nd.l i]) * ht
  ·
    intro w' hw' hine y hy
    have hA : (D.nd.plOm.1 w').valuation ((D.nd.l i : ℕ) : D.nd.Om) < 1 := by
      have h := (D.nd.plOm.2 w' ((D.nd.l i : ℕ) : 𝓞 D.host.E)).2 hw'
      simpa using h
    have hfd : FiniteDimensional D.host.E (IntermediateField.adjoin D.host.E {y}) :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral y)
    have ho := IntermediateField.fixingSubgroup_isOpen (IntermediateField.adjoin D.host.E {y})
    obtain ⟨H, hH⟩ := IsTopologicalGroup.exist_openNormalSubgroup_sub_clopen_nhds_of_one
      ⟨Subgroup.isClosed_of_isOpen _ ho, ho⟩ (IntermediateField.adjoin D.host.E {y}).fixingSubgroup.one_mem
    obtain ⟨a, ha⟩ := hP H.toSubgroup H.isNormal' H.isOpen
    have hfix : (g0 ^ (D.nd.l i ^ a)) y = y :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 (hH ha) y
        (IntermediateField.subset_adjoin _ _ (Set.mem_singleton y))
    exact wild_of_pow hl hA hine hy hfix

end GlobalTheory.WildCycGen

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExpandMapDvdOfBreuilKisinFrobeniusDvdStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.expand_map_dvd_of_breuilKisinFrobenius_dvd : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (P Q : Polynomial (Wq l a)), P.Monic →
    (∀ i < P.natDegree, (l : Wq l a) ∣ P.coeff i) → frobS l a (P : (Wq l a)⟦X⟧) ∣ (Q : (Wq l a)⟦X⟧) →
    Polynomial.expand (Wq l a) l (P.map (sigma l a : Wq l a →+* Wq l a)) ∣ Q := by
  first | exact @GlobalTheory.expand_map_dvd_of_frobS_dvd | exact GlobalTheory.expand_map_dvd_of_frobS_dvd | (intros; apply GlobalTheory.expand_map_dvd_of_frobS_dvd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorialMulCoeffMemDividedPowerSeriesSubringStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.factorial_mul_coeff_mem_dividedPowerSeriesSubring : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ F ∈ PPSet t K e, ∀ (τ : ZMod a) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (F τ) ∈ S O K e := by
  first | exact @GlobalTheory.CrysPrism.factorial_mul_coeff_mem_S | exact GlobalTheory.CrysPrism.factorial_mul_coeff_mem_S | (intros; apply GlobalTheory.CrysPrism.factorial_mul_coeff_mem_S <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FirstCharacterTrivialWildInertiaTypePrimeStatement
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.firstCharacter_trivial_wildInertia_typePrime : ∀ (D : D7) (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k), D.nd.l i ≠ D.host.g k → ∀ s ∈ wildSet D.nd (D.nd.plOm.1 (D.naut.plGw k v)), D.nd.chi i 1 s = 1 := by
  first | exact @GlobalTheory.ChiTame.main | exact GlobalTheory.ChiTame.main | (intros; apply GlobalTheory.ChiTame.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisEisensteinEvalEqMulUnitCoeffDeRhamPlusStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_eisensteinEval_eq_mul_unit_coeffDeRhamPlus : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [CompleteSpace K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (g : GQ l), g ∈ GK (ϖ.field a) → ∃ v : OD l O, IsUnit v ∧ GlobalTheory.GalStep.galOD O g (GlobalTheory.GalStep.ED K t ϖ) = GlobalTheory.GalStep.ED K t ϖ * v := by
  first | exact @GlobalTheory.GalStep.galOD_ED | exact GlobalTheory.GalStep.galOD_ED | (intros; apply GlobalTheory.GalStep.galOD_ED <;> assumption)
end

