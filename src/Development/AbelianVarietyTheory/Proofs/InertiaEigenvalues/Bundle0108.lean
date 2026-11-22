import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0076
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0075
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedQuadraticNormsTraceUniformizerFacts
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0087
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0067
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0088
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0089
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodDataComparison
import Formalism.WeaklyAdmissibleFiltrations.Statement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemAdjoinOfMulEqOne
section
namespace GlobalTheory.UnitLemma.TwistUnit

open GlobalTheory.UnitLemma Polynomial

theorem mem_adjoin_of_mul_eq_one {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {s t : A}
    (h : s * t = 1) (ht : IsIntegral O t) : t ∈ Algebra.adjoin O {s} := by
  obtain ⟨p, hp, hpt⟩ := ht
  have e : aeval t p = 0 := hpt
  rw [aeval_eq_sum_range, Finset.sum_range_succ, hp.coeff_natDegree, one_smul] at e
  rcases Nat.eq_zero_or_pos p.natDegree with h0 | hpos
  · rw [h0] at e
    simp at e
    have : t = 0 := by simpa using congrArg (t * ·) e
    rw [this]; exact Subalgebra.zero_mem _
  obtain ⟨k, hk⟩ : ∃ k, p.natDegree = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
  rw [hk] at e
  have hts : t * s = 1 := by rw [mul_comm]; exact h
  have h1 : t ^ (k + 1) * s ^ k = t := by
    rw [pow_succ', mul_assoc, ← mul_pow, hts, one_pow, mul_one]
  have h2 : ∀ i ∈ Finset.range (k + 1), p.coeff i • t ^ i * s ^ k = p.coeff i • s ^ (k - i) := by
    intro i hi
    have hik : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    rw [smul_mul_assoc]
    congr 1
    rw [show s ^ k = s ^ i * s ^ (k - i) by rw [← pow_add, Nat.add_sub_cancel' hik], ← mul_assoc,
      ← mul_pow, hts, one_pow, one_mul]
  have e2 := congrArg (· * s ^ k) e
  simp only [add_mul, zero_mul, Finset.sum_mul] at e2
  rw [Finset.sum_congr rfl h2, h1] at e2
  have key : t = -∑ i ∈ Finset.range (k + 1), p.coeff i • s ^ (k - i) := by
    linear_combination e2
  rw [key]
  exact Subalgebra.neg_mem _ (Subalgebra.sum_mem _ fun i _ =>
    Subalgebra.smul_mem _ (Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton O s) _) _)

theorem adjoin_stab {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {s : A} (L : Submodule O A)
    (hL : ∀ y ∈ L, s * y ∈ L) {a : A} (ha : a ∈ Algebra.adjoin O {s}) : ∀ y ∈ L, a * y ∈ L := by
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    subst hx; exact hL
  | algebraMap r =>
    intro y hy
    rw [← Algebra.smul_def]; exact L.smul_mem r hy
  | add x z _ _ hx hz =>
    intro y hy
    rw [add_mul]; exact L.add_mem (hx y hy) (hz y hy)
  | mul x z _ _ hx hz =>
    intro y hy
    rw [mul_assoc]; exact hx _ (hz y hy)

variable {K : UQ}

theorem trace_σ (B : InvAlg K) (a : B.A) :
    Algebra.trace K.E B.A (B.σ a) = K.c (Algebra.trace K.E B.A a) := by
  classical
  let b := Module.Free.chooseBasis K.E B.A
  have hsm : ∀ (e : K.E) (y : B.A), B.σ (e • y) = K.c e • B.σ y := by
    intro e y
    rw [Algebra.smul_def, map_mul, B.σ_alg, ← Algebra.smul_def]
  have hli : LinearIndependent K.E ((B.σ : B.A →+ B.A) ∘ b) := by
    refine b.linearIndependent.map_of_injective_injective (fun r => K.c.symm r) (B.σ : B.A →+ B.A) ?_ ?_ ?_
    · intro r hr
      simpa using hr
    · intro m hm
      have : B.σ m = 0 := hm
      simpa using this
    · intro r m
      show B.σ (K.c.symm r • m) = r • B.σ m
      rw [hsm, RingEquiv.apply_symm_apply]
  have hsp : ⊤ ≤ Submodule.span K.E (Set.range ((B.σ : B.A →+ B.A) ∘ b)) := by
    intro y _
    have h1 : y = ∑ j, K.c (b.repr (B.σ.symm y) j) • B.σ (b j) := by
      conv_lhs => rw [← B.σ.apply_symm_apply y, ← b.sum_repr (B.σ.symm y)]
      rw [map_sum]
      exact Finset.sum_congr rfl fun j _ => hsm _ _
    rw [h1]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  let b' : Module.Basis (Module.Free.ChooseBasisIndex K.E B.A) K.E B.A := Module.Basis.mk hli hsp
  have hb' : ∀ i, b' i = B.σ (b i) := fun i => by
    simp only [b', Module.Basis.mk_apply]
    rfl
  have hrepr : ∀ y i, b'.repr (B.σ y) i = K.c (b.repr y i) := by
    intro y i
    have h1 : B.σ y = ∑ j, K.c (b.repr y j) • b' j := by
      conv_lhs => rw [← b.sum_repr y]
      rw [map_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [hsm, hb']
    rw [h1, b'.repr_sum_self]
  rw [Algebra.trace_eq_matrix_trace b', Algebra.trace_eq_matrix_trace b, Matrix.trace, Matrix.trace,
    map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul]
  rw [hb', ← map_mul, hrepr]

theorem mem_range_c (e : K.E) : K.c e ∈ (algebraMap K.O K.E).range ↔ e ∈ (algebraMap K.O K.E).range := by
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨b, hb⟩ := K.c_int a
    refine ⟨b, ?_⟩
    rw [← hb, ha, K.c_c]
  · rintro ⟨a, rfl⟩
    obtain ⟨b, hb⟩ := K.c_int a
    exact ⟨b, hb.symm⟩

theorem trace_σ_mem (B : InvAlg K) (a : B.A) :
    Algebra.trace K.E B.A (B.σ a) ∈ (algebraMap K.O K.E).range ↔
      Algebra.trace K.E B.A a ∈ (algebraMap K.O K.E).range := by
  rw [trace_σ, mem_range_c]

theorem twisted_unit_eq_unit : ∀ (K : UQ) (B : InvAlg K), B.g * B.σ B.g = 1 → B.P.Separable → IsIntegral K.O B.g →
    ∀ (ε : B.A), (ε = 1 ∨ ε = -1) → ∃ β₀ : B.Aˣ, B.σ (β₀ : B.A) = β₀ * (ε * B.g) ∧
      ∀ x : B.Aˣ, B.σ (x : B.A) = x →
        {L : Submodule K.O B.A | IsLat K.O K.E L ∧ ∀ z, z ∈ L ↔ ∀ y ∈ L,
          B.herm (β₀ * x) y z ∈ (algebraMap K.O K.E).range} = B.X x := by
  intro K B hg hs hi ε hε
  obtain ⟨β₀, hβ, hb1, hb2⟩ := GlobalTheory.T.exists_unit_basePoint_adjoin_twisted_sigma K B hg hs hi ε hε
  refine ⟨β₀, hβ, fun x hx => ?_⟩
  set R := (algebraMap K.O K.E).range with hR
  set T := Algebra.trace K.E B.A with hT
  have hεT : ∀ a, T (ε * a) ∈ R ↔ T a ∈ R := by
    intro a
    rcases hε with rfl | rfl
    · rw [one_mul]
    · rw [neg_one_mul, map_neg, neg_mem_iff]
  have hstab : ∀ L : Submodule K.O B.A, (∀ y ∈ L, B.g * y ∈ L) → ∀ w : B.A,
      ((∀ y ∈ L, T ((β₀ : B.A) * x * y * B.σ w) ∈ R) ↔ ∀ y ∈ L, T ((x : B.A) * y * B.σ w) ∈ R) := by
    intro L hL w
    have s1 := adjoin_stab L hL hb1
    have s2 := adjoin_stab L hL hb2
    constructor
    · intro h y hy
      have := h _ (s2 y hy)
      have e : (β₀ : B.A) * x * (((β₀⁻¹ : B.Aˣ) : B.A) * y) * B.σ w = x * y * B.σ w := by
        have := β₀.mul_inv
        linear_combination (↑x * y * B.σ w) * this
      rwa [e] at this
    · intro h y hy
      have := h _ (s1 y hy)
      rwa [show (x : B.A) * ((β₀ : B.A) * y) * B.σ w = β₀ * x * y * B.σ w by ring] at this
  have hX' : ∀ (L : Submodule K.O B.A) (w : B.A),
      ((∀ y ∈ L, T ((x : B.A) * w * B.σ y) ∈ R) ↔ ∀ y ∈ L, T ((x : B.A) * y * B.σ w) ∈ R) := by
    intro L w
    refine forall₂_congr fun y _ => ?_
    rw [← trace_σ_mem B]
    rw [show B.σ ((x : B.A) * w * B.σ y) = x * y * B.σ w by
      rw [map_mul, map_mul, hx, B.σ_σ]; ring]
  have hsym : ∀ a b : B.A, T ((β₀ : B.A) * x * a * B.σ b) ∈ R ↔
      T ((β₀ : B.A) * x * (B.g * b) * B.σ a) ∈ R := by
    intro a b
    rw [← trace_σ_mem B ((β₀ : B.A) * x * a * B.σ b),
      show B.σ ((β₀ : B.A) * x * a * B.σ b) = ε * ((β₀ : B.A) * x * (B.g * b) * B.σ a) by
        rw [map_mul, map_mul, map_mul, hβ, hx, B.σ_σ]; ring, hεT]
  have hgg : B.σ B.g * B.g = 1 := by rw [mul_comm]; exact hg
  have hgad : B.g ∈ Algebra.adjoin K.O {B.σ B.g} := mem_adjoin_of_mul_eq_one hgg hi
  ext L
  simp only [Set.mem_setOf_eq, InvAlg.X, InvAlg.herm, Units.val_mul, ← hT, ← hR]
  constructor
  · rintro ⟨hLat, hU⟩
    have h1 : ∀ y ∈ L, B.σ B.g * y ∈ L := by
      intro y hy
      rw [hU]
      intro y' hy'
      rw [hsym, show (β₀ : B.A) * x * (B.g * (B.σ B.g * y)) * B.σ y' = β₀ * x * y * B.σ y' by
        linear_combination ((β₀ : B.A) * x * y * B.σ y') * hg]
      exact (hU y').1 hy' y hy
    have h2 : ∀ y ∈ L, B.g * y ∈ L := adjoin_stab L h1 hgad
    refine ⟨hLat, h2, fun y => ?_⟩
    rw [hX' L y, ← hstab L h2, ← hU]
  · rintro ⟨hLat, h2, hXc⟩
    refine ⟨hLat, fun z => ?_⟩
    rw [hstab L h2, ← hX', ← hXc]

end GlobalTheory.UnitLemma.TwistUnit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormCharacterOnIdempotentPartFrameProperties
section
noncomputable section

namespace GlobalTheory.UnitLemma.Desc

open GlobalTheory.UnitLemma Polynomial Filter Topology

variable {K : UQ} (B : InvAlg K)

theorem eta_c (x : K.E) : K.eta (K.c x) = K.eta x := by
  unfold UQ.eta; rw [UnramNorm.val_c]

theorem norm_sigma (u : B.A) : Algebra.norm K.E (B.σ u) = K.c (Algebra.norm K.E u) := by
  have h := Algebra.norm_eq_of_equiv_equiv K.c B.σ (by ext e; simp [B.σ_alg]) u
  rw [h, RingEquiv.apply_symm_apply]

theorem norm_ne_zero_of_isUnit {u : B.A} (hu : IsUnit u) : Algebra.norm K.E u ≠ 0 :=
  (hu.map (Algebra.norm K.E)).ne_zero

theorem eta_norm_mul_sigma {v : B.A} (hv : IsUnit v) : K.eta (Algebra.norm K.E (v * B.σ v)) = 1 := by
  rw [map_mul, norm_sigma, eta_mul (norm_ne_zero_of_isUnit B hv)
    ((map_ne_zero K.c).2 (norm_ne_zero_of_isUnit B hv)), eta_c, eta_sq]

theorem twist_mul {E : B.A} (hE : E * E = E) (x y : B.A) :
    (x * E + (1 - E)) * (y * E + (1 - E)) = x * y * E + (1 - E) := by
  linear_combination (x * y - x - y + 1) * hE

theorem twist_isUnit {E : B.A} (hE : E * E = E) {x : B.A} (hx : IsUnit x) : IsUnit (x * E + (1 - E)) := by
  obtain ⟨u, rfl⟩ := hx
  refine isUnit_iff_exists_inv.2 ⟨((u⁻¹ : B.Aˣ) : B.A) * E + (1 - E), ?_⟩
  rw [twist_mul B hE, Units.mul_inv, one_mul]; ring

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem e_mul_eS {e : ι → B.A} (he : OrthogonalIdempotents e) (i : ι) (I : Finset ι) :
    e i * eS B e I = if i ∈ I then e i else 0 := by
  unfold eS; rw [Finset.mul_sum]; split_ifs with h
  · rw [Finset.sum_eq_single i (fun j _ hji => he.ortho (Ne.symm hji)) (fun h' => absurd h h'), (he.idem i).eq]
  · exact Finset.sum_eq_zero fun j hj => he.ortho (fun hij => h (hij ▸ hj))

theorem eS_idem {e : ι → B.A} (he : OrthogonalIdempotents e) (I : Finset ι) :
    eS B e I * eS B e I = eS B e I := by
  show (∑ i ∈ I, e i) * eS B e I = _
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [e_mul_eS B he, if_pos hi]

theorem sigma_e {e : ι → B.A} {S : Finset ι} (h : IsPre B e S) (i : ι) : B.σ (e i) = e i := by
  obtain ⟨f, -, -, -, h1, h2⟩ := h.2 i
  by_cases hi : i ∈ S
  · rw [(h1 hi).1, (h1 hi).2]
  · rw [(h2 hi).2, map_add, B.σ_σ, add_comm]

theorem sigma_eS {e : ι → B.A} {S : Finset ι} (h : IsPre B e S) (I : Finset ι) : B.σ (eS B e I) = eS B e I := by
  unfold eS; rw [map_sum]; exact Finset.sum_congr rfl fun i _ => sigma_e B h i

theorem chi_mul {e : ι → B.A} (he : OrthogonalIdempotents e) (I : Finset ι) {x y : B.A} (hx : IsUnit x)
    (hy : IsUnit y) : chi B e I (x * y) = chi B e I x * chi B e I y := by
  unfold chi
  have hE := eS_idem B he I
  rw [← twist_mul B hE, map_mul, eta_mul (norm_ne_zero_of_isUnit B (twist_isUnit B hE hx))
    (norm_ne_zero_of_isUnit B (twist_isUnit B hE hy))]

theorem chi_norm {e : ι → B.A} {S : Finset ι} (h : IsPre B e S) (I : Finset ι) {w : B.A} (hw : IsUnit w) :
    chi B e I (w * B.σ w) = 1 := by
  unfold chi
  have hE := eS_idem B h.1.toOrthogonalIdempotents I
  have hσ : B.σ (w * eS B e I + (1 - eS B e I)) = B.σ w * eS B e I + (1 - eS B e I) := by
    rw [map_add, map_mul, map_sub, map_one, sigma_eS B h]
  rw [← twist_mul B hE, ← hσ]
  exact eta_norm_mul_sigma B (twist_isUnit B hE hw)

theorem eta_prod {s : Finset ι} (x : ι → K.E) (hx : ∀ i ∈ s, x i ≠ 0) :
    K.eta (∏ i ∈ s, x i) = ∏ i ∈ s, K.eta (x i) := by
  induction s using Finset.induction_on with
  | empty => simp [UQ.eta, val]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      eta_mul (hx a (Finset.mem_insert_self a s)) (Finset.prod_ne_zero_iff.2 fun i hi => hx i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hx i (Finset.mem_insert_of_mem hi)]

theorem chi_prod {e π : ι → B.A} {S : Finset ι} (h : IsFrame B e π S) (I J : Finset ι) (hJ : J ⊆ S) :
    chi B e I (∏ j ∈ J, π j) = (-1) ^ (J ∩ I).card := by
  have he := h.1.1.toOrthogonalIdempotents
  set E := eS B e I with hEdef
  have hE := eS_idem B he I

  have h1 : (∏ j ∈ J.filter (· ∉ I), π j) * E = E := by
    refine Finset.prod_induction _ (fun t => t * E = E) (fun a b ha hb => by rw [mul_assoc, hb, ha]) (one_mul _) ?_
    intro j hj
    obtain ⟨hjJ, hjI⟩ := Finset.mem_filter.1 hj
    have hEe : E = (1 - e j) * E := by
      rw [sub_mul, one_mul, mul_comm (e j) E, hEdef, mul_comm, e_mul_eS B he, if_neg hjI, sub_zero]
    show π j * E = E
    rw [hEe, ← mul_assoc, (h.2 j (hJ hjJ)).2.1]
  have h2 : (∏ j ∈ J.filter (· ∈ I), π j) * (1 - E) = 1 - E := by
    refine Finset.prod_induction _ (fun t => t * (1 - E) = 1 - E) (fun a b ha hb => by rw [mul_assoc, hb, ha]) (one_mul _) ?_
    intro j hj
    obtain ⟨hjJ, hjI⟩ := Finset.mem_filter.1 hj
    have hEe : 1 - E = (1 - e j) * (1 - E) := by
      have := e_mul_eS B he j I
      rw [if_pos hjI] at this
      rw [← hEdef] at this
      linear_combination -this
    show π j * (1 - E) = 1 - E
    rw [hEe, ← mul_assoc, (h.2 j (hJ hjJ)).2.1]
  have hprod : (∏ j ∈ J, π j) * E + (1 - E) = ∏ j ∈ J.filter (· ∈ I), π j := by
    rw [← Finset.prod_filter_mul_prod_filter_not J (· ∈ I), mul_assoc]
    rw [h1]
    linear_combination -h2
  unfold chi
  rw [← hEdef, hprod, map_prod, eta_prod]
  · rw [Finset.filter_mem_eq_inter]
    rw [Finset.prod_congr rfl fun j hj => (h.2 j (hJ (Finset.mem_inter.1 hj).1)).2.2, Finset.prod_const]
  · intro j hj
    exact norm_ne_zero_of_isUnit B (h.2 j (hJ (Finset.mem_filter.1 hj).1)).1.1

theorem mul_eq_zero_of_idem {e : ι → B.A} (he : OrthogonalIdempotents e) {i j : ι} (hij : i ≠ j) {a b : B.A}
    (ha : a * e i = a) (hb : b * e j = b) : a * b = 0 := by
  rw [← ha, ← hb, show a * e i * (b * e j) = a * b * (e i * e j) by ring, he.ortho hij, mul_zero]

theorem sum_mul_sum_diag {e : ι → B.A} (he : OrthogonalIdempotents e) (s : Finset ι) (a b : ι → B.A)
    (ha : ∀ i ∈ s, a i * e i = a i) (hb : ∀ i ∈ s, b i * e i = b i) :
    (∑ i ∈ s, a i) * (∑ j ∈ s, b j) = ∑ i ∈ s, a i * b i := by
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  exact Finset.sum_eq_single i (fun j hj hji => mul_eq_zero_of_idem B he (Ne.symm hji) (ha i hi) (hb j hj))
    (fun h => absurd hi h)

theorem chi_plus {e : ι → B.A} {S : Finset ι} (h : IsPre B e S) {y : B.A} (hy : B.Plus y) :
    chi B e S y = K.eta (Algebra.norm K.E y) := by
  have he := h.1.toOrthogonalIdempotents
  have hcomp := h.1.complete
  choose f hf using h.2
  set E := eS B e S with hEdef
  have hE : E * E = E := eS_idem B he S
  have hσE : B.σ E = E := sigma_eS B h S
  have hfe : ∀ i ∈ Sᶜ, f i * e i = f i := by
    intro i hi
    have hiS := Finset.mem_compl.1 hi
    obtain ⟨hid, -, -, -, h2⟩ := hf i
    rw [(h2 hiS).2, mul_add, hid.eq, (h2 hiS).1, add_zero]
  have hge : ∀ i ∈ Sᶜ, B.σ (f i) * e i = B.σ (f i) := by
    intro i hi
    have hiS := Finset.mem_compl.1 hi
    obtain ⟨hid, -, -, -, h2⟩ := hf i
    rw [(h2 hiS).2, mul_add, mul_comm (B.σ (f i)) (f i), (h2 hiS).1, zero_add, ← map_mul, hid.eq]
  set F := ∑ i ∈ Sᶜ, f i with hFdef
  set G := ∑ i ∈ Sᶜ, B.σ (f i) with hGdef
  have hGσ : G = B.σ F := by rw [hGdef, hFdef, map_sum]
  have hFF : F * F = F := by
    rw [hFdef, sum_mul_sum_diag B he _ f f hfe hfe]; exact Finset.sum_congr rfl fun i _ => (hf i).1.eq
  have hFG : F * G = 0 := by
    rw [hFdef, hGdef, sum_mul_sum_diag B he _ f _ hfe hge]
    exact Finset.sum_eq_zero fun i hi => ((hf i).2.2.2.2 (Finset.mem_compl.1 hi)).1
  have hGG : G * G = G := by rw [hGσ, ← map_mul, hFF]
  have hFE : F * E = 0 := by
    rw [hFdef, hEdef, eS, Finset.sum_mul_sum]
    exact Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj =>
      mul_eq_zero_of_idem B he (fun hij => Finset.mem_compl.1 hi (by rw [hij]; exact hj)) (hfe i hi) (he.idem j).eq
  have hGE : G * E = 0 := by rw [hGσ, ← hσE, ← map_mul, hFE, map_zero]
  have hFGsum : F + G = 1 - E := by
    have h1 : F + G = ∑ i ∈ Sᶜ, e i := by
      rw [hFdef, hGdef, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i hi => ((hf i).2.2.2.2 (Finset.mem_compl.1 hi)).2.symm
    rw [h1, ← hcomp, ← Finset.sum_add_sum_compl S e, hEdef, eS]; ring
  set w := y * F + G + E with hwdef
  have hσw : B.σ w = y * G + F + E := by
    rw [hwdef, map_add, map_add, map_mul, hy.2, hσE, hGσ, B.σ_σ]
  have hw : w * B.σ w = y * (1 - E) + E := by
    rw [hσw, ← hFGsum]
    linear_combination (y ^ 2 + 1) * hFG + y * hFF + (y + 1) * hFE + y * hGG + (y + 1) * hGE + hE
  have hE' : (1 - E) * (1 - E) = 1 - E := by linear_combination hE
  have hwwU : IsUnit (w * B.σ w) := by
    have := twist_isUnit B hE' hy.1
    rwa [sub_sub_cancel, ← hw] at this
  have hwU : IsUnit w := isUnit_of_mul_isUnit_left hwwU
  have hsplit : y = (y * E + (1 - E)) * (w * B.σ w) := by
    rw [hw]; linear_combination (y ^ 2 - 2 * y + 1) * hE
  unfold chi
  rw [← hEdef]
  conv_rhs => rw [hsplit]
  rw [map_mul, eta_mul (norm_ne_zero_of_isUnit B (twist_isUnit B hE hy.1)) (norm_ne_zero_of_isUnit B hwwU),
    eta_norm_mul_sigma B hwU, mul_one]

theorem chi_frame_props : ∀ (K : UQ) (B : InvAlg K) (ι : Type) [Fintype ι] [DecidableEq ι] (e π : ι → B.A)
    (S : Finset ι), IsFrame B e π S →
    (∀ (I : Finset ι) (x y : B.A), IsUnit x → IsUnit y → chi B e I (x * y) = chi B e I x * chi B e I y) ∧
    (∀ (I : Finset ι) (w : B.A), IsUnit w → chi B e I (w * B.σ w) = 1) ∧
    (∀ I J : Finset ι, I ⊆ S → J ⊆ S → chi B e I (∏ j ∈ J, π j) = (-1) ^ (J ∩ I).card) ∧
    (∀ y, B.Plus y → chi B e S y = K.eta (Algebra.norm K.E y)) := by
  intro K B ι _ _ e π S h
  exact ⟨fun I x y hx hy => chi_mul B h.1.1.toOrthogonalIdempotents I hx hy, fun I w hw => chi_norm B h.1 I hw,
    fun I J _ hJ => chi_prod B h I J hJ, fun y hy => chi_plus B h.1 hy⟩

end GlobalTheory.UnitLemma.Desc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalOfInvMulStatement
section
open GlobalTheory.PMonE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normal_inv_mul_and_norm_inv_le_one : ∀ (F : Type) [NormedField F] [IsUltrametricDist F] (m : Type) [Fintype m] [DecidableEq m] (N : ℕ) (B : ℕ → Matrix m m F), (∀ n i j, ‖B n i j‖ ≤ 1) → (∀ n, N < n → ∀ i j, ‖B n i j‖ < 1) → ‖(B N).det‖ = 1 → Normal N (fun n => (B N)⁻¹ * B n) ∧ ∀ i j, ‖(B N)⁻¹ i j‖ ≤ 1 := by
  first | exact @GlobalTheory.PMonE.normal_of_inv_mul | exact GlobalTheory.PMonE.normal_of_inv_mul | (intros; apply GlobalTheory.PMonE.normal_of_inv_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalisedPeriodAlgebraicEstimateStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_apply_neg_mul_sub_sub_le_mul : ∀ (E : Type) [NormedField E] [IsUltrametricDist E] (n : Type) [Fintype n] [DecidableEq n] (σ : E →+* E) (r M Mi Z : Matrix n n E) (a s t : ℝ), 0 ≤ a → 0 ≤ s → 0 ≤ t → (∀ x, ‖σ x‖ = ‖x‖) → M * Mi = 1 → r * M.map σ = M → Z.map σ = Z → (∀ i j, ‖M i j‖ ≤ a) → (∀ i j, ‖(Mi - Z) i j‖ ≤ s) → (∀ i j, ‖(r - 1) i j‖ ≤ t) → ∀ i j, ‖σ (-(M * Z) i j) - (-(M * Z) i j) - (r - 1) i j‖ ≤ t * (a * s) := by
  first | exact @GlobalTheory.normalisedPeriod_algebraic_estimate | exact GlobalTheory.normalisedPeriod_algebraic_estimate | (intros; apply GlobalTheory.normalisedPeriod_algebraic_estimate <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalizedRowCoefficientMatricesDetNormStatement
section
open GlobalTheory.PMonE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalizedRowCoefficientMatrices_det_norm : ∀ (F : Type) [NormedField F] [IsUltrametricDist F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p] (h : ℕ) (ϖ : F), ϖ ≠ 0 → ∀ lam π : Fin h → F, (∀ j, lam j ≠ 0) → (∀ j, π j ≠ 0) → Antitone (fun j => ‖lam j‖) → Orth p lam → ∀ L U : ℕ, ‖(coefB p ϖ lam π L U L).det‖ = 1 ∧ (coefB p ϖ lam π L U 0).det ≠ 0 := by
  first | exact @GlobalTheory.PMonE.coefB_det | exact GlobalTheory.PMonE.coefB_det | (intros; apply GlobalTheory.PMonE.coefB_det <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NotIsIntegralResidueInvSmallIntegerStatement
section
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.not_isIntegral_residue_inv_small_integer : ∀ (K : UQ) (B : InvAlg K) (a : K.O), K.Small a → ∀ m : MaximalSpectrum B.A, ¬ IsIntegral K.O (algebraMap K.E (B.A ⧸ m.asIdeal) (algebraMap K.O K.E a)⁻¹) := by
  first | exact @GlobalTheory.NotIntegral.inv_small_not_integral | exact GlobalTheory.NotIntegral.inv_small_not_integral | (intros; apply GlobalTheory.NotIntegral.inv_small_not_integral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PartialFourierGLBlockUnitIndicatorStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partialFourierGLBlock_unitIndicator : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → fourG M ψ (unitG r F) = unitG r F := by
  first | exact @GlobalTheory.JR.fourG_unitG | exact GlobalTheory.JR.fourG_unitG | (intros; apply GlobalTheory.JR.fourG_unitG <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PartialFourierHermitianBlockHasCompactSupportStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partialFourierHermitianBlock_hasCompactSupport : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → (∀ y : E, algebraMap F E (Algebra.trace F E y) = y + star y) → ∀ f : Hn r F E → ℂ, IsTest f → (∃ U ∈ 𝓝 (0 : Hn r F E), ∀ X : Hn r F E, ∀ u ∈ U, f (X + u) = f X) → HasCompactSupport (fourU M ψ f) := by
  first | exact @GlobalTheory.fourU_hasCompactSupport | exact GlobalTheory.fourU_hasCompactSupport | (intros; apply GlobalTheory.fourU_hasCompactSupport <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PartialFourierHermitianBlockIsLocallyConstantStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partialFourierHermitianBlock_isLocallyConstant : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → (∀ y : E, algebraMap F E (Algebra.trace F E y) = y + star y) → ∀ f : Hn r F E → ℂ, IsTest f → (∃ U ∈ 𝓝 (0 : Hn r F E), ∀ X : Hn r F E, ∀ u ∈ U, f (X + u) = f X) → IsLocallyConstant (fourU M ψ f) := by
  first | exact @GlobalTheory.fourU_isLocallyConstant | exact GlobalTheory.fourU_isLocallyConstant | (intros; apply GlobalTheory.fourU_isLocallyConstant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PartialFourierHermitianBlockUnitIndicatorStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partialFourierHermitianBlock_unitIndicator : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → (∀ y : E, algebraMap F E (Algebra.trace F E y) = y + star y) → (∃ u : E, ‖u‖ ≤ 1 ∧ ‖Algebra.trace F E u‖ = 1) → fourU M ψ (unitU r F E) = unitU r F E := by
  first | exact @GlobalTheory.JR.FourUnit.fourU_unitU | exact GlobalTheory.JR.FourUnit.fourU_unitU | (intros; apply GlobalTheory.JR.FourUnit.fourU_unitU <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodDataComparisonStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_data_comparison : ∀ {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL] {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] (ρ : Representation LL G V) {n : ℕ} (e : Module.Basis (Fin n) Qp V) (W W' : Matrix (Fin n) (Fin n) BdR), W * W' = 1 → (∀ i j, W i j ∈ PD.Fil 0) → (∀ i j, W' i j ∈ PD.Fil 0) → (∀ g, (Matrix.of fun i j => algebraMap Qp BdR (e.repr (ρ g (e j)) i)) * W.map (PD.actdR g) = W) → ∀ (τ : K →ₐ[Qp] LL) (a : ℤ), Formalism.WeaklyAdmissibleFiltrations.IsJumpV PD ρ τ a → a = 0 := by
  first | exact @GlobalTheory.SplitJump.jump_eq_zero | exact GlobalTheory.SplitJump.jump_eq_zero | (intros; apply GlobalTheory.SplitJump.jump_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiGammaModuleSaturationTheoremStatement
section
open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.phiGammaModule_saturation_theorem : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {n : ℕ} [NeZero n] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] {W : Type} [AddCommGroup W] [Module k⸨X⸩ W] [Module k⟦X⟧ W] [Module k W] [IsScalarTower k⟦X⟧ k⸨X⸩ W] [IsScalarTower k k⸨X⸩ W] [IsScalarTower k k⟦X⟧ W] [FiniteDimensional k⸨X⸩ W] (D : ModPG R n V) (D' : ModPG R n W) (f : ZMod n → W →ₗ[k⸨X⸩] V), (∀ i, Function.Injective (f i)) → (∀ i x, f i (D'.φ i x) = D.φ i (f (i - 1) x)) → (∀ i x, f i (D'.γ i x) = D.γ i (f i x)) → ∀ (w w' : ZMod n → ℤ) (N : ZMod n → Submodule k⟦X⟧ V), (∀ i, IsLat (N i)) → CondAB D.φ w w' N → (∀ i, CondC (D.γ i) (N i)) → let N' := fun i => (N i).comap ((f i).restrictScalars k⟦X⟧); (∀ i, IsLat (N' i)) ∧ CondAB D'.φ w w' N' ∧ ∀ i, CondC (D'.γ i) (N' i) := by
  first | exact @GlobalTheory.PhiGam.Sat.main | exact GlobalTheory.PhiGam.Sat.main | (intros; apply GlobalTheory.PhiGam.Sat.main <;> assumption)
end

