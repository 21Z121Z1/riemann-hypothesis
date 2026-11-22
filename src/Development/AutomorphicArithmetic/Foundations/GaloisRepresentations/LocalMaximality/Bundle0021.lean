import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ResidueOfTraceIsFiberSum
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0395

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.POmLoc
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

section OmLocAux
variable {L : Type} [Field L] [Algebra ℂ L]

private noncomputable def om1 (B : Subalgebra ℂ L) : Submodule ℂ Ω[L⁄ℂ] :=
  Submodule.span ℂ {w | ∃ b ∈ B, ∃ u ∈ B, w = b • D ℂ L u}

private lemma omB_stab (B : Subalgebra ℂ L) (q : ℕ) {r : L} (hr : r ∈ B) {m : DR ℂ L}
    (hm : m ∈ omB ℂ L B q) : r • m ∈ omB ℂ L B q := by
  have h : omB ℂ L B q ≤ (omB ℂ L B q).comap (Algebra.lsmul ℂ ℂ (DR ℂ L) r) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨b, hb, v, hv, rfl⟩
    refine Submodule.subset_span ⟨r * b, B.mul_mem hr hb, v, hv, ?_⟩
    simp [mul_smul]
  exact h hm

private lemma omB_mono {B B' : Subalgebra ℂ L} (h : B ≤ B') (q : ℕ) : omB ℂ L B q ≤ omB ℂ L B' q := by
  refine Submodule.span_mono ?_
  rintro _ ⟨b, hb, v, hv, rfl⟩
  exact ⟨b, h hb, v, fun j => h (hv j), rfl⟩

private lemma ι_mul_mem (B : Subalgebra ℂ L) (q : ℕ) {w : Ω[L⁄ℂ]} (hw : w ∈ om1 B) {y : DR ℂ L}
    (hy : y ∈ omB ℂ L B q) : ExteriorAlgebra.ι L w * y ∈ omB ℂ L B (q + 1) := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨b, hb, u, hu, rfl⟩ := hw
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨c, hc, v, hv, rfl⟩ := hy
      refine Submodule.subset_span ⟨b * c, B.mul_mem hb hc, Fin.cons u v, fun j => ?_, ?_⟩
      · exact Fin.cases hu hv j
      · rw [ExteriorAlgebra.ιMulti_succ_apply]
        simp [Matrix.vecTail, mul_smul, Function.comp_def, smul_comm b c]
    | zero => simp
    | add a a' _ _ h h' => rw [mul_add]; exact Submodule.add_mem _ h h'
    | smul t a _ h => rw [mul_smul_comm]; exact Submodule.smul_mem _ t h
  | zero => simp
  | add a a' _ _ h h' => rw [map_add, add_mul]; exact Submodule.add_mem _ h h'
  | smul t a _ h => rw [LinearMap.map_smul_of_tower, smul_mul_assoc]; exact Submodule.smul_mem _ t h

private lemma ιMulti_mem (B : Subalgebra ℂ L) (q : ℕ) (w : Fin q → Ω[L⁄ℂ]) (hw : ∀ j, w j ∈ om1 B) :
    ExteriorAlgebra.ιMulti L q w ∈ omB ℂ L B q := by
  induction q with
  | zero =>
    refine Submodule.subset_span ⟨1, B.one_mem, Fin.elim0, fun j => j.elim0, ?_⟩
    rw [one_smul]
    exact congrArg _ (Subsingleton.elim _ _)
  | succ q ih =>
    rw [ExteriorAlgebra.ιMulti_succ_apply]
    exact ι_mul_mem B q (hw 0) (ih _ fun j => hw _)

private lemma two_mem (B : Subalgebra ℂ L) {b v : L} (hb : b ∈ B) (hv : b * v ∈ B) :
    (b ^ 2) • D ℂ L v ∈ om1 B := by
  have h : (b ^ 2) • D ℂ L v = b • D ℂ L (b * v) - (b * v) • D ℂ L b := by
    rw [Derivation.leibniz, smul_add, smul_smul, smul_smul, pow_two, mul_comm b v]
    abel
  rw [h]
  exact Submodule.sub_mem _ (Submodule.subset_span ⟨b, hb, _, hv, rfl⟩)
    (Submodule.subset_span ⟨_, hv, b, hb, rfl⟩)

private lemma common_den (B : Subalgebra ℂ L) (e : B →ₐ[ℂ] ℂ) {q : ℕ} {c : L} {v : Fin q → L}
    (hc : c ∈ loc B e) (hv : ∀ j, v j ∈ loc B e) :
    ∃ b : B, e b ≠ 0 ∧ (b : L) * c ∈ B ∧ ∀ j, (b : L) * v j ∈ B := by
  obtain ⟨b0, h0, hc'⟩ := hc
  choose f hf hf' using hv
  refine ⟨b0 * ∏ j, f j, ?_, ?_, fun j => ?_⟩
  · rw [map_mul, map_prod]
    exact mul_ne_zero h0 (Finset.prod_ne_zero_iff.2 fun j _ => hf j)
  · have h := B.mul_mem (∏ j, f j).2 hc'
    convert h using 1
    push_cast
    ring
  · have h := B.mul_mem (b0 * ∏ i ∈ Finset.univ.erase j, f i).2 (hf' j)
    rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ j)]
    convert h using 1
    push_cast
    ring

end OmLocAux

theorem UpperTheory.Gal.productCup_of_system.omLoc_of :
    OmLoc := by
  intro L _ _ B e q
  have hle : B ≤ loc B e := fun v hv => ⟨1, by simp, by simpa using hv⟩
  refine ⟨le_antisymm ?_ ?_, fun r hr m hm => omB_stab B q hr hm, fun B' h => omB_mono h q⟩
  · refine Submodule.span_le.2 ?_
    rintro v ⟨b, hb, hv⟩
    have hb0 : (b : L) ≠ 0 := fun h => hb (by rw [show b = 0 from Subtype.ext h, map_zero])
    have hinv : (b : L)⁻¹ ∈ loc B e := ⟨b, hb, by rw [mul_inv_cancel₀ hb0]; exact B.one_mem⟩
    have h := omB_stab (loc B e) q hinv (omB_mono hle q hv)
    rwa [smul_smul, inv_mul_cancel₀ hb0, one_smul] at h
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨c, hc, v, hv, rfl⟩
    obtain ⟨b, hb, hbc, hbv⟩ := common_den B e hc hv
    refine Submodule.subset_span ⟨b ^ (2 * q + 1), by rw [map_pow]; exact pow_ne_zero _ hb, ?_⟩
    have h1 := ιMulti_mem B q (fun j => ((b : L) ^ 2) • D ℂ L (v j)) fun j => two_mem B b.2 (hbv j)
    have h2 := omB_stab B q hbc h1
    rw [AlternatingMap.map_smul_univ, smul_smul, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] at h2
    convert h2 using 1
    rw [smul_smul]
    congr 1
    push_cast
    ring
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PResVal
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

section ResValAux
variable {F K : Type} [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] {d : ℕ}

private noncomputable def mono (x : Fin (d + 1) → F) (a : Fin d → ℕ) : F := ∏ l, (x l.succ / x 0) ^ a l

private lemma mono_zero (x : Fin (d + 1) → F) : mono x 0 = 1 := by simp [mono]

private lemma mono_add (x : Fin (d + 1) → F) (a b : Fin d → ℕ) : mono x (a + b) = mono x a * mono x b := by
  simp [mono, pow_add, Finset.prod_mul_distrib]

private lemma mono_closure (x : Fin (d + 1) → F) (hx : x 0 ≠ 0) (y : F)
    (hy : y ∈ Submonoid.closure {y | ∃ i ∈ ({0} : Finset (Fin (d + 1))), ∃ j, y = x j / x i}) :
    ∃ a, y = mono x a := by
  induction hy using Submonoid.closure_induction with
  | mem z hz =>
    obtain ⟨i, hi, j, rfl⟩ := hz
    rw [Finset.mem_singleton] at hi
    subst hi
    cases j using Fin.cases with
    | zero => exact ⟨0, by rw [mono_zero, div_self hx]⟩
    | succ l =>
      refine ⟨Pi.single l 1, ?_⟩
      simp only [mono]
      rw [Finset.prod_eq_single l]
      · simp
      · intro b _ hb
        simp [Pi.single_apply, hb]
      · simp
  | one => exact ⟨0, (mono_zero x).symm⟩
  | mul y z _ _ hy hz =>
    obtain ⟨a, rfl⟩ := hy
    obtain ⟨b, rfl⟩ := hz
    exact ⟨a + b, (mono_add x a b).symm⟩

private lemma rho_mono (x : Fin (d + 1) → F) (hx : x 0 ≠ 0) (ρ : F →ₗ[ℂ] ℂ) (hρ : IsRes ℂ x ρ) (a : Fin d → ℕ)
    (ha : a ≠ 0) : ρ (mono x a) = 0 := by
  obtain ⟨_, hρ2⟩ := hρ
  set m : Fin (d + 1) → ℤ := Fin.cons (-(∑ l, (a l : ℤ))) (fun l => (a l : ℤ)) with hm
  have hsum : ∑ j, m j = 0 := by
    rw [Fin.sum_univ_succ]
    simp [hm]
  have hne : m ≠ 0 := by
    intro h
    apply ha
    funext l
    simpa [hm] using congrFun h l.succ
  have heq : mono x a = ∏ j, x j ^ m j := by
    rw [Fin.prod_univ_succ]
    simp only [hm, Fin.cons_zero, Fin.cons_succ, zpow_natCast, zpow_neg, mono, div_pow,
      Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum]
    rw [show (∑ l, (a l : ℤ)) = ((∑ l, a l : ℕ) : ℤ) by push_cast; rfl, zpow_natCast]
    ring
  rw [heq]
  exact hρ2 m hsum hne

end ResValAux

theorem UpperTheory.Gal.productCup_of_system.resVal_of :
    ValBasic → ResVal := by
  intro hval F K _ _ _ _ _ _ d x hfc ρ hρ e f hf
  obtain ⟨_, _, hBval, _⟩ := hval K (rB ℂ K (xv x) {0}) e.1
  have hx0 : xv x 0 ≠ 0 := (x 0).ne_zero
  have hmemB : ∀ g ∈ rA ℂ (xv x) {0}, algebraMap F K g ∈ rB ℂ K (xv x) {0} := by
    intro g hg
    exact (isIntegral_algebraMap : IsIntegral (rA ℂ (xv x) {0}) (algebraMap (rA ℂ (xv x) {0}) K ⟨g, hg⟩))
  have hspan : ∀ g, g ∈ rA ℂ (xv x) {0} ↔ g ∈ Submodule.span ℂ
      (Submonoid.closure {y | ∃ i ∈ ({0} : Finset (Fin (d + 1))), ∃ j, y = xv x j / xv x i} : Set F) := by
    intro g
    rw [← Algebra.adjoin_eq_span]
    rfl
  have hmono : ∀ (a : Fin d → ℕ) (h : algebraMap F K (mono (xv x) a) ∈ rB ℂ K (xv x) {0}),
      e.1 ⟨_, h⟩ = ρ (mono (xv x) a) := by
    intro a h
    by_cases ha : a = 0
    · subst ha
      have h1 : (⟨algebraMap F K (mono (xv x) 0), h⟩ : rB ℂ K (xv x) {0}) = 1 :=
        Subtype.ext (by simp [mono_zero])
      rw [h1, map_one, mono_zero, hρ.1]
    · rw [rho_mono (xv x) hx0 ρ hρ a ha]
      have h1 : (⟨algebraMap F K (mono (xv x) a), h⟩ : rB ℂ K (xv x) {0}) =
          ∏ l, (⟨algebraMap F K (xv x l.succ / xv x 0), tco_mem ℂ K (xv x) l⟩ : rB ℂ K (xv x) {0}) ^ a l :=
        Subtype.ext (by simp [mono, map_prod, map_pow])
      rw [h1, map_prod]
      obtain ⟨l, hl⟩ : ∃ l, a l ≠ 0 := by
        by_contra hc
        push_neg at hc
        exact ha (funext hc)
      exact Finset.prod_eq_zero (Finset.mem_univ l) (by rw [map_pow, e.2 l, zero_pow hl])
  have key : ∀ g (hg : g ∈ Submodule.span ℂ
      (Submonoid.closure {y | ∃ i ∈ ({0} : Finset (Fin (d + 1))), ∃ j, y = xv x j / xv x i} : Set F))
      (h : algebraMap F K g ∈ rB ℂ K (xv x) {0}), e.1 ⟨_, h⟩ = ρ g := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem y hy =>
      intro h
      obtain ⟨a, rfl⟩ := mono_closure (xv x) hx0 y hy
      exact hmono a h
    | zero =>
      intro h
      have h1 : (⟨algebraMap F K 0, h⟩ : rB ℂ K (xv x) {0}) = 0 := Subtype.ext (map_zero _)
      rw [h1, map_zero, map_zero]
    | add y z hy hz ihy ihz =>
      intro h
      have hy' := hmemB y ((hspan y).2 hy)
      have hz' := hmemB z ((hspan z).2 hz)
      have h1 : (⟨algebraMap F K (y + z), h⟩ : rB ℂ K (xv x) {0}) = ⟨_, hy'⟩ + ⟨_, hz'⟩ :=
        Subtype.ext (map_add _ _ _)
      rw [h1, map_add, map_add, ihy hy', ihz hz']
    | smul r y hy ihy =>
      intro h
      have hy' := hmemB y ((hspan y).2 hy)
      have h1 : (⟨algebraMap F K (r • y), h⟩ : rB ℂ K (xv x) {0}) = r • ⟨_, hy'⟩ := by
        apply Subtype.ext
        show algebraMap F K (r • y) = r • algebraMap F K y
        rw [Algebra.smul_def, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply]
      rw [h1, map_smul, map_smul, ihy hy']
  have hfB := hmemB f hf
  have hv := hBval ⟨_, hfB⟩
  rw [key f ((hspan f).1 hf) hfB] at hv
  exact hv
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PTrVal
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

noncomputable section

namespace UpperTheory.Gal.productCup_of_system.PartialTraceValue

private theorem nakGen {A B : Type} [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B] (I : Ideal A) (𝔟 : Ideal B)
    (hb : 𝔟 ⊔ I.map (algebraMap A B) = ⊤) : ∃ r : A, r - 1 ∈ I ∧ algebraMap A B r ∈ 𝔟 := by
  let N : Submodule A B := 𝔟.restrictScalars A
  have key : ∀ j ∈ I.map (algebraMap A B), ∀ b : B,
      (Submodule.Quotient.mk (j * b) : B ⧸ N) ∈ I • (⊤ : Submodule A (B ⧸ N)) := by
    intro j hj
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hj
    · rintro _ ⟨i, hi, rfl⟩ b
      rw [← Algebra.smul_def, Submodule.Quotient.mk_smul]
      exact Submodule.smul_mem_smul hi Submodule.mem_top
    · intro b
      rw [zero_mul]
      exact Submodule.zero_mem _
    · intro u v _ _ hu hv b
      rw [add_mul, Submodule.Quotient.mk_add]
      exact Submodule.add_mem _ (hu b) (hv b)
    · intro c u _ hu b
      rw [smul_eq_mul, show c * u * b = u * (c * b) by ring]
      exact hu _
  have hin : (⊤ : Submodule A (B ⧸ N)) ≤ I • ⊤ := by
    rintro q -
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨a, ha, j, hj, haj⟩ := Submodule.mem_sup.1 (hb ▸ Submodule.mem_top : (1 : B) ∈ 𝔟 ⊔ I.map (algebraMap A B))
    have : (Submodule.Quotient.mk b : B ⧸ N) = Submodule.Quotient.mk (j * b) := by
      rw [Submodule.Quotient.eq]
      have : b - j * b = a * b := by
        linear_combination (-b) * haj
      rw [this]
      exact 𝔟.mul_mem_right b ha
    rw [this]
    exact key j hj b
  obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I
    (⊤ : Submodule A (B ⧸ N)) Module.Finite.fg_top hin
  refine ⟨r, hr1, ?_⟩
  have h0 := hr (Submodule.Quotient.mk 1) Submodule.mem_top
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Algebra.smul_def, mul_one] at h0
  exact h0

private theorem nakHom {A B : Type} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B] [Algebra.FiniteType ℂ B]
    (φ : A →ₐ[ℂ] B) (hint : ∀ b : B, φ.toRingHom.IsIntegralElem b) (I : Ideal A) (𝔟 : Ideal B)
    (hb : 𝔟 ⊔ I.map φ.toRingHom = ⊤) : ∃ r : A, r - 1 ∈ I ∧ φ r ∈ 𝔟 := by
  letI alg : Algebra A B := φ.toRingHom.toAlgebra
  haveI tow : IsScalarTower ℂ A B := IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
  haveI int : Algebra.IsIntegral A B := ⟨hint⟩
  haveI : Algebra.FiniteType A B := Algebra.FiniteType.of_restrictScalars_finiteType ℂ _ _
  haveI fin : Module.Finite A B := Algebra.IsIntegral.finite
  exact nakGen I 𝔟 hb

variable {F L : Type} [Field F] [Field L] [Algebra ℂ F] [Algebra ℂ L] [Algebra F L] [IsScalarTower ℂ F L]
  {d : ℕ} (x : Fin (d + 1) → F)

private def tA (j : Fin d) : rA ℂ x {0} :=
  ⟨x j.succ / x 0, Algebra.subset_adjoin ⟨0, Finset.mem_singleton_self 0, j.succ, rfl⟩⟩

private def IA : Ideal (rA ℂ x {0}) := Ideal.span (Set.range (tA x))

private theorem val_one (φ : rA ℂ x {0} →ₐ[ℂ] ℂ) (hφ : ∀ j, φ (tA x j) = 0) {r : rA ℂ x {0}}
    (hr : r - 1 ∈ IA x) : φ r = 1 := by
  have hle : IA x ≤ RingHom.ker φ := by
    rw [IA, Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    exact hφ j
  have := hle hr
  rw [RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at this
  exact this

private theorem nak (h : IsFinCover ℂ L x) (𝔟 : Ideal (rB ℂ L x {0}))
    (hb : 𝔟 ⊔ FibFin.coordIdeal ℂ L x = ⊤) :
    ∃ r : rA ℂ x {0}, r - 1 ∈ IA x ∧ FibFin.incl ℂ L x r ∈ 𝔟 := by
  haveI := h.smooth 0
  have hcomp : (rB ℂ L x {0}).val.toRingHom.comp (FibFin.incl ℂ L x).toRingHom =
      algebraMap (rA ℂ x {0}) L := RingHom.ext fun a => rfl
  have hint : ∀ b : rB ℂ L x {0}, (FibFin.incl ℂ L x).toRingHom.IsIntegralElem b := fun b => by
    obtain ⟨p, hpm, hp⟩ : IsIntegral (rA ℂ x {0}) (b : L) := b.2
    refine ⟨p, hpm, ?_⟩
    apply Subtype.ext
    change (rB ℂ L x {0}).val.toRingHom (Polynomial.eval₂ (FibFin.incl ℂ L x).toRingHom b p) = (0 : L)
    rw [Polynomial.hom_eval₂, hcomp]
    exact hp
  have hJ : FibFin.coordIdeal ℂ L x ≤ (IA x).map (FibFin.incl ℂ L x).toRingHom := by
    rw [FibFin.coordIdeal, Ideal.span_le]
    rintro _ ⟨l, rfl⟩
    change (FibFin.incl ℂ L x).toRingHom (tA x l) ∈ _
    exact Ideal.mem_map_of_mem _ (Ideal.subset_span (Set.mem_range_self l))
  exact nakHom (FibFin.incl ℂ L x) hint (IA x) 𝔟 (top_le_iff.1 (hb ▸ sup_le_sup_left hJ 𝔟))

private theorem fib_nonempty (h : IsFinCover ℂ L x)
    (hred : IsReduced (rB ℂ L x {0} ⧸ FibFin.coordIdeal ℂ L x)) : Nonempty (fib ℂ L x) := by
  by_contra hne
  have hall := (FibFin.fib_finite_and_sep ℂ L x h hred).2 1 (fun e => (hne ⟨e⟩).elim)
  have ht : FibFin.coordIdeal ℂ L x = ⊤ := (Ideal.eq_top_iff_one _).2 hall
  obtain ⟨r, hr1, hr⟩ := nak x h ⊥ (by rw [ht]; simp)
  have hr0 : r = 0 := by
    have h0 : algebraMap F L (r : F) = 0 := congrArg Subtype.val ((Ideal.mem_bot).1 hr)
    exact Subtype.ext ((map_eq_zero _).1 h0)
  obtain ⟨e, he⟩ := rA_single_polyEquiv ℂ F d x h.pd 0
  have hε : ((MvPolynomial.aeval (0 : Fin d → ℂ)).comp e.symm.toAlgHom) r = 1 := by
    refine val_one x _ (fun j => ?_) hr1
    have htj : tA x j = e (MvPolynomial.X j) := Subtype.ext (by rw [he j, Fin.succAbove_zero]; rfl)
    rw [htj]
    simp
  rw [hr0, map_zero] at hε
  exact zero_ne_one hε

private theorem comax (h : IsFinCover ℂ L x)
    (hred : IsReduced (rB ℂ L x {0} ⧸ FibFin.coordIdeal ℂ L x))
    (hCRT : ∀ v : fib ℂ L x → ℂ, ∃ b : rB ℂ L x {0}, ∀ e : fib ℂ L x, e.1 b = v e)
    (𝔞 : Ideal (rB ℂ L x {0})) (h𝔞 : ∀ e : fib ℂ L x, ∃ b ∈ 𝔞, e.1 b ≠ 0) :
    𝔞 ⊔ FibFin.coordIdeal ℂ L x = ⊤ := by
  obtain ⟨hfin, hsep⟩ := FibFin.fib_finite_and_sep ℂ L x h hred
  haveI := Fintype.ofFinite (fib ℂ L x)
  classical
  choose b hb hb0 using h𝔞
  choose c hc using fun e0 : fib ℂ L x => hCRT (fun e => if e = e0 then (e0.1 (b e0))⁻¹ else 0)
  have hs : (∑ e0, c e0 * b e0) ∈ 𝔞 := Ideal.sum_mem _ fun e0 _ => 𝔞.mul_mem_left _ (hb e0)
  have hval : ∀ e : fib ℂ L x, e.1 (∑ e0, c e0 * b e0) = 1 := by
    intro e
    rw [map_sum, Finset.sum_eq_single e (fun e0 _ hne => by rw [map_mul, hc, if_neg (Ne.symm hne), zero_mul])
      (fun hn => (hn (Finset.mem_univ e)).elim), map_mul, hc, if_pos rfl]
    exact inv_mul_cancel₀ (hb0 e)
  have h1 := hsep (1 - ∑ e0, c e0 * b e0) (fun e => by rw [map_sub, map_one, hval, sub_self])
  rw [Ideal.eq_top_iff_one]
  exact Submodule.mem_sup.2 ⟨_, hs, _, h1, by ring⟩

private theorem partialTrace_valuation_sum (h : IsFinCover ℂ L x)
    (hred : IsReduced (rB ℂ L x {0} ⧸ FibFin.coordIdeal ℂ L x)) (ρ : F →ₗ[ℂ] ℂ)
    (hRT : ∀ b : rB ℂ L x {0}, ρ (Algebra.trace F L b) = ∑ᶠ e : fib ℂ L x, e.1 b)
    (hRes : ∀ e : fib ℂ L x, ∀ f ∈ rA ℂ x {0}, Val (rB ℂ L x {0}) e.1 (algebraMap F L f) (ρ f))
    (hCRT : ∀ v : fib ℂ L x → ℂ, ∃ b : rB ℂ L x {0}, ∀ e : fib ℂ L x, e.1 b = v e)
    (g : L) (γ : fib ℂ L x → ℂ) (hg : ∀ e : fib ℂ L x, Val (rB ℂ L x {0}) e.1 g (γ e))
    (ht : Algebra.trace F L g ∈ rA ℂ x {0}) :
    ρ (Algebra.trace F L g) = ∑ᶠ e, γ e := by
  let 𝔞 : Ideal (rB ℂ L x {0}) :=
    { carrier := {b | (b : L) * g ∈ rB ℂ L x {0}}
      add_mem' := by
        intro a b ha hb
        have := (rB ℂ L x {0}).add_mem ha hb
        simpa [add_mul] using this
      zero_mem' := by simpa using (rB ℂ L x {0}).zero_mem
      smul_mem' := by
        intro c b hb
        have := (rB ℂ L x {0}).mul_mem c.2 hb
        simpa [mul_assoc] using this }
  have h𝔞 : ∀ e : fib ℂ L x, ∃ b ∈ 𝔞, e.1 b ≠ 0 := fun e => by
    obtain ⟨b, hb, hbv, hne, -⟩ := hg e
    exact ⟨⟨b, hb⟩, hbv, hne⟩
  obtain ⟨s, hs1, hs⟩ := nak x h 𝔞 (comax x h hred hCRT 𝔞 h𝔞)
  have hs' : algebraMap F L (s : F) * g ∈ rB ℂ L x {0} := hs
  have hone : ∀ e : fib ℂ L x, e.1 (FibFin.incl ℂ L x s) = 1 := fun e =>
    val_one x (e.1.comp (FibFin.incl ℂ L x)) (fun j => e.2 j) hs1
  have hval : ∀ e : fib ℂ L x, e.1 ⟨_, hs'⟩ = γ e := by
    intro e
    obtain ⟨b, hb, hbv, hne, heq⟩ := hg e
    have h1 : (⟨b, hb⟩ : rB ℂ L x {0}) * ⟨_, hs'⟩ = FibFin.incl ℂ L x s * ⟨b * g, hbv⟩ := by
      apply Subtype.ext
      change b * (algebraMap F L (s : F) * g) = algebraMap F L (s : F) * (b * g)
      ring
    have h2 := congrArg e.1 h1
    rw [map_mul, map_mul, hone, one_mul, heq] at h2
    exact mul_left_cancel₀ hne h2
  obtain ⟨e0⟩ := fib_nonempty x h hred
  have hev : ∀ f : rA ℂ x {0}, e0.1 (FibFin.incl ℂ L x f) = ρ f := by
    intro f
    obtain ⟨b, hb, hbv, hne, heq⟩ := hRes e0 f f.2
    have h1 : (⟨b * algebraMap F L f, hbv⟩ : rB ℂ L x {0}) = ⟨b, hb⟩ * FibFin.incl ℂ L x f := rfl
    rw [h1, map_mul] at heq
    exact mul_left_cancel₀ hne heq
  have htr : Algebra.trace F L (algebraMap F L (s : F) * g) = (s : F) * Algebra.trace F L g := by
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  have h3 : ρ ((s : F) * Algebra.trace F L g) = ρ (Algebra.trace F L g) := by
    have h4 := hev (s * ⟨_, ht⟩)
    rw [map_mul, map_mul, hone e0, one_mul, hev] at h4
    exact h4.symm
  rw [← h3, ← htr]
  exact (hRT ⟨_, hs'⟩).trans (finsum_congr hval)

end UpperTheory.Gal.productCup_of_system.PartialTraceValue

end

theorem UpperTheory.Gal.productCup_of_system.trVal_of :
    ResidueOfTraceIsFiberSum → ResVal → CRT → ValBasic → TrVal := by
  intro hRT hRes hCRT _ F L _ _ _ _ _ _ d x hc hred ρ hρ g γ hg ht
  exact PartialTraceValue.partialTrace_valuation_sum (xv x) hc hred ρ (hRT F L d x hc hred ρ hρ)
    (fun e f hf => hRes F L d x hc ρ hρ e f hf) (hCRT F L d x hc).2 g γ hg ht
end

