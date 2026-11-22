import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0006
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0016
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0013

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.GaGram
section
noncomputable section

namespace PositivityTheory.HtPt.Ga

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

section

variable {E : Type} [Field E] [NumberField E] {N : ℕ}

def vb (E : Type) [Field E] [NumberField E] {N : ℕ}
    (q : Fin N × Module.Free.ChooseBasisIndex ℤ (𝓞 E)) : Fin N → 𝓞 E :=
  Pi.single q.1 (RingOfIntegers.basis E q.2)

theorem exists_left_inv {B : Type} [CommRing B] {n : ℕ} (φ : ZMod n →+* B) (c : 𝓞 E ≃+* 𝓞 E)
    (hc : ∀ a, c (c a) = a) (e : (Fin N → 𝓞 E) →+ (Fin N → 𝓞 E) →+ ZMod n)
    (adj : ∀ (a : 𝓞 E) (x y : Fin N → 𝓞 E), e (a • x) y = e x (c a • y))
    (surj : ∀ f : (Fin N → 𝓞 E) →+ ZMod n, ∃ x, e x = f)
    (s : 𝓞 E →+* B) (cc u : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → B) (hu : ∑ k, u k * cc k = 1)
    (hcc : ∀ (a : 𝓞 E) l, ∑ k, cc k *
      (((RingOfIntegers.basis E).repr (a * RingOfIntegers.basis E k) l : ℤ) : B) = s a * cc l) :
    ∃ β : Matrix (Fin N) (Fin N) B, ∀ j₀ j, ∑ i, β j₀ i *
      (∑ k, cc k * φ (e (Pi.single i (RingOfIntegers.basis E k)) (Pi.single j 1))) =
        if j₀ = j then 1 else 0 := by
  classical
  set b := RingOfIntegers.basis E with hb
  let Λ : (Fin N → 𝓞 E) → (Fin N → 𝓞 E) → B := fun x y => ∑ k, cc k * φ (e (b k • x) y)
  have Λadd : ∀ x x' y, Λ (x + x') y = Λ x y + Λ x' y := by
    intro x x' y
    simp only [Λ, smul_add, map_add, AddMonoidHom.add_apply, mul_add, Finset.sum_add_distrib]
  have Λsmul : ∀ (a : 𝓞 E) x y, Λ (a • x) y = s a * Λ x y := by
    intro a x y
    have h1 : ∀ k, b k • a • x = ∑ l, (b.repr (a * b k) l) • (b l • x) := by
      intro k
      rw [smul_smul, mul_comm]
      conv_lhs => rw [← b.sum_repr (a * b k)]
      rw [Finset.sum_smul]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [smul_assoc]
    have h2 : ∀ k, φ (e (b k • a • x) y) = ∑ l, ((b.repr (a * b k) l : ℤ) : B) * φ (e (b l • x) y) := by
      intro k
      rw [h1, map_sum, AddMonoidHom.finset_sum_apply, map_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_zsmul, AddMonoidHom.zsmul_apply, map_zsmul, zsmul_eq_mul]
    simp only [Λ, h2, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← mul_assoc, ← hcc a l, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  let Λh : (Fin N → 𝓞 E) → (Fin N → 𝓞 E) →+ B := fun y =>
    AddMonoidHom.mk' (fun x => Λ x y) (fun x x' => Λadd x x' y)
  have hdec : ∀ x y, Λ x y = ∑ i, s (x i) * Λ (Pi.single i 1) y := by
    intro x y
    have hx : x = ∑ i, x i • (Pi.single i 1 : Fin N → 𝓞 E) := by
      conv_lhs => rw [← Finset.univ_sum_single x]
      refine Finset.sum_congr rfl fun i _ => ?_
      funext j
      simp [Pi.single_apply]
    have := congrArg (Λh y) hx
    rw [map_sum] at this
    simpa [Λh, Λsmul] using this
  let f : Fin N × Module.Free.ChooseBasisIndex ℤ (𝓞 E) → (Fin N → 𝓞 E) →+ ZMod n := fun q =>
    AddMonoidHom.mk' (fun y => ((b.repr (c (y q.1)) q.2 : ℤ) : ZMod n)) (by
      intro y y'
      simp only [Pi.add_apply, map_add, Finsupp.add_apply, Int.cast_add])
  choose x hx using fun q => surj (f q)
  have hΛx : ∀ j₀ l j, Λ (x (j₀, l)) (Pi.single j 1) = if j₀ = j then cc l else 0 := by
    intro j₀ l j
    have hk : ∀ k, e (b k • x (j₀, l)) (Pi.single j 1) =
        ((b.repr (c ((Pi.single j (c (b k)) : Fin N → 𝓞 E) j₀)) l : ℤ) : ZMod n) := by
      intro k
      rw [adj, hx]
      have : (c (b k) • (Pi.single j 1 : Fin N → 𝓞 E)) = Pi.single j (c (b k)) := by
        funext i
        simp [Pi.single_apply]
      rw [this]
      rfl
    simp only [Λ, hk]
    split_ifs with hj
    · subst hj
      simp only [Pi.single_eq_same, hc, Basis.repr_self, Finsupp.single_apply]
      simp
    · simp [Pi.single_apply, hj]
  refine ⟨Matrix.of fun j₀ i => ∑ l, u l * s (x (j₀, l) i), ?_⟩
  intro j₀ j
  have hΓ : ∀ i, (∑ k, cc k * φ (e (Pi.single i (b k)) (Pi.single j 1))) = Λ (Pi.single i 1) (Pi.single j 1) := by
    intro i
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show (Pi.single i (b k) : Fin N → 𝓞 E) = b k • Pi.single i 1 from by
      funext i'
      simp [Pi.single_apply]]
  simp only [hΓ, Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  have : ∀ l, ∑ i, u l * s (x (j₀, l) i) * Λ (Pi.single i 1) (Pi.single j 1) = u l * (if j₀ = j then cc l else 0) := by
    intro l
    rw [← hΛx, hdec (x (j₀, l)), Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  simp only [this]
  split_ifs
  · simpa using hu
  · simp

end

theorem exists_of_map_eq_one {A : Type} [CommRing A] {N : ℕ} (t : A) (M : Matrix (Fin N) (Fin N) A)
    (h : (Ideal.Quotient.mk (Ideal.span {t})).mapMatrix M = 1) :
    ∃ Z : Matrix (Fin N) (Fin N) A, M = 1 + t • Z := by
  have hmem : ∀ i j, ∃ z : A, z * t = M i j - (1 : Matrix (Fin N) (Fin N) A) i j := by
    intro i j
    have h1 := congrFun (congrFun h i) j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply] at h1
    have h2 : Ideal.Quotient.mk (Ideal.span {t}) (M i j) =
        Ideal.Quotient.mk (Ideal.span {t}) ((1 : Matrix (Fin N) (Fin N) A) i j) := by
      rw [h1, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    exact Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 h2)
  choose Z hZ using hmem
  refine ⟨Matrix.of Z, ?_⟩
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
  rw [mul_comm, hZ]
  ring

theorem gram_unit : ∀ (A K : Type) [CommRing A] [Field K] [Algebra A K] [CharZero K] (hAK : Function.Injective (algebraMap A K)) (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (D : HTChart A K c p R N Ω) (σ : E →+* K) (d : A), (∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap A K).range) → GeneratesDiff σ d → ∃ G H Z Z' : Matrix (Fin N) (Fin N) A, (∀ i j, algebraMap A K (G i j) = D.gram σ d i j) ∧ G * H = 1 + ((p : A) ^ R) • Z ∧ H * G = 1 + ((p : A) ^ R) • Z' := by
  intro A K _ _ _ _ hAK E _ _ c hc p R N _ Ω _ _ _ _ D σ d hσ hd
  classical
  obtain ⟨-, hrange, u, hu⟩ := GlobalTheory.CompanionTheory.Ar.HT.different_generator_dualInt A K E σ d hAK hσ hd
  choose g hg using hrange
  set T := algebraMap A K with hT
  set b := RingOfIntegers.basis E with hb
  let Gm : Matrix (Fin N) (Fin N) A := Matrix.of fun i j =>
    ∑ k, g k * (((D.e (Pi.single i (b k)) (Pi.single j 1)).val : ℕ) : A)
  let I : Ideal A := Ideal.span {(p : A) ^ R}
  let mkB := Ideal.Quotient.mk I
  haveI : NeZero (p ^ R) := ⟨by have := (Fact.out : p.Prime).pos; positivity⟩
  have hzero : (Int.castRingHom (A ⧸ I)) ((p ^ R : ℕ) : ℤ) = 0 := by
    show ((((p ^ R : ℕ) : ℤ)) : A ⧸ I) = 0
    rw [Int.cast_natCast, Nat.cast_pow, ← map_natCast mkB, ← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
  let φ : ZMod (p ^ R) →+* A ⧸ I :=
    (Ideal.Quotient.lift (Ideal.span {((p ^ R : ℕ) : ℤ)}) (Int.castRingHom (A ⧸ I)) (by
      intro a ha
      obtain ⟨k, rfl⟩ := Ideal.mem_span_singleton'.1 ha
      rw [map_mul, hzero, mul_zero])).comp (Int.quotientSpanNatEquivZMod (p ^ R)).symm.toRingHom
  have hφ : ∀ z : ZMod (p ^ R), φ z = mkB ((z.val : ℕ) : A) := by
    intro z
    conv_lhs => rw [← ZMod.natCast_zmod_val z]
    rw [map_natCast, map_natCast]
  have hinj : Function.Injective T.rangeRestrict := fun x y h => hAK (by
    have := congrArg Subtype.val h
    simpa using this)
  let eA : A ≃+* T.range := RingEquiv.ofBijective T.rangeRestrict ⟨hinj, T.rangeRestrict_surjective⟩
  let σ' : 𝓞 E →+* T.range := (σ.comp (algebraMap (𝓞 E) E)).codRestrict T.range (fun a => hσ a)
  let ψ : 𝓞 E →+* A := eA.symm.toRingHom.comp σ'
  have hψ : ∀ a, T (ψ a) = σ a := by
    intro a
    have := congrArg Subtype.val (eA.apply_symm_apply (σ' a))
    exact this
  let s : 𝓞 E →+* A ⧸ I := mkB.comp ψ
  let cc : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → A ⧸ I := fun k => mkB (g k)
  let uB : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → A ⧸ I := fun k => mkB (u k)
  have hu' : ∑ k, uB k * cc k = 1 := by
    have : ∑ k, u k * g k = 1 := by
      apply hAK
      rw [map_sum, map_one, ← hu]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul, hg]
    simp only [uB, cc, ← map_mul, ← map_sum, this, map_one]
  have hcc : ∀ (a : 𝓞 E) l, ∑ k, cc k * (((b.repr (a * b k) l : ℤ)) : A ⧸ I) = s a * cc l := by
    intro a l
    have : ∑ k, g k * (((b.repr (a * b k) l : ℤ)) : A) = ψ a * g l := by
      apply hAK
      rw [map_sum, map_mul, hψ, hg, mul_left_comm, ← map_mul, GlobalTheory.CompanionTheory.Ar.HT.ProjEig.mul_dualInt_eq,
        map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul T, hg, map_mul σ, map_intCast σ, map_intCast T]
      ring
    simp only [cc, s, RingHom.comp_apply, ← map_intCast mkB, ← map_mul, ← map_sum, this]
  have hc' : ∀ a, RingOfIntegers.mapRingEquiv c (RingOfIntegers.mapRingEquiv c a) = a := by
    intro a
    apply RingOfIntegers.ext
    simp [hc]
  obtain ⟨β, hβ⟩ := exists_left_inv φ (RingOfIntegers.mapRingEquiv c) hc' D.e D.adj D.e_surj s cc uB hu' hcc
  have hΓ : mkB.mapMatrix Gm = Matrix.of fun i j =>
      ∑ k, cc k * φ (D.e (Pi.single i (b k)) (Pi.single j 1)) := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Gm, map_sum, map_mul, hφ, cc]
  have hβΓ : β * mkB.mapMatrix Gm = 1 := by
    rw [hΓ]
    ext j₀ j
    rw [Matrix.mul_apply, Matrix.one_apply]
    simpa only [Matrix.of_apply] using hβ j₀ j
  choose Hf hHf using fun ij : Fin N × Fin N => Ideal.Quotient.mk_surjective (I := I) (β ij.1 ij.2)
  let H : Matrix (Fin N) (Fin N) A := Matrix.of fun i j => Hf (i, j)
  have hH : mkB.mapMatrix H = β := by
    ext i j
    simp [H, hHf, mkB]
  obtain ⟨Z, hZ⟩ := exists_of_map_eq_one ((p : A) ^ R) (Gm * H) (by
    rw [map_mul, hH]
    exact mul_eq_one_comm.1 hβΓ)
  obtain ⟨Z', hZ'⟩ := exists_of_map_eq_one ((p : A) ^ R) (H * Gm) (by
    rw [map_mul, hH]
    exact hβΓ)
  refine ⟨Gm, H, Z, Z', ?_, hZ, hZ'⟩
  intro i j
  simp only [Gm, Matrix.of_apply, map_sum, map_mul, map_natCast, hg]
  unfold GlobalTheory.CompanionTheory.Ar.HT.HTChart.gram
  rfl

end PositivityTheory.HtPt.Ga
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.GaSurj
section
noncomputable section

namespace PositivityTheory.HtPt.Ga

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

section

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {E : Type} [Field E] [NumberField E]
  {c : E ≃+* E} {p R N : ℕ}
  {Ω : Type} [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω]
  (D : HTChart A K c p R N Ω)

theorem h_mem_om' (x : Fin N → 𝓞 E) : D.h x ∈ D.om' :=
  Submodule.mem_sup_left (Submodule.subset_span ⟨x, rfl⟩)

theorem proj_mem_omHT (σ : E →+* K) {y : Ω} (hy : y ∈ D.om') : eigProj D.ρΩ σ y ∈ D.omHT σ :=
  ⟨y, hy, rfl⟩

theorem q_mem (σ : E →+* K) (x : Fin N → A) : D.q σ x ∈ D.omHT σ := by
  unfold HTChart.q
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
  exact proj_mem_omHT D σ (h_mem_om' D _)

theorem q_add (σ : E →+* K) (x y : Fin N → A) : D.q σ (x + y) = D.q σ x + D.q σ y := by
  unfold HTChart.q
  simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem q_smul (σ : E →+* K) (a : A) (x : Fin N → A) : D.q σ (a • x) = a • D.q σ x := by
  unfold HTChart.q
  simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

private theorem toZMod_cycZ_eq_one_of_cycMod_eq_one (σ : E →+* K) (hσ : ∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap A K).range)
    (z : Fin N → 𝓞 E) :
    ∃ x : Fin N → A, ∃ y' ∈ D.om, eigProj D.ρΩ σ (D.h z) = D.q σ x + ((p : A) ^ R) • eigProj D.ρΩ σ y' := by
  choose y hy he using fun i => D.h_lin (z i) (Pi.single i 1)
  choose b hb using fun i => hσ (z i)
  have hz : z = ∑ i, z i • Pi.single i (1 : 𝓞 E) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have hrho : ∀ (a : 𝓞 E) (v : Ω), eigProj D.ρΩ σ (D.ρΩ a v) = σ (a : E) • eigProj D.ρΩ σ v := by
    intro a v
    have h1 := congrArg (fun f : Module.End K Ω => f v) (ProjEig.eigProj_mul_rho_comm D.ρΩ σ a)
    have h2 := congrArg (fun f : Module.End K Ω => f v) (ProjEig.rho_mul_eigProj D.ρΩ σ a)
    simp only [Module.End.mul_apply, LinearMap.smul_apply] at h1 h2
    rw [h1, h2]
  refine ⟨b, ∑ i, y i, Submodule.sum_mem _ fun i _ => hy i, ?_⟩
  conv_lhs => rw [hz]
  rw [map_sum, map_sum]
  simp only [he, map_add, hrho, ← hb, algebraMap_smul]
  rw [Finset.sum_add_distrib, map_sum, Finset.smul_sum]
  unfold HTChart.q
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_nsmul, ← Nat.cast_smul_eq_nsmul A]
  push_cast
  rfl

theorem exists_q_add (σ : E →+* K) (hσ : ∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap A K).range)
    {y : Ω} (hy : y ∈ D.om') :
    ∃ x : Fin N → A, ∃ y' ∈ D.om, eigProj D.ρΩ σ y = D.q σ x + ((p : A) ^ R) • eigProj D.ρΩ σ y' := by
  obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.mp hy
  obtain ⟨y0, hy0, rfl⟩ := Submodule.mem_map.mp ht
  clear hy ht
  have key : ∃ x : Fin N → A, ∃ y' ∈ D.om,
      eigProj D.ρΩ σ s = D.q σ x + ((p : A) ^ R) • eigProj D.ρΩ σ y' := by
    induction hs using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨z, rfl⟩ := hv
      exact toZMod_cycZ_eq_one_of_cycMod_eq_one D σ hσ z
    | zero => exact ⟨0, 0, D.om.zero_mem, by simp [HTChart.q]⟩
    | add u v _ _ hu hv =>
      obtain ⟨x1, y1, hy1, e1⟩ := hu
      obtain ⟨x2, y2, hy2, e2⟩ := hv
      refine ⟨x1 + x2, y1 + y2, D.om.add_mem hy1 hy2, ?_⟩
      rw [map_add, e1, e2, q_add, map_add, smul_add]
      abel
    | smul a v _ hv =>
      obtain ⟨x1, y1, hy1, e1⟩ := hv
      refine ⟨a • x1, a • y1, D.om.smul_mem a hy1, ?_⟩
      rw [LinearMap.map_smul_of_tower, e1, q_smul, LinearMap.map_smul_of_tower, smul_add, smul_comm a]
  obtain ⟨x, y', hy', e⟩ := key
  have ht0 : eigProj D.ρΩ σ (((p : A) ^ R • LinearMap.id : Ω →ₗ[A] Ω) y0)
      = ((p : A) ^ R) • eigProj D.ρΩ σ y0 := by
    simp [LinearMap.map_smul_of_tower]
  refine ⟨x, y' + y0, D.om.add_mem hy' hy0, ?_⟩
  rw [map_add, e, ht0, map_add, smul_add, add_assoc]

end

theorem q_surj : ∀ (A K : Type) [CommRing A] [Field K] [Algebra A K] [CharZero K] (hAK : Function.Injective (algebraMap A K)) (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (D : HTChart A K c p R N Ω) (κ : A) (σ : E →+* K) (m : ℕ), (∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap A K).range) → κ * (p : A) ^ m ∣ (p : A) ^ R → (∀ x ∈ D.om, κ • x ∈ D.om') → (∀ x, D.q σ x ∈ D.omHT σ) ∧ (D.omHT σ).FG ∧ ∀ y ∈ D.omHT σ, ∃ x : Fin N → A, ∃ y' ∈ D.omHT σ, y = D.q σ x + ((p : A) ^ m) • y' := by
  intro A K _ _ _ _ hAK E _ _ c hc p R N _ Ω _ _ _ _ D κ σ m hσ hdiv hκ
  classical
  refine ⟨fun x => q_mem D σ x, ?_, ?_⟩
  · unfold HTChart.omHT eigQuot
    apply Submodule.FG.map
    unfold HTChart.om'
    refine Submodule.FG.sup ?_ (Submodule.FG.map _ D.om_lat.fg)
    obtain ⟨T, hT⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℤ (Fin N → 𝓞 E)).FG)
    refine ⟨T.image D.h, le_antisymm ?_ ?_⟩
    · apply Submodule.span_mono
      intro v hv
      simp only [Finset.coe_image, Set.mem_image] at hv
      obtain ⟨z, _, rfl⟩ := hv
      exact ⟨z, rfl⟩
    · rw [Submodule.span_le]
      rintro _ ⟨z, rfl⟩
      have hz : z ∈ Submodule.span ℤ (T : Set (Fin N → 𝓞 E)) := hT ▸ Submodule.mem_top
      induction hz using Submodule.span_induction with
      | mem w hw =>
        exact Submodule.subset_span (by simp only [Finset.coe_image]; exact ⟨w, hw, rfl⟩)
      | zero => simp
      | add u v _ _ hu hv =>
        rw [map_add]
        exact Submodule.add_mem _ hu hv
      | smul n u _ hu =>
        rw [map_zsmul]
        exact zsmul_mem hu n
  · intro y hy
    simp only [HTChart.omHT, eigQuot] at hy
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hy
    obtain ⟨x, y'', hy'', e⟩ := exists_q_add D σ hσ hw
    obtain ⟨d, hd⟩ := hdiv
    refine ⟨x, d • eigProj D.ρΩ σ (κ • y''), ?_, ?_⟩
    · exact Submodule.smul_mem _ d (proj_mem_omHT D σ (hκ y'' hy''))
    · rw [LinearMap.restrictScalars_apply, e, hd, LinearMap.map_smul_of_tower]
      congr 1
      simp only [smul_smul]
      congr 1
      ring

end PositivityTheory.HtPt.Ga
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.GcBase
section
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

namespace PositivityTheory.HtPt.Gc

theorem isLocalizedModule_subtype {A K : Type} [CommRing A] [IsDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] {Ω : Type} [AddCommGroup Ω] [Module K Ω] [Module A Ω]
    [IsScalarTower A K Ω] (M : Submodule A Ω) (hM : Submodule.span K (M : Set Ω) = ⊤) :
    IsLocalizedModule (nonZeroDivisors A) M.subtype := by
  refine ⟨fun x => ?_, fun y => ?_, fun {x₁ x₂} h => ⟨1, by rw [one_smul, one_smul]; exact Subtype.ext h⟩⟩
  · have hx : algebraMap A K (x : A) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors x.2
    rw [Module.End.isUnit_iff]
    constructor
    · intro v w hvw
      have h' : (x : A) • v = (x : A) • w := by
        simpa [Module.algebraMap_end_apply] using hvw
      rw [← algebraMap_smul K (x : A) v, ← algebraMap_smul K (x : A) w] at h'
      exact smul_right_injective Ω hx h'
    · intro v
      refine ⟨(algebraMap A K (x : A))⁻¹ • v, ?_⟩
      rw [Module.algebraMap_end_apply, ← algebraMap_smul K (x : A), smul_smul,
        mul_inv_cancel₀ hx, one_smul]
  · have hy : y ∈ Submodule.span K (M : Set Ω) := hM ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem z hz => exact ⟨(⟨z, hz⟩, 1), by simp⟩
    | zero => exact ⟨(0, 1), by simp⟩
    | add y₁ y₂ _ _ h₁ h₂ =>
      obtain ⟨⟨m₁, s₁⟩, e₁⟩ := h₁
      obtain ⟨⟨m₂, s₂⟩, e₂⟩ := h₂
      refine ⟨((s₂ : A) • m₁ + (s₁ : A) • m₂, s₁ * s₂), ?_⟩
      have e₁' : (s₁ : A) • y₁ = (m₁ : Ω) := e₁
      have e₂' : (s₂ : A) • y₂ = (m₂ : Ω) := e₂
      simp only [map_add, map_smul, Submodule.subtype_apply, ← e₁', ← e₂', Submonoid.smul_def,
        Submonoid.coe_mul]
      rw [smul_add, mul_smul, mul_comm, mul_smul, smul_comm (s₂ : A) (s₁ : A) y₁,
        smul_comm (s₂ : A) (s₁ : A) y₂]
    | smul c z _ h =>
      obtain ⟨⟨m, s⟩, e⟩ := h
      obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors A) c
      dsimp only at hab
      have e' : (s : A) • z = (m : Ω) := e
      have hb : (b : A) • (c • z) = a • z := by
        rw [← algebraMap_smul K (b : A), smul_smul, mul_comm _ c, hab, algebraMap_smul]
      refine ⟨(a • m, b * s), ?_⟩
      rw [map_smul, Submodule.subtype_apply, ← e', Submonoid.smul_def, Submonoid.coe_mul,
        mul_comm, mul_smul, hb]
      exact smul_comm _ _ _

theorem finrank_lattice {A K : Type} [CommRing A] [IsDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] {Ω : Type} [AddCommGroup Ω] [Module K Ω] [Module A Ω]
    [IsScalarTower A K Ω] (M : Submodule A Ω) (hM : Submodule.span K (M : Set Ω) = ⊤) :
    finrank K Ω = finrank A M := by
  haveI := isLocalizedModule_subtype M hM
  rw [IsFractionRing.finrank_right_eq A K Ω]
  exact IsLocalizedModule.finrank_eq (nonZeroDivisors A) M.subtype le_rfl

private theorem rankAtStalk_eq_finrank' {R : Type} [CommRing R] [IsDomain R] {P : Type} [AddCommGroup P]
    [Module R P] (q : PrimeSpectrum R) : Module.rankAtStalk P q = Module.finrank R P := by
  unfold Module.rankAtStalk
  rw [IsLocalization.finrank_eq (Localization.AtPrime q.asIdeal) q.asIdeal.primeCompl
    q.asIdeal.primeCompl_le_nonZeroDivisors]
  exact IsLocalizedModule.finrank_eq q.asIdeal.primeCompl
    (LocalizedModule.mkLinearMap q.asIdeal.primeCompl P) q.asIdeal.primeCompl_le_nonZeroDivisors

theorem bc_iso : ∀ (A K : Type) [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (M : Submodule A Ω) (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O) [Algebra A O] (Ω' : Type) [AddCommGroup Ω'] [Module C Ω'] [Module O Ω'] [IsScalarTower O C Ω'] (L : Submodule O Ω') (ι : M →ₛₗ[algebraMap A O] Ω'), M.IsLattice K → Module.Projective A M → L.IsLattice C → Submodule.span O (Set.range ι) = L → Module.finrank K Ω = Module.finrank C Ω' → ∃ j : O ⊗[A] M →ₗ[O] Ω', Function.Injective j ∧ LinearMap.range j = L ∧ ∀ x, j (1 ⊗ₜ x) = ι x := by
  intro A K _ _ _ _ _ Ω _ _ _ _ M C _ v O _ _ hv _ Ω' _ _ _ _ L ι hM hproj hL hspan hdim
  haveI : IsDomain O := hv.hom_inj.isDomain
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  haveI : IsFractionRing O C := hv.isFractionRing
  haveI : Module.Finite A M := Module.Finite.iff_fg.mpr hM.1
  haveI : Module.Finite O L := Module.Finite.iff_fg.mpr hL.1
  haveI : Module.Flat O L := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
    rintro x ⟨a, ha⟩
    rw [Submodule.mem_bot]
    have ha' : (a : O) • (x : Ω') = 0 := by
      have := congrArg Subtype.val ha
      simpa [Submonoid.smul_def] using this
    rw [← algebraMap_smul C (a : O)] at ha'
    have hne : algebraMap O C (a : O) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors a.2
    exact Subtype.ext ((smul_eq_zero.mp ha').resolve_left hne)
  letI : Module A Ω' := Module.compHom Ω' (algebraMap A O)
  haveI : IsScalarTower A O Ω' := ⟨fun a o x => by rw [Algebra.smul_def, mul_smul]; rfl⟩
  let ι' : M →ₗ[A] Ω' :=
    { toFun := ι, map_add' := map_add ι
      map_smul' := fun a x => by rw [LinearMap.map_smulₛₗ]; rfl }
  let j : O ⊗[A] M →ₗ[O] Ω' := ι'.liftBaseChange O
  have hj : ∀ x, j (1 ⊗ₜ x) = ι x := fun x => by
    show (1 : O) • ι x = ι x
    exact one_smul _ _
  have hrange : LinearMap.range j = L := by
    apply le_antisymm
    · rintro _ ⟨t, rfl⟩
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul o x =>
        show o • ι x ∈ L
        exact L.smul_mem o (hspan ▸ Submodule.subset_span ⟨x, rfl⟩)
      | add t₁ t₂ h₁ h₂ => rw [map_add]; exact L.add_mem h₁ h₂
    · rw [← hspan, Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      exact ⟨1 ⊗ₜ x, hj x⟩
  refine ⟨j, ?_, hrange, hj⟩
  let j' : O ⊗[A] M →ₗ[O] L := j.codRestrict L (fun t => hrange ▸ LinearMap.mem_range_self j t)
  have hsurj : Function.Surjective j' := by
    rintro ⟨y, hy⟩
    rw [← hrange] at hy
    obtain ⟨t, rfl⟩ := hy
    exact ⟨t, rfl⟩
  have hbij : Function.Bijective j' := by
    apply Module.bijective_of_surjective_of_rankAtStalk_eq hsurj
    intro m _
    rw [Module.rankAtStalk_baseChange, rankAtStalk_eq_finrank', rankAtStalk_eq_finrank', ← finrank_lattice M hM.2, hdim,
      finrank_lattice L hL.2]
  intro t₁ t₂ h
  exact hbij.1 (Subtype.ext h)

end PositivityTheory.HtPt.Gc
end

