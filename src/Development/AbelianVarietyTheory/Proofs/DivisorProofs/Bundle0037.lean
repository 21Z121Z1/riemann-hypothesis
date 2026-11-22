import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNsmulMemSpan
section
namespace GlobalTheory.MultiplierOrders

theorem exists_nsmul_mem_span {C : Type} [AddCommGroup C] [Module ℚ C] (S : Set C) (x : C)
    (hx : x ∈ Submodule.span ℚ S) : ∃ m : ℕ, 0 < m ∧ m • x ∈ Submodule.span ℤ S := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_pos, by rw [one_smul]; exact Submodule.subset_span hy⟩
  | zero => exact ⟨1, one_pos, by rw [smul_zero]; exact Submodule.zero_mem _⟩
  | add y z _ _ hy hz =>
    obtain ⟨m, hm, hy⟩ := hy
    obtain ⟨n, hn, hz⟩ := hz
    refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
    rw [smul_add]
    refine Submodule.add_mem _ ?_ ?_
    · rw [mul_comm, mul_smul]
      exact nsmul_mem hy n
    · rw [mul_smul]
      exact nsmul_mem hz m
  | smul q y _ hy =>
    obtain ⟨m, hm, hy⟩ := hy
    refine ⟨m * q.den, Nat.mul_pos hm q.den_pos, ?_⟩
    have h : (m * q.den) • q • y = q.num • m • y := by
      rw [← Nat.cast_smul_eq_nsmul ℚ, ← Nat.cast_smul_eq_nsmul ℚ m, ← Int.cast_smul_eq_zsmul ℚ,
        smul_smul, smul_smul]
      congr 1
      push_cast
      rw [mul_assoc, Rat.den_mul_eq_num, mul_comm]
    rw [h]
    exact Submodule.smul_mem _ _ hy

def multipliers {C : Type} [Ring C] (L : Submodule ℤ C) : Subring C where
  carrier := {x | ∀ y ∈ L, x * y ∈ L}
  mul_mem' := fun {a b} ha hb y hy => by
    rw [mul_assoc]; exact ha _ (hb y hy)
  one_mem' := fun y hy => by rw [one_mul]; exact hy
  add_mem' := fun {a b} ha hb y hy => by
    rw [add_mul]; exact L.add_mem (ha y hy) (hb y hy)
  zero_mem' := fun y _ => by rw [zero_mul]; exact L.zero_mem
  neg_mem' := fun {a} ha y hy => by
    rw [neg_mul]; exact L.neg_mem (ha y hy)

theorem exists_order (C : Type) [Ring C] [Algebra ℚ C] [FiniteDimensional ℚ C] :
    ∃ OB : Subring C, Module.Finite ℤ OB ∧ ∀ b : C, ∃ m : ℕ, 0 < m ∧ (m : C) * b ∈ OB := by
  classical
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := ℚ) (M := C)
  have key : ∀ x : C, ∃ m : ℕ, 0 < m ∧ m • x ∈ Submodule.span ℤ (S : Set C) := fun x =>
    exists_nsmul_mem_span _ x (by rw [hS]; exact Submodule.mem_top)
  set L : Submodule ℤ C := Submodule.span ℤ (S : Set C) with hL
  haveI : Module.Finite ℤ L := Module.Finite.iff_fg.mpr ⟨S, rfl⟩
  refine ⟨multipliers L, ?_, ?_⟩
  · obtain ⟨m, hm, h1⟩ := key 1
    let f : multipliers L →+ L :=
      { toFun := fun x => ⟨x.1 * (m • (1 : C)), x.2 _ h1⟩
        map_zero' := Subtype.ext (by simp)
        map_add' := fun a b => Subtype.ext (by simp [add_mul]) }
    refine Module.Finite.of_injective f.toIntLinearMap ?_
    intro a b hab
    have h : a.1 * (m • (1 : C)) = b.1 * (m • (1 : C)) := congrArg Subtype.val hab
    rw [mul_smul_comm, mul_smul_comm, mul_one, mul_one, ← Nat.cast_smul_eq_nsmul ℚ,
      ← Nat.cast_smul_eq_nsmul ℚ] at h
    have hm' : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
    exact Subtype.ext (smul_right_injective C hm' h)
  · intro b
    choose n hn hmem using fun s : C => key (b * s)
    refine ⟨∏ s ∈ S, n s, Finset.prod_pos fun s _ => hn s, ?_⟩
    intro y hy
    induction hy using Submodule.span_induction with
    | mem s hs =>
      have hs' : s ∈ S := hs
      rw [mul_assoc, ← nsmul_eq_mul, ← Finset.prod_erase_mul S n hs', mul_smul]
      exact nsmul_mem (hmem s) _
    | zero => rw [mul_zero]; exact L.zero_mem
    | add y z _ _ hy hz => rw [mul_add]; exact L.add_mem hy hz
    | smul k y _ hy => rw [mul_smul_comm]; exact L.smul_mem k hy

end GlobalTheory.MultiplierOrders
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNumDen
section
open IsLocalRing

namespace GlobalTheory
namespace SpreadOut

lemma exists_num_den {T : Type} [CommRing T] (p : Ideal T) [p.IsPrime]
    (y : Localization.AtPrime p) :
    ∃ a s : T, s ∉ p ∧ algebraMap T _ s * y = algebraMap T _ a := by
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl y
  exact ⟨a, s, s.2, IsLocalization.mk'_spec' _ a s⟩

lemma prod_not_mem {T : Type} [CommRing T] {ι : Type} (p : Ideal T) [p.IsPrime]
    (S : Finset ι) (g : ι → T) (h : ∀ i ∈ S, g i ∉ p) : ∏ i ∈ S, g i ∉ p :=
  Submonoid.prod_mem p.primeCompl (fun i hi => h i hi)

lemma exists_kill {T : Type} [CommRing T] (p : Ideal T) [p.IsPrime] (f₀ : T)
    (z : Localization.Away f₀)
    (ι₀ : Localization.Away f₀ →ₐ[T] Localization.AtPrime p) (hz : ι₀ z = 0) :
    ∃ t : T, t ∉ p ∧ ∀ (B : Type) [CommRing B] [Algebra T B]
      (κ : Localization.Away f₀ →ₐ[T] B), IsUnit (algebraMap T B t) → κ z = 0 := by
  obtain ⟨⟨b, m⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers f₀) z
  have hspec := IsLocalization.mk'_spec' (Localization.Away f₀) b m
  have h1 : algebraMap T (Localization.AtPrime p) b = 0 := by
    have := congrArg ι₀ hspec
    rw [map_mul, AlgHom.commutes, AlgHom.commutes, hz, mul_zero] at this
    exact this.symm
  obtain ⟨t, ht⟩ := (IsLocalization.map_eq_zero_iff p.primeCompl _ b).1 h1
  refine ⟨t, t.2, fun B _ _ κ hu => ?_⟩
  have h2 := congrArg κ hspec
  rw [map_mul, AlgHom.commutes, AlgHom.commutes] at h2
  have hb : algebraMap T B b = 0 := by
    apply hu.mul_left_cancel
    rw [← map_mul, ht, map_zero, mul_zero]
  have hm : IsUnit (algebraMap T B m) := by
    rw [← AlgHom.commutes κ]
    exact (IsLocalization.map_units (Localization.Away f₀) m).map κ
  rw [hb] at h2
  exact hm.mul_right_eq_zero.1 h2

theorem spread_out : ∀ (T A : Type) [CommRing T] [CommRing A] [Algebra T A]
    [Algebra.FinitePresentation T A] (p : Ideal T) [p.IsPrime]
    (φ : A →ₐ[T] Localization.AtPrime p), ∃ f : T, f ∉ p ∧
      ∃ (s : A →ₐ[T] Localization.Away f) (ι : Localization.Away f →ₐ[T] Localization.AtPrime p),
        ι.comp s = φ := by
  intro T A _ _ _ _ p _ φ
  obtain ⟨n, π, hπ, hker⟩ := Algebra.FinitePresentation.out (R := T) (A := A)
  obtain ⟨G, hG⟩ := hker
  choose a s hs hy using fun i : Fin n => exists_num_den p (φ (π (MvPolynomial.X i)))
  set f₀ : T := ∏ i, s i with hf₀
  have hf₀p : f₀ ∉ p := prod_not_mem p _ s (fun i _ => hs i)
  have hu₀ : IsUnit ((Algebra.ofId T (Localization.AtPrime p)) f₀) :=
    IsLocalization.map_units (Localization.AtPrime p) (⟨f₀, hf₀p⟩ : p.primeCompl)
  let ι₀ : Localization.Away f₀ →ₐ[T] Localization.AtPrime p :=
    IsLocalization.Away.liftAlgHom (S := Localization.Away f₀) f₀ hu₀
  have hu : ∀ i, IsUnit (algebraMap T (Localization.Away f₀) (s i)) := fun i =>
    isUnit_of_dvd_unit (map_dvd _ (Finset.dvd_prod_of_mem s (Finset.mem_univ i)))
      (IsLocalization.Away.algebraMap_isUnit f₀)
  let x : Fin n → Localization.Away f₀ := fun i =>
    algebraMap T _ (a i) * ↑(hu i).unit⁻¹
  let ψ₀ : MvPolynomial (Fin n) T →ₐ[T] Localization.Away f₀ := MvPolynomial.aeval x
  have hι0 : ∀ i, ι₀ (x i) = φ (π (MvPolynomial.X i)) := by
    intro i
    have hu' : IsUnit (algebraMap T (Localization.AtPrime p) (s i)) :=
      IsLocalization.map_units _ (⟨s i, hs i⟩ : p.primeCompl)
    apply hu'.mul_left_cancel
    rw [hy i, ← AlgHom.commutes ι₀ (s i), ← map_mul]
    simp only [x]
    rw [mul_left_comm, IsUnit.mul_val_inv, mul_one, AlgHom.commutes]
  have hφ : ι₀.comp ψ₀ = φ.comp π := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, ψ₀, MvPolynomial.aeval_X]
    exact hι0 i
  have hzero : ∀ g : G, ι₀ (ψ₀ g) = 0 := by
    intro g
    have hg : (g : MvPolynomial (Fin n) T) ∈ RingHom.ker π.toRingHom := by
      rw [← hG]; exact Ideal.subset_span g.2
    rw [RingHom.mem_ker] at hg
    have := congrArg (fun h => h (g : MvPolynomial (Fin n) T)) hφ
    simp only [AlgHom.comp_apply] at this
    rw [this]
    have hg' : π g = 0 := hg
    rw [hg', map_zero]
  choose t ht hkill using fun g : G => exists_kill p f₀ (ψ₀ g) ι₀ (hzero g)
  set f : T := f₀ * ∏ g, t g with hfdef
  have hfp : f ∉ p :=
    p.primeCompl.mul_mem hf₀p (prod_not_mem p _ t (fun g _ => ht g))
  have huj : IsUnit ((Algebra.ofId T (Localization.Away f)) f₀) :=
    isUnit_of_dvd_unit (map_dvd _ (dvd_mul_right f₀ _)) (IsLocalization.Away.algebraMap_isUnit f)
  let j : Localization.Away f₀ →ₐ[T] Localization.Away f :=
    IsLocalization.Away.liftAlgHom (S := Localization.Away f₀) f₀ huj
  let ψ : MvPolynomial (Fin n) T →ₐ[T] Localization.Away f := j.comp ψ₀
  have hψG : ∀ g : G, ψ g = 0 := by
    intro g
    apply hkill g (Localization.Away f) j
    exact isUnit_of_dvd_unit
      (map_dvd _ (Dvd.dvd.mul_left (Finset.dvd_prod_of_mem t (Finset.mem_univ g)) f₀))
      (IsLocalization.Away.algebraMap_isUnit f)
  have hspan : Ideal.span (G : Set (MvPolynomial (Fin n) T)) ≤
      RingHom.ker (ψ : MvPolynomial (Fin n) T →+* Localization.Away f) := by
    rw [Ideal.span_le]
    intro g hg
    rw [SetLike.mem_coe, RingHom.mem_ker]
    exact hψG ⟨g, hg⟩
  have hψker : ∀ q : MvPolynomial (Fin n) T, q ∈ RingHom.ker π → ψ q = 0 := by
    intro q hq
    have hq' : q ∈ Ideal.span (G : Set (MvPolynomial (Fin n) T)) := by
      rw [hG]; exact hq
    exact (RingHom.mem_ker).1 (hspan hq')
  let sq := Ideal.Quotient.liftₐ (RingHom.ker π) ψ hψker
  let e := Ideal.quotientKerAlgEquivOfSurjective hπ
  let σ : A →ₐ[T] Localization.Away f := sq.comp e.symm.toAlgHom
  have hσ : ∀ q, σ (π q) = ψ q := by
    intro q
    have : e.symm (π q) = Ideal.Quotient.mk (RingHom.ker π) q := by
      rw [AlgEquiv.symm_apply_eq]; rfl
    show sq (e.symm (π q)) = ψ q
    rw [this]
    simp only [sq, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
    rfl
  have huι : IsUnit ((Algebra.ofId T (Localization.AtPrime p)) f) :=
    IsLocalization.map_units (Localization.AtPrime p) (⟨f, hfp⟩ : p.primeCompl)
  let ι : Localization.Away f →ₐ[T] Localization.AtPrime p :=
    IsLocalization.Away.liftAlgHom (S := Localization.Away f) f huι
  refine ⟨f, hfp, σ, ι, ?_⟩
  have hιj : ι.comp j = ι₀ :=
    (IsLocalization.algHom_subsingleton (Submonoid.powers f₀)).elim _ _
  apply AlgHom.ext
  intro y
  obtain ⟨q, rfl⟩ := hπ y
  rw [AlgHom.comp_apply, hσ q]
  have h1 := congrArg (fun h => h (ψ₀ q)) hιj
  have h2 := congrArg (fun h => h q) hφ
  simp only [AlgHom.comp_apply] at h1 h2
  simp only [ψ, AlgHom.comp_apply]
  rw [h1, h2]

end SpreadOut
end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOfValILeOne
section
noncomputable section

namespace GlobalTheory.ValIwasawa

open Matrix

variable {V F : Type} [CommRing V] [IsDomain V] [ValuationRing V] [Field F] [Algebra V F]
  [IsFractionRing V F]

variable (V) in

abbrev valI : Valuation F (ValuationRing.ValueGroup V F) := ValuationRing.valuation V F

theorem exists_of_valI_le_one {x : F} (h : valI V x ≤ 1) : ∃ a : V, algebraMap V F a = x :=
  (ValuationRing.mem_integer_iff V F x).1 h

theorem exists_clear_col {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) F) (hA : A.det ≠ 0) :
    ∃ Q : Matrix (Fin (n + 1)) (Fin (n + 1)) V, IsUnit Q.det ∧
      ∀ i : Fin n, (Q.map (algebraMap V F) * A) i.succ 0 = 0 := by
  obtain ⟨p, -, hp⟩ := Finset.exists_max_image Finset.univ (fun r => valI V (A r 0)) Finset.univ_nonempty
  have hcol : ∃ r, A r 0 ≠ 0 := by
    by_contra h
    push Not at h
    exact hA (Matrix.det_eq_zero_of_column_eq_zero 0 h)
  have hp0 : A p 0 ≠ 0 := by
    obtain ⟨r, hr⟩ := hcol
    intro h0
    have := hp r (Finset.mem_univ _)
    rw [h0, map_zero] at this
    exact hr ((valI V).zero_iff.1 (le_antisymm this zero_le))
  let σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap 0 p
  let P : Matrix (Fin (n + 1)) (Fin (n + 1)) V := σ.toPEquiv.toMatrix
  have hc : ∀ i, ∃ a : V, algebraMap V F a = A (σ i) 0 / A p 0 := by
    intro i
    apply exists_of_valI_le_one
    rw [map_div₀]
    have hpos : valI V (A p 0) ≠ 0 := by simpa using hp0
    rw [div_le_one₀ (zero_lt_iff.2 hpos)]
    exact hp _ (Finset.mem_univ _)
  choose c hc using hc
  let E : Matrix (Fin (n + 1)) (Fin (n + 1)) V := Matrix.of fun i j =>
    if i = j then 1 else if j = 0 then -c i else 0
  refine ⟨E * P, ?_, ?_⟩
  · rw [Matrix.det_mul]
    refine IsUnit.mul ?_ ?_
    · have hE : E.det = 1 := by
        rw [Matrix.det_of_lowerTriangular E]
        · simp [E]
        · intro i j hij
          have hij' : i < j := hij
          have hj : j ≠ 0 := fun h => by subst h; exact Fin.not_lt_zero _ hij'
          simp only [E, Matrix.of_apply, if_neg (ne_of_lt hij'), if_neg hj]
      rw [hE]; exact isUnit_one
    · simp only [P, Matrix.det_permutation]
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  · intro i
    rw [Matrix.map_mul, Matrix.mul_assoc, Matrix.mul_apply, Fin.sum_univ_succ]
    have hPA : ∀ r, (P.map (algebraMap V F) * A) r 0 = A (σ r) 0 := by
      intro r
      simp [P, Matrix.mul_apply, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
    simp only [hPA, Matrix.map_apply, E, Matrix.of_apply]
    rw [if_neg (Fin.succ_ne_zero i)]
    simp only [if_true, Fin.succ_ne_zero, map_neg, map_one, map_zero, zero_mul]
    rw [Finset.sum_eq_single i]
    · simp only [if_true, map_one, one_mul]
      rw [hc]
      have : σ 0 = p := by simp [σ]
      rw [this]
      field_simp
      ring
    · intro j _ hji
      rw [if_neg (fun h => hji (Fin.succ_injective _ h).symm)]
      simp
    · intro h; exact absurd (Finset.mem_univ i) h

theorem iwasawa_matrix : ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) F), A.det ≠ 0 →
    ∃ (k : Matrix (Fin n) (Fin n) V) (U : Matrix (Fin n) (Fin n) F), IsUnit k.det ∧ U.BlockTriangular id ∧
      (∀ i, U i i ≠ 0) ∧ A = k.map (algebraMap V F) * U
  | 0, A, _ => ⟨1, A, by simp, fun i => i.elim0, fun i => i.elim0, by ext i; exact i.elim0⟩
  | n + 1, A, hA => by
    obtain ⟨Q, hQ, hQA⟩ := exists_clear_col (V := V) A hA
    set B := Q.map (algebraMap V F) * A with hB
    have hdetB : B.det = B 0 0 * (B.submatrix Fin.succ Fin.succ).det := by
      rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
      simp [hQA, B]
    have hQF : (Q.map (algebraMap V F)).det = algebraMap V F Q.det := by
      rw [RingHom.map_det]; rfl
    have hBne : B.det ≠ 0 := by
      rw [hB, Matrix.det_mul, hQF]
      exact mul_ne_zero (hQ.map (algebraMap V F)).ne_zero hA
    have hB00 : B 0 0 ≠ 0 := by intro h; apply hBne; rw [hdetB, h, zero_mul]
    obtain ⟨k', U', hk', hU', hd', hA'⟩ := iwasawa_matrix (B.submatrix Fin.succ Fin.succ) (by
      intro h; apply hBne; rw [hdetB, h, mul_zero])
    let K : Matrix (Fin (n + 1)) (Fin (n + 1)) V := Matrix.of fun i j =>
      Fin.cases (Fin.cases 1 (fun _ => 0) j) (fun i' => Fin.cases 0 (fun j' => k' i' j') j) i
    let U : Matrix (Fin (n + 1)) (Fin (n + 1)) F := Matrix.of fun i j =>
      Fin.cases (B 0 j) (fun i' => Fin.cases 0 (fun j' => U' i' j') j) i
    have hKU : K.map (algebraMap V F) * U = B := by
      ext i j
      refine Fin.cases ?_ (fun i' => ?_) i
      · simp [K, U, Matrix.mul_apply, Fin.sum_univ_succ]
      · refine Fin.cases ?_ (fun j' => ?_) j
        · simp [K, U, Matrix.mul_apply, Fin.sum_univ_succ, hQA]
        · have h1 := congrFun (congrFun hA' i') j'
          simp only [Matrix.submatrix_apply] at h1
          rw [h1]
          simp [K, U, Matrix.mul_apply, Fin.sum_univ_succ]
    have hKdet : K.det = k'.det := by
      rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
      simp [K]
      rfl
    refine ⟨Q⁻¹ * K, U, ?_, ?_, ?_, ?_⟩
    · rw [Matrix.det_mul, hKdet]
      exact (Matrix.isUnit_nonsing_inv_det Q hQ).mul hk'
    · intro i j hij
      induction i using Fin.cases with
      | zero => exact absurd hij (Fin.not_lt_zero _)
      | succ i' =>
        induction j using Fin.cases with
        | zero => simp [U]
        | succ j' =>
          have : j' < i' := Fin.succ_lt_succ_iff.1 hij
          simpa [U] using hU' this
    · intro i
      induction i using Fin.cases with
      | zero => simpa [U] using hB00
      | succ i' => simpa [U] using hd' i'
    · rw [Matrix.map_mul, Matrix.mul_assoc, hKU, hB, ← Matrix.mul_assoc, ← Matrix.map_mul,
        Matrix.nonsing_inv_mul Q hQ, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]

theorem iwasawa : ∀ (V K : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K]
    [IsFractionRing V K] (N : ℕ) (g : GL (Fin N) K), ∃ (k : GL (Fin N) V) (b : GL (Fin N) K),
    b.1.BlockTriangular id ∧ g = GeneralLinearGroup.map (algebraMap V K) k * b := by
  intro V K _ _ _ _ _ _ N g
  obtain ⟨k, U, hk, hU, -, hg⟩ := iwasawa_matrix (V := V) g.1 (Matrix.GeneralLinearGroup.det_ne_zero g)
  obtain ⟨u, rfl⟩ := (Matrix.isUnit_iff_isUnit_det k).2 hk
  refine ⟨u, (GeneralLinearGroup.map (n := Fin N) (algebraMap V K) u)⁻¹ * g, ?_, by simp⟩
  have : ((GeneralLinearGroup.map (n := Fin N) (algebraMap V K) u)⁻¹ * g).1 = U := by
    have h1 : g.1 = (GeneralLinearGroup.map (n := Fin N) (algebraMap V K) u).1 * U := hg
    rw [Units.val_mul, h1, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  rw [this]
  exact hU

end GlobalTheory.ValIwasawa
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrthogonalEigenIdempotentsOfSeparability
section
open scoped TensorProduct

namespace GlobalTheory.LieIdempotents

theorem balanced_apply {K : Type} {M : Type*} [CommRing K] [AddCommGroup M] (k : ℕ) (u v : Fin k → K)
    (hyp : ∀ c : K, ∑ j, (c * u j) ⊗ₜ[ℤ] v j = ∑ j, u j ⊗ₜ[ℤ] (v j * c))
    (B : K →+ K →+ M) (c : K) : ∑ j, B (c * u j) (v j) = ∑ j, B (u j) (v j * c) := by
  have hB : ∀ (r : ℤ) (m n : K), B (r • m) n = B m (r • n) := by
    intro r m n; rw [map_zsmul, map_zsmul]; rfl
  have := congrArg (TensorProduct.liftAddHom B hB) (hyp c)
  simpa [map_sum, TensorProduct.liftAddHom_tmul] using this

end GlobalTheory.LieIdempotents

open GlobalTheory.LieIdempotents in
theorem GlobalTheory.lie_idempotents : ∀ (R C K : Type) [CommRing R] [CommRing C] [CommRing K] (tR : R →+* C) (a : ℕ) (t : Fin a → (K →+* R)), (∀ i j, i ≠ j → Ideal.span (Set.range fun x => t i x - t j x) = ⊤) → ∀ (N : ℤ) (k : ℕ) (u v : Fin k → K), ∑ j, u j * v j = (N : K) → (∀ c : K, ∑ j, (c * u j) ⊗ₜ[ℤ] v j = ∑ j, u j ⊗ₜ[ℤ] (v j * c)) → IsUnit (N : C) → ∀ (H : Type*) [AddCommGroup H] [Module C H] (ρF : K →+* Module.End C H), ∃ φ : Fin a → Module.End C H, (∀ i c, ρF c * φ i = tR (t i c) • φ i) ∧ (∀ i j, φ i * φ j = if i = j then φ i else 0) ∧ (∀ g : Module.End C H, (∀ c, g * ρF c = ρF c * g) → ∀ i, g * φ i = φ i * g) ∧ (∀ F : Submodule C H, (∀ c, ∀ x ∈ F, ρF c x ∈ F) → ∀ i, ∀ x ∈ F, φ i x ∈ F) ∧ (∀ F : Submodule C H, (∀ c, ∀ x ∈ F, ρF c x ∈ F) → ∀ i w, (∀ c, ρF c w - tR (t i c) • w ∈ F) → ∀ j, φ j w - (if j = i then w else 0) ∈ F) := by
  intro R C K _ _ _ tR a t hcom N k u v huv hyp hN H _ _ ρF
  set n : C := ((hN.unit⁻¹ : Cˣ) : C) with hn
  have hnN : n * (N : C) = 1 := hN.val_inv_mul

  have hS : ∀ p q, ∑ j, t p (u j) * t q (v j) = if p = q then (N : R) else 0 := by
    intro p q
    split_ifs with hpq
    · subst hpq
      simp only [← map_mul, ← map_sum, huv, map_intCast]
    · set S := ∑ j, t p (u j) * t q (v j) with hSdef
      let B : K →+ K →+ R := AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (fun y => t p x * t q y)
        (by intro y y'; simp [mul_add])) (by intro x x'; ext y; simp [add_mul])
      have hc : ∀ c, t p c * S = S * t q c := by
        intro c
        have := balanced_apply k u v hyp B c
        simp only [B, AddMonoidHom.mk'_apply, map_mul] at this
        rw [hSdef, Finset.mul_sum, Finset.sum_mul]
        convert this using 2 <;> ring
      have hle : Ideal.span (Set.range fun x => t p x - t q x) ≤ LinearMap.ker (LinearMap.mulLeft R S) := by
        rw [Ideal.span_le]
        rintro _ ⟨x, rfl⟩
        simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.mulLeft_apply]
        rw [mul_sub, mul_comm S, hc, sub_self]
      rw [hcom p q hpq] at hle
      have h1 : (1 : R) ∈ LinearMap.ker (LinearMap.mulLeft R S) := hle Submodule.mem_top
      simpa using h1
  have hSC : ∀ p q, ∑ j, tR (t p (u j)) * tR (t q (v j)) = if p = q then (N : C) else 0 := by
    intro p q
    have := congrArg tR (hS p q)
    simp only [map_sum, map_mul] at this
    rw [this]; split_ifs <;> simp
  have hnNx : ∀ x : Module.End C H, n • (N : C) • x = x := by
    intro x; rw [smul_smul, hnN, one_smul]
  have heig : ∀ i c, ρF c * (n • ∑ j, tR (t i (v j)) • ρF (u j)) = tR (t i c) • (n • ∑ j, tR (t i (v j)) • ρF (u j)) := by
    intro i c
    let B : K →+ K →+ Module.End C H := AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (fun y => tR (t i y) • ρF x)
        (by intro y y'; simp [add_smul])) (by intro x x'; ext y : 1; simp [smul_add])
    have hb := balanced_apply k u v hyp B c
    simp only [B, AddMonoidHom.mk'_apply, map_mul] at hb
    rw [mul_smul_comm, Finset.mul_sum]
    simp only [mul_smul_comm]
    rw [hb, smul_comm (tR (t i c)) n]
    simp only [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    rw [smul_smul, mul_comm]
  refine ⟨fun i => n • ∑ j, tR (t i (v j)) • ρF (u j), heig, ?_, ?_, ?_, ?_⟩
  ·
    intro i j
    dsimp only
    generalize hΦ : n • ∑ l, tR (t j (v l)) • ρF (u l) = Φ at heig
    have hj := heig j
    rw [hΦ] at hj
    rw [smul_mul_assoc, Finset.sum_mul]
    simp only [smul_mul_assoc, hj, smul_smul, ← Finset.sum_smul]
    have hsum : ∑ l, tR (t i (v l)) * tR (t j (u l)) = ∑ l, tR (t j (u l)) * tR (t i (v l)) :=
      Finset.sum_congr rfl fun _ _ => mul_comm _ _
    rw [hsum, hSC j i]
    by_cases hij : i = j
    · subst hij; rw [if_pos rfl, if_pos rfl, hnN, one_smul]; exact hΦ.symm
    · simp [hij, Ne.symm hij]
  · intro g hg i
    simp only [mul_smul_comm, smul_mul_assoc, Finset.mul_sum, Finset.sum_mul, hg]
  · intro F hF i x hx
    simp only [LinearMap.smul_apply, LinearMap.sum_apply]
    exact F.smul_mem _ (F.sum_mem fun l _ => F.smul_mem _ (hF _ _ hx))
  · intro F hF i w hw j
    have e : (n • ∑ l, tR (t j (v l)) • ρF (u l)) w - (if j = i then w else 0)
        = n • ∑ l, tR (t j (v l)) • (ρF (u l) w - tR (t i (u l)) • w) := by
      have hite : (if j = i then w else 0) = n • (∑ l, tR (t i (u l)) * tR (t j (v l))) • w := by
        rw [hSC i j]; by_cases hij : i = j
        · subst hij; simp [smul_smul, hnN]
        · simp [hij, Ne.symm hij]
      rw [hite]
      simp only [LinearMap.smul_apply, LinearMap.sum_apply, smul_sub, Finset.sum_sub_distrib, Finset.sum_smul, Finset.smul_sum, smul_smul]
      congr 1
      refine Finset.sum_congr rfl fun l _ => ?_
      ring_nf
    rw [e]
    exact F.smul_mem _ (F.sum_mem fun l _ => F.smul_mem _ (hw _))
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPosMulExtendIntLinearForm
section
namespace GlobalTheory

theorem exists_pos_mul_extend_int_linearForm (F : Type) [AddCommGroup F] [Module.Free ℤ F]
    [Module.Finite ℤ F] (P : Submodule ℤ F) (f : P →ₗ[ℤ] ℤ) :
    ∃ c : ℤ, 0 < c ∧ ∃ lam : F →ₗ[ℤ] ℤ, ∀ x : P, lam x = c * f x := by
  classical
  obtain ⟨g, hg⟩ := (Module.Baer.of_divisible ℚ).extension_property P.subtype
    P.injective_subtype ((Algebra.linearMap ℤ ℚ).comp f)
  let b := Module.Free.chooseBasis ℤ F
  obtain ⟨⟨d, hd⟩, hint⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors ℤ) (S := ℚ) (fun i => g (b i))
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  choose n hn using hint
  let lam : F →ₗ[ℤ] ℤ := b.constr ℤ n
  have key : (Algebra.linearMap ℤ ℚ).comp lam = d • g := by
    refine b.ext fun i => ?_
    simpa [lam] using hn i
  refine ⟨d * d, mul_self_pos.mpr hd0, d • lam, fun x => ?_⟩
  have h1 := LinearMap.congr_fun key x
  have h2 := LinearMap.congr_fun hg x
  simp at h1 h2
  rw [h2] at h1
  have h3 : lam x = d * f x := by exact_mod_cast h1
  simp [h3, mul_assoc]

end GlobalTheory
end

