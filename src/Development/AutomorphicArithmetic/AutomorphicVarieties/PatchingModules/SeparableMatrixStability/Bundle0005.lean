import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.MapEta
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.Bundle0006

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.RhoHom
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

section Cont

variable {Γ R : Type} [TopologicalSpace Γ] [CommRing R] {I : Ideal R}

private theorem ac_const (c : R) : AdicCont I fun _ : Γ => c := fun _ => IsLocallyConstant.const _

private theorem ac_add {f g : Γ → R} (hf : AdicCont I f) (hg : AdicCont I g) : AdicCont I fun a => f a + g a := fun N => by
  simpa only [map_add] using (hf N).comp₂ (hg N) (· + ·)

private theorem ac_mul {f g : Γ → R} (hf : AdicCont I f) (hg : AdicCont I g) : AdicCont I fun a => f a * g a := fun N => by
  simpa only [map_mul] using (hf N).comp₂ (hg N) (· * ·)

private theorem ac_sum {ι : Type} (s : Finset ι) {f : ι → Γ → R} (hf : ∀ i, AdicCont I (f i)) :
    AdicCont I fun a => ∑ i ∈ s, f i a := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ac_const (0 : R)
  | insert i s hi ih => simpa only [Finset.sum_insert hi] using ac_add (hf i) ih

private theorem ac_map {S : Type} [CommRing S] (φ : R →+* S) {t : R} {f : Γ → R} (hf : AdicCont (Ideal.span {t}) f) :
    AdicCont (Ideal.span {φ t}) fun a => φ (f a) := fun N => by
  have hle : Ideal.span {t} ^ N ≤ (Ideal.span {φ t} ^ N).comap φ := by
    rw [Ideal.span_singleton_pow, Ideal.span_singleton_pow, Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_pow]
    exact Ideal.mem_span_singleton_self _
  exact (hf N).comp (Ideal.quotientMap _ φ hle)

private theorem ac_nil {t : R} (ht : IsNilpotent t) {f : Γ → R} (hf : AdicCont (Ideal.span {t}) f) :
    IsLocallyConstant f := by
  obtain ⟨N, hN⟩ := ht
  refine IsLocallyConstant.desc _ (Ideal.Quotient.mk (Ideal.span {t} ^ N)) (hf N) ?_
  rw [RingHom.injective_iff_ker_eq_bot, Ideal.mk_ker, Ideal.span_singleton_pow, hN]
  simp

private theorem lc_mat {n : ℕ} {f : Γ → Matrix (Fin n) (Fin n) R} (hf : ∀ i j, IsLocallyConstant fun a => f a i j) :
    IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro a
  have : ∀ᶠ b in nhds a, ∀ i j, f b i j = f a i j :=
    eventually_all.2 fun i => eventually_all.2 fun j => (hf i j).eventually_eq a
  exact this.mono fun b hb => Matrix.ext hb

end Cont

private theorem epM_entry {A X : Type} [CommRing A] [CommRing X] [Algebra A X] {g n : ℕ}
    (Z : Fin g → Matrix (Fin n) (Fin n) A) (a b : Fin n) :
    (DD.epM fun j => (Z j).map (algebraMap A X)) a b =
      ∑ j, (⟨0, Pi.single j 1, 0, 0⟩ : DD X g) * algebraMap A (DD X g) (Z j a b) := by
  have e : ∀ c : A, algebraMap A (DD X g) c = DD.C (algebraMap A X c) := fun _ => rfl
  have s : ∀ (s : Finset (Fin g)), (∑ j ∈ s, (⟨0, Pi.single j 1, 0, 0⟩ : DD X g) * algebraMap A (DD X g) (Z j a b)) =
      ⟨0, fun i => if i ∈ s then algebraMap A X (Z i a b) else 0, 0, 0⟩ := by
    intro s
    induction s using Finset.induction_on with
    | empty => ext <;> simp
    | insert i s hi ih =>
      rw [Finset.sum_insert hi, ih, e]
      ext j
      · simp
      · by_cases h : j = i
        · subst h; simp [hi]
        · simp [h]
      · simp
      · simp
  rw [s]
  simp [DD.epM]

private theorem ρX_cont {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n) (X : Type) [CommRing X]
    [Algebra x.A X] (i j : Fin n) : AdicCont (Ideal.span {algebraMap x.A X x.t}) fun g => x.ρX X g i j := by
  have h := x.cont i j
  rw [PowerSeries.maximalIdeal_eq_span_X] at h
  exact ac_map (algebraMap x.A X) h

theorem UpperTheory.V.Pa.rho_hom :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (n : ℕ) (x : NP F n) (k : Kap x) (X : Type) [CommRing X] [Algebra x.A X], (x.ρX X 1 = 1 ∧ (∀ g h, x.ρX X (g * h) = x.ρX X g * x.ρX X h) ∧ ∀ i j, AdicCont (Ideal.span {algebraMap x.A X x.t}) fun g => x.ρX X g i j) ∧ (k.ρ1 X 1 = 1 ∧ (∀ g h, k.ρ1 X (g * h) = k.ρ1 X g * k.ρ1 X h) ∧ ∀ i j, AdicCont (Ideal.span {algebraMap x.A (DD X k.g) x.t}) fun g => k.ρ1 X g i j) ∧ (IsNilpotent (algebraMap x.A X x.t) → IsLocallyConstant (x.ρX X) ∧ IsLocallyConstant (k.ρ1 X)) ∧ ∀ v, k.w1 X v * k.wi1 X v = 1 ∧ x.wX X v * x.wiX X v = 1 := by
  intro l _ F n x k X _ _
  obtain ⟨h1, h2, -, h4⟩ := Det.rho1Hom k X
  have c1 : ∀ i j, AdicCont (Ideal.span {algebraMap x.A (DD X k.g) x.t}) fun g => k.ρ1 X g i j := by
    intro i j
    simp only [Kap.ρ1, Matrix.mul_apply, Matrix.add_apply, epM_entry]
    refine ac_sum _ fun c => ac_mul (ac_add (ac_const _) (ac_sum _ fun a => ac_mul (ac_const _) ?_)) (ρX_cont x _ c j)
    exact ac_map (algebraMap x.A (DD X k.g)) ((k.mem a).2.1 i c)
  refine ⟨⟨by simp [NP.ρX, mat], fun g h => by simp [NP.ρX, mat, Matrix.map_mul], ρX_cont x X⟩, ⟨h1, h2, c1⟩,
    fun ht => ⟨lc_mat fun i j => ac_nil ht (ρX_cont x X i j), lc_mat fun i j => ac_nil ?_ (c1 i j)⟩,
    fun v => ⟨(h4 v).1, ?_⟩⟩
  · exact ht.map (DD.C : X →+* DD X k.g)
  · rw [NP.wX, NP.wiX, ← Matrix.map_mul]; simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.SelLin
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem adic_lin {G R : Type} [TopologicalSpace G] [CommRing R] (I : Ideal R) (c : R) {f f' : G → R}
    (h : AdicCont I f) (h' : AdicCont I f') : AdicCont I fun g => c * f g + f' g := by
  intro N
  have e : (fun g => (Ideal.Quotient.mk (I ^ N)) (c * f g + f' g)) =
      fun g => Ideal.Quotient.mk (I ^ N) c * Ideal.Quotient.mk (I ^ N) (f g) + Ideal.Quotient.mk (I ^ N) (f' g) := by
    funext g
    simp only [map_add, map_mul]
  rw [e]
  exact ((IsLocallyConstant.const _).mul (h N)).add (h' N)

private theorem adic_zero {G R : Type} [TopologicalSpace G] [CommRing R] (I : Ideal R) :
    AdicCont I fun _ : G => (0 : R) := fun _ => IsLocallyConstant.const _

section

variable {l : ℕ} [Fact l.Prime] (F : GFrame l) {n : ℕ} {A R : Type} [CommRing A] [CommRing R] [Algebra A R]
  (ρ : F.G₀ → Matrix (Fin n) (Fin n) R)

private theorem dY_lin (c : A) (Y Y' : Matrix (Fin n) (Fin n) R) (g : F.G₀) :
    dY F ρ (c • Y + Y') g = c • dY F ρ Y g + dY F ρ Y' g := by
  simp only [dY, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, smul_sub]
  abel

private theorem dY_zero (g : F.G₀) : dY F ρ 0 g = 0 := by simp [dY]

private theorem locAt_lin (w wi : F.Vl → Matrix (Fin n) (Fin n) R) (c : A) {z z' : F.G₀ → Matrix (Fin n) (Fin n) R}
    {v : F.Vl} {Y Y' : Matrix (Fin n) (Fin n) R} (h : LocAt F ρ w wi z v Y) (h' : LocAt F ρ w wi z' v Y') :
    LocAt F ρ w wi (c • z + z') v (c • Y + Y') := by
  intro g
  obtain ⟨h1, h2⟩ := h g
  obtain ⟨h1', h2'⟩ := h' g
  have key : wi v * ((c • z + z') ((F.φ v) g) - dY F ρ (c • Y + Y') ((F.φ v) g)) * w v =
      c • (wi v * (z ((F.φ v) g) - dY F ρ Y ((F.φ v) g)) * w v) +
        wi v * (z' ((F.φ v) g) - dY F ρ Y' ((F.φ v) g)) * w v := by
    rw [dY_lin]
    simp only [Pi.add_apply, Pi.smul_apply, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_sub, Matrix.sub_mul, smul_sub]
    abel
  refine ⟨fun i j hij => ?_, fun hg i => ?_⟩
  · rw [key, Matrix.add_apply, Matrix.smul_apply, h1 i j hij, h1' i j hij, smul_zero, add_zero]
  · rw [key, Matrix.add_apply, Matrix.smul_apply, h2 hg i, h2' hg i, smul_zero, add_zero]

end

private theorem sub_of_lin {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (s : Set M) (h0 : (0 : M) ∈ s)
    (h : ∀ (c : A) x y, x ∈ s → y ∈ s → c • x + y ∈ s) : ∃ S : Submodule A M, (S : Set M) = s := by
  refine ⟨{ carrier := s, add_mem' := ?_, zero_mem' := h0, smul_mem' := ?_ }, rfl⟩
  · intro x y hx hy
    have := h 1 x y hx hy
    rwa [one_smul] at this
  · intro c x hx
    have := h c x 0 hx h0
    rwa [add_zero] at this

theorem UpperTheory.V.Pa.sel_lin :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (n : ℕ) (A R : Type) [CommRing A] [CommRing R] [Algebra A R] (t : A) (ρ : F.G₀ → Matrix (Fin n) (Fin n) R) (w wi : F.Vl → Matrix (Fin n) (Fin n) R) (V : Submodule A (Matrix (Fin n) (Fin n) R)), (∃ S : Submodule A (F.G₀ → Matrix (Fin n) (Fin n) R), (S : Set _) = SelZ F t ρ w wi V) ∧ ∃ S : Submodule A (F.G₀ → Matrix (Fin n) (Fin n) R), (S : Set _) = Bd F ρ V := by
  intro l _ F n A R _ _ _ t ρ w wi V
  constructor
  · apply sub_of_lin
    · refine ⟨fun _ => V.zero_mem, fun i j => ?_, fun g h => by simp, fun g => by simp, fun u g _ => rfl,
        fun v => ⟨0, V.zero_mem, fun g => ?_⟩⟩
      · exact adic_zero _
      · simp [dY_zero]
    · intro c x y hx hy
      obtain ⟨x1, x2, x3, x4, x5, x6⟩ := hx
      obtain ⟨y1, y2, y3, y4, y5, y6⟩ := hy
      refine ⟨fun g => V.add_mem (V.smul_mem c (x1 g)) (y1 g), fun i j => ?_, fun g h => ?_, fun g => ?_,
        fun u g hg => ?_, fun v => ?_⟩
      · have e : (fun g => (c • x + y) g i j) = fun g => algebraMap A R c * x g i j + y g i j := by
          funext g
          rw [Pi.add_apply, Pi.smul_apply, Matrix.add_apply, Matrix.smul_apply, Algebra.smul_def]
        rw [e]
        exact adic_lin _ _ (x2 i j) (y2 i j)
      · simp only [Pi.add_apply, Pi.smul_apply, x3 g h, y3 g h, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
          Matrix.smul_mul, smul_add]
        abel
      · simp only [Pi.add_apply, Pi.smul_apply, x4 g, y4 g, Matrix.transpose_add, Matrix.transpose_smul,
          Matrix.transpose_neg, smul_neg]
        abel
      · simp [x5 u g hg, y5 u g hg]
      · obtain ⟨Y, hY, hYl⟩ := x6 v
        obtain ⟨Y', hY', hYl'⟩ := y6 v
        exact ⟨c • Y + Y', V.add_mem (V.smul_mem c hY) hY', locAt_lin F ρ w wi c hYl hYl'⟩
  · apply sub_of_lin
    · exact ⟨0, V.zero_mem, by simp, funext fun g => (dY_zero F ρ g).symm⟩
    · rintro c x y ⟨Y, hY, hYt, rfl⟩ ⟨Y', hY', hYt', rfl⟩
      refine ⟨c • Y + Y', V.add_mem (V.smul_mem c hY) hY', ?_, ?_⟩
      · rw [Matrix.transpose_add, Matrix.transpose_smul, hYt, hYt', smul_neg, neg_add]
      · funext g
        rw [dY_lin]
        rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.SelMap
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

section

variable {A R R' : Type} [CommRing A] [CommRing R] [Algebra A R] [CommRing R'] [Algebra A R'] (f : R →ₐ[A] R') {n : ℕ}

private theorem adic_map {G : Type} [TopologicalSpace G] (t : A) (u : G → R)
    (hu : AdicCont (Ideal.span {algebraMap A R t}) u) :
    AdicCont (Ideal.span {algebraMap A R' t}) fun g => f (u g) := by
  intro N
  have hmap : Ideal.map f ((Ideal.span {algebraMap A R t}) ^ N) =
      (Ideal.span {algebraMap A R' t}) ^ N := by
    rw [Ideal.map_pow, Ideal.map_span, Set.image_singleton, AlgHom.commutes]
  have hle : (Ideal.span {algebraMap A R t}) ^ N ≤
      ((Ideal.span {algebraMap A R' t}) ^ N).comap (f : R →+* R') := by
    rw [← Ideal.map_le_iff_le_comap]
    exact hmap.le
  have e : (fun g => Ideal.Quotient.mk ((Ideal.span {algebraMap A R' t}) ^ N) (f (u g))) =
      (Ideal.quotientMap _ (f : R →+* R') hle) ∘
        (fun g => Ideal.Quotient.mk ((Ideal.span {algebraMap A R t}) ^ N) (u g)) := by
    funext g
    simp [Ideal.quotientMap_mk]
  change IsLocallyConstant (fun g => Ideal.Quotient.mk ((Ideal.span {algebraMap A R' t}) ^ N) (f (u g)))
  rw [e]
  exact (hu N).comp _

private theorem mm_mul (M N : Matrix (Fin n) (Fin n) R) : (M * N).map f = M.map f * N.map f :=
  map_mul f.mapMatrix M N

private theorem mm_add (M N : Matrix (Fin n) (Fin n) R) : (M + N).map f = M.map f + N.map f :=
  map_add f.mapMatrix M N

private theorem mm_sub (M N : Matrix (Fin n) (Fin n) R) : (M - N).map f = M.map f - N.map f :=
  map_sub f.mapMatrix M N

private theorem mm_neg (M : Matrix (Fin n) (Fin n) R) : (-M).map f = -M.map f :=
  map_neg f.mapMatrix M

private theorem dY_map {l : ℕ} [Fact l.Prime] (F : GFrame l) (ρ : F.G₀ → Matrix (Fin n) (Fin n) R)
    (Y : Matrix (Fin n) (Fin n) R) (g : F.G₀) :
    (dY F ρ Y g).map f = dY F (fun g => (ρ g).map f) (Y.map f) g := by
  unfold dY
  rw [mm_sub, mm_mul, mm_mul]

end

theorem UpperTheory.V.Pa.sel_map :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (n : ℕ) (A R R' : Type) [CommRing A] [CommRing R] [Algebra A R] [CommRing R'] [Algebra A R'] (f : R →ₐ[A] R') (t : A) (ρ : F.G₀ → Matrix (Fin n) (Fin n) R) (w wi : F.Vl → Matrix (Fin n) (Fin n) R) (V : Submodule A (Matrix (Fin n) (Fin n) R)) (V' : Submodule A (Matrix (Fin n) (Fin n) R')), (∀ Z ∈ V, Z.map f ∈ V') → ∀ z, (z ∈ SelZ F t ρ w wi V → (fun g => (z g).map f) ∈ SelZ F t (fun g => (ρ g).map f) (fun v => (w v).map f) (fun v => (wi v).map f) V') ∧ (z ∈ Bd F ρ V → (fun g => (z g).map f) ∈ Bd F (fun g => (ρ g).map f) V') := by
  intro l _ F n A R R' _ _ _ _ _ f t ρ w wi V V' hV z
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨fun g => hV _ (h1 g), fun i j => ?_, fun g k => ?_, fun g => ?_, fun u g hg => ?_,
      fun v => ?_⟩
    · exact adic_map f t (fun g => z g i j) (h2 i j)
    · beta_reduce
      rw [h3, mm_add, mm_mul, mm_mul]
    · beta_reduce
      rw [h4, mm_neg, Matrix.transpose_map]
    · beta_reduce
      rw [h5 u g hg]
      exact Matrix.map_zero _ (map_zero f)
    · obtain ⟨Y, hY, hloc⟩ := h6 v
      refine ⟨Y.map f, hV _ hY, fun g => ?_⟩
      have key : (wi v).map f * ((z ((F.φ v) g)).map f -
            dY F (fun g => (ρ g).map f) (Y.map f) ((F.φ v) g)) * (w v).map f =
          (wi v * (z ((F.φ v) g) - dY F ρ Y ((F.φ v) g)) * w v).map f := by
        rw [mm_mul, mm_mul, mm_sub, dY_map]
      obtain ⟨hl1, hl2⟩ := hloc g
      refine ⟨fun i j hij => ?_, fun hg i => ?_⟩
      · beta_reduce
        rw [key, Matrix.map_apply, hl1 i j hij, map_zero]
      · beta_reduce
        rw [key, Matrix.map_apply, hl2 hg i, map_zero]
  · rintro ⟨Y, hY, hT, rfl⟩
    refine ⟨Y.map f, hV _ hY, ?_, ?_⟩
    · rw [← Matrix.transpose_map, hT, mm_neg]
    · funext g
      exact dY_map f F ρ Y g
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.UnipOf
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem cast_zero (l : ℕ) [Fact l.Prime] (K : Type) [Field K] [Finite K] [Algebra ℤ_[l] K] : (l : K) = 0 := by
  have hni : ¬ Function.Injective (algebraMap ℤ_[l] K) := by
    haveI : Infinite ℤ_[l] := Infinite.of_injective (Nat.cast : ℕ → ℤ_[l]) Nat.cast_injective
    exact not_injective_infinite_finite _
  have hker : RingHom.ker (algebraMap ℤ_[l] K) ≠ ⊥ := by
    intro h
    exact hni ((RingHom.injective_iff_ker_eq_bot _).2 h)
  obtain ⟨e, he⟩ := PadicInt.ideal_eq_span_pow_p hker
  have hmem : (l : ℤ_[l]) ^ e ∈ RingHom.ker (algebraMap ℤ_[l] K) := by
    rw [he]
    exact Ideal.subset_span rfl
  rw [RingHom.mem_ker, map_pow, map_natCast] at hmem
  exact pow_eq_zero_iff'.mp hmem |>.1

private theorem key (l : ℕ) [Fact l.Prime] (K : Type) [Field K] (hl : (l : K) = 0) (n : ℕ)
    (P : Matrix (Fin n) (Fin n) (PowerSeries K))
    (hP : P.charpoly.map (PowerSeries.constantCoeff : PowerSeries K →+* K) = (Polynomial.X - 1) ^ n) (m : ℕ) :
    ∃ e : ℕ, ∀ i j, (P ^ l ^ e - 1) i j ∈ Ideal.span {(PowerSeries.X : PowerSeries K) ^ m} := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨0, fun i => i.elim0⟩
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  haveI : CharP K l := (CharP.charP_iff_prime_eq_zero (Fact.out : l.Prime)).2 hl
  haveI : CharP (PowerSeries K) l :=
    charP_of_injective_algebraMap (algebraMap K (PowerSeries K)).injective l
  set I : Ideal (PowerSeries K) := Ideal.span {PowerSeries.X} with hI
  have hmul : ∀ (A B : Matrix (Fin n) (Fin n) (PowerSeries K)) (J J' : Ideal (PowerSeries K)),
      (∀ i j, A i j ∈ J) → (∀ i j, B i j ∈ J') → ∀ i j, (A * B) i j ∈ J * J' := by
    intro A B J J' hA hB i j
    rw [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_mul (hA i k) (hB k j)
  have hpow : ∀ (A : Matrix (Fin n) (Fin n) (PowerSeries K)) (J : Ideal (PowerSeries K)),
      (∀ i j, A i j ∈ J) → ∀ k : ℕ, ∀ i j, (A ^ k) i j ∈ J ^ k := by
    intro A J hA k
    induction k with
    | zero => intro i j; simp
    | succ k ih =>
      intro i j
      rw [pow_succ, pow_succ]
      exact hmul _ _ _ _ ih hA i j
  set d := P.charpoly - (Polynomial.X - 1) ^ n with hd
  have hdmap : d.map (PowerSeries.constantCoeff : PowerSeries K →+* K) = 0 := by
    rw [hd, Polynomial.map_sub, hP, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X,
      Polynomial.map_one, sub_self]
  have hdc : ∀ k, d.coeff k ∈ I := by
    intro k
    rw [hI, Ideal.mem_span_singleton, PowerSeries.X_dvd_iff]
    have := congrArg (fun q => Polynomial.coeff q k) hdmap
    simpa [Polynomial.coeff_map] using this
  have hev : Polynomial.aeval P d = -(P - 1) ^ n := by
    rw [hd, map_sub, Matrix.aeval_self_charpoly, map_pow, map_sub, Polynomial.aeval_X, map_one,
      zero_sub]
  have hA : ∀ i j, (Polynomial.aeval P d) i j ∈ I := by
    intro i j
    rw [Polynomial.aeval_eq_sum_range, Matrix.sum_apply]
    exact Ideal.sum_mem _ fun k _ => by
      rw [Matrix.smul_apply, smul_eq_mul]
      exact Ideal.mul_mem_right _ _ (hdc k)
  have hQ : ∀ i j, ((P - 1) ^ n) i j ∈ I := by
    intro i j
    have h1 : (P - 1) ^ n = -(Polynomial.aeval P d) := by rw [hev, neg_neg]
    rw [h1, Matrix.neg_apply]
    exact I.neg_mem (hA i j)
  refine ⟨n * m, fun i j => ?_⟩
  have hle : n * m ≤ l ^ (n * m) := (Nat.lt_pow_self (Fact.out : l.Prime).one_lt).le
  have hsub : P ^ l ^ (n * m) - 1 = (P - 1) ^ l ^ (n * m) := by
    rw [sub_pow_char_pow_of_commute l (n * m) (Commute.one_right P), one_pow]
  obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hle
  rw [hsub, hr, pow_add, pow_mul]
  have h2 := hmul (((P - 1) ^ n) ^ m) ((P - 1) ^ r) (I ^ m) ⊤ (hpow _ _ hQ m)
    (fun a b => Submodule.mem_top (x := ((P - 1) ^ r) a b)) i j
  rwa [Ideal.mul_top, hI, Ideal.span_singleton_pow] at h2

theorem UpperTheory.V.Pa.unip_of :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (n : ℕ) (x : NP F n) (H : Subgroup F.Γ), (∀ h : F.G₀, (h : F.Γ) ∈ H → (mat x.ρ h).charpoly.map (PowerSeries.constantCoeff : x.A →+* x.K) = (Polynomial.X - 1) ^ n) → x.UnipOn H := by
  intro l _ F n x H hH m h hh
  obtain ⟨e, he⟩ := key l x.K (cast_zero l x.K) n (mat x.ρ h) (hH h hh) m
  exact ⟨e, fun i j => by rw [map_pow]; exact he i j⟩
end

