import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.ExistsResQ
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.Bundle0003
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.Bundle0001

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.CharacterSubgroupOpenEvenIndexTamePower
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem false_of_two_primes_valuation_lt_one {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q) (h1 : A.valuation (p : Ω) < 1) (h2 : A.valuation (q : Ω) < 1) : False := by
  have hc : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  have hz : ((Nat.gcd p q : ℕ) : ℤ) = p * Nat.gcdA p q + q * Nat.gcdB p q := Nat.gcd_eq_gcd_ab p q
  rw [hc.gcd_eq_one] at hz
  have hΩ : (1 : Ω) = (p : Ω) * ((Nat.gcdA p q : ℤ) : Ω) + (q : Ω) * ((Nat.gcdB p q : ℤ) : Ω) := by
    have := congrArg (fun z : ℤ => (z : Ω)) hz
    push_cast at this
    exact this
  have ha : A.valuation ((Nat.gcdA p q : ℤ) : Ω) ≤ 1 := A.valuation_le_one_iff _ |>.2 (intCast_mem A _)
  have hb : A.valuation ((Nat.gcdB p q : ℤ) : Ω) ≤ 1 := A.valuation_le_one_iff _ |>.2 (intCast_mem A _)
  have e1 : A.valuation ((p : Ω) * ((Nat.gcdA p q : ℤ) : Ω)) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' ha) h1
  have e2 : A.valuation ((q : Ω) * ((Nat.gcdB p q : ℤ) : Ω)) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' hb) h2
  have e3 := Valuation.map_add_lt _ e1 e2
  rw [← hΩ, map_one] at e3
  exact lt_irrefl _ e3

theorem UpperTheory.V.Ws.characterSubgroup_open_even_index_tame_power :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ X : Set2 D, IsOpen (X.H : Set (G ℚ Ω)) ∧ commutator (G ℚ Ω) ≤ X.H ∧ (∀ σ : G ℚ Ω, IsCC σ → σ ∈ X.H) ∧ Even X.H.index ∧ ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∀ g ∈ Ine (F := ℚ) A, ∃ m : ℕ, l.Coprime m ∧ g ^ m ∈ X.H := by
  intro Ω _ _ _ l _ c D hD X
  obtain ⟨_, _, _, _, _, _, _, ⟨m, hm, hpow⟩, hopen⟩ := barFacts D hD
  have hbarpow : ∀ (a : G ℚ Ω) (n : ℕ), Raw.bar D.Psi (a ^ n) = Raw.bar D.Psi a ^ n := by
    intro a n
    simp [Raw.bar]
  have hsub : ∀ g : G ℚ Ω, X.φ g = 1 → X.η g = 1 → X.η' g = 1 → X.κ g = 1 →
      Raw.bar D.Psi g = 1 → g ∈ X.H := by
    intro g h1 h2 h3 h4 h5
    rw [Set2.mem_H]
    refine ⟨?_, by rw [h2, h3], h4⟩
    rw [h5, h1]
    simp
  have hl : l.Prime := Fact.out
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hU : IsOpen ((X.φ.ker : Set (G ℚ Ω)) ∩ X.η.ker ∩ X.η'.ker ∩ X.κ.ker ∩
        {g | Raw.bar D.Psi g = 1}) :=
      (((X.hφ.opn.inter X.hη.opn).inter X.hη'.opn).inter X.kap.opn).inter hopen
    have h1 : (1 : G ℚ Ω) ∈ (X.φ.ker : Set (G ℚ Ω)) ∩ X.η.ker ∩ X.η'.ker ∩ X.κ.ker ∩
        {g | Raw.bar D.Psi g = 1} := by
      simp [Raw.bar]
    have hmem : (X.H : Set (G ℚ Ω)) ∈ nhds (1 : G ℚ Ω) := by
      refine Filter.mem_of_superset (hU.mem_nhds h1) ?_
      rintro g ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
      exact hsub g h1 h2 h3 h4 h5
    exact Subgroup.isOpen_of_mem_nhds _ hmem
  · rw [commutator, Subgroup.commutator_le]
    intro a _ b _
    refine hsub _ ?_ ?_ ?_ ?_ ?_ <;>
      simp [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm, mul_comm, Raw.bar]
    all_goals
      rw [commutatorElement_eq_one_iff_mul_comm.2 (mul_comm _ _)]
      simp
  · intro σ hσ
    have hsq : σ ^ 2 = 1 := by
      obtain ⟨j, hj⟩ := hσ
      ext x
      apply j.injective
      rw [pow_two, AlgEquiv.mul_apply, hj, hj, Complex.conj_conj]
      rfl
    have hκ : X.κ σ = 1 := by
      obtain ⟨k, hk⟩ := X.kap.pow
      have e1 : X.κ σ ^ (l ^ k) = 1 := by
        have := congrArg (fun f => f σ) hk
        simpa using this
      have e2 : X.κ σ ^ 2 = 1 := by
        rw [← map_pow, hsq, map_one]
      have hcop : Nat.Coprime 2 (l ^ k) :=
        Nat.Coprime.pow_right k ((Nat.coprime_primes Nat.prime_two hl).mpr (Ne.symm hD.l_odd))
      have := pow_gcd_eq_one.2 ⟨e2, e1⟩
      rwa [hcop.gcd_eq_one, pow_one] at this
    have hψ := X.psi_cc σ hσ
    rw [Set2.mem_H]
    refine ⟨?_, by rw [X.hη.cc σ hσ, X.hη'.cc σ hσ], hκ⟩
    simp [Raw.bar, hψ, X.hφ.cc σ hσ]
  · let f : G ℚ Ω →* ℤˣ := X.η * X.η'⁻¹
    have hle : X.H ≤ f.ker := by
      intro g hg
      rw [Set2.mem_H] at hg
      simp [f, hg.2.1]
    have hsurj : Function.Surjective f := by
      intro s
      obtain ⟨g', -, h2, h3, -⟩ := adj2 D hD X 1 1 s 1
      exact ⟨g', by simp [f, h2, h3]⟩
    have hidx : f.ker.index = 2 := by
      rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hsurj, Subgroup.card_top]
      simp
    rw [even_iff_two_dvd, ← hidx]
    exact Subgroup.index_dvd_of_le hle
  · intro A hA g hg
    have hne : ∀ q : ℕ, q.Prime → q ∉ D.S → ¬ A.valuation (q : Ω) < 1 := by
      intro q hq hqS hv
      exact false_of_two_primes_valuation_lt_one A hq hl (fun e => hqS (e ▸ hD.l_mem)) hv hA
    have hφg : X.φ g = 1 := (MonoidHom.mem_ker).1 (X.hφ.unr A (hne _ X.hφ.prime X.hφ.nm) hg)
    have hηg : X.η g = 1 := (MonoidHom.mem_ker).1
      (X.hη.unr A (hne _ X.hη.prime (fun h => X.hη.nm (Finset.mem_insert_of_mem h))) hg)
    have hη'g : X.η' g = 1 := (MonoidHom.mem_ker).1
      (X.hη'.unr A (hne _ X.hη'.prime
        (fun h => X.hη'.nm (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h)))) hg)
    have hκg : X.κ g = 1 := (MonoidHom.mem_ker).1 (X.kap.unrL A hA hg)
    refine ⟨m, hm, hsub _ ?_ ?_ ?_ ?_ ?_⟩
    · rw [map_pow, hφg, one_pow]
    · rw [map_pow, hηg, one_pow]
    · rw [map_pow, hη'g, one_pow]
    · rw [map_pow, hκg, one_pow]
    · rw [hbarpow, hpow g]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.Elts2
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem bar_mul {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    (γ : G ℚ Ω →* c.Oˣ) (g h : G ℚ Ω) : Raw.bar γ (g * h) = Raw.bar γ g * Raw.bar γ h := by
  simp only [Raw.bar, map_mul, Units.val_mul]

private theorem move {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    (D : Raw Ω c) (hD : D.Good) (X : Set2 D) (g : G ℚ Ω) (s : ℤˣ) (hk : X.κ g = 1)
    (hs : Raw.bar D.Psi g = ((s : ℤ) : ResidueField c.O)) :
    ∃ g' ∈ X.H ⊓ X.η.ker, D.Psi g' = D.Psi g ∧ D.ξ g' = D.ξ g ∧ D.om g' = D.om g := by
  obtain ⟨g', h1, h2, h3, h4, h5, h6, h7⟩ := adj2 D hD X g s 1 1
  refine ⟨g', ⟨X.mem_H.2 ⟨?_, h2.trans h3.symm, h7.trans hk⟩, h2⟩, h4, h5, h6⟩
  rw [h1, ← hs, Raw.bar, h4]

theorem UpperTheory.V.Ws.elts2 :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ X : Set2 D, ∃ a u t, X.Elts a u t := by
  intro Ω _ _ _ l hl c D hD X
  obtain ⟨w1, w2, -, w4, -⟩ := away D hD
  obtain ⟨j, hj⟩ := X.kap.pow
  have hodd : Odd (l ^ j) := (hl.out.odd_of_ne_two hD.l_odd).pow
  have hk : X.κ (D.cc ^ l ^ j) = 1 := by
    rw [map_pow, ← MonoidHom.pow_apply, hj, MonoidHom.one_apply]
  have hP : D.Psi (D.cc ^ l ^ j) = 1 := by rw [map_pow, hD.Psi_even, one_pow]
  obtain ⟨a, a0, a1, a2, a3⟩ := move D hD X (D.cc ^ l ^ j) 1 hk (by simp [Raw.bar, hP])
  rw [hP] at a1
  rw [map_pow, hD.xi_odd, hodd.neg_one_pow] at a2
  rw [map_pow, w4 _ hD.isCC, hodd.neg_one_pow] at a3
  have h2 := hD.pl_over 2 Nat.prime_two
  obtain ⟨u₀, hu, b1, b2, b3⟩ := X.big2 (D.pl 2) (by exact_mod_cast h2)
  have b4 := (w2 (D.pl 2) (fun h => hD.l_odd (w1 _ _ _ hl.out Nat.prime_two h h2)) u₀ hu).1
  obtain ⟨u, u0, u1, u2, u3⟩ := move D hD X u₀ 1 b2 (by simpa using b1)
  have u1' : Raw.bar D.Psi u = 1 := by rw [Raw.bar, u1]; exact b1
  have u2' : Raw.bar D.ξ u ^ 4 ≠ 1 := by rw [Raw.bar, u2]; exact b3
  rw [b4] at u3
  obtain ⟨t₀, c1, c2, c3⟩ := X.ev
  obtain ⟨t, t0, t1, -, t3⟩ := move D hD X t₀ (-1) c2 (by simpa using c3)
  have t1' : Raw.bar D.Psi t = -1 := by rw [Raw.bar, t1]; exact c3
  rw [c1] at t3
  have a1' : Raw.bar D.Psi a = 1 := by simp [Raw.bar, a1]
  have a2' : Raw.bar D.ξ a = -1 := by simp [Raw.bar, a2]
  have a3' : Raw.bar D.om a = -1 := by simp [Raw.bar, a3]
  by_cases ht : Raw.bar D.ξ t ^ 2 = 1
  · refine ⟨a, u, t * u, a0, a2', a1', a3', u0, u2', u1', u3, mul_mem t0 u0, fun h => u2' ?_, ?_, ?_⟩
    · rw [bar_mul, mul_pow, ht, one_mul] at h
      rw [show 4 = 2 * 2 from rfl, pow_mul, h, one_pow]
    · rw [bar_mul, t1', u1', mul_one]
    · rw [map_mul, t3, u3, mul_one]
  · exact ⟨a, u, t, a0, a2', a1', a3', u0, u2', u1', u3, t0, ht, t1', t3⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.OddPowNe
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem odd_pow_ne {k : Type} [Field k] {x : k} {n : ℕ} (hn : x ^ 2 ^ n = 1) (h4 : x ^ 4 ≠ 1) {m : ℤ} (hm : Odd m) :
    x ^ m ≠ 1 := by
  intro hxm
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hn
  set u := Units.mk0 x hx0 with hu_def
  have hu : u ^ 2 ^ n = 1 := Units.ext (by simpa [u] using hn)
  have hum : u ^ m = 1 := Units.ext (by simpa [u] using hxm)
  obtain ⟨j, -, hoj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hu)
  have hdm : (orderOf u : ℤ) ∣ m := orderOf_dvd_iff_zpow_eq_one.mpr hum
  cases j with
  | zero =>
    rw [pow_zero, orderOf_eq_one_iff] at hoj
    apply h4
    have hx1 : x = 1 := by simpa [u] using congrArg Units.val hoj
    simp [hx1]
  | succ j =>
    have h2 : (2 : ℤ) ∣ m := by
      refine dvd_trans ?_ hdm
      rw [hoj]
      exact_mod_cast dvd_pow_self 2 (Nat.succ_ne_zero j)
    exact (Int.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr h2)

private theorem dist4 {k : Type} [Field k] {x : k} (h1 : (-1 : k) ≠ 1) (h0 : x ≠ 0) (hx : x ^ 2 ≠ 1) :
    Function.Injective (![x * -1, -1, x, 1] : Fin 4 → k) := by
  have h2 : (2 : k) ≠ 0 := by
    intro h
    apply h1
    linear_combination -h
  intro i j h
  fin_cases i <;> fin_cases j <;> simp at h ⊢
  all_goals first
    | exact absurd (by linear_combination h * h) hx
    | exact absurd (by linear_combination (-x - 1) * h) hx
    | exact absurd (by linear_combination (x - 1) * h) hx
    | exact absurd (by linear_combination (-x + 1) * h) hx
    | exact absurd (by linear_combination (x + 1) * h) hx
    | exact h1 h
    | exact h1 h.symm
    | exact h0 ((mul_eq_zero.mp (by linear_combination -h : (2 : k) * x = 0)).resolve_left h2)
    | exact h0 ((mul_eq_zero.mp (by linear_combination h : (2 : k) * x = 0)).resolve_left h2)

private theorem lab_inj (pr : Bool) : Function.Injective (lab pr) := by
  cases pr <;> decide

private theorem lab_surj (pr : Bool) : ∃ i, lab pr i = 3 := by
  cases pr <;> decide

theorem UpperTheory.V.Ws.ok2A :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (X : Set2 D) (T : Tower D), X.On T → ∀ a u t, X.Elts a u t → (∀ w, ∃ g ∈ T.GalL, T.rb w g ≠ Raw.bar D.om (resQ T.F g)) ∧ (∀ w ∈ roots, ∃ g ∈ T.GalL, T.rb w g ≠ 1) ∧ (∀ η : T.GalL →* (ResidueField c.O)ˣ, η ^ 2 = 1 → (∀ g : T.GalL, D.om (resQ T.F g) = 1 → η g = 1) → (∀ i, ∃ j, ∀ g : T.GalL, η g * Raw.bar (chi D T.pr i) (resQ T.F g) = Raw.bar (chi D T.pr j) (resQ T.F g)) → η = 1) ∧ (∃ w ∈ roots, ∀ n : ℕ, 0 < n → n ≤ 4 → ∃ g ∈ T.GalL, T.rb w g ^ n ≠ 1) ∧ (resQ T.F T.g0 = t → ∀ i j, i ≠ j → Raw.bar (chi D T.pr i) (resQ T.F T.g0) ≠ Raw.bar (chi D T.pr j) (resQ T.F T.g0)) := by
  intro Ω _ _ _ l _ c D hD X T hOn a u t hE
  obtain ⟨h1, -, hal, hth, -, -, hrb, -, -⟩ := barFacts D hD
  obtain ⟨n, hn⟩ := X.ord
  have hxord : ∀ g, Raw.bar D.ξ g ^ 2 ^ n = 1 := by
    intro g
    simp only [Raw.bar]
    rw [← map_pow, ← Units.val_pow_eq_pow_val, ← MonoidHom.pow_apply, hn]
    simp
  have hchi : ∀ b i, chi D b i = D.ps (lab b i) := fun b i => rfl
  have lift : ∀ y ∈ X.H ⊓ X.η.ker, ∃ s ∈ T.GalL, resQ T.F s = y := by
    intro y hy
    obtain ⟨s, hs⟩ := exists_resQ (F := T.F) (g := y) (by rw [hOn.1]; exact hy.1)
    refine ⟨s, ?_, hs⟩
    unfold Tower.GalL
    rw [Subgroup.mem_comap, hOn.2, hs]
    exact hy.2
  have hbu : Raw.bar D.om u = 1 := by simp [Raw.bar, hE.u_om]
  have hxu1 : Raw.bar D.ξ u ≠ 1 := by
    intro h
    apply hE.u_xi
    rw [h, one_pow]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro w
    rcases Int.even_or_odd w.1 with he | ho
    · obtain ⟨s, hsG, hs⟩ := lift a hE.a_mem
      refine ⟨s, hsG, ?_⟩
      rw [hrb, hs, hE.a_xi, hE.a_psi, hE.a_om, one_zpow, mul_one, he.neg_one_zpow]
      exact fun h => h1 h.symm
    · obtain ⟨s, hsG, hs⟩ := lift u hE.u_mem
      refine ⟨s, hsG, ?_⟩
      rw [hrb, hs, hE.u_psi, one_zpow, mul_one, hbu]
      exact odd_pow_ne (hxord u) hE.u_xi ho
  · intro w hw
    by_cases ho : Odd w.1
    · obtain ⟨s, hsG, hs⟩ := lift u hE.u_mem
      refine ⟨s, hsG, ?_⟩
      rw [hrb, hs, hE.u_psi, one_zpow, mul_one]
      exact odd_pow_ne (hxord u) hE.u_xi ho
    · obtain ⟨w1, w2⟩ := w
      simp [UpperTheory.V.Ws.roots, oddRoots, wAl, wBe, wTh, wPs] at hw
      obtain ⟨s, hsG, hs⟩ := lift t hE.t_mem
      refine ⟨s, hsG, ?_⟩
      rw [hrb, hs, hE.t_psi]
      rcases hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      all_goals first
        | exact absurd (by decide) ho
        | (split_ifs <;> simpa using h1)
  · intro η hη2 hηom hperm
    obtain ⟨i0, hi0⟩ := lab_surj T.pr
    obtain ⟨j, hj⟩ := hperm i0
    have key : ∀ s : T.GalL, (η s : ResidueField c.O) = Raw.bar (D.ps (lab T.pr j)) (resQ T.F s) := by
      intro s
      have h := hj s
      rw [hchi, hchi, hi0] at h
      have h3 : D.ps 3 = 1 := rfl
      rw [h3] at h
      simpa [Raw.bar] using h
    obtain ⟨su, hsuG, hsu⟩ := lift u hE.u_mem
    obtain ⟨st, hstG, hst⟩ := lift t hE.t_mem
    have hηu : η ⟨su, hsuG⟩ = 1 := hηom _ (by simp only [hsu]; exact hE.u_om)
    have hηt : η ⟨st, hstG⟩ = 1 := hηom _ (by simp only [hst]; exact hE.t_om)
    have ku := key ⟨su, hsuG⟩
    have kt := key ⟨st, hstG⟩
    rw [hηu] at ku
    rw [hηt] at kt
    simp only [hsu] at ku
    simp only [hst] at kt
    generalize lab T.pr j = k at ku kt key
    fin_cases k
    · exfalso
      change _ = Raw.bar D.th u at ku
      simp only [hth, hE.u_psi, mul_one, Units.val_one] at ku
      exact hxu1 ku.symm
    · exfalso
      change _ = Raw.bar D.Psi t at kt
      simp only [hE.t_psi, Units.val_one] at kt
      exact h1 kt.symm
    · exfalso
      change _ = Raw.bar D.al u at ku
      simp only [hal, Units.val_one] at ku
      exact hxu1 ku.symm
    · ext s
      have h0 : D.ps 3 = 1 := rfl
      have := key s
      simp only [Fin.reduceFinMk, Fin.isValue] at this
      rw [h0] at this
      simpa [Raw.bar] using this
  · refine ⟨(1, 0), by simp [UpperTheory.V.Ws.roots, oddRoots, wAl], fun m hm0 hm4 => ?_⟩
    obtain ⟨s, hsG, hs⟩ := lift u hE.u_mem
    refine ⟨s, hsG, ?_⟩
    rw [hrb, hs, hE.u_psi]
    simp only [one_zpow, mul_one, zpow_one]
    interval_cases m
    · simpa using hxu1
    · intro h
      apply hE.u_xi
      rw [show 4 = 2 * 2 by rfl, pow_mul, h, one_pow]
    · have h3 := odd_pow_ne (hxord u) hE.u_xi (m := 3) (by decide)
      simpa using h3
    · exact hE.u_xi
  · intro hg0 i j hij heq
    rw [hg0] at heq
    have hx0 : Raw.bar D.ξ t ≠ 0 := by
      intro h0
      have h := hxord t
      rw [h0, zero_pow (by positivity)] at h
      exact zero_ne_one h
    have hinj := dist4 h1 hx0 hE.t_xi
    have hvals : ∀ k, Raw.bar (D.ps k) t = ![Raw.bar D.ξ t * -1, -1, Raw.bar D.ξ t, 1] k := by
      intro k
      fin_cases k
      · show Raw.bar D.th t = _
        simp [hth, hE.t_psi]
      · show Raw.bar D.Psi t = _
        simp [hE.t_psi]
      · show Raw.bar D.al t = _
        simp [hal]
      · show Raw.bar (1 : G ℚ Ω →* (↥c.O)ˣ) t = _
        simp [Raw.bar]
    rw [hchi, hchi, hvals, hvals] at heq
    exact hij (lab_inj T.pr (hinj heq))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.Ok2B
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.ok2B :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (X : Set2 D) (T : Tower D), X.On T → (∀ A : ValuationSubring Ω, Ine (F := T.F) A ≤ T.GalL) ∧ (∀ A : ValuationSubring Ω, Raw.Away {l} A → ∀ g ∈ Ine (F := T.F) A, D.rbar (resQ T.F g) = 1 → D.ψ (resQ T.F g) = 1) ∧ (∃ m : ℕ, l.Coprime m ∧ ∀ g : G T.F Ω, cycZ T.F Ω l g = 1 → D.ψ (resQ T.F g) ^ m = 1) ∧ ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∀ g ∈ Ine (F := T.F) A, D.rbar (resQ T.F g) = 1 := by
  intro Ω _ _ _ l hl c D hD X T hT
  obtain ⟨hpq, -, hxi, -, -⟩ := away D hD
  obtain ⟨-, -, -, -, -, hrb, -, -, -⟩ := barFacts D hD
  have hH : ∀ g : G T.F Ω, resQ T.F g ∈ X.H := fun g => hT.1 ▸ resQ_mem T.F g
  refine ⟨fun A g hg => ?_, fun A hA g hg h => ?_, ?_, fun A hA g hg => ?_⟩
  · have hg' := (resQ_Ine T.F A g).1 hg
    change resQ T.F g ∈ T.K.fixingSubgroup
    rw [hT.2]
    by_cases hp : A.valuation (X.p : Ω) < 1
    · have hp' : ¬ A.valuation (X.p' : Ω) < 1 := fun h =>
        X.hη'.nm (hpq A _ _ X.hη.prime X.hη'.prime hp h ▸ Finset.mem_insert_self _ _)
      exact (X.mem_H.1 (hH g)).2.1.trans (X.hη'.unr A hp' hg')
    · exact X.hη.unr A hp hg'
  · exact X.kap.kb A hA _ ((resQ_Ine T.F A g).1 hg) ((hrb _).1 h).2 (X.mem_H.1 (hH g)).2.2
  · obtain ⟨m, hm, h⟩ := X.kap.kc
    exact ⟨m, hm, fun g hg => h _ ((resQ_cyc T.F g).trans hg) (X.mem_H.1 (hH g)).2.2⟩
  · have hg' := (resQ_Ine T.F A g).1 hg
    have h3 : ¬ A.valuation (X.p₃ : Ω) < 1 := fun h =>
      X.hφ.nm (hpq A _ _ hl.out X.hφ.prime hA h ▸ hD.l_mem)
    have h1 : D.ξ (resQ T.F g) = 1 := hxi A hA hg'
    have h2 : X.φ (resQ T.F g) = 1 := X.hφ.unr A h3 hg'
    refine (hrb _).2 ⟨?_, ?_⟩
    · rw [Raw.bar, h1, Units.val_one, map_one]
    · rw [(X.mem_H.1 (hH g)).1, h2, Units.val_one, Int.cast_one]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.Two2
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.two2 :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (X : Set2 D) (T : Tower D), X.On T → ∀ k₀ : IntermediateField ℚ Ω, Module.finrank ℚ k₀ = 2 → IsTotallyReal k₀ → k₀.fixingSubgroup = X.φ.ker → T.Two := by
  intro Ω _ _ _ l hl c D hD X T hOn k₀ hk hr hfix
  obtain ⟨hne, -, -, -, -, -, hrb, -, -⟩ := barFacts D hD
  obtain ⟨-, -, -, -, haw⟩ := away D hD
  have hH : ∀ g : G T.F Ω, Raw.bar D.Psi (resQ T.F g) = ((X.φ (resQ T.F g) : ℤ) : ResidueField c.O) := fun g =>
    (X.mem_H.1 (hOn.1 ▸ resQ_mem T.F g)).1
  have hps : ∀ g : G T.F Ω, T.rb wPs g = ((X.φ (resQ T.F g) : ℤ) : ResidueField c.O) := fun g => by
    rw [hrb, hH]
    rcases Int.units_eq_one_or (X.φ (resQ T.F g)) with h | h <;> rw [h] <;> cases T.pr <;> simp [wPs]
  have hal : ∀ g : G T.F Ω, T.rb wAl g = Raw.bar D.ξ (resQ T.F g) := fun g => by
    rw [hrb]
    cases T.pr <;> simp [wAl]
  have hiff : ∀ g : G T.F Ω, T.rb wPs g = 1 ↔ X.φ (resQ T.F g) = 1 := fun g => by
    rw [hps]
    rcases Int.units_eq_one_or (X.φ (resQ T.F g)) with h | h <;> rw [h]
    · simp
    · constructor
      · intro h'
        exact absurd (by simpa using h') hne
      · intro h'
        exact absurd h' (by decide)
  have key : ∀ q ∈ D.S, ∀ A : ValuationSubring Ω, A.valuation (q : Ω) < 1 → ∀ g ∈ Dec (F := ℚ) A,
      Raw.bar D.Psi g = 1 → X.κ g = 1 → ∃ s : G T.F Ω, resQ T.F s = g := fun q hq A hA g hg h1 h2 => by
    have a : X.φ g = 1 := X.hφ.split q hq A hA hg
    have b : X.η g = 1 := X.hη.split q (Finset.mem_insert_of_mem hq) A hA hg
    have d : X.η' g = 1 := X.hη'.split q (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hq)) A hA hg
    refine exists_resQ ?_
    rw [hOn.1, X.mem_H]
    refine ⟨?_, b.trans d.symm, h2⟩
    rw [h1, a]
    simp
  refine ⟨fun g => ?_, fun A g hg => ?_, fun A hA g hg => ?_, ⟨k₀, hk, hr, fun p hp A hA => ?_, fun g => ?_⟩,
    X.ord, X.xi, fun A hA => ?_, fun A hA => ?_⟩
  · rw [hps]
    rcases Int.units_eq_one_or (X.φ (resQ T.F g)) with h | h <;> rw [h] <;> simp
  · have hg' := (resQ_Ine T.F A g).1 hg
    by_cases hA : A.valuation (X.p₃ : Ω) < 1
    · rw [hps, ← hH, Raw.bar, ((haw A X.p₃ X.hφ.prime X.hφ.nm hA).2 _ hg').1]
      simp
    · exact (hiff g).2 (X.hφ.unr A hA hg')
  · exact (hiff g).2 (X.hφ.split l hD.l_mem A hA ((resQ_Dec T.F A g).1 hg))
  · rw [hfix]
    refine X.hφ.split p ?_ A hA
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact hD.two_mem
    · exact hD.l_mem
  · rw [hfix, MonoidHom.mem_ker]
    exact hiff g
  · obtain ⟨g, hg, h1, h2, h3⟩ := X.bigL A hA
    obtain ⟨s, rfl⟩ := key l hD.l_mem A hA g hg h1 h2
    exact ⟨s, (resQ_Dec T.F A s).2 hg, by rw [hal]; exact h3⟩
  · obtain ⟨g, hg, h1, h2, h3⟩ := X.big2 A hA
    obtain ⟨s, rfl⟩ := key 2 hD.two_mem A (by exact_mod_cast hA) g (Ine_le_Dec A hg) h1 h2
    exact ⟨s, (resQ_Ine T.F A s).2 hg, by rw [hal]; exact h3⟩
end

