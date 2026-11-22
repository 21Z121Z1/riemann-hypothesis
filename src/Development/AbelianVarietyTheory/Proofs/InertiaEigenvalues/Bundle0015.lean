import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntertwiningMapNeZeroOfIsotypicIrreducible
section
namespace GlobalTheory.IsoSep

open Representation

theorem main : ∀ (H V W : Type) [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ H V) (σ : Representation ℂ H W), σ.IsIrreducible → (⨆ f : σ.IntertwiningMap ρ, LinearMap.range f.toLinearMap) = ⊤ → (∀ (W' : Type) [AddCommGroup W'] [Module ℂ W'] (σ' : Representation ℂ H W'), σ'.IsIrreducible → ∀ f' : σ'.IntertwiningMap ρ, f' ≠ 0 → Nonempty (σ.Equiv σ')) → ∀ v : V, v ≠ 0 → ∃ p : ρ.IntertwiningMap σ, p v ≠ 0 := by
  intro H V W _ _ _ _ _ ρ σ hσ hsum hiso v hv
  haveI := hσ
  let e := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)

  have hatom : ∀ f : σ.IntertwiningMap ρ, f ≠ 0 → IsAtom f.range := by
    intro f hf
    refine ⟨?_, ?_⟩
    · intro h
      apply hf
      ext w
      have hw : f w ∈ f.range := ⟨w, rfl⟩
      rw [h] at hw
      exact hw
    · intro U hU
      let U' : Subrepresentation σ := ⟨U.toSubmodule.comap f.toLinearMap, fun g w hw => by
        show f (σ g w) ∈ U.toSubmodule
        rw [f.isIntertwining]
        exact U.apply_mem_toSubmodule g hw⟩
      rcases eq_bot_or_eq_top U' with h | h
      · refine le_antisymm (fun x hx => ?_) bot_le
        obtain ⟨w, rfl⟩ := hU.le hx
        have hw : w ∈ U'.toSubmodule := hx
        rw [h] at hw
        have hw0 : w = 0 := (Submodule.mem_bot ℂ).1 hw
        show f w ∈ (⊥ : Submodule ℂ V)
        rw [hw0, map_zero]
        exact zero_mem _
      · exfalso
        refine hU.ne (le_antisymm hU.le ?_)
        rintro _ ⟨w, rfl⟩
        have hw : w ∈ U'.toSubmodule := by rw [h]; trivial
        exact hw

  have hss : IsSemisimpleModule (MonoidAlgebra ℂ H) ρ.asModule := by
    apply IsSemisimpleModule.of_sSup_simples_eq_top
    refine eq_top_iff.2 fun x _ => ?_
    have hx : ρ.asModuleEquiv x ∈ (⨆ f : σ.IntertwiningMap ρ, LinearMap.range f.toLinearMap) := by
      rw [hsum]; trivial
    have key := Submodule.iSup_induction _ (motive := fun y : V => ρ.asModuleEquiv.symm y ∈
      sSup {m : Submodule (MonoidAlgebra ℂ H) ρ.asModule | IsSimpleModule (MonoidAlgebra ℂ H) m}) hx
      (fun f y hy => by
        by_cases hf : f = 0
        · subst hf
          obtain ⟨w, rfl⟩ := hy
          simp
        · refine le_sSup (a := e f.range) ?_ ?_
          · exact isSimpleModule_iff_isAtom.2 ((e.isAtom_iff _).2 (hatom f hf))
          · exact hy)
      (by simp) (fun a b ha hb => by rw [map_add]; exact add_mem ha hb)
    simpa using key

  let K : Submodule (MonoidAlgebra ℂ H) ρ.asModule := Submodule.span _ {ρ.asModuleEquiv.symm v}
  have hK : K ≠ ⊥ := by
    intro h
    apply hv
    have hm : ρ.asModuleEquiv.symm v ∈ K := Submodule.subset_span rfl
    rw [h, Submodule.mem_bot] at hm
    simpa using hm
  obtain ⟨N, hN, hNK⟩ := (eq_bot_or_exists_atom_le K).resolve_left hK
  obtain ⟨C, hC⟩ := exists_isCompl N
  let N' := e.symm N
  let C' := e.symm C
  have hC' : IsCompl N' C' := (e.isCompl_iff).2 (by
    simp only [N', C', OrderIso.apply_symm_apply]; exact hC)
  have hN' : IsAtom N' := (e.isAtom_iff N').1 (by simp only [N', OrderIso.apply_symm_apply]; exact hN)
  have hc : IsCompl N'.toSubmodule C'.toSubmodule := by
    constructor
    · rw [disjoint_iff]; exact congrArg Subrepresentation.toSubmodule hC'.inf_eq_bot
    · rw [codisjoint_iff]; exact congrArg Subrepresentation.toSubmodule hC'.sup_eq_top
  let P := Submodule.projectionOnto N'.toSubmodule C'.toSubmodule hc
  let τ := N'.toRepresentation
  let p : ρ.IntertwiningMap τ := ⟨P, fun g => LinearMap.ext fun x => by
    have hx : x ∈ N'.toSubmodule ⊔ C'.toSubmodule := by rw [hc.sup_eq_top]; trivial
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    have h1 : P (ρ g y) = ⟨ρ g y, N'.apply_mem_toSubmodule g hy⟩ :=
      Submodule.projectionOnto_apply_left hc ⟨ρ g y, N'.apply_mem_toSubmodule g hy⟩
    have h2 : P (ρ g z) = 0 :=
      Submodule.projectionOnto_apply_right hc ⟨ρ g z, C'.apply_mem_toSubmodule g hz⟩
    have h3 : P y = ⟨y, hy⟩ := Submodule.projectionOnto_apply_left hc ⟨y, hy⟩
    have h4 : P z = 0 := Submodule.projectionOnto_apply_right hc ⟨z, hz⟩
    simp only [LinearMap.coe_comp, Function.comp_apply, map_add, h1, h2, h3, h4, add_zero, map_zero]
    rfl⟩
  have hpv : p v ≠ 0 := by
    intro h0
    have hvC : v ∈ C'.toSubmodule := (Submodule.projectionOnto_apply_eq_zero_iff hc).1 h0
    have hKC : K ≤ C := by
      refine Submodule.span_le.2 ?_
      rintro _ rfl
      exact hvC
    have hNC : N ≤ N ⊓ C := le_inf le_rfl (hNK.trans hKC)
    rw [hC.inf_eq_bot] at hNC
    exact hN.1 (le_bot_iff.1 hNC)

  have hN'0 : N'.toSubmodule ≠ ⊥ := fun h => hN'.1 (Subrepresentation.toSubmodule_injective h)
  obtain ⟨x0, hx0, hx00⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN'0
  have hτ : τ.IsIrreducible := by
    refine { exists_pair_ne := ⟨⊥, ⊤, fun h => ?_⟩, eq_bot_or_eq_top := fun U => ?_ }
    · have hm : (⟨x0, hx0⟩ : N'.toSubmodule) ∈ (⊤ : Subrepresentation τ).toSubmodule := trivial
      rw [← h] at hm
      have : (⟨x0, hx0⟩ : N'.toSubmodule) = 0 := (Submodule.mem_bot ℂ).1 hm
      exact hx00 (congrArg Subtype.val this)
    · let U'' : Subrepresentation ρ := ⟨U.toSubmodule.map N'.toSubmodule.subtype, fun g x hx => by
        obtain ⟨y, hy, rfl⟩ := hx
        exact ⟨τ g y, U.apply_mem_toSubmodule g hy, rfl⟩⟩
      have hle : U'' ≤ N' := by
        rintro _ ⟨y, -, rfl⟩
        exact y.2
      rcases hN'.le_iff.1 hle with h | h
      · left
        refine Subrepresentation.toSubmodule_injective (eq_bot_iff.2 fun y hy => ?_)
        have hm : (y : V) ∈ U''.toSubmodule := ⟨y, hy, rfl⟩
        rw [h] at hm
        have h0 : (y : V) = 0 := (Submodule.mem_bot ℂ).1 hm
        exact (Submodule.mem_bot ℂ).2 (Subtype.ext h0)
      · right
        refine Subrepresentation.toSubmodule_injective (eq_top_iff.2 fun y _ => ?_)
        have hm : (y : V) ∈ U''.toSubmodule := by rw [h]; exact y.2
        obtain ⟨z, hz, hzy⟩ := hm
        have : z = y := Subtype.ext hzy
        rw [← this]
        exact hz
  let f' : τ.IntertwiningMap ρ := ⟨N'.toSubmodule.subtype, fun g => LinearMap.ext fun x => rfl⟩
  have hf' : f' ≠ 0 := by
    intro h
    have := congrArg (fun q : τ.IntertwiningMap ρ => q ⟨x0, hx0⟩) h
    exact hx00 this
  obtain ⟨eqv⟩ := hiso _ τ hτ f' hf'
  refine ⟨eqv.symm.toIntertwiningMap.comp p, fun h => hpv ?_⟩
  have := congrArg eqv h
  simpa using this

end GlobalTheory.IsoSep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvariantMatrixLiftOfAdicComplete
section
namespace GlobalTheory.InvariantLift

variable {G : Type} [Group G] {A : Type} [CommRing A] {r : ℕ}

theorem average_step (σ : G → A →+* A) (hσ : ∀ g h a, σ (g * h) a = σ g (σ h a))
    (M : G →* Matrix (Fin r) (Fin r) A) (hM : ∀ g h i j, σ g (M h i j) = M h i j)
    (N : Subgroup G) [hN : N.Normal] [Finite (G ⧸ N)] (τ : A) (hτ : ∀ g ∈ N, σ g τ = τ)
    (hτ1 : ∑ᶠ x : G ⧸ N, σ x.out τ = 1) (c d : A) (hd : ∀ g ∈ N, ∀ i j, d ∣ (M g - 1) i j)
    (W : Matrix (Fin r) (Fin r) A) (hW : ∀ g ∈ N, W.map (σ g) = W)
    (hc : ∀ g i j, c ∣ (M g * W.map (σ g) - W) i j) :
    ∃ W' : Matrix (Fin r) (Fin r) A, (∀ i j, c ∣ (W - W') i j) ∧ (∀ g ∈ N, W'.map (σ g) = W') ∧
      ∀ g i j, d ∣ (M g * W'.map (σ g) - W') i j := by
  classical
  haveI : Fintype (G ⧸ N) := Fintype.ofFinite _

  have dl : ∀ (e : A) (X : Matrix (Fin r) (Fin r) A), (∀ i j, e ∣ X i j) →
      ∀ (Y : Matrix (Fin r) (Fin r) A) i j, e ∣ (X * Y) i j := by
    intro e X hX Y i j
    rw [Matrix.mul_apply]
    exact Finset.dvd_sum fun k _ => (hX i k).mul_right _
  have dr : ∀ (e : A) (Y : Matrix (Fin r) (Fin r) A), (∀ i j, e ∣ Y i j) →
      ∀ (X : Matrix (Fin r) (Fin r) A) i j, e ∣ (X * Y) i j := by
    intro e Y hY X i j
    rw [Matrix.mul_apply]
    exact Finset.dvd_sum fun k _ => (hY k j).mul_left _

  have hfix : ∀ a : A, (∀ m ∈ N, σ m a = a) → ∀ g, ∀ n ∈ N, σ n (σ g a) = σ g a := by
    intro a ha g n hn
    have hm : g⁻¹ * n * g ∈ N := by simpa using hN.conj_mem n hn g⁻¹
    rw [← hσ, show n * g = g * (g⁻¹ * n * g) by group, hσ, ha _ hm]
  obtain ⟨U, hU⟩ : ∃ U : Matrix (Fin r) (Fin r) A, U = τ • W := ⟨_, rfl⟩
  have hUfix : ∀ m ∈ N, ∀ k l, σ m (U k l) = U k l := by
    intro m hm k l
    have hWe : σ m (W k l) = W k l := congrFun (congrFun (hW m hm) k) l
    rw [hU, Matrix.smul_apply, smul_eq_mul, map_mul, hτ m hm, hWe]
  have hUl : ∀ g, ∀ n ∈ N, U.map (σ (n * g)) = U.map (σ g) := by
    intro g n hn
    ext k l
    simp only [Matrix.map_apply, hσ]
    exact hfix _ (fun m hm => hUfix m hm k l) g n hn
  have hUr : ∀ g, ∀ n ∈ N, U.map (σ (g * n)) = U.map (σ g) := by
    intro g n hn
    ext k l
    simp only [Matrix.map_apply, hσ, hUfix n hn]
  have hMfix : ∀ g h, (M h).map (σ g) = M h := by
    intro g h
    ext i j
    exact hM g h i j
  have hUmap : ∀ g h, (U.map (σ h)).map (σ g) = U.map (σ (g * h)) := by
    intro g h
    ext i j
    simp [hσ]
  have hsum : ∀ (f : A →+* A) (X : G ⧸ N → Matrix (Fin r) (Fin r) A),
      (∑ x, X x).map f = ∑ x, (X x).map f := by
    intro f X
    ext i j
    simp [Matrix.sum_apply, map_sum]

  refine ⟨∑ x : G ⧸ N, M x.out * U.map (σ x.out), ?_, ?_, ?_⟩
  · intro i j
    have h1 : ∑ x : G ⧸ N, σ x.out τ = 1 := by
      rw [← finsum_eq_sum_of_fintype]
      exact hτ1
    have hent : ∀ x : G ⧸ N, (M x.out * U.map (σ x.out)) i j =
        σ x.out τ * (M x.out * W.map (σ x.out)) i j := by
      intro x
      simp only [hU, Matrix.mul_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul,
        Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    have hsplit : (W - ∑ x : G ⧸ N, M x.out * U.map (σ x.out)) i j =
        ∑ x : G ⧸ N, σ x.out τ * (W i j - (M x.out * W.map (σ x.out)) i j) := by
      rw [Matrix.sub_apply, Matrix.sum_apply, Finset.sum_congr rfl (fun x _ => hent x)]
      simp only [mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, h1, one_mul]
    rw [hsplit]
    refine Finset.dvd_sum fun x _ => dvd_mul_of_dvd_right ?_ _
    exact dvd_sub_comm.mp (by simpa only [Matrix.sub_apply] using hc x.out i j)
  · intro n hn
    rw [hsum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Matrix.map_mul, hMfix, hUmap, hUl _ n hn]
  · intro g i j
    have hmul : M g * (∑ x : G ⧸ N, M x.out * U.map (σ x.out)).map (σ g) =
        ∑ x : G ⧸ N, M (g * x.out) * U.map (σ (g * x.out)) := by
      rw [hsum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Matrix.map_mul, hMfix, hUmap, map_mul, mul_assoc]
    have hre : ∑ x : G ⧸ N, M x.out * U.map (σ x.out) =
        ∑ x : G ⧸ N, M (g • x).out * U.map (σ (g • x).out) :=
      (Equiv.sum_comp (MulAction.toPerm g) (fun y : G ⧸ N => M y.out * U.map (σ y.out))).symm
    rw [hmul, hre, ← Finset.sum_sub_distrib, Matrix.sum_apply]
    refine Finset.dvd_sum fun x _ => ?_
    obtain ⟨n, hn, hgx⟩ : ∃ n ∈ N, g * x.out = (g • x).out * n := by
      refine ⟨((g • x).out)⁻¹ * (g * x.out), ?_, (mul_inv_cancel_left _ _).symm⟩
      rw [← QuotientGroup.eq]
      simp only [QuotientGroup.out_eq']
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
      simp only [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.mk_mul, QuotientGroup.out_eq',
        Quotient.out_eq]
    rw [hgx, map_mul, hUr _ n hn]
    have hfac : M (g • x).out * M n * U.map (σ (g • x).out) - M (g • x).out * U.map (σ (g • x).out)
        = M (g • x).out * ((M n - 1) * U.map (σ (g • x).out)) := by
      noncomm_ring
    rw [hfac]
    exact dr d _ (dl d _ (fun i' j' => by simpa [Matrix.sub_apply] using hd n hn i' j') _) _ i j

theorem exists_invariant_lift : ∀ (G : Type) [Group G] (A : Type) [CommRing A] (π : A), IsAdicComplete (Ideal.span {π}) A → ∀ (σ : G → A →+* A), (∀ g h a, σ (g * h) a = σ g (σ h a)) → (∀ g, σ g π = π) → ∀ (r : ℕ) (M : G →* Matrix (Fin r) (Fin r) A), (∀ g h i j, σ g (M h i j) = M h i j) → ∀ (S : Set (Subgroup G)), (∀ N ∈ S, N.Normal ∧ Finite (G ⧸ N) ∧ ∃ τ : A, (∀ g ∈ N, σ g τ = τ) ∧ ∑ᶠ x : G ⧸ N, σ x.out τ = 1) → (∀ N ∈ S, ∀ k : ℕ, ∃ N' ∈ S, N' ≤ N ∧ ∀ g ∈ N', ∀ i j, π ^ k ∣ (M g - 1) i j) → ∀ (W₀ : Matrix (Fin r) (Fin r) A), (∃ N ∈ S, ∀ g ∈ N, W₀.map (σ g) = W₀) → (∀ g i j, π ∣ (M g * W₀.map (σ g) - W₀) i j) → ∃ W : Matrix (Fin r) (Fin r) A, (∀ i j, π ∣ (W - W₀) i j) ∧ ∀ g, M g * W.map (σ g) = W := by
  intro G _ A _ π hA σ hσ hσπ r M hM S hS hSk W₀ hW₀ hW₀c
  classical

  have hstep : ∀ (k : ℕ) (N : Subgroup G) (W : Matrix (Fin r) (Fin r) A), N ∈ S →
      (∀ g ∈ N, W.map (σ g) = W) → (∀ g i j, π ^ (k + 1) ∣ (M g * W.map (σ g) - W) i j) →
      ∃ (N' : Subgroup G) (W' : Matrix (Fin r) (Fin r) A), N' ∈ S ∧ (∀ g ∈ N', W'.map (σ g) = W') ∧
        (∀ g i j, π ^ (k + 1 + 1) ∣ (M g * W'.map (σ g) - W') i j) ∧
        ∀ i j, π ^ (k + 1) ∣ (W - W') i j := by
    intro k N W hNS hWN hWc
    obtain ⟨N', hN'S, hN'N, hN'd⟩ := hSk N hNS (k + 1 + 1)
    obtain ⟨hN'n, hN'f, τ, hτ, hτ1⟩ := hS N' hN'S
    haveI := hN'n
    haveI := hN'f
    obtain ⟨W', h1, h2, h3⟩ := GlobalTheory.InvariantLift.average_step σ hσ M hM N' τ hτ hτ1
      (π ^ (k + 1)) (π ^ (k + 1 + 1)) hN'd W (fun g hg => hWN g (hN'N hg)) hWc
    exact ⟨N', W', hN'S, h2, h3, h1⟩
  choose! Nf Wf hNf hWf hcf hdf using hstep
  obtain ⟨N₀, hN₀S, hN₀W⟩ := hW₀
  obtain ⟨seq, hseq0, hseqs⟩ : ∃ seq : ℕ → Subgroup G × Matrix (Fin r) (Fin r) A,
      seq 0 = (N₀, W₀) ∧ ∀ k, seq (k + 1) = (Nf k (seq k).1 (seq k).2, Wf k (seq k).1 (seq k).2) :=
    ⟨fun k => Nat.rec (N₀, W₀) (fun k q => (Nf k q.1 q.2, Wf k q.1 q.2)) k, rfl, fun _ => rfl⟩
  have hP : ∀ k, (seq k).1 ∈ S ∧ (∀ g ∈ (seq k).1, (seq k).2.map (σ g) = (seq k).2) ∧
      ∀ g i j, π ^ (k + 1) ∣ (M g * (seq k).2.map (σ g) - (seq k).2) i j := by
    intro k
    induction k with
    | zero => exact ⟨by simp [hseq0, hN₀S], by simpa [hseq0] using hN₀W,
        by simpa [hseq0] using hW₀c⟩
    | succ k ih =>
      rw [hseqs]
      exact ⟨hNf k _ _ ih.1 ih.2.1 ih.2.2, hWf k _ _ ih.1 ih.2.1 ih.2.2, hcf k _ _ ih.1 ih.2.1 ih.2.2⟩
  have hd : ∀ k i j, π ^ (k + 1) ∣ (seq k).2 i j - (seq (k + 1)).2 i j := by
    intro k i j
    have := hdf k _ _ (hP k).1 (hP k).2.1 (hP k).2.2 i j
    rw [hseqs]
    simpa [Matrix.sub_apply] using this
  have hcauchy : ∀ m n, m ≤ n → ∀ i j, π ^ m ∣ (seq m).2 i j - (seq n).2 i j := by
    intro m n hmn i j
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have e : (seq m).2 i j - (seq (n + 1)).2 i j =
          ((seq m).2 i j - (seq n).2 i j) + ((seq n).2 i j - (seq (n + 1)).2 i j) := by ring
      rw [e]
      exact dvd_add ih ((pow_dvd_pow π (by omega)).trans (hd n i j))

  have hmod : ∀ (n : ℕ) (x y : A),
      x ≡ y [SMOD ((Ideal.span {π}) ^ n • (⊤ : Submodule A A))] ↔ π ^ n ∣ x - y := by
    intro n x y
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
  have hlim : ∀ i j, ∃ L : A, ∀ n, π ^ n ∣ (seq n).2 i j - L := by
    intro i j
    obtain ⟨L, hL⟩ := hA.toIsPrecomplete.prec (f := fun n => (seq n).2 i j)
      (fun {m n} hmn => (hmod m _ _).mpr (hcauchy m n hmn i j))
    exact ⟨L, fun n => (hmod n _ _).mp (hL n)⟩
  choose L hL using hlim
  refine ⟨Matrix.of L, ?_, ?_⟩
  · intro i j
    have a := hd 0 i j
    have b := hL i j 1
    rw [hseq0] at a
    simp only [zero_add, pow_one] at a b
    have c : π ∣ W₀ i j - L i j := by
      have e : W₀ i j - L i j = (W₀ i j - (seq 1).2 i j) + ((seq 1).2 i j - L i j) := by ring
      rw [e]
      exact dvd_add a b
    simpa [Matrix.sub_apply] using dvd_sub_comm.mp c
  · intro g
    ext i j
    apply sub_eq_zero.mp
    rw [← Matrix.sub_apply]
    apply hA.toIsHausdorff.haus
    intro n
    rw [hmod, sub_zero]
    have key : (M g * (Matrix.of L).map (σ g) - Matrix.of L) i j =
        (∑ k, M g i k * σ g (L k j - (seq n).2 k j)) +
          (M g * (seq n).2.map (σ g) - (seq n).2) i j + ((seq n).2 i j - L i j) := by
      simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply, map_sub,
        mul_sub, Finset.sum_sub_distrib]
      ring
    rw [key]
    refine dvd_add (dvd_add (Finset.dvd_sum fun k _ => ?_) ?_) (hL i j n)
    · obtain ⟨e, he⟩ := dvd_sub_comm.mp (hL k j n)
      refine dvd_mul_of_dvd_right ⟨σ g e, ?_⟩ _
      rw [he, map_mul, map_pow, hσπ]
    · exact (pow_dvd_pow π (Nat.le_succ n)).trans ((hP n).2.2 g i j)

end GlobalTheory.InvariantLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsComplOfSaturated
section
namespace GlobalTheory.SaturatedComplement

theorem exists_isCompl_of_saturated {O M : Type} [CommRing O] [IsDomain O]
    [IsPrincipalIdealRing O] [AddCommGroup M] [Module O M] [Module.Finite O M]
    (N : Submodule O M) (h : ∀ (a : O) (x : M), a ≠ (0 : O) → a • x ∈ N → x ∈ N) :
    ∃ C : Submodule O M, IsCompl N C := by
  have htf : Module.IsTorsionFree O (M ⧸ N) := by
    rw [Module.isTorsionFree_iff_smul_eq_zero]
    intro a q hq
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective N q
    by_cases ha : a = 0
    · exact Or.inl ha
    · right
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hq
      rw [Submodule.Quotient.mk_eq_zero]
      exact h a x ha hq
  obtain ⟨s, hs⟩ := Module.projective_lifting_property N.mkQ LinearMap.id N.mkQ_surjective
  have hsec : ∀ q, N.mkQ (s q) = q := fun q => by
    simpa using LinearMap.congr_fun hs q
  refine ⟨LinearMap.range s, ?_, ?_⟩
  · rw [Submodule.disjoint_def]
    rintro x hxN ⟨q, rfl⟩
    have hq : q = 0 := by
      rw [← hsec q, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hxN
    rw [hq, map_zero]
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    have hx : x - s (N.mkQ x) ∈ N := by
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, ← Submodule.mkQ_apply,
        ← Submodule.mkQ_apply, hsec, sub_self]
    have := Submodule.add_mem_sup hx (LinearMap.mem_range_self s (N.mkQ x))
    simpa using this

end GlobalTheory.SaturatedComplement
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsNonarchimedeanLocalFieldSpectralNorm
section
open ValuativeRel

namespace GlobalTheory

theorem exists_isNonarchimedeanLocalField_spectralNorm :
    ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [CompleteSpace F]
      [LocallyCompactSpace F] (K : Type) [Field K] [Algebra F K] [FiniteDimensional F K],
      ∃ (_ : ValuativeRel K) (_ : TopologicalSpace K), IsNonarchimedeanLocalField K ∧
        ∀ x y : K, x ≤ᵥ y ↔ spectralNorm F K x ≤ spectralNorm F K y := by
  intro F _ _ _ _ K _ _ _
  letI nK : NontriviallyNormedField K := spectralNorm.nontriviallyNormedField F K
  haveI : IsUltrametricDist K := IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
    (isNonarchimedean_spectralNorm (K := F) (L := K))
  letI rel : ValuativeRel K := ValuativeRel.ofValuation (NormedField.valuation (K := K))
  refine ⟨rel, inferInstance, ?_, fun x y => Iff.rfl⟩
  haveI : ProperSpace F := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  have hc : (NormedField.valuation (K := K)).Compatible := Valuation.Compatible.ofValuation _
  refine { toIsValuativeTopology := ?_, toLocallyCompactSpace := ?_, toIsNontrivial := ?_ }
  · exact IsValuativeTopology.of_mem_nhds_zero_iff_vle (NormedField.valuation (K := K))
      (fun {s} => (NormedField.toValued (K := K)).is_topological_valuation s)
  · letI : NormedSpace F K := spectralNorm.normedSpace F K
    haveI : ProperSpace K := FiniteDimensional.proper F K
    infer_instance
  · rw [isNontrivial_iff_isNontrivial (NormedField.valuation (K := K))]
    infer_instance

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsPrimitiveRootSubIsUnitOfDvdSubOne
section
open PowerSeries

namespace GlobalTheory

open IsLocalRing Polynomial in

theorem exists_isPrimitiveRoot_sub_isUnit_of_dvd_sub_one {l : ℕ} {O : Type} [CommRing O]
    [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (hl : l.Prime) (hu : ¬ IsUnit (l : O)) (e : ℕ) (he : e ∣ l - 1) :
    ∃ ω : O, IsPrimitiveRoot ω e ∧
      ∀ i j : ℕ, i < e → j < e → i ≠ j → IsUnit (ω ^ i - ω ^ j) := by
  classical
  have : Fact l.Prime := ⟨hl⟩
  have hl1 : l - 1 ≠ 0 := by have := hl.two_le; omega
  have he0 : e ≠ 0 := by rintro rfl; exact hl1 (zero_dvd_iff.1 he)
  have hel : e < l := by have := Nat.le_of_dvd (Nat.pos_of_ne_zero hl1) he; omega

  have hlk : ((l : ℕ) : ResidueField O) = 0 := by
    have h : residue O (l : O) = 0 := (residue_eq_zero_iff _).2 ((mem_maximalIdeal _).2 hu)
    simpa using h
  have : CharP (ResidueField O) l := (CharP.charP_iff_prime_eq_zero hl).2 hlk

  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod l)ˣ)
  have hg' : IsPrimitiveRoot g (l - 1) := by
    have h := IsPrimitiveRoot.orderOf g
    rwa [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units] at h
  have hd : (l - 1) / e ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hl1) he) (Nat.pos_of_ne_zero he0)).ne'
  have hζ : IsPrimitiveRoot ((g ^ ((l - 1) / e) : (ZMod l)ˣ) : ZMod l) e := by
    have h := hg'.pow_of_dvd hd (Nat.div_dvd_of_dvd he)
    rw [Nat.div_div_self he hl1] at h
    exact IsPrimitiveRoot.coe_units_iff.2 h
  have hζk := hζ.map_of_injective (f := ZMod.castHom (dvd_refl l) (ResidueField O))
    (RingHom.injective _)
  obtain ⟨ω₀, hω₀⟩ := residue_surjective
    (ZMod.castHom (dvd_refl l) (ResidueField O) ((g ^ ((l - 1) / e) : (ZMod l)ˣ) : ZMod l))
  rw [← hω₀] at hζk

  have heu : IsUnit (e : O) := by
    rw [← residue_ne_zero_iff_isUnit, map_natCast]
    intro h
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero he0) ((CharP.cast_eq_zero_iff _ l e).1 h)
    omega
  have hω₀u : IsUnit ω₀ := (residue_ne_zero_iff_isUnit _).1 (hζk.ne_zero he0)
  obtain ⟨ω, hroot, hsub⟩ := HenselianRing.is_henselian (I := maximalIdeal O)
    (Polynomial.X ^ e - Polynomial.C 1 : O[X]) (monic_X_pow_sub_C 1 he0) ω₀
    (by
      rw [← residue_eq_zero_iff]
      simp [hζk.pow_eq_one])
    (by
      have h : IsUnit ((e : O) * ω₀ ^ (e - 1)) := heu.mul (hω₀u.pow _)
      simpa [derivative_X_pow] using h.map (Ideal.Quotient.mk (maximalIdeal O)))
  have hres : residue O ω = residue O ω₀ := by
    rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]; exact hsub
  have hωe : ω ^ e = 1 := by
    have h := hroot.eq_zero
    simpa [sub_eq_zero] using h
  refine ⟨ω, ⟨hωe, fun k hk => hζk.dvd_of_pow_eq_one k ?_⟩, fun i j hi hj hij => ?_⟩
  · rw [← hres, ← map_pow, hk, map_one]
  · rw [← residue_ne_zero_iff_isUnit, map_sub, map_pow, map_pow, hres, sub_ne_zero]
    exact fun h => hij (hζk.pow_inj hi hj h)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLimitFamilyOfFiniteCoefficients
section
open scoped BigOperators

namespace GlobalTheory

theorem exists_limit_family_of_finite_coefficients (σ I R : Type) [Finite σ] [Finite I] [Finite R]
    (F : ℕ → I → (σ →₀ ℕ) → R) :
    ∃ G : I → (σ →₀ ℕ) → R, ∀ N M₀ : ℕ, ∃ M, M₀ ≤ M ∧
      ∀ x m, m.degree ≤ N → F M x m = G x m := by
  let _ : TopologicalSpace R := ⊥
  have : DiscreteTopology R := ⟨rfl⟩

  obtain ⟨G, hG⟩ : ∃ G : I → (σ →₀ ℕ) → R, MapClusterPt G Filter.atTop F :=
    exists_clusterPt_of_compactSpace _
  refine ⟨G, fun N M₀ => ?_⟩

  have hnhds : ∀ᶠ H in nhds G, ∀ x, ∀ m ∈ {m : σ →₀ ℕ | m.degree ≤ N}, H x m = G x m := by
    refine Filter.eventually_all.2 fun x => ?_
    refine ((Finsupp.finite_of_degree_le N).eventually_all).2 fun m _ => ?_
    have hc : Continuous fun H : I → (σ →₀ ℕ) → R => H x m :=
      (continuous_apply m).comp (continuous_apply x)
    exact hc.continuousAt.eventually (isOpen_discrete {G x m} |>.mem_nhds rfl)
  obtain ⟨M, hM, hFM⟩ := Filter.frequently_atTop.1 (hG.frequently hnhds) M₀
  exact ⟨M, hM, fun x m hm => hFM x m hm⟩

end GlobalTheory
end

