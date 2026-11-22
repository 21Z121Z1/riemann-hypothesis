import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichmullerDistinguishedRegularSequence
section
open scoped NNReal

namespace GlobalTheory

theorem teichmuller_dvd_of_dvd_natCast_mul (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O]
    [IsDomain O] [CharP O l] [PerfectRing O l] (x : O) (hx : x ≠ 0) (a : WittVector l O)
    (h : WittVector.teichmuller l x ∣ ((l : ℕ) : WittVector l O) * a) :
    WittVector.teichmuller l x ∣ a := by
  obtain ⟨b, hb⟩ := h
  have h0 : (((l : ℕ) : WittVector l O) * a).coeff 0 = 0 := by
    rw [← WittVector.mem_span_p_iff_coeff_zero_eq_zero]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  rw [hb, WittVector.mul_coeff_zero, WittVector.teichmuller_coeff_zero] at h0
  have hb0 : b.coeff 0 = 0 := (mul_eq_zero.mp h0).resolve_left hx
  rw [← WittVector.mem_span_p_iff_coeff_zero_eq_zero, Ideal.mem_span_singleton] at hb0
  obtain ⟨c, rfl⟩ := hb0
  have hl : ((l : ℕ) : WittVector l O) ≠ 0 := WittVector.p_nonzero l O
  refine ⟨c, mul_left_cancel₀ hl ?_⟩
  rw [hb]; ring

theorem teichmuller_distinguished_regular : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [CharP O l] [PerfectRing O l] (x : O) (e : ℕ) (w E' : WittVector l O), x ≠ 0 → 0 < e → IsUnit w → E' = WittVector.teichmuller l x ^ e + ((l : ℕ) : WittVector l O) * w → ∀ (k : ℕ) (a : WittVector l O), (WittVector.teichmuller l x ^ k ∣ E' * a → WittVector.teichmuller l x ^ k ∣ a) ∧ (E' ∣ WittVector.teichmuller l x ^ k * a → E' ∣ a) := by
  intro l _ O _ _ _ _ x e w E' hx he hw hE
  have hT : WittVector.teichmuller l x ≠ 0 := by
    intro h
    apply hx
    rw [← WittVector.teichmuller_coeff_zero l x, h]
    simp
  have h1 : ∀ a : WittVector l O, WittVector.teichmuller l x ∣ E' * a →
      WittVector.teichmuller l x ∣ a := by
    intro a h
    rw [hE, add_mul] at h
    have h2 : WittVector.teichmuller l x ∣ WittVector.teichmuller l x ^ e * a :=
      (dvd_pow_self _ he.ne').mul_right a
    have h3 := (dvd_add_right h2).mp h
    rw [mul_assoc] at h3
    exact hw.dvd_mul_left.mp (teichmuller_dvd_of_dvd_natCast_mul l O x hx _ h3)
  have hk : ∀ (k : ℕ) (a : WittVector l O), WittVector.teichmuller l x ^ k ∣ E' * a →
      WittVector.teichmuller l x ^ k ∣ a := by
    intro k
    induction k with
    | zero => intro a _; simp
    | succ k ih =>
      intro a h
      obtain ⟨c, rfl⟩ := h1 a ((dvd_pow_self _ k.succ_ne_zero).trans h)
      rw [pow_succ', mul_left_comm, mul_dvd_mul_iff_left hT] at h
      rw [pow_succ']
      exact mul_dvd_mul_left _ (ih c h)
  intro k a
  refine ⟨hk k a, ?_⟩
  rintro ⟨b, hb⟩
  obtain ⟨c, rfl⟩ := hk k b ⟨a, hb.symm⟩
  refine ⟨c, mul_left_cancel₀ (pow_ne_zero k hT) ?_⟩
  rw [hb]; ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TendstoRatioBoxCountsProdOne
section
open Filter

namespace GlobalTheory

theorem ratio_box_counts_tendsto_one (r : ℕ) (c : Fin r → ℕ) (m : ℕ) :
    Filter.Tendsto (fun k : ℕ => ((∏ i, (2 * (k + m) * c i + 1) : ℕ) : ℝ) /
      ((∏ i, (2 * k * c i + 1) : ℕ) : ℝ)) Filter.atTop (nhds 1) := by
  have key : ∀ i, Tendsto (fun k : ℕ => ((2 * (k + m) * c i + 1 : ℕ) : ℝ) /
      ((2 * k * c i + 1 : ℕ) : ℝ)) atTop (nhds 1) := by
    intro i
    rcases Nat.eq_zero_or_pos (c i) with h | h
    · simp [h]
    · have hc : (0:ℝ) < c i := by exact_mod_cast h
      have hden : Tendsto (fun k : ℕ => ((2 * k * c i + 1 : ℕ) : ℝ)) atTop atTop := by
        push_cast
        apply tendsto_atTop_add_const_right
        exact (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0:ℝ) < 2)).atTop_mul_const hc
      have h0 : Tendsto (fun k : ℕ => (2 * m * c i : ℝ) / ((2 * k * c i + 1 : ℕ) : ℝ)) atTop (nhds 0) :=
        tendsto_const_nhds.div_atTop hden
      have h1 := (tendsto_const_nhds (x := (1:ℝ))).add h0
      rw [add_zero] at h1
      refine h1.congr (fun k => ?_)
      have hpos : ((2 * k * c i + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp
      push_cast
      ring
  have h := tendsto_finset_prod (Finset.univ : Finset (Fin r)) (fun i _ => key i)
  simp only [Finset.prod_const_one] at h
  refine h.congr (fun k => ?_)
  rw [Nat.cast_prod, Nat.cast_prod, Finset.prod_div_distrib]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TensorProductBasisCoordinates
section
open TensorProduct Module

theorem GlobalTheory.tensorBasisCoords : ∀ (F : Type) [Field F] (B : Type) [CommRing B] [Algebra F B] (V : Type) [AddCommGroup V] [Module F V] (n : Type) [Fintype n] [DecidableEq n] (b : Basis n F V), ∃ e : V ⊗[F] B ≃ₗ[F] (n → B), (∀ v x i, e (v ⊗ₜ[F] x) i = b.repr v i • x) ∧ (∀ y : n → B, e.symm y = ∑ i, b i ⊗ₜ[F] y i) ∧ ∀ (r : V →ₗ[F] V) (f : B →ₗ[F] B) (y : V ⊗[F] B), e (TensorProduct.map r f y) = ((LinearMap.toMatrix b b r).map (algebraMap F B)).mulVec (fun i => f (e y i)) := by
  intro F _ B _ _ V _ _ n _ _ b
  let e : V ⊗[F] B ≃ₗ[F] (n → B) :=
    (TensorProduct.comm F V B) ≪≫ₗ (TensorProduct.congr (LinearEquiv.refl F B) b.equivFun) ≪≫ₗ
      TensorProduct.piScalarRight F F B n
  have h1 : ∀ v x i, e (v ⊗ₜ[F] x) i = b.repr v i • x := by
    intro v x i
    simp [e, TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
  have hadd : ∀ y z : V ⊗[F] B, e (y + z) = e y + e z := fun y z => map_add e y z
  refine ⟨e, h1, ?_, ?_⟩
  · intro y
    rw [LinearEquiv.symm_apply_eq]
    funext j
    rw [map_sum, Finset.sum_apply]
    simp only [h1, Basis.repr_self, Finsupp.single_apply]
    simp
  · intro r f y
    induction y using TensorProduct.induction_on with
    | zero =>
      simp only [map_zero]
      rw [show (fun _ : n => f ((0 : n → B) _)) = 0 from by funext i; simp, Matrix.mulVec_zero]
    | tmul v x =>
      funext i
      rw [TensorProduct.map_tmul, h1]
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, LinearMap.toMatrix_apply, h1, map_smul]
      simp_rw [← Algebra.smul_def, smul_smul]
      rw [← Finset.sum_smul]
      congr 1
      conv_lhs => rw [← b.sum_repr v]
      rw [map_sum, map_sum, Finsupp.finset_sum_apply]
      simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    | add y z hy hz =>
      rw [map_add, hadd, hy, hz, hadd, ← Matrix.mulVec_add]
      congr 1
      funext i
      simp [map_add]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TensorRight
section
namespace GlobalTheory.Cyc.FontW

def Dv (l r : ℕ) (M : Type*) [AddCommGroup M] : AddSubgroup M :=
  (nsmulAddMonoidHom (l ^ r) : M →+ M).range

theorem mem_Dv {l r : ℕ} {M : Type*} [AddCommGroup M] {x : M} :
    x ∈ Dv l r M ↔ ∃ y, l ^ r • y = x := Iff.rfl

theorem Dv_map {l r : ℕ} {M M' F : Type*} [AddCommGroup M] [AddCommGroup M'] [FunLike F M M']
    [AddMonoidHomClass F M M'] (f : F) {x : M} (hx : x ∈ Dv l r M) : f x ∈ Dv l r M' := by
  obtain ⟨y, rfl⟩ := mem_Dv.1 hx
  exact mem_Dv.2 ⟨f y, (map_nsmul f _ _).symm⟩

theorem Dv_smul {l r : ℕ} {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M] (a : A) {x : M}
    (hx : x ∈ Dv l r M) : a • x ∈ Dv l r M := by
  obtain ⟨y, rfl⟩ := mem_Dv.1 hx
  exact mem_Dv.2 ⟨a • y, smul_comm _ _ _⟩

def Cpl (l : ℕ) (M : Type*) [AddCommGroup M] : Prop :=
  (∀ x : M, (∀ r, x ∈ Dv l r M) → x = 0) ∧
    ∀ f : ℕ → M, (∀ r, f (r + 1) - f r ∈ Dv l r M) → ∃ L, ∀ r, L - f r ∈ Dv l r M

theorem Cpl.equiv {l : ℕ} {M M' : Type*} [AddCommGroup M] [AddCommGroup M'] (e : M ≃+ M')
    (h : Cpl l M') : Cpl l M := by
  refine ⟨fun x hx => ?_, fun f hf => ?_⟩
  · exact e.injective (by rw [map_zero]; exact h.1 _ fun r => Dv_map e (hx r))
  · obtain ⟨L, hL⟩ := h.2 (fun r => e (f r)) fun r => by
      rw [← map_sub]; exact Dv_map e (hf r)
    refine ⟨e.symm L, fun r => ?_⟩
    have := Dv_map e.symm (hL r)
    rwa [map_sub, e.symm_apply_apply] at this

theorem Cpl.pi {l : ℕ} {M : Type*} [AddCommGroup M] (ι : Type*) (h : Cpl l M) : Cpl l (ι → M) := by
  refine ⟨fun x hx => funext fun i => ?_, fun f hf => ?_⟩
  · exact h.1 _ fun r => Dv_map (Pi.evalAddMonoidHom (fun _ : ι => M) i) (hx r)
  · choose L hL using fun i => h.2 (fun r => f r i) fun r =>
      Dv_map (Pi.evalAddMonoidHom (fun _ : ι => M) i) (hf r)
    refine ⟨L, fun r => ?_⟩
    choose y hy using fun i => mem_Dv.1 (hL i r)
    exact mem_Dv.2 ⟨y, funext hy⟩

theorem Cpl.tensor_left {l : ℕ} {R P M : Type*} [CommRing R] [AddCommGroup P] [Module R P]
    [Module.Free R P] [Module.Finite R P] [AddCommGroup M] [Module R M] (h : Cpl l M) :
    Cpl l (TensorProduct R P M) := by
  classical
  let b := Module.Free.chooseBasis R P
  exact Cpl.equiv ((TensorProduct.equivFinsuppOfBasisLeft b).toAddEquiv.trans
    Finsupp.addEquivFunOnFinite) (h.pi _)

theorem Cpl.tensor_right {l : ℕ} {R P M : Type*} [CommRing R] [AddCommGroup P] [Module R P]
    [Module.Free R P] [Module.Finite R P] [AddCommGroup M] [Module R M] (h : Cpl l M) :
    Cpl l (TensorProduct R M P) :=
  Cpl.equiv (TensorProduct.comm R M P).toAddEquiv h.tensor_left

theorem cpl_witt (p : ℕ) [Fact p.Prime] (k : Type*) [CommRing k] [CharP k p] [PerfectRing k p] :
    Cpl p (WittVector p k) := by
  have key : ∀ (r : ℕ) (x : WittVector p k), x ∈ Dv p r (WittVector p k) ↔
      x ∈ ((Ideal.span {(p : WittVector p k)}) ^ r • ⊤ : Submodule (WittVector p k) (WittVector p k)) := by
    intro r x
    rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton', mem_Dv]
    simp [mul_comm]
  refine ⟨fun x hx => ?_, fun f hf => ?_⟩
  · exact IsHausdorff.haus (I := Ideal.span {(p : WittVector p k)}) inferInstance x fun n =>
      SModEq.zero.2 ((key n x).1 (hx n))
  · obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := Ideal.span {(p : WittVector p k)}) inferInstance
      (f := f) ((AdicCompletion.isAdicCauchy_iff _ _ f).2 fun n => by
        rw [SModEq.sub_mem, ← key, ← neg_sub]; exact neg_mem (hf n))
    refine ⟨L, fun r => ?_⟩
    have := hL r
    rw [SModEq.sub_mem, ← key] at this
    rw [← neg_sub]; exact neg_mem this

theorem sum_translate {G X : Type*} [Group G] [AddCommMonoid X] (N : Subgroup G) (S : Finset G)
    (hS : ∀ h, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ N) (f : G → X) (hf : ∀ g, ∀ n ∈ N, f (g * n) = f g) (σ : G) :
    ∑ s ∈ S, f (σ * s) = ∑ s ∈ S, f s := by
  choose π hπ huniq using hS
  refine Finset.sum_nbij' (fun s => π (σ * s)) (fun t => π (σ⁻¹ * t)) (fun s _ => (hπ _).1)
    (fun s _ => (hπ _).1) (fun s hs => ?_) (fun t ht => ?_) (fun s _ => ?_)
  · refine (huniq _ s ⟨hs, ?_⟩).symm
    have := N.inv_mem (hπ (σ * s)).2
    simpa [mul_assoc] using this
  · refine (huniq _ t ⟨ht, ?_⟩).symm
    have := N.inv_mem (hπ (σ⁻¹ * t)).2
    simpa [mul_assoc] using this
  · have := hf (π (σ * s)) _ (hπ (σ * s)).2
    rw [← this]; simp

section Avg

variable {G A M : Type*} [Group G] [CommRing A] [AddCommGroup M] [Module A M] (l : ℕ)
  (𝓕 : Filter G) (a : G → A → A) (ρ : G → M →+ M)

theorem avg_step (amul : ∀ g h β, a (g * h) β = a g (a h β))
    (ρmul : ∀ g h x, ρ (g * h) x = ρ g (ρ h x))
    (semi : ∀ g β x, ρ g (β • x) = a g β • ρ g x)
    (htr : ∀ W ∈ 𝓕, ∃ N : Subgroup G, N.Normal ∧ (N : Set G) ∈ 𝓕 ∧ (N : Set G) ⊆ W ∧
      ∃ S : Finset G, (∀ h, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ N) ∧
        ∃ β, (∀ n ∈ N, a n β = β) ∧ ∑ s ∈ S, a s β = 1)
    (c : G → M) (hc : ∀ g h, c (g * h) = c g + ρ g (c h))
    (hcont : ∀ r, {g | c g ∈ Dv l r M} ∈ 𝓕) (k : ℕ) (hk : ∀ g, c g ∈ Dv l k M) :
    ∃ b ∈ Dv l k M, (∀ r, {g | c g - (ρ g b - b) ∈ Dv l r M} ∈ 𝓕) ∧
      ∀ g, c g - (ρ g b - b) ∈ Dv l (k + 1) M := by
  obtain ⟨N, hN, hNF, hNW, S, hS, β, hβ, hsum⟩ := htr _ (hcont (k + 1))
  have hβ' : ∀ g, ∀ n ∈ N, a (g * n) β = a g β := fun g n hn => by rw [amul, hβ n hn]
  have hρ : ∀ σ, ρ σ (∑ s ∈ S, a s β • c s) = ∑ s ∈ S, a (σ * s) β • ρ σ (c s) := by
    intro σ
    rw [map_sum]
    exact Finset.sum_congr rfl fun s _ => by rw [semi, amul]
  refine ⟨-∑ s ∈ S, a s β • c s, neg_mem (sum_mem fun s _ => Dv_smul _ (hk s)), fun r => ?_,
    fun σ => ?_⟩
  · obtain ⟨N', hN', hNF', hNW', -⟩ := htr _ (hcont r)
    filter_upwards [hNF, hNF'] with n hn hn'
    refine sub_mem (hNW' hn') ?_
    rw [map_neg, hρ, neg_sub_neg, ← Finset.sum_sub_distrib]
    refine sum_mem fun s _ => ?_
    have h1 : n * s = s * (s⁻¹ * n * s) := by group
    have h2 : a (n * s) β = a s β := by
      rw [h1]; exact hβ' _ _ (by simpa using hN.conj_mem n hn s⁻¹)
    rw [h2, ← smul_sub]
    refine Dv_smul _ ?_
    have h3 : c s - ρ n (c s) = c n - ρ s (c (s⁻¹ * n * s)) := by
      have h4 := hc n s
      rw [h1, hc] at h4
      rw [sub_eq_sub_iff_add_eq_add, h4]
    rw [h3]
    exact sub_mem (hNW' hn') (Dv_map _ (hNW' (by simpa using hN'.conj_mem n hn' s⁻¹)))
  · have h1 : ∑ s ∈ S, a (σ * s) β = 1 := by
      rw [sum_translate N S hS (fun g => a g β) hβ' σ, hsum]
    have h2 : c σ - (ρ σ (-∑ s ∈ S, a s β • c s) - -∑ s ∈ S, a s β • c s) =
        ∑ s ∈ S, a (σ * s) β • c (σ * s) - ∑ s ∈ S, a s β • c s := by
      rw [map_neg, hρ]
      simp only [hc, smul_add, Finset.sum_add_distrib, ← Finset.sum_smul, h1, one_smul]
      abel
    rw [h2, ← QuotientAddGroup.eq_iff_sub_mem]
    have h3 := sum_translate N S hS
      (fun g => QuotientAddGroup.mk' (Dv l (k + 1) M) (a g β • c g)) (fun g n hn => by
        rw [hβ' g n hn]
        refine QuotientAddGroup.eq_iff_sub_mem.2 ?_
        rw [hc, smul_add, add_sub_cancel_left]
        exact Dv_smul _ (Dv_map _ (hNW hn))) σ
    rw [← map_sum, ← map_sum] at h3
    exact h3

theorem avg_cob (hM : Cpl l M) (amul : ∀ g h β, a (g * h) β = a g (a h β))
    (ρmul : ∀ g h x, ρ (g * h) x = ρ g (ρ h x))
    (semi : ∀ g β x, ρ g (β • x) = a g β • ρ g x)
    (htr : ∀ W ∈ 𝓕, ∃ N : Subgroup G, N.Normal ∧ (N : Set G) ∈ 𝓕 ∧ (N : Set G) ⊆ W ∧
      ∃ S : Finset G, (∀ h, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ N) ∧
        ∃ β, (∀ n ∈ N, a n β = β) ∧ ∑ s ∈ S, a s β = 1)
    (c : G → M) (hc : ∀ g h, c (g * h) = c g + ρ g (c h))
    (hcont : ∀ r, {g | c g ∈ Dv l r M} ∈ 𝓕) : ∃ b, ∀ g, c g = ρ g b - b := by
  let P : ℕ → M → Prop := fun k b => (∀ r, {g | c g - (ρ g b - b) ∈ Dv l r M} ∈ 𝓕) ∧
      ∀ g, c g - (ρ g b - b) ∈ Dv l k M
  have h0 : P 0 0 := ⟨by simpa using hcont, fun g => mem_Dv.2 ⟨_, by rw [pow_zero, one_smul]⟩⟩
  have hstep : ∀ k b, P k b → ∃ b', P (k + 1) b' ∧ b' - b ∈ Dv l k M := by
    intro k b hb
    obtain ⟨d, hd, h1, h2⟩ := avg_step l 𝓕 a ρ amul ρmul semi htr (fun g => c g - (ρ g b - b))
      (fun g h => by simp only [hc, ρmul, map_sub]; abel) hb.1 k hb.2
    have e : ∀ g, c g - (ρ g (b + d) - (b + d)) = c g - (ρ g b - b) - (ρ g d - d) := fun g => by
      rw [map_add]; abel
    refine ⟨b + d, ⟨?_, ?_⟩, by simpa using hd⟩
    · simpa only [e] using h1
    · simpa only [e] using h2
  choose nx hnx using hstep
  let f : (k : ℕ) → {b // P k b} := fun k =>
    Nat.rec ⟨0, h0⟩ (fun k b => ⟨nx k b.1 b.2, (hnx k b.1 b.2).1⟩) k
  obtain ⟨L, hL⟩ := hM.2 (fun k => (f k).1) fun k => (hnx k (f k).1 (f k).2).2
  refine ⟨L, fun g => sub_eq_zero.1 (hM.1 _ fun r => ?_)⟩
  have e : c g - (ρ g L - L) = (c g - (ρ g (f r).1 - (f r).1)) - (ρ g (L - (f r).1) - (L - (f r).1)) := by
    rw [map_sub]; abel
  rw [e]
  exact sub_mem ((f r).2.2 g) (sub_mem (Dv_map _ (hL r)) (hL r))

end Avg

end GlobalTheory.Cyc.FontW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TotallyComplexOfRootQuadraticNegDisc
section
open NumberField IsDedekindDomain Polynomial

namespace GlobalTheory

theorem totallyComplex_of_root_quadratic_neg_disc :
    ∀ (K : Type) [Field K] [NumberField K] (x : K) (a b : ℤ), x ^ 2 + (a : K) * x + (b : K) = 0 →
    a ^ 2 < 4 * b → NumberField.IsTotallyComplex K := by
  intro K _ _ x a b hx hab
  refine ⟨fun v => ?_⟩
  rw [← NumberField.InfinitePlace.not_isReal_iff_isComplex]
  intro hv
  set φ : K →+* ℝ := NumberField.InfinitePlace.embedding_of_isReal hv
  have h := congrArg φ hx
  simp only [map_add, map_mul, map_pow, map_intCast, map_zero] at h
  have hab' : ((a : ℝ)) ^ 2 < 4 * (b : ℝ) := by exact_mod_cast hab
  nlinarith [sq_nonneg (2 * φ x + (a : ℝ))]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceAdjoinRootMap
section
open Polynomial

namespace GlobalTheory

theorem adjoinRoot_map_mk_map {R S : Type} [CommRing R] [CommRing S] (g : R →+* S) (h f : R[X]) :
    AdjoinRoot.map g h (h.map g) dvd_rfl (AdjoinRoot.mk h f) = AdjoinRoot.mk (h.map g) (f.map g) := by
  have : (AdjoinRoot.map g h (h.map g) dvd_rfl).comp (AdjoinRoot.mk h) =
      (AdjoinRoot.mk (h.map g)).comp (Polynomial.mapRingHom g) := by
    ext <;> simp
  exact DFunLike.congr_fun this f

theorem trace_adjoinRoot_map : ∀ (R S : Type) [CommRing R] [CommRing S] (g : R →+* S) (h : R[X]),
    h.Monic → ∀ x : AdjoinRoot h, g (Algebra.trace R (AdjoinRoot h) x) =
      Algebra.trace S (AdjoinRoot (h.map g)) (AdjoinRoot.map g h (h.map g) dvd_rfl x) := by
  intro R S _ _ g h hm x
  rcases subsingleton_or_nontrivial S with hS | hS
  · exact Subsingleton.elim _ _
  have hm' : (h.map g).Monic := hm.map g
  have hn : (h.map g).natDegree = h.natDegree := hm.natDegree_map g
  have key : ∀ (y : AdjoinRoot h) (k : ℕ),
      (AdjoinRoot.modByMonicHom hm' (AdjoinRoot.map g h (h.map g) dvd_rfl y)).coeff k =
        g ((AdjoinRoot.modByMonicHom hm y).coeff k) := by
    intro y k
    induction y using AdjoinRoot.induction_on with
    | ih f =>
      rw [adjoinRoot_map_mk_map, AdjoinRoot.modByMonicHom_mk, AdjoinRoot.modByMonicHom_mk,
        ← Polynomial.map_modByMonic g hm, Polynomial.coeff_map]
  let b : Module.Basis (Fin h.natDegree) R (AdjoinRoot h) := (AdjoinRoot.powerBasis' hm).basis
  let b' : Module.Basis (Fin h.natDegree) S (AdjoinRoot (h.map g)) := (AdjoinRoot.powerBasis' hm').basis.reindex (finCongr hn)
  have hb : ∀ i, b i = AdjoinRoot.root h ^ (i : ℕ) := fun i =>
    (AdjoinRoot.powerBasis' hm).basis_eq_pow i
  have hb' : ∀ i, b' i = AdjoinRoot.root (h.map g) ^ (i : ℕ) := fun i => by
    simp only [b', Module.Basis.reindex_apply, PowerBasis.coe_basis, AdjoinRoot.powerBasis'_gen]
    rfl
  have hr : ∀ (z : AdjoinRoot h) (i : Fin h.natDegree), b.repr z i = (AdjoinRoot.modByMonicHom hm z).coeff i :=
    fun _ _ => rfl
  have hr' : ∀ (z : AdjoinRoot (h.map g)) (i : Fin h.natDegree),
      b'.repr z i = (AdjoinRoot.modByMonicHom hm' z).coeff i := fun z i => by
    simp only [b', Module.Basis.repr_reindex_apply]
    rfl
  rw [Algebra.trace_eq_matrix_trace b, Algebra.trace_eq_matrix_trace b', Matrix.trace, Matrix.trace,
    map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.diag]
  rw [Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul]
  have hbi : b' i = AdjoinRoot.map g h (h.map g) dvd_rfl (b i) := by
    rw [hb, hb', map_pow, AdjoinRoot.map_root]
  rw [hbi, ← map_mul, hr', hr, key]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransferCocycleFormula
section
namespace GlobalTheory

open QuotientGroup

theorem transfer_cocycle_formula : ∀ (R G X : Type) [CommRing R] [Group G] [AddCommGroup X] [Module R X] (ρ : Representation R G X) (H : Subgroup G) [Fintype (G ⧸ H)], let tr : (G → X) → G → X := fun f g => ∑ q : G ⧸ H, ρ (g • q).out (f ((g • q).out⁻¹ * g * q.out)); (∀ (g : G) (q : G ⧸ H), (g • q).out⁻¹ * g * q.out ∈ H) ∧ (∀ f : G → X, (∀ a ∈ H, ∀ b ∈ H, f (a * b) = f a + ρ a (f b)) → ∀ a b, tr f (a * b) = tr f a + ρ a (tr f b)) ∧ (∀ (f : G → X) (x : X), (∀ h ∈ H, f h = ρ h x - x) → ∀ g, tr f g = ρ g (∑ q : G ⧸ H, ρ q.out x) - ∑ q : G ⧸ H, ρ q.out x) ∧ (∀ f : G → X, (∀ a b, f (a * b) = f a + ρ a (f b)) → ∀ g, tr f g = H.index • f g + (ρ g (∑ q : G ⧸ H, f q.out) - ∑ q : G ⧸ H, f q.out)) := by
  intro R G X _ _ _ _ ρ H _ tr
  have mem : ∀ (g : G) (q : G ⧸ H), (g • q).out⁻¹ * g * q.out ∈ H := by
    intro g q
    have h1 : (((g • q).out : G) : G ⧸ H) = ((g * q.out : G) : G ⧸ H) := by
      rw [QuotientGroup.out_eq', ← smul_eq_mul, ← MulAction.Quotient.smul_mk, QuotientGroup.out_eq']
    rw [mul_assoc]
    exact QuotientGroup.eq.mp h1
  have reidx : ∀ (g : G) (F : G ⧸ H → X), ∑ q, F (g • q) = ∑ q, F q := fun g F =>
    Equiv.sum_comp (MulAction.toPerm g) F
  have rmul : ∀ (s t : G) (y : X), ρ s (ρ t y) = ρ (s * t) y := by
    intro s t y
    rw [map_mul, Module.End.mul_apply]
  refine ⟨mem, ?_, ?_, ?_⟩
  · intro f hf a b
    have key : ∀ q : G ⧸ H, ρ ((a * b) • q).out (f (((a * b) • q).out⁻¹ * (a * b) * q.out))
        = ρ (a • (b • q)).out (f ((a • (b • q)).out⁻¹ * a * (b • q).out))
          + ρ a (ρ (b • q).out (f ((b • q).out⁻¹ * b * q.out))) := by
      intro q
      rw [mul_smul]
      have e : (a • b • q).out⁻¹ * (a * b) * q.out
          = ((a • b • q).out⁻¹ * a * (b • q).out) * ((b • q).out⁻¹ * b * q.out) := by group
      rw [e, hf _ (mem a (b • q)) _ (mem b q), map_add, rmul, rmul]
      congr 3
      group
    show ∑ q : G ⧸ H, ρ ((a * b) • q).out (f (((a * b) • q).out⁻¹ * (a * b) * q.out))
      = ∑ q : G ⧸ H, ρ (a • q).out (f ((a • q).out⁻¹ * a * q.out))
        + ρ a (∑ q : G ⧸ H, ρ (b • q).out (f ((b • q).out⁻¹ * b * q.out)))
    rw [Finset.sum_congr rfl (fun q _ => key q), Finset.sum_add_distrib, map_sum,
      reidx b (fun q => ρ (a • q).out (f ((a • q).out⁻¹ * a * q.out)))]
  · intro f x hf g
    have key : ∀ q : G ⧸ H, ρ (g • q).out (f ((g • q).out⁻¹ * g * q.out))
        = ρ g (ρ q.out x) - ρ (g • q).out x := by
      intro q
      rw [hf _ (mem g q), map_sub, rmul, rmul]
      congr 2
      group
    show ∑ q : G ⧸ H, ρ (g • q).out (f ((g • q).out⁻¹ * g * q.out)) = _
    rw [Finset.sum_congr rfl (fun q _ => key q), Finset.sum_sub_distrib, map_sum,
      reidx g (fun q => ρ q.out x)]
  · intro f hf g
    have f1 : f 1 = 0 := by
      have := hf 1 1
      simp only [mul_one, map_one, Module.End.one_apply] at this
      exact left_eq_add.mp this
    have finv : ∀ s : G, ρ s (f s⁻¹) = - f s := by
      intro s
      have := hf s s⁻¹
      rw [mul_inv_cancel, f1] at this
      exact (neg_eq_of_add_eq_zero_right this.symm).symm
    have key : ∀ q : G ⧸ H, ρ (g • q).out (f ((g • q).out⁻¹ * g * q.out))
        = (f g + ρ g (f q.out)) - f (g • q).out := by
      intro q
      rw [mul_assoc, hf, map_add, finv, rmul, mul_inv_cancel, map_one, Module.End.one_apply, hf]
      abel
    show ∑ q : G ⧸ H, ρ (g • q).out (f ((g • q).out⁻¹ * g * q.out)) = _
    rw [Finset.sum_congr rfl (fun q _ => key q), Finset.sum_sub_distrib, Finset.sum_add_distrib,
      map_sum, reidx g (fun q => f q.out), Finset.sum_const, Finset.card_univ,
      Subgroup.index_eq_card, Nat.card_eq_fintype_card]
    abel

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransferContinuousOfContinuousOn
section
namespace GlobalTheory

theorem transfer_continuous_of_continuousOn : ∀ (R G X : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup X] [Module R X] [TopologicalSpace X] [IsTopologicalAddGroup X] (ρ : Representation R G X) (H : Subgroup G) [Fintype (G ⧸ H)], IsOpen (H : Set G) → (∀ g, Continuous (ρ g)) → let tr : (G → X) → G → X := fun f g => ∑ q : G ⧸ H, ρ (g • q).out (f ((g • q).out⁻¹ * g * q.out)); ∀ f : G → X, ContinuousOn f H → Continuous (tr f) := by
  intro R G X _ _ _ _ _ _ _ _ ρ H _ hH hρ tr f hf
  show Continuous (fun g => ∑ q : G ⧸ H, ρ (g • q).out (f ((g • q).out⁻¹ * g * q.out)))
  refine continuous_finset_sum _ (fun q _ => ?_)
  refine continuous_iff_continuousAt.2 (fun g₀ => ?_)
  have hsmul : ∀ g : G, g • q = ((g * q.out : G) : G ⧸ H) := by
    intro g
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rfl
  let ψ : G → G := fun g => (g * q.out)⁻¹ * (g₀ • q).out
  have hψc : Continuous ψ := by fun_prop
  let V : Set G := ψ ⁻¹' (H : Set G)
  have hVo : IsOpen V := hH.preimage hψc
  have key : ∀ g ∈ V, g • q = g₀ • q := by
    intro g hg
    have h1 : ((g * q.out : G) : G ⧸ H) = ((g₀ • q).out : G ⧸ H) := QuotientGroup.eq.2 hg
    rw [hsmul g, h1, QuotientGroup.out_eq']
  have hg₀ : g₀ ∈ V := by
    show (g₀ * q.out)⁻¹ * (g₀ • q).out ∈ H
    apply QuotientGroup.eq.1
    rw [QuotientGroup.out_eq', hsmul]
  have hmem : ∀ g ∈ V, (g₀ • q).out⁻¹ * g * q.out ∈ H := by
    intro g hg
    have h1 := QuotientGroup.eq.1 (show (((g₀ • q).out : G) : G ⧸ H) = ((g * q.out : G) : G ⧸ H) by
      rw [QuotientGroup.out_eq', ← hsmul g, key g hg])
    simpa [mul_assoc] using h1
  have hV : V ∈ nhds g₀ := hVo.mem_nhds hg₀
  have hc : ContinuousAt (fun g => ρ (g₀ • q).out (f ((g₀ • q).out⁻¹ * g * q.out))) g₀ := by
    have hφ : Continuous (fun g : G => (g₀ • q).out⁻¹ * g * q.out) := by fun_prop
    have hw : ContinuousWithinAt (fun g => f ((g₀ • q).out⁻¹ * g * q.out)) V g₀ :=
      ContinuousWithinAt.comp (g := f) (f := fun g : G => (g₀ • q).out⁻¹ * g * q.out) (t := (H : Set G))
        (hf _ (hmem g₀ hg₀)) hφ.continuousWithinAt (fun g hg => hmem g hg)
    exact (hρ _).continuousAt.comp (hw.continuousAt hV)
  refine hc.congr ?_
  filter_upwards [hV] with g hg
  rw [key g hg]

end GlobalTheory
end

