import Mathlib

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ContDiffHerm
section
namespace UpperTheory.Reformulated.B.Qj20

@[reducible] noncomputable def Mat (k r : ℕ) : Type :=
  Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ

noncomputable def Hpk (k r : ℕ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
  fun i j =>
    if (i : ℕ) < r ∧ (i : ℕ) + (j : ℕ) = 2 * r + k then 1
    else if (j : ℕ) < r ∧ (i : ℕ) + (j : ℕ) = 2 * r + k then 1
    else if r ≤ (i : ℕ) ∧ (i : ℕ) ≤ r + k ∧ i = j then
      if (i : ℕ) = r + k then -1 else 1
    else 0

noncomputable def inLie (k r : ℕ) (X : Mat k r) : Prop :=
  X.conjTranspose * Hpk k r + Hpk k r * X = 0

theorem aux4 (n : ℕ) : IsTopologicalRing (Matrix (Fin n) (Fin n) ℂ) :=
  inferInstance

noncomputable def RdV.{u_1} {n : ℕ} {E : Type u_1} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (X : Matrix (Fin n) (Fin n) ℂ) (f : Matrix (Fin n) (Fin n) ℂ → E)
    (g : Matrix (Fin n) (Fin n) ℂ) : E :=
  letI : NormedSpace ℝ E := NormedSpace.complexToReal
  deriv (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) 0

noncomputable def herm.{u_1} {ι : Type u_1} [Fintype ι] (H : Matrix ι ι ℂ) (v w : ι → ℂ) : ℂ :=
  star w ⬝ᵥ H.mulVec v

noncomputable def bvec {m : ℕ} (i : Fin m) : Fin m → ℂ :=
  Pi.single i 1

theorem aux8 (k r : ℕ) (a : Fin r) : (a : ℕ) < 2 * r + k + 1 := by
  have := a.isLt
  omega

noncomputable def eI (k r : ℕ) (a : Fin r) : Fin (2 * r + k + 1) :=
  ⟨a.val, aux8 k r a⟩

noncomputable def Top.{u_1} {n : ℕ} {E : Type u_1} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Eop : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E) → Matrix (Fin n) (Fin n) ℂ → E)
    (u : ℂ) (a b : Fin n) (f : Matrix (Fin n) (Fin n) ℂ → E)
    (g : Matrix (Fin n) (Fin n) ℂ) : E :=
  (if a = b then u • f g else 0) + Eop a b f g

noncomputable def qminorOp.{u_1} {n : ℕ} {E : Type u_1} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {t : ℕ} (Eop : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E) → Matrix (Fin n) (Fin n) ℂ → E)
    (a b : Fin t → Fin n) (u : ℂ) (f : Matrix (Fin n) (Fin n) ℂ → E) :
    Matrix (Fin n) (Fin n) ℂ → E :=
  ∑ σ : Equiv.Perm (Fin t),
    ((Equiv.Perm.sign σ : ℤ) : ℂ) •
      (List.ofFn fun k : Fin t => Top Eop (u - (k : ℂ)) (a (σ k)) (b k)).foldr
        (fun T h => T h) f

theorem aux12 : (1 + 1).AtLeastTwo :=
  ⟨by decide⟩

noncomputable def hpart1 {n : ℕ} (H Z : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  (1 / 2 : ℂ) • (Z - H⁻¹ * Z.conjTranspose * H)

noncomputable def hpart2 {n : ℕ} (H Z : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  (1 / (2 * Complex.I) : ℂ) • (Z + H⁻¹ * Z.conjTranspose * H)

noncomputable def EabH.{u_1} {n : ℕ} {E : Type u_1} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (H : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) (f : Matrix (Fin n) (Fin n) ℂ → E)
    (g : Matrix (Fin n) (Fin n) ℂ) : E :=
  RdV (hpart1 H (Matrix.single a b 1)) f g +
    Complex.I • RdV (hpart2 H (Matrix.single a b 1)) f g

noncomputable def xR (k r m : ℕ) (h : m ≤ r) (l : Fin m) : Fin (2 * r + k + 1) :=
  eI k r (Fin.castLE h l)

noncomputable def AAop.{u_1} {E : Type u_1} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (k r m : ℕ) (hm : m ≤ r) (u : ℂ) (f : Mat k r → E) (g : Mat k r) : E :=
  ∑ c : Fin m → Fin (2 * r + k + 1),
    if StrictMono c then
      (Matrix.of fun a l : Fin m =>
        herm (Hpk k r) (g.mulVec (bvec (c l))) (bvec (eI k r (Fin.castLE hm a)))).det •
      qminorOp (EabH (Hpk k r)) (xR k r m hm) c u f g
    else 0

section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

private theorem Hpk_herm (k r : ℕ) : (Hpk k r).conjTranspose = Hpk k r := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Hpk, Fin.ext_iff]
  split_ifs <;> first | omega | simp

private theorem Hpk_sq (k r : ℕ) : Hpk k r * Hpk k r = 1 := by
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  rw [Matrix.mul_apply]
  obtain ⟨s, hs⟩ : ∃ s : Fin (2 * r + k + 1),
      (s : ℕ) = if r ≤ (i : ℕ) ∧ (i : ℕ) ≤ r + k then (i : ℕ) else 2 * r + k - i :=
    ⟨⟨if r ≤ (i : ℕ) ∧ (i : ℕ) ≤ r + k then (i : ℕ) else 2 * r + k - i,
      by split_ifs <;> omega⟩, rfl⟩
  rw [Finset.sum_eq_single s]
  · simp only [Hpk, Matrix.one_apply, Fin.ext_iff]
    split_ifs at hs <;> split_ifs <;> first | omega | simp
  · intro b _ hb
    have hb' : (b : ℕ) ≠ s := fun h => hb (Fin.ext h)
    have h0 : Hpk k r i b = 0 := by
      simp only [Hpk, Fin.ext_iff]
      split_ifs at hs <;> split_ifs <;> first | omega | rfl
    rw [h0, zero_mul]
  · simp

private theorem Hpk_inv (k r : ℕ) : (Hpk k r)⁻¹ = Hpk k r :=
  Matrix.inv_eq_right_inv (Hpk_sq k r)

private theorem inLie_hpart1 (k r : ℕ) (Z : Mat k r) : inLie k r (hpart1 (Hpk k r) Z) := by
  have h2 : star (1 / 2 : ℂ) = 1 / 2 := by simp
  simp only [inLie, hpart1, Hpk_inv, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Hpk_herm, h2,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, Hpk_sq,
    Matrix.mul_one]
  rw [← Matrix.mul_assoc (Hpk k r) (Hpk k r), Hpk_sq, Matrix.one_mul, ← smul_add]
  simp

private theorem inLie_hpart2 (k r : ℕ) (Z : Mat k r) : inLie k r (hpart2 (Hpk k r) Z) := by
  have h2 : star (1 / (2 * Complex.I) : ℂ) = -(1 / (2 * Complex.I)) := by simp
  simp only [inLie, hpart2, Hpk_inv, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Hpk_herm, h2,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, Hpk_sq,
    Matrix.mul_one]
  rw [← Matrix.mul_assoc (Hpk k r) (Hpk k r), Hpk_sq, Matrix.one_mul, neg_smul,
    add_comm (Hpk k r * Z), neg_add_cancel]

private theorem contDiff_entry {n : ℕ} (i j : Fin n) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun g : Matrix (Fin n) (Fin n) ℂ => g i j) :=
  contDiff_apply_apply ℝ ℂ i j

private theorem contDiff_cst {n : ℕ} (c : ℂ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun _ : Matrix (Fin n) (Fin n) ℂ => c) :=
  contDiff_const

private theorem contDiff_herm {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (v w : Fin n → ℂ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun g : Matrix (Fin n) (Fin n) ℂ => herm H (g.mulVec v) w) := by
  simp only [herm, dotProduct, Matrix.mulVec]
  refine ContDiff.sum fun a _ => contDiff_const.mul ?_
  refine ContDiff.sum fun b _ => contDiff_const.mul ?_
  exact ContDiff.sum fun c _ => (contDiff_entry b c).mul contDiff_const

private theorem contDiff_det {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℂ → Fin m → Fin m → ℂ)
    (hA : ∀ a l, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun g => A g a l)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun g => (Matrix.of (A g)).det) := by
  simp only [Matrix.det_apply', Matrix.of_apply]
  exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun l _ => hA _ _)

private theorem closed_sum {X E ι : Type*} [AddCommMonoid E] (P : (X → E) → Prop)
    (hadd : ∀ f₁ f₂, P f₁ → P f₂ → P fun x => f₁ x + f₂ x) (h0 : P fun _ => 0)
    (s : Finset ι) (F : ι → X → E) (hF : ∀ i, P (F i)) : P fun x => ∑ i ∈ s, F i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact hadd _ _ (hF a) ih

private theorem closed_foldr {Y : Type*} (P : Y → Prop) (f : Y) (hf : P f) (L : List (Y → Y))
    (hL : ∀ T ∈ L, ∀ y, P y → P (T y)) : P (L.foldr (fun T h => T h) f) := by
  induction L with
  | nil => exact hf
  | cons T L ih =>
    exact hL T (List.mem_cons_self ..) _ (ih fun S hS => hL S (List.mem_cons_of_mem _ hS))

theorem aa_closed.{u_1} {k r : ℕ} {E : Type u_1} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (P : (Mat k r → E) → Prop)
    (hR : ∀ (X : Mat k r) (f : Mat k r → E), inLie k r X → P f → P (RdV X f))
    (hadd : ∀ f₁ f₂ : Mat k r → E, P f₁ → P f₂ → P fun x => f₁ x + f₂ x)
    (hmul : ∀ φ : Mat k r → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ →
      ∀ f : Mat k r → E, P f → P fun x => φ x • f x)
    (h0 : P fun _ => 0) (m : ℕ) (hm : m ≤ r) (u : ℂ) (f : Mat k r → E) (hf : P f) :
    P (AAop k r m hm u f) := by
  have hc : ∀ (c : ℂ) (f : Mat k r → E), P f → P fun x => c • f x :=
    fun c f hf => hmul (fun _ => c) (contDiff_cst c) f hf
  have hE : ∀ a b (f : Mat k r → E), P f → P (EabH (Hpk k r) a b f) := fun a b f hf =>
    hadd _ _ (hR _ f (inLie_hpart1 k r _) hf) (hc _ _ (hR _ f (inLie_hpart2 k r _) hf))
  have hT : ∀ (v : ℂ) a b (f : Mat k r → E), P f → P (Top (EabH (Hpk k r)) v a b f) := by
    intro v a b f hf
    refine hadd (fun g => if a = b then v • f g else 0) _ ?_ (hE a b f hf)
    by_cases hab : a = b
    · simp only [if_pos hab]; exact hc v f hf
    · simp only [if_neg hab]; exact h0
  have hQ : ∀ (a b : Fin m → Fin (2 * r + k + 1)),
      P (qminorOp (EabH (Hpk k r)) a b u f) := by
    intro a b
    unfold qminorOp
    rw [Finset.sum_fn]
    refine closed_sum P hadd h0 _ _ fun σ => ?_
    refine hc _ _ (closed_foldr P f hf _ fun T hTm => ?_)
    obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hTm
    exact hT _ _ _
  unfold AAop
  refine closed_sum P hadd h0 _ _ fun c => ?_
  by_cases hcm : StrictMono c
  · simp only [if_pos hcm]
    exact hmul _ (contDiff_det _ fun a l => contDiff_herm _ _ _) _ (hQ _ c)
  · simp only [if_neg hcm]
    exact h0

end

end UpperTheory.Reformulated.B.Qj20
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CoproductAdjoin
section
private theorem UpperTheory.Reformulated.B.CoproductAdjoin.reindex {G : Type} [Mul G] (A : Subalgebra ℂ (G → ℂ))
    (p : G → ℂ) {ι : Type} [Fintype ι] (a b : ι → G → ℂ) (h : ∀ i, a i ∈ A ∧ b i ∈ A)
    (hp : ∀ x k : G, p (x * k) = ∑ i, a i x * b i k) :
    ∃ (m : ℕ) (a : Fin m → G → ℂ) (b : Fin m → G → ℂ),
      (∀ i : Fin m, a i ∈ A ∧ b i ∈ A) ∧ ∀ x k : G, p (x * k) = ∑ i : Fin m, a i x * b i k := by
  refine ⟨Fintype.card ι, fun j => a ((Fintype.equivFin ι).symm j),
    fun j => b ((Fintype.equivFin ι).symm j), fun j => h _, fun x k => ?_⟩
  rw [hp]
  exact (Equiv.sum_comp (Fintype.equivFin ι).symm (fun i => a i x * b i k)).symm

theorem UpperTheory.Reformulated.B.CoproductAdjoin.coprod_adjoin :
    ∀ {G : Type} [inst : Mul G] (S : Set (G → ℂ)),
    (∀ p ∈ S,
        ∃ (m : ℕ) (a : Fin m → G → ℂ) (b : Fin m → G → ℂ),
          (∀ (i : Fin m), a i ∈ Algebra.adjoin ℂ S ∧ b i ∈ Algebra.adjoin ℂ S) ∧
            ∀ (x k : G), p (x * k) = ∑ i : Fin m, a i x * b i k) →
      ∀ p ∈ Algebra.adjoin ℂ S,
        ∃ (m : ℕ) (a : Fin m → G → ℂ) (b : Fin m → G → ℂ),
          (∀ (i : Fin m), a i ∈ Algebra.adjoin ℂ S ∧ b i ∈ Algebra.adjoin ℂ S) ∧
            ∀ (x k : G), p (x * k) = ∑ i : Fin m, a i x * b i k := by
  intro G _ S hS p hp
  induction hp using Algebra.adjoin_induction with
  | mem p hp => exact hS p hp
  | algebraMap r =>
    refine ⟨1, fun _ => algebraMap ℂ (G → ℂ) r, fun _ => 1,
      fun _ => ⟨Subalgebra.algebraMap_mem _ r, one_mem _⟩, fun x k => ?_⟩
    simp
  | add p q _ _ ihp ihq =>
    obtain ⟨m, a, b, hab, hp⟩ := ihp
    obtain ⟨n, c, d, hcd, hq⟩ := ihq
    refine UpperTheory.Reformulated.B.CoproductAdjoin.reindex _ _ (Sum.elim a c) (Sum.elim b d) ?_ ?_
    · rintro (i | i)
      · exact hab i
      · exact hcd i
    · intro x k
      simp [Fintype.sum_sum_type, hp, hq]
  | mul p q _ _ ihp ihq =>
    obtain ⟨m, a, b, hab, hp⟩ := ihp
    obtain ⟨n, c, d, hcd, hq⟩ := ihq
    refine UpperTheory.Reformulated.B.CoproductAdjoin.reindex _ _ (ι := Fin m × Fin n)
      (fun z => a z.1 * c z.2) (fun z => b z.1 * d z.2) ?_ ?_
    · intro z
      exact ⟨mul_mem (hab _).1 (hcd _).1, mul_mem (hab _).2 (hcd _).2⟩
    · intro x k
      rw [Pi.mul_apply, hp, hq, Finset.sum_mul_sum, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      simp only [Pi.mul_apply]
      ring
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CoproductGeometry
section
theorem UpperTheory.Reformulated.B.CoproductGeometry.cop_geom :
    ∀ {R κ : Type} [inst : CommRing R] [IsNoetherianRing R]
    [inst_2 : NormedField κ] [IsUltrametricDist κ] (m : Ideal R) (y : R →+* κ),
    (∀ (x : R), ‖(y : R → κ) x‖ ≤ (1 : ℝ)) →
      (∀ x ∈ m, ‖(y : R → κ) x‖ < (1 : ℝ)) →
        ∃ a < (1 : ℝ), (0 : ℝ) ≤ a ∧ ∀ (n : ℕ), ∀ x ∈ m ^ n, ‖(y : R → κ) x‖ ≤ a ^ n := by
  intro R κ _ _ _ _ m y h1 hm
  classical
  have key : ∀ T : Finset R, (∀ s ∈ T, ‖y s‖ < 1) →
      ∃ a < (1 : ℝ), (0 : ℝ) ≤ a ∧ ∀ s ∈ T, ‖y s‖ ≤ a := by
    intro T
    induction T using Finset.induction_on with
    | empty => intro _; exact ⟨0, by norm_num, le_rfl, by simp⟩
    | insert b T hb ih =>
      intro h
      obtain ⟨a, ha1, ha0, ha⟩ := ih (fun s hs => h s (Finset.mem_insert_of_mem hs))
      refine ⟨max a ‖y b‖, max_lt ha1 (h b (Finset.mem_insert_self _ _)),
        le_max_of_le_left ha0, ?_⟩
      intro s hs
      rcases Finset.mem_insert.mp hs with rfl | hs
      · exact le_max_right _ _
      · exact (ha s hs).trans (le_max_left _ _)
  obtain ⟨S, hS⟩ : m.FG := IsNoetherian.noetherian m
  obtain ⟨a, ha1, ha0, ha⟩ := key S (fun s hs => hm s (hS ▸ Ideal.subset_span hs))
  have hgen : ∀ z ∈ m, ‖y z‖ ≤ a := by
    intro z hz
    rw [← hS] at hz
    induction hz using Submodule.span_induction with
    | mem x hx => exact ha x hx
    | zero => simpa using ha0
    | add u v _ _ hu hv =>
      rw [map_add]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hu hv)
    | smul r u _ hu =>
      rw [smul_eq_mul, map_mul, norm_mul]
      calc ‖y r‖ * ‖y u‖ ≤ 1 * a := mul_le_mul (h1 r) hu (norm_nonneg _) zero_le_one
        _ = a := one_mul a
  refine ⟨a, ha1, ha0, ?_⟩
  intro n
  induction n with
  | zero => intro x _; simpa using h1 x
  | succ n ih =>
    intro x hx
    rw [pow_succ] at hx
    induction hx using Submodule.mul_induction_on' with
    | mem_mul_mem u hu v hv =>
      rw [map_mul, norm_mul, pow_succ]
      exact mul_le_mul (ih u hu) (hgen v hv) (norm_nonneg _) (pow_nonneg ha0 n)
    | add u _ v _ hu hv =>
      rw [map_add]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hu hv)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CosetOfCover
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qn18.Mat :
    Type → ℕ → Type :=
    fun (C : Type) (N : ℕ) ↦ Matrix (Fin N) (Fin N) C

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qn18.MP :
    (C : Type) → [Field C] → ℕ → Type :=
    fun (C : Type) [Field C] (N : ℕ) ↦ MvPolynomial (Fin N × Fin N) C

noncomputable def UpperTheory.Reformulated.B.Qn18.ev :
    {C : Type} → [inst : Field C] → {N : ℕ} → UpperTheory.Reformulated.B.Qn18.Mat C N → UpperTheory.Reformulated.B.Qn18.MP C N → C :=
    fun {C : Type} [Field C] {N : ℕ} (x : UpperTheory.Reformulated.B.Qn18.Mat C N) (f : UpperTheory.Reformulated.B.Qn18.MP C N) ↦
      (MvPolynomial.eval fun (p : Fin N × Fin N) ↦ x p.1 p.2 : MvPolynomial (Fin N × Fin N) C → C) f

noncomputable def UpperTheory.Reformulated.B.Qn18.dAt :
    {C : Type} →
      [inst : Field C] → {N : ℕ} → UpperTheory.Reformulated.B.Qn18.MP C N → UpperTheory.Reformulated.B.Qn18.Mat C N → UpperTheory.Reformulated.B.Qn18.Mat C N → C :=
    fun {C : Type} [Field C] {N : ℕ} (f : UpperTheory.Reformulated.B.Qn18.MP C N) (x Y : UpperTheory.Reformulated.B.Qn18.Mat C N) ↦
      ∑ p : Fin N × Fin N,
        UpperTheory.Reformulated.B.Qn18.ev x
            ((MvPolynomial.pderiv p : MvPolynomial (Fin N × Fin N) C → MvPolynomial (Fin N × Fin N) C) f) *
          Y p.1 p.2

noncomputable def UpperTheory.Reformulated.B.Qn18.Chain :
    Prop :=
    ∀ (C : Type) [inst : Field C] (N M : ℕ) (φ : UpperTheory.Reformulated.B.Qn18.Mat C N →ₗ[C] UpperTheory.Reformulated.B.Qn18.Mat C M)
      (f : UpperTheory.Reformulated.B.Qn18.MP C M),
      ∃ (f' : UpperTheory.Reformulated.B.Qn18.MP C N),
        (∀ (x : UpperTheory.Reformulated.B.Qn18.Mat C N),
            UpperTheory.Reformulated.B.Qn18.ev x f' =
              UpperTheory.Reformulated.B.Qn18.ev ((φ : UpperTheory.Reformulated.B.Qn18.Mat C N → UpperTheory.Reformulated.B.Qn18.Mat C M) x) f) ∧
          ∀ (x Y : UpperTheory.Reformulated.B.Qn18.Mat C N),
            UpperTheory.Reformulated.B.Qn18.dAt f' x Y =
              UpperTheory.Reformulated.B.Qn18.dAt f ((φ : UpperTheory.Reformulated.B.Qn18.Mat C N → UpperTheory.Reformulated.B.Qn18.Mat C M) x)
                ((φ : UpperTheory.Reformulated.B.Qn18.Mat C N → UpperTheory.Reformulated.B.Qn18.Mat C M) Y)

noncomputable def UpperTheory.Reformulated.B.Qn18.OpenCoset :
    Prop :=
    ∀ (Γ C : Type) [inst : Group Γ] [inst_1 : TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [inst_4 : Field C]
      (n : ℕ) (r : Γ →* GL (Fin n) C) (f : UpperTheory.Reformulated.B.Qn18.MP C n) (O : Set Γ),
      IsOpen O →
        O.Nonempty →
          (∀ g ∈ O, UpperTheory.Reformulated.B.Qn18.ev (↑((r : Γ → GL (Fin n) C) g) : Matrix (Fin n) (Fin n) C) f = (0 : C)) →
            ∃ (U : Subgroup Γ),
              U.Normal ∧
                U.FiniteIndex ∧
                  ∃ (g : Γ),
                    ∀ u ∈ U, UpperTheory.Reformulated.B.Qn18.ev (↑((r : Γ → GL (Fin n) C) (g * u)) : Matrix (Fin n) (Fin n) C) f = (0 : C)

open scoped Pointwise in
private theorem UpperTheory.Reformulated.B.Qn18.coset_of_cover {G : Type} [Group G] [TopologicalSpace G]
    [TopologicalSpace.NoetherianSpace G] (hc : ∀ h : G, Continuous fun x : G => h * x)
    (Z : Set G) (hZ : IsClosed Z) (s : Finset G) (hs : ∀ x : G, ∃ a ∈ s, a * x ∈ Z) :
    ∃ U : Subgroup G, U.Normal ∧ U.FiniteIndex ∧ ∃ g : G, ∀ u ∈ U, g * u ∈ Z := by
  classical
  haveI : ContinuousConstSMul G G := ⟨hc⟩
  set X : Set G := irreducibleComponent (1 : G) with hX
  have hXc : X ∈ irreducibleComponents G := irreducibleComponent_mem_irreducibleComponents _
  have horb : MulAction.orbit G X ⊆ irreducibleComponents G := by
    rintro _ ⟨h, rfl⟩
    refine ⟨?_, ?_⟩
    · exact hXc.1.image _ (hc h).continuousOn
    · intro Y hY hle
      have h1 : IsIrreducible (h⁻¹ • Y) := IsIrreducible.image hY _ (hc h⁻¹).continuousOn
      have h2 : X ⊆ h⁻¹ • Y := by
        have : h • X ⊆ Y := hle
        exact Set.smul_set_subset_iff_subset_inv_smul_set.mp this
      have h3 : h⁻¹ • Y ⊆ X := hXc.2 h1 h2
      have h4 : Y ⊆ h • X := by
        have := Set.smul_set_subset_iff_subset_inv_smul_set.mp h3
        simpa using this
      exact h4
  have hfin : (MulAction.orbit G X).Finite :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.subset horb
  haveI : (MulAction.stabilizer G X).FiniteIndex := by
    refine ⟨?_⟩
    rw [MulAction.index_stabilizer]
    exact ((Set.ncard_pos hfin).mpr ⟨X, MulAction.mem_orbit_self X⟩).ne'
  obtain ⟨W, hW, hXW⟩ := isIrreducible_iff_sUnion_isClosed.mp hXc.1
    (s.image fun a => (fun x : G => a * x) ⁻¹' Z)
    (by
      intro z hz
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hz
      exact hZ.preimage (hc a))
    (by
      intro x _
      obtain ⟨a, ha, hx⟩ := hs x
      exact ⟨_, Finset.mem_coe.mpr (Finset.mem_image_of_mem _ ha), hx⟩)
  obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hW
  refine ⟨(MulAction.stabilizer G X).normalCore, inferInstance, inferInstance, a, ?_⟩
  intro u hu
  have hu' : u • X = X := Subgroup.normalCore_le _ hu
  have : u ∈ X := by
    rw [← hu']
    exact ⟨1, mem_irreducibleComponent, by simp⟩
  exact hXW this

private theorem UpperTheory.Reformulated.B.Qn18.finite_cover {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] (O : Set G) (hO : IsOpen O) (hne : O.Nonempty) :
    ∃ s : Finset G, ∀ x : G, ∃ a ∈ s, a * x ∈ O := by
  obtain ⟨o, ho⟩ := hne
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun a : G => (fun x : G => a * x) ⁻¹' O)
    (fun a => hO.preimage (continuous_const_mul a))
    (fun x _ => Set.mem_iUnion.mpr ⟨o * x⁻¹, by simpa using ho⟩)
  refine ⟨s, fun x => ?_⟩
  simpa using hs (Set.mem_univ x)

theorem UpperTheory.Reformulated.B.Qn18.main :
    UpperTheory.Reformulated.B.Qn18.Chain → UpperTheory.Reformulated.B.Qn18.OpenCoset := by
  intro hch Γ C _ _ _ _ _ n r f O hO hne hf
  obtain ⟨s, hs⟩ := UpperTheory.Reformulated.B.Qn18.finite_cover O hO hne
  let p : Γ → PrimeSpectrum (MvPolynomial (Fin n × Fin n) C) := fun g =>
    ⟨RingHom.ker (MvPolynomial.eval fun q : Fin n × Fin n =>
      (↑(r g) : Matrix (Fin n) (Fin n) C) q.1 q.2), RingHom.ker_isPrime _⟩
  have hp : ∀ (g : Γ) (S : Set (MvPolynomial (Fin n × Fin n) C)),
      p g ∈ PrimeSpectrum.zeroLocus S ↔
        ∀ k ∈ S, UpperTheory.Reformulated.B.Qn18.ev (↑(r g) : Matrix (Fin n) (Fin n) C) k = 0 := by
    intro g S
    rw [PrimeSpectrum.mem_zeroLocus]
    exact Iff.rfl
  let τ : TopologicalSpace Γ := TopologicalSpace.induced p inferInstance
  have hcl : ∀ k : MvPolynomial (Fin n × Fin n) C,
      @IsClosed Γ τ {g | UpperTheory.Reformulated.B.Qn18.ev (↑(r g) : Matrix (Fin n) (Fin n) C) k = 0} := by
    intro k
    refine (@isClosed_induced_iff _ _ _ _ p).mpr ⟨_, PrimeSpectrum.isClosed_zeroLocus {k}, ?_⟩
    ext g
    simp [hp]
  have hN : @TopologicalSpace.NoetherianSpace Γ τ := by
    letI := τ
    exact (@Topology.IsInducing.mk _ _ τ _ p rfl).noetherianSpace
  have hc : ∀ h : Γ, @Continuous Γ Γ τ τ fun x => h * x := by
    intro h
    refine (@continuous_iff_isClosed _ _ τ τ _).mpr ?_
    intro T hT
    obtain ⟨T', hT', rfl⟩ := (@isClosed_induced_iff _ _ _ _ p).mp hT
    obtain ⟨S, rfl⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus _).mp hT'
    choose F hF using fun k => hch C n n
      (LinearMap.mulLeft C (↑(r h) : Matrix (Fin n) (Fin n) C)) k
    have : (fun x => h * x) ⁻¹' (p ⁻¹' PrimeSpectrum.zeroLocus S) =
        ⋂ k ∈ S, {g | UpperTheory.Reformulated.B.Qn18.ev (↑(r g) : Matrix (Fin n) (Fin n) C) (F k) = 0} := by
      ext g
      simp only [Set.mem_preimage, hp, Set.mem_iInter, Set.mem_setOf_eq, (hF _).1,
        LinearMap.mulLeft_apply, map_mul, Units.val_mul]
    rw [this]
    exact @isClosed_biInter _ _ τ _ _ fun k _ => hcl (F k)
  exact @UpperTheory.Reformulated.B.Qn18.coset_of_cover Γ _ τ hN hc _ (hcl f) s fun x => by
    obtain ⟨a, ha, hx⟩ := hs x
    exact ⟨a, ha, hf _ hx⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CurveDVRPrecompleteFinite
section
theorem UpperTheory.Reformulated.B.PrecompleteOfFiniteOverAdicComplete.curveDVR_prec_finite :
    ∀ {O M : Type} [inst : CommRing O] [IsNoetherianRing O]
    (I : Ideal O) [IsAdicComplete I O] [inst_3 : AddCommGroup M] [inst_4 : _root_.Module O M] [Module.Finite O M],
    IsPrecomplete I M := by
  intro O M _ _ I _ _ _ _
  rw [← AdicCompletion.of_surjective_iff]
  intro y
  obtain ⟨t, rfl⟩ := AdicCompletion.ofTensorProduct_surjective_of_finite I M y
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, by rw [map_zero, map_zero]⟩
  | tmul r m =>
    obtain ⟨a, rfl⟩ := AdicCompletion.of_surjective I O r
    refine ⟨a • m, ?_⟩
    rw [AdicCompletion.ofTensorProduct_tmul, map_smul]
    exact (algebraMap_smul (AdicCompletion I O) a (AdicCompletion.of I M m)).symm
  | add x z hx hz =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hz
    exact ⟨a + b, by rw [map_add, map_add, ha, hb]⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IofAdd
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qk7.Om :
    (l : ℕ) → [Fact (Nat.Prime l)] → Type :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ PadicAlgCl l

theorem UpperTheory.Reformulated.B.Qk7.iof_add :
    ∀ {v : ℕ} [inst : Fact (Nat.Prime v)] {x y : UpperTheory.Reformulated.B.Qk7.Om v}, ‖x‖ < (1 : ℝ) → ‖y‖ < (1 : ℝ) → ‖x + y‖ < (1 : ℝ) := by
  intro v inst x y hx hy
  exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max x y) (max_lt hx hy)
end

