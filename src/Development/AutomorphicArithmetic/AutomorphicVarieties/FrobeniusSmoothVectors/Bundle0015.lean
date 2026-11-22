import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0007
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0003
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0006
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0005
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0011
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0002
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0012
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0010
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ObsPres

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ExistsFrobeniusCorner
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem cor_mul {K : Type} [CommRing K] (A B : Matrix (Fin 3) (Fin 3) K) (h0 : A 0 1 = 0) (h2 : A 2 1 = 0) :
    (A * B).submatrix cor cor = A.submatrix cor cor * B.submatrix cor cor := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp [cor, h0, h2]

private theorem mid_mul' {K : Type} [CommRing K] (A B : Matrix (Fin 3) (Fin 3) K) (h0 : B 0 1 = 0) (h2 : B 2 1 = 0) :
    (A * B) 1 1 = A 1 1 * B 1 1 := by
  simp [Matrix.mul_apply, Fin.sum_univ_three, h0, h2]

private theorem cor_one' {K : Type} [CommRing K] :
    (1 : Matrix (Fin 3) (Fin 3) K).submatrix cor cor = 1 :=
  Matrix.submatrix_one _ (by decide)

private theorem cor_sub {K : Type} [CommRing K] (A : Matrix (Fin 3) (Fin 3) K) (t : K) :
    (A - t • (1 : Matrix (Fin 3) (Fin 3) K)).submatrix cor cor = A.submatrix cor cor - t • 1 := by
  simp [Matrix.submatrix_sub, Matrix.submatrix_smul, cor_one']

private theorem cor_J {K : Type} [CommRing K] (A : Matrix (Fin 3) (Fin 3) K) :
    (Jmat K 3 * Aᵀ * Jmat K 3).submatrix cor cor = Jmat K 2 * (A.submatrix cor cor)ᵀ * Jmat K 2 := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp [Jmat, cor, Fin.rev]

private theorem ordProd_three {H K : Type} [CommRing K] (r : H → Matrix (Fin 3) (Fin 3) K) (ψ : Fin 3 → H → K)
    (x y z : H) : ordProd r ψ ![x, y, z] =
      (r x - ψ 0 x • 1) * (r y - ψ 1 y • 1) * (r z - ψ 2 z • 1) := by
  simp [ordProd, List.ofFn_succ, mul_assoc]

private theorem ordProd_two {H K : Type} [CommRing K] (r : H → Matrix (Fin 2) (Fin 2) K) (ψ : Fin 2 → H → K)
    (g : Fin 2 → H) : ordProd r ψ g = (r (g 0) - ψ 0 (g 0) • 1) * (r (g 1) - ψ 1 (g 1) • 1) := by
  simp [ordProd, List.ofFn_succ]

theorem UpperTheory.V.Fr.exists_frobenius_corner :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} {K : Type} [CommRing K] (ρ : NRep F 3 K), (∀ g i j, Odd (w 3 i - w 3 j) → ρ.r g i j = 0) → CornerUnits ρ → ∃ σ : NRep F 2 K, IsCorner ρ σ := by
  intro l _ k _ F K _ ρ hodd hU
  have hc : ∀ g (i : Fin 3), i ≠ 1 → ρ.r g i 1 = 0 := by
    intro g i hi
    apply hodd
    fin_cases i <;> simp_all [w, Int.odd_iff]
  have hcs : ∀ g (t : K) (i : Fin 3), i ≠ 1 → (ρ.r g - t • 1) i 1 = 0 := by
    intro g t i hi
    rw [Matrix.sub_apply, Matrix.smul_apply, hc g i hi, Matrix.one_apply_ne hi, smul_zero, sub_zero]
  have hinj : Function.Injective cor := by decide
  let s : F.G0 →* Matrix (Fin 2) (Fin 2) K :=
    { toFun := fun g => (ρ.r g).submatrix cor cor
      map_one' := by simp only [map_one, cor_one']
      map_mul' := fun a b => by
        simp only [map_mul]
        exact cor_mul _ _ (hc a 0 (by decide)) (hc a 2 (by decide)) }
  refine ⟨⟨s, fun v i => ρ.ψ v (cor i), ?_, ?_, ?_⟩, ?_⟩
  · intro g
    show (ρ.r (F.star g)).submatrix cor cor = Jmat K 2 * ((ρ.r g).submatrix cor cor)ᵀ * Jmat K 2
    rw [ρ.pol, cor_J]
  · intro i j hij
    have hd := ρ.diag (cor i) (cor j) (hinj.ne hij)
    rw [Matrix.sub_apply] at hd ⊢
    exact hd
  · intro v g
    obtain ⟨g₁, -, -, u1⟩ := hU v
    have key := frobenius_corner_order_skips (s.comp (F.loc0 v)) (fun x => (ρ.ψ v 0 x : K)) ((Units.coeHom K).comp (ρ.ψ v 2)) g₁ (ρ.ψ v 1 g₁ : K) ?det ?three (g 0) (g 1)
    · rw [ordProd_two]
      exact key
    · show IsUnit ((ρ.r (F.loc0 v g₁)).submatrix cor cor - (ρ.ψ v 1 g₁ : K) • 1).det
      rw [← cor_sub, Matrix.det_fin_two]
      simpa [cor, Matrix.one_apply] using u1
    · intro x y
      show ((ρ.r (F.loc0 v x)).submatrix cor cor - (ρ.ψ v 0 x : K) • 1) * ((ρ.r (F.loc0 v g₁)).submatrix cor cor - (ρ.ψ v 1 g₁ : K) • 1) * ((ρ.r (F.loc0 v y)).submatrix cor cor - (ρ.ψ v 2 y : K) • 1) = 0
      have h3 := ρ.ord v ![x, g₁, y]
      rw [ordProd_three] at h3
      beta_reduce at h3
      rw [← cor_sub, ← cor_sub, ← cor_sub, mul_assoc, ← cor_mul _ _ (hcs _ _ 0 (by decide)) (hcs _ _ 2 (by decide)), ← cor_mul _ _ (hcs _ _ 0 (by decide)) (hcs _ _ 2 (by decide)), ← mul_assoc, h3, Matrix.submatrix_zero]
      rfl
  · refine ⟨hodd, fun g i j => rfl, fun v i g => rfl, fun v g => ?_⟩
    obtain ⟨g₁, u0, u2, -⟩ := hU v
    have h3 := ρ.ord v ![g₁, g, g₁]
    rw [ordProd_three] at h3
    beta_reduce at h3
    have h11 := congrFun (congrFun h3 1) 1
    rw [mid_mul' _ _ (hcs _ _ 0 (by decide)) (hcs _ _ 2 (by decide)), mid_mul' _ _ (hcs _ _ 0 (by decide)) (hcs _ _ 2 (by decide))] at h11
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, Matrix.zero_apply] at h11
    rw [u2.mul_left_eq_zero, u0.mul_right_eq_zero, sub_eq_zero] at h11
    exact h11
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FinrankStructMapSRange
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.finrank_structMapS_range :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ : ℕ}, F.Ok C₀ → Module.rank k (F.strS k) ≤ C₀ := by
  intro l _ k _ _ F C₀ hF
  have h2 : (2 : k) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : k) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff k l] at h'
    exact hF.l_odd ((Nat.prime_dvd_prime_iff_eq (Fact.out : l.Prime) Nat.prime_two).mp h')
  set χ := F.Ψ⁻¹ ^ 2 * F.delK k with hχ
  have hc : ((χ F.c : kˣ) : k) = -1 := by
    simp [hχ, Frame.delK, hF.del_c, hF.Ψ_c]
  let Z := Z1C F.loc (chRep χ) fun _ => (⊥ : Submodule k k)
  let f : Z →ₗ[k] (F.G0 → k) :=
    { toFun := fun x g => (x.1.1 g + ((χ g : k) * x.1.1 F.c - x.1.1 F.c) * 2⁻¹) * (F.Ψ g : k)
      map_add' := by
        intro x y
        funext g
        simp
        ring
      map_smul' := by
        intro r x
        funext g
        simp
        ring }
  have hker : Submodule.comap Z.subtype (continuousCoboundaries1 (chRep χ) fun _ => (⊥ : Submodule k k)) ≤ LinearMap.ker f := by
    rintro ⟨x, hx⟩ hb
    rw [Submodule.mem_comap] at hb
    obtain ⟨X, hX, -⟩ := hb
    rw [LinearMap.mem_ker]
    funext g
    have e1 := hX (g : F.Γ)
    have e2 := hX F.c
    simp only [Submodule.subtype_apply, chRep_apply, hc] at e1 e2
    simp only [f, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply]
    rw [e1, e2]
    field_simp
    ring
  let L := Submodule.liftQ _ f hker
  have hle : F.strS k ≤ LinearMap.range L := by
    intro a ha
    obtain ⟨x, hx, hx0, hax⟩ := frame_extension_of_locallyConstant hF a ha
    refine ⟨Submodule.Quotient.mk ⟨x, hx⟩, ?_⟩
    rw [Submodule.liftQ_apply]
    funext g
    simp [f, hx0, hax]
  calc Module.rank k (F.strS k) ≤ Module.rank k (LinearMap.range L) := Submodule.rank_mono hle
    _ ≤ Module.rank k (H1C F.loc (chRep χ) fun _ => (⊥ : Submodule k k)) := rank_range_le L
    _ ≤ C₀ := hF.b1p
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.GrMIff
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem sg_sub (R : Type) [CommRing R] (i j : ZMod 2) : sg R (i - j) = sg R i * sg R j := by
  have h : ∀ i : ZMod 2, i = 0 ∨ i = 1 := by decide
  have s0 : sg R 0 = 1 := pow_zero _
  have s1 : sg R 1 = -1 := pow_one _
  have e : (0 : ZMod 2) - 1 = 1 := by decide
  rcases h i with rfl | rfl <;> rcases h j with rfl | rfl
  · rw [sub_self, s0, one_mul]
  · rw [e, s0, one_mul]
  · rw [sub_zero, s0, mul_one]
  · rw [sub_self, s0, s1, neg_mul_neg, one_mul]

private theorem sg_sq (R : Type) [CommRing R] (i : ZMod 2) : sg R i * sg R i = 1 := by
  rw [← sg_sub, sub_self]
  exact pow_zero _

private def sgM (R : Type) [CommRing R] (α : Fin 3 → ZMod 2) : Matrix (Fin 3) (Fin 3) R :=
  Matrix.diagonal fun a => sg R (α a)

private theorem sgM_sq (R : Type) [CommRing R] (α : Fin 3 → ZMod 2) : sgM R α * sgM R α = 1 := by
  simp only [sgM, Matrix.diagonal_mul_diagonal, sg_sq, Matrix.diagonal_one]

private theorem grM_iff {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (σ : R →ₐ[O] R)
    (α β : Fin 3 → ZMod 2) (M : Matrix (Fin 3) (Fin 3) R) :
    GrM σ α β M ↔ (σ : R →+* R).mapMatrix M = sgM R α * M * sgM R β := by
  rw [← Matrix.ext_iff]
  refine forall₂_congr fun a b => ?_
  rw [sgM, sgM, Matrix.mul_diagonal, Matrix.diagonal_mul]
  show σ (M a b) = sg R (α a - β b) * M a b ↔ σ (M a b) = _
  rw [sg_sub, mul_right_comm]

private theorem grM_mul {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (σ : R →ₐ[O] R)
    (α β γ : Fin 3 → ZMod 2) (M N : Matrix (Fin 3) (Fin 3) R) (h : GrM σ α β M) (h' : GrM σ β γ N) :
    GrM σ α γ (M * N) := by
  rw [grM_iff] at h h' ⊢
  rw [map_mul, h, h']
  calc sgM R α * M * sgM R β * (sgM R β * N * sgM R γ)
      = sgM R α * M * (sgM R β * sgM R β) * N * sgM R γ := by simp only [Matrix.mul_assoc]
    _ = sgM R α * (M * N) * sgM R γ := by rw [sgM_sq, Matrix.mul_one, Matrix.mul_assoc _ M]

private theorem grM_inv {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (σ : R →ₐ[O] R)
    (α β : Fin 3 → ZMod 2) (g : GL (Fin 3) R) (h : GrM σ α β (g : Matrix (Fin 3) (Fin 3) R)) :
    GrM σ β α ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) := by
  rw [grM_iff] at h ⊢
  have h1 : (σ : R →+* R).mapMatrix (g : Matrix (Fin 3) (Fin 3) R) *
      (σ : R →+* R).mapMatrix ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have h2 : sgM R β * ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * sgM R α *
      (σ : R →+* R).mapMatrix (g : Matrix (Fin 3) (Fin 3) R) = 1 := by
    rw [h]
    calc _ = sgM R β * (((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * (sgM R α * sgM R α) *
          (g : Matrix (Fin 3) (Fin 3) R)) * sgM R β := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [sgM_sq, Matrix.mul_one, Units.inv_mul, Matrix.mul_one, sgM_sq]
  exact (left_inv_eq_right_inv h2 h1).symm

private theorem grM_J {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (σ : R →ₐ[O] R) :
    GrM σ pq pq (Jmat R 3) := by
  intro a b
  unfold Jmat
  split_ifs with e
  · have : pq a - pq b = 0 := by
      subst e
      revert a
      decide
    rw [this]
    show σ 1 = sg R 0 * 1
    rw [map_one, mul_one]
    exact (pow_zero _).symm
  · exact Submodule.zero_mem _

private theorem grM_tr {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (σ : R →ₐ[O] R)
    (α β : Fin 3 → ZMod 2) (M : Matrix (Fin 3) (Fin 3) R) (h : GrM σ α β M) : GrM σ β α Mᵀ := by
  intro a b
  have e : σ (M b a) = sg R (α b - β a) * M b a := h b a
  show σ (M b a) = sg R (β a - α b) * M b a
  rw [e, sg_sub, sg_sub, mul_comm (sg R (α b))]

theorem UpperTheory.V.Fr.ep_grm :
    ∀ {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (σ : R →ₐ[O] R), (∀ α, GrM σ α α 1) ∧ (∀ α β M N, GrM σ α β M → GrM σ α β N → GrM σ α β (M - N)) ∧ (∀ α β γ M N, GrM σ α β M → GrM σ β γ N → GrM σ α γ (M * N)) ∧ (∀ α β (g : GL (Fin 3) R), GrM σ α β (g : Matrix (Fin 3) (Fin 3) R) → GrM σ β α ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R)) ∧ ∀ (e : ℤˣ) (g : GL (Fin 3) R), GrM σ pq pq (g : Matrix (Fin 3) (Fin 3) R) → GrM σ pq pq ((sgnAct 3 R e g : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) := by
  intro O R _ _ _ σ
  refine ⟨fun α => ?_, fun α β M N h h' a b => Submodule.sub_mem _ (h a b) (h' a b), grM_mul σ, grM_inv σ,
    fun e g h => ?_⟩
  · rw [grM_iff, map_one, Matrix.mul_one, sgM_sq]
  · rcases Int.units_eq_one_or e with rfl | rfl
    · rwa [sgnAct_one]
    · rw [sgnAct_neg_one, theta_val]
      exact grM_mul σ _ pq _ _ _ (grM_mul σ _ pq _ _ _ (grM_J σ) (grM_tr σ _ _ _ (grM_inv σ _ _ g h))) (grM_J σ)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.IwahoriFactorizationLowerDiagUpper
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.iwahori_factorization_lower_diag_upper :
    ∀ {H Q : Type} [CommRing Q] (r : H → Matrix (Fin 3) (Fin 3) Q) (ψ : Fin 3 → H → Q) (s₀ : H), (∀ i j, i ≠ j → IsUnit (ψ i s₀ - ψ j s₀)) → (∀ s i j, i < j → r s i j = 0) → (∀ s i, r s i i = ψ i s) → (∀ g, ordProd r ψ g = 0) → ∃ α β γ : Q, ∀ s, r s 1 0 = (ψ 0 s - ψ 1 s) * α ∧ r s 2 1 = (ψ 1 s - ψ 2 s) * β ∧ r s 2 0 = (ψ 0 s - ψ 2 s) * γ - (ψ 1 s - ψ 2 s) * (α * β) := by
  intro H Q _ r ψ s₀ hu hup hd h0
  have key : ∀ a b c : H, (r a - ψ 0 a • 1) * ((r b - ψ 1 b • 1) * (r c - ψ 2 c • 1)) = 0 := by
    intro a b c
    simpa [ordProd, List.ofFn_succ] using h0 ![a, b, c]
  obtain ⟨u', e1⟩ : ∃ u' : Q, (ψ 0 s₀ - ψ 1 s₀) * u' = 1 := ⟨_, (hu 0 1 (by decide)).mul_val_inv⟩
  obtain ⟨v', e2⟩ : ∃ v' : Q, (ψ 1 s₀ - ψ 2 s₀) * v' = 1 := ⟨_, (hu 1 2 (by decide)).mul_val_inv⟩
  obtain ⟨w', e3⟩ : ∃ w' : Q, (ψ 0 s₀ - ψ 2 s₀) * w' = 1 := ⟨_, (hu 0 2 (by decide)).mul_val_inv⟩
  have hx : ∀ s, r s 1 0 = (ψ 0 s - ψ 1 s) * (r s₀ 1 0 * u') := by
    intro s
    have e := congrFun (congrFun (key s₀ s s₀) 1) 0
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply, hd, hup _ 0 1 (by decide),
      hup _ 0 2 (by decide), hup _ 1 2 (by decide)] at e
    have F : r s₀ 1 0 * (ψ 0 s - ψ 1 s) = (ψ 0 s₀ - ψ 1 s₀) * r s 1 0 := by
      linear_combination w' * e - (r s₀ 1 0 * (ψ 0 s - ψ 1 s) - (ψ 0 s₀ - ψ 1 s₀) * r s 1 0) * e3
    linear_combination (-(r s 1 0)) * e1 - u' * F
  have hy : ∀ s, r s 2 1 = (ψ 1 s - ψ 2 s) * (r s₀ 2 1 * v') := by
    intro s
    have e := congrFun (congrFun (key s₀ s₀ s) 2) 1
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply, hd, hup _ 0 1 (by decide),
      hup _ 0 2 (by decide), hup _ 1 2 (by decide)] at e
    have G : r s₀ 2 1 * (ψ 1 s - ψ 2 s) = (ψ 1 s₀ - ψ 2 s₀) * r s 2 1 := by
      linear_combination (-w') * e - (r s₀ 2 1 * (ψ 1 s - ψ 2 s) - (ψ 1 s₀ - ψ 2 s₀) * r s 2 1) * e3
    linear_combination (-(r s 2 1)) * e2 - v' * G
  refine ⟨r s₀ 1 0 * u', r s₀ 2 1 * v',
    r s₀ 1 0 * u' * (r s₀ 2 1 * v') +
      ((ψ 1 s₀ - ψ 2 s₀) * r s₀ 2 0 - r s₀ 2 1 * r s₀ 1 0) * w' * v', fun s => ⟨hx s, hy s, ?_⟩⟩
  have e := congrFun (congrFun (key s₀ s₀ s) 2) 0
  simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply, hd, hup _ 0 1 (by decide),
    hup _ 0 2 (by decide), hup _ 1 2 (by decide)] at e
  have Z : (ψ 0 s₀ - ψ 2 s₀) * (ψ 1 s₀ - ψ 2 s₀) * r s 2 0 =
      (ψ 0 s₀ - ψ 2 s₀) * r s₀ 2 1 * r s 1 0 +
        (ψ 0 s - ψ 2 s) * ((ψ 1 s₀ - ψ 2 s₀) * r s₀ 2 0 - r s₀ 2 1 * r s₀ 1 0) := by
    linear_combination e
  linear_combination w' * v' * Z + r s₀ 2 1 * v' * hx s +
    (r s₀ 2 1 * v' * r s 1 0 - r s 2 0) * e3 - (ψ 0 s₀ - ψ 2 s₀) * w' * r s 2 0 * e2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LowerTriangularConjAntidiag
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem jconj {K : Type} [CommRing K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    (Jmat K n * Mᵀ * Jmat K n) i j = M j.rev i.rev := by
  simp only [Matrix.mul_apply, Jmat]
  simp [Fin.rev_eq_iff]
  simp [eq_comm (a := j), Fin.rev_eq_iff]

private theorem ord3 {K : Type} [CommRing K] (α β γ p₀ q₀ p₁ q₁ p₂ q₂ : K) :
    (!![p₀, 0, 0; (p₀ - 1) * α, 1, 0; (p₀ - q₀) * γ - (1 - q₀) * (α * β), (1 - q₀) * β, q₀] -
        p₀ • (1 : Matrix (Fin 3) (Fin 3) K)) *
      ((!![p₁, 0, 0; (p₁ - 1) * α, 1, 0; (p₁ - q₁) * γ - (1 - q₁) * (α * β), (1 - q₁) * β, q₁] -
        (1 : K) • (1 : Matrix (Fin 3) (Fin 3) K)) *
      (!![p₂, 0, 0; (p₂ - 1) * α, 1, 0; (p₂ - q₂) * γ - (1 - q₂) * (α * β), (1 - q₂) * β, q₂] -
        q₂ • (1 : Matrix (Fin 3) (Fin 3) K))) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply] <;> ring

private theorem low_pol {K : Type} [CommRing K] (p q y z a : K) :
    !![q, 0, 0; z, 1, 0; a, y, p] = Jmat K 3 * (!![p, 0, 0; y, 1, 0; a, z, q])ᵀ * Jmat K 3 := by
  ext i j
  rw [jconj]
  fin_cases i <;> fin_cases j <;> rfl

private theorem low_mul {K : Type} [CommRing K] (p q y z a p' q' y' z' a' : K) :
    !![p * p', 0, 0; y * p' + y', 1, 0; a * p' + z * y' + q * a', z + q * z', q * q'] =
      !![p, 0, 0; y, 1, 0; a, z, q] * !![p', 0, 0; y', 1, 0; a', z', q'] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

private theorem low_diag {K : Type} [CommRing K] (p q p' q' y a : K) (i j : Fin 3) (h : i ≠ j) :
    (!![p, 0, 0; y, 1, 0; a, y, q] - !![p', 0, 0; y, 1, 0; a, y, q'] : Matrix (Fin 3) (Fin 3) K) i j = 0 := by
  fin_cases i <;> fin_cases j <;> simp at h ⊢

private theorem low_up {K : Type} [CommRing K] (p q y z a : K) (i j : Fin 3) (h : i < j) :
    (!![p, 0, 0; y, 1, 0; a, z, q] : Matrix (Fin 3) (Fin 3) K) i j = 0 := by
  fin_cases i <;> fin_cases j <;> simp at h ⊢

theorem UpperTheory.lowerTriangular_conj_antidiag :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ : ℕ}, F.Ok C₀ → ∀ (Q : Type) [CommRing Q] [Algebra k Q] (y a : F.G0 → Q), F.Low Q y a → ∃ ρ : NRep F 3 Q, ρ.IsBar (algebraMap k Q) ∧ ρ.triM = ⊥ ∧ (∀ i j, IsLocallyConstant fun g => ρ.r g i j) ∧ (∀ g, ρ.r g 1 0 = y g) ∧ ∀ g, ρ.r g 2 0 = a g := by
  intro l _ k _ _ F C₀ hF Q _ _ y a h
  obtain ⟨s1, s2, s3, s4, -⟩ := UpperTheory.V.Fr.star hF
  have y1 : y 1 = 0 := by
    have := h.muly 1 1
    simpa using this
  have st1 : F.star 1 = 1 := by simp [Frame.star]
  have a1 : a 1 = 0 := by
    have := h.mula 1 1
    simpa [y1] using this
  let p : F.G0 → Q := fun g => algebraMap k Q (F.Ψ g : k)
  let q : F.G0 → Q := fun g => algebraMap k Q (((F.Ψ g)⁻¹ : kˣ) : k)
  have pm : ∀ g g', p (g * g') = p g * p g' := fun g g' => by simp [p]
  have qm : ∀ g g', q (g * g') = q g * q g' := fun g g' => by simp [q, mul_comm]
  have ps : ∀ g, p (F.star g) = q g := fun g => by simp only [p, q, s3]
  have qs : ∀ g, q (F.star g) = p g := fun g => by simp only [p, q, s3, inv_inv]
  have ym : ∀ g g', y (g * g') = y g * p g' + y g' := fun g g' => by
    rw [h.muly, Algebra.smul_def, mul_comm]
  have am : ∀ g g', a (g * g') = a g * p g' + y (F.star g) * y g' + q g * a g' := fun g g' => by
    rw [h.mula, Algebra.smul_def, Algebra.smul_def, mul_comm _ (a g)]
  have zm : ∀ g g', y (F.star (g * g')) = y (F.star g) + q g * y (F.star g') := fun g g' => by
    rw [s2, ym, ps]; ring
  let r : F.G0 →* Matrix (Fin 3) (Fin 3) Q :=
    { toFun := fun g => !![p g, 0, 0; y g, 1, 0; a g, y (F.star g), q g]
      map_one' := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [p, q, y1, a1, st1]
      map_mul' := fun g g' => by
        rw [zm, pm, qm, ym, am, low_mul] }
  have hr : ∀ g, r g = !![p g, 0, 0; y g, 1, 0; a g, y (F.star g), q g] := fun _ => rfl
  have w0 : w 3 0 = 1 := rfl
  have w1 : w 3 1 = 0 := rfl
  have w2 : w 3 2 = -1 := rfl
  let ψ : ∀ v, Fin 3 → F.Gv v →* Qˣ := fun v i =>
    (Units.map (algebraMap k Q).toMonoidHom).comp ((zpowGroupHom (w 3 i)).comp (F.Ψ.comp (F.loc v)))
  have hψ : ∀ v i g, (ψ v i g : Q) = algebraMap k Q ((F.Ψ (F.loc v g) ^ w 3 i : kˣ) : k) := fun _ _ _ => rfl
  have hΨ : IsLocallyConstant fun g : F.G0 => F.Ψ g := by
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun g => ?_
    have hc : Continuous fun x : F.G0 => (g : F.Γ)⁻¹ * (x : F.Γ) := by fun_prop
    have : ∀ᶠ x : F.G0 in nhds g, (g : F.Γ)⁻¹ * (x : F.Γ) ∈ (F.Ψ.ker : Set F.Γ) :=
      (hF.Ψ_open.preimage hc).mem_nhds (by simp)
    refine this.mono fun x hx => ?_
    have hx' : F.Ψ ((g : F.Γ)⁻¹ * (x : F.Γ)) = 1 := hx
    rw [map_mul, map_inv, inv_mul_eq_one] at hx'
    exact hx'.symm
  have lp : IsLocallyConstant p := hΨ.comp fun u : kˣ => algebraMap k Q (u : k)
  have lq : IsLocallyConstant q := hΨ.comp fun u : kˣ => algebraMap k Q ((u⁻¹ : kˣ) : k)
  have lz : IsLocallyConstant fun g => y (F.star g) := h.lcy.comp_continuous s4
  refine ⟨⟨r, ψ, fun g => ?_, fun i j hij => ?_, fun v g => ?_⟩, ⟨fun g i => ?_, hψ⟩, ?_, fun i j => ?_,
    fun g => rfl, fun g => rfl⟩
  · rw [hr, hr, ps, qs, s1, h.pol, ← low_pol]
  · rw [hr, hr, s1, h.pol, ← h.nor]
    exact low_diag _ _ _ _ _ _ i j hij
  · obtain ⟨α, β, γ, H⟩ := h.loc v
    have e : ∀ s, r (F.loc0 v s) = !![p (F.loc0 v s), 0, 0; (p (F.loc0 v s) - 1) * α, 1, 0;
        (p (F.loc0 v s) - q (F.loc0 v s)) * γ - (1 - q (F.loc0 v s)) * (α * β), (1 - q (F.loc0 v s)) * β,
        q (F.loc0 v s)] := fun s => by
      obtain ⟨h1, h2, h3⟩ := H s
      rw [hr, h1, h2, h3]
      simp only [Algebra.smul_def, map_sub, map_one]
      rfl
    have e0 : ∀ s, (ψ v 0 s : Q) = p (F.loc0 v s) := fun s => by rw [hψ, w0, zpow_one]; rfl
    have e1 : ∀ s, (ψ v 1 s : Q) = 1 := fun s => by rw [hψ, w1, zpow_zero]; simp
    have e2 : ∀ s, (ψ v 2 s : Q) = q (F.loc0 v s) := fun s => by rw [hψ, w2, _root_.zpow_neg_one]; rfl
    have := ord3 α β γ (p (F.loc0 v (g 0))) (q (F.loc0 v (g 0))) (p (F.loc0 v (g 1))) (q (F.loc0 v (g 1)))
      (p (F.loc0 v (g 2))) (q (F.loc0 v (g 2)))
    rw [← e, ← e, ← e] at this
    rw [ordProd, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_cons,
      List.prod_cons, List.prod_nil, mul_one]
    show (r _ - (ψ v 0 (g 0) : Q) • 1) * ((r _ - (ψ v 1 (g 1) : Q) • 1) * (r _ - (ψ v 2 (g 2) : Q) • 1)) = 0
    rw [e0, e1, e2]
    exact this
  · show r g i i = _
    rw [hr]
    fin_cases i
    · simp [w0, p]
    · simp [w1]
    · simp [w2, q]
  · refine Ideal.span_eq_bot.2 ?_
    rintro x ⟨g, i, j, hij, rfl⟩
    show r g i j = 0
    rw [hr]
    exact low_up _ _ _ _ _ i j hij
  · show IsLocallyConstant fun g => r g i j
    simp only [hr]
    fin_cases i <;> fin_cases j
    exacts [lp, IsLocallyConstant.const 0, IsLocallyConstant.const 0, h.lcy, IsLocallyConstant.const 1,
      IsLocallyConstant.const 0, h.lca, lz, lq]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrMazur
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.pr_mazur :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (H : Type) [AddCommGroup H] [Module (ResidueField O) H] [Module.Finite (ResidueField O) H], HasObs O R H → ∃ (p : MvPowerSeries (Fin (Module.finrank (ResidueField O) (Tan O R))) O →ₐ[O] R) (f : Fin (Module.finrank (ResidueField O) H) → MvPowerSeries (Fin (Module.finrank (ResidueField O) (Tan O R))) O), Function.Surjective p ∧ RingHom.ker p = Ideal.span (Set.range f) := by
  intro O _ _ _ _ _ R _ _ _ H _ _ _ hob
  obtain ⟨a, π, f, hπ, hker, hcard⟩ := obs_pres O R H (by
    intro A _ _ _ p hp hK κ _ ε hspan hmin
    obtain ⟨ob, hob'⟩ := hob A p hp hK
    obtain ⟨co, hco⟩ := pr_dualb O A (RingHom.ker p) κ ε hK hspan hmin
    refine ⟨fun u => ob (co u), ?_⟩
    intro c hc A' _ _ _ p' p'' η hp' hcomp hη hη0 hε
    have hw0 : ob (∑ u, residue O (c u) • co u) = 0 := by
      rw [map_sum]
      simp only [map_smul]
      exact hc
    refine hob' _ hw0 A' p' p'' hcomp hp' ?_
    intro y hy
    obtain ⟨b, hb, hy'⟩ := hco y
    rw [hy', map_sum]
    simp only [map_smul, hε, smul_smul]
    rw [← Finset.sum_smul]
    have hm : ∑ u, b u * c u ∈ maximalIdeal O := by
      rw [← residue_eq_zero_iff, map_sum]
      simp only [map_mul, hb]
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] at hy
      rw [← hy]
      exact Finset.sum_congr rfl (fun u _ => mul_comm _ _)
    haveI := IsCO.isLocalHom (O := O) (R := A')
    rw [Algebra.smul_def]
    exact hη _ (map_nonunit (algebraMap O A') _ hm))
  have hT := (pr_tan O R).2
  haveI := (pr_tan O R).1
  classical
  haveI := Fintype.ofFinite (ResidueField O)
  haveI : Finite (Tan O R) := Module.finite_of_finite (ResidueField O)
  haveI := Fintype.ofFinite (Tan O R)
  have h2 : 2 ≤ Fintype.card (ResidueField O) := Fintype.one_lt_card
  have hTc : Nat.card (Tan O R) =
      Fintype.card (ResidueField O) ^ Module.finrank (ResidueField O) (Tan O R) := by
    rw [Nat.card_eq_fintype_card]
    exact Module.card_eq_pow_finrank
  have ha : a = Module.finrank (ResidueField O) (Tan O R) := by
    apply Nat.pow_right_injective h2
    change Fintype.card (ResidueField O) ^ a = Fintype.card (ResidueField O) ^ _
    rw [← hTc, ← hT, hcard, Nat.card_eq_fintype_card]
  subst ha
  exact ⟨π, f, hπ, hker⟩
end

