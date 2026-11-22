import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0037
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0012
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteOpenHopfOrder
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0031
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0002
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FirstOrderPointsCommute
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0003
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagBasisChangeIntegral
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0024
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0032
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemOfAevalEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0018
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0033
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUnitOfSumEqOne
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell

open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm

def kMinor {F : Type} [CommRing F] {n r : ℕ} (A : Matrix (Fin n) (Fin r) F) (k : ℕ) (hk : k ≤ r)
    (I : Fin k → Fin n) : F :=
  (A.submatrix I (Fin.castLE hk)).det

theorem stepMinor_eq_kMinor {F : Type} [CommRing F] {n r : ℕ} (A : Matrix (Fin n) (Fin r) F) (i : Fin r)
    (J : Fin ((i : ℕ) + 1) → Fin n) : stepMinor A i J = kMinor A ((i : ℕ) + 1) i.2 J := rfl

def NormAt {F : Type} [Field F] (O : Subring F) {n r : ℕ} (Y : Matrix (Fin n) (Fin r) F) (k : ℕ) (hk : k ≤ r)
    (I : Fin k → Fin n) : Prop :=
  kMinor Y k hk I ≠ 0 ∧ ∀ I' : Fin k → Fin n, kMinor Y k hk I' / kMinor Y k hk I ∈ O

theorem normAt_zero {F : Type} [Field F] (O : Subring F) {n r : ℕ} (Y : Matrix (Fin n) (Fin r) F)
    (I : Fin 0 → Fin n) : NormAt O Y 0 (Nat.zero_le r) I := by
  refine ⟨by simp [kMinor], fun I' => ?_⟩
  simpa [kMinor] using O.one_mem

theorem det_mul_expand {F : Type} [CommRing F] {k r : ℕ} (A : Matrix (Fin k) (Fin r) F)
    (B : Matrix (Fin r) (Fin k) F) :
    (A * B).det = ∑ f : Fin k → Fin r, (∏ a, A a (f a)) * (B.submatrix f id).det :=
  _root_.UpperTheory.Reformulated.B.DetMulExpand.det_mul_expand A B

theorem kMinor_mul_expand {F : Type} [CommRing F] {n m r : ℕ} (A : Matrix (Fin n) (Fin m) F)
    (B : Matrix (Fin m) (Fin r) F) (k : ℕ) (hk : k ≤ r) (J : Fin k → Fin n) :
    kMinor (A * B) k hk J = ∑ I : Fin k → Fin m, (∏ a, A (J a) (I a)) * kMinor B k hk I := by
  unfold kMinor
  have : (A * B).submatrix J (Fin.castLE hk) = A.submatrix J id * B.submatrix id (Fin.castLE hk) := by
    ext a b
    simp [Matrix.mul_apply]
  rw [this, det_mul_expand]
  rfl

theorem kMinor_mul_div_mem {F : Type} [Field F] (D : Subring F) {n m r : ℕ} (A : Matrix (Fin n) (Fin m) F)
    (B : Matrix (Fin m) (Fin r) F) (k : ℕ) (hk : k ≤ r) (c : F) (hA : ∀ a b, A a b ∈ D)
    (hB : ∀ I, kMinor B k hk I / c ∈ D) (J : Fin k → Fin n) : kMinor (A * B) k hk J / c ∈ D := by
  rw [kMinor_mul_expand, Finset.sum_div]
  refine D.sum_mem fun I _ => ?_
  rw [mul_div_assoc]
  exact D.mul_mem (D.prod_mem fun a _ => hA _ _) (hB I)

theorem exists_unit_of_sum_eq_one {F : Type} [Field F] (O : Subring F) [IsLocalRing O] {ι : Type}
    (s : Finset ι) (a : ι → F) (ha : ∀ i ∈ s, a i ∈ O) (h1 : ∑ i ∈ s, a i = 1) :
    ∃ i ∈ s, a i ≠ 0 ∧ (a i)⁻¹ ∈ O := by
  classical
  by_contra hcon
  push_neg at hcon
  have key : ∀ t : Finset ι, t ⊆ s → ∃ h : ∑ i ∈ t, a i ∈ O, (⟨_, h⟩ : O) ∈ IsLocalRing.maximalIdeal O := by
    intro t
    induction t using Finset.cons_induction with
    | empty => intro _; exact ⟨by simp, Ideal.zero_mem _⟩
    | cons i t hi ih =>
      intro hts
      rw [Finset.cons_eq_insert, Finset.insert_subset_iff] at hts
      obtain ⟨h2, h3⟩ := ih hts.2
      have h4 : a i ∈ O := ha i hts.1
      have h5 : (⟨a i, h4⟩ : O) ∈ IsLocalRing.maximalIdeal O := by
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        intro hu
        obtain ⟨v, hv⟩ := hu.exists_right_inv
        have hv' : a i * (v : F) = 1 := congrArg Subtype.val hv
        have h0 : a i ≠ 0 := left_ne_zero_of_mul_eq_one hv'
        refine hcon i hts.1 h0 ?_
        rw [eq_comm.1 (eq_inv_of_mul_eq_one_right hv')]
        exact v.2
      rw [Finset.sum_cons]
      refine ⟨O.add_mem h4 h2, ?_⟩
      exact Ideal.add_mem _ h5 h3
  obtain ⟨h, hm⟩ := key s subset_rfl
  have : (⟨∑ i ∈ s, a i, h⟩ : O) = 1 := Subtype.ext h1
  rw [this] at hm
  exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 hm)

theorem kMinor_mul_upper {F : Type} [CommRing F] {n r : ℕ} (A : Matrix (Fin n) (Fin r) F)
    (C : Matrix (Fin r) (Fin r) F) (hC : ∀ l k, k < l → C l k = 0) (k : ℕ) (hk : k ≤ r) (I : Fin k → Fin n) :
    kMinor (A * C) k hk I = kMinor A k hk I * kMinor C k hk (Fin.castLE hk) := by
  unfold kMinor
  rw [← Matrix.det_mul]
  congr 1
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  symm
  refine Finset.sum_of_injOn (Fin.castLE hk) (Fin.castLE_injective hk).injOn (fun _ _ => Finset.mem_univ _)
    (fun j _ hj => ?_) (fun _ _ => rfl)
  have hjk : (Fin.castLE hk b) < j := by
    rw [Fin.lt_def]
    by_contra hlt
    have hjk' : (j : ℕ) < k := by
      have := b.2
      simp only [Fin.val_castLE] at hlt
      omega
    exact hj ⟨⟨j, hjk'⟩, by simp, by ext; simp⟩
  rw [hC _ _ hjk, mul_zero]

theorem kMinor_lower_lead {F : Type} [CommRing F] {r : ℕ} (L : Matrix (Fin r) (Fin r) F)
    (h0 : ∀ l k, l < k → L l k = 0) (h1 : ∀ l, L l l = 1) (k : ℕ) (hk : k ≤ r) :
    kMinor L k hk (Fin.castLE hk) = 1 := by
  unfold kMinor
  rw [Matrix.det_of_lowerTriangular]
  · simp [h1]
  · intro a b hab
    exact h0 _ _ (by simpa using hab)

def lastRow {r : ℕ} (k l : Fin r) : Fin ((k : ℕ) + 1) → Fin r := fun a =>
  if h : (a : ℕ) = k then l else ⟨a, by have := a.2; have := k.2; omega⟩

theorem kMinor_lower_lastRow {F : Type} [CommRing F] {r : ℕ} (L : Matrix (Fin r) (Fin r) F)
    (h0 : ∀ l k, l < k → L l k = 0) (h1 : ∀ l, L l l = 1) (k l : Fin r) (hkl : k < l) :
    kMinor L ((k : ℕ) + 1) k.2 (lastRow k l) = L l k := by
  unfold kMinor
  rw [Matrix.det_of_lowerTriangular, Fin.prod_univ_castSucc]
  · have e1 : ∀ a : Fin (k : ℕ), (L.submatrix (lastRow k l) (Fin.castLE k.2)) a.castSucc a.castSucc = 1 := by
      intro a
      have : lastRow k l a.castSucc = Fin.castLE k.2 a.castSucc := by
        have := a.2
        ext
        simp [lastRow, Nat.ne_of_lt this]
      simp [this, h1]
    have e2 : (L.submatrix (lastRow k l) (Fin.castLE k.2)) (Fin.last _) (Fin.last _) = L l k := by
      have a1 : lastRow k l (Fin.last _) = l := by simp [lastRow]
      have a2 : Fin.castLE k.2 (Fin.last (k : ℕ)) = k := by ext; simp
      simp [a1, a2]
    rw [Finset.prod_congr rfl (fun a _ => e1 a), e2]
    simp
  · intro a b hab
    have hab' : a < b := by simpa using hab
    have hb := b.2
    have ha : (a : ℕ) ≠ k := by
      have : (a : ℕ) < b := hab'
      omega
    simp only [Matrix.submatrix_apply, lastRow, dif_neg ha]
    exact h0 _ _ (by rw [Fin.lt_def]; simpa using hab')

theorem exists_normAt {F : Type} [Field F] (O : Subring F) [IsLocalRing O] {n r : ℕ}
    (A : Matrix (Fin n) (Fin r) F) (N : Matrix (Fin r) (Fin n) F) (hA : ∀ a b, A a b ∈ O)
    (hN : ∀ a b, N a b ∈ O) (hNA : N * A = 1) (Y : Matrix (Fin r) (Fin r) F) (k : ℕ) (hk : k ≤ r)
    (J : Fin k → Fin n) (hJ : NormAt O (A * Y) k hk J) : ∃ I, NormAt O Y k hk I := by
  obtain ⟨hP, hr⟩ := hJ
  set P := kMinor (A * Y) k hk J with hPdef
  have hY : Y = N * (A * Y) := by rw [← Matrix.mul_assoc, hNA, Matrix.one_mul]
  have hyO : ∀ I, kMinor Y k hk I / P ∈ O := fun I => by
    rw [hY]
    exact kMinor_mul_div_mem O N (A * Y) k hk P hN hr I
  have h1 : ∑ I : Fin k → Fin r, (∏ a, A (J a) (I a)) * (kMinor Y k hk I / P) = 1 := by
    have : P = ∑ I : Fin k → Fin r, (∏ a, A (J a) (I a)) * kMinor Y k hk I := kMinor_mul_expand A Y k hk J
    simp only [← mul_div_assoc]
    rw [← Finset.sum_div, ← this, div_self hP]
  obtain ⟨I, -, hne, hinv⟩ := exists_unit_of_sum_eq_one O Finset.univ _
    (fun I _ => O.mul_mem (O.prod_mem fun a _ => hA _ _) (hyO I)) h1
  have hc : (∏ a, A (J a) (I a)) ≠ 0 := left_ne_zero_of_mul hne
  have hd : kMinor Y k hk I / P ≠ 0 := right_ne_zero_of_mul hne
  have hy : kMinor Y k hk I ≠ 0 := fun h => hd (by rw [h, zero_div])
  refine ⟨I, hy, fun I' => ?_⟩
  have e : kMinor Y k hk I' / kMinor Y k hk I =
      (kMinor Y k hk I' / P) * ((∏ a, A (J a) (I a)) * ((∏ a, A (J a) (I a)) * (kMinor Y k hk I / P))⁻¹) := by
    field_simp
  rw [e]
  exact O.mul_mem (hyO I') (O.mul_mem (O.prod_mem fun a _ => hA _ _) hinv)

theorem kMinor_mem {F : Type} [CommRing F] (D : Subring F) {n r : ℕ} (A : Matrix (Fin n) (Fin r) F)
    (hA : ∀ a b, A a b ∈ D) (k : ℕ) (hk : k ≤ r) (I : Fin k → Fin n) : kMinor A k hk I ∈ D := by
  unfold kMinor
  rw [Matrix.det_apply']
  refine D.sum_mem fun σ _ => D.mul_mem (intCast_mem D _) (D.prod_mem fun a _ => hA _ _)

theorem ratio_eq_kMinor {F : Type} [Field F] {r : ℕ} (Y C V : Matrix (Fin r) (Fin r) F)
    (hC : ∀ l k, k < l → C l k = 0) (hV0 : ∀ l k, l < k → V l k = 0) (hV1 : ∀ l, V l l = 1)
    (h : Y * C = V) (k : ℕ) (hk : k ≤ r) (I : Fin k → Fin r) (h0 : kMinor Y k hk (Fin.castLE hk) ≠ 0) :
    kMinor Y k hk I / kMinor Y k hk (Fin.castLE hk) = kMinor V k hk I := by
  have h1 := kMinor_lower_lead V hV0 hV1 k hk
  rw [← h, kMinor_mul_upper Y C hC] at h1
  rw [← h, kMinor_mul_upper Y C hC, div_eq_iff h0]
  linear_combination (-(kMinor Y k hk I)) * h1

theorem entries_mem {Ω K : Type} [Field Ω] [Field K] [Algebra Ω K] (Fd : IntermediateField Ω K) {r : ℕ}
    (T' : Matrix (Fin r) (Fin r) Ω) (hT : T'.det ≠ 0) (u C V : Matrix (Fin r) (Fin r) K)
    (hu0 : ∀ l k, l < k → u l k = 0) (hu1 : ∀ l, u l l = 1) (hC : ∀ l k, k < l → C l k = 0)
    (hV0 : ∀ l k, l < k → V l k = 0) (hV1 : ∀ l, V l l = 1)
    (h : T'.map (algebraMap Ω K) * u * C = V) (hF : ∀ l k, V l k ∈ Fd) (l k : Fin r) (hkl : k < l) :
    u l k ∈ Fd := by
  have hdet : IsUnit T'.det := isUnit_iff_ne_zero.2 hT
  have hTi : (T'⁻¹).map (algebraMap Ω K) * T'.map (algebraMap Ω K) = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hdet, Matrix.map_one _ (map_zero _) (map_one _)]
  set Q := (T'⁻¹).map (algebraMap Ω K) * V with hQ
  have hQ' : u * C = Q := by
    rw [hQ, ← h, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hTi, Matrix.one_mul]
  have hQF : ∀ a b, Q a b ∈ Fd := fun a b => by
    rw [hQ, Matrix.mul_apply]
    exact sum_mem fun j _ => mul_mem (Fd.algebraMap_mem _) (hF _ _)
  have hk : (k : ℕ) + 1 ≤ r := k.2
  have h1 := kMinor_lower_lead V hV0 hV1 _ hk
  rw [← h, kMinor_mul_upper _ C hC] at h1
  have hc : kMinor C _ hk (Fin.castLE hk) ≠ 0 := right_ne_zero_of_mul_eq_one h1
  have h2 := kMinor_mul_upper u C hC _ hk (lastRow k l)
  have h3 := kMinor_mul_upper u C hC _ hk (Fin.castLE hk)
  rw [kMinor_lower_lastRow u hu0 hu1 k l hkl, hQ'] at h2
  rw [kMinor_lower_lead u hu0 hu1, hQ', _root_.one_mul] at h3
  have e : u l k = kMinor Q _ hk (lastRow k l) / kMinor Q _ hk (Fin.castLE hk) := by
    rw [h2, h3, mul_div_assoc, div_self hc, mul_one]
  rw [e]
  exact div_mem (kMinor_mem Fd.toSubalgebra.toSubring Q hQF _ hk _) (kMinor_mem Fd.toSubalgebra.toSubring Q hQF _ hk _)

theorem genU_zero (Ω : Type) [Field Ω] {S : Type} (r : S → ℕ) (s : S) (l k : Fin (r s)) (h : l < k) :
    genU Ω r s l k = 0 := by
  unfold genU
  rw [dif_neg (not_lt.2 h.le), if_neg h.ne]

theorem genU_one (Ω : Type) [Field Ω] {S : Type} (r : S → ℕ) (s : S) (l : Fin (r s)) :
    genU Ω r s l l = 1 := by
  unfold genU
  simp

theorem genU_gen (Ω : Type) [Field Ω] {S : Type} (r : S → ℕ) (q : GenIx r) :
    genU Ω r q.1 q.2.1.1 q.2.1.2 = algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) (MvPolynomial.X q) := by
  unfold genU
  rw [dif_pos q.2.2]
  rfl

theorem genU_indep (Ω : Type) [Field Ω] {S : Type} (r : S → ℕ) :
    AlgebraicIndependent Ω (fun q : GenIx r =>
      algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) (MvPolynomial.X q)) :=
  (MvPolynomial.algebraicIndependent_X (GenIx r) Ω).map'
    (f := IsScalarTower.toAlgHom Ω (MvPolynomial (GenIx r) Ω) (GenField Ω r))
    (IsFractionRing.injective _ _)

end GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteOpenHopfOrderStatement
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_open_hopf_order : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens), Γ.IsFinOpenSub U → ∃ (H : Subgroup T) (A : Subalgebra R (H → R)), (∀ t, t ∈ H ↔ ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U) ∧ IsHopfOrder A ∧ ∀ f : H → R, f ∈ A ↔ ∃ s : Γ(Γ.G.left, U), ∀ (t : H) (h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U), valAt (Γ.pt t).left U h s = algebraMap R _ (f t) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.SubOrder.hopfOrder_of_finOpenSub | exact GlobalTheory.CompanionTheory.Ar.BT.SubOrder.hopfOrder_of_finOpenSub | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.SubOrder.hopfOrder_of_finOpenSub <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteSchemeMapFromSpecialFibreStatement
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_scheme_map_from_special_fibre : ∀ (R : Type) [CommRing R] [IsLocalRing R] (X Y : Over (Spec (CommRingCat.of R))) [IsFinite X.hom] [IsFinite Y.hom] (f : X ⟶ Y), ∃ (P Q : Type) (_ : CommRing P) (_ : CommRing Q) (_ : Algebra R P) (_ : Algebra R Q) (φ : Q →ₐ[R] P) (i : X.left ≅ Spec (CommRingCat.of P)) (j : Y.left ≅ Spec (CommRingCat.of Q)) (i₀ : ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).obj X).left ≅ Spec (CommRingCat.of (IsLocalRing.ResidueField R ⊗[R] P))) (j₀ : ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).obj Y).left ≅ Spec (CommRingCat.of (IsLocalRing.ResidueField R ⊗[R] Q))), Module.Finite R P ∧ Module.Finite R Q ∧ (Flat X.hom → Module.Flat R P) ∧ f.left = i.hom ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ j.inv ∧ ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map f).left = i₀.hom ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id R (IsLocalRing.ResidueField R)) φ).toRingHom) ≫ j₀.inv := by
  first | exact @GlobalTheory.CompanionTheory.FinFlatModel.exists_algHom_model | exact GlobalTheory.CompanionTheory.FinFlatModel.exists_algHom_model | (intros; apply GlobalTheory.CompanionTheory.FinFlatModel.exists_algHom_model <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FirstOrderPointsCommuteStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.first_order_points_commute : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (B : Type) [CommRing B] [IsLocalRing B] (b : Sp B ⟶ S) (A : Type) [CommRing A] (g : B →+* A) (J : Ideal A), J ^ 2 = ⊥ → ∀ x y : Over.mk (spMap g ≫ b) ⟶ G, spMap (Ideal.Quotient.mk J) ≫ x.left = spMap (Ideal.Quotient.mk J) ≫ (1 : Over.mk (spMap g ≫ b) ⟶ G).left → spMap (Ideal.Quotient.mk J) ≫ y.left = spMap (Ideal.Quotient.mk J) ≫ (1 : Over.mk (spMap g ≫ b) ⟶ G).left → ∀ (V : G.left.Opens) (hx : ⊤ ≤ x.left ⁻¹ᵁ V) (hy : ⊤ ≤ y.left ⁻¹ᵁ V) (hxy : ⊤ ≤ (x * y).left ⁻¹ᵁ V) (h1 : ⊤ ≤ (1 : Over.mk (spMap g ≫ b) ⟶ G).left ⁻¹ᵁ V) (f : Γ(G.left, V)), ((x * y).left.appLE V ⊤ hxy).hom f + ((1 : Over.mk (spMap g ≫ b) ⟶ G).left.appLE V ⊤ h1).hom f = (x.left.appLE V ⊤ hx).hom f + (y.left.appLE V ⊤ hy).hom f := by
  first | exact @GlobalTheory.CompanionTheory.Ar.sqzero_add | exact GlobalTheory.CompanionTheory.Ar.sqzero_add | (intros; apply GlobalTheory.CompanionTheory.Ar.sqzero_add <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagBasisChangeIntegralStatement
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_basis_change_integral : ∀ (K : Type) [Field K] (R : Subring K) [IsLocalRing R] (r : ℕ) (g : Fin r → Fin r → K), (∀ k : Fin r, ∃ D Ee : Fin ((k : ℕ) + 1) → Fin r → K, (∀ l i, D l i ∈ R) ∧ (∀ l i, Ee l i ∈ R) ∧ (∀ l l', ∑ i, Ee l i * D l' i = if l = l' then 1 else 0) ∧ ∀ l, D l ∈ flagStep K g ((k : ℕ) + 1)) → ∃ P : Matrix (Fin r) (Fin r) K, (∀ a b, P a b ∈ R) ∧ P.det ≠ 0 ∧ P.det⁻¹ ∈ R ∧ ∀ i, flagStep K (fun k a => P a k) i = flagStep K g i := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.Adapted.exists_adapted | exact GlobalTheory.CompanionTheory.Ar.FlagBun.Adapted.exists_adapted | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.Adapted.exists_adapted <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagChartGenericFieldStatement
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_chart_generic_field : ∀ (Ω : Type) [Field Ω] (E : Type) [AddCommGroup E] [Module Ω E] (κ : Type) (x : κ → Ω) (S : Type) [Fintype S] (r n : S → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω E) (c : ∀ s, Fin (r s) → E) (X' : Scheme.{0}) (ξ' : Spec (CommRingCat.of (GenField Ω r)) ⟶ X') (p' : Cpt ξ') (c₁ : κ) (J : (q : Σ s, Fin (r s)) → Fin ((q.2 : ℕ) + 1) → Fin (n q.1)), InChart ξ' (flagCoord κ x φ c) ((c₁, J) : FlagIx κ n r) p' → algebraMap Ω (GenField Ω r) (x c₁) ≠ 0 ∧ InChart ξ' (fun k => algebraMap Ω (GenField Ω r) (x k)) c₁ p' ∧ ∀ q : Σ s, Fin (r s), ((flagMat φ c q.1).submatrix (J q) (Fin.castLE q.2.2)).det ≠ 0 ∧ ∀ l j, ((flagMat φ c q.1).submatrix (Function.update (J q) l j) (Fin.castLE q.2.2)).det / ((flagMat φ c q.1).submatrix (J q) (Fin.castLE q.2.2)).det ∈ regAt ξ' p' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.inChart_flagCoord_ratios | exact GlobalTheory.CompanionTheory.Ar.FlagBun.inChart_flagCoord_ratios | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.inChart_flagCoord_ratios <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatHermUnitConstant
section
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem notMem_mCoordIdeal_of_aeval_ne_zero {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    {y : (Σ k, ι k) → Ω} {h : MRing ι} (h0 : aeval y h ≠ 0) : h ∉ mCoordIdeal y := by
  intro hh
  apply h0
  have e := UnitChart.aeval_scaled y (fun _ => 1) h
  simp only [mul_one] at e
  rw [e, show mConeMap y h = 0 from hh, map_zero]

theorem exists_flatHerm_unit : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) (α : (𝓞 F)ˣ), OverInt y φ → ∃ S : FlatHerm y φ (constLine (ι := ι) 0), S.M = 1 ∧ ∀ σ, S.κ σ = ‖σ ((α : 𝓞 F) : F)‖ := by
  intro K _ ι _ Ω _ F _ _ y φ α hO
  obtain ⟨hy, hR⟩ := hO
  choose c hc using id hy
  obtain ⟨m, G, hG, e⟩ := UnitChart.chart_form hc (hR c hc (α : 𝓞 F))
  have hα : ((α : 𝓞 F) : F) ≠ 0 := by
    simp
  have hφα : φ ((α : 𝓞 F) : F) ≠ 0 := (map_ne_zero φ).2 hα
  have hprod : (∏ k, y ⟨k, c k⟩ ^ m k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)
  have hg0 : aeval y (UnitChart.cMon c m) ≠ 0 := by rwa [UnitChart.aeval_cMon]
  have hG0 : aeval y G ≠ 0 := by rw [← e]; exact mul_ne_zero hφα hprod
  have e' : aeval y G = φ ((α : 𝓞 F) : F) * aeval y (UnitChart.cMon c m) := by
    rw [UnitChart.aeval_cMon, e]
  have hq : aeval y G / aeval y (UnitChart.cMon c m) = φ ((α : 𝓞 F) : F) := by
    rw [e', mul_div_cancel_right₀ _ hg0]
  have hinv : φ (((α⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) = (φ ((α : 𝓞 F) : F))⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← map_mul]
    have : (((α⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * ((α : 𝓞 F) : F) = 1 := by
      have h1 : ((α⁻¹ : (𝓞 F)ˣ) : 𝓞 F) * (α : 𝓞 F) = 1 := α.inv_mul
      have h2 := congrArg (algebraMap (𝓞 F) F) h1
      rw [map_mul, map_one] at h2
      exact h2
    rw [this, map_one]
  have hfn := notMem_mCoordIdeal_of_aeval_ne_zero hG0
  have hgn := notMem_mCoordIdeal_of_aeval_ne_zero hg0
  refine ⟨{ M := 1
            M_pos := one_pos
            f := G
            g := UnitChart.cMon c m
            df := m
            dg := m
            hf := hG
            hg := UnitChart.homog_cMon c m
            deg := fun k => by simp [constLine, HermLine.ofWeight]
            f_ne := hfn
            g_ne := hgn
            unit := ?_
            κ := fun σ => ‖σ ((α : 𝓞 F) : F)‖
            κ_pos := fun σ => norm_pos_iff.2 ((map_ne_zero σ).2 hα)
            κ_conj := fun σ => by simp [ComplexEmbedding.conjugate_coe_eq]
            norm := ?_ }, rfl, fun _ => rfl⟩
  · rw [isUnitSec_iff_chart K ι Ω y G _ m m hy hG (UnitChart.homog_cMon c m) hfn hgn]
    intro c' hc'
    simp only [sub_self, neg_zero, zpow_zero, Finset.prod_const_one, mul_one, hq]
    exact ⟨hR c' hc' _, hinv ▸ hR c' hc' _⟩
  · intro σ z hz
    rw [hz.2 _ m G _ hG (UnitChart.homog_cMon c m) e', norm_mul]
    simp [constLine, HermLine.ofWeight]

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatOfFlatSpecialFibreStatement
section
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_of_flat_special_fibre : ∀ (R P Q : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing P] [CommRing Q] [Algebra R P] [Algebra R Q] [Module.Finite R P] [Module.Finite R Q] [Module.Flat R Q] (φ : P →ₐ[R] Q), (Algebra.TensorProduct.map (AlgHom.id R (IsLocalRing.ResidueField R)) φ).toRingHom.Flat → φ.toRingHom.Flat := by
  first | exact @GlobalTheory.CompanionTheory.FinAlgFlat.ringHom_flat_of_fibre_flat | exact GlobalTheory.CompanionTheory.FinAlgFlat.ringHom_flat_of_fibre_flat | (intros; apply GlobalTheory.CompanionTheory.FinAlgFlat.ringHom_flat_of_fibre_flat <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameChangeByUnitMatrixStatement
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_change_by_unit_matrix : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (r : ℕ) (β : Fin r → E) (q : Cpt ξ) (P : Matrix (Fin r) (Fin r) Ω), L.IsFrameAt β q → (∀ a b, P a b ∈ regAt ξ q) → unitAt ξ q P.det → L.IsFrameAt (fun k => ∑ a, P a k • β a) q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.isFrameAt_matrix_comb | exact GlobalTheory.CompanionTheory.Ar.FlagBun.isFrameAt_matrix_comb | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.isFrameAt_matrix_comb <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameCoeffsRegularInChartStatement
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_coeffs_regular_in_chart : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (κ : Type) (x : κ → Ω) (L : Lat ξ E) (m n r : ℕ) (φ : Fin n → Module.Dual Ω E), IsTwistGen ξ x L m φ → ∀ (p : Cpt ξ) (c₁ : κ), InChart ξ x c₁ p → ∀ β : Fin r → E, L.IsFrameAt β p → ∃ B : Matrix (Fin r) (Fin n) Ω, (∀ a j, B a j ∈ regAt ξ p) ∧ (∀ j a, φ j (β a) / x c₁ ^ m ∈ regAt ξ p) ∧ B * Matrix.of (fun j a => φ j (β a) / x c₁ ^ m) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.twist_left_inverse | exact GlobalTheory.CompanionTheory.Ar.FlagBun.twist_left_inverse | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.twist_left_inverse <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameMatrixChartRatiosStatement
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_matrix_chart_ratios : ∀ (Ω : Type) [Field Ω] (E : Type) [AddCommGroup E] [Module Ω E] (S : Type) [Fintype S] (r n : S → ℕ) (κ : Type) (x : κ → Ω) (φ : ∀ s, Fin (n s) → Module.Dual Ω E) (c : ∀ s, Fin (r s) → E) (c₀ : κ), x c₀ ≠ 0 → (∀ a : Ω, ∃ g ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c₀), ∃ h ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c₀), h ≠ 0 ∧ a = g / h) → (∀ s, ∃ B : Matrix (Fin (r s)) (Fin (n s)) Ω, B * Matrix.of (fun j l => φ s j (c s l)) = 1) → ∃ J₀ : FlagIx κ n r, flagCoord κ x φ c J₀ ≠ 0 ∧ ∀ a : GenField Ω r, ∃ g ∈ Algebra.adjoin ℤ (Set.range fun j => flagCoord κ x φ c j / flagCoord κ x φ c J₀), ∃ h ∈ Algebra.adjoin ℤ (Set.range fun j => flagCoord κ x φ c j / flagCoord κ x φ c J₀), h ≠ 0 ∧ a = g / h := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen.flagCoord_generate | exact GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen.flagCoord_generate | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen.flagCoord_generate <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameNearGenericPointStatement
section
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_near_generic_point : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (T : Set (Cpt ξ)) (r : ℕ) (V : Submodule Ω E) (b : Fin r → E), IsCptGen ξ → (⟨genPt ξ, specializes_rfl⟩ : Cpt ξ) ∈ T → L.IsVBOn T r V → LinearIndependent Ω b → Submodule.span Ω (Set.range b) = V → ∃ W : X.Opens, genPt ξ ∈ W ∧ ∀ q ∈ T, q.1 ∈ W → L.IsFrameAt b q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.FrameOpen.isFrameAt_near_genPt | exact GlobalTheory.CompanionTheory.Ar.Flat.FrameOpen.isFrameAt_near_genPt | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.FrameOpen.isFrameAt_near_genPt <;> assumption)
end

