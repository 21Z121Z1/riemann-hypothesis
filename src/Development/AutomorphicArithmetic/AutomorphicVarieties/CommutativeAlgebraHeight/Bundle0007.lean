import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0005
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0004
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0002
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0003
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueFixedPointOfAdicContraction

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.AevalNat
section
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

section

variable {n : ℕ} {A G : Type} [CommRing A] [Group G]

private noncomputable def pol (D : GDet n A G) (s : Finset G) : MvPolynomial s A :=
  D.D _ (∑ a : s, MonoidAlgebra.single (a : G) (MvPolynomial.X a))

private theorem pol_homog (D : GDet n A G) (s : Finset G) : (pol D s).IsHomogeneous n := by
  have h := (d_poly D.toDet (fun a : s => (MonoidAlgebra.single (a : G) 1 : MonoidAlgebra A G))).1
  have h2 : D.toDet.poly (fun a : s => (MonoidAlgebra.single (a : G) 1 : MonoidAlgebra A G)) = pol D s := by
    change D.D _ (ofT A G _ _) = D.D _ _
    congr 1
    simp [Det.gen, map_sum, ofT_tmul]
  rwa [h2] at h

private theorem nat' (D : GDet n A G) {A' : Type} [CommRing A'] (f : A →+* A') {S S' : Type} [CommRing S]
    [Algebra A S] [CommRing S'] [Algebra A' S'] (φ : S →+* S')
    (h : ∀ a, φ (algebraMap A S a) = algebraMap A' S' (f a)) (y : MonoidAlgebra S G) :
    (D.map f).D S' (MonoidAlgebra.mapRingHom G φ y) = φ (D.D S y) :=
  letI : Algebra A S' := ((algebraMap A' S').comp f).toAlgebra
  D.nat S S' { φ with commutes' := h } y

private theorem pol_map (D : GDet n A G) {A' : Type} [CommRing A'] (f : A →+* A') (s : Finset G) :
    pol (D.map f) s = MvPolynomial.map f (pol D s) := by
  rw [pol, pol, ← nat' D f (MvPolynomial.map f) (by simp)]
  congr 1
  simp [map_sum]

private theorem sum_single {S : Type} [CommRing S] (s : Finset G) (y : MonoidAlgebra S G)
    (hy : y.coeff.support ⊆ s) : ∑ a : s, MonoidAlgebra.single (a : G) (y.coeff a) = y := by
  classical
  rw [Finset.sum_coe_sort s (fun a => MonoidAlgebra.single a (y.coeff a))]
  ext g
  simp only [MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single, Finsupp.finset_sum_apply, Finsupp.single_apply, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · exact (Finsupp.notMem_support_iff.1 fun h' => h (hy h')).symm

private theorem pol_eval (D : GDet n A G) (s : Finset G) {S : Type} [CommRing S] [Algebra A S]
    (y : MonoidAlgebra S G) (hy : y.coeff.support ⊆ s) :
    D.D S y = MvPolynomial.aeval (fun a : s => y.coeff a) (pol D s) := by
  rw [pol, ← D.nat]
  congr 1
  conv_lhs => rw [← sum_single s y hy]
  simp [map_sum]

private theorem aeval_nat {σ A' : Type} [CommRing A'] (f : A →+* A') {S S' : Type} [CommRing S]
    [Algebra A S] [CommRing S'] [Algebra A' S'] (φ : S →+* S')
    (h : ∀ a, φ (algebraMap A S a) = algebraMap A' S' (f a)) (c : σ → S) (p : MvPolynomial σ A) :
    φ (MvPolynomial.aeval c p) = MvPolynomial.aeval (fun a => φ (c a)) (MvPolynomial.map f p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [h]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp only [map_mul, hp, MvPolynomial.aeval_X, MvPolynomial.map_X]

private theorem supp_map {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S') (y : MonoidAlgebra S G) :
    (MonoidAlgebra.mapRingHom G φ y).coeff.support ⊆ y.coeff.support := by
  intro g hg
  rw [Finsupp.mem_support_iff] at hg ⊢
  intro h
  apply hg
  simp [h]

private theorem sep (I : Ideal A) [IsAdicComplete I A] {σ : Type} {p q : MvPolynomial σ A}
    (h : ∀ N : ℕ, MvPolynomial.map (Ideal.Quotient.mk (I ^ N)) p = MvPolynomial.map (Ideal.Quotient.mk (I ^ N)) q) :
    p = q := by
  ext m
  refine sub_eq_zero.1 (IsHausdorff.haus (I := I) inferInstance _ fun N => ?_)
  have := congrArg (MvPolynomial.coeff m) (h N)
  rw [MvPolynomial.coeff_map, MvPolynomial.coeff_map, Ideal.Quotient.eq] at this
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  exact this

private theorem lim0 (I : Ideal A) [IsAdicComplete I A] (c : ∀ N : ℕ, A ⧸ I ^ N)
    (h : ∀ (N M : ℕ) (h : M ≤ N), Ideal.Quotient.factor (Ideal.pow_le_pow_right h) (c N) = c M) :
    ∃ a : A, ∀ N, Ideal.Quotient.mk (I ^ N) a = c N := by
  choose f hf using fun N => Ideal.Quotient.mk_surjective (c N)
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := I) inferInstance (f := f) (fun {m k} hmk => by
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← Ideal.Quotient.eq, hf, ← h k m hmk, ← hf k,
      Ideal.Quotient.factor_mk])
  refine ⟨L, fun N => ?_⟩
  have := hL N
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← Ideal.Quotient.eq, hf] at this
  exact this.symm

private theorem lim1 (I : Ideal A) [IsAdicComplete I A] {σ : Type} [Finite σ]
    (c : ∀ N : ℕ, MvPolynomial σ (A ⧸ I ^ N)) (hc : ∀ N, (c N).IsHomogeneous n)
    (h : ∀ (N M : ℕ) (h : M ≤ N),
      MvPolynomial.map (Ideal.Quotient.factor (Ideal.pow_le_pow_right h)) (c N) = c M) :
    ∃ p : MvPolynomial σ A, ∀ N, MvPolynomial.map (Ideal.Quotient.mk (I ^ N)) p = c N := by
  classical
  choose a ha using fun m : σ →₀ ℕ => lim0 I (fun N => (c N).coeff m) fun N M hle => by
    rw [← h N M hle, MvPolynomial.coeff_map]
  refine ⟨∑ m ∈ (Finsupp.finite_of_degree_le (σ := σ) n).toFinset, MvPolynomial.monomial m (a m), fun N => ?_⟩
  ext m
  simp only [MvPolynomial.coeff_map, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, Finset.sum_ite_eq']
  split_ifs with hm
  · exact ha m N
  · rw [map_zero, (hc N).coeff_eq_zero]
    intro hd
    exact hm (by simp [hd])

private theorem lift_ex {S : Type} [CommRing S] [Algebra A S] (y : MonoidAlgebra S G) :
    ∃ y' : MonoidAlgebra (MvPolynomial S A) G, y'.coeff.support ⊆ y.coeff.support ∧
      MonoidAlgebra.mapRingHom G ((MvPolynomial.aeval id : MvPolynomial S A →ₐ[A] S) : MvPolynomial S A →+* S) y' = y := by
  classical
  refine ⟨∑ a : y.coeff.support, MonoidAlgebra.single (a : G) (MvPolynomial.X (y.coeff a)), ?_, ?_⟩
  · intro g hg
    by_contra h
    rw [Finsupp.mem_support_iff] at hg
    apply hg
    simp only [MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single, Finsupp.finset_sum_apply]
    refine Finset.sum_eq_zero fun a _ => Finsupp.single_eq_of_ne ?_
    rintro rfl
    exact h a.2
  · conv_rhs => rw [← sum_single _ y le_rfl]
    simp [map_sum]

end

theorem UpperTheory.V.CA.u_lim :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] (I : Ideal A) [IsAdicComplete I A] (Ds : ∀ N : ℕ, GDet n (A ⧸ I ^ N) G), (∀ (N M : ℕ) (h : M ≤ N), (Ds N).map (Ideal.Quotient.factor (Ideal.pow_le_pow_right h)) = Ds M) → ∃! D : GDet n A G, ∀ N, D.map (Ideal.Quotient.mk (I ^ N)) = Ds N := by
  intro n A G _ _ I _ Ds hDs
  choose P hP using fun s : Finset G => lim1 I (fun N => pol (Ds N) s) (fun N => pol_homog _ s)
    fun N M h => by rw [← pol_map, hDs N M h]
  have red : ∀ (N : ℕ) (s : Finset G) {S S' : Type} [CommRing S] [Algebra A S] [CommRing S'] [Algebra (A ⧸ I ^ N) S']
      (φ : S →+* S') (_ : ∀ a, φ (algebraMap A S a) = algebraMap _ S' (Ideal.Quotient.mk (I ^ N) a))
      (y : MonoidAlgebra S G), y.coeff.support ⊆ s →
      φ (MvPolynomial.aeval (fun a : s => y.coeff a) (P s)) = (Ds N).D S' (MonoidAlgebra.mapRingHom G φ y) := by
    intro N s S S' _ _ _ _ φ h y hy
    rw [aeval_nat _ φ h, hP, pol_eval _ s _ ((supp_map φ y).trans hy)]
    simp
  have red' : ∀ (N : ℕ) (s : Finset G) {σ : Type} (y : MonoidAlgebra (MvPolynomial σ A) G), y.coeff.support ⊆ s →
      MvPolynomial.map (Ideal.Quotient.mk (I ^ N)) (MvPolynomial.aeval (fun a : s => y.coeff a) (P s)) =
        (Ds N).D _ (MonoidAlgebra.mapRingHom G (MvPolynomial.map (Ideal.Quotient.mk (I ^ N))) y) :=
    fun N s σ y hy => red N s _ (by simp) y hy
  have nat : ∀ (s : Finset G) {S S' : Type} [CommRing S] [Algebra A S] [CommRing S'] [Algebra A S']
      (φ : S →ₐ[A] S') (y : MonoidAlgebra S G),
      MvPolynomial.aeval (fun a : s => (MonoidAlgebra.mapRingHom G (φ : S →+* S') y).coeff a) (P s) =
        φ (MvPolynomial.aeval (fun a : s => y.coeff a) (P s)) := by
    intro s S S' _ _ _ _ φ y
    rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
    simp
  have indep : ∀ (s : Finset G) {S : Type} [CommRing S] [Algebra A S] (y : MonoidAlgebra S G),
      y.coeff.support ⊆ s → MvPolynomial.aeval (fun a : y.coeff.support => y.coeff a) (P _) =
        MvPolynomial.aeval (fun a : s => y.coeff a) (P s) := by
    intro s S _ _ y hy
    obtain ⟨y', h1, h2⟩ := lift_ex (A := A) y
    have e1 := nat s (MvPolynomial.aeval id) y'
    have e2 := nat y.coeff.support (MvPolynomial.aeval id) y'
    rw [h2] at e1 e2
    rw [e1, e2]
    congr 1
    exact sep I fun N => by rw [red' N _ _ h1, red' N _ _ (h1.trans hy)]
  let E : ∀ (S : Type) [CommRing S] [Algebra A S], MonoidAlgebra S G → S :=
    fun S _ _ y => MvPolynomial.aeval (fun a : y.coeff.support => y.coeff a) (P _)
  have Enat : ∀ (S S' : Type) [CommRing S] [Algebra A S] [CommRing S'] [Algebra A S']
      (φ : S →ₐ[A] S') (y : MonoidAlgebra S G), E S' (MonoidAlgebra.mapRingHom G (φ : S →+* S') y) = φ (E S y) :=
    fun S S' _ _ _ _ φ y => (indep _ _ (supp_map _ y)).trans (nat _ φ y)
  have Ered : ∀ (N : ℕ) {σ : Type} (y : MonoidAlgebra (MvPolynomial σ A) G),
      MvPolynomial.map (Ideal.Quotient.mk (I ^ N)) (E _ y) =
        (Ds N).D _ (MonoidAlgebra.mapRingHom G (MvPolynomial.map (Ideal.Quotient.mk (I ^ N))) y) :=
    fun N σ y => red' N _ y le_rfl
  have Eone : ∀ (S : Type) [CommRing S] [Algebra A S], E S 1 = 1 := by
    intro S _ _
    have h1 : E (MvPolynomial S A) 1 = 1 := sep I fun N => by simp only [Ered, map_one]
    have := Enat _ S (MvPolynomial.aeval id) 1
    rwa [h1, map_one, map_one] at this
  have Emul : ∀ (S : Type) [CommRing S] [Algebra A S] (x y), E S (x * y) = E S x * E S y := by
    intro S _ _ x y
    obtain ⟨x', -, rfl⟩ := lift_ex (A := A) x
    obtain ⟨y', -, rfl⟩ := lift_ex (A := A) y
    rw [← map_mul, Enat, Enat, Enat, ← map_mul]
    congr 1
    exact sep I fun N => by simp only [Ered, map_mul]
  have Ehom : ∀ (S : Type) [CommRing S] [Algebra A S] (b : S) (x), E S (b • x) = b ^ n * E S x := by
    intro S _ _ b x
    obtain ⟨x', -, rfl⟩ := lift_ex (A := A) x
    have h1 : E _ ((MvPolynomial.X b : MvPolynomial S A) • x') = MvPolynomial.X b ^ n * E _ x' :=
      sep I fun N => by
        rw [map_mul, map_pow, Ered, Ered, ← (Ds N).homog]
        congr 1
        ext1
        ext1
        simp
    have h2 := Enat _ S (MvPolynomial.aeval id) ((MvPolynomial.X b : MvPolynomial S A) • x')
    rw [h1, map_mul, map_pow, MvPolynomial.aeval_X, ← Enat] at h2
    refine Eq.trans ?_ h2
    congr 1
    ext g
    simp
  refine ⟨⟨fun S _ _ => ⟨⟨E S, Eone S⟩, Emul S⟩, Enat, Ehom⟩, fun N => ?_, ?_⟩
  · ext B _ _ y
    letI : Algebra A B := ((algebraMap (A ⧸ I ^ N) B).comp (Ideal.Quotient.mk (I ^ N))).toAlgebra
    have := red N _ (RingHom.id B) (fun _ => rfl) y le_rfl
    refine Eq.trans this ?_
    congr 1
    ext g
    simp
  · intro D hD
    ext B _ _ y
    have : pol D y.coeff.support = P _ := sep I fun N => by rw [hP, ← pol_map, hD]
    rw [pol_eval D _ y le_rfl, this]
    rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.BaseChangeResidueSurjective
section
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.CA ReciprocityTheory.CA

private theorem base_change_residue_surjective (O' R T : Type) [CommRing O'] [IsLocalRing O'] [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [CommRing T] [Algebra O' T] [Algebra R T]
    [Module.Finite R T] (φ : T →+* ResidueField O') (hφ : ∀ a, φ (algebraMap O' T a) = residue O' a)
    (hm : ∀ r ∈ maximalIdeal R, φ (algebraMap R T r) = 0)
    (hs : ∀ x : T, ∃ a : O', x - algebraMap O' T a ∈ (maximalIdeal R).map (algebraMap R T)) :
    IsCO O' T := by
  have hJ : (maximalIdeal R).map (algebraMap R T) ≤ Ideal.jacobson ⊥ := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, Ideal.jacobson, Submodule.mem_sInf]
    rintro P ⟨-, hP⟩
    have h1 : Ideal.comap (algebraMap R T) P = maximalIdeal R :=
      IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := R) P)
    rw [← Ideal.mem_comap, h1]
    exact hr
  haveI : Nontrivial T := by
    refine ⟨⟨0, 1, fun h => ?_⟩⟩
    have h2 := congrArg φ h
    rw [map_zero, map_one] at h2
    exact zero_ne_one h2
  have key : ∀ (u y : T), IsUnit u → y ∈ Ideal.jacobson (⊥ : Ideal T) → IsUnit (u + y) := by
    intro u y hu hy
    obtain ⟨v, rfl⟩ := hu
    have h3 := (Ideal.mem_jacobson_bot.mp hy) ↑v⁻¹
    have e : (v : T) + y = v * (y * ↑v⁻¹ + 1) := by
      rw [mul_add, mul_one, mul_comm y, ← mul_assoc, Units.mul_inv, one_mul, add_comm]
    rw [e]
    exact v.isUnit.mul h3
  haveI : IsLocalRing T := by
    refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_
    obtain ⟨a, ha⟩ := hs x
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self a with h | h
    · left
      have h4 := key _ _ (h.map (algebraMap O' T)) (hJ ha)
      rwa [add_sub_cancel] at h4
    · right
      have h4 := key _ _ (h.map (algebraMap O' T)) (hJ (neg_mem ha))
      convert h4 using 1
      rw [map_sub, map_one]
      ring
  have hR : IsCL R R := by
    refine ⟨inferInstance, inferInstance, ?_, ?_⟩
    · rw [Algebra.algebraMap_self]
      infer_instance
    · infer_instance
  have hT : IsCL R T := cl_fin R R T hR
  haveI : IsNoetherianRing T := hT.noeth
  refine ⟨hT.complete, ?_, ?_⟩
  · refine ⟨fun a ha => ?_⟩
    have h5 := ha.map φ
    rw [hφ] at h5
    exact (IsLocalRing.residue_ne_zero_iff_isUnit a).mp h5.ne_zero
  · intro x
    obtain ⟨a, ha⟩ := hs x
    refine ⟨a, ?_⟩
    have h6 : (maximalIdeal R).map (algebraMap R T) ≤ maximalIdeal T := by
      rw [Ideal.map_le_iff_le_comap]
      intro r hr
      rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      have h7 := hu.map φ
      rw [hm r hr] at h7
      exact not_isUnit_zero h7
    exact h6 ha

theorem UpperTheory.V.CA.cl_bc :
    ∀ (O O' R : Type) [CommRing O] [IsLocalRing O] [CommRing O'] [IsLocalRing O'] [Algebra O O'] [Module.Finite O O'] [IsLocalHom (algebraMap O O')] [CommRing R] [Algebra O R] [IsCO O R], IsCO O' (TensorProduct O O' R) := by
  intro O O' R _ _ _ _ _ _ _ _ _ _
  letI : Algebra R (TensorProduct O O' R) := Algebra.TensorProduct.rightAlgebra
  have hR : ∀ r : R, algebraMap R (TensorProduct O O' R) r = 1 ⊗ₜ r := fun r => rfl
  have hL : ∀ x : O', algebraMap O' (TensorProduct O O' R) x = x ⊗ₜ 1 := fun x => rfl
  haveI : Module.Finite R (TensorProduct O O' R) := by
    let c := Algebra.TensorProduct.comm O R O'
    let e : TensorProduct O R O' →ₗ[R] TensorProduct O O' R :=
      { toFun := c
        map_add' := map_add c
        map_smul' := fun r y => by
          rw [Algebra.smul_def, Algebra.smul_def, map_mul]
          congr 1 }
    exact Module.Finite.of_surjective e c.surjective
  haveI : IsNoetherianRing R := inferInstance
  haveI : IsAdicComplete (maximalIdeal R) R := IsCO.complete (O := O)
  let f : O' →ₐ[O] ResidueField O' := IsScalarTower.toAlgHom O O' (ResidueField O')
  let g : R →ₐ[O] ResidueField O' :=
    (IsScalarTower.toAlgHom O (ResidueField O) (ResidueField O')).comp (res O R)
  let φ : TensorProduct O O' R →+* ResidueField O' := (Algebra.TensorProduct.productMap f g).toRingHom
  refine base_change_residue_surjective O' R (TensorProduct O O' R) φ ?_ ?_ ?_
  · intro a
    simp [φ, f, g]
  · intro r hr
    have h1 : res O R r = 0 := (res_eq_zero_iff O R r).mpr hr
    show Algebra.TensorProduct.productMap f g (algebraMap R (TensorProduct O O' R) r) = 0
    rw [hR, Algebra.TensorProduct.productMap_apply_tmul]
    simp [g, h1]
  · intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul o r =>
      obtain ⟨c, hc⟩ := IsCO.res_surj (O := O) r
      refine ⟨algebraMap O O' c * o, ?_⟩
      have e2 : o ⊗ₜ[O] r - algebraMap O' (TensorProduct O O' R) (algebraMap O O' c * o) =
          algebraMap O' (TensorProduct O O' R) o * algebraMap R (TensorProduct O O' R) (r - algebraMap O R c) := by
        rw [hR, hL, hL, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, TensorProduct.tmul_sub,
          ← Algebra.smul_def, TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]
      rw [e2]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hc)
    | add x y hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      refine ⟨a + b, ?_⟩
      have e3 : x + y - algebraMap O' (TensorProduct O O' R) (a + b) =
          (x - algebraMap O' (TensorProduct O O' R) a) + (y - algebraMap O' (TensorProduct O O' R) b) := by
        rw [map_add]
        ring
      rw [e3]
      exact add_mem ha hb
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.ClMvps
section
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.CA ReciprocityTheory.CA

private theorem cl_mvps_fin {A S : Type} [CommRing A] [CommRing S] [Algebra A S]
    [IsNoetherianRing S] {I J : Ideal S} (h : Module.Finite A (S ⧸ I)) {N : ℕ}
    (hN : I ^ N ≤ J) : Module.Finite A (S ⧸ J) := by
  classical
  have toP : ∀ K : Ideal S, Module.Finite A (S ⧸ K) →
      ∃ F : Finset S, ∀ s : S, ∃ t ∈ Submodule.span A (F : Set S), s - t ∈ K := by
    intro K hK
    obtain ⟨T, hT⟩ := hK.fg_top
    choose l hl using fun q : S ⧸ K => Ideal.Quotient.mk_surjective q
    refine ⟨T.image l, fun s => ?_⟩
    have himg : (Ideal.Quotient.mkₐ A K).toLinearMap '' ((T.image l : Finset S) : Set S) = (T : Set (S ⧸ K)) := by
      ext q
      simp [hl]
    have hs : Ideal.Quotient.mk K s ∈ Submodule.map (Ideal.Quotient.mkₐ A K).toLinearMap
        (Submodule.span A ((T.image l : Finset S) : Set S)) := by
      rw [Submodule.map_span, himg, hT]
      exact Submodule.mem_top
    obtain ⟨t, ht, hts⟩ := hs
    refine ⟨t, ht, ?_⟩
    rw [← Ideal.Quotient.eq]
    simpa using hts.symm
  have ofP : ∀ K : Ideal S, (∃ F : Finset S, ∀ s : S, ∃ t ∈ Submodule.span A (F : Set S), s - t ∈ K) →
      Module.Finite A (S ⧸ K) := by
    rintro K ⟨F, hF⟩
    refine ⟨⟨F.image (Ideal.Quotient.mk K), ?_⟩⟩
    rw [eq_top_iff]
    rintro q -
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨t, ht, hst⟩ := hF s
    have h1 : Ideal.Quotient.mk K s = (Ideal.Quotient.mkₐ A K).toLinearMap t := by
      simpa [Ideal.Quotient.eq] using hst
    have h2 := Submodule.mem_map_of_mem (f := (Ideal.Quotient.mkₐ A K).toLinearMap) ht
    have himg : (Ideal.Quotient.mkₐ A K).toLinearMap '' (F : Set S) = ((F.image (Ideal.Quotient.mk K) : Finset (S ⧸ K)) : Set (S ⧸ K)) := by
      ext q
      simp
    rw [Submodule.map_span, himg] at h2
    rw [h1]
    exact h2
  obtain ⟨F1, hF1⟩ := toP I h
  have hpow : ∀ n : ℕ, ∃ F : Finset S, ∀ s : S, ∃ t ∈ Submodule.span A (F : Set S), s - t ∈ I ^ n := by
    intro n
    induction n with
    | zero => exact ⟨∅, fun s => ⟨0, Submodule.zero_mem _, by simp⟩⟩
    | succ n ih =>
      obtain ⟨Fn, hFn⟩ := ih
      obtain ⟨G, hG⟩ := (IsNoetherian.noetherian (I ^ n) : (I ^ n).FG)
      refine ⟨Fn ∪ (F1 ×ˢ G).image (fun p => p.1 * p.2), fun s => ?_⟩
      obtain ⟨t, ht, hst⟩ := hFn s
      rw [← hG, Submodule.mem_span_finset] at hst
      obtain ⟨c, -, hc⟩ := hst
      choose u hu hcu using fun g => hF1 (c g)
      refine ⟨t + ∑ g ∈ G, u g * g, ?_, ?_⟩
      · refine Submodule.add_mem _ (Submodule.span_mono ?_ ht) (Submodule.sum_mem _ fun g hg => ?_)
        · exact Finset.coe_subset.mpr Finset.subset_union_left
        · have h3 := Submodule.mem_map_of_mem (f := LinearMap.mulRight A g) (hu g)
          rw [Submodule.map_span] at h3
          refine Submodule.span_mono ?_ h3
          rintro _ ⟨f, hf, rfl⟩
          rw [Finset.coe_union, Finset.coe_image]
          right
          exact ⟨(f, g), Finset.mem_product.mpr ⟨hf, hg⟩, by simp⟩
      · have hct : s - t = ∑ g ∈ G, c g * g := by
          rw [← hc]
          simp [smul_eq_mul]
        have he : s - (t + ∑ g ∈ G, u g * g) = ∑ g ∈ G, (c g - u g) * g := by
          calc s - (t + ∑ g ∈ G, u g * g) = (s - t) - ∑ g ∈ G, u g * g := by ring
            _ = ∑ g ∈ G, c g * g - ∑ g ∈ G, u g * g := by rw [hct]
            _ = ∑ g ∈ G, (c g - u g) * g := by
              rw [← Finset.sum_sub_distrib]
              simp [sub_mul]
        rw [he, pow_succ']
        refine Ideal.sum_mem _ fun g hg => Ideal.mul_mem_mul (hcu g) ?_
        rw [← hG]
        exact Submodule.subset_span hg
  obtain ⟨F, hF⟩ := hpow N
  exact ofP J ⟨F, fun s => (hF s).imp fun t ⟨ht, hst⟩ => ⟨ht, hN hst⟩⟩

private theorem cl_mvps_max {O σ : Type} [CommRing O] [IsLocalRing O] (g : MvPowerSeries σ O) :
    g ∈ maximalIdeal (MvPowerSeries σ O) ↔ MvPowerSeries.constantCoeff g ∈ maximalIdeal O := by
  simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff]

theorem UpperTheory.V.CA.cl_mvps :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (R : Type) [CommRing R] [Algebra O R] [IsLocalRing R], IsCL O R → ∀ (σ : Type) [Finite σ] (a : σ → R), (∀ s, a s ∈ maximalIdeal R) → maximalIdeal R ≤ (Ideal.span (Set.range a) ⊔ (maximalIdeal O).map (algebraMap O R)).radical → ∃ φ : MvPowerSeries σ O →ₐ[O] R, (∀ s, φ (MvPowerSeries.X s) = a s) ∧ φ.toRingHom.Finite ∧ IsLocalHom φ := by
  intro O _ _ _ _ R _ _ _ hR σ _ a ha hrad
  haveI := hR.noeth
  haveI := hR.complete
  haveI := hR.isLocalHom
  let φ : MvPowerSeries σ O →ₐ[O] R := GlobalTheory.mvEvalAdic O (maximalIdeal R) a ha
  have hX : ∀ s, φ (MvPowerSeries.X s) = a s := GlobalTheory.mvEvalAdic_X _ a ha
  have hXm : ∀ s, φ (MvPowerSeries.X s) ∈ maximalIdeal R := fun s => (hX s).symm ▸ ha s
  refine ⟨φ, hX, ?_, ?_⟩
  · letI : Algebra (MvPowerSeries σ O) R := φ.toRingHom.toAlgebra
    show Module.Finite (MvPowerSeries σ O) R
    haveI hOO : IsCO O O := ⟨inferInstance, ⟨fun x hx => by simpa using hx⟩, fun x => ⟨x, by simp⟩⟩
    haveI hCO := co_mvps O O σ
    haveI := hCO.complete
    haveI : IsScalarTower O (MvPowerSeries σ O) R :=
      IsScalarTower.of_algebraMap_eq (fun c => (φ.commutes c).symm)
    have hJ : Ideal.span (Set.range a) ⊔ (maximalIdeal O).map (algebraMap O R) ≤
        (maximalIdeal (MvPowerSeries σ O)).map (algebraMap (MvPowerSeries σ O) R) := by
      refine sup_le ?_ ?_
      · rw [Ideal.span_le]
        rintro _ ⟨s, rfl⟩
        rw [← hX s]
        refine Ideal.mem_map_of_mem (algebraMap (MvPowerSeries σ O) R) ?_
        rw [cl_mvps_max]
        simp
      · rw [Ideal.map_le_iff_le_comap]
        intro c hc
        rw [Ideal.mem_comap, ← φ.commutes c]
        refine Ideal.mem_map_of_mem (algebraMap (MvPowerSeries σ O) R) ?_
        rw [cl_mvps_max, MvPowerSeries.algebraMap_apply]
        simpa using hc
    have hJm : (maximalIdeal (MvPowerSeries σ O)).map (algebraMap (MvPowerSeries σ O) R) ≤ maximalIdeal R := by
      rw [Ideal.map_le_iff_le_comap]
      intro g hg
      rw [Ideal.mem_comap]
      rw [cl_mvps_max] at hg
      have h1 : algebraMap O R (MvPowerSeries.constantCoeff g) ∈ maximalIdeal R := by
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        exact fun hu => ((IsLocalRing.mem_maximalIdeal _).mp hg) (isUnit_of_map_unit (algebraMap O R) _ hu)
      have h2 := GlobalTheory.algHom_sub_constantCoeff_mem φ (K := maximalIdeal R) hXm g
      have h3 := Ideal.add_mem _ h2 h1
      have h4 : φ g ∈ maximalIdeal R := by simpa using h3
      exact h4
    haveI : IsHausdorff ((maximalIdeal (MvPowerSeries σ O)).map (algebraMap (MvPowerSeries σ O) R)) R :=
      IsHausdorff.of_isLocalRing _ R (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal R).ne_top hJm)
    obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg
      (hrad.trans (Ideal.radical_mono hJ)) (IsNoetherian.noetherian (maximalIdeal R))
    haveI : Module.Finite O (R ⧸ maximalIdeal R) := hR.res_fin
    haveI : Module.Finite (MvPowerSeries σ O) (R ⧸ maximalIdeal R) :=
      Module.Finite.of_restrictScalars_finite O _ _
    haveI : Module.Finite (MvPowerSeries σ O)
        (R ⧸ (maximalIdeal (MvPowerSeries σ O)).map (algebraMap (MvPowerSeries σ O) R)) :=
      cl_mvps_fin (A := MvPowerSeries σ O) inferInstance hN
    exact GlobalTheory.FormalIsogeny.finite_of_finite_quotient_map (maximalIdeal (MvPowerSeries σ O))
  · constructor
    intro g hg
    rw [MvPowerSeries.isUnit_iff_constantCoeff]
    by_contra hc
    have h1 : algebraMap O R (MvPowerSeries.constantCoeff g) ∈ maximalIdeal R := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact fun hu => hc (isUnit_of_map_unit (algebraMap O R) _ hu)
    have h2 := GlobalTheory.algHom_sub_constantCoeff_mem φ (K := maximalIdeal R) hXm g
    have h3 : φ g ∈ maximalIdeal R := by simpa using Ideal.add_mem _ h2 h1
    exact ((IsLocalRing.mem_maximalIdeal _).mp h3) hg
end

