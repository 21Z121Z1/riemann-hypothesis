import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0114
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0139
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0142
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0032
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SelGLengthConj
section
noncomputable section

namespace GlobalTheory.SelConj

open Formalism.BasicNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations ReciprocityTheory.Gal TensorProduct

section Hf

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [Module O V] [IsScalarTower O LL V]
    {ρ ρ' : Representation LL G V} [TopologicalSpace G]
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]

theorem blochKatoCocycle_map_equivariant (f : V →ₗ[LL] V) (hf : Continuous f) (he : ∀ g x, f (ρ g x) = ρ' g (f x))
    (c : G → V) (hc : c ∈ finiteCocycles PD ρ) : (fun g => f (c g)) ∈ finiteCocycles PD ρ' := by
  obtain ⟨⟨h1, h2⟩, x, hx⟩ := hc
  refine ⟨⟨hf.comp h1, fun g h => ?_⟩,
    AlgebraTensorModule.map f (LinearMap.id : B →ₗ[Qp] B) x, fun g => ?_⟩
  · simp only [h2, map_add, he]
  · have e := congrArg (AlgebraTensorModule.map f (LinearMap.id : B →ₗ[Qp] B)) (hx g)
    rw [map_sub, AlgebraTensorModule.map_tmul, LinearMap.id_apply] at e
    rw [e]
    congr 1
    clear e hx
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [actVB, he]
    | add a b ha hb => simp only [map_add, ha, hb]

theorem hfD_map (L : Lattice (O := O) ρ) (L' : Lattice (O := O) ρ') (f : V →ₗ[LL] V)
    (hf : Continuous f) (he : ∀ g x, f (ρ g x) = ρ' g (f x))
    (q : (V ⧸ L.T) → (V ⧸ L'.T)) (hadd : ∀ a b, q (a + b) = q a + q b)
    (hq : ∀ x, q (Submodule.Quotient.mk x) = Submodule.Quotient.mk (f x))
    (c : G → V ⧸ L.T) (hc : c ∈ HfD PD L) : (fun g => q (c g)) ∈ HfD PD L' := by
  obtain ⟨a, ⟨z, hz, rfl⟩, b, ⟨m, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hc
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  refine Submodule.mem_sup.2 ⟨_, ⟨fun g => f (z g), blochKatoCocycle_map_equivariant PD f hf he z hz, rfl⟩, _,
    ⟨Submodule.Quotient.mk (f m), rfl⟩, ?_⟩
  funext g
  show Submodule.Quotient.mk (f (z g)) + Submodule.Quotient.mk (ρ' g (f m) - f m) =
    q (Submodule.Quotient.mk (z g) + Submodule.Quotient.mk (ρ g m - m))
  rw [hadd, hq, hq, map_sub, he]

end Hf

section Std

variable {O LL : Type} [CommRing O] [Field LL] [Algebra O LL] {k : ℕ}

def qMat (LL : Type) [Field LL] [Algebra O LL] (U : Matrix (Fin k) (Fin k) O) :
    ((Fin k → LL) ⧸ stdG O LL k) →ₗ[O] ((Fin k → LL) ⧸ stdG O LL k) :=
  Submodule.mapQ _ _ ((U.map (algebraMap O LL)).mulVecLin.restrictScalars O) (by
    rintro _ ⟨u, rfl⟩
    refine ⟨U.mulVec u, ?_⟩
    funext j
    exact RingHom.map_mulVec (algebraMap O LL) U u j)

theorem qMat_mk (U : Matrix (Fin k) (Fin k) O) (x : Fin k → LL) :
    qMat LL U (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ((U.map (algebraMap O LL)).mulVec x) := rfl

theorem qMat_mul (U U' : Matrix (Fin k) (Fin k) O) (x : (Fin k → LL) ⧸ stdG O LL k) :
    qMat LL U (qMat LL U' x) = qMat LL (U * U') x := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [qMat_mk, qMat_mk, qMat_mk, Matrix.mulVec_mulVec, Matrix.map_mul]

theorem qMat_one (x : (Fin k → LL) ⧸ stdG O LL k) : qMat LL 1 x = x := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [qMat_mk, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]

end Std

section W

variable {O : Type} [CommRing O] [IsDomain O] {Γ : Type} [Group Γ] {k : ℕ}

theorem wkg_apply (M : Γ →* Matrix (Fin k) (Fin k) O) (g : Γ) (x : KOG O k) :
    WKG M g x = qMat (FractionRing O) (M g) x := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

theorem qMat_equiv (M M' : Γ →* Matrix (Fin k) (Fin k) O) (U : Matrix (Fin k) (Fin k) O)
    (h : ∀ g, M' g * U = U * M g) (g : Γ) (x : KOG O k) :
    qMat (FractionRing O) U (WKG M g x) = WKG M' g (qMat (FractionRing O) U x) := by
  rw [wkg_apply, wkg_apply, qMat_mul, qMat_mul, h]

end W

section Coh

variable {R : Type} [CommRing R] {G : Type} [Group G] [TopologicalSpace G]
  {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M]

theorem res_map (rho rho' : Representation R G M) (u : M →ₗ[R] M) (hu : Continuous u)
    (he : ∀ g m, u (rho g m) = rho' g (u m)) {H : Type} [Group H] [TopologicalSpace H]
    (phi : H →* G) (hphi : Continuous phi) (x : H1 rho) :
    resH1 rho' phi hphi (mapH1 rho rho' u hu he x) =
      mapH1 (rho.comp phi) (rho'.comp phi) u hu (fun g m => he (phi g) m)
        (resH1 rho phi hphi x) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

theorem ur_map (rho rho' : Representation R G M) (u : M →ₗ[R] M) (hu : Continuous u)
    (he : ∀ g m, u (rho g m) = rho' g (u m)) (J : Subgroup G) (x : H1 rho)
    (hx : x ∈ H1ur rho J) : mapH1 rho rho' u hu he x ∈ H1ur rho' J := by
  have hx' : resH1 rho J.subtype continuous_subtype_val x = 0 := hx
  exact (res_map rho rho' u hu he J.subtype continuous_subtype_val x).trans
    ((congrArg _ hx').trans (map_zero _))

theorem map_left_inv (rho rho' : Representation R G M) (u u' : M →ₗ[R] M) (hu : Continuous u)
    (hu' : Continuous u') (he : ∀ g m, u (rho g m) = rho' g (u m))
    (he' : ∀ g m, u' (rho' g m) = rho g (u' m)) (hi : ∀ m, u' (u m) = m) (x : H1 rho) :
    mapH1 rho' rho u' hu' he' (mapH1 rho rho' u hu he x) = x := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  show Submodule.Quotient.mk _ = Submodule.Quotient.mk _
  congr 1
  exact Subtype.ext (funext fun g => hi _)

end Coh

section Bridge

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω Gw O) [IsDomain O]

set_option synthInstance.maxHeartbeats 400000 in
theorem phi_qMat {k : ℕ} (U : Matrix (Fin k) (Fin k) O) (x : KOG O k) :
    Br.phi Bw k (qMat (FractionRing O) U x) =
      qMat (Br.LLw Bw) (U.map Bw.eO.toRingHom) (Br.phi Bw k x) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  show Submodule.Quotient.mk (Br.vecS Bw k ((U.map (algebraMap O (FractionRing O))).mulVec x)) =
    Submodule.Quotient.mk (((U.map Bw.eO.toRingHom).map
      (algebraMap (Br.Ow Bw) (Br.LLw Bw))).mulVec (Br.vecS Bw k x))
  congr 1
  funext j
  show Br.toLLK Bw (((U.map (algebraMap O (FractionRing O))).mulVec x) j) = _
  rw [RingHom.map_mulVec]
  congr 1
  exact Matrix.ext fun a b => Br.toLLK_alg Bw (U a b)

set_option synthInstance.maxHeartbeats 400000 in
theorem bk_map (P : LocPrime l) {k : ℕ} (rho rho' : Representation O ↥Gw (KOG O k))
    (M M' : ↥Gw →* Matrix (Fin k) (Fin k) O) (U : Matrix (Fin k) (Fin k) O)
    (h : ∀ g, M' g * U = U * M g) (hu : Continuous (qMat (FractionRing O) U))
    (he : ∀ g m, qMat (FractionRing O) U (rho g m) = rho' g (qMat (FractionRing O) U m))
    (x : H1 rho) (hx : x ∈ Br.bkG Bw P rho M) :
    mapH1 rho rho' (qMat (FractionRing O) U) hu he x ∈ Br.bkG Bw P rho' M' := by
  obtain ⟨c, hc, rfl⟩ := hx
  refine ⟨cocycles1MapOfEquivariant rho rho' (qMat (FractionRing O) U) hu he c, ?_, rfl⟩
  have key := hfD_map (P.PD Bw.Kw) (Br.lat Bw M) (Br.lat Bw M')
    (((U.map Bw.eO.toRingHom).map (algebraMap (Br.Ow Bw) (Br.LLw Bw))).mulVecLin)
    (continuous_const.matrix_mulVec continuous_id) ?_
    (qMat (Br.LLw Bw) (U.map Bw.eO.toRingHom)) (map_add _) (fun _ => rfl) _ hc
  · have e : Br.Phi Bw rho' (cocycles1MapOfEquivariant rho rho' (qMat (FractionRing O) U) hu he c) =
        fun g => qMat (Br.LLw Bw) (U.map Bw.eO.toRingHom) (Br.Phi Bw rho c g) := by
      funext g
      exact phi_qMat Bw U _
    show Br.Phi Bw rho' (cocycles1MapOfEquivariant rho rho' (qMat (FractionRing O) U) hu he c) ∈
      HfD (P.PD Bw.Kw) (Br.lat Bw M')
    rw [e]
    exact key
  · intro g v
    show Matrix.mulVec ((U.map Bw.eO.toRingHom).map (algebraMap (Br.Ow Bw) (Br.LLw Bw)))
        (Matrix.mulVec (((M (Br.ι Bw g)).map Bw.eO.toRingHom).map
          (algebraMap (Br.Ow Bw) (Br.LLw Bw))) v) =
      Matrix.mulVec (((M' (Br.ι Bw g)).map Bw.eO.toRingHom).map
          (algebraMap (Br.Ow Bw) (Br.LLw Bw)))
        (Matrix.mulVec ((U.map Bw.eO.toRingHom).map (algebraMap (Br.Ow Bw) (Br.LLw Bw))) v)
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.map_mul, ← Matrix.map_mul,
      ← Matrix.map_mul, ← Matrix.map_mul, h]

end Bridge

section Sel

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (A : Formalism.GaloisCohomology.Places E Ω)
  (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (P : LocPrime l)
  (nb : ∀ w, w ∈ placesOver E l → LocBridge l E Ω (Dec (F := E) (A.1 w)) O)
  (Sig : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E))) {k : ℕ}

theorem sel_map (M M' : Formalism.ConjugateSelfDual.G E Ω →* Matrix (Fin k) (Fin k) O) (U : Matrix (Fin k) (Fin k) O)
    (h : ∀ g, M' g * U = U * M g) (x : H1 (WKG M)) (hx : x ∈ Br.selG A l P nb Sig M) :
    mapH1 (WKG M) (WKG M') (qMat (FractionRing O) U) continuous_of_discreteTopology
      (qMat_equiv M M' U h) x ∈ Br.selG A l P nb Sig M' := by
  refine (mem_Sel _ _ _ _ _).2 fun v => ?_
  have hv := (mem_Sel _ _ _ _ _).1 hx v
  refine (res_map (WKG M) (WKG M') (qMat (FractionRing O) U) continuous_of_discreteTopology
    (qMat_equiv M M' U h) (Dec (F := E) (A.1 v)).subtype continuous_subtype_val x).symm ▸ ?_
  unfold Formalism.GaloisCohomology.bkCond at hv ⊢
  split_ifs at hv ⊢ with h1 h2
  · unfold Br.LlG at hv ⊢
    split_ifs at hv ⊢ with h3
    · exact bk_map (nb v h3) P _ _ _ _ U (fun g => h g) _ _ _ hv
    · trivial
  · trivial
  · exact ur_map _ _ _ _ _ _ _ hv

theorem sel_le (M M' : Formalism.ConjugateSelfDual.G E Ω →* Matrix (Fin k) (Fin k) O)
    (U U' : Matrix (Fin k) (Fin k) O) (hi : U' * U = 1)
    (h : ∀ g, M' g * U = U * M g) (h' : ∀ g, M g * U' = U' * M' g) :
    Module.length O (Br.selG A l P nb Sig M) ≤ Module.length O (Br.selG A l P nb Sig M') := by
  refine Module.length_le_of_injective
    ((mapH1 (WKG M) (WKG M') (qMat (FractionRing O) U) continuous_of_discreteTopology
      (qMat_equiv M M' U h)).restrict (sel_map A l P nb Sig M M' U h)) ?_
  intro x y hxy
  apply Subtype.ext
  have e := congrArg (fun z => mapH1 (WKG M') (WKG M) (qMat (FractionRing O) U')
    continuous_of_discreteTopology (qMat_equiv M' M U' h') (Subtype.val z)) hxy
  have hi' : ∀ m, qMat (FractionRing O) U' (qMat (FractionRing O) U m) = m := fun m => by
    rw [qMat_mul, hi, qMat_one]
  simpa only [LinearMap.restrict_apply, map_left_inv _ _ _ _ _ _ _ _ hi'] using e

end Sel

theorem selG_length_conj : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (A : Formalism.GaloisCohomology.Places E Ω) (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [Algebra ℤ_[l] O] [TopologicalSpace O] (P : LocPrime l) (nb : ∀ w, w ∈ Formalism.BasicNotions.placesOver E l → LocBridge l E Ω (ReciprocityTheory.Gal.Dec (F := E) (A.1 w)) O) (Sig : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E))) (k : ℕ) (M M' : Formalism.ConjugateSelfDual.G E Ω →* Matrix (Fin k) (Fin k) O) (U : GL (Fin k) O), (∀ g, M' g * (U : Matrix (Fin k) (Fin k) O) = (U : Matrix (Fin k) (Fin k) O) * M g) → Module.length O (Formalism.MainNotions.N.Br.selG A l P nb Sig M) = Module.length O (Formalism.MainNotions.N.Br.selG A l P nb Sig M') := by
  intro E Ω _ _ _ _ A l _ O _ _ _ _ P nb Sig k M M' U h
  have h' : ∀ g, M g * ((U⁻¹ : GL (Fin k) O) : Matrix (Fin k) (Fin k) O) =
      ((U⁻¹ : GL (Fin k) O) : Matrix (Fin k) (Fin k) O) * M' g := fun g => by
    rw [Units.mul_inv_eq_iff_eq_mul, mul_assoc, h, ← mul_assoc, Units.inv_mul, one_mul]
  exact le_antisymm (sel_le A l P nb Sig M M' _ _ (Units.inv_mul U) h h')
    (sel_le A l P nb Sig M' M _ _ (Units.mul_inv U) h' h)

end GlobalTheory.SelConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SubOneMulSumEq
section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.TateInv

theorem sub_one_mul_sum {R : Type*} [CommRing R] (ω : R) (n : ℕ) :
    (ω - 1) * ∑ s ∈ Finset.range n, (s : R) * ω ^ s = n * ω ^ n - ω * ∑ s ∈ Finset.range n, ω ^ s := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, mul_add, ih]
    push_cast
    ring

theorem sub_one_mul_sum_eq {Ω : Type*} [Field Ω] (ω : Ω) (p : ℕ) (h1 : ω ≠ 1) (hp : ω ^ p = 1) :
    (ω - 1) * ∑ s ∈ Finset.range p, (s : Ω) * ω ^ s = p := by
  rw [sub_one_mul_sum, hp, geom_sum_eq h1, hp, sub_self, zero_div, mul_zero, sub_zero, mul_one]

theorem pow_apply_pow {Ω : Type} [Field Ω] [Algebra ℚ Ω] (γ : Ω ≃ₐ[ℚ] Ω) (ζ : Ω) (a : ℕ) (hγ : γ ζ = ζ ^ a)
    (t i : ℕ) : (γ ^ t) (ζ ^ i) = ζ ^ (i * a ^ t) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ', AlgEquiv.mul_apply, ih, map_pow, hγ, ← pow_mul, pow_succ]
    congr 1; ring

theorem pow_apply_mem {Ω : Type} [Field Ω] [Algebra ℚ Ω] (γ : Ω ≃ₐ[ℚ] Ω) (ζ : Ω) (a : ℕ) (hγ : γ ζ = ζ ^ a)
    (t : ℕ) {x : Ω} (hx : x ∈ Subring.closure {ζ}) : (γ ^ t) x ∈ Subring.closure {ζ} := by
  have h : Subring.closure {ζ} ≤ (Subring.closure {ζ}).comap ((γ ^ t : Ω ≃ₐ[ℚ] Ω) : Ω →+* Ω) := by
    rw [Subring.closure_le]
    intro y hy
    rw [Set.mem_singleton_iff.1 hy, SetLike.mem_coe, Subring.mem_comap]
    have := pow_apply_pow γ ζ a hγ t 1
    simp only [pow_one, one_mul] at this
    show (γ ^ t) ζ ∈ _
    rw [this]
    exact Subring.pow_mem _ (Subring.subset_closure (Set.mem_singleton _)) _
  exact h hx

theorem mono {Ω : Type} [Field Ω] [Algebra ℚ Ω] (p : ℕ) [hpf : Fact p.Prime] (hp2 : p ≠ 2) (L m : ℕ) (hm1 : 1 ≤ m)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ (p ^ L)) (γ : Ω ≃ₐ[ℚ] Ω) (hγ : γ ζ = ζ ^ (1 + p ^ m)) (i : ℕ)
    (hi : ¬ p ^ (L - m) ∣ i) :
    ∃ H ∈ Subring.closure {ζ}, (p : Ω) * ζ ^ i = γ H - H := by
  have hp : p.Prime := hpf.out
  obtain ⟨hmL, K, d, u, hd, hu, he, -⟩ := GlobalTheory.K5.MonX.exists_pow_eq hp2 hm1 hi
  have hpL : p ^ L = p ^ (L - 1) * p := by rw [← pow_succ, Nat.sub_add_cancel (by omega)]
  have hpm : p ^ m = p ^ (m - 1) * p := by rw [← pow_succ, Nat.sub_add_cancel (by omega)]
  set ω := ζ ^ (u * d * p ^ (L - 1)) with hω
  have hω1 : ω ≠ 1 := by
    rw [hω, Ne, hζ.pow_eq_one_iff_dvd, hpL]
    intro h
    have h' : p ^ (L - 1) * p ∣ p ^ (L - 1) * (u * d) := by rwa [mul_comm (p ^ (L - 1)) (u * d)]
    have := Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.pos _) h'
    rcases (Nat.Prime.dvd_mul hp).1 this with h | h
    · exact hu h
    · exact hd h
  have hωp : ω ^ p = 1 := by
    rw [hω, ← pow_mul, hζ.pow_eq_one_iff_dvd]
    exact ⟨u * d, by rw [hpL]; ring⟩
  have hγω : γ ω = ω := by
    rw [hω, map_pow, hγ, ← pow_mul]
    have e : (1 + p ^ m) * (u * d * p ^ (L - 1)) = u * d * p ^ (L - 1) + p ^ L * (u * d * p ^ (m - 1)) := by
      rw [hpL, hpm]; ring
    rw [e, pow_add, pow_mul ζ (p ^ L), hζ.pow_eq_one, one_pow, mul_one]
  have hγtω : ∀ t : ℕ, (γ ^ t) ω = ω := by
    intro t
    induction t with
    | zero => simp
    | succ t ih => rw [pow_succ', AlgEquiv.mul_apply, ih, hγω]
  set S : Ω := ∑ s ∈ Finset.range p, (s : Ω) * ω ^ s with hS
  have hγtS : ∀ t : ℕ, (γ ^ t) S = S := by
    intro t
    rw [hS, map_sum]
    exact Finset.sum_congr rfl fun s _ => by rw [map_mul, map_natCast, map_pow, hγtω]
  have hK : (γ ^ K) (ζ ^ i) = ω * ζ ^ i := by
    rw [pow_apply_pow γ ζ _ hγ, he, pow_add, hω, mul_comm]
  have hωmem : ω ∈ Subring.closure {ζ} := Subring.pow_mem _ (Subring.subset_closure (Set.mem_singleton _)) _
  have hSmem : S ∈ Subring.closure {ζ} :=
    Subring.sum_mem _ fun s _ => Subring.mul_mem _ (natCast_mem _ s) (Subring.pow_mem _ hωmem _)
  have hH0 : S * ζ ^ i ∈ Subring.closure {ζ} :=
    Subring.mul_mem _ hSmem (Subring.pow_mem _ (Subring.subset_closure (Set.mem_singleton _)) _)
  refine ⟨∑ t ∈ Finset.range K, (γ ^ t) (S * ζ ^ i),
    Subring.sum_mem _ fun t _ => pow_apply_mem γ ζ _ hγ t hH0, ?_⟩
  have hγH : γ (∑ t ∈ Finset.range K, (γ ^ t) (S * ζ ^ i)) = ∑ t ∈ Finset.range K, (γ ^ (t + 1)) (S * ζ ^ i) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun t _ => by rw [pow_succ', AlgEquiv.mul_apply]
  rw [hγH, ← Finset.sum_sub_distrib, Finset.sum_range_sub (fun t => (γ ^ t) (S * ζ ^ i)), pow_zero,
    AlgEquiv.one_apply, map_mul, hγtS, hK]
  have := sub_one_mul_sum_eq ω p hω1 hωp
  rw [← hS] at this
  linear_combination (-(ζ ^ i)) * this

open Classical in

theorem trace_mono {Ω : Type} [Field Ω] [Algebra ℚ Ω] (p : ℕ) [hpf : Fact p.Prime] (L m : ℕ) (hm1 : 1 ≤ m) (hm : m ≤ L)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ (p ^ L)) (τ : (ZMod (p ^ L))ˣ → (Ω ≃ₐ[ℚ] Ω))
    (hτ : ∀ a, τ a ζ = ζ ^ (a : ZMod (p ^ L)).val) (i : ℕ) :
      ∑ a ∈ Finset.univ.filter (fun a : (ZMod (p ^ L))ˣ => (a : ZMod (p ^ L)).val ≡ 1 [MOD p ^ m]), τ a (ζ ^ i)
        = (p : Ω) ^ (L - m) * (if p ^ (L - m) ∣ i then ζ ^ i else 0) := by
  have hp : p.Prime := hpf.out
  have hN : p ^ L = p ^ m * p ^ (L - m) := by rw [← pow_add, Nat.add_sub_cancel' hm]
  have hs : ∀ a : (ZMod (p ^ L))ˣ, τ a (ζ ^ i) = ζ ^ ((a : ZMod (p ^ L)).val * i) := by
    intro a; rw [map_pow, hτ, ← pow_mul]
  have hr := GlobalTheory.NTr.sum_reindex p L m hm1 hm (fun v => ζ ^ (v * i))
  rw [Finset.sum_congr rfl (fun a _ => hs a), hr]
  have hw : IsPrimitiveRoot (ζ ^ p ^ m) (p ^ (L - m)) := hζ.pow (pow_pos hp.pos _) hN
  have hterm : ∀ k, ζ ^ ((1 + p ^ m * k) * i) = ζ ^ i * ((ζ ^ p ^ m) ^ i) ^ k := by
    intro k; rw [← pow_mul, ← pow_mul, ← pow_add]; congr 1; ring
  simp only [hterm, ← Finset.mul_sum]
  split_ifs with hd
  · have h1 : (ζ ^ p ^ m) ^ i = 1 := by
      obtain ⟨j, hj⟩ := hd
      rw [hj, pow_mul, hw.pow_eq_one, one_pow]
    rw [h1]
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, Nat.cast_pow]
    ring
  · have h1 : (ζ ^ p ^ m) ^ i ≠ 1 := fun h => hd ((hw.pow_eq_one_iff_dvd i).mp h)
    rw [geom_sum_eq h1, ← pow_mul, mul_comm i, pow_mul, hw.pow_eq_one, one_pow, sub_self, zero_div, mul_zero, mul_zero]

open Classical in

theorem key_mono {Ω : Type} [Field Ω] [Algebra ℚ Ω] (p : ℕ) [hpf : Fact p.Prime] (hp2 : p ≠ 2) (L m : ℕ) (hm1 : 1 ≤ m)
    (hm : m ≤ L) (ζ : Ω) (hζ : IsPrimitiveRoot ζ (p ^ L)) (γ : Ω ≃ₐ[ℚ] Ω) (hγ : γ ζ = ζ ^ (1 + p ^ m))
    (τ : (ZMod (p ^ L))ˣ → (Ω ≃ₐ[ℚ] Ω)) (hτ : ∀ a, τ a ζ = ζ ^ (a : ZMod (p ^ L)).val) (i : ℕ) :
    ∃ H ∈ Subring.closure {ζ}, ∃ z : Ω, (p : Ω) * (ζ ^ i - z) = γ H - H ∧
      ∑ a ∈ Finset.univ.filter (fun a : (ZMod (p ^ L))ˣ => (a : ZMod (p ^ L)).val ≡ 1 [MOD p ^ m]), τ a (ζ ^ i)
        = (p : Ω) ^ (L - m) * z := by
  rw [trace_mono p L m hm1 hm ζ hζ τ hτ i]
  split_ifs with hd
  · exact ⟨0, Subring.zero_mem _, ζ ^ i, by simp, rfl⟩
  · obtain ⟨H, hH, e⟩ := mono p hp2 L m hm1 ζ hζ γ hγ i hd
    exact ⟨H, hH, 0, by rw [sub_zero, e], rfl⟩

open Classical in

theorem key {Ω : Type} [Field Ω] [Algebra ℚ Ω] (p : ℕ) [hpf : Fact p.Prime] (hp2 : p ≠ 2) (L m : ℕ) (hm1 : 1 ≤ m)
    (hm : m ≤ L) (ζ : Ω) (hζ : IsPrimitiveRoot ζ (p ^ L)) (γ : Ω ≃ₐ[ℚ] Ω) (hγ : γ ζ = ζ ^ (1 + p ^ m))
    (τ : (ZMod (p ^ L))ˣ → (Ω ≃ₐ[ℚ] Ω)) (hτ : ∀ a, τ a ζ = ζ ^ (a : ZMod (p ^ L)).val)
    (y : Ω) (hy : y ∈ Subring.closure {ζ}) :
    ∃ H ∈ Subring.closure {ζ}, ∃ z : Ω, (p : Ω) * (y - z) = γ H - H ∧
      ∑ a ∈ Finset.univ.filter (fun a : (ZMod (p ^ L))ˣ => (a : ZMod (p ^ L)).val ≡ 1 [MOD p ^ m]), τ a y
        = (p : Ω) ^ (L - m) * z := by
  rw [Subring.mem_closure_iff, Submonoid.closure_singleton_eq] at hy
  induction hy using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact key_mono p hp2 L m hm1 hm ζ hζ γ hγ τ hτ (Multiplicative.toAdd i)
  | zero => exact ⟨0, Subring.zero_mem _, 0, by simp, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨H1, h1, z1, e1, f1⟩ := hx
    obtain ⟨H2, h2, z2, e2, f2⟩ := hy
    exact ⟨H1 + H2, Subring.add_mem _ h1 h2, z1 + z2, by rw [map_add]; linear_combination e1 + e2,
      by simp only [map_add, Finset.sum_add_distrib, f1, f2]; ring⟩
  | neg x _ hx =>
    obtain ⟨H1, h1, z1, e1, f1⟩ := hx
    exact ⟨-H1, Subring.neg_mem _ h1, -z1, by rw [map_neg]; linear_combination -e1,
      by simp only [map_neg, Finset.sum_neg_distrib, f1]; ring⟩

theorem tate_inv : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∃ c : ℕ, ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (L m : ℕ), 1 ≤ m → m ≤ L → ∀ F F' : Ω, InZl ε p L F → IsNT ε p L m F F' →
  ∀ γ : Ω ≃ₐ[ℚ] Ω, γ (zt ε p L) = zt ε p L ^ (1 + p ^ m) → ∃ H : Ω, InZl ε p L H ∧ (p : Ω) ^ c * (F - F') = γ H - H := by
  intro p hpf hp2
  refine ⟨1, ?_⟩
  intro Ω _ _ _ ε L m hm1 hmL F F' hF hNT γ hγ
  have hp : p.Prime := hpf.out
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have hζ := GlobalTheory.NTr.zt_prim ε p L hp.pos
  obtain ⟨D, hD, hDF⟩ := hF
  obtain ⟨τ, hτ, hT⟩ := hNT
  have hD0 : (D : Ω) ≠ 0 := by
    have : D ≠ 0 := by rintro rfl; exact hD (dvd_zero p)
    exact_mod_cast this
  have hpN : (p : Ω) ^ (L - m) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
  obtain ⟨H, hH, z, e1, e2⟩ := key p hp2 L m hm1 hmL (zt ε p L) hζ γ hγ τ hτ _ hDF
  have hz : z = D * F' := by
    apply mul_left_cancel₀ hpN
    rw [← e2]
    simp only [map_mul, map_natCast, ← Finset.mul_sum]
    rw [← hT]; ring
  refine ⟨H / D, ⟨D, hD, by rwa [mul_div_cancel₀ _ hD0]⟩, ?_⟩
  rw [map_div₀, map_natCast, pow_one, ← sub_div, ← e1, hz, eq_div_iff hD0]
  ring

end GlobalTheory.TateInv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerLevelAdjoinRootsIntegrallyClosedQuotientStatement
section
open GlobalTheory.K5 GlobalTheory.KumDlog
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.towerLevelAdjoinRoots_integrallyClosed_quotient : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω) (m : ℕ), 1 ≤ m → ∀ a ∈ Lev T m, ∀ b ∈ Lev T m, b ≠ 0 →
  IsInt p (a / b) → a / b ∈ Lev T m := by
  first | exact @GlobalTheory.K5.LevClosed.lev_closed | exact GlobalTheory.K5.LevClosed.lev_closed | (intros; apply GlobalTheory.K5.LevClosed.lev_closed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerParameterPowersOrthogonalGeometricInvariantStatement
section
open GlobalTheory.K5
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_coeffs_of_geometricInvariant_towerParameter_expansion : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (N : ℕ) (c : ℕ → Ω), (∀ j, ∀ g ∈ Ggeo p Ω, g (c j) = c j) →
  IsInt p (∑ j ∈ Finset.range (p ^ N), c j * T.qq N ^ j) → ∀ j < p ^ N, IsInt p (c j) := by
  first | exact @GlobalTheory.K5.Orth.orth | exact GlobalTheory.K5.Orth.orth | (intros; apply GlobalTheory.K5.Orth.orth <;> assumption)
end

