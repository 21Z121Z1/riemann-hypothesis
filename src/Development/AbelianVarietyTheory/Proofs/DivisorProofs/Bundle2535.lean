import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2411
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsHolomorphicUniformisationPowerThetaKeyDatu
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Formalism.LocalToGlobal.ProjectiveLattices.BetaAtSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0120
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiUnitOnOfFixedOverUnramifiedExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2433
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2170

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeSpectrumDualEq
section
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal

set_option autoImplicit false
noncomputable section
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PeriodLattice

open GlobalTheory.GrpTangent

theorem primeSpectrum_dual_eq (x y : PrimeSpectrum (DualNumber ℂ)) : x = y := by
  have h : ∀ z : PrimeSpectrum (DualNumber ℂ), ∀ a, a ∈ z.asIdeal ↔ a.fst = 0 := fun z a => by
    constructor
    · intro ha
      by_contra h0
      exact z.2.ne_top (z.asIdeal.eq_top_of_isUnit_mem ha (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (Ne.isUnit h0)))
    · intro ha
      refine z.2.mem_of_pow_mem 2 ?_
      rw [show a ^ 2 = 0 by ext <;> simp [pow_two, ha]]
      exact z.asIdeal.zero_mem
  ext a
  rw [h, h]

theorem isDiff_epsScale {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) {w : Fin g → ℂ}
    {v : epsR ℂ ⟶ A} (h : u.IsDiff w v) (c : ℂ) : u.IsDiff (c • w) (epsScale c ≫ v) := by
  intro U hU f
  have hU' : ⊤ ≤ v.left ⁻¹ᵁ U := fun x _ => by
    have := hU (Set.mem_univ x)
    have hx : (spMap (epsScaleR c)) x = x := primeSpectrum_dual_eq _ _
    change v.left ((spMap (epsScaleR c)) x) ∈ U at this
    rwa [hx] at this
  rw [map_smul, ← h U hU' f]
  have e : (epsScale c ≫ v).left.appLE U ⊤ hU = v.left.appLE U ⊤ hU' ≫ (spMap (epsScaleR c)).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    exact (Scheme.Hom.appLE_comp_appLE (spMap (epsScaleR c)) v.left U ⊤ ⊤ hU' le_rfl).symm
  have e2 := congrArg (fun k => k.hom ((v.left.appLE U ⊤ hU').hom f))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (epsScaleR c)))
  rw [e]
  refine (congrArg TrivSqZeroExt.snd e2).trans ?_
  simp [epsScaleR]

section Ext

variable {E : Type} {V : Type*} [AddCommGroup E] [AddCommGroup V] [Module ℂ V] (L : AddSubgroup E)

theorem inv_smul_eq (Q : L →+ V) {x : E} {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (h : n • x ∈ L) (h' : m • x ∈ L) :
    (n : ℂ)⁻¹ • Q ⟨n • x, h⟩ = (m : ℂ)⁻¹ • Q ⟨m • x, h'⟩ := by
  have key : m • Q ⟨n • x, h⟩ = n • Q ⟨m • x, h'⟩ := by
    rw [← map_nsmul, ← map_nsmul]
    congr 1
    ext
    simp only [AddSubgroup.coe_nsmul]
    rw [smul_smul, smul_smul, mul_comm]
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have key' : (m : ℂ) • Q ⟨n • x, h⟩ = (n : ℂ) • Q ⟨m • x, h'⟩ := by
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, key]
  calc (n : ℂ)⁻¹ • Q ⟨n • x, h⟩ = ((n : ℂ)⁻¹ * (m : ℂ)⁻¹) • ((m : ℂ) • Q ⟨n • x, h⟩) := by
        rw [smul_smul]; congr 1; field_simp
    _ = ((n : ℂ)⁻¹ * (m : ℂ)⁻¹) • ((n : ℂ) • Q ⟨m • x, h'⟩) := by rw [key']
    _ = (m : ℂ)⁻¹ • Q ⟨m • x, h'⟩ := by rw [smul_smul]; congr 1; field_simp

theorem exists_ext (hfull : ∀ x : E, ∃ n : ℕ, 0 < n ∧ n • x ∈ L) (Q : L →+ V) :
    ∃ P : E →+ V, ∀ (x : E) (n : ℕ) (hn : 0 < n) (h : n • x ∈ L), P x = (n : ℂ)⁻¹ • Q ⟨n • x, h⟩ := by
  choose N hN hNL using hfull
  let P : E →+ V :=
    { toFun := fun x => (N x : ℂ)⁻¹ • Q ⟨N x • x, hNL x⟩
      map_zero' := by
        rw [show (⟨N 0 • (0 : E), hNL 0⟩ : L) = 0 from Subtype.ext (by simp), map_zero, smul_zero]
      map_add' := fun x y => by
        have hxy : (N x * N y) • (x + y) ∈ L := by
          rw [smul_add, mul_comm, mul_smul, mul_comm, mul_smul]
          exact add_mem (L.nsmul_mem (hNL x) _) (L.nsmul_mem (hNL y) _)
        have hx : (N x * N y) • x ∈ L := by rw [mul_comm, mul_smul]; exact L.nsmul_mem (hNL x) _
        have hy : (N x * N y) • y ∈ L := by rw [mul_smul]; exact L.nsmul_mem (hNL y) _
        have hpos : 0 < N x * N y := Nat.mul_pos (hN x) (hN y)
        rw [inv_smul_eq L Q (hN _) hpos _ hxy, inv_smul_eq L Q (hN _) hpos _ hx,
          inv_smul_eq L Q (hN _) hpos _ hy, ← smul_add, ← map_add]
        congr 2
        ext
        simp [smul_add] }
  exact ⟨P, fun x n hn h => inv_smul_eq L Q (hN x) hn (hNL x) h⟩

end Ext

end GlobalTheory.PeriodLattice

namespace GlobalTheory.PeriodLattice

theorem exists_nsmul_mem {E : Type} [AddCommGroup E] [Module ℚ E] [FiniteDimensional ℚ E] {g : ℕ} (L : AddSubgroup E)
    (ι : E →ₗ[ℚ] (Fin g → ℂ)) (hdim : Module.finrank ℚ E ≤ 2 * g)
    (hsp : Submodule.span ℝ (ι '' (L : Set E)) = ⊤) (x : E) : ∃ n : ℕ, 0 < n ∧ n • x ∈ L := by
  set W := Submodule.span ℚ (L : Set E)
  let b := Module.finBasis ℚ W
  have hsub : ι '' (L : Set E) ⊆ Submodule.span ℝ (Set.range fun k => ι (b k)) := by
    rintro _ ⟨y, hy, rfl⟩
    have hyW : y ∈ W := Submodule.subset_span hy
    have e : (⟨y, hyW⟩ : W) = ∑ k, b.repr ⟨y, hyW⟩ k • b k := (b.sum_repr _).symm
    have e' : y = ∑ k, b.repr ⟨y, hyW⟩ k • (b k : E) := by
      have := congrArg Subtype.val e
      rw [Submodule.coe_sum] at this
      exact this.trans (Finset.sum_congr rfl fun k _ => Submodule.coe_smul _ _)
    rw [e', map_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [map_smul, ← algebraMap_smul ℝ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  have htop : Submodule.span ℝ (Set.range fun k => ι (b k)) = ⊤ :=
    top_unique (hsp ▸ Submodule.span_le.2 hsub)
  have h1 : Module.finrank ℝ (Fin g → ℂ) ≤ Module.finrank ℚ W := by
    have := finrank_span_le_card (R := ℝ) (Set.range fun k => ι (b k))
    rw [htop, finrank_top] at this
    refine this.trans ?_
    refine (Set.toFinset_card _).le.trans ?_
    exact (Fintype.card_range_le _).trans (by simp)
  have h2 : Module.finrank ℝ (Fin g → ℂ) = 2 * g := by
    rw [Module.finrank_pi_fintype, Complex.finrank_real_complex]; simp [mul_comm]
  have hW : W = ⊤ := Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le W) (by omega))
  have hx : x ∈ W := hW ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_pos, by simpa using hy⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨n, hn, hny⟩ := hy
    obtain ⟨m, hm, hmz⟩ := hz
    refine ⟨n * m, Nat.mul_pos hn hm, ?_⟩
    rw [smul_add, mul_comm, mul_smul, mul_comm, mul_smul]
    exact add_mem (L.nsmul_mem hny _) (L.nsmul_mem hmz _)
  | smul q y _ hy =>
    obtain ⟨n, hn, hny⟩ := hy
    refine ⟨q.den * n, Nat.mul_pos q.den_pos hn, ?_⟩
    have : (q.den * n) • (q • y) = q.num • (n • y) := by
      rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, ← Nat.cast_smul_eq_nsmul ℚ n y, ← Int.cast_smul_eq_zsmul ℚ, smul_smul]
      congr 1
      push_cast
      rw [mul_comm (q.den : ℚ) n, mul_assoc, Rat.den_mul_eq_num, mul_comm]
    rw [this]
    exact L.zsmul_mem hny _

end GlobalTheory.PeriodLattice

namespace GlobalTheory.PeriodLattice

open GlobalTheory.GrpTangent

end GlobalTheory.PeriodLattice

namespace GlobalTheory.PeriodLattice

open GlobalTheory.GrpTangent

end GlobalTheory.PeriodLattice
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductAbelianUniformization
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ProdUnifSq

variable {g : ℕ}

def halfL (g : ℕ) : (Fin (g + g) → ℂ) →L[ℂ] (Fin g → ℂ) :=
  ContinuousLinearMap.pi fun k => ContinuousLinearMap.proj (Fin.castAdd g k)

def halfR (g : ℕ) : (Fin (g + g) → ℂ) →L[ℂ] (Fin g → ℂ) :=
  ContinuousLinearMap.pi fun k => ContinuousLinearMap.proj (Fin.natAdd g k)

theorem halfL_apply (v : Fin (g + g) → ℂ) : halfL g v = fun k => v (Fin.castAdd g k) := rfl
theorem halfR_apply (v : Fin (g + g) → ℂ) : halfR g v = fun k => v (Fin.natAdd g k) := rfl

theorem halfL_append (x y : Fin g → ℂ) : halfL g (Fin.append x y) = x := by
  funext k; simp [halfL_apply]
theorem halfR_append (x y : Fin g → ℂ) : halfR g (Fin.append x y) = y := by
  funext k; exact Fin.append_right x y k

theorem append_halves (v : Fin (g + g) → ℂ) : Fin.append (halfL g v) (halfR g v) = v := by
  funext q
  refine Fin.addCases (fun k => ?_) (fun k => ?_) q
  · rw [Fin.append_left, halfL_apply]
  · rw [Fin.append_right, halfR_apply]

def sqLat (Λ : Submodule ℤ (Fin g → ℂ)) : Submodule ℤ (Fin (g + g) → ℂ) :=
  Λ.comap ((halfL g).toLinearMap.restrictScalars ℤ) ⊓ Λ.comap ((halfR g).toLinearMap.restrictScalars ℤ)

theorem mem_sqLat (Λ : Submodule ℤ (Fin g → ℂ)) (v : Fin (g + g) → ℂ) :
    v ∈ sqLat Λ ↔ halfL g v ∈ Λ ∧ halfR g v ∈ Λ := Iff.rfl

theorem sqLat_discrete (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ] : DiscreteTopology (sqLat Λ) := by
  refine DiscreteTopology.of_continuous_injective (β := Λ × Λ)
    (f := fun z => (⟨halfL g z.1, z.2.1⟩, ⟨halfR g z.1, z.2.2⟩))
    (Continuous.prodMk (((halfL g).continuous.comp continuous_subtype_val).subtype_mk _)
      (((halfR g).continuous.comp continuous_subtype_val).subtype_mk _)) fun z z' h => ?_
  refine Subtype.ext ?_
  rw [← append_halves z.1, ← append_halves z'.1]
  simp only [Prod.mk.injEq] at h
  have h1 : halfL g z.1 = halfL g z'.1 := congrArg Subtype.val h.1
  have h2 : halfR g z.1 = halfR g z'.1 := congrArg Subtype.val h.2
  rw [h1, h2]

def appendL (g : ℕ) : (Fin g → ℂ) →ₗ[ℝ] (Fin (g + g) → ℂ) where
  toFun x := Fin.append x 0
  map_add' x y := by
    funext q
    refine Fin.addCases (fun k => ?_) (fun k => ?_) q <;>
      simp only [Fin.append_left, Fin.append_right, Pi.add_apply, Pi.smul_apply, Pi.zero_apply, add_zero,
        smul_zero, RingHom.id_apply]
  map_smul' c x := by
    funext q
    refine Fin.addCases (fun k => ?_) (fun k => ?_) q <;>
      simp only [Fin.append_left, Fin.append_right, Pi.add_apply, Pi.smul_apply, Pi.zero_apply, add_zero,
        smul_zero, RingHom.id_apply]

def appendR (g : ℕ) : (Fin g → ℂ) →ₗ[ℝ] (Fin (g + g) → ℂ) where
  toFun y := Fin.append 0 y
  map_add' x y := by
    funext q
    refine Fin.addCases (fun k => ?_) (fun k => ?_) q <;>
      simp only [Fin.append_left, Fin.append_right, Pi.add_apply, Pi.smul_apply, Pi.zero_apply, add_zero,
        smul_zero, RingHom.id_apply]
  map_smul' c x := by
    funext q
    refine Fin.addCases (fun k => ?_) (fun k => ?_) q <;>
      simp only [Fin.append_left, Fin.append_right, Pi.add_apply, Pi.smul_apply, Pi.zero_apply, add_zero,
        smul_zero, RingHom.id_apply]

theorem sqLat_full (Λ : Submodule ℤ (Fin g → ℂ)) (h : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤) :
    Submodule.span ℝ (sqLat Λ : Set (Fin (g + g) → ℂ)) = ⊤ := by
  have hL : Set.range (appendL g) ⊆ Submodule.span ℝ (sqLat Λ : Set (Fin (g + g) → ℂ)) := by
    have : (Submodule.span ℝ (Λ : Set (Fin g → ℂ))).map (appendL g) ≤ Submodule.span ℝ (sqLat Λ : Set _) := by
      rw [Submodule.map_span]
      refine Submodule.span_mono ?_
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨?_, ?_⟩
      · change halfL g (Fin.append x 0) ∈ Λ
        rw [halfL_append]; exact hx
      · change halfR g (Fin.append x 0) ∈ Λ
        rw [halfR_append]; exact Λ.zero_mem
    rintro _ ⟨x, rfl⟩
    exact this ⟨x, by rw [h]; trivial, rfl⟩
  have hR : Set.range (appendR g) ⊆ Submodule.span ℝ (sqLat Λ : Set (Fin (g + g) → ℂ)) := by
    have : (Submodule.span ℝ (Λ : Set (Fin g → ℂ))).map (appendR g) ≤ Submodule.span ℝ (sqLat Λ : Set _) := by
      rw [Submodule.map_span]
      refine Submodule.span_mono ?_
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨?_, ?_⟩
      · change halfL g (Fin.append 0 x) ∈ Λ
        rw [halfL_append]; exact Λ.zero_mem
      · change halfR g (Fin.append 0 x) ∈ Λ
        rw [halfR_append]; exact hx
    rintro _ ⟨x, rfl⟩
    exact this ⟨x, by rw [h]; trivial, rfl⟩
  refine eq_top_iff.2 fun v _ => ?_
  have hv : v = appendL g (halfL g v) + appendR g (halfR g v) := by
    conv_lhs => rw [← append_halves v]
    funext q
    refine Fin.addCases (fun k => ?_) (fun k => ?_) q <;>
      simp only [appendL, appendR, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply, Fin.append_left, Fin.append_right,
        Pi.zero_apply, add_zero, zero_add]
  rw [hv]
  exact Submodule.add_mem _ (hL ⟨_, rfl⟩) (hR ⟨_, rfl⟩)

variable (A : Over (Sp ℂ)) [GrpObj A]

abbrev trivLB (X : Scheme.{0}) : LB X := ⟨PUnit, fun _ => ⊤, fun _ _ => 1⟩

def sqUnif {L : LB A.left} (u : HolUnif A L g) : HolUnif (A ⊗ A) (trivLB (A ⊗ A).left) (g + g) where
  ex v := lift (u.ex (halfL g v)) (u.ex (halfR g v))
  ex_add z w := by
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
    · rw [MonObj.mul_comp, lift_fst, lift_fst, lift_fst, map_add, u.ex_add]
    · rw [MonObj.mul_comp, lift_snd, lift_snd, lift_snd, map_add, u.ex_add]
  ex_onto p := by
    obtain ⟨x, hx⟩ := u.ex_onto (p ≫ fst _ _)
    obtain ⟨y, hy⟩ := u.ex_onto (p ≫ snd _ _)
    refine ⟨Fin.append x y, ?_⟩
    show lift (u.ex (halfL g (Fin.append x y))) (u.ex (halfR g (Fin.append x y))) = p
    rw [halfL_append, halfR_append, hx, hy]
    exact (CartesianMonoidalCategory.hom_ext _ _ (lift_fst _ _) (lift_snd _ _))
  Λ := sqLat u.Λ
  ker z := by
    rw [mem_sqLat, ← u.ker, ← u.ker]
    constructor
    · intro h
      constructor
      · have := congrArg (· ≫ fst A A) h
        simpa only [lift_fst, MonObj.one_comp] using this
      · have := congrArg (· ≫ snd A A) h
        simpa only [lift_snd, MonObj.one_comp] using this
    · rintro ⟨h1, h2⟩
      refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
      · rw [lift_fst, MonObj.one_comp, h1]
      · rw [lift_snd, MonObj.one_comp, h2]
  discrete := by
    have := u.discrete
    exact sqLat_discrete u.Λ
  full := sqLat_full u.Λ u.full
  hol := by
    have hd : GlobalTheory.PowUnif.IsHolFamily (fun z => (u.ex z).left) := u.hol
    refine GlobalTheory.PowUnif.isHolFamily_tensor A A _ ?_ ?_
    · simp only [lift_fst]
      exact hd.precomp (halfL g).differentiable
    · simp only [lift_snd]
      exact hd.precomp (halfR g).differentiable
  fr _ _ := 1
  fr_hol _ := differentiableOn_const _
  fr_ne _ _ _ := one_ne_zero
  fr_compat i j z h := by
    rw [Units.val_one, valAt'_one _ h, _root_.one_mul]

theorem sqUnif_ex_append {L : LB A.left} (u : HolUnif A L g) (x y : Fin g → ℂ) :
    (sqUnif A u).ex (Fin.append x y) = lift (u.ex x) (u.ex y) := by
  change lift (u.ex (halfL g (Fin.append x y))) (u.ex (halfR g (Fin.append x y))) = _
  rw [halfL_append, halfR_append]

end GlobalTheory.ProdUnifSq

open GlobalTheory.ProdUnifSq in

theorem GlobalTheory.exists_holUnif_tensor_self : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (L : LB A.left) (g : ℕ) (u : HolUnif A L g),
    ∃ U : HolUnif (A ⊗ A) (⟨PUnit, fun _ => ⊤, fun _ _ => 1⟩ : LB (A ⊗ A).left) (g + g),
      ∀ x y : Fin g → ℂ, U.ex (Fin.append x y) = lift (u.ex x) (u.ex y) := by
  intro A _ _ _ L g u
  exact ⟨sqUnif A u, sqUnif_ex_append A u⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiScalingIntegralRescale
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.PsiTopUnit

theorem unit_factor {R : Type} [CommRing R] [IsDomain R] {Y : Scheme.{0}}
    (f : Y ⟶ Spec (CommRingCat.of (FractionRing R))) (y : Y) (c a : (FractionRing R)ˣ) (u : Rˣ)
    (h : c * a = Units.map (algebraMap R (FractionRing R)).toMonoidHom u) :
    (gm (f ≫ jK R) y ⊤ (unitOn u)).val = (gm f y ⊤ (unitOn c)).val * gs (𝟙 Y) y ⊤ (scal f a.val) := by
  let φ : FractionRing R →+* Y.presheaf.stalk y := (Y.presheaf.germ (f ⁻¹ᵁ ⊤) y trivial).hom.comp
    ((f.app ⊤).hom.comp (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom)
  have e1 : (gm f y ⊤ (unitOn c)).val = φ c.val := by rw [gm_val f y ⊤ trivial]; rfl
  have e2 : gs (𝟙 Y) y ⊤ (scal f a.val) = φ a.val := by rw [gs_eq _ y ⊤ trivial]; rfl
  have e3 : (gm (f ≫ jK R) y ⊤ (unitOn u)).val = φ (algebraMap R (FractionRing R) u.val) := by
    rw [gm_val _ y ⊤ trivial]
    have e := congrArg (fun q => q.hom u.val)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
    show _ = (Y.presheaf.germ (f ⁻¹ᵁ ⊤) y trivial).hom ((f.app ⊤).hom
      ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom (CommRingCat.ofHom (algebraMap R (FractionRing R)) u.val)))
    rw [e]
    rfl
  rw [e1, e2, e3, ← map_mul, ← Units.val_mul, h]
  rfl

theorem exists_psiOn_top_rescale : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (a : D.X → (FractionRing R)ˣ), GlobalTheory.UU.PsiScal D ga a → ∀ c : D.X → (FractionRing R)ˣ, (∀ χ : D.X, ∃ u : Rˣ, c χ * a χ = Units.map (algebraMap R (FractionRing R)).toMonoidHom u) → Nonempty (PsiOn (GlobalTheory.PolDeg.rescale D c) ⊤) := by
  intro R _ _ _ D ga a hs c hc
  choose u hu using hc
  refine ⟨⟨fun χ => LB.pullGen D.P.L _ _ (GlobalTheory.UU.scaleGen (unitOn (u χ)) (ga χ)) (⊤ : (Spec (CommRingCat.of R)).Opens).ι,
    fun χ => DVR.pullGen_isGen _ _ _ _ (GlobalTheory.UU.scaleGen_isGen _ (hs χ).1) _,
    fun χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩⟩
  refine (val_pull hJ _ _ _).trans ((val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm))
  rw [Category.id_comp, Category.id_comp, morphismRestrict_ι]
  refine (GlobalTheory.UU.val_scaleGen _ _ _ hJ).trans (Eq.trans ?_ (GlobalTheory.UU.val_scaleGen _ _ _ hJ).symm)
  have hp := (hs χ).2 (Over.mk ((jK R ⁻¹ᵁ ⊤).ι ≫ jK R)) (Over.homMk (jK R ⁻¹ᵁ ⊤).ι) y J hJ
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  erw [hp]
  rw [unit_factor _ y (c χ) (a χ) (u χ) (hu χ), _root_.mul_assoc]
  rfl

end GlobalTheory.PsiTopUnit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiValueFractionRingOfPsiCoord
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

theorem valF_psi_of_psiCoord : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (χ : D.X) (r : R), Formalism.L2.Pj.PsiCoord D χ r → ∃ j : PUnit → D.P.L.ι, ⊤ ≤ (D.c χ).left ⁻¹ᵁ D.P.L.U (j PUnit.unit) ∧ valF (𝟙 (Sp (FractionRing R))) _ ((D.psi χ).s j).val = algebraMap R (FractionRing R) r := by
  intro R _ _ D χ r h
  obtain ⟨j, hj, h, e⟩ := h
  refine ⟨j, hj, ?_⟩
  unfold valF
  rw [dif_pos (by exact h)]
  have e1 : ∀ (h' : ⊤ ≤ 𝟙 (Sp (FractionRing R)) ⁻¹ᵁ (D.P.L.LinComb (fun _ ↦ ptK (D.c χ)) fun _ ↦ -1).U j),
      (Scheme.Hom.appLE (𝟙 (Sp (FractionRing R)))
        ((D.P.L.LinComb (fun _ ↦ ptK (D.c χ)) fun _ ↦ -1).U j) ⊤ h').hom ((D.psi χ).s j).val
      = ((TK R).left.presheaf.map (homOfLE h).op).hom ((D.psi χ).s j).val := by
    intro h'
    rfl
  refine (congrArg (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom ((e1 h).trans e.symm)).trans ?_
  have e2 : DegPre.toOpen (R := R) ⊤ r = (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r := by
    have : (homOfLE (le_top : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ ⊤)).op = 𝟙 _ := rfl
    simp only [DegPre.toOpen, RingHom.comp_apply, this, CategoryTheory.Functor.map_id]
    rfl
  rw [e2]
  have n := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R)))
  have n' := congrArg (fun f => (f ≫ (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom).hom r) n
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at n'
  exact n'.symm

end GlobalTheory.Poinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiValueIsUnitOfPsiUnitOnLocalRing
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.PsiValUnit
open GlobalTheory.BXOf

theorem psi_val_unit_of_psiUnitOn : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (W : (Sp R).Opens) (χ : D.X), PsiUnitOn D χ W → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (T : Subring F) [IsLocalRing T] (φ₁ : R →+* T), (∀ r, (φ₁ r : F) = algebraMap (FractionRing R) F (algebraMap R _ r)) → spMap φ₁ (closedPoint T) ∈ W → ∀ (J₀ : D.P.A.left → D.P.L.ι), (∀ x, x ∈ D.P.L.U (J₀ x)) → ∀ (J : ((TF (R := R) F).left ⟶ D.P.A.left) → D.P.L.ι), (∀ ψ : Sp T ⟶ D.P.A.left, J (spMap T.subtype ≫ ψ) = J₀ (ψ (closedPoint T))) → ∃ u : Tˣ, (GlobalTheory.BXOf.sig F (val (D.psi χ) ((𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F) (closedPoint F) J) : F) = ((u : T) : F) := by
  intro R _ _ D W χ hW F _ _ T _ φ₁ hφ hP J₀ h₀ J hJ
  have hmem : spMap φ₁ (closedPoint T) ∈ W ⊓ (D.c χ).left ⁻¹ᵁ D.P.L.U (J₀ ((D.c χ).left (spMap φ₁ (closedPoint T)))) :=
    ⟨hP, h₀ _⟩
  obtain ⟨V, hVa, hPV, hVle⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Sp R).isBasis_affineOpens) hmem
  set j₀ := J₀ ((D.c χ).left (spMap φ₁ (closedPoint T))) with hj₀
  have hxK : D.xK χ = jK R ≫ (D.c χ).left := by
    show (toUnit (TK R) ≫ D.c χ).left = _
    rw [Over.comp_left]
    congr 1
  have hwch : jK R ⁻¹ᵁ V ≤ (LB.LinComb D.P.L (K := PUnit) (fun _ => D.xK χ) (fun _ => -1)).U (fun _ => j₀) :=
    fun x hx => Set.mem_iInter.2 fun _ => by
      show D.xK χ x ∈ D.P.L.U j₀
      rw [hxK]
      exact (hVle hx).2
  obtain ⟨r, hr, hre⟩ := hW (fun _ => j₀) V hVa (fun x hx => (hVle hx).1) (fun x hx => (hVle hx).2) hwch
  have hcomp : ((𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F) ≫ jK R = spMap T.subtype ≫ spMap φ₁ := by
    rw [Over.id_left, Category.id_comp]
    rw [jFK, jK, spMap, spMap, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact (RingHom.ext hφ).symm
  have hch : J (((𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F) ≫ D.xK χ) = j₀ := by
    have e : ((𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F) ≫ D.xK χ = spMap T.subtype ≫ (spMap φ₁ ≫ (D.c χ).left) := by
      rw [hxK, ← Category.assoc, hcomp, Category.assoc]
    rw [e, hJ]
    rfl
  have e1 := val_of (D.psi χ) ((𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F) (closedPoint F) J (fun _ => j₀) (fun _ => hch)
  have hin : jK R (((𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F) (closedPoint F)) ∈ V := by
    show (((𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F) ≫ jK R) (closedPoint F) ∈ V
    rw [hcomp]
    exact top_le_of_mem (spMap φ₁) hPV trivial
  have e2 : res hwch ((D.psi χ).s fun _ => j₀) = pullU (jK R) V hr.unit := Units.ext hre.symm
  have e3 := gm_res ((𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F) (closedPoint F) hwch hin ((D.psi χ).s fun _ => j₀)
  rw [e2, gm_pull ((𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F) (jK R) (closedPoint F) V hin hr.unit, hcomp] at e3
  have e4 := sig_nat T.subtype (spMap φ₁) hPV hr.unit
  refine ⟨sig T (gm (spMap φ₁) (closedPoint T) V hr.unit), ?_⟩
  exact (congrArg (fun u => (sig F u : F)) (e1.trans e3.symm)).trans (congrArg Units.val e4).symm

end GlobalTheory.PsiValUnit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSquareActionSectionsGeneratedStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_square_action_sections_generated : ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {S S' : Scheme.{0}} (X : Obj F 𝔠 S) (b : S' ⟶ S) (A' : Over S') [GrpObj A'] [IsCommMonObj A']
    (φ : A'.left ⟶ X.A.left), IsGrpPullback A' X.A b φ → ∀ (rm' : OAct (𝓞 F) A'),
    (∀ a, (rm'.act a).left ≫ φ = φ ≫ (X.rm.act a).left) → ∀ (φ₂ : (G2 A').left ⟶ (G2 X.A).left), IsSquare φ φ₂ →
    ∀ (c : 𝔠.elt) (T : Over S') (x : T ⟶ A'),
      HasGen (((X.P c).pull φ₂).pull (lift (fst A' T) (snd A' T ≫ x)).left) →
      ∀ a : 𝓞 F, (∀ d : 𝔠.elt, ∃ b : 𝓞 F, a • d = b • c) → x ≫ rm'.act a = 1 := by
  first | exact @GlobalTheory.PolKerPull.ker_pull | exact GlobalTheory.PolKerPull.ker_pull | (intros; apply GlobalTheory.PolKerPull.ker_pull <;> assumption)
end

