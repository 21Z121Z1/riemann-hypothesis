import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0048
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjugateHermitianLineIsometries
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0003
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0006
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0046
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0050
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0012
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0049
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0041
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionFamilySymmetricStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersection_family_symmetric : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ), IsIntersectionFamily I → ∀ (P : Ideal (MRing ι)) (e : ℕ) (L : Fin (e + 1) → HermLine ι) (i : Fin (e + 1)), IsArithVar P (e + 1) → (∀ j, IsSmoothHerm (L j)) → I P (e + 1) L = I P (e + 1) (Fin.snoc (fun j : Fin e => L (i.succAbove j)) (L i)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.movePositionToLast | exact GlobalTheory.CompanionTheory.Ar.Cmp.movePositionToLast | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.movePositionToLast <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.JoinCoordsChartIntegral
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace GlobalTheory.CompanionTheory.Ar.ChNorm

theorem mem_of_isIntegral_of_inv_mem {Ω : Type} [Field Ω] (R : Subring Ω) {v : Ω} (hv : IsIntegral R v)
    (hv0 : v ≠ 0) (hu : v⁻¹ ∈ R) : v ∈ R := by
  obtain ⟨p, hp, hpv⟩ := hv
  have huv : v * v⁻¹ = 1 := mul_inv_cancel₀ hv0
  have key : ∀ i m : ℕ, i ≤ m → v ^ i * v⁻¹ ^ m = v⁻¹ ^ (m - i) := by
    intro i m him
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le him
    rw [pow_add, ← mul_assoc, ← mul_pow, huv, one_pow, one_mul, Nat.add_sub_cancel_left]
  rw [hp.as_sum] at hpv
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul, Polynomial.eval₂_C,
    Polynomial.eval₂_X_pow] at hpv
  generalize p.natDegree = n at hpv
  cases n with
  | zero => simp at hpv
  | succ m =>
    have h2 := congrArg (· * v⁻¹ ^ m) hpv
    simp only [add_mul, Finset.sum_mul, zero_mul] at h2
    rw [pow_succ, mul_comm (v ^ m) v, mul_assoc, key m m le_rfl, Nat.sub_self, pow_zero, mul_one] at h2
    have e : v = -∑ i ∈ Finset.range (m + 1), algebraMap R Ω (p.coeff i) * v⁻¹ ^ (m - i) := by
      rw [eq_neg_iff_add_eq_zero, ← h2]
      congr 1
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [mul_assoc, key i m (by simp at hi; omega)]
    rw [e]
    refine neg_mem (sum_mem fun i _ => mul_mem ?_ (pow_mem hu _))
    exact (p.coeff i).2

end GlobalTheory.CompanionTheory.Ar.ChNorm

namespace GlobalTheory.CompanionTheory.Ar.ChNorm

theorem chRing_join_iff {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} (x : κ → Ω)
    {d n : ℕ} (z : κ ⊕ Fin n → Ω) (hz : ∀ c, z (Sum.inl c) = x c ^ d) (c : κ) (hc : x c ≠ 0) (a : Ω) :
    a ∈ chRing o (joinCo (RingHom.id Ω) x z) (c, Sum.inl c) ↔
      a ∈ Algebra.adjoin o (Set.range (fun j => x j / x c) ∪ Set.range (fun k => z k / x c ^ d)) := by
  have hd : x c ^ d ≠ 0 := pow_ne_zero _ hc
  have hrat : ∀ q : κ × (κ ⊕ Fin n), joinCo (RingHom.id Ω) x z q / joinCo (RingHom.id Ω) x z (c, Sum.inl c) =
      x q.1 / x c * (z q.2 / x c ^ d) := by
    intro q
    simp only [joinCo, RingHom.id_apply, hz c]
    exact mul_div_mul_comm _ _ _ _
  have hT : chRing o (joinCo (RingHom.id Ω) x z) (c, Sum.inl c) =
      Algebra.adjoin o (Set.range (fun j => x j / x c) ∪ Set.range (fun k => z k / x c ^ d)) := by
    apply le_antisymm
    · apply Algebra.adjoin_le
      rintro _ ⟨q, rfl⟩
      dsimp only
      rw [hrat]
      exact mul_mem (Algebra.subset_adjoin (Or.inl ⟨q.1, rfl⟩)) (Algebra.subset_adjoin (Or.inr ⟨q.2, rfl⟩))
    · apply Algebra.adjoin_le
      rintro _ (⟨j, rfl⟩ | ⟨k, rfl⟩)
      · have h1 : joinCo (RingHom.id Ω) x z (j, Sum.inl c) / joinCo (RingHom.id Ω) x z (c, Sum.inl c) ∈
            chRing o (joinCo (RingHom.id Ω) x z) (c, Sum.inl c) :=
          Algebra.subset_adjoin (Set.mem_range_self (j, Sum.inl c))
        rw [hrat, hz c, div_self hd, mul_one] at h1
        exact h1
      · have h1 : joinCo (RingHom.id Ω) x z (c, k) / joinCo (RingHom.id Ω) x z (c, Sum.inl c) ∈
            chRing o (joinCo (RingHom.id Ω) x z) (c, Sum.inl c) :=
          Algebra.subset_adjoin (Set.mem_range_self (c, k))
        rw [hrat, div_self hc, one_mul] at h1
        exact h1
  rw [hT]

end GlobalTheory.CompanionTheory.Ar.ChNorm

namespace GlobalTheory.CompanionTheory.Ar.ChNorm

theorem joinCo_div {Ω : Type} [Field Ω] {κ : Type} (x : κ → Ω) {d n : ℕ} (z : κ ⊕ Fin n → Ω)
    (hz : ∀ c, z (Sum.inl c) = x c ^ d) (c : κ) (q : κ × (κ ⊕ Fin n)) :
    joinCo (RingHom.id Ω) x z q / joinCo (RingHom.id Ω) x z (c, Sum.inl c) = x q.1 / x c * (z q.2 / x c ^ d) := by
  simp only [joinCo, RingHom.id_apply, hz c]
  exact mul_div_mul_comm _ _ _ _

theorem join_chart_normalisation : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (d n : ℕ) (z : κ ⊕ Fin n → Ω) (M' : PModel o (joinCo (RingHom.id Ω) x z)), (∀ c, z (Sum.inl c) = x c ^ d) → (∀ c, x c ≠ 0 → ∀ a : Ω, IsIntegral (chRing o x c) a ↔ a ∈ Submodule.span (chRing o x c) (Set.range fun k => z k / x c ^ d)) → ∀ c, x c ≠ 0 → (∀ a : Ω, a ∈ chRing o (joinCo (RingHom.id Ω) x z) (c, Sum.inl c) ↔ IsIntegral (chRing o x c) a) ∧ ∀ p' : Cpt M'.ξ, (∀ j, x j / x c ∈ regAt M'.ξ p') → InChart M'.ξ (joinCo (RingHom.id Ω) x z) (c, Sum.inl c) p' := by
  intro o _ Ω _ _ κ _ x d n z M' hz hspan c hc
  have hd : x c ^ d ≠ 0 := pow_ne_zero _ hc
  have hyS : ∀ k, IsIntegral (chRing o x c) (z k / x c ^ d) := fun k =>
    (hspan c hc _).2 (Submodule.subset_span ⟨k, rfl⟩)
  have hxS : ∀ j, x j / x c ∈ chRing o x c := fun j => Algebra.subset_adjoin ⟨j, rfl⟩
  refine ⟨fun a => ?_, fun p' hp' => ?_⟩
  · rw [chRing_join_iff x z hz c hc a]
    constructor
    · intro ha
      have hle : Algebra.adjoin o (Set.range (fun j => x j / x c) ∪ Set.range (fun k => z k / x c ^ d)) ≤
          (integralClosure (chRing o x c) Ω).restrictScalars o := by
        apply Algebra.adjoin_le
        rintro _ (⟨j, rfl⟩ | ⟨k, rfl⟩)
        · exact (Subalgebra.mem_restrictScalars o).2 ((mem_integralClosure_iff _ _).2
            (isIntegral_algebraMap (x := (⟨_, hxS j⟩ : chRing o x c))))
        · exact (Subalgebra.mem_restrictScalars o).2 ((mem_integralClosure_iff _ _).2 (hyS k))
      exact (mem_integralClosure_iff _ _).1 ((Subalgebra.mem_restrictScalars o).1 (hle ha))
    · intro ha
      have hSle : chRing o x c ≤
          Algebra.adjoin o (Set.range (fun j => x j / x c) ∪ Set.range (fun k => z k / x c ^ d)) :=
        Algebra.adjoin_mono Set.subset_union_left
      refine Submodule.span_induction
        (p := fun b _ => b ∈ Algebra.adjoin o (Set.range (fun j => x j / x c) ∪ Set.range (fun k => z k / x c ^ d)))
        ?_ ?_ ?_ ?_ ((hspan c hc a).1 ha)
      · rintro _ ⟨k, rfl⟩
        exact Algebra.subset_adjoin (Or.inr ⟨k, rfl⟩)
      · exact zero_mem _
      · intro a b _ _ ha hb
        exact add_mem ha hb
      · intro s b _ hb
        rw [Subalgebra.smul_def]
        exact mul_mem (hSle s.2) hb
  · obtain ⟨hctr, l, hl⟩ :=
      GlobalTheory.T.join_coords_centre_chart o Ω κ (κ ⊕ Fin n) x Ω (RingHom.id Ω) z M' (fun _ => rfl) p'
    obtain ⟨c', -, hc'⟩ := hctr
    have ho : ∀ r : o, algebraMap o Ω r ∈ regAt M'.ξ p' := fun r =>
      hc' _ (Subalgebra.algebraMap_mem _ r)
    have hSle : ∀ a ∈ chRing o x c, a ∈ regAt M'.ξ p' := by
      intro a ha
      have h1 : a ∈ (chRing o x c).toSubring := ha
      rw [chRing, Algebra.adjoin_eq_ring_closure] at h1
      exact (Subring.closure_le.2 (Set.union_subset (by rintro _ ⟨r, rfl⟩; exact ho r)
        (by rintro _ ⟨j, rfl⟩; exact hp' j))) h1
    let φ : chRing o x c →+* regAt M'.ξ p' :=
      { toFun := fun s => ⟨s, hSle s s.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    have hvint : IsIntegral (regAt M'.ξ p') (z l / x c ^ d) :=
      IsIntegral.map_of_comp_eq φ (RingHom.id Ω) (by ext; rfl) (hyS l)
    obtain ⟨hzl, hzr⟩ := hl
    have hv : z l / x c ^ d ∈ regAt M'.ξ p' :=
      mem_of_isIntegral_of_inv_mem _ hvint (div_ne_zero hzl hd) (by rw [inv_div, ← hz c]; exact hzr _)
    have hy : ∀ k, z k / x c ^ d ∈ regAt M'.ξ p' := fun k => by
      have e : z k / x c ^ d = z k / z l * (z l / x c ^ d) := by field_simp
      rw [e]
      exact mul_mem (hzr k) hv
    refine ⟨?_, fun q => ?_⟩
    · simp only [joinCo, RingHom.id_apply, hz c]
      exact mul_ne_zero hc hd
    · rw [joinCo_div x z hz c q]
      exact mul_mem (hp' q.1) (hy q.2)

end GlobalTheory.CompanionTheory.Ar.ChNorm
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeEqOfCodimOneEqStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_eq_of_codim_one_eq : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) [IsLocallyNoetherian X], IsCptGen ξ → ∀ (T : Set (Cpt ξ)), (∀ p ∈ T, ∀ q : Cpt ξ, q.1 ⤳ p.1 → q ∈ T) → (∀ p ∈ T, IsIntegrallyClosed (X.presheaf.stalk p.1)) → ∀ (E : Type) [AddCommGroup E] [Module Ω E] (L L' : Lat ξ E) (r : ℕ) (V : Submodule Ω E), L.IsVBOn T r V → L'.IsVBOn T r V → (∀ p ∈ T, ringKrullDim (X.presheaf.stalk p.1) = 1 → L p = L' p) → ∀ p ∈ T, L p = L' p := by
  first | exact @GlobalTheory.CompanionTheory.Ar.lat_agree_of_height_one | exact GlobalTheory.CompanionTheory.Ar.lat_agree_of_height_one | (intros; apply GlobalTheory.CompanionTheory.Ar.lat_agree_of_height_one <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeGeneratorInvertConstantStatement
section
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_generator_invert_constant : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [IsDomain O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)) [IsNoetherianRing O] [LocallyOfFiniteType s] [QuasiCompact s], ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → Function.Injective (algebraMap O Ω) → IsCptGen ξ → ∀ (L : Lat ξ Ω) (T : Set (Cpt ξ)) (n₀ : O) (t : Ω), n₀ ≠ 0 → (∀ p, unitAt ξ p (algebraMap O Ω n₀) → p ∈ T) → L.IsVBOn T 1 ⊤ → (∀ p ∈ genFibre O ξ, L.IsGenAt p t) → ∃ n : O, n ≠ 0 ∧ ∀ p, unitAt ξ p (algebraMap O Ω n) → L.IsGenAt p t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.lattice_generator_spread | exact GlobalTheory.CompanionTheory.Ar.Flat.lattice_generator_spread | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.lattice_generator_spread <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticePatchAtPrimesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_patch_at_primes : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (S : Finset ℕ) (L₀ : Lat ξ E) (Lp : ℕ → Lat ξ E) (q : Cpt ξ), (∀ p ∈ S, p.Prime) → ((∀ p ∈ S, ¬ InFibre ξ p q) → Lat.patch S L₀ Lp q = L₀ q) ∧ ∀ p ∈ S, InFibre ξ p q → Lat.patch S L₀ Lp q = Lp p q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Lat.patch_values | exact GlobalTheory.CompanionTheory.Ar.Lat.patch_values | (intros; apply GlobalTheory.CompanionTheory.Ar.Lat.patch_values <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeSubQuotientSplit
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SatSub

open Submodule Module

variable {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E]

theorem exists_basis_of_isCompl (R : Type) [CommRing R] [IsLocalRing R] {M : Type} [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M] (A B : Submodule R M) (h : IsCompl A B) :
    ∃ k : ℕ, Nonempty (Module.Basis (Fin k) R A) := by
  have h1 : Module.Projective R A :=
    Module.Projective.of_split A.subtype (Submodule.linearProjOfIsCompl A B h)
      (LinearMap.ext fun x => Submodule.linearProjOfIsCompl_apply_left h x)
  have h2 : Module.Finite R A :=
    Module.Finite.of_surjective (Submodule.linearProjOfIsCompl A B h) (Submodule.linearProjOfIsCompl_surjective h)
  have h3 : Module.FinitePresentation R A := Module.finitePresentation_of_projective R A
  have h4 : Module.Free R A := Module.free_of_flat_of_isLocalRing
  exact ⟨_, ⟨Module.finBasis R A⟩⟩

theorem eq_zero_of_mem {V : Submodule Ω E} {s : ℕ} {e : Fin s → E}
    (hc : LinearIndependent Ω fun i => V.mkQ (e i)) {y : E} (hy : y ∈ span Ω (Set.range e)) (hyV : y ∈ V) :
    y = 0 := by
  obtain ⟨a, rfl⟩ := (mem_span_range_iff_exists_fun Ω).1 hy
  have h0 : ∑ i, a i • V.mkQ (e i) = 0 := by
    have h := (Submodule.Quotient.mk_eq_zero V).2 hyV
    rw [← Submodule.mkQ_apply, map_sum] at h
    simpa using h
  have ha := Fintype.linearIndependent_iff.1 hc a h0
  simp [ha]

theorem sup_inf_eq (R : Subring Ω) {V : Submodule Ω E} {s k : ℕ} {e : Fin s → E} {n : Fin k → E}
    (hc : LinearIndependent Ω fun i => V.mkQ (e i)) (hn : ∀ j, n j ∈ V) :
    (span R (Set.range e) ⊔ span R (Set.range n)) ⊓ V.restrictScalars R = span R (Set.range n) := by
  have hnV : span R (Set.range n) ≤ V.restrictScalars R := span_le.2 (by rintro _ ⟨j, rfl⟩; exact hn j)
  apply le_antisymm
  · rintro x ⟨hx, hxV⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := mem_sup.1 hx
    have hy0 : y = 0 := eq_zero_of_mem hc (span_le_restrictScalars R Ω _ hy) (by
      have h := V.sub_mem hxV (hnV hz)
      simpa using h)
    simpa [hy0] using hz
  · exact le_inf le_sup_right hnV

def cat {s k : ℕ} (e : Fin s → E) (n : Fin k → E) : Fin (s + k) → E := Sum.elim e n ∘ finSumFinEquiv.symm

theorem range_cat {s k : ℕ} (e : Fin s → E) (n : Fin k → E) : Set.range (cat e n) = Set.range e ∪ Set.range n := by
  rw [cat, EquivLike.range_comp, Set.Sum.elim_range]

theorem span_cat (R : Subring Ω) {s k : ℕ} (e : Fin s → E) (n : Fin k → E) :
    span R (Set.range (cat e n)) = span R (Set.range e) ⊔ span R (Set.range n) := by
  rw [range_cat, span_union]

theorem exists_frame (R : Subring Ω) [IsLocalRing R] {V W : Submodule Ω E} (hVW : V ≤ W) (P : Submodule R E)
    {g s : ℕ} (b : Fin g → E) (hb : LinearIndependent Ω b) (hbW : span Ω (Set.range b) = W)
    (hP : P = span R (Set.range b)) (c : Fin s → E ⧸ V) (hc : LinearIndependent Ω c)
    (hPc : P.map (V.mkQ.restrictScalars R) = span R (Set.range c)) :
    ∃ (k : ℕ) (e : Fin s → E) (n : Fin k → E), LinearIndependent Ω (cat e n) ∧
      P = span R (Set.range e) ⊔ span R (Set.range n) ∧ (LinearIndependent Ω fun i => V.mkQ (e i)) ∧
      (∀ j, n j ∈ V) ∧ span Ω (Set.range n) = V := by
  have hinj : Function.Injective fun r : R => r • (1 : Ω) := fun x y h => by
    simpa [Subring.smul_def] using h

  have hlift : ∀ i, ∃ x ∈ P, V.mkQ x = c i := fun i => by
    have h : c i ∈ P.map (V.mkQ.restrictScalars R) := by
      rw [hPc]; exact subset_span ⟨i, rfl⟩
    obtain ⟨x, hx, e⟩ := h
    exact ⟨x, hx, e⟩
  choose e heP hec using hlift
  have hc' : LinearIndependent Ω fun i => V.mkQ (e i) := by simpa only [hec] using hc
  set Q := span R (Set.range e) with hQ
  set N := P ⊓ V.restrictScalars R with hN
  have hQP : Q ≤ P := span_le.2 (by rintro _ ⟨i, rfl⟩; exact heP i)
  have hdec : ∀ x ∈ P, ∃ y ∈ Q, ∃ z ∈ N, y + z = x := fun x hx => by
    have h : V.mkQ x ∈ span R (Set.range c) := by
      rw [← hPc]; exact ⟨x, hx, rfl⟩
    obtain ⟨a, ha⟩ := (mem_span_range_iff_exists_fun R).1 h
    have hy : ∑ i, a i • e i ∈ Q := sum_mem fun i _ => Q.smul_mem _ (subset_span ⟨i, rfl⟩)
    refine ⟨_, hy, x - ∑ i, a i • e i, ⟨P.sub_mem hx (hQP hy), ?_⟩, by abel⟩
    change x - ∑ i, a i • e i ∈ V
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub, ← ha, map_sum]
    simp [hec, Subring.smul_def]
  have hdisj : ∀ x, x ∈ Q → x ∈ N → x = 0 := fun x hx hxN =>
    eq_zero_of_mem hc' (span_le_restrictScalars R Ω _ hx) hxN.2

  have hbR : LinearIndependent R b := hb.restrict_scalars hinj
  have hfree : Module.Free R P := by
    subst hP; exact Module.Free.of_basis (Module.Basis.span hbR)
  have hfin : Module.Finite R P := by
    subst hP; exact Module.Finite.span_of_finite R (Set.finite_range b)
  have hcompl : IsCompl (N.comap P.subtype) (Q.comap P.subtype) := by
    constructor
    · rw [Submodule.disjoint_def]
      intro x h1 h2
      exact Subtype.ext (hdisj _ h2 h1)
    · rw [codisjoint_iff, eq_top_iff]
      intro x _
      obtain ⟨y, hy, z, hz, e⟩ := hdec x x.2
      refine mem_sup.2 ⟨⟨z, hz.1⟩, hz, ⟨y, hQP hy⟩, hy, Subtype.ext ?_⟩
      simpa [add_comm] using e
  obtain ⟨k, ⟨β⟩⟩ := exists_basis_of_isCompl R _ _ hcompl
  let φ : (N.comap P.subtype) →ₗ[R] E := P.subtype ∘ₗ (N.comap P.subtype).subtype
  have hφ : Function.Injective φ := fun x y h => Subtype.ext (Subtype.ext h)
  have hφr : LinearMap.range φ = N := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩; exact y.2
    · intro h; exact ⟨⟨⟨x, h.1⟩, h⟩, rfl⟩
  let n : Fin k → E := fun j => φ (β j)
  have hnN : span R (Set.range n) = N := by
    have h : Set.range n = φ '' Set.range β := by
      rw [← Set.range_comp]; rfl
    rw [h, ← Submodule.map_span, β.span_eq, Submodule.map_top, hφr]
  have hnR : LinearIndependent R n := β.linearIndependent.map' φ (LinearMap.ker_eq_bot.2 hφ)
  have hnV : ∀ j, n j ∈ V := fun j => by
    have h : n j ∈ N := by rw [← hφr]; exact ⟨_, rfl⟩
    exact h.2
  have hPsup : P = Q ⊔ span R (Set.range n) := by
    rw [hnN]
    refine le_antisymm (fun x hx => ?_) (sup_le hQP inf_le_left)
    obtain ⟨y, hy, z, hz, rfl⟩ := hdec x hx
    exact add_mem (mem_sup_left hy) (mem_sup_right hz)

  have heR : LinearIndependent R e := by
    have h : LinearIndependent R ((V.mkQ.restrictScalars R) ∘ e) := hc'.restrict_scalars hinj
    exact h.of_comp _
  have hdisj' : Disjoint (span R (Set.range e)) (span R (Set.range n)) := by
    rw [hnN, Submodule.disjoint_def]
    exact hdisj
  have hsumR : LinearIndependent R (Sum.elim e n) := heR.sum_type hnR hdisj'
  have hcatR : LinearIndependent R (cat e n) := hsumR.comp _ (Equiv.injective _)
  have hspan : span R (Set.range (cat e n)) = P := by rw [span_cat, hPsup, hnN]
  have hcard : g = s + k := by
    have h1 := finrank_span_eq_card hbR
    have h2 := finrank_span_eq_card hcatR
    rw [hspan] at h2
    rw [← hP] at h1
    simpa using h1.symm.trans h2

  have hPW : ∀ {x}, x ∈ P → x ∈ W := fun {x} hx => by
    rw [hP] at hx
    rw [← hbW]
    exact span_le_restrictScalars R Ω _ hx
  have hW : span Ω (Set.range (cat e n)) = W := by
    apply le_antisymm
    · refine span_le.2 ?_
      rintro _ ⟨i, rfl⟩
      refine hPW ?_
      rw [← hspan]
      exact subset_span ⟨i, rfl⟩
    · rw [← hbW]
      refine span_le.2 ?_
      rintro _ ⟨i, rfl⟩
      have h : b i ∈ span R (Set.range (cat e n)) := by
        rw [hspan, hP]; exact subset_span ⟨i, rfl⟩
      exact span_le_restrictScalars R Ω _ h
  have hcatΩ : LinearIndependent Ω (cat e n) := by
    rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, hW, ← hbW, finrank_span_eq_card hb]
    simp [hcard]
  have hsumΩ : LinearIndependent Ω (Sum.elim e n) := by
    have h := hcatΩ.comp _ (finSumFinEquiv (m := s) (n := k)).injective
    simpa [cat, Function.comp_def] using h
  refine ⟨k, e, n, hcatΩ, hPsup, hc', hnV, le_antisymm (span_le.2 ?_) fun v hv => ?_⟩
  · rintro _ ⟨j, rfl⟩; exact hnV j
  · have hvW := hVW hv
    rw [← hW, range_cat, span_union] at hvW
    obtain ⟨y, hy, z, hz, rfl⟩ := mem_sup.1 hvW
    have hzV : z ∈ V := (span_le.2 (by rintro _ ⟨j, rfl⟩; exact hnV j) : span Ω (Set.range n) ≤ V) hz
    have hy0 : y = 0 := eq_zero_of_mem hc' hy (by
      have h := V.sub_mem hv hzV
      simpa using h)
    simpa [hy0] using hz

end GlobalTheory.CompanionTheory.Ar.SatSub

namespace GlobalTheory.CompanionTheory.Ar

open Submodule Module SatSub

theorem inter_isVBOn_of_map : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type)
    [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (T : Set (Cpt ξ)) (g s : ℕ) (W V : Submodule Ω E)
    (W' : Submodule Ω (E ⧸ V)), V ≤ W → L.IsVBOn T g W → (L.map V.mkQ).IsVBOn T s W' →
    (L.inter V).IsVBOn T (Module.finrank Ω V) V ∧
      ∀ p ∈ T, ∃ Q : Submodule (regAt ξ p) E, Disjoint Q (L.inter V p) ∧ Q ⊔ L.inter V p = L p := by
  intro X Ω _ ξ E _ _ L T g s W V W' hVW hL hM
  have hcoh : L.IsCohOn T := (GlobalTheory.T.coherent_lattice_closure X Ω ξ E E L L T).1 g W hL
  have key : ∀ p ∈ T, ∃ (k : ℕ) (e : Fin s → E) (n : Fin k → E), LinearIndependent Ω (cat e n) ∧
      L p = span (regAt ξ p) (Set.range e) ⊔ span (regAt ξ p) (Set.range n) ∧
      (LinearIndependent Ω fun i => V.mkQ (e i)) ∧ (∀ j, n j ∈ V) ∧ span Ω (Set.range n) = V := fun p hp => by
    have := (GlobalTheory.T.regAt_local_order_fraction X Ω ξ).1 p
    obtain ⟨U, hU, b, hbW, hb⟩ := hL p hp
    obtain ⟨U', hU', c, -, hc⟩ := hM p hp
    obtain ⟨hb1, hb2⟩ := hb p hp hU
    obtain ⟨hc1, hc2⟩ := hc p hp hU'
    exact exists_frame (regAt ξ p) hVW (L p) b hb1 hbW hb2 c hc1 hc2
  refine ⟨fun p hp => ?_, fun p hp => ?_⟩
  · obtain ⟨k, e, n, hf, hP, hc, hn, hnV⟩ := key p hp
    have hnI : LinearIndependent Ω n := by
      have h := hf.comp _ ((finSumFinEquiv (m := s) (n := k)).injective.comp Sum.inr_injective)
      simpa [cat, Function.comp_def] using h
    have hk : k = Module.finrank Ω V := by
      rw [← hnV, finrank_span_eq_card hnI]; simp
    subst hk
    obtain ⟨U, hU, h⟩ := GlobalTheory.T.frame_open_neighbourhood X Ω ξ E L T _ (cat e n) p hcoh hp
      ⟨hf, by rw [span_cat]; exact hP⟩
    refine ⟨U, hU, n, hnV, fun q hq hqU => ⟨hnI, ?_⟩⟩
    obtain ⟨-, h2⟩ := h q hq hqU
    rw [span_cat] at h2
    change L q ⊓ V.restrictScalars (regAt ξ q) = _
    rw [h2]
    exact sup_inf_eq (regAt ξ q) hc hn
  · obtain ⟨k, e, n, hf, hP, hc, hn, hnV⟩ := key p hp
    have hint : L.inter V p = span (regAt ξ p) (Set.range n) := by
      change L p ⊓ V.restrictScalars (regAt ξ p) = _
      rw [hP]
      exact sup_inf_eq (regAt ξ p) hc hn
    refine ⟨span (regAt ξ p) (Set.range e), ?_, by rw [hint, ← hP]⟩
    rw [Submodule.disjoint_def]
    intro x hx hx'
    have hxV : x ∈ V := by
      rw [hint] at hx'
      exact (span_le.2 (by rintro _ ⟨j, rfl⟩; exact hn j) : span Ω (Set.range n) ≤ V)
        (span_le_restrictScalars (regAt ξ p) Ω _ hx')
    exact eq_zero_of_mem hc (span_le_restrictScalars (regAt ξ p) Ω _ hx) hxV

end GlobalTheory.CompanionTheory.Ar
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LineBundleNormalProperPullback
section
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem lat_isGenAt_of_proper_birational : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) [IsLocallyNoetherian X] (X' : Scheme.{0}) (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω') [IsProper f], Dominates ξ' ξ f i → Function.Bijective i → IsCptGen ξ → NormalCpt ξ → ∀ (L : Lat ξ Ω) (T : Set (Cpt ξ)) (p : Cpt ξ) (t : Ω), L.IsVBOn T 1 ⊤ → (∀ q : Cpt ξ, q.1 ⤳ p.1 → q ∈ T) → (∀ p' : Cpt ξ', f p'.1 ⤳ p.1 → (L.pull ξ' f i.toAddMonoidHom).IsGenAt p' (i t)) → L.IsGenAt p t :=
  @PositivityTheory.Xgn.line_lattice_proper_pushdown

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalizationClosureEqualStatement
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localization_closure_equal : ∀ {K : Type} [Field K] {Q : Type} [Fintype Q] (A B : Subring K) (t : Q → K), (∀ q, t q ≠ 0) → (∀ q, t q ∈ A) → (∀ q, (t q)⁻¹ ∈ B) → A ≤ Subring.closure ((B : Set K) ∪ Set.range t) → B ≤ Subring.closure ((A : Set K) ∪ Set.range fun q => (t q)⁻¹) → locSub A (∏ q, t q) = locSub B (∏ q, t q)⁻¹ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.locSub_eq_of_inverse_family | exact GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.locSub_eq_of_inverse_family | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.locSub_eq_of_inverse_family <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalizationClosureSmoothStatement
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localization_closure_smooth : ∀ {Ω K : Type} [Field Ω] [Field K] [Algebra Ω K] {ι : Type} [Finite ι] (R : Subring Ω) (v : ι → K), AlgebraicIndependent Ω v → ∀ ℓ : K, ℓ ∈ Subring.closure (((R.map (algebraMap Ω K) : Subring K) : Set K) ∪ Set.range v) → ℓ ≠ 0 → ∀ h : (∀ a ∈ R, algebraMap Ω K a ∈ locSub (Subring.closure (((R.map (algebraMap Ω K) : Subring K) : Set K) ∪ Set.range v)) ℓ), (((algebraMap Ω K).comp R.subtype).codRestrict (locSub (Subring.closure (((R.map (algebraMap Ω K) : Subring K) : Set K) ∪ Set.range v)) ℓ) (fun a => h a a.2)).Smooth := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.smooth_locSub_closure | exact GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.smooth_locSub_closure | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.smooth_locSub_closure <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LuDecompositionOfMinorsStatement
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lu_decomposition_of_minors : ∀ {F : Type} [Field F] {r : ℕ} (Y : Matrix (Fin r) (Fin r) F), (∀ (k : ℕ) (hk : k ≤ r), kMinor Y k hk (Fin.castLE hk) ≠ 0) → ∃ C V : Matrix (Fin r) (Fin r) F, (∀ l k, k < l → C l k = 0) ∧ (∀ l k, l < k → V l k = 0) ∧ (∀ l, V l l = 1) ∧ Y * C = V := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.exists_lu_of_leading_minors | exact GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.exists_lu_of_leading_minors | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.exists_lu_of_leading_minors <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemBtOrderIffBtSetStatement
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_btOrder_iff_btSet : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens) (f : T → R), f ∈ Γ.btOrder U ↔ f ∈ Γ.btSet U := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.mem_btOrder_iff_mem_btSet | exact GlobalTheory.CompanionTheory.Ar.BT.mem_btOrder_iff_mem_btSet | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.mem_btOrder_iff_mem_btSet <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NormalCodimOneStalkDvrStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normal_codim_one_stalk_dvr : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X], IsNormalScheme X → ∀ p : X, ringKrullDim (X.presheaf.stalk p) = 1 → ∃ _ : IsDomain (X.presheaf.stalk p), IsDiscreteValuationRing (X.presheaf.stalk p) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.stalk_isDiscreteValuationRing_of_dim_one | exact GlobalTheory.CompanionTheory.Ar.stalk_isDiscreteValuationRing_of_dim_one | (intros; apply GlobalTheory.CompanionTheory.Ar.stalk_isDiscreteValuationRing_of_dim_one <;> assumption)
end

