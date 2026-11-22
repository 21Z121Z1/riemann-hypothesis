import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeSandwichAinf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0250
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0303
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachInclusionXQFrobenius
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0323
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0270
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0244
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachFreeLatticeEqWachLatticeInvertX
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices Module

noncomputable section

namespace GlobalTheory.NL.InvX

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
    {W : LocWach PD LL O v n} (E : EtTie W RA RW inclR φR gR πA)

theorem jD_smulA (T : LocLat G Qp LL O) (a : LetA O n) (y : W.DD T) :
    E.jD T (a • y) = inclR (E.io a) • E.jD T y := by
  rw [← algebraMap_smul W.EE a y, E.jD_smul, E.ioE_ext]

theorem φD_smulA (T : LocLat G Qp LL O) (a : LetA O n) (y : W.DD T) :
    W.φD T (a • y) = W.φA a • W.φD T y := by
  rw [← algebraMap_smul W.EE a y, W.φD_smul, W.φE_ext, algebraMap_smul]
  rfl

theorem uniform {A M ι : Type} [CommRing A] [AddCommGroup M] [Module A M] [Fintype ι] (q : A)
    (S : Submodule A M) (w : ι → M) (h : ∀ i, ∃ k : ℕ, q ^ k • w i ∈ S) :
    ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ i, q ^ k • w i ∈ S := by
  choose k hk using h
  refine ⟨Finset.univ.sup k, fun m hm i => ?_⟩
  have : k i ≤ m := (Finset.le_sup (Finset.mem_univ i)).trans hm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le this
  rw [add_comm, pow_add, mul_smul]
  exact S.smul_mem _ (hk i)

theorem basis_of_free (T : LocLat G Qp LL O) (S : Submodule (LetA O n) (W.DD T)) (hS : FreeA W T S) :
    ∃ r : ℕ, Nonempty (Basis (Fin r) (LetA O n) ↥S) := by
  obtain ⟨r, b, hb, hu⟩ := hS
  refine ⟨r, ⟨Basis.mk (v := fun j => (⟨b j, hb j⟩ : ↥S)) ?_ ?_⟩⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg
    have h1 := congrArg S.subtype hg
    rw [map_sum, map_zero] at h1
    have h2 : g = 0 := (hu 0 S.zero_mem).unique h1.symm (by simp)
    intro i; rw [h2]; rfl
  · intro x _
    obtain ⟨a, ha, -⟩ := hu x.1 x.2
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨a, Subtype.ext ?_⟩
    change S.subtype _ = _
    rw [map_sum]
    exact ha.symm

theorem basis_rank [Nontrivial W.EE] (T : LocLat G Qp LL O) (S : Submodule (LetA O n) (W.DD T))
    (hS : FreeA W T S) (hB : IsBaseChange W.EE S.subtype) :
    Nonempty (Basis (Fin (Module.finrank O ↥T.L.T)) (LetA O n) ↥S) := by
  obtain ⟨r, ⟨b⟩⟩ := basis_of_free T S hS
  have h := Module.finrank_eq_card_basis (hB.basis b)
  rw [(W.DD_free T).2, Fintype.card_fin] at h
  rw [h]
  exact ⟨b⟩

theorem sand_of
    (hA : ∀ (p q : Type) [Fintype p] [Fintype q] (Z : Matrix p q RW) (P : Matrix p p RA)
      (P' : Matrix q q RA) (Y : Matrix p q RA),
      Z.map φR = P.map inclR * Z * P'.map inclR + Y.map inclR → ∀ a b, Z a b ∈ Set.range inclR)
    (hφ : ∀ a, inclR (E.io (W.φA a)) = φR (inclR (E.io a)))
    (hE : ∀ x : W.EE, (∃ y, inclR y = E.ioE x) → ∃ a : LetA O n, algebraMap _ W.EE a = x)
    (T : LocLat G Qp LL O) [Nontrivial O] (S : Submodule (LetA O n) (W.DD T))
    (b : Basis (Fin (Module.finrank O ↥T.L.T)) (LetA O n) ↥S)
    (hB : IsBaseChange W.EE S.subtype)
    (hS1 : ∀ x ∈ S, ∃ k : ℕ, W.Q ^ k • W.φD T x ∈ S)
    (hS2 : ∀ y ∈ S, ∃ k : ℕ, W.Q ^ k • y ∈ φspan W T S) :
    ∃ m : ℕ, (∀ y ∈ S, E.jD T (W.X ^ m • y) ∈ LinearMap.range (TWincl inclR T)) ∧
      ∀ y : W.DD T, E.jD T y ∈ LinearMap.range (TWincl inclR T) → W.X ^ m • y ∈ S := by
  classical
  have hx : φR (inclR (E.io W.X)) = inclR (E.io W.X) * inclR (E.io W.Q) := by
    rw [← hφ, W.φA_X, map_mul, map_mul]
  have : Module.Free O ↥T.L.T := T.L.free
  have : Module.Finite O ↥T.L.T := Module.Finite.iff_fg.mpr T.L.fg
  let tb := Module.finBasis O ↥T.L.T
  have hexp : ∀ y ∈ S, ∃ c : Fin (Module.finrank O ↥T.L.T) → LetA O n,
      y = ∑ j, c j • (b j : W.DD T) := by
    intro y hy
    refine ⟨fun j => b.repr ⟨y, hy⟩ j, ?_⟩
    have := congrArg S.subtype (b.sum_repr ⟨y, hy⟩)
    rw [map_sum] at this
    exact this.symm
  have hexpE : ∀ y : W.DD T, ∃ c : Fin (Module.finrank O ↥T.L.T) → W.EE,
      y = ∑ j, c j • (b j : W.DD T) := by
    intro y
    refine ⟨fun j => (hB.basis b).repr y j, ?_⟩
    conv_lhs => rw [← (hB.basis b).sum_repr y]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hB.basis_apply]; rfl
  have hj : ∀ (c : Fin (Module.finrank O ↥T.L.T) → LetA O n)
      (w : Fin (Module.finrank O ↥T.L.T) → W.DD T),
      E.jD T (∑ j, c j • w j) = ∑ j, inclR (E.io (c j)) • E.jD T (w j) := by
    intro c w
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => jD_smulA E T _ _
  have hjE : ∀ (c : Fin (Module.finrank O ↥T.L.T) → W.EE)
      (w : Fin (Module.finrank O ↥T.L.T) → W.DD T),
      E.jD T (∑ j, c j • w j) = ∑ j, E.ioE (c j) • E.jD T (w j) := by
    intro c w
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => E.jD_smul T _ _
  have hsp : ⊤ ≤ Submodule.span RW (Set.range fun i => E.jD T (b i : W.DD T)) := by
    rw [← E.jD_span T, Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    obtain ⟨c, rfl⟩ := hexpE y
    rw [hjE]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hli : LinearIndependent RW fun i => E.jD T (b i : W.DD T) := by
    have hs := hsp
    rw [← Finsupp.range_linearCombination, top_le_iff, LinearMap.range_eq_top] at hs
    exact OrzechProperty.injective_of_surjective_of_injective _ _
      (Algebra.TensorProduct.basis RW tb).linearIndependent hs
  obtain ⟨k₁, h1⟩ := uniform W.Q S (fun i => W.φD T (b i : W.DD T))
    (fun i => hS1 _ (b i).2)
  obtain ⟨k₂, h2⟩ := uniform W.Q (φspan W T S)
    (fun i => (b i : W.DD T)) (fun i => hS2 _ (b i).2)
  replace h1 := h1 (max k₁ k₂) (le_max_left _ _)
  replace h2 := h2 (max k₁ k₂) (le_max_right _ _)
  refine ⟨max k₁ k₂, ?_⟩
  generalize max k₁ k₂ = m at h1 h2
  constructor
  · choose P hP using fun i => hexp _ (h1 i)
    have hup := GlobalTheory.Sandwich.upper tb inclR φR hA _ _ hx m (fun i => E.jD T (b i : W.DD T))
      (Matrix.of fun i j => E.io (P i j)) (by
        intro i
        have := congrArg (E.jD T) (hP i)
        rw [hj, jD_smulA, E.jD_φ, map_pow, map_pow] at this
        exact this)
    intro y hy
    obtain ⟨c, rfl⟩ := hexp y hy
    rw [jD_smulA, map_pow, map_pow, hj, Finset.smul_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [smul_comm]
    exact GlobalTheory.Sandwich.incl_smul_mem inclR _ _ (hup j)
  · have hexp2 : ∀ y ∈ φspan W T S,
        ∃ c : Fin (Module.finrank O ↥T.L.T) → LetA O n,
        y = ∑ j, c j • W.φD T (b j : W.DD T) := by
      intro y hy
      have : φspan W T S ≤ Submodule.span (LetA O n)
          (Set.range fun j => W.φD T (b j : W.DD T)) := by
        refine Submodule.span_le.mpr ?_
        rintro _ ⟨z, hz, rfl⟩
        obtain ⟨c, rfl⟩ := hexp z hz
        rw [map_sum]
        refine Submodule.sum_mem _ fun j _ => ?_
        rw [φD_smulA]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp (this hy)
      exact ⟨c, hc.symm⟩
    choose U hU using fun i => hexp2 _ (h2 i)
    let nb : Basis (Fin (Module.finrank O ↥T.L.T)) RW (TW RW T) := Basis.mk hli hsp
    have hnb : ∀ i, nb i = E.jD T (b i : W.DD T) := fun i => Basis.mk_apply _ _ i
    have hlow := GlobalTheory.Sandwich.lower tb inclR φR hA _ _ hx m nb
      (Matrix.of fun i j => E.io (U i j)) (by
        intro i
        have := congrArg (E.jD T) (hU i)
        rw [hj, jD_smulA, map_pow, map_pow] at this
        simp only [E.jD_φ] at this
        simp only [hnb]
        exact this)
    choose cc hcc using hlow
    have hall : ∀ w : TW RA T, ∃ c : Fin (Module.finrank O ↥T.L.T) → RA,
        inclR (E.io W.X) ^ m • TWincl inclR T w = ∑ j, inclR (c j) • nb j := by
      intro w
      let ta := Algebra.TensorProduct.basis RA tb
      refine ⟨fun j => ∑ k, ta.repr w k * cc k j, ?_⟩
      have hk : ∀ (a : RA) k, TWincl inclR T (a • ta k) = inclR a • ((1 : RW) ⊗ₜ[O] tb k) := by
        intro a k
        simp [ta, TWincl, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul']
      conv_lhs => rw [← ta.sum_repr w]
      simp only [map_sum, hk, Finset.smul_sum, Finset.sum_smul, map_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_comm, hcc k, Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [smul_smul]
    rintro y ⟨w, hw⟩
    obtain ⟨c, hc⟩ := hall w
    obtain ⟨e, he⟩ := hexpE (W.X ^ m • y)
    have h3 : ∑ j, E.ioE (e j) • nb j = ∑ j, inclR (c j) • nb j := by
      rw [← hc, hw, ← map_pow, ← map_pow, ← jD_smulA, he, hjE]
      simp only [hnb]
    have h4 : ∀ j, E.ioE (e j) = inclR (c j) := fun j =>
      (Fintype.linearIndependent_iffₛ.mp nb.linearIndependent) _ _ h3 j
    choose a ha using fun j => hE (e j) ⟨c j, (h4 j).symm⟩
    rw [he]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [← ha j, algebraMap_smul]
    exact S.smul_mem _ (b j).2

theorem compare
    (hA : ∀ (p q : Type) [Fintype p] [Fintype q] (Z : Matrix p q RW) (P : Matrix p p RA)
      (P' : Matrix q q RA) (Y : Matrix p q RA),
      Z.map φR = P.map inclR * Z * P'.map inclR + Y.map inclR → ∀ a b, Z a b ∈ Set.range inclR)
    (hφ : ∀ a, inclR (E.io (W.φA a)) = φR (inclR (E.io a)))
    (hE : ∀ x : W.EE, (∃ y, inclR y = E.ioE x) → ∃ a : LetA O n, algebraMap _ W.EE a = x)
    (T : LocLat G Qp LL O) [Nontrivial O] (hT : IsCrys PD T.ρ)
    (hb : Nonempty (Basis (Fin (Module.finrank O ↥T.L.T)) (LetA O n) ↥(W.N T)))
    (S : Submodule (LetA O n) (W.DD T)) (hS : FreeA W T S)
    (hB : IsBaseChange W.EE S.subtype)
    (hS1 : ∀ x ∈ S, ∃ k : ℕ, W.Q ^ k • W.φD T x ∈ S)
    (hS2 : ∀ y ∈ S, ∃ k : ℕ, W.Q ^ k • y ∈ φspan W T S) :
    ∃ a : ℕ, (∀ x ∈ S, W.X ^ a • x ∈ W.N T) ∧ ∀ x ∈ W.N T, W.X ^ a • x ∈ S := by
  have : Nontrivial W.EE := W.EE_inj.nontrivial
  obtain ⟨b⟩ := hb
  obtain ⟨b₁⟩ := basis_rank T S hS hB
  obtain ⟨m, h1, h2⟩ := sand_of E hA hφ hE T (W.N T) b (W.N_base T hT) (W.N_φ T) (W.N_φinv T)
  obtain ⟨m', h1', h2'⟩ := sand_of E hA hφ hE T S b₁ hB hS1 hS2
  refine ⟨m + m', fun x hx => ?_, fun x hx => ?_⟩
  · rw [pow_add, mul_smul]
    exact h2 _ (h1' x hx)
  · rw [add_comm, pow_add, mul_smul]
    exact h2' _ (h1 x hx)

end Generic

set_option maxHeartbeats 1000000 in

theorem main : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ N₁ : Submodule (AA K LL) (W.DD T), FreeA W T N₁ → IsBaseChange W.EE N₁.subtype → (∀ x ∈ N₁, ∃ k : ℕ, W.Q ^ k • W.φD T x ∈ N₁) → (∀ y ∈ N₁, ∃ k : ℕ, W.Q ^ k • y ∈ φspan W T N₁) → ∃ a : ℕ, (∀ x ∈ N₁, W.X ^ a • x ∈ W.N T) ∧ ∀ x ∈ W.N T, W.X ^ a • x ∈ N₁ := by
  intro D HW F l _ K s LL h
  have hio := GlobalTheory.NL.IoXQ.main D HW F l K s LL h
  exact fun T hT N₁ h1 h2 h3 h4 => compare ((F l).E K s LL h).tie
    (GlobalTheory.FrobIntegralCoeff.frobenius_integrality_coeff l LL) hio.2.2.2.2.1 hio.2.2.2.2.2.1 T hT
    (GlobalTheory.NL.N_basis D HW F l K s LL h T hT) N₁ h1 h2 h3 h4

end GlobalTheory.NL.InvX
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachFrobeniusFlatCrystalline
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

noncomputable section

namespace GlobalTheory.NL.PhiFlat

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem φD_smulA (T : LocLat G Qp LL O) (a : LetA O n) (y : W.DD T) :
    W.φD T (a • y) = W.φA a • W.φD T y := by
  rw [← algebraMap_smul W.EE a y, W.φD_smul, W.φE_ext, algebraMap_smul]
  rfl

theorem span_φ (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) {r : ℕ}
    (bN : Module.Basis (Fin r) (LetA O n) ↥(W.N T)) (hQ : IsUnit (algebraMap (LetA O n) W.EE W.Q)) :
    Submodule.span W.EE (Set.range fun j => W.φD T (bN j)) = ⊤ := by
  set S := Submodule.span W.EE (Set.range fun j => W.φD T (bN j)) with hS
  have hA : Submodule.span (LetA O n) (W.φD T '' (W.N T : Set (W.DD T))) ≤ S.restrictScalars (LetA O n) := by
    rw [Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    have hy' : y = ∑ m, bN.repr ⟨y, hy⟩ m • (bN m : W.DD T) := by
      have h0 := congrArg Subtype.val (bN.sum_repr ⟨y, hy⟩)
      rw [Submodule.coe_sum] at h0
      simp only [Submodule.coe_smul] at h0
      exact h0.symm
    rw [hy', map_sum]
    refine Submodule.sum_mem _ fun m _ => ?_
    rw [φD_smulA, ← algebraMap_smul W.EE, Submodule.restrictScalars_mem]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self m))
  have hb : ∀ j, (bN j : W.DD T) ∈ S := by
    intro j
    obtain ⟨k, hk⟩ := W.N_φinv T (bN j) (bN j).2
    change W.Q ^ k • (bN j : W.DD T) ∈ _ at hk
    have h1 := hA hk
    rw [Submodule.restrictScalars_mem] at h1
    obtain ⟨u, hu⟩ := hQ.pow k
    have h2 : (bN j : W.DD T) = ((u⁻¹ : W.EEˣ) : W.EE) • (W.Q ^ k • (bN j : W.DD T)) := by
      rw [← algebraMap_smul W.EE (W.Q ^ k), smul_smul, map_pow, ← hu, Units.inv_mul, one_smul]
    rw [h2]
    exact S.smul_mem _ h1
  let bD : Module.Basis (Fin r) W.EE (W.DD T) := (W.N_base T hT).basis bN
  have hbD : ∀ j, bD j = (bN j : W.DD T) := fun j => by simp [bD, IsBaseChange.basis_apply]
  rw [eq_top_iff, ← bD.span_eq, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  rw [hbD]
  exact hb j

theorem phi_flat (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) {r : ℕ}
    (bN : Module.Basis (Fin r) (LetA O n) ↥(W.N T)) (hQ : IsUnit (algebraMap (LetA O n) W.EE W.Q))
    [Nontrivial W.EE] (hr : Module.finrank W.EE (W.DD T) = r) (l : ℕ)
    (hφ₀ : ∀ w : Fin l → PowerSeries O, ∑ j : Fin l, (1 + PowerSeries.X) ^ (j : ℕ) * W.φ₀ (w j) = 0 → w = 0)
    (z : Fin l → W.DD T) (hz : ∀ j, z j ∈ W.N T)
    (hsum : ∑ j : Fin l, (fun _ => ((1 : PowerSeries O) + PowerSeries.X) ^ (j : ℕ) : LetA O n) • W.φD T (z j) = 0) :
    ∀ j, z j = 0 := by
  have hsp := span_φ W T hT bN hQ
  let c : Module.Basis (Fin r) W.EE (W.DD T) :=
    basisOfTopLeSpanOfCardEqFinrank (fun j => W.φD T (bN j)) hsp.ge (by rw [hr, Fintype.card_fin])
  have hli : LinearIndependent W.EE (fun j => W.φD T (bN j)) := by
    have := c.linearIndependent
    rwa [coe_basisOfTopLeSpanOfCardEqFinrank] at this
  set a : Fin l → Fin r → LetA O n := fun j m => bN.repr ⟨z j, hz j⟩ m with ha
  have hzj : ∀ j, z j = ∑ m, a j m • (bN m : W.DD T) := by
    intro j
    have h0 := congrArg Subtype.val (bN.sum_repr ⟨z j, hz j⟩)
    rw [Submodule.coe_sum] at h0
    simp only [Submodule.coe_smul] at h0
    exact h0.symm
  set e : Fin l → LetA O n := fun j => fun _ => ((1 : PowerSeries O) + PowerSeries.X) ^ (j : ℕ) with he
  have hexp : ∑ m, algebraMap (LetA O n) W.EE (∑ j, e j * W.φA (a j m)) • W.φD T (bN m) = 0 := by
    rw [← hsum]
    simp_rw [algebraMap_smul, hzj, map_sum, φD_smulA, Finset.smul_sum, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm
  have hc : ∀ m, ∑ j, e j * W.φA (a j m) = 0 := by
    intro m
    have := Fintype.linearIndependent_iff.1 hli _ hexp m
    exact W.EE_inj (by rw [this, map_zero])
  have hzero : ∀ j m, a j m = 0 := by
    intro j m
    funext k
    have h1 := congrFun (hc m) (k + 1)
    simp only [Finset.sum_apply, Pi.mul_apply, he, LocWach.φA, letφ, AlgHom.pi_apply, AlgHom.comp_apply,
      Pi.evalAlgHom_apply, add_sub_cancel_right, Pi.zero_apply] at h1
    exact congrFun (hφ₀ (fun j => a j m k) h1) j
  intro j
  rw [hzj j]
  simp [hzero]

end Generic

end GlobalTheory.NL.PhiFlat

namespace GlobalTheory.NL.PhiFlat

set_option maxHeartbeats 1600000 in

theorem main : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ z : Fin l → W.DD T, (∀ j, z j ∈ W.N T) → ∑ j : Fin l, (fun _ => ((1 : PowerSeries ↥(OL LL)) + PowerSeries.X) ^ (j : ℕ) : AA K LL) • W.φD T (z j) = 0 → ∀ j, z j = 0 := by
  intro D HW F l _ K s LL h W T hT z hz hsum
  obtain ⟨bN⟩ := GlobalTheory.NL.N_basis D HW F l K s LL h T hT
  have hQ : IsUnit (algebraMap (AA K LL) W.EE W.Q) := by
    have := ((GlobalTheory.NL.IoXQ.main D HW F l K s LL h).2.2.2.2.2.2 0).2
    rw [pow_zero, AlgHom.one_apply] at this
    exact this
  obtain ⟨χ, -, hφ, -⟩ := GlobalTheory.NL.CycRing.rings_cyclotomic D HW l K s LL h
  obtain ⟨hdvr, hcpl, hnu⟩ := GlobalTheory.FinExtIntegers.dvr_complete LL
  have hl0 : ((l : ℕ) : ↥(OL LL)) ≠ 0 := by
    intro h0
    have := congrArg (fun x : ↥(OL LL) => (x : ↥LL.1)) h0
    simp [(Fact.out : l.Prime).ne_zero] at this
  haveI : Nontrivial W.EE :=
    ⟨⟨algebraMap (AA K LL) W.EE 0, algebraMap (AA K LL) W.EE 1, fun h0 => zero_ne_one (W.EE_inj h0)⟩⟩
  refine GlobalTheory.NL.PhiFlat.phi_flat W T hT bN hQ (W.DD_free T).2 l ?_ z hz hsum
  intro w hw
  obtain ⟨y, -, huniq⟩ := GlobalTheory.Cyc.phi_free l (↥(OL LL)) hl0 hnu 0
  rw [hφ] at hw
  have e1 := huniq w hw.symm
  have e2 := huniq 0 (by simp)
  rw [e1, e2]

end GlobalTheory.NL.PhiFlat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WittVectorMapBreuilKisinEvEq
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem wmap_ev_eq : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (O : Type) [CommRing O] [IsDomain O]
    [CharP O l] [PerfectRing O l] (ψ ψ' : OCb l →+* O), ψ bk.flat ≠ 0 →
    IsAdicComplete (Ideal.span {ψ bk.flat}) O →
    (∀ s : bk.S, ψ ((bk.ev s).coeff 0) = ψ' ((bk.ev s).coeff 0)) →
    ∀ s : bk.S, WittVector.map ψ (bk.ev s) = WittVector.map ψ' (bk.ev s) := by
  intro l _ K bk O _ _ _ _ ψ ψ' h0 hc h s
  have hval : ∀ y : Fq l bk.a, ψ (Fq.val l bk.a y) = ψ' (Fq.val l bk.a y) := fun y => by
    have := h (C (WittVector.teichmuller l y))
    rwa [bk.ev_C, wA_teich, WittVector.teichmuller_coeff_zero] at this
  have hflat : ψ bk.flat = ψ' bk.flat := by
    have := h X
    rwa [bk.ev_X, WittVector.teichmuller_coeff_zero] at this
  have hX : ((WittVector.map ψ).comp bk.ev) X = WittVector.teichmuller l (ψ bk.flat) := by
    rw [RingHom.comp_apply, bk.ev_X, WittVector.map_teichmuller]
  have hcomp := (GlobalTheory.T.wittVector_teichmuller_isAdicComplete_of_perfect l O (ψ bk.flat) h0 hc).1
  refine RingHom.congr_fun (ringHom_ext_of_sep ((WittVector.map ψ).comp bk.ev) ((WittVector.map ψ').comp bk.ev)
    (fun w => ?_) ?_ fun x hx => ?_) s
  · simp only [RingHom.comp_apply, bk.ev_C]
    refine WittVector.ext fun n => ?_
    simp only [wA, AlgHom.coe_mk, WittVector.map_coeff]
    exact hval _
  · rw [hX, RingHom.comp_apply, bk.ev_X, WittVector.map_teichmuller, hflat]
  · rw [hX] at hx
    refine IsHausdorff.haus' (I := Ideal.span {WittVector.teichmuller l (ψ bk.flat)}) x fun n => ?_
    simp only [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
    exact Ideal.mem_span_singleton.2 (hx n)

end GlobalTheory.BSP
end
end

