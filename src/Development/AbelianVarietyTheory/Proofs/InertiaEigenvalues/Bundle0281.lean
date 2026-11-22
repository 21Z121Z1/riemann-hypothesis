import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeOfSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0272
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0259
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0039
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0216
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0205
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0224
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0262
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0053
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InfinitelyManyPrimesInRayClass
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0219
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0245
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0223
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0264

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrameOfTorsionInvariants
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct

namespace GlobalTheory.RedFun

theorem exists_invariant_basis {F₀ F R M D : Type} [Field F₀] [Field F] [CommRing R] [AddCommGroup M] [Module R M]
    [Fintype D] (κ : F →+* R) (ι : F₀ →+* F) (σ : D → (F →+* F)) (t : D → (M →+ M)) (V : AddSubgroup M)
    (hV : ∀ c, ∀ y ∈ V, κ c • y ∈ V) {m : ℕ} (u : Fin m → M)
    (hu : ∀ y ∈ V, ∃ c : Fin m → F, y = ∑ j, κ (c j) • u j) (hσ : Function.Injective σ)
    (hsl : ∀ d c y, t d (κ c • y) = κ (σ d c) • t d y) (hst : ∀ d, ∀ y ∈ V, t d y ∈ V)
    (hav : ∀ d, ∀ y ∈ V, t d (∑ d', t d' y) = ∑ d', t d' y) (hid : ∃ d, ∀ y ∈ V, t d y = y)
    (hfix : ∀ c, (∀ d, σ d c = c) → ∃ c₀, ι c₀ = c) :
    ∃ s, s ≤ m ∧ ∃ w : Fin s → M, (∀ j, w j ∈ V) ∧ (∀ j d, t d (w j) = w j) ∧
      (∀ c : Fin s → F, ∑ j, κ (c j) • w j = 0 → c = 0) ∧
      (∀ y ∈ V, ∃ c : Fin s → F, y = ∑ j, κ (c j) • w j) ∧
      (∀ y ∈ V, (∀ d, t d y = y) → ∃ c : Fin s → F₀, y = ∑ j, κ (ι (c j)) • w j) := by
  classical
  let : Module F M := Module.compHom M κ
  have hs : ∀ (c : F) (y : M), c • y = κ c • y := fun _ _ => rfl
  let V' : Submodule F M := { V with smul_mem' := fun c y hy => hV c y hy }
  have h1 := GlobalTheory.stable_le_span_invariants_of_semilinear_family F M D σ t V' hσ (fun d c y _ => hsl d c y)
    hst hav hid
  obtain ⟨b, hb, hsp, hli⟩ := exists_linearIndependent F {y | y ∈ V' ∧ ∀ d, t d y = y}
  have hle : V' ≤ Submodule.span F (Set.range u) := by
    intro y hy
    obtain ⟨c, rfl⟩ := hu y hy
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ (c j) (Submodule.subset_span ⟨j, rfl⟩)
  have hbu : Set.range ((↑) : b → M) ≤ Submodule.span F (Set.range u) := by
    rintro _ ⟨x, rfl⟩
    exact hle (hb x.2).1
  have : Finite b := by
    have : Module.Finite F (Submodule.span F (Set.range u)) := Module.Finite.span_of_finite F (Set.finite_range u)
    have h0 : LinearIndependent F fun x : b => (⟨x.1, hbu ⟨x, rfl⟩⟩ : Submodule.span F (Set.range u)) :=
      LinearIndependent.of_comp (Submodule.subtype _) hli
    exact h0.finite
  have : Fintype b := Fintype.ofFinite b
  have hc := (linearIndependent_le_span_aux' _ hli (Set.range u) hbu).trans (Fintype.card_range_le u)
  rw [Fintype.card_fin] at hc
  let e := (Fintype.equivFin b).symm
  have hli' : LinearIndependent F (fun j => (e j : M)) := hli.comp e e.injective
  have hind : ∀ c : Fin (Fintype.card b) → F, ∑ j, κ (c j) • (e j : M) = 0 → c = 0 := fun c hc =>
    funext (Fintype.linearIndependent_iff.1 hli' c hc)
  have hgen : ∀ y ∈ V, ∃ c : Fin (Fintype.card b) → F, y = ∑ j, κ (c j) • (e j : M) := by
    intro y hy
    have h2 : y ∈ Submodule.span F (Set.range fun j => (e j : M)) := by
      have h3 : (Set.range fun j => (e j : M)) = b := by
        ext x
        constructor
        · rintro ⟨j, rfl⟩; exact (e j).2
        · intro hx; exact ⟨e.symm ⟨x, hx⟩, by simp⟩
      rw [h3, hsp]
      exact h1 hy
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).1 h2
    exact ⟨c, hc.symm⟩
  refine ⟨_, hc, fun j => e j, fun j => (hb (e j).2).1, fun j => (hb (e j).2).2, hind, hgen, ?_⟩
  intro y hy hinv
  obtain ⟨c, rfl⟩ := hgen y hy
  have h4 : ∀ j d, σ d (c j) = c j := by
    intro j d
    have h5 := hinv d
    rw [map_sum] at h5
    simp only [hsl, fun j => (hb (e j).2).2 d] at h5
    have h6 := hind (fun j => σ d (c j) - c j) (by
      simp only [map_sub, sub_smul, Finset.sum_sub_distrib, h5, sub_self])
    exact sub_eq_zero.1 (congrFun h6 j)
  choose c₀ hc₀ using fun j => hfix (c j) (h4 j)
  exact ⟨c₀, by simp only [hc₀]⟩

theorem exists_frame_of_invariants : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n) {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA] [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA} (E : EtTie W RA RW inclR φR gR πA) {k : Type} [Field k] [Algebra O k] {Rk : Type} [CommRing Rk] [Algebra k Rk] [Algebra O Rk] [IsScalarTower O k Rk] (ρ : RW →ₐ[O] Rk) (lam : O) (κ : k⸨X⸩ →+* Rk) (a : G → (Rk →ₐ[k] Rk)) (ι : k⸨X⸩ →+* k⸨X⸩) (σ : {δ // δ ∈ W.DelF} → (k⸨X⸩ →+* k⸨X⸩)), IsRed E ρ (k := k) lam κ → IsDel E ρ κ a ι σ → ∀ (T : LocLat G Qp LL O) (A : Ob k G) (q : ↥T.L.T →ₗ[O] (Fin A.m → k)), Onto T A q → ∀ i, (∃ u : Fin A.m → W.DD T, ∀ x, ∃ c : Fin A.m → k⸨X⸩, eps E ρ i • J E ρ T q x = ∑ j, κ (c j) • eps E ρ i • J E ρ T q (u j)) → ∃ β : Vc k A.m →+ Rk ⊗[k] (Fin A.m → k), IsFrame (κ.comp ι) (eps E ρ i) β ∧ ∀ y, (∃ x, β x = y) ↔ ∃ x : ↥(DΔ W T), y = eps E ρ i • J E ρ T q x := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL O _ _ _ _ _ v n W RA RW _ _ _ _ inclR φR gR πA
    E k _ _ Rk _ _ _ _ ρ lam κ a ι σ hR hD T A q hq i hu
  classical
  obtain ⟨u, hu⟩ := hu
  set ε := eps E ρ i with hε
  have hεε : ε * ε = ε := eps_idem E ρ i
  choose g hg using fun δ : {δ // δ ∈ W.DelF} => W.resΓ_onto δ.1
  let f : W.DD T →+ Rk ⊗[k] (Fin A.m → k) := (DistribSMul.toAddMonoidHom _ ε).comp (J E ρ T q)
  have hf : ∀ x, f x = ε • J E ρ T q x := fun _ => rfl
  let t : {δ // δ ∈ W.DelF} → (Rk ⊗[k] (Fin A.m → k) →+ Rk ⊗[k] (Fin A.m → k)) :=
    fun δ => (Act a A (g δ)).toAddMonoidHom
  have ht : ∀ δ x, t δ (f x) = f (W.γD T δ.1 x) := by
    intro δ x
    change Act a A (g δ) (ε • J E ρ T q x) = _
    rw [Act_smul, hD.a_eps, ← J_act E ρ hD.a_ρ T A q hq, hg, hf]
  have hsum : ∀ x, ∑ δ, t δ (f x) = f (∑ δ ∈ W.DelF, W.γD T δ x) := by
    intro x
    simp only [ht]
    rw [map_sum, Finset.sum_coe_sort W.DelF (fun δ => f (W.γD T δ x))]
  have hinv : ∀ x ∈ DΔ W T, ∀ δ, t δ (f x) = f x := by
    intro x hx δ
    rw [ht, hx δ.1 δ.2]
  have hV : ∀ c, ∀ y ∈ f.range, κ c • y ∈ f.range := by
    rintro c _ ⟨x, rfl⟩
    obtain ⟨e, he⟩ := hR.κ_of i c
    refine ⟨e • x, ?_⟩
    rw [hf, hf, J_smul, smul_smul, smul_smul, ← he, mul_comm]
  have hsl : ∀ d c y, t d (κ c • y) = κ (σ d c) • t d y := by
    intro d c y
    change Act a A (g d) (κ c • y) = κ (σ d c) • Act a A (g d) y
    rw [Act_smul, hD.a_κ _ d (hg d)]
  obtain ⟨s, hs, w, hwV, hwi, hind, hgen, hgen₀⟩ := exists_invariant_basis κ ι σ t f.range hV
    (fun j => f (u j)) (by rintro _ ⟨x, rfl⟩; exact hu x) hD.σ_inj hsl
    (by rintro d _ ⟨x, rfl⟩; exact ⟨_, (ht d x).symm⟩)
    (by rintro d _ ⟨x, rfl⟩; rw [hsum]; exact hinv _ (sum_mem_DΔ T x) d)
    ⟨⟨1, (W.DelF_def 1).2 ⟨1, one_pos, one_pow 1⟩⟩, by rintro _ ⟨x, rfl⟩; rw [ht, W.γD_one]⟩
    (fun c => (hD.σ_fix c).1)
  have hspan : ∀ y : Fin A.m → k, ε ⊗ₜ[k] y ∈ Submodule.span Rk (Set.range w) := by
    intro y
    obtain ⟨x, rfl⟩ := hq.1 y
    have key : ∀ z ∈ Submodule.span Rk (Set.range (J E ρ T q)), ε • z ∈ Submodule.span Rk (Set.range w) := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨x, rfl⟩ := hz
        obtain ⟨c, hc⟩ := hgen _ ⟨x, rfl⟩
        rw [← hf, hc]
        exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
      | zero => rw [smul_zero]; exact Submodule.zero_mem _
      | add y z _ _ hy hz => rw [smul_add]; exact Submodule.add_mem _ hy hz
      | smul r y _ hy => rw [smul_comm]; exact Submodule.smul_mem _ _ hy
    have := key _ (J_span E ρ T q x)
    rwa [TensorProduct.smul_tmul', smul_eq_mul, mul_one] at this
  have hm : A.m ≤ s := card_le_of_span (eps_idem E ρ i) (hR.eps_ne i) w (Pi.basisFun k (Fin A.m))
    (Pi.basisFun k (Fin A.m)).linearIndependent (fun j => hspan _)
  obtain rfl : s = A.m := le_antisymm hs hm
  let β : Vc k A.m →+ Rk ⊗[k] (Fin A.m → k) :=
    { toFun := fun c => ∑ j, κ (ι (c j)) • w j
      map_zero' := by simp
      map_add' := fun c c' => by simp [add_smul, Finset.sum_add_distrib] }
  have hβ : ∀ c, β c = ∑ j, κ (ι (c j)) • w j := fun _ => rfl
  have hβV : ∀ c, β c ∈ f.range := fun c => by
    rw [hβ]; exact AddSubgroup.sum_mem _ fun j _ => hV _ _ (hwV j)
  refine ⟨β, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro c hc
    have := hind (fun j => ι (c j)) hc
    funext j
    exact (map_eq_zero ι).1 (congrFun this j)
  · intro c x
    simp [hβ, Finset.smul_sum, smul_smul]
  · intro c
    obtain ⟨x, hx⟩ := hβV c
    rw [← hx, hf, smul_smul, hεε]
  · intro y
    refine Submodule.span_mono ?_ (hspan y)
    rintro _ ⟨j, rfl⟩
    refine ⟨Pi.single j 1, ?_⟩
    rw [hβ, Finset.sum_eq_single j]
    · simp
    · intro j' _ hj; simp [hj]
    · simp
  · intro y
    constructor
    · rintro ⟨c, rfl⟩
      obtain ⟨x, hx⟩ := hβV c
      have hi : ∀ δ, t δ (β c) = β c := by
        intro δ
        rw [hβ, map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hsl, hwi, (hD.σ_fix _).2 ⟨_, rfl⟩]
      obtain ⟨r, hr⟩ := hR.res_surj ((W.DelF.card : k)⁻¹)
      refine ⟨⟨r • ∑ δ ∈ W.DelF, W.γD T δ x, ?_⟩, ?_⟩
      · intro δ hδ
        rw [map_smul, sum_mem_DΔ T x δ hδ]
      · change _ = ε • J E ρ T q (r • _)
        rw [J_smulO, smul_comm, ← hf, ← hsum, hx, hr, algebraMap_smul]
        simp only [hi, Finset.sum_const, Finset.card_univ, Fintype.card_coe]
        rw [← Nat.cast_smul_eq_nsmul k, smul_smul, inv_mul_cancel₀ hD.card_ne, one_smul]
    · rintro ⟨x, rfl⟩
      obtain ⟨c, hc⟩ := hgen₀ _ ⟨x.1, rfl⟩ (hinv x.1 x.2)
      exact ⟨c, hc.symm⟩

end GlobalTheory.RedFun
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralDualFunctional
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section
namespace GlobalTheory.IntDual

theorem lattice_basis (l : ℕ) [Fact l.Prime] (LL : Type) [Field LL] [Algebra ℚ_[l] LL]
    [FiniteDimensional ℚ_[l] LL] :
    ∃ (n : ℕ) (b : Basis (Fin n) ℚ_[l] LL),
      (∀ i, ((algebraMap ℚ_[l] LL).comp (algebraMap ℤ_[l] ℚ_[l])).IsIntegralElem (b i)) ∧
      ∀ x : LL, ((algebraMap ℚ_[l] LL).comp (algebraMap ℤ_[l] ℚ_[l])).IsIntegralElem x →
        ∀ i, ∃ z : ℤ_[l], b.repr x i = (z : ℚ_[l]) := by
  letI : Algebra ℤ_[l] LL := ((algebraMap ℚ_[l] LL).comp (algebraMap ℤ_[l] ℚ_[l])).toAlgebra
  haveI : IsScalarTower ℤ_[l] ℚ_[l] LL := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let S := integralClosure ℤ_[l] LL
  haveI : IsIntegralClosure S ℤ_[l] LL := integralClosure.isIntegralClosure _ _
  haveI : Module.Finite ℤ_[l] S := IsIntegralClosure.finite ℤ_[l] ℚ_[l] LL S
  have hinj : Function.Injective (algebraMap ℤ_[l] LL) := by
    intro a c h
    exact IsFractionRing.injective ℤ_[l] ℚ_[l] ((algebraMap ℚ_[l] LL).injective h)
  haveI : Module.IsTorsionFree ℤ_[l] S := ⟨fun r hr a c hac => by
    have hr0 : algebraMap ℤ_[l] LL r ≠ 0 := by
      intro h0; exact hr.ne_zero (hinj (h0.trans (map_zero _).symm))
    apply Subtype.ext
    have h1 := congrArg (fun s : S => (s : LL)) hac
    simp only [Subalgebra.coe_smul, Algebra.smul_def] at h1
    exact mul_left_cancel₀ hr0 h1⟩
  haveI : Module.Free ℤ_[l] S := Module.free_of_finite_type_torsion_free'
  haveI : IsLocalization (Algebra.algebraMapSubmonoid S (nonZeroDivisors ℤ_[l])) LL :=
    IsIntegralClosure.isLocalization ℤ_[l] ℚ_[l] LL S
  let bO := (Module.Free.chooseBasis ℤ_[l] S).reindex (Fintype.equivFin _)
  let b := bO.localizationLocalization ℚ_[l] (nonZeroDivisors ℤ_[l]) LL
  have hb : ∀ i, b i = (bO i : LL) := fun i => Module.Basis.localizationLocalization_apply _ _ _ _ i
  refine ⟨_, b, fun i => ?_, fun x hx i => ?_⟩
  · rw [hb]; exact (bO i).2
  · have := bO.localizationLocalization_repr_algebraMap ℚ_[l] (nonZeroDivisors ℤ_[l]) LL ⟨x, hx⟩ i
    exact ⟨bO.repr ⟨x, hx⟩ i, this⟩

theorem intDual_coef : ∀ (l : ℕ) [Fact l.Prime] (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL]
    (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O →
    ∃ (lam : LL →ₗ[ℚ_[l]] ℚ_[l]) (n : ℕ) (e f : Fin n → O),
      (∀ z : ℤ_[l], ∃ o : O, algebraMap O LL o = algebraMap ℚ_[l] LL (z : ℚ_[l])) ∧
      (∀ o : O, ∃ z : ℤ_[l], lam (algebraMap O LL o) = (z : ℚ_[l])) ∧
      (∀ x : LL, x = ∑ i, lam (algebraMap O LL (f i) * x) • algebraMap O LL (e i)) := by
  intro l _ LL _ _ _ O _ _ hO
  have H := GlobalTheory.T.coefficient_ring_integers_compact_adic_properties l LL O hO
  obtain ⟨⟨hdom, hdvr, hfrac⟩, hfd, -, -, -⟩ := hO
  haveI := hdom
  haveI := hdvr
  haveI := hfrac
  haveI := hfd
  have hmem := H.1
  obtain ⟨n, b, hbint, hcoord⟩ := lattice_basis l LL
  let ι := algebraMap O LL
  have hιinj : Function.Injective ι := IsFractionRing.injective O LL
  let Tr := Algebra.trace ℚ_[l] LL
  let B := Algebra.traceForm ℚ_[l] LL
  have hB : B.Nondegenerate := traceForm_nondegenerate ℚ_[l] LL
  let f' := B.dualBasis hB b
  have hcoef : ∀ x i, Tr (f' i * x) = b.repr x i := by
    intro x i
    conv_lhs => rw [← b.sum_repr x]
    rw [Finset.mul_sum, map_sum]
    have : ∀ j, Tr (f' i * (b.repr x j • b j)) = b.repr x j * (if j = i then 1 else 0) := by
      intro j
      rw [mul_smul_comm, map_smul, smul_eq_mul, ← LinearMap.BilinForm.apply_dualBasis_left hB b i j]
      rfl
    simp_rw [this, mul_ite, mul_one, mul_zero]
    simp

  let Zs : Subring ℚ_[l] := (algebraMap ℤ_[l] ℚ_[l]).range
  have hZ : ∀ q : ℚ_[l], q ∈ Zs ↔ ∃ z : ℤ_[l], q = (z : ℚ_[l]) := by
    intro q; constructor
    · rintro ⟨z, hz⟩; exact ⟨z, hz.symm⟩
    · rintro ⟨z, hz⟩; exact ⟨z, hz.symm⟩
  have hintO : ∀ o : O, ((algebraMap ℚ_[l] LL).comp (algebraMap ℤ_[l] ℚ_[l])).IsIntegralElem (ι o) :=
    fun o => (hmem (ι o)).1 ⟨o, rfl⟩
  have hf'M : ∀ i (s : O), Tr (f' i * ι s) ∈ Zs := by
    intro i s
    obtain ⟨z, hz⟩ := hcoord (ι s) (hintO s) i
    rw [hcoef, hZ]; exact ⟨z, hz⟩
  obtain ⟨⟨c, hc⟩, hcint⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors O)
    (Finset.univ : Finset (Fin n)) f'
  let D := ι c
  have hD : D ≠ 0 := by
    intro h0
    exact nonZeroDivisors.coe_ne_zero ⟨c, hc⟩ (hιinj (h0.trans (map_zero ι).symm))
  have ho : ∀ i, ∃ o : O, ι o = D * f' i := by
    intro i
    obtain ⟨o, ho⟩ := hcint i (Finset.mem_univ i)
    exact ⟨o, by rw [ho, Algebra.smul_def]⟩
  choose o hoD using ho
  let I : Ideal O :=
    { carrier := {a | ∀ s : O, Tr (D⁻¹ * ι a * ι s) ∈ Zs}
      add_mem' := by
        intro a a' ha ha' s
        have e : D⁻¹ * ι (a + a') * ι s = D⁻¹ * ι a * ι s + D⁻¹ * ι a' * ι s := by
          rw [map_add]; ring
        rw [e, map_add]; exact Zs.add_mem (ha s) (ha' s)
      zero_mem' := by
        intro s; simp only [map_zero, mul_zero, zero_mul]; exact Zs.zero_mem
      smul_mem' := by
        intro r a ha s
        have e : D⁻¹ * ι (r • a) * ι s = D⁻¹ * ι a * ι (r * s) := by
          rw [smul_eq_mul, map_mul, map_mul]; ring
        rw [e]; exact ha (r * s) }
  have hoI : ∀ i, o i ∈ I := by
    intro i s
    show Tr (D⁻¹ * ι (o i) * ι s) ∈ Zs
    rw [hoD i, ← mul_assoc, inv_mul_cancel₀ hD, one_mul]
    exact hf'M i s
  let g := Submodule.IsPrincipal.generator I
  have hgI : g ∈ I := Submodule.IsPrincipal.generator_mem I
  have ha : ∀ i, ∃ a : O, a * g = o i := by
    intro i
    have h := hoI i
    rw [← Submodule.IsPrincipal.span_singleton_generator I] at h
    exact Ideal.mem_span_singleton'.1 h
  choose a hag using ha
  let δ := D⁻¹ * ι g
  let lam : LL →ₗ[ℚ_[l]] ℚ_[l] := Tr.comp (LinearMap.mulLeft ℚ_[l] δ)
  have hlam : ∀ y, lam y = Tr (δ * y) := fun y => rfl
  have hδa : ∀ i, δ * ι (a i) = f' i := by
    intro i
    show D⁻¹ * ι g * ι (a i) = f' i
    rw [mul_assoc, ← map_mul, mul_comm g, hag, hoD, ← mul_assoc, inv_mul_cancel₀ hD, one_mul]
  have he : ∀ i, ∃ e : O, ι e = b i := fun i => (hmem (b i)).2 (hbint i)
  choose e he using he
  refine ⟨lam, n, e, a, fun z => ?_, fun y => ?_, fun x => ?_⟩
  · have hz : ((algebraMap ℚ_[l] LL).comp (algebraMap ℤ_[l] ℚ_[l])).IsIntegralElem
        (algebraMap ℚ_[l] LL (z : ℚ_[l])) := RingHom.isIntegralElem_map _
    exact (hmem _).2 hz
  · have h := hgI y
    rw [hZ] at h
    obtain ⟨z, hz⟩ := h
    exact ⟨z, by rw [hlam]; exact hz⟩
  · conv_lhs => rw [← b.sum_repr x]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hlam, ← mul_assoc, hδa, hcoef, he]
end GlobalTheory.IntDual
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMonodromyEqLeadingCoeffBreuilKisinDescent
section
noncomputable section

open PowerSeries GlobalTheory.BK

namespace GlobalTheory.Proof.exists_monodromy_eq_leadingCoeff_breuilKisinDescent

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime]
  [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] {η H : ℕ}

omit [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] in
theorem natCast_l_ne_zero : (l : K) ≠ 0 := by
  rw [← map_natCast (algebraMap ℚ_[l] K)]
  exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)

theorem exists_Mon_eq_Lc_cls : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H) (U : Finset ℤ) (N : ℕ), D.jumps ⊆ U → U ⊆ Finset.Icc (-(η : ℤ)) H → U.card ≤ N + 1 → 1 ≤ η → η < H → 14 * H + (N + 2) * η < l → 10 * H + 2 ≤ l → IsAdicComplete (Ideal.span {(l : O)}) D.Y' → IsHausdorff (Ideal.span {(l : O)}) D.Z → ∀ y ∈ D.Y', ∃ y₀ ∈ D.Y', D.Mon y₀ = D.Lc (D.cls y) := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D U N hU hUI hUc hη1 hηH hl hl2 hC hS y hy
  have hlK : (l : K) ≠ 0 := natCast_l_ne_zero
  set k : ℕ := l - 14 * H with hk
  have hlk : ((l : K) ^ k) ≠ 0 := pow_ne_zero _ hlK
  have hint := GlobalTheory.T.breuilKisin_descent_operator_preserves_lattice O K l e a ι η H D hηH hl2
  have hcomp := GlobalTheory.T.breuilKisin_integrality_computation O K l e a ι η H D hηH hl2
  have hY'Y : ∀ {y : Vec K a ι}, y ∈ D.Y' → y ∈ D.Y := fun h => D.desc.Y'_le_Y η h

  let LcK : Vec K a ι →ₗ[K] D.Pol := D.Lc ∘ₗ D.cls
  have hLc : ∀ v : D.Y', LcK.restrictScalars O (v : Vec K a ι) ∈ D.Z := fun v =>
    hint _ (D.desc.cls_mem_Z (hY'Y v.2))
  let Lc' : D.Y' →ₗ[O] D.Z := ((LcK.restrictScalars O).comp D.Y'.subtype).codRestrict D.Z hLc

  let PK : Vec K a ι →ₗ[K] D.Pol := -((l : K) ^ k)⁻¹ • (D.cls ∘ₗ mulV K a ι (E K l e) ∘ₗ D.zeta)
  have hPK : ∀ y : Vec K a ι, PK y = -((l : K) ^ k)⁻¹ • D.cls (E K l e • D.zeta y) := fun y => by
    simp [PK]
  have hP : ∀ v : D.Y', PK.restrictScalars O (v : Vec K a ι) ∈ D.Z := by
    intro v
    have hv := v.2
    obtain ⟨p, hp, f, hf, hz⟩ := GlobalTheory.T.breuilKisin_zeta_fine_bound_second_basis O K l e a ι η H D hη1 hηH (by omega) v hv
    have hEf : D.cls (E K l e • f) = 0 := by
      rw [PhiMod.cls_eq_zero_iff]
      have h1 := hcomp.2.1 f hf
      have h2 := D.smul_mem_Man (pow_mem (A_le_Rpi l e (E_mem l e (A O K))) (2 * H + 1)) h1
      rwa [smul_smul, ← Ezpow_natCast, ← Ezpow_add, show ((2 * H + 1 : ℕ) : ℤ) + -(2 * H : ℤ) = 1 by push_cast; ring,
        show (1 : ℤ) = ((1 : ℕ) : ℤ) by rfl, Ezpow_natCast, pow_one] at h2
    have hval : PK (v : Vec K a ι) = D.cls (-(E K l e • p)) := by
      rw [hPK, hz, smul_add, smul_comm (E K l e) ((l : K) ^ k) p,
        smul_comm (E K l e) (((l : K) ^ (3 * H))⁻¹) f, map_add, map_smul D.cls ((l : K) ^ k), map_smul D.cls ((l : K) ^ (3 * H))⁻¹, hEf, smul_zero, add_zero,
        smul_smul, neg_mul, inv_mul_cancel₀ hlk, neg_smul, one_smul, map_neg]
    refine D.desc.mem_Z.2 ⟨⟨-(E K l e • p), ?_, hval.symm⟩, fun g => ?_⟩
    · refine neg_mem ?_
      rw [mem_divE, smul_comm]
      exact D.M.smul_mem (EIn l e (A O K)) (D.upper p hp)
    · have h : D.cls (E K l e • D.zeta v) = D.Lc (D.cls v) - D.Mon v := by
        rw [D.Mon_eq, sub_sub_cancel]
      have hinv : D.cls (E K l e • D.zeta v) ∈ D.desc.actPol.invariants := by
        rw [h]
        refine sub_mem (fun g => ?_) (D.desc.Mon_mem_invariants (hY'Y hv).2)
        rw [BKDat.actPol_Lc, D.desc.cls_mem_invariants (hY'Y hv).2 g]
      have h2 : PK v ∈ D.desc.actPol.invariants := by
        rw [hPK]
        exact Submodule.smul_mem _ _ hinv
      exact h2 g
  let P : D.Y' →ₗ[O] D.Z := ((PK.restrictScalars O).comp D.Y'.subtype).codRestrict D.Z hP
  have hLc'apply : ∀ v : D.Y', (Lc' v : D.Pol) = D.Lc (D.cls v) := fun v => rfl
  have hPapply : ∀ v : D.Y', (P v : D.Pol) = PK v := fun v => rfl
  have hsum : ∀ v : D.Y', (((Lc' + (l : O) ^ k • P) v : D.Z) : D.Pol) = D.Mon v := by
    intro v
    rw [LinearMap.add_apply, LinearMap.smul_apply, Submodule.coe_add, Submodule.coe_smul_of_tower,
      hLc'apply, hPapply, hPK, ← algebraMap_smul K ((l : O) ^ k), map_pow, map_natCast, smul_smul, mul_neg,
      mul_inv_cancel₀ hlk, neg_one_smul, D.Mon_eq, sub_eq_add_neg]
  let W : Submodule O D.Z := ((D.Zl.map D.Lc).restrictScalars O).comap D.Z.subtype
  have hW : ∀ z : D.Z, z ∈ W ↔ ∃ w ∈ D.Zl, D.Lc w = z := fun z => Iff.rfl
  have hc : η + (N + 1) * η < k := by
    have : (N + 2) * η = η + (N + 1) * η := by ring
    omega
  have h1 : ∀ v, Lc' v ∈ W ∧ (Lc' + (l : O) ^ k • P) v ∈ W := by
    intro v
    refine ⟨(hW _).2 ⟨D.cls v, D.desc.mem_Zl_of_mem_Z (D.desc.cls_mem_Z (hY'Y v.2)), rfl⟩, (hW _).2 ?_⟩
    rw [hsum]
    obtain ⟨-, w, hw, h⟩ := GlobalTheory.T.monodromy_mem_range_of_invariant_vector O K l e a ι η H D v
      (D.desc.mem_Yl_iff.2 ⟨0, by rw [pow_zero, one_smul]; exact hY'Y v.2⟩)
    exact ⟨w, hw, h⟩
  have h2 : ∀ z : D.Z, (l : O) • z ∈ W → z ∈ W := by
    intro z hz
    obtain ⟨w, hw, h⟩ := (hW _).1 hz
    refine (hW _).2 ⟨((l : K))⁻¹ • w, D.Zl.smul_mem _ hw, ?_⟩
    rw [map_smul, h, Submodule.coe_smul_of_tower, ← algebraMap_smul K (l : O), map_natCast, smul_smul,
      inv_mul_cancel₀ hlK, one_smul]
  have h3 : ∀ z ∈ W, (l : O) ^ (η + (N + 1) * η) • z ∈ LinearMap.range Lc' := by
    intro z hz
    obtain ⟨w, hw, h⟩ := (hW z).1 hz
    obtain ⟨y', hy', hy'eq⟩ := GlobalTheory.T.exists_mem_tameDescent_class_eq_of_pow_mem O K l e a ι η H D U N hU hUI hUc hηH (by omega) hl2 0 w hw
      (by rw [pow_zero, one_smul, h]; exact z.2)
    refine ⟨⟨y', hy'⟩, Subtype.ext ?_⟩
    rw [hLc'apply, Submodule.coe_smul_of_tower, ← algebraMap_smul K ((l : O) ^ (η + (N + 1) * η)), map_pow, map_natCast, ← h, hy'eq,
      zero_add]
  obtain ⟨y₁, hy₁⟩ := GlobalTheory.successive_approximation (l : O) Lc' P W (η + (N + 1) * η) k hc h1 h2 h3 ⟨y, hy⟩
  refine ⟨y₁, y₁.2, ?_⟩
  have := congrArg Subtype.val hy₁
  rw [hsum] at this
  exact this

end GlobalTheory.Proof.exists_monodromy_eq_leadingCoeff_breuilKisinDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimeAbsNormEqOfIrreducibleCyclotomic
section
open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial
open scoped ContDiff Classical

namespace GlobalTheory.CyclotomicPrimes

theorem summable_subset_union_finite {ι : Type} (f : ι → ℝ) (A B C : Set ι) (hB : B.Finite) (h : C ⊆ A ∪ B)
    (hA : Summable fun x : A => f x) : Summable fun x : C => f x := by
  have h1 : Summable (f ∘ ((↑) : ↥(A ∪ B) → ι)) := by
    rw [← Set.union_diff_self]
    exact (HasSum.add_disjoint Set.disjoint_sdiff_right hA.hasSum ((hB.subset Set.diff_subset).summable f).hasSum).summable
  exact h1.comp_injective (i := Set.inclusion h) (Set.inclusion_injective h)

theorem exists_prime_absNorm_eq_of_irreducible_cyclotomic : ∀ (K : Type) [Field K] [NumberField K] (m : ℕ), m.Prime → Irreducible (cyclotomic m K) → ∀ (τ : (ZMod m)ˣ) (S : Set (HeightOneSpectrum (𝓞 K))), S.Finite → ∃ P : HeightOneSpectrum (𝓞 K), P ∉ S ∧ (Ideal.absNorm P.asIdeal).Prime ∧ ((Ideal.absNorm P.asIdeal : ℕ) : ZMod m) = (τ : ZMod m) := by
  classical
  intro K _ _ m hm hirr τ S hS
  have : Fact m.Prime := ⟨hm⟩
  let cl : HeightOneSpectrum (𝓞 K) → (ZMod m)ˣ := fun P =>
    if h : ((Ideal.absNorm P.asIdeal : ℕ) : ZMod m) = 0 then 1 else Units.mk0 _ h
  have hcl : ∀ P, ¬ m ∣ Ideal.absNorm P.asIdeal → (cl P : ZMod m) = (Ideal.absNorm P.asIdeal : ℕ) := by
    intro P hP
    simp only [cl]
    rw [dif_neg (by rwa [ZMod.natCast_eq_zero_iff])]
    rfl
  by_contra hcon
  push Not at hcon
  obtain ⟨Z, hZ, hZ1, hZs⟩ := GlobalTheory.T.exists_entire_sub_one_mul_euler_exp_ne_zero_one K
  refine GlobalTheory.Mem.RayPrimes.not_summable_class (fun P : HeightOneSpectrum (𝓞 K) => Ideal.absNorm P.asIdeal)
    GlobalTheory.Mem.RayPrimes.two_le_absNorm cl
    (fun s hs => ((GlobalTheory.countable_ideal_and_summable_absNorm_rpow K).2 s hs).2) ?_ Z hZ.continuous hZ1 ?_ τ ?_
  · intro χ hχ
    obtain ⟨P, u, hu, hχu⟩ := GlobalTheory.T.exists_prime_norm_cyclotomicChar_ne_one K m hm hirr χ hχ
    have hP : ¬ m ∣ Ideal.absNorm P.asIdeal := by
      rw [← ZMod.natCast_eq_zero_iff, ← hu]; exact u.ne_zero
    refine GlobalTheory.T.exists_continuous_normCharLFunction_ne_zero_one K m hm χ cl hcl ⟨P, hP, ?_⟩
    rwa [show cl P = u from Units.ext ((hcl P hP).trans hu.symm)]
  · intro s hs
    simpa using hZs s (by simpa using hs)
  · have hfin : (S ∪ {P : HeightOneSpectrum (𝓞 K) | Ideal.absNorm P.asIdeal ≤ m}).Finite :=
      hS.union ((Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) m).preimage
        (f := fun P : HeightOneSpectrum (𝓞 K) => P.asIdeal) (fun a _ b _ h => HeightOneSpectrum.ext h))
    refine summable_subset_union_finite (fun P : HeightOneSpectrum (𝓞 K) => ((Ideal.absNorm P.asIdeal : ℕ) : ℝ)⁻¹)
      {P | ¬ (Ideal.absNorm P.asIdeal).Prime} _ {P | cl P = τ} hfin ?_ (GlobalTheory.T.summable_inv_absNorm_primes_of_not_prime_norm K)
    intro P hP
    by_contra hn
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le, not_not] at hn hP
    have hd : ¬ m ∣ Ideal.absNorm P.asIdeal := fun h =>
      hn.2.2.ne ((Nat.prime_dvd_prime_iff_eq hm hn.1).1 h)
    exact hcon P hn.2.1 hn.1 (by rw [← hcl P hd, hP])

end GlobalTheory.CyclotomicPrimes
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixedOfFixedByDeltaGammaLiftsStatement
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fixed_of_fixed_by_delta_gamma_lifts : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (H : LocHW l P) (S : TopSit P) (k : Type) [Field k] [Algebra S.O k] [CharP k l], S.IsRes k → (((S.W H).DelF.card : ℕ) : k) ≠ 0 ∧ ∀ γ : (S.W H).Gam, ((S.W H).χΓ γ : S.O) = 1 + (l : S.O) → ∀ (T : LocLat S.G ℚ_[l] ↥S.LL.1 S.O) (A : Ob k S.G) (q : ↥T.L.T →ₗ[S.O] (Fin A.m → k)), Onto T A q → ∀ t : Fin A.m → k, (∀ g, ((S.W H).resΓ g ∈ (S.W H).DelF ∨ (S.W H).resΓ g = γ) → A.ρ g t = t) → ∀ g, A.ρ g t = t := by
  first | exact @GlobalTheory.RedDense.fixed_of_fixed_lifts | exact GlobalTheory.RedDense.fixed_of_fixed_lifts | (intros; apply GlobalTheory.RedDense.fixed_of_fixed_lifts <;> assumption)
end

