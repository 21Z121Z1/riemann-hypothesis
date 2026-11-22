import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0065
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0099
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0087
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0100
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0064
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0075

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAlgebraMapSubEqSumConjugates
section
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open scoped Pointwise

namespace GlobalTheory

theorem exists_algebraMap_sub_eq_sum_conjugates : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (y : Ω), ∃ (e : E) (s : Finset Ω), (∀ x ∈ s, x ≠ y ∧ ∃ σ : G E Ω, σ y = x) ∧ algebraMap E Ω e - y = ∑ x ∈ s, x := by
  intro E Ω _ _ _ _ _ y
  classical
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI : Normal E Ω := IsAlgClosure.normal E Ω
  have hy : IsIntegral E y := Algebra.IsIntegral.isIntegral y
  set p := minpoly E y with hp
  set q := p.map (algebraMap E Ω) with hq
  have hirr : Irreducible p := minpoly.irreducible hy
  have hmon : p.Monic := minpoly.monic hy
  have hsep : q.Separable := Polynomial.Separable.map (Algebra.IsSeparable.isSeparable E y : p.Separable)
  have hnd : q.roots.Nodup := nodup_roots hsep
  have hspl : q.Splits := IsAlgClosed.splits q
  have hsum : q.nextCoeff = -q.roots.sum := hspl.nextCoeff_eq_neg_sum_roots_of_monic (hmon.map _)
  have hq0 : q ≠ 0 := (hmon.map _).ne_zero
  have hyr : y ∈ q.roots.toFinset := by
    rw [Multiset.mem_toFinset, mem_roots hq0, IsRoot, eval_map_algebraMap]
    exact minpoly.aeval E y
  refine ⟨-p.nextCoeff, q.roots.toFinset.erase y, ?_, ?_⟩
  · intro x hx
    obtain ⟨hxy, hxr⟩ := Finset.mem_erase.mp hx
    refine ⟨hxy, ?_⟩
    have hax : aeval x p = 0 := by
      rw [Multiset.mem_toFinset, mem_roots hq0, IsRoot, eval_map_algebraMap] at hxr
      exact hxr
    have hmx : p = minpoly E x := minpoly.eq_of_irreducible_of_monic hirr hax hmon
    have horb : x ∈ MulAction.orbit (G E Ω) y :=
      (Normal.minpoly_eq_iff_mem_orbit (F := E) Ω).mp (by rw [← hmx])
    obtain ⟨σ, hσ⟩ := horb
    exact ⟨σ, hσ⟩
  · rw [Finset.sum_erase_eq_sub hyr, Finset.sum_eq_multiset_sum, Multiset.toFinset_val,
      Multiset.dedup_eq_self.mpr hnd, Multiset.map_id', map_neg, ← nextCoeff_map_eq, ← hq, hsum, neg_neg]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEigenvectorOfTraceEqAddCharacter
section
namespace GlobalTheory

private lemma exists_char_augmentation_zero_acting_as_one {K Γ V : Type} [Field K] [Group Γ]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (ρ : Representation K Γ V)
    (χ : Γ →* Kˣ) (hs : ρ.IsSemisimpleRepresentation)
    (hno : ∀ v : V, (∀ g, ρ g v = ((χ g : Kˣ) : K) • v) → v = 0) :
    ∃ x : MonoidAlgebra K Γ, MonoidAlgebra.lift K K Γ ((Units.coeHom K).comp χ) x = 0 ∧
      ρ.asAlgebraHom x = 1 := by
  set ε := MonoidAlgebra.lift K K Γ ((Units.coeHom K).comp χ) with hε
  have hsm : IsSemisimpleModule (MonoidAlgebra K Γ) ρ.asModule :=
    (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule ρ).mp hs
  let b := Module.finBasis K V
  let m : Fin (Module.finrank K V) → ρ.asModule := fun i => ρ.asModuleEquiv.symm (b i)
  let P : Submodule (MonoidAlgebra K Γ) (Fin (Module.finrank K V) → ρ.asModule) :=
    Submodule.map (LinearMap.toSpanSingleton (MonoidAlgebra K Γ) _ m)
      (RingHom.ker (ε : MonoidAlgebra K Γ →+* K))
  obtain ⟨C, hC⟩ := exists_isCompl P
  have hm : m ∈ P ⊔ C := by rw [hC.sup_eq_top]; trivial
  obtain ⟨p, hp, c, hc, hpc⟩ := Submodule.mem_sup.mp hm
  have hkill : ∀ x, ε x = 0 → x • c = 0 := by
    intro x hx
    have h1 : x • c ∈ P := by
      have : x • c = x • m - x • p := by rw [← hpc, smul_add, add_sub_cancel_left]
      rw [this]
      exact P.sub_mem (Submodule.mem_map.mpr ⟨x, RingHom.mem_ker.mpr hx,
        LinearMap.toSpanSingleton_apply _ _ _ _⟩) (P.smul_mem x hp)
    have h2 : x • c ∈ P ⊓ C := Submodule.mem_inf.mpr ⟨h1, C.smul_mem x hc⟩
    rwa [hC.inf_eq_bot, Submodule.mem_bot] at h2
  have hc0 : c = 0 := by
    funext i
    have hv := hno (ρ.asModuleEquiv (c i)) fun g => by
      have h := congrFun (hkill (MonoidAlgebra.single g 1 - MonoidAlgebra.single 1 ((χ g : Kˣ) : K))
        (by simp [hε, MonoidAlgebra.lift_single])) i
      change ρ.asModuleEquiv.symm (ρ.asAlgebraHom _ (ρ.asModuleEquiv (c i))) = 0 at h
      rw [LinearEquiv.map_eq_zero_iff, map_sub, Representation.asAlgebraHom_single,
        Representation.asAlgebraHom_single, one_smul, map_one, LinearMap.sub_apply,
        LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at h
      exact h
    simpa using hv
  rw [hc0, add_zero] at hpc
  obtain ⟨y, hy, hym⟩ := Submodule.mem_map.mp (show m ∈ P from hpc ▸ hp)
  refine ⟨y, RingHom.mem_ker.mp hy, b.ext fun i => ?_⟩
  have h := congrFun hym i
  change ρ.asModuleEquiv.symm (ρ.asAlgebraHom y (ρ.asModuleEquiv (ρ.asModuleEquiv.symm (b i)))) =
    ρ.asModuleEquiv.symm (b i) at h
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_eq, LinearEquiv.apply_symm_apply] at h
  simpa using h

private lemma false_of_trace_pow_eq_card_add_one_sub {L ι : Type} [Field L] [CharZero L] [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι L) (h : ∀ n : ℕ, (M ^ n).trace = ((Fintype.card ι : L) + 1) - 0 ^ n) :
    False := by
  set D : L := (Fintype.card ι : L) + 1 with hD
  have hD0 : D ≠ 0 := by rw [hD]; exact Nat.cast_add_one_ne_zero _
  have hpoly : ∀ f : Polynomial L, (Polynomial.aeval M f).trace = D * f.eval 1 - f.eval 0 := by
    intro f
    induction f using Polynomial.induction_on' with
    | add f g hf hg => simp only [map_add, Matrix.trace_add, hf, hg, Polynomial.eval_add]; ring
    | monomial n a =>
      rw [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
        Matrix.trace_smul, h n, Polynomial.eval_monomial, Polynomial.eval_monomial, one_pow,
        smul_eq_mul]
      ring
  set p := M.charpoly with hp
  have hvan : ∀ g : Polynomial L, D * (g * p).eval 1 - (g * p).eval 0 = 0 := by
    intro g
    rw [← hpoly, map_mul, hp, Matrix.aeval_self_charpoly, mul_zero, Matrix.trace_zero]
  have hp1 : p.eval 1 = 0 := by
    have := hvan Polynomial.X
    simp only [Polynomial.eval_mul, Polynomial.eval_X, one_mul, zero_mul, sub_zero] at this
    exact (mul_eq_zero.mp this).resolve_left hD0
  have hp0 : p.eval 0 = 0 := by
    have := hvan 1
    simpa [hp1] using this
  have hpne : p ≠ 0 := (Matrix.charpoly_monic M).ne_zero
  obtain ⟨q, hpq, hq⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hpne 1
  set b := p.rootMultiplicity 1
  have hb : 0 < b := (Polynomial.rootMultiplicity_pos hpne).mpr hp1
  have hcop : IsCoprime ((Polynomial.X - Polynomial.C (1 : L)) ^ b) q :=
    ((Polynomial.irreducible_X_sub_C (1 : L)).coprime_iff_not_dvd.mpr hq).pow_left
  obtain ⟨u, v, huv⟩ := hcop
  have hq0 : q.eval 0 = 0 := by
    have := hp0
    rw [hpq, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C] at this
    exact (mul_eq_zero.mp this).resolve_left (pow_ne_zero _ (by norm_num))
  have he1 : (v * q).eval 1 = 1 := by
    have := congrArg (Polynomial.eval 1) huv
    simpa [Polynomial.eval_mul, zero_pow hb.ne'] using this
  have he0 : (v * q).eval 0 = 0 := by simp [Polynomial.eval_mul, hq0]
  have hidem : (v * q) * (v * q) = v * q - (u * v) * p := by
    rw [hpq]; linear_combination (v * q) * huv
  set E := Polynomial.aeval M (v * q) with hE
  have hEE : E * E = E := by
    rw [hE, ← map_mul, hidem, map_sub, map_mul (Polynomial.aeval M) (u * v) p, hp,
      Matrix.aeval_self_charpoly, mul_zero, sub_zero]
  have htrE : E.trace = D := by rw [hE, hpoly, he1, he0]; ring
  have hid : IsIdempotentElem (Matrix.toLin' E) := by
    unfold IsIdempotentElem
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hEE]
  have htr := (LinearMap.IsIdempotentElem.isProj_range _ hid).trace
  rw [LinearMap.trace_eq_matrix_trace L (Pi.basisFun L ι), LinearMap.toMatrix_eq_toMatrix',
    LinearMap.toMatrix'_toLin', htrE, hD] at htr
  have hle := Submodule.finrank_le (LinearMap.range (Matrix.toLin' E))
  rw [Module.finrank_fintype_fun_eq_card] at hle
  have : Fintype.card ι + 1 = Module.finrank L (LinearMap.range (Matrix.toLin' E)) := by
    exact_mod_cast htr
  omega

theorem _root_.GlobalTheory.exists_eigenvector_of_trace_eq_add_character :
    ∀ (K L Γ V ι : Type) [Field K] [Field L] [CharZero L] [Group Γ] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype ι] [DecidableEq ι] (φ : K →+* L) (ρ : Representation K Γ V) (σ : Γ →* Matrix ι ι L) (χ : Γ →* Kˣ), ρ.IsSemisimpleRepresentation → (∀ g, φ (LinearMap.trace K V (ρ g)) = (σ g).trace + φ ((χ g : Kˣ) : K)) → ∃ v : V, v ≠ 0 ∧ ∀ g, ρ g v = ((χ g : Kˣ) : K) • v := by
  intro K L Γ V ι _ _ _ _ _ _ _ _ _ φ ρ σ χ hs htr
  by_contra hcon
  push_neg at hcon
  have hno : ∀ v : V, (∀ g, ρ g v = ((χ g : Kˣ) : K) • v) → v = 0 := fun v hv => by
    by_contra h0
    obtain ⟨g, hg⟩ := hcon v h0
    exact hg (hv g)
  obtain ⟨x, hx, hρx⟩ := exists_char_augmentation_zero_acting_as_one ρ χ hs hno
  let S : MonoidAlgebra K Γ →+* Matrix ι ι L :=
    MonoidAlgebra.liftNCRingHom ((Matrix.scalar ι).comp φ) σ
      (fun _ _ => Matrix.scalar_commute _ (fun _ => Commute.all _ _) _)
  have hkey : ∀ z : MonoidAlgebra K Γ, φ (LinearMap.trace K V (ρ.asAlgebraHom z)) =
      (S z).trace + φ (MonoidAlgebra.lift K K Γ ((Units.coeHom K).comp χ) z) := by
    intro z
    refine MonoidAlgebra.induction_linear z ?_ ?_ ?_
    · simp
    · intro f g hf hg
      simp only [map_add, Matrix.trace_add, hf, hg]; ring
    · intro g r
      rw [Representation.asAlgebraHom_single, map_smul, smul_eq_mul, map_mul, htr g]
      have hS : S (MonoidAlgebra.single g r) = Matrix.scalar ι (φ r) * σ g := by
        simp [S, MonoidAlgebra.liftNCRingHom, MonoidAlgebra.liftNC_single]
      rw [hS]
      rw [MonoidAlgebra.lift_single, Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul,
        Matrix.trace_smul, smul_eq_mul, smul_eq_mul, map_mul]
      simp only [MonoidHom.coe_comp, Function.comp_apply, Units.coeHom_apply]
      ring
  have hdim := htr 1
  rw [map_one ρ, LinearMap.trace_one, map_natCast, map_one σ, Matrix.trace_one, map_one χ,
    Units.val_one, map_one φ] at hdim
  have hpow : ∀ n : ℕ, ((S x) ^ n).trace = ((Fintype.card ι : L) + 1) - 0 ^ n := by
    intro n
    have h1 := hkey (x ^ n)
    rw [map_pow, hρx, one_pow, LinearMap.trace_one, map_natCast, map_pow, map_pow, hx] at h1
    have h0 : φ ((0 : K) ^ n) = (0 : L) ^ n := by rw [map_pow, map_zero]
    linear_combination hdim - h1 - h0
  exact false_of_trace_pow_eq_card_add_one_sub (S x) hpow

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinsetFixingIffPreservesSubgroupOrbit
section
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

namespace GlobalTheory

theorem orbit_stab_cut_finite (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (H : Subgroup (G E Ω)) (y : Ω) :
    ∃ s : Finset Ω, ∀ σ : G E Ω, (∀ x ∈ s, σ x = x) ↔ ∀ τ ∈ H, ∃ τ' ∈ H, σ (τ y) = τ' y := by
  classical
  haveI : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  have hint : IsIntegral E y := Algebra.IsIntegral.isIntegral y
  set S : Set Ω := {t | ∃ τ ∈ H, τ y = t} with hSdef
  have hS : S.Finite := by
    refine ((minpoly E y).rootSet_finite Ω).subset ?_
    rintro t ⟨τ, -, rfl⟩
    rw [Polynomial.mem_rootSet]
    refine ⟨minpoly.ne_zero hint, ?_⟩
    rw [Polynomial.aeval_algEquiv]
    simp [minpoly.aeval]
  set O := hS.toFinset with hOdef
  have hmemO : ∀ t, t ∈ O ↔ ∃ τ ∈ H, τ y = t := fun t => by simp [O, S]
  set P : Polynomial Ω := ∏ t ∈ O, (X - C t) with hP
  refine ⟨(Finset.range (P.natDegree + 1)).image P.coeff, fun σ => ?_⟩
  have key : (∀ x ∈ (Finset.range (P.natDegree + 1)).image P.coeff, σ x = x) ↔
      P.map (σ : Ω →+* Ω) = P := by
    constructor
    · intro h
      ext n
      rw [coeff_map]
      by_cases hn : n ≤ P.natDegree
      · exact h _ (Finset.mem_image.2 ⟨n, Finset.mem_range.2 (Nat.lt_succ_of_le hn), rfl⟩)
      · rw [coeff_eq_zero_of_natDegree_lt (not_le.1 hn)]; simp
    · intro h x hx
      obtain ⟨n, -, rfl⟩ := Finset.mem_image.1 hx
      have := congrArg (fun p => p.coeff n) h
      simpa [coeff_map] using this
  have hmap : P.map (σ : Ω →+* Ω) = ∏ t ∈ O, (X - C (σ t)) := by
    simp [hP, Polynomial.map_prod]
  rw [key, hmap]
  constructor
  · intro h τ hτ
    have h0 : (∏ t ∈ O, (X - C (σ t))).eval (σ (τ y)) = 0 := by
      rw [eval_prod]
      exact Finset.prod_eq_zero ((hmemO _).2 ⟨τ, hτ, rfl⟩) (by simp)
    rw [h, hP, eval_prod, Finset.prod_eq_zero_iff] at h0
    obtain ⟨t, ht, ht0⟩ := h0
    obtain ⟨τ', hτ', rfl⟩ := (hmemO t).1 ht
    refine ⟨τ', hτ', ?_⟩
    simpa [sub_eq_zero] using ht0
  · intro h
    have hinj : Function.Injective (σ : Ω → Ω) := σ.injective
    have hsub : O.image σ ⊆ O := by
      intro u hu
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hu
      obtain ⟨τ, hτ, rfl⟩ := (hmemO t).1 ht
      obtain ⟨τ', hτ', he⟩ := h τ hτ
      exact (hmemO _).2 ⟨τ', hτ', he.symm⟩
    have heq : O.image σ = O :=
      Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_image_of_injective _ hinj])
    calc ∏ t ∈ O, (X - C (σ t)) = ∏ u ∈ O.image σ, (X - C u) :=
          by
          rw [Finset.prod_image (fun a _ b _ hab => hinj hab)]
      _ = P := by rw [heq]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinsetFixingLeFiniteIndexWeilSubgroup
section
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

namespace GlobalTheory.WeilOpenFin

theorem exists_finset_fix_le : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w), (∀ (σ : G E Ω) (s : Finset Ω), ∃ m : ℕ, 0 < m ∧ ∀ x ∈ s, (σ ^ m) x = x) → (∀ k : ℕ, 0 < k → ∃ ζ : Ω, ∀ σ : Weil h, (σ : G E Ω) ζ = ζ → (k : ℤ) ∣ deg σ) → (∀ M : Subgroup (Ine (F := E) A), IsOpen (M : Set (Ine (F := E) A)) → ∃ s : Finset Ω, ∀ σ : Ine (F := E) A, (∀ x ∈ s, (σ : G E Ω) x = x) → σ ∈ M) → ∀ H : Subgroup (Weil h), H.FiniteIndex → IsOpen {σ : Ine (F := E) A | ineIncl h σ ∈ H} → ∃ s : Finset Ω, ∀ σ : Weil h, (∀ x ∈ s, (σ : G E Ω) x = x) → σ ∈ H := by
  intro E Ω _ _ _ _ _ A w h h1 h2 h3 H hH hopen
  classical

  have hfix : ∀ (g : G E Ω) (t : Finset Ω), (∀ x ∈ t, g x = x) → ∀ n : ℤ, ∀ x ∈ t, (g ^ n) x = x := by
    intro g t hg n x hx
    have hm : g ∈ MulAction.stabilizer (G E Ω) x := by
      rw [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]; exact hg x hx
    have := (MulAction.mem_stabilizer_iff).mp (Subgroup.zpow_mem _ hm n)
    rwa [AlgEquiv.smul_def] at this
  obtain ⟨s₁, hs₁⟩ := h3 (H.comap (ineIncl h)) hopen
  let φ : Weil h := frob h
  obtain ⟨m, hm0, hm⟩ := h1 (φ : G E Ω) s₁
  have hN : H.normalCore.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  set k : ℕ := m * H.normalCore.index with hk
  have hk0 : 0 < k := Nat.mul_pos hm0 (Nat.pos_of_ne_zero hN)
  let ψ : Weil h := φ ^ k
  have hψH : ψ ∈ H := by
    apply Subgroup.normalCore_le
    show φ ^ (m * H.normalCore.index) ∈ H.normalCore
    rw [pow_mul]; exact Subgroup.pow_index_mem _ _
  have hψdeg : deg ψ = k := by simp [ψ, φ]
  have hψfix : ∀ x ∈ s₁, (ψ : G E Ω) x = x := by
    intro x hx
    have := hfix _ s₁ hm (H.normalCore.index : ℤ) x hx
    simpa [ψ, φ, hk, pow_mul] using this
  obtain ⟨ζ, hζ⟩ := h2 k hk0
  refine ⟨insert ζ s₁, fun τ hτ => ?_⟩
  obtain ⟨i, hi⟩ := hζ τ (hτ ζ (Finset.mem_insert_self _ _))
  let ρ : Weil h := τ * ψ ^ (-i)
  have hρdeg : deg ρ = 0 := by
    simp only [ρ, deg_mul, deg_zpow, hψdeg, hi]; ring
  have hρIne : (ρ : G E Ω) ∈ Ine (F := E) A := deg_eq_zero_iff.mp hρdeg
  have hρfix : ∀ x ∈ s₁, (ρ : G E Ω) x = x := by
    intro x hx
    have e1 := hfix _ s₁ hψfix (-i) x hx
    show ((τ : G E Ω) * ((ψ ^ (-i) : Weil h) : G E Ω)) x = x
    rw [AlgEquiv.mul_apply, Subgroup.coe_zpow, e1]
    exact hτ x (Finset.mem_insert_of_mem hx)
  have hρM := hs₁ ⟨ρ, hρIne⟩ hρfix
  have hρH : ρ ∈ H := by
    have : ineIncl h ⟨ρ, hρIne⟩ ∈ H := hρM
    exact this
  have : τ = ρ * ψ ^ i := by simp [ρ]
  rw [this]
  exact H.mul_mem hρH (H.zpow_mem hψH i)

end GlobalTheory.WeilOpenFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinsetFixingSubsetOpenInertiaSubgroup
section
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

namespace GlobalTheory.WeilDeligne

theorem exists_finset_fix_subset_of_isOpen : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A : ValuationSubring Ω) (M : Subgroup (Ine (F := E) A)),
    IsOpen (M : Set (Ine (F := E) A)) → ∃ s : Finset Ω, ∀ σ : Ine (F := E) A,
      (∀ x ∈ s, (σ : G E Ω) x = x) → σ ∈ M := by
  intro E Ω _ _ _ _ _ A M hM
  obtain ⟨U, hU, hUM⟩ := isOpen_induced_iff.mp hM
  have h1 : (1 : G E Ω) ∈ U := by
    have : (1 : Ine (F := E) A) ∈ (Subtype.val ⁻¹' U) := by rw [hUM]; exact M.one_mem
    simpa using this
  obtain ⟨L, hL, hLU⟩ := (krullTopology_mem_nhds_one_iff E Ω U).mp (hU.mem_nhds h1)
  have hfg : L.toSubalgebra.FG := by
    apply Subalgebra.fg_of_fg_toSubmodule
    exact Module.Finite.iff_fg.mp hL
  obtain ⟨t, ht⟩ := hfg
  refine ⟨t, fun σ hσ => ?_⟩
  have hmem : (σ : G E Ω) ∈ L.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have hx' : x ∈ Algebra.adjoin E (t : Set Ω) := by rw [ht]; exact hx
    have key : Set.EqOn ((σ : G E Ω) : Ω →ₐ[E] Ω) (AlgHom.id E Ω) (Algebra.adjoin E (t : Set Ω)) :=
      AlgHom.eqOn_adjoin_iff.mpr (fun y hy => hσ y hy)
    exact key hx'
  have : σ ∈ (Subtype.val ⁻¹' U : Set (Ine (F := E) A)) := hLU hmem
  rw [hUM] at this
  exact this

end GlobalTheory.WeilDeligne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegerMapIsIntegralUnramifiedInvolutionEx
section
noncomputable section

namespace GlobalTheory.UnitLemma.Unr

open GlobalTheory.UnitLemma Polynomial

theorem intMap_isIntegral_of_unr : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ →
    ∃ φO : K.O →+* K'.O, (∀ x, algebraMap K'.O K'.E (φO x) = φ (algebraMap K.O K.E x)) ∧
      @Algebra.IsIntegral K.O K'.O _ _ φO.toAlgebra := by
  intro K K' d φ hU
  obtain ⟨φO, hφO⟩ := exists_intMap_of_unr hU
  refine ⟨φO, hφO, ?_⟩
  letI : Algebra K.O K'.O := φO.toAlgebra
  obtain ⟨u, hu⟩ := exists_int_basis_of_unr K K' d φ hU
  have hspan : Submodule.span K.O (Set.range u) = ⊤ := by
    refine eq_top_iff.2 fun y _ => ?_
    obtain ⟨a, ha⟩ := hu y
    have hy : y = ∑ i, a i • u i := by
      apply IsFractionRing.injective K'.O K'.E
      rw [ha, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, map_mul]
      change φ (algebraMap K.O K.E (a i)) * _ = algebraMap K'.O K'.E (φO (a i)) * _
      rw [hφO]
    rw [hy]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  haveI : Module.Finite K.O K'.O := ⟨Submodule.fg_def.2 ⟨_, Set.finite_range u, hspan⟩⟩
  exact Algebra.IsIntegral.of_finite K.O K'.O

end GlobalTheory.UnitLemma.Unr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegerSpanningFamilyOfUnramifiedExtStatement
section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integer_spanning_family_of_unramifiedExt : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∃ u : Fin d → K'.O, ∀ y : K'.O, ∃ a : Fin d → K.O, algebraMap K'.O K'.E y = ∑ i, φ (algebraMap K.O K.E (a i)) * algebraMap K'.O K'.E (u i) := by
  first | exact @GlobalTheory.UnitLemma.Unr.exists_int_basis_of_unr | exact GlobalTheory.UnitLemma.Unr.exists_int_basis_of_unr | (intros; apply GlobalTheory.UnitLemma.Unr.exists_int_basis_of_unr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralGLMulDiagOneOfUnitIndicatorLiftNeZStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integralGL_mul_diagOne_of_unitIndicator_lift_ne_zero : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (Z : Gl r F) (μ l : F), ‖μ‖ = 1 → ∀ g : GL (Fin (r + 1)) F, unitG (r + 1) F (act g (GlobalTheory.JR.Step.lift Z μ l)) ≠ 0 → ∃ k ∈ glO (r + 1) F, ∃ s : GL (Fin r) F, g = k * GlobalTheory.JR.Step.emb r F s := by
  first | exact @GlobalTheory.JR.GLift.support_lift | exact GlobalTheory.JR.GLift.support_lift | (intros; apply GlobalTheory.JR.GLift.support_lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsIntegralSmallElementPowSmulStatement
section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isIntegral_smallElement_pow_smul : ∀ (K : UQ) (B : InvAlg K) (a : K.O), K.Small a → ∀ x : B.A, ∃ k : ℕ, IsIntegral K.O ((al K a ^ k) • x) := by
  first | exact @GlobalTheory.UnitLemma.Desc.smul_pow_integral | exact GlobalTheory.UnitLemma.Desc.smul_pow_integral | (intros; apply GlobalTheory.UnitLemma.Desc.smul_pow_integral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPosPowGaloisFixingFinset
section
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

namespace GlobalTheory.PowFix

theorem exists_pos_pow_apply_eq {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
    (σ : Ω ≃ₐ[E] Ω) (x : Ω) (hx : IsIntegral E x) : ∃ k : ℕ, 0 < k ∧ (σ ^ k) x = x := by
  classical
  have hfin : ((minpoly E x).rootSet Ω).Finite := Polynomial.rootSet_finite _ _
  haveI := hfin.to_subtype
  let f : ℕ → (minpoly E x).rootSet Ω := fun n => ⟨(σ ^ n) x, by
    rw [Polynomial.mem_rootSet]
    refine ⟨minpoly.ne_zero hx, ?_⟩
    rw [show ((σ ^ n) x) = ((σ ^ n : Ω ≃ₐ[E] Ω) : Ω →ₐ[E] Ω) x from rfl,
      Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]⟩
  obtain ⟨a, b, hab, h⟩ := Finite.exists_ne_map_eq_of_infinite f
  have h' : (σ ^ a) x = (σ ^ b) x := congrArg Subtype.val h
  have key : ∀ a b : ℕ, a < b → (σ ^ a) x = (σ ^ b) x → ∃ k : ℕ, 0 < k ∧ (σ ^ k) x = x := by
    intro a b hlt he
    refine ⟨b - a, Nat.sub_pos_of_lt hlt, ?_⟩
    have e : σ ^ b = σ ^ a * σ ^ (b - a) := by rw [← pow_add, Nat.add_sub_cancel' hlt.le]
    rw [e, AlgEquiv.mul_apply] at he
    exact ((σ ^ a).injective he).symm
  rcases lt_or_gt_of_ne hab with hlt | hlt
  · exact key a b hlt h'
  · exact key b a hlt h'.symm

theorem pow_apply_eq_of_apply_eq {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
    (τ : Ω ≃ₐ[E] Ω) (x : Ω) (h : τ x = x) (j : ℕ) : (τ ^ j) x = x := by
  induction j with
  | zero => rfl
  | succ j ih => rw [pow_succ, AlgEquiv.mul_apply, h, ih]

theorem exists_pos_pow_fix : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (σ : G E Ω) (s : Finset Ω), ∃ m : ℕ, 0 < m ∧ ∀ x ∈ s, (σ ^ m) x = x := by
  intro E Ω _ _ _ _ _ σ s
  classical
  have hint : ∀ x : Ω, IsIntegral E x := fun x =>
    (Algebra.IsAlgebraic.isAlgebraic (R := E) x).isIntegral
  choose k hk0 hk using fun x : Ω => exists_pos_pow_apply_eq σ x (hint x)
  refine ⟨∏ x ∈ s, k x, Finset.prod_pos fun x _ => hk0 x, fun x hx => ?_⟩
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem k hx
  rw [hc, pow_mul]
  exact pow_apply_eq_of_apply_eq _ x (hk x) c

end GlobalTheory.PowFix
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimitiveElementStabilizerFinset
section
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

theorem GlobalTheory.stab_finset_eq_stab_primitive : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (s : Finset Ω), ∃ β : Ω, ∀ σ : G E Ω, σ β = β ↔ ∀ x ∈ s, σ x = x := by
  intro E Ω _ _ _ _ _ s
  haveI : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  set K := IntermediateField.adjoin E (s : Set Ω) with hK
  haveI : FiniteDimensional E K :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  obtain ⟨α, hα⟩ := Field.exists_primitive_element E K
  refine ⟨(α : Ω), fun σ => ?_⟩
  have key : IntermediateField.adjoin E {(α : Ω)} = K := by
    have h1 := congrArg (IntermediateField.map K.val) hα
    rw [IntermediateField.adjoin_map] at h1
    have hm : IntermediateField.map K.val ⊤ = K := by
      ext y; constructor
      · rintro ⟨z, -, rfl⟩; exact z.2
      · intro hy; exact ⟨⟨y, hy⟩, trivial, rfl⟩
    rw [hm] at h1
    simpa [Set.image_singleton] using h1

  have gen : ∀ (T : Set Ω), (∀ x ∈ T, σ x = x) → ∀ y ∈ IntermediateField.adjoin E T, σ y = y := by
    intro T hT y hy
    have := IntermediateField.algHom_ext_of_eq_adjoin E (S := IntermediateField.adjoin E T) (s := T) rfl
      (φ₁ := ((σ : Ω →ₐ[E] Ω)).comp (IntermediateField.adjoin E T).val)
      (φ₂ := (IntermediateField.adjoin E T).val) (fun x hx => by simp [hT x hx])
    exact congrArg (fun φ => φ ⟨y, hy⟩) this
  constructor
  · intro h x hx
    have hxK : x ∈ IntermediateField.adjoin E {(α : Ω)} := by
      rw [key]; exact IntermediateField.subset_adjoin E _ hx
    exact gen {(α : Ω)} (by simpa using h) x hxK
  · intro h
    exact gen (s : Set Ω) (fun x hx => h x hx) (α : Ω) α.2
end

