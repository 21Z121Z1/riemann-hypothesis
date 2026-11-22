import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0120
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnramifiedExtTorsionPointsGoodReduction
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstMulEqUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0995
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumUnipotentConjEqZeroOfConstantTermZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0934
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0975

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformizerPowerIntegralRatios
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

namespace GlobalTheory

theorem adicCompletion_tensor_matrixUnit_identity : ∀ (L : Type) [Field L] [NumberField L] (C : Type) [Ring C] [Algebra ℚ C] (ι : L →ₐ[ℚ] C) (r : ℕ)
    (e : Fin r → C) (N : ℕ) (l : Fin N → L) (c : Fin N → C) (i i' : Fin r),
    (∀ β : Fin r → L, ∑ k, ι (l k) * (∑ i'', ι (β i'') * e i'') * c k = ι (β i') * e i) →
    ∀ (v : HeightOneSpectrum ℤ) (β : Fin r → v.adicCompletion ℚ ⊗[ℚ] L),
    ∑ k, Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] l k) *
        (∑ i'', Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι (β i'') *
          ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] e i'')) * ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] c k) =
      Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι (β i') * ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] e i) := by
  intro L _ _ C _ _ ι r e N l c i i' h v β
  set φ := Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι with hφ
  let P : (Fin r → v.adicCompletion ℚ ⊗[ℚ] L) → Prop := fun β =>
    ∑ k, φ ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] l k) *
        (∑ i'', φ (β i'') * ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] e i'')) * ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] c k) =
      φ (β i') * ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] e i)
  have hzero : P 0 := by simp [P]
  have hadd : ∀ β₁ β₂, P β₁ → P β₂ → P (β₁ + β₂) := by
    intro β₁ β₂ h₁ h₂
    simp only [P, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib, mul_add] at h₁ h₂ ⊢
    rw [h₁, h₂]
  have hpure : ∀ (a : v.adicCompletion ℚ) (γ : Fin r → L), P (fun j => a ⊗ₜ[ℚ] γ j) := by
    intro a γ
    simp only [P, hφ, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, ← TensorProduct.tmul_sum]
    rw [h γ]
  have hsingle : ∀ j x, P (Pi.single j x) := by
    intro j x
    induction x using TensorProduct.induction_on with
    | zero => simpa using hzero
    | tmul a m =>
      have : (Pi.single j (a ⊗ₜ[ℚ] m) : Fin r → v.adicCompletion ℚ ⊗[ℚ] L) =
          fun j' => a ⊗ₜ[ℚ] (Pi.single j m : Fin r → L) j' := by
        funext j'
        by_cases hj : j' = j
        · subst hj; simp
        · simp [Pi.single_apply, hj]
      rw [this]; exact hpure a _
    | add x y hx hy =>
      rw [Pi.single_add]; exact hadd _ _ hx hy
  have hall : P (∑ j, Pi.single j (β j)) :=
    Finset.sum_induction _ P hadd hzero (fun j _ => hsingle j (β j))
  rw [Finset.univ_sum_single] at hall
  exact hall

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueLeftBasisCoordsAdicCompletion
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

namespace GlobalTheory.LeftBasisBC

theorem existsUnique_coords_baseChange (K : Type) [CommRing K] [Algebra ℚ K]
    (L : Type) [Field L] [Algebra ℚ L] (C : Type) [Ring C] [Algebra ℚ C] (ι : L →ₐ[ℚ] C) (r : ℕ)
    (e : Fin r → C) (h : ∀ x : C, ∃! c : Fin r → L, x = ∑ i, ι (c i) * e i)
    (y : K ⊗[ℚ] C) :
    ∃! β : Fin r → K ⊗[ℚ] L,
      y = ∑ i, Algebra.TensorProduct.map (AlgHom.id ℚ K) ι (β i) * ((1 : K) ⊗ₜ[ℚ] e i) := by
  let φ : (Fin r → L) →ₗ[ℚ] C :=
    { toFun := fun c => ∑ i, ι (c i) * e i
      map_add' := fun a b => by simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun q a => by simp [Finset.smul_sum] }
  have hφ : Function.Bijective φ := by
    rw [Function.bijective_iff_existsUnique]
    intro x
    obtain ⟨c, hc, hu⟩ := h x
    exact ⟨c, hc.symm, fun d hd => hu d hd.symm⟩
  let E : (Fin r → L) ≃ₗ[ℚ] C := LinearEquiv.ofBijective φ hφ
  let P : K ⊗[ℚ] (Fin r → L) ≃ₗ[ℚ] (Fin r → K ⊗[ℚ] L) :=
    TensorProduct.piRight ℚ ℚ K (fun _ : Fin r => L)
  let F : K ⊗[ℚ] (Fin r → L) ≃ₗ[ℚ] K ⊗[ℚ] C := TensorProduct.congr (LinearEquiv.refl ℚ K) E
  have key : ∀ z : K ⊗[ℚ] (Fin r → L), F z =
      ∑ i, Algebra.TensorProduct.map (AlgHom.id ℚ K) ι (P z i) * ((1 : K) ⊗ₜ[ℚ] e i) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a c =>
      simp [F, P, E, φ, TensorProduct.tmul_sum]
    | add a b ha hb =>
      simp only [map_add, ha, hb, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  refine ⟨P (F.symm y), ?_, ?_⟩
  · show y = _
    rw [← key, LinearEquiv.apply_symm_apply]
  · intro β hβ
    have h1 := key (P.symm β)
    rw [LinearEquiv.apply_symm_apply, ← hβ] at h1
    rw [← h1, LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]

theorem existsUnique_coords_adicCompletion :
    ∀ (L : Type) [Field L] [NumberField L] (C : Type) [Ring C] [Algebra ℚ C] (ι : L →ₐ[ℚ] C) (r : ℕ)
    (e : Fin r → C), (∀ x : C, ∃! c : Fin r → L, x = ∑ i, ι (c i) * e i) →
    ∀ (v : HeightOneSpectrum ℤ) (y : v.adicCompletion ℚ ⊗[ℚ] C),
    ∃! β : Fin r → v.adicCompletion ℚ ⊗[ℚ] L,
      y = ∑ i, Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι (β i) *
        ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] e i) :=
  fun L _ _ C _ _ ι r e h v y =>
    existsUnique_coords_baseChange (v.adicCompletion ℚ) L C ι r e h y

end GlobalTheory.LeftBasisBC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryAdelicPointOfEventuallyIntegralLoca
section
noncomputable section

open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical RestrictedProduct

namespace GlobalTheory.OrbFinAf

variable {p : ℕ} [Fact p.Prime]

theorem finiteAdeleRingAway_ext {x y : AfP p} (h : ∀ v : AwayP p, AfP.eval v x = AfP.eval v y) : x = y :=
  Subtype.ext (funext h)

theorem exists_afP (s : ∀ v : AwayP p, Qv v)
    (hs : ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), s v ∈ v.1.adicCompletionIntegers ℚ) :
    ∃ t : AfP p, ∀ v, AfP.eval v t = s v :=
  ⟨(⟨s, hs⟩ : Πʳ v : AwayP p, [v.1.adicCompletion ℚ, v.1.adicCompletionIntegers ℚ]), fun _ => rfl⟩

variable (G : HTGroup p)

abbrev basA : Module.Basis (Fin (Module.finrank ℚ G.C)) (AfP p) (AfP p ⊗[ℚ] G.C) :=
  Algebra.TensorProduct.basis (AfP p) (Module.finBasis ℚ G.C)

abbrev mapV (v : AwayP p) : AfP p ⊗[ℚ] G.C →ₐ[ℚ] Qv v ⊗[ℚ] G.C :=
  Algebra.TensorProduct.map (AfP.eval v) (AlgHom.id ℚ G.C)

theorem repr_mapV (v : AwayP p) (z : AfP p ⊗[ℚ] G.C) (i : Fin (Module.finrank ℚ G.C)) :
    (basV G v).repr (mapV G v z) i = AfP.eval v ((basA G).repr z i) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r y =>
    simp [basV, Algebra.TensorProduct.basis_repr_tmul, Algebra.TensorProduct.map_tmul]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

theorem eq_of_mapV {z z' : AfP p ⊗[ℚ] G.C} (h : ∀ v, mapV G v z = mapV G v z') : z = z' :=
  (basA G).ext_elem fun i => finiteAdeleRingAway_ext fun v => by rw [← repr_mapV, ← repr_mapV, h v]

theorem exists_of_local (y : ∀ v : AwayP p, Qv v ⊗[ℚ] G.C)
    (hy : ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), IsIntV G v (y v)) :
    ∃ z : AfP p ⊗[ℚ] G.C, ∀ v, mapV G v z = y v := by
  choose a ha using fun i : Fin (Module.finrank ℚ G.C) =>
    exists_afP (fun v => (basV G v).repr (y v) i) (hy.mono fun v hv => hv i)
  refine ⟨(basA G).equivFun.symm a, fun v => (basV G v).ext_elem fun i => ?_⟩
  rw [repr_mapV, ← ha i v]
  congr 1
  exact congrFun ((basA G).equivFun.apply_symm_apply a) i

theorem mapV_star (v : AwayP p) (z : AfP p ⊗[ℚ] G.C) :
    (starT G.star (Qv v) (mapV G v z)).unop = mapV G v (starT G.star (AfP p) z).unop := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r y =>
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      starT_tmul]
  | add x y hx hy => simp only [map_add, MulOpposite.unop_add, hx, hy]

theorem mapV_algebraMap (v : AwayP p) (s : AfP p) :
    mapV G v (algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) s) = algebraMap (Qv v) (Qv v ⊗[ℚ] G.C) (AfP.eval v s) := by
  simp [Algebra.TensorProduct.algebraMap_apply]

theorem exists_glue : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (h : ∀ v : AwayP p, Gv G v),
    (∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), h v ∈ IntV G v) → ∃ g : G.GAf, ∀ v, piV G v g = h v := by
  intro p _ G h hint
  obtain ⟨X, hX⟩ := exists_of_local G
    (fun v => ((((h v : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : (Qv v ⊗[ℚ] G.C)ˣ)) : Qv v ⊗[ℚ] G.C))
    (hint.mono fun v hv => hv.1)
  obtain ⟨Y, hY⟩ := exists_of_local G
    (fun v => ((((h v : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1)⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C))
    (hint.mono fun v hv => hv.2.1)
  obtain ⟨s, hs⟩ := exists_afP (fun v => (((h v : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).2 : (Qv v)ˣ) : Qv v))
    (hint.mono fun v hv => hv.2.2.1)
  obtain ⟨s', hs'⟩ := exists_afP (fun v => ((((h v : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).2)⁻¹ : (Qv v)ˣ) : Qv v))
    (hint.mono fun v hv => hv.2.2.2)
  have hXY : X * Y = 1 := eq_of_mapV G fun v => by rw [map_mul, hX, hY, map_one, Units.mul_inv]
  have hYX : Y * X = 1 := eq_of_mapV G fun v => by rw [map_mul, hX, hY, map_one, Units.inv_mul]
  have hss : s * s' = 1 := finiteAdeleRingAway_ext fun v => by rw [map_mul, hs, hs', map_one, Units.mul_inv]
  have hss' : s' * s = 1 := finiteAdeleRingAway_ext fun v => by rw [map_mul, hs, hs', map_one, Units.inv_mul]
  let U : (AfP p ⊗[ℚ] G.C)ˣ := ⟨X, Y, hXY, hYX⟩
  let c : (AfP p)ˣ := ⟨s, s', hss, hss'⟩
  have hmem : (U, c) ∈ UPts G.star (AfP p) := by
    show X * (starT G.star (AfP p) X).unop = algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) s
    refine eq_of_mapV G fun v => ?_
    rw [map_mul, ← mapV_star, hX, mapV_algebraMap, hs]
    exact (h v).2
  refine ⟨⟨(U, c), hmem⟩, fun v => ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · apply Units.ext
    exact hX v
  · apply Units.ext
    exact hs v

end GlobalTheory.OrbFinAf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnramifiedDvrAdjoiningUnitRoots
section
open IsLocalRing Polynomial

namespace GlobalTheory.KummerUnram

theorem etale_adjoinRoot_pow_sub {R : Type} [CommRing R] [Nontrivial R] {k : ℕ} (hk : IsUnit (k : R)) (u : Rˣ) :
    Algebra.Etale R (AdjoinRoot (X ^ k - C (u : R))) := by
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact not_isUnit_zero (M₀ := R) (by simpa using hk)
  have hm : (X ^ k - C (u : R)).Monic := monic_X_pow_sub_C _ hk0
  have h1 : AdjoinRoot.root (X ^ k - C (u : R)) ^ k = algebraMap R _ (u : R) := by
    have := AdjoinRoot.eval₂_root (X ^ k - C (u : R))
    simpa [sub_eq_zero] using this
  have hr : IsUnit (AdjoinRoot.root (X ^ k - C (u : R))) :=
    (isUnit_pow_iff hk0).1 (h1 ▸ (u.isUnit.map _))
  let P : StandardEtalePair R := ⟨X ^ k - C (u : R), hm, derivative (X ^ k - C (u : R)), 1, 0, 1, by simp⟩
  have h : IsUnit (AdjoinRoot.mk (X ^ k - C (u : R)) (derivative (X ^ k - C (u : R)))) := by
    have e : AdjoinRoot.mk (X ^ k - C (u : R)) (derivative (X ^ k - C (u : R))) =
        algebraMap R _ (k : R) * AdjoinRoot.root _ ^ (k - 1) := by
      simp [derivative_X_pow, AdjoinRoot.algebraMap_eq]
    rw [e]
    exact (hk.map _).mul (hr.pow _)
  exact .of_equiv (P.equivAwayAdjoinRoot.trans
    ((IsLocalization.atUnit _ (Localization.Away (AdjoinRoot.mk _ (derivative (X ^ k - C (u : R))))) _
      h).symm.restrictScalars R))

end GlobalTheory.KummerUnram

namespace GlobalTheory.KummerUnram

theorem exists_root_step {F : Type} [Field F] [IsAlgClosed F] (T : Subring F)
    [IsDiscreteValuationRing T] {k : ℕ} (hk : IsUnit (k : T)) (u : Tˣ)
    (ub : AlgebraicClosure (ResidueField T)) (hub : ub ^ k = algebraMap _ _ (residue T u)) :
    ∃ T' : Subring F, UnramSub T.subtype T' ∧ ∃ y ∈ T', y ^ k = ((u : T) : F) ∧
      ∀ n : ℕ, ub ^ n ≠ 1 → y ^ n ≠ 1 := by
  have := etale_adjoinRoot_pow_sub hk u
  let ρ : T →+* AlgebraicClosure (ResidueField T) :=
    (algebraMap (ResidueField T) _).comp (residue T)
  let ε : AdjoinRoot (X ^ k - C (u : T)) →+* AlgebraicClosure (ResidueField T) :=
    AdjoinRoot.lift ρ ub (by simp [ρ, hub])
  have hερ : ε.comp (algebraMap T _) = ρ := by
    ext t
    simp [ε, AdjoinRoot.algebraMap_eq]
  have hε : IsLocalHom (ε.comp (algebraMap T (AdjoinRoot (X ^ k - C (u : T))))) := by
    rw [hερ]; infer_instance
  obtain ⟨B, _, _, _, ψ, ρ', j', -, h2, h3, h4, h5⟩ :=
    TorsionUnram.exists_local_of_etale ε hε T.subtype Subtype.val_injective
  obtain ⟨hD, f, hf, hirr⟩ := UnramSub.range (i := j') h3
  refine ⟨j'.range, ⟨hD, f.comp (ψ.comp (algebraMap T _)), fun v => ?_,
    fun π hπ => hirr _ (h5 π hπ)⟩, j' (ψ (AdjoinRoot.root _)), ⟨_, rfl⟩, ?_, fun n hn hy => hn ?_⟩
  · rw [RingHom.comp_apply, hf]
    exact congr($h4 v)
  · have h1 : AdjoinRoot.root (X ^ k - C (u : T)) ^ k = algebraMap T _ (u : T) := by
      have := AdjoinRoot.eval₂_root (X ^ k - C (u : T))
      simpa [sub_eq_zero] using this
    rw [← map_pow, ← map_pow, h1]
    exact congr($h4 (u : T))
  · have e1 : ψ (AdjoinRoot.root (X ^ k - C (u : T))) ^ n = 1 :=
      h3 (by rw [map_pow, hy, map_one])
    have e2 : ρ' (ψ (AdjoinRoot.root (X ^ k - C (u : T)))) = ub := by
      rw [← RingHom.comp_apply, h2]
      simp [ε]
    rw [← e2, ← map_pow, e1, map_one]

end GlobalTheory.KummerUnram

namespace GlobalTheory.KummerUnram

theorem exists_rootsOfUnity {F : Type} [Field F] [IsAlgClosed F] (T : Subring F)
    [IsDiscreteValuationRing T] {k : ℕ} (hk : IsUnit (k : T)) :
    ∃ T' : Subring F, UnramSub T.subtype T' ∧ ∀ z : F, z ^ k = 1 → z ∈ T' := by
  let ρ : T →+* AlgebraicClosure (ResidueField T) :=
    (algebraMap (ResidueField T) _).comp (residue T)
  have hkΩ : ((k : ℕ) : AlgebraicClosure (ResidueField T)) ≠ 0 := by
    simpa [ρ] using (hk.map ρ).ne_zero
  have hk0 : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hkΩ)
  haveI : NeZero ((k : ℕ) : AlgebraicClosure (ResidueField T)) := ⟨hkΩ⟩
  obtain ⟨ub, hub⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure (ResidueField T)) k
  obtain ⟨T', hT', y, hyT, hy, hyn⟩ := exists_root_step T hk 1 ub (by simp [hub.pow_eq_one])
  have hy1 : y ^ k = 1 := by simpa using hy
  have hprim : IsPrimitiveRoot y k := IsPrimitiveRoot.mk_of_lt y hk0 hy1
    fun l hl hlk => hyn l (hub.pow_ne_one_of_pos_of_lt hl.ne' hlk)
  refine ⟨T', hT', fun z hz => ?_⟩
  haveI : NeZero k := ⟨hk0.ne'⟩
  obtain ⟨i, -, rfl⟩ := hprim.eq_pow_of_pow_eq_one hz
  exact pow_mem hyT i

end GlobalTheory.KummerUnram

namespace GlobalTheory

open KummerUnram in

theorem exists_unramSub_of_pow_eq_units : ∀ (F : Type) [Field F] [IsAlgClosed F] (T : Subring F) [IsDiscreteValuationRing T] (k : ℕ), IsUnit (k : T) → ∀ U : Set Tˣ, U.Finite → ∃ T' : Subring F, GlobalTheory.UnramSub T.subtype T' ∧ ∀ x : F, (∃ u ∈ U, x ^ k = ((u : T) : F)) → x ∈ T' := by
  intro F _ _ T _ k hk U hU
  obtain ⟨T₁, h₁, hroots⟩ := exists_rootsOfUnity T hk
  suffices key : ∃ T' : Subring F, UnramSub T.subtype T' ∧ T₁ ≤ T' ∧
      ∀ x : F, (∃ u ∈ U, x ^ k = ((u : T) : F)) → x ∈ T' by
    obtain ⟨T', h, -, h'⟩ := key
    exact ⟨T', h, h'⟩
  induction U, hU using Set.Finite.induction_on with
  | empty => exact ⟨T₁, h₁, le_rfl, by simp⟩
  | @insert a s _ _ ih =>
    obtain ⟨T', hT', hle, hmem⟩ := ih
    haveI := hT'.isDVR
    have hTT' : T ≤ T' := fun z hz => hT'.mem ⟨z, hz⟩
    let ι : T →+* T' := Subring.inclusion hTT'
    have hk' : IsUnit (k : T') := by simpa [ι] using hk.map ι
    let a' : T'ˣ := Units.map ι.toMonoidHom a
    have hk0 : k ≠ 0 := by rintro rfl; exact not_isUnit_zero (M₀ := T) (by simpa using hk)
    obtain ⟨ub, hub⟩ := IsAlgClosed.exists_pow_nat_eq
      (algebraMap (ResidueField T') (AlgebraicClosure (ResidueField T')) (residue T' a'))
      (Nat.pos_of_ne_zero hk0)
    obtain ⟨T'', hT'', y, hyT, hy, -⟩ := exists_root_step T' hk' a' ub hub
    have hy' : y ^ k = ((a : T) : F) := by simpa [a', ι] using hy
    have ha0 : ((a : T) : F) ≠ 0 := fun h => a.ne_zero (Subtype.ext h)
    have hy0 : y ≠ 0 := by rintro rfl; exact ha0 (by rw [← hy', zero_pow hk0])
    have hle' : T' ≤ T'' := UnramSub.le hT''
    refine ⟨T'', hT'.trans hT'', hle.trans hle', fun x ⟨u, hu, hx⟩ => ?_⟩
    rcases Set.mem_insert_iff.1 hu with rfl | hu
    · have hz : (x / y) ^ k = 1 := by rw [div_pow, hx, hy', div_self ha0]
      have : x = (x / y) * y := by field_simp
      rw [this]
      exact mul_mem (hle' (hle (hroots _ hz))) hyT
    · exact hle' (hmem x ⟨u, hu, hx⟩)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExteriorDerivativeIsDifferential
section
open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem GlobalTheory.LogDR.isExtD_extD : ∀ (K : Type) [Field K], IsExtD ℤ K (extD K) := by
  intro K _
  refine { mul := ?_, sq := ?_, alg := ?_ }
  ·
    intro x y
    rw [extD_apply, extD_apply, extD_apply, CechDR.dDR_mul, add_comm]
    rfl
  · intro x
    rw [extD_apply, extD_apply, CechDR.dDR_dDR]
  · intro a
    rw [extD_apply, CechDR.dDR_algebraMap]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FgFunctionField
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option autoImplicit false

namespace GlobalTheory.FGFun

theorem fg_functionField : ∀ (F : Type) [Field F] (G : Scheme.{0}) [IsIntegral G] (sG : G ⟶ Sp F), IsProjOver sG → ∀ (P Ω : Type) [Field P] [Field Ω] (φ : P →+* G.functionField) (t : Sp P ⟶ Sp F) (ι : G.functionField →+* Ω), spMap ι ≫ G.fromSpecStalk (genericPoint G) ≫ sG = spMap ι ≫ spMap φ ≫ t → (letI := φ.toAlgebra; (⊤ : IntermediateField P G.functionField).FG) := by
  intro F _ G _ sG hproj P Ω _ _ φ t ι h
  letI := φ.toAlgebra
  obtain ⟨τ, rfl⟩ := Spec.map_surjective t
  obtain ⟨β, hβ⟩ := Spec.map_surjective (G.fromSpecStalk (genericPoint G) ≫ sG)
  have hβτ : ∀ c : F, β.hom c = φ (τ.hom c) := by
    rw [← hβ] at h
    simp only [← Spec.map_comp] at h
    have h' := Spec.map_injective h
    intro c
    apply ι.injective
    have := congrArg (fun f => f.hom c) h'
    simpa using this
  have hft : LocallyOfFiniteType sG := by
    obtain ⟨N, i, hi, rfl⟩ := hproj
    haveI := isProper_str F N
    infer_instance
  obtain ⟨U, hU, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 G.isBasis_affineOpens
    (TopologicalSpace.Opens.mem_top (genericPoint G))
  haveI : Nonempty U := ⟨⟨_, hx⟩⟩
  have e : U ≤ sG ⁻¹ᵁ ⊤ := by simp
  have hfin := HasRingHomProperty.appLE (P := @LocallyOfFiniteType) sG hft ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ e
  have key : sG.appLE ⊤ U e ≫ G.presheaf.germ U _ hx = (Scheme.ΓSpecIso (.of F)).hom ≫ β := by
    rw [← Scheme.ΓSpecIso_naturality, hβ, Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop,
      Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res]
    have h3 : (Spec (G.presheaf.stalk (genericPoint G))).presheaf.map
        (homOfLE (le_top : (⊤ : (Spec (G.presheaf.stalk (genericPoint G))).Opens) ≤ ⊤)).op = 𝟙 _ := by
      rw [Subsingleton.elim (homOfLE _) (𝟙 _)]; exact CategoryTheory.Functor.map_id _ _
    rw [h3]
    simp
  classical
  letI : Algebra Γ(Sp F, ⊤) Γ(G, U) := (sG.appLE ⊤ U e).hom.toAlgebra
  have hfin' : Algebra.FiniteType Γ(Sp F, ⊤) Γ(G, U) := hfin
  obtain ⟨s, hs⟩ := hfin'.out
  have hmem : ∀ a : Γ(G, U), (G.presheaf.germ U _ hx).hom a ∈
      IntermediateField.adjoin P ((s.image (G.presheaf.germ U _ hx).hom : Finset _) : Set G.functionField) := by
    intro a
    have ha : a ∈ Algebra.adjoin Γ(Sp F, ⊤) (s : Set Γ(G, U)) := hs ▸ Algebra.mem_top
    induction ha using Algebra.adjoin_induction with
    | mem x hx' =>
      exact IntermediateField.subset_adjoin _ _ (by rw [Finset.coe_image]; exact ⟨x, hx', rfl⟩)
    | algebraMap r =>
      have := congrArg (fun f => f.hom r) key
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
      rw [RingHom.algebraMap_toAlgebra, this, hβτ]
      exact IntermediateField.algebraMap_mem _ _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  refine ⟨s.image (G.presheaf.germ U _ hx).hom, eq_top_iff.2 fun f _ => ?_⟩
  have := functionField_isFractionRing_of_isAffineOpen G U hU
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := Γ(G, U)) f
  exact div_mem (hmem a) (hmem b)

end GlobalTheory.FGFun
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoheightOneNotMemOpenGenericPoint
section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.VerticalUnit

theorem finite_coheight_one_notMem (X : Scheme.{0}) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
    (S : Set X) (hS : IsOpen S) (hη : genericPoint X ∈ S) :
    {x : X | Order.coheight x = 1 ∧ x ∉ S}.Finite := by
  classical
  obtain ⟨T, hT, hc, hi, hU⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hS.isClosed_compl
  refine (hT.image fun Z => if h : IsIrreducible Z then h.genericPoint else genericPoint X).subset ?_
  rintro x ⟨h1, hxS⟩
  obtain ⟨Z, hZ, hxZ⟩ := hU.le hxS
  have hg := (hi Z hZ).isGenericPoint_genericPoint (hc Z hZ)
  set z := (hi Z hZ).genericPoint
  have hzS : z ∉ S := hU.ge (Set.subset_sUnion_of_mem hZ hg.mem)
  have hxz : x ≤ z := hg.specializes hxZ
  have hzη : z < genericPoint X := lt_of_le_not_ge (genericPoint_specializes z)
    fun h => hzS ((show z ⤳ genericPoint X from h).mem_open hS hη)
  refine ⟨Z, hZ, ?_⟩
  simp only [dif_pos (hi Z hZ)]
  by_contra hne
  have hxlt : x < z := lt_of_le_not_ge hxz fun h =>
    hne ((show x ⤳ z from h).antisymm (show z ⤳ x from hxz)).eq.symm
  have a1 := Order.coheight_add_one_le hxlt
  have a2 := Order.coheight_add_one_le hzη
  rw [h1] at a1
  have : (2 : ℕ∞) ≤ 1 := by
    calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
      _ ≤ Order.coheight (genericPoint X) + 1 + 1 := by gcongr; exact zero_le
      _ ≤ Order.coheight z + 1 := by gcongr
      _ ≤ 1 := a1
  exact absurd this (by decide)

end GlobalTheory.VerticalUnit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePadicIntegersQuotPrimePowOfFiniteDimStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_padicIntegers_quot_primePow_of_finiteDim : ∀ (p : ℕ) [Fact p.Prime] (L : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] L] (m : ℕ), Finite (GlobalTheory.LKLoc.intK p L ⧸ Ideal.span {(p : GlobalTheory.LKLoc.intK p L) ^ m}) := by
  first | (exact @GlobalTheory.LKLoc.IntFin.finite_intK_quot_pow) | (exact GlobalTheory.LKLoc.IntFin.finite_intK_quot_pow) | (intros; apply GlobalTheory.LKLoc.IntFin.finite_intK_quot_pow  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePadicTensorUnramifiedIntegersQuotPrimePowStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_padicTensorUnramifiedIntegers_quot_primePow : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r m : ℕ), Finite (GlobalTheory.LKLoc.intK p K ⧸ Ideal.span {(p : GlobalTheory.LKLoc.intK p K) ^ m}) → Finite (GlobalTheory.LKLoc.intK p (Qr p r) ⧸ Ideal.span {(p : GlobalTheory.LKLoc.intK p (Qr p r)) ^ m}) → Finite (intKQ p K r ⧸ Ideal.span {(p : intKQ p K r) ^ m}) := by
  first | (exact @GlobalTheory.TenFin.finite_intKQ_quot) | (exact GlobalTheory.TenFin.finite_intKQ_quot) | (intros; apply GlobalTheory.TenFin.finite_intKQ_quot  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumUnipotentConjEqZeroOfConstantTermZeroStatement
section
open MeasureTheory Matrix
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finsum_unipotentConj_eq_zero_of_constantTerm_zero : ∀ (K : Type) [Field K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K] [MeasurableSpace K] [BorelSpace K]
  (ι : Type) [Fintype ι] [DecidableEq ι] (a b : ℕ) (e : ι ≃ Fin a ⊕ Fin b) (f : GL ι K → ℂ),
  IsLocallyConstant f → HasCompactSupport f →
  (∀ (μ : Measure (Fin a → Fin b → K)), μ.IsAddHaarMeasure →
    ∀ g h : GL ι K, ∫ X, f (g * (h⁻¹ * GlobalTheory.OrbDesc.uGL e X * h)) ∂μ = 0) →
  ∀ K' : Subgroup (GL ι K), IsOpen (K' : Set (GL ι K)) → IsCompact (K' : Set (GL ι K)) →
  (∀ k ∈ K', ∀ k' ∈ K', ∀ g, f (k * g * k') = f g) →
  ∀ γ ∈ GlobalTheory.OrbDesc.blockPar e, (γ : Matrix ι ι K).charpoly.Separable →
  ∑ᶠ q : GL ι K ⧸ (GlobalTheory.OrbDesc.blockUni e ⊓ (GlobalTheory.OrbDesc.blockPar e ⊓ K')),
    (if Quotient.out q ∈ GlobalTheory.OrbDesc.blockUni e then f ((Quotient.out q)⁻¹ * γ * Quotient.out q) else 0) = 0 := by
  first | (exact @GlobalTheory.OrbDesc.NSum.finsum_conj_eq_zero) | (exact GlobalTheory.OrbDesc.NSum.finsum_conj_eq_zero) | (intros; apply GlobalTheory.OrbDesc.NSum.finsum_conj_eq_zero  <;> assumption)
end

