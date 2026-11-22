import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0026
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedFormsMutualShuffleEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0061
import GroundTheory.PAdicHodge.AInfGalois
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0391
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Zj
import GroundTheory.AutomorphicForms.SupercuspidalCoefficients
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0392
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0042
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0032
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0322
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.TemperedProducts.CentredSegSqInt
import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.TemperedLocalGlobal.LocalGlobalOfIwahori
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0051
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanNecTemp
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusTrivialOnLeviCompact
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc GlobalTheory.SplitWeil

namespace GlobalTheory.CompanionTheory.HalfModCompact

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_nabs_le_of_isCompact {C : Set k} (hC : IsCompact C) :
    ∃ B : ℝ, ∀ u : kˣ, (u : k) ∈ C → nabs k u ≤ B := by
  classical
  have hopen : ∀ y : kˣ, IsOpen {x : k | valuation k x ≤ valuation k (y : k)} := by
    intro y
    have hy : valuation k (y : k) ≠ 0 := by simp
    rw [isOpen_iff_mem_nhds]
    intro x hx
    rw [IsValuativeTopology.mem_nhds_iff]
    refine ⟨Units.mk0 (valuation k (y : k)) hy, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    simp only [Set.mem_ofPred_eq] at hz hx ⊢
    calc valuation k (x + z) ≤ max (valuation k x) (valuation k z) := Valuation.map_add _ _ _
      _ ≤ valuation k (y : k) := max_le hx (le_of_lt (by simpa using hz))
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover (fun y : kˣ => {x : k | valuation k x ≤ valuation k (y : k)})
    hopen (by
      intro x _
      rw [Set.mem_iUnion]
      by_cases hx : x = 0
      · exact ⟨1, by simp [hx]⟩
      · exact ⟨Units.mk0 x hx, by simp⟩)
  obtain ⟨y, -, hy⟩ := Finset.exists_max_image (insert 1 t) (fun y : kˣ => valuation k (y : k))
    (Finset.insert_nonempty _ _)
  refine ⟨nabs k y, fun u hu => nabs_le_of_valuation_le ?_⟩
  obtain ⟨z, hz, hzu⟩ := Set.mem_iUnion₂.1 (ht hu)
  exact le_trans hzu (hy z (Finset.mem_insert_of_mem hz))

theorem nabs_pow_eq (y : kˣ) (n : ℕ) : nabs k (y ^ n) = nabs k y ^ n := by
  unfold nabs
  rw [map_pow, NNReal.coe_pow]

theorem nabs_inv_eq (y : kˣ) : nabs k y⁻¹ = (nabs k y)⁻¹ := by
  unfold nabs
  rw [map_inv, NNReal.coe_inv]

theorem nabs_eq_one_of_pow_le (y : kˣ) (B : ℝ) (h₁ : ∀ n : ℕ, nabs k (y ^ n) ≤ B)
    (h₂ : ∀ n : ℕ, nabs k (y⁻¹ ^ n) ≤ B) : nabs k y = 1 := by
  have hpos : 0 < nabs k y := (nabs_properties k).2.1 y
  rcases lt_trichotomy (nabs k y) 1 with hlt | heq | hgt
  · exfalso
    have hinv : 1 < (nabs k y)⁻¹ := (one_lt_inv₀ hpos).2 hlt
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt B hinv
    have h3 := h₂ n
    rw [nabs_pow_eq, nabs_inv_eq] at h3
    linarith
  · exact heq
  · exfalso
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt B hgt
    have h3 := h₁ n
    rw [nabs_pow_eq] at h3
    linarith

def blockDet {N h : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (a : Fin h) (g : GL (Fin N) k) : k :=
  Matrix.det (Matrix.of fun i j : Fin (d a) =>
    (g : Matrix (Fin N) (Fin N) k) (stdBlocks d hd ⟨a, i⟩) (stdBlocks d hd ⟨a, j⟩))

theorem continuous_blockDet {N h : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (a : Fin h) :
    Continuous (blockDet (k := k) d hd a) := by
  unfold blockDet
  first
    | fun_prop
    | exact Continuous.matrix_det (continuous_pi fun i => continuous_pi fun j =>
        (Units.continuous_val.matrix_elem _ _))

theorem blockDet_leviEmb {N h : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (a : Fin h)
    (x : Levi k (Bl d)) :
    blockDet d hd a (leviEmb k (stdBlocks d hd) x) =
      ((Matrix.GeneralLinearGroup.det (x a) : kˣ) : k) := by
  unfold blockDet
  have hm : (Matrix.of fun i j : Fin (d a) =>
      ((leviEmb k (stdBlocks d hd) x : GL (Fin N) k) : Matrix (Fin N) (Fin N) k)
        (stdBlocks d hd ⟨a, i⟩) (stdBlocks d hd ⟨a, j⟩)) =
      ((x a : GL (Bl d a) k) : Matrix (Bl d a) (Bl d a) k) := by
    ext i j
    simp [leviEmb, Matrix.blockDiagonal'_apply_eq]
  rw [hm, Matrix.GeneralLinearGroup.val_det_apply]

theorem nabs_det_eq_one_of_mem_KM {N h : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N)
    {J : Subgroup (GL (Fin N) k)} (hJ : IsCompact (J : Set (GL (Fin N) k)))
    {x : Levi k (Bl d)} (hx : x ∈ KM k N J d hd) (a : Fin h) :
    nabs k (Matrix.GeneralLinearGroup.det (x a)) = 1 := by
  have hmem : ∀ z ∈ KM k N J d hd, blockDet d hd a (leviEmb k (stdBlocks d hd) z) ∈
      blockDet (k := k) d hd a '' (J : Set (GL (Fin N) k)) :=
    fun z hz => ⟨_, hz, rfl⟩
  obtain ⟨B, hB⟩ := exists_nabs_le_of_isCompact (hJ.image (continuous_blockDet d hd a))
  apply nabs_eq_one_of_pow_le _ B
  · intro n
    apply hB
    have h1 := hmem _ ((KM k N J d hd).pow_mem hx n)
    have e : (x ^ n) a = x a ^ n := rfl
    rw [blockDet_leviEmb, e, map_pow] at h1
    exact h1
  · intro n
    apply hB
    have h1 := hmem _ ((KM k N J d hd).pow_mem ((KM k N J d hd).inv_mem hx) n)
    have e : (x⁻¹ ^ n) a = (x a)⁻¹ ^ n := rfl
    rw [blockDet_leviEmb, e, map_pow, map_inv] at h1
    exact h1

theorem deltaHalf_eq_one_of_mem_KM :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (N h : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (J : Subgroup (GL (Fin N) k)),
      IsCompact (J : Set (GL (Fin N) k)) → ∀ x ∈ KM k N J d hd, deltaHalf k (Bl d) x = 1 := by
  intro k _ _ _ _ N h d hd J hJ x hx
  unfold deltaHalf
  rw [MonoidHom.finsetProd_apply]
  apply Finset.prod_eq_one
  intro a _
  rw [MonoidHom.comp_apply, Pi.evalMonoidHom_apply]
  unfold detChar
  rw [MonoidHom.comp_apply]
  apply Units.ext
  simp [absPow, nabs_det_eq_one_of_mem_KM d hd hJ hx a]

end GlobalTheory.CompanionTheory.HalfModCompact
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedFormsInterleaveSum
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

namespace GlobalTheory.CompanionTheory.ZcMerge

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def fromA (a : Comb.ASeg (CuspT k)) : Segment k := Segment.ofFirst a.start.1 a.start.2 a.len a.len_pos

theorem toA_fromA (a : Comb.ASeg (CuspT k)) : toA (fromA a) = a := rfl

theorem fromA_toA (Δ : Segment k) : fromA (toA Δ) = Δ := Segment.ext_first rfl rfl

theorem carrier_subset_of_image {Δ Δ' : Segment k} (h : (toA Δ).carrier sNu ⊆ (toA Δ').carrier sNu) :
    Δ.carrier ⊆ Δ'.carrier := by
  rw [← ZcWords.image_carrier, ← ZcWords.image_carrier]
  exact Set.image_mono h

theorem aPrecedes_of_precedes {Δ Δ' : Segment k} (h : Δ.Precedes Δ') : Comb.APrecedes sNu (toA Δ) (toA Δ') := by
  obtain ⟨⟨⟨Γ, hΓ⟩, h1, h2⟩, j, hj, hs⟩ := h
  refine ⟨⟨⟨toA Γ, ?_⟩, fun e => h1 (carrier_subset_of_image e), fun e => h2 (carrier_subset_of_image e)⟩, j, hj,
    Subtype.ext ?_⟩
  · apply Set.image_injective.2 (Subtype.val_injective (p := fun x : IrrGL k => x.IsCusp))
    rw [Set.image_union, ZcWords.image_carrier, ZcWords.image_carrier, ZcWords.image_carrier, hΓ]
  · exact hs.trans (ZcWords.val_sNu_iterate (toA Δ).start j).symm

theorem map_toA_map_fromA (L : List (Comb.ASeg (CuspT k))) : (L.map fromA).map toA = L := by
  rw [List.map_map]
  exact List.map_id'' toA_fromA L

theorem isOrderedForm_get {L : List (Comb.ASeg (CuspT k))} {𝔪 : Multiset (Segment k)}
    (hL : (L : Multiset (Comb.ASeg (CuspT k))) = 𝔪.map toA) (hO : Comb.AOrdered sNu L) :
    IsOrderedForm (L.map fromA).get 𝔪 := by
  constructor
  · rw [Fin.univ_val_map, List.ofFn_get, ← Multiset.map_coe, hL, Multiset.map_map]
    exact (Multiset.map_congr rfl fun Δ _ => fromA_toA Δ).trans (Multiset.map_id' 𝔪)
  · intro i j hij hp
    rw [Comb.AOrdered, ← map_toA_map_fromA L, List.pairwise_map] at hO
    exact List.pairwise_iff_get.1 hO i j hij (aPrecedes_of_precedes hp)

theorem wtW_get (L : List (Comb.ASeg (CuspT k))) :
    wtW (L.map fromA).get = (Comb.wt sNu L).map Subtype.val := by
  rw [ZcWords.wtW_eq, List.ofFn_get, map_toA_map_fromA]

theorem exists_common_orderedForm : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL), ∀ (𝔪 𝔫 : Multiset (Segment k)),
    ∃ (h₁ h₂ h : ℕ) (Δ₁ : Fin h₁ → Segment k) (Δ₂ : Fin h₂ → Segment k) (Δ : Fin h → Segment k),
      IsOrderedForm Δ₁ 𝔪 ∧ IsOrderedForm Δ₂ 𝔫 ∧ IsOrderedForm Δ (𝔪 + 𝔫) ∧
        Zc.Comb.Interleave (wtW Δ₁) (wtW Δ₂) (wtW Δ) := by
  intro k _ _ _ _ _ 𝔪 𝔫
  obtain ⟨L₁, L₂, L, h1, h2, h3, o1, o2, o3, hI⟩ := GlobalTheory.CompanionTheory.SegOrder.exists_common_ordered_form (sNu (k := k)) ZcWords.sNu_injective
    ZcWords.sNu_aperiodic (𝔪.map toA) (𝔫.map toA)
  refine ⟨_, _, _, (L₁.map fromA).get, (L₂.map fromA).get, (L.map fromA).get, isOrderedForm_get h1 o1,
    isOrderedForm_get h2 o2, isOrderedForm_get (by rw [h3, Multiset.map_add]) o3, ?_⟩
  rw [wtW_get, wtW_get, wtW_get]
  exact ZcWords.interleave_map _ hI

end GlobalTheory.CompanionTheory.ZcMerge

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PiTensorCentralBlockScalarStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pi_tensor_central_block_scalar : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ {h : ℕ} (x : Fin h → IrrGL k) (t : kˣ) (c : Fin h → ℂ), (∀ i, Zl.ScalarBy (x i) t (c i)) → ∀ (j : Fin h) (v : PiTensorProduct ℂ (fun a => (x a).2.rep.V)), piTensor (fun a => (x a).rep) (Zl.JC.zj (fun a => (x a).1) t j) v = (∏ i ∈ Finset.univ.filter (· ≤ j), c i) • v := by
  first | exact @GlobalTheory.CompanionTheory.JCScalar.piTensor_zj | exact GlobalTheory.CompanionTheory.JCScalar.piTensor_zj | (intros; apply GlobalTheory.CompanionTheory.JCScalar.piTensor_zj <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PiTensorIrreducibleNontrivialStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pi_tensor_irreducible_nontrivial : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ {h : ℕ} (x : Fin h → IrrGL k), Nontrivial (PiTensorProduct ℂ (fun a => (x a).2.rep.V)) := by
  first | exact @GlobalTheory.CompanionTheory.TensorIrr.nontrivial_piTensorProduct_irrGL | exact GlobalTheory.CompanionTheory.TensorIrr.nontrivial_piTensorProduct_irrGL | (intros; apply GlobalTheory.CompanionTheory.TensorIrr.nontrivial_piTensorProduct_irrGL <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PolyBall
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.CompanionTheory.MirFourier

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def polyBall (n : ℕ) (s : kˣ) : Subgroup (Multiplicative (Fin n → k)) where
  carrier := {x | ∀ i, x.toAdd i ∈ cball s}
  mul_mem' := fun ha hb i => add_mem_cball (ha i) (hb i)
  one_mem' := fun i => by simp [cball]
  inv_mem' := fun {x} hx i => by
    have h := hx i
    simpa [cball, Valuation.map_neg] using h

def resChr (ψ : AddChar k Circle) {n : ℕ} (a : Fin n → k) (L : Subgroup (Multiplicative (Fin n → k))) : L →* ℂˣ :=
  (chrA k ψ a).comp L.subtype

def unipIn (k : Type) [Field k] (n : ℕ) : Multiplicative (Fin n → k) →* Mir k n :=
  (unip k n).codRestrict (Mir k n) (fun v => MirU_le_Mir k n ⟨v, rfl⟩)

def ann (ψ : AddChar k Circle) (n : ℕ) (t : kˣ) : Subgroup (Multiplicative (Fin n → k)) where
  carrier := {x | ∀ a ∈ polyBall n t, ψ (a.toAdd ⬝ᵥ x.toAdd) = 1}
  mul_mem' := fun {x y} hx hy a ha => by
    rw [toAdd_mul, dotProduct_add, AddChar.map_add_eq_mul, hx a ha, hy a ha, one_mul]
  one_mem' := fun a _ => by simp
  inv_mem' := fun {x} hx a ha => by
    rw [toAdd_inv, dotProduct_neg, AddChar.map_neg_eq_inv, hx a ha, inv_one]

end GlobalTheory.CompanionTheory.MirFourier

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuotientVanishingStatement
section
open Matrix MeasureTheory PositivityTheory.Rg.BcB PositivityTheory.Rg.Tf.Loc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotient_vanishing : GlobalTheory.CompanionTheory.LocVan.QuotVanish := by
  first | exact @GlobalTheory.CompanionTheory.LocVan.quotVanish | exact GlobalTheory.CompanionTheory.LocVan.quotVanish | (intros; apply GlobalTheory.CompanionTheory.LocVan.quotVanish <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealPowPartialSegmentLtOneStatement
section
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_pow_partial_segment_lt_one : ∀ (α r : ℝ) (d l0 l1 : ℕ), 0 < α → α < 1 → 0 < r → 1 ≤ d → 1 ≤ l0 → 1 ≤ l1 → r ^ (l0 + l1) * α ^ (d * ((l0 + l1) * (l0 + l1 - 1) / 2)) = 1 → r ^ l0 * α ^ (d * (l0 * l1 + l0 * (l0 - 1) / 2)) < 1 := by
  first | exact @GlobalTheory.CompanionTheory.Segment.top_piece_exponent_lt_one | exact GlobalTheory.CompanionTheory.Segment.top_piece_exponent_lt_one | (intros; apply GlobalTheory.CompanionTheory.Segment.top_piece_exponent_lt_one <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelationOperations
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct
open GlobalTheory.WeilDeligne LocalGlobalAboveLAlt

namespace GlobalTheory.CompanionTheory.RelOpsLeaf

section Linear

variable {V V' : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']

theorem eq_det_smul_one (hV : finrank ℂ V = 1) (f : Module.End ℂ V) :
    f = LinearMap.det f • (1 : Module.End ℂ V) := by
  have hm := LinearMap.charpoly_monic f
  have hd : f.charpoly.natDegree = 1 := by rw [LinearMap.charpoly_natDegree, hV]
  have h1 := hm.eq_X_add_C hd
  have h2 := LinearMap.aeval_self_charpoly f
  obtain ⟨t, ht⟩ : ∃ t : ℂ, f = t • (1 : Module.End ℂ V) := by
    refine ⟨-f.charpoly.coeff 0, ?_⟩
    rw [h1, map_add, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one] at h2
    rw [neg_smul, eq_neg_iff_add_eq_zero]
    exact h2
  subst ht
  rw [LinearMap.det_smul, hV, pow_one]
  simp

theorem charpoly_smul_eq_scaleRoots (f : Module.End ℂ V) {t : ℂ} (ht : t ≠ 0) :
    (t • f).charpoly = f.charpoly.scaleRoots t := by
  refine Polynomial.funext fun z => ?_
  have h0 : t * (z / t) = z := by field_simp
  have h1 := scaleRoots_eval₂_mul (p := f.charpoly) (RingHom.id ℂ) (z / t) t
  simp only [RingHom.id_apply, h0, eval₂_id] at h1
  rw [h1, LinearMap.eval_charpoly, LinearMap.eval_charpoly, LinearMap.charpoly_natDegree,
    ← LinearMap.det_smul]
  congr 1
  rw [smul_sub, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_smul, h0]

theorem charpoly_map_one (hV' : finrank ℂ V' = 1) (f : Module.End ℂ V) :
    (TensorProduct.map f (1 : Module.End ℂ V')).charpoly = f.charpoly := by
  let e : V' ≃ₗ[ℂ] ℂ := LinearEquiv.ofFinrankEq _ _ (by rw [hV', finrank_self])
  let F : (V ⊗[ℂ] V') ≃ₗ[ℂ] V :=
    (TensorProduct.congr (LinearEquiv.refl ℂ V) e).trans (TensorProduct.rid ℂ V)
  have key : ∀ u, F (TensorProduct.map f (1 : Module.End ℂ V') u) = f (F u) := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [F]
    | add a b ha hb => simp only [map_add, ha, hb]
  rw [← LinearEquiv.charpoly_conj F]
  congr 1
  refine LinearMap.ext fun v => ?_
  obtain ⟨u, rfl⟩ := F.surjective v
  simp [LinearEquiv.conj_apply, key]

end Linear

theorem pow_of_mul_eq_pow {p q : ℂ[X]} {m n : ℕ} (hp : p.Monic) (hq : q.Monic)
    (hpd : p.natDegree = m) (hqd : q.natDegree = n) (h : p * q = (X - 1) ^ (m + n)) :
    p = (X - 1) ^ m ∧ q = (X - 1) ^ n := by
  have e : (X - 1 : ℂ[X]) = X - C 1 := by simp
  rw [e] at h ⊢
  have key : ∀ {r : ℂ[X]}, r.Monic → r ∣ (X - C 1) ^ (m + n) → r = (X - C 1) ^ r.natDegree := by
    intro r hr hd
    obtain ⟨i, -, hi⟩ := (dvd_prime_pow (prime_X_sub_C (1 : ℂ)) _).1 hd
    have h1 := eq_of_monic_of_associated hr ((monic_X_sub_C (1 : ℂ)).pow i) hi
    have h2 : r.natDegree = i := by rw [h1, natDegree_pow, natDegree_X_sub_C, mul_one]
    rw [h2]
    exact h1
  subst hpd hqd
  exact ⟨key hp (Dvd.intro _ h), key hq (Dvd.intro_left _ h)⟩

section Rel

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem exists_char_of_lpDim_eq_one (c : WD h) (hc : c.lpDim = 1) :
    ∃ χ : ↥(Weil h) →* ℂˣ, ∀ (x : WD h) (g : ↥(Weil h)),
      (x.lpChar c).charPol g = (x.charPol g).scaleRoots (χ g : ℂ) := by
  induction c using WD.ind with
  | hP m b =>
    rw [WD.lpDim_mk] at hc
    let f : ↥(Weil h) →* ℂ := (LinearMap.det : Module.End ℂ (Fin m → ℂ) →* ℂ).comp b.ρ
    refine ⟨f.toHomUnits, fun x g => ?_⟩
    induction x using WD.ind with
    | hP n a =>
      have hb : b.ρ g = ((f.toHomUnits g : ℂˣ) : ℂ) • (1 : Module.End ℂ (Fin m → ℂ)) := by
        rw [MonoidHom.coe_toHomUnits]
        exact eq_det_smul_one hc (b.ρ g)
      rw [WD.lpChar_mk, WD.charPol_mk, WD.charPol_mk, WDRep.tensor_ρ, hb,
        TensorProduct.map_smul_right, charpoly_smul_eq_scaleRoots _ (Units.ne_zero _),
        charpoly_map_one hc]

end Rel

end GlobalTheory.CompanionTheory.RelOpsLeaf
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictionMirabolicTwistedKernelStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restriction_mirabolic_twisted_kernel : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (m n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin (m + 1)) k) V), twKer (resM k π).ρ (derUnipM k m n) (derCharM k ψ m n) = twKer π (derUnip k (m + 1) n) (derChar k ψ (m + 1) n) := by
  first | exact @GlobalTheory.CompanionTheory.BZMirDer.twKer_resM_derUnipM | exact GlobalTheory.CompanionTheory.BZMirDer.twKer_resM_derUnipM | (intros; apply GlobalTheory.CompanionTheory.BZMirDer.twKer_resM_derUnipM <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentJacquetTwoFactorSplitStatement
section
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.segment_jacquet_two_factor_split : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (Δ : Segment k) (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), Zc.LSegJacquet k → IsLSeg Δ π → ∀ (x : Fin 2 → IrrGL k) (hd : ∑ a, (x a).1 = N), (∀ a, 0 < (x a).1) → Zc.jm x hd π ≠ 0 → ∃ Γ : Fin 2 → Segment k, Zc.IsTopCut Δ Γ ∧ ∀ a, IsLSeg (Γ a) (x a).rep := by
  first | exact @GlobalTheory.CompanionTheory.SegJacquet.exists_isTopCut_two_of_jhMult_ne_zero | exact GlobalTheory.CompanionTheory.SegJacquet.exists_isTopCut_two_of_jhMult_ne_zero | (intros; apply GlobalTheory.CompanionTheory.SegJacquet.exists_isTopCut_two_of_jhMult_ne_zero <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentRepCentralCharacterFormulaStatement
section
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.segment_rep_central_character_formula : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (Γ : Segment k) (y : IrrGL k), IsLSeg Γ y.rep → ∀ (t : kˣ) (c : ℂ), Zl.ScalarBy Γ.first t c → Zl.ScalarBy y t (c ^ Γ.len * ((absPow k (Γ.first.1 : ℂ) t : ℂˣ) : ℂ) ^ (Γ.len * (Γ.len - 1) / 2)) := by
  first | exact @GlobalTheory.CompanionTheory.SegScalar.scalarBy_of_isLSeg | exact GlobalTheory.CompanionTheory.SegScalar.scalarBy_of_isLSeg | (intros; apply GlobalTheory.CompanionTheory.SegScalar.scalarBy_of_isLSeg <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentRepCentralCharacterStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.segment_rep_central_character : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (Δ : Segment k) (y : IrrGL k), IsLSeg Δ y.rep → ∀ (t : kˣ) (c : ℂ), Zl.ScalarBy Δ.first t c → Zl.ScalarBy y t (c ^ Δ.len * ((absPow k (((Δ.len * (Δ.len - 1) / 2 : ℕ) : ℂ)) (t ^ Δ.d) : ℂˣ) : ℂ)) := by
  first | exact @GlobalTheory.CompanionTheory.ZlScalar.scalarBy_lseg | exact GlobalTheory.CompanionTheory.ZlScalar.scalarBy_lseg | (intros; apply GlobalTheory.CompanionTheory.ZlScalar.scalarBy_lseg <;> assumption)
end

