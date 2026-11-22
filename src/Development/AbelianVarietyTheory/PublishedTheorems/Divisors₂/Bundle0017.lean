import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0032
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0098
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0214
import Formalism.SatakeDualWeyl.Bundle0001
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Definitions.Divisors.SecondCountableTopologyOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1139

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GindikinKarpelevich
section
noncomputable section

open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound Formalism.UG

namespace GlobalTheory

namespace WeylCell

section Ring

variable {R : Type} [CommRing R] {n : ℕ}

def IsWeylRep (w : Equiv.Perm (Fin n)) (x : GL (Fin n) R) : Prop :=
  ∀ i j, i ≠ w j → (x : Matrix (Fin n) (Fin n) R) i j = 0

def cell (x : GL (Fin n) R) : Subgroup (GL (Fin n) R) :=
  unipB R (Fin n) ⊓ (unipBLower R (Fin n)).comap (MulAut.conj x⁻¹).toMonoidHom

theorem mem_unipBLower {g : GL (Fin n) R} :
    g ∈ unipBLower R (Fin n) ↔ (∀ i j, i < j → (g : Matrix (Fin n) (Fin n) R) i j = 0) ∧
      ∀ i, (g : Matrix (Fin n) (Fin n) R) i i = 1 := by
  refine (mem_unipRad (e := opp (points (Fin n)))).trans (and_congr Iff.rfl ⟨fun h i => ?_, fun h i _ _ => ?_⟩)
  · exact (h i () ()).trans (by simp)
  · exact (h i).trans (by simp)

theorem mem_cell {x u : GL (Fin n) R} :
    u ∈ cell x ↔ u ∈ unipB R (Fin n) ∧ x⁻¹ * u * x ∈ unipBLower R (Fin n) := by
  simp [cell, Subgroup.mem_inf, Subgroup.mem_comap]

theorem isClosed_cell [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] (x : GL (Fin n) R) :
    IsClosed (cell x : Set (GL (Fin n) R)) := by
  have key : ∀ (f : GL (Fin n) R → GL (Fin n) R), Continuous f → ∀ i j (c : R),
      IsClosed {u | (f u : Matrix (Fin n) (Fin n) R) i j = c} := fun f hf i j c =>
    isClosed_eq ((Units.continuous_val.comp hf).matrix_elem i j) continuous_const
  have hc : Continuous fun u : GL (Fin n) R => x⁻¹ * u * x := by fun_prop
  have e : (cell x : Set (GL (Fin n) R)) =
      ((⋂ i, ⋂ j, ⋂ _ : j < i, {u : GL (Fin n) R | (u : Matrix (Fin n) (Fin n) R) i j = 0}) ∩
        ⋂ i, {u : GL (Fin n) R | (u : Matrix (Fin n) (Fin n) R) i i = 1}) ∩
      ((⋂ i, ⋂ j, ⋂ _ : i < j, {u : GL (Fin n) R | ((x⁻¹ * u * x : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j = 0}) ∩
        ⋂ i, {u : GL (Fin n) R | ((x⁻¹ * u * x : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i i = 1}) := by
    ext u
    simp only [SetLike.mem_coe, mem_cell, mem_unipB, mem_unipBLower, Set.mem_inter_iff, Set.mem_iInter,
      Set.mem_setOf_eq]
  rw [e]
  refine ((isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => key _ continuous_id i j 0).inter
    (isClosed_iInter fun i => key _ continuous_id i i 1)).inter
    ((isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => key _ hc i j 0).inter
    (isClosed_iInter fun i => key _ hc i i 1))

variable (R) in

abbrev permRep (w : Equiv.Perm (Fin n)) : GL (Fin n) R := (Matrix.permMatrixHom (R := R)).toHomUnits w

theorem permRep_apply (w : Equiv.Perm (Fin n)) (i j : Fin n) :
    (permRep R w : Matrix (Fin n) (Fin n) R) i j = if i = w j then 1 else 0 := by
  simp [Matrix.permMatrixHom, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.Perm.inv_def, Equiv.symm_apply_eq]

theorem isWeylRep_permRep (w : Equiv.Perm (Fin n)) : IsWeylRep w (permRep R w) := fun _ _ h => by
  rw [permRep_apply, if_neg h]

end Ring

def cSL (Q z : ℂ) : ℂ := (1 - Q⁻¹ * z) / (1 - z)

def cSU (q z : ℂ) : ℂ := (1 - (q ^ 2)⁻¹ * z) * (1 + q⁻¹ * z) / (1 - z ^ 2)

abbrev lo {n : ℕ} (i : Fin (n / 2)) : Fin n := Fin.castLE (Nat.div_le_self n 2) i

def FormulaGL (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] : Prop :=
  ∀ (n : ℕ) (α : Fin n → ℂˣ) (φ : GL (Fin n) k → ℂ),
    IsBorelSph k (fun i => (α i : ℂ) * (resCard k : ℂ) ^ (-(((n : ℂ) - 1 - 2 * (i.val : ℂ)) / 2))) φ →
  ∀ (w : Equiv.Perm (Fin n)) (x : GL (Fin n) k), x ∈ KO k (Fin n) → IsWeylRep w x →
    (∀ i j, i < j → w j < w i → ‖(α i : ℂ) / α j‖ < 1) →
  ∀ [MeasurableSpace (cell x)] [BorelSpace (cell x)] (μ : Measure (cell x)) [μ.IsHaarMeasure],
    μ ((KO k (Fin n)).subgroupOf (cell x)) = 1 →
    Integrable (fun u : cell x => φ (x⁻¹ * u)) μ ∧
      ∫ u : cell x, φ (x⁻¹ * u) ∂μ =
        ∏ i, ∏ j with i < j ∧ w j < w i, cSL (resCard k) ((α i : ℂ) / α j)

section Unitary

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

def cellU {σ : L →+* L} {n : ℕ} (x : GU σ n) : Subgroup (GU σ n) :=
  (cell (x : GL (Fin n) L)).subgroupOf (GU σ n)

def FormulaU (σ : L →+* L) (q : ℕ) : Prop :=
  ∀ (n : ℕ) (α : Fin (n / 2) → ℂˣ) (φ : GU σ n → ℂ), IsSphericalU q (fun i => (α i : ℂ)) φ → φ 1 = 1 →
  ∀ (w : Equiv.Perm (Fin n)) (x : GU σ n), x ∈ KU σ n → IsWeylRep w (x : GL (Fin n) L) →
    (∀ i j, i < j → w (lo j) < w (lo i) → ‖(α i : ℂ) / α j‖ < 1) →
    (∀ i j, i < j → w (lo j).rev < w (lo i) → ‖(α i : ℂ) * α j‖ < 1) →
    (∀ i, w (lo i).rev < w (lo i) → ‖(α i : ℂ)‖ < 1) →
  ∀ [MeasurableSpace (cellU x)] [BorelSpace (cellU x)] (μ : Measure (cellU x)) [μ.IsHaarMeasure],
    μ ((KU σ n).subgroupOf (cellU x)) = 1 →
    Integrable (fun u : cellU x => φ (x⁻¹ * u)) μ ∧
      ∫ u : cellU x, φ (x⁻¹ * u) ∂μ =
        (∏ i, ∏ j with i < j ∧ w (lo j) < w (lo i), cSL ((q : ℂ) ^ 2) ((α i : ℂ) / α j)) *
        (∏ i, ∏ j with i < j ∧ w (lo j).rev < w (lo i), cSL ((q : ℂ) ^ 2) ((α i : ℂ) * α j)) *
        ∏ i with w (lo i).rev < w (lo i), if Even n then cSL q (α i) else cSU q (α i)

end Unitary

end WeylCell

namespace Published

open WeylCell

def GindikinKarpelevich : Prop :=
  (∀ (k : Type) [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    FormulaGL k) ∧
  ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L)
    (q : ℕ), IsUnramInv ϖ σ q → FormulaU σ q

end Published

namespace WeylCell

theorem exists_haar {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {K N : Subgroup G}
    (ho : IsOpen (K : Set G)) (hc : IsCompact (K : Set G)) (hN : IsClosed (N : Set G))
    [MeasurableSpace N] [BorelSpace N] : ∃ μ : Measure N, μ.IsHaarMeasure ∧ μ (K.subgroupOf N) = 1 := by
  have h1 : IsOpen (K.subgroupOf N : Set N) := ho.preimage continuous_subtype_val
  have h2 : IsCompact (K.subgroupOf N : Set N) := hN.isClosedEmbedding_subtypeVal.isCompact_preimage hc
  let P : TopologicalSpace.PositiveCompacts N := ⟨⟨_, h2⟩, by
    rw [show interior ((⟨_, h2⟩ : TopologicalSpace.Compacts N).carrier) = (K.subgroupOf N : Set N) from h1.interior_eq]
    exact ⟨1, one_mem _⟩⟩
  haveI : LocallyCompactSpace N := h2.locallyCompactSpace_of_mem_nhds_of_group (h1.mem_nhds (one_mem _))
  exact ⟨Measure.haarMeasure P, inferInstance, Measure.haarMeasure_self⟩

theorem exists_data_U {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] {ϖ : L}
    {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) (n : ℕ) (α : Fin (n / 2) → ℂˣ) (w : Equiv.Perm (Fin n))
    (hw : ∀ i, w i.rev = (w i).rev) :
    (∃ φ : GU σ n → ℂ, IsSphericalU q (fun i => (α i : ℂ)) φ ∧ φ 1 = 1) ∧
      (∃ x : GU σ n, x ∈ KU σ n ∧ IsWeylRep w (x : GL (Fin n) L)) ∧
      ∀ (x : GU σ n) [MeasurableSpace (cellU x)] [BorelSpace (cellU x)],
        ∃ μ : Measure (cellU x), μ.IsHaarMeasure ∧ μ ((KU σ n).subgroupOf (cellU x)) = 1 := by
  obtain ⟨ho, hc⟩ := LFun.IntPtsUnitary.isOpen_isCompact_KU L ϖ σ q n h
  obtain ⟨φ, hφ, h1, -⟩ := Final.SphericalExistsU L ϖ σ q n (n / 2) h (by omega) (by omega) (fun i => (α i : ℂ))
    fun i => (α i).ne_zero
  have hx : permRep L w ∈ GU σ n := by
    rw [LGrp.mem_GU_iff]
    intro i j
    rw [← map_inv, permRep_apply, permRep_apply, hw, apply_ite σ, map_one, map_zero]
    simp only [Fin.rev_inj, Equiv.Perm.eq_inv_iff_eq, eq_comm (a := j)]
  refine ⟨⟨φ, hφ, h1⟩, ⟨⟨_, hx⟩, ⟨hx, permRep _ w, ?_⟩, isWeylRep_permRep w⟩,
    fun x _ _ => exists_haar ho hc ((isClosed_cell _).preimage continuous_subtype_val)⟩
  ext i j
  show (intL L).subtype ((permRep _ w).val i j) = (permRep L w).val i j
  simp only [permRep_apply, apply_ite (intL L).subtype, map_one, map_zero]

end WeylCell

end GlobalTheory

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LbH0EqChiStructureModuleOfKrullDimZero
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.QCoh GlobalTheory.CechPic

namespace GlobalTheory.NefNumericsModel

section General
variable {k : Type} [Field k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)]

theorem lbH0_eq_chi_structureModule_of_krullDim_zero (hp : IsProjOver (strHom k X)) (hD : topologicalKrullDim X = (0 : ℕ))
    {L : LB X} (hL : L.IsLB) : (lbH0 k L : ℤ) = chi k (structureModule X) := by
  have : AlgebraicGeometry.IsNoetherian X := isNoetherian_of_isProjOver hp
  have h0 : suppDim (structureModule X) ≤ 0 := by
    unfold suppDim
    exact (topologicalKrullDim_subspace_le _ _).trans (by rw [hD]; simp)
  have : IsFiniteQC (twist (structureModule X) L) := Twist.isFiniteQC_twist hL
  have h1 : suppDim (twist (structureModule X) L) ≤ 0 := by
    rw [Twist.suppDim_twist hL]; exact h0
  rw [lineBundleGlobalSectionsDim_def, ← chi_eq_hdim_zero_of_suppDim_le_zero k h1, chi_twist_of_suppDim_le_zero k h0 hL]

theorem product_nonneg_zero (hp : IsProjOver (strHom k X)) (hD : topologicalKrullDim X = (0 : ℕ))
    (N : Fin 0 → LB X) : 0 ≤ interNum k (structureModule X) N := by
  rw [interNum_of_isEmpty, ← lbH0_eq_chi_structureModule_of_krullDim_zero hp hD (LB.isLB_triv X)]
  exact Int.natCast_nonneg _

theorem riemannRoch_zero (hp : IsProjOver (strHom k X)) (hD : topologicalKrullDim X = (0 : ℕ))
    {L : LB X} (hL : L.IsLB) :
    (fun m : ℕ => (lbH0 k (lbPow L m) : ℝ) - (topSelfIntersection k L 0 : ℝ) * (m : ℝ) ^ 0 / (0 : ℕ).factorial)
      =O[atTop] fun m : ℕ => (m : ℝ) ^ (((0 : ℕ) : ℤ) - 1) := by
  have h : (fun m : ℕ => (lbH0 k (lbPow L m) : ℝ) - (topSelfIntersection k L 0 : ℝ) * (m : ℝ) ^ 0 /
      (0 : ℕ).factorial) = fun _ => 0 := by
    funext m
    have e := lbH0_eq_chi_structureModule_of_krullDim_zero hp hD (isLB_lbPow hL m)
    rw [topSelf_zero, ← e]
    simp
  rw [h]
  exact isBigO_zero _ _

theorem product_nonneg_curve [IsIntegral X] (hp : IsProjOver (strHom k X))
    (hD : topologicalKrullDim X = (1 : ℕ)) (N : Fin 1 → LB X) (hN : ∀ i, IsNef k (N i)) :
    0 ≤ interNum k (structureModule X) N := by
  have hpr : IsProper (strHom k X) := ((isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hp).1
  have e : N = ![N 0] := by
    funext i; fin_cases i; rfl
  rw [e, ← interNumOn_id]
  exact (isNef_iff_isClosedImmersion.1 (hN 0)).2 X (𝟙 X) inferInstance inferInstance
    (by rw [hD]; rfl) (by rw [Category.id_comp]; exact hpr)

end General

section Space
open ProjSpace
variable (k : Type) [Field k]

theorem selfIntersection_O1 (N : ℕ) : topSelfIntersection k (O1 k N) N = 1 := by
  have hc : ∀ j : ℕ, chi k (twistZ (structureModule (PSpace k N)) (O1 k N) (-(j : ℤ))) =
      Ring.choose (-(j : ℤ) + N) N := fun j => ProjCoh.chi_sheafO k N _
  rw [topSelf_def, interNum_const_eq_sum k _ (O1_isLB k N) N, Finset.sum_eq_single 0]
  · rw [hc]
    simp [Ring.choose_natCast]
  · intro j hj hj0
    have hjN : j ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    have hn : -(j : ℤ) + N = ((N - j : ℕ) : ℤ) := by
      rw [Nat.cast_sub hjN]; ring
    rw [hc, hn, Ring.choose_natCast, Nat.choose_eq_zero_of_lt (show N - j < N by omega)]
    simp
  · intro h
    exact absurd (Finset.mem_range.2 (Nat.succ_pos N)) h

theorem big_iff_space (N : ℕ) :
    (IsBig k (O1 k N) ↔ 0 < topSelfIntersection k (O1 k N) N) ∧
    (IsBig k (LB.triv (PSpace k (N + 1))) ↔ 0 < topSelfIntersection k (LB.triv (PSpace k (N + 1))) (N + 1)) := by
  refine ⟨iff_of_true (isBig_twistingSheaf k N) (by rw [selfIntersection_O1 k N]; exact one_pos),
    iff_of_false (triv_nef_not_big k N).2.2 ?_⟩
  rw [topSelf_def, interNum_eq_zero_of_cls_eq_zero k _
    (L := fun _ : Fin (N + 1) => LB.triv (PSpace k (N + 1))) (fun _ => LB.isLB_triv _) 0 (cls_triv _)]
  exact lt_irrefl 0

theorem riemannRoch_line :
    (fun m : ℕ => (lbH0 k (lbPow (O1 k 1) m) : ℝ) -
      (topSelfIntersection k (O1 k 1) 1 : ℝ) * (m : ℝ) ^ 1 / (1 : ℕ).factorial)
      =O[atTop] fun m : ℕ => (m : ℝ) ^ (((1 : ℕ) : ℤ) - 1) := by
  have h : (fun m : ℕ => (lbH0 k (lbPow (O1 k 1) m) : ℝ) -
      (topSelfIntersection k (O1 k 1) 1 : ℝ) * (m : ℝ) ^ 1 / (1 : ℕ).factorial) = fun _ => 1 := by
    funext m
    rw [sectionDim_twistingSheaf_pow, selfIntersection_O1 k 1]
    simp
  have h' : (fun m : ℕ => (m : ℝ) ^ (((1 : ℕ) : ℤ) - 1)) = fun _ => 1 := by
    funext m; simp
  rw [h, h']

theorem riemannRoch_plane :
    (fun m : ℕ => (lbH0 k (lbPow (O1 k 2) m) : ℝ) -
      (topSelfIntersection k (O1 k 2) 2 : ℝ) * (m : ℝ) ^ 2 / (2 : ℕ).factorial)
      =O[atTop] fun m : ℕ => (m : ℝ) ^ (((2 : ℕ) : ℤ) - 1) := by
  have h : ∀ m : ℕ, (lbH0 k (lbPow (O1 k 2) m) : ℝ) -
      (topSelfIntersection k (O1 k 2) 2 : ℝ) * (m : ℝ) ^ 2 / (2 : ℕ).factorial = (3 * m + 2) / 2 := by
    intro m
    rw [sectionDim_twistingSheaf_pow, selfIntersection_O1 k 2, Nat.cast_choose_two]
    push_cast
    simp [Nat.factorial]
    ring
  refine IsBigO.of_bound 3 ?_
  filter_upwards [eventually_ge_atTop 1] with m hm
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have he : (((2 : ℕ) : ℤ) - 1) = 1 := by norm_num
  rw [h m, he, zpow_one, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    abs_of_nonneg (by positivity)]
  linarith

theorem product_neg_line : interNum k (structureModule (PSpace k 1)) ![dual (O1 k 1)] < 0 := by
  have h1 := O1_isLB k 1
  have hz : (lbZPow (O1 k 1) (-1)).IsLB := Twist.isLB_lbZPow h1 (-1)
  have e : interNum k (structureModule (PSpace k 1)) ![dual (O1 k 1)] =
      interNum k (structureModule (PSpace k 1))
        (fun i : Fin 1 => lbZPow (O1 k 1) ((fun _ : Fin 1 => (-1 : ℤ)) i)) := by
    refine interNum_congr_cls k _ (fun i => ?_) (fun _ => hz) (fun i => ?_)
    · fin_cases i; exact CechPic.isLB_dual h1
    · fin_cases i
      show cls (dual (O1 k 1)) _ = cls (lbZPow (O1 k 1) (-1)) _
      rw [cls_lbZPow h1, eq_neg_of_add_eq_zero_left (CechPic.cls_dual_add h1)]
      simp
  have hp : ∀ n : ℤ, (chi k (twistZ (structureModule (PSpace k 1)) (O1 k 1) n) : ℚ) =
      (Polynomial.X + 1 : Polynomial ℚ).eval (n : ℚ) := by
    intro n
    have hc : chi k (twistZ (structureModule (PSpace k 1)) (O1 k 1) n) =
        Ring.choose (n + (1 : ℕ)) 1 := ProjCoh.chi_sheafO k 1 n
    rw [hc, Ring.choose_one_right]
    simp
  have key := interNum_lbZPow_of_polynomial k (structureModule (PSpace k 1)) h1
    (Polynomial.X + 1) (by compute_degree!) hp (fun _ : Fin 1 => (-1 : ℤ))
  have hq : (interNum k (structureModule (PSpace k 1)) ![dual (O1 k 1)] : ℚ) = -1 := by
    rw [e, key]
    simp [Polynomial.coeff_one]
  have : (interNum k (structureModule (PSpace k 1)) ![dual (O1 k 1)] : ℚ) < 0 := by
    rw [hq]; norm_num
  exact_mod_cast this

end Space

end GlobalTheory.NefNumericsModel
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SerreHolomorphicSections
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.Vanishing

namespace GlobalTheory.Published

def SerreHolomorphicSections : Prop :=
  ∀ (Y : Scheme.{0}) (p : Y ⟶ Sp ℂ) (D : ℕ), SmoothOfRelativeDimension D p → IsProjOver p →
    ∀ (R : AnRead p (RingHom.id ℂ) D) (B : LB Y), B.IsLB →
      Function.Bijective fun s : B.Sec =>
        (⟨secVal p (RingHom.id ℂ) s, R.secVal_mem_holSec s⟩ : R.holSec B)

section BaseChange

variable {k k' : Type} [CommRing k] [CommRing k'] {Y Y' : Scheme.{0}} {p : Y ⟶ Sp k} {q : Y' ⟶ Sp k'}
  {r : Y' ⟶ Y} {σ : k →+* ℂ} {τ : k' →+* ℂ} {D D' : ℕ} {m : CxPts q τ → CxPts p σ} {B : LB Y}

variable (r m B) in

def pullVal : (B.ι → CxPts p σ → ℂ) →ₗ[ℂ] ((B.pull r).ι → CxPts q τ → ℂ) where
  toFun s J z := s (J PUnit.unit) (m z)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem pullVal_injective (hb : Function.Surjective m) : Function.Injective (pullVal r m B) :=
  fun _ _ h => funext₂ fun i y => by
    obtain ⟨z, rfl⟩ := hb y
    exact congrFun₂ h (fun _ => i) z

theorem mem_ptsIn_pull (hm : ∀ z, (m z).1 = z.1 ≫ r) {J : (B.pull r).ι} {z : CxPts q τ} :
    z ∈ ptsIn q τ ((B.pull r).U J) ↔ m z ∈ ptsIn p σ (B.U (J PUnit.unit)) := by
  rw [← mem_ptsIn_preimage hm, mem_ptsIn, mem_ptsIn]
  exact mem_pull

theorem pullVal_mem_holSec (hm : ∀ z, (m z).1 = z.1 ≫ r) {R : AnRead p σ D} (R' : AnRead q τ D')
    {s : B.ι → CxPts p σ → ℂ} (hs : s ∈ R.holSec B) : pullVal r m B s ∈ R'.holSec (B.pull r) := by
  refine ⟨⟨fun J J' z h h' => ?_, fun J z h => hs.1.2 _ _ (mt (mem_ptsIn_pull hm).2 h)⟩, fun J =>
    ((hs.2 _).comp_map (isOpen_ptsIn _) hm R').mono fun _ hz => (mem_ptsIn_pull hm).1 hz⟩
  rw [gv_linComb (m := fun _ => m z) (fun _ => hm z) h h', Fintype.prod_unique, zpow_one]
  exact hs.1.1 _ _ _ ((mem_ptsIn_pull hm).1 h) ((mem_ptsIn_pull hm).1 h')

theorem cval_pullChart_ofSec {ρ : k →+* k'} (hm : ∀ z, (m z).1 = z.1 ≫ r) (w : r ≫ p = q ≫ spMap ρ)
    (s : B.Sec) : cval τ (pullChart (W := ⊤) (GlobalTheory.chartPullPull B r) w le_top (H0.ofSec p ⊤ s)) =
      pullVal r m B (secVal p σ s) := funext₂ fun J z => by
  by_cases h : z ∈ ptsIn q τ ((B.pull r).U J)
  · rw [cval_pullChart hm _ _ _ h, cval_ofSec]
    rfl
  · exact ((cval_mem _ _).2 _ _ h).trans ((secVal_mem s).2 _ _ (mt (mem_ptsIn_pull hm).2 h)).symm

end BaseChange

theorem SerreHolomorphicSections.bijective_valC (h : SerreHolomorphicSections) {F : Type} [Field F]
    {Y : Scheme.{0}} {p : Y ⟶ Sp F} {σ : F →+* ℂ} {D : ℕ} [SmoothOfRelativeDimension D p] (hp : IsProjOver p)
    (R : AnRead p σ D) {B : LB Y} (hB : B.IsLB) : Function.Bijective (R.valC B) := by
  let := σ.toAlgebra
  have H := IsPullback.of_hasPullback p (spMap σ)
  generalize Limits.pullback.fst p (spMap σ) = r at H
  generalize Limits.pullback.snd p (spMap σ) = q at H
  have hq := ProjSpace.isProjOver_of_isPullback_spMap σ H hp
  have hs : SmoothOfRelativeDimension D q :=
    have := smoothOfRelativeDimension_isStableUnderBaseChange D
    MorphismProperty.of_isPullback H ‹SmoothOfRelativeDimension D p›
  obtain ⟨m, hm, hb⟩ : ∃ m : CxPts q (RingHom.id ℂ) → CxPts p σ, (∀ z, (m z).1 = z.1 ≫ r) ∧
      Function.Surjective m := ⟨bcMap H.w (RingHom.id ℂ), fun _ => rfl, (bijective_bcMap H _).2⟩
  have hB' := LB.isLB_pull hB r
  have hS := h _ q D hs hq (AnRead.all _ _ D) _ hB'
  have hE := isExtension_pullChart_top (k := F) (E := ℂ) H hB hB' (GlobalTheory.chartPullPull B r) hp hq
  set ι := pullChart (O := ⊤) (W := ⊤) (GlobalTheory.chartPullPull B r) H.w le_top
  let L : SecC p σ B →ₗ[ℂ] H0 q (B.pull r) ⊤ :=
    SecC.lift (ι.toAddMonoidHom.comp (H0.ofSec p ⊤)) fun a s =>
      (congrArg ι (H0.ofSec_smul a s)).trans (map_smulₛₗ ι a _)
  have hL (s) : L (SecC.of p σ s) = ι (H0.ofSec p ⊤ s) := SecC.lift_of _ _ s
  have hc (x) : cval (RingHom.id ℂ) (L x) = pullVal r m B (SecC.val x) := by
    refine LinearMap.eqOn_span' (f := cval (RingHom.id ℂ) ∘ₗ L) (g := pullVal r m B ∘ₗ SecC.val)
      (s := range (SecC.of p σ)) ?_ (SecC.span_range_of.ge Submodule.mem_top)
    rintro _ ⟨s, rfl⟩
    simp only [LinearMap.comp_apply, hL, SecC.val_of]
    exact cval_pullChart_ofSec hm H.w s
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, fun s => ?_⟩
  · have h₀ : L x = 0 := by
      obtain ⟨t, ht⟩ := H0.bijective_ofSec_top.2 (L x)
      have e := hc x
      rw [← ht, cval_ofSec, show SecC.val x = 0 from congrArg Subtype.val hx, map_zero] at e
      rw [← ht, hS.1 (a₁ := t) (a₂ := 0) (Subtype.ext (e.trans (map_zero _).symm)), map_zero]
    have := finite_top hp hB
    let b := Module.finBasis F (H0 p B ⊤)
    choose v hv using fun i => H0.bijective_ofSec_top.2 (b i)
    have hx' : x ∈ Submodule.span ℂ (range fun i => SecC.of p σ (v i)) := by
      refine (SecC.span_range_of.ge.trans (Submodule.span_le.2 ?_)) Submodule.mem_top
      rintro _ ⟨s, rfl⟩
      have e : s = ∑ i, DVR.FlatBC.algX p ⊤ (b.repr (H0.ofSec p ⊤ s) i) • v i :=
        (H0.bijective_ofSec_top (p := p)).1 (by simp only [map_sum, H0.ofSec_smul, hv, b.sum_repr])
      rw [e, map_sum]
      exact Submodule.sum_mem _ fun i _ => by
        rw [SecC.of_smul]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hx'
    simp only [map_sum, map_smul, hL, hv] at h₀
    simp [Fintype.linearIndependent_iff.1 (hE.indep _ b b.linearIndependent) c h₀]
  · obtain ⟨t, ht⟩ := hS.2 ⟨_, pullVal_mem_holSec hm (AnRead.all _ _ D) s.2⟩
    have hr : H0.ofSec q ⊤ t ∈ LinearMap.range L := by
      refine (hE.span.ge.trans (Submodule.span_le.2 ?_)) Submodule.mem_top
      rintro _ ⟨f, rfl⟩
      obtain ⟨u, rfl⟩ := H0.bijective_ofSec_top.2 f
      exact ⟨_, hL u⟩
    obtain ⟨x, hx⟩ := hr
    refine ⟨x, Subtype.ext (pullVal_injective (r := r) hb ((hc x).symm.trans ?_))⟩
    rw [hx, cval_ofSec]
    exact congrArg Subtype.val ht

end GlobalTheory.Published
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelEisensteinDoubled
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling

namespace GlobalTheory.Published

def SiegelEisensteinDoubled : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) →
  ∀ (B : Base F E) (n : ℕ), 1 ≤ n →
  ∀ W : Spc F E n, (∀ i j, σ (W.J j i) = -W.J i j) → W.L.IsLattice E →
    (∀ y, y ∈ W.L ↔ ∀ x ∈ W.L, ∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E (o * form σ W.J y x))) →
    (∀ w, IsCartan (Complex.I • W.J.map (B.emb w).1) (W.θ w)) →
  ∀ W₂ : Spc F E (n + n), W₂.J = dblGram finSumFinEquiv W.J → W₂.L = sumLat finSumFinEquiv W.L W.L →
    (∀ w, W₂.θ w = blkMat finSumFinEquiv (W.θ w) (-W.θ w)) →
  ∀ K : Subgroup (UA σ W₂.J), IsStab B K → IwasawaOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K →
  ∀ χ : Chr F E, IsHecke F E χ →
  ∀ (s₁ : ℂ) (φ : UA σ W₂.J → ℂ), φ ∈ degPSOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K χ s₁ →
    let P : Subgroup (UA σ W₂.J) := siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype
    let f : ℂ → UA σ W₂.J → ℂ := flatOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K φ s₁
    ∃ Ei : ℂ → UA σ W₂.J → ℂ,
      (∀ s : ℂ, (n : ℝ) / 2 < s.re → ∀ g,
        Eis.CosetConv P (ratU σ W₂.J) (f s) g ∧ Ei s g = Eis.cosetSum P (ratU σ W₂.J) (f s) g) ∧
      ∀ s₀ : ℂ, ∃ (k : ℕ) (r : ℝ) (H : ℂ → UA σ W₂.J → ℂ), 0 < r ∧
        (∀ s ∈ Metric.ball s₀ r, s ≠ s₀ → ∀ g, H s g = (s - s₀) ^ k * Ei s g) ∧
        (∀ g, DifferentiableOn ℂ (fun s => H s g) (Metric.ball s₀ r)) ∧
        ContinuousOn (fun x : ℂ × UA σ W₂.J => H x.1 x.2) (Metric.ball s₀ r ×ˢ Set.univ) ∧
        ∃ (C : ℝ) (N : ℕ), ∀ s ∈ Metric.ball s₀ r, ∀ g, ‖H s g‖ ≤ C * (ht g : ℝ) ^ N

end GlobalTheory.Published

end
end

