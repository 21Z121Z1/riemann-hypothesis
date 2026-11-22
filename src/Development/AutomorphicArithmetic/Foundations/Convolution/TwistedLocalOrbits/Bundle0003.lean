import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.Bundle0001
import GroundTheory.LocalFields.Unramified
import GroundTheory.LocalFields.UnramifiedGalois
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.Bundle0001
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.HoweSpace
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.ContractRow
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4HoweTheory.InjMat
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4HoweTheory.Bundle0001
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0007
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.Bundle0003
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.Bundle0002
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.ExtCont

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.Bridge
section
open MeasureTheory ValuativeRel GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets PositivityTheory.Rg.Tf.Loc UpperTheory.ConvolutionTheory.Loc

private theorem iter_eq {k E : Type} [Field k] [Field E] [Algebra k E] (σ : E ≃ₐ[k] E) (j : ℕ) (x : E) :
    (σ : E ≃+* E)^[j] x = (σ ^ j) x := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', ih, pow_succ']; rfl

private theorem mem_range_incl {k E : Type} [Field k] [Field E] [Algebra k E] {n : ℕ} (g : GL (Fin n) E) :
    (∃ y : GL (Fin n) k, incl y = g) ↔
      ∀ i j, (g : Matrix (Fin n) (Fin n) E) i j ∈ Set.range (algebraMap k E) := by
  constructor
  · rintro ⟨y, rfl⟩ i j
    exact ⟨(y : Matrix (Fin n) (Fin n) k) i j, rfl⟩
  · intro h
    choose M hM using h
    have e : (algebraMap k E).mapMatrix (Matrix.of M) = (g : Matrix (Fin n) (Fin n) E) := by
      ext i j
      exact hM i j
    have hd : (Matrix.of M).det ≠ 0 := by
      intro h0
      have h1 := RingHom.map_det (algebraMap k E) (Matrix.of M)
      rw [h0, map_zero, e] at h1
      exact (Matrix.GeneralLinearGroup.det g).ne_zero h1.symm
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd, ?_⟩
    ext i j
    exact hM i j

section

variable (k E : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E]

private theorem closedEmb_alg : Topology.IsClosedEmbedding (algebraMap k E) := by
  let _ := GroundTheory.LocalField.nontriviallyNormedField k
  have := GroundTheory.LocalField.completeSpace_nontriviallyNormedField k
  have := GroundTheory.LocalField.t2Space_of_isNonarchimedeanLocalField E
  exact LinearMap.isClosedEmbedding_of_injective (f := Algebra.linearMap k E)
    (LinearMap.ker_eq_bot.mpr (algebraMap k E).injective)

private theorem closedEmb_incl (n : ℕ) :
    Topology.IsClosedEmbedding (incl : GL (Fin n) k → GL (Fin n) E) := by
  have h := closedEmb_alg k E
  have hM : Topology.IsEmbedding
      ((algebraMap k E).mapMatrix.toMonoidHom : Matrix (Fin n) (Fin n) k →* Matrix (Fin n) (Fin n) E) :=
    Topology.IsEmbedding.piMap (f := fun _ : Fin n => Pi.map fun _ : Fin n => algebraMap k E)
      fun _ => Topology.IsEmbedding.piMap fun _ => h.isEmbedding
  refine ⟨hM.units_map, ?_⟩
  have e : Set.range (incl : GL (Fin n) k → GL (Fin n) E) =
      ⋂ i, ⋂ j, (fun g : GL (Fin n) E => (g : Matrix (Fin n) (Fin n) E) i j) ⁻¹' Set.range (algebraMap k E) := by
    ext g
    simp only [Set.mem_iInter, Set.mem_preimage]
    exact mem_range_incl g
  rw [e]
  refine isClosed_iInter fun i => isClosed_iInter fun j => h.isClosed_range.preimage ?_
  exact Units.continuous_val.matrix_elem i j

private theorem ram_one (h : IsUnramifiedLoc k E) : GroundTheory.LocalField.ramificationIndex k E = 1 := by
  obtain ⟨π, hπ, hmax⟩ := h
  have key : ∀ x : 𝒪[E], x ∈ IsLocalRing.maximalIdeal 𝒪[E] ↔ valuation E (x : E) < 1 := by
    intro x
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      (Valuation.integer.integers (valuation E)).isUnit_iff_valuation_eq_one]
    exact ⟨fun h => lt_of_le_of_ne x.2 h, fun h => h.ne⟩
  have hπk : π ∈ 𝒪[k] := (GroundTheory.LocalField.algebraMap_mem_integer_iff k E π).1 hπ.le
  have hm : (⟨π, hπk⟩ : 𝒪[k]) ∈ IsLocalRing.maximalIdeal 𝒪[k] := by
    intro hu
    exact (key _).2 hπ (hu.map (algebraMap 𝒪[k] 𝒪[E]))
  rw [← GroundTheory.LocalField.isUnramified_iff, ← GroundTheory.LocalField.map_maximalIdeal_eq_iff]
  refine le_antisymm ?_ fun x hx => ?_
  · rw [Ideal.map_le_iff_le_comap]
    intro y hy hu
    exact hy (isUnit_of_map_unit _ _ hu)
  · have hd : algebraMap 𝒪[k] 𝒪[E] ⟨π, hπk⟩ ∣ x :=
      (Valuation.integer.integers (valuation E)).dvd_of_le (hmax _ ((key x).1 hx))
    exact Ideal.mem_of_dvd _ hd (Ideal.mem_map_of_mem _ hm)

private theorem res_move (h : IsUnramifiedLoc k E) (τ : E ≃ₐ[k] E) (hτ : τ ≠ 1) :
    ∃ x, valuation E x ≤ 1 ∧ valuation E (τ x - x) = 1 := by
  by_contra hc
  push Not at hc
  apply hτ
  apply GroundTheory.LocalField.residueAlgEquiv_injective_of_unramified k E (ram_one k E h)
  rw [map_one]
  ext z
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
  rw [GroundTheory.LocalField.residueAlgEquiv_residue, AlgEquiv.one_apply, ← sub_eq_zero, ← map_sub,
    IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    (Valuation.integer.integers (valuation E)).isUnit_iff_valuation_eq_one]
  exact hc x x.2

end

theorem UpperTheory.ConvolutionTheory.Loc.bridge :
    ∀ (k E : Type) [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
        [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
        [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E] (σ : E ≃ₐ[k] E), Cyc (σ : E ≃+* E) (Module.finrank k E) ∧
      (IsUnramifiedLoc k E → (∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) → Unram (σ : E ≃+* E) (Module.finrank k E)) ∧
      ∀ n : ℕ, (∀ g : GL (Fin n) E, sg (σ : E ≃+* E) g = sigmaGL σ g) ∧ (∀ g : GL (Fin n) E, nrm (σ : E ≃+* E) (Module.finrank k E) g = normGL σ g) ∧
        ((∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) → ∀ g : GL (Fin n) E, sigmaGL σ g = g ↔ ∃ y : GL (Fin n) k, incl y = g) ∧
        Topology.IsClosedEmbedding (incl : GL (Fin n) k → GL (Fin n) E) ∧
        iwahori (m := n) E = (GlobalTheory.SmGL.iwahori E (Fin n) : Set (GL (Fin n) E)) := by
  intro k E _ _ _ _ _ _ _ _ _ _ _ _ _ σ
  have hc : Cyc (σ : E ≃+* E) (Module.finrank k E) := by
    refine ⟨fun x => GroundTheory.LocalField.valuation_algEquiv_apply k E σ x, Module.finrank_pos, fun x => ?_⟩
    rw [iter_eq, ← IsGalois.card_aut_eq_finrank, pow_card_eq_one']
    rfl
  refine ⟨hc, fun hu hgen => ⟨hc, fun j hj hj' => ?_⟩, fun n => ⟨fun g => rfl, fun g => ?_, fun hgen g => ?_,
    closedEmb_incl k E n, ?_⟩⟩
  · simp only [iter_eq]
    refine res_move k E hu _ (pow_ne_one_of_lt_orderOf hj.ne' ?_)
    rwa [orderOf_eq_card_of_forall_mem_zpowers hgen, IsGalois.card_aut_eq_finrank]
  · unfold nrm normGL twNorm
    congr 2
  · rw [mem_range_incl]
    constructor
    · intro h i j
      have hσ : σ ∈ MulAction.stabilizer (E ≃ₐ[k] E) ((g : Matrix (Fin n) (Fin n) E) i j) :=
        congrArg (fun x : GL (Fin n) E => (x : Matrix (Fin n) (Fin n) E) i j) h
      have := (IsGalois.mem_bot_iff_fixed ((g : Matrix (Fin n) (Fin n) E) i j)).mpr fun τ =>
        (Subgroup.zpowers_le.mpr hσ) (hgen τ)
      rwa [IntermediateField.mem_bot] at this
    · intro h
      ext i j
      obtain ⟨y, hy⟩ := h i j
      show σ ((g : Matrix (Fin n) (Fin n) E) i j) = _
      rw [← hy, AlgEquiv.commutes]
  · ext g
    rw [SetLike.mem_coe, GlobalTheory.SmGL.mem_iwahori]
    rfl
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.ConjDesc
section
open MeasureTheory ValuativeRel GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets PositivityTheory.Rg.Tf.Loc UpperTheory.ConvolutionTheory.Loc

theorem UpperTheory.ConvolutionTheory.Loc.conjDesc :
    ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (n : ℕ) (γ γ' : GL (Fin n) k), IsRegSemisimple γ →
      (∃ h : GL (Fin n) E, incl γ' = h * incl γ * h⁻¹) → ∃ y : GL (Fin n) k, γ' = y * γ * y⁻¹ := by
  intro k E _ _ _ n γ γ' hγ ⟨h, hh⟩
  have hc : (γ' : Matrix (Fin n) (Fin n) k).charpoly = (γ : Matrix (Fin n) (Fin n) k).charpoly := by
    apply Polynomial.map_injective (algebraMap k E) (algebraMap k E).injective
    rw [← Matrix.charpoly_map, ← Matrix.charpoly_map]
    have e := congrArg (fun g : GL (Fin n) E => (g : Matrix (Fin n) (Fin n) E).charpoly) hh
    simp only [Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj] at e
    exact e
  obtain ⟨x, hx⟩ := (UpperTheory.ConvolutionTheory.D.conjSep k k n _ hγ).1 _ hc
  refine ⟨x⁻¹, ?_⟩
  have : γ * x = x * γ' := Units.ext hx
  rw [inv_inv, mul_assoc, this, inv_mul_cancel_left]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.ContractI
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.Loc

section

variable {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] {n : ℕ}

private theorem mem_iw {g : GL (Fin n) E} : g ∈ iwahori E (Fin n) ↔
    ((∀ i j, valuation E (g.val i j) ≤ 1) ∧ ∀ i j, valuation E (g⁻¹.val i j) ≤ 1) ∧
      ∀ i j, j < i → valuation E (g.val i j) < 1 := by
  rw [mem_iwahori, GlobalTheory.SplitFlip.mem_KO_iff]
  rfl

private theorem diag_one {g : GL (Fin n) E} (hg : g ∈ iwahori E (Fin n)) (i : Fin n) :
    valuation E (g.val i i) = 1 := by
  obtain ⟨⟨h1, h2⟩, h3⟩ := mem_iw.1 hg
  have h4 := (mem_iw.1 (inv_mem hg)).2
  refine le_antisymm (h1 i i) (not_lt.1 fun h => ?_)
  have : valuation E (∑ l, g.val i l * g⁻¹.val l i) < 1 := by
    refine Valuation.map_sum_lt _ one_ne_zero fun l _ => ?_
    rw [map_mul]
    rcases lt_trichotomy l i with hl | hl | hl
    · exact (mul_le_of_le_one_right' (h2 l i)).trans_lt (h3 i l hl)
    · subst hl
      exact (mul_le_of_le_one_right' (h2 l l)).trans_lt h
    · exact (mul_le_of_le_one_left' (h1 i l)).trans_lt (h4 l i hl)
  rw [← mul_apply, g.mul_inv] at this
  simp at this

private theorem sg_mem {σ : E ≃+* E} (hσ : Isom σ) {g : GL (Fin n) E} (hg : g ∈ iwahori E (Fin n)) :
    sg σ g ∈ iwahori E (Fin n) := by
  obtain ⟨⟨h1, h2⟩, h3⟩ := mem_iw.1 hg
  rw [mem_iw, ← map_inv]
  exact ⟨⟨fun i j => (hσ _).le.trans (h1 i j), fun i j => (hσ _).le.trans (h2 i j)⟩,
    fun i j h => (hσ _).le.trans_lt (h3 i j h)⟩

end

theorem UpperTheory.ConvolutionTheory.Loc.contractI :
    ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) (σ : E ≃+* E), Isom σ → ∀ t : Fin n → Eˣ, Strict t → ∀ g ∈ iwahoriCoset t,
      ∃ k ∈ iwahori E (Fin n), ∃ s ∈ torusO E (Fin n), g = k⁻¹ * diagT E (Fin n) (t * s) * sg σ k := by
  rintro E _ _ _ _ n σ hσ t ht g ⟨a, ha, b, hb, rfl⟩
  have hb' : b * sg σ a ∈ iwahori E (Fin n) := mul_mem hb (sg_mem hσ ha)
  obtain ⟨⟨h1, h2⟩, h3⟩ := mem_iw.1 hb'
  have hu : uniformizer E < 1 := uniformizer_lt_one
  have ht' : ∀ j l, j < l → valuation E ((t j : E) / t l) ≤ uniformizer E := fun j l h => by
    rw [le_uniformizer_iff, map_div₀, div_lt_one₀ (zero_le.trans_lt (ht j l h))]
    exact ht j l h
  obtain ⟨k, hk, hk', s, hs, e⟩ := exists_conj hσ t le_rfl hu ht' (b * sg σ a) h1 h2 (diag_one hb')
    (diag_one (inv_mem hb')) (fun j l h => le_uniformizer_iff.2 (h3 j l h)) (fun j l h => by
      rw [map_mul]
      exact (mul_le_of_le_one_right' (h2 j l)).trans (ht' j l h))
  have hkI : k ∈ iwahori E (Fin n) := by
    refine mem_iw.2 ⟨⟨fun i j => ?_, hk'⟩, fun i j h => by simpa [one_apply_ne h.ne'] using (hk i j).trans_lt hu⟩
    rw [← sub_add_cancel (k.val i j) ((1 : Matrix (Fin n) (Fin n) E) i j)]
    refine Valuation.map_add_le _ ((hk i j).trans hu.le) ?_
    rw [one_apply]
    split_ifs <;> simp
  refine ⟨k * a⁻¹, mul_mem hkI (inv_mem ha), s, inv_mem_iff.1 fun i => ?_, ?_⟩
  · have hd := diag_one (inv_mem hb') i
    show valuation E (((s i)⁻¹ : Eˣ) : E) = 1
    rw [← sub_add_cancel (((s i)⁻¹ : Eˣ) : E) ((b * sg σ a)⁻¹.val i i), Valuation.map_add_eq_of_lt_right, hd]
    exact hd ▸ (hs i).trans_lt hu
  · calc a * diagT E (Fin n) t * b = a * (diagT E (Fin n) t * (b * sg σ a)) * (sg σ a)⁻¹ := by group
      _ = _ := by rw [e, map_mul (sg σ), map_inv]; group
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.HoweInj
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.Loc UpperTheory.V.Z.Tf.L4

section

variable {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] {n : ℕ}

private theorem conj_sub (ϖ : Eˣ) (c : ℤ) (g : GL (Fin n) E) (i j : Fin n) :
    ((diagT E (Fin n) (fun i => ϖ ^ (c * (i : ℕ))) * g * (diagT E (Fin n) (fun i => ϖ ^ (c * (i : ℕ))))⁻¹ : GL (Fin n) E) :
      Matrix (Fin n) (Fin n) E) i j - (1 : Matrix (Fin n) (Fin n) E) i j =
      ((ϖ ^ (c * (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ))) : Eˣ) : E) * ((g : Matrix (Fin n) (Fin n) E) i j - (1 : Matrix (Fin n) (Fin n) E) i j) := by
  rw [DiscreteGroups.sglob.DzType.diag_conj_apply, mul_right_comm, ← Units.val_mul, ← _root_.zpow_sub, ← mul_sub, mul_sub ((ϖ ^ _ : Eˣ) : E)]
  congr 1
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.one_apply_ne h]

private theorem conj_mem (ϖ : Eˣ) (a c : ℤ) (g : GL (Fin n) E) :
    diagT E (Fin n) (fun i => ϖ ^ (c * (i : ℕ))) * g * (diagT E (Fin n) (fun i => ϖ ^ (c * (i : ℕ))))⁻¹ ∈ howeSet n ϖ a c ↔
      Bd (valuation E ((ϖ ^ a : Eˣ) : E)) ((g : Matrix (Fin n) (Fin n) E) - 1) := by
  refine forall_congr' fun i => forall_congr' fun j => ?_
  rw [conj_sub, add_comm a, _root_.zpow_add, Units.val_mul, map_mul, map_mul, Matrix.sub_apply]
  exact mul_le_mul_iff_right₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 (Units.ne_zero _)))

private theorem conj_sd (ϖ : Eˣ) (c : ℤ) (g : GL (Fin n) E) :
    GlobalTheory.Whittaker.superDiag (diagT E (Fin n) (fun i => ϖ ^ (c * (i : ℕ))) * g * (diagT E (Fin n) (fun i => ϖ ^ (c * (i : ℕ))))⁻¹) =
      ((ϖ ^ (-c) : Eˣ) : E) * GlobalTheory.Whittaker.superDiag g := by
  simp only [GlobalTheory.Whittaker.superDiag, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => ?_
  have h := (Finset.mem_filter.1 hj).2
  rw [DiscreteGroups.sglob.DzType.diag_conj_apply, mul_right_comm, ← Units.val_mul, ← _root_.zpow_sub, h]
  congr 3
  push_cast
  ring

private theorem whit_eq (ψ : AddChar E Circle) (u : unipB E (Fin n)) :
    ((GlobalTheory.LocGL.whitChar ψ n u : ℂˣ) : ℂ) = (ψ (GlobalTheory.Whittaker.superDiag (u : GL (Fin n) E)) : ℂ) := by
  change ((ψ _ : Circle) : ℂ) = _
  congr 2
  simp only [GlobalTheory.Whittaker.superDiag, Finset.sum_filter]
  exact Fintype.sum_prod_type _

end

theorem UpperTheory.ConvolutionTheory.Loc.howeInj :
    ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) E) V), IsSmooth π → ∀ ϖ : Eˣ, valuation E (ϖ : E) = uniformizer E → ∀ a c : ℤ, 1 ≤ a →
      ∀ ψ : AddChar E Circle, HasConductor ψ (ϖ ^ (2 * a - c)) → ∀ v ∈ howeSpace π ψ (howeSet n ϖ a c),
        v ∈ twKer π (unipB E (Fin n)) (GlobalTheory.LocGL.whitChar ψ n) → v = 0 := by
  intro E _ _ _ _ n V _ _ π hs ϖ hϖ a c ha ψ hψ v hv hk
  obtain ⟨J, hJ, ho, hc⟩ := howeGroup E n ϖ hϖ a c ha
  have hmem : ∀ x, x ∈ J ↔ x ∈ howeSet n ϖ a c := fun x => by rw [← hJ]; rfl
  refine eq_zero_of_no_intertwining hs J (unipB E (Fin n)) hc ho DiscreteGroups.sglob.DzType.exists_compact_unip
    (fun x => (ψ (GlobalTheory.Whittaker.superDiag x) : ℂ)) (howeChar E n ϖ hϖ a c ha ψ hψ).1.continuous (fun x hx y hy => ?_)
    (fun u hu hn => ?_) v (fun k h => hv k ((hmem k).1 h)) (Submodule.span_mono ?_ hk)
  · have := congrArg Units.val (map_mul (GlobalTheory.LocGL.whitChar ψ n) ⟨x, hx⟩ ⟨y, hy⟩)
    rwa [Units.val_mul, whit_eq, whit_eq, whit_eq] at this
  · obtain ⟨d, hd⟩ : ∃ d, d = diagT E (Fin n) (fun i => ϖ ^ (c * (i : ℕ))) := ⟨_, rfl⟩
    have hu' : d⁻¹ * u * d ∈ unipB E (Fin n) := by
      have e : diagT E (Fin n) (fun i => (ϖ ^ (c * (i : ℕ)))⁻¹) = d⁻¹ := by rw [hd, ← map_inv]; rfl
      have := DiscreteGroups.sglob.DzType.diag_conj_mem_unipB (fun i => (ϖ ^ (c * (i : ℕ)))⁻¹) hu
      rwa [e, inv_inv] at this
    have hp : valuation E ((ϖ ^ a : Eˣ) : E) < 1 := by
      rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hϖ]
      exact zpow_lt_one₀ (zero_lt_iff.2 uniformizer_ne_zero) uniformizer_lt_one (by omega)
    obtain ⟨k, h1, h2, h3⟩ := not_intertwine (ϖ ^ a) hp (ψ.mulShift ((ϖ ^ (-c) : Eˣ) : E)) (fun x hx => by
      have h0 : 0 < valuation E ((ϖ ^ (-c) : Eˣ) : E) := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 (Units.ne_zero _))
      have h4 : ¬ valuation E (((ϖ ^ (-c) : Eˣ) : E) * x) ≤ valuation E ((ϖ ^ (2 * a - c) : Eˣ) : E) := by
        rw [show 2 * a - c = -c + (a + a) by ring, _root_.zpow_add, _root_.zpow_add, Units.val_mul, Units.val_mul, map_mul, map_mul _ ((ϖ ^ (-c) : Eˣ) : E),
          mul_le_mul_iff_right₀ h0]
        exact not_le.2 hx
      rw [← hψ] at h4
      push Not at h4
      obtain ⟨y, h5, h6⟩ := h4
      refine ⟨((ϖ ^ (-c) : Eˣ) : E)⁻¹ * y, ?_, by rwa [AddChar.mulShift_apply, mul_inv_cancel_left₀ (Units.ne_zero _)]⟩
      rwa [map_mul, map_inv₀, inv_mul_le_iff₀ h0, ← map_mul]) (d⁻¹ * u * d) hu' fun h => hn (by
        have := (conj_mem ϖ a c _).2 h
        rw [← hd, show d * (d⁻¹ * u * d) * d⁻¹ = u by group] at this
        exact (hmem u).2 this)
    have e : u * (d * k * d⁻¹) * u⁻¹ = d * (d⁻¹ * u * d * k * (d⁻¹ * u * d)⁻¹) * d⁻¹ := by group
    refine ⟨d * k * d⁻¹, (hmem _).2 (hd ▸ (conj_mem ϖ a c k).2 h1), ?_, fun h => h3 (Circle.ext ?_)⟩
    · rw [e]
      generalize d⁻¹ * u * d * k * (d⁻¹ * u * d)⁻¹ = z at h2
      exact (hmem _).2 (hd ▸ (conj_mem ϖ a c z).2 h2)
    · rw [e] at h
      generalize d⁻¹ * u * d * k * (d⁻¹ * u * d)⁻¹ = z at h
      simp only [hd, conj_sd] at h
      exact h
  · rintro w ⟨u, x, rfl⟩
    exact ⟨u, u.2, x, by rw [whit_eq]⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.NormInj
section
open MeasureTheory ValuativeRel GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets PositivityTheory.Rg.Tf.Loc UpperTheory.ConvolutionTheory.Loc

private theorem inj {k E : Type} [Field k] [Field E] [Algebra k E] [FiniteDimensional k E] [IsGalois k E] (σ : E ≃ₐ[k] E)
    (hσ : ∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) {n : ℕ} (δ δ' : GL (Fin n) E) (h : IsTwRegSemisimple σ δ)
    (e : (normGL σ δ' : Matrix (Fin n) (Fin n) E).charpoly = (normGL σ δ : Matrix (Fin n) (Fin n) E).charpoly) :
    TwConjugate (sigmaGL σ) δ δ' := by
  have hn : ∀ x : GL (Fin n) E, UpperTheory.ConvolutionTheory.D.nm σ (Module.finrank k E) x = normGL σ x := fun x => by
    unfold UpperTheory.ConvolutionTheory.D.nm normGL twNorm
    congr 2
    funext i
    rw [← sigmaGL_pow]
    rfl
  obtain ⟨x, hx⟩ := UpperTheory.ConvolutionTheory.D.nmInj k E σ _ (UpperTheory.ConvolutionTheory.D.galField k E σ hσ) n δ δ' (by rw [hn]; exact h) (by rw [hn, hn]; exact e)
  exact ⟨x, hx⟩

theorem UpperTheory.ConvolutionTheory.Loc.normInj :
    ∀ (k E : Type) [Field k] [CharZero k] [Field E] [Algebra k E] [FiniteDimensional k E] [IsGalois k E] (σ : E ≃ₐ[k] E),
      (∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) → ∀ (n : ℕ) (γ : GL (Fin n) k), IsRegSemisimple γ → ∀ δ δ' : GL (Fin n) E,
        IsNormOf σ δ γ → IsNormOf σ δ' γ → TwConjugate (sigmaGL σ) δ δ' := by
  intro k E _ _ _ _ _ _ σ hσ n γ hγ δ δ' h h'
  have key : ∀ x : GL (Fin n) E, IsNormOf σ x γ → (normGL σ x : Matrix (Fin n) (Fin n) E).charpoly =
      (γ : Matrix (Fin n) (Fin n) k).charpoly.map (algebraMap k E) := fun x ⟨g, hg⟩ => by
    rw [hg, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj, ← Matrix.charpoly_map]
    rfl
  refine inj σ hσ δ δ' ?_ ((key _ h').trans (key _ h).symm)
  unfold IsTwRegSemisimple
  rw [key _ h]
  exact Polynomial.Separable.map hγ
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.RigidNear
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.Loc

private theorem UpperTheory.ConvolutionTheory.Loc.nrm_fixed_eq_pow {E : Type} [Field E] {n : ℕ} (σ : E ≃+* E) (q : ℕ) (u : GL (Fin n) E)
    (hu : sg σ u = u) : nrm σ q u = u ^ q := by
  induction q with
  | zero => simp [nrm]
  | succ q ih => rw [nrm_succ, ih, Function.iterate_fixed hu, pow_succ]

theorem UpperTheory.ConvolutionTheory.Loc.rigidNear :
    ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) (σ : E ≃+* E) (q : ℕ), Cyc σ q → ∀ r : ValueGroupWithZero E, r < valuation E (q : E) →
      ∀ u ∈ ball n r, ∀ u' ∈ ball n r, sg σ u = u → sg σ u' = u' → ∀ g : GL (Fin n) E, g⁻¹ * u * sg σ g = u' → sg σ g = g := by
  intro E _ _ _ _ n σ q hc r hr u hu u' hu' h h' g hg
  have h1 : g⁻¹ * u ^ q * g = u' ^ q := by
    rw [← UpperTheory.ConvolutionTheory.Loc.nrm_fixed_eq_pow σ q u h, ← UpperTheory.ConvolutionTheory.Loc.nrm_fixed_eq_pow σ q u' h', ← hg, nrm_conj hc.ord]
  have h2 := UpperTheory.ConvolutionTheory.Loc.rootConj E n q r hr u hu u' hu' g h1
  exact mul_left_cancel (hg.trans h2.symm)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.TwOrbConj
section
open MeasureTheory ValuativeRel GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets PositivityTheory.Rg.Tf.Loc UpperTheory.ConvolutionTheory.Loc

theorem UpperTheory.ConvolutionTheory.Loc.twOrbConj :
    ∀ (k E : Type) [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
        [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
        [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E] (σ : E ≃ₐ[k] E) (n : ℕ) [MeasurableSpace (GL (Fin n) E)] [BorelSpace (GL (Fin n) E)] (μE : Measure (GL (Fin n) E)), μE.IsHaarMeasure →
      ∀ (δ g : GL (Fin n) E) (μ : Measure (twCent (sigmaGL σ) δ)) (μ' : Measure (twCent (sigmaGL σ) (twConj (sigmaGL σ) g δ))),
        IsTwRegSemisimple σ δ → μ.IsHaarMeasure → μ'.IsHaarMeasure →
        Measure.map (fun x : twCent (sigmaGL σ) δ => g⁻¹ * (x : GL (Fin n) E) * g) μ =
          Measure.map (fun x : twCent (sigmaGL σ) (twConj (sigmaGL σ) g δ) => (x : GL (Fin n) E)) μ' →
        ∀ φ ∈ SB (GL (Fin n) E), twOrbIntegralC (sigmaGL σ) μE (twConj (sigmaGL σ) g δ) μ' φ = twOrbIntegralC (sigmaGL σ) μE δ μ φ := by
  intro k E _ _ _ _ _ _ _ _ _ _ _ _ _ σ n _ _ μE hμE δ g μ μ' hδ hμ hμ' hmap φ hφ
  obtain ⟨h1, h2, h3, -, -⟩ := UpperTheory.V.Z.Tf.Orb.gLTop E n
  have hc : Continuous (sigmaGL σ : GL (Fin n) E → GL (Fin n) E) :=
    ((UpperTheory.V.Z.Tf.Orb.extCont k E).2.2 n).2 σ
  have htw : Continuous fun x : GL (Fin n) E => twConj (sigmaGL σ) x δ :=
    (continuous_inv.mul continuous_const).mul hc
  have hclosed : IsClosed (twCent (sigmaGL σ) δ : Set (GL (Fin n) E)) := isClosed_eq htw continuous_const
  have hℓ : σ ^ Module.finrank k E = 1 := by
    rw [← IsGalois.card_aut_eq_finrank]; exact pow_card_eq_one'
  have hθ : (sigmaGL σ : Monoid.End (GL (Fin n) E)) ^ Module.finrank k E = 1 := by
    rw [← sigmaGL_pow, hℓ, sigmaGL_one]
  have hcomm : ∀ a ∈ twCent (sigmaGL σ) δ, ∀ b ∈ twCent (sigmaGL σ) δ, Commute a b := by
    intro a ha b hb
    have key : ∀ c ∈ twCent (sigmaGL σ) δ, Commute (c : Matrix (Fin n) (Fin n) E) (normGL σ δ : GL (Fin n) E) := by
      intro c hc
      have := congrArg Units.val (twCent_commute_twNorm (sigmaGL σ) hθ δ hc)
      exact this
    exact Units.ext (UpperTheory.V.Z.Tf.Orb.centComm E n _ _ _ hδ (key a ha) (key b hb))
  have hmem : ∀ x, x ∈ twCent (sigmaGL σ) δ ↔ g⁻¹ * x * g ∈ twCent (sigmaGL σ) (twConj (sigmaGL σ) g δ) := by
    intro x
    rw [mem_twCent, mem_twCent, twConj, map_mul, map_mul, map_inv]
    have e : (g⁻¹ * x * g)⁻¹ * (g⁻¹ * δ * sigmaGL σ g) * ((sigmaGL σ g)⁻¹ * sigmaGL σ x * sigmaGL σ g) =
        g⁻¹ * (x⁻¹ * δ * sigmaGL σ x) * sigmaGL σ g := by group
    rw [e, mul_left_inj, mul_right_inj]
  have hφc : Continuous φ := IsLocallyConstant.continuous hφ.1
  have main := UpperTheory.V.Z.Tf.Orb.quotConj UpperTheory.V.Z.Tf.Orb.haarComm UpperTheory.V.Z.Tf.Orb.quotIndep (GL (Fin n) E) μE hμE
    _ _ g hclosed hcomm hmem μ μ' hμ hμ' hmap (fun x => φ (twConj (sigmaGL σ) x δ)) (hφc.comp htw).measurable
    (fun h hh x => by rw [twConj_mul_left _ _ hh])
  unfold twOrbIntegralC
  rw [← main]
  congr 1
  funext x
  congr 1
  simp only [twConj, map_mul]
  group
end

