import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0010
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0565
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0564
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0027
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0047
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0084
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0198
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SabMapOfIsoOfExtendGen
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RangeSubsetAbLocusOfIsProper
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SvalEqZeroOfExpandsAt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MovedFiniteDatumFourierExpansionChainless
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PureTensorOSmul
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0083
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneMapTypingsEquiv
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.GeneratorValues
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MulConjTransposeEq
section
noncomputable section

open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open scoped ComplexOrder ENNReal Topology

namespace GlobalTheory.BoundedFundDomain

theorem exists_section {G Y : Type} [Group G] [Countable G] [TopologicalSpace Y] [SecondCountableTopology Y]
    [T2Space Y] [MeasurableSpace Y] [BorelSpace Y] (a : G → Y → Y) (hc : ∀ g, Continuous (a g))
    (hmul : ∀ g h y, a (g * h) y = a g (a h y)) (hone : ∀ y, a 1 y = y)
    (hfin : ∀ y, ∃ W ∈ 𝓝 y, {g | a g y ∈ W}.Finite) :
    ∃ F : Set Y, MeasurableSet F ∧ (∀ y, ∃ g, a g y ∈ F) ∧ ∀ y ∈ F, ∀ g, a g y ∈ F → a g y = y := by
  classical
  obtain ⟨B, hB⟩ := ((TopologicalSpace.countable_countableBasis Y).insert ∅).exists_eq_range
    (Set.insert_nonempty _ _)
  have hBo : ∀ n, IsOpen (B n) := fun n => by
    have : B n ∈ insert ∅ (TopologicalSpace.countableBasis Y) := hB ▸ Set.mem_range_self n
    rcases this with h | h
    · rw [h]; exact isOpen_empty
    · exact TopologicalSpace.isOpen_of_mem_countableBasis h
  let P : ℕ → Y → Prop := fun n y => ∃ g, a g y ∈ B n ∧ ∀ g', a g' y ∈ B n → a g' y = a g y
  have hP : ∀ n g y, P n y → P n (a g y) := by
    rintro n g y ⟨k, hk, hk'⟩
    have e : a (k * g⁻¹) (a g y) = a k y := by rw [← hmul, inv_mul_cancel_right]
    refine ⟨k * g⁻¹, e ▸ hk, fun g' h => ?_⟩
    rw [e, ← hmul] at *
    exact hk' _ h
  have hP' : ∀ n g y, P n (a g y) → P n y := fun n g y h => by
    have := hP n g⁻¹ _ h
    rwa [← hmul, inv_mul_cancel, hone] at this
  have hm : ∀ n g, MeasurableSet {y | a g y ∈ B n} := fun n g => ((hBo n).preimage (hc g)).measurableSet
  have hPm : ∀ n, MeasurableSet {y | P n y} := fun n => by
    simp only [P, Set.ofPred_exists, Set.ofPred_and, Set.ofPred_forall]
    refine MeasurableSet.iUnion fun g => (hm n g).inter (MeasurableSet.iInter fun g' => ?_)
    have := (hm n g').compl.union (isClosed_eq (hc g') (hc g)).measurableSet
    convert this using 1
    ext y
    by_cases h : a g' y ∈ B n <;> simp [h]
  have hex : ∀ y, ∃ n, P n y := fun y => by
    obtain ⟨W, hW, hf⟩ := hfin y
    have hcl : IsClosed (((fun g => a g y) '' {g | a g y ∈ W}) \ {y}) := ((hf.image _).subset Set.sdiff_subset).isClosed
    have hn : W ∩ (((fun g => a g y) '' {g | a g y ∈ W}) \ {y})ᶜ ∈ 𝓝 y :=
      Filter.inter_mem hW (hcl.isOpen_compl.mem_nhds fun h => h.2 rfl)
    obtain ⟨U, hU, hyU, hUW⟩ := (TopologicalSpace.isBasis_countableBasis Y).mem_nhds_iff.1 hn
    obtain ⟨n, rfl⟩ : U ∈ Set.range B := hB ▸ Set.mem_insert_of_mem _ hU
    refine ⟨n, 1, by rwa [hone], fun g' h => ?_⟩
    rw [hone]
    by_contra hne
    exact (hUW h).2 ⟨⟨g', (hUW h).1, rfl⟩, hne⟩
  refine ⟨⋃ n, B n ∩ ({y | P n y} ∩ ⋂ m, ⋂ _ : m < n, {y | P m y}ᶜ), ?_, fun y => ?_, ?_⟩
  · exact MeasurableSet.iUnion fun n => (hBo n).measurableSet.inter ((hPm n).inter
      (MeasurableSet.iInter fun m => MeasurableSet.iInter fun _ => (hPm m).compl))
  · have h := Nat.find_spec (hex y)
    obtain ⟨g, hg, -⟩ := id h
    exact ⟨g, Set.mem_iUnion.2 ⟨_, hg, hP _ g y h,
      Set.mem_iInter₂.2 fun m hm h' => Nat.find_min (hex y) hm (hP' _ _ _ h')⟩⟩
  · intro y hy g hg
    obtain ⟨n, h1, h2, h3⟩ := Set.mem_iUnion.1 hy
    obtain ⟨n', h1', h2', h3'⟩ := Set.mem_iUnion.1 hg
    rcases lt_trichotomy n n' with h | rfl | h
    · exact (Set.mem_iInter₂.1 h3' n h (hP _ g _ h2)).elim
    · obtain ⟨k, -, hk⟩ := h2
      rw [hk g h1', ← hk 1 (by rwa [hone]), hone]
    · exact (Set.mem_iInter₂.1 h3 n' h (hP' _ g _ h2')).elim

variable {p q : ℕ}

def majMat (w : Matrix (Fin p) (Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ :=
  Jpq p q + (2 : ℂ) • (fromRows w (1 : Matrix (Fin q) (Fin q) ℂ) * (hQ w)⁻¹ *
    (fromRows w (1 : Matrix (Fin q) (Fin q) ℂ))ᴴ)

theorem mul_conjTranspose_eq {g : GL (Fin p ⊕ Fin q) ℂ} (hg : g ∈ Upq p q) :
    g.1 * g.1ᴴ = majMat (moeb g.1 0) := by
  have h0 := zero_mem_hcDom p q
  have hu := kapQ_isUnit hg h0
  have h1 := hQ_moeb hg h0
  have h2 := moeb_mul_kapQ hg h0
  have h3 := upq_right hg
  have hd : kapQ g 0 = g.1.toBlocks₂₂ := by simp [kapQ]
  rw [hd] at hu h1 h2
  rw [Matrix.mul_zero, zero_add] at h2
  set w := moeb g.1 0
  set G := g.1
  have h4 : (hQ w)⁻¹ = G.toBlocks₂₂ * G.toBlocks₂₂ᴴ := by
    apply inv_eq_left_inv
    have h5 : G.toBlocks₂₂ᴴ * hQ w * G.toBlocks₂₂ = 1 := by rw [h1]; simp [hQ]
    rw [Matrix.mul_assoc]
    exact mul_eq_one_comm.1 h5
  have h6 : fromRows w (1 : Matrix (Fin q) (Fin q) ℂ) * G.toBlocks₂₂ = fromRows G.toBlocks₁₂ G.toBlocks₂₂ := by
    rw [fromRows_mul, h2, Matrix.one_mul]
  rw [majMat, h4, ← h3, ← Matrix.mul_assoc, Matrix.mul_assoc _ G.toBlocks₂₂ᴴ, ← conjTranspose_mul, h6]
  ext a b
  have e : ∀ a c, fromRows G.toBlocks₁₂ G.toBlocks₂₂ a c = G a (Sum.inr c) := by
    rintro (a | a) c <;> rfl
  simp only [Jpq, Matrix.add_apply, Matrix.smul_apply, mul_apply, conjTranspose_apply, Fintype.sum_sum_type, e,
    fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, one_apply, Matrix.neg_apply,
    Matrix.zero_apply]
  simp
  ring

theorem continuousAt_majMat {w : Matrix (Fin p) (Fin q) ℂ} (hw : w ∈ hcDom p q) : ContinuousAt majMat w := by
  have h : (hQ w).PosDef := hw
  have hQc : Continuous (hQ (p := p) (q := q)) := by unfold hQ; fun_prop
  have h1 : ContinuousAt (fun w : Matrix (Fin p) (Fin q) ℂ => (hQ w)⁻¹) w := by
    refine ContinuousAt.comp (continuousAt_matrix_inv _ ?_) hQc.continuousAt
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ h.det_pos.ne'
  have h2 : Continuous fun w : Matrix (Fin p) (Fin q) ℂ => fromRows w (1 : Matrix (Fin q) (Fin q) ℂ) := by
    refine continuous_matrix ?_
    rintro (a | a) c
    · simp only [fromRows_apply_inl]; fun_prop
    · simp only [fromRows_apply_inr]; fun_prop
  have h3 : Continuous fun x : Matrix (Fin p) (Fin q) ℂ × Matrix (Fin q) (Fin q) ℂ =>
      Jpq p q + (2 : ℂ) • (fromRows x.1 (1 : Matrix (Fin q) (Fin q) ℂ) * x.2 *
        (fromRows x.1 (1 : Matrix (Fin q) (Fin q) ℂ))ᴴ) :=
    continuous_const.add ((((h2.comp continuous_fst).matrix_mul continuous_snd).matrix_mul
      (h2.comp continuous_fst).matrix_conjTranspose).const_smul (2 : ℂ))
  have h4 : ContinuousAt (fun w : Matrix (Fin p) (Fin q) ℂ => (w, (hQ w)⁻¹)) w := continuousAt_id.prodMk h1
  exact ContinuousAt.comp (f := fun w : Matrix (Fin p) (Fin q) ℂ => (w, (hQ w)⁻¹)) h3.continuousAt h4

theorem exists_bound {w : Matrix (Fin p) (Fin q) ℂ} (hw : w ∈ hcDom p q) :
    ∃ C : ℝ, ∀ᶠ w' in 𝓝 w, ∀ g ∈ Upq p q, moeb g.1 0 = w' → ∀ a b, ‖g.1 a b‖ ≤ C := by
  have h : ContinuousAt (fun w => ‖(majMat (p := p) (q := q) w).trace‖) w :=
    ((continuous_id.matrix_trace).continuousAt.comp (continuousAt_majMat hw)).norm
  refine ⟨√(‖(majMat w).trace‖ + 1), ?_⟩
  filter_upwards [h.eventually (gt_mem_nhds (lt_add_one _))] with w' hw' g hg e a b
  rw [← e, ← mul_conjTranspose_eq hg] at hw'
  refine Real.le_sqrt_of_sq_le (le_trans ?_ hw'.le)
  have e2 : (g.1 * g.1ᴴ).trace = ((∑ a, ∑ b, ‖g.1 a b‖ ^ 2 : ℝ) : ℂ) := by
    simp [trace, mul_apply, Complex.mul_conj']
  rw [e2, Complex.norm_real]
  refine le_trans ?_ (le_abs_self _)
  exact (Finset.single_le_sum (f := fun b => ‖g.1 a b‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ b)).trans
    (Finset.single_le_sum (f := fun a => ∑ b, ‖g.1 a b‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ a))

theorem norm_mul_mul_le {n : Type} [Fintype n] (A M B : Matrix n n ℂ) {C : ℝ} (h : ∀ a b, ‖M a b‖ ≤ C) (a b : n) :
    ‖(A * M * B) a b‖ ≤ ∑ d, (∑ c, ‖A a c‖ * C) * ‖B d b‖ := by
  simp only [mul_apply]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d _ => ?_)
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_right ((norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)) (norm_nonneg _)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (h c d) (norm_nonneg _)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r j : ℕ} (X : Data E r) (hj : j ≤ r) {Tau : Type}
  [Fintype Tau] (κ : Tau ≃ X.Ψ)

theorem eventually_finite (hp : X.p0 = r - j) {x : Frame X.Ψ r} (hx : IsOrth X x) {w : Pt Tau j (r - j)}
    (hw : w ∈ DomI Tau j (r - j)) :
    ∃ W ∈ 𝓝 w, {γ : GL (Fin r) E | γ ∈ X.Γ ∧ domPt X hj κ (lact γ x) ∈ W}.Finite := by
  choose C hC using fun t => exists_bound (hw t)
  obtain ⟨R, hR⟩ := (Set.finite_range fun s : Tau × Fin r × Fin r =>
    ∑ d, (∑ c, ‖mat (x0F X) (κ s.1) s.2.1 c‖ * C s.1) * ‖(mat x (κ s.1))⁻¹ d s.2.2‖).bddAbove
  refine ⟨_, Filter.eventually_all.2 fun t => (continuous_apply t).continuousAt.eventually (hC t),
    (GlobalTheory.LatFin.finite_automorphisms r X R).subset ?_⟩
  rintro γ ⟨hγ, h⟩
  refine ⟨X.Γ_stab γ hγ, fun τ a b => ?_⟩
  obtain ⟨t, rfl⟩ := κ.surjective τ
  obtain ⟨g, hg, e⟩ := exists_upq_of_orth X hj hp (KU.isOrth_lact X hγ hx) (κ t)
  have h1 := h t g hg (by rw [e]; rfl)
  have e2 : γ.1.map (κ t).1 = mat (x0F X) (κ t) * g.1.submatrix (idx hj) (idx hj) * (mat x (κ t))⁻¹ := by
    have hu : IsUnit (mat x (κ t)).det := (ExF.det_ne_of_orth X hx _).isUnit
    rw [e, frameCo, reindex_apply, submatrix_submatrix, Equiv.symm_comp_self, submatrix_id_id,
      mul_nonsing_inv_cancel_left _ _ (det_x0F X _).isUnit]
    exact (mul_nonsing_inv_cancel_right _ _ hu).symm
  have h2 := norm_mul_mul_le (mat (x0F X) (κ t)) (g.1.submatrix (idx hj) (idx hj)) (mat x (κ t))⁻¹
    (fun a b => h1 _ _) a b
  rw [← e2] at h2
  exact h2.trans (hR ⟨(t, a, b), rfl⟩)

theorem exists_isFD : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r j : ℕ) (X : Data E r) (hj : j ≤ r) (Tau : Type) [Fintype Tau] (κ : Tau ≃ X.Ψ), X.p0 = r - j → ∃ F, IsFD (gammaU X hj κ) F := by
  intro E _ _ _ r j X hj Tau _ κ hp
  have := KU.countable_Γ X
  obtain ⟨hO, hD⟩ := GlobalTheory.HodgeDomain.ActionDeriv.isOpen_and_fderiv_moebI Tau j (r - j)
  have hU : ∀ γ : X.Γ, toUpq X hj κ γ ∈ UpqI Tau j (r - j) := fun γ => gammaU_le X hj κ hp (Subgroup.mem_map_of_mem _ γ.2)
  have hmem : ∀ (γ : X.Γ), ∀ z ∈ DomI Tau j (r - j), moebI (toUpq X hj κ γ) z ∈ DomI Tau j (r - j) :=
    fun γ z hz t => moeb_mem (g := toUpq X hj κ γ t) (z := z t) (hU γ t trivial) (hz t)
  let a : X.Γ → DomFlat Tau j (r - j) → DomFlat Tau j (r - j) := fun γ v =>
    ⟨flat (moebI (toUpq X hj κ γ) (unflat v.1)), hmem γ _ v.2⟩
  have hx : ∀ v : DomFlat Tau j (r - j), ∃ x, IsOrth X x ∧ unflat v.1 = domPt X hj κ x := fun v => by
    obtain ⟨x, hx, e⟩ := GlobalTheory.TrueCx.FrameOnto.frame_onto E r j X hj Tau κ hp _ v.2
    obtain ⟨x1, h1, b, hb, rfl⟩ := ortho_holds r X x hx
    exact ⟨x1, h1, by rw [← e, domPt_rmul X hj κ hb]⟩
  have hdom : ∀ {x}, IsOrth X x → x ∈ X.dom := fun h => KU.orth_dom X h
  have ha : ∀ (γ : X.Γ) v x, IsOrth X x → unflat v.1 = domPt X hj κ x →
      unflat (a γ v).1 = domPt X hj κ (lact γ x) := fun γ v x h e => by
    rw [domPt_lact X hj κ hp _ (hdom h), ← e]; rfl
  have hinj : ∀ v w : DomFlat Tau j (r - j), unflat v.1 = unflat w.1 → v = w := fun v w h =>
    Subtype.ext (congrArg flat h)
  have hcont : ∀ γ, Continuous (a γ) := fun γ => by
    have h : Continuous fun v : DomFlat Tau j (r - j) => flat (moebI (toUpq X hj κ γ) (unflat v.1)) :=
      continuousOn_iff_continuous_restrict.1 (hD _ (hU γ)).1.continuousOn
    exact h.subtype_mk _
  obtain ⟨F, hF, h1, h2⟩ := exists_section a hcont
    (fun γ δ v => by
      obtain ⟨x, h, e⟩ := hx v
      refine hinj _ _ ?_
      rw [ha _ _ _ h e, ha _ _ _ (KU.isOrth_lact X δ.2 h) (ha _ _ _ h e), KU.lact_lact]; rfl)
    (fun v => by
      obtain ⟨x, h, e⟩ := hx v
      refine hinj _ _ ?_
      rw [ha _ _ _ h e, e, OneMemClass.coe_one, KU.lact_one])
    (fun v => by
      obtain ⟨x, h, e⟩ := hx v
      obtain ⟨W, hW, hf⟩ := eventually_finite X hj κ hp h v.2
      have hc : Continuous fun v : DomFlat Tau j (r - j) => unflat v.1 :=
        continuous_pi fun t => continuous_matrix fun a b => (continuous_apply (t, a, b)).comp continuous_subtype_val
      refine ⟨_, hc.continuousAt.preimage_mem_nhds hW, (hf.preimage Subtype.val_injective.injOn).subset ?_⟩
      intro γ hγ
      exact ⟨γ.2, by rw [← ha γ v x h e]; exact hγ⟩)
  refine ⟨Subtype.val '' F, (MeasurableEmbedding.subtype_coe hO.measurableSet).measurableSet_image.2 hF,
    Subtype.coe_image_subset _ _, fun z hz => ?_, ?_⟩
  · obtain ⟨γ, h⟩ := h1 ⟨flat z, hz⟩
    exact ⟨_, ⟨γ, γ.2, rfl⟩, _, h, rfl⟩
  · convert measure_empty (μ := muD Tau j (r - j))
    refine Set.eq_empty_of_forall_notMem ?_
    rintro _ ⟨⟨v, hv, rfl⟩, _, ⟨γ, hγ, rfl⟩, ⟨w, hw, e⟩, hne⟩
    have e' : w = a ⟨γ, hγ⟩ v := Subtype.ext e
    exact hne (congrArg (fun v => unflat v.1) (h2 v hv ⟨γ, hγ⟩ (e' ▸ hw)))

end GlobalTheory.BoundedFundDomain
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SabExtNormalStOfHomExtNormalSt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.TorRef

namespace GlobalTheory.TorRef

theorem sabExtNormalSt_of_homExtNormalSt : HomExtNormalSt → SabExtNormalSt := by
  intro hext E _ _ _ H X U _ j hX hoi hdom t₀ t t' a a' hp
  have hj₁ : IsPreimmersion j := inferInstance
  have hj₂ : Flat j := inferInstance
  have hj₄ : QuasiCompact j := inferInstance
  obtain ⟨hgen, -, hsd, -⟩ := densePart_basic X U j hj₁ hj₂ hdom hj₄
  have hred : IsReduced X := by
    have : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => by
      have := (hX x).1
      infer_instance
    exact isReduced_of_isReduced_stalk X
  have := hsd hred
  obtain ⟨_, _⟩ := ExtUnique.flat_and_isSeparated_of_isSemiAbelian t.G t.semi
  obtain ⟨_, _⟩ := ExtUnique.flat_and_isSeparated_of_isSemiAbelian t'.G t'.semi
  obtain ⟨F, hF, hφ⟩ := TripleExt.exists_hom a.cart a'.cart (hext X U j hX hoi hdom t.G t'.G t.semi t'.semi)
  obtain ⟨F', -, hφ'⟩ := TripleExt.exists_hom a'.cart a.cart (hext X U j hX hoi hdom t'.G t.G t'.semi t.semi)
  have hiso : IsIso F := ExtUnique.isIso_of_isPullback a.cart.1 a'.cart.1 (Iso.refl _) F F'
    ((Category.id_comp _).trans hφ.symm) ((Category.id_comp _).trans hφ'.symm)
  have gp : IsGrpPullback t.G t'.G (𝟙 X) F.left :=
    haveI : IsMonHom (asIso F).hom := hF
    isGrpPullback_of_iso (asIso F)
  have hact : ∀ x, (t.act.act x).left ≫ F.left = F.left ≫ (t'.act.act x).left := fun x => by
    have : t.act.act x ≫ F = F ≫ t'.act.act x := ExtUnique.over_hom_ext_of_isPullback a.cart.1 (by
      rw [Over.comp_left, Over.comp_left, ← Category.assoc, ← a.act, Category.assoc, hφ, ← Category.assoc, hφ,
        a'.act])
    exact congrArg (fun z => z.left) this
  have hlb : LBIso t.PP.L (t'.PP.L.pull F.left) := by
    obtain ⟨w, hw, -⟩ := (isPullCubical_iff _ _ _).1 a.lin
    obtain ⟨w', hw', -⟩ := (isPullCubical_iff _ _ _).1 a'.lin
    have hw'' : ∃ w'' : LB.Iso t₀.PP.L (t'.PP.L.pull (a.cm.F ≫ F.left)), PGen w'' := by
      rw [hφ]; exact ⟨w', hw'⟩
    obtain ⟨w'', hw''⟩ := hw''
    obtain ⟨r, hr, -⟩ := Exist.CubicalExtension.exists_quot_of_isos t'.PP.isLB t.PP.isLB t₀.PP.isLB w w'' hw hw''
      a.cart.1.isoPullback.inv (pullback.fst t.G.hom j) a.cart.1.isoPullback_inv_fst
    obtain ⟨ρ, hρ, -⟩ := Exist.CubicalExtension.exists_quot_of_gens (CubeMap.ofHom F).e_comm t'.PP.rig t.PP.rig
      t'.PP.rigGen t.PP.rigGen
    have sm := t.semi.smooth
    have gc := t.semi.geomConnected
    exact GlobalTheory.T.exists_lineBundleGenerator_extending_densePart X U j hX hj₁ hj₂ hdom hj₄ t.G (eSec t.G) (LB.div (t'.PP.L.pull F.left) t.PP.L) (Over.w η[t.G])
      sm (grpObj_geometricallyIntegral_of_smooth X t.G) (LB.isLB_div (pull_isLB t'.PP.isLB _) t.PP.isLB) ⟨ρ, hρ⟩ ⟨r, hr⟩
  obtain ⟨b, hb⟩ := exists_sabMap_of_lbIso E H X X t' t (𝟙 X) F.left
    ⟨hred, hgen.trans (range_subset_abLocus_of_isProper t.semi a.cart.1)⟩ gp hact hlb
  exact ⟨b, by rw [hb]; exact hφ⟩

end GlobalTheory.TorRef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SvalUpSec
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorRef

def upSec {S : Scheme.{0}} (G : Over S) {L : LB G.left} {k : ℕ} (σ : H0 L k) :
    LB.Sec (LPow G L (k : ℤ) (Over.mk (𝟙 S))) :=
  GlobalTheory.VVRank.pullTo σ (snd (Over.mk (𝟙 S)) G).left (fun _ => Category.comp_id _)

theorem sval_upSec {S : Scheme.{0}} (G : Over S) {L : LB G.left} {k : ℕ} (σ : H0 L k) {Z : Scheme.{0}}
    (r : Z ⟶ (Over.mk (𝟙 S) ⊗ G).left) (z : Z) {J : (Z ⟶ G.left) → L.ι} (hJ : Good L z J) :
    sval (upSec G σ) r z J = sval σ (r ≫ (snd (Over.mk (𝟙 S)) G).left) z J :=
  GlobalTheory.VVRank.sval_pullTo σ _ _ r z hJ

end GlobalTheory.TorRef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TieInOfFwTie
section
noncomputable section

open NumberField

namespace GlobalTheory.OneMapRefObj

open Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.IndefR.Links Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem tieIn_of_fwTie {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {κ : ∀ i : Fin D.R.m, Formalism.MainNotions.WeightFamilies.Wt D ((i : ℕ) + 1)}
    {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec} (t : FWTie T R κ v₀) : TieIn T R κ v₀ :=
  ⟨t.laws, t.alg_eq, t.kap, t.hv₀, t.chiR, t.x0⟩

end GlobalTheory.OneMapRefObj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorusCharacterRestrictionCommutesRingAction
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

set_option autoImplicit false

namespace GlobalTheory

theorem restrict_torus_smul_comm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (t' : SAB H (Sp W)) (P' : PELUnif (maximalIdeal W) t')
    (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ψ : R →+* V) [IsLocalHom ψ]
    (tV : SAB H (Sp V)) (mV : SABMap tV t (spMap ψ))
    (Ω : Type) [Field Ω] (α : V →+* Ω) (β : W →+* Ω) (hβ : ∀ x ∈ maximalIdeal W, β x = 0)
    (tΩ : SAB H (Sp Ω)) (n : SABMap tΩ tV (spMap α)) (n' : SABMap tΩ t' (spMap β))
    (j : splitTorus (Sp V) P'.D.toPre.X ⟶ tV.G) [IsMonHom j]
    (t₀ : SAB H (Sp (ResidueField V))) (m₀ : SABMap t₀ tV (spMap (residue V)))
    (h₀ : ∀ x ∈ maximalIdeal R, (residue V).comp ψ x = 0) (m₀' : SABMap t₀ t (spMap ((residue V).comp ψ)))
    (ρ : P.D.toPre.X →+ P'.D.toPre.X),
    Function.Injective α → GlobalTheory.TorusPart.pullTorus n.cart j = GlobalTheory.TorusPart.PELUnif.torus P' hβ n' →
    m₀'.φ = m₀.φ ≫ mV.φ →
    GlobalTheory.TorusPart.pullTorus m₀.cart j = GlobalTheory.SplitTorus.torusMap _ ρ ≫ GlobalTheory.TorusPart.PELUnif.torus P h₀ m₀' →
    ∀ (a : 𝓞 E) (x : P.D.toPre.X), ρ (a • x) = a • ρ x := by
  intro E _ _ _ H R _ _ _ t P W _ _ _ t' P' V _ _ _ ψ _ tV mV Ω _ α β hβ tΩ n n' j _ t₀ m₀ h₀ m₀' ρ
    hα hj _ h₀j
  letI := H.starRing
  have key : ∀ a : 𝓞 E, j ≫ tV.act.act a =
      SplitTorus.torusMap _ (DistribSMul.toAddMonoidHom P'.D.toPre.X (H.bar a)) ≫ j := by
    intro a
    have : IsSchemeTheoreticallyDominant (spMap α) :=
      ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective _ hα
    have : IsSeparated tV.G.hom := tV.semi.separated
    have : Flat (splitTorusAff ZU P'.D.toPre.X).hom :=
      (ExtUnique.splitTorusAff_flat_and_isSeparated _ _).1
    have : Flat (splitTorus (Sp V) P'.D.toPre.X).hom := inferInstanceAs (Flat (pullback.snd _ _))
    refine ExtUnique.over_hom_ext_of_isPullback (SplitTorus.isPullback_bcMap (spMap α) _) ?_
    have e1 := TorusPart.pullTorus_comp n.cart n.cart (tV.act.act a) (tΩ.act.act a) (n.act a) j
    have e2 := TorusPart.pullTorus_torusMap_comp n.cart j
      (DistribSMul.toAddMonoidHom P'.D.toPre.X (H.bar a))
    have e3 := TorusPart.PELUnif.torus_comp_act P' hβ n' a
    rw [hj, e3] at e1
    rw [hj] at e2
    rw [← TorusPart.pullTorus_left n.cart, ← TorusPart.pullTorus_left n.cart, e1, e2]
  have hmono := (GlobalTheory.T.uniformisationTorus_mono_and_factor E H R (maximalIdeal R) t P (ResidueField V) ((residue V).comp ψ) 0
    (TorusPart.map_pow_one_eq_zero h₀) t₀.G m₀'.φ m₀'.cart).1
  have key2 : ∀ a : 𝓞 E, ρ.comp (DistribSMul.toAddMonoidHom P.D.toPre.X (H.bar a)) =
      (DistribSMul.toAddMonoidHom P'.D.toPre.X (H.bar a)).comp ρ := by
    intro a
    have e := congrArg (TorusPart.pullTorus m₀.cart) (key a)
    rw [TorusPart.pullTorus_comp m₀.cart m₀.cart (tV.act.act a) (t₀.act.act a) (m₀.act a) j,
      TorusPart.pullTorus_torusMap_comp m₀.cart j, h₀j, Category.assoc,
      TorusPart.PELUnif.torus_comp_act P h₀ m₀' a, ← Category.assoc, ← Category.assoc,
      ← SplitTorus.torusMap_comp, ← SplitTorus.torusMap_comp] at e
    haveI : Mono (TorusPart.PELUnif.torus P h₀ m₀') := hmono
    have : Nonempty (Sp (ResidueField V)) := inferInstance
    exact SplitTorus.torusMap_injective ((cancel_mono _).1 e)
  intro a x
  have k := DFunLike.congr_fun (key2 (H.bar a)) x
  rw [show H.bar (H.bar a) = a from star_star a] at k
  exact k

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TriIff
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.FlagBundle

namespace GlobalTheory.ShFam

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

def EigFrame.Coord {R R' : Type} [CommRing R] [CommRing R'] {φ : c.F →+* R} {φ' : c.F →+* R'}
    {x : Sp R ⟶ Z.X} {x' : Sp R' ⟶ Z.X} (f : EigFrame Z φ x) (ψ : R →+* R') (g : EigFrame Z φ' x')
    (A : Mat Dw.mult R') : Prop :=
  x' = spMap ψ ≫ x ∧ φ' = ψ.comp φ ∧
    ∀ τ i, IsCombAtG Z.t x' (fun k => spMap (dualMap ψ) ≫ f.v τ k) (A τ i) (g.v τ i)

def EigFrame.Stable {R : Type} [CommRing R] {φ : c.F →+* R} {x : Sp R ⟶ Z.X} (f : EigFrame Z φ x) : Prop :=
  ∀ (R' : Type) [CommRing R'] [IsLocalRing R'] (ψ : R →+* R'),
    ∃ g : EigFrame Z (ψ.comp φ) (spMap ψ ≫ x), ∀ τ i, g.v τ i = spMap (dualMap ψ) ≫ f.v τ i

theorem EigFrame.tri_iff {R R' : Type} [CommRing R] [CommRing R'] {φ : c.F →+* R} {φ' : c.F →+* R'}
    {x : Sp R ⟶ Z.X} {x' : Sp R' ⟶ Z.X} (f : EigFrame Z φ x) (ψ : R →+* R') (g : EigFrame Z φ' x')
    (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → R'ˣ) :
    f.Tri ψ g t ↔ ∃ A : Mat Dw.mult R', f.Coord ψ g A ∧ (∀ τ i, A τ i i = t τ i) ∧ ∀ τ i k, i < k → A τ i k = 0 := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    choose A hA hA' hA'' using h3
    exact ⟨A, ⟨h1, h2, hA''⟩, hA, hA'⟩
  · rintro ⟨A, ⟨h1, h2, h3⟩, hA, hA'⟩
    exact ⟨h1, h2, fun τ i => ⟨A τ i, hA τ i, hA' τ i, h3 τ i⟩⟩

variable {F : Type} [Field F]

def Tied (e : F ≃+* c.F) (Y : GlobalTheory.ProjVar.Var F) (π : Y.X ⟶ gen Z)
    (f₀ : EigFrame Z (constF e Y) (genericPt Y ≫ π ≫ genι Z)) {k : (E →+* ℂ) → ℕ} (S : Fr (ratOf Y) Dw.mult k)
    (A₀ : Mat Dw.mult Y.Fn) : Prop :=
  A₀ ∈ S.S (genericPoint Y.X) ∧ ∀ y : Y.X, ∀ A ∈ S.S y, ∃ (φ : c.F →+* Y.X.presheaf.stalk y)
    (f : EigFrame Z φ (stalkPt Y y ≫ π ≫ genι Z)),
    f.Coord (algebraMap (Y.X.presheaf.stalk y) Y.X.functionField) f₀ (A₀ * A⁻¹)

end GlobalTheory.ShFam
end
end

