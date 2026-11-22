import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0170
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0053
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivDetCharacterOfIrreducibleRankLeOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParIndJacPlacing
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0194
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0197
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0036
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0149
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0142
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0132
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0156
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0170
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0157
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0191
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0195

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCentralScalarDistinctGeometricLemmaCells
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.CellCentral

open scoped TensorProduct

theorem twKer_piTensor_eq_top {α : Type} [DecidableEq α] {Γ X : α → Type} [∀ a, Group (Γ a)]
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (Γ a) (X a))
    (N : Subgroup (∀ a, Γ a)) (a : α) (Na : Subgroup (Γ a)) (hN : ∀ u ∈ Na, Pi.mulSingle a u ∈ N)
    (h : twKer (ρ a) Na 1 = ⊤) : twKer (piTensor ρ) N 1 = ⊤ := by
  refine eq_top_iff.2 fun y hy0 => ?_
  clear hy0
  induction y using PiTensorProduct.induction_on with
  | add x y hx hy => exact add_mem hx hy
  | smul_tprod r x =>
    refine Submodule.smul_mem _ r ?_
    let L := (PiTensorProduct.tprod ℂ : MultilinearMap ℂ X (⨂[ℂ] i, X i)).toLinearMap x a
    have hL : ∀ w, L w = PiTensorProduct.tprod ℂ (Function.update x a w) := fun w => rfl
    have hle : twKer (ρ a) Na 1 ≤ (twKer (piTensor ρ) N 1).comap L := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨u, v, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap]
      have hpi : piTensor ρ (Pi.mulSingle a (u : Γ a)) (PiTensorProduct.tprod ℂ (Function.update x a v)) =
          PiTensorProduct.tprod ℂ (Function.update x a (ρ a u v)) := by
        rw [piTensor_tprod]
        congr 1
        funext b
        by_cases hb : b = a
        · subst hb; simp
        · simp [Pi.mulSingle_eq_of_ne hb, Function.update_of_ne hb]
      refine Submodule.subset_span ⟨⟨_, hN u u.2⟩, PiTensorProduct.tprod ℂ (Function.update x a v), ?_⟩
      simp only [MonoidHom.one_apply, Units.val_one, one_smul]
      rw [map_sub, hL, hL, hpi]
    have hx : x a ∈ twKer (ρ a) Na 1 := h ▸ Submodule.mem_top
    have := hle hx
    simpa [hL] using this

theorem deltaHalf_eq_one {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {α : Type} [Fintype α] [LinearOrder α] (m : α → Type) [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
    (hm : ∀ a b, a ≠ b → IsEmpty (m a) ∨ IsEmpty (m b)) (g : Levi k m) : deltaHalf k m g = 1 := by
  rw [deltaHalf_apply]
  refine Finset.prod_eq_one fun a _ => ?_
  by_cases ha : IsEmpty (m a)
  · have : Matrix.GeneralLinearGroup.det (g a) = 1 := Units.ext (by simp [Matrix.det_isEmpty])
    rw [this, map_one]
  · have h0 : modExp m a = 0 := by
      unfold modExp
      rw [Finset.sum_eq_zero, Finset.sum_eq_zero, sub_zero]
      · intro b hb
        have hne : b ≠ a := by rintro rfl; simp at hb
        have : IsEmpty (m b) := (hm a b hne.symm).resolve_left ha
        simp
      · intro b hb
        have hne : b ≠ a := by rintro rfl; simp at hb
        have : IsEmpty (m b) := (hm a b hne.symm).resolve_left ha
        simp
    simp [h0]

theorem smInd_central {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W]
    [Module ℂ W] (H : Subgroup G) (σ : Representation ℂ H W) (z : G) (hz : z ∈ H)
    (hcen : ∀ x, x * z = z * x) (c : ℂ) (hc : ∀ w, σ ⟨z, hz⟩ w = c • w) (F : smoothPart (ind H σ)) :
    smInd H σ z F = c • F := by
  apply Subtype.ext
  apply Subtype.ext
  funext x
  show F.1.1 (x * z) = c • F.1.1 x
  rw [hcen x]
  exact (F.1.2 ⟨z, hz⟩ x).trans (hc _)

theorem one_case (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (σ : Fin 2 → Irr k 1) (hσ : ∀ i, 0 < 1 ∧ IsCuspidal (σ i).π)
    (hnt : ¬ Nonempty ((σ 0).π.Equiv (twist (σ 1).π (detChar (Fin 1) (unrChar k 1))))) :
    ∃ (z : Levi k fun _ : Fin 2 => Fin 1) (c c' : ℂ), (∀ g, g * z = z * g) ∧ c ≠ c' ∧
      (∀ x, (piTensor fun j => (σ (Equiv.swap 0 1 j)).π) z x = c • x) ∧
      ∀ (b : SizeMatrix (fun _ : Fin 2 => Fin 1) (fun _ : Fin 2 => Fin 1)),
        b.1 1 0 = 0 → ∀ (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Fin 1)
          (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Fin 1) y,
          cellFunctor f g (piTensor fun i => (σ i).π) z y = c' • y := by
  have hact : ∀ i (ψ : kˣ →* ℂˣ), (σ i).π.Equiv (detRep (Fin 1) ψ) → ∀ (g : GL (Fin 1) k) v,
      (σ i).π g v = (ψ (Matrix.GeneralLinearGroup.det g) : ℂ) • v := by
    intro i ψ e g v
    apply EquivLike.injective e
    have h1 : e ((σ i).π g v) = detRep (Fin 1) ψ g (e v) :=
      LinearMap.congr_fun (e.toIntertwiningMap.isIntertwining' g) v
    rw [h1, map_smul]
    simp [detRep, detChar_apply, smul_eq_mul]
  have h0 := RankLeOne.exists_equiv_detRep k (Fin 1) (σ 0).V (σ 0).π (σ 0).smooth (σ 0).irr
  have h1 := RankLeOne.exists_equiv_detRep k (Fin 1) (σ 1).V (σ 1).π (σ 1).smooth (σ 1).irr
  obtain ⟨ψ₀, -, ⟨e₀⟩⟩ := h0
  obtain ⟨ψ₁, -, ⟨e₁⟩⟩ := h1
  have hψ : ∃ t, ψ₀ t ≠ ψ₁ t := by
    by_contra hc
    push_neg at hc
    have hu : unrChar k 1 = 1 := MonoidHom.ext fun x => by simp [unrChar_apply]
    have hdet : detChar (Fin 1) (1 : kˣ →* ℂˣ) = (1 : GL (Fin 1) k →* ℂˣ) :=
      MonoidHom.ext fun x => by simp
    have hψe : ψ₀ = ψ₁ := MonoidHom.ext hc
    subst hψe
    rw [hu, hdet, twist_one] at hnt
    exact hnt ⟨e₀.trans e₁.symm⟩
  obtain ⟨t, ht⟩ := hψ
  let z : Levi k fun _ : Fin 2 => Fin 1 := Pi.mulSingle 0 (Matrix.GeneralLinearGroup.scalar (Fin 1) t)
  have hcomm : ∀ (g h : GL (Fin 1) k), g * h = h * g := by
    intro g h
    ext a b
    fin_cases a; fin_cases b
    simp [Matrix.mul_apply, mul_comm]
  have hcen : ∀ g, g * z = z * g := fun g => funext fun j => hcomm _ _
  refine ⟨z, ψ₁ t, ψ₀ t, hcen, fun h => ht (Units.ext h).symm, ?_, ?_⟩
  · intro x
    refine GlobalTheory.ProdSupport.piTensor_mulSingle _ 0 _ _ (fun v => ?_) x
    have hs : Equiv.swap (0 : Fin 2) 1 0 = 1 := by simp
    rw [hact _ ψ₁ (hs ▸ e₁), GlobalTheory.ProdSupport.det_scalar_one rfl]
  · intro b hb f g y
    have hr0 := b.2.1 0
    have hr1 := b.2.1 1
    have hc0 := b.2.2 0
    have hc1 := b.2.2 1
    simp only [Fin.sum_univ_two, Fintype.card_fin] at hr0 hr1 hc0 hc1
    have h01 : b.1 0 1 = 0 := by omega
    have hoff : ∀ i j : Fin 2, i ≠ j → b.1 i j = 0 := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    have hemp : ∀ i j : Fin 2, i ≠ j → IsEmpty (Fin (b.1 i j)) := fun i j hij => by
      rw [hoff i j hij]; infer_instance
    have hz : z ∈ relParab k g := by
      refine (Subgroup.mem_pi _).2 fun j _ => mem_parab.2 fun p q hpq => ?_
      rw [Subsingleton.elim p q] at hpq
      exact absurd hpq (lt_irrefl _)
    have hA : relDeltaHalf k (fun j i => Fin (b.1 i j)) (relProj k g ⟨z, hz⟩) = 1 := by
      rw [relDeltaHalf_apply]
      refine Finset.prod_eq_one fun j _ => deltaHalf_eq_one _ (fun a a' haa' => ?_) _
      by_cases h : a = j
      · subst h; exact Or.inr (hemp a' a (Ne.symm haa'))
      · exact Or.inl (hemp a j h)
    have hB : ∀ P, relDeltaHalf k (fun i j => Fin (b.1 i j)) P = 1 := by
      intro P
      rw [relDeltaHalf_apply]
      refine Finset.prod_eq_one fun i _ => deltaHalf_eq_one _ (fun a a' haa' => ?_) _
      by_cases h : a = i
      · subst h; exact Or.inr (hemp a a' haa')
      · exact Or.inl (hemp i a (Ne.symm h))
    have hC : relEmb k f (swapBlocks k (fun i j => Fin (b.1 i j)) (relProj k g ⟨z, hz⟩)) =
        (Pi.mulSingle (0 : Fin 2) (Matrix.GeneralLinearGroup.scalar (Fin 1) t) : Levi k fun _ : Fin 2 => Fin 1) := by
      funext i
      ext p q
      obtain rfl : p = q := Subsingleton.elim p q
      obtain ⟨⟨j, r⟩, hr⟩ := (f i).surjective p
      subst hr
      rw [relEmb_apply, leviEmb_apply_same]
      have hij : i = j := by
        by_contra hne
        have := r.2
        have h0 := hoff i j hne
        omega
      subst hij
      show ((z i : GL (Fin 1) k) : Matrix (Fin 1) (Fin 1) k) (g i ⟨i, r⟩) (g i ⟨i, r⟩) = _
      rw [Subsingleton.elim (g i ⟨i, r⟩) (f i ⟨i, r⟩)]
    refine smInd_central _ _ z hz hcen _ (fun w => ?_) y
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    simp only [MonoidHom.comp_apply, twist_apply, relJac_mk, hA, hB, hC, inv_one, Units.val_one, one_smul]
    rw [GlobalTheory.ProdSupport.piTensor_mulSingle _ 0 _ _ (hact 0 ψ₀ e₀ _), GlobalTheory.ProdSupport.det_scalar_one rfl,
      Submodule.Quotient.mk_smul]

theorem exists_central_scalar_ne_cell : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (d : Fin 2 → ℕ) (σ : ∀ i, Irr k (d i)), (∀ i, 0 < d i ∧ IsCuspidal (σ i).π) → d 1 = 1 →
    (∀ (h : d 0 = d 1) (α : ℂˣ), ¬ Nonempty ((h ▸ σ 0 : Irr k (d 1)).π.Equiv
      (twist (σ 1).π (detChar (Fin (d 1)) (unrChar k α))))) →
    ∃ (z : Levi k fun j : Fin 2 => Fin (d (Equiv.swap 0 1 j))) (c c' : ℂ), (∀ g, g * z = z * g) ∧ c ≠ c' ∧
      (∀ x, (piTensor fun j => (σ (Equiv.swap 0 1 j)).π) z x = c • x) ∧
      ∀ (b : SizeMatrix (fun i : Fin 2 => Fin (d i)) (fun j : Fin 2 => Fin (d (Equiv.swap 0 1 j)))),
        b.1 1 0 = 0 → ∀ (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Fin (d i))
          (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Fin (d (Equiv.swap 0 1 j))) y,
          cellFunctor f g (piTensor fun i => (σ i).π) z y = c' • y := by
  intro k _ _ _ _ d σ hσ hd1 hnt
  by_cases hd0 : d 0 = 1
  · have hd : d = fun _ => 1 := by
      funext i
      fin_cases i
      · exact hd0
      · exact hd1
    subst hd
    exact one_case k σ hσ (hnt rfl 1)
  · refine ⟨1, 1, 2, fun g => by simp, by norm_num, fun x => by simp, ?_⟩
    intro b hb f g y
    have hr0 := b.2.1 0
    have hr1 := b.2.1 1
    have hc0 := b.2.2 0
    have hc1 := b.2.2 1
    simp only [Fin.sum_univ_two, Fintype.card_fin, Equiv.swap_apply_left, Equiv.swap_apply_right] at hr0 hr1 hc0 hc1
    have hpos := (hσ 0).1
    have h00 : b.1 0 0 = 1 := by omega
    have h01 : 0 < b.1 0 1 := by omega
    have hne : unipRad k (f 0) ≠ ⊥ := by
      refine CuspMax.unipRad_ne_bot_iff.2 ⟨f 0 ⟨0, ⟨0, by omega⟩⟩, f 0 ⟨1, ⟨0, h01⟩⟩, ?_⟩
      simp
    have hJ : twKer (σ 0).π (unipRad k (f 0)) 1 = ⊤ :=
      Submodule.Quotient.subsingleton_iff.1 ((hσ 0).2.2 2 (b.1 0) (f 0) hne)
    have hT : twKer (piTensor fun i => (σ i).π) (relUnip k f) 1 = ⊤ := by
      refine twKer_piTensor_eq_top _ _ 0 _ (fun u hu => ?_) hJ
      refine (Subgroup.mem_pi _).2 fun i _ => ?_
      by_cases hi : i = 0
      · subst hi; simpa using hu
      · rw [Pi.mulSingle_eq_of_ne hi]; exact one_mem _
    haveI : Subsingleton (Jacquet (piTensor fun i => (σ i).π) (relUnip k f)) :=
      Submodule.Quotient.subsingleton_iff.2 hT
    apply Subtype.ext
    apply Subtype.ext
    funext x
    exact Subsingleton.elim (α := Jacquet (piTensor fun i => (σ i).π) (relUnip k f)) _ _

end GlobalTheory.CellCentral
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFinitePlaceOverLOfHostEmbeddingQbarStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
open Formalism.BasicNotions.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finitePlace_over_l_of_hostEmbedding_qbar : ∀ (D : D7) (l : ℕ) [Fact l.Prime] (τ : D.host.E →+* Qbar l), ∃ w : PlE D.host, w ∈ placesOver D.host.E l ∧ ∀ x : 𝓞 D.host.E, ‖τ (x : D.host.E)‖ < 1 ↔ x ∈ w.asIdeal := by
  first | exact @GlobalTheory.PlaceOfEmb.exists_place_of_emb | exact GlobalTheory.PlaceOfEmb.exists_place_of_emb | (intros; apply GlobalTheory.PlaceOfEmb.exists_place_of_emb <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntUnitaryOfGramClass
section
noncomputable section

open Matrix

namespace GlobalTheory.Hk3.HoweG

theorem exists_intUnitary_of_gramClass : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n n' : ℕ)
    (JS : GL (Fin n) L) (JT : GL (Fin n') L), Formalism.UG.IsUnramInv ϖ σ q → Odd q →
    JS ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) → JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JS : Matrix (Fin n) (Fin n) L) i j) = (JS : Matrix (Fin n) (Fin n) L) j i) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    ∀ x y : Matrix (Fin n') (Fin n) L,
    (∀ i j, (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose (x.map σ)) i j ∈ Formalism.UG.intL L) →
    GlobalTheory.Hk3.HoweG.HomA σ JS JT x y → GlobalTheory.Hk3.HoweG.GramEq σ JT x y → GlobalTheory.Hk3.HoweDuality.latIdx y = GlobalTheory.Hk3.HoweDuality.latIdx x →
    ∃ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) ∧
      ∀ i j, (y - ((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x) i j ∈ Formalism.UG.intL L := by
  intro L _ _ _ ϖ σ q n n' JS JT hU hq hJS hJT hS hT x y _hG hA hGr hidx
  classical
  have hvϖ := hU.2.2.2.1
  have hϖ0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hvϖ; exact WithZero.zero_ne_coe hvϖ
  have hϖint : ϖ ∈ Formalism.UG.intL L := by
    unfold Formalism.UG.intL
    rw [Valuation.mem_integer_iff, hvϖ]
    exact_mod_cast (show Multiplicative.ofAdd (-1 : ℤ) ≤ 1 by decide)
  have mulVec_int : ∀ {a b : ℕ} (M : Matrix (Fin a) (Fin b) L) (v : Fin b → L), (∀ i j, M i j ∈ Formalism.UG.intL L) →
      (∀ j, v j ∈ Formalism.UG.intL L) → ∀ i, (M *ᵥ v) i ∈ Formalism.UG.intL L := by
    intro a b M v hM hv i
    simp only [Matrix.mulVec, dotProduct]
    exact (Formalism.UG.intL L).sum_mem fun j _ => (Formalism.UG.intL L).mul_mem (hM i j) (hv j)
  obtain ⟨V, hV, a, hxV⟩ := GlobalTheory.T.exists_elementaryDivisors_integral_preimage_lattice L ϖ hvϖ n n' x
  obtain ⟨g0, hg0⟩ := hV
  have hVint : ∀ i j, (V : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L := by
    intro i j; rw [← hg0]; exact ((g0 : Matrix (Fin n) (Fin n) (Formalism.UG.intL L)) i j).2
  have hVinv : ∀ i j, ((V⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L := by
    intro i j; rw [← hg0, ← map_inv]
    exact (((g0⁻¹ : GL (Fin n) (Formalism.UG.intL L)) : Matrix (Fin n) (Fin n) (Formalism.UG.intL L)) i j).2
  set Vm : Matrix (Fin n) (Fin n) L := (V : Matrix (Fin n) (Fin n) L) with hVm
  have hyV : ∀ c : Fin n → L, (∀ j, c j ∈ Formalism.UG.intL L) →
      ((∀ i, (y *ᵥ (Vm *ᵥ c)) i ∈ Formalism.UG.intL L) ↔ ∀ j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (a j) (c j)) := by
    intro c hc
    have hu : ∀ i, (Vm *ᵥ c) i ∈ Formalism.UG.intL L := mulVec_int Vm c hVint hc
    rw [← hxV c hc]
    exact ⟨fun h => GlobalTheory.T.latticeKernel_le_of_matrixLatticeIndex_eq L ϖ σ q hU n n' x y hA.1 hidx _ hu h, fun h => hA.1 _ hu h⟩
  let ej : Fin n → Fin n → L := fun j => Pi.single j (ϖ ^ a j)
  have hej_int : ∀ j k, ej j k ∈ Formalism.UG.intL L := by
    intro j k
    by_cases h : k = j
    · subst h; simpa [ej] using (Formalism.UG.intL L).pow_mem hϖint (a k)
    · simp [ej, Pi.single_apply, h]
  have hej_dvd : ∀ j k, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (a k) (ej j k) := by
    intro j k
    by_cases h : k = j
    · subst h; exact ⟨1, (Formalism.UG.intL L).one_mem, by simp [ej]⟩
    · simpa [ej, Pi.single_apply, h] using GlobalTheory.Hk3.IntWitt.dvdPow_zero ϖ (a k)
  let zx : {j : Fin n // 0 < a j} → Fin n' → L := fun j => x *ᵥ (Vm *ᵥ ej j)
  let zy : {j : Fin n // 0 < a j} → Fin n' → L := fun j => y *ᵥ (Vm *ᵥ ej j)
  have hzx : ∀ j r, zx j r ∈ Formalism.UG.intL L := fun j => (hxV _ (hej_int j)).mpr (hej_dvd j)
  have hzy : ∀ j r, zy j r ∈ Formalism.UG.intL L := fun j => (hyV _ (hej_int j)).mpr (hej_dvd j)
  have hix : GlobalTheory.Hk3.IntWitt.IndepMod ϖ zx := GlobalTheory.T.elementaryDivisor_columns_independentModUniformizer L ϖ hvϖ n n' x Vm a hxV
  have hiy : GlobalTheory.Hk3.IntWitt.IndepMod ϖ zy := GlobalTheory.T.elementaryDivisor_columns_independentModUniformizer L ϖ hvϖ n n' y Vm a hyV
  have hgr := GlobalTheory.T.gramClass_elementaryDivisor_columns_congr L ϖ σ q hU n n' JT x y Vm a hVint hxV hGr
  obtain ⟨h, hh, hcong⟩ := GlobalTheory.T.integralWittTheorem_mod_uniformizerPow L ϖ σ q hU hq n' JT hJT hT {j : Fin n // 0 < a j} (fun j => a j) zx zy
    (fun j => j.2) hzx hzy hix hiy (fun i j => hgr i j)
  refine ⟨h, hh, ?_⟩
  set H : Matrix (Fin n') (Fin n') L := ((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) with hH
  have hHint : ∀ i j, H i j ∈ Formalism.UG.intL L := by
    obtain ⟨h0, hh0⟩ := hh
    intro i j; rw [hH, ← hh0]; exact ((h0 : Matrix (Fin n') (Fin n') (Formalism.UG.intL L)) i j).2
  set M := y - H * x with hM
  have hMv : ∀ w : Fin n → L, M *ᵥ w = y *ᵥ w - H *ᵥ (x *ᵥ w) := by
    intro w; rw [hM, Matrix.sub_mulVec, Matrix.mulVec_mulVec]
  have hcol : ∀ j i, (M *ᵥ (Vm *ᵥ Pi.single j 1)) i ∈ Formalism.UG.intL L := by
    intro j i
    by_cases ha : a j = 0
    · have he : Pi.single j (1 : L) = ej j := by simp [ej, ha]
      rw [he, hMv]
      exact (Formalism.UG.intL L).sub_mem ((hyV _ (hej_int j)).mpr (hej_dvd j) i)
        (mulVec_int H _ hHint ((hxV _ (hej_int j)).mpr (hej_dvd j)) i)
    · have hpos : 0 < a j := Nat.pos_of_ne_zero ha
      obtain ⟨b, hb, hbe⟩ := hcong ⟨j, hpos⟩ i
      have he : ej j = ϖ ^ a j • Pi.single j (1 : L) := by
        funext k; simp [ej, Pi.single_apply]
      have key : ϖ ^ a j * (M *ᵥ (Vm *ᵥ Pi.single j 1)) i = ϖ ^ a j * (-b) := by
        have : (M *ᵥ (Vm *ᵥ ej j)) i = -((H *ᵥ zx ⟨j, hpos⟩) i - zy ⟨j, hpos⟩ i) := by
          rw [hMv]; simp only [zx, zy, Pi.sub_apply]; ring
        rw [he, Matrix.mulVec_smul, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul] at this
        rw [this, hbe]; ring
      have := mul_left_cancel₀ (pow_ne_zero _ hϖ0) key
      rw [this]; exact (Formalism.UG.intL L).neg_mem hb
  intro i r
  have hMe : M = (M * Vm) * ((V⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
    rw [Matrix.mul_assoc, hVm, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  rw [hMe, Matrix.mul_apply]
  refine (Formalism.UG.intL L).sum_mem fun k _ => (Formalism.UG.intL L).mul_mem ?_ (hVinv k r)
  have hc := hcol k i
  rwa [Matrix.mulVec_mulVec, Matrix.mulVec_single_one, Matrix.col_apply] at hc

end GlobalTheory.Hk3.HoweG

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleSubquotientCommonEigenvectorStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_irreducible_subquotient_common_eigenvector : ∀ (G : Type) [Group G] (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (S : Set G) (θ : G → ℂ) (x : V), x ≠ 0 → (∀ g ∈ S, ρ g x = θ g • x) → ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y) (τ : Representation ℂ G Y), τ.IsIrreducible ∧ IsSubquotient τ ρ ∧ ∃ y : Y, y ≠ 0 ∧ ∀ g ∈ S, τ g y = θ g • y := by
  first | exact @GlobalTheory.EigenSubquot.exists_irreducible_subquotient_eigen | exact GlobalTheory.EigenSubquot.exists_irreducible_subquotient_eigen | (intros; apply GlobalTheory.EigenSubquot.exists_irreducible_subquotient_eigen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleTensorOfJacquetSubquotientStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_irreducible_tensor_of_jacquet_subquotient : GlobalTheory.Published.GeometricLemma → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (π : Irr k n) (s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n) (Y : Type) [AddCommGroup Y] [Module ℂ Y] (τ : Representation ℂ (Levi k fun a => Fin (d a)) Y), τ.IsIrreducible → IsSubquotient τ (jac e π.π) → ∃ σ : ∀ a, Irr k (d a), IsSubquotient τ (piTensor fun a => (σ a).π) := by
  first | exact @GlobalTheory.JacTensor.exists_irr_tensor_of_isSubquotient_jac | exact GlobalTheory.JacTensor.exists_irr_tensor_of_isSubquotient_jac | (intros; apply GlobalTheory.JacTensor.exists_irr_tensor_of_isSubquotient_jac <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLevelCharacterAtConjugateSplitPlace
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TypeTame

def invTranspose {R : Type} [CommRing R] (n : ℕ) : GL (Fin n) R →* GL (Fin n) R where
  toFun g := ⟨(g⁻¹).val.transpose, g.val.transpose,
    by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]⟩
  map_one' := by
    apply Units.ext
    simp
  map_mul' a b := by
    apply Units.ext
    simp only [Units.val_mul, mul_inv_rev, Matrix.transpose_mul]

theorem invTranspose_val {R : Type} [CommRing R] (n : ℕ) (g : GL (Fin n) R) :
    (invTranspose n g).val = (g⁻¹).val.transpose := rfl

theorem invTranspose_inv_val {R : Type} [CommRing R] (n : ℕ) (g : GL (Fin n) R) :
    ((invTranspose n g)⁻¹).val = g.val.transpose := rfl

theorem invTranspose_invTranspose {R : Type} [CommRing R] (n : ℕ) (g : GL (Fin n) R) :
    invTranspose n (invTranspose n g) = g := by
  apply Units.ext
  rw [invTranspose_val, invTranspose_inv_val, Matrix.transpose_transpose]

theorem continuous_invTranspose {R : Type} [CommRing R] [TopologicalSpace R] (n : ℕ) :
    Continuous (invTranspose (R := R) n) := by
  rw [Units.continuous_iff]
  exact ⟨Units.continuous_coe_inv.matrix_transpose, Units.continuous_val.matrix_transpose⟩

theorem invTranspose_mem_GLint {F : Type} [Field F] (n : ℕ) (O : Subring F) {g : GL (Fin n) F}
    (hg : g ∈ Formalism.UG.GLint (Fin n) O) : invTranspose n g ∈ Formalism.UG.GLint (Fin n) O := by
  obtain ⟨h, rfl⟩ := hg
  exact ⟨invTranspose n h, Units.ext rfl⟩

theorem conjSP_proj {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (x : AL L) :
    (conjSP s).proj x = s.proj (conjAL L x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b => simp [SplitPlace.proj, conjAL, Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.map_tmul]
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]

theorem conjSP_loc {L : Type} [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L) (κ : GA L n) :
    (conjSP s).loc n κ = invTranspose n (s.loc n κ) := by
  have hm : κ.1.val * conjT (conjAL L) κ.1.val = 1 := κ.2
  have h1 : (κ.1⁻¹).val = conjT (conjAL L) κ.1.val := Units.inv_eq_of_mul_eq_one_right hm
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  change (conjSP s).proj (κ.1.val i j) = s.proj ((κ.1⁻¹).val j i)
  rw [h1, conjSP_proj]
  rfl

theorem exists_conj_level : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L) (K : Subgroup (GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)))) (θ : K →* ℂˣ), (∀ g ∈ K, g ∈ Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring) → IsOpen (θ.ker : Set K) → ∃ (K' : Subgroup (GL (Fin n) ((GlobalTheory.TypeTame.conjSP s).v.adicCompletion (maximalRealSubfield L)))) (θ' : K' →* ℂˣ), (∀ g ∈ K', g ∈ Formalism.UG.GLint (Fin n) ((GlobalTheory.TypeTame.conjSP s).v.adicCompletionIntegers (maximalRealSubfield L)).toSubring) ∧ IsOpen (θ'.ker : Set K') ∧ (∀ κ : GAf L n, (GlobalTheory.TypeTame.conjSP s).loc n κ ∈ K' ↔ s.loc n κ ∈ K) ∧ (∀ (κ : GAf L n) (h : s.loc n κ ∈ K) (h' : (GlobalTheory.TypeTame.conjSP s).loc n κ ∈ K'), θ' ⟨(GlobalTheory.TypeTame.conjSP s).loc n κ, h'⟩ = θ ⟨s.loc n κ, h⟩) ∧ ∀ g (hg : g ∈ K) (g' : GL (Fin n) ((GlobalTheory.TypeTame.conjSP s).v.adicCompletion (maximalRealSubfield L))), g'.val = (g⁻¹).val.transpose → ∃ h' : g' ∈ K', θ' ⟨g', h'⟩ = θ ⟨g, hg⟩ := by
  intro L _ _ _ n s K θ hK hθ
  have key : ∀ (g' : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) (g) (hg : g ∈ K),
      g' = invTranspose n g → ∃ h' : g' ∈ K.comap (invTranspose n),
        θ.comp ((invTranspose n).subgroupComap K) ⟨g', h'⟩ = θ ⟨g, hg⟩ := by
    rintro g' g hg rfl
    refine ⟨by rw [Subgroup.mem_comap, invTranspose_invTranspose]; exact hg, ?_⟩
    rw [MonoidHom.comp_apply]
    exact congrArg θ (Subtype.ext (invTranspose_invTranspose n g))
  refine ⟨K.comap (invTranspose n), θ.comp ((invTranspose n).subgroupComap K), ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    have := invTranspose_mem_GLint n _ (hK _ hg)
    rwa [invTranspose_invTranspose] at this
  · have hc : Continuous ((invTranspose n).subgroupComap K) :=
      Continuous.subtype_mk ((continuous_invTranspose n).comp continuous_subtype_val) _
    exact hθ.preimage hc
  · intro κ
    rw [conjSP_loc]
    change invTranspose n (invTranspose n (s.loc n κ)) ∈ K ↔ _
    rw [invTranspose_invTranspose]
  · intro κ h h'
    exact (key _ _ h (conjSP_loc n s κ)).2
  · intro g hg g' hg'
    exact key g' g hg (Units.ext hg')

end GlobalTheory.TypeTame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLeviBlockEigenvectorAtIdentityStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_levi_block_eigenvector_at_identity : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (α : Type) [Fintype α] [LinearOrder α] (m : α → Type) [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] (n : Type) [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) (X : α → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (σ : ∀ a, Representation ℂ (GL (m a) k) (X a)) (χ : kˣ →* ℂˣ) (x : IndSp e (piTensor σ)), x ≠ 0 → (∀ g ∈ KO k n, multiProd e σ g x = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • x) → ∃ w : PiTensorProduct ℂ X, w ≠ 0 ∧ ∀ a, ∀ h ∈ KO k (m a), piTensor σ (Pi.mulSingle a h) w = (χ (Matrix.GeneralLinearGroup.det h) : ℂ) • w := by
  first | exact @GlobalTheory.SphBlock.exists_eigen_at_one | exact GlobalTheory.SphBlock.exists_eigen_at_one | (intros; apply GlobalTheory.SphBlock.exists_eigen_at_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharLocalComponentExistsUniqueUnitaryStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeChar_localComponent_exists_unique_unitary : ∀ (E : Type) [Field E] [NumberField E] (χ : HChar E) (w : HeightOneSpectrum (𝓞 E)), ∃ ξ, IsComp χ w ξ ∧ (∀ ξ', IsComp χ w ξ' → ξ' = ξ) ∧ (χ.IsUnitary → ∀ x, ‖((ξ x : ℂˣ) : ℂ)‖ = 1) := by
  first | exact @GlobalTheory.HeckeComp.main | exact GlobalTheory.HeckeComp.main | (intros; apply GlobalTheory.HeckeComp.main <;> assumption)
end

