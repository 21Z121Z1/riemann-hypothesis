import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0149
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0142
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0139
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0173
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0086
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1061
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0133
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.AntisymmetrizedProductEqFactorialSmulQdet
import Formalism.LocalToGlobal.KernelLattices.KerStd
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0011
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FourthPowerTheta
import Formalism.LocalToGlobal.InertKernelTheory.Bundle0001
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0174
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0118
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0175
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0132
import Formalism.LocalToGlobal.InertKernelTheory.Bundle0004
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0176
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0156
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0177

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HermitianDualSubsetOfIntegralGram
section
open Matrix

namespace GlobalTheory.Hk3.HoweG

theorem dualA_hform_eq {L : Type} [Field L] (σ : L →+* L) {n : ℕ} (J : Matrix (Fin n) (Fin n) L) (u v : Fin n → L) :
    Formalism.UG.hform σ J u v = (fun i => σ (u i)) ⬝ᵥ (J *ᵥ v) := by
  simp [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem dualA_conj_mulVec {L : Type} [Field L] (σ : L →+* L) {a b : ℕ} (y : Matrix (Fin a) (Fin b) L) (w : Fin b → L) :
    (fun i => σ ((y *ᵥ w) i)) = (y.map σ) *ᵥ (fun i => σ (w i)) := by
  funext i
  simp [dotProduct, Matrix.mulVec, map_sum]

theorem dualA_mulVec_int {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {a b : ℕ}
    {A : Matrix (Fin a) (Fin b) L} (hA : ∀ i j, A i j ∈ Formalism.UG.intL L) {w : Fin b → L}
    (hw : ∀ i, w i ∈ Formalism.UG.intL L) (i : Fin a) : (A *ᵥ w) i ∈ Formalism.UG.intL L := by
  simp only [Matrix.mulVec, dotProduct]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hA i k) (hw k)

theorem hermDual_subset_of_gram_int : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L),
    (∀ z, σ (σ z) = z) → (∀ z, Valued.v (σ z) = Valued.v z) →
    JS ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) → JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JS : Matrix (Fin n) (Fin n) L) i j) = (JS : Matrix (Fin n) (Fin n) L) j i) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    ∀ x : Matrix (Fin n') (Fin n) L, (∀ i j, (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose (x.map σ)) i j ∈ Formalism.UG.intL L) →
    ∀ v : Fin n → L,
      (∀ u : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) → (∀ i, (x *ᵥ u) i ∈ Formalism.UG.intL L) →
        Formalism.UG.hform σ (JS : Matrix (Fin n) (Fin n) L) u v ∈ Formalism.UG.intL L) →
      (∀ w : Fin n' → L, (∀ i, w i ∈ Formalism.UG.intL L) →
        Formalism.UG.hform σ (JS : Matrix (Fin n) (Fin n) L) (GlobalTheory.Hk3.HoweG.adj σ JS JT x *ᵥ w) v ∈ Formalism.UG.intL L) →
      ∃ u : Fin n → L, ∃ w : Fin n' → L, (∀ i, u i ∈ Formalism.UG.intL L) ∧ (∀ i, (x *ᵥ u) i ∈ Formalism.UG.intL L) ∧
        (∀ i, w i ∈ Formalism.UG.intL L) ∧ v = u + GlobalTheory.Hk3.HoweG.adj σ JS JT x *ᵥ w := by
  intro L _ _ σ n n' JS JT hσ hv hJS hJT hS0 hT0 x hx v h1 h2
  have hS : Formalism.UG.cT σ (JS : Matrix (Fin n) (Fin n) L) = JS := HoweSwap.cT_herm hS0
  have hT : Formalism.UG.cT σ (JT : Matrix (Fin n') (Fin n') L) = JT := HoweSwap.cT_herm hT0
  have hSi := HoweSwap.cT_inv_herm JS hS
  obtain ⟨hS1, hS2⟩ := HoweSwap.glint_int hJS
  obtain ⟨hT1, hT2⟩ := HoweSwap.glint_int hJT
  have hint : ∀ z, z ∈ Formalism.UG.intL L → σ z ∈ Formalism.UG.intL L := by
    intro z hz
    simp only [Formalism.UG.intL, Valuation.mem_integer_iff] at hz ⊢
    rwa [hv]
  obtain ⟨l, w, hl, hw, hz⟩ := GlobalTheory.T.dual_integral_preimage_le_sum_transpose_image L n' n (x.map σ) ((JS : Matrix (Fin n) (Fin n) L) *ᵥ v) (by
    intro u hu hxu
    have e : x *ᵥ (fun i => σ (u i)) = fun i => σ ((x.map σ *ᵥ u) i) := by
      rw [dualA_conj_mulVec]
      congr 1
      ext i j; simp [hσ]
    have := h1 (fun i => σ (u i)) (fun i => hint _ (hu i)) (fun i => by rw [e]; exact hint _ (hxu i))
    rw [dualA_hform_eq] at this
    simpa [dotProduct, hσ] using this)
  have hc : ∀ {a b : Type} (Z : Matrix a b L), (Z.map σ)ᵀ = Formalism.UG.cT σ Z := fun _ => rfl
  have hy : Formalism.UG.cT σ (adj σ JS JT x) * (JS : Matrix (Fin n) (Fin n) L) = (JT : Matrix (Fin n') (Fin n') L) * x := by
    simp only [adj, Formalism.UG.cT_mul, HoweSwap.cT_cT hσ, hT, hSi, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  have hTxv : ∀ k, (((JT : Matrix (Fin n') (Fin n') L) * x) *ᵥ v) k ∈ Formalism.UG.intL L := by
    intro k
    have := h2 (Pi.single k 1) (fun i => by
      by_cases h : i = k
      · subst h; simp
      · simp [h])
    rw [dualA_hform_eq, dualA_conj_mulVec, dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hc,
      Matrix.mulVec_mulVec, hy] at this
    have e : (fun i => σ ((Pi.single k 1 : Fin n' → L) i)) = Pi.single k 1 := by
      funext i
      by_cases h : i = k
      · subst h; simp
      · simp [h]
    rw [e] at this
    simpa using this
  have hxv : ∀ k, (x *ᵥ v) k ∈ Formalism.UG.intL L := by
    intro k
    have := dualA_mulVec_int hT2 hTxv k
    rwa [Matrix.mulVec_mulVec, HoweSwap.inv_mul_cl] at this
  have hyw : adj σ JS JT x *ᵥ (((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ w) =
      (((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (x.map σ)ᵀ) *ᵥ w := by
    rw [Matrix.mulVec_mulVec, adj, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, hc]
  have hv2 : v = ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ l +
      (((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (x.map σ)ᵀ) *ᵥ w := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_add, ← hz, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  refine ⟨((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ l,
    ((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ w, dualA_mulVec_int hS2 hl, fun i => ?_,
    dualA_mulVec_int hT2 hw, by rw [hyw]; exact hv2⟩
  have e : x *ᵥ (((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ l) = x *ᵥ v -
      (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (x.map σ)ᵀ) *ᵥ w := by
    conv_rhs => rw [hv2]
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec w, ← Matrix.mul_assoc, add_sub_cancel_right]
  rw [e, Pi.sub_apply]
  exact Subring.sub_mem _ (hxv i) (dualA_mulVec_int hx hw i)

end GlobalTheory.Hk3.HoweG
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdeleMapInfDiagMaxRealSubfieldCm
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Published GlobalTheory.TheRec GlobalTheory.ContraPair
open GlobalTheory.CuspRep.InfType GlobalTheory.CuspRep.AlgExpo

noncomputable section

namespace GlobalTheory.InfDiagExt

theorem val_infDiag (L : Type) [Field L] [NumberField L] (k : Lˣ) :
    ((infDiag k : Ideles L) : AdeleRing (𝓞 L) L) = (algebraMap L (InfiniteAdeleRing L) k, 1) := by
  classical
  unfold infDiag
  rw [MonoidHom.finsetProd_apply, Units.coe_prod]
  let ι : (∀ w : InfinitePlace L, w.Completion) →* AdeleRing (𝓞 L) L :=
    MonoidHom.inl (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)
  change ∏ w : InfinitePlace L, ι (Pi.mulSingle w (algebraMap L w.Completion k)) =
    ι (fun w => algebraMap L w.Completion k)
  rw [← map_prod, Finset.univ_prod_mulSingle]

theorem ideleMap_infDiag_gen (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (x : Kˣ) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap K L (infDiag x) = infDiag (Units.map (algebraMap K L).toMonoidHom x) := by
  apply Units.ext
  change GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap K L ((infDiag x : Ideles K) : AdeleRing (𝓞 K) K) = _
  rw [val_infDiag, val_infDiag]
  refine Prod.ext ?_ ?_
  · have h := congrArg Prod.fst (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap_algebraMap K L (x : K))
    exact h
  · exact map_one (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteAdeleMap K L)

theorem ideleMap_infDiag : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (x : (maximalRealSubfield E)ˣ), GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E (infDiag x) = infDiag (Units.map (algebraMap (maximalRealSubfield E) E).toMonoidHom x) :=
  fun E _ _ _ x => ideleMap_infDiag_gen (maximalRealSubfield E) E x

end GlobalTheory.InfDiagExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdeleMapOfAlgebraMaximalRealSubfieldInjectiveStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Published GlobalTheory.TheRec GlobalTheory.ContraPair
open GlobalTheory.CuspRep.InfType GlobalTheory.CuspRep.AlgExpo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideleMapOfAlgebra_maximalRealSubfield_injective : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Function.Injective (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E) := by
  first | exact @GlobalTheory.IdeleMapInjective.ideleMap_injective | exact GlobalTheory.IdeleMapInjective.ideleMap_injective | (intros; apply GlobalTheory.IdeleMapInjective.ideleMap_injective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InfCharConjEmbeddingNegOfInvariantPairing
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Published GlobalTheory.TheRec GlobalTheory.ContraPair

noncomputable section

namespace GlobalTheory.CapPair

open Formalism.REAL Formalism.HermitianLatticeCounting.P MulOpposite

section Algebra

variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ}

omit [Algebra ℂ A] in

theorem glRel_op {X : Fin n → Fin n → A} (h : Formalism.REAL.GlRel X) : Formalism.REAL.GlRel fun i j => op (X j i) := by
  intro a b c d
  have h1 := congrArg op (h d c b a)
  simp only [op_sub, op_mul, apply_ite op, op_zero] at h1
  rw [h1]
  simp only [eq_comm (a := c) (b := b), eq_comm (a := a) (b := d)]

theorem qdet_op {X : Fin n → Fin n → A} (h : Formalism.REAL.GlRel X) (y : ℂ) :
    qdet (fun i j => op (X j i)) y = op (qdet X y) := by
  have hP : ∀ (arg : Fin n → ℂ) (σ τ : Equiv.Perm (Fin n)), orderedTermProduct (fun i j => op (X j i)) arg σ τ =
      op (orderedTermProduct X (arg ∘ Fin.revPerm) (τ * Fin.revPerm) (σ * Fin.revPerm)) := fun arg σ τ => by
    unfold orderedTermProduct
    rw [op_list_prod, List.map_ofFn]
    congr 1
    refine List.ext_getElem (by simp) fun k h1 h2 => ?_
    have hk : k < n := by simpa using h1
    have e : (⟨n - 1 - k, by omega⟩ : Fin n).rev = ⟨k, hk⟩ := Fin.ext (by rw [Fin.val_rev]; simp only; omega)
    simp only [List.getElem_reverse, List.getElem_ofFn, List.length_ofFn, Function.comp_apply, Equiv.Perm.mul_apply,
      Fin.revPerm_apply, e, Tm, op_add, apply_ite op, op_zero, eq_comm (a := τ _)]
    rfl
  have hS : ∀ arg : Fin n → ℂ, doublyAntisymmetrizedProduct (fun i j => op (X j i)) arg = op (doublyAntisymmetrizedProduct X (arg ∘ Fin.revPerm)) := fun arg => by
    unfold doublyAntisymmetrizedProduct
    rw [Finset.sum_comm, Finset.op_sum]
    refine Fintype.sum_equiv (Equiv.mulRight Fin.revPerm) _ _ fun σ => ?_
    rw [Finset.op_sum]
    refine Fintype.sum_equiv (Equiv.mulRight Fin.revPerm) _ _ fun τ => ?_
    simp only [hP, ← zsmul_eq_mul, op_smul, smul_smul, Equiv.coe_mulRight, Equiv.Perm.sign_mul, Units.val_mul]
    congr 1
    linear_combination (-((Equiv.Perm.sign σ : ℤ) * (Equiv.Perm.sign τ : ℤ))) *
      Int.units_coe_mul_self (Equiv.Perm.sign (Fin.revPerm (n := n)))
  have e := hS fun k => y - (k : ℂ)
  rw [antisymmetrizedProduct_perm_invariant, antisymmetrizedProduct_eq_factorial_smul_qdet _ h, antisymmetrizedProduct_eq_factorial_smul_qdet _ (glRel_op h), op_smul] at e
  exact (IsUnit.mk0 _ (by exact_mod_cast n.factorial_ne_zero)).smul_left_cancel.mp e

theorem qdet_antipode {X : Fin n → Fin n → A} (h : Formalism.REAL.GlRel X) (x : ℂ) :
    qdet (fun i j => -op (X i j)) x = op ((-1 : ℂ) ^ n • qdet X ((n : ℂ) - 1 - x)) := by
  rw [quantumDet_neg_transpose _ (glRel_op h), qdet_op h, op_smul]

theorem qdet_prod {A' : Type} [Ring A'] [Algebra ℂ A'] (X : Fin n → Fin n → A) (Y : Fin n → Fin n → A') (x : ℂ) :
    qdet (fun i j => (X i j, Y i j)) x = (qdet X x, qdet Y x) :=
  Prod.ext (map_qdet (AlgHom.fst ℂ A A') _ _) (map_qdet (AlgHom.snd ℂ A A') _ _)

end Algebra

def adjPairs {M : Type} [AddCommGroup M] [Module ℂ M] (V W : Submodule ℂ M) (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) :
    Subalgebra ℂ (Module.End ℂ M × (Module.End ℂ M)ᵐᵒᵖ) where
  carrier := {z | ∀ (φ : V) (ψ : W), ∃ (h : z.1 φ.1 ∈ V) (h' : z.2.unop ψ.1 ∈ W), B ⟨_, h⟩ ψ = B φ ⟨_, h'⟩}
  mul_mem' {x y} hx hy φ ψ := by
    obtain ⟨h1, -, -⟩ := hy φ ψ
    obtain ⟨h2, h3, e1⟩ := hx ⟨_, h1⟩ ψ
    obtain ⟨_, h4, e2⟩ := hy φ ⟨_, h3⟩
    exact ⟨h2, h4, e1.trans e2⟩
  add_mem' {x y} hx hy φ ψ := by
    obtain ⟨h1, h2, e1⟩ := hx φ ψ
    obtain ⟨h3, h4, e2⟩ := hy φ ψ
    refine ⟨add_mem h1 h3, add_mem h2 h4, ?_⟩
    change B (⟨_, h1⟩ + ⟨_, h3⟩) ψ = B φ (⟨_, h2⟩ + ⟨_, h4⟩)
    rw [map_add, LinearMap.add_apply, map_add, e1, e2]
  algebraMap_mem' c φ ψ := by
    refine ⟨V.smul_mem c φ.2, W.smul_mem c ψ.2, ?_⟩
    change B (c • φ) ψ = B φ (c • ψ)
    rw [map_smul, map_smul, LinearMap.smul_apply]

theorem infChar_conj_of_paired : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (π π' : CuspSub E a),
    Paired π π' conjOp → ∀ (τ : E →+* ℂ) (m m' : Multiset ℂ), π.HasInfChar τ m →
      π'.HasInfChar (NumberField.ComplexEmbedding.conjugate τ) m' → m' = m.map Neg.neg := by
  intro E _ _ _ a π π' ⟨B, hB, _, _, _, hL⟩ τ m m' hm hm'
  let S := adjPairs π.V π'.V B
  have h1 : ∀ i j z, (lieS E a i j (atEmb τ z), -op (lieS E a i j (atEmb (ComplexEmbedding.conjugate τ) z))) ∈ S := by
    intro i j z φ ψ
    have e : star (atEmb τ z) = atEmb (ComplexEmbedding.conjugate τ) z := by
      classical
      rw [atEmb_conj]
      unfold atEmb
      rw [Pi.star_single]
      split_ifs <;> rfl
    have e2 : conjOp (.lie (toL (Matrix.single i j (atEmb τ z))) : Op E a) =
        .lie (toL (Matrix.single i j (atEmb (ComplexEmbedding.conjugate τ) z))) := by
      refine congrArg Op.lie (funext fun k => funext fun l => ?_)
      change star (Matrix.single i j (atEmb τ z) k l) = Matrix.single i j _ k l
      rw [Matrix.single_apply, Matrix.single_apply, apply_ite star, e, star_zero]
    have h := hL (toL (Matrix.single i j (atEmb τ z))) φ ψ
    rw [e2, add_eq_zero_iff_eq_neg, ← map_neg] at h
    exact ⟨π.stable (.lie _) _ φ.2, neg_mem (π'.stable (.lie _) _ ψ.2), h⟩
  have h2 : ∀ i j, (Eop τ i j, -op (Eop (ComplexEmbedding.conjugate τ) i j)) ∈ S := fun i j => by
    convert S.smul_mem (S.sub_mem (h1 i j 1) (S.smul_mem (h1 i j Complex.I) Complex.I)) (1 / 2) using 1
    refine Prod.ext rfl ?_
    simp only [Eop, op_smul, op_sub, Prod.smul_snd, Prod.snd_sub]
    module
  have h3 : ∀ x, qdet (fun i j => (Eop (a := a) τ i j, -op (Eop (ComplexEmbedding.conjugate τ) i j))) x ∈ S := fun x => by
    refine S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.list_prod_mem fun x hx => ?_)
    obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
    refine S.add_mem ?_ (h2 _ _)
    split_ifs
    · exact S.algebraMap_mem _
    · exact S.zero_mem
  have h4 : ∀ u, (cap (a := a) τ u, op ((-1 : ℂ) ^ a • cap (a := a) (ComplexEmbedding.conjugate τ) (-u) : Module.End ℂ (Sm E a))) ∈ S := fun u => by
    convert h3 (u + ((a : ℂ) - 1) / 2) using 1
    rw [qdet_prod, qdet_antipode (A := Module.End ℂ (Sm E a)) (glRel_Eop (a := a) (ComplexEmbedding.conjugate τ)), show (a : ℂ) - 1 - (u + ((a : ℂ) - 1) / 2) = -u + ((a : ℂ) - 1) / 2 by ring]
    rfl
  have h5 : π.HasInfChar τ (m'.map Neg.neg) := by
    refine ⟨by rw [Multiset.card_map, hm'.1], fun u φ hφ => ?_⟩
    have e : ((m'.map Neg.neg).map (u + ·)) = (m'.map (-u + ·)).map Neg.neg := by
      rw [Multiset.map_map, Multiset.map_map]
      refine Multiset.map_congr rfl fun z _ => ?_
      simp only [Function.comp_apply]; ring
    rw [e, Multiset.prod_map_neg, Multiset.card_map, hm'.1]
    obtain ⟨h, -⟩ := h4 u ⟨φ, hφ⟩ 0
    refine sub_eq_zero.1 (congrArg Subtype.val (hB (⟨_, h⟩ - ((-1) ^ a * (m'.map (-u + ·)).prod) • ⟨φ, hφ⟩) fun ψ => ?_))
    obtain ⟨_, h', e'⟩ := h4 u ⟨φ, hφ⟩ ψ
    have e3 : (⟨_, h'⟩ : π'.V) = ((-1) ^ a * (m'.map (-u + ·)).prod) • ψ := Subtype.ext (by
      change (-1 : ℂ) ^ a • cap (ComplexEmbedding.conjugate τ) (-u) ψ.1 = _ • ψ.1
      rw [hm'.2 _ _ ψ.2, smul_smul])
    rw [map_sub, LinearMap.sub_apply, e', e3, map_smul, map_smul, LinearMap.smul_apply, sub_self]
  rw [hm.unique h5, Multiset.map_map]
  simp

end GlobalTheory.CapPair

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralJetsNormalisedThetaTranslatesAwayDisc
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

open scoped ComplexConjugate

theorem GlobalTheory.ThLoc.jetsIntegral_three (hIn : GlobalTheory.ThLoc.Inputs) {a₀ : ℕ} {b₀ c₀ : ℤ} {dK : ℕ} (ha : 0 < a₀) (hd : 0 < dK)
    (lam : ℂ) (hlam : lam ≠ 0) (hd3 : dK % 3 = 2) {n : Type} [Fintype n] [DecidableEq n] (h : Matrix n n ℂ)
    (Λ : AddSubgroup (n → ℂ)) (θ : (n → ℂ) → ℂ) (ι : ℂ ≃+* ℂ_[3])
    (hL : GlobalTheory.ThLoc.LatAt a₀ b₀ c₀ dK ha hd lam hlam h Λ θ 3 ι) (W : WeierstrassCurve ℂ_[3])
    (hU : Unif 3 (cmL a₀ b₀ dK ha hd lam hlam) ι W) (hW : IntCurve W)
    {κx : Type} [Fintype κx] (r : κx → ℂ_[3]) (t : κx → n → ℂ) (M : ℕ) (hr : ∀ k, ‖r k‖ ≤ 1) (hM : 0 < M)
    (hpM : ¬ 3 ∣ M) (ht : ∀ k, (M : ℂ) • t k ∈ Λ) {J : Type} [Fintype J] (v : J → n → ℂ)
    (hv : ∀ j, InMul (cmL a₀ b₀ dK ha hd lam hlam) Λ (v j)) {ν : Type} [Fintype ν] (A : J → ν → ℂ_[3])
    (hA : ∀ j x, ‖A j x‖ ≤ 1) :
    JetsIntegral (thetaLin (ι : ℂ →+* ℂ_[3]) h θ r t (frameM (ι : ℂ →+* ℂ_[3]) v A)) := by
  obtain ⟨hcmok, l2, l3, l4, l5⟩ := hL
  obtain ⟨-, -, hcm⟩ := GlobalTheory.ThLoc.LocJets.data ha hd lam hlam hcmok
  have hω : lam * (a₀ : ℂ) ∈ (cmL a₀ b₀ dK ha hd lam hlam).lattice :=
    (cmL a₀ b₀ dK ha hd lam hlam).ω₁_mem_lattice
  have hω1 : Formalism.L2.Th1.CM.omegaK dK * (lam * (a₀ : ℂ) / 2) ∉ (cmL a₀ b₀ dK ha hd lam hlam).lattice := by
    have := GlobalTheory.ThLoc.LocJets.half_notMem ha hd lam hlam hcmok 1 (Or.inl rfl)
    simpa [Formalism.L2.Th1.CM.omegaK] using this
  have hω2 : conj (Formalism.L2.Th1.CM.omegaK dK) * (lam * (a₀ : ℂ) / 2) ∉ (cmL a₀ b₀ dK ha hd lam hlam).lattice := by
    have := GlobalTheory.ThLoc.LocJets.half_notMem ha hd lam hlam hcmok (-1) (Or.inr rfl)
    rw [GlobalTheory.ThLoc.LocJets.conj_omegaK]
    simpa [sub_eq_add_neg] using this
  obtain ⟨g₁, ε, hiso, hidx, hidx', hε, hten⟩ := l5
  obtain ⟨Dm, q0, hD, hq0, hfac, hgram⟩ :=
    GlobalTheory.ThLoc.LocJets.gram_transfer a₀ b₀ c₀ dK ha hd lam hlam hcmok n h Λ g₁ hiso 3 ι hidx J v hv
  obtain ⟨Cm, q1, hCm, -, hfacC, -⟩ :=
    Formalism.L2.Th1.GD.FrameCompose_proof ℂ_[3] (Fin 4 × n) n J ν
      (fun w w' => ι (g₁.symm (Pi.single w' 1) w)) Dm (fun i j => ι (v j i))
      (fun j k => ι (Formalism.L2.Th1.GD.hOK (cmL a₀ b₀ dK ha hd lam hlam) h (v j) (v k))) _ q0 A hD hq0 hA hfac hgram
  have key : ∀ k, JetsIntegral (Formalism.L2.Th1.G.linSub (frameM (ι : ℂ →+* ℂ_[3]) v A)
        (MvPowerSeries.map (ι : ℂ →+* ℂ_[3]) (taylorMv (Formalism.L2.Th1.H.opU (matH h) (t k) θ)))) := by
    intro k
    obtain ⟨κ, _, r', s', N', hr', hN', h2N', hs', he⟩ := GlobalTheory.ThLoc.LocJets.fourth_power_theta a₀ b₀ c₀ dK ha hd
      lam hlam hcmok n h Λ l2 l3 θ l4 3 ι g₁ ε hiso hidx hidx' hε hten (t k) M hM hpM (ht k)
    have hj := hIn.jetsThree dK _ hcmok.2.2.1 hd3 hcm ι W hU hW (lam * a₀) hω hω1 hω2
      (Fin 4 × n) κ r' s' N' hr' hN' h2N' hs'
    rw [← he] at hj
    exact GlobalTheory.ThLoc.LocJets.jets_linear ℂ_[3] n _ _ hj ν (frameM (ι : ℂ →+* ℂ_[3]) v A) Cm hCm hfacC
  exact GlobalTheory.ThLoc.LocJets.jets_comb r _ hr key

theorem GlobalTheory.ThLoc.jetsIntegral_away_disc : GlobalTheory.ThLoc.Inputs → ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (lam : ℂ) (hlam : lam ≠ 0), CmOK a₀ b₀ c₀ D.host.d → (cmL a₀ b₀ D.host.d ha hd lam hlam).lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ → ∀ (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ)) (θ : (n → ℂ) → ℂ) (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]), GlobalTheory.ThLoc.LatAt a₀ b₀ c₀ D.host.d ha hd lam hlam h Λ θ p ι → p ≠ D.host.d → (p = 3 → D.host.d % 3 = 2) → ∀ (κx : Type) [Fintype κx] (r : κx → ℂ_[p]) (t : κx → n → ℂ) (M : ℕ), (∀ k, ‖r k‖ ≤ 1) → 0 < M → ¬ p ∣ M → (∀ k, (M : ℂ) • t k ∈ Λ) → ∀ (J : Type) [Fintype J] (v : J → n → ℂ), (∀ j, InMul (cmL a₀ b₀ D.host.d ha hd lam hlam) Λ (v j)) → ∀ (ν : Type) [Fintype ν] (A : J → ν → ℂ_[p]), (∀ j x, ‖A j x‖ ≤ 1) → JetsIntegral (thetaLin (ι : ℂ →+* ℂ_[p]) h θ r t (frameM (ι : ℂ →+* ℂ_[p]) v A)) := by
  intro hIn D cc δ hcc hδ a₀ b₀ c₀ ha hd lam hlam hcmok hlat n _ _ h Λ θ p _ ι hL hpd h3 κx _ r t M hr hM hpM ht
    J _ v hv ν _ A hA
  have hpr : p.Prime := Fact.out
  by_cases hp2 : p = 2
  · subst hp2
    obtain ⟨l1, l2, l3, l4, l5⟩ := hL
    obtain ⟨W, hU, hW, ha1⟩ := GlobalTheory.ThLoc.goodModelTwo_scaleOne hIn D cc δ hcc hδ a₀ b₀ c₀ ha hd lam hlam hcmok hlat ι
    exact (hIn.jetsTwo a₀ b₀ c₀ _ ha hd lam hlam l1 n h Λ l2 l3 θ l4 ι W hU hW ha1 l5 κx r t M hr hM hpM ht
      J v hv ν A hA).1
  by_cases hp3 : p = 3
  · subst hp3
    obtain ⟨W, hU, hW⟩ := GlobalTheory.ThLoc.ModelThree.goodModelThree hIn D cc δ hcc hδ a₀ b₀ c₀ ha hd lam hlam hcmok hlat ι
    exact GlobalTheory.ThLoc.jetsIntegral_three hIn ha hd lam hlam (h3 rfl) h Λ θ ι hL W hU hW r t M hr hM hpM ht v hv A hA
  obtain ⟨l1, l2, l3, l4, l5⟩ := hL
  have h4 : p ≠ 4 := by rintro rfl; exact absurd hpr (by decide)
  have h5 : 5 ≤ p := by have := hpr.two_le; omega
  have hW := GlobalTheory.GoodModelFive.goodModel_five hIn D cc δ hcc hδ a₀ b₀ c₀ ha hd lam hlam hcmok hlat p h5 ι
  have hnd : ¬ p ∣ D.host.d := fun hdv => hpd ((Nat.prime_dvd_prime_iff_eq hpr l1.2.2.2).1 hdv)
  exact (hIn.jetsOdd a₀ b₀ c₀ _ ha hd lam hlam l1 n h Λ l2 l3 θ l4 p hp2 hnd ι hW l5 κx r t M hr hM hpM ht
    J v hv ν A hA).1
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralWittUnitaryModUniformizerStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_witt_unitary_mod_uniformizer : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → ∀ (n' : ℕ) (JT : GL (Fin n') L),
    JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    ∀ (ι : Type) [Fintype ι] (z z' : ι → Fin n' → L), (∀ i r, z i r ∈ Formalism.UG.intL L) → (∀ i r, z' i r ∈ Formalism.UG.intL L) →
    GlobalTheory.Hk3.IntWitt.IndepMod ϖ z → GlobalTheory.Hk3.IntWitt.IndepMod ϖ z' →
    (∀ i j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ 1 (Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (z' i) (z' j) - Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (z i) (z j))) →
    ∃ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) ∧
      ∀ i r, GlobalTheory.Hk3.IntWitt.DvdPow ϖ 1 ((((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ z i) r - z' i r) := by
  first | exact @GlobalTheory.Hk3.IntWittBase.witt_mod_base | exact GlobalTheory.Hk3.IntWittBase.witt_mod_base | (intros; apply GlobalTheory.Hk3.IntWittBase.witt_mod_base <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InverseSeriesFormalGroupIsoIntegralStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inverse_series_formalGroup_iso_integral : ∀ (l : ℕ) [Fact l.Prime] (g : Formalism.MainNotions.GL3Theta.G1 l), g.Ok → ∀ (hLT : Formalism.L2.G.Pend.LTIso g) (n : ℕ), ‖PowerSeries.coeff n (Formalism.L2.KerInert.BeCob.vLT hLT)‖ ≤ 1 := by
  first | exact @GlobalTheory.InverseSeriesIntegral.v_integral | exact GlobalTheory.InverseSeriesIntegral.v_integral | (intros; apply GlobalTheory.InverseSeriesIntegral.v_integral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsLocalVacuumOfIsLatticeVacuumCoprimeLevelStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLocalVacuum_of_isLatticeVacuum_coprime_level : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) ΛS ΛT (NS NT : ℕ), IsBaseFrame S βS ΛS NS → IsBaseFrame T βT ΛT NT → ∀ P : Pl D.host.E, ((NS * NT : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal → ∀ f₀, IsThetaFunO ψ S T f₀ → IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun _ => True) f₀ → IsVacAt ψ S T P f₀ := by
  first | exact @GlobalTheory.VacLat.isVacAt_of_isLatVac | exact GlobalTheory.VacLat.isVacAt_of_isLatVac | (intros; apply GlobalTheory.VacLat.isVacAt_of_isLatVac <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalGlobalOfGelfandKazhdan
section
open NumberField GlobalTheory.CuspRep GlobalTheory.ContraPair

namespace GlobalTheory

theorem galoisRepOfPolarizedCuspidal_iff_pair : GlobalTheory.Published.GelfandKazhdanDual →
    (GlobalTheory.Published.CaraianiLocalGlobalDual → GlobalTheory.Published.CaraianiLocalGlobal) ∧
    (GlobalTheory.Published.GaloisRepOfPolarizedPair → GlobalTheory.Published.GaloisRepOfPolarizedCuspidal) := by
  intro hGK
  refine ⟨fun hC => ?_, fun hP => ?_⟩
  · intro E Ω _ _ _ _ _ _ l _ ι a ha π hcsd hcoh
    have hd : DualIsConj π :=
      (dualIsConjBy_one π).1 (GlobalTheory.T.cuspContragredientIsCMConjTwist_of_paired_invTranspose E a π 1 (hGK E a _) ((GlobalTheory.GalOfCusp.isConjDualBy_one π).2 hcsd))
    exact hC E Ω l ι a ha π hd hcoh
  · intro E Ω _ _ _ _ _ _ l _ ι a ha π χ hr hpol
    exact hP E Ω l ι a ha π χ hr
      ⟨hpol.sign, GlobalTheory.T.cuspContragredientIsCMConjTwist_of_paired_invTranspose E a π (GlobalTheory.GalOfCusp.compNorm E χ) (hGK E a _) hpol.dual⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LogCoordinatesExponentIsCoboundaryStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_coordinates_exponent_is_coboundary : Formalism.L2.KerInert.BeCob.CobExact := by
  first | exact @GlobalTheory.CobExactProof.cobExact | exact GlobalTheory.CobExactProof.cobExact | (intros; apply GlobalTheory.CobExactProof.cobExact <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormalSubgroupContainingHyperspecialEqTopUnramifStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normal_subgroup_containing_hyperspecial_eq_top_unramifiedUnitary : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ) (J : GL (Fin n) L), Formalism.UG.IsUnramInv ϖ σ q → Odd q → J ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) → (∀ i j, σ ((J : Matrix (Fin n) (Fin n) L) i j) = (J : Matrix (Fin n) (Fin n) L) j i) → ∀ N : Subgroup (Formalism.UG.UJ σ (J : Matrix (Fin n) (Fin n) L)), N.Normal → (∀ g : Formalism.UG.UJ σ (J : Matrix (Fin n) (Fin n) L), (g : GL (Fin n) L) ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) → g ∈ N) → N = ⊤ := by
  first | exact @GlobalTheory.NormalHyp.normal_closure_hyp | exact GlobalTheory.NormalHyp.normal_closure_hyp | (intros; apply GlobalTheory.NormalHyp.normal_closure_hyp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhEquivShortWeierstrassModelStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.phEquiv_shortWeierstrassModel : Formalism.L2.KerInert.BeCob.PhTie := by
  first | exact @GlobalTheory.ShortModelTie.phTie | exact GlobalTheory.ShortModelTie.phTie | (intros; apply GlobalTheory.ShortModelTie.phTie <;> assumption)
end

