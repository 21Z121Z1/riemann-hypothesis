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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0142
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0201
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0036
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0198

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GeometricLemmaCellOneBlockSwapEquiv
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.OneBlockCell

def valEquiv {β : Type} {n : β → ℕ} {t : ℕ} (a₀ : β) (ha₀ : n a₀ = t) (h0 : ∀ j, j ≠ a₀ → n j = 0) :
    (Σ j, Fin (n j)) ≃ Fin t where
  toFun p := ⟨p.2.val, by
    by_cases hp : p.1 = a₀
    · have h1 := p.2.2
      have h2 : n p.1 = t := hp ▸ ha₀
      omega
    · have h1 := p.2.2
      have h2 := h0 _ hp
      omega⟩
  invFun x := ⟨a₀, ⟨x.val, by have := x.2; omega⟩⟩
  left_inv p := by
    obtain ⟨a, s⟩ := p
    by_cases ha : a = a₀
    · subst ha
      rfl
    · have h1 := s.2
      have h2 := h0 _ ha
      omega
  right_inv x := rfl

@[simp] theorem val_valEquiv {β : Type} {n : β → ℕ} {t : ℕ} (a₀ : β) (ha₀ : n a₀ = t)
    (h0 : ∀ j, j ≠ a₀ → n j = 0) (p : Σ j, Fin (n j)) : (valEquiv a₀ ha₀ h0 p).val = p.2.val := rfl

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem deltaHalf_eq_one_of_single {β : Type} [Fintype β] [LinearOrder β] {n : β → ℕ} (a₀ : β)
    (h0 : ∀ j, j ≠ a₀ → n j = 0) (g : Levi k (fun j => Fin (n j))) :
    deltaHalf k (fun j => Fin (n j)) g = 1 := by
  rw [deltaHalf_apply]
  refine Finset.prod_eq_one fun a _ => ?_
  by_cases ha : a = a₀
  · subst ha
    have hs : ∀ s : Finset β, a ∉ s → ∑ b ∈ s, (Fintype.card (Fin (n b)) : ℤ) = 0 := fun s hs =>
      Finset.sum_eq_zero fun b hb => by
        have hba : b ≠ a := fun e => hs (e ▸ hb)
        simp [h0 b hba]
    have hm : modExp (fun j => Fin (n j)) a = 0 := by
      unfold modExp
      rw [hs _ (by simp), hs _ (by simp), sub_zero]
    rw [hm]
    simp
  · haveI : IsEmpty (Fin (n a)) := ⟨fun x => absurd x.2 (by have := x.2; have := h0 a ha; omega)⟩
    have : Matrix.GeneralLinearGroup.det (g a) = 1 := by
      ext
      simp [Matrix.det_isEmpty]
    rw [this, map_one]

theorem mem_parab_of_single {R : Type} [CommRing R] {β : Type} [LinearOrder β] {n : β → ℕ} {t : ℕ}
    (e : (Σ j, Fin (n j)) ≃ Fin t) (a₀ : β) (h0 : ∀ j, j ≠ a₀ → n j = 0) (x : GL (Fin t) R) :
    x ∈ parab R e := by
  refine mem_parab_iff.2 fun a b i j hab => ?_
  by_cases ha : a = a₀
  · have hb : b ≠ a₀ := fun e => by rw [e, ha] at hab; exact lt_irrefl _ hab
    exact absurd j.2 (by have := j.2; have := h0 b hb; omega)
  · exact absurd i.2 (by have := i.2; have := h0 a ha; omega)

theorem eq_one_of_mem_unipRad_single {R : Type} [CommRing R] {β : Type} [Fintype β] [LinearOrder β]
    {n : β → ℕ} {t : ℕ} (e : (Σ j, Fin (n j)) ≃ Fin t) (a₀ : β) (h0 : ∀ j, j ≠ a₀ → n j = 0)
    {g : GL (Fin t) R} (hg : g ∈ unipRad R e) : g = 1 := by
  obtain ⟨-, h2⟩ := mem_unipRad.1 hg
  refine Units.ext (Matrix.ext fun x y => ?_)
  obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective x
  obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective y
  by_cases ha : a = a₀
  · by_cases hb : b = a₀
    · obtain rfl : b = a := hb.trans ha.symm
      rw [h2 b i j]
      simp [Matrix.one_apply]
    · exact absurd j.2 (by have := j.2; have := h0 b hb; omega)
  · exact absurd i.2 (by have := i.2; have := h0 a ha; omega)

open scoped TensorProduct

theorem reindex_piTensor {d : Fin 2 → ℕ} (σ : ∀ i, Irr k (d i)) (γ : ∀ i, GL (Fin (d i)) k)
    (p : ∀ j, GL (Fin (d (Equiv.swap 0 1 j))) k) (h : ∀ j, γ (Equiv.swap 0 1 j) = p j)
    (y : ⨂[ℂ] i, (σ i).V) :
    PiTensorProduct.reindex ℂ (fun i => (σ i).V) (Equiv.swap 0 1) ((piTensor fun i => (σ i).π) γ y) =
      (piTensor fun j => (σ (Equiv.swap 0 1 j)).π) p
        (PiTensorProduct.reindex ℂ (fun i => (σ i).V) (Equiv.swap 0 1) y) := by
  suffices H : (PiTensorProduct.reindex ℂ (fun i => (σ i).V) (Equiv.swap 0 1)).toLinearMap ∘ₗ
      (piTensor fun i => (σ i).π) γ = (piTensor fun j => (σ (Equiv.swap 0 1 j)).π) p ∘ₗ
      (PiTensorProduct.reindex ℂ (fun i => (σ i).V) (Equiv.swap 0 1)).toLinearMap from
    LinearMap.congr_fun H y
  refine PiTensorProduct.ext (MultilinearMap.ext fun z => ?_)
  have e1 : (((piTensor fun j => (σ (Equiv.swap 0 1 j)).π) p ∘ₗ
      (PiTensorProduct.reindex ℂ (fun i => (σ i).V) (Equiv.swap 0 1)).toLinearMap).compMultilinearMap
        (PiTensorProduct.tprod ℂ)) z = (piTensor fun j => (σ (Equiv.swap 0 1 j)).π) p
          (PiTensorProduct.reindex ℂ (fun i => (σ i).V) (Equiv.swap 0 1) (PiTensorProduct.tprod ℂ z)) := rfl
  have e2 := PiTensorProduct.reindex_tprod (R := ℂ) (s := fun i => (σ i).V) (Equiv.swap 0 1) z
  have e3 := piTensor_tprod (fun j => (σ (Equiv.swap 0 1 j)).π) p (fun j => z (Equiv.swap 0 1 j))
  refine Eq.trans ?_ e1.symm
  refine Eq.trans ?_ (congrArg (fun w => (piTensor fun j => (σ (Equiv.swap 0 1 j)).π) p w) e2).symm
  refine Eq.trans ?_ e3.symm
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    piTensor_tprod, PiTensorProduct.reindex_tprod]
  refine congrArg (PiTensorProduct.tprod ℂ (s := fun j => (σ (Equiv.swap 0 1 j)).V)) (funext fun j => ?_)
  show (σ (Equiv.swap 0 1 j)).π (γ (Equiv.swap 0 1 j)) (z (Equiv.swap 0 1 j)) = _
  rw [h j]

theorem cellFunctor_swap_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (d : Fin 2 → ℕ) (σ : ∀ i, Irr k (d i)), d 1 = 1 →
    ∀ (b : SizeMatrix (fun i : Fin 2 => Fin (d i)) (fun j : Fin 2 => Fin (d (Equiv.swap 0 1 j)))), b.1 1 0 = 1 →
    ∃ (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Fin (d i)) (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Fin (d (Equiv.swap 0 1 j))),
      Nonempty ((cellFunctor f g (piTensor fun i => (σ i).π)).Equiv
        (piTensor fun j => (σ (Equiv.swap 0 1 j)).π)) := by
  intro k _ _ _ _ d σ hd b hb
  have r0 := b.2.1 0
  have r1 := b.2.1 1
  have c0 := b.2.2 0
  have c1 := b.2.2 1
  simp only [Fin.sum_univ_two, Fintype.card_fin, Equiv.swap_apply_left, Equiv.swap_apply_right] at r0 r1 c0 c1
  have h00 : b.1 0 0 = 0 := by omega
  have h11 : b.1 1 1 = 0 := by omega
  have hrz : ∀ i j, j ≠ Equiv.swap 0 1 i → b.1 i j = 0 := by
    intro i j hj
    fin_cases i <;> fin_cases j <;> simp_all
  have hcz : ∀ j i, i ≠ Equiv.swap 0 1 j → b.1 i j = 0 := by
    intro j i hi
    fin_cases i <;> fin_cases j <;> simp_all
  have hrf : ∀ i, b.1 i (Equiv.swap 0 1 i) = d i := by
    intro i
    fin_cases i <;> simp <;> omega
  have hcf : ∀ j, b.1 (Equiv.swap 0 1 j) j = d (Equiv.swap 0 1 j) := by
    intro j
    fin_cases j <;> simp <;> omega

  let f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Fin (d i) := fun i =>
    valEquiv (Equiv.swap 0 1 i) (hrf i) (fun j hj => hrz i j hj)
  let g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Fin (d (Equiv.swap 0 1 j)) := fun j =>
    valEquiv (Equiv.swap 0 1 j) (hcf j) (fun i hi => hcz j i hi)
  refine ⟨f, g, ?_⟩
  have hbot : twKer (piTensor fun i => (σ i).π) (relUnip k f) 1 = ⊥ := by
    refine eq_bot_iff.2 (Submodule.span_le.2 ?_)
    rintro _ ⟨n, v, rfl⟩
    have : (n : Levi k (fun i => Fin (d i))) = 1 := funext fun i =>
      eq_one_of_mem_unipRad_single (f i) (Equiv.swap 0 1 i) (fun j hj => hrz i j hj) (n.2 i trivial)
    simp [this]
  have hδ : ∀ z, relDeltaHalf k (fun i j => Fin (b.1 i j)) z = 1 := fun z => by
    rw [relDeltaHalf_apply]
    exact Finset.prod_eq_one fun i _ =>
      deltaHalf_eq_one_of_single (Equiv.swap 0 1 i) (fun j hj => hrz i j hj) (z i)
  have hδ' : ∀ z, relDeltaHalf k (fun j i => Fin (b.1 i j)) z = 1 := fun z => by
    rw [relDeltaHalf_apply]
    exact Finset.prod_eq_one fun j _ =>
      deltaHalf_eq_one_of_single (Equiv.swap 0 1 j) (fun i hi => hcz j i hi) (z j)
  have hP : ∀ x, x ∈ relParab k g := fun x j _ =>
    mem_parab_of_single (g j) (Equiv.swap 0 1 j) (fun i hi => hcz j i hi) (x j)
  have hγ : ∀ (p : relParab k g) j,
      relEmb k f (swapBlocks k (fun i j => Fin (b.1 i j)) (relProj k g p)) (Equiv.swap 0 1 j) =
        (p : Levi k (fun j => Fin (d (Equiv.swap 0 1 j)))) j := by
    intro p j
    rw [relEmb_apply]
    refine Units.ext (Matrix.ext fun x y => ?_)
    obtain ⟨⟨a, t⟩, rfl⟩ := (f (Equiv.swap 0 1 j)).surjective x
    obtain ⟨⟨a', s⟩, rfl⟩ := (f (Equiv.swap 0 1 j)).surjective y
    have ha : a = j := by
      by_contra hne
      have h1 := hrz (Equiv.swap 0 1 j) a (by rwa [Equiv.swap_apply_self])
      have h2 := t.2
      omega
    have ha' : a' = j := by
      by_contra hne
      have h1 := hrz (Equiv.swap 0 1 j) a' (by rwa [Equiv.swap_apply_self])
      have h2 := s.2
      omega
    subst ha
    subst ha'
    rw [leviEmb_apply_same]
    rfl

  have hsm : IsSmooth (piTensor fun j => (σ (Equiv.swap 0 1 j)).π) :=
    isSmooth_piTensor fun j => (σ (Equiv.swap 0 1 j)).smooth
  let R := PiTensorProduct.reindex ℂ (fun i => (σ i).V) (Equiv.swap 0 1)
  let Ψ : (⨂[ℂ] j, (σ (Equiv.swap 0 1 j)).V) ≃ₗ[ℂ]
      Jacquet (piTensor fun i => (σ i).π) (relUnip k f) :=
    R.symm.trans (Submodule.quotEquivOfEqBot _ hbot).symm
  have hΨ : ∀ u, Ψ u = Submodule.Quotient.mk (R.symm u) := fun u => rfl
  let τ := (twist ((relJac f (piTensor fun i => (σ i).π)).comp (swapBlocks k (fun i j => Fin (b.1 i j))))
        (relDeltaHalf k (fun j i => Fin (b.1 i j)))).comp (relProj k g)
  have law : ∀ (p : relParab k g) u, τ p (Ψ u) =
        Ψ ((piTensor fun j => (σ (Equiv.swap 0 1 j)).π) p u) := by
    intro p u
    rw [MonoidHom.comp_apply, twist_apply, MonoidHom.comp_apply, hΨ, relJac_mk, hδ, hδ', hΨ]
    simp only [inv_one, Units.val_one, one_smul]
    congr 1
    apply R.injective
    rw [reindex_piTensor σ _ (p : Levi k (fun j => Fin (d (Equiv.swap 0 1 j)))) (hγ p)]
    exact (congrArg (fun w => (piTensor fun j => (σ (Equiv.swap 0 1 j)).π)
      (p : Levi k (fun j => Fin (d (Equiv.swap 0 1 j)))) w) (R.apply_symm_apply u)).trans
        (R.apply_symm_apply _).symm
  let F : (piTensor fun j => (σ (Equiv.swap 0 1 j)).π).IntertwiningMap
      (cellFunctor f g (piTensor fun i => (σ i).π)) :=
    { toFun := fun u => ⟨⟨fun x => Ψ ((piTensor fun j => (σ (Equiv.swap 0 1 j)).π) x u), fun p x => by
          show Ψ ((piTensor fun j => (σ (Equiv.swap 0 1 j)).π) (↑p * x) u) = _
          rw [map_mul, Module.End.mul_apply]
          exact (law p _).symm⟩,
        mem_smoothPart_of_nhds (Filter.mem_of_superset ((hsm u).mem_nhds (by simp)) fun x hx => by
          have hx' : (piTensor fun j => (σ (Equiv.swap 0 1 j)).π) x u = u := hx
          refine Subtype.ext (funext fun y => ?_)
          show Ψ ((piTensor fun j => (σ (Equiv.swap 0 1 j)).π) (y * x) u) =
            Ψ ((piTensor fun j => (σ (Equiv.swap 0 1 j)).π) y u)
          rw [map_mul, Module.End.mul_apply, hx'])⟩
      map_add' := fun u w => Subtype.ext (Subtype.ext (funext fun x => by simp))
      map_smul' := fun c u => Subtype.ext (Subtype.ext (funext fun x => by simp))
      isIntertwining' := fun h => LinearMap.ext fun u => Subtype.ext (Subtype.ext (funext fun x => by
        show Ψ ((piTensor fun j => (σ (Equiv.swap 0 1 j)).π) x
            ((piTensor fun j => (σ (Equiv.swap 0 1 j)).π) h u)) =
          Ψ ((piTensor fun j => (σ (Equiv.swap 0 1 j)).π) (x * h) u)
        rw [map_mul, Module.End.mul_apply])) }
  refine ⟨(LocGL.equivOfBijective F ⟨fun u w hw => ?_, fun φ => ⟨Ψ.symm (φ.1.1 1),
    Subtype.ext (Subtype.ext (funext fun x => ?_))⟩⟩).symm⟩
  · have h1 : Ψ ((piTensor fun j => (σ (Equiv.swap 0 1 j)).π) 1 u) =
        Ψ ((piTensor fun j => (σ (Equiv.swap 0 1 j)).π) 1 w) := congrArg (fun φ => φ.1.1 1) hw
    simpa using h1
  · show Ψ ((piTensor fun j => (σ (Equiv.swap 0 1 j)).π) x (Ψ.symm (φ.1.1 1))) = φ.1.1 x
    refine (law ⟨x, hP x⟩ (Ψ.symm (φ.1.1 1))).symm.trans ?_
    refine (congrArg (τ ⟨x, hP x⟩) (Ψ.apply_symm_apply (φ.1.1 1))).trans ?_
    refine (φ.1.2 ⟨x, hP x⟩ 1).symm.trans ?_
    exact congrArg φ.1.1 (mul_one x)

end GlobalTheory.OneBlockCell
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HoweUnramifiedAllVacua
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3

theorem comb_of_scalar {X A M : Type} [AddCommGroup M] [Module ℂ M] (vac : M → Prop) (r : X → Module.End ℂ M)
    (a : A → Module.End ℂ M) (ha : ∀ p, ∃ c : X →₀ ℂ, ∀ s, vac s → a p s = c.sum fun x z => z • r x s) (cA : A →₀ ℂ) :
    ∃ C : X →₀ ℂ, ∀ s, vac s → (cA.sum fun p z => z • a p s) = C.sum fun x z => z • r x s := by
  choose ca hca using ha
  refine ⟨Finsupp.linearCombination ℂ ca cA, fun s hs => ?_⟩
  have h : Finsupp.linearCombination ℂ (fun x => r x s) (Finsupp.linearCombination ℂ ca cA) =
      Finsupp.linearCombination ℂ (fun p => a p s) cA := by
    rw [LinearMap.map_finsupp_linearCombination]
    congr 2
    funext p
    simp only [Function.comp, hca p s hs, Finsupp.linearCombination_apply]
  calc (cA.sum fun p z => z • a p s) = Finsupp.linearCombination ℂ (fun p => a p s) cA :=
        (Finsupp.linearCombination_apply ℂ cA).symm
    _ = _ := h.symm
    _ = _ := Finsupp.linearCombination_apply ℂ _

theorem comb_transfer {X A B M : Type} [AddCommGroup M] [Module ℂ M] (vac : M → Prop) (r : X → Module.End ℂ M)
    (a : A → Module.End ℂ M) (b : B → Module.End ℂ M)
    (hmodel : ∀ c : X →₀ ℂ, ∀ s, s ≠ 0 → vac s → (c.sum fun x z => z • r x s) = 0 →
      ∀ s', vac s' → (c.sum fun x z => z • r x s') = 0)
    (ha : ∀ p, ∃ c : X →₀ ℂ, ∀ s, vac s → a p s = c.sum fun x z => z • r x s)
    (hb : ∀ p, ∃ c : X →₀ ℂ, ∀ s, vac s → b p s = c.sum fun x z => z • r x s)
    (cA : A →₀ ℂ) (cB : B →₀ ℂ) (s0 : M) (h0 : s0 ≠ 0) (hv : vac s0)
    (heq : (cA.sum fun p z => z • a p s0) = cB.sum fun p z => z • b p s0) :
    ∀ s, vac s → (cA.sum fun p z => z • a p s) = cB.sum fun p z => z • b p s := by
  obtain ⟨CA, hA⟩ := comb_of_scalar vac r a ha cA
  obtain ⟨CB, hB⟩ := comb_of_scalar vac r b hb cB
  have hsub : ∀ s, ((CA - CB).sum fun x z => z • r x s) =
      (CA.sum fun x z => z • r x s) - CB.sum fun x z => z • r x s := by
    intro s
    have e : ∀ C : X →₀ ℂ, (C.sum fun x z => z • r x s) = Finsupp.linearCombination ℂ (fun x => r x s) C :=
      fun C => (Finsupp.linearCombination_apply ℂ C).symm
    rw [e, e, e, map_sub]
  have h0' : ((CA - CB).sum fun x z => z • r x s0) = 0 := by
    rw [hsub, ← hA _ hv, ← hB _ hv, heq, sub_self]
  intro s hs
  have h := hmodel (CA - CB) s0 h0 hv h0' s hs
  rw [hsub, sub_eq_zero, ← hA s hs, ← hB s hs] at h
  exact h

theorem howe_on_span (hH : HoweUnram) {L : Type} [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L]
    {ϖ : L} {σ : L →+* L} {q : ℕ} {δ : L} {n n' : ℕ} {JS : GL (Fin n) L} {JT : GL (Fin n') L} {ψ : AddChar L ℂ}
    {M : Type} [AddCommGroup M] [Module ℂ M] {ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M}
    {ω : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M}
    (hp : LocPair ϖ σ q δ JS JT ψ ρ ω) (s0 : M) (h0 : s0 ≠ 0) (hv : LocVac ρ s0) :
    (∀ w ∈ Submodule.span ℂ (Set.range fun x => ρ x s0),
      (∀ g : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L),
        (g : GL (Fin n) L) ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) → ω (g, 1) w = w) →
      w ∈ Submodule.span ℂ (Set.range fun h => ω (1, h) s0)) ∧
    ∀ w ∈ Submodule.span ℂ (Set.range fun x => ρ x s0),
      (∀ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L),
        (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) → ω (1, h) w = w) →
      w ∈ Submodule.span ℂ (Set.range fun g => ω (g, 1) s0) := by
  have scal := GlobalTheory.T.unramifiedLocalPair_acts_on_vacua_by_heisenberg_comb L ϖ σ q δ n n' JS JT ψ M ρ ω hp
  set M0 := Submodule.span ℂ (Set.range fun x => ρ x s0) with hM0
  have hs0 : s0 ∈ M0 := by
    refine Submodule.subset_span ⟨0, ?_⟩
    simp [hp.rho_zero]
  have hρ : ∀ x, ∀ m ∈ M0, ρ x m ∈ M0 := by
    intro x m hm
    have hle : M0 ≤ M0.comap (ρ x) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨y, rfl⟩
      have e : ρ x (ρ y s0) = (ρ x * ρ y) s0 := rfl
      simp only [SetLike.mem_coe, Submodule.mem_comap]
      rw [e, hp.rho_mul x y]
      exact M0.smul_mem _ (Submodule.subset_span ⟨x + y, rfl⟩)
    exact hle hm
  have hω : ∀ p, ∀ m ∈ M0, ω p m ∈ M0 := by
    rintro ⟨g, h⟩ m hm
    have hle : M0 ≤ M0.comap (ω (g, h)) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨y, rfl⟩
      have e : ω (g, h) (ρ y s0) = (ω (g, h) * ρ y) s0 := rfl
      simp only [SetLike.mem_coe, Submodule.mem_comap]
      rw [e, hp.norm g h y]
      refine hρ _ _ ?_
      obtain ⟨c, hc⟩ := scal (g, h)
      rw [hc s0 hv]
      exact Finsupp.mem_span_range_iff_exists_finsupp.2 ⟨c, rfl⟩
    exact hle hm
  let ρ0 : Matrix (Fin n') (Fin n) L → Module.End ℂ M0 := fun x => (ρ x).restrict (hρ x)
  let ω0 : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M0 :=
    { toFun := fun p => (ω p).restrict (hω p)
      map_one' := by
        ext m
        simp
      map_mul' := by
        intro p p'
        ext m
        simp }
  have ρ0_val : ∀ x (m : M0), ((ρ0 x m : M0) : M) = ρ x m := fun _ _ => rfl
  have ω0_val : ∀ p (m : M0), ((ω0 p m : M0) : M) = ω p m := fun _ _ => rfl
  let t0 : M0 := ⟨s0, hs0⟩
  have hv0 : LocVac ρ0 t0 := fun u hu => Subtype.ext (hv u hu)
  have ht0 : t0 ≠ 0 := fun h => h0 (congrArg Subtype.val h)
  have hspan : Submodule.span ℂ (Set.range fun x => ρ0 x t0) = ⊤ := by
    have e : (Set.range fun x => ρ0 x t0) = (Subtype.val ⁻¹' (Set.range fun x => ρ x s0) : Set M0) := by
      ext m
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨x, rfl⟩
      · rintro ⟨x, hx⟩
        exact ⟨x, Subtype.ext hx⟩
    rw [e]
    exact Submodule.span_span_coe_preimage
  have hp0 : LocPair ϖ σ q δ JS JT ψ ρ0 ω0 :=
    { unr := hp.unr
      odd := hp.odd
      intS := hp.intS
      intT := hp.intT
      hermS := hp.hermS
      hermT := hp.hermT
      delta := hp.delta
      psi_int := hp.psi_int
      psi_ne := hp.psi_ne
      rho_zero := by
        ext m
        simp [ρ0, hp.rho_zero]
      rho_mul := by
        intro x y
        ext m
        have h := congrArg (fun T : Module.End ℂ M => T (m : M)) (hp.rho_mul x y)
        exact h
      span := by
        rw [eq_top_iff, ← hspan]
        refine Submodule.span_mono ?_
        rintro _ ⟨x, rfl⟩
        exact ⟨x, t0, hv0, rfl⟩
      norm := by
        intro g h x
        ext m
        have e := congrArg (fun T : Module.End ℂ M => T (m : M)) (hp.norm g h x)
        exact e
      fix := by
        intro g h hg hh s hs
        exact Subtype.ext (hp.fix g h hg hh s (fun u hu => congrArg Subtype.val (hs u hu))) }
  obtain ⟨h1, h2⟩ := hH L ϖ σ q δ n n' JS JT ψ M0 ρ0 ω0 hp0 t0 ht0 hv0 hspan
  constructor
  · intro w hw hfix
    have h := Submodule.mem_map_of_mem (f := M0.subtype) (h1 ⟨w, hw⟩ (fun g hg => Subtype.ext (hfix g hg)))
    rw [Submodule.map_span, ← Set.range_comp] at h
    exact h
  · intro w hw hfix
    have h := Submodule.mem_map_of_mem (f := M0.subtype) (h2 ⟨w, hw⟩ (fun g hg => Subtype.ext (hfix g hg)))
    rw [Submodule.map_span, ← Set.range_comp] at h
    exact h

theorem howe_all_vacua : HoweUnram → ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L) (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ) (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M) (ω : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M), LocPair ϖ σ q δ JS JT ψ ρ ω → (∀ cT : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →₀ ℂ, (∀ s, LocVac ρ s → ∀ k : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (k : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) → ω (1, k) (cT.sum fun b z => z • ω (1, b) s) = cT.sum fun b z => z • ω (1, b) s) → ∃ cS : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) →₀ ℂ, ∀ s, LocVac ρ s → (cT.sum fun b z => z • ω (1, b) s) = cS.sum fun a z => z • ω (a, 1) s) ∧ ∀ cS : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) →₀ ℂ, (∀ s, LocVac ρ s → ∀ k : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L), (k : GL (Fin n) L) ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) → ω (k, 1) (cS.sum fun a z => z • ω (a, 1) s) = cS.sum fun a z => z • ω (a, 1) s) → ∃ cT : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →₀ ℂ, ∀ s, LocVac ρ s → (cS.sum fun a z => z • ω (a, 1) s) = cT.sum fun b z => z • ω (1, b) s := by
  intro hH L _ _ _ _ ϖ σ q δ n n' JS JT ψ M _ _ ρ ω hp
  have scal := GlobalTheory.T.unramifiedLocalPair_acts_on_vacua_by_heisenberg_comb L ϖ σ q δ n n' JS JT ψ M ρ ω hp
  have model := GlobalTheory.T.locPair_vacuum_relation_independent L ϖ σ q δ n n' JS JT ψ M ρ ω hp
  by_cases hz : ∃ s0 : M, s0 ≠ 0 ∧ LocVac ρ s0
  · obtain ⟨s0, h0, hv⟩ := hz
    obtain ⟨hA, hB⟩ := howe_on_span hH hp s0 h0 hv
    refine ⟨fun cT hT => ?_, fun cS hS => ?_⟩
    · have hw : (cT.sum fun b z => z • ω (1, b) s0) ∈ Submodule.span ℂ (Set.range fun x => ρ x s0) := by
        obtain ⟨C, hC⟩ := comb_of_scalar (LocVac ρ) ρ (fun b => ω (1, b)) (fun b => scal (1, b)) cT
        rw [hC s0 hv]
        exact Finsupp.mem_span_range_iff_exists_finsupp.2 ⟨C, rfl⟩
      obtain ⟨cS, hcS⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 (hB _ hw (hT s0 hv))
      exact ⟨cS, comb_transfer (LocVac ρ) ρ (fun b => ω (1, b)) (fun a => ω (a, 1)) model
        (fun b => scal (1, b)) (fun a => scal (a, 1)) cT cS s0 h0 hv hcS.symm⟩
    · have hw : (cS.sum fun a z => z • ω (a, 1) s0) ∈ Submodule.span ℂ (Set.range fun x => ρ x s0) := by
        obtain ⟨C, hC⟩ := comb_of_scalar (LocVac ρ) ρ (fun a => ω (a, 1)) (fun a => scal (a, 1)) cS
        rw [hC s0 hv]
        exact Finsupp.mem_span_range_iff_exists_finsupp.2 ⟨C, rfl⟩
      obtain ⟨cT, hcT⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 (hA _ hw (hS s0 hv))
      exact ⟨cT, comb_transfer (LocVac ρ) ρ (fun a => ω (a, 1)) (fun b => ω (1, b)) model
        (fun a => scal (a, 1)) (fun b => scal (1, b)) cS cT s0 h0 hv hcT.symm⟩
  · have hz' : ∀ s, LocVac ρ s → s = 0 := by
      intro s hs
      by_contra hne
      exact hz ⟨s, hne, hs⟩
    refine ⟨fun cT _ => ⟨0, fun s hs => ?_⟩, fun cS _ => ⟨0, fun s hs => ?_⟩⟩
    · simp [hz' s hs, Finsupp.sum]
    · simp [hz' s hs, Finsupp.sum]

end GlobalTheory.Hk3

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IrreducibleGl1IsoDetStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducible_gl1_iso_det : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (d : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL (Fin d) k) V) (ω : kˣ →* ℂˣ), d = 1 → σ.IsIrreducible → GlobalTheory.SmGL.HasCentralChar σ ω → Nonempty (σ.Equiv (GlobalTheory.SmGL.detRep (Fin d) ω)) := by
  first | exact @GlobalTheory.GLOneChar.equiv_detRep_of_isIrreducible | exact GlobalTheory.GLOneChar.equiv_detRep_of_isIrreducible | (intros; apply GlobalTheory.GLOneChar.equiv_detRep_of_isIrreducible <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IrreducibleSubquotientEigenvectorStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducible_subquotient_eigenvector : ∀ (G V : Type) [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (x : V), x ≠ 0 →
    ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y) (τ : Representation ℂ G Y) (y : Y),
      τ.IsIrreducible ∧ GlobalTheory.SmGL.IsSubquotient τ ρ ∧ y ≠ 0 ∧ ∀ (g : G) (c : ℂ), ρ g x = c • x → τ g y = c • y := by
  first | exact @GlobalTheory.VecSubquot.exists_irreducible_subquotient_of_ne_zero | exact GlobalTheory.VecSubquot.exists_irreducible_subquotient_of_ne_zero | (intros; apply GlobalTheory.VecSubquot.exists_irreducible_subquotient_of_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSplitPlaceOfSplitPlaceRealSubfieldHostStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSplitPlace_of_splitPlace_realSubfield_host : ∀ (D : D7) (s : SplitPlace D.host.E), IsSplitPl D.host s.w := by
  first | exact @GlobalTheory.SplitPlaceConj.isSplitPl_w | exact GlobalTheory.SplitPlaceConj.isSplitPl_w | (intros; apply GlobalTheory.SplitPlaceConj.isSplitPl_w <;> assumption)
end

