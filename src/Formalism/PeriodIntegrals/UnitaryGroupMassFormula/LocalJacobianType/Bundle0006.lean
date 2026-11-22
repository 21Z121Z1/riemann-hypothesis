import Mathlib
import Formalism.PeriodIntegrals.Bundle0019
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.Bundle0005
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.KitScale

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.CentreVolume
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.LocJacTyp

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain PI.LocJacTyp
open scoped TensorProduct

attribute [local instance] PI.VolStabSW.secondCountable_Fv PI.VolStabSW.locallyCompact_Fv
attribute [local instance] Sd.finDim

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F))

theorem centre_volume : VolZZ σ v := by
  intro g r TF TF' m hS hg hTF hTF' hdiff μ hμ hm
  haveI := hμ
  obtain ⟨D⟩ := exists_SD hS
  have hp0 : ∀ s t, D.p 0 (D.pt s t) = s := fun s t => (D.p_pt s t).1
  have hp1 : ∀ s t, D.p 1 (D.pt s t) = t := fun s t => (D.p_pt s t).2
  have hg0 : (g : Fv F v) ≠ 0 := natCast_ne_zero v hg
  have hgO : (g : Fv F v) ∈ v.adicCompletionIntegers F := natCast_mem _ g
  have hT1 : ∀ a b, sigR (Fv F v) σ (TF b a) = TF a b := hTF
  have hT1' : ∀ a b, sigR (Fv F v) σ (TF' b a) = TF' a b := hTF'
  have hf : ∀ a b, D.p 1 (TF a b) = D.p 0 (TF b a) := fun a b => by rw [← hT1 a b, (D.p_sig _).2]
  have hf' : ∀ a b, D.p 1 (TF' a b) = D.p 0 (TF' b a) := fun a b => by rw [← hT1' a b, (D.p_sig _).2]
  obtain ⟨t, ht⟩ : ∃ t : Fin (r + 1) × Fin (r + 1) → Fv F v, ∀ k, t k = alp v r k.1 * alp v r k.2 :=
    ⟨_, fun _ => rfl⟩
  have ht0 : ∀ k, t k ≠ 0 := fun k => by rw [ht]; exact mul_ne_zero (alp_ne_zero v r _) (alp_ne_zero v r _)
  obtain ⟨y, hy⟩ : ∃ y : Fin (r + 1) × Fin (r + 1) → Fv F v ⊗[F] E,
      ∀ k, y k = D.pt (((g : Fv F v)⁻¹) ^ 2 * t k) ((g : Fv F v)⁻¹ * t k) := ⟨_, fun _ => rfl⟩
  obtain ⟨κ, hκ⟩ : ∃ κ : Fin (r + 1) × Fin (r + 1) → Fv F v ⊗[F] E,
      ∀ k, κ k = D.pt (-(D.p 0 (TF k.1 k.2) + D.p 0 (TF' k.1 k.2)) / t k) (-(D.p 0 (TF k.2 k.1)) / t k) :=
    ⟨_, fun _ => rfl⟩
  have hd : ∀ i j, (D.p 0 (TF' i j) - D.p 0 (TF i j)) * (g : Fv F v)⁻¹ ∈ v.adicCompletionIntegers F := by
    intro i j
    have := hdiff i j
    rw [D.mem_iff] at this
    simpa only [map_mul, map_sub, D.p_sc] using this.1
  have hset : ZZTyp σ v g r TF TF' = (D.shear Prod.swap) ⁻¹' ((fun w => w + κ) ⁻¹'
      Set.univ.pi fun k => {c | y k * c ∈ OEv (E := E) v}) := by
    ext z
    simp only [ZZTyp, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies,
      Pi.add_apply]
    have hR : ∀ i j, y (i, j) * ((D.shear Prod.swap) z (i, j) + κ (i, j)) ∈ OEv (E := E) v ↔
        ((g : Fv F v)⁻¹) ^ 2 * t (i, j) * (D.p 0 (z (i, j)) + D.p 1 (z (j, i)) +
            -(D.p 0 (TF i j) + D.p 0 (TF' i j)) / t (i, j)) ∈ v.adicCompletionIntegers F ∧
          (g : Fv F v)⁻¹ * t (i, j) * (D.p 1 (z (i, j)) + -(D.p 0 (TF j i)) / t (i, j)) ∈
            v.adicCompletionIntegers F := by
      intro i j
      rw [D.mem_iff, hy, hκ, map_mul, map_mul, map_add, map_add, D.shear_first_coordinate, D.shear_second_coordinate, hp0, hp1, hp0, hp1]
      rfl
    have hL : ∀ i j, ((locZ v z i j - TF i j) * sc (E := E) v (g : Fv F v)⁻¹ ∈ OEv (E := E) v ∧
        ((locZ v z i j - TF i j) * sc (E := E) v (g : Fv F v)⁻¹ +
          sigR (Fv F v) σ ((locZ v z j i - TF j i) * sc (E := E) v (g : Fv F v)⁻¹) -
          (TF' i j - TF i j) * sc (E := E) v (g : Fv F v)⁻¹) * sc (E := E) v (g : Fv F v)⁻¹ ∈ OEv (E := E) v) ↔
        (((alp v r i * alp v r j) * D.p 0 (z (i, j)) - D.p 0 (TF i j)) * (g : Fv F v)⁻¹ ∈
            v.adicCompletionIntegers F ∧
          ((alp v r i * alp v r j) * D.p 1 (z (i, j)) - D.p 0 (TF j i)) * (g : Fv F v)⁻¹ ∈
            v.adicCompletionIntegers F) ∧
        ((((alp v r i * alp v r j) * D.p 0 (z (i, j)) - D.p 0 (TF i j)) * (g : Fv F v)⁻¹ +
            ((alp v r j * alp v r i) * D.p 1 (z (j, i)) - D.p 0 (TF i j)) * (g : Fv F v)⁻¹ -
            (D.p 0 (TF' i j) - D.p 0 (TF i j)) * (g : Fv F v)⁻¹) * (g : Fv F v)⁻¹ ∈
            v.adicCompletionIntegers F ∧
          (((alp v r i * alp v r j) * D.p 1 (z (i, j)) - D.p 0 (TF j i)) * (g : Fv F v)⁻¹ +
            ((alp v r j * alp v r i) * D.p 0 (z (j, i)) - D.p 0 (TF j i)) * (g : Fv F v)⁻¹ -
            (D.p 0 (TF' j i) - D.p 0 (TF j i)) * (g : Fv F v)⁻¹) * (g : Fv F v)⁻¹ ∈
            v.adicCompletionIntegers F) := by
      intro i j
      rw [D.mem_iff, D.mem_iff]
      simp only [locZ, map_mul, map_sub, map_add, D.p_sc, (D.p_sig _).1, (D.p_sig _).2, hf, hf']
    constructor
    · intro hz k
      obtain ⟨i, j⟩ := k
      have ai := alp_ne_zero v r i
      have aj := alp_ne_zero v r j
      rw [hR]
      have h1 := (hL i j).1 (hz i j)
      refine ⟨?_, ?_⟩
      · convert h1.2.1 using 1
        rw [ht]
        field_simp
        ring
      · convert h1.1.2 using 1
        rw [ht]
        field_simp
        ring
    · intro hz i j
      have ai := alp_ne_zero v r i
      have aj := alp_ne_zero v r j
      rw [hL]
      have r1 := (hR i j).1 (hz (i, j))
      have r2 := (hR j i).1 (hz (j, i))
      have e1 : ((alp v r i * alp v r j) * D.p 1 (z (i, j)) - D.p 0 (TF j i)) * (g : Fv F v)⁻¹ =
          (g : Fv F v)⁻¹ * t (i, j) * (D.p 1 (z (i, j)) + -(D.p 0 (TF j i)) / t (i, j)) := by
        have := ht0 (i, j)
        rw [ht] at this ⊢
        field_simp
        ring
      have e2 : (((alp v r i * alp v r j) * D.p 0 (z (i, j)) - D.p 0 (TF i j)) * (g : Fv F v)⁻¹ +
            ((alp v r j * alp v r i) * D.p 1 (z (j, i)) - D.p 0 (TF i j)) * (g : Fv F v)⁻¹ -
            (D.p 0 (TF' i j) - D.p 0 (TF i j)) * (g : Fv F v)⁻¹) * (g : Fv F v)⁻¹ =
          ((g : Fv F v)⁻¹) ^ 2 * t (i, j) * (D.p 0 (z (i, j)) + D.p 1 (z (j, i)) +
            -(D.p 0 (TF i j) + D.p 0 (TF' i j)) / t (i, j)) := by
        have := ht0 (i, j)
        rw [ht] at this ⊢
        field_simp
        ring
      have e3 : (((alp v r i * alp v r j) * D.p 1 (z (i, j)) - D.p 0 (TF j i)) * (g : Fv F v)⁻¹ +
            ((alp v r j * alp v r i) * D.p 0 (z (j, i)) - D.p 0 (TF j i)) * (g : Fv F v)⁻¹ -
            (D.p 0 (TF' j i) - D.p 0 (TF j i)) * (g : Fv F v)⁻¹) * (g : Fv F v)⁻¹ =
          ((g : Fv F v)⁻¹) ^ 2 * t (j, i) * (D.p 0 (z (j, i)) + D.p 1 (z (i, j)) +
            -(D.p 0 (TF j i) + D.p 0 (TF' j i)) / t (j, i)) := by
        have := ht0 (j, i)
        rw [ht] at this ⊢
        field_simp
        ring
      have e4 : ((alp v r j * alp v r i) * D.p 1 (z (j, i)) - D.p 0 (TF i j)) * (g : Fv F v)⁻¹ =
          (g : Fv F v)⁻¹ * t (j, i) * (D.p 1 (z (j, i)) + -(D.p 0 (TF i j)) / t (j, i)) := by
        have := ht0 (j, i)
        rw [ht] at this ⊢
        field_simp
        ring
      have e5 : ((alp v r i * alp v r j) * D.p 0 (z (i, j)) - D.p 0 (TF i j)) * (g : Fv F v)⁻¹ =
          (g : Fv F v) * ((((alp v r i * alp v r j) * D.p 0 (z (i, j)) - D.p 0 (TF i j)) * (g : Fv F v)⁻¹ +
            ((alp v r j * alp v r i) * D.p 1 (z (j, i)) - D.p 0 (TF i j)) * (g : Fv F v)⁻¹ -
            (D.p 0 (TF' i j) - D.p 0 (TF i j)) * (g : Fv F v)⁻¹) * (g : Fv F v)⁻¹) -
          ((alp v r j * alp v r i) * D.p 1 (z (j, i)) - D.p 0 (TF i j)) * (g : Fv F v)⁻¹ +
          (D.p 0 (TF' i j) - D.p 0 (TF i j)) * (g : Fv F v)⁻¹ := by
        field_simp
        ring
      have c2 : (((alp v r i * alp v r j) * D.p 0 (z (i, j)) - D.p 0 (TF i j)) * (g : Fv F v)⁻¹ +
            ((alp v r j * alp v r i) * D.p 1 (z (j, i)) - D.p 0 (TF i j)) * (g : Fv F v)⁻¹ -
            (D.p 0 (TF' i j) - D.p 0 (TF i j)) * (g : Fv F v)⁻¹) * (g : Fv F v)⁻¹ ∈
            v.adicCompletionIntegers F := by rw [e2]; exact r1.1
      have c4 : ((alp v r j * alp v r i) * D.p 1 (z (j, i)) - D.p 0 (TF i j)) * (g : Fv F v)⁻¹ ∈
          v.adicCompletionIntegers F := by rw [e4]; exact r2.2
      refine ⟨⟨?_, by rw [e1]; exact r1.2⟩, c2, by rw [e3]; exact r2.1⟩
      rw [e5]
      exact add_mem (sub_mem (mul_mem hgO c2) c4) (hd i j)
  have hsh := haar_shear μ (D.shear Prod.swap) (Obox (E := E) v _) (obox_compact _) (obox_open _)
    (obox_nonempty _) (D.shear_box Prod.swap)
  have hu : ∀ k, IsUnit (y k) := fun k => by
    rw [hy]
    exact D.isUnit_pt (mul_ne_zero (pow_ne_zero _ (inv_ne_zero hg0)) (ht0 k)) (mul_ne_zero (inv_ne_zero hg0) (ht0 k))
  rw [hset, hsh, measure_preimage_add_right, BM.box_measure_mul (E := E) v _ μ y hu, hm]
  have hk : ∀ k : Fin (r + 1) × Fin (r + 1), (absV v (Algebra.norm (Fv F v) (y k)))⁻¹ =
      absV v (g : Fv F v) ^ 3 * ((absV v (alp v r k.1) * absV v (alp v r k.2)) ^ 2)⁻¹ := by
    intro k
    rw [hy, D.norm_pt, ht]
    simp only [absV_mul, absV_pow, absV_inv]
    have h1 := absV_pos v (alp_ne_zero v r k.1)
    have h2 := absV_pos v (alp_ne_zero v r k.2)
    have hG := absV_pos v hg0
    field_simp
  rw [Finset.prod_congr rfl (fun k _ => hk k), Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_prod, Fintype.card_fin, ← Fintype.prod_prod_type' (f := fun i j =>
      ((absV v (alp v r i) * absV v (alp v r j)) ^ 2)⁻¹), pow_mul]
  ring

end PI.UnitaryGroupMassFormula.LocJacTyp
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.DeepCongruenceVolume
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.LocJacTyp

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain PI.LocJacTyp
open scoped TensorProduct

attribute [local instance] PI.VolStabSW.secondCountable_Fv PI.VolStabSW.locallyCompact_Fv
attribute [local instance] Sd.finDim

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F))

def shearU (ι : Type) :
    ((ι → Fv F v ⊗[F] E) × (ι → Fv F v ⊗[F] E)) ≃ₜ+ ((ι → Fv F v ⊗[F] E) × (ι → Fv F v ⊗[F] E)) where
  toFun p := (p.1, p.1 - p.2)
  invFun p := (p.1, p.1 - p.2)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp
  map_add' x y := Prod.ext rfl (by
    show x.1 + y.1 - (x.2 + y.2) = (x.1 - x.2) + (y.1 - y.2)
    abel)
  continuous_toFun := continuous_fst.prodMk (continuous_fst.sub continuous_snd)
  continuous_invFun := continuous_fst.prodMk (continuous_fst.sub continuous_snd)

theorem unipotent_volume : VolU σ v := by
  intro g r m hS hg μ hμ hm
  haveI := hμ
  haveI : SigmaFinite μ := inferInstance
  haveI : (μ.prod μ).IsAddHaarMeasure := inferInstance
  obtain ⟨D⟩ := exists_SD hS
  have hfin : Module.finrank F E = 2 := hS.1
  have hg0 : (g : Fv F v) ≠ 0 := natCast_ne_zero v hg
  have hgO : (g : Fv F v) ∈ v.adicCompletionIntegers F := natCast_mem _ g
  set γ : UIdx r → Fv F v := fun q => (alp v r q.1.1)⁻¹ * alp v r q.1.2 with hγ
  have hγ0 : ∀ q, γ q ≠ 0 := fun q => mul_ne_zero (inv_ne_zero (alp_ne_zero v r _)) (alp_ne_zero v r _)
  have hγg0 : ∀ q, γ q * (g : Fv F v)⁻¹ ≠ 0 := fun q => mul_ne_zero (hγ0 q) (inv_ne_zero hg0)
  set A := Set.univ.pi fun q : UIdx r => {c | sc (E := E) v (γ q) * c ∈ OEv (E := E) v} with hA
  set B := Set.univ.pi fun q : UIdx r => {c | sc (E := E) v (γ q * (g : Fv F v)⁻¹) * c ∈ OEv (E := E) v}
    with hB
  have hset : deepCongruenceVolume (E := E) v g r = (shearU v (UIdx r)) ⁻¹' (A ×ˢ B) := by
    ext ⟨u, u'⟩
    simp only [deepCongruenceVolume, UO, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_prod, hA, hB, Set.mem_pi,
      Set.mem_univ, true_implies]
    show _ ↔ (∀ q, sc (E := E) v (γ q) * u q ∈ OEv (E := E) v) ∧
      ∀ q, sc (E := E) v (γ q * (g : Fv F v)⁻¹) * (u - u') q ∈ OEv (E := E) v
    simp only [Pi.sub_apply]
    constructor
    · rintro ⟨h1, _, h3⟩
      exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩
      refine ⟨h1, fun q => ?_, h3⟩
      have k1 := (D.mem_sc_mul _ _).1 (h1 q)
      have k3 := (D.mem_sc_mul _ _).1 (h3 q)
      rw [D.mem_sc_mul]
      simp only [map_sub] at k3
      constructor
      · have e1 : γ q * D.p 0 (u' q) = γ q * D.p 0 (u q) -
            (g : Fv F v) * (γ q * (g : Fv F v)⁻¹ * (D.p 0 (u q) - D.p 0 (u' q))) := by
          field_simp; ring
        rw [e1]; exact sub_mem k1.1 (mul_mem hgO k3.1)
      · have e1 : γ q * D.p 1 (u' q) = γ q * D.p 1 (u q) -
            (g : Fv F v) * (γ q * (g : Fv F v)⁻¹ * (D.p 1 (u q) - D.p 1 (u' q))) := by
          field_simp; ring
        rw [e1]; exact sub_mem k1.2 (mul_mem hgO k3.2)
  have hbox : (shearU v (UIdx r)) ⁻¹' (Obox (E := E) v (UIdx r) ×ˢ Obox (E := E) v (UIdx r)) =
      Obox (E := E) v (UIdx r) ×ˢ Obox (E := E) v (UIdx r) := by
    ext ⟨u, u'⟩
    simp only [Set.mem_preimage, Set.mem_prod]
    show (u ∈ Obox (E := E) v (UIdx r) ∧ u - u' ∈ Obox (E := E) v (UIdx r)) ↔ _
    simp only [Obox, Set.mem_pi, Set.mem_univ, true_implies, Pi.sub_apply]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun q => ?_⟩
      have := Sd.oev_add v (h1 q) (Sd.oev_neg v (h2 q))
      simpa using this
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun q => Sd.oev_add v (h1 q) (Sd.oev_neg v (h2 q))⟩
  have hsh := haar_shear (μ.prod μ) (shearU v (UIdx r))
    (Obox (E := E) v (UIdx r) ×ˢ Obox (E := E) v (UIdx r))
    ((obox_compact (UIdx r)).prod (obox_compact (UIdx r)))
    ((obox_open (UIdx r)).prod (obox_open (UIdx r)))
    ((obox_nonempty (UIdx r)).prod (obox_nonempty (UIdx r))) hbox (A ×ˢ B)
  have hK : m ^ Fintype.card (UIdx r) = ∏ _q : UIdx r, m := by rw [Finset.prod_const, Finset.card_univ]
  rw [hset, hsh, Measure.prod_prod, ENNReal.toReal_mul, hA, hB, boxScale v hfin μ γ hγ0,
    boxScale v hfin μ _ hγg0, hm, hK, ← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun q _ => ?_)
  simp only [hγ, absV_mul, absV_inv]
  have h1 := absV_pos v (alp_ne_zero v r q.1.1)
  have h2 := absV_pos v (alp_ne_zero v r q.1.2)
  have hG := absV_pos v hg0
  field_simp

end PI.UnitaryGroupMassFormula.LocJacTyp
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.DiagonalPhaseFirstVector
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.LocJacTyp.Sd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain Topology Filter PI.LocJacTyp
open PI.VolStabSW.SdUniqW
open scoped TensorProduct

attribute [local instance] PI.VolStabSW.secondCountable_Fv PI.VolStabSW.locallyCompact_Fv finDim

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) (ψ : AddChar (AF F) ℂ)

theorem continuous_tr : Continuous (Algebra.trace (Fv F v) (Fv F v ⊗[F] E)) :=
  PI.VolStabSW.SdUniqW.continuous_trace_tens (F := F) (E := E) (Fv F v)

theorem diagonal_phase_first_vector : (0 : Fv F v ⊗[F] E) ∈ D1 (E := E) v ψ := by
  intro x _; simp [psiV_zero]

theorem conductor_add_mem {y y' : Fv F v ⊗[F] E} (hy : y ∈ D1 (E := E) v ψ) (hy' : y' ∈ D1 (E := E) v ψ) :
    y + y' ∈ D1 (E := E) v ψ := by
  intro x hx
  rw [mul_add, map_add, psiV_add', hy x hx, hy' x hx, mul_one]

theorem conductor_neg_mem {y : Fv F v ⊗[F] E} (hy : y ∈ D1 (E := E) v ψ) : -y ∈ D1 (E := E) v ψ := by
  intro x hx
  have h := psiV_neg_mul v ψ (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (x * y))
  rw [hy x hx, mul_one] at h
  rwa [mul_neg, map_neg]

def D1sub : AddSubgroup (Fv F v ⊗[F] E) where
  carrier := D1 (E := E) v ψ
  add_mem' := conductor_add_mem v ψ
  zero_mem' := diagonal_phase_first_vector v ψ
  neg_mem' := conductor_neg_mem v ψ

theorem trE_mem_Aset {y : Fv F v ⊗[F] E} (hy : y ∈ D1 (E := E) v ψ) (j : Fin (Module.finrank F E)) :
    trE (E := E) v y j ∈ PI.OmFibreUniq.W.SdChar.Aset v (psiV F ψ v) := by
  intro c hc
  have e : c * trE (E := E) v y j =
      Algebra.trace (Fv F v) (Fv F v ⊗[F] E) ((c • bas (E := E) v j) * y) := by
    rw [trE_apply, trC_apply, smul_mul_assoc, map_smul, smul_eq_mul]
  rw [e]
  exact hy _ (smul_bas_mem v hc j)

variable (hK : OpenKer v ψ)
include hK

theorem conductor_isClosed : IsClosed (D1 (E := E) v ψ) := by
  have e : D1 (E := E) v ψ = ⋂ x ∈ OEv (E := E) v,
      {y | psiV F ψ v (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (x * y)) = 1} := by
    ext y; simp [D1]
  rw [e]
  exact isClosed_biInter fun x _ => isClosed_eq ((continuous_psiV_of v ψ hK).comp
    ((continuous_tr v).comp (continuous_const.mul continuous_id))) continuous_const

theorem conductor_isCompact (hnt : ∃ r, psiV F ψ v r ≠ 1) : IsCompact (D1 (E := E) v ψ) := by
  obtain ⟨y0, -, hy0⟩ := PI.OmFibreUniq.W.SdChar.Aset_bdd v (psiV F ψ v) (psiV_add' v ψ)
    (norm_psiV_of v ψ hK) hnt
  set C : Set (Fin (Module.finrank F E) → Fv F v) :=
    Set.univ.pi fun _ => (fun s => y0 * s) '' (v.adicCompletionIntegers F : Set (Fv F v))
  have hC : IsCompact C := isCompact_univ_pi fun _ =>
    (PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F v).image (continuous_const.mul continuous_id)
  refine (hC.image (continuous_trE_symm (E := E) v)).of_isClosed_subset (conductor_isClosed v ψ hK) ?_
  intro y hy
  refine ⟨trE (E := E) v y, fun j _ => ?_, by simp⟩
  obtain ⟨s, hs, e⟩ := hy0 _ (trE_mem_Aset v ψ hy j)
  exact ⟨s, hs, e.symm⟩

theorem conductor_mem_nhds : D1 (E := E) v ψ ∈ 𝓝 (0 : Fv F v ⊗[F] E) := by
  obtain ⟨m, w, hw, hgen⟩ := exists_gens (E := E) v
  have hA := PI.OmFibreUniq.W.SdChar.Aset_mem_nhds v (psiV F ψ v) (continuous_psiV_of v ψ hK)
    (psiV_add' v ψ) (norm_psiV_of v ψ hK)
  have hN : (⋂ k, {y : Fv F v ⊗[F] E | Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (w k * y) ∈
      PI.OmFibreUniq.W.SdChar.Aset v (psiV F ψ v)}) ∈ 𝓝 (0 : Fv F v ⊗[F] E) := by
    refine Filter.iInter_mem.2 fun k => ?_
    have hc : Continuous fun y : Fv F v ⊗[F] E => Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (w k * y) :=
      (continuous_tr v).comp (continuous_const.mul continuous_id)
    exact hc.continuousAt.preimage_mem_nhds (by simpa using hA)
  refine Filter.mem_of_superset hN fun y hy x hx => ?_
  simp only [Set.mem_iInter, Set.mem_setOf_eq] at hy
  obtain ⟨c, hc, rfl⟩ := hgen x hx
  rw [Finset.sum_mul, map_sum, psiV_sum]
  refine Finset.prod_eq_one fun k _ => ?_
  rw [smul_mul_assoc, map_smul, smul_eq_mul]
  exact hy k (c k) (hc k)

theorem conductor_isOpen : IsOpen (D1 (E := E) v ψ) :=
  AddSubgroup.isOpen_of_mem_nhds (D1sub (E := E) v ψ) (conductor_mem_nhds v ψ hK)

end PI.UnitaryGroupMassFormula.LocJacTyp.Sd
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.ParabolicVolume
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.LocJacTyp

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain PI.LocJacTyp
open scoped TensorProduct

attribute [local instance] PI.VolStabSW.secondCountable_Fv PI.VolStabSW.locallyCompact_Fv
attribute [local instance] Sd.finDim

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F))

theorem unit_forall {P : Unit → Prop} : (∀ i, P i) ↔ P () := ⟨fun h => h (), fun h _ => h⟩

theorem parabolic_volume : VolPP σ v := by
  intro g r T T' m hS hg hT μ hμ hm l
  obtain ⟨D⟩ := exists_SD hS
  have hp0 : ∀ s t, D.p 0 (D.pt s t) = s := fun s t => (D.p_pt s t).1
  have hp1 : ∀ s t, D.p 1 (D.pt s t) = t := fun s t => (D.p_pt s t).2
  have hg0 : (g : Fv F v) ≠ 0 := natCast_ne_zero v hg
  have hgO : (g : Fv F v) ∈ v.adicCompletionIntegers F := natCast_mem _ g
  have hsh : ∀ X : Set (Unit → Fv F v ⊗[F] E), μ ((D.shear id) ⁻¹' X) = μ X :=
    haar_shear μ (D.shear id) (Obox (E := E) v Unit) (obox_compact Unit) (obox_open Unit)
      (obox_nonempty Unit) (D.shear_box id)
  by_cases hl : (l : ℕ) < r
  · have ha : alp v r l ^ 2 ≠ 0 := pow_ne_zero _ (alp_ne_zero v r l)
    have hset : (fun c : Unit → Fv F v ⊗[F] E => c ()) ⁻¹' PPTyp σ v g r T T' l =
        (D.shear id) ⁻¹' (Set.univ.pi fun _ : Unit =>
          {c | D.pt (alp v r l ^ 2 * ((g : Fv F v)⁻¹) ^ 2) (alp v r l ^ 2 * (g : Fv F v)⁻¹) * c ∈
            OEv (E := E) v}) := by
      ext c
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_ofPred_eq, PPTyp,
        if_pos hl, unit_forall]
      rw [D.mem_sc_mul, D.mem_sc_mul, D.mem_pt_mul, D.shear_first_coordinate, D.shear_second_coordinate]
      simp only [map_add, (D.p_sig _).1, (D.p_sig _).2, id]
      constructor
      · rintro ⟨⟨_, h2⟩, h3, _⟩
        exact ⟨h3, h2⟩
      · rintro ⟨h3, h2⟩
        refine ⟨⟨?_, h2⟩, h3, ?_⟩
        · have e1 : alp v r l ^ 2 * (g : Fv F v)⁻¹ * D.p 0 (c ()) =
              (g : Fv F v) * (alp v r l ^ 2 * ((g : Fv F v)⁻¹) ^ 2 * (D.p 0 (c ()) + D.p 1 (c ()))) -
                alp v r l ^ 2 * (g : Fv F v)⁻¹ * D.p 1 (c ()) := by
            field_simp <;> ring
          rw [e1]
          exact sub_mem (mul_mem hgO h3) h2
        · rwa [add_comm (D.p 1 (c ()))]
    have hu : ∀ _ : Unit, IsUnit (D.pt (alp v r l ^ 2 * ((g : Fv F v)⁻¹) ^ 2) (alp v r l ^ 2 * (g : Fv F v)⁻¹)) :=
      fun _ => D.isUnit_pt (mul_ne_zero ha (pow_ne_zero _ (inv_ne_zero hg0))) (mul_ne_zero ha (inv_ne_zero hg0))
    rw [hset, hsh, BM.box_measure_mul (E := E) v Unit μ _ hu, hm]
    simp only [Finset.univ_unique, Finset.prod_singleton, D.norm_pt]
    rw [absV_mul, absV_mul, absV_mul, absV_pow, absV_pow, absV_inv]
    have hA := absV_pos v (alp_ne_zero v r l)
    have hG := absV_pos v hg0
    field_simp
  · have hlr : alp v r l = 1 := by unfold alp; rw [if_neg hl]
    obtain ⟨k, hk⟩ := hT
    have hk' : ((T : Fv F v) - (T' : Fv F v)) = (g : Fv F v) * (k : Fv F v) := by
      have := congrArg (Int.cast : ℤ → Fv F v) hk
      push_cast at this
      exact this
    have hset : (fun c : Unit → Fv F v ⊗[F] E => c ()) ⁻¹' PPTyp σ v g r T T' l =
        (D.shear id) ⁻¹' ((fun w => w + fun _ : Unit => D.pt ((T : Fv F v) + T') (T : Fv F v)) ⁻¹'
          (Set.univ.pi fun _ : Unit =>
            {c | D.pt (((g : Fv F v)⁻¹) ^ 2) (g : Fv F v)⁻¹ * c ∈ OEv (E := E) v})) := by
      ext c
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_ofPred_eq, PPTyp,
        if_neg hl, unit_forall, Pi.add_apply]
      rw [D.mem_sc_mul, D.mem_sc_mul, D.mem_pt_mul]
      simp only [map_add, D.shear_first_coordinate, D.shear_second_coordinate, hp0, hp1, map_natCast, (D.p_sig _).1, (D.p_sig _).2, id]
      constructor
      · rintro ⟨⟨_, h2⟩, h3, _⟩
        refine ⟨?_, h2⟩
        have e1 : ((g : Fv F v)⁻¹) ^ 2 * (D.p 0 (c ()) + D.p 1 (c ()) + ((T : Fv F v) + T')) =
            ((g : Fv F v)⁻¹) ^ 2 * (D.p 0 (c ()) + D.p 1 (c ()) + T + T') := by ring
        rw [e1]; exact h3
      · rintro ⟨h3, h2⟩
        have e0 : ((g : Fv F v)⁻¹) ^ 2 * (D.p 0 (c ()) + D.p 1 (c ()) + T + T') =
            ((g : Fv F v)⁻¹) ^ 2 * (D.p 0 (c ()) + D.p 1 (c ()) + ((T : Fv F v) + T')) := by ring
        refine ⟨⟨?_, h2⟩, by rw [e0]; exact h3, ?_⟩
        · have e1 : (g : Fv F v)⁻¹ * (D.p 0 (c ()) + T) =
              (g : Fv F v) * (((g : Fv F v)⁻¹) ^ 2 * (D.p 0 (c ()) + D.p 1 (c ()) + ((T : Fv F v) + T'))) -
                (g : Fv F v)⁻¹ * (D.p 1 (c ()) + T) + (g : Fv F v)⁻¹ * ((T : Fv F v) - T') := by
            field_simp <;> ring
          have e2 : (g : Fv F v)⁻¹ * ((T : Fv F v) - T') = (k : Fv F v) := by
            rw [hk']; field_simp
          rw [e1, e2]
          exact add_mem (sub_mem (mul_mem hgO h3) h2) (intCast_mem _ k)
        · have e2 : ((g : Fv F v)⁻¹) ^ 2 * (D.p 1 (c ()) + D.p 0 (c ()) + T + T') =
              ((g : Fv F v)⁻¹) ^ 2 * (D.p 0 (c ()) + D.p 1 (c ()) + ((T : Fv F v) + T')) := by ring
          rw [e2]; exact h3
    have hu : ∀ _ : Unit, IsUnit (D.pt (((g : Fv F v)⁻¹) ^ 2) (g : Fv F v)⁻¹) :=
      fun _ => D.isUnit_pt (pow_ne_zero _ (inv_ne_zero hg0)) (inv_ne_zero hg0)
    rw [hset, hsh, measure_preimage_add_right, BM.box_measure_mul (E := E) v Unit μ _ hu, hm]
    simp only [Finset.univ_unique, Finset.prod_singleton, D.norm_pt, hlr, absV_one]
    rw [absV_mul, absV_pow, absV_inv]
    have hG := absV_pos v hg0
    field_simp

end PI.UnitaryGroupMassFormula.LocJacTyp
end
end

