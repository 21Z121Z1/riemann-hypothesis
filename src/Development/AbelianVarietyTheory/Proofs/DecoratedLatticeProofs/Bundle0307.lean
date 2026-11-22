import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0287
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0147
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0289
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawCombinationsOperatorDatum
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LastOpPf

open GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule (ofAdj starAdj)

variable {D : D7}

theorem cA_mem_idAt {P : Pl D → Prop} {a : AE D} (h : a ∈ idAt D P) : cA D a ∈ idAt D P := by
  obtain ⟨ε, -, hc, -, hε, -⟩ := (localComponents D P).1
  rw [hε] at h ⊢
  conv_rhs => rw [← h]
  rw [map_mul, hc]

theorem mxAt_adj {P : Pl D → Prop} {m n : ℕ} {x : Mx D m n} (hx : MxAt P x) : MxAt P (adj x) := fun i j => by
  have := cA_mem_idAt (hx j i)
  simpa [adj] using this

theorem mxAt_mul_l {P : Pl D → Prop} {l m n : ℕ} (A : Mx D l m) {x : Mx D m n} (hx : MxAt P x) : MxAt P (A * x) :=
  fun i j => by
    rw [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (hx k j)

theorem mxAt_mul_r {P : Pl D → Prop} {l m n : ℕ} {x : Mx D l m} (hx : MxAt P x) (A : Mx D m n) : MxAt P (x * A) :=
  fun i j => by
    rw [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (hx i k)

theorem mxAt_smul {P : Pl D → Prop} {m n : ℕ} (c : AE D) {x : Mx D m n} (hx : MxAt P x) : MxAt P (c • x) :=
  fun i j => Ideal.mul_mem_left _ _ (hx i j)

theorem mxAt_add {P : Pl D → Prop} {m n : ℕ} {x y : Mx D m n} (hx : MxAt P x) (hy : MxAt P y) : MxAt P (x + y) :=
  fun i j => add_mem (hx i j) (hy i j)

theorem mxAt_zero {P : Pl D → Prop} {m n : ℕ} : MxAt P (0 : Mx D m n) := fun _ _ => zero_mem _

theorem combAt_single {P : Pl D → Prop} {S T : HSp D} {z : WO S T} (hz : MxAt P z) (c : ℂ) :
    CombAt P (Finsupp.single z c) := fun u hu => by
  rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hu)]; exact hz

theorem comb_apply (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c : WO S T →₀ ℂ) (f : WO S T → ℂ) (w : WO S T) :
    comb ψ S T c f w = ∑ z ∈ c.support, c z * heisO ψ S T z f w := by
  simp [comb, Finset.sum_apply, smul_eq_mul]

theorem comb_single (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (z : WO S T) (c : ℂ) (f : WO S T → ℂ) :
    comb ψ S T (Finsupp.single z c) f = c • heisO ψ S T z f := by
  by_cases hc : c = 0
  · subst hc; simp [comb]
  · simp [comb, Finsupp.support_single_ne_zero _ hc]

theorem symplOH_zero_right (S T : HSp D) (w : WO S T) : symplOH S T w 0 = 0 := by
  simp [symplOH, symplO, hO]

theorem ofAdj_starAdj (S T : HSp D) (x : WO S T) : ofAdj S T (starAdj S T x) = x := by
  have h : incA D (-D.host.xi0⁻¹) * cA D (incA D D.host.xi0) = 1 := by
    rw [GlobalTheory.DualPairCheck.cA_incA, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, ← map_mul]
    rw [show -D.host.xi0⁻¹ * -D.host.xi0 = 1 by rw [neg_mul_neg]; exact inv_mul_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)]
    exact map_one _
  rw [ofAdj, starAdj, adj_smul, adj_mul, adj_mul, adj_adj, adj_gA, adj_giA, Matrix.smul_mul, Matrix.mul_smul, smul_smul, h,
    one_smul, Matrix.mul_assoc, Matrix.mul_assoc, giA_gA_cancel, giA_mul_gA, Matrix.mul_one]

end GlobalTheory.LastOpPf

namespace GlobalTheory.LastOpPf

open GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule (ofAdj starAdj)

variable {D : D7}

def invLine {m n : ℕ} (τ : Matrix (Fin m) (Fin n) D.host.E) : Matrix (Fin n) (Fin m) D.host.E := fun i j => (τ j i)⁻¹

theorem mul_invLine {L L'' : HSp D} (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (hL : L.rank = 1) (hL'' : L''.rank = 1)
    (hτ : τᴴ * (L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram) : τ * invLine τ = 1 := by
  have hsub : ∀ a b : Fin L.rank, a = b := fun a b => Fin.ext (by have := a.2; have := b.2; omega)
  have hsub'' : ∀ a b : Fin L''.rank, a = b := fun a b => Fin.ext (by have := a.2; have := b.2; omega)
  let k0 : Fin L''.rank := ⟨0, by omega⟩
  have hne : ∀ i, τ i k0 ≠ 0 := by
    intro i hi
    have h0 : τ = 0 := by
      funext a b
      rw [hsub a i, hsub'' b k0]; exact hi
    rw [h0, Matrix.mul_zero, Matrix.mul_zero] at hτ
    have hc : (-(D.host.xi0 * star D.host.xi0)) ≠ 0 := by
      have := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
      simpa using this
    have hg : L''.gram = 0 := by
      have := hτ.symm
      rwa [smul_eq_zero, or_iff_right hc] at this
    haveI : Nonempty (Fin L''.rank) := ⟨k0⟩
    exact Formalism.L2.Theta.gram_det_ne L'' (by rw [hg, Matrix.det_zero])
  funext i j
  rw [hsub j i, Matrix.one_apply_eq, Matrix.mul_apply, Finset.sum_eq_single k0 (fun b _ hb => absurd (hsub'' b k0) hb)
    (fun h => absurd (Finset.mem_univ _) h)]
  show τ i k0 * (τ i k0)⁻¹ = 1
  exact mul_inv_cancel₀ (hne i)

def kapInv {L L'' : HSp D} (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (S : HSp D) (b : WO L S) : WO S L'' :=
  (rat (invLine τ) : Mx D L''.rank L.rank) * starAdj L S b

theorem kap_kapInv {L L'' : HSp D} (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (hL : L.rank = 1) (hL'' : L''.rank = 1)
    (hτ : τᴴ * (L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram) (S : HSp D) (b : WO L S) :
    kap τ S (kapInv τ S b) = b := by
  rw [kap, kapInv, ← Matrix.mul_assoc, ← rat_mul, mul_invLine τ hL hL'' hτ, rat_one, Matrix.one_mul, ofAdj_starAdj]

theorem mxAt_kapInv {P : Pl D → Prop} {L L'' : HSp D} (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (S : HSp D)
    {b : WO L S} (hb : MxAt P b) : MxAt P (kapInv τ S b) :=
  mxAt_mul_l _ (mxAt_smul _ (mxAt_mul_l _ (mxAt_mul_r (mxAt_adj hb) _)))

theorem mxAt_kap {P : Pl D → Prop} {L L'' : HSp D} (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (S : HSp D)
    {w : WO S L''} (hw : MxAt P w) : MxAt P (kap τ S w) :=
  mxAt_smul _ (mxAt_mul_l _ (mxAt_mul_r (mxAt_adj (mxAt_mul_l _ hw)) _))

theorem kap_add {L L'' : HSp D} (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (S : HSp D) (w w' : WO S L'') :
    kap τ S (w + w') = kap τ S w + kap τ S w' := by
  rw [kap, kap, kap, ← GlobalTheory.LinkKappa.ofAdj_add, Matrix.mul_add]

theorem symplOH_kap {L L'' : HSp D} (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E)
    (hτ : τᴴ * (L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram) (S : HSp D) (w w' : WO S L'') :
    symplOH L S (kap τ S w) (kap τ S w') = symplOH S L'' w w' := by
  have hτ' : τᴴ * (L.gram * τ) = (((-1 : ℤ) : D.host.E) * (D.host.xi0 * star D.host.xi0)) • L''.gram := by
    rw [hτ]; congr 1; push_cast; ring
  have h := GlobalTheory.LinkKappa.symplO_ofAdj L L'' S τ (-1) hτ' w w'
  unfold symplOH
  rw [kap, kap, h]
  push_cast; ring

end GlobalTheory.LastOpPf

namespace GlobalTheory.LastOpPf

variable {D : D7}

theorem lastBi_apply {V₀ A L S X T L'' : HSp D} (o : OrthDec V₀ A L) (o'' : OrthDec X T L'')
    (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (Ξ : WO V₀ S → ℂ) (Φ₂ : WO S T → ℂ) (u : WO A S) (v : WO S X) :
    lastBi o o'' τ Ξ Φ₂ u v = Φ₂ (o''.resT S v).1 * Ξ ((o.resS S).symm (u, kap τ S (o''.resT S v).2)) := rfl

theorem heisO_split {V₀ A L S L'' : HSp D} (o : OrthDec V₀ A L) (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E)
    (hτ : τᴴ * (L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram) (ψ : AddChar (AF D.host.F) ℂ)
    (Ξ : WO V₀ S → ℂ) (x u : WO A S) (y w : WO S L'') :
    heisO ψ V₀ S ((o.resS S).symm (x, kap τ S y)) Ξ ((o.resS S).symm (u, kap τ S w)) =
      ψ (symplOH A S u x) * ψ (symplOH S L'' w y) * Ξ ((o.resS S).symm (u + x, kap τ S (w + y))) := by
  simp only [heisO]
  rw [o.symplOH_resS, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, ← map_add, Prod.mk_add_mk, kap_add,
    symplOH_kap τ hτ, AddChar.map_add_eq_mul]

end GlobalTheory.LastOpPf

namespace GlobalTheory.LastOpPf

variable {D : D7}

theorem biComb_lastBi {V₀ A L S X T L'' : HSp D} (o : OrthDec V₀ A L) (o'' : OrthDec X T L'')
    (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E)
    (hτ : τᴴ * (L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram) (ψ : AddChar (AF D.host.F) ℂ)
    (d : WO A S →₀ ℂ) (d' : WO S X →₀ ℂ) (Ξ : WO V₀ S → ℂ) (Φ₂ : WO S T → ℂ) :
    biComb ψ A S X d d' (lastBi o o'' τ Ξ Φ₂) = ∑ p ∈ d.support ×ˢ d'.support,
      lastBi o o'' τ (comb ψ V₀ S (Finsupp.single ((o.resS S).symm (p.1, kap τ S (o''.resT S p.2).2)) (d p.1 * d' p.2)) Ξ)
        (comb ψ S T (Finsupp.single (o''.resT S p.2).1 1) Φ₂) := by
  funext u v
  simp only [Finset.sum_apply, lastBi_apply, comb_single, Pi.smul_apply, smul_eq_mul, one_mul, heisO_split o τ hτ]
  simp only [biComb, comb_apply]
  simp only [heisO, lastBi_apply, map_add, Prod.fst_add, Prod.snd_add, o''.symplOH_resT, AddChar.map_add_eq_mul]
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  ring

end GlobalTheory.LastOpPf

namespace GlobalTheory.LastOpPf

variable {D : D7}

theorem lastBi_comb {V₀ A L S X T L'' : HSp D} (o : OrthDec V₀ A L) (o'' : OrthDec X T L'')
    (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (hL : L.rank = 1) (hL'' : L''.rank = 1)
    (hτ : τᴴ * (L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram) (ψ : AddChar (AF D.host.F) ℂ)
    (e : WO V₀ S →₀ ℂ) (Ξ : WO V₀ S → ℂ) (Φ₂ : WO S T → ℂ) :
    lastBi o o'' τ (comb ψ V₀ S e Ξ) Φ₂ = ∑ z ∈ e.support, biComb ψ A S X (Finsupp.single (o.resS S z).1 (e z))
      (Finsupp.single ((o''.resT S).symm (0, kapInv τ S (o.resS S z).2)) 1) (lastBi o o'' τ Ξ Φ₂) := by
  funext u v
  simp only [Finset.sum_apply]
  rw [lastBi_apply, comb_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  have hz : (o.resS S).symm ((o.resS S z).1, kap τ S (kapInv τ S (o.resS S z).2)) = z := by
    rw [kap_kapInv τ hL hL'' hτ, Prod.mk.eta, AddEquiv.symm_apply_apply]
  have hK := heisO_split o τ hτ ψ Ξ (o.resS S z).1 u (kapInv τ S (o.resS S z).2) (o''.resT S v).2
  rw [hz] at hK
  rw [hK]
  simp only [biComb, comb_single, Pi.smul_apply, smul_eq_mul, one_mul, heisO, lastBi_apply, map_add,
    AddEquiv.apply_symm_apply, Prod.fst_add, Prod.snd_add, add_zero, o''.symplOH_resT, symplOH_zero_right,
    AddChar.map_add_eq_mul, AddChar.map_zero_eq_one]
  ring

end GlobalTheory.LastOpPf

namespace GlobalTheory.LastOpPf

variable {D : D7}

theorem sum_equivFin {α M : Type} [AddCommMonoid M] (s : Finset α) (f : α → M) :
    ∑ p ∈ s, f p = ∑ i : Fin s.card, f (s.equivFin.symm i : α) :=
  (Finset.sum_coe_sort s f).symm.trans (Equiv.sum_comp s.equivFin.symm (fun p : s => f p)).symm

theorem lastOp : ∀ D : D7, GlobalTheory.FinPl.LastOp D := by
  intro D ψ V₀ A L S X T L'' o o'' τ hL hL'' hτ P
  refine ⟨fun e he => ?_, fun d d' hd hd' => ?_⟩
  · refine ⟨⟨e.support.card, fun i => Finsupp.single (o.resS S (e.support.equivFin.symm i : WO V₀ S)).1
        (e (e.support.equivFin.symm i : WO V₀ S)), fun i => Finsupp.single ((o''.resT S).symm
        (0, kapInv τ S (o.resS S (e.support.equivFin.symm i : WO V₀ S)).2)) 1⟩, fun i => ⟨?_, ?_⟩, fun Ξ Φ₂ => ?_⟩
    · exact combAt_single (mxAt_mul_r (he _ (e.support.equivFin.symm i).2) _) _
    · refine combAt_single ?_ 1
      rw [OrthDec.resT_symm_apply]
      exact mxAt_add (mxAt_mul_l _ mxAt_zero) (mxAt_mul_l _ (mxAt_kapInv τ S (mxAt_mul_r (he _ (e.support.equivFin.symm i).2) _)))
    · rw [lastBi_comb o o'' τ hL hL'' hτ ψ e Ξ Φ₂, sum_equivFin]
      rfl
  · refine ⟨(d.support ×ˢ d'.support).card,
      fun i => Finsupp.single ((o.resS S).symm (((d.support ×ˢ d'.support).equivFin.symm i : WO A S × WO S X).1,
        kap τ S (o''.resT S ((d.support ×ˢ d'.support).equivFin.symm i : WO A S × WO S X).2).2))
        (d ((d.support ×ˢ d'.support).equivFin.symm i : WO A S × WO S X).1 *
          d' ((d.support ×ˢ d'.support).equivFin.symm i : WO A S × WO S X).2),
      fun i => Finsupp.single (o''.resT S ((d.support ×ˢ d'.support).equivFin.symm i : WO A S × WO S X).2).1 1,
      fun i => ⟨?_, ?_⟩, fun Ξ Φ₂ => ?_⟩
    · have hp := Finset.mem_product.1 ((d.support ×ˢ d'.support).equivFin.symm i).2
      refine combAt_single ?_ _
      rw [OrthDec.resS_symm_apply]
      exact mxAt_add (mxAt_mul_r (hd _ hp.1) _) (mxAt_mul_r (mxAt_kap τ S (mxAt_mul_l _ (hd' _ hp.2))) _)
    · have hp := Finset.mem_product.1 ((d.support ×ˢ d'.support).equivFin.symm i).2
      exact combAt_single (mxAt_mul_l _ (hd' _ hp.2)) _
    · rw [biComb_lastBi o o'' τ hτ ψ d d' Ξ Φ₂, sum_equivFin]

end GlobalTheory.LastOpPf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawDatumOfVacuaIsVacuumBoth
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LastVacPf

variable {D : D7}

theorem lastBi_apply {V₀ A L S X T L'' : HSp D} (o : OrthDec V₀ A L) (o'' : OrthDec X T L'')
    (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (Ξ : WO V₀ S → ℂ) (Φ₂ : WO S T → ℂ) (u : WO A S) (v : WO S X) :
    lastBi o o'' τ Ξ Φ₂ u v = Φ₂ (o''.resT S v).1 * Ξ ((o.resS S).symm (u, kap τ S (o''.resT S v).2)) := rfl

theorem heis_left (ψ : AddChar (AF D.host.F) ℂ) {V₀ A L S X T L'' : HSp D} (o : OrthDec V₀ A L) (o'' : OrthDec X T L'')
    (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (Ξ : WO V₀ S → ℂ) (Φ₂ : WO S T → ℂ) (a : WO A S) (v : WO S X) :
    heisO ψ A S a (fun u => lastBi o o'' τ Ξ Φ₂ u v) = fun u =>
      Φ₂ (o''.resT S v).1 * heisO ψ V₀ S ((o.resS S).symm (a, 0)) Ξ ((o.resS S).symm (u, kap τ S (o''.resT S v).2)) := by
  funext u
  simp only [heisO, lastBi_apply]
  have e : (o.resS S).symm (u + a, kap τ S (o''.resT S v).2) =
      (o.resS S).symm (u, kap τ S (o''.resT S v).2) + (o.resS S).symm (a, 0) := by
    rw [← map_add, Prod.mk_add_mk, add_zero]
  rw [e, GlobalTheory.LastBiTheta.sOH_resS_symm, GlobalTheory.LastBiTheta.sOH_zero_right, add_zero]
  ring

theorem heis_right (ψ : AddChar (AF D.host.F) ℂ) {V₀ A L S X T L'' : HSp D} (o : OrthDec V₀ A L) (o'' : OrthDec X T L'')
    (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E)
    (hτ : τᴴ * (L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram)
    (Ξ : WO V₀ S → ℂ) (Φ₂ : WO S T → ℂ) (b : WO S X) (u : WO A S) :
    heisO ψ S X b (lastBi o o'' τ Ξ Φ₂ u) = o''.boxT S (heisO ψ S T (o''.resT S b).1 Φ₂) (fun w =>
      heisO ψ V₀ S ((o.resS S).symm (0, kap τ S (o''.resT S b).2)) Ξ ((o.resS S).symm (u, kap τ S w))) := by
  obtain ⟨kadd, -, -, -, ksympl, -⟩ := GlobalTheory.LinkKappa.kappa_props D L L'' S τ (-1)
    (by rw [Int.cast_neg, Int.cast_one, neg_one_mul]; exact hτ) (kap τ S) (fun _ => rfl)
  have kH : ∀ w w', symplOH L S (kap τ S w) (kap τ S w') = symplOH S L'' w w' := fun w w' => by
    unfold symplOH
    rw [ksympl]
    simp only [Int.cast_neg, Int.cast_one, neg_one_mul, neg_neg]
  show heisO ψ S X b (o''.boxT S Φ₂ fun w => Ξ ((o.resS S).symm (u, kap τ S w))) = _
  rw [o''.heisO_boxT]
  congr 1
  funext w
  simp only [heisO]
  have e : (o.resS S).symm (u, kap τ S (w + (o''.resT S b).2)) =
      (o.resS S).symm (u, kap τ S w) + (o.resS S).symm (0, kap τ S (o''.resT S b).2) := by
    rw [kadd, ← map_add, Prod.mk_add_mk, add_zero]
  rw [e, GlobalTheory.LastBiTheta.sOH_resS_symm, GlobalTheory.LastBiTheta.sOH_zero_right, zero_add, kH]

theorem slice_left {ψ : AddChar (AF D.host.F) ℂ} {A S A' : HSp D} {C : WO A S → WO S A' → ℂ} (h : IsBiTheta ψ A S A' C)
    (v : WO S A') : IsThetaFunO ψ A S fun u => C u v where
  quasi := fun γ u => h.quasiL γ u v
  level := by
    obtain ⟨U, hU, hl⟩ := h.levL
    exact ⟨U, hU, fun a ha h0 => hl a ha h0 v⟩
  cont := h.cont.comp (continuous_id.prodMk continuous_const)
  smooth := fun n L hL h0 u => by
    have := h.smooth n L 0 hL continuous_const h0 (fun _ => Matrix.map_zero _ (map_zero (finPart D))) u v
    simpa using this

theorem slice_right {ψ : AddChar (AF D.host.F) ℂ} {A S A' : HSp D} {C : WO A S → WO S A' → ℂ} (h : IsBiTheta ψ A S A' C)
    (u : WO A S) : IsThetaFunO ψ S A' (C u) where
  quasi := fun γ v => h.quasiR γ u v
  level := by
    obtain ⟨U, hU, hl⟩ := h.levR
    exact ⟨U, hU, fun a ha h0 => hl a ha h0 u⟩
  cont := h.cont.comp (continuous_const.prodMk continuous_id)
  smooth := fun n L hL h0 v => by
    have := h.smooth n 0 L continuous_const hL (fun _ => Matrix.map_zero _ (map_zero (finPart D))) h0 u v
    simpa using this

theorem isHalf_mul_left {e : AE D} {k m n : ℕ} (P : Mx D k m) {y : Mx D m n} (h : IsHalf e y) : IsHalf e (P * y) := by
  intro i j
  simp only [Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [mul_left_comm, h l j]

theorem isHalf_mul_right {e : AE D} {k m n : ℕ} {y : Mx D k m} (P : Mx D m n) (h : IsHalf e y) : IsHalf e (y * P) := by
  intro i j
  simp only [Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [← mul_assoc, h i l]

theorem isHalf_add {e : AE D} {m n : ℕ} {y z : Mx D m n} (hy : IsHalf e y) (hz : IsHalf e z) : IsHalf e (y + z) := by
  intro i j
  rw [Matrix.add_apply, mul_add, hy i j, hz i j]

theorem isHalf_zero (e : AE D) (m n : ℕ) : IsHalf e (0 : Mx D m n) := fun i j => by
  rw [Matrix.zero_apply, mul_zero]

theorem isHalf_smul {e : AE D} {m n : ℕ} (c : AE D) {y : Mx D m n} (h : IsHalf e y) : IsHalf e (c • y) := by
  intro i j
  rw [Matrix.smul_apply, smul_eq_mul, mul_left_comm, h i j]

theorem isHalf_adj {e : AE D} {m n : ℕ} {y : Mx D m n} (h : IsHalf e y) : IsHalf (cA D e) (adj y) := by
  intro i j
  simp only [adj, Matrix.transpose_apply, Matrix.map_apply]
  rw [← map_mul, h j i]

theorem isHalf_kap {e : AE D} {L L'' : HSp D} (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (S : HSp D) {w : WO S L''}
    (h : IsHalf e w) : IsHalf (cA D e) (kap τ S w) := by
  unfold kap GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj
  exact isHalf_smul _ (isHalf_mul_left _ (isHalf_mul_right _ (isHalf_adj (isHalf_mul_left _ h))))

theorem cA_cA (x : AE D) : cA D (cA D x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a e =>
    simp only [cA, sigR]
    simp
    congr 1
    exact star_star e

theorem isSplitIdem_cA {e : AE D} (he : IsSplitIdem D e) : IsSplitIdem D (cA D e) := by
  obtain ⟨h1, h2, v, ε, hε, h3⟩ := he
  refine ⟨by rw [← map_mul, h1], ?_, v, ε, hε, ?_⟩
  · rw [cA_cA, mul_comm, h2]
  · rw [cA_cA, add_comm, h3]

theorem isHalf_resS_symm {e : AE D} {V₀ A L : HSp D} (o : OrthDec V₀ A L) (S : HSp D) {a : WO A S} {b : WO L S}
    (ha : IsHalf e a) (hb : IsHalf e b) : IsHalf e ((o.resS S).symm (a, b)) := by
  rw [OrthDec.resS_symm_apply]
  exact isHalf_add (isHalf_mul_right _ ha) (isHalf_mul_right _ hb)

theorem isHalf_resT {e : AE D} {X T L'' : HSp D} (o'' : OrthDec X T L'') (S : HSp D) {w : WO S X} (h : IsHalf e w) :
    IsHalf e (o''.resT S w).1 ∧ IsHalf e (o''.resT S w).2 := by
  rw [OrthDec.resT_apply]
  exact ⟨isHalf_mul_left _ h, isHalf_mul_left _ h⟩

theorem smul_latV_mem_latA {S : HSp D} (L : Lat S) (P : Pl D → Prop) {c : D.host.E} (hc : c ∈ D.host.AA)
    {w : Fin S.rank → AE D} (hw : w ∈ latV S L P) : ((1 : AF D.host.F) ⊗ₜ[D.host.F] c : AE D) • w ∈ latA S L P := by
  induction hw using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, hv, a, ha, z, hz, rfl⟩ := hy
    rw [Set.mem_singleton_iff] at ha
    subst ha
    refine AddSubgroup.subset_closure ⟨α, hα, hv, c, hc, z, hz, ?_⟩
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add y y' _ _ h h' => rw [smul_add]; exact add_mem h h'
  | neg y _ h => rw [smul_neg]; exact neg_mem h

theorem latA_orth {S A B : HSp D} (o : OrthDec S A B) (L : Lat S) (LA : Lat A) (LB : Lat B) (x : Pl D)
    (hO : OrthAt o L LA LB x) {z : Fin S.rank → AE D} (hz : z ∈ latA S L (· = x)) :
    o.pA *ᵥ z ∈ latA A LA (· = x) ∧ o.pB *ᵥ z ∈ latA B LB (· = x) := by
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, hv, a, ha, z, hz, rfl⟩ := hy
    have h0 : (fun i => pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * z i) : Fin S.rank → AE D) ∈ latV S L (· = x) :=
      AddSubgroup.subset_closure ⟨α, hα, hv, 1, Set.mem_singleton _, z, hz, rfl⟩
    have e : (fun i => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * z i) : Fin S.rank → AE D) =
        ((1 : AF D.host.F) ⊗ₜ[D.host.F] a : AE D) • (fun i => pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * z i)) := by
      funext i
      simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    obtain ⟨hA, hB⟩ := (hO _).1 h0
    rw [e, Matrix.mulVec_smul, Matrix.mulVec_smul]
    exact ⟨smul_latV_mem_latA LA _ ha hA, smul_latV_mem_latA LB _ ha hB⟩
  | zero => simp only [Matrix.mulVec_zero]; exact ⟨zero_mem _, zero_mem _⟩
  | add y y' _ _ h h' => simp only [Matrix.mulVec_add]; exact ⟨add_mem h.1 h'.1, add_mem h.2 h'.2⟩
  | neg y _ h => simp only [Matrix.mulVec_neg]; exact ⟨neg_mem h.1, neg_mem h.2⟩

theorem extLat : ∀ (D : D7) (V₀ A L S : HSp D) (o : OrthDec V₀ A L) (M : Lat V₀) (LA : Lat A) (LL : Lat L) (LS : Lat S)
    (x : Pl D), IsSelfDualC V₀ M → IsSelfDualC A LA → IsSelfDualC L LL → IsSelfDualC S LS → OrthAt o M LA LL x →
    ∀ (a : WO A S) (b : WO L S), a ∈ latO A S (LA : Set _) (LS : Set _) (· = x) → b ∈ latO L S (LL : Set _) (LS : Set _) (· = x) →
      (o.resS S).symm (a, b) ∈ latO V₀ S (M : Set _) (LS : Set _) (· = x) := by
  intro D V₀ A L S o M LA LL LS x hM hLA hLL hLS hO a b ha hb
  rw [GlobalTheory.FinPl.LatMem.mem_latO_iff D A S LA LS hLA hLS] at ha
  rw [GlobalTheory.FinPl.LatMem.mem_latO_iff D L S LL LS hLL hLS] at hb
  rw [GlobalTheory.FinPl.LatMem.mem_latO_iff D V₀ S M LS hM hLS, OrthDec.resS_symm_apply]
  refine ⟨fun i j => ?_, fun y hy => ?_⟩
  · rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply]
    exact add_mem (sum_mem fun k _ => Ideal.mul_mem_right _ _ (ha.1 i k))
      (sum_mem fun k _ => Ideal.mul_mem_right _ _ (hb.1 i k))
  · obtain ⟨hA, hB⟩ := (hO y).1 hy
    rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact add_mem (ha.2 _ hA) (hb.2 _ hB)

theorem resLat : ∀ (D : D7) (X T L'' S : HSp D) (o'' : OrthDec X T L'') (LX : Lat X) (LT : Lat T) (LZ : Lat L'') (LS : Lat S)
    (x : Pl D), IsSelfDualC X LX → IsSelfDualC T LT → IsSelfDualC L'' LZ → IsSelfDualC S LS → OrthAt o'' LX LT LZ x →
    ∀ w : WO S X, w ∈ latO S X (LS : Set _) (LX : Set _) (· = x) →
      (o''.resT S w).1 ∈ latO S T (LS : Set _) (LT : Set _) (· = x) ∧ (o''.resT S w).2 ∈ latO S L'' (LS : Set _) (LZ : Set _) (· = x) := by
  intro D X T L'' S o'' LX LT LZ LS x hLX hLT hLZ hLS hO w hw
  rw [GlobalTheory.FinPl.LatMem.mem_latO_iff D S X LS LX hLS hLX] at hw
  rw [GlobalTheory.FinPl.LatMem.mem_latO_iff D S T LS LT hLS hLT, GlobalTheory.FinPl.LatMem.mem_latO_iff D S L'' LS LZ hLS hLZ,
    OrthDec.resT_apply]
  refine ⟨⟨fun i j => ?_, fun y hy => ?_⟩, ⟨fun i j => ?_, fun y hy => ?_⟩⟩
  · show (o''.pA * (w : Matrix (Fin X.rank) (Fin S.rank) (AE D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D)) i j ∈ _
    rw [Matrix.mul_apply]; exact sum_mem fun k _ => Ideal.mul_mem_left _ _ (hw.1 k j)
  · rw [← Matrix.mulVec_mulVec]; exact (latA_orth o'' LX LT LZ x hO (hw.2 y hy)).1
  · show (o''.pB * (w : Matrix (Fin X.rank) (Fin S.rank) (AE D)) : Matrix (Fin L''.rank) (Fin S.rank) (AE D)) i j ∈ _
    rw [Matrix.mul_apply]; exact sum_mem fun k _ => Ideal.mul_mem_left _ _ (hw.1 k j)
  · rw [← Matrix.mulVec_mulVec]; exact (latA_orth o'' LX LT LZ x hO (hw.2 y hy)).2

theorem lastVac : ∀ D : D7, GlobalTheory.FinPl.LastVac D := by
  intro D ψ hψ V₀ A L S X T L'' o o'' τ hL hL'' hτ P M LA LS LX LT hM hLA hLS hLX hLT hP Ξ Φ₂ hΞ hΦ
  have hB := GlobalTheory.LastBiTheta.isBiTheta_lastBi D ψ hψ V₀ A L S X T L'' o o'' τ hτ Ξ Φ₂ hΞ.1 hΦ.1
  obtain ⟨kadd, -, -, -, -, -⟩ := GlobalTheory.LinkKappa.kappa_props D L L'' S τ (-1)
    (by rw [Int.cast_neg, Int.cast_one, neg_one_mul]; exact hτ) (kap τ S) (fun _ => rfl)
  have mono : ∀ {S' T' : HSp D} (LS' : Lat S') (LT' : Lat T') (x : Pl D), P x → ∀ w,
      w ∈ latO S' T' (LS' : Set _) (LT' : Set _) (· = x) → w ∈ latO S' T' (LS' : Set _) (LT' : Set _) P :=
    fun LS' LT' x hx w hw => GlobalTheory.VacLoc.latO_mono _ _ _ _ (fun v hv => hv ▸ hx) hw
  refine ⟨fun v => ⟨slice_left hB v, GlobalTheory.VacLoc.latVac_of_places ψ A S LA LS P _ (slice_left hB v) fun x hx => ?_⟩,
    fun u => ⟨slice_right hB u,
      GlobalTheory.VacLoc.latVac_of_places ψ S X LS LX P _ (slice_right hB u) fun x hx => ?_⟩⟩
  · obtain ⟨-, LL, LZ, hLL, hLZ, hOM, -, -⟩ := hP x hx
    refine ⟨slice_left hB v, fun a ha => ?_, fun e he a ha hh => ?_⟩
    · have hm := mono M LS x hx _ (extLat D V₀ A L S o M LA LL LS x hM hLA hLL hLS hOM a 0 ha (zero_mem _))
      have e2 : (o.resS S).symm (2 • a, 0) = 2 • (o.resS S).symm (a, 0) := by
        simp only [two_nsmul]
        rw [← map_add, Prod.mk_add_mk, add_zero]
      rw [heis_left, e2, hΞ.2.1 _ hm]
      rfl
    · have hm := mono M LS x hx _ (extLat D V₀ A L S o M LA LL LS x hM hLA hLL hLS hOM a 0 ha (zero_mem _))
      rw [heis_left, hΞ.2.2 e he _ hm (isHalf_resS_symm o S hh (isHalf_zero e _ _))]
      rfl
  · obtain ⟨-, LL, LZ, hLL, hLZ, hOM, hOX, hk⟩ := hP x hx
    refine ⟨slice_right hB u, fun b hb => ?_, fun e he b hb hh => ?_⟩
    · obtain ⟨h1, h2⟩ := resLat D X T L'' S o'' LX LT LZ LS x hLX hLT hLZ hLS hOX b hb
      have hm1 := mono LS LT x hx _ h1
      have hm2 := mono M LS x hx _ (extLat D V₀ A L S o M LA LL LS x hM hLA hLL hLS hOM 0 _ (zero_mem _) (hk _ h2))
      have e1 : (o''.resT S (2 • b)).1 = 2 • (o''.resT S b).1 := by
        simp only [two_nsmul, map_add, Prod.fst_add]
      have e2 : (o.resS S).symm (0, kap τ S (o''.resT S (2 • b)).2) = 2 • (o.resS S).symm (0, kap τ S (o''.resT S b).2) := by
        simp only [two_nsmul]
        rw [map_add, Prod.snd_add, kadd, ← map_add, Prod.mk_add_mk, add_zero]
      rw [heis_right ψ o o'' τ hτ, e1, e2, hΦ.2.1 _ hm1, hΞ.2.1 _ hm2]
      rfl
    · obtain ⟨h1, h2⟩ := resLat D X T L'' S o'' LX LT LZ LS x hLX hLT hLZ hLS hOX b hb
      have hm1 := mono LS LT x hx _ h1
      have hm2 := mono M LS x hx _ (extLat D V₀ A L S o M LA LL LS x hM hLA hLL hLS hOM 0 _ (zero_mem _) (hk _ h2))
      obtain ⟨he1, he2⟩ := isHalf_resT o'' S hh
      rw [heis_right ψ o o'' τ hτ, hΦ.2.2 e he _ hm1 he1,
        hΞ.2.2 (cA D e) (isSplitIdem_cA he) _ hm2 (isHalf_resS_symm o S (isHalf_zero _ _ _) (isHalf_kap τ S he2))]
      rfl

end GlobalTheory.LastVacPf

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSupportedSubgroupOfSuppAtSplitPlaceMemStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_supportedSubgroup_of_suppAt_splitPlace_mem : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (V : HSp D) (g : GA D V), SuppAt q.e V g → ∀ P : GlobalTheory.FinPl.Pl D → Prop, P q.v → g ∈ GlobalTheory.FinPl.grpAt V P := by
  first | exact @GlobalTheory.SuppGrp.mem_grpAt_of_suppAt | exact GlobalTheory.SuppGrp.mem_grpAt_of_suppAt | (intros; apply GlobalTheory.SuppGrp.mem_grpAt_of_suppAt <;> assumption)
end

