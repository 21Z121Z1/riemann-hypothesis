import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0264
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0138
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0125
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0141
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.VacuumMemSpanHeisenbergTranslatesOfNeZero
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VacCyclic

theorem exists_mem_of_eigen {X ι U : Type} [AddCommGroup X] [Module ℂ X] (v : ι → X) (A : U → X →ₗ[ℂ] X) (χ : ι → U → ℂ)
    (hA : ∀ i u, A u (v i) = χ i u • v i) (hp : ∀ i j, (∀ u, χ i u = χ j u) → v i ∈ Submodule.span ℂ {v j})
    (W : Submodule ℂ X) (hW : ∀ u, ∀ x ∈ W, A u x ∈ W) (s : Finset ι) :
    ∀ f ∈ Submodule.span ℂ (v '' s), f ∈ W → f ≠ 0 → ∃ i, v i ∈ W := by
  classical
  induction s using Finset.strongInduction with
  | H s ih =>
  intro f hf hfW hf0

  have hrem : ∀ i ∈ s, ∀ u, A u f - χ i u • f ∈ Submodule.span ℂ (v '' (s.erase i : Finset ι)) := by
    intro i _ u
    have : Submodule.span ℂ (v '' s) ≤
        (Submodule.span ℂ (v '' (s.erase i : Finset ι))).comap (A u - χ i u • LinearMap.id) := by
      rw [Submodule.span_le]
      rintro _ ⟨j, hj, rfl⟩
      show A u (v j) - χ i u • v j ∈ Submodule.span ℂ (v '' (s.erase i : Finset ι))
      rw [hA, ← sub_smul]
      by_cases h : j = i
      · rw [h, sub_self, zero_smul]; exact zero_mem _
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, Finset.mem_coe.2 (Finset.mem_erase.2 ⟨h, hj⟩), rfl⟩)
    exact this hf
  rcases s.eq_empty_or_nonempty with rfl | ⟨i, hi⟩
  · simp at hf; exact absurd hf hf0
  by_cases hall : ∀ j ∈ s, ∀ u, χ j u = χ i u
  · have : Submodule.span ℂ (v '' s) ≤ Submodule.span ℂ {v i} := by
      rw [Submodule.span_le]
      rintro _ ⟨j, hj, rfl⟩
      exact hp j i (hall j hj)
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 (this hf)
    have hc : c ≠ 0 := by rintro rfl; exact hf0 (zero_smul _ _)
    exact ⟨i, (W.smul_mem_iff hc).1 hfW⟩
  · push Not at hall
    obtain ⟨j, hj, u, hu⟩ := hall
    have hm : ∀ k, A u f - χ k u • f ∈ W := fun k => W.sub_mem (hW u f hfW) (W.smul_mem _ hfW)
    by_cases h0 : A u f - χ i u • f = 0
    · refine ih _ (Finset.erase_ssubset hj) _ (hrem j hj u) (hm j) fun h1 => hf0 ?_
      have : (χ j u - χ i u) • f = 0 := by
        rw [sub_smul, ← sub_eq_zero.1 h0, ← sub_eq_zero.1 h1, sub_self]
      exact (smul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hu)
    · exact ih _ (Finset.erase_ssubset hi) _ (hrem i hi u) (hm i) h0

theorem psi_ne_zero {A : Type} [AddCommGroup A] (ψ : AddChar A ℂ) (x : A) : ψ x ≠ 0 := fun h => by
  have := ψ.map_add_eq_mul x (-x)
  rw [add_neg_cancel, ψ.map_zero_eq_one, h, zero_mul] at this
  exact one_ne_zero this

theorem fin_add {D : D7} {S T : HSp D} {a b : WO S T} (ha : a.map (infPart D) = 0) (hb : b.map (infPart D) = 0) :
    (a + b).map (infPart D) = 0 := by
  ext i j
  have h1 : infPart D (a i j) = 0 := congrFun (congrFun ha i) j
  have h2 : infPart D (b i j) = 0 := congrFun (congrFun hb i) j
  show infPart D (a i j + b i j) = 0
  rw [RingHom.map_add, h1, h2, add_zero]

theorem fin_neg {D : D7} {S T : HSp D} {a : WO S T} (ha : a.map (infPart D) = 0) : (-a).map (infPart D) = 0 := by
  ext i j
  have h1 : infPart D (a i j) = 0 := congrFun (congrFun ha i) j
  show infPart D (-a i j) = 0
  rw [RingHom.map_neg, h1, neg_zero]

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem fin_zero : (0 : WO S T).map (infPart D) = 0 := by
  ext i j
  show infPart D (0 : AE D) = 0
  exact RingHom.map_zero _

theorem symplO_neg_right (u b : WO S T) : symplO S T u (-b) = -symplO S T u b := by
  refine eq_neg_of_add_eq_zero_left ?_
  rw [← GlobalTheory.LatVac.symplO_add_right, neg_add_cancel, GlobalTheory.SplitScalar.symplO_zero_right]

theorem psi_diff {u a b : WO S T} (h : ψ (symplO S T u a) = ψ (symplO S T u b)) : ψ (symplO S T (-b + a) u) = 1 := by
  rw [GlobalTheory.SplitScalar.symplO_skew S T u, GlobalTheory.LatVac.symplO_add_right, symplO_neg_right, neg_add, neg_neg,
    ψ.map_add_eq_mul, ← h, ← ψ.map_add_eq_mul, add_neg_cancel, ψ.map_zero_eq_one]

theorem prop_of_eigen {a b : WO S T} {f₀ : WO S T → ℂ} {ε : ℂ} (h : heisO ψ S T (-b + a) f₀ = ε • f₀) :
    heisO ψ S T a f₀ ∈ Submodule.span ℂ {heisO ψ S T b f₀} := by
  have e := GlobalTheory.LatVac.heisO_heisO ψ b (-b + a) f₀
  rw [h, GlobalTheory.LatVac.heisO_smul, add_neg_cancel_left] at e
  refine (Submodule.smul_mem_iff _ (psi_ne_zero ψ (symplOH S T b (-b + a)))).1 ?_
  rw [← e]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

theorem heis_mem_span {f x : WO S T → ℂ} {b : WO S T} (hb : b.map (infPart D) = 0)
    (hx : x ∈ Submodule.span ℂ (Set.range fun a : {a : WO S T // a.map (infPart D) = 0} => heisO ψ S T a f)) :
    heisO ψ S T b x ∈ Submodule.span ℂ (Set.range fun a : {a : WO S T // a.map (infPart D) = 0} => heisO ψ S T a f) := by
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hx
  rw [← GlobalTheory.SplitScalar.heisL_apply, Finsupp.sum, map_sum]
  refine Submodule.sum_mem _ fun a _ => ?_
  rw [map_smul, GlobalTheory.SplitScalar.heisL_apply, GlobalTheory.LatVac.heisO_heisO]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨b + a, fin_add hb a.2⟩, rfl⟩))

theorem mem_of_heis_mem {W : Submodule ℂ (WO S T → ℂ)} {f₀ : WO S T → ℂ} {a : WO S T}
    (h : heisO ψ S T (-a) (heisO ψ S T a f₀) ∈ W) : f₀ ∈ W := by
  rw [GlobalTheory.LatVac.heisO_heisO, neg_add_cancel, GlobalTheory.LatVac.heisO_zero] at h
  exact (W.smul_mem_iff (psi_ne_zero ψ _)).1 h

theorem mem_span_of_dual (Λ : AddSubgroup (WO S T)) (hfin : ∀ u ∈ Λ, u.map (infPart D) = 0)
    (hdual : ∀ u : WO S T, u.map (infPart D) = 0 → (∀ u' ∈ Λ, ψ (symplO S T u u') = 1) → u ∈ Λ) {f₀ f : WO S T → ℂ}
    (hε : ∀ u : Λ, ∃ ε : ℂ, ε ≠ 0 ∧ heisO ψ S T u f₀ = ε • f₀)
    (hf : f ∈ Submodule.span ℂ (Set.range fun a : {a : WO S T // a.map (infPart D) = 0} => heisO ψ S T a f₀))
    (hf0 : f ≠ 0) :
    f₀ ∈ Submodule.span ℂ (Set.range fun a : {a : WO S T // a.map (infPart D) = 0} => heisO ψ S T a f) := by
  choose ε hε0 hε using hε
  have hfW : f ∈ Submodule.span ℂ (Set.range fun a : {a : WO S T // a.map (infPart D) = 0} => heisO ψ S T a f) :=
    Submodule.subset_span ⟨⟨0, fin_zero⟩, GlobalTheory.LatVac.heisO_zero ψ f⟩
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hf
  have hfs : f ∈ Submodule.span ℂ ((fun a : {a : WO S T // a.map (infPart D) = 0} => heisO ψ S T a f₀) '' c.support) := by
    rw [← hc]
    exact Submodule.sum_mem _ fun a ha => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, ha, rfl⟩)
  obtain ⟨a, ha⟩ := exists_mem_of_eigen (fun a : {a : WO S T // a.map (infPart D) = 0} => heisO ψ S T a f₀)
    (fun u : Λ => GlobalTheory.SplitScalar.heisL ψ S T u) (fun a u => ψ (symplO S T u a) * ε u)
    (fun a u => by
      rw [GlobalTheory.SplitScalar.heisL_apply, GlobalTheory.SplitScalar.heisO_comm, hε, GlobalTheory.LatVac.heisO_smul, smul_smul])
    (fun a b h => prop_of_eigen (hε ⟨_, hdual _ (fin_add (fin_neg b.2) a.2) fun u hu =>
      psi_diff (mul_right_cancel₀ (hε0 ⟨u, hu⟩) (h ⟨u, hu⟩))⟩))
    _ (fun u x hx => by
      rw [GlobalTheory.SplitScalar.heisL_apply]
      exact heis_mem_span (hfin u u.2) hx) c.support f hfs hfW hf0
  exact mem_of_heis_mem (heis_mem_span (fin_neg a.2) ha)

theorem vac_mem_span : ∀ {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {f₀ f : WO S T → ℂ}, IsVacO ψ θ S T sS sT ΛS ΛT f₀ → IsSelfDualC S ΛS → IsSelfDualC T ΛT → f ∈ Submodule.span ℂ (Set.range fun a : {a : WO S T // a.map (infPart D) = 0} => heisO ψ S T a f₀) → f ≠ 0 → f₀ ∈ Submodule.span ℂ (Set.range fun a : {a : WO S T // a.map (infPart D) = 0} => heisO ψ S T a f) := by
  intro D ψ θ S T sS sT ΛS ΛT f₀ f hv hS hT hf hf0
  obtain ⟨hdual, -, hsign⟩ := GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hv.1 hS hT
  refine mem_span_of_dual _ (fun u hu => GlobalTheory.SplitScalar.latO_fin hu) (fun u hu h => (hdual u hu).2 h) (fun u => ?_) hf hf0
  obtain ⟨ε, h1, h2⟩ := hsign f₀ hv.2.lat u u.2
  refine ⟨ε, ?_, h2 f₀ hv.2.lat⟩
  rcases h1 with rfl | rfl <;> simp

end GlobalTheory.VacCyclic

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittLeviTransvectionMemCompactAtPlace
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.RootKeep

open GlobalTheory.IwaPlace

variable {D : D7} {S S₀ : HSp D} {ρ : ℕ}

theorem conj_mem_idAt {v : Pl D} {r : AE D} (hr : r ∈ idAt D (· = v)) : cA D r ∈ idAt D (· = v) := by
  obtain ⟨ε, hc, hε, hact⟩ := LocSD.exists_idem v
  rw [← hact r hr, RingHom.map_mul, hc]
  exact Ideal.mul_mem_right _ _ hε.1

theorem colMul_add {m n : ℕ} (x : Mx D m n) (l : Fin n) (a b : AE D) :
    colMul x l (a + b) = colMul x l a + colMul x l b := by
  funext k; exact add_mul _ _ _

theorem colMul_neg {m n : ℕ} (x : Mx D m n) (l : Fin n) (a : AE D) : colMul x l (-a) = -colMul x l a := by
  funext k; exact neg_mul _ _

theorem hermAt_colMul_jY (d : HypDec S S₀ ρ) (l : Fin ρ) (b : AE D) (x : Fin S.rank → AE D) :
    hermAt S (colMul d.jY l b) x = b * cA D ((d.pX *ᵥ x) l) := by
  have hg : ∀ k m, cA D (gA S k m) = gA S m k := fun k m => congrFun (congrFun (adj_gA S) m) k
  have hp : ∀ m, cA D (d.pX l m) = ∑ k, gA S m k * d.jY k l := fun m => by
    rw [d.pX_eq, Matrix.mul_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [RingHom.map_mul, hg, mul_comm]
    exact congrArg _ (congrFun (congrFun (adj_adj d.jY) k) l)
  unfold hermAt colMul
  rw [Matrix.mulVec, dotProduct, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [RingHom.map_mul, hp, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem pX_colMul_jX (d : HypDec S S₀ ρ) (l : Fin ρ) (a : AE D) : (d.pX *ᵥ colMul d.jX l a) l = a := by
  have h : (d.pX ⬝ d.jX) l l = 1 := by rw [d.pX_jX, Matrix.one_apply_eq]
  rw [Matrix.mul_apply] at h
  refine Eq.trans ?_ (mul_one a)
  rw [Matrix.mulVec, dotProduct, ← h, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold colMul
  ring

theorem transv_mulVec (i j : Fin ρ) (r : AE D) (u : Fin ρ → AE D) (l : Fin ρ) :
    (transvection i j r *ᵥ u) l = u l + if l = i then r * u j else 0 := by
  rw [transvection, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec, Pi.add_apply, Function.update_apply]
  rfl

theorem adj_transv (i j : Fin ρ) (r : AE D) : adj (transvection i j r : Mx D ρ ρ) = transvection j i (cA D r) := by
  rw [transvection, transvection, adj_add, adj_one]
  congr 1
  funext a b
  change cA D (Matrix.single i j r b a) = _
  simp only [Matrix.single_apply]
  by_cases h : i = b ∧ j = a
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun h' => h h'.symm), RingHom.map_zero]

theorem levi_maps (d : HypDec S S₀ ρ) {L : Lat S} {L₀ : Lat S₀} {v : Pl D} (hL : IsSelfDualC S L)
    (hM : MonoAt d L L₀ v) {i j : Fin ρ} (hij : i ≠ j) {r : AE D}
    (h : ∀ a ∈ idAt D (· = v), colMul d.jX j a ∈ latV S L (· = v) → colMul d.jX i (r * a) ∈ latV S L (· = v))
    {y : Fin S.rank → AE D} (hy : y ∈ latV S L (· = v)) :
    mt S (d.levi (GlobalTheory.GLGen.transvGL hij r)) *ᵥ y ∈ latV S L (· = v) := by
  obtain ⟨hs, -, hd⟩ := LocSD.isSDAt_latV D S L v hL
  have hX : ∀ x ∈ latV S L (· = v), colMul d.jX i (r * (d.pX *ᵥ x) j) ∈ latV S L (· = v) := fun x hx =>
    h _ (mulVec_mem_idAt _ (hs x hx) j) (((hM x).1 hx).1 j)
  obtain ⟨h1, h2, h3⟩ := (hM y).1 hy
  refine (hM _).2 ⟨fun l => ?_, fun l => ?_, ?_⟩
  · rw [Matrix.mulVec_mulVec, d.pX_levi, ← Matrix.mulVec_mulVec]
    change colMul d.jX l ((transvection i j r *ᵥ _) l) ∈ _
    rw [transv_mulVec, colMul_add]
    refine add_mem (h1 l) ?_
    split_ifs with hl
    · rw [hl]; exact hX y hy
    · have : colMul d.jX l 0 = 0 := funext fun k => zero_mul _
      rw [this]; exact zero_mem _
  · rw [Matrix.mulVec_mulVec, d.pY_levi, ← Matrix.mulVec_mulVec]
    change colMul d.jY l ((adj (transvection i j (-r) : Mx D ρ ρ) *ᵥ _) l) ∈ _
    rw [adj_transv, transv_mulVec, colMul_add]
    refine add_mem (h2 l) ?_
    split_ifs with hl
    · rw [hl, RingHom.map_neg, neg_mul, colMul_neg]
      refine neg_mem ((hd _ fun k => ?_).2 fun x hx => ?_)
      · exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (mulVec_mem_idAt _ (hs y hy) i))
      · have h4 := (hd _ (hs _ (h2 i))).1 (h2 i) _ (hX x hx)
        rw [hermAt_colMul_jY, pX_colMul_jX, RingHom.map_mul] at h4
        rw [hermAt_colMul_jY]
        convert h4 using 1
        ring
    · have : colMul d.jY l 0 = 0 := funext fun k => zero_mul _
      rw [this]; exact zero_mem _
  · rwa [Matrix.mulVec_mulVec, d.wittDecomp_projAnisotropic_levi]

theorem levi_mem_grpAt (d : HypDec S S₀ ρ) {v : Pl D} {i j : Fin ρ} (hij : i ≠ j) {r : AE D}
    (hr : r ∈ idAt D (· = v)) : d.levi (GlobalTheory.GLGen.transvGL hij r) ∈ grpAt S (· = v) := by
  refine (mem_congGrp_iff S _ _).2 fun a b => ?_
  have e : mt S (d.levi (GlobalTheory.GLGen.transvGL hij r)) - 1 =
      d.jX ⬝ (Matrix.single i j r : Mx D ρ ρ) ⬝ d.pX + d.jY ⬝ (Matrix.single j i (cA D (-r)) : Mx D ρ ρ) ⬝ d.pY := by
    rw [d.mt_levi, ← d.sum_eq_one]
    change d.jX ⬝ (transvection i j r : Mx D ρ ρ) ⬝ d.pX + _ + d.jY ⬝ adj (transvection i j (-r) : Mx D ρ ρ) ⬝ d.pY - _ = _
    rw [adj_transv, transvection, transvection]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one]
    abel
  have k : ∀ (A : Mx D S.rank ρ) (B : Mx D ρ S.rank) (p q : Fin ρ) (s : AE D), s ∈ idAt D (· = v) →
      (A ⬝ (Matrix.single p q s : Mx D ρ ρ) ⬝ B) a b ∈ idAt D (· = v) := fun A B p q s hs => by
    rw [Matrix.mul_apply]
    refine Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ ?_
    rw [Matrix.mul_apply]
    refine Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ ?_
    rw [Matrix.single_apply]
    split_ifs
    · exact hs
    · exact zero_mem _
  rw [← Matrix.sub_apply, e, Matrix.add_apply]
  exact add_mem (k _ _ _ _ _ hr) (k _ _ _ _ _ (conj_mem_idAt (neg_mem hr)))

theorem inK_levi_transv : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L : Lat S) (L₀ : Lat S₀) (v : Pl D), IsSelfDualC S L → MonoAt d L L₀ v → ∀ (i j : Fin ρ) (hij : i ≠ j) (r : AE D), r ∈ idAt D (· = v) → (∀ a ∈ idAt D (· = v), colMul d.jX j a ∈ latV S L (· = v) → colMul d.jX i (r * a) ∈ latV S L (· = v)) → InK S L (· = v) (d.levi (GlobalTheory.GLGen.transvGL hij r)) := by
  intro D S S₀ ρ d L L₀ v hL hM i j hij r hr h
  refine ⟨levi_mem_grpAt d hij hr, fun y _ => ⟨fun hy => levi_maps d hL hM hij h hy, fun hy => ?_⟩⟩
  have h' := levi_maps d hL hM hij (r := -r) (fun a ha hb => by
    rw [neg_mul, colMul_neg]; exact neg_mem (h a ha hb)) hy
  have e : GlobalTheory.GLGen.transvGL hij (-r) = (GlobalTheory.GLGen.transvGL hij r)⁻¹ := Units.ext rfl
  rwa [Matrix.mulVec_mulVec, ← mt_mul, ← map_mul, e, inv_mul_cancel, map_one, mt_one, Matrix.one_mulVec] at h'

end GlobalTheory.FinPl.RootKeep

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittSourceMixedCoordHeisenbergRestrictionStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wittSourceMixedCoord_heisenbergRestriction : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), (0 < ρ → GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit S S₀ d.e d.i₀) ∧ GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D T.rank ρ = ratMx D T.rank ρ ∧ (∀ y, GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart S T d.e y = d.extY T y) ∧ (∀ y, GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart S T d.e' y = d.extX T y) ∧ (∀ w, GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart S S₀ T d.i₀ w = d.ext0 T w) ∧ (∀ μ 𝓕 f x, d.mixS T ψ μ 𝓕 f x = GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res S S₀ T d.e d.i₀ μ 𝓕 (heisO ψ S T (d.extX T x) f)) ∧ (∀ μ 𝓕 f x, d.mixS T ψ μ 𝓕 f x = d.mixS T ψ μ 𝓕 (heisO ψ S T (d.extX T x) f) 0) ∧ (∀ b, d.nB b ∈ NI S d.e) ∧ ∀ c, d.nC c ∈ NI S d.e := by
  first | exact @GlobalTheory.Bridge.heis_bridge | exact GlobalTheory.Bridge.heis_bridge | (intros; apply GlobalTheory.Bridge.heis_bridge <;> assumption)
end

