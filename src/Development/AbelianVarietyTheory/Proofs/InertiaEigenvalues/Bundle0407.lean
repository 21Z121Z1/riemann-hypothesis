import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsJumpMultiset
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0385
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0191
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0401
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeakTopologyWittTiltTensor
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZlTowerGen
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0295
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0382
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0302
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0296
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0260
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0283
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0282
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0377
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0278
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0336
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0358
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0267
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0311

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContChiRat
section
noncomputable section

namespace GlobalTheory.HfCharProof

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

variable (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
  (hw : w ∈ placesOver D.host.E (D.nd.l i))

theorem act_chiRat (c : ℕ) (g : Br.G D.nbr i w hw) (x : Fin 1 → Br.LL D.nbr i w hw) :
    matRep (Br.loc D.nbr i w hw (chiRatO D.nd i c)) g x =
      (D.nbr i w hw).toLL (((chiU D.nd i c * (chiU D.nd i 1)⁻¹)
        (decS D.nd w (Br.iota D.nbr i w hw g)) : (D.nd.O i)ˣ) : D.nd.O i) • x := by
  funext b
  rw [Subsingleton.elim b 0]
  change (Br.loc D.nbr i w hw (chiRatO D.nd i c) g).mulVec x 0 = _
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_one, Fin.isValue, Pi.smul_apply, smul_eq_mul]
  congr 1
  change (D.nbr i w hw).toLL (chiRatO D.nd i c (decS D.nd w (Br.iota D.nbr i w hw g)) 0 0) = _
  congr 1
  simp [chiRatO, twistM]

theorem cont_chiRat (c : ℕ) (x : Fin 1 → Br.LL D.nbr i w hw) :
    Continuous fun g => matRep (Br.loc D.nbr i w hw (chiRatO D.nd i c)) g x := by
  simp only [act_chiRat]
  have hs : Continuous fun g : Br.G D.nbr i w hw => decS D.nd w (Br.iota D.nbr i w hw g) :=
    continuous_subtype_val.comp (Br.iota_cont D.nbr i w hw)
  have hL : Continuous (D.nbr i w hw).toLL := continuous_subtype_val.comp (D.nbr i w hw).eO_cont
  have h1 : Continuous fun g : Br.G D.nbr i w hw => (D.nbr i w hw).toLL
      ((D.nd.chi i c (decS D.nd w (Br.iota D.nbr i w hw g)) : (D.nd.O i)ˣ) : D.nd.O i) *
      (D.nbr i w hw).toLL
      ((D.nd.chi i 1 (decS D.nd w (Br.iota D.nbr i w hw g⁻¹)) : (D.nd.O i)ˣ) : D.nd.O i) :=
    (hL.comp ((D.nd.chi_cont i c).comp hs)).mul
      (hL.comp ((D.nd.chi_cont i 1).comp (hs.comp continuous_inv)))
  refine Continuous.smul (h1.congr fun g => ?_) continuous_const
  rw [← map_mul, ← Units.val_mul, map_inv, map_inv, map_inv]
  rfl

theorem chiRat_eq (n : ℕ) (hn : n = 0 ∨ n + 1 ≤ D.R.t) (g : Formalism.MainNotions.N.GE D.nd) :
    (chiU D.nd i (n + 1) * (chiU D.nd i 1)⁻¹) g = (epsU D.nd i g)⁻¹ ^ n := by
  rcases hn with rfl | hc
  · simp
  · have h := D.nd.chi_def i (n + 1) (by omega) hc
    change D.nd.chi i (n + 1) g * (D.nd.chi i 1)⁻¹ g = _
    rw [mul_comm, h, MonoidHom.mul_apply, MonoidHom.inv_apply, inv_mul_cancel_left, Nat.cast_add, Nat.cast_one,
      add_sub_cancel_right, MonoidHom.zpow_apply, zpow_neg, zpow_natCast, inv_pow]
    rfl

theorem eps_eq (g : Br.G D.nbr i w hw) :
    (D.nbr i w hw).toLL ((epsU D.nd i (decS D.nd w (Br.iota D.nbr i w hw g)) : (D.nd.O i)ˣ) : D.nd.O i) =
      algebraMap ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) ((Br.PD D.loc D.nbr i w hw).χ g : ℚ_[D.nd.l i]) := by
  haveI : IsAlgClosed D.nd.Om := IsAlgClosure.isAlgClosed D.host.E
  rw [Br.PD, (D.loc _).PD_χ, ← GlobalTheory.BlockJumps.cycZ_eq_chi (D.nbr i w hw) (D.loc _) g]
  exact congrArg Subtype.val ((D.nbr i w hw).eO_alg _)

theorem act_eq (n : ℕ) (hn : n = 0 ∨ n + 1 ≤ D.R.t) (g : Br.G D.nbr i w hw)
    (x : Fin 1 → Br.LL D.nbr i w hw) :
    matRep (Br.loc D.nbr i w hw (chiRatO D.nd i (n + 1))) g x =
      ((algebraMap ℚ_[D.nd.l i] (Br.LL D.nbr i w hw)
        ((Br.PD D.loc D.nbr i w hw).χ g : ℚ_[D.nd.l i]))⁻¹) ^ n • x := by
  rw [act_chiRat, chiRat_eq D i n hn, Units.val_pow_eq_pow_val, map_pow, map_units_inv, eps_eq]

def chiLat (c : ℕ) :
    LocLat (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw) where
  V := Fin 1 → Br.LL D.nbr i w hw
  ρ := matRep (Br.loc D.nbr i w hw (chiRatO D.nd i c))
  cont := cont_chiRat D i w hw c
  L := Br.locLat D.nbr i w hw (chiRatO D.nd i c)

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

theorem hfChar : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), LocalSituation.Conclusion4 D HW F → InertEq D →
    ∀ (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
      D.nd.l i ≠ 2 → (D.nbr i w hw).Kw.1 ≤ Ks (D.nbr i w hw).Kw 1 → HfChar i w hw := by
  intro D HW F h4 hI i w hw h2 hK
  have hs := (D.self_good i w hw).good_one (D.nbr i w hw).LL_split h2 hK
  have hT := (h4 (D.nd.l i) _ 1 _ hs).2
  have hr : ∀ c, finrank (Br.LL D.nbr i w hw) (chiLat D i w hw c).V = 1 := fun c =>
    Module.finrank_fin_fun _
  refine ⟨fun c hc => ?_, fun f hf => ?_⟩
  · obtain ⟨hc1, hc2⟩ := Finset.mem_Icc.1 hc
    obtain ⟨n, rfl⟩ : ∃ n, c = n + 1 := ⟨c - 1, by omega⟩
    exact ((hT n (chiLat D i w hw (n + 1)) (hr _) (act_eq D i w hw n (Or.inr hc2))).2.1 (by omega)).le
  · obtain ⟨-, x, hx⟩ :=
      ((hT 0 (chiLat D i w hw 1) (hr _) (act_eq D i w hw 0 (Or.inl rfl))).2.2 rfl f).1 hf
    refine ⟨x, fun g hg => hx g ?_⟩
    rw [hI i w hw] at hg
    exact hg

end GlobalTheory.HfCharProof

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOnGaussNormAcrisRadiusIco
section
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per
open Filter Topology

noncomputable section

namespace GlobalTheory.PMon.Gauss

theorem gC_zero_of_lt_one (l : ℕ) [Fact l.Prime] {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) :
    gC l ρ (0 : Formalism.Per.Acris l) = 0 := by
  unfold gC
  split_ifs with h
  · have hN := Classical.choose_spec h
    set N := Classical.choose h
    have hm := hN.2.2.2.1 ((l : Formalism.Per.Acris l)) 0
    have hl : N (l : Formalism.Per.Acris l) = ρ := by
      have := hN.2.2.2.2 (l : Formalism.Per.Ainf l)
      rw [map_natCast] at this
      rw [this]
      exact GlobalTheory.GaussSlope.gauss_l l h0
    rw [mul_zero, hl] at hm
    have : (1 - ρ) * N 0 = 0 := by linarith
    rcases mul_eq_zero.1 this with h' | h'
    · linarith
    · exact h'
  · rfl

theorem continuousOn_gC (l : ℕ) [Fact l.Prime] (x : Formalism.Per.Acris l) :
    ContinuousOn (fun ρ => gC l ρ x) (Set.Ico (l : ℝ)⁻¹ 1) := by
  have hl0 : (0 : ℝ) < (l : ℝ)⁻¹ := by
    have : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
    positivity
  by_cases hx : x = 0
  · subst hx
    refine (continuousOn_const (c := (0 : ℝ))).congr fun ρ hρ => ?_
    exact gC_zero_of_lt_one l (hl0.le.trans hρ.1) hρ.2
  intro ρ₀ hρ₀
  have hpos : 0 < ρ₀ := hl0.trans_le hρ₀.1
  obtain ⟨⟨c, k, ρ₂, -, h02, -, hR⟩, hL⟩ := GlobalTheory.T.gaussNormAcris_locally_monomial l x hx ρ₀ hρ₀.1 hρ₀.2
  have hS : Set.Ico (l : ℝ)⁻¹ 1 = (Set.Ico (l : ℝ)⁻¹ 1 ∩ Set.Iic ρ₀) ∪ (Set.Ico (l : ℝ)⁻¹ 1 ∩ Set.Ici ρ₀) := by
    ext y
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ici]
    constructor
    · intro hy
      rcases le_total y ρ₀ with h | h
      · exact Or.inl ⟨hy, h⟩
      · exact Or.inr ⟨hy, h⟩
    · rintro (h | h) <;> exact h.1
  rw [ContinuousWithinAt, hS, ← ContinuousWithinAt, continuousWithinAt_union]
  constructor
  · rcases eq_or_lt_of_le hρ₀.1 with heq | hlt
    · refine (continuousWithinAt_singleton (f := fun ρ => gC l ρ x) (x := ρ₀)).mono ?_
      rintro y ⟨hy1, hy2⟩
      exact le_antisymm hy2 (heq ▸ hy1.1)
    · obtain ⟨c', k', ρ₁, -, -, h10, hL'⟩ := hL hlt
      have hg : ContinuousWithinAt (fun ρ : ℝ => c' * ρ ^ k') (Set.Iic ρ₀) ρ₀ :=
        (continuousAt_const.mul (continuousAt_zpow₀ ρ₀ k' (Or.inl hpos.ne'))).continuousWithinAt
      have hg' : ContinuousWithinAt (fun ρ => gC l ρ x) (Set.Icc ρ₁ ρ₀) ρ₀ :=
        (hg.mono Set.Icc_subset_Iic_self).congr (fun y hy => hL' y hy) (hL' ρ₀ ⟨h10.le, le_rfl⟩)
      exact (hg'.mono_of_mem_nhdsWithin (Icc_mem_nhdsLE h10)).mono Set.inter_subset_right
  · have hg : ContinuousWithinAt (fun ρ : ℝ => c * ρ ^ k) (Set.Ici ρ₀) ρ₀ :=
      (continuousAt_const.mul (continuousAt_zpow₀ ρ₀ k (Or.inl hpos.ne'))).continuousWithinAt
    have hg' : ContinuousWithinAt (fun ρ => gC l ρ x) (Set.Icc ρ₀ ρ₂) ρ₀ :=
      (hg.mono Set.Icc_subset_Ici_self).congr (fun y hy => hR y hy) (hR ρ₀ ⟨le_rfl, h02.le⟩)
    exact (hg'.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE h02)).mono Set.inter_subset_right

theorem continuousOn_gC_target :
    ∀ (l : ℕ) [Fact l.Prime] (x : Formalism.Per.Acris l), ContinuousOn (fun ρ => gC l ρ x) (Set.Ico (l : ℝ)⁻¹ 1) :=
  fun l _ x => continuousOn_gC l x

end GlobalTheory.PMon.Gauss

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousRepOfMatrixTuplePadicBasis
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.CovRep

variable {l : ℕ} [Fact l.Prime]

theorem zOm_smul_eq {m a : ℕ} (c : ℤ_[l]) (x : Fin m → Matrix (Fin a) (Fin a) (Om l)) :
    zOm l c • x = ((c : ℚ_[l])) • x := by
  rw [← algebraMap_smul (Om l) (c : ℚ_[l]) x]
  rfl

theorem isInducing_coe : Topology.IsInducing (fun x : ℤ_[l] => (x : ℚ_[l])) := { eq_induced := rfl }

theorem coord_unique {m a d' : ℕ} {bb : Fin d' → Fin m → Matrix (Fin a) (Fin a) (Om l)}
    (hli : LinearIndependent ℚ_[l] bb) {z z' : Fin d' → ℤ_[l]}
    (h : ∑ s, zOm l (z s) • bb s = ∑ s, zOm l (z' s) • bb s) : z = z' := by
  simp only [zOm_smul_eq] at h
  have h0 : ∑ s, (((z s : ℚ_[l])) - (z' s : ℚ_[l])) • bb s = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, h, sub_self]
  have := (Fintype.linearIndependent_iff.mp hli) _ h0
  funext s
  have hs := this s
  rw [sub_eq_zero] at hs
  exact Subtype.ext hs

theorem tup_mul {Γ : Type} [Group Γ] {a m : ℕ} (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (g h : Γ) :
    GlobalTheory.TraceConjugationCover.tup ρs (g * h) = GlobalTheory.TraceConjugationCover.tup ρs g * GlobalTheory.TraceConjugationCover.tup ρs h := by
  funext k
  simp [GlobalTheory.TraceConjugationCover.tup]

theorem tup_one {Γ : Type} [Group Γ] {a m : ℕ} (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) :
    GlobalTheory.TraceConjugationCover.tup ρs 1 = 1 := by
  funext k
  simp [GlobalTheory.TraceConjugationCover.tup]

theorem tup_inv {Γ : Type} [Group Γ] {a m : ℕ} (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (g : Γ) :
    GlobalTheory.TraceConjugationCover.tup ρs g⁻¹ = fun k => (((ρs k g)⁻¹ : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) := by
  funext k
  simp [GlobalTheory.TraceConjugationCover.tup]

end GlobalTheory.CovRep

open GlobalTheory.CovRep in
theorem GlobalTheory.CovRep.rep_of_basis : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] (a m : ℕ) (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (T : Submodule ℤ_[l] (Fin m → Matrix (Fin a) (Fin a) (Om l))) (d' : ℕ) (bb : Fin d' → Fin m → Matrix (Fin a) (Fin a) (Om l)), (∀ k, Continuous (ρs k)) → LinearIndependent ℚ_[l] bb → (∀ s, bb s ∈ T) → (∀ x ∈ T, ∃ z : Fin d' → ℤ_[l], x = ∑ s, zOm l (z s) • bb s) → (∀ g, ∀ x ∈ T, GlobalTheory.TraceConjugationCover.tup ρs g * x ∈ T) → ∃ ρ' : Γ →* GL (Fin d') ℤ_[l], Continuous ρ' ∧ ∀ g j, GlobalTheory.TraceConjugationCover.tup ρs g * bb j = ∑ s, zOm l (((ρ' g : GL (Fin d') ℤ_[l]) : Matrix (Fin d') (Fin d') ℤ_[l]) s j) • bb s := by
  intro l _ Γ _ _ a m ρs T d' bb hc hli hbbT hcoord hstab
  classical
  let crd : (Fin m → Matrix (Fin a) (Fin a) (Om l)) → Fin d' → ℤ_[l] := fun x =>
    if h : ∃ z : Fin d' → ℤ_[l], x = ∑ s, zOm l (z s) • bb s then h.choose else 0
  have hcrd : ∀ x ∈ T, x = ∑ s, zOm l (crd x s) • bb s := by
    intro x hx
    have h := hcoord x hx
    simp only [crd, dif_pos h]
    exact h.choose_spec
  have hcrd_eq : ∀ z : Fin d' → ℤ_[l], crd (∑ s, zOm l (z s) • bb s) = z := by
    intro z
    have h : ∃ z' : Fin d' → ℤ_[l], ∑ s, zOm l (z s) • bb s = ∑ s, zOm l (z' s) • bb s := ⟨z, rfl⟩
    simp only [crd, dif_pos h]
    exact (coord_unique hli h.choose_spec).symm
  let Mf : Γ → Matrix (Fin d') (Fin d') ℤ_[l] := fun g => Matrix.of fun s j => crd (GlobalTheory.TraceConjugationCover.tup ρs g * bb j) s
  have hMf : ∀ g j, GlobalTheory.TraceConjugationCover.tup ρs g * bb j = ∑ s, zOm l (Mf g s j) • bb s :=
    fun g j => hcrd _ (hstab g _ (hbbT j))
  have key : ∀ g (z : Fin d' → ℤ_[l]),
      GlobalTheory.TraceConjugationCover.tup ρs g * ∑ s, zOm l (z s) • bb s = ∑ t, zOm l ((Mf g *ᵥ z) t) • bb t := by
    intro g z
    rw [Finset.mul_sum]
    simp_rw [mul_smul_comm, hMf, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← Finset.sum_smul]
    congr 1
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
    exact Finset.sum_congr rfl fun s _ => mul_comm _ _
  have hmul : ∀ g h, Mf (g * h) = Mf g * Mf h := by
    intro g h
    ext s j
    have e : GlobalTheory.TraceConjugationCover.tup ρs (g * h) * bb j = ∑ t, zOm l ((Mf g *ᵥ fun s => Mf h s j) t) • bb t := by
      rw [tup_mul, mul_assoc, hMf h j, key]
    show crd (GlobalTheory.TraceConjugationCover.tup ρs (g * h) * bb j) s = _
    rw [e, hcrd_eq]
    simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
  have hone : Mf 1 = 1 := by
    ext s j
    have e : GlobalTheory.TraceConjugationCover.tup ρs 1 * bb j = ∑ t, zOm l ((1 : Matrix (Fin d') (Fin d') ℤ_[l]) t j) • bb t := by
      rw [tup_one, one_mul]
      simp [Matrix.one_apply]
    show crd (GlobalTheory.TraceConjugationCover.tup ρs 1 * bb j) s = _
    rw [e, hcrd_eq]
  let ρM : Γ →* Matrix (Fin d') (Fin d') ℤ_[l] :=
    { toFun := Mf, map_one' := hone, map_mul' := hmul }
  let ρ' : Γ →* GL (Fin d') ℤ_[l] := ρM.toHomUnits
  have hval : ∀ g, ((ρ' g : GL (Fin d') ℤ_[l]) : Matrix (Fin d') (Fin d') ℤ_[l]) = Mf g := fun g => rfl

  let W := Submodule.span ℚ_[l] (Set.range bb)
  let B : Module.Basis (Fin d') ℚ_[l] W := Module.Basis.span hli
  haveI : FiniteDimensional ℚ_[l] W := Module.Finite.of_basis B
  have hW : ∀ x ∈ T, x ∈ W := by
    intro x hx
    rw [hcrd x hx]
    simp only [zOm_smul_eq]
    exact Submodule.sum_mem _ fun s _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, rfl⟩)
  have hrepr : ∀ x (hx : x ∈ T) s, ((crd x s : ℚ_[l])) = B.repr ⟨x, hW x hx⟩ s := by
    intro x hx s
    have e : (⟨x, hW x hx⟩ : W) = ∑ t, ((crd x t : ℚ_[l])) • B t := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      have hB : ∀ t, ((B t : W) : Fin m → Matrix (Fin a) (Fin a) (Om l)) = bb t := fun t => by
        show ((Module.Basis.span hli t : W) : Fin m → Matrix (Fin a) (Fin a) (Om l)) = bb t
        rw [Module.Basis.span_apply]
      simp only [Submodule.coe_smul, hB]
      show x = _
      conv_lhs => rw [hcrd x hx]
      exact Finset.sum_congr rfl fun t _ => zOm_smul_eq _ _
    rw [e, B.repr_sum_self]
  have hcont : ∀ F : Γ → (Fin m → Matrix (Fin a) (Fin a) (Om l)), Continuous F → (∀ g, F g ∈ T) →
      ∀ s, Continuous fun g => crd (F g) s := by
    intro F hF hT s
    rw [isInducing_coe.continuous_iff]
    have e : (fun x : ℤ_[l] => (x : ℚ_[l])) ∘ (fun g => crd (F g) s) =
        fun g => B.coord s ⟨F g, hW _ (hT g)⟩ := by
      funext g
      simp only [Function.comp_apply, Module.Basis.coord_apply]
      exact hrepr _ (hT g) s
    rw [e]
    exact (LinearMap.continuous_of_finiteDimensional (B.coord s)).comp (hF.subtype_mk _)
  have htup : Continuous fun g => GlobalTheory.TraceConjugationCover.tup ρs g :=
    continuous_pi fun k => Units.continuous_val.comp (hc k)
  have htupi : Continuous fun g => GlobalTheory.TraceConjugationCover.tup ρs g⁻¹ := by
    simp_rw [tup_inv]
    exact continuous_pi fun k => Units.continuous_coe_inv.comp (hc k)
  have hMc : Continuous Mf := by
    refine continuous_matrix fun s j => ?_
    exact hcont (fun g => GlobalTheory.TraceConjugationCover.tup ρs g * bb j)
      (continuous_pi fun k => (((continuous_apply k).comp htup).matrix_mul continuous_const))
      (fun g => hstab g _ (hbbT j)) s
  have hMci : Continuous fun g => Mf g⁻¹ := by
    refine continuous_matrix fun s j => ?_
    exact hcont (fun g => GlobalTheory.TraceConjugationCover.tup ρs g⁻¹ * bb j)
      (continuous_pi fun k => (((continuous_apply k).comp htupi).matrix_mul continuous_const))
      (fun g => hstab g⁻¹ _ (hbbT j)) s
  refine ⟨ρ', ?_, fun g j => by rw [hval]; exact hMf g j⟩
  rw [Units.continuous_iff]
  refine ⟨hMc, ?_⟩
  have e : (fun g => (((ρ' g)⁻¹ : GL (Fin d') ℤ_[l]) : Matrix (Fin d') (Fin d') ℤ_[l])) = fun g => Mf g⁻¹ := by
    funext g
    rw [← map_inv]
    exact hval _
  rw [e]
  exact hMci

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousWittCbInclusionSmulWeakTopology
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.WeakClosed

theorem continuous_io_smul_of {O RA RW M : Type} [CommRing O] [TopologicalSpace O] [CommRing RA]
    [Algebra O RA] [CommRing RW] [Algebra O RW] [AddCommGroup M] [Module RW M] [Module O M]
    [IsScalarTower O RW M] [TopologicalSpace M] [IsTopologicalAddGroup M] {n : ℕ}
    (io : LetA O n →ₐ[O] RA) (inc : RA →ₐ[O] RW) (y : M) (πA : RA) (hπ : io letπ = πA)
    (hsmall : ∀ U ∈ 𝓝 (0 : M), ∃ k : ℕ, ∀ z : RA, inc (πA ^ k * z) • y ∈ U)
    (hlin : ∀ f : (ZMod n → O) →ₗ[O] M, Continuous f) :
    Continuous fun a : LetA O n => inc (io a) • y := by
  let Φ : LetA O n →+ M :=
    { toFun := fun a => inc (io a) • y
      map_zero' := by simp
      map_add' := fun a c => by simp [add_smul] }
  refine GlobalTheory.T.continuous_of_tail_small_of_monomial_continuous Φ ?_ ?_
  · intro U hU
    obtain ⟨k, hk⟩ := hsmall U hU
    refine ⟨k, fun r => ?_⟩
    have hΦ : Φ (letπ ^ k * r) = inc (πA ^ k * io r) • y := by
      show inc (io (letπ ^ k * r)) • y = _
      rw [map_mul, map_pow, hπ]
    rw [hΦ]
    exact hk _
  · intro j
    let f : (ZMod n → O) →ₗ[O] M :=
      { toFun := fun c => inc (io (fun i => PowerSeries.C (c i))) • (inc (io letπ) ^ j • y)
        map_add' := fun c c' => by
          have : (fun i => PowerSeries.C ((c + c') i)) =
              (fun i => PowerSeries.C (c i)) + fun i => PowerSeries.C (c' i) := by
            funext i; simp
          simp only [this, map_add, add_smul]
        map_smul' := fun o c => by
          have : (fun i => PowerSeries.C ((o • c) i)) = o • (fun i => PowerSeries.C (c i)) := by
            funext i; simp [PowerSeries.smul_eq_C_mul, map_mul]
          simp only [this, map_smul, smul_assoc, RingHom.id_apply] }
    refine (hlin f).congr fun c => ?_
    have hc : (fun i => PowerSeries.C (c i) * PowerSeries.X ^ j : LetA O n) =
        (fun i => PowerSeries.C (c i)) * letπ ^ j := by
      funext i; simp [letπ]
    show inc (io (fun i => PowerSeries.C (c i))) • (inc (io letπ) ^ j • y) =
      inc (io (fun i => PowerSeries.C (c i) * PowerSeries.X ^ j)) • y
    rw [hc, map_mul, map_mul, mul_smul, map_pow, map_pow]

end GlobalTheory.WeakClosed

namespace GlobalTheory.WeakClosed

theorem isTopologicalAddGroup_twTop {l : ℕ} [Fact l.Prime] {K LL : FinExt l} (T : Lt K LL) {d : ℕ}
    (b : LatB T d) : letI := twTop T b; IsTopologicalAddGroup (TW (RW LL) T) := by
  letI := cbValued l
  letI := zlMod T
  haveI := zlTower T
  letI : TopologicalSpace (WCb l) := wTop l
  letI : TopologicalSpace (TW (RW LL) T) := twTop T b
  haveI : IsTopologicalRing (Cb l) := inferInstance
  haveI : IsTopologicalRing (WCb l) := GlobalTheory.WeakTop.isTopologicalRing_witt
  exact Topology.IsInducing.topologicalAddGroup (GlobalTheory.WeakTop.coords (WCb l) ↥(OL LL) b) ⟨rfl⟩

theorem finrank_maxUnramifiedSubfield_pos {l : ℕ} [Fact l.Prime] (K : FinExt l) : 0 < Module.finrank ℚ_[l] ↥(K0 K) := by
  haveI : FiniteDimensional ℚ_[l] K.1 := K.2
  haveI : FiniteDimensional ℚ_[l] (K0 K) :=
    FiniteDimensional.of_injective (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
      (RingHom.injective _)
  exact Module.finrank_pos

theorem continuous_inclR_io_smul : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {K : FinExt l} {s : ℕ} {LL : FinExt l} {h : Good K s LL} {W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))} (E : EtSit P AI K s LL h W) (T : Lt K LL) {d e : ℕ} (b : LatB T d) (bO : Module.Basis (Fin e) ℤ_[l] ↥(OL LL)) (y : TW (RW LL) T), letI := twTop T b; letI := aTop (K := K) bO; Continuous fun a : AA K LL => inclR LL (E.tie.io a) • y := by
  intro l _ P AI K s LL h W E T d e b bO y
  letI tT : TopologicalSpace (TW (RW LL) T) := twTop T b
  letI tO : TopologicalSpace ↥(OL LL) := oTop bO
  haveI := isTopologicalAddGroup_twTop T b
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨(finrank_maxUnramifiedSubfield_pos K).ne'⟩
  have hlin : ∀ f : (ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ↥(OL LL)) →ₗ[↥(OL LL)] TW (RW LL) T,
      Continuous f := fun f => GlobalTheory.T.continuous_linearMap_pi_of_continuous_coord bO (GlobalTheory.T.continuous_padicInt_smul_latB T b) f
  exact continuous_io_smul_of E.tie.io (inclR LL) y _ E.tie.io_π (GlobalTheory.T.exists_pow_inclR_smul_mem' AI s T b y) hlin

end GlobalTheory.WeakClosed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecompletionPhiSubOneBijective
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

namespace GlobalTheory.Decompl

set_option maxHeartbeats 2000000 in

theorem decompletion_matrix (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (W : Wach P K LL)
    (E : EtSit P AI K s LL h W) (H : Set (GQ l))
    (hH : ∀ g, g ∈ H ↔ ∃ hg : g ∈ GK K, W.resΓ ⟨g, hg⟩ = 1)
    (d : ℕ) (Pm : Matrix (Fin d) (Fin d) W.EE) :
    (∀ y : Fin d → RW LL, (∀ i, y i ∈ fixSub AI LL H) → ∃ z : Fin d → RW LL,
      (∀ i, z i ∈ fixSub AI LL H) ∧
        ∀ i, ∃ e, y i - (∑ k, E.tie.ioE (Pm i k) * φRW LL (z k) - z i) = E.tie.ioE e) ∧
    (∀ z : Fin d → RW LL, (∀ i, z i ∈ fixSub AI LL H) →
      (∀ i, ∃ e, ∑ k, E.tie.ioE (Pm i k) * φRW LL (z k) - z i = E.tie.ioE e) →
        ∀ i, ∃ e, z i = E.tie.ioE e) := by
  obtain ⟨c1, c2, c3, c4⟩ := GlobalTheory.T.etaleEmbedding_frobenius_galois_compat l P AI K s LL h W E
  obtain ⟨f1, f2, f3⟩ := GlobalTheory.T.galoisFixedSubringTensorWitt_saturated_complete l P AI LL H
  obtain ⟨p1, p2, -, -⟩ := GlobalTheory.T.frobenius_constants_piAdic_filtration_modEll l P AI LL s
  obtain ⟨s1, s2⟩ := GlobalTheory.T.etaleRing_image_saturated_adicClosed l P AI K s LL h W E
  have hE : ∀ e, E.tie.ioE e ∈ fixSub AI LL H := fun e => mem_fixSub.2 fun g hg => by
    obtain ⟨hg, hg1⟩ := (hH g).1 hg
    exact c2 ⟨g, hg⟩ hg1 e
  have hsub : ∀ y ∈ fixSub AI LL H, y ∈ fixSub AI LL (Hinf K : Set (GQ l)) := fun y hy =>
    mem_fixSub.2 fun g hg => mem_fixSub.1 hy g
      ((hH g).2 ((GlobalTheory.T.cyclotomicTower_fixes_epsilonRoots_resGamma_trivial l P AI K).2 s LL h W g hg))
  have hπ : piR AI LL s ∈ fixSub AI LL H := by rw [← c3]; exact hE _
  have q1 := GlobalTheory.T.galoisFixedTensorWitt_complete_piAdic_modEll l P AI LL s H hπ
  have q2 := GlobalTheory.T.etaleRing_image_add_ell_pi_adic_closed l P AI K s LL h W E
  have q3 := fun y hy => GlobalTheory.T.galoisFixedTensorWitt_approx_frobeniusPerfection l P AI K s LL h W E y (hsub y hy)
  have q4 := GlobalTheory.T.matrix_frobenius_sub_one_bijective_mod_subring (RW LL) W.EE (RA LL) (E.tie.ioE : W.EE →+* RW LL) (inclR LL : RA LL →+* RW LL)
    (φRW LL : RW LL →+* RW LL) (fixSub AI LL H) l (piR AI LL s)
    ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] piW AI s) rfl
  simp only [RingHom.coe_coe] at q4
  have q5 := q4 hE f2 (fun e => ⟨W.φE e, (c1 e).symm⟩) p1 p2 c4 f1 s1
  have q6 := q5 q1 q2 q3
  exact q6 f3 s2 d Pm

theorem decompletion : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := sit D.loc HW l (D.locA l) K s LL h; let E : S.Comparison₂ := ((F l).E K s LL h).tie; DecW S E := by
  intro D HW F l _ K s LL h S E
  refine GlobalTheory.T.decW_of_matrix_criterion S E fun d Pm => ?_
  have hm := decompletion_matrix l (D.loc l) (D.locA l) K s LL h ((HW l).W K s LL h)
    ((F l).E K s LL h) {g | ∃ hg : g ∈ GK K, ((HW l).W K s LL h).resΓ ⟨g, hg⟩ = 1}
    (fun _ => Iff.rfl) d Pm
  have hf : ∀ x : RW LL, x ∈ fixSub (D.locA l) LL
      {g | ∃ hg : g ∈ GK K, ((HW l).W K s LL h).resΓ ⟨g, hg⟩ = 1} ↔
      ∀ g ∈ Hker S, S.gR g x = x := fun x =>
    mem_fixSub.trans ⟨fun hx g hg => hx g.1 ⟨g.2, hg⟩, fun hx g ⟨hg, hg1⟩ => hx ⟨g, hg⟩ hg1⟩
  refine ⟨fun y hy => ?_, fun z hz => hm.2 z fun i => (hf _).2 (hz i)⟩
  obtain ⟨z, hz, hz'⟩ := hm.1 y fun i => (hf _).2 (hy i)
  exact ⟨z, fun i => (hf _).1 (hz i), hz'⟩

end GlobalTheory.Decompl
end

