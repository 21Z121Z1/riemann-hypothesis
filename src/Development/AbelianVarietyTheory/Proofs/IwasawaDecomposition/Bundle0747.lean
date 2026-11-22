import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0687
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0638
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0623
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0025
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0727
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0721
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0730
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0587
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0684
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartBoundsOfSchurLemW
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0728
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0725
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultCellsAmong
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0682
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAdmissibleFanOfCellMultOneCMField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0733
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0729
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodReductionCondition
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0044
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0377
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemIdealOfFlatStalkPullback
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.FlatPush

theorem flat_sections_to_chart {X : Scheme.{0}} {R : Type} [CommRing R] [IsLocalRing R] (ξ : Sp R ⟶ X) (U : X.affineOpens)
    (hle : ⊤ ≤ ξ ⁻¹ᵁ (U : X.Opens)) (hx : ξ (closedPoint R) ∈ (U : X.Opens)) (hfl : (Scheme.stalkClosedPointTo ξ).hom.Flat) :
    (ξ.appLE U ⊤ hle ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom.Flat := by
  have hf : (ξ.appLE U ⊤ hle ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom) =
      X.presheaf.germ U _ hx ≫ Scheme.stalkClosedPointTo ξ := by
    rw [Scheme.germ_stalkClosedPointTo]; rfl
  rw [hf, CommRingCat.hom_comp]
  refine RingHom.Flat.comp ?_ hfl
  letI : Algebra Γ(X, U) (X.presheaf.stalk (ξ (closedPoint R))) := X.presheaf.algebra_section_stalk ⟨_, hx⟩
  haveI := U.2.isLocalization_stalk ⟨_, hx⟩
  have : Module.Flat Γ(X, U) (X.presheaf.stalk (ξ (closedPoint R))) := IsLocalization.flat _ (U.2.primeIdealOf ⟨_, hx⟩).asIdeal.primeCompl
  exact this

theorem tmul_mem_of_germ {X Y' : Scheme.{0}} (ρ : Y' ⟶ X) (I : Y'.IdealSheafData) {R : Type} [CommRing R]
    (ξ : Sp R ⟶ X) (U : X.affineOpens) (hle : ⊤ ≤ ξ ⁻¹ᵁ (U : X.Opens)) (W : Y'.affineOpens)
    (hW : (W : Y'.Opens) ≤ ρ ⁻¹ᵁ (U : X.Opens)) (h : R)
    (hh : ∀ v : ↥(pullback ξ ρ : Scheme.{0}), ((pullback ξ ρ).presheaf.germ ⊤ v trivial).hom
      ((pullback.fst ξ ρ).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom h)) ∈
        FinalTheorems.stalkId (I.comap (pullback.snd ξ ρ)) v) :
    letI := (ρ.appLE U W hW).hom.toAlgebra
    letI := (ξ.appLE U ⊤ hle ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom.toAlgebra
    (1 : Γ(Y', W)) ⊗ₜ[Γ(X, U)] h ∈ (I.ideal W).map
      (Algebra.TensorProduct.includeLeftRingHom : Γ(Y', W) →+* Γ(Y', W) ⊗[Γ(X, U)] R) := by
  letI := (ρ.appLE U W hW).hom.toAlgebra
  letI := (ξ.appLE U ⊤ hle ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom.toAlgebra
  obtain ⟨κ, hκ, hL, hR⟩ := GlobalTheory.T.exists_specTensor_to_pullback_sections_compat ρ ξ U hle W hW
  obtain ⟨s0, hs0⟩ : ∃ s0, (pullback.fst ξ ρ).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom h) = s0 :=
    ⟨_, rfl⟩
  rw [hs0] at hh
  have hs : ∀ t, ((Spec (CommRingCat.of (Γ(Y', W) ⊗[Γ(X, U)] R))).presheaf.germ ⊤ t trivial).hom
      (κ.appTop.hom s0) ∈ FinalTheorems.stalkId (I.comap (κ ≫ pullback.snd ξ ρ)) t := by
    intro t
    have e := Scheme.Hom.germ_stalkMap_apply κ ⊤ t trivial s0
    rw [Scheme.IdealSheafData.comap_comp]
    refine GlobalTheory.VanStalk.map_le_stalkId_comap κ _ t ?_
    have : (κ.stalkMap t).hom (((pullback ξ ρ).presheaf.germ ⊤ (κ t) trivial).hom s0) ∈ _ :=
      Ideal.mem_map_of_mem _ (hh (κ t))
    rw [e] at this
    exact this
  have h4 := GlobalTheory.T.mem_ideal_map_of_germs_affineScheme (κ ≫ pullback.snd ξ ρ) I W hκ _ hs
  have h5 := Ideal.mem_map_of_mem (Scheme.ΓSpecIso (CommRingCat.of (Γ(Y', W) ⊗[Γ(X, U)] R))).hom.hom h4
  rw [Ideal.map_map] at h5
  have e1 : (Scheme.ΓSpecIso _).hom.hom (κ.appTop.hom s0) = (1 : Γ(Y', W)) ⊗ₜ[Γ(X, U)] h := by
    rw [← hR h, ← hs0]
  have e2 : (Scheme.ΓSpecIso (CommRingCat.of (Γ(Y', W) ⊗[Γ(X, U)] R))).hom.hom.comp
      ((κ ≫ pullback.snd ξ ρ).appLE W ⊤ hκ).hom = Algebra.TensorProduct.includeLeftRingHom := by
    ext c; exact hL c
  rwa [e1, e2] at h5

theorem mem_idlAlong_map_of_flat : ∀ {X Y' : Scheme.{0}} (ρ : Y' ⟶ X) [QuasiCompact ρ] [QuasiSeparated ρ]
    (I : Y'.IdealSheafData) {R : Type} [CommRing R] [IsLocalRing R] (ξ : Sp R ⟶ X),
    (Scheme.stalkClosedPointTo ξ).hom.Flat → ∀ h : R, (∀ v : ↥(pullback ξ ρ : Scheme.{0}),
      ((pullback ξ ρ).presheaf.germ ⊤ v trivial).hom ((pullback.fst ξ ρ).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom h)) ∈ FinalTheorems.stalkId (I.comap (pullback.snd ξ ρ)) v) →
      h ∈ idlAlong (I.map ρ) ξ := by
  intro X Y' ρ _ _ I R _ _ ξ hfl h hh
  obtain ⟨U₀, hU, hx, -⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
    (show ξ (closedPoint R) ∈ (⊤ : X.Opens) from trivial)
  let U : X.affineOpens := ⟨U₀, hU⟩
  have hle : ⊤ ≤ ξ ⁻¹ᵁ (U : X.Opens) := (Scheme.preimage_eq_top_of_closedPoint_mem ξ hx).ge
  rw [TraitOrder.idlAlong_eq_map (I.map ρ) ξ U hle]
  have hc : IsCompact ((ρ ⁻¹ᵁ (U : X.Opens) : Y'.Opens) : Set Y') :=
    QuasiCompact.isCompact_preimage (f := ρ) _ U.1.isOpen U.2.isCompact
  obtain ⟨Us, hUs, hfin, heq⟩ := Y'.isBasis_affineOpens.exists_finite_of_isCompact hc
  let ι := ↥Us
  haveI : Finite ι := hfin.to_subtype
  let W : ι → Y'.affineOpens := fun i => ⟨i.1, hUs i.2⟩
  have hW : ∀ i, (W i : Y'.Opens) ≤ ρ ⁻¹ᵁ (U : X.Opens) := fun i => heq ▸ le_sSup i.2
  have hcov : ρ ⁻¹ᵁ (U : X.Opens) ≤ ⨆ i, (W i : Y'.Opens) := by
    rw [heq, sSup_le_iff]
    intro V hV
    exact le_iSup (fun i : ι => (W i : Y'.Opens)) ⟨V, hV⟩
  letI : Algebra Γ(X, U) R := (ξ.appLE U ⊤ hle ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom.toAlgebra
  haveI : Module.Flat Γ(X, U) R := GlobalTheory.FlatPush.flat_sections_to_chart ξ U hle hx hfl
  let K : ι → Ideal Γ(X, U) := fun i => (I.ideal (W i)).comap (ρ.appLE U (W i) (hW i)).hom
  have h1 : ⨅ i, K i ≤ (I.map ρ).ideal U := fun b hb =>
    GlobalTheory.T.mem_idealSheaf_map_of_affineCover_preimage ρ I U W hW hcov b fun i => (Ideal.mem_iInf.1 hb i)
  have h2 : h ∈ ⨅ i, (K i).map (algebraMap Γ(X, U) R) := by
    refine Ideal.mem_iInf.2 fun i => ?_
    letI : Algebra Γ(X, U) Γ(Y', W i) := (ρ.appLE U (W i) (hW i)).hom.toAlgebra
    exact GlobalTheory.T.mem_map_comap_of_one_tmul_mem_map (I.ideal (W i)) h (tmul_mem_of_germ ρ I ξ U hle (W i) (hW i) h hh)
  exact Ideal.map_mono h1 (GlobalTheory.T.iInf_map_le_map_iInf_of_flat K h2)

end GlobalTheory.FlatPush
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSpanOfChernClassesOfRootsEqZero
section
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.GoodMetric GlobalTheory.LieBase GlobalTheory.GrassTop
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GrassKernel

section Esymm

variable (R : Type) [CommRing R] {ι : Type} (m : ι → ℕ)

def blockEsymm : MvPolynomial (Root m) R →ₐ[R] MvPolynomial (Root m) R :=
  aeval fun x : Root m => rename (Sigma.mk x.1) (esymm (Fin (m x.1)) R (x.2 + 1))

theorem split_blockEsymm [DecidableEq ι] (τ₀ : ι) :
    (GlobalTheory.BlockSymm.splitEquiv R τ₀).toAlgHom.comp (blockEsymm R m) =
      ((aeval fun i : Fin (m τ₀) =>
          esymm (Fin (m τ₀)) (MvPolynomial (Root (fun τ : {τ // τ ≠ τ₀} => m τ.1)) R) (i + 1)).restrictScalars R).comp
        ((mapAlgHom (blockEsymm R (fun τ : {τ // τ ≠ τ₀} => m τ.1))).comp
          (GlobalTheory.BlockSymm.splitEquiv R τ₀).toAlgHom) := by
  ext ⟨τ, i⟩ : 1
  by_cases h : τ = τ₀
  · subst h
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, blockEsymm, aeval_X,
      GlobalTheory.BlockSymm.splitEquiv_X_self, mapAlgHom_apply, map_X, AlgHom.restrictScalars_apply]
    have hc : rename (Sigma.mk τ) (esymm (Fin (m τ)) R ((i : ℕ) + 1)) =
        GlobalTheory.BlockSymm.chernRootsOver R m (X (τ, (i : ℕ) + 1)) := by
      simp [GlobalTheory.BlockSymm.chernRootsOver]
    rw [hc, ← GlobalTheory.BlockSymm.splitEquiv_symm_esymm, AlgEquiv.apply_symm_apply]
  · simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, blockEsymm, aeval_X,
      GlobalTheory.BlockSymm.splitEquiv_X_ne R τ₀ h, mapAlgHom_apply, map_C, AlgHom.restrictScalars_apply, aeval_C]
    simp [esymm, map_sum, map_prod, GlobalTheory.BlockSymm.splitEquiv_X_ne R τ₀ h]

end Esymm

theorem blockEsymm_injective (n : ℕ) : ∀ (ι : Type) [Fintype ι], Fintype.card ι = n →
    ∀ (R : Type) [CommRing R] (m : ι → ℕ), Function.Injective (blockEsymm R m) := by
  induction n with
  | zero =>
    intro ι _ hc R _ m
    haveI : IsEmpty ι := Fintype.card_eq_zero_iff.mp hc
    haveI : IsEmpty (Root m) := ⟨fun x => IsEmpty.false x.1⟩
    intro p q hpq
    rw [eq_C_of_isEmpty p, eq_C_of_isEmpty q] at hpq ⊢
    simp only [blockEsymm, aeval_C, algebraMap_eq] at hpq
    rw [hpq]
  | succ n ih =>
    intro ι _ hc R _ m
    classical
    obtain ⟨τ₀⟩ : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
    have hc' : Fintype.card {τ // τ ≠ τ₀} = n := by
      simp [Fintype.card_subtype_compl, hc]
    let R' := MvPolynomial (Root (fun τ : {τ // τ ≠ τ₀} => m τ.1)) R
    have h1 : Function.Injective (aeval (R := R') fun i : Fin (m τ₀) => esymm (Fin (m τ₀)) R' (i + 1)) := by
      intro p q hpq
      apply esymmAlgHom_fin_injective R' (m := m τ₀) (n := m τ₀) le_rfl
      apply Subtype.ext
      rw [esymmAlgHom_apply, esymmAlgHom_apply]
      exact hpq
    have h2 : Function.Injective (mapAlgHom (R := R) (σ := Fin (m τ₀))
        (blockEsymm R (fun τ : {τ // τ ≠ τ₀} => m τ.1))) := by
      intro p q hpq
      exact map_injective _ (ih _ hc' R _) hpq
    have key := split_blockEsymm R m τ₀
    intro p q hpq
    apply (GlobalTheory.BlockSymm.splitEquiv R τ₀).injective
    apply h2
    apply h1
    have := congrArg (fun F => F p) key
    have h' := congrArg (fun F => F q) key
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgHom.restrictScalars_apply] at this h'
    rw [← this, ← h', hpq]

variable {ι : Type} (m : ι → ℕ)

def truncChern : MvPolynomial (ι × ℕ) ℝ →ₐ[ℝ] MvPolynomial (Root m) ℝ :=
  aeval fun x : ι × ℕ =>
    if x.2 = 0 then 1 else if h : x.2 - 1 < m x.1 then X (⟨x.1, ⟨x.2 - 1, h⟩⟩ : Root m) else 0

def liftChern : MvPolynomial (Root m) ℝ →ₐ[ℝ] MvPolynomial (ι × ℕ) ℝ :=
  aeval fun x : Root m => X (x.1, (x.2 : ℕ) + 1)

theorem chernRoots_eq_comp : chernRoots m = (blockEsymm ℝ m).comp (truncChern m) := by
  ext ⟨τ, k⟩ : 1
  simp only [AlgHom.comp_apply, truncChern, aeval_X]
  rcases k with _ | j
  · simp [chernRoots, esymm_zero]
  · by_cases h : j < m τ
    · simp [chernRoots, h, blockEsymm]
    · have hc : (Finset.univ : Finset (Fin (m τ))).card < j + 1 := by simp; omega
      simp [chernRoots, h, esymm, Finset.powersetCard_eq_empty.mpr hc]

def rankIdeal : Ideal (MvPolynomial (ι × ℕ) ℝ) :=
  Ideal.span ((Set.range fun τ : ι => (X (τ, 0) - 1 : MvPolynomial (ι × ℕ) ℝ)) ∪
    {P | ∃ (τ : ι) (k : ℕ), m τ < k ∧ P = X (τ, k)})

theorem mk_liftChern_truncChern :
    (Ideal.Quotient.mkₐ ℝ (rankIdeal m)).comp ((liftChern m).comp (truncChern m)) =
      Ideal.Quotient.mkₐ ℝ (rankIdeal m) := by
  ext ⟨τ, k⟩ : 1
  simp only [AlgHom.comp_apply, truncChern, aeval_X, Ideal.Quotient.mkₐ_eq_mk]
  rcases k with _ | j
  · simp only [if_true, map_one]
    rw [← map_one (Ideal.Quotient.mk (rankIdeal m)), Ideal.Quotient.eq]
    rw [← neg_mem_iff, neg_sub]
    exact Ideal.subset_span (Or.inl ⟨τ, rfl⟩)
  · by_cases h : j < m τ
    · simp [h, liftChern]
    · simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel, h, dif_neg, not_false_eq_true, map_zero]
      rw [eq_comm, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span (Or.inr ⟨τ, j + 1, by omega, rfl⟩)

theorem mem_span_of_chernRoots_eq_zero : ∀ {ι : Type} [Fintype ι] (m : ι → ℕ) (Q : MvPolynomial (ι × ℕ) ℝ),
    chernRoots m Q = 0 → Q ∈ Ideal.span ((Set.range fun τ : ι => (X (τ, 0) - 1 : MvPolynomial (ι × ℕ) ℝ)) ∪
      {P | ∃ (τ : ι) (k : ℕ), m τ < k ∧ P = X (τ, k)}) := by
  intro ι _ m Q hQ
  have h0 : truncChern m Q = 0 := by
    apply blockEsymm_injective _ ι rfl ℝ m
    rw [map_zero, ← AlgHom.comp_apply, ← chernRoots_eq_comp, hQ]
  have h1 := congrArg (fun F => F Q) (mk_liftChern_truncChern m)
  simp only [AlgHom.comp_apply, h0, map_zero, Ideal.Quotient.mkₐ_eq_mk] at h1
  exact (Ideal.Quotient.eq_zero_iff_mem).mp h1.symm

end GlobalTheory.GrassKernel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MumfordGoodGrowthBoundFrameChangeOrthogonalSumma
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.FrameGood
open ReciprocityTheory.L2DbarEstimates (V)

theorem goodBound_submatrix {n : ℕ} {K L : Type} [Fintype K] [DecidableEq K] [Fintype L] [DecidableEq L]
    (e : K ≃ L) {S : Finset (Fin n)} {c : ℝ} {N : ℕ} {G : V n → Matrix L L ℂ} {v : V n}
    (h : GoodBound S c N G v) : GoodBound S c N (fun u => (G u).submatrix e e) v where
  entry i j := h.entry (e i) (e j)
  det := by simpa [det_submatrix_equiv_self] using h.det
  form a i j := by simpa [GlobalTheory.HermFrame.conn_submatrix_equiv] using h.form a (e i) (e j)
  dbar a b i j := by simpa [GlobalTheory.HermFrame.curv_submatrix_equiv] using h.dbar a b (e i) (e j)
  del a b i j := by
    have h1 : ∀ ξ, (fun u => GlobalTheory.HermFrame.conn (fun x => (G x).submatrix e e) u ξ) =
        fun u => (GlobalTheory.HermFrame.conn G u ξ).submatrix e e :=
      fun ξ => funext fun u => GlobalTheory.HermFrame.conn_submatrix_equiv G e u ξ
    simp only [h1]
    exact h.del a b (e i) (e j)

theorem frame_summands_goodBound : ∀ (n g : ℕ) (S : Finset (Fin n)) (W : Set (ReciprocityTheory.L2DbarEstimates.V n)) (G₀ : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin g) (Fin g) ℂ) (c : ℝ) (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (m : ι → ℕ) (Q : ∀ τ : ι, ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin (m τ)) (Fin g) ℂ) (r : ℝ), IsOpen W → 0 < r → (∀ τ i k, DifferentiableOn ℂ (fun u => Q τ u i k) (Metric.ball 0 r)) → Fintype.card (Σ τ, Fin (m τ)) = g → LinearIndependent ℂ (fun p : Σ τ, Fin (m τ) => Q p.1 0 p.2) → (∀ v ∈ W, (G₀ v).det ≠ 0 ∧ (∀ i k, ContDiffAt ℝ 2 (fun u => G₀ u i k) v) ∧ GlobalTheory.GoodMetric.GoodBound S c N G₀ v) → (∀ v ∈ W, ∀ τ τ', τ ≠ τ' → Q τ v * G₀ v * (Q τ' v)ᴴ = 0) → ∃ r' : ℝ, 0 < r' ∧ ∃ (c' : ℝ) (N' : ℕ), ∀ v ∈ W, ‖v‖ < r' → ∀ τ, GlobalTheory.GoodMetric.GoodBound S c' N' (fun u => Q τ u * G₀ u * (Q τ u)ᴴ) v := by
  intro n g S W G₀ c N ι _ _ m Q r hW hr hQ hcard hind hG₀ horth
  let K := Σ τ, Fin (m τ)
  let e : K ≃ Fin g := Fintype.equivFinOfCardEq hcard
  let P : V n → Matrix K K ℂ := fun u => Matrix.of fun p k => Q p.1 u p.2 (e k)
  let G₁ : V n → Matrix K K ℂ := fun u => (G₀ u).submatrix e e
  have hP : ∀ i k, DifferentiableOn ℂ (fun u => P u i k) (Metric.ball 0 r) := fun i k => hQ i.1 i.2 (e k)
  have hP0 : IsUnit (P 0).det := by
    rw [← isUnit_iff_isUnit_det, ← linearIndependent_rows_iff_isUnit]
    have h2 := hind.map' _ (LinearEquiv.ker (LinearEquiv.funCongrLeft ℂ ℂ e))
    have h3 : (P 0).row = ⇑(LinearEquiv.funCongrLeft ℂ ℂ e) ∘ fun p => Q p.1 0 p.2 := by
      funext p k; rfl
    rw [h3]; exact h2
  have hG₁ : ∀ v ∈ W, (G₁ v).det ≠ 0 ∧ (∀ i k, ContDiffAt ℝ 2 (fun u => G₁ u i k) v) ∧
      GoodBound S c N G₁ v := by
    intro v hv
    obtain ⟨h1, h2, h3⟩ := hG₀ v hv
    exact ⟨by simpa [G₁, det_submatrix_equiv_self] using h1, fun i k => h2 (e i) (e k),
      goodBound_submatrix e h3⟩
  obtain ⟨r₁, hr₁, -, B, hB⟩ := GlobalTheory.T.holomorphicFrameChange_local_bounds n K P r hr hP hP0
  obtain ⟨c₁, hc₁⟩ := GlobalTheory.T.mumfordGoodGrowthBound_holomorphic_frameChange n K S c N B
  let Gb : V n → Matrix K K ℂ := fun u => blockDiagonal' fun τ => Q τ u * G₀ u * (Q τ u)ᴴ
  obtain ⟨c', N', h3⟩ := GlobalTheory.T.mumfordGoodGrowthBound_blocks_of_blockDiagonal n S ι m (fun τ u => Q τ u * G₀ u * (Q τ u)ᴴ) c₁ N
  refine ⟨min r₁ (1 / 2), by positivity, c', N', fun v hv hvr τ => ?_⟩
  have hv1 : ‖v‖ < r₁ := hvr.trans_le (min_le_left _ _)
  have hv2 : ‖v‖ < 1 / 2 := hvr.trans_le (min_le_right _ _)
  obtain ⟨hPu, hPc, hPd, hPb, hPib, hPdb, hPddb⟩ := hB v hv1
  obtain ⟨hdet, hC, hgb⟩ := hG₁ v hv
  obtain ⟨d1, c1, g1⟩ := hc₁ G₁ P v (by linarith) hdet hC hPc hPd hPu hPb hPib hPdb hPddb hgb
  have heq : ∀ u ∈ W, P u * G₁ u * (P u)ᴴ = Gb u := by
    intro u hu
    ext ⟨τ, i⟩ ⟨τ', j⟩
    have key : (P u * G₁ u * (P u)ᴴ) ⟨τ, i⟩ ⟨τ', j⟩ = (Q τ u * G₀ u * (Q τ' u)ᴴ) i j := by
      simp only [P, G₁, mul_apply, conjTranspose_apply, of_apply, submatrix_apply]
      exact Fintype.sum_equiv e _ _ fun l => by
        congr 1
        exact Fintype.sum_equiv e _ _ fun k => rfl
    by_cases hτ : τ = τ'
    · subst hτ
      rw [key]
      simp only [Gb, blockDiagonal'_apply_eq]
    · rw [key, horth u hu τ τ' hτ]
      simp only [Gb, blockDiagonal'_apply_ne _ _ _ hτ, Matrix.zero_apply]
  have hev : (fun u => P u * G₁ u * (P u)ᴴ) =ᶠ[𝓝 v] Gb :=
    Filter.eventually_of_mem (hW.mem_nhds hv) heq
  refine h3 v (fun a _ => (PiLp.norm_apply_le v a).trans_lt hv2) ?_ ?_ ?_ τ
  · change (Gb v).det ≠ 0
    rw [← heq v hv]; exact d1
  · intro p q
    exact (c1 p q).congr_of_eventuallyEq (hev.mono fun u hu => by
      exact (congrFun (congrFun hu p) q).symm)
  · exact GlobalTheory.T.mumfordGoodGrowthBound_congr_germ_gram n K S c₁ N _ Gb v hev g1

end GlobalTheory.FrameGood
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NatCardTorsionQuotSpanDvdOfRangeSubset
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory

theorem natCard_torsion_quot_span_dvd_of_range_subset :
    ∀ (L : Type) [AddCommGroup L] {m n : ℕ} (δ : Fin m → L) (γ : Fin n → L), LinearIndependent ℤ δ →
    Set.range γ ⊆ Set.range δ →
    Nat.card (Submodule.torsion ℤ (L ⧸ Submodule.span ℤ (Set.range γ))) ∣
      Nat.card (Submodule.torsion ℤ (L ⧸ Submodule.span ℤ (Set.range δ))) := by
  intro L _ m n δ γ hli hsub
  have hAB : Submodule.span ℤ (Set.range γ) ≤ Submodule.span ℤ (Set.range δ) :=
    Submodule.span_mono hsub
  have key : ∀ z : L, z ∈ Submodule.span ℤ (Set.range δ) → ∀ a : ℤ, a ≠ 0 →
      a • z ∈ Submodule.span ℤ (Set.range γ) → z ∈ Submodule.span ℤ (Set.range γ) := by
    intro z hz a ha haz
    have himg : δ '' (δ ⁻¹' Set.range γ) = Set.range γ := Set.image_preimage_eq_of_subset hsub
    rw [← himg] at haz ⊢
    rw [Finsupp.mem_span_image_iff_linearCombination] at haz ⊢
    obtain ⟨l', hl'S, hl'⟩ := haz
    rw [Finsupp.mem_span_range_iff_exists_finsupp] at hz
    obtain ⟨c, hc⟩ := hz
    have hlc : Finsupp.linearCombination ℤ δ c = z := by
      rw [Finsupp.linearCombination_apply]; exact hc
    have heq : a • c = l' := by
      apply hli
      rw [map_smul, hlc, hl']
    refine ⟨c, ?_, hlc⟩
    rw [Finsupp.mem_supported'] at hl'S ⊢
    intro i hi
    have := hl'S i hi
    rw [← heq, Finsupp.smul_apply, smul_eq_mul] at this
    exact (mul_eq_zero.mp this).resolve_left ha
  let q : (L ⧸ Submodule.span ℤ (Set.range γ)) →ₗ[ℤ] (L ⧸ Submodule.span ℤ (Set.range δ)) :=
    Submodule.factor hAB
  let f : Submodule.torsion ℤ (L ⧸ Submodule.span ℤ (Set.range γ)) →+
      Submodule.torsion ℤ (L ⧸ Submodule.span ℤ (Set.range δ)) :=
    (q.restrict (p := Submodule.torsion ℤ _) (q := Submodule.torsion ℤ _) (fun x hx => by
      rw [Submodule.mem_torsion_iff] at hx ⊢
      obtain ⟨a, ha⟩ := hx
      exact ⟨a, by rw [Submonoid.smul_def] at ha ⊢; rw [← map_smul, ha, map_zero]⟩)).toAddMonoidHom
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨x, hx⟩ hfx
    have hqx : q x = 0 := congrArg Subtype.val hfx
    apply Subtype.ext
    simp only [ZeroMemClass.coe_zero]
    induction x using Submodule.Quotient.induction_on with
    | H z =>
      rw [Submodule.mem_torsion_iff] at hx
      obtain ⟨⟨a, ha0⟩, ha⟩ := hx
      have hz : z ∈ Submodule.span ℤ (Set.range δ) := by
        rw [← Submodule.Quotient.mk_eq_zero]
        simpa [q] using hqx
      have ha' : a ≠ 0 := nonZeroDivisors.ne_zero ha0
      have haz : a • z ∈ Submodule.span ℤ (Set.range γ) := by
        rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
        simpa [Submonoid.smul_def] using ha
      rw [Submodule.Quotient.mk_eq_zero]
      exact key z hz a ha' haz
  exact AddSubgroup.card_dvd_of_injective f hinj

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormalisedReadingsRelatedLocalizedAdelicData
section
noncomputable section

namespace GlobalTheory.HeightCounting.Fin3

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2
  GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

theorem yRel_of_pin : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P)
    (L : LocAll (lay0 (Dof x))) (m : Moved (oL x L)), m.z = datL x L → m.Coh → ∀ (s : Side0 (oL x L)) (r : ReadPk m s), r.Pin →
      ∀ Y : YT x L s.p0, HEq Y r.Y → YRel L Y := by
  intro K B f T w P x L m hz hC s r hP Y hY
  have hR := CopyRead.repOf_heq x.coh x.r x.pin hC r hP
  obtain ⟨z, intersectionNumber_baseChange, exAt, inGeo, Xg, tr, core, eta, W1, y, tup, t, tA⟩ := m
  dsimp only at hz
  subst hz
  obtain ⟨rY, rZ, rtup, rtupT, rPY, rPW, rjA, rjA0, reMt⟩ := r
  dsimp only at hY
  cases hY
  refine ⟨(by with_unfolding_all exact (hR :)), ?_, ?_⟩
  · intro i y
    have heW := hP.eW
    have hf : HEq t.lf.eW x.m.t.lf.eW := hC.eW.trans x.coh.eW.symm
    have h3 : @Eq (type_of% t.lf.eW) t.lf.eW ((by with_unfolding_all exact (x.m.t.lf.eW :))) :=
      @eq_of_heq (type_of% t.lf.eW) t.lf.eW ((by with_unfolding_all exact (x.m.t.lf.eW :))) ((by with_unfolding_all exact (hf :)))
    exact kc% ((heW i y).trans ((heq_of_eq (congrArg (fun g => g i y) h3)).trans (x.pin.eW i y).symm))
  · intro μ h i y
    have hjMt := hP.jMt
    have hf : HEq t.lf.jMt x.m.t.lf.jMt := hC.jMt.trans x.coh.jMt.symm
    have h3 : @Eq (type_of% t.lf.jMt) t.lf.jMt ((by with_unfolding_all exact (x.m.t.lf.jMt :))) :=
      @eq_of_heq (type_of% t.lf.jMt) t.lf.jMt ((by with_unfolding_all exact (x.m.t.lf.jMt :))) ((by with_unfolding_all exact (hf :)))
    exact (by with_unfolding_all exact (((hjMt μ h i y).trans ((heq_of_eq (congrArg (fun g => g μ i y) h3)).trans (x.pin.jMt μ h i y).symm)) :))

end GlobalTheory.HeightCounting.Fin3

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OverNEOfNEb
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

namespace GlobalTheory.Mem.AtPtTransport

variable {hL : GlobalTheory.Published.LocalLanglandsGL}

theorem overNE_of_NEb {N : NExt hL}
    (hN : ∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (NEb hL K B f T w Z Wt p0 t nch n xd c)) :
    GlobalTheory.NRows.AtPt.OverNE N :=
  fun K B f T w Z Wt p0 t nch n xd c h => (hN K B f T w Z Wt p0 t nch n xd c h).elim fun x => ⟨x.1⟩

theorem atMem_at_wit : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (N : NExt hL) (S : SExt) (Γ : GeoP), WitMv (prmR N S Γ).s →
    (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (NEb hL K B f T w Z Wt p0 t nch n xd c)) →
    (∀ p : LayP hL, AtMem hL p → RL.At (prmR N S Γ) fun Q L => RowE Q L fun κ D O _ _ => ∃ K : Ctx, κ.Of K ∧ O.L.sc = K.s ∧
      Val K.C K.cD K.ch O.L ∧ ∃ q : WPt (prmR N S Γ).s K, q.Is D O ∧
        p K q.B q.f q.T q.w q.Z q.x.Wt _ q.x.what₂ _ q.x.n (WPt.core (p := prmR N S Γ) q)) ∧
    ∀ P : ∀ D : D7, NChoice D → Prop, AtMem hL (fun _ _ _ _ w Z _ _ _ nch _ _ => P (w.D Z) nch) →
      RL.At (prmR N S Γ) fun Q L => RowE Q L fun _ D O _ _ => P D O.ex.nch := by
  intro hL N S Γ H hN
  have hN' := overNE_of_NEb hN
  refine ⟨fun p hp => ?_, fun P hP => ?_⟩
  · refine GlobalTheory.NRows.AtPt.linkedBundleProperty_after_largeBaseCoreProperty (GlobalTheory.NRows.AtPt.largeBasePropertyG_memberProperty hp _) ?_
    refine RowE.of_all fun κ K β c b hk hβ _ => ?_
    obtain ⟨q, hq, _, hw⟩ := GlobalTheory.NRows.AtPt.exists_wit hN' H β hβ
    exact ⟨K, hk, β.sc, β.p.pt_val β.val, q, hq, hw⟩
  · exact GlobalTheory.NRows.AtPt.lg1_entryPred_of_atMem_witMv hP hN' H (r := fun D O => P D O.ex.nch) (fun K q _ t => t) _

end GlobalTheory.Mem.AtPtTransport
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationLineBundleUnifIsoStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarization_line_bundle_unif_iso : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G) (L L' : LB ((Over.pullback (jK R)).obj G).left), L.IsLB → L'.IsLB → LBIso L (U.LG.L.pull (pullback.fst G.hom (jK R))) → LBIso L' (U'.LG.L.pull (pullback.fst G.hom (jK R))) → LBIso (abelian₂ ((Over.pullback (jK R)).obj G) L) (abelian₂ ((Over.pullback (jK R)).obj G) L') → LBIso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) := by
  first | exact @GlobalTheory.squares_iso_of_lam_generic | exact GlobalTheory.squares_iso_of_lam_generic | (intros; apply GlobalTheory.squares_iso_of_lam_generic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PreimageIUnionOpensEqRangeFlagCellsStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.preimage_iUnion_opens_eq_range_flagCells : ∀ (O K : Type) [CommRing O] [Field K] (β : O →+* K) (X : Scheme.{0}) (s : X ⟶ Sp O) (T : Type) [Finite T] (m : T → ℕ) (M : ℕ) (B : Type) (V : B → X.affineOpens) (α : ∀ b, K →+* Γ(X, (V b).1)) (c D : ∀ b, Let m → Fin (M + 1) → Γ(X, (V b).1)) (P : Scheme.{0}) (p0 : P ⟶ X) (p : ∀ en : En m, P ⟶ PSpace O (plN M en.1)) (h : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ P)), IsCover β s V α c D → IsPlk β s V α c p0 p h → ∀ (F Z : Scheme.{0}) (f : F ⟶ P) (i : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ F)) (j : F ⟶ Z) (ν : Z ⟶ P), IsImmersion f → (∀ b w, IsOpenImmersion (i b w)) → (∀ b w, i b w ≫ f = h b w) → (∀ x : F, ∃ b w, x ∈ Set.range (i b w)) → IsOpenImmersion j → j ≫ ν = f → Dense (Set.range j) → TopologicalSpace.NoetherianSpace F → IsSeparated (ν ≫ p0) → (ν ≫ p0) ⁻¹' ⋃ b, ((V b).1 : Set X) = Set.range j := by
  first | exact @GlobalTheory.FlagEmb.preimage_iUnion_eq_range_cells | exact GlobalTheory.FlagEmb.preimage_iUnion_eq_range_cells | (intros; apply GlobalTheory.FlagEmb.preimage_iUnion_eq_range_cells <;> assumption)
end

